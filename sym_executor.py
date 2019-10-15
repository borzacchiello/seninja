import z3
from binaryninja import (
    BinaryReader, BinaryWriter, 
    RegisterValueType, enums
)
from sym_state import State
from arch.arch_x86 import x86Arch
from arch.arch_x86_64 import x8664Arch
from models.function_models import library_functions
from utility.z3_wrap_util import (
    bvv_from_bytes, bvv, bvs, symbolic
)
from utility.bninja_util import (
    get_function, get_imported_functions, 
    get_imported_addresses, find_os
)
from utility.models_util import get_result_reg
from memory.sym_memory import InitData
from multipath.fringe import Fringe
from utility.error_codes import ErrorInstruction
from options import CHECK_DIVISION_BY_ZERO, SINGLE_LLIL_STEP

NO_COLOR             = enums.HighlightStandardColor(0)
CURR_STATE_COLOR     = enums.HighlightStandardColor.GreenHighlightColor
DEFERRED_STATE_COLOR = enums.HighlightStandardColor.RedHighlightColor

class BNILVisitor(object):
    # thanks joshwatson (https://github.com/joshwatson/f-ing-around-with-binaryninja/blob/master/ep4-emulator/vm_visitor.py)
    def __init__(self, **kw):
        super(BNILVisitor, self).__init__()

    def visit(self, expression):
        method_name = 'visit_{}'.format(expression.operation.name)
        if hasattr(self, method_name):
            value = getattr(self, method_name)(expression)
        else:
            value = None
        return value

class SymbolicVisitor(BNILVisitor):
    def __init__(self, view, addr):
        super(SymbolicVisitor, self).__init__()

        self.view    = view
        self.bw      = BinaryWriter(view)
        self.br      = BinaryReader(view)
        self.vars    = set()
        self.fringe  = Fringe()
        self.ip      = addr
        self.llil_ip = None 
        self.arch    = None
        self.imported_functions = get_imported_functions(view)
        self.imported_addresses = get_imported_addresses(view)

        self._wasjmp = False
        if self.view.arch.name == "x86":
            self.arch = x86Arch()
        elif self.view.arch.name == "x86_64":
            self.arch = x8664Arch()
        
        assert self.arch is not None
        self.state = State(self, arch=self.arch, os=find_os(view), page_size=0x1000)

        # load memory
        print("loading segments...")
        for segment in self.view.segments:
            start = segment.start
            size  = segment.data_length
            print(segment, hex(start), "->", hex(size))

            if size == 0:
                continue
            
            self.br.seek(start)
            data = self.br.read(size)

            self.state.mem.mmap(
                self.state.address_page_aligned(start),
                self.state.address_page_aligned(start + size + self.state.mem.page_size) - self.state.address_page_aligned(start),
                InitData(data, start - self.state.address_page_aligned(start))
            )
        print("loading finished!")

        current_function = get_function(view, addr)

        # initialize stack
        unmapped_page_init = self.state.get_unmapped(2)
        self.state.mem.mmap(unmapped_page_init*self.state.page_size, self.state.page_size * 2)
        p = unmapped_page_init + 1
        stack_base = p * self.state.page_size - self.arch.bits() // 8

        self.state.initialize_stack(stack_base)

        # initialize registers
        for reg in self.arch.regs_data():
            reg_dict = self.arch.regs_data()[reg]
            val = current_function.get_reg_value_after(addr, reg)

            if val.type.value == RegisterValueType.StackFrameOffset:
                setattr(self.state.regs, reg, bvv(stack_base + val.offset, reg_dict['size'] * 8))
            elif (
                val.type.value == RegisterValueType.ConstantPointerValue or 
                val.type.value == RegisterValueType.ConstantValue
            ):
                setattr(self.state.regs, reg, bvv(val.value, reg_dict['size'] * 8))
            else:
                symb = bvs(reg + "_init", reg_dict['size'] * 8)
                self.vars.add(symb)
                setattr(self.state.regs, reg, symb)
        
        # initialize known local variables
        stack_vars = current_function.stack_layout
        for var in stack_vars:
            offset = var.storage
            s_type = var.type

            if s_type.confidence != 255:
                continue
            
            width = s_type.width
            name = var.name
            val  = current_function.get_stack_contents_at(addr, offset, width)
            if val.type.value == RegisterValueType.StackFrameOffset:
                assert width*8 == self.arch.bits()  # has to happen... right?
                self.state.mem.store(
                    bvv(stack_base + offset, self.arch.bits()), 
                    bvv(stack_base + val.offset, width*8 ),
                    endness=self.arch.endness())
            elif (
                val.type.value == RegisterValueType.ConstantPointerValue or 
                val.type.value == RegisterValueType.ConstantValue
            ):
                self.state.mem.store(
                    bvv(stack_base + offset, self.arch.bits()), 
                    bvv(val.value, width*8 ),
                    endness=self.arch.endness())
            else:
                symb = bvs(name + "_init", self.arch.bits())
                self.vars.add(symb)
                self.state.mem.store(
                    bvv(stack_base + offset, self.arch.bits()), 
                    symb,
                    endness=self.arch.endness())
        
        # set eip
        self.state.set_ip(addr)
        self.llil_ip = current_function.llil.get_instruction_start(addr)

        current_function.set_auto_instr_highlight(self.ip, CURR_STATE_COLOR)
    
    def _check_unsupported(self, val, expr):
        if val is None:
            raise Exception("unsupported instruction '%s'" % (expr.operation.name))
        
    def _check_error(self, val):
        return isinstance(val, ErrorInstruction)
    
    def _handle_error(self, err):
        if err in {
            ErrorInstruction.DIVISION_BY_ZERO,
            ErrorInstruction.UNMAPPED_READ,
            ErrorInstruction.UNMAPPED_WRITE
        }:
            assert self.state is None
            print("WARNING: changing current state due to %s" % err.name)
            return
        
        raise Exception("Unknown error")
    
    def _handle_symbolic_ip(self):
        raise NotImplementedError  # implement this
    
    def _put_in_deferred(self, state):
        # ip = state.get_ip()
        self.fringe.add_deferred(state)
    
    def _put_in_unsat(self, state):
        # ip = state.get_ip()
        self.fringe.add_unsat(state)
    
    def _put_in_errored(self, state, msg: str):
        self.fringe.add_errored(
            (msg, state)
        )
    
    def _set_colors(self, old_ip=None, reset=False):
        if old_ip is not None:
            old_func = get_function(self.view, old_ip)
            old_func.set_auto_instr_highlight(old_ip, NO_COLOR)

        for ip in self.fringe._deferred:
            func = get_function(self.view, ip)
            func.set_auto_instr_highlight(ip, DEFERRED_STATE_COLOR if not reset else NO_COLOR)
            # func.set_comment_at(ip, str(len(self.fringe._deferred[ip]) if not reset else ""))
        
        func = get_function(self.view, self.ip)
        func.set_auto_instr_highlight(self.ip, CURR_STATE_COLOR if not reset else NO_COLOR)

    def set_current_state(self, state):
        if self.state is not None:
            self.state.llil_ip = self.llil_ip
            self._put_in_deferred(self.state)
            self.state = None
        
        ip = state.get_ip()
        llil_ip = state.llil_ip

        self.state = state
        new_func = get_function(self.view, ip) 
        self.ip = ip
        self.llil_ip = new_func.llil.get_instruction_start(ip) if llil_ip is None else llil_ip

        self._set_colors()

    def select_from_deferred(self):
        if self.fringe.is_empty():
            return False
        
        state = self.fringe.get_one_deferred()
        self.set_current_state(state)
        return True
    
    def update_ip(self, function, new_llil_ip):
        old_ip = self.ip

        self.llil_ip = new_llil_ip
        self.ip = function.llil[new_llil_ip].address
        self.state.set_ip(self.ip)
        self.state.llil_ip = new_llil_ip

        self._set_colors(old_ip)
    
    def _execute_one(self):
        old_ip = self.ip
        func = get_function(self.view, self.ip)
        expr = func.llil[self.llil_ip]
        res = self.visit(expr)

        self._check_unsupported(res, expr)
        if self._check_error(res):
            self._handle_error(res)
        
        if self.state is None:
            if self.fringe.is_empty():
                return
            else:
                self.select_from_deferred()
                self._wasjmp = True
                self._set_colors(old_ip)
        
        if not self._wasjmp:
            # go on by 1 instruction
            self.update_ip(func, self.llil_ip + 1)
        else:
            self._wasjmp = False
            self._set_colors(old_ip)
        
        return self.ip
    
    def execute_one(self):
        if SINGLE_LLIL_STEP:
            self._execute_one()
        else:
            old_ip = self.ip
            while self._execute_one() == old_ip:
                pass

    def visit_LLIL_CONST(self, expr):
        return bvv(expr.constant, expr.size * 8)

    def visit_LLIL_CONST_PTR(self, expr):
        return bvv(expr.constant, self.arch.bits())

    def visit_LLIL_SET_REG(self, expr):
        dest = expr.dest.name
        src  = self.visit(expr.src)

        self._check_unsupported(src, expr.src)
        if self._check_error(src): return src

        setattr(self.state.regs, dest, src)
        return True

    def visit_LLIL_REG(self, expr):
        src = expr.src
        return getattr(self.state.regs, src.name)
    
    def visit_LLIL_REG_SPLIT(self, expr):
        lo = getattr(self.state.regs, expr.lo.name)
        hi = getattr(self.state.regs, expr.hi.name)

        return z3.Concat(hi, lo)

    def visit_LLIL_SET_REG_SPLIT(self, expr):
        src = self.visit(expr.src)
        lo = expr.lo.name
        hi = expr.hi.name

        self._check_unsupported(src, expr.src)
        if self._check_error(src): return src

        lo_val = z3.Extract(src.size() // 2 - 1, 0, src)
        hi_val = z3.Extract(src.size() - 1, src.size() // 2, src)
        
        setattr(self.state.regs, lo, lo_val)
        setattr(self.state.regs, hi, hi_val)
        return True
    
    def visit_LLIL_SET_FLAG(self, expr):
        dest = expr.dest.name
        src  = self.visit(expr.src)

        self._check_unsupported(src, expr.src)
        if self._check_error(src): return src

        if isinstance(src, z3.BoolRef):
            res = z3.simplify(z3.If(src, bvv(1, 1), bvv(0, 1)))
        else:
            res = z3.simplify(z3.If(src == 0, bvv(0, 1), bvv(1, 1)))
        self.state.regs.flags[dest] = res
        return True
    
    def visit_LLIL_FLAG(self, expr):
        src = expr.src.name
        return self.state.regs.flags[src]
    
    def visit_LLIL_LOW_PART(self, expr):
        src = self.visit(expr.src)
        size = expr.size

        self._check_unsupported(src, expr.src)
        if self._check_error(src): return src
        
        return z3.Extract(size*8-1, 0, src)
    
    def visit_LLIL_ADD(self, expr):
        left  = self.visit(expr.left)
        right = self.visit(expr.right)

        self._check_unsupported(left,  expr.left )
        self._check_unsupported(right, expr.right)
        if self._check_error(left):  return left
        if self._check_error(right): return right

        if right.size() > left.size():
            left = z3.SignExt(right.size() - left.size(), left)
        if left.size() > right.size():
            right = z3.SignExt(left.size() - right.size(), right)
        
        return z3.simplify(left + right)
    
    def visit_LLIL_ADC(self, expr):
        left  = self.visit(expr.left)
        right = self.visit(expr.right)
        carry = self.visit(expr.carry)

        self._check_unsupported(left,  expr.left )
        self._check_unsupported(right, expr.right)
        self._check_unsupported(carry, expr.carry)
        if self._check_error(left):  return left
        if self._check_error(right): return right
        if self._check_error(carry): return carry

        if right.size() > left.size():
            left = z3.SignExt(right.size() - left.size(), left)
        if left.size() > right.size():
            right = z3.SignExt(left.size() - right.size(), right)
        
        return z3.simplify(left + right + z3.ZeroExt(left.size() - 1, carry))

    def visit_LLIL_SUB(self, expr):
        left  = self.visit(expr.left)
        right = self.visit(expr.right)

        self._check_unsupported(left,  expr.left )
        self._check_unsupported(right, expr.right)
        if self._check_error(left):  return left
        if self._check_error(right): return right

        if right.size() > left.size():
            left = z3.SignExt(right.size() - left.size(), left)
        if left.size() > right.size():
            right = z3.SignExt(left.size() - right.size(), right)
        
        return z3.simplify(left - right)
    
    def visit_LLIL_MUL(self, expr):
        left  = self.visit(expr.left)
        right = self.visit(expr.right)

        self._check_unsupported(left,  expr.left )
        self._check_unsupported(right, expr.right)
        if self._check_error(left):  return left
        if self._check_error(right): return right

        if right.size() > left.size():
            left = z3.SignExt(right.size() - left.size(), left)
        if left.size() > right.size():
            right = z3.SignExt(left.size() - right.size(), right)
        
        return z3.simplify(left * right)
    
    def visit_LLIL_MULS_DP(self, expr):
        left = self.visit(expr.left)
        right = self.visit(expr.right)

        self._check_unsupported(left,  expr.left )
        self._check_unsupported(right, expr.right)
        if self._check_error(left):  return left
        if self._check_error(right): return right

        assert left.size() == right.size()
        left  = z3.SignExt(left.size(),  left)
        right = z3.SignExt(right.size(), right)
        return left * right

    def visit_LLIL_MULU_DP(self, expr):
        left = self.visit(expr.left)
        right = self.visit(expr.right)

        self._check_unsupported(left,  expr.left )
        self._check_unsupported(right, expr.right)
        if self._check_error(left):  return left
        if self._check_error(right): return right

        assert left.size() == right.size()
        left  = z3.ZeroExt(left.size(),  left)
        right = z3.ZeroExt(right.size(), right)
        return left * right

    def visit_LLIL_DIVU_DP(self, expr):
        left = self.visit(expr.left)
        right = self.visit(expr.right)

        self._check_unsupported(left,  expr.left )
        self._check_unsupported(right, expr.right)
        if self._check_error(left):  return left
        if self._check_error(right): return right

        assert left.size() == 2*right.size()
        
        right = z3.ZeroExt(left.size() - right.size(), right)
        if CHECK_DIVISION_BY_ZERO and self.state.solver.satisfiable(extra_constraints=[right == 0]):
            print("WARNING: division by zero detected")
            errored = self.state.copy(solver_copy_fast=True)
            errored.solver.add_constraints(right == 0)
            self._put_in_errored(
                    errored, 
                    "DIVU_DP at %s (%d LLIL) division by zero" % (hex(errored.get_ip()), self.llil_ip)
                )

        self.state.solver.add_constraints(right != 0)
        if not self.state.solver.satisfiable():
            self._put_in_unsat(self.state)
            self.state = None
            return ErrorInstruction.DIVISION_BY_ZERO

        div = left / right
        return z3.simplify(z3.Extract(expr.size * 8 - 1, 0, div))
    
    def visit_LLIL_DIVS_DP(self, expr):  # is it correct?
        left = self.visit(expr.left)
        right = self.visit(expr.right)

        self._check_unsupported(left,  expr.left )
        self._check_unsupported(right, expr.right)
        if self._check_error(left):  return left
        if self._check_error(right): return right

        assert left.size() == 2*right.size()

        right = z3.SignExt(left.size() - right.size(), right)
        if CHECK_DIVISION_BY_ZERO and self.state.solver.satisfiable(extra_constraints=[right == 0]):
            print("WARNING: division by zero detected")
            errored = self.state.copy(solver_copy_fast=True)
            errored.solver.add_constraints(right == 0)
            self._put_in_errored(
                    errored, 
                    "DIVS_DP at %s (%d LLIL) division by zero" % (hex(errored.get_ip()), self.llil_ip)
                )

        self.state.solver.add_constraints(right != 0)
        if not self.state.solver.satisfiable():
            self._put_in_unsat(self.state)
            self.state = None
            return ErrorInstruction.DIVISION_BY_ZERO
        
        div = left / right
        return z3.simplify(z3.Extract(expr.size * 8 - 1, 0, div))
    
    def visit_LLIL_MODU_DP(self, expr):
        left = self.visit(expr.left)
        right = self.visit(expr.right)

        self._check_unsupported(left,  expr.left )
        self._check_unsupported(right, expr.right)
        if self._check_error(left):  return left
        if self._check_error(right): return right

        assert left.size() == 2*right.size()

        right = z3.ZeroExt(left.size() - right.size(), right)
        if CHECK_DIVISION_BY_ZERO and self.state.solver.satisfiable(extra_constraints=[right == 0]):
            print("WARNING: division by zero detected")
            errored = self.state.copy(solver_copy_fast=True)
            errored.solver.add_constraints(right == 0)
            self._put_in_errored(
                    errored, 
                    "MODU_DP at %s (%d LLIL) division by zero" % (hex(errored.get_ip()), self.llil_ip)
                )

        self.state.solver.add_constraints(right != 0)
        if not self.state.solver.satisfiable():
            self._put_in_unsat(self.state)
            self.state = None
            return ErrorInstruction.DIVISION_BY_ZERO

        mod = left % right
        return z3.simplify(z3.Extract(expr.size * 8 - 1, 0, mod))

    def visit_LLIL_MODS_DP(self, expr):  # is it correct?
        left = self.visit(expr.left)
        right = self.visit(expr.right)

        self._check_unsupported(left,  expr.left )
        self._check_unsupported(right, expr.right)
        if self._check_error(left):  return left
        if self._check_error(right): return right

        assert left.size() == 2*right.size()

        right = z3.SignExt(left.size() - right.size(), right)
        if CHECK_DIVISION_BY_ZERO and self.state.solver.satisfiable(extra_constraints=[right == 0]):
            print("WARNING: division by zero detected")
            errored = self.state.copy(solver_copy_fast=True)
            errored.solver.add_constraints(right == 0)
            self._put_in_errored(
                    errored, 
                    "MODS_DP at %s (%d LLIL) division by zero" % (hex(errored.get_ip()), self.llil_ip)
                )

        self.state.solver.add_constraints(right != 0)
        if not self.state.solver.satisfiable():
            self._put_in_unsat(self.state)
            self.state = None
            return ErrorInstruction.DIVISION_BY_ZERO

        mod = left % right
        return z3.simplify(z3.Extract(expr.size * 8 - 1, 0, mod))

    def visit_LLIL_AND(self, expr):
        left = self.visit(expr.left)
        right = self.visit(expr.right)

        self._check_unsupported(left,  expr.left )
        self._check_unsupported(right, expr.right)
        if self._check_error(left):  return left
        if self._check_error(right): return right

        self._check_unsupported(left,  expr.left )
        self._check_unsupported(right, expr.right)

        if right.size() > left.size():
            left = z3.ZeroExt(right.size() - left.size(), left)
        if left.size() > right.size():
            right = z3.ZeroExt(left.size() - right.size(), right)

        return z3.simplify(left & right)

    def visit_LLIL_OR(self, expr):
        left  = self.visit(expr.left)
        right = self.visit(expr.right)

        self._check_unsupported(left,  expr.left )
        self._check_unsupported(right, expr.right)
        if self._check_error(left):  return left
        if self._check_error(right): return right

        if right.size() > left.size():
            left = z3.ZeroExt(right.size() - left.size(), left)
        if left.size() > right.size():
            right = z3.ZeroExt(left.size() - right.size(), right)
        
        return z3.simplify(left | right)

    def visit_LLIL_XOR(self, expr):
        left = self.visit(expr.left)
        right = self.visit(expr.right)

        self._check_unsupported(left,  expr.left )
        self._check_unsupported(right, expr.right)
        if self._check_error(left):  return left
        if self._check_error(right): return right

        if right.size() > left.size():
            left = z3.ZeroExt(right.size() - left.size(), left)
        if left.size() > right.size():
            right = z3.ZeroExt(left.size() - right.size(), right)

        return z3.simplify(left ^ right)

    def visit_LLIL_NOT(self, expr):
        src = self.visit(expr.src)

        self._check_unsupported(src,  expr.src)
        if self._check_error(src):  return src

        return z3.simplify( src.__invert__() )

    def visit_LLIL_NEG(self, expr):
        src = self.visit(expr.src)

        self._check_unsupported(src,  expr.src)
        if self._check_error(src):  return src

        return z3.simplify( src.__neg__() )

    def visit_LLIL_LOAD(self, expr):
        src  = self.visit(expr.src)
        size = expr.size

        self._check_unsupported(src, expr.src)
        if self._check_error(src):  return src
        
        loaded = self.state.mem.load(src, size, endness=self.arch.endness())

        return loaded

    def visit_LLIL_STORE(self, expr):
        dest = self.visit(expr.dest)
        src  = self.visit(expr.src)

        self._check_unsupported(dest, expr.dest)
        self._check_unsupported(src,  expr.src )
        if self._check_error(src):  return src
        if self._check_error(dest):  return dest

        self.state.mem.store(dest, src, endness=self.arch.endness())
        return True

    def visit_LLIL_LSL(self, expr):
        left = self.visit(expr.left)
        right = self.visit(expr.right)

        assert right.size() <= left.size()

        self._check_unsupported(left,  expr.left )
        self._check_unsupported(right, expr.right)
        if self._check_error(left):  return left
        if self._check_error(right): return right

        # the logical and arithmetic left-shifts are exactly the same
        return z3.simplify(left << z3.ZeroExt(left.size() - right.size(), right))

    def visit_LLIL_LSR(self, expr):
        left = self.visit(expr.left)
        right = self.visit(expr.right)

        assert right.size() <= left.size()

        self._check_unsupported(left,  expr.left )
        self._check_unsupported(right, expr.right)
        if self._check_error(left):  return left
        if self._check_error(right): return right

        return z3.simplify(
            z3.LShR(
                left, 
                z3.ZeroExt(left.size() - right.size(), right)
            )
        )

    def visit_LLIL_ASL(self, expr):
        left = self.visit(expr.left)
        right = self.visit(expr.right)

        assert right.size() <= left.size()

        self._check_unsupported(left,  expr.left )
        self._check_unsupported(right, expr.right)
        if self._check_error(left):  return left
        if self._check_error(right): return right

        return z3.simplify(left << z3.ZeroExt(left.size() - right.size(), right))

    def visit_LLIL_ASR(self, expr):
        left = self.visit(expr.left)
        right = self.visit(expr.right)

        self._check_unsupported(left,  expr.left )
        self._check_unsupported(right, expr.right)
        if self._check_error(left):  return left
        if self._check_error(right): return right

        assert right.size() <= left.size()

        return z3.simplify(left >> z3.ZeroExt(left.size() - right.size(), right))

    def visit_LLIL_CALL(self, expr):
        dest = self.visit(expr.dest)

        self._check_unsupported(dest, expr.dest)
        if self._check_error(dest): return dest
        
        if symbolic(dest):
            raise Exception("symbolic IP")
        
        curr_fun = get_function(self.view, self.ip)
        dest_fun = self.view.get_function_at(dest.as_long())
        ret_addr = self.ip + self.view.get_instruction_length(self.ip)

        # push ret address
        self.state.stack_push(bvv(ret_addr, self.arch.bits()))

        # check if imported
        if dest.as_long() in self.imported_functions:
            name = self.imported_functions[dest.as_long()]
            if name not in library_functions:
                raise Exception("unsupported external function '%s'" % name)
            
            res = library_functions[name](self.state, self.view)
            setattr(self.state.regs, get_result_reg(self.state, self.view, res.size()), res)
            
            dest = self.state.stack_pop()
            dest_fun = curr_fun 
            assert not symbolic(dest)  # cannot happen (right?)

        # change ip
        self.update_ip(dest_fun, dest_fun.llil.get_instruction_start(dest.as_long()))

        self._wasjmp = True
        return True
    
    def visit_LLIL_IF(self, expr):
        condition = self.visit(expr.condition)
        true_llil_index = expr.true
        false_llil_index = expr.false

        self._check_unsupported(condition, expr.condition)
        if self._check_error(condition): return condition
        
        if isinstance(condition, z3.BitVecRef):
            assert condition.size() == 1
            condition = condition == 1
        curr_fun = get_function(self.view, self.ip)
        false_unsat = False
        if self.state.solver.satisfiable([z3.Not(condition)]):
            false_state = self.state.copy()
        else:
            false_unsat = True
            false_state = self.state.copy(solver_copy_fast=True)

        self.state.solver.add_constraints(condition)
        if self.state.solver.satisfiable():
            self.update_ip(curr_fun, true_llil_index)
        else:
            self._put_in_unsat(self.state)
            self.state = None

        false_state.solver.add_constraints(z3.Not(condition))
        if not false_unsat:
            false_state.set_ip(curr_fun.llil[false_llil_index].address)
            false_state.llil_ip = false_llil_index
            if self.state is None:
                self.set_current_state(false_state)
            else:
                self._put_in_deferred(false_state)
        else:
            self._put_in_unsat(false_state)
        
        self._wasjmp = True
        return True

    def visit_LLIL_CMP_E(self, expr):
        left = self.visit(expr.left)
        right = self.visit(expr.right)

        self._check_unsupported(left,  expr.left )
        self._check_unsupported(right, expr.right)
        if self._check_error(left):  return left
        if self._check_error(right): return right
        
        return z3.simplify(left == right)

    def visit_LLIL_CMP_NE(self, expr):
        left = self.visit(expr.left)
        right = self.visit(expr.right)

        self._check_unsupported(left,  expr.left )
        self._check_unsupported(right, expr.right)
        if self._check_error(left):  return left
        if self._check_error(right): return right
        
        return z3.simplify(left != right)

    def visit_LLIL_CMP_SLT(self, expr):
        left = self.visit(expr.left)
        right = self.visit(expr.right)

        self._check_unsupported(left,  expr.left )
        self._check_unsupported(right, expr.right)
        if self._check_error(left):  return left
        if self._check_error(right): return right
        
        return z3.simplify(left < right)

    def visit_LLIL_CMP_ULT(self, expr):
        left = self.visit(expr.left)
        right = self.visit(expr.right)

        self._check_unsupported(left,  expr.left )
        self._check_unsupported(right, expr.right)
        if self._check_error(left):  return left
        if self._check_error(right): return right
        
        return z3.simplify(z3.ULT(left, right))

    def visit_LLIL_CMP_SLE(self, expr):
        left = self.visit(expr.left)
        right = self.visit(expr.right)

        self._check_unsupported(left,  expr.left )
        self._check_unsupported(right, expr.right)
        if self._check_error(left):  return left
        if self._check_error(right): return right
        
        return z3.simplify(left <= right)

    def visit_LLIL_CMP_ULE(self, expr):
        left = self.visit(expr.left)
        right = self.visit(expr.right)

        self._check_unsupported(left,  expr.left )
        self._check_unsupported(right, expr.right)
        if self._check_error(left):  return left
        if self._check_error(right): return right
        
        return z3.simplify(z3.ULE(left, right))

    def visit_LLIL_CMP_SGT(self, expr):
        left = self.visit(expr.left)
        right = self.visit(expr.right)

        self._check_unsupported(left,  expr.left )
        self._check_unsupported(right, expr.right)
        if self._check_error(left):  return left
        if self._check_error(right): return right
        
        return z3.simplify(left > right)

    def visit_LLIL_CMP_UGT(self, expr):
        left = self.visit(expr.left)
        right = self.visit(expr.right)

        self._check_unsupported(left,  expr.left )
        self._check_unsupported(right, expr.right)
        if self._check_error(left):  return left
        if self._check_error(right): return right
        
        return z3.simplify(z3.UGT(left, right))

    def visit_LLIL_CMP_SGE(self, expr):
        left = self.visit(expr.left)
        right = self.visit(expr.right)

        self._check_unsupported(left,  expr.left )
        self._check_unsupported(right, expr.right)
        if self._check_error(left):  return left
        if self._check_error(right): return right
        
        return z3.simplify(left >= right)

    def visit_LLIL_CMP_UGE(self, expr):
        left = self.visit(expr.left)
        right = self.visit(expr.right)

        self._check_unsupported(left,  expr.left )
        self._check_unsupported(right, expr.right)
        if self._check_error(left):  return left
        if self._check_error(right): return right
        
        return z3.simplify(z3.UGE(left, right))

    def visit_LLIL_GOTO(self, expr):
        dest = expr.dest

        curr_fun = get_function(self.view, self.ip)
        self.update_ip(curr_fun, dest)
        
        self._wasjmp = True
        return True

    def visit_LLIL_RET(self, expr):
        dest = self.visit(expr.dest)

        self._check_unsupported(dest, expr.dest)
        if self._check_error(dest): return dest

        if symbolic(dest):
            raise Exception("symbolic IP")
        
        dest_fun = get_function(self.view, dest.as_long())
        self.update_ip(dest_fun, dest_fun.llil.get_instruction_start(dest.as_long()))

        self._wasjmp = True
        return True

    def visit_LLIL_PUSH(self, expr):
        src = self.visit(expr.src)

        self._check_unsupported(src, expr.src)
        if self._check_error(src): return src
        
        self.state.stack_push(src)
        return True
    
    def visit_LLIL_POP(self, expr):
        return self.state.stack_pop()
    
    def visit_LLIL_SX(self, expr):
        src = self.visit(expr.src)
        dest_size = expr.size * 8

        self._check_unsupported(src, expr.src)
        if self._check_error(src): return src

        assert src.size() <= dest_size

        return z3.SignExt(dest_size - src.size(), src) 

    def visit_LLIL_ZX(self, expr):
        src = self.visit(expr.src)
        dest_size = expr.size * 8

        self._check_unsupported(src, expr.src)
        if self._check_error(src): return src

        assert src.size() <= dest_size

        return z3.ZeroExt(dest_size - src.size(), src) 

    def visit_LLIL_SYSCALL(self, expr):
        n_reg = self.state.os.get_syscall_n_reg()
        n = getattr(self.state.regs, n_reg)
        assert not symbolic(n)
        n = n.as_long()
        
        handler = self.state.os.get_syscall_by_number(n)
        if handler is None:
            raise Exception("Unsopported syscall #%d" % n)
        
        res = handler(self.state)
        res_reg = self.state.os.get_out_syscall_reg()
        setattr(self.state.regs, res_reg, res)

        return True

    # def visit_LLIL_NORET(self, expr):
    #     log_alert("VM Halted.")
