from binaryninja import (
    BinaryReader, BinaryWriter, 
    RegisterValueType, enums
)
from .sym_state import State
from .arch.arch_x86 import x86Arch
from .arch.arch_x86_64 import x8664Arch
from .arch.arch_armv7 import ArmV7Arch
from .models.function_models import library_functions
from .utility.expr_wrap_util import (
    bvv_from_bytes, symbolic
)
from .expr import BV, BVV, BVS, Bool, ITE
from .utility.bninja_util import (
    get_imported_functions_and_addresses,
    find_os,
    parse_disasm_str
)
from .utility.binary_ninja_cache import BNCache
from .memory.sym_memory import InitData
from .multipath.fringe import Fringe
from .utility.error_codes import ErrorInstruction
from .utility.executor_utility import (
    check_unsupported, 
    check_error
)

class BNILVisitor(object):
    # thanks joshwatson
    # https://github.com/joshwatson/f-ing-around-with-binaryninja/blob/master/ep4-emulator/vm_visitor.py
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
    def __init__(self, executor):
        super(SymbolicVisitor, self).__init__()
        self.executor = executor

    def _handle_symbolic_ip(self, expr, max_sol):
        state = self.executor.state
        sols  = state.solver.evaluate_upto(expr, max_sol)
        return len(sols), sols

    # --- HANDLERS ---

    def visit_LLIL_CONST(self, expr):
        return BVV(expr.constant, expr.size * 8)

    def visit_LLIL_CONST_PTR(self, expr):
        return BVV(expr.constant, self.executor.arch.bits())

    def visit_LLIL_SET_REG(self, expr):
        dest = expr.dest.name
        src  = self.visit(expr.src)

        check_unsupported(src, expr.src)
        if check_error(src): return src

        # X86_64 fix
        if isinstance(self.executor.arch, x8664Arch):
            if dest in {
                'eax',  'ebx',  'ecx',  'edx',
                'edi',  'esi',  'esp',  'ebp',
                'r8d',  'r9d',  'r10d', 'r11d',
                'r12d', 'r13d', 'r14d', 'r15d'
            }:
                dest = ("r" + dest[1:]) if dest[0] == 'e' else dest[:-1]
                src  = src.ZeroExt(32)

        if isinstance(src, Bool):
            src = ITE(
                src,
                BVV(1, 1).ZeroExt(expr.dest.info.size*8-1),
                BVV(0, 1).ZeroExt(expr.dest.info.size*8-1)
            )

        setattr(self.executor.state.regs, dest, src)
        return True

    def visit_LLIL_REG(self, expr):
        src = expr.src
        return getattr(self.executor.state.regs, src.name)

    def visit_LLIL_REG_SPLIT(self, expr):
        lo = getattr(self.executor.state.regs, expr.lo.name)
        hi = getattr(self.executor.state.regs, expr.hi.name)

        return hi.Concat(lo)

    def visit_LLIL_SET_REG_SPLIT(self, expr):
        src = self.visit(expr.src)
        lo = expr.lo.name
        hi = expr.hi.name

        check_unsupported(src, expr.src)
        if check_error(src): return src

        lo_val = src.Extract(src.size // 2 - 1, 0)
        hi_val = src.Extract(src.size - 1, src.size // 2)

        setattr(self.executor.state.regs, lo, lo_val)
        setattr(self.executor.state.regs, hi, hi_val)
        return True

    def visit_LLIL_SET_FLAG(self, expr):
        dest = expr.dest.name
        src  = self.visit(expr.src)

        check_unsupported(src, expr.src)
        if check_error(src): return src

        if isinstance(src, Bool):
            res = ITE(src, BVV(1, 1), BVV(0, 1))
        else:
            res = ITE(src == 0, BVV(0, 1), BVV(1, 1))
        self.executor.state.regs.flags[dest] = res
        return True

    def visit_LLIL_FLAG(self, expr):
        src = expr.src.name
        return self.executor.state.regs.flags[src]

    def visit_LLIL_LOW_PART(self, expr):
        src = self.visit(expr.src)
        size = expr.size

        check_unsupported(src, expr.src)
        if check_error(src): return src

        return src.Extract(size*8-1, 0)

    def visit_LLIL_ADD(self, expr):
        left  = self.visit(expr.left)
        right = self.visit(expr.right)

        check_unsupported(left,  expr.left )
        check_unsupported(right, expr.right)
        if check_error(left):  return left
        if check_error(right): return right

        if right.size > left.size:
            left = left.SignExt(right.size - left.size)
        if left.size > right.size:
            right = right.SignExt(left.size - right.size)

        return left + right

    def visit_LLIL_ADC(self, expr):
        left  = self.visit(expr.left)
        right = self.visit(expr.right)
        carry = self.visit(expr.carry)

        check_unsupported(left,  expr.left )
        check_unsupported(right, expr.right)
        check_unsupported(carry, expr.carry)
        if check_error(left):  return left
        if check_error(right): return right
        if check_error(carry): return carry

        if right.size > left.size:
            left = left.SignExt(right.size - left.size)
        if left.size > right.size:
            right = right.SignExt(left.size - right.size)

        return left + right + carry.ZeroExt(left.size - 1)

    def visit_LLIL_ADD_OVERFLOW(self, expr):
        left  = self.visit(expr.left)
        right = self.visit(expr.right)

        check_unsupported(left,  expr.left )
        check_unsupported(right, expr.right)
        if check_error(left):  return left
        if check_error(right): return right

        res = (BVV(0, 1).Concat(left) + BVV(0, 1).Concat(right))  # add with one more bit
        res = res.Extract(left.size, left.size)                   # check if overflow
        return res

    def visit_LLIL_SUB(self, expr):
        left  = self.visit(expr.left)
        right = self.visit(expr.right)

        check_unsupported(left,  expr.left )
        check_unsupported(right, expr.right)
        if check_error(left):  return left
        if check_error(right): return right

        if right.size > left.size:
            left = left.SignExt(right.size - left.size)
        if left.size > right.size:
            right = right.SignExt(left.size - right.size)

        return left - right

    def visit_LLIL_MUL(self, expr):
        left  = self.visit(expr.left)
        right = self.visit(expr.right)

        check_unsupported(left,  expr.left )
        check_unsupported(right, expr.right)
        if check_error(left):  return left
        if check_error(right): return right

        if right.size > left.size:
            left = left.SignExt(right.size - left.size)
        if left.size > right.size:
            right = right.SignExt(left.size - right.size)

        return left * right

    def visit_LLIL_MULS_DP(self, expr):
        left = self.visit(expr.left)
        right = self.visit(expr.right)

        check_unsupported(left,  expr.left )
        check_unsupported(right, expr.right)
        if check_error(left):  return left
        if check_error(right): return right

        assert left.size == right.size
        left  = left.SignExt(left.size)
        right = right.SignExt(right.size)
        return left * right

    def visit_LLIL_MULU_DP(self, expr):
        left = self.visit(expr.left)
        right = self.visit(expr.right)

        check_unsupported(left,  expr.left )
        check_unsupported(right, expr.right)
        if check_error(left):  return left
        if check_error(right): return right

        assert left.size == right.size
        left  = left.ZeroExt(left.size)
        right = right.ZeroExt(right.size)
        return left * right

    def visit_LLIL_DIVU_DP(self, expr):
        left = self.visit(expr.left)
        right = self.visit(expr.right)

        check_unsupported(left,  expr.left )
        check_unsupported(right, expr.right)
        if check_error(left):  return left
        if check_error(right): return right

        assert left.size == 2*right.size

        check_division_by_zero = self.executor.bncache.get_setting("check_division_by_zero") == 'true'
        
        right = right.ZeroExt(left.size - right.size)
        if check_division_by_zero and self.executor.state.solver.satisfiable(extra_constraints=[right == 0]):
            print("WARNING: division by zero detected")
            errored = self.executor.state.copy(solver_copy_fast=True)
            errored.solver.add_constraints(right == 0)
            self.executor.put_in_errored(
                    errored, 
                    "DIVU_DP at %s (%d LLIL) division by zero" % (hex(errored.get_ip()), self.executor.llil_ip)
                )

        self.executor.state.solver.add_constraints(right != 0)
        if not self.executor.state.solver.satisfiable():
            self.executor.put_in_errored(self.executor.state, "division by zero")
            return ErrorInstruction.DIVISION_BY_ZERO

        div = left.UDiv(right)
        return div.Extract(expr.size * 8 - 1, 0)
    
    def visit_LLIL_DIVS_DP(self, expr):  # is it correct?
        left = self.visit(expr.left)
        right = self.visit(expr.right)

        check_unsupported(left,  expr.left )
        check_unsupported(right, expr.right)
        if check_error(left):  return left
        if check_error(right): return right

        assert left.size == 2*right.size

        check_division_by_zero = self.executor.bncache.get_setting("check_division_by_zero") == 'true'

        right = right.SignExt(left.size - right.size)
        if check_division_by_zero and self.executor.state.solver.satisfiable(extra_constraints=[right == 0]):
            print("WARNING: division by zero detected")
            errored = self.executor.state.copy(solver_copy_fast=True)
            errored.solver.add_constraints(right == 0)
            self.executor.put_in_errored(
                    errored, 
                    "DIVS_DP at %s (%d LLIL) division by zero" % (hex(errored.get_ip()), self.executor.llil_ip)
                )

        self.executor.state.solver.add_constraints(right != 0)
        if not self.executor.state.solver.satisfiable():
            self.executor.put_in_errored(self.executor.state, "division by zero")
            return ErrorInstruction.DIVISION_BY_ZERO
        
        div = left / right
        return div.Extract(expr.size * 8 - 1, 0)
    
    def visit_LLIL_MODU_DP(self, expr):
        left = self.visit(expr.left)
        right = self.visit(expr.right)

        check_unsupported(left,  expr.left )
        check_unsupported(right, expr.right)
        if check_error(left):  return left
        if check_error(right): return right

        assert left.size == 2*right.size

        check_division_by_zero = self.executor.bncache.get_setting("check_division_by_zero") == 'true'

        right = right.ZeroExt(left.size - right.size)
        if check_division_by_zero and self.executor.state.solver.satisfiable(extra_constraints=[right == 0]):
            print("WARNING: division by zero detected")
            errored = self.executor.state.copy(solver_copy_fast=True)
            errored.solver.add_constraints(right == 0)
            self.executor.put_in_errored(
                    errored, 
                    "MODU_DP at %s (%d LLIL) division by zero" % (hex(errored.get_ip()), self.executor.llil_ip)
                )

        self.executor.state.solver.add_constraints(right != 0)
        if not self.executor.state.solver.satisfiable():
            self.executor.put_in_errored(self.executor.state, "division by zero")
            return ErrorInstruction.DIVISION_BY_ZERO

        mod = left.URem(right)
        return mod.Extract(expr.size * 8 - 1, 0)

    def visit_LLIL_MODS_DP(self, expr):  # is it correct?
        left = self.visit(expr.left)
        right = self.visit(expr.right)

        check_unsupported(left,  expr.left )
        check_unsupported(right, expr.right)
        if check_error(left):  return left
        if check_error(right): return right

        assert left.size == 2*right.size

        check_division_by_zero = self.executor.bncache.get_setting("check_division_by_zero") == 'true'

        right = right.SignExt(left.size - right.size)
        if check_division_by_zero and self.executor.state.solver.satisfiable(extra_constraints=[right == 0]):
            print("WARNING: division by zero detected")
            errored = self.executor.state.copy(solver_copy_fast=True)
            errored.solver.add_constraints(right == 0)
            self.executor.put_in_errored(
                    errored, 
                    "MODS_DP at %s (%d LLIL) division by zero" % (hex(errored.get_ip()), self.executor.llil_ip)
                )

        self.executor.state.solver.add_constraints(right != 0)
        if not self.executor.state.solver.satisfiable():
            self.executor.put_in_errored(self.executor.state, "division by zero")
            return ErrorInstruction.DIVISION_BY_ZERO

        mod = left.SRem(right)
        return mod.Extract(expr.size * 8 - 1, 0)

    def visit_LLIL_AND(self, expr):
        left = self.visit(expr.left)
        right = self.visit(expr.right)

        check_unsupported(left,  expr.left )
        check_unsupported(right, expr.right)
        if check_error(left):  return left
        if check_error(right): return right

        check_unsupported(left,  expr.left )
        check_unsupported(right, expr.right)

        if right.size > left.size:
            left = left.ZeroExt(right.size - left.size)
        if left.size > right.size:
            right = right.ZeroExt(left.size - right.size)

        return left & right

    def visit_LLIL_OR(self, expr):
        left  = self.visit(expr.left)
        right = self.visit(expr.right)

        check_unsupported(left,  expr.left )
        check_unsupported(right, expr.right)
        if check_error(left):  return left
        if check_error(right): return right

        if right.size > left.size:
            left = left.ZeroExt(right.size - left.size)
        if left.size > right.size:
            right = right.ZeroExt(left.size - right.size)
        
        return left | right

    def visit_LLIL_XOR(self, expr):
        left = self.visit(expr.left)
        right = self.visit(expr.right)

        check_unsupported(left,  expr.left )
        check_unsupported(right, expr.right)
        if check_error(left):  return left
        if check_error(right): return right

        if right.size > left.size:
            left = left.ZeroExt(right.size - left.size)
        if left.size > right.size:
            right = right.ZeroExt(left.size - right.size)

        return left ^ right

    def visit_LLIL_NOT(self, expr):
        src = self.visit(expr.src)

        check_unsupported(src,  expr.src)
        if check_error(src):  return src

        return src.__invert__()

    def visit_LLIL_NEG(self, expr):
        src = self.visit(expr.src)

        check_unsupported(src,  expr.src)
        if check_error(src):  return src

        return src.__neg__()

    def visit_LLIL_LOAD(self, expr):
        src  = self.visit(expr.src)
        size = expr.size

        check_unsupported(src, expr.src)
        if check_error(src):  return src
        
        loaded = self.executor.state.mem.load(src, size, endness=self.executor.arch.endness())

        return loaded

    def visit_LLIL_STORE(self, expr):
        dest = self.visit(expr.dest)
        src  = self.visit(expr.src)

        check_unsupported(dest, expr.dest)
        check_unsupported(src,  expr.src )
        if check_error(src):  return src
        if check_error(dest):  return dest

        self.executor.state.mem.store(dest, src, endness=self.executor.arch.endness())
        return True

    def visit_LLIL_LSL(self, expr):
        left = self.visit(expr.left)
        right = self.visit(expr.right)

        assert right.size <= left.size

        check_unsupported(left,  expr.left )
        check_unsupported(right, expr.right)
        if check_error(left):  return left
        if check_error(right): return right

        # the logical and arithmetic left-shifts are exactly the same
        return left << right.ZeroExt(left.size - right.size)

    def visit_LLIL_LSR(self, expr):
        left = self.visit(expr.left)
        right = self.visit(expr.right)

        assert right.size <= left.size

        check_unsupported(left,  expr.left )
        check_unsupported(right, expr.right)
        if check_error(left):  return left
        if check_error(right): return right

        return left.LShR(
            right.ZeroExt(left.size - right.size)
        )

    def visit_LLIL_ROR(self, expr):
        left = self.visit(expr.left)
        right = self.visit(expr.right)

        assert right.size <= left.size

        check_unsupported(left,  expr.left )
        check_unsupported(right, expr.right)
        if check_error(left):  return left
        if check_error(right): return right

        return left.RotateRight(
            right.ZeroExt(left.size - right.size)
        )

    def visit_LLIL_ROL(self, expr):
        left = self.visit(expr.left)
        right = self.visit(expr.right)

        assert right.size <= left.size

        check_unsupported(left,  expr.left )
        check_unsupported(right, expr.right)
        if check_error(left):  return left
        if check_error(right): return right

        return left.RotateLeft(
            right.ZeroExt(left.size - right.size)
        )

    def visit_LLIL_ASL(self, expr):
        left = self.visit(expr.left)
        right = self.visit(expr.right)

        assert right.size <= left.size

        check_unsupported(left,  expr.left )
        check_unsupported(right, expr.right)
        if check_error(left):  return left
        if check_error(right): return right

        return left << right.ZeroExt(left.size - right.size)

    def visit_LLIL_ASR(self, expr):
        left = self.visit(expr.left)
        right = self.visit(expr.right)

        check_unsupported(left,  expr.left )
        check_unsupported(right, expr.right)
        if check_error(left):  return left
        if check_error(right): return right

        assert right.size <= left.size

        return left >> right.ZeroExt(left.size - right.size)

    def visit_LLIL_CALL(self, expr):
        dest = self.visit(expr.dest)

        check_unsupported(dest, expr.dest)
        if check_error(dest): return dest
        
        if symbolic(dest):
            raise Exception("symbolic IP")
        
        curr_fun_name = self.executor.bncache.get_function_name(self.executor.ip)
        if dest.value in self.executor.imported_functions:
            dest_fun_name = self.executor.imported_functions[dest.value]
        else:
            dest_fun_name = self.executor.bncache.get_function_name(dest.value)
        ret_addr = self.executor.ip + self.executor.bncache.get_instruction_len(self.executor.ip)

        # save ret address
        self.executor.arch.save_return_address(self.executor.state, BVV(ret_addr, self.executor.arch.bits()))

        # check if we have an handler
        if dest_fun_name in library_functions:
            res = library_functions[dest_fun_name](self.executor.state, self.executor.view)

            dest_fun = self.executor.bncache.get_function(dest.value)
            self.executor.arch.save_result_value(self.executor.state, dest_fun.calling_convention, res)

            # retrive return address
            dest = self.executor.arch.get_return_address(self.executor.state)
            dest_fun_name = curr_fun_name
            assert not symbolic(dest)  # cannot happen (right?)

        # check if imported
        elif dest.value in self.executor.imported_functions:
            name = self.executor.imported_functions[dest.value]
            if name not in library_functions:
                raise Exception("unsupported external function '%s'" % name)
            
            res = library_functions[name](self.executor.state, self.executor.view)
            
            dest_fun = self.executor.bncache.get_function(dest.value)
            self.executor.arch.save_result_value(self.executor.state, dest_fun.calling_convention, res)
            
            # retrive return address
            dest = self.executor.arch.get_return_address(self.executor.state)
            dest_fun_name = curr_fun_name
            assert not symbolic(dest)  # cannot happen (right?)

        # change ip
        self.executor.update_ip(dest_fun_name, self.executor.bncache.get_llil_address(dest_fun_name, dest.value))

        self.executor._wasjmp = True
        return True
    
    def visit_LLIL_TAILCALL(self, expr):
        dest = self.visit(expr.dest)

        check_unsupported(dest, expr.dest)
        if check_error(dest): return dest
        
        if symbolic(dest):
            raise Exception("symbolic IP")
        
        if dest.value in self.executor.imported_functions:
            dest_fun_name = self.executor.imported_functions[dest.value]
        else:
            dest_fun_name = self.executor.bncache.get_function_name(dest.value)

        # check if we have an handler
        if dest_fun_name in library_functions:
            res = library_functions[dest_fun_name](self.executor.state, self.executor.view)

            dest_fun = self.executor.bncache.get_function(dest.value)
            self.executor.arch.save_result_value(self.executor.state, dest_fun.calling_convention, res)

            # retrive return address
            dest = self.executor.arch.get_return_address(self.executor.state)
            if symbolic(dest):
                raise Exception("symbolic IP") 

            dest_fun_name = self.executor.bncache.get_function_name(dest.value)

        # check if imported
        if dest.value in self.executor.imported_functions:
            name = self.executor.imported_functions[dest.value]
            if name not in library_functions:
                raise Exception("unsupported external function '%s'" % name)
            
            res = library_functions[name](self.executor.state, self.executor.view)
            
            dest_fun = self.executor.bncache.get_function(dest.value)
            self.executor.arch.save_result_value(self.executor.state, dest_fun.calling_convention, res)

            # retrive return address
            dest = self.executor.arch.get_return_address(self.executor.state)
            if symbolic(dest):
                raise Exception("symbolic IP") 

            dest_fun_name = self.executor.bncache.get_function_name(dest.value)

        # change ip
        self.executor.update_ip(dest_fun_name, self.executor.bncache.get_llil_address(dest_fun_name, dest.value))

        self.executor._wasjmp = True
        return True

    def visit_LLIL_JUMP(self, expr):
        destination = self.visit(expr.dest)

        check_unsupported(destination, expr.dest)
        if check_error(destination): return destination

        if not symbolic(destination):
            # fast path. The destination is concrete
            dest_fun_name = self.executor.bncache.get_function_name(destination.value)
            self.executor.update_ip(dest_fun_name, self.executor.bncache.get_llil_address(dest_fun_name, destination.value))
            self.executor._wasjmp = True
            return True
        
        assert False  # implement this

    def visit_LLIL_JUMP_TO(self, expr):
        destination = self.visit(expr.dest)

        check_unsupported(destination, expr.dest)
        if check_error(destination): return destination

        curr_fun_name = self.executor.bncache.get_function_name(self.executor.ip)

        if not symbolic(destination):
            # fast path. The destination is concrete
            self.executor.update_ip(curr_fun_name, self.executor.bncache.get_llil_address(curr_fun_name, destination.value))
            self.executor._wasjmp = True
            return True

        # symbolic IP path
        if self.executor.bncache.get_setting("use_bn_jumptable_targets") == 'true':
            max_num = len(expr.targets)
        else:
            max_num = 256
        num_ips, dest_ips = self._handle_symbolic_ip(destination, max_num)

        if num_ips == 256:
            self.executor.put_in_errored(self.executor.state, "Probably unconstrained IP")
            return ErrorInstruction.UNCONSTRAINED_IP

        if num_ips == 0:
            self.executor.put_in_errored(self.executor.state, "No valid destination")
            return ErrorInstruction.NO_DEST

        for ip in dest_ips[1:]:
            new_state = self.executor.state.copy()
            new_state.solver.add_constraints(
                destination == ip
            )
            new_state.set_ip(ip.value)
            new_state.llil_ip = self.executor.bncache.get_llil_address(curr_fun_name, ip.value)
            self.executor.put_in_deferred(new_state)

        self.executor.update_ip(curr_fun_name, self.executor.bncache.get_llil_address(curr_fun_name, dest_ips[0].value))
        self.executor.state.solver.add_constraints(dest_ips[0] == destination)
        self.executor._wasjmp = True
        return True

        # llil_indexes = expr.targets
        # current_constraint = None
        # for llil_index in llil_indexes:

        #     dst_ip = curr_fun.llil[llil_index].address
        #     if self.executor.state.solver.satisfiable([
        #         destination == dst_ip
        #     ]):
        #         if current_constraint is None:
        #             current_constraint = destination == dst_ip
        #             self.executor.update_ip(curr_fun, llil_index)
        #         else:
        #             new_state = self.executor.state.copy()
        #             new_state.solver.add_constraints(
        #                 destination == dst_ip
        #             )
        #             new_state.set_ip(dst_ip)
        #             new_state.llil_ip = llil_index
        #             self.executor.put_in_deferred(new_state)

        # if current_constraint is None:
        #     return ErrorInstruction.NO_DEST
        
        # self.executor.state.solver.add_constraints(current_constraint)
        # self.executor._wasjmp = True
        # return True

    def visit_LLIL_IF(self, expr):
        condition = self.visit(expr.condition)
        true_llil_index = expr.true
        false_llil_index = expr.false

        check_unsupported(condition, expr.condition)
        if check_error(condition): return condition

        save_unsat = self.executor.bncache.get_setting("save_unsat") == 'true'
        
        if isinstance(condition, BV):
            assert condition.size == 1
            condition = condition == 1
        curr_fun_name = self.executor.bncache.get_function_name(self.executor.ip)

        true_sat = True
        false_sat = True
        if not self.executor.state.solver.satisfiable(extra_constraints=[
            condition
        ]):
            true_sat = False
        if not self.executor.state.solver.satisfiable(extra_constraints=[
            condition.Not()
        ]):
            false_sat = False
        
        if true_sat and false_sat:
            true_state = self.executor.state
            false_state = self.executor.state.copy()

            true_state.solver.add_constraints(condition)
            self.executor.update_ip(curr_fun_name, true_llil_index)

            false_state.solver.add_constraints(condition.Not())
            false_state.set_ip(self.executor.bncache.get_address(curr_fun_name, false_llil_index))
            false_state.llil_ip = false_llil_index
            self.executor.put_in_deferred(false_state)
        elif true_sat and not false_sat:
            true_state = self.executor.state
            false_state = self.executor.state.copy() if save_unsat else None

            true_state.solver.add_constraints(condition)
            self.executor.update_ip(curr_fun_name, true_llil_index)

            if save_unsat:
                false_state.solver.add_constraints(condition.Not())
                false_state.set_ip(self.executor.bncache.get_address(curr_fun_name, false_llil_index))
                false_state.llil_ip = false_llil_index
                self.executor.put_in_unsat(false_state)
        elif not true_sat and false_sat:
            false_state = self.executor.state
            true_state = self.executor.state.copy() if save_unsat else None

            false_state.solver.add_constraints(condition.Not())
            self.executor.state = false_state
            self.executor.update_ip(curr_fun_name, false_llil_index)

            if save_unsat:
                true_state.solver.add_constraints(condition)
                true_state.set_ip(self.executor.bncache.get_address(curr_fun_name, true_llil_index))
                true_state.llil_ip = true_llil_index
                self.executor.put_in_unsat(true_state)
        else:
            true_state  = self.executor.state.copy() if save_unsat else None
            false_state = self.executor.state.copy() if save_unsat else None

            if save_unsat:
                true_state.solver.add_constraints(condition)
                true_state.set_ip(self.executor.bncache.get_address(curr_fun_name, true_llil_index))
                true_state.llil_ip = true_llil_index
                self.executor.put_in_unsat(true_state)
                false_state.solver.add_constraints(condition.Not())
                false_state.set_ip(self.executor.bncache.get_address(curr_fun_name, false_llil_index))
                false_state.llil_ip = false_llil_index
                self.executor.put_in_unsat(false_state)

            self.executor.put_in_unsat(self.executor.state)
            return ErrorInstruction.UNSAT_STATE

        self.executor._wasjmp = True
        return True

    def visit_LLIL_CMP_E(self, expr):
        left = self.visit(expr.left)
        right = self.visit(expr.right)

        check_unsupported(left,  expr.left )
        check_unsupported(right, expr.right)
        if check_error(left):  return left
        if check_error(right): return right
        
        return left == right

    def visit_LLIL_CMP_NE(self, expr):
        left = self.visit(expr.left)
        right = self.visit(expr.right)

        check_unsupported(left,  expr.left )
        check_unsupported(right, expr.right)
        if check_error(left):  return left
        if check_error(right): return right
        
        return left != right

    def visit_LLIL_CMP_SLT(self, expr):
        left = self.visit(expr.left)
        right = self.visit(expr.right)

        check_unsupported(left,  expr.left )
        check_unsupported(right, expr.right)
        if check_error(left):  return left
        if check_error(right): return right
        
        return left < right

    def visit_LLIL_CMP_ULT(self, expr):
        left = self.visit(expr.left)
        right = self.visit(expr.right)

        check_unsupported(left,  expr.left )
        check_unsupported(right, expr.right)
        if check_error(left):  return left
        if check_error(right): return right
        
        return left.ULT(right)

    def visit_LLIL_CMP_SLE(self, expr):
        left = self.visit(expr.left)
        right = self.visit(expr.right)

        check_unsupported(left,  expr.left )
        check_unsupported(right, expr.right)
        if check_error(left):  return left
        if check_error(right): return right
        
        return left <= right

    def visit_LLIL_CMP_ULE(self, expr):
        left = self.visit(expr.left)
        right = self.visit(expr.right)

        check_unsupported(left,  expr.left )
        check_unsupported(right, expr.right)
        if check_error(left):  return left
        if check_error(right): return right
        
        return left.ULE(right)

    def visit_LLIL_CMP_SGT(self, expr):
        left = self.visit(expr.left)
        right = self.visit(expr.right)

        check_unsupported(left,  expr.left )
        check_unsupported(right, expr.right)
        if check_error(left):  return left
        if check_error(right): return right
        
        return left > right

    def visit_LLIL_CMP_UGT(self, expr):
        left = self.visit(expr.left)
        right = self.visit(expr.right)

        check_unsupported(left,  expr.left )
        check_unsupported(right, expr.right)
        if check_error(left):  return left
        if check_error(right): return right
        
        return left.UGT(right)

    def visit_LLIL_CMP_SGE(self, expr):
        left = self.visit(expr.left)
        right = self.visit(expr.right)

        check_unsupported(left,  expr.left )
        check_unsupported(right, expr.right)
        if check_error(left):  return left
        if check_error(right): return right
        
        return left >= right

    def visit_LLIL_CMP_UGE(self, expr):
        left = self.visit(expr.left)
        right = self.visit(expr.right)

        check_unsupported(left,  expr.left )
        check_unsupported(right, expr.right)
        if check_error(left):  return left
        if check_error(right): return right
        
        return left.UGE(right)

    def visit_LLIL_GOTO(self, expr):
        dest = expr.dest

        curr_fun_name = self.executor.bncache.get_function_name(self.executor.ip) 
        self.executor.update_ip(curr_fun_name, dest)
        
        self.executor._wasjmp = True
        return True

    def visit_LLIL_RET(self, expr):
        dest = self.visit(expr.dest)

        check_unsupported(dest, expr.dest)
        if check_error(dest): return dest

        if symbolic(dest):
            num_ips, dest_ips = self._handle_symbolic_ip(dest, 256)

            if num_ips == 256:
                self.executor.put_in_errored(self.executor.state, "Probably unconstrained IP")
                return ErrorInstruction.UNCONSTRAINED_IP
            if num_ips == 0:
                self.executor.put_in_errored(self.executor.state, "No valid destination")
                return ErrorInstruction.NO_DEST
            
            for ip in dest_ips[1:]:
                dest_fun_name = self.executor.bncache.get_function_name(ip.value) 
                new_state = self.executor.state.copy()
                new_state.solver.add_constraints(
                    dest == ip
                )
                new_state.set_ip(ip.value)
                new_state.llil_ip = self.executor.bncache.get_llil_address(dest_fun_name, ip.value) 
                self.executor.put_in_deferred(new_state)
            
            dest_ip = dest_ips[0].value
        else:
            dest_ip = dest.value
        
        dest_fun_name = self.executor.bncache.get_function_name(dest_ip) 
        self.executor.update_ip(dest_fun_name, self.executor.bncache.get_llil_address(dest_fun_name, dest_ip)) 

        self.executor._wasjmp = True
        return True

    def visit_LLIL_PUSH(self, expr):
        src = self.visit(expr.src)

        check_unsupported(src, expr.src)
        if check_error(src): return src
        
        self.executor.state.stack_push(src)
        return True
    
    def visit_LLIL_POP(self, expr):
        return self.executor.state.stack_pop()
    
    def visit_LLIL_SX(self, expr):
        src = self.visit(expr.src)
        dest_size = expr.size * 8

        check_unsupported(src, expr.src)
        if check_error(src): return src

        assert src.size <= dest_size

        return src.SignExt(dest_size - src.size) 

    def visit_LLIL_ZX(self, expr):
        src = self.visit(expr.src)
        dest_size = expr.size * 8

        check_unsupported(src, expr.src)
        if check_error(src): return src

        assert src.size <= dest_size

        return src.ZeroExt(dest_size - src.size) 

    def visit_LLIL_SYSCALL(self, expr):
        n_reg = self.executor.state.os.get_syscall_n_reg()
        n = getattr(self.executor.state.regs, n_reg)
        assert not symbolic(n)
        n = n.value
        
        handler = self.executor.state.os.get_syscall_by_number(n)
        if handler is None:
            raise Exception("Unsopported syscall #%d" % n)
        
        res = handler(self.executor.state)
        res_reg = self.executor.state.os.get_out_syscall_reg()
        setattr(self.executor.state.regs, res_reg, res)

        return True

    # def visit_LLIL_NORET(self, expr):
    #     log_alert("VM Halted.")
