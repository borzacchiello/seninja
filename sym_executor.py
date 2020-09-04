from binaryninja import (
    BinaryReader, BinaryWriter,
    RegisterValueType, enums
)
from .sym_visitor import SymbolicVisitor
from .sym_state import State
from .arch.arch_x86 import x86Arch
from .arch.arch_x86_64 import x8664Arch
from .arch.arch_armv7 import ArmV7Arch
from .utility.bninja_util import (
    get_imported_functions_and_addresses,
    find_os
)
from .expr import BVV, BVS
from .utility.binary_ninja_cache import BNCache
from .memory.sym_memory import InitData
from .multipath.fringe import Fringe
from .utility.error_codes import ErrorInstruction
from .utility.executor_utility import (
    check_unsupported,
    check_error
)

NO_COLOR = enums.HighlightStandardColor(0)
CURR_STATE_COLOR = enums.HighlightStandardColor.GreenHighlightColor
DEFERRED_STATE_COLOR = enums.HighlightStandardColor.RedHighlightColor
ERRORED_STATE_COLOR = enums.HighlightStandardColor.BlackHighlightColor


class SymbolicExecutor(object):
    def __init__(self, view, addr):

        self.view = view
        self.bw = BinaryWriter(view)
        self.br = BinaryReader(view)
        self.visitor = SymbolicVisitor(self)
        self.bncache = BNCache(view)
        self.vars = set()
        self.fringe = Fringe()
        self.ip = addr
        self.llil_ip = None
        self.arch = None
        self.user_hooks = dict()
        self.user_loggers = dict()
        self.imported_functions, self.imported_addresses = \
            get_imported_functions_and_addresses(view)
        self._last_colored_ip = None
        self._last_error = None
        self.init_with_zero = self.bncache.get_setting(
            "init_reg_mem_with_zero") == "true"

        self._wasjmp = False
        if self.view.arch.name == "x86":
            self.arch = x86Arch()
        elif self.view.arch.name == "x86_64":
            self.arch = x8664Arch()
        elif self.view.arch.name == "armv7":
            self.arch = ArmV7Arch()

        assert self.arch is not None
        page_size = int(self.bncache.get_setting("memory.page_size"))
        self.state = State(self, arch=self.arch,
                           os=find_os(view), page_size=page_size)

        # load memory
        print("loading segments...")
        for segment in self.view.segments:
            start = segment.start
            end = segment.end
            size = segment.data_length
            print(segment, hex(start), "->", hex(size))

            if size == 0 and end - start != 0:
                size = end - start
                data = b"\x00" * size
            elif size == 0:
                continue
            else:
                self.br.seek(start)
                data = self.br.read(end-start)

            self.state.mem.mmap(
                self.state.address_page_aligned(start),
                self.state.address_page_aligned(end + self.state.mem.page_size - 1) -
                self.state.address_page_aligned(start),
                InitData(data, start - self.state.address_page_aligned(start))
            )
        print("loading finished!")

        current_function = self.bncache.get_function(addr)

        # initialize stack

        stack_page_size = int(self.bncache.get_setting("stack_size"))

        unmapped_page_init = self.state.mem.get_unmapped(
            stack_page_size,
            start_from=(0x80 << (self.arch.bits() - 8)))
        self.state.mem.mmap(
            unmapped_page_init*self.state.page_size,
            self.state.page_size * stack_page_size)
        # leave one page for upper stack portion
        p = unmapped_page_init + stack_page_size - 1
        stack_base = p * self.state.page_size - self.arch.bits() // 8

        self.state.initialize_stack(stack_base)

        # initialize registers
        for reg in self.arch.regs_data():
            reg_dict = self.arch.regs_data()[reg]
            val = current_function.get_reg_value_after(addr, reg)

            if val.type.value == RegisterValueType.StackFrameOffset:
                setattr(self.state.regs, reg, BVV(
                    stack_base + val.offset, reg_dict['size'] * 8))
            elif (
                val.type.value == RegisterValueType.ConstantPointerValue or
                val.type.value == RegisterValueType.ConstantValue
            ):
                setattr(self.state.regs, reg, BVV(
                    val.value, reg_dict['size'] * 8))
            else:
                if not self.init_with_zero:
                    symb = BVS(reg + "_init", reg_dict['size'] * 8)
                    self.vars.add(symb)
                    setattr(self.state.regs, reg, symb)
                else:
                    setattr(self.state.regs, reg, BVV(0, reg_dict['size'] * 8))

        # initialize known local variables
        stack_vars = current_function.stack_layout
        for var in stack_vars:
            offset = var.storage
            s_type = var.type

            if abs(offset) > self.state.page_size * (stack_page_size - 1):
                print("ERROR: not enough space in stack. Increase stack size")
                raise Exception(
                    "Not enough space in stack. Increase stack size")

            if s_type.confidence != 255:
                continue

            width = s_type.width
            name = var.name
            val = current_function.get_stack_contents_at(addr, offset, width)
            if val.type.value == RegisterValueType.StackFrameOffset:
                assert width*8 == self.arch.bits()  # has to happen... right?
                self.state.mem.store(
                    BVV(stack_base + offset, self.arch.bits()),
                    BVV(stack_base + val.offset, width*8),
                    endness=self.arch.endness())
            elif (
                val.type.value == RegisterValueType.ConstantPointerValue or
                val.type.value == RegisterValueType.ConstantValue
            ):
                self.state.mem.store(
                    BVV(stack_base + offset, self.arch.bits()),
                    BVV(val.value, width*8),
                    endness=self.arch.endness())
            elif not self.init_with_zero:
                symb = BVS(name + "_init", self.arch.bits())
                self.vars.add(symb)
                self.state.mem.store(
                    BVV(stack_base + offset, self.arch.bits()),
                    symb,
                    endness=self.arch.endness())

        # set eip
        self.state.set_ip(addr)
        self.llil_ip = current_function.llil.get_instruction_start(addr)

    def __str__(self):
        return "<SymExecutor id: 0x%x, %d states>" % \
            (id(self), self.fringe.num_states + 1 if self.state is not None else 0)

    def __repr__(self):
        return self.__str__()

    def _handle_error(self, err):
        if err in {
            ErrorInstruction.DIVISION_BY_ZERO,
            ErrorInstruction.UNMAPPED_READ,
            ErrorInstruction.UNMAPPED_WRITE,
            ErrorInstruction.NO_DEST,
            ErrorInstruction.UNCONSTRAINED_IP,
            ErrorInstruction.UNSAT_STATE
        }:
            self.state = None
            self._last_error = err
            print("WARNING: changing current state due to %s" % err.name)
            return

        raise Exception("Unknown error")

    def put_in_deferred(self, state):
        self.fringe.add_deferred(state)

    def put_in_unsat(self, state):
        save_unsat = self.bncache.get_setting("save_unsat") == 'true'
        if save_unsat:
            self.fringe.add_unsat(state)

    def put_in_errored(self, state, msg: str):
        self.fringe.add_errored(
            (msg, state)
        )

    def set_colors(self, reset=False):
        old_ip = self._last_colored_ip
        if old_ip is not None:
            old_func = self.bncache.get_function(old_ip)
            old_func.set_auto_instr_highlight(old_ip, NO_COLOR)

        for ip in self.fringe._deferred:
            func = self.bncache.get_function(ip)
            func.set_auto_instr_highlight(
                ip, DEFERRED_STATE_COLOR if not reset else NO_COLOR)
            # func.set_comment_at(ip, str(len(self.fringe._deferred[ip]) if not reset else ""))

        for _, state in self.fringe.errored:
            func = self.bncache.get_function(state.get_ip())
            func.set_auto_instr_highlight(
                state.get_ip(), ERRORED_STATE_COLOR if not reset else NO_COLOR)

        if self.state:
            func = self.bncache.get_function(self.ip)
            func.set_auto_instr_highlight(
                self.ip, CURR_STATE_COLOR if not reset else NO_COLOR)
        if not reset:
            self._last_colored_ip = self.ip

    def reset(self):
        self.set_colors(reset=True)

    def set_current_state(self, state):
        if self.state is not None:
            self.state.llil_ip = self.llil_ip
            self.put_in_deferred(self.state)
            self.state = None

        ip = state.get_ip()
        llil_ip = state.llil_ip

        self.state = state
        new_func = self.bncache.get_function(ip)
        self.ip = ip
        self.llil_ip = new_func.llil.get_instruction_start(
            ip) if llil_ip is None else llil_ip

    def select_from_deferred(self):
        if self.fringe.is_empty():
            return False

        state = self.fringe.get_one_deferred()
        self.set_current_state(state)
        return True

    def update_ip(self, funcion_name, new_llil_ip):
        self.llil_ip = new_llil_ip
        self.ip = self.bncache.get_address(funcion_name, new_llil_ip)
        self.state.set_ip(self.ip)
        self.state.llil_ip = new_llil_ip

    def _execute_one(self):
        self._last_error = None
        func_name = self.bncache.get_function_name(self.ip)

        # handle user hooks and loggers
        if self.ip in self.user_loggers:
            self.user_loggers[self.ip](self.state)
        if self.ip in self.user_hooks:
            old_ip = self.ip
            new_state, new_deferred, new_errored = self.user_hooks[self.ip](
                self.state)

            for s in new_deferred:
                self.put_in_deferred(s)
            for s, msg in new_errored:
                self.put_in_errored(s, msg)

            if new_state is not None:
                self.state = new_state

                if old_ip == self.state.get_ip():
                    new_ip = self.ip + \
                        self.bncache.get_instruction_len(self.ip)
                else:
                    new_ip = self.state.get_ip()

                dest_func_name = self.bncache.get_function_name(
                    new_ip
                )
                self.update_ip(
                    dest_func_name,
                    self.bncache.get_llil_address(dest_func_name, new_ip)
                )
                return self.ip

        else:
            # check if a special handler is defined

            dont_use_special_handlers = \
                self.bncache.get_setting("dont_use_special_handlers") == 'true'
            disasm_str = self.bncache.get_disasm(self.ip)
            if (
                dont_use_special_handlers or
                not self.arch.execute_special_handler(disasm_str, self)
            ):
                expr = self.bncache.get_llil(func_name, self.llil_ip)
                res = self.visitor.visit(expr)

                if res is None:
                    raise Exception("")

                check_unsupported(res, expr)
                if check_error(res):
                    self._handle_error(res)

        if self.state is None:
            if self.fringe.is_empty():
                print("WARNING: no more states")
                return -1
            else:
                self.select_from_deferred()
                self._wasjmp = True

        if not self._wasjmp:
            # go on by 1 instruction
            self.update_ip(func_name, self.llil_ip + 1)
        else:
            self._wasjmp = False

        return self.ip

    def execute_one(self):
        if not self.state:
            return

        single_llil_step = self.bncache.get_setting(
            "single_llil_step") == 'true'
        if single_llil_step:
            res = self._execute_one()
        else:
            old_ip = self.ip
            res = old_ip
            while res == old_ip:
                res = self._execute_one()
        return res
