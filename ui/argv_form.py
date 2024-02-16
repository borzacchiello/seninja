from PySide6.QtWidgets import (
    QDialog,
    QLineEdit,
    QPushButton,
    QGridLayout,
    QLabel,
    QComboBox
)
from binaryninja.interaction import show_message_box
from ..utility.string_util import str_to_bv, str_to_bv_list
from ..expr import BVV, BV
from ..globals import Globals

import sys

class GetArgvDialog(QDialog):
    def __init__(self, state, parent=None):
        super(GetArgvDialog, self).__init__(parent)
        self.state = state

        self.setWindowTitle('Setup argv')

        self._outerLayout = QGridLayout()
        self._layout = QGridLayout()
        self._outerLayout.addLayout(self._layout, 0, 0, 1, 2)

        self.okButton = QPushButton("Ok")
        self.okButton.clicked.connect(self.onOkClick)
        self.cancelButton = QPushButton("Cancel")
        self.cancelButton.clicked.connect(self.onCancelClick)

        self._outerLayout.addWidget(self.okButton, 2, 0, 1, 1)
        self._outerLayout.addWidget(self.cancelButton, 2, 1, 1, 1)

        self.n_args = 0
        self.args = list()

        self.add_conc_button = QPushButton("Add conc param")
        self.add_conc_button.clicked.connect(self.onConcClick)
        self.add_symb_button = QPushButton("Add symb param")
        self.add_symb_button.clicked.connect(self.onSymbClick)

        self.label = QLabel("Number of args: " + str(self.n_args))

        self._layout.addWidget(self.add_conc_button, 0, 0, 1, 5)
        self._layout.addWidget(self.add_symb_button, 0, 5, 1, 5)
        self._layout.addWidget(self.label, 1, 0, 1, 10)

        self.setLayout(self._outerLayout)

    def update_label_args(self):
        self.label.setText("Number of args: " + str(self.n_args))

    def onConcClick(self):
        self.n_args += 1
        self.update_label_args()

        label = QLabel(str(self.n_args) + ": ")
        line_edit = QLineEdit("arg value...")

        self._layout.addWidget(label, self.n_args + 2, 0, 1, 1)
        self._layout.addWidget(line_edit, self.n_args + 2, 1, 1, 9)

        self.args.append(
            ("conc", label, line_edit)
        )

    def onSymbClick(self):
        self.n_args += 1
        self.update_label_args()

        label = QLabel(str(self.n_args) + ": ")
        combo_box = QComboBox()
        buffer_names = [
            b[0].name for b in self.state.symbolic_buffers]

        if len(buffer_names) == 0:
            show_message_box("Error", "No symbolic buffer")
            return

        for name in buffer_names:
            combo_box.addItem(name)

        self._layout.addWidget(label, self.n_args + 2, 0, 1, 1)
        self._layout.addWidget(combo_box, self.n_args + 2, 1, 1, 9)

        self.args.append(
            ("symb", label, combo_box)
        )

    def _get_buff_from_name(self, name):
        for buff, _, _ in self.state.symbolic_buffers:
            if buff.name == name:
                return buff
        return None

    def _get_arguments(self):
        res = list()
        for t, _, obj in self.args:
            if t == "conc":
                res.append(str_to_bv(obj.text(), True))
            else:
                buff = self._get_buff_from_name(
                    obj.currentText())
                assert buff is not None
                res.append(buff.Concat(BVV(0, 8)))
        return res

    def onOkClick(self):
        args = self._get_arguments()
        GetArgvDialog.setup_argv(*args)
        self.accept()

    def onCancelClick(self):
        self.reject()

    @staticmethod
    def setup_argv(*args, argc_loc=None, argv_loc=None):
        filename = Globals.uimanager.executor.view.file.filename
        state = Globals.uimanager.executor.state
        argv_p = BVV(state.mem.allocate((len(args) + 1) *
                                        (state.arch.bits() // 8)), state.arch.bits())
        argv_1_p = BVV(state.mem.allocate(len(filename)), state.arch.bits())
        for i, b in enumerate(str_to_bv_list(filename, terminator=True)):
            state.mem.store(argv_1_p + i, b)
        state.mem.store(argv_p, argv_1_p, state.arch.endness())

        for i, arg in enumerate(args):
            if not isinstance(arg, BV):
                sys.stderr.write("SENinja [error]: %s is not a BitVector\n" % str(arg))
                return
            argv_el_p = BVV(state.mem.allocate(
                arg.size // 8 + 1), state.arch.bits())
            state.mem.store(argv_el_p, arg)
            state.mem.store(argv_p + (i + 1) *
                            (state.arch.bits() // 8), argv_el_p, state.arch.endness())

        argc = BVV(len(args) + 1, state.arch.bits())
        if argc_loc is None:
            current_function = Globals.uimanager.executor.bncache.get_function(
                Globals.uimanager.executor.ip)
            argc_loc = current_function.calling_convention.int_arg_regs[0]

        if isinstance(argc_loc, str):
            setattr(state.regs, argc_loc, argc)
        elif isinstance(argc_loc, BV):
            state.mem.store(argc_loc, argc, state.arch.endness())
        else:
            sys.stderr.write("SENinja [error]: invalid argc_loc %s" % str(argc_loc))
            return

        if argv_loc is None:
            current_function = Globals.uimanager.executor.bncache.get_function(
                Globals.uimanager.executor.ip)
            argv_loc = current_function.calling_convention.int_arg_regs[1]

        if isinstance(argv_loc, str):
            setattr(state.regs, argv_loc, argv_p)
        elif isinstance(argv_loc, BV):
            state.mem.store(argv_loc, argv_p, state.arch.endness())
        else:
            sys.stderr.write("SENinja [error]: invalid argv_loc %s" % str(argv_loc))
            return
