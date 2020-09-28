from PySide2.QtWidgets import (
    QDialog,
    QLineEdit,
    QPushButton,
    QGridLayout,
    QLabel,
    QComboBox
)
from binaryninja.interaction import show_message_box


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

        self._layout.addWidget(self.add_conc_button, 0, 0, 1, 1)
        self._layout.addWidget(self.add_symb_button, 0, 1, 1, 1)
        self._layout.addWidget(self.label, 1, 0, 2, 1)

        self.setLayout(self._outerLayout)

    def update_label_args(self):
        self.label.setText("Number of args: " + str(self.n_args))

    def onConcClick(self):
        self.n_args += 1
        self.update_label_args()

        label = QLabel(str(self.n_args) + ": ")
        line_edit = QLineEdit("arg value...")

        self._layout.addWidget(label, self.n_args + 2, 0, 1, 1)
        self._layout.addWidget(line_edit, self.n_args + 2, 1, 1, 1)

        self.args.append(
            (label, line_edit)
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
        self._layout.addWidget(combo_box, self.n_args + 2, 1, 1, 1)

        self.args.append(
            (label, combo_box)
        )

    def onOkClick(self):
        print("Ok clicked")

    def onCancelClick(self):
        print("Cancel clicked")
