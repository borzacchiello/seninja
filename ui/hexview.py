# based on https://github.com/williballenthin/python-pyqt5-hexview

from PySide2.QtCore import (
    Qt,
    Signal,
    QSize,
    QCoreApplication,
    QMetaObject,
    QModelIndex,
    QAbstractTableModel,
    QItemSelectionModel,
    QItemSelection
)
from PySide2.QtWidgets import (
    QApplication, 
    QTableView, 
    QWidget, 
    QTableWidgetItem, 
    QMainWindow,
    QFormLayout,
    QVBoxLayout,
    QLabel,
    QSizePolicy,
    QAbstractItemView,
    QMenu,
    QHeaderView,
    QItemDelegate,
    QSizePolicy
)
from PySide2.QtGui import (
    QMouseEvent,
    QKeySequence,
    QFontDatabase
)

def row_start_index(index):
    """ get index of the start of the 0x10 byte row containing the given index """
    return index - (index % 0x10)


def row_end_index(index):
    """ get index of the end of the 0x10 byte row containing the given index """
    return index - (index % 0x10) + 0xF


def row_number(index):
    """ get row number of the 0x10 byte row containing the given index """
    return index // 0x10


def column_number(index):
    return index % 0x10

def is_int(val):
    try:
        int(val, 16)
        return True
    except:
        pass
    return False

class HexItemDelegate(QItemDelegate):
    def __init__(self, model, parent, *args):
        super(HexItemDelegate, self).__init__(parent)
        self._model = model

    # def editorEvent(self, event, model, option, index):
    #     print(event, model, option, index)
    #     return True
    
    # def setEditorData(self, editor, index):
    #     pass

class HexTableModel(QAbstractTableModel):
    FILTER = ''.join([(len(repr(chr(x)))==3 or chr(x) == "\\") and chr(x) or '.' for x in range(256)])

    def __init__(self, parent=None, *args):
        super(HexTableModel, self).__init__(parent, *args)
        self.buf = {}
        self.rows = 512 // 16
        self.buf_size = 0
        self.start_address = 0
        self.parent = parent

    @staticmethod
    def qindex2index(index):
        """ from a QIndex (row/column coordinate system), get the buffer index of the byte """
        r = index.row()
        c = index.column()
        if c > 0x10:
            return (0x10 * r) + c - 0x11
        else:
            return (0x10 * r) + c

    def index2qindexb(self, index):
        """ from a buffer index, get the QIndex (row/column coordinate system) of the byte pane """
        r = index // 0x10
        c = index % 0x10
        return self.index(r, c)

    def index2qindexc(self, index):
        """ from a buffer index, get the QIndex (row/column coordinate system) of the char pane """
        r = (index // 0x10)
        c = index % 0x10 + 0x11
        return self.index(r, c)

    def rowCount(self, parent):
        return self.rows
        if self.buf_size % 0x10 != 0:
            return (self.buf_size // 0x10) + 1
        else:
            return self.buf_size // 0x10

    def columnCount(self, parent):
        return 0x21

    def data(self, index, role):
        if self.buf_size == 0: return
        if not index.isValid():
            return None

        elif self.qindex2index(index) >= self.buf_size:
            return None

        col = index.column()
        bindex = self.qindex2index(index)
        if role == Qt.DisplayRole:
            if col == 0x10:
                return ""
            c = self.buf[bindex]
            if col > 0x10:
                val = int(c, 16) if c != ".." and c != "__" else c
                return chr(val) if (
                    val != "__" and
                    val != ".." and 
                    val >= 33 and 
                    val <= 126
                ) else "."
            else:
                return c
        elif role == Qt.BackgroundRole:
            return None
        else:
            return None
    
    def setData(self, index, value, role = Qt.EditRole):
        if role == Qt.EditRole:
            if index.column() == 0x10:
                return False
            is_ascii = False
            if index.column() > 0x10:
                is_ascii = True
            if not is_ascii and is_int(value) and int(value, 16) <= 255 and int(value, 16) >= 0:
                off = self.qindex2index(index)
                self.buf[off] = value.lower()
                self.parent.data_edited.emit(off, int(value, 16))
                # memory_view will send a dataChanged signal
                return True
            elif is_ascii and len(value) == 1 and ord(value) < 128:
                off = self.qindex2index(index)
                self.buf[off] = "{:02x}".format(ord(value))
                self.parent.data_edited.emit(off, ord(value))
        return False

    @property
    def data_length(self):
        return self.buf_size

    def flags(self, index):
        return Qt.ItemIsEnabled | Qt.ItemIsSelectable | Qt.ItemIsEditable
    
    def headerData(self, section, orientation, role):
        if role != Qt.DisplayRole:
            return None
        elif orientation == Qt.Horizontal:
            if section < 0x10:
                return "%01X" % (section)
            else:
                return ""
        elif orientation == Qt.Vertical:
            return "%016X" % (section * 0x10 + self.start_address)
        else:
            return None

    def _emit_data_changed(self, start_bindex, end_bindex):
        for i in range(start_bindex, end_bindex):
            # mark data changed to encourage re-rendering of cell
            qib = self.index2qindexb(i)
            qic = self.index2qindexc(i)
            self.dataChanged.emit(qib, qib)
            self.dataChanged.emit(qic, qic)

    def _handle_range_changed(self, range_min, range_max):
        self._emit_data_changed(range_min, range_max)

class HexItemSelectionModel(QItemSelectionModel):
    selectionRangeChanged = Signal([int])

    def __init__(self, model, view):
        """
        :type view: HexTableView
        """
        super(HexItemSelectionModel, self).__init__(model)
        self._model = model
        self._view = view

        self._start_qindex = None
        self._view.leftMousePressedIndex.connect(self._handle_mouse_pressed)
        self._view.leftMouseMovedIndex.connect(self._handle_mouse_moved)
        self._view.leftMouseReleasedIndex.connect(self._handle_mouse_released)

        self.start = None
        self.end = None

    def _bselect(self, selection, start_bindex, end_bindex):
        """ add the given buffer indices to the given QItemSelection, both byte and char panes """
        selection.select(self._model.index2qindexb(start_bindex), self._model.index2qindexb(end_bindex))
        selection.select(self._model.index2qindexc(start_bindex), self._model.index2qindexc(end_bindex))

    def _do_select(self, start_bindex, end_bindex):
        """
        select the given range by buffer indices

        selects items like this:

            ..................
            ......xxxxxxxxxxxx
            xxxxxxxxxxxxxxxxxx
            xxxxxxxxxxxxxxxxxx
            xxxxxxxxxxxx......
            ..................

        *not* like this:

            ..................
            ......xxxxxx......
            ......xxxxxx......
            ......xxxxxx......
            ......xxxxxx......
            ..................
         """
        self.select(QItemSelection(), QItemSelectionModel.Clear)
        if start_bindex > end_bindex:
            start_bindex, end_bindex = end_bindex, start_bindex

        selection = QItemSelection()
        if row_number(end_bindex) - row_number(start_bindex) == 0:
            # all on one line
            self._bselect(selection, start_bindex, end_bindex)
        elif row_number(end_bindex) - row_number(start_bindex) == 1:
            # two lines
            self._bselect(selection, start_bindex, row_end_index(start_bindex))
            self._bselect(selection, row_start_index(end_bindex), end_bindex)
        else:
            # many lines
            self._bselect(selection, start_bindex, row_end_index(start_bindex))
            self._bselect(selection, row_start_index(start_bindex) + 0x10, row_end_index(end_bindex) - 0x10)
            self._bselect(selection, row_start_index(end_bindex), end_bindex)

        self.select(selection, QItemSelectionModel.SelectCurrent)
        self.start = start_bindex
        self.end = end_bindex
        self.selectionRangeChanged.emit(end_bindex)

    def bselect(self, start_bindex, end_bindex):
        """  the public interface to _do_select """
        return self._do_select(start_bindex, end_bindex)

    def handle_move_key(self, key):
        if self._start_qindex == self._model.index2qindexc(self.start) or \
            self._start_qindex == self._model.index2qindexb(self.start):
            i = self.end
        else:
            i = self.start
        if key == QKeySequence.MoveToEndOfDocument:
            i = self._model.data_length - 1
        elif key == QKeySequence.MoveToEndOfLine:
            i = row_end_index(i)
        elif key == QKeySequence.MoveToNextChar:
            i += 1
        elif key == QKeySequence.MoveToNextLine:
            i += 0x10
        elif key == QKeySequence.MoveToNextPage:
            i += 0x40
        elif key == QKeySequence.MoveToNextWord:
            i += 1
        elif key == QKeySequence.MoveToPreviousChar:
            i -= 1
        elif key == QKeySequence.MoveToPreviousLine:
            i -= 0x10
        elif key == QKeySequence.MoveToPreviousPage:
            i -= 0x40
        elif key == QKeySequence.MoveToPreviousWord:
            i -= 1
        elif key == QKeySequence.MoveToStartOfDocument:
            i = 0x0
        elif key == QKeySequence.MoveToStartOfLine:
            i = row_start_index(i)
        else:
            raise RuntimeError("Unexpected movement key: %s" % (key))

        # this behavior selects the smallest or largest cell in the
        #   same column as the out-of-bounds index
        if i < 0:
            i %= 0x10
        if i > self._model.data_length:
            i %= 0x10
            i = self._model.data_length - 0x10 + i

        self.bselect(i, i)

    def handle_select_key(self, key):
        i = None
        j = None
        if self._start_qindex == self._model.index2qindexc(self.start) or \
            self._start_qindex == self._model.index2qindexb(self.start):
            i = self.end
            j = self.start
        else:
            i = self.start
            j = self.end

        if key == QKeySequence.SelectEndOfDocument:
            i = self._model.data_length - 1
        elif key == QKeySequence.SelectEndOfLine:
            i = row_end_index(i)
        elif key == QKeySequence.SelectNextChar:
            i += 1
        elif key == QKeySequence.SelectNextLine:
            i += 0x10
        elif key == QKeySequence.SelectNextPage:
            i += 0x40
        elif key == QKeySequence.SelectNextWord:
            i += 1
        elif key == QKeySequence.SelectPreviousChar:
            i -= 1
        elif key == QKeySequence.SelectPreviousLine:
            i -= 0x10
        elif key == QKeySequence.SelectPreviousPage:
            i -= 0x40
        elif key == QKeySequence.SelectPreviousWord:
            i -= 1
        elif key == QKeySequence.SelectStartOfDocument:
            i = 0x0
        elif key == QKeySequence.SelectStartOfLine:
            i = row_start_index(i)
        else:
            raise RuntimeError("Unexpected select key: %s" % (key))

        # this behavior selects the smallest or largest cell in the
        #   same column as the out-of-bounds index
        if i < 0:
            i %= 0x10
        if i > self._model.data_length:
            i %= 0x10
            i = self._model.data_length - 0x10 + i

        # need to explicitly reset start_qindex so that the current index
        #   doesn't get confused when coming from a selection of a single cell
        #   (in the check at the start of this function to decide which end of
        #    the selection was most recently active)
        self._start_qindex = self._model.index2qindexc(j)

        self.bselect(i, j)

    def _update_selection(self, qindex1, qindex2):
        """  select the given range by qmodel indices """
        m = self.model()
        self._do_select(m.qindex2index(qindex1), m.qindex2index(qindex2))

    def _handle_mouse_pressed(self, qindex):
        self._start_qindex = qindex
        self._update_selection(qindex, qindex)

    def _handle_mouse_moved(self, qindex):
        self._update_selection(self._start_qindex, qindex)

    def _handle_mouse_released(self, qindex):
        self._update_selection(self._start_qindex, qindex)
        self._start_qindex = None

class HexTableView(QTableView):
    """ table view that handles click events for better selection handling """
    leftMousePressed = Signal([QMouseEvent])
    leftMousePressedIndex = Signal([QModelIndex])
    leftMouseMoved = Signal([QMouseEvent])
    leftMouseMovedIndex = Signal([QModelIndex])
    leftMouseReleased = Signal([QMouseEvent])
    leftMouseReleasedIndex = Signal([QModelIndex])
    moveKeyPressed = Signal([QKeySequence])
    selectKeyPressed = Signal([QKeySequence])

    def __init__(self, *args, **kwargs):
        super(HexTableView, self).__init__(*args, **kwargs)
        self.parent = kwargs["parent"]
        self.leftMousePressed.connect(self._handle_mouse_press)
        self.leftMouseMoved.connect(self._handle_mouse_move)
        self.leftMouseReleased.connect(self._handle_mouse_release)

        self._press_start_index = None
        self._press_current_index = None
        self._press_end_index = None
        self._is_tracking_mouse = False

    def _reset_press_state(self):
        self._press_start_index = None
        self._press_current_index = None
        self._press_end_index = None

    def mousePressEvent(self, event):
        super(HexTableView, self).mousePressEvent(event)
        if event.buttons() & Qt.LeftButton:
            self.leftMousePressed.emit(event)

    def mouseMoveEvent(self, event):
        super(HexTableView, self).mouseMoveEvent(event)
        if event.buttons() & Qt.LeftButton:
            self.leftMouseMoved.emit(event)

    def mouseReleaseEvent(self, event):
        super(HexTableView, self).mousePressEvent(event)
        if event.buttons() & Qt.LeftButton:
            self.leftMouseReleased.emit(event)

    def focusOutEvent(self, event):
        super(HexTableView, self).focusOutEvent(event)
        if not event.reason() & Qt.MenuBarFocusReason:
            self.parent._hsm.clearSelection()

    def keyPressEvent(self, event):
        move_keys = (
            QKeySequence.MoveToEndOfDocument,
            QKeySequence.MoveToEndOfLine,
            QKeySequence.MoveToNextChar,
            QKeySequence.MoveToNextLine,
            QKeySequence.MoveToNextPage,
            QKeySequence.MoveToNextWord,
            QKeySequence.MoveToPreviousChar,
            QKeySequence.MoveToPreviousLine,
            QKeySequence.MoveToPreviousPage,
            QKeySequence.MoveToPreviousWord,
            QKeySequence.MoveToStartOfDocument,
            QKeySequence.MoveToStartOfLine,
        )

        for move_key in move_keys:
            if event.matches(move_key):
                self.moveKeyPressed.emit(move_key)
                return

        select_keys = (
            QKeySequence.SelectAll,
            QKeySequence.SelectEndOfDocument,
            QKeySequence.SelectEndOfLine,
            QKeySequence.SelectNextChar,
            QKeySequence.SelectNextLine,
            QKeySequence.SelectNextPage,
            QKeySequence.SelectNextWord,
            QKeySequence.SelectPreviousChar,
            QKeySequence.SelectPreviousLine,
            QKeySequence.SelectPreviousPage,
            QKeySequence.SelectPreviousWord,
            QKeySequence.SelectStartOfDocument,
            QKeySequence.SelectStartOfLine,
        )

        for select_key in select_keys:
            if event.matches(select_key):
                self.selectKeyPressed.emit(select_key)
                return

    def _handle_mouse_press(self, key_event):
        self._reset_press_state()

        self._press_start_index = self.indexAt(key_event.pos())
        self._is_tracking_mouse = True

        self.leftMousePressedIndex.emit(self._press_start_index)

    def _handle_mouse_move(self, key_event):
        if self._is_tracking_mouse:
            i = self.indexAt(key_event.pos())
            if i != self._press_current_index:
                self._press_current_index = i
                self.leftMouseMovedIndex.emit(i)

    def _handle_mouse_release(self, key_event):
        self._press_end_index = self.indexAt(key_event.pos())
        self._is_tracking_mouse = False

        self.leftMouseReleasedIndex.emit(self._press_end_index)

class HexViewWidget(QWidget):
    full_data_changed = Signal(list, list, int)
    single_data_changed = Signal(object, list)
    data_edited = Signal(object, int)

    def __init__(self, parent=None, menu_handler=None):
        super(HexViewWidget, self).__init__()
        self.setupUi(self)

        self._model = HexTableModel(self)
        self.view = HexTableView(parent=self)
        sizePolicy = QSizePolicy(QSizePolicy.MinimumExpanding, QSizePolicy.Expanding)
        sizePolicy.setHorizontalStretch(0)
        sizePolicy.setVerticalStretch(0)
        sizePolicy.setHeightForWidth(self.view.sizePolicy().hasHeightForWidth())
        self.view.setSizePolicy(sizePolicy)
        # self.view.setMinimumSize(QSize(660, 0))
        self.view.setVerticalScrollBarPolicy(Qt.ScrollBarAlwaysOn)
        self.view.setHorizontalScrollBarPolicy(Qt.ScrollBarAlwaysOff)
        self.view.setSelectionMode(QAbstractItemView.NoSelection)
        self.view.setShowGrid(False)
        self.view.setWordWrap(False)
        self.view.setStyleSheet("QHeaderView { } QTableView::item { } ")  # bypass stylesheet
        # self.view.setObjectName("view")
        # self.view.horizontalHeader().setDefaultSectionSize(10)
        self.view.horizontalHeader().setMinimumSectionSize(5)
        # self.view.verticalHeader().setDefaultSectionSize(21)
        # self.view.setMinimumWidth( self.view.width() )
        self.mainLayout.insertWidget(0, self.view)

        self.view.setModel(self._model)
        for i in range(0x10):
            self.view.setColumnWidth(i, 25)
        self.view.setColumnWidth(0x10, 5)
        for i in range(0x11, 0x22):
            self.view.setColumnWidth(i, 11)

        self._hsm = HexItemSelectionModel(self._model, self.view)
        self.view.setSelectionModel(self._hsm)

        self.view.setContextMenuPolicy(Qt.CustomContextMenu)
        self.view.customContextMenuRequested.connect(self._handle_context_menu_requested)
        if menu_handler is not None:
            self.get_context_menu = menu_handler

        self.optimal_width = self.view.verticalScrollBar().width()+self.view.verticalHeader().width() - 40
        for i in range(0x22):
            self.optimal_width += self.view.columnWidth(i)

        f = QFontDatabase.systemFont(QFontDatabase.FixedFont)
        f.setPointSize(8)
        self.view.horizontalHeader().setFont(f)
        self.view.verticalHeader().setFont(f)
        self.view.setFont(f)
        self.statusLabel.setFont(f)

        self.view.setMinimumWidth(self.optimal_width)
        self.view.setMaximumWidth(self.optimal_width)

        self._hsm.selectionRangeChanged.connect(self._handle_selection_range_changed)
        self.view.moveKeyPressed.connect(self._hsm.handle_move_key)
        self.view.selectKeyPressed.connect(self._hsm.handle_select_key)

        self.view.setItemDelegate(HexItemDelegate(self._model, self))

        self.full_data_changed.connect(self._handle_data_changed)
        self.single_data_changed.connect(self._handle_single_data_changed)
        # self.data_edited.connect(self._handle_data_edited)

        self.statusLabel.setText("")
    
    def _handle_data_edited(self, address, data):
        pass
        # print("edited address data", address, data)

    def _handle_data_changed(self, new_address, new_data, new_data_size):
        self._model.buf = new_data
        self._model.buf_size = new_data_size
        self._model.start_address = new_address
        self._model._handle_range_changed(0, 512)

    def _handle_single_data_changed(self, idx, new_val):
        self._model.buf[idx] = new_val
        self._model._handle_range_changed(idx, idx)

    def _handle_context_menu_requested(self, qpoint):
        menu = self.get_context_menu(qpoint)
        if menu is None: return
        menu.exec_(self.view.mapToGlobal(qpoint))

    def _print_selection(self):
        start = self._hsm.start
        end   = self._hsm.end

        print(start, end)

    def get_context_menu(self, qpoint):
        """ override this method to customize the context menu """
        menu = QMenu(self)
        index = self.view.indexAt(qpoint)

        a = menu.addAction("Print selection")
        a.triggered.connect(self._print_selection)
        return menu

    def _render_status_text(self):
        txt = []
        start = self._hsm.start
        end = self._hsm.end
        if start not in (None, -1) and end not in (None, -1):
            txt.append("sel: [{:s}, {:s}]".format(hex(start), hex(end)))
            txt.append("len: {:s}".format(hex(end - start + 1)))
        self.statusLabel.setText(" ".join(txt))

    def _handle_selection_range_changed(self, end_bindex):
        self._render_status_text()

    def setupUi(self, Form):
        Form.setObjectName("Form")
        Form.resize(400, 300)
        self.verticalLayout = QVBoxLayout(Form)
        self.verticalLayout.setObjectName("verticalLayout")
        self.mainLayout = QVBoxLayout()
        self.mainLayout.setObjectName("mainLayout")
        self.statusLabel = QLabel(Form)
        self.statusLabel.setMaximumSize(QSize(16777215, 15))
        self.statusLabel.setObjectName("statusLabel")
        self.mainLayout.addWidget(self.statusLabel)
        self.verticalLayout.addLayout(self.mainLayout)

        self.retranslateUi(Form)
        QMetaObject.connectSlotsByName(Form)

    def retranslateUi(self, Form):
        _translate = QCoreApplication.translate
        Form.setWindowTitle(_translate("Form", "Form"))
        self.statusLabel.setText(_translate("Form", "TextLabel"))
