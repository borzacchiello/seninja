from PySide6.QtCore import Qt, QRectF
from PySide6.QtGui import QFontMetrics, QFontDatabase, QMouseEvent, QPainter, QPen, QColor, QPalette
from PySide6.QtWidgets import QAbstractScrollArea

from binaryninjaui import ThemeColor, getThemeColor

import math

class QMemView(QAbstractScrollArea):
    ROW_WIDTH      = 16 # amount of bytes per row
    CHARS_PER_WORD = 2

    COLOR_ADDR      = getThemeColor(ThemeColor.AddressColor)
    COLOR_LINE      = getThemeColor(ThemeColor.WhiteStandardHighlightColor)
    COLOR_BYTES     = getThemeColor(ThemeColor.OpcodeColor)
    HIGHLIGHT_COLOR = getThemeColor(ThemeColor.BackgroundHighlightLightColor)

    HIGHLIGHT_ON  = 1
    HIGHLIGHT_OFF = 2

    def __init__(self, addr, size, dataCallback, parent=None):
        super().__init__(parent)
        self.addr         = addr
        self.size         = size
        self.dataCallback = dataCallback
        self.customMenu   = None
        self.enabled      = True

        self.highligting    = QMemView.HIGHLIGHT_OFF
        self.selectionStart = -1
        self.selectionEnd   = -1

        self.setFont()
        self.updateScrollbars()

    def setEnabled(self, v):
        self.enabled = v

    def setDisabled(self, v):
        self.setEnabled(not v)

    def getSelection(self):
        if self.selectionStart == self.selectionEnd:
            return 0, 0
        return self.addr + min(self.selectionStart, self.selectionEnd), abs(self.selectionEnd-self.selectionStart)

    def setFont(self):
        self.font        = QFontDatabase.systemFont(QFontDatabase.FixedFont)
        self.fontMetrics = QFontMetrics(self.font)

        self.fontWidth  = self.fontMetrics.horizontalAdvance('X')
        self.fontHeight = self.fontMetrics.height()
        super().setFont(self.font)

    def padding(self):
        """ Padding space """
        return self.fontWidth / 2

    def addrline(self):
        """ The X coordinate of the line between the addresses and the hexdump """
        return 17 * self.fontWidth + self.padding()

    def hexdumpCoordinate(self):
        """ The X coordinate of the hexdump """
        return self.addrline() + self.padding()

    def rightborder(self):
        """ The X coordinate of the right border """
        elements = QMemView.ROW_WIDTH * (QMemView.CHARS_PER_WORD + 1) - 1
        return self.hexdumpCoordinate() + elements * self.fontWidth + self.padding()

    def updateScrollbars(self):
        maxval = self.size / QMemView.ROW_WIDTH - self.viewport().height() / self.fontHeight + 2

        self.verticalScrollBar().setMaximum(max(0, maxval))
        self.horizontalScrollBar().setMaximum(
            max(0, (self.rightborder() - self.viewport().width()) / self.fontWidth))

    def isSelected(self, index):
        if index >= self.size:
            return False
        if self.selectionStart == self.selectionEnd:
            return False
        if self.selectionStart < self.selectionEnd:
            return index >= self.selectionStart and index < self.selectionEnd
        return index >= self.selectionEnd and index < self.selectionStart

    def paintEvent(self, event):
        painter = QPainter(self.viewport())
        painter.translate(
            -self.horizontalScrollBar().value() * self.fontWidth, 0)

        charsPerRow = QMemView.ROW_WIDTH
        row         = self.fontHeight
        offset      = self.verticalScrollBar().value() * charsPerRow

        while row + self.fontHeight < self.height() and offset < self.size:
            # Draw the address
            addr    = self.addr + offset
            addrStr = "%016x" % addr
            painter.setPen(QPen(QMemView.COLOR_ADDR))
            painter.drawText(self.padding(), row, addrStr)

            # Draw the bytes
            for i in range(QMemView.ROW_WIDTH):
                boff = offset + i
                if boff >= self.size:
                    break

                drawCoordinate = self.hexdumpCoordinate() + (i * (QMemView.CHARS_PER_WORD + 1) * self.fontWidth)
                drawText       = self.dataCallback(self.addr + boff) if self.dataCallback is not None else "  "
                assert isinstance(drawText, str) and len(drawText) == 2

                if self.isSelected(boff):
                    colorGroup = QPalette.ColorGroup.Active if self.hasFocus() else QPalette.ColorGroup.Inactive
                    painter.fillRect(
                        QRectF(drawCoordinate, row-self.fontHeight+self.padding(), self.fontWidth*2, self.fontHeight),
                        QMemView.HIGHLIGHT_COLOR
                    )
                    if (boff+1) % QMemView.ROW_WIDTH != 0 and self.isSelected(boff+1):
                        painter.fillRect(
                            QRectF(drawCoordinate+self.fontWidth*2, row-self.fontHeight+self.padding(), self.fontWidth, self.fontHeight),
                            QMemView.HIGHLIGHT_COLOR
                        )

                painter.setPen(QPen(QMemView.COLOR_BYTES))
                painter.drawText(drawCoordinate, row, drawText)

            offset += charsPerRow
            row    += self.fontHeight

        # Draw the address line
        painter.setPen(QPen(QMemView.COLOR_LINE))
        painter.drawLine(self.addrline(), 0, self.addrline(), self.height())

    def pixelToOffset(self, x, y):
        x  = max(self.addrline()+self.padding(), min(x, self.rightborder()))
        x -= self.addrline()
        x  = x / self.fontWidth

        y /= self.fontHeight
        x /= QMemView.CHARS_PER_WORD + 1

        x = math.floor(x)
        y = math.floor(y)
        return y * QMemView.ROW_WIDTH + x + self.verticalScrollBar().value() * QMemView.ROW_WIDTH

    def mousePressEvent(self, event: QMouseEvent):
        if not self.enabled:
            return

        if event.buttons() & Qt.LeftButton:
            if self.highligting == QMemView.HIGHLIGHT_ON:
                self.highligting = QMemView.HIGHLIGHT_OFF
                self.selectionStart = -1
                self.selectionEnd   = -1

            else:
                self.highligting = QMemView.HIGHLIGHT_ON

                x = event.x() + self.horizontalScrollBar().value() * self.fontWidth
                y = event.y()
                off = self.pixelToOffset(x, y)
                self.selectionStart = off
                self.selectionEnd   = off+1

            self.viewport().update()
        if self.customMenu is not None and event.buttons() & Qt.RightButton:
            menu = self.customMenu()
            menu.exec_(self.mapToGlobal(event.pos()))

    def mouseMoveEvent(self, event: QMouseEvent):
        if not self.enabled:
            return

        if self.highligting != QMemView.HIGHLIGHT_ON:
            return

        x = event.x() + self.horizontalScrollBar().value() * self.fontWidth
        y = event.y()
        off = self.pixelToOffset(x, y)
        self.selectionEnd = off+1
        self.viewport().update()

    def resizeEvent(self, event):
        self.updateScrollbars()
