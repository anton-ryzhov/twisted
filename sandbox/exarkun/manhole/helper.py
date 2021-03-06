
from twisted.internet import protocol
from twisted.python import log

import insults

FOREGROUND = 30
BACKGROUND = 40
BLACK, RED, GREEN, YELLOW, BLUE, MAGENTA, CYAN, WHITE, N_COLORS = range(9)

class CharacterAttribute:
    def __init__(self, charset=insults.G0,
                 bold=False, underline=False,
                 blink=False, reverseVideo=False,
                 foreground=WHITE, background=BLACK,

                 _subtracting=False):
        self.charset = charset
        self.bold = bold
        self.underline = underline
        self.blink = blink
        self.reverseVideo = reverseVideo
        self.foreground = foreground
        self.background = background

        self._subtracting = _subtracting

    def __eq__(self, other):
        return vars(self) == vars(other)

    def __ne__(self, other):
        return not self.__eq__(other)

    def copy(self):
        c = self.__class__()
        c.__dict__.update(vars(self))
        return c

    def wantOne(self, **kw):
        k, v = kw.popitem()
        if getattr(self, k) != v:
            attr = self.copy()
            attr._subtracting = not v
            setattr(attr, k, v)
            return attr
        else:
            return self.copy()

    def toVT102(self):
        # Spit out a vt102 control sequence that will set up
        # all the attributes set here.  Except charset.
        attrs = []
        if self._subtracting:
            attrs.append(0)
        if self.bold:
            attrs.append(insults.BOLD)
        if self.underline:
            attrs.append(insults.UNDERLINE)
        if self.blink:
            attrs.append(insults.BLINK)
        if self.reverseVideo:
            attrs.append(insults.REVERSE_VIDEO)
        if self.foreground != WHITE:
            attrs.append(FOREGROUND + self.foreground)
        if self.background != BLACK:
            attrs.append(BACKGROUND + self.background)
        if attrs:
            return '\x1b[' + ';'.join(map(str, attrs)) + 'm'
        return ''

# XXX - need to support scroll regions and scroll history
class TerminalBuffer(protocol.Protocol):
    width = 80
    height = 24

    fill = ' '

    def getCharacter(self, x, y):
        return self.lines[y][x]

    def connectionMade(self):
        self.reset()

    def write(self, bytes):
        for b in bytes:
            self.insertAtCursor(b)

    def _currentCharacterAttributes(self):
        return CharacterAttribute(self.activeCharset, **self.graphicRendition)

    def insertAtCursor(self, b):
        if b == '\r':
            self.x = 0
        elif b == '\n' or self.x >= self.width:
            self.x = 0
            self._scrollDown()
        if b != '\r' and b != '\n':
            ch = (b, self._currentCharacterAttributes())
            if self.modes.get(insults.IRM):
                self.lines[self.y][self.x] = ch
            else:
                self.lines[self.y][self.x:self.x] = [ch]
                self.lines[self.y].pop()
            self.x += 1

    def _emptyLine(self, width):
        return [(self.fill, self._currentCharacterAttributes()) for i in xrange(width)]

    def _scrollDown(self):
        self.y += 1
        if self.y >= self.height:
            self.y -= 1
            del self.lines[0]
            self.lines.append(self._emptyLine(self.width))

    def _scrollUp(self):
        self.y -= 1
        if self.y < 0:
            self.y = 0
            del self.lines[-1]
            self.lines.insert(0, self._emptyLine(self.width))

    def cursorUp(self, n=1):
        self.y = max(0, self.y - n)

    def cursorDown(self, n=1):
        self.y = min(self.height - 1, self.y + n)

    def cursorBackward(self, n=1):
        self.x = max(0, self.x - n)

    def cursorForward(self, n=1):
        self.x = min(self.width, self.x + n)

    def cursorPosition(self, column, line):
        self.x = column
        self.y = line

    def cursorHome(self):
        self.x = self.home.x
        self.y = self.home.y

    def index(self):
        self._scrollDown()

    def reverseIndex(self):
        self._scrollUp()

    def nextLine(self):
        self.insertAtCursor('\n')

    def saveCursor(self):
        self._savedCursor = (self.x, self.y)

    def restoreCursor(self):
        self.x, self.y = self._savedCursor
        del self._savedCursor

    def setModes(self, modes):
        for m in modes:
            self.modes[m] = True

    def resetModes(self, modes):
        for m in modes:
            try:
                del self.modes[m]
            except KeyError:
                pass

    def applicationKeypadMode(self):
        self.keypadMode = 'app'

    def numericKeypadMode(self):
        self.keypadMode = 'num'

    def selectCharacterSet(self, charSet, which):
        self.charsets[which] = charSet

    def shiftIn(self):
        self.activeCharset = insults.G0

    def shiftOut(self):
        self.activeCharset = insults.G1

    def singleShift2(self):
        oldActiveCharset = self.activeCharset
        self.activeCharset = insults.G2
        f = self.insertAtCursor
        def insertAtCursor(b):
            f(b)
            del self.insertAtCursor
            self.activeCharset = oldActiveCharset
        self.insertAtCursor = insertAtCursor

    def singleShift3(self):
        oldActiveCharset = self.activeCharset
        self.activeCharset = insults.G3
        f = self.insertAtCursor
        def insertAtCursor(b):
            f(b)
            del self.insertAtCursor
            self.activeCharset = oldActiveCharset
        self.insertAtCursor = insertAtCursor

    def selectGraphicRendition(self, *attributes):
        for a in attributes:
            if a == insults.NORMAL:
                self.graphicRendition = {
                    'bold': False,
                    'underline': False,
                    'blink': False,
                    'reverseVideo': False,
                    'foreground': WHITE,
                    'background': BLACK}
            elif a == insults.BOLD:
                self.graphicRendition['bold'] = True
            elif a == insults.UNDERLINE:
                self.graphicRendition['underline'] = True
            elif a == insults.BLINK:
                self.graphicRendition['blink'] = True
            elif a == insults.REVERSE_VIDEO:
                self.graphicRendition['reverseVideo'] = True
            else:
                try:
                    v = int(a)
                except ValueError:
                    log.msg("Unknown graphic rendition attribute: " + repr(a))
                else:
                    if FOREGROUND <= v <= FOREGROUND + N_COLORS:
                        self.graphicRendition['foreground'] = v - FOREGROUND
                    elif BACKGROUND <= v <= BACKGROUND + N_COLORS:
                        self.graphicRendition['background'] = v - BACKGROUND
                    else:
                        log.msg("Unknown graphic rendition attribute: " + repr(a))

    def eraseLine(self):
        self.lines[self.y] = self._emptyLine(self.width)

    def eraseToLineEnd(self):
        width = self.width - self.x
        self.lines[self.y][self.x:] = self._emptyLine(width)

    def eraseToLineBeginning(self):
        self.lines[self.y][:self.x + 1] = self._emptyLine(self.x + 1)

    def eraseDisplay(self):
        self.lines = [self._emptyLine(self.width) for i in xrange(self.height)]

    def eraseToDisplayEnd(self):
        self.eraseToLineEnd()
        height = self.height - self.y - 1
        self.lines[self.y + 1:] = [self._emptyLine(self.width) for i in range(height)]

    def eraseToDisplayBeginning(self):
        self.eraseToLineBeginning()
        self.lines[:self.y] = [self._emptyLine(self.width) for i in range(self.y)]

    def deleteCharacter(self, n=1):
        del self.lines[self.y][self.x:self.x+n]
        self.lines[self.y].extend(self._emptyLine(min(self.width - self.x, n)))

    def insertLine(self, n=1):
        self.lines[self.y:self.y] = [self._emptyLine(self.width) for i in range(n)]
        del self.lines[self.height:]

    def deleteLine(self, n=1):
        del self.lines[self.y:self.y+n]
        self.lines.extend([self._emptyLine(self.width) for i in range(n)])

    def reportCursorPosition(self):
        return (self.x, self.y)

    def reset(self):
        self.home = insults.Vector(0, 0)
        self.x = self.y = 0
        self.modes = {}
        self.numericKeypad = 'app'
        self.activeCharset = insults.G0
        self.graphicRendition = {
            'bold': False,
            'underline': False,
            'blink': False,
            'reverseVideo': False,
            'foreground': WHITE,
            'background': BLACK}
        self.charsets = {
            insults.G0: insults.CS_US,
            insults.G1: insults.CS_US,
            insults.G2: insults.CS_ALTERNATE,
            insults.G3: insults.CS_ALTERNATE_SPECIAL}
        self.eraseDisplay()

    def __str__(self):
        return '\n'.join([''.join([ch for (ch, attr) in L]).rstrip() for L in self.lines])

