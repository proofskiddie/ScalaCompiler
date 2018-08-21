def printChar(c: Char) = putchar(c.toInt);

def charRead() = getchar().toChar;

def println() = printChar('\n');

val int0 = '0'.toInt;
val int9 = '9'.toInt;
def isCharDigit(c: Char) = {
  val intC = c.toInt;
  int0 <= intC && intC <= int9
};

def charDigitToInt(c: Char) = c.toInt - int0;

def intCharDigit(i: Int) = (i + int0).toChar;
