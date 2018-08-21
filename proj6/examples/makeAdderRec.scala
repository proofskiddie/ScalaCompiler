val ten = 10;
val zero = '0'.toInt;

def printDigit(x: Int) = {
  putchar(zero + x)
};

def myPrintInt(x: Int) = { // only positive
  if (x >= 0) {
    if (x <= 9)
      printDigit(x)
    else {
      myPrintInt(x/ten);
      printDigit(x%ten)
    }
  }
};

def makeAdder(x: Int) = (y: Int) => x + y;

val inc = makeAdder(1);
myPrintInt(inc(13));
putchar(10)
