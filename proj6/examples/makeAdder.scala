val zero = '0'.toInt;

def printDigit(x: Int) = {
  putchar(zero + x)
};

def myPrintInt(x: Int) = { // only 1 digits!
  if (x >= 0 && x <= 9)
    printDigit(x)
};

def makeAdder(x: Int) = (y: Int) => x + y;

val inc = makeAdder(1);
myPrintInt(inc(3));
putchar(10)
