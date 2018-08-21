// Integers

def isEven(i: Int) = 0 == (1 & i);

def isOdd(i: Int) = !isEven(i);

def intAbs(i: Int) = if (i < 0) -i else i;

def intSignum(i: Int) = if (i < 0) -1 else { if (i == 0) 0 else 1 };

def intGcd(x: Int, y: Int) = {
    def auxGcd(x: Int, y: Int): Int = {
      if (0 == y)
        x
      else
        auxGcd(y, x % y)
    };
    auxGcd(intAbs(x), intAbs(y))
};

def intPow(x: Int, y: Int): Int = {
  if (y == 0)
    1
  else {
    if (isEven(y)) {
      val t = intPow(x, y/2);
      t * t
    } else {
      x * intPow(x, y - 1)
    }
  }
};

def intRead() = {
  def aux(accf: (Int, Int) => Int, acc: Int): Int = {
    val c = charRead();
    if (isCharDigit(c)) {
      aux(accf, accf(10 * acc, charDigitToInt(c)))
    } else {
      acc
    }
  };
  val c = charRead();
  if (c == '-') {
    aux((x: Int, y: Int) => x - y, 0)
  } else if (isCharDigit(c)) {
    aux((x: Int, y: Int) => x + y, charDigitToInt(c))
  } else {
    0
  }
};

def printInt(i: Int) = {
  if (i < 0) {
    printChar('-')
  };
  def aux(i: Int): Unit = {
    if (i <= -10)
      aux((i + 9) / 10);
    printChar(intCharDigit(-i % 10))
  };
  aux(if (i < 0) i else -i)
};
