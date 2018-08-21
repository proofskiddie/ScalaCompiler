def base() = 10000;

def intToBignum(x: Int) = listMake1[Int](x);

def bignumPrint(b: List[Int]) = {
  val revB = listReverse[Int](b);
  printInt(revB.head);
  listForeach[Int]((d: Int) => {
    if (d < 1000)  printInt(0);
    if (d < 100)   printInt(0);
    if (d < 10)    printInt(0);
    printInt(d) }, revB.tail)
};

def bignumPlus(b1: List[Int], b2: List[Int]) = {
  def loop(b1: List[Int], b2: List[Int], carry: Int): List[Int] = {
    if (b1.isEmpty)
      if (0 == carry) b2 else loop(intToBignum(carry), b2, 0)
    else if (b2.isEmpty)
      if (0 == carry) b1 else loop(b1, intToBignum(carry), 0)
    else {
      val res = b1.head + b2.head + carry;
      (res % base())::loop(b1.tail, b2.tail, res / base())
    }
  };
  loop(b1, b2, 0)
};

def bignumScale(b: List[Int], n: Int) = {
  def loop(b: List[Int], n: Int, carry: Int): List[Int] = {
    if (b.isEmpty)
      if (0 == carry) Nil else intToBignum(carry)
    else {
      val sh = b.head * n +  carry;
      (sh % base())::loop(b.tail, n, sh / base())
    }
  };
  loop(b, n, 0)
};

def bignumTimes(b1: List[Int], b2: List[Int]) =
  if (b1.isEmpty)
    Nil
  else
    bignumPlus(bignumScale(b2, b1.head), bignumScale(bignumTimes(b1.tail, b2), base()));

def bignumIsZero(x: List[Int]) = x.isEmpty;

def bignumFact(n: Int) =
  if (0 == n)
    intToBignum(1)
  else
    bignumTimes(intToBignum(n), bignumFact(n - 1));

printString("Factorial of? ");
val n = intRead();
printInt(n);
printString("! = ");
bignumPrint(bignumFact(n));
println()
