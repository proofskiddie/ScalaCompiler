val zip = (l1: List[Int], l2: List[Int]) => listZip[Int, Int](l1, l2);

def pascal(n: Int): List[List[Int]] = {
  if (n == 1) listMake1[List[Int]](listMake1[Int](1))
  else {
    val p = pascal(n - 1);
    val p1 = zip(p.head, (0 :: p.head));
    val p2 = listMap[(Int, Int), Int]((pair: (Int, Int)) => pair._1 + pair._2, p1);
    listAppend[Int](p2, listMake1[Int](1)) :: p
  }
};

def listIntPrint(l: List[Int]): Unit = {
  printChar('(');
  listForeach[Int]((elem: Int) => { printInt(elem); printChar(' ') }, l);
  printChar(')')
};

def printPascal(p: List[List[Int]]) =
  listMap[List[Int], Unit]((l: List[Int]) => { listIntPrint(l); println()}, p);

def tui(): Int = {
  printString("enter size (0 to exit)> ");
  val size = intRead();
  if (size == 0) 0
  else {
    val x = pascal(size);
    printPascal(x);
    tui()
  }
};

tui()