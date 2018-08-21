//  solutions are represented as integer list, where the index denotes the
//  row (from the bottom), the value the column. for example, the solution
//  for n = 4
//    _ _ _ _
//   | |o| | |
//   | | | |o|
//   |o| | | |
//   | | |o| |
//
//  is represented as (3, 1, 4, 2)
//
//  SOME USEFUL LIST FUNCTIONS

def listRange(first: Int, to: Int) =
  listTabulate[Int](to - first + 1, (i: Int) => first + i);

def listZipWithIndex(l: List[Int]) =
  listZip[Int,Int](l, listRange(1, listLength[Int](l)));

def listIntPrint(l: List[Int]) = {
  printChar('(');
  listForeach[Int]((elem: Int) => { printInt(elem); printChar(' ') }, l);
  printChar(')')
};

// CHECK IF NO TWO QUEENS IN A COLUMN
//
// essentially checks for duplicates
def colOk(rows: List[Int]) =
  rows.isEmpty ||
    listEvery[Int]((x: Int) => rows.head != x, rows.tail) &&
                colOk(rows.tail);

// CHECK IF NO TWO QUEENS IN A DIAGONAL

// depth denotes how many rows x and y are separated
def onDiag(x: Int, y: Int, depth: Int) =
  x + depth == y || x - depth == y;

def diagOk(rows: List[Int]) =
  rows.isEmpty ||
    listEvery[(Int,Int)]((pair: (Int, Int)) =>
      !onDiag(rows.head, pair._1, pair._2),
      listZipWithIndex(rows.tail)) // index is the row distance from (rows.head)
    && diagOk(rows.tail);

// CHECKING SOLUTIONS

def partialOk(rows: List[Int]) = colOk(rows) && diagOk(rows);

// not actually used in the algorithm below
def queensOk(rows: List[Int], n: Int) =
  listEvery[Int]((x: Int) => x <= n, rows) // no elt. bigger than n
  && n == listLength[Int](rows)            // n queens
  && partialOk(rows);                      // no conflict

// FINDING A SOLUTION

val queens = {
  def auxAdvance(partial: List[Int], n: Int): List[Int] = {
    if (partial.head < n)
      auxQueens((1 + partial.head)::partial.tail, n) // try next value of (list-head partial)
    else
      Nil // there's no solution for (list-tail partial)
  };
  def auxQueens(partial: List[Int], n: Int): List[Int] = {
    if (partialOk(partial))
      if (listLength[Int](partial) == n)
        partial // partial solution with full length: we're done
      else {
        val sol = auxQueens(1::partial, n);
        if (sol.isEmpty)
          auxAdvance(partial, n)
        else
          sol
      }
    else
      auxAdvance(partial, n)
  };
  (n: Int) => auxQueens(listMake1[Int](1), n)
};

// PRINTING

def for(from: Int, to: Int, body: Int => Unit) = {
  if (from < to) {
    body(from);
    for(from + 1, to, body)
  }
};

def header(rows: List[Int]) = {
  println();
  printInt(listLength[Int](rows));
  printString("-queen(s)");
  println();
  printString("list: ");
  listIntPrint(rows);
  println();
  for (0, listLength[Int](rows),
    (x: Int) => printString(" _"));
  println()
};

def row(p: Int, n: Int) = {
  for(0, n,
    (x: Int) => {
      printString("|");
      printString(if (x + 1 ==  p) "o" else " ")
    });
  printString("|");
  println()
};

def printRows(rows: List[Int], n: Int): Unit = {
  if (listLength[Int](rows) == n)
     header(rows);
  if (rows.isEmpty)
    println()
  else {
    row(rows.head, n);
    printRows(rows.tail, n)
  }
};

def printSolution(rows: List[Int]) = {
  if (listLength[Int](rows) == 0) {
    printString("no solution found!");
    println()
  } else
    printRows(listReverse[Int](rows), listLength[Int](rows))
};

// USER INTERFACE

def tui() = {
  printString("enter size (0 to exit)> ");
  val size = intRead();
  if (size != 0) {
    printSolution(queens(size));
    tui()
  }
};


// "main"
tui()
