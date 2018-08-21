def printNChar(n: Int, c: Char): Unit =
  if (n > 0) {
    printChar(c);
    printNChar(n - 1, c)
  };

def contains(l: List[Int], elem: Int): Boolean =
  !l.isEmpty && (l.head == elem || contains(l.tail, elem));

def shuffle(l: List[Int], seed: Int) = {
  val v = listToArray[Int](l);
  arrayShuffle[Int](v, seed);
  arrayToList[Int](v)
};

def cell(r: Int, c: Int, s: Int) = r * s + c;

def atE(c: Int, s: Int) = c + 1;

def atW(c: Int, s: Int) = c - 1;

def atN(c: Int, s: Int) = c - s;

def atS(c: Int, s: Int) = c + s;

// Walls
// Represented as a pair of 15-bits integers (cell indices), packed in
// a single one.

def wallMake(c1: Int, c2: Int) = (c1 << 15) | c2;

def wallCell1(w: Int) = w >> 15;

def wallCell2(w: Int) = w & 0x7FFF;

def isWallUp(c1: Int, c2: Int, w: List[Int]) = contains(w, wallMake(c1, c2));

// Create a maze that has walls everywhere
def completeMazeAcc(r: Int, c: Int, s: Int, acc: List[Int]) =
  if (r < s) {
    if (c < s) {
      val rc = cell(r, c, s);
      val res1 = if (c < s - 1)
                    wallMake(cell(r, c, s), atE(rc, s))::acc
                  else
                    acc;
      val res2 = if (r < s - 1)
                   wallMake(cell(r, c, s), atS(rc, s))::res1
                 else
                   res1;
      completeMazeAcc(r, c + 1, s, res2)
    } else {
      completeMazeAcc(r + 1, 0, s, acc)
    }
  } else {
    acc
  };

def completeMaze(s: Int) =
  completeMazeAcc(0, 0, s, Nil);

// Create a list of singleton lists for each cell of the maze
def fullyDisconnectedSetsAcc(r: Int, c: Int, s: Int, acc: List[List[Int]]): List[List[Int]] = {
  if (r < s)
    if (c < s) {
      val res = listMake1[Int](cell(r, c, s))::acc;
      fullyDisconnectedSetsAcc(r, c + 1, s, res)
    } else
      fullyDisconnectedSetsAcc(r + 1, 0, s, acc)
  else
    acc
};

def fullyDisconnectedSets(s: Int) =
  fullyDisconnectedSetsAcc(0, 0, s, Nil);

def connected(sets: List[List[Int]], c1: Int, c2: Int): Boolean =
  !sets.isEmpty && {
    val set = sets.head;
    contains(set, c1) && contains(set, c2) ||
      connected(sets.tail, c1, c2)
  };

// return the first element that satisfies p
def find(p: List[Int] => Boolean, l: List[List[Int]]) = {
  val res = listFilter[List[Int]](p, l);
  if (res.isEmpty)
    Nil
  else
    res.head
};

def connect(sets: List[List[Int]], c1: Int, c2: Int) = {
  val setOfC1 = find((e: List[Int]) => contains(e, c1), sets);
  val setOfC2 = find((e: List[Int]) => contains(e, c2), sets);
  listAppend[Int](setOfC1, setOfC2)::listFilter[List[Int]](
    (e: List[Int]) => !contains(e, c1) && !contains(e, c2), sets)
};

// execute body for each int between from and to
def for(from: Int, to: Int, body: Int => Unit): Unit = {
  if (from < to) {
    body(from);
    for(from + 1, to, body)
  }
};

def printMaze(s: Int, w: List[Int]) = {
  val space = ' ';
  val wall = '#';
  printNChar(s * 2 + 1, wall);
  println();
  for(0, s, (r: Int) => {
    printChar(wall);
    for(0, s, (c: Int) => {
      printChar(space);
      if (c < s - 1) {
        val rc = cell(r, c, s);
        printChar(if (isWallUp(rc, atE(rc, s), w)) wall else space)
      }
    });
    printChar(wall);
    println();
    if (r < s - 1) {
      printChar(wall);
      for(0, s, (c: Int) => {
        val rc = cell(r, c, s);
        printChar(if (isWallUp(rc, atS(rc, s), w)) wall else space);
        if (c < s - 1)
          printChar(wall)
      });
      printChar(wall);
      println()
    }
  });
  printNChar(s * 2 + 1, wall);
  println()
};

def randomMazeAcc(m: List[Int], c: List[List[Int]], acc: List[Int]): List[Int] = {
  if (m.isEmpty)
     acc
   else {
     val w = m.head;
     if (connected(c, wallCell1(w), wallCell2(w)))
       randomMazeAcc(m.tail, c, w::acc)
     else
       randomMazeAcc(m.tail, connect(c, wallCell1(w), wallCell2(w)), acc)
   }
};

def randomMaze(s: Int, seed: Int) = {
  val m = shuffle(completeMaze(s), seed);
  val c = fullyDisconnectedSets(s);
  randomMazeAcc(m, c, Nil)
};


printString("Size: ");
val size = intRead();
printString("Seed: ");
val seed = intRead();
printMaze(size, randomMaze(size, seed))
