def listMake1[T](e1: T) = e1::Nil;
def listMake2[T](e1: T, e2: T) = e1::listMake1[T](e2);
def listMake3[T](e1: T, e2: T, e3: T) = e1::listMake2[T](e2, e3);
def listMake4[T](e1: T, e2: T, e3: T, e4: T) = e1::listMake3[T](e2, e3, e4);
def listMake5[T](e1: T, e2: T, e3: T, e4: T, e5: T) = e1::listMake4[T](e2, e3, e4, e5);
def listMake6[T](e1: T, e2: T, e3: T, e4: T, e5: T, e6: T) = e1::listMake5[T](e2, e3, e4, e5, e6);
def listMake7[T](e1: T, e2: T, e3: T, e4: T, e5: T, e6: T, e7: T) = e1::listMake6[T](e2, e3, e4, e5, e6, e7);
def listMake8[T](e1: T, e2: T, e3: T, e4: T, e5: T, e6: T, e7: T, e8: T) = e1::listMake7[T](e2, e3, e4, e5, e6, e7, e8);

def listTabulate[T](n: Int, f: Int => T) = {
  def aux(i: Int, l: List[T]): List[T] = {
    if (i == 0)
      l
    else
      aux(i - 1, f(i - 1)::l)
  };
  aux(n, Nil)
};

def listLength[T](l: List[T]): Int =
  if (l.isEmpty)
    0
  else
    1 + listLength[T](l.tail);

def listForeach[T](f: T => Unit, l: List[T]): Unit =
  if (!l.isEmpty) {
    f(l.head);
    listForeach[T](f, l.tail)
  };

def listMap[T,U](f: T => U, l: List[T]): List[U] =
  if (l.isEmpty)
    Nil
  else
    f(l.head)::listMap[T,U](f, l.tail);

def listFoldLeft[T,U](f: (T, U) => T, z: T, l: List[U]): T =
  if (l.isEmpty)
    z
  else
    listFoldLeft[T,U](f, f(z, l.head), l.tail);

def listFoldRight[T,U](f: (U, T) => T, z: T, l: List[U]): T =
  if (l.isEmpty)
    z
  else
    f(l.head, listFoldRight[T,U](f, z, l.tail));

def listEvery[T](p: T => Boolean, l: List[T]): Boolean =
  l.isEmpty || p(l.head) && listEvery[T](p, l.tail);

def listAny[T](p: T => Boolean, l: List[T]): Boolean =
  !l.isEmpty && (p(l.head) || listAny[T](p, l.tail));

def listFilter[T](p: T => Boolean, l: List[T]): List[T] =
  listFoldRight[List[T],T]((e: T, r: List[T]) =>  if (p(e)) e::r else r, Nil, l);

def listPartition[T](p: T => Boolean, l: List[T]) =
  listFoldRight[(List[T], List[T]),T](
    (e: T,  yn: (List[T], List[T])) =>
      if (p(e))
        (e::yn._1, yn._2)
      else
        (yn._1, e::yn._2),
      (Nil, Nil),
      l);

def listTake[T](l: List[T], n: Int): List[T] =
  if (0 == n || l.isEmpty)
    Nil
  else
    l.head :: listTake[T](l.tail, n - 1);

def listDrop[T](l: List[T], n: Int): List[T] =
  if (0 == n || l.isEmpty)
    l
  else
    listDrop[T](l.tail, n - 1);

def listNth[T](l: List[T], n: Int): T =
  listDrop[T](l, n).head;

def listReverse[T](l: List[T]): List[T] =
  listFoldLeft[List[T],T]((t: List[T], h: T) => h::t, Nil, l);

def listAppend[T](l1: List[T], l2: List[T]) =
  if (l1.isEmpty) l2
  else if (l2.isEmpty) l1
  else l1.head :: listAppend[T](l1.tail, l2);

def listZip[T,U](l1: List[T], l2: List[U]): List[(T, U)] =
  if (l1.isEmpty  || l2.isEmpty)
    Nil
  else
    (l1.head, l2.head) :: listZip[T,U](l1.tail, l2.tail);
