def arrayTabulate[T](n: Int, f: Int => T) = {
  val v = new Array[T](n);
  var i = 0;
  while (i < n) {
    v(i) = f(i);
    i = i + 1
  };
  v
};

def arraySwap[T](v: Array[T], i1: Int, i2: Int) = {
  val t = v(i1);
  v(i1) = v(i2);
  v(i2) = t
};

def arrayShuffle[T](v: Array[T], seed: Int) = {
  val rng = makeRNG(seed);
  val l = v.length;
  var i = 0;
  while (i < l) {
    val j = i + rngNextInt(rng) % (l - i);
    arraySwap[T](v, i, j);
    i = i + 1
  };
  ()
};

def auxArrayPartition[T](v: Array[T], p: T => Boolean, l: Int, h: Int) = {
  def loop(l: Int, h: Int): Int = {
    if (l >= h)
      l
    else if (p(v(l)))
      loop(l + 1, h)
    else if (!p(v(h-1)))
      loop(l, h - 1)
    else {
      arraySwap[T](v, l, h - 1);
      loop(l + 1, h + 1)
    }
  };
  loop(l, h)
};

// Reorganize the elements of the vector so that all those not
// satisfying the predicate [p] are before those that satisfy it.
// Return the index of the first element not satisfying [p], or the
// length of the vector if all elements satisfy [p].
def arrayPartition[T](v: Array[T], p: T => Boolean) =
  auxArrayPartition[T](v, p, 0, v.length);

def arrayFoldLeft[T,U](f: (T,U) => T, z: T, v: Array[U]) = {
  var i = 0;
  val l = v.length;
  var zz = z;
  while (i < l) {
    zz = f(zz, v(i));
    i = i + 1
  };
  zz
};

def arrayForeach[T](f: T => Unit, v: Array[T]) = {
  var i = 0;
  val l = v.length;
  while (i < l) {
    f(v(i));
    i = i + 1
  };
  ()
};

def arraySort[T](v: Array[T], el: (T, T) => Boolean) = {
  def qsort(l: Int, h: Int) = {
    if (h - l > 0) {
       val p = v(h);
       val pred = (x: T) => el(x, p);
       val m = auxArrayPartition[T](v, pred, l, h);
       arraySwap[T](v, m, h);
       qsort(l, m - 1);
       qsort(m + 1, h)
    }
  };
  qsort(0, v.length - 1)
};

def arrayBinarySearch[T](v: Array[T], e: T, el: (T, T) => Boolean) = {
  def loop(l: Int, h: Int): Int = {
    if (l > h)
      -1 - l
    else {
      val m = l + (h - l) / 2;
      val me = v(m);
      if (el(e, me))
        loop(l, m - 1)
      else if (el(me, e))
        loop(m + 1, h)
      else
        m
    }
  };
  loop(0, v.length - 1)
};

def arrayToList[T](v: Array[T]) = {
  def loop(i: Int): List[T] = {
    if (i == -1)
      Nil
    else
      v(i)::loop(i - 1)
  };
  loop(v.length - 1)
};

def listToArray[T](l: List[T]) = {
  val n = listLength[T](l);
  val v = new Array[T](n);
  def loop(i: Int, l: List[T]) = {
    if (i < n) {
      v(i) = l.head;
      loop(i + 1, l.tail)
    }
  };
  loop(0, l);
  v
};
