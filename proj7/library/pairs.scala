def pairDeriveEq[T,U](eq1: (T, T) => Boolean, eq2: (U, U) => Boolean) =
  (p1: (T, U), p2: (T, U)) => eq1(p1._1, p2._1) && eq2(p1._2, p2._2);

def pairDeriveLt[T,U](lt1: (T, T) => Boolean, lt2: (U, U) => Boolean) =
  (p1: (T, U), p2: (T, U)) => lt1(p1._1, p2._1) || (!lt1(p1._1, p2._1) && lt2(p1._2, p2._2));
