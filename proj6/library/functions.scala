def functionCompose[T,U,V](f: U => V, g: T => U) = (x: T) => f(g(x));
