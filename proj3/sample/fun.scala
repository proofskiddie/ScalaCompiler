def f(x: Int) = {
  val arr = new Array[Int](x);
  var i = 0;
  var sum = 0;
  while(i < x) {
    sum = sum + arr(i);
    i = i + 1
  };
  sum
};
f(3)
