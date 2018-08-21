def printString(s: String) = {
  var idx = 0;
  while (idx < s.length) {
    printChar(s(idx));
    idx = idx + 1
  };
  ()
};

def stringConcat(s1: String, s2: String) = {
  val s3 = new Array[Char](s1.length + s2.length);
  var idx = 0;
  while (idx < s1.length) {
    s3(idx) = s1(idx);
    idx = idx + 1
  };
  idx = 0;
  while (idx < s2.length) {
    s3(s1.length + idx) = s2(idx);
    idx = idx + 1
  };
  s3
};
