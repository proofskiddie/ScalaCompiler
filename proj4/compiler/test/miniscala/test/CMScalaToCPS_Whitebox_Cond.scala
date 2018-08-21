package miniscala.test

import miniscala.test.infrastructure.CPSHighTest
import org.junit.Test

class CMScalaToCPS_Whitebox_Cond extends CPSHighTest {
  @Test def testCondNestedTrueTrue =
    testCPSHighTreeEquality("if (if (3 == 4) true else true) 1 else 2", """defc v$1(v$2) = { vall v$3 = 0; v$3 };
      |defc v$4() = { vall v$5 = 1; v$1(v$5) };
      |defc v$6() = { vall v$7 = 2; v$1(v$7) };
      |vall v$8 = 3;
      |vall v$9 = 4;
      |if (v$8 == v$9) v$4 else v$4
      """.stripMargin)

  // TODO add more cases
}
