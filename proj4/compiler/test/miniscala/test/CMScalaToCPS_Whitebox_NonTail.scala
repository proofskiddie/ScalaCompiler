package miniscala.test

import ok.AllOKTests

import miniscala.test.infrastructure.CPSHighTest
import org.junit.Test

/** Whitebox testing for entire program outputs */
class CMScalaToCPS_Whitebox_NonTail extends CPSHighTest {

  // TODO: Test recursive functions

  @Test def testNonTailLiteral =
    testCPSHighTreeEquality("3", "vall v$1 = 3; vall v$2 = 0; v$2")

  @Test def testNonTailMultiLet =
    testCPSHighTreeEquality("val x = 1; val y = 2; y",
        "vall v$1 = 1; valp v$2 = id(v$1); vall v$3 = 2; valp v$4 = id(v$3); vall v$5 = 0; v$5")


  // TODO add more tests

}
