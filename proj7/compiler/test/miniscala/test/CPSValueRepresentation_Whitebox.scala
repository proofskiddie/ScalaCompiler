package miniscala.test

import miniscala.test.infrastructure.CPSLowTest
import org.junit.Test

/** Whitebox testing for entire program outputs */
class CPSValueRepresentation_Whitebox extends CPSLowTest {

  // Starting this "Value representation" assignment, we will not have whitebox
  // tests anymore. We will keep the black box tests, to check your submission
  // correctness, but from now on it's up to you to find the best translation.

  // Nevertheless, here's a test, to have an example:
  @Test def testValueReprOnePlusTwo =
    testCPSLowTreeEquality("1 + 2",
      """vall v$1 = 3;
        |vall v$2 = 5;
        |valp v$3 = v$1 + v$2;
        |vall v$4 = 1;
        |valp v$5 = v$3 - v$4;
        |vall v$6 = 1;
        |vall v$7 = 1;
        |valp v$8 = v$6 >> v$7;
        |v$8""".stripMargin)
}
