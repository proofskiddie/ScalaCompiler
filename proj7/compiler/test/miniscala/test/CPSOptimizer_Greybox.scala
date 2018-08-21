package miniscala
package test

import org.junit.Test
import miniscala.test.infrastructure.CPSOptTest

/** Greybox testing for entire program outputs:
 *    - much like blackbox tests, but can access the internal state of the interpreter
 *    - they can query how many instructions or primitives have been executed for example */
class CPSOptimizer_Greybox extends CPSOptTest {

  // ETA REDUCTION
  @Test def testEtaReduction =
    testCPSOptEarly("""
      def f(x: Int) = x; def g(y: Int) = f(y); def h(z: Int) = g(z);
      g(1) + g(2) + g(3) + h(1) + h(2) + h(3) + f(1) + f(2) + f(3)
    """, _.getFuncs <= 2)

  @Test def testEtaReductionInfintelyRecursiveFunction = // needs to keep the resulting infinitely-recursive function
    testCPSOptEarly("""def f(x: Int): Int = g(x); def g(x: Int): Int = f(x); if (getchar() == -1) g(3) else 0""", _.getFuncs == 1)

  // DEAD CODE ELIMINATION
  @Test def testDCEFunsSimple =
    testCPSOptEarly("def f(x: Int): Int = f(x); ()", _.getFuncs == 0)

  @Test def testDCEFunsRecursive1 =
    testCPSOptEarly("def f(x: Int): Int = g(x) + 1; def g(y: Int): Int = f(y) + 1; 0", _.getFuncs == 0)

  @Test def testDCEFunsRecursive2 =
    testCPSOptEarly("def f(x: Int): Int = g(x) + 1; def g(y: Int): Int = f(y) + 1; def h(z: Int) = z; 0", _.getFuncs == 0)

  @Test def testDCEFunsRecursive3WithEtaReduction =
    testCPSOptEarly("def f(x: Int): Int = if (x == 0) 0 else g(x - 1); def g(y: Int): Int = f(y); def h(z: Int) = z; f(0) + f(0) + f(0)", _.getFuncs <= 1)

  @Test def testDCELetLiteral =
    testCPSBothSeq("val u = 1; 0", _.get(LetL) == 1)

  @Test def testDCELetPrimitive =
    testCPSOptEarly("val x = 80.toChar; 0", _.get(LetP) == 1)

  // INLINING
  @Test def testFunInlining =
    testCPSOptEarly("def f(x: Int) = x; f(1)", _.get(AppF) == 0)

  @Test def testFunInliningInsideFunctionBodySameLetRec =
    testCPSOptEarly("def f(x: Int) = x; def g(x: Int) = f(x); g(1)", _.get(AppF) == 0)

  @Test def testFunInliningInsideFunctionBodyDifferentLetRecs =
    testCPSOptEarly("def f(x: Int) = x; val o = 1; def g(x: Int) = f(x); g(o)", _.get(AppF) == 0)

  @Test def testFunInliningCrasher =
    testCPSOptEarly("def f(x: Int): Int = if (x == 0) 0 else g(x - 1); def g(y: Int) = f(y); def h(z: Int) = z; f(0)", _.get(AppF) == 0)

  @Test def testFunInliningRecursiveTrick =
    testCPSOptEarly("def f(x: Int): Int = g(x); def g(y: Int) = f(y); def h(z: Int) = z; h(3)", _.get(AppF) == 0)

  @Test def testContInlining =
    testCPSOptEarly("val x = 1; x", _.get(AppK) == 0)

  @Test def testContInliningInsideContBody =
    testCPSOptEarly("val x = 1; val y = 2; x + y", _.get(AppK) == 0)

  // CONSTANT FOLDING
  @Test def testConstantFoldingIntP =
    testCPSOptLate("val x = 1.isInt; ()", stats => stats.get(LetP) == 0 && stats.get(If) == 0)

  @Test def testConstantFoldingIntPNot =
    testCPSOptLate("val x = ().isUnit; ()", stats => stats.get(LetP) == 0 && stats.get(If) == 0)

  @Test def testConstantFoldingPlus =
    testCPSOptLate("2 + 1", stats => stats.get(LetP) == 0)

  @Test def testConstantFoldingMinus =
    testCPSOptLate("2 - 1", stats => stats.get(LetP) == 0)

  @Test def testConstantFoldingTimes =
    testCPSOptLate("2 * 1", stats => stats.get(LetP) == 0)

  @Test def testConstantFoldingDiv =
    testCPSOptLate("2 / 1", stats => stats.get(LetP) == 0)

  @Test def testConstantFoldingMod =
    testCPSOptLate("2 % 1", stats => stats.get(LetP) == 0)

  @Test def testConstantFoldingIntChar =
    testCPSOptLate("10.toChar", stats => stats.get(LetP) == 0)

  @Test def testConstantFoldingCharInt =
    testCPSOptLate("'a'.toInt", stats => stats.get(LetP) == 0)

  @Test def testConstantFoldingTypePrims = {
    for (prim <- List("isBool", "isUnit", "isInt"))
      for (value <- List("true", "false", "2", "()", "'x'"))
        // The early optimizer should be enough to
        // eliminate these simple type primitives:
        testCPSOptEarly(s"$value.$prim",
            stats => stats.get(LetP) == 1 && stats.get(If) == 0)
  }

  @Test def testConstantFoldingBooleanAnd =
    testCPSOptEarly("true && false", stats => stats.get(LetP) == 1 && stats.get(If) == 0)

  @Test def testConstantFoldingBooleanOr =
    testCPSOptEarly("true || false", stats => stats.get(LetP) == 1 && stats.get(If) == 0)

  @Test def testConstantFoldDCEContinuations =
    testCPSOptEarly("if (true) 1 else 2", _.get(LetK) == 0)

  // CONSTANT PROPAGATION
  @Test def testConstantPropagationSimple =
    testCPSBothSeq("putchar((((getchar()/3)/3)/3))", _.get(LetL) <= 4)

//  not supported by current optimizer: FIXME: Update to latest l3!
//
  @Test def testConstantCapturingInFunction1 =
    testCPSBothSeq("val a = 1; val b = 2; val c = 3; def f(x: Int) = x + a + b + c; putchar(f(getchar()) + f(1) + f(1))", _.get(BlockSet) <= 1)

  @Test def testConstantCapturingInFunction2 =
    testCPSBothSeq("val one = 1; def f(x: Int) = x + one; f(1) + f(2) + f(3) + one", _.get(LetL) == 1)

  // NEUTRAL ELEMENTS
  @Test def testNeutralElementsAddZero1 =
    testCPSBothSeq("val u = getchar(); putchar(u + 0)", _.get(Add) == 0)

  @Test def testNeutralElementsAddZero2 =
    testCPSBothSeq("val u = getchar(); putchar(u + 0)", _.get(Add) == 0)

  @Test def testNeutralElementsSubZero =
    testCPSBothSeq("val u = getchar(); putchar(u - 0)", _.get(Sub) == 0)

  @Test def testNeutralElementsSubItself =
    testCPSBothSeq("val u = getchar(); putchar(u - u)", _.get(Sub) == 0)

  @Test def testNeutralElementsMulOne1 =
    testCPSBothSeq("val u = getchar(); putchar(u * 1)", _.get(Mul) == 0)

  @Test def testNeutralElementsMulOne2 =
    testCPSBothSeq("val u = getchar(); putchar(1 * u)", _.get(Mul) == 0)

  @Test def testNeutralElementsMulZero1 =
    testCPSBothSeq("val u = getchar(); putchar(u * 0)", _.get(Mul) == 0)

  @Test def testNeutralElementsMulZero2 =
    testCPSBothSeq("val u = getchar(); putchar(0 * u)", _.get(Mul) == 0)

  @Test def testNeutralElementsDivOne =
    testCPSBothSeq("val u = getchar(); putchar(u / 1)", _.get(Div) == 0)

  // COMMON SUBEXPRESSION ELIMINATION
  @Test def testCommonSubexpressionEliminationSimpleBlockTag =
    testCPSBothSeq("val a = new Array[Int](1); putchar(if (a.isList || a.isArray) 96 else 87)", _.get(BlockTag) <= 1)

  @Test def testCommonSubexpressionEliminationComplexBlockTag =
    testCPSBothSeq("val a = new Array[Int](300); val p = putchar(getchar()); putchar((if (a.isArray) 90 else 80) + (if (a.isList) 6 else 7))", _.get(BlockTag) <= 1)

  // USE MULTIPLE MICROPHASES
  @Test def testFunInlingAndDCE =
    testCPSOptEarly("def f(x: Int) = x; def g(y: Boolean, z: Int) = f(z); g", _.getFuncs == 0)

  // Yes, it's possible only with inlining, constant folding and DCE:
  @Test def testInliningConstantFoldingDCE =
    testCPSOptTreeEquality(
        """def printChar(c: Int) = putchar(c);
           def functionCompose(f: Int => Int, g: Int => Int) = (x: Int) => f(g(x));
           def plus(x: Int, y: Int) = x + y;
           def succ(x: Int) = x + 1;
           def twice(x: Int) = x + x;
           printChar(functionCompose(succ,twice)(39));
           printChar(functionCompose(succ,succ)(73));
           printChar(functionCompose(twice,succ)(4))""",
        """vall v$1 = 79;
           valp v$2 = byte-write(v$1);
           vall v$3 = 75;
           valp v$4 = byte-write(v$3);
           vall v$5 = 10;
           valp v$6 = byte-write(v$5);
           vall v$7 = 0;
           v$7"""
    )
}
