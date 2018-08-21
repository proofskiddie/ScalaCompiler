package miniscala.test.ok
import org.junit.Test

trait ConditionalOKTests {
  this: AllOKTests =>

  @Test def testConditional1 =
    compileAndInterpret("""
    { putchar('O'.toInt); false } && { putchar('*'.toInt); true };
    true && { putchar('K'.toInt); true };
    putchar('\n'.toInt)
    """)

  @Test def testConditional2 =
    compileAndInterpret("""
      { putchar('O'.toInt); true } || { putchar('*'.toInt); true };
      false || { putchar('K'.toInt); true };
      putchar('\n'.toInt)
      """
    )

  @Test def testSideEffectingCondition =
    compileAndInterpret("""
      if (putchar('O'.toInt) == ()) {
        if (putchar('K'.toInt) == ()) {
          if (putchar(10) == ()) // don't optimize this away!
            true
          else
            true
        } else {
          true
        }
      } else {
        true
      }
    """)

  @Test def testConditional4 =
    compileAndInterpret("""
      if (if (putchar('O'.toInt) == ()) true else true) {
        putchar('K'.toInt)
      } else {
        putchar('T'.toInt)
      }
      """)
}
