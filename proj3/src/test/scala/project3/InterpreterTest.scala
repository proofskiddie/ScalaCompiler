package project3

import org.scalatest._

class InterpretTest extends FunSuite {
  import Language._
  import StackVal._

  def testInterpreter(ast: Exp, res: Any) = {
    val interpreter = new StackInterpreter

    assert(res == interpreter.run(ast), "Interpreter does not return the correct value")
  }

  test("arithm") {
    testInterpreter(Lit(-21), Cst(-21))
    testInterpreter(Prim("-", List(Lit(10), Lit(2))), Cst(8))
  }

}
