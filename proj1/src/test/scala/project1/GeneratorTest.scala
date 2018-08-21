package project1

import java.io._
import org.scalatest._

// Define the stream method
trait TestOutput {
  val out = new ByteArrayOutputStream
  val pOut = new PrintWriter(out, true)
  def stream = pOut
  def emitCode(ast: Exp): Unit

  def code(ast: Exp) = {
    emitCode(ast)
    out.toString.stripLineEnd
  }
}

class StackGeneratorTest extends FunSuite {

  def runner(src: String, gData: Map[Char,Int] = Map()) = new ASMRunner(src, gData)

  // Function Helper for StackASMGenerator
  def testStackASMGenerator(ast: Exp, res: Int) = {
    val gen = new StackASMGenerator with TestOutput

    val code = gen.code(ast)
    val asm = runner(code)

    assert(asm.assemble == 0, "Code generated couldn't be assembled")
    assert(asm.run == res, "Invalid result")
  }

  test("SingleDigit") {
    testStackASMGenerator(Lit(2), 2)
  }

  // TODO more tests
}

class RegGeneratorTest extends FunSuite {

  def runner(src: String, gData: Map[Char,Int] = Map()) = new ASMRunner(src, gData)

  // Function Helper for StackASMGenerator
  def testRegASMGenerator(ast: Exp, res: Int) = {
    val gen = new RegASMGenerator with TestOutput

    val code = gen.code(ast)
    val asm = runner(code)

    assert(asm.assemble == 0, "Code generated couldn't be assembled")
    assert(asm.run == res, "Invalid result")
  }

  test("SingleDigit") {
    testRegASMGenerator(Lit(2), 2)
  }

  // TODO more tests
}
