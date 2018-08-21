package project3

import java.io._
import org.scalatest._

class ParserTest extends FunSuite {
  import Language._

  def scanner(src: String) = new Scanner(new BaseReader(src, '\u0000'))

  def testBaseParser(op: String, res: Exp) = {
    val gen = new BaseParser(scanner(op))
    val ast = gen.parseCode

    assert(ast == LetRec(Nil, res), "Invalid result")
  }

  test("SingleDigit") {
    testBaseParser("1", Lit(1))
  }

  test("GenericPrecedence") {
    testBaseParser("2-4*3", Prim("-", List(Lit(2), Prim("*", List(Lit(4), Lit(3))))))
  }

  test("ParseType") {
    testBaseParser("val x: Int = 1; 2", Let("x", IntType, Lit(1), Lit(2)))
  }

  test("ParseOptionalType") {
    testBaseParser("val x = 1; 2", Let("x", UnknownType, Lit(1), Lit(2)))
  }
}
