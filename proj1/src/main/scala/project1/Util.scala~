package project1

import java.io._
import scala.sys.process._

// Error reporting
trait Reporter {

  // report an error
  def error(s: String): Unit = System.err.println(s"Error: $s.")
  // report error and halt
  def abort(s: String): Nothing = { error(s); throw new Exception()}

  def expected(s: String): Nothing = abort(s"$s expected")
}

// Utilities to emit code
trait Codegen {

  def stream: PrintWriter

   // output
   def emit(s: String): Unit = stream.print('\t' + s)
   def emitln(s: String): Unit = stream.println('\t' + s)
}

// Scanner/Parser base classes
abstract class Reader[T] {
  def peek: T
  def hasNext: Boolean
  def hasNext(f: T => Boolean): Boolean
  def next(): T
}

class BaseReader[T](input: Iterator[T], eof: T) extends Reader[T] {
  var peek = if (input.hasNext) input.next() else eof
  def hasNext: Boolean = peek != eof
  def hasNext(f: T => Boolean) = f(peek)
  def next() = {
    val res = peek
    peek = if (input.hasNext) input.next() else eof
    res
  }
}

// ASM bootstrapping
class ASMRunner(snipet: String, gData: Map[Char,Int]) {

  val data = if (gData.size > 0) {
    ".data\n" + (gData map {
      case (k,v) => s"$k:\t.quad $v"
    } mkString "\n")
  } else ""

  val template =
    s"""|.text
        |\t.global entry_point
        |
        |entry_point:
        |\tpush %rbp\t# save stack frame for C convention
        |\tmov %rsp, %rbp
        |
        |\t# beginning generated code
        |${snipet}
        |\t# end generated code
        |\t# %rax contains the result
        |
        |\tmov %rbp, %rsp\t# reset frame
        |\tpop %rbp
        |\tret
        |
        |$data
        |""".stripMargin

  def code = template

  def assemble = {
    val file = new File("gen/gen.s")
    val writer = new PrintWriter(file)

    writer.println(template)
    writer.flush
    writer.close

    Seq("gcc","gen/bootstrap.c","gen/gen.s","-o","gen/out").!.toInt
  }

  def run = {
    val stdout = "gen/out".!!
    // output format: Result: <res>\n
    stdout.split(" ").last.trim.toInt
  }
}
