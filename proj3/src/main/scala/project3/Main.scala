package project3

import java.io._
import scala.io._

trait CodeGenerator {
  // Define the PrintWriter used to emit
  // the code.
  val out = new ByteArrayOutputStream
  val pOut = new PrintWriter(out, true)
  def stream = pOut

  def emitCode(ast: Language.Exp): Unit

  // Emit the code and return the String
  // representation of the code
  def code(ast: Language.Exp) = {
    emitCode(ast)
    out.toString.stripLineEnd
  }
}

object Runner {
  import Language._

  def main(args: Array[String]): Unit = {

    val src = if (new File(args(0)).exists) {
      val source = Source.fromFile(args(0))
      try source.getLines mkString "\n" finally source.close()
    } else {
      args(0)
    }

    println("============ SRC CODE ============")
    println(src)
    println("==================================\n")

    val reader = new BaseReader(src, '\u0000')
    val scanner = new Scanner(reader)

    // Parser to test!
    // TODO: Change this as you finish parsers
    val parser = new ArrayParser(scanner)
    val ast = try {
      parser.parseCode
    } catch {
      case e: AbortException => return
      case e: Throwable => throw e
    }

    println("============= AST ================")
    println(ast)
    println("==================================\n")

    val analyzer = new SemanticAnalyzer(parser)
    println("======= Semantic Analyzer ========")
    val (nast, numWarning, numError) = analyzer.run(ast)
    if (numError > 0) {
      println("==================================\n")
      return
    }
    println("=========== Typed AST ============")
    print(nast)
    println(s": ${nast.tp}")
    println("==================================\n")



    val interpreter = if (args.contains("st_int"))
      new StackInterpreter
    else
      new ValueInterpreter
    println("========== Interpreter ===========")
    println(s"Exit Code: ${interpreter.run(nast)}")
    println("==================================\n")

    // Generator to test
    val generator = new X86Compiler with CodeGenerator
    val code = generator.code(nast)

    val runner = new ASMRunner(code)
    println("============ OUTPUT ==============")
    println(runner.code)
    println("==================================\n")

    if (runner.assemble != 0) {
      println("Compilation error!")
    } else {
      println("============ RESULT ==============")
      println(s"Exit Code: ${runner.run}")
      println("==================================")
    }
  }
}
