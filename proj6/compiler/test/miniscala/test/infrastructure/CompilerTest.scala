package miniscala.test.infrastructure

import miniscala._

/**
 * Common compiler testing infrastructure
 *
 * @author Vlad Ureche <vlad.ureche@epfl.ch>
 */
trait CompilerTest extends SandboxedTest {

  /** Compile the given source using a customizable set of phases given in pipeline */
  private def compileInner[T](source: () => String, pipeline: () => (miniscala.SymbolicCMScalaTreeModule.Tree => T)): T = {

    val dummyPosition: Int => (String,Int) = _ => ("test", 0)

    val src = source()
    val reader = new BaseReader(src, '\u0000')
    val scanner = new Scanner(reader, dummyPosition)

    // Parser to test!
    val parser = new MiniScalaParser(scanner)
    val ast = try {
      parser.parseCode
    } catch {
      case e: Throwable =>
        assert(false, s"parsing error:\n${e.getMessage}")
        ???
    }

    val analyzer = new SemanticAnalyzer(parser)
    val (nast, numWarning, numError) = analyzer.run(ast, CMScalaType.UnknownType)
    if (numError > 0) {
      assert(false, "semantic analyzer errors")
    }

    pipeline()(nast)
  }

  def compileUsingPipeline[T](source: () => String, pipeline: () => (miniscala.SymbolicCMScalaTreeModule.Tree => T)): T =
    sandboxedTest { compileInner(source, pipeline) }

  def compileUsingPipelineAndRedirect[T](source: () => String, pipeline: () => (miniscala.SymbolicCMScalaTreeModule.Tree => T), input: String): String =
    sandboxedTestWithRedirectedIO(compileInner(source, pipeline), input)

  def TreeToString[T](implicit f: Formatter[T]): TreeToString[T] = new TreeToString[T]

  /** A compiler phase that stores the tree as a string */
  class TreeToString[T](implicit f: Formatter[T]) extends Function1[T, String] {
    def apply(t: T): String = {
      val output = new java.io.StringWriter()
      f.toDocument(t).format(78, output)
      output.toString
    }
  }
}
