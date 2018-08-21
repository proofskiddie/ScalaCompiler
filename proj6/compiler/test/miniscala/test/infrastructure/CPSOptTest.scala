package miniscala.test.infrastructure

import miniscala._
import miniscala.CPSTreeFormatter._

/**
 * Low-level CPS testing infrastructure, after the value representation transformation
 *
 * @author Vlad Ureche <vlad.ureche@epfl.ch>
 */
class CPSOptTest extends CPSLowTest with MainHelper {

  val LetL = classOf[CPSTreeModule#LetL]
  val LetF = classOf[CPSTreeModule#LetF]
  val LetK = classOf[CPSTreeModule#LetC]
  val LetP = classOf[CPSTreeModule#LetP]
  val AppF = classOf[CPSTreeModule#AppF]
  val AppK = classOf[CPSTreeModule#AppC]
  val If = classOf[CPSTreeModule#If]
  val Add = miniscala.CPSAdd.getClass()
  val Sub = miniscala.CPSSub.getClass()
  val Mul = miniscala.CPSMul.getClass()
  val Div = miniscala.CPSDiv.getClass()
  val Mod = miniscala.CPSMod.getClass()
  val BlockSet = miniscala.CPSBlockSet.getClass()
  val BlockGet = miniscala.CPSBlockGet.getClass()
  val BlockSize = miniscala.CPSBlockLength.getClass()
  val BlockTag = miniscala.CPSBlockTag.getClass()

  /** Unused */
  override def testCPSLowTreeEquality(source: String, expectedTree: String) = ???

  /** Tree equality */
  def testCPSOptTreeEquality(source: String, expectedTree: String) = {
    val pipeline =
      () => (CMScalaToCPSTranslator
             andThen CPSOptimizerHigh
             andThen CPSValueRepresenter
             andThen CPSHoister
             andThen CPSOptimizerLow
             andThen CPSVariableRenamePhase
             andThen TreeToString)
    val generatedTree = compileUsingPipeline(() => source, pipeline)
    assertEqual(source, "", generatedTree, expectedTree)
  }


  /** Checks stats on a tree */
  def testCPSOptStats(source: String, check: Statistics => Boolean, earlyOpt: Boolean = true, lateOpt: Boolean = true, input: String = "", expectedOutput: String = null) = {
    def opt[T](opt: Boolean, phase: T => T): (T => T) = if (opt) phase else (x: T) => x
    var interpreter: CPSInterpreterLowWithStats = null
    val pipeline =
      () => (CMScalaToCPSTranslator
             andThen opt(earlyOpt, treePrinter("Before early optimization")(SymbolicCPSTreeFormatter) andThen CPSOptimizerHigh andThen treePrinter("After early optimization"))
             andThen CPSValueRepresenter
             andThen CPSHoister
             andThen opt(lateOpt, treePrinter("Before late optimization")(SymbolicCPSTreeLowFormatter) andThen CPSOptimizerLow andThen treePrinter("After late optimization"))
             andThen treePrinter("Interpreted Tree")(SymbolicCPSTreeLowFormatter)
             andThen { interpreter = new CPSInterpreterLowWithStats(showStats = false); interpreter })
    val output = compileUsingPipelineAndRedirect(() => source, pipeline, input)
    if (expectedOutput != null)
      assertEqual(source, input, output, expectedOutput)
    assert(check(interpreter.stats), "Checks failed for: \n" + source + "\nStatistics:\n" + interpreter.stats)
  }

  /** Test Early Optimizer */
  def testCPSOptEarly(source: String, check: Statistics => Boolean) = testCPSOptStats(source, check, earlyOpt = true, lateOpt = false, input = "  ")

  /** Test Late Optimizer */
  def testCPSOptLate(source: String, check: Statistics => Boolean) = testCPSOptStats(source, check, earlyOpt = false, lateOpt = true, input = "  ")

  /** Test Both Optimizers, running sequentially */
  def testCPSBothSeq(source: String, check: Statistics => Boolean) = testCPSOptStats(source, check, earlyOpt = true, lateOpt = true, input = "  ")

  /** Test Both Optimizers, running in parallel */
  def testCPSBothPar(source: String, check: Statistics => Boolean) = { testCPSOptEarly(source, check); testCPSOptLate(source, check) }

  /** Checks the equality between the result produced by compiling and running
   *  the source code for a given input. Comparison is done string-wise,
   *  ignoring white spaces. Used for checking entire programs.
   */
  override def testCPSLowProgramOutput(source: String, input: String = "", expectedOutput: String = "OK") = {
    val pipeline =
      () => (CMScalaToCPSTranslator
             andThen CPSOptimizerHigh
             andThen CPSValueRepresenter
             andThen CPSHoister
             andThen CPSOptimizerLow
             andThen CPSHoistChecker
             andThen CPSInterpreterLow)
    val output = compileUsingPipelineAndRedirect(() => source, pipeline, input)
    assertEqual(source, input, output, expectedOutput)
  }
}
