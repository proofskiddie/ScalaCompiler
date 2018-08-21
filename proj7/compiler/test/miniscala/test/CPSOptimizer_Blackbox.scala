package miniscala.test

import miniscala.test.infrastructure.CPSOptTest
import miniscala.test.ok.AllOKTests

/** Blackbox testing for entire program outputs */
class CPSOptimizer_Blackbox extends CPSOptTest with AllOKTests {

  val compileAndInterpret = (src: String) => testCPSLowProgramOutput(source = src)
  // TODO: Add other specific tests here
}
