package miniscala.test

import miniscala.test.infrastructure.CPSLowTest
import miniscala.test.ok.AllOKTests

/** Blackbox testing for entire program outputs */
class CPSValueRepresentation_Blackbox extends CPSLowTest with AllOKTests {

  val compileAndInterpret = (src: String) => testCPSLowProgramOutput(source = src)
  // TODO: Add other specific tests here
}
