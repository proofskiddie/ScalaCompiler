package miniscala.test

import miniscala.test.infrastructure.CPSHighTest
import miniscala.test.ok.AllOKTests

/** Blackbox testing for entire program outputs */
class CMScalaToCPS_Blackbox extends CPSHighTest with AllOKTests {

  val compileAndInterpret = (src: String) => testCPSHighProgramOutput(source = src)
  // TODO: Add other specific tests here
}
