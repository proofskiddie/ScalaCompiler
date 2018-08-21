package miniscala.test.ok

/** The set of OK-printing tests
 *  These can be used at any phase that has an interpreter. */
trait AllOKTests extends ConditionalOKTests with PrimitivesOKTests with LibraryOKTests with ConstructsOKTests {

  /** Fill this in depending on the phase + interpreter */
  def compileAndInterpret: String => Unit
}
