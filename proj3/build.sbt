scalaVersion := "2.12.3"

scalacOptions in ThisBuild ++= Seq("-unchecked", "-deprecation", "-feature")

libraryDependencies += "org.scalatest" %% "scalatest" % "3.0.1" % "test"

excludeFilter in unmanagedSources := HiddenFileFilter || "*sample*"

logBuffered in Test := false

parallelExecution in Test := false

initialCommands in console := """
  import project3._
  import Language._
  import Tokens._
  val src = "def b(r: Int):Int = 5; b(1)"
  val b = new BaseReader(src,'\u0000')
  val s = new Scanner(b)
  val fp = new ArrayParser(s)
//  val fakeParser = new Parser(null) {
//    override def error(msg: String, pos: Position) = {}
//    override def warn(msg: String, pos: Position) = {}
//  }
  val sa = new SemanticAnalyzer(fp)
  val st = new StackInterpreter
"""
