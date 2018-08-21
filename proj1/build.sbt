scalaVersion := "2.12.3"

scalacOptions in ThisBuild ++= Seq("-unchecked", "-deprecation", "-feature")

libraryDependencies += "org.scalatest" %% "scalatest" % "3.0.1" % "test"

logBuffered in Test := false

parallelExecution in Test := false
