name := "CMScala-compiler"

version := "1.0"

organization := "Purdue"

initialCommands in console := """
  import miniscala._
  import miniscala.{ SymbolicCPSTreeModule => H }
  import miniscala.{ SymbolicCPSTreeModuleLow => L }
"""
