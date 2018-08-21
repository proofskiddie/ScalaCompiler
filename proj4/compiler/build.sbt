name := "CMScala-compiler"

version := "0.13.9"

organization := "Purdue"

initialCommands in console := """
  import miniscala._
  import miniscala.{ SymbolicCMScalaTreeModule => S }
  import miniscala.{ SymbolicCPSTreeModule => C }
"""
