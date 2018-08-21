package miniscala

import scala.io._
import scala.collection.mutable.ArrayBuilder

/**
 * File reading for MiniScala (both modules and source files).
 *
 * @author Michel Schinz <Michel.Schinz@epfl.ch>
 * @author Gregory Essertel
 */

object MiniScalaFileReader {
  def expandModules(paths: Seq[String]): Seq[String] = paths flatMap { path =>
    if (path.endsWith(".lib")) {
      val file = Source.fromFile(path)
      val relPath = path.split("/")
      val pref = relPath.slice(0, relPath.length - 1).mkString("/") + "/"
      file.getLines.toSeq.filter(_ != "").flatMap { f =>
        expandModules(Seq(pref + f))
      }
    } else {
      Seq(path)
    }
  }

  def readFiles(paths: Seq[String]): (String, Int=>(String,Int)) = {

    val allFiles = expandModules(paths).distinct

    def indexToPosition(indices: Array[Int])
                       (index: Int): (String, Int) = {

      var p = 1;
      while (p < indices.length && indices(p) <= index) p += 1
      (allFiles((p - 1) min (allFiles.length - 1)), index - indices(p - 1))
    }

    val progB = new StringBuilder()
    val indicesB: ArrayBuilder[Int] = ArrayBuilder.make()
    var totLines = 0
    indicesB += 0
    for (path <- allFiles) {
      val file = Source.fromFile(path)
      try {
        val lines = file.getLines.toList

        totLines += lines.length
        progB ++= lines mkString "\n"
        progB += '\n'

        indicesB += totLines
      } finally file.close()
    }
    (progB.result, indexToPosition(indicesB.result))
  }
}
