package miniscala
package test.ok

import miniscala.MiniScalaFileReader.expandModules
import org.junit.Test

trait LibraryOKTests extends MainHelper {
  this: AllOKTests =>

  // TODO: This is dangerous, the students can inject an infinite loop via the library:
  lazy val library: String = {
    val fs = java.nio.file.FileSystems.getDefault
    val inFiles = expandModules(Seq("../library/miniscala.lib")).distinct
    val inSource = inFiles.map({ f => scala.io.Source.fromFile(f.toString).mkString }).mkString("\n")
    println(inSource)
    inSource
  }

  def compileAndInterpretWithLib: String => Unit = (source: String) => compileAndInterpret(library + "\n" + source)

  @Test def testLibFunctions3 =
    compileAndInterpretWithLib("""
     |def succ(x: Int) = x + 1;
     |def twice(x: Int) = x + x;
     |printChar(functionCompose[Int,Int,Int](succ, twice)(39).toChar);
     |printChar(functionCompose[Int,Int,Int](succ, succ)(73).toChar);
     |printChar(functionCompose[Int,Int,Int](twice, succ)(4).toChar)
    """.stripMargin)

  @Test def testLibLists1 =
    compileAndInterpretWithLib("""
      |printChar(if (Nil[Int].isEmpty) 'O' else 'K');
      |printChar(if ((42::Nil).isList) 'K' else 'O');
      |printChar(if (42.isList) '*' else '\n')
    """.stripMargin)

  @Test def testLibLists2 =
    compileAndInterpretWithLib("""
      |val l = 'O'::'K'::'\n'::Nil;
      |printChar(l.head);
      |printChar(l.tail.head);
      |printChar(l.tail.tail.head)
    """.stripMargin)

  @Test def testLibLists3 =
    compileAndInterpretWithLib("""
      |val l = listMake3[Char]('O', 'K', '\n');
      |listForeach[Char](printChar, l)
    """.stripMargin)

  @Test def testLibLists4 =
    compileAndInterpretWithLib("""
      |val intPrintAsChar = functionCompose[Int,Char,Unit](printChar, (x: Int) => x.toChar);
      |val l = listMake3[Int](78, 74, 9);
      |listForeach[Int](intPrintAsChar, listMap[Int,Int]((x: Int) => x + 1, l))
    """.stripMargin)

  @Test def testLibLists5 =
    compileAndInterpretWithLib("""
      |val intPrintAsChar = functionCompose[Int,Char,Unit](printChar, (x: Int) => x.toChar);
      |val o = listMake1[Int](79);
      |val k = listMake3[Int](3, 5, 5);
      |val nl = listMake2[Int](2, 5);
      |def prod(l: List[Int]) = listFoldLeft[Int,Int]((x: Int, y: Int) => x * y, 1, l);
      |intPrintAsChar(prod(o));
      |intPrintAsChar(prod(k));
      |intPrintAsChar(prod(nl))
    """.stripMargin)

  @Test def testLibLists6 =
    compileAndInterpretWithLib("""
      |val intPrintAsChar = functionCompose[Int,Char,Unit](printChar, (x: Int) => x.toChar);
      |val o = listMake1[Int](79);
      |val k = listMake3[Int](3, 5, 5);
      |val nl = listMake2[Int](2, 5);
      |def prod(l: List[Int]) = listFoldRight[Int,Int]((x: Int, y: Int) => x * y, 1, l);
      |intPrintAsChar(prod(o));
      |intPrintAsChar(prod(k));
      |intPrintAsChar(prod(nl))
    """.stripMargin)

  @Test def testLibLists7 =
    compileAndInterpretWithLib("""
      |val intPrintAsChar = functionCompose[Int,Char,Unit](printChar, (x: Int) => x.toChar);
      |val l = listMake8[Int](1, 79, 2, 3, 1, 75, 10, 2);
      |listForeach[Int](intPrintAsChar, listFilter[Int]((x: Int) => x >= 10, l))
    """.stripMargin)

  @Test def testLibLists8 =
    compileAndInterpretWithLib("""
      |val intPrintAsChar = functionCompose[Int,Char,Unit](printChar, (x: Int) => x.toChar);
      |val l = listMake3[Int](75, 10, 79);
      |val yn = listPartition[Int]((c: Int) => c < 79, l);
      |listForeach[Int](intPrintAsChar, yn._2);
      |listForeach[Int](intPrintAsChar, yn._1)
    """.stripMargin)

  @Test def testLibLists9 =
    compileAndInterpretWithLib("""
      |val l = listMake6[Char]('O', 'K', '\n', 'K', 'O', '\n');
      |listForeach[Char](printChar, listTake[Char](l, 3))
    """.stripMargin)

  @Test def testLibLists10 =
    compileAndInterpretWithLib("""
      |val l = listMake6[Char]('K', 'O', '\n', 'O', 'K', '\n');
      |listForeach[Char](printChar, listDrop[Char](l, 3))
    """.stripMargin)

  @Test def testLibLists11 =
    compileAndInterpretWithLib("""
      |val intPrintAsChar = functionCompose[Int,Char,Unit](printChar, (x: Int) => x.toChar);
      |val l5 = listMake5[Int](0,0,0,0,0);
      |val l9 = listTabulate[Int](9, (x: Int) => x);
      |intPrintAsChar(70 + listLength[Int](l9));
      |intPrintAsChar(70 + listLength[Int](l5));
      |intPrintAsChar(10 - listLength[Int](Nil))
    """.stripMargin)

  @Test def testLibLists12 =
    compileAndInterpretWithLib("""
      |val l = listMake3[Char]('\n', 'K', 'O');
      |listForeach[Char](printChar, listReverse[Char](l))
    """.stripMargin)

  @Test def testLibLists13 =
    compileAndInterpretWithLib("""
      |val l1 = listMake2[Char]('O', 'K');
      |val l2 = listMake1[Char]('\n');
      |listForeach[Char](printChar, listAppend[Char](l1, l2))
    """.stripMargin)

  @Test def testLibStrings1 =
    compileAndInterpretWithLib("""
      |printString("OK");
      |printChar('\n')
    """.stripMargin)

  @Test def testLibStrings2 =
    compileAndInterpretWithLib("""
      |val s = "KO";
      |printChar(s(1));
      |printChar(s(0));
      |printChar('\n')
    """.stripMargin)

  @Test def testLibStrings3 =
    compileAndInterpretWithLib("""
      |printChar("OOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOO".length.toChar);
      |printChar("KKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKK".length.toChar);
      |printChar("1111100000".length.toChar)
    """.stripMargin)
}
