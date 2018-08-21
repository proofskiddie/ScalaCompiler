package miniscala.test.ok
import org.junit.Test

trait PrimitivesOKTests {
  this: AllOKTests =>

  @Test def testPrimitiveArithmetic1 =
    compileAndInterpret("""
      |putchar(1 + 78);
      |putchar(6 + 69);
      |putchar(10)
    """.stripMargin)

  @Test def testPrimitiveArithmetic2 =
    compileAndInterpret("""
      |putchar(80 - 1);
      |putchar(85 - 10);
      |putchar(10)
    """.stripMargin)

  @Test def testPrimitiveArithmetic3 =
    compileAndInterpret("""
      |putchar(2 * 3 * 13 + 1);
      |putchar(3 * 5 * 5);
      |putchar(10)
    """.stripMargin)

  @Test def testPrimitiveArithmetic4 =
    compileAndInterpret("""
      |putchar(158 / 2);
      |putchar(147976 / 1973);
      |putchar(10)
    """.stripMargin)

  @Test def testPrimitiveArithmetic5 =
    compileAndInterpret("""
      |putchar(159 % 80);
      |putchar(153075 % 1000);
      |putchar(10)
    """.stripMargin)

  @Test def testPrimitiveArithmetic6 =
    compileAndInterpret("""
      |putchar((5 << 4) - 1);
      |putchar((37 << 1) + 1);
      |putchar(10)
    """.stripMargin)

  @Test def testPrimitiveArithmetic7 =
    compileAndInterpret("""
      |putchar(1264 >> 4);
      |putchar(150 >> 1);
      |putchar(10)
    """.stripMargin)

  @Test def testPrimitiveArithmetic8 =
    compileAndInterpret("""
      |putchar(65535 & 79);
      |putchar(91 & 111);
      |putchar(10)
    """.stripMargin)

  @Test def testPrimitiveArithmetic9 =
    compileAndInterpret("""
      |putchar(0 | 79);
      |putchar(72 | 67);
      |putchar(10)
    """.stripMargin)

  @Test def testPrimitiveArithmetic10 =
    compileAndInterpret("""
      |putchar(127 ^ 48);
      |putchar(101 ^ 46);
      |putchar(10)
    """.stripMargin)

  @Test def testPrimitiveBlocks1 =
    compileAndInterpret("""
      |val nl = 10.toChar;
      |val v = "OK";
      |putchar((if (v.isBlock) 'O' else 'K').toInt);
      |putchar((if (1.isBlock) 'O' else 'K').toInt);
      |putchar(nl.toInt)
      |
    """.stripMargin)

  @Test def testPrimitiveBlocks2 =
    compileAndInterpret("""
     |def nl() = 10.toChar;
     |val v = "OK";
     |putchar(v(0).toInt);
     |putchar(v(1).toInt);
     |putchar(nl().toInt)
    """.stripMargin)

  @Test def testPrimitiveBlocks3 =
    compileAndInterpret("""
     |def nl() = 10.toChar;
     |val v = "KO";
     |v(0) = 'O';
     |v(1) = 'K';
     |putchar(v(0).toInt);
     |putchar(v(1).toInt);
     |putchar(nl().toInt)
    """.stripMargin)

  @Test def testPrimitiveBlocks4 =
    compileAndInterpret("""
     |def nl() = 10.toChar;
     |val v = "KO";
     |putchar(v.length + 77);
     |putchar(v.length + 73);
     |putchar(nl().toInt)
    """.stripMargin)

  @Test def testPrimitiveBlocks5 =
    compileAndInterpret("""
     |def nl() = 10.toChar;
     |val v = "qq";
     |v(0) = 'O';
     |v(1) = 'K';
     |putchar(v(0).toInt);
     |putchar(v(1).toInt);
     |putchar(nl().toInt)
    """.stripMargin)

  // @Test def testPrimitiveBlocks6 =
  //   compileAndInterpret("""
  //     (def nl (@int->char 10))
  //     |putchar(@block-tag (@block-alloc-79 12)))
  //     |putchar(@block-tag (@block-alloc-75 12)))
  //     |putchar(@char->int nl))
  //   """.stripMargin)

  @Test def testPrimitiveBlocks7 =
    compileAndInterpret("""
     |def nl() = 10.toChar;
     |val v = "q";
     |val u = "q";
     |putchar((if (v == u) 'K' else 'O').toInt);
     |putchar((if (v != u) 'K' else 'O').toInt);
     |putchar(nl().toInt)
    """.stripMargin)

  // @Test def testPrimitiveLogic1 =
  //   compileAndInterpret("""
  //     (def newline (fun () |putchar(10)))
  //     |putchar(@char->int (if (@block? "") 'O' 'K')))
  //     |putchar(@char->int (if (@block? (@block-alloc-1 1)) 'K' 'O')))
  //     (newline)
  //   """.stripMargin)

  // @Test def testPrimitiveLogic2 =
  //   compileAndInterpret("""
  //     (def newline (fun () |putchar(10)))
  //     |putchar(@char->int (let ((v (@block? ""))) (if v 'O' 'K'))))
  //     |putchar(@char->int (let ((v (@block? (@block-alloc-1 1)))) (if v 'K''O'))))
  //     (newline)
  //   """.stripMargin)

  @Test def testPrimitiveLogic3 =
    compileAndInterpret("""
      |def nl() = putchar(10);
      |putchar((if (0.isInt) 'O' else 'K').toInt);
      |putchar((if ('K'.isInt) 'O' else 'K').toInt);
      |nl()
    """.stripMargin)

  @Test def testPrimitiveLogic4 =
    compileAndInterpret("""
      |def nl() = putchar(10);
      |putchar({ val v = 0.isInt; (if (v) 'O' else 'K').toInt });
      |putchar({ val v = 'K'.isInt; (if (v) 'O' else 'K').toInt });
      |nl()
    """.stripMargin)

  @Test def testPrimitiveLogic5 =
    compileAndInterpret("""
      |def nl() = putchar(10);
      |putchar((if (true.isBool) 'O' else 'K').toInt);
      |putchar((if (false.isBool) 'K' else 'O').toInt);
      |nl()
    """.stripMargin)

  @Test def testPrimitiveLogic6 =
    compileAndInterpret("""
      |def nl() = putchar(10);
      |putchar((if (1 < 2) 'O' else 'K').toInt);
      |putchar((if (1 < 1) 'O' else 'K').toInt);
      |nl()
    """.stripMargin)

  @Test def testPrimitiveLogic7 =
    compileAndInterpret("""
      |def nl() = putchar(10);
      |putchar({ val v = 1 < 2; (if (v) 'O' else 'K').toInt });
      |putchar({ val v = 1 < 1; (if (v) 'O' else 'K').toInt });
      |nl()
    """.stripMargin)

  @Test def testPrimitiveLogic8 =
    compileAndInterpret("""
      |def nl() = putchar(10);
      |putchar((if (2 >= 1) 'O' else 'K').toInt);
      |putchar((if (1 >= 1) 'K' else 'O').toInt);
      |nl()
    """.stripMargin)

  @Test def testPrimitiveLogic9 =
    compileAndInterpret("""
      |def nl() = putchar(10);
      |putchar({ val v = 1 >= 1; (if (v) 'O' else 'K').toInt });
      |putchar({ val v = 1 >= 2; (if (v) 'O' else 'K').toInt });
      |nl()
    """.stripMargin)

  @Test def testPrimitiveLogic10 =
    compileAndInterpret("""
      |def nl() = putchar(10);
      |putchar((if (2 > 1) 'O' else 'K').toInt);
      |putchar((if (1 > 1) 'O' else 'K').toInt);
      |nl()
    """.stripMargin)

  @Test def testPrimitiveLogic11 =
    compileAndInterpret("""
      |def nl() = putchar(10);
      |putchar({ val v = 2 > 1; (if (v) 'O' else 'K').toInt });
      |putchar({ val v = 1 > 1; (if (v) 'O' else 'K').toInt });
      |nl()
    """.stripMargin)

  @Test def testPrimitiveLogic12 =
    compileAndInterpret("""
      |def nl() = putchar(10);
      |putchar((if (1 == 1) 'O' else 'K').toInt);
      |putchar((if (2 == 1) 'O' else 'K').toInt);
      |nl()
    """.stripMargin)

  @Test def testPrimitiveLogic13 =
    compileAndInterpret("""
      |def nl() = putchar(10);
      |putchar({ val v = 1 == 1; (if (v) 'O' else 'K').toInt });
      |putchar({ val v = 1 == 2; (if (v) 'O' else 'K').toInt });
      |nl()
    """.stripMargin)

  @Test def testPrimitiveLogic14 =
    compileAndInterpret("""
      |def nl() = putchar(10);
      |putchar((if (true != false) 'O' else 'K').toInt);
      |putchar((if (false != false) 'O' else 'K').toInt);
      |nl()
    """.stripMargin)


  @Test def testPrimitiveLogic15 =
    compileAndInterpret("""
      |def nl() = putchar(10);
      |putchar((if (true.isBool) 'O' else 'K').toInt);
      |putchar((if ("true".isBool) 'O' else 'K').toInt);
      |nl()
    """.stripMargin)

  @Test def testPrimitiveLogic16 =
    compileAndInterpret("""
      |def nl() = putchar(10);
      |putchar((if (().isUnit) 'O' else 'K').toInt);
      |putchar((if (true.isUnit) 'O' else 'K').toInt);
      |nl()
    """.stripMargin)

  @Test def testPrimitiveLogic17 =
    compileAndInterpret("""
      |def nl() = putchar(10);
      |putchar((if (!false) 'O' else 'K').toInt);
      |putchar((if (!true) 'O' else 'K').toInt);
      |nl()
    """.stripMargin)

  @Test def testPrimitiveLogic18 =
    compileAndInterpret("""
      |def nl() = putchar(10);
      |putchar({ val v = true.isBool; (if (v) 'O' else 'K').toInt });
      |putchar({ val v = "false".isBool; (if (v) 'O' else 'K').toInt });
      |nl()
    """.stripMargin)

  @Test def testPrimitiveLogic19 =
    compileAndInterpret("""
      |def nl() = putchar(10);
      |putchar({ val v = 1.isBool; (if (v) 'K' else 'O').toInt });
      |putchar({ val v = ().isBool; (if (v) 'O' else 'K').toInt });
      |nl()
    """.stripMargin)

  @Test def testPrimitiveLog20 =
    compileAndInterpret("""
      |def nl() = putchar(10);
      |putchar({ val v = 3.isUnit; (if (v) 'K' else 'O').toInt });
      |putchar({ val v = ().isUnit; (if (v) 'K' else 'O').toInt });
      |nl()
    """.stripMargin)

  @Test def testPrimitiveLog21 =
    compileAndInterpret("""
      |def nl() = putchar(10);
      |putchar({ val v = '3'.isChar; (if (v) 'O' else 'K').toInt });
      |putchar({ val v = 65.isChar; (if (v) 'O' else 'K').toInt });
      |nl()
    """.stripMargin)

  @Test def testPrimitiveLogic22 =
    compileAndInterpret("""
      |def nl() = putchar(10);
      |putchar({ val v = !true; (if (v) 'K' else 'O').toInt });
      |putchar({ val v = !false; (if (v) 'K' else 'O').toInt });
      |nl()
    """.stripMargin)
  @Test def testPrimitiveLogic23 =
    compileAndInterpret("""
                          |def nl() = putchar(10);
                          |var x = 10;
                          |putchar({ val v = x > 10; (if (v) 'K' else 'O').toInt });
                          |putchar({ val v = x < 11; (if (v) 'K' else 'O').toInt });
                          |nl()
                        """.stripMargin)
  @Test def testPrimitiveLogic24 =
    compileAndInterpret("""
                          |def nl() = putchar(10);
                          |var x = 10;
                          |putchar({ val v = (x != 10); (if (v) 'K' else 'O').toInt });
                          |x = x+1;
                          |putchar({ val v = x == 11; (if (v) 'K' else 'O').toInt });
                          |nl()
                        """.stripMargin)
  @Test def testPrimitiveLogic25 =
    compileAndInterpret("""
                          |def nl() = putchar(10);
                          |var x = 10;
                          |while(x<100)
                          |x=x+1;
                          |putchar({ val v = (x != 100); (if (v) 'K' else 'O').toInt });
                          |while(x>0)
                          |x=x-1;
                          |putchar({ val v = (x == 0); (if (v) 'K' else 'O').toInt });
                          |nl()
                        """.stripMargin)
}
