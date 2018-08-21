package miniscala

import NominalCMScalaTreeModule._
import CMScalaType._

// Class used to carry position information within the source code
case class Pos(gapLine: Int, gapCol: Int, startLine: Int, startCol: Int, endLine: Int, endCol: Int) {
  override def toString = "pos"
}

object Tokens {

  abstract class Token {
    var pos: Pos = _
  }
  case object EOF extends Token

  // CHANGED: As we added new types, instead of having a Token call Number,
  // we have a Token called Literal for all constant values.
  case class Literal(x: Any) extends Token
  case class Ident(x: String) extends Token
  case class Keyword(x: String) extends Token
  case class Primitive(x: String) extends Token
  case class Delim(x: Char) extends Token
}


// Scanner
class Scanner(in: Reader[Char], idxToPos: Int => (String, Int)) extends Reader[Tokens.Token] with MiniScalaReporter {
  import Tokens._

  // Pos handling
  def pos = in.pos
  def input = in.input

  // Current line in the file
  var line = 0

  // lineStarts(i) contains the offset of the i th line within the file
  val lineStarts = scala.collection.mutable.ArrayBuffer(0)

  // Current column in the file
  def column = pos - lineStarts(line)

  // Extract the i th line of code.
  def getLine(i: Int) = {
    val start = lineStarts(i)
    val end = input.indexOf('\n', start)

    if (end < 0)
      input.substring(start)
    else
      input.substring(start, end)
  }

  // Information for the current Pos
  var gapLine = 0;
  var gapCol = 0;
  var startLine = 0;
  var startCol = 0;
  var endLine = 0;
  var endCol = 0;

  override def abort(msg: String) = {
    abort(msg, showSource(getCurrentPos()))
  }

  /*
   * Show the line of code and highlight the token at position p
   */
  def showSource(p: Pos) = {
    val width = if (p.endLine == p.startLine) (p.endCol - p.startCol) else 0

    val (file, rLine) = idxToPos(p.startLine)
    val header = s"${file.split("/").last}:${rLine + 1}:${p.startCol + 1}: "
    val line1 = getLine(p.startLine)
    val line2 = " "*(p.startCol+header.length) + "^"*(width max 1)
    header + line1 + '\n' + line2
  }

  def isAlpha(c: Char) =
    ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z') || c == '_'

  def isDigit(c: Char) = '0' <= c && c <= '9'
  def isHexDigit(c: Char) = 'a' <= c && c <= 'f' || 'A' <= c && c <= 'F'|| isDigit(c)

  def isAlphaNum(c: Char) = isAlpha(c) || isDigit(c)

  def isCommentStart(c1: Char, c2: Char) = c1 == '/' && c2 == '/'

  val isWhiteSpace = Set(' ','\t','\n','\r')

  // Boolean operators start with one of the following characters
  val isBOperator  = Set('<', '>', '!', '=')

  //  Operators start with one of the following characters
  val isOperator   = Set('+','-','*','/', '%', '&', '|', '^') ++ isBOperator

  // List of delimiters
  val isDelim      = Set('(',')','=',';','{','}',':',',','[',']','.')

  // List of keywords
  val isKeyword    = Set("if", "else", "val", "var", "while", "def", "=>", "new","Nil")

  val isBoolean = Set("true", "false")

  val prim = Map("getchar" -> "byte-read", "putchar" -> "byte-write")

  /*
   * Extract a name from the stream
   */
  def getName() = {
    val buf = new StringBuilder
    while (in.hasNext(isAlphaNum)) {
      buf += in.next()
    }
    val s = buf.toString
    if (isKeyword(s)) Keyword(s)
    else if (isBoolean(s)) Literal(s == "true")
    else if (prim.isDefinedAt(s)) Primitive(prim(s))
    else Ident(s)
  }

  /*
   * Extract an operator from the stream
   */
  def getOperator() = {
    val buf = new StringBuilder
    do {
      buf += in.next()
    } while (in.hasNext(isOperator))
    val s = buf.toString
    // "=" is a delimiter, "=>" is a keyword, "==","=+", etc are operators
    if (s == "=") Delim('=')
    else if (isKeyword(s)) Keyword(s)
    else Ident(s)
  }

  /*
   * Extract a number from the stream and return it.
   * Raise an error if there is overflow.
   *
   * NOTE: An integer can be between 0 and (2 to the power 31) minus 1
   */
  def getNum() = (in.peek, in.peek1) match {
    case ('0', 'x') =>
      in.next; in.next;
      if (!in.hasNext(isHexDigit)) abort("missing integer number")

      val num = new StringBuilder
      while (in.hasNext(isDigit)) {
        num += in.next()
      }
      val sNum = num.toString
      if (sNum.length < 8 || (sNum.length == 8 && sNum.charAt(0) <= '3'))
        Literal(Integer.parseInt(sNum, 16))
      else
        abort(s"integer overflow")
    case _ =>
      val MAX_NUM = s"${(1 << 30) - 1}"
      val num = new StringBuilder
      while (in.hasNext(isDigit)) {
        num += in.next()
      }
      val sNum = num.toString
      if (sNum.length < MAX_NUM.length || (sNum.length == MAX_NUM.length && sNum <= MAX_NUM))
        Literal(sNum.toInt)
      else
        abort(s"integer overflow")
  }

  def getEscape = {
    in.next match {
      case '\\' => '\\'
      case 'n' => '\n'
      case 'r' => '\r'
      case 't' => '\t'
      case '\'' => '\''
      case '\"' => '\"'
      case c => abort(s"TODO escape: $c")
    }
  }

  def getChar() = {
    in.next
    var c = in.next
    if (c == '\\')
      c = getEscape

    if (in.next != '\'') expected("'")
    Literal(c)
  }

  def getString() = {
    in.next
    val s = new StringBuilder
    while (in.peek != '\"') {
      val c = in.next
      if (c == '\\')
        s += getEscape
      else
        s += c
    }
    in.next
    Literal(s.toString)
  }

  /*
   * Extract a raw token from the stream.
   * i.e. without position information.
   */
  def getRawToken(): Token = {
    if (in.hasNext(isAlpha)) {
      getName()
    } else if (in.hasNext(isOperator)) {
      getOperator()
    } else if (in.hasNext(isDigit)) {
      getNum()
    } else if (in.peek == ''') {
      getChar()
    } else if (in.peek == '"') {
      getString()
    } else if (in.hasNext(isDelim)) {
      in.next match {
        case ':' =>
          if (in.peek == ':') {
            in.next
            Keyword("::")
          } else
            Delim(':')
        case d => Delim(d)
      }
    } else if (!in.hasNext) {
      EOF
    } else {
      abort(s"unexpected character")
    }
  }

  /*
   * Skip whitespace and comments. Stop at the next token.
   */
  def skipWhiteSpace() = {
    while (in.hasNext(isWhiteSpace) || in.hasNext2(isCommentStart)) {

      // If it is a comment, consume the full line
      if (in.peek == '/') {
        in.next()
        while (in.peek != '\n') in.next()

      }

      // Update file statistics if new line
      if (in.peek == '\n') {
        lineStarts += pos + 1
        line += 1
      }
      in.next()
    }
  }

  def getCurrentPos() = {
    endLine = line; endCol = column
    Pos(gapLine,gapCol,startLine,startCol,endLine,endCol)
  }

  /*
   * Extract a token and set position information
   */
  def getToken(): Token = {
    gapLine = line; gapCol = column
    skipWhiteSpace()
    startLine = line; startCol = column
    val tok = getRawToken()
    tok.pos = getCurrentPos()

    tok
  }

  var peek  = getToken()
  var peek1 = getToken()
  var peek2 = getToken()
  def hasNext: Boolean = peek != EOF
  def hasNext(f: Token => Boolean) = f(peek)
  def hasNext2(f: (Token, Token) => Boolean) = f(peek, peek1)
  def next() = {
    val res = peek
    peek = peek1
    peek1 = peek2
    peek2 = getToken()
    res
  }
}

class Parser(in: Scanner) extends MiniScalaReporter {
  import Tokens._

  /*
   * Overloaded methods that show the source code
   * and highlight the current token when reporting
   * an error.
   */
  override def expected(msg: String) = {
    expected(msg, in.showSource(in.peek.pos))
  }

  override def abort(msg: String) = {
    abort(msg, in.showSource(in.peek.pos))
  }

  def expected(msg: String, pos: Pos): Nothing =
    expected(msg, in.showSource(pos))

  def error(msg: String, pos: Pos): Unit =
    error(msg, in.showSource(pos))

  def warn(msg: String, pos: Pos): Unit =
    warn(msg, in.showSource(pos))

  def accept(c: Char): Token = {
    if (in.hasNext(_ == Delim(c))) in.next()
    else {
      val Pos(gapLine, gapCol, startLine, startCol, endLine, endCol) = in.peek.pos
      if (gapLine < startLine)
        expected(s"'$c'", Pos(gapLine, gapCol, gapLine, gapCol, gapLine, gapCol+1))
      else
        expected(s"'$c'")
    }
  }

  def accept(s: String) = {
    if (in.hasNext(_ == Keyword(s))) in.next()
    else expected(s"'$s'")
  }

  /*
   * Auxilaries functions
   * Test and extract data
   */
  def isName(x: Token) = x match {
    case Ident(x) => true
    case _ => false
  }

  def getName(): (String, Pos) = {
    if (!in.hasNext(isName)) expected("Name")
    val pos = in.peek.pos
    val Ident(x) = in.next()
    (x, pos)
  }

  // CHANGED: It was only Number previsously
  def isLiteral(x: Token) = x match {
    case Literal(x) => true
    case _ => false
  }

  def getLiteral(): (Any, Pos) = {
    if (!in.hasNext(isLiteral)) expected("Literal")
    val pos = in.peek.pos
    val Literal(x) = in.next()
    (x, pos)
  }

  def getOperator(): (String, Pos) = {
    if (!in.hasNext(isName)) expected("Operator")
    val pos = in.peek.pos
    val Ident(x) = in.next()
    (x, pos)
  }

  /*
   * Test if the following token is an infix
   * operator with highest precedence
   */
  def isInfixOp(min: Int)(x: Token) = x match {
    case Ident(x) => prec(x) >= min
    case _ => false
  }

  /*
   * Test if the following token is an operator.
   */
  def isOperator(x: Token) = x match {
    case Ident(x) => in.isOperator(x.charAt(0))
    case _ => false
  }

  /*
   * Define precedence of operator.
   * Negative precedence means that the operator can
   * not be used as an infix operator within a simple expression.
   *
   * CHANGED: boolean operators have precedence of 0
   */
  def prec(a: String) = a.charAt(0) match { // higher bind tighter
    case '|' => 1
    case '^' => 2
    case '&' => 3
    case '=' | '!' => 4
    case '<' | '>' => 5
    case '+' | '-' => 6
    case '*' | '/' | '%' => 7
    case _ => 0
  }

  def assoc(a: String) = a match {
    case _    => 1
  }
}



/*
 * The BaseParser class implements all of the functionality implemented in project 2,
 * with the addition of type information.
 *
 * To avoid repeating your effort from project 2, we have implemented all of the
 * parsing for you, excluding the parsing of types. As such...
 *
 * <type>   ::= <ident>
 *            | <type> '=>' <type>
 *            | '('[<type>[','<type>]*]')' '=>' <type>
 * <op>     ::= ['*' | '/' | '+' | '-' | '<' | '>' | '=' | '!']+
 * <bool>   ::= 'true' | 'false'
 * <atom>   ::= <number> | <bool> | '()'
 *            | '('<simp>')'
 *            | <ident>
 * <tight>  ::= <atom>['('[<simp>[','<simp>]*]')']*
 *            | '{'<exp>'}'
 * <utight> ::= [<op>]<tight>
 * <simp>   ::= <utight>[<op><utight>]*
 *            | 'if' '('<simp>')' <simp> ['else' <simp>]
 *            |  <ident> '=' <simp>
 * <exp>    ::= <simp>[;<exp>]
 *            | 'val' <ident> [':'<ident>] '=' <simp>';' <exp>
 *            | 'var' <ident> [':'<ident>] '=' <simp>';' <exp>
 *            | 'while' '('<simp>')'<simp>';' <exp>
 * <arg>    ::= <ident>':'<type>
 * <prog>   ::= ['def'<ident>'('[<arg>[','<arg>]*]')'[':' <type>] '=' <simp>';']*<exp>
 */
class MiniScalaParser(in: Scanner) extends Parser(in) {
  import Tokens._

  var next = 0
  def freshName(suf: String = "x") = {
    next += 1
    suf + "$" + next
  }

  /*
   * This function is an auxilary function that is parsing a list of elements of type T which are
   * separated by 'sep'.
   *
   * 'sep' must be a valid delimiter.
   *
   * 12, 14, 11, 23, 10, 234
   *
   * parseList[Exp](parseAtom, ',', tok => tok match {
   *    case Literal(x: Int) => x < 20;
   *    case _ => false
   *  })
   *
   *  will return the list List(Lit(12), Lit(14), lit(11)) and the next token will be Delim(',')
   *
   *  You don't have to use this function but it may be useful.
   */
  def parseList[T](parseElem: => T, sep: Char, cond: Token => Boolean, first: Boolean = true): List[T] = {
    if (first && cond(in.peek) || (!first && in.peek == Delim(sep) && cond(in.peek1))) {
      if (!first) {
        accept(sep)
      }
      parseElem :: parseList(parseElem, sep, cond, false)
    } else {
      Nil
    }
  }


  /******************* Types **********************/

  /*
   * This function extracts the type information from
   * the source code. Raise an error if there is no
   * type information.
   *
   *  This function will only be used to read in a type
   * (i.e. you should not read in a delimiter)
   */
  def parseType: Type = {
    val lhs = in.peek match {
      case Ident("Array") =>
        in.next
        accept('[')
        val tp = parseType
        accept(']')
        ArrayType(tp)
      case Ident("List") =>
        in.next
        accept('[')
        val tp = parseType
        accept(']')
        ListType(tp)
      case Ident("String") =>
        in.next
        StringType
      case Ident(tp) =>
        in.next
        BaseType(tp)
      case Delim('(') =>
        in.next()
        val args = parseList[Type](parseType, ',', tok => tok != Delim(')'))
        accept(')')
        if (args.length == 2 && in.peek != Keyword("=>")) {
          PairType(args(0), args(1))
        } else {
          accept("=>")
          val rte = parseType
          FunType(args map { arg => ("", arg) }, rte)
        }
      case _ => expected("type")
    }
    if (in.peek == Keyword("=>")) {
      in.next()
      FunType(List(("", lhs)), parseType)
    } else {
      lhs
    }
  }


  /*
   * This function is parsing a type which can be omitted.
   * If the type information is not in the source code,
   * it returns UnknownType
   */
  def parseOptionalType: Type = in.peek match {
    case Delim(':') =>
      accept(':')
      parseType
    case _ => UnknownType
  }

  /******************* Code  **********************/

  /*
   * Parse the program and verify that there nothing left
   * to be parsed.
   */
  def parseCode: Tree = {
    val prog = parseExpression
    if (in.hasNext)
      expected(s"EOF")
    prog
  }


  def parseAtom: Tree = (in.peek, in.peek1) match {
    case (Literal(s: String), _) =>
      val (_, pos) = getLiteral
      val name = freshName("str")
      Let(name, StringType, PrimAlloc(StringType, List(Lit(IntLit(s.length)))).withPos(pos),
        (s.zipWithIndex :\ (Ref(name).withPos(pos): Tree)) {
          case ((c, idx), body) => Let(freshName(), UnitType, Prim("block-set", List(Ref(name).withPos(pos), Lit(IntLit(idx)).withPos(pos), Lit(CharLit(c)).withPos(pos))).withPos(pos), body)
        }).withPos(pos)
    case (Literal(x), _) =>
      val (_, pos) = getLiteral
      Lit(CMScalaLiteral(x)).withPos(pos)
    case (Delim('('), Delim(')')) =>
      val pos = in.next().pos
      in.next
      Lit(UnitLit).withPos(pos)
    case (Delim('('), _) =>
      val pos = in.next().pos
      val t1 = parseSimpleExpression
      in.peek match {
        case Delim(',') =>
          accept(',')
          val t2 = parseSimpleExpression
          accept(')')
          PairDec(t1, t2).withPos(pos)
        case _ =>
          accept(')')
          t1
      }
    case (Primitive(name), _) =>
      val pos = in.next.pos
      accept('(')
      val args = parseList[Tree](parseSimpleExpression, ',', tok => tok != Delim(')'))
      accept(')')
      Prim(name, args).withPos(pos)
    case (Ident(x), _) =>
      val (_, pos) = getName
      Ref(x).withPos(pos)
    case (Delim('{'), _) =>
      accept('{')
      val res = parseExpression
      accept('}')
      res
    case (Keyword("Nil"), _) =>
      val pos = in.next.pos
      val t = in.peek match {
        case Delim('[') =>
          accept('[')
          val t = parseType
          accept(']')
          t
        case _ =>
          UnknownType
      }
      PrimAlloc(ListType(t), Nil).withPos(pos)
    case _ => abort(s"Illegal start of simple expression")
  }

  /*
   * Parse <tight> grammar. i.e. function applications.
   *
   * Remember function application is left associative
   * and they all have the same precedence.
   *
   * a(i)(k, j) is parsed to
   *
   * App(App(Ref("a"), Ref("i")), List(Ref("k"), Ref("j")))
   */
  def set(x: Char*) = Set[Token](x map(Delim(_)): _*)
  def isRef(x: Tree) = x match {
    case Ref(_) => true
    case _ => false
  }

  def parseTight = {
    // Parse a tight
    val res = in.peek match {
      case Delim('{') =>
        val pos = in.next().pos
        val res = parseExpression
        accept('}')
        res
      case  _ =>
        var res = parseAtom
        var tps: List[Type] = null
        while (in.hasNext(set('(', '.','[')) || in.peek == Keyword("::")) {
          in.peek match {
            case Delim('[') if isRef(res) =>
              in.next
              tps = parseList[Type](parseType, ',', tok => tok != Delim(']'))
              accept(']')
            case Delim('[') =>
              expected(";")
            case Delim('(') =>
              val pos = in.next.pos
              val args = parseList[Tree](parseSimpleExpression, ',', tok => tok != Delim(')'))
              accept(')')
              res = App(res, if (tps == null) Nil else tps, args).withPos(pos)
              tps = null
            case Delim('.') =>
              in.next
              val (name, pos) = getName
              res = Select(res, name).withPos(pos)
            case Keyword("::") =>
              val pos = in.next.pos
              val tail = parseSimpleExpression
              res = PrimAlloc(ListType(UnknownType), List(res, tail)).withPos(pos)
          }
        }
        if (tps != null)
          expected("(")
        res
    }

    // Check for array assigement
    (res, in.peek) match {
      case (App(arr, _, args), Delim('=')) if args.length == 1 =>
        val pos = in.next.pos
        val rhs = parseSimpleExpression
        Prim("block-set", arr :: args ++ List(rhs)).withPos(pos)
      case _ => res
    }
  }

  def parseUTight = if (in.hasNext(isOperator)) {
    val (op, pos) = getOperator
    Prim(op, List(parseTight)).withPos(pos)
  } else {
    parseTight
  }

  def parseSimpleExpression(min: Int): Tree = {
    var res = parseUTight
    while (in.hasNext(isInfixOp(min))) {
      val (op, pos) = getOperator
      val nMin = prec(op) + assoc(op)
      val rhs = parseSimpleExpression(nMin)
      res = Prim(op, List(res, rhs)).withPos(pos)
    }
    res
  }

  def parseSimpleExpression: Tree = (in.peek, in.peek1, in.peek2) match {
    case (Ident(x), Delim('='), _) =>
      val (_, pos) = getName
      accept('=')
      val rhs = parseSimpleExpression
      VarAssign(x, rhs).withPos(pos)
    case (Keyword("if"), _, _) =>
      val pos = accept("if").pos
      accept('(')
      val cond = parseSimpleExpression
      accept(')')
      val tBranch = parseSimpleExpression
      val eBranch = if (in.peek == Keyword("else")) {
        accept("else")
        parseSimpleExpression
      } else {
        Lit(UnitLit).withPos(pos)
      }
      If(cond, tBranch, eBranch).withPos(pos)
    case (Delim('('), Ident(_), Delim(':')) => // anonymous functions
      accept('(')
      val args = parseList[Arg](parseArg, ',', tok => tok != Delim(')'))
      accept(')')
      val pos = accept("=>").pos
      val body = parseSimpleExpression
      val fname = freshName("fun")
      LetRec(List(FunDef(fname, Nil, args, UnknownType, body).withPos(pos)), Ref(fname).withPos(pos)).withPos(pos)
    case (Keyword("new"), _, _) =>
      val pos = in.next.pos
      val t = parseType
      accept('(')
      val args = parseList[Tree](parseSimpleExpression, ',', tok => tok != Delim(')'))
      accept(')')
      PrimAlloc(t, args).withPos(pos)
    case _ => parseSimpleExpression(0)
  }

  /*
   * Parse one argument (<arg>)
   */
  def parseArg: Arg = {
    val (name, pos) = getName
    accept(':')
    Arg(name, parseType, pos)
  }

  def parseIdent = in.peek match {
    case Ident(x) => in.next; x
    case _ => expected("identifier")
  }
  /*
   * Parse one function.
   * We assume that the first token is Keyword("def")
   */
  def parseFunction: FunDef = {
    accept("def")
    val (fname, pos) = getName
    val ptps = if (in.peek == Delim('[')) {
      in.next
      val ptps = parseList[String](parseIdent, ',', tok => tok != Delim(']'))
      accept(']')
      ptps
    } else {
      Nil
    }
    accept('(')
    val args = parseList[Arg](parseArg, ',', tok => tok != Delim(')'))
    accept(')')
    val rtp = parseOptionalType
    accept('=')
    val body = parseSimpleExpression
    FunDef(fname, ptps, args, rtp, body).withPos(pos)
  }

  def parseExpression: Tree = in.peek match {
    case Keyword("val") =>
      accept("val")
      val (name, pos) = getName
      val tp = parseOptionalType
      accept('=')
      val rhs = parseSimpleExpression
      accept(';')
      val body = parseExpression
      Let(name, tp, rhs, body).withPos(pos)
    case Keyword("var") =>
      accept("var")
      val (name, pos) = getName
      val tp = parseOptionalType
      accept('=')
      val rhs = parseSimpleExpression
      accept(';')
      val body = parseExpression
      VarDec(name, tp, rhs, body).withPos(pos)
    case Keyword("while") =>
      val pos = accept("while").pos
      accept('(')
      val cond = parseSimpleExpression
      accept(')')
      val lBody = parseSimpleExpression
      accept(';')
      val body = parseExpression
      While(cond, lBody, body).withPos(pos)
    case Keyword("def") =>
      val pos = in.peek.pos
      val funs = parseList[FunDef](parseFunction, ';', tok => tok == Keyword("def"))
      accept(';')
      val body = parseExpression
      LetRec(funs, body).withPos(pos)
    case _ =>
      val res = parseSimpleExpression
      if (in.hasNext(isNewLine)) {
        val pos = accept(';').pos
        Let(freshName(), UnknownType, res, parseExpression).withPos(pos)
      } else {
        res
      }
  }

  // Can be overriden for ; inference
  def isNewLine(x: Token) = x match {
    case Delim(';') => true
    case _ => false
  }

}

/*
 * We are now going to add heap storage. This kind of storage is persistant
 * between function calls.
 *
 * We are going to use the scala syntax of: new Array[Int](4). However
 * we are not going to implement object. The array behavior will be closer
 * to a C array.
 *
 * In order to access an element the element in the array we use the syntax:
 *
 * val arr = new Array[Int](4);
 * val x = arr(0);
 *
 * And for the update:
 *
 * arr(0) = 3;
 *
 * The acces is going to be parse as a function application but this is fine.
 * For the value update, the parser need to generate a primitive: block-set
 * which take three paramter. 1 the arr, 2 the idx and 3 the value to update.
 *
 * arr(0) = 3;
 *
 * will be parsed to
 * Prim("block-set", List(Ref("arr"), Lit(0), Lit(3)))
 *
 * One idea to parse it it to follow the following process:
 *
 * parse a tight, if it returns a function application with only one argument
 * and the following token is an '=' then you are in the array update situation.
 *
 *
 * <type>   ::= <ident>
 *            | <type> '=>' <type>
 *            | '('[<type>[','<type>]*]')' '=>' <type>
 * <op>     ::= ['*' | '/' | '+' | '-' | '<' | '>' | '=' | '!']+
 * <bool>   ::= 'true' | 'false'
 * <atom>   ::= <number> | <bool> | '()'
 *            | '('<simp>')'
 *            | <ident>
 * <tight>  ::= <atom>['('[<simp>[','<simp>]*]')']*['('<simp>')' '=' <simp>]
 *            | '{'<exp>'}'
 * <utight> ::= [<op>]<tight>
 * <simp>   ::= <utight>[<op><utight>]*
 *            | 'if' '('<simp>')' <simp> ['else' <simp>]
 *            |  <ident> '=' <simp>
 *            | 'new' 'Array' '['<type> ']' '('<simpl>')' // type not optional '[' is the delimiter.
 * <exp>    ::= <simp>[;<exp>]
 *            | 'val' <ident> [':'<ident>] '=' <simp>';' <exp>
 *            | 'var' <ident> [':'<ident>] '=' <simp>';' <exp>
 *            | 'while' '('<simp>')'<simp>';' <exp>
 * <arg>    ::= <ident>':'<type>
 * <prog>   ::= ['def'<ident>'('[<arg>[','<arg>]*]')'[':' <type>] '=' <simp>';']*<exp>
 */
