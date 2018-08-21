package miniscala

import prettyprint.Document

class CPSTreeFormatter[T <: CPSTreeModule](treeModule: T)
    extends Formatter[T#Tree] {
  import treeModule._
  import Formatter._

  def toDocument(tree: T#Tree): Document = {

    def cntDefToDoc(c: CntDef): Document = {
      val argsDoc = seqToDoc(c.args, anyToDoc)
      anyToDoc(s"defc ${c.name}(")::argsDoc::anyToDoc(") = ")::paren(toDocument(c.body))
    }

    def funDefToDoc(f: FunDef): Document = {
      val argsDoc = seqToDoc(f.retC +: f.args, anyToDoc)
      anyToDoc(s"deff ${f.name}(")::argsDoc::anyToDoc(") = ")::paren(toDocument(f.body))
    }

    def primToDoc(op: Any, args: Seq[Name]) = args match {
      case Nil      => anyToDoc(op)::anyToDoc("()")
      case List(e1) if op.toString.length == 1 => anyToDoc(s"$op$e1")
      case List(e1) => anyToDoc(s"$op($e1)")
      case List(e1, e2) if op != MiniScalaBlockGet  => anyToDoc(s"$e1 $op $e2")
      case List(e1, e2) => anyToDoc(s"$op($e1, $e2)")
      case List(e1, e2, e3) => anyToDoc(s"$op($e1, $e2, $e3)")
    }

    (tree: @unchecked) match {
      case LetL(name, rhs, body) =>
        anyToDoc(s"vall $name = $rhs;"):/:toDocument(body)
      case LetP(name, op, args, body) =>
        anyToDoc(s"valp $name = ")::primToDoc(op, args)::anyToDoc(";"):/:toDocument(body)
      case LetC(c, body) =>
        foldDoc(c map(cntDefToDoc(_))):/: toDocument(body)
      case LetF(f, body) =>
        foldDoc(f map(funDefToDoc(_))):/: toDocument(body)
      case AppF(fun, retC, args) =>
        anyToDoc(s"$fun(")::seqToDoc(retC +: args, anyToDoc)::anyToDoc(")")
      case AppC(cont, args) =>
        anyToDoc(s"$cont(")::seqToDoc(args, anyToDoc)::anyToDoc(")")
      case If(p, args, thenC, elseC) =>
        anyToDoc("if (")::primToDoc(p, args)::anyToDoc(s") $thenC else $elseC")
      case Halt(arg) =>
        anyToDoc(arg)
    }
  }
}

object CPSTreeFormatter {
  implicit object SymbolicCPSTreeFormatter
      extends CPSTreeFormatter(SymbolicCPSTreeModule)
}
