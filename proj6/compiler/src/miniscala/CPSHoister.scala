package miniscala

import SymbolicCPSTreeModuleLow._

object CPSHoister extends (Tree => Tree) {
  def apply(tree: Tree): Tree =
    hoist(tree)

  private def hoist(tree: Tree): LetF = tree match {
    case LetL(name, value, body) =>
      val LetF(funs, hBody) = hoist(body)
      LetF(funs, LetL(name, value, hBody))
    case LetP(name, prim, args, body) =>
      val LetF(funs, hBody) = hoist(body)
      LetF(funs, LetP(name, prim, args, hBody))
    case LetC(cnts, body) =>
      val (funsS, hCnts) = (cnts map hoistC).unzip
      val LetF(funs, hBody) = hoist(body)
      LetF(funsS.flatten ++ funs, LetC(hCnts, hBody))
    case LetF(funs, body) =>
      val funsH = funs flatMap hoistF
      val LetF(funs1, hBody) = hoist(body)
      LetF(funsH ++ funs1, hBody)
    case other @ (AppC(_, _) | AppF(_, _, _) | If(_, _, _, _) | Halt(_)) =>
      LetF(Seq(), other)
  }

  private def hoistC(cnt: CntDef): (Seq[FunDef], CntDef) = {
    val LetF(funs, hBody) = hoist(cnt.body)
    (funs, CntDef(cnt.name, cnt.args, hBody))
  }

  private def hoistF(fun: FunDef): Seq[FunDef] = {
    val LetF(funs, hBody) = hoist(fun.body)
    FunDef(fun.name, fun.retC, fun.args, hBody) +: funs
  }
}
