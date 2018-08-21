package miniscala

import miniscala.{ SymbolicCMScalaTreeModule => S }
import miniscala.{ SymbolicCPSTreeModule => C }

object CMScalaToCPSTranslator extends (S.Tree => C.Tree) {
  def apply(tree: S.Tree): C.Tree = {
    nonTail(tree){_ =>
      val z = Symbol.fresh("c0")
      C.LetL(z, IntLit(0), C.Halt(z))
    }(Set.empty)
  }

  private def nonTail(tree: S.Tree)(ctx: Symbol=>C.Tree)(implicit mut: Set[Symbol]): C.Tree = {
    // @unchecked to avoid bogus compiler warnings

    (tree: @unchecked) match {
      case S.Let(name, _, value, body) =>
        nonTail(value)(v =>
            C.LetP(name, MiniScalaId, Seq(v), nonTail(body)(ctx)))

      // TODO: complete the following cases and add the missing ones.

      // Reference of an immutable variable
      case S.Ref(name) if !mut(name) =>
        ctx(name)

      // Reference of an mutable variable
      case S.Ref(name) if mut(name) =>
        val z = Symbol.fresh("z")
        val v = Symbol.fresh("v")
        C.LetL(z, CMScalaLiteral(0), 
        C.LetP(v, MiniScalaBlockGet, Seq(name, z), ctx(v)))

      // Mutable variable declaration
      case S.VarDec(n1, _, rhs, body) =>
        val s = Symbol.fresh("s")
        val z = Symbol.fresh("z")
        val d = Symbol.fresh("d")
        val lambda_v = (v : Symbol) => {
          C.LetP(d, MiniScalaBlockSet, Seq(n1, z, v),
            nonTail(body)(ctx)) }
        C.LetL(s, CMScalaLiteral(1),
        C.LetP(n1, MiniScalaBlockAlloc(242), Seq(s),
        C.LetL(z, CMScalaLiteral(0),
        nonTail(rhs)(lambda_v)(mut + n1))))

      // Mutable variable assign
      case S.VarAssign(n1, rhs) =>
        val z = Symbol.fresh("z") 
        val d = Symbol.fresh("d") 
        val lambda_v = (v : Symbol) => {
          C.LetP(d, MiniScalaBlockSet, Seq(n1, z, v), ctx(v)) }
        C.LetL(z, CMScalaLiteral(0),
        nonTail(rhs)(lambda_v))

      // MiniScala top level function declarations
      case S.LetRec(funs, body) =>
        val nfuns = funs map {
          case S.FunDef(name, _, alist, _, fbody) =>
            val c = Symbol.fresh("c")
            C.FunDef(name, c,
              alist map { case S.Arg(n, _,_) => n },
              tail(fbody, c)) }
        C.LetF(nfuns, nonTail(body)(ctx))
        
      // MiniScala While loop
      case S.While(e1, e2, e3) =>
        val c = Symbol.fresh("c")
        val ct = Symbol.fresh("ct")
        val d = Symbol.fresh("d")
        val loop = Symbol.fresh("loop")
        C.LetC(
          Seq(
            C.CntDef(loop, Seq(),
              C.LetC(Seq(
                C.CntDef( c, Seq(), nonTail(e3)(ctx)),
                C.CntDef(ct, Seq(), tail(e2, loop))),
              cond(e1,ct,c)))),
          C.LetL(d, CMScalaLiteral(()), ctx(d)))


  
      // MiniScala Literal
      case S.Lit(l) =>
        val n = Symbol.fresh("n")
        C.LetL(n, l, ctx(n))

      // MiniScala Primitives
      case S.Prim(op: MiniScalaValuePrimitive, args) =>
        val n = Symbol.fresh("n")
        nonTail_*(args)(as => C.LetP(n, op, as, ctx(n)))

      // MiniScala Primitives
      case S.Prim(op: MiniScalaTestPrimitive, args) =>
        nonTail(S.If(S.Prim(op, args),
          S.Lit(CMScalaLiteral(true)),
          S.Lit(CMScalaLiteral(false))))(ctx)
        
      // Miniscala If
      case S.If(e1, e2, e3) =>
        val c  = Symbol.fresh("c")
        val r  = Symbol.fresh("r")
        val ct = Symbol.fresh("ct")
        val cf = Symbol.fresh("cf")
        val f  = Symbol.fresh("f")
        C.LetC(
          Seq(
            C.CntDef(c, Seq(r), ctx(r)),
            C.CntDef(ct, Seq(), tail(e2, c)),
            C.CntDef(cf, Seq(), tail(e3, c))),
          C.LetL(f, CMScalaLiteral(false),
            cond(e1, ct, cf)))

      // Miniscala App
      case S.App(f, _, args) =>
        val c = Symbol.fresh("c")
        val r = Symbol.fresh("r")
        nonTail(f)( v =>
          nonTail_*(args)( arg => 
          C.LetC(Seq(C.CntDef(c, Seq(r), ctx(r))),
          C.AppF(v, c, arg))))


    }
  }


  private def nonTail_*(trees: Seq[S.Tree])(ctx: Seq[Symbol]=>C.Tree)(implicit mut: Set[Symbol]): C.Tree =
    trees match {
      case Seq() =>
        ctx(Seq())
      case t +: ts =>
        nonTail(t)(tSym => nonTail_*(ts)(tSyms => ctx(tSym +: tSyms)))
    }

  private def tail(tree: S.Tree, c: Symbol)(implicit mut: Set[Symbol]): C.Tree = {
    // @unchecked to avoid bogus compiler warnings
    (tree: @unchecked) match {

    case S.Let(name, _, value, body) =>
        nonTail(value)(v =>
          C.LetP(name, MiniScalaId, Seq(v), tail(body, c)))

    case S.LetRec(funs, body) =>
      val nfuns = funs map {
        case S.FunDef(name, _, alist, _, fbody) =>
          val c1 = Symbol.fresh("c")
            C.FunDef(name, c1,
              alist map { case S.Arg(n, _,_) => n },
              tail(fbody, c1)) }
        C.LetF(nfuns, nonTail(body)(v => C.AppC(c, Seq(v))))

      case S.Ref(name) if !mut(name) =>
        C.AppC(c, Seq(name))

      // Reference of an mutable variable
      case S.Ref(name) if mut(name) =>
        val z = Symbol.fresh("z")
        val v = Symbol.fresh("v")
        C.LetL(z, CMScalaLiteral(0), 
        C.LetP(v, MiniScalaBlockGet, Seq(name, z), C.AppC(c,Seq(v))))

      // Mutable variable declaration
      case S.VarDec(n1, _, rhs, body) =>
        val s = Symbol.fresh("s")
        val z = Symbol.fresh("z")
        val d = Symbol.fresh("d")
        val lambda_v = (v : Symbol) => {
          C.LetP(d, MiniScalaBlockSet, Seq(n1, z, v),
            nonTail(body)(v => C.AppC(c,Seq(v)))) }
        C.LetL(s, CMScalaLiteral(1),
        C.LetP(n1, MiniScalaBlockAlloc(242), Seq(s),
        C.LetL(z, CMScalaLiteral(0),
        nonTail(rhs)(lambda_v)(mut + n1))))

      // Mutable variable assign
      case S.VarAssign(n1, rhs) =>
        val z = Symbol.fresh("z") 
        val d = Symbol.fresh("d") 
        val lambda_v = (v : Symbol) => {
          C.LetP(d, MiniScalaBlockSet, Seq(n1, z, v), C.AppC(c,Seq(v))) }
        C.LetL(z, CMScalaLiteral(0),
        nonTail(rhs)(lambda_v))

      // MiniScala While loop
      case S.While(e1, e2, e3) =>
        val c1 = Symbol.fresh("c")
        val ct = Symbol.fresh("ct")
        val d = Symbol.fresh("d")
        val loop = Symbol.fresh("loop")
        C.LetC(
          Seq(
            C.CntDef(loop, Seq(),
              C.LetC(Seq(
                C.CntDef(c1, Seq(), nonTail(e3)(v => C.AppC(c,Seq(v)))),
                C.CntDef(ct, Seq(), tail(e2, loop))),
              cond(e1,ct,c1)))),
          C.LetL(d, CMScalaLiteral(()), C.AppC(loop, Seq(d))))
  
      // MiniScala Literal
      case S.Lit(l) =>
        val n = Symbol.fresh("n")
        C.LetL(n, l, C.AppC(c,Seq(n)))

      // MiniScala Primitives
      case S.Prim(op: MiniScalaValuePrimitive, args) =>
        val n = Symbol.fresh("n")
        nonTail_*(args)(as => C.LetP(n, op, as, C.AppC(c, Seq(n))))

      // MiniScala Primitives
      case S.Prim(op: MiniScalaTestPrimitive, args) =>
        nonTail(S.If(S.Prim(op, args),
          S.Lit(CMScalaLiteral(true)),
          S.Lit(CMScalaLiteral(false))))(v => C.AppC(c,Seq(v)))

      // Miniscala If
      case S.If(e1, e2, e3) =>
        val c1  = Symbol.fresh("c")
        val r  = Symbol.fresh("r")
        val ct = Symbol.fresh("ct")
        val cf = Symbol.fresh("cf")
        val f  = Symbol.fresh("f")
        C.LetC(
          Seq(
            C.CntDef(c1, Seq(r), C.AppC(c,Seq(r))),
            C.CntDef(ct, Seq(), tail(e2, c1)),
            C.CntDef(cf, Seq(), tail(e3, c1))),
          C.LetL(f, CMScalaLiteral(false),
            cond(e1, ct, cf)))

      // Miniscala App
      case S.App(f, _, args) =>
        val c1 = Symbol.fresh("c")
        val r = Symbol.fresh("r")
        nonTail(f)( v =>
          nonTail_*(args)( arg => 
          C.LetC(Seq(C.CntDef(c1, Seq(r), C.AppC(c,Seq(r)))),
          C.AppF(v, c1, arg))))

    }
  }

  private def cond(tree: S.Tree, trueC: Symbol, falseC: Symbol)(implicit mut: Set[Symbol]): C.Tree = {
    implicit val pos = tree.pos

    def litToCont(l: CMScalaLiteral): Symbol =
      if (l != BooleanLit(false)) trueC else falseC

    tree match {
      case S.If(condE, S.Lit(tl), S.Lit(fl)) =>
        cond(condE, litToCont(tl), litToCont(fl))

      case S.If(condE, S.Lit(tl), e3) =>
        cond(condE, litToCont(tl), falseC)

      case S.If(condE, e1, S.Lit(fl)) =>
        cond(condE, trueC, litToCont(fl))

      case S.Prim(p: MiniScalaTestPrimitive, args) =>
        nonTail_*(args)(as => C.If(p, as, trueC, falseC))

      case other =>
        nonTail(other)(o =>
          nonTail(S.Lit(BooleanLit(false)))(n =>
            C.If(MiniScalaNe, Seq(o, n), trueC, falseC)))
    }
  }

  private def tempLetC(cName: String, args: Seq[C.Name], cBody: C.Tree)
                      (body: C.Name=>C.Tree): C.Tree = {
    val cSym = Symbol.fresh(cName)
    C.LetC(Seq(C.CntDef(cSym, args, cBody)), body(cSym))
  }
}
