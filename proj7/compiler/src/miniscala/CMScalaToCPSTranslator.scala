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

      case S.LetRec(functions, body) =>
        val funDefs = functions map { f =>
          val rc = Symbol.fresh("rc")
          C.FunDef(f.name, rc, f.args map(_.name), tail(f.body, rc))
        }
        C.LetF(funDefs, nonTail(body)(ctx))

      case S.If(condE, thenE, elseE) =>
        val v = Symbol.fresh("v")
        tempLetC("ic", Seq(v), ctx(v))(ic =>
          tempLetC("tc", Seq(), tail(thenE, ic))(tc =>
            tempLetC("fc", Seq(), tail(elseE, ic))(fc =>
              cond(condE, tc, fc))))

      case S.While(condE, lbodyE, bodyE) =>
        val d1 = Symbol.fresh("d")
        val d2 = Symbol.fresh("d")
        val loop = Symbol.fresh("loop")
        val f = Symbol.fresh("f")
        C.LetC(Seq(C.CntDef(loop, Seq(d1),
          tempLetC("c", Seq(), nonTail(bodyE)(ctx))(c =>
            tempLetC("ct", Seq(), tail(lbodyE, loop))(ct =>
              cond(condE, ct, c))))),
          C.LetL(d2, UnitLit,
            C.AppC(loop, Seq(d2))))

      case S.App(fun, _, args) =>
        val r = Symbol.fresh("r")
        nonTail(fun)(f =>
          nonTail_*(args)(as =>
            tempLetC("rc", Seq(r), ctx(r))(rc => C.AppF(f, rc, as))))

      case t @ S.Prim(prim: MiniScalaTestPrimitive, _) =>
        nonTail(S.If(t, S.Lit(BooleanLit(true)), S.Lit(BooleanLit(false))))(ctx)

      case S.Prim(prim: MiniScalaValuePrimitive, args) =>
        val v = Symbol.fresh("v")
        nonTail_*(args)(as => C.LetP(v, prim, as, ctx(v)))

      case S.Halt(arg) =>
        nonTail(arg)(C.Halt(_))

      case S.Ref(name) if !mut(name) =>
        ctx(name)

      case S.VarDec(name, _, value, body) =>
        val s = Symbol.fresh("s")
        val z = Symbol.fresh("z")
        val d = Symbol.fresh("d")
        C.LetL(s, IntLit(1),
          C.LetP(name, MiniScalaBlockAlloc(BlockTag.Variable.id), Seq(s),
            C.LetL(z, IntLit(0),
              nonTail(value)(v =>
                C.LetP(d, MiniScalaBlockSet, Seq(name, z, v), nonTail(body)(ctx)(mut + name))))))

      case S.VarAssign(name, value) =>
        val z = Symbol.fresh("z")
        val d = Symbol.fresh("d")
        C.LetL(z, IntLit(0),
          nonTail(value)(v =>
            C.LetP(d, MiniScalaBlockSet, Seq(name, z, v), ctx(v))))

      case S.Ref(name) => // if mut(name) =>
        val z = Symbol.fresh("z")
        val v = Symbol.fresh("v")
        C.LetL(z, IntLit(0),
          C.LetP(v, MiniScalaBlockGet, Seq(name, z),
            ctx(v)))

      case S.Lit(value) =>
        val i = Symbol.fresh("i")
        C.LetL(i, value, ctx(i))
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

      case S.LetRec(functions, body) =>
        val funDefs = functions map { f =>
          val rc = Symbol.fresh("rc")
          C.FunDef(f.name, rc, f.args map(_.name), tail(f.body, rc))
        }
        C.LetF(funDefs, tail(body, c))

      case S.If(condE, thenE, elseE) =>
        tempLetC("tc", Seq(), tail(thenE, c))(tc =>
          tempLetC("fc", Seq(), tail(elseE, c))(fc =>
            cond(condE, tc, fc)))

      case S.While(condE, lbodyE, bodyE) =>
        val d1 = Symbol.fresh("d")
        val d2 = Symbol.fresh("d")
        val loop = Symbol.fresh("loop")
        val f = Symbol.fresh("f")
        C.LetC(Seq(C.CntDef(loop, Seq(d1),
          tempLetC("c", Seq(), tail(bodyE, c))(cc =>
            tempLetC("ct", Seq(), tail(lbodyE, loop))(ct =>
              cond(condE, ct, cc))))),
          C.LetL(d2, UnitLit,
            C.AppC(loop, Seq(d2))))

      case S.App(fun, _, args) =>
        nonTail(fun)(f => nonTail_*(args)(as => C.AppF(f, c, as)))

      case t @ S.Prim(prim: MiniScalaTestPrimitive, _) =>
        tail(S.If(t, S.Lit(BooleanLit(true)), S.Lit(BooleanLit(false))), c)

      case S.Prim(prim: MiniScalaValuePrimitive, args) =>
        val v = Symbol.fresh("v")
        nonTail_*(args)(as => C.LetP(v, prim, as, C.AppC(c, Seq(v))))

      case S.Halt(arg) =>
        nonTail(arg)(C.Halt(_))

      case S.Ref(name) if !mut(name) =>
        C.AppC(c, Seq(name))

      case S.VarDec(name, _, value, body) =>
        val s = Symbol.fresh("s")
        val z = Symbol.fresh("z")
        val d = Symbol.fresh("d")
        C.LetL(s, IntLit(1),
          C.LetP(name, MiniScalaBlockAlloc(BlockTag.Variable.id), Seq(s),
            C.LetL(z, IntLit(0),
              nonTail(value)(v =>
                C.LetP(d, MiniScalaBlockSet, Seq(name, z, v), tail(body, c)(mut + name))))))

      case S.VarAssign(name, value) =>
        val z = Symbol.fresh("z")
        val d = Symbol.fresh("d")
        C.LetL(z, IntLit(0),
          nonTail(value)(v =>
            C.LetP(d, MiniScalaBlockSet, Seq(name, z, v), C.AppC(c, Seq(v)))))

      case S.Ref(name) => // if mut(name) =>
        val z = Symbol.fresh("z")
        val v = Symbol.fresh("v")
        C.LetL(z, IntLit(0),
          C.LetP(v, MiniScalaBlockGet, Seq(name, z),
            C.AppC(c, Seq(v))))

      case S.Lit(value) =>
        val i = Symbol.fresh("i")
        C.LetL(i, value, C.AppC(c, Seq(i)))
    }
  }

  private def cond(tree: S.Tree, trueC: Symbol, falseC: Symbol)(implicit mut: Set[Symbol]): C.Tree = {
    implicit val pos = tree.pos

    def litToCont(l: CMScalaLiteral): Symbol =
      if (l != BooleanLit(false)) trueC else falseC

    tree match {
      case S.If(condE, S.Lit(tl), S.Lit(fl)) =>
        cond(condE, litToCont(tl), litToCont(fl))

      case S.If(condE, thenE, S.Lit(l)) =>
        tempLetC("tc", Seq(), cond(thenE, trueC, falseC))(tc =>
          cond(condE, tc, litToCont(l)))

      case S.If(condE, S.Lit(l), elseE) =>
        tempLetC("ec", Seq(), cond(elseE, trueC, falseC))(ec =>
          cond(condE, litToCont(l), ec))

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
