package miniscala

import BitTwiddling.bitsToIntMSBF
import miniscala.{ SymbolicCPSTreeModule => H }
import miniscala.{ SymbolicCPSTreeModuleLow => L }

/**
 * Value-representation phase for the CPS language. Translates a tree
 * with high-level values (blocks, integers, booleans, unit) and
 * corresponding primitives to one with low-level values (blocks
 * and integers only) and corresponding primitives.
 *
 * @author Michel Schinz <Michel.Schinz@epfl.ch>
 */

object CPSValueRepresenter extends (H.Tree => L.Tree) {
  def apply(tree: H.Tree): L.Tree =
    transform(tree)(Map.empty)

  val unitLit = bitsToIntMSBF(0, 0, 1, 0)
  val optimized = true

  private def transform(tree: H.Tree)
                       (implicit worker: Map[Symbol, (Symbol, Seq[Symbol])])
      : L.Tree = tree match {
    case H.LetL(name, IntLit(value), body) =>
      L.LetL(name, (value << 1) | 1, transform(body))
    case H.LetL(name, CharLit(value), body) =>
      L.LetL(name, (value << 3) | bitsToIntMSBF(1, 1, 0), transform(body))
    case H.LetL(name, BooleanLit(value), body) =>
      val truthBit = if (value) 1 else 0
      L.LetL(name, bitsToIntMSBF(truthBit, 1, 0, 1, 0), transform(body))
    case H.LetL(name, UnitLit, body) =>
      L.LetL(name, unitLit, transform(body))

    case H.LetP(name, MiniScalaBlockAlloc(tag), Seq(s), body) =>
      tempLetL(1) { c1 =>
        tempLetP(CPSArithShiftR, Seq(s, c1)) { us =>
          L.LetP(name, CPSBlockAlloc(tag), Seq(us),
                 transform(body)) } }
    case H.LetP(name, MiniScalaBlockTag, args, body) =>
      tempLetP(CPSBlockTag, args) { ut =>
        tempLetL(1) { c1 =>
          tempLetP(CPSArithShiftL, Seq(ut, c1)) { ut1 =>
            L.LetP(name, CPSOr, Seq(ut1, c1), transform(body)) } } }
    case H.LetP(name, MiniScalaBlockLength, args, body) =>
      tempLetP(CPSBlockLength, args) { ul =>
        tempLetL(1) { c1 =>
          tempLetP(CPSArithShiftL, Seq(ul, c1)) { ul1 =>
            L.LetP(name, CPSOr, Seq(ul1, c1), transform(body)) } } }
    case H.LetP(name, MiniScalaBlockGet, Seq(v, i), body) =>
      tempLetL(1) { c1 =>
        tempLetP(CPSArithShiftR, Seq(i, c1)) { ui =>
          L.LetP(name, CPSBlockGet, Seq(v, ui), transform(body)) } }
    case H.LetP(name, MiniScalaBlockSet, Seq(v, i, o), body) =>
      tempLetL(1) { c1 =>
        tempLetP(CPSArithShiftR, Seq(i, c1)) { ui =>
          tempLetP(CPSBlockSet, Seq(v, ui, o)) { _ =>
            L.LetL(name, unitLit, transform(body)) } } }

    case H.LetP(name, MiniScalaIntAdd, args, body) =>
      tempLetP(CPSAdd, args) { r =>
        tempLetL(1) { c1 =>
          L.LetP(name, CPSSub, Seq(r, c1), transform(body)) } }
    case H.LetP(name, MiniScalaIntSub, Seq(v), body) =>
      tempLetL(2) { c1 =>
        L.LetP(name, CPSSub, Seq(c1, v), transform(body)) }
    case H.LetP(name, MiniScalaIntSub, args, body) =>
      tempLetP(CPSSub, args) { r =>
        tempLetL(1) { c1 =>
          L.LetP(name, CPSAdd, Seq(r, c1), transform(body)) } }
    case H.LetP(name, MiniScalaIntMul, Seq(x, y), body) =>
      tempLetL(1) { c1 =>
        tempLetP(CPSSub, Seq(x, c1)) { vx =>
          tempLetP(CPSArithShiftR, Seq(y, c1)) { uy =>
            tempLetP(CPSMul, Seq(vx, uy)) { ur =>
              L.LetP(name, CPSAdd, Seq(ur, c1), transform(body)) } } } }
    case H.LetP(name, MiniScalaIntDiv, Seq(x, y), body) =>
      tempLetL(1) { c1 =>
        tempLetP(CPSSub, Seq(x, c1)) { x1 =>
          tempLetP(CPSArithShiftR, Seq(y, c1)) { y1 =>
            tempLetP(CPSDiv, Seq(x1, y1)) { r =>
              L.LetP(name, CPSOr, Seq(r, c1), transform(body)) } } } }
    case H.LetP(name, MiniScalaIntMod, Seq(x, y), body) =>
      tempLetL(1) { c1 =>
        tempLetP(CPSSub, Seq(x, c1)) { x1 =>
          tempLetP(CPSSub, Seq(y, c1)) { y1 =>
            tempLetP(CPSMod, Seq(x1, y1)) { r0 =>
                L.LetP(name, CPSAdd, Seq(r0, c1), transform(body)) } } } }

    case H.LetP(name, MiniScalaIntArithShiftLeft, Seq(x, y), body) =>
      tempLetL(1) { c1 =>
        tempLetP(CPSSub, Seq(x, c1)) { x2 =>
          tempLetP(CPSArithShiftR, Seq(y, c1)) { uy =>
            tempLetP(CPSArithShiftL, Seq(x2, uy)) { ur =>
                L.LetP(name, CPSAdd, Seq(ur, c1), transform(body)) } } } }
    case H.LetP(name, MiniScalaIntArithShiftRight, Seq(x, y), body) =>
      tempLetL(1) { c1 =>
        tempLetP(CPSArithShiftR, Seq(y, c1)) { uy =>
          tempLetP(CPSArithShiftR, Seq(x, uy)) { ur =>
            L.LetP(name, CPSOr, Seq(ur, c1), transform(body)) } } }
    case H.LetP(name, MiniScalaIntBitwiseAnd, Seq(x, y), body) =>
      L.LetP(name, CPSAnd, Seq(x, y), transform(body))
    case H.LetP(name, MiniScalaIntBitwiseOr, Seq(x, y), body) =>
      L.LetP(name, CPSOr, Seq(x, y), transform(body))
    case H.LetP(name, MiniScalaIntBitwiseXOr, Seq(x, y), body) =>
      tempLetL(1) { c1 =>
        tempLetP(CPSXOr, Seq(x, y)) { ur =>
          L.LetP(name, CPSOr, Seq(ur, c1), transform(body)) } }

    case H.LetP(name, MiniScalaIntToChar, Seq(x), body) =>
      tempLetL(2) { c2 =>
        tempLetP(CPSArithShiftL, Seq(x, c2)) { tx =>
          L.LetP(name, CPSOr, Seq(tx, c2), transform(body)) } }

    case H.LetP(name, MiniScalaByteRead, Seq(), body) =>
      tempLetP(CPSByteRead, Seq()) { t1 =>
        tempLetL(1) { c1 =>
          tempLetP(CPSArithShiftL, Seq(t1, c1)) { t2 =>
            L.LetP(name, CPSOr, Seq(t2, c1), transform(body)) } } }
    case H.LetP(name, MiniScalaByteWrite, Seq(a), body) =>
      tempLetL(1) { c1 =>
        tempLetP(CPSArithShiftR, Seq(a, c1)) { t1 =>
          tempLetP(CPSByteWrite, Seq(t1)) { _ =>
            L.LetL(name, unitLit, transform(body)) } } }

    case H.LetP(name, MiniScalaCharToInt, Seq(x), body) =>
      tempLetL(2) { c2 =>
        L.LetP(name, CPSArithShiftR, Seq(x, c2), transform(body)) }

    case H.LetP(name, MiniScalaId, args, body) =>
      L.LetP(name, CPSId, args, transform(body))

    case H.LetC(cnts, body) =>
      L.LetC(cnts map { c => L.CntDef(c.name, c.args, transform(c.body)) },
             transform(body))

    case H.AppC(cont, args) =>
      L.AppC(cont, args)

    case H.LetF(funs, body) if optimized =>
      val funNames = funs map (_.name)

      // Workers
      val workerFVs = {
        val enclosingFVs = worker mapValues (_._2.toSet)
        fixedPoint(Map(funNames map { n => (n, Set.empty[Symbol]) } :_*)) {
          funFVsApprox =>
          val allFVs = enclosingFVs ++ funFVsApprox
          Map(funs map { f =>
                (f.name, freeVariables(f.body)(allFVs) -- f.args) } : _*)
        }
      }
      val workerLinFVs = workerFVs map { case (f, fv) =>
        (f, if (fv(f)) f +: ((fv - f).toSeq) else fv.toSeq) }
      val workerName =
        (funNames map { n => (n, Symbol.fresh(n.toString)) }).toMap
      val newWorker = worker ++ (
        workerLinFVs map { case (n, fvs) => (n, (workerName(n), fvs)) })
      val workers = funs map { f =>
        val envArgs = workerLinFVs(f.name) map (_.copy)
        val closedBody = (transform(f.body)(newWorker)
                            subst Substitution(workerLinFVs(f.name), envArgs))
        L.FunDef(workerName(f.name), f.retC, envArgs ++ f.args, closedBody)
      }

      val escapingNames = funNames filter (
        workerFVs.values.flatten.toSet ++ freeVariables(body)(workerFVs))
      val escapingFuns = funs filter { f => escapingNames contains (f.name) }

      // Wrappers
      val wrapperFVs = workerLinFVs map { case (f, fv) =>
        (f, fv filter (_ != f)) }
      val wrappers = escapingFuns map { f =>
        val ret = Symbol.fresh("ret")
        val env = Symbol.fresh("env")
        val args = f.args map (_.copy)
        val expEnv = wrapperFVs(f.name) map (_.copy)
        val envArgs =
          if (workerFVs(f.name) contains f.name) env +: expEnv else expEnv
        val workerCall = L.AppF(workerName(f.name), ret, envArgs ++ args)
        val body = (expEnv.zipWithIndex :\ (workerCall : L.Tree)) {
          case ((s, i), b) =>
            tempLetL(i + 1) { i =>
              L.LetP(s, CPSBlockGet, Seq(env, i), b) }}
        L.FunDef(workerName(f.name).copy, ret, env +: args, body)
      }
      val wrapperName = (escapingNames, wrappers map (_.name)).zipped.toMap

      val newBody = {
        val init = (escapingNames :\ transform(body)(newWorker)) {
          case (n, b) =>
            ((wrapperName(n) +: wrapperFVs(n)).zipWithIndex :\ b) {
              case ((fv, i), b) =>
                tempLetL(i) { iSym =>
                  tempLetP(CPSBlockSet, Seq(n, iSym, fv)) { _ => b }}}}

        (escapingNames :\ init) { case (n, b) =>
        tempLetL(1 + wrapperFVs(n).length) { lSym =>
          L.LetP(n, CPSBlockAlloc(BlockTag.Function.id), Seq(lSym), b) }}
      }
      L.LetF(workers ++ wrappers, newBody)

    case H.LetF(funs, body) => // if !optimized =>
      val funNames = funs map(_.name)
      val workerNamesFV = funs map(fun => (Symbol.fresh(s"${fun.name}_worker"), freeVariables(fun)(Map.empty).toSeq))

      // Create each workers
      val workers = (funs zip workerNamesFV) map { case (H.FunDef(name, retC, args, body), (wName, wFV)) =>
        val env = Symbol.fresh(s"${name}_env")
        val extFV = wFV map (v => Symbol.fresh(s"${name}_free_$v"))
        val sub = Substitution(name +: wFV, env +: extFV)

        val nbody = wrap(extFV.zipWithIndex, transform(body) subst sub) {
          case ((fv, idx), body) =>
            tempLetL(idx + 1) { idx =>
              L.LetP(fv, CPSBlockGet, Seq(env, idx), body)
            }
        }

        L.FunDef(wName, retC, env +: args, nbody)
      }

      // Block sets
      val blockSets = wrap(funNames zip workerNamesFV, transform(body)) {
        case ((fName, (wName, wFV)), body) =>
          tempLetL(0) { z =>
            L.LetP(Symbol.fresh("t"), CPSBlockSet, Seq(fName, z, wName),
              wrap(wFV.zipWithIndex, body) {
                case ((fv, idx), body) =>
                  tempLetL(idx + 1) { idx =>
                    L.LetP(Symbol.fresh("t"), CPSBlockSet, Seq(fName, idx, fv), body)
                  }
              }
            )
          }
      }

      // Wrap block allocs
      val nbody = wrap(funNames zip workerNamesFV, blockSets) {
        case ((fName, (_, wFV)), body) =>
          tempLetL(wFV.length + 1) { size =>
            L.LetP(fName, CPSBlockAlloc(BlockTag.Function.id), Seq(size), body)
          }
      }

      L.LetF(workers, nbody)

    case H.AppF(fun, retC, args) if optimized && (worker contains fun) =>
      val (workerName, workerFVs) = worker(fun)
      L.AppF(workerName, retC, workerFVs ++ args)

    case H.AppF(fun, retC, args) =>
      tempLetL(0) { zSym =>
        tempLetP(CPSBlockGet, Seq(fun, zSym)) { codePtrSym =>
          L.AppF(codePtrSym, retC, fun +: args)}}

    case H.If(MiniScalaBlockP, Seq(a), thenC, elseC) =>
      ifEqLSB(a, Seq(0, 0), thenC, elseC)
    case H.If(MiniScalaIntP, Seq(a), thenC, elseC) =>
      ifEqLSB(a, Seq(1), thenC, elseC)
    case H.If(MiniScalaCharP, Seq(a), thenC, elseC) =>
      ifEqLSB(a, Seq(1,1,0), thenC, elseC)
    case H.If(MiniScalaBoolP, Seq(a), thenC, elseC) =>
      ifEqLSB(a, Seq(1,0,1,0), thenC, elseC)
    case H.If(MiniScalaUnitP, Seq(a), thenC, elseC) =>
      ifEqLSB(a, Seq(0,0,1,0), thenC, elseC)

    case H.If(MiniScalaIntLt, args, thenC, elseC) =>
      L.If(CPSLt, args, thenC, elseC)
    case H.If(MiniScalaIntLe, args, thenC, elseC) =>
      L.If(CPSLe, args, thenC, elseC)
    case H.If(MiniScalaEq, args, thenC, elseC) =>
      L.If(CPSEq, args, thenC, elseC)
    case H.If(MiniScalaNe, args, thenC, elseC) =>
      L.If(CPSNe, args, thenC, elseC)
    case H.If(MiniScalaIntGe, args, thenC, elseC) =>
      L.If(CPSGe, args, thenC, elseC)
    case H.If(MiniScalaIntGt, args, thenC, elseC) =>
      L.If(CPSGt, args, thenC, elseC)

    case H.Halt(arg) =>
      tempLetL(1) { c1 =>
        tempLetP(CPSArithShiftR, Seq(arg, c1)) { t1 =>
          L.Halt(t1) } }
  }

  private def freeVariables(tree: H.Tree)
                           (implicit worker: Map[Symbol, Set[Symbol]])
      : Set[Symbol] = tree match {
    case H.LetL(name, _, body) =>
      freeVariables(body) - name
    case H.LetP(name, _, args, body) =>
      freeVariables(body) - name ++ args
    case H.LetC(cnts, body) =>
      val cntNames = cnts map (_.name)
      freeVariables(body) ++ (cnts flatMap freeVariables)
    case H.LetF(funs, body) =>
      val funNames = funs map ((_ : H.FunDef).name)
      freeVariables(body) ++ (funs flatMap freeVariables) -- funNames
    case H.AppC(_, args) =>
      args.toSet
    case H.AppF(fun, _, args) =>
      args.toSet ++ (worker getOrElse(fun, Seq(fun)))
    case H.If(_, args, _, _) =>
      args.toSet
    case H.Halt(arg) =>
      Set(arg)
  }

  /*
   * Auxilary function.
   *
   * Example:
   *  // assuming we have a function with symbol f and the return continuation is rc:
   *
   *  val names = Seq("first", "second")
   *  val values = Seq(42, 112)
   *  val inner = L.AppF(f, rc, names)
   *  val res = wrap(names zip values , inner) {
   *    case ((n, v), inner) => L.LetL(n, v, inner)
   *  }
   *
   *  // res is going to be the following L.Tree
   *  L.LetL("first", 42,
   *    L.LetL("second", 112,
   *      L.AppF(f, rc, Seq("first", "second"))
   *    )
   *  )
   */
  private def wrap[T](args: Seq[T], inner: L.Tree)(createLayer: (T, L.Tree) => L.Tree) = {
    def addLayers(args: Seq[T]): L.Tree = args match {
      case h +: t => createLayer(h, addLayers(t))
      case _ => inner
    }
    addLayers(args)
  }

  private def freeVariables(cnt: H.CntDef)
                           (implicit worker: Map[Symbol, Set[Symbol]])
      : Set[Symbol] =
    freeVariables(cnt.body) -- cnt.args

  private def freeVariables(fun: H.FunDef)
                           (implicit worker: Map[Symbol, Set[Symbol]])
      : Set[Symbol] =
    freeVariables(fun.body) - fun.name -- fun.args

  // Tree builders

  /**
   * Call body with a fresh name, and wraps its resulting tree in one
   * that binds the fresh name to the given literal value.
   */
  private def tempLetL(v: Int)(body: L.Name => L.Tree): L.Tree = {
    val tempSym = Symbol.fresh("t")
    L.LetL(tempSym, v, body(tempSym))
  }

  /**
   * Call body with a fresh name, and wraps its resulting tree in one
   * that binds the fresh name to the result of applying the given
   * primitive to the given arguments.
   */
  private def tempLetP(p: L.ValuePrimitive, args: Seq[L.Name])
                      (body: L.Name => L.Tree): L.Tree = {
    val tempSym = Symbol.fresh("t")
    L.LetP(tempSym, p, args, body(tempSym))
  }

  /**
   * Generate an If tree to check whether the least-significant bits
   * of the value bound to the given name are equal to those passed as
   * argument. The generated If tree will apply continuation tC if it
   * is the case, and eC otherwise. The bits should be ordered with
   * the most-significant one first (e.g. the list (1,1,0) represents
   * the decimal value 6).
   */
  private def ifEqLSB(arg: L.Name, bits: Seq[Int], tC: L.Name, eC: L.Name)
      : L.Tree =
    tempLetL(bitsToIntMSBF(bits map { b => 1 } : _*)) { mask =>
      tempLetP(CPSAnd, Seq(arg, mask)) { masked =>
        tempLetL(bitsToIntMSBF(bits : _*)) { value =>
          L.If(CPSEq, Seq(masked, value), tC, eC) } } }
}
