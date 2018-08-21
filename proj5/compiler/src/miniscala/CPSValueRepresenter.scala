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

  private def transform(tree: H.Tree)
                       (implicit worker: Map[Symbol, (Symbol, Seq[Symbol])])
      : L.Tree = tree match {

    // Literals
    case H.LetL(name, IntLit(value), body) =>
      L.LetL(name, (value << 1) | 1, transform(body))
    case H.LetL(name, CharLit(value), body) =>
      L.LetL(name, (value << 3) | bitsToIntMSBF(1, 1, 0), transform(body))

    // TODO: Add missing literals

    // *************** Primitives ***********************
    // Make sure you implement all possible primitives
    // (defined in MiniScalaPrimitives.scala)
    //
    // Integer primitives
    case H.LetP(name, MiniScalaIntAdd, args, body) =>
      tempLetP(CPSAdd, args) { r =>
        tempLetL(1) { c1 =>
          L.LetP(name, CPSSub, Seq(r, c1), transform(body)) } }

    case H.LetP(name, MiniScalaIntSub, args, body) =>
      tempLetP(CPSSub, args) { r =>
        tempLetL(1) { c1 =>
          L.LetP(name, CPSAdd, Seq(r, c1), transform(body)) } }
  
    case H.LetP(name, MiniScalaIntMul, Seq(a1,a2), body) =>
      arithHelper(CPSMul, name)(a1,a2)(body)

    case H.LetP(name, MiniScalaIntDiv, Seq(a1,a2), body) =>
      arithHelper(CPSDiv, name)(a1,a2)(body)

    case H.LetP(name, MiniScalaIntMod, Seq(a1,a2), body) =>
      arithHelper(CPSMod, name)(a1,a2)(body)

    case H.LetP(name, MiniScalaIntArithShiftLeft, Seq(a1,a2), body) =>
      arithHelper(CPSArithShiftL, name)(a1,a2)(body)

    case H.LetP(name, MiniScalaIntArithShiftRight, Seq(a1,a2), body) =>
      arithHelper(CPSArithShiftR, name)(a1,a2)(body)

    case H.LetP(name, MiniScalaIntBitwiseAnd, args, body) =>
      tempLetPKeepName(CPSAnd, args, name) { c1 => transform(body) }

    case H.LetP(name, MiniScalaIntBitwiseOr, args, body) =>
      tempLetPKeepName(CPSOr, args, name) { c1 => transform(body) }

    case H.LetP(name, MiniScalaIntBitwiseXOr, args, body) =>
      tempLetP(CPSXOr, args) { c1 =>
        tempLetL(1) { one =>
          tempLetPKeepName(CPSAdd, Seq(c1, one), name) { ret => transform(body) }}}

    case H.LetP(name, MiniScalaId, args, body) =>
      tempLetPKeepName(CPSId, args, name) { c1 => transform(body) }

    // TODO: Add missing integer primitives
    case H.LetL(name, BooleanLit(b), body) =>
      val i = if (b) 26 else 10
      L.LetL(name, i, transform(body))

    case H.LetL(name, UnitLit, body) =>
        L.LetL(name, 2, transform(body)) 

    // Block primitives
    case H.LetP(name, MiniScalaBlockAlloc(k), Seq(n1), body) =>
      tempLetL(1) { c1 =>
        tempLetP (CPSArithShiftR, Seq(n1, c1)) { t1 =>
          tempLetPKeepName (CPSBlockAlloc(k), Seq(t1), name) {
            e => transform(body) }}}

    case H.LetP(name, MiniScalaBlockTag, Seq(n1), body) =>
      tempLetL(1) { c1 =>
        tempLetP (CPSBlockTag, Seq(n1)) { t1 =>
          tempLetP (CPSArithShiftL, Seq(t1, c1)) { t2 =>
            tempLetPKeepName (CPSAdd, Seq(t2, c1), name) {
              e => transform(body) }}}}

    case H.LetP(name, MiniScalaBlockLength, Seq(n1), body) =>
      tempLetL(1) { c1 =>
        tempLetP (CPSBlockLength, Seq(n1)) { t1 =>
          tempLetP (CPSArithShiftL, Seq(t1, c1)) { t2 =>
            tempLetPKeepName (CPSAdd, Seq(t2, c1), name) {
              e => transform(body) }}}}

    case H.LetP(name, MiniScalaBlockGet, Seq(b, i), body) =>
      tempLetL(1) { c1 =>
        tempLetP(CPSArithShiftR, Seq(i, c1)) { ni =>
          tempLetPKeepName(CPSBlockGet, Seq(b, ni), name) { e => transform(body) }}}

    case H.LetP(name, MiniScalaBlockSet, Seq(b, i, w), body) =>
      tempLetL(1) { c1 => 
        tempLetP(CPSArithShiftR, Seq(i, c1)) { ni =>
          tempLetPKeepName(CPSBlockSet, Seq(b, ni, w), name) { e => transform(body) }}}

    case H.LetP(name, MiniScalaCharToInt, Seq(n1), body) =>
      tempLetL(2) { c2 =>
        tempLetPKeepName(CPSArithShiftR, Seq(n1, c2), name) {
          e => transform(body) }}

    case H.LetP(name, MiniScalaIntToChar, Seq(n1), body) =>
      tempLetL(2) { c2 =>
        tempLetP(CPSArithShiftL, Seq(n1, c2)) { t1 =>
          tempLetPKeepName(CPSAdd, Seq(t1, c2), name) {
            e => transform(body) }}}

    case H.LetP(name, MiniScalaByteWrite, Seq(n1), body) =>
      tempLetL(1) { one => 
        tempLetP(CPSArithShiftR, Seq(n1, one)) { c =>
          tempLetP(CPSByteWrite, Seq(c)) { _ =>
            L.LetL(name, 2, transform(body))
          }}}

    case H.LetP(name, MiniScalaByteRead, Seq(), body) =>
      tempLetP(CPSByteRead, Seq()) { t1 =>
        tempLetL(1) { c1 =>
          tempLetP(CPSArithShiftL, Seq(t1, c1)) { t2 =>
            tempLetPKeepName(CPSAdd, Seq(t2, c1), name)
            { e => transform(body) }}}}
    
    // IO primitives
    // TODO

    // Other primitives
    // TODO
  //  case H.LetP
    // Continuations nodes (LetC, AppC)
    case H.LetC(cnts, body) =>
      val ncnts = cnts map { case H.CntDef(name, args, e) =>
        L.CntDef(name, args, transform(e)) }
      L.LetC(ncnts, transform(body))

    case H.AppC(name, args) =>
      L.AppC(name, args)
/*
    // Functions nodes (LetF, AppF)
    case H.LetF(funs, e) =>
      val tempData = funs map { case fun@H.FunDef(name, retC, args, body) =>
        val w = Symbol.fresh("w")
        val s = Symbol.fresh("s")
        val env = Symbol.fresh("env")
        val funFV = freeVariables(fun)(Map.empty).toSeq
        val symVs = funFV map { c => Symbol.fresh("v") }
        val symUs = funFV map { c => Symbol.fresh("U") }
        val indices = Seq.range(1, funFV.size + 1, 1)
        val subU = Substitution(funFV.toSeq, symUs.toSeq)
        val workerfunDef = L.FunDef(w, retC, args ++ symUs, transform(body.subst(subU)))
        val wrapperfunDef = L.FunDef(s, 
        wrap(symVs zip indices, transform(body.subst(sub))) {
            case ((n, v), inner) => tempLetL(v) { c =>
              L.LetP(n, CPSBlockGet, Seq(env, c), inner)}
          })
        (name, funDef, w +: funFV)
      }
      val funDefs = tempData map { case (_, fd, _) => fd }
      val namesFV = tempData map { case(x,_,y) => (x,y)}
      val allFV = (tempData map { case (name,_,fv) =>
        (Seq().padTo(fv.size, name).zipWithIndex) zip fv }).flatten
      val blockSetArgs = allFV map { x => (Symbol.fresh("t"),x) }

      val f_blockAlloc = { (tree : L.Tree) =>
        wrap(namesFV, tree) { case ((n, v), inner) =>
          tempLetL(v.size) { c =>
            L.LetP(n, CPSBlockAlloc(202), Seq(c), inner) }}}
      val blockSetTree = wrap(blockSetArgs, transform(e))
          { case ((sym, ((name, index), fv)), inner) =>
              tempLetL(index) { c =>
                L.LetP(sym, CPSBlockSet, Seq(name, c, fv), inner) }}
      val body = f_blockAlloc(blockSetTree)
      L.LetF(funDefs, body)
 */
    // Functions nodes (LetF, AppF)
    case H.LetF(funs, e) =>
      val tempData = funs map { case fun@H.FunDef(name, retC, args, body) =>
        val w = Symbol.fresh("w")
        val env = Symbol.fresh("env")
        val funFV = freeVariables(fun)(Map.empty).toSeq
        val symVs = funFV map { c => Symbol.fresh("v") }
        val indices = Seq.range(1, funFV.size + 1, 1)
        val sub = Substitution(name +: funFV.toSeq, env +: symVs.toSeq)
        val funDef = L.FunDef(w, retC, env +: args,
          wrap(symVs zip indices, transform(body.subst(sub))) {
            case ((n, v), inner) => tempLetL(v) { c =>
              L.LetP(n, CPSBlockGet, Seq(env, c), inner)}
          })
        (name, funDef, w +: funFV)
      }
      val funDefs = tempData map { case (_, fd, _) => fd }
      val namesFV = tempData map { case(x,_,y) => (x,y)}
      val allFV = (tempData map { case (name,_,fv) =>
        (Seq().padTo(fv.size, name).zipWithIndex) zip fv }).flatten
      val blockSetArgs = allFV map { x => (Symbol.fresh("t"),x) }

      val f_blockAlloc = { (tree : L.Tree) =>
        wrap(namesFV, tree) { case ((n, v), inner) =>
          tempLetL(v.size) { c =>
            L.LetP(n, CPSBlockAlloc(202), Seq(c), inner) }}}
      val blockSetTree = wrap(blockSetArgs, transform(e))
          { case ((sym, ((name, index), fv)), inner) =>
              tempLetL(index) { c =>
                L.LetP(sym, CPSBlockSet, Seq(name, c, fv), inner) }}
      val body = f_blockAlloc(blockSetTree)
      L.LetF(funDefs, body)

    case H.AppF(name, retC, args) =>
      tempLetL(0) { zero =>
      tempLetP(CPSBlockGet, Seq(name, zero)) { c =>
        L.AppF(c, retC, name +: args) }}

    // ********************* Conditionnals ***********************
    // Type tests
    case H.If(MiniScalaBlockP, Seq(a), thenC, elseC) =>
      ifEqLSB(a, Seq(0, 0), thenC, elseC)
      
    case H.If(MiniScalaIntP, Seq(a), thenC, elseC) =>
      ifEqLSB(a, Seq(1), thenC, elseC)      

    case H.If(MiniScalaBoolP, Seq(b), thenC, elseC) =>
      ifEqLSB(b, Seq(1,0,1,0), thenC, elseC)

    case H.If(MiniScalaUnitP, Seq(u), thenC, elseC) =>
      ifEqLSB(u, Seq(0,0,1,0), thenC, elseC)

    case H.If(MiniScalaCharP, Seq(c), thenC, elseC) =>
      ifEqLSB(c, Seq(1,1,0), thenC, elseC)
      
    // Test primitives (<, >, ==, ...)
      
    case H.If(MiniScalaIntLt, args, thenC, elseC) =>
      L.If(CPSLt, args, thenC, elseC)

    case H.If(MiniScalaIntLe, args, thenC, elseC) =>
      L.If(CPSLe, args, thenC, elseC)

    case H.If(MiniScalaIntGe, args, thenC, elseC) =>
      L.If(CPSGe, args, thenC, elseC)

    case H.If(MiniScalaIntGt, args, thenC, elseC) =>
      L.If(CPSGt, args, thenC, elseC)

    case H.If(MiniScalaEq, args, thenC, elseC) =>
      L.If(CPSEq, args, thenC, elseC)

    case H.If(MiniScalaNe, args, thenC, elseC) =>
      L.If(CPSNe, args, thenC, elseC)

    // Halt case
    case H.Halt(name) =>
      tempLetL(1) { c1 =>
        tempLetP(CPSArithShiftR, Seq(name, c1)) { c2 => L.Halt(c2) } }
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
  private def wrap[T](args: Seq[T], inner: L.Tree)(addOneLayer: (T, L.Tree) => L.Tree) = {
    def addLayers(args: Seq[T]): L.Tree = args match {
      case h +: t => addOneLayer(h, addLayers(t))
      case _ => inner
    }
    addLayers(args)
  }

  private def freeVariables(tree: H.Tree)
                           (implicit worker: Map[Symbol, Set[Symbol]])
      : Set[Symbol] = tree match {
    case H.LetL(name, _, body) =>
      freeVariables(body) - name
    case H.LetP(name, _, args, body) =>
      freeVariables(body) - name ++ args
    case H.LetC(cnts, e) =>
      val contFV = cnts map { x => freeVariables(x) }
      val setContFV = contFV.fold(Set()) { (a, b) => a ++ b }
      freeVariables(e) ++ setContFV
    case H.LetF(funs, e) =>
      val freenames = funs map { case H.FunDef(name, _, _, _) => name }
      val funsFV = funs map { x => freeVariables(x) }
      val setFunsFV = funsFV.fold(Set()) { (a, b) => a ++ b }
      freeVariables(e) ++ setFunsFV -- freenames
    case H.AppC(name, args) => args.toSet
    case H.AppF(name, _, args) => args.toSet + name
    case H.If(_, args, _, _) => args.toSet
    case _ => Set()
  }

  private def freeVariables(cnt: H.CntDef)
                           (implicit worker: Map[Symbol, Set[Symbol]])
      : Set[Symbol] =
    freeVariables(cnt.body) - cnt.name -- cnt.args

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

  private def tempLetPKeepName(p: L.ValuePrimitive, args: Seq[L.Name], name : L.Name)
                      (body: L.Name => L.Tree): L.Tree = {
    L.LetP(name, p, args, body(name)) 
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

  private def arithHelper(op : L.ValuePrimitive, name : L.Name)(a1 :Symbol, a2 :Symbol)
    (body :H.Tree)(implicit worker: Map[Symbol, (Symbol, Seq[Symbol])])
      : L.Tree = {
     tempLetL(1) { c1 =>
        tempLetP(CPSArithShiftR, Seq(a1, c1)) { arg1 =>
          tempLetP(CPSArithShiftR, Seq(a2, c1)) { arg2 =>
            tempLetP(op, Seq(arg1, arg2)) { res =>
              tempLetP(CPSArithShiftL, Seq(res, c1)) { sres =>
                tempLetPKeepName(CPSAdd, Seq(c1, sres), name) { c2 =>  transform(body)}}}}}}
  }
}
