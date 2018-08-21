package miniscala

import miniscala.{ NominalCMScalaTreeModule => N }
import miniscala.{ SymbolicCMScalaTreeModule => S }
import CMScalaType._

class SemanticAnalyzer(parser: Parser) extends MiniScalaReporter with BugMiniScalaReporter {

  /*
   * Env that keeps track of variables defined.
   * The map stores true if the variable is mutable,
   * false otherwise and its type.
   */
  case class Env(
    vars: Map[String,(Symbol, Boolean, Type)] = Map.empty
    ) {

    /*
     * Return true if the variable is already defined
     * in this scope
     */
    def isDefined(name: String) = vars.contains(name)

    /*
     * Make a copy of this object and add a mutable variable 'name'
     */
    def withVar(name: String, tp: Type): Env = {
      copy(vars = vars + (name -> (new Symbol(name), true, tp)))
    }

    /*
     * Make a copy of this object and add an immutable variable 'name'
     */
    def withVal(name: String, tp: Type): Env = {
      copy(vars = vars + (name -> (new Symbol(name), false, tp)))
    }

    /*
     * Make a copy of this object and add in the list of immutable variables.
     */
    def withVals(list: List[(String,Type)]): Env = {
      copy(vars = vars ++ (list map { t => (t._1, (new Symbol(t._1), false, t._2)) }).toMap)
    }

    /*
     * Make a copy of this object and add in the list of immutable variables.
     */
    def withValsSym(list: List[(Symbol,Type)]): Env = {
      copy(vars = vars ++ (list map { t => (t._1.name, (t._1, false, t._2)) }).toMap)
    }

    /*
     * Return true if 'name' is a mutable variable defined in this scope
     * or in the outer scope.
     */
    def isVar(name: String) = vars.get(name) match {
      case None => false
      case Some((_, mut, _)) => mut
    }

    /*
     * Return the Type if the variable 'name' is an option.
     * i.e. Some(tp) if the variable exists or None if it doesn't
     */
    def apply(name: String): Option[Type] = vars.get(name) match {
      case Some((_, _, tp)) => Some(tp)
      case None => None
    }

    def sym(name: String): Symbol = vars.get(name) match {
      case Some((s, _, _)) => s
      case None => ???
    }
  }

  // Error reporting
  var printErr = 0;
  def ignoreErrors[T](f: => T) = {
    val sErr = numError;
    numError = 0
    printErr += 1
    val res = f
    printErr -= 1
    val nnErr = if (printErr == 0 ) numError else 0
    numError = sErr
    (res, nnErr)
  }

  var numError = 0
  def error(msg: String, pos: Pos): Unit = if (printErr == 0) {
    numError += 1
    parser.error(msg, pos)
  } else {
    numError += 1
  }

  // Warning reporting
  var numWarning = 0
  def warn(msg: String, pos: Pos): Unit = if (printErr == 0) {
    numWarning += 1
    parser.warn(msg, pos)
  }

  /*
   * Return a fresh name if a new variable needs to be defined
   */
  var next = 0
  def freshName(pref: String = "x") = {
    next += 1
    new Symbol(s"${pref}_$next")
  }

  /*
   * Auxiliary functions. May be useful.
   */
  def getName(arg: Any): String = arg match {
    case N.Arg(name, _, _) => name
    case N.FunDef(name, _, _, _, _) =>  name
    case _ => BUG(s"Don't know how to extract name from $arg")
  }

  def getPos(arg: Any): Pos = arg match {
    case N.Arg(_, _, pos) => pos
    case fd@N.FunDef(_, _, _, _, _) => fd.pos
    case _ => BUG(s"Don't know how to extract position from $arg")
  }

  def checkDuplicateNames(args: List[Any]): Boolean = args match {
    case h::t =>
      val name = getName(h)
      val (dup, other) = t partition { arg => name == getName(arg) }
      dup foreach { arg =>
        error(s"$name is already defined", getPos(arg))
      }
      checkDuplicateNames(other) || dup.length > 0
    case Nil => false
  }

  def funType(ftps: List[String], args: List[N.Arg], rtp: Type): FunType = {
    FunType(ftps.map(t => ("$Type", RefType(t))) ++ args.map { arg => (arg.name, arg.tp) }, rtp)
  }

  def listArgType(size: Int, tp: Type) = List.fill(size)(("", tp))

  /**
   * Run the Semantic Analyzer on the given AST.
   *
   * Print out the number of warnings and errors found, if any.
   * Return the AST with types resolved and the number of warnings
   * and errors.
   *
   * NOTE: we want our main program to return an Int!
   */
  def run(exp: N.Tree, progType: Type = UnknownType): (S.Tree, Int, Int) = {
    numError = 0
    numWarning = 0
    val nexp = typeCheck(exp, progType)(Env())
    if (numWarning > 0)
      System.err.println(s"""$numWarning warning${if (numWarning != 1) "s" else ""} found""")
    if (numError > 0)
      System.err.println(s"""$numError error${if (numError != 1) "s" else ""} found""")

    (nexp, numWarning, numError)
  }

  def typeNuOperator(op: String)(pos: Pos) = op match {
    case "byte-read" => FunType(Nil, IntType)
    case _ =>
      error(s"undefined operator", pos)
      UnknownType
  }

  // List of valid unary operators
  val isIntUnOperator   = Set("+","-")
  val isPolTest = Set("isBlock","isInt","isChar","isBool","isUnit","isPair","isList","isArray")

  /*
   * Returns the type of the unary operator 'op'
   */
  def typeUnOperator(op: String)(pos: Pos) = op match {
    case _ if isIntUnOperator(op) => FunType(List(("", IntType)), IntType)
    case "byte-write" => FunType(List(("", IntType)), UnitType)
    case _ =>
      error(s"undefined unary operator $op", pos)
      UnknownType
  }

  def blockGet(t: S.Tree, idx: Int) = S.Prim(MiniScalaBlockGet, List(t, S.Lit(IntLit(idx))))
  def blockSet(t: S.Tree, idx: Int, v: S.Tree) = S.Prim(MiniScalaBlockSet, List(t, S.Lit(IntLit(idx)), v))

  def isTags(t: S.Tree, tags: Int*): S.Tree = {
    val tag = freshName("tag")
    val name = freshName("sel")
    val ref = S.Ref(name).withType(t.tp)
    S.Let(name, t.tp, t,
      S.If(S.Prim(MiniScalaBlockP, List(ref)),
        S.Let(tag, IntType, S.Prim(MiniScalaBlockTag, List(ref)),
          (tags :\ (S.Lit(BooleanLit(false)): S.Tree)) {
            case (tt, tree) => S.If(S.Prim(MiniScalaEq, List(S.Ref(tag), S.Lit(IntLit(tt)))), S.Lit(BooleanLit(true)), tree)
          }
        ).withType(BooleanType),
        S.Lit(BooleanLit(false)).withType(BooleanType)
      ).withType(BooleanType)
    ).withType(BooleanType)
  }

  def anySelect(t: S.Tree, m: String, pt: Type, pos: Pos): S.Tree = {
    m match {
      case "isPair" => isTags(t, BlockTag.Pair.id)
      case "isArray" => isTags(t, BlockTag.Array.id)
      case "isList" => isTags(t, BlockTag.EmptyList.id, BlockTag.List.id)
      case _ if isPolTest(m) => S.Prim(MiniScalaPrimitive(m.substring(2).toLowerCase + "?"), List(t)).withType(BooleanType)
      case _ =>
        error(s"value $m is not a member of type Any", pos)
        S.Prim(ErrorPrim, Nil).withType(pt)
    }
  }

  def pairSelect(t: S.Tree, m: String, pt: Type, pos: Pos): S.Tree = {
    val BlockType(tps, _) = t.tp
    m match {
      case "_1" => blockGet(t, 0).withType(tps(0))
      case "_2" => blockGet(t, 1).withType(tps(1))
      case _ =>
        error(s"value $m is not a member of type Pair", pos)
        S.Prim(ErrorPrim, Nil).withType(pt)
    }
  }

  def arraySelect(t: S.Tree, m: String, pt: Type, pos: Pos): S.Tree = m match {
    case "length" => S.Prim(MiniScalaBlockLength, List(t)).withType(IntType)
    case _ =>
      error(s"value $m is not a member of type Array", pos)
      S.Prim(ErrorPrim, Nil).withType(pt)
  }

  def listSelect(t: S.Tree, m: String, pt: Type, pos: Pos): S.Tree = {
    val BlockType(List(tp), _) = t.tp
    m match {
      case "isEmpty" => S.Prim(MiniScalaEq, List(S.Prim(MiniScalaBlockTag, List(t)), S.Lit(IntLit(2)))).withType(BooleanType)
      case "head" => blockGet(t, 0).withType(tp)
      case "tail" => blockGet(t, 1).withType(t.tp)
      case _ =>
        error(s"value $m is not a member of type List", pos)
        S.Prim(ErrorPrim, Nil).withType(pt)
    }
  }

  // List of valid infix operators
  val isBOperator   = Set("<=",">=","<",">")
  val isIntOperator   = Set("+","-","*","/","%","&","|","^","<<",">>")

  /*
   * Returns the type of the binary operator 'op'. See case "+" for an example
   */
  def typeBinOperator(op: String)(pos: Pos) = op match {
    case _ if isIntOperator(op) => FunType(List(("", IntType), ("", IntType)), IntType)
    case _ if isBOperator(op) => FunType(List(("", IntType), ("", IntType)), BooleanType)
    case _ =>
      error("undefined binary operator", pos)
      UnknownType
  }


  /*
   * Returns the type of the ternary operator 'op'
   * operators: block-set
   */
  def typeTerOperator(op: String)(pos: Pos) = op match {
    case _ =>
      error(s"undefined ternary operator", pos)
      UnknownType
  }
  /*
   * Return the type of the operator 'op' with arity 'arity'
   */
  def typeOperator(op: String, arity: Int)(pos: Pos): Type = arity match {
    case 3 => typeTerOperator(op)(pos)
    case 2 => typeBinOperator(op)(pos)
    case 1 => typeUnOperator(op)(pos)
    case 0 => typeNuOperator(op)(pos)
    case _ =>
      error(s"undefined operator", pos)
      UnknownType
  }

  def subst(tp: Type, from: Map[String, Type]): Type = tp match {
    case FunType(args, rtp) => FunType(args map(arg => (arg._1, subst(arg._2, from))), subst(rtp, from))
    case BlockType(tps, tags) => BlockType(tps map(subst(_, from)), tags)
    case BaseType(tp) if from.isDefinedAt(tp) => from(tp)
    case _ => tp
  }

  /*
   * Check if 'tp' conforms to 'pt' and return the more precise type.
   * The result needs to be well formed.
   */
  def typeConforms(tp: Type, pt: Type)(env: Env, pos: Pos): Type = (tp, pt) match {
    case (_, _) if tp == pt => typeWellFormed(tp)(env, pos)
    case (_, UnknownType) => typeWellFormed(tp)(env, pos)  // tp <: Any
    case (NothingType, _) => typeWellFormed(pt)(env, pos)  // for function arguments
    case (_, AnyType) => typeWellFormed(tp)(env, pos)  // tp <: Any
    case (FunType(args1, rtp1), FunType(args2, rtp2)) if args1.length == args2.length =>

      // Extract argument types
      val (tparg1, rargs1) = args1 partition(_._1 == "$Type")
      val (tparg2, rargs2) = args2 partition(_._1 == "$Type")

      if (tparg1.length == tparg2.length) {
        val from = (tparg1 zip tparg2) map {
          case ((_, RefType(tp)), (_, pt)) => (tp, pt)
        } toMap
        val (nargs1, nargs2) = (rargs1 zip rargs2) map { case ((n1, a1), (n2, a2)) => ((n1, subst(a1, from)), (n2, subst(a2, from))) } unzip

        val nrtp1 = subst(rtp1, from)
        val nrtp2 = rtp2 // subst(rtp2, from)

        val (ntp, nErr) = ignoreErrors {
          FunType(typeConform(nargs2, nargs1)(env, pos), typeConforms(nrtp1, nrtp2)(env, pos))
        }
        if (nErr > 0) {
          error(s"type mismatch;\nfound   : $tp\nexpected: $pt", pos);
          pt
        } else {
          ntp
        }
      } else {
          error(s"error invalid number of generic types got ${tparg2.length} expected ${tparg1.length}", pos);
          pt
      }
    case (BlockType(List(pt), tags), FunType(List((_, tp)), rte)) if tags(BlockTag.Array.id) =>
      typeConforms(tp, IntType)(env, pos)
      ArrayType(typeConforms(pt, rte)(env, pos))
    case (BlockType(_, _), BlockType(_, tags)) if tags(-1) => // BlockType(Set(-1)) = any block
      typeWellFormed(tp)(env, pos)
    case (BlockType(tps, t1), BlockType(pts, t2)) if t1 subsetOf t2 =>
      BlockType((tps zip pts) map { p => typeConforms(p._1, p._2)(env, pos) } , t1)
    case _ => error(s"type mismatch;\nfound   : $tp\nexpected: $pt", pos); pt
  }

  /*
   * Auxiliary function used to check function type argument conformity.
   *
   * The function is verifying that 'tp' elements number n conforms
   * to 'pt' element number n. It returns the list of precise types
   * returned by each invocation to typeConforms
   */
  def typeConform(tp: List[(String, Type)], pt: List[(String,Type)])(env: Env, pos: Pos): List[(String, Type)] = {
    if (tp.length != pt.length) BUG("length of list does not match")
    (tp zip pt) map { case ((arg1, tp1), (arg2, tp2)) => {
      (if (tp1 != UnknownType) arg1 else arg2, typeConforms(tp1, tp2)(env, pos)) }
    }
  }

  /*
   * Verify that the type 'tp' is well formed. i.e there is no
   * UnknownType.
   */
  def typeWellFormed(tp: Type)(env: Env, pos: Pos): Type = tp match {
    case FunType(args, rte) =>
      FunType(args map { case (n, tp) => (n, typeWellFormed(tp)(env, pos)) }, typeWellFormed(rte)(env, pos))
    case BlockType(tps, tags) => BlockType(tps map(typeWellFormed(_)(env, pos)), tags)
    case UnknownType => error("malformed type", pos); UnknownType
    case _ => tp
  }

  /*
   * typeCheck takes an expression and an expected type (which may be UnknownType).
   * This is done via calling the typeInfer and typeConforms
   * functions (details below), and finally returning the original
   * expression with all typing information resolved.
   *
   * typeInfer uses the inference rules seen during the lectures
   * to discover the type of an expression. As a reminder, the rules we saw can be
   * found in lectures 5 and 6.
   *
   * The code must follow the inference rules seen during the lectures.
   *
   * The errors/warnings check that you had to implement for project 2
   * should be already implemented. However, there are new variables
   * introduced that need to be check for duplicate (function name,
   * variables names). We defined the rules for function semantic in
   * lecture 5.
   */
  def typeCheck(exp: N.Tree, pt: Type)(env: Env): S.Tree = {
    val nexp = typeInfer(exp, pt)(env)
    val rnexpType = typeConforms(nexp.tp, pt)(env, exp.pos)
    nexp.withType(rnexpType)
  }

  def typeInfer(exp: N.Tree, pt: Type)(env: Env): S.Tree = exp match {
    case N.Lit(i@IntLit(_)) => S.Lit(i).withType(IntType)
    case N.Lit(c@CharLit(_)) => S.Lit(c).withType(CharType)
    case N.Lit(b@BooleanLit(_)) => S.Lit(b).withType(BooleanType)
    case N.Lit(UnitLit) => S.Lit(UnitLit).withType(UnitType)
    case N.Prim("&&", List(e1, e2)) =>
      typeInfer(N.If(e1, e2, N.Lit(BooleanLit(false))).withPos(exp.pos), pt)(env)
    case N.Prim("||", List(e1, e2)) =>
      typeInfer(N.If(e1, N.Lit(BooleanLit(true)), e2).withPos(exp.pos), pt)(env)
    case N.Prim("!", List(e1)) =>
      typeInfer(N.If(e1, N.Lit(BooleanLit(false)), N.Lit(BooleanLit(true))).withPos(exp.pos), pt)(env)
    case N.Prim(op, List(e1, e2)) if op == "!=" || op == "==" =>
      val ne1 = typeCheck(e1, UnknownType)(env)
      val ne2 = typeCheck(e2, ne1.tp)(env)
      S.Prim(MiniScalaPrimitive(op), List(ne1, ne2)).withType(BooleanType)
    case N.Prim("block-set", List(e1, e2, e3)) =>
      val ne1 = typeCheck(e1, BlockTypeAny)(env)
      val ne2 = typeCheck(e2, IntType)(env)
      (ne1.tp, ne2) match {
        case (BlockType(List(tp), tags), _) if tags(BlockTag.Array.id) =>
          val ne3 = typeCheck(e3, tp)(env)
          S.Prim(MiniScalaBlockSet, List(ne1, ne2, ne3)).withType(UnitType)
      }
    case N.Prim(op, args) =>
      typeOperator(op, args.length)(exp.pos) match {
        case FunType(atps, rtp) =>
          val nargs = (args zip atps) map { case (arg, (_, tp)) =>
            typeCheck(arg, tp)(env) }
          S.Prim(MiniScalaPrimitive(op), nargs).withType(rtp)
        case UnknownType =>
          args foreach(typeCheck(_, AnyType)(env))
          S.Prim(ErrorPrim, Nil).withType(pt)
        case _ => BUG("operator's type needs to be FunType")
      }
    case N.Select(t, m) =>
      val nt = typeCheck(t, UnknownType)(env)
      nt.tp match {
        case _ if isPolTest(m) => anySelect(nt, m, pt, exp.pos)
        case BlockType(_, tags) if tags(BlockTag.Pair.id) =>
          pairSelect(nt, m, pt, exp.pos)
        case BlockType(_, tags) if tags(BlockTag.Array.id) =>
          arraySelect(nt, m, pt, exp.pos)
        case BlockType(_, tags) if tags(BlockTag.List.id) =>
          listSelect(nt, m, pt, exp.pos)
        case IntType if m == "toChar" =>
          S.Prim(MiniScalaIntToChar, List(nt)).withType(CharType)
        case CharType if m == "toInt" =>
          S.Prim(MiniScalaCharToInt, List(nt)).withType(IntType)
        case _ =>
          error(s"value $m is not a member of ${nt.tp}", exp.pos)
          S.Prim(ErrorPrim, Nil).withType(pt)
      }
    case N.Let(x, tp, rhs, body) =>
      if (env.isDefined(x))
        warn("reuse of variable name", exp.pos)
      val nrhs = typeCheck(rhs, tp)(env)
      val nenv = env.withVal(x, nrhs.tp)
      val nbody = typeCheck(body, pt)(nenv)
      S.Let(nenv.sym(x), nrhs.tp, nrhs, nbody).withType(nbody.tp)
    case N.Ref(x) =>
      env(x) match {
        case Some(tp) =>
          S.Ref(env.sym(x)).withType(tp)
        case _ =>
          error("undefined identifier", exp.pos)
          S.Ref(new Symbol(x)).withType(pt)
      }
    case N.If(cond, tBranch, eBranch) =>
      val ncond = typeCheck(cond, BooleanType)(env)
      val neBranch = typeCheck(eBranch, pt)(env)
      val ntBranch = typeCheck(tBranch, neBranch.tp)(env)

      S.If(ncond, ntBranch, neBranch).withType(neBranch.tp)
    case N.VarDec(x, tp, rhs, body) =>
      if (env.isDefined(x))
        warn("reuse of variable name", exp.pos)
      val nrhs = typeCheck(rhs, tp)(env)
      val nenv = env.withVar(x, nrhs.tp)
      val nbody = typeCheck(body, pt)(nenv)

      S.VarDec(nenv.sym(x), nrhs.tp, nrhs, nbody).withType(nbody.tp)
    case N.VarAssign(x, rhs) =>
      val (xs, xtp) = if (!env.isDefined(x)) {
        error("undefined identifier", exp.pos)
        (freshName(), UnknownType)
      } else {
        if (!env.isVar(x))
          error("reassignment to val", exp.pos)
        (env.sym(x), env(x).get)
      }

      val nrhs = typeCheck(rhs, xtp)(env)

      /*
       * Because of syntactic sugar, the variable
       * assignment can be accepted for an expression
       * of type Unit. In this case, we will modify
       * the AST and store the assignment value into
       * a "dummy" variable an return the Unit Literal.
       *
       * For example,
       *
       * If(..., VarAssign("x", Lit(1)), Lit(()))
       *
       * requires the two branches of the If to be of the same
       * type. In this case Unit. Therefore the then branch
       * will need to be modify to have the correct type.
       * Without changing the semantic!
       */
      pt match {
        case UnitType =>
          S.Let(freshName(), nrhs.tp, S.VarAssign(xs, nrhs).withType(nrhs.tp), S.Lit(UnitLit)).withType(UnitType)
        case _ => S.VarAssign(xs, nrhs).withType(nrhs.tp)
      }
    case N.While(cond, lbody, body) =>
      val ncond = typeCheck(cond, BooleanType)(env)
      val nlbody = typeCheck(lbody, UnitType)(env)
      val nbody = typeCheck(body, pt)(env)

      S.While(ncond, nlbody, nbody).withType(nbody.tp)
    case N.LetRec(funs, body) =>
      // Check duplicate name
      val (dup, other) = funs partition { fd => env.isDefined(fd.name) }
      dup foreach { fd => error(s"${fd.name} is already defined", fd.pos) }
      checkDuplicateNames(other)

      // Extract function types before type inference
      val ftps: List[(String, Type)] = funs map { fd => (fd.name, funType(fd.ptps, fd.args, fd.rtp)) }

      // Type check the function until it converges while ignoring errors.
      val (nftps, _) = ignoreErrors {
        fixedPoint(ftps, 10) { ftps => // what is a good limit?
          // Type check functions
          val nenv = env.withVals(ftps)
          val nfuns = (funs zip ftps) map { case (fd, (_, ftp)) => typeCheck(fd, ftp)(nenv) }

          // Extract functions' type after type inference
          (funs zip nfuns) map { case (fd, fdn) => (fd.name, funType(fd.ptps, fd.args, fdn.rtp)) }
        }
      }

      // Type check function against the converged types and now raise errors if any occurs
      val nenv = env.withVals(nftps)
      val nfuns = (funs zip nftps) map { case (fd, (_, ftp)) => typeCheck(fd, ftp)(nenv) }

      // Type check the body
      val nbody = typeCheck(body, pt)(nenv)

      S.LetRec(nfuns, nbody).withType(nbody.tp)
    case N.App(fun, ptps, args) =>
      // Check fun type
      val nFun = typeCheck(fun, FunType(ptps.map(("$Type", _)) ++ listArgType(args.length, NothingType), pt))(env)

      // Handling some errors
      val ftp = nFun.tp match {
        case ftp@FunType(fargs, _) => // if fargs.length == args.length =>
          ftp
        case BlockType(List(tp), tags) if tags(BlockTag.Array.id) =>
          FunType(List(("", IntType)), tp)
        case tp =>
          error(s"$tp does not take paramters", exp.pos)
          FunType(List.fill(args.length)(("", AnyType)), pt)
      }

      // Check arguments type
      val nargs = (args zip ftp.args) map { case (exp, (_, tp)) => typeCheck(exp, tp)(env) }

      // Transform some function applications into primitives on arrays.
      nFun.tp match {
        case BlockType(List(tp), tags) if tags(BlockTag.Array.id) =>
          S.Prim(MiniScalaBlockGet, List(nFun, nargs.head)).withType(tp)
        case _ =>
          S.App(nFun, ptps, nargs).withType(ftp.rtp)
      }
    case N.PairDec(p1, p2) =>
      val BlockType(List(t1, t2), _) = pt match {
        case BlockType(List(t1, t2), tags) if tags(BlockTag.Pair.id) => pt
        case _ => PairType(UnknownType, UnknownType)
      }
      val np1 = typeCheck(p1, t1)(env)
      val np2 = typeCheck(p2, t2)(env)
      val tp = PairType(np1.tp, np2.tp)
      val name = freshName("p")
      S.Let(name, tp, S.Prim(MiniScalaBlockAlloc(BlockTag.Pair.id), List(S.Lit(IntLit(2)))).withType(tp),
        S.Let(freshName(), UnitType, blockSet(S.Ref(name).withType(tp), 0, np1).withType(UnitType),
          S.Let(freshName(), UnitType, blockSet(S.Ref(name).withType(tp), 1, np2).withType(UnitType),
            S.Ref(name).withType(tp)
          ).withType(tp)
        ).withType(tp)
      ).withType(tp)
    case N.PrimAlloc(tp, args) =>
      (tp, args) match {
        case (BlockType(List(xtp), tags), List(size)) if tags(BlockTag.Array.id) => // Array
          val nsize = typeCheck(size, IntType)(env)
          S.Prim(MiniScalaBlockAlloc(BlockTag.Array.id), List(nsize)).withType(ArrayType(xtp))
        case (BlockType(List(xtp), tags), Nil) if tags(BlockTag.EmptyList.id) =>
          S.Prim(MiniScalaBlockAlloc(BlockTag.EmptyList.id), List(S.Lit(IntLit(0)))).withType(xtp match {
            case UnknownType => pt
            case _ => tp
          })
        case (BlockType(List(xtp), tags), List(h, t)) if tags(BlockTag.List.id) =>
          val nh = typeCheck(h, xtp)(env)
          val ntp = ListType(nh.tp)
          val nt = typeCheck(t, ntp)(env)
          val name = freshName("l")
          S.Let(name, ntp, S.Prim(MiniScalaBlockAlloc(BlockTag.List.id), List(S.Lit(IntLit(2)))).withType(ListType(xtp)),
            S.Let(freshName(), UnitType, blockSet(S.Ref(name).withType(tp), 0, nh).withType(UnitType),
              S.Let(freshName(), UnitType, blockSet(S.Ref(name).withType(tp), 1, nt).withType(UnitType),
                S.Ref(name).withType(ntp)
              ).withType(ntp)
            ).withType(ntp)
          ).withType(ntp)
        case _ =>
          error(s"no constructor found for type $tp with ${args.length} argument${if(args.length == 1) "" else "s"}.", exp.pos)
          S.Prim(ErrorPrim, Nil).withType(AnyType)
      }
    case N.Halt(prg) =>
      val nprg = typeCheck(prg, IntType)(env)
      S.Halt(nprg).withType(IntType)
    case _ => BUG(s"malformed expresstion $exp")
  }

  def typeCheck(fun: N.FunDef, pt: Type)(env: Env): S.FunDef = {
    // Check that argument names are unique
    checkDuplicateNames(fun.args)

    // Extract argument name/tpe
    val atps = fun.args map { arg => (arg.name, arg.tp) }
    val nenv = env.withVals(atps)

    // Type check function body
    val nfbody = typeCheck(fun.body, fun.rtp)(nenv)

    // Type check function def
    val ftp = funType(fun.ptps, fun.args, nfbody.tp)
    val rftp = typeConforms(ftp, pt)(env, fun.pos)

    val nargs = fun.args map { case N.Arg(name, tp, pos) => S.Arg(nenv.sym(name), tp, pos) }
    S.FunDef(env.sym(fun.name), fun.ptps, nargs, nfbody.tp, nfbody).withType(rftp)
  }
}
