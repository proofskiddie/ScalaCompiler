package project3

class SemanticAnalyzer(parser: Parser) extends Reporter with BugReporter {
  import Language._

  /*
   * Primitive functions that do not need to be defined or declared.
   */
  val primitives = Map[String,(Boolean,Type)](
      "getchar" -> (false, FunType(List(), IntType)),
      "putchar" -> (false, FunType(List(("", IntType)), UnitType))
    )

  /*
   * Define an empty state for the Semantic Analyzer.
   *
   * NOTE:
   *   val env = new Env
   *
   *   env("hello") is equivalent to env.apply("hello")
   */
  class Env {
    def apply(name: String): Option[Type] = None
    def isVar(name: String) = false
  }

  /*
   * Env that keeps track of variables defined.
   * The map stores true if the variable is mutable,
   * false otherwise and its type.
   */
  case class TypeEnv(
    vars: Map[String,(Boolean, Type)] = primitives,
    outer: Env = new Env) extends Env {

    /*
     * Return true if the variable is already defined
     * in this scope
     */
    def isDefined(name: String) = vars.contains(name)

    /*
     * Make a copy of this object and add a mutable variable 'name'
     */
    def withVar(name: String, tp: Type): TypeEnv = {
      copy(vars = vars + (name -> (true, tp)))
    }

    /*
     * Make a copy of this object and add an immutable variable 'name'
     */
    def withVal(name: String, tp: Type): TypeEnv = {
      copy(vars = vars + (name -> (false, tp)))
    }

    /*
     * Make a copy of this object and add in the list of immutable variables.
     */
    def withVals(list: List[(String,Type)]): TypeEnv = {
      copy(vars = vars ++ (list map { t => (t._1, (false, t._2)) }).toMap)
    }

    /*
     * Return true if 'name' is a mutable variable defined in this scope
     * or in the outer scope.
     */
    override def isVar(name: String) = vars.get(name) match {
      case None => outer.isVar(name)
      case Some((mut, _)) => mut
    }

    /*
     * Return the Type if the variable 'name' is an option.
     * i.e. Some(tp) if the variable exists or None if it doesn't
     */
    override def apply(name: String): Option[Type] = vars.get(name) match {
      case Some((_, tp)) => Some(tp)
      case None => outer(name)
    }
  }

  // Error reporting
  var numError = 0
  def error(msg: String, pos: Position): Unit = {
    numError += 1
    parser.error(msg, pos)
  }

  // Warning reporting
  var numWarning = 0
  def warn(msg: String, pos: Position): Unit = {
    numWarning += 1
    parser.warn(msg, pos)
  }

  /*
   * Return a fresh name if a new variable needs to be defined
   */
  var next = 0
  def freshName(pref: String = "x") = {
    next += 1
    s"${pref}_$next"
  }

  /*
   * Auxiliary functions. May be useful.
   */
  def getName(arg: Any): String = arg match {
    case Arg(name, _, _) => name
    case FunDef(name, _, _, _) =>  name
    case _ => BUG(s"Don't know how to extract name from $arg")
  }

  def getPos(arg: Any): Position = arg match {
    case Arg(_, _, pos) => pos
    case fd@FunDef(_, _, _, _) => fd.pos
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

  def funType(args: List[Arg], rtp: Type): FunType = {
    FunType(args map { arg => (arg.name, arg.tp) }, rtp)
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
  def run(exp: Exp) = {
    numError = 0
    val nexp = typeCheck(exp, IntType)(TypeEnv())
    if (numWarning > 0)
      System.err.println(s"""$numWarning warning${if (numWarning != 1) "s" else ""} found""")
    if (numError > 0)
      System.err.println(s"""$numError error${if (numError != 1) "s" else ""} found""")

    (nexp, numWarning, numError)
  }

  // List of valid infix operators
  val isBOperator   = Set("==","!=","<=",">=","<",">")
  val isIntOperator   = Set("+","-","*","/")

  /*
   * Returns the type of the binary operator 'op'. See case "+" for an example
   * TODO: implement the remaining binary operators for typeBinOperator
   */
  def typeBinOperator(op: String)(pos: Position) = op match {
    case "+" => FunType(List((op, IntType), ("", IntType)), IntType)
    case "-" => FunType(List((op, IntType), ("", IntType)), IntType)
    case "*" => FunType(List((op, IntType), ("", IntType)), IntType)
    case "/" => FunType(List((op, IntType), ("", IntType)), IntType)
    case "==" => FunType(List((op, IntType), ("", IntType)), BooleanType)
    case "!=" => FunType(List((op, IntType), ("", IntType)), BooleanType)
    case "<=" => FunType(List((op, IntType), ("", IntType)), BooleanType)
    case ">=" => FunType(List((op, IntType), ("", IntType)), BooleanType)
    case "<"  => FunType(List((op, IntType), ("", IntType)), BooleanType)
    case ">"  => FunType(List((op, IntType), ("", IntType)), BooleanType)
    case _ =>
      error("undefined binary operator", pos)
      UnknownType
  }

  // List of valid unary operators
  val isIntUnOperator   = Set("+","-")

  /*
   * Returns the type of the unary operator 'op'
   * TODO: implement typeUnOperator
   */
  def typeUnOperator(op: String)(pos: Position) = op match {
    case "+" => FunType(List(("", IntType)), IntType)
    case "-" => FunType(List(("", IntType)), IntType)
    case _ =>
      error(s"undefined unary operator", pos)
      UnknownType
  }

  /*
   * Returns the type of the ternary operator 'op'
   * TODO: implement typeTerOperator
   * operators: block-set
   */
  def typeTerOperator(op: String)(pos: Position) = op match {
    case "block-set" =>
      FunType(List(("", ArrayType(UnknownType)), ("", IntType)), UnknownType)
    case _ => 
      error(s"undefined unary operator", pos)
      UnknownType
  }
  /*
   * Return the type of the operator 'op' with arity 'arity'
   */
  def typeOperator(op: String, arity: Int)(pos: Position): Type = arity match {
    case 3 => typeTerOperator(op)(pos)
    case 2 => typeBinOperator(op)(pos)
    case 1 => typeUnOperator(op)(pos)
    case _ =>
      error(s"undefined operator", pos)
      UnknownType
  }

  /*
   * Check if 'tp' conforms to 'pt' and return the more precise type.
   * The result needs to be well formed.
   *
   * TODO: implement the case of function type.
   */
  def typeConforms(tp: Type, pt: Type)(env: TypeEnv, pos: Position): Type = (tp, pt) match {
    case (_, _) if tp == pt => typeWellFormed(tp)(env, pos)
    case (_, UnknownType) => typeWellFormed(tp)(env, pos)  // tp <: Any
    case (UnknownType, _) => typeWellFormed(pt)(env, pos)  // for function arguments
    case (FunType(args1, rtp1), FunType(args2, rtp2)) if args1.length == args2.length =>
      FunType(typeConform(args2, args1)(env,pos), typeConforms(rtp1, rtp2)(env, pos))
    case (ArrayType(tp), ArrayType(pt)) => ArrayType(typeConforms(tp, pt)(env, pos))
    case (ArrayType(pt), FunType(List((_, tp)), rte)) =>
      typeConforms(tp, IntType)(env, pos)
      ArrayType(typeConforms(pt, rte)(env, pos))
    case _ => error(s"type mismatch;\nfound   : $tp\nexpected: $pt", pos); pt
  }

  /*
   * Auxiliary function used to check function type argument conformity.
   *
   * The function is verifying that 'tp' elements number n conforms
   * to 'pt' element number n. It returns the list of precise types
   * returned by each invocation to typeConforms
   */
  def typeConform(tp: List[(String, Type)], pt: List[(String,Type)])(env: TypeEnv, pos: Position): List[(String, Type)] = {
    if (tp.length != pt.length) BUG("length of list does not match")
    (tp zip pt) map { case ((arg1, tp1), (arg2, tp2)) =>
      (if (tp1 != UnknownType) arg1 else arg2, typeConforms(tp1, tp2)(env, pos))
    }
  }

  /*
   * Verify that the type 'tp' is well formed. i.e there is no
   * UnknownType.
   */
  def typeWellFormed(tp: Type)(env: TypeEnv, pos: Position): Type = tp match {
    case FunType(args, rte) =>
      FunType(args map { case (n, tp) => (n, typeWellFormed(tp)(env, pos)) }, typeWellFormed(rte)(env, pos))
    case ArrayType(tp) => ArrayType(typeWellFormed(tp)(env, pos))
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
   * TODO: Remove the ??? and add the correct implementation.
   * The code must follow the inference rules seen during the lectures.
   *
   * The errors/warnings check that you had to implement for project 2
   * should be already implemented. However, there are new variables
   * introduced that need to be check for duplicate (function name,
   * variables names). We depfined the rules for function semantic in
   * lecture 5.
   */
  def typeCheck(exp: Exp, pt: Type)(env: TypeEnv): Exp = {
    val nexp = typeInfer(exp, pt)(env)
    val rnexpType = typeConforms(nexp.tp, pt)(env, exp.pos)
    nexp.withType(rnexpType)
  }

  def typeInfer(exp: Exp, pt: Type)(env: TypeEnv): Exp = exp match {
    case Lit(_: Int) => exp.withType(IntType)
    case Lit(_: Boolean) => exp.withType(BooleanType)
    case Lit(_: Unit) => exp.withType(UnitType)
    case Prim(op, args) =>
      typeOperator(op, args.length)(exp.pos) match {
        case FunType(List(("", ArrayType(UnknownType)), ("", IntType)), UnknownType) =>
          val nargs = args map { x => typeCheck(x,UnknownType)(env) }
          Prim(op, nargs).withType(nargs(2).tp)
        case FunType(atps, rtp) =>
          val nargs = (args zip atps) map {
            case (x,t) => typeCheck(x, t._2)(env) }
          Prim(op, nargs).withType(rtp)
        case UnknownType => exp.withType(UnknownType)
        case _ => BUG("operator's type needs to be FunType")
      }
    case Let(x, tp, rhs, body) =>
      if (env.isDefined(x))
        warn("reuse of variable name", exp.pos)
      val nrhs = typeCheck(rhs, tp)(env)
      val nbody = typeCheck(body, pt)(env.withVal(x, nrhs.tp))
      Let(x, nrhs.tp, nrhs, nbody).withType(nbody.tp)
    case Ref(x) =>
      env(x) match {
        case Some(tp) => exp.withType(tp)
        case _ =>
          error("undefined identifier", exp.pos)
          exp.withType(UnknownType)
        }
    case If(cond, tBranch, eBranch) =>
      // Hint: type check the else branch before the
      // then branch.
      val condCheck = typeCheck(cond, BooleanType)(env)
      val eBranchCheck = typeCheck(eBranch, UnknownType)(env)
      val expectedType = eBranchCheck.tp
      val tBranchCheck = typeCheck(tBranch, expectedType)(env)
      If(condCheck, tBranchCheck, eBranchCheck).withType(tBranchCheck.tp)
    case VarDec(x, tp, rhs, body) =>
      if (env.isDefined(x))
        warn("reuse of variable name", exp.pos)
      val nrhs = typeCheck(rhs, tp)(env)
      val nbody = typeCheck(body, pt)(env.withVar(x, nrhs.tp))
      VarDec(x, nrhs.tp, nrhs, nbody).withType(nbody.tp)
    case VarAssign(x, rhs) =>
      val xtp = if (!env.isDefined(x)) {
        error("undefined identifier", exp.pos)
        UnknownType
      } else {
        if (!env.isVar(x))
          error("reassignment to val", exp.pos)
        env(x).get
      }
      val nrhs = typeCheck(rhs, env(x) match {
        case Some(tp) => tp
        case _ => UnknownType })(env)
      val nassign = VarAssign(x, nrhs).withType(nrhs.tp)
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
           Let(freshName(), nrhs.tp, nassign, Lit(()).withType(UnitType)).withType(UnitType)
        case _ => nassign
      }
    case While(cond, lbody, body) =>
      val ncond  = typeCheck(cond, BooleanType)(env)
      val nlbody = typeCheck(lbody, UnitType)(env)
      val nbody  = typeCheck(body, pt)(env)
      While(ncond, nlbody, nbody).withType(nbody.tp)
    case FunDef(fname, args, rtp, fbody) =>
      val raw = args map { case Arg(s, tp, _) => (s,tp) }
      val nbody = typeCheck(fbody, rtp)(env.withVals(raw))
      val funType = FunType(raw, nbody.tp)
      FunDef(fname, args, rtp, nbody).withType(funType)
    case LetRec(funs, body) => funs match {
      case Nil =>
        val nbody = typeCheck(body, IntType)(env)
        LetRec(Nil, nbody).withType(nbody.tp)
      case _ =>
        val funtypes = funs map {
          case FunDef(f,a,tp,_) => 
               (f, FunType( a map { case Arg(s, tp, _) => (s, tp) }, tp))
        }
        val nenv  = env.withVals(funtypes)
        val nfuns = (funs zip funtypes) map { case (f, ft) =>
          typeCheck(f, ft._2)(nenv) }
        val nbody = typeCheck(body, pt)(nenv)
        LetRec(nfuns , nbody).withType(nbody.tp)
    }
    case App(fun, args) =>

      // Check fun type
      val nFun: Exp = typeCheck(fun, fun.tp)(env)

      // Handling some errors
      val ftp = nFun.tp match {
        case ftp@FunType(fargs, _) if fargs.length == args.length =>
          ftp
        case ftp@FunType(fargs, rtp) if fargs.length < args.length =>
          error(s"too many arguments for method: ($fargs)$rtp", exp.pos)
          FunType(fargs ++ List.fill(args.length - fargs.length)(("", UnknownType)), rtp)
        case ftp@FunType(fargs, rtp) =>
          error(s"not enough arguments for method: ($fargs)$rtp", exp.pos)
          ftp
        case ArrayType(tp) =>
          FunType(List(("", IntType)), tp)
        case tp =>
          error(s"$tp does not take paramters", exp.pos)
          FunType(List.fill(args.length)(("", UnknownType)), pt)
      }

      // Check arguments type
      val nargs: List[Exp] = 
          args map { exp => typeCheck(exp, nFun.tp)(env)}

      // Transform some function applications into primitives on arrays.
      nFun.tp match {
        case ArrayType(tp) =>
          Prim("block-get", List(nFun, nargs.head)).withType(tp)
        case _ => App(nFun, nargs).withType(ftp.rtp)
      }
    case ArrayDec(size: Exp, etp: Type) =>
      val nsize = typeCheck(size, IntType)(env)
      ArrayDec(nsize, etp).withType(etp)
    case _ => BUG(s"malformed expresstion $exp")
  }
}
