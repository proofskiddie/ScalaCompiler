package miniscala

import SymbolicCMScalaTreeModule._

/**
 * This interpreter specifies the semantics of our
 * programming language.
 *
 * The evaluation of each node returns a value.
 */
object CMScalaInterpreter extends (Tree => Unit) with BugMiniScalaReporter {

  def apply(ast: Tree): Unit =
    eval(ast)(Env())

  /*
   * Definition of the values of our language
   *
   * We can return constant Int, Boolean, Unit or Array.
   * We can also return Function. Primitive is a special
   * kind of function.
   */
  abstract class Value
  case class BlockV(tag: Int, contents: Array[Value]) extends Value
  case class IntV(x: Int) extends Value
  case class CharV(x: Int) extends Value
  case class BoolV(x: Boolean) extends Value
  case object UnitV extends Value
  case class FunctionV(args: List[Symbol], fbody: Tree, var env: Env) extends Value {
    // Add all the value into the existing environment
    def withVals(list: List[(Symbol,Value)]) = env = env.withVals(list)
  }
  case class Primitive(name: String) extends Value

  /**
   * Env of the interpreter. Keeps track of the value
   * of each variable defined.
   */
  case class Env(
    vars: Map[Symbol, Value] = Map.empty) {

      /*
       * Return a copy of the current state plus an immutable
       * variable 'name' of value 'v'
       */
      def withVal(name: Symbol, v: Value): Env = {
        copy(vars = vars + (name -> v))
      }

      /*
       * Return a copy of the current state plus all the immutables
       * variable in list.
       */
      def withVals(list: List[(Symbol,Value)]): Env = {
        copy(vars = vars ++ (list.map {case (n, v) => n -> v }))
      }

      /*
       * Return the value of the variable 'name'
       */
      def apply(name: Symbol): Value = vars(name)
  }

  private def validIndex(a: Array[Value], i: Int): Boolean =
    0 <= i && i < a.length

  /*
   * Evaluate the AST within the environment 'env'
   */
  def eval(exp: Tree)(env: Env): Value = exp match {
    case Lit(IntLit(x)) => IntV(x)
    case Lit(CharLit(x)) => CharV(x)
    case Lit(BooleanLit(x)) => BoolV(x)
    case Lit(UnitLit) => UnitV
    case Prim(op, args) => (op, args map { arg => eval(arg)(env) }) match {
      case (MiniScalaBlockAlloc(t), Seq(IntV(i))) => BlockV(t, Array.fill(i)(UnitV))
      case (MiniScalaBlockP, Seq(BlockV(_, _))) => BoolV(true)
      case (MiniScalaBlockP, Seq(_)) => BoolV(false)
      case (MiniScalaBlockTag, Seq(BlockV(t, _))) => IntV(t)
      case (MiniScalaBlockLength, Seq(BlockV(_, c))) => IntV(c.length)
      case (MiniScalaBlockGet, Seq(BlockV(_, v), IntV(i))) if (validIndex(v, i)) =>
        v(i)
      case (MiniScalaBlockSet, Seq(BlockV(_, v), IntV(i), o)) if (validIndex(v, i)) =>
        v(i) = o; UnitV

      case (MiniScalaIntP, Seq(IntV(_))) => BoolV(true)
      case (MiniScalaIntP, Seq(_)) => BoolV(false)

      case (MiniScalaIntAdd, Seq(IntV(v1), IntV(v2))) => IntV(v1 + v2)
      case (MiniScalaIntSub, Seq(IntV(v1), IntV(v2))) => IntV(v1 - v2)
      case (MiniScalaIntMul, Seq(IntV(v1), IntV(v2))) => IntV(v1 * v2)
      case (MiniScalaIntDiv, Seq(IntV(v1), IntV(v2))) => IntV(v1/v2)
      case (MiniScalaIntMod, Seq(IntV(v1), IntV(v2))) => IntV(v1%v2)

      case (MiniScalaIntArithShiftLeft, Seq(IntV(v1), IntV(v2))) => IntV(v1 << v2)
      case (MiniScalaIntArithShiftRight, Seq(IntV(v1), IntV(v2))) => IntV(v1 >> v2)
      case (MiniScalaIntBitwiseAnd, Seq(IntV(v1), IntV(v2))) => IntV(v1 & v2)
      case (MiniScalaIntBitwiseOr, Seq(IntV(v1), IntV(v2))) => IntV(v1 | v2)
      case (MiniScalaIntBitwiseXOr, Seq(IntV(v1), IntV(v2))) => IntV(v1 ^ v2)

      case (MiniScalaIntLt, Seq(IntV(v1), IntV(v2))) => BoolV(v1 < v2)
      case (MiniScalaIntLe, Seq(IntV(v1), IntV(v2))) => BoolV(v1 <= v2)
      case (MiniScalaEq, Seq(v1, v2)) => BoolV(v1 == v2)
      case (MiniScalaNe, Seq(v1, v2)) => BoolV(v1 != v2)
      case (MiniScalaIntGe, Seq(IntV(v1), IntV(v2))) => BoolV(v1 >= v2)
      case (MiniScalaIntGt, Seq(IntV(v1), IntV(v2))) => BoolV(v1 > v2)

      case (MiniScalaIntToChar, Seq(IntV(i)))
          if Character.isValidCodePoint(i) => CharV(i)

      case (MiniScalaCharP, Seq(CharV(_))) => BoolV(true)
      case (MiniScalaCharP, Seq(_)) => BoolV(false)

      case (MiniScalaByteRead, Seq()) => IntV(Console.in.read)
      case (MiniScalaByteWrite, Seq(IntV(c))) =>
        Console.out.write(c)
        Console.out.flush
        UnitV

      case (MiniScalaCharToInt, Seq(CharV(c))) => IntV(c)

      case (MiniScalaBoolP, Seq(BoolV(_))) => BoolV(true)
      case (MiniScalaBoolP, Seq(_)) => BoolV(false)

      case (MiniScalaUnitP, Seq(UnitV)) => BoolV(true)
      case (MiniScalaUnitP, Seq(_)) => BoolV(false)
    }
    case Let(x, tp, a, b) =>
      eval(b)(env.withVal(x, eval(a)(env)))
    case Ref(x) => env(x)
    case If(cond, tBranch, eBranch) =>
      eval(cond)(env) match {
        case BoolV(true)  => eval(tBranch)(env)
        case BoolV(false) => eval(eBranch)(env)
        case _ => BUG("Type should have been checked")
      }
    case VarDec(x, tp, rhs, body) =>
      eval(body)(env.withVal(x, BlockV(242, Array(eval(rhs)(env)))))
    case VarAssign(x, rhs) =>
      val erhs = eval(rhs)(env)
      val BlockV(_, arr) = env(x)
      arr(0) = erhs
      erhs
    case While(cond, lBody, body) =>
      while (eval(cond)(env) == BoolV(true)) {
        eval(lBody)(env)
      }
      eval(body)(env)
    case LetRec(funs, body) =>
      // Evaluate all functions
      val funcs = funs map { fun =>  (fun.name, BlockV(BlockTag.Function.id, Array(FunctionV(fun.args map { arg => arg.name }, fun.body, env)))) }

      // Add all functions to the functions environment (recursion)
      funcs foreach { case (_, BlockV(_, Array(func: FunctionV))) => func.withVals(funcs) }

      eval(body)(env.withVals(funcs))
    case App(fun, _, args) =>
      // Evaluate the arguments
      val eargs = args map { arg => eval(arg)(env) }

      // Evaluate the function to be called.
      eval(fun)(env) match {
        case BlockV(_, Array(FunctionV(fargs, fbody, fenv))) =>
          eval(fbody)(fenv.withVals(fargs zip eargs))
      }
    case Halt(arg) =>
      val IntV(e) = eval(arg)(env)
      println(s"Exit code: $e")
      UnitV
  }
}
