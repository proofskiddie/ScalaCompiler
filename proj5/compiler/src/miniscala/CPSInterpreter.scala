package miniscala

import java.lang.Math.{ floorDiv, floorMod }
import scala.annotation.tailrec
import scala.collection.mutable.{ Map => MutableMap }
import IO._

/**
 * A tree-based interpreter for the CPS languages.
 *
 * @author Michel Schinz <Michel.Schinz@epfl.ch>
 */

abstract class CPSInterpreter[M <: CPSTreeModule](protected val treeModule: M) {
  import treeModule._

  def apply(tree: Tree): Unit =
    eval(tree, emptyEnv)

  def statistics(tree: Tree): Unit =
    ()

  protected sealed trait Value
  protected case class FunV(retC: Name, args: Seq[Name], body: Tree, env: Env)
      extends Value
  protected case class CntV(args: Seq[Name], body: Tree, env: Env)
      extends Value

  protected type Env = PartialFunction[Name, Value]
  protected val emptyEnv: Env = Map.empty

  @tailrec
  private def eval(tree: Tree, env: Env): Unit = {
    statistics(tree: Tree)
    (tree: @unchecked) match {
      case LetL(name, lit, body) =>
        eval(body, Map(name -> evalLit(lit)) orElse env)

      case LetP(name, prim, args, body) =>
        eval(body, Map(name -> evalValuePrim(prim, args map env)) orElse env)

      case LetC(cnts, body) =>
        val recEnv = MutableMap[Name, Value]()
        val env1 = recEnv orElse env
        for (CntDef(name, args, body) <- cnts)
          recEnv(name) = CntV(args, body, env1)
        eval(body, env1)

      case LetF(funs, body) =>
        val recEnv = MutableMap[Name, Value]()
        val env1 = recEnv orElse env
        for (FunDef(name, retC, args, body) <- funs) {
          recEnv(name) = wrapFunV(FunV(retC, args, body, env1))
        }
        eval(body, env1)

      case AppC(cnt, args) =>
        val CntV(cArgs, cBody, cEnv) = env(cnt)
        assume(cArgs.length == args.length)
        eval(cBody, Map(cArgs zip (args map env) : _*) orElse cEnv)

      case AppF(fun, retC, args) =>
        val FunV(fRetC, fArgs, fBody, fEnv) = unwrapFunV(env(fun))
        assume(fArgs.length == args.length)
        eval(fBody,
             Map((fRetC +: fArgs) zip ((retC +: args) map env): _*) orElse fEnv)

      case If(cond, args, thenC, elseC) =>
        val cnt = if (evalTestPrim(cond, args map env)) thenC else elseC
        val cntV = env(cnt).asInstanceOf[CntV]
        eval(cntV.body, cntV.env)

      case Halt(arg) =>
        ()
    }
  }

  protected def wrapFunV(funV: FunV): Value
  protected def unwrapFunV(v: Value): FunV

  protected def evalLit(l: Literal): Value
  protected def evalValuePrim(p: ValuePrimitive, args: Seq[Value]): Value
  protected def evalTestPrim(p: TestPrimitive, args: Seq[Value]): Boolean
}

object CPSInterpreterHigh extends CPSInterpreterHigh
class CPSInterpreterHigh extends CPSInterpreter(SymbolicCPSTreeModule)
    with (SymbolicCPSTreeModule.Tree => Unit) {
  import treeModule._

  private case class BlockV(tag: Int, contents: Array[Value]) extends Value
  private case class IntV_(value: Int) extends Value {
    require(BitTwiddling.fitsInNSignedBits(31)(value))
  }
  private case class CharV(value: Int) extends Value
  private case class BooleanV(value: Boolean) extends Value
  private case object UnitV extends Value

  private object IntV {
    def apply(v: Int): Value = IntV_((v << 1) >> 1)
    def unapply(v: Value): Option[Int] = v match {
      case IntV_(i) => Some(i)
      case _ => None
    }
  }

  protected def wrapFunV(funV: FunV): Value =
    BlockV(BlockTag.Function.id, Array(funV))
  protected def unwrapFunV(v: Value): FunV = v match {
    case BlockV(_, Array(funV: FunV)) => funV
  }

  protected def evalLit(l: Literal): Value = l match {
    case IntLit(i) => IntV(i)
    case CharLit(c) => CharV(c)
    case BooleanLit(b) => BooleanV(b)
    case UnitLit => UnitV
  }

  protected def evalValuePrim(p: ValuePrimitive, args: Seq[Value]): Value =
    (p, args) match {
      case (MiniScalaBlockAlloc(t), Seq(IntV(i))) => BlockV(t, Array.fill(i)(UnitV))
      case (MiniScalaBlockTag, Seq(BlockV(t, _))) => IntV(t)
      case (MiniScalaBlockLength, Seq(BlockV(_, c))) => IntV(c.length)
      case (MiniScalaBlockGet, Seq(BlockV(_, v), IntV(i))) => v(i)
      case (MiniScalaBlockSet, Seq(BlockV(_, v), IntV(i), o)) => v(i) = o; UnitV

      case (MiniScalaIntAdd, Seq(IntV(v1), IntV(v2))) => IntV(v1 + v2)
      case (MiniScalaIntSub, Seq(IntV(v1), IntV(v2))) => IntV(v1 - v2)
      case (MiniScalaIntSub, Seq(IntV(v1)))           => IntV(-v1)
      case (MiniScalaIntMul, Seq(IntV(v1), IntV(v2))) => IntV(v1 * v2)
      case (MiniScalaIntDiv, Seq(IntV(v1), IntV(v2))) => IntV(floorDiv(v1, v2))
      case (MiniScalaIntMod, Seq(IntV(v1), IntV(v2))) => IntV(floorMod(v1, v2))
      case (MiniScalaIntToChar, Seq(IntV(v))) => CharV(v)

      case (MiniScalaIntArithShiftLeft, Seq(IntV(v1), IntV(v2))) => IntV(v1 << v2)
      case (MiniScalaIntArithShiftRight, Seq(IntV(v1), IntV(v2))) => IntV(v1 >> v2)
      case (MiniScalaIntBitwiseAnd, Seq(IntV(v1), IntV(v2))) => IntV(v1 & v2)
      case (MiniScalaIntBitwiseOr, Seq(IntV(v1), IntV(v2))) => IntV(v1 | v2)
      case (MiniScalaIntBitwiseXOr, Seq(IntV(v1), IntV(v2))) => IntV(v1 ^ v2)

      case (MiniScalaByteRead, Seq()) => IntV(readByte())
      case (MiniScalaByteWrite, Seq(IntV(c))) => writeByte(c); UnitV
      case (MiniScalaCharToInt, Seq(CharV(c))) => IntV(c.toInt)

      case (MiniScalaId, Seq(v)) => v
    }

  protected def evalTestPrim(p: TestPrimitive, args: Seq[Value]): Boolean =
    (p, args) match {
      case (MiniScalaBlockP, Seq(BlockV(_, _))) => true
      case (MiniScalaBlockP, Seq(_)) => false

      case (MiniScalaIntP, Seq(IntV(_))) => true
      case (MiniScalaIntP, Seq(_)) => false
      case (MiniScalaIntLt, Seq(IntV(v1), IntV(v2))) => v1 < v2
      case (MiniScalaIntLe, Seq(IntV(v1), IntV(v2))) => v1 <= v2
      case (MiniScalaIntGe, Seq(IntV(v1), IntV(v2))) => v1 >= v2
      case (MiniScalaIntGt, Seq(IntV(v1), IntV(v2))) => v1 > v2

      case (MiniScalaCharP, Seq(CharV(_))) => true
      case (MiniScalaCharP, Seq(_)) => false

      case (MiniScalaBoolP, Seq(BooleanV(_))) => true
      case (MiniScalaBoolP, Seq(_)) => false

      case (MiniScalaUnitP, Seq(UnitV)) => true
      case (MiniScalaUnitP, Seq(_)) => false

      case (MiniScalaEq, Seq(v1, v2)) => v1 == v2
      case (MiniScalaNe, Seq(v1, v2)) => v1 != v2
    }
}

object CPSInterpreterLow extends CPSInterpreterLow
class CPSInterpreterLow extends CPSInterpreter(SymbolicCPSTreeModuleLow)
    with (SymbolicCPSTreeModuleLow.Tree => Unit) {
  import treeModule._
  import scala.language.implicitConversions

  protected case class BlockV(addr: Int, tag: Int, contents: Array[Value])
      extends Value
  protected case class IntV(value: Int) extends Value

  private var nextBlockAddr = 0
  private def allocBlock(tag: Int, contents: Array[Value]): BlockV = {
    val block = BlockV(nextBlockAddr, tag, contents)
    nextBlockAddr += 4
    block
  }

  private implicit def valueToInt(v: Value): Int = v match {
    case BlockV(addr, _, _) => addr
    case IntV(value)        => value
    case _: FunV | _: CntV  => sys.error(s"cannot convert $v to integer")
  }

  protected def wrapFunV(funV: FunV): Value = funV
  protected def unwrapFunV(v: Value): FunV = v.asInstanceOf[FunV]

  protected def evalLit(l: Literal): Value = IntV(l)

  protected def evalValuePrim(p: ValuePrimitive, args: Seq[Value]): Value =
    (p, args) match {
      case (CPSAdd, Seq(v1, v2)) => IntV(v1 + v2)
      case (CPSSub, Seq(v1, v2)) => IntV(v1 - v2)
      case (CPSSub, Seq(v1))     => IntV(-v1)
      case (CPSMul, Seq(v1, v2)) => IntV(v1 * v2)
      case (CPSDiv, Seq(v1, v2)) => IntV(floorDiv(v1, v2))
      case (CPSMod, Seq(v1, v2)) => IntV(floorMod(v1, v2))

      case (CPSArithShiftL, Seq(v1, v2)) => IntV(v1 << v2)
      case (CPSArithShiftR, Seq(v1, v2)) => IntV(v1 >> v2)
      case (CPSAnd, Seq(v1, v2)) => IntV(v1 & v2)
      case (CPSOr, Seq(v1, v2)) => IntV(v1 | v2)
      case (CPSXOr, Seq(v1, v2)) => IntV(v1 ^ v2)

      case (CPSByteRead, Seq()) => IntV(readByte())
      case (CPSByteWrite, Seq(c)) => writeByte(c); IntV(0)

      case (CPSBlockAlloc(t), Seq(s)) => allocBlock(t, Array.fill(s)(IntV(0)))
      case (CPSBlockTag, Seq(BlockV(_, t, _))) => IntV(t)
      case (CPSBlockLength, Seq(BlockV(_, _, c))) => IntV(c.length)
      case (CPSBlockGet, Seq(BlockV(_, _, c), i)) => c(i)
      case (CPSBlockSet, Seq(BlockV(_, _, c), i, v)) => c(i) = v; IntV(0)

      case (CPSId, Seq(o)) => o
    }

  protected def evalTestPrim(p: TestPrimitive, args: Seq[Value]): Boolean =
    (p, args) match {
      case (CPSLt, Seq(v1, v2)) => v1 < v2
      case (CPSLe, Seq(v1, v2)) => v1 <= v2
      case (CPSEq, Seq(v1, v2)) => v1 == v2
      case (CPSNe, Seq(v1, v2)) => v1 != v2
      case (CPSGe, Seq(v1, v2)) => v1 >= v2
      case (CPSGt, Seq(v1, v2)) => v1 > v2
    }
}

class CPSInterpreterLowWithStats(showStats: Boolean) extends CPSInterpreterLow {

  import SymbolicCPSTreeModuleLow._

  val stats = new Statistics()

  override def statistics(tree: Tree): Unit = {
    stats.inc(tree.getClass())
    tree match {
      case LetP(_, prim, _, _) =>
        stats.inc(prim.getClass())
      case LetF(funs, _) =>
        stats.incFuncs(funs.length)
      case LetC(conts, _) =>
        stats.incConts(conts.length)
      case If(cond, _, _, _) =>
        stats.inc(cond.getClass())
      case Halt(_) =>
        if (showStats) stats.print()
      case _ =>
    }
  }
}

class Statistics {
  import scala.collection.mutable.Map
  import Statistics._

  private[this] var funcs = 0
  private[this] var conts = 0
  private[this] val insts = Map[Class[_ <: miniscala.CPSTreeModule#Tree], Int]()
  private[this] val lprims = Map[Class[_ <: miniscala.CPSTestPrimitive], Int]()
  private[this] val vprims = Map[Class[_ <: miniscala.CPSValuePrimitive], Int]()
  private[this] def m_inc[T](map: Map[T, Int], cls: T): Unit = map += cls -> (m_get(map, cls) + 1)
  private[this] def m_get[T](map: Map[T, Int], cls: T): Int =  map.getOrElse(cls, 0)

  def inc(cls: Class[_ <: miniscala.CPSTreeModule#Tree])(implicit ov: OverloadHack1.type) = m_inc(insts, cls)
  def inc(cls: Class[_ <: miniscala.CPSTestPrimitive])(implicit ov: OverloadHack2.type)   = m_inc(lprims, cls)
  def inc(cls: Class[_ <: miniscala.CPSValuePrimitive])(implicit ov: OverloadHack3.type)  = m_inc(vprims, cls)
  def get(cls: Class[_ <: miniscala.CPSTreeModule#Tree])(implicit ov: OverloadHack1.type) = m_get(insts, cls)
  def get(cls: Class[_ <: miniscala.CPSTestPrimitive])(implicit ov: OverloadHack2.type)   = m_get(lprims, cls)
  def get(cls: Class[_ <: miniscala.CPSValuePrimitive])(implicit ov: OverloadHack3.type)  = m_get(vprims, cls)

  def incFuncs(incr: Int) = funcs += incr
  def incConts(incr: Int) = conts += incr
  def getFuncs = funcs
  def getConts = conts

  def print() =
    println(toString)

  override def toString: String = {
    def append(label: String, vals: Map[_ <: Class[_], Int], sb: StringBuffer) =
      if (!vals.isEmpty) {
        sb.append(label + "\n" + "=" * label.length + "\n")
        for ((occ, prim) <- vals.toList.map(p => (p._2, p._1.getSimpleName())).sortBy(-_._1))
          sb.append("%8d  %s\n".format(occ, prim))
        sb.append("\n")
      }

    // Create stats
    val sb = new StringBuffer()
    append("Instruction Stats", insts, sb)
    append("Value Primitives Stats", vprims, sb)
    append("Logic Primitives Stats", lprims, sb)

    sb.append("Functions defined: " + getFuncs + "\n")
    sb.append("Continuations defined: " + getConts + "\n")
    sb.toString
  }
}

object Statistics {
  /* We need to do overloading with methods that
   * have the exact same signature after erasure,
   * so we add an implicit OverloadHack parameter */
  implicit object OverloadHack1
  implicit object OverloadHack2
  implicit object OverloadHack3
}
