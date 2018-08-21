package miniscala

object CMScalaType {
  abstract class Type
  case object UnknownType extends Type
  case class BaseType(v: String) extends Type {
    override def toString = v
  }

  case class RefType(tp: String) extends Type
  case class FunType(args: List[(String, Type)], rtp: Type) extends Type {
    val srtp = rtp match {
      case BaseType(t) => t
      case _ => s"($rtp)"
    }
    override def toString = if (args.length != 1)
       s"(${args map(_._2) mkString ","}) => $srtp"
     else
       s"${args.head._2} => $srtp"
  }
  case class BlockType(tp: List[Type], tags: Set[Int]) extends Type {
    override def toString = {
      if (tags(BlockTag.Pair.id)) s"(${tp(0)}, ${tp(1)})"
      else if (tags(BlockTag.Array.id)) s"Array[${tp(0)}]"
      else if (tags(BlockTag.List.id)) s"List[${tp{0}}]"
      else if (tags(BlockTag.String.id)) s"String"
      else super.toString
    }
  }

  object BlockType {
    def apply(tp: List[Type], x: Int*): BlockType = BlockType(tp, Set(x : _*))
  }

  val IntType = BaseType("Int")
  val UnitType = BaseType("Unit")
  val BooleanType = BaseType("Boolean")
  val CharType = BaseType("Char")
  val AnyType = BaseType("Any")
  val NothingType = BaseType("Nothing")

  // block types
  val BlockTypeAny = BlockType(Nil, Set(-1))
  def ListType(tp: Type) = BlockType(List(tp), BlockTag.EmptyList.id, BlockTag.List.id)
  def ArrayType(tp: Type) = BlockType(List(tp), BlockTag.Array.id)
  val StringType = ArrayType(CharType)
  def PairType(tp: Type, pt: Type) = BlockType(List(tp, pt), BlockTag.Pair.id)
}

import CMScalaType._

/**
 * Definition of our target language.
 *
 * The different nodes of the AST also keep Pos information
 * for error handling during the semantic analysis.
 */
trait CMScalaTreeModule {

  type Name
  type Primitive

  abstract class Tree {
    var pos: Pos = _
    var tp: Type = UnknownType

    def withPos(p: Pos) = {
      pos = p
      this
    }

    def withType(pt: Type) = {
      tp = pt
      this
    }
  }


  // Arithmetic
  case class Lit(x: CMScalaLiteral) extends Tree
  // CHANGED: instead of creating a node for different operator arity,
  // we use a single node with a list of arguments.
  case class Prim(op: Primitive, args: List[Tree]) extends Tree

  // Immutable variables
  case class Let(x: Name, xtp: Type, a: Tree, b: Tree) extends Tree
  case class Ref(x: Name) extends Tree

  // Branches
  case class If(cond: Tree, tBranch: Tree, eBranch: Tree) extends Tree

  // Mutable variables
  case class VarDec(x: Name, xtp: Type, rhs: Tree, body: Tree) extends Tree
  case class VarAssign(x: Name, rhs: Tree) extends Tree

  // While loops
  case class While(cond: Tree, lbody: Tree, body: Tree) extends Tree

  // Functions
  case class Arg(name: Name, tp: Type, pos: Pos)
  case class FunDef(name: Name, ptps: List[String], args: List[Arg], rtp: Type, body: Tree) {
    var pos: Pos = _
    var tp: Type = UnknownType

    def withPos(p: Pos) = {
      pos = p
      this
    }

    def withType(pt: Type) = {
      tp = pt
      this
    }
  }


  case class LetRec(funs: List[FunDef], body: Tree) extends Tree
  case class App(f: Tree, ptps: List[Type], args: List[Tree]) extends Tree

  // Data structure
  case class PairDec(p1: Tree, p2: Tree) extends Tree
  case class PrimAlloc(tps: Type, args: List[Tree]) extends Tree
  case class Select(t: Tree, m: String) extends Tree

  // halt
  case class Halt(exitVal: Tree) extends Tree
}

/**
 * Module for trees after parsing: names and primitives are
 * represented as strings.
 */
object NominalCMScalaTreeModule extends CMScalaTreeModule {
  type Name = String
  type Primitive = String
}

/**
 * Module for trees after name analysis: names are represented as
 * symbols (globally-unique names) and primitives as objects.
 */
object SymbolicCMScalaTreeModule extends CMScalaTreeModule {
  type Name = Symbol
  type Primitive = MiniScalaPrimitive
}
