package miniscala

/**
 * A class for MiniScala primitives.
 *
 * @author Michel Schinz <Michel.Schinz@epfl.ch>
 */

sealed abstract class MiniScalaPrimitive(val name: String) {
  override def toString: String = s"$name"
  def arity: Int
}

trait Nullary extends MiniScalaPrimitive { def arity = 0 }
trait Unary extends MiniScalaPrimitive { def arity = 1 }
trait Binary extends MiniScalaPrimitive { def arity = 2 }
trait Ternary extends MiniScalaPrimitive { def arity = 3 }

sealed abstract class MiniScalaValuePrimitive(name: String) extends MiniScalaPrimitive(name)
sealed abstract class MiniScalaTestPrimitive(name: String) extends MiniScalaPrimitive(name)

case object ErrorPrim extends MiniScalaPrimitive("error") with Nullary

// Primitives on blocks
case class MiniScalaBlockAlloc(tag: Int) extends MiniScalaValuePrimitive("block-alloc-"+ tag)
     with Unary
case object MiniScalaBlockP extends MiniScalaTestPrimitive("block?")
     with Unary
case object MiniScalaBlockTag extends MiniScalaValuePrimitive("block-tag")
     with Unary
case object MiniScalaBlockLength extends MiniScalaValuePrimitive("block-length")
     with Unary
case object MiniScalaBlockGet extends MiniScalaValuePrimitive("block-get")
     with Binary
case object MiniScalaBlockSet extends MiniScalaValuePrimitive("block-set")
     with Ternary

// Primitives on integers
case object MiniScalaIntP extends MiniScalaTestPrimitive("int?")
     with Unary

case object MiniScalaIntAdd extends MiniScalaValuePrimitive("+")
     with Binary
case object MiniScalaIntSub extends MiniScalaValuePrimitive("-")
     with Binary
case object MiniScalaIntMul extends MiniScalaValuePrimitive("*")
     with Binary
case object MiniScalaIntDiv extends MiniScalaValuePrimitive("/")
     with Binary
case object MiniScalaIntMod extends MiniScalaValuePrimitive("%")
     with Binary

case object MiniScalaIntArithShiftLeft extends MiniScalaValuePrimitive("<<")
    with Binary
case object MiniScalaIntArithShiftRight extends MiniScalaValuePrimitive(">>")
    with Binary
case object MiniScalaIntBitwiseAnd extends MiniScalaValuePrimitive("&")
    with Binary
case object MiniScalaIntBitwiseOr extends MiniScalaValuePrimitive("|")
    with Binary
case object MiniScalaIntBitwiseXOr extends MiniScalaValuePrimitive("^")
    with Binary

case object MiniScalaIntLt extends MiniScalaTestPrimitive("<")
     with Binary
case object MiniScalaIntLe extends MiniScalaTestPrimitive("<=")
     with Binary
case object MiniScalaIntGe extends MiniScalaTestPrimitive(">=")
     with Binary
case object MiniScalaIntGt extends MiniScalaTestPrimitive(">")
     with Binary

case object MiniScalaByteRead extends MiniScalaValuePrimitive("byte-read")
     with Nullary
case object MiniScalaByteWrite extends MiniScalaValuePrimitive("byte-write")
     with Unary

case object MiniScalaIntToChar extends MiniScalaValuePrimitive("int->char")
     with Unary

// Primitives on characters
case object MiniScalaCharP extends MiniScalaTestPrimitive("char?")
     with Unary

case object MiniScalaCharToInt extends MiniScalaValuePrimitive("char->int")
     with Unary

// Primitives on booleans
case object MiniScalaBoolP extends MiniScalaTestPrimitive("bool?")
     with Unary

// Primitives on unit
case object MiniScalaUnitP extends MiniScalaTestPrimitive("unit?")
     with Unary

// Primitives on arbitrary values

case object MiniScalaEq extends MiniScalaTestPrimitive("==")
     with Binary
case object MiniScalaNe extends MiniScalaTestPrimitive("!=")
     with Binary
case object MiniScalaId extends MiniScalaValuePrimitive("id")
    with Unary

object MiniScalaPrimitive {
  def isDefinedAt(name: String): Boolean =
    byName isDefinedAt name

  def isDefinedAt(name: String, arity: Int): Boolean =
    (byName isDefinedAt name) && (byName(name).arity == arity)

  def apply(name: String): MiniScalaPrimitive =
    byName(name)

  private val blockAllocators = for (i <- 0 to 200) yield MiniScalaBlockAlloc(i)

  // Note: private primitives (id and block-allo-c for n > 200) are ommitted
  // on purpose from this map, as they are not meant to be used by user code.
  private val byName: Map[String, MiniScalaPrimitive] =
    Map((Seq(MiniScalaBlockP, MiniScalaBlockTag, MiniScalaBlockLength, MiniScalaBlockGet, MiniScalaBlockSet,
             MiniScalaIntP, MiniScalaIntAdd, MiniScalaIntSub, MiniScalaIntMul, MiniScalaIntDiv, MiniScalaIntMod,
             MiniScalaIntArithShiftLeft, MiniScalaIntArithShiftRight,
             MiniScalaIntBitwiseAnd, MiniScalaIntBitwiseOr, MiniScalaIntBitwiseXOr,
             MiniScalaIntLt, MiniScalaIntLe, MiniScalaEq, MiniScalaNe, MiniScalaIntGe, MiniScalaIntGt, MiniScalaIntToChar,
             MiniScalaCharP, MiniScalaByteRead, MiniScalaByteWrite, MiniScalaCharToInt,
             MiniScalaBoolP,
             MiniScalaUnitP) ++ blockAllocators)
        map { p => (p.name, p) } : _*)
}
