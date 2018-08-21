package miniscala

sealed trait CMScalaLiteral {
  override def toString: String = this match {
    case IntLit(i) => i.toString
    case CharLit(c) => "'"+ (new String(Character.toChars(c))) +"'"
    case BooleanLit(v) => if (v) "true" else "false"
    case UnitLit => "()"
  }
}

object CMScalaLiteral {
  def apply(x: Any) = x match {
    case i: Int => IntLit(i)
    case c: Char => CharLit(c)
    case b: Boolean => BooleanLit(b)
    case _: Unit => UnitLit
    case _ => throw new Exception(s"$x is anot a Literal of our language")
  }
}

case class IntLit(value: Int) extends CMScalaLiteral
case class CharLit(value: Char) extends CMScalaLiteral
case class BooleanLit(value: Boolean) extends CMScalaLiteral
case object UnitLit extends CMScalaLiteral
