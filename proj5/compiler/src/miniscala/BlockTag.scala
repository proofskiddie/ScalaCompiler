package miniscala

/**
 * Predefined tags for blocks.
 *
 * @author Michel Schinz <Michel.Schinz@epfl.ch>
 */

object BlockTag extends Enumeration {
  val Pair, Array, EmptyList, List = Value
  val String = Value(200)
  val RegisterFrame = Value(201)
  val Function = Value(202)
  val Variable = Value(242)
}
