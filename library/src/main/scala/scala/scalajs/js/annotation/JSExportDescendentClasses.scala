/*                     __                                               *\
**     ________ ___   / /  ___      __ ____  Scala.js API               **
**    / __/ __// _ | / /  / _ | __ / // __/  (c) 2013, LAMP/EPFL        **
**  __\ \/ /__/ __ |/ /__/ __ |/_// /_\ \    http://scala-lang.org/     **
** /____/\___/_/ |_/____/_/ | |__/ /____/                               **
**                          |/____/                                     **
\*                                                                      */



package scala.scalajs.js.annotation

/** Specifies that all the concrete classes extending the annotated class or
 *  should have all their public constructors exported for use in raw JS.
 *  The constructors exported this way are exported under their fully
 *  qualified name.
 *
 *  @param ignoreInvalidDescendants If true, descendants that cannot be exported
 *      are silently ignored.
 *  @see [[http://www.scala-js.org/doc/export-to-javascript.html Export Scala.js APIs to JavaScript]]
 */
class JSExportDescendentClasses(ignoreInvalidDescendants: Boolean)
    extends scala.annotation.StaticAnnotation {
  /** Constructor that makes invalid descendants fail.
   *
   *  same as setting ingoreInvalidDescendants to false
   */
  def this() = this(false)
}
