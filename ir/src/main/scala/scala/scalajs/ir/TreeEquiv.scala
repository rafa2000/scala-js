package scala.scalajs.ir

import scala.annotation.tailrec

import scala.math.Equiv

import Trees._

trait TreeEquiv extends Equiv[Tree] {
  def equiv(x: PropertyName, y: PropertyName): Boolean
}

object TreeEquiv {

  class StructTreeEquiv extends TreeEquiv {

    @inline
    @tailrec
    private final def equivList(x: List[Tree], y: List[Tree]): Boolean =
      if (x.isEmpty) y.isEmpty
      else y.nonEmpty && equiv(x.head, y.head) && equivList(x.tail, y.tail)

    @inline
    private final def equivOpt(x: Option[Ident], y: Option[Ident]) =
      x.isDefined == y.isDefined && (x.isEmpty || equiv(x.get, y.get))

    @inline
    @tailrec
    private final def equivSwitch(x: List[(Tree, Tree)],
        y: List[(Tree, Tree)]): Boolean = {
      if (x.isEmpty) y.isEmpty
      else y.nonEmpty && equiv(x.head._1, y.head._1) &&
      equiv(x.head._2, y.head._2) && equivSwitch(x.tail, y.tail)
    }

    @inline
    @tailrec
    private final def equivMatch(x: List[(List[Tree], Tree)],
        y: List[(List[Tree], Tree)]): Boolean = {
      if (x.isEmpty) y.isEmpty
      else y.nonEmpty && equivList(x.head._1, y.head._1) &&
      equiv(x.head._2, y.head._2) && equivMatch(x.tail, y.tail)
    }

    @inline
    @tailrec
    private final def equivObj(x: List[(PropertyName, Tree)],
        y: List[(PropertyName, Tree)]): Boolean = {
      if (x.isEmpty) y.isEmpty
      else y.nonEmpty && equiv(x.head._1, y.head._1) &&
      equiv(x.head._2, y.head._2) && equivObj(x.tail, y.tail)
    }

    @inline
    @tailrec
    private final def equivIdList(x: List[Ident], y: List[Ident]): Boolean = {
      if (x.isEmpty) y.isEmpty
      else y.nonEmpty && equiv(x.head, y.head) && equivIdList(x.tail, y.tail)
    }

    def equiv(x: Ident, y: Ident): Boolean =
      x.name == y.name && x.originalName == y.originalName

    def equiv(x: PropertyName, y: PropertyName): Boolean = x match {
      case x: Ident => y match {
        case y: Ident => equiv(x, y)
        case _ => false
      }

      case StringLiteral(x_value, x_originalName) => y match {
        case StringLiteral(y_value, y_originalName) =>
          x_value == y_value && x_originalName == y_originalName
        case _ => false
      }
    }

    def equiv(x: Tree, y: Tree): Boolean = x match {
      case EmptyTree => y == EmptyTree

      case DocComment(x_text) => y match {
        case DocComment(y_text) =>
          x_text == y_text
        case _ => false
      }

      case VarDef(x_name, x_vtpe, x_mutable, x_rhs) => y match {
        case VarDef(y_name, y_vtpe, y_mutable, y_rhs) =>
          equiv(x_name, y_name) && x_vtpe == y_vtpe &&
          x_mutable == y_mutable && equiv(x_rhs, y_rhs)
        case _ => false
      }

      case ParamDef(x_name, x_ptpe, x_mutable) => y match {
        case ParamDef(y_name, y_ptpe, y_mutable) =>
          equiv(x_name, y_name) && x_ptpe == y_ptpe && x_mutable == y_mutable
        case _ => false
      }

      case Skip() => y match {
        case Skip() => true
        case _ => false
      }

      case x: Block => y match {
        case y: Block => equivList(x.stats, y.stats)
        case _ => false
      }

      case Labeled(x_label, x_tpe, x_body) => y match {
        case Labeled(y_label, y_tpe, y_body) =>
          equiv(x_label, y_label) && x_tpe == y_tpe && equiv(x_body, y_body)
        case _ => false
      }

      case Assign(x_lhs, x_rhs) => y match {
        case Assign(y_lhs, y_rhs) => equiv(x_lhs, y_lhs) && equiv(x_rhs, y_rhs)
        case _ => false
      }

      case Return(x_expr, x_label) => y match {
        case Return(y_expr, y_label) =>
          equiv(x_expr, y_expr) && equivOpt(x_label, y_label)
        case _ => false
      }

      case If(x_cond, x_thenp, x_elsep) => y match {
        case If(y_cond, y_thenp, y_elsep) =>
          x.tpe == y.tpe && equiv(x_cond, y_cond) &&
          equiv(x_thenp, y_thenp) && equiv(x_elsep, y_elsep)
        case _ => false
      }

      case While(x_cond, x_body, x_label) => y match {
        case While(y_cond, y_body, y_label) =>
          equiv(x_cond, y_cond) && equiv(x_body, y_body) &&
          equivOpt(x_label, y_label)
        case _ => false
      }

      case DoWhile(x_body, x_cond, x_label) => y match {
        case DoWhile(y_body, y_cond, y_label) =>
          equiv(x_cond, y_cond) && equiv(x_body, y_body) &&
          equivOpt(x_label, y_label)
        case _ => false
      }

      case Try(x_block, x_errVar, x_handler, x_finalizer) => y match {
        case Try(y_block, y_errVar, y_handler, y_finalizer) =>
          x.tpe == y.tpe && equiv(x_block, y_block) &&
          equiv(x_errVar, y_errVar) && equiv(x_handler, y_handler) &&
          equiv(x_finalizer, y_finalizer)
        case _ => false
      }

      case Throw(x_expr) => y match {
        case Throw(y_expr) => equiv(x_expr, y_expr)
        case _ => false
      }

      case Break(x_label) => y match {
        case Break(y_label) => equivOpt(x_label, y_label)
        case _ => false
      }

      case Continue(x_label) => y match {
        case Continue(y_label) => equivOpt(x_label, y_label)
        case _ => false
      }

      case Switch(x_selector, x_cases, x_default) => y match {
        case Switch(y_selector, y_cases, y_default) =>
          equiv(x_selector, y_selector) && equiv(x_default, y_default) &&
          x_cases.size == y_cases.size && equivSwitch(x_cases, y_cases)
        case _ => false
      }

      case Match(x_selector, x_cases, x_default) => y match {
        case Match(y_selector, y_cases, y_default) =>
          x.tpe == y.tpe && equiv(x_selector, y_selector) &&
          equiv(x_default, y_default) && x_cases.size == y_cases.size &&
          equivMatch(x_cases, y_cases)
        case _ => false
      }

      case Debugger() => y match {
        case Debugger() => true
        case _ => false
      }

      case New(x_cls, x_ctor, x_args) => y match {
        case New(y_cls, y_ctor, y_args) =>
          x_cls == y_cls && equiv(x_ctor, y_ctor) && equivList(x_args, y_args)
        case _ => false
      }

      case LoadModule(x_cls) => y match {
        case LoadModule(y_cls) => x_cls == y_cls
        case _ => false
      }

      case StoreModule(x_cls, x_value) => y match {
        case StoreModule(y_cls, y_value) =>
          x_cls == y_cls && equiv(x_value, y_value)
        case _ => false
      }

      case Select(x_qualifier, x_item, x_mutable) => y match {
        case Select(y_qualifier, y_item, y_mutable) =>
          x.tpe == y.tpe && x_mutable == y_mutable &&
          equiv(x_qualifier, y_qualifier) && equiv(x_item, y_item)
        case _ => false
      }

      case Apply(x_receiver, x_method, x_args) => y match {
        case Apply(y_receiver, y_method, y_args) =>
          x.tpe == y.tpe && equiv(x_receiver, y_receiver) &&
          equiv(x_method, y_method) && equivList(x_args, y_args)
        case _ => false
      }

      case StaticApply(x_receiver, x_cls, x_method, x_args) => y match {
        case StaticApply(y_receiver, y_cls, y_method, y_args) =>
          x.tpe == y.tpe && x_cls == y_cls && equiv(x_receiver, y_receiver) &&
          equiv(x_method, y_method) && equivList(x_args, y_args)
        case _ => false
      }

      case TraitImplApply(x_impl, x_method, x_args) => y match {
        case TraitImplApply(y_impl, y_method, y_args) =>
          x.tpe == y.tpe && x_impl == y_impl && equiv(x_method, y_method) &&
          equivList(x_args, y_args)
        case _ => false
      }

      case UnaryOp(x_op, x_lhs) => y match {
        case UnaryOp(y_op, y_lhs) => x_op == y_op && equiv(x_lhs, y_lhs)
        case _ => false
      }

      case BinaryOp(x_op, x_lhs, x_rhs) => y match {
        case BinaryOp(y_op, y_lhs, y_rhs) =>
          x_op == y_op && equiv(x_lhs, y_lhs) && equiv(x_rhs, y_rhs)
        case _ => false
      }

      case NewArray(x_tpe, x_lengths) => y match {
        case NewArray(y_tpe, y_lengths) =>
          x_tpe == y_tpe && equivList(x_lengths, y_lengths)
        case _ => false
      }

      case ArrayValue(x_tpe, x_elems) => y match {
        case ArrayValue(y_tpe, y_elems) =>
          x_tpe == y_tpe && equivList(x_elems, y_elems)
        case _ => false
      }

      case ArrayLength(x_array) => y match {
        case ArrayLength(y_array) => equiv(x_array, y_array)
        case _ => false
      }

      case ArraySelect(x_array, x_index) => y match {
        case ArraySelect(y_array, y_index) =>
          x.tpe == y.tpe && equiv(x_array, y_array) && equiv(x_index, y_index)
        case _ => false
      }

      case RecordValue(x_tpe, x_elems) => y match {
        case RecordValue(y_tpe, y_elems) =>
          x_tpe == y_tpe && equivList(x_elems, y_elems)
        case _ => false
      }

      case IsInstanceOf(x_expr, x_cls) => y match {
        case IsInstanceOf(y_expr, y_cls) =>
          x_cls == y_cls && equiv(x_expr, y_expr)
        case _ => false
      }

      case AsInstanceOf(x_expr, x_cls) => y match {
        case AsInstanceOf(y_expr, y_cls) =>
          x_cls == y_cls && equiv(x_expr, y_expr)
        case _ => false
      }

      case ClassOf(x_cls) => y match {
        case ClassOf(y_cls) => x_cls == y_cls
        case _ => false
      }

      case CallHelper(x_helper, x_args) => y match {
        case CallHelper(y_helper, y_args) =>
          x_helper == y_helper && x.tpe == y.tpe && equivList(x_args, y_args)
        case _ => false
      }

      case JSGlobal() => y match {
        case JSGlobal() => true
        case _ => false
      }

      case JSNew(x_ctor, x_args) => y match {
        case JSNew(y_ctor, y_args) =>
          equiv(x_ctor, y_ctor) && equivList(x_args, y_args)
        case _ => false
      }

      case JSDotSelect(x_qualifier, x_item) => y match {
        case JSDotSelect(y_qualifier, y_item) =>
          equiv(x_qualifier, y_qualifier) && equiv(x_item, y_item)
        case _ => false
      }

      case JSBracketSelect(x_qualifier, x_item) => y match {
        case JSBracketSelect(y_qualifier, y_item) =>
          equiv(x_qualifier, y_qualifier) && equiv(x_item, y_item)
        case _ => false
      }

      case JSFunctionApply(x_fun, x_args) => y match {
        case JSFunctionApply(y_fun, y_args) =>
          equiv(x_fun, y_fun) && equivList(x_args, y_args)
        case _ => false
      }

      case JSDotMethodApply(x_receiver, x_method, x_args) => y match {
        case JSDotMethodApply(y_receiver, y_method, y_args) =>
          equiv(x_receiver, y_receiver) && equiv(x_method, y_method) &&
          equivList(x_args, y_args)
        case _ => false
      }

      case JSBracketMethodApply(x_receiver, x_method, x_args) => y match {
        case JSBracketMethodApply(y_receiver, y_method, y_args) =>
          equiv(x_receiver, y_receiver) && equiv(x_method, y_method) &&
          equivList(x_args, y_args)
        case _ => false
      }

      case JSApply(x_fun, x_args) => y match {
        case JSApply(y_fun, y_args) =>
          equiv(x_fun, y_fun) && equivList(x_args, y_args)
        case _ => false
      }

      case JSDelete(x_obj, x_prop) => y match {
        case JSDelete(y_obj, y_prop) =>
          equiv(x_obj, y_obj) && equiv(x_prop, y_prop)
        case _ => false
      }

      case JSUnaryOp(x_op, x_lhs) => y match {
        case JSUnaryOp(y_op, y_lhs) => x_op == y_op && equiv(x_lhs, y_lhs)
        case _ => false
      }

      case JSBinaryOp(x_op, x_lhs, x_rhs) => y match {
        case JSBinaryOp(y_op, y_lhs, y_rhs) =>
          x_op == y_op && equiv(x_lhs, y_lhs) && equiv(x_rhs, y_rhs)
        case _ => false
      }

      case JSArrayConstr(x_items) => y match {
        case JSArrayConstr(y_items) => equivList(x_items, y_items)
        case _ => false
      }

      case JSObjectConstr(x_fields) => y match {
        case JSObjectConstr(y_fields) =>
          x_fields.size == y_fields.size && equivObj(x_fields, y_fields)
        case _ => false
      }

      case Undefined() => y match {
        case Undefined() => true
        case _ => false
      }

      case UndefinedParam() => y match {
        case UndefinedParam() => true
        case _ => false
      }

      case Null() => y match {
        case Null() => true
        case _ => false
      }

      case BooleanLiteral(x_value) => y match {
        case BooleanLiteral(y_value) => x_value == y_value
        case _ => false
      }

      case IntLiteral(x_value) => y match {
        case IntLiteral(y_value) => x_value == y_value
        case _ => false
      }

      case DoubleLiteral(x_value) => y match {
        case DoubleLiteral(y_value) => x_value == y_value
        case _ => false
      }

      case StringLiteral(x_value, x_originalName) => y match {
        case StringLiteral(y_value, y_originalName) =>
          x_value == y_value && x_originalName == y_originalName
        case _ => false
      }

      case VarRef(x_ident, x_mutable) => y match {
        case VarRef(y_ident, y_mutable) =>
          x_mutable == y_mutable && x.tpe == y.tpe && equiv(x_ident, y_ident)
        case _ => false
      }

      case This() => y match {
        case This() => x.tpe == y.tpe
        case _ => false
      }

      case Closure(x_thisType, x_args, x_resultType, x_body, x_captures) => y match {
        case Closure(y_thisType, y_args, y_resultType, y_body, y_captures) =>
          x_thisType == y_thisType && x_resultType == y_resultType &&
          equivList(x_args, y_args) && equiv(x_body, y_body) &&
          equivList(x_captures, y_captures)
        case _ => false
      }

      case Function(x_thisType, x_args, x_resultType, x_body) => y match {
        case Function(y_thisType, y_args, y_resultType, y_body) =>
          x_thisType == y_thisType && x_resultType == y_resultType &&
          equivList(x_args, y_args) && equiv(x_body, y_body)
        case _ => false
      }

      case Cast(x_expr, x_tpe) => y match {
        case Cast(y_expr, y_tpe) => x_tpe == y_tpe && equiv(x_expr, y_expr)
        case _ => false
      }

      case ClassDef(x_name, x_kind, x_parent, x_ancestors, x_defs) => y match {
        case ClassDef(y_name, y_kind, y_parent, y_ancestors, y_defs) =>
          x_kind == y_kind && equiv(x_name, y_name) &&
          equivOpt(x_parent, y_parent) &&
          equivIdList(x_ancestors, y_ancestors) && equivList(x_defs, y_defs)
        case _ => false
      }

      case MethodDef(x_name, x_args, x_resultType, x_body) => y match {
        case MethodDef(y_name, y_args, y_resultType, y_body) =>
          x_resultType == y_resultType && equiv(x_name, y_name) &&
          equivList(x_args, y_args) && equiv(x_body, y_body)
        case _ => false
      }

      case PropertyDef(x_name, x_getterBody, x_setterArg, x_setterBody) => y match {
        case PropertyDef(y_name, y_getterBody, y_setterArg, y_setterBody) =>
          equiv(x_name, y_name) && equiv(x_getterBody, y_getterBody) &&
          equiv(x_setterArg, y_setterArg) && equiv(x_setterBody, y_setterBody)
        case _ => false
      }

      case ConstructorExportDef(x_name, x_args, x_body) => y match {
        case ConstructorExportDef(y_name, y_args, y_body) =>
          x_name == y_name && equivList(x_args, y_args) && equiv(x_body, y_body)
        case _ => false
      }

      case ModuleExportDef(x_fullName) => y match {
        case ModuleExportDef(y_fullName) => x_fullName == y_fullName
        case _ => false
      }

    }

  }

  object StructTreeEquiv extends StructTreeEquiv

  class PosStructTreeEquiv extends StructTreeEquiv {
    override def equiv(x: Ident, y: Ident): Boolean =
      x.pos == y.pos && super.equiv(x, y)

    override def equiv(x: PropertyName, y: PropertyName): Boolean =
      x.pos == y.pos && super.equiv(x, y)

    override def equiv(x: Tree, y: Tree): Boolean =
      x.pos == y.pos && super.equiv(x, y)
  }

  object PosStructTreeEquiv extends PosStructTreeEquiv

}
