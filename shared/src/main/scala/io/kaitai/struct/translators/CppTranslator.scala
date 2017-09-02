package io.kaitai.struct.translators

import java.nio.charset.Charset

import io.kaitai.struct.{ImportList, Utils}
import io.kaitai.struct.exprlang.Ast
import io.kaitai.struct.exprlang.Ast.expr
import io.kaitai.struct.datatype.DataType
import io.kaitai.struct.datatype.DataType._
import io.kaitai.struct.format.Identifier
import io.kaitai.struct.languages.CppCompiler

class CppTranslator(provider: TypeProvider, importListSrc: ImportList) extends BaseTranslator(provider) {
  val CHARSET_UTF8 = Charset.forName("UTF-8")

  /**
    * Handles string literal for C++ by wrapping a C `const char*`-style string
    * into a std::string constructor. Note that normally std::string
    * constructor treats given string in C manner, i.e. as zero-terminated
    * (and it is indeed would be generated by compiler as zero-terminated const
    * in .rodata segment). However, this is bad for string literals that contain
    * zero inside them: they would be cut abruptly at that zero. So, for string
    * literals that contain zero inside them, we use another constructor, which
    * allows explicit byte size argument.
    *
    * @param s string to present as C++ string literal
    * @return string as C++ string literal
    */
  override def doStringLiteral(s: String): String = {
    val lenSuffix = if (s.contains("\0")) {
      ", " + s.getBytes(CHARSET_UTF8).length
    } else {
      ""
    }
    s"std::string(${super.doStringLiteral(s)}$lenSuffix)"
  }

  /**
    * http://en.cppreference.com/w/cpp/language/escape
    */
  override val asciiCharQuoteMap: Map[Char, String] = Map(
    '\t' -> "\\t",
    '\n' -> "\\n",
    '\r' -> "\\r",
    '"' -> "\\\"",
    '\\' -> "\\\\",

    '\7' -> "\\a",
    '\f' -> "\\f",
    '\13' -> "\\v",
    '\b' -> "\\b"
  )

  override def doArrayLiteral(t: DataType, values: Seq[expr]): String =
    throw new RuntimeException("C++ literal arrays are not implemented yet")

  override def doByteArrayLiteral(arr: Seq[Byte]): String =
    "std::string(\"" + Utils.hexEscapeByteArray(arr) + "\", " + arr.length + ")"

  override def numericBinOp(left: Ast.expr, op: Ast.operator, right: Ast.expr) = {
    (detectType(left), detectType(right), op) match {
      case (_: IntType, _: IntType, Ast.operator.Mod) =>
        s"${CppCompiler.kstreamName}::mod(${translate(left)}, ${translate(right)})"
      case _ =>
        super.numericBinOp(left, op, right)
    }
  }

  override def anyField(value: expr, attrName: String): String =
    s"${translate(value)}->${doName(attrName)}"

  override def doName(s: String) = s match {
    case Identifier.ITERATOR => "_"
    case Identifier.ITERATOR2 => "_buf"
    case Identifier.INDEX => "i"
    case _ => s"$s()"
  }

  override def doEnumByLabel(enumType: List[String], label: String): String =
    (enumType.last + "_" + label).toUpperCase
  override def doEnumById(enumType: List[String], id: String): String =
    s"static_cast<${CppCompiler.types2class(enumType)}>($id)"

  override def doStrCompareOp(left: Ast.expr, op: Ast.cmpop, right: Ast.expr) = {
    if (op == Ast.cmpop.Eq) {
      s"${translate(left)} == (${translate(right)})"
    } else if (op == Ast.cmpop.NotEq) {
      s"${translate(left)} != ${translate(right)}"
    } else {
      s"(${translate(left)}.compare(${translate(right)}) ${cmpOp(op)} 0)"
    }
  }

  override def doSubscript(container: expr, idx: expr): String =
    s"${translate(container)}->at(${translate(idx)})"
  override def doIfExp(condition: expr, ifTrue: expr, ifFalse: expr): String =
    s"((${translate(condition)}) ? (${translate(ifTrue)}) : (${translate(ifFalse)}))"
  override def doCast(value: Ast.expr, typeName: String): String =
    s"static_cast<${CppCompiler.types2class(List(typeName))}*>(${translate(value)})"

  // Predefined methods of various types
  override def strToInt(s: expr, base: expr): String = {
    val baseStr = translate(base)
    s"std::stoi(${translate(s)}" + (baseStr match {
      case "10" => ""
      case _ => s", 0, $baseStr"
    }) + ")"
  }
  override def enumToInt(v: expr, et: EnumType): String =
    translate(v)
  override def boolToInt(v: expr): String =
    s"((${translate(v)})?1:0)"
  override def floatToInt(v: expr): String =
    s"static_cast<int>(${translate(v)})"
  override def intToStr(i: expr, base: expr): String = {
    val baseStr = translate(base)
    baseStr match {
      case "10" =>
        // FIXME: proper way for C++11, but not available in earlier versions
        //s"std::to_string(${translate(i)})"
        s"${CppCompiler.kstreamName}::to_string(${translate(i)})"
      case _ => throw new UnsupportedOperationException(baseStr)
    }
  }
  override def bytesToStr(bytesExpr: String, encoding: Ast.expr): String =
    s"${CppCompiler.kstreamName}::bytes_to_str($bytesExpr, ${translate(encoding)})"
  override def strLength(s: expr): String =
    s"${translate(s)}.length()"
  override def strReverse(s: expr): String =
    s"${CppCompiler.kstreamName}::reverse(${translate(s)})"
  override def strSubstring(s: expr, from: expr, to: expr): String =
    s"${translate(s)}.substr(${translate(from)}, (${translate(to)}) - (${translate(from)}))"

  override def arrayFirst(a: expr): String =
    s"${translate(a)}->front()"
  override def arrayLast(a: expr): String =
    s"${translate(a)}->back()"
  override def arraySize(a: expr): String =
    s"${translate(a)}->size()"
  override def arrayMin(a: expr): String = {
    importListSrc.add("algorithm")
    val v = translate(a)
    s"*std::min_element($v->begin(), $v->end())"
  }
  override def arrayMax(a: expr): String = {
    importListSrc.add("algorithm")
    val v = translate(a)
    s"*std::max_element($v->begin(), $v->end())"
  }
}
