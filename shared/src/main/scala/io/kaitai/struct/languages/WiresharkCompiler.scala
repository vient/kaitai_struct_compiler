package io.kaitai.struct.languages

import io.kaitai.struct.{ClassTypeProvider, RuntimeConfig, Utils}
import io.kaitai.struct.datatype.{DataType, KSError, ValidationNotEqualError, NeedRaw}
import io.kaitai.struct.datatype.{CalcEndian, LittleEndian, BigEndian, FixedEndian, InheritedEndian}
import io.kaitai.struct.datatype.Endianness
import io.kaitai.struct.datatype.DataType._
import io.kaitai.struct.exprlang.Ast
import io.kaitai.struct.format._
import io.kaitai.struct.languages.components._
import io.kaitai.struct.translators.WiresharkTranslator

class WiresharkCompiler(typeProvider: ClassTypeProvider, config: RuntimeConfig)
  extends LanguageCompiler(typeProvider, config)
    with AllocateIOLocalVar
    with EveryReadIsExpression
    with FixedContentsUsingArrayByteLiteral
    with ObjectOrientedLanguage
    with SingleOutputFile
    with UniversalDoc
    with UniversalFooter
    with SwitchIfOps
    with UpperCamelCaseClasses {

  import WiresharkCompiler._

  override val translator = new WiresharkTranslator(typeProvider, importList)

  override def innerClasses = false
  override def innerEnums = true

  override def indent: String = "  "
  override def outFileName(topClassName: String): String = s"${topClassName}_dissector.lua"
  override def outImports(topClass: ClassSpec) =
    importList.toList.mkString("", "\n", "\n")

  override def opaqueClassDeclaration(classSpec: ClassSpec): Unit =
    out.puts("require(\"" + classSpec.name.head + "\")")

  override def fileHeader(topClassName: String): Unit = {
    outHeader.puts(s"-- $headerComment")
    outHeader.puts("--")
    outHeader.puts("-- This file is compatible with Lua 5.3")
    outHeader.puts

    importList.add("local class = require(\"class\")")
    importList.add("local stringstream = require(\"string_stream\")")
    importList.add("require(\"kaitaistruct\")")

    out.puts
  }

  override def universalFooter: Unit =
    out.puts

  override def universalDoc(doc: DocSpec): Unit = {}

  override def classHeader(name: List[String]): Unit = {
    out.puts(s"${types2class(name)} = class.class()")
    out.puts
  }
  override def classFooter(name: List[String]): Unit =
    universalFooter
  override def classConstructorHeader(name: List[String], parentType: DataType, rootClassName: List[String], isHybrid: Boolean, params: List[ParamDefSpec]): Unit = {
    val endianAdd = if (isHybrid) ", is_le" else ""
    val paramsList = Utils.join(params.map((p) => paramName(p.id)), "", ", ", ", ")

    out.puts(s"function ${types2class(name)}:_init($paramsList" + s"io, parent, root$endianAdd)")
    out.inc
    out.puts("self._tvb = io._io._buf")
    out.puts("self._io = io")
    out.puts("self._parent = parent")
    out.puts("self._root = root or self")
    if (isHybrid)
      out.puts("self._is_le = is_le")

    // Store parameters passed to us
    params.foreach((p) => handleAssignmentSimple(p.id, paramName(p.id)))
  }
  override def classConstructorFooter: Unit = {
    out.dec
    out.puts("end")
    out.puts
  }

  override def runRead(name: List[String]): Unit =
    out.puts("self:_read()")
  override def runReadCalc(): Unit = {
    out.puts
    out.puts(s"if self._is_le then")
    out.inc
    out.puts("self:_read_le()")
    out.dec
    out.puts(s"elseif not self._is_le then")
    out.inc
    out.puts("self:_read_be()")
    out.dec
    out.puts("else")
    out.inc
    out.puts("error(\"unable to decide endianness\")")
    out.dec
    out.puts("end")
  }
  override def readHeader(endian: Option[FixedEndian], isEmpty: Boolean): Unit = {
    val suffix = endian match {
      case Some(e) => s"_${e.toSuffix}"
      case None => ""
    }

    out.puts(s"function ${types2class(typeProvider.nowClass.name)}:_read$suffix()")
    out.inc
  }
  override def readFooter(): Unit = {
    out.dec
    out.puts("end")
    out.puts
  }

  override def attributeDeclaration(attrName: Identifier, attrType: DataType, isNullable: Boolean): Unit =
    {}
  override def attributeReader(attrName: Identifier, attrType: DataType, isNullable: Boolean): Unit =
    {}

  override def attrParseHybrid(leProc: () => Unit, beProc: () => Unit): Unit = {
    out.puts("if self._is_le then")
    out.inc
    leProc()
    out.dec
    out.puts("else")
    out.inc
    beProc()
    out.dec
    out.puts("end")
  }

  override def attrFixedContentsParse(attrName: Identifier, contents: String): Unit =
    out.puts(s"${privateMemberName(attrName)} = self._io:ensure_fixed_contents($contents)")

  override def condIfHeader(expr: Ast.expr): Unit = {
    out.puts(s"if ${expression(expr)} then")
    out.inc
  }
  override def condIfFooter(expr: Ast.expr): Unit = {
    out.dec
    out.puts("end")
  }

  override def condRepeatEosHeader(id: Identifier, io: String, dataType: DataType, needRaw: NeedRaw): Unit = {
    assert(needRaw.level < 1, "condRepeatEosHeader: TODO: raw levels are not supported (and not understood)")
    if (needRaw.level >= 1)
      out.puts(s"${privateMemberName(RawIdentifier(id))} = {}")
    if (needRaw.level >= 2)
      out.puts(s"${privateMemberName(RawIdentifier(RawIdentifier(id)))} = {}")
    out.puts(s"${privateMemberNameTvbrange(id)}, ${privateMemberName(id)} = {}, {}")
    out.puts("local i = 0")
    out.puts(s"while not $io:is_eof() do")
    out.inc
  }
  override def condRepeatEosFooter: Unit = {
    out.puts("i = i + 1")
    out.dec
    out.puts("end")
  }

  override def condRepeatExprHeader(id: Identifier, io: String, dataType: DataType, needRaw: NeedRaw, repeatExpr: Ast.expr): Unit = {
    // assert(needRaw.level < 1, "condRepeatExprHeader: TODO: raw levels are not supported (and not understood)")
    if (needRaw.level >= 1)
      out.puts(s"${privateMemberName(RawIdentifier(id))} = {}")
    if (needRaw.level >= 2)
      out.puts(s"${privateMemberName(RawIdentifier(RawIdentifier(id)))} = {}")
    out.puts(s"${privateMemberNameTvbrange(id)}, ${privateMemberName(id)} = {}, {}")
    out.puts(s"for i = 0, ${expression(repeatExpr)} - 1 do")
    out.inc
  }
  override def condRepeatExprFooter: Unit = {
    out.dec
    out.puts("end")
  }

  override def condRepeatUntilHeader(id: Identifier, io: String, datatype: DataType, needRaw: NeedRaw, repeatExpr: Ast.expr): Unit = {
    assert(needRaw.level < 1, "condRepeatUntilHeader: TODO: raw levels are not supported (and not understood)")
    if (needRaw.level >= 1)
      out.puts(s"${privateMemberName(RawIdentifier(id))} = {}")
    if (needRaw.level >= 2)
      out.puts(s"${privateMemberName(RawIdentifier(RawIdentifier(id)))} = {}")
    out.puts(s"${privateMemberNameTvbrange(id)}, ${privateMemberName(id)} = {}, {}")
    out.puts("local i = 0")
    out.puts("while true do")
    out.inc
  }
  override def condRepeatUntilFooter(id: Identifier, io: String, dataType: DataType, needRaw: NeedRaw, untilExpr: Ast.expr): Unit = {
    typeProvider._currentIteratorType = Some(dataType)
    out.puts(s"if ${expression(untilExpr)} then")
    out.inc
    out.puts("break")
    out.dec
    out.puts("end")
    out.puts("i = i + 1")
    out.dec
    out.puts("end")
    out.dec
  }

  override def attrProcess(proc: ProcessExpr, varSrc: Identifier, varDest: Identifier, rep: RepeatSpec): Unit = {
    val srcExpr = getRawIdExpr(varSrc, rep)

    val expr = proc match {
      case ProcessXor(xorValue) =>
        val procName = translator.detectType(xorValue) match {
          case _: IntType => "process_xor_one"
          case _: BytesType => "process_xor_many"
        }
        s"$kstreamName.$procName($srcExpr, ${expression(xorValue)})"
      case ProcessZlib =>
        throw new RuntimeException("Lua zlib not supported")
      case ProcessRotate(isLeft, rotValue) =>
        val expr = if (isLeft) {
          expression(rotValue)
        } else {
          s"8 - (${expression(rotValue)})"
        }
        s"$kstreamName.process_rotate_left($srcExpr, $expr, 1)"
      case ProcessCustom(name, args) =>
        val procName = s"_process_${idToStr(varSrc)}"

        importList.add("require(\"" + s"${name.last}" + "\")")

        out.puts(s"local $procName = ${types2class(name)}(${args.map(expression).mkString(", ")})")
        s"$procName:decode($srcExpr)"
    }
    handleAssignment(varDest, expr, rep, false)
  }

  def getRawIdExpr(varName: Identifier, rep: RepeatSpec): String = {
    val memberName = privateMemberName(varName)
    rep match {
      case NoRepeat => memberName
      case RepeatExpr(_) => s"$memberName[i + 1]"
      case _ => s"$memberName[#$memberName]"
    }
  }

  override def useIO(ioEx: Ast.expr): String = {
    out.puts(s"local _io = ${expression(ioEx)}")
    "_io"
  }
  override def pushPos(io:String): Unit =
    out.puts(s"local _pos = $io:pos()")
  override def seek(io: String, pos: Ast.expr): Unit =
    out.puts(s"$io:seek(${expression(pos)})")
  override def popPos(io: String): Unit =
    out.puts(s"$io:seek(_pos)")
  override def alignToByte(io: String): Unit =
    out.puts(s"$io:align_to_byte()")

  override def instanceHeader(className: List[String], instName: InstanceIdentifier, dataType: DataType, isNullable: Boolean): Unit = {
    out.puts(s"${types2class(className)}.property.${publicMemberName(instName)} = {}")
    out.puts(s"function ${types2class(className)}.property.${publicMemberName(instName)}:get()")
    out.inc
  }
  override def instanceFooter: Unit = {
    out.dec
    out.puts("end")
    out.puts
  }
  override def instanceCheckCacheAndReturn(instName: InstanceIdentifier, dataType: DataType): Unit = {
    out.puts(s"if self.${idToStr(instName)} ~= nil then")
    out.inc
    instanceReturn(instName, dataType)
    out.dec
    out.puts("end")
    out.puts
  }
  override def instanceReturn(instName: InstanceIdentifier, attrType: DataType): Unit =
    out.puts(s"return ${privateMemberName(instName)}")

  override def enumDeclaration(curClass: List[String], enumName: String, enumColl: Seq[(Long, EnumValueSpec)]): Unit = {
    importList.add("local enum = require(\"enum\")")

    out.puts(s"${types2class(curClass)}.${type2class(enumName)} = enum.Enum {")
    out.inc
    enumColl.foreach { case (id, label) => out.puts(s"${label.name} = $id,") }
    out.dec
    out.puts("}")
    out.puts
  }

  def enumWiresharkDeclaration(curClass: List[String], enumName: String, enumColl: Seq[(Long, EnumValueSpec)]): Unit = {
    out.puts(s"${types2class(curClass)}.${type2class(enumName)}__ws_proto = {")
    out.inc
    enumColl.foreach { case (id, label) => out.puts(s"[$id] = '${label.name.toUpperCase()}',") }
    out.dec
    out.puts("}")
    out.puts
  }

  override def idToStr(id: Identifier): String = id match {
    case SpecialIdentifier(name) => name
    case NamedIdentifier(name) => name
    case NumberedIdentifier(idx) => s"_${NumberedIdentifier.TEMPLATE}$idx"
    case InstanceIdentifier(name) => s"_m_$name"
    case RawIdentifier(innerId) => s"_raw_${idToStr(innerId)}"
  }
  override def privateMemberName(id: Identifier): String =
    s"self.${idToStr(id)}"
  override def publicMemberName(id: Identifier): String = id match {
    case SpecialIdentifier(name) => name
    case NamedIdentifier(name) => name
    case InstanceIdentifier(name) => name
    case RawIdentifier(innerId) => s"_raw_${publicMemberName(innerId)}"
  }
  override def localTemporaryName(id: Identifier): String =
    s"_t_${idToStr(id)}"

  override def handleAssignmentRepeatEos(id: Identifier, expr: String): Unit =
    out.puts(s"${privateMemberName(id)}[i + 1] = $expr")
  override def handleAssignmentRepeatExpr(id: Identifier, expr: String): Unit =
    out.puts(s"${privateMemberName(id)}[i + 1] = $expr")
  override def handleAssignmentRepeatUntil(id: Identifier, expr: String, isRaw: Boolean): Unit = {
    val tmpName = translator.doName(if (isRaw) Identifier.ITERATOR2 else Identifier.ITERATOR)
    out.puts(s"$tmpName = $expr")
    out.puts(s"${privateMemberName(id)}[i + 1] = $tmpName")
  }
  override def handleAssignmentSimple(id: Identifier, expr: String): Unit =
    out.puts(s"${privateMemberName(id)} = $expr")
  
  def handleAssignmentDumb(id: Identifier, expr: String): Unit =
    out.puts(s"${idToStr(id)} = $expr")

  def handleAssignmentRepeatEosTvbrange(id: Identifier, expr: String): Unit =
    out.puts(s"${privateMemberNameTvbrange(id)}[i + 1], ${privateMemberName(id)}[i + 1] = $expr")
  def handleAssignmentRepeatExprTvbrange(id: Identifier, expr: String): Unit =
    out.puts(s"${privateMemberNameTvbrange(id)}[i + 1], ${privateMemberName(id)}[i + 1] = $expr")
  def handleAssignmentRepeatUntilTvbrange(id: Identifier, expr: String, isRaw: Boolean): Unit = {
    val tmpName = translator.doName(if (isRaw) Identifier.ITERATOR2 else Identifier.ITERATOR)
    out.puts(s"${tmpName}__tvbrange, $tmpName = $expr")
    out.puts(s"${privateMemberNameTvbrange(id)}[i + 1], ${privateMemberName(id)}[i + 1] = ${tmpName}__tvbrange, $tmpName")
  }
  def handleAssignmentSimpleTvbrange(id: Identifier, expr: String): Unit =
    out.puts(s"${privateMemberNameTvbrange(id)}, ${privateMemberName(id)} = $expr")

  def handleAssignmentTvbrange(id: Identifier, expr: String, rep: RepeatSpec, isRaw: Boolean): Unit = {
    rep match {
      case RepeatEos => handleAssignmentRepeatEosTvbrange(id, expr)
      case RepeatExpr(_) => handleAssignmentRepeatExprTvbrange(id, expr)
      case RepeatUntil(_) => handleAssignmentRepeatUntilTvbrange(id, expr, isRaw)
      case NoRepeat => handleAssignmentSimpleTvbrange(id, expr)
    }
  }

  override def parseExpr(dataType: DataType, assignType: DataType, io: String, defEndian: Option[FixedEndian]): String = dataType match {
    case tvb: TvbLimitType =>
      s"$io:read(${expression(tvb.size)})"
    case t: ReadableType =>
      s"$io:read_${t.apiCall(defEndian)}()"
    case blt: BytesLimitType =>
      s"$io:read_bytes(${expression(blt.size)})"
    case _: BytesEosType =>
      s"$io:read_bytes_full()"
    case BytesTerminatedType(terminator, include, consume, eosError, _) =>
      s"$io:read_bytes_term($terminator, $include, $consume, $eosError)"
    case BitsType1(bitEndian) =>
      s"$io:read_bits_int_${bitEndian.toSuffix}(1)"
    case BitsType(width: Int, bitEndian) =>
      s"$io:read_bits_int_${bitEndian.toSuffix}($width)"
    case t: UserType =>
      val addParams = Utils.join(t.args.map((a) => translator.translate(a)), "", ", ", ", ")
      val addArgs = if (t.isOpaque) {
        ""
      } else {
        val parent = t.forcedParent match {
          case Some(fp) => translator.translate(fp)
          case None => "self"
        }
        val addEndian = t.classSpec.get.meta.endian match {
          case Some(InheritedEndian) => ", self._is_le"
          case _ => ""
        }
        s", $parent, self._root$addEndian"
      }
      s"${types2class(t.classSpec.get.name)}($addParams$io$addArgs)"
  }
  override def bytesPadTermExpr(expr0: String, padRight: Option[Int], terminator: Option[Int], include: Boolean): String = {
    val expr1 = padRight match {
      case Some(padByte) => s"$kstreamName.bytes_strip_right($padByte, $expr0)"
      case None => expr0
    }
    val expr2 = terminator match {
      case Some(term) => s"$kstreamName.bytes_terminate($term, $include, $expr1)"
      case None => expr1
    }
    expr2
  }

  override def userTypeDebugRead(id: String, dataType: DataType, assignType: DataType): Unit =
    out.puts(s"$id:_read()")

  override def switchStart(id: Identifier, on: Ast.expr): Unit = {}
  override def switchCaseStart(condition: Ast.expr): Unit = {}
  override def switchCaseEnd(): Unit = {}
  override def switchElseStart(): Unit = {}
  override def switchEnd(): Unit = {}

  override def switchRequiresIfs(onType: DataType): Boolean = true

  override def switchIfStart(id: Identifier, on: Ast.expr, onType: DataType): Unit =
    out.puts(s"local _on = ${expression(on)}")

  override def switchIfCaseFirstStart(condition: Ast.expr): Unit = {
    out.puts(s"if _on == ${expression(condition)} then")
    out.inc
  }

  override def switchIfCaseStart(condition: Ast.expr): Unit = {
    out.puts(s"elseif _on == ${expression(condition)} then")
    out.inc
  }

  override def switchIfCaseEnd(): Unit =
    out.dec

  override def switchIfElseStart(): Unit = {
    out.puts("else")
    out.inc
  }

  override def switchIfEnd(): Unit =
    out.puts("end")

  override def allocateIO(varName: Identifier, rep: RepeatSpec): String = {
    val varStr = privateMemberName(varName)

    val args = getRawIdExpr(varName, rep)

    importList.add("local stringstream = require(\"string_stream\")")
    out.puts(s"local _io = $kstreamName(stringstream($args:tvb()))")
    "_io"
  }

  override def ksErrorName(err: KSError): String = WiresharkCompiler.ksErrorName(err)

  override def attrValidateExpr(
    attrId: Identifier,
    attrType: DataType,
    checkExpr: Ast.expr,
    err: KSError,
    errArgs: List[Ast.expr]
  ): Unit = {
    val errArgsCode = errArgs.map(translator.translate)
    out.puts(s"if not(${translator.translate(checkExpr)}) then")
    out.inc
    val msg = err match {
      case _: ValidationNotEqualError => {
        val (expected, actual) = (
          errArgsCode.lift(0).getOrElse("[expected]"),
          errArgsCode.lift(1).getOrElse("[actual]")
        )
        s""""not equal, expected " ..  $expected .. ", but got " .. $actual"""
      }
      case _ => "\"" + ksErrorName(err) + "\""
    }
    out.puts(s"error($msg)")
    out.dec
    out.puts("end")
  }

  override def attrBytesTypeParse(
    id: Identifier,
    dataType: BytesType,
    io: String,
    rep: RepeatSpec,
    isRaw: Boolean
  ): Unit = {
    // use intermediate variable name, if we'll be doing post-processing
    val rawId = dataType.process match {
      case None => id
      case Some(_) => RawIdentifier(id)
    }

    val expr = parseExprBytes(dataType, io)
    handleAssignmentTvbrange(rawId, expr, rep, isRaw)

    // apply post-processing
    dataType.process.foreach((proc) => attrProcess(proc, rawId, id, rep))
  }

  override def attrUserTypeParse(id: Identifier, dataType: UserType, io: String, rep: RepeatSpec, defEndian: Option[FixedEndian], assignType: DataType): Unit = {
    val newIO = dataType match {
      case knownSizeType: UserTypeFromBytes =>
        // we have a fixed buffer, thus we shall create separate IO for it
        val rawId = RawIdentifier(id)
        val byteType = knownSizeType.bytes

        // attrParse2(rawId, byteType, io, rep, true, defEndian)
        byteType match {
          case BytesLimitType(size, _, _, _, _) =>
            attrParse2(rawId, DataType.TvbLimitType(size), io, rep, true, defEndian)
          case _ =>
            assert(false, "attrUserTypeParse: TODO: creating substreams without fixed size is not supported")
        }

        val extraType = rep match {
          case NoRepeat => byteType
          case _ => ArrayTypeInStream(byteType)
        }

        this match {
          case thisStore: AllocateAndStoreIO =>
            thisStore.allocateIO(rawId, rep)
          case thisLocal: AllocateIOLocalVar =>
            thisLocal.allocateIO(rawId, rep)
        }
      case _: UserTypeInstream =>
        // no fixed buffer, just use regular IO
        io
    }
    val expr = parseExpr(dataType, dataType, newIO, defEndian)
    if (config.autoRead) {
      handleAssignment(id, expr, rep, false)
    } else {
      // Disabled autoRead requires one to actually call `_read` method on constructed
      // user type, and this must be done as a separate statement - or else exception
      // handler would blast the whole structure, not only this element. This, in turn,
      // makes us assign constructed element to a temporary variable in case of arrays.
      rep match {
        case NoRepeat =>
          handleAssignmentSimple(id, expr)
          userTypeDebugRead(privateMemberName(id), dataType, assignType)
        case _ =>
          val tempVarName = localTemporaryName(id)
          handleAssignmentTempVar(dataType, tempVarName, expr)
          userTypeDebugRead(tempVarName, dataType, assignType)
          handleAssignment(id, tempVarName, rep, false)
      }
    }
  }

  override def attrParse2(
    id: Identifier,
    dataType: DataType,
    io: String,
    rep: RepeatSpec,
    isRaw: Boolean,
    defEndian: Option[FixedEndian],
    assignTypeOpt: Option[DataType] = None
  ): Unit = {
    val assignType = assignTypeOpt.getOrElse(dataType)

    if (config.readStoresPos && rep != NoRepeat)
      attrDebugStart(id, dataType, Some(io), rep)

    dataType match {
      case t: UserType =>
        attrUserTypeParse(id, t, io, rep, defEndian, assignType)
      case t: BytesType =>
        attrBytesTypeParse(id, t, io, rep, isRaw)
      case t: TvbType =>
        attrTvbTypeParse(id, t, io, rep, isRaw)
      case st: SwitchType =>
        val isNullable = rep == NoRepeat && (if (switchBytesOnlyAsRaw) {
          st.isNullableSwitchRaw
        } else {
          st.isNullable
        })
        attrSwitchTypeParse(id, st.on, st.cases, io, rep, defEndian, isNullable, st.combinedType)
      case t: StrFromBytesType =>
        val expr = translator.bytesToStr(parseExprBytes(t.bytes, io), Ast.expr.Str(t.encoding))
        handleAssignmentTvbrange(id, expr, rep, isRaw)
      case t: EnumType =>
        val expr = translator.doEnumById(t.enumSpec.get.name, parseExpr(t.basedOn, t.basedOn, io, defEndian))
        handleAssignmentTvbrange(id, expr, rep, isRaw)
      case _ =>
        val expr = parseExpr(dataType, assignType, io, defEndian)
        handleAssignmentTvbrange(id, expr, rep, isRaw)
    }

    if (config.readStoresPos && rep != NoRepeat)
      attrDebugEnd(id, dataType, io, rep)
  }

  def attrTvbTypeParse(
    id: Identifier,
    dataType: TvbType,
    io: String,
    rep: RepeatSpec,
    isRaw: Boolean
  ): Unit = {
    val expr = parseExpr(dataType, dataType, io, None)
    handleAssignment(id, expr, rep, isRaw)
  }

  def switchCasesToIndexMap(cases: Map[Ast.expr, DataType]): Map[DataType, Int] = {
    var idx = 0
    cases.map { case (_, resultDataType) =>
      idx = idx + 1
      resultDataType -> idx
    }
  }





  //  _____                                                     _        
  // |_   _|  _   _   _ __     ___   ___      ___    ___     __| |   ___ 
  //   | |   | | | | | '_ \   / _ \ / __|    / __|  / _ \   / _` |  / _ \
  //   | |   | |_| | | |_) | |  __/ \__ \   | (__  | (_) | | (_| | |  __/
  //   |_|    \__, | | .__/   \___| |___/    \___|  \___/   \__,_|  \___|
  //          |___/  |_|                                                 

  def wiresharkTypesHeader(): Unit = {
    out.puts("local proto_fields = {")
    out.inc
  }

  def readableWiresharkProto(datatype: ReadableType): String = datatype match {
    case t: Int1Type =>
      val prefix = if (t.signed) "" else "u"
      s"${prefix}int8"
    case t: IntMultiType =>
      val prefix = if (t.signed) "" else "u"
      val width = t.width.width * 8
      s"${prefix}int${width}"
    case t: FloatMultiType =>
      assert(false, "readableWiresharkProto: TODO: not implemented")
      ""
  }

  def attrWiresharkParse(
    curClass: ClassSpec,
    attr: AttrLikeSpec,
    dataType: Option[DataType] = None,
    postfix: String = ""
  ): Unit = {
    val wsAttrProtoName = NamedIdentifier(attr2ws_proto_name(curClass, attr) + postfix)
    val wsAttrPath = attr2ws_path(curClass, attr)
    val wsAttrName = idToStr(attr.id)
    val doc = attr.doc.summary match {
      case Some(s) => s
      case None => ""
    }
    val usingDataType: DataType = dataType match {
      case Some(t) => t
      case None => attr.dataType
    }
    usingDataType match {
      case rt: ReadableType =>
        val protoMethod = readableWiresharkProto(rt)
        handleAssignmentDumb(
          wsAttrProtoName,
          s"""ProtoField.${protoMethod}("${wsAttrPath}", "${wsAttrName}", base.DEC, nil, nil, "${doc}"),"""
        )
      case et: EnumType =>
        val protoMethod = readableWiresharkProto(et.basedOn.asInstanceOf[ReadableType])
        val wsEnumName = s"${types2class(curClass.name)}.${types2class(et.name)}__ws_proto"
        handleAssignmentDumb(
          wsAttrProtoName,
          s"""ProtoField.${protoMethod}("${wsAttrPath}", "${wsAttrName}", base.DEC, ${wsEnumName}, nil, "${doc}"),"""
        )
      case _: BytesType =>
        handleAssignmentDumb(
          wsAttrProtoName,
          s"""ProtoField.bytes("${wsAttrPath}", "${wsAttrName}", base.SPACE, "${doc}"),"""
        )
      case _: StrType =>
        handleAssignmentDumb(
          wsAttrProtoName,
          s"""ProtoField.string("${wsAttrPath}", "${wsAttrName}", base.UNICODE, "${doc}"),"""
        )
      case st: SwitchType =>
        val typeMap = switchCasesToIndexMap(st.cases)
        typeMap.foreach { case (dataType, idx) =>
          attrWiresharkParse(curClass, attr, Some(dataType), switchTypeProtoPostfix(idx))
        }
      case _ =>
        // assert(false, s"attrWiresharkParse: unsupported type ${attr.dataType}")
        // out.puts(s"attrWiresharkParse: unsupported type ${attr.dataType}")
        Unit
    }
  }

  def wiresharkTypesFooter(): Unit = {
    out.dec
    out.puts("}")
    out.puts("")
  }





  //     _                      _                                _        
  //    / \     _ __    _ __   | |  _   _      ___    ___     __| |   ___ 
  //   / _ \   | '_ \  | '_ \  | | | | | |    / __|  / _ \   / _` |  / _ \
  //  / ___ \  | |_) | | |_) | | | | |_| |   | (__  | (_) | | (_| | |  __/
  // /_/   \_\ | .__/  | .__/  |_|  \__, |    \___|  \___/   \__,_|  \___|
  //           |_|     |_|          |___/                                 

  def runApply(name: List[String]): Unit =
    out.puts("self:_apply(tree)")
  def runApplyCalc(): Unit = {
    out.puts
    out.puts(s"if self._is_le then")
    out.inc
    out.puts("self:_apply_le(tree)")
    out.dec
    out.puts(s"elseif not self._is_le then")
    out.inc
    out.puts("self:_apply_be(tree)")
    out.dec
    out.puts("else")
    out.inc
    out.puts("error(\"unable to decide endianness\")")
    out.dec
    out.puts("end")
  }
  def applyHeader(endian: Option[FixedEndian], isEmpty: Boolean, name: String): Unit = {
    val suffix = endian match {
      case Some(e) => s"_${e.toSuffix}"
      case None => ""
    }

    out.puts(s"function ${types2class(typeProvider.nowClass.name)}:_apply$suffix(tree)")
    out.inc
    out.puts(s"""self._tree = tree:add(generic_kaitai_tcp_protocol, self._tvb, "${name}")""")
  }
  def applyFooter(): Unit = {
    out.puts("return self._io:pos()")
    out.dec
    out.puts("end")
    out.puts
  }

  def condRepeatHeaderApply(id: Identifier, needRaw: NeedRaw): Unit = {
    out.puts(s"for i = 0, #${privateMemberName(id)} - 1 do")  // until array end
    out.inc
  }
  def condRepeatFooterApply(): Unit = {
    out.dec
    out.puts("end")
  }

  def handleApplyRepeat(proto_id: Identifier, id: Identifier, postfix: String = ""): Unit =
    out.puts(s"self._tree:add(proto_fields.${idToStr(proto_id)}, ${privateMemberNameTvbrange(id)}[i + 1], ${privateMemberName(id)}[i + 1]${postfix})")
  def handleApplySimple(proto_id: Identifier, id: Identifier, postfix: String = ""): Unit =
    out.puts(s"self._tree:add(proto_fields.${idToStr(proto_id)}, ${privateMemberNameTvbrange(id)}, ${privateMemberName(id)}${postfix})")

  def handleApply(proto_id: Identifier, id: Identifier, rep: RepeatSpec, postfix: String = ""): Unit = {
    rep match {
      case NoRepeat => handleApplySimple(proto_id, id, postfix)
      case _ => handleApplyRepeat(proto_id, id, postfix)
    }
  }

  def attrApplyParse(curClass: ClassSpec, attr: AttrLikeSpec, defEndian: Option[Endianness]): Unit = {
    attrParseIfHeader(attr.id, attr.cond.ifExpr)
    defEndian match {
      case Some(_: CalcEndian) | Some(InheritedEndian) =>
        attrParseHybrid(
          () => attrApplyParse0(curClass, attr, Some(LittleEndian)),
          () => attrApplyParse0(curClass, attr, Some(BigEndian))
        )
      case None =>
        attrApplyParse0(curClass, attr, None)
      case Some(fe: FixedEndian) =>
        attrApplyParse0(curClass, attr, Some(fe))
    }
    attrParseIfFooter(attr.cond.ifExpr)
  }

  def attrApplyParse0(curClass: ClassSpec, attr: AttrLikeSpec, defEndian: Option[FixedEndian]): Unit = {
    attr.cond.repeat match {
      case NoRepeat =>
        attrApplyParse2(curClass, attr, defEndian)
      case _ =>
        condRepeatHeaderApply(attr.id, needRaw(attr.dataType))
        attrApplyParse2(curClass, attr, defEndian)
        condRepeatFooterApply()
    }
  }

  def attrApplyParse2(
    curClass: ClassSpec,
    attr: AttrLikeSpec,
    defEndian: Option[FixedEndian],
    dataType: Option[DataType] = None,
    postfix: String = ""
  ): Unit = {
    val id = attr.id
    val rep = attr.cond.repeat
    val wsAttrProtoName = NamedIdentifier(attr2ws_proto_name(curClass, attr) + postfix)
    val usingDataType: DataType = dataType match {
      case Some(t) => t
      case None => attr.dataType
    }

    usingDataType match {
      case t: UserType =>
        attrApplyUserTypeParse(attr)
      case t: BytesType =>
        handleApply(wsAttrProtoName, id, rep)
      case t: TvbType => Unit
      case st: SwitchType =>
        val isNullable = rep == NoRepeat && (if (switchBytesOnlyAsRaw) {
          st.isNullableSwitchRaw
        } else {
          st.isNullable
        })
        attrApplySwitchTypeParse(curClass, attr, st.on, st.cases, rep, defEndian, isNullable, st.combinedType)
      case t: StrFromBytesType => handleApply(wsAttrProtoName, id, rep)
      case t: EnumType => handleApply(wsAttrProtoName, id, rep, ".value")
      case _ => handleApply(wsAttrProtoName, id, rep)
    }
  }

  def attrApplyUserTypeParse(attr: AttrLikeSpec): Unit = {
    attr.cond.repeat match {
      case NoRepeat => out.puts(s"${privateMemberName(attr.id)}:_apply(self._tree)")
      case _ => out.puts(s"${privateMemberName(attr.id)}[i + 1]:_apply(self._tree)")
    }
  }

  def attrApplySwitchTypeParse(
    curClass: ClassSpec,
    attr: AttrLikeSpec,
    on: Ast.expr,
    cases: Map[Ast.expr, DataType],
    rep: RepeatSpec,
    defEndian: Option[FixedEndian],
    isNullable: Boolean,
    assignType: DataType
  ): Unit = {
    val id = attr.id
    val typeMap = switchCasesToIndexMap(cases)

    if (isNullable)
      condIfSetNull(id)

    switchCases[DataType](id, on, cases,
      (dataType) => {
        if (isNullable)
          condIfSetNonNull(id)
        attrApplyParse2(curClass, attr, defEndian, Some(dataType), switchTypeProtoPostfix(typeMap(dataType)))
      },
      (dataType) => attrApplyParse2(curClass, attr, defEndian, Some(dataType), switchTypeProtoPostfix(typeMap(dataType)))
    )
  }





  def type2ws_class(className: String) = s"_ws_${className}"

  def types2class(name: List[String]): String = name.map(x => type2class(x)).mkString(".")

  def types2ws_class(name: List[String]): String = name.mkString("__")
  
  def attr2ws_proto_name(curClass: ClassSpec, attr: AttrLikeSpec): String = 
    s"${types2ws_class(curClass.name)}__${idToStr(attr.id)}"

  def attr2ws_path(curClass: ClassSpec, attr: AttrLikeSpec): String = 
    s"${curClass.name.mkString(".")}.${idToStr(attr.id)}"
  
  def privateMemberNameTvbrange(s: Identifier): String = s"${privateMemberName(s)}__tvbrange"

  def switchTypeProtoPostfix(idx: Int): String = s"__case_${idx}"
}

object WiresharkCompiler extends LanguageCompilerStatic
    with UpperCamelCaseClasses
    with StreamStructNames
    with ExceptionNames {
  override def getCompiler(
    tp: ClassTypeProvider,
    config: RuntimeConfig
  ): LanguageCompiler = new WiresharkCompiler(tp, config)

  override def kstructName: String = "KaitaiStruct"
  override def kstreamName: String = "KaitaiStream"
  override def ksErrorName(err: KSError): String = err.name
}
