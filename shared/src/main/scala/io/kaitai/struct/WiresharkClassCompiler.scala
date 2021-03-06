package io.kaitai.struct

import io.kaitai.struct.CompileLog.FileSuccess
import io.kaitai.struct.datatype.DataType._
import io.kaitai.struct.datatype._
import io.kaitai.struct.exprlang.Ast
import io.kaitai.struct.format.{AttrSpec, _}
import io.kaitai.struct.languages.WiresharkCompiler
import io.kaitai.struct.languages.components.{ExtraAttrs, LanguageCompiler, LanguageCompilerStatic}

class WiresharkClassCompiler(
  classSpecs: ClassSpecs,
  override val topClass: ClassSpec,
  config: RuntimeConfig
) extends ClassCompiler(classSpecs, topClass, config, WiresharkCompiler) {

  override def compile: CompileLog.SpecSuccess = {
    lang.fileHeader(topClassName.head)
    lang.asInstanceOf[WiresharkCompiler].defineProtocol(topClassName.head)
    compileOpaqueClasses(topClass)
    compileClassHeadersRecursively(topClass)
    lang.asInstanceOf[WiresharkCompiler].setParserRoot(topClassName)
    compileWiresharkEnumsRecursively(topClass)
    compileWiresharkTypesRecursively(topClass)
    compileClass(topClass)
    lang.fileFooter(topClassName.head)

    CompileLog.SpecSuccess(
      lang.type2class(topClassName.head),
      lang.results(topClass).map { case (fileName, contents) => FileSuccess(fileName, contents) }.toList
    )
  }

  override def compileClass(curClass: ClassSpec): Unit = {
    provider.nowClass = curClass

    curClass.meta.imports.foreach(file => lang.importFile(file))

    // Forward declarations for recursive types
    curClass.types.foreach { case (typeName, _) => lang.classForwardDeclaration(List(typeName)) }

    // Forward declarations for params which reference types external to this type
    curClass.params.foreach((paramDefSpec) =>
      paramDefSpec.dataType match {
        case ut: UserType =>
          val externalTypeName = ut.classSpec.get.name
          if (externalTypeName.head != curClass.name.head) {
            lang.classForwardDeclaration(externalTypeName)
          }
        case _ => // no forward declarations needed
      }
    )

    if (lang.innerEnums)
      compileEnums(curClass)

    if (lang.config.readStoresPos)
      lang.debugClassSequence(curClass.seq)

    // Constructor
    compileConstructor(curClass)

    // Read method(s)
    compileEagerRead(curClass.seq, curClass.meta.endian)

    // Apply method(s)
    compileApply(curClass)

    // Destructor
    compileDestructor(curClass)

    // Recursive types
    if (lang.innerClasses) {
      compileSubclasses(curClass)

      provider.nowClass = curClass
    }

    compileInstances(curClass)

    // Attributes declarations and readers
    val allAttrs: List[MemberSpec] =
      curClass.seq ++
      curClass.params ++
      List(
        AttrSpec(List(), RootIdentifier, CalcUserType(topClassName, None)),
        AttrSpec(List(), ParentIdentifier, curClass.parentType)
      ) ++
      ExtraAttrs.forClassSpec(curClass, lang)
    compileAttrDeclarations(allAttrs)
    compileAttrReaders(allAttrs)

    curClass.toStringExpr.foreach(expr => lang.classToString(expr))

    lang.classFooter(curClass.name)

    if (!lang.innerClasses)
      compileSubclasses(curClass)

    if (!lang.innerEnums)
      compileEnums(curClass)
  }

  override def compileSubclasses(curClass: ClassSpec): Unit =
    curClass.types.foreach { case (_, intClass) => compileClass(intClass) }

  def compileClassHeadersRecursively(curClass: ClassSpec): Unit = {
    lang.classHeader(curClass.name)
    curClass.types.foreach { case (_, intClass) => compileClassHeadersRecursively(intClass) }
  }

  def compileWiresharkEnumsRecursively(curClass: ClassSpec): Unit = {
    compileWiresharkEnums(curClass)
    curClass.types.foreach { case (_, intClass) => compileWiresharkEnumsRecursively(intClass) }
  }

  def compileWiresharkEnums(curClass: ClassSpec): Unit =
    curClass.enums.foreach { case(_, enumColl) => compileWiresharkEnum(curClass, enumColl) }

  def compileWiresharkEnum(curClass: ClassSpec, enumColl: EnumSpec): Unit =
    lang.asInstanceOf[WiresharkCompiler].enumWiresharkDeclaration(curClass.name, enumColl.name.last, enumColl.sortedSeq)

  def compileWiresharkTypesRecursively(curClass: ClassSpec): Unit = {
    lang.asInstanceOf[WiresharkCompiler].wiresharkTypesHeader()
    compileWiresharkTypesRecursivelyInner(curClass)
    lang.asInstanceOf[WiresharkCompiler].wiresharkTypesFooter()
  }

  def compileWiresharkTypesRecursivelyInner(curClass: ClassSpec): Unit = {
    compileWiresharkTypes(curClass)
    curClass.types.foreach { case (_, intClass) => compileWiresharkTypesRecursivelyInner(intClass) }
  }

  def compileWiresharkTypes(curClass: ClassSpec): Unit =
    curClass.seq.foreach { (attr) => compileWiresharkType(curClass, attr) }
  
  def compileWiresharkType(curClass: ClassSpec, attr: AttrLikeSpec): Unit =
    lang.asInstanceOf[WiresharkCompiler].attrWiresharkParse(curClass, attr)

  def compileApply(curClass: ClassSpec): Unit = {
    compileApplyProc(curClass)
  }

  def compileApplyProc(curClass: ClassSpec) = {
    lang.asInstanceOf[WiresharkCompiler].applyHeader(curClass.seq.isEmpty, curClass.name.last)
    compileApplySeq(curClass)
    lang.asInstanceOf[WiresharkCompiler].applyFooter()
  }

  def compileApplySeq(curClass: ClassSpec) = {
    curClass.seq.foreach { (attr) =>
      lang.asInstanceOf[WiresharkCompiler].attrApplyParse(curClass, attr)
    }
  }
}
