# eztoml's laws. Each file under laws/ is one guarantee, its prose on top and
# its quantified laws under it; proofs/<name>.bend proves it. A law file that
# says pending proves part of its guarantee, not all of it. There are two
# families: conformance to TOML v1.0.0 and its toml.abnf, and the public
# interface in main.bend -- the defs parse, render, get, at, root, bad, string,
# digits, flag, str, integer, float, boolean, array, inline, table, pair, key,
# bare and wf, and the types Doc, Val, Hit, Sign, When, Date, Clock and Zone.
# Every other def in main.bend is internal and carries no promise.
#
# A document is well-formed when wf holds of it: the shapes parse returns.
# same is "the same TOML document": it ignores whether a string is owned or a
# span of the source and the order of a table's pairs, compares tables as maps
# and arrays in order, and compares neither the stored paths nor the error
# field; own reads every span into an owned string. A text is short when it is
# shorter than 2^32 characters: the scanner counts a plain string's characters
# in a U32, so a longer string would not read back, and the laws that go
# through parse are stated for short texts. same, own and short are under
# laws/defs/.
#
# The reasoning behind each guarantee is in docs/rfc/eztoml-spec.md. It
# names the guarantees by the requirement IDs of docs/SPEC.md, the table these
# files replaced.
import Base
import ./laws/AotHeaderExtendsArray.bend as AotHeaderExtendsArray
import ./laws/AotHeaderStartsArray.bend as AotHeaderStartsArray
import ./laws/AtWalksKeys.bend as AtWalksKeys
import ./laws/BareKey.bend as BareKey
import ./laws/BareWordReadsOn.bend as BareWordReadsOn
import ./laws/BareWordReadsOnInArray.bend as BareWordReadsOnInArray
import ./laws/BareWordRefused.bend as BareWordRefused
import ./laws/BareWordRefusedInArray.bend as BareWordRefusedInArray
import ./laws/BoolReadsBack.bend as BoolReadsBack
import ./laws/BoolWord.bend as BoolWord
import ./laws/BooleanIsBareWord.bend as BooleanIsBareWord
import ./laws/BooleanNotDateTime.bend as BooleanNotDateTime
import ./laws/BooleanNotFloat.bend as BooleanNotFloat
import ./laws/BooleanNotInteger.bend as BooleanNotInteger
import ./laws/BooleanParsesAsDenoted.bend as BooleanParsesAsDenoted
import ./laws/BooleanParsesAsDenotedInArray.bend as BooleanParsesAsDenotedInArray
import ./laws/BooleanParsesAsDenotedInInlineTable.bend as BooleanParsesAsDenotedInInlineTable
import ./laws/BooleanParsesExactly.bend as BooleanParsesExactly
import ./laws/BooleanWordExact.bend as BooleanWordExact
import ./laws/DateTimeReadExactly.bend as DateTimeReadExactly
import ./laws/DefinesEachTableOnce.bend as DefinesEachTableOnce
import ./laws/ErrorStays.bend as ErrorStays
import ./laws/FloReadsBack.bend as FloReadsBack
import ./laws/FloatNotDateTime.bend as FloatNotDateTime
import ./laws/FloatReadExactly.bend as FloatReadExactly
import ./laws/GLinesTextAppend.bend as GLinesTextAppend
import ./laws/GTextParts.bend as GTextParts
import ./laws/GValTextTail.bend as GValTextTail
import ./laws/GapIsWs.bend as GapIsWs
import ./laws/GetFindsFirstPair.bend as GetFindsFirstPair
import ./laws/HeaderDefinesImplicitTable.bend as HeaderDefinesImplicitTable
import ./laws/HeaderDefinesNewTable.bend as HeaderDefinesNewTable
import ./laws/HeaderQuoteAfterBareRefused.bend as HeaderQuoteAfterBareRefused
import ./laws/HeaderQuoteAtStartOpensSegment.bend as HeaderQuoteAtStartOpensSegment
import ./laws/HeadersParseAsReplay.bend as HeadersParseAsReplay
import ./laws/IntReadsBack.bend as IntReadsBack
import ./laws/IntegerNotDateTime.bend as IntegerNotDateTime
import ./laws/IntegerNotFloat.bend as IntegerNotFloat
import ./laws/IntegerReadExactly.bend as IntegerReadExactly
import ./laws/KeyNameIsItsCharacters.bend as KeyNameIsItsCharacters
import ./laws/KeyRendersAndReadsBack.bend as KeyRendersAndReadsBack
import ./laws/NumOneSign.bend as NumOneSign
import ./laws/NumSignedZeroUnderscore.bend as NumSignedZeroUnderscore
import ./laws/NumTwoSigns.bend as NumTwoSigns
import ./laws/NumZeroUnderscore.bend as NumZeroUnderscore
import ./laws/ParseRenderParse.bend as ParseRenderParse
import ./laws/ParsedIsWellFormed.bend as ParsedIsWellFormed
import ./laws/ParsesExactlyTheGrammar.bend as ParsesExactlyTheGrammar
import ./laws/PassValue.bend as PassValue
import ./laws/ReadersOfValues.bend as ReadersOfValues
import ./laws/RenderParseValuePair.bend as RenderParseValuePair
import ./laws/RenderThenParse.bend as RenderThenParse
import ./laws/SameOwn.bend as SameOwn
import ./laws/SameRefl.bend as SameRefl
import ./laws/SameSwap.bend as SameSwap
import ./laws/SameSym.bend as SameSym
import ./laws/ScalarReadsBack.bend as ScalarReadsBack
import ./laws/SealPutsNewestLast.bend as SealPutsNewestLast
import ./laws/StringReadsAsDenoted.bend as StringReadsAsDenoted
import ./laws/StringRenderEscapes.bend as StringRenderEscapes
import ./laws/TbOpenAfterSet.bend as TbOpenAfterSet
import ./laws/TbRowsAfterSet.bend as TbRowsAfterSet
import ./laws/TextReadsAsReplay.bend as TextReadsAsReplay
import ./laws/ValueReadsBack.bend as ValueReadsBack
import ./laws/WalkPutAtHead.bend as WalkPutAtHead
import ./laws/WhenReadsBack.bend as WhenReadsBack
import ./laws/WordReadsBack.bend as WordReadsBack
import ./laws/WordRefusedInDocument.bend as WordRefusedInDocument
import ./laws/WordSignedZeroUnderscore.bend as WordSignedZeroUnderscore
import ./laws/WordTwoSigns.bend as WordTwoSigns
import ./laws/WordZeroUnderscore.bend as WordZeroUnderscore
