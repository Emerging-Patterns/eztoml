# proofs of laws/KeyRendersAndReadsBack.bend
import Base
import ../main.bend as T
import ../src/eq.bend as Eq
import ../laws/KeyRendersAndReadsBack.bend as Laws
import ../laws/StringRenderEscapes.bend as L1
import ./lemmas/BareKeyValueScan.bend as M1
import ./lemmas/ControlEscapeText.bend as M2
import ./lemmas/FreshNamesInRows.bend as M3
import ./lemmas/QuotedKeySegments.bend as M4
import ./lemmas/ValueTextReadback.bend as M5

def Laws.key_is_bare_when_it_can(s, e):
  %e : {T.key.go(_, s) == s : String}
  {==}

def Laws.key_is_quoted_when_it_must(s, e):
  %e : {T.key.go(_, s) == T.key.basic(s) : String}
  {==}

# laws/KeyRendersAndReadsBack.bend's read-back. A quoted key is read in LKeyQ, one character of
# escs at a time: a plain character on the fast path, an escape through
# LKeyE, and a \u escape through LKeyU. After each character's escape the
# scanner is back in LKeyQ with that character pushed onto its buffer; only
# where an escape last returned it (back) differs, and nothing after the key
# reads that. A per-character step takes the rest of the walk as a function
# of back, so no lemma has to name it. The per-character lemmas are WP0's
# quoted-segment family (qs, below), taken at a key's state.

# a scanner inside the first quoted key of a document, its characters so far
# reversed in buf
def kq(back: T.Lex, buf: List<&2, Char>) -> T.St:
  T.St{"", [], [], [], [], buf, T.LKeyQ{}, back, T.QBasic{}, [], T.HNone{}, 0, 0,
    False{}, False{}}

# every character of a name, as escs writes it, then the closing quote and
# " = 1": the document is one pair named by the buffer, whatever the last
# escape left in back
def kq.body(
  +ss: String,
  +back: T.Lex,
  +buf: List<&2, Char>
) -> {T.doc.read(String.append(L1.escs(ss), "\" = 1"), T.MScan{kq(back, buf)})
  == M4.kq.doc(M3.rev.onto(ss, buf)) : T.Doc}:
  M4.qs.escs(ss, False{}, [], [], [], [], [], False{}, back, buf, "\" = 1",
    M4.kq.doc(M3.rev.onto(ss, buf)), _bk => {==})

# a quoted key: key.basic is quotes around escs, and the scanner reads them
def kq.quoted(
  +ss: String
) -> {T.parse(String.append(T.key.basic(ss), " = 1"))
  == T.Doc{"", [T.VPair{ss, T.VInt{T.Plus{}, "1"}}]} : T.Doc}:
  Equal.trans(T.Doc,
    T.parse(String.append(T.key.basic(ss), " = 1")),
    T.parse(String.append("\"" ++ L1.escs(ss) ++ "\"", " = 1")),
    T.Doc{"", [T.VPair{ss, T.VInt{T.Plus{}, "1"}}]},
    Equal.cong(String, T.Doc, xs => T.parse(String.append(xs, " = 1")), T.key.basic(ss),
      "\"" ++ L1.escs(ss) ++ "\"", L1.basic_escs(ss)),
    Equal.trans(T.Doc,
      T.doc.read(String.append(String.append(L1.escs(ss), "\""), " = 1"),
        T.MScan{kq(T.LTop{}, [])}),
      T.doc.read(String.append(L1.escs(ss), "\" = 1"), T.MScan{kq(T.LTop{}, [])}),
      T.Doc{"", [T.VPair{ss, T.VInt{T.Plus{}, "1"}}]},
      Equal.cong(String, T.Doc, xs => T.doc.read(xs, T.MScan{kq(T.LTop{}, [])}),
        String.append(String.append(L1.escs(ss), "\""), " = 1"),
        String.append(L1.escs(ss), "\" = 1"),
        Eq.append_assoc(L1.escs(ss), "\"", " = 1")),
      Equal.trans(T.Doc,
        T.doc.read(String.append(L1.escs(ss), "\" = 1"), T.MScan{kq(T.LTop{}, [])}),
        M4.kq.doc(M3.rev.onto(ss, [])),
        T.Doc{"", [T.VPair{ss, T.VInt{T.Plus{}, "1"}}]},
        kq.body(ss, T.LTop{}, []),
        M4.kq.name(ss))))

# a space ends a nonempty bare key, and " = 1" is read to the end
def key.sp(
  +bb: List<&2, Char>,
  full: {List.is_empty(&2, Char, bb) == False{} : Bool}
) -> {T.doc.read(" = 1", T.MScan{M1.ky(bb)}) == M4.kq.doc(bb) : T.Doc}:
  Equal.trans(T.Doc,
    T.doc.read("= 1", T.MScan{T.read.once2(T.lex.key.end.go(List.is_empty(&2, Char, bb),
      M1.ky(bb), T.LAfter{}))}),
    T.doc.read("= 1", T.MScan{T.read.once2(T.lex.key.end.go(False{}, M1.ky(bb), T.LAfter{}))}),
    M4.kq.doc(bb),
    Equal.cong(Bool, T.Doc,
      bt => T.doc.read("= 1", T.MScan{T.read.once2(T.lex.key.end.go(bt, M1.ky(bb), T.LAfter{}))}),
      List.is_empty(&2, Char, bb), False{}, full),
    {==})

# a bare key: its characters are read on the key's fast path, as for
# empty_basic_at_end
def kq.bare(
  +xx: U32,
  +tt: String,
  +ee: {T.bare.all.step(T.bare.at(Chr{xx}), _u => T.bare.all(String.to_list(tt))) == True{} : Bool}
) -> {T.parse(String.append(SCon{Chr{xx}, tt}, " = 1"))
  == T.Doc{"", [T.VPair{SCon{Chr{xx}, tt}, T.VInt{T.Plus{}, "1"}}]} : T.Doc}:
  Equal.trans(T.Doc,
    T.doc.read(String.append(tt, " = 1"), T.doc.scan(T.st.start(), Chr{xx})),
    T.doc.read(String.append(tt, " = 1"), T.MScan{M1.ky([Chr{xx}])}),
    T.Doc{"", [T.VPair{SCon{Chr{xx}, tt}, T.VInt{T.Plus{}, "1"}}]},
    Equal.cong(T.Mode, T.Doc, md => T.doc.read(String.append(tt, " = 1"), md),
      T.doc.scan(T.st.start(), Chr{xx}), T.MScan{M1.ky([Chr{xx}])},
      M1.key.first(xx, M5.ball.head(T.bare.at(Chr{xx}), String.to_list(tt), ee))),
    Equal.trans(T.Doc,
      T.doc.read(String.append(tt, " = 1"), T.MScan{M1.ky([Chr{xx}])}),
      T.doc.read(" = 1", T.MScan{M1.ky(M3.rev.onto(tt, [Chr{xx}]))}),
      T.Doc{"", [T.VPair{SCon{Chr{xx}, tt}, T.VInt{T.Plus{}, "1"}}]},
      M1.key.body(tt, " = 1", [Chr{xx}], M5.ball.tail(T.bare.at(Chr{xx}), String.to_list(tt), ee)),
      Equal.trans(T.Doc,
        T.doc.read(" = 1", T.MScan{M1.ky(M3.rev.onto(tt, [Chr{xx}]))}),
        M4.kq.doc(M3.rev.onto(tt, [Chr{xx}])),
        T.Doc{"", [T.VPair{SCon{Chr{xx}, tt}, T.VInt{T.Plus{}, "1"}}]},
        key.sp(M3.rev.onto(tt, [Chr{xx}]), M5.rev.full(tt, Chr{xx}, [])),
        M4.kq.name(SCon{Chr{xx}, tt}))))

# bare or quoted, as key picks
def kq.law(
  bb: Bool,
  +ss: String,
  eb: {T.bare(ss) == bb : Bool}
) -> {T.parse(String.append(T.key.go(bb, ss), " = 1"))
  == T.Doc{"", [T.VPair{ss, T.VInt{T.Plus{}, "1"}}]} : T.Doc}:
  match bb:
    case False{}:
      kq.quoted(ss)
    case True{}:
      match ss:
        case SNil{}:
          Eq.bit.absurd(&2, {T.parse(String.append(SNil{}, " = 1"))
            == T.Doc{"", [T.VPair{SNil{}, T.VInt{T.Plus{}, "1"}}]} : T.Doc}, eb)
        case SCon{hh, +tt}:
          match hh:
            case Chr{+xx}:
              kq.bare(xx, tt, eb)

def Laws.key_reads_back(s):
  kq.law(T.bare(s), s, {==})
