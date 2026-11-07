import Mathlib.Data.List.Basic

namespace MetaMRNA

/-- 1. ヌクレオチド定義（RNA） -/
inductive RNA where
  | A | U | G | C
  deriving Repr, DecidableEq, BEq

/-- 2. アミノ酸定義（ターゲット） -/
inductive AminoAcid where
  | Ala | Arg | Asn | Asp | Cys | Gln | Glu | Gly | His | Ile | Leu | Lys | Met | Phe | Pro | Ser | Thr | Trp | Tyr | Val | Stop
  deriving Repr, DecidableEq

/-- 3. コドン最適化テーブル（ヒト細胞用）
    1つのアミノ酸に対して、翻訳効率や安定性を重視した代表的なコドンを割り当てる。
-/
def optimal_codon : AminoAcid → RNA × RNA × RNA
  | .Ala => (.G, .C, .U)
  | .Arg => (.C, .G, .U)
  | .Asn => (.A, .A, .U)
  | .Asp => (.G, .A, .U)
  | .Cys => (.U, .G, .U)
  | .Gln => (.C, .A, .A)
  | .Glu => (.G, .A, .A)
  | .Gly => (.G, .G, .U)
  | .His => (.C, .A, .U)
  | .Ile => (.A, .U, .U)
  | .Leu => (.C, .U, .U)
  | .Lys => (.A, .A, .A)
  | .Met => (.A, .U, .G)
  | .Phe => (.U, .U, .U)
  | .Pro => (.C, .C, .U)
  | .Ser => (.U, .C, .U)
  | .Thr => (.A, .C, .U)
  | .Trp => (.U, .G, .G)
  | .Tyr => (.U, .A, .U)
  | .Val => (.G, .U, .U)
  | .Stop => (.U, .A, .A)

/-- 4. アミノ酸配列からmRNA配列への変換 -/
def generate_mrna (protein : List AminoAcid) : List RNA :=
  protein.bind fun aa =>
    let (c1, c2, c3) := optimal_codon aa
    [c1, c2, c3]

/-- 5. mRNAの安定性スコア（GC含量評価）
    空リストの場合は 0.0 を返してゼロ除算を回避 -/
def gc_content (seq : List RNA) : Float :=
  if seq.isEmpty then 0.0
  else
    let gc := (seq.filter fun b => b == .G || b == .C).length
    gc.toFloat / seq.length.toFloat * 100.0

/-- 6. 命題：mrna が protein を正しくコードする
    ≡ generate_mrna による変換結果と一致する -/
def is_correct_encoding (protein : List AminoAcid) (mrna : List RNA) : Prop :=
  mrna = generate_mrna protein

/-- 7. 定理：generate_mrna は常に is_correct_encoding を満たす -/
theorem generate_mrna_correct (protein : List AminoAcid) :
    is_correct_encoding protein (generate_mrna protein) := rfl

end MetaMRNA
