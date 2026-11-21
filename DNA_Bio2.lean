/-
  License: Apache 2.0 / CC BY 4.0
  Author: Takeo Yamamoto

  細胞構造に合わせて DNA → Codon → AminoAcid → Protein → Cell → Protocol
  までを一つに統合した抽象モデル（基盤レイヤ・翻訳系・細胞プロトコル系 精緻化版）。
-/

namespace Bio

/-- 1. DNA塩基（4bit構造と同型） -/
inductive Base : Type
  | A | T | G | C
  deriving Repr, DecidableEq

/-- Char → Base の安全変換 -/
def char_to_base : Char → Option Base
  | 'A' => some Base.A
  | 'T' => some Base.T
  | 'G' => some Base.G
  | 'C' => some Base.C
  | _   => none

/-- Base → Char の変換 -/
def base_to_char : Base → Char
  | Base.A => 'A'
  | Base.T => 'T'
  | Base.G => 'G'
  | Base.C => 'C'

theorem char_to_base_of_base_to_char (b : Base) :
    char_to_base (base_to_char b) = some b := by
  cases b <;> rfl

/-- 相補的塩基 -/
def complement : Base → Base
  | Base.A => Base.T
  | Base.T => Base.A
  | Base.G => Base.C
  | Base.C => Base.G

/-- 相補塩基の対合性（二重相補は元に戻る） -/
theorem complement_complement (b : Base) : complement (complement b) = b := by
  cases b <;> rfl

/-- 相補塩基は固定点を持たない（A≠T, G≠Cなど） -/
theorem complement_ne (b : Base) : complement b ≠ b := by
  cases b <;> decide

/-- 塩基リストの相補鎖と逆相補鎖 -/
def complementStrand (bs : List Base) : List Base :=
  bs.map complement

def reverseComplementStrand (bs : List Base) : List Base :=
  (bs.map complement).reverse

theorem complementStrand_length (bs : List Base) :
    (complementStrand bs).length = bs.length := by
  simp [complementStrand]

theorem reverseComplementStrand_length (bs : List Base) :
    (reverseComplementStrand bs).length = bs.length := by
  simp [reverseComplementStrand]

theorem reverseComplementStrand_involutive (bs : List Base) :
    reverseComplementStrand (reverseComplementStrand bs) = bs := by
  simp [reverseComplementStrand, complement_complement]

/-- reverse_complement（文字列版：検証済みリスト処理） -/
def reverse_complement (s : String) : String :=
  let chars := s.toList.reverse.map (fun c =>
    match char_to_base c with
    | some b => base_to_char (complement b)
    | none   => c)
  String.ofList chars

/-- 2. Codon（3塩基・全64種） -/
structure Codon where
  b1 : Base
  b2 : Base
  b3 : Base
  deriving Repr, DecidableEq

/-- String → Codon の安全変換 -/
def string_to_codon (s : String) : Option Codon :=
  match s.toList.map char_to_base with
  | [some b1, some b2, some b3] => some ⟨b1, b2, b3⟩
  | _ => none

/-- 塩基列（List Base）を 3塩基ごとのコドン列へ翻訳（端数 < 3 塩基は切り捨て） -/
def basesToCodons : List Base → List Codon
  | b1 :: b2 :: b3 :: rest => ⟨b1, b2, b3⟩ :: basesToCodons rest
  | _ => []

/-- コドン列から塩基列への復元（3 × コドン数） -/
def codonsToBases : List Codon → List Base
  | [] => []
  | c :: cs => c.b1 :: c.b2 :: c.b3 :: codonsToBases cs

theorem codonsToBases_length (cs : List Codon) :
    (codonsToBases cs).length = 3 * cs.length := by
  induction cs with
  | nil => rfl
  | cons c rest ih =>
    simp [codonsToBases, ih]
    omega

/-- 3. アミノ酸（20種類すべてを明示） -/
inductive AminoAcid : Type
  | Ala | Arg | Asn | Asp | Cys
  | Gln | Glu | Gly | His | Ile
  | Leu | Lys | Met | Phe | Pro
  | Ser | Thr | Trp | Tyr | Val
  deriving Repr, DecidableEq

/-- 翻訳結果（アミノ酸、または終止コドン `stop`） -/
inductive TranslationUnit : Type
  | aa (a : AminoAcid)
  | stop
  deriving Repr, DecidableEq

/-- 標準遺伝暗号表に基づく Codon → TranslationUnit -/
def codonToUnit (c : Codon) : TranslationUnit :=
  match c.b1, c.b2, c.b3 with
  -- 終止コドン：TAA, TAG, TGA
  | .T, .A, .A => .stop
  | .T, .A, .G => .stop
  | .T, .G, .A => .stop
  -- 開始コドン / Met：ATG
  | .A, .T, .G => .aa .Met
  -- Trp：TGG
  | .T, .G, .G => .aa .Trp
  -- Phe：TTT, TTC
  | .T, .T, .T | .T, .T, .C => .aa .Phe
  -- Leu：TTA, TTG, CTT, CTC, CTA, CTG
  | .T, .T, .A | .T, .T, .G
  | .C, .T, .T | .C, .T, .C | .C, .T, .A | .C, .T, .G => .aa .Leu
  -- Ile：ATT, ATC, ATA
  | .A, .T, .T | .A, .T, .C | .A, .T, .A => .aa .Ile
  -- Val：GTT, GTC, GTA, GTG
  | .G, .T, .T | .G, .T, .C | .G, .T, .A | .G, .T, .G => .aa .Val
  -- Ser：TCT, TCC, TCA, TCG, AGT, AGC
  | .T, .C, .T | .T, .C, .C | .T, .C, .A | .T, .C, .G
  | .A, .G, .T | .A, .G, .C => .aa .Ser
  -- Pro：CCT, CCC, CCA, CCG
  | .C, .C, .T | .C, .C, .C | .C, .C, .A | .C, .C, .G => .aa .Pro
  -- Thr：ACT, ACC, ACA, ACG
  | .A, .C, .T | .A, .C, .C | .A, .C, .A | .A, .C, .G => .aa .Thr
  -- Ala：GCT, GCC, GCA, GCG
  | .G, .C, .T | .G, .C, .C | .G, .C, .A | .G, .C, .G => .aa .Ala
  -- Tyr：TAT, TAC
  | .T, .A, .T | .T, .A, .C => .aa .Tyr
  -- His：CAT, CAC
  | .C, .A, .T | .C, .A, .C => .aa .His
  -- Gln：CAA, CAG
  | .C, .A, .A | .C, .A, .G => .aa .Gln
  -- Asn：AAT, AAC
  | .A, .A, .T | .A, .A, .C => .aa .Asn
  -- Lys：AAA, AAG
  | .A, .A, .A | .A, .A, .G => .aa .Lys
  -- Asp：GAT, GAC
  | .G, .A, .T | .G, .A, .C => .aa .Asp
  -- Glu：GAA, GAG
  | .G, .A, .A | .G, .A, .G => .aa .Glu
  -- Cys：TGT, TGC
  | .T, .G, .T | .T, .G, .C => .aa .Cys
  -- Arg：CGT, CGC, CGA, CGG, AGA, AGG
  | .C, .G, .T | .C, .G, .C | .C, .G, .A | .C, .G, .G
  | .A, .G, .A | .A, .G, .G => .aa .Arg
  -- Gly：GGT, GGC, GGA, GGG
  | .G, .G, .T | .G, .G, .C | .G, .G, .A | .G, .G, .G => .aa .Gly

/-- 既存互換の `codonToAA : Codon → Option AminoAcid` -/
def codonToAA (c : Codon) : Option AminoAcid :=
  match codonToUnit c with
  | .aa a => some a
  | .stop => none

theorem codonToAA_start_met :
    codonToAA ⟨.A, .T, .G⟩ = some .Met := rfl

theorem codonToAA_stop_taa :
    codonToAA ⟨.T, .A, .A⟩ = none := rfl

/-- コドン列からアミノ酸列への翻訳（終止コドンで停止） -/
def codonsToAminoAcids : List Codon → List AminoAcid
  | [] => []
  | c :: cs =>
      match codonToAA c with
      | none    => []
      | some aa => aa :: codonsToAminoAcids cs

/-- 4. タンパク質の役割 -/
inductive ProteinRole : Type
  | Structural      -- 細胞骨格
  | Enzyme          -- 代謝酵素
  | Transcription   -- 転写因子
  | Signal          -- シグナル伝達
  deriving Repr, DecidableEq

/-- タンパク質 -/
structure Protein where
  seq  : List AminoAcid
  role : ProteinRole
  deriving Repr, DecidableEq

/-- 塩基列から指定した役割のタンパク質を構成する -/
def synthesizeProtein (role : ProteinRole) (bases : List Base) : Protein :=
  { seq := codonsToAminoAcids (basesToCodons bases), role := role }

theorem synthesizeProtein_role (role : ProteinRole) (bases : List Base) :
    (synthesizeProtein role bases).role = role := rfl

/-- 5. 細胞状態（iPS / Direct / 分化 / 減数分裂期 / 半数体） -/
inductive CellState : Type
  | Stem
  | IPS
  | Direct
  | Differentiated
  | ProphaseI
  | MeiosisI
  | MeiosisII
  | Haploid
  deriving Repr, DecidableEq

/-- 細胞はタンパク質の集合として表現できる -/
structure Cell where
  proteins : List Protein
  state    : CellState
  deriving Repr, DecidableEq

/-- 細胞内に指定の役割（`ProteinRole`）を持つタンパク質が存在するか（決定可能） -/
def hasRole (c : Cell) (r : ProteinRole) : Bool :=
  c.proteins.any (fun pr => decide (pr.role = r))

/-- 6. 細胞生成プロトコル -/
structure Protocol where
  name          : String
  requiredRoles : List ProteinRole
  targetState   : CellState
  deriving Repr, DecidableEq

def IPSProtocol : Protocol :=
  { name := "iPS Induction"
    requiredRoles := [ProteinRole.Transcription]
    targetState := CellState.IPS }

def DirectProtocol : Protocol :=
  { name := "Direct Conversion"
    requiredRoles := [ProteinRole.Signal]
    targetState := CellState.Direct }

/-- プロトコル適用可能性（命題レベル） -/
def CanApply (p : Protocol) (c : Cell) : Prop :=
  ∀ r ∈ p.requiredRoles, ∃ pr ∈ c.proteins, pr.role = r

instance (p : Protocol) (c : Cell) : Decidable (CanApply p c) :=
  inferInstanceAs (Decidable (∀ r ∈ p.requiredRoles, ∃ pr ∈ c.proteins, pr.role = r))

/-- 7. 細胞状態遷移（プロセス思考の核） -/
def applyProtocol (p : Protocol) (c : Cell) (_h : CanApply p c) : Cell :=
  { proteins := c.proteins, state := p.targetState }

/-- 2つのプロトコルを直列合成する（要求役割は和集合、状態は後段の `targetState` へ遷移） -/
def sequenceProtocols (p1 p2 : Protocol) : Protocol :=
  { name := p1.name ++ " -> " ++ p2.name
    requiredRoles := p1.requiredRoles ++ p2.requiredRoles
    targetState := p2.targetState }

theorem canApply_sequence {p1 p2 : Protocol} {c : Cell}
    (h1 : CanApply p1 c) (h2 : CanApply p2 c) :
    CanApply (sequenceProtocols p1 p2) c := by
  intro r hr
  simp [sequenceProtocols, List.mem_append] at hr
  rcases hr with hr1 | hr2
  · exact h1 r hr1
  · exact h2 r hr2

theorem applyProtocol_preserves_proteins (p : Protocol) (c : Cell) (h : CanApply p c) :
    (applyProtocol p c h).proteins = c.proteins := rfl

end Bio
