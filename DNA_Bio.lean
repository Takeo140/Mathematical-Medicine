/-
  License: Apache 2.0 / CC BY 4.0
  Author: Takeo Yamamoto

  細胞構造に合わせて DNA → Codon → AminoAcid → Protein → Cell → Protocol
  までを一つに統合した抽象モデル（精緻化版：多点交叉・四分子分離・翻訳接続・不変量証明）。
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

/-- 相補的塩基 -/
def complement : Base → Base
  | Base.A => Base.T
  | Base.T => Base.A
  | Base.G => Base.C
  | Base.C => Base.G

/-- 相補塩基の対合性 -/
theorem complement_complement (b : Base) : complement (complement b) = b := by
  cases b <;> rfl

/-- reverse_complement（検証済みリスト処理） -/
def reverse_complement (s : String) : String :=
  let chars := s.toList.reverse.map (fun c =>
    match char_to_base c with
    | some b => base_to_char (complement b)
    | none   => c)
  String.ofList chars

/-- 2. Codon（3塩基） -/
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

/-- 3. アミノ酸（20種類） -/
inductive AminoAcid : Type
  | Ala | Arg | Asn | Asp | Cys
  | Gln | Glu | Gly | His | Ile
  | Leu | Lys | Met | Phe | Pro
  | Ser | Thr | Trp | Tyr | Val
  deriving Repr, DecidableEq

/-- Codon → AminoAcid（簡略版：開始コドン ATG → Met、TAA → 終止 `none`） -/
def codonToAA : Codon → Option AminoAcid
  | ⟨Base.A, Base.T, Base.G⟩ => some AminoAcid.Met
  | ⟨Base.T, Base.A, Base.A⟩ => none
  | _ => some AminoAcid.Ala

/-- コドン列からアミノ酸列への翻訳（終止コドンに到達したら翻訳終了） -/
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

/-- 塩基列から指定した役割（`ProteinRole`）のタンパク質を構成する -/
def synthesizeProtein (role : ProteinRole) (bases : List Base) : Protein :=
  { seq := codonsToAminoAcids (basesToCodons bases), role := role }

/-- 5. 細胞状態（iPS / Direct / 減数分裂期 / 半数体配偶子） -/
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

def MeiosisIProtocol : Protocol :=
  { name := "Meiosis I (Homolog Separation)"
    requiredRoles := [ProteinRole.Structural, ProteinRole.Enzyme]
    targetState := CellState.MeiosisI }

def MeiosisIIProtocol : Protocol :=
  { name := "Meiosis II (Gamete Formation)"
    requiredRoles := [ProteinRole.Structural]
    targetState := CellState.Haploid }

/-- プロトコル適用可能性（命題レベル） -/
def CanApply (p : Protocol) (c : Cell) : Prop :=
  ∀ r ∈ p.requiredRoles, ∃ pr ∈ c.proteins, pr.role = r

instance (p : Protocol) (c : Cell) : Decidable (CanApply p c) :=
  inferInstanceAs (Decidable (∀ r ∈ p.requiredRoles, ∃ pr ∈ c.proteins, pr.role = r))

/-- 7. 細胞状態遷移（プロセス思考の核） -/
def applyProtocol (p : Protocol) (c : Cell) (_h : CanApply p c) : Cell :=
  { proteins := c.proteins, state := p.targetState }

/-- `applyProtocol` 適用後の状態は `p.targetState` に一致する -/
theorem applyProtocol_state (p : Protocol) (c : Cell) (h : CanApply p c) :
    (applyProtocol p c h).state = p.targetState := rfl

-- ─────────────────────────────────────────────────
-- 8. 精緻化版 DNA 減数分裂モデル
-- ─────────────────────────────────────────────────

abbrev DnaStrand := List Base

/-- 二倍体（Diploid）の相同DNA対（母方・父方） -/
structure DiploidDna where
  maternal : DnaStrand
  paternal : DnaStrand
  deriving Repr, DecidableEq

/-- 半数体（Haploid）のDNA鎖 -/
structure HaploidDna where
  strand : DnaStrand
  deriving Repr, DecidableEq

/-- 1点交叉（位置 `k` で鎖の前後を入れ替える） -/
def singleCrossover (k : Nat) (m p : DnaStrand) : DnaStrand × DnaStrand :=
  (m.take k ++ p.drop k, p.take k ++ m.drop k)

/-- 多点交叉（交叉点のリスト `sites` を順次適用して組換え鎖ペアを構成） -/
def multiCrossover (sites : List Nat) (m p : DnaStrand) : DnaStrand × DnaStrand :=
  sites.foldl (fun (accM, accP) k => singleCrossover k accM accP) (m, p)

/-- 1点交叉は左鎖・右鎖それぞれの長さを保存する -/
theorem singleCrossover_lengths (k : Nat) (m p : DnaStrand)
    (hlen : m.length = p.length) :
    (singleCrossover k m p).1.length = m.length ∧
      (singleCrossover k m p).2.length = p.length := by
  constructor
  · simp [singleCrossover, List.length_append, List.length_take, List.length_drop, hlen]
    omega
  · simp [singleCrossover, List.length_append, List.length_take, List.length_drop, hlen]
    omega

/-- 多点交叉は任意の交叉点リスト `sites` に対して両鎖の長さを保存する -/
theorem multiCrossover_lengths (sites : List Nat) (m p : DnaStrand)
    (hlen : m.length = p.length) :
    (multiCrossover sites m p).1.length = m.length ∧
      (multiCrossover sites m p).2.length = p.length := by
  induction sites generalizing m p with
  | nil =>
    exact ⟨rfl, rfl⟩
  | cons k ks ih =>
    dsimp [multiCrossover, List.foldl]
    have h1 := singleCrossover_lengths k m p hlen
    exact ih (singleCrossover k m p).1 (singleCrossover k m p).2
      (by omega)

/-- 複製（S期）後の四分子（Tetrad）：各相同染色体が姉妹染色分体対を持つ -/
structure Tetrad where
  matA : DnaStrand  -- 母方 姉妹染色分体A
  matB : DnaStrand  -- 母方 姉妹染色分体B
  patA : DnaStrand  -- 父方 姉妹染色分体A
  patB : DnaStrand  -- 父方 姉妹染色分体B
  deriving Repr, DecidableEq

/-- 二倍体DNAの複製により四分子（Tetrad）を形成 -/
def replicateDiploid (d : DiploidDna) : Tetrad :=
  { matA := d.maternal
    matB := d.maternal
    patA := d.paternal
    patB := d.paternal }

/-- 第一減数分裂（Meiosis I）：
    交叉点 `sites` で `matA` と `patA` の間で乗換えを起こし、
    2つの娘細胞（第1娘群・第2娘群）へ相同染色体を分配する。 -/
def meiosisI (sites : List Nat) (t : Tetrad) :
    (DnaStrand × DnaStrand) × (DnaStrand × DnaStrand) :=
  let (recMat, recPat) := multiCrossover sites t.matA t.patA
  ((recMat, t.matB), (recPat, t.patB))

/-- 減数分裂完了時の4つの半数体配偶子パネル（4 Gametes） -/
structure GametePanel where
  gamete1 : HaploidDna  -- 組換え母方由来
  gamete2 : HaploidDna  -- 非組換え母方姉妹由来
  gamete3 : HaploidDna  -- 組換え父方由来
  gamete4 : HaploidDna  -- 非組換え父方姉妹由来
  deriving Repr, DecidableEq

/-- 第二減数分裂（Meiosis II）：
    姉妹染色分体が分離し、4つの半数体配偶子（`GametePanel`）を生成する。 -/
def meiosisII (sites : List Nat) (d : DiploidDna) : GametePanel :=
  let t := replicateDiploid d
  let ((g1, g2), (g3, g4)) := meiosisI sites t
  { gamete1 := ⟨g1⟩
    gamete2 := ⟨g2⟩
    gamete3 := ⟨g3⟩
    gamete4 := ⟨g4⟩ }

/-- 第二減数分裂で得られる4配偶子すべてのDNA鎖長が元の相同鎖長と一致すること -/
theorem meiosisII_all_gametes_length (sites : List Nat) (d : DiploidDna)
    (hlen : d.maternal.length = d.paternal.length) :
    let panel := meiosisII sites d
    panel.gamete1.strand.length = d.maternal.length ∧
    panel.gamete2.strand.length = d.maternal.length ∧
    panel.gamete3.strand.length = d.paternal.length ∧
    panel.gamete4.strand.length = d.paternal.length := by
  dsimp [meiosisII, meiosisI, replicateDiploid]
  have hrec := multiCrossover_lengths sites d.maternal d.paternal hlen
  exact ⟨hrec.1, rfl, hrec.2, rfl⟩

/-- 配偶子DNAから合成されたタンパク質群を持つ細胞が、`MeiosisIIProtocol` を適用可能であること -/
theorem gamete_cell_can_apply_meiosisII (g : HaploidDna) :
    CanApply MeiosisIIProtocol
      { proteins := [synthesizeProtein ProteinRole.Structural g.strand]
        state := CellState.MeiosisII } := by
  intro r hr
  simp [MeiosisIIProtocol] at hr
  subst hr
  exact ⟨synthesizeProtein ProteinRole.Structural g.strand, by simp, rfl⟩

end Bio
