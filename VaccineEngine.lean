import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Basic

namespace VaccineEngine

inductive Nucleotide : Type
  | A | C | G | U
  deriving Repr, DecidableEq, Inhabited

def Codon := Nucleotide × Nucleotide × Nucleotide
  deriving Repr, DecidableEq, Inhabited

def Nucleotide.hydrogenBonds : Nucleotide → Nat
  | .G | .C => 3
  | .A | .U => 2

def countGC : List Nucleotide → Nat
  | [] => 0
  | b :: bs => match b with
    | .G | .C => 1 + countGC bs
    | .A | .U => countGC bs

def gcContentRatio (seq : List Nucleotide) : Nat :=
  if seq.length = 0 then 0
  else (countGC seq * 100) / seq.length

structure VaccineCassette where
  cap5  : List Nucleotide
  utr5  : List Nucleotide
  cds   : List Nucleotide
  utr3  : List Nucleotide
  polyA : List Nucleotide

def assembleRNA (v : VaccineCassette) : List Nucleotide :=
  v.cap5 ++ v.utr5 ++ v.cds ++ v.utr3 ++ v.polyA

structure ManufacturingQC where
  raw_yield_mg      : ℝ
  dsRNA_percentage  : ℝ
  u_modification_rate : ℝ

def isGMPCompliant (qc : ManufacturingQC) : Prop :=
  qc.dsRNA_percentage < 0.001 ∧
  qc.u_modification_rate ≥ 0.99 ∧
  qc.raw_yield_mg ≥ 10.0

instance (qc : ManufacturingQC) : Decidable (isGMPCompliant qc) := by
  unfold isGMPCompliant
  infer_instance

def target_spike_cds_fragment : List Nucleotide :=
  [.G, .U, .G, .C, .U, .G, .U, .C, .G, .A, .G, .C, .A, .U, .C]

def optimized_vaccine_production : VaccineCassette := {
  cap5  := [.G, .G, .A]
  utr5  := [.C, .C, .G, .A, .U]
  cds   := target_spike_cds_fragment
  utr3  := [.U, .G, .A, .C]
  polyA := [.A, .A, .A, .A, .A, .A, .A, .A, .A, .A]
}

def operational_qc_report : ManufacturingQC := {
  raw_yield_mg        := 45.5
  dsRNA_percentage    := 0.0003
  u_modification_rate := 0.995
}

lemma countGC_nil : countGC [] = 0 := rfl

lemma countGC_append (xs ys : List Nucleotide) : countGC (xs ++ ys) = countGC xs + countGC ys := by
  induction xs with
  | nil => simp [countGC_nil]
  | cons x xs ih =>
      cases x <;> (simp [countGC, ih]; omega)

theorem assemble_gc_conservation (v : VaccineCassette) :
  countGC (assembleRNA v) = countGC v.cap5 + countGC v.utr5 + countGC v.cds + countGC v.utr3 + countGC v.polyA := by
  unfold assembleRNA
  repeat rw [countGC_append]
  omega

/-- 空配列時の GC 含有率は 0 を返すことを保証 -/
lemma gcContentRatio_empty : gcContentRatio [] = 0 := by
  simp [gcContentRatio]

/-- 実運用 QC レポートが GMP 基準を満たすことの証明 -/
theorem operational_batch_is_safe : isGMPCompliant operational_qc_report := by
  unfold isGMPCompliant
  unfold operational_qc_report
  refine ⟨by linarith, by linarith, by linarith⟩

end VaccineEngine
