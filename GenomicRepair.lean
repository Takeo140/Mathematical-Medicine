/-!
# Genomic Repair — formal verification of genomic medicine

A proof-verified prototype of genomic medicine, built directly on the
foundations of the Mathematical-Medicine formalization: the base layer
(`Base`, `Codon`, `Genome`) follows Takeo Yamamoto's `GenomicModel.lean`
in that repository, where a genome is a list of codons and each base is
two bits of information.

What this file adds is the repair theory:

* Each base is encoded as **two bits** (`baseBits`), with a decoder;
  the round trip is proved, so the bit view and the base view agree.
* A patient genome and a healthy reference genome are compared
  position by position. The **Hamming distance** counts the positions
  that differ — the anomalies, i.e. bugs in the information space.
* The **canonical repair** rewrites exactly the anomalous positions to
  the reference codons and leaves every other position untouched:
  the treatment as a compiled, checkable patch.
* Machine-checked properties (no `sorry` anywhere), for genomes of
  equal length:
  * `repair_correct`  — the repaired genome has distance 0 from the
                        reference: every anomaly is fixed.
  * `repair_safe`     — at any position where patient and reference
                        already agree, the repair changes nothing:
                        no off-target edits.
  * `repair_minimal`  — any genome that fixes all anomalies differs
                        from the patient in at least as many positions
                        as the patient differs from the reference
                        (via a triangle inequality for Hamming distance).
  * `repair_optimal_exists` — the canonical repair attains that bound:
                        a complete, optimal repair always exists and
                        the search problem is therefore closed.

Honest note: this is a formal prototype. Codons and references are
abstract models; what is proved (Q.E.D.) is the correctness, safety
and optimality of the repair *inside the model*. The bridge to
clinical reality belongs to experiments and trials, as with any
model of a treatment.

Author: Takeo Yamamoto (GitHub: Takeo140)
License: Apache-2.0
-/

namespace GenomicRepair

/-! ## The base layer — after `GenomicModel.lean` (Mathematical-Medicine) -/

/-- The four DNA bases. -/
inductive Base : Type
  | A | T | G | C
  deriving Repr, DecidableEq

/-- A codon: three bases. -/
structure Codon where
  b1 : Base
  b2 : Base
  b3 : Base
  deriving Repr, DecidableEq

/-- A genome: a list of codons. (An `abbrev` rather than a plain `def`,
    so that list operations and indexing apply to genomes directly.) -/
abbrev Genome := List Codon

/-! ## Bases as bits

The design premise of Mathematical-Medicine: DNA is information.
Each base is exactly two bits. -/

/-- The two-bit encoding of a base: A = 00, T = 01, G = 10, C = 11. -/
def baseBits : Base → Bool × Bool
  | Base.A => (false, false)
  | Base.T => (false, true)
  | Base.G => (true, false)
  | Base.C => (true, true)

/-- Decoding two bits back to a base. -/
def decodeBase : Bool × Bool → Base
  | (false, false) => Base.A
  | (false, true) => Base.T
  | (true, false) => Base.G
  | (true, true) => Base.C

/-- The bit view is lossless: decoding the encoding returns the base. -/
theorem decodeBase_baseBits (b : Base) : decodeBase (baseBits b) = b := by
  cases b <;> rfl

/-- Hence the encoding is injective: the bits determine the base. -/
theorem baseBits_injective : Function.Injective baseBits := by
  intro a b h
  have h2 := congrArg decodeBase h
  rwa [decodeBase_baseBits, decodeBase_baseBits] at h2

/-- The bits of a codon: six bits, three bases at two bits each. -/
def codonBits (c : Codon) : List Bool :=
  [ (baseBits c.b1).1, (baseBits c.b1).2,
    (baseBits c.b2).1, (baseBits c.b2).2,
    (baseBits c.b3).1, (baseBits c.b3).2 ]

/-- A codon's bit view always has length 6. -/
theorem codonBits_length (c : Codon) : (codonBits c).length = 6 := rfl

/-! ## Distance and repair -/

/-- Hamming distance between two genomes: the number of positions
    (within the overlap) whose codons differ. -/
def hamming (p r : Genome) : Nat :=
  (p.zip r).countP (fun q => decide (q.1 ≠ q.2))

/-- One-step unfolding of Hamming distance on cons lists. -/
theorem hamming_cons (a b : Codon) (as bs : Genome) :
    hamming (a :: as) (b :: bs)
      = (if a = b then 0 else 1) + hamming as bs := by
  unfold hamming
  rw [List.zip_cons_cons, List.countP_cons]
  by_cases h : a = b <;> simp [h] <;> omega

/-- The canonical repair: at each position, keep the patient's codon
    if it already agrees with the reference, otherwise take the
    reference codon. -/
def repair (p r : Genome) : Genome :=
  (p.zip r).map (fun q => if q.1 = q.2 then q.1 else q.2)

/-- Pairs in a self-zip have equal components. -/
theorem zip_self_fst_eq_snd (g : Genome) (q : Codon × Codon)
    (hq : q ∈ g.zip g) : q.1 = q.2 := by
  induction g with
  | nil => simp at hq
  | cons c cs ih =>
      simp only [List.zip_cons_cons, List.mem_cons] at hq
      rcases hq with rfl | hq
      · rfl
      · exact ih hq

theorem hamming_self (g : Genome) : hamming g g = 0 := by
  unfold hamming
  rw [List.countP_eq_zero]
  intro q hq
  have hqq : q.1 = q.2 := zip_self_fst_eq_snd g q hq
  simp [hqq]

theorem repair_length (p r : Genome) :
    (repair p r).length = min p.length r.length := by
  unfold repair
  rw [List.length_map, List.length_zip]

/-- Correctness, pointwise form: the repair at every position equals
    the reference there. Stated through `get?` so that the safety
    theorem below can use the same lemma. -/
theorem repair_get? {p r : Genome} (h : p.length = r.length) (i : Nat) :
    (repair p r)[i]? = r[i]? := by
  induction p generalizing r i with
  | nil =>
      cases r with
      | nil => simp [repair]
      | cons r rs => simp at h
  | cons c cs ih =>
      cases r with
      | nil => simp at h
      | cons d ds =>
          have hlen : cs.length = ds.length := by
            simpa [List.length_cons] using h
          cases i with
          | zero =>
              by_cases hcd : c = d
              · subst hcd; simp [repair]
              · simp [repair, hcd]
          | succ i =>
              have hrec := ih hlen i
              simp only [repair, List.zip_cons_cons, List.map_cons,
                List.getElem?_cons_succ]
              exact hrec

/-- Correctness: the repaired genome *is* the reference genome. -/
theorem repair_eq_ref {p r : Genome} (h : p.length = r.length) :
    repair p r = r := by
  apply List.ext_getElem?
  intro i
  exact repair_get? h i

/-- Correctness, distance form: after repair, no anomaly remains. -/
theorem repair_correct {p r : Genome} (h : p.length = r.length) :
    hamming (repair p r) r = 0 := by
  rw [repair_eq_ref h]
  exact hamming_self r

/-- Safety: at any position where patient and reference already agree,
    the repair leaves the patient's codon untouched — the patch has
    no off-target edits. -/
theorem repair_safe {p r : Genome} (h : p.length = r.length) (i : Nat)
    (hi : p[i]? = r[i]?) :
    (repair p r)[i]? = p[i]? := by
  rw [repair_get? h i, ← hi]

/-- The repair edits exactly the anomalous positions: its distance
    from the patient equals the patient's distance from the reference. -/
theorem hamming_patient_repair {p r : Genome} (h : p.length = r.length) :
    hamming p (repair p r) = hamming p r := by
  induction p generalizing r with
  | nil => simp [hamming, repair]
  | cons c cs ih =>
      cases r with
      | nil => simp at h
      | cons d ds =>
          have hlen : cs.length = ds.length := by
            simpa [List.length_cons] using h
          have step : repair (c :: cs) (d :: ds)
              = (if c = d then c else d) :: repair cs ds := rfl
          rw [step]
          by_cases hcd : c = d
          · subst hcd
            simp only [hamming_cons, ite_true]
            rw [ih hlen]
          · rw [ite_eq_right hcd, hamming_cons, hamming_cons, ite_eq_right hcd, ih hlen]

/-- Triangle inequality for Hamming distance (on the common overlap,
    stated here for equal-length genomes). -/
theorem hamming_triangle {p r g : Genome}
    (h1 : p.length = r.length) (h2 : r.length = g.length) :
    hamming p r ≤ hamming p g + hamming g r := by
  induction p generalizing r g with
  | nil => simp [hamming]
  | cons a as ih =>
      cases r with
      | nil => simp at h1
      | cons b bs =>
          cases g with
          | nil => simp at h2
          | cons c cs =>
              have e1 : as.length = bs.length := by
                simpa [List.length_cons] using h1
              have e2 : bs.length = cs.length := by
                simpa [List.length_cons] using h2
              have ih' := ih e1 e2
              simp only [hamming_cons]
              by_cases hab : a = b
              · by_cases hac : a = c
                · have hcb : c = b := hac.symm.trans hab
                  rw [ite_eq_left hab, ite_eq_left hac, ite_eq_left hcb]
                  omega
                · have hcb : ¬ c = b := fun hh => hac (hab.trans hh.symm)
                  rw [ite_eq_left hab, ite_eq_right hac, ite_eq_right hcb]
                  omega
              · by_cases hac : a = c
                · have hcb : ¬ c = b := fun hh => hab (hac.trans hh)
                  rw [ite_eq_right hab, ite_eq_left hac, ite_eq_right hcb]
                  omega
                · by_cases hcb : c = b
                  · rw [ite_eq_right hab, ite_eq_right hac, ite_eq_left hcb]
                    omega
                  · rw [ite_eq_right hab, ite_eq_right hac, ite_eq_right hcb]
                    omega

/-- Minimality: any genome that fixes every anomaly (distance 0 from
    the reference) must differ from the patient in at least as many
    positions as the patient differs from the reference. No repair
    can use fewer edits than the canonical one. -/
theorem repair_minimal {p r g : Genome}
    (h1 : p.length = r.length) (h2 : r.length = g.length)
    (hg : hamming g r = 0) :
    hamming p r ≤ hamming p g := by
  have h := hamming_triangle h1 h2
  rw [hg, Nat.add_zero] at h
  exact h

/-- Completeness and optimality together: a repair always exists
    that fixes every anomaly and uses the smallest possible number
    of edits — namely, the canonical repair. -/
theorem repair_optimal_exists {p r : Genome} (h : p.length = r.length) :
    ∃ g : Genome, hamming g r = 0 ∧ hamming p g = hamming p r ∧
      ∀ g' : Genome, g'.length = r.length → hamming g' r = 0 →
        hamming p g ≤ hamming p g' := by
  refine ⟨repair p r, repair_correct h, hamming_patient_repair h, ?_⟩
  intro g' hg' hfix
  rw [hamming_patient_repair h]
  exact repair_minimal h hg'.symm hfix

/-! ## A worked example

A four-codon fragment, in the style of a model-organism example:
two codons are anomalous (positions 1 and 3), two are intact.
The canonical repair fixes exactly those two and nothing else. -/

/-- Reference (healthy) fragment. -/
def demoRef : Genome :=
  [ ⟨Base.A, Base.T, Base.G⟩, ⟨Base.C, Base.A, Base.A⟩,
    ⟨Base.G, Base.G, Base.T⟩, ⟨Base.T, Base.C, Base.A⟩ ]

/-- Patient fragment: codons at positions 1 and 3 differ. -/
def demoPatient : Genome :=
  [ ⟨Base.A, Base.T, Base.G⟩, ⟨Base.C, Base.G, Base.A⟩,
    ⟨Base.G, Base.G, Base.T⟩, ⟨Base.A, Base.C, Base.A⟩ ]

/-- The patient differs from the reference at exactly 2 positions. -/
example : hamming demoPatient demoRef = 2 := by decide

/-- The repair restores the reference exactly. -/
example : repair demoPatient demoRef = demoRef := by decide

/-- After repair, the distance to the reference is 0. -/
example : hamming (repair demoPatient demoRef) demoRef = 0 := by decide

/-- The repair itself is 2 edits away from the patient — the minimum. -/
example : hamming demoPatient (repair demoPatient demoRef) = 2 := by decide

end GenomicRepair

/-! ## Axiom check

The main theorems must depend only on the standard axioms
(`propext`, `Classical.choice`, `Quot.sound`) — in particular,
no `sorryAx`. -/

#print axioms GenomicRepair.repair_correct
#print axioms GenomicRepair.repair_safe
#print axioms GenomicRepair.repair_minimal
#print axioms GenomicRepair.repair_optimal_exists
#print axioms GenomicRepair.decodeBase_baseBits
