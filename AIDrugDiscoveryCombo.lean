/-!
# AI Drug Discovery: Combination Therapy — proof-verified coverage by a pair

A fourth part of the proof-verified AI drug discovery line in this
repository. `AIDrugDiscovery` screens a library, `AIDrugDiscoveryExt`
adds selectivity and certificates, and `AIDrugDiscoveryDescent`
optimizes a single lead. This file covers the next step of a discovery
pipeline: **combination therapy** — using two compounds together.

The model is deliberately abstract:

* A **compound** is a molecular fingerprint — a list of bits — together
  with a toxicity flag, as in the earlier files.
* The **coverage defect** (`uncovered`) of a fingerprint against a
  target profile counts the positions where the target requires a
  feature (`true`) that the fingerprint does not have. Extra features
  are not counted here; they are the selectivity question, handled in
  `AIDrugDiscoveryExt`.
* The **combination** of two compounds covers a feature when either of
  them has it (bitwise OR of the fingerprints), and it is toxic when
  either of them is toxic (a conservative safety rule).

Machine-checked properties (no `sorry` anywhere):

* `uncovered_zipOr_le_left` / `uncovered_zipOr_le_right`
                           — a combination never covers less than
                             either compound alone: the coverage defect
                             of the pair is at most each single defect.
* `combo_covers_of_left`   — if one compound already covers the
                             target, so does any combination with it.
* `combine_safe`           — a combination is non-toxic exactly when
                             both compounds are non-toxic.
* `combine_comm`           — the order of the two compounds does not
                             matter.
* `comboCertified_ok`      — the decidable certificate checker is
                             sound: a certified pair really has
                             coverage defect within the stated bound
                             and is non-toxic.

The worked examples show the point of a combination: two compounds
with coverage defect 2 each whose combination has defect 0 — each
covers features the other lacks.

Honest note: this is a formal prototype. Bitwise OR is an abstract
model of combined coverage, not pharmacology; synergy and antagonism
in the pharmacological sense, drug interactions, and dosing are not
modelled. What is proved (Q.E.D.) is the correctness of the
combination rules *inside the model*. Judgement of the model itself
is left to the reader.

Author: Takeo Yamamoto (GitHub: Takeo140)
License: Apache-2.0
-/

namespace AIDrugDiscoveryCombo

/-- A candidate compound: a molecular fingerprint as a list of bits,
    plus a toxicity flag. -/
structure Compound where
  fingerprint : List Bool
  toxic : Bool
deriving DecidableEq, Repr

/-- The number of `true` bits in a list. -/
def countTrue : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + countTrue bs

/-- The coverage defect of a fingerprint against a target profile:
    the number of positions where the target requires a feature the
    fingerprint does not have. A fingerprint shorter than the target
    leaves the remaining required features uncovered. -/
def uncovered : List Bool → List Bool → Nat
  | [], ts => countTrue ts
  | _ :: _, [] => 0
  | f :: fs, t :: ts => (if t && !f then 1 else 0) + uncovered fs ts

/-- The combined coverage of two fingerprints: a feature is covered
    when either fingerprint has it. -/
def zipOr : List Bool → List Bool → List Bool
  | [], ys => ys
  | x :: xs, [] => x :: xs
  | x :: xs, y :: ys => (x || y) :: zipOr xs ys

/-- The combination of two compounds: coverage is the union of the
    two fingerprints, and the combination is toxic when either
    compound is toxic. -/
def combine (a b : Compound) : Compound :=
  { fingerprint := zipOr a.fingerprint b.fingerprint,
    toxic := a.toxic || b.toxic }

/-- No fingerprint leaves more of the target uncovered than the whole
    target contains. -/
theorem uncovered_le_countTrue (f t : List Bool) :
    uncovered f t ≤ countTrue t := by
  induction f generalizing t with
  | nil => simp [uncovered]
  | cons x xs ih =>
    cases t with
    | nil => simp [uncovered]
    | cons s ss =>
      have hbit : (if s && !x then 1 else 0) ≤ (if s then 1 else 0) := by
        cases s <;> cases x <;> decide
      have h2 := ih (t := ss)
      have e1 : uncovered (x :: xs) (s :: ss)
          = (if s && !x then 1 else 0) + uncovered xs ss := by
        simp [uncovered]
      have e2 : countTrue (s :: ss)
          = (if s then 1 else 0) + countTrue ss := by
        simp [countTrue]
      rw [e1, e2]
      omega

/-- A combination never covers less than the first compound alone. -/
theorem uncovered_zipOr_le_left (f g t : List Bool) :
    uncovered (zipOr f g) t ≤ uncovered f t := by
  induction f generalizing g t with
  | nil => exact uncovered_le_countTrue g t
  | cons x xs ih =>
    cases g with
    | nil => simp [zipOr]
    | cons y ys =>
      cases t with
      | nil => simp [zipOr, uncovered]
      | cons s ss =>
        have hbit : (if s && !(x || y) then 1 else 0)
            ≤ (if s && !x then 1 else 0) := by
          cases s <;> cases x <;> cases y <;> decide
        have h2 := ih (g := ys) (t := ss)
        have e1 : uncovered (zipOr (x :: xs) (y :: ys)) (s :: ss)
            = (if s && !(x || y) then 1 else 0)
              + uncovered (zipOr xs ys) ss := by
          simp [zipOr, uncovered]
        have e2 : uncovered (x :: xs) (s :: ss)
            = (if s && !x then 1 else 0) + uncovered xs ss := by
          simp [uncovered]
        rw [e1, e2]
        omega

/-- Combined coverage does not depend on the order of the two
    fingerprints. -/
theorem zipOr_comm (f g : List Bool) : zipOr f g = zipOr g f := by
  induction f generalizing g with
  | nil => cases g <;> rfl
  | cons x xs ih =>
    cases g with
    | nil => rfl
    | cons y ys => simp [zipOr, Bool.or_comm, ih]

/-- A combination never covers less than the second compound alone. -/
theorem uncovered_zipOr_le_right (f g t : List Bool) :
    uncovered (zipOr f g) t ≤ uncovered g t := by
  rw [zipOr_comm]
  exact uncovered_zipOr_le_left g f t

/-- At the compound level: a combination's coverage defect is at most
    the first compound's. -/
theorem combine_uncovered_le_left (a b : Compound) (t : List Bool) :
    uncovered (combine a b).fingerprint t ≤ uncovered a.fingerprint t :=
  uncovered_zipOr_le_left _ _ _

/-- At the compound level: a combination's coverage defect is at most
    the second compound's. -/
theorem combine_uncovered_le_right (a b : Compound) (t : List Bool) :
    uncovered (combine a b).fingerprint t ≤ uncovered b.fingerprint t :=
  uncovered_zipOr_le_right _ _ _

/-- If one compound already covers the target, any combination with
    it covers the target too. -/
theorem combo_covers_of_left {a b : Compound} {t : List Bool}
    (h : uncovered a.fingerprint t = 0) :
    uncovered (combine a b).fingerprint t = 0 := by
  have hle := combine_uncovered_le_left a b t
  rw [h] at hle
  exact Nat.eq_zero_of_le_zero hle

/-- A combination is non-toxic exactly when both compounds are. -/
theorem combine_safe {a b : Compound} :
    (combine a b).toxic = false ↔ a.toxic = false ∧ b.toxic = false := by
  simp [combine]

/-- The combination does not depend on the order of the compounds. -/
theorem combine_comm (a b : Compound) : combine a b = combine b a := by
  obtain ⟨fa, ta⟩ := a
  obtain ⟨fb, tb⟩ := b
  simp [combine, zipOr_comm, Bool.or_comm]

/-- A decidable certificate for a proposed combination: the coverage
    defect against the target is within the bound `k`, and the
    combination is non-toxic. -/
def comboCertified (a b : Compound) (t : List Bool) (k : Nat) : Bool :=
  (uncovered (combine a b).fingerprint t ≤ k) && !(combine a b).toxic

/-- The certificate checker is sound: a certified pair really meets
    the stated bound and is non-toxic. -/
theorem comboCertified_ok {a b : Compound} {t : List Bool} {k : Nat}
    (h : comboCertified a b t k = true) :
    uncovered (combine a b).fingerprint t ≤ k
      ∧ (combine a b).toxic = false := by
  simp [comboCertified] at h
  exact h

/-- First worked example: each compound alone leaves two required
    features uncovered. -/
example :
    uncovered [true, false, false, true] [true, true, true, true]
      = 2 := by
  decide

/-- Second worked example: the other compound also leaves two. -/
example :
    uncovered [false, true, true, false] [true, true, true, true]
      = 2 := by
  decide

/-- Together they cover everything: the combination of the two
    defect-2 compounds has coverage defect 0. -/
example :
    uncovered
      (combine { fingerprint := [true, false, false, true], toxic := false }
               { fingerprint := [false, true, true, false], toxic := false }
      ).fingerprint [true, true, true, true] = 0 := by
  decide

/-- The same pair passes the certificate checker at bound 0. -/
example :
    comboCertified { fingerprint := [true, false, false, true], toxic := false }
      { fingerprint := [false, true, true, false], toxic := false }
      [true, true, true, true] 0 = true := by
  decide

/-- But a pair containing a toxic compound is toxic, however good
    its coverage. -/
example :
    (combine { fingerprint := [true], toxic := true }
             { fingerprint := [true], toxic := false }).toxic
      = true := by
  decide

end AIDrugDiscoveryCombo

#print axioms AIDrugDiscoveryCombo.uncovered_zipOr_le_left
#print axioms AIDrugDiscoveryCombo.uncovered_zipOr_le_right
#print axioms AIDrugDiscoveryCombo.combine_safe
#print axioms AIDrugDiscoveryCombo.comboCertified_ok
