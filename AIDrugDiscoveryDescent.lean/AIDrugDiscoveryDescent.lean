/-!
# AI Drug Discovery by Descent — proof-verified lead optimization

A third part of the proof-verified AI drug discovery line in this
repository. `AIDrugDiscovery` searches a finite library for the best
existing candidate, and `AIDrugDiscoveryExt` adds a fuller screen and a
certificate layer. This file covers the complementary half of a
discovery pipeline: **lead optimization** — improving a given candidate
until it matches the target profile.

The optimization is a descent, in the sense of the DescentCore line of
work:

* A **compound** is a molecular fingerprint — a list of bits — together
  with a toxicity flag.
* The **defect** of a compound against a target profile is the number
  of positions where the fingerprint disagrees with the target, plus
  the length difference.
* One **improvement step** repairs the first disagreeing position.
* **Optimization** iterates the step. Each step strictly lowers the
  defect, so the iteration provably settles — within at most the
  initial defect many steps — on the target profile itself.

Machine-checked properties (no `sorry` anywhere):

* `mismatch_improve_lt`    — one step strictly lowers a positive defect
                             (for equal-length fingerprints).
* `optimize_mismatch`      — after at most the initial defect many
                             steps, the defect is zero.
* `optimize_eq_target`     — the optimized fingerprint *is* the target
                             profile (for equal-length fingerprints).
* `optimizeCompound_safe`  — optimization never touches the toxicity
                             flag: a non-toxic lead stays non-toxic.
* `optimizeCompound_fingerprint` — at the compound level, optimization
                             reaches the target profile.

Honest note: this is a formal prototype. The defect is an abstract
model of lead optimization, not medicinal chemistry; what is proved
(Q.E.D.) is the correctness of the optimization *inside the model* —
that it terminates, within the stated bound, at the stated target.
Judgement of the model itself is left to the reader.

Author: Takeo Yamamoto (GitHub: Takeo140)
License: Apache-2.0
-/

namespace AIDrugDiscoveryDescent

/-- A candidate compound: a molecular fingerprint as a list of bits,
    plus a toxicity flag. -/
structure Compound where
  fingerprint : List Bool
  toxic : Bool
deriving DecidableEq, Repr

/-- The defect of a fingerprint against a target profile: the number of
    positions where they disagree, plus the length difference. -/
def mismatch : List Bool → List Bool → Nat
  | [], [] => 0
  | [], _ :: bs => bs.length + 1
  | _ :: as, [] => as.length + 1
  | a :: as, b :: bs => (if a = b then 0 else 1) + mismatch as bs

/-- One improvement step: repair the first position where the
    fingerprint disagrees with the target. Positions past the end of
    either list are left alone. -/
def improve : List Bool → List Bool → List Bool
  | [], _ => []
  | a :: as, [] => a :: as
  | a :: as, b :: bs => if a = b then a :: improve as bs else b :: as

/-- Optimization by descent: iterate `improve`, with `fuel` as the
    remaining step budget. -/
def optimize : Nat → List Bool → List Bool → List Bool
  | 0, f, _ => f
  | fuel + 1, f, t => if mismatch f t = 0 then f else optimize fuel (improve f t) t

/-- Optimization at the compound level: the fingerprint is optimized
    against the target profile; the toxicity flag is untouched. -/
def optimizeCompound (target : List Bool) (c : Compound) : Compound :=
  { c with fingerprint := optimize (mismatch c.fingerprint target) c.fingerprint target }

/-- The improvement step preserves the fingerprint's length when the
    fingerprint and the target have the same length. -/
theorem improve_length {f t : List Bool} (h : f.length = t.length) :
    (improve f t).length = f.length := by
  induction f generalizing t with
  | nil =>
    cases t with
    | nil => rfl
    | cons b bs => simp at h
  | cons a as ih =>
    cases t with
    | nil => simp at h
    | cons b bs =>
      have h' : as.length = bs.length := by simpa using h
      by_cases hab : a = b
      · simp [improve, hab, ih h']
      · simp [improve, hab]

/-- One improvement step strictly lowers a positive defect. -/
theorem mismatch_improve_lt {f t : List Bool} (h : f.length = t.length)
    (hne : mismatch f t ≠ 0) :
    mismatch (improve f t) t < mismatch f t := by
  induction f generalizing t with
  | nil =>
    cases t with
    | nil => simp [mismatch] at hne
    | cons b bs => simp at h
  | cons a as ih =>
    cases t with
    | nil => simp at h
    | cons b bs =>
      have h' : as.length = bs.length := by simpa using h
      by_cases hab : a = b
      · have hne' : mismatch as bs ≠ 0 := by
          have e : mismatch (a :: as) (b :: bs) = mismatch as bs := by
            simp [mismatch, hab]
          rw [e] at hne
          exact hne
        have ih' := ih h' hne'
        have e1 : improve (a :: as) (b :: bs) = a :: improve as bs := by
          simp [improve, hab]
        have e2 : mismatch (a :: improve as bs) (b :: bs)
            = mismatch (improve as bs) bs := by
          simp [mismatch, hab]
        have e3 : mismatch (a :: as) (b :: bs) = mismatch as bs := by
          simp [mismatch, hab]
        rw [e1, e2, e3]
        exact ih'
      · have e1 : improve (a :: as) (b :: bs) = b :: as := by
          simp [improve, hab]
        have e2 : mismatch (b :: as) (b :: bs) = mismatch as bs := by
          simp [mismatch]
        have e3 : mismatch (a :: as) (b :: bs) = 1 + mismatch as bs := by
          simp [mismatch, hab]
        rw [e1, e2, e3]
        omega

/-- A fingerprint with zero defect against an equal-length target is
    the target itself. -/
theorem mismatch_eq_zero {f t : List Bool} (h : f.length = t.length)
    (h0 : mismatch f t = 0) : f = t := by
  induction f generalizing t with
  | nil =>
    cases t with
    | nil => rfl
    | cons b bs => simp at h
  | cons a as ih =>
    cases t with
    | nil => simp at h
    | cons b bs =>
      have h' : as.length = bs.length := by simpa using h
      by_cases hab : a = b
      · have hm : mismatch as bs = 0 := by
          have e : mismatch (a :: as) (b :: bs) = mismatch as bs := by
            simp [mismatch, hab]
          rw [e] at h0
          exact h0
        have ih' := ih h' hm
        simp [hab, ih']
      · exfalso
        have e : mismatch (a :: as) (b :: bs) = 1 + mismatch as bs := by
          simp [mismatch, hab]
        rw [e] at h0
        omega

/-- Optimization preserves the fingerprint's length. -/
theorem optimize_length {fuel : Nat} {f t : List Bool} (h : f.length = t.length) :
    (optimize fuel f t).length = f.length := by
  induction fuel generalizing f with
  | zero => rfl
  | succ fuel ih =>
    by_cases h0 : mismatch f t = 0
    · simp [optimize, h0]
    · have e : optimize (fuel + 1) f t = optimize fuel (improve f t) t := by
        simp [optimize, h0]
      rw [e, ih ((improve_length h).trans h)]
      exact improve_length h

/-- The settling theorem: with a budget of the initial defect many
    steps, optimization always reaches defect zero. -/
theorem optimize_mismatch_aux {t : List Bool} :
    ∀ (fuel : Nat) {f : List Bool}, f.length = t.length →
      mismatch f t ≤ fuel → mismatch (optimize fuel f t) t = 0 := by
  intro fuel
  induction fuel with
  | zero =>
    intro f h hle
    have h0 : mismatch f t = 0 := Nat.eq_zero_of_le_zero hle
    simp [optimize, h0]
  | succ fuel ih =>
    intro f h hle
    by_cases h0 : mismatch f t = 0
    · simp [optimize, h0]
    · have e : optimize (fuel + 1) f t = optimize fuel (improve f t) t := by
        simp [optimize, h0]
      have hlt : mismatch (improve f t) t < mismatch f t :=
        mismatch_improve_lt h h0
      rw [e]
      exact ih ((improve_length h).trans h) (by omega)

/-- With the initial defect as the budget, optimization reaches
    defect zero: the iteration settles within the bound. -/
theorem optimize_mismatch {f t : List Bool} (h : f.length = t.length) :
    mismatch (optimize (mismatch f t) f t) t = 0 :=
  optimize_mismatch_aux (mismatch f t) h (Nat.le_refl _)

/-- The main guarantee: optimization turns an equal-length fingerprint
    into the target profile itself. -/
theorem optimize_eq_target {f t : List Bool} (h : f.length = t.length) :
    optimize (mismatch f t) f t = t := by
  have hlen : (optimize (mismatch f t) f t).length = t.length := by
    rw [optimize_length h, h]
  exact mismatch_eq_zero hlen (optimize_mismatch h)

/-- Optimization never touches the toxicity flag: a non-toxic lead
    stays non-toxic. -/
theorem optimizeCompound_safe {target : List Bool} {c : Compound}
    (h : c.toxic = false) : (optimizeCompound target c).toxic = false := by
  simp [optimizeCompound, h]

/-- At the compound level, optimization reaches the target profile. -/
theorem optimizeCompound_fingerprint {target : List Bool} {c : Compound}
    (h : c.fingerprint.length = target.length) :
    (optimizeCompound target c).fingerprint = target :=
  optimize_eq_target h

/-- A worked example, checked by computation: three disagreeing
    positions are repaired one by one, and the iteration lands exactly
    on the target profile. -/
example :
    optimize (mismatch [true, false, true, false] [true, true, false, false])
      [true, false, true, false] [true, true, false, false]
      = [true, true, false, false] := by
  decide

/-- The same example at the compound level. -/
example :
    optimizeCompound [true, true, false, false]
      { fingerprint := [true, false, true, false], toxic := false }
      = { fingerprint := [true, true, false, false], toxic := false } := by
  decide

end AIDrugDiscoveryDescent

#print axioms AIDrugDiscoveryDescent.optimize_eq_target
#print axioms AIDrugDiscoveryDescent.optimize_mismatch
#print axioms AIDrugDiscoveryDescent.optimizeCompound_fingerprint
