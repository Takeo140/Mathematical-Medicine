/-!
# AI Drug Discovery — a proof-verified prototype
 
A prototype of proof-verified AI drug discovery, in the line of the
Mathematical-Medicine formalization: where that work treats DNA bases as
bits, this file treats candidate compounds as bits.
 
Design:
 
* A **compound** is a molecular fingerprint — a list of bits — together
  with a toxicity flag (a decidable safety screen).
* A **target** is a binding profile, also a list of bits.
* The **binding score** counts the positions where a compound's
  fingerprint agrees with the target profile.
* **Search** is exhaustive machine search over a finite candidate
  library: it returns a non-toxic compound with maximal score.
 
Machine-checked properties (no `sorry` anywhere):
 
* `search_mem`        — the result is a member of the library.
* `search_safe`       — the result passes the toxicity screen.
* `search_optimal`    — no non-toxic candidate in the library scores
                        higher than the result.
* `search_complete`   — if any non-toxic candidate exists, the search
                        finds one (proved via `search_none_iff`).
 
Honest note: this is a formal prototype. The score is an abstract model
of binding, not pharmacology; what is proved (Q.E.D.) is the correctness
of the search *inside the model*. Judgement of the model itself is left
to the reader.
 
Author: Takeo Yamamoto (GitHub: Takeo140)
License: Apache-2.0
-/
 
namespace AIDrugDiscovery
 
/-- A candidate compound: a molecular fingerprint as a list of bits,
    plus a toxicity flag. -/
structure Compound where
  /-- Molecular fingerprint, as bits. -/
  fp : List Bool
  /-- Toxicity screen: `true` means the compound is rejected. -/
  toxic : Bool
deriving DecidableEq, Repr
 
/-- A target binding profile, as a list of bits. -/
abbrev Target := List Bool
 
/-- Binding score: the number of positions where the compound's
    fingerprint agrees with the target profile. -/
def score (t : Target) (c : Compound) : Nat :=
  (t.zip c.fp).countP (fun p => p.1 == p.2)
 
/-- Of two compounds, keep the one with the higher score against `t`
    (ties keep the first). -/
def better (t : Target) (a b : Compound) : Compound :=
  if score t b ≤ score t a then a else b
 
/-- One step of the search: consider candidate `c` against the best
    candidate found so far (`acc`). Toxic candidates are skipped;
    a safe candidate replaces `acc` if it scores at least as well. -/
def step (t : Target) (c : Compound) (acc : Option Compound) : Option Compound :=
  if c.toxic then acc
  else match acc with
    | none => some c
    | some b => some (better t c b)
 
/-- Exhaustive search over a finite candidate library: returns a
    non-toxic compound of maximal score, or `none` if every candidate
    is toxic (or the library is empty). -/
def search (t : Target) (cs : List Compound) : Option Compound :=
  cs.foldr (step t) none
 
theorem search_cons (t : Target) (c : Compound) (cs : List Compound) :
    search t (c :: cs) = step t c (search t cs) := rfl
 
/-! ## Properties of `better` -/
 
theorem better_score_left (t : Target) (a b : Compound) :
    score t a ≤ score t (better t a b) := by
  unfold better
  split
  · exact Nat.le_refl _
  · exact Nat.le_of_lt (Nat.lt_of_not_le ‹_›)
 
theorem better_score_right (t : Target) (a b : Compound) :
    score t b ≤ score t (better t a b) := by
  unfold better
  split
  · exact ‹score t b ≤ score t a›
  · exact Nat.le_refl _
 
theorem better_mem (t : Target) (a b : Compound) :
    better t a b = a ∨ better t a b = b := by
  unfold better
  split
  · exact Or.inl rfl
  · exact Or.inr rfl
 
/-! ## Properties of `step` -/
 
theorem step_eq_none {t : Target} {c : Compound} {acc : Option Compound} :
    step t c acc = none ↔ acc = none ∧ c.toxic = true := by
  constructor
  · intro h
    by_cases htox : c.toxic = true
    · refine ⟨?_, htox⟩
      unfold step at h
      rw [ite_eq_left htox] at h
      exact h
    · exfalso
      have hcf : c.toxic = false := Bool.eq_false_iff.mpr htox
      unfold step at h
      rw [ite_eq_right htox] at h
      cases acc with
      | none => simp at h
      | some b => simp at h
  · rintro ⟨rfl, htox⟩
    unfold step
    rw [ite_eq_left htox]
 
theorem step_some {t : Target} {c : Compound} {acc : Option Compound} {b : Compound}
    (h : step t c acc = some b) : b = c ∨ acc = some b := by
  by_cases htox : c.toxic = true
  · unfold step at h
    rw [ite_eq_left htox] at h
    exact Or.inr h
  · unfold step at h
    rw [ite_eq_right htox] at h
    cases acc with
    | none =>
        simp at h
        exact Or.inl h.symm
    | some b' =>
        have hb : better t c b' = b := Option.some.inj h
        rcases better_mem t c b' with hm | hm
        · exact Or.inl (hb.symm.trans hm)
        · exact Or.inr (by rw [← hb, hm])
 
theorem step_safe {t : Target} {c : Compound} {acc : Option Compound} {b : Compound}
    (hacc : ∀ a : Compound, acc = some a → a.toxic = false)
    (h : step t c acc = some b) : b.toxic = false := by
  by_cases htox : c.toxic = true
  · unfold step at h
    rw [ite_eq_left htox] at h
    exact hacc b h
  · have hcf : c.toxic = false := Bool.eq_false_iff.mpr htox
    unfold step at h
    rw [ite_eq_right htox] at h
    cases acc with
    | none =>
        simp at h
        rw [← h]
        exact hcf
    | some b' =>
        have hb : better t c b' = b := Option.some.inj h
        rcases better_mem t c b' with hm | hm
        · rw [← hb, hm]; exact hcf
        · rw [← hb, hm]; exact hacc b' rfl
 
theorem step_score_acc {t : Target} {c : Compound} {acc : Option Compound} {b : Compound}
    (h : step t c acc = some b) :
    ∀ a : Compound, acc = some a → score t a ≤ score t b := by
  intro a ha
  by_cases htox : c.toxic = true
  · unfold step at h
    rw [ite_eq_left htox] at h
    have hab : a = b := Option.some.inj (ha.symm.trans h)
    rw [hab]
    exact Nat.le_refl _
  · unfold step at h
    rw [ite_eq_right htox] at h
    cases acc with
    | none => cases ha
    | some b' =>
        have haa : a = b' := (Option.some.inj ha).symm
        have hb : better t c b' = b := Option.some.inj h
        rw [haa, ← hb]
        exact better_score_right t c b'
 
theorem step_score_head {t : Target} {c : Compound} {acc : Option Compound} {b : Compound}
    (hc : c.toxic = false) (h : step t c acc = some b) :
    score t c ≤ score t b := by
  have htox : ¬ (c.toxic = true) := by simp [hc]
  unfold step at h
  rw [ite_eq_right htox] at h
  cases acc with
  | none =>
      simp at h
      cases h
      exact Nat.le_refl _
  | some b' =>
      have hb : better t c b' = b := Option.some.inj h
      rw [← hb]
      exact better_score_left t c b'
 
/-! ## Correctness of `search` -/
 
/-- The search result comes from the library. -/
theorem search_mem (t : Target) :
    ∀ (cs : List Compound) (b : Compound), search t cs = some b → b ∈ cs := by
  intro cs
  induction cs with
  | nil => intro b h; simp [search] at h
  | cons c cs ih =>
      intro b h
      rw [search_cons] at h
      rcases step_some h with rfl | hacc
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih _ hacc)
 
/-- The search result is non-toxic. -/
theorem search_safe (t : Target) :
    ∀ (cs : List Compound) (b : Compound),
      search t cs = some b → b.toxic = false := by
  intro cs
  induction cs with
  | nil => intro b h; simp [search] at h
  | cons c cs ih =>
      intro b h
      rw [search_cons] at h
      exact step_safe ih h
 
/-- The search fails exactly when every candidate is toxic. -/
theorem search_none_iff (t : Target) :
    ∀ (cs : List Compound),
      search t cs = none ↔ ∀ c ∈ cs, c.toxic = true := by
  intro cs
  induction cs with
  | nil => simp [search]
  | cons c cs ih =>
      rw [search_cons, step_eq_none, ih]
      constructor
      · rintro ⟨hcs, hc⟩ d hd
        rcases List.mem_cons.mp hd with rfl | hd'
        · exact hc
        · exact hcs _ hd'
      · intro h
        exact ⟨fun d hd => h d (List.mem_cons_of_mem _ hd),
               h c List.mem_cons_self⟩
 
/-- Optimality: no non-toxic candidate scores higher than the result. -/
theorem search_optimal (t : Target) :
    ∀ (cs : List Compound) (b : Compound), search t cs = some b →
      ∀ c ∈ cs, c.toxic = false → score t c ≤ score t b := by
  intro cs
  induction cs with
  | nil => intro b h; simp [search] at h
  | cons c cs ih =>
      intro b h d hd hdtox
      rw [search_cons] at h
      rcases List.mem_cons.mp hd with rfl | hd'
      · exact step_score_head hdtox h
      · cases hacc : search t cs with
        | none =>
            have := (search_none_iff t cs).mp hacc d hd'
            rw [this] at hdtox
            cases hdtox
        | some b' =>
            rw [hacc] at h
            exact Nat.le_trans (ih _ hacc _ hd' hdtox) (step_score_acc h _ rfl)
 
/-- Completeness: if a non-toxic candidate exists, the search finds one. -/
theorem search_complete (t : Target) {cs : List Compound} :
    (∃ c ∈ cs, c.toxic = false) → ∃ b, search t cs = some b := by
  intro h
  cases hsearch : search t cs with
  | some b => exact ⟨b, rfl⟩
  | none =>
      exfalso
      rcases h with ⟨c, hc, hctox⟩
      have htoxic := (search_none_iff t cs).mp hsearch c hc
      rw [htoxic] at hctox
      cases hctox
 
/-! ## A worked example
 
The library below contains a perfect-matching compound that is toxic
and must be rejected, and a perfect-matching compound that is safe.
The search must return the safe one. -/
 
/-- Toy target profile. -/
def demoTarget : Target := [true, false, true, true]
 
/-- Toy candidate library: an imperfect safe compound, a perfect but
    toxic compound, and a perfect safe compound. -/
def demoLibrary : List Compound :=
  [ ⟨[true, false, true, false], false⟩,
    ⟨[true, false, true, true], true⟩,
    ⟨[true, false, true, true], false⟩ ]
 
/-- The search returns the perfect safe compound. -/
example : search demoTarget demoLibrary = some ⟨[true, false, true, true], false⟩ := by
  decide
 
/-- Its score is the maximum possible for this target: 4. -/
example : score demoTarget ⟨[true, false, true, true], false⟩ = 4 := by
  decide
 
end AIDrugDiscovery
 
/-! ## Axiom check
 
The main theorems must depend only on the standard axioms
(`propext`, `Classical.choice`, `Quot.sound`) — in particular,
no `sorryAx`. -/
 
#print axioms AIDrugDiscovery.search_mem
#print axioms AIDrugDiscovery.search_safe
#print axioms AIDrugDiscovery.search_optimal
#print axioms AIDrugDiscovery.search_complete

