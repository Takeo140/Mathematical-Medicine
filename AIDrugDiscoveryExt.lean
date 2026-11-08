/-!
# AI Drug Discovery, Extended — proof-verified screening with certificates

An extended version of the `AIDrugDiscovery` prototype. Where the first
version screened candidates by a single toxicity flag and a binding score,
this version models a fuller discovery pipeline:

* A **compound** is a molecular fingerprint (a list of bits), a toxicity
  flag, and a solubility score.
* A **problem** gives an on-target profile, an off-target (anti-target)
  profile, and a **specification**: minimum solubility and a cap on
  off-target binding.
* The **screen** (`passes`) admits a compound only if it is non-toxic,
  soluble enough, and selective enough (off-target matches at most the cap).
* The **objective** is selectivity: on-target matches minus off-target
  matches. **Search** exhaustively returns an admitted compound of
  maximal selectivity.
* A **certificate layer** (`certify`): an external proposer — an AI
  model, a human, another program — may propose any candidate, and
  `certify` checks, inside the same formal system, that the proposal is
  in the library, passes the screen, and is optimal among admitted
  compounds. AI proposes; the proof system certifies.

Machine-checked properties (no `sorry` anywhere):

* `search_mem`        — the result is a member of the library.
* `search_passes`     — the result passes the screen.
* `search_optimal`    — no admitted candidate has higher selectivity.
* `search_complete`   — if any admitted candidate exists, search finds one.
* `certify_sound`     — a certified candidate really is in the library,
                        passes the screen, and is optimal.
* `certify_complete`  — every truly optimal admitted member certifies.
* `search_certified`  — whatever the search returns passes certification.

Honest note: this is a formal prototype. The scores are abstract models
of binding, solubility and selectivity, not pharmacology; what is proved
(Q.E.D.) is the correctness of the screening, the search and the
certification *inside the model*. The bridge to clinical reality belongs
to experiments and trials, as with any model of a drug.

Author: Takeo Yamamoto (GitHub: Takeo140)
License: Apache-2.0
-/

namespace AIDrugDiscoveryExt

/-- A candidate compound: a molecular fingerprint as a list of bits,
    a toxicity flag, and a solubility score (higher is more soluble). -/
structure Compound where
  /-- Molecular fingerprint, as bits. -/
  fp : List Bool
  /-- Toxicity screen: `true` means the compound is rejected. -/
  toxic : Bool
  /-- Solubility score (abstract units). -/
  solubility : Nat
deriving DecidableEq, Repr

/-- The screening specification: minimum solubility and the maximum
    number of off-target matches a compound may have. -/
structure Spec where
  /-- Minimum solubility for admission. -/
  minSolubility : Nat
  /-- Maximum allowed off-target matches. -/
  maxOffTarget : Nat
deriving DecidableEq, Repr

/-- A discovery problem: an on-target profile, an off-target profile,
    and the screening specification. -/
structure Problem where
  /-- On-target binding profile, as bits. -/
  target : List Bool
  /-- Off-target (anti-target) binding profile, as bits. -/
  anti : List Bool
  /-- Screening specification. -/
  spec : Spec
deriving DecidableEq, Repr

/-- Number of positions where a fingerprint agrees with a profile. -/
def matchCount (profile fp : List Bool) : Nat :=
  (profile.zip fp).countP (fun p => p.1 == p.2)

/-- On-target score of a compound. -/
def onScore (p : Problem) (c : Compound) : Nat := matchCount p.target c.fp

/-- Off-target score of a compound. -/
def offScore (p : Problem) (c : Compound) : Nat := matchCount p.anti c.fp

/-- Selectivity: on-target matches minus off-target matches. -/
def selectivity (p : Problem) (c : Compound) : Int :=
  (onScore p c : Int) - (offScore p c : Int)

/-- The admission screen: non-toxic, soluble enough, and off-target
    binding within the cap. -/
def passes (p : Problem) (c : Compound) : Bool :=
  !c.toxic && (p.spec.minSolubility ≤ c.solubility) && (offScore p c ≤ p.spec.maxOffTarget)

/-- Of two compounds, keep the one with higher selectivity against `p`
    (ties keep the first). -/
def better (p : Problem) (a b : Compound) : Compound :=
  if selectivity p b ≤ selectivity p a then a else b

/-- One step of the search: consider candidate `c` against the best
    candidate found so far (`acc`). Candidates failing the screen are
    skipped; an admitted candidate replaces `acc` if its selectivity is
    at least as high. -/
def step (p : Problem) (c : Compound) (acc : Option Compound) : Option Compound :=
  match passes p c with
  | false => acc
  | true =>
    match acc with
    | none => some c
    | some b => some (better p c b)

/-- Exhaustive search over a finite candidate library: returns an
    admitted compound of maximal selectivity, or `none` if no candidate
    passes the screen. -/
def search (p : Problem) (cs : List Compound) : Option Compound :=
  cs.foldr (step p) none

theorem search_cons (p : Problem) (c : Compound) (cs : List Compound) :
    search p (c :: cs) = step p c (search p cs) := rfl

/-! ## Properties of `better` -/

theorem better_sel_left (p : Problem) (a b : Compound) :
    selectivity p a ≤ selectivity p (better p a b) := by
  unfold better
  split
  · exact Int.le_refl _
  · omega

theorem better_sel_right (p : Problem) (a b : Compound) :
    selectivity p b ≤ selectivity p (better p a b) := by
  unfold better
  split
  · exact ‹selectivity p b ≤ selectivity p a›
  · exact Int.le_refl _

theorem better_mem (p : Problem) (a b : Compound) :
    better p a b = a ∨ better p a b = b := by
  unfold better
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-! ## Properties of `step` -/

theorem step_eq_none {p : Problem} {c : Compound} {acc : Option Compound} :
    step p c acc = none ↔ acc = none ∧ passes p c = false := by
  constructor
  · intro h
    cases hp : passes p c with
    | false =>
        rw [show step p c acc = acc from by simp [step, hp]] at h
        exact ⟨h, rfl⟩
    | true =>
        exfalso
        cases acc with
        | none => simp [step, hp] at h
        | some b => simp [step, hp] at h
  · rintro ⟨rfl, hp⟩
    simp [step, hp]

theorem step_some {p : Problem} {c : Compound} {acc : Option Compound} {b : Compound}
    (h : step p c acc = some b) : b = c ∨ acc = some b := by
  cases hp : passes p c with
  | false =>
      rw [show step p c acc = acc from by simp [step, hp]] at h
      exact Or.inr h
  | true =>
      cases acc with
      | none =>
          have : step p c none = some c := by simp [step, hp]
          rw [this] at h
          exact Or.inl (Option.some.inj h).symm
      | some b' =>
          have hb : step p c (some b') = some (better p c b') := by simp [step, hp]
          rw [hb] at h
          have hbb : better p c b' = b := Option.some.inj h
          rcases better_mem p c b' with hm | hm
          · exact Or.inl (hbb.symm.trans hm)
          · exact Or.inr (by rw [← hbb, hm])

theorem step_passes {p : Problem} {c : Compound} {acc : Option Compound} {b : Compound}
    (hacc : ∀ a : Compound, acc = some a → passes p a = true)
    (h : step p c acc = some b) : passes p b = true := by
  cases hp : passes p c with
  | false =>
      rw [show step p c acc = acc from by simp [step, hp]] at h
      exact hacc b h
  | true =>
      cases acc with
      | none =>
          have hstep : step p c none = some c := by simp [step, hp]
          rw [hstep] at h
          have : b = c := (Option.some.inj h).symm
          rw [this]; exact hp
      | some b' =>
          have hb : step p c (some b') = some (better p c b') := by simp [step, hp]
          rw [hb] at h
          have hbb : better p c b' = b := Option.some.inj h
          rcases better_mem p c b' with hm | hm
          · rw [← hbb, hm]; exact hp
          · rw [← hbb, hm]; exact hacc b' rfl

theorem step_sel_acc {p : Problem} {c : Compound} {acc : Option Compound} {b : Compound}
    (h : step p c acc = some b) :
    ∀ a : Compound, acc = some a → selectivity p a ≤ selectivity p b := by
  intro a ha
  cases hp : passes p c with
  | false =>
      rw [show step p c acc = acc from by simp [step, hp]] at h
      have hab : a = b := Option.some.inj (ha.symm.trans h)
      rw [hab]
      exact Int.le_refl _
  | true =>
      cases acc with
      | none => cases ha
      | some b' =>
          have haa : a = b' := (Option.some.inj ha).symm
          have hb : step p c (some b') = some (better p c b') := by simp [step, hp]
          rw [hb] at h
          have hbb : better p c b' = b := Option.some.inj h
          rw [haa, ← hbb]
          exact better_sel_right p c b'

theorem step_sel_head {p : Problem} {c : Compound} {acc : Option Compound} {b : Compound}
    (hc : passes p c = true) (h : step p c acc = some b) :
    selectivity p c ≤ selectivity p b := by
  cases acc with
  | none =>
      have hstep : step p c none = some c := by simp [step, hc]
      rw [hstep] at h
      have : b = c := (Option.some.inj h).symm
      rw [this]
      exact Int.le_refl _
  | some b' =>
      have hb : step p c (some b') = some (better p c b') := by simp [step, hc]
      rw [hb] at h
      have hbb : better p c b' = b := Option.some.inj h
      rw [← hbb]
      exact better_sel_left p c b'

/-! ## Correctness of `search` -/

/-- The search result comes from the library. -/
theorem search_mem (p : Problem) :
    ∀ (cs : List Compound) (b : Compound), search p cs = some b → b ∈ cs := by
  intro cs
  induction cs with
  | nil => intro b h; simp [search] at h
  | cons c cs ih =>
      intro b h
      rw [search_cons] at h
      rcases step_some h with rfl | hacc
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih _ hacc)

/-- The search result passes the screen. -/
theorem search_passes (p : Problem) :
    ∀ (cs : List Compound) (b : Compound),
      search p cs = some b → passes p b = true := by
  intro cs
  induction cs with
  | nil => intro b h; simp [search] at h
  | cons c cs ih =>
      intro b h
      rw [search_cons] at h
      exact step_passes ih h

/-- The search fails exactly when no candidate passes the screen. -/
theorem search_none_iff (p : Problem) :
    ∀ (cs : List Compound),
      search p cs = none ↔ ∀ c ∈ cs, passes p c = false := by
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

/-- Optimality: no admitted candidate has higher selectivity than
    the result. -/
theorem search_optimal (p : Problem) :
    ∀ (cs : List Compound) (b : Compound), search p cs = some b →
      ∀ c ∈ cs, passes p c = true → selectivity p c ≤ selectivity p b := by
  intro cs
  induction cs with
  | nil => intro b h; simp [search] at h
  | cons c cs ih =>
      intro b h d hd hdpass
      rw [search_cons] at h
      rcases List.mem_cons.mp hd with rfl | hd'
      · exact step_sel_head hdpass h
      · cases hacc : search p cs with
        | none =>
            have := (search_none_iff p cs).mp hacc d hd'
            rw [this] at hdpass
            cases hdpass
        | some b' =>
            rw [hacc] at h
            exact Int.le_trans (ih _ hacc _ hd' hdpass) (step_sel_acc h _ rfl)

/-- Completeness: if an admitted candidate exists, the search finds one. -/
theorem search_complete (p : Problem) {cs : List Compound} :
    (∃ c ∈ cs, passes p c = true) → ∃ b, search p cs = some b := by
  intro h
  cases hsearch : search p cs with
  | some b => exact ⟨b, rfl⟩
  | none =>
      exfalso
      rcases h with ⟨c, hc, hcpass⟩
      have hfail := (search_none_iff p cs).mp hsearch c hc
      rw [hfail] at hcpass
      cases hcpass

/-! ## The certificate layer

An external proposer — an AI model, a human, another program — may
propose any candidate compound. `certify` checks the proposal inside
the formal system: the candidate must be in the library, pass the
screen, and be optimal among admitted compounds. -/

/-- The certification statement: `cand` is a member of the library,
    passes the screen, and no admitted member has higher selectivity. -/
def Certified (p : Problem) (cs : List Compound) (cand : Compound) : Prop :=
  cand ∈ cs ∧ passes p cand = true ∧
    ∀ c ∈ cs, passes p c = true → selectivity p c ≤ selectivity p cand

instance (p : Problem) (cs : List Compound) (cand : Compound) :
    Decidable (Certified p cs cand) := by
  unfold Certified
  infer_instance

/-- The certificate checker: `true` exactly for certified candidates. -/
def certify (p : Problem) (cs : List Compound) (cand : Compound) : Bool :=
  decide (Certified p cs cand)

/-- Soundness: a certified candidate really is in the library, passes
    the screen, and is optimal among admitted compounds. -/
theorem certify_sound {p : Problem} {cs : List Compound} {cand : Compound} :
    certify p cs cand = true → Certified p cs cand :=
  of_decide_eq_true

/-- Completeness of certification: every candidate that truly is an
    optimal admitted member of the library certifies. -/
theorem certify_complete {p : Problem} {cs : List Compound} {cand : Compound} :
    Certified p cs cand → certify p cs cand = true := by
  intro h
  simp only [certify, decide_eq_true_eq]
  exact h

/-- Whatever the search returns is certified: the pipeline's own
    proposals pass the certificate check by construction. -/
theorem search_certified {p : Problem} {cs : List Compound} {b : Compound}
    (h : search p cs = some b) : certify p cs b = true :=
  certify_complete ⟨search_mem p cs b h, search_passes p cs b h,
    search_optimal p cs b h⟩

/-! ## A worked example

Against the demo problem below: one compound matches the target
perfectly but is toxic; one is potent but binds the anti-target too
much and fails the selectivity screen; one passes everything with the
best selectivity and must win; one passes but is weaker. -/

/-- Toy discovery problem. -/
def demoProblem : Problem where
  target := [true, true, false, true, false]
  anti := [false, true, false, false, true]
  spec := { minSolubility := 50, maxOffTarget := 2 }

/-- Toy candidate library: perfect but toxic; potent but unselective;
    selective and admissible; admissible but weaker. -/
def demoLibrary : List Compound :=
  [ ⟨[true, true, false, true, false], true, 90⟩,
    ⟨[true, true, false, true, true], false, 80⟩,
    ⟨[true, false, false, true, false], false, 70⟩,
    ⟨[true, false, true, false, false], false, 90⟩ ]

/-- The winner of the demo library. -/
def demoWinner : Compound := ⟨[true, false, false, true, false], false, 70⟩

/-- The search returns the selective admissible compound. -/
example : search demoProblem demoLibrary = some demoWinner := by decide

/-- Its selectivity is 3 (4 on-target matches, 1 off-target match). -/
example : selectivity demoProblem demoWinner = 3 := by decide

/-- The winner is certified. -/
example : certify demoProblem demoLibrary demoWinner = true := by decide

/-- The weaker admissible compound is not certified: it is not optimal. -/
example : certify demoProblem demoLibrary
    ⟨[true, false, true, false, false], false, 90⟩ = false := by decide

/-- The unselective compound is not certified: it fails the screen. -/
example : certify demoProblem demoLibrary
    ⟨[true, true, false, true, true], false, 80⟩ = false := by decide

end AIDrugDiscoveryExt

/-! ## Axiom check

The main theorems must depend only on the standard axioms
(`propext`, `Classical.choice`, `Quot.sound`) — in particular,
no `sorryAx`. -/

#print axioms AIDrugDiscoveryExt.search_mem
#print axioms AIDrugDiscoveryExt.search_passes
#print axioms AIDrugDiscoveryExt.search_optimal
#print axioms AIDrugDiscoveryExt.search_complete
#print axioms AIDrugDiscoveryExt.certify_sound
#print axioms AIDrugDiscoveryExt.certify_complete
#print axioms AIDrugDiscoveryExt.search_certified
