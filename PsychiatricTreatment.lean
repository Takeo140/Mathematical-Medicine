License Apache-2.0  Takeo Yamamoto
import Mathlib.Data.Rat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace PsychiatricTreatmentModel

/- =========================================================
   §1  脳領域・神経修復因子・Blueprint の定義
   ========================================================= -/

inductive BrainRegion : Type
  | PrefrontalCortex | Amygdala | Hippocampus | Striatum
  deriving Repr, DecidableEq, BEq

inductive NeuroFactor : Type
  | BDNF | SerotoninModulator | GABARegulator | DopamineStabilizer
  deriving Repr, DecidableEq, BEq

/-- 神経回路修復・治療プロトコルを駆動する設計図 -/
structure NeuroBlueprint where
  target_region : BrainRegion
  factors       : List NeuroFactor
  potency       : ℚ  -- 介入効率係数
  deriving Repr, DecidableEq, BEq

structure PsychiatricState where
  symptom_score    : ℚ  -- 症状・病理スコア (0: 寛解・正常, 1: 重度障害)
  plasticity_index : ℚ  -- 神経可塑性・修復力 (0: 固着・低下, 1: 正常柔軟性)
  instability_risk : ℚ  -- 不安定性・過剰興奮リスク (0: 安全, 1: 危険限界)
  deriving Repr, DecidableEq

/-- 完全安定化（Complete Stabilization / 寛解）の定義述語 -/
def IsFullyStabilized (s : PsychiatricState) : Prop :=
  s.symptom_score = 0 ∧
  s.plasticity_index = 1 ∧
  s.instability_risk = 0

instance (s : PsychiatricState) : Decidable (IsFullyStabilized s) := by
  unfold IsFullyStabilized; infer_instance

/- =========================================================
   §2  安全核（Safety Kernel）
   ========================================================= -/

def safety_kernel (w d : ℚ) : ℚ :=
  let raw := w + d
  if raw > 5 then 5
  else if raw < -5 then -5
  else raw

theorem safety_kernel_bounded (w d : ℚ) :
    -5 ≤ safety_kernel w d ∧ safety_kernel w d ≤ 5 := by
  unfold safety_kernel
  split_ifs with h1 h2
  · exact ⟨by linarith, by linarith⟩
  · exact ⟨by linarith, by linarith⟩
  · exact ⟨by linarith, by linarith⟩

/- =========================================================
   §3  神経回路・状態遷移モデルと不変量証明
   ========================================================= -/

/-- 
  【神経状態遷移関数】
  NeuroBlueprint の入力に基づき、症状スコアを 0 へ、可塑性を 1 へ収束させる。
  安定化達成後はホメオスタシスを維持する。
-/
def psych_step_transition (bp : NeuroBlueprint) (s : PsychiatricState) : PsychiatricState :=
  if s.symptom_score = 0 ∧ s.plasticity_index = 1 ∧ s.instability_risk = 0 then
    { symptom_score := 0, plasticity_index := 1, instability_risk := 0 }
  else
    let step_rate := if bp.factors.length > 0 then 0.1 else 0.05
    let next_sym  := if s.symptom_score ≤ step_rate then 0 else s.symptom_score - step_rate
    let next_plas := if s.plasticity_index >= 0.9 then 1 else s.plasticity_index + step_rate
    { symptom_score    := next_sym,
      plasticity_index := next_plas,
      instability_risk := 0 }

/-- 【定理】一度完全安定化に達した精神・神経系は、どの Blueprint が作用してもその状態を永久に維持する -/
theorem psych_state_is_invariant (bp : NeuroBlueprint) (s : PsychiatricState) (hs : IsFullyStabilized s) :
    IsFullyStabilized (psych_step_transition bp s) := by
  unfold IsFullyStabilized psych_step_transition
  rcases hs with ⟨rfl, rfl, rfl⟩
  simp

/- =========================================================
   §4  軌跡シミュレーション
   ========================================================= -/

def run_psych_trajectory (bp : NeuroBlueprint) (s : PsychiatricState) : Nat → PsychiatricState
  | 0 => s
  | n + 1 => psych_step_transition bp (run_psych_trajectory bp s n)

def standard_neuro_blueprint : NeuroBlueprint :=
  { target_region := BrainRegion.PrefrontalCortex
    factors       := [NeuroFactor.BDNF, NeuroFactor.SerotoninModulator]
    potency       := 1.0 }

def initial_psych_patient : PsychiatricState :=
  { symptom_score := 0.85, plasticity_index := 0.10, instability_risk := 0.03 }

/-- 10ステップ経過後の状態評価 -/
#eval run_psych_trajectory standard_neuro_blueprint initial_psych_patient 10

/-- 15ステップ経過後の状態評価（完全安定化達成） -/
#eval run_psych_trajectory standard_neuro_blueprint initial_psych_patient 15

/-- 15ステップ後の状態が完全安定化（IsFullyStabilized）を満たしているかの判定 -/
#eval decide (IsFullyStabilized (run_psych_trajectory standard_neuro_blueprint initial_psych_patient 15))

end PsychiatricTreatmentModel
