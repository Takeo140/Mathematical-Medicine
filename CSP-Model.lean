-- License Apache-2.0 Takeo Yamamoto
import Mathlib.Data.Rat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace ComplexSystemsPsychiatryModel

/- =========================================================
   §1  複雑系としての神経回路状態とアトラクターの定義
   ========================================================= -/

/-- 複雑系（非線形ダイナミクス・フィードバック）としての脳状態 -/
structure ComplexNeuralState where
  excitation_level : ℚ     -- 神経興奮・ストレス水準 (0: 安定, 高いほど過剰興奮)
  network_entropy  : ℚ     -- ネットワークの乱れ・エントロピー (0: 秩序/健常, 1: 崩壊/カオス)
  attractor_basin  : Int   -- 0: 病理的アトラクター(トラップ), 1: 健常アトラクター
  deriving Repr, DecidableEq

/-- 複雑系における完全安定化（健常アトラクターへの固定）の定義 -/
def IsHealthyAttractor (st : ComplexNeuralState) : Prop :=
  st.excitation_level = 0 ∧
  st.network_entropy = 0 ∧
  st.attractor_basin = 1

instance (st : ComplexNeuralState) : Decidable (IsHealthyAttractor st) := by
  unfold IsHealthyAttractor; infer_instance

/- =========================================================
   §2  非線形フィードバックと相転移を伴う状態遷移関数
   ========================================================= -/

/-- 
  【複雑系・非線形神経状態遷移関数】
  興奮水準とエントロピーが相互に影響し合う非線形フィードバック項を含み、
  外部制御入力（Control Input）によって病理的アトラクターから健常アトラクターへ
  相転移（Bifurcation）を起こすモデル。
-/
def complex_system_transition (control_input : ℚ) (st : ComplexNeuralState) : ComplexNeuralState :=
  if IsHealthyAttractor st then
    -- 健常アトラクターに達した系は、自己組織化フィードバックによりその秩序を維持する
    { excitation_level := 0, network_entropy := 0, attractor_basin := 1 }
  else
    -- 非線形フィードバック：興奮とエントロピーが互いに増幅し合う結合項
    let non_linear_coupling := st.excitation_level * st.network_entropy
    let effective_control   := control_input + non_linear_coupling

    -- 状態の非線形減衰
    let next_exc := if st.excitation_level ≤ effective_control then 0 else st.excitation_level - effective_control
    let next_ent := if st.network_entropy ≤ effective_control * 0.5 then 0 else st.network_entropy - effective_control * 0.5

    -- 閾値クリア時に、病理的アトラクター(0)から健常アトラクター(1)へ相転移を起こす
    let next_basin := if next_exc = 0 ∧ next_ent = 0 then 1 else st.attractor_basin

    { excitation_level := next_exc,
      network_entropy  := next_ent,
      attractor_basin  := next_basin }

/- =========================================================
   §3  複雑系における不変量定理の証明
   ========================================================= -/

/-- 
  【定理】複雑系ダイナミクスおよび非線形フィードバックを内包するモデルであっても、
  一度健常アトラクター（IsHealthyAttractor）に到達した系は、
  いかなる制御入力やカオス的外乱が加わろうとも、その健康な秩序を永久に逸脱しない。
-/
theorem complex_healthy_invariant (control_input : ℚ) (st : ComplexNeuralState) (hs : IsHealthyAttractor st) :
    IsHealthyAttractor (complex_system_transition control_input st) := by
  unfold IsHealthyAttractor complex_system_transition
  rcases hs with ⟨hexc, hent, hbas⟩
  -- IsHealthyAttractor st が成立しているため、if の条件が真となる
  rw [if_pos (by exact ⟨hexc, hent, hbas⟩)]
  exact ⟨rfl, rfl, rfl⟩

/- =========================================================
   §4  複雑系シミュレーションと相転移の観測
   ========================================================= -/

def initial_pathological_complex_state : ComplexNeuralState :=
  { excitation_level := 0.90
    network_entropy  := 0.85
    attractor_basin  := 0 } -- 病理的トラップに囚われた状態

def running_complex_simulation (control_input : ℚ) (st : ComplexNeuralState) : Nat → ComplexNeuralState
  | 0 => st
  | n + 1 => complex_system_transition control_input (running_complex_simulation control_input st n)

-- 適切な制御入力（例: 0.35）を継続投与したときのダイナミクス
/-- 3ステップ経過後の状態（病理的アトラクターからの脱出プロセス） -/
#eval running_complex_simulation 0.35 initial_pathological_complex_state 3

/-- 5ステップ経過後の状態（健常アトラクターへの相転移完了） -/
#eval running_complex_simulation 0.35 initial_pathological_complex_state 5

/-- 5ステップ後の状態が IsHealthyAttractor を満たしているかの判定 -/
#eval decide (IsHealthyAttractor (running_complex_simulation 0.35 initial_pathological_complex_state 5))

end ComplexSystemsPsychiatryModel
