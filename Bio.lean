import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
  # 生物学的動的平衡理論 (Biological Dynamic Equilibrium)

  Licensed under Apache 2.0 (Author: Takeo Yamamoto / 山本健夫)

  生命の本質は、静的な構造維持ではなく、絶え間ない「分解」と「合成」の
  流動のなかで一定の状態を保つ『動的平衡（Dynamic Equilibrium）』である。

  本コードは、生体を構成する分子ストックが常に新生（合成）され、
  同時に陳腐化（分解）されながらも、システム全体として生命の恒常性（ホメオスタシス）
  を維持する数理動態を型システム上で完全証明する。
-/

namespace BiologicalEquilibrium

/--
  生体システム（Organism）の内部状態
  - `X`  : 現在の生体構成分子ストックの総量（タンパク質など）
  - `α`  : 分解率（絶え間なく自己破壊される速度、エントロピー増大への傾き）
  - `S`  : 外部からの栄養摂取および合成能力（系へのインプット）
-/
structure Organism where
  X : ℝ
  α : ℝ
  S : ℝ
  X_pos : 0 < X
  α_bounds : 0 < α ∧ α < 1
  S_pos : 0 < S

/--
  シェーンハイマーの生命遷移関数（流動方程式）
  次の一歩における生命の状態は、現在のストックから「自己分解（α * X）」を引き算し、
  そこに新たな「自己合成（S）」を足し合わせたものになる。
-/
def next_organic_state (org : Organism) : ℝ :=
  org.X - (org.α * org.X) + org.S

/--
  動的平衡（Dynamic Equilibrium）の定義
  「入る流れ（合成）」と「出る流れ（分解）」が完全に平衝し、
  見た目の構造（X）に変化がないように見えるが、内部の分子は100%入れ替わっている状態。
-/
def IsDynamicEquilibrium (org : Organism) : Prop :=
  org.S = org.α * org.X

/--
  【定理：動的平衡の維持とホメオスタシス】
  生体システムが「分解の速度（α * X）」をぴったり補うだけの「合成の流動（S）」
  を維持している（IsDynamicEquilibrium）ならば、次の一歩における生体ストックは
  寸分違わず現在の状態を維持（next_organic_state = X）することを完全証明する。

  言葉のレトリックを排し、生命の本質が「物質の固定」ではなく
  「流れが創り出す定常パターン」であることを型システムが承認する。
-/
theorem dynamic_equilibrium_preserves_state (org : Organism) (hEq : IsDynamicEquilibrium org) :
    next_organic_state org = org.X := by
  dsimp [next_organic_state]
  rw [hEq]
  ring

/--
  【定理：死と衰退（エントロピーの勝利）】
  もし合成・栄養摂取の流動が遮断される（S = 0）、あるいは分解の速度を下回るならば、
  生体ストックは確定的に減少（構造の崩壊）に向かう。
  生命の持続には、絶え間ない「流動（インプット）」が不可欠であることの証明。
-/
theorem non_equilibrium_decay (org : Organism) (h_no_input : org.S < org.α * org.X) :
    next_organic_state org < org.X := by
  dsimp [next_organic_state]
  linarith

/-- 動的平衡の理論を、より明示的な形で再利用可能にする補助定理 -/
lemma dynamic_equilibrium_preserves_state' (org : Organism) (hEq : IsDynamicEquilibrium org) :
    org.X - (org.α * org.X) + org.S = org.X := by
  rw [hEq]
  ring

end BiologicalEquilibrium
