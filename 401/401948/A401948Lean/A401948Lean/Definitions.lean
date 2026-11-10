import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Real.Basic

/-! Definitions for line-size profiles of finite planar configurations. -/

namespace Erdos607

open Finset
open scoped BigOperators

abbrev Point := ℝ × ℝ

inductive Line
  | vertical (x : ℝ)
  | graph (slope intercept : ℝ)

def On (line : Line) (p : Point) : Prop :=
  match line with
  | .vertical x => p.1 = x
  | .graph m b => p.2 = m * p.1 + b

noncomputable def linePoints (P : Finset Point) (l : Line) : Finset Point := by
  classical
  exact P.filter (On l)

@[simp] theorem mem_linePoints {P : Finset Point} {l : Line} {p : Point} :
    p ∈ linePoints P l ↔ p ∈ P ∧ On l p := by
  classical
  simp [linePoints]

def profile (P : Finset Point) : Set ℕ :=
  {s | 2 ≤ s ∧ ∃ l : Line, (linePoints P l).card = s}

def required {r : ℕ} (sizes : Fin r → ℕ) : ℕ :=
  ∑ i : Fin r, (sizes i + (i.val + 1) - r)

end Erdos607
