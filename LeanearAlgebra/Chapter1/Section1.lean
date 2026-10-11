import Mathlib.Data.Fin.VecNotation
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option linter.style.header false
set_option linter.style.whitespace false

#check funext

-- 1.1
-- The trick is to frame each problem as a statement
-- - points are parallel: statement is true
-- - points are not parallel: false
-- Providing a proof of the statement verifies the statement

-- (3,1,2) and (6,4,2)
example (v w : Fin 3 → ℝ) (h₀ : v = ![3, 1, 2]) (h₁ : w = ![6, 4, 2]) :
  ¬ ∃ x, ![x, x, x] = v / w := by
  rintro ⟨ x, hx ⟩
  have h0 : (![x, x, x] : Fin 3 → ℝ) 0 = (v / w) 0 := by rw[hx]
  have h1 : (![x, x, x] : Fin 3 → ℝ) 1 = (v / w) 1 := by rw[hx]
  norm_num [h₀, h₁] at h0 h1
  linarith

-- (-3,1,7) and (9,-3,-21)
namespace Ex2
def v : Fin 3 → ℝ := ![-3, 1, 7]
def w : Fin 3 → ℝ := ![9, -3, -21]

example : ∃ x, ![x, x, x] = (v / w) := by
  use -1/3
  rw [v, w]
  apply funext
  intro i
  match i with
  | 0
  | 1
  | 2 => norm_num

  --- equivalent to
  -- | 0 => norm_num
  -- | 1 => norm_num
  -- | 2 => norm_num
  ---

end Ex2

-- 1.4
example (e : Fin 2 → ℝ) (h : ∀ v, v + e = v) : e 0 = 0 ∧ e 1 = 0 := by
  have h0 := h ![0, 0]
  have hx := congrFun h0 0
  simp at hx
  have hy := congrFun h0 1
  simp at hy
  exact ⟨hx, hy⟩

-- 1.7
namespace P17

#check sub_div
#check funext

variable {n : ℕ} (a b : Fin n → ℝ)
example : (a + b) / 2 = a + (b - a) / 2 := by
  let m1 := (a + b) / 2
  let m2 := a + (b - a) / 2
  -- have : ∀ i < n, m1 i = m2 i := by sorry
  have : ∀ i : Fin n, m1 i = m2 i := by
    intro i
    calc
      m1 i = ((a + b) / 2) i := by rfl
      _ = (a/2 + b/2) i := by apply add_div
      _ = (a/2) i + (b/2) i := by simp
      _ = (a i) / 2 + (b i) / 2 := by simp
      _ = (a i) / 2 + (b i) / 2 + (a i) / 2  - (a i) / 2 := by simp
      _ = (a i) / 2 + (a i) / 2 + (b i) / 2  - (a i) / 2 := by rw [add_right_comm]
      _ = (a i) + (b i) / 2 - (a i) / 2 := by simp
      _ = (a i) + (b i - a i) / 2 := by rw [add_sub_assoc, ← sub_div]
      _ = (a + (b - a) / 2) i := by simp
      _ = m2 i := rfl
  exact funext this

-- using ring
example : (a + b) / 2 = a + (b - a) / 2 := by
  funext i
  change (a i + b i) / 2 = a i + (b i - a i) / 2
  ring

end P17
