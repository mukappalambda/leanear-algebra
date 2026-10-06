import Mathlib.Data.Fin.VecNotation
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

set_option linter.style.header false
set_option linter.style.whitespace false

#check funext

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
