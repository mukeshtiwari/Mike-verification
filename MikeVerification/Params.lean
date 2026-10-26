import Mathlib
open QuadraticAlgebra

/-!
# MIKE parameters and the ring `R = ℤ[ω]`

Formalises the *Notations* paragraph of the MIKE paper (p. 8, before §2).
The condition `f ≥ 3` is taken from Corollary 3.1 (p. 13).
Not yet encoded: primality of `p`, maximality of `R` in `ℚ(√-p)`.
-/

/-- MIKE parameters: p = c * 2^f - 1 with f ≥ 3. --/

structure Params where
  c : ℕ
  f : ℕ
  hf : 3 ≤ f

namespace Params
variable (P : Params)

def p : ℤ := P.c * 2 ^ P.f - 1

/-- `(p + 1) / 4`, an integer because `f ≥ 3`. -/
def n : ℤ := P.c * 2 ^ (P.f - 2)

theorem p_eq : P.p = 4 * P.n - 1 := by
  obtain ⟨c, f, hf⟩ := P
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 2 := ⟨f - 2, by omega⟩
  simp [p, n, pow_add]; ring

/-- `R = ℤ[ω]` with `ω = (1 + j)/2`, `j² = -p`, so `ω² = ω - (p+1)/4`. -/
abbrev R := QuadraticAlgebra ℤ (-P.n) 1

/-- `j = 2ω - 1` squares to `-p`. -/
theorem j_sq : ((2 : P.R) * ω - 1) ^ 2 = -(P.p : P.R) := by
  rw [p_eq]; ext <;> simp [sq]; ring

end Params
