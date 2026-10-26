import Mathlib
open QuadraticAlgebra

/-!
# MIKE parameters and the rings `R = ℤ[ω]`, `S = ℤ[j]`

Formalises the *Notations* paragraph of the MIKE paper (p. 8, before §2).
* `f ≥ 3` is taken from Corollary 3.1 (p. 13).
* `c` odd is taken from the parameter selection (§5 / p. 17).
* The Notations paragraph writes `e < f - 2`, but Corollary 3.1 and the parameter
  selection use `e ≤ f - 2` (with `e = f - 2` the recommended choice); we follow the latter.

`p` is stored as a field together with the relation `p + 1 = c * 2^f` (rather than defined
by natural-number subtraction), so that `ZMod p`, `GaloisField p 2`, `CharP _ p` etc. apply
directly and no truncation lemmas are needed.

Not yet encoded: maximality of `R` in `ℚ(√-p)` (but see `discr_R`), the quaternion order `O₀`
and the curve `E₀'`.
-/

/-- MIKE parameters: a prime `p = c * 2^f - 1` with `c` odd, `f ≥ 3`,
and isogeny length `e ≤ f - 2`. -/
structure Params where
  p : ℕ
  c : ℕ
  f : ℕ
  e : ℕ
  hp : p.Prime
  hpc : p + 1 = c * 2 ^ f
  hc : Odd c
  hf : 3 ≤ f
  he : e + 2 ≤ f

namespace Params
variable (P : Params)

instance : Fact P.p.Prime := ⟨P.hp⟩

/-- `(p + 1) / 4`, a natural number since `f ≥ 2`; see `four_mul_n`. -/
def n : ℕ := P.c * 2 ^ (P.f - 2)

theorem four_mul_n : 4 * P.n = P.p + 1 := by
  obtain ⟨p, c, f, e, hp, hpc, hc, hf, he⟩ := P
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 2 := ⟨f - 2, by omega⟩
  simp only [n, hpc, pow_add, Nat.add_sub_cancel]; ring

theorem p_eq : (P.p : ℤ) = 4 * P.n - 1 := by
  have := P.four_mul_n
  omega

theorem p_mod_four : P.p % 4 = 3 := by
  have := P.four_mul_n
  omega

theorem n_pos : 0 < P.n := by
  have hc : 0 < P.c := P.hc.pos
  unfold n; positivity

theorem seven_le_p : 7 ≤ P.p := by
  have h1 := P.four_mul_n
  have h2 := P.n_pos
  have hf := P.hf
  have hc : 1 ≤ P.c := P.hc.pos
  have : 2 ≤ 2 ^ (P.f - 2) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (P.f - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : 2 ≤ P.n := by unfold n; nlinarith
  omega

/-- `R = ℤ[ω]` with `ω = (1 + j)/2`, `j² = -p`, so `ω² = ω - (p+1)/4`. -/
abbrev R := QuadraticAlgebra ℤ (-(P.n : ℤ)) 1

/-- `S = ℤ[j]` with `j² = -p`. Here `ω` plays the role of `j`. -/
abbrev S := QuadraticAlgebra ℤ (-(P.p : ℤ)) 0

/-- `j = 2ω - 1` squares to `-p`. -/
theorem j_sq : ((2 : P.R) * ω - 1) ^ 2 = -((P.p : ℤ) : P.R) := by
  rw [p_eq]; ext <;> simp [sq]; ring

/-- `disc R = 1 - 4n = -p`, the fundamental discriminant of `ℚ(√-p)` for `p ≡ 3 mod 4`. -/
theorem discr_R : discr (-(P.n : ℤ)) 1 = -(P.p : ℤ) := by
  rw [p_eq, discr_def]; ring

/-- `disc S = -4p`, so `S` has index 2 in `R`. -/
theorem discr_S : discr (-(P.p : ℤ)) 0 = -4 * (P.p : ℤ) := by
  rw [discr_def]; ring

end Params
