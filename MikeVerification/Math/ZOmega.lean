import MikeVerification.Math.Params
open QuadraticAlgebra

/-!
# The rings `R = ℤ[ω]` and `S = ℤ[j]`

From the *Notations* paragraph (p. 8): `j² = -p`, `ω = (1 + j)/2`, `R = ℤ[ω]` is the maximal
order of `K = ℚ(√-p)`, and `S = ℤ[j]`.

Both are instances of Mathlib's `QuadraticAlgebra ℤ a b`, the ring `ℤ[X]/(X² - bX - a)` with
generator `ω` satisfying `ω² = a + b ω`:
* `R = QuadraticAlgebra ℤ (-n) 1`, so `ω² = ω - n` where `n = (p+1)/4`;
* `S = QuadraticAlgebra ℤ (-p) 0`, so its generator (also written `ω` by Mathlib) squares to `-p`.

Inside `R` we define `j := 2ω - 1` and check `j² = -p`. The conjugation `star` on `R` is the
nontrivial automorphism `ω ↦ 1 - ω`, `j ↦ -j`.
-/

namespace Params
variable (P : Params)

/-- `R = ℤ[ω]` with `ω = (1 + j)/2`, `j² = -p`, so `ω² = ω - (p+1)/4`. -/
abbrev R := QuadraticAlgebra ℤ (-(P.n : ℤ)) 1

/-- `S = ℤ[j]` with `j² = -p`. Mathlib calls the generator `ω`; it plays the role of `j`. -/
abbrev S := QuadraticAlgebra ℤ (-(P.p : ℤ)) 0

/-! ### Discriminants -/

/-- `disc R = 1 - 4n = -p`, the fundamental discriminant of `ℚ(√-p)` for `p ≡ 3 mod 4`. -/
theorem discr_R : discr (-(P.n : ℤ)) 1 = -(P.p : ℤ) := by
  rw [p_eq, discr_def]; ring

/-- `disc S = -4p`, so `S` has index 2 in `R`. -/
theorem discr_S : discr (-(P.p : ℤ)) 0 = -4 * (P.p : ℤ) := by
  rw [discr_def]; ring

theorem not_isSquare_discr_R : ¬ IsSquare (discr (-(P.n : ℤ)) 1) := by
  rw [discr_R]
  rintro ⟨r, hr⟩
  have hp : (0 : ℤ) < P.p := by exact_mod_cast P.hp.pos
  nlinarith [mul_self_nonneg r]

theorem not_isSquare_discr_S : ¬ IsSquare (discr (-(P.p : ℤ)) 0) := by
  rw [discr_S]
  rintro ⟨r, hr⟩
  have hp : (0 : ℤ) < P.p := by exact_mod_cast P.hp.pos
  nlinarith [mul_self_nonneg r]

instance : Fact (¬ IsSquare (discr (-(P.n : ℤ)) 1)) := ⟨P.not_isSquare_discr_R⟩
instance : Fact (¬ IsSquare (discr (-(P.p : ℤ)) 0)) := ⟨P.not_isSquare_discr_S⟩

example : IsDomain P.R := inferInstance
example : IsDomain P.S := inferInstance

/-! ### The element `j` and conjugation in `R` -/

/-- `j = 2ω - 1 ∈ R`, the square root of `-p` (the Frobenius `σ` under `[·]`). -/
def j : P.R := 2 * ω - 1

theorem two_omega : (2 : P.R) * ω = 1 + P.j := by
  simp [j]

/-- `j² = -p`. -/
theorem j_sq : P.j ^ 2 = -((P.p : ℤ) : P.R) := by
  rw [p_eq]; ext <;> simp [j, sq]; ring

theorem j_mul_j : P.j * P.j = -((P.p : ℤ) : P.R) := by
  rw [← sq, j_sq]

/-- The conjugate of `ω` is `ω' = 1 - ω`. -/
theorem star_omega : star (ω : P.R) = 1 - ω := by
  ext <;> simp

/-- `j` is purely imaginary: `star j = -j`. -/
theorem star_j : star P.j = -P.j := by
  ext <;> simp [j]

/-- `N(j) = j · j̄ = p`. -/
theorem norm_j : norm P.j = (P.p : ℤ) := by
  rw [p_eq, norm_def]; simp [j]; ring

/-- `N(ω) = ω · ω̄ = n = (p+1)/4`. -/
theorem norm_omega : norm (ω : P.R) = (P.n : ℤ) := by
  rw [norm_def]; simp

/-! ### The inclusion `S ⊆ R` -/

/-- The inclusion `S = ℤ[j] → R = ℤ[ω]`, sending the generator of `S` to `j = 2ω - 1`. -/
def SToR : P.S →ₐ[ℤ] P.R :=
  lift ⟨P.j, by
    rw [zero_smul, add_zero, j_mul_j, Int.smul_one_eq_cast]; push_cast; ring⟩

@[simp] theorem SToR_omega : P.SToR ω = P.j := by
  simp [SToR]

theorem SToR_injective : Function.Injective P.SToR := by
  intro x y h
  have h' := QuadraticAlgebra.ext_iff.mp h
  simp [SToR, j] at h'
  ext <;> omega

end Params
