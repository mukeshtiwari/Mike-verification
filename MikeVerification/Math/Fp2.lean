import MikeVerification.Math.Params
open QuadraticAlgebra

/-!
# The field `𝔽_{p²} = 𝔽_p(i)`, `i² = -1`

Since `p ≡ 3 mod 4`, `-1` is not a square in `𝔽_p`, so `𝔽_p[X]/(X² + 1)` is a field with `p²`
elements. This is the model of `𝔽_{p²}` used throughout the paper (and in `mike_rs`).

We realise it as `QuadraticAlgebra (ZMod p) (-1) 0`; Mathlib's generator `ω` is our `i`.
Mathlib's `Field` instance (inverse `N(z)⁻¹ • z̄`) is computable, so this type already runs.
The explicit-formula twin used by the implementation is `MikeVerification.Impl.Fp2`, related
by the ring isomorphism `MikeVerification.Refine.Fp2.toMath`.
-/

namespace Params
variable (P : Params)

instance : NeZero P.p := ⟨P.hp.ne_zero⟩

/-- `𝔽_{p²} = 𝔽_p(i)` with `i² = -1`. Mathlib writes the generator `ω`; it is `i`. -/
abbrev Fp2 := QuadraticAlgebra (ZMod P.p) (-1) 0

/-- `i² = -1`. -/
theorem Fp2.omega_mul_omega : (ω : P.Fp2) * ω = -1 := by
  ext <;> simp

/-- Conjugation (the Frobenius `x ↦ x^p` on `𝔽_{p²}`) is `a + b i ↦ a - b i`. -/
theorem Fp2.star_mk (a b : ZMod P.p) : star (⟨a, b⟩ : P.Fp2) = ⟨a, -b⟩ := by
  ext <;> simp

/-! ### `𝔽_{p²}` is a field -/

theorem two_ne_zero_zmod : (2 : ZMod P.p) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod P.p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  have := Nat.le_of_dvd (by norm_num) h'
  have := P.seven_le_p
  omega

instance : NeZero (2 : ZMod P.p) := ⟨P.two_ne_zero_zmod⟩

/-- `-1` is not a square mod `p`, because `p ≡ 3 mod 4`. -/
theorem not_isSquare_neg_one : ¬ IsSquare (-1 : ZMod P.p) := by
  rw [ZMod.exists_sq_eq_neg_one_iff]
  simp [P.p_mod_four]

theorem not_isSquare_discr_Fp2 : ¬ IsSquare (discr (-1 : ZMod P.p) 0) := by
  rw [discr_def]
  rintro ⟨r, hr⟩
  apply P.not_isSquare_neg_one
  refine ⟨r / 2, ?_⟩
  have h4 : (2 : ZMod P.p) * 2 ≠ 0 := mul_ne_zero P.two_ne_zero_zmod P.two_ne_zero_zmod
  rw [div_mul_div_comm, ← hr, eq_div_iff h4]
  ring

instance : Fact (¬ IsSquare (-1 : ZMod P.p)) := ⟨P.not_isSquare_neg_one⟩

/-- Mathlib's `Field` instance on `QuadraticAlgebra K a 0` fires from `Fact (¬ IsSquare a)`.
Its inverse `z⁻¹ = N(z)⁻¹ • z̄` is computable. -/
example : Field P.Fp2 := inferInstance

theorem Fp2.isField : IsField P.Fp2 := Field.toIsField _

/-! ### `𝔽_{p²}` has `p²` elements and is *the* field with `p²` elements -/

instance : Fintype P.Fp2 := Fintype.ofEquiv (ZMod P.p × ZMod P.p) (equivProd _ _).symm

theorem Fp2.card : Fintype.card P.Fp2 = P.p ^ 2 := by
  rw [Fintype.card_congr (equivProd _ _), Fintype.card_prod, ZMod.card]; ring

/-- `𝔽_p(i) ≅ GF(p²)`, Mathlib's abstract Galois field. -/
noncomputable def Fp2.algEquivGaloisField : P.Fp2 ≃ₐ[ZMod P.p] GaloisField P.p 2 :=
  GaloisField.algEquivGaloisFieldOfFintype P.p 2 (Fp2.card P)

end Params
