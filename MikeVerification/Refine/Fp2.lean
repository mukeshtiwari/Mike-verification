import MikeVerification.Impl.Fp2
open QuadraticAlgebra

/-!
# Refinement: `Impl.Fp2 = Math.Fp2`

The representation map `⟨re, im⟩ ↦ re + im·ω` is a ring isomorphism from the executable
`MikeVerification.Impl.Fp2 P` onto `Params.Fp2 P = QuadraticAlgebra (ZMod p) (-1) 0`.
Consequently the computable inverse and conjugation agree with the field inverse and `star`.
-/

namespace MikeVerification.Refine
namespace Fp2
variable {P : Params}

/-- The representation map, as a ring isomorphism. -/
def toMath : Impl.Fp2 P ≃+* P.Fp2 where
  toFun x := ⟨x.re, x.im⟩
  invFun z := ⟨z.re, z.im⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := by
    ext <;> simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
      Impl.Fp2.re_mul, Impl.Fp2.im_mul] <;> ring
  map_add' _ _ := by ext <;> simp

@[simp] theorem toMath_apply (x : Impl.Fp2 P) : toMath x = ⟨x.re, x.im⟩ := rfl
@[simp] theorem toMath_symm_apply (z : P.Fp2) : toMath.symm z = (⟨z.re, z.im⟩ : Impl.Fp2 P) := rfl

/-- The executable inverse is the field inverse. -/
theorem toMath_inv (x : Impl.Fp2 P) : toMath x⁻¹ = (toMath x)⁻¹ :=
  map_inv₀ toMath x

/-- The executable conjugation is `star`. -/
theorem toMath_conj (x : Impl.Fp2 P) : toMath (Impl.Fp2.conj x) = star (toMath x) := by
  ext <;> simp

/-- `i ↦ ω`. -/
theorem toMath_i : toMath (Impl.Fp2.i : Impl.Fp2 P) = ω := by
  ext <;> simp

/-- The executable norm is `N(x) = x · x̄`, read off in `𝔽_p`. -/
theorem toMath_nrm (x : Impl.Fp2 P) :
    toMath x * star (toMath x) = algebraMap _ _ (Impl.Fp2.nrm x) := by
  ext <;> simp only [toMath_apply, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, re_star,
    im_star, algebraMap_re, algebraMap_im, Impl.Fp2.nrm] <;> ring

end Fp2
end MikeVerification.Refine
