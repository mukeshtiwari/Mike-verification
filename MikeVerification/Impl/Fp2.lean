import MikeVerification.Math.Fp2

/-!
# Executable `𝔽_{p²}`

`𝔽_{p²} = 𝔽_p(i)`, `i² = -1`, as pairs `(re, im)` of `ZMod p` with explicit formulas,
including a computable inverse `(a + b i)⁻¹ = (a - b i) / (a² + b²)`.
This is the computable twin of `Params.Fp2`; see `MikeVerification.Refine.Fp2.toMath`.
-/

namespace MikeVerification.Impl

/-- `𝔽_{p²}` as pairs `⟨re, im⟩` standing for `re + im · i`, `i² = -1`. -/
@[ext]
structure Fp2 (P : Params) where
  re : ZMod P.p
  im : ZMod P.p
deriving DecidableEq, Repr

namespace Fp2
variable {P : Params}

instance : Zero (Fp2 P) := ⟨⟨0, 0⟩⟩
instance : One (Fp2 P) := ⟨⟨1, 0⟩⟩
instance : Add (Fp2 P) := ⟨fun x y => ⟨x.re + y.re, x.im + y.im⟩⟩
instance : Neg (Fp2 P) := ⟨fun x => ⟨-x.re, -x.im⟩⟩
instance : Sub (Fp2 P) := ⟨fun x y => ⟨x.re - y.re, x.im - y.im⟩⟩
instance : Mul (Fp2 P) :=
  ⟨fun x y => ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩⟩
instance : NatCast (Fp2 P) := ⟨fun n => ⟨n, 0⟩⟩
instance : IntCast (Fp2 P) := ⟨fun n => ⟨n, 0⟩⟩

/-- The norm `𝔽_{p²} → 𝔽_p`, `a + b i ↦ a² + b²`. -/
def nrm (x : Fp2 P) : ZMod P.p := x.re * x.re + x.im * x.im

/-- `(a + b i)⁻¹ = (a - b i) / (a² + b²)`, using the computable inverse of `ZMod p`. -/
instance : Inv (Fp2 P) := ⟨fun x => ⟨x.re * (nrm x)⁻¹, -(x.im * (nrm x)⁻¹)⟩⟩

/-- Conjugation `a + b i ↦ a - b i`, i.e. the Frobenius `x ↦ x^p`. -/
def conj (x : Fp2 P) : Fp2 P := ⟨x.re, -x.im⟩

/-- `i`. -/
def i : Fp2 P := ⟨0, 1⟩

@[simp] theorem re_zero : (0 : Fp2 P).re = 0 := rfl
@[simp] theorem im_zero : (0 : Fp2 P).im = 0 := rfl
@[simp] theorem re_one : (1 : Fp2 P).re = 1 := rfl
@[simp] theorem im_one : (1 : Fp2 P).im = 0 := rfl
@[simp] theorem re_add (x y : Fp2 P) : (x + y).re = x.re + y.re := rfl
@[simp] theorem im_add (x y : Fp2 P) : (x + y).im = x.im + y.im := rfl
@[simp] theorem re_neg (x : Fp2 P) : (-x).re = -x.re := rfl
@[simp] theorem im_neg (x : Fp2 P) : (-x).im = -x.im := rfl
@[simp] theorem re_sub (x y : Fp2 P) : (x - y).re = x.re - y.re := rfl
@[simp] theorem im_sub (x y : Fp2 P) : (x - y).im = x.im - y.im := rfl
@[simp] theorem re_mul (x y : Fp2 P) : (x * y).re = x.re * y.re - x.im * y.im := rfl
@[simp] theorem im_mul (x y : Fp2 P) : (x * y).im = x.re * y.im + x.im * y.re := rfl
@[simp] theorem re_natCast (n : ℕ) : (n : Fp2 P).re = n := rfl
@[simp] theorem im_natCast (n : ℕ) : (n : Fp2 P).im = 0 := rfl
@[simp] theorem re_intCast (n : ℤ) : (n : Fp2 P).re = n := rfl
@[simp] theorem im_intCast (n : ℤ) : (n : Fp2 P).im = 0 := rfl
@[simp] theorem re_inv (x : Fp2 P) : (x⁻¹).re = x.re * (nrm x)⁻¹ := rfl
@[simp] theorem im_inv (x : Fp2 P) : (x⁻¹).im = -(x.im * (nrm x)⁻¹) := rfl
@[simp] theorem re_conj (x : Fp2 P) : (conj x).re = x.re := rfl
@[simp] theorem im_conj (x : Fp2 P) : (conj x).im = -x.im := rfl
@[simp] theorem re_i : (i : Fp2 P).re = 0 := rfl
@[simp] theorem im_i : (i : Fp2 P).im = 1 := rfl

instance : CommRing (Fp2 P) where
  add_assoc _ _ _ := by ext <;> simp [add_assoc]
  zero_add _ := by ext <;> simp
  add_zero _ := by ext <;> simp
  add_comm _ _ := by ext <;> simp [add_comm]
  neg_add_cancel _ := by ext <;> simp
  sub_eq_add_neg _ _ := by ext <;> simp [sub_eq_add_neg]
  left_distrib _ _ _ := by ext <;> simp <;> ring
  right_distrib _ _ _ := by ext <;> simp <;> ring
  zero_mul _ := by ext <;> simp
  mul_zero _ := by ext <;> simp
  mul_assoc _ _ _ := by ext <;> simp <;> ring
  one_mul _ := by ext <;> simp
  mul_one _ := by ext <;> simp
  mul_comm _ _ := by ext <;> simp <;> ring
  natCast_zero := by ext <;> simp
  natCast_succ _ := by ext <;> simp
  intCast_ofNat _ := by ext <;> simp
  intCast_negSucc _ := by ext <;> simp [Int.cast_negSucc]
  nsmul := nsmulRec
  zsmul := zsmulRec

theorem i_mul_i : (i : Fp2 P) * i = -1 := by
  ext <;> simp

theorem conj_mul_self (x : Fp2 P) : x * conj x = ⟨nrm x, 0⟩ := by
  ext <;> simp only [re_mul, im_mul, re_conj, im_conj, nrm] <;> ring

/-- The norm vanishes only at `0`, because `-1` is not a square in `𝔽_p`. -/
theorem nrm_eq_zero_iff (x : Fp2 P) : nrm x = 0 ↔ x = 0 := by
  constructor
  · intro h
    by_contra hx
    rcases eq_or_ne x.im 0 with him | him
    · have hre : x.re = 0 := by simpa [nrm, him] using h
      exact hx (Fp2.ext hre him)
    · apply P.not_isSquare_neg_one
      refine ⟨x.re / x.im, ?_⟩
      rw [div_mul_div_comm, eq_comm, div_eq_iff (mul_ne_zero him him)]
      unfold nrm at h
      linear_combination h
  · rintro rfl; simp [nrm]

theorem nrm_ne_zero {x : Fp2 P} (hx : x ≠ 0) : nrm x ≠ 0 :=
  mt (nrm_eq_zero_iff x).mp hx

/-- `𝔽_{p²}` is a field, with the *computable* inverse above. -/
instance : Field (Fp2 P) :=
  { (inferInstance : CommRing (Fp2 P)) with
    inv := Inv.inv
    exists_pair_ne := ⟨0, 1, fun h => by simpa using congrArg Fp2.re h⟩
    mul_inv_cancel := fun x hx => by
      have hd := nrm_ne_zero hx
      ext
      · show x.re * (x.re * (nrm x)⁻¹) - x.im * (-(x.im * (nrm x)⁻¹)) = 1
        rw [show x.re * (x.re * (nrm x)⁻¹) - x.im * (-(x.im * (nrm x)⁻¹))
              = nrm x * (nrm x)⁻¹ by unfold nrm; ring, mul_inv_cancel₀ hd]
      · show x.re * (-(x.im * (nrm x)⁻¹)) + x.im * (x.re * (nrm x)⁻¹) = 0
        ring
    inv_zero := by ext <;> simp
    nnqsmul := _
    nnqsmul_def := fun _ _ => rfl
    qsmul := _
    qsmul_def := fun _ _ => rfl }

end Fp2
end MikeVerification.Impl
