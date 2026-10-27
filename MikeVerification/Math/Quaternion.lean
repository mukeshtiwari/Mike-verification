import MikeVerification.Math.ZOmega
open QuadraticAlgebra Quaternion

/-!
# The quaternion order `O₀ = R ⊕ R·i`

From the *Notations* paragraph (p. 8): `End(E₀') ≅ O₀ := ⟨1, i, (1+j)/2, (i-k)/2⟩`, a maximal
order in the quaternion algebra `B = (-1, -p)_ℚ` with `i² = -1`, `j² = -p`, `k = ij = -ji`.
With `ω = (1+j)/2` and `R = ℤ[ω]` one has `O₀ = R ⊕ R·i`, and
`ρ₀ : O₀ → R²`, `α + βi ↦ (α, β)` is an isomorphism (of left `R`-modules).

## Design

We *define* `O₀` as pairs `(α, β) ∈ R × R` standing for `α + β i`. Since `i` anticommutes
with `j` it conjugates `R`: `i α = ᾱ i`. Hence the product is
```
(α + β i)(γ + δ i) = (α γ - β δ̄) + (α δ + β γ̄) i .
```
With this definition `ρ₀` is the identity on the underlying pairs, which is what the module
action in §2 and the Impl layer actually use. To tie this back to the paper's definition we
give an injective ring hom `toQuat : O₀ → ℍ[ℚ, -1, -p]` sending `1, i, ω, ωi` to
`1, i, (1+j)/2, (i-k)/2`.
-/

namespace Params

/-- The order `O₀ = R ⊕ R i`; `⟨α, β⟩` stands for `α + β i`. -/
@[ext]
structure O₀ (P : Params) where
  α : P.R
  β : P.R
deriving DecidableEq

namespace O₀
variable {P : Params}

instance : Zero (O₀ P) := ⟨⟨0, 0⟩⟩
instance : One (O₀ P) := ⟨⟨1, 0⟩⟩
instance : Add (O₀ P) := ⟨fun x y => ⟨x.α + y.α, x.β + y.β⟩⟩
instance : Neg (O₀ P) := ⟨fun x => ⟨-x.α, -x.β⟩⟩
instance : Sub (O₀ P) := ⟨fun x y => ⟨x.α - y.α, x.β - y.β⟩⟩
/-- `(α + β i)(γ + δ i) = (α γ - β δ̄) + (α δ + β γ̄) i`, using `i r = r̄ i`. -/
instance : Mul (O₀ P) :=
  ⟨fun x y => ⟨x.α * y.α - x.β * star y.β, x.α * y.β + x.β * star y.α⟩⟩
/-- Left multiplication by `R`. -/
instance : SMul P.R (O₀ P) := ⟨fun r x => ⟨r * x.α, r * x.β⟩⟩
instance : NatCast (O₀ P) := ⟨fun n => ⟨n, 0⟩⟩
instance : IntCast (O₀ P) := ⟨fun n => ⟨n, 0⟩⟩

@[simp] theorem α_zero : (0 : O₀ P).α = 0 := rfl
@[simp] theorem β_zero : (0 : O₀ P).β = 0 := rfl
@[simp] theorem α_one : (1 : O₀ P).α = 1 := rfl
@[simp] theorem β_one : (1 : O₀ P).β = 0 := rfl
@[simp] theorem α_add (x y : O₀ P) : (x + y).α = x.α + y.α := rfl
@[simp] theorem β_add (x y : O₀ P) : (x + y).β = x.β + y.β := rfl
@[simp] theorem α_neg (x : O₀ P) : (-x).α = -x.α := rfl
@[simp] theorem β_neg (x : O₀ P) : (-x).β = -x.β := rfl
@[simp] theorem α_sub (x y : O₀ P) : (x - y).α = x.α - y.α := rfl
@[simp] theorem β_sub (x y : O₀ P) : (x - y).β = x.β - y.β := rfl
@[simp] theorem α_mul (x y : O₀ P) : (x * y).α = x.α * y.α - x.β * star y.β := rfl
@[simp] theorem β_mul (x y : O₀ P) : (x * y).β = x.α * y.β + x.β * star y.α := rfl
@[simp] theorem α_smul (r : P.R) (x : O₀ P) : (r • x).α = r * x.α := rfl
@[simp] theorem β_smul (r : P.R) (x : O₀ P) : (r • x).β = r * x.β := rfl
@[simp] theorem α_natCast (n : ℕ) : (n : O₀ P).α = n := rfl
@[simp] theorem β_natCast (n : ℕ) : (n : O₀ P).β = 0 := rfl
@[simp] theorem α_intCast (n : ℤ) : (n : O₀ P).α = n := rfl
@[simp] theorem β_intCast (n : ℤ) : (n : O₀ P).β = 0 := rfl

instance : Ring (O₀ P) where
  add_assoc _ _ _ := by ext <;> simp [add_assoc]
  zero_add _ := by ext <;> simp
  add_zero _ := by ext <;> simp
  add_comm _ _ := by ext <;> simp [add_comm]
  neg_add_cancel _ := by ext <;> simp
  left_distrib _ _ _ := by ext <;> simp <;> ring
  right_distrib _ _ _ := by ext <;> simp <;> ring
  zero_mul _ := by ext <;> simp
  mul_zero _ := by ext <;> simp
  mul_assoc _ _ _ := by ext <;> simp [star_mul', star_add, star_sub, mul_sub, sub_mul] <;> ring
  one_mul _ := by ext <;> simp
  mul_one _ := by ext <;> simp
  natCast_zero := by ext <;> simp
  natCast_succ _ := by ext <;> simp
  intCast_ofNat _ := by ext <;> simp
  intCast_negSucc _ := by ext <;> simp [Int.cast_negSucc]
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- `O₀` is a left `R`-module (in fact free of rank 2 with basis `1, i`). -/
instance : Module P.R (O₀ P) where
  one_smul _ := by ext <;> simp
  mul_smul _ _ _ := by ext <;> simp [mul_assoc]
  smul_zero _ := by ext <;> simp
  smul_add _ _ _ := by ext <;> simp [mul_add]
  add_smul _ _ _ := by ext <;> simp [add_mul]
  zero_smul _ := by ext <;> simp

/-! ### Distinguished elements -/

/-- `i ∈ O₀`, with `i² = -1`. -/
def i : O₀ P := ⟨0, 1⟩

/-- The image of `α ∈ R` in `O₀`. -/
def ofR (α : P.R) : O₀ P := ⟨α, 0⟩

@[simp] theorem α_i : (i : O₀ P).α = 0 := rfl
@[simp] theorem β_i : (i : O₀ P).β = 1 := rfl
@[simp] theorem α_ofR (α : P.R) : (ofR α).α = α := rfl
@[simp] theorem β_ofR (α : P.R) : (ofR α).β = 0 := rfl

theorem i_mul_i : (i : O₀ P) * i = -1 := by
  ext <;> simp

theorem i_sq : (i : O₀ P) ^ 2 = -1 := by
  rw [sq, i_mul_i]

/-- Every element is `α + β i`. -/
theorem eq_ofR_add_ofR_mul_i (x : O₀ P) : x = ofR x.α + ofR x.β * i := by
  ext <;> simp

/-- `i` conjugates `R`: `i α = ᾱ i`. -/
theorem i_mul_ofR (α : P.R) : (i : O₀ P) * ofR α = ofR (star α) * i := by
  ext <;> simp

/-- `ω ∈ O₀`, i.e. `(1 + j)/2`. -/
theorem omega_def : (ofR ω : O₀ P) = ⟨ω, 0⟩ := rfl

/-- The fourth generator `(i - k)/2 = ω i`. -/
def omegaI : O₀ P := ⟨0, ω⟩

theorem ofR_omega_mul_i : (ofR ω : O₀ P) * i = omegaI := by
  ext <;> simp [omegaI]

theorem ofR_mul_i (α : P.R) : (ofR α : O₀ P) * i = ⟨0, α⟩ := by
  ext <;> simp

/-- `ofR` is a ring hom `R → O₀`. -/
def ofRHom : P.R →+* O₀ P where
  toFun := ofR
  map_one' := rfl
  map_mul' _ _ := by ext <;> simp
  map_zero' := rfl
  map_add' _ _ := by ext <;> simp

/-! ### `ρ₀ : O₀ ≃ R²` -/

/-- `ρ₀ : O₀ → R²`, `α + β i ↦ (α, β)`, an isomorphism of left `R`-modules. -/
def ρ₀ : O₀ P ≃ₗ[P.R] P.R × P.R where
  toFun x := (x.α, x.β)
  invFun v := ⟨v.1, v.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem ρ₀_apply (x : O₀ P) : ρ₀ x = (x.α, x.β) := rfl
@[simp] theorem ρ₀_symm_apply (v : P.R × P.R) : ρ₀.symm v = (⟨v.1, v.2⟩ : O₀ P) := rfl
@[simp] theorem ρ₀_one : ρ₀ (1 : O₀ P) = (1, 0) := rfl
@[simp] theorem ρ₀_i : ρ₀ (i : O₀ P) = (0, 1) := rfl
@[simp] theorem ρ₀_ofR (α : P.R) : ρ₀ (ofR α : O₀ P) = (α, 0) := rfl

/-! ### Embedding into the quaternion algebra `(-1, -p)_ℚ`

Mathlib's `ℍ[ℚ, -1, -p]` has `i² = -1`, `j² = -p`, `ij = k = -ji`. Writing `α = a₀ + a₁ ω`,
`β = b₀ + b₁ ω` with `ω = (1+j)/2` and `ω i = (i - k)/2`:
```
α + β i = (a₀ + a₁/2) + (b₀ + b₁/2) i + (a₁/2) j - (b₁/2) k .
```
-/

/-- The embedding `O₀ → ℍ[ℚ, -1, -p]`. -/
def toQuat : O₀ P →+* ℍ[ℚ, -1, -(P.p : ℚ)] where
  toFun x := ⟨x.α.re + x.α.im / 2, x.β.re + x.β.im / 2, x.α.im / 2, -(x.β.im / 2)⟩
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp <;> ring
  map_mul' x y := by
    have hn : (P.n : ℚ) = ((P.p : ℚ) + 1) / 4 := by
      have h := P.four_mul_n
      rw [eq_div_iff (by norm_num)]
      exact_mod_cast (by omega : P.n * 4 = P.p + 1)
    ext <;> simp [QuaternionAlgebra.mk_mul_mk] <;> (try rw [hn]) <;> ring

@[simp] theorem toQuat_apply (x : O₀ P) :
    toQuat x = ⟨x.α.re + x.α.im / 2, x.β.re + x.β.im / 2, x.α.im / 2, -(x.β.im / 2)⟩ := rfl

/-- `1 ↦ 1`. -/
theorem toQuat_one : toQuat (1 : O₀ P) = ⟨1, 0, 0, 0⟩ := by ext <;> simp
/-- `i ↦ i`. -/
theorem toQuat_i : toQuat (i : O₀ P) = ⟨0, 1, 0, 0⟩ := by ext <;> simp
/-- `ω ↦ (1 + j)/2`. -/
theorem toQuat_omega : toQuat (ofR ω : O₀ P) = ⟨1/2, 0, 1/2, 0⟩ := by ext <;> simp
/-- `ω i ↦ (i - k)/2`. -/
theorem toQuat_omegaI : toQuat (omegaI : O₀ P) = ⟨0, 1/2, 0, -(1/2)⟩ := by
  ext <;> simp [omegaI]

theorem toQuat_injective : Function.Injective (toQuat : O₀ P → ℍ[ℚ, -1, -(P.p : ℚ)]) := by
  intro x y h
  rw [toQuat_apply, toQuat_apply, QuaternionAlgebra.ext_iff] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have e1 : (x.α.im : ℚ) = y.α.im := by linarith
  have e2 : (x.α.re : ℚ) = y.α.re := by linarith
  have e3 : (x.β.im : ℚ) = y.β.im := by linarith
  have e4 : (x.β.re : ℚ) = y.β.re := by linarith
  ext
  · exact_mod_cast e2
  · exact_mod_cast e1
  · exact_mod_cast e4
  · exact_mod_cast e3

end O₀
end Params
