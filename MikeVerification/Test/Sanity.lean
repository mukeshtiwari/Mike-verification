import MikeVerification.Math.Quaternion
import MikeVerification.Impl.Fp2
open QuadraticAlgebra Params

/-!
# Executability sanity checks for the `Math` layer

Every definition in `MikeVerification.Math` that the protocol touches must be computable.
This file `#eval`s them at toy parameters so that an accidental `noncomputable` dependency
(or a sign/convention error) fails the build immediately.
-/

namespace MikeVerification.Test

/-- Toy parameters: `p = 1 · 2^3 − 1 = 7`, `e = 1`. -/
def toy : Params := ⟨7, 1, 3, 1, by norm_num, by norm_num, by decide, by norm_num, by norm_num⟩

-- `j² = -p` in `R`, `N(j) = p`
#eval (toy.j * toy.j).re        -- -7
#eval (toy.j * toy.j).im        -- 0
#eval norm toy.j                -- 7
-- the inclusion `S → R` sends the generator of `S` to `j = -1 + 2ω`
#eval (toy.SToR ω).re           -- -1
#eval (toy.SToR ω).im           -- 2
-- `i² = -1` and `(ωi)² = -N(ω) = -n` in `O₀`
#eval ((O₀.i : O₀ toy) * O₀.i).α.re             -- -1
#eval ((O₀.omegaI : O₀ toy) * O₀.omegaI).α.re   -- -2
-- `ρ₀(2^e · i) = (0, 2^e)`
#eval (O₀.ρ₀ ((2 : O₀ toy) ^ toy.e * O₀.i)).2.re   -- 2
-- the embedding into `ℍ[ℚ, -1, -p]`
#eval (O₀.toQuat (O₀.omegaI : O₀ toy)).imK         -- -1/2

-- The same facts as decidable propositions, so the build fails if a value changes.
example : (toy.j * toy.j).re = -7 := by decide
example : norm toy.j = 7 := by decide
example : ((O₀.i : O₀ toy) * O₀.i) = -1 := by decide
example : (O₀.ρ₀ ((2 : O₀ toy) ^ toy.e * O₀.i)) = (0, 2) := by decide

end MikeVerification.Test

namespace MikeVerification.Test

-- Executable `𝔽_{p²}` at `p = 7`: `i² = -1`, and `(2 + 3i)⁻¹ (2 + 3i) = 1`.
#eval ((⟨2, 3⟩ : Impl.Fp2 toy)⁻¹)                    -- { re := 2 * 13⁻¹ = 2 * 6⁻¹ = 5, im := ... }
#eval ((⟨2, 3⟩ : Impl.Fp2 toy)⁻¹ * ⟨2, 3⟩)           -- { re := 1, im := 0 }
example : (Impl.Fp2.i : Impl.Fp2 toy) * Impl.Fp2.i = -1 := by decide
-- `ZMod` inversion (extended gcd, well-founded recursion) does not kernel-reduce, so these two
-- use `native_decide`; this is acceptable in `Test/` only.
example : ((⟨2, 3⟩ : Impl.Fp2 toy)⁻¹ * ⟨2, 3⟩) = 1 := by native_decide
example : ((⟨0, 0⟩ : Impl.Fp2 toy)⁻¹) = 0 := by native_decide
-- The Math type runs as well: `ω⁻¹ = -ω` in `𝔽_49`.
#eval ((ω : toy.Fp2)⁻¹).im                                 -- -1 (i.e. 6)
example : ((ω : toy.Fp2)⁻¹) = -ω := by native_decide

end MikeVerification.Test
