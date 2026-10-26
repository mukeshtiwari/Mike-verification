# Mike-verification

Lean 4 / Mathlib formalisation of the MIKE post-quantum NIKE (`mike.pdf`).

## Layout

```
MikeVerification/
  Trusted/   -- axioms: Vélu existence, Hasse, Thm 4.2, module-action commutativity
  Math/      -- layer 2: Params, ZOmega, Quaternion O_0, Fp2, Montgomery, Isogeny, Theta
  Spec/      -- protocol as pure functions over Math types (Alg. 1, 2, 3 abstractly)
  Impl/      -- executable Lean: representations, ladders, chains, Hadamard, Algs 5–10
  Refine/    -- Impl f = Spec f, one theorem per algorithm
  Test/      -- #eval against mike_py / mike_rs KATs
```

Dependencies flow downward only: `Trusted → Math → Spec → Impl → Refine`, and `Test`
depends on `Impl`. Only `Trusted/` may declare axioms.

## Building

```
lake build
```
