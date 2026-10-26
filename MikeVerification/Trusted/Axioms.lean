import Mathlib

/-!
# Trusted base

Results from the literature that are *assumed*, not proved, in this development.
Everything here is stated as an `axiom` (or an opaque hypothesis bundled into a structure)
and nothing else in the repository may introduce axioms. Intended contents:

* existence of Vélu isogenies with prescribed finite kernel;
* the Hasse bound / point counts of supersingular curves over `𝔽_p`, `𝔽_{p²}`;
* Theorem 4.2 of the MIKE paper;
* commutativity of the module action (Theorem 2.3 / Appendix B).

Check with `#print axioms` on the final theorems that only these (and the standard
`propext`, `Classical.choice`, `Quot.sound`) appear.
-/

namespace MikeVerification.Trusted

end MikeVerification.Trusted
