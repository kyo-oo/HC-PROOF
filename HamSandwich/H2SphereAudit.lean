import HamSandwich.SphereOddDegree.AlgebraicTopology.SphereOrientationPosFromMV

/-
Copyright (c) 2026. The HC-PROOF campaign. All rights reserved.

# THE WAVE-13 AXIOM AUDIT — the vendored sphere-homology machine

The audit target of the HamSandwich port: `sphereTopHomologyIso_unconditional`
(the unconditional isomorphism H_n(S^n;ℤ) ≅ ℤ on Mathlib's own
`singularChainComplexFunctor`, built by the vendored subdivision →
small-chains → Mayer-Vietoris → suspension-tower spine).

The expected axiom set is the standard three (`propext`,
`Classical.choice`, `Quot.sound`) — anything else, and in particular
`sorryAx`, red-flags the lane.
-/

#print axioms SphereOddDegree.sphereTopHomologyIso_unconditional
