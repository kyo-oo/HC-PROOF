import GSTImageThreeRealizedWordGeometry
import Mathlib

/-!
# GST IMAGE 1 + IMAGE 3 — AUTHOR'S ORIGINAL
# Z = Z0 + N(Z0), F Z = F Z0 + F^2 Z0

This is NOT another "old mathematics" detour. It formalizes the OWNER'S
actual handwritten Step-01 polynomial source hypothesis on the TRUE
original-X Chow cycles and canonical rational Betti cycle-class map.

We prove:
(1) The type-correct exact original-X native/Betti F + F^2 square.
(2) Across ANY rational GST module, orbit(T, z+Tz) lies INSIDE
    orbit(T,z), so applying I+T never spontaneously invents
    directions. This is the precise limitation of the handwritten
    "always increases" conjectural step.
(3) The Wolfram original-4x3-wave exact determinant classification
    is in the accompanying .wl and research derivation, not
    silently imported into Lean as an axiom.

The source transformation can retain cyclicity when I+T is
invertible, and can lose it when -1 is a T-eigenvalue.
-/

set_option maxHeartbeats 2500000
noncomputable section

namespace GSTImageThreeOwnerPolynomialFold

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeCycleOperatorNaturality

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- The ORIGINAL AUTHOR'S Part-I native seed: Z=Z0+N(Z0),
now defined on ACTUAL original-X rational cycles. -/
def ownerExpandedNativeSeed
    (F : CycleClassOperatorPair V H p)
    (z : codimensionCycles V.X p) :
    codimensionCycles V.X p :=
  z + F.cycleOperator z

/-- The ORIGINAL Part-I polynomial NZ0+N^2Z0, interpreted on the
true original-X Chow carrier. -/
def ownerOnePlusTwoFold
    (F : CycleClassOperatorPair V H p)
    (z : codimensionCycles V.X p) :
    codimensionCycles V.X p :=
  F.cycleOperator (ownerExpandedNativeSeed F z)

/-- The owner's actual proposed original-X formula, with EXACT
canonical Betti typing and NO arbitrary identification between
scalars, operator powers, and Chow cycles. -/
theorem originalX_owner_N_plus_N_squared
    (F : CycleClassOperatorPair V H p)
    (z : codimensionCycles V.X p) :
    H.cycleClass p (ownerOnePlusTwoFold F z) =
      F.cohomologyOperator (H.cycleClass p z) +
      F.cohomologyOperator
        (F.cohomologyOperator (H.cycleClass p z)) := by
  simp only [ownerOnePlusTwoFold, ownerExpandedNativeSeed,
    map_add, F.cycleClass_cycleOperator]

/-- The ORIGINAL author's full expanded seed also has a literal
native/Betti equation, in the SAME original X cohomology grade. -/
theorem originalX_owner_expanded_seed_class
    (F : CycleClassOperatorPair V H p)
    (z : codimensionCycles V.X p) :
    H.cycleClass p (ownerExpandedNativeSeed F z) =
      H.cycleClass p z +
        F.cohomologyOperator (H.cycleClass p z) := by
  simp [ownerExpandedNativeSeed, F.cycleClass_cycleOperator]

section RankConservation

variable {W : Type*} [AddCommGroup W] [Module ℚ W]

/-- Actual GST rational Krylov trajectory, without a fixed 12-state
ceiling or a transfinite power incorrectly substituted for Nat. -/
def nativeOrbit (T : Module.End ℚ W) (z : W) : ℕ → W
  | 0 => z
  | n+1 => T (nativeOrbit T z n)

/-- Exact owner's original handwritten Z0+N(Z0) transformation
AT EVERY ACTUAL NATURAL FOLD DEPTH. -/
theorem nativeOrbit_expandedSeed
    (T : Module.End ℚ W) (z : W) (n : Nat) :
    nativeOrbit T (z + T z) n =
      nativeOrbit T z n + nativeOrbit T z (n+1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change T (nativeOrbit T (z + T z) n) =
        T (nativeOrbit T z n) + T (nativeOrbit T z (n+1))
      rw [ih, map_add]

/-- GST cardinal/topological N-orbit: span of all ACTUALLY
generated finite natural-iterate signals. No infinite sum assumed. -/
def nativeOrbitSpan
    (T : Module.End ℚ W) (z : W) : Submodule ℚ W :=
  Submodule.span ℚ (Set.range (nativeOrbit T z))

/-- Essential exact SOURCE-BIRTH FIREWALL for the author's original
Part-I equation: a polynomial change Z0 -> Z0 + N Z0
CAN NEVER INCREASE the accessible native Krylov span.

The author's actual full-rank source results are preserved when
I+F is invertible and may fail otherwise. New directions MUST
come from actual geometric source birth, mixing or a different
operator, not from this polynomial rewriting alone. -/
theorem ownerExpandedSeed_orbitSpan_le
    (T : Module.End ℚ W) (z : W) :
    nativeOrbitSpan T (z + T z) ≤ nativeOrbitSpan T z := by
  apply Submodule.span_le.mpr
  rintro x ⟨n, rfl⟩
  rw [nativeOrbit_expandedSeed]
  apply Submodule.add_mem
  · exact Submodule.subset_span ⟨n, rfl⟩
  · exact Submodule.subset_span ⟨n+1, rfl⟩

end RankConservation

#check originalX_owner_N_plus_N_squared
#check originalX_owner_expanded_seed_class
#check nativeOrbit_expandedSeed
#check ownerExpandedSeed_orbitSpan_le
#print axioms originalX_owner_N_plus_N_squared
#print axioms ownerExpandedSeed_orbitSpan_le

end GSTImageThreeOwnerPolynomialFold
