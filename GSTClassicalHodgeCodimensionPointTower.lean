import GSTClassicalHodgePrincipalCutNonzeroForcesExactSuccessor
import GSTClassicalHodgeCodimensionZeroDegreeApex

/-!
# GST CLASSICAL HODGE — CODIMENSION POINT TOWER

This module removes the ghost-indexed codimension-point existence burden from
GST Plane Completeness.

The preceding principal-cut theorem already proves that nonvanishing of the
native principal-cut image of an actual codimension-p point manufactures an
actual ambient codimension-(p+1) point.  The projective carrier already has a
canonical codimension-zero apex.  Therefore one uniform LOCAL law saying that
the native principal cut of every tower point survives recursively generates
actual codimension points at every finite weight.

This is stronger and cleaner than separately postulating a point at each weight
selected by a hypothetical Hodge ghost.  No Hodge target, separator sheet,
cycle representative of a target class, or Plane Completeness statement occurs
in the local survival law.
-/

set_option maxHeartbeats 120000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeCodimensionPointTower

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgePrincipalCutSuccessorOperator
open GSTClassicalHodgePrincipalCutNonzeroForcesExactSuccessor
open GSTClassicalHodgeCodimensionZeroDegreeApex
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeOmniversalSeparatorGhostCrown

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- **UNIFORM LOCAL PRINCIPAL-CUT SURVIVAL LAW.**

Every actual codimension-p point has a nonzero geometry-built principal-cut
successor.  This law is purely native and contains no Hodge target or ghost
index. -/
def NativePointSuccessorNonvanishing
    (V : SmoothProjectiveComplexScheme) : Prop :=
  ∀ (p : Nat) (x : CodimensionPoint V.X p),
    successorNativeOperator V p (codimensionPointCycle V.X p x) ≠ 0

/-- **LIMITLESS ACTUAL CODIMENSION-POINT TOWER.**

Starting from the canonical codimension-zero generic apex, repeatedly extract
the actual exact ambient successor forced by native principal-cut
nonvanishing. -/
noncomputable def codimensionPointTower
    (V : SmoothProjectiveComplexScheme)
    [Nonempty V.X]
    (hstep : NativePointSuccessorNonvanishing V) :
    (p : Nat) → CodimensionPoint V.X p
  | 0 => apexCodimensionZeroPoint V
  | p + 1 =>
      Classical.choice
        (exists_codimensionPoint_succ_of_native_point_nonzero
          (V := V) p (codimensionPointTower V hstep p)
          (hstep p (codimensionPointTower V hstep p)))

/-- Every finite codimension therefore has an actual point under the single
uniform local survival law. -/
theorem codimensionPoint_exists_of_nativePointSuccessorNonvanishing
    (V : SmoothProjectiveComplexScheme)
    [Nonempty V.X]
    (hstep : NativePointSuccessorNonvanishing V)
    (p : Nat) :
    Nonempty (CodimensionPoint V.X p) :=
  ⟨codimensionPointTower V hstep p⟩

/-- In particular every weight selected by a hypothetical omniversal separator
ghost has an actual codimension point.  The ghost contributes only its natural
number weight; no ghost-specific geometric existence axiom remains. -/
theorem ghostCodimensionPoints_of_nativePointSuccessorNonvanishing
    (G : GeometricCycleClassSpine V H)
    [Nonempty V.X]
    (hstep : NativePointSuccessorNonvanishing V) :
    ∀ E : OmniversalSeparatorGhost G,
      Nonempty (CodimensionPoint V.X E.weight) := by
  intro E
  exact codimensionPoint_exists_of_nativePointSuccessorNonvanishing
    V hstep E.weight

#check NativePointSuccessorNonvanishing
#check codimensionPointTower
#check codimensionPoint_exists_of_nativePointSuccessorNonvanishing
#check ghostCodimensionPoints_of_nativePointSuccessorNonvanishing

#print axioms codimensionPointTower
#print axioms codimensionPoint_exists_of_nativePointSuccessorNonvanishing
#print axioms ghostCodimensionPoints_of_nativePointSuccessorNonvanishing

end GSTClassicalHodgeCodimensionPointTower
