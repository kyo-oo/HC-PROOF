import GSTClassicalHodgeStrictCorrespondenceChainTransfer

/-!
# GST CLASSICAL HODGE — FINITE TRANSFER RIGIDITY

A nonzero-degree chain transfer is much stronger than set-theoretic finiteness.
After normalization it is a literal section of the projection chain map.
Consequently the projection is split-surjective on the complete singular chain
complex and its pullback is injective on every rational Betti degree.

This theorem is the geometry firewall separating true full-degree finite
correspondences from lower-dimensional closed finite carriers.  The latter may
still define graded algebraic correspondences, but they cannot carry the
same-degree transfer packet used by the whole-Betti push-pull construction.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicTopology

namespace GSTClassicalHodgeStrictCorrespondenceTransferRigidity

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTClassicalHodgeSchemeFiniteCorrespondenceFirewall
open GSTClassicalHodgeStrictCorrespondenceAnalyticSpan
open GSTClassicalHodgeStrictCorrespondenceChainTransfer
open GSTClassicalHodgeStrictCorrespondenceBettiTracePushPull

variable {V : SmoothProjectiveComplexScheme}
variable (A : AnalytificationData V)
variable (K : SchemeBiFiniteClosedCorrespondence V)

/-- Normalize a nonzero-degree finite chain transfer. -/
noncomputable def normalizedChainTransfer
    (T : RightFiniteChainTransfer A K) :
    rationalSingularChains A ⟶ carrierSingularChains A K :=
  T.degree⁻¹ • T.transfer

/-- **CHAIN SPLITTING THEOREM.**  A genuine finite transfer makes the right
projection chain map a split epimorphism. -/
theorem normalizedChainTransfer_right
    (T : RightFiniteChainTransfer A K) :
    normalizedChainTransfer A K T ≫ rightChainMap A K =
      𝟙 (rationalSingularChains A) := by
  rw [normalizedChainTransfer]
  simp only [Preadditive.smul_comp]
  rw [T.transfer_right]
  ext m x
  simp [T.degree_ne_zero]

/-- The right chain projection is therefore an epimorphism in the chain-complex
category. -/
instance rightChainMap_epi
    (T : RightFiniteChainTransfer A K) : Epi (rightChainMap A K) := by
  apply epi_of_epi_fac (normalizedChainTransfer A K T)
  rw [normalizedChainTransfer_right A K T]
  infer_instance

/-- The induced right Betti pullback is injective in every degree.  This is the
cohomological shadow of the chain splitting and follows through the already
constructed trace descent. -/
theorem rightCohomologyPullback_injective_all
    (T : RightFiniteChainTransfer A K) :
    ∀ n : Nat, Function.Injective (rightCohomologyPullback A K n) := by
  intro n
  exact (T.toRightFiniteBettiTrace n).rightPullback_injective

/-- No class can disappear under pullback once a genuine nonzero-degree chain
transfer exists. -/
theorem rightPullback_ne_zero_of_ne_zero
    (T : RightFiniteChainTransfer A K)
    (n : Nat)
    {alpha : RationalSingularCohomology A n}
    (ha : alpha ≠ 0) :
    rightCohomologyPullback A K n alpha ≠ 0 := by
  intro hz
  apply ha
  exact (T.rightCohomologyPullback_injective_all A K n)
    (hz.trans (map_zero _).symm)

/-- Transfer-existence predicate.  This is strictly stronger than scheme
finiteness and is the correct eligibility test for same-degree Betti trace. -/
def HasFullDegreeRightTransfer : Prop :=
  Nonempty (RightFiniteChainTransfer A K)

/-- Full-degree transfer automatically gives Betti-faithful right pullback in
every degree. -/
theorem HasFullDegreeRightTransfer.bettiFaithful
    (hT : HasFullDegreeRightTransfer A K) :
    ∀ n : Nat, Function.Injective (rightCohomologyPullback A K n) := by
  rcases hT with ⟨T⟩
  exact T.rightCohomologyPullback_injective_all A K

#check normalizedChainTransfer
#check normalizedChainTransfer_right
#check rightCohomologyPullback_injective_all
#check HasFullDegreeRightTransfer
#check HasFullDegreeRightTransfer.bettiFaithful

end GSTClassicalHodgeStrictCorrespondenceTransferRigidity
