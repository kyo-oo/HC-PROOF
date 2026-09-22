import Mathlib
import GSTTransferBridge
import GSTWorldCrownBridge
import GSTDimensionFreeHodgeDiagonal

/-!
# GST LEGACY HODGE / TRANSFER ABSORPTION

The historical Layer 10-12 machinery uses the fixed 4 x 3 wave chart,
Fin 12 addresses, p < 3, and the diagonal address 4p.

The upgraded cosmology has already replaced those ingredients by:
* arbitrary world shape;
* AddressRing N;
* arbitrary live diagonal weight p < A, p < B;
* diagonal code (B+1)p.

This file proves that the historical objects are literally the 4 x 3
specialization of the upgraded parent objects.

No theorem is renamed into strength.  The old dictionary, support predicate,
cycle class, and rank-one theorem are absorbed by exact comparison maps.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

namespace GSTLegacyHodgeAbsorption

open GSTWaveCohomology
open GSTWorldCosmology
open GSTWorldCrownBridge
open GSTWorldRecoordinationGroupoid
open GSTUniversalAddressBridge
open GSTDimensionFreeHodgeDiagonal
open GSTHodgeAssault
open GSTTransferBridge

/-- **THE OLD FIN-12 ADDRESS IS THE UNIVERSAL ADDRESS AT 4 x 3.** -/
theorem legacy_addr_eq_universal
    (f : WaveCoef) :
    addr f =
      worldAddress (outputShape 4 3) (liftWave f) := by
  funext i
  let x : ShapeState (outputShape 4 3) :=
    (shapeCodeEquiv (outputShape 4 3)).symm i
  have hcode :
      worldCode (outputShape 4 3) x = i.1 := by
    unfold worldCode
    simp [x]
  have hnum :
      3 * x.1.1 + x.2.1 = i.1 := by
    rw [worldCode_expanded] at hcode
    omega
  calc
    addr f i = gev f i.1 := rfl
    _ = gev f (3 * x.1.1 + x.2.1) := by rw [hnum]
    _ = f (worldToWave x) := by
      symm
      exact wave_coordinate_at
        f x.1.1 x.2.1 x.1.2 x.2.2
    _ = liftWave f x := rfl
    _ = worldAddress (outputShape 4 3) (liftWave f) i := by
      simp [worldAddress, x]

/-- The old additive/bijective dictionary is therefore inherited from the
universal linear address equivalence. -/
theorem legacy_addr_bijective_from_universal :
    Function.Bijective addr := by
  rw [show addr =
      fun f : WaveCoef =>
        worldAddress (outputShape 4 3) (liftWave f) by
          funext f
          exact legacy_addr_eq_universal f]
  constructor
  · intro f g h
    apply liftWave_injective
    exact (worldAddress_injective (outputShape 4 3)) h
  · intro phi
    obtain ⟨w, hw⟩ :=
      worldAddress_surjective (outputShape 4 3) phi
    refine ⟨lowerWave w, ?_⟩
    rw [legacy_addr_eq_universal, liftWave_lowerWave]
    exact hw

/-- **OLD HODGE SUPPORT = UNIVERSAL DIAGONAL SUPPORT.**
This equivalence is valid for every natural p; no p < 3 hypothesis is
needed merely to compare the predicates. -/
theorem legacy_hodge_iff_universal
    (p : Nat) (f : WaveCoef) :
    isHodgeClass p f ↔
      isWorldHodgeClass p (liftWave f) := by
  constructor
  · intro hf x hx
    exact hf (worldToWave x) hx
  · intro hf c hc
    have h := hf (waveToWorld c) hc
    simpa [liftWave, worldToWave_waveToWorld] using h

/-- The old algebraic cycle class is exactly the universal diagonal basis
class in the 4 x 3 chart. -/
theorem legacy_cycleClass_eq_universal
    (p : Nat) (hp : p < 3) :
    liftWave (cycleClass p) =
      worldDiagonalClass
        (A:=4) (B:=3) (p:=p) (by omega) hp := by
  funext x
  by_cases hC : x.1.1 = p
  · by_cases hd : x.2.1 = p
    · have hx :
        x = diagonalState
          (A:=4) (B:=3) (p:=p) (by omega) hp := by
        apply Prod.ext
        · apply Fin.ext
          exact hC
        · apply Fin.ext
          exact hd
      subst x
      simp [liftWave, worldToWave, cycleClass,
        worldDiagonalClass, worldBasis, diagonalState,
        cellClass, S12]
    · have hold :
        cycleClass p (worldToWave x) = 0 :=
          cycle_at_offdiagonal p hp
            x.1.1 x.2.1 x.1.2 x.2.2
            (by exact fun h => hd h.2)
      have hnew :
        worldDiagonalClass
          (A:=4) (B:=3) (p:=p) (by omega) hp x = 0 :=
        worldDiagonalClass_off_diagonal
          (A:=4) (B:=3) (p:=p) (by omega) hp x
          (Or.inr hd)
      simpa [liftWave] using hold.trans hnew.symm
  · have hold :
      cycleClass p (worldToWave x) = 0 :=
        cycle_at_offdiagonal p hp
          x.1.1 x.2.1 x.1.2 x.2.2
          (by exact fun h => hC h.1)
    have hnew :
      worldDiagonalClass
        (A:=4) (B:=3) (p:=p) (by omega) hp x = 0 :=
      worldDiagonalClass_off_diagonal
        (A:=4) (B:=3) (p:=p) (by omega) hp x
        (Or.inl hC)
    simpa [liftWave] using hold.trans hnew.symm

/-- The historical diagonal address 4p is the universal (B+1)p law. -/
theorem legacy_diagonal_address_is_universal
    (p : Nat) (hp : p < 3) :
    (diagonalAddress
      (A:=4) (B:=3) (p:=p) (by omega) hp).1 = 4*p :=
  hc_diagonal_address hp

/-- **LEGACY RANK-ONE HODGE THEOREM ABSORBED BY THE UNIVERSAL PARENT.**
The forward classification is obtained by transporting the dimension-free
rank-one theorem back through the exact 4 x 3 chart. -/
theorem legacy_hodge_rank_one_from_universal
    (p : Nat) (hp : p < 3)
    (f : WaveCoef)
    (hf : isHodgeClass p f) :
    ∃! z : ℤ,
      f = fun c => z * cycleClass p c := by
  have hfu :
      isWorldHodgeClass p (liftWave f) :=
    (legacy_hodge_iff_universal p f).mp hf
  obtain ⟨z, hz, huniq⟩ :=
    (world_hodge_rank_one
      (A:=4) (B:=3) (p:=p)
      (by omega) hp (liftWave f)).mp hfu
  have hcycle := legacy_cycleClass_eq_universal p hp
  refine ⟨z, ?_, ?_⟩
  · apply liftWave_injective
    funext x
    calc
      liftWave f x =
          z * worldDiagonalClass
            (A:=4) (B:=3) (p:=p) (by omega) hp x :=
        congrFun hz x
      _ = z * liftWave (cycleClass p) x := by
        rw [hcycle]
      _ = liftWave (fun c => z * cycleClass p c) x := by
        rfl
  · intro w hw
    apply huniq w
    funext x
    calc
      liftWave f x =
          liftWave (fun c => w * cycleClass p c) x := by
        exact congrFun (congrArg liftWave hw) x
      _ = w * liftWave (cycleClass p) x := rfl
      _ = w * worldDiagonalClass
          (A:=4) (B:=3) (p:=p) (by omega) hp x := by
        rw [hcycle]

/-- The universal address image of the historical cycle is exactly the old
degree-4p monomial. -/
theorem legacy_cycle_address_absorbed
    (p : Nat) (hp : p < 3) :
    worldAddress (outputShape 4 3)
      (worldDiagonalClass
        (A:=4) (B:=3) (p:=p) (by omega) hp)
      =
    clMono (4*p) := by
  rw [← legacy_cycleClass_eq_universal p hp]
  rw [← legacy_addr_eq_universal]
  exact addr_cycleClass p

/-- Capstone: Layer 10-12 fixed-chart objects are specializations of the
dimension-free address/Hodge cosmology. -/
theorem legacy_hodge_transfer_absorption_crown :
    (∀ f : WaveCoef,
      addr f =
        worldAddress (outputShape 4 3) (liftWave f))
    ∧ (∀ p f,
      isHodgeClass p f ↔
        isWorldHodgeClass p (liftWave f))
    ∧ (∀ p (hp : p < 3),
      liftWave (cycleClass p) =
        worldDiagonalClass
          (A:=4) (B:=3) (p:=p) (by omega) hp)
    ∧ (∀ p (hp : p < 3) f,
      isHodgeClass p f ->
        ∃! z : ℤ, f = fun c => z * cycleClass p c) := by
  exact ⟨
    legacy_addr_eq_universal,
    legacy_hodge_iff_universal,
    legacy_cycleClass_eq_universal,
    legacy_hodge_rank_one_from_universal⟩

#check legacy_addr_eq_universal
#check legacy_addr_bijective_from_universal
#check legacy_hodge_iff_universal
#check legacy_cycleClass_eq_universal
#check legacy_diagonal_address_is_universal
#check legacy_hodge_rank_one_from_universal
#check legacy_cycle_address_absorbed
#check legacy_hodge_transfer_absorption_crown

#print axioms legacy_addr_eq_universal
#print axioms legacy_hodge_iff_universal
#print axioms legacy_cycleClass_eq_universal
#print axioms legacy_hodge_rank_one_from_universal
#print axioms legacy_hodge_transfer_absorption_crown

end GSTLegacyHodgeAbsorption
