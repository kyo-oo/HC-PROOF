import GSTGeneralSpaceDuality

universe u v w

namespace GSTGeneralSpace

/-- Cohomological structure is an optional realization capability, not part of
General Space ontology.  It is deliberately grading-generic. -/
structure CohomologyGeometry (G : GeneralSpace) (R : Type w)
    [CommSemiring R] where
  Grade : Type w
  Coh : Grade → Type w
  addCommMonoid : ∀ q, AddCommMonoid (Coh q)
  module : ∀ q, Module R (Coh q)
  gradeMul : Grade → Grade → Grade
  cup : ∀ {p q}, Coh p → Coh q → Coh (gradeMul p q)
  cup_zero_left : ∀ {p q} (b : Coh q), cup (0 : Coh p) b = 0
  cup_zero_right : ∀ {p q} (a : Coh p), cup a (0 : Coh q) = 0

namespace CohomologyGeometry

variable {G : GeneralSpace} {R : Type w} [CommSemiring R]

/-- A cohomological observable attached to a General Space point. -/
structure ClassField (C : CohomologyGeometry G R) where
  grade : C.Grade
  classAt : G.Point → C.Coh grade

/-- A graded transport operation, stated independently of coordinates. -/
structure Transport (C : CohomologyGeometry G R) where
  map : ∀ {q : C.Grade} {x y : G.Point}, G.Path x y → C.Coh q → C.Coh q
  map_id : ∀ {q} (x : G.Point) (a : C.Coh q), map (G.idPath x) a = a
  map_comp : ∀ {q} {x y z : G.Point}
      (α : G.Path x y) (β : G.Path y z) (a : C.Coh q),
    map (G.compPath α β) a = map β (map α a)
  map_cup : ∀ {p q} {x y : G.Point} (γ : G.Path x y)
      (a : C.Coh p) (b : C.Coh q),
    map γ (C.cup a b) = C.cup (map γ a) (map γ b)

end CohomologyGeometry

#check CohomologyGeometry
#check CohomologyGeometry.ClassField
#check CohomologyGeometry.Transport


/-! ## GST native cycle geometry versus reversible General Space paths

All GST cohomology, cosmology, CM/NM, and world-transport laws must
respect the REAL native cycle-class map. This new compatibility
theorem proves a sharp algebraicity invariant of reversible GST
recoordination: no series of reversible path operations can turn
an unrepresented cohomology class into an algebraic cycle.

It does not rule out genuinely new sources: an irreversible native
world birth, exceptional Gysin class, or extra geometric cycle can
change the native image. It also does not disprove the Hodge conjecture:
the argument is about the precise power of one kind of GST operator.
-/

namespace NativeCycleRecoordination

variable {G : GeneralSpace}
variable {N H : Type*}
  [AddCommGroup N] [Module ℚ N]
  [AddCommGroup H] [Module ℚ H]

/-- A native algebraic cycle class map intertwined with ACTUAL GST
General Space paths, both at the native-cycle and rational Hodge
cohomology levels. No reverse cohomology-to-Chow selector is given. -/
structure CyclePathRealization
    (G : GeneralSpace)
    (N H : Type*)
    [AddCommGroup N] [Module ℚ N]
    [AddCommGroup H] [Module ℚ H] where
  cycleClass : N →ₗ[ℚ] H
  nativeTransport :
    ∀ {x y : G.Point}, G.Path x y → N →ₗ[ℚ] N
  hodgeTransport :
    ∀ {x y : G.Point}, G.Path x y → H →ₗ[ℚ] H
  naturality : ∀ {x y : G.Point} (γ : G.Path x y) (Z : N),
    cycleClass (nativeTransport γ Z) =
      hodgeTransport γ (cycleClass Z)
  hodge_id : ∀ (x : G.Point) (alpha : H),
    hodgeTransport (G.idPath x) alpha = alpha
  hodge_comp : ∀ {x y z : G.Point}
    (γ : G.Path x y) (δ : G.Path y z) (alpha : H),
    hodgeTransport (G.compPath γ δ) alpha =
      hodgeTransport δ (hodgeTransport γ alpha)

/-- FORWARD: every actual native Chow representative survives any
general-space geometric path compatible with the cycle-class map. -/
theorem transported_native_cycle_stays_algebraic
    (P : CyclePathRealization G N H)
    {x y : G.Point} (γ : G.Path x y)
    (alpha : H)
    (h : alpha ∈ LinearMap.range P.cycleClass) :
    P.hodgeTransport γ alpha ∈ LinearMap.range P.cycleClass := by
  obtain ⟨Z, hZ⟩ := h
  refine ⟨P.nativeTransport γ Z, ?_⟩
  calc
    P.cycleClass (P.nativeTransport γ Z) =
      P.hodgeTransport γ (P.cycleClass Z) := P.naturality γ Z
    _ = P.hodgeTransport γ alpha := by rw [hZ]

/-- REVERSE: a reversible GST recoordination cannot hide a
nonalgebraic Hodge direction. If the transported class has an
actual rational Chow representative, its backward native transport
constructs a representative of the original class. -/
theorem algebraicity_iff_reversible_general_space_transport
    (P : CyclePathRealization G N H)
    {x y : G.Point}
    (ρ : Recoordination G x y)
    (alpha : H) :
    alpha ∈ LinearMap.range P.cycleClass ↔
      P.hodgeTransport ρ.forward alpha ∈
        LinearMap.range P.cycleClass := by
  constructor
  · exact transported_native_cycle_stays_algebraic P ρ.forward alpha
  · intro h
    obtain ⟨Z, hZ⟩ := h
    refine ⟨P.nativeTransport ρ.backward Z, ?_⟩
    calc
      P.cycleClass (P.nativeTransport ρ.backward Z) =
        P.hodgeTransport ρ.backward (P.cycleClass Z) :=
          P.naturality ρ.backward Z
      _ = P.hodgeTransport ρ.backward
            (P.hodgeTransport ρ.forward alpha) := by rw [hZ]
      _ = P.hodgeTransport
            (G.compPath ρ.forward ρ.backward) alpha := by
              rw [P.hodge_comp]
      _ = P.hodgeTransport (G.idPath x) alpha := by
              rw [ρ.forward_backward]
      _ = alpha := P.hodge_id x alpha

/-- Exact CONTRAPOSITIVE GST obstruction. No generalized world
recoordination, including composition of arbitrarily many
reversible presentations, can magically eliminate a missing
primitive rational Hodge direction from the native image. -/
theorem missing_native_direction_persists_recoordination
    (P : CyclePathRealization G N H)
    {x y : G.Point} (ρ : Recoordination G x y)
    (alpha : H)
    (hMissing : alpha ∉ LinearMap.range P.cycleClass) :
    P.hodgeTransport ρ.forward alpha ∉
      LinearMap.range P.cycleClass := by
  intro h
  exact hMissing
    ((algebraicity_iff_reversible_general_space_transport
      P ρ alpha).mpr h)

#check CyclePathRealization
#check algebraicity_iff_reversible_general_space_transport
#check missing_native_direction_persists_recoordination
#print axioms algebraicity_iff_reversible_general_space_transport
#print axioms missing_native_direction_persists_recoordination

end NativeCycleRecoordination

end GSTGeneralSpace
