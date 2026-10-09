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

end GSTGeneralSpace
