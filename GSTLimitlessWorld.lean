import GSTWorldCosmology

/-!
# GST Limitless World — RED specification probe

This file begins as the executable specification for the unbounded compact
algebraic cosmos.  The declarations checked below intentionally do not exist
at the RED stage.  Task 1 is green only when the exact interfaces and laws are
implemented without weakening the existing finite `WorldCell` / `WorldCoef`
API.
-/

namespace GSTLimitlessWorld

open GSTWorldCosmology

#check CosmicCell
#check CosmicCoef
#check windowExtend
#check windowRestrict
#check SupportInWindow
#check windowRestrict_windowExtend
#check windowExtend_windowRestrict_of_support
#check windowRestrict_nested

example (carryDepth digitDepth : Nat)
    (f : WorldCoef carryDepth digitDepth) :
    windowRestrict carryDepth digitDepth (windowExtend f) = f := by
  exact windowRestrict_windowExtend carryDepth digitDepth f

example (carryDepth digitDepth : Nat)
    (g : CosmicCoef)
    (h : SupportInWindow carryDepth digitDepth g) :
    windowExtend (windowRestrict carryDepth digitDepth g) = g := by
  exact windowExtend_windowRestrict_of_support carryDepth digitDepth g h

example (g : CosmicCoef) :
    windowRestrict 0 0 g = (fun c => nomatch c) := by
  funext c
  exact Fin.elim0 c.1

end GSTLimitlessWorld
