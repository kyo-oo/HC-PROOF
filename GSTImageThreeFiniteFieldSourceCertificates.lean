import Mathlib

/-!
# GST Image 3 — kernel-checkable finite-field native cyclicity leaf

Original CM-wave F_a = U + J + a M + [J,M] has a 12x12 Krylov
determinant equal to Q8(a) * Q12(a), by an independent exact symbolic
matrix identity recorded in the computation/derivation sources.
This file FORMALLY checks the complete finite-field obstruction leaf:
neither actual integer factor Q8 nor Q12 has ANY root in F_11.

This is a complete universal statement over the eleven-element
finite field, not a sample or an unchecked external computation.
The map from this finite-field certificate to Q-rational non-root
requires the separately recorded rational-root argument and the
exact source determinant identity. Those are not silently assumed
as Lean premises here, and this file does not prove Hodge.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace GSTImageThreeFiniteFieldSourceCertificates

/-- Degree-eight exact original-source determinant factor, modulo 11. -/
def originalP8Mod11 (a : ZMod 11) : ZMod 11 :=
  -130491 - 27750*a - 25120*a^2 - 31800*a^3 +
   7068*a^4 - 3304*a^5 + 1520*a^6 - 80*a^7 + 64*a^8

/-- Degree-twelve exact original-source spectral resultant, modulo 11. -/
def originalP12Mod11 (a : ZMod 11) : ZMod 11 :=
  -10623 + 474348*a + 710952*a^2 + 141208*a^3 +
   696720*a^4 - 249912*a^5 + 418988*a^6 -
   196384*a^7 + 166048*a^8 - 59264*a^9 +
   33664*a^10 - 6912*a^11 + 2560*a^12

/-- Every element of the ENTIRE eleven-point field is excluded as a
root of the genuine original degree-eight source factor. -/
theorem originalP8Mod11_no_roots :
    ∀ a : ZMod 11, originalP8Mod11 a ≠ 0 := by
  decide

/-- Every element of the ENTIRE eleven-point field is excluded as a
root of the genuine original degree-twelve spectral resultant. -/
theorem originalP12Mod11_no_roots :
    ∀ a : ZMod 11, originalP12Mod11 a ≠ 0 := by
  decide

/-- For EVERY modulo-eleven direct-source strength, both ORIGINAL
independent factors survive, so their product is a unit. -/
theorem originalCMSourceProductMod11_nonzero (a : ZMod 11) :
    originalP8Mod11 a * originalP12Mod11 a ≠ 0 :=
  mul_ne_zero (originalP8Mod11_no_roots a)
    (originalP12Mod11_no_roots a)

/-- Rational root reduction is legitimate because neither leading
integer coefficient is divisible by eleven. -/
theorem originalCMSourceLeadingCoefficients_units :
    (64 : ZMod 11) ≠ 0 ∧ (2560 : ZMod 11) ≠ 0 := by
  decide

#check originalP8Mod11_no_roots
#check originalP12Mod11_no_roots
#check originalCMSourceProductMod11_nonzero
#check originalCMSourceLeadingCoefficients_units

#print axioms originalP8Mod11_no_roots
#print axioms originalP12Mod11_no_roots
#print axioms originalCMSourceProductMod11_nonzero

end GSTImageThreeFiniteFieldSourceCertificates
