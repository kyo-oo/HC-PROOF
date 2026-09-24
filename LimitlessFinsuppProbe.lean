import Mathlib

noncomputable section

abbrev ProbeCell : Type := Nat × Nat
abbrev ProbeCoefArrow : Type := ProbeCell →₀ ℤ
abbrev ProbeCoefExplicit : Type := Finsupp ProbeCell ℤ

#synth AddCommMonoid (Finsupp ProbeCell ℤ)
#synth AddCommMonoid ProbeCoefArrow
#synth AddCommMonoid ProbeCoefExplicit

example (f g : ProbeCoefExplicit) : ProbeCoefExplicit := f + g

example (n : Nat) (f : ProbeCoefExplicit) : ProbeCoefExplicit :=
  f.sum fun c z => Finsupp.single (c.1, c.2 + n) z
