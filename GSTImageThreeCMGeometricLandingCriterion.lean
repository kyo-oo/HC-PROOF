import GSTImageThreePureCMOriginalXLanding
import Mathlib

/-!
# GST Image3 pure CM-curvature rank-adaptive native-to-Hodge landing gate

This is a NEW precise theorem answering the author's requirement "what
else must be proved?" from the original all-rank CM-only native fold.

A full cyclic native signal may have ANY finite rank, as shown in
the accompanying true U/J/[J,M] Wolfram/CRT derivation. But this does
NOT automatically yield algebraic Hodge classes on a chosen X.

The correct algebraic landing test:
* a linear map L from the true GST native signal to the CANONICAL
  rational Hodge target space W;
* a true original-X native Chow operator N, its Betti action B, and
  a canonical Chow cycle-class map cl, with exact naturality;
* L intertwines the native GST F and actual geometric Betti B;
* the single GST root signal lands on the class of an ACTUAL Chow seed;
* if L is surjective, native cyclicity forces cl surjective.

The theorem proves **more** than unstructured rank language: it says
every image of a cyclic native GST signal lands inside the actual
algebraic cycle-class image, WITHOUT assuming that any unknown Hodge
class has a native cycle. This makes the geometric bottleneck exact.

No surjective L is postulated as existing for arbitrary X. The
universal existence construction, rather than this theorem, is the
remaining Hodge hypothesis.
-/

set_option maxHeartbeats 2500000
noncomputable section

namespace GSTImageThreeCMGeometricLandingCriterion

universe u v w

variable {V : Type u} {C : Type v} {W : Type w}
variable [AddCommGroup V] [Module ℚ V]
variable [AddCommGroup C] [Module ℚ C]
variable [AddCommGroup W] [Module ℚ W]

/-- Any genuine linear GST fold orbit, in the owner's true
rank-adaptive native module; finite or transfinite world indexing
is NOT silently assumed to imply finite cohomological dimension. -/
def gstOrbit (T : V →ₗ[ℚ] V) (v₀ : V) : ℕ → V
  | 0 => v₀
  | n+1 => T (gstOrbit T v₀ n)

/-- ALL elements of the native GST CYCLIC source map to classes of
ACTUAL original-X native cycles when the original Chow–Betti square,
the single root native cycle, and exact F-intertwining are given.
No assumed surjectivity of cl or guessed Hodge basis enters. -/
theorem cyclic_landing_always_algebraic
    (T : V →ₗ[ℚ] V) (N : C →ₗ[ℚ] C)
    (B : W →ₗ[ℚ] W) (L : V →ₗ[ℚ] W)
    (cl : C →ₗ[ℚ] W) (v₀ : V) (z₀ : C)
    (hCyclic :
      Submodule.span ℚ (Set.range (gstOrbit T v₀)) = ⊤)
    (hIntertwines : ∀ v, L (T v) = B (L v))
    (hNaturality : ∀ z, cl (N z) = B (cl z))
    (hSeedClass : L v₀ = cl z₀)
    (v : V) :
    L v ∈ LinearMap.range cl := by
  have horbit :
      ∀ n : ℕ, L (gstOrbit T v₀ n) =
        cl (gstOrbit N z₀ n) := by
    intro n
    induction n with
    | zero =>
      simpa only [gstOrbit] using hSeedClass
    | succ n ih =>
      simp only [gstOrbit]
      rw [hIntertwines, ih, hNaturality]
  have hSpan :
      Submodule.span ℚ (Set.range (gstOrbit T v₀)) ≤
        (LinearMap.range cl).comap L := by
    apply Submodule.span_le.mpr
    rintro x ⟨n, rfl⟩
    change L (gstOrbit T v₀ n) ∈ LinearMap.range cl
    exact ⟨gstOrbit N z₀ n, (horbit n).symm⟩
  have hv :
      v ∈ Submodule.span ℚ (Set.range (gstOrbit T v₀)) := by
    rw [hCyclic]
    exact Submodule.mem_top
  exact hSpan hv

/-- THIS IS THE PRECISE RANK-TRANSFER GATE FOR THE HODGE ANTECEDENT.
A genuine source-cycle seed, natural true geometric operators, and
SURJECTIVE honest Hodge landing from a cyclic native GST space
construct an actual Chow representative of EVERY target Hodge class.
The only unproved universal requirement is constructing such a
surjective L from the geometry of every original X,p. -/
theorem full_hodge_of_genuine_surjective_cyclic_landing
    (T : V →ₗ[ℚ] V) (N : C →ₗ[ℚ] C)
    (B : W →ₗ[ℚ] W) (L : V →ₗ[ℚ] W)
    (cl : C →ₗ[ℚ] W) (v₀ : V) (z₀ : C)
    (hCyclic :
      Submodule.span ℚ (Set.range (gstOrbit T v₀)) = ⊤)
    (hIntertwines : ∀ v, L (T v) = B (L v))
    (hNaturality : ∀ z, cl (N z) = B (cl z))
    (hSeedClass : L v₀ = cl z₀)
    (hL : Function.Surjective L) :
    Function.Surjective cl := by
  intro alpha
  obtain ⟨v, rfl⟩ := hL alpha
  exact cyclic_landing_always_algebraic
    T N B L cl v₀ z₀
    hCyclic hIntertwines hNaturality hSeedClass v

/-- Constructive impossibility criterion:
a non-algebraic rational Hodge class, IF it exists, would obstruct
every surjective original-X landing satisfying the honest geometry
requirements above. This is a no-circularity theorem, not an
assertion that such a non-algebraic class exists. -/
theorem no_surjective_landing_of_missing_algebraic_class
    (T : V →ₗ[ℚ] V) (N : C →ₗ[ℚ] C)
    (B : W →ₗ[ℚ] W) (L : V →ₗ[ℚ] W)
    (cl : C →ₗ[ℚ] W) (v₀ : V) (z₀ : C)
    (hCyclic :
      Submodule.span ℚ (Set.range (gstOrbit T v₀)) = ⊤)
    (hIntertwines : ∀ v, L (T v) = B (L v))
    (hNaturality : ∀ z, cl (N z) = B (cl z))
    (hSeedClass : L v₀ = cl z₀)
    (hMissing : ¬ Function.Surjective cl) :
    ¬ Function.Surjective L := by
  intro hL
  exact hMissing
    (full_hodge_of_genuine_surjective_cyclic_landing
      T N B L cl v₀ z₀
      hCyclic hIntertwines hNaturality hSeedClass hL)

#check gstOrbit
#check cyclic_landing_always_algebraic
#check full_hodge_of_genuine_surjective_cyclic_landing
#check no_surjective_landing_of_missing_algebraic_class

#print axioms cyclic_landing_always_algebraic
#print axioms full_hodge_of_genuine_surjective_cyclic_landing

end GSTImageThreeCMGeometricLandingCriterion
