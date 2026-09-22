import Mathlib
import GSTRadixWorldDynamics
import GSTGradedWorldAlgebra

/-!
# GST WORLD RECOORDINATION GROUPOID

The mixed-radix upgrade still keeps one rectangular world shape fixed.
This layer removes that restriction.

A GST world shape of total cardinality N is any rectangle A x B with
A * B = N.  Every such shape has a canonical code equivalence with Fin N.
Therefore every pair of equal-cardinality world shapes is canonically
recoordinated through Fin N.

The resulting transport has:
* exact code conservation;
* unique targets;
* identity, inverse and composition laws;
* functorial transport of coefficient fields;
* functorial transport of every code spectral sector;
* functorial polynomial functional calculus;
* the previous mixed-radix transpose as one swapped-chart specialization.

Thus rectangular world shape is coordinate data, not a mathematical
invariant of the underlying finite GST state universe.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

namespace GSTWorldRecoordinationGroupoid

open GSTRadixWorldDynamics
open GSTGradedWorldAlgebra

/-- A rectangular presentation of one N-state GST universe. -/
structure GSTWorldShape (N : Nat) where
  rows : Nat
  cols : Nat
  area_eq : rows * cols = N

/-- State type carried by one world shape. -/
abbrev ShapeState {N : Nat} (S : GSTWorldShape N) : Type :=
  Fin S.rows × Fin S.cols

/-- Canonical row-major coding of a shaped world into the underlying N states. -/
def shapeCodeEquiv {N : Nat} (S : GSTWorldShape N) :
    ShapeState S ≃ Fin N :=
  (finProdFinEquiv : Fin S.rows × Fin S.cols ≃ Fin (S.rows * S.cols)).trans
    (finCongr S.area_eq)

/-- Integer code of one state, independent of later recoordination. -/
def worldCode {N : Nat} (S : GSTWorldShape N) (x : ShapeState S) : Nat :=
  (shapeCodeEquiv S x).1

@[simp]
theorem worldCode_expanded
    {N : Nat} (S : GSTWorldShape N) (x : ShapeState S) :
    worldCode S x = x.2.1 + S.cols * x.1.1 := by
  rfl

theorem worldCode_lt
    {N : Nat} (S : GSTWorldShape N) (x : ShapeState S) :
    worldCode S x < N :=
  (shapeCodeEquiv S x).2

/-- Canonical recoordination between any two equal-cardinality GST worlds. -/
def worldRecoordinate
    {N : Nat} (S T : GSTWorldShape N) :
    ShapeState S ≃ ShapeState T :=
  (shapeCodeEquiv S).trans (shapeCodeEquiv T).symm

/-- Recoordination preserves the underlying state code exactly. -/
theorem worldRecoordinate_code
    {N : Nat} (S T : GSTWorldShape N) (x : ShapeState S) :
    worldCode T (worldRecoordinate S T x) = worldCode S x := by
  unfold worldCode worldRecoordinate
  simp

/-- A target with the same code is uniquely the canonical recoordination. -/
theorem worldRecoordinate_unique
    {N : Nat} (S T : GSTWorldShape N)
    (x : ShapeState S) (y : ShapeState T)
    (h : worldCode T y = worldCode S x) :
    worldRecoordinate S T x = y := by
  apply (shapeCodeEquiv T).injective
  apply Fin.ext
  simpa [worldCode] using h.symm

/-- Every source state has a unique equal-code target in every other shape. -/
theorem existsUnique_worldRecoordinate
    {N : Nat} (S T : GSTWorldShape N) (x : ShapeState S) :
    ∃! y : ShapeState T, worldCode T y = worldCode S x := by
  refine ⟨worldRecoordinate S T x, worldRecoordinate_code S T x, ?_⟩
  intro y hy
  exact (worldRecoordinate_unique S T x y hy).symm

/-- Recoordination by the same chart is identity. -/
theorem worldRecoordinate_self
    {N : Nat} (S : GSTWorldShape N) (x : ShapeState S) :
    worldRecoordinate S S x = x := by
  apply (shapeCodeEquiv S).injective
  simp [worldRecoordinate]

/-- Recoordination is exactly reversible by reversing the chart pair. -/
theorem worldRecoordinate_inverse
    {N : Nat} (S T : GSTWorldShape N) (y : ShapeState T) :
    (worldRecoordinate S T).symm y = worldRecoordinate T S y := by
  apply (shapeCodeEquiv S).injective
  simp [worldRecoordinate]

/-- **WORLD GROUPOID COMPOSITION.**
Passing through an intermediate rectangular chart is exactly direct
recoordination. -/
theorem worldRecoordinate_comp
    {N : Nat} (S T U : GSTWorldShape N) (x : ShapeState S) :
    worldRecoordinate T U (worldRecoordinate S T x) =
      worldRecoordinate S U x := by
  apply (shapeCodeEquiv U).injective
  simp [worldRecoordinate]

/-- Coefficient field living on one shaped finite world. -/
abbrev ShapeCoef {N : Nat} (S : GSTWorldShape N) : Type :=
  ShapeState S → ℤ

/-- Push a coefficient field through a world recoordination. -/
def transportCoef
    {N : Nat} (S T : GSTWorldShape N)
    (f : ShapeCoef S) : ShapeCoef T :=
  fun y => f ((worldRecoordinate S T).symm y)

theorem transportCoef_self
    {N : Nat} (S : GSTWorldShape N) (f : ShapeCoef S) :
    transportCoef S S f = f := by
  funext x
  simp [transportCoef, worldRecoordinate]

/-- **FUNCTORIAL COEFFICIENT TRANSPORT.** -/
theorem transportCoef_comp
    {N : Nat} (S T U : GSTWorldShape N)
    (f : ShapeCoef S) :
    transportCoef T U (transportCoef S T f) =
      transportCoef S U f := by
  funext z
  simp [transportCoef, worldRecoordinate]

/-- Spectral projector onto one invariant state code. -/
def codeSectorProj
    {N : Nat} (S : GSTWorldShape N) (k : Nat)
    (f : ShapeCoef S) : ShapeCoef S :=
  fun x => if worldCode S x = k then f x else 0

theorem codeSectorProj_idempotent
    {N : Nat} (S : GSTWorldShape N) (k : Nat)
    (f : ShapeCoef S) :
    codeSectorProj S k (codeSectorProj S k f) =
      codeSectorProj S k f := by
  funext x
  by_cases h : worldCode S x = k <;>
    simp [codeSectorProj, h]

theorem codeSectorProj_orthogonal
    {N : Nat} (S : GSTWorldShape N)
    (j k : Nat) (hjk : j ≠ k) (f : ShapeCoef S) :
    codeSectorProj S j (codeSectorProj S k f) = fun _ => 0 := by
  funext x
  by_cases hk : worldCode S x = k
  · have hj : worldCode S x ≠ j := by
      intro h
      exact hjk (h.symm.trans hk)
    simp [codeSectorProj, hk, hj]
  · simp [codeSectorProj, hk]

/-- All N code sectors sum exactly to the coefficient field. -/
theorem codeSectorProj_sum
    {N : Nat} (S : GSTWorldShape N) (f : ShapeCoef S) :
    (fun x => ∑ k ∈ Finset.range N, codeSectorProj S k f x) = f := by
  funext x
  classical
  have hmem : worldCode S x ∈ Finset.range N :=
    Finset.mem_range.mpr (worldCode_lt S x)
  rw [Finset.sum_eq_single (worldCode S x)]
  · simp [codeSectorProj]
  · intro b hb hne
    have hne' : worldCode S x ≠ b := hne.symm
    simp [codeSectorProj, hne']
  · intro hnot
    exact (hnot hmem).elim

/-- **SPECTRAL NATURALITY.**
World recoordination commutes with every exact code projector. -/
theorem transportCoef_codeSectorProj
    {N : Nat} (S T : GSTWorldShape N)
    (k : Nat) (f : ShapeCoef S) :
    transportCoef S T (codeSectorProj S k f) =
      codeSectorProj T k (transportCoef S T f) := by
  funext y
  have hcode :
      worldCode S ((worldRecoordinate S T).symm y) =
        worldCode T y := by
    rw [worldRecoordinate_inverse S T y]
    exact (worldRecoordinate_code T S y).symm
  by_cases h : worldCode T y = k <;>
    simp [transportCoef, codeSectorProj, h, hcode]

/-- Polynomial functional calculus of the invariant code observable. -/
def codePolyOp
    {N : Nat} (S : GSTWorldShape N)
    (p : Polynomial ℤ) (f : ShapeCoef S) : ShapeCoef S :=
  fun x => p.eval (worldCode S x : ℤ) * f x

/-- Polynomial observables are exactly natural under world recoordination. -/
theorem transportCoef_codePolyOp
    {N : Nat} (S T : GSTWorldShape N)
    (p : Polynomial ℤ) (f : ShapeCoef S) :
    transportCoef S T (codePolyOp S p f) =
      codePolyOp T p (transportCoef S T f) := by
  funext y
  have hcode :
      worldCode S ((worldRecoordinate S T).symm y) =
        worldCode T y := by
    rw [worldRecoordinate_inverse S T y]
    exact (worldRecoordinate_code T S y).symm
  simp [transportCoef, codePolyOp, hcode]

/-- Every code projector is an explicit integer spectral polynomial,
up to a nonzero integer scalar, on every shaped N-state world. -/
theorem codeSector_projector_polynomial
    {N : Nat} (S : GSTWorldShape N)
    (k : Nat) (hk : k < N) :
    ∃ (p : Polynomial ℤ) (c : ℤ), c ≠ 0 ∧
      ∀ (f : ShapeCoef S) (x : ShapeState S),
        codePolyOp S p f x = c * codeSectorProj S k f x := by
  refine ⟨worldKunnethPoly N k,
    (worldKunnethPoly N k).eval (k : ℤ),
    worldKunnethPoly_eval_self_ne_zero N k hk, ?_⟩
  intro f x
  unfold codePolyOp codeSectorProj
  by_cases h : worldCode S x = k
  · simp [h]
  · have hlt := worldCode_lt S x
    have hz :=
      worldKunnethPoly_eval_zero N k (worldCode S x) hlt h
    simp [h, hz]

/-- Standard output-oriented rectangular shape. -/
def outputShape (s b : Nat) : GSTWorldShape (s*b) where
  rows := s
  cols := b
  area_eq := rfl

/-- Input-oriented shape of the same s*b state universe. -/
def inputShape (s b : Nat) : GSTWorldShape (s*b) where
  rows := b
  cols := s
  area_eq := Nat.mul_comm b s

/-- Swap the old mixed-radix input coordinates into the input-shaped world. -/
def inputShapeState
    {s b : Nat} (x : RadixState s b) :
    ShapeState (inputShape s b) :=
  (x.2, x.1)

/-- **ABSORPTION OF MIXED-RADIX TRANSPOSE.**
The earlier transpose is exactly: swap into the input chart, then apply the
canonical equal-cardinality world recoordination. -/
theorem mixedRadixTranspose_is_worldRecoordinate
    {s b : Nat} (x : RadixState s b) :
    mixedRadixTranspose s b x =
      worldRecoordinate (inputShape s b) (outputShape s b)
        (inputShapeState x) := by
  apply mixedRadixTranspose_unique
  have h :=
    worldRecoordinate_code
      (inputShape s b) (outputShape s b)
      (inputShapeState x)
  simpa [worldCode_expanded, inputShape, outputShape,
    inputShapeState, inputCode, outputCode] using h

/-- Capstone: equal-cardinality world shapes form an exact finite
recoordination groupoid, and all code-spectral mathematics is natural
under that groupoid. -/
theorem world_recoordination_groupoid_crown :
    (∀ N (S T : GSTWorldShape N) (x : ShapeState S),
      worldCode T (worldRecoordinate S T x) = worldCode S x)
    ∧ (∀ N (S T U : GSTWorldShape N) (x : ShapeState S),
      worldRecoordinate T U (worldRecoordinate S T x) =
        worldRecoordinate S U x)
    ∧ (∀ N (S T : GSTWorldShape N) (f : ShapeCoef S) k,
      transportCoef S T (codeSectorProj S k f) =
        codeSectorProj T k (transportCoef S T f))
    ∧ (∀ N (S T : GSTWorldShape N)
        (p : Polynomial ℤ) (f : ShapeCoef S),
      transportCoef S T (codePolyOp S p f) =
        codePolyOp T p (transportCoef S T f)) := by
  exact ⟨worldRecoordinate_code, worldRecoordinate_comp,
    transportCoef_codeSectorProj, transportCoef_codePolyOp⟩

#check GSTWorldShape
#check worldRecoordinate
#check worldRecoordinate_code
#check worldRecoordinate_unique
#check existsUnique_worldRecoordinate
#check worldRecoordinate_comp
#check transportCoef_comp
#check codeSectorProj_sum
#check transportCoef_codeSectorProj
#check transportCoef_codePolyOp
#check codeSector_projector_polynomial
#check mixedRadixTranspose_is_worldRecoordinate
#check world_recoordination_groupoid_crown

#print axioms worldRecoordinate_code
#print axioms worldRecoordinate_unique
#print axioms worldRecoordinate_comp
#print axioms transportCoef_comp
#print axioms transportCoef_codeSectorProj
#print axioms codeSector_projector_polynomial
#print axioms mixedRadixTranspose_is_worldRecoordinate
#print axioms world_recoordination_groupoid_crown

end GSTWorldRecoordinationGroupoid
