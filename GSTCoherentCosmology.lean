import waves.GSTWaveCohomology
import waves.CardinalWorldsPostulateLaw
import GSTGraphV2Ontological
import GSTTailFFourthDimension
import GSTClimbInfiniteFamily

/-!
# Coherent GST cosmology: exact wave reconstruction and nonstationary towers

An additive extension of the existing GST laws. All observations are finite;
compatibility relates different resolutions. No terminal-boundary proposition
or unproved universal signature statement is used as a hypothesis.
-/

set_option maxHeartbeats 20000000
set_option maxRecDepth 1000000

namespace GSTCoherentCosmology

open GSTCanonicalSevenAxisBridge GST2DMixedEmergence
open GSTGraphV2Ontological GSTGraphV2OmegaWaveLaw

/-- The mixed wave and the pure ontological current, read together. -/
def dualCurrent (C d : Nat) : Int × Int :=
  (mixedDensity C d, ontDensity C d)

/-- The two existing currents jointly separate every physical cell. -/
theorem dual_current_finite_separation :
    ∀ C₁ : Fin 4, ∀ d₁ : Fin 3, ∀ C₂ : Fin 4, ∀ d₂ : Fin 3,
      dualCurrent C₁.val d₁.val = dualCurrent C₂.val d₂.val →
        C₁ = C₂ ∧ d₁ = d₂ := by decide

theorem dual_current_separation (C₁ d₁ C₂ d₂ : Nat)
    (hC₁ : C₁ < 4) (hd₁ : d₁ < 3) (hC₂ : C₂ < 4) (hd₂ : d₂ < 3)
    (h : dualCurrent C₁ d₁ = dualCurrent C₂ d₂) :
    C₁ = C₂ ∧ d₁ = d₂ := by
  have hs := dual_current_finite_separation
    ⟨C₁, hC₁⟩ ⟨d₁, hd₁⟩ ⟨C₂, hC₂⟩ ⟨d₂, hd₂⟩ h
  exact ⟨congrArg Fin.val hs.1, congrArg Fin.val hs.2⟩

/-- A concrete decoder, not an existential inverse. -/
def decodeCurrent (v : Int × Int) : Nat × Nat :=
  if v = (70, -54) then (0, 0) else
  if v = (112, -21) then (0, 1) else
  if v = (-56, 84) then (0, 2) else
  if v = (0, -21) then (1, 0) else
  if v = (210, 0) then (1, 1) else
  if v = (-112, -33) then (1, 2) else
  if v = (112, 0) then (2, 0) else
  if v = (42, -54) then (2, 1) else
  if v = (-56, 0) then (2, 2) else
  if v = (168, -33) then (3, 0) else
  if v = (0, 0) then (3, 1) else
  if v = (70, 42) then (3, 2) else (0, 0)

theorem decode_current_finite : ∀ C : Fin 4, ∀ d : Fin 3,
    decodeCurrent (dualCurrent C.val d.val) = (C.val, d.val) := by decide

theorem decode_current (C d : Nat) (hC : C < 4) (hd : d < 3) :
    decodeCurrent (dualCurrent C d) = (C, d) :=
  decode_current_finite ⟨C, hC⟩ ⟨d, hd⟩

/-- Mixed amplitude alone cannot even distinguish the two fixed-axis cells. -/
theorem mixed_current_alias : mixedDensity 0 0 = mixedDensity 3 2 := by decide

/-- This is the precise limitation of the previous controlled-tower structure. -/
theorem old_controlled_tower_stationary {α : Type}
    (T : CardinalWorldsPostulateLaw.ControlledTower α) (n : Nat) :
    T.level n = T.level 0 := by
  induction n with
  | zero => rfl
  | succ n ih => exact (T.ledger n).trans ((T.controller n).symm.trans ih)

/-- A world at resolution k is an actual finite residue. Refining resolution
preserves its lower window, while allowing new trits above that window. -/
structure WindowTower where
  level : Nat → Nat
  bounded : ∀ k, level k < 3^k
  coherent : ∀ k s, k ≤ s → level s % 3^k = level k

/-- A finite physical world, embedded into all resolutions. -/
def naturalTower (R : Nat) : WindowTower where
  level k := R % 3^k
  bounded k := Nat.mod_lt _ (Nat.pow_pos (by decide))
  coherent k s h := Nat.mod_mod_of_dvd R (Nat.pow_dvd_pow 3 h)

/-- The existing Omega frozen-window law constructs a tower in the new space. -/
def omegaTower (core : Nat) : WindowTower where
  level k := (omegaCutWord (k-1) 1 * core) % 3^k
  bounded k := Nat.mod_lt _ (Nat.pow_pos (by decide))
  coherent k s h := by
    rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 3 h)]
    exact GSTTailFFourthDimension.omega_tower_word_mod_chain core k (s-1) (by omega)

/-- The new space contains changing levels, witnessed by the repository's tower. -/
theorem omega_tower_nonstationary :
    (omegaTower 1).level 1 = 1 ∧ (omegaTower 1).level 2 = 7 ∧
      (omegaTower 1).level 3 = 16 := by decide

/-- Build a finite window from an arbitrary stream of legal trits. -/
def streamPrefix (a : Nat → Fin 3) : Nat → Nat
  | 0 => 0
  | n+1 => streamPrefix a n + 3^n * (a n).val

theorem stream_prefix_bound (a : Nat → Fin 3) (n : Nat) :
    streamPrefix a n < 3^n := by
  induction n with
  | zero => simp [streamPrefix]
  | succ n ih =>
    have ha := (a n).isLt
    have hp : 0 < (3:Nat)^n := Nat.pow_pos (by decide)
    simp only [streamPrefix, Nat.pow_succ]
    nlinarith

theorem stream_prefix_coherent (a : Nat → Fin 3) (k s : Nat) (h : k ≤ s) :
    streamPrefix a s % 3^k = streamPrefix a k := by
  induction s with
  | zero =>
    have hk : k = 0 := by omega
    subst k
    simp [streamPrefix]
  | succ s ih =>
    by_cases hks : k ≤ s
    · have hz : (3^s * (a s).val) % 3^k = 0 := by
        apply Nat.mod_eq_zero_of_dvd
        exact dvd_mul_of_dvd_left (Nat.pow_dvd_pow 3 hks) _
      rw [streamPrefix, Nat.add_mod, hz, Nat.add_zero, ih hks]
      exact Nat.mod_eq_of_lt (stream_prefix_bound a k)
    · have hk : k = s+1 := by omega
      subst k
      exact Nat.mod_eq_of_lt (stream_prefix_bound a (s+1))

def streamTower (a : Nat → Fin 3) : WindowTower where
  level := streamPrefix a
  bounded := stream_prefix_bound a
  coherent := stream_prefix_coherent a

/-- Distinct infinite innovation streams give distinct level families. -/
theorem stream_tower_injective : Function.Injective (fun a => (streamTower a).level) := by
  intro a b h
  funext n
  apply Fin.ext
  have h0 : streamPrefix a n = streamPrefix b n := congrFun h n
  have h1 : streamPrefix a (n+1) = streamPrefix b (n+1) := congrFun h (n+1)
  simp only [streamPrefix] at h1
  rw [h0] at h1
  have hm := Nat.add_left_cancel h1
  exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide)) hm

/-- Every finite world has all three distinct legal next-resolution branches. -/
theorem three_way_extension (k r : Nat) (hr : r < 3^k) :
    (∀ d : Fin 3, r + 3^k * d.val < 3^(k+1) ∧
      (r + 3^k * d.val) % 3^k = r) ∧
    Function.Injective (fun d : Fin 3 => r + 3^k * d.val) := by
  constructor
  · intro d
    constructor
    · have hd := d.isLt
      have hp : 0 < (3:Nat)^k := Nat.pow_pos (by decide)
      rw [Nat.pow_succ]
      nlinarith
    · simp [Nat.add_mod, Nat.mod_eq_of_lt hr]
  · intro a b h
    apply Fin.ext
    exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide)) (Nat.add_left_cancel h)

/-- Exact finite locality of both coordinates of a GST cell. -/
theorem cell_coordinates_local (R S p : Nat)
    (h : R % 3^(p+1) = S % 3^(p+1)) :
    carry4 R p = carry4 S p ∧ digit3 R p = digit3 S p := by
  have hlow : R % 3^p = S % 3^p := by
    have hdvd : 3^p ∣ 3^(p+1) := Nat.pow_dvd_pow 3 (by omega)
    rw [← Nat.mod_mod_of_dvd R hdvd, h, Nat.mod_mod_of_dvd S hdvd]
  refine ⟨?_, ?_⟩
  · simp only [carry4, hlow]
  · exact GSTFourPowerDirectResidue.digit3_eq_of_mod_next R S p h

/-- The entire infinite horizontal orbit below a fixed height is determined
by one finite tower level. The precision requirement does not grow with t. -/
theorem finite_realization (X : WindowTower) (K t p : Nat) (hp : p+1 ≤ K) :
    carry4 (4^t * X.level (p+1)) p = carry4 (4^t * X.level K) p ∧
    digit3 (4^t * X.level (p+1)) p = digit3 (4^t * X.level K) p := by
  apply cell_coordinates_local
  have hs := X.coherent (p+1) K hp
  have hl := Nat.mod_eq_of_lt (X.bounded (p+1))
  simp only [Nat.mul_mod, hs, hl]

def towerCarry (X : WindowTower) (t p : Nat) : Nat :=
  carry4 (4^t * X.level (p+1)) p

def towerDigit (X : WindowTower) (t p : Nat) : Nat :=
  digit3 (4^t * X.level (p+1)) p

def towerCurrent (X : WindowTower) (t p : Nat) : Int × Int :=
  dualCurrent (towerCarry X t p) (towerDigit X t p)

theorem tower_carry_bound (X : WindowTower) (t p : Nat) : towerCarry X t p < 4 :=
  (GSTWaveCohomology.cellOf (4^t * X.level (p+1)) p).hcarry

theorem tower_digit_bound (X : WindowTower) (t p : Nat) : towerDigit X t p < 3 :=
  (GSTWaveCohomology.cellOf (4^t * X.level (p+1)) p).hdigit

/-- Both graph edge laws survive on the coherent infinite tower. -/
theorem tower_edge_laws (X : WindowTower) (t p : Nat) :
    outDigit (towerCarry X t p) (towerDigit X t p) = towerDigit X (t+1) p ∧
    nextCarry (towerCarry X t p) (towerDigit X t p) = towerCarry X t (p+1) := by
  constructor
  · unfold towerCarry towerDigit
    rw [show (4:Nat)^(t+1) * X.level (p+1) = 4 * (4^t * X.level (p+1)) by
      rw [Nat.pow_succ]; ring]
    exact (digit3_mul_four_exact _ p).symm
  · have h := finite_realization X (p+2) t p (by omega)
    unfold towerCarry towerDigit
    rw [h.1, h.2]
    exact (carry4_forward_exact (4^t * X.level (p+2)) p).symm

/-- New trit = the exact next-resolution innovation; this reconstructs levels. -/
theorem level_reconstruction (X : WindowTower) (p : Nat) :
    X.level (p+1) = X.level p + 3^p * towerDigit X 0 p := by
  have h := GSTClimbInfiniteFamily.mod_slice_up (X.level (p+1)) p
  rw [Nat.mod_eq_of_lt (X.bounded (p+1)), X.coherent p (p+1) (by omega)] at h
  simpa [towerDigit] using h

/-- Every level can be reconstructed from its wave-current trace, without
assuming any whole-number realization of the infinite tower. -/
theorem current_trace_reconstructs (X Y : WindowTower) (K : Nat)
    (h : ∀ p, p < K → towerCurrent X 0 p = towerCurrent Y 0 p) :
    X.level K = Y.level K := by
  induction K with
  | zero =>
    have hx := X.bounded 0
    have hy := Y.bounded 0
    norm_num at hx hy
    omega
  | succ K ih =>
    have hprev := ih (fun p hp => h p (by omega))
    have hd := (dual_current_separation _ _ _ _
      (tower_carry_bound X 0 K) (tower_digit_bound X 0 K)
      (tower_carry_bound Y 0 K) (tower_digit_bound Y 0 K) (h K (by omega))).2
    rw [level_reconstruction X K, level_reconstruction Y K, hprev, hd]

/-- Equality of finite worlds is exactly equality of their complete two-current
observations below that resolution, at every horizontal time. -/
theorem finite_observation_equivalence (X Y : WindowTower) (K : Nat) :
    X.level K = Y.level K ↔
      ∀ t p, p < K → towerCurrent X t p = towerCurrent Y t p := by
  constructor
  · intro h t p hp
    have hx := finite_realization X K t p (by omega)
    have hy := finite_realization Y K t p (by omega)
    unfold towerCurrent towerCarry towerDigit
    rw [hx.1, hx.2, hy.1, hy.2, h]
  · intro h
    exact current_trace_reconstructs X Y K (h 0)

/-- Arbitrary innovation streams remain distinguishable by wave observations. -/
theorem wave_stream_injective :
    Function.Injective (fun a => towerCurrent (streamTower a) 0) := by
  intro a b h
  apply stream_tower_injective
  funext K
  exact current_trace_reconstructs _ _ K (fun p _ => congrFun h p)

/-- Every GST finite rectangle law extends to every coherent tower. -/
theorem tower_rectangle_gauss (X : WindowTower) (N K : Nat) :
    (∑ p ∈ Finset.range K, (3:Int)^p * ∑ t ∈ Finset.range N,
      mixedDensity (towerCarry X t p) (towerDigit X t p)) =
    (∑ p ∈ Finset.range K, (3:Int)^p *
      (infoPotential (towerDigit X N p) - infoPotential (towerDigit X 0 p))) +
    7 * ((∑ t ∈ Finset.range N, carryPotential (towerCarry X t 0)) -
      (3:Int)^K * ∑ t ∈ Finset.range N, carryPotential (towerCarry X t K)) +
    56 * ∑ p ∈ Finset.range K, (3:Int)^p * ∑ t ∈ Finset.range N,
      surviveI (towerCarry X t p) (towerDigit X t p) := by
  apply mixed_rectangle_emergence
  intro t p _ _
  exact ⟨tower_carry_bound X t p, tower_digit_bound X t p,
    (tower_edge_laws X t p).1, (tower_edge_laws X t p).2⟩

/-- The existing no-erasure theorem now holds on every coherent tower,
including those with no finite natural-number representative. -/
theorem tower_no_erasure (X : WindowTower) (N q : Nat) (hN : 1 ≤ N)
    (h : GSTU2DEventTransport.HappyCell (towerCarry X 0 q) (towerDigit X 0 q)) :
    0 < weightedOntPrefix (towerCarry X) (towerDigit X) N (q+1) := by
  apply weightedOntPrefix_positive_of_top_leading_happy
  · exact hN
  · intro t p _ _
    exact tower_carry_bound X t p
  · intro t p _ _
    exact tower_digit_bound X t p
  · exact h

#print axioms dual_current_separation
#print axioms stream_tower_injective
#print axioms finite_observation_equivalence
#print axioms wave_stream_injective
#print axioms tower_rectangle_gauss
#print axioms tower_no_erasure

end GSTCoherentCosmology
