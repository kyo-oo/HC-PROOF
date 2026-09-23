import GSTGraphV2TransparentWidthThree

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTGraphV2CanonicalTransparentBridgeProbe

open GSTCanonicalSevenAxisBridge
open GSTGraphV2PerfectPowerBlock
open GSTGraphV2TransparentWidthThree
open GSTU2DEventTransport

/-- Every positive canonical width is an exact integer number of transparent
width-three blocks. -/
theorem canonicalWidth_eq_three_mul
    (s : Nat) (hs : 1 ≤ s) :
    ∃ r : Nat, canonicalWidth s = 3 * 3^r := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hs
  refine ⟨r, ?_⟩
  simp [canonicalWidth, pow_add]

#check canonicalWidth_eq_three_mul
#print axioms canonicalWidth_eq_three_mul

/-- Every transparent width is identified by its exact number of blocks;
the converse excludes scale zero without a separate scale hypothesis. -/
theorem canonicalWidth_three_dvd_iff (s : Nat) :
    3 ∣ canonicalWidth s ↔ 1 ≤ s := by
  cases s with
  | zero => norm_num [canonicalWidth]
  | succ s =>
      constructor
      · intro _; omega
      · intro _
        refine ⟨3^s, ?_⟩
        simp [canonicalWidth, pow_succ, Nat.mul_comm]


end GSTGraphV2CanonicalTransparentBridgeProbe
