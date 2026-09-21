import GSTCoherentCosmology
import CardinalWorlds
import MonolithBoundary
import GSTGraphV2Ontological
import GSTGraphV2OmegaWaveLaw
import GSTGraphV2SixAdicSynchronizedShadows
import GSTGraphV2ProductionLaws
import GSTWorldtraceArithmetic
import GSTTailFFourthDimension
import GSTTheAct
import GSTBladeWave
import GSTTowerAxis
import GSTTowerFire
import GSTDiagonalRead
import GSTGhostRayExclusion
import GSTClimbInfiniteFamily
import GSTTheActConstruction
import GSTWorldtraceMahlerRelativePrecision
import HodgeDeRhamBridge
import GSTAnalyticAbsorption
import GSTLefschetzCrown
import waves.GSTWaveCohomology
import waves.GSTNCohomology
import waves.GSTVortexSingularity
import waves.CardinalWorldsPostulateLaw

/-!
# HC PROOF — the universe's entry face

One universe, assembled and merged:

* **THE CARDINAL WORLDS** (`CardinalWorlds`) — the deep pre-GST theory:
  the 2-world, the 3-world, the mixed 6-world, the bridge `3 = 1 + 2`,
  the POSTULATES I & II (bridge signature + valuation bound), the
  `c`/`d` dual towers with their exact identities.

* **THE MONOLITH BOUNDARY** (`MonolithBoundary`) — the terminal identity
  interface: the deep theorems proven in the source monolith
  (`kyo-oo/erdosternary2`), stated as named boundary propositions taken
  as explicit hypotheses downstream.  Zero sorries, zero custom axioms.

* **THE GST GRAPH V2 ONTOLOGICAL UNIVERSE** — the ontological current, the
  six-adic geometry and synchronized shadows, the production graph, the
  Ω-wave law, the worldtrace arithmetic, the fourth dimension
  (`GSTTailFFourthDimension`), the act, the towers, the climb.

* **THE ABSORPTION** (`HodgeDeRhamBridge`) — Hodge and de Rham cohomology
  wired into the universe as finite comparison certificates.

This file is the comparator's one-screen receipt of the whole universe.
All declarations below are root-level (the modules carry no namespaces).
-/

/-! ## The Cardinal Worlds face -/

#check d_identity
#check bridge_sig_even
#check bridge_sig_j_mod6_3
#check four_mul_preserves_digit
#check gst_three_world_factor_rawS
#check gst_handwritten_three_world_joined_prefix_closedS
#check modular_check_base

/-! ## The GST V2 ontological universe face -/

#check GSTGraphV2Ontological.happy_iff_ontDensity_positive
#check GSTGraphV2SixAdicSynchronizedShadows.six_iso_iff_synchronized_shadows
#check GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF

/-! ## The absorption face -/

#check HodgeDeRhamBridge.deRham_betti_comparison_finite
#check HodgeDeRhamBridge.finite_hodge_characterization
#check HodgeDeRhamBridge.period_rebase

/-! ## The analytic crown face (Layer 8 — Task 7, machine-checked) -/

#check GSTAnalyticAbsorption.hc_plane_is_manifold
#check GSTAnalyticAbsorption.hc_descent_flow_smooth
#check GSTAnalyticAbsorption.hc_universal_cover
#check GSTAnalyticAbsorption.hc_circle_compact
#check GSTAnalyticAbsorption.hc_period_transport
#check GSTAnalyticAbsorption.hc_haar_is_probability
#check GSTAnalyticAbsorption.hc_fourier_character_norm
#check GSTAnalyticAbsorption.hc_characters_dense
#check GSTAnalyticAbsorption.hc_circle_L2_basis
#check GSTAnalyticAbsorption.hc_transcendentals_residual
#check GSTAnalyticAbsorption.hc_tower_window_transcendental
#check GSTAnalyticAbsorption.hc_twist_kernel_law
#check GSTAnalyticAbsorption.hc_cyclotomic_tate_degree
#check GSTAnalyticAbsorption.hc_finite_twist_embeds
#check GSTAnalyticAbsorption.hc_twist_torsion_law

/-! ## The wave mechanics face (Task 4 — machine-checked) -/

#check GSTWaveCohomology.wave_cell_decomposition
#check GSTWaveCohomology.rectangle_gauss_law
#check GSTWaveCohomology.wave_class_transport
#check GSTWaveCohomology.total_matter
#check GSTNCohomology.interference_decomposition
#check GSTNCohomology.channel_embedding
#check GSTNCohomology.two_wave_frame_refines
#check GSTVortexSingularity.core_rotation_period_five
#check GSTVortexSingularity.lattice_curvature_zero
#check GSTVortexSingularity.vortex_singularity_forms
#check GSTVortexSingularity.gvsm_full_signature
#check GSTVortexSingularity.vortex_energy_finite
#check CardinalWorldsPostulateLaw.emergent_dimension_full
#check CardinalWorldsPostulateLaw.infinite_dimension_is_colimit
#check CardinalWorldsPostulateLaw.postulate_three_law

/-! ## The Lefschetz crown face (Layer 9) -/

#check GSTLefschetzCrown.cup_comm
#check GSTLefschetzCrown.cupDigit_cubed
#check GSTLefschetzCrown.cupCarry_fourth
#check GSTLefschetzCrown.monomial_is_cellClass
#check GSTLefschetzCrown.divisor_generation
#check GSTLefschetzCrown.lefschetz_iterate_zero
#check GSTLefschetzCrown.lefschetz_sixth_power
#check GSTLefschetzCrown.sector_rank_table
#check GSTLefschetzCrown.lefschetz_injective_below_middle
#check GSTLefschetzCrown.lefschetz_surjective_3
#check GSTLefschetzCrown.lefschetz_surjective_4
#check GSTLefschetzCrown.lefschetz_surjective_5
#check GSTLefschetzCrown.pairing_nondegenerate_left
#check GSTLefschetzCrown.pairing_nondegenerate_right
#check GSTLefschetzCrown.poincare_monomial_kronecker
#check GSTLefschetzCrown.proj_sum
#check GSTLefschetzCrown.lefschetz_respects_kunneth
#check GSTLefschetzCrown.kunneth_projector_polynomial
#check GSTLefschetzCrown.hodge_locus_mod_invariant
#check GSTLefschetzCrown.hodge_locus_residue_algebraic
#check GSTLefschetzCrown.the_lefschetz_crown

/-! ## The boundary face -/

#check erdos_even_conjecture_iff_tailF
#check erdos_ternary_2_universal_of_tailF
#check erdos_ternary_2_conjecture_odd
#check infinite_controller_ternary_two_chokehold
