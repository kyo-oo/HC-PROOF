# Retained-path historical declaration migration

Target branch: `clean/upgraded-advanced-only-20261009`.

This manifest covers the highest-priority cases where the canonical branch
already has a file at the historical path, but an older independent lineage
contains declaration names absent from the canonical file.  Replacing the
canonical file with the old version would regress current work; the declarations
must instead be ported as strengthened theorems or thin compatibility
corollaries after semantic comparison.

The inventory is static Git analysis.  It does not run Lean locally.  Every
ported declaration must be validated by GitHub-hosted Lean.

## GST cosmology strengthening

### `GSTGeometricRealizationStage2G.lean` — 18 names

Source: `origin/gst-cosmology-strengthening`.

`bigraded_betti_hodge_of_cosmology_family`,
`bigraded_betti_hodge_of_cosmology_obligation`,
`cosmology_chart_realization_iff`, `cosmology_coordinate_reconstruct`,
`cosmology_cycle_fiber_exact`, `cosmologyCoordinateBasis`,
`cosmologyCycleLift`, `cosmologyCycleLift_section`, `cosmologyCycleWitness`,
`cosmologyCycleWitness_spec`, `CosmologyHodgeRealization`,
`CosmologyPureCoordinates`, `CosmologyStage2GRealizationObligation`,
`hodge_class_has_cosmology_cycle`, `hodge_sector_of_transport_duality`,
`transportDualityCycleWitness`, `transportDualityCycleWitness_spec`,
`zero_cycleClass_hodge_iff`.

### `GSTTruncatedWorldCohomologyRing.lean` — 9 names

`H_pow_eq_zero_of_depth_le`, `L_binomial`, `L_pow_boundary`,
`L_pow_eq_zero_of_boundary_le`, `mem_worldOperatorHom_ker_iff_annihilates`,
`V_pow_eq_zero_of_depth_le`, `worldAct_eq_iff_operator_eq`, `worldAct_neg`,
`worldAct_pow_add`.

### `CardinalWorldsV2.lean` — 7 names

`joined_prefix_add`, `packet_add_comm`, `packet_composition_crown`,
`packetMul_comm`, `packetMul_one_left`, `packetMul_one_right`, `packetOne`.

### `waves/GSTWaveCohomology.lean` — 6 names

`finite_weighted_wave_decomposition`, `rowClass_add_exact`,
`rowClass_all_zero_iff_exact`, `rowClass_cut_exact`,
`rowClass_prefix_complete`, `rowClassAt_recovered_exact`.

### `waves/GSTNCohomologyV2.lean` — 6 names

`canonicalNCohoBasis_injective`, `weighted_interference_energy`,
`weighted_interference_ext`, `weighted_interference_separates`,
`weighted_interference_single_probe`, `weightedInterference_delta`.

### `waves/GSTNCohomology.lean` — 6 names

`waveII_channel_reconstruction`, `waveII_prefix_add`,
`waveII_prefix_all_zero_iff`, `waveII_prefix_complete_observable`,
`waveIIAmplitude_prefix_recovered`, `waveIIAmplitude_telescope`.

### `GSTGlobalPureHodgeCosmology.lean` — 6 names

`pure_hodge_basis_expansion`, `pure_hodge_eq_iff_coordinates`,
`pure_hodge_eq_zero_iff_coordinates_zero`, `pure_residual_decomposition`,
`pureCoordinates_residual`, `pureProjection`.

## General-space cosmology

Source: `origin/sol/hodge-general-space-cosmology-20261003`.

### `GSTClassicalHodgeGeneralSpaceRealization.lean` — 8 names

`bettiProgramTransport`, `geometricBettiCycleRealization`,
`gradedProgramSpace`, `nativeCycleRealization`, `nativeCycleSpace`,
`nativeProgramTransport`, `supplied_geometric_face_agree`,
`suppliedBettiCycleRealization`.

### `GSTGeneralSpace.lean` — 8 names

`carrier_is_unconstrained`, `CausalGeometry`, `discrete_lawful`, `Faithful`,
`LawfulPaths`, `ofPreorder`, `ofPreorder_lawful`, `SpectralGeometry`.

### `GSTGraphV2GeneralSpaceRealization.lean` — 8 names

`graphPositionSpace`, `nextPath`, `overlayChart`,
`sevenAxes_next_is_forwardEdge`, `uCut_chart_recoordination`,
`uCut_intrinsic_observable`, `uCut_intrinsic_predicate`, `vertexChart`.

### `GSTClassicalHodgeGeneralSpaceSynchronization.lean` — 6 names

`cycleClassTransportMorphism`, `native_betti_faces_synchronize`,
`programDefect`, `programDefect_source_zero`, `programDefect_transport`,
`programDefect_zero_propagates`.

## Early pure-math engine

### `GSTClassicalHodgeRangeLiftedSpectralOperator.lean` — 7 names

Source: `origin/sol/hodge-pure-math-engine`.

`ClassicalHodgeSpectralOperator.cycleClassRange_stable`,
`ClassicalHodgeSpectralOperator.toSpectralCycleOperatorViaRange`,
`ClassicalHodgeSpectralOperator.toSpectralCycleOperatorViaRange_basisIndex`,
`CycleClassOperatorPair.ofRangeStable`,
`LocalCyclicRealization.exists_native_cycle_constructive`,
`LocalCyclicRealization.exists_point_presentation_constructive`,
`LocalCyclicRealization.toLocalCycleSpectralRealization`.

## Remaining retained-path work

These first 12 paths account for 95 of the 309 missing declaration names in
retained paths.  The other 128 paths must be routed using the same rule:
compare statements under their full namespaces, choose the strongest
canonical theorem, move any genuinely independent result into that module,
and retain historical names only according to the selected compatibility
policy.  Never replace a currently GitHub-green canonical file wholesale with
an older branch version.
