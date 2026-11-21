# The pinned Mathlib source cache (the F2 recon artifacts)

Fetched verbatim from leanprover-community/mathlib4 at the campaign pin
`51e6992efd06126df61a496bebf8f49482a4e129` (v4.33.0-rc2, the CI-verified
revision of every lane) for local API verification of the finite-line
carrier's next waves. Apache 2.0, (c) the Mathlib community — attribution
preserved here; these are reference copies, not corpus sources.

* `Functor.lean` — `Proj.map` (l.148), `map_preimage_basicOpen` (l.160),
  `awayι_comp_map` (l.192 — THE per-chart square), `mapAffineOpenCover` (l.203),
  `map_comp` (l.210), `map_id` (l.217).
* `Basic.lean` — `awayToSection` (l.134), `basicOpenToSpec` (l.140),
  `basicOpenIsoSpec` (l.161), `basicOpenIsoAway` (l.176), `awayι` (l.186),
  `IsOpenImmersion (awayι ..)` (l.193), `opensRange_awayι` (l.196).
* `Scheme.lean` — `HomogeneousLocalization.Away` usage (l.151).
* `HomogeneousLocalization.lean` — `Away` (l.601), `Away.mk` (l.609),
  `Away.mk_surjective` (l.618), `Away.map` (l.727), `Away.map_mk` (l.732,
  simp), `Away.map_comp` (l.738). NO Away-surjectivity lemma exists at the
  pin — the F2 sub-battle proves it (see the F2 recon record).
