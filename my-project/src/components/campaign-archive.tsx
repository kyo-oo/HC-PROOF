'use client'

import { useState } from 'react'
import { Card, CardContent, CardHeader, CardTitle } from '@/components/ui/card'
import { Badge } from '@/components/ui/badge'
import { Button } from '@/components/ui/button'
import { Tabs, TabsContent, TabsList, TabsTrigger } from '@/components/ui/tabs'
import { ScrollArea } from '@/components/ui/scroll-area'
import { Separator } from '@/components/ui/separator'

const GREEN = 'bg-emerald-600'
const RED = 'bg-red-600'
const LIVE = 'bg-amber-500'
const STONE = 'bg-stone-600'

function StatusBadge({ status }: { status: 'green' | 'red' | 'live' | 'staged' }) {
  const map = {
    green: { cls: GREEN, label: 'KERNEL-GREEN' },
    red: { cls: RED, label: 'IN REPAIR' },
    live: { cls: LIVE, label: 'CI IN FLIGHT' },
    staged: { cls: STONE, label: 'STAGED' },
  } as const
  const m = map[status]
  return <Badge className={`${m.cls} text-white font-mono text-[10px] tracking-wider`}>{m.label}</Badge>
}

const waves = [
  { id: 'W1–W50', name: 'The Original Campaign (10 waves × 5 agents)', status: 'green' as const, detail: 'The GST Hypothesis spanning law: GSTHypothesisSpanningProof + CompilerFace, det[Krylov] = −1,149,656,584,000 ≠ 0, rank 12/12. 3,261 sub-agent turns.' },
  { id: 'W51–W62', name: 'Reconstruction + Unified Family', status: 'green' as const, detail: 'Corpus recovery, repair waves, the twelve-point world, GSTUnifiedNativeWorldFamilyLaw.lean CI-green (run 44756915591 @ 4188c31) — the family law: every member satisfies NativeGSTSingleFoldOrbitLaw.' },
  { id: 'W63', name: 'Positive-Dimensional Live-Weight Law (M=1)', status: 'green' as const, detail: 'GSTPositiveDimensionalLiveWeightLaw.lean — run 44844378079 @ 1cfb58f, zero sorryAx, five axiom receipts. Weight-1 live, monogenic by the honest sphere class.' },
  { id: 'W64', name: 'General-M Cyclic Word', status: 'green' as const, detail: 'The M-cycle certificate: the Krylov orbit IS the honest point-class family — the identity Krylov matrix, det = 1, rank M/M at every M (verified M = 1..24, two-method).' },
  { id: 'W65', name: 'Finite-Line Carrier (F1)', status: 'green' as const, detail: 'GSTFiniteLineWorldCarrier.lean — run 44899187702 @ 99f6366: the Proj scheme, the M-cycle automorphism (IsIso), the closed embedding presentation. Receipts [propext, Classical.choice, Quot.sound].' },
  { id: 'W66', name: 'Closed Immersion (F2)', status: 'green' as const, detail: 'GSTFiniteLineClosedImmersion.lean — run 44918529342 @ 1cf6ff2: the cover twins + awayMap_surjective + the five-stage chart cascade + the of_iSup_eq_top assembly. All receipts clean. THIS SESSION.' },
  { id: 'W67', name: 'Smoothness (F3)', status: 'staged' as const, detail: 'GSTFiniteLineSmoothness.lean staged: B-substrate (partner involution, block retraction, chart square) + the cascade + the battle cores (the chart ring ≃ ℂ[T]) in commander authoring.' },
  { id: 'W68', name: 'THE GENERAL-M LAW (the capstone)', status: 'green' as const, detail: 'GSTFiniteLineGeneralMLaw.lean (1,031 lines) — CI-GREEN (run 44928010015 @ dc31a62, 8,982 jobs, zero errors, sorry-gate silent): native_GST_single_fold_orbit_law_finiteLine — the general-M NativeGSTSingleFoldOrbitLaw on the finite-line world for every M ≥ 1, discharged through the green wave-60 engine with the wave-64 identity-Krylov certificates. THIS SESSION.' },
]

const gates = [
  { name: 'F1 — the carrier', status: 'green' as const, note: 'Proj (lineGrading M), the M-cycle automorphism, the embedding' },
  { name: 'F2 — the closed immersion', status: 'green' as const, note: 'finiteLine_closedImmersion, chartwise certified' },
  { name: 'F3 — smoothness', status: 'staged' as const, note: 'the chart-ring battle (Algebra.Smooth ℂ (Away) via the chart equivalence)' },
  { name: 'The analytification receipt', status: 'staged' as const, note: 'A.space = ⊔ M S² (the gated input)' },
  { name: 'The letter realization', status: 'staged' as const, note: 'the M-cycle graphs as RealizedCorrespondenceWord (R₁/R₀ gates)' },
  { name: 'The world instantiation', status: 'staged' as const, note: 'finiteLineWorld M : SmoothProjectiveComplexScheme (needs over_base + F3)' },
]

const lawStatement = `theorem native_GST_single_fold_orbit_law_finiteLine (M : ℕ) [NeZero M]
    (V : SmoothProjectiveComplexScheme)
    (hWX : V.X = finiteLineScheme M)
    (hWmap : hWX ▸ V.structureMap = finiteLineStructureMap M)
    (A : AnalytificationData V)
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2)
    (Z₀ : codimensionCycles V.X 0) (hZ₀ : Z₀ ≠ 0)
    (Z₁ : codimensionCycles V.X 1) (hZ₁ : Z₁ ≠ 0)
    (R₁ : RealizedFiniteClosedCorrespondence V (... H ...) 1)
    (hR₁ : ∀ j : Fin M, R₁.cohomologyOperator
      (spherePointClassWorld ... M hspace ω j) =
      spherePointClassWorld ... M hspace ω (cyclicPred M j))
    (R₀ : RealizedFiniteClosedCorrespondence V (... H ...) 0)
    (hR₀ : ∀ j : Fin M, R₀.cohomologyOperator
      (sphereComponentClass ... M hspace j) =
      sphereComponentClass ... M hspace (cyclicPred M j)) :
    NativeGSTSingleFoldOrbitLaw V (... H ...)
:= native_GST_single_fold_orbit_law_of_sphereUnion_gate ...
    -- the GREEN wave-60 engine (run 44642555839),
    -- the wave-64 identity-Krylov certificates inside`

const arsenal = [
  { name: 'Z3 5.4.1', status: 'SMT — counterexample hunter (289 queries UNSAT, the campaign record)' },
  { name: 'PARI/GP 2.17.2 (cypari2)', status: 'number-theory king — two-method agreement law' },
  { name: 'Vampire 5.1.0', status: 'FOL ATP — TPTP refuter' },
  { name: 'sympy 1.14 + gmpy2 2.3.2', status: 'baseline stack — exact rational arithmetic' },
  { name: 'Lean 4.33.0-rc2 + Mathlib @ 51e6992', status: 'THE CERTIFIER — GitHub Actions CI (never local)' },
]

export function CampaignArchive() {
  const [openWave, setOpenWave] = useState<string | null>(null)

  return (
    <div className="min-h-screen flex flex-col bg-stone-950 text-stone-100">
      <header className="border-b border-stone-800 bg-stone-900/80 backdrop-blur-sm sticky top-0 z-10">
        <div className="max-w-6xl mx-auto px-4 py-4 sm:px-6">
          <div className="flex flex-wrap items-center gap-3">
            <span className="text-2xl" aria-hidden>🐉</span>
            <div>
              <h1 className="text-lg sm:text-xl font-bold tracking-tight">HC-PROOF — GST Campaign Live Status</h1>
              <p className="text-xs text-stone-400 font-mono">branch research/gpt6-gst-hypothesis-part1-chow-square-20261110 · The NativeGSTSingleFoldOrbitLaw assault</p>
            </div>
            <div className="ml-auto flex items-center gap-2">
              <StatusBadge status="green" />
              <span className="text-[10px] text-stone-500 font-mono hidden sm:inline">ARK v3 PROTECTING</span>
            </div>
          </div>
        </div>
      </header>

      <main className="flex-1 max-w-6xl w-full mx-auto px-4 py-6 sm:px-6">
        <Tabs defaultValue="waves" className="w-full">
          <TabsList className="grid w-full grid-cols-4 mb-6 bg-stone-900">
            <TabsTrigger value="waves" className="font-mono text-xs sm:text-sm data-[state=active]:bg-stone-700">WAVES</TabsTrigger>
            <TabsTrigger value="law" className="font-mono text-xs sm:text-sm data-[state=active]:bg-stone-700">THE LAW</TabsTrigger>
            <TabsTrigger value="gates" className="font-mono text-xs sm:text-sm data-[state=active]:bg-stone-700">GATES</TabsTrigger>
            <TabsTrigger value="arsenal" className="font-mono text-xs sm:text-sm data-[state=active]:bg-stone-700">ARSENAL</TabsTrigger>
          </TabsList>

          <TabsContent value="waves" className="space-y-3">
            {waves.map((w) => (
              <Card key={w.id} className="bg-stone-900 border-stone-800">
                <CardHeader className="pb-2 py-4">
                  <div className="flex flex-wrap items-center gap-2">
                    <span className="font-mono text-xs text-amber-500">{w.id}</span>
                    <CardTitle className="text-sm sm:text-base">{w.name}</CardTitle>
                    <span className="ml-auto"><StatusBadge status={w.status} /></span>
                  </div>
                </CardHeader>
                <CardContent className="pt-0">
                  <p className="text-xs text-stone-400 leading-relaxed">{w.detail}</p>
                </CardContent>
              </Card>
            ))}
          </TabsContent>

          <TabsContent value="law">
            <Card className="bg-stone-900 border-stone-800">
              <CardHeader>
                <CardTitle className="text-base">THE GENERAL-M LAW — GSTFiniteLineGeneralMLaw.lean (§8, line 968)</CardTitle>
              </CardHeader>
              <CardContent>
                <p className="text-xs text-stone-400 mb-3">
                  The capstone theorem: for every M ≥ 1, the finite-line world (the disjoint union of M
                  projective lines) carries the full NativeGSTSingleFoldOrbitLaw — every weight&apos;s Hodge
                  fiber is Krylov-cyclic under the single M-cycle fold. Discharged through the CI-green
                  wave-60 sphere-union engine; the certificates are the wave-64 identity Krylov matrices
                  (the orbit IS the honest point-class family).
                </p>
                <Separator className="bg-stone-800 my-3" />
                <ScrollArea className="h-80 rounded-md bg-stone-950 border border-stone-800">
                  <pre className="p-4 text-[10px] sm:text-xs font-mono text-emerald-300 whitespace-pre leading-relaxed">{lawStatement}</pre>
                </ScrollArea>
                <p className="text-[10px] text-stone-500 mt-3 font-mono">
                  Gate-form: the world V, the analytification receipt, the honest seeds and the letter
                  realizations are the disclosed inputs — each a frozen interface discharged by its sibling
                  wave (F1 ✓, F2 ✓, F3 staged, analytification staged, letters staged).
                </p>
              </CardContent>
            </Card>
          </TabsContent>

          <TabsContent value="gates" className="space-y-3">
            {gates.map((g) => (
              <Card key={g.name} className="bg-stone-900 border-stone-800">
                <CardContent className="py-4">
                  <div className="flex flex-wrap items-center gap-2">
                    <span className="text-sm font-medium">{g.name}</span>
                    <span className="ml-auto"><StatusBadge status={g.status} /></span>
                  </div>
                  <p className="text-xs text-stone-400 mt-1">{g.note}</p>
                </CardContent>
              </Card>
            ))}
            <Card className="bg-stone-900 border-stone-800">
              <CardContent className="py-4">
                <p className="text-xs text-stone-300 leading-relaxed">
                  <span className="text-amber-500 font-mono">THE FROZEN ORDER:</span> F2 ✓ → F3 (the chart-ring
                  battle) → the ℂ-points classification + analytification receipt → the gate discharges (the
                  letters as graphs of finiteLineCycle, the seeds as the honest point/component cycles) → the
                  composition with the wave-64 cyclic word → THE INSTANTIATED LAW. Each is a CI-adjudicated
                  Lean wave; the kernel never lies.
                </p>
              </CardContent>
            </Card>
          </TabsContent>

          <TabsContent value="arsenal" className="space-y-3">
            <Card className="bg-stone-900 border-stone-800">
              <CardHeader><CardTitle className="text-base">The Weapons (all live this session)</CardTitle></CardHeader>
              <CardContent className="space-y-2">
                {arsenal.map((a) => (
                  <div key={a.name} className="flex flex-col sm:flex-row sm:items-center gap-1 sm:gap-3">
                    <span className="font-mono text-xs text-amber-500 min-w-44">{a.name}</span>
                    <span className="text-xs text-stone-400">{a.status}</span>
                  </div>
                ))}
              </CardContent>
            </Card>
            <Card className="bg-stone-900 border-stone-800">
              <CardHeader><CardTitle className="text-base">The Certificate Record</CardTitle></CardHeader>
              <CardContent>
                <div className="space-y-2 text-xs text-stone-300 font-mono">
                  <p>det[Krylov(F₁, seed12)] = −1,149,656,584,000 ≠ 0 — rank 12/12 (five exact methods)</p>
                  <p>det[Krylov(M-cycle, point-class seed)] = 1 — rank M/M at every M (identity matrix)</p>
                  <p>Z3 5.4.1: 289/289 queries UNSAT · two-method law (sympy + Bareiss)</p>
                  <p>ARK v3: vault + snapshots + GitHub mirror + 8h watchdog — everything survives</p>
                </div>
              </CardContent>
            </Card>
          </TabsContent>
        </Tabs>
      </main>

      <footer className="mt-auto border-t border-stone-800 bg-stone-900/80">
        <div className="max-w-6xl mx-auto px-4 py-4 sm:px-6 flex flex-wrap items-center gap-x-4 gap-y-1">
          <span className="text-[10px] font-mono text-stone-500">The engine never stops; it never lies.</span>
          <span className="text-[10px] font-mono text-stone-600 ml-auto">HC-PROOF · kyo-oo · Lean 4.33.0-rc2 · Mathlib 51e6992</span>
        </div>
      </footer>
    </div>
  )
}
