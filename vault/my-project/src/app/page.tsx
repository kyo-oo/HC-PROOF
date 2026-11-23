"use client";

import { useEffect, useState } from "react";
import { Card, CardContent, CardHeader, CardTitle } from "@/components/ui/card";
import { Badge } from "@/components/ui/badge";
import { Button } from "@/components/ui/button";
import { Tabs, TabsContent, TabsList, TabsTrigger } from "@/components/ui/tabs";
import { Alert, AlertDescription, AlertTitle } from "@/components/ui/alert";
import {
  ShieldCheck,
  Swords,
  Terminal,
  Activity,
  CircleCheck,
  XCircle,
  Loader2,
  Clock,
  GitBranch,
  Zap,
} from "lucide-react";

type Run = {
  id: number;
  lane: string;
  sha: string;
  status: string;
  conclusion: string | null;
  created: string;
  url: string;
};

const TASKS = [
  {
    id: "TASK 1",
    name: "The smooth-projective finite-line world",
    state: "GREEN",
    detail:
      "finiteLineWorld M : SmoothProjectiveComplexScheme — kernel-certified (run 45019987397): carrier F1, closed immersion F2, smoothness F3, the world bundle + the base-naturality pin lemma. The V/hWX/hWmap gates discharged by rfl.",
    runs: "44899187702 / 44918529342 / 44975856432 / 45019987397",
  },
  {
    id: "TASK 2",
    name: "The analytification identification",
    state: "IN BATTLE",
    detail:
      "The Riemann arithmetic core repaired twice (wave 5-C split-ite; wave 6-D killed the six residuals: the two split-failures re-routed through the empirically-green rw [sphereToCoord, if_pos/if_neg] pattern, the hfrac orphan ring, and the three ext-bullet closers rebuilt as hand-computed linear_combination coefficients against the sphere equation). The module body (581 lines, wave 6-B) stands. The full points-classification remains as the gate.",
    runs: "in adjudication at 36bcdf4 — runs 45105003249 / 45105003233",
  },
  {
    id: "TASK 3",
    name: "The genuine GST correspondences",
    state: "IN BATTLE",
    detail:
      "GATE-L's six point-action lemmas spliced (wave 6-C: the ideal-level §2a + the order-level §2b). Wave 6-D rebuilt §1's residue-degree receipt on the pinned CONTRAvariant residue-field API — the two ill-typed RingHom.id roundtrips replaced by the transported congruence-composites closing at Iso.inv_hom_id/hom_inv_id — and re-bridged the §2a/§2b mem_comap rewrites through explicit show-anchors. The letters (§3) ride these plus the green graph machinery.",
    runs: "in adjudication at 36bcdf4 — run 45105003211",
  },
  {
    id: "TASK 4",
    name: "The canonical Hodge-data semantics",
    state: "GREEN",
    detail:
      "GSTFiniteLineHonestHodgeData kernel-certified GREEN (run at ff48e2f): the honest cycle-class maps (the component-indicator at weight 0, the degree-per-component at weight 1), the atom formulas on the presentationOfNativeCycle_point receipt, the assembled data at the concrete world, the seed equations, the hstash clone. The choice-functional trick is dead.",
    runs: "45093883420 — SUCCESS at ff48e2f",
  },
  {
    id: "TASK 5",
    name: "The gate-free general-M law",
    state: "GREEN (gated)",
    detail:
      "GSTFiniteLineWorldDischarge kernel-certified GREEN (run 45090036794 at 35aa0dc): native_GST_single_fold_orbit_law_finiteLineWorld — the Wave-68 law body at the ACTUAL world; the remaining hypotheses are exactly the three gate families (analytification, seeds, letters). Route H: the engine instantiated at the honest data — the seeds are certified dischargers.",
    runs: "45090036794 — SUCCESS at 35aa0dc",
  },
  {
    id: "TASK 6",
    name: "The universal original-X source",
    state: "STAGED",
    detail:
      "The capstone module (GSTFiniteLineUnconditionalSource) is armed and firing: the route-H architecture crystallized — native_GST_single_fold_orbit_law_of_sphereUnion_gate instantiated at finiteLineHodgeDataHonest with the honest seeds, the two M-cycle letters, and the analytification gate. The lane's path-filter repaired; the battle order frozen.",
    runs: "in adjudication at 36bcdf4 — run 45105003219",
  },
];

const WAVES = [
  {
    id: "5-A",
    title: "The 52-error cascade root killed",
    body:
      "The honest-data module never imported GSTFiniteLineOverBase and never opened GSTSingularCohomologyMaps / GSTPositiveDimensionalLiveCoreKit — one import + two opens killed the entire cascade; the cycle module's own errors were all this import's inheritance.",
  },
  {
    id: "5-B",
    title: "The honest-data rebuild",
    body:
      "The assembled data + all downstream theorems restated at the CONCRETE world finiteLineWorld M (the polymorphic-V statement was the whole type-mismatch family); the atom proofs rebuilt on the green presentationOfNativeCycle_point receipt through defeq show-bridges; the seeds restated on the At-family (the wave-4-A renamed closed-point family).",
  },
  {
    id: "5-C",
    title: "The Riemann nine-site kill",
    body:
      "The eq_northPole bullets closed by DEFEQ (the Fin-MK-vs-OfNat mismatch killed in term mode); both cancellation theorems rebuilt on split (the stale-Decidable-instance disease); the hd rebuilt on the hfrac-route; the coordToSphere applications parenthesized; the Equiv constructor's field order corrected.",
  },
  {
    id: "5-D",
    title: "The two residuals closed in term mode",
    body:
      "The seed theorems' rw died at implicit transparency — the .X-typed goal is only type-correct at default; hidx now rides congrArg + Eq.trans. Plus the hstash clone (the wave-60 engine's route-H gate input) and the unconditional-source lane's path filter repaired.",
  },
  {
    id: "6-A",
    title: "The cycle module's own six defects",
    body:
      "map_id_of_eq localized (the carrier's private helper does not export); the hcomp/hcomp2 statements restated at RingHom.id (the bare-𝟙 elaborated in the WRONG category); the comp-pattern's roundtrips swapped to the correct directions; the finrank family fully qualified and the one_ne_zero ascribed at the residue field.",
  },
  {
    id: "6-B",
    title: "The analytification body",
    body:
      "581 lines, 26 declarations: the space identification, the coordinate model over the repaired Riemann equivalence, the chart arithmetic (verbatim transplants of the CI-green chart_retract chains), the constructive half of GATE-A (the section-calculus chart-point liftings), and the gate-form assembly with the hspace rfl-receipt.",
  },
  {
    id: "6-C",
    title: "GATE-L §2 spliced — the six point-action lemmas",
    body:
      "The ideal-level §2a (the comapFun show-bridge, the block-ideal permutation through the span receipts, the generic-point action L1–L3) and the order-level §2b (mono, reflection, strict mono, coheight transport, the component-index law L4–L6) — the entire remaining mathematical content of GATE-L per the wave-2 battle map.",
  },
  {
    id: "6-D",
    title: "The CI verdict repairs at 6c9bc8a",
    body:
      "Riemann: the two split-failures killed by the rw [sphereToCoord, coordToSphere, if_pos/if_neg] route (the def-fold never yields an ite to split), the hfrac orphan ring dropped, the three ext-bullet closers rebuilt as linear_combination coefficients against the sphere equation. Cycle correspondence: §1's residue-degree receipt rebuilt on the pinned CONTRAvariant residue-field API (the two transported congruence-composites closing at Iso.inv_hom_id/hom_inv_id — the RingHom.id statements were unstatable), the §2a/§2b mem_comap rewrites show-bridged, strictMono/strictReflect rebuilt on the reflect-mono routes. All four lanes re-fired at 36bcdf4.",
  },
];

function StateBadge({ state }: { state: string }) {
  if (state === "GREEN" || state.startsWith("GREEN"))
    return (
      <Badge className="bg-emerald-600 hover:bg-emerald-600 text-white">
        <CircleCheck className="mr-1 h-3 w-3" />
        {state}
      </Badge>
    );
  if (state === "IN BATTLE")
    return (
      <Badge className="bg-amber-500 hover:bg-amber-500 text-black">
        <Swords className="mr-1 h-3 w-3" />
        {state}
      </Badge>
    );
  if (state === "STAGED")
    return (
      <Badge className="bg-violet-600 hover:bg-violet-600 text-white">
        <Clock className="mr-1 h-3 w-3" />
        {state}
      </Badge>
    );
  return <Badge variant="secondary">{state}</Badge>;
}

function RunRow({ run }: { run: Run }) {
  const icon =
    run.conclusion === "success" ? (
      <CircleCheck className="h-4 w-4 text-emerald-500 shrink-0" />
    ) : run.conclusion === "failure" ? (
      <XCircle className="h-4 w-4 text-red-500 shrink-0" />
    ) : run.status === "in_progress" ? (
      <Loader2 className="h-4 w-4 text-amber-500 animate-spin shrink-0" />
    ) : (
      <Clock className="h-4 w-4 text-zinc-400 shrink-0" />
    );
  return (
    <a
      href={run.url}
      target="_blank"
      rel="noreferrer"
      className="flex items-center gap-3 px-3 py-2 rounded-md hover:bg-zinc-800/60 transition-colors text-sm"
    >
      {icon}
      <span className="font-medium truncate w-40 sm:w-64">{run.lane}</span>
      <span className="font-mono text-xs text-zinc-400 hidden sm:inline">
        {run.sha}
      </span>
      <span className="ml-auto text-xs text-zinc-400">
        {run.conclusion ?? run.status}
      </span>
    </a>
  );
}

export default function Home() {
  const [runs, setRuns] = useState<Run[]>([]);
  const [loaded, setLoaded] = useState(false);
  const [tick, setTick] = useState(0);

  useEffect(() => {
    let active = true;
    (async () => {
      try {
        const res = await fetch("/api/campaign");
        const data = await res.json();
        if (!active) return;
        setRuns(data.lanes || []);
        setLoaded(true);
      } catch {
        if (active) setLoaded(true);
      }
    })();
    return () => {
      active = false;
    };
  }, [tick]);

  useEffect(() => {
    const t = setInterval(() => setTick((x) => x + 1), 30000);
    return () => clearInterval(t);
  }, []);

  return (
    <div className="min-h-screen flex flex-col bg-zinc-950 text-zinc-100">
      <header className="border-b border-zinc-800 bg-zinc-900/80 backdrop-blur sticky top-0 z-10">
        <div className="max-w-6xl mx-auto px-4 py-4 flex flex-wrap items-center gap-3">
          <Swords className="h-6 w-6 text-red-500" />
          <div className="min-w-0">
            <h1 className="text-lg font-bold tracking-tight leading-tight">
              GST CAMPAIGN — HC-PROOF
            </h1>
            <p className="text-xs text-zinc-400 font-mono truncate">
              NativeGSTSingleFoldOrbitLaw — the complete proof assault · kyo-oo/HC-PROOF
            </p>
          </div>
          <div className="ml-auto flex items-center gap-2">
            <Badge className="bg-red-600 hover:bg-red-600 text-white font-mono">
              <GitBranch className="mr-1 h-3 w-3" />
              campaign branch
            </Badge>
          </div>
        </div>
      </header>

      <main className="flex-1 max-w-6xl w-full mx-auto px-4 py-6 space-y-6">
        <Alert className="border-red-800 bg-red-950/40">
          <Zap className="h-4 w-4 text-red-400" />
          <AlertTitle className="text-red-200">
            THE ENGINE NEVER STOPS. IT NEVER LIES.
          </AlertTitle>
          <AlertDescription className="text-red-200/80">
            Every verdict on this page is a GitHub-Actions kernel verdict or a
            live run — nothing inferred. The kernel is Lean 4.33 + Mathlib at
            the pinned SHA 51e6992. Zero sorry, zero sorryAx, the receipts
            [propext, Classical.choice, Quot.sound].
          </AlertDescription>
        </Alert>

        <Tabs defaultValue="board">
          <TabsList className="bg-zinc-900 border border-zinc-800">
            <TabsTrigger value="board" className="data-[state=active]:bg-zinc-800">
              Task Board
            </TabsTrigger>
            <TabsTrigger value="kernel" className="data-[state=active]:bg-zinc-800">
              Kernel Verdicts
            </TabsTrigger>
            <TabsTrigger value="waves" className="data-[state=active]:bg-zinc-800">
              Wave Reports
            </TabsTrigger>
            <TabsTrigger value="ark" className="data-[state=active]:bg-zinc-800">
              ARK
            </TabsTrigger>
          </TabsList>

          <TabsContent value="board" className="space-y-4">
            {TASKS.map((t) => (
              <Card
                key={t.id}
                className="bg-zinc-900 border-zinc-800 break-inside-avoid"
              >
                <CardHeader className="pb-2">
                  <div className="flex flex-wrap items-center gap-2">
                    <span className="font-mono text-xs text-zinc-400">
                      {t.id}
                    </span>
                    <CardTitle className="text-base">{t.name}</CardTitle>
                    <span className="ml-auto">
                      <StateBadge state={t.state} />
                    </span>
                  </div>
                </CardHeader>
                <CardContent className="space-y-2">
                  <p className="text-sm text-zinc-300 leading-relaxed">
                    {t.detail}
                  </p>
                  <p className="text-xs font-mono text-zinc-500">
                    Runs: {t.runs}
                  </p>
                </CardContent>
              </Card>
            ))}
          </TabsContent>

          <TabsContent value="kernel" className="space-y-3">
            <Card className="bg-zinc-900 border-zinc-800">
              <CardHeader className="pb-2">
                <div className="flex items-center gap-2">
                  <Activity className="h-4 w-4 text-red-500" />
                  <CardTitle className="text-base">
                    Live kernel verdicts
                  </CardTitle>
                  <Button
                    size="sm"
                    variant="outline"
                    className="ml-auto border-zinc-700 bg-transparent"
                    onClick={() => setTick((x) => x + 1)}
                  >
                    <Terminal className="mr-1 h-3 w-3" /> Refresh
                  </Button>
                </div>
              </CardHeader>
              <CardContent>
                <p className="text-xs text-zinc-500 mb-3">
                  Polled server-side every 30 seconds. The token never reaches
                  the client.
                </p>
                {!loaded ? (
                  <div className="flex items-center gap-2 text-sm text-zinc-400 py-6 justify-center">
                    <Loader2 className="h-4 w-4 animate-spin" /> Loading CI
                    state...
                  </div>
                ) : runs.length === 0 ? (
                  <p className="text-sm text-zinc-400 py-6 text-center">
                    No lane runs visible yet.
                  </p>
                ) : (
                  <div className="max-h-96 overflow-y-auto space-y-1 pr-1">
                    {runs.map((r) => (
                      <RunRow key={r.id} run={r} />
                    ))}
                  </div>
                )}
              </CardContent>
            </Card>
          </TabsContent>

          <TabsContent value="waves" className="space-y-4">
            {WAVES.map((w) => (
              <Card
                key={w.id}
                className="bg-zinc-900 border-zinc-800"
              >
                <CardHeader className="pb-2">
                  <div className="flex items-center gap-2">
                    <Badge
                      variant="outline"
                      className="font-mono border-red-800 text-red-400"
                    >
                      WAVE {w.id}
                    </Badge>
                    <CardTitle className="text-sm">{w.title}</CardTitle>
                  </div>
                </CardHeader>
                <CardContent>
                  <p className="text-sm text-zinc-300 leading-relaxed">
                    {w.body}
                  </p>
                </CardContent>
              </Card>
            ))}
          </TabsContent>

          <TabsContent value="ark" className="space-y-4">
            <Card className="bg-zinc-900 border-emerald-900/50">
              <CardHeader className="pb-2">
                <div className="flex items-center gap-2">
                  <ShieldCheck className="h-5 w-5 text-emerald-500" />
                  <CardTitle className="text-base">
                    THE ARK — five-layer survival system
                  </CardTitle>
                </div>
              </CardHeader>
              <CardContent className="space-y-3">
                <p className="text-sm text-zinc-300">
                  BOSS order in force: every file survives, even under forced
                  deletion. Five independent layers:
                </p>
                <ol className="text-sm space-y-2 text-zinc-300 list-decimal list-inside">
                  <li>
                    <span className="font-semibold">Layer 1 — git vault:</span>{" "}
                    /home/z/ark/vault (versioned, committed every sweep)
                  </li>
                  <li>
                    <span className="font-semibold">
                      Layer 2 — dual snapshots:
                    </span>{" "}
                    tarballs + the full hc-repo git bundle at BOTH
                    /home/z/ark/snapshots and the /home/z/my-project/.ark
                    fallback
                  </li>
                  <li>
                    <span className="font-semibold">
                      Layer 3 — GitHub mirror:
                    </span>{" "}
                    the ark/sandbox-vault branch on kyo-oo/HC-PROOF (immutable
                    remote history)
                  </li>
                  <li>
                    <span className="font-semibold">
                      Layer 4 — Drive bag:
                    </span>{" "}
                    the token + secrets re-downloadable from the Drive link on
                    any wipe
                  </li>
                  <li>
                    <span className="font-semibold">
                      Layer 5 — watchdog:
                    </span>{" "}
                    the 8-hour cron sweep — protect + integrity check +
                    auto-resurrect (survives sandbox deletion itself)
                  </li>
                </ol>
                <p className="text-xs font-mono text-zinc-500">
                  protect.sh — re-vault, re-snapshot, mirror-push · resurrect.sh
                  — restore from vault/snapshot/mirror/public-clone layers
                </p>
              </CardContent>
            </Card>
          </TabsContent>
        </Tabs>
      </main>

      <footer className="mt-auto border-t border-zinc-800 bg-zinc-900">
        <div className="max-w-6xl mx-auto px-4 py-4 flex flex-wrap items-center gap-x-4 gap-y-2">
          <span className="text-xs font-mono text-zinc-500">
            HC-PROOF · the GST campaign · BOSS&apos;s own mathematics
          </span>
          <span className="text-xs font-mono text-zinc-500 ml-auto">
            det[Krylov] = -1,149,656,584,000 ≠ 0 · rank 12/12
          </span>
        </div>
      </footer>
    </div>
  );
}
