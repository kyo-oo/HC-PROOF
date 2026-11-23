# THE ARSENAL — Weapon Inventory + Invocation System (v2.0 NEXT-GEN)

> This file is THE invocation system for the MATHS Berserker engine and ALL sub-agents.
> Every weapon below has a VERIFIED invocation command tested on THIS machine.
> Sub-agents: READ THIS FILE FIRST. Copy invocation patterns EXACTLY. Do not improvise paths.

## §W.0 — WEAPON ROUTING TABLE (problem class → weapon)

| Target class | Primary weapon | Secondary / cross-check |
|---|---|---|
| Number theory (factoring, primality, congruences, orders, class groups, elliptic curves, L-functions, Galois) | PARI/GP 2.17.2 (cypari2) | sympy + gmpy2 (two-method agreement law) |
| Symbolic algebra (solve, simplify, Groebner, series, limits, combinatorics) | sympy 1.14 | PARI for polynomial/number-theoretic core |
| Big-integer arithmetic, fast primality (BPSW), factor helpers | gmpy2 2.3.2 | PARI `isprime` (provable) |
| SMT: integer/real nonlinear arithmetic, SAT, optimization, scheduling, bounds-hunting, counterexample search | Z3 5.4.1 (`z3-solver` py) | Vampire (arith via TPTP) for pure FOL |
| First-order logic conjectures, axiom systems,自动 refutation, TPTP problems, proof certification | Vampire 5.1.0 (binary) | Z3 (if decidable fragment) |
| Formal theorem certification (Lean 4 + Mathlib, `#print axioms`, sorry-free) | GitHub Actions CI ONLY | NEVER local Lean (repo law) |
| Group theory (permutation groups, named groups) | sympy.combinatorics | PARI `polgalois` for Galois groups |
| Wolfram .wl checks | Commit to HC repo + CI dispatch | — (no local Wolfram) |

## §W.1 — TIER 0: LIVE WEAPONS (installed, verified on this machine)

### W.1.1 — PARI/GP 2.17.2 via cypari2 (NUMBER THEORY KING)

```python
import cypari2
pari = cypari2.Pari(size=10**8)   # 800MB stack; raise to 10**9 for big jobs
pari.factor('2^64+1')             # → [274177, 1; 67280421310721, 1]
pari('sigma(28)')                 # → 56
pari('ellinit([0,0,1,-1,0])')     # elliptic curve object (indexing 0-based: [15] = conductor in GP 1-based → [14] py)
pari('quadclassunit(-163)')       # class group of Q(√-163); [0] = class number
pari('znorder(Mod(2,59))')        # multiplicative order → 58
pari('polgalois(x^5-x-1)')        # Galois group of polynomial
pari('isprime(2^127-1)')          # PROVABLE primality (Pratt certificate)
pari('factorint(10^30+57)')       # integer factoring
pari('quadgen(-163)')             # quadratic field generator
pari('bnfinit(x^2+163)')          # full number field data (class group, units)
pari('ellsearch(\"11a1\")')       # curve lookup in Cremona-like tables
pari('Mod(3,10^8).znlog(6561)')   # discrete log in (Z/n)*
```
**Verified**: factor(2^64+1), sigma(28)=56, h(-163)=1, ord_59(2)=58 all correct.
**Use for**: every number-theoretic computation in Erdős-class problems; cross-check sympy.
**Trap**: GP 1-based indexing translated to Python 0-based. Strings are safest for complex calls.

### W.1.2 — Z3 5.4.1 (SMT SOLVER — counterexample hunter)

```python
from z3 import *
s = Solver()
x, y = Ints('x y')
s.add(x*x > 100, x < 20, x > 0)
s.check()      # sat → model is a WITNESS
s.model()      # [x = 17]
# Optimization:
o = Optimize(); o.add(x > 0); o.minimize(x*x + 3); o.check(); o.model()
# Prove a conjecture (unsat of negation = PROOF for decidable fragment):
s2 = Solver(); s2.add(Not(ForAll([x], Implies(x > 2, x*x > 4))))
s2.check()     # unsat → ∀x>2: x²>4 VERIFIED
```
**Verified**: live on this machine (5.4.1).
**Use for**: finite-range certification, witness construction, bounded counterexample search, nonlinear integer arithmetic, SAT encodings of combinatorial problems.
**NO-OOM LAW**: never push Z3 a search space > ~2^30 without a timeout: `s.set("timeout", 60000)` (ms).

### W.1.3 — Vampire 5.1.0 (FIRST-ORDER ATP — TPTP)

Binary: `/home/z/atp/vampire` (static, 55MB, links Z3 4.14 + CaDiCaL 2.1.3 internally).

```bash
# TPTP file format (.p): fof(axiom...), fof(conjecture...)
/home/z/atp/vampire --proof tptp problem.p          # refutation = PROOF
/home/z/atp/vampire --proof tptp -t 60 problem.p    # 60s time cap
/home/z/atp/vampire --avatar off problem.p          # classic mode for reproducibility
```
**Verified**: asymmetry + transitivity ⊢ irreflexivity refuted in 0.0000s on this machine.
**Use for**: FOL conjecture certification, axiom-consistency checks, automated lemma proving before Lean formalization, TPTP library problems.

### W.1.4 — sympy 1.14 + gmpy2 2.3.2 (BASELINE STACK)

```python
import sympy as sp, gmpy2
sp.solve([x**2+y**2-25, x-y-1], [x,y])    # exact solving
sp.groebner([...], x, y, order='lex')     # Groebner bases
gmpy2.is_prime(2**89-1)                   # BPSW strong probable prime
gmpy2.iroot(10**40, 3)                    # exact integer roots
gmpy2.mpz(2)**1000                        # fast big arithmetic
sp.combinatorics.SymmetricGroup(5)        # permutation groups (GAP substitute)
```
**Use for**: everything symbolic; SECOND METHOD for the two-method agreement law (§8 MATHS).

## §W.2 — TIER 1: CI-ONLY WEAPONS (GitHub Actions — the carrier discipline)

### W.2.1 — Lean 4.33.0-rc2 + Mathlib v4.33.0-rc2 (THE CERTIFIER)

**LAW (from both campaign repos): NEVER install/compile Lean locally. All Lean verification via GitHub Actions.**

```
Repo:     kyo-oo/HC-PROOF       (branch: research/gpt6-native-point-primitive-span-20261017)
Repo:     kyo-oo/erdos-weak-problems (branch: campaign)
Token:    /home/z/bag/extracted/erdos-zipbag/secrets/ghtoken.txt
Clone:    git clone --single-branch --branch <branch> https://x-access-token:$(cat <token>)@github.com/kyo-oo/HC-PROOF.git
Push:     git push https://x-access-token:$(cat <token>)@github.com/kyo-oo/HC-PROOF.git HEAD:<branch>
Watch:    curl -s -H "Authorization: token $(cat <token>)" "https://api.github.com/repos/kyo-oo/HC-PROOF/actions/runs?per_page=5"
Dispatch: curl -X POST -H "Authorization: token $(cat <token>)" "https://api.github.com/repos/kyo-oo/HC-PROOF/actions/workflows/<wf>.yml/dispatches" -d '{"ref":"<branch>"}'
```
HC-PROOF CI pattern (175 per-module workflows): ubuntu-24.04, elan + leanprover/lean4:v4.33.0-rc2, `lake exe cache get`, per-module `[[lean_lib]]` roots appended to lakefile.toml, `lake build <lib>`, grep-fail on `error:|sorryAx|declaration uses 'sorry'`, 95-min timeout, .lake/build cache keys.
**Use for**: the ONLY truth for formal claims. A Lean file that never compiled green is BLUFFING.
**Audit law**: `#print axioms <thm>` must show only `[propext, Quot.sound]` (or documented extras). `sorry`/`admit`/fake axioms = death.

### W.2.2 — Wolfram .wl (HC repo discipline)
145 .wl files live in HC repo research/computations. No local Wolfram. They are evidence records; new .wl checks follow existing repo patterns (commit + document outputs in records).

## §W.3 — TIER 2: UNAVAILABLE LOCALLY + VERIFIED SUBSTITUTES

| Weapon | Status | Substitute (use this) |
|---|---|---|
| SageMath | NOT installable (no root) | **sympy + cypari2(PARI) + gmpy2 stack** — covers the number-theory 80% of sage usage |
| GAP | NOT installable (no root; `gappy` on PyPI is a Discord bot — TRAP) | **sympy.combinatorics** (perm groups, named groups) + **PARI polgalois/galoisinit** |
| local Lean/lake | FORBIDDEN by repo law | GitHub Actions CI (W.2.1) |

## §W.4 — THE INVOCATION LAW (for commander + every sub-agent)

1. **Sub-agent briefs ALWAYS begin**: "Read /home/z/my-project/skills/prove-that-shit/ARSENAL.md first. Use its exact invocation patterns."
2. **Two-method agreement** (MATHS §8): every computation runs on TWO weapons before it enters a claim (e.g. PARI + sympy).
3. **Weapon escalation**: sympy → PARI (number theory) or Z3 (logic/search) → Vampire (FOL proof) → Lean CI (final certification). Numerics never jump the queue.
4. **CI-carrier discipline**: no local lake/lean ever; pushes only after worklog-recorded intent; never label an old green run as validating a new SHA.
5. **NO-OOM LAW**: decide sweeps ≤ 501; Z3 timeouts set; Vampire `-t` cap set; PARI parisize bounded.
6. **Honest tiers**: a Tier-0 result is evidence; only CI-green Lean is certification. Label accordingly — never dress evidence as proof.

## §W.5 — CAMPAIGN CONTEXT (what these weapons serve)

- **Erdős campaign** (kyo-oo/erdos-weak-problems, branch campaign, HEAD fa4a160, sealed S059): 47 problem folders, 65+ kernels, kills.yml CI assembly line. Worklog: WORKLOG.md (3474 lines). Full bag: /home/z/bag/extracted/erdos-zipbag/.
- **HC-PROOF campaign** (kyo-oo/HC-PROOF, branch research/gpt6-native-point-primitive-span-20261017, HEAD da5e109): THE HODGE CONJECTURE assault — Cardinal Worlds + GST V2 Graph Ontological Universe merged; Hodge & de Rham as finite comparison certificates. 824 Lean files, 394 md, 151 tex, 145 wl, 121 py. Law file: AGENTS.md. Active plan: research/ACTIVE_HODGE_PROOF_PLAN.md. Cloned at /home/z/hc-repo.
- **The map** (agent-only understanding files): /home/z/hc-map/ — read MANIFEST.md first.
- **The engine never stops; it never lies. In English, always.**
