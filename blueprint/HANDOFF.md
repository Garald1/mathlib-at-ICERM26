# Handoff to Claude Code: Weil's explicit formula (Montgomery–Vaughan Theorem 12.13, q = 1)

Written on 26 November 2026 by Claude (claude.ai, in a sandbox without Lean) for Harald Helfgott, who will run
Claude Code on his laptop. Nothing under `blueprint/` has been compiled.

## What this is

The goal is a Lean proof of Theorem 12.13 of Montgomery–Vaughan (MV), *Multiplicative Number Theory I*, in the case
q = 1, integrated into IEANTN (`teorth/IEANTN`) as a node whose imports are other IEANTN nodes, and from there
registered on Palomar through IEANTN's spin-off tool. The proofs use Harald's Riemann–Stieltjes library (branch
`dirichlet-jordan` of `Garald1/mathlib-at-icerm26`, and the other chat's branch `mv-lemma-12-14` on top of it).

Read, in this order, before doing anything:
1. `blueprint/WeilExplicitFormula.md`, all of it. §4 records Harald's decisions; §5 the IEANTN plan.
2. In the IEANTN clone: `CLAUDE.md`, `CONTRIBUTING.md`, `docs/ARCHITECTURE.md`, `docs/NODES.md`, `docs/SOLUTIONS.md`.

## Coordination (updated 27 November 2026, evening)

Another chat works on the same project, in branch `mv-lemma-12-14` of `Garald1/mathlib-at-ICERM26` (head `e62f9988`:
thirteen commits on top of `dirichlet-jordan` `90f274f8`, with the same Lean and Mathlib as the library; it merges
cleanly into `weil-explicit-formula`). That chat reports no `sorry` and no axioms beyond `propext`,
`Classical.choice`, `Quot.sound`.

**All the mathematics is done there**, on the fork's Mathlib:
- Part A (the Fourier integral theorem), Part B (Theorem C.5, Lemma 12.14, the digamma bounds);
- **Theorem 12.13 (q = 1) from three hypotheses**: `WeilExplicitFormula.theorem_12_13_of (h1013 : Theorem_10_13)
  (h122 : Lemma_12_2) (hres : ResidueTheoremRectangle) : Theorem_12_13` (`NumberTheory/WeilExplicitFormula/ExplicitFormula.lean`);
- **Theorem 10.13 and Lemma 12.2**: `WeilExplicitFormula.theorem_10_13 : Theorem_10_13` and
  `WeilExplicitFormula.lemma_12_2 : Lemma_12_2` (`Main.lean`; proofs in `ZetaBounds`, `ZeroCount`, `ZetaLogDeriv`,
  `Landau`, `GoodHeights`), and `theorem_12_13_of_residueTheorem (hres) : Theorem_12_13`;
- **the residue theorem on rectangles**: `ResidueRectangle.residue_theorem_rectangle`, in
  `Mathlib/Analysis/Complex/ResidueRectangle.lean`, which imports only Mathlib;
- **the equivalence of MV's printed hypotheses (12.20)–(12.21) with the node's form**: `isTestFunctionNode_iff`
  (`Hypotheses.lean`; (12.21) as a Riemann–Stieltjes integral against the variation of F).

Checked from claude.ai, textually: `Theorem_12_13`, `Theorem_10_13`, `Lemma_12_2`, `ResidueTheoremRectangle`,
`LogDerivFunctionalEquation`, the residue theorem's statement, and the copies of `zetaZeroesIn`, `zetaOrder`,
`zetaZeroesSum` are verbatim copies of the IEANTN statements (`Phi` writes `π` for `Real.pi`). Nothing has been
compiled at IEANTN's pin yet: that is this laptop's job.

**So this laptop does:** Task 5 (the reactivation pull request, then the solution of `ContourIntegration.v1` from
`ResidueRectangle.lean`), Task 1 (the port), Task 2 from step 2 on, and Task 7 (the solutions of
`ZetaGoodHeights.v1` and `WeilExplicitFormula.v1`, by unfolding). Tasks 3, 4 and 6, and step 1 of Task 2, are done
there: do not redo them.

## Ground rules

- **The book is the ground truth for statements.** Harald has the PDF of MV; ask him for its path. Do not quote
  equation or theorem numbers from memory.
- **Never weaken a statement to make a proof go through.** If a draft statement here is wrong, say so and propose the
  correction; do not quietly change its meaning. Report every change of meaning, however small.
- Anything reported as proved has no `sorry`, no `native_decide`, and no axioms beyond `propext`, `Quot.sound` and
  `Classical.choice` (what Comparator permits). Check with `#print axioms`.
- Use `lake exe cache get`; never build Mathlib from source.
- Toolchain: IEANTN's `lean-toolchain` and the Mathlib commit in IEANTN's `lake-manifest.json` (v4.34.0-rc2 and
  `71a80585ee495fc24472fd0eaffc89d94e4fd8d6` when this was written; if IEANTN's `main` has moved, use its current pin).
- Push only to Harald's own repositories (`Garald1/...`). **No pull requests or issues** on `teorth/IEANTN`,
  `leanprover-community/...` or anyone else's repository without Harald's explicit go-ahead.
- Keep `STATUS.md` at the root of the library repository: what is done, what is next, open questions. Update it at
  every milestone, so that work can resume after an interruption.
- Small commits with descriptive messages; push at each milestone.

## Layout

Work in `~/Documents/lean/weil` (Harald's Lean directory is `~/Documents/lean`). Harald starts Claude Code there,
after cloning this branch into `plan/` with
`git clone --depth 1 -b weil-explicit-formula https://github.com/Garald1/mathlib-at-icerm26.git plan`.
If he already has clones of the repositories below elsewhere in `~/Documents/lean`, ask before making new ones.
- `plan/` — this branch (`weil-explicit-formula` of `Garald1/mathlib-at-icerm26`). Besides the blueprint, it contains
  the Riemann–Stieltjes files, since it is based on `dirichlet-jordan`.
- `RiemannStieltjes/` — the ICERM library (Riemann–Stieltjes theory), created in Task 1.
- `WeilExplicitFormula/` — the second package (everything else the proof needs), created in Task 1.
- `ieantn/` — Harald's fork `Garald1/ieantn` (use his existing clone if he has one), brought up to date with
  `teorth/IEANTN` `main` before starting.

## Task 1 — two standalone Lake packages: the ICERM library, and the rest

An IEANTN solution must use the core's Mathlib revision and cannot depend on a fork of Mathlib, so the code has to
become packages of its own, pinned to IEANTN's Lean and Mathlib. **Harald's decision (27 November): the ICERM library
keeps its own identity.** It holds basic Riemann–Stieltjes theory (Montgomery–Vaughan's Appendix A) and the
Dirichlet–Jordan theorem as in Wheeden–Zygmund (12.50), already in it, and nothing else. Everything written since,
for the explicit formula, goes into a second package that requires the first.

1. Repositories, both **public** (IEANTN's verification and the Palomar spin-off must fetch them at published commits):
   `Garald1/RiemannStieltjes` (Lake package `RiemannStieltjes`) and, for the rest, a second one (proposed:
   `Garald1/WeilExplicitFormula`, Lake package `WeilExplicitFormula`). Ask Harald to confirm the second name, then
   create both.
2. Both packages: `lean-toolchain` identical to IEANTN's; `require mathlib` at IEANTN's Mathlib commit, as a full
   40-character hash. `WeilExplicitFormula` also requires `RiemannStieltjes`, pinned at a commit.
3. What to port. **Into `RiemannStieltjes`:** relative to upstream Mathlib commit `09370b01` (the last upstream merge into the workshop branch,
   18 May 2026; the full `git diff --stat` is in `blueprint/port/diffstat-against-mathlib-09370b01.txt`), branch
   `dirichlet-jordan` does the following, and nothing else:
   - **adds 18 files** (about 7,600 lines):
     `Mathlib/Analysis/BoxIntegral/Box/Ioc.lean`,
     `Mathlib/Analysis/BoxIntegral/Partition/{Dual,Onedim,OrderedDivision}.lean`,
     `Mathlib/Analysis/BoxIntegral/Stieltjes/{Defs,Basic,Riemann,RiemannStieltjesSum,IntegrationByParts,Measure,
     ChangeVariables,Sum,Fourier,DirichletJordan,Unused}.lean`,
     `Mathlib/Analysis/Fourier/{Fejer,FejerKernel}.lean`, `Mathlib/Analysis/SpecificLimits/Cesaro.lean`
     (also `Scratch.lean`, not to be ported);
   - **adds about 500 lines of lemmas to six existing Mathlib files**: `Mathlib/Analysis/BoxIntegral/Basic.lean` and
     `Mathlib/Analysis/BoxIntegral/Partition/{Additive,Basic,Filter,Measure,Split}.lean`. A package cannot edit
     Mathlib, so these go into new files of the package, one per original file, with unchanged names (unless a name
     now clashes with something Mathlib has added since: then report it). The additions are in
     `blueprint/port/additions-to-mathlib-files.patch`. The only deleted lines (two) are inside a proof in
     `Partition/Basic.lean` and need not be carried over.

   **Into `WeilExplicitFormula`:** branch `mv-lemma-12-14` (the other chat's; `dirichlet-jordan` plus thirteen commits,
   head `e62f9988`, so port from it) **adds 20 files** (about 8,850 lines):
   `Mathlib/Analysis/SpecialFunctions/Gamma/{DigammaSeries,DigammaFourier}.lean`,
   `Mathlib/Analysis/BoxIntegral/Stieltjes/{VariationBounds,DigammaPairing,FourierIntegral}.lean`, and
   `Mathlib/NumberTheory/WeilExplicitFormula/{TestFunction,TranslateSum,PrimeSum,CriticalLine,Rectangle,Xi,Contour,ExplicitFormula,ZetaBounds,ZeroCount,ZetaLogDeriv,Landau,GoodHeights,Hypotheses,Main}.lean`.
   Its 21st new file, `Mathlib/Analysis/Complex/ResidueRectangle.lean`, goes into IEANTN instead (Task 5).
   Besides Mathlib, they import only each other and the library's own files. Two notes on the last eight:
   `Contour.lean` imports `Mathlib.NumberTheory.LSeries.ZetaZeros`, which the pin has (with
   `IsCompact.inter_riemannZetaZeros_finite`); and `Xi.lean` proves `WeilExplicitFormula.riemannZeta_conj` (for
   s ≠ 1) because the fork's Mathlib lacks it, while the pin has `riemannZeta_conj` (all s) in
   `NumberTheory/Harmonic/ZetaAsymp.lean`. The names don't clash (namespace); keep the library's or derive it from
   Mathlib's, as is easier. The pin has no `deriv_`, `logDeriv_` or `analyticOrderAt_riemannZeta_conj`: keep those.
   The same branch qualifies `Set.Ioc` in
   `Mathlib/Analysis/BoxIntegral/DivergenceTheorem.lean` and `Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean`
   to fix the fork's build: **do not port that.** `Complex.hasSum_digamma` (in `DigammaSeries.lean`) is the Gauss
   series for Re s > 0, proved independently of `GammaSolution.digamma_eq_gaussSum` in IEANTN's
   `Solutions/GammaAsymptotics.v2`: use the library's, and do not copy the IEANTN one into the library. Whatever the
   other chat adds later is ported the same way (Theorem 10.13 and Lemma 12.2, the (12.20)–(12.21) equivalence),
   **except the residue theorem on rectangles**: the other chat writes it as Mathlib-only file(s), and they go
   directly into IEANTN's `Solutions/ContourIntegration.v1/`, the one place that proof will live, and into neither
   package. (The explicit formula only needs its statement, `ResidueTheoremRectangle`, as a hypothesis.)

   `Stieltjes/Unused.lean` says of itself that it is not in use: ask Harald before dropping it. Keep every file's
   copyright header and author list as it is.
4. Module names `RiemannStieltjes.<path as in Mathlib>` and `WeilExplicitFormula.<path as in Mathlib>`; keep
   namespaces and declaration names unchanged, so that the code can later go into Mathlib without renaming.
5. Port to the newer Mathlib with the smallest changes that work; record each kind of change in `PORTING.md`.
6. `lake build` clean (no `sorry`). Commit, push, update `STATUS.md`.

## Task 2 — compile the draft statements

1. **Done in the other chat; skip it (see Coordination).** Every statement of `FourierIntegral.lean` is proved,
   unchanged, in `Stieltjes/FourierIntegral.lean`; of `DigammaFourier.lean`, B3 (both statements), B4 and B5 are
   proved under the draft's names. What this step said: library: add `blueprint/drafts/FourierIntegral.lean` and
   `blueprint/drafts/DigammaFourier.lean` as
   `RiemannStieltjes.FourierIntegral` and `RiemannStieltjes.DigammaFourier` (fix imports and module syntax). They are
   statements with `sorry`. **First audit each statement** against the blueprint (§2, parts A and B) and, for B4 and
   B5, against MV Theorem C.5 and Lemma 12.14 in the PDF; then make them elaborate.
2. IEANTN: in `ieantn/`, on a new branch `weil-explicit-formula`, add the drafts in `blueprint/ieantn/` as
   `IEANTN/Nodes/WeilExplicitFormula/v1/` and `IEANTN/Nodes/ZetaGoodHeights/v1/`, registering them wherever
   `docs/NODES.md` says nodes are registered. Run `python scripts/ieantn.py gen-challenges`,
   `python scripts/ieantn.py fingerprint`, `lake build`, `python scripts/ieantn.py check`, and fix what fails.
   `ContourIntegration.v1` is `inactive`: report what `check` says about importing it, but do not change its status —
   that is for Harald to agree with the maintainers. Do not commit generated views (`STATE.md`, `GRAPH.md`,
   `docs/graph.html`, `docs/nodes/`). Push the branch to `Garald1/ieantn`; no pull request.
3. `blueprint/drafts/WeilExplicitFormula.lean` holds statements of the intermediate lemmas about ζ (C1–C7, D1, E, F,
   G), written against the old Mathlib fork. Superseded: the other chat's `NumberTheory/WeilExplicitFormula/` files
   prove them (with the departures listed in the blueprint, §2). Do not compile it.
4. **Stop and report** to Harald: what compiled, every statement whose meaning you changed and why, and questions.

## Task 3 — Part A: the Fourier integral theorem

**Done in the other chat** (`Stieltjes/FourierIntegral.lean`, commit `3992e7d7`). Nothing to do here beyond
porting (Task 1). What this task said: in the library, prove A1–A6 of the blueprint (`FourierIntegral.lean`) by the route of `DirichletJordan.lean`:
Fejér's theorem for Fourier integrals, Hardy's Tauberian theorem for integrals reduced to the discrete
`tendsto_sum_range_of_tendsto_cesaroMean`, and `FourierTransform.fourier_bounded_variation`. No `sorry` left.
**Stop and report.**

## Task 4 — Part B: the digamma function, Theorem C.5, Lemma 12.14

**Done in the other chat** (branch `mv-lemma-12-14`; blueprint §2, entries marked **L**): B4 is
`Complex.exists_integral_digamma_mul_exp`, B5 is `Complex.tendsto_integral_digamma_mul_fourier` and
`Complex.tendsto_integral_digamma_conj_mul_fourier`, and the two B3 statements are `Complex.exists_norm_digamma_le_log`
and `Complex.exists_norm_digamma_sub_le`.
B4 was proved without residues, so it does not need Task 5. Nothing to do here beyond porting (Task 1).

## Task 5 — `ContourIntegration.v1`: reactivation now, solution later

**Reactivation (decided by Harald, 27 November).** Branch `reactivate-contour-integration` of `Garald1/IEANTN`
(commit `906a4d0`, on `main` at `e25e4f8`) runs `python scripts/ieantn.py reactivate ContourIntegration.v1`: the
node's status goes back to `awaiting-solution` and it rejoins the umbrella `IEANTN/Nodes.lean`; `check-graph` and
`check-closure` pass. What is missing is the node's `fingerprints.json`, which needs a Lean build. To finish:
1. Check out that branch in `ieantn/`. Its one commit's author line reads `Harald Andres Helfgott
   <noreply@anthropic.com>` (a slip): amend it to Harald's own identity
   (`git commit --amend --reset-author --no-edit`).
2. `lake exe cache get`, `lake build`, then `python scripts/ieantn.py fingerprint`. It should create
   `IEANTN/Nodes/ContourIntegration/v1/fingerprints.json` and change nothing else; if it changes anything else, stop
   and report. Then `python scripts/ieantn.py check`.
3. Add the fingerprints to the same commit (`git commit --amend --no-edit`), force-push this branch (it is new and
   nobody else uses it), and open the pull request to `teorth/IEANTN` with the title and description below (Harald
   has approved this one pull request). Do not commit `STATE.md`, `GRAPH.md`, `docs/graph.html` or `docs/nodes/`.

Title: `Reactivate ContourIntegration.v1 (residue theorem on a rectangle)`

Description:

> Reactivates `ContourIntegration.v1` with `python scripts/ieantn.py reactivate ContourIntegration.v1`: its status
> returns to `awaiting-solution`, it rejoins the umbrella, and its fingerprint is regenerated. The statement is
> unchanged.
>
> Its recorded reason for deactivation said this would be "the first thing to reactivate if a future node needs
> contour integration". The future node is coming: `WeilExplicitFormula.v1`, Montgomery–Vaughan Theorem 12.13
> (Weil's explicit formula) for q = 1, will import `residue_theorem_rectangle`, together with Montgomery–Vaughan
> Theorem 10.13 and Lemma 12.2 in a second new node, `ZetaGoodHeights.v1`. A Lean proof of Theorem 12.13 from exactly
> these three statements, copied verbatim, already exists in a Riemann–Stieltjes library that the solutions will pin.
> The two nodes, and a solution for this one, will follow in separate pull requests.

Base the Task 2 branch (the node drafts) on this branch until it is merged: `WeilExplicitFormula.v1` imports this node,
and `check-graph` fails an edge onto an inactive node.

**Solution.** The proof is `Mathlib/Analysis/Complex/ResidueRectangle.lean` on `mv-lemma-12-14` (commit `e62f9988`;
Mathlib-only, five imports; its theorem `ResidueRectangle.residue_theorem_rectangle` states the node's conclusion
verbatim). It goes into IEANTN as this node's solution, and nowhere else (not into either package):
1. Copy it to `Solutions/ContourIntegration.v1/ResidueRectangle.lean`. Delete the lines `module` and
   `@[expose] public section`, and change `public import` to `import` (compare `Solutions/CH2.v3/ResiduePort.lean`).
   Keep its header.
2. Add `Solution.lean`, importing `ResidueRectangle` and `IEANTN.Nodes.ContourIntegration.v1.Conclusions`, with
   ```lean
   theorem ContourIntegration.v1.challenge_residue_theorem_rectangle :
       ContourIntegration.v1.residue_theorem_rectangle :=
     ResidueRectangle.residue_theorem_rectangle
   ```
   (the name and statement of the theorem in the node's `Challenge.lean`; do not import the `Challenge`).
3. Add `lakefile.toml` (package `solution_ContourIntegration_v1`, `require IEANTN` with `path = "../.."`, one
   `lean_lib` per root), `lean-toolchain` (IEANTN's) and `comparator.json` (`challenge_module`
   `IEANTN.Nodes.ContourIntegration.v1.Challenge`, `solution_module` `Solution`, `theorem_names`
   `["ContourIntegration.v1.challenge_residue_theorem_rectangle"]`, the three permitted axioms, `enable_nanoda`),
   all as in `Solutions/CH2.v3/`.
4. Build it at IEANTN's pin. The other chat could not: it only checked that the five imported modules and every
   Mathlib name the file uses exist at `71a80585` and are not deprecated. If something fails, make the smallest change
   that works and record it in `PORTING.md`.
5. Run Comparator locally (`scripts/verify-comparator.sh`). Commit on a branch of `Garald1/IEANTN` based on the
   reactivation branch. The pull request for the solution is Harald's to start, after the reactivation is merged.

## Task 6 — a solution for `ZetaGoodHeights.v1`

**Done in the other chat**: `WeilExplicitFormula.theorem_10_13 : Theorem_10_13` and
`WeilExplicitFormula.lemma_12_2 : Lemma_12_2`. Its proof of Lemma 12.2 proves the functional equation of ζ'/ζ
itself (`ZetaLogDeriv.lean`, as `LogDerivFunctionalEquation`, a verbatim copy of
`ZetaLogDeriv.v1.logDeriv_functional_equation`). The node keeps importing `ZetaLogDeriv.v1` (decision 3 of the
blueprint: import the nodes already there), so the solution should use the imported statement, through a library
theorem `lemma_12_2_of (hFE : LogDerivFunctionalEquation) : Lemma_12_2`, which the other chat has been asked to add.
If it is not there when you get to Task 7, ask Harald. The IEANTN solution itself is part of Task 7.

## Task 7 — the IEANTN solutions for `WeilExplicitFormula.v1` and `ZetaGoodHeights.v1`

After Task 1 (and Task 2, so that the node drafts compile in IEANTN). The library states the IEANTN conclusions and
their imports verbatim, with its own copies of `zetaZeroesIn`, `zetaOrder`, `zetaZeroesSum`. So each solution is the
library theorem plus unfolding: for `WeilExplicitFormula.v1`, `WeilExplicitFormula.theorem_12_13_of` gives
`theorem_12_13` from the challenge's hypotheses (`ContourIntegration.v1.residue_theorem_rectangle`,
`ZetaGoodHeights.v1.theorem_10_13`, `ZetaGoodHeights.v1.lemma_12_2`); for `ZetaGoodHeights.v1`, the library's proofs
of `Theorem_10_13` (`theorem_10_13`) and `Lemma_12_2` (`lemma_12_2_of` applied to the challenge's hypothesis). The node's `IsTestFunction`, `rhs` and `Phi` correspond to the library's
`IsTestFunctionNode`, `rhsNode` and `Phi` (same bodies; `Phi` writes `π`). If unfolding does not close a goal by
`Iff.rfl` or `rfl`, report it rather than proving a bridge by hand: it would mean a copy is not verbatim after all.

Then run Comparator locally (`scripts/verify-comparator.sh`, as `CONTRIBUTING.md` describes). The official
verification workflow, any pull request, and the Palomar submission (`python scripts/ieantn.py spinoff ...`) are
Harald's to start.

## Reporting

At each stop: what was done; every change of meaning in a statement; what is next; questions. Keep it short; details
go in `STATUS.md` and the commit messages.

## Appendix — draft issue for `teorth/IEANTN` (for Harald to post, edited as he likes)

> **Weil's explicit formula (Montgomery–Vaughan Theorem 12.13, q = 1): two new nodes, a reactivation, a solution**
>
> I would like to add `WeilExplicitFormula.v1` (kind `standard`; MV Theorem 12.13 for q = 1) and
> `ZetaGoodHeights.v1` (kind `standard`; MV Theorem 10.13 and Lemma 12.2, which a contour argument needs to place its
> horizontal sides). The first imports `ContourIntegration.v1` (`residue_theorem_rectangle`) and both conclusions of
> `ZetaGoodHeights.v1`; it does not use `ZetaHadamard.v1`, since the proofs go through Jensen's inequality and the
> Borel–Carathéodory lemma rather than the Hadamard product, nor `ZetaZeroes.v1`, since Mathlib's
> `IsCompact.inter_riemannZetaZeros_finite` and the functional equation of ξ suffice. The second imports
> `ZetaLogDeriv.v1` [if the solution takes it as a hypothesis].
>
> A proof of the first from exactly these imports already exists. This needs `ContourIntegration.v1` reactivated; I
> plan to supply a solution for it. The solutions rest on two pinned packages on the core's Mathlib pin (a
> Riemann–Stieltjes library, and one with the rest of the proof), as `docs/ARCHITECTURE.md` allows; the estimates for the digamma function that the proofs
> need (Montgomery–Vaughan Theorem C.5, Lemma 12.14, and a bound uniform on vertical strips) are proved there, so
> neither node imports `GammaAsymptotics.v1`.
>
> One statement deviates in form from the book: MV's hypothesis (12.21), ∫ e^{(1/2+δ₀)2π|x|} |dF(x)| < ∞, cannot be
> written in Mathlib, so (12.20) and (12.21) are stated together as "x ↦ e^{(1/2+δ₀)2π|x|} F(x) is integrable and of
> bounded variation on ℝ", which is equivalent; the solution proves the equivalence.
>
> Unrelated small erratum: the `sources` note in `ZetaHadamard.v1/formalization.yaml` says "Theorem 10.13 is the
> Hadamard product for xi"; in MV the Hadamard product is Theorem 10.12, and Theorem 10.13 is N(T+1) − N(T) ≪ log(T+2).
