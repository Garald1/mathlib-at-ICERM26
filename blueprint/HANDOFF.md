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

## Coordination (updated 27 November 2026)

Another chat works on the same project.
- **Done there** (branch `mv-lemma-12-14` of `Garald1/mathlib-at-ICERM26`, head `3992e7d7`: five commits on top of
  `dirichlet-jordan` `90f274f8`, with the same Lean and Mathlib as the library; it merges cleanly into
  `weil-explicit-formula`): Part A (the Fourier integral theorem, with the statements of `drafts/FourierIntegral.lean`
  unchanged); Part B (Montgomery–Vaughan Theorem C.5 and Lemma 12.14, both signs); and the uniform digamma bound
  `Complex.exists_norm_digamma_le_log`. That chat reports no `sorry` and no axioms beyond `propext`,
  `Classical.choice`, `Quot.sound`.
- **Proposed next there** (Harald to confirm): E, F and G5 of the blueprint, as library lemmas. It proposes to leave
  C1–C3, D1, G1–G4 and G6 to this laptop (Task 7), since the node's statement uses IEANTN's vocabulary and its sandbox
  cannot build against IEANTN's pin. Where those parts go will be settled once E, F, G5 are done.

So Tasks 3 and 4, and step 1 of Task 2, are done there; do not start Task 7 until Harald says so. Here: Task 1
(which now includes the other chat's new files), Task 2 from step 2 on, and Task 6. Ask Harald before starting
Task 5.

**Decided by Harald (27 November):** the digamma bound uniform on vertical strips (blueprint B3, first statement,
`Complex.exists_norm_digamma_le_log`) is added to the library by the other chat. Neither node draft imports
`GammaAsymptotics.v1` any more, and nobody here writes a solution for it.

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
- `RiemannStieltjes/` — the library, created in Task 1.
- `ieantn/` — Harald's fork `Garald1/ieantn` (use his existing clone if he has one), brought up to date with
  `teorth/IEANTN` `main` before starting.

## Task 1 — the Riemann–Stieltjes library as a standalone Lake package

An IEANTN solution must use the core's Mathlib revision and cannot depend on a fork of Mathlib, so the library has to
become its own package, pinned to IEANTN's Lean and Mathlib.

1. Ask Harald to confirm the repository name (proposed: `Garald1/RiemannStieltjes`, private at first) and create it.
2. Lake package `RiemannStieltjes`: `lean-toolchain` identical to IEANTN's; `require mathlib` at IEANTN's Mathlib
   commit, as a full 40-character hash.
3. What to port. Relative to upstream Mathlib commit `09370b01` (the last upstream merge into the workshop branch,
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

   Then **branch `mv-lemma-12-14`** (the other chat's; `dirichlet-jordan` plus five commits, head `3992e7d7`, so port
   from it) **adds 5 files** (about 3,350 lines):
   `Mathlib/Analysis/SpecialFunctions/Gamma/{DigammaSeries,DigammaFourier}.lean` and
   `Mathlib/Analysis/BoxIntegral/Stieltjes/{VariationBounds,DigammaPairing,FourierIntegral}.lean`. Besides Mathlib,
   they import only each other and the library's own files. The same branch qualifies `Set.Ioc` in
   `Mathlib/Analysis/BoxIntegral/DivergenceTheorem.lean` and `Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean`
   to fix the fork's build: **do not port that.** `Complex.hasSum_digamma` (in `DigammaSeries.lean`) is the Gauss
   series for Re s > 0, proved independently of `GammaSolution.digamma_eq_gaussSum` in IEANTN's
   `Solutions/GammaAsymptotics.v2`: use the library's, and do not copy the IEANTN one into the library. Whatever the
   other chat adds later is ported the same way.

   `Stieltjes/Unused.lean` says of itself that it is not in use: ask Harald before dropping it. Keep every file's
   copyright header and author list as it is.
4. Module names `RiemannStieltjes.<path as in Mathlib>`; keep namespaces and declaration names unchanged, so that the
   library can later go back into Mathlib without renaming.
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
   G), written against the old Mathlib fork. Keep it as a reference for the solution of Task 7; do not compile it now.
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

## Task 5 — a solution for `ContourIntegration.v1`

Needed for D1 and G4 of the proof of 12.13 (not for B4). Only after Harald has agreed its reactivation with the
maintainers, and has said whether the other chat, which does 12.13, will do this too. Port PNT+'s rectangle and residue lemmas
(`ResidueCalcOnRectangles.lean` in `AlexKontorovich/PrimeNumberTheoremAnd`) with credit, or prove directly from
Mathlib's Cauchy theorem on rectangles and its annulus invariance of circle integrals.

## Task 6 — a solution for `ZetaGoodHeights.v1`

Blueprint C4–C7: Jensen's inequality (`AnalyticOnNhd.sum_divisor_le`) on MV's disc for Theorem 10.13; the local
expansion of ζ'/ζ over nearby zeros from `Complex.borelCaratheodory` and `MeromorphicOn.extract_zeros_poles` (MV's
Lemma 6.3 route); a polynomial bound for ζ in σ ≥ 1/8; the pigeonhole choice of T₁; the functional equation of ζ'/ζ
(IEANTN `ZetaLogDeriv.v1`) for −1 ≤ σ < 1/2. **The proofs are written out step by step, with the Mathlib names
checked at the pin, in `blueprint/proofs/GoodHeights.md`; follow it.** The most delicate part of the project.

For −1 ≤ σ < 1/2, Lemma 12.2 needs the digamma bound (D) of `GoodHeights.md`: the library's
`Complex.exists_norm_digamma_le_log` (`Gamma/DigammaSeries.lean`, ported in Task 1), with σ ∈ [1, 5/2]. Do not
write a solution for `GammaAsymptotics.v1` (Appendix A of `GoodHeights.md` is optional, and not for now).

**Stop and report** at the end, and also whenever an approach is abandoned.

## Task 7 — a solution for `WeilExplicitFormula.v1`

**Not before Harald says so (see Coordination).** The other chat proposes that the parts of 12.13 that involve the
zeros (C1–C3, D1, G1–G4, G6) be done here, from the library's A, B, E, F and G5. If so, note that
`drafts/WeilExplicitFormula.lean` (and so, probably, the library's E and F) uses a structure `IsTestFunction` and
writes `rhs` with `(2π)⁻¹ * …` where the node has a conjunction and `… / (2π)`: bridge with a one-line lemma
each; `Phi` has the same body in both.

Blueprint C1–C3, D1, E, F, G, using the library at a pinned commit and the node's imports as hypotheses. Then run
Comparator locally (`scripts/verify-comparator.sh`, as `CONTRIBUTING.md` describes). The official verification
workflow, any pull request, and the Palomar submission (`python scripts/ieantn.py spinoff ...`) are Harald's to
start.

## Reporting

At each stop: what was done; every change of meaning in a statement; what is next; questions. Keep it short; details
go in `STATUS.md` and the commit messages.

## Appendix — draft issue for `teorth/IEANTN` (for Harald to post, edited as he likes)

> **Weil's explicit formula (Montgomery–Vaughan Theorem 12.13, q = 1): two new nodes, a reactivation, a solution**
>
> I would like to add `WeilExplicitFormula.v1` (kind `standard`; MV Theorem 12.13 for q = 1) and
> `ZetaGoodHeights.v1` (kind `standard`; MV Theorem 10.13 and Lemma 12.2, which a contour argument needs to place its
> horizontal sides). The first imports `ZetaZeroes.v1` (`finite_zeroes_on_compact`, `no_nontrivial_zeroes_left`,
> `zeroes_off_axis_in_strip`), `ContourIntegration.v1` and `ZetaGoodHeights.v1`; it does not
> use `ZetaHadamard.v1`, since the planned proofs go through Jensen's inequality and the Borel–Carathéodory lemma
> rather than the Hadamard product. The second imports `ZetaZeroes.v1` (`finite_zeroes_on_compact`) and
> `ZetaLogDeriv.v1`.
>
> This needs `ContourIntegration.v1` reactivated; I plan to supply a solution for it. The solutions would rest on a
> pinned Riemann–Stieltjes library (a standalone package on the core's Mathlib pin), as `docs/ARCHITECTURE.md` allows;
> the estimates for the digamma function that the proofs need (Montgomery–Vaughan Theorem C.5, Lemma 12.14, and a
> bound uniform on vertical strips) are proved there, so neither node imports `GammaAsymptotics.v1`.
>
> One statement deviates in form from the book: MV's hypothesis (12.21), ∫ e^{(1/2+δ₀)2π|x|} |dF(x)| < ∞, cannot be
> written in Mathlib, so (12.20) and (12.21) are stated together as "x ↦ e^{(1/2+δ₀)2π|x|} F(x) is integrable and of
> bounded variation on ℝ", which is equivalent; the solution proves the equivalence.
>
> Unrelated small erratum: the `sources` note in `ZetaHadamard.v1/formalization.yaml` says "Theorem 10.13 is the
> Hadamard product for xi"; in MV the Hadamard product is Theorem 10.12, and Theorem 10.13 is N(T+1) − N(T) ≪ log(T+2).
