# Handoff to Claude Code: Weil's explicit formula (Montgomery–Vaughan Theorem 12.13, q = 1)

Written on 26 November 2026 by Claude (claude.ai, in a sandbox without Lean) for Harald Helfgott, who will run
Claude Code on his laptop. Nothing under `blueprint/` has been compiled.

## What this is

The goal is a Lean proof of Theorem 12.13 of Montgomery–Vaughan (MV), *Multiplicative Number Theory I*, in the case
q = 1, integrated into IEANTN (`teorth/IEANTN`) as a node whose imports are other IEANTN nodes, and from there
registered on Palomar through IEANTN's spin-off tool. The proofs use Harald's Riemann–Stieltjes library (branch
`dirichlet-jordan` of `Garald1/mathlib-at-icerm26`).

Read, in this order, before doing anything:
1. `blueprint/WeilExplicitFormula.md`, all of it. §4 records Harald's decisions; §5 the IEANTN plan.
2. In the IEANTN clone: `CLAUDE.md`, `CONTRIBUTING.md`, `docs/ARCHITECTURE.md`, `docs/NODES.md`, `docs/SOLUTIONS.md`.

## Coordination (added 26 November 2026)

**Another chat is formalizing Montgomery–Vaughan Lemma 12.14 (with Theorem C.5) and Theorem 12.13 itself.** So, until
Harald says otherwise: in Task 2, compile only the IEANTN node drafts, not `FourierIntegral.lean` or
`DigammaFourier.lean`; and do not start Tasks 3, 4 or 7. Tasks 1, 5 and 6 are inputs that the other chat's proof of
12.13 needs, but are not 12.13 or 12.14 themselves; check with Harald before starting 5 or 6 that the other chat is
not doing them too.

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

   `Stieltjes/Unused.lean` says of itself that it is not in use: ask Harald before dropping it. Keep every file's
   copyright header and author list as it is.
4. Module names `RiemannStieltjes.<path as in Mathlib>`; keep namespaces and declaration names unchanged, so that the
   library can later go back into Mathlib without renaming.
5. Port to the newer Mathlib with the smallest changes that work; record each kind of change in `PORTING.md`.
6. `lake build` clean (no `sorry`). Commit, push, update `STATUS.md`.

## Task 2 — compile the draft statements

1. **On hold (see Coordination).** Library: add `blueprint/drafts/FourierIntegral.lean` and
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

**On hold (see Coordination): possibly done in the other chat.**

In the library, prove A1–A6 of the blueprint (`FourierIntegral.lean`) by the route of `DirichletJordan.lean`:
Fejér's theorem for Fourier integrals, Hardy's Tauberian theorem for integrals reduced to the discrete
`tendsto_sum_range_of_tendsto_cesaroMean`, and `FourierTransform.fourier_bounded_variation`. No `sorry` left.
**Stop and report.**

## Task 4 — Part B: the digamma function, Theorem C.5, Lemma 12.14

**On hold (see Coordination): Lemma 12.14 and Theorem C.5 are being done in the other chat.**

In the library. B1 is already proved in IEANTN's `Solutions/GammaAsymptotics.v2/` (`digamma_eq_gaussSum`, for
Re s > 0): reuse it, crediting its authors in the file header. B4 needs a residue theorem on rectangles (Task 5); do
that first, or prove what B4 needs for its specific function. (The solution for the IEANTN node
`GammaAsymptotics.v1` has moved to Task 6, which needs it.) **Stop and report.**

## Task 5 — a solution for `ContourIntegration.v1`

Only after Harald has agreed its reactivation with the maintainers. Port PNT+'s rectangle and residue lemmas
(`ResidueCalcOnRectangles.lean` in `AlexKontorovich/PrimeNumberTheoremAnd`) with credit, or prove directly from
Mathlib's Cauchy theorem on rectangles and its annulus invariance of circle integrals.

## Task 6 — a solution for `ZetaGoodHeights.v1`

Blueprint C4–C7: Jensen's inequality (`AnalyticOnNhd.sum_divisor_le`) on MV's disc for Theorem 10.13; the local
expansion of ζ'/ζ over nearby zeros from `Complex.borelCaratheodory` and `MeromorphicOn.extract_zeros_poles` (MV's
Lemma 6.3 route); a polynomial bound for ζ in σ ≥ 1/8; the pigeonhole choice of T₁; the functional equation of ζ'/ζ
(IEANTN `ZetaLogDeriv.v1`) for −1 ≤ σ < 1/2. **The proofs are written out step by step, with the Mathlib names
checked at the pin, in `blueprint/proofs/GoodHeights.md`; follow it.** The most delicate part of the project.

`lemma_12_2` imports `GammaAsymptotics.v1.digamma_sub_log_isBigO`, which has no solution yet. Appendix A of
`GoodHeights.md` derives it from `digamma_eq_gaussSum` (IEANTN `Solutions/GammaAsymptotics.v2/Analytic.lean`, by
T. Tao; reuse it with credit). Write that as a solution for `GammaAsymptotics.v1` (in
`ieantn/Solutions/GammaAsymptotics.v1/`, following `docs/SOLUTIONS.md` and `CONTRIBUTING.md`), first, unless Harald
says the other chat is doing it.

**Stop and report** at the end, and also whenever an approach is abandoned.

## Task 7 — a solution for `WeilExplicitFormula.v1`

**On hold (see Coordination): Theorem 12.13 is being done in the other chat**, whose proof should end up as this
node's solution (ideally proving the node's statement as drafted, or one that implies it immediately).

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
> `zeroes_off_axis_in_strip`), `ContourIntegration.v1`, `GammaAsymptotics.v1` and `ZetaGoodHeights.v1`; it does not
> use `ZetaHadamard.v1`, since the planned proofs go through Jensen's inequality and the Borel–Carathéodory lemma
> rather than the Hadamard product. The second imports `ZetaZeroes.v1` (`finite_zeroes_on_compact`),
> `ZetaLogDeriv.v1` and `GammaAsymptotics.v1`.
>
> This needs `ContourIntegration.v1` reactivated; I plan to supply solutions for it and for `GammaAsymptotics.v1` (the
> latter from the Gauss series already proved in `Solutions/GammaAsymptotics.v2`). The solutions would rest on a
> pinned Riemann–Stieltjes library (a standalone package on the core's Mathlib pin), as `docs/ARCHITECTURE.md` allows.
>
> One statement deviates in form from the book: MV's hypothesis (12.21), ∫ e^{(1/2+δ₀)2π|x|} |dF(x)| < ∞, cannot be
> written in Mathlib, so (12.20) and (12.21) are stated together as "x ↦ e^{(1/2+δ₀)2π|x|} F(x) is integrable and of
> bounded variation on ℝ", which is equivalent; the solution proves the equivalence.
>
> Unrelated small erratum: the `sources` note in `ZetaHadamard.v1/formalization.yaml` says "Theorem 10.13 is the
> Hadamard product for xi"; in MV the Hadamard product is Theorem 10.12, and Theorem 10.13 is N(T+1) − N(T) ≪ log(T+2).
