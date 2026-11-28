# Partial fractions for ζ'/ζ without the Hadamard product (IEANTN `ZetaHadamard.v1`)

For the `mv-lemma-12-14` chat. Written on 27 November 2026 by Claude (claude.ai, in a sandbox without Lean) for
Harald Helfgott, who chose this route over porting PNT+'s Hadamard factorization of ξ (PNT+ `471f10c`: about 14,300
lines in the closure of `RiemannZetaHadamard.lean`, on Lean v4.36.0 and a newer Mathlib than IEANTN's). Nothing here
has been compiled.

## 0. Target

IEANTN's node `ZetaHadamard.v1` (kind `standard`; it imports nothing; today it rests on a citation, with the
locator Montgomery–Vaughan, Corollary 10.14). Its conclusion, verbatim from `IEANTN/Nodes/ZetaHadamard/v1/Conclusions.lean`
(inside `namespace ZetaHadamard.v1`, with `open IEANTN`):

```lean
noncomputable def logDeriv_partial_fractions : Prop :=
  ∀ s w : ℂ, s ≠ 1 → w ≠ 1 → riemannZeta s ≠ 0 → riemannZeta w ≠ 0 →
    HasSum (fun ρ : zetaZeroesIn (Set.Ioo (0:ℝ) 1) Set.univ ↦
        (1 / (s - (ρ : ℂ)) - 1 / (w - (ρ : ℂ))) * (zetaOrder (ρ : ℂ) : ℂ))
      (deriv riemannZeta s / riemannZeta s - deriv riemannZeta w / riemannZeta w
        + (Complex.digamma (s / 2 + 1) - Complex.digamma (w / 2 + 1)) / 2
        + 1 / (s - 1) - 1 / (w - 1))
```

`zetaZeroesIn` and `zetaOrder` are IEANTN's Vocabulary definitions; `Contour.lean` has verbatim copies. The library
gets `LogDerivPartialFractions : Prop`, a verbatim copy of the body above, and
`theorem logDeriv_partial_fractions : LogDerivPartialFractions`. The node imports nothing, so the proof must be
unconditional; it may use anything in the library.

The paired form never mentions the constant B of the Hadamard product, and neither does the proof below.

## 1. Notation, and what is already there

- `Z = zetaZeroesIn (Ioo 0 1) univ`, the non-trivial zeros; `m(ρ) = zetaOrder ρ`. On `Z`, `m(ρ)` is the order of ξ
  at ρ and is at least 1 (`zeroMult_eq`, `zetaOrder_eq`, `one_le_zetaOrder`). Write ρ = β + iγ and z = σ + it.
- ξ = `riemannXi` (`Xi.lean`): `differentiable_riemannXi`; `riemannXi_one_sub`; `riemannXi_eq_zero_iff`
  (ξ(s) = 0 iff ζ(s) = 0 and 0 < Re s < 1); `analyticOrderAt_riemannXi`; `logDeriv_riemannXi` (for Re s > 0);
  `logDeriv_riemannXi_one_sub`; and for conjugation `riemannZeta_conj`, `logDeriv_riemannZeta_conj`,
  `analyticOrderAt_riemannZeta_conj`.
- Counting: `zetaZeroesSum_le_log` and `exists_zetaZeroesSum_le` (Theorem 10.13: the number of zeros, with
  multiplicity, with γ ∈ [T, T + 1] is ≪ log(T + 2) for T ≥ 0); `sum_zetaOrder_le_of_window`.
- Good heights: `exists_good_height_of`, whose T₁ comes from `exists_far_point`.
- Digamma: `Complex.hasSum_digamma` (Gauss's series, Re s > 0) and `Complex.exists_norm_digamma_le_log` (vertical
  strips).
- Mathlib: `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le` (Cauchy's estimate),
  `Complex.norm_le_of_forall_mem_frontier_norm_le` (maximum modulus on a bounded set),
  `differentiableOn_tsum_of_summable_norm`.

Put

  H(z) = ζ'/ζ(z) + ψ(z/2 + 1)/2 + 1/(z − 1),

so that the value in the target is H(s) − H(w); and, with the base point 2,

  S(z) = Σ_{ρ ∈ Z} m(ρ) (1/(z − ρ) − 1/(2 − ρ))    (z ∉ Z).

## 2. The proof

**A. ξ'/ξ everywhere.** For z ≠ 1 with ζ(z) ≠ 0: ξ(z) ≠ 0, and ξ'/ξ(z) = H(z) − (log π)/2.
For Re z > 0 this is `logDeriv_riemannXi`, with ψ(z/2 + 1) = ψ(z/2) + 2/z. For Re z ≤ 0 one way is the identity
ξ(u) = (u − 1) π^{−u/2} Γ(u/2 + 1) ζ(u) on the connected open set U = ℂ ∖ ({1} ∪ {−2, −4, …}): both sides are
analytic on U and agree for Re u > 0. Then take the logarithmic derivative of the product at z ∈ U. Mathlib's Γ is
0 at its poles, so the product formula is false at the trivial zeros: use it on U only. (The other way, through
`logDeriv_riemannXi_one_sub` and the functional equation of ζ'/ζ, needs more digamma identities.)

**B. Counting.** From Theorem 10.13, with conjugation for γ < 0, by summing over unit windows. What C and F need,
in some form:
- (N1) the number of zeros, with multiplicity, with γ ∈ [t, t + 1] is ≪ log(|t| + 2), for every real t;
- (N2) Σ_ρ m(ρ)/(1 + γ²) < ∞;
- (N3) for X ≥ 2 and |t| ≤ 2X: Σ_{|γ| ≤ 2X, |γ − t| ≥ 1} m(ρ)/|γ − t| ≪ log² X, and
  Σ_{|γ| ≤ 2X} m(ρ)/(1 + |γ|) ≪ log² X;
- (N4) for X ≥ 2: Σ_{|γ| > X} m(ρ)/γ² ≪ (log X)/X.

**C. S.** For z ∉ Z the terms are m(ρ)(2 − z)/((z − ρ)(2 − ρ)). On a compact set K disjoint from Z they are
O_K(m(ρ)/(1 + γ²)), so by (N2) the family is summable, normally on K. Hence S is holomorphic on ℂ ∖ Z, and near
ρ₀ ∈ Z the function S(z) − m(ρ₀)/(z − ρ₀) is holomorphic: drop one term, since Z is discrete.

**D. G is entire.** On ℂ ∖ Z put G = ξ'/ξ − S. At ρ₀ ∈ Z, ξ has a zero of order m(ρ₀), so ξ'/ξ − m(ρ₀)/(z − ρ₀) is
holomorphic near ρ₀, and G has a removable singularity there. Let G̃ be the entire extension.

**E. Symmetry.** Z is invariant under ρ ↦ 1 − ρ and under ρ ↦ ρ̄, with m preserved. Reindexing S(1 − z) by ρ ↦ 1 − ρ
and adding the two sums termwise,

  S(z) + S(1 − z) = −Σ_ρ m(ρ) (1/(2 − ρ) + 1/(1 + ρ)) =: c₁,

absolutely convergent, since 1/(2 − ρ) + 1/(1 + ρ) = 3/((2 − ρ)(1 + ρ)) ≤ 6/(1 + γ²) in absolute value. Since
ξ'/ξ(1 − z) = −ξ'/ξ(z), G̃(z) + G̃(1 − z) = −c₁ for every z.

**F. |G̃(z)| ≪ log²(|z| + 2) everywhere.**
- F1, σ ≥ 2. |ζ'/ζ(z)| ≤ Σ_n Λ(n)/n² (the Dirichlet series of Λ), and |ψ(z/2 + 1)| ≪ log(|z| + 2) (Gauss's series,
  or the strip bound and ψ(u + 1) = ψ(u) + 1/u), so |ξ'/ξ(z)| ≪ log(|z| + 2). For S: every zero satisfies
  |z − ρ| ≥ max(1, |t − γ|). For the zeros with |γ| ≤ 2|z|, bound 1/(z − ρ) and 1/(2 − ρ) separately: (N1) for
  |γ − t| < 1 and (N3) with X = |z| for the rest. For the zeros with |γ| > 2|z|, the term is at most
  4 m(ρ)(|z| + 2)/γ², and (N4) applies.
- F2, σ ≤ −1: from F1 and E.
- F3, segments at good heights. Export from `GoodHeights.lean`, beside `exists_good_height_of` (which stays as it
  is), the margin that its proof already constructs:

      ∃ C c > 0, ∀ T ≥ 2, ∃ T₁ ∈ [T, T + 1], (∀ ρ ∈ Z, c / log T ≤ |T₁ − Im ρ|) ∧
        ∀ σ ∈ [−1, 2], ζ(σ + iT₁) ≠ 0 ∧ ‖ζ'(σ + iT₁)/ζ(σ + iT₁)‖ ≤ C log² T.

  In the proof, |T₁ − γ| ≥ 1/(2(|Z_T| + 1)) for the zeros with γ ∈ [T − 2, T + 3], |T₁ − γ| ≥ 2 for the others,
  and |Z_T| ≪ log T by `sum_zetaOrder_le_of_window`; this is Montgomery–Vaughan's choice of T₁ in their proof of
  Lemma 12.2. State it with `hFE : LogDerivFunctionalEquation` as a hypothesis, as `exists_good_height_of` does, and
  add an unconditional wrapper. Then for z = σ + iT₁ with −1 ≤ σ ≤ 2: |ξ'/ξ(z)| ≪ log² T (the bound on ζ'/ζ, and
  `Complex.exists_norm_digamma_le_log` for 1/2 ≤ Re ≤ 2); and |S(z)| ≪ log² T, because each zero with
  |γ − T₁| ≤ 1 contributes at most m(ρ)(log T)/c + m(ρ)/|2 − ρ|, there are ≪ log T of them by (N1), and the other
  zeros are treated as in F1. At −T₁ the same holds by conjugation.
- F4, the strip −1 ≤ σ ≤ 2, |t| ≥ 3. For integers k ≥ 2 let T₁(k) ∈ [k, k + 1] be the good height of F3. Apply
  the maximum modulus principle on the rectangles [−1, 2] × [T₁(k), T₁(k + 1)]: their boundaries lie on σ = −1 and
  σ = 2 (F1, F2) and on two good-height segments (F3), and together they cover every height t ≥ T₁(2), so every
  t ≥ 3. Negative heights by conjugation.
- F5, the rest: −1 ≤ σ ≤ 2, |t| ≤ 3, is compact.

**G. G̃ is constant.** For every z₀ and R ≥ 1, Cauchy's estimate on the circle |z − z₀| = R gives
|G̃'(z₀)| ≪ log²(|z₀| + R + 2)/R, which tends to 0 as R → ∞. So G̃' = 0 and G̃ is a constant κ.

**H. Conclusion.** Let z ≠ 1 with ζ(z) ≠ 0. Then z ∉ Z, and by A, S(z) = ξ'/ξ(z) − κ = H(z) − (log π)/2 − κ. Since
S(2) = 0, S(z) = H(z) − H(2), with `HasSum`. For admissible s and w, `HasSum.sub` of the families at s and at w
gives `HasSum (fun ρ ↦ m(ρ) (1/(s − ρ) − 1/(w − ρ))) (H(s) − H(w))`. Rearrange the summand to
`(1 / (s - ρ) - 1 / (w - ρ)) * (zetaOrder ρ : ℂ)` and the value to the node's expression.

## 3. Deliverables and rules

1. In `GoodHeights.lean`: the good height with its margin (F3). `exists_good_height_of`, `exists_good_height`,
   `Lemma_12_2` and everything else already exported stay unchanged.
2. A new file `Mathlib/NumberTheory/WeilExplicitFormula/PartialFractions.lean` on `mv-lemma-12-14`, with
   `LogDerivPartialFractions` (verbatim) and `logDeriv_partial_fractions`.
3. No `sorry`, no `native_decide`; axioms only `propext`, `Classical.choice`, `Quot.sound`. Report any change of
   meaning (none should be needed). Push and report the commit.
4. Claude Code then ports the commit to `Garald1/WeilExplicitFormula` and writes the IEANTN solution
   (`blueprint/HANDOFF.md`, Task 8).

Not part of this task: identity (2.4) of the Mertens note, which follows from S by integrating along a horizontal
segment.
