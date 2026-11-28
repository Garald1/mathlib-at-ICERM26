/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Harald Helfgott
-/
module

public import Mathlib.NumberTheory.WeilExplicitFormula.GoodHeights
public import Mathlib.NumberTheory.WeilExplicitFormula.Contour
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.PSeries

/-! # The partial-fraction expansion of `ζ'/ζ`, without the Hadamard product

`LogDerivPartialFractions` is the statement of `IEANTN`'s node
`ZetaHadamard.v1.logDeriv_partial_fractions`, verbatim (Montgomery–Vaughan, Corollary 10.14,
taken at two points and subtracted): for `s, w ≠ 1` with `ζ(s), ζ(w) ≠ 0`,
`∑_ρ m(ρ) (1/(s - ρ) - 1/(w - ρ)) = H(s) - H(w)` as a `HasSum` over the non-trivial zeros, where
`H(z) = ζ'/ζ(z) + ψ(z/2 + 1)/2 + 1/(z - 1)` (`zetaH`). `logDeriv_partial_fractions` proves it
unconditionally, without the Hadamard product and without the residue theorem, following
`blueprint/proofs/PartialFractions.md` (branch `weil-explicit-formula`):
* (B) counting: zeros in windows `[t, t + 1]` and annuli `j ≤ |γ - t| < j + 1`, from Theorem 10.13
  (`zetaZeroesSum_le_log`) and conjugation; `∑_ρ m(ρ) (1 + |γ|)^{-3/2} < ∞` (`summable_zeroWeight`);
* (C) `S(z) = ∑_ρ m(ρ) (1/(z - ρ) - 1/(2 - ρ))` (`zeroSum`) converges absolutely off the zeros,
  locally uniformly (`differentiableOn_zeroSumExcept`), and
  `‖S(z)‖ ≪ (1/δ) log (‖z‖ + 4) + log² (‖z‖ + 4) + √(‖z‖ + 2)` if every zero is at distance at
  least `δ ≤ 1` from `z` (`norm_zeroSum_le`);
* (A) `ξ'/ξ(z) = H(z) - (log π)/2` for `z ≠ 1`, `ζ(z) ≠ 0` (`logDeriv_riemannXi_eq_zetaH`), from
  `ξ(u) = (u - 1) π^{-u/2} Γ(u/2 + 1) ζ(u)`;
* (D) `G = ξ'/ξ - S` (`xiRem`) agrees off the zeros with the entire function `xiRemExt`, its limit
  at each point (`exists_local_rep`, from `ξ(z) = (z - ρ)^m g(z)` near each point `ρ`);
* (E) `S(z) + S(1 - z)` is constant, by `ρ ↦ 1 - ρ` (`zeroSum_add_zeroSum_one_sub`), and
  `ξ'/ξ(1 - z) = -ξ'/ξ(z)`, so `G(z) + G(1 - z)` is constant;
* (F) `‖G‖ ≤ A √(3n + 6)` on the boundary of `[-n, n + 1] × [-T₁, T₁]`, where `T₁ ∈ [n, n + 1]`
  is a good height whose distance to the ordinate of every zero is at least `c / log n`
  (`exists_good_height_margin`, in `GoodHeights.lean`): for `Re z ≥ 2` by the Dirichlet series of
  `Λ` and the bound for `ψ`, for `Re z ≤ -1` by (E), and for `-1 ≤ Re z ≤ 2` at the heights `±T₁`
  by the good height and its margin (`exists_norm_xiRemExt_le_frontier`);
* (G) the maximum modulus principle on these rectangles and Cauchy's estimate on the circles
  `|z - z₀| = n/2` give `G'(z₀) = 0` (`deriv_xiRemExt`), so `G` is constant;
* (H) `S(z) = H(z) - H(2)`, since `S(2) = 0` (`zeroSum_eq_zetaH_sub`); subtract at `s` and `w`.

The bound in (F) is `√` rather than the blueprint's `log²`: the zeros with `|γ| > 2(‖z‖ + 2)` are
summed against the weight `(1 + |γ|)^{-3/2}`, which avoids a separate estimate for the tail
`∑_{|γ| > X} m(ρ)/γ²`; any `o(n)` suffices for (G).

## AI usage

This file was written by Claude (Anthropic) in November 2026. It compiles, but has not been
reviewed by a human.
-/

set_option linter.style.longFile 1600

@[expose] public section

open Complex Set Filter Topology Metric
open scoped ComplexConjugate Real

noncomputable section

namespace WeilExplicitFormula

/-- **The partial-fraction expansion of `ζ'/ζ`, in paired form**: the statement of IEANTN's
`ZetaHadamard.v1.logDeriv_partial_fractions`, verbatim. -/
def LogDerivPartialFractions : Prop :=
  ∀ s w : ℂ, s ≠ 1 → w ≠ 1 → riemannZeta s ≠ 0 → riemannZeta w ≠ 0 →
    HasSum (fun ρ : zetaZeroesIn (Set.Ioo (0:ℝ) 1) Set.univ ↦
        (1 / (s - (ρ : ℂ)) - 1 / (w - (ρ : ℂ))) * (zetaOrder (ρ : ℂ) : ℂ))
      (deriv riemannZeta s / riemannZeta s - deriv riemannZeta w / riemannZeta w
        + (Complex.digamma (s / 2 + 1) - Complex.digamma (w / 2 + 1)) / 2
        + 1 / (s - 1) - 1 / (w - 1))

/-- The non-trivial zeros of `ζ`. -/
local notation "𝒵" => zetaZeroesIn (Set.Ioo (0:ℝ) 1) Set.univ

/-! ### The non-trivial zeros -/

theorem mem_ntZeros {ρ : ℂ} : ρ ∈ 𝒵 ↔ (0 < ρ.re ∧ ρ.re < 1) ∧ riemannZeta ρ = 0 := by
  simp only [zetaZeroesIn, zetaZeroes, mem_setOf_eq, mem_Ioo, mem_univ, true_and]

theorem ne_one_of_mem_ntZeros {ρ : ℂ} (h : ρ ∈ 𝒵) : ρ ≠ 1 :=
  ne_one_of_re_lt_one (mem_ntZeros.1 h).1.2

theorem zetaOrder_nonneg_of_mem_ntZeros {ρ : ℂ} (h : ρ ∈ 𝒵) : (0 : ℝ) ≤ zetaOrder ρ :=
  zetaOrder_nonneg (mem_ntZeros.1 h).1.2

theorem conj_mem_ntZeros {ρ : ℂ} (h : ρ ∈ 𝒵) : conj ρ ∈ 𝒵 := by
  obtain ⟨⟨h0, h1⟩, hz⟩ := mem_ntZeros.1 h
  refine mem_ntZeros.2 ⟨⟨by simpa using h0, by simpa using h1⟩, ?_⟩
  rw [riemannZeta_conj (ne_one_of_mem_ntZeros h), hz, map_zero]

theorem zetaOrder_conj_of_mem {ρ : ℂ} (h : ρ ∈ 𝒵) : zetaOrder (conj ρ) = zetaOrder ρ := by
  rw [zetaOrder_eq (ne_one_of_mem_ntZeros (conj_mem_ntZeros h)),
    zetaOrder_eq (ne_one_of_mem_ntZeros h)]
  unfold analyticOrderNatAt
  rw [analyticOrderAt_riemannZeta_conj (ne_one_of_mem_ntZeros h)]

theorem one_sub_mem_ntZeros {ρ : ℂ} (h : ρ ∈ 𝒵) : 1 - ρ ∈ 𝒵 := by
  have hc := conj_mem_ntZeros h
  obtain ⟨⟨h0, h1⟩, hz⟩ := mem_ntZeros.1 hc
  have := (riemannZeta_one_sub_conj_eq_zero_iff h0 h1).2 hz
  rw [Complex.conj_conj] at this
  obtain ⟨⟨h0', h1'⟩, -⟩ := mem_ntZeros.1 h
  exact mem_ntZeros.2 ⟨⟨by simp; linarith, by simp; linarith⟩, this⟩

theorem zetaOrder_one_sub_of_mem {ρ : ℂ} (h : ρ ∈ 𝒵) : zetaOrder (1 - ρ) = zetaOrder ρ := by
  have hc := conj_mem_ntZeros h
  obtain ⟨⟨h0, h1⟩, -⟩ := mem_ntZeros.1 hc
  have := zetaOrder_one_sub_conj h0 h1
  rw [Complex.conj_conj] at this
  rw [this, zetaOrder_conj_of_mem h]

/-! ### Counting zeros in windows and annuli -/

/-- Theorem 10.13 (`zetaZeroesSum_le_log`), for a finite set of zeros. -/
theorem sum_zetaOrder_le_of_im_mem {t : ℝ} (ht : 0 ≤ t) {F : Finset ℂ}
    (hF : ∀ ρ ∈ F, ρ ∈ 𝒵 ∧ ρ.im ∈ Icc t (t + 1)) :
    ∑ ρ ∈ F, (zetaOrder ρ : ℝ) ≤ 20 / Real.log (22 / 21) * Real.log (t + 2) := by
  classical
  have hfin : (zetaZeroesIn (Ioo 0 1) (Icc t (t + 1))).Finite :=
    zetaZeroesIn_finite Ioo_subset_Icc_self subset_rfl
  have h := zetaZeroesSum_le_log ht
  rw [zetaZeroesSum_eq_sum hfin] at h
  simp only [one_mul] at h
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) h
  · intro ρ hρ
    obtain ⟨hZ, hI⟩ := hF ρ hρ
    rw [Set.Finite.mem_toFinset]
    exact ⟨hZ.1, hI, hZ.2.2⟩
  · intro ρ hρ _
    rw [Set.Finite.mem_toFinset] at hρ
    exact zetaOrder_nonneg hρ.1.2

/-- The constant in the counts of zeros in windows of height one. -/
def windowConst : ℝ := 2 * (20 / Real.log (22 / 21))

theorem windowConst_nonneg : 0 ≤ windowConst :=
  mul_nonneg (by norm_num) (div_nonneg (by norm_num) (Real.log_pos (by norm_num)).le)

/-- The zeros with ordinate in a window `[t, t + 1]`, with multiplicity, number at most
`windowConst · log (|t| + 3)`, for every real `t`. -/
theorem sum_zetaOrder_le_window (t : ℝ) {F : Finset ℂ}
    (hF : ∀ ρ ∈ F, ρ ∈ 𝒵 ∧ ρ.im ∈ Icc t (t + 1)) :
    ∑ ρ ∈ F, (zetaOrder ρ : ℝ) ≤ windowConst * Real.log (|t| + 3) := by
  classical
  have hA0 : 0 ≤ 20 / Real.log (22 / 21) := div_nonneg (by norm_num) (Real.log_pos (by norm_num)).le
  rw [← Finset.sum_filter_add_sum_filter_not F (fun ρ ↦ 0 ≤ ρ.im)]
  have h1 : ∑ ρ ∈ F.filter (fun ρ ↦ 0 ≤ ρ.im), (zetaOrder ρ : ℝ) ≤
      20 / Real.log (22 / 21) * Real.log (|t| + 3) := by
    refine (sum_zetaOrder_le_of_im_mem (t := max t 0) (le_max_right _ _) ?_).trans ?_
    · intro ρ hρ
      rw [Finset.mem_filter] at hρ
      obtain ⟨hZ, hlo, hhi⟩ := hF ρ hρ.1
      exact ⟨hZ, max_le hlo hρ.2, by linarith [le_max_left t 0]⟩
    · refine mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) ?_) hA0
      have : max t 0 ≤ |t| := max_le (le_abs_self t) (abs_nonneg t)
      linarith
  have h2 : ∑ ρ ∈ F.filter (fun ρ ↦ ¬ 0 ≤ ρ.im), (zetaOrder ρ : ℝ) ≤
      20 / Real.log (22 / 21) * Real.log (|t| + 3) := by
    set F₂ := F.filter (fun ρ ↦ ¬ 0 ≤ ρ.im) with hF₂
    have hmem : ∀ ρ ∈ F₂, ρ ∈ 𝒵 ∧ ρ.im ∈ Icc t (t + 1) ∧ ρ.im < 0 := by
      intro ρ hρ
      rw [hF₂, Finset.mem_filter] at hρ
      exact ⟨(hF ρ hρ.1).1, (hF ρ hρ.1).2, not_le.1 hρ.2⟩
    have hsum : ∑ ρ ∈ F₂, (zetaOrder ρ : ℝ) = ∑ ρ ∈ F₂.image conj, (zetaOrder ρ : ℝ) := by
      rw [Finset.sum_image fun x _ y _ hxy ↦ by simpa using congrArg conj hxy]
      exact Finset.sum_congr rfl fun ρ hρ ↦ by rw [zetaOrder_conj_of_mem (hmem ρ hρ).1]
    rw [hsum]
    refine (sum_zetaOrder_le_of_im_mem (t := max (-t - 1) 0) (le_max_right _ _) ?_).trans ?_
    · intro σ hσ
      obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.1 hσ
      obtain ⟨hZ, ⟨hlo, hhi⟩, hneg⟩ := hmem ρ hρ
      refine ⟨conj_mem_ntZeros hZ, ?_, ?_⟩
      · rw [Complex.conj_im]
        exact max_le (by linarith) (by linarith)
      · rw [Complex.conj_im]
        linarith [le_max_left (-t - 1) 0]
    · refine mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) ?_) hA0
      have : max (-t - 1) 0 ≤ |t| + 1 := max_le (by linarith [neg_abs_le t]) (by positivity)
      linarith
  have : 20 / Real.log (22 / 21) * Real.log (|t| + 3) +
      20 / Real.log (22 / 21) * Real.log (|t| + 3) = windowConst * Real.log (|t| + 3) := by
    rw [windowConst]
    ring
  linarith

/-- The zeros at distance `j ≤ |γ - t| < j + 1` from the height `t`, with multiplicity, number at
most `2 · windowConst · log (|t| + j + 4)`. -/
theorem sum_zetaOrder_le_annulus (t : ℝ) (j : ℕ) {F : Finset ℂ}
    (hF : ∀ ρ ∈ F, ρ ∈ 𝒵 ∧ ⌊|ρ.im - t|⌋₊ = j) :
    ∑ ρ ∈ F, (zetaOrder ρ : ℝ) ≤ 2 * windowConst * Real.log (|t| + j + 4) := by
  classical
  have hfl : ∀ ρ ∈ F, (j : ℝ) ≤ |ρ.im - t| ∧ |ρ.im - t| < j + 1 := fun ρ hρ ↦ by
    rw [← (hF ρ hρ).2]
    exact ⟨Nat.floor_le (abs_nonneg _), Nat.lt_floor_add_one _⟩
  rw [← Finset.sum_filter_add_sum_filter_not F (fun ρ ↦ t ≤ ρ.im)]
  have hW := windowConst_nonneg
  have h1 : ∑ ρ ∈ F.filter (fun ρ ↦ t ≤ ρ.im), (zetaOrder ρ : ℝ) ≤
      windowConst * Real.log (|t| + j + 4) := by
    refine (sum_zetaOrder_le_window (t + j) ?_).trans ?_
    · intro ρ hρ
      rw [Finset.mem_filter] at hρ
      obtain ⟨hlo, hhi⟩ := hfl ρ hρ.1
      rw [abs_of_nonneg (by linarith [hρ.2])] at hlo hhi
      exact ⟨(hF ρ hρ.1).1, by linarith, by linarith⟩
    · refine mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) ?_) hW
      have := abs_add_le t j
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ j)] at this
      linarith
  have h2 : ∑ ρ ∈ F.filter (fun ρ ↦ ¬ t ≤ ρ.im), (zetaOrder ρ : ℝ) ≤
      windowConst * Real.log (|t| + j + 4) := by
    refine (sum_zetaOrder_le_window (t - j - 1) ?_).trans ?_
    · intro ρ hρ
      rw [Finset.mem_filter] at hρ
      obtain ⟨hlo, hhi⟩ := hfl ρ hρ.1
      rw [abs_of_neg (by linarith [not_le.1 hρ.2])] at hlo hhi
      exact ⟨(hF ρ hρ.1).1, by linarith, by linarith⟩
    · refine mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) ?_) hW
      have := abs_sub (t - j) 1
      have h' := abs_sub t j
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ j)] at h'
      rw [abs_one] at this
      linarith
  linarith

/-- Sums over zeros, by annuli about the height `t`: if `w(ρ) ≤ b(j)` on the annulus
`j ≤ |γ - t| < j + 1`, then `∑ m(ρ) w(ρ) ≤ ∑_j 2 · windowConst · log (|t| + j + 4) · b(j)`. -/
theorem sum_mul_le_of_annuli (t : ℝ) {F : Finset ℂ} (hF : ∀ ρ ∈ F, ρ ∈ 𝒵) (w : ℂ → ℝ)
    (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (hw : ∀ ρ ∈ F, w ρ ≤ b ⌊|ρ.im - t|⌋₊) (J : ℕ)
    (hJ : ∀ ρ ∈ F, ⌊|ρ.im - t|⌋₊ < J) :
    ∑ ρ ∈ F, (zetaOrder ρ : ℝ) * w ρ ≤
      ∑ j ∈ Finset.range J, 2 * windowConst * Real.log (|t| + j + 4) * b j := by
  classical
  calc ∑ ρ ∈ F, (zetaOrder ρ : ℝ) * w ρ
      ≤ ∑ ρ ∈ F, (zetaOrder ρ : ℝ) * b ⌊|ρ.im - t|⌋₊ :=
        Finset.sum_le_sum fun ρ hρ ↦
          mul_le_mul_of_nonneg_left (hw ρ hρ) (zetaOrder_nonneg_of_mem_ntZeros (hF ρ hρ))
    _ = ∑ j ∈ Finset.range J, ∑ ρ ∈ F with ⌊|ρ.im - t|⌋₊ = j,
          (zetaOrder ρ : ℝ) * b ⌊|ρ.im - t|⌋₊ :=
        (Finset.sum_fiberwise_of_maps_to (fun ρ hρ ↦ Finset.mem_range.2 (hJ ρ hρ)) _).symm
    _ = ∑ j ∈ Finset.range J, (∑ ρ ∈ F with ⌊|ρ.im - t|⌋₊ = j, (zetaOrder ρ : ℝ)) * b j := by
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun ρ hρ ↦ by rw [(Finset.mem_filter.1 hρ).2]
    _ ≤ ∑ j ∈ Finset.range J, 2 * windowConst * Real.log (|t| + j + 4) * b j := by
        refine Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_right ?_ (hb j)
        refine sum_zetaOrder_le_annulus t j fun ρ hρ ↦ ?_
        rw [Finset.mem_filter] at hρ
        exact ⟨hF ρ hρ.1, hρ.2⟩

/-! ### Lattice sums -/

theorem inv_max_le (j : ℕ) : 1 / max 1 (j : ℝ) ≤ 2 * (1 / ((j : ℝ) + 1)) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · norm_num
  · have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
    rw [max_eq_right hj1, div_le_iff₀ (by linarith), mul_comm, ← mul_assoc,
      mul_one_div, le_div_iff₀ (by linarith)]
    linarith

/-- `∑_{j < J} 1/max(1, j) ≤ 2 (1 + log J)`. -/
theorem sum_range_inv_max_le (J : ℕ) :
    ∑ j ∈ Finset.range J, 1 / max 1 (j : ℝ) ≤ 2 * (1 + Real.log J) := by
  calc ∑ j ∈ Finset.range J, 1 / max 1 (j : ℝ)
      ≤ ∑ j ∈ Finset.range J, 2 * (1 / ((j : ℝ) + 1)) := Finset.sum_le_sum fun j _ ↦ inv_max_le j
    _ = 2 * (harmonic J : ℝ) := by
        rw [← Finset.mul_sum, harmonic]
        push_cast
        simp [one_div]
    _ ≤ 2 * (1 + Real.log J) := by
        have := harmonic_le_one_add_log J
        linarith

/-- `∑_{j < J} log (a + j + 4)/max(1, j) ≤ 2 log (a + J + 4) (1 + log J)` for `a ≥ 0`. -/
theorem sum_range_log_div_le {a : ℝ} (ha : 0 ≤ a) (J : ℕ) :
    ∑ j ∈ Finset.range J, Real.log (a + j + 4) * (1 / max 1 (j : ℝ)) ≤
      Real.log (a + J + 4) * (2 * (1 + Real.log J)) := by
  calc ∑ j ∈ Finset.range J, Real.log (a + j + 4) * (1 / max 1 (j : ℝ))
      ≤ ∑ j ∈ Finset.range J, Real.log (a + J + 4) * (1 / max 1 (j : ℝ)) := by
        refine Finset.sum_le_sum fun j hj ↦ mul_le_mul_of_nonneg_right
          (Real.log_le_log (by positivity) ?_) (by positivity)
        have : (j : ℝ) ≤ J := by exact_mod_cast (Finset.mem_range.1 hj).le
        linarith
    _ = Real.log (a + J + 4) * ∑ j ∈ Finset.range J, 1 / max 1 (j : ℝ) := by
        rw [Finset.mul_sum]
    _ ≤ Real.log (a + J + 4) * (2 * (1 + Real.log J)) :=
        mul_le_mul_of_nonneg_left (sum_range_inv_max_le J) (Real.log_nonneg (by linarith))

theorem log_mul_rpow_le (j : ℕ) :
    Real.log ((j : ℝ) + 4) * ((j : ℝ) + 1) ^ (-(3 / 2 : ℝ)) ≤
      16 * (((j : ℝ) + 1) ^ (5 / 4 : ℝ))⁻¹ := by
  have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have h1 : Real.log ((j : ℝ) + 4) ≤ ((j : ℝ) + 4) ^ (1 / 4 : ℝ) / (1 / 4) :=
    Real.log_le_rpow_div (by positivity) (by norm_num)
  have h2 : ((j : ℝ) + 4) ^ (1 / 4 : ℝ) ≤ (4 * ((j : ℝ) + 1)) ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
  have h3 : (4 * ((j : ℝ) + 1)) ^ (1 / 4 : ℝ) =
      (4 : ℝ) ^ (1 / 4 : ℝ) * ((j : ℝ) + 1) ^ (1 / 4 : ℝ) :=
    Real.mul_rpow (by norm_num) hj1.le
  have h4 : (4 : ℝ) ^ (1 / 4 : ℝ) ≤ 4 := by
    calc (4 : ℝ) ^ (1 / 4 : ℝ) ≤ (4 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 4 := Real.rpow_one 4
  have h5 : ((j : ℝ) + 1) ^ (1 / 4 : ℝ) * ((j : ℝ) + 1) ^ (-(3 / 2 : ℝ)) =
      (((j : ℝ) + 1) ^ (5 / 4 : ℝ))⁻¹ := by
    rw [← Real.rpow_add hj1, ← Real.rpow_neg hj1.le]
    norm_num
  have hpos : 0 ≤ ((j : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hj1.le _
  have hpos' : 0 ≤ ((j : ℝ) + 1) ^ (1 / 4 : ℝ) := Real.rpow_nonneg hj1.le _
  calc Real.log ((j : ℝ) + 4) * ((j : ℝ) + 1) ^ (-(3 / 2 : ℝ))
      ≤ (4 * (4 * ((j : ℝ) + 1) ^ (1 / 4 : ℝ))) * ((j : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
        refine mul_le_mul_of_nonneg_right ?_ hpos
        rw [div_eq_mul_inv] at h1
        norm_num at h1
        nlinarith
    _ = 16 * (((j : ℝ) + 1) ^ (1 / 4 : ℝ) * ((j : ℝ) + 1) ^ (-(3 / 2 : ℝ))) := by ring
    _ = 16 * (((j : ℝ) + 1) ^ (5 / 4 : ℝ))⁻¹ := by rw [h5]

theorem summable_log_mul_rpow :
    Summable fun j : ℕ ↦ Real.log ((j : ℝ) + 4) * ((j : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
  have hs : Summable fun j : ℕ ↦ (((j : ℝ) + 1) ^ (5 / 4 : ℝ))⁻¹ := by
    have := (summable_nat_add_iff 1).2
      (Real.summable_nat_rpow_inv.2 (by norm_num : (1 : ℝ) < 5 / 4))
    simpa using this
  refine (hs.mul_left 16).of_nonneg_of_le (fun j ↦ ?_) log_mul_rpow_le
  exact mul_nonneg (Real.log_nonneg (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]))
    (Real.rpow_nonneg (by positivity) _)

/-! ### The weight `m(ρ) (1 + |γ|)^{-3/2}` -/

/-- The summable weight `m(ρ) (1 + |γ|)^{-3/2}`. -/
def zeroWeight (ρ : ℂ) : ℝ := (zetaOrder ρ : ℝ) * (1 + |ρ.im|) ^ (-(3 / 2 : ℝ))

theorem zeroWeight_nonneg {ρ : ℂ} (h : ρ ∈ 𝒵) : 0 ≤ zeroWeight ρ :=
  mul_nonneg (zetaOrder_nonneg_of_mem_ntZeros h) (Real.rpow_nonneg (by positivity) _)

theorem sum_zeroWeight_le {F : Finset ℂ} (hF : ∀ ρ ∈ F, ρ ∈ 𝒵) :
    ∑ ρ ∈ F, zeroWeight ρ ≤
      2 * windowConst * ∑' j : ℕ, Real.log ((j : ℝ) + 4) * ((j : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
  classical
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, ∀ ρ ∈ F, ⌊|ρ.im - 0|⌋₊ < J :=
    ⟨F.sup (fun ρ ↦ ⌊|ρ.im - 0|⌋₊) + 1, fun ρ hρ ↦
      Nat.lt_succ_of_le (Finset.le_sup (f := fun ρ ↦ ⌊|ρ.im - 0|⌋₊) hρ)⟩
  have h := sum_mul_le_of_annuli 0 hF (fun ρ ↦ (1 + |ρ.im|) ^ (-(3 / 2 : ℝ)))
    (fun j ↦ ((j : ℝ) + 1) ^ (-(3 / 2 : ℝ))) (fun j ↦ Real.rpow_nonneg (by positivity) _)
    (fun ρ _ ↦ by
      simp only [sub_zero]
      refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by norm_num)
      linarith [Nat.floor_le (abs_nonneg ρ.im)]) J hJ
  simp only [abs_zero, zero_add] at h
  refine le_trans (le_of_eq_of_le (Finset.sum_congr rfl fun ρ _ ↦ rfl) h) ?_
  calc _ = 2 * windowConst * ∑ j ∈ Finset.range J,
          Real.log ((j : ℝ) + 4) * ((j : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ ↦ by ring
    _ ≤ _ := by
      refine mul_le_mul_of_nonneg_left ?_ (by linarith [windowConst_nonneg])
      refine Summable.sum_le_tsum _ (fun j _ ↦ ?_) summable_log_mul_rpow
      exact mul_nonneg (Real.log_nonneg (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]))
        (Real.rpow_nonneg (by positivity) _)

theorem summable_zeroWeight : Summable fun ρ : 𝒵 ↦ zeroWeight ρ := by
  classical
  refine summable_of_sum_le (c := 2 * windowConst *
    ∑' j : ℕ, Real.log ((j : ℝ) + 4) * ((j : ℝ) + 1) ^ (-(3 / 2 : ℝ)))
    (fun ρ ↦ zeroWeight_nonneg ρ.2) fun u ↦ ?_
  have h := sum_zeroWeight_le (F := u.map (Function.Embedding.subtype _))
    (fun ρ hρ ↦ by
      obtain ⟨σ, -, rfl⟩ := Finset.mem_map.1 hρ
      exact σ.2)
  rwa [Finset.sum_map] at h

/-! ### The sum over the zeros -/

theorem one_div_sq_le_rpow {a : ℝ} (ha : 1 ≤ a) : 1 / a ^ 2 ≤ a ^ (-(3 / 2 : ℝ)) := by
  have h : a ^ (-(2 : ℝ)) ≤ a ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le ha (by norm_num)
  rwa [Real.rpow_neg (by linarith), Real.rpow_two, ← one_div] at h

theorem one_le_norm_two_sub {ρ : ℂ} (h : ρ ∈ 𝒵) : 1 ≤ ‖2 - ρ‖ := by
  have h1 := (mem_ntZeros.1 h).1.2
  calc (1 : ℝ) ≤ (2 - ρ).re := by simp only [sub_re, re_ofNat]; linarith
    _ ≤ |(2 - ρ).re| := le_abs_self _
    _ ≤ ‖2 - ρ‖ := Complex.abs_re_le_norm _

theorem abs_im_le_norm_two_sub (ρ : ℂ) : |ρ.im| ≤ ‖2 - ρ‖ := by
  have := Complex.abs_im_le_norm (2 - ρ)
  simpa only [sub_im, im_ofNat, zero_sub, abs_neg] using this

theorem max_le_norm_two_sub {ρ : ℂ} (h : ρ ∈ 𝒵) : max 1 |ρ.im| ≤ ‖2 - ρ‖ :=
  max_le (one_le_norm_two_sub h) (abs_im_le_norm_two_sub ρ)

theorem abs_im_sub_le_norm (z ρ : ℂ) : |ρ.im - z.im| ≤ ‖z - ρ‖ := by
  have := Complex.abs_im_le_norm (z - ρ)
  rwa [sub_im, abs_sub_comm] at this

theorem norm_one_div_le {a : ℂ} {r : ℝ} (hr : 0 < r) (h : r ≤ ‖a‖) : ‖1 / a‖ ≤ 1 / r := by
  rw [norm_div, norm_one]
  exact one_div_le_one_div_of_le hr h

theorem mul_one_add_le {ρ w : ℂ} {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hw : δ ≤ ‖w - ρ‖) :
    δ * (1 + |ρ.im|) ≤ 2 * (‖w‖ + 1) * ‖w - ρ‖ := by
  have h1 : |ρ.im| ≤ ‖w‖ + ‖w - ρ‖ := by
    calc |ρ.im| ≤ ‖ρ‖ := Complex.abs_im_le_norm ρ
      _ = ‖w - (w - ρ)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖w‖ + ‖w - ρ‖ := norm_sub_le _ _
  have hw0 : 0 ≤ ‖w‖ := norm_nonneg _
  have hd0 : 0 ≤ ‖w - ρ‖ := norm_nonneg _
  rcases le_or_gt (2 * ‖w‖ + 1) |ρ.im| with h | h
  · have h2 : 1 + |ρ.im| ≤ 2 * ‖w - ρ‖ := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h2 hδ, mul_le_mul_of_nonneg_right hδ1 hd0]
  · nlinarith [mul_le_mul_of_nonneg_left h.le hδ,
      mul_le_mul_of_nonneg_right hw (by linarith : (0 : ℝ) ≤ ‖w‖ + 1)]

/-- The basic estimate for the terms of `S`. -/
theorem norm_one_div_sub_sub_le {ρ w : ℂ} (hρ : ρ ∈ 𝒵) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hw : δ ≤ ‖w - ρ‖) :
    ‖1 / (w - ρ) - 1 / (2 - ρ)‖ ≤ 4 * (‖w‖ + 2) ^ 2 / δ * (1 + |ρ.im|) ^ (-(3 / 2 : ℝ)) := by
  set a := 1 + |ρ.im| with ha
  have ha1 : 1 ≤ a := by rw [ha]; linarith [abs_nonneg ρ.im]
  have hwρ : w - ρ ≠ 0 := fun h ↦ by rw [h, norm_zero] at hw; linarith
  have h2ρ : (2 : ℂ) - ρ ≠ 0 := fun h ↦ by
    have := one_le_norm_two_sub hρ
    rw [h, norm_zero] at this
    linarith
  have hid : 1 / (w - ρ) - 1 / (2 - ρ) = (2 - w) * (1 / (w - ρ)) * (1 / (2 - ρ)) := by
    field_simp
    ring
  have hw0 : 0 ≤ ‖w‖ := norm_nonneg _
  have e1 : ‖(2 : ℂ) - w‖ ≤ ‖w‖ + 2 := by
    have := norm_sub_le (2 : ℂ) w
    rw [show ‖(2 : ℂ)‖ = 2 by simp] at this
    linarith
  have e2 : ‖1 / (w - ρ)‖ ≤ 2 * (‖w‖ + 1) / (δ * a) := by
    rw [norm_div, norm_one, div_le_div_iff₀ (norm_pos_iff.2 hwρ) (by positivity)]
    have := mul_one_add_le hδ.le hδ1 hw
    rw [← ha] at this
    linarith
  have e3 : ‖1 / (2 - ρ)‖ ≤ 2 / a := by
    rw [norm_div, norm_one, div_le_div_iff₀ (norm_pos_iff.2 h2ρ) (by positivity)]
    have := one_le_norm_two_sub hρ
    have := abs_im_le_norm_two_sub ρ
    rw [ha]
    linarith
  have e4 := one_div_sq_le_rpow ha1
  rw [hid, norm_mul, norm_mul]
  calc ‖(2 : ℂ) - w‖ * ‖1 / (w - ρ)‖ * ‖1 / (2 - ρ)‖
      ≤ (‖w‖ + 2) * (2 * (‖w‖ + 1) / (δ * a)) * (2 / a) := by
        gcongr
    _ = 4 * ((‖w‖ + 2) * (‖w‖ + 1)) / δ * (1 / a ^ 2) := by
        field_simp
        ring
    _ ≤ 4 * (‖w‖ + 2) ^ 2 / δ * a ^ (-(3 / 2 : ℝ)) := by
        gcongr
        nlinarith

/-- The term `m(ρ) (1/(z - ρ) - 1/(2 - ρ))` of `S(z)`. -/
def zeroTerm (z ρ : ℂ) : ℂ := (zetaOrder ρ : ℂ) * (1 / (z - ρ) - 1 / (2 - ρ))

/-- `S(z) = ∑_ρ m(ρ) (1/(z - ρ) - 1/(2 - ρ))`, over the non-trivial zeros. -/
def zeroSum (z : ℂ) : ℂ := ∑' ρ : 𝒵, zeroTerm z ρ

open Classical in
/-- `S` without the term of `z₀`. -/
def zeroSumExcept (z₀ z : ℂ) : ℂ := ∑' ρ : 𝒵, if (ρ : ℂ) = z₀ then 0 else zeroTerm z ρ

theorem norm_zetaOrder_of_mem {ρ : ℂ} (h : ρ ∈ 𝒵) : ‖(zetaOrder ρ : ℂ)‖ = (zetaOrder ρ : ℝ) := by
  rw [Complex.norm_intCast, abs_of_nonneg (zetaOrder_nonneg_of_mem_ntZeros h)]

theorem norm_zeroTerm_le {ρ w : ℂ} (hρ : ρ ∈ 𝒵) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hw : δ ≤ ‖w - ρ‖) : ‖zeroTerm w ρ‖ ≤ 4 * (‖w‖ + 2) ^ 2 / δ * zeroWeight ρ := by
  rw [zeroTerm, norm_mul, norm_zetaOrder_of_mem hρ, zeroWeight]
  calc (zetaOrder ρ : ℝ) * ‖1 / (w - ρ) - 1 / (2 - ρ)‖
      ≤ (zetaOrder ρ : ℝ) * (4 * (‖w‖ + 2) ^ 2 / δ * (1 + |ρ.im|) ^ (-(3 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left (norm_one_div_sub_sub_le hρ hδ hδ1 hw)
          (zetaOrder_nonneg_of_mem_ntZeros hρ)
    _ = _ := by ring

theorem summable_norm_zeroTerm {z : ℂ} {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (h : ∀ ρ ∈ 𝒵, δ ≤ ‖z - ρ‖) : Summable fun ρ : 𝒵 ↦ ‖zeroTerm z ρ‖ :=
  (summable_zeroWeight.mul_left (4 * (‖z‖ + 2) ^ 2 / δ)).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    fun ρ ↦ norm_zeroTerm_le ρ.2 hδ hδ1 (h ρ ρ.2)

/-! ### Isolation of the zeros, and the local factorization of `ξ` -/

theorem mem_ntZeros_iff_riemannXi {z : ℂ} : z ∈ 𝒵 ↔ riemannXi z = 0 := by
  rw [mem_ntZeros, riemannXi_eq_zero_iff]
  tauto

theorem analyticOrderAt_riemannXi_ne_top (z : ℂ) : analyticOrderAt riemannXi z ≠ ⊤ :=
  analyticOrderAt_ne_top_of_ne_zero (U := univ) (fun z _ ↦ differentiable_riemannXi.analyticAt z)
    isPreconnected_univ (mem_univ 0) (by rw [riemannXi_zero]; norm_num) (mem_univ z)

theorem exists_ball_factor_riemannXi (z₀ : ℂ) :
    ∃ ε > 0, ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball z₀ ε) ∧ (∀ s ∈ ball z₀ ε, g s ≠ 0) ∧
      ∀ s ∈ ball z₀ ε, riemannXi s = (s - z₀) ^ analyticOrderNatAt riemannXi z₀ * g s := by
  obtain ⟨ε, hε, g, -, hg, hg0, hfac⟩ := exists_ball_factor
    (differentiable_riemannXi.analyticAt z₀) (analyticOrderAt_riemannXi_ne_top z₀) univ_mem
  exact ⟨ε, hε, g, hg, hg0, hfac⟩

theorem natCast_analyticOrderNatAt_riemannXi_of_mem {ρ : ℂ} (h : ρ ∈ 𝒵) :
    ((analyticOrderNatAt riemannXi ρ : ℕ) : ℂ) = (zetaOrder ρ : ℂ) := by
  obtain ⟨⟨h0, h1⟩, -⟩ := mem_ntZeros.1 h
  have := zeroMult_eq h0 h1
  unfold zeroMult at this
  rw [zetaOrder_eq (ne_one_of_re_lt_one h1), this]
  push_cast
  rfl

theorem analyticOrderNatAt_riemannXi_of_not_mem {z : ℂ} (h : z ∉ 𝒵) :
    analyticOrderNatAt riemannXi z = 0 := by
  have hz : riemannXi z ≠ 0 := fun h' ↦ h (mem_ntZeros_iff_riemannXi.2 h')
  unfold analyticOrderNatAt
  rw [(differentiable_riemannXi.analyticAt z).analyticOrderAt_eq_zero.2 hz]
  rfl

theorem not_mem_of_mem_ball {z₀ : ℂ} {ε : ℝ} {g : ℂ → ℂ} (hg0 : ∀ s ∈ ball z₀ ε, g s ≠ 0)
    (hfac : ∀ s ∈ ball z₀ ε, riemannXi s = (s - z₀) ^ analyticOrderNatAt riemannXi z₀ * g s)
    {w : ℂ} (hw : w ∈ ball z₀ ε) (hwz : w ≠ z₀) : w ∉ 𝒵 := by
  rw [mem_ntZeros_iff_riemannXi, hfac w hw]
  exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.2 hwz)) (hg0 w hw)

/-- Away from the zeros, `S` converges absolutely: the zeros keep a positive distance. -/
theorem exists_le_norm_sub_of_not_mem {z : ℂ} (hz : z ∉ 𝒵) :
    ∃ δ > 0, δ ≤ 1 ∧ ∀ ρ ∈ 𝒵, δ ≤ ‖z - ρ‖ := by
  obtain ⟨ε, hε, g, -, hg0, hfac⟩ := exists_ball_factor_riemannXi z
  refine ⟨min ε 1, lt_min hε one_pos, min_le_right _ _, fun ρ hρ ↦ ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  have hρb : ρ ∈ ball z ε := by
    rw [mem_ball, dist_eq_norm, norm_sub_rev]
    exact hlt.trans_le (min_le_left _ _)
  exact not_mem_of_mem_ball hg0 hfac hρb (fun h ↦ hz (h ▸ hρ)) hρ

theorem summable_zeroTerm {z : ℂ} (hz : z ∉ 𝒵) : Summable fun ρ : 𝒵 ↦ zeroTerm z ρ := by
  obtain ⟨δ, hδ, hδ1, h⟩ := exists_le_norm_sub_of_not_mem hz
  exact (summable_norm_zeroTerm hδ hδ1 h).of_norm

theorem hasSum_zeroSum {z : ℂ} (hz : z ∉ 𝒵) : HasSum (fun ρ : 𝒵 ↦ zeroTerm z ρ) (zeroSum z) :=
  (summable_zeroTerm hz).hasSum

theorem differentiableOn_zeroSumExcept {z₀ : ℂ} {ε : ℝ} (hε : 0 < ε)
    (hiso : ∀ w ∈ ball z₀ ε, w ≠ z₀ → w ∉ 𝒵) :
    DifferentiableOn ℂ (zeroSumExcept z₀) (ball z₀ (min (ε / 2) 1)) := by
  classical
  set δ := min (ε / 2) 1 with hδdef
  have hδ : 0 < δ := lt_min (by linarith) one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδε : δ ≤ ε / 2 := min_le_left _ _
  have hfar : ∀ ρ ∈ 𝒵, ρ ≠ z₀ → ε ≤ ‖ρ - z₀‖ := by
    intro ρ hρ hne
    by_contra h
    exact hiso ρ (by rw [mem_ball, dist_eq_norm]; linarith) hne hρ
  have hnear : ∀ ρ ∈ 𝒵, ρ ≠ z₀ → ∀ w ∈ ball z₀ δ, δ ≤ ‖w - ρ‖ := by
    intro ρ hρ hne w hw
    rw [mem_ball, dist_eq_norm] at hw
    have h1 := hfar ρ hρ hne
    have h2 : ‖ρ - z₀‖ ≤ ‖w - ρ‖ + ‖w - z₀‖ := by
      calc ‖ρ - z₀‖ = ‖(w - z₀) - (w - ρ)‖ := by ring_nf
        _ ≤ ‖w - z₀‖ + ‖w - ρ‖ := norm_sub_le _ _
        _ = ‖w - ρ‖ + ‖w - z₀‖ := add_comm _ _
    linarith
  have hsimp : zeroSumExcept z₀ = fun w ↦
      ∑' ρ : 𝒵, if (ρ : ℂ) = z₀ then 0 else zeroTerm w ρ := by
    funext w
    rw [zeroSumExcept]
  rw [hsimp]
  refine differentiableOn_tsum_of_summable_norm
    (u := fun ρ : 𝒵 ↦ 4 * (‖z₀‖ + 3) ^ 2 / δ * zeroWeight ρ)
    (summable_zeroWeight.mul_left _) (fun ρ ↦ ?_) isOpen_ball (fun ρ w hw ↦ ?_)
  · by_cases hρ : (ρ : ℂ) = z₀
    · simp only [hρ, if_true]
      exact differentiableOn_const _
    · simp only [hρ, if_false]
      intro w hw
      have hwρ : w - ρ ≠ 0 := fun h ↦ by
        have := hnear ρ ρ.2 hρ w hw
        rw [h, norm_zero] at this
        linarith
      have h1 : DifferentiableAt ℂ (fun u : ℂ ↦ 1 / (u - ρ)) w :=
        (differentiableAt_const (1 : ℂ)).div (differentiableAt_id.sub_const (ρ : ℂ)) hwρ
      have h2 : DifferentiableAt ℂ (fun u : ℂ ↦ zeroTerm u ρ) w :=
        (h1.sub_const _).const_mul _
      exact h2.differentiableWithinAt
  · have hu : 0 ≤ 4 * (‖z₀‖ + 3) ^ 2 / δ * zeroWeight ρ :=
      mul_nonneg (by positivity) (zeroWeight_nonneg ρ.2)
    by_cases hρ : (ρ : ℂ) = z₀
    · rw [if_pos hρ, norm_zero]
      exact hu
    · rw [if_neg hρ]
      refine (norm_zeroTerm_le ρ.2 hδ hδ1 (hnear ρ ρ.2 hρ w hw)).trans
        (mul_le_mul_of_nonneg_right ?_ (zeroWeight_nonneg ρ.2))
      rw [mem_ball, dist_eq_norm] at hw
      have := norm_le_norm_add_norm_sub' w z₀
      have h3 : ‖w‖ + 2 ≤ ‖z₀‖ + 3 := by linarith
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) h3 2) (by norm_num)) hδ.le

/-! ### `ξ'/ξ - S` extends to an entire function -/

/-- `G = ξ'/ξ - S`. -/
def xiRem (z : ℂ) : ℂ := logDeriv riemannXi z - zeroSum z

open Classical in
theorem zeroSum_eq_zeroSumExcept_add {z₀ w : ℂ} (hw : w ∉ 𝒵) :
    zeroSum w = zeroSumExcept z₀ w + if z₀ ∈ 𝒵 then zeroTerm w z₀ else 0 := by
  classical
  split_ifs with hz₀
  · rw [zeroSum, (summable_zeroTerm hw).tsum_eq_add_tsum_ite ⟨z₀, hz₀⟩, add_comm, zeroSumExcept]
    congr 1
    refine tsum_congr fun ρ ↦ ?_
    by_cases h : (ρ : ℂ) = z₀
    · have h' : ρ = ⟨z₀, hz₀⟩ := Subtype.ext h
      simp [h']
    · have h' : ρ ≠ ⟨z₀, hz₀⟩ := fun h' ↦ h (by rw [h'])
      simp [h, h']
  · rw [add_zero, zeroSum, zeroSumExcept]
    refine tsum_congr fun ρ ↦ ?_
    rw [if_neg (show ¬((ρ : ℂ) = z₀) from fun h ↦ hz₀ (h ▸ ρ.2))]

/-- Near every point, `ξ'/ξ - S` agrees off the zeros with a holomorphic function. -/
theorem exists_local_rep (z₀ : ℂ) : ∃ ε > 0, ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (ball z₀ ε) ∧
    (∀ w ∈ ball z₀ ε, w ≠ z₀ → w ∉ 𝒵) ∧ ∀ w ∈ ball z₀ ε, w ∉ 𝒵 → xiRem w = h w := by
  obtain ⟨ε, hε, g, hg, hg0, hfac⟩ := exists_ball_factor_riemannXi z₀
  have hiso : ∀ w ∈ ball z₀ ε, w ≠ z₀ → w ∉ 𝒵 := fun w hw hne ↦
    not_mem_of_mem_ball hg0 hfac hw hne
  set m := analyticOrderNatAt riemannXi z₀ with hm
  set δ := min (ε / 2) 1 with hδdef
  have hδ : 0 < δ := lt_min (by linarith) one_pos
  have hδε : δ ≤ ε := (min_le_left _ _).trans (by linarith)
  refine ⟨δ, hδ, fun w ↦ logDeriv g w - zeroSumExcept z₀ w + (m : ℂ) / (2 - z₀), ?_,
    fun w hw hne ↦ hiso w (ball_subset_ball hδε hw) hne, ?_⟩
  · have h1 : DifferentiableOn ℂ (logDeriv g) (ball z₀ δ) := by
      have : DifferentiableOn ℂ (fun s ↦ deriv g s / g s) (ball z₀ ε) :=
        (hg.deriv isOpen_ball).div hg hg0
      exact this.mono (ball_subset_ball hδε)
    exact (h1.sub (differentiableOn_zeroSumExcept hε hiso)).add_const _
  · intro w hw hwZ
    have hwε := ball_subset_ball hδε hw
    have hgw : DifferentiableAt ℂ g w := hg.differentiableAt (isOpen_ball.mem_nhds hwε)
    have hev : riemannXi =ᶠ[𝓝 w] fun u ↦ (u - z₀) ^ m * g u :=
      Filter.eventually_of_mem (isOpen_ball.mem_nhds hwε) hfac
    have hl : logDeriv riemannXi w = logDeriv (fun u ↦ (u - z₀) ^ m * g u) w := by
      rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
    have hlog : logDeriv riemannXi w = (m : ℂ) / (w - z₀) + logDeriv g w := by
      rcases Nat.eq_zero_or_pos m with hm0 | hm0
      · rw [hl, hm0]
        simp only [pow_zero, one_mul, Nat.cast_zero, zero_div, zero_add]
      · have hwz : w ≠ z₀ := by
          rintro rfl
          apply hwZ
          rw [mem_ntZeros_iff_riemannXi, hfac w (mem_ball_self hε), sub_self,
            zero_pow hm0.ne', zero_mul]
        rw [hl, logDeriv_mul (f := fun u ↦ (u - z₀) ^ m) (g := g) w
          (pow_ne_zero m (sub_ne_zero.2 hwz)) (hg0 w hwε) (by fun_prop) hgw,
          logDeriv_fun_pow (f := fun u : ℂ ↦ u - z₀) (x := w) (by fun_prop) m,
          logDeriv_sub_const]
        ring
    classical
    rw [xiRem, hlog, zeroSum_eq_zeroSumExcept_add (z₀ := z₀) hwZ]
    split_ifs with hz₀
    · rw [zeroTerm, ← natCast_analyticOrderNatAt_riemannXi_of_mem hz₀, ← hm]
      ring
    · rw [show m = 0 from analyticOrderNatAt_riemannXi_of_not_mem hz₀]
      simp

/-- The entire extension of `G = ξ'/ξ - S`. -/
def xiRemExt (z : ℂ) : ℂ := limUnder (𝓝[≠] z) xiRem

theorem xiRemExt_eq_of_local {z₀ : ℂ} {ε : ℝ} {h : ℂ → ℂ}
    (hh : DifferentiableOn ℂ h (ball z₀ ε)) (hiso : ∀ w ∈ ball z₀ ε, w ≠ z₀ → w ∉ 𝒵)
    (heq : ∀ w ∈ ball z₀ ε, w ∉ 𝒵 → xiRem w = h w) {z : ℂ} (hz : z ∈ ball z₀ ε) :
    xiRemExt z = h z := by
  apply Tendsto.limUnder_eq
  have hc : ContinuousAt h z := (hh.differentiableAt (isOpen_ball.mem_nhds hz)).continuousAt
  refine (hc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  have hmem : ball z₀ ε \ {z₀} ∈ 𝓝[≠] z := by
    by_cases hzz : z = z₀
    · subst hzz
      exact diff_mem_nhdsWithin_compl (isOpen_ball.mem_nhds hz) _
    · exact mem_nhdsWithin_of_mem_nhds
        ((isOpen_ball.sdiff isClosed_singleton).mem_nhds ⟨hz, hzz⟩)
  filter_upwards [hmem] with w hw
  exact (heq w hw.1 (hiso w hw.1 hw.2)).symm

theorem differentiable_xiRemExt : Differentiable ℂ xiRemExt := by
  intro z₀
  obtain ⟨ε, hε, h, hh, hiso, heq⟩ := exists_local_rep z₀
  have hev : xiRemExt =ᶠ[𝓝 z₀] h :=
    Filter.eventually_of_mem (isOpen_ball.mem_nhds (mem_ball_self hε))
      fun z hz ↦ xiRemExt_eq_of_local hh hiso heq hz
  exact (hh.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hε))).congr_of_eventuallyEq hev

theorem xiRemExt_eq {z : ℂ} (hz : z ∉ 𝒵) : xiRemExt z = xiRem z := by
  obtain ⟨ε, hε, h, hh, hiso, heq⟩ := exists_local_rep z
  rw [xiRemExt_eq_of_local hh hiso heq (mem_ball_self hε), heq z (mem_ball_self hε) hz]

/-! ### The symmetry `ρ ↦ 1 - ρ` -/

/-- `ρ ↦ 1 - ρ` on the non-trivial zeros. -/
def oneSubEquiv : 𝒵 ≃ 𝒵 where
  toFun ρ := ⟨1 - ρ, one_sub_mem_ntZeros ρ.2⟩
  invFun ρ := ⟨1 - ρ, one_sub_mem_ntZeros ρ.2⟩
  left_inv ρ := by ext; simp
  right_inv ρ := by ext; simp

/-- The constant `c₁ = -∑_ρ m(ρ) (1/(2 - ρ) + 1/(1 + ρ))` of `S(z) + S(1 - z) = c₁`. -/
def symmConst : ℂ := ∑' ρ : 𝒵, (zetaOrder (ρ : ℂ) : ℂ) * (-(1 / (2 - (ρ : ℂ))) - 1 / (1 + ρ))

theorem zeroSum_add_zeroSum_one_sub {z : ℂ} (hz : z ∉ 𝒵) :
    zeroSum z + zeroSum (1 - z) = symmConst := by
  have hz' : 1 - z ∉ 𝒵 := fun h ↦ hz (by simpa using one_sub_mem_ntZeros h)
  have h1 : zeroSum (1 - z) = ∑' ρ : 𝒵, zeroTerm (1 - z) (oneSubEquiv ρ) :=
    (oneSubEquiv.tsum_eq (fun ρ : 𝒵 ↦ zeroTerm (1 - z) ρ)).symm
  have hs : Summable fun ρ : 𝒵 ↦ zeroTerm (1 - z) (oneSubEquiv ρ) :=
    oneSubEquiv.summable_iff.2 (summable_zeroTerm hz')
  rw [h1, zeroSum, ← (summable_zeroTerm hz).tsum_add hs, symmConst]
  refine tsum_congr fun ρ ↦ ?_
  have hρ := ρ.2
  simp only [zeroTerm, oneSubEquiv, Equiv.coe_fn_mk]
  rw [zetaOrder_one_sub_of_mem hρ]
  have e1 : (1 : ℂ) - z - (1 - ρ) = -(z - ρ) := by ring
  have e2 : (2 : ℂ) - (1 - ρ) = 1 + ρ := by ring
  rw [e1, e2, div_neg]
  ring

theorem xiRem_add_xiRem_one_sub {z : ℂ} (hz : z ∉ 𝒵) : xiRem z + xiRem (1 - z) = -symmConst := by
  rw [xiRem, xiRem, logDeriv_riemannXi_one_sub, ← zeroSum_add_zeroSum_one_sub hz]
  ring

/-! ### `ξ'/ξ` in terms of `ζ'/ζ` -/

/-- `H(z) = ζ'/ζ(z) + ψ(z/2 + 1)/2 + 1/(z - 1)`; the value in the target is `H(s) - H(w)`. -/
def zetaH (z : ℂ) : ℂ :=
  deriv riemannZeta z / riemannZeta z + digamma (z / 2 + 1) / 2 + 1 / (z - 1)

/-- `ξ(u) = (u - 1) π^{-u/2} Γ(u/2 + 1) ζ(u)`, away from `1` and the zeros of `ζ`. -/
theorem riemannXi_eq_Gamma_add_one {u : ℂ} (hu1 : u ≠ 1) (hu : riemannZeta u ≠ 0) :
    riemannXi u = (u - 1) * (π : ℂ) ^ (-u / 2) * Complex.Gamma (u / 2 + 1) * riemannZeta u := by
  rcases eq_or_ne u 0 with rfl | hu0
  · rw [riemannXi_zero, riemannZeta_zero]
    simp only [zero_sub, neg_zero, zero_div, cpow_zero, zero_add, Complex.Gamma_one]
    norm_num
  have hΓ : Gammaℝ u ≠ 0 := by
    intro h
    obtain ⟨n, hn⟩ := Gammaℝ_eq_zero_iff.1 h
    rcases n with _ | n
    · exact hu0 (by simpa using hn)
    · apply hu
      rw [hn]
      have := riemannZeta_neg_two_mul_nat_add_one n
      convert this using 2
      push_cast
      ring
  have hΛ : completedRiemannZeta u = Gammaℝ u * riemannZeta u := by
    rw [riemannZeta_def_of_ne_zero hu0]
    field_simp
  rw [riemannXi_eq_completed hu0 hu1, hΛ, Gammaℝ_def,
    Complex.Gamma_add_one _ (div_ne_zero hu0 two_ne_zero)]
  ring

/-- **Step A**: `ξ'/ξ(z) = H(z) - (log π)/2` for `z ≠ 1` with `ζ(z) ≠ 0`. -/
theorem logDeriv_riemannXi_eq_zetaH {z : ℂ} (hz1 : z ≠ 1) (hz : riemannZeta z ≠ 0) :
    logDeriv riemannXi z = zetaH z - Real.log π / 2 := by
  have hev : riemannXi =ᶠ[𝓝 z] fun u ↦
      (u - 1) * (π : ℂ) ^ (-u / 2) * Complex.Gamma (u / 2 + 1) * riemannZeta u := by
    filter_upwards [isOpen_ne.mem_nhds hz1,
      (differentiableAt_riemannZeta hz1).continuousAt.eventually_ne hz] with u hu1 hu
    exact riemannXi_eq_Gamma_add_one hu1 hu
  have hG : ∀ m : ℕ, z / 2 + 1 ≠ -m := by
    intro m hm
    apply hz
    have : z = -2 * ((m : ℂ) + 1) := by linear_combination 2 * hm
    rw [this]
    exact riemannZeta_neg_two_mul_nat_add_one m
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have hd1 : HasDerivAt (fun u : ℂ ↦ (π : ℂ) ^ (-u / 2))
      ((π : ℂ) ^ (-z / 2) * Complex.log π * (-1 / 2)) z := by
    have : HasDerivAt (fun u : ℂ ↦ -u / 2) (-1 / 2) z := by
      simpa using ((hasDerivAt_id' z).neg.div_const 2)
    exact this.const_cpow (Or.inl hπ)
  have hc0 : (π : ℂ) ^ (-z / 2) ≠ 0 := cpow_ne_zero_iff.2 (Or.inl hπ)
  have hΓd : DifferentiableAt ℂ (fun u : ℂ ↦ Complex.Gamma (u / 2 + 1)) z :=
    (differentiableAt_Gamma _ hG).comp z (f := fun u : ℂ ↦ u / 2 + 1) (by fun_prop)
  have hΓ0 : Complex.Gamma (z / 2 + 1) ≠ 0 := Complex.Gamma_ne_zero hG
  have hs1 : z - 1 ≠ 0 := sub_ne_zero.2 hz1
  have hd2 : DifferentiableAt ℂ (fun u : ℂ ↦ (u - 1) * (π : ℂ) ^ (-u / 2)) z :=
    (by fun_prop : DifferentiableAt ℂ (fun u : ℂ ↦ u - 1) z).mul hd1.differentiableAt
  have hlog : logDeriv riemannXi z = logDeriv (fun u ↦
      (u - 1) * (π : ℂ) ^ (-u / 2) * Complex.Gamma (u / 2 + 1) * riemannZeta u) z := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  rw [hlog, logDeriv_mul (f := fun u ↦ (u - 1) * (π : ℂ) ^ (-u / 2) * Complex.Gamma (u / 2 + 1))
      z (mul_ne_zero (mul_ne_zero hs1 hc0) hΓ0) hz (hd2.mul hΓd) (differentiableAt_riemannZeta hz1),
    logDeriv_mul (f := fun u ↦ (u - 1) * (π : ℂ) ^ (-u / 2)) z (mul_ne_zero hs1 hc0) hΓ0 hd2 hΓd,
    logDeriv_mul (f := fun u : ℂ ↦ u - 1) z hs1 hc0 (by fun_prop) hd1.differentiableAt]
  have e1 : logDeriv (fun u : ℂ ↦ u - 1) z = 1 / (z - 1) := logDeriv_sub_const 1 z
  have e2 : logDeriv (fun u : ℂ ↦ (π : ℂ) ^ (-u / 2)) z = -(Real.log π / 2) := by
    rw [logDeriv_apply, hd1.deriv, ← ofReal_log Real.pi_pos.le]
    field_simp
  have e3 : logDeriv (fun u : ℂ ↦ Complex.Gamma (u / 2 + 1)) z = digamma (z / 2 + 1) / 2 := by
    have h3 := logDeriv_comp (f := Complex.Gamma) (g := fun u : ℂ ↦ u / 2 + 1) (x := z)
      (differentiableAt_Gamma _ hG) (by fun_prop)
    have h4 : deriv (fun u : ℂ ↦ u / 2 + 1) z = 1 / 2 := by
      have : HasDerivAt (fun u : ℂ ↦ u / 2 + 1) (1 / 2) z := by
        simpa using ((hasDerivAt_id' z).div_const 2).add_const 1
      exact this.deriv
    have h5 : (Complex.Gamma ∘ fun u : ℂ ↦ u / 2 + 1) = fun u ↦ Complex.Gamma (u / 2 + 1) := rfl
    rw [h5] at h3
    rw [h3, h4, ← digamma_def]
    ring
  rw [e1, e2, e3, zetaH, logDeriv_apply]
  ring

theorem riemannXi_ne_zero_of_riemannZeta_ne_zero {z : ℂ} (hz : riemannZeta z ≠ 0) :
    z ∉ 𝒵 := fun h ↦ hz (mem_ntZeros.1 h).2

/-! ### Bounds for `ζ'/ζ`, `ψ` and logarithms -/

/-- `∑ Λ(n)/n²`, a bound for `ζ'/ζ` on `Re s ≥ 2`. -/
def vonMangoldtSumTwo : ℝ :=
  ∑' n : ℕ, ‖LSeries.term (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) 2 n‖

theorem vonMangoldtSumTwo_nonneg : 0 ≤ vonMangoldtSumTwo := tsum_nonneg fun _ ↦ norm_nonneg _

theorem norm_logDeriv_riemannZeta_le_of_two_le_re {z : ℂ} (hz : 2 ≤ z.re) :
    ‖deriv riemannZeta z / riemannZeta z‖ ≤ vonMangoldtSumTwo := by
  set f : ℕ → ℂ := fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ) with hf
  have h := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (s := z) (by linarith)
  have hs2 : Summable fun n ↦ ‖LSeries.term f 2 n‖ :=
    summable_norm_iff.2 (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := 2) (by norm_num))
  have hle : ∀ n, ‖LSeries.term f z n‖ ≤ ‖LSeries.term f 2 n‖ :=
    LSeries.norm_term_le_of_re_le_re f (by simpa using hz)
  have hsz : Summable fun n ↦ ‖LSeries.term f z n‖ :=
    hs2.of_nonneg_of_le (fun n ↦ norm_nonneg _) hle
  calc ‖deriv riemannZeta z / riemannZeta z‖ = ‖LSeries f z‖ := by
        rw [h, neg_div, norm_neg]
    _ ≤ ∑' n, ‖LSeries.term f z n‖ := norm_tsum_le_tsum_norm hsz
    _ ≤ vonMangoldtSumTwo := hsz.tsum_le_tsum hle hs2

theorem norm_digamma_ofReal_le {a : ℝ} (ha : 1 ≤ a) : ‖digamma (a : ℂ)‖ ≤ Real.log a + 1 := by
  rw [Complex.digamma_ofReal (by linarith), Complex.norm_real, Real.norm_eq_abs]
  have hup := Real.digamma_le_log (by linarith : (0 : ℝ) < a)
  have hlow : 0 ≤ deriv Real.Gamma a / Real.Gamma a + Real.eulerMascheroniConstant := by
    refine (Real.hasSum_digamma (by linarith : (0 : ℝ) < a)).nonneg fun k ↦ ?_
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    rw [sub_nonneg]
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hγ := Real.eulerMascheroniConstant_lt_two_thirds
  have hlog : 0 ≤ Real.log a := Real.log_nonneg ha
  rw [abs_le]
  constructor <;> linarith

theorem norm_digamma_le_of_one_le_re {w : ℂ} (hw : 1 ≤ w.re) :
    ‖digamma w‖ ≤ Real.log w.re + 1 + 4 * Real.log (1 + |w.im|) := by
  have h := Complex.norm_digamma_sub_le (a := w.re) (by linarith) w.im
  rw [min_eq_right hw, Complex.re_add_im] at h
  have h4 : (2 : ℝ) * (1 / 1 ^ 2 + 1 / 1) = 4 := by norm_num
  rw [h4] at h
  have h1 := norm_digamma_ofReal_le hw
  have h2 : ‖digamma w‖ ≤ ‖digamma (w.re : ℂ)‖ + ‖digamma w - digamma (w.re : ℂ)‖ := by
    have := norm_add_le (digamma (w.re : ℂ)) (digamma w - digamma (w.re : ℂ))
    rwa [add_sub_cancel] at this
  linarith

theorem one_lt_log_four : 1 < Real.log 4 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

theorem norm_log_pi_div_two_le : ‖((Real.log π : ℝ) : ℂ) / 2‖ ≤ 1 := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, show ‖(2 : ℂ)‖ = 2 by simp]
  have h0 : 0 ≤ Real.log π := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have h1 : Real.log π ≤ Real.log 4 := Real.log_le_log Real.pi_pos Real.pi_le_four
  have h2 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have h3 := Real.log_two_lt_d9
  rw [abs_of_nonneg h0]
  linarith

theorem log_le_two_mul_sqrt {y : ℝ} (hy : 0 ≤ y) : Real.log y ≤ 2 * Real.sqrt y := by
  have h := Real.log_le_rpow_div hy (by norm_num : (0 : ℝ) < 1 / 2)
  rw [← Real.sqrt_eq_rpow] at h
  linarith

theorem log_sq_le_sixteen_mul_sqrt {y : ℝ} (hy : 1 ≤ y) :
    Real.log y ^ 2 ≤ 16 * Real.sqrt y := by
  have h := Real.log_le_rpow_div (by linarith : (0 : ℝ) ≤ y) (by norm_num : (0 : ℝ) < 1 / 4)
  have h0 : 0 ≤ Real.log y := Real.log_nonneg hy
  have h4 : (y ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt y := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith), Real.sqrt_eq_rpow]
    norm_num
  calc Real.log y ^ 2 ≤ (y ^ (1 / 4 : ℝ) / (1 / 4)) ^ 2 := pow_le_pow_left₀ h0 h 2
    _ = 16 * (y ^ (1 / 4 : ℝ)) ^ 2 := by ring
    _ = 16 * Real.sqrt y := by rw [h4]

/-! ### The bound for `S` -/

theorem rpow_neg_three_halves_eq {a : ℝ} (ha : 0 < a) :
    a ^ (-(3 / 2 : ℝ)) = 1 / (a * Real.sqrt a) := by
  rw [Real.rpow_neg ha.le, Real.sqrt_eq_rpow, ← Real.rpow_one_add' ha.le (by norm_num), one_div]
  norm_num

/-- The zeros far above `z`: `|γ| > 2 (‖z‖ + 2)`. -/
theorem norm_zeroTerm_le_far {z ρ : ℂ} (hρ : ρ ∈ 𝒵) (hfar : 2 * (‖z‖ + 2) < |ρ.im|) :
    ‖zeroTerm z ρ‖ ≤ 4 * Real.sqrt (‖z‖ + 2) * zeroWeight ρ := by
  set Y := ‖z‖ + 2 with hYdef
  set g := |ρ.im| with hgdef
  have hY : 2 ≤ Y := by rw [hYdef]; linarith [norm_nonneg z]
  have hg : 4 ≤ g := by linarith
  have htz : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
  have hzρ : g / 2 ≤ ‖z - ρ‖ := by
    have h1 := abs_im_sub_le_norm z ρ
    have h2 : g - |z.im| ≤ |ρ.im - z.im| := by
      rw [hgdef]
      have := abs_sub_abs_le_abs_sub ρ.im z.im
      linarith
    linarith
  have h2ρ : g ≤ ‖2 - ρ‖ := abs_im_le_norm_two_sub ρ
  have hzρ0 : z - ρ ≠ 0 := fun h ↦ by rw [h, norm_zero] at hzρ; linarith
  have h2ρ0 : (2 : ℂ) - ρ ≠ 0 := fun h ↦ by rw [h, norm_zero] at h2ρ; linarith
  have hid : 1 / (z - ρ) - 1 / (2 - ρ) = (2 - z) * (1 / (z - ρ)) * (1 / (2 - ρ)) := by
    field_simp
    ring
  have e1 : ‖(2 : ℂ) - z‖ ≤ Y := by
    have := norm_sub_le (2 : ℂ) z
    rw [show ‖(2 : ℂ)‖ = 2 by simp] at this
    linarith
  have e2 : ‖1 / (z - ρ)‖ ≤ 2 / g := by
    have := norm_one_div_le (by linarith) hzρ
    rwa [one_div_div] at this
  have e3 : ‖1 / (2 - ρ)‖ ≤ 1 / g := norm_one_div_le (by linarith) h2ρ
  have hsY := Real.sqrt_nonneg Y
  have hYY : Real.sqrt Y * Real.sqrt Y = Y := Real.mul_self_sqrt (by linarith)
  have hkey : Y * (2 / g) * (1 / g) ≤ 4 * Real.sqrt Y * (1 + g) ^ (-(3 / 2 : ℝ)) := by
    rw [rpow_neg_three_halves_eq (by linarith)]
    have hs1 : 0 < Real.sqrt (1 + g) := Real.sqrt_pos.2 (by linarith)
    have hl : Y * (2 / g) * (1 / g) = 2 * Y / g ^ 2 := by field_simp
    have hr : 4 * Real.sqrt Y * (1 / ((1 + g) * Real.sqrt (1 + g))) =
        4 * Real.sqrt Y / ((1 + g) * Real.sqrt (1 + g)) := by ring
    rw [hl, hr, div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : Real.sqrt (1 + g) ≤ Real.sqrt (2 * g) := Real.sqrt_le_sqrt (by linarith)
    have h2 : Real.sqrt (2 * g) * Real.sqrt Y ≤ g := by
      rw [← Real.sqrt_mul (by linarith)]
      calc Real.sqrt (2 * g * Y) ≤ Real.sqrt (g ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
        _ = g := Real.sqrt_sq (by linarith)
    have h3 : 0 ≤ Real.sqrt (2 * g) := Real.sqrt_nonneg _
    calc 2 * Y * ((1 + g) * Real.sqrt (1 + g)) ≤ 2 * Y * ((2 * g) * Real.sqrt (2 * g)) := by
          gcongr
          linarith
      _ = 4 * g * Real.sqrt Y * (Real.sqrt (2 * g) * Real.sqrt Y) := by
          linear_combination (-4 * g * Real.sqrt (2 * g)) * hYY
      _ ≤ 4 * g * Real.sqrt Y * g := by gcongr
      _ = 4 * Real.sqrt Y * g ^ 2 := by ring
  rw [zeroTerm, norm_mul, norm_zetaOrder_of_mem hρ, hid, norm_mul, norm_mul, zeroWeight]
  have hm := zetaOrder_nonneg_of_mem_ntZeros hρ
  calc (zetaOrder ρ : ℝ) * (‖(2 : ℂ) - z‖ * ‖1 / (z - ρ)‖ * ‖1 / (2 - ρ)‖)
      ≤ (zetaOrder ρ : ℝ) * (Y * (2 / g) * (1 / g)) := by
        gcongr
    _ ≤ (zetaOrder ρ : ℝ) * (4 * Real.sqrt Y * (1 + g) ^ (-(3 / 2 : ℝ))) := by gcongr
    _ = 4 * Real.sqrt Y * ((zetaOrder ρ : ℝ) * (1 + |ρ.im|) ^ (-(3 / 2 : ℝ))) := by ring

/-- `∑_ρ m(ρ) (1 + |γ|)^{-3/2}`, bounded through the lattice sum. -/
def weightBound : ℝ :=
  2 * windowConst * ∑' j : ℕ, Real.log ((j : ℝ) + 4) * ((j : ℝ) + 1) ^ (-(3 / 2 : ℝ))

theorem weightBound_nonneg : 0 ≤ weightBound :=
  mul_nonneg (by linarith [windowConst_nonneg]) (tsum_nonneg fun j ↦ mul_nonneg
    (Real.log_nonneg (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]))
    (Real.rpow_nonneg (by positivity) _))

/-- The harmonic sums over the annuli about a height `t₀` with `|t₀| ≤ ‖z‖`, for the zeros with
`|γ - t₀| ≤ 3 (‖z‖ + 2)`. -/
theorem sum_zetaOrder_div_floor_le {z : ℂ} {t₀ : ℝ} (ht₀ : |t₀| ≤ ‖z‖) {F : Finset ℂ}
    (hF : ∀ x ∈ F, x ∈ 𝒵 ∧ |x.im - t₀| ≤ 3 * (‖z‖ + 2)) :
    ∑ x ∈ F, (zetaOrder x : ℝ) * (1 / max 1 (⌊|x.im - t₀|⌋₊ : ℝ)) ≤
      24 * windowConst * Real.log (‖z‖ + 4) ^ 2 := by
  set ℓ := Real.log (‖z‖ + 4) with hℓdef
  have hz0 := norm_nonneg z
  have hW := windowConst_nonneg
  have hℓ1 : 1 ≤ ℓ := one_lt_log_four.le.trans (Real.log_le_log (by norm_num) (by linarith))
  have hsq : Real.log ((‖z‖ + 4) ^ 2) = 2 * ℓ := by rw [Real.log_pow]; push_cast; ring
  set J := ⌊3 * (‖z‖ + 2)⌋₊ + 1 with hJdef
  have hJle : (J : ℝ) ≤ 3 * (‖z‖ + 2) + 1 := by
    rw [hJdef]
    push_cast
    linarith [Nat.floor_le (by positivity : (0 : ℝ) ≤ 3 * (‖z‖ + 2))]
  have hJ0 : (0 : ℝ) < J := by rw [hJdef]; push_cast; positivity
  have h1 := sum_mul_le_of_annuli t₀ (fun x hx ↦ (hF x hx).1)
    (fun x ↦ 1 / max 1 (⌊|x.im - t₀|⌋₊ : ℝ)) (fun j ↦ 1 / max 1 (j : ℝ))
    (fun j ↦ by positivity) (fun x _ ↦ le_rfl) J
    (fun x hx ↦ Nat.lt_succ_of_le (Nat.floor_le_floor (hF x hx).2))
  have h2 := sum_range_log_div_le (abs_nonneg t₀) J
  have h3 : Real.log (|t₀| + J + 4) ≤ 2 * ℓ := by
    rw [← hsq]
    exact Real.log_le_log (by positivity) (by nlinarith)
  have h4 : 1 + Real.log J ≤ 3 * ℓ := by
    have : Real.log J ≤ 2 * ℓ := by
      rw [← hsq]
      exact Real.log_le_log hJ0 (by nlinarith)
    linarith
  have h5 : 0 ≤ Real.log (|t₀| + J + 4) := Real.log_nonneg (by linarith [abs_nonneg t₀])
  have h6 : ∑ j ∈ Finset.range J,
      2 * windowConst * Real.log (|t₀| + j + 4) * (1 / max 1 (j : ℝ)) =
      2 * windowConst * ∑ j ∈ Finset.range J, Real.log (|t₀| + j + 4) * (1 / max 1 (j : ℝ)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  calc _ ≤ _ := h1
    _ = _ := h6
    _ ≤ 2 * windowConst * (Real.log (|t₀| + J + 4) * (2 * (1 + Real.log J))) := by gcongr
    _ ≤ 2 * windowConst * ((2 * ℓ) * (2 * (3 * ℓ))) := by gcongr
    _ = 24 * windowConst * ℓ ^ 2 := by ring

/-- **The bound for `S`**: if every zero is at distance at least `δ ≤ 1` from `z`, then
`‖S(z)‖ ≪ (1/δ) log(‖z‖ + 4) + log²(‖z‖ + 4) + √(‖z‖ + 2)`. -/
theorem norm_zeroSum_le {z : ℂ} {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (h : ∀ ρ ∈ 𝒵, δ ≤ ‖z - ρ‖) :
    ‖zeroSum z‖ ≤ 4 * windowConst * Real.log (‖z‖ + 4) / δ +
      48 * windowConst * Real.log (‖z‖ + 4) ^ 2 + 4 * weightBound * Real.sqrt (‖z‖ + 2) := by
  classical
  set Y := ‖z‖ + 2 with hYdef
  set t := z.im with htdef
  set ℓ := Real.log (‖z‖ + 4) with hℓdef
  have hz0 := norm_nonneg z
  have hW := windowConst_nonneg
  have hℓ1 : 1 ≤ ℓ := by
    rw [hℓdef]
    exact one_lt_log_four.le.trans (Real.log_le_log (by norm_num) (by linarith))
  have htz : |t| ≤ ‖z‖ := Complex.abs_im_le_norm z
  have hB : 0 ≤ 4 * windowConst * ℓ / δ + 48 * windowConst * ℓ ^ 2 +
      4 * weightBound * Real.sqrt Y := by
    have := weightBound_nonneg
    positivity
  have hsum := summable_norm_zeroTerm hδ hδ1 h
  rw [zeroSum]
  refine (norm_tsum_le_tsum_norm hsum).trans (tsum_le_of_sum_le' hB fun u ↦ ?_)
  set F : Finset ℂ := u.map (Function.Embedding.subtype _) with hFdef
  have hF : ∀ x ∈ F, x ∈ 𝒵 := by
    intro x hx
    obtain ⟨σ, -, rfl⟩ := Finset.mem_map.1 hx
    exact σ.2
  have hsF : ∑ ρ ∈ u, ‖zeroTerm z ρ‖ = ∑ x ∈ F, ‖zeroTerm z x‖ := by
    rw [hFdef, Finset.sum_map]
    rfl
  rw [hsF, ← Finset.sum_filter_add_sum_filter_not F (fun x ↦ |x.im - t| < 1),
    ← Finset.sum_filter_add_sum_filter_not (F.filter fun x ↦ ¬|x.im - t| < 1)
      (fun x ↦ |x.im| ≤ 2 * Y)]
  -- the zeros near the height of `z`
  have p1 : ∑ x ∈ F.filter (fun x ↦ |x.im - t| < 1), ‖zeroTerm z x‖ ≤
      4 * windowConst * ℓ / δ := by
    have hterm : ∀ x ∈ F.filter (fun x ↦ |x.im - t| < 1),
        ‖zeroTerm z x‖ ≤ (zetaOrder x : ℝ) * (2 / δ) := by
      intro x hx
      have hxZ := hF x (Finset.mem_filter.1 hx).1
      rw [zeroTerm, norm_mul, norm_zetaOrder_of_mem hxZ]
      refine mul_le_mul_of_nonneg_left ?_ (zetaOrder_nonneg_of_mem_ntZeros hxZ)
      have a1 := norm_one_div_le hδ (h x hxZ)
      have a2 := norm_one_div_le one_pos (one_le_norm_two_sub hxZ)
      have a3 := norm_sub_le (1 / (z - x)) (1 / (2 - x))
      have a4 : 1 / δ ≥ 1 := by rw [ge_iff_le, le_div_iff₀ hδ]; linarith
      have a5 : 1 / δ + 1 / δ = 2 / δ := by ring
      linarith
    have hcount := sum_zetaOrder_le_annulus t 0 (F := F.filter (fun x ↦ |x.im - t| < 1))
      (fun x hx ↦ ⟨hF x (Finset.mem_filter.1 hx).1, Nat.floor_eq_zero.2 (Finset.mem_filter.1 hx).2⟩)
    have hlog : Real.log (|t| + ((0 : ℕ) : ℝ) + 4) ≤ ℓ :=
      Real.log_le_log (by positivity) (by push_cast; linarith)
    calc ∑ x ∈ F.filter (fun x ↦ |x.im - t| < 1), ‖zeroTerm z x‖
        ≤ ∑ x ∈ F.filter (fun x ↦ |x.im - t| < 1), (zetaOrder x : ℝ) * (2 / δ) :=
          Finset.sum_le_sum hterm
      _ = (∑ x ∈ F.filter (fun x ↦ |x.im - t| < 1), (zetaOrder x : ℝ)) * (2 / δ) := by
          rw [Finset.sum_mul]
      _ ≤ (2 * windowConst * ℓ) * (2 / δ) := by
          gcongr
          exact hcount.trans (mul_le_mul_of_nonneg_left hlog (by linarith))
      _ = 4 * windowConst * ℓ / δ := by ring
  -- the zeros at moderate height
  set F₂ := (F.filter fun x ↦ ¬|x.im - t| < 1).filter (fun x ↦ |x.im| ≤ 2 * Y) with hF₂def
  have hF₂ : ∀ x ∈ F₂, x ∈ 𝒵 ∧ 1 ≤ |x.im - t| ∧ |x.im| ≤ 2 * Y := by
    intro x hx
    rw [hF₂def, Finset.mem_filter, Finset.mem_filter] at hx
    exact ⟨hF x hx.1.1, not_lt.1 hx.1.2, hx.2⟩
  have p2a : ∑ x ∈ F₂, (zetaOrder x : ℝ) * (1 / max 1 (⌊|x.im - t|⌋₊ : ℝ)) ≤
      24 * windowConst * ℓ ^ 2 :=
    sum_zetaOrder_div_floor_le htz fun x hx ↦ ⟨(hF₂ x hx).1, by
      have := abs_sub x.im t
      linarith [(hF₂ x hx).2.2]⟩
  have p2b : ∑ x ∈ F₂, (zetaOrder x : ℝ) * (1 / max 1 (⌊|x.im - 0|⌋₊ : ℝ)) ≤
      24 * windowConst * ℓ ^ 2 :=
    sum_zetaOrder_div_floor_le (t₀ := 0) (by rw [abs_zero]; exact hz0) fun x hx ↦
      ⟨(hF₂ x hx).1, by rw [sub_zero]; linarith [(hF₂ x hx).2.2]⟩
  have p2 : ∑ x ∈ F₂, ‖zeroTerm z x‖ ≤ 48 * windowConst * ℓ ^ 2 := by
    have hterm : ∀ x ∈ F₂, ‖zeroTerm z x‖ ≤
        (zetaOrder x : ℝ) * (1 / max 1 (⌊|x.im - t|⌋₊ : ℝ)) +
          (zetaOrder x : ℝ) * (1 / max 1 (⌊|x.im - 0|⌋₊ : ℝ)) := by
      intro x hx
      obtain ⟨hxZ, hx1, -⟩ := hF₂ x hx
      rw [zeroTerm, norm_mul, norm_zetaOrder_of_mem hxZ, ← mul_add]
      refine mul_le_mul_of_nonneg_left ?_ (zetaOrder_nonneg_of_mem_ntZeros hxZ)
      have hfl1 : max 1 (⌊|x.im - t|⌋₊ : ℝ) ≤ ‖z - x‖ :=
        max_le (hx1.trans (abs_im_sub_le_norm z x))
          ((Nat.floor_le (abs_nonneg _)).trans (abs_im_sub_le_norm z x))
      have hfl2 : max 1 (⌊|x.im - 0|⌋₊ : ℝ) ≤ ‖2 - x‖ := by
        rw [sub_zero]
        exact (max_le_max le_rfl (Nat.floor_le (abs_nonneg _))).trans (max_le_norm_two_sub hxZ)
      have a1 := norm_one_div_le (by positivity) hfl1
      have a2 := norm_one_div_le (by positivity) hfl2
      have a3 := norm_sub_le (1 / (z - x)) (1 / (2 - x))
      linarith
    calc ∑ x ∈ F₂, ‖zeroTerm z x‖ ≤ ∑ x ∈ F₂, ((zetaOrder x : ℝ) *
          (1 / max 1 (⌊|x.im - t|⌋₊ : ℝ)) + (zetaOrder x : ℝ) * (1 / max 1 (⌊|x.im - 0|⌋₊ : ℝ))) :=
          Finset.sum_le_sum hterm
      _ = _ := Finset.sum_add_distrib
      _ ≤ 24 * windowConst * ℓ ^ 2 + 24 * windowConst * ℓ ^ 2 := add_le_add p2a p2b
      _ = 48 * windowConst * ℓ ^ 2 := by ring
  -- the zeros far above
  have p3 : ∑ x ∈ (F.filter fun x ↦ ¬|x.im - t| < 1).filter (fun x ↦ ¬|x.im| ≤ 2 * Y),
      ‖zeroTerm z x‖ ≤ 4 * weightBound * Real.sqrt Y := by
    set F₃ := (F.filter fun x ↦ ¬|x.im - t| < 1).filter (fun x ↦ ¬|x.im| ≤ 2 * Y) with hF₃def
    have hF₃ : ∀ x ∈ F₃, x ∈ 𝒵 ∧ 2 * Y < |x.im| := by
      intro x hx
      rw [hF₃def, Finset.mem_filter, Finset.mem_filter] at hx
      exact ⟨hF x hx.1.1, not_le.1 hx.2⟩
    calc ∑ x ∈ F₃, ‖zeroTerm z x‖ ≤ ∑ x ∈ F₃, 4 * Real.sqrt Y * zeroWeight x :=
          Finset.sum_le_sum fun x hx ↦ norm_zeroTerm_le_far (hF₃ x hx).1 (hF₃ x hx).2
      _ = 4 * Real.sqrt Y * ∑ x ∈ F₃, zeroWeight x := by rw [Finset.mul_sum]
      _ ≤ 4 * Real.sqrt Y * weightBound := by
          gcongr
          exact sum_zeroWeight_le fun x hx ↦ (hF₃ x hx).1
      _ = 4 * weightBound * Real.sqrt Y := by ring
  linarith

/-! ### `|G(z)| ≪ √(|z| + 2)` on the boundaries of the rectangles -/

/-- The constant of the bound on `Re z ≥ 2`. -/
def rightConst : ℝ := vonMangoldtSumTwo + 8 + 776 * windowConst + 4 * weightBound

theorem rightConst_nonneg : 0 ≤ rightConst := by
  have := vonMangoldtSumTwo_nonneg
  have := windowConst_nonneg
  have := weightBound_nonneg
  unfold rightConst
  positivity

theorem two_le_sqrt {y : ℝ} (hy : 4 ≤ y) : 2 ≤ Real.sqrt y := by
  rw [show (2 : ℝ) = Real.sqrt 4 by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt hy

/-- `‖G(z)‖ ≤ ‖ζ'/ζ(z)‖ + ‖ψ(z/2 + 1)‖/2 + ‖1/(z - 1)‖ + 1 + ‖S(z)‖`, by Step A. -/
theorem norm_xiRem_le {z : ℂ} (hz1 : z ≠ 1) (hz : riemannZeta z ≠ 0) :
    ‖xiRem z‖ ≤ ‖deriv riemannZeta z / riemannZeta z‖ + ‖digamma (z / 2 + 1)‖ / 2 +
      ‖1 / (z - 1)‖ + 1 + ‖zeroSum z‖ := by
  rw [xiRem, logDeriv_riemannXi_eq_zetaH hz1 hz, zetaH]
  have h1 : ‖deriv riemannZeta z / riemannZeta z + digamma (z / 2 + 1) / 2 + 1 / (z - 1)‖ ≤
      ‖deriv riemannZeta z / riemannZeta z‖ + ‖digamma (z / 2 + 1) / 2‖ + ‖1 / (z - 1)‖ :=
    norm_add₃_le
  rw [norm_div (digamma _), show ‖(2 : ℂ)‖ = 2 by simp] at h1
  have h2 := norm_sub_le (deriv riemannZeta z / riemannZeta z + digamma (z / 2 + 1) / 2 +
    1 / (z - 1) - ((Real.log π : ℝ) : ℂ) / 2) (zeroSum z)
  have h3 := norm_sub_le (deriv riemannZeta z / riemannZeta z + digamma (z / 2 + 1) / 2 +
    1 / (z - 1)) (((Real.log π : ℝ) : ℂ) / 2)
  have := norm_log_pi_div_two_le
  linarith

/-- F1: `|G(z)| ≤ rightConst · √(‖z‖ + 4)` for `Re z ≥ 2`. -/
theorem norm_xiRem_le_of_two_le_re {z : ℂ} (hz : 2 ≤ z.re) :
    ‖xiRem z‖ ≤ rightConst * Real.sqrt (‖z‖ + 4) := by
  have hz1 : z ≠ 1 := fun h ↦ by rw [h, one_re] at hz; linarith
  have hζ : riemannZeta z ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by linarith)
  have hz0 := norm_nonneg z
  have hrez := Complex.re_le_norm z
  have himz := Complex.abs_im_le_norm z
  set s := Real.sqrt (‖z‖ + 4) with hsdef
  set ℓ := Real.log (‖z‖ + 4) with hℓdef
  have hs2 : 2 ≤ s := two_le_sqrt (by linarith)
  have hℓ0 : 0 ≤ ℓ := Real.log_nonneg (by linarith)
  have hℓs : ℓ ≤ 2 * s := log_le_two_mul_sqrt (by linarith)
  have hℓ2s : ℓ ^ 2 ≤ 16 * s := log_sq_le_sixteen_mul_sqrt (by linarith)
  have hfar : ∀ ρ ∈ 𝒵, (1 : ℝ) ≤ ‖z - ρ‖ := by
    intro ρ hρ
    have := (mem_ntZeros.1 hρ).1.2
    calc (1 : ℝ) ≤ (z - ρ).re := by simp only [sub_re]; linarith
      _ ≤ ‖z - ρ‖ := (le_abs_self _).trans (Complex.abs_re_le_norm _)
  have hS := norm_zeroSum_le one_pos le_rfl hfar
  rw [div_one, ← hℓdef] at hS
  have hsq : Real.sqrt (‖z‖ + 2) ≤ s := Real.sqrt_le_sqrt (by linarith)
  have hζb := norm_logDeriv_riemannZeta_le_of_two_le_re hz
  have hw : 1 ≤ (z / 2 + 1).re := by
    simp only [add_re, div_ofNat_re, one_re]
    linarith
  have hψ := norm_digamma_le_of_one_le_re hw
  have hre : Real.log (z / 2 + 1).re ≤ ℓ := by
    refine Real.log_le_log (by linarith) ?_
    simp only [add_re, div_ofNat_re, one_re]
    linarith
  have him : Real.log (1 + |(z / 2 + 1).im|) ≤ ℓ := by
    refine Real.log_le_log (by positivity) ?_
    simp only [add_im, div_ofNat_im, one_im, add_zero, abs_div, abs_two]
    linarith
  have hpole : ‖1 / (z - 1)‖ ≤ 1 := by
    refine (norm_one_div_le one_pos ?_).trans (by norm_num)
    calc (1 : ℝ) ≤ (z - 1).re := by simp only [sub_re, one_re]; linarith
      _ ≤ ‖z - 1‖ := (le_abs_self _).trans (Complex.abs_re_le_norm _)
  have hX := norm_xiRem_le hz1 hζ
  have hW := windowConst_nonneg
  have hB := weightBound_nonneg
  have hV := vonMangoldtSumTwo_nonneg
  have k1 : vonMangoldtSumTwo ≤ vonMangoldtSumTwo * s := le_mul_of_one_le_right hV (by linarith)
  have k2 : 4 * windowConst * ℓ ≤ 8 * windowConst * s := by
    have := mul_le_mul_of_nonneg_left hℓs hW
    linarith
  have k3 : 48 * windowConst * ℓ ^ 2 ≤ 768 * windowConst * s := by
    have := mul_le_mul_of_nonneg_left hℓ2s hW
    linarith
  have k4 : 4 * weightBound * Real.sqrt (‖z‖ + 2) ≤ 4 * weightBound * s :=
    mul_le_mul_of_nonneg_left hsq (by positivity)
  rw [rightConst]
  linarith only [hX, hψ, hre, him, hS, hζb, hpole, hℓs, hs2, k1, k2, k3, k4]

/-- F2: by the symmetry, for `Re z ≤ -1`. -/
theorem norm_xiRem_le_of_re_le_neg_one {z : ℂ} (hz : z.re ≤ -1) :
    ‖xiRem z‖ ≤ ‖symmConst‖ + rightConst * Real.sqrt (‖z‖ + 5) := by
  have hzZ : z ∉ 𝒵 := fun h ↦ by
    have := (mem_ntZeros.1 h).1.1
    linarith
  have h1 : 2 ≤ (1 - z).re := by simp only [sub_re, one_re]; linarith
  have h2 := norm_xiRem_le_of_two_le_re h1
  have h3 : ‖1 - z‖ + 4 ≤ ‖z‖ + 5 := by
    have := norm_sub_le (1 : ℂ) z
    rw [norm_one] at this
    linarith
  have h4 : Real.sqrt (‖1 - z‖ + 4) ≤ Real.sqrt (‖z‖ + 5) := Real.sqrt_le_sqrt h3
  have h5 : xiRem z = -symmConst - xiRem (1 - z) := by
    have := xiRem_add_xiRem_one_sub hzZ
    linear_combination this
  rw [h5]
  calc ‖-symmConst - xiRem (1 - z)‖ ≤ ‖symmConst‖ + ‖xiRem (1 - z)‖ := by
        have := norm_sub_le (-symmConst) (xiRem (1 - z))
        rwa [norm_neg] at this
    _ ≤ ‖symmConst‖ + rightConst * Real.sqrt (‖z‖ + 5) := by
        gcongr
        exact h2.trans (mul_le_mul_of_nonneg_left h4 rightConst_nonneg)

/-- F3: on the segments `Re z ∈ [-1, 2]` at the heights `±T₁`, where `T₁` is a good height. -/
theorem exists_norm_xiRem_le_good : ∃ A : ℝ, 0 ≤ A ∧ ∀ T : ℝ, 2 ≤ T → ∃ T₁ ∈ Icc T (T + 1),
    ∀ z : ℂ, z.re ∈ Icc (-1 : ℝ) 2 → |z.im| = T₁ →
      z ∉ 𝒵 ∧ ‖xiRem z‖ ≤ A * Real.sqrt (‖z‖ + T + 4) := by
  obtain ⟨C, c, hC, hc, hgood⟩ := exists_good_height_margin
  obtain ⟨CD, hCD⟩ := Complex.exists_norm_digamma_le_log (σ₁ := 1 / 2) (σ₂ := 2) (by norm_num)
  have hW := windowConst_nonneg
  have hB := weightBound_nonneg
  set CD' := max CD 0 with hCD'
  have hCD'0 : 0 ≤ CD' := le_max_right _ _
  refine ⟨16 * C + CD' + 4 + 64 * windowConst / c + 8 * windowConst + 768 * windowConst +
    4 * weightBound, by positivity, fun T hT ↦ ?_⟩
  obtain ⟨T₁, hT₁, hmargin, hζ⟩ := hgood T hT
  refine ⟨T₁, hT₁, fun z hzre hzim ↦ ?_⟩
  have hT₁2 : 2 ≤ T₁ := le_trans hT hT₁.1
  have hlogT : 0 < Real.log T := Real.log_pos (by linarith)
  -- `ζ(z) ≠ 0` and the bound for `ζ'/ζ(z)`, at `+T₁` from the good height, at `-T₁` by conjugation
  set s₀ : ℂ := (z.re : ℂ) + T₁ * I with hs₀
  have hs₀1 : s₀ ≠ 1 := fun h ↦ by
    have := congrArg im h
    simp [hs₀] at this
    linarith
  obtain ⟨hζs₀, hζ's₀⟩ := hζ z.re hzre
  have hcases : z = s₀ ∨ z = conj s₀ := by
    rcases (abs_eq (by linarith)).1 hzim with h | h
    · left
      apply Complex.ext <;> simp [hs₀, h]
    · right
      apply Complex.ext <;> simp [hs₀, h]
  have hζz : riemannZeta z ≠ 0 ∧ ‖deriv riemannZeta z / riemannZeta z‖ ≤ C * Real.log T ^ 2 := by
    rcases hcases with h | h
    · rw [h]
      exact ⟨hζs₀, hζ's₀⟩
    · rw [h, riemannZeta_conj hs₀1, deriv_riemannZeta_conj hs₀1, ← map_div₀, Complex.norm_conj]
      exact ⟨by rwa [ne_eq, map_eq_zero], hζ's₀⟩
  have hzZ : z ∉ 𝒵 := riemannXi_ne_zero_of_riemannZeta_ne_zero hζz.1
  refine ⟨hzZ, ?_⟩
  have hz1 : z ≠ 1 := fun h ↦ by
    rw [h, one_im, abs_zero] at hzim
    linarith
  -- the margin
  have hmz : ∀ ρ ∈ 𝒵, c / Real.log T ≤ |ρ.im - z.im| := by
    intro ρ hρ
    rcases (abs_eq (by linarith)).1 hzim with h | h
    · rw [h, abs_sub_comm]
      exact hmargin ρ hρ
    · have := hmargin (conj ρ) (conj_mem_ntZeros hρ)
      rw [Complex.conj_im] at this
      rw [h]
      rwa [show ρ.im - -T₁ = T₁ - -ρ.im by ring]
  set δ := min (c / Real.log T) 1 with hδdef
  have hδ : 0 < δ := lt_min (div_pos hc hlogT) one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδz : ∀ ρ ∈ 𝒵, δ ≤ ‖z - ρ‖ := fun ρ hρ ↦
    ((min_le_left _ _).trans (hmz ρ hρ)).trans (abs_im_sub_le_norm z ρ)
  have hinvδ : 1 / δ ≤ Real.log T / c + 1 := by
    rcases min_cases (c / Real.log T) 1 with ⟨h, -⟩ | ⟨h, -⟩
    · rw [hδdef, h, one_div_div]
      linarith [div_nonneg hlogT.le hc.le]
    · rw [hδdef, h]
      linarith [div_nonneg hlogT.le hc.le]
  -- the scales
  have hz0 := norm_nonneg z
  have himz := Complex.abs_im_le_norm z
  set sq := Real.sqrt (‖z‖ + T + 4) with hsqdef
  set L := Real.log (‖z‖ + T + 4) with hLdef
  have hsq2 : 2 ≤ sq := two_le_sqrt (by linarith)
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith)
  have hLs : L ≤ 2 * sq := log_le_two_mul_sqrt (by linarith)
  have hL2s : L ^ 2 ≤ 16 * sq := log_sq_le_sixteen_mul_sqrt (by linarith)
  have hTL : Real.log T ≤ L := Real.log_le_log (by linarith) (by linarith)
  set ℓ := Real.log (‖z‖ + 4) with hℓdef
  have hℓ0 : 0 ≤ ℓ := Real.log_nonneg (by linarith)
  have hℓL : ℓ ≤ L := Real.log_le_log (by linarith) (by linarith)
  -- `S`
  have hS := norm_zeroSum_le hδ hδ1 hδz
  rw [← hℓdef] at hS
  have hsq' : Real.sqrt (‖z‖ + 2) ≤ sq := Real.sqrt_le_sqrt (by linarith)
  -- `ψ`
  have hψ : ‖digamma (z / 2 + 1)‖ ≤ CD' * L := by
    have e : z / 2 + 1 = ((z.re / 2 + 1 : ℝ) : ℂ) + ((z.im / 2 : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp
    have h1 := hCD (z.re / 2 + 1) (z.im / 2) ⟨by linarith [hzre.1], by linarith [hzre.2]⟩
    rw [← e] at h1
    have h2 : Real.log (|z.im / 2| + 2) ≤ L := by
      refine Real.log_le_log (by positivity) ?_
      rw [abs_div, abs_two]
      linarith
    have h3 : 0 ≤ Real.log (|z.im / 2| + 2) := Real.log_nonneg (by linarith [abs_nonneg (z.im / 2)])
    calc ‖digamma (z / 2 + 1)‖ ≤ CD * Real.log (|z.im / 2| + 2) := h1
      _ ≤ CD' * Real.log (|z.im / 2| + 2) := mul_le_mul_of_nonneg_right (le_max_left _ _) h3
      _ ≤ CD' * L := mul_le_mul_of_nonneg_left h2 hCD'0
  have hpole : ‖1 / (z - 1)‖ ≤ 1 := by
    refine (norm_one_div_le one_pos ?_).trans (by norm_num)
    have := Complex.abs_im_le_norm (z - 1)
    rw [sub_im, one_im, sub_zero, hzim] at this
    linarith
  have hX := norm_xiRem_le hz1 hζz.1
  -- converting everything to `√(‖z‖ + T + 4)`
  have k1 : C * Real.log T ^ 2 ≤ 16 * C * sq := by
    have : Real.log T ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hlogT.le hTL 2
    calc C * Real.log T ^ 2 ≤ C * L ^ 2 := mul_le_mul_of_nonneg_left this hC.le
      _ ≤ C * (16 * sq) := mul_le_mul_of_nonneg_left hL2s hC.le
      _ = 16 * C * sq := by ring
  have k2 : CD' * L / 2 ≤ CD' * sq := by
    have := mul_le_mul_of_nonneg_left hLs hCD'0
    linarith
  have k3 : 4 * windowConst * ℓ / δ ≤ 64 * windowConst / c * sq + 8 * windowConst * sq := by
    have h1 : 4 * windowConst * ℓ / δ = 4 * windowConst * ℓ * (1 / δ) := by ring
    have h2 : 4 * windowConst * ℓ * (1 / δ) ≤ 4 * windowConst * L * (L / c + 1) := by
      gcongr
      linarith [div_le_div_of_nonneg_right hTL hc.le]
    have h3 : 4 * windowConst * L * (L / c + 1) =
        4 * windowConst / c * L ^ 2 + 4 * windowConst * L := by
      field_simp
    have h4 : 4 * windowConst / c * L ^ 2 ≤ 4 * windowConst / c * (16 * sq) :=
      mul_le_mul_of_nonneg_left hL2s (by positivity)
    have h5 : 4 * windowConst * L ≤ 4 * windowConst * (2 * sq) :=
      mul_le_mul_of_nonneg_left hLs (by positivity)
    have h6 : 4 * windowConst / c * (16 * sq) = 64 * windowConst / c * sq := by ring
    linarith
  have k4 : 48 * windowConst * ℓ ^ 2 ≤ 768 * windowConst * sq := by
    have : ℓ ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hℓ0 hℓL 2
    calc 48 * windowConst * ℓ ^ 2 ≤ 48 * windowConst * L ^ 2 :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ ≤ 48 * windowConst * (16 * sq) := mul_le_mul_of_nonneg_left hL2s (by positivity)
      _ = 768 * windowConst * sq := by ring
  have k5 : 4 * weightBound * Real.sqrt (‖z‖ + 2) ≤ 4 * weightBound * sq :=
    mul_le_mul_of_nonneg_left hsq' (by positivity)
  have k6 : (2 : ℝ) ≤ 4 * sq := by linarith
  linarith only [hX, hζz.2, hψ, hpole, hS, k1, k2, k3, k4, k5, k6]

/-- **F**: on the boundary of `[-n, n + 1] × [-T₁, T₁]`, with `T₁ ∈ [n, n + 1]` a good height,
`|G| ≤ A √(3n + 6)`. -/
theorem exists_norm_xiRemExt_le_frontier : ∃ A : ℝ, 0 ≤ A ∧ ∀ n : ℕ, 2 ≤ n → ∃ T₁ : ℝ,
    (n : ℝ) ≤ T₁ ∧ T₁ ≤ n + 1 ∧ ∀ z ∈ frontier (Icc (-(n : ℝ)) (n + 1) ×ℂ Icc (-T₁) T₁),
      ‖xiRemExt z‖ ≤ A * Real.sqrt (3 * n + 6) := by
  obtain ⟨A₁, hA₁, hgood⟩ := exists_norm_xiRem_le_good
  have hc := norm_nonneg symmConst
  have hr := rightConst_nonneg
  refine ⟨‖symmConst‖ + rightConst + A₁, by positivity, fun n hn ↦ ?_⟩
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨T₁, hT₁, hT₁good⟩ := hgood n hn2
  refine ⟨T₁, hT₁.1, hT₁.2, fun z hz ↦ ?_⟩
  rw [frontier_reProdIm, closure_Icc, closure_Icc,
    frontier_Icc (show -T₁ ≤ T₁ by linarith [hT₁.1]),
    frontier_Icc (show -(n : ℝ) ≤ n + 1 by linarith)] at hz
  have hsq1 : 1 ≤ Real.sqrt (3 * n + 6) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hbox : z.re ∈ Icc (-(n : ℝ)) (n + 1) ∧ z.im ∈ Icc (-T₁) T₁ ∧
      ((z.im = -T₁ ∨ z.im = T₁) ∨ (z.re = -n ∨ z.re = n + 1)) := by
    rcases hz with hz | hz
    · rw [Complex.mem_reProdIm] at hz
      refine ⟨hz.1, ?_, Or.inl hz.2⟩
      rcases hz.2 with h | h
      · rw [h]
        exact ⟨le_rfl, by linarith [hT₁.1]⟩
      · rw [Set.mem_singleton_iff.1 h]
        exact ⟨by linarith [hT₁.1], le_rfl⟩
    · rw [Complex.mem_reProdIm] at hz
      refine ⟨?_, hz.2, Or.inr hz.1⟩
      rcases hz.1 with h | h
      · rw [h]
        exact ⟨le_rfl, by linarith⟩
      · rw [Set.mem_singleton_iff.1 h]
        exact ⟨by linarith, le_rfl⟩
  obtain ⟨⟨hre1, hre2⟩, ⟨him1, him2⟩, hside⟩ := hbox
  have hnorm : ‖z‖ ≤ 2 * n + 2 := by
    have := Complex.norm_le_abs_re_add_abs_im z
    have h1 : |z.re| ≤ n + 1 := abs_le.2 ⟨by linarith, hre2⟩
    have h2 : |z.im| ≤ n + 1 := abs_le.2 ⟨by linarith [hT₁.2], by linarith [hT₁.2]⟩
    linarith
  have hz0 := norm_nonneg z
  rcases le_or_gt 2 z.re with hre | hre
  · -- right of the strip
    have hzZ : z ∉ 𝒵 := fun h ↦ by
      have := (mem_ntZeros.1 h).1.2
      linarith
    rw [xiRemExt_eq hzZ]
    calc ‖xiRem z‖ ≤ rightConst * Real.sqrt (‖z‖ + 4) := norm_xiRem_le_of_two_le_re hre
      _ ≤ rightConst * Real.sqrt (3 * n + 6) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) hr
      _ ≤ (‖symmConst‖ + rightConst + A₁) * Real.sqrt (3 * n + 6) := by
          gcongr
          linarith
  rcases le_or_gt z.re (-1) with hre' | hre'
  · -- left of the strip
    have hzZ : z ∉ 𝒵 := fun h ↦ by
      have := (mem_ntZeros.1 h).1.1
      linarith
    rw [xiRemExt_eq hzZ]
    calc ‖xiRem z‖ ≤ ‖symmConst‖ + rightConst * Real.sqrt (‖z‖ + 5) :=
          norm_xiRem_le_of_re_le_neg_one hre'
      _ ≤ ‖symmConst‖ * Real.sqrt (3 * n + 6) + rightConst * Real.sqrt (3 * n + 6) :=
          add_le_add (le_mul_of_one_le_right hc hsq1)
            (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) hr)
      _ ≤ (‖symmConst‖ + rightConst + A₁) * Real.sqrt (3 * n + 6) := by
          nlinarith
  · -- the strip, at a good height
    have hzim : |z.im| = T₁ := by
      rcases hside with h | h
      · rcases h with h | h
        · rw [h, abs_neg, abs_of_pos (by linarith [hT₁.1])]
        · rw [h, abs_of_pos (by linarith [hT₁.1])]
      · exfalso
        rcases h with h | h <;> rw [h] at hre hre' <;> linarith
    obtain ⟨hzZ, hb⟩ := hT₁good z ⟨hre'.le, hre.le⟩ hzim
    rw [xiRemExt_eq hzZ]
    calc ‖xiRem z‖ ≤ A₁ * Real.sqrt (‖z‖ + n + 4) := hb
      _ ≤ A₁ * Real.sqrt (3 * n + 6) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) hA₁
      _ ≤ (‖symmConst‖ + rightConst + A₁) * Real.sqrt (3 * n + 6) := by
          gcongr
          linarith

/-! ### `G` is constant -/

/-- **G**: by Cauchy's estimate on the circles `|z - z₀| = n/2`, inside the rectangles. -/
theorem deriv_xiRemExt (z₀ : ℂ) : deriv xiRemExt z₀ = 0 := by
  obtain ⟨A, hA, hfr⟩ := exists_norm_xiRemExt_le_frontier
  by_contra hne
  set ε := ‖deriv xiRemExt z₀‖ with hεdef
  have hε : 0 < ε := norm_pos_iff.2 hne
  obtain ⟨n, hn⟩ := exists_nat_gt (2 + 2 * ‖z₀‖ + 24 * A ^ 2 / ε ^ 2)
  have hz0 := norm_nonneg z₀
  have h24 : 0 ≤ 24 * A ^ 2 / ε ^ 2 := by positivity
  have hn2 : (2 : ℝ) ≤ n := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  obtain ⟨T₁, hnT, hTn, hbd⟩ := hfr n (by exact_mod_cast hn2)
  have hRc : IsCompact (Icc (-(n : ℝ)) (n + 1) ×ℂ Icc (-T₁) T₁) :=
    isCompact_Icc.reProdIm isCompact_Icc
  have hmax : ∀ w ∈ Icc (-(n : ℝ)) (n + 1) ×ℂ Icc (-T₁) T₁,
      ‖xiRemExt w‖ ≤ A * Real.sqrt (3 * n + 6) := fun w hw ↦
    Complex.norm_le_of_forall_mem_frontier_norm_le hRc.isBounded
      differentiable_xiRemExt.diffContOnCl hbd (by rwa [hRc.isClosed.closure_eq])
  have hr : 0 < (n : ℝ) / 2 := by positivity
  have hsph : ∀ w ∈ sphere z₀ ((n : ℝ) / 2), ‖xiRemExt w‖ ≤ A * Real.sqrt (3 * n + 6) := by
    intro w hw
    apply hmax
    rw [mem_sphere, dist_eq_norm] at hw
    have h1 : ‖w‖ ≤ ‖z₀‖ + n / 2 := by
      have := norm_le_norm_add_norm_sub' w z₀
      linarith
    have h2 := abs_le.1 ((Complex.abs_re_le_norm w).trans h1)
    have h3 := abs_le.1 ((Complex.abs_im_le_norm w).trans h1)
    rw [Complex.mem_reProdIm]
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hC := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr
    differentiable_xiRemExt.diffContOnCl hsph
  have hss : Real.sqrt (3 * n + 6) ^ 2 = 3 * n + 6 := Real.sq_sqrt (by linarith)
  have hsq0 := Real.sqrt_nonneg (3 * (n : ℝ) + 6)
  have hn24 : 24 * A ^ 2 < ε ^ 2 * n := by
    have h' : 24 * A ^ 2 / ε ^ 2 < n := by linarith
    rw [div_lt_iff₀ (by positivity)] at h'
    linarith
  have key : 2 * A * Real.sqrt (3 * n + 6) < ε * n := by
    have h1 : (2 * A * Real.sqrt (3 * n + 6)) ^ 2 < (ε * n) ^ 2 := by
      calc (2 * A * Real.sqrt (3 * n + 6)) ^ 2 = 4 * A ^ 2 * (3 * n + 6) := by
            rw [mul_pow, hss]
            ring
        _ ≤ 24 * A ^ 2 * n := by nlinarith [sq_nonneg A]
        _ < ε ^ 2 * n * n := by nlinarith
        _ = (ε * n) ^ 2 := by ring
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) h1
  have hlt : A * Real.sqrt (3 * n + 6) / ((n : ℝ) / 2) < ε := by
    rw [div_lt_iff₀ hr]
    linarith
  linarith

theorem xiRemExt_eq_xiRemExt_two (z : ℂ) : xiRemExt z = xiRemExt 2 :=
  is_const_of_deriv_eq_zero differentiable_xiRemExt deriv_xiRemExt z 2

/-! ### The conclusion -/

theorem zeroSum_two : zeroSum 2 = 0 := by
  simp [zeroSum, zeroTerm]

/-- **H**: `S(z) = H(z) - H(2)` for `z ≠ 1` with `ζ(z) ≠ 0`. -/
theorem zeroSum_eq_zetaH_sub {z : ℂ} (hz1 : z ≠ 1) (hz : riemannZeta z ≠ 0) :
    zeroSum z = zetaH z - zetaH 2 := by
  have hzZ := riemannXi_ne_zero_of_riemannZeta_ne_zero hz
  have h2ζ : riemannZeta 2 ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by norm_num)
  have h2Z := riemannXi_ne_zero_of_riemannZeta_ne_zero h2ζ
  have e3 := xiRemExt_eq_xiRemExt_two z
  rw [xiRemExt_eq hzZ, xiRemExt_eq h2Z, xiRem, xiRem, logDeriv_riemannXi_eq_zetaH hz1 hz,
    logDeriv_riemannXi_eq_zetaH (by norm_num) h2ζ, zeroSum_two] at e3
  linear_combination -e3

/-- **The partial-fraction expansion of `ζ'/ζ`, in paired form** (IEANTN's
`ZetaHadamard.v1.logDeriv_partial_fractions`), proved without the Hadamard product. -/
theorem logDeriv_partial_fractions : LogDerivPartialFractions := by
  intro s w hs1 hw1 hs hw
  have hsZ := riemannXi_ne_zero_of_riemannZeta_ne_zero hs
  have hwZ := riemannXi_ne_zero_of_riemannZeta_ne_zero hw
  have h := (hasSum_zeroSum hsZ).sub (hasSum_zeroSum hwZ)
  rw [zeroSum_eq_zetaH_sub hs1 hs, zeroSum_eq_zetaH_sub hw1 hw] at h
  convert h using 1
  · funext ρ
    simp only [zeroTerm]
    ring
  · simp only [zetaH]
    ring

end WeilExplicitFormula
