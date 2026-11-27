/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Harald Helfgott
-/
module

public import Mathlib.NumberTheory.WeilExplicitFormula.Landau
public import Mathlib.NumberTheory.WeilExplicitFormula.ZetaBounds

/-! # Zeros of `ζ` in a box of height one (Montgomery–Vaughan, Theorem 10.13)

The number of zeros `ρ = β + iγ` of `ζ` with `0 < β < 1` and `T ≤ γ ≤ T + 1`, counted with
multiplicity, is `O(log (T + 2))` for `T ≥ 0` (`exists_zetaZeroesSum_le`, which is the statement
`Theorem_10_13` of `ExplicitFormula.lean`, i.e. `IEANTN`'s node).

The proof follows `blueprint/proofs/GoodHeights.md`, §2: Jensen's inequality
(`AnalyticOnNhd.sum_divisor_le`) for `(s - 1) ζ(s)` (`zetaOne`), on the discs of radii
`7/4 < 11/6` about `c = 2 + i(T + 1/2)`, with the bounds (Z1)–(Z2) of `ZetaBounds.lean`
(here `M = 7 (T + 5)²` and `‖(c - 1) ζ(c)‖ ≥ 1/3`), counts the zeros with `β ≥ 1/2`; the symmetry
`ρ ↦ 1 - ρ̄` (Z3) maps the zeros with `β < 1/2` injectively to zeros with `β > 1/2`, preserving
`γ` and the multiplicity.

## AI usage

This file was written by Claude (Anthropic) in November 2026. It compiles, but has not been
reviewed by a human.
-/

@[expose] public section

open Real Complex Filter Topology Set Metric MeromorphicOn
open scoped ComplexConjugate

noncomputable section

namespace WeilExplicitFormula

theorem divisor_zetaOne_eq {U : Set ℂ} {ρ : ℂ} (hρ : ρ ∈ U) (hρ1 : ρ ≠ 1) :
    divisor zetaOne U ρ = zetaOrder ρ := by
  rw [AnalyticOnNhd.divisor_apply (fun z _ ↦ differentiable_zetaOne.analyticAt z) hρ,
    analyticOrderAt_zetaOne hρ1, zetaOrder_eq hρ1]
  unfold analyticOrderNatAt
  cases analyticOrderAt riemannZeta ρ with
  | top => simp
  | coe n => simp

/-- The zeros of `ζ` with `1/2 ≤ β < 1`, `T ≤ γ ≤ T + 1` lie in the disc of radius `7/4` about
`2 + i(T + 1/2)`. -/
theorem norm_sub_le_seven_fourths {T : ℝ} {ρ : ℂ} (h1 : 1 / 2 ≤ ρ.re) (h2 : ρ.re < 1)
    (h3 : T ≤ ρ.im) (h4 : ρ.im ≤ T + 1) :
    ‖ρ - (2 + ((T + 1 / 2 : ℝ) : ℂ) * I)‖ ≤ 7 / 4 := by
  have hsq : ‖ρ - (2 + ((T + 1 / 2 : ℝ) : ℂ) * I)‖ ^ 2 ≤ (7 / 4) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [sub_re, sub_im, add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im,
      re_ofNat, im_ofNat]
    nlinarith [mul_nonneg (sub_nonneg.2 h1) (show (0 : ℝ) ≤ 7 / 2 - ρ.re by linarith),
      mul_nonneg (sub_nonneg.2 h3) (show (0 : ℝ) ≤ T + 1 - ρ.im by linarith)]
  nlinarith [norm_nonneg (ρ - (2 + ((T + 1 / 2 : ℝ) : ℂ) * I))]

/-- `(s - 1) ζ(s)` is at most `7 (T + 5)²` on the circle of radius `11/6` about
`2 + i(T + 1/2)`. -/
theorem norm_zetaOne_le_of_mem_sphere {T : ℝ} (hT : 0 ≤ T) {z : ℂ}
    (hz : ‖z - (2 + ((T + 1 / 2 : ℝ) : ℂ) * I)‖ = 11 / 6) :
    ‖zetaOne z‖ ≤ 7 * (T + 5) ^ 2 := by
  set c : ℂ := 2 + ((T + 1 / 2 : ℝ) : ℂ) * I with hc
  have hcre : c.re = 2 := by simp [hc]
  have hcim : c.im = T + 1 / 2 := by simp [hc]
  have hre : 1 / 6 ≤ z.re := by
    have h := Complex.abs_re_le_norm (z - c)
    rw [hz, sub_re, hcre] at h
    linarith [(abs_le.1 h).1]
  have hcn : ‖c‖ ≤ T + 5 / 2 := by
    have h := Complex.norm_le_abs_re_add_abs_im c
    rw [hcre, hcim, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_nonneg (by linarith)] at h
    linarith
  have hc1n : ‖c - 1‖ ≤ T + 3 / 2 := by
    have h := Complex.norm_le_abs_re_add_abs_im (c - 1)
    rw [sub_re, sub_im, hcre, hcim, one_re, one_im, sub_zero,
      abs_of_pos (by norm_num : (0 : ℝ) < 2 - 1), abs_of_nonneg (by linarith)] at h
    linarith
  have hz0 : ‖z‖ ≤ T + 5 := by
    calc ‖z‖ = ‖c + (z - c)‖ := by congr 1; ring
      _ ≤ ‖c‖ + ‖z - c‖ := norm_add_le _ _
      _ ≤ T + 5 := by rw [hz]; linarith
  have hz1 : ‖z - 1‖ ≤ T + 5 := by
    calc ‖z - 1‖ = ‖(c - 1) + (z - c)‖ := by congr 1; ring
      _ ≤ ‖c - 1‖ + ‖z - c‖ := norm_add_le _ _
      _ ≤ T + 5 := by rw [hz]; linarith
  have hpos : 0 < z.re := by linarith
  have hq : ‖z - 1‖ / z.re ≤ 6 * (T + 5) := by
    rw [div_le_iff₀ hpos]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ T + 5) (by linarith : (0 : ℝ) ≤ 6 * z.re - 1)]
  calc ‖zetaOne z‖ ≤ ‖z‖ * (1 + ‖z - 1‖ / z.re) := norm_zetaOne_le hpos
    _ ≤ (T + 5) * (1 + 6 * (T + 5)) :=
        mul_le_mul hz0 (by linarith) (add_nonneg zero_le_one (div_nonneg (norm_nonneg _) hpos.le))
          (by linarith)
    _ ≤ 7 * (T + 5) ^ 2 := by nlinarith

/-- `‖(c - 1) ζ(c)‖ ≥ 1/3` at `c = 2 + i(T + 1/2)`. -/
theorem norm_zetaOne_two_add_ge (t : ℝ) : 1 / 3 ≤ ‖zetaOne (2 + t * I)‖ := by
  have hc1 : (2 + t * I : ℂ) ≠ 1 := fun h ↦ by
    have := congrArg re h
    simp at this
  rw [zetaOne_of_ne hc1, norm_mul]
  have h1 : 1 ≤ ‖(2 + t * I : ℂ) - 1‖ := by
    have h := Complex.abs_re_le_norm ((2 + t * I : ℂ) - 1)
    have hre : ((2 + t * I : ℂ) - 1).re = 1 := by simp; norm_num
    rwa [hre, abs_one] at h
  have h2 := norm_riemannZeta_two_add_ge t
  nlinarith [norm_nonneg (riemannZeta (2 + t * I))]

/-- Jensen's inequality, applied to `(s - 1) ζ(s)` about `2 + i(T + 1/2)`: the zeros of `ζ` with
`1/2 ≤ β < 1`, `T ≤ γ ≤ T + 1`, counted with multiplicity, number at most
`10 log (T + 2) / log (22/21)`. -/
theorem sum_zetaOrder_le_of_jensen {T : ℝ} (hT : 0 ≤ T) (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, 1 / 2 ≤ ρ.re ∧ ρ.re < 1 ∧ T ≤ ρ.im ∧ ρ.im ≤ T + 1) :
    ∑ ρ ∈ S, (zetaOrder ρ : ℝ) ≤ 10 * Real.log (T + 2) / Real.log (22 / 21) := by
  set c : ℂ := 2 + ((T + 1 / 2 : ℝ) : ℂ) * I with hc
  have hA : AnalyticOnNhd ℂ zetaOne (closedBall c |(11 / 6 : ℝ)|) := fun z _ ↦
    differentiable_zetaOne.analyticAt z
  have hfc : 1 / 3 ≤ ‖zetaOne c‖ := norm_zetaOne_two_add_ge (T + 1 / 2)
  have hfc0 : zetaOne c ≠ 0 := norm_pos_iff.1 (by linarith)
  have hbound : ∀ z ∈ sphere c |(11 / 6 : ℝ)|, ‖zetaOne z‖ ≤ 7 * (T + 5) ^ 2 := by
    intro z hz
    rw [mem_sphere, Complex.dist_eq, abs_of_pos (by norm_num)] at hz
    exact norm_zetaOne_le_of_mem_sphere hT hz
  have hJ := AnalyticOnNhd.sum_divisor_le (c := c) (r := 7 / 4) (R := 11 / 6)
    (M := 7 * (T + 5) ^ 2) (by norm_num)
    (by rw [abs_of_pos (by norm_num), abs_of_pos (by norm_num)]; norm_num) (by nlinarith) hA
    hfc0 hbound
  set B := closedBall c |(7 / 4 : ℝ)| with hB
  have hAB : AnalyticOnNhd ℂ zetaOne B := fun z _ ↦ differentiable_zetaOne.analyticAt z
  have hsub : ∀ ρ ∈ S, ρ ∈ B ∧ ρ ≠ 1 := by
    intro ρ hρ
    obtain ⟨h1, h2, h3, h4⟩ := hS ρ hρ
    refine ⟨?_, ne_one_of_re_lt_one h2⟩
    rw [hB, mem_closedBall, Complex.dist_eq, abs_of_pos (by norm_num)]
    exact norm_sub_le_seven_fourths h1 h2 h3 h4
  have hdiv : ∑ ρ ∈ S, (zetaOrder ρ : ℝ) = ((∑ ρ ∈ S, divisor zetaOne B ρ : ℤ) : ℝ) := by
    push_cast
    exact Finset.sum_congr rfl fun ρ hρ ↦ by rw [divisor_zetaOne_eq (hsub ρ hρ).1 (hsub ρ hρ).2]
  have hle : (∑ ρ ∈ S, divisor zetaOne B ρ : ℤ) ≤ ∑ᶠ u, divisor zetaOne B u :=
    sum_le_finsum_of_nonneg (fun u ↦ by simpa using hAB.divisor_nonneg u)
      ((divisor zetaOne B).finiteSupport (isCompact_closedBall _ _)) S
  have hlog : Real.log (7 * (T + 5) ^ 2 / ‖zetaOne c‖) ≤ 10 * Real.log (T + 2) := by
    have hpos : 0 < 7 * (T + 5) ^ 2 / ‖zetaOne c‖ := div_pos (by nlinarith) (by linarith)
    calc Real.log (7 * (T + 5) ^ 2 / ‖zetaOne c‖) ≤ Real.log ((T + 2) ^ 10) := by
          apply Real.log_le_log hpos
          calc 7 * (T + 5) ^ 2 / ‖zetaOne c‖ ≤ 7 * (T + 5) ^ 2 / (1 / 3) := by gcongr
            _ = 21 * (T + 5) ^ 2 := by ring
            _ ≤ 189 * (T + 2) ^ 2 := by nlinarith
            _ ≤ (T + 2) ^ 8 * (T + 2) ^ 2 := by
                gcongr
                calc (189 : ℝ) ≤ 2 ^ 8 := by norm_num
                  _ ≤ (T + 2) ^ 8 := by gcongr; linarith
            _ = (T + 2) ^ 10 := by ring
      _ = 10 * Real.log (T + 2) := by rw [Real.log_pow]; norm_num
  have hlogR : Real.log (11 / 6 / (7 / 4)) = Real.log (22 / 21) := by norm_num
  have hL : 0 < Real.log (22 / 21) := Real.log_pos (by norm_num)
  calc ∑ ρ ∈ S, (zetaOrder ρ : ℝ) = ((∑ ρ ∈ S, divisor zetaOne B ρ : ℤ) : ℝ) := hdiv
    _ ≤ ((∑ᶠ u, divisor zetaOne B u : ℤ) : ℝ) := by exact_mod_cast hle
    _ ≤ Real.log (7 * (T + 5) ^ 2 / ‖zetaOne c‖) / Real.log (11 / 6 / (7 / 4)) := hJ
    _ ≤ 10 * Real.log (T + 2) / Real.log (22 / 21) := by
        rw [hlogR]
        gcongr

/-- **Montgomery–Vaughan, Theorem 10.13**, with an explicit constant: for `T ≥ 0` there are at
most `(20 / log (22/21)) log (T + 2)` zeros `ρ = β + iγ` of `ζ` with `0 < β < 1` and
`T ≤ γ ≤ T + 1`, counted with multiplicity. -/
theorem zetaZeroesSum_le_log {T : ℝ} (hT : 0 ≤ T) :
    zetaZeroesSum (Set.Ioo 0 1) (Set.Icc T (T + 1)) (fun _ ↦ (1 : ℝ)) ≤
      20 / Real.log (22 / 21) * Real.log (T + 2) := by
  have hfin : (zetaZeroesIn (Ioo 0 1) (Icc T (T + 1))).Finite :=
    zetaZeroesIn_finite Ioo_subset_Icc_self subset_rfl
  rw [zetaZeroesSum_eq_sum hfin]
  simp only [one_mul]
  set S := hfin.toFinset with hS
  have hmemS : ∀ ρ, ρ ∈ S ↔ (0 < ρ.re ∧ ρ.re < 1) ∧ (T ≤ ρ.im ∧ ρ.im ≤ T + 1) ∧
      riemannZeta ρ = 0 := fun ρ ↦ by
    rw [hS, Set.Finite.mem_toFinset]
    exact Iff.rfl
  have hnonneg : ∀ ρ ∈ S, (0 : ℝ) ≤ (zetaOrder ρ : ℝ) := by
    intro ρ hρ
    rw [zetaOrder_eq (ne_one_of_re_lt_one ((hmemS ρ).1 hρ).1.2)]
    positivity
  rw [← Finset.sum_filter_add_sum_filter_not S (fun ρ ↦ 1 / 2 ≤ ρ.re)]
  set S₁ := S.filter (fun ρ ↦ 1 / 2 ≤ ρ.re) with hS₁
  set S₂ := S.filter (fun ρ ↦ ¬ 1 / 2 ≤ ρ.re) with hS₂
  -- the zeros with `β < 1/2`, reflected by `ρ ↦ 1 - ρ̄`
  have h₂ : ∑ ρ ∈ S₂, (zetaOrder ρ : ℝ) ≤ ∑ ρ ∈ S₁, (zetaOrder ρ : ℝ) := by
    have hmem2 : ∀ ρ ∈ S₂, 0 < ρ.re ∧ ρ.re < 1 := fun ρ hρ ↦
      ((hmemS ρ).1 (Finset.mem_filter.1 hρ).1).1
    calc ∑ ρ ∈ S₂, (zetaOrder ρ : ℝ) = ∑ ρ ∈ S₂, (zetaOrder (1 - conj ρ) : ℝ) :=
          Finset.sum_congr rfl fun ρ hρ ↦ by
            rw [zetaOrder_one_sub_conj (hmem2 ρ hρ).1 (hmem2 ρ hρ).2]
      _ = ∑ ρ ∈ S₂.image (fun ρ ↦ 1 - conj ρ), (zetaOrder ρ : ℝ) := by
          rw [Finset.sum_image]
          intro x _ y _ hxy
          have := congrArg (fun z ↦ conj (1 - z)) hxy
          simpa using this
      _ ≤ ∑ ρ ∈ S₁, (zetaOrder ρ : ℝ) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun ρ hρ _ ↦
            hnonneg ρ (Finset.mem_filter.1 hρ).1
          intro ρ' hρ'
          obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.1 hρ'
          obtain ⟨hρS, hρhalf⟩ := Finset.mem_filter.1 hρ
          rw [not_le] at hρhalf
          obtain ⟨⟨h0, h1⟩, ⟨hT1, hT2⟩, hz⟩ := (hmemS ρ).1 hρS
          have hre : (1 - conj ρ).re = 1 - ρ.re := by simp
          have him : (1 - conj ρ).im = ρ.im := by simp
          refine Finset.mem_filter.2 ⟨(hmemS _).2 ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩, ?_⟩
          · rw [hre]; linarith
          · rw [hre]; linarith
          · rw [him]; exact hT1
          · rw [him]; exact hT2
          · exact (riemannZeta_one_sub_conj_eq_zero_iff h0 h1).2 hz
          · rw [hre]; linarith
  -- the zeros with `β ≥ 1/2`: Jensen
  have h₁ : ∑ ρ ∈ S₁, (zetaOrder ρ : ℝ) ≤ 10 * Real.log (T + 2) / Real.log (22 / 21) := by
    refine sum_zetaOrder_le_of_jensen hT S₁ fun ρ hρ ↦ ?_
    obtain ⟨hρS, hhalf⟩ := Finset.mem_filter.1 hρ
    obtain ⟨⟨-, h1⟩, ⟨hT1, hT2⟩, -⟩ := (hmemS ρ).1 hρS
    exact ⟨hhalf, h1, hT1, hT2⟩
  calc ∑ ρ ∈ S₁, (zetaOrder ρ : ℝ) + ∑ ρ ∈ S₂, (zetaOrder ρ : ℝ)
      ≤ 2 * (10 * Real.log (T + 2) / Real.log (22 / 21)) := by linarith
    _ = 20 / Real.log (22 / 21) * Real.log (T + 2) := by ring

/-- **Montgomery–Vaughan, Theorem 10.13**: there are `O(log (T + 2))` zeros `ρ = β + iγ` of `ζ`
with `0 < β < 1` and `T ≤ γ ≤ T + 1`, counted with multiplicity. This is the proposition
`Theorem_10_13` of `ExplicitFormula.lean`. -/
theorem exists_zetaZeroesSum_le : ∃ C : ℝ, ∀ T : ℝ, 0 ≤ T →
    zetaZeroesSum (Set.Ioo 0 1) (Set.Icc T (T + 1)) (fun _ ↦ (1 : ℝ)) ≤
      C * Real.log (T + 2) :=
  ⟨_, fun _ hT ↦ zetaZeroesSum_le_log hT⟩

end WeilExplicitFormula
