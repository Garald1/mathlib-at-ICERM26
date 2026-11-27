/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Harald Helfgott
-/
module

public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.LSeries.SumCoeff
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.NumberTheory.WeilExplicitFormula.Contour

/-! # Bounds for `ζ` in `Re s > 0`, and the symmetry of its zeros

Inputs (Z1)–(Z3) of `blueprint/proofs/GoodHeights.md` for Montgomery–Vaughan Theorem 10.13 and
Lemma 12.2.

* (Z1) `zetaOne`: `(s - 1) ζ(s)`, extended by `1` at `s = 1`, is entire (`differentiable_zetaOne`),
  and for `Re s > 0`,
  `(s - 1) ζ(s) = s - s (s - 1) ∫_1^∞ {t} t^{-s-1} dt` (`zetaOne_eq`), hence
  `‖(s - 1) ζ(s)‖ ≤ ‖s‖ (1 + ‖s - 1‖ / Re s)` (`norm_zetaOne_le`) and
  `‖ζ(s)‖ ≤ ‖s‖/‖s - 1‖ + ‖s‖ / Re s` (`norm_riemannZeta_le`). The representation is proved for
  `Re s > 1` from Mathlib's `LSeries_eq_mul_integral'`, and extended by the identity theorem: the
  integral is a Mellin transform, holomorphic in `Re s > 0`
  (`mellin_differentiableAt_of_isBigO_rpow`).
* (Z2) `norm_riemannZeta_two_add_ge`: `‖ζ(2 + it)‖ ≥ 2 - π²/6 ≥ 1/3`.
* (Z3) `analyticOrderAt_riemannZeta_one_sub`: in `0 < Re s < 1`, `ζ` vanishes to the same order
  at `s` and at `1 - s` (from `ξ(1 - s) = ξ(s)`); with `analyticOrderAt_riemannZeta_conj`, the same
  holds at `1 - s̄` (`analyticOrderAt_riemannZeta_one_sub_conj`, `zetaOrder_one_sub_conj`).

## AI usage

This file was written by Claude (Anthropic) in November 2026. It compiles, but has not been
reviewed by a human.
-/

@[expose] public section

open Real Complex Filter Topology Set MeasureTheory Asymptotics
open scoped ComplexConjugate

noncomputable section

namespace WeilExplicitFormula

/-! ### `(s - 1) ζ(s)` -/

/-- `(s - 1) ζ(s)`, extended by `1` at `s = 1`: an entire function (Mathlib's later
`riemannZeta₁`). -/
def zetaOne : ℂ → ℂ := Function.update (fun s ↦ (s - 1) * riemannZeta s) 1 1

theorem zetaOne_of_ne {s : ℂ} (hs : s ≠ 1) : zetaOne s = (s - 1) * riemannZeta s :=
  Function.update_of_ne hs _ _

theorem zetaOne_one : zetaOne 1 = 1 := Function.update_self _ _ _

theorem zetaOne_eventuallyEq {s : ℂ} (hs : s ≠ 1) :
    zetaOne =ᶠ[𝓝 s] fun z ↦ (z - 1) * riemannZeta z := by
  filter_upwards [isOpen_ne.mem_nhds hs] with z hz
  exact zetaOne_of_ne hz

theorem differentiable_zetaOne : Differentiable ℂ zetaOne := by
  intro s
  have hd : ∀ z : ℂ, z ≠ 1 → DifferentiableAt ℂ zetaOne z := fun z hz ↦
    ((zetaOne_eventuallyEq hz).differentiableAt_iff).2
      ((differentiableAt_id.sub_const 1).mul (differentiableAt_riemannZeta hz))
  rcases eq_or_ne s 1 with rfl | hs
  · have hc : ContinuousAt zetaOne 1 := by
      unfold zetaOne
      rw [continuousAt_update_same]
      exact riemannZeta_residue_one
    have hd' : ∀ᶠ z in 𝓝[≠] (1 : ℂ), DifferentiableAt ℂ zetaOne z := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact hd z hz
    exact (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hd'
      hc).differentiableAt
  · exact hd s hs

theorem zetaOne_eq_zero_iff {s : ℂ} : zetaOne s = 0 ↔ s ≠ 1 ∧ riemannZeta s = 0 := by
  rcases eq_or_ne s 1 with rfl | hs
  · simp [zetaOne_one]
  · rw [zetaOne_of_ne hs, mul_eq_zero, or_iff_right (sub_ne_zero.2 hs)]
    exact ⟨fun h ↦ ⟨hs, h⟩, fun h ↦ h.2⟩

/-- Away from `1`, `(s - 1) ζ(s)` vanishes to the same order as `ζ`. -/
theorem analyticOrderAt_zetaOne {s : ℂ} (hs : s ≠ 1) :
    analyticOrderAt zetaOne s = analyticOrderAt riemannZeta s := by
  rw [analyticOrderAt_congr (zetaOne_eventuallyEq hs)]
  have hA : AnalyticAt ℂ (fun z : ℂ ↦ z - 1) s := by fun_prop
  change analyticOrderAt ((fun z : ℂ ↦ z - 1) * riemannZeta) s = _
  rw [analyticOrderAt_mul hA (analyticOn_riemannZeta s hs),
    hA.analyticOrderAt_eq_zero.2 (sub_ne_zero.2 hs), zero_add]

/-! ### The integral `∫_1^∞ {t} t^{-s-1} dt` -/

/-- `∫_1^∞ t^{-s-1} {t} dt`. -/
def fractIntegral (s : ℂ) : ℂ := ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (-s - 1) * ((Int.fract t : ℝ) : ℂ)

theorem norm_cpow_mul_fract_le {t : ℝ} (ht : 1 < t) (s : ℂ) :
    ‖(t : ℂ) ^ (-s - 1) * ((Int.fract t : ℝ) : ℂ)‖ ≤ t ^ (-s.re - 1) := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Int.fract_nonneg t),
    Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
  have : (-s - 1).re = -s.re - 1 := by simp
  rw [this]
  calc t ^ (-s.re - 1) * Int.fract t ≤ t ^ (-s.re - 1) * 1 :=
        mul_le_mul_of_nonneg_left (Int.fract_lt_one t).le (Real.rpow_nonneg (by linarith) _)
    _ = _ := mul_one _

theorem aestronglyMeasurable_cpow_mul_fract (s : ℂ) (μ : Measure ℝ) :
    AEStronglyMeasurable (fun t : ℝ ↦ (t : ℂ) ^ (-s - 1) * ((Int.fract t : ℝ) : ℂ)) μ :=
  ((Complex.measurable_ofReal.pow_const _).mul
    (Complex.measurable_ofReal.comp measurable_fract)).aestronglyMeasurable

theorem integrableOn_cpow_mul_fract {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ (-s - 1) * ((Int.fract t : ℝ) : ℂ)) (Ioi 1) := by
  refine Integrable.mono' (integrableOn_Ioi_rpow_of_lt (a := -s.re - 1) (by linarith) one_pos)
    (aestronglyMeasurable_cpow_mul_fract s _) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact norm_cpow_mul_fract_le ht s

theorem norm_fractIntegral_le {s : ℂ} (hs : 0 < s.re) : ‖fractIntegral s‖ ≤ 1 / s.re := by
  unfold fractIntegral
  calc ‖∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (-s - 1) * ((Int.fract t : ℝ) : ℂ)‖
      ≤ ∫ t in Ioi (1 : ℝ), t ^ (-s.re - 1) :=
        norm_integral_le_of_norm_le (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos)
          (by
            filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
            exact norm_cpow_mul_fract_le ht s)
    _ = 1 / s.re := by
        rw [integral_Ioi_rpow_of_lt (by linarith) one_pos, Real.one_rpow]
        have : -s.re - 1 + 1 = -s.re := by ring
        rw [this]
        field_simp

/-- The function whose Mellin transform at `-s` is `fractIntegral s`. -/
def fractTail (t : ℝ) : ℂ := (Ioi (1 : ℝ)).indicator (fun t ↦ ((Int.fract t : ℝ) : ℂ)) t

theorem fractIntegral_eq_mellin (s : ℂ) : fractIntegral s = mellin fractTail (-s) := by
  unfold fractIntegral mellin
  have h : ∀ t : ℝ, (t : ℂ) ^ (-s - 1) • fractTail t =
      (Ioi (1 : ℝ)).indicator (fun t ↦ (t : ℂ) ^ (-s - 1) * ((Int.fract t : ℝ) : ℂ)) t := by
    intro t
    by_cases ht : t ∈ Ioi (1 : ℝ) <;> simp [fractTail, ht]
  simp_rw [h]
  rw [setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, max_eq_right zero_le_one]

theorem locallyIntegrable_fractTail : LocallyIntegrable fractTail := by
  rw [locallyIntegrable_iff]
  intro k hk
  refine Measure.integrableOn_of_bounded (M := 1) hk.measure_lt_top.ne ?_
    (Eventually.of_forall fun t ↦ ?_)
  · exact ((Complex.measurable_ofReal.comp measurable_fract).indicator
      measurableSet_Ioi).aestronglyMeasurable
  · unfold fractTail
    by_cases ht : t ∈ Ioi (1 : ℝ)
    · rw [indicator_of_mem ht, Complex.norm_real, Real.norm_of_nonneg (Int.fract_nonneg t)]
      exact (Int.fract_lt_one t).le
    · rw [indicator_of_notMem ht, norm_zero]
      exact zero_le_one

theorem differentiableAt_fractIntegral {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ fractIntegral s := by
  have hfun : fractIntegral = fun s ↦ mellin fractTail (-s) := funext fractIntegral_eq_mellin
  rw [hfun]
  have hm : DifferentiableAt ℂ (mellin fractTail) (-s) := by
    refine mellin_differentiableAt_of_isBigO_rpow (a := 0) (b := -s.re - 1)
      (locallyIntegrable_fractTail.locallyIntegrableOn _) ?_ (by simpa using hs) ?_ (by simp)
    · refine Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun t ↦ ?_)
      rw [neg_zero, Real.rpow_zero, norm_one, one_mul]
      unfold fractTail
      by_cases ht : t ∈ Ioi (1 : ℝ)
      · rw [indicator_of_mem ht, Complex.norm_real, Real.norm_of_nonneg (Int.fract_nonneg t)]
        exact (Int.fract_lt_one t).le
      · rw [indicator_of_notMem ht, norm_zero]
        exact zero_le_one
    · refine Asymptotics.IsBigO.of_bound 0 ?_
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
      unfold fractTail
      rw [indicator_of_notMem (by simp only [mem_Ioi, not_lt]; exact ht.2.le), norm_zero, zero_mul]
  exact hm.comp (f := fun z : ℂ ↦ -z) s differentiableAt_id.neg

/-! ### The representation of `ζ` in `Re s > 0` (Z1) -/

/-- For `Re s > 1`, `ζ(s) = s/(s - 1) - s ∫_1^∞ {t} t^{-s-1} dt`. -/
theorem riemannZeta_eq_fractIntegral {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = s / (s - 1) - s * fractIntegral s := by
  have hO : (fun n ↦ ∑ k ∈ Finset.Icc 1 n, ‖(1 : ℕ → ℂ) k‖) =O[atTop]
      fun n ↦ (n : ℝ) ^ (1 : ℝ) := by
    refine Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun n ↦ ?_)
    simp
  have hL := LSeries_eq_mul_integral' (1 : ℕ → ℂ) zero_le_one hs hO
  rw [LSeries_one_eq_riemannZeta hs] at hL
  rw [hL]
  have hfl : ∀ t ∈ Ioi (1 : ℝ), (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (1 : ℕ → ℂ) k) * (t : ℂ) ^ (-(s + 1)) =
      (t : ℂ) ^ (-s) - (t : ℂ) ^ (-s - 1) * ((Int.fract t : ℝ) : ℂ) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := by linarith [mem_Ioi.1 ht]
    have hsum : (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (1 : ℕ → ℂ) k) = ((⌊t⌋₊ : ℝ) : ℂ) := by simp
    have hfloor : ((⌊t⌋₊ : ℝ) : ℂ) = (t : ℂ) - ((Int.fract t : ℝ) : ℂ) := by
      rw [natCast_floor_eq_intCast_floor ht0.le, ← Int.self_sub_fract t]
      push_cast
      ring
    have hpow : (t : ℂ) ^ (-s) = (t : ℂ) * (t : ℂ) ^ (-s - 1) := by
      rw [show -s = 1 + (-s - 1) by ring, cpow_add _ _ (ofReal_ne_zero.2 ht0.ne'), cpow_one]
      ring_nf
    rw [hsum, hfloor, hpow, show -(s + 1) = -s - 1 by ring]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hfl,
    integral_sub (integrableOn_Ioi_cpow_of_lt (by simp; linarith) one_pos)
      (integrableOn_cpow_mul_fract (by linarith)),
    integral_Ioi_cpow_of_lt (by simp; linarith) one_pos]
  have hs1 : s - 1 ≠ 0 := fun h ↦ by
    have := congrArg re h
    simp at this
    linarith
  have hs1' : -s + 1 ≠ 0 := fun h ↦ hs1 (by linear_combination -h)
  unfold fractIntegral
  field_simp
  ring_nf
  simp

/-- (Z1): for `Re s > 0`, `(s - 1) ζ(s) = s - s (s - 1) ∫_1^∞ {t} t^{-s-1} dt`. -/
theorem zetaOne_eq {s : ℂ} (hs : 0 < s.re) :
    zetaOne s = s - s * (s - 1) * fractIntegral s := by
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  have hf : AnalyticOnNhd ℂ zetaOne {z : ℂ | 0 < z.re} := fun z _ ↦
    differentiable_zetaOne.analyticAt z
  have hg : AnalyticOnNhd ℂ (fun z ↦ z - z * (z - 1) * fractIntegral z) {z : ℂ | 0 < z.re} :=
    DifferentiableOn.analyticOnNhd (fun z hz ↦ (differentiableAt_id.sub
      ((differentiableAt_id.mul (differentiableAt_id.sub_const 1)).mul
        (differentiableAt_fractIntegral hz))).differentiableWithinAt) hU
  have heq : zetaOne =ᶠ[𝓝 (2 : ℂ)] fun z ↦ z - z * (z - 1) * fractIntegral z := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
    have hz1 : z ≠ 1 := fun h ↦ by rw [h, one_re] at hz; exact lt_irrefl 1 hz
    have hz10 : z - 1 ≠ 0 := sub_ne_zero.2 hz1
    rw [zetaOne_of_ne hz1, riemannZeta_eq_fractIntegral hz]
    field_simp
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg (convex_halfSpace_re_gt 0).isPreconnected
    (show (2 : ℂ) ∈ {z : ℂ | 0 < z.re} by norm_num) heq hs

/-- (Z1): `‖(s - 1) ζ(s)‖ ≤ ‖s‖ (1 + ‖s - 1‖ / Re s)` for `Re s > 0`. -/
theorem norm_zetaOne_le {s : ℂ} (hs : 0 < s.re) :
    ‖zetaOne s‖ ≤ ‖s‖ * (1 + ‖s - 1‖ / s.re) := by
  rw [zetaOne_eq hs]
  calc ‖s - s * (s - 1) * fractIntegral s‖ ≤ ‖s‖ + ‖s‖ * ‖s - 1‖ * ‖fractIntegral s‖ := by
        refine (norm_sub_le _ _).trans (le_of_eq ?_)
        rw [norm_mul, norm_mul]
    _ ≤ ‖s‖ + ‖s‖ * ‖s - 1‖ * (1 / s.re) := by
        gcongr
        exact norm_fractIntegral_le hs
    _ = ‖s‖ * (1 + ‖s - 1‖ / s.re) := by ring

/-- (Z1): `‖ζ(s)‖ ≤ ‖s‖/‖s - 1‖ + ‖s‖ / Re s` for `Re s > 0`, `s ≠ 1`. -/
theorem norm_riemannZeta_le {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    ‖riemannZeta s‖ ≤ ‖s‖ / ‖s - 1‖ + ‖s‖ / s.re := by
  have h1 : 0 < ‖s - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hs1)
  have h := norm_zetaOne_le hs
  rw [zetaOne_of_ne hs1, norm_mul] at h
  calc ‖riemannZeta s‖ = ‖s - 1‖ * ‖riemannZeta s‖ / ‖s - 1‖ :=
        (mul_div_cancel_left₀ _ h1.ne').symm
    _ ≤ ‖s‖ * (1 + ‖s - 1‖ / s.re) / ‖s - 1‖ := by gcongr
    _ = ‖s‖ / ‖s - 1‖ + ‖s‖ / s.re := by field_simp

/-! ### A lower bound on `Re s = 2` (Z2) -/

/-- (Z2): `‖ζ(2 + it)‖ ≥ 2 - π²/6 ≥ 1/3`. -/
theorem norm_riemannZeta_two_add_ge (t : ℝ) : 1 / 3 ≤ ‖riemannZeta (2 + t * I)‖ := by
  set s : ℂ := 2 + t * I with hsdef
  have hs : 1 < s.re := by simp [hsdef]
  set f : ℕ → ℂ := fun n ↦ 1 / ((n : ℂ) + 1) ^ s with hf
  have hnorm : ∀ n : ℕ, ‖f n‖ = 1 / ((n : ℝ) + 1) ^ 2 := by
    intro n
    have hpos : (0 : ℝ) < n + 1 := by positivity
    simp only [hf]
    rw [norm_div, norm_one, show ((n : ℂ) + 1) = ((n + 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos hpos]
    have : s.re = 2 := by simp [hsdef]
    rw [this]
    norm_cast
  have hreal : HasSum (fun n : ℕ ↦ 1 / ((n : ℝ) + 1) ^ 2) (π ^ 2 / 6) := by
    have h := (hasSum_nat_add_iff' 1).2 hasSum_zeta_two
    simpa using h
  have hsummf : Summable fun n ↦ ‖f n‖ := by simpa only [hnorm] using hreal.summable
  have hz : riemannZeta s = f 0 + ∑' n, f (n + 1) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
    exact hsummf.of_norm.tsum_eq_zero_add
  have hf0 : f 0 = 1 := by simp [hf]
  have htail : ‖∑' n, f (n + 1)‖ ≤ π ^ 2 / 6 - 1 := by
    have hsn : Summable fun n ↦ ‖f (n + 1)‖ := (summable_nat_add_iff 1).2 hsummf
    have h1 : ∑' n, ‖f n‖ = ‖f 0‖ + ∑' n, ‖f (n + 1)‖ := hsummf.tsum_eq_zero_add
    have h2 : ∑' n, ‖f n‖ = π ^ 2 / 6 := by simp only [hnorm]; exact hreal.tsum_eq
    rw [hf0, norm_one] at h1
    calc ‖∑' n, f (n + 1)‖ ≤ ∑' n, ‖f (n + 1)‖ := norm_tsum_le_tsum_norm hsn
      _ = π ^ 2 / 6 - 1 := by linarith
  have hpi : π ^ 2 / 6 ≤ 5 / 3 := by
    have := Real.pi_lt_d2
    nlinarith [Real.pi_pos]
  rw [hz, hf0]
  have htri := norm_sub_le (1 + ∑' n, f (n + 1)) (∑' n, f (n + 1))
  rw [add_sub_cancel_right, norm_one] at htri
  linarith

/-! ### The symmetry of the zeros (Z3) -/

/-- (Z3): in the critical strip, `ζ` vanishes to the same order at `s` and at `1 - s`. -/
theorem analyticOrderAt_riemannZeta_one_sub {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    analyticOrderAt riemannZeta (1 - s) = analyticOrderAt riemannZeta s := by
  have h0' : 0 < (1 - s).re := by simp; linarith
  have h1' : (1 - s).re < 1 := by simp; linarith
  rw [← analyticOrderAt_riemannXi h0' h1', ← analyticOrderAt_riemannXi h0 h1]
  have hg : AnalyticAt ℂ (fun z : ℂ ↦ 1 - z) s := by fun_prop
  have hg' : deriv (fun z : ℂ ↦ 1 - z) s ≠ 0 := by
    rw [((hasDerivAt_id' s).const_sub (1 : ℂ)).deriv]
    norm_num
  have h := analyticOrderAt_comp_of_deriv_ne_zero (f := riemannXi) hg hg'
  have hcomp : riemannXi ∘ (fun z : ℂ ↦ 1 - z) = riemannXi :=
    funext fun z ↦ riemannXi_one_sub z
  rw [hcomp] at h
  exact h.symm

/-- (Z3): in the critical strip, `ζ` vanishes to the same order at `s` and at `1 - s̄`. -/
theorem analyticOrderAt_riemannZeta_one_sub_conj {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    analyticOrderAt riemannZeta (1 - conj s) = analyticOrderAt riemannZeta s := by
  rw [analyticOrderAt_riemannZeta_one_sub (by simpa using h0) (by simpa using h1),
    analyticOrderAt_riemannZeta_conj (ne_one_of_re_lt_one h1)]

theorem riemannZeta_one_sub_conj_eq_zero_iff {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    riemannZeta (1 - conj s) = 0 ↔ riemannZeta s = 0 := by
  have hs1 := ne_one_of_re_lt_one h1
  have hs1' : 1 - conj s ≠ 1 := ne_one_of_re_lt_one (by simp; linarith)
  have e1 := (analyticOn_riemannZeta s hs1).analyticOrderAt_eq_zero
  have e2 := (analyticOn_riemannZeta (1 - conj s) hs1').analyticOrderAt_eq_zero
  rw [analyticOrderAt_riemannZeta_one_sub_conj h0 h1] at e2
  exact not_iff_not.mp (e2.symm.trans e1)

theorem zetaOrder_one_sub_conj {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    zetaOrder (1 - conj s) = zetaOrder s := by
  have hs1 := ne_one_of_re_lt_one h1
  have hs1' : 1 - conj s ≠ 1 := ne_one_of_re_lt_one (by simp; linarith)
  rw [zetaOrder_eq hs1, zetaOrder_eq hs1']
  unfold analyticOrderNatAt
  rw [analyticOrderAt_riemannZeta_one_sub_conj h0 h1]

end WeilExplicitFormula
