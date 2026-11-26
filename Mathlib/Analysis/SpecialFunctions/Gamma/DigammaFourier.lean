/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Harald Helfgott
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.DigammaSeries
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! # The truncated Fourier transform of `ψ(a + ibt)`

Let `a, b > 0` and `G(t) = ψ(a + ibt)`, where `ψ = Γ'/Γ`. We prove Montgomery–Vaughan,
*Multiplicative Number Theory I*, Theorem C.5: for `x ≠ 0` and `T ≥ 1`,
`∫_{-T}^{T} G(t) e(-xt) dt = -G(T) e(-xT)/(2πix) + G(-T) e(xT)/(2πix)
  - [x < 0] (2π/b) e^{2πax/b} / (1 - e^{2πx/b}) + O(x⁻² T⁻¹)`,
where `e(θ) = e^{2πiθ}` and the implied constant depends only on `a` and `b`
(`Complex.norm_integral_digamma_line_mul_cexp_sub_le`).

Montgomery–Vaughan prove this by the calculus of residues. Here we integrate by parts twice
instead, and evaluate the remaining integral `∫_ℝ G''(t) e(-xt) dt` by Fourier inversion: by
`Complex.deriv_deriv_digamma_eq_integral`, `G''` is the Fourier transform of the integrable
function `digammaFourierKernel a b`, `v ↦ (2π)³/b · v² e^{-2πav/b} / (1 - e^{-2πv/b})` for
`v > 0` and `0` for `v ≤ 0` (`Complex.fourier_digammaFourierKernel`).

## AI usage

This file was written by Claude (Anthropic) in November 2026. It compiles, but has not been
reviewed by a human.
-/

@[expose] public section

open Filter Topology Set MeasureTheory Real FourierTransform

noncomputable section

namespace Complex

variable {a b : ℝ}

/-! ### `ψ` along a vertical line -/

theorem re_ofReal_add_mul_I_pos (ha : 0 < a) (b t : ℝ) : 0 < ((a : ℂ) + b * t * I).re := by
  simpa using ha

theorem hasDerivAt_ofReal_add_mul_I (a b t : ℝ) :
    HasDerivAt (fun t : ℝ ↦ (a : ℂ) + b * t * I) (b * I) t := by
  have := ((((hasDerivAt_id (t : ℂ)).const_mul (b : ℂ)).mul_const I).const_add (a : ℂ)).comp_ofReal
  simpa using this

/-- `G(t) = ψ(a + ibt)` has derivative `ψ'(a + ibt) · ib`. -/
theorem hasDerivAt_digamma_line (ha : 0 < a) (b t : ℝ) :
    HasDerivAt (fun t : ℝ ↦ digamma (a + b * t * I)) (deriv digamma (a + b * t * I) * (b * I)) t :=
  (hasDerivAt_digamma (re_ofReal_add_mul_I_pos ha b t)).comp t (hasDerivAt_ofReal_add_mul_I a b t)

theorem hasDerivAt_deriv_digamma_line (ha : 0 < a) (b t : ℝ) :
    HasDerivAt (fun t : ℝ ↦ deriv digamma (a + b * t * I) * (b * I))
      (deriv (deriv digamma) (a + b * t * I) * (b * I) * (b * I)) t :=
  ((hasDerivAt_deriv_digamma (re_ofReal_add_mul_I_pos ha b t)).comp t
    (hasDerivAt_ofReal_add_mul_I a b t)).mul_const _

theorem continuous_deriv_digamma_line (ha : 0 < a) (b : ℝ) :
    Continuous fun t : ℝ ↦ deriv digamma (a + b * t * I) * (b * I) :=
  continuous_iff_continuousAt.2 fun t ↦ (hasDerivAt_deriv_digamma_line ha b t).continuousAt

theorem continuous_deriv_deriv_digamma_line (ha : 0 < a) (b : ℝ) :
    Continuous fun t : ℝ ↦ deriv (deriv digamma) (a + b * t * I) * (b * I) * (b * I) := by
  refine continuous_iff_continuousAt.2 fun t ↦ ?_
  have hc : ContinuousAt (fun t : ℝ ↦ (a : ℂ) + b * t * I) t :=
    (hasDerivAt_ofReal_add_mul_I a b t).continuousAt
  have hd : ContinuousAt (deriv (deriv digamma)) ((a : ℂ) + b * t * I) :=
    (analyticOnNhd_digamma.deriv.deriv _ (re_ofReal_add_mul_I_pos ha b t)).continuousAt
  have h : ContinuousAt (fun t : ℝ ↦ deriv (deriv digamma) ((a : ℂ) + b * t * I)) t :=
    ContinuousAt.comp (g := deriv (deriv digamma)) (f := fun t : ℝ ↦ (a : ℂ) + b * t * I) hd hc
  exact (h.mul continuousAt_const).mul continuousAt_const

/-- `|G'(t)| ≤ K / |t|` with `K = 2 (1/m² + 1/m)`, `m = min a 1`. -/
theorem norm_deriv_digamma_line_le (ha : 0 < a) (hb : 0 < b) (t : ℝ) :
    ‖deriv digamma (a + b * t * I) * (b * I)‖ * |t| ≤ 2 * (1 / min a 1 ^ 2 + 1 / min a 1) := by
  have h := norm_deriv_digamma_le' ha (b * t)
  push_cast at h
  rw [norm_mul, norm_mul, norm_I, mul_one, norm_real, Real.norm_of_nonneg hb.le]
  set K := 2 * (1 / min a 1 ^ 2 + 1 / min a 1)
  have hK : 0 ≤ K := by positivity
  rw [abs_mul, abs_of_pos hb] at h
  calc ‖deriv digamma (a + b * t * I)‖ * b * |t| = ‖deriv digamma (a + b * t * I)‖ * (b * |t|) := by
        ring
    _ ≤ K / (1 + b * |t|) * (b * |t|) := by gcongr
    _ ≤ K := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith [abs_nonneg t]

/-- `|G''(t)| ≤ C / (1 + |t|)²` with `C = 8b² (1/m³ + 1/(2m²))`, `m = min a b`. -/
theorem norm_deriv_deriv_digamma_line_le (ha : 0 < a) (hb : 0 < b) (t : ℝ) :
    ‖deriv (deriv digamma) (a + b * t * I) * (b * I) * (b * I)‖ ≤
      8 * b ^ 2 * (1 / min a b ^ 3 + 1 / (2 * min a b ^ 2)) / (1 + |t|) ^ 2 := by
  have h := norm_deriv_deriv_digamma_le ha (b * t)
  push_cast at h
  rw [abs_mul, abs_of_pos hb] at h
  set m := min a b
  have hm : 0 < m := lt_min ha hb
  have h1 : m * (1 + |t|) ≤ a + b * |t| := by
    have := min_le_left a b; have := min_le_right a b
    nlinarith [abs_nonneg t]
  have hp : 0 < m * (1 + |t|) := by positivity
  rw [norm_mul, norm_mul, norm_mul, norm_I, mul_one, norm_real, Real.norm_of_nonneg hb.le]
  have e3 : 1 / (a + b * |t|) ^ 3 ≤ 1 / m ^ 3 / (1 + |t|) ^ 2 := by
    rw [div_div]
    refine one_div_le_one_div_of_le (by positivity) ?_
    calc m ^ 3 * (1 + |t|) ^ 2 ≤ m ^ 3 * (1 + |t|) ^ 3 := by
          gcongr
          · exact le_add_of_nonneg_right (abs_nonneg t)
          · norm_num
      _ = (m * (1 + |t|)) ^ 3 := by ring
      _ ≤ (a + b * |t|) ^ 3 := by gcongr
  have e2 : 1 / (2 * (a + b * |t|) ^ 2) ≤ 1 / (2 * m ^ 2) / (1 + |t|) ^ 2 := by
    rw [div_div]
    refine one_div_le_one_div_of_le (by positivity) ?_
    calc 2 * m ^ 2 * (1 + |t|) ^ 2 = 2 * (m * (1 + |t|)) ^ 2 := by ring
      _ ≤ 2 * (a + b * |t|) ^ 2 := by gcongr
  calc ‖deriv (deriv digamma) (a + b * t * I)‖ * b * b
      ≤ 8 * (1 / (a + b * |t|) ^ 3 + 1 / (2 * (a + b * |t|) ^ 2)) * b * b := by gcongr
    _ ≤ 8 * (1 / m ^ 3 / (1 + |t|) ^ 2 + 1 / (2 * m ^ 2) / (1 + |t|) ^ 2) * b * b := by gcongr
    _ = 8 * b ^ 2 * (1 / m ^ 3 + 1 / (2 * m ^ 2)) / (1 + |t|) ^ 2 := by ring

theorem integrable_deriv_deriv_digamma_line (ha : 0 < a) (hb : 0 < b) :
    Integrable fun t : ℝ ↦ deriv (deriv digamma) (a + b * t * I) * (b * I) * (b * I) := by
  set C := 8 * b ^ 2 * (1 / min a b ^ 3 + 1 / (2 * min a b ^ 2))
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul C)
    (continuous_deriv_deriv_digamma_line ha b).aestronglyMeasurable
    (Eventually.of_forall fun t ↦ ?_)
  refine (norm_deriv_deriv_digamma_line_le ha hb t).trans ?_
  rw [div_eq_mul_inv]
  gcongr
  nlinarith [abs_nonneg t, sq_abs t]

/-! ### The kernel whose Fourier transform is `ψ''(a + ibt)` -/

/-- The function `v ↦ (2π)³/b · v² e^{-2πav/b} / (1 - e^{-2πv/b})` on `v > 0`, extended by `0`.
Its Fourier transform is `t ↦ -b² ψ''(a + ibt)` (`fourier_digammaFourierKernel`). -/
def digammaFourierKernel (a b : ℝ) : ℝ → ℂ :=
  indicator (Ioi 0) fun v ↦ (((2 * π) ^ 3 / b * v ^ 2 * Real.exp (-(2 * π * a * v / b)) /
    (1 - Real.exp (-(2 * π * v / b))) : ℝ) : ℂ)

theorem one_sub_exp_neg_pos {y : ℝ} (hy : 0 < y) : 0 < 1 - Real.exp (-y) := by
  have := Real.exp_lt_one_iff.2 (neg_neg_of_pos hy)
  linarith

/-- `1 - e^{-y} ≥ y / (1 + y)` for `y ≥ 0`. -/
theorem div_one_add_le_one_sub_exp_neg {y : ℝ} (hy : 0 ≤ y) : y / (1 + y) ≤ 1 - Real.exp (-y) := by
  have h1 : 1 + y ≤ Real.exp y := by linarith [Real.add_one_le_exp y]
  have h2 : Real.exp (-y) ≤ 1 / (1 + y) := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by positivity) h1
  have h3 : y / (1 + y) = 1 - 1 / (1 + y) := by field_simp; ring
  linarith

theorem fourier_digammaFourierKernel (ha : 0 < a) (hb : 0 < b) (t : ℝ) :
    𝓕 (digammaFourierKernel a b) t =
      deriv (deriv digamma) (a + b * t * I) * (b * I) * (b * I) := by
  have hc : 0 < b / (2 * π) := by positivity
  set H : ℝ → ℂ := fun v ↦ (((2 * π) ^ 3 / b * v ^ 2 * Real.exp (-(2 * π * a * v / b)) /
    (1 - Real.exp (-(2 * π * v / b))) : ℝ) : ℂ) with hH
  rw [fourier_real_eq_integral_exp_smul]
  have h1 : (fun v : ℝ ↦ cexp (↑(-2 * π * v * t) * I) • digammaFourierKernel a b v) =
      indicator (Ioi 0) fun v ↦ cexp (↑(-2 * π * v * t) * I) * H v := by
    funext v
    by_cases hv : v ∈ Ioi (0 : ℝ) <;> simp [digammaFourierKernel, hv, hH]
  rw [h1, integral_indicator measurableSet_Ioi]
  -- substitute `v = (b / (2π)) u`
  have h2 := integral_comp_mul_left_Ioi (fun v ↦ cexp (↑(-2 * π * v * t) * I) * H v) 0 hc
  rw [mul_zero] at h2
  rw [show (∫ v in Ioi (0 : ℝ), cexp (↑(-2 * π * v * t) * I) * H v) =
      (b / (2 * π)) • ∫ u in Ioi (0 : ℝ), cexp (↑(-2 * π * (b / (2 * π) * u) * t) * I) *
        H (b / (2 * π) * u) by
    rw [h2, smul_smul, mul_inv_cancel₀ hc.ne', one_smul]]
  have h3 : ∀ u ∈ Ioi (0 : ℝ), (b / (2 * π) : ℝ) • (cexp (↑(-2 * π * (b / (2 * π) * u) * t) * I) *
      H (b / (2 * π) * u)) = (b : ℂ) ^ 2 * ((u : ℂ) ^ 2 * cexp (-((a + b * t * I) * u)) /
        (1 - cexp (-(u : ℂ)))) := by
    intro u hu
    have hu' : 0 < u := hu
    have hd : 1 - Real.exp (-u) ≠ 0 := (one_sub_exp_neg_pos hu').ne'
    have e1 : -(2 * π * a * (b / (2 * π) * u) / b) = -(a * u) := by field_simp
    have e2 : -(2 * π * (b / (2 * π) * u) / b) = -u := by field_simp
    have e3 : (-2 * π * (b / (2 * π) * u) * t : ℝ) = -(b * u * t) := by field_simp
    simp only [hH, e1, e2, e3]
    have hd' : (1 : ℂ) - cexp (-(u : ℂ)) ≠ 0 := by
      rw [← ofReal_neg, ← ofReal_exp, ← ofReal_one, ← ofReal_sub]
      exact_mod_cast hd
    rw [real_smul]
    push_cast
    rw [show -(((a : ℂ) + b * t * I) * u) = -(a * u) + -(b * u * t) * I by ring, Complex.exp_add]
    field_simp
  rw [← integral_smul, setIntegral_congr_fun measurableSet_Ioi h3, integral_const_mul,
    deriv_deriv_digamma_eq_integral (re_ofReal_add_mul_I_pos ha b t)]
  have key : ∀ X : ℂ, (b : ℂ) ^ 2 * X = (-X) * (b * I) * (b * I) := fun X ↦ by
    ring_nf; rw [I_sq]; ring
  exact key _

theorem integrable_digammaFourierKernel (hb : 0 < b) (ha : 0 < a) :
    Integrable (digammaFourierKernel a b) := by
  rw [digammaFourierKernel, integrable_indicator_iff measurableSet_Ioi]
  set α := 2 * π * a / b
  have hα : 0 < α := by positivity
  have h1 : IntegrableOn (fun v : ℝ ↦ v ^ (1 : ℝ) * Real.exp (-α * v ^ (1 : ℝ))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) le_rfl hα
  have h2 : IntegrableOn (fun v : ℝ ↦ v ^ (2 : ℝ) * Real.exp (-α * v ^ (1 : ℝ))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) le_rfl hα
  have hg : IntegrableOn (fun v : ℝ ↦ (2 * π) ^ 2 * (v ^ (1 : ℝ) * Real.exp (-α * v ^ (1 : ℝ))) +
      (2 * π) ^ 2 * (2 * π / b) * (v ^ (2 : ℝ) * Real.exp (-α * v ^ (1 : ℝ)))) (Ioi 0) :=
    (h1.const_mul _).add (h2.const_mul _)
  refine Integrable.mono' hg ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable (fun v hv ↦ ?_) measurableSet_Ioi
    have hv' : (0 : ℝ) < v := hv
    have hd : 1 - Real.exp (-(2 * π * v / b)) ≠ 0 := (one_sub_exp_neg_pos (by positivity)).ne'
    exact (continuous_ofReal.continuousAt.comp (by fun_prop (disch := exact hd))).continuousWithinAt
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun v hv ↦ ?_)
    have hv' : (0 : ℝ) < v := hv
    set y := 2 * π * v / b
    have hy : 0 < y := by positivity
    have hden := div_one_add_le_one_sub_exp_neg hy.le
    have hden0 : 0 < 1 - Real.exp (-y) := one_sub_exp_neg_pos hy
    rw [norm_real, Real.norm_of_nonneg (by positivity)]
    try simp only [Real.rpow_one, Real.rpow_two]
    have hexp : Real.exp (-(2 * π * a * v / b)) = Real.exp (-α * v) := by
      congr 1; simp only [α]; ring
    rw [hexp, div_le_iff₀ hden0]
    calc (2 * π) ^ 3 / b * v ^ 2 * Real.exp (-α * v) =
          ((2 * π) ^ 2 * (v * Real.exp (-α * v)) +
            (2 * π) ^ 2 * (2 * π / b) * (v ^ 2 * Real.exp (-α * v))) * (y / (1 + y)) := by
          simp only [y]
          field_simp
      _ ≤ ((2 * π) ^ 2 * (v * Real.exp (-α * v)) +
            (2 * π) ^ 2 * (2 * π / b) * (v ^ 2 * Real.exp (-α * v))) * (1 - Real.exp (-y)) := by
          gcongr

theorem continuousAt_digammaFourierKernel (hb : 0 < b) {y : ℝ} (hy : y ≠ 0) :
    ContinuousAt (digammaFourierKernel a b) y := by
  rcases hy.lt_or_gt with hy | hy
  · have : digammaFourierKernel a b =ᶠ[𝓝 y] fun _ ↦ 0 := by
      filter_upwards [Iio_mem_nhds hy] with v hv
      have hv' : v ∉ Ioi (0 : ℝ) := fun h ↦ lt_asymm (show v < 0 from hv) h
      simp [digammaFourierKernel, indicator_of_notMem hv']
    exact continuousAt_const.congr this.symm
  · have hd : 1 - Real.exp (-(2 * π * y / b)) ≠ 0 := (one_sub_exp_neg_pos (by positivity)).ne'
    have hc : ContinuousAt (fun v : ℝ ↦ (((2 * π) ^ 3 / b * v ^ 2 *
        Real.exp (-(2 * π * a * v / b)) / (1 - Real.exp (-(2 * π * v / b))) : ℝ) : ℂ)) y :=
      continuous_ofReal.continuousAt.comp (by fun_prop (disch := exact hd))
    refine hc.congr ?_
    filter_upwards [Ioi_mem_nhds hy] with v hv
    simp [digammaFourierKernel, hv]

/-- **Fourier inversion**: `∫_ℝ G''(t) e(-xt) dt = h(-x)` where `h = digammaFourierKernel a b`. -/
theorem integral_deriv_deriv_digamma_line_mul_cexp (ha : 0 < a) (hb : 0 < b) {x : ℝ}
    (hx : x ≠ 0) :
    ∫ t : ℝ, deriv (deriv digamma) (a + b * t * I) * (b * I) * (b * I) *
      cexp (-(2 * π * x * t) * I) = digammaFourierKernel a b (-x) := by
  have hF : 𝓕 (digammaFourierKernel a b) =
      fun t : ℝ ↦ deriv (deriv digamma) (a + b * t * I) * (b * I) * (b * I) :=
    funext (fourier_digammaFourierKernel ha hb)
  have h := (integrable_digammaFourierKernel hb ha).fourierInv_fourier_eq
    (hF ▸ integrable_deriv_deriv_digamma_line ha hb)
    (continuousAt_digammaFourierKernel hb (neg_ne_zero.2 hx))
  rw [fourierInv_eq_fourier_neg, neg_neg, fourier_real_eq_integral_exp_smul, hF] at h
  rw [← h]
  congr 1
  funext t
  rw [smul_eq_mul, mul_comm]
  congr 2
  push_cast
  ring

/-- The main term in Theorem C.5. -/
theorem digammaFourierKernel_neg_div_sq (hb : 0 < b) {x : ℝ} (hx : x ≠ 0) :
    digammaFourierKernel a b (-x) / (2 * π * x * I) ^ 2 =
      if x < 0 then -(((2 * π / b) * (Real.exp (2 * π * a * x / b) /
        (1 - Real.exp (2 * π * x / b))) : ℝ) : ℂ) else 0 := by
  have hω : (2 * π * x * I : ℂ) ^ 2 = -(4 * π ^ 2 * x ^ 2 : ℝ) := by
    push_cast; ring_nf; rw [I_sq]; ring
  split_ifs with hneg
  · have hpos : -x ∈ Ioi (0 : ℝ) := neg_pos.2 hneg
    rw [digammaFourierKernel, indicator_of_mem hpos, hω, div_neg, neg_inj, ← ofReal_div,
      ofReal_inj]
    have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
    have hd : 1 - Real.exp (2 * π * x / b) ≠ 0 := by
      have : Real.exp (2 * π * x / b) < 1 := Real.exp_lt_one_iff.2 (by
        have : 2 * π * x < 0 := by nlinarith [Real.pi_pos]
        exact div_neg_of_neg_of_pos this hb)
      linarith
    have e1 : -(2 * π * a * -x / b) = 2 * π * a * x / b := by ring
    have e2 : -(2 * π * -x / b) = 2 * π * x / b := by ring
    rw [e1, e2, neg_sq]
    field_simp
    ring
  · have hnpos : -x ∉ Ioi (0 : ℝ) := by simp only [mem_Ioi, neg_pos]; exact hneg
    rw [digammaFourierKernel, indicator_of_notMem hnpos, zero_div]

/-- A tail bound: if `‖f t‖ ≤ C/(1 + |t|)²`, then `‖∫_{-T}^{T} f - ∫_ℝ f‖ ≤ 2C/T`. -/
theorem norm_intervalIntegral_sub_integral_le {f : ℝ → ℂ} {C T : ℝ} (hf : Integrable f)
    (hT : 0 < T) (hbound : ∀ t, ‖f t‖ ≤ C / (1 + |t|) ^ 2) :
    ‖(∫ t in -T..T, f t) - ∫ t, f t‖ ≤ 2 * C / T := by
  have hC : 0 ≤ C := by
    have := (norm_nonneg _).trans (hbound 0)
    simpa using this
  have htail : ∀ g : ℝ → ℂ, Integrable g → (∀ t, ‖g t‖ ≤ C / (1 + |t|) ^ 2) →
      ‖∫ t in Ioi T, g t‖ ≤ C / T := by
    intro g hg hgb
    have hint : IntegrableOn (fun t : ℝ ↦ C * t ^ (-2 : ℝ)) (Ioi T) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) hT).const_mul C
    have hval : ∫ t in Ioi T, C * t ^ (-2 : ℝ) = C / T := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hT]
      norm_num
      rw [Real.rpow_neg_one]
      ring
    rw [← hval]
    refine norm_integral_le_of_norm_le hint ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht ↦ ?_)
    have ht' : 0 < t := lt_trans hT ht
    refine (hgb t).trans ?_
    rw [Real.rpow_neg ht'.le, Real.rpow_two, ← div_eq_mul_inv]
    gcongr
    rw [abs_of_pos ht']
    linarith
  have h1 := hf.integrableOn (s := Iic T)
  have h2 := hf.integrableOn (s := Ioi T)
  have h3 := hf.integrableOn (s := Iic (-T))
  rw [← intervalIntegral.integral_Iic_sub_Iic h3 h1, ← intervalIntegral.integral_Iic_add_Ioi h1 h2]
  have e : (∫ t in Iic T, f t) - (∫ t in Iic (-T), f t) - ((∫ t in Iic T, f t) + ∫ t in Ioi T, f t)
      = -((∫ t in Ioi T, f (-t)) + ∫ t in Ioi T, f t) := by
    rw [integral_comp_neg_Ioi]
    ring
  rw [e, norm_neg]
  calc ‖(∫ t in Ioi T, f (-t)) + ∫ t in Ioi T, f t‖
      ≤ ‖∫ t in Ioi T, f (-t)‖ + ‖∫ t in Ioi T, f t‖ := norm_add_le _ _
    _ ≤ C / T + C / T := by
        gcongr
        · exact htail (fun t ↦ f (-t)) hf.comp_neg fun t ↦ by simpa using hbound (-t)
        · exact htail f hf hbound
    _ = 2 * C / T := by ring

theorem norm_cexp_neg_mul_I (x t : ℝ) : ‖cexp (-(2 * π * x * t) * I)‖ = 1 := by
  rw [show -(2 * (π : ℂ) * x * t) * I = ((-(2 * π * x * t) : ℝ) : ℂ) * I by push_cast; ring]
  exact norm_exp_ofReal_mul_I _

/-! ### Theorem C.5 -/

/-- **Montgomery–Vaughan, Theorem C.5**, with the main term written as `h(-x)/(2πix)²`, where
`h = digammaFourierKernel a b` (see `digammaFourierKernel_neg_div_sq`). -/
theorem norm_integral_digamma_line_mul_cexp_sub_le' (ha : 0 < a) (hb : 0 < b) :
    ∃ C, ∀ x : ℝ, x ≠ 0 → ∀ T : ℝ, 1 ≤ T →
      ‖(∫ t in -T..T, digamma (a + b * t * I) * cexp (-(2 * π * x * t) * I)) -
        (-(digamma (a + b * T * I) * cexp (-(2 * π * x * T) * I)) / (2 * π * x * I) +
          digamma (a + b * (-T) * I) * cexp (-(2 * π * x * (-T)) * I) / (2 * π * x * I) +
          digammaFourierKernel a b (-x) / (2 * π * x * I) ^ 2)‖ ≤ C / (x ^ 2 * T) := by
  set K₁ := 2 * (1 / min a 1 ^ 2 + 1 / min a 1) with hK₁
  set C₂ := 8 * b ^ 2 * (1 / min a b ^ 3 + 1 / (2 * min a b ^ 2)) with hC₂
  have hK₁0 : 0 ≤ K₁ := by positivity
  have hC₂0 : 0 ≤ C₂ := by positivity
  refine ⟨(2 * K₁ + 2 * C₂) / (4 * π ^ 2), fun x hx T hT ↦ ?_⟩
  have hT0 : 0 < T := by linarith
  have hπ : (0 : ℝ) < π := Real.pi_pos
  set ω : ℂ := 2 * π * x * I with hω_def
  have hω : ω ≠ 0 := by
    rw [hω_def]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero (ofReal_ne_zero.2 hπ.ne'))
      (ofReal_ne_zero.2 hx)) I_ne_zero
  have hnω : ‖ω‖ = 2 * π * |x| := by
    rw [hω_def, norm_mul, norm_mul, norm_mul, norm_I, mul_one, norm_real, norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hπ, Complex.norm_two]
  have hE : ∀ t : ℝ, HasDerivAt (fun t : ℝ ↦ cexp (-(2 * π * x * t) * I))
      (cexp (-(2 * π * x * t) * I) * (-ω)) t := by
    intro t
    have h := ((((hasDerivAt_id (t : ℂ)).const_mul (-(2 * π * x : ℂ))).mul_const I).cexp)
      |>.comp_ofReal
    convert h using 1
    · funext s
      simp only [id_eq]
      ring_nf
    · rw [hω_def]
      simp only [id_eq, mul_one]
      ring_nf
  have hV : ∀ t : ℝ, HasDerivAt (fun t : ℝ ↦ -cexp (-(2 * π * x * t) * I) / ω)
      (cexp (-(2 * π * x * t) * I)) t := by
    intro t
    convert (hE t).neg.div_const ω using 1
    field_simp
  have cE : Continuous fun t : ℝ ↦ cexp (-(2 * π * x * t) * I) := by fun_prop
  have ibp1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := -T) (b := T)
    (fun t _ ↦ hasDerivAt_digamma_line ha b t) (fun t _ ↦ hV t)
    ((continuous_deriv_digamma_line ha b).intervalIntegrable _ _) (cE.intervalIntegrable _ _)
  have ibp2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := -T) (b := T)
    (fun t _ ↦ hasDerivAt_deriv_digamma_line ha b t) (fun t _ ↦ hV t)
    ((continuous_deriv_deriv_digamma_line ha b).intervalIntegrable _ _) (cE.intervalIntegrable _ _)
  have hVint : ∀ F : ℝ → ℂ, ∫ t in -T..T, F t * (-cexp (-(2 * π * x * t) * I) / ω) =
      -(1 / ω) * ∫ t in -T..T, F t * cexp (-(2 * π * x * t) * I) := by
    intro F
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext t
    ring
  rw [hVint] at ibp1 ibp2
  push_cast at ibp1 ibp2
  -- the integral of `G'' e(-xt)` over `ℝ`, and the tail
  have hint : Integrable fun t : ℝ ↦
      deriv (deriv digamma) (a + b * t * I) * (b * I) * (b * I) * cexp (-(2 * π * x * t) * I) := by
    refine Integrable.mono' (integrable_deriv_deriv_digamma_line ha hb).norm
      ((continuous_deriv_deriv_digamma_line ha b).mul cE).aestronglyMeasurable
      (Eventually.of_forall fun t ↦ ?_)
    rw [norm_mul, norm_cexp_neg_mul_I, mul_one]
  have htail := norm_intervalIntegral_sub_integral_le hint hT0 fun t ↦ by
    rw [norm_mul, norm_cexp_neg_mul_I, mul_one]
    exact norm_deriv_deriv_digamma_line_le ha hb t
  rw [integral_deriv_deriv_digamma_line_mul_cexp ha hb hx] at htail
  set I₂ := ∫ t in -T..T, deriv (deriv digamma) (a + b * t * I) * (b * I) * (b * I) *
    cexp (-(2 * π * x * t) * I) with hI₂
  set g₁ := deriv digamma (a + b * T * I) * (b * I) with hg₁
  set g₂ := deriv digamma (a + b * (-T) * I) * (b * I) with hg₂
  have key : (∫ t in -T..T, digamma (a + b * t * I) * cexp (-(2 * π * x * t) * I)) -
      (-(digamma (a + b * T * I) * cexp (-(2 * π * x * T) * I)) / ω +
        digamma (a + b * (-T) * I) * cexp (-(2 * π * x * (-T)) * I) / ω +
        digammaFourierKernel a b (-x) / ω ^ 2) =
      (1 / ω ^ 2) * (-(g₁ * cexp (-(2 * π * x * T) * I)) +
        g₂ * cexp (-(2 * π * x * (-T)) * I)) +
      (1 / ω ^ 2) * (I₂ - digammaFourierKernel a b (-x)) := by
    linear_combination ibp1 + (1 / ω) * ibp2
  rw [key]
  have hg₁b : ‖g₁‖ ≤ K₁ / T := by
    have := norm_deriv_digamma_line_le ha hb T
    rw [abs_of_pos hT0] at this
    rw [le_div_iff₀ hT0]; exact this
  have hg₂b : ‖g₂‖ ≤ K₁ / T := by
    have := norm_deriv_digamma_line_le ha hb (-T)
    rw [abs_neg, abs_of_pos hT0] at this
    push_cast at this
    rw [le_div_iff₀ hT0]
    exact this
  have hEmT : ‖cexp (-(2 * (π : ℂ) * x * -(T : ℂ)) * I)‖ = 1 := by
    have := norm_cexp_neg_mul_I x (-T)
    push_cast at this
    exact this
  have hω2 : ‖1 / ω ^ 2‖ = 1 / (4 * π ^ 2 * x ^ 2) := by
    rw [norm_div, norm_one, norm_pow, hnω, mul_pow, sq_abs]
    ring
  calc ‖(1 / ω ^ 2) * (-(g₁ * cexp (-(2 * π * x * T) * I)) + g₂ * cexp (-(2 * π * x * (-T)) * I)) +
        (1 / ω ^ 2) * (I₂ - digammaFourierKernel a b (-x))‖
      ≤ ‖1 / ω ^ 2‖ * (‖g₁‖ + ‖g₂‖) + ‖1 / ω ^ 2‖ * ‖I₂ - digammaFourierKernel a b (-x)‖ := by
        refine (norm_add_le _ _).trans (add_le_add ?_ (norm_mul_le _ _))
        refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_neg, norm_mul, norm_cexp_neg_mul_I, mul_one]
        · rw [norm_mul, hEmT, mul_one]
    _ ≤ 1 / (4 * π ^ 2 * x ^ 2) * (K₁ / T + K₁ / T) + 1 / (4 * π ^ 2 * x ^ 2) * (2 * C₂ / T) := by
        rw [hω2]
        gcongr
    _ = (2 * K₁ + 2 * C₂) / (4 * π ^ 2) / (x ^ 2 * T) := by
        field_simp
        ring

/-- **Montgomery–Vaughan, Theorem C.5.** Let `a, b > 0`. There is a constant `C` such that for
`x ≠ 0` and `T ≥ 1`,
`∫_{-T}^{T} ψ(a + ibt) e(-xt) dt = -ψ(a + ibT) e(-xT)/(2πix) + ψ(a - ibT) e(xT)/(2πix)
  - [x < 0] (2π/b) e^{2πax/b} / (1 - e^{2πx/b}) + E`, with `|E| ≤ C / (x² T)`. -/
theorem norm_integral_digamma_line_mul_cexp_sub_le (ha : 0 < a) (hb : 0 < b) :
    ∃ C, ∀ x : ℝ, x ≠ 0 → ∀ T : ℝ, 1 ≤ T →
      ‖(∫ t in -T..T, digamma (a + b * t * I) * cexp (-(2 * π * x * t) * I)) -
        (-(digamma (a + b * T * I) * cexp (-(2 * π * x * T) * I)) / (2 * π * x * I) +
          digamma (a - b * T * I) * cexp ((2 * π * x * T) * I) / (2 * π * x * I) -
          if x < 0 then (((2 * π / b) * (Real.exp (2 * π * a * x / b) /
            (1 - Real.exp (2 * π * x / b))) : ℝ) : ℂ) else 0)‖ ≤ C / (x ^ 2 * T) := by
  obtain ⟨C, hC⟩ := norm_integral_digamma_line_mul_cexp_sub_le' ha hb
  refine ⟨C, fun x hx T hT ↦ ?_⟩
  have h := hC x hx T hT
  rw [digammaFourierKernel_neg_div_sq hb hx] at h
  have e1 : digamma (a + b * (-T) * I) = digamma (a - b * T * I) := by
    congr 1; ring
  have e2 : cexp (-(2 * π * x * (-T)) * I) = cexp ((2 * π * x * T) * I) := by
    congr 1; ring
  rw [e1, e2] at h
  convert h using 3
  split_ifs <;> ring

end Complex
