/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Harald Helfgott
-/
module

public import Mathlib.Analysis.BoxIntegral.Stieltjes.DirichletJordan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-! # The Fourier integral theorem for integrable functions of bounded variation

The integral analogue of the Dirichlet–Jordan theorem (`DirichletJordan.lean`): if `g : ℝ → ℂ` is
integrable and of bounded variation on `ℝ`, then for every `x`,
`∫_{-T}^{T} ĝ(t) e(tx) dt → (g(x+) + g(x-))/2` as `T → ∞`, where `e(θ) = e^{2πiθ}` and
`ĝ = 𝓕 g`.

This is the Fourier integral theorem used in the proof of Theorem 12.13 of Montgomery–Vaughan,
*Multiplicative Number Theory I*. The proof follows the route of `DirichletJordan.lean`:

* the Fejér kernel `K_T(y) = T sinc(πTy)²` on `ℝ` is the Fourier transform of the triangle
  function `(1 - |t|/T)₊`, is nonnegative and even, has integral `1`, and
  `K_T(y) ≤ 1/(π²Ty²)`;
* Fejér's theorem for Fourier integrals: if `g ∈ L¹` has one-sided limits `ℓ₊`, `ℓ₋` at `x`,
  then `∫_{-T}^{T} (1 - |t|/T) ĝ(t) e(tx) dt = ∫ K_T(y) g(x - y) dy → (ℓ₊ + ℓ₋)/2`;
* Hardy's Tauberian theorem for integrals, reduced to the discrete theorem
  `tendsto_sum_range_of_tendsto_cesaroMean` of `SpecificLimits/Cesaro.lean`;
* `ĝ(t) = O(1/|t|)` for `g` of bounded variation (`FourierTransform.fourier_bounded_variation`).

The names and statements follow the draft `blueprint/drafts/FourierIntegral.lean` of the
blueprint for Theorem 12.13 (branch `weil-explicit-formula` of `Garald1/mathlib-at-ICERM26`).

## AI usage

This file was written by Claude (Anthropic) in November 2026. It compiles, but has not been
reviewed by a human.
-/

@[expose] public section

open Real Filter Topology MeasureTheory Set
open scoped FourierTransform

noncomputable section

namespace FourierIntegral

variable {g : ℝ → ℂ}

/-- The partial Fourier inversion integral `∫_{-T}^{T} ĝ(t) e(tx) dt`, `e(θ) = e^{2πiθ}`. -/
def partialInv (g : ℝ → ℂ) (T x : ℝ) : ℂ :=
  ∫ t in (-T)..T, 𝓕 g t * Complex.exp (2 * π * t * x * Complex.I)

/-- The Fejér (Cesàro) mean of `partialInv`: `∫_{-T}^{T} (1 - |t|/T) ĝ(t) e(tx) dt`. -/
def fejerInv (g : ℝ → ℂ) (T x : ℝ) : ℂ :=
  ∫ t in (-T)..T, ((1 - |t| / T : ℝ) : ℂ) * 𝓕 g t * Complex.exp (2 * π * t * x * Complex.I)

/-- The Fejér kernel on `ℝ`, `K_T(y) = T sinc(πTy)²`. -/
def fejerKernel (T y : ℝ) : ℝ := T * sinc (π * T * y) ^ 2

/-! ### A2: the Fejér kernel -/

theorem fejerKernel_nonneg {T : ℝ} (hT : 0 ≤ T) (y : ℝ) : 0 ≤ fejerKernel T y :=
  mul_nonneg hT (sq_nonneg _)

theorem fejerKernel_neg (T y : ℝ) : fejerKernel T (-y) = fejerKernel T y := by
  unfold fejerKernel
  rw [show π * T * -y = -(π * T * y) by ring, sinc_neg]

theorem continuous_fejerKernel (T : ℝ) : Continuous (fejerKernel T) :=
  continuous_const.mul ((continuous_sinc.comp (continuous_const.mul continuous_id)).pow 2)

theorem fejerKernel_le {T : ℝ} (hT : 0 ≤ T) (y : ℝ) : fejerKernel T y ≤ T := by
  unfold fejerKernel
  have h : sinc (π * T * y) ^ 2 ≤ 1 := by
    rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) (abs_sinc_le_one _)
  calc T * sinc (π * T * y) ^ 2 ≤ T * 1 := mul_le_mul_of_nonneg_left h hT
    _ = T := mul_one T

theorem fejerKernel_le_div_sq {T : ℝ} (hT : 0 < T) {y : ℝ} (hy : y ≠ 0) :
    fejerKernel T y ≤ 1 / (π ^ 2 * T * y ^ 2) := by
  unfold fejerKernel
  have hz : π * T * y ≠ 0 := mul_ne_zero (mul_ne_zero pi_ne_zero hT.ne') hy
  rw [sinc_of_ne_zero hz, div_pow,
    show T * (sin (π * T * y) ^ 2 / (π * T * y) ^ 2) = sin (π * T * y) ^ 2 / (π ^ 2 * T * y ^ 2)
      by field_simp]
  exact div_le_div_of_nonneg_right (sin_sq_le_one _) (by positivity)

/-- Away from `0`, `K_T(y) ≤ (1 + η⁻²)/(π²T) · (1 + y²)⁻¹`. -/
theorem fejerKernel_le_of_le_abs {T η : ℝ} (hT : 0 < T) (hη : 0 < η) {y : ℝ} (hy : η ≤ |y|) :
    fejerKernel T y ≤ (1 + (η ^ 2)⁻¹) / (π ^ 2 * T) * (1 + y ^ 2)⁻¹ := by
  have hy0 : y ≠ 0 := by rintro rfl; rw [abs_zero] at hy; linarith
  have hy2 : η ^ 2 ≤ y ^ 2 := by rw [← sq_abs y]; gcongr
  have hη2 : 0 < η ^ 2 := by positivity
  have hyy : 0 < y ^ 2 := by positivity
  have h1 : 1 ≤ y ^ 2 * (η ^ 2)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hη2, one_mul]; exact hy2
  have key : 1 / y ^ 2 ≤ (1 + (η ^ 2)⁻¹) * (1 + y ^ 2)⁻¹ := by
    have e : (1 + (η ^ 2)⁻¹) * (1 + y ^ 2)⁻¹ - 1 / y ^ 2 =
        (y ^ 2 * (η ^ 2)⁻¹ - 1) / ((1 + y ^ 2) * y ^ 2) := by
      field_simp
      ring
    have : 0 ≤ (y ^ 2 * (η ^ 2)⁻¹ - 1) / ((1 + y ^ 2) * y ^ 2) :=
      div_nonneg (sub_nonneg.2 h1) (by positivity)
    linarith
  refine (fejerKernel_le_div_sq hT hy0).trans ?_
  calc 1 / (π ^ 2 * T * y ^ 2) = 1 / (π ^ 2 * T) * (1 / y ^ 2) := by
        rw [one_div_mul_one_div]
    _ ≤ 1 / (π ^ 2 * T) * ((1 + (η ^ 2)⁻¹) * (1 + y ^ 2)⁻¹) := by gcongr
    _ = (1 + (η ^ 2)⁻¹) / (π ^ 2 * T) * (1 + y ^ 2)⁻¹ := by ring

theorem integrable_fejerKernel {T : ℝ} (hT : 0 < T) : Integrable (fejerKernel T) := by
  refine (integrable_inv_one_add_sq.const_mul (2 * T + 2 / (π ^ 2 * T))).mono'
    (continuous_fejerKernel T).aestronglyMeasurable (Eventually.of_forall fun y ↦ ?_)
  rw [Real.norm_of_nonneg (fejerKernel_nonneg hT.le y)]
  have h1 : 0 < (1 + y ^ 2)⁻¹ := by positivity
  rcases le_or_gt |y| 1 with hy | hy
  · have hy2 : y ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg y]
    have h2 : 1 ≤ 2 * (1 + y ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]; linarith
    calc fejerKernel T y ≤ T := fejerKernel_le hT.le y
      _ ≤ T * (2 * (1 + y ^ 2)⁻¹) := le_mul_of_one_le_right hT.le h2
      _ ≤ (2 * T + 2 / (π ^ 2 * T)) * (1 + y ^ 2)⁻¹ := by
          have : 0 ≤ 2 / (π ^ 2 * T) * (1 + y ^ 2)⁻¹ := by positivity
          nlinarith
  · have h := fejerKernel_le_of_le_abs hT one_pos hy.le
    rw [one_pow, inv_one, show (1 : ℝ) + 1 = 2 by norm_num] at h
    refine h.trans ?_
    have : 0 ≤ 2 * T * (1 + y ^ 2)⁻¹ := by positivity
    nlinarith

/-- `∫_{-T}^{T} f(t) dt = ∫_0^T (f(t) + f(-t)) dt` for continuous `f`. -/
theorem integral_symm {f : ℝ → ℂ} (hf : Continuous f) (T : ℝ) :
    ∫ t in (-T)..T, f t = ∫ t in (0 : ℝ)..T, (f t + f (-t)) := by
  have h := intervalIntegral.integral_comp_neg (a := 0) (b := T) (f := f)
  rw [neg_zero] at h
  calc ∫ t in (-T)..T, f t = (∫ t in (-T)..0, f t) + ∫ t in (0 : ℝ)..T, f t :=
        (intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable _ _)
          (hf.intervalIntegrable _ _)).symm
    _ = ∫ t in (0 : ℝ)..T, (f t + f (-t)) := by
        rw [intervalIntegral.integral_add (f := f) (g := fun t ↦ f (-t))
          (hf.intervalIntegrable _ _) ((hf.comp continuous_neg).intervalIntegrable _ _), h,
          add_comm]

/-- `∫_0^T 2 (1 - t/T) cos(2πyt) dt = T sinc(πTy)²`. -/
theorem integral_triangle_mul_cos {T : ℝ} (hT : 0 < T) (y : ℝ) :
    ∫ t in (0 : ℝ)..T, 2 * (1 - t / T) * Real.cos (2 * π * y * t) = T * sinc (π * T * y) ^ 2 := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp only [mul_zero, zero_mul, Real.cos_zero, mul_one, sinc_zero, one_pow]
    have hd : ∀ t ∈ uIcc (0 : ℝ) T,
        HasDerivAt (fun t ↦ 2 * (t - t ^ 2 / (2 * T))) (2 * (1 - t / T)) t := by
      intro t _
      have := ((hasDerivAt_id' t).sub ((hasDerivAt_pow 2 t).div_const (2 * T))).const_mul 2
      convert this using 1
      field_simp
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((by fun_prop : Continuous fun t : ℝ ↦ 2 * (1 - t / T)).intervalIntegrable _ _)]
    field_simp
    ring
  · set a := 2 * π * y with ha
    have ha0 : a ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero pi_ne_zero) hy
    have hd : ∀ t ∈ uIcc (0 : ℝ) T, HasDerivAt
        (fun t ↦ 2 * ((1 - t / T) * Real.sin (a * t) / a - Real.cos (a * t) / (a ^ 2 * T)))
        (2 * (1 - t / T) * Real.cos (a * t)) t := by
      intro t _
      have hs := ((hasDerivAt_id' t).const_mul a).sin
      have hc := ((hasDerivAt_id' t).const_mul a).cos
      have hl := ((hasDerivAt_id' t).div_const T).const_sub (1 : ℝ)
      have := (((hl.mul hs).div_const a).sub (hc.div_const (a ^ 2 * T))).const_mul 2
      convert this using 1
      field_simp
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((by fun_prop : Continuous fun t : ℝ ↦ 2 * (1 - t / T) * Real.cos (a * t)).intervalIntegrable
        _ _)]
    have hz : π * T * y ≠ 0 := mul_ne_zero (mul_ne_zero pi_ne_zero hT.ne') hy
    have hθ : a * T = 2 * (π * T * y) := by rw [ha]; ring
    rw [hθ, sinc_of_ne_zero hz, Real.cos_two_mul, Real.cos_sq']
    simp only [mul_zero, Real.sin_zero, Real.cos_zero, zero_div, sub_zero, div_self hT.ne',
      sub_self, zero_mul]
    rw [ha]
    field_simp
    ring

/-- **A2.** The Fourier transform of the triangle function `(1 - |t|/T)₊` is the Fejér kernel. -/
theorem integral_triangle_mul_exp {T : ℝ} (hT : 0 < T) (y : ℝ) :
    ∫ t in (-T)..T, ((1 - |t| / T : ℝ) : ℂ) * Complex.exp (2 * π * t * y * Complex.I) =
      (fejerKernel T y : ℂ) := by
  rw [integral_symm (by fun_prop) T]
  have h : ∀ t ∈ uIcc (0 : ℝ) T, ((1 - |t| / T : ℝ) : ℂ) * Complex.exp (2 * π * t * y * Complex.I) +
      ((1 - |-t| / T : ℝ) : ℂ) * Complex.exp (2 * π * ↑(-t) * y * Complex.I) =
      ((2 * (1 - t / T) * Real.cos (2 * π * y * t) : ℝ) : ℂ) := by
    intro t ht
    rw [uIcc_of_le hT.le] at ht
    rw [abs_neg, abs_of_nonneg ht.1]
    push_cast
    rw [show (2 : ℂ) * (1 - t / T) * Complex.cos (2 * π * y * t) =
      (1 - t / T) * (2 * Complex.cos (2 * π * y * t)) by ring, Complex.two_cos]
    ring_nf
  rw [intervalIntegral.integral_congr h, intervalIntegral.integral_ofReal,
    integral_triangle_mul_cos hT y, fejerKernel]

/-- The triangle function `t ↦ (1 - |t|/T)₊`. -/
def triangle (T t : ℝ) : ℝ := max 0 (1 - |t| / T)

theorem continuous_triangle (T : ℝ) : Continuous (triangle T) := by
  unfold triangle; fun_prop

theorem triangle_eq_zero {T t : ℝ} (hT : 0 < T) (ht : T ≤ |t|) : triangle T t = 0 := by
  unfold triangle
  apply max_eq_left
  rw [sub_nonpos, le_div_iff₀ hT, one_mul]
  exact ht

theorem triangle_eq {T t : ℝ} (hT : 0 < T) (ht : |t| ≤ T) : triangle T t = 1 - |t| / T := by
  unfold triangle
  apply max_eq_right
  rw [sub_nonneg, div_le_one hT]
  exact ht

theorem integrable_triangle {T : ℝ} (hT : 0 < T) : Integrable fun t ↦ (triangle T t : ℂ) := by
  refine (Complex.continuous_ofReal.comp
    (continuous_triangle T)).integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (isCompact_Icc (a := -T) (b := T)) fun t ht ↦ ?_
  have h : T ≤ |t| := by
    by_contra h
    exact ht (abs_le.1 (not_le.1 h).le)
  simp [triangle_eq_zero hT h]

theorem fourier_triangle {T : ℝ} (hT : 0 < T) (y : ℝ) :
    𝓕 (fun t ↦ (triangle T t : ℂ)) y = (fejerKernel T y : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioc (-T) T) (fun t ht ↦ ?_),
    ← intervalIntegral.integral_of_le (by linarith), ← fejerKernel_neg,
    ← integral_triangle_mul_exp hT (-y)]
  · refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [uIcc_of_le (by linarith)] at ht
    simp only [smul_eq_mul, triangle_eq hT (abs_le.2 ht)]
    push_cast
    ring_nf
  · have h : T ≤ |t| := by
      rw [mem_Ioc, not_and_or, not_lt, not_le] at ht
      rcases ht with h | h
      · rw [le_abs]; right; linarith
      · rw [le_abs]; left; linarith
    simp [triangle_eq_zero hT h]

/-- `∫ K_T = 1`, by Fourier inversion for the triangle function. -/
theorem integral_fejerKernel {T : ℝ} (hT : 0 < T) : ∫ y, fejerKernel T y = 1 := by
  have hΛc : Continuous fun t ↦ (triangle T t : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_triangle T)
  have hFΛ : 𝓕 (fun t ↦ (triangle T t : ℂ)) = fun y ↦ (fejerKernel T y : ℂ) :=
    funext (fourier_triangle hT)
  have hFi : Integrable (𝓕 (fun t ↦ (triangle T t : ℂ))) := by
    rw [hFΛ]; exact (integrable_fejerKernel hT).ofReal
  have h := (integrable_triangle hT).fourierInv_fourier_eq hFi (hΛc.continuousAt (x := 0))
  rw [hFΛ, Real.fourierInv_eq'] at h
  simp only [inner_zero_right, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
    one_smul, integral_complex_ofReal] at h
  have h0 : triangle T 0 = 1 := by simp [triangle]
  rw [h0, Complex.ofReal_one] at h
  exact_mod_cast h

theorem integral_Ioi_fejerKernel {T : ℝ} (hT : 0 < T) : ∫ y in Ioi 0, fejerKernel T y = 1 / 2 := by
  have hi := integrable_fejerKernel hT
  have h1 : ∫ y in Iio 0, fejerKernel T y = ∫ y in Ioi 0, fejerKernel T y := by
    rw [← integral_Iic_eq_integral_Iio, ← neg_zero, ← integral_comp_neg_Ioi]
    simp only [fejerKernel_neg, neg_zero]
  have h2 := integral_add_compl (measurableSet_Iio : MeasurableSet (Iio (0 : ℝ))) hi
  rw [compl_Iio, integral_Ici_eq_integral_Ioi, h1, integral_fejerKernel hT] at h2
  linarith

theorem integral_Iio_fejerKernel {T : ℝ} (hT : 0 < T) : ∫ y in Iio 0, fejerKernel T y = 1 / 2 := by
  rw [← integral_Iic_eq_integral_Iio, ← neg_zero, ← integral_comp_neg_Ioi]
  simp only [fejerKernel_neg]
  exact integral_Ioi_fejerKernel hT

/-! ### A3: Fejér's theorem for Fourier integrals -/

theorem norm_exp_two_pi_mul_I (r : ℝ) : ‖Complex.exp (2 * π * r * Complex.I)‖ = 1 := by
  rw [show (2 : ℂ) * π * r * Complex.I = ((2 * π * r : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- **A3.** `∫_{-T}^{T} (1 - |t|/T) ĝ(t) e(tx) dt = ∫ K_T(y) g(x - y) dy`. -/
theorem fejerInv_eq_integral (hg : Integrable g) {T : ℝ} (hT : 0 < T) (x : ℝ) :
    fejerInv g T x = ∫ y, (fejerKernel T y : ℂ) * g (x - y) := by
  have hΛc : Continuous fun t : ℝ ↦ ((1 - |t| / T : ℝ) : ℂ) := by fun_prop
  unfold fejerInv
  rw [intervalIntegral.integral_of_le (by linarith)]
  have hF : ∀ t : ℝ, ((1 - |t| / T : ℝ) : ℂ) * 𝓕 g t * Complex.exp (2 * π * t * x * Complex.I) =
      ∫ u : ℝ, ((1 - |t| / T : ℝ) : ℂ) * Complex.exp (2 * π * t * (x - u) * Complex.I) * g u := by
    intro t
    rw [Real.fourier_real_eq_integral_exp_smul, ← integral_const_mul, ← integral_mul_const]
    congr 1
    ext u
    rw [smul_eq_mul, show Complex.exp (2 * π * t * (x - u) * Complex.I) =
      Complex.exp (↑(-2 * π * u * t) * Complex.I) * Complex.exp (2 * π * t * x * Complex.I) by
        rw [← Complex.exp_add]; congr 1; push_cast; ring]
    ring
  simp_rw [hF]
  rw [integral_integral_swap]
  · have hK : ∀ u : ℝ, ∫ t in Ioc (-T) T,
        ((1 - |t| / T : ℝ) : ℂ) * Complex.exp (2 * π * t * (x - u) * Complex.I) * g u =
        (fejerKernel T (x - u) : ℂ) * g u := by
      intro u
      rw [integral_mul_const, ← intervalIntegral.integral_of_le (by linarith)]
      have h := integral_triangle_mul_exp hT (x - u)
      push_cast at h ⊢
      rw [h]
    simp_rw [hK]
    have h := integral_sub_left_eq_self (fun y ↦ (fejerKernel T y : ℂ) * g (x - y)) volume x
    simp only [sub_sub_cancel] at h
    exact h
  · refine Integrable.mono' (Integrable.mul_prod
      (hΛc.norm.integrableOn_Icc.mono_set Ioc_subset_Icc_self) hg.norm) ?_
      (Eventually.of_forall fun z ↦ ?_)
    · exact ((hΛc.comp continuous_fst).mul (by fun_prop)).aestronglyMeasurable.mul
        hg.aestronglyMeasurable.comp_snd
    · obtain ⟨t, u⟩ := z
      simp only [Function.uncurry_apply_pair, norm_mul]
      rw [show (2 : ℂ) * π * t * (x - u) * Complex.I = 2 * π * ((t * (x - u) : ℝ) : ℂ) * Complex.I
        by push_cast; ring, norm_exp_two_pi_mul_I, mul_one]

/-- **A3. Fejér's theorem for Fourier integrals**: at a point where `g` has one-sided limits,
the Fejér means of the Fourier inversion integral converge to the average of the two limits. -/
theorem tendsto_fejerInv_of_tendsto (hg : Integrable g) {x : ℝ} {l₁ l₂ : ℂ}
    (h₁ : Tendsto g (𝓝[>] x) (𝓝 l₁)) (h₂ : Tendsto g (𝓝[<] x) (𝓝 l₂)) :
    Tendsto (fun T ↦ fejerInv g T x) atTop (𝓝 ((l₁ + l₂) / 2)) := by
  set L : ℝ → ℂ := fun y ↦ if y < 0 then l₁ else if 0 < y then l₂ else g x with hLdef
  set M : ℝ := ‖l₁‖ + ‖l₂‖ + ‖g x‖ with hMdef
  have hM0 : 0 ≤ M := by positivity
  have hLb : ∀ y, ‖L y‖ ≤ M := fun y ↦ by
    have := norm_nonneg l₁; have := norm_nonneg l₂; have := norm_nonneg (g x)
    simp only [hLdef, hMdef]
    split_ifs <;> linarith
  have hLm : Measurable L :=
    Measurable.ite measurableSet_Iio measurable_const
      (Measurable.ite measurableSet_Ioi measurable_const measurable_const)
  set N := ∫ y, ‖g y‖ with hNdef
  have hN0 : 0 ≤ N := integral_nonneg fun _ ↦ norm_nonneg _
  have hgx : Integrable fun y ↦ g (x - y) := hg.comp_sub_left x
  have hKc : ∀ T, Continuous fun y ↦ (fejerKernel T y : ℂ) := fun T ↦
    Complex.continuous_ofReal.comp (continuous_fejerKernel T)
  have hKg : ∀ T, 0 < T → Integrable fun y ↦ (fejerKernel T y : ℂ) * g (x - y) := fun T hT ↦
    (hgx.norm.const_mul T).mono' ((hKc T).aestronglyMeasurable.mul hgx.1)
      (Eventually.of_forall fun y ↦ by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (fejerKernel_nonneg hT.le y)]
        exact mul_le_mul_of_nonneg_right (fejerKernel_le hT.le y) (norm_nonneg _))
  have hKL : ∀ T, 0 < T → Integrable fun y ↦ (fejerKernel T y : ℂ) * L y := fun T hT ↦
    ((integrable_fejerKernel hT).mul_const M).mono'
      ((hKc T).aestronglyMeasurable.mul hLm.aestronglyMeasurable)
      (Eventually.of_forall fun y ↦ by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (fejerKernel_nonneg hT.le y)]
        exact mul_le_mul_of_nonneg_left (hLb y) (fejerKernel_nonneg hT.le y))
  have hKLint : ∀ T, 0 < T → ∫ y, (fejerKernel T y : ℂ) * L y = (l₁ + l₂) / 2 := by
    intro T hT
    rw [← integral_add_compl measurableSet_Iio (hKL T hT), compl_Iio,
      integral_Ici_eq_integral_Ioi,
      setIntegral_congr_fun measurableSet_Iio (g := fun y ↦ (fejerKernel T y : ℂ) * l₁)
        (fun y hy ↦ by simp only [hLdef, if_pos (show y < 0 from hy)]),
      setIntegral_congr_fun measurableSet_Ioi (g := fun y ↦ (fejerKernel T y : ℂ) * l₂)
        (fun y hy ↦ by
          simp only [hLdef, if_neg (not_lt.2 (le_of_lt (show 0 < y from hy))),
            if_pos (show 0 < y from hy)]),
      integral_mul_const, integral_mul_const, integral_complex_ofReal, integral_complex_ofReal,
      integral_Iio_fejerKernel hT, integral_Ioi_fejerKernel hT]
    push_cast
    ring
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨η₁, hη₁, hη₁'⟩ := Metric.tendsto_nhdsWithin_nhds.1 h₁ (ε / 4) (by positivity)
  obtain ⟨η₂, hη₂, hη₂'⟩ := Metric.tendsto_nhdsWithin_nhds.1 h₂ (ε / 4) (by positivity)
  set η := min η₁ η₂ with hηdef
  have hη : 0 < η := lt_min hη₁ hη₂
  set B := N / (π ^ 2 * η ^ 2) + M * (1 + (η ^ 2)⁻¹) / π with hBdef
  have hB : 0 ≤ B := by positivity
  have hbound : ∀ T, 0 < T → ‖fejerInv g T x - (l₁ + l₂) / 2‖ ≤ ε / 4 + B / T := by
    intro T hT
    rw [fejerInv_eq_integral hg hT, ← hKLint T hT, ← integral_sub (hKg T hT) (hKL T hT)]
    set D : ℝ → ℝ := fun y ↦ ε / 4 * fejerKernel T y + 1 / (π ^ 2 * T * η ^ 2) * ‖g (x - y)‖ +
      M * (1 + (η ^ 2)⁻¹) / (π ^ 2 * T) * (1 + y ^ 2)⁻¹ with hDdef
    have hD1 : Integrable fun y ↦ ε / 4 * fejerKernel T y :=
      (integrable_fejerKernel hT).const_mul _
    have hD2 : Integrable fun y ↦ 1 / (π ^ 2 * T * η ^ 2) * ‖g (x - y)‖ := hgx.norm.const_mul _
    have hD3 : Integrable fun y : ℝ ↦ M * (1 + (η ^ 2)⁻¹) / (π ^ 2 * T) * (1 + y ^ 2)⁻¹ :=
      integrable_inv_one_add_sq.const_mul _
    have hD12 : Integrable fun y ↦ ε / 4 * fejerKernel T y +
        1 / (π ^ 2 * T * η ^ 2) * ‖g (x - y)‖ := hD1.add hD2
    have hDi : Integrable D := hD12.add hD3
    have hpt : ∀ y, ‖(fejerKernel T y : ℂ) * g (x - y) - (fejerKernel T y : ℂ) * L y‖ ≤ D y := by
      intro y
      have hK0 := fejerKernel_nonneg hT.le y
      rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg hK0]
      have hE1 : 0 ≤ ε / 4 * fejerKernel T y := by positivity
      have hE2 : 0 ≤ 1 / (π ^ 2 * T * η ^ 2) * ‖g (x - y)‖ := by positivity
      have hE3 : 0 ≤ M * (1 + (η ^ 2)⁻¹) / (π ^ 2 * T) * (1 + y ^ 2)⁻¹ := by positivity
      rcases lt_or_ge |y| η with hy | hy
      · have hclose : ‖g (x - y) - L y‖ ≤ ε / 4 := by
          rcases lt_trichotomy y 0 with hy0 | rfl | hy0
          · have hmem : x - y ∈ Ioi x := by rw [mem_Ioi]; linarith
            have hdist : dist (x - y) x < η₁ := by
              rw [Real.dist_eq, show x - y - x = -y by ring, abs_neg]
              exact hy.trans_le (min_le_left _ _)
            have := hη₁' hmem hdist
            simp only [hLdef, if_pos hy0]
            rw [← dist_eq_norm]
            exact this.le
          · simp only [hLdef, lt_irrefl, if_false, sub_zero, sub_self, norm_zero]
            positivity
          · have hmem : x - y ∈ Iio x := by rw [mem_Iio]; linarith
            have hdist : dist (x - y) x < η₂ := by
              rw [Real.dist_eq, show x - y - x = -y by ring, abs_neg]
              exact hy.trans_le (min_le_right _ _)
            have := hη₂' hmem hdist
            simp only [hLdef, if_neg (not_lt.2 hy0.le), if_pos hy0]
            rw [← dist_eq_norm]
            exact this.le
        calc fejerKernel T y * ‖g (x - y) - L y‖ ≤ fejerKernel T y * (ε / 4) :=
              mul_le_mul_of_nonneg_left hclose hK0
          _ = ε / 4 * fejerKernel T y := by ring
          _ ≤ D y := by simp only [hDdef]; linarith
      · have hy0 : y ≠ 0 := by rintro rfl; rw [abs_zero] at hy; linarith
        have hK1 : fejerKernel T y ≤ 1 / (π ^ 2 * T * η ^ 2) := by
          refine (fejerKernel_le_div_sq hT hy0).trans ?_
          have hy2 : η ^ 2 ≤ y ^ 2 := by rw [← sq_abs y]; gcongr
          gcongr
        have hK2 := fejerKernel_le_of_le_abs hT hη hy
        calc fejerKernel T y * ‖g (x - y) - L y‖
            ≤ fejerKernel T y * (‖g (x - y)‖ + M) :=
              mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (by linarith [hLb y])) hK0
          _ = fejerKernel T y * ‖g (x - y)‖ + fejerKernel T y * M := by ring
          _ ≤ 1 / (π ^ 2 * T * η ^ 2) * ‖g (x - y)‖ +
                (1 + (η ^ 2)⁻¹) / (π ^ 2 * T) * (1 + y ^ 2)⁻¹ * M :=
              add_le_add (mul_le_mul_of_nonneg_right hK1 (norm_nonneg _))
                (mul_le_mul_of_nonneg_right hK2 hM0)
          _ = 1 / (π ^ 2 * T * η ^ 2) * ‖g (x - y)‖ +
                M * (1 + (η ^ 2)⁻¹) / (π ^ 2 * T) * (1 + y ^ 2)⁻¹ := by ring
          _ ≤ D y := by simp only [hDdef]; linarith
    have hintD : ∫ y, D y = ε / 4 + B / T := by
      simp only [hDdef]
      rw [integral_add hD12 hD3, integral_add hD1 hD2, integral_const_mul,
        integral_const_mul, integral_const_mul, integral_fejerKernel hT,
        integral_univ_inv_one_add_sq,
        show ∫ y, ‖g (x - y)‖ = N from integral_sub_left_eq_self (fun y ↦ ‖g y‖) volume x]
      simp only [hBdef]
      field_simp
      ring
    calc ‖∫ y, ((fejerKernel T y : ℂ) * g (x - y) - (fejerKernel T y : ℂ) * L y)‖
        ≤ ∫ y, D y := norm_integral_le_of_norm_le hDi (Eventually.of_forall hpt)
      _ = ε / 4 + B / T := hintD
  set T₀ := 4 * (B + 1) / ε with hT₀def
  have hT₀ : 0 < T₀ := by positivity
  refine ⟨T₀, fun T hT ↦ ?_⟩
  have hTpos : 0 < T := hT₀.trans_le hT
  rw [dist_eq_norm]
  refine (hbound T hTpos).trans_lt ?_
  have h1 : B / T ≤ B / T₀ := div_le_div_of_nonneg_left hB hT₀ hT
  have h2 : B / T₀ < ε / 4 := by
    rw [hT₀def, div_div_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

/-! ### A4: Hardy's Tauberian theorem for integrals -/

/-- `‖∫_a^b u‖ ≤ A/c` when `‖u(t)‖ ≤ A/t` for `t ≥ 1`, `1 ≤ c ≤ a ≤ b ≤ c + 1`. -/
theorem norm_integral_le_of_le_div {u : ℝ → ℂ} {A : ℝ} (hA : ∀ t, 1 ≤ t → ‖u t‖ ≤ A / t)
    {a b c : ℝ} (hc : 1 ≤ c) (hca : c ≤ a) (hab : a ≤ b) (hbc : b ≤ c + 1) :
    ‖∫ t in a..b, u t‖ ≤ A / c := by
  have hA0 : 0 ≤ A := by
    have := (norm_nonneg _).trans (hA 1 le_rfl); simpa using this
  calc ‖∫ t in a..b, u t‖ ≤ A / c * |b - a| :=
        intervalIntegral.norm_integral_le_of_norm_le_const fun t ht ↦ by
          rw [uIoc_of_le hab] at ht
          refine (hA t (by linarith [ht.1])).trans ?_
          exact div_le_div_of_nonneg_left hA0 (by linarith) (by linarith [ht.1])
    _ ≤ A / c * 1 := by
        gcongr
        rw [abs_of_nonneg (by linarith)]; linarith
    _ = A / c := mul_one _

/-- **A4. Hardy's Tauberian theorem for integrals**: if `u(t) = O(1/t)` and the Cesàro means of
`∫_0^T u` converge to `s`, then `∫_0^T u → s`. (By reduction to
`tendsto_sum_range_of_tendsto_cesaroMean`, with `u_k = ∫_k^{k+1} u`.) -/
theorem tendsto_integral_of_tendsto_cesaro {u : ℝ → ℂ} {A : ℝ} {s : ℂ}
    (hu : ∀ T, IntervalIntegrable u volume 0 T) (hA : ∀ t, 1 ≤ t → ‖u t‖ ≤ A / t)
    (hσ : Tendsto (fun T : ℝ ↦ (T : ℂ)⁻¹ * ∫ v in (0 : ℝ)..T, ∫ t in (0 : ℝ)..v, u t) atTop
      (𝓝 s)) :
    Tendsto (fun T ↦ ∫ t in (0 : ℝ)..T, u t) atTop (𝓝 s) := by
  have hab : ∀ a b, IntervalIntegrable u volume a b := fun a b ↦ (hu a).symm.trans (hu b)
  set U : ℝ → ℂ := fun v ↦ ∫ t in (0 : ℝ)..v, u t with hUdef
  have hUc : Continuous U := intervalIntegral.continuous_primitive hab 0
  have hUsub : ∀ a b, U b - U a = ∫ t in a..b, u t := fun a b ↦
    intervalIntegral.integral_interval_sub_left (hab 0 b) (hab 0 a)
  -- the discrete series `w k = ∫_k^{k+1} u`
  set w : ℕ → ℂ := fun k ↦ ∫ t in (k : ℝ)..(k + 1), u t with hwdef
  have hsum : ∀ n : ℕ, ∑ k ∈ Finset.range (n + 1), w k = U (n + 1) := by
    intro n
    have h := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := u)
      (a := fun k : ℕ ↦ (k : ℝ)) (n := n + 1) (fun k _ ↦ hab _ _)
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] at h
    exact h
  have hw : ∀ k : ℕ, 1 ≤ k → ‖w k‖ ≤ A / k := fun k hk ↦
    norm_integral_le_of_le_div hA (by exact_mod_cast hk) le_rfl (by linarith) le_rfl
  -- the error terms `e_n = U(n+1) - ∫_n^{n+1} U`
  set e : ℕ → ℂ := fun n ↦ U (n + 1) - ∫ v in (n : ℝ)..(n + 1), U v with hedef
  have he : ∀ n : ℕ, 1 ≤ n → ‖e n‖ ≤ A / n := by
    intro n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have h1 : e n = ∫ v in (n : ℝ)..(n + 1), (U (n + 1) - U v) := by
      simp only [hedef]
      rw [intervalIntegral.integral_sub intervalIntegrable_const (hUc.intervalIntegrable _ _),
        intervalIntegral.integral_const]
      simp
    rw [h1]
    calc ‖∫ v in (n : ℝ)..(n + 1), (U (n + 1) - U v)‖ ≤ A / n * |((n : ℝ) + 1) - n| :=
          intervalIntegral.norm_integral_le_of_norm_le_const fun v hv ↦ by
            rw [uIoc_of_le (by linarith)] at hv
            rw [hUsub]
            exact norm_integral_le_of_le_div hA hn' hv.1.le hv.2 le_rfl
      _ = A / n := by rw [add_sub_cancel_left, abs_one, mul_one]
  have he0 : Tendsto e atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_const_div_atTop_nhds_zero_nat A)
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact he n hn
  -- the Cesàro means of `w`
  have hm : Tendsto (fun m : ℕ ↦ ((m : ℝ) + 1)) atTop atTop := by
    have := (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using this
  have hσ' := hσ.comp hm
  have hd := (he0.cesaro_smul).comp (tendsto_add_atTop_nat 1)
  have hcesaro : Tendsto (cesaroMean w) atTop (𝓝 s) := by
    have := hσ'.add hd
    rw [add_zero] at this
    refine this.congr fun m ↦ ?_
    simp only [Function.comp_apply, cesaroMean, hsum]
    have h := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := U)
      (a := fun k : ℕ ↦ (k : ℝ)) (n := m + 1) (fun k _ ↦ hUc.intervalIntegrable _ _)
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] at h
    rw [← h, hedef]
    simp only [Finset.sum_sub_distrib, Complex.real_smul, Nat.cast_add, Nat.cast_one]
    push_cast
    ring
  have hS := tendsto_sum_range_of_tendsto_cesaroMean hw hcesaro
  simp only [hsum] at hS
  have hUn : Tendsto (fun n : ℕ ↦ U n) atTop (𝓝 s) := by
    rw [← tendsto_add_atTop_iff_nat 1]
    simpa only [Nat.cast_add, Nat.cast_one] using hS
  -- from integers to real `T`
  have hfl := hUn.comp (tendsto_nat_floor_atTop (α := ℝ))
  have hdiff : Tendsto (fun T : ℝ ↦ U T - U ⌊T⌋₊) atTop (𝓝 0) := by
    have hlim : Tendsto (fun T : ℝ ↦ A / (⌊T⌋₊ : ℝ)) atTop (𝓝 0) :=
      (tendsto_const_div_atTop_nhds_zero_nat A).comp (tendsto_nat_floor_atTop (α := ℝ))
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop 1] with T hT
    have hf1 : (1 : ℝ) ≤ ⌊T⌋₊ := by exact_mod_cast (Nat.one_le_floor_iff T).2 hT
    rw [hUsub]
    exact norm_integral_le_of_le_div hA hf1 le_rfl (Nat.floor_le (by linarith))
      (Nat.lt_floor_add_one T).le
  have := hfl.add hdiff
  rw [add_zero] at this
  refine this.congr fun T ↦ ?_
  simp only [Function.comp_apply, hUdef]
  ring

/-! ### A5: the Fourier integral theorem -/

theorem continuous_fourier_of_integrable (hg : Integrable g) : Continuous (𝓕 g) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hg

theorem norm_exp_two_pi_mul_mul_I (t x : ℝ) :
    ‖Complex.exp (2 * π * t * x * Complex.I)‖ = 1 := by
  rw [show (2 : ℂ) * π * t * x * Complex.I = 2 * π * ((t * x : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact norm_exp_two_pi_mul_I _

/-- The integrand `u(t) = ĝ(t) e(tx) + ĝ(-t) e(-tx)`, so that `partialInv g T x = ∫_0^T u`. -/
def symmInv (g : ℝ → ℂ) (x t : ℝ) : ℂ :=
  𝓕 g t * Complex.exp (2 * π * t * x * Complex.I) +
    𝓕 g (-t) * Complex.exp (2 * π * ((-t : ℝ) : ℂ) * x * Complex.I)

theorem continuous_symmInv (hg : Integrable g) (x : ℝ) : Continuous (symmInv g x) := by
  have hc := continuous_fourier_of_integrable hg
  unfold symmInv
  exact (hc.mul (by fun_prop)).add ((hc.comp continuous_neg).mul (by fun_prop))

theorem partialInv_eq (hg : Integrable g) (T x : ℝ) :
    partialInv g T x = ∫ t in (0 : ℝ)..T, symmInv g x t := by
  unfold partialInv symmInv
  exact integral_symm ((continuous_fourier_of_integrable hg).mul (by fun_prop)) T

theorem fejerInv_eq (hg : Integrable g) {T : ℝ} (hT : 0 ≤ T) (x : ℝ) :
    fejerInv g T x = ∫ t in (0 : ℝ)..T, ((1 - t / T : ℝ) : ℂ) * symmInv g x t := by
  unfold fejerInv
  rw [integral_symm (f := fun t ↦ ((1 - |t| / T : ℝ) : ℂ) * 𝓕 g t *
    Complex.exp (2 * π * t * x * Complex.I))
    (((by fun_prop : Continuous fun t : ℝ ↦ ((1 - |t| / T : ℝ) : ℂ)).mul
    (continuous_fourier_of_integrable hg)).mul (by fun_prop)) T]
  refine intervalIntegral.integral_congr fun t ht ↦ ?_
  rw [uIcc_of_le hT] at ht
  simp only [symmInv, abs_neg, abs_of_nonneg ht.1]
  ring

/-- The Cesàro mean of `∫_0^T u` is the Fejér mean `fejerInv g T x`. -/
theorem cesaro_symmInv (hg : Integrable g) {T : ℝ} (hT : 0 < T) (x : ℝ) :
    (T : ℂ)⁻¹ * ∫ v in (0 : ℝ)..T, ∫ t in (0 : ℝ)..v, symmInv g x t = fejerInv g T x := by
  have hc := continuous_symmInv hg x
  rw [fejerInv_eq hg hT.le]
  have hU : ∀ v ∈ uIcc (0 : ℝ) T,
      HasDerivAt (fun v ↦ ∫ t in (0 : ℝ)..v, symmInv g x t) (symmInv g x v) v :=
    fun v _ ↦ (hc.integral_hasStrictDerivAt 0 v).hasDerivAt
  have hφ : ∀ v ∈ uIcc (0 : ℝ) T, HasDerivAt (fun v : ℝ ↦ ((v - T : ℝ) : ℂ)) 1 v := fun v _ ↦ by
    simpa using ((hasDerivAt_id' v).sub_const T).ofReal_comp
  have ibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hU hφ (hc.intervalIntegrable _ _)
    intervalIntegrable_const
  simp only [mul_one, sub_self, Complex.ofReal_zero, mul_zero, intervalIntegral.integral_same,
    zero_mul, zero_sub] at ibp
  rw [ibp, ← intervalIntegral.integral_neg, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  have hT' : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hT.ne'
  push_cast
  field_simp
  ring

/-- `|u(t)| ≤ V(g)/(π t)` for `t > 0`, by `FourierTransform.fourier_bounded_variation`. -/
theorem norm_symmInv_le (hg1 : Integrable g) (hg2 : BoundedVariationOn g univ) (x : ℝ) {t : ℝ}
    (ht : 0 < t) : ‖symmInv g x t‖ ≤ (eVariationOn g univ).toReal / π / t := by
  have h1 := FourierTransform.fourier_bounded_variation hg1 hg2 ht.ne'
  have h2 := FourierTransform.fourier_bounded_variation hg1 hg2 (neg_ne_zero.2 ht.ne')
  rw [abs_of_pos ht] at h1
  rw [abs_neg, abs_of_pos ht] at h2
  unfold symmInv
  calc ‖𝓕 g t * Complex.exp (2 * π * t * x * Complex.I) +
        𝓕 g (-t) * Complex.exp (2 * π * ((-t : ℝ) : ℂ) * x * Complex.I)‖
      ≤ ‖𝓕 g t * Complex.exp (2 * π * t * x * Complex.I)‖ +
        ‖𝓕 g (-t) * Complex.exp (2 * π * ((-t : ℝ) : ℂ) * x * Complex.I)‖ := norm_add_le _ _
    _ = ‖𝓕 g t‖ + ‖𝓕 g (-t)‖ := by
        rw [norm_mul, norm_mul, norm_exp_two_pi_mul_mul_I, norm_exp_two_pi_mul_mul_I, mul_one,
          mul_one]
    _ ≤ t⁻¹ * (π⁻¹ * 2⁻¹) * (eVariationOn g univ).toReal +
        t⁻¹ * (π⁻¹ * 2⁻¹) * (eVariationOn g univ).toReal := add_le_add h1 h2
    _ = (eVariationOn g univ).toReal / π / t := by field_simp; ring

/-- **A5. Fourier integral theorem** (integral analogue of the Dirichlet–Jordan theorem): if `g` is
integrable and of bounded variation on `ℝ`, then `∫_{-T}^{T} ĝ(t) e(tx) dt → (g(x+) + g(x-))/2`. -/
theorem tendsto_partialInv (hg1 : Integrable g) (hg2 : BoundedVariationOn g Set.univ) (x : ℝ) :
    Tendsto (fun T ↦ partialInv g T x) atTop
      (𝓝 ((Function.rightLim g x + Function.leftLim g x) / 2)) := by
  have hfejer := tendsto_fejerInv_of_tendsto hg1 (hg2.tendsto_rightLim x) (hg2.tendsto_leftLim x)
  have hσ : Tendsto (fun T : ℝ ↦ (T : ℂ)⁻¹ * ∫ v in (0 : ℝ)..T, ∫ t in (0 : ℝ)..v, symmInv g x t)
      atTop (𝓝 ((Function.rightLim g x + Function.leftLim g x) / 2)) :=
    hfejer.congr' ((eventually_gt_atTop 0).mono fun T hT ↦ (cesaro_symmInv hg1 hT x).symm)
  have h := tendsto_integral_of_tendsto_cesaro
    (fun T ↦ (continuous_symmInv hg1 x).intervalIntegrable _ _)
    (fun t ht ↦ norm_symmInv_le hg1 hg2 x (by linarith)) hσ
  exact h.congr fun T ↦ (partialInv_eq hg1 T x).symm

/-- The Fourier integral theorem at a point where `g` is normalized. -/
theorem tendsto_partialInv_of_normalized (hg1 : Integrable g)
    (hg2 : BoundedVariationOn g Set.univ) {x : ℝ}
    (hx : g x = (Function.rightLim g x + Function.leftLim g x) / 2) :
    Tendsto (fun T ↦ partialInv g T x) atTop (𝓝 (g x)) := by
  rw [hx]
  exact tendsto_partialInv hg1 hg2 x

/-- A6 (the analogue of Wheeden–Zygmund (12.50)(c)): the partial inversion integrals are
uniformly bounded. -/
theorem exists_norm_partialInv_le (hg1 : Integrable g) (hg2 : BoundedVariationOn g Set.univ) :
    ∃ C, ∀ T x, 0 ≤ T → ‖partialInv g T x‖ ≤ C := by
  set V := (eVariationOn g univ).toReal with hVdef
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  set S := ‖g 0‖ + V with hSdef
  have hS : ∀ y, ‖g y‖ ≤ S := fun y ↦ by
    have h := hg2.dist_le (mem_univ y) (mem_univ 0)
    rw [dist_eq_norm] at h
    calc ‖g y‖ = ‖g 0 + (g y - g 0)‖ := by rw [add_sub_cancel]
      _ ≤ ‖g 0‖ + ‖g y - g 0‖ := norm_add_le _ _
      _ ≤ S := by rw [hSdef]; linarith
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hS 0)
  refine ⟨S + V / π, fun T x hT ↦ ?_⟩
  rcases hT.eq_or_lt with rfl | hT
  · simp only [partialInv, neg_zero, intervalIntegral.integral_same, norm_zero]
    positivity
  have hsplit : ∫ t in (0 : ℝ)..T, symmInv g x t =
      fejerInv g T x + ∫ t in (0 : ℝ)..T, ((t / T : ℝ) : ℂ) * symmInv g x t := by
    have hc := continuous_symmInv hg1 x
    rw [fejerInv_eq hg1 hT.le, ← intervalIntegral.integral_add
      (f := fun t ↦ ((1 - t / T : ℝ) : ℂ) * symmInv g x t)
      (g := fun t ↦ ((t / T : ℝ) : ℂ) * symmInv g x t)
      (((by fun_prop : Continuous fun t : ℝ ↦ ((1 - t / T : ℝ) : ℂ)).mul hc).intervalIntegrable
        _ _)
      (((by fun_prop : Continuous fun t : ℝ ↦ ((t / T : ℝ) : ℂ)).mul hc).intervalIntegrable _ _)]
    refine intervalIntegral.integral_congr fun t _ ↦ ?_
    push_cast
    ring
  have h1 : ‖fejerInv g T x‖ ≤ S := by
    rw [fejerInv_eq_integral hg1 hT]
    calc ‖∫ y, (fejerKernel T y : ℂ) * g (x - y)‖ ≤ ∫ y, S * fejerKernel T y :=
          norm_integral_le_of_norm_le ((integrable_fejerKernel hT).const_mul S)
            (Eventually.of_forall fun y ↦ by
              rw [norm_mul, Complex.norm_real,
                Real.norm_of_nonneg (fejerKernel_nonneg hT.le y), mul_comm]
              exact mul_le_mul_of_nonneg_right (hS _) (fejerKernel_nonneg hT.le y))
      _ = S := by rw [integral_const_mul, integral_fejerKernel hT, mul_one]
  have h2 : ‖∫ t in (0 : ℝ)..T, ((t / T : ℝ) : ℂ) * symmInv g x t‖ ≤ V / π := by
    calc ‖∫ t in (0 : ℝ)..T, ((t / T : ℝ) : ℂ) * symmInv g x t‖ ≤ V / π / T * |T - 0| :=
          intervalIntegral.norm_integral_le_of_norm_le_const fun t ht ↦ by
            rw [uIoc_of_le hT.le] at ht
            have ht0 : 0 < t := ht.1
            rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
            calc t / T * ‖symmInv g x t‖ ≤ t / T * (V / π / t) :=
                  mul_le_mul_of_nonneg_left (norm_symmInv_le hg1 hg2 x ht0) (by positivity)
              _ = V / π / T := by field_simp
      _ = V / π := by rw [sub_zero, abs_of_pos hT]; field_simp
  rw [partialInv_eq hg1, hsplit]
  calc ‖fejerInv g T x + ∫ t in (0 : ℝ)..T, ((t / T : ℝ) : ℂ) * symmInv g x t‖
      ≤ ‖fejerInv g T x‖ + ‖∫ t in (0 : ℝ)..T, ((t / T : ℝ) : ℂ) * symmInv g x t‖ :=
        norm_add_le _ _
    _ ≤ S + V / π := add_le_add h1 h2

end FourierIntegral
