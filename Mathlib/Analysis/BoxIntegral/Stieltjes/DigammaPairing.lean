/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Harald Helfgott
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.DigammaFourier
public import Mathlib.Analysis.BoxIntegral.Stieltjes.Fourier
public import Mathlib.Analysis.BoxIntegral.Stieltjes.VariationBounds
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Pairing `ψ(a + ibt)` with a Fourier transform

Let `a, b > 0` and `ψ = Γ'/Γ`. We prove Montgomery–Vaughan, *Multiplicative Number Theory I*,
Lemma 12.14: if `J ∈ L¹(ℝ)` has bounded variation on `ℝ` and `J(x) = J(0) + O(|x|)`, then
`lim_{T → ∞} ∫_{-T}^{T} ψ(a + ibt) Ĵ(t) dt
  = ψ(a) J(0) + (2π/b) ∫_0^∞ e^{-2πax/b} / (1 - e^{-2πx/b}) · (J(0) - J(-x)) dx`,
and the same with `ψ(a - ibt)` and `J(x)` in place of `ψ(a + ibt)` and `J(-x)`. Here
`Ĵ(t) = ∫ J(x) e(-tx) dx`, `e(θ) = e^{2πiθ}`, is Mathlib's Fourier transform `𝓕 J`.

The proof follows Montgomery–Vaughan. When `J(0) = 0`, Fubini's theorem turns the integral into
`∫ J(x) Ĝ_T(x) dx`, where `Ĝ_T(x) = ∫_{-T}^{T} ψ(a + ibt) e(-xt) dt`. On `|x| < δ` we use the
trivial bound `|Ĝ_T(x)| ≪ T log T`; on `|x| ≥ δ` we use Theorem C.5
(`Complex.norm_integral_digamma_line_mul_cexp_sub_le`), whose boundary terms are controlled
by the bound for the Fourier transform of a function of bounded variation
(`FourierTransform.fourier_bounded_variation`) applied to `x ↦ J(x)/x · 1_{|x| ≥ δ}`.
We take `δ = T^{-2/3}`. The general case follows by applying this to
`J(x) - J(0) e^{-πx²/A}` and letting `A → ∞`.

## Main results

* `Complex.tendsto_integral_digamma_line_mul_fourier_of_zero`: the case `J(0) = 0`.
* `Complex.tendsto_integral_digamma_line_mul_fourier`: Lemma 12.14, sign `+`.
* `Complex.tendsto_integral_digamma_line_neg_mul_fourier`: Lemma 12.14, sign `-`.

## AI usage

This file was written by Claude (Anthropic) in November 2026. It compiles, but has not been
reviewed by a human.
-/

@[expose] public section

open Filter Topology Set MeasureTheory Real
open scoped FourierTransform

noncomputable section

namespace Complex

variable {a b : ℝ}

/-! ### `ψ` along a vertical line -/

theorem continuous_digamma_line (ha : 0 < a) (b : ℝ) :
    Continuous fun t : ℝ ↦ digamma (a + b * t * I) :=
  continuous_iff_continuousAt.2 fun t ↦ (hasDerivAt_digamma_line ha b t).continuousAt

/-- `|ψ(a + ibt)| ≤ C log(2 + b|t|)`. -/
theorem exists_norm_digamma_line_le (ha : 0 < a) (hb : 0 < b) :
    ∃ C, 0 ≤ C ∧ ∀ t : ℝ, ‖digamma (a + b * t * I)‖ ≤ C * Real.log (2 + b * |t|) := by
  obtain ⟨C, hC⟩ := exists_norm_digamma_le ha
  have hC0 : 0 ≤ C := by
    have h := hC 0
    have hlog : 0 < Real.log (2 + |(0 : ℝ)|) := Real.log_pos (by norm_num)
    by_contra hneg
    have : C * Real.log (2 + |(0 : ℝ)|) < 0 := mul_neg_of_neg_of_pos (not_le.1 hneg) hlog
    linarith [norm_nonneg (digamma (a + ((0 : ℝ) : ℂ) * I))]
  refine ⟨C, hC0, fun t ↦ ?_⟩
  have h := hC (b * t)
  rw [abs_mul, abs_of_pos hb] at h
  have e : (a : ℂ) + b * t * I = a + ((b * t : ℝ) : ℂ) * I := by push_cast; ring
  rw [e]
  exact h

theorem norm_digamma_line_le_of_abs_le (hb : 0 < b) {C T t : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ t : ℝ, ‖digamma (a + b * t * I)‖ ≤ C * Real.log (2 + b * |t|)) (ht : |t| ≤ T) :
    ‖digamma (a + b * t * I)‖ ≤ C * Real.log (2 + b * T) := by
  refine (hC t).trans (mul_le_mul_of_nonneg_left (Real.log_le_log ?_ ?_) hC0)
  · have := mul_nonneg hb.le (abs_nonneg t); linarith
  · have := mul_le_mul_of_nonneg_left ht hb.le; linarith

theorem norm_two_mul_pi_mul_I : ‖(2 * π * I : ℂ)‖ = 2 * π := by
  simp [abs_of_pos pi_pos]

/-! ### The truncated Fourier transform `Ĝ_T` -/

/-- The truncated Fourier transform `Ĝ_T(x) = ∫_{-T}^{T} ψ(a + ibt) e(-xt) dt`. -/
def digammaLineFourier (a b T x : ℝ) : ℂ :=
  ∫ t in -T..T, digamma (a + b * t * I) * cexp (-(2 * π * x * t) * I)

theorem continuous_digammaLineFourier (ha : 0 < a) (b T : ℝ) :
    Continuous (digammaLineFourier a b T) := by
  unfold digammaLineFourier
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact ((continuous_digamma_line ha b).comp continuous_snd).mul (by fun_prop)

/-- The trivial bound `|Ĝ_T(x)| ≤ 2T · C log(2 + bT)`. -/
theorem norm_digammaLineFourier_le (hb : 0 < b) {C T : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ t : ℝ, ‖digamma (a + b * t * I)‖ ≤ C * Real.log (2 + b * |t|)) (hT : 0 ≤ T)
    (x : ℝ) : ‖digammaLineFourier a b T x‖ ≤ 2 * T * (C * Real.log (2 + b * T)) := by
  unfold digammaLineFourier
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := -T) (b := T)
    (C := C * Real.log (2 + b * T))
    (f := fun t ↦ digamma (a + b * t * I) * cexp (-(2 * π * x * t) * I)) (fun t ht ↦ by
      rw [uIoc_of_le (by linarith)] at ht
      rw [norm_mul, norm_cexp_neg_mul_I, mul_one]
      exact norm_digamma_line_le_of_abs_le hb hC0 hC (abs_le.2 ⟨ht.1.le, ht.2⟩))
  rw [show |T - -T| = 2 * T by rw [abs_of_nonneg (by linarith)]; ring] at h
  linarith

theorem integrable_mul_digammaLineFourier (ha : 0 < a) (hb : 0 < b) {J : ℝ → ℂ}
    (hJ : Integrable J) {T : ℝ} (hT : 0 ≤ T) :
    Integrable fun x ↦ J x * digammaLineFourier a b T x := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_digamma_line_le ha hb
  refine (hJ.norm.mul_const (2 * T * (C * Real.log (2 + b * T)))).mono'
    (hJ.1.mul (continuous_digammaLineFourier ha b T).aestronglyMeasurable)
    (Eventually.of_forall fun x ↦ ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_digammaLineFourier_le hb hC0 hC hT x) (norm_nonneg _)

/-- Fubini: `∫_{-T}^{T} ψ(a + ibt) Ĵ(t) dt = ∫ J(x) Ĝ_T(x) dx`. -/
theorem integral_digamma_line_mul_fourier_eq (ha : 0 < a) {J : ℝ → ℂ} (hJ : Integrable J)
    {T : ℝ} (hT : 0 ≤ T) :
    ∫ t in -T..T, digamma (a + b * t * I) * 𝓕 J t = ∫ x, J x * digammaLineFourier a b T x := by
  have hG := continuous_digamma_line ha b
  rw [intervalIntegral.integral_of_le (by linarith)]
  simp_rw [Real.fourier_real_eq_integral_exp_smul, ← integral_const_mul]
  rw [integral_integral_swap]
  · congr 1
    ext x
    rw [digammaLineFourier, intervalIntegral.integral_of_le (by linarith), ← integral_const_mul]
    congr 1
    ext t
    simp only [smul_eq_mul]
    push_cast
    ring_nf
  · refine Integrable.mono' (Integrable.mul_prod
      (hG.norm.integrableOn_Icc.mono_set Ioc_subset_Icc_self) hJ.norm) ?_
      (Eventually.of_forall fun z ↦ ?_)
    · exact ((hG.comp continuous_fst).aestronglyMeasurable).mul
        ((Continuous.aestronglyMeasurable (by fun_prop)).smul hJ.aestronglyMeasurable.comp_snd)
    · obtain ⟨t, x⟩ := z
      simp only [Function.uncurry_apply_pair, norm_mul, norm_smul,
        Complex.norm_exp_ofReal_mul_I, one_mul]
      exact le_rfl

/-! ### The kernel `M(x) = [x < 0] (2π/b) e^{2πax/b} / (1 - e^{2πx/b})` -/

/-- The kernel `M(x) = (2π/b) e^{2πax/b} / (1 - e^{2πx/b})` for `x < 0`, `M(x) = 0` for
`x ≥ 0`, of Theorem C.5. -/
def digammaPairingKernel (a b x : ℝ) : ℝ :=
  if x < 0 then (2 * π / b) * (Real.exp (2 * π * a * x / b) / (1 - Real.exp (2 * π * x / b)))
  else 0

theorem digammaPairingKernel_of_nonneg {x : ℝ} (hx : 0 ≤ x) : digammaPairingKernel a b x = 0 :=
  if_neg (not_lt.2 hx)

theorem ofReal_digammaPairingKernel (x : ℝ) :
    (digammaPairingKernel a b x : ℂ) = if x < 0 then (((2 * π / b) *
      (Real.exp (2 * π * a * x / b) / (1 - Real.exp (2 * π * x / b))) : ℝ) : ℂ) else 0 := by
  unfold digammaPairingKernel
  split_ifs <;> simp

theorem measurable_digammaPairingKernel (a b : ℝ) : Measurable (digammaPairingKernel a b) := by
  unfold digammaPairingKernel
  exact Measurable.ite measurableSet_Iio (by fun_prop) measurable_const

theorem digammaPairingKernel_nonneg (hb : 0 < b) (x : ℝ) : 0 ≤ digammaPairingKernel a b x := by
  unfold digammaPairingKernel
  split_ifs with hx
  · have hu : 0 < -(2 * π * x / b) := by
      have : 2 * π * x / b < 0 := div_neg_of_neg_of_pos (by nlinarith [pi_pos]) hb
      linarith
    have h1 := one_sub_exp_neg_pos hu
    rw [neg_neg] at h1
    positivity
  · exact le_rfl

/-- `M(x) ≤ e^{2πax/b} (2π/b + 1/|x|)` for `x < 0`. -/
theorem digammaPairingKernel_le (hb : 0 < b) {x : ℝ} (hx : x < 0) :
    digammaPairingKernel a b x ≤ Real.exp (2 * π * a * x / b) * (2 * π / b + 1 / |x|) := by
  have hx' : 0 < -x := neg_pos.2 hx
  set u := 2 * π * (-x) / b with hu
  have hu0 : 0 < u := by positivity
  have h1 : u / (1 + u) ≤ 1 - Real.exp (-u) := div_one_add_le_one_sub_exp_neg hu0.le
  have hexp : Real.exp (2 * π * x / b) = Real.exp (-u) := by congr 1; rw [hu]; ring
  have hden : 0 < 1 - Real.exp (-u) := one_sub_exp_neg_pos hu0
  unfold digammaPairingKernel
  rw [if_pos hx, hexp, abs_of_neg hx]
  have hE : 0 < Real.exp (2 * π * a * x / b) := Real.exp_pos _
  have h2 : 1 / (1 - Real.exp (-u)) ≤ (1 + u) / u := by
    rw [div_le_div_iff₀ hden hu0]
    have := (div_le_iff₀ (by positivity : (0 : ℝ) < 1 + u)).1 h1
    linarith
  calc 2 * π / b * (Real.exp (2 * π * a * x / b) / (1 - Real.exp (-u)))
      = 2 * π / b * Real.exp (2 * π * a * x / b) * (1 / (1 - Real.exp (-u))) := by ring
    _ ≤ 2 * π / b * Real.exp (2 * π * a * x / b) * ((1 + u) / u) := by gcongr
    _ = Real.exp (2 * π * a * x / b) * (2 * π / b + 1 / -x) := by
        have hx0 : x ≠ 0 := hx.ne
        rw [hu]; field_simp; ring

/-- If `F(x) = O(|x|)` and `F` is bounded on `x < 0`, then `F M` is integrable. -/
theorem integrable_mul_digammaPairingKernel (ha : 0 < a) (hb : 0 < b) {F : ℝ → ℂ}
    (hF : AEStronglyMeasurable F volume) {L V : ℝ}
    (hL : ∀ x < 0, ‖F x‖ ≤ L * |x|) (hV : ∀ x < 0, ‖F x‖ ≤ V) :
    Integrable fun x ↦ F x * (digammaPairingKernel a b x : ℂ) := by
  have hL0 : 0 ≤ L := by
    have := (norm_nonneg _).trans (hL (-1) (by norm_num)); simpa using this
  have hV0 : 0 ≤ V := (norm_nonneg _).trans (hV (-1) (by norm_num))
  have hc : 0 < 2 * π * a / b := by positivity
  have hint : Integrable ((Iic (0 : ℝ)).indicator
      fun x ↦ (2 * π / b * V + L) * Real.exp (2 * π * a / b * x)) :=
    IntegrableOn.integrable_indicator ((integrableOn_exp_mul_Iic hc 0).const_mul _)
      measurableSet_Iic
  refine hint.mono' (hF.mul (Complex.measurable_ofReal.comp
    (measurable_digammaPairingKernel a b)).aestronglyMeasurable)
    (Eventually.of_forall fun x ↦ ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (digammaPairingKernel_nonneg hb x)]
  rcases lt_or_ge x 0 with hx | hx
  · rw [indicator_of_mem (show x ∈ Iic 0 from hx.le)]
    have hk := digammaPairingKernel_le (a := a) hb hx
    have hxabs : 0 < |x| := abs_pos.2 hx.ne
    calc ‖F x‖ * digammaPairingKernel a b x
        ≤ ‖F x‖ * (Real.exp (2 * π * a * x / b) * (2 * π / b + 1 / |x|)) :=
          mul_le_mul_of_nonneg_left hk (norm_nonneg _)
      _ = Real.exp (2 * π * a * x / b) * (2 * π / b * ‖F x‖ + ‖F x‖ / |x|) := by ring
      _ ≤ Real.exp (2 * π * a * x / b) * (2 * π / b * V + L) := by
          gcongr
          · exact hV x hx
          · rw [div_le_iff₀ hxabs]; exact hL x hx
      _ = (2 * π / b * V + L) * Real.exp (2 * π * a / b * x) := by
          rw [mul_comm]; congr 2; ring
  · rw [digammaPairingKernel_of_nonneg hx, mul_zero]
    exact indicator_nonneg (fun _ _ ↦ by positivity) x

/-! ### The cut-off function `x ↦ J(x)/x · 1_{|x| ≥ δ}` -/

/-- The function `x ↦ x⁻¹ J(x) 1_{|x| ≥ δ}`. -/
def invCutoffSMul (J : ℝ → ℂ) (δ x : ℝ) : ℂ := (if δ ≤ |x| then x⁻¹ else 0) • J x

theorem abs_ite_inv_le {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    |(if δ ≤ |x| then x⁻¹ else 0)| ≤ δ⁻¹ := by
  split_ifs with h
  · rw [abs_inv]; exact inv_anti₀ hδ h
  · simp [hδ.le]

theorem measurable_ite_inv (δ : ℝ) : Measurable fun x : ℝ ↦ if δ ≤ |x| then x⁻¹ else 0 :=
  Measurable.ite (measurableSet_le measurable_const continuous_abs.measurable) measurable_inv
    measurable_const

theorem integrable_invCutoffSMul {J : ℝ → ℂ} (hJ : Integrable J) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (invCutoffSMul J δ) := by
  refine (hJ.norm.const_mul δ⁻¹).mono' ((measurable_ite_inv δ).aestronglyMeasurable.smul hJ.1)
    (Eventually.of_forall fun x ↦ ?_)
  unfold invCutoffSMul
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (abs_ite_inv_le hδ x) (norm_nonneg _)

theorem eVariationOn_invCutoffSMul_le {J : ℝ → ℂ} (hJv : BoundedVariationOn J univ) {V : ℝ}
    (hJV : ∀ x, ‖J x‖ ≤ V) {δ : ℝ} (hδ : 0 < δ) :
    eVariationOn (invCutoffSMul J δ) univ ≤
      ENNReal.ofReal (δ⁻¹ * (eVariationOn J univ).toReal + V * (4 / δ)) :=
  eVariationOn_smul_le_ofReal (fun x _ ↦ abs_ite_inv_le hδ x) (fun x _ ↦ hJV x)
    (eVariationOn_inv_cutoff_le hδ univ) (ENNReal.ofReal_toReal hJv).ge (inv_pos.2 hδ).le
    ((norm_nonneg _).trans (hJV 0)) (by positivity) ENNReal.toReal_nonneg

theorem fourier_eq_integral_e_mul (g : ℝ → ℂ) (ξ : ℝ) :
    𝓕 g ξ = ∫ x, FourierTransform.e ξ x * g x := by
  simp [Real.fourier_real_eq_integral_exp_smul, FourierTransform.e]

theorem e_eq_cexp (ξ x : ℝ) : FourierTransform.e ξ x = cexp (-(2 * π * x * ξ) * I) := by
  simp only [FourierTransform.e]
  push_cast
  ring_nf

/-- The Fourier transform of `x ↦ J(x)/x · 1_{|x| ≥ δ}` is `≪ 1/(|ξ| δ)`. -/
theorem norm_fourier_invCutoffSMul_le {J : ℝ → ℂ} (hJi : Integrable J)
    (hJv : BoundedVariationOn J univ) {V : ℝ} (hJV : ∀ x, ‖J x‖ ≤ V) {δ : ℝ} (hδ : 0 < δ)
    {ξ : ℝ} (hξ : ξ ≠ 0) :
    ‖𝓕 (invCutoffSMul J δ) ξ‖ ≤
      |ξ|⁻¹ * (π⁻¹ * 2⁻¹) * (δ⁻¹ * (eVariationOn J univ).toReal + V * (4 / δ)) := by
  have hV0 : 0 ≤ V := (norm_nonneg _).trans (hJV 0)
  have hvar := eVariationOn_invCutoffSMul_le hJv hJV hδ
  refine (FourierTransform.fourier_bounded_variation (integrable_invCutoffSMul hJi hδ)
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvar) hξ).trans ?_
  gcongr
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hvar

/-! ### The case `J(0) = 0` -/

/-- Montgomery–Vaughan, Lemma 12.14, in the case `J(0) = 0`: if `J ∈ L¹(ℝ)` has bounded
variation on `ℝ` and `‖J(x)‖ ≤ L|x|` for all `x`, then
`∫_{-T}^{T} ψ(a + ibt) Ĵ(t) dt → -∫ J(x) M(x) dx`, where `M = digammaPairingKernel a b`. -/
theorem tendsto_integral_digamma_line_mul_fourier_of_zero (ha : 0 < a) (hb : 0 < b)
    {J : ℝ → ℂ} (hJi : Integrable J) (hJv : BoundedVariationOn J univ) {L : ℝ}
    (hJL : ∀ x, ‖J x‖ ≤ L * |x|) :
    Tendsto (fun T : ℝ ↦ ∫ t in -T..T, digamma (a + b * t * I) * 𝓕 J t) atTop
      (𝓝 (-∫ x, J x * (digammaPairingKernel a b x : ℂ))) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_digamma_line_le ha hb
  obtain ⟨C₅, hC₅⟩ := norm_integral_digamma_line_mul_cexp_sub_le ha hb
  have hC₅0 : 0 ≤ C₅ := by
    have h := (norm_nonneg _).trans (hC₅ 1 one_ne_zero 1 le_rfl)
    simpa using h
  set V := (eVariationOn J univ).toReal with hVdef
  have hJ0 : J 0 = 0 := by
    have h := hJL 0
    rw [abs_zero, mul_zero] at h
    exact norm_le_zero_iff.1 h
  have hJV : ∀ x, ‖J x‖ ≤ V := fun x ↦ by
    have h := hJv.dist_le (mem_univ x) (mem_univ 0)
    rwa [hJ0, dist_zero_right] at h
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  have hL0 : 0 ≤ L := by
    have h := (norm_nonneg _).trans (hJL 1); simpa using h
  set M : ℝ → ℂ := fun x ↦ (digammaPairingKernel a b x : ℂ) with hMdef
  have hJM : Integrable fun x ↦ J x * M x :=
    integrable_mul_digammaPairingKernel ha hb hJi.1 (fun x _ ↦ hJL x) (fun x _ ↦ hJV x)
  have hℓ : ∀ T : ℝ, 1 ≤ T → 0 ≤ Real.log (2 + b * T) := fun T hT ↦
    Real.log_nonneg (by nlinarith)
  -- the scales `s = T^{1/3}` and `δ = s⁻² = T^{-2/3}`
  set s : ℝ → ℝ := fun T ↦ T ^ ((1 : ℝ) / 3) with hsdef
  set δ : ℝ → ℝ := fun T ↦ (s T ^ 2)⁻¹ with hδdef
  have hs_pos : ∀ T : ℝ, 1 ≤ T → 0 < s T := fun T hT ↦ Real.rpow_pos_of_pos (by linarith) _
  have hs3 : ∀ T : ℝ, 1 ≤ T → s T ^ 3 = T := fun T hT ↦ by
    simp only [hsdef]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    norm_num
  have hδ_pos : ∀ T : ℝ, 1 ≤ T → 0 < δ T := fun T hT ↦ by
    have := hs_pos T hT
    simp only [hδdef]
    positivity
  have hδT : ∀ T : ℝ, 1 ≤ T → (δ T)⁻¹ / T = (s T)⁻¹ := fun T hT ↦ by
    have h0 := hs_pos T hT
    have h3 := hs3 T hT
    simp only [hδdef, inv_inv]
    generalize s T = σ at h0 h3 ⊢
    subst h3
    field_simp
  have hTδ : ∀ T : ℝ, 1 ≤ T → T * δ T ^ 2 = (s T)⁻¹ := fun T hT ↦ by
    have h0 := hs_pos T hT
    have h3 := hs3 T hT
    simp only [hδdef]
    generalize s T = σ at h0 h3 ⊢
    subst h3
    field_simp
  have hs_top : Tendsto s atTop atTop := tendsto_rpow_atTop (by norm_num)
  have hs_inv : Tendsto (fun T ↦ (s T)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hs_top
  have hδ_zero : Tendsto δ atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop two_ne_zero).comp hs_top)
  have hlog : Tendsto (fun T ↦ Real.log (2 + b * T) / s T) atTop (𝓝 0) := by
    have h1 : Tendsto (fun T ↦ Real.log T / s T) atTop (𝓝 0) :=
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).tendsto_div_nhds_zero
    have h2 := h1.add (hs_inv.const_mul (Real.log (2 + b)))
    rw [mul_zero, add_zero] at h2
    refine squeeze_zero' ?_ ?_ h2
    · filter_upwards [eventually_ge_atTop 1] with T hT
      exact div_nonneg (hℓ T hT) (hs_pos T hT).le
    · filter_upwards [eventually_ge_atTop 1] with T hT
      have hlogle : Real.log (2 + b * T) ≤ Real.log T + Real.log (2 + b) := by
        rw [← Real.log_mul (by linarith : (0 : ℝ) < T).ne' (by linarith : (0 : ℝ) < 2 + b).ne']
        exact Real.log_le_log (by nlinarith) (by nlinarith)
      calc Real.log (2 + b * T) / s T ≤ (Real.log T + Real.log (2 + b)) / s T :=
            div_le_div_of_nonneg_right hlogle (hs_pos T hT).le
        _ = Real.log T / s T + Real.log (2 + b) * (s T)⁻¹ := by ring
  -- the pieces of the decomposition of `J Ĝ_T`
  set F : ℝ → ℝ → ℂ := fun T x ↦ J x * digammaLineFourier a b T x with hFdef
  set g : ℝ → ℝ → ℂ := fun T ↦ invCutoffSMul J (δ T) with hgdef
  set c₁ : ℝ → ℂ := fun T ↦ -digamma (a + b * T * I) / (2 * π * I) with hc₁def
  set c₂ : ℝ → ℂ := fun T ↦ digamma (a - b * T * I) / (2 * π * I) with hc₂def
  set near : ℝ → ℝ → ℂ := fun T ↦ (Ioo (-δ T) (δ T)).indicator (F T) with hneardef
  set farM : ℝ → ℝ → ℂ := fun T ↦ {x : ℝ | δ T ≤ |x|}.indicator (fun x ↦ J x * M x)
    with hfardef
  set R : ℝ → ℝ → ℂ := fun T x ↦ F T x - near T x - c₁ T * (FourierTransform.e T x * g T x) -
    c₂ T * (FourierTransform.e (-T) x * g T x) + farM T x with hRdef
  have hmeasS : ∀ T, MeasurableSet {x : ℝ | δ T ≤ |x|} := fun T ↦
    measurableSet_le measurable_const continuous_abs.measurable
  -- the decomposition
  have hmain : ∀ᶠ T in atTop, ∫ t in -T..T, digamma (a + b * t * I) * 𝓕 J t =
      (∫ x, near T x) + c₁ T * 𝓕 (g T) T + c₂ T * 𝓕 (g T) (-T) - (∫ x, farM T x) +
        ∫ x, R T x := by
    filter_upwards [eventually_ge_atTop 1] with T hT
    have hδ0 := hδ_pos T hT
    rw [integral_digamma_line_mul_fourier_eq ha hJi (by linarith : (0 : ℝ) ≤ T)]
    change ∫ x, F T x = _
    have hF : Integrable (F T) := integrable_mul_digammaLineFourier ha hb hJi (by linarith)
    have hnear : Integrable (near T) := hF.indicator measurableSet_Ioo
    have hg : Integrable (g T) := integrable_invCutoffSMul hJi hδ0
    have he1 : Integrable fun x ↦ c₁ T * (FourierTransform.e T x * g T x) :=
      (FourierTransform.integrable_e_mul T hg).const_mul _
    have he2 : Integrable fun x ↦ c₂ T * (FourierTransform.e (-T) x * g T x) :=
      (FourierTransform.integrable_e_mul (-T) hg).const_mul _
    have hfar : Integrable (farM T) := hJM.indicator (hmeasS T)
    have h1 : Integrable fun x ↦ F T x - near T x := hF.sub hnear
    have h2 : Integrable fun x ↦ F T x - near T x - c₁ T * (FourierTransform.e T x * g T x) :=
      h1.sub he1
    have h3 : Integrable fun x ↦ F T x - near T x - c₁ T * (FourierTransform.e T x * g T x) -
        c₂ T * (FourierTransform.e (-T) x * g T x) := h2.sub he2
    have hR : ∫ x, R T x = (∫ x, F T x) - (∫ x, near T x) - c₁ T * 𝓕 (g T) T -
        c₂ T * 𝓕 (g T) (-T) + ∫ x, farM T x := by
      simp only [hRdef]
      rw [integral_add h3 hfar, integral_sub h2 he2, integral_sub h1 he1, integral_sub hF hnear,
        integral_const_mul, integral_const_mul, fourier_eq_integral_e_mul,
        fourier_eq_integral_e_mul]
    rw [hR]
    ring
  -- `|x| < δ`
  have t1 : Tendsto (fun T ↦ ∫ x, near T x) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun T ↦ 4 * L * C * (Real.log (2 + b * T) / s T)) ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with T hT
      have hδ0 := hδ_pos T hT
      simp only [hneardef]
      rw [integral_indicator measurableSet_Ioo]
      calc ‖∫ x in Ioo (-δ T) (δ T), F T x‖
          ≤ (L * δ T * (2 * T * (C * Real.log (2 + b * T)))) *
              volume.real (Ioo (-δ T) (δ T)) := by
            refine norm_setIntegral_le_of_norm_le_const measure_Ioo_lt_top fun x hx ↦ ?_
            have hxδ : |x| ≤ δ T := (abs_lt.2 hx).le
            simp only [hFdef, norm_mul]
            exact mul_le_mul ((hJL x).trans (mul_le_mul_of_nonneg_left hxδ hL0))
              (norm_digammaLineFourier_le hb hC0 hC (by linarith) x) (norm_nonneg _)
              (mul_nonneg hL0 hδ0.le)
        _ = 4 * L * C * (Real.log (2 + b * T) * (T * δ T ^ 2)) := by
            rw [Real.volume_real_Ioo_of_le (by linarith)]; ring
        _ = 4 * L * C * (Real.log (2 + b * T) / s T) := by rw [hTδ T hT]; ring
    · have := hlog.const_mul (4 * L * C); rwa [mul_zero] at this
  -- the boundary terms
  have hc₁ : ∀ T : ℝ, 1 ≤ T → ‖c₁ T‖ ≤ C * Real.log (2 + b * T) / (2 * π) := fun T hT ↦ by
    simp only [hc₁def, norm_div, norm_neg, norm_two_mul_pi_mul_I]
    gcongr
    exact norm_digamma_line_le_of_abs_le hb hC0 hC (by rw [abs_of_pos (by linarith)])
  have hc₂ : ∀ T : ℝ, 1 ≤ T → ‖c₂ T‖ ≤ C * Real.log (2 + b * T) / (2 * π) := fun T hT ↦ by
    simp only [hc₂def, norm_div, norm_two_mul_pi_mul_I]
    gcongr
    have e : (a : ℂ) - b * T * I = a + b * ((-T : ℝ) : ℂ) * I := by push_cast; ring
    rw [e]
    exact norm_digamma_line_le_of_abs_le hb hC0 hC (by rw [abs_neg, abs_of_pos (by linarith)])
  have hfour : ∀ T : ℝ, 1 ≤ T → ∀ ξ : ℝ, |ξ| = T →
      ‖𝓕 (g T) ξ‖ ≤ T⁻¹ * (π⁻¹ * 2⁻¹) * ((δ T)⁻¹ * V + V * (4 / δ T)) := fun T hT ξ hξ ↦ by
    have hξ0 : ξ ≠ 0 := by
      rw [← abs_ne_zero, hξ]; exact (by linarith : (0 : ℝ) < T).ne'
    have h := norm_fourier_invCutoffSMul_le hJi hJv hJV (hδ_pos T hT) hξ0
    rwa [hξ, ← hVdef] at h
  have hK : 0 ≤ C / (2 * π) * (π⁻¹ * 2⁻¹) * (5 * V) := by positivity
  have hbd : ∀ T : ℝ, 1 ≤ T → ∀ c : ℂ, ‖c‖ ≤ C * Real.log (2 + b * T) / (2 * π) →
      ∀ ξ : ℝ, |ξ| = T → ‖c * 𝓕 (g T) ξ‖ ≤
        C / (2 * π) * (π⁻¹ * 2⁻¹) * (5 * V) * (Real.log (2 + b * T) / s T) := by
    intro T hT c hc ξ hξ
    have hδ0 := hδ_pos T hT
    have hT0 : T ≠ 0 := (by linarith : (0 : ℝ) < T).ne'
    have hδne : δ T ≠ 0 := hδ0.ne'
    rw [norm_mul]
    calc ‖c‖ * ‖𝓕 (g T) ξ‖ ≤ (C * Real.log (2 + b * T) / (2 * π)) *
          (T⁻¹ * (π⁻¹ * 2⁻¹) * ((δ T)⁻¹ * V + V * (4 / δ T))) :=
          mul_le_mul hc (hfour T hT ξ hξ) (norm_nonneg _)
            (div_nonneg (mul_nonneg hC0 (hℓ T hT)) (by positivity))
      _ = C / (2 * π) * (π⁻¹ * 2⁻¹) * (5 * V) * (Real.log (2 + b * T) * ((δ T)⁻¹ / T)) := by
          field_simp
          ring
      _ = _ := by rw [hδT T hT]; ring
  have t2 : Tendsto (fun T ↦ c₁ T * 𝓕 (g T) T) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun T ↦ C / (2 * π) * (π⁻¹ * 2⁻¹) * (5 * V) *
      (Real.log (2 + b * T) / s T)) ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with T hT
      exact hbd T hT _ (hc₁ T hT) T (abs_of_pos (by linarith))
    · have := hlog.const_mul (C / (2 * π) * (π⁻¹ * 2⁻¹) * (5 * V)); rwa [mul_zero] at this
  have t3 : Tendsto (fun T ↦ c₂ T * 𝓕 (g T) (-T)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun T ↦ C / (2 * π) * (π⁻¹ * 2⁻¹) * (5 * V) *
      (Real.log (2 + b * T) / s T)) ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with T hT
      exact hbd T hT _ (hc₂ T hT) (-T) (by rw [abs_neg, abs_of_pos (by linarith)])
    · have := hlog.const_mul (C / (2 * π) * (π⁻¹ * 2⁻¹) * (5 * V)); rwa [mul_zero] at this
  -- the main term
  have t4 : Tendsto (fun T ↦ ∫ x, farM T x) atTop (𝓝 (∫ x, J x * M x)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x ↦ ‖J x * M x‖)
      (Eventually.of_forall fun T ↦ (hJM.indicator (hmeasS T)).1)
      (Eventually.of_forall fun T ↦ Eventually.of_forall fun x ↦ ?_) hJM.norm
      (Eventually.of_forall fun x ↦ ?_)
    · simp only [hfardef]
      rw [norm_indicator_eq_indicator_norm]
      exact indicator_le_self' (fun _ _ ↦ norm_nonneg _) x
    · rcases eq_or_ne x 0 with rfl | hx
      · simp only [hfardef, Set.indicator_apply, hJ0, zero_mul, ite_self]
        exact tendsto_const_nhds
      · have hev : ∀ᶠ T in atTop, δ T ≤ |x| :=
          (hδ_zero.eventually (gt_mem_nhds (abs_pos.2 hx))).mono fun _ h ↦ h.le
        refine tendsto_const_nhds.congr' (hev.mono fun T hT ↦ ?_)
        simp only [hfardef]
        rw [indicator_of_mem (show x ∈ {x : ℝ | δ T ≤ |x|} from hT)]
  -- the error term of Theorem C.5
  have t5 : Tendsto (fun T ↦ ∫ x, R T x) atTop (𝓝 0) := by
    set N := ∫ x, ‖J x‖ with hNdef
    refine squeeze_zero_norm' (a := fun T ↦ C₅ * N * T⁻¹ + 2 * C₅ * L * (s T)⁻¹) ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with T hT
      have hδ0 := hδ_pos T hT
      have hT0 : 0 < T := by linarith
      have hind_int : Integrable ((Icc (-1 : ℝ) 1).indicator (fun _ ↦ (1 : ℝ))) :=
        IntegrableOn.integrable_indicator continuous_const.integrableOn_Icc measurableSet_Icc
      set D : ℝ → ℝ := fun x ↦ C₅ / T * ‖J x‖ +
        C₅ / T * (L / δ T) * (Icc (-1 : ℝ) 1).indicator (fun _ ↦ (1 : ℝ)) x with hDdef
      have hD : Integrable D := (hJi.norm.const_mul _).add (hind_int.const_mul _)
      have hRx : ∀ x, ‖R T x‖ ≤ D x := by
        intro x
        have hind0 : 0 ≤ (Icc (-1 : ℝ) 1).indicator (fun _ ↦ (1 : ℝ)) x :=
          indicator_nonneg (fun _ _ ↦ zero_le_one) _
        have hD0 : 0 ≤ D x := add_nonneg (mul_nonneg (div_nonneg hC₅0 hT0.le) (norm_nonneg _))
          (mul_nonneg (mul_nonneg (div_nonneg hC₅0 hT0.le) (div_nonneg hL0 hδ0.le)) hind0)
        by_cases hxδ : δ T ≤ |x|
        · have hx0 : x ≠ 0 := by rintro rfl; rw [abs_zero] at hxδ; linarith
          have hxnot : x ∉ Ioo (-δ T) (δ T) := fun h ↦ by have := abs_lt.2 h; linarith
          have he1 : FourierTransform.e T x = cexp (-(2 * π * x * T) * I) := e_eq_cexp T x
          have he2 : FourierTransform.e (-T) x = cexp ((2 * π * x * T) * I) := by
            rw [e_eq_cexp]; congr 1; push_cast; ring
          have key : R T x = J x * ((∫ t in -T..T, digamma (a + b * t * I) *
              cexp (-(2 * π * x * t) * I)) -
              (-(digamma (a + b * T * I) * cexp (-(2 * π * x * T) * I)) / (2 * π * x * I) +
                digamma (a - b * T * I) * cexp ((2 * π * x * T) * I) / (2 * π * x * I) -
                if x < 0 then (((2 * π / b) * (Real.exp (2 * π * a * x / b) /
                  (1 - Real.exp (2 * π * x / b))) : ℝ) : ℂ) else 0)) := by
            simp only [hRdef, hneardef, hfardef, hFdef, hgdef, hc₁def, hc₂def, hMdef,
              indicator_of_notMem hxnot, indicator_of_mem (show x ∈ {x : ℝ | δ T ≤ |x|} from hxδ),
              invCutoffSMul, if_pos hxδ, he1, he2, ← ofReal_digammaPairingKernel,
              digammaLineFourier, Complex.real_smul]
            have hx0' : (x : ℂ) ≠ 0 := ofReal_ne_zero.2 hx0
            have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 pi_ne_zero
            push_cast
            field_simp
            ring_nf
          rw [key, norm_mul]
          refine (mul_le_mul_of_nonneg_left (hC₅ x hx0 T hT) (norm_nonneg _)).trans ?_
          have hx2 : 0 < x ^ 2 := by positivity
          simp only [hDdef]
          rcases le_or_gt 1 |x| with h1 | h1
          · have hx21 : 1 ≤ x ^ 2 := by nlinarith [sq_abs x, abs_nonneg x]
            have h' : ‖J x‖ * (C₅ / (x ^ 2 * T)) ≤ C₅ / T * ‖J x‖ := by
              rw [show ‖J x‖ * (C₅ / (x ^ 2 * T)) = C₅ / T * ‖J x‖ / x ^ 2 by ring]
              exact div_le_self (by positivity) hx21
            have h0 : 0 ≤ C₅ / T * (L / δ T) * (Icc (-1 : ℝ) 1).indicator (fun _ ↦ (1 : ℝ)) x :=
              mul_nonneg (mul_nonneg (div_nonneg hC₅0 hT0.le) (div_nonneg hL0 hδ0.le)) hind0
            linarith
          · have hmem : x ∈ Icc (-1 : ℝ) 1 := by
              have := abs_lt.1 h1; exact ⟨this.1.le, this.2.le⟩
            rw [indicator_of_mem hmem, mul_one]
            have hJx : ‖J x‖ * δ T ≤ L * x ^ 2 :=
              calc ‖J x‖ * δ T ≤ (L * |x|) * |x| :=
                    mul_le_mul (hJL x) hxδ hδ0.le (mul_nonneg hL0 (abs_nonneg x))
                _ = L * x ^ 2 := by rw [mul_assoc, ← sq, sq_abs]
            have h' : ‖J x‖ * (C₅ / (x ^ 2 * T)) ≤ C₅ / T * (L / δ T) := by
              rw [show ‖J x‖ * (C₅ / (x ^ 2 * T)) = C₅ / T * (‖J x‖ / x ^ 2) by ring]
              refine mul_le_mul_of_nonneg_left ?_ (div_nonneg hC₅0 hT0.le)
              rw [div_le_div_iff₀ hx2 hδ0]
              linarith
            have h0 : 0 ≤ C₅ / T * ‖J x‖ := mul_nonneg (div_nonneg hC₅0 hT0.le) (norm_nonneg _)
            linarith
        · have hxin : x ∈ Ioo (-δ T) (δ T) := abs_lt.1 (not_le.1 hxδ)
          have h0 : R T x = 0 := by
            simp only [hRdef, hneardef, hfardef, hgdef, invCutoffSMul, indicator_of_mem hxin,
              indicator_of_notMem (show x ∉ {x : ℝ | δ T ≤ |x|} from hxδ), if_neg hxδ,
              zero_smul, mul_zero, sub_self, add_zero]
          rw [h0, norm_zero]
          exact hD0
      calc ‖∫ x, R T x‖ ≤ ∫ x, D x := norm_integral_le_of_norm_le hD (Eventually.of_forall hRx)
        _ = C₅ / T * N + C₅ / T * (L / δ T) * 2 := by
            simp only [hDdef]
            rw [integral_add (hJi.norm.const_mul _) (hind_int.const_mul _), integral_const_mul,
              integral_const_mul, integral_indicator_const _ measurableSet_Icc,
              Real.volume_real_Icc_of_le (by norm_num), ← hNdef]
            norm_num
        _ = C₅ * N * T⁻¹ + 2 * C₅ * L * ((δ T)⁻¹ / T) := by ring
        _ = C₅ * N * T⁻¹ + 2 * C₅ * L * (s T)⁻¹ := by rw [hδT T hT]
    · have := (tendsto_inv_atTop_zero.const_mul (C₅ * N)).add (hs_inv.const_mul (2 * C₅ * L))
      rwa [mul_zero, mul_zero, add_zero] at this
  have hlim := (((t1.add t2).add t3).sub t4).add t5
  rw [zero_add, zero_add, zero_sub, add_zero] at hlim
  exact hlim.congr' (hmain.mono fun T hT ↦ hT.symm)

/-! ### The Gaussian `x ↦ e^{-πx²/A}` and the general case -/

/-- The Gaussian `x ↦ e^{-πx²/A}`, whose Fourier transform is `t ↦ √A e^{-πAt²}`. -/
def gaussAux (A x : ℝ) : ℂ := ((Real.exp (-(π * A⁻¹) * x ^ 2) : ℝ) : ℂ)

theorem gaussAux_zero (A : ℝ) : gaussAux A 0 = 1 := by simp [gaussAux]

theorem continuous_gaussAux (A : ℝ) : Continuous (gaussAux A) := by
  unfold gaussAux; fun_prop

theorem integrable_gaussAux {A : ℝ} (hA : 0 < A) : Integrable (gaussAux A) :=
  (integrable_exp_neg_mul_sq (by positivity : 0 < π * A⁻¹)).ofReal

theorem eVariationOn_gaussAux_le {A : ℝ} (hA : 0 ≤ A) : eVariationOn (gaussAux A) univ ≤ 2 := by
  have h := eVariationOn_exp_neg_mul_sq_le (c := π * A⁻¹) (by positivity) univ
  have heq : gaussAux A = (fun r : ℝ ↦ (r : ℂ)) ∘ fun x : ℝ ↦ Real.exp (-(π * A⁻¹ * x ^ 2)) := by
    funext x; simp only [gaussAux, Function.comp, neg_mul]
  rw [heq]
  refine ((Complex.isometry_ofReal.lipschitz.lipschitzOnWith).comp_eVariationOn_le
    (mapsTo_univ _ _)).trans ?_
  simpa using h

theorem fourier_gaussAux {A : ℝ} (hA : 0 < A) (t : ℝ) :
    𝓕 (gaussAux A) t = ((√A * Real.exp (-π * A * t ^ 2) : ℝ) : ℂ) := by
  have hb : 0 < ((A : ℂ)⁻¹).re := by rw [← ofReal_inv, ofReal_re]; positivity
  have h := congr_fun (fourier_gaussian_pi hb) t
  have heq : gaussAux A = fun x : ℝ ↦ cexp (-π * (A : ℂ)⁻¹ * x ^ 2) := by
    funext x; simp only [gaussAux]; push_cast; ring_nf
  rw [heq, h]
  have hpow : ((A : ℂ)⁻¹) ^ (1 / 2 : ℂ) = (((√A)⁻¹ : ℝ) : ℂ) := by
    rw [← ofReal_inv, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_cpow (inv_nonneg.2 hA.le), Real.sqrt_eq_rpow, Real.inv_rpow hA.le]
  rw [hpow]
  have hA' : (A : ℂ) ≠ 0 := ofReal_ne_zero.2 hA.ne'
  have hsA : ((√A : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 (Real.sqrt_pos.2 hA).ne'
  push_cast
  field_simp

theorem norm_gaussAux_sub_one_le {A : ℝ} (hA : 1 ≤ A) (x : ℝ) :
    ‖gaussAux A x - 1‖ ≤ 1 - Real.exp (-π * x ^ 2) := by
  have hA0 : 0 < A := by linarith
  have hc : 0 ≤ π * A⁻¹ := by positivity
  have h1 : Real.exp (-(π * A⁻¹) * x ^ 2) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg x])
  have h2 : Real.exp (-π * x ^ 2) ≤ Real.exp (-(π * A⁻¹) * x ^ 2) := by
    apply Real.exp_le_exp.2
    have : π * A⁻¹ ≤ π := by
      have : A⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hA
      nlinarith [pi_pos]
    nlinarith [sq_nonneg x]
  rw [gaussAux, ← ofReal_one, ← ofReal_sub, norm_real, Real.norm_eq_abs,
    abs_of_nonpos (by linarith)]
  linarith

theorem one_sub_exp_neg_pi_mul_sq_nonneg (x : ℝ) : 0 ≤ 1 - Real.exp (-π * x ^ 2) := by
  have : Real.exp (-π * x ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [pi_pos, sq_nonneg x])
  linarith

theorem one_sub_exp_neg_pi_mul_sq_le_one (x : ℝ) : 1 - Real.exp (-π * x ^ 2) ≤ 1 := by
  linarith [Real.exp_pos (-π * x ^ 2)]

theorem one_sub_exp_neg_pi_mul_sq_le (x : ℝ) : 1 - Real.exp (-π * x ^ 2) ≤ (π + 1) * |x| := by
  rcases le_or_gt |x| 1 with h | h
  · have h1 : 1 - Real.exp (-π * x ^ 2) ≤ π * x ^ 2 := by
      linarith [Real.add_one_le_exp (-π * x ^ 2)]
    have h2 : x ^ 2 ≤ |x| := by rw [← sq_abs]; nlinarith [abs_nonneg x]
    nlinarith [pi_pos, abs_nonneg x]
  · nlinarith [pi_pos, one_sub_exp_neg_pi_mul_sq_le_one x]

/-- `|ψ(a + ibt)| ≤ C (1 + b|t|)`. -/
theorem exists_norm_digamma_line_le_linear (ha : 0 < a) (hb : 0 < b) :
    ∃ C, 0 ≤ C ∧ ∀ t : ℝ, ‖digamma (a + b * t * I)‖ ≤ C * (1 + b * |t|) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_digamma_line_le ha hb
  refine ⟨C, hC0, fun t ↦ (hC t).trans (mul_le_mul_of_nonneg_left ?_ hC0)⟩
  have hpos : 0 < 2 + b * |t| := by have := mul_nonneg hb.le (abs_nonneg t); linarith
  have h := Real.log_le_sub_one_of_pos hpos
  linarith

theorem integrable_digamma_line_mul_gaussian (ha : 0 < a) (hb : 0 < b) {c : ℝ} (hc : 0 < c) :
    Integrable fun t : ℝ ↦ digamma (a + b * t * I) * ((Real.exp (-c * t ^ 2) : ℝ) : ℂ) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_digamma_line_le_linear ha hb
  have h1 := integrable_exp_neg_mul_sq hc
  have h2 := (integrable_mul_exp_neg_mul_sq hc).norm
  refine ((h1.add (h2.const_mul b)).const_mul C).mono'
    ((continuous_digamma_line ha b).aestronglyMeasurable.mul
      (by fun_prop : Continuous fun t : ℝ ↦ ((Real.exp (-c * t ^ 2) : ℝ) : ℂ)).aestronglyMeasurable)
    (Eventually.of_forall fun t ↦ ?_)
  have he : 0 < Real.exp (-c * t ^ 2) := Real.exp_pos _
  change _ ≤ C * (Real.exp (-c * t ^ 2) + b * ‖t * Real.exp (-c * t ^ 2)‖)
  simp only [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos he]
  calc ‖digamma (a + b * t * I)‖ * Real.exp (-c * t ^ 2)
      ≤ C * (1 + b * |t|) * Real.exp (-c * t ^ 2) := mul_le_mul_of_nonneg_right (hC t) he.le
    _ = C * (Real.exp (-c * t ^ 2) + b * (|t| * Real.exp (-c * t ^ 2))) := by ring

/-- `∫ ψ(a + ibt) √A e^{-πAt²} dt → ψ(a)` as `A → ∞`. -/
theorem tendsto_integral_digamma_line_mul_fourier_gaussAux (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun A ↦ ∫ t : ℝ, digamma (a + b * t * I) * 𝓕 (gaussAux A) t) atTop
      (𝓝 (digamma a)) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_digamma_line_le_linear ha hb
  set G : ℝ → ℂ := fun t ↦ digamma (a + b * t * I) with hGdef
  have hGc : Continuous G := continuous_digamma_line ha b
  have hsub : ∀ A : ℝ, 0 < A → ∫ t, G t * 𝓕 (gaussAux A) t =
      ∫ u, G (u / √A) * ((Real.exp (-π * u ^ 2) : ℝ) : ℂ) := by
    intro A hA
    have hsA : 0 < √A := Real.sqrt_pos.2 hA
    simp_rw [fourier_gaussAux hA]
    have h := Measure.integral_comp_div
      (fun t ↦ G t * ((√A * Real.exp (-π * A * t ^ 2) : ℝ) : ℂ)) (√A)
    have hpt : ∀ u : ℝ, G (u / √A) * ((√A * Real.exp (-π * A * (u / √A) ^ 2) : ℝ) : ℂ) =
        (√A : ℂ) * (G (u / √A) * ((Real.exp (-π * u ^ 2) : ℝ) : ℂ)) := by
      intro u
      have : -π * A * (u / √A) ^ 2 = -π * u ^ 2 := by
        rw [div_pow, Real.sq_sqrt hA.le]; field_simp
      rw [this]; push_cast; ring
    simp only [hpt, integral_const_mul] at h
    rw [abs_of_pos hsA, Complex.real_smul] at h
    exact (mul_left_cancel₀ (ofReal_ne_zero.2 hsA.ne') h).symm
  have hlim : Tendsto (fun A ↦ ∫ u, G (u / √A) * ((Real.exp (-π * u ^ 2) : ℝ) : ℂ)) atTop
      (𝓝 (∫ u, G 0 * ((Real.exp (-π * u ^ 2) : ℝ) : ℂ))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun u ↦ C * (Real.exp (-π * u ^ 2) + b * ‖u * Real.exp (-π * u ^ 2)‖)) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun A ↦ ((hGc.comp (continuous_id.div_const _)).mul
        (by fun_prop)).aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop 1] with A hA
      refine Eventually.of_forall fun u ↦ ?_
      have hsA : 1 ≤ √A := Real.one_le_sqrt.2 hA
      have he : 0 < Real.exp (-π * u ^ 2) := Real.exp_pos _
      have hu : |u / √A| ≤ |u| := by
        rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < √A)]
        exact div_le_self (abs_nonneg u) hsA
      simp only [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos he]
      calc ‖G (u / √A)‖ * Real.exp (-π * u ^ 2)
          ≤ C * (1 + b * |u|) * Real.exp (-π * u ^ 2) := by
            refine mul_le_mul_of_nonneg_right ((hC _).trans ?_) he.le
            gcongr
        _ = C * (Real.exp (-π * u ^ 2) + b * (|u| * Real.exp (-π * u ^ 2))) := by ring
    · exact ((integrable_exp_neg_mul_sq pi_pos).add
        ((integrable_mul_exp_neg_mul_sq pi_pos).norm.const_mul b)).const_mul C
    · refine Eventually.of_forall fun u ↦ ?_
      have h1 : Tendsto (fun A : ℝ ↦ u / √A) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
      exact ((hGc.tendsto 0).comp h1).mul tendsto_const_nhds
  have hval : ∫ u, G 0 * ((Real.exp (-π * u ^ 2) : ℝ) : ℂ) = digamma a := by
    rw [integral_const_mul, integral_complex_ofReal, integral_gaussian, div_self pi_ne_zero,
      Real.sqrt_one]
    simp [hGdef]
  rw [hval] at hlim
  exact hlim.congr' ((eventually_gt_atTop 0).mono fun A hA ↦ (hsub A hA).symm)

/-- Montgomery–Vaughan, Lemma 12.14 (sign `+`), with the limit written as
`ψ(a) J(0) + ∫ (J(0) - J(x)) M(x) dx`, `M = digammaPairingKernel a b`, and with the hypothesis
`J(x) = J(0) + O(|x|)` in the global form `‖J(x) - J(0)‖ ≤ L|x|`. -/
theorem tendsto_integral_digamma_line_mul_fourier_of_le (ha : 0 < a) (hb : 0 < b) {J : ℝ → ℂ}
    (hJi : Integrable J) (hJv : BoundedVariationOn J univ) {L : ℝ}
    (hJL : ∀ x, ‖J x - J 0‖ ≤ L * |x|) :
    Tendsto (fun T : ℝ ↦ ∫ t in -T..T, digamma (a + b * t * I) * 𝓕 J t) atTop
      (𝓝 (digamma a * J 0 + ∫ x, (J 0 - J x) * (digammaPairingKernel a b x : ℂ))) := by
  set M : ℝ → ℂ := fun x ↦ (digammaPairingKernel a b x : ℂ) with hMdef
  set G : ℝ → ℂ := fun t ↦ digamma (a + b * t * I) with hGdef
  set V := (eVariationOn J univ).toReal with hVdef
  have hJV : ∀ x, ‖J x - J 0‖ ≤ V := fun x ↦ by
    rw [← dist_eq_norm]; exact hJv.dist_le (mem_univ x) (mem_univ 0)
  have hMm : Measurable M := Complex.measurable_ofReal.comp (measurable_digammaPairingKernel a b)
  set β : ℝ → ℂ := fun A ↦ (∫ x, (gaussAux A x - 1) * M x) + ∫ t, G t * 𝓕 (gaussAux A) t
    with hβdef
  set Rm : ℂ := ∫ x, (J 0 - J x) * M x with hRmdef
  have hRint : Integrable fun x ↦ (J 0 - J x) * M x :=
    integrable_mul_digammaPairingKernel ha hb (aestronglyMeasurable_const.sub hJi.1)
      (fun x _ ↦ by rw [norm_sub_rev]; exact hJL x) (fun x _ ↦ by rw [norm_sub_rev]; exact hJV x)
  have hρint : Integrable fun x ↦ ((1 - Real.exp (-π * x ^ 2) : ℝ) : ℂ) * M x :=
    integrable_mul_digammaPairingKernel ha hb (by fun_prop : Continuous fun x : ℝ ↦
      ((1 - Real.exp (-π * x ^ 2) : ℝ) : ℂ)).aestronglyMeasurable
      (fun x _ ↦ by
        rw [norm_real, Real.norm_of_nonneg (one_sub_exp_neg_pi_mul_sq_nonneg x)]
        exact one_sub_exp_neg_pi_mul_sq_le x)
      (fun x _ ↦ by
        rw [norm_real, Real.norm_of_nonneg (one_sub_exp_neg_pi_mul_sq_nonneg x)]
        exact one_sub_exp_neg_pi_mul_sq_le_one x)
  have hgM : ∀ A : ℝ, 1 ≤ A → Integrable fun x ↦ (gaussAux A x - 1) * M x := fun A hA ↦
    integrable_mul_digammaPairingKernel ha hb
      ((continuous_gaussAux A).sub continuous_const).aestronglyMeasurable
      (fun x _ ↦ (norm_gaussAux_sub_one_le hA x).trans (one_sub_exp_neg_pi_mul_sq_le x))
      (fun x _ ↦ (norm_gaussAux_sub_one_le hA x).trans (one_sub_exp_neg_pi_mul_sq_le_one x))
  -- for each `A ≥ 1`, the limit exists and equals `Rm + J(0) β(A)`
  have key : ∀ A : ℝ, 1 ≤ A → Tendsto (fun T : ℝ ↦ ∫ t in -T..T, G t * 𝓕 J t) atTop
      (𝓝 (Rm + J 0 * β A)) := by
    intro A hA
    have hA0 : 0 < A := by linarith
    set K : ℝ → ℂ := fun x ↦ J x - J 0 * gaussAux A x with hKdef
    have hgi := integrable_gaussAux hA0
    have hKi : Integrable K := hJi.sub (hgi.const_mul (J 0))
    have hgv : eVariationOn (fun x ↦ J 0 * gaussAux A x) univ ≤ ‖J 0‖₊ * 2 := by
      have h1 : eVariationOn (fun x ↦ J 0 * gaussAux A x) univ ≤
          ‖J 0‖₊ * eVariationOn (gaussAux A) univ :=
        (lipschitzWith_smul (J 0)).lipschitzOnWith.comp_eVariationOn_le (mapsTo_univ _ _)
      exact h1.trans (by gcongr; exact eVariationOn_gaussAux_le hA0.le)
    have hKv : BoundedVariationOn K univ :=
      ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hJv, ENNReal.mul_ne_top ENNReal.coe_ne_top
        ENNReal.ofNat_ne_top⟩) ((eVariationOn_sub_le J _ univ).trans (add_le_add le_rfl hgv))
    have hKL : ∀ x, ‖K x‖ ≤ (L + ‖J 0‖ * (π + 1)) * |x| := fun x ↦ by
      have h2 := (norm_gaussAux_sub_one_le hA x).trans (one_sub_exp_neg_pi_mul_sq_le x)
      calc ‖K x‖ = ‖(J x - J 0) - J 0 * (gaussAux A x - 1)‖ := by simp only [hKdef]; ring_nf
        _ ≤ ‖J x - J 0‖ + ‖J 0‖ * ‖gaussAux A x - 1‖ := by
            rw [← norm_mul]; exact norm_sub_le _ _
        _ ≤ L * |x| + ‖J 0‖ * ((π + 1) * |x|) := by gcongr; exact hJL x
        _ = (L + ‖J 0‖ * (π + 1)) * |x| := by ring
    have h0 : Tendsto (fun T : ℝ ↦ ∫ t in -T..T, G t * 𝓕 K t) atTop (𝓝 (-∫ x, K x * M x)) :=
      tendsto_integral_digamma_line_mul_fourier_of_zero ha hb hKi hKv hKL
    have hsplit : ∀ T : ℝ, 0 ≤ T → ∫ t in -T..T, G t * 𝓕 J t =
        (∫ t in -T..T, G t * 𝓕 K t) + J 0 * ∫ t in -T..T, G t * 𝓕 (gaussAux A) t := by
      intro T hT
      simp only [hGdef]
      rw [integral_digamma_line_mul_fourier_eq ha hJi hT,
        integral_digamma_line_mul_fourier_eq ha hKi hT,
        integral_digamma_line_mul_fourier_eq ha hgi hT, ← integral_const_mul,
        ← integral_add (integrable_mul_digammaLineFourier ha hb hKi hT)
          ((integrable_mul_digammaLineFourier ha hb hgi hT).const_mul _)]
      congr 1
      ext x
      simp only [hKdef]
      ring
    have hgauss : Tendsto (fun T : ℝ ↦ ∫ t in -T..T, G t * 𝓕 (gaussAux A) t) atTop
        (𝓝 (∫ t, G t * 𝓕 (gaussAux A) t)) := by
      have hint : Integrable fun t ↦ G t * 𝓕 (gaussAux A) t := by
        have := (integrable_digamma_line_mul_gaussian ha hb (c := π * A) (by positivity)).const_mul
          (√A : ℂ)
        refine this.congr (Eventually.of_forall fun t ↦ ?_)
        simp only [hGdef, fourier_gaussAux hA0]
        push_cast
        ring_nf
      exact intervalIntegral_tendsto_integral hint tendsto_neg_atTop_atBot tendsto_id
    have hlim := h0.add (hgauss.const_mul (J 0))
    have hval : -(∫ x, K x * M x) + J 0 * ∫ t, G t * 𝓕 (gaussAux A) t = Rm + J 0 * β A := by
      have hsplitM : ∫ x, K x * M x = -(Rm + J 0 * ∫ x, (gaussAux A x - 1) * M x) := by
        rw [hRmdef, ← integral_const_mul, ← integral_add hRint ((hgM A hA).const_mul _),
          ← integral_neg]
        congr 1
        ext x
        simp only [hKdef]
        ring
      rw [hsplitM, hβdef]
      ring
    rw [hval] at hlim
    exact hlim.congr' ((eventually_ge_atTop 0).mono fun T hT ↦ (hsplit T hT).symm)
  -- `β(A) → ψ(a)`
  have hβ : Tendsto β atTop (𝓝 (digamma a)) := by
    have h1 : Tendsto (fun A ↦ ∫ x, (gaussAux A x - 1) * M x) atTop (𝓝 0) := by
      have := tendsto_integral_filter_of_dominated_convergence (f := fun _ ↦ (0 : ℂ))
        (F := fun A x ↦ (gaussAux A x - 1) * M x) (l := atTop)
        (fun x ↦ ‖((1 - Real.exp (-π * x ^ 2) : ℝ) : ℂ) * M x‖)
        (Eventually.of_forall fun A ↦ (((continuous_gaussAux A).sub
          continuous_const).aestronglyMeasurable.mul hMm.aestronglyMeasurable))
        (by
          filter_upwards [eventually_ge_atTop 1] with A hA
          refine Eventually.of_forall fun x ↦ ?_
          rw [norm_mul, norm_mul]
          refine mul_le_mul_of_nonneg_right
            ((norm_gaussAux_sub_one_le hA x).trans (le_of_eq ?_)) (norm_nonneg _)
          rw [norm_real, Real.norm_of_nonneg (one_sub_exp_neg_pi_mul_sq_nonneg x)])
        hρint.norm
        (Eventually.of_forall fun x ↦ by
          have hA_lim : Tendsto (fun A : ℝ ↦ -(π * A⁻¹) * x ^ 2) atTop (𝓝 0) := by
            have := (tendsto_inv_atTop_zero.const_mul π).neg.mul_const (x ^ 2)
            rwa [mul_zero, neg_zero, zero_mul] at this
          have hg_lim : Tendsto (fun A : ℝ ↦ gaussAux A x) atTop (𝓝 1) := by
            have := (continuous_ofReal.tendsto _).comp ((Real.continuous_exp.tendsto 0).comp hA_lim)
            rw [Real.exp_zero, ofReal_one] at this
            exact this
          have := (hg_lim.sub_const 1).mul_const (M x)
          rwa [sub_self, zero_mul] at this)
      simpa using this
    have h2 : Tendsto (fun A ↦ ∫ t, G t * 𝓕 (gaussAux A) t) atTop (𝓝 (digamma a)) :=
      tendsto_integral_digamma_line_mul_fourier_gaussAux ha hb
    have := h1.add h2
    rwa [zero_add] at this
  have hconst : ∀ A : ℝ, 1 ≤ A → J 0 * β A = J 0 * β 1 := fun A hA ↦ by
    have := tendsto_nhds_unique (key A hA) (key 1 le_rfl)
    linear_combination this
  have hβ1 : J 0 * β 1 = J 0 * digamma a := by
    refine tendsto_nhds_unique (f := fun A ↦ J 0 * β A) (l := atTop) ?_ (hβ.const_mul (J 0))
    exact tendsto_const_nhds.congr' ((eventually_ge_atTop 1).mono fun A hA ↦ (hconst A hA).symm)
  have h := key 1 le_rfl
  rw [hβ1] at h
  have h' : Tendsto (fun T : ℝ ↦ ∫ t in -T..T, digamma (a + b * t * I) * 𝓕 J t) atTop
      (𝓝 (Rm + J 0 * digamma a)) := h
  rw [show digamma a * J 0 + ∫ x, (J 0 - J x) * (digammaPairingKernel a b x : ℂ) =
    Rm + J 0 * digamma a by rw [hRmdef]; ring]
  exact h'

/-- Rewriting `∫ F(x) M(x) dx` as `(2π/b) ∫_0^∞ e^{-2πay/b} / (1 - e^{-2πy/b}) F(-y) dy`. -/
theorem integral_mul_digammaPairingKernel_eq (F : ℝ → ℂ) :
    ∫ x, F x * (digammaPairingKernel a b x : ℂ) = (2 * π / b : ℂ) * ∫ y in Ioi 0,
      ((Real.exp (-(2 * π * a * y / b)) / (1 - Real.exp (-(2 * π * y / b))) : ℝ) : ℂ) *
        F (-y) := by
  rw [← integral_neg_eq_self, ← integral_indicator measurableSet_Ioi, ← integral_const_mul]
  congr 1
  ext y
  simp only [ofReal_digammaPairingKernel, indicator_apply, mem_Ioi]
  by_cases hy : 0 < y
  · rw [if_pos (by linarith : -y < 0), if_pos hy]
    push_cast
    ring_nf
  · rw [if_neg (by linarith), if_neg hy]
    simp

/-- If `J` has bounded variation on `ℝ` and `J(x) - J(0) = O(x)` as `x → 0`, then
`‖J(x) - J(0)‖ ≤ L|x|` for all `x`, for some `L`. -/
theorem exists_norm_sub_le_mul_abs {J : ℝ → ℂ} (hJv : BoundedVariationOn J univ)
    (hJ0 : (fun x ↦ J x - J 0) =O[𝓝 0] fun x ↦ x) : ∃ L, ∀ x, ‖J x - J 0‖ ≤ L * |x| := by
  obtain ⟨c, hc⟩ := hJ0.bound
  obtain ⟨ε, hε, hεc⟩ := Metric.eventually_nhds_iff.1 hc
  set V := (eVariationOn J univ).toReal
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  refine ⟨|c| + V / ε, fun x ↦ ?_⟩
  have hV : ‖J x - J 0‖ ≤ V := by
    rw [← dist_eq_norm]; exact hJv.dist_le (mem_univ x) (mem_univ 0)
  have hVε : 0 ≤ V / ε := div_nonneg hV0 hε.le
  rcases lt_or_ge |x| ε with h | h
  · have h1 := hεc (show dist x 0 < ε by simpa using h)
    rw [Real.norm_eq_abs] at h1
    calc ‖J x - J 0‖ ≤ c * |x| := h1
      _ ≤ |c| * |x| := mul_le_mul_of_nonneg_right (le_abs_self c) (abs_nonneg x)
      _ ≤ (|c| + V / ε) * |x| := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg x)
  · calc ‖J x - J 0‖ ≤ V := hV
      _ = V / ε * ε := by field_simp
      _ ≤ V / ε * |x| := mul_le_mul_of_nonneg_left h hVε
      _ ≤ (|c| + V / ε) * |x| := mul_le_mul_of_nonneg_right (by linarith [abs_nonneg c])
          (abs_nonneg x)

/-- **Montgomery–Vaughan, Lemma 12.14**, sign `+`: if `J ∈ L¹(ℝ)` has bounded variation on `ℝ`
and `J(x) = J(0) + O(|x|)` as `x → 0`, then for `a, b > 0`,
`lim_{T → ∞} ∫_{-T}^{T} ψ(a + ibt) Ĵ(t) dt
  = ψ(a) J(0) + (2π/b) ∫_0^∞ e^{-2πax/b} / (1 - e^{-2πx/b}) · (J(0) - J(-x)) dx`. -/
theorem tendsto_integral_digamma_line_mul_fourier (ha : 0 < a) (hb : 0 < b) {J : ℝ → ℂ}
    (hJi : Integrable J) (hJv : BoundedVariationOn J univ)
    (hJ0 : (fun x ↦ J x - J 0) =O[𝓝 0] fun x ↦ x) :
    Tendsto (fun T : ℝ ↦ ∫ t in -T..T, digamma (a + b * t * I) * 𝓕 J t) atTop
      (𝓝 (digamma a * J 0 + (2 * π / b : ℂ) * ∫ x in Ioi 0,
        ((Real.exp (-(2 * π * a * x / b)) / (1 - Real.exp (-(2 * π * x / b))) : ℝ) : ℂ) *
          (J 0 - J (-x)))) := by
  obtain ⟨L, hL⟩ := exists_norm_sub_le_mul_abs hJv hJ0
  have h := tendsto_integral_digamma_line_mul_fourier_of_le ha hb hJi hJv hL
  rwa [integral_mul_digammaPairingKernel_eq] at h

theorem fourier_comp_neg (J : ℝ → ℂ) (t : ℝ) : 𝓕 (fun x ↦ J (-x)) t = 𝓕 J (-t) := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul,
    ← integral_neg_eq_self (fun v ↦ cexp (↑(-2 * π * v * -t) * I) • J v)]
  congr 1
  ext v
  rw [show -2 * π * -v * -t = -2 * π * v * t by ring]

/-- **Montgomery–Vaughan, Lemma 12.14**, sign `-`: under the hypotheses of
`Complex.tendsto_integral_digamma_line_mul_fourier`,
`lim_{T → ∞} ∫_{-T}^{T} ψ(a - ibt) Ĵ(t) dt
  = ψ(a) J(0) + (2π/b) ∫_0^∞ e^{-2πax/b} / (1 - e^{-2πx/b}) · (J(0) - J(x)) dx`. -/
theorem tendsto_integral_digamma_line_neg_mul_fourier (ha : 0 < a) (hb : 0 < b) {J : ℝ → ℂ}
    (hJi : Integrable J) (hJv : BoundedVariationOn J univ)
    (hJ0 : (fun x ↦ J x - J 0) =O[𝓝 0] fun x ↦ x) :
    Tendsto (fun T : ℝ ↦ ∫ t in -T..T, digamma (a - b * t * I) * 𝓕 J t) atTop
      (𝓝 (digamma a * J 0 + (2 * π / b : ℂ) * ∫ x in Ioi 0,
        ((Real.exp (-(2 * π * a * x / b)) / (1 - Real.exp (-(2 * π * x / b))) : ℝ) : ℂ) *
          (J 0 - J x))) := by
  have hJ'i : Integrable fun x ↦ J (-x) := hJi.comp_neg
  have hJ'v : BoundedVariationOn (fun x ↦ J (-x)) univ := by
    have h := eVariationOn.comp_eq_of_antitoneOn J (fun x : ℝ ↦ -x) (t := univ)
      (fun x _ y _ hxy ↦ neg_le_neg hxy)
    have himg : (fun x : ℝ ↦ -x) '' univ = univ := Set.image_univ_of_surjective neg_surjective
    rw [himg] at h
    change eVariationOn (J ∘ fun x ↦ -x) univ ≠ ⊤
    rw [h]
    exact hJv
  have hJ'0 : (fun x ↦ J (-x) - J (-0)) =O[𝓝 0] fun x ↦ x := by
    have htend : Tendsto (fun x : ℝ ↦ -x) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_neg.tendsto (0 : ℝ))
    rw [neg_zero]
    exact Asymptotics.isBigO_neg_right.1 (hJ0.comp_tendsto htend)
  have h := tendsto_integral_digamma_line_mul_fourier ha hb hJ'i hJ'v hJ'0
  simp only [neg_zero, neg_neg] at h
  refine h.congr' (Eventually.of_forall fun T ↦ ?_)
  simp only [fourier_comp_neg]
  have h2 := intervalIntegral.integral_comp_neg (a := -T) (b := T)
    (f := fun s ↦ digamma (a - b * s * I) * 𝓕 J s)
  rw [neg_neg] at h2
  rw [← h2]
  congr 1
  ext t
  congr 2
  push_cast
  ring

/-! ### Restatements in the form of the draft blueprint for Theorem 12.13 -/

/-- `ψ(a + ibt) = ψ(a) + O(|t|)` for all real `t`. -/
theorem exists_norm_digamma_sub_le (ha : 0 < a) (b : ℝ) :
    ∃ C, ∀ t : ℝ, ‖digamma (a + b * t * I) - digamma a‖ ≤ C * |t| := by
  set K := 2 * (1 / min a 1 ^ 2 + 1 / min a 1) with hKdef
  have hK : 0 ≤ K := by positivity
  refine ⟨K * |b|, fun t ↦ ?_⟩
  have e : (a : ℂ) + b * t * I = a + ((b * t : ℝ) : ℂ) * I := by push_cast; ring
  rw [e]
  refine (norm_digamma_sub_le ha (b * t)).trans ?_
  have hlog : Real.log (1 + |b * t|) ≤ |b * t| := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + |b * t| by positivity)
    linarith
  calc K * Real.log (1 + |b * t|) ≤ K * |b * t| := mul_le_mul_of_nonneg_left hlog hK
    _ = K * |b| * |t| := by rw [abs_mul]; ring

/-- Montgomery–Vaughan, Theorem C.5, as `Complex.norm_integral_digamma_line_mul_cexp_sub_le`
with the denominators written `2πix` and the main term `(2π/b) e^{2πax/b} / (1 - e^{2πx/b})`
grouped differently. -/
theorem exists_integral_digamma_mul_exp (ha : 0 < a) (hb : 0 < b) :
    ∃ C, ∀ x T : ℝ, x ≠ 0 → 1 ≤ T →
      ‖(∫ t in (-T)..T, digamma (a + b * t * I) * Complex.exp (-(2 * π * x * t) * I)) -
          (-(digamma (a + b * T * I) * Complex.exp (-(2 * π * x * T) * I)) / (2 * π * I * x) +
            digamma (a - b * T * I) * Complex.exp ((2 * π * x * T) * I) / (2 * π * I * x) -
            if x < 0 then
              ((2 * π / b * Real.exp (2 * π * a * x / b) / (1 - Real.exp (2 * π * x / b)) : ℝ) : ℂ)
            else 0)‖ ≤ C / (x ^ 2 * T) := by
  obtain ⟨C, hC⟩ := norm_integral_digamma_line_mul_cexp_sub_le ha hb
  refine ⟨C, fun x T hx hT ↦ ?_⟩
  have e1 : (2 * π * I * x : ℂ) = 2 * π * x * I := by ring
  have e2 : 2 * π / b * Real.exp (2 * π * a * x / b) / (1 - Real.exp (2 * π * x / b)) =
      2 * π / b * (Real.exp (2 * π * a * x / b) / (1 - Real.exp (2 * π * x / b))) := by ring
  rw [e1, e2]
  exact hC x hx T hT

/-- Montgomery–Vaughan, Lemma 12.14, sign `+`; the same statement as
`Complex.tendsto_integral_digamma_line_mul_fourier`, with the factor `2π/b` cast from `ℝ`. -/
theorem tendsto_integral_digamma_mul_fourier (ha : 0 < a) (hb : 0 < b) {J : ℝ → ℂ}
    (hJ1 : Integrable J) (hJ2 : BoundedVariationOn J Set.univ)
    (hJ0 : (fun x ↦ J x - J 0) =O[𝓝 0] (fun x ↦ x)) :
    Tendsto (fun T : ℝ ↦ ∫ t in (-T)..T, digamma (a + b * t * I) * 𝓕 J t) atTop
      (𝓝 (digamma a * J 0 + ((2 * π / b : ℝ) : ℂ) *
        ∫ x in Set.Ioi (0 : ℝ),
          ((Real.exp (-(2 * π * a * x / b)) / (1 - Real.exp (-(2 * π * x / b))) : ℝ) : ℂ) *
            (J 0 - J (-x)))) := by
  rw [show ((2 * π / b : ℝ) : ℂ) = (2 * π / b : ℂ) by push_cast; ring]
  exact tendsto_integral_digamma_line_mul_fourier ha hb hJ1 hJ2 hJ0

/-- Montgomery–Vaughan, Lemma 12.14, sign `-`; the same statement as
`Complex.tendsto_integral_digamma_line_neg_mul_fourier`, with the factor `2π/b` cast from `ℝ`. -/
theorem tendsto_integral_digamma_conj_mul_fourier (ha : 0 < a) (hb : 0 < b) {J : ℝ → ℂ}
    (hJ1 : Integrable J) (hJ2 : BoundedVariationOn J Set.univ)
    (hJ0 : (fun x ↦ J x - J 0) =O[𝓝 0] (fun x ↦ x)) :
    Tendsto (fun T : ℝ ↦ ∫ t in (-T)..T, digamma (a - b * t * I) * 𝓕 J t) atTop
      (𝓝 (digamma a * J 0 + ((2 * π / b : ℝ) : ℂ) *
        ∫ x in Set.Ioi (0 : ℝ),
          ((Real.exp (-(2 * π * a * x / b)) / (1 - Real.exp (-(2 * π * x / b))) : ℝ) : ℂ) *
            (J 0 - J x))) := by
  rw [show ((2 * π / b : ℝ) : ℂ) = (2 * π / b : ℂ) by push_cast; ring]
  exact tendsto_integral_digamma_line_neg_mul_fourier ha hb hJ1 hJ2 hJ0

end Complex
