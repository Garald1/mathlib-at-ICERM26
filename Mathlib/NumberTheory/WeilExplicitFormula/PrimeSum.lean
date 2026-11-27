/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Harald Helfgott
-/
module

public import Mathlib.NumberTheory.WeilExplicitFormula.TranslateSum
public import Mathlib.NumberTheory.LSeries.Dirichlet

/-! # The Dirichlet series part of Weil's explicit formula

Part F of the blueprint for Montgomery–Vaughan, *Multiplicative Number Theory I*, Theorem 12.13
with `q = 1`. For `0 < δ₁ < δ₀`, Montgomery–Vaughan put
`H(x) = -∑ Λ(n) n^{-1/2} (F(x - log n / 2π) + F(-x + log n / 2π)) e^{-(1/2+δ₁)2πx}`
and show, from (12.25)–(12.26), that `H ∈ L¹ ∩ BV(ℝ)`, that `H` is normalized, and that
`Ĥ(t) = (Φ(s) + Φ(1-s)) ζ'/ζ(s)` at `s = 1 + δ₁ + it`; so that, by the Fourier integral theorem,
`(1/2πi) ∫_{1+δ₁-iT}^{1+δ₁+iT} (Φ(s) + Φ(1-s)) ζ'/ζ(s) ds → H(0)/2π`.

Here `H` is written as a sum of translates `∑ aₙ K(x - Lₙ)` (`H_eq_translateSum`) with
`aₙ = Λ(n) n^{-1-δ₁}`, `Lₙ = log n / 2π` and `K(y) = -(F(y) + F(-y)) e^{-(1/2+δ₁)2πy}`, and the
results of `TranslateSum.lean` do the rest.

## Main results

* `IsTestFunction.integrable_H`, `IsTestFunction.boundedVariationOn_H`, `IsTestFunction.H_zero`,
  `IsTestFunction.fourier_H`: the statements F2 of the draft
  `blueprint/drafts/WeilExplicitFormula.lean`.
* `IsTestFunction.tendsto_integral_Phi_mul_logDeriv`: F3, in the form
  `∫_{-T}^{T} (Φ(s) + Φ(1-s)) ζ'/ζ(s) dt → -∑ Λ(n) n^{-1/2} (F(-log n/2π) + F(log n/2π))`,
  `s = 1 + δ₁ + it`.

## AI usage

This file was written by Claude (Anthropic) in November 2026. It compiles, but has not been
reviewed by a human.
-/

@[expose] public section

open Real Complex Filter Topology MeasureTheory Set Function Asymptotics
open scoped FourierTransform

noncomputable section

namespace WeilExplicitFormula

variable {F : ℝ → ℂ} {δ₀ : ℝ}

/-! ### `x ↦ F(-x)`, and one-sided limits -/

theorem IsTestFunction.comp_neg (hF : IsTestFunction F δ₀) :
    IsTestFunction (fun x ↦ F (-x)) δ₀ where
  pos := hF.pos
  integrable := by
    have := hF.integrable.comp_neg
    simpa only [abs_neg] using this
  boundedVariation := by
    have h := eVariationOn_comp_neg (fun x ↦ (Real.exp ((1 + 2 * δ₀) * π * |x|) : ℂ) * F x)
    simp only [abs_neg] at h
    unfold BoundedVariationOn
    rw [h]
    exact hF.boundedVariation
  normalized := by
    intro x
    have hbv := hF.boundedVariationOn_self
    have hl : Tendsto (fun y ↦ F (-y)) (𝓝[<] x) (𝓝 (rightLim F (-x))) :=
      (hbv.tendsto_rightLim (-x)).comp (tendsto_neg_nhdsLT' x)
    have hr : Tendsto (fun y ↦ F (-y)) (𝓝[>] x) (𝓝 (leftLim F (-x))) :=
      (hbv.tendsto_leftLim (-x)).comp (tendsto_neg_nhdsGT' x)
    rw [leftLim_eq_of_tendsto (NeBot.ne inferInstance) hl,
      rightLim_eq_of_tendsto (NeBot.ne inferInstance) hr, hF.normalized (-x)]
    ring
  isBigO_zero := by
    simp only [neg_neg, neg_zero]
    exact hF.isBigO_zero.congr_left fun x ↦ by ring

theorem continuous_ofReal_exp_mul (c : ℝ) : Continuous fun x : ℝ ↦ (Real.exp (c * x) : ℂ) :=
  Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id))

theorem IsTestFunction.tendsto_mul_exp_nhdsGT (hF : IsTestFunction F δ₀) (c y : ℝ) :
    Tendsto (fun x ↦ F x * (Real.exp (c * x) : ℂ)) (𝓝[>] y)
      (𝓝 (rightLim F y * (Real.exp (c * y) : ℂ))) :=
  (hF.boundedVariationOn_self.tendsto_rightLim y).mul
    (((continuous_ofReal_exp_mul c).tendsto y).mono_left nhdsWithin_le_nhds)

theorem IsTestFunction.tendsto_mul_exp_nhdsLT (hF : IsTestFunction F δ₀) (c y : ℝ) :
    Tendsto (fun x ↦ F x * (Real.exp (c * x) : ℂ)) (𝓝[<] y)
      (𝓝 (leftLim F y * (Real.exp (c * y) : ℂ))) :=
  (hF.boundedVariationOn_self.tendsto_leftLim y).mul
    (((continuous_ofReal_exp_mul c).tendsto y).mono_left nhdsWithin_le_nhds)

theorem integrable_fourierIntegrand {g : ℝ → ℂ} (hg : Integrable g) (t : ℝ) :
    Integrable fun x ↦ cexp (↑(-2 * π * x * t) * I) • g x :=
  hg.mono ((Continuous.aestronglyMeasurable (by fun_prop)).smul hg.aestronglyMeasurable)
    (Eventually.of_forall fun x ↦ by rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul])

/-! ### The kernel `K(y) = -(F(y) + F(-y)) e^{-(1/2+δ₁)2πy}` -/

/-- The function whose translates make up `H`. -/
def hKernel (F : ℝ → ℂ) (δ₁ y : ℝ) : ℂ :=
  -(F y * (Real.exp (-((1 / 2 + δ₁) * 2 * π) * y) : ℂ) +
    F (-y) * (Real.exp (-((1 / 2 + δ₁) * 2 * π) * y) : ℂ))

theorem abs_coeff_le {δ₁ : ℝ} (h0 : 0 < δ₁) (h1 : δ₁ < δ₀) :
    |-((1 / 2 + δ₁) * 2 * π)| ≤ (1 + 2 * δ₀) * π := by
  rw [abs_neg, abs_of_pos (by positivity)]
  nlinarith [pi_pos]

theorem IsTestFunction.integrable_hKernel (hF : IsTestFunction F δ₀) {δ₁ : ℝ} (h0 : 0 < δ₁)
    (h1 : δ₁ < δ₀) : Integrable (hKernel F δ₁) :=
  ((hF.integrable_mul_exp (abs_coeff_le h0 h1)).add
    (hF.comp_neg.integrable_mul_exp (abs_coeff_le h0 h1))).neg

theorem IsTestFunction.boundedVariationOn_hKernel (hF : IsTestFunction F δ₀) {δ₁ : ℝ}
    (h0 : 0 < δ₁) (h1 : δ₁ < δ₀) : BoundedVariationOn (hKernel F δ₁) univ := by
  have h₁ := hF.boundedVariationOn_mul_exp (abs_coeff_le h0 h1)
  have h₂ := hF.comp_neg.boundedVariationOn_mul_exp (abs_coeff_le h0 h1)
  unfold BoundedVariationOn hKernel
  rw [eVariationOn_neg]
  exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨h₁, h₂⟩) (eVariationOn_add_le _ _ _)

theorem IsTestFunction.hKernel_eq_rightLim_add_leftLim (hF : IsTestFunction F δ₀) {δ₁ : ℝ}
    (y : ℝ) : hKernel F δ₁ y = (rightLim (hKernel F δ₁) y + leftLim (hKernel F δ₁) y) / 2 := by
  set c := -((1 / 2 + δ₁) * 2 * π) with hc
  have hr := ((hF.tendsto_mul_exp_nhdsGT c y).add (hF.comp_neg.tendsto_mul_exp_nhdsGT c y)).neg
  have hl := ((hF.tendsto_mul_exp_nhdsLT c y).add (hF.comp_neg.tendsto_mul_exp_nhdsLT c y)).neg
  refine eq_rightLim_add_leftLim_div_two hr hl ?_
  simp only [hKernel]
  rw [← hc, hF.normalized y, hF.comp_neg.normalized y]
  ring

theorem IsTestFunction.fourier_hKernel (hF : IsTestFunction F δ₀) {δ₁ : ℝ} (h0 : 0 < δ₁)
    (h1 : δ₁ < δ₀) (t : ℝ) :
    𝓕 (hKernel F δ₁) t = -(Phi F (1 + δ₁ + t * I) + Phi F (1 - (1 + δ₁ + t * I))) := by
  set c := -((1 / 2 + δ₁) * 2 * π) with hcdef
  have hcx : ∀ x : ℝ, (1 - 2 * (1 + δ₁)) * π * x = c * x := fun x ↦ by rw [hcdef]; ring
  have hcast : ((1 + δ₁ : ℝ) : ℂ) = 1 + δ₁ := by push_cast; ring
  have e₁ : Phi F (1 + δ₁ + t * I) = 𝓕 (fun x ↦ F x * (Real.exp (c * x) : ℂ)) t := by
    have h := Phi_eq_fourier F (1 + δ₁) t
    rw [hcast] at h
    rw [h]
    simp_rw [hcx]
  have e₂ : Phi F (1 - (1 + δ₁ + t * I)) = 𝓕 (fun x ↦ F (-x) * (Real.exp (c * x) : ℂ)) t := by
    have h := Phi_eq_fourier (fun x ↦ F (-x)) (1 + δ₁) t
    rw [hcast] at h
    rw [Phi_one_sub, h]
    simp_rw [hcx]
  have hi₁ := integrable_fourierIntegrand (hF.integrable_mul_exp (abs_coeff_le h0 h1)) t
  have hi₂ := integrable_fourierIntegrand (hF.comp_neg.integrable_mul_exp (abs_coeff_le h0 h1)) t
  rw [e₁, e₂, Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul, ← integral_add hi₁ hi₂, ← integral_neg]
  congr 1
  ext x
  simp only [hKernel, smul_eq_mul]
  ring

/-! ### The weights `Λ(n) n^{-1-δ₁}` and the shifts `log n / 2π` -/

/-- The shifts `log n / 2π`. -/
def primeShift (n : ℕ) : ℝ := Real.log n / (2 * π)

/-- The weights `Λ(n) n^{-1/2} e^{-(1/2+δ₁) log n} = Λ(n) n^{-1-δ₁}`. -/
def primeWeight (δ₁ : ℝ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n / Real.sqrt n *
    Real.exp (-((1 / 2 + δ₁) * 2 * π) * primeShift n)

theorem primeWeight_nonneg (δ₁ : ℝ) (n : ℕ) : 0 ≤ primeWeight δ₁ n :=
  mul_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
    (Real.exp_pos _).le

theorem primeWeight_mul_exp_eq_term (δ₁ t : ℝ) (n : ℕ) :
    (primeWeight δ₁ n : ℂ) * cexp (↑(-2 * π * primeShift n * t) * I) =
      LSeries.term (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) (1 + δ₁ + t * I) n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [primeWeight]
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hnr : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hreal : primeWeight δ₁ n =
      ArithmeticFunction.vonMangoldt n * Real.exp (-((1 + δ₁) * Real.log n)) := by
    simp only [primeWeight, primeShift]
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hnr, div_eq_mul_inv, ← Real.exp_neg, mul_assoc,
      ← Real.exp_add]
    congr 2
    field_simp
    ring
  have hshift : -2 * π * primeShift n * t = -(t * Real.log n) := by
    simp only [primeShift]
    field_simp
  rw [hreal, hshift, LSeries.term_of_ne_zero hn.ne', Complex.cpow_def_of_ne_zero hn0,
    div_eq_mul_inv, ← Complex.exp_neg, ← Complex.ofReal_natCast n, ← Complex.ofReal_log hnr.le]
  push_cast
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  ring

theorem summable_primeWeight {δ₁ : ℝ} (h0 : 0 < δ₁) : Summable (primeWeight δ₁) := by
  have h := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := 1 + δ₁ + ((0 : ℝ) : ℂ) * I)
    (by simp; linarith)
  have h2 : Summable fun n ↦ (primeWeight δ₁ n : ℂ) := by
    refine h.congr fun n ↦ ?_
    rw [← primeWeight_mul_exp_eq_term δ₁ 0 n]
    simp
  exact Complex.summable_ofReal.1 h2

/-! ### The function `H` -/

/-- The function `H` of the proof of Montgomery–Vaughan Theorem 12.13, for `q = 1`. -/
def H (F : ℝ → ℂ) (δ₁ x : ℝ) : ℂ :=
  -∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
    (F (x - Real.log n / (2 * π)) + F (-x + Real.log n / (2 * π))) *
      (Real.exp (-((1 / 2 + δ₁) * 2 * π * x)) : ℂ)

theorem H_eq_translateSum (F : ℝ → ℂ) (δ₁ : ℝ) :
    H F δ₁ = translateSum (primeWeight δ₁) primeShift (hKernel F δ₁) := by
  funext x
  simp only [H, translateSum, primeWeight, primeShift, hKernel]
  rw [← tsum_neg]
  congr 1
  ext n
  have he : Real.exp (-((1 / 2 + δ₁) * 2 * π * x)) =
      Real.exp (-((1 / 2 + δ₁) * 2 * π) * (Real.log n / (2 * π))) *
        Real.exp (-((1 / 2 + δ₁) * 2 * π) * (x - Real.log n / (2 * π))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he, show -(x - Real.log n / (2 * π)) = -x + Real.log n / (2 * π) by ring]
  push_cast
  ring

theorem H_zero_eq (F : ℝ → ℂ) (δ₁ : ℝ) :
    H F δ₁ 0 = -∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
      (F (-(Real.log n / (2 * π))) + F (Real.log n / (2 * π))) := by
  simp [H]

/-- F2 -/
theorem IsTestFunction.integrable_H (hF : IsTestFunction F δ₀) {δ₁ : ℝ} (h0 : 0 < δ₁)
    (h1 : δ₁ < δ₀) : Integrable (H F δ₁) := by
  rw [H_eq_translateSum]
  exact integrable_translateSum (primeWeight_nonneg δ₁) (summable_primeWeight h0)
    (hF.integrable_hKernel h0 h1) (hF.boundedVariationOn_hKernel h0 h1)

/-- F2 -/
theorem IsTestFunction.boundedVariationOn_H (hF : IsTestFunction F δ₀) {δ₁ : ℝ} (h0 : 0 < δ₁)
    (h1 : δ₁ < δ₀) : BoundedVariationOn (H F δ₁) Set.univ := by
  rw [H_eq_translateSum]
  exact boundedVariationOn_translateSum (primeWeight_nonneg δ₁) (summable_primeWeight h0)
    (hF.boundedVariationOn_hKernel h0 h1)

/-- `H` is normalized at every point. -/
theorem IsTestFunction.H_eq_rightLim_add_leftLim (hF : IsTestFunction F δ₀) {δ₁ : ℝ}
    (h0 : 0 < δ₁) (h1 : δ₁ < δ₀) (x : ℝ) :
    H F δ₁ x = (Function.rightLim (H F δ₁) x + Function.leftLim (H F δ₁) x) / 2 := by
  rw [H_eq_translateSum]
  exact translateSum_eq_rightLim_add_leftLim (primeWeight_nonneg δ₁) (summable_primeWeight h0)
    (hF.boundedVariationOn_hKernel h0 h1) hF.hKernel_eq_rightLim_add_leftLim x

/-- F2: `H` is normalized at `0`. -/
theorem IsTestFunction.H_zero (hF : IsTestFunction F δ₀) {δ₁ : ℝ} (h0 : 0 < δ₁) (h1 : δ₁ < δ₀) :
    H F δ₁ 0 = (Function.rightLim (H F δ₁) 0 + Function.leftLim (H F δ₁) 0) / 2 :=
  hF.H_eq_rightLim_add_leftLim h0 h1 0

/-- F1–F2: Montgomery–Vaughan (12.25)–(12.26) on the line `σ = 1 + δ₁`. -/
theorem IsTestFunction.fourier_H (hF : IsTestFunction F δ₀) {δ₁ : ℝ} (h0 : 0 < δ₁) (h1 : δ₁ < δ₀)
    (t : ℝ) :
    𝓕 (H F δ₁) t = (Phi F (1 + δ₁ + t * I) + Phi F (1 - (1 + δ₁ + t * I))) *
      logDeriv riemannZeta (1 + δ₁ + t * I) := by
  rw [H_eq_translateSum, fourier_translateSum (primeWeight_nonneg δ₁) (summable_primeWeight h0)
    (hF.integrable_hKernel h0 h1), hF.fourier_hKernel h0 h1]
  have hL : ∑' n, (primeWeight δ₁ n : ℂ) * cexp (↑(-2 * π * primeShift n * t) * I) =
      LSeries (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) (1 + δ₁ + t * I) :=
    tsum_congr (primeWeight_mul_exp_eq_term δ₁ t)
  have hre : 1 < (1 + δ₁ + t * I : ℂ).re := by simp; linarith
  rw [hL, ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hre, logDeriv_apply]
  ring

/-- F3: by the Fourier integral theorem, `∫_{-T}^{T} Ĥ → H(0)`. -/
theorem IsTestFunction.tendsto_integral_fourier_H (hF : IsTestFunction F δ₀) {δ₁ : ℝ}
    (h0 : 0 < δ₁) (h1 : δ₁ < δ₀) :
    Tendsto (fun T : ℝ ↦ ∫ t in (-T)..T, 𝓕 (H F δ₁) t) atTop (𝓝 (H F δ₁ 0)) := by
  have h := FourierIntegral.tendsto_partialInv_of_normalized (hF.integrable_H h0 h1)
    (hF.boundedVariationOn_H h0 h1) (hF.H_zero h0 h1)
  simpa [FourierIntegral.partialInv] using h

/-- F3, in the form used in the proof of Theorem 12.13: with `s = 1 + δ₁ + it`,
`∫_{-T}^{T} (Φ(s) + Φ(1-s)) ζ'/ζ(s) dt → -∑ Λ(n) n^{-1/2} (F(-log n/2π) + F(log n/2π))`. -/
theorem IsTestFunction.tendsto_integral_Phi_mul_logDeriv (hF : IsTestFunction F δ₀) {δ₁ : ℝ}
    (h0 : 0 < δ₁) (h1 : δ₁ < δ₀) :
    Tendsto (fun T : ℝ ↦ ∫ t in (-T)..T,
        (Phi F (1 + δ₁ + t * I) + Phi F (1 - (1 + δ₁ + t * I))) *
          logDeriv riemannZeta (1 + δ₁ + t * I)) atTop
      (𝓝 (-∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
        (F (-(Real.log n / (2 * π))) + F (Real.log n / (2 * π))))) := by
  have h := hF.tendsto_integral_fourier_H h0 h1
  rw [H_zero_eq] at h
  simp_rw [hF.fourier_H h0 h1] at h
  exact h

end WeilExplicitFormula
