/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Harald Helfgott
-/
module

public import Mathlib.NumberTheory.WeilExplicitFormula.PrimeSum
public import Mathlib.Analysis.BoxIntegral.Stieltjes.DigammaPairing

/-! # The terms of Weil's explicit formula on the critical line

Part G5 of the blueprint for Montgomery–Vaughan, *Multiplicative Number Theory I*,
Theorem 12.13 with `q = 1`. By (12.24), `ξ'/ξ(s) = G(s) + ζ'/ζ(s)` with
`G(s) = 1/s + 1/(s-1) + ψ(s/2)/2 - (log π)/2` (`gammaFactor`). On the line `σ = 1/2`,
`Φ(1/2 + it) + Φ(1/2 - it) = F̂(t) + F̂(-t) = Ĵ(t)` with `J(x) = F(x) + F(-x)`, and
* `1/s + 1/(s-1)` is odd in `t` while `Ĵ` is even, so it contributes nothing;
* `∫_{-T}^{T} Ĵ → J(0) = 2F(0)` by the Fourier integral theorem;
* `∫_{-T}^{T} ψ(1/4 + it/2) Ĵ(t) dt →
    2ψ(1/4) F(0) + 4π ∫_0^∞ e^{-πx}/(1 - e^{-4πx}) (2F(0) - F(x) - F(-x)) dx`
  by Montgomery–Vaughan Lemma 12.14 (`Complex.tendsto_integral_digamma_line_mul_fourier`, with
  `a = 1/4`, `b = 1/2`).

## Main result

* `IsTestFunction.tendsto_integral_gammaFactor_half`:
  `∫_{-T}^{T} G(1/2 + it) (Φ(1/2 + it) + Φ(1/2 - it)) dt →
    (ψ(1/4) - log π) F(0) + 2π ∫_0^∞ e^{-πx}/(1 - e^{-4πx}) (2F(0) - F(x) - F(-x)) dx`.

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

/-- The part of `ξ'/ξ(s)` that does not involve `ζ`: `1/s + 1/(s-1) + ψ(s/2)/2 - (log π)/2`
(Montgomery–Vaughan (12.24) with `q = 1`). -/
def gammaFactor (s : ℂ) : ℂ := 1 / s + 1 / (s - 1) + digamma (s / 2) / 2 - Real.log π / 2

/-- `J(x) = F(x) + F(-x)`. -/
def symmPart (F : ℝ → ℂ) (x : ℝ) : ℂ := F x + F (-x)

/-- `1/s + 1/(s-1)` at `s = 1/2 + it`. -/
def poleTerm (t : ℝ) : ℂ := 1 / (1 / 2 + t * I) + 1 / (t * I - 1 / 2)

theorem poleTerm_neg (t : ℝ) : poleTerm (-t) = -poleTerm t := by
  simp only [poleTerm, Complex.ofReal_neg]
  rw [show (1 / 2 + -(t : ℂ) * I) = -((t : ℂ) * I - 1 / 2) by ring,
    show (-(t : ℂ) * I - 1 / 2) = -(1 / 2 + (t : ℂ) * I) by ring, div_neg, div_neg]
  ring

theorem continuous_poleTerm : Continuous poleTerm := by
  have h1 : ∀ t : ℝ, (1 / 2 + (t : ℂ) * I) ≠ 0 := fun t h ↦ by
    have := congrArg Complex.re h
    simp at this
  have h2 : ∀ t : ℝ, ((t : ℂ) * I - 1 / 2) ≠ 0 := fun t h ↦ by
    have := congrArg Complex.re h
    simp at this
  unfold poleTerm
  exact (continuous_const.div (by fun_prop) h1).add (continuous_const.div (by fun_prop) h2)

/-- The integral over `[-T, T]` of an odd function vanishes. -/
theorem intervalIntegral_eq_zero_of_odd {f : ℝ → ℂ} (hf : ∀ t, f (-t) = -f t) (T : ℝ) :
    ∫ t in (-T)..T, f t = 0 := by
  have h := intervalIntegral.integral_comp_neg (a := -T) (b := T) f
  rw [neg_neg] at h
  simp_rw [hf, intervalIntegral.integral_neg] at h
  linear_combination (-1 / 2 : ℂ) * h

theorem gammaFactor_half_add_mul_I (t : ℝ) :
    gammaFactor (1 / 2 + t * I) =
      poleTerm t + digamma (((1 / 4 : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) * t * I) / 2 -
        Real.log π / 2 := by
  simp only [gammaFactor, poleTerm]
  rw [show (1 / 2 + (t : ℂ) * I - 1) = (t : ℂ) * I - 1 / 2 by ring,
    show (1 / 2 + (t : ℂ) * I) / 2 = ((1 / 4 : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) * t * I by
      push_cast; ring]

theorem Phi_add_Phi_one_sub_half (F : ℝ → ℂ) (t : ℝ) :
    Phi F (1 / 2 + t * I) + Phi F (1 - (1 / 2 + t * I)) = 𝓕 F t + 𝓕 F (-t) := by
  rw [show (1 : ℂ) - (1 / 2 + t * I) = 1 / 2 + ((-t : ℝ) : ℂ) * I by push_cast; ring,
    Phi_half_add_mul_I, Phi_half_add_mul_I]

theorem IsTestFunction.integrable_symmPart (hF : IsTestFunction F δ₀) :
    Integrable (symmPart F) :=
  hF.integrable_self.add hF.comp_neg.integrable_self

theorem IsTestFunction.boundedVariationOn_symmPart (hF : IsTestFunction F δ₀) :
    BoundedVariationOn (symmPart F) univ :=
  ne_top_of_le_ne_top
    (ENNReal.add_ne_top.2 ⟨hF.boundedVariationOn_self, hF.comp_neg.boundedVariationOn_self⟩)
    (eVariationOn_add_le _ _ _)

theorem IsTestFunction.isBigO_symmPart (hF : IsTestFunction F δ₀) :
    (fun x ↦ symmPart F x - symmPart F 0) =O[𝓝 0] fun x ↦ x := by
  simp only [symmPart, neg_zero]
  exact hF.isBigO_zero.congr_left fun x ↦ by ring

theorem IsTestFunction.fourier_symmPart (hF : IsTestFunction F δ₀) (t : ℝ) :
    𝓕 (symmPart F) t = 𝓕 F t + 𝓕 F (-t) := by
  rw [← Complex.fourier_comp_neg F t, Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul,
    ← integral_add (integrable_fourierIntegrand hF.integrable_self t)
      (integrable_fourierIntegrand hF.comp_neg.integrable_self t)]
  congr 1
  ext x
  simp only [symmPart, smul_add]

/-- `J = F + F(-·)` is continuous at `0`, hence normalized there. -/
theorem IsTestFunction.symmPart_zero (hF : IsTestFunction F δ₀) :
    symmPart F 0 = (rightLim (symmPart F) 0 + leftLim (symmPart F) 0) / 2 := by
  have h : Tendsto (fun x ↦ symmPart F x - symmPart F 0) (𝓝 0) (𝓝 0) :=
    hF.isBigO_symmPart.trans_tendsto (by simpa using (continuous_id (X := ℝ)).tendsto 0)
  have h' : Tendsto (symmPart F) (𝓝 0) (𝓝 (symmPart F 0)) := by
    have := h.add_const (symmPart F 0)
    simpa using this
  exact eq_rightLim_add_leftLim_div_two (h'.mono_left nhdsWithin_le_nhds)
    (h'.mono_left nhdsWithin_le_nhds) (by ring)

/-- `∫_{-T}^{T} Ĵ → J(0) = 2F(0)`. -/
theorem IsTestFunction.tendsto_integral_fourier_symmPart (hF : IsTestFunction F δ₀) :
    Tendsto (fun T : ℝ ↦ ∫ t in (-T)..T, 𝓕 (symmPart F) t) atTop (𝓝 (symmPart F 0)) := by
  have h := FourierIntegral.tendsto_partialInv_of_normalized hF.integrable_symmPart
    hF.boundedVariationOn_symmPart hF.symmPart_zero
  simpa [FourierIntegral.partialInv] using h

/-- G5: the terms of `ξ'/ξ` other than `ζ'/ζ`, integrated against `Φ(s) + Φ(1 - s)` on the critical
line. -/
theorem IsTestFunction.tendsto_integral_gammaFactor_half (hF : IsTestFunction F δ₀) :
    Tendsto (fun T : ℝ ↦ ∫ t in (-T)..T,
        gammaFactor (1 / 2 + t * I) * (Phi F (1 / 2 + t * I) + Phi F (1 - (1 / 2 + t * I))))
      atTop (𝓝 ((digamma (1 / 4) - Real.log π) * F 0 +
        2 * π * ∫ x in Ioi (0 : ℝ),
          ((Real.exp (-(π * x)) / (1 - Real.exp (-(4 * π * x))) : ℝ) : ℂ) *
            (2 * F 0 - F x - F (-x)))) := by
  set Ψ : ℝ → ℂ := fun t ↦ digamma (((1 / 4 : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) * t * I) with hΨdef
  set c : ℂ := (Real.log π / 2 : ℂ) with hc
  have hJc : Continuous (𝓕 (symmPart F)) :=
    FourierIntegral.continuous_fourier_of_integrable hF.integrable_symmPart
  have hΨc : Continuous Ψ := Complex.continuous_digamma_line (by norm_num) (1 / 2)
  have hpt : ∀ t : ℝ,
      gammaFactor (1 / 2 + t * I) * (Phi F (1 / 2 + t * I) + Phi F (1 - (1 / 2 + t * I))) =
        poleTerm t * 𝓕 (symmPart F) t + 1 / 2 * (Ψ t * 𝓕 (symmPart F) t) -
          c * 𝓕 (symmPart F) t := by
    intro t
    rw [gammaFactor_half_add_mul_I, Phi_add_Phi_one_sub_half, ← hF.fourier_symmPart t]
    ring
  have hodd : ∀ t : ℝ, poleTerm (-t) * 𝓕 (symmPart F) (-t) =
      -(poleTerm t * 𝓕 (symmPart F) t) := by
    intro t
    rw [poleTerm_neg, hF.fourier_symmPart, hF.fourier_symmPart, neg_neg]
    ring
  have hsplit : ∀ T : ℝ, ∫ t in (-T)..T,
      gammaFactor (1 / 2 + t * I) * (Phi F (1 / 2 + t * I) + Phi F (1 - (1 / 2 + t * I))) =
        1 / 2 * (∫ t in (-T)..T, Ψ t * 𝓕 (symmPart F) t) -
          c * ∫ t in (-T)..T, 𝓕 (symmPart F) t := by
    intro T
    have i1 : IntervalIntegrable (fun t ↦ poleTerm t * 𝓕 (symmPart F) t) volume (-T) T :=
      (continuous_poleTerm.mul hJc).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun t ↦ 1 / 2 * (Ψ t * 𝓕 (symmPart F) t)) volume (-T) T :=
      (continuous_const.mul (hΨc.mul hJc)).intervalIntegrable _ _
    have i12 : IntervalIntegrable
        (fun t ↦ poleTerm t * 𝓕 (symmPart F) t + 1 / 2 * (Ψ t * 𝓕 (symmPart F) t))
        volume (-T) T :=
      ((continuous_poleTerm.mul hJc).add (continuous_const.mul (hΨc.mul hJc))).intervalIntegrable
        _ _
    have i3 : IntervalIntegrable (fun t ↦ c * 𝓕 (symmPart F) t) volume (-T) T :=
      (continuous_const.mul hJc).intervalIntegrable _ _
    rw [intervalIntegral.integral_congr (fun t _ ↦ hpt t), intervalIntegral.integral_sub i12 i3,
      intervalIntegral.integral_add i1 i2, intervalIntegral_eq_zero_of_odd hodd T,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, zero_add]
  have h1 := Complex.tendsto_integral_digamma_line_mul_fourier (a := 1 / 4) (b := 1 / 2)
    (by norm_num) (by norm_num) hF.integrable_symmPart hF.boundedVariationOn_symmPart
    hF.isBigO_symmPart
  have h2 := hF.tendsto_integral_fourier_symmPart
  have h3 := (h1.const_mul (1 / 2 : ℂ)).sub (h2.const_mul c)
  have hK : ∫ x in Ioi (0 : ℝ), ((Real.exp (-(2 * π * (1 / 4 : ℝ) * x / (1 / 2 : ℝ))) /
        (1 - Real.exp (-(2 * π * x / (1 / 2 : ℝ)))) : ℝ) : ℂ) *
          (symmPart F 0 - symmPart F (-x)) =
      ∫ x in Ioi (0 : ℝ), ((Real.exp (-(π * x)) / (1 - Real.exp (-(4 * π * x))) : ℝ) : ℂ) *
        (2 * F 0 - F x - F (-x)) := by
    congr 1
    ext x
    have e1 : -(2 * π * (1 / 4 : ℝ) * x / (1 / 2 : ℝ)) = -(π * x) := by ring
    have e2 : -(2 * π * x / (1 / 2 : ℝ)) = -(4 * π * x) := by ring
    rw [e1, e2]
    simp only [symmPart, neg_zero, neg_neg]
    ring
  rw [hK] at h3
  convert h3.congr (fun T ↦ (hsplit T).symm) using 2
  simp only [symmPart, neg_zero, hc]
  push_cast
  ring

end WeilExplicitFormula
