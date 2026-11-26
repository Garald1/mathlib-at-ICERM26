/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Harald Helfgott
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.DigammaFourier
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.Complex.BorelCaratheodory
public import Mathlib.Analysis.Meromorphic.FactorizedRational
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.NumberTheory.LSeries.RiemannZeta

/-! # Weil's explicit formula for the Riemann zeta function

Theorem 12.13 of Montgomery–Vaughan, *Multiplicative Number Theory I*, in the case `q = 1`:
for a test function `F` as in (12.20)–(12.21) of Montgomery–Vaughan, with
`Φ(s) = ∫ F(x) e^{-(s-1/2)2πx} dx`,
```
lim_{T→∞} ∑_{|γ| ≤ T} Φ(ρ) = Φ(0) + Φ(1) + (ψ(1/4) - log π) F(0) / (2π)
    - (1/2π) ∑_n Λ(n) n^{-1/2} (F(-log n / 2π) + F(log n / 2π))
    + ∫_0^∞ e^{-πx} (1 - e^{-4πx})⁻¹ (2F(0) - F(x) - F(-x)) dx,
```
the sum running over the non-trivial zeros `ρ = β + iγ` of `ζ`, with multiplicity.

The hypotheses (12.20)–(12.21) are stated in the equivalent form "`x ↦ e^{a|x|} F(x)` is integrable
and of bounded variation on `ℝ`", `a = (1/2 + δ₀) 2π` (see the blueprint, §0).

Blueprint: `blueprint/WeilExplicitFormula.md`, parts C–G. The labels C1, …, G6 below refer to it.

## Status

STATEMENTS ONLY. This file was drafted by Claude (Anthropic) in November 2026 in an environment
without Lean; it has not been compiled. Every proof is `sorry`.
-/

@[expose] public section

open Real Complex Filter Topology MeasureTheory Asymptotics Metric
open scoped FourierTransform Interval

namespace WeilExplicitFormula

/-! ### C: the function `ξ` and the zeros of `ζ` -/

/-- Riemann's `ξ(s) = ½ s (s-1) π^{-s/2} Γ(s/2) ζ(s)` (Montgomery–Vaughan (10.5)), written with
Mathlib's entire function `completedRiemannZeta₀`, so that it is visibly entire. -/
noncomputable def riemannXi (s : ℂ) : ℂ := (s * (s - 1) * completedRiemannZeta₀ s + 1) / 2

/-- C1 -/
theorem differentiable_riemannXi : Differentiable ℂ riemannXi := by
  sorry

/-- C1: the functional equation. -/
theorem riemannXi_one_sub (s : ℂ) : riemannXi (1 - s) = riemannXi s := by
  sorry

/-- C1: `ξ(s̄) = conj ξ(s)`. -/
theorem riemannXi_conj (s : ℂ) : riemannXi (starRingEnd ℂ s) = starRingEnd ℂ (riemannXi s) := by
  sorry

/-- C1: agreement with Montgomery–Vaughan (10.5) in the right half-plane. (The restriction
`0 < s.re` matters in Lean: at `s = -2k` Mathlib's `Gamma` takes the value `0`.) -/
theorem riemannXi_eq {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannXi s = s * (s - 1) / 2 * Gammaℝ s * riemannZeta s := by
  sorry

/-- C2: the zeros of `ξ` are the non-trivial zeros of `ζ`. -/
theorem riemannXi_eq_zero_iff {s : ℂ} :
    riemannXi s = 0 ↔ riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 := by
  sorry

/-- C2: with the same multiplicities. -/
theorem analyticOrderAt_riemannXi {s : ℂ} (hs : 0 < s.re) (hs1 : s.re < 1) :
    analyticOrderAt riemannXi s = analyticOrderAt riemannZeta s := by
  sorry

/-- The multiplicity of `ρ` as a zero of `ξ` (`0` if `ξ(ρ) ≠ 0`). -/
noncomputable def zeroMult (ρ : ℂ) : ℕ := analyticOrderNatAt riemannXi ρ

/-- C3: Montgomery–Vaughan (10.25). -/
theorem logDeriv_riemannXi {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    logDeriv riemannXi s = 1 / s + 1 / (s - 1) + logDeriv riemannZeta s +
      digamma (s / 2) / 2 - Real.log π / 2 := by
  sorry

/-- C4: Montgomery–Vaughan Theorem 10.13, `N(T + 1) - N(T) ≪ log(T + 2)`. -/
theorem exists_sum_zeroMult_le :
    ∃ C, ∀ T : ℝ, 0 ≤ T →
      (∑ᶠ ρ ∈ {ρ : ℂ | riemannXi ρ = 0 ∧ ρ.im ∈ Set.Icc T (T + 1)}, (zeroMult ρ : ℝ)) ≤
        C * Real.log (T + 2) := by
  sorry

/-- C5: Montgomery–Vaughan Lemma 6.3 (Landau). The sum runs over the zeros of `f` in `|w| ≤ R`. -/
theorem exists_norm_logDeriv_sub_sum_le {r R : ℝ} (hr : 0 < r) (hrR : r < R) (hR : R < 1) :
    ∃ C, ∀ (f : ℂ → ℂ) (M : ℝ), AnalyticOnNhd ℂ f (closedBall 0 1) → f 0 ≠ 0 →
      (∀ z ∈ closedBall (0 : ℂ) 1, ‖f z‖ ≤ M) →
      ∀ z ∈ closedBall (0 : ℂ) r, f z ≠ 0 →
        ‖logDeriv f z - ∑ᶠ w ∈ {w : ℂ | ‖w‖ ≤ R ∧ f w = 0}, (analyticOrderNatAt f w : ℂ) / (z - w)‖ ≤
          C * Real.log (M / ‖f 0‖) := by
  sorry

/-- C6: local partial fractions for `ζ'/ζ` (compare Montgomery–Vaughan Lemma 12.1). -/
theorem exists_norm_logDeriv_riemannZeta_sub_sum_le :
    ∃ C, ∀ s : ℂ, 2 ≤ |s.im| → s.re ∈ Set.Icc (1 / 2 : ℝ) 2 → riemannZeta s ≠ 0 →
      ‖logDeriv riemannZeta s -
          ∑ᶠ ρ ∈ {ρ : ℂ | riemannXi ρ = 0 ∧ |ρ.im - s.im| ≤ 1}, (zeroMult ρ : ℂ) / (s - ρ)‖ ≤
        C * Real.log |s.im| := by
  sorry

/-- C7: good heights (Montgomery–Vaughan Lemma 12.2, for `ξ'/ξ`). -/
theorem exists_good_height :
    ∃ C, ∀ T : ℝ, 2 ≤ T → ∃ T₁ ∈ Set.Icc T (T + 1), ∀ σ ∈ Set.Icc (-1 : ℝ) 2,
      riemannXi (σ + T₁ * I) ≠ 0 ∧ riemannXi (σ - T₁ * I) ≠ 0 ∧
      ‖logDeriv riemannXi (σ + T₁ * I)‖ ≤ C * Real.log T ^ 2 ∧
      ‖logDeriv riemannXi (σ - T₁ * I)‖ ≤ C * Real.log T ^ 2 := by
  sorry

/-! ### D: integrals over the boundary of a rectangle -/

/-- The integral of `f` over the boundary of the rectangle with opposite corners `z` and `w`
(counterclockwise if `z.re < w.re` and `z.im < w.im`); this is the expression of
`Complex.integral_boundary_rect_eq_zero_of_differentiableOn`. -/
noncomputable def rectIntegral (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
    I * (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) - I * (∫ y : ℝ in z.im..w.im, f (z.re + y * I))

/-- D1: the argument principle with a holomorphic weight. -/
theorem rectIntegral_mul_logDeriv {f φ : ℂ → ℂ} {z w : ℂ} (hre : z.re < w.re) (him : z.im < w.im)
    (hf : AnalyticOnNhd ℂ f ([[z.re, w.re]] ×ℂ [[z.im, w.im]]))
    (hφ : AnalyticOnNhd ℂ φ ([[z.re, w.re]] ×ℂ [[z.im, w.im]]))
    (hbd : ∀ u ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]], u ∉ Set.Ioo z.re w.re ×ℂ Set.Ioo z.im w.im →
      f u ≠ 0) :
    rectIntegral (fun s ↦ φ s * logDeriv f s) z w =
      2 * π * I * ∑ᶠ ρ ∈ {ρ : ℂ | ρ ∈ Set.Ioo z.re w.re ×ℂ Set.Ioo z.im w.im ∧ f ρ = 0},
        (analyticOrderNatAt f ρ : ℂ) * φ ρ := by
  sorry

/-! ### E: the test function and `Φ` -/

/-- The hypotheses of Montgomery–Vaughan Theorem 12.13, in the form described in the blueprint
(§0): with `a = (1 + 2δ₀)π`, the function `x ↦ e^{a|x|} F(x)` is integrable and of bounded
variation on `ℝ` (equivalent to (12.20) and (12.21)); `F` is normalized at every point; and
`F(x) + F(-x) = 2F(0) + O(|x|)`. -/
structure IsTestFunction (F : ℝ → ℂ) (δ₀ : ℝ) : Prop where
  pos : 0 < δ₀
  integrable : Integrable (fun x ↦ (Real.exp ((1 + 2 * δ₀) * π * |x|) : ℂ) * F x)
  boundedVariation :
    BoundedVariationOn (fun x ↦ (Real.exp ((1 + 2 * δ₀) * π * |x|) : ℂ) * F x) Set.univ
  normalized : ∀ x, F x = (Function.leftLim F x + Function.rightLim F x) / 2
  isBigO_zero : (fun x ↦ F x + F (-x) - 2 * F 0) =O[𝓝 0] (fun x ↦ x)

/-- `Φ(s) = ∫ F(x) e^{-(s - 1/2) 2π x} dx`. -/
noncomputable def Phi (F : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ x : ℝ, F x * Complex.exp (-(s - 1 / 2) * (2 * π * x))

variable {F : ℝ → ℂ} {δ₀ : ℝ}

/-- E0: continuous, Lipschitz, compactly supported functions are test functions for every `δ₀ > 0`
(this is the case needed in Proposition 2.2 of the Mertens note). -/
theorem IsTestFunction.of_lipschitzWith {K : NNReal} (hL : LipschitzWith K F)
    (hc : HasCompactSupport F) (hδ₀ : 0 < δ₀) : IsTestFunction F δ₀ := by
  sorry

/-- E2 -/
theorem IsTestFunction.differentiableOn_Phi (hF : IsTestFunction F δ₀) :
    DifferentiableOn ℂ (Phi F) {s | -δ₀ < s.re ∧ s.re < 1 + δ₀} := by
  sorry

/-- E2: on the critical line, `Φ` is the Fourier transform of `F`. -/
theorem Phi_half_add_mul_I (F : ℝ → ℂ) (t : ℝ) : Phi F (1 / 2 + t * I) = 𝓕 F t := by
  sorry

/-- E2: `Φ(1 - s)` is the `Φ` of `x ↦ F(-x)`. -/
theorem Phi_one_sub (F : ℝ → ℂ) (s : ℂ) : Phi F (1 - s) = Phi (fun x ↦ F (-x)) s := by
  sorry

/-- E3: `Φ(s) ≪ 1/(|t| + 1)` uniformly in the closed strip `-δ₀ ≤ σ ≤ 1 + δ₀`. -/
theorem IsTestFunction.exists_norm_Phi_le (hF : IsTestFunction F δ₀) :
    ∃ C, ∀ s : ℂ, s.re ∈ Set.Icc (-δ₀) (1 + δ₀) → ‖Phi F s‖ ≤ C / (|s.im| + 1) := by
  sorry

/-! ### F: the Dirichlet series part -/

/-- The function `H` of the proof of Montgomery–Vaughan Theorem 12.13, for `q = 1`. -/
noncomputable def H (F : ℝ → ℂ) (δ₁ x : ℝ) : ℂ :=
  -∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
    (F (x - Real.log n / (2 * π)) + F (-x + Real.log n / (2 * π))) *
      (Real.exp (-((1 / 2 + δ₁) * 2 * π * x)) : ℂ)

/-- F2 -/
theorem IsTestFunction.integrable_H (hF : IsTestFunction F δ₀) {δ₁ : ℝ} (h0 : 0 < δ₁)
    (h1 : δ₁ < δ₀) : Integrable (H F δ₁) := by
  sorry

/-- F2 -/
theorem IsTestFunction.boundedVariationOn_H (hF : IsTestFunction F δ₀) {δ₁ : ℝ} (h0 : 0 < δ₁)
    (h1 : δ₁ < δ₀) : BoundedVariationOn (H F δ₁) Set.univ := by
  sorry

/-- F2: `H` is normalized at `0`. -/
theorem IsTestFunction.H_zero (hF : IsTestFunction F δ₀) {δ₁ : ℝ} (h0 : 0 < δ₁) (h1 : δ₁ < δ₀) :
    H F δ₁ 0 = (Function.rightLim (H F δ₁) 0 + Function.leftLim (H F δ₁) 0) / 2 := by
  sorry

/-- F1–F2: Montgomery–Vaughan (12.25)–(12.26) on the line `σ = 1 + δ₁`. -/
theorem IsTestFunction.fourier_H (hF : IsTestFunction F δ₀) {δ₁ : ℝ} (h0 : 0 < δ₁) (h1 : δ₁ < δ₀)
    (t : ℝ) :
    𝓕 (H F δ₁) t = (Phi F (1 + δ₁ + t * I) + Phi F (1 - (1 + δ₁ + t * I))) *
      logDeriv riemannZeta (1 + δ₁ + t * I) := by
  sorry

/-! ### G: assembly -/

/-- G1: the argument principle for `ξ` on the rectangle `[-δ₁, 1 + δ₁] × [-T₁, T₁]`. -/
theorem IsTestFunction.sum_zeros_eq_rectIntegral (hF : IsTestFunction F δ₀) {δ₁ T₁ : ℝ}
    (h0 : 0 < δ₁) (h1 : δ₁ < δ₀) (hT₁ : 0 < T₁)
    (hT : ∀ σ : ℝ, riemannXi (σ + T₁ * I) ≠ 0 ∧ riemannXi (σ - T₁ * I) ≠ 0) :
    ∑ᶠ ρ ∈ {ρ : ℂ | riemannXi ρ = 0 ∧ |ρ.im| ≤ T₁}, (zeroMult ρ : ℂ) * Phi F ρ =
      (2 * π * I)⁻¹ *
        rectIntegral (fun s ↦ Phi F s * logDeriv riemannXi s) (-δ₁ - T₁ * I) (1 + δ₁ + T₁ * I) := by
  sorry

/-- The right-hand side of the explicit formula (Montgomery–Vaughan (12.22) with `q = 1`). -/
noncomputable def rhs (F : ℝ → ℂ) : ℂ :=
  Phi F 0 + Phi F 1 + (2 * π : ℂ)⁻¹ * (digamma (1 / 4) - Real.log π) * F 0 -
    (2 * π : ℂ)⁻¹ * ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
      (F (-(Real.log n / (2 * π))) + F (Real.log n / (2 * π))) +
    ∫ x in Set.Ioi (0 : ℝ),
      ((Real.exp (-(π * x)) / (1 - Real.exp (-(4 * π * x))) : ℝ) : ℂ) * (2 * F 0 - F x - F (-x))

/-- **Weil's explicit formula** (Montgomery–Vaughan Theorem 12.13 with `q = 1`), summing over the
zeros of `ξ` with multiplicity. -/
theorem IsTestFunction.tendsto_sum_zeros (hF : IsTestFunction F δ₀) :
    Tendsto (fun T : ℝ ↦ ∑ᶠ ρ ∈ {ρ : ℂ | riemannXi ρ = 0 ∧ |ρ.im| ≤ T}, (zeroMult ρ : ℂ) * Phi F ρ)
      atTop (𝓝 (rhs F)) := by
  sorry

/-- **Weil's explicit formula** (Montgomery–Vaughan Theorem 12.13 with `q = 1`), summing over the
non-trivial zeros of `ζ` with multiplicity. -/
theorem IsTestFunction.tendsto_sum_riemannZeta_zeros (hF : IsTestFunction F δ₀) :
    Tendsto (fun T : ℝ ↦ ∑ᶠ ρ ∈ {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        (analyticOrderNatAt riemannZeta ρ : ℂ) * Phi F ρ) atTop (𝓝 (rhs F)) := by
  sorry

end WeilExplicitFormula
