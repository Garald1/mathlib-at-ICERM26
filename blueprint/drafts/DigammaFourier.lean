/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Harald Helfgott
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.BoxIntegral.Stieltjes.FourierIntegral

/-! # The digamma function on vertical lines, and Montgomery–Vaughan's Lemma 12.14

* (C.10) of Montgomery–Vaughan: `ψ(s) = -1/s - C₀ - ∑_{n ≥ 1} (1/(s+n) - 1/n)`;
* `ψ'(s) = ∑_{n ≥ 0} (n+s)⁻²`, and `ψ'(σ+iy) = O(1/|y|)` for `|y| ≥ 1`;
* growth of `ψ` on vertical lines;
* Theorem C.5 of Montgomery–Vaughan: `∫_{-T}^{T} ψ(a+ibt) e(-xt) dt`;
* Lemma 12.14 of Montgomery–Vaughan, (12.27): `lim_T ∫_{-T}^{T} ψ(a ± ibt) Ĵ(t) dt`.

Here `ψ = Γ'/Γ` is `Complex.digamma`.

Blueprint: `blueprint/WeilExplicitFormula.md`, part B.

## Status

STATEMENTS ONLY. This file was drafted by Claude (Anthropic) in November 2026 in an environment
without Lean; it has not been compiled. Every proof is `sorry`.
-/

@[expose] public section

open Real Filter Topology MeasureTheory Asymptotics
open scoped FourierTransform

namespace Complex

/-- B1: (C.10) of Montgomery–Vaughan. -/
theorem digamma_eq_tsum {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) :
    digamma s = -1 / s - Real.eulerMascheroniConstant -
      ∑' n : ℕ, (1 / (s + ((n : ℂ) + 1)) - 1 / ((n : ℂ) + 1)) := by
  sorry

/-- B2: `ψ'(s) = ∑_{n ≥ 0} (n + s)⁻²`. -/
theorem deriv_digamma {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) :
    deriv digamma s = ∑' n : ℕ, 1 / (s + n) ^ 2 := by
  sorry

/-- B2: `ψ'(σ + iy) = O(1/|y|)` for `|y| ≥ 1`, uniformly in `σ ∈ ℝ`. -/
theorem exists_norm_deriv_digamma_le :
    ∃ C, ∀ σ y : ℝ, 1 ≤ |y| → ‖deriv digamma (σ + y * I)‖ ≤ C / |y| := by
  sorry

/-- B3: `ψ(σ + it) = O(log(|t| + 2))` uniformly for `σ` in a compact subinterval of `(0, ∞)`. -/
theorem exists_norm_digamma_le_log {σ₁ σ₂ : ℝ} (h₁ : 0 < σ₁) :
    ∃ C, ∀ σ t : ℝ, σ ∈ Set.Icc σ₁ σ₂ → ‖digamma (σ + t * I)‖ ≤ C * Real.log (|t| + 2) := by
  sorry

/-- B3: `ψ(a + ibt) = ψ(a) + O(|t|)` for all real `t`. -/
theorem exists_norm_digamma_sub_le {a : ℝ} (ha : 0 < a) (b : ℝ) :
    ∃ C, ∀ t : ℝ, ‖digamma (a + b * t * I) - digamma a‖ ≤ C * |t| := by
  sorry

/-- B4: Theorem C.5 of Montgomery–Vaughan. For `x < 0` the integral picks up the residues of
`ψ(a + bs)` at `s = -(n + a)/b`, whose sum is `-(2π/b) e^{2πax/b} (1 - e^{2πx/b})⁻¹`. -/
theorem exists_integral_digamma_mul_exp {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ C, ∀ x T : ℝ, x ≠ 0 → 1 ≤ T →
      ‖(∫ t in (-T)..T, digamma (a + b * t * I) * Complex.exp (-(2 * π * x * t) * I)) -
          (-(digamma (a + b * T * I) * Complex.exp (-(2 * π * x * T) * I)) / (2 * π * I * x) +
            digamma (a - b * T * I) * Complex.exp ((2 * π * x * T) * I) / (2 * π * I * x) -
            if x < 0 then
              ((2 * π / b * Real.exp (2 * π * a * x / b) / (1 - Real.exp (2 * π * x / b)) : ℝ) : ℂ)
            else 0)‖ ≤ C / (x ^ 2 * T) := by
  sorry

/-- B5: Lemma 12.14 of Montgomery–Vaughan, (12.27), with the sign `+`. -/
theorem tendsto_integral_digamma_mul_fourier {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {J : ℝ → ℂ}
    (hJ1 : Integrable J) (hJ2 : BoundedVariationOn J Set.univ)
    (hJ0 : (fun x ↦ J x - J 0) =O[𝓝 0] (fun x ↦ x)) :
    Tendsto (fun T : ℝ ↦ ∫ t in (-T)..T, digamma (a + b * t * I) * 𝓕 J t) atTop
      (𝓝 (digamma a * J 0 + ((2 * π / b : ℝ) : ℂ) *
        ∫ x in Set.Ioi (0 : ℝ),
          ((Real.exp (-(2 * π * a * x / b)) / (1 - Real.exp (-(2 * π * x / b))) : ℝ) : ℂ) *
            (J 0 - J (-x)))) := by
  sorry

/-- B5: Lemma 12.14 of Montgomery–Vaughan, (12.27), with the sign `-`. -/
theorem tendsto_integral_digamma_conj_mul_fourier {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {J : ℝ → ℂ}
    (hJ1 : Integrable J) (hJ2 : BoundedVariationOn J Set.univ)
    (hJ0 : (fun x ↦ J x - J 0) =O[𝓝 0] (fun x ↦ x)) :
    Tendsto (fun T : ℝ ↦ ∫ t in (-T)..T, digamma (a - b * t * I) * 𝓕 J t) atTop
      (𝓝 (digamma a * J 0 + ((2 * π / b : ℝ) : ℂ) *
        ∫ x in Set.Ioi (0 : ℝ),
          ((Real.exp (-(2 * π * a * x / b)) / (1 - Real.exp (-(2 * π * x / b))) : ℝ) : ℂ) *
            (J 0 - J x))) := by
  sorry

end Complex
