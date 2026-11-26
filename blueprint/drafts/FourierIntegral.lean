/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Harald Helfgott
-/
module

public import Mathlib.Analysis.BoxIntegral.Stieltjes.DirichletJordan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-! # The Fourier integral theorem for integrable functions of bounded variation

The integral analogue of the Dirichlet–Jordan theorem (`DirichletJordan.lean`): if `g : ℝ → ℂ` is
integrable and of bounded variation on `ℝ`, then for every `x`,
`∫_{-T}^{T} ĝ(t) e(tx) dt → (g(x+) + g(x-))/2` as `T → ∞`.

This is the "Fourier integral theorem" invoked in the proof of Theorem 12.13 of
Montgomery–Vaughan (applied there to the function `H` and to `F`). The proof follows the route of
`DirichletJordan.lean`: Fejér's theorem for Fourier integrals, Hardy's Tauberian theorem (reduced
to the discrete one in `SpecificLimits/Cesaro.lean`), and `ĝ(t) = O(1/|t|)`
(`FourierTransform.fourier_bounded_variation`).

Blueprint: `blueprint/WeilExplicitFormula.md`, part A.

## Status

STATEMENTS ONLY. This file was drafted by Claude (Anthropic) in November 2026 in an environment
without Lean; it has not been compiled. Every proof is `sorry`.
-/

@[expose] public section

open Real Filter Topology MeasureTheory
open scoped FourierTransform

namespace FourierIntegral

variable {g : ℝ → ℂ}

/-- The partial Fourier inversion integral `∫_{-T}^{T} ĝ(t) e(tx) dt`, `e(θ) = e^{2πiθ}`. -/
noncomputable def partialInv (g : ℝ → ℂ) (T x : ℝ) : ℂ :=
  ∫ t in (-T)..T, 𝓕 g t * Complex.exp (2 * π * t * x * Complex.I)

/-- The Fejér (Cesàro) mean of `partialInv`: `∫_{-T}^{T} (1 - |t|/T) ĝ(t) e(tx) dt`. -/
noncomputable def fejerInv (g : ℝ → ℂ) (T x : ℝ) : ℂ :=
  ∫ t in (-T)..T, ((1 - |t| / T : ℝ) : ℂ) * 𝓕 g t * Complex.exp (2 * π * t * x * Complex.I)

/-- The Fejér kernel on `ℝ`, `K_T(y) = T sinc(πTy)²`. -/
noncomputable def fejerKernel (T y : ℝ) : ℝ := T * sinc (π * T * y) ^ 2

/-! ### A2: the Fejér kernel -/

/-- The Fourier transform of the triangle function `(1 - |t|/T)₊` is the Fejér kernel. -/
theorem integral_triangle_mul_exp {T : ℝ} (hT : 0 < T) (y : ℝ) :
    ∫ t in (-T)..T, ((1 - |t| / T : ℝ) : ℂ) * Complex.exp (2 * π * t * y * Complex.I) =
      (fejerKernel T y : ℂ) := by
  sorry

theorem fejerKernel_nonneg {T : ℝ} (hT : 0 ≤ T) (y : ℝ) : 0 ≤ fejerKernel T y := by
  sorry

theorem fejerKernel_neg (T y : ℝ) : fejerKernel T (-y) = fejerKernel T y := by
  sorry

theorem fejerKernel_le_div_sq {T : ℝ} (hT : 0 < T) {y : ℝ} (hy : y ≠ 0) :
    fejerKernel T y ≤ 1 / (π ^ 2 * T * y ^ 2) := by
  sorry

theorem integrable_fejerKernel {T : ℝ} (hT : 0 < T) : Integrable (fejerKernel T) := by
  sorry

/-- `∫ K_T = 1` (for instance by Fourier inversion, `Continuous.fourierInv_fourier_eq`, applied to
the triangle function). -/
theorem integral_fejerKernel {T : ℝ} (hT : 0 < T) : ∫ y, fejerKernel T y = 1 := by
  sorry

/-! ### A3: Fejér's theorem for Fourier integrals -/

theorem fejerInv_eq_integral (hg : Integrable g) {T : ℝ} (hT : 0 < T) (x : ℝ) :
    fejerInv g T x = ∫ y, (fejerKernel T y : ℂ) * g (x - y) := by
  sorry

/-- **Fejér's theorem for Fourier integrals**: at a point where `g` has one-sided limits, the
Fejér means of the Fourier inversion integral converge to the average of the two limits. -/
theorem tendsto_fejerInv_of_tendsto (hg : Integrable g) {x : ℝ} {l₁ l₂ : ℂ}
    (h₁ : Tendsto g (𝓝[>] x) (𝓝 l₁)) (h₂ : Tendsto g (𝓝[<] x) (𝓝 l₂)) :
    Tendsto (fun T ↦ fejerInv g T x) atTop (𝓝 ((l₁ + l₂) / 2)) := by
  sorry

/-! ### A4: Hardy's Tauberian theorem for integrals -/

/-- **Hardy's Tauberian theorem for integrals**: if `u(t) = O(1/t)` and the Cesàro means of
`∫_0^T u` converge to `s`, then `∫_0^T u → s`. (By reduction to
`tendsto_sum_range_of_tendsto_cesaroMean`, with `u_k = ∫_k^{k+1} u`.) -/
theorem tendsto_integral_of_tendsto_cesaro {u : ℝ → ℂ} {A : ℝ} {s : ℂ}
    (hu : ∀ T, IntervalIntegrable u volume 0 T) (hA : ∀ t, 1 ≤ t → ‖u t‖ ≤ A / t)
    (hσ : Tendsto (fun T : ℝ ↦ (T : ℂ)⁻¹ * ∫ v in (0 : ℝ)..T, ∫ t in (0 : ℝ)..v, u t) atTop (𝓝 s)) :
    Tendsto (fun T ↦ ∫ t in (0 : ℝ)..T, u t) atTop (𝓝 s) := by
  sorry

/-! ### A5: the Fourier integral theorem -/

/-- **Fourier integral theorem** (integral analogue of the Dirichlet–Jordan theorem): if `g` is
integrable and of bounded variation on `ℝ`, then `∫_{-T}^{T} ĝ(t) e(tx) dt → (g(x+) + g(x-))/2`. -/
theorem tendsto_partialInv (hg1 : Integrable g) (hg2 : BoundedVariationOn g Set.univ) (x : ℝ) :
    Tendsto (fun T ↦ partialInv g T x) atTop
      (𝓝 ((Function.rightLim g x + Function.leftLim g x) / 2)) := by
  sorry

/-- The Fourier integral theorem at a point where `g` is normalized. -/
theorem tendsto_partialInv_of_normalized (hg1 : Integrable g) (hg2 : BoundedVariationOn g Set.univ)
    {x : ℝ} (hx : g x = (Function.rightLim g x + Function.leftLim g x) / 2) :
    Tendsto (fun T ↦ partialInv g T x) atTop (𝓝 (g x)) := by
  sorry

/-- A6 (the analogue of Wheeden–Zygmund (12.50)(c)): the partial inversion integrals are
uniformly bounded. -/
theorem exists_norm_partialInv_le (hg1 : Integrable g) (hg2 : BoundedVariationOn g Set.univ) :
    ∃ C, ∀ T x, 0 ≤ T → ‖partialInv g T x‖ ≤ C := by
  sorry

end FourierIntegral
