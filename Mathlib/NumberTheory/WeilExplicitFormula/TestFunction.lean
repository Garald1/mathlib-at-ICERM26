/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Harald Helfgott
-/
module

public import Mathlib.Analysis.BoxIntegral.Stieltjes.FourierIntegral
public import Mathlib.Analysis.BoxIntegral.Stieltjes.VariationBounds
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-! # Test functions for Weil's explicit formula, and the transform `Φ`

Part E of the blueprint for Montgomery–Vaughan, *Multiplicative Number Theory I*,
Theorem 12.13 (Weil's explicit formula) with `q = 1`. Montgomery–Vaughan assume that `F` is
measurable, that `∫ e^{(1/2+δ₀)2π|x|} |F(x)| dx < ∞` (12.20) and
`∫ e^{(1/2+δ₀)2π|x|} |dF(x)| < ∞` (12.21), that `F(x) = (F(x-) + F(x+))/2` for all `x`, and that
`F(x) + F(-x) = 2F(0) + O(|x|)`; and they put `Φ(s) = ∫ F(x) e^{-(s-1/2)2πx} dx`.

As in the blueprint, (12.20)–(12.21) are replaced by the equivalent condition that
`G(x) = e^{a|x|} F(x)`, `a = (1 + 2δ₀)π`, is integrable and of bounded variation on `ℝ`
(`IsTestFunction`).

## Main results

* `IsTestFunction.integrable_mul_exp`, `IsTestFunction.eVariationOn_mul_exp_le`: for
  `|c| ≤ a`, `x ↦ F(x) e^{cx}` is integrable, with variation bounded uniformly in `c` (E1).
* `Phi_eq_fourier`, `Phi_half_add_mul_I`, `Phi_one_sub`: `Φ(σ + it)` is the Fourier transform of
  `x ↦ F(x) e^{(1-2σ)πx}` at `t`; `Φ(1/2 + it) = F̂(t)`; `Φ(1 - s)` is the `Φ` of `x ↦ F(-x)` (E2).
* `IsTestFunction.differentiableOn_Phi`: `Φ` is holomorphic on `-δ₀ < σ < 1 + δ₀` (E2).
* `IsTestFunction.exists_norm_Phi_le`: `Φ(s) ≪ 1/(|t| + 1)` uniformly for
  `-δ₀ ≤ σ ≤ 1 + δ₀` (E3).
* `IsTestFunction.of_lipschitzWith`: Lipschitz functions of compact support are test functions
  for every `δ₀ > 0` (E0).

The names and statements of `IsTestFunction`, `Phi` and of the results E0, E2, E3 are those of the
draft `blueprint/drafts/WeilExplicitFormula.lean` (branch `weil-explicit-formula` of
`Garald1/mathlib-at-ICERM26`).

## AI usage

This file was written by Claude (Anthropic) in November 2026. It compiles, but has not been
reviewed by a human.
-/

@[expose] public section

open Real Complex Filter Topology MeasureTheory Asymptotics Set
open scoped FourierTransform

noncomputable section

namespace WeilExplicitFormula

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
def Phi (F : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ x : ℝ, F x * Complex.exp (-(s - 1 / 2) * (2 * π * x))

variable {F : ℝ → ℂ} {δ₀ : ℝ}

/-! ### E1: the weight `e^{a|x|}` -/

/-- `G(x) = e^{a|x|} F(x)`, `a = (1 + 2δ₀)π`. -/
def weighted (F : ℝ → ℂ) (δ₀ x : ℝ) : ℂ := (Real.exp ((1 + 2 * δ₀) * π * |x|) : ℂ) * F x

theorem eq_exp_mul_weighted (x : ℝ) :
    F x = (Real.exp (-((1 + 2 * δ₀) * π * |x|)) : ℂ) * weighted F δ₀ x := by
  unfold weighted
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
    Complex.ofReal_one, one_mul]

theorem IsTestFunction.aestronglyMeasurable (hF : IsTestFunction F δ₀) :
    AEStronglyMeasurable F volume := by
  have h : F = fun x ↦ (Real.exp (-((1 + 2 * δ₀) * π * |x|)) : ℂ) * weighted F δ₀ x :=
    funext eq_exp_mul_weighted
  rw [h]
  exact (by fun_prop : Continuous fun x : ℝ ↦
    (Real.exp (-((1 + 2 * δ₀) * π * |x|)) : ℂ)).aestronglyMeasurable.mul hF.integrable.1

/-- `G` is bounded: `‖G(x)‖ ≤ ‖G(0)‖ + Var(G)`. -/
theorem IsTestFunction.norm_weighted_le (hF : IsTestFunction F δ₀) (x : ℝ) :
    ‖weighted F δ₀ x‖ ≤ ‖weighted F δ₀ 0‖ + (eVariationOn (weighted F δ₀) univ).toReal := by
  have h : dist (weighted F δ₀ x) (weighted F δ₀ 0) ≤ (eVariationOn (weighted F δ₀) univ).toReal :=
    hF.boundedVariation.dist_le (mem_univ x) (mem_univ 0)
  rw [dist_eq_norm] at h
  calc ‖weighted F δ₀ x‖ = ‖weighted F δ₀ 0 + (weighted F δ₀ x - weighted F δ₀ 0)‖ := by
        rw [add_sub_cancel]
    _ ≤ ‖weighted F δ₀ 0‖ + ‖weighted F δ₀ x - weighted F δ₀ 0‖ := norm_add_le _ _
    _ ≤ _ := by linarith

/-- The damping factor `x ↦ e^{cx - a|x|}`. -/
def damp (a c x : ℝ) : ℝ := Real.exp (c * x - a * |x|)

theorem damp_pos (a c x : ℝ) : 0 < damp a c x := Real.exp_pos _

theorem damp_le_one {a c : ℝ} (hc : |c| ≤ a) (x : ℝ) : damp a c x ≤ 1 := by
  unfold damp
  rw [Real.exp_le_one_iff]
  have h1 : c * x ≤ |c| * |x| := by rw [← abs_mul]; exact le_abs_self _
  have h2 : |c| * |x| ≤ a * |x| := mul_le_mul_of_nonneg_right hc (abs_nonneg x)
  linarith

/-- `x ↦ e^{cx - a|x|}` has variation at most `2` when `|c| ≤ a`. -/
theorem eVariationOn_damp_le {a c : ℝ} (hc : |c| ≤ a) (s : Set ℝ) :
    eVariationOn (damp a c) s ≤ 2 := by
  have hca : 0 ≤ c + a := by linarith [neg_abs_le c]
  have hac : c - a ≤ 0 := by linarith [le_abs_self c]
  set u : ℝ → ℝ := fun x ↦ Real.exp ((c + a) * min x 0) with hudef
  set v : ℝ → ℝ := fun x ↦ 1 - Real.exp ((c - a) * max x 0) with hvdef
  have hu : Monotone u := fun x y hxy ↦
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (min_le_min hxy le_rfl) hca)
  have hv : Monotone v := fun x y hxy ↦ by
    simp only [hvdef]
    apply sub_le_sub_left
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonpos_left (max_le_max hxy le_rfl) hac)
  have bu : ∀ x, u x ∈ Icc 0 1 := fun x ↦
    ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.2
      (mul_nonpos_of_nonneg_of_nonpos hca (min_le_right _ _))⟩
  have bv : ∀ x, v x ∈ Icc 0 1 := fun x ↦
    ⟨sub_nonneg.2 (Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg hac (le_max_right _ _))),
      by simp only [hvdef]; linarith [Real.exp_pos ((c - a) * max x 0)]⟩
  have heq : damp a c = fun x ↦ u x + -v x := by
    funext x
    simp only [damp, hudef, hvdef]
    rcases le_total x 0 with h | h
    · rw [min_eq_left h, max_eq_right h, abs_of_nonpos h, mul_zero, Real.exp_zero]
      ring_nf
    · rw [min_eq_right h, max_eq_left h, abs_of_nonneg h, mul_zero, Real.exp_zero]
      ring_nf
  rw [heq]
  calc eVariationOn (fun x ↦ u x + -v x) s ≤ eVariationOn u s + eVariationOn v s := by
        refine (eVariationOn_add_le _ _ s).trans ?_
        rw [eVariationOn_neg v]
    _ ≤ ENNReal.ofReal 1 + ENNReal.ofReal 1 :=
        add_le_add (hu.eVariationOn_le_of_mem_Icc bu s) (hv.eVariationOn_le_of_mem_Icc bv s)
    _ = 2 := by rw [ENNReal.ofReal_one]; norm_num

theorem mul_exp_eq_damp_smul (c x : ℝ) :
    F x * (Real.exp (c * x) : ℂ) = damp ((1 + 2 * δ₀) * π) c x • weighted F δ₀ x := by
  unfold damp weighted
  rw [Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, mul_comm (F x)]
  congr 3
  ring

/-- E1: for `|c| ≤ a`, `x ↦ F(x) e^{cx}` is integrable. -/
theorem IsTestFunction.integrable_mul_exp (hF : IsTestFunction F δ₀) {c : ℝ}
    (hc : |c| ≤ (1 + 2 * δ₀) * π) : Integrable fun x ↦ F x * (Real.exp (c * x) : ℂ) := by
  refine hF.integrable.norm.mono' (hF.aestronglyMeasurable.mul (by fun_prop :
    Continuous fun x : ℝ ↦ (Real.exp (c * x) : ℂ)).aestronglyMeasurable)
    (Eventually.of_forall fun x ↦ ?_)
  rw [mul_exp_eq_damp_smul (δ₀ := δ₀), norm_smul, Real.norm_of_nonneg (damp_pos _ _ _).le]
  calc damp ((1 + 2 * δ₀) * π) c x * ‖weighted F δ₀ x‖ ≤ 1 * ‖weighted F δ₀ x‖ :=
        mul_le_mul_of_nonneg_right (damp_le_one hc x) (norm_nonneg _)
    _ = ‖(Real.exp ((1 + 2 * δ₀) * π * |x|) : ℂ) * F x‖ := one_mul _

/-- E1: for `|c| ≤ a`, the variation of `x ↦ F(x) e^{cx}` is bounded uniformly in `c`. -/
theorem IsTestFunction.eVariationOn_mul_exp_le (hF : IsTestFunction F δ₀) {c : ℝ}
    (hc : |c| ≤ (1 + 2 * δ₀) * π) :
    eVariationOn (fun x ↦ F x * (Real.exp (c * x) : ℂ)) univ ≤
      ENNReal.ofReal ((eVariationOn (weighted F δ₀) univ).toReal +
        (‖weighted F δ₀ 0‖ + (eVariationOn (weighted F δ₀) univ).toReal) * 2) := by
  have h : (fun x ↦ F x * (Real.exp (c * x) : ℂ)) =
      fun x ↦ damp ((1 + 2 * δ₀) * π) c x • weighted F δ₀ x :=
    funext fun x ↦ mul_exp_eq_damp_smul c x
  rw [h]
  have h1 := eVariationOn_smul_le_ofReal (C := 1)
    (D := ‖weighted F δ₀ 0‖ + (eVariationOn (weighted F δ₀) univ).toReal) (A := 2)
    (B := (eVariationOn (weighted F δ₀) univ).toReal) (s := univ)
    (f := damp ((1 + 2 * δ₀) * π) c) (g := weighted F δ₀)
    (fun x _ ↦ by rw [abs_of_pos (damp_pos _ _ _)]; exact damp_le_one hc x)
    (fun x _ ↦ hF.norm_weighted_le x)
    (by rw [show ENNReal.ofReal 2 = 2 by norm_num]; exact eVariationOn_damp_le hc univ)
    (ENNReal.ofReal_toReal hF.boundedVariation).ge zero_le_one (by positivity) zero_le_two
    ENNReal.toReal_nonneg
  rwa [one_mul] at h1

theorem IsTestFunction.boundedVariationOn_mul_exp (hF : IsTestFunction F δ₀) {c : ℝ}
    (hc : |c| ≤ (1 + 2 * δ₀) * π) :
    BoundedVariationOn (fun x ↦ F x * (Real.exp (c * x) : ℂ)) univ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hF.eVariationOn_mul_exp_le hc)

theorem IsTestFunction.abs_zero_le (hF : IsTestFunction F δ₀) : |(0 : ℝ)| ≤ (1 + 2 * δ₀) * π := by
  rw [abs_zero]; have := hF.pos; positivity

/-- `F` is integrable. -/
theorem IsTestFunction.integrable_self (hF : IsTestFunction F δ₀) : Integrable F := by
  simpa using hF.integrable_mul_exp hF.abs_zero_le

/-- `F` has bounded variation on `ℝ`. -/
theorem IsTestFunction.boundedVariationOn_self (hF : IsTestFunction F δ₀) :
    BoundedVariationOn F univ := by
  simpa using hF.boundedVariationOn_mul_exp hF.abs_zero_le

theorem norm_mul_exp_le {c : ℝ} (hc : |c| ≤ (1 + 2 * δ₀) * π) (x : ℝ) :
    ‖F x * (Real.exp (c * x) : ℂ)‖ ≤ ‖weighted F δ₀ x‖ := by
  rw [mul_exp_eq_damp_smul (δ₀ := δ₀), norm_smul, Real.norm_of_nonneg (damp_pos _ _ _).le]
  calc damp ((1 + 2 * δ₀) * π) c x * ‖weighted F δ₀ x‖ ≤ 1 * ‖weighted F δ₀ x‖ :=
        mul_le_mul_of_nonneg_right (damp_le_one hc x) (norm_nonneg _)
    _ = ‖weighted F δ₀ x‖ := one_mul _

/-! ### E2: `Φ` as a Fourier transform, and holomorphy -/

/-- E2: `Φ(σ + it)` is the Fourier transform of `x ↦ F(x) e^{(1-2σ)πx}` at `t`. -/
theorem Phi_eq_fourier (F : ℝ → ℂ) (σ t : ℝ) :
    Phi F (σ + t * I) = 𝓕 (fun x ↦ F x * (Real.exp ((1 - 2 * σ) * π * x) : ℂ)) t := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  unfold Phi
  congr 1
  ext x
  have hexp : -((σ : ℂ) + t * I - 1 / 2) * (2 * π * x) =
      (((1 - 2 * σ) * π * x : ℝ) : ℂ) + ((-2 * π * x * t : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [hexp, Complex.exp_add, smul_eq_mul, Complex.ofReal_exp]
  ring

/-- E2: on the critical line, `Φ` is the Fourier transform of `F`. -/
theorem Phi_half_add_mul_I (F : ℝ → ℂ) (t : ℝ) : Phi F (1 / 2 + t * I) = 𝓕 F t := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  unfold Phi
  congr 1
  ext x
  rw [smul_eq_mul, mul_comm]
  congr 2
  push_cast
  ring

/-- E2: `Φ(1 - s)` is the `Φ` of `x ↦ F(-x)`. -/
theorem Phi_one_sub (F : ℝ → ℂ) (s : ℂ) : Phi F (1 - s) = Phi (fun x ↦ F (-x)) s := by
  simp only [Phi]
  rw [← integral_neg_eq_self (fun x ↦ F (-x) * Complex.exp (-(s - 1 / 2) * (2 * π * x)))]
  congr 1
  ext x
  simp only [neg_neg]
  congr 2
  push_cast
  ring

/-- E2: `Φ` is holomorphic on the strip `-δ₀ < σ < 1 + δ₀`. -/
theorem IsTestFunction.differentiableOn_Phi (hF : IsTestFunction F δ₀) :
    DifferentiableOn ℂ (Phi F) {s | -δ₀ < s.re ∧ s.re < 1 + δ₀} := by
  intro s₀ hs₀
  obtain ⟨h1, h2⟩ := hs₀
  set η := min (s₀.re + δ₀) (1 + δ₀ - s₀.re) / 2 with hηdef
  have hm1 : min (s₀.re + δ₀) (1 + δ₀ - s₀.re) ≤ s₀.re + δ₀ := min_le_left _ _
  have hm2 : min (s₀.re + δ₀) (1 + δ₀ - s₀.re) ≤ 1 + δ₀ - s₀.re := min_le_right _ _
  have hη : 0 < η := div_pos (lt_min (by linarith) (by linarith)) two_pos
  have hball : ∀ s ∈ Metric.ball s₀ η, |s.re - 1 / 2| ≤ 1 / 2 + δ₀ - η := by
    intro s hs
    rw [Metric.mem_ball, Complex.dist_eq] at hs
    have hre : |s.re - s₀.re| < η := by
      calc |s.re - s₀.re| = |(s - s₀).re| := by rw [Complex.sub_re]
        _ ≤ ‖s - s₀‖ := Complex.abs_re_le_norm _
        _ < η := hs
    rw [abs_lt] at hre
    rw [abs_le]
    constructor <;> linarith
  set Fs : ℂ → ℝ → ℂ := fun s x ↦ F x * Complex.exp (-(s - 1 / 2) * (2 * π * x)) with hFs
  set Fs' : ℂ → ℝ → ℂ := fun s x ↦ F x * (Complex.exp (-(s - 1 / 2) * (2 * π * x)) *
    (-(2 * π * x))) with hFs'
  have hnorm : ∀ (s : ℂ) (x : ℝ), ‖Complex.exp (-(s - 1 / 2) * (2 * π * x))‖ =
      Real.exp (-(s.re - 1 / 2) * (2 * π * x)) := by
    intro s x
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re, Complex.sub_re]
  have hmeas : ∀ s, AEStronglyMeasurable (Fs s) volume := fun s ↦
    hF.aestronglyMeasurable.mul (by fun_prop)
  have hmeas' : AEStronglyMeasurable (Fs' s₀) volume :=
    hF.aestronglyMeasurable.mul (by fun_prop)
  have hc₀ : |(1 - 2 * s₀.re) * π| ≤ (1 + 2 * δ₀) * π := by
    rw [abs_mul, abs_of_pos pi_pos]
    apply mul_le_mul_of_nonneg_right _ pi_pos.le
    rw [abs_le]; constructor <;> linarith
  have hint : Integrable (Fs s₀) := by
    refine (hF.integrable_mul_exp hc₀).mono (hmeas s₀) (Eventually.of_forall fun x ↦ ?_)
    simp only [hFs]
    rw [norm_mul, norm_mul, hnorm, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    apply le_of_eq
    congr 2
    ring
  have hbound : ∀ x : ℝ, ∀ s ∈ Metric.ball s₀ η, ‖Fs' s x‖ ≤ ‖weighted F δ₀ x‖ / η := by
    intro x s hs
    have hσ := hball s hs
    have hFx : ‖F x‖ = Real.exp (-((1 + 2 * δ₀) * π * |x|)) * ‖weighted F δ₀ x‖ := by
      rw [eq_exp_mul_weighted (F := F) (δ₀ := δ₀) x, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (Real.exp_pos _).le]
    have he : -(s.re - 1 / 2) * (2 * π * x) ≤ (1 / 2 + δ₀ - η) * (2 * π * |x|) := by
      have h3 : -(s.re - 1 / 2) * x ≤ |s.re - 1 / 2| * |x| := by
        rw [← abs_mul, neg_mul]; exact neg_le_abs _
      have h4 : |s.re - 1 / 2| * |x| ≤ (1 / 2 + δ₀ - η) * |x| :=
        mul_le_mul_of_nonneg_right hσ (abs_nonneg x)
      nlinarith [pi_pos]
    have hy : 2 * π * η * |x| * Real.exp (-(2 * π * η * |x|)) ≤ 1 := by
      have h5 := Real.add_one_le_exp (2 * π * η * |x|)
      calc 2 * π * η * |x| * Real.exp (-(2 * π * η * |x|))
          ≤ Real.exp (2 * π * η * |x|) * Real.exp (-(2 * π * η * |x|)) :=
            mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    simp only [hFs']
    rw [norm_mul, norm_mul, hnorm, norm_neg, hFx]
    have hx2 : ‖(2 * π * x : ℂ)‖ = 2 * π * |x| := by
      rw [show (2 * π * x : ℂ) = ((2 * π * x : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
    rw [hx2]
    calc Real.exp (-((1 + 2 * δ₀) * π * |x|)) * ‖weighted F δ₀ x‖ *
          (Real.exp (-(s.re - 1 / 2) * (2 * π * x)) * (2 * π * |x|))
        = ‖weighted F δ₀ x‖ * (Real.exp (-((1 + 2 * δ₀) * π * |x|) +
            -(s.re - 1 / 2) * (2 * π * x)) * (2 * π * |x|)) := by
          rw [Real.exp_add]; ring
      _ ≤ ‖weighted F δ₀ x‖ * (Real.exp (-(2 * π * η * |x|)) * (2 * π * |x|)) := by
          gcongr
          nlinarith [pi_pos, abs_nonneg x]
      _ = ‖weighted F δ₀ x‖ / η * (2 * π * η * |x| * Real.exp (-(2 * π * η * |x|))) := by
          field_simp
      _ ≤ ‖weighted F δ₀ x‖ / η * 1 := by gcongr
      _ = ‖weighted F δ₀ x‖ / η := mul_one _
  have hdiff : ∀ x : ℝ, ∀ s ∈ Metric.ball s₀ η, HasDerivAt (Fs · x) (Fs' s x) s := by
    intro x s _
    have h0 : HasDerivAt (fun y : ℂ ↦ y - 1 / 2) 1 s := (hasDerivAt_id' s).sub_const _
    have h3 : HasDerivAt (fun y : ℂ ↦ -(y - 1 / 2)) (-1) s := h0.neg
    have h1 : HasDerivAt (fun y : ℂ ↦ -(y - 1 / 2) * (2 * π * x)) (-(2 * π * x)) s :=
      (h3.mul_const (2 * π * x : ℂ)).congr_deriv (by ring)
    exact h1.cexp.const_mul (F x)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (F := Fs) (F' := Fs')
    (x₀ := s₀) (bound := fun x ↦ ‖weighted F δ₀ x‖ / η) (Metric.ball_mem_nhds s₀ hη)
    (Eventually.of_forall hmeas) hint hmeas' (ae_of_all _ hbound)
    (hF.integrable.norm.div_const η) (ae_of_all _ hdiff)
  exact h.2.differentiableAt.differentiableWithinAt

/-! ### E3: `Φ(s) ≪ 1/(|t| + 1)` -/

theorem norm_fourier_le_integral_norm (g : ℝ → ℂ) (t : ℝ) : ‖𝓕 g t‖ ≤ ∫ x, ‖g x‖ := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  ext x
  rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- E3: `Φ(s) ≪ 1/(|t| + 1)` uniformly in the closed strip `-δ₀ ≤ σ ≤ 1 + δ₀`. -/
theorem IsTestFunction.exists_norm_Phi_le (hF : IsTestFunction F δ₀) :
    ∃ C, ∀ s : ℂ, s.re ∈ Set.Icc (-δ₀) (1 + δ₀) → ‖Phi F s‖ ≤ C / (|s.im| + 1) := by
  set V := (eVariationOn (weighted F δ₀) univ).toReal with hVdef
  set S := ‖weighted F δ₀ 0‖ + V with hSdef
  set N := ∫ x, ‖weighted F δ₀ x‖ with hNdef
  set K := π⁻¹ * 2⁻¹ * (V + S * 2) with hKdef
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  have hS0 : 0 ≤ S := by positivity
  have hN0 : 0 ≤ N := integral_nonneg fun _ ↦ norm_nonneg _
  have hK0 : 0 ≤ K := by positivity
  refine ⟨2 * (N + K), fun s hs ↦ ?_⟩
  have hc : |(1 - 2 * s.re) * π| ≤ (1 + 2 * δ₀) * π := by
    rw [abs_mul, abs_of_pos pi_pos]
    apply mul_le_mul_of_nonneg_right _ pi_pos.le
    rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
  have hΦ := Phi_eq_fourier F s.re s.im
  rw [Complex.re_add_im] at hΦ
  rw [hΦ]
  set g : ℝ → ℂ := fun x ↦ F x * (Real.exp ((1 - 2 * s.re) * π * x) : ℂ) with hgdef
  have hgi : Integrable g := hF.integrable_mul_exp hc
  have hb1 : ‖𝓕 g s.im‖ ≤ N :=
    (norm_fourier_le_integral_norm g s.im).trans
      (integral_mono hgi.norm hF.integrable.norm fun x ↦ norm_mul_exp_le hc x)
  have ht1 : 0 < |s.im| + 1 := by positivity
  rcases le_or_gt |s.im| 1 with ht | ht
  · calc ‖𝓕 g s.im‖ ≤ N := hb1
      _ ≤ 2 * (N + K) / (|s.im| + 1) := by
          rw [le_div_iff₀ ht1]; nlinarith [abs_nonneg s.im]
  · have hne : s.im ≠ 0 := by intro h; rw [h, abs_zero] at ht; linarith
    have h2 := FourierTransform.fourier_bounded_variation hgi
      (hF.boundedVariationOn_mul_exp hc) hne
    have hvar : (eVariationOn g univ).toReal ≤ V + S * 2 :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) (hF.eVariationOn_mul_exp_le hc)
    have hpos : 0 < |s.im| := by linarith
    calc ‖𝓕 g s.im‖ ≤ |s.im|⁻¹ * (π⁻¹ * 2⁻¹) * (eVariationOn g univ).toReal := h2
      _ ≤ |s.im|⁻¹ * (π⁻¹ * 2⁻¹) * (V + S * 2) := by gcongr
      _ = K / |s.im| := by rw [hKdef]; field_simp
      _ ≤ 2 * (N + K) / (|s.im| + 1) := by
          rw [div_le_div_iff₀ hpos ht1]
          nlinarith

/-! ### E0: Lipschitz functions of compact support -/

theorem abs_exp_sub_exp_le {u v c : ℝ} (hu : u ≤ c) (hv : v ≤ c) :
    |Real.exp u - Real.exp v| ≤ Real.exp c * |u - v| := by
  wlog huv : u ≤ v generalizing u v
  · rw [abs_sub_comm, abs_sub_comm u]
    exact this hv hu (not_le.1 huv).le
  rw [abs_of_nonpos (by linarith [Real.exp_le_exp.2 huv]), abs_of_nonpos (by linarith)]
  have h1 : 1 - Real.exp (u - v) ≤ v - u := by linarith [Real.add_one_le_exp (u - v)]
  have h2 : Real.exp u = Real.exp v * Real.exp (u - v) := by rw [← Real.exp_add]; ring_nf
  calc -(Real.exp u - Real.exp v) = Real.exp v * (1 - Real.exp (u - v)) := by rw [h2]; ring
    _ ≤ Real.exp v * (v - u) := mul_le_mul_of_nonneg_left h1 (Real.exp_pos v).le
    _ ≤ Real.exp c * (v - u) := mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hv) (by linarith)
    _ = Real.exp c * -(u - v) := by ring

/-- A function vanishing for `|x| ≥ R` has the same variation on `ℝ` as on `[-R, R]`. -/
theorem eVariationOn_univ_le_of_eq_zero {G : ℝ → ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hG : ∀ x, R ≤ |x| → G x = 0) : eVariationOn G univ ≤ eVariationOn G (Icc (-R) R) := by
  set φ : ℝ → ℝ := fun x ↦ max (-R) (min R x) with hφ
  have hGφ : G ∘ φ = G := by
    funext x
    simp only [Function.comp, hφ]
    rcases le_total x (-R) with h | h
    · rw [min_eq_right (by linarith), max_eq_left h,
        hG (-R) (by rw [abs_neg, abs_of_nonneg hR]),
        hG x (by rw [abs_of_nonpos (by linarith)]; linarith)]
    · rcases le_total x R with h' | h'
      · rw [min_eq_right h', max_eq_right h]
      · rw [min_eq_left h', max_eq_right (by linarith), hG R (by rw [abs_of_nonneg hR]),
          hG x (by rw [abs_of_nonneg (by linarith)]; linarith)]
  calc eVariationOn G univ = eVariationOn (G ∘ φ) univ := by rw [hGφ]
    _ ≤ eVariationOn G (Icc (-R) R) :=
        eVariationOn.comp_le_of_monotoneOn G φ
          (fun x _ y _ hxy ↦ max_le_max le_rfl (min_le_min le_rfl hxy))
          (fun x _ ↦ ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩)

/-- E0: continuous, Lipschitz, compactly supported functions are test functions for every `δ₀ > 0`
(this is the case needed in Proposition 2.2 of the Mertens note). -/
theorem IsTestFunction.of_lipschitzWith {K : NNReal} (hL : LipschitzWith K F)
    (hc : HasCompactSupport F) (hδ₀ : 0 < δ₀) : IsTestFunction F δ₀ := by
  set a := (1 + 2 * δ₀) * π with ha
  have ha0 : 0 ≤ a := by positivity
  obtain ⟨R, hR0, hR⟩ := hc.exists_pos_le_norm
  have hR' : ∀ x : ℝ, R ≤ |x| → F x = 0 := fun x hx ↦ hR x (by rwa [Real.norm_eq_abs])
  obtain ⟨M, hM⟩ := hL.continuous.bounded_above_of_compact_support hc
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hWc : Continuous fun x ↦ (Real.exp (a * |x|) : ℂ) * F x :=
    (Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul continuous_abs))).mul hL.continuous
  refine ⟨hδ₀, hWc.integrable_of_hasCompactSupport hc.mul_left, ?_, ?_, ?_⟩
  · -- bounded variation
    set C : ℝ := Real.exp (a * R) * K + M * (a * Real.exp (a * R)) with hC
    have hC0 : 0 ≤ C := by positivity
    have hlip : LipschitzOnWith C.toNNReal (fun x ↦ (Real.exp (a * |x|) : ℂ) * F x)
        (Icc (-R) R) := by
      refine LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_
      rw [Real.coe_toNNReal _ hC0]
      have hxR : |x| ≤ R := abs_le.2 hx
      have hyR : |y| ≤ R := abs_le.2 hy
      have he : |Real.exp (a * |x|) - Real.exp (a * |y|)| ≤ a * Real.exp (a * R) * |x - y| := by
        calc |Real.exp (a * |x|) - Real.exp (a * |y|)|
            ≤ Real.exp (a * R) * abs (a * |x| - a * |y|) :=
              abs_exp_sub_exp_le (mul_le_mul_of_nonneg_left hxR ha0)
                (mul_le_mul_of_nonneg_left hyR ha0)
          _ = Real.exp (a * R) * (a * abs (|x| - |y|)) := by
              rw [← mul_sub, abs_mul, abs_of_nonneg ha0]
          _ ≤ Real.exp (a * R) * (a * |x - y|) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (abs_abs_sub_abs_le x y) ha0)
                (Real.exp_pos _).le
          _ = a * Real.exp (a * R) * |x - y| := by ring
      have hex : Real.exp (a * |x|) ≤ Real.exp (a * R) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hxR ha0)
      have hFL : ‖F x - F y‖ ≤ K * |x - y| := by
        have := hL.norm_sub_le x y
        rwa [Real.norm_eq_abs] at this
      rw [dist_eq_norm, Real.dist_eq]
      calc ‖(Real.exp (a * |x|) : ℂ) * F x - (Real.exp (a * |y|) : ℂ) * F y‖
          = ‖(Real.exp (a * |x|) : ℂ) * (F x - F y) +
              ((Real.exp (a * |x|) - Real.exp (a * |y|) : ℝ) : ℂ) * F y‖ := by
            congr 1
            push_cast
            ring
        _ ≤ Real.exp (a * |x|) * ‖F x - F y‖ +
              |Real.exp (a * |x|) - Real.exp (a * |y|)| * ‖F y‖ := by
            refine (norm_add_le _ _).trans (le_of_eq ?_)
            rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
              Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        _ ≤ Real.exp (a * R) * (K * |x - y|) + (a * Real.exp (a * R) * |x - y|) * M := by
            gcongr
            exact hM y
        _ = C * |x - y| := by rw [hC]; ring
    have h2 := hlip.comp_eVariationOn_le (g := id) (s := Icc (-R) R) (mapsTo_id _)
    have h3 : eVariationOn (id : ℝ → ℝ) (Icc (-R) R) ≤ ENNReal.ofReal (R - -R) :=
      monotoneOn_id.eVariationOn_le_of_mapsTo (fun x hx ↦ hx.1) (fun x hx ↦ hx.2)
    have hvar := eVariationOn_univ_le_of_eq_zero (G := fun x ↦ (Real.exp (a * |x|) : ℂ) * F x)
      hR0.le (fun x hx ↦ by simp only [hR' x hx, mul_zero])
    unfold BoundedVariationOn
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top)
      (hvar.trans (h2.trans (by gcongr)))
  · -- normalized
    intro x
    have h := hL.continuous.tendsto x
    rw [leftLim_eq_of_tendsto (NeBot.ne inferInstance) (h.mono_left nhdsWithin_le_nhds),
      rightLim_eq_of_tendsto (NeBot.ne inferInstance) (h.mono_left nhdsWithin_le_nhds)]
    ring
  · -- `F(x) + F(-x) - 2F(0) = O(x)`
    refine Asymptotics.IsBigO.of_bound (2 * K) (Eventually.of_forall fun x ↦ ?_)
    have h1 := hL.norm_sub_le x 0
    have h2 := hL.norm_sub_le (-x) 0
    calc ‖F x + F (-x) - 2 * F 0‖ = ‖(F x - F 0) + (F (-x) - F 0)‖ := by congr 1; ring
      _ ≤ ‖F x - F 0‖ + ‖F (-x) - F 0‖ := norm_add_le _ _
      _ ≤ K * ‖x - 0‖ + K * ‖-x - 0‖ := add_le_add h1 h2
      _ = 2 * K * ‖x‖ := by rw [sub_zero, sub_zero, norm_neg]; ring

end WeilExplicitFormula
