/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Harald Helfgott
-/
module

public import Mathlib.NumberTheory.WeilExplicitFormula.TestFunction
public import Mathlib.Analysis.Normed.Group.Tannery

/-! # Sums of translates of a function of bounded variation

For `G ∈ L¹(ℝ)` of bounded variation on `ℝ`, nonnegative summable weights `aₙ` and shifts `Lₙ`,
the function `S(x) = ∑ aₙ G(x - Lₙ)` (`translateSum`) is integrable and of bounded variation,
with `Var S ≤ (∑ aₙ) Var G`; its Fourier transform is `Ŝ(t) = (∑ aₙ e(-Lₙ t)) Ĝ(t)`; and `S` is
normalized (`S(x) = (S(x+) + S(x-))/2`) wherever `G` is normalized everywhere.

This is what Montgomery–Vaughan use, in the proof of their Theorem 12.13, for the function
`H(x) = -∑ Λ(n) n^{-1/2} (F(x - log n / 2π) + F(-x + log n / 2π)) e^{-(1/2 + δ₁)2πx}`
(part F of the blueprint).

## AI usage

This file was written by Claude (Anthropic) in November 2026. It compiles, but has not been
reviewed by a human.
-/

@[expose] public section

open Real Complex Filter Topology MeasureTheory Set Function
open scoped FourierTransform

noncomputable section

namespace WeilExplicitFormula

/-! ### Generalities -/

/-- A series of integrable functions whose `L¹` norms are summable, and which converges at every
point, has an integrable sum. -/
theorem integrable_tsum_of_summable_integral_norm {f : ℕ → ℝ → ℂ} (hf : ∀ n, Integrable (f n))
    (hs : Summable fun n ↦ ∫ x, ‖f n x‖) (hp : ∀ x, Summable fun n ↦ f n x) :
    Integrable fun x ↦ ∑' n, f n x := by
  refine ⟨aestronglyMeasurable_of_tendsto_ae atTop
    (fun N ↦ (integrable_finsetSum (Finset.range N) fun n _ ↦ hf n).aestronglyMeasurable)
    (ae_of_all _ fun x ↦ (hp x).hasSum.tendsto_sum_nat), ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  calc ∫⁻ x, ‖∑' n, f n x‖ₑ ≤ ∫⁻ x, ∑' n, ‖f n x‖ₑ :=
        lintegral_mono fun x ↦ enorm_tsum_le_tsum_enorm
    _ = ∑' n, ∫⁻ x, ‖f n x‖ₑ := lintegral_tsum fun n ↦ (hf n).aestronglyMeasurable.enorm
    _ = ∑' n, ENNReal.ofReal (∫ x, ‖f n x‖) := by
        congr 1
        ext n
        exact (ofReal_integral_norm_eq_lintegral_enorm (hf n)).symm
    _ = ENNReal.ofReal (∑' n, ∫ x, ‖f n x‖) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun n ↦ integral_nonneg fun x ↦ norm_nonneg _) hs).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- A bound for a function of bounded variation on `ℝ`. -/
def bvBound (G : ℝ → ℂ) : ℝ := ‖G 0‖ + (eVariationOn G univ).toReal

theorem norm_le_bvBound {G : ℝ → ℂ} (hG : BoundedVariationOn G univ) (y : ℝ) :
    ‖G y‖ ≤ bvBound G := by
  have h : dist (G y) (G 0) ≤ (eVariationOn G univ).toReal :=
    hG.dist_le (mem_univ y) (mem_univ 0)
  rw [dist_eq_norm] at h
  have := norm_sub_norm_le (G y) (G 0)
  unfold bvBound
  linarith

theorem norm_rightLim_le_bvBound {G : ℝ → ℂ} (hG : BoundedVariationOn G univ) (y : ℝ) :
    ‖rightLim G y‖ ≤ bvBound G :=
  le_of_tendsto (hG.tendsto_rightLim y).norm (Eventually.of_forall fun z ↦ norm_le_bvBound hG z)

theorem norm_leftLim_le_bvBound {G : ℝ → ℂ} (hG : BoundedVariationOn G univ) (y : ℝ) :
    ‖leftLim G y‖ ≤ bvBound G :=
  le_of_tendsto (hG.tendsto_leftLim y).norm (Eventually.of_forall fun z ↦ norm_le_bvBound hG z)

/-- If `f` has limits `r` and `l` on the right and on the left of `y`, and `f(y) = (r + l)/2`,
then `f` is normalized at `y`. -/
theorem eq_rightLim_add_leftLim_div_two {f : ℝ → ℂ} {y : ℝ} {r l : ℂ}
    (hr : Tendsto f (𝓝[>] y) (𝓝 r)) (hl : Tendsto f (𝓝[<] y) (𝓝 l)) (h : f y = (r + l) / 2) :
    f y = (rightLim f y + leftLim f y) / 2 := by
  rw [rightLim_eq_of_tendsto (NeBot.ne inferInstance) hr,
    leftLim_eq_of_tendsto (NeBot.ne inferInstance) hl, h]

theorem tendsto_sub_right_nhdsGT (x c : ℝ) :
    Tendsto (fun y ↦ y - c) (𝓝[>] x) (𝓝[>] (x - c)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (((continuous_sub_right c).tendsto x).mono_left nhdsWithin_le_nhds)
    (eventually_nhdsWithin_of_forall fun y hy ↦ by
      simp only [mem_Ioi] at hy ⊢
      linarith)

theorem tendsto_sub_right_nhdsLT (x c : ℝ) :
    Tendsto (fun y ↦ y - c) (𝓝[<] x) (𝓝[<] (x - c)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (((continuous_sub_right c).tendsto x).mono_left nhdsWithin_le_nhds)
    (eventually_nhdsWithin_of_forall fun y hy ↦ by
      simp only [mem_Iio] at hy ⊢
      linarith)

theorem tendsto_neg_nhdsGT' (x : ℝ) : Tendsto (fun y : ℝ ↦ -y) (𝓝[>] x) (𝓝[<] (-x)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    ((continuous_neg.tendsto x).mono_left nhdsWithin_le_nhds)
    (eventually_nhdsWithin_of_forall fun y hy ↦ by
      simp only [mem_Ioi, mem_Iio] at hy ⊢
      linarith)

theorem tendsto_neg_nhdsLT' (x : ℝ) : Tendsto (fun y : ℝ ↦ -y) (𝓝[<] x) (𝓝[>] (-x)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    ((continuous_neg.tendsto x).mono_left nhdsWithin_le_nhds)
    (eventually_nhdsWithin_of_forall fun y hy ↦ by
      simp only [mem_Ioi, mem_Iio] at hy ⊢
      linarith)

/-! ### Variation -/

theorem eVariationOn_finset_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℂ) (t : Set ℝ) :
    eVariationOn (fun x ↦ ∑ i ∈ s, f i x) t ≤ ∑ i ∈ s, eVariationOn (f i) t := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact (eVariationOn_const (0 : ℂ) t).le
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (eVariationOn_add_le _ _ _).trans (add_le_add le_rfl ih)

theorem eVariationOn_const_mul (c : ℂ) (g : ℝ → ℂ) (s : Set ℝ) :
    eVariationOn (fun x ↦ c * g x) s = ‖c‖ₑ * eVariationOn g s := by
  simp only [eVariationOn, ENNReal.mul_iSup, Finset.mul_sum, edist_eq_enorm_sub, ← mul_sub,
    enorm_mul]

theorem eVariationOn_comp_sub_right (G : ℝ → ℂ) (c : ℝ) :
    eVariationOn (fun x ↦ G (x - c)) univ = eVariationOn G univ := by
  have h := eVariationOn.comp_eq_of_monotoneOn G (fun x ↦ x - c) (t := univ)
    (fun x _ y _ hxy ↦ by simp only; linarith)
  rw [image_univ_of_surjective (fun y ↦ ⟨y + c, by ring⟩)] at h
  exact h

theorem eVariationOn_comp_neg (G : ℝ → ℂ) :
    eVariationOn (fun x ↦ G (-x)) univ = eVariationOn G univ := by
  have h := eVariationOn.comp_eq_of_antitoneOn G (fun x ↦ -x) (t := univ)
    (fun x _ y _ hxy ↦ by simp only; linarith)
  rw [image_univ_of_surjective neg_surjective] at h
  exact h

/-! ### Sums of translates -/

section TranslateSum

variable {a L : ℕ → ℝ} {G : ℝ → ℂ}

/-- `∑ₙ aₙ G(x - Lₙ)`. -/
def translateSum (a L : ℕ → ℝ) (G : ℝ → ℂ) (x : ℝ) : ℂ := ∑' n, (a n : ℂ) * G (x - L n)

theorem norm_translateSum_term_le (ha : ∀ n, 0 ≤ a n) (hG : BoundedVariationOn G univ)
    (x : ℝ) (n : ℕ) : ‖(a n : ℂ) * G (x - L n)‖ ≤ a n * bvBound G := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (ha n)]
  exact mul_le_mul_of_nonneg_left (norm_le_bvBound hG _) (ha n)

theorem summable_translateSum (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hG : BoundedVariationOn G univ) (x : ℝ) : Summable fun n ↦ (a n : ℂ) * G (x - L n) :=
  Summable.of_norm_bounded (hs.mul_right (bvBound G)) (norm_translateSum_term_le ha hG x)

theorem integral_norm_translateSum_term (ha : ∀ n, 0 ≤ a n) (n : ℕ) :
    ∫ x, ‖(a n : ℂ) * G (x - L n)‖ = a n * ∫ x, ‖G x‖ := by
  simp_rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (ha n)]
  rw [integral_const_mul, integral_sub_right_eq_self (fun x ↦ ‖G x‖) (L n)]

theorem integrable_translateSum (ha : ∀ n, 0 ≤ a n) (hs : Summable a) (hGi : Integrable G)
    (hGv : BoundedVariationOn G univ) : Integrable (translateSum a L G) := by
  have hint : ∀ n, Integrable fun x ↦ (a n : ℂ) * G (x - L n) := fun n ↦
    (hGi.comp_sub_right (L n)).const_mul _
  refine integrable_tsum_of_summable_integral_norm hint ?_ (summable_translateSum ha hs hGv)
  simp_rw [integral_norm_translateSum_term ha]
  exact hs.mul_right _

theorem fourier_translateSum (ha : ∀ n, 0 ≤ a n) (hs : Summable a) (hGi : Integrable G)
    (t : ℝ) :
    𝓕 (translateSum a L G) t =
      (∑' n, (a n : ℂ) * cexp (↑(-2 * π * L n * t) * I)) * 𝓕 G t := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  have hen : ∀ x : ℝ, ‖cexp (↑(-2 * π * x * t) * I)‖ = 1 := fun x ↦
    Complex.norm_exp_ofReal_mul_I _
  have hint : ∀ n, Integrable fun x ↦
      cexp (↑(-2 * π * x * t) * I) • ((a n : ℂ) * G (x - L n)) := by
    intro n
    have h1 := (hGi.comp_sub_right (L n)).const_mul (a n : ℂ)
    refine h1.mono ((Continuous.aestronglyMeasurable (by fun_prop)).smul h1.aestronglyMeasurable)
      (Eventually.of_forall fun x ↦ ?_)
    rw [norm_smul, hen, one_mul]
  have hsum : Summable fun n ↦
      ∫ x, ‖cexp (↑(-2 * π * x * t) * I) • ((a n : ℂ) * G (x - L n))‖ := by
    simp_rw [norm_smul, hen, one_mul, integral_norm_translateSum_term ha]
    exact hs.mul_right _
  have hpt : ∀ x : ℝ, cexp (↑(-2 * π * x * t) * I) • translateSum a L G x =
      ∑' n, cexp (↑(-2 * π * x * t) * I) • ((a n : ℂ) * G (x - L n)) := by
    intro x
    simp only [translateSum, smul_eq_mul]
    exact tsum_mul_left.symm
  simp_rw [hpt]
  rw [← integral_tsum_of_summable_integral_norm hint hsum, ← tsum_mul_right]
  congr 1
  ext n
  rw [← integral_add_right_eq_self
    (fun x ↦ cexp (↑(-2 * π * x * t) * I) • ((a n : ℂ) * G (x - L n))) (L n)]
  simp only [add_sub_cancel_right, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  ext x
  rw [show (↑(-2 * π * (x + L n) * t) * I : ℂ) =
      ↑(-2 * π * L n * t) * I + ↑(-2 * π * x * t) * I by push_cast; ring, Complex.exp_add]
  ring

theorem eVariationOn_translateSum_le (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hGv : BoundedVariationOn G univ) :
    eVariationOn (translateSum a L G) univ ≤
      ENNReal.ofReal ((∑' n, a n) * (eVariationOn G univ).toReal) := by
  set V := (eVariationOn G univ).toReal with hV
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  have hVe : eVariationOn G univ = ENNReal.ofReal V := (ENNReal.ofReal_toReal hGv).symm
  have hlim : ∀ x ∈ (univ : Set ℝ), Tendsto
      (fun N ↦ ∑ n ∈ Finset.range N, (a n : ℂ) * G (x - L n)) atTop
      (𝓝 (translateSum a L G x)) := fun x _ ↦
    (summable_translateSum ha hs hGv x).hasSum.tendsto_sum_nat
  have hbound : ∀ N, eVariationOn (fun x ↦ ∑ n ∈ Finset.range N, (a n : ℂ) * G (x - L n)) univ ≤
      ENNReal.ofReal ((∑' n, a n) * V) := by
    intro N
    calc _ ≤ ∑ n ∈ Finset.range N, eVariationOn (fun x ↦ (a n : ℂ) * G (x - L n)) univ :=
          eVariationOn_finset_sum_le _ _ _
      _ = ∑ n ∈ Finset.range N, ENNReal.ofReal (a n * V) := by
          refine Finset.sum_congr rfl fun n _ ↦ ?_
          rw [eVariationOn_const_mul, eVariationOn_comp_sub_right G (L n), hVe,
            ← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_of_nonneg (ha n),
            ← ENNReal.ofReal_mul (ha n)]
      _ = ENNReal.ofReal (∑ n ∈ Finset.range N, a n * V) :=
          (ENNReal.ofReal_sum_of_nonneg fun n _ ↦ mul_nonneg (ha n) hV0).symm
      _ ≤ ENNReal.ofReal ((∑' n, a n) * V) := by
          apply ENNReal.ofReal_le_ofReal
          rw [← Finset.sum_mul]
          exact mul_le_mul_of_nonneg_right (hs.sum_le_tsum _ fun n _ ↦ ha n) hV0
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨N, hN⟩ := (eVariationOn.lowerSemicontinuous_aux hlim hcon).exists
  exact absurd (hbound N) (not_le.2 hN)

theorem boundedVariationOn_translateSum (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hGv : BoundedVariationOn G univ) : BoundedVariationOn (translateSum a L G) univ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (eVariationOn_translateSum_le ha hs hGv)

theorem translateSum_eq_rightLim_add_leftLim (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hGv : BoundedVariationOn G univ) (hGn : ∀ y, G y = (rightLim G y + leftLim G y) / 2)
    (x : ℝ) :
    translateSum a L G x =
      (rightLim (translateSum a L G) x + leftLim (translateSum a L G) x) / 2 := by
  have hb : ∀ y n, ‖(a n : ℂ) * G (y - L n)‖ ≤ a n * bvBound G := fun y n ↦
    norm_translateSum_term_le ha hGv y n
  have hR : Tendsto (translateSum a L G) (𝓝[>] x)
      (𝓝 (∑' n, (a n : ℂ) * rightLim G (x - L n))) := by
    refine tendsto_tsum_of_dominated_convergence (hs.mul_right _) (fun n ↦ ?_)
      (Eventually.of_forall fun y n ↦ hb y n)
    exact ((hGv.tendsto_rightLim (x - L n)).comp (tendsto_sub_right_nhdsGT x (L n))).const_mul _
  have hL : Tendsto (translateSum a L G) (𝓝[<] x)
      (𝓝 (∑' n, (a n : ℂ) * leftLim G (x - L n))) := by
    refine tendsto_tsum_of_dominated_convergence (hs.mul_right _) (fun n ↦ ?_)
      (Eventually.of_forall fun y n ↦ hb y n)
    exact ((hGv.tendsto_leftLim (x - L n)).comp (tendsto_sub_right_nhdsLT x (L n))).const_mul _
  have hRs : Summable fun n ↦ (a n : ℂ) * rightLim G (x - L n) := by
    refine Summable.of_norm_bounded (hs.mul_right (bvBound G)) fun n ↦ ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (ha n)]
    exact mul_le_mul_of_nonneg_left (norm_rightLim_le_bvBound hGv _) (ha n)
  have hLs : Summable fun n ↦ (a n : ℂ) * leftLim G (x - L n) := by
    refine Summable.of_norm_bounded (hs.mul_right (bvBound G)) fun n ↦ ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (ha n)]
    exact mul_le_mul_of_nonneg_left (norm_leftLim_le_bvBound hGv _) (ha n)
  refine eq_rightLim_add_leftLim_div_two hR hL ?_
  rw [← hRs.tsum_add hLs, ← tsum_div_const]
  simp only [translateSum]
  congr 1
  ext n
  rw [hGn (x - L n)]
  ring

end TranslateSum

end WeilExplicitFormula
