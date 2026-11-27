/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Harald Helfgott
-/
module

public import Mathlib.NumberTheory.WeilExplicitFormula.CriticalLine
public import Mathlib.NumberTheory.WeilExplicitFormula.Rectangle
public import Mathlib.NumberTheory.WeilExplicitFormula.Xi
public import Mathlib.NumberTheory.LSeries.ZetaZeros
public import Mathlib.Analysis.Meromorphic.Order

/-! # The contour integrals in the proof of Weil's explicit formula

Parts G1, G3 and G4 of the blueprint for Montgomery–Vaughan, *Multiplicative Number Theory I*,
Theorem 12.13 with `q = 1`, taking the residue theorem on rectangles (`ResidueTheoremRectangle`,
the statement of IEANTN's `ContourIntegration.v1.residue_theorem_rectangle`) as a hypothesis.

* G1 (`IsTestFunction.zetaZeroesSum_eq_rectIntegral`): if `ζ(σ + iT₁) ≠ 0` for `0 ≤ σ ≤ 1`, the
  sum of `Φ(ρ)` over the non-trivial zeros with `|γ| ≤ T₁`, with multiplicity, is
  `(2πi)⁻¹ ∮ Φ ξ'/ξ` over the boundary of `[-δ₁, 1 + δ₁] × [-T₁, T₁]`.
* G3 (`IsTestFunction.rectIntegral_riemannXi_eq`): by `ξ'/ξ(1 - s) = -ξ'/ξ(s)` and (12.24), the
  two vertical sides together are
  `i ∫_{-T₁}^{T₁} (Φ(s) + Φ(1 - s)) (ζ'/ζ(s) + G(s)) dt`, `s = 1 + δ₁ + it`.
* G4 (`IsTestFunction.integral_gammaFactor_right_eq`): by the residue theorem, the integral of
  `G(s)(Φ(s) + Φ(1 - s))` over `σ = 1 + δ₁` is that over `σ = 1/2`, plus `2π(Φ(0) + Φ(1))`,
  plus the horizontal sides.

The sums over zeros are written with the vocabulary of IEANTN (`IEANTN/Vocabulary/Zeta.lean`),
copied verbatim: `zetaZeroesIn`, `zetaOrder`, `zetaZeroesSum`.

## AI usage

This file was written by Claude (Anthropic) in November 2026. It compiles, but has not been
reviewed by a human.
-/

@[expose] public section

open Real Complex Filter Topology Set Metric MeasureTheory
open scoped Interval FourierTransform ComplexConjugate

noncomputable section

namespace WeilExplicitFormula

variable {F : ℝ → ℂ} {δ₀ : ℝ}

/-! ### The vocabulary of IEANTN, copied verbatim -/

/-- `IEANTN.zetaZeroes`: the zero set of `ζ`. -/
def zetaZeroes : Set ℂ := {s : ℂ | riemannZeta s = 0}

/-- `IEANTN.zetaZeroesIn`: the zeroes of `ζ` in the rectangle `{Re s ∈ I, Im s ∈ J}`. -/
def zetaZeroesIn (I J : Set ℝ) : Set ℂ :=
  {s : ℂ | s.re ∈ I ∧ s.im ∈ J ∧ s ∈ zetaZeroes}

/-- `IEANTN.zetaOrder`: the order of vanishing of `ζ` at `s`, as an integer. -/
def zetaOrder (s : ℂ) : ℤ := (meromorphicOrderAt riemannZeta s).untopD 0

/-- `IEANTN.zetaZeroesSum`: the sum of `f` over the zeroes of `ζ` in a rectangle, counted with
multiplicity. -/
def zetaZeroesSum {α : Type*} [RCLike α] (I J : Set ℝ) (f : ℂ → α) : α :=
  ∑' ρ : zetaZeroesIn I J, f ρ * (zetaOrder ρ : ℤ)

theorem zetaOrder_eq {ρ : ℂ} (hρ : ρ ≠ 1) : zetaOrder ρ = analyticOrderNatAt riemannZeta ρ := by
  have hA : AnalyticAt ℂ riemannZeta ρ := analyticOn_riemannZeta ρ hρ
  unfold zetaOrder analyticOrderNatAt
  rw [hA.meromorphicOrderAt_eq]
  cases analyticOrderAt riemannZeta ρ with
  | top => simp
  | coe n =>
    simp only [ENat.map_coe, ENat.toNat_coe]
    rw [WithTop.untopD_coe]

theorem zetaZeroesIn_finite {I J : Set ℝ} {a b c d : ℝ} (hI : I ⊆ Icc a b) (hJ : J ⊆ Icc c d) :
    (zetaZeroesIn I J).Finite := by
  have hK : IsCompact (Icc a b ×ℂ Icc c d) :=
    Metric.isCompact_of_isClosed_isBounded (isClosed_Icc.reProdIm isClosed_Icc)
      (Metric.isBounded_Icc a b |>.reProdIm (Metric.isBounded_Icc c d))
  refine hK.inter_riemannZetaZeros_finite.subset ?_
  rintro s ⟨hsI, hsJ, hs0⟩
  exact ⟨mem_reProdIm.2 ⟨hI hsI, hJ hsJ⟩, mem_riemannZetaZeros.2 hs0⟩

theorem zetaZeroesSum_eq_sum {α : Type*} [RCLike α] {I J : Set ℝ} (h : (zetaZeroesIn I J).Finite)
    (f : ℂ → α) : zetaZeroesSum I J f = ∑ ρ ∈ h.toFinset, f ρ * (zetaOrder ρ : α) := by
  unfold zetaZeroesSum
  rw [tsum_subtype (zetaZeroesIn I J) (fun ρ ↦ f ρ * (zetaOrder ρ : α)),
    tsum_eq_sum (s := h.toFinset) (fun b hb ↦ Set.indicator_of_notMem (by simpa using hb) _)]
  exact Finset.sum_congr rfl fun b hb ↦ Set.indicator_of_mem (by simpa using hb) _

/-! ### Continuity on vertical lines -/

theorem isOpen_strip (δ₀ : ℝ) : IsOpen {s : ℂ | -δ₀ < s.re ∧ s.re < 1 + δ₀} :=
  (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)

theorem IsTestFunction.analyticAt_Phi (hF : IsTestFunction F δ₀) {s : ℂ} (h1 : -δ₀ < s.re)
    (h2 : s.re < 1 + δ₀) : AnalyticAt ℂ (Phi F) s :=
  hF.differentiableOn_Phi.analyticAt ((isOpen_strip δ₀).mem_nhds ⟨h1, h2⟩)

theorem continuous_vline (σ : ℝ) : Continuous fun y : ℝ ↦ (σ : ℂ) + y * I := by fun_prop

theorem continuous_one_sub_vline (σ : ℝ) : Continuous fun y : ℝ ↦ 1 - ((σ : ℂ) + y * I) := by
  fun_prop

theorem IsTestFunction.continuous_Phi_vline (hF : IsTestFunction F δ₀) {σ : ℝ} (h1 : -δ₀ < σ)
    (h2 : σ < 1 + δ₀) : Continuous fun y : ℝ ↦ Phi F (σ + y * I) :=
  continuous_iff_continuousAt.2 fun y ↦ ((hF.analyticAt_Phi (by simpa using h1)
    (by simpa using h2)).continuousAt).comp (continuous_vline σ).continuousAt

theorem IsTestFunction.continuous_Phi_one_sub_vline (hF : IsTestFunction F δ₀) {σ : ℝ}
    (h1 : -δ₀ < σ) (h2 : σ < 1 + δ₀) : Continuous fun y : ℝ ↦ Phi F (1 - (σ + y * I)) :=
  continuous_iff_continuousAt.2 fun y ↦ ((hF.analyticAt_Phi
    (by simp only [sub_re, one_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
      mul_one, sub_self, add_zero]; linarith)
    (by simp only [sub_re, one_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
      mul_one, sub_self, add_zero]; linarith)).continuousAt).comp
    (continuous_one_sub_vline σ).continuousAt

theorem continuousAt_logDeriv_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    ContinuousAt (logDeriv riemannZeta) s := by
  have hs1 : s ≠ 1 := fun h ↦ by rw [h, one_re] at hs; exact lt_irrefl 1 hs
  have hA : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta s hs1
  have : ContinuousAt (fun u ↦ deriv riemannZeta u / riemannZeta u) s :=
    hA.deriv.continuousAt.div hA.continuousAt (riemannZeta_ne_zero_of_one_lt_re hs)
  exact this

theorem differentiableAt_gammaFactor {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ gammaFactor s := by
  have hs0 := ne_zero_of_re_pos hs
  have hd : DifferentiableAt ℂ (fun u : ℂ ↦ digamma (u / 2)) s := by
    have h2 : 0 < (s / 2).re := by simp only [div_ofNat_re]; linarith
    exact (Complex.analyticOnNhd_digamma (s / 2) h2).differentiableAt.comp (x := s)
      (f := fun u : ℂ ↦ u / 2) (by fun_prop)
  have h1 : DifferentiableAt ℂ (fun u : ℂ ↦ 1 / u) s :=
    (differentiableAt_const (1 : ℂ)).div differentiableAt_id hs0
  have h2 : DifferentiableAt ℂ (fun u : ℂ ↦ 1 / (u - 1)) s :=
    (differentiableAt_const (1 : ℂ)).div (differentiableAt_id.sub_const 1) (sub_ne_zero.2 hs1)
  have h4 := ((h1.add h2).add (hd.div_const 2)).sub_const ((Real.log π : ℂ) / 2)
  unfold gammaFactor
  exact h4

theorem continuousAt_gammaFactor {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    ContinuousAt gammaFactor s :=
  (differentiableAt_gammaFactor hs hs1).continuousAt

/-- (12.24): `ξ'/ξ = G + ζ'/ζ` in `Re s > 0`, away from `1` and from the zeros of `ζ`. -/
theorem logDeriv_riemannXi_eq_gammaFactor_add {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s ≠ 0) :
    logDeriv riemannXi s = gammaFactor s + logDeriv riemannZeta s := by
  rw [logDeriv_riemannXi hs hs1 hz, gammaFactor]
  ring

/-! ### G1: the argument principle for `ξ` -/

/-- The zeros of `ζ` counted in `zetaZeroesSum (Ioo 0 1) (Icc (-T) T)`. -/
theorem zetaZeroesIn_strip_finite (T : ℝ) : (zetaZeroesIn (Ioo 0 1) (Icc (-T) T)).Finite :=
  zetaZeroesIn_finite (a := 0) (b := 1) Ioo_subset_Icc_self subset_rfl

/-- G1: if `ζ(σ + iT₁) ≠ 0` for `0 ≤ σ ≤ 1`, the sum over the zeros with `|γ| ≤ T₁` is the
integral of `Φ ξ'/ξ` over the boundary of `[-δ₁, 1 + δ₁] × [-T₁, T₁]`, divided by `2πi`. -/
theorem IsTestFunction.zetaZeroesSum_eq_rectIntegral (hres : ResidueTheoremRectangle)
    (hF : IsTestFunction F δ₀) {δ₁ T₁ : ℝ} (h0 : 0 < δ₁) (h1 : δ₁ < δ₀) (hT₁ : 0 < T₁)
    (hT : ∀ σ ∈ Icc (0 : ℝ) 1, riemannZeta (σ + T₁ * I) ≠ 0) :
    zetaZeroesSum (Ioo 0 1) (Icc (-T₁) T₁) (Phi F) =
      (2 * π * I)⁻¹ * rectIntegral (fun s ↦ Phi F s * logDeriv riemannXi s)
        ⟨-δ₁, -T₁⟩ ⟨1 + δ₁, T₁⟩ := by
  set hfin := zetaZeroesIn_strip_finite T₁
  set P := hfin.toFinset with hP
  have hmemP : ∀ ρ, ρ ∈ P ↔ ρ.re ∈ Ioo 0 1 ∧ ρ.im ∈ Icc (-T₁) T₁ ∧ riemannZeta ρ = 0 := by
    intro ρ
    rw [hP, Set.Finite.mem_toFinset]
    rfl
  -- no zeros on the horizontal sides
  have hne : ∀ ρ, riemannZeta ρ = 0 → ρ.re ∈ Icc (0 : ℝ) 1 → |ρ.im| ≠ T₁ := by
    intro ρ hρ hre him
    rcases abs_eq hT₁.le |>.1 him with h | h
    · apply hT ρ.re hre
      rw [← h, re_add_im]
      exact hρ
    · have hρ1 : ρ ≠ 1 := fun h' ↦ by rw [h', one_im] at h; linarith
      apply hT ρ.re hre
      have : (ρ.re : ℂ) + T₁ * I = conj ρ := by
        apply Complex.ext <;> simp [h]
      rw [this, riemannZeta_conj hρ1, hρ, map_zero]
  have hD1 := rectIntegral_mul_logDeriv_eq_sum (f := riemannXi) (φ := Phi F) (P := P) hres
    (z := ⟨-δ₁, -T₁⟩) (w := ⟨1 + δ₁, T₁⟩) (by simp only; linarith) (by simp only; linarith)
    (fun u _ ↦ differentiable_riemannXi.analyticAt u)
    (fun u hu ↦ by
      rw [mem_reProdIm] at hu
      simp only at hu
      rw [uIcc_of_le (by linarith)] at hu
      exact hF.analyticAt_Phi (by linarith [hu.1.1]) (by linarith [hu.1.2]))
    (fun ρ hρ ↦ by
      obtain ⟨hre, him, hz⟩ := (hmemP ρ).1 hρ
      refine mem_reProdIm.2 ⟨⟨by simp only; linarith [hre.1], by simp only; linarith [hre.2]⟩,
        ?_⟩
      have := hne ρ hz ⟨hre.1.le, hre.2.le⟩
      simp only
      constructor
      · rcases lt_or_eq_of_le him.1 with h | h
        · exact h
        · exact absurd (by rw [← h, abs_neg, abs_of_pos hT₁]) this
      · rcases lt_or_eq_of_le him.2 with h | h
        · exact h
        · exact absurd (by rw [h, abs_of_pos hT₁]) this)
    (fun u hu hξ ↦ by
      obtain ⟨hz, hre0, hre1⟩ := riemannXi_eq_zero_iff.1 hξ
      rw [mem_reProdIm] at hu
      simp only at hu
      rw [uIcc_of_le (by linarith), uIcc_of_le (by linarith)] at hu
      exact (hmemP u).2 ⟨⟨hre0, hre1⟩, hu.2, hz⟩)
  rw [hD1, zetaZeroesSum_eq_sum hfin, ← mul_assoc, inv_mul_cancel₀ (by
    simp [Real.pi_ne_zero, I_ne_zero]), one_mul]
  refine Finset.sum_congr rfl fun ρ hρ ↦ ?_
  obtain ⟨hre, -, -⟩ := (hmemP ρ).1 hρ
  have hord : analyticOrderNatAt riemannXi ρ = analyticOrderNatAt riemannZeta ρ := by
    unfold analyticOrderNatAt
    rw [analyticOrderAt_riemannXi hre.1 hre.2]
  rw [hord, zetaOrder_eq (ne_one_of_re_lt_one hre.2)]
  push_cast
  ring

/-! ### G3: the vertical sides -/

theorem rectIntegral_mk (f : ℂ → ℂ) (a b c d : ℝ) : rectIntegral f ⟨a, c⟩ ⟨b, d⟩ =
    (∫ x : ℝ in a..b, f (x + c * I)) - (∫ x : ℝ in a..b, f (x + d * I)) +
      I * (∫ y : ℝ in c..d, f (b + y * I)) - I * (∫ y : ℝ in c..d, f (a + y * I)) := rfl

/-- G3: the vertical sides of the contour of G1, by `ξ'/ξ(1 - s) = -ξ'/ξ(s)` and (12.24). -/
theorem IsTestFunction.rectIntegral_riemannXi_eq (hF : IsTestFunction F δ₀) {δ₁ : ℝ}
    (h0 : 0 < δ₁) (h1 : δ₁ < δ₀) (T₁ : ℝ) :
    rectIntegral (fun s ↦ Phi F s * logDeriv riemannXi s) ⟨-δ₁, -T₁⟩ ⟨1 + δ₁, T₁⟩ =
      (∫ x : ℝ in (-δ₁)..(1 + δ₁),
          Phi F (x + (-T₁ : ℝ) * I) * logDeriv riemannXi (x + (-T₁ : ℝ) * I)) -
        (∫ x : ℝ in (-δ₁)..(1 + δ₁), Phi F (x + T₁ * I) * logDeriv riemannXi (x + T₁ * I)) +
      I * ((∫ y : ℝ in (-T₁)..T₁, (Phi F (1 + δ₁ + y * I) + Phi F (1 - (1 + δ₁ + y * I))) *
              logDeriv riemannZeta (1 + δ₁ + y * I)) +
          ∫ y : ℝ in (-T₁)..T₁, gammaFactor (1 + δ₁ + y * I) *
              (Phi F (1 + δ₁ + y * I) + Phi F (1 - (1 + δ₁ + y * I)))) := by
  rw [rectIntegral_mk]
  -- the line `σ = 1 + δ₁`
  have hre : ∀ y : ℝ, (1 + δ₁ + y * I : ℂ).re = 1 + δ₁ := fun y ↦ by simp
  have hcast : ∀ y : ℝ, ((1 + δ₁ : ℝ) : ℂ) + y * I = 1 + δ₁ + y * I := fun y ↦ by push_cast; ring
  have hzeta : ∀ y : ℝ, riemannZeta (1 + δ₁ + y * I) ≠ 0 := fun y ↦
    riemannZeta_ne_zero_of_one_lt_re (by rw [hre]; linarith)
  have hne1 : ∀ y : ℝ, (1 + δ₁ + y * I : ℂ) ≠ 1 := fun y h ↦ by
    have := congrArg re h
    rw [hre, one_re] at this
    linarith
  have hsplit : ∀ y : ℝ, logDeriv riemannXi (1 + δ₁ + y * I) =
      gammaFactor (1 + δ₁ + y * I) + logDeriv riemannZeta (1 + δ₁ + y * I) := fun y ↦
    logDeriv_riemannXi_eq_gammaFactor_add (by rw [hre]; linarith) (hne1 y) (hzeta y)
  -- continuity of the pieces
  have hΦ : Continuous fun y : ℝ ↦ Phi F (1 + δ₁ + y * I) := by
    have := hF.continuous_Phi_vline (σ := 1 + δ₁) (by linarith) (by linarith)
    simpa only [hcast] using this
  have hΦ' : Continuous fun y : ℝ ↦ Phi F (1 - (1 + δ₁ + y * I)) := by
    have := hF.continuous_Phi_one_sub_vline (σ := 1 + δ₁) (by linarith) (by linarith)
    simpa only [hcast] using this
  have hL : Continuous fun y : ℝ ↦ logDeriv riemannZeta (1 + δ₁ + y * I) := by
    refine continuous_iff_continuousAt.2 fun y ↦ ?_
    have hc : Continuous fun y : ℝ ↦ (1 + δ₁ + y * I : ℂ) := by fun_prop
    exact (continuousAt_logDeriv_riemannZeta (by rw [hre]; linarith)).comp (x := y)
      (f := fun y : ℝ ↦ (1 + δ₁ + y * I : ℂ)) hc.continuousAt
  have hG : Continuous fun y : ℝ ↦ gammaFactor (1 + δ₁ + y * I) := by
    refine continuous_iff_continuousAt.2 fun y ↦ ?_
    have hc : Continuous fun y : ℝ ↦ (1 + δ₁ + y * I : ℂ) := by fun_prop
    exact (continuousAt_gammaFactor (by rw [hre]; linarith) (hne1 y)).comp (x := y)
      (f := fun y : ℝ ↦ (1 + δ₁ + y * I : ℂ)) hc.continuousAt
  -- the left side, by `y ↦ -y`
  have hleft : (∫ y : ℝ in (-T₁)..T₁,
        Phi F ((-δ₁ : ℝ) + y * I) * logDeriv riemannXi ((-δ₁ : ℝ) + y * I)) =
      -∫ y : ℝ in (-T₁)..T₁, Phi F (1 - (1 + δ₁ + y * I)) *
        logDeriv riemannXi (1 + δ₁ + y * I) := by
    have hc := intervalIntegral.integral_comp_neg (a := -T₁) (b := T₁)
      (fun y : ℝ ↦ Phi F ((-δ₁ : ℝ) + y * I) * logDeriv riemannXi ((-δ₁ : ℝ) + y * I))
    rw [neg_neg] at hc
    rw [← hc, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun y _ ↦ ?_
    have he : ((-δ₁ : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I = 1 - (1 + δ₁ + y * I) := by push_cast; ring
    rw [he, logDeriv_riemannXi_one_sub]
    ring
  have hright : (∫ y : ℝ in (-T₁)..T₁,
        Phi F ((1 + δ₁ : ℝ) + y * I) * logDeriv riemannXi ((1 + δ₁ : ℝ) + y * I)) =
      ∫ y : ℝ in (-T₁)..T₁, Phi F (1 + δ₁ + y * I) * logDeriv riemannXi (1 + δ₁ + y * I) := by
    refine intervalIntegral.integral_congr fun y _ ↦ ?_
    simp only [hcast]
  rw [hleft, hright]
  -- combine
  have hX : ∀ y : ℝ, Phi F (1 + δ₁ + y * I) * logDeriv riemannXi (1 + δ₁ + y * I) +
      Phi F (1 - (1 + δ₁ + y * I)) * logDeriv riemannXi (1 + δ₁ + y * I) =
      (Phi F (1 + δ₁ + y * I) + Phi F (1 - (1 + δ₁ + y * I))) *
          logDeriv riemannZeta (1 + δ₁ + y * I) +
        gammaFactor (1 + δ₁ + y * I) * (Phi F (1 + δ₁ + y * I) + Phi F (1 - (1 + δ₁ + y * I))) :=
    fun y ↦ by rw [hsplit]; ring
  have hcξ : Continuous fun y : ℝ ↦ logDeriv riemannXi (1 + δ₁ + y * I) := by
    have : (fun y : ℝ ↦ logDeriv riemannXi (1 + δ₁ + y * I)) =
        fun y : ℝ ↦ gammaFactor (1 + δ₁ + y * I) + logDeriv riemannZeta (1 + δ₁ + y * I) :=
      funext hsplit
    rw [this]
    exact hG.add hL
  have i1 : IntervalIntegrable (fun y : ℝ ↦ Phi F (1 + δ₁ + y * I) *
      logDeriv riemannXi (1 + δ₁ + y * I)) volume (-T₁) T₁ :=
    (hΦ.mul hcξ).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun y : ℝ ↦ Phi F (1 - (1 + δ₁ + y * I)) *
      logDeriv riemannXi (1 + δ₁ + y * I)) volume (-T₁) T₁ :=
    (hΦ'.mul hcξ).intervalIntegrable _ _
  have i3 : IntervalIntegrable (fun y : ℝ ↦ (Phi F (1 + δ₁ + y * I) +
      Phi F (1 - (1 + δ₁ + y * I))) * logDeriv riemannZeta (1 + δ₁ + y * I)) volume (-T₁) T₁ :=
    ((hΦ.add hΦ').mul hL).intervalIntegrable _ _
  have i4 : IntervalIntegrable (fun y : ℝ ↦ gammaFactor (1 + δ₁ + y * I) *
      (Phi F (1 + δ₁ + y * I) + Phi F (1 - (1 + δ₁ + y * I)))) volume (-T₁) T₁ :=
    (hG.mul (hΦ.add hΦ')).intervalIntegrable _ _
  have hsum : (∫ y : ℝ in (-T₁)..T₁, Phi F (1 + δ₁ + y * I) *
        logDeriv riemannXi (1 + δ₁ + y * I)) +
      (∫ y : ℝ in (-T₁)..T₁, Phi F (1 - (1 + δ₁ + y * I)) * logDeriv riemannXi (1 + δ₁ + y * I))
      = (∫ y : ℝ in (-T₁)..T₁, (Phi F (1 + δ₁ + y * I) + Phi F (1 - (1 + δ₁ + y * I))) *
              logDeriv riemannZeta (1 + δ₁ + y * I)) +
          ∫ y : ℝ in (-T₁)..T₁, gammaFactor (1 + δ₁ + y * I) *
              (Phi F (1 + δ₁ + y * I) + Phi F (1 - (1 + δ₁ + y * I))) := by
    rw [← intervalIntegral.integral_add i1 i2, ← intervalIntegral.integral_add i3 i4]
    exact intervalIntegral.integral_congr fun y _ ↦ hX y
  rw [← hsum]
  ring

/-! ### G4: from `σ = 1 + δ₁` to `σ = 1/2` -/

/-- `G(s)(Φ(s) + Φ(1 - s))`, the part of `(Φ(s) + Φ(1 - s)) ξ'/ξ(s)` not involving `ζ`. -/
def gammaIntegrand (F : ℝ → ℂ) (s : ℂ) : ℂ := gammaFactor s * (Phi F s + Phi F (1 - s))

theorem IsTestFunction.differentiableAt_Phi_add_Phi_one_sub (hF : IsTestFunction F δ₀) {s : ℂ}
    (h1 : -δ₀ < s.re) (h2 : s.re < 1 + δ₀) (h3 : -δ₀ < 1 - s.re) (h4 : 1 - s.re < 1 + δ₀) :
    DifferentiableAt ℂ (fun u ↦ Phi F u + Phi F (1 - u)) s := by
  have ha := (hF.analyticAt_Phi h1 h2).differentiableAt
  have hb : DifferentiableAt ℂ (fun u ↦ Phi F (1 - u)) s :=
    (hF.analyticAt_Phi (s := 1 - s) (by simpa using h3) (by simpa using h4)).differentiableAt.comp
      (x := s) (f := fun u : ℂ ↦ 1 - u) (by fun_prop)
  exact ha.add hb

/-- The residue of `G(s)(Φ(s) + Φ(1 - s))` at `s = 1` is `Φ(0) + Φ(1)`. -/
theorem IsTestFunction.circleIntegral_gammaIntegrand (hF : IsTestFunction F δ₀) {r : ℝ}
    (hr : 0 < r) (hr2 : r < 1 / 2) (hrδ : r < δ₀) :
    ∮ s in C(1, r), gammaIntegrand F s = 2 * π * I * (Phi F 0 + Phi F 1) := by
  set ε := min (1 / 2) δ₀ with hε
  have hrε : r < ε := lt_min hr2 hrδ
  have hcl : closedBall (1 : ℂ) r ⊆ ball 1 ε := closedBall_subset_ball hrε
  have hball : ∀ s ∈ ball (1 : ℂ) ε, 1 / 2 < s.re ∧ s.re < 1 + δ₀ ∧ -δ₀ < 1 - s.re := by
    intro s hs
    rw [mem_ball, dist_eq_norm] at hs
    have h := (abs_re_le_norm (s - 1)).trans_lt hs
    rw [sub_re, one_re, abs_lt] at h
    have h1 : ε ≤ 1 / 2 := min_le_left _ _
    have h2 : ε ≤ δ₀ := min_le_right _ _
    refine ⟨by linarith, by linarith, by linarith⟩
  set φ : ℂ → ℂ := fun u ↦ Phi F u + Phi F (1 - u) with hφ
  set h : ℂ → ℂ := fun u ↦ (1 / u + digamma (u / 2) / 2 - Real.log π / 2) * φ u with hh
  have hφd : DifferentiableOn ℂ φ (ball 1 ε) := fun s hs ↦ by
    obtain ⟨h1, h2, h3⟩ := hball s hs
    exact (hF.differentiableAt_Phi_add_Phi_one_sub (by linarith [hF.pos]) h2 h3
      (by linarith)).differentiableWithinAt
  have hhd : DifferentiableOn ℂ h (ball 1 ε) := fun s hs ↦ by
    obtain ⟨h1, -, -⟩ := hball s hs
    have hs0 : s ≠ 0 := ne_zero_of_re_pos (by linarith)
    have hd : DifferentiableAt ℂ (fun u : ℂ ↦ digamma (u / 2)) s :=
      (Complex.analyticOnNhd_digamma (s / 2) (by simp only [mem_setOf_eq, div_ofNat_re]; linarith)
        ).differentiableAt.comp (x := s) (f := fun u : ℂ ↦ u / 2) (by fun_prop)
    have h1' : DifferentiableAt ℂ (fun u : ℂ ↦ 1 / u) s :=
      (differentiableAt_const (1 : ℂ)).div differentiableAt_id hs0
    exact (((h1'.add (hd.div_const 2)).sub_const ((Real.log π : ℂ) / 2)).mul
      (hφd.differentiableAt (isOpen_ball.mem_nhds hs))).differentiableWithinAt
  have heq : EqOn (gammaIntegrand F) (fun s ↦ (s - 1)⁻¹ • φ s + h s) (sphere 1 r) := by
    intro s _
    simp only [gammaIntegrand, gammaFactor, hφ, hh, smul_eq_mul, one_div]
    ring
  have hi1 : CircleIntegrable (fun s ↦ (s - 1)⁻¹ • φ s) 1 r := by
    refine ContinuousOn.circleIntegrable hr.le (ContinuousOn.smul ?_ ?_)
    · refine ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const) fun s hs h' ↦ ?_
      rw [mem_sphere, dist_eq_norm, h', norm_zero] at hs
      exact hr.ne hs
    · exact (hφd.mono (sphere_subset_closedBall.trans hcl)).continuousOn
  have hi2 : CircleIntegrable h 1 r :=
    ContinuousOn.circleIntegrable hr.le (hhd.mono (sphere_subset_closedBall.trans hcl)).continuousOn
  rw [circleIntegral.integral_congr hr.le heq, circleIntegral.integral_add hi1 hi2,
    (hφd.mono hcl).circleIntegral_sub_inv_smul (mem_ball_self hr),
    ((hhd.mono hcl).mono closure_ball_subset_closedBall).diffContOnCl.circleIntegral_eq_zero hr.le]
  simp only [hφ, smul_eq_mul, add_zero, sub_self]
  ring

/-- G4: by the residue theorem on `[1/2, 1 + δ₁] × [-T, T]`, the integral of
`G(s)(Φ(s) + Φ(1 - s))` over `σ = 1 + δ₁` is that over `σ = 1/2`, plus `2π(Φ(0) + Φ(1))`, plus
the horizontal sides. -/
theorem IsTestFunction.integral_gammaIntegrand_right_eq (hres : ResidueTheoremRectangle)
    (hF : IsTestFunction F δ₀) {δ₁ : ℝ} (h0 : 0 < δ₁) (h1 : δ₁ < δ₀) {T : ℝ} (hT : 0 < T) :
    ∫ y : ℝ in (-T)..T, gammaIntegrand F ((1 + δ₁ : ℝ) + y * I) =
      (∫ y : ℝ in (-T)..T, gammaIntegrand F ((1 / 2 : ℝ) + y * I)) +
        2 * π * (Phi F 0 + Phi F 1) -
        I * ((∫ x : ℝ in (1 / 2)..(1 + δ₁), gammaIntegrand F (x + T * I)) -
          ∫ x : ℝ in (1 / 2)..(1 + δ₁), gammaIntegrand F (x + (-T : ℝ) * I)) := by
  set r := min (1 / 4) (min (δ₁ / 2) (T / 2)) with hr
  have hr0 : 0 < r := lt_min (by norm_num) (lt_min (by linarith) (by linarith))
  have hr1 : r ≤ 1 / 4 := min_le_left _ _
  have hr2 : r ≤ δ₁ / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hr3 : r ≤ T / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hdiff : DifferentiableOn ℂ (gammaIntegrand F)
      ((Set.uIcc (1 / 2 : ℝ) (1 + δ₁) ×ℂ Set.uIcc (-T) T) \ ↑({1} : Finset ℂ)) := by
    intro u hu
    obtain ⟨hu1, hu2⟩ := hu
    rw [mem_reProdIm, uIcc_of_le (by linarith)] at hu1
    have hu1' : u ≠ 1 := by simpa using hu2
    have hre : 0 < u.re := by linarith [hu1.1.1]
    exact ((differentiableAt_gammaFactor hre hu1').mul
      (hF.differentiableAt_Phi_add_Phi_one_sub (by linarith [hu1.1.1, hF.pos])
        (by linarith [hu1.1.2]) (by linarith [hu1.1.2]) (by linarith [hu1.1.1]))
      ).differentiableWithinAt
  have hR := hres ⟨1 / 2, -T⟩ ⟨1 + δ₁, T⟩ {1} r (gammaIntegrand F)
    (by simp only; linarith) (by simp only; linarith) hr0
    (fun ρ hρ ↦ by
      rw [Finset.mem_singleton] at hρ
      subst hρ
      simp only [one_re, one_im]
      refine ⟨by linarith, by linarith, by linarith, by linarith⟩)
    (fun ρ hρ σ hσ hne ↦ by
      rw [Finset.mem_singleton] at hρ hσ
      exact absurd (hρ.trans hσ.symm) hne) hdiff
  rw [Finset.sum_singleton, hF.circleIntegral_gammaIntegrand hr0 (by linarith) (by linarith)] at hR
  simp only at hR
  linear_combination (-I) * hR +
    ((∫ y : ℝ in (-T)..T, gammaIntegrand F ((1 + δ₁ : ℝ) + y * I)) -
      (∫ y : ℝ in (-T)..T, gammaIntegrand F ((1 / 2 : ℝ) + y * I)) -
        2 * π * (Phi F 0 + Phi F 1)) * I_sq

end WeilExplicitFormula
