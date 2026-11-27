/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Harald Helfgott
-/
module

public import Mathlib.NumberTheory.WeilExplicitFormula.Contour

/-! # Weil's explicit formula

Montgomery–Vaughan, *Multiplicative Number Theory I*, Theorem 12.13 with `q = 1`
(parts G2 and G6 of the blueprint, and the assembly), taking as hypotheses the statements of
three IEANTN conclusions, copied verbatim:

* `Theorem_10_13` (`ZetaGoodHeights.v1.theorem_10_13`): `N(T + 1) - N(T) ≪ log(T + 2)`;
* `Lemma_12_2` (`ZetaGoodHeights.v1.lemma_12_2`): for `T ≥ 2` there is `T₁ ∈ [T, T + 1]` with
  `ζ(σ + iT₁) ≠ 0` and `ζ'/ζ(σ + iT₁) ≪ (log T)²` for `-1 ≤ σ ≤ 2`;
* `ResidueTheoremRectangle` (`ContourIntegration.v1.residue_theorem_rectangle`).

## Main results

* `IsTestFunction.tendsto_zetaZeroesSum`: for a test function `F`,
  `∑_{|γ| ≤ T} Φ(ρ) → Φ(0) + Φ(1) + (ψ(1/4) - log π) F(0)/2π
    - (1/2π) ∑ Λ(n) n^{-1/2} (F(-log n/2π) + F(log n/2π))
    + ∫_0^∞ e^{-πx}/(1 - e^{-4πx}) (2F(0) - F(x) - F(-x)) dx`,
  the sum running over the zeros of `ζ` in `0 < Re s < 1` with multiplicity.
* `theorem_12_13_of`: the conclusion `WeilExplicitFormula.v1.theorem_12_13` of the IEANTN draft
  node, verbatim (`Theorem_12_13`), from the three hypotheses.

## AI usage

This file was written by Claude (Anthropic) in November 2026. It compiles, but has not been
reviewed by a human.
-/

@[expose] public section

open Real Complex Filter Topology Set Metric MeasureTheory Asymptotics
open scoped Interval FourierTransform ComplexConjugate

noncomputable section

namespace WeilExplicitFormula

variable {F : ℝ → ℂ} {δ₀ : ℝ}

/-! ### The hypotheses, copied verbatim from IEANTN -/

/-- **Montgomery–Vaughan, Theorem 10.13**: the statement of `ZetaGoodHeights.v1.theorem_10_13`. -/
def Theorem_10_13 : Prop :=
  ∃ C : ℝ, ∀ T : ℝ, 0 ≤ T →
    zetaZeroesSum (Set.Ioo 0 1) (Set.Icc T (T + 1)) (fun _ ↦ (1 : ℝ)) ≤ C * Real.log (T + 2)

/-- **Montgomery–Vaughan, Lemma 12.2**: the statement of `ZetaGoodHeights.v1.lemma_12_2`. -/
def Lemma_12_2 : Prop :=
  ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T → ∃ T₁ ∈ Set.Icc T (T + 1), ∀ σ ∈ Set.Icc (-1 : ℝ) 2,
    riemannZeta (σ + T₁ * Complex.I) ≠ 0 ∧
      ‖deriv riemannZeta (σ + T₁ * Complex.I) / riemannZeta (σ + T₁ * Complex.I)‖ ≤
        C * Real.log T ^ 2

/-! ### Bounds on horizontal segments (G2) -/

theorem exists_norm_gammaFactor_le :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ s : ℂ, s.re ∈ Icc (1 / 2 : ℝ) 2 → 1 ≤ |s.im| →
      ‖gammaFactor s‖ ≤ A + B * Real.log (|s.im| + 2) := by
  obtain ⟨C, hC⟩ := Complex.exists_norm_digamma_le_log (σ₁ := 1 / 4) (σ₂ := 1) (by norm_num)
  have hlogπ : 0 ≤ Real.log π := Real.log_nonneg (by linarith [Real.two_le_pi])
  refine ⟨2 + Real.log π / 2, |C| / 2, by linarith, by positivity, fun s hs hs1 ↦ ?_⟩
  have hs0 : s ≠ 0 := fun h ↦ by rw [h, zero_im, abs_zero] at hs1; linarith
  have h1 : ‖1 / s‖ ≤ 1 := by
    rw [norm_div, norm_one, div_le_one (norm_pos_iff.2 hs0)]
    exact hs1.trans (abs_im_le_norm s)
  have h2 : ‖1 / (s - 1)‖ ≤ 1 := by
    have hs10 : s - 1 ≠ 0 := fun h ↦ by
      have := congrArg im h
      rw [sub_im, one_im, sub_zero, zero_im] at this
      rw [this, abs_zero] at hs1
      linarith
    rw [norm_div, norm_one, div_le_one (norm_pos_iff.2 hs10)]
    calc 1 ≤ |s.im| := hs1
      _ = |(s - 1).im| := by rw [sub_im, one_im, sub_zero]
      _ ≤ ‖s - 1‖ := abs_im_le_norm _
  have h3 : ‖digamma (s / 2)‖ ≤ |C| * Real.log (|s.im| + 2) := by
    have hs2 : s / 2 = ((s.re / 2 : ℝ) : ℂ) + ((s.im / 2 : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp
    rw [hs2]
    have hlog : 0 ≤ Real.log (|s.im / 2| + 2) :=
      Real.log_nonneg (by linarith [abs_nonneg (s.im / 2)])
    calc ‖digamma (((s.re / 2 : ℝ) : ℂ) + ((s.im / 2 : ℝ) : ℂ) * I)‖
        ≤ C * Real.log (|s.im / 2| + 2) :=
          hC _ _ ⟨by linarith [hs.1], by linarith [hs.2]⟩
      _ ≤ |C| * Real.log (|s.im / 2| + 2) := mul_le_mul_of_nonneg_right (le_abs_self C) hlog
      _ ≤ |C| * Real.log (|s.im| + 2) := by
          refine mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) ?_) (abs_nonneg C)
          rw [abs_div, abs_two]
          linarith [abs_nonneg s.im]
  have h4 : ‖(Real.log π : ℂ) / 2‖ = Real.log π / 2 := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hlogπ, Complex.norm_two]
  have hX : ‖1 / s + 1 / (s - 1) + digamma (s / 2) / 2‖ ≤
      ‖1 / s‖ + ‖1 / (s - 1)‖ + ‖digamma (s / 2)‖ / 2 := by
    refine (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_of_eq ?_))
    rw [norm_div, Complex.norm_two]
  unfold gammaFactor
  calc ‖1 / s + 1 / (s - 1) + digamma (s / 2) / 2 - (Real.log π : ℂ) / 2‖
      ≤ ‖1 / s + 1 / (s - 1) + digamma (s / 2) / 2‖ + ‖(Real.log π : ℂ) / 2‖ := norm_sub_le _ _
    _ ≤ (1 + 1 + |C| * Real.log (|s.im| + 2) / 2) + Real.log π / 2 := by
        rw [h4]
        refine add_le_add (hX.trans ?_) le_rfl
        gcongr
    _ = 2 + Real.log π / 2 + |C| / 2 * Real.log (|s.im| + 2) := by ring

theorem IsTestFunction.exists_norm_Phi_le' (hF : IsTestFunction F δ₀) :
    ∃ C, 0 ≤ C ∧ ∀ s : ℂ, s.re ∈ Set.Icc (-δ₀) (1 + δ₀) → ‖Phi F s‖ ≤ C / (|s.im| + 1) := by
  obtain ⟨C, hC⟩ := hF.exists_norm_Phi_le
  refine ⟨max C 0, le_max_right _ _, fun s hs ↦ (hC s hs).trans ?_⟩
  gcongr
  exact le_max_left _ _

/-- At a good height `T₁` (`ζ ≠ 0` and `‖ζ'/ζ‖ ≤ M` on `[-1, 2] + iT₁`), `ζ ≠ 0` and
`‖ζ'/ζ‖ ≤ M` on `[-1, 2] ± iT₁`. -/
theorem logDeriv_riemannZeta_le_of_good {T₁ M : ℝ} (hT₁ : 0 < T₁)
    (hgood : ∀ σ ∈ Icc (-1 : ℝ) 2, riemannZeta (σ + T₁ * I) ≠ 0 ∧
      ‖deriv riemannZeta (σ + T₁ * I) / riemannZeta (σ + T₁ * I)‖ ≤ M)
    {x t : ℝ} (hx : x ∈ Icc (-1 : ℝ) 2) (ht : |t| = T₁) :
    riemannZeta (x + t * I) ≠ 0 ∧ ‖logDeriv riemannZeta (x + t * I)‖ ≤ M := by
  obtain ⟨h0, hM⟩ := hgood x hx
  have hne1 : (x : ℂ) + T₁ * I ≠ 1 := fun h ↦ by
    have := congrArg im h
    simp at this
    linarith
  rcases abs_eq hT₁.le |>.1 ht with rfl | rfl
  · exact ⟨h0, by rwa [logDeriv_apply]⟩
  · have hc : (x : ℂ) + ((-T₁ : ℝ) : ℂ) * I = conj ((x : ℂ) + T₁ * I) := by
      apply Complex.ext <;> simp
    rw [hc, riemannZeta_conj hne1, logDeriv_riemannZeta_conj hne1, norm_conj]
    refine ⟨by rwa [ne_eq, map_eq_zero], ?_⟩
    rwa [logDeriv_apply]

/-- `‖ξ'/ξ‖ ≤ M + A + B log(T₁ + 2)` on the horizontal segments `[-1, 2] ± iT₁` at a good
height `T₁ ≥ 1`. -/
theorem norm_logDeriv_riemannXi_le_of_good {T₁ M A B : ℝ} (hT₁ : 1 ≤ T₁)
    (hAB : ∀ s : ℂ, s.re ∈ Icc (1 / 2 : ℝ) 2 → 1 ≤ |s.im| →
      ‖gammaFactor s‖ ≤ A + B * Real.log (|s.im| + 2))
    (hgood : ∀ σ ∈ Icc (-1 : ℝ) 2, riemannZeta (σ + T₁ * I) ≠ 0 ∧
      ‖deriv riemannZeta (σ + T₁ * I) / riemannZeta (σ + T₁ * I)‖ ≤ M)
    {x t : ℝ} (hx : x ∈ Icc (-1 : ℝ) 2) (ht : |t| = T₁) :
    ‖logDeriv riemannXi (x + t * I)‖ ≤ M + (A + B * Real.log (T₁ + 2)) := by
  -- first for `x ≥ 1/2`
  have key : ∀ x t : ℝ, x ∈ Icc (1 / 2 : ℝ) 2 → |t| = T₁ →
      ‖logDeriv riemannXi (x + t * I)‖ ≤ M + (A + B * Real.log (T₁ + 2)) := by
    intro x t hx ht
    have hre : ((x : ℂ) + t * I).re = x := by simp
    have him : ((x : ℂ) + t * I).im = t := by simp
    obtain ⟨hz, hL⟩ := logDeriv_riemannZeta_le_of_good (by linarith) hgood
      ⟨by linarith [hx.1], hx.2⟩ ht
    have hne1 : (x : ℂ) + t * I ≠ 1 := fun h ↦ by
      have := congrArg im h
      rw [him, one_im] at this
      rw [this, abs_zero] at ht
      linarith
    rw [logDeriv_riemannXi_eq_gammaFactor_add (by rw [hre]; linarith [hx.1]) hne1 hz]
    refine (norm_add_le _ _).trans ?_
    rw [add_comm M]
    refine add_le_add ?_ hL
    have := hAB _ (by rw [hre]; exact hx) (by rw [him, ht]; exact hT₁)
    rwa [him, ht] at this
  rcases le_or_gt (1 / 2) x with h | h
  · exact key x t ⟨h, hx.2⟩ ht
  · have he : (x : ℂ) + t * I = 1 - (((1 - x : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I) := by
      push_cast
      ring
    rw [he, logDeriv_riemannXi_one_sub, norm_neg]
    exact key (1 - x) (-t) ⟨by linarith, by linarith [hx.1]⟩ (by rw [abs_neg, ht])

/-- The integral of `f` along a horizontal segment of length `L` is at most `L` times a bound
for `f`. -/
theorem norm_integral_horizontal_le {f : ℂ → ℂ} {a b t K : ℝ} (hab : a ≤ b)
    (hK : ∀ x ∈ Icc a b, ‖f (x + t * I)‖ ≤ K) :
    ‖∫ x : ℝ in a..b, f (x + t * I)‖ ≤ K * (b - a) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
    (f := fun x : ℝ ↦ f (x + t * I)) (C := K) (fun x hx ↦ hK x (by
      rw [uIoc_of_le hab] at hx
      exact ⟨hx.1.le, hx.2⟩))
  rwa [abs_of_nonneg (by linarith)] at h

/-! ### G6: from good heights to all heights -/

theorem zetaOrder_nonneg_of_mem {ρ : ℂ} (hρ : ρ.re < 1) :
    ((zetaOrder ρ : ℤ) : ℝ) = (analyticOrderNatAt riemannZeta ρ : ℝ) := by
  rw [zetaOrder_eq (ne_one_of_re_lt_one hρ)]
  push_cast
  rfl

theorem mem_zetaZeroesIn_toFinset {I J : Set ℝ} (h : (zetaZeroesIn I J).Finite) (ρ : ℂ) :
    ρ ∈ h.toFinset ↔ ρ.re ∈ I ∧ ρ.im ∈ J ∧ riemannZeta ρ = 0 := by
  rw [Set.Finite.mem_toFinset]
  rfl

/-- The zeros with ordinate in `[-T-1, -T]` are the conjugates of those with ordinate in
`[T, T+1]`, with the same multiplicities. -/
theorem sum_order_neg_eq (T : ℝ) :
    ∑ ρ ∈ (zetaZeroesIn_finite (I := Ioo 0 1) (J := Icc (-T - 1) (-T)) (a := 0) (b := 1)
        Ioo_subset_Icc_self subset_rfl).toFinset, (analyticOrderNatAt riemannZeta ρ : ℝ) =
      ∑ ρ ∈ (zetaZeroesIn_finite (I := Ioo 0 1) (J := Icc T (T + 1)) (a := 0) (b := 1)
        Ioo_subset_Icc_self subset_rfl).toFinset, (analyticOrderNatAt riemannZeta ρ : ℝ) := by
  refine Finset.sum_nbij' (starRingEnd ℂ) (starRingEnd ℂ) ?_ ?_ (fun ρ _ ↦ conj_conj ρ)
    (fun ρ _ ↦ conj_conj ρ) ?_
  · intro ρ hρ
    rw [mem_zetaZeroesIn_toFinset] at hρ ⊢
    obtain ⟨hre, him, hz⟩ := hρ
    refine ⟨by simpa using hre, ⟨by simp; linarith [him.2], by simp; linarith [him.1]⟩, ?_⟩
    rw [riemannZeta_conj (ne_one_of_re_lt_one hre.2), hz, map_zero]
  · intro ρ hρ
    rw [mem_zetaZeroesIn_toFinset] at hρ ⊢
    obtain ⟨hre, him, hz⟩ := hρ
    refine ⟨by simpa using hre, ⟨by simp; linarith [him.2], by simp; linarith [him.1]⟩, ?_⟩
    rw [riemannZeta_conj (ne_one_of_re_lt_one hre.2), hz, map_zero]
  · intro ρ hρ
    rw [mem_zetaZeroesIn_toFinset] at hρ
    unfold analyticOrderNatAt
    rw [analyticOrderAt_riemannZeta_conj (ne_one_of_re_lt_one hρ.1.2)]

/-- G6: the zeros with `T < |γ| ≤ T'`, `T' ≤ T + 1`, contribute at most
`2 (C/(T + 1)) (N(T + 1) - N(T))` to the sum of `Φ(ρ)`, where `‖Φ(s)‖ ≤ C/(|t| + 1)`. -/
theorem norm_zetaZeroesSum_sub_le {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ s : ℂ, s.re ∈ Set.Icc (-δ₀) (1 + δ₀) → ‖Phi F s‖ ≤ C / (|s.im| + 1))
    (hδ₀ : 0 < δ₀) {T T' : ℝ} (hT : 0 ≤ T) (hTT' : T ≤ T') (hT' : T' ≤ T + 1) :
    ‖zetaZeroesSum (Ioo 0 1) (Icc (-T') T') (Phi F) -
        zetaZeroesSum (Ioo 0 1) (Icc (-T) T) (Phi F)‖ ≤
      C / (T + 1) * (2 * zetaZeroesSum (Ioo 0 1) (Icc T (T + 1)) (fun _ ↦ (1 : ℝ))) := by
  classical
  set hP := zetaZeroesIn_strip_finite T
  set hP' := zetaZeroesIn_strip_finite T'
  set hQ := zetaZeroesIn_finite (I := Ioo 0 1) (J := Icc T (T + 1)) (a := 0) (b := 1)
    Ioo_subset_Icc_self subset_rfl
  set hQ' := zetaZeroesIn_finite (I := Ioo 0 1) (J := Icc (-T - 1) (-T)) (a := 0) (b := 1)
    Ioo_subset_Icc_self subset_rfl
  have hsub : hP.toFinset ⊆ hP'.toFinset := by
    intro ρ hρ
    rw [mem_zetaZeroesIn_toFinset] at hρ ⊢
    exact ⟨hρ.1, ⟨by linarith [hρ.2.1.1], by linarith [hρ.2.1.2]⟩, hρ.2.2⟩
  have hdiff : hP'.toFinset \ hP.toFinset ⊆ hQ.toFinset ∪ hQ'.toFinset := by
    intro ρ hρ
    rw [Finset.mem_sdiff, mem_zetaZeroesIn_toFinset, mem_zetaZeroesIn_toFinset] at hρ
    obtain ⟨⟨hre, him, hz⟩, hnot⟩ := hρ
    rw [Finset.mem_union, mem_zetaZeroesIn_toFinset, mem_zetaZeroesIn_toFinset]
    by_cases hpos : T < ρ.im
    · exact Or.inl ⟨hre, ⟨hpos.le, by linarith [him.2]⟩, hz⟩
    · have hneg : ρ.im < -T := by
        by_contra h'
        exact hnot ⟨hre, ⟨not_lt.1 h', not_lt.1 hpos⟩, hz⟩
      exact Or.inr ⟨hre, ⟨by linarith [him.1], hneg.le⟩, hz⟩
  have hord : ∀ ρ ∈ hP'.toFinset, ((zetaOrder ρ : ℤ) : ℂ) =
      ((analyticOrderNatAt riemannZeta ρ : ℕ) : ℂ) := by
    intro ρ hρ
    rw [mem_zetaZeroesIn_toFinset] at hρ
    rw [zetaOrder_eq (ne_one_of_re_lt_one hρ.1.2)]
    push_cast
    rfl
  rw [zetaZeroesSum_eq_sum hP', zetaZeroesSum_eq_sum hP, zetaZeroesSum_eq_sum hQ,
    ← Finset.sum_sdiff hsub, add_sub_cancel_right]
  calc ‖∑ ρ ∈ hP'.toFinset \ hP.toFinset, Phi F ρ * ((zetaOrder ρ : ℤ) : ℂ)‖
      ≤ ∑ ρ ∈ hP'.toFinset \ hP.toFinset, C / (T + 1) * (analyticOrderNatAt riemannZeta ρ : ℝ) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ hρ ↦ ?_)
        have hρ' := Finset.mem_sdiff.1 hρ
        rw [hord ρ hρ'.1, norm_mul, Complex.norm_natCast]
        refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
        rw [mem_zetaZeroesIn_toFinset] at hρ'
        obtain ⟨⟨hre, -, -⟩, -⟩ := hρ'
        have hin : |ρ.im| ≥ T := by
          have := Finset.mem_sdiff.1 hρ
          rw [mem_zetaZeroesIn_toFinset, mem_zetaZeroesIn_toFinset] at this
          obtain ⟨⟨-, him, hz⟩, hnot⟩ := this
          by_contra h'
          rw [not_le, abs_lt] at h'
          exact hnot ⟨hre, ⟨h'.1.le, h'.2.le⟩, hz⟩
        refine (hC ρ ⟨by linarith [hre.1], by linarith [hre.2]⟩).trans ?_
        gcongr
    _ = C / (T + 1) * ∑ ρ ∈ hP'.toFinset \ hP.toFinset, (analyticOrderNatAt riemannZeta ρ : ℝ) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ C / (T + 1) * ∑ ρ ∈ hQ.toFinset ∪ hQ'.toFinset, (analyticOrderNatAt riemannZeta ρ : ℝ) := by
        exact mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum_of_subset_of_nonneg hdiff fun _ _ _ ↦ Nat.cast_nonneg _)
          (div_nonneg hC0 (by linarith))
    _ ≤ C / (T + 1) * (∑ ρ ∈ hQ.toFinset, (analyticOrderNatAt riemannZeta ρ : ℝ) +
          ∑ ρ ∈ hQ'.toFinset, (analyticOrderNatAt riemannZeta ρ : ℝ)) := by
        gcongr
        rw [← Finset.sum_union_inter]
        exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _)
    _ = C / (T + 1) * (2 * ∑ ρ ∈ hQ.toFinset, 1 * ((zetaOrder ρ : ℤ) : ℝ)) := by
        rw [sum_order_neg_eq T]
        congr 1
        rw [two_mul]
        congr 1 <;> refine Finset.sum_congr rfl fun ρ hρ ↦ ?_ <;>
          rw [mem_zetaZeroesIn_toFinset] at hρ <;>
          rw [one_mul, zetaOrder_nonneg_of_mem hρ.1.2]

/-! ### The assembly -/

/-- The right-hand side of the explicit formula (Montgomery–Vaughan (12.22) with `q = 1`), as in
the draft `blueprint/drafts/WeilExplicitFormula.lean`. -/
def rhs (F : ℝ → ℂ) : ℂ :=
  Phi F 0 + Phi F 1 + (2 * π : ℂ)⁻¹ * (digamma (1 / 4) - Real.log π) * F 0 -
    (2 * π : ℂ)⁻¹ * ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
      (F (-(Real.log n / (2 * π))) + F (Real.log n / (2 * π))) +
    ∫ x in Set.Ioi (0 : ℝ),
      ((Real.exp (-(π * x)) / (1 - Real.exp (-(4 * π * x))) : ℝ) : ℂ) * (2 * F 0 - F x - F (-x))

/-- A horizontal side of the contour of G1, at height `t`. -/
def horizXi (F : ℝ → ℂ) (δ₁ t : ℝ) : ℂ :=
  ∫ x : ℝ in (-δ₁)..(1 + δ₁), Phi F (x + t * I) * logDeriv riemannXi (x + t * I)

/-- A horizontal side of the contour of G4, at height `t`. -/
def horizGamma (F : ℝ → ℂ) (δ₁ t : ℝ) : ℂ :=
  ∫ x : ℝ in (1 / 2)..(1 + δ₁), gammaIntegrand F (x + t * I)

/-- The main terms, at height `u`. -/
def mainTerm (F : ℝ → ℂ) (δ₁ u : ℝ) : ℂ :=
  (2 * π : ℂ)⁻¹ * (∫ y : ℝ in (-u)..u, (Phi F (1 + δ₁ + y * I) + Phi F (1 - (1 + δ₁ + y * I))) *
      logDeriv riemannZeta (1 + δ₁ + y * I)) +
    (2 * π : ℂ)⁻¹ * (∫ y : ℝ in (-u)..u,
      gammaFactor (1 / 2 + y * I) * (Phi F (1 / 2 + y * I) + Phi F (1 - (1 / 2 + y * I)))) +
    (Phi F 0 + Phi F 1)

/-- The error terms (the horizontal sides), at height `T₁`. -/
def errTerm (F : ℝ → ℂ) (δ₁ T₁ : ℝ) : ℂ :=
  (2 * π * I)⁻¹ * (horizXi F δ₁ (-T₁) - horizXi F δ₁ T₁) -
    (2 * π : ℂ)⁻¹ * I * (horizGamma F δ₁ T₁ - horizGamma F δ₁ (-T₁))

/-- The main terms tend to the right-hand side (F3 and G5). -/
theorem IsTestFunction.tendsto_mainTerm (hF : IsTestFunction F δ₀) {δ₁ : ℝ} (h0 : 0 < δ₁)
    (h1 : δ₁ < δ₀) : Tendsto (mainTerm F δ₁) atTop (𝓝 (rhs F)) := by
  have h3 := hF.tendsto_integral_Phi_mul_logDeriv h0 h1
  have h5 := hF.tendsto_integral_gammaFactor_half
  have := ((h3.const_mul (2 * π : ℂ)⁻¹).add (h5.const_mul (2 * π : ℂ)⁻¹)).add
    (tendsto_const_nhds (x := Phi F 0 + Phi F 1))
  convert this using 2
  have h2π : (2 * π : ℂ) ≠ 0 := mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_ne_zero)
  have hK : ∀ K : ℂ, (2 * π : ℂ)⁻¹ * (2 * π * K) = K := fun K ↦ by
    rw [← mul_assoc, inv_mul_cancel₀ h2π, one_mul]
  simp only [rhs, mul_add, hK]
  ring

/-- G1–G4: at a height `T₁` with `ζ(σ + iT₁) ≠ 0` for `0 ≤ σ ≤ 1`, the sum over zeros is the main
terms plus the horizontal sides. -/
theorem IsTestFunction.zetaZeroesSum_eq_main_add_err (hres : ResidueTheoremRectangle)
    (hF : IsTestFunction F δ₀) {δ₁ T₁ : ℝ} (h0 : 0 < δ₁) (h1 : δ₁ < δ₀) (hT₁ : 0 < T₁)
    (hT : ∀ σ ∈ Icc (0 : ℝ) 1, riemannZeta (σ + T₁ * I) ≠ 0) :
    zetaZeroesSum (Ioo 0 1) (Icc (-T₁) T₁) (Phi F) = mainTerm F δ₁ T₁ + errTerm F δ₁ T₁ := by
  rw [hF.zetaZeroesSum_eq_rectIntegral hres h0 h1 hT₁ hT, hF.rectIntegral_riemannXi_eq h0 h1]
  have h4 := hF.integral_gammaIntegrand_right_eq hres h0 h1 hT₁
  have hr : (∫ y : ℝ in (-T₁)..T₁, gammaFactor (1 + δ₁ + y * I) *
      (Phi F (1 + δ₁ + y * I) + Phi F (1 - (1 + δ₁ + y * I)))) =
      ∫ y : ℝ in (-T₁)..T₁, gammaIntegrand F ((1 + δ₁ : ℝ) + y * I) := by
    refine intervalIntegral.integral_congr fun y _ ↦ ?_
    simp only [gammaIntegrand]
    push_cast
    ring_nf
  have hl : (∫ y : ℝ in (-T₁)..T₁, gammaIntegrand F ((1 / 2 : ℝ) + y * I)) =
      ∫ y : ℝ in (-T₁)..T₁, gammaFactor (1 / 2 + y * I) *
        (Phi F (1 / 2 + y * I) + Phi F (1 - (1 / 2 + y * I))) := by
    refine intervalIntegral.integral_congr fun y _ ↦ ?_
    simp only [gammaIntegrand]
    push_cast
    ring_nf
  rw [hr, h4, hl]
  simp only [mainTerm, errTerm, horizXi, horizGamma]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  field_simp
  ring

theorem norm_two_pi_I_inv : ‖(2 * π * I : ℂ)⁻¹‖ = (2 * π)⁻¹ := by
  rw [norm_inv, norm_mul, norm_I, mul_one, norm_mul, Complex.norm_two, Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le]

theorem norm_two_pi_inv_mul_I : ‖(2 * π : ℂ)⁻¹ * I‖ = (2 * π)⁻¹ := by
  rw [norm_mul, norm_I, mul_one, norm_inv, norm_mul, Complex.norm_two, Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le]

/-- G2: a bound for the horizontal sides of the contour of G1 at a good height. -/
theorem norm_horizXi_le {δ₁ T₁ M A B C : ℝ}
    (h0 : 0 < δ₁) (h1 : δ₁ < δ₀) (hδ₁ : δ₁ ≤ 1) (hT₁ : 1 ≤ T₁) (hC0 : 0 ≤ C)
    (hC : ∀ s : ℂ, s.re ∈ Set.Icc (-δ₀) (1 + δ₀) → ‖Phi F s‖ ≤ C / (|s.im| + 1))
    (hAB : ∀ s : ℂ, s.re ∈ Icc (1 / 2 : ℝ) 2 → 1 ≤ |s.im| →
      ‖gammaFactor s‖ ≤ A + B * Real.log (|s.im| + 2))
    (hgood : ∀ σ ∈ Icc (-1 : ℝ) 2, riemannZeta (σ + T₁ * I) ≠ 0 ∧
      ‖deriv riemannZeta (σ + T₁ * I) / riemannZeta (σ + T₁ * I)‖ ≤ M)
    {t : ℝ} (ht : |t| = T₁) :
    ‖horizXi F δ₁ t‖ ≤ C / (T₁ + 1) * (M + (A + B * Real.log (T₁ + 2))) * (1 + 2 * δ₁) := by
  have h := norm_integral_horizontal_le (f := fun s ↦ Phi F s * logDeriv riemannXi s)
    (a := -δ₁) (b := 1 + δ₁) (t := t) (K := C / (T₁ + 1) * (M + (A + B * Real.log (T₁ + 2))))
    (by linarith) (fun x hx ↦ ?_)
  · unfold horizXi
    rw [show 1 + δ₁ - -δ₁ = 1 + 2 * δ₁ by ring] at h
    exact h
  · rw [norm_mul]
    have hΦ := hC (x + t * I) (by simp; constructor <;> linarith [hx.1, hx.2])
    rw [show ((x : ℂ) + t * I).im = t by simp, ht] at hΦ
    exact mul_le_mul hΦ (norm_logDeriv_riemannXi_le_of_good hT₁ hAB hgood
      ⟨by linarith [hx.1], by linarith [hx.2]⟩ ht) (norm_nonneg _) (by positivity)

/-- G4: a bound for the horizontal sides of the contour of G4. -/
theorem norm_horizGamma_le {δ₁ T₁ A B C : ℝ}
    (h0 : 0 < δ₁) (h1 : δ₁ < δ₀) (hδ₁ : δ₁ ≤ 1) (hT₁ : 1 ≤ T₁)
    (hC : ∀ s : ℂ, s.re ∈ Set.Icc (-δ₀) (1 + δ₀) → ‖Phi F s‖ ≤ C / (|s.im| + 1))
    (hAB : ∀ s : ℂ, s.re ∈ Icc (1 / 2 : ℝ) 2 → 1 ≤ |s.im| →
      ‖gammaFactor s‖ ≤ A + B * Real.log (|s.im| + 2))
    {t : ℝ} (ht : |t| = T₁) :
    ‖horizGamma F δ₁ t‖ ≤ (A + B * Real.log (T₁ + 2)) * (2 * (C / (T₁ + 1))) * (1 / 2 + δ₁) := by
  have h := norm_integral_horizontal_le (f := gammaIntegrand F)
    (a := 1 / 2) (b := 1 + δ₁) (t := t) (K := (A + B * Real.log (T₁ + 2)) * (2 * (C / (T₁ + 1))))
    (by linarith) (fun x hx ↦ ?_)
  · unfold horizGamma
    rw [show 1 + δ₁ - 1 / 2 = 1 / 2 + δ₁ by ring] at h
    exact h
  · have him : ((x : ℂ) + t * I).im = t := by simp
    have hγ := hAB (x + t * I) (by simp; constructor <;> linarith [hx.1, hx.2])
      (by rw [him, ht]; exact hT₁)
    rw [him, ht] at hγ
    have hΦ1 := hC (x + t * I) (by simp; constructor <;> linarith [hx.1, hx.2])
    rw [him, ht] at hΦ1
    have hΦ2 := hC (1 - (x + t * I)) (by simp; constructor <;> linarith [hx.1, hx.2])
    rw [show (1 - ((x : ℂ) + t * I)).im = -t by simp, abs_neg, ht] at hΦ2
    rw [gammaIntegrand, norm_mul]
    refine mul_le_mul hγ ((norm_add_le _ _).trans (by linarith)) (norm_nonneg _)
      ((norm_nonneg _).trans hγ)

/-- G2 and G4: a bound for the error terms at a good height. -/
theorem norm_errTerm_le {δ₁ T₁ M A B C : ℝ}
    (h0 : 0 < δ₁) (h1 : δ₁ < δ₀) (hδ₁ : δ₁ ≤ 1) (hT₁ : 1 ≤ T₁) (hC0 : 0 ≤ C)
    (hC : ∀ s : ℂ, s.re ∈ Set.Icc (-δ₀) (1 + δ₀) → ‖Phi F s‖ ≤ C / (|s.im| + 1))
    (hAB : ∀ s : ℂ, s.re ∈ Icc (1 / 2 : ℝ) 2 → 1 ≤ |s.im| →
      ‖gammaFactor s‖ ≤ A + B * Real.log (|s.im| + 2))
    (hgood : ∀ σ ∈ Icc (-1 : ℝ) 2, riemannZeta (σ + T₁ * I) ≠ 0 ∧
      ‖deriv riemannZeta (σ + T₁ * I) / riemannZeta (σ + T₁ * I)‖ ≤ M) :
    ‖errTerm F δ₁ T₁‖ ≤ (2 * π)⁻¹ *
      (2 * (C / (T₁ + 1) * (M + (A + B * Real.log (T₁ + 2))) * (1 + 2 * δ₁)) +
        2 * ((A + B * Real.log (T₁ + 2)) * (2 * (C / (T₁ + 1))) * (1 / 2 + δ₁))) := by
  have hT₁0 : (0 : ℝ) ≤ T₁ := by linarith
  have e1 := norm_horizXi_le h0 h1 hδ₁ hT₁ hC0 hC hAB hgood (t := T₁) (abs_of_nonneg hT₁0)
  have e2 := norm_horizXi_le h0 h1 hδ₁ hT₁ hC0 hC hAB hgood (t := -T₁)
    (by rw [abs_neg, abs_of_nonneg hT₁0])
  have e3 := norm_horizGamma_le h0 h1 hδ₁ hT₁ hC hAB (t := T₁) (abs_of_nonneg hT₁0)
  have e4 := norm_horizGamma_le h0 h1 hδ₁ hT₁ hC hAB (t := -T₁)
    (by rw [abs_neg, abs_of_nonneg hT₁0])
  unfold errTerm
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_two_pi_I_inv, norm_mul, norm_two_pi_inv_mul_I, ← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine add_le_add ((norm_sub_le _ _).trans ?_) ((norm_sub_le _ _).trans ?_) <;> linarith

/-- Elementary inequalities for `T ≥ max 3 e` and `T ≤ T₁ ≤ T + 1`. -/
theorem log_bounds {T T₁ : ℝ} (hT : max 3 (Real.exp 1) ≤ T) (hT₁ : T₁ ∈ Icc T (T + 1)) :
    1 ≤ Real.log T ^ 2 ∧ Real.log (T₁ + 2) ≤ 2 * Real.log T ^ 2 ∧
      Real.log (T + 2) ≤ 2 * Real.log T ^ 2 := by
  have h3 : 3 ≤ T := (le_max_left _ _).trans hT
  have he : Real.exp 1 ≤ T := (le_max_right _ _).trans hT
  have hT0 : 0 < T := by linarith
  have hl1 : 1 ≤ Real.log T := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) he
  have hsq : Real.log T ≤ Real.log T ^ 2 := by nlinarith
  have hT3 : Real.log (T + 3) ≤ 2 * Real.log T := by
    rw [← Real.log_rpow hT0, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact Real.log_le_log (by linarith) (by nlinarith)
  refine ⟨by nlinarith, ?_, ?_⟩
  · calc Real.log (T₁ + 2) ≤ Real.log (T + 3) :=
          Real.log_le_log (by linarith [hT₁.1]) (by linarith [hT₁.2])
      _ ≤ 2 * Real.log T := hT3
      _ ≤ 2 * Real.log T ^ 2 := by linarith
  · calc Real.log (T + 2) ≤ Real.log (T + 3) := Real.log_le_log (by linarith) (by linarith)
      _ ≤ 2 * Real.log T := hT3
      _ ≤ 2 * Real.log T ^ 2 := by linarith

theorem tendsto_log_sq_div : Tendsto (fun T : ℝ ↦ Real.log T ^ 2 / (T + 1)) atTop (𝓝 0) := by
  have := Real.tendsto_pow_log_div_mul_add_atTop 1 1 2 one_ne_zero
  simpa only [one_mul] using this

/-- **Weil's explicit formula** (Montgomery–Vaughan Theorem 12.13 with `q = 1`), from Theorem 10.13,
Lemma 12.2 and the residue theorem on rectangles: the sum of `Φ(ρ)` over the zeros of `ζ` with
`0 < Re ρ < 1`, `|Im ρ| ≤ T`, counted with multiplicity, tends to `rhs F`. -/
theorem IsTestFunction.tendsto_zetaZeroesSum (h1013 : Theorem_10_13) (h122 : Lemma_12_2)
    (hres : ResidueTheoremRectangle) (hF : IsTestFunction F δ₀) :
    Tendsto (fun T : ℝ ↦ zetaZeroesSum (Ioo 0 1) (Icc (-T) T) (Phi F)) atTop (𝓝 (rhs F)) := by
  -- parameters
  set δ₁ := min δ₀ (1 / 2) / 2 with hδ₁def
  have hm0 : 0 < min δ₀ (1 / 2) := lt_min hF.pos (by norm_num)
  have h0 : 0 < δ₁ := by positivity
  have h1 : δ₁ < δ₀ := by linarith [min_le_left δ₀ (1 / 2)]
  have hδ₁ : δ₁ ≤ 1 := by linarith [min_le_right δ₀ (1 / 2)]
  obtain ⟨A, B, hA0, hB0, hAB⟩ := exists_norm_gammaFactor_le
  obtain ⟨C, hC0, hC⟩ := hF.exists_norm_Phi_le'
  obtain ⟨C₁₀, hC₁₀⟩ := h1013
  obtain ⟨C₁₂, hC₁₂⟩ := h122
  -- the good heights
  have hτ : ∀ T : ℝ, ∃ T₁ : ℝ, 2 ≤ T → T₁ ∈ Icc T (T + 1) ∧ ∀ σ ∈ Icc (-1 : ℝ) 2,
      riemannZeta (σ + T₁ * I) ≠ 0 ∧
        ‖deriv riemannZeta (σ + T₁ * I) / riemannZeta (σ + T₁ * I)‖ ≤ C₁₂ * Real.log T ^ 2 := by
    intro T
    by_cases hT : 2 ≤ T
    · obtain ⟨T₁, hT₁, h⟩ := hC₁₂ T hT
      exact ⟨T₁, fun _ ↦ ⟨hT₁, h⟩⟩
    · exact ⟨0, fun h ↦ absurd h hT⟩
  choose τ hτ using hτ
  have hτtop : Tendsto τ atTop atTop :=
    tendsto_atTop_mono' atTop ((eventually_ge_atTop 2).mono fun T hT ↦ (hτ T hT).1.1) tendsto_id
  set T₀ := max 3 (Real.exp 1) with hT₀
  have hT₀2 : (2 : ℝ) ≤ T₀ := (by norm_num : (2 : ℝ) ≤ 3).trans (le_max_left _ _)
  -- the error terms tend to `0`
  set K : ℝ := (2 * π)⁻¹ * (2 * (C * (|C₁₂| + A + 2 * B) * (1 + 2 * δ₁)) +
    2 * ((A + 2 * B) * (2 * C) * (1 / 2 + δ₁))) with hK
  have herr : Tendsto (fun T ↦ errTerm F δ₁ (τ T)) atTop (𝓝 0) := by
    have hlim : Tendsto (fun T : ℝ ↦ K * (Real.log T ^ 2 / (T + 1))) atTop (𝓝 0) := by
      simpa using tendsto_log_sq_div.const_mul K
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop T₀] with T hT
    have hT2 : 2 ≤ T := hT₀2.trans hT
    obtain ⟨hT₁, hgood⟩ := hτ T hT2
    obtain ⟨hL1, hL2, -⟩ := log_bounds hT hT₁
    have hT1 : 1 ≤ τ T := by linarith [hT₁.1]
    have hb := norm_errTerm_le h0 h1 hδ₁ hT1 hC0 hC hAB hgood
    set L := Real.log T ^ 2
    have hCT : C / (τ T + 1) ≤ C / (T + 1) := by
      gcongr
      exact hT₁.1
    have hM : C₁₂ * L ≤ |C₁₂| * L :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    have hW : C₁₂ * L + (A + B * Real.log (τ T + 2)) ≤ (|C₁₂| + A + 2 * B) * L := by
      nlinarith
    have hV : A + B * Real.log (τ T + 2) ≤ (A + 2 * B) * L := by nlinarith
    have hW0 : 0 ≤ C₁₂ * L + (A + B * Real.log (τ T + 2)) :=
      (norm_nonneg _).trans (norm_logDeriv_riemannXi_le_of_good hT1 hAB hgood
        (x := 1) (t := τ T) ⟨by norm_num, by norm_num⟩ (abs_of_nonneg (by linarith)))
    have hV0 : 0 ≤ A + B * Real.log (τ T + 2) :=
      add_nonneg hA0 (mul_nonneg hB0 (Real.log_nonneg (by linarith)))
    refine hb.trans ?_
    have hTp : (0 : ℝ) < T + 1 := by linarith
    calc (2 * π)⁻¹ * (2 * (C / (τ T + 1) * (C₁₂ * L + (A + B * Real.log (τ T + 2))) *
          (1 + 2 * δ₁)) + 2 * ((A + B * Real.log (τ T + 2)) * (2 * (C / (τ T + 1))) *
            (1 / 2 + δ₁)))
        ≤ (2 * π)⁻¹ * (2 * (C / (T + 1) * ((|C₁₂| + A + 2 * B) * L) * (1 + 2 * δ₁)) +
          2 * (((A + 2 * B) * L) * (2 * (C / (T + 1))) * (1 / 2 + δ₁))) := by
          gcongr
      _ = K * (L / (T + 1)) := by
          rw [hK]
          field_simp
  -- the sum over zeros at the good heights
  have hZτ : Tendsto (fun T ↦ zetaZeroesSum (Ioo 0 1) (Icc (-(τ T)) (τ T)) (Phi F)) atTop
      (𝓝 (rhs F)) := by
    have := ((hF.tendsto_mainTerm h0 h1).comp hτtop).add herr
    rw [add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with T hT
    obtain ⟨hT₁, hgood⟩ := hτ T hT
    exact (hF.zetaZeroesSum_eq_main_add_err hres h0 h1 (by linarith [hT₁.1])
      (fun σ hσ ↦ (hgood σ ⟨by linarith [hσ.1], by linarith [hσ.2]⟩).1)).symm
  -- from the good heights to all heights
  have hdiff : Tendsto (fun T ↦ zetaZeroesSum (Ioo 0 1) (Icc (-(τ T)) (τ T)) (Phi F) -
      zetaZeroesSum (Ioo 0 1) (Icc (-T) T) (Phi F)) atTop (𝓝 0) := by
    have hlim : Tendsto (fun T : ℝ ↦ (4 * C * |C₁₀|) * (Real.log T ^ 2 / (T + 1))) atTop
        (𝓝 0) := by
      simpa using tendsto_log_sq_div.const_mul (4 * C * |C₁₀|)
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop T₀] with T hT
    have hT2 : 2 ≤ T := hT₀2.trans hT
    obtain ⟨hT₁, -⟩ := hτ T hT2
    obtain ⟨hL1, -, hL3⟩ := log_bounds hT hT₁
    have h := norm_zetaZeroesSum_sub_le hC0 hC hF.pos (by linarith) hT₁.1 hT₁.2
    have hN := hC₁₀ T (by linarith)
    have hN' : zetaZeroesSum (Ioo 0 1) (Icc T (T + 1)) (fun _ ↦ (1 : ℝ)) ≤
        |C₁₀| * (2 * Real.log T ^ 2) := by
      refine hN.trans ?_
      calc C₁₀ * Real.log (T + 2) ≤ |C₁₀| * Real.log (T + 2) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (Real.log_nonneg (by linarith))
        _ ≤ |C₁₀| * (2 * Real.log T ^ 2) := mul_le_mul_of_nonneg_left hL3 (abs_nonneg _)
    refine h.trans ?_
    have hTp : (0 : ℝ) < T + 1 := by linarith
    calc C / (T + 1) * (2 * zetaZeroesSum (Ioo 0 1) (Icc T (T + 1)) fun _ ↦ (1 : ℝ))
        ≤ C / (T + 1) * (2 * (|C₁₀| * (2 * Real.log T ^ 2))) := by gcongr
      _ = 4 * C * |C₁₀| * (Real.log T ^ 2 / (T + 1)) := by
          field_simp
          ring
  have := hZτ.sub hdiff
  rw [sub_zero] at this
  exact this.congr fun T ↦ by ring

/-! ### The statement of the IEANTN node `WeilExplicitFormula.v1` -/

/-- The node's `IsTestFunction`: the same conditions as `IsTestFunction`, as a conjunction. -/
def IsTestFunctionNode (F : ℝ → ℂ) (δ₀ : ℝ) : Prop :=
  0 < δ₀ ∧
  MeasureTheory.Integrable (fun x : ℝ ↦ (Real.exp ((1 + 2 * δ₀) * Real.pi * |x|) : ℂ) * F x) ∧
  BoundedVariationOn (fun x : ℝ ↦ (Real.exp ((1 + 2 * δ₀) * Real.pi * |x|) : ℂ) * F x) Set.univ ∧
  (∀ x : ℝ, F x = (Function.leftLim F x + Function.rightLim F x) / 2) ∧
  (fun x : ℝ ↦ F x + F (-x) - 2 * F 0) =O[𝓝 0] (fun x : ℝ ↦ x)

/-- The node's right-hand side of (12.22) for `q = 1`. -/
def rhsNode (F : ℝ → ℂ) : ℂ :=
  Phi F 0 + Phi F 1
    + (Complex.digamma (1 / 4) - (Real.log Real.pi : ℂ)) * F 0 / (2 * Real.pi)
    - (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
        (F (-(Real.log n / (2 * Real.pi))) + F (Real.log n / (2 * Real.pi)))) / (2 * Real.pi)
    + ∫ x in Set.Ioi (0 : ℝ),
        ((Real.exp (-(Real.pi * x)) / (1 - Real.exp (-(4 * Real.pi * x))) : ℝ) : ℂ) *
          (2 * F 0 - F x - F (-x))

/-- **Weil's explicit formula**, Montgomery–Vaughan Theorem 12.13 with `q = 1`: the statement of
the conclusion `WeilExplicitFormula.v1.theorem_12_13` of the IEANTN draft node, verbatim. -/
def Theorem_12_13 : Prop :=
  ∀ (F : ℝ → ℂ) (δ₀ : ℝ), IsTestFunctionNode F δ₀ →
    Tendsto (fun T : ℝ ↦ zetaZeroesSum (Set.Ioo 0 1) (Set.Icc (-T) T) (Phi F)) atTop
      (𝓝 (rhsNode F))

theorem isTestFunction_of_node {F : ℝ → ℂ} {δ₀ : ℝ} (h : IsTestFunctionNode F δ₀) :
    IsTestFunction F δ₀ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem rhsNode_eq (F : ℝ → ℂ) : rhsNode F = rhs F := by
  simp only [rhsNode, rhs]
  ring

/-- **Weil's explicit formula** (Montgomery–Vaughan Theorem 12.13 with `q = 1`), in the form of the
IEANTN node `WeilExplicitFormula.v1`, from the conclusions it imports:
`ZetaGoodHeights.v1.theorem_10_13`, `ZetaGoodHeights.v1.lemma_12_2` and
`ContourIntegration.v1.residue_theorem_rectangle` (the facts from `ZetaZeroes.v1` are proved here
from Mathlib). -/
theorem theorem_12_13_of (h1013 : Theorem_10_13) (h122 : Lemma_12_2)
    (hres : ResidueTheoremRectangle) : Theorem_12_13 := by
  intro F δ₀ hF
  rw [rhsNode_eq]
  exact (isTestFunction_of_node hF).tendsto_zetaZeroesSum h1013 h122 hres

end WeilExplicitFormula
