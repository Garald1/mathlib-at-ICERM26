/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Harald Helfgott
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Analytic.Order

/-! # Riemann's `ξ` function, and the symmetry of `ζ` under conjugation

Part C1–C3 of the blueprint for Montgomery–Vaughan, *Multiplicative Number Theory I*,
Theorem 12.13 with `q = 1`.

`riemannXi s = (s(s-1) Λ₀(s) + 1)/2`, with Mathlib's entire `completedRiemannZeta₀ = Λ₀`, is
Riemann's `ξ(s) = ½ s(s-1) π^{-s/2} Γ(s/2) ζ(s)` (Montgomery–Vaughan (10.5)).

## Main results

* `differentiable_riemannXi`, `riemannXi_one_sub` (C1).
* `riemannXi_eq`: `ξ(s) = ½ s(s-1) Γ_ℝ(s) ζ(s)` for `Re s > 0`, `s ≠ 1` (C1).
* `riemannXi_eq_zero_iff`, `analyticOrderAt_riemannXi`: the zeros of `ξ` are the zeros of `ζ`
  in `0 < Re s < 1`, with the same multiplicities (C2).
* `logDeriv_riemannXi`: `ξ'/ξ(s) = 1/s + 1/(s-1) + ζ'/ζ(s) + ψ(s/2)/2 - (log π)/2` (C3,
  Montgomery–Vaughan (10.25)); `logDeriv_riemannXi_one_sub`: `ξ'/ξ(1-s) = -ξ'/ξ(s)`.
* `riemannZeta_conj`, `deriv_riemannZeta_conj`, `analyticOrderAt_riemannZeta_conj`:
  `ζ(s̄) = conj ζ(s)`, and the same for `ζ'` and for the order of vanishing (`s ≠ 1`).

The names and statements of C1–C3 are those of the draft
`blueprint/drafts/WeilExplicitFormula.lean` (branch `weil-explicit-formula`).

## AI usage

This file was written by Claude (Anthropic) in November 2026. It compiles, but has not been
reviewed by a human.
-/

@[expose] public section

open Real Complex Filter Topology Set
open scoped ComplexConjugate

noncomputable section

namespace WeilExplicitFormula

/-! ### `ξ` -/

/-- Riemann's `ξ(s) = ½ s (s-1) π^{-s/2} Γ(s/2) ζ(s)` (Montgomery–Vaughan (10.5)), written with
Mathlib's entire function `completedRiemannZeta₀`, so that it is visibly entire. -/
def riemannXi (s : ℂ) : ℂ := (s * (s - 1) * completedRiemannZeta₀ s + 1) / 2

/-- C1 -/
theorem differentiable_riemannXi : Differentiable ℂ riemannXi := by
  have h := differentiable_completedZeta₀
  unfold riemannXi
  fun_prop

/-- C1: the functional equation. -/
theorem riemannXi_one_sub (s : ℂ) : riemannXi (1 - s) = riemannXi s := by
  simp only [riemannXi, completedRiemannZeta₀_one_sub]
  ring

theorem riemannXi_zero : riemannXi 0 = 1 / 2 := by simp [riemannXi]

theorem riemannXi_one : riemannXi 1 = 1 / 2 := by simp [riemannXi]

theorem riemannXi_eq_completed {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    riemannXi s = s * (s - 1) / 2 * completedRiemannZeta s := by
  have h1 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.2 (Ne.symm hs1)
  rw [riemannXi, completedRiemannZeta_eq]
  field_simp
  ring

theorem ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) : s ≠ 0 := fun h ↦ by
  rw [h, zero_re] at hs
  exact lt_irrefl 0 hs

theorem ne_one_of_re_lt_one {s : ℂ} (hs : s.re < 1) : s ≠ 1 := fun h ↦ by
  rw [h, one_re] at hs
  exact lt_irrefl 1 hs

/-- C1: agreement with Montgomery–Vaughan (10.5) in the right half-plane. -/
theorem riemannXi_eq {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannXi s = s * (s - 1) / 2 * Gammaℝ s * riemannZeta s := by
  have hΓ := Gammaℝ_ne_zero_of_re_pos hs
  rw [riemannXi_eq_completed (ne_zero_of_re_pos hs) hs1,
    riemannZeta_def_of_ne_zero (ne_zero_of_re_pos hs)]
  field_simp

theorem riemannXi_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : riemannXi s ≠ 0 := by
  rcases eq_or_ne s 1 with rfl | hs1
  · rw [riemannXi_one]
    norm_num
  have hs0 : 0 < s.re := by linarith
  rw [riemannXi_eq hs0 hs1]
  exact mul_ne_zero (mul_ne_zero (div_ne_zero (mul_ne_zero (ne_zero_of_re_pos hs0)
    (sub_ne_zero.2 hs1)) two_ne_zero) (Gammaℝ_ne_zero_of_re_pos hs0))
    (riemannZeta_ne_zero_of_one_le_re hs)

theorem riemannXi_ne_zero_of_re_nonpos {s : ℂ} (hs : s.re ≤ 0) : riemannXi s ≠ 0 := by
  rw [← riemannXi_one_sub]
  exact riemannXi_ne_zero_of_one_le_re (by simp only [sub_re, one_re]; linarith)

/-- C2: the zeros of `ξ` are the non-trivial zeros of `ζ`. -/
theorem riemannXi_eq_zero_iff {s : ℂ} :
    riemannXi s = 0 ↔ riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 := by
  constructor
  · intro h
    have h0 : 0 < s.re := by
      by_contra h'
      exact riemannXi_ne_zero_of_re_nonpos (not_lt.1 h') h
    have h1 : s.re < 1 := by
      by_contra h'
      exact riemannXi_ne_zero_of_one_le_re (not_lt.1 h') h
    have hs1 := ne_one_of_re_lt_one h1
    refine ⟨?_, h0, h1⟩
    rw [riemannXi_eq h0 hs1] at h
    rcases mul_eq_zero.1 h with h' | h'
    · exfalso
      exact mul_ne_zero (div_ne_zero (mul_ne_zero (ne_zero_of_re_pos h0) (sub_ne_zero.2 hs1))
        two_ne_zero) (Gammaℝ_ne_zero_of_re_pos h0) h'
    · exact h'
  · rintro ⟨hz, h0, h1⟩
    rw [riemannXi_eq h0 (ne_one_of_re_lt_one h1), hz, mul_zero]

theorem differentiableAt_Gammaℝ {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ Gammaℝ s := by
  have h1 : DifferentiableAt ℂ (fun u : ℂ ↦ (π : ℂ) ^ (-u / 2)) s :=
    DifferentiableAt.const_cpow (by fun_prop) (Or.inl (ofReal_ne_zero.2 Real.pi_ne_zero))
  have h2 : DifferentiableAt ℂ (fun u : ℂ ↦ Complex.Gamma (u / 2)) s := by
    refine (differentiableAt_Gamma _ fun m h ↦ ?_).comp s (f := fun u : ℂ ↦ u / 2) (by fun_prop)
    have := congrArg re h
    simp only [div_ofNat_re, neg_re, natCast_re] at this
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have h3 : Gammaℝ = fun u ↦ (π : ℂ) ^ (-u / 2) * Complex.Gamma (u / 2) := funext Gammaℝ_def
  rw [h3]
  exact h1.mul h2

/-- Near a point of `Re s > 0`, `s ≠ 1`, `ξ` is `½ s(s-1) Γ_ℝ(s) ζ(s)`. -/
theorem riemannXi_eventuallyEq {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannXi =ᶠ[𝓝 s] fun u ↦ u * (u - 1) / 2 * Gammaℝ u * riemannZeta u := by
  filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hs,
    isOpen_ne.mem_nhds hs1] with u hu hu1
  exact riemannXi_eq hu hu1

/-- C2: with the same multiplicities. -/
theorem analyticOrderAt_riemannXi {s : ℂ} (hs : 0 < s.re) (hs1 : s.re < 1) :
    analyticOrderAt riemannXi s = analyticOrderAt riemannZeta s := by
  have hs1' := ne_one_of_re_lt_one hs1
  have hopen : IsOpen {u : ℂ | 0 < u.re ∧ u ≠ 1} :=
    (isOpen_lt continuous_const continuous_re).inter isOpen_ne
  have hA : AnalyticAt ℂ (fun u ↦ u * (u - 1) / 2 * Gammaℝ u) s := by
    refine DifferentiableOn.analyticAt (s := {u : ℂ | 0 < u.re ∧ u ≠ 1}) (fun u hu ↦ ?_)
      (hopen.mem_nhds ⟨hs, hs1'⟩)
    exact ((by fun_prop : DifferentiableAt ℂ (fun u : ℂ ↦ u * (u - 1) / 2) u).mul
      (differentiableAt_Gammaℝ hu.1)).differentiableWithinAt
  have hZ : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta s hs1'
  have hA0 : s * (s - 1) / 2 * Gammaℝ s ≠ 0 :=
    mul_ne_zero (div_ne_zero (mul_ne_zero (ne_zero_of_re_pos hs) (sub_ne_zero.2 hs1'))
      two_ne_zero) (Gammaℝ_ne_zero_of_re_pos hs)
  rw [analyticOrderAt_congr (riemannXi_eventuallyEq hs hs1')]
  change analyticOrderAt ((fun u ↦ u * (u - 1) / 2 * Gammaℝ u) * riemannZeta) s = _
  rw [analyticOrderAt_mul hA hZ, hA.analyticOrderAt_eq_zero.2 hA0, zero_add]

theorem logDeriv_Gammaℝ {s : ℂ} (hs : 0 < s.re) :
    logDeriv Gammaℝ s = -(Real.log π / 2) + digamma (s / 2) / 2 := by
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have hG : ∀ m : ℕ, s / 2 ≠ -m := fun m h ↦ by
    have := congrArg re h
    simp only [div_ofNat_re, neg_re, natCast_re] at this
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have h3 : Gammaℝ = fun u ↦ (π : ℂ) ^ (-u / 2) * (Complex.Gamma ∘ fun u : ℂ ↦ u / 2) u :=
    funext Gammaℝ_def
  have hd1 : HasDerivAt (fun u : ℂ ↦ (π : ℂ) ^ (-u / 2))
      ((π : ℂ) ^ (-s / 2) * Complex.log π * (-1 / 2)) s := by
    have : HasDerivAt (fun u : ℂ ↦ -u / 2) (-1 / 2) s := by
      simpa using ((hasDerivAt_id' s).neg.div_const 2)
    exact this.const_cpow (Or.inl hπ)
  have hc0 : (π : ℂ) ^ (-s / 2) ≠ 0 := cpow_ne_zero_iff.2 (Or.inl hπ)
  rw [h3, logDeriv_mul s hc0
      (show (Complex.Gamma ∘ fun u : ℂ ↦ u / 2) s ≠ 0 from Complex.Gamma_ne_zero hG)
      hd1.differentiableAt
      ((differentiableAt_Gamma _ hG).comp s (by fun_prop)),
    logDeriv_comp (g := fun u : ℂ ↦ u / 2) (x := s) (differentiableAt_Gamma _ hG) (by fun_prop),
    ← digamma_def]
  rw [logDeriv_apply, hd1.deriv, deriv_div_const, deriv_id'',
    ← ofReal_log Real.pi_pos.le]
  field_simp

/-- C3: Montgomery–Vaughan (10.25). -/
theorem logDeriv_riemannXi {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    logDeriv riemannXi s = 1 / s + 1 / (s - 1) + logDeriv riemannZeta s +
      digamma (s / 2) / 2 - Real.log π / 2 := by
  have hs0 := ne_zero_of_re_pos hs
  have hs10 : s - 1 ≠ 0 := sub_ne_zero.2 hs1
  have hev := riemannXi_eventuallyEq hs hs1
  have hlog : logDeriv riemannXi s =
      logDeriv (fun u ↦ u * (u - 1) / 2 * Gammaℝ u * riemannZeta u) s := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  have hp0 : s * (s - 1) / 2 ≠ 0 := div_ne_zero (mul_ne_zero hs0 hs10) two_ne_zero
  have hpd : DifferentiableAt ℂ (fun u : ℂ ↦ u * (u - 1) / 2) s := by fun_prop
  have hpoly : logDeriv (fun u : ℂ ↦ u * (u - 1) / 2) s = 1 / s + 1 / (s - 1) := by
    have hd : HasDerivAt (fun u : ℂ ↦ u * (u - 1) / 2) ((1 * (s - 1) + s * 1) / 2) s :=
      ((hasDerivAt_id' s).mul ((hasDerivAt_id' s).sub_const 1)).div_const 2
    rw [logDeriv_apply, hd.deriv]
    field_simp
  rw [hlog, logDeriv_mul (f := fun u ↦ u * (u - 1) / 2 * Gammaℝ u) s
      (mul_ne_zero hp0 (Gammaℝ_ne_zero_of_re_pos hs)) hz
      (hpd.mul (differentiableAt_Gammaℝ hs)) (differentiableAt_riemannZeta hs1),
    logDeriv_mul (f := fun u : ℂ ↦ u * (u - 1) / 2) s hp0 (Gammaℝ_ne_zero_of_re_pos hs) hpd
      (differentiableAt_Gammaℝ hs), hpoly, logDeriv_Gammaℝ hs]
  ring

/-- `ξ'/ξ(1 - s) = -ξ'/ξ(s)`. -/
theorem logDeriv_riemannXi_one_sub (s : ℂ) :
    logDeriv riemannXi (1 - s) = -logDeriv riemannXi s := by
  have h1 : HasDerivAt (riemannXi ∘ fun u ↦ 1 - u) (deriv riemannXi (1 - s) * (-1)) s :=
    (differentiable_riemannXi (1 - s)).hasDerivAt.comp s ((hasDerivAt_id' s).const_sub 1)
  have h2 : (riemannXi ∘ fun u ↦ 1 - u) = riemannXi := funext fun u ↦ riemannXi_one_sub u
  rw [h2] at h1
  have h3 : deriv riemannXi (1 - s) = -deriv riemannXi s := by
    rw [h1.deriv]
    ring
  rw [logDeriv_apply, logDeriv_apply, h3, riemannXi_one_sub, neg_div]

/-! ### Conjugation -/

theorem conj_ne_one_iff {u : ℂ} : conj u ≠ 1 ↔ u ≠ 1 := by
  rw [Ne, Ne, ← map_one (starRingEnd ℂ), (RingHom.injective (starRingEnd ℂ)).eq_iff, map_one]

/-- `ζ(s̄) = conj ζ(s)` for `s ≠ 1`. -/
theorem riemannZeta_conj {s : ℂ} (hs : s ≠ 1) :
    riemannZeta (conj s) = conj (riemannZeta s) := by
  have hUo : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
  have hUc : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by rw [rank_real_complex]; norm_num)
      1).isPreconnected
  have hg : AnalyticOnNhd ℂ (conj ∘ riemannZeta ∘ conj) {1}ᶜ := by
    refine DifferentiableOn.analyticOnNhd (fun u hu ↦ ?_) hUo
    have hu' : conj u ≠ 1 := conj_ne_one_iff.2 hu
    have := (differentiableAt_riemannZeta hu').hasDerivAt.conj_conj
    rw [conj_conj] at this
    exact this.differentiableAt.differentiableWithinAt
  have heq : riemannZeta =ᶠ[𝓝 2] (conj ∘ riemannZeta ∘ conj) := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with u hu
    have hu' : 1 < (conj u).re := by simpa using hu
    simp only [Function.comp]
    rw [zeta_eq_tsum_one_div_nat_cpow hu, zeta_eq_tsum_one_div_nat_cpow hu', Complex.conj_tsum]
    congr 1
    ext n
    have harg : (n : ℂ).arg ≠ Real.pi := by rw [natCast_arg]; exact Real.pi_ne_zero.symm
    rw [map_div₀, map_one, cpow_conj _ _ harg, conj_conj, map_natCast]
  have hall := analyticOn_riemannZeta.eqOn_of_preconnected_of_eventuallyEq hg hUc
    (show (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) by norm_num) heq
  have := hall (show conj s ∈ ({1}ᶜ : Set ℂ) from conj_ne_one_iff.2 hs)
  simpa only [Function.comp, conj_conj] using this

theorem conj_comp_riemannZeta_comp_conj_eventuallyEq {s : ℂ} (hs : s ≠ 1) :
    (conj ∘ riemannZeta ∘ conj) =ᶠ[𝓝 s] riemannZeta := by
  filter_upwards [isOpen_ne.mem_nhds hs] with u hu
  simp only [Function.comp, riemannZeta_conj hu, conj_conj]

theorem deriv_riemannZeta_conj {s : ℂ} (hs : s ≠ 1) :
    deriv riemannZeta (conj s) = conj (deriv riemannZeta s) := by
  have h := (conj_comp_riemannZeta_comp_conj_eventuallyEq (conj_ne_one_iff.2 hs)).deriv_eq
  rw [← h, deriv_conj_conj]
  simp only [Function.comp, conj_conj]

theorem logDeriv_riemannZeta_conj {s : ℂ} (hs : s ≠ 1) :
    logDeriv riemannZeta (conj s) = conj (logDeriv riemannZeta s) := by
  rw [logDeriv_apply, logDeriv_apply, deriv_riemannZeta_conj hs, riemannZeta_conj hs, map_div₀]

/-- The order of vanishing of `ζ` at `s̄` is that at `s` (`s ≠ 1`). -/
theorem analyticOrderAt_riemannZeta_conj {s : ℂ} (hs : s ≠ 1) :
    analyticOrderAt riemannZeta (conj s) = analyticOrderAt riemannZeta s := by
  have hs' : conj s ≠ 1 := conj_ne_one_iff.2 hs
  have hev : ∀ {P : ℂ → Prop}, (∀ᶠ u in 𝓝 s, P u) → ∀ᶠ w in 𝓝 (conj s), P (conj w) :=
    fun {P} h ↦ by
      have := (Complex.continuous_conj.tendsto (conj s)).eventually (p := P)
      rw [conj_conj] at this
      exact this h
  have hzeq : ∀ w, w ≠ 1 → riemannZeta w = conj (riemannZeta (conj w)) := fun w hw ↦ by
    rw [riemannZeta_conj hw, conj_conj]
  have hZs : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta s hs
  have hZs' : AnalyticAt ℂ riemannZeta (conj s) := analyticOn_riemannZeta (conj s) hs'
  cases hn : analyticOrderAt riemannZeta s with
  | top =>
    rw [analyticOrderAt_eq_top] at hn ⊢
    filter_upwards [hev hn, isOpen_ne.mem_nhds hs'] with w hw hw1
    rw [hzeq w hw1, hw, map_zero]
  | coe n =>
    obtain ⟨g, hga, hg0, hfg⟩ := hZs.analyticOrderAt_eq_natCast.1 hn
    rw [hZs'.analyticOrderAt_eq_natCast]
    refine ⟨conj ∘ g ∘ conj, ?_, ?_, ?_⟩
    · rw [analyticAt_iff_eventually_differentiableAt] at hga ⊢
      filter_upwards [hev hga] with w hw
      have := hw.hasDerivAt.conj_conj
      rw [conj_conj] at this
      exact this.differentiableAt
    · simpa only [Function.comp, conj_conj, ne_eq, map_eq_zero] using hg0
    · filter_upwards [hev hfg, isOpen_ne.mem_nhds hs'] with w hw hw1
      rw [hzeq w hw1, hw, smul_eq_mul, smul_eq_mul, map_mul, map_pow, map_sub, conj_conj]
      rfl

end WeilExplicitFormula
