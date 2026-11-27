/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Harald Helfgott
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.PSeries
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-! # Series and integral representations of the digamma function

Mathlib defines `Complex.digamma = logDeriv Gamma`. We prove, for `Re s > 0`:

* `Complex.hasSum_digamma`: `ψ(s) + γ = ∑_{k ≥ 0} (1/(k+1) - 1/(k+s))`;
* `Complex.hasSum_deriv_digamma`: `ψ'(s) = ∑_{k ≥ 0} (k+s)⁻²`;
* `Complex.hasSum_deriv_deriv_digamma`: `ψ''(s) = -2 ∑_{k ≥ 0} (k+s)⁻³`.

The series for `ψ` is first proved on `(0, ∞)`, using the log-convexity of `Γ`
(`Real.convexOn_log_Gamma`), which gives `log (x - 1) ≤ ψ(x) ≤ log x` for `x > 1`
(`Real.log_sub_one_le_digamma`, `Real.digamma_le_log`). It then extends to `Re s > 0` by the
identity theorem.

## AI usage

This file was written by Claude (Anthropic) in November 2026. It compiles, but has not been
reviewed by a human.
-/

@[expose] public section

open Filter Topology Set

/-! ### The digamma function on `(0, ∞)` -/

namespace Real

/-- `log Γ` has derivative `Γ'/Γ` on `(0, ∞)`. -/
theorem hasDerivAt_log_Gamma {x : ℝ} (hx : 0 < x) :
    HasDerivAt (log ∘ Gamma) (deriv Gamma x / Gamma x) x :=
  ((differentiableAt_Gamma fun m h ↦ by
    have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m); linarith).hasDerivAt.log
    (Gamma_pos_of_pos hx).ne')

/-- The log-convexity of `Γ` gives `ψ(x) ≤ log x` for `x > 0`. -/
theorem digamma_le_log {x : ℝ} (hx : 0 < x) : deriv Gamma x / Gamma x ≤ log x := by
  have h := convexOn_log_Gamma.deriv_le_slope (x := x) (y := x + 1) hx (by simp; linarith)
    (by linarith) (hasDerivAt_log_Gamma hx).differentiableAt
  rw [(hasDerivAt_log_Gamma hx).deriv, slope_def_field] at h
  simp only [Function.comp, Gamma_add_one hx.ne', add_sub_cancel_left, div_one] at h
  rwa [log_mul hx.ne' (Gamma_pos_of_pos hx).ne', add_sub_cancel_right] at h

/-- The log-convexity of `Γ` gives `log (x - 1) ≤ ψ(x)` for `x > 1`. -/
theorem log_sub_one_le_digamma {x : ℝ} (hx : 1 < x) :
    log (x - 1) ≤ deriv Gamma x / Gamma x := by
  have hx0 : 0 < x - 1 := by linarith
  have h := convexOn_log_Gamma.slope_le_deriv (x := x - 1) (y := x) hx0 (by simp; linarith)
    (by linarith) (hasDerivAt_log_Gamma (by linarith)).differentiableAt
  have hΓ : Gamma x = (x - 1) * Gamma (x - 1) := by
    simpa using Gamma_add_one hx0.ne'
  have hslope : slope (log ∘ Gamma) (x - 1) x = log (x - 1) := by
    rw [slope_def_field]
    simp only [Function.comp, sub_sub_cancel, div_one]
    rw [hΓ, log_mul hx0.ne' (Gamma_pos_of_pos hx0).ne', add_sub_cancel_right]
  rwa [hslope, (hasDerivAt_log_Gamma (by linarith)).deriv] at h

end Real

namespace Complex

/-- On `(0, ∞)` the digamma function is real: `ψ(x) = Γ'(x)/Γ(x)`. -/
theorem digamma_ofReal {x : ℝ} (hx : 0 < x) :
    digamma x = ((deriv Real.Gamma x / Real.Gamma x : ℝ) : ℂ) := by
  have hx' : ∀ m : ℕ, (x : ℂ) ≠ -m := fun m h ↦ by
    have := congrArg re h
    simp only [ofReal_re, neg_re, natCast_re] at this
    have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m); linarith
  have h1 : HasDerivAt (fun y : ℝ ↦ Gamma (y : ℂ)) (deriv Gamma (x : ℂ)) x :=
    (differentiableAt_Gamma _ hx').hasDerivAt.comp_ofReal
  have h2 : HasDerivAt (fun y : ℝ ↦ Gamma (y : ℂ)) ((deriv Real.Gamma x : ℝ) : ℂ) x := by
    simpa only [Gamma_ofReal] using
      (Real.differentiableAt_Gamma fun m h ↦ by
        have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m); linarith).hasDerivAt.ofReal_comp
  rw [digamma_def, logDeriv_apply, h1.unique h2, Gamma_ofReal, ofReal_div]

theorem digamma_add_one_ofReal {x : ℝ} (hx : 0 < x) :
    deriv Real.Gamma (x + 1) / Real.Gamma (x + 1) = deriv Real.Gamma x / Real.Gamma x + x⁻¹ := by
  have hx' : ∀ m : ℕ, (x : ℂ) ≠ -m := fun m h ↦ by
    have := congrArg re h
    simp only [ofReal_re, neg_re, natCast_re] at this
    have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m); linarith
  have h := digamma_apply_add_one (x : ℂ) hx'
  rw [← ofReal_one, ← ofReal_add, digamma_ofReal (by linarith), digamma_ofReal hx,
    ← ofReal_inv, ← ofReal_add, ofReal_inj] at h
  exact h

end Complex

namespace Real

open Complex in
/-- `ψ(x + n) = ψ(x) + ∑_{k < n} 1/(x + k)` on `(0, ∞)`. -/
theorem digamma_add_nat {x : ℝ} (hx : 0 < x) (n : ℕ) :
    deriv Gamma (x + n) / Gamma (x + n) =
      deriv Gamma x / Gamma x + ∑ k ∈ Finset.range n, 1 / (x + k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hxn : 0 < x + n := by positivity
    rw [Nat.cast_succ, ← add_assoc, digamma_add_one_ofReal hxn, ih, Finset.sum_range_succ,
      one_div (x + n), add_assoc]

/-- **Series for the digamma function on `(0, ∞)`**: `ψ(x) + γ = ∑_{k ≥ 0} (1/(k+1) - 1/(k+x))`. -/
theorem hasSum_digamma {x : ℝ} (hx : 0 < x) :
    HasSum (fun k : ℕ ↦ 1 / ((k : ℝ) + 1) - 1 / (k + x))
      (deriv Gamma x / Gamma x + eulerMascheroniConstant) := by
  set m := min x 1 with hm
  have hm0 : 0 < m := lt_min hx one_pos
  -- the terms are `O(1/k²)`
  have hbound : ∀ k : ℕ,
      ‖1 / ((k : ℝ) + 1) - 1 / (k + x)‖ ≤ |x - 1| / m * (1 / ((k : ℝ) + 1) ^ 2) := by
    intro k
    have hk1 : (0 : ℝ) < k + 1 := by positivity
    have hkx : (0 : ℝ) < k + x := by positivity
    have hkm : m * (k + 1) ≤ k + x := by
      have := min_le_left x 1; have := min_le_right x 1
      nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    rw [Real.norm_eq_abs, div_sub_div _ _ hk1.ne' hkx.ne', abs_div, abs_of_pos (mul_pos hk1 hkx),
      show (1 * (k + x) - (k + 1) * 1 : ℝ) = x - 1 by ring, div_le_iff₀ (mul_pos hk1 hkx)]
    calc |x - 1| = |x - 1| / m * (1 / ((k : ℝ) + 1) ^ 2) * (m * (k + 1) ^ 2) := by
          field_simp
      _ ≤ |x - 1| / m * (1 / ((k : ℝ) + 1) ^ 2) * ((k + 1) * (k + x)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          nlinarith
  have hsum : Summable fun k : ℕ ↦ ‖1 / ((k : ℝ) + 1) - 1 / (k + x)‖ := by
    refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hbound ?_
    refine Summable.mul_left _ ?_
    have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
    simpa [Nat.cast_add, Nat.cast_one] using this
  refine (hasSum_iff_tendsto_nat_of_summable_norm hsum).2 ?_
  -- partial sums
  have hpartial : ∀ n : ℕ, ∑ k ∈ Finset.range n, (1 / ((k : ℝ) + 1) - 1 / (k + x)) =
      ((harmonic n : ℝ) - log n) + (log n - deriv Gamma (x + n) / Gamma (x + n)) +
        deriv Gamma x / Gamma x := by
    intro n
    have hH : (harmonic n : ℝ) = ∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1) := by
      simp [harmonic, Rat.cast_sum, one_div]
    have hx' : ∑ k ∈ Finset.range n, 1 / ((k : ℝ) + x) = ∑ k ∈ Finset.range n, 1 / (x + k) :=
      Finset.sum_congr rfl fun k _ ↦ by rw [add_comm]
    rw [Finset.sum_sub_distrib, digamma_add_nat hx n, hH, hx']
    ring
  simp_rw [hpartial]
  have hlim : Tendsto (fun n : ℕ ↦ log n - deriv Gamma (x + n) / Gamma (x + n)) atTop (𝓝 0) := by
    -- squeeze between `log n - log (n + x)` and `log n - log (n + (x - 1))`
    have h₁ := (tendsto_log_comp_add_sub_log x).comp tendsto_natCast_atTop_atTop
    have h₂ := (tendsto_log_comp_add_sub_log (x - 1)).comp tendsto_natCast_atTop_atTop
    have h₁' : Tendsto (fun n : ℕ ↦ log n - log (n + x)) atTop (𝓝 0) := by
      simpa using h₁.neg
    have h₂' : Tendsto (fun n : ℕ ↦ log n - log (n + (x - 1))) atTop (𝓝 0) := by
      simpa using h₂.neg
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h₁' h₂' ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have := digamma_le_log (x := x + n) (by positivity)
      rw [add_comm x] at this ⊢
      linarith
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have := log_sub_one_le_digamma (x := x + n) (by linarith)
      rw [show x + n - 1 = n + (x - 1) by ring] at this
      linarith
  have := (tendsto_harmonic_sub_log.add hlim).add_const (deriv Gamma x / Gamma x)
  simpa [add_comm] using this

end Real

/-! ### The series for `ψ`, `ψ'` and `ψ''` on the right half-plane -/

namespace Complex

theorem ne_neg_natCast_of_re_pos {s : ℂ} (hs : 0 < s.re) (m : ℕ) : s ≠ -m := by
  intro h
  have := congrArg re h
  simp only [neg_re, natCast_re] at this
  have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  linarith

theorem natCast_add_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) (k : ℕ) : (k : ℂ) + s ≠ 0 := by
  intro h
  have := congrArg re h
  simp only [add_re, natCast_re, zero_re] at this
  have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  linarith

theorem natCast_add_re_le_norm (s : ℂ) (k : ℕ) : (k : ℝ) + s.re ≤ ‖(k : ℂ) + s‖ := by
  calc (k : ℝ) + s.re = ((k : ℂ) + s).re := by simp
    _ ≤ ‖(k : ℂ) + s‖ := re_le_norm _

theorem summable_one_div_nat_add_one_sq : Summable fun k : ℕ ↦ 1 / ((k : ℝ) + 1) ^ 2 := by
  have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
  simpa [Nat.cast_add, Nat.cast_one] using this

/-- The terms `1/(k+1) - 1/(k+s)` of the series for `ψ(s) + γ`. -/
noncomputable def digammaTerm (s : ℂ) (k : ℕ) : ℂ := 1 / ((k : ℂ) + 1) - 1 / (k + s)

theorem norm_digammaTerm_le {s : ℂ} {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hs : ε ≤ s.re)
    (k : ℕ) : ‖digammaTerm s k‖ ≤ (‖s‖ + 1) / ε * (1 / ((k : ℝ) + 1) ^ 2) := by
  have hk1 : (0 : ℝ) < k + 1 := by positivity
  have hk : (0 : ℝ) ≤ k := k.cast_nonneg
  have hks : ε * (k + 1) ≤ ‖(k : ℂ) + s‖ := by
    have := natCast_add_re_le_norm s k
    nlinarith
  have hks0 : (k : ℂ) + s ≠ 0 := natCast_add_ne_zero_of_re_pos (by linarith) k
  have hk10 : (k : ℂ) + 1 ≠ 0 := by
    have : ((k : ℂ) + 1) = ((k + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [this]; exact_mod_cast Nat.succ_ne_zero k
  have hn1 : ‖(k : ℂ) + 1‖ = k + 1 := by
    rw [show ((k : ℂ) + 1) = ((k + 1 : ℝ) : ℂ) by push_cast; ring, norm_real,
      Real.norm_of_nonneg hk1.le]
  rw [digammaTerm, div_sub_div _ _ hk10 hks0, norm_div, norm_mul, hn1,
    show (1 * ((k : ℂ) + s) - ((k : ℂ) + 1) * 1) = s - 1 by ring]
  have hpos : 0 < ‖(k : ℂ) + s‖ := norm_pos_iff.2 hks0
  rw [div_le_iff₀ (by positivity)]
  have hs1 : ‖s - 1‖ ≤ ‖s‖ + 1 := by simpa using norm_sub_le s 1
  calc ‖s - 1‖ ≤ ‖s‖ + 1 := hs1
    _ = (‖s‖ + 1) / ε * (1 / ((k : ℝ) + 1) ^ 2) * (ε * (k + 1) * (k + 1)) := by
        field_simp
    _ ≤ (‖s‖ + 1) / ε * (1 / ((k : ℝ) + 1) ^ 2) * ((k + 1) * ‖(k : ℂ) + s‖) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith

theorem summable_digammaTerm {s : ℂ} (hs : 0 < s.re) : Summable (digammaTerm s) :=
  Summable.of_norm_bounded (summable_one_div_nat_add_one_sq.mul_left ((‖s‖ + 1) / min s.re 1))
    fun k ↦ norm_digammaTerm_le (lt_min hs one_pos) (min_le_right _ _) (min_le_left _ _) k

/-- Each point of the right half-plane has an open neighbourhood on which the terms of the series
for `ψ` are bounded by a summable sequence. -/
theorem exists_nhds_digammaTerm_le {s₀ : ℂ} (hs₀ : 0 < s₀.re) :
    ∃ V : Set ℂ, IsOpen V ∧ s₀ ∈ V ∧ (∀ w ∈ V, 0 < w.re) ∧ ∃ u : ℕ → ℝ, Summable u ∧
      ∀ k, ∀ w ∈ V, ‖digammaTerm w k‖ ≤ u k := by
  set ε := min (s₀.re / 2) 1 with hε_def
  have hε : 0 < ε := lt_min (by linarith) one_pos
  refine ⟨{s | ε < s.re} ∩ Metric.ball 0 (‖s₀‖ + 1),
    (isOpen_lt continuous_const continuous_re).inter Metric.isOpen_ball, ⟨?_, by simp⟩,
    fun w hw ↦ lt_trans hε hw.1, fun k ↦ (‖s₀‖ + 1 + 1) / ε * (1 / ((k : ℝ) + 1) ^ 2),
    summable_one_div_nat_add_one_sq.mul_left _, fun k w hw ↦ ?_⟩
  · change ε < s₀.re
    have := min_le_left (s₀.re / 2) 1
    linarith
  · have hwR : ‖w‖ < ‖s₀‖ + 1 := by simpa using hw.2
    calc ‖digammaTerm w k‖ ≤ (‖w‖ + 1) / ε * (1 / ((k : ℝ) + 1) ^ 2) :=
          norm_digammaTerm_le hε (min_le_right _ _) hw.1.le k
      _ ≤ (‖s₀‖ + 1 + 1) / ε * (1 / ((k : ℝ) + 1) ^ 2) := by gcongr

theorem hasDerivAt_digammaTerm {s : ℂ} (hs : 0 < s.re) (k : ℕ) :
    HasDerivAt (fun w ↦ digammaTerm w k) (1 / ((k : ℂ) + s) ^ 2) s := by
  have h := ((hasDerivAt_id s).const_add (k : ℂ)).inv (natCast_add_ne_zero_of_re_pos hs k)
  have h2 := (hasDerivAt_const s (1 / ((k : ℂ) + 1))).sub h
  convert h2 using 1
  · funext w
    simp [digammaTerm, one_div]
  · simp only [id_eq]
    ring

theorem differentiableOn_tsum_digammaTerm :
    DifferentiableOn ℂ (fun s ↦ ∑' k, digammaTerm s k) {s | 0 < s.re} := by
  intro s₀ hs₀
  obtain ⟨V, hVo, hs₀V, hVpos, u, hu, hbound⟩ := exists_nhds_digammaTerm_le hs₀
  have hd : DifferentiableOn ℂ (fun w ↦ ∑' k, digammaTerm w k) V :=
    differentiableOn_tsum_of_summable_norm (F := fun k w ↦ digammaTerm w k) hu
      (fun k w hw ↦ (hasDerivAt_digammaTerm (hVpos w hw) k).differentiableAt.differentiableWithinAt)
      hVo hbound
  exact (hd.differentiableAt (hVo.mem_nhds hs₀V)).differentiableWithinAt

theorem differentiableOn_digamma : DifferentiableOn ℂ digamma {s | 0 < s.re} := by
  have hU : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const continuous_re
  have hΓ : DifferentiableOn ℂ Gamma {s | 0 < s.re} := fun s hs ↦
    (differentiableAt_Gamma s (ne_neg_natCast_of_re_pos hs)).differentiableWithinAt
  have hΓ' : DifferentiableOn ℂ (deriv Gamma) {s | 0 < s.re} :=
    (hΓ.analyticOnNhd hU).deriv.differentiableOn
  have h := hΓ'.div hΓ fun s hs ↦ Gamma_ne_zero_of_re_pos hs
  rwa [show digamma = fun s ↦ deriv Gamma s / Gamma s from funext fun s ↦ by
    rw [digamma_def, logDeriv_apply]]

theorem analyticOnNhd_digamma : AnalyticOnNhd ℂ digamma {s | 0 < s.re} :=
  differentiableOn_digamma.analyticOnNhd (isOpen_lt continuous_const continuous_re)

/-- **Series for the digamma function**: for `Re s > 0`,
`ψ(s) + γ = ∑_{k ≥ 0} (1/(k+1) - 1/(k+s))`. -/
theorem hasSum_digamma {s : ℂ} (hs : 0 < s.re) :
    HasSum (digammaTerm s) (digamma s + Real.eulerMascheroniConstant) := by
  have hU : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const continuous_re
  have hpre : IsPreconnected {s : ℂ | 0 < s.re} := (convex_halfSpace_re_gt 0).isPreconnected
  have hf : AnalyticOnNhd ℂ (fun s ↦ digamma s + Real.eulerMascheroniConstant)
      {s | 0 < s.re} :=
    (differentiableOn_digamma.add_const _).analyticOnNhd hU
  have hg : AnalyticOnNhd ℂ (fun s ↦ ∑' k, digammaTerm s k) {s | 0 < s.re} :=
    differentiableOn_tsum_digammaTerm.analyticOnNhd hU
  have hreal : ∀ x : ℝ, 0 < x →
      digamma x + Real.eulerMascheroniConstant = ∑' k, digammaTerm x k := by
    intro x hx
    rw [digamma_ofReal hx, ← ofReal_add]
    refine (HasSum.tsum_eq ?_).symm
    convert hasSum_ofReal.2 (Real.hasSum_digamma hx) using 1
    funext k
    simp [digammaTerm]
  have hfreq : ∃ᶠ z in 𝓝[≠] (1 : ℂ),
      digamma z + Real.eulerMascheroniConstant = ∑' k, digammaTerm z k := by
    have hmap : Tendsto (fun x : ℝ ↦ (x : ℂ)) (𝓝[≠] 1) (𝓝[≠] 1) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have := (continuous_ofReal.tendsto 1).mono_left (nhdsWithin_le_nhds (s := {(1 : ℝ)}ᶜ))
        simpa using this
      · filter_upwards [self_mem_nhdsWithin] with x hx
        simpa [ofReal_eq_one] using hx
    refine hmap.frequently (Eventually.frequently ?_)
    filter_upwards [nhdsWithin_le_nhds (lt_mem_nhds one_pos)] with x hx using hreal x hx
  have heq := hf.eqOn_of_preconnected_of_frequently_eq hg hpre (by simp) hfreq hs
  simp only at heq
  rw [heq]
  exact (summable_digammaTerm hs).hasSum

/-- For `Re s > 0`, `ψ'(s) = ∑_{k ≥ 0} 1/(k+s)²`. -/
theorem hasSum_deriv_digamma {s : ℂ} (hs : 0 < s.re) :
    HasSum (fun k : ℕ ↦ 1 / ((k : ℂ) + s) ^ 2) (deriv digamma s) := by
  have hU : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const continuous_re
  obtain ⟨V, hVo, hsV, hVpos, u, hu, hbound⟩ := exists_nhds_digammaTerm_le hs
  have h := hasSum_deriv_of_summable_norm (F := fun k w ↦ digammaTerm w k) hu
      (fun k w hw ↦ (hasDerivAt_digammaTerm (hVpos w hw) k).differentiableAt.differentiableWithinAt)
      hVo hbound hsV
  have heq : deriv digamma s = deriv (fun w ↦ ∑' k, digammaTerm w k) s := by
    have : (fun w ↦ digamma w + Real.eulerMascheroniConstant) =ᶠ[𝓝 s]
        fun w ↦ ∑' k, digammaTerm w k := by
      filter_upwards [hU.mem_nhds hs] with w hw using (hasSum_digamma hw).tsum_eq.symm
    rw [← this.deriv_eq, deriv_add_const]
  rw [heq]
  convert h using 1
  funext k
  exact (hasDerivAt_digammaTerm hs k).deriv.symm

theorem hasDerivAt_one_div_natCast_add_sq {s : ℂ} (hs : 0 < s.re) (k : ℕ) :
    HasDerivAt (fun w ↦ 1 / ((k : ℂ) + w) ^ 2) (-2 / ((k : ℂ) + s) ^ 3) s := by
  have hks := natCast_add_ne_zero_of_re_pos hs k
  have h1 : HasDerivAt (fun w : ℂ ↦ (k : ℂ) + w) 1 s := (hasDerivAt_id s).const_add _
  have h3 := (hasDerivAt_const s (1 : ℂ)).div (h1.mul h1) (mul_ne_zero hks hks)
  convert h3 using 1
  · funext w
    simp only [Pi.div_apply, Pi.mul_apply]
    ring
  · simp only [Pi.mul_apply]
    field_simp
    ring

/-- For `Re s > 0`, `ψ''(s) = -2 ∑_{k ≥ 0} 1/(k+s)³`. -/
theorem hasSum_deriv_deriv_digamma {s : ℂ} (hs : 0 < s.re) :
    HasSum (fun k : ℕ ↦ -2 / ((k : ℂ) + s) ^ 3) (deriv (deriv digamma) s) := by
  have hU : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const continuous_re
  set ε := min (s.re / 2) 1 with hε_def
  have hε : 0 < ε := lt_min (by linarith) one_pos
  have hsV : s ∈ {w : ℂ | ε < w.re} := by
    change ε < s.re
    have := min_le_left (s.re / 2) 1
    linarith
  have hbound : ∀ (k : ℕ) (w : ℂ), w ∈ {w : ℂ | ε < w.re} →
      ‖1 / ((k : ℂ) + w) ^ 2‖ ≤ 1 / ε ^ 2 * (1 / ((k : ℝ) + 1) ^ 2) := by
    intro k w hw
    have hk : (0 : ℝ) ≤ k := k.cast_nonneg
    have hkw : ε * (k + 1) ≤ ‖(k : ℂ) + w‖ := by
      have := natCast_add_re_le_norm w k
      have := min_le_right (s.re / 2) 1
      have hw' : ε < w.re := hw
      nlinarith
    have hpos : 0 < ‖(k : ℂ) + w‖ := lt_of_lt_of_le (by positivity) hkw
    rw [norm_div, norm_one, norm_pow, div_le_iff₀ (pow_pos hpos 2)]
    calc (1 : ℝ) = 1 / ε ^ 2 * (1 / ((k : ℝ) + 1) ^ 2) * (ε * (k + 1)) ^ 2 := by field_simp
      _ ≤ 1 / ε ^ 2 * (1 / ((k : ℝ) + 1) ^ 2) * ‖(k : ℂ) + w‖ ^ 2 := by
          gcongr
  have h := hasSum_deriv_of_summable_norm (F := fun (k : ℕ) w ↦ 1 / ((k : ℂ) + w) ^ 2)
    (summable_one_div_nat_add_one_sq.mul_left _)
    (fun k w hw ↦ (hasDerivAt_one_div_natCast_add_sq (lt_trans hε hw) k).differentiableAt
      |>.differentiableWithinAt)
    (isOpen_lt continuous_const continuous_re) hbound hsV
  have heq : deriv (deriv digamma) s = deriv (fun w ↦ ∑' k : ℕ, 1 / ((k : ℂ) + w) ^ 2) s := by
    have : deriv digamma =ᶠ[𝓝 s] fun w ↦ ∑' k : ℕ, 1 / ((k : ℂ) + w) ^ 2 := by
      filter_upwards [hU.mem_nhds hs] with w hw using (hasSum_deriv_digamma hw).tsum_eq.symm
    exact this.deriv_eq
  rw [heq]
  convert h using 1
  funext k
  exact (hasDerivAt_one_div_natCast_add_sq hs k).deriv.symm

end Complex

/-! ### An integral representation of `ψ''` -/

namespace Complex

open MeasureTheory

theorem integrableOn_sq_mul_cexp_neg_mul_Ioi {c : ℂ} (hc : 0 < c.re) :
    IntegrableOn (fun u : ℝ ↦ (u : ℂ) ^ 2 * cexp (-(c * u))) (Ioi 0) := by
  have hr : IntegrableOn (fun u : ℝ ↦ u ^ (2 : ℝ) * Real.exp (-c.re * u ^ (1 : ℝ))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) le_rfl hc
  refine Integrable.mono' hr (Continuous.aestronglyMeasurable (by fun_prop)) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u _ ↦ ?_)
  rw [norm_mul, norm_pow, norm_real, Real.norm_eq_abs, sq_abs, norm_exp, Real.rpow_two,
    Real.rpow_one]
  simp [neg_mul]

/-- `∫_0^∞ u² e^{-cu} du = 2/c³` for `Re c > 0`. -/
theorem integral_sq_mul_cexp_neg_mul_Ioi {c : ℂ} (hc : 0 < c.re) :
    ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ 2 * cexp (-(c * u)) = 2 / c ^ 3 := by
  have hc0 : c ≠ 0 := by rintro rfl; simp at hc
  set G : ℂ → ℂ := fun z ↦ -(cexp (-(c * z)) * (z ^ 2 / c + 2 * z / c ^ 2 + 2 / c ^ 3))
    with hG_def
  have hG : ∀ z : ℂ, HasDerivAt G (z ^ 2 * cexp (-(c * z))) z := by
    intro z
    have h1 : HasDerivAt (fun z : ℂ ↦ cexp (-(c * z))) (cexp (-(c * z)) * -(c * 1)) z :=
      ((hasDerivAt_id z).const_mul c).neg.cexp
    have h2 : HasDerivAt (fun z : ℂ ↦ z ^ 2 / c + 2 * z / c ^ 2 + 2 / c ^ 3)
        (2 * z / c + 2 / c ^ 2) z := by
      have := (((hasDerivAt_pow 2 z).div_const c).add
        (((hasDerivAt_id z).const_mul (2 : ℂ)).div_const (c ^ 2))).add_const (2 / c ^ 3)
      convert this using 1
      simp only [Nat.cast_ofNat, mul_one]
      ring
    convert (h1.mul h2).neg using 1
    field_simp
    ring
  have hF : ∀ u : ℝ, HasDerivAt (fun u : ℝ ↦ G u) ((u : ℂ) ^ 2 * cexp (-(c * u))) u :=
    fun u ↦ (hG u).comp_ofReal
  have key : ∀ n : ℕ, Tendsto (fun u : ℝ ↦ u ^ n * Real.exp (-(c.re * u))) atTop (𝓝 0) := by
    intro n
    have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).comp
      (tendsto_id.const_mul_atTop hc)).div_const (c.re ^ n)
    rw [zero_div] at h
    refine h.congr fun u ↦ ?_
    simp only [Function.comp, id_eq, mul_pow]
    field_simp
  have hlim : Tendsto (fun u : ℝ ↦ G u) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hbound : Tendsto (fun u : ℝ ↦ u ^ 2 * Real.exp (-(c.re * u)) / ‖c‖ +
        2 * (u ^ 1 * Real.exp (-(c.re * u))) / ‖c‖ ^ 2 +
        2 * (u ^ 0 * Real.exp (-(c.re * u))) / ‖c‖ ^ 3) atTop (𝓝 0) := by
      have := (((key 2).div_const ‖c‖).add (((key 1).const_mul 2).div_const (‖c‖ ^ 2))).add
        (((key 0).const_mul 2).div_const (‖c‖ ^ 3))
      simpa using this
    refine squeeze_zero' (Eventually.of_forall fun u ↦ norm_nonneg _) ?_ hbound
    filter_upwards [eventually_ge_atTop 0] with u hu
    simp only [hG_def, norm_neg, norm_mul, norm_exp, pow_one, pow_zero, one_mul]
    have he : (-(c * (u : ℂ))).re = -(c.re * u) := by simp
    rw [he]
    have hP : ‖(u : ℂ) ^ 2 / c + 2 * u / c ^ 2 + 2 / c ^ 3‖ ≤
        u ^ 2 / ‖c‖ + 2 * u / ‖c‖ ^ 2 + 2 / ‖c‖ ^ 3 := by
      refine (norm_add₃_le).trans (le_of_eq ?_)
      simp [norm_pow, Real.norm_eq_abs, abs_of_nonneg hu]
    calc Real.exp (-(c.re * u)) * ‖(u : ℂ) ^ 2 / c + 2 * u / c ^ 2 + 2 / c ^ 3‖
        ≤ Real.exp (-(c.re * u)) * (u ^ 2 / ‖c‖ + 2 * u / ‖c‖ ^ 2 + 2 / ‖c‖ ^ 3) :=
          mul_le_mul_of_nonneg_left hP (Real.exp_pos _).le
      _ = _ := by ring
  rw [integral_Ioi_of_hasDerivAt_of_tendsto (hF 0).continuousAt.continuousWithinAt
    (fun u _ ↦ hF u) (integrableOn_sq_mul_cexp_neg_mul_Ioi hc) hlim]
  simp only [hG_def, ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, one_mul]
  ring

/-- For `Re s > 0`, `ψ''(s) = -∫_0^∞ u² e^{-su} / (1 - e^{-u}) du`. -/
theorem deriv_deriv_digamma_eq_integral {s : ℂ} (hs : 0 < s.re) :
    deriv (deriv digamma) s =
      -∫ u in Ioi (0 : ℝ), (u : ℂ) ^ 2 * cexp (-(s * u)) / (1 - cexp (-(u : ℂ))) := by
  set f : ℕ → ℝ → ℂ := fun k u ↦ (u : ℂ) ^ 2 * cexp (-(((k : ℂ) + s) * u)) with hf_def
  have hre : ∀ k : ℕ, 0 < ((k : ℂ) + s).re := fun k ↦ by
    simp only [add_re, natCast_re]; positivity
  have hf_int : ∀ k, Integrable (f k) (volume.restrict (Ioi 0)) := fun k ↦
    integrableOn_sq_mul_cexp_neg_mul_Ioi (hre k)
  have hf_norm : ∀ k : ℕ, ∫ u in Ioi (0 : ℝ), ‖f k u‖ = 2 / ((k : ℝ) + s.re) ^ 3 := by
    intro k
    have hk : 0 < (k : ℝ) + s.re := by positivity
    have h := integral_sq_mul_cexp_neg_mul_Ioi (c := ((k + s.re : ℝ) : ℂ)) (by simpa using hk)
    have hnorm : ∀ u : ℝ, ‖f k u‖ = u ^ 2 * Real.exp (-((k + s.re) * u)) := by
      intro u
      simp only [hf_def, norm_mul, norm_pow, norm_real, Real.norm_eq_abs, sq_abs, norm_exp]
      congr 2
      simp
    have hcast : ∀ u : ℝ, (u : ℂ) ^ 2 * cexp (-(((k + s.re : ℝ) : ℂ) * u)) =
        ((u ^ 2 * Real.exp (-((k + s.re) * u)) : ℝ) : ℂ) := by
      intro u
      push_cast
      rfl
    simp_rw [hcast, integral_complex_ofReal] at h
    simp_rw [hnorm]
    have h2 : (2 : ℂ) / ((k + s.re : ℝ) : ℂ) ^ 3 = ((2 / ((k : ℝ) + s.re) ^ 3 : ℝ) : ℂ) := by
      push_cast; ring
    rw [h2] at h
    exact_mod_cast h
  have hsum : Summable fun k ↦ ∫ u in Ioi (0 : ℝ), ‖f k u‖ := by
    simp_rw [hf_norm]
    set m := min s.re 1
    have hm : 0 < m := lt_min hs one_pos
    refine Summable.of_nonneg_of_le (fun k ↦ by positivity) (fun k ↦ ?_)
      ((summable_one_div_nat_add_one_sq.mul_left (2 / m ^ 3)))
    have hk : (0 : ℝ) ≤ k := k.cast_nonneg
    have h1 : m * (k + 1) ≤ k + s.re := by
      have := min_le_left s.re 1; have := min_le_right s.re 1; nlinarith
    calc 2 / ((k : ℝ) + s.re) ^ 3 ≤ 2 / (m * (k + 1)) ^ 3 := by gcongr
      _ = 2 / m ^ 3 * (1 / ((k : ℝ) + 1) ^ 3) := by rw [mul_pow, div_mul_div_comm, mul_one]
      _ ≤ 2 / m ^ 3 * (1 / ((k : ℝ) + 1) ^ 2) := by
          gcongr
          · exact le_add_of_nonneg_left hk
          · norm_num
  have hFub := integral_tsum_of_summable_integral_norm hf_int hsum
  have hgeom : ∀ u ∈ Ioi (0 : ℝ), ∑' k, f k u =
      (u : ℂ) ^ 2 * cexp (-(s * u)) / (1 - cexp (-(u : ℂ))) := by
    intro u hu
    have hr : ‖cexp (-(u : ℂ))‖ < 1 := by
      rw [norm_exp]
      simp only [neg_re, ofReal_re]
      exact Real.exp_lt_one_iff.2 (neg_neg_of_pos hu)
    have := (hasSum_geometric_of_norm_lt_one hr).mul_left ((u : ℂ) ^ 2 * cexp (-(s * u)))
    rw [div_eq_mul_inv, ← this.tsum_eq]
    congr 1
    funext k
    simp only [hf_def, ← Complex.exp_nat_mul, mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  rw [← (hasSum_deriv_deriv_digamma hs).tsum_eq, ← setIntegral_congr_fun measurableSet_Ioi hgeom,
    ← hFub]
  rw [← tsum_neg]
  congr 1
  funext k
  simp only [hf_def]
  rw [integral_sq_mul_cexp_neg_mul_Ioi (hre k)]
  ring

end Complex

/-! ### Bounds on vertical lines -/

namespace Complex

/-- `∑_{k ≥ 0} 1/(k+c)² ≤ 1/c² + 1/c` for `c > 0`. -/
theorem tsum_one_div_nat_add_sq_le {c : ℝ} (hc : 0 < c) :
    ∑' k : ℕ, 1 / ((k : ℝ) + c) ^ 2 ≤ 1 / c ^ 2 + 1 / c := by
  have hstep : ∀ n : ℕ, ∑ k ∈ Finset.range (n + 1), 1 / ((k : ℝ) + c) ^ 2 ≤
      1 / c ^ 2 + 1 / c - 1 / (n + c) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have hx : (0 : ℝ) < n + c := by positivity
      have h1 : 1 / ((n : ℝ) + 1 + c) ^ 2 ≤ 1 / (n + c) - 1 / (n + 1 + c) := by
        rw [div_sub_div _ _ hx.ne' (by positivity), one_mul, mul_one,
          show (n : ℝ) + 1 + c - (n + c) = 1 by ring]
        exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
      push_cast
      linarith
  refine Real.tsum_le_of_sum_range_le (fun k ↦ by positivity) fun n ↦ ?_
  rcases n with _ | n
  · rw [Finset.sum_range_zero]; positivity
  · have := hstep n
    have : 0 ≤ 1 / ((n : ℝ) + c) := by positivity
    linarith

/-- `∑_{k ≥ 0} 1/(k+c)³ ≤ 1/c³ + 1/(2c²)` for `c > 0`. -/
theorem tsum_one_div_nat_add_cube_le {c : ℝ} (hc : 0 < c) :
    ∑' k : ℕ, 1 / ((k : ℝ) + c) ^ 3 ≤ 1 / c ^ 3 + 1 / (2 * c ^ 2) := by
  have hstep : ∀ n : ℕ, ∑ k ∈ Finset.range (n + 1), 1 / ((k : ℝ) + c) ^ 3 ≤
      1 / c ^ 3 + 1 / (2 * c ^ 2) - 1 / (2 * (n + c) ^ 2) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have hx : (0 : ℝ) < n + c := by positivity
      have h1 : 1 / ((n : ℝ) + 1 + c) ^ 3 ≤
          1 / (2 * (n + c) ^ 2) - 1 / (2 * (n + 1 + c) ^ 2) := by
        rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
          (by positivity)]
        nlinarith [pow_pos hx 2, pow_pos hx 3, pow_pos hx 4, pow_pos hx 5]
      push_cast
      linarith
  refine Real.tsum_le_of_sum_range_le (fun k ↦ by positivity) fun n ↦ ?_
  rcases n with _ | n
  · rw [Finset.sum_range_zero]; positivity
  · have := hstep n
    have : 0 ≤ 1 / (2 * ((n : ℝ) + c) ^ 2) := by positivity
    linarith

theorem add_abs_le_two_mul_norm (a t : ℝ) (k : ℕ) :
    (k : ℝ) + a + |t| ≤ 2 * ‖(k : ℂ) + (a + t * I)‖ := by
  have h1 : (k : ℝ) + a ≤ ‖(k : ℂ) + (a + t * I)‖ := by
    simpa using natCast_add_re_le_norm (a + t * I) k
  have h2 : |t| ≤ ‖(k : ℂ) + (a + t * I)‖ := by
    have := abs_im_le_norm ((k : ℂ) + (a + t * I))
    simpa using this
  linarith

theorem add_abs_sq_le_two_mul_norm_sq (a t : ℝ) (k : ℕ) :
    ((k : ℝ) + a + |t|) ^ 2 ≤ 2 * ‖(k : ℂ) + (a + t * I)‖ ^ 2 := by
  have hn : ‖(k : ℂ) + (a + t * I)‖ ^ 2 = ((k : ℝ) + a) ^ 2 + t ^ 2 := by
    rw [← normSq_eq_norm_sq, normSq_apply]
    simp
    ring
  rw [hn]
  nlinarith [sq_abs t, abs_nonneg t, sq_nonneg ((k : ℝ) + a - |t|)]

/-- On the vertical line `Re s = a > 0`, `|ψ'(a + it)| ≤ 2 (1/(a+|t|)² + 1/(a+|t|))`. -/
theorem norm_deriv_digamma_le {a : ℝ} (ha : 0 < a) (t : ℝ) :
    ‖deriv digamma (a + t * I)‖ ≤ 2 * (1 / (a + |t|) ^ 2 + 1 / (a + |t|)) := by
  have hs : 0 < (a + t * I : ℂ).re := by simpa using ha
  have hc : 0 < a + |t| := by positivity
  have hsum : Summable fun k : ℕ ↦ 1 / ((k : ℝ) + (a + |t|)) ^ 2 := by
    refine Summable.of_nonneg_of_le (fun k ↦ by positivity) (fun k ↦ ?_)
      (summable_one_div_nat_add_one_sq.mul_left (1 / min (a + |t|) 1 ^ 2))
    have hk : (0 : ℝ) ≤ k := k.cast_nonneg
    have h1 : min (a + |t|) 1 * (k + 1) ≤ k + (a + |t|) := by
      have := min_le_left (a + |t|) 1; have := min_le_right (a + |t|) 1; nlinarith
    have hm : 0 < min (a + |t|) 1 := lt_min hc one_pos
    calc 1 / ((k : ℝ) + (a + |t|)) ^ 2 ≤ 1 / (min (a + |t|) 1 * (k + 1)) ^ 2 := by
          gcongr
      _ = 1 / min (a + |t|) 1 ^ 2 * (1 / ((k : ℝ) + 1) ^ 2) := by
          rw [mul_pow, div_mul_div_comm, mul_one]
  rw [← (hasSum_deriv_digamma hs).tsum_eq]
  calc ‖∑' k : ℕ, 1 / ((k : ℂ) + (a + t * I)) ^ 2‖
      ≤ ∑' k : ℕ, 2 * (1 / ((k : ℝ) + (a + |t|)) ^ 2) := by
        refine tsum_of_norm_bounded (hsum.mul_left 2).hasSum fun k ↦ ?_
        have hpos : 0 < ‖(k : ℂ) + (a + t * I)‖ := by
          have := add_abs_le_two_mul_norm a t k
          have : 0 < (k : ℝ) + a + |t| := by positivity
          linarith
        rw [norm_div, norm_one, norm_pow, div_le_iff₀ (pow_pos hpos 2)]
        have := add_abs_sq_le_two_mul_norm_sq a t k
        calc (1 : ℝ) = 2 * (1 / ((k : ℝ) + (a + |t|)) ^ 2) * (((k : ℝ) + a + |t|) ^ 2 / 2) := by
              field_simp
              ring
          _ ≤ 2 * (1 / ((k : ℝ) + (a + |t|)) ^ 2) * ‖(k : ℂ) + (a + t * I)‖ ^ 2 := by
              gcongr
              linarith
    _ = 2 * ∑' k : ℕ, 1 / ((k : ℝ) + (a + |t|)) ^ 2 := tsum_mul_left
    _ ≤ 2 * (1 / (a + |t|) ^ 2 + 1 / (a + |t|)) := by
        gcongr
        exact tsum_one_div_nat_add_sq_le hc

/-- On the vertical line `Re s = a > 0`, `|ψ''(a + it)| ≤ 8 (1/(a+|t|)³ + 1/(2(a+|t|)²))`. -/
theorem norm_deriv_deriv_digamma_le {a : ℝ} (ha : 0 < a) (t : ℝ) :
    ‖deriv (deriv digamma) (a + t * I)‖ ≤
      8 * (1 / (a + |t|) ^ 3 + 1 / (2 * (a + |t|) ^ 2)) := by
  have hs : 0 < (a + t * I : ℂ).re := by simpa using ha
  have hc : 0 < a + |t| := by positivity
  have hsum : Summable fun k : ℕ ↦ 1 / ((k : ℝ) + (a + |t|)) ^ 3 := by
    refine Summable.of_nonneg_of_le (fun k ↦ by positivity) (fun k ↦ ?_)
      (summable_one_div_nat_add_one_sq.mul_left (1 / min (a + |t|) 1 ^ 3))
    have hk : (0 : ℝ) ≤ k := k.cast_nonneg
    have h1 : min (a + |t|) 1 * (k + 1) ≤ k + (a + |t|) := by
      have := min_le_left (a + |t|) 1; have := min_le_right (a + |t|) 1; nlinarith
    have hm : 0 < min (a + |t|) 1 := lt_min hc one_pos
    calc 1 / ((k : ℝ) + (a + |t|)) ^ 3 ≤ 1 / (min (a + |t|) 1 * (k + 1)) ^ 3 := by
          gcongr
      _ = 1 / min (a + |t|) 1 ^ 3 * (1 / ((k : ℝ) + 1) ^ 3) := by
          rw [mul_pow, div_mul_div_comm, mul_one]
      _ ≤ 1 / min (a + |t|) 1 ^ 3 * (1 / ((k : ℝ) + 1) ^ 2) := by
          gcongr
          · exact le_add_of_nonneg_left hk
          · norm_num
  rw [← (hasSum_deriv_deriv_digamma hs).tsum_eq]
  calc ‖∑' k : ℕ, -2 / ((k : ℂ) + (a + t * I)) ^ 3‖
      ≤ ∑' k : ℕ, 8 * (1 / ((k : ℝ) + (a + |t|)) ^ 3) := by
        refine tsum_of_norm_bounded (hsum.mul_left 8).hasSum fun k ↦ ?_
        have h1 := add_abs_le_two_mul_norm a t k
        have h2 := add_abs_sq_le_two_mul_norm_sq a t k
        have hck : 0 < (k : ℝ) + a + |t| := by positivity
        have hpos : 0 < ‖(k : ℂ) + (a + t * I)‖ := by linarith
        have h2n : ‖(-2 : ℂ)‖ = 2 := by simp
        rw [norm_div, h2n, norm_pow, div_le_iff₀ (pow_pos hpos 3)]
        have h3 : ((k : ℝ) + a + |t|) ^ 3 ≤ 4 * ‖(k : ℂ) + (a + t * I)‖ ^ 3 := by
          calc ((k : ℝ) + a + |t|) ^ 3 = ((k : ℝ) + a + |t|) ^ 2 * ((k : ℝ) + a + |t|) := by ring
            _ ≤ (2 * ‖(k : ℂ) + (a + t * I)‖ ^ 2) * (2 * ‖(k : ℂ) + (a + t * I)‖) := by
                gcongr
            _ = 4 * ‖(k : ℂ) + (a + t * I)‖ ^ 3 := by ring
        calc (2 : ℝ) = 8 * (1 / ((k : ℝ) + (a + |t|)) ^ 3) * (((k : ℝ) + a + |t|) ^ 3 / 4) := by
              field_simp
              ring
          _ ≤ 8 * (1 / ((k : ℝ) + (a + |t|)) ^ 3) * ‖(k : ℂ) + (a + t * I)‖ ^ 3 := by
              gcongr
              linarith
    _ = 8 * ∑' k : ℕ, 1 / ((k : ℝ) + (a + |t|)) ^ 3 := tsum_mul_left
    _ ≤ 8 * (1 / (a + |t|) ^ 3 + 1 / (2 * (a + |t|) ^ 2)) := by
        gcongr
        exact tsum_one_div_nat_add_cube_le hc

end Complex

namespace Complex

theorem hasDerivAt_digamma {s : ℂ} (hs : 0 < s.re) : HasDerivAt digamma (deriv digamma s) s :=
  (differentiableOn_digamma.differentiableAt
    ((isOpen_lt continuous_const continuous_re).mem_nhds hs)).hasDerivAt

theorem hasDerivAt_deriv_digamma {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt (deriv digamma) (deriv (deriv digamma) s) s :=
  ((analyticOnNhd_digamma.deriv s hs).differentiableAt).hasDerivAt

/-- On the vertical line `Re s = a > 0`, `|ψ'(a + it)| ≤ K/(1 + |t|)` with
`K = 2 (1/m² + 1/m)`, `m = min a 1`. -/
theorem norm_deriv_digamma_le' {a : ℝ} (ha : 0 < a) (t : ℝ) :
    ‖deriv digamma (a + t * I)‖ ≤ 2 * (1 / min a 1 ^ 2 + 1 / min a 1) / (1 + |t|) := by
  set m := min a 1
  have hm : 0 < m := lt_min ha one_pos
  have h1 : m * (1 + |t|) ≤ a + |t| := by
    have := min_le_left a 1; have := min_le_right a 1
    nlinarith [abs_nonneg t]
  have hpos : 0 < m * (1 + |t|) := by positivity
  refine (norm_deriv_digamma_le ha t).trans ?_
  have e1 : 1 / (a + |t|) ≤ 1 / m / (1 + |t|) := by
    rw [div_div]; exact one_div_le_one_div_of_le hpos h1
  have e2 : 1 / (a + |t|) ^ 2 ≤ 1 / m ^ 2 / (1 + |t|) := by
    have h2 : (m * (1 + |t|)) ^ 2 ≤ (a + |t|) ^ 2 := by gcongr
    have h3 : m ^ 2 * (1 + |t|) ≤ (m * (1 + |t|)) ^ 2 := by
      rw [mul_pow]
      have : (1 : ℝ) + |t| ≤ (1 + |t|) ^ 2 := by nlinarith [abs_nonneg t]
      exact mul_le_mul_of_nonneg_left this (by positivity)
    rw [div_div]
    exact one_div_le_one_div_of_le (by positivity) (h3.trans h2)
  calc 2 * (1 / (a + |t|) ^ 2 + 1 / (a + |t|))
      ≤ 2 * (1 / m ^ 2 / (1 + |t|) + 1 / m / (1 + |t|)) := by gcongr
    _ = 2 * (1 / m ^ 2 + 1 / m) / (1 + |t|) := by ring

private theorem norm_digamma_sub_le_aux {a : ℝ} (ha : 0 < a) {ε : ℝ} (hε : |ε| = 1) {t : ℝ}
    (ht : 0 ≤ t) :
    ‖digamma (a + (ε * t : ℝ) * I) - digamma a‖ ≤
      2 * (1 / min a 1 ^ 2 + 1 / min a 1) * Real.log (1 + t) := by
  set K := 2 * (1 / min a 1 ^ 2 + 1 / min a 1)
  have hline : ∀ τ : ℝ, 0 < ((a : ℂ) + (ε * τ : ℝ) * I).re := fun τ ↦ by simpa using ha
  have hderiv : ∀ τ : ℝ, HasDerivAt (fun τ : ℝ ↦ digamma (a + (ε * τ : ℝ) * I) - digamma a)
      (deriv digamma (a + (ε * τ : ℝ) * I) * (ε * I)) τ := by
    intro τ
    have h1 : HasDerivAt (fun τ : ℝ ↦ (a : ℂ) + (ε * τ : ℝ) * I) (ε * I) τ := by
      have := (((hasDerivAt_id (τ : ℂ)).const_mul (ε : ℂ)).mul_const I).const_add (a : ℂ)
      have := this.comp_ofReal
      simpa [mul_assoc] using this
    exact ((hasDerivAt_digamma (hline τ)).comp τ h1).sub_const _
  have hcont : ContinuousOn (fun τ : ℝ ↦ digamma (a + (ε * τ : ℝ) * I) - digamma a) (Icc 0 t) :=
    fun τ _ ↦ (hderiv τ).continuousAt.continuousWithinAt
  have hB : ∀ τ ∈ Ico (0 : ℝ) t, HasDerivWithinAt (fun τ ↦ K * Real.log (1 + τ))
      (K * (1 / (1 + τ))) (Ici τ) τ := by
    intro τ hτ
    have h1 : (1 : ℝ) + τ ≠ 0 := by linarith [hτ.1]
    have := (((hasDerivAt_id τ).const_add (1 : ℝ)).log h1).const_mul K
    simpa [one_div] using this.hasDerivWithinAt
  have hBc : ContinuousOn (fun τ ↦ K * Real.log (1 + τ)) (Icc 0 t) := by
    intro τ hτ
    have h1 : (1 : ℝ) + τ ≠ 0 := by linarith [hτ.1]
    exact (((continuous_const.add continuous_id).continuousAt).log h1).const_mul K
      |>.continuousWithinAt
  have := image_norm_le_of_norm_deriv_right_le_deriv_boundary' hcont
    (fun τ _ ↦ (hderiv τ).hasDerivWithinAt) (B := fun τ ↦ K * Real.log (1 + τ)) (by simp)
    hBc hB (fun τ hτ ↦ ?_) (right_mem_Icc.2 ht)
  · simpa using this
  · rw [norm_mul, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs, hε, mul_one]
    have := norm_deriv_digamma_le' ha (ε * τ)
    rw [abs_mul, hε, one_mul, abs_of_nonneg hτ.1] at this
    rw [mul_one_div]
    exact this

/-- On the vertical line `Re s = a > 0`, `|ψ(a + it) - ψ(a)| ≤ K log (1 + |t|)` with
`K = 2 (1/m² + 1/m)`, `m = min a 1`. -/
theorem norm_digamma_sub_le {a : ℝ} (ha : 0 < a) (t : ℝ) :
    ‖digamma (a + t * I) - digamma a‖ ≤
      2 * (1 / min a 1 ^ 2 + 1 / min a 1) * Real.log (1 + |t|) := by
  rcases le_or_gt 0 t with ht | ht
  · have := norm_digamma_sub_le_aux ha (ε := 1) (by simp) ht
    simpa [abs_of_nonneg ht] using this
  · have := norm_digamma_sub_le_aux ha (ε := -1) (by simp) (t := -t) (by linarith)
    simpa [abs_of_neg ht] using this

/-- On the vertical line `Re s = a > 0`, `ψ(a + it) ≪ log (2 + |t|)`. -/
theorem exists_norm_digamma_le {a : ℝ} (ha : 0 < a) :
    ∃ C, ∀ t : ℝ, ‖digamma (a + t * I)‖ ≤ C * Real.log (2 + |t|) := by
  set K := 2 * (1 / min a 1 ^ 2 + 1 / min a 1)
  have hK : 0 ≤ K := by positivity
  refine ⟨‖digamma a‖ / Real.log 2 + K, fun t ↦ ?_⟩
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog : Real.log 2 ≤ Real.log (2 + |t|) :=
    Real.log_le_log two_pos (by linarith [abs_nonneg t])
  have hlog' : Real.log (1 + |t|) ≤ Real.log (2 + |t|) :=
    Real.log_le_log (by positivity) (by linarith)
  calc ‖digamma (a + t * I)‖ ≤ ‖digamma a‖ + ‖digamma (a + t * I) - digamma a‖ := by
        simpa using norm_add_le (digamma a) (digamma (a + t * I) - digamma a)
    _ ≤ ‖digamma a‖ + K * Real.log (1 + |t|) := by gcongr; exact norm_digamma_sub_le ha t
    _ ≤ ‖digamma a‖ / Real.log 2 * Real.log (2 + |t|) + K * Real.log (2 + |t|) := by
        gcongr
        rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
        exact mul_le_mul_of_nonneg_left hlog (norm_nonneg _)
    _ = (‖digamma a‖ / Real.log 2 + K) * Real.log (2 + |t|) := by ring

/-- `ψ(σ + it) ≪ log (|t| + 2)`, uniformly for `σ` in a compact interval `[σ₁, σ₂] ⊂ (0, ∞)`. -/
theorem exists_norm_digamma_le_log {σ₁ σ₂ : ℝ} (h₁ : 0 < σ₁) :
    ∃ C, ∀ σ t : ℝ, σ ∈ Icc σ₁ σ₂ → ‖digamma (σ + t * I)‖ ≤ C * Real.log (|t| + 2) := by
  have hcont : ContinuousOn (fun σ : ℝ ↦ digamma σ) (Icc σ₁ σ₂) :=
    differentiableOn_digamma.continuousOn.comp continuous_ofReal.continuousOn
      (fun σ hσ ↦ by change 0 < (σ : ℂ).re; rw [ofReal_re]; exact h₁.trans_le hσ.1)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  set m := min σ₁ 1 with hm
  have hm0 : 0 < m := lt_min h₁ one_pos
  set K := 2 * (1 / m ^ 2 + 1 / m) with hK
  have hK0 : 0 ≤ K := by positivity
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine ⟨max M 0 / Real.log 2 + K, fun σ t hσ ↦ ?_⟩
  have hσ0 : 0 < σ := h₁.trans_le hσ.1
  have hmσ : m ≤ min σ 1 := min_le_min hσ.1 le_rfl
  have hKσ : 2 * (1 / min σ 1 ^ 2 + 1 / min σ 1) ≤ K := by
    have h1 : 1 / min σ 1 ≤ 1 / m := one_div_le_one_div_of_le hm0 hmσ
    have h2 : 1 / min σ 1 ^ 2 ≤ 1 / m ^ 2 :=
      one_div_le_one_div_of_le (by positivity) (by gcongr)
    linarith
  have hlog : Real.log 2 ≤ Real.log (|t| + 2) :=
    Real.log_le_log two_pos (by linarith [abs_nonneg t])
  have hlog' : Real.log (1 + |t|) ≤ Real.log (|t| + 2) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlog0 : 0 ≤ Real.log (1 + |t|) := Real.log_nonneg (by linarith [abs_nonneg t])
  have hMσ : ‖digamma σ‖ ≤ max M 0 := (hM σ hσ).trans (le_max_left _ _)
  have hM2 : max M 0 ≤ max M 0 / Real.log 2 * Real.log (|t| + 2) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
    exact mul_le_mul_of_nonneg_left hlog (le_max_right _ _)
  calc ‖digamma (σ + t * I)‖ ≤ ‖digamma σ‖ + ‖digamma (σ + t * I) - digamma σ‖ := by
        simpa using norm_add_le (digamma σ) (digamma (σ + t * I) - digamma σ)
    _ ≤ max M 0 + K * Real.log (1 + |t|) :=
        add_le_add hMσ ((norm_digamma_sub_le hσ0 t).trans
          (mul_le_mul_of_nonneg_right hKσ hlog0))
    _ ≤ max M 0 / Real.log 2 * Real.log (|t| + 2) + K * Real.log (|t| + 2) :=
        add_le_add hM2 (mul_le_mul_of_nonneg_left hlog' hK0)
    _ = (max M 0 / Real.log 2 + K) * Real.log (|t| + 2) := by ring

end Complex
