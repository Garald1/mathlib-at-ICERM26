/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Harald Helfgott
-/
module

public import Mathlib.NumberTheory.WeilExplicitFormula.ZeroCount
public import Mathlib.NumberTheory.WeilExplicitFormula.ZetaLogDeriv
public import Mathlib.Analysis.SpecialFunctions.Gamma.DigammaSeries

/-! # Good heights (Montgomery–Vaughan, Lemma 12.2)

There is a constant `C` such that for every `T ≥ 2` there is `T₁ ∈ [T, T + 1]` with
`ζ(σ + iT₁) ≠ 0` and `‖ζ'/ζ(σ + iT₁)‖ ≤ C log² T` for all `-1 ≤ σ ≤ 2` (`exists_good_height`,
which is the statement `Lemma_12_2` of `ExplicitFormula.lean`, i.e. `IEANTN`'s node).
`exists_good_height_of` proves it from the functional equation of `ζ'/ζ` in the form
`LogDerivFunctionalEquation` (the statement of `IEANTN`'s
`ZetaLogDeriv.v1.logDeriv_functional_equation`, which `IEANTN`'s `lemma_12_2` imports);
`exists_good_height` supplies it from `ZetaLogDeriv.lean` (`logDeriv_functional_equation`).

The proof follows `blueprint/proofs/GoodHeights.md`, §§3–4, without the Hadamard product:
* §3, the local expansion (`exists_finset_logDeriv_riemannZeta_sub_sum_le`): Landau's lemma
  (`Landau.lean`) for `ζ` on the discs of radii `3/2 < 27/16 < 15/8` about `2 + it`, `|t| ≥ 2`,
  where `|ζ| ≤ 16 (|t| + 4)` by (Z1) and `|ζ(2 + it)| ≥ 1/3` by (Z2);
* the choice of `T₁` (`exists_far_point`): if `Z` is the set of the zeros with `0 < β < 1`,
  `T - 2 ≤ γ ≤ T + 3`, one of `|Z| + 1` equally spaced points of `[T, T + 1]` is at distance
  `≥ 1/(2(|Z| + 1))` from every ordinate; and `|Z| ≤ ∑_{ρ ∈ Z} m_ρ ≪ log T` by Theorem 10.13
  (`zetaZeroesSum_le_log`) on five intervals of length one;
* `1/2 ≤ σ ≤ 2`: the zeros in the local expansion are in `Z`, at distance at least
  `1/(2(|Z| + 1))` from `σ + iT₁`;
* `-1 ≤ σ < 1/2`: the functional equation of `ζ'/ζ` (`LogDerivFunctionalEquation`), the case
  `1/2 < σ ≤ 2` at `1 - s̄ = (1 - σ) + iT₁`, `ψ(s) = ψ(s + 2) - 1/s - 1/(s + 1)` with the library's
  `Complex.exists_norm_digamma_le_log` on `1 ≤ Re ≤ 5/2`, and `|tan(πs/2)| ≤ 2`.

`exists_good_height_margin_of` (and `exists_good_height_margin`, from `ZetaLogDeriv.lean`) is the
same statement with the margin that the choice of `T₁` provides: `|T₁ - γ| ≥ c / log T` for every
non-trivial zero `ρ = β + iγ`. `PartialFractions.lean` uses it; `exists_good_height_of` is
unchanged.

## AI usage

This file was written by Claude (Anthropic) in November 2026. It compiles, but has not been
reviewed by a human.
-/

@[expose] public section

open Real Complex Filter Topology Set Metric
open scoped ComplexConjugate

noncomputable section

namespace WeilExplicitFormula

/-! ### Elementary facts -/

theorem cos_pi_mul_div_two_ne_zero {s : ℂ} (hs : s.im ≠ 0) : Complex.cos (π * s / 2) ≠ 0 := by
  rw [Ne, Complex.cos_eq_zero_iff]
  rintro ⟨k, hk⟩
  have := congrArg Complex.im hk
  simp only [div_ofNat_im, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero, add_re, mul_re,
    re_ofNat, intCast_re, im_ofNat, intCast_im, mul_zero, sub_zero, one_re, add_im, one_im,
    zero_div, div_eq_zero_iff, mul_eq_zero, pi_ne_zero, false_or, OfNat.ofNat_ne_zero,
    or_false] at this
  exact hs this

/-- `ζ(s) ≠ 0` for `Re s ≤ 0` and `s` not real (`GoodHeights.md` §4, by `riemannZeta_one_sub`). -/
theorem riemannZeta_ne_zero_of_re_nonpos {s : ℂ} (hs : s.re ≤ 0) (him : s.im ≠ 0) :
    riemannZeta s ≠ 0 := by
  have hwre : 1 ≤ (1 - s).re := by simp; linarith
  have hwim : (1 - s).im ≠ 0 := by simpa using him
  have hwn : ∀ n : ℕ, 1 - s ≠ -n := fun n h ↦ hwim (by rw [h]; simp)
  have hw1 : 1 - s ≠ 1 := fun h ↦ hwim (by rw [h]; simp)
  have h := riemannZeta_one_sub hwn hw1
  rw [sub_sub_cancel] at h
  rw [h]
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_) ?_) ?_) ?_
  · exact cpow_ne_zero_iff.2 (Or.inl (mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_ne_zero)))
  · exact Complex.Gamma_ne_zero_of_re_pos (by linarith)
  · exact cos_pi_mul_div_two_ne_zero hwim
  · exact riemannZeta_ne_zero_of_one_le_re hwre

/-- `‖tan w‖ ≤ 2` for `Im w ≥ 1`. -/
theorem norm_tan_le_two {w : ℂ} (hw : 1 ≤ w.im) : ‖Complex.tan w‖ ≤ 2 := by
  have ha : ‖Complex.exp (w * I)‖ = Real.exp (-w.im) := by
    rw [Complex.norm_exp]
    congr 1
    simp
  have hb : ‖Complex.exp (-w * I)‖ = Real.exp w.im := by
    rw [Complex.norm_exp]
    congr 1
    simp
  have hsin : ‖2 * Complex.sin w‖ ≤ Real.exp w.im + Real.exp (-w.im) := by
    rw [Complex.two_sin, norm_mul, Complex.norm_I, mul_one]
    calc _ ≤ ‖Complex.exp (-w * I)‖ + ‖Complex.exp (w * I)‖ := norm_sub_le _ _
      _ = _ := by rw [ha, hb]
  have hcos : Real.exp w.im - Real.exp (-w.im) ≤ ‖2 * Complex.cos w‖ := by
    rw [Complex.two_cos]
    have := norm_sub_norm_le (Complex.exp (-w * I)) (-Complex.exp (w * I))
    rw [norm_neg, sub_neg_eq_add, ha, hb, add_comm] at this
    exact this
  have h3 : 3 * Real.exp (-w.im) ≤ Real.exp w.im := by
    have h1 : Real.exp w.im = Real.exp (-w.im) * Real.exp (2 * w.im) := by
      rw [← Real.exp_add]
      ring_nf
    have h2 : 3 ≤ Real.exp (2 * w.im) := by
      have := Real.add_one_le_exp (2 * w.im)
      linarith
    rw [h1]
    nlinarith [Real.exp_pos (-w.im)]
  have e1 : ‖2 * Complex.sin w‖ = 2 * ‖Complex.sin w‖ := by rw [norm_mul]; norm_num
  have e2 : ‖2 * Complex.cos w‖ = 2 * ‖Complex.cos w‖ := by rw [norm_mul]; norm_num
  have hcos' : 0 < ‖Complex.cos w‖ := by nlinarith [Real.exp_pos (-w.im)]
  rw [Complex.tan_eq_sin_div_cos, norm_div, div_le_iff₀ hcos']
  nlinarith [Real.exp_pos (-w.im)]

theorem digamma_eq_add_two {s : ℂ} (hs : ∀ m : ℕ, s ≠ -m) :
    digamma s = digamma (s + 2) - 1 / s - 1 / (s + 1) := by
  have hs1 : ∀ m : ℕ, s + 1 ≠ -m := fun m h ↦ hs (m + 1) (by push_cast; linear_combination h)
  have h1 := Complex.digamma_apply_add_one s hs
  have h2 := Complex.digamma_apply_add_one (s + 1) hs1
  rw [show s + 1 + 1 = s + 2 by ring] at h2
  rw [h2, h1]
  ring

theorem zetaOrder_nonneg {ρ : ℂ} (h : ρ.re < 1) : (0 : ℝ) ≤ zetaOrder ρ := by
  rw [zetaOrder_eq (ne_one_of_re_lt_one h)]
  positivity

theorem one_le_zetaOrder {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hz : riemannZeta ρ = 0) :
    (1 : ℝ) ≤ zetaOrder ρ := by
  have hρ1 := ne_one_of_re_lt_one h1
  rw [zetaOrder_eq hρ1]
  have htop : analyticOrderAt riemannZeta ρ ≠ ⊤ := by
    rw [← analyticOrderAt_riemannXi h0 h1]
    exact analyticOrderAt_ne_top_of_ne_zero (U := univ)
      (fun z _ ↦ differentiable_riemannXi.analyticAt z) isPreconnected_univ (mem_univ 0)
      (by rw [riemannXi_zero]; norm_num) (mem_univ ρ)
  exact_mod_cast one_le_analyticOrderNatAt (analyticOn_riemannZeta ρ hρ1) hz htop

/-- If `X ≤ a ℓ² + b ℓ + c` and `ℓ ≥ log 2`, then `X ≤ (a + b/log 2 + c/log² 2) ℓ²`. -/
theorem le_mul_log_sq {X a b c ℓ : ℝ} (hℓ : Real.log 2 ≤ ℓ) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : X ≤ a * ℓ ^ 2 + b * ℓ + c) :
    X ≤ (a + b / Real.log 2 + c / Real.log 2 ^ 2) * ℓ ^ 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hℓ0 : 0 < ℓ := hl2.trans_le hℓ
  have h1 : b * ℓ ≤ b / Real.log 2 * ℓ ^ 2 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
    have : ℓ * Real.log 2 ≤ ℓ ^ 2 := by nlinarith
    nlinarith
  have h2 : c ≤ c / Real.log 2 ^ 2 * ℓ ^ 2 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have : Real.log 2 ^ 2 ≤ ℓ ^ 2 := pow_le_pow_left₀ hl2.le hℓ 2
    nlinarith
  nlinarith

/-! ### The local expansion of `ζ'/ζ` (§3) -/

/-- The constant of Landau's lemma for the radii `3/2 < 27/16 < 15/8`. -/
def landauConst : ℝ :=
  8 * (15 / 8) / (27 / 16 - 3 / 2) ^ 2 +
    1 / (Real.log (2 * (15 / 8) / (27 / 16 + 15 / 8)) * (27 / 16 - 3 / 2))

theorem landauConst_nonneg : 0 ≤ landauConst := by
  have h : 0 < Real.log (2 * (15 / 8) / (27 / 16 + 15 / 8) : ℝ) := Real.log_pos (by norm_num)
  have h' : (0 : ℝ) < 27 / 16 - 3 / 2 := by norm_num
  unfold landauConst
  positivity

/-- On `closedBall (2 + it) (15/8)`, `|t| ≥ 2`: `Re s ≥ 1/8`, `‖s - 1‖ ≥ 1/8`, `‖s‖ ≤ |t| + 4`,
hence `‖ζ(s)‖ ≤ 16 (|t| + 4)`. -/
theorem norm_riemannZeta_le_of_mem_closedBall {t : ℝ} (ht : 2 ≤ |t|) {z : ℂ}
    (hz : ‖z - (2 + t * I)‖ ≤ 15 / 8) :
    1 / 8 ≤ z.re ∧ 1 / 8 ≤ ‖z - 1‖ ∧ ‖riemannZeta z‖ ≤ 16 * (|t| + 4) := by
  have hre : 1 / 8 ≤ z.re := by
    have h := Complex.abs_re_le_norm (z - (2 + t * I))
    simp only [sub_re, add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im, re_ofNat] at h
    have := (abs_le.1 (h.trans hz)).1
    linarith
  have him : 1 / 8 ≤ |z.im| := by
    have h := Complex.abs_im_le_norm (z - (2 + t * I))
    simp only [sub_im, add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im, im_ofNat] at h
    have h' := h.trans hz
    have := abs_sub_abs_le_abs_sub t z.im
    rw [abs_sub_comm t z.im] at this
    norm_num at h'
    linarith
  have hz1 : 1 / 8 ≤ ‖z - 1‖ := by
    have := Complex.abs_im_le_norm (z - 1)
    simp only [sub_im, one_im, sub_zero] at this
    linarith
  have hzn : ‖z‖ ≤ |t| + 4 := by
    have hc : ‖(2 + t * I : ℂ)‖ ≤ 2 + |t| := by
      have := Complex.norm_le_abs_re_add_abs_im (2 + t * I)
      simpa using this
    calc ‖z‖ = ‖(2 + t * I) + (z - (2 + t * I))‖ := by congr 1; ring
      _ ≤ ‖(2 + t * I : ℂ)‖ + ‖z - (2 + t * I)‖ := norm_add_le _ _
      _ ≤ |t| + 4 := by linarith
  refine ⟨hre, hz1, ?_⟩
  have hre0 : 0 < z.re := by linarith
  have hz1' : z ≠ 1 := fun h ↦ by rw [h, sub_self, norm_zero] at hz1; linarith
  calc ‖riemannZeta z‖ ≤ ‖z‖ / ‖z - 1‖ + ‖z‖ / z.re := norm_riemannZeta_le hre0 hz1'
    _ ≤ ‖z‖ / (1 / 8) + ‖z‖ / (1 / 8) := by
        gcongr
    _ = 16 * ‖z‖ := by ring
    _ ≤ 16 * (|t| + 4) := by linarith

/-- `GoodHeights.md` §3: for `|t| ≥ 2` there is a finite set `S` of zeros of `ζ` within `27/16`
of `2 + it` such that, on `closedBall (2 + it) (3/2)` away from the zeros,
`‖ζ'/ζ(s) - ∑_{ρ ∈ S} m_ρ/(s - ρ)‖ ≤ landauConst (1 + log (48 (|t| + 4)))`. -/
theorem exists_finset_logDeriv_riemannZeta_sub_sum_le {t : ℝ} (ht : 2 ≤ |t|) :
    ∃ S : Finset ℂ, (∀ u ∈ S, riemannZeta u = 0 ∧ ‖u - (2 + t * I)‖ ≤ 27 / 16) ∧
      ∀ z ∈ closedBall (2 + t * I) (3 / 2), riemannZeta z ≠ 0 →
        ‖logDeriv riemannZeta z - ∑ u ∈ S, (analyticOrderNatAt riemannZeta u : ℂ) / (z - u)‖ ≤
          landauConst * (1 + Real.log (48 * (|t| + 4))) := by
  have hgeo : ∀ z ∈ closedBall (2 + t * I) (15 / 8),
      1 / 8 ≤ z.re ∧ 1 / 8 ≤ ‖z - 1‖ ∧ ‖riemannZeta z‖ ≤ 16 * (|t| + 4) := fun z hz ↦
    norm_riemannZeta_le_of_mem_closedBall ht (by rwa [mem_closedBall, dist_eq_norm] at hz)
  have hf : AnalyticOnNhd ℂ riemannZeta (closedBall (2 + t * I) (15 / 8)) := by
    intro z hz
    refine analyticOn_riemannZeta z fun h ↦ ?_
    have := (hgeo z hz).2.1
    rw [mem_singleton_iff.1 h, sub_self, norm_zero] at this
    linarith
  have hc3 : 1 / 3 ≤ ‖riemannZeta (2 + t * I)‖ := norm_riemannZeta_two_add_ge t
  have hfc : riemannZeta (2 + t * I) ≠ 0 := norm_pos_iff.1 (by linarith)
  obtain ⟨S, hS, hbound⟩ := exists_norm_logDeriv_sub_sum_le (r := 3 / 2) (R := 27 / 16)
    (R₀ := 15 / 8) (M := 16 * (|t| + 4)) (by norm_num) (by norm_num) (by norm_num) hf hfc
    (by linarith [abs_nonneg t]) fun z hz ↦ (hgeo z hz).2.2
  refine ⟨S, hS, fun z hz hz0 ↦ (hbound z hz hz0).trans ?_⟩
  have hlog : Real.log (16 * (|t| + 4) / ‖riemannZeta (2 + t * I)‖) ≤
      Real.log (48 * (|t| + 4)) := by
    apply Real.log_le_log (div_pos (by positivity) (by linarith))
    rw [div_le_iff₀ (by linarith)]
    nlinarith [abs_nonneg t]
  exact mul_le_mul_of_nonneg_left (by linarith) landauConst_nonneg

/-! ### The choice of `T₁` -/

/-- One of the `N + 1` points `T + (2j + 1)/(2(N + 1))` of `[T, T + 1]` is at distance at least
`1/(2(N + 1))` from each of `N` given reals. -/
theorem exists_far_point (Γ : Finset ℝ) (T : ℝ) :
    ∃ T₁ ∈ Icc T (T + 1), ∀ γ ∈ Γ, 1 / (2 * ((Γ.card : ℝ) + 1)) ≤ |T₁ - γ| := by
  set N := Γ.card with hN
  set η : ℝ := 1 / (2 * ((N : ℝ) + 1)) with hη
  have hη0 : 0 < η := by positivity
  set p : ℕ → ℝ := fun j ↦ T + (2 * j + 1) * η with hp
  by_contra hcon
  simp only [not_exists, not_and, not_forall, not_le, exists_prop] at hcon
  have hpmem : ∀ j ∈ Finset.range (N + 1), p j ∈ Icc T (T + 1) := by
    intro j hj
    have hjN : (j : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    refine ⟨by simp only [hp]; nlinarith, ?_⟩
    simp only [hp, hη]
    rw [add_le_add_iff_left, mul_one_div, div_le_one (by positivity)]
    linarith
  have hbad : ∀ j ∈ Finset.range (N + 1), ∃ γ ∈ Γ, |p j - γ| < η := fun j hj ↦
    hcon (p j) (hpmem j hj)
  choose! g hgΓ hg using hbad
  have hinj : Set.InjOn g (Finset.range (N + 1) : Set ℕ) := by
    intro j hj k hk hjk
    have h1 := hg j hj
    have h2 := hg k hk
    rw [hjk] at h1
    have hlt : |p j - p k| < 2 * η := by
      calc |p j - p k| = |(p j - g k) - (p k - g k)| := by ring_nf
        _ ≤ |p j - g k| + |p k - g k| := abs_sub _ _
        _ < η + η := add_lt_add h1 h2
        _ = 2 * η := by ring
    have hdiff : p j - p k = 2 * ((j : ℝ) - k) * η := by simp only [hp]; ring
    rw [hdiff, abs_mul, abs_mul, abs_of_pos hη0, abs_two] at hlt
    have hjk' : |(j : ℝ) - k| < 1 := by nlinarith
    have : (j : ℤ) = k := by
      have : |((j : ℤ) - k : ℤ)| < 1 := by exact_mod_cast hjk'
      rw [abs_lt] at this
      omega
    exact_mod_cast this
  have := Finset.card_le_card_of_injOn g (fun j hj ↦ hgΓ j hj) hinj
  rw [Finset.card_range] at this
  omega

/-- The zeros with `0 < β < 1`, `T - 2 ≤ γ ≤ T + 3` number `≪ log T`, by Theorem 10.13 on five
intervals of length one. -/
theorem sum_zetaOrder_le_of_window {T : ℝ} (hT : 2 ≤ T) {Zf : Finset ℂ}
    (hZf : ∀ ρ, ρ ∈ Zf ↔ ρ ∈ zetaZeroesIn (Ioo 0 1) (Icc (T - 2) (T + 3))) :
    ∑ ρ ∈ Zf, (zetaOrder ρ : ℝ) ≤ 5 * (20 / Real.log (22 / 21) * Real.log (T + 4)) := by
  classical
  set K₀ : ℝ := 20 / Real.log (22 / 21) with hK₀
  have hK₀0 : 0 ≤ K₀ := div_nonneg (by norm_num) (Real.log_pos (by norm_num)).le
  have hfin : ∀ j : ℕ, (zetaZeroesIn (Ioo 0 1) (Icc (T - 2 + j) (T - 2 + j + 1))).Finite :=
    fun j ↦ zetaZeroesIn_finite Ioo_subset_Icc_self subset_rfl
  set Z : ℕ → Finset ℂ := fun j ↦ (hfin j).toFinset with hZ
  have hm0 : ∀ ρ ∈ Zf, (0 : ℝ) ≤ zetaOrder ρ := fun ρ hρ ↦
    zetaOrder_nonneg ((hZf ρ).1 hρ).1.2
  -- every zero of the window lies in one of the five unit intervals
  have hcover : ∀ ρ ∈ Zf, ∃ j ∈ Finset.range 5, ρ ∈ Z j := by
    intro ρ hρ
    obtain ⟨hre, ⟨hlo, hhi⟩, hz⟩ := (hZf ρ).1 hρ
    set x := ρ.im - (T - 2) with hx
    have hx0 : 0 ≤ x := by rw [hx]; linarith
    refine ⟨min ⌊x⌋₊ 4, Finset.mem_range.2 (by omega), ?_⟩
    rw [hZ, Set.Finite.mem_toFinset]
    refine ⟨hre, ⟨?_, ?_⟩, hz⟩
    · have : ((min ⌊x⌋₊ 4 : ℕ) : ℝ) ≤ x :=
        (Nat.cast_le.2 (min_le_left _ _)).trans (Nat.floor_le hx0)
      linarith
    · rcases le_or_gt ⌊x⌋₊ 4 with h | h
      · rw [min_eq_left h]
        have := Nat.lt_floor_add_one x
        linarith
      · rw [min_eq_right h.le]
        push_cast
        linarith
  have hZj : ∀ j ∈ Finset.range 5, ∑ ρ ∈ Z j, (zetaOrder ρ : ℝ) ≤ K₀ * Real.log (T + 4) := by
    intro j hj
    have hj4 : (j : ℝ) ≤ 4 := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have h := zetaZeroesSum_le_log (T := T - 2 + j) (by linarith)
    rw [zetaZeroesSum_eq_sum (hfin j)] at h
    simp only [one_mul] at h
    calc ∑ ρ ∈ Z j, (zetaOrder ρ : ℝ) ≤ K₀ * Real.log (T - 2 + j + 2) := h
      _ ≤ K₀ * Real.log (T + 4) :=
          mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) (by linarith)) hK₀0
  calc ∑ ρ ∈ Zf, (zetaOrder ρ : ℝ)
      ≤ ∑ ρ ∈ Zf, ∑ j ∈ Finset.range 5, (if ρ ∈ Z j then (zetaOrder ρ : ℝ) else 0) := by
        refine Finset.sum_le_sum fun ρ hρ ↦ ?_
        obtain ⟨j, hj, hρj⟩ := hcover ρ hρ
        calc (zetaOrder ρ : ℝ) = if ρ ∈ Z j then (zetaOrder ρ : ℝ) else 0 := by rw [if_pos hρj]
          _ ≤ ∑ j ∈ Finset.range 5, (if ρ ∈ Z j then (zetaOrder ρ : ℝ) else 0) :=
            Finset.single_le_sum (f := fun j ↦ if ρ ∈ Z j then (zetaOrder ρ : ℝ) else 0)
              (fun i _ ↦ ite_nonneg (hm0 ρ hρ) le_rfl) hj
    _ = ∑ j ∈ Finset.range 5, ∑ ρ ∈ Zf, (if ρ ∈ Z j then (zetaOrder ρ : ℝ) else 0) :=
        Finset.sum_comm
    _ ≤ ∑ j ∈ Finset.range 5, K₀ * Real.log (T + 4) := by
        refine Finset.sum_le_sum fun j hj ↦ ?_
        rw [← Finset.sum_filter]
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun ρ hρ _ ↦ ?_) (hZj j hj)
        · intro ρ hρ
          exact (Finset.mem_filter.1 hρ).2
        · rw [hZ, Set.Finite.mem_toFinset] at hρ
          exact zetaOrder_nonneg hρ.1.2
    _ = 5 * (K₀ * Real.log (T + 4)) := by simp

/-! ### The bounds on the segment -/

section Segment

variable {T T₁ η : ℝ} {Zf : Finset ℂ}

theorem riemannZeta_ne_zero_of_far (hT₁ : T₁ ∈ Icc T (T + 1)) (hT : 2 ≤ T) (hη : 0 < η)
    (hZf : ∀ ρ, ρ ∈ Zf ↔ ρ ∈ zetaZeroesIn (Ioo 0 1) (Icc (T - 2) (T + 3)))
    (hsep : ∀ ρ ∈ Zf, η ≤ |T₁ - ρ.im|) (σ : ℝ) : riemannZeta (σ + T₁ * I) ≠ 0 := by
  intro h0
  have him : (σ + T₁ * I : ℂ).im = T₁ := by simp
  have hre : (σ + T₁ * I : ℂ).re = σ := by simp
  rcases le_or_gt σ 0 with hσ | hσ
  · exact riemannZeta_ne_zero_of_re_nonpos (by rw [hre]; exact hσ)
      (by rw [him]; linarith [hT₁.1]) h0
  rcases lt_or_ge σ 1 with hσ1 | hσ1
  · have hmem : (σ + T₁ * I : ℂ) ∈ Zf := by
      rw [hZf]
      refine ⟨⟨by rw [hre]; exact hσ, by rw [hre]; exact hσ1⟩, ⟨?_, ?_⟩, h0⟩
      · rw [him]; linarith [hT₁.1]
      · rw [him]; linarith [hT₁.2]
    have := hsep _ hmem
    rw [him, sub_self, abs_zero] at this
    linarith
  · exact riemannZeta_ne_zero_of_one_le_re (by rw [hre]; exact hσ1) h0

/-- `1/2 ≤ σ ≤ 2` (`GoodHeights.md` §4). -/
theorem norm_logDeriv_riemannZeta_le_right (hT₁ : T₁ ∈ Icc T (T + 1)) (hT : 2 ≤ T)
    (hη : 0 < η) (hZf : ∀ ρ, ρ ∈ Zf ↔ ρ ∈ zetaZeroesIn (Ioo 0 1) (Icc (T - 2) (T + 3)))
    (hsep : ∀ ρ ∈ Zf, η ≤ |T₁ - ρ.im|) {σ : ℝ} (hσ : σ ∈ Icc (1 / 2 : ℝ) 2) :
    ‖logDeriv riemannZeta (σ + T₁ * I)‖ ≤
      (∑ ρ ∈ Zf, (zetaOrder ρ : ℝ)) / η + landauConst * (1 + Real.log (48 * (T + 5))) := by
  have hT₁0 : 0 < T₁ := by linarith [hT₁.1]
  have hT₁2 : 2 ≤ |T₁| := by rw [abs_of_pos hT₁0]; linarith [hT₁.1]
  have hz := riemannZeta_ne_zero_of_far hT₁ hT hη hZf hsep σ
  obtain ⟨S, hS, hbound⟩ := exists_finset_logDeriv_riemannZeta_sub_sum_le hT₁2
  set s : ℂ := σ + T₁ * I with hs
  have hsball : s ∈ closedBall (2 + T₁ * I) (3 / 2) := by
    rw [mem_closedBall, dist_eq_norm]
    have : s - (2 + T₁ * I) = ((σ - 2 : ℝ) : ℂ) := by rw [hs]; push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hσ.1, hσ.2]
  have h1 := hbound s hsball hz
  have hSZ : S ⊆ Zf := by
    intro u hu
    obtain ⟨hu0, hud⟩ := hS u hu
    rw [hZf]
    have hre := Complex.abs_re_le_norm (u - (2 + T₁ * I))
    have him := Complex.abs_im_le_norm (u - (2 + T₁ * I))
    simp only [sub_re, sub_im, add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im,
      re_ofNat, im_ofNat] at hre him
    norm_num at hre him
    have hre' := abs_le.1 (hre.trans hud)
    have him' := abs_le.1 (him.trans hud)
    refine ⟨⟨by linarith [hre'.1], ?_⟩, ⟨by linarith [him'.1, hT₁.1], by linarith [him'.2, hT₁.2]⟩,
      hu0⟩
    by_contra h
    rw [not_lt] at h
    exact riemannZeta_ne_zero_of_one_le_re h hu0
  have hsum : ‖∑ u ∈ S, (analyticOrderNatAt riemannZeta u : ℂ) / (s - u)‖ ≤
      (∑ ρ ∈ Zf, (zetaOrder ρ : ℝ)) / η := by
    calc ‖∑ u ∈ S, (analyticOrderNatAt riemannZeta u : ℂ) / (s - u)‖
        ≤ ∑ u ∈ S, ‖(analyticOrderNatAt riemannZeta u : ℂ) / (s - u)‖ := norm_sum_le _ _
      _ ≤ ∑ u ∈ S, (analyticOrderNatAt riemannZeta u : ℝ) / η := by
          refine Finset.sum_le_sum fun u hu ↦ ?_
          rw [norm_div, Complex.norm_natCast]
          gcongr
          calc η ≤ |T₁ - u.im| := hsep u (hSZ hu)
            _ = |(s - u).im| := by simp [hs]
            _ ≤ ‖s - u‖ := Complex.abs_im_le_norm _
      _ = (∑ u ∈ S, (zetaOrder u : ℝ)) / η := by
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl fun u hu ↦ ?_
          have hu1 : u.re < 1 := (((hZf u).1 (hSZ hu)).1).2
          rw [zetaOrder_eq (ne_one_of_re_lt_one hu1)]
          push_cast
          rfl
      _ ≤ (∑ ρ ∈ Zf, (zetaOrder ρ : ℝ)) / η :=
          div_le_div_of_nonneg_right (Finset.sum_le_sum_of_subset_of_nonneg hSZ fun ρ hρ _ ↦
            zetaOrder_nonneg ((hZf ρ).1 hρ).1.2) hη.le
  have hlog : Real.log (48 * (|T₁| + 4)) ≤ Real.log (48 * (T + 5)) := by
    rw [abs_of_pos hT₁0]
    exact Real.log_le_log (by positivity) (by linarith [hT₁.2])
  have htri := norm_sub_norm_le (logDeriv riemannZeta s)
    (∑ u ∈ S, (analyticOrderNatAt riemannZeta u : ℂ) / (s - u))
  have hA := mul_le_mul_of_nonneg_left (show 1 + Real.log (48 * (|T₁| + 4)) ≤
    1 + Real.log (48 * (T + 5)) by linarith) landauConst_nonneg
  linarith

/-- `-1 ≤ σ < 1/2`, by the functional equation of `ζ'/ζ` (`GoodHeights.md` §4). -/
theorem norm_logDeriv_riemannZeta_le_left (hFE : LogDerivFunctionalEquation) (hT₁ : 2 ≤ T₁)
    {σ : ℝ} (hσ : σ < 1 / 2)
    (hσ' : -1 ≤ σ) (hz : riemannZeta (σ + T₁ * I) ≠ 0) {B : ℝ}
    (hB : ‖logDeriv riemannZeta ((1 - σ : ℝ) + T₁ * I)‖ ≤ B) {CD : ℝ}
    (hCD : ∀ σ' t : ℝ, σ' ∈ Icc 1 (5 / 2) → ‖digamma (σ' + t * I)‖ ≤ CD * Real.log (|t| + 2)) :
    ‖logDeriv riemannZeta (σ + T₁ * I)‖ ≤
      B + Real.log (2 * π) + (CD * Real.log (T₁ + 2) + 1) + π := by
  set s : ℂ := σ + T₁ * I with hs
  have him : s.im = T₁ := by simp [hs]
  have him0 : s.im ≠ 0 := by rw [him]; linarith
  have hsn : ∀ n : ℕ, s ≠ -n := fun n h ↦ him0 (by rw [h]; simp)
  have hs1 : s ≠ 1 := fun h ↦ him0 (by rw [h]; simp)
  have hfe : logDeriv riemannZeta s = -logDeriv riemannZeta (1 - s) + Complex.log (2 * π) -
      digamma s + π / 2 * Complex.tan (π * s / 2) := by
    simpa only [logDeriv_apply] using hFE s hsn hs1 hz (cos_pi_mul_div_two_ne_zero him0)
  -- `1 - s = conj ((1 - σ) + iT₁)`
  have hconj : 1 - s = conj (((1 - σ : ℝ) : ℂ) + T₁ * I) := by
    rw [hs]
    apply Complex.ext <;> simp
  have hw1 : ((1 - σ : ℝ) : ℂ) + T₁ * I ≠ 1 := fun h ↦ by
    have := congrArg Complex.im h
    simp at this
    linarith
  have h1 : ‖logDeriv riemannZeta (1 - s)‖ ≤ B := by
    rw [hconj, logDeriv_riemannZeta_conj hw1, Complex.norm_conj]
    exact hB
  have h2 : ‖Complex.log (2 * π)‖ = Real.log (2 * π) := by
    have : (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) := by push_cast; ring
    rw [this, ← Complex.ofReal_log (by positivity), Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by nlinarith [Real.pi_gt_three]))]
  have h3 : ‖digamma s‖ ≤ CD * Real.log (T₁ + 2) + 1 := by
    rw [digamma_eq_add_two hsn]
    have hs2 : s + 2 = ((σ + 2 : ℝ) : ℂ) + T₁ * I := by rw [hs]; push_cast; ring
    have hψ := hCD (σ + 2) T₁ ⟨by linarith, by linarith⟩
    rw [abs_of_pos (by linarith)] at hψ
    have hinv : ∀ w : ℂ, w.im = T₁ → ‖1 / w‖ ≤ 1 / 2 := by
      intro w hw
      rw [norm_div, norm_one]
      have : 2 ≤ ‖w‖ := by
        have := Complex.abs_im_le_norm w
        rw [hw, abs_of_pos (by linarith)] at this
        linarith
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
    have hi1 := hinv s him
    have hi2 := hinv (s + 1) (by simp [him])
    calc ‖digamma (s + 2) - 1 / s - 1 / (s + 1)‖
        ≤ ‖digamma (s + 2)‖ + ‖1 / s‖ + ‖1 / (s + 1)‖ := by
          refine (norm_sub_le _ _).trans ?_
          gcongr
          exact norm_sub_le _ _
      _ ≤ CD * Real.log (T₁ + 2) + 1 / 2 + 1 / 2 := by
          rw [hs2]
          linarith
      _ = CD * Real.log (T₁ + 2) + 1 := by ring
  have h4 : ‖(π : ℂ) / 2 * Complex.tan (π * s / 2)‖ ≤ π := by
    have hT : 1 ≤ (π * s / 2 : ℂ).im := by
      have : (π * s / 2 : ℂ).im = π * T₁ / 2 := by
        rw [← him]
        simp
      rw [this]
      nlinarith [Real.pi_gt_three]
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    have := norm_tan_le_two hT
    norm_num
    nlinarith [Real.pi_pos]
  rw [hfe]
  calc ‖-logDeriv riemannZeta (1 - s) + Complex.log (2 * π) - digamma s +
        π / 2 * Complex.tan (π * s / 2)‖
      ≤ ‖logDeriv riemannZeta (1 - s)‖ + ‖Complex.log (2 * π)‖ + ‖digamma s‖ +
          ‖(π : ℂ) / 2 * Complex.tan (π * s / 2)‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        refine (norm_sub_le _ _).trans ?_
        gcongr
        refine (norm_add_le _ _).trans ?_
        rw [norm_neg]
    _ ≤ B + Real.log (2 * π) + (CD * Real.log (T₁ + 2) + 1) + π := by
        rw [h2]
        linarith

end Segment

/-! ### Lemma 12.2 -/

theorem log_le_mul_log_of_le_pow {T x : ℝ} {k : ℕ} (hx : 0 < x) (h : x ≤ T ^ k) :
    Real.log x ≤ k * Real.log T := by
  rw [← Real.log_pow]
  exact Real.log_le_log hx h

/-- The arithmetic at the end of the proof of Lemma 12.2. -/
theorem good_height_arith {X nZ N K₀ Λ CD T : ℝ} (hT : 2 ≤ T) (hK₀ : 0 ≤ K₀) (hΛ : 0 ≤ Λ)
    (hnZ : nZ ≤ 5 * (K₀ * Real.log (T + 4))) (hN : N ≤ nZ) (hN0 : 0 ≤ N)
    (hX : X ≤ 2 * nZ * (N + 1) + Λ * (1 + Real.log (48 * (T + 5))) + Real.log (2 * π) +
      (|CD| * Real.log (T + 3) + 1) + π) :
    X ≤ (450 * K₀ ^ 2 + (30 * K₀ + 9 * Λ + 3 * |CD|) / Real.log 2 +
      (Λ + Real.log (2 * π) + 1 + π) / Real.log 2 ^ 2) * Real.log T ^ 2 := by
  have hT0 : 0 < T := by linarith
  have hℓ : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT
  have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hT3 : T + 4 ≤ T ^ 3 := by
    have h2 : 4 ≤ T ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h2 hT0.le]
  have hT9 : 48 * (T + 5) ≤ T ^ 9 := by
    have h8 : (2 : ℝ) ^ 8 ≤ T ^ 8 := pow_le_pow_left₀ (by norm_num) hT 8
    have : T ^ 9 = T * T ^ 8 := by ring
    nlinarith
  have hL4 : Real.log (T + 4) ≤ 3 * Real.log T := by
    have := log_le_mul_log_of_le_pow (k := 3) (by linarith) hT3
    exact_mod_cast this
  have hL48 : Real.log (48 * (T + 5)) ≤ 9 * Real.log T := by
    have := log_le_mul_log_of_le_pow (k := 9) (by positivity) hT9
    exact_mod_cast this
  have hL3 : Real.log (T + 3) ≤ 3 * Real.log T := by
    have := log_le_mul_log_of_le_pow (T := T) (k := 3) (x := T + 3) (by linarith)
      (by linarith [hT3])
    exact_mod_cast this
  have hnZ0 : 0 ≤ nZ := hN0.trans hN
  have hnZℓ : nZ ≤ 15 * K₀ * Real.log T := by
    have := mul_le_mul_of_nonneg_left hL4 hK₀
    linarith
  have hsq : 2 * nZ * (N + 1) ≤ 450 * K₀ ^ 2 * Real.log T ^ 2 + 30 * K₀ * Real.log T := by
    have h1 : 2 * nZ * (N + 1) ≤ 2 * nZ * (nZ + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have h2 : nZ * (nZ + 1) ≤ (15 * K₀ * Real.log T) * (15 * K₀ * Real.log T + 1) :=
      mul_le_mul hnZℓ (by linarith) (by linarith) (by positivity)
    calc 2 * nZ * (N + 1) ≤ 2 * nZ * (nZ + 1) := h1
      _ = 2 * (nZ * (nZ + 1)) := by ring
      _ ≤ 2 * ((15 * K₀ * Real.log T) * (15 * K₀ * Real.log T + 1)) := by linarith
      _ = 450 * K₀ ^ 2 * Real.log T ^ 2 + 30 * K₀ * Real.log T := by ring
  have hΛ' : Λ * (1 + Real.log (48 * (T + 5))) ≤ Λ + 9 * Λ * Real.log T := by
    have := mul_le_mul_of_nonneg_left hL48 hΛ
    calc Λ * (1 + Real.log (48 * (T + 5))) = Λ + Λ * Real.log (48 * (T + 5)) := by ring
      _ ≤ Λ + Λ * (9 * Real.log T) := by linarith
      _ = Λ + 9 * Λ * Real.log T := by ring
  have hCD' : |CD| * Real.log (T + 3) ≤ 3 * |CD| * Real.log T := by
    have := mul_le_mul_of_nonneg_left hL3 (abs_nonneg CD)
    calc |CD| * Real.log (T + 3) ≤ |CD| * (3 * Real.log T) := this
      _ = 3 * |CD| * Real.log T := by ring
  have hlog2π : 0 ≤ Real.log (2 * π) := Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  refine le_mul_log_sq hℓ (by positivity) (by positivity) ?_
  have e : (30 * K₀ + 9 * Λ + 3 * |CD|) * Real.log T =
      30 * K₀ * Real.log T + 9 * Λ * Real.log T + 3 * |CD| * Real.log T := by ring
  rw [e]
  linarith

/-- **Montgomery–Vaughan, Lemma 12.2**: there is `C` such that for every `T ≥ 2` there is
`T₁ ∈ [T, T + 1]` with `ζ(σ + iT₁) ≠ 0` and `‖ζ'/ζ(σ + iT₁)‖ ≤ C log² T` for `-1 ≤ σ ≤ 2`.
This is the proposition `Lemma_12_2` of `ExplicitFormula.lean`. -/
theorem exists_good_height_of (hFE : LogDerivFunctionalEquation) :
    ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T → ∃ T₁ ∈ Set.Icc T (T + 1),
    ∀ σ ∈ Set.Icc (-1 : ℝ) 2,
      riemannZeta (σ + T₁ * Complex.I) ≠ 0 ∧
        ‖deriv riemannZeta (σ + T₁ * Complex.I) / riemannZeta (σ + T₁ * Complex.I)‖ ≤
          C * Real.log T ^ 2 := by
  obtain ⟨CD, hCD⟩ := Complex.exists_norm_digamma_le_log (σ₁ := 1) (σ₂ := 5 / 2) one_pos
  have hK₀0 : (0 : ℝ) ≤ 20 / Real.log (22 / 21) :=
    div_nonneg (by norm_num) (Real.log_pos (by norm_num)).le
  refine ⟨450 * (20 / Real.log (22 / 21)) ^ 2 +
    (30 * (20 / Real.log (22 / 21)) + 9 * landauConst + 3 * |CD|) / Real.log 2 +
    (landauConst + Real.log (2 * π) + 1 + π) / Real.log 2 ^ 2, fun T hT ↦ ?_⟩
  -- the zeros near `[T, T + 1]`
  have hZ : (zetaZeroesIn (Ioo 0 1) (Icc (T - 2) (T + 3))).Finite :=
    zetaZeroesIn_finite Ioo_subset_Icc_self subset_rfl
  have hZf : ∀ ρ, ρ ∈ hZ.toFinset ↔ ρ ∈ zetaZeroesIn (Ioo 0 1) (Icc (T - 2) (T + 3)) :=
    fun ρ ↦ hZ.mem_toFinset
  have hnZ := sum_zetaOrder_le_of_window hT hZf
  have hN : (hZ.toFinset.card : ℝ) ≤ ∑ ρ ∈ hZ.toFinset, (zetaOrder ρ : ℝ) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    exact Finset.sum_le_sum fun ρ hρ ↦ by
      obtain ⟨⟨h0, h1⟩, -, hz⟩ := (hZf ρ).1 hρ
      exact one_le_zetaOrder h0 h1 hz
  -- the height `T₁`
  obtain ⟨T₁, hT₁, hfar⟩ := exists_far_point (hZ.toFinset.image Complex.im) T
  have hη0 : (0 : ℝ) < 1 / (2 * ((hZ.toFinset.card : ℝ) + 1)) := by positivity
  have hsep : ∀ ρ ∈ hZ.toFinset, 1 / (2 * ((hZ.toFinset.card : ℝ) + 1)) ≤ |T₁ - ρ.im| := by
    intro ρ hρ
    refine le_trans ?_ (hfar _ (Finset.mem_image_of_mem _ hρ))
    have hcard : ((hZ.toFinset.image Complex.im).card : ℝ) ≤ hZ.toFinset.card := by
      exact_mod_cast Finset.card_image_le
    gcongr
  refine ⟨T₁, hT₁, fun σ hσ ↦ ?_⟩
  have hz := riemannZeta_ne_zero_of_far hT₁ hT hη0 hZf hsep σ
  refine ⟨hz, ?_⟩
  rw [← logDeriv_apply]
  have hT₁2 : 2 ≤ T₁ := by linarith [hT₁.1]
  have hright : ∀ σ' ∈ Icc (1 / 2 : ℝ) 2, ‖logDeriv riemannZeta (σ' + T₁ * I)‖ ≤
      (∑ ρ ∈ hZ.toFinset, (zetaOrder ρ : ℝ)) / (1 / (2 * ((hZ.toFinset.card : ℝ) + 1))) +
        landauConst * (1 + Real.log (48 * (T + 5))) :=
    fun σ' hσ' ↦ norm_logDeriv_riemannZeta_le_right hT₁ hT hη0 hZf hsep hσ'
  have hηeq : (∑ ρ ∈ hZ.toFinset, (zetaOrder ρ : ℝ)) / (1 / (2 * ((hZ.toFinset.card : ℝ) + 1))) =
      2 * (∑ ρ ∈ hZ.toFinset, (zetaOrder ρ : ℝ)) * ((hZ.toFinset.card : ℝ) + 1) := by
    field_simp
  refine good_height_arith hT hK₀0 landauConst_nonneg hnZ hN (Nat.cast_nonneg _) ?_
  rw [← hηeq]
  have hpi := Real.pi_pos
  have hlog2π : 0 ≤ Real.log (2 * π) := Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  rcases lt_or_ge σ (1 / 2) with hσ' | hσ'
  · have h := norm_logDeriv_riemannZeta_le_left hFE hT₁2 hσ' hσ.1 hz
      (hright (1 - σ) ⟨by linarith, by linarith [hσ.1]⟩) hCD
    have hlog : CD * Real.log (T₁ + 2) ≤ |CD| * Real.log (T + 3) := by
      calc CD * Real.log (T₁ + 2) ≤ |CD| * Real.log (T₁ + 2) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (Real.log_nonneg (by linarith))
        _ ≤ |CD| * Real.log (T + 3) :=
            mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) (by linarith [hT₁.2]))
              (abs_nonneg _)
    linarith
  · have h := hright σ ⟨hσ', hσ.2⟩
    have : 0 ≤ |CD| * Real.log (T + 3) :=
      mul_nonneg (abs_nonneg _) (Real.log_nonneg (by linarith))
    linarith

/-- **Montgomery–Vaughan, Lemma 12.2**, with the functional equation of `ζ'/ζ` from
`ZetaLogDeriv.lean`. -/
theorem exists_good_height : ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T → ∃ T₁ ∈ Set.Icc T (T + 1),
    ∀ σ ∈ Set.Icc (-1 : ℝ) 2,
      riemannZeta (σ + T₁ * Complex.I) ≠ 0 ∧
        ‖deriv riemannZeta (σ + T₁ * Complex.I) / riemannZeta (σ + T₁ * Complex.I)‖ ≤
          C * Real.log T ^ 2 :=
  exists_good_height_of logDeriv_functional_equation

/-- **Good heights with a margin.** Montgomery–Vaughan's choice of `T₁` in their proof of
Lemma 12.2 keeps `T₁` at distance at least `c / log T` from the ordinate of every non-trivial zero:
it is at distance at least `1/(2(N + 1))`, with `N ≪ log T`, from the ordinates in
`[T - 2, T + 3]`, and at distance at least `2` from the others. This is `exists_good_height_of`
with that margin added (and with `C > 0`); the functional equation of `ζ'/ζ` is a hypothesis, as
there. -/
theorem exists_good_height_margin_of (hFE : LogDerivFunctionalEquation) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ T : ℝ, 2 ≤ T → ∃ T₁ ∈ Set.Icc T (T + 1),
      (∀ ρ ∈ zetaZeroesIn (Set.Ioo 0 1) Set.univ, c / Real.log T ≤ |T₁ - ρ.im|) ∧
      ∀ σ ∈ Set.Icc (-1 : ℝ) 2,
        riemannZeta (σ + T₁ * Complex.I) ≠ 0 ∧
          ‖deriv riemannZeta (σ + T₁ * Complex.I) / riemannZeta (σ + T₁ * Complex.I)‖ ≤
            C * Real.log T ^ 2 := by
  obtain ⟨CD, hCD⟩ := Complex.exists_norm_digamma_le_log (σ₁ := 1) (σ₂ := 5 / 2) one_pos
  have hK₀0 : (0 : ℝ) ≤ 20 / Real.log (22 / 21) :=
    div_nonneg (by norm_num) (Real.log_pos (by norm_num)).le
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hpi0 := Real.pi_pos
  have hΛ0 := landauConst_nonneg
  refine ⟨450 * (20 / Real.log (22 / 21)) ^ 2 +
    (30 * (20 / Real.log (22 / 21)) + 9 * landauConst + 3 * |CD|) / Real.log 2 +
    (landauConst + Real.log (2 * π) + 1 + π) / Real.log 2 ^ 2,
    1 / (30 * (20 / Real.log (22 / 21)) + 2 / Real.log 2), ?_, by positivity, fun T hT ↦ ?_⟩
  · have hlog2π : 0 ≤ Real.log (2 * π) := Real.log_nonneg (by nlinarith [Real.pi_gt_three])
    have h1 : 0 ≤ 450 * (20 / Real.log (22 / 21)) ^ 2 := by positivity
    have h2 : 0 ≤ (30 * (20 / Real.log (22 / 21)) + 9 * landauConst + 3 * |CD|) / Real.log 2 :=
      div_nonneg (by positivity) hlog2.le
    have h3 : 0 < (landauConst + Real.log (2 * π) + 1 + π) / Real.log 2 ^ 2 :=
      div_pos (by linarith) (by positivity)
    linarith
  -- the zeros near `[T, T + 1]`
  have hZ : (zetaZeroesIn (Ioo 0 1) (Icc (T - 2) (T + 3))).Finite :=
    zetaZeroesIn_finite Ioo_subset_Icc_self subset_rfl
  have hZf : ∀ ρ, ρ ∈ hZ.toFinset ↔ ρ ∈ zetaZeroesIn (Ioo 0 1) (Icc (T - 2) (T + 3)) :=
    fun ρ ↦ hZ.mem_toFinset
  have hnZ := sum_zetaOrder_le_of_window hT hZf
  have hN : (hZ.toFinset.card : ℝ) ≤ ∑ ρ ∈ hZ.toFinset, (zetaOrder ρ : ℝ) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    exact Finset.sum_le_sum fun ρ hρ ↦ by
      obtain ⟨⟨h0, h1⟩, -, hz⟩ := (hZf ρ).1 hρ
      exact one_le_zetaOrder h0 h1 hz
  -- the height `T₁`
  obtain ⟨T₁, hT₁, hfar⟩ := exists_far_point (hZ.toFinset.image Complex.im) T
  have hη0 : (0 : ℝ) < 1 / (2 * ((hZ.toFinset.card : ℝ) + 1)) := by positivity
  have hsep : ∀ ρ ∈ hZ.toFinset, 1 / (2 * ((hZ.toFinset.card : ℝ) + 1)) ≤ |T₁ - ρ.im| := by
    intro ρ hρ
    refine le_trans ?_ (hfar _ (Finset.mem_image_of_mem _ hρ))
    have hcard : ((hZ.toFinset.image Complex.im).card : ℝ) ≤ hZ.toFinset.card := by
      exact_mod_cast Finset.card_image_le
    gcongr
  -- the margin
  have hlogT : Real.log 2 ≤ Real.log T := Real.log_le_log two_pos hT
  have hlogT0 : 0 < Real.log T := hlog2.trans_le hlogT
  have hmargin : ∀ ρ ∈ zetaZeroesIn (Set.Ioo 0 1) Set.univ,
      1 / (30 * (20 / Real.log (22 / 21)) + 2 / Real.log 2) / Real.log T ≤ |T₁ - ρ.im| := by
    intro ρ hρ
    obtain ⟨hre, -, hz⟩ := hρ
    by_cases hw : ρ.im ∈ Icc (T - 2) (T + 3)
    · refine le_trans ?_ (hsep ρ ((hZf ρ).2 ⟨hre, hw, hz⟩))
      have hlogT4 : Real.log (T + 4) ≤ 3 * Real.log T := by
        have h3 : Real.log (T ^ 3) = 3 * Real.log T := by
          rw [Real.log_pow]
          norm_num
        rw [← h3]
        have h4 : 4 ≤ T ^ 2 := by nlinarith
        have h5 : T * 4 ≤ T * T ^ 2 := mul_le_mul_of_nonneg_left h4 (by linarith)
        exact Real.log_le_log (by linarith) (by nlinarith)
      have hNle : (hZ.toFinset.card : ℝ) ≤ 15 * (20 / Real.log (22 / 21)) * Real.log T := by
        calc (hZ.toFinset.card : ℝ)
            ≤ 5 * (20 / Real.log (22 / 21) * Real.log (T + 4)) := hN.trans hnZ
          _ ≤ 5 * (20 / Real.log (22 / 21) * (3 * Real.log T)) := by gcongr
          _ = 15 * (20 / Real.log (22 / 21)) * Real.log T := by ring
      have h2 : 2 ≤ 2 * Real.log T / Real.log 2 := by
        rw [le_div_iff₀ hlog2]
        linarith
      rw [div_div, one_div_le_one_div (by positivity) (by positivity)]
      calc 2 * ((hZ.toFinset.card : ℝ) + 1)
          ≤ 2 * (15 * (20 / Real.log (22 / 21)) * Real.log T) + 2 * Real.log T / Real.log 2 := by
            linarith
        _ = (30 * (20 / Real.log (22 / 21)) + 2 / Real.log 2) * Real.log T := by ring
    · have hfar2 : 2 ≤ |T₁ - ρ.im| := by
        simp only [mem_Icc, not_and_or, not_le] at hw
        rcases hw with h | h
        · rw [abs_of_pos (by linarith [hT₁.1])]
          linarith [hT₁.1]
        · rw [abs_of_neg (by linarith [hT₁.2])]
          linarith [hT₁.2]
      refine le_trans ?_ hfar2
      have hc : 1 / (30 * (20 / Real.log (22 / 21)) + 2 / Real.log 2) ≤ Real.log 2 / 2 := by
        calc 1 / (30 * (20 / Real.log (22 / 21)) + 2 / Real.log 2) ≤ 1 / (2 / Real.log 2) :=
              one_div_le_one_div_of_le (div_pos two_pos hlog2)
                (le_add_of_nonneg_left (mul_nonneg (by norm_num : (0 : ℝ) ≤ 30) hK₀0))
          _ = Real.log 2 / 2 := one_div_div 2 (Real.log 2)
      rw [div_le_iff₀ hlogT0]
      nlinarith
  refine ⟨T₁, hT₁, hmargin, fun σ hσ ↦ ?_⟩
  have hz := riemannZeta_ne_zero_of_far hT₁ hT hη0 hZf hsep σ
  refine ⟨hz, ?_⟩
  rw [← logDeriv_apply]
  have hT₁2 : 2 ≤ T₁ := by linarith [hT₁.1]
  have hright : ∀ σ' ∈ Icc (1 / 2 : ℝ) 2, ‖logDeriv riemannZeta (σ' + T₁ * I)‖ ≤
      (∑ ρ ∈ hZ.toFinset, (zetaOrder ρ : ℝ)) / (1 / (2 * ((hZ.toFinset.card : ℝ) + 1))) +
        landauConst * (1 + Real.log (48 * (T + 5))) :=
    fun σ' hσ' ↦ norm_logDeriv_riemannZeta_le_right hT₁ hT hη0 hZf hsep hσ'
  have hηeq : (∑ ρ ∈ hZ.toFinset, (zetaOrder ρ : ℝ)) / (1 / (2 * ((hZ.toFinset.card : ℝ) + 1))) =
      2 * (∑ ρ ∈ hZ.toFinset, (zetaOrder ρ : ℝ)) * ((hZ.toFinset.card : ℝ) + 1) := by
    field_simp
  refine good_height_arith hT hK₀0 landauConst_nonneg hnZ hN (Nat.cast_nonneg _) ?_
  rw [← hηeq]
  have hpi := Real.pi_pos
  have hlog2π : 0 ≤ Real.log (2 * π) := Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  rcases lt_or_ge σ (1 / 2) with hσ' | hσ'
  · have h := norm_logDeriv_riemannZeta_le_left hFE hT₁2 hσ' hσ.1 hz
      (hright (1 - σ) ⟨by linarith, by linarith [hσ.1]⟩) hCD
    have hlog : CD * Real.log (T₁ + 2) ≤ |CD| * Real.log (T + 3) := by
      calc CD * Real.log (T₁ + 2) ≤ |CD| * Real.log (T₁ + 2) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (Real.log_nonneg (by linarith))
        _ ≤ |CD| * Real.log (T + 3) :=
            mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) (by linarith [hT₁.2]))
              (abs_nonneg _)
    linarith
  · have h := hright σ ⟨hσ', hσ.2⟩
    have : 0 ≤ |CD| * Real.log (T + 3) :=
      mul_nonneg (abs_nonneg _) (Real.log_nonneg (by linarith))
    linarith

/-- Good heights with a margin, with the functional equation of `ζ'/ζ` from
`ZetaLogDeriv.lean`. -/
theorem exists_good_height_margin :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ T : ℝ, 2 ≤ T → ∃ T₁ ∈ Set.Icc T (T + 1),
      (∀ ρ ∈ zetaZeroesIn (Set.Ioo 0 1) Set.univ, c / Real.log T ≤ |T₁ - ρ.im|) ∧
      ∀ σ ∈ Set.Icc (-1 : ℝ) 2,
        riemannZeta (σ + T₁ * Complex.I) ≠ 0 ∧
          ‖deriv riemannZeta (σ + T₁ * Complex.I) / riemannZeta (σ + T₁ * Complex.I)‖ ≤
            C * Real.log T ^ 2 :=
  exists_good_height_margin_of logDeriv_functional_equation

end WeilExplicitFormula
