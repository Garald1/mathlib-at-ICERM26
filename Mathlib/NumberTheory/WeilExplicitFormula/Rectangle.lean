/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Harald Helfgott
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Analytic.Order

/-! # The argument principle with a weight, on a rectangle

Part D1 of the blueprint for Montgomery–Vaughan, *Multiplicative Number Theory I*, Theorem 12.13:
if `f` and `φ` are analytic near a closed rectangle `R`, and the zeros of `f` in `R` lie in a finite
set `P` of interior points, then
`∮_{∂R} φ f'/f = 2πi ∑_{ρ ∈ P} ord_ρ(f) φ(ρ)`.

Mathlib has Cauchy's theorem on rectangles but not the residue theorem. The latter is assumed
here, in the form of the IEANTN conclusion `ContourIntegration.v1.residue_theorem_rectangle`
(`ResidueTheoremRectangle`, copied verbatim): the boundary integral of a function holomorphic on
the rectangle off a finite set `P` equals the sum of its integrals over small circles around the
points of `P`. Each circle integral is then computed by writing `f = (s - ρ)^m g` near `ρ`
with `g(ρ) ≠ 0` (Cauchy's integral formula for `m φ(s)/(s - ρ)`, Cauchy's theorem for `φ g'/g`).

## Main results

* `rectIntegral`: the boundary integral, in the shape of
  `Complex.integral_boundary_rect_eq_zero_of_differentiableOn` (as in the draft
  `blueprint/drafts/WeilExplicitFormula.lean`).
* `ResidueTheoremRectangle`: the statement of `ContourIntegration.v1.residue_theorem_rectangle`.
* `circleIntegral_mul_logDeriv`: `∮_{|s-ρ|=r} φ f'/f = 2πi m φ(ρ)` when `f = (s - ρ)^m g` on a
  disc of radius `> r` around `ρ`, with `g` holomorphic and zero-free there.
* `rectIntegral_mul_logDeriv_eq_sum`: the argument principle with a weight (D1).

## AI usage

This file was written by Claude (Anthropic) in November 2026. It compiles, but has not been
reviewed by a human.
-/

@[expose] public section

open Real Complex Filter Topology Set Metric MeasureTheory
open scoped Interval

noncomputable section

namespace WeilExplicitFormula

/-- The integral of `f` over the boundary of the rectangle with opposite corners `z` and `w`
(counterclockwise if `z.re < w.re` and `z.im < w.im`); this is the expression of
`Complex.integral_boundary_rect_eq_zero_of_differentiableOn`. -/
def rectIntegral (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
    I * (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) - I * (∫ y : ℝ in z.im..w.im, f (z.re + y * I))

/-- **The residue theorem on a rectangle**, with residues written as circle integrals: the
statement of the IEANTN conclusion `ContourIntegration.v1.residue_theorem_rectangle`, copied
verbatim. It is used as a hypothesis. -/
def ResidueTheoremRectangle : Prop :=
  ∀ (z w : ℂ) (P : Finset ℂ) (r : ℝ) (f : ℂ → ℂ),
    z.re < w.re → z.im < w.im → 0 < r →
    (∀ ρ ∈ P, z.re < ρ.re - r ∧ ρ.re + r < w.re ∧ z.im < ρ.im - r ∧ ρ.im + r < w.im) →
    (∀ ρ ∈ P, ∀ σ ∈ P, ρ ≠ σ → 2 * r < dist ρ σ) →
    DifferentiableOn ℂ f ((Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) \ ↑P) →
      (∫ x : ℝ in z.re..w.re, f (x + z.im * Complex.I))
        - (∫ x : ℝ in z.re..w.re, f (x + w.im * Complex.I))
        + Complex.I * (∫ y : ℝ in z.im..w.im, f (w.re + y * Complex.I))
        - Complex.I * (∫ y : ℝ in z.im..w.im, f (z.re + y * Complex.I))
        = ∑ ρ ∈ P, (∮ ζ in C(ρ, r), f ζ)

theorem logDeriv_sub_const (ρ s : ℂ) : logDeriv (fun u ↦ u - ρ) s = 1 / (s - ρ) := by
  rw [logDeriv_apply, deriv_sub_const, deriv_id'']

/-- The circle integral of `φ f'/f` around a zero of order `m` of `f`. -/
theorem circleIntegral_mul_logDeriv {f φ g : ℂ → ℂ} {ρ : ℂ} {ε r : ℝ} {m : ℕ}
    (hr : 0 < r) (hrε : r < ε)
    (hg : DifferentiableOn ℂ g (ball ρ ε)) (hg0 : ∀ s ∈ ball ρ ε, g s ≠ 0)
    (hfg : ∀ s ∈ ball ρ ε, f s = (s - ρ) ^ m * g s)
    (hφ : DifferentiableOn ℂ φ (ball ρ ε)) :
    ∮ s in C(ρ, r), φ s * logDeriv f s = 2 * π * I * (m * φ ρ) := by
  have hcl : closedBall ρ r ⊆ ball ρ ε := closedBall_subset_ball hrε
  have hgd : DifferentiableOn ℂ (fun s ↦ φ s * logDeriv g s) (ball ρ ε) := by
    have : DifferentiableOn ℂ (fun s ↦ deriv g s / g s) (ball ρ ε) :=
      (hg.deriv isOpen_ball).div hg hg0
    exact hφ.mul this
  have heq : EqOn (fun s ↦ φ s * logDeriv f s)
      (fun s ↦ (m : ℂ) * ((s - ρ)⁻¹ • φ s) + φ s * logDeriv g s) (sphere ρ r) := by
    intro s hs
    have hsb : s ∈ ball ρ ε := hcl (sphere_subset_closedBall hs)
    have hsρ : s - ρ ≠ 0 := by
      intro h
      rw [mem_sphere, dist_eq_norm, h, norm_zero] at hs
      exact hr.ne hs
    have hev : f =ᶠ[𝓝 s] fun u ↦ (u - ρ) ^ m * g u :=
      Filter.eventually_of_mem (isOpen_ball.mem_nhds hsb) hfg
    have hgs : DifferentiableAt ℂ g s := hg.differentiableAt (isOpen_ball.mem_nhds hsb)
    have hlog : logDeriv f s = logDeriv (fun u ↦ (u - ρ) ^ m * g u) s := by
      rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
    have hpow : DifferentiableAt ℂ (fun u ↦ (u - ρ) ^ m) s := by fun_prop
    simp only [smul_eq_mul]
    rw [hlog, logDeriv_mul (f := fun u ↦ (u - ρ) ^ m) (g := g) s (pow_ne_zero m hsρ) (hg0 s hsb)
      hpow hgs,
      logDeriv_fun_pow (f := fun u : ℂ ↦ u - ρ) (x := s) (by fun_prop) m, logDeriv_sub_const]
    ring
  have hi1 : CircleIntegrable (fun s ↦ (m : ℂ) * ((s - ρ)⁻¹ • φ s)) ρ r := by
    refine ContinuousOn.circleIntegrable hr.le ?_
    refine continuousOn_const.mul (ContinuousOn.smul ?_ ?_)
    · refine ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const) fun s hs h ↦ ?_
      rw [mem_sphere, dist_eq_norm, h, norm_zero] at hs
      exact hr.ne hs
    · exact (hφ.mono (sphere_subset_closedBall.trans hcl)).continuousOn
  have hi2 : CircleIntegrable (fun s ↦ φ s * logDeriv g s) ρ r :=
    ContinuousOn.circleIntegrable hr.le
      (hgd.mono (sphere_subset_closedBall.trans hcl)).continuousOn
  rw [circleIntegral.integral_congr hr.le heq, circleIntegral.integral_add hi1 hi2,
    circleIntegral.integral_const_mul,
    (hφ.mono hcl).circleIntegral_sub_inv_smul (mem_ball_self hr),
    ((hgd.mono hcl).mono closure_ball_subset_closedBall).diffContOnCl.circleIntegral_eq_zero hr.le]
  simp only [smul_eq_mul, add_zero]
  ring

/-- Near a point of finite order, an analytic function is `(s - ρ)^m g(s)` on a disc, with `g`
holomorphic and zero-free there; the disc can be taken inside any given neighbourhood. -/
theorem exists_ball_factor {f : ℂ → ℂ} {ρ : ℂ} (hf : AnalyticAt ℂ f ρ)
    (hfin : analyticOrderAt f ρ ≠ ⊤) {U : Set ℂ} (hU : U ∈ 𝓝 ρ) :
    ∃ ε > 0, ∃ g : ℂ → ℂ, ball ρ ε ⊆ U ∧ DifferentiableOn ℂ g (ball ρ ε) ∧
      (∀ s ∈ ball ρ ε, g s ≠ 0) ∧
      ∀ s ∈ ball ρ ε, f s = (s - ρ) ^ analyticOrderNatAt f ρ * g s := by
  have hm : analyticOrderAt f ρ = (analyticOrderNatAt f ρ : ℕ∞) :=
    (Nat.cast_analyticOrderNatAt hfin).symm
  obtain ⟨g, hga, hg0, hev⟩ := hf.analyticOrderAt_eq_natCast.1 hm
  have h1 := hga.eventually_analyticAt
  have h2 := hga.continuousAt.eventually_ne hg0
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (((h1.and h2).and hev).and hU)
  refine ⟨ε, hε, g, fun s hs ↦ (hball s hs).2, fun s hs ↦ ?_, fun s hs ↦ (hball s hs).1.1.2,
    fun s hs ↦ ?_⟩
  · exact (hball s hs).1.1.1.differentiableAt.differentiableWithinAt
  · rw [(hball s hs).1.2, smul_eq_mul]

/-- **The argument principle with a holomorphic weight** on a rectangle (D1), from the residue
theorem: if `f` and `φ` are analytic on the closed rectangle `R` with corners `z`, `w`, and every
zero of `f` in `R` lies in the finite set `P` of interior points, then
`∮_{∂R} φ f'/f = 2πi ∑_{ρ ∈ P} ord_ρ(f) φ(ρ)`. -/
theorem rectIntegral_mul_logDeriv_eq_sum (hres : ResidueTheoremRectangle) {f φ : ℂ → ℂ}
    {z w : ℂ} {P : Finset ℂ} (hre : z.re < w.re) (him : z.im < w.im)
    (hf : AnalyticOnNhd ℂ f ([[z.re, w.re]] ×ℂ [[z.im, w.im]]))
    (hφ : AnalyticOnNhd ℂ φ ([[z.re, w.re]] ×ℂ [[z.im, w.im]]))
    (hP : ∀ ρ ∈ P, ρ ∈ Ioo z.re w.re ×ℂ Ioo z.im w.im)
    (hzero : ∀ u ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]], f u = 0 → u ∈ P) :
    rectIntegral (fun s ↦ φ s * logDeriv f s) z w =
      2 * π * I * ∑ ρ ∈ P, (analyticOrderNatAt f ρ : ℂ) * φ ρ := by
  set R := [[z.re, w.re]] ×ℂ [[z.im, w.im]] with hRdef
  set Q := Ioo z.re w.re ×ℂ Ioo z.im w.im with hQdef
  have hQo : IsOpen Q := isOpen_Ioo.reProdIm isOpen_Ioo
  have hQR : Q ⊆ R := by
    intro u hu
    rw [hQdef, mem_reProdIm] at hu
    rw [hRdef, mem_reProdIm, uIcc_of_le hre.le, uIcc_of_le him.le]
    exact ⟨Ioo_subset_Icc_self hu.1, Ioo_subset_Icc_self hu.2⟩
  -- the orders at the points of `P` are finite
  have hfin : ∀ ρ ∈ P, analyticOrderAt f ρ ≠ ⊤ := by
    intro ρ hρ htop
    have hev : ∀ᶠ s in 𝓝 ρ, f s = 0 := analyticOrderAt_eq_top.1 htop
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hev.and (hQo.mem_nhds (hP ρ hρ)))
    have hinf : (Ioo (0 : ℝ) ε).Infinite := Ioo_infinite hε
    have hinf' : ((fun t : ℝ ↦ ρ + t) '' Ioo (0 : ℝ) ε).Infinite :=
      hinf.image (fun a _ b _ h ↦ by simpa using h)
    obtain ⟨u, hu, huP⟩ := hinf'.exists_notMem_finset P
    obtain ⟨t, ht, rfl⟩ := hu
    have hb : ρ + (t : ℂ) ∈ ball ρ ε := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos ht.1]
      exact ht.2
    exact huP (hzero _ (hQR (hball _ hb).2) (hball _ hb).1)
  -- local factorizations
  have hloc : ∀ ρ ∈ P, ∃ ε > 0, ∃ g : ℂ → ℂ, ball ρ ε ⊆ Q ∩ {s | AnalyticAt ℂ φ s} ∧
      DifferentiableOn ℂ g (ball ρ ε) ∧ (∀ s ∈ ball ρ ε, g s ≠ 0) ∧
      ∀ s ∈ ball ρ ε, f s = (s - ρ) ^ analyticOrderNatAt f ρ * g s := by
    intro ρ hρ
    refine exists_ball_factor (hf ρ (hQR (hP ρ hρ))) (hfin ρ hρ) ?_
    exact Filter.inter_mem (hQo.mem_nhds (hP ρ hρ)) (hφ ρ (hQR (hP ρ hρ))).eventually_analyticAt
  choose! ε hε g hsub hgd hg0 hfg using hloc
  -- a common radius
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r ∧
      (∀ ρ ∈ P, z.re < ρ.re - r ∧ ρ.re + r < w.re ∧ z.im < ρ.im - r ∧ ρ.im + r < w.im) ∧
      (∀ ρ ∈ P, ∀ σ ∈ P, ρ ≠ σ → 2 * r < dist ρ σ) ∧ (∀ ρ ∈ P, r < ε ρ) := by
    refine (eventually_mem_nhdsWithin).and (Filter.Eventually.and ?_ (Filter.Eventually.and ?_ ?_))
    · refine (Filter.eventually_all_finset P).2 fun ρ hρ ↦ ?_
      have hρQ := hP ρ hρ
      rw [hQdef, mem_reProdIm] at hρQ
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hρQ
      refine nhdsWithin_le_nhds ?_
      filter_upwards [eventually_lt_nhds (show (0 : ℝ) < ρ.re - z.re by linarith),
        eventually_lt_nhds (show (0 : ℝ) < w.re - ρ.re by linarith),
        eventually_lt_nhds (show (0 : ℝ) < ρ.im - z.im by linarith),
        eventually_lt_nhds (show (0 : ℝ) < w.im - ρ.im by linarith)] with r e1 e2 e3 e4
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
    · refine (Filter.eventually_all_finset P).2 fun ρ _ ↦
        (Filter.eventually_all_finset P).2 fun σ _ ↦ ?_
      by_cases hρσ : ρ = σ
      · exact Filter.Eventually.of_forall fun r h ↦ absurd hρσ h
      · have hd : 0 < dist ρ σ / 2 := by have := dist_pos.2 hρσ; linarith
        refine nhdsWithin_le_nhds ?_
        filter_upwards [eventually_lt_nhds hd] with r hr _
        linarith
    · refine (Filter.eventually_all_finset P).2 fun ρ hρ ↦ ?_
      exact nhdsWithin_le_nhds (eventually_lt_nhds (hε ρ hρ))
  obtain ⟨r, hr0, hbox, hdisj, hrε⟩ := hev.exists
  -- holomorphy off `P`
  have hdiff : DifferentiableOn ℂ (fun s ↦ φ s * logDeriv f s) (R \ ↑P) := by
    intro u hu
    have hfu : f u ≠ 0 := fun h ↦ hu.2 (hzero u hu.1 h)
    have h1 : DifferentiableAt ℂ (fun s ↦ deriv f s / f s) u :=
      (hf u hu.1).deriv.differentiableAt.div (hf u hu.1).differentiableAt hfu
    exact ((hφ u hu.1).differentiableAt.mul h1).differentiableWithinAt
  have h := hres z w P r (fun s ↦ φ s * logDeriv f s) hre him hr0 hbox hdisj hdiff
  rw [rectIntegral, h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ρ hρ ↦ ?_
  rw [circleIntegral_mul_logDeriv hr0 (hrε ρ hρ) (hgd ρ hρ) (hg0 ρ hρ) (hfg ρ hρ)
    (fun s hs ↦ ((hsub ρ hρ hs).2 : AnalyticAt ℂ φ s).differentiableAt.differentiableWithinAt)]

end WeilExplicitFormula
