/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Harald Helfgott
-/
module

public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.Complex.BorelCaratheodory
public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Meromorphic.FactorizedRational
public import Mathlib.Analysis.Calculus.LogDeriv

/-! # Landau's lemma: the logarithmic derivative near the zeros

**Landau's lemma** (Montgomery–Vaughan, Lemma 6.3, in the form of
`blueprint/proofs/GoodHeights.md`, (L)): let `f` be analytic on a neighbourhood of
`closedBall c R₀`, with `f c ≠ 0` and `‖f‖ ≤ M` there (`M ≥ 1`), and let `0 < r < R < R₀`. Then
there is a finite set `S` of zeros of `f`, all with `‖u - c‖ ≤ R`, such that for `‖z - c‖ ≤ r`,
`f z ≠ 0`,
`‖f'/f (z) - ∑_{u ∈ S} m_u / (z - u)‖ ≤ A (1 + log (M / ‖f c‖))`,
where `m_u` is the order of the zero `u` and `A` depends only on `r, R, R₀`
(`exists_norm_logDeriv_sub_sum_le`).

[MV]'s statement sums over all the zeros with `‖u - c‖ ≤ R`; ours sums over those with
`‖u - c‖ < R''` for a radius `R < R'' ≤ (R + R₀)/2` chosen so that no zero has
`R < ‖u - c‖ < R''`, which is all that the application (Lemma 12.2) needs.

The proof is [MV]'s: with `R < R' < R''` and `U = ball c R''`,
* Mathlib's `MeromorphicOn.extract_zeros_poles` writes `f = P g` on `U`, `P(z) = ∏ (z - u)^{m_u}`,
  `g` analytic and zero-free on `U` (`exists_eq_prod_mul`);
* `G = g ∏ ((R'² - conj (u - c) (z - c))/R')^{m_u}` is analytic on `U`, zero-free on
  `closedBall c R'`, `‖G‖ = ‖f‖ ≤ M` on the circle of radius `R'`, so `‖G‖ ≤ M` inside (maximum
  modulus), and `‖G c‖ ≥ ‖f c‖`;
* `G'/G` has a primitive `h` on `ball c R'` with `h c = 0` (`DifferentiableOn.isExactOn_ball`),
  `G = G(c) e^h`, so `Re h ≤ log (M / ‖f c‖)`; Borel–Carathéodory (`Complex.borelCaratheodory_zero`)
  bounds `h`, and Cauchy's estimate bounds `h' = G'/G` on `closedBall c r`;
* `f'/f - ∑ m_u/(z - u) = g'/g = G'/G - ∑ m_u (log B_u)'`, and each `(log B_u)'` is at most
  `1/(R' - r)`; Jensen's inequality (`AnalyticOnNhd.sum_divisor_le`) bounds `∑ m_u`.

## AI usage

This file was written by Claude (Anthropic) in November 2026. It compiles, but has not been
reviewed by a human.
-/

@[expose] public section

open Complex Metric Set Filter Topology MeromorphicOn
open scoped ComplexConjugate

noncomputable section

namespace WeilExplicitFormula

/-! ### Divisors and orders of analytic functions -/

theorem sum_le_finsum_of_nonneg {α : Type*} {f : α → ℤ} (hf : ∀ a, 0 ≤ f a)
    (hs : (Function.support f).Finite) (s : Finset α) : ∑ a ∈ s, f a ≤ ∑ᶠ a, f a := by
  classical
  rw [finsum_eq_sum_of_support_subset f (s := s ∪ hs.toFinset) (fun a ha ↦ by simp [ha])]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left fun a _ _ ↦ hf a

theorem divisor_eq_analyticOrderNatAt {f : ℂ → ℂ} {U : Set ℂ} (hf : AnalyticOnNhd ℂ f U)
    {u : ℂ} (hu : u ∈ U) : divisor f U u = analyticOrderNatAt f u := by
  rw [hf.divisor_apply hu]
  unfold analyticOrderNatAt
  cases analyticOrderAt f u with
  | top => simp
  | coe n => simp

theorem analyticOrderAt_ne_top_of_ne_zero {f : ℂ → ℂ} {U : Set ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hU : IsPreconnected U) {x u : ℂ} (hx : x ∈ U) (hfx : f x ≠ 0) (hu : u ∈ U) :
    analyticOrderAt f u ≠ ⊤ :=
  hf.analyticOrderAt_ne_top_of_isPreconnected hU hx hu
    (by rw [(hf x hx).analyticOrderAt_eq_zero.2 hfx]; exact ENat.zero_ne_top)

theorem one_le_analyticOrderNatAt {f : ℂ → ℂ} {u : ℂ} (hf : AnalyticAt ℂ f u) (hfu : f u = 0)
    (htop : analyticOrderAt f u ≠ ⊤) : 1 ≤ analyticOrderNatAt f u := by
  have h0 : analyticOrderAt f u ≠ 0 := fun h ↦ (hf.analyticOrderAt_eq_zero.1 h) hfu
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 htop
  unfold analyticOrderNatAt
  rw [← hn] at h0 ⊢
  rw [ENat.toNat_coe, Nat.one_le_iff_ne_zero]
  rintro rfl
  exact h0 rfl

/-- A finite set of reals has a gap above `R`: some `d ∈ (R, R₂]` with no element in `(R, d)`. -/
theorem exists_gap (D : Finset ℝ) {R R₂ : ℝ} (h : R < R₂) :
    ∃ d, R < d ∧ d ≤ R₂ ∧ ∀ x ∈ D, R < x → d ≤ x := by
  classical
  set E := (D.filter (fun x ↦ R < x)) ∪ {R₂} with hE
  have hne : E.Nonempty := ⟨R₂, by simp [hE]⟩
  refine ⟨E.min' hne, ?_, E.min'_le _ (by simp [hE]),
    fun x hx hRx ↦ E.min'_le _ (by simp [hE, hx, hRx])⟩
  rw [Finset.lt_min'_iff]
  intro y hy
  simp only [hE, Finset.mem_union, Finset.mem_filter, Finset.mem_singleton] at hy
  rcases hy with ⟨-, hy⟩ | rfl
  · exact hy
  · exact h

/-! ### Factoring out the zeros on a disc -/

/-- On a disc where `f` is analytic, not identically zero, with finitely many zeros,
`f = (∏ (z - u)^{m_u}) g` with `g` analytic and zero-free. -/
theorem exists_eq_prod_mul {f : ℂ → ℂ} {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hf : AnalyticOnNhd ℂ f (ball c ρ)) (hfc : f c ≠ 0)
    (hfin : {u | u ∈ ball c ρ ∧ f u = 0}.Finite) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (ball c ρ) ∧ (∀ z ∈ ball c ρ, g z ≠ 0) ∧
      ∀ z ∈ ball c ρ, f z = (∏ u ∈ hfin.toFinset, (z - u) ^ analyticOrderNatAt f u) * g z := by
  classical
  have hcU : c ∈ ball c ρ := mem_ball_self hρ
  have hpre : IsPreconnected (ball c ρ) := (convex_ball c ρ).isPreconnected
  have htop : ∀ u ∈ ball c ρ, analyticOrderAt f u ≠ ⊤ := fun u hu ↦
    analyticOrderAt_ne_top_of_ne_zero hf hpre hcU hfc hu
  have h₂f : ∀ u : ball c ρ, meromorphicOrderAt f u ≠ ⊤ := by
    intro u
    rw [(hf u u.2).meromorphicOrderAt_eq]
    simpa using htop u u.2
  have hsupp : (divisor f (ball c ρ)).support ⊆ {u | u ∈ ball c ρ ∧ f u = 0} := by
    intro u hu
    have huU : u ∈ ball c ρ := (divisor f (ball c ρ)).supportWithinDomain hu
    refine ⟨huU, ?_⟩
    by_contra hfu
    apply hu
    rw [hf.divisor_apply huU, (hf u huU).analyticOrderAt_eq_zero.2 hfu]
    simp
  have h₃f : (divisor f (ball c ρ)).support.Finite := hfin.subset hsupp
  obtain ⟨g, hgA, hg0, heq⟩ := hf.meromorphicOn.extract_zeros_poles h₂f h₃f
  set P : ℂ → ℂ := fun z ↦ ∏ u ∈ hfin.toFinset, (z - u) ^ analyticOrderNatAt f u with hP
  have hPeq : (∏ᶠ u, (· - u) ^ divisor f (ball c ρ) u) = P := by
    rw [Function.FactorizedRational.finprod_eq_fun h₃f]
    funext z
    rw [finprod_eq_prod_of_mulSupport_subset (s := hfin.toFinset)]
    · refine Finset.prod_congr rfl fun u hu ↦ ?_
      rw [divisor_eq_analyticOrderNatAt hf (hfin.mem_toFinset.1 hu).1, zpow_natCast]
    · intro u hu
      rw [Set.Finite.coe_toFinset]
      apply hsupp
      intro h0
      apply hu
      simp [h0]
  rw [hPeq] at heq
  have hPA : AnalyticOnNhd ℂ P (ball c ρ) := fun z _ ↦
    (Differentiable.fun_finsetProd fun u _ ↦ (differentiable_id.sub_const u).pow _).analyticAt z
  have hPg : AnalyticOnNhd ℂ (P • g) (ball c ρ) := hPA.smul hgA
  have hacc : AccPt c (𝓟 (ball c ρ)) := by
    rw [accPt_iff_frequently_nhdsNE]
    exact (eventually_nhdsWithin_of_eventually_nhds (isOpen_ball.mem_nhds hcU)).frequently
  have hev := (hf c hcU).meromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin
    (hPg c hcU).meromorphicAt hcU hacc heq
  have hEq := hf.eqOn_of_preconnected_of_frequently_eq hPg hpre hcU hev.frequently
  refine ⟨g, hgA, fun z hz ↦ hg0 ⟨z, hz⟩, fun z hz ↦ ?_⟩
  rw [hEq hz]
  rfl

/-! ### The Blaschke factors -/

/-- On the circle `‖z - c‖ = ρ`, `‖ρ² - conj (u - c) (z - c)‖ = ρ ‖z - u‖`. -/
theorem norm_sq_sub_conj_mul_eq {c z u : ℂ} {ρ : ℝ} (hz : ‖z - c‖ = ρ) :
    ‖(ρ : ℂ) ^ 2 - conj (u - c) * (z - c)‖ = ρ * ‖z - u‖ := by
  have hρ2 : (ρ : ℂ) ^ 2 = conj (z - c) * (z - c) := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
    push_cast
    ring
  rw [hρ2, ← sub_mul, ← map_sub, norm_mul, Complex.norm_conj, hz, mul_comm]
  congr 2
  ring

theorem norm_sq_sub_conj_mul_ge {c z u : ℂ} {ρ a b : ℝ} (hu : ‖u - c‖ ≤ a) (hz : ‖z - c‖ ≤ b)
    (ha : 0 ≤ a) : ρ ^ 2 - a * b ≤ ‖(ρ : ℂ) ^ 2 - conj (u - c) * (z - c)‖ := by
  have h1 : ‖conj (u - c) * (z - c)‖ ≤ a * b := by
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul hu hz (norm_nonneg _) ha
  have h2 : ‖(ρ : ℂ) ^ 2‖ = ρ ^ 2 := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have := norm_sub_norm_le ((ρ : ℂ) ^ 2) (conj (u - c) * (z - c))
  linarith

/-! ### Landau's lemma -/

/-- **Landau's lemma** (Montgomery–Vaughan, Lemma 6.3; `GoodHeights.md`, (L)). -/
theorem exists_norm_logDeriv_sub_sum_le {f : ℂ → ℂ} {c : ℂ} {r R R₀ M : ℝ} (hr : 0 < r)
    (hrR : r < R) (hRR₀ : R < R₀) (hf : AnalyticOnNhd ℂ f (closedBall c R₀)) (hfc : f c ≠ 0)
    (hM : 1 ≤ M) (hfM : ∀ z ∈ closedBall c R₀, ‖f z‖ ≤ M) :
    ∃ S : Finset ℂ, (∀ u ∈ S, f u = 0 ∧ ‖u - c‖ ≤ R) ∧
      ∀ z ∈ closedBall c r, f z ≠ 0 →
        ‖logDeriv f z - ∑ u ∈ S, (analyticOrderNatAt f u : ℂ) / (z - u)‖ ≤
          (8 * R₀ / (R - r) ^ 2 + 1 / (Real.log (2 * R₀ / (R + R₀)) * (R - r))) *
            (1 + Real.log (M / ‖f c‖)) := by
  classical
  set R₂ := (R + R₀) / 2 with hR₂
  have hRR₂ : R < R₂ := by rw [hR₂]; linarith
  have hR₂R₀ : R₂ < R₀ := by rw [hR₂]; linarith
  have hR0 : 0 < R := hr.trans hrR
  have hfc' : 0 < ‖f c‖ := norm_pos_iff.2 hfc
  have hcR₀ : c ∈ closedBall c R₀ := mem_closedBall_self (by linarith)
  have hMc : ‖f c‖ ≤ M := hfM c hcR₀
  set L := Real.log (M / ‖f c‖) with hLdef
  have hL : 0 ≤ L := Real.log_nonneg (by rw [le_div_iff₀ hfc']; linarith)
  have hpre : IsPreconnected (closedBall c R₀) := (convex_closedBall c R₀).isPreconnected
  have htop : ∀ u ∈ closedBall c R₀, analyticOrderAt f u ≠ ⊤ := fun u hu ↦
    analyticOrderAt_ne_top_of_ne_zero hf hpre hcR₀ hfc hu
  have hf₂ : AnalyticOnNhd ℂ f (closedBall c R₂) :=
    hf.mono (closedBall_subset_closedBall hR₂R₀.le)
  -- the zeros in `closedBall c R₂` are finitely many
  have hZfin : {u | u ∈ closedBall c R₂ ∧ f u = 0}.Finite := by
    refine ((divisor f (closedBall c R₂)).finiteSupport (isCompact_closedBall _ _)).subset ?_
    rintro u ⟨hu, hfu⟩
    have h1 := one_le_analyticOrderNatAt (hf₂ u hu) hfu
      (htop u (closedBall_subset_closedBall hR₂R₀.le hu))
    change divisor f (closedBall c R₂) u ≠ 0
    rw [divisor_eq_analyticOrderNatAt hf₂ hu]
    omega
  -- a radius `R₃ ∈ (R, R₂)` such that the zeros in `ball c R₃` are in `closedBall c R`
  obtain ⟨d, hRd, hdR₂, hd⟩ := exists_gap (hZfin.toFinset.image fun u ↦ ‖u - c‖) hRR₂
  set R₁ := (2 * R + d) / 3 with hR₁
  set R₃ := (R + 2 * d) / 3 with hR₃
  have hRR₁ : R < R₁ := by rw [hR₁]; linarith
  have hR₁R₃ : R₁ < R₃ := by rw [hR₁, hR₃]; linarith
  have hR₃R₂ : R₃ < R₂ := by rw [hR₃]; linarith
  have hR₁0 : 0 < R₁ := by linarith
  have hzeros : ∀ u ∈ ball c R₃, f u = 0 → ‖u - c‖ ≤ R := by
    intro u hu hfu
    rw [mem_ball, dist_eq_norm] at hu
    by_contra hlt
    rw [not_le] at hlt
    have hmem : u ∈ hZfin.toFinset := by
      rw [Set.Finite.mem_toFinset]
      exact ⟨by rw [mem_closedBall, dist_eq_norm]; linarith, hfu⟩
    have := hd _ (Finset.mem_image_of_mem _ hmem) hlt
    rw [hR₃] at hu
    linarith
  -- factor out the zeros in `U = ball c R₃`
  set U := ball c R₃ with hU
  have hfU : AnalyticOnNhd ℂ f U :=
    hf.mono (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)))
  have hUfin : {u | u ∈ U ∧ f u = 0}.Finite := hZfin.subset fun u ⟨hu, hfu⟩ ↦
    ⟨closedBall_subset_closedBall (by linarith) (ball_subset_closedBall hu), hfu⟩
  obtain ⟨g, hgA, hg0, hfg⟩ := exists_eq_prod_mul (by linarith) hfU hfc hUfin
  set S := hUfin.toFinset with hS
  set m : ℂ → ℕ := fun u ↦ analyticOrderNatAt f u with hm
  have hSmem : ∀ u ∈ S, u ∈ U ∧ f u = 0 := fun u hu ↦ hUfin.mem_toFinset.1 hu
  have hSR : ∀ u ∈ S, ‖u - c‖ ≤ R := fun u hu ↦ hzeros u (hSmem u hu).1 (hSmem u hu).2
  refine ⟨S, fun u hu ↦ ⟨(hSmem u hu).2, hSR u hu⟩, ?_⟩
  -- the Blaschke factors and `G`
  set B : ℂ → ℂ → ℂ := fun u z ↦ ((R₁ : ℂ) ^ 2 - conj (u - c) * (z - c)) / R₁ with hB
  set Q : ℂ → ℂ := fun z ↦ ∏ u ∈ S, B u z ^ m u with hQ
  set G : ℂ → ℂ := fun z ↦ g z * Q z with hG
  set P : ℂ → ℂ := fun z ↦ ∏ u ∈ S, (z - u) ^ m u with hP
  have hR₁ne : (R₁ : ℂ) ≠ 0 := ofReal_ne_zero.2 hR₁0.ne'
  have hBd : ∀ u, Differentiable ℂ (B u) := fun u ↦ by
    simp only [hB]
    fun_prop
  have hQd : Differentiable ℂ Q := Differentiable.fun_finsetProd fun u _ ↦ (hBd u).pow _
  have hGA : AnalyticOnNhd ℂ G U := hgA.mul fun z _ ↦ hQd.analyticAt z
  have hBne : ∀ u ∈ S, ∀ z, ‖z - c‖ ≤ R₁ → B u z ≠ 0 := by
    intro u hu z hz
    refine div_ne_zero ?_ hR₁ne
    intro h0
    have := norm_sq_sub_conj_mul_ge (ρ := R₁) (hSR u hu) hz hR0.le
    rw [h0, norm_zero] at this
    nlinarith
  have hQne : ∀ z, ‖z - c‖ ≤ R₁ → Q z ≠ 0 := fun z hz ↦
    Finset.prod_ne_zero_iff.2 fun u hu ↦ pow_ne_zero _ (hBne u hu z hz)
  have hR₁U : ∀ z, ‖z - c‖ ≤ R₁ → z ∈ U := fun z hz ↦ by
    rw [hU, mem_ball, dist_eq_norm]; linarith
  have hGne : ∀ z, ‖z - c‖ ≤ R₁ → G z ≠ 0 := fun z hz ↦
    mul_ne_zero (hg0 z (hR₁U z hz)) (hQne z hz)
  -- `‖G‖ = ‖f‖` on the circle of radius `R₁`
  have hGsphere : ∀ z, ‖z - c‖ = R₁ → ‖G z‖ = ‖f z‖ := by
    intro z hz
    have hQP : ‖Q z‖ = ‖P z‖ := by
      simp only [hQ, hP, norm_prod, norm_pow]
      refine Finset.prod_congr rfl fun u _ ↦ ?_
      rw [hB, norm_div, norm_sq_sub_conj_mul_eq hz, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hR₁0, mul_div_cancel_left₀ _ hR₁0.ne']
    rw [hfg z (hR₁U z hz.le), norm_mul, norm_mul, hQP, mul_comm]
  -- maximum modulus
  have hGM : ∀ z, ‖z - c‖ ≤ R₁ → ‖G z‖ ≤ M := by
    intro z hz
    have hcl : closure (ball c R₁) = closedBall c R₁ := closure_ball c hR₁0.ne'
    refine Complex.norm_le_of_forall_mem_frontier_norm_le (U := ball c R₁) isBounded_ball ?_ ?_ ?_
    · refine DifferentiableOn.diffContOnCl ?_
      rw [hcl]
      intro w hw
      rw [mem_closedBall, dist_eq_norm] at hw
      exact (hGA w (hR₁U w hw)).differentiableAt.differentiableWithinAt
    · intro w hw
      rw [frontier_ball c hR₁0.ne', mem_sphere, dist_eq_norm] at hw
      rw [hGsphere w hw]
      exact hfM w (by rw [mem_closedBall, dist_eq_norm]; linarith)
    · rw [hcl, mem_closedBall, dist_eq_norm]
      exact hz
  -- `‖G c‖ ≥ ‖f c‖`
  have hGc : ‖f c‖ ≤ ‖G c‖ := by
    have hc0 : ‖c - c‖ ≤ R₁ := by simp [hR₁0.le]
    rw [hfg c (hR₁U c hc0), norm_mul, norm_mul, mul_comm]
    gcongr
    simp only [hQ, norm_prod, norm_pow]
    refine Finset.prod_le_prod (fun u _ ↦ by positivity) fun u hu ↦ ?_
    gcongr
    have hBc : ‖B u c‖ = R₁ := by
      simp only [hB, sub_self, mul_zero, sub_zero, norm_div, norm_pow, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hR₁0]
      field_simp
    rw [hBc, norm_sub_rev]
    linarith [hSR u hu]
  -- a primitive of `G'/G` on `ball c R₁`
  have hφ : DifferentiableOn ℂ (logDeriv G) (ball c R₁) := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz
    have hzU := hR₁U z hz.le
    exact (((hGA z hzU).deriv.differentiableAt).div (hGA z hzU).differentiableAt
      (hGne z hz.le)).differentiableWithinAt
  obtain ⟨h, hh0, hhd⟩ := (hφ.isExactOn_ball).with_val_at c 0
  -- `G = G(c) e^h`
  have hconst : ∀ z ∈ ball c R₁, G z * Complex.exp (-h z) = G c := by
    have hk : ∀ z ∈ ball c R₁, HasDerivAt (fun z ↦ G z * Complex.exp (-h z)) 0 z := by
      intro z hz
      have hz' : ‖z - c‖ ≤ R₁ := by rw [mem_ball, dist_eq_norm] at hz; exact hz.le
      have hG' : HasDerivAt G (deriv G z) z := (hGA z (hR₁U z hz')).differentiableAt.hasDerivAt
      have hE : HasDerivAt (fun z ↦ Complex.exp (-h z)) (Complex.exp (-h z) * -logDeriv G z) z :=
        (hhd z hz).neg.cexp
      convert hG'.mul hE using 1
      rw [logDeriv_apply]
      field_simp [hGne z hz']
      ring
    intro z hz
    have := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball c R₁).isPreconnected
      (fun w hw ↦ (hk w hw).differentiableAt.differentiableWithinAt)
      (fun w hw ↦ by simpa using (hk w hw).deriv) hz (mem_ball_self hR₁0)
    rw [this, hh0, neg_zero, Complex.exp_zero, mul_one]
  have hre : ∀ z ∈ ball c R₁, (h z).re ≤ L := by
    intro z hz
    have hz' : ‖z - c‖ ≤ R₁ := by rw [mem_ball, dist_eq_norm] at hz; exact hz.le
    have hGz : G z = G c * Complex.exp (h z) := by
      rw [← hconst z hz, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
    have hGc0 : 0 < ‖G c‖ := hfc'.trans_le hGc
    have hnorm : ‖G z‖ = ‖G c‖ * Real.exp (h z).re := by rw [hGz, norm_mul, Complex.norm_exp]
    have hexp : Real.exp (h z).re ≤ M / ‖f c‖ := by
      have h1 : Real.exp (h z).re = ‖G z‖ / ‖G c‖ := by rw [hnorm]; field_simp
      rw [h1, div_le_div_iff₀ hGc0 hfc']
      calc ‖G z‖ * ‖f c‖ ≤ M * ‖f c‖ := by gcongr; exact hGM z hz'
        _ ≤ M * ‖G c‖ := by gcongr
    calc (h z).re = Real.log (Real.exp (h z).re) := (Real.log_exp _).symm
      _ ≤ L := Real.log_le_log (Real.exp_pos _) hexp
  -- Borel–Carathéodory
  have hBC : ∀ w ∈ ball (0 : ℂ) R₁, ‖h (w + c)‖ ≤ 2 * (L + 1) * ‖w‖ / (R₁ - ‖w‖) := by
    intro w hw
    have hmem : ∀ w ∈ ball (0 : ℂ) R₁, w + c ∈ ball c R₁ := fun w hw ↦ by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_right]
      rwa [mem_ball, dist_zero_right] at hw
    refine Complex.borelCaratheodory_zero (f := fun w ↦ h (w + c)) (by linarith) ?_ ?_ hR₁0 hw
      (by simp [hh0])
    · intro w hw
      exact ((hhd _ (hmem w hw)).differentiableAt.comp w
        (differentiableAt_id.add_const c)).differentiableWithinAt
    · intro w hw
      have := hre _ (hmem w hw)
      simp only [mem_setOf_eq]
      linarith
  -- Cauchy's estimate for `h'` on `closedBall c r`
  have hderiv : ∀ z ∈ closedBall c r, ‖deriv h z‖ ≤ 4 * (L + 1) * (R₁ + r) / (R₁ - r) ^ 2 := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    set ρ := (R₁ - r) / 2 with hρ
    have hρ0 : 0 < ρ := by rw [hρ]; linarith
    have hsub : closedBall z ρ ⊆ ball c R₁ := by
      intro y hy
      rw [mem_closedBall, dist_eq_norm] at hy
      rw [mem_ball, dist_eq_norm]
      calc ‖y - c‖ = ‖(y - z) + (z - c)‖ := by congr 1; ring
        _ ≤ ‖y - z‖ + ‖z - c‖ := norm_add_le _ _
        _ < R₁ := by rw [hρ] at hy; linarith
    have hdc : DiffContOnCl ℂ h (ball z ρ) :=
      DifferentiableOn.diffContOnCl_ball
        (fun w hw ↦ (hhd w hw).differentiableAt.differentiableWithinAt) hsub
    have hbound : ∀ y ∈ sphere z ρ, ‖h y‖ ≤ 2 * (L + 1) * (R₁ + r) / (R₁ - r) := by
      intro y hy
      rw [mem_sphere, dist_eq_norm] at hy
      have hyc : ‖y - c‖ ≤ (R₁ + r) / 2 := by
        calc ‖y - c‖ = ‖(y - z) + (z - c)‖ := by congr 1; ring
          _ ≤ ‖y - z‖ + ‖z - c‖ := norm_add_le _ _
          _ ≤ (R₁ + r) / 2 := by rw [hy, hρ]; linarith
      have h1 := hBC (y - c) (by rw [mem_ball, dist_zero_right]; linarith)
      rw [sub_add_cancel] at h1
      calc ‖h y‖ ≤ 2 * (L + 1) * ‖y - c‖ / (R₁ - ‖y - c‖) := h1
        _ ≤ 2 * (L + 1) * ((R₁ + r) / 2) / (R₁ - (R₁ + r) / 2) := by
            gcongr
            all_goals linarith
        _ = 2 * (L + 1) * (R₁ + r) / (R₁ - r) := by
            field_simp
            ring
    have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ0 hdc hbound
    calc ‖deriv h z‖ ≤ 2 * (L + 1) * (R₁ + r) / (R₁ - r) / ρ := this
      _ = 4 * (L + 1) * (R₁ + r) / (R₁ - r) ^ 2 := by
          rw [hρ]
          field_simp
          ring
  -- Jensen's inequality bounds the number of zeros
  have hK : (∑ u ∈ S, (m u : ℝ)) ≤ L / Real.log (R₀ / R₂) := by
    have hR₀abs : |R₀| = R₀ := abs_of_pos (by linarith)
    have hR₂abs : |R₂| = R₂ := abs_of_pos (by linarith)
    have hJ := AnalyticOnNhd.sum_divisor_le (c := c) (r := R₂) (R := R₀) (M := M)
      (by rw [hR₂abs]; linarith) (by rw [hR₂abs, hR₀abs]; exact hR₂R₀) hM
      (by rw [hR₀abs]; exact hf) hfc
      (fun z hz ↦ hfM z (by rw [hR₀abs] at hz; exact sphere_subset_closedBall hz))
    rw [hR₂abs] at hJ
    have hS₂ : ∀ u ∈ S, u ∈ closedBall c R₂ := fun u hu ↦
      closedBall_subset_closedBall hR₃R₂.le (ball_subset_closedBall (hSmem u hu).1)
    have hsum : (∑ u ∈ S, (m u : ℝ)) = ((∑ u ∈ S, divisor f (closedBall c R₂) u : ℤ) : ℝ) := by
      push_cast
      refine Finset.sum_congr rfl fun u hu ↦ ?_
      rw [divisor_eq_analyticOrderNatAt hf₂ (hS₂ u hu)]
      simp [hm]
    have hle : (∑ u ∈ S, divisor f (closedBall c R₂) u) ≤ ∑ᶠ u, divisor f (closedBall c R₂) u :=
      sum_le_finsum_of_nonneg (fun u ↦ by simpa using hf₂.divisor_nonneg u)
        ((divisor f (closedBall c R₂)).finiteSupport (isCompact_closedBall _ _)) S
    calc (∑ u ∈ S, (m u : ℝ)) = ((∑ u ∈ S, divisor f (closedBall c R₂) u : ℤ) : ℝ) := hsum
      _ ≤ ((∑ᶠ u, divisor f (closedBall c R₂) u : ℤ) : ℝ) := by exact_mod_cast hle
      _ ≤ L / Real.log (R₀ / R₂) := hJ
  -- the logarithmic derivatives at a point `z` of `closedBall c r`
  intro z hz hfz
  have hzc : ‖z - c‖ ≤ r := by rwa [mem_closedBall, dist_eq_norm] at hz
  have hzR₁ : ‖z - c‖ ≤ R₁ := by linarith
  have hzU := hR₁U z hzR₁
  have hzB : z ∈ ball c R₁ := by rw [mem_ball, dist_eq_norm]; linarith
  have hfeq : f =ᶠ[𝓝 z] fun w ↦ P w * g w := by
    filter_upwards [isOpen_ball.mem_nhds hzU] with w hw
    exact hfg w hw
  have hgz : g z ≠ 0 := hg0 z hzU
  have hzu : ∀ u ∈ S, z - u ≠ 0 := fun u hu h0 ↦
    hfz (by rw [sub_eq_zero.1 h0]; exact (hSmem u hu).2)
  have hPz : P z ≠ 0 := Finset.prod_ne_zero_iff.2 fun u hu ↦ pow_ne_zero _ (hzu u hu)
  have hPd : Differentiable ℂ P :=
    Differentiable.fun_finsetProd fun u _ ↦ (differentiable_id.sub_const u).pow _
  have hlogP : logDeriv P z = ∑ u ∈ S, (m u : ℂ) / (z - u) := by
    have h1 : logDeriv P z = ∑ u ∈ S, logDeriv (fun w ↦ (w - u) ^ m u) z :=
      logDeriv_prod (f := fun u w ↦ (w - u) ^ m u) (fun u hu ↦ pow_ne_zero _ (hzu u hu))
        (fun u _ ↦ by fun_prop)
    rw [h1]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    have h2 : logDeriv (fun w ↦ (w - u) ^ m u) z = (m u : ℂ) * logDeriv (fun w ↦ w - u) z :=
      logDeriv_fun_pow (f := fun w ↦ w - u) (by fun_prop) (m u)
    rw [h2, logDeriv_apply, deriv_sub_const, deriv_id'']
    ring
  have hlogf : logDeriv f z = logDeriv P z + logDeriv g z := by
    rw [logDeriv_apply, logDeriv_apply, logDeriv_apply, hfeq.deriv_eq, hfeq.eq_of_nhds]
    have := logDeriv_mul (f := P) (g := g) z hPz hgz (hPd z) (hgA z hzU).differentiableAt
    rwa [logDeriv_apply, logDeriv_apply, logDeriv_apply] at this
  have hlogB : ∀ u ∈ S,
      logDeriv (B u) z = -conj (u - c) / ((R₁ : ℂ) ^ 2 - conj (u - c) * (z - c)) := by
    intro u hu
    have hd : HasDerivAt (B u) (-conj (u - c) / R₁) z := by
      have := (((hasDerivAt_id z).sub_const c).const_mul (conj (u - c))).const_sub
        ((R₁ : ℂ) ^ 2) |>.div_const (R₁ : ℂ)
      simpa [hB] using this
    have hden : (R₁ : ℂ) ^ 2 - conj (u - c) * (z - c) ≠ 0 := fun h0 ↦
      hBne u hu z hzR₁ (by simp only [hB]; rw [h0, zero_div])
    rw [logDeriv_apply, hd.deriv]
    simp only [hB]
    field_simp
  have hlogQ : logDeriv Q z = ∑ u ∈ S, (m u : ℂ) * logDeriv (B u) z := by
    have h1 : logDeriv Q z = ∑ u ∈ S, logDeriv (fun w ↦ B u w ^ m u) z :=
      logDeriv_prod (f := fun u w ↦ B u w ^ m u) (fun u hu ↦ pow_ne_zero _ (hBne u hu z hzR₁))
        (fun u _ ↦ ((hBd u).pow _) z)
    rw [h1]
    exact Finset.sum_congr rfl fun u _ ↦ logDeriv_fun_pow (f := B u) ((hBd u) z) (m u)
  have hlogG : logDeriv G z = logDeriv g z + logDeriv Q z :=
    logDeriv_mul (f := g) (g := Q) z hgz (hQne z hzR₁) (hgA z hzU).differentiableAt (hQd z)
  have hhz : deriv h z = logDeriv G z := (hhd z hzB).deriv
  have hkey : logDeriv f z - ∑ u ∈ S, (m u : ℂ) / (z - u) =
      deriv h z - ∑ u ∈ S, (m u : ℂ) * logDeriv (B u) z := by
    rw [hlogf, hlogP, hhz, hlogG, hlogQ]
    ring
  have hBbound : ∀ u ∈ S, ‖logDeriv (B u) z‖ ≤ 1 / (R₁ - r) := by
    intro u hu
    rw [hlogB u hu, norm_div, norm_neg, Complex.norm_conj]
    have hge := norm_sq_sub_conj_mul_ge (ρ := R₁) (le_refl ‖u - c‖) hzc (norm_nonneg _)
    have hpos : 0 < R₁ ^ 2 - ‖u - c‖ * r := by nlinarith [hSR u hu]
    rw [div_le_div_iff₀ (hpos.trans_le hge) (by linarith)]
    nlinarith [hSR u hu]
  have hsumB : ‖∑ u ∈ S, (m u : ℂ) * logDeriv (B u) z‖ ≤ (∑ u ∈ S, (m u : ℝ)) / (R₁ - r) := by
    calc ‖∑ u ∈ S, (m u : ℂ) * logDeriv (B u) z‖ ≤ ∑ u ∈ S, ‖(m u : ℂ) * logDeriv (B u) z‖ :=
          norm_sum_le _ _
      _ ≤ ∑ u ∈ S, (m u : ℝ) * (1 / (R₁ - r)) := by
          refine Finset.sum_le_sum fun u hu ↦ ?_
          rw [norm_mul, Complex.norm_natCast]
          gcongr
          exact hBbound u hu
      _ = (∑ u ∈ S, (m u : ℝ)) / (R₁ - r) := by rw [← Finset.sum_mul]; ring
  have hlogR : Real.log (R₀ / R₂) = Real.log (2 * R₀ / (R + R₀)) := by
    congr 1
    rw [hR₂]
    field_simp
  have hlam : 0 < Real.log (R₀ / R₂) := Real.log_pos (by rw [one_lt_div (by linarith)]; exact hR₂R₀)
  have hRr : 0 < R - r := by linarith
  have hL1 : 0 ≤ L + 1 := by linarith
  have hK0 : 0 ≤ ∑ u ∈ S, (m u : ℝ) := Finset.sum_nonneg fun u _ ↦ Nat.cast_nonneg _
  have ha : 4 * (L + 1) * (R₁ + r) / (R₁ - r) ^ 2 ≤ 8 * R₀ / (R - r) ^ 2 * (1 + L) := by
    calc 4 * (L + 1) * (R₁ + r) / (R₁ - r) ^ 2 ≤ 4 * (L + 1) * (2 * R₀) / (R - r) ^ 2 :=
          div_le_div₀ (mul_nonneg (mul_nonneg (by norm_num) hL1) (by linarith))
            (mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (by norm_num) hL1))
            (pow_pos hRr 2) (pow_le_pow_left₀ hRr.le (by linarith) 2)
      _ = 8 * R₀ / (R - r) ^ 2 * (1 + L) := by ring
  have hb : (∑ u ∈ S, (m u : ℝ)) / (R₁ - r) ≤
      1 / (Real.log (R₀ / R₂) * (R - r)) * (1 + L) := by
    calc (∑ u ∈ S, (m u : ℝ)) / (R₁ - r) ≤ (L / Real.log (R₀ / R₂)) / (R - r) :=
          div_le_div₀ (div_nonneg hL hlam.le) hK hRr (by linarith)
      _ = 1 / (Real.log (R₀ / R₂) * (R - r)) * L := by
          field_simp
      _ ≤ 1 / (Real.log (R₀ / R₂) * (R - r)) * (1 + L) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  rw [hkey]
  calc ‖deriv h z - ∑ u ∈ S, (m u : ℂ) * logDeriv (B u) z‖
      ≤ ‖deriv h z‖ + ‖∑ u ∈ S, (m u : ℂ) * logDeriv (B u) z‖ := norm_sub_le _ _
    _ ≤ 4 * (L + 1) * (R₁ + r) / (R₁ - r) ^ 2 + (∑ u ∈ S, (m u : ℝ)) / (R₁ - r) :=
        add_le_add (hderiv z hz) hsumB
    _ ≤ 8 * R₀ / (R - r) ^ 2 * (1 + L) + 1 / (Real.log (R₀ / R₂) * (R - r)) * (1 + L) :=
        add_le_add ha hb
    _ = (8 * R₀ / (R - r) ^ 2 + 1 / (Real.log (2 * R₀ / (R + R₀)) * (R - r))) * (1 + L) := by
        rw [hlogR]
        ring

end WeilExplicitFormula
