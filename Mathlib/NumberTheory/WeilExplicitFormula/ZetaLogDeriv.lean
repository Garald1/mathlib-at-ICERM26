/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Terence Tao, Harald Helfgott
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Calculus.LogDeriv

/-! # The functional equation of `ζ'/ζ`

`ζ'/ζ(s) = -ζ'/ζ(1 - s) + log 2π - ψ(s) + (π/2) tan(πs/2)`, obtained by taking logarithmic
derivatives in Mathlib's `riemannZeta_one_sub`, `ζ(1 - s) = 2 (2π)^{-s} Γ(s) cos(πs/2) ζ(s)`.

`LogDerivFunctionalEquation` is the statement of IEANTN's
`ZetaLogDeriv.v1.logDeriv_functional_equation`, copied verbatim, and
`logDeriv_functional_equation` proves it, so that the library's proof of Montgomery–Vaughan
Lemma 12.2 does not need it as a hypothesis.

The proof is T. Tao's IEANTN solution (`Solutions/ZetaLogDeriv.v1/Solution.lean`), adapted to this
version of Mathlib. The only step with content is to find a neighbourhood of `s` on which the
functional equation holds: `{z | 1 < Re z} ∪ (ℤ)ᶜ`, which contains `s` because the hypotheses
force an integer `s` to be `≥ 2`.

## AI usage

This file was adapted by Claude (Anthropic) in November 2026 from T. Tao's IEANTN solution. It
compiles, but has not been reviewed by a human.
-/

@[expose] public section

open scoped Real
open Complex Filter Topology

noncomputable section

namespace WeilExplicitFormula

/-- The statement of IEANTN's `ZetaLogDeriv.v1.logDeriv_functional_equation`, verbatim. -/
def LogDerivFunctionalEquation : Prop :=
  ∀ s : ℂ, (∀ n : ℕ, s ≠ -n) → s ≠ 1 →
    riemannZeta s ≠ 0 → Complex.cos (Real.pi * s / 2) ≠ 0 →
      deriv riemannZeta s / riemannZeta s
        = -(deriv riemannZeta (1 - s) / riemannZeta (1 - s))
          + Complex.log (2 * Real.pi) - Complex.digamma s
          + (Real.pi / 2) * Complex.tan (Real.pi * s / 2)

/-- The functional equation of `ζ'/ζ`, in `logDeriv` form. -/
theorem logDeriv_riemannZeta_one_sub {s : ℂ} (hsn : ∀ n : ℕ, s ≠ -n) (hs1 : s ≠ 1)
    (hz : riemannZeta s ≠ 0) (hcos : Complex.cos (π * s / 2) ≠ 0) :
    logDeriv riemannZeta s =
      -logDeriv riemannZeta (1 - s) + Complex.log (2 * π) - digamma s
        + π / 2 * Complex.tan (π * s / 2) := by
  have hs0 : s ≠ 0 := by simpa using hsn 0
  have hΓ : Gamma s ≠ 0 := Gamma_ne_zero hsn
  have h2π : (2 * (π : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hcpow : (2 * (π : ℂ)) ^ (-s) ≠ 0 := by simp [Complex.cpow_eq_zero_iff, h2π]
  have hUopen : IsOpen ({z : ℂ | 1 < z.re} ∪ (Set.range ((↑) : ℤ → ℂ))ᶜ) :=
    (isOpen_lt continuous_const Complex.continuous_re).union
      Complex.isClosed_range_intCast.isOpen_compl
  have hsU : s ∈ ({z : ℂ | 1 < z.re} ∪ (Set.range ((↑) : ℤ → ℂ))ᶜ) := by
    by_cases h : s ∈ Set.range ((↑) : ℤ → ℂ)
    · obtain ⟨k, rfl⟩ := h
      refine Or.inl ?_
      have hk0 : 0 < k := by
        by_contra hk
        rw [not_lt] at hk
        obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = -(m : ℤ) := ⟨(-k).toNat, by omega⟩
        exact hsn m (by push_cast; ring)
      have hk1 : k ≠ 1 := fun h ↦ hs1 (by exact_mod_cast h)
      have hk2 : (1 : ℤ) < k := by omega
      simpa using (by exact_mod_cast hk2 : (1 : ℝ) < (k : ℝ))
    · exact Or.inr h
  have hEq : (fun z ↦ riemannZeta (1 - z)) =ᶠ[𝓝 s]
      (fun z ↦ 2 * (2 * π) ^ (-z) * Gamma z * Complex.cos (π * z / 2) * riemannZeta z) := by
    filter_upwards [hUopen.mem_nhds hsU] with z hzU
    rcases hzU with hlt | hnot
    · simp only [Set.mem_setOf_eq] at hlt
      refine riemannZeta_one_sub (fun n hn ↦ ?_) (fun hn ↦ ?_)
      · rw [hn] at hlt
        simp at hlt
        linarith
      · rw [hn] at hlt
        simp at hlt
    · simp only [Set.mem_compl_iff, Set.mem_range, not_exists] at hnot
      exact riemannZeta_one_sub (fun n h ↦ hnot (-n) (by simp [h]))
        (fun h ↦ hnot 1 (by simp [h]))
  have hlog : logDeriv (fun z ↦ riemannZeta (1 - z)) s =
      logDeriv (fun z ↦ 2 * (2 * π) ^ (-z) * Gamma z * Complex.cos (π * z / 2) * riemannZeta z)
        s := by
    rw [logDeriv_apply, logDeriv_apply, hEq.deriv_eq, hEq.eq_of_nhds]
  have hLHS : logDeriv (fun z ↦ riemannZeta (1 - z)) s = -logDeriv riemannZeta (1 - s) := by
    rw [show (fun z ↦ riemannZeta (1 - z)) = riemannZeta ∘ (fun z ↦ 1 - z) from rfl,
      logDeriv_comp (differentiableAt_riemannZeta (by simpa [sub_eq_iff_eq_add] using hs0))
        (by fun_prop), ((hasDerivAt_id' s).const_sub 1).deriv]
    ring
  have hcpowLog : logDeriv (fun z ↦ (2 * (π : ℂ)) ^ (-z)) s = -Complex.log (2 * π) := by
    rw [logDeriv_apply, ((hasDerivAt_neg' s).const_cpow (Or.inl h2π)).deriv]
    field_simp
  have hcosLog : logDeriv (fun z ↦ Complex.cos (π * z / 2)) s
      = -(π / 2 * Complex.tan (π * s / 2)) := by
    have hinner : HasDerivAt (fun z : ℂ ↦ (π : ℂ) * z / 2) (π / 2) s := by
      simpa using ((hasDerivAt_id s).const_mul (π : ℂ)).div_const 2
    rw [logDeriv_apply, hinner.ccos.deriv, Complex.tan_eq_sin_div_cos]
    field_simp
  rw [hLHS] at hlog
  have hdΓ : DifferentiableAt ℂ Gamma s := differentiableAt_Gamma s hsn
  have hdζ : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs1
  have hd2π : DifferentiableAt ℂ (fun z ↦ (2 * (π : ℂ)) ^ (-z)) s :=
    ((hasDerivAt_neg' s).const_cpow (Or.inl h2π)).differentiableAt
  have hdcos : DifferentiableAt ℂ (fun z ↦ Complex.cos (π * z / 2)) s := by fun_prop
  rw [logDeriv_mul (f := fun z ↦ 2 * (2 * (π : ℂ)) ^ (-z) * Gamma z * Complex.cos (π * z / 2))
      (g := riemannZeta) s (by simp [hcpow, hΓ, hcos]) hz
      (((differentiableAt_const _).mul hd2π).mul hdΓ |>.mul hdcos) hdζ,
    logDeriv_mul (f := fun z ↦ 2 * (2 * (π : ℂ)) ^ (-z) * Gamma z)
      (g := fun z ↦ Complex.cos (π * z / 2)) s (by simp [hcpow, hΓ]) hcos
      (((differentiableAt_const _).mul hd2π).mul hdΓ) hdcos,
    logDeriv_mul (f := fun z ↦ 2 * (2 * (π : ℂ)) ^ (-z)) (g := Gamma) s (by simp [hcpow]) hΓ
      ((differentiableAt_const _).mul hd2π) hdΓ,
    logDeriv_mul (f := fun _ ↦ (2 : ℂ)) (g := fun z ↦ (2 * (π : ℂ)) ^ (-z)) s two_ne_zero hcpow
      (differentiableAt_const _) hd2π] at hlog
  rw [logDeriv_const, hcpowLog, show logDeriv Gamma s = digamma s from rfl, hcosLog] at hlog
  simp only [Pi.zero_apply] at hlog
  linear_combination -hlog

/-- **The functional equation of `ζ'/ζ`**: IEANTN's `ZetaLogDeriv.v1.logDeriv_functional_equation`,
which spells `logDeriv` out as `deriv f / f`. -/
theorem logDeriv_functional_equation : LogDerivFunctionalEquation := by
  intro s hsn hs1 hz hcos
  simpa only [logDeriv_apply] using logDeriv_riemannZeta_one_sub hsn hs1 hz hcos

end WeilExplicitFormula
