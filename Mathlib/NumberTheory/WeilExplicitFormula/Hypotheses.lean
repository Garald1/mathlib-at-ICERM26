/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Harald Helfgott
-/
module

public import Mathlib.Analysis.BoxIntegral.Stieltjes.Basic
public import Mathlib.Analysis.BoxIntegral.Stieltjes.IntegrationByParts
public import Mathlib.Analysis.BoxIntegral.Stieltjes.VariationBounds
public import Mathlib.NumberTheory.WeilExplicitFormula.ExplicitFormula

/-! # The hypotheses (12.20)–(12.21) of Montgomery–Vaughan, Theorem 12.13

Montgomery–Vaughan state Theorem 12.13 for measurable `F` with
`∫ e^{a|x|} |F(x)| dx < ∞` (12.20) and `∫ e^{a|x|} |dF(x)| < ∞` (12.21), `a = (1/2 + δ₀) 2π`.
The library (`IsTestFunction`, and `IEANTN`'s node `IsTestFunctionNode`) asks instead that
`G(x) = e^{a|x|} F(x)` be integrable and of bounded variation on `ℝ`. This file states (12.20)
and (12.21) (`MV_12_20`, `MV_12_21`), the latter with the library's Riemann–Stieltjes integral of
`e^{a|x|}` against the variation `x ↦ Var_{[0, x]} F` of `F` (`variationOnFromTo F univ 0`), and
proves that the two forms are equivalent (`mv_12_20_and_12_21_iff`, `isTestFunctionNode_iff`).

* `⇒` is [MV]'s remark after the theorem (`∫|d(fg)| ≤ ∫|f||dg| + ∫|g||df|`);
* `⇐` uses `dF = e^{-a|x|} dG + G d(e^{-a|x|})`, so `∫ e^{a|x|}|dF| ≤ ∫|dG| + a ∫|G|`
  (`blueprint/WeilExplicitFormula.md`, "Form of the hypotheses").

Both directions are proved with a uniform partition of `[-X, X]` into pieces `J` of length
`h ≤ 1`, on which `e^{a|x|}` varies by a factor at most `e^{ah}`: on each piece the
Riemann–Stieltjes integral of `e^{a|x|}` is between `e^{a(M_J - h)} Var_J F` and
`e^{a M_J} Var_J F` (`M_J = max_J |x|`), and the variation of a product is bounded by
`eVariationOn_smul_le`.

## AI usage

This file was written by Claude (Anthropic) in November 2026. It compiles, but has not been
reviewed by a human.
-/

@[expose] public section

open Real Complex Filter Topology Set MeasureTheory BoxIntegral ContinuousLinearMap

noncomputable section

namespace WeilExplicitFormula

/-! ### Riemann–Stieltjes integrals against nondecreasing integrators -/

section RS

variable {f V : ℝ → ℝ} {u v m M : ℝ}

theorem stieltjesIntegrable_of_monotoneOn (huv : u ≤ v) (hf : ContinuousOn f (Icc u v))
    (hV : MonotoneOn V (Icc u v)) : StieltjesIntegrable u v (mul ℝ ℝ) f V :=
  StieltjesIntegrable.of_continuousOn_of_boundedVariationOn (by rwa [uIcc_of_le huv])
    (by rw [uIcc_of_le huv]; exact hV.boundedVariationOn)

/-- For `V` nondecreasing on `[u, v]` and `f` continuous with `0 ≤ m ≤ f ≤ M` there,
`m (V v - V u) ≤ ∫_u^v f dV ≤ M (V v - V u)`. -/
theorem stieltjesIntegral_mem_Icc_of_monotoneOn (huv : u ≤ v) (hf : ContinuousOn f (Icc u v))
    (hV : MonotoneOn V (Icc u v)) (hm : 0 ≤ m) (hfm : ∀ x ∈ Icc u v, m ≤ f x)
    (hfM : ∀ x ∈ Icc u v, f x ≤ M) :
    m * (V v - V u) ≤ ∫⟨mul ℝ ℝ⟩ x in u..v, f x ∂V ∧
      ∫⟨mul ℝ ℝ⟩ x in u..v, f x ∂V ≤ M * (V v - V u) := by
  have hu : u ∈ Icc u v := left_mem_Icc.2 huv
  have hv : v ∈ Icc u v := right_mem_Icc.2 huv
  have hVbv : BoundedVariationOn V (uIcc u v) := by
    rw [uIcc_of_le huv]; exact hV.boundedVariationOn
  have hΔ : 0 ≤ V v - V u := sub_nonneg.2 (hV hu hv huv)
  have hvar : (eVariationOn V (Icc u v)).toReal = V v - V u := by
    have := hV.eVariationOn_eq huv hu hv
    rw [inter_self] at this
    rw [this, ENNReal.toReal_ofReal hΔ]
  have hint := (stieltjesIntegrable_of_monotoneOn huv hf hV).hasStieltjesIntegral
  have hc : HasStieltjesIntegral u v (mul ℝ ℝ) (fun _ ↦ M) V (M * V v - M * V u) := by
    simpa using HasStieltjesIntegral.of_const (B := mul ℝ ℝ) (c := M) (a := u) (b := v) (g := V)
  constructor
  · have h1 := stieltjesIntegral_le_bound_mul huv (opNorm_mul_le ℝ ℝ) hVbv (hc.sub_left hint)
      (L' := M - m) (fun x hx ↦ by
        simp only [Pi.sub_apply, Real.norm_eq_abs]
        rw [abs_of_nonneg (by linarith [hfM x hx])]
        linarith [hfm x hx])
    rw [hvar, one_mul, Real.norm_eq_abs] at h1
    linarith [(abs_le.1 h1).2]
  · have h1 := stieltjesIntegral_le_bound_mul huv (opNorm_mul_le ℝ ℝ) hVbv hint (L' := M)
      (fun x hx ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (hm.trans (hfm x hx))]
        exact hfM x hx)
    rw [hvar, one_mul, Real.norm_eq_abs] at h1
    exact (le_abs_self _).trans h1

/-- The integral over `[x 0, x n]` is the sum of the integrals over the `[x k, x (k + 1)]`. -/
theorem stieltjesIntegral_eq_sum {x : ℕ → ℝ} (hx : Monotone x) (n : ℕ)
    (hf : ContinuousOn f (Icc (x 0) (x n))) (hV : MonotoneOn V (Icc (x 0) (x n))) :
    ∫⟨mul ℝ ℝ⟩ y in x 0..x n, f y ∂V =
      ∑ k ∈ Finset.range n, ∫⟨mul ℝ ℝ⟩ y in x k..x (k + 1), f y ∂V := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h0n : x 0 ≤ x n := hx (Nat.zero_le n)
    have hn1 : x n ≤ x (n + 1) := hx (Nat.le_succ n)
    have hsub : Icc (x 0) (x n) ⊆ Icc (x 0) (x (n + 1)) := Icc_subset_Icc le_rfl hn1
    have hsub' : Icc (x n) (x (n + 1)) ⊆ Icc (x 0) (x (n + 1)) := Icc_subset_Icc h0n le_rfl
    rw [Finset.sum_range_succ, ← ih (hf.mono hsub) (hV.mono hsub)]
    exact stieltjesIntegral.add_adjacent
      (stieltjesIntegrable_of_monotoneOn (h0n.trans hn1) hf hV)
      (stieltjesIntegrable_of_monotoneOn h0n (hf.mono hsub) (hV.mono hsub))
      (stieltjesIntegrable_of_monotoneOn hn1 (hf.mono hsub') (hV.mono hsub'))

end RS

/-- The variation over `[x 0, x n]` is the sum of the variations over the `[x k, x (k + 1)]`. -/
theorem eVariationOn_Icc_eq_sum {E : Type*} [PseudoEMetricSpace E] (g : ℝ → E) {x : ℕ → ℝ}
    (hx : Monotone x) (n : ℕ) :
    eVariationOn g (Icc (x 0) (x n)) =
      ∑ k ∈ Finset.range n, eVariationOn g (Icc (x k) (x (k + 1))) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    have := eVariationOn.Icc_add_Icc g (s := univ) (hx (Nat.zero_le n)) (hx (Nat.le_succ n))
      (mem_univ _)
    simpa only [univ_inter] using this.symm

/-! ### Bounds on one piece of a partition -/

section Piece

theorem abs_le_max_abs {u v x : ℝ} (hx : x ∈ Icc u v) : |x| ≤ max |u| |v| := by
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h]; exact (hx.2.trans (le_abs_self v)).trans (le_max_right _ _)
  · rw [abs_of_nonpos h]; exact ((neg_le_neg hx.1).trans (neg_le_abs u)).trans (le_max_left _ _)

theorem max_abs_le_abs_add {u v x : ℝ} (hx : x ∈ Icc u v) : max |u| |v| ≤ |x| + (v - u) := by
  apply max_le
  · have h1 := abs_sub_abs_le_abs_sub u x
    have h2 : |u - x| ≤ v - u := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith [hx.1])]; linarith [hx.2]
    linarith
  · have h1 := abs_sub_abs_le_abs_sub v x
    have h2 : |v - x| ≤ v - u := by
      rw [abs_of_nonneg (by linarith [hx.2])]; linarith [hx.1]
    linarith

/-- `x ↦ e^{c|x|}` is Lipschitz on `[u, v]`, hence of variation at most `|c| e^K (v - u)` there,
if `c |x| ≤ K` on `[u, v]`. -/
theorem eVariationOn_exp_mul_abs_le {c K u v : ℝ} (huv : u ≤ v)
    (hK : ∀ x ∈ Icc u v, c * |x| ≤ K) :
    eVariationOn (fun x ↦ Real.exp (c * |x|)) (Icc u v) ≤
      ENNReal.ofReal (|c| * Real.exp K * (v - u)) := by
  have hL : LipschitzOnWith (Real.toNNReal (|c| * Real.exp K)) (fun x ↦ Real.exp (c * |x|))
      (Icc u v) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
    calc abs (Real.exp (c * |x|) - Real.exp (c * |y|)) ≤
          Real.exp K * abs (c * |x| - c * |y|) :=
          abs_exp_sub_exp_le (hK x hx) (hK y hy)
      _ = Real.exp K * (|c| * abs (|x| - |y|)) := by rw [← mul_sub, abs_mul]
      _ ≤ Real.exp K * (|c| * |x - y|) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (abs_abs_sub_abs_le_abs_sub x y)
            (abs_nonneg c)) (Real.exp_pos K).le
      _ = |c| * Real.exp K * |x - y| := by ring
  have h := hL.comp_eVariationOn_le (g := id) (s := Icc u v) (mapsTo_id _)
  rw [eVariationOn_id_Icc huv, Function.comp_id] at h
  refine h.trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul (by positivity)]
  rfl

theorem norm_le_norm_add_variation {E : Type*} [NormedAddCommGroup E] {g : ℝ → E} {s : Set ℝ}
    (hg : BoundedVariationOn g s) {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) :
    ‖g x‖ ≤ ‖g y‖ + (eVariationOn g s).toReal := by
  have h := hg.dist_le hx hy
  rw [dist_eq_norm] at h
  calc ‖g x‖ = ‖g y + (g x - g y)‖ := by rw [add_sub_cancel]
    _ ≤ ‖g y‖ + ‖g x - g y‖ := norm_add_le _ _
    _ ≤ _ := by linarith

/-- `(v - u) ‖g u‖ ≤ ∫_u^v ‖g‖ + (v - u) Var_{[u, v]} g`. -/
theorem mul_norm_le_integral_add {E : Type*} [NormedAddCommGroup E] {g : ℝ → E} {u v : ℝ}
    (huv : u ≤ v) (hg : BoundedVariationOn g (Icc u v))
    (hgi : IntervalIntegrable (fun x ↦ ‖g x‖) volume u v) :
    (v - u) * ‖g u‖ ≤ (∫ x in u..v, ‖g x‖) + (v - u) * (eVariationOn g (Icc u v)).toReal := by
  have h : ∀ x ∈ Icc u v, ‖g u‖ ≤ ‖g x‖ + (eVariationOn g (Icc u v)).toReal := fun x hx ↦
    norm_le_norm_add_variation hg (left_mem_Icc.2 huv) hx
  have := intervalIntegral.integral_mono_on huv intervalIntegrable_const
    (hgi.add intervalIntegrable_const) h
  rw [intervalIntegral.integral_const, intervalIntegral.integral_add hgi intervalIntegrable_const,
    intervalIntegral.integral_const, smul_eq_mul, smul_eq_mul] at this
  linarith

variable {a u v : ℝ}

/-- `⇐` on one piece: with `F = e^{-a|x|} G`,
`e^{a M} Var_{[u, v]} F ≤ e^a (1 + a) Var_{[u, v]} G + a e^a (v - u) ‖G u‖`,
`M = max (|u|, |v|)`, `v - u ≤ 1`. -/
theorem piece_bound_left {G : ℝ → ℂ} (ha : 0 ≤ a) (huv : u ≤ v) (hh : v - u ≤ 1)
    (hG : BoundedVariationOn G (Icc u v)) :
    Real.exp (a * max |u| |v|) *
        (eVariationOn (fun x ↦ Real.exp (-(a * |x|)) • G x) (Icc u v)).toReal ≤
      Real.exp a * (1 + a) * (eVariationOn G (Icc u v)).toReal +
        a * Real.exp a * ((v - u) * ‖G u‖) := by
  set M := max |u| |v| with hM
  set h := v - u with hhdef
  set VG := (eVariationOn G (Icc u v)).toReal with hVG
  have hh0 : 0 ≤ h := by rw [hhdef]; linarith
  have hVG0 : 0 ≤ VG := ENNReal.toReal_nonneg
  have hf : ∀ x ∈ Icc u v, |Real.exp (-(a * |x|))| ≤ Real.exp (-(a * (M - h))) := by
    intro x hx
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.2
    have := max_abs_le_abs_add hx
    nlinarith
  have hg : ∀ x ∈ Icc u v, ‖G x‖ ≤ ‖G u‖ + VG := fun x hx ↦
    norm_le_norm_add_variation hG hx (left_mem_Icc.2 huv)
  have hfA : eVariationOn (fun x ↦ Real.exp (-(a * |x|))) (Icc u v) ≤
      ENNReal.ofReal (a * Real.exp (-(a * (M - h))) * h) := by
    have := eVariationOn_exp_mul_abs_le (c := -a) (K := -(a * (M - h))) huv (fun x hx ↦ by
      have := max_abs_le_abs_add hx
      nlinarith)
    simpa only [neg_mul, abs_neg, abs_of_nonneg ha] using this
  have h1 := eVariationOn_smul_le_ofReal hf hg hfA (ENNReal.ofReal_toReal hG).ge
    (Real.exp_pos _).le (by positivity) (by positivity) hVG0
  have h2 := ENNReal.toReal_le_of_le_ofReal (by positivity) h1
  have hexp : Real.exp (a * M) * Real.exp (-(a * (M - h))) = Real.exp (a * h) := by
    rw [← Real.exp_add]; ring_nf
  have hah : Real.exp (a * h) ≤ Real.exp a := Real.exp_le_exp.2 (by nlinarith)
  have hah' : a * h ≤ a := by nlinarith
  calc Real.exp (a * M) *
        (eVariationOn (fun x ↦ Real.exp (-(a * |x|)) • G x) (Icc u v)).toReal
      ≤ Real.exp (a * M) * (Real.exp (-(a * (M - h))) * VG +
          (‖G u‖ + VG) * (a * Real.exp (-(a * (M - h))) * h)) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = Real.exp (a * h) * (1 + a * h) * VG + a * Real.exp (a * h) * (h * ‖G u‖) := by
        rw [← hexp]; ring
    _ ≤ Real.exp a * (1 + a) * VG + a * Real.exp a * (h * ‖G u‖) := by
        gcongr

theorem boundedVariationOn_exp_smul {F : ℝ → ℂ} (ha : 0 ≤ a) (huv : u ≤ v)
    (hF : BoundedVariationOn F (Icc u v)) :
    BoundedVariationOn (fun x ↦ Real.exp (a * |x|) • F x) (Icc u v) := by
  have hf : ∀ x ∈ Icc u v, |Real.exp (a * |x|)| ≤ Real.exp (a * max |u| |v|) := by
    intro x hx
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (abs_le_max_abs hx) ha)
  have hg : ∀ x ∈ Icc u v, ‖F x‖ ≤ ‖F u‖ + (eVariationOn F (Icc u v)).toReal := fun x hx ↦
    norm_le_norm_add_variation hF hx (left_mem_Icc.2 huv)
  have hfA := eVariationOn_exp_mul_abs_le (c := a) (K := a * max |u| |v|) huv (fun x hx ↦
    mul_le_mul_of_nonneg_left (abs_le_max_abs hx) ha)
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (eVariationOn_smul_le_ofReal hf hg hfA
    (ENNReal.ofReal_toReal hF).ge (Real.exp_pos _).le (by positivity)
    (mul_nonneg (mul_nonneg (abs_nonneg a) (Real.exp_pos _).le) (sub_nonneg.2 huv))
    ENNReal.toReal_nonneg)

/-- `⇒` on one piece: with `G = e^{a|x|} F`,
`Var_{[u, v]} G ≤ e^{a M} (1 + a (v - u)) Var_{[u, v]} F + a (v - u) e^{a M} ‖F u‖`. -/
theorem piece_bound_right {F : ℝ → ℂ} (ha : 0 ≤ a) (huv : u ≤ v)
    (hF : BoundedVariationOn F (Icc u v)) :
    (eVariationOn (fun x ↦ Real.exp (a * |x|) • F x) (Icc u v)).toReal ≤
      Real.exp (a * max |u| |v|) * (1 + a * (v - u)) * (eVariationOn F (Icc u v)).toReal +
        a * (v - u) * Real.exp (a * max |u| |v|) * ‖F u‖ := by
  set M := max |u| |v| with hM
  set h := v - u with hhdef
  set VF := (eVariationOn F (Icc u v)).toReal with hVF
  have hh0 : 0 ≤ h := by rw [hhdef]; linarith
  have hVF0 : 0 ≤ VF := ENNReal.toReal_nonneg
  have hf : ∀ x ∈ Icc u v, |Real.exp (a * |x|)| ≤ Real.exp (a * M) := by
    intro x hx
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (abs_le_max_abs hx) ha)
  have hg : ∀ x ∈ Icc u v, ‖F x‖ ≤ ‖F u‖ + VF := fun x hx ↦
    norm_le_norm_add_variation hF hx (left_mem_Icc.2 huv)
  have hfA : eVariationOn (fun x ↦ Real.exp (a * |x|)) (Icc u v) ≤
      ENNReal.ofReal (a * Real.exp (a * M) * h) := by
    have := eVariationOn_exp_mul_abs_le (c := a) (K := a * M) huv (fun x hx ↦
      mul_le_mul_of_nonneg_left (abs_le_max_abs hx) ha)
    simpa only [abs_of_nonneg ha] using this
  have h1 := eVariationOn_smul_le_ofReal hf hg hfA (ENNReal.ofReal_toReal hF).ge
    (Real.exp_pos _).le (by positivity) (by positivity) hVF0
  have h2 := ENNReal.toReal_le_of_le_ofReal (by positivity) h1
  calc (eVariationOn (fun x ↦ Real.exp (a * |x|) • F x) (Icc u v)).toReal
      ≤ Real.exp (a * M) * VF + (‖F u‖ + VF) * (a * Real.exp (a * M) * h) := h2
    _ = Real.exp (a * M) * (1 + a * h) * VF + a * h * Real.exp (a * M) * ‖F u‖ := by ring

end Piece

/-! ### The two directions -/

/-- A uniform partition `-X + k h`, `k = 0, …, n`, of `[-X, X]`, with `h ≤ δ`. -/
theorem exists_uniform_partition {X δ : ℝ} (hX : 0 ≤ X) (hδ : 0 < δ) :
    ∃ (n : ℕ) (h : ℝ), 0 ≤ h ∧ h ≤ δ ∧ -X + n * h = X := by
  refine ⟨⌈2 * X / δ⌉₊ + 1, 2 * X / ((⌈2 * X / δ⌉₊ + 1 : ℕ) : ℝ), by positivity, ?_, ?_⟩
  · rw [div_le_iff₀ (by positivity)]
    have h1 := Nat.le_ceil (2 * X / δ)
    rw [div_le_iff₀ hδ] at h1
    push_cast
    nlinarith
  · field_simp
    ring

/-- The variation on `ℝ` is the supremum of the variations on the `[-X, X]`. -/
theorem eVariationOn_univ_le_of_Icc {E : Type*} [PseudoEMetricSpace E] {g : ℝ → E}
    {B : ENNReal} (h : ∀ X : ℝ, 0 ≤ X → eVariationOn g (Icc (-X) X) ≤ B) :
    eVariationOn g univ ≤ B := by
  apply iSup_le
  rintro ⟨n, u, hu, -⟩
  refine le_trans ?_ (h (|u 0| + |u n|) (by positivity))
  rw [Finset.range_eq_Ico]
  refine eVariationOn.sum_le_of_monotoneOn_Icc (hu.monotoneOn _) fun i hi ↦ ⟨?_, ?_⟩
  · have h1 := hu (Nat.zero_le i)
    have h2 := neg_abs_le (u 0)
    linarith [abs_nonneg (u n)]
  · have h1 := hu hi.2
    have h2 := le_abs_self (u n)
    linarith [abs_nonneg (u 0)]

variable {F : ℝ → ℂ} {a : ℝ}

theorem exp_neg_smul_exp_mul (x : ℝ) :
    Real.exp (-(a * |x|)) • ((Real.exp (a * |x|) : ℂ) * F x) = F x := by
  rw [Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel,
    Real.exp_zero, Complex.ofReal_one, one_mul]

theorem variationOnFromTo_sub_eq (hFv : LocallyBoundedVariationOn F univ) {u v : ℝ}
    (huv : u ≤ v) :
    variationOnFromTo F univ 0 v - variationOnFromTo F univ 0 u =
      (eVariationOn F (Icc u v)).toReal := by
  have := variationOnFromTo.add hFv (mem_univ 0) (mem_univ u) (mem_univ v)
  rw [variationOnFromTo.eq_of_le _ _ huv, univ_inter] at this
  linarith

theorem monotone_variationOnFromTo (hFv : LocallyBoundedVariationOn F univ) :
    Monotone (variationOnFromTo F univ 0) := fun x y hxy ↦
  variationOnFromTo.monotoneOn hFv (mem_univ 0) (mem_univ x) (mem_univ y) hxy

/-- `⇐`: if `G = e^{a|·|} F` is integrable and of bounded variation, then
`∫_{-X}^X e^{a|x|} dV_F ≤ e^a (1 + 2a) Var G + a e^a ∫ |G|` for every `X ≥ 0`. -/
theorem stieltjesIntegral_exp_abs_le (ha : 0 ≤ a)
    (hGi : Integrable (fun x ↦ (Real.exp (a * |x|) : ℂ) * F x))
    (hGv : BoundedVariationOn (fun x ↦ (Real.exp (a * |x|) : ℂ) * F x) univ)
    (hFv : LocallyBoundedVariationOn F univ) {X : ℝ} (hX : 0 ≤ X) :
    ∫⟨mul ℝ ℝ⟩ x in -X..X, Real.exp (a * |x|) ∂(variationOnFromTo F univ 0) ≤
      Real.exp a * (1 + 2 * a) *
          (eVariationOn (fun x ↦ (Real.exp (a * |x|) : ℂ) * F x) univ).toReal +
        a * Real.exp a * ∫ x, ‖(Real.exp (a * |x|) : ℂ) * F x‖ := by
  set G : ℝ → ℂ := fun x ↦ (Real.exp (a * |x|) : ℂ) * F x with hG
  set V := variationOnFromTo F univ 0 with hV
  have hVmono : Monotone V := monotone_variationOnFromTo hFv
  have hFeq : (fun x ↦ Real.exp (-(a * |x|)) • G x) = F := funext exp_neg_smul_exp_mul
  obtain ⟨n, h, hh0, hh1, hnX⟩ := exists_uniform_partition hX one_pos
  set x : ℕ → ℝ := fun k ↦ -X + k * h with hx
  have hxmono : Monotone x := fun i j hij ↦ show -X + (i : ℝ) * h ≤ -X + (j : ℝ) * h from
    add_le_add le_rfl (mul_le_mul_of_nonneg_right (Nat.cast_le.2 hij) hh0)
  have hx0 : x 0 = -X := by simp [hx]
  have hxn : x n = X := hnX
  have hxs : ∀ k, x (k + 1) - x k = h := fun k ↦ by simp only [hx]; push_cast; ring
  have hcont : Continuous fun y : ℝ ↦ Real.exp (a * |y|) := by fun_prop
  have hsum := stieltjesIntegral_eq_sum (f := fun y ↦ Real.exp (a * |y|)) (V := V) hxmono n
    hcont.continuousOn (hVmono.monotoneOn _)
  rw [hx0, hxn] at hsum
  rw [hsum]
  have hGint : ∀ k, IntervalIntegrable (fun y ↦ ‖G y‖) volume (x k) (x (k + 1)) := fun k ↦
    hGi.norm.intervalIntegrable
  have hae : 0 ≤ a * Real.exp a := by positivity
  have hpiece : ∀ k ∈ Finset.range n,
      ∫⟨mul ℝ ℝ⟩ y in x k..x (k + 1), Real.exp (a * |y|) ∂V ≤
        Real.exp a * (1 + 2 * a) * (eVariationOn G (Icc (x k) (x (k + 1)))).toReal +
          a * Real.exp a * ∫ y in x k..x (k + 1), ‖G y‖ := by
    intro k _
    have huv : x k ≤ x (k + 1) := hxmono (Nat.le_succ k)
    have hhk : x (k + 1) - x k ≤ 1 := by rw [hxs]; exact hh1
    have hGJ : BoundedVariationOn G (Icc (x k) (x (k + 1))) := hGv.mono (subset_univ _)
    have hRS := (stieltjesIntegral_mem_Icc_of_monotoneOn huv hcont.continuousOn
      (hVmono.monotoneOn _) (m := 0) (M := Real.exp (a * max |x k| |x (k + 1)|)) le_rfl
      (fun y _ ↦ (Real.exp_pos _).le)
      (fun y hy ↦ Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (abs_le_max_abs hy) ha))).2
    rw [hV, variationOnFromTo_sub_eq hFv huv] at hRS
    have hP := piece_bound_left ha huv hhk hGJ
    rw [hFeq] at hP
    have hI := mul_norm_le_integral_add huv hGJ (hGint k)
    have hVG0 : 0 ≤ (eVariationOn G (Icc (x k) (x (k + 1)))).toReal := ENNReal.toReal_nonneg
    have hI' : (x (k + 1) - x k) * ‖G (x k)‖ ≤
        (∫ y in x k..x (k + 1), ‖G y‖) + (eVariationOn G (Icc (x k) (x (k + 1)))).toReal := by
      have : (x (k + 1) - x k) * (eVariationOn G (Icc (x k) (x (k + 1)))).toReal ≤
          (eVariationOn G (Icc (x k) (x (k + 1)))).toReal := by
        nlinarith
      linarith
    calc ∫⟨mul ℝ ℝ⟩ y in x k..x (k + 1), Real.exp (a * |y|) ∂V
        ≤ Real.exp (a * max |x k| |x (k + 1)|) *
            (eVariationOn F (Icc (x k) (x (k + 1)))).toReal := hRS
      _ ≤ Real.exp a * (1 + a) * (eVariationOn G (Icc (x k) (x (k + 1)))).toReal +
            a * Real.exp a * ((x (k + 1) - x k) * ‖G (x k)‖) := hP
      _ ≤ Real.exp a * (1 + a) * (eVariationOn G (Icc (x k) (x (k + 1)))).toReal +
            a * Real.exp a * ((∫ y in x k..x (k + 1), ‖G y‖) +
              (eVariationOn G (Icc (x k) (x (k + 1)))).toReal) := by
          have := mul_le_mul_of_nonneg_left hI' hae
          linarith
      _ = Real.exp a * (1 + 2 * a) * (eVariationOn G (Icc (x k) (x (k + 1)))).toReal +
            a * Real.exp a * ∫ y in x k..x (k + 1), ‖G y‖ := by ring
  have hVsum : ∑ k ∈ Finset.range n, (eVariationOn G (Icc (x k) (x (k + 1)))).toReal ≤
      (eVariationOn G univ).toReal := by
    rw [← ENNReal.toReal_sum (fun k _ ↦ hGv.mono (subset_univ _)),
      ← eVariationOn_Icc_eq_sum G hxmono n]
    exact ENNReal.toReal_mono hGv (eVariationOn.mono G (subset_univ _))
  have hIsum : ∑ k ∈ Finset.range n, ∫ y in x k..x (k + 1), ‖G y‖ ≤ ∫ y, ‖G y‖ := by
    rw [intervalIntegral.sum_integral_adjacent_intervals (fun k _ ↦ hGint k), hx0, hxn,
      intervalIntegral.integral_of_le (by linarith)]
    exact setIntegral_le_integral hGi.norm (Eventually.of_forall fun y ↦ norm_nonneg _)
  calc ∑ k ∈ Finset.range n, ∫⟨mul ℝ ℝ⟩ y in x k..x (k + 1), Real.exp (a * |y|) ∂V
      ≤ ∑ k ∈ Finset.range n,
          (Real.exp a * (1 + 2 * a) * (eVariationOn G (Icc (x k) (x (k + 1)))).toReal +
            a * Real.exp a * ∫ y in x k..x (k + 1), ‖G y‖) := Finset.sum_le_sum hpiece
    _ = Real.exp a * (1 + 2 * a) *
            ∑ k ∈ Finset.range n, (eVariationOn G (Icc (x k) (x (k + 1)))).toReal +
          a * Real.exp a * ∑ k ∈ Finset.range n, ∫ y in x k..x (k + 1), ‖G y‖ := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ Real.exp a * (1 + 2 * a) * (eVariationOn G univ).toReal + a * Real.exp a * ∫ y, ‖G y‖ :=
        add_le_add (mul_le_mul_of_nonneg_left hVsum (by positivity))
          (mul_le_mul_of_nonneg_left hIsum hae)

/-- `⇒`: if `F` has locally bounded variation, `G = e^{a|·|} F` is integrable, and
`∫_{-X}^X e^{a|x|} dV_F ≤ C` for all `X ≥ 0`, then
`Var_{[-X, X]} G ≤ 2 (e^a (1 + a) C + a e^a ∫ |G|)`. -/
theorem eVariationOn_Icc_le_of_stieltjes (ha : 0 ≤ a)
    (hGi : Integrable (fun x ↦ (Real.exp (a * |x|) : ℂ) * F x))
    (hFv : LocallyBoundedVariationOn F univ) {C : ℝ}
    (hC : ∀ X : ℝ, 0 ≤ X →
      ∫⟨mul ℝ ℝ⟩ x in -X..X, Real.exp (a * |x|) ∂(variationOnFromTo F univ 0) ≤ C)
    {X : ℝ} (hX : 0 ≤ X) :
    eVariationOn (fun x ↦ (Real.exp (a * |x|) : ℂ) * F x) (Icc (-X) X) ≤
      ENNReal.ofReal (2 * (Real.exp a * (1 + a) * C +
        a * Real.exp a * ∫ x, ‖(Real.exp (a * |x|) : ℂ) * F x‖)) := by
  set G : ℝ → ℂ := fun x ↦ (Real.exp (a * |x|) : ℂ) * F x with hG
  set V := variationOnFromTo F univ 0 with hV
  have hVmono : Monotone V := monotone_variationOnFromTo hFv
  have hGeq : (fun x ↦ Real.exp (a * |x|) • F x) = G := funext fun x ↦ Complex.real_smul
  have hae : 0 ≤ a * Real.exp a := by positivity
  set δ : ℝ := 1 / (1 + 2 * (a * Real.exp a)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by rw [hδ, div_le_one (by positivity)]; linarith
  have hδa : a * Real.exp a * δ ≤ 1 / 2 := by
    rw [hδ, mul_one_div, div_le_iff₀ (by positivity)]
    linarith
  obtain ⟨n, h, hh0, hhδ, hnX⟩ := exists_uniform_partition hX hδ0
  set x : ℕ → ℝ := fun k ↦ -X + k * h with hx
  have hxmono : Monotone x := fun i j hij ↦ show -X + (i : ℝ) * h ≤ -X + (j : ℝ) * h from
    add_le_add le_rfl (mul_le_mul_of_nonneg_right (Nat.cast_le.2 hij) hh0)
  have hx0 : x 0 = -X := by simp [hx]
  have hxn : x n = X := hnX
  have hxs : ∀ k, x (k + 1) - x k = h := fun k ↦ by simp only [hx]; push_cast; ring
  have hcont : Continuous fun y : ℝ ↦ Real.exp (a * |y|) := by fun_prop
  have hFJ : ∀ k, BoundedVariationOn F (Icc (x k) (x (k + 1))) := fun k ↦ by
    have := hFv (x k) (x (k + 1)) (mem_univ _) (mem_univ _)
    rwa [univ_inter] at this
  have hGJ : ∀ k, BoundedVariationOn G (Icc (x k) (x (k + 1))) := fun k ↦ by
    rw [← hGeq]; exact boundedVariationOn_exp_smul ha (hxmono (Nat.le_succ k)) (hFJ k)
  have hGint : ∀ k, IntervalIntegrable (fun y ↦ ‖G y‖) volume (x k) (x (k + 1)) := fun k ↦
    hGi.norm.intervalIntegrable
  have hpiece : ∀ k ∈ Finset.range n,
      (eVariationOn G (Icc (x k) (x (k + 1)))).toReal ≤
        Real.exp a * (1 + a) * ∫⟨mul ℝ ℝ⟩ y in x k..x (k + 1), Real.exp (a * |y|) ∂V +
          a * Real.exp a * ((∫ y in x k..x (k + 1), ‖G y‖) +
            h * (eVariationOn G (Icc (x k) (x (k + 1)))).toReal) := by
    intro k _
    have huv : x k ≤ x (k + 1) := hxmono (Nat.le_succ k)
    have hhk : x (k + 1) - x k = h := hxs k
    have hh1 : h ≤ 1 := hhδ.trans hδ1
    set M := max |x k| |x (k + 1)| with hM
    set I := ∫⟨mul ℝ ℝ⟩ y in x k..x (k + 1), Real.exp (a * |y|) ∂V with hI
    set VF := (eVariationOn F (Icc (x k) (x (k + 1)))).toReal with hVF
    set VG := (eVariationOn G (Icc (x k) (x (k + 1)))).toReal with hVG
    have hlow : ∀ y ∈ Icc (x k) (x (k + 1)), a * (M - h) ≤ a * |y| := fun y hy ↦ by
      have := max_abs_le_abs_add hy
      rw [hhk] at this
      exact mul_le_mul_of_nonneg_left (by linarith) ha
    have hRS := (stieltjesIntegral_mem_Icc_of_monotoneOn huv hcont.continuousOn
      (hVmono.monotoneOn _) (m := Real.exp (a * (M - h))) (M := Real.exp (a * M))
      (Real.exp_pos _).le (fun y hy ↦ Real.exp_le_exp.2 (hlow y hy))
      (fun y hy ↦ Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (abs_le_max_abs hy) ha))).1
    rw [hV, variationOnFromTo_sub_eq hFv huv] at hRS
    have hP := piece_bound_right ha huv (hFJ k)
    rw [hGeq, hhk] at hP
    have hexpM : Real.exp (a * M) = Real.exp (a * h) * Real.exp (a * (M - h)) := by
      rw [← Real.exp_add]; ring_nf
    have hGn : ‖G (x k)‖ = Real.exp (a * |x k|) * ‖F (x k)‖ := by
      simp only [hG, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    have hFG : Real.exp (a * M) * ‖F (x k)‖ ≤ Real.exp (a * h) * ‖G (x k)‖ := by
      rw [hGn, hexpM, mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.2 (hlow _ (left_mem_Icc.2 huv))) (norm_nonneg _)) (Real.exp_pos _).le
    have hVFI : Real.exp (a * M) * VF ≤ Real.exp (a * h) * I := by
      rw [hexpM, mul_assoc]
      exact mul_le_mul_of_nonneg_left hRS (Real.exp_pos _).le
    have hInt := mul_norm_le_integral_add huv (hGJ k) (hGint k)
    rw [hhk] at hInt
    have hah : Real.exp (a * h) ≤ Real.exp a := Real.exp_le_exp.2 (by nlinarith)
    have hah' : a * h ≤ a := by nlinarith
    have hI0 : 0 ≤ I := (mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg).trans hRS
    have hGk0 : 0 ≤ ‖G (x k)‖ := norm_nonneg _
    have e1 : (1 + a * h) * (Real.exp (a * h) * I) ≤ Real.exp a * (1 + a) * I := by
      have := mul_le_mul (by linarith : 1 + a * h ≤ 1 + a) (mul_le_mul_of_nonneg_right hah hI0)
        (mul_nonneg (Real.exp_pos _).le hI0) (by linarith)
      linarith
    have e2 : a * h * (Real.exp (a * h) * ‖G (x k)‖) ≤
        a * Real.exp a * ((∫ y in x k..x (k + 1), ‖G y‖) + h * VG) := by
      have h1 : a * h * (Real.exp (a * h) * ‖G (x k)‖) ≤ a * Real.exp a * (h * ‖G (x k)‖) := by
        have := mul_le_mul_of_nonneg_right hah (mul_nonneg hh0 hGk0)
        nlinarith
      have h2 := mul_le_mul_of_nonneg_left hInt hae
      linarith
    calc VG ≤ Real.exp (a * M) * (1 + a * h) * VF + a * h * Real.exp (a * M) * ‖F (x k)‖ := hP
      _ = (1 + a * h) * (Real.exp (a * M) * VF) + a * h * (Real.exp (a * M) * ‖F (x k)‖) := by
          ring
      _ ≤ (1 + a * h) * (Real.exp (a * h) * I) + a * h * (Real.exp (a * h) * ‖G (x k)‖) :=
          add_le_add (mul_le_mul_of_nonneg_left hVFI (by positivity))
            (mul_le_mul_of_nonneg_left hFG (by positivity))
      _ ≤ _ := add_le_add e1 e2
  -- sum over the pieces
  have hfin : ∀ k ∈ Finset.range n, eVariationOn G (Icc (x k) (x (k + 1))) ≠ ⊤ := fun k _ ↦
    hGJ k
  have hVX : eVariationOn G (Icc (-X) X) =
      ∑ k ∈ Finset.range n, eVariationOn G (Icc (x k) (x (k + 1))) := by
    rw [← hx0, ← hxn]; exact eVariationOn_Icc_eq_sum G hxmono n
  have hVXfin : eVariationOn G (Icc (-X) X) ≠ ⊤ := by
    rw [hVX]; exact ENNReal.sum_ne_top.2 hfin
  have hVXr : (eVariationOn G (Icc (-X) X)).toReal =
      ∑ k ∈ Finset.range n, (eVariationOn G (Icc (x k) (x (k + 1)))).toReal := by
    rw [hVX, ENNReal.toReal_sum hfin]
  have hIsum :
      ∑ k ∈ Finset.range n, ∫⟨mul ℝ ℝ⟩ y in x k..x (k + 1), Real.exp (a * |y|) ∂V ≤ C := by
    rw [← stieltjesIntegral_eq_sum (f := fun y ↦ Real.exp (a * |y|)) (V := V) hxmono n
      hcont.continuousOn (hVmono.monotoneOn _), hx0, hxn]
    exact hC X hX
  have hNsum : ∑ k ∈ Finset.range n, ∫ y in x k..x (k + 1), ‖G y‖ ≤ ∫ y, ‖G y‖ := by
    rw [intervalIntegral.sum_integral_adjacent_intervals (fun k _ ↦ hGint k), hx0, hxn,
      intervalIntegral.integral_of_le (by linarith)]
    exact setIntegral_le_integral hGi.norm (Eventually.of_forall fun y ↦ norm_nonneg _)
  set VX := (eVariationOn G (Icc (-X) X)).toReal with hVXdef
  have hmain : VX ≤ Real.exp a * (1 + a) * C + a * Real.exp a * (∫ y, ‖G y‖) +
      a * Real.exp a * h * VX := by
    have hA0 : 0 ≤ Real.exp a * (1 + a) := by positivity
    have e : ∀ k ∈ Finset.range n,
        Real.exp a * (1 + a) * ∫⟨mul ℝ ℝ⟩ y in x k..x (k + 1), Real.exp (a * |y|) ∂V +
          a * Real.exp a * ((∫ y in x k..x (k + 1), ‖G y‖) +
            h * (eVariationOn G (Icc (x k) (x (k + 1)))).toReal) =
        Real.exp a * (1 + a) * ∫⟨mul ℝ ℝ⟩ y in x k..x (k + 1), Real.exp (a * |y|) ∂V +
          a * Real.exp a * (∫ y in x k..x (k + 1), ‖G y‖) +
          a * Real.exp a * h * (eVariationOn G (Icc (x k) (x (k + 1)))).toReal :=
      fun k _ ↦ by ring
    have hsum := Finset.sum_le_sum hpiece
    rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← hVXr] at hsum
    calc VX ≤ _ := hsum
      _ ≤ Real.exp a * (1 + a) * C + a * Real.exp a * (∫ y, ‖G y‖) + a * Real.exp a * h * VX :=
          add_le_add (add_le_add (mul_le_mul_of_nonneg_left hIsum hA0)
            (mul_le_mul_of_nonneg_left hNsum hae)) le_rfl
  have hVX0 : 0 ≤ VX := ENNReal.toReal_nonneg
  have hhalf : a * Real.exp a * h * VX ≤ 1 / 2 * VX :=
    mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left hhδ hae).trans hδa) hVX0
  rw [← ENNReal.ofReal_toReal hVXfin]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-! ### Montgomery–Vaughan's hypotheses -/

/-- Montgomery–Vaughan (12.20): `∫ e^{a|x|} |F(x)| dx < ∞`. -/
def MV_12_20 (F : ℝ → ℂ) (a : ℝ) : Prop :=
  ∫⁻ x, ENNReal.ofReal (Real.exp (a * |x|) * ‖F x‖) < ⊤

/-- Montgomery–Vaughan (12.21): `∫ e^{a|x|} |dF(x)| < ∞`. Here `|dF|` is the Stieltjes measure of
the variation `V(x) = Var_{[0, x]} F` (`variationOnFromTo F univ 0`), and the integral is the
library's Riemann–Stieltjes integral of `e^{a|x|}` against `V`, taken over `ℝ` as the limit of the
integrals over `[-X, X]`: `F` has locally bounded variation, and these integrals (which are
nondecreasing in `X`) are bounded. -/
def MV_12_21 (F : ℝ → ℂ) (a : ℝ) : Prop :=
  LocallyBoundedVariationOn F univ ∧ ∃ C : ℝ, ∀ X : ℝ, 0 ≤ X →
    ∫⟨mul ℝ ℝ⟩ x in -X..X, Real.exp (a * |x|) ∂(variationOnFromTo F univ 0) ≤ C

/-- For measurable `F`, (12.20) says that `e^{a|x|} F(x)` is integrable. -/
theorem mv_12_20_iff (hF : AEStronglyMeasurable F) :
    MV_12_20 F a ↔ Integrable (fun x ↦ (Real.exp (a * |x|) : ℂ) * F x) := by
  have heq : ∀ x, ENNReal.ofReal (Real.exp (a * |x|) * ‖F x‖) =
      ‖(Real.exp (a * |x|) : ℂ) * F x‖ₑ := fun x ↦ by
    rw [← ofReal_norm_eq_enorm, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le]
  have hmeas : AEStronglyMeasurable (fun x ↦ (Real.exp (a * |x|) : ℂ) * F x) :=
    (by fun_prop : Continuous fun x : ℝ ↦ (Real.exp (a * |x|) : ℂ)).aestronglyMeasurable.mul hF
  simp only [MV_12_20, heq]
  exact ⟨fun h ↦ ⟨hmeas, hasFiniteIntegral_iff_enorm.2 h⟩,
    fun h ↦ hasFiniteIntegral_iff_enorm.1 h.2⟩

/-- If `e^{a|x|} F(x)` has bounded variation (`a ≥ 0`), so does `F`. -/
theorem boundedVariationOn_of_exp_mul (ha : 0 ≤ a)
    (hGv : BoundedVariationOn (fun x ↦ (Real.exp (a * |x|) : ℂ) * F x) univ) :
    BoundedVariationOn F univ := by
  set G : ℝ → ℂ := fun x ↦ (Real.exp (a * |x|) : ℂ) * F x with hG
  have hFeq : (fun x ↦ Real.exp (-(a * |x|)) • G x) = F := funext exp_neg_smul_exp_mul
  have hdamp : (fun x ↦ Real.exp (-(a * |x|))) = damp a 0 := by
    funext x; simp only [damp, zero_mul, zero_sub]
  have hf : ∀ x ∈ (univ : Set ℝ), |Real.exp (-(a * |x|))| ≤ 1 := fun x _ ↦ by
    rw [abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, neg_nonpos]; positivity
  have hg : ∀ x ∈ (univ : Set ℝ), ‖G x‖ ≤ ‖G 0‖ + (eVariationOn G univ).toReal := fun x _ ↦
    norm_le_norm_add_variation hGv (mem_univ x) (mem_univ 0)
  have hfA : eVariationOn (fun x ↦ Real.exp (-(a * |x|))) univ ≤ ENNReal.ofReal 2 := by
    rw [hdamp, show ENNReal.ofReal 2 = 2 by norm_num]
    exact eVariationOn_damp_le (by rw [abs_zero]; exact ha) univ
  rw [← hFeq]
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (eVariationOn_smul_le_ofReal hf hg hfA
    (ENNReal.ofReal_toReal hGv).ge zero_le_one (by positivity) zero_le_two ENNReal.toReal_nonneg)

/-- **The hypotheses of Montgomery–Vaughan, Theorem 12.13**: for measurable `F` and `a ≥ 0`,
(12.20) and (12.21) hold iff `G(x) = e^{a|x|} F(x)` is integrable and of bounded variation on
`ℝ`. -/
theorem mv_12_20_and_12_21_iff (ha : 0 ≤ a) (hF : AEStronglyMeasurable F) :
    MV_12_20 F a ∧ MV_12_21 F a ↔
      Integrable (fun x ↦ (Real.exp (a * |x|) : ℂ) * F x) ∧
        BoundedVariationOn (fun x ↦ (Real.exp (a * |x|) : ℂ) * F x) univ := by
  rw [mv_12_20_iff hF]
  constructor
  · rintro ⟨hGi, hFv, C, hC⟩
    exact ⟨hGi, ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (eVariationOn_univ_le_of_Icc fun X hX ↦ eVariationOn_Icc_le_of_stieltjes ha hGi hFv hC hX)⟩
  · rintro ⟨hGi, hGv⟩
    have hFv : LocallyBoundedVariationOn F univ :=
      (boundedVariationOn_of_exp_mul ha hGv).locallyBoundedVariationOn
    exact ⟨hGi, hFv, _, fun X hX ↦ stieltjesIntegral_exp_abs_le ha hGi hGv hFv hX⟩

/-- `IEANTN`'s node `IsTestFunctionNode F δ₀` is Montgomery–Vaughan's hypotheses: `δ₀ > 0`, `F`
measurable with (12.20) and (12.21) for `a = (1/2 + δ₀) 2π`, `F(x) = (F(x-) + F(x+))/2`, and
`F(x) + F(-x) = 2F(0) + O(|x|)`. -/
theorem isTestFunctionNode_iff {F : ℝ → ℂ} {δ₀ : ℝ} :
    IsTestFunctionNode F δ₀ ↔
      0 < δ₀ ∧ AEStronglyMeasurable F ∧ MV_12_20 F ((1 / 2 + δ₀) * (2 * π)) ∧
        MV_12_21 F ((1 / 2 + δ₀) * (2 * π)) ∧
        (∀ x : ℝ, F x = (Function.leftLim F x + Function.rightLim F x) / 2) ∧
        (fun x : ℝ ↦ F x + F (-x) - 2 * F 0) =O[𝓝 0] (fun x : ℝ ↦ x) := by
  have ha : (1 / 2 + δ₀) * (2 * π) = (1 + 2 * δ₀) * π := by ring
  rw [ha]
  constructor
  · rintro ⟨hδ, hGi, hGv, hnorm, hO⟩
    have hF : AEStronglyMeasurable F :=
      (isTestFunction_of_node ⟨hδ, hGi, hGv, hnorm, hO⟩).aestronglyMeasurable
    have ha0 : 0 ≤ (1 + 2 * δ₀) * π := by positivity
    obtain ⟨h1, h2⟩ := (mv_12_20_and_12_21_iff ha0 hF).2 ⟨hGi, hGv⟩
    exact ⟨hδ, hF, h1, h2, hnorm, hO⟩
  · rintro ⟨hδ, hF, h1, h2, hnorm, hO⟩
    have ha0 : 0 ≤ (1 + 2 * δ₀) * π := by positivity
    obtain ⟨hGi, hGv⟩ := (mv_12_20_and_12_21_iff ha0 hF).1 ⟨h1, h2⟩
    exact ⟨hδ, hGi, hGv, hnorm, hO⟩

end WeilExplicitFormula
