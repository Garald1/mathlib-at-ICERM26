/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Harald Helfgott
-/
module

public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.Analysis.SpecialFunctions.Exp

/-! # Elementary bounds on the variation of functions

We bound the variation of sums and products of functions, of bounded monotone functions on
arbitrary sets, and of two explicit functions on `ℝ` that are used in the proof of
Montgomery–Vaughan, *Multiplicative Number Theory I*, Lemma 12.14
(see `Mathlib.Analysis.BoxIntegral.Stieltjes.DigammaPairing`):

* the cut-off reciprocal `x ↦ x⁻¹ 1_{|x| ≥ δ}`, whose variation is at most `4 / δ`
  (`eVariationOn_inv_cutoff_le`);
* the Gaussian `x ↦ exp(-c x²)`, `c ≥ 0`, whose variation is at most `2`
  (`eVariationOn_exp_neg_mul_sq_le`).

The product bound `eVariationOn_smul_le` is a special case of `eVariationOn_bilinear_comp_le`
in current Mathlib (`Mathlib/Analysis/BoundedVariation.lean`), which is not available in this
branch; we give a direct proof.

## AI usage

This file was written by Claude (Anthropic) in November 2026. It compiles, but has not been
reviewed by a human.
-/

@[expose] public section

open Set
open scoped ENNReal

section General

variable {α : Type*} [LinearOrder α] {E : Type*} [SeminormedAddCommGroup E]

theorem eVariationOn_add_le (f g : α → E) (s : Set α) :
    eVariationOn (fun x ↦ f x + g x) s ≤ eVariationOn f s + eVariationOn g s := by
  apply iSup_le
  rintro ⟨n, ⟨u, hu, us⟩⟩
  calc ∑ i ∈ Finset.range n, edist (f (u (i + 1)) + g (u (i + 1))) (f (u i) + g (u i))
      ≤ ∑ i ∈ Finset.range n,
          (edist (f (u (i + 1))) (f (u i)) + edist (g (u (i + 1))) (g (u i))) :=
        Finset.sum_le_sum fun i _ ↦ edist_add_add_le _ _ _ _
    _ = ∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)) +
          ∑ i ∈ Finset.range n, edist (g (u (i + 1))) (g (u i)) := Finset.sum_add_distrib
    _ ≤ eVariationOn f s + eVariationOn g s :=
        add_le_add (eVariationOn.sum_le hu us) (eVariationOn.sum_le hu us)

theorem eVariationOn_neg (f : α → E) (s : Set α) :
    eVariationOn (fun x ↦ -f x) s = eVariationOn f s := by
  simp only [eVariationOn, edist_neg_neg]

theorem eVariationOn_sub_le (f g : α → E) (s : Set α) :
    eVariationOn (fun x ↦ f x - g x) s ≤ eVariationOn f s + eVariationOn g s := by
  simpa only [sub_eq_add_neg, eVariationOn_neg] using eVariationOn_add_le f (fun x ↦ -g x) s

theorem eVariationOn_const (c : E) (s : Set α) : eVariationOn (fun _ : α ↦ c) s = 0 :=
  eVariationOn.constant_on (by
    rintro _ ⟨x, -, rfl⟩ _ ⟨y, -, rfl⟩
    rfl)

/-- Variation of a product `f • g` of a bounded real function and a bounded vector-valued
function: `Var(f • g) ≤ sup |f| · Var g + sup ‖g‖ · Var f`. -/
theorem eVariationOn_smul_le [NormedSpace ℝ E] {f : α → ℝ} {g : α → E} {s : Set α} {C D : ℝ}
    (hf : ∀ x ∈ s, |f x| ≤ C) (hg : ∀ x ∈ s, ‖g x‖ ≤ D) :
    eVariationOn (fun x ↦ f x • g x) s ≤
      ENNReal.ofReal C * eVariationOn g s + ENNReal.ofReal D * eVariationOn f s := by
  apply iSup_le
  rintro ⟨n, ⟨u, hu, us⟩⟩
  have key : ∀ i, edist (f (u (i + 1)) • g (u (i + 1))) (f (u i) • g (u i)) ≤
      ENNReal.ofReal C * edist (g (u (i + 1))) (g (u i)) +
        ENNReal.ofReal D * edist (f (u (i + 1))) (f (u i)) := by
    intro i
    have h1 := hf _ (us i)
    have h2 := hg _ (us (i + 1))
    have hC : 0 ≤ C := (abs_nonneg _).trans h1
    have hD : 0 ≤ D := (norm_nonneg _).trans h2
    rw [edist_dist, edist_dist, edist_dist, ← ENNReal.ofReal_mul hC, ← ENNReal.ofReal_mul hD,
      ← ENNReal.ofReal_add (mul_nonneg hC dist_nonneg) (mul_nonneg hD dist_nonneg)]
    apply ENNReal.ofReal_le_ofReal
    rw [dist_eq_norm, dist_eq_norm, Real.dist_eq]
    calc ‖f (u (i + 1)) • g (u (i + 1)) - f (u i) • g (u i)‖
        = ‖(f (u (i + 1)) - f (u i)) • g (u (i + 1)) + f (u i) • (g (u (i + 1)) - g (u i))‖ := by
          congr 1; rw [sub_smul, smul_sub]; abel
      _ ≤ |f (u (i + 1)) - f (u i)| * ‖g (u (i + 1))‖ +
            |f (u i)| * ‖g (u (i + 1)) - g (u i)‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ |f (u (i + 1)) - f (u i)| * D + C * ‖g (u (i + 1)) - g (u i)‖ := by
          gcongr
      _ = C * ‖g (u (i + 1)) - g (u i)‖ + D * |f (u (i + 1)) - f (u i)| := by ring
  calc ∑ i ∈ Finset.range n, edist (f (u (i + 1)) • g (u (i + 1))) (f (u i) • g (u i))
      ≤ ∑ i ∈ Finset.range n, (ENNReal.ofReal C * edist (g (u (i + 1))) (g (u i)) +
          ENNReal.ofReal D * edist (f (u (i + 1))) (f (u i))) :=
        Finset.sum_le_sum fun i _ ↦ key i
    _ = ENNReal.ofReal C * ∑ i ∈ Finset.range n, edist (g (u (i + 1))) (g (u i)) +
          ENNReal.ofReal D * ∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ ENNReal.ofReal C * eVariationOn g s + ENNReal.ofReal D * eVariationOn f s := by
        gcongr <;> exact eVariationOn.sum_le hu us

/-- A real form of `eVariationOn_smul_le`. -/
theorem eVariationOn_smul_le_ofReal [NormedSpace ℝ E] {f : α → ℝ} {g : α → E} {s : Set α}
    {C D A B : ℝ} (hf : ∀ x ∈ s, |f x| ≤ C) (hg : ∀ x ∈ s, ‖g x‖ ≤ D)
    (hfA : eVariationOn f s ≤ ENNReal.ofReal A) (hgB : eVariationOn g s ≤ ENNReal.ofReal B)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    eVariationOn (fun x ↦ f x • g x) s ≤ ENNReal.ofReal (C * B + D * A) := by
  refine (eVariationOn_smul_le hf hg).trans ?_
  rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul hC,
    ENNReal.ofReal_mul hD]
  gcongr

/-- A monotone function with values in `[m, M]` has variation at most `M - m` on any set. -/
theorem MonotoneOn.eVariationOn_le_of_mapsTo {f : α → ℝ} {s : Set α} (hf : MonotoneOn f s)
    {m M : ℝ} (hm : ∀ x ∈ s, m ≤ f x) (hM : ∀ x ∈ s, f x ≤ M) :
    eVariationOn f s ≤ ENNReal.ofReal (M - m) := by
  apply iSup_le
  rintro ⟨n, ⟨u, hu, us⟩⟩
  calc
    (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) =
        ∑ i ∈ Finset.range n, ENNReal.ofReal (f (u (i + 1)) - f (u i)) := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [edist_dist, Real.dist_eq, abs_of_nonneg]
      exact sub_nonneg_of_le (hf (us i) (us (i + 1)) (hu (Nat.le_succ _)))
    _ = ENNReal.ofReal (∑ i ∈ Finset.range n, (f (u (i + 1)) - f (u i))) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro i _
      exact sub_nonneg_of_le (hf (us i) (us (i + 1)) (hu (Nat.le_succ _)))
    _ = ENNReal.ofReal (f (u n) - f (u 0)) := by rw [Finset.sum_range_sub fun i ↦ f (u i)]
    _ ≤ ENNReal.ofReal (M - m) :=
      ENNReal.ofReal_le_ofReal (sub_le_sub (hM _ (us n)) (hm _ (us 0)))

theorem Monotone.eVariationOn_le_of_mem_Icc {f : α → ℝ} (hf : Monotone f) {c : ℝ}
    (h : ∀ x, f x ∈ Icc 0 c) (s : Set α) : eVariationOn f s ≤ ENNReal.ofReal c := by
  simpa using (hf.monotoneOn s).eVariationOn_le_of_mapsTo (fun x _ ↦ (h x).1)
    (fun x _ ↦ (h x).2)

end General

section Explicit

/-- The variation of the cut-off reciprocal `x ↦ x⁻¹ 1_{|x| ≥ δ}` is at most `4 / δ`. -/
theorem eVariationOn_inv_cutoff_le {δ : ℝ} (hδ : 0 < δ) (s : Set ℝ) :
    eVariationOn (fun x : ℝ ↦ if δ ≤ |x| then x⁻¹ else 0) s ≤ ENNReal.ofReal (4 / δ) := by
  have hδi : 0 < δ⁻¹ := inv_pos.2 hδ
  set p₁ : ℝ → ℝ := fun x ↦ if -δ < x then δ⁻¹ else 0 with hp₁def
  set p₂ : ℝ → ℝ := fun x ↦ if δ ≤ x then δ⁻¹ else 0 with hp₂def
  set q₁ : ℝ → ℝ := fun x ↦ -(min (-δ) x)⁻¹ with hq₁def
  set q₂ : ℝ → ℝ := fun x ↦ δ⁻¹ - (max δ x)⁻¹ with hq₂def
  have hp₁ : Monotone p₁ := fun x y hxy ↦ by
    simp only [p₁]; split_ifs with h1 h2 <;> linarith
  have hp₂ : Monotone p₂ := fun x y hxy ↦ by
    simp only [p₂]; split_ifs with h1 h2 <;> linarith
  have hq₁ : Monotone q₁ := fun x y hxy ↦ by
    simp only [q₁, neg_le_neg_iff]
    have h1 : min (-δ) x ≤ min (-δ) y := min_le_min le_rfl hxy
    have h2 : min (-δ) y < 0 := (min_le_left _ _).trans_lt (by linarith)
    exact (inv_le_inv_of_neg h2 (h1.trans_lt h2)).2 h1
  have hq₂ : Monotone q₂ := fun x y hxy ↦ by
    simp only [q₂, sub_le_sub_iff_left]
    exact inv_anti₀ (lt_max_of_lt_left hδ) (max_le_max le_rfl hxy)
  have bp₁ : ∀ x, p₁ x ∈ Icc 0 δ⁻¹ := fun x ↦ by
    simp only [p₁]; split_ifs <;> constructor <;> linarith
  have bp₂ : ∀ x, p₂ x ∈ Icc 0 δ⁻¹ := fun x ↦ by
    simp only [p₂]; split_ifs <;> constructor <;> linarith
  have bq₁ : ∀ x, q₁ x ∈ Icc 0 δ⁻¹ := fun x ↦ by
    have hm : min (-δ) x ≤ -δ := min_le_left _ _
    have hm0 : min (-δ) x < 0 := hm.trans_lt (by linarith)
    simp only [q₁, ← inv_neg]
    exact ⟨(inv_pos.2 (by linarith)).le, inv_anti₀ hδ (by linarith)⟩
  have bq₂ : ∀ x, q₂ x ∈ Icc 0 δ⁻¹ := fun x ↦ by
    have hm : δ ≤ max δ x := le_max_left _ _
    have hm0 : 0 < (max δ x)⁻¹ := inv_pos.2 (hδ.trans_le hm)
    simp only [q₂]
    exact ⟨sub_nonneg.2 (inv_anti₀ hδ hm), by linarith⟩
  have heq : (fun x : ℝ ↦ if δ ≤ |x| then x⁻¹ else 0) =
      fun x ↦ ((p₁ x + p₂ x) + -q₁ x) + -q₂ x := by
    funext x
    simp only [p₁, p₂, q₁, q₂]
    rcases le_or_gt x (-δ) with h | h
    · have hx : δ ≤ |x| := by rw [abs_of_neg (by linarith)]; linarith
      rw [if_pos hx, if_neg (not_lt.2 h), if_neg (by linarith), min_eq_right h,
        max_eq_left (by linarith)]
      ring
    · rcases lt_or_ge x δ with h' | h'
      · have hx : ¬ δ ≤ |x| := by rw [not_le, abs_lt]; exact ⟨h, h'⟩
        rw [if_neg hx, if_pos h, if_neg (not_le.2 h'), min_eq_left h.le, max_eq_left h'.le]
        ring
      · have hx : δ ≤ |x| := by rw [abs_of_pos (by linarith)]; exact h'
        rw [if_pos hx, if_pos h, if_pos h', min_eq_left h.le, max_eq_right h']
        ring
  rw [heq]
  calc eVariationOn (fun x ↦ ((p₁ x + p₂ x) + -q₁ x) + -q₂ x) s
      ≤ ((eVariationOn p₁ s + eVariationOn p₂ s) + eVariationOn q₁ s) + eVariationOn q₂ s := by
        refine (eVariationOn_add_le _ _ s).trans ?_
        rw [eVariationOn_neg q₂]
        gcongr
        refine (eVariationOn_add_le _ _ s).trans ?_
        rw [eVariationOn_neg q₁]
        gcongr
        exact eVariationOn_add_le _ _ s
    _ ≤ ((ENNReal.ofReal δ⁻¹ + ENNReal.ofReal δ⁻¹) + ENNReal.ofReal δ⁻¹) +
          ENNReal.ofReal δ⁻¹ := by
        gcongr
        · exact hp₁.eVariationOn_le_of_mem_Icc bp₁ s
        · exact hp₂.eVariationOn_le_of_mem_Icc bp₂ s
        · exact hq₁.eVariationOn_le_of_mem_Icc bq₁ s
        · exact hq₂.eVariationOn_le_of_mem_Icc bq₂ s
    _ = ENNReal.ofReal (4 / δ) := by
        rw [← ENNReal.ofReal_add hδi.le hδi.le, ← ENNReal.ofReal_add (by positivity) hδi.le,
          ← ENNReal.ofReal_add (by positivity) hδi.le]
        congr 1
        ring

/-- The variation of the Gaussian `x ↦ exp(-c x²)`, `c ≥ 0`, is at most `2`. -/
theorem eVariationOn_exp_neg_mul_sq_le {c : ℝ} (hc : 0 ≤ c) (s : Set ℝ) :
    eVariationOn (fun x : ℝ ↦ Real.exp (-(c * x ^ 2))) s ≤ 2 := by
  set u : ℝ → ℝ := fun x ↦ Real.exp (-(c * (min x 0) ^ 2)) with hudef
  set v : ℝ → ℝ := fun x ↦ 1 - Real.exp (-(c * (max x 0) ^ 2)) with hvdef
  have hu : Monotone u := fun x y hxy ↦ by
    simp only [u]
    apply Real.exp_le_exp.2
    apply neg_le_neg
    apply mul_le_mul_of_nonneg_left _ hc
    have h1 : min x 0 ≤ min y 0 := min_le_min hxy le_rfl
    have h2 : min y 0 ≤ 0 := min_le_right _ _
    nlinarith
  have hv : Monotone v := fun x y hxy ↦ by
    simp only [v]
    apply sub_le_sub_left
    apply Real.exp_le_exp.2
    apply neg_le_neg
    apply mul_le_mul_of_nonneg_left _ hc
    have h1 : max x 0 ≤ max y 0 := max_le_max hxy le_rfl
    have h2 : 0 ≤ max x 0 := le_max_right _ _
    nlinarith
  have hle : ∀ z : ℝ, Real.exp (-(c * z ^ 2)) ≤ 1 := fun z ↦
    Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hc (sq_nonneg z)))
  have bu : ∀ x, u x ∈ Icc 0 1 := fun x ↦ ⟨(Real.exp_pos _).le, hle _⟩
  have bv : ∀ x, v x ∈ Icc 0 1 := fun x ↦
    ⟨sub_nonneg.2 (hle _), by simp only [v]; linarith [Real.exp_pos (-(c * (max x 0) ^ 2))]⟩
  have heq : (fun x : ℝ ↦ Real.exp (-(c * x ^ 2))) = fun x ↦ u x + -v x := by
    funext x
    simp only [u, v]
    rcases le_total x 0 with h | h
    · rw [min_eq_left h, max_eq_right h]; simp
    · rw [min_eq_right h, max_eq_left h]; simp
  rw [heq]
  calc eVariationOn (fun x ↦ u x + -v x) s ≤ eVariationOn u s + eVariationOn v s := by
        refine (eVariationOn_add_le _ _ s).trans ?_
        rw [eVariationOn_neg v]
    _ ≤ ENNReal.ofReal 1 + ENNReal.ofReal 1 :=
        add_le_add (hu.eVariationOn_le_of_mem_Icc bu s) (hv.eVariationOn_le_of_mem_Icc bv s)
    _ = 2 := by rw [ENNReal.ofReal_one]; norm_num

end Explicit
