/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Harald Helfgott
-/
module

public import Mathlib.NumberTheory.WeilExplicitFormula.ExplicitFormula
public import Mathlib.NumberTheory.WeilExplicitFormula.GoodHeights

/-! # Montgomery–Vaughan, Theorem 12.13 (`q = 1`): assembly

`ExplicitFormula.lean` proves Weil's explicit formula, `Theorem_12_13`, from three hypotheses:
`Theorem_10_13`, `Lemma_12_2` and `ResidueTheoremRectangle` (`theorem_12_13_of`). The first two are
proved in `ZeroCount.lean` and `GoodHeights.lean`; here they are restated under the names of the
propositions, and `Theorem_12_13` is derived from the residue theorem alone.

## AI usage

This file was written by Claude (Anthropic) in November 2026. It compiles, but has not been
reviewed by a human.
-/

@[expose] public section

noncomputable section

namespace WeilExplicitFormula

/-- Montgomery–Vaughan, Theorem 10.13, in the form of `IEANTN`'s node. -/
theorem theorem_10_13 : Theorem_10_13 := exists_zetaZeroesSum_le

/-- Montgomery–Vaughan, Lemma 12.2, in the form of `IEANTN`'s node. -/
theorem lemma_12_2 : Lemma_12_2 := exists_good_height

/-- Montgomery–Vaughan, Theorem 12.13 (`q = 1`), from the residue theorem for rectangles. -/
theorem theorem_12_13_of_residueTheorem (hres : ResidueTheoremRectangle) : Theorem_12_13 :=
  theorem_12_13_of theorem_10_13 lemma_12_2 hres

end WeilExplicitFormula
