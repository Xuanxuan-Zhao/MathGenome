import MathGenome.Internal.Specs.D07.Ch19.MasonStothers
import Mathlib.NumberTheory.FLT.MasonStothers

/-!
Polynomial abc in characteristic zero, K07.19.mason_stothers.

Mathlib's polynomial abc theorem supplies three degree bounds or vanishing
of all three formal derivatives. We use the sum-zero triple `(a,b,-c)`.
Characteristic zero makes the second branch a triple of constants, excluded
by the source hypothesis. Negating the third input changes neither its degree
nor the normalized radical. The final arithmetic step gives the paper's
maximum bound. The radical interfaces verify the source's monic normalization
and the nonzero-constant convention directly from the canonical definitions.
-/

universe u

namespace D07.Ch19.MasonStothers

open Polynomial UniqueFactorizationMonoid
open Specs.D07.Ch19.MasonStothers

theorem radical_factors : RadicalFactors.{u} := by
  intro F _ f hf
  classical
  constructor
  · intro p
    rw [mem_primeFactors]
    exact Polynomial.mem_normalizedFactors_iff hf
  · rfl

theorem radical_constant : RadicalConstant.{u} := by
  intro F _ x hx
  classical
  exact radical_of_isUnit (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hx))

theorem mason_stothers_bounds : MasonStothersBounds.{u} := by
  intro F _ _ a b c ha hb hc hab _ _ hsum hnonconstant
  classical
  have hsum0 : a + b + -c = 0 := by rw [hsum]; exact add_neg_cancel c
  rcases Polynomial.abc ha hb (neg_ne_zero.mpr hc) hab hsum0 with hbound | hderiv
  · simpa only [mul_neg, UniqueFactorizationDomain.radical_neg, natDegree_neg] using hbound
  · obtain ⟨hda, hdb, hdc⟩ := hderiv
    have hdc' : derivative c = 0 := by simpa only [derivative_neg, neg_eq_zero] using hdc
    exact False.elim (hnonconstant ⟨a.coeff 0, b.coeff 0, c.coeff 0,
      eq_C_of_derivative_eq_zero hda, eq_C_of_derivative_eq_zero hdb,
      eq_C_of_derivative_eq_zero hdc'⟩)

theorem mason_stothers : MasonStothersInequality.{u} := by
  intro F _ _ a b c ha hb hc hab hac hbc hsum hnonconstant
  obtain ⟨hda, hdb, hdc⟩ :=
    mason_stothers_bounds F a b c ha hb hc hab hac hbc hsum hnonconstant
  exact max_le (by omega) (max_le (by omega) (by omega))

end D07.Ch19.MasonStothers
