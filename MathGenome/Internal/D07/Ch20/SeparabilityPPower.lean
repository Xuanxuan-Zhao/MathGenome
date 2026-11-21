import MathGenome.Internal.Specs.D07.Ch20.SeparabilityPPower
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure

/-!
K07.20.separability_p_power: an algebraic element a in characteristic p
is separable over K exactly when K(a^p) = K(a).

For the converse, algebraicity makes K(a^p) equal to the polynomial algebra
K[a^p]. Thus a = q(a^p) for some q over K. The polynomial X - q(X^p)
annihilates a and has derivative 1, hence is separable. The minimal polynomial
of a divides it and is therefore separable. This avoids imposing any
hypothesis on the other elements of the ambient field.
-/

universe u v

namespace D07.Ch20.SeparabilityPPower

open Polynomial

/-- The full equivalence from the source, for an arbitrary ambient extension. -/
theorem separability_p_power :
    Specs.D07.Ch20.SeparabilityPPower.SeparabilityCriterion.{u, v} := by
  intro K L _ _ _ p _ hp a ha
  let : ExpChar K p := ExpChar.prime hp
  constructor
  · intro hs
    exact (IntermediateField.adjoin_simple_eq_adjoin_pow_expChar_of_isSeparable
      K L hs p).symm
  · intro heq
    have hm : a ∈ IntermediateField.adjoin K {a ^ p} := by
      rw [heq]
      exact IntermediateField.mem_adjoin_simple_self K a
    have hm' : a ∈ Algebra.adjoin K {a ^ p} := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (ha.pow p)]
      exact hm
    obtain ⟨q, hq⟩ := Algebra.adjoin_mem_exists_aeval K (a ^ p) hm'
    have hd : derivative (X - expand K p q) = (1 : K[X]) := by
      simp [derivative_sub, derivative_expand, CharP.cast_eq_zero]
    have hs : (X - expand K p q).Separable := by
      rw [separable_def, hd]
      exact isCoprime_one_right
    apply hs.of_dvd
    apply minpoly.dvd K a
    simp only [map_sub, aeval_X, expand_aeval, hq, sub_self]

end D07.Ch20.SeparabilityPPower
