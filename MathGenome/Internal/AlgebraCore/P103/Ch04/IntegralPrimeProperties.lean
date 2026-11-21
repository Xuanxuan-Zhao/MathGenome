import MathGenome.Internal.AlgebraCore.Specs.P103.Ch04.IntegralPrimeProperties
import Mathlib.RingTheory.Ideal.GoingUp

/-! Maximality and incomparability under integral maps (Theorem 4.7).

Mathlib's strict-contraction result proves incomparability by taking a
monic equation for an element in the difference of two ideals and passing
to the quotient by the smaller prime. It applies to arbitrary ring maps;
no injectivity or domain assumption on either original ring is needed.
-/

namespace P103.Ch04.IntegralPrimeProperties

/-- A commutative domain integral over a field is a field. -/
theorem domain_integral_over_field : Specs.domain_integral_over_field := by
  intro K D _ _ _ _ hK hi
  let : Algebra.IsIntegral K D := ⟨hi⟩
  exact isField_of_isIntegral_of_isField' hK

/-- Both directions hold for every prime, including for noninjective maps. -/
theorem maximal_iff_contraction_maximal : Specs.maximal_iff_contraction_maximal := by
  intro R A _ _ g hg q hq
  let : q.IsPrime := hq
  constructor
  · intro hmax
    let : q.IsMaximal := hmax
    exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal g hg q
  · intro hmax
    exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap g hg q hmax

/-- Strict containment forces strict containment of contractions under an integral map. -/
theorem incomparability : Specs.incomparability := by
  intro R A _ _ g hg q q' hq _ hle heq
  let : Algebra R A := g.toAlgebra
  let : Algebra.IsIntegral R A := ⟨hg⟩
  let : q.IsPrime := hq
  by_contra hne
  have hlt : q.under R < q'.under R :=
    Ideal.IsIntegral.under_lt_under (lt_of_le_of_ne hle hne)
  exact (ne_of_lt hlt) heq

end P103.Ch04.IntegralPrimeProperties
