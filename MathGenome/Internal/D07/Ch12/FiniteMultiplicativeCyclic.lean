import MathGenome.Internal.Specs.D07.Ch12.FiniteMultiplicativeCyclic
import Mathlib.RingTheory.IntegralDomain

/-!
Every finite subgroup of a field's multiplicative group is cyclic
(`lem:finite-multiplicative-cyclic`, paper.tex:3802).

The inclusion H → Kˣ followed by the unit-value map is an injective
multiplicative map into the integral domain K. Mathlib's theorem applies
the polynomial root bound to this map to deduce cyclicity. It requires
finiteness of H alone, and also covers the one-element subgroup.
-/

namespace D07.Ch12.FiniteMultiplicativeCyclic

universe u

theorem finite_multiplicative_subgroup_is_cyclic :
    Specs.D07.Ch12.FiniteMultiplicativeCyclic.FiniteMultiplicativeSubgroupIsCyclic.{u} := by
  intro K _ H _
  exact isCyclic_of_injective_ringHom
    ((Units.coeHom K).comp H.subtype)
    (Units.val_injective.comp Subtype.val_injective)

end D07.Ch12.FiniteMultiplicativeCyclic
