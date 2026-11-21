import MathGenome.Internal.Specs.D07.Ch12.FiniteIntermediateCriterion
import MathGenome.Internal.D07.Ch12.DegreeDefinition
import Mathlib.FieldTheory.PrimitiveElement

/-!
K07.12.finite_intermediate_criterion: a finite extension is simple if and
only if it has finitely many intermediate fields.

Mathlib's Steinitz theorem gives the equivalence for arbitrary extensions
with algebraicity conjoined on the simple-extension side. Here finite cardinal
dimension supplies finite dimensionality, hence algebraicity. Its proof uses
the mapped minimal polynomial to distinguish intermediate fields in the
forward direction, and the finite-field cyclic argument / infinite-base
two-generator argument in the converse. Thus no separability assumption or
particular algebraically closed field is needed.
-/

universe u v

namespace D07.Ch12.FiniteIntermediateCriterion

theorem simple_iff_finite_intermediate_fields :
    Specs.D07.Ch12.FiniteIntermediateCriterion.SimpleIffFiniteIntermediateFields.{u, v} := by
  intro K E _ _ _ hfinite
  let : FiniteDimensional K E :=
    (DegreeDefinition.finite_iff_finiteDimensional K E).mp hfinite
  have halg : Algebra.IsAlgebraic K E := inferInstance
  constructor
  · intro hsimple
    exact (Field.exists_primitive_element_iff_finite_intermediateField K E).mp
      ⟨halg, hsimple⟩
  · intro hfields
    exact ((Field.exists_primitive_element_iff_finite_intermediateField K E).mpr
      hfields).2

end D07.Ch12.FiniteIntermediateCriterion
