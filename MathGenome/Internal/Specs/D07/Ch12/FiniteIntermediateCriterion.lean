import MathGenome.Internal.Specs.D07.Ch12.DegreeDefinition
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs

/-!
Independent specification for K07.12.finite_intermediate_criterion,
paper.tex:3826–3836.

The `Algebra K E` argument records the specified embedding. Finite extension
means finite cardinal vector-space dimension, as in the source. Simplicity
means that one element of E generates all of E as an intermediate field.
Finiteness on the right concerns the entire type of intermediate fields,
including both endpoints. No separability or characteristic hypothesis occurs.
-/

universe u v

namespace Specs.D07.Ch12.FiniteIntermediateCriterion

/-- A finite extension is simple exactly when its intermediate-field lattice
has finitely many elements. The identity extension is included. -/
def SimpleIffFiniteIntermediateFields : Prop :=
  ∀ (K : Type u) (E : Type v) [Field K] [Field E] [Algebra K E],
    DegreeDefinition.finiteExtensionValue K E →
      ((∃ a : E, IntermediateField.adjoin K {a} = ⊤) ↔
        Finite (IntermediateField K E))

end Specs.D07.Ch12.FiniteIntermediateCriterion
