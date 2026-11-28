import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Quantum.BasicNormalForm
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Quantum.SerreCrossCommutators
import Mathlib.Algebra.Module.Submodule.RestrictScalars

noncomputable section

open scoped TensorProduct

namespace Specs.LieNotes.Quantum.SerreIdeal

open Presentation BasicNormalForm SerreCrossCommutators

universe u v

variable {A : Type u} {T : Type v} [CommRing A] [CommRing T] [Algebra A T]

/-- The underlying coefficient submodule of the Serre ideal of either free factor. -/
def freeSerreSubmodule (q : Aˣ) : Submodule A (FreeAlgebra A Root) :=
  (SerrePresentation.serreIdeal q).asIdeal.restrictScalars A

/-- The image of the tensor inclusion on the negative side. -/
def negativeRange (C : Cartan A T) : Submodule A (OrderedTensor A T) :=
  LinearMap.range
    (TensorProduct.map
      (TensorProduct.map (freeSerreSubmodule C.q).subtype (LinearMap.id (M := T)))
      (LinearMap.id (M := FreeAlgebra A Root)))

/-- The image of the tensor inclusion on the positive side. -/
def positiveRange (C : Cartan A T) : Submodule A (OrderedTensor A T) :=
  LinearMap.range
    (TensorProduct.map
      (LinearMap.id (M := FreeAlgebra A Root ⊗[A] T))
      (freeSerreSubmodule C.q).subtype)

/-- The preimage of the generated two-sided Serre ideal under ordered multiplication. -/
def IdealCorrespondence (C : Cartan A T) : Prop :=
  Submodule.comap (multiplication C)
      ((Presentation.serreIdeal C).asIdeal.restrictScalars A) =
    negativeRange C ⊔ positiveRange C

theorem idealCorrespondence_iff_comap_normalFormEquiv (C : Cartan A T)
    (h : HasNormalForm C) :
    IdealCorrespondence C ↔
      Submodule.comap (normalFormEquiv C h).toLinearMap
          ((Presentation.serreIdeal C).asIdeal.restrictScalars A) =
        negativeRange C ⊔ positiveRange C :=
  Iff.rfl

/-- Both mixed commutation assertions and the ideal correspondence in the basic algebra. -/
def CrossingSerreIdeal (C : Cartan A T) : Prop :=
  CrossCommutators C ∧ IdealCorrespondence C

def GenericProp : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (q : kˣ) (hq : (q : k)^2 ≠ 1),
    CrossingSerreIdeal (generic q hq)

def IndeterminateProp : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k], CrossingSerreIdeal (indeterminate k)

def TruncatedProp : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (N : ℕ), 1 ≤ N →
    CrossingSerreIdeal (truncated k N)

end Specs.LieNotes.Quantum.SerreIdeal
