import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Model.Complexes.Projective
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Model.Complexes.CellCokernels
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Model.Complexes.CellCokernelsKFlat

open CategoryTheory CategoryTheory.Limits

universe u v

namespace DerivedFormalization.Specs.ComplexCofibrations

open Model.Complexes ComplexProjective ComplexCellCokernelsKFlat

/-- A projective cofibration splits in each degree and has a termwise projective
cokernel whose signed Hom into every acyclic left-module complex is acyclic. -/
def cofibrationCharacterizationType : Prop :=
  ∀ (A : Type u) [Ring A] {X Y : Cochains A} (f : X ⟶ Y),
    cofibrationsValue A f ↔
      (∀ n : ℤ, IsSplitMono (f.f n)) ∧
      (∀ n : ℤ, Projective ((cokernel f).X n)) ∧
      (∀ E : Cochains A, E.Acyclic → (CochainComplex.HomComplex (cokernel f) E).Acyclic)

/-- The cokernel of a projective cofibration is K-flat against acyclic complexes
of right modules, with no commutativity assumption on the ring. -/
def cofibrationCokernelKFlatType : Prop :=
  ∀ (A : Type u) [Ring A] {X Y : Cochains A} (f : X ⟶ Y),
    cofibrationsValue A f → isKFlatValue.{u,v} A (cokernel f)

end DerivedFormalization.Specs.ComplexCofibrations
