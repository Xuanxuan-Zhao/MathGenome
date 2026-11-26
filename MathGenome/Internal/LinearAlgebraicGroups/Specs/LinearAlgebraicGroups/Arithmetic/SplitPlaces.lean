import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.GlobalPlaces
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.TensorProduct.Finite

namespace LinearAlgebraicGroups.Arithmetic

universe u v l

open scoped TensorProduct

/-- For a finite Galois extension, complete splitting at a finite place means that
over the completion every minimal polynomial of an element of the extension splits. -/
def GlobalFieldData.SplitsCompletelyAt {K : Type u} [Field K]
    (D : GlobalFieldData.{u, v} K) (w : D.FinitePlace) (L : Type l)
    [Field L] [Algebra K L] : Prop :=
  ∀ x : L, ((minpoly K x).map (D.embedding (.inl w))).Splits

namespace SplitPlacesSpec

def splitsCompletelyAt_iff_embedding : Prop :=
  ∀ {K : Type u} {L : Type l} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (D : GlobalFieldData.{u, v} K) (w : D.FinitePlace),
    D.SplitsCompletelyAt w L ↔
      ∃ i : L →+* D.FiniteCompletion w, i.comp (algebraMap K L) = D.embedding (.inl w)

def splitsCompletelyAt_iff_tensorProduct : Prop :=
  ∀ {K : Type u} {L : Type l} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (D : GlobalFieldData.{u, v} K) (w : D.FinitePlace),
    let C := D.FiniteCompletion w
    letI : Algebra K C := (D.embedding (.inl w)).toAlgebra
    D.SplitsCompletelyAt w L ↔
      Nonempty (C ⊗[K] L ≃ₐ[C] (Fin (Module.finrank K L) → C))

def exists_splitPlace_outside : Prop :=
  ∀ {K : Type u} {L : Type l} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (D : GlobalFieldData.{u, v} K) (S : Finset D.FinitePlace),
    ∃ w : D.FinitePlace, w ∉ S ∧ D.SplitsCompletelyAt w L

end SplitPlacesSpec

end LinearAlgebraicGroups.Arithmetic
