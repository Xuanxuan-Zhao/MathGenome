import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.QuasiSplitInducedWeilProduct
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Multiplicative.CharacterDescent
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy

open CategoryTheory

universe u

namespace LinearAlgebraicGroups.Specs.Arithmetic.TransitiveLeviDescent

open CharacterDescent (Cocharacter)
open GeometricBorelConjugacy (IsQuasiSplit)
open QuasiSplitInducedWeilProduct (ProductDescent orbitField)
open StandardGroups (specialLinearPoints)
open Unipotent (baseChangedAlgebraicGroup)

/-- A quasi-split extension of the permuted rank-one product to the
actual orbit field gives a noncentral cocharacter over the ground field. -/
def TransitiveFactorDescent : Prop :=
  ∀ (F E K I : Type u) [Field F] [Field E] [Infinite E] [Field K]
    [Algebra F E] [Algebra F K] [Module.Finite F E] [Algebra.IsSeparable F E]
    [FiniteDimensional F K] [IsGalois F K] [Finite I] [MulAction Gal(K/F) I]
    (label : I ≃ (E →ₐ[F] K)) (a : E →ₐ[F] K),
    (∀ (σ : Gal(K/F)) i, label (σ • i) = σ.toAlgHom.comp (label i)) →
    ∀ (H : AffineAlgebraicGroup F) (X : ProductDescent (F := F) (K := K) (I := I)),
      Nonempty (specGroup X.descent.coordinate ≅ H.val) →
      (∀ i, Nonempty ((groupPointsFunctor K).obj (specGroup (X.factor i)) ≅
        specialLinearPoints K (ULift.{u} (Fin 2)))) →
      IsQuasiSplit (baseChangedAlgebraicGroup E H) →
      orbitField (F := F) (K := K) (label.symm a) = a.fieldRange ∧
      ∃ (c : Cocharacter H.val) (Y : SchemeOver F) (g : Y ⟶ H.val.X), ¬ Centralizes c g

end LinearAlgebraicGroups.Specs.Arithmetic.TransitiveLeviDescent
