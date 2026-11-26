import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.QuasiSplitInducedWeilProduct
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.RelativeFormComparison

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace LinearAlgebraicGroups.Specs.Arithmetic.DerivedProjectionDescent

open AutomorphismSequence (relativePoints)
open RelativeFormComparison (fieldTest IsInduced transportedAut)
open QuasiSplitInducedWeilProduct (ProductDescent)
open _root_.LinearAlgebraicGroups.Descent.Forms (IsScalarExtensionComparison spectrumIso)

variable {F K : Type u} [Field F] [Field K] [Algebra F K]

/-- A comparison of scalar extensions and its relative point comparison determine
each other uniquely. -/
def ComparisonUniqueness : Prop :=
  ∀ (F K : Type u) [Field F] [Field K] [Algebra F K]
    (V W : GroupScheme F),
    (∀ v : (groupBaseChange F K).obj V ≅ (groupBaseChange F K).obj W,
      ∃! r : relativePoints V (fieldTest F K) ≅ relativePoints W (fieldTest F K),
        IsInduced F K v r) ∧
    (∀ r : relativePoints V (fieldTest F K) ≅ relativePoints W (fieldTest F K),
      ∃! v : (groupBaseChange F K).obj V ≅ (groupBaseChange F K).obj W,
        IsInduced F K v r)

/-- The displacements of two comparisons intertwine the scalar extension of
the reference map whenever the comparisons intertwine the two original maps. -/
def DisplacementSquare : Prop :=
  ∀ (F K : Type u) [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [IsGalois F K]
    {V₀ W₀ V W : GroupScheme F} (u₀ : V₀ ⟶ W₀) (u : V ⟶ W)
    (v : (groupBaseChange F K).obj V₀ ≅ (groupBaseChange F K).obj V)
    (w : (groupBaseChange F K).obj W₀ ≅ (groupBaseChange F K).obj W),
    (groupBaseChange F K).map u₀ ≫ w.hom = v.hom ≫ (groupBaseChange F K).map u →
    ∀ (vR : relativePoints V₀ (fieldTest F K) ≅ relativePoints V (fieldTest F K))
      (wR : relativePoints W₀ (fieldTest F K) ≅ relativePoints W (fieldTest F K)),
      IsInduced F K v vR → IsInduced F K w wR →
      ∀ (σ : Gal(K/F)) (dV : (groupBaseChange F K).obj V₀ ≅ (groupBaseChange F K).obj V₀)
        (dW : (groupBaseChange F K).obj W₀ ≅ (groupBaseChange F K).obj W₀),
        IsInduced F K dV (transportedAut F K vR σ).asIso →
        IsInduced F K dW (transportedAut F K wR σ).asIso →
        (groupBaseChange F K).map u₀ ≫ dW.hom = dV.hom ≫ (groupBaseChange F K).map u₀

/-- The coordinate datum of the known form permutes its actual product
projections when its linear displacements permute the reference projections. -/
def CoordinatePermutationDescent : Prop :=
  ∀ (F K I : Type u) [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [IsGalois F K] [Finite I] [MulAction Gal(K/F) I]
    (H₀ H S : AffineAlgebraicGroup F) (π : I → (H₀.val ⟶ S.val)),
    IsLimit (Fan.mk H₀.val π) →
    ∀ (e : (groupBaseChange F K).obj H₀.val ≅ (groupBaseChange F K).obj H.val)
      (r : relativePoints H₀.val (fieldTest F K) ≅ relativePoints H.val (fieldTest F K)),
      IsInduced F K e r →
      ∀ (δ : Gal(K/F) → ((groupBaseChange F K).obj H₀.val ≅ (groupBaseChange F K).obj H₀.val)),
        (∀ σ, IsInduced F K (δ σ) (transportedAut F K r σ).asIso) →
        (∀ (σ : Gal(K/F)) i, ∃ a : (groupBaseChange F K).obj S.val ≅ (groupBaseChange F K).obj S.val,
          (δ σ).hom ≫ (groupBaseChange F K).map (π (σ • i)) =
            (groupBaseChange F K).map (π i) ≫ a.hom) →
        ∃ (X : ProductDescent (F := F) (K := K) (I := I))
          (j : specGroup X.descent.coordinate ≅ H.val)
          (t : ∀ B : HopfAlgebraCategory F,
            specGroup (extendedHopf K B) ≅ (groupBaseChange F K).obj (specGroup B)),
          IsScalarExtensionComparison t ∧
          ∃ θ : ∀ i, specGroup (X.factor i) ≅ (groupBaseChange F K).obj S.val,
            let γ := (groupBaseChange F K).mapIso j.symm ≪≫
              (t X.descent.coordinate).symm ≪≫ spectrumIso X.descent.comparison
            ∀ i, γ.hom ≫ specGroupMap (X.projection i) ≫ (θ i).hom =
              e.inv ≫ (groupBaseChange F K).map (π i)

end LinearAlgebraicGroups.Specs.Arithmetic.DerivedProjectionDescent
