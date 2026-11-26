import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.SplitIwahoriSchemeOperators

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace LinearAlgebraicGroups.Specs.ExceptionalSplitIwahoriDescent

open ExceptionalAffineBruhat
open ExceptionalIwahoriCongruence (localIntegers localIntegersInclusion)
open ExceptionalIwahoriImageComparison (MarkedCentralCover)
open ExceptionalMarkedRootDescent (MarkedFibre markedFibrePoint)
open IntegralSemisimpleModel (Model Integers integerAlgebra)
open Pinning (BasedRootDatum)
open AdjointRepresentation (GroupPoints)
open SplitIwahoriSchemeOperators (IwahoriModel ScaledRootChart integerScheme genericPoint
  CoefficientExtension RepresentativeExtension semilinearMap GenericScalarFormula
  GenericPinnedFormula twistAction IsCoefficientAction IsMarkedRepresentative)

attribute [local instance] integerAlgebra

noncomputable section

section SplitLevel

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
  {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
  (Y : SplitLevel K c p p' e)

/-- The smooth affine dilatation with its marked centre, flat-test universal
property, geometric connectedness, and comparison with the actual Iwahori. -/
structure IwahoriDilatation extends IwahoriModel Y where
  connected : GeometricallyConnected model.X.hom
  pointIso : (Over.mk (𝟙 (integerScheme K)) ⟶ model.X) ≃* Y.ad.I
  pointIso_field (x : Over.mk (𝟙 (integerScheme K)) ⟶ model.X) :
    (pointIso x : FieldPoints M' K).left = genericPoint K ≫ x.left ≫
      toIntegral.hom.hom.left ≫
      pullback.fst M'.group.X.hom
        (Spec.map (CommRingCat.ofHom (algebraMap Integers (localIntegers K))))

end SplitLevel

/-- At every split level the marked smooth dilatation has the scaled
negative–torus–positive root chart covering the special fibre. -/
def SplitIwahoriDilatations : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
    {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
    {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
    (Y : SplitLevel K c p p' e),
    ∃ H : IwahoriDilatation Y, Nonempty (ScaledRootChart H.toIwahoriModel)

/-- The marked representative and its inverse act by group-scheme isomorphisms,
with the actual conjugation formula on every generic test algebra. -/
def MarkedRepresentativeExtensions : Prop :=
  ∀ {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
    {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
    {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
    (Y : SplitLevel K c p p' e) (H : IwahoriDilatation Y) (r : FieldPoints M' K),
    IsMarkedRepresentative Y r → Nonempty (RepresentativeExtension H.toIwahoriModel r)

section Coefficients

variable {F K : Type u} [Field F] [Field K] [Algebra F K]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
  {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
  {Y : SplitLevel K c p p' e}

/-- The extensions of an actual scalar action and its marked representative
twist, with comparison of the composite as a semilinear scheme map. -/
def MarkedScalarTwist (H : IwahoriDilatation Y)
    (ρ : Gal(K/F) →* MulAut (FieldPoints M' K))
    (a : CoefficientExtension H.toIwahoriModel ρ) : Prop :=
  ∀ (r : Gal(K/F) → FieldPoints M' K)
    (hr : ∀ σ τ, r (σ * τ) = r σ * ρ σ (r τ)),
    (∀ σ, IsMarkedRepresentative Y (r σ)) →
    ∃ (b : ∀ σ, RepresentativeExtension H.toIwahoriModel (r σ))
      (A : CoefficientExtension H.toIwahoriModel (twistAction ρ r hr)),
      ∀ σ, semilinearMap H.toIwahoriModel (A.onIntegers σ) (A.onModel σ) =
        semilinearMap H.toIwahoriModel (a.onIntegers σ) (a.onModel σ) ≫
          (b σ).onModel.hom.hom.hom.left

end Coefficients

/-- Scalar and pinned Galois operators extend over the valuation ring.
The relative isomorphisms have the specified generic scheme comparisons and
obey the semilinear action laws. The scalar extension also admits the
compatible twist by a marked representative cocycle. -/
def SplitCoefficientExtensions : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    [ValuativeRel F] [ValuativeRel K] [TopologicalSpace F] [TopologicalSpace K]
    [IsNonarchimedeanLocalField F] [IsNonarchimedeanLocalField K] [ValuativeExtension F K],
    IsUnramifiedLocalExtension F K →
    ∀ {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
    {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
    {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
    (Y : SplitLevel K c p p' e) (H : IwahoriDilatation Y)
    (ρ : Gal(K/F) →* MulAut (FieldPoints M' K)),
    let J := H.toIwahoriModel
    ((∀ σ g, ρ σ g = scalarPoints M' σ.toRingHom g) →
      ∃ a : CoefficientExtension J ρ,
        (∀ σ, GenericScalarFormula J (semilinearMap J (a.onIntegers σ) (a.onModel σ))) ∧
          MarkedScalarTwist H ρ a) ∧
    (∀ (C : MarkedFibre M' F) (δ : Gal(K/F) →* Aut C.realization.pinned),
      (∀ σ v, ρ σ (markedFibrePoint C (CommAlgCat.of F K) v) =
        pinnedCoefficientPoint C (δ σ) σ v) →
      ∃ a : CoefficientExtension J ρ,
        ∀ σ, GenericPinnedFormula J C (δ σ) (semilinearMap J (a.onIntegers σ) (a.onModel σ)))

/-- In the scalar and pinned cases, an Iwahori-valued cocycle is neutralized
inside the Iwahori. For a marked scalar cocycle twist, the integral correction
takes the original cocycle to the representative cocycle in the adjoint group. -/
def SplitIwahoriCocycleNeutralization : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    [ValuativeRel F] [ValuativeRel K] [TopologicalSpace F] [TopologicalSpace K]
    [IsNonarchimedeanLocalField F] [IsNonarchimedeanLocalField K] [ValuativeExtension F K],
    IsUnramifiedLocalExtension F K →
    ∀ {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
    {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
    {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
    (Y : SplitLevel K c p p' e) (ρ : Gal(K/F) →* MulAut (FieldPoints M' K))
    (r a : Gal(K/F) → FieldPoints M' K),
    (∀ σ τ, r (σ * τ) = r σ * ρ σ (r τ)) →
    ((IsCoefficientAction ρ ∧ r = 1) ∨
      ((∀ σ g, ρ σ g = scalarPoints M' σ.toRingHom g) ∧
        ∀ σ, IsMarkedRepresentative Y (r σ))) →
    (∀ σ τ, a (σ * τ) = a σ * ρ σ (a τ)) →
    (∀ σ, a σ * (r σ)⁻¹ ∈ Y.ad.I) →
    ∃ k : Y.ad.I, ∀ σ, (k : FieldPoints M' K)⁻¹ * a σ * ρ σ k = r σ

end

end LinearAlgebraicGroups.Specs.ExceptionalSplitIwahoriDescent
