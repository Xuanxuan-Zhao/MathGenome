import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace LinearAlgebraicGroups.Specs.IwahoriScalarCocycleComposition

open ExceptionalAffineBruhat (FieldPoints scalarPoints)
open ExceptionalIwahoriCongruence (integralRing localIntegers localIntegersInclusion
  changeRingHom integralRingMap)
open IntegralSemisimpleModel (Model Integers integerAlgebra integralSpec)
open Pinning (BasedRootDatum)

attribute [local instance] integerAlgebra

noncomputable section

abbrev changeBase {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :=
  Over.pullback (Spec.map (CommRingCat.ofHom f))

abbrev groupBaseChange {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :=
  (changeBase f).mapGrp

abbrev integerScheme (K : Type u) [Field K] [ValuativeRel K] : Scheme.{u} :=
  Spec (CommRingCat.of (localIntegers K))

abbrev genericPoint (K : Type u) [Field K] [ValuativeRel K] :
    Spec (CommRingCat.of K) ⟶ integerScheme K :=
  Spec.map (CommRingCat.ofHom (localIntegersInclusion K).hom.toRingHom)

/-- A test algebra over the generic point, viewed as a scheme over the valuation ring. -/
abbrev genericTest {K : Type u} [Field K] [ValuativeRel K] (R : TestAlgebra K) :
    Over (integerScheme K) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K R)) ≫ genericPoint K)


variable {K : Type u} [Field K] [ValuativeRel K]
  {E : BasedRootDatum.{u}} {M' : Model E}

local notation "O" => localIntegers K
local notation "S" => integerScheme K

/-- The smooth affine model and its comparison with the marked integral group. -/
structure IwahoriModel (M' : Model E) (K : Type u) [Field K] [ValuativeRel K] where
  model : Grp (Over (integerScheme K))
  affine : IsAffine model.X.left
  smooth : Smooth model.X.hom
  toIntegral : model ⟶ (groupBaseChange (algebraMap Integers (localIntegers K))).obj M'.group
  genericIso : IsIso ((groupBaseChange (localIntegersInclusion K).hom.toRingHom).map toIntegral)

variable (H : IwahoriModel M' K)

/-- The projection of the dilatation to the actual integral group over the integers. -/
def IwahoriModel.projection : H.model.X.left ⟶ M'.group.X.left :=
  H.toIntegral.hom.hom.left ≫
    pullback.fst M'.group.X.hom (Spec.map (CommRingCat.ofHom (algebraMap Integers O)))

theorem IwahoriModel.projection_overIntegers :
    H.projection ≫ M'.group.X.hom =
      H.model.X.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Integers O)) := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap Integers O))
  let f := M'.group.X.hom
  let t := H.toIntegral.hom.hom.left
  change (t ≫ pullback.fst f b) ≫ f = H.model.X.hom ≫ b
  have h : t ≫ pullback.snd f b = H.model.X.hom := Over.w H.toIntegral.hom.hom
  exact (Category.assoc _ _ _).trans
    ((congrArg (t ≫ ·) pullback.condition).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ b) h)))

/-- The generic comparison with the marked integral-group points, on every test algebra. -/
def IwahoriModel.genericImage {R : TestAlgebra K} (x : genericTest R ⟶ H.model.X) :
    IntegralSemisimpleModel.IntegralPoints M'.group (integralRing R) := by
  refine Over.homMk (x.left ≫ H.projection) ?_
  calc
    _ = (genericTest R).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Integers O)) :=
      (Category.assoc _ _ _).trans
        ((congrArg (x.left ≫ ·) H.projection_overIntegers).trans
          ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (Over.w x))))
    _ = _ := by
      change (Spec.map (CommRingCat.ofHom (algebraMap K R)) ≫ genericPoint K) ≫
          Spec.map (CommRingCat.ofHom (algebraMap Integers O)) = _
      rw [Category.assoc, genericPoint, ← Spec.map_comp, ← Spec.map_comp]
      congr 2
      ext n
      change algebraMap K R (algebraMap Integers K n) = algebraMap Integers R n
      exact map_intCast (algebraMap K R) n.down


variable {F : Type u} [Field F] [Algebra F K]

open scoped CategoryTheory.MonObj

/-- The absolute scheme map of a group isomorphism over the inverse ring operation. -/
def semilinearMap (b : O ≃+* O)
    (f : H.model ≅ (groupBaseChange b.symm.toRingHom).obj H.model) :
    H.model.X.left ⟶ H.model.X.left :=
  f.hom.hom.hom.left ≫
    pullback.fst H.model.X.hom (Spec.map (CommRingCat.ofHom b.symm.toRingHom))

/-- The map on arbitrary generic test algebras is the actual conjugation. -/
def ExtendsConjugation (r : FieldPoints M' K) (f : H.model ⟶ H.model) : Prop :=
  ∀ (R : TestAlgebra K) (x : genericTest R ⟶ H.model.X),
    let rR := changeRingHom M'.group (integralRingMap (algebraMap K R)) r
    H.genericImage (R := R) (x ≫ f.hom.hom) = rR * H.genericImage (R := R) x * rR⁻¹

/-- The scalar operation is characterized on the generic fibre by its map on
the base and by preserving the projection to the integral group. -/
def GenericScalarFormula (s : H.model.X.left ⟶ H.model.X.left) : Prop :=
  pullback.fst H.model.X.hom (genericPoint K) ≫ s ≫ H.projection =
    pullback.fst H.model.X.hom (genericPoint K) ≫ H.projection

structure RepresentativeExtension (r : FieldPoints M' K) where
  onModel : H.model ≅ H.model
  generic_agrees : ExtendsConjugation H r onModel.hom
  generic_inverse : ExtendsConjugation H r⁻¹ onModel.inv

structure CoefficientExtension (ρ : Gal(K/F) →* MulAut (FieldPoints M' K)) where
  onIntegers : Gal(K/F) →* (O ≃+* O)
  restricts (σ : Gal(K/F)) (x : O) :
    (localIntegersInclusion K).hom (onIntegers σ x) =
      σ ((localIntegersInclusion K).hom x)
  onModel (σ : Gal(K/F)) :
    H.model ≅ (groupBaseChange (onIntegers σ).symm.toRingHom).obj H.model
  map_one : semilinearMap H (onIntegers 1) (onModel 1) = 𝟙 H.model.X.left
  map_mul (σ τ : Gal(K/F)) :
    semilinearMap H (onIntegers (σ * τ)) (onModel (σ * τ)) =
      semilinearMap H (onIntegers τ) (onModel τ) ≫
        semilinearMap H (onIntegers σ) (onModel σ)
  generic_agrees (σ : Gal(K/F)) (x : genericTest (CommAlgCat.of K K) ⟶ H.model.X) :
    (ρ σ (H.genericImage (R := CommAlgCat.of K K) x)).left =
      Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x.left ≫
        semilinearMap H (onIntegers σ) (onModel σ) ≫ H.projection

/-- The usual twist by a scalar cocycle in the actual coefficient action. -/
def twistAction (ρ : Gal(K/F) →* MulAut (FieldPoints M' K)) (r : Gal(K/F) → FieldPoints M' K)
    (hr : ∀ σ τ, r (σ * τ) = r σ * ρ σ (r τ)) :
    Gal(K/F) →* MulAut (FieldPoints M' K) where
  toFun σ := MulAut.conj (r σ) * ρ σ
  map_one' := by
    have h : r 1 = 1 := by
      have he : r 1 = r 1 * r 1 := by
        simpa only [one_mul, map_one, MulAut.one_apply] using hr 1 1
      exact (mul_left_cancel ((mul_one (r 1)).trans he)).symm
    simp [h]
  map_mul' σ τ := by
    ext x
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, hr, map_inv, mul_inv_rev]


/-- Twisting the scalar maps by the representative isomorphisms extends the
cocycle twist on the marked field points. The same valuation-ring automorphisms
and the specified absolute composites realize the twisted action. -/
def TwistedScalarExtensions : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K] [ValuativeRel K]
    {E : BasedRootDatum.{u}} {M' : Model E}
    (H : IwahoriModel M' K)
    (ρ : Gal(K/F) →* MulAut (FieldPoints M' K))
    (r : Gal(K/F) → FieldPoints M' K)
    (hr : ∀ σ τ, r (σ * τ) = r σ * ρ σ (r τ))
    (_ : ∀ σ g, ρ σ g = scalarPoints M' σ.toRingHom g)
    (a : CoefficientExtension H ρ)
    (_ : ∀ σ, GenericScalarFormula H (semilinearMap H (a.onIntegers σ) (a.onModel σ)))
    (b : ∀ σ, RepresentativeExtension H (r σ)),
    ∃ A : CoefficientExtension H (twistAction ρ r hr),
      A.onIntegers = a.onIntegers ∧
      ∀ σ, semilinearMap H (A.onIntegers σ) (A.onModel σ) =
        semilinearMap H (a.onIntegers σ) (a.onModel σ) ≫ (b σ).onModel.hom.hom.hom.left

end

end LinearAlgebraicGroups.Specs.IwahoriScalarCocycleComposition
