import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBuilding

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.MonoidalCategory TensorProduct WithZero

universe u

namespace LinearAlgebraicGroups.Specs.SplitIwahoriSchemeOperators

open ExceptionalAffineBruhat
open ExceptionalAffineBuilding (lengthZeroNormalizer)
open ExceptionalIwahoriCongruence (integralRing localIntegers localIntegersInclusion residueHom
  CellValues cellValue cellValuePoint changeRingHom integralRingMap)
open ExceptionalIwahoriImageComparison (MarkedCentralCover markedPositiveBorel)
open ExceptionalLocalRootCoordinates (normalizedValuation)
open ExceptionalMarkedRootDescent (MarkedFibre markedFibrePoint markedWeylWord)
open IntegralSemisimpleModel (Model Integers fibre integerAlgebra integralSpec cocharacter
  torusPoint forgetFibrePoint)
open Pinning (BasedRootDatum)
open AdjointRepresentation (GroupPoints)

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
  (Over.map (genericPoint K)).obj ((testSpec K).obj (op R))

/-- A test algebra over the valuation ring viewed as a scheme over that ring. -/
abbrev integerTest {K : Type u} [Field K] [ValuativeRel K]
    (R : CommAlgCat.{u} (localIntegers K)) : Over (integerScheme K) :=
  (algSpec (CommRingCat.of (localIntegers K))).obj (op R)

section Model

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
  {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
  (Y : SplitLevel K c p p' e)

set_option quotPrecheck false in
local notation "O" => localIntegers K
set_option quotPrecheck false in
local notation "S" => integerScheme K
set_option quotPrecheck false in
local notation "Gₒ" => (groupBaseChange (algebraMap Integers O)).obj M'.group
set_option quotPrecheck false in
local notation "special" => changeBase (residueHom O).hom.toRingHom
set_option quotPrecheck false in
local notation "generic" => groupBaseChange (localIntegersInclusion K).hom.toRingHom

/-- The dilatation data used by the operators. The centre is the marked special Borel. -/
structure IwahoriModel where
  model : Grp (Over S)
  affine : IsAffine model.X.left
  smooth : Smooth model.X.hom
  toIntegral : model ⟶ Gₒ
  genericIso : IsIso ((generic).map toIntegral)
  residueIso : ((groupBaseChange (residueHom O).hom.toRingHom).obj Gₒ) ≅ (fibre (residue K)).obj M'.group
  residueIso_overIntegral :
    residueIso.hom.hom.hom.left ≫ pullback.fst M'.group.X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap Integers (residue K)))) =
      pullback.fst (Gₒ).X.hom (Spec.map (CommRingCat.ofHom (residueHom O).hom.toRingHom)) ≫
      pullback.fst M'.group.X.hom (Spec.map (CommRingCat.ofHom (algebraMap Integers O)))
  borel : ClosedSubgroup ((groupBaseChange (residueHom O).hom.toRingHom).obj Gₒ)
  borel_marked : ∀ R : TestAlgebra (residue K),
    Set.range (fun b : GroupPoints borel.group R =>
      forgetFibrePoint M'.group R
        (b ≫ borel.inclusion.hom.hom ≫ residueIso.hom.hom.hom)) =
      markedPositiveBorel Y.ad.localIwahori.residueFibre R
  universal (X : Over S) (_ : Flat X.hom) (g : X ⟶ (Gₒ).X) :
    (∃ b : (special).obj X ⟶ borel.group.X,
      b ≫ borel.inclusion.hom.hom = (special).map g) ↔
    ∃! f : X ⟶ model.X, f ≫ toIntegral.hom.hom = g

variable {Y} (H : IwahoriModel Y)

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

/-- The marked integral-group point carried by a test point of the dilatation. -/
def IwahoriModel.image {R : CommAlgCat.{u} O} (x : integerTest R ⟶ H.model.X) :
    IntegralSemisimpleModel.IntegralPoints M'.group (integralRing R) := by
  refine Over.homMk (x.left ≫ H.projection) ?_
  calc
    _ = (integerTest R).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Integers O)) :=
      (Category.assoc _ _ _).trans
        ((congrArg (x.left ≫ ·) H.projection_overIntegers).trans
          ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (Over.w x))))
    _ = _ := by
      change Spec.map (CommRingCat.ofHom (algebraMap O R)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap Integers O)) = _
      rw [← Spec.map_comp]
      congr 2
      ext n
      exact map_intCast (algebraMap O R) n.down

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

/-- The product of the marked root lines in order, with the torus in the middle. -/
abbrev rootProductChart (M' : Model E) (negative positive : List E.I) :
    IntegralSemisimpleModel.IntegralScheme :=
  IntegralSemisimpleModel.product (fun _ : E.I => M'.line.group.X) negative ⊗
    ((IntegralSemisimpleModel.splitTorus E).X ⊗
      IntegralSemisimpleModel.product (fun _ : E.I => M'.line.group.X) positive)

/-- An ordered chart of the dilatation, with negative parameters multiplied by
the uniformizer in its projection. The chart and the generic fibre cover the model. -/
structure ScaledRootChart where
  uniformizer : O
  uniformizer_value : normalizedValuation K (uniformizer : K) = WithZero.exp (-1)
  negative : List E.I
  positive : List E.I
  negative_enumerates : OrderedRootProducts.Enumerates negative {i | ¬ E.base.IsPos i}
  positive_enumerates : OrderedRootProducts.Enumerates positive {i | E.base.IsPos i}
  chart : (changeBase (algebraMap Integers O)).obj (rootProductChart M' negative positive) ⟶
    H.model.X
  open_chart : IsOpenImmersion chart.left
  covers : Set.range chart.left ∪ Set.range (pullback.fst H.model.X.hom (genericPoint K)) =
    Set.univ
  scales (R : CommAlgCat.{u} O)
    (q : integerTest R ⟶ (changeBase (algebraMap Integers O)).obj
      (rootProductChart M' negative positive)) :
    ∃ z : CellValues E (integralRing R) negative positive,
      q.left ≫ pullback.fst (rootProductChart M' negative positive).hom
        (Spec.map (CommRingCat.ofHom (algebraMap Integers O))) =
        (cellValuePoint M'.line (integralRing R) negative positive z).left ∧
      H.image (R := R) (q ≫ chart) =
        cellValue M'.toIntegralMarking (integralRing R) negative positive
          ((fun i => algebraMap O R uniformizer * z.1 i), z.2.1, z.2.2)

end Model

section Operators

variable {F K : Type u} [Field F] [Field K] [Algebra F K]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
  {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
  (Y : SplitLevel K c p p' e)

set_option quotPrecheck false in
local notation "O" => localIntegers K

/-- The actual scalar action or the actual pinned semilinear action. -/
def IsCoefficientAction (ρ : Gal(K/F) →* MulAut (FieldPoints M' K)) : Prop :=
  (∀ σ g, ρ σ g = scalarPoints M' σ.toRingHom g) ∨
    ∃ (C : MarkedFibre M' F) (δ : Gal(K/F) →* Aut C.realization.pinned),
      ∀ σ (v : GroupPoints C.realization.pinned.pair.G.val (CommAlgCat.of F K)),
        ρ σ (markedFibrePoint C (CommAlgCat.of F K) v) = pinnedCoefficientPoint C (δ σ) σ v

/-- A length-zero normalizer representative of marked cocharacter and Weyl-word form. -/
def IsMarkedRepresentative (r : FieldPoints M' K) : Prop :=
  r ∈ lengthZeroNormalizer Y.ad ∧
    ∃ (π : Kˣ) (y : E.Y) (word : List E.I),
      normalizedValuation K (π : K) = WithZero.exp (-1) ∧
      r = (torusPoint E (integralRing K) (cocharacter E y (integralRing K) π) ≫
          M'.torus.hom.hom) * markedWeylWord M'.toIntegralMarking (integralRing K) word

variable {Y} (H : IwahoriModel Y)

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

/-- The relative pinned comparison on the generic fibre, on arbitrary generic
test algebras. Together with the semilinear base square, this specifies the scheme map. -/
def GenericPinnedFormula (C : MarkedFibre M' F) (δ : Aut C.realization.pinned)
    (s : H.model.X.left ⟶ H.model.X.left) : Prop :=
  ∀ (R : TestAlgebra K) (x : genericTest R ⟶ H.model.X),
    letI : Algebra F R := ((algebraMap K R).comp (algebraMap F K)).toAlgebra
    ∃ v : GroupPoints C.realization.pinned.pair.G.val (CommAlgCat.of F R),
      (markedFibrePoint C (CommAlgCat.of F R) v).left = x.left ≫ H.projection ∧
      (markedFibrePoint C (CommAlgCat.of F R)
        (v ≫ δ.asIso.hom.group.hom.hom.hom)).left = x.left ≫ s ≫ H.projection

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

end Operators

/-- Precomposing with the generic base change detects equality of scheme morphisms
out of a flat scheme into an affine scheme. -/
def GenericRestrictionInjective : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K]
    (X : Over (integerScheme K)) (Y : Scheme.{u}) (_ : Flat X.hom) (_ : IsAffine Y)
    (f g : X.left ⟶ Y),
    pullback.fst X.hom (genericPoint K) ≫ f = pullback.fst X.hom (genericPoint K) ≫ g →
    f = g

/-- Conjugation by every marked length-zero representative and its inverse extend. -/
def MarkedRepresentativeExtensions : Prop :=
  ∀ {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
    {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
    {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
    (Y : SplitLevel K c p p' e) (H : IwahoriModel Y) (_ : ScaledRootChart H)
    (r : FieldPoints M' K),
    IsMarkedRepresentative Y r → Nonempty (RepresentativeExtension H r)

/-- The scalar and pinned extensions, with their scheme comparisons. In the pinned
case the comparison uses the specified marking and diagram action. -/
def SplitCoefficientExtensions : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    [ValuativeRel F] [ValuativeRel K] [TopologicalSpace F] [TopologicalSpace K]
    [IsNonarchimedeanLocalField F] [IsNonarchimedeanLocalField K] [ValuativeExtension F K],
    IsUnramifiedLocalExtension F K →
    ∀ {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
    {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
    {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
    (Y : SplitLevel K c p p' e) (H : IwahoriModel Y) (_ : ScaledRootChart H)
    (ρ : Gal(K/F) →* MulAut (FieldPoints M' K)),
    ((∀ σ g, ρ σ g = scalarPoints M' σ.toRingHom g) →
      ∃ a : CoefficientExtension H ρ,
        ∀ σ, GenericScalarFormula H (semilinearMap H (a.onIntegers σ) (a.onModel σ))) ∧
    (∀ (C : MarkedFibre M' F) (δ : Gal(K/F) →* Aut C.realization.pinned),
      (∀ σ v, ρ σ (markedFibrePoint C (CommAlgCat.of F K) v) =
        pinnedCoefficientPoint C (δ σ) σ v) →
      ∃ a : CoefficientExtension H ρ,
        ∀ σ, GenericPinnedFormula H C (δ σ) (semilinearMap H (a.onIntegers σ) (a.onModel σ)))

/-- The integral representative extensions and the scalar extensions compose to a
semilinear action whenever the representatives satisfy the actual scalar cocycle law. -/
def TwistedScalarExtensions : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
    {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
    {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
    {Y : SplitLevel K c p p' e} (H : IwahoriModel Y)
    (ρ : Gal(K/F) →* MulAut (FieldPoints M' K))
    (r : Gal(K/F) → FieldPoints M' K)
    (hr : ∀ σ τ, r (σ * τ) = r σ * ρ σ (r τ))
    (_ : ∀ σ g, ρ σ g = scalarPoints M' σ.toRingHom g)
    (a : CoefficientExtension H ρ)
    (_ : ∀ σ, GenericScalarFormula H (semilinearMap H (a.onIntegers σ) (a.onModel σ)))
    (b : ∀ σ, RepresentativeExtension H (r σ)),
    ∃ A : CoefficientExtension H (twistAction ρ r hr),
      ∀ σ, semilinearMap H (A.onIntegers σ) (A.onModel σ) =
        semilinearMap H (a.onIntegers σ) (a.onModel σ) ≫ (b σ).onModel.hom.hom.hom.left

end

end LinearAlgebraicGroups.Specs.SplitIwahoriSchemeOperators
