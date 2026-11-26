import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.MonoidalCategory TensorProduct WithZero

universe u

namespace LinearAlgebraicGroups.Specs.IwahoriPinnedDiagramExtension

open ExceptionalAffineBruhat
open ExceptionalIwahoriCongruence (integralRing localIntegers localIntegersInclusion residueHom
  CellValues cellValue cellValuePoint)
open ExceptionalIwahoriImageComparison (MarkedCentralCover markedPositiveBorel)
open ExceptionalLocalRootCoordinates (normalizedValuation)
open ExceptionalMarkedRootDescent (MarkedFibre markedFibrePoint)
open IntegralSemisimpleModel (Model Integers fibre integerAlgebra integralSpec forgetFibrePoint)
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
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
  {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
  {Y : SplitLevel K c p p' e}

/-- The comparison with the geometric part of the pinned action on every generic test. -/
def GenericPinnedFormula (H : IwahoriModel Y) (C : MarkedFibre M' F)
    (a : Aut C.realization.pinned) (f : H.model ⟶ H.model) : Prop :=
  ∀ (R : TestAlgebra K) (x : genericTest R ⟶ H.model.X),
    letI : Algebra F R := ((algebraMap K R).comp (algebraMap F K)).toAlgebra
    ∃ v : GroupPoints C.realization.pinned.pair.G.val (CommAlgCat.of F R),
      (markedFibrePoint C (CommAlgCat.of F R) v).left = x.left ≫ H.projection ∧
      (markedFibrePoint C (CommAlgCat.of F R)
        (v ≫ a.asIso.hom.group.hom.hom.hom)).left =
          (x ≫ f.hom.hom).left ≫ H.projection

/-- The geometric pinned action at a finite unramified level on the split Iwahori group. -/
def PinnedDiagramExtension : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [FiniteDimensional F K] [IsGalois F K]
    (_ : IsUnramifiedLocalExtension F K)
    {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
    {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
    {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
    (Y : SplitLevel K c p p' e) (H : IwahoriModel Y) (_ : ScaledRootChart H)
    (C : MarkedFibre M' F) (δ : Gal(K/F) →* Aut C.realization.pinned),
    ∃ f : Gal(K/F) →* Aut H.model,
      ∀ σ, GenericPinnedFormula H C (δ σ) (f σ).asIso.hom

end Operators

end

end LinearAlgebraicGroups.Specs.IwahoriPinnedDiagramExtension
