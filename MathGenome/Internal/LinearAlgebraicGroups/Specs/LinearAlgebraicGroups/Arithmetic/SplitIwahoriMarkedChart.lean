import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat
import Mathlib.AlgebraicGeometry.Geometrically.Connected

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.MonoidalCategory TensorProduct

universe u

namespace LinearAlgebraicGroups.Specs.SplitIwahoriMarkedChart

open AdjointRepresentation (GroupPoints)
open ExceptionalAffineBruhat (SplitLevel FieldPoints residue)
open ExceptionalIwahoriCongruence (localIntegers localIntegersInclusion residueHom)
open ExceptionalIwahoriImageComparison (MarkedCentralCover markedPositiveBorel)
open IntegralSemisimpleModel
open OrderedRootProducts (Enumerates)
open Pinning (BasedRootDatum)

attribute [local instance] integerAlgebra

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 60000

noncomputable section

abbrev ringBaseChange {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :=
  Over.pullback (Spec.map (CommRingCat.ofHom f))

abbrev integerScheme (K : Type u) [Field K] [ValuativeRel K] : Scheme.{u} :=
  Spec (CommRingCat.of (localIntegers K))

abbrev genericPoint (K : Type u) [Field K] [ValuativeRel K] :
    Spec (CommRingCat.of K) ⟶ integerScheme K :=
  Spec.map (CommRingCat.ofHom (localIntegersInclusion K).hom.toRingHom)

abbrev integralBase (K : Type u) [Field K] [ValuativeRel K] :=
  ringBaseChange (algebraMap Integers (localIntegers K))

abbrev specialBase (K : Type u) [Field K] [ValuativeRel K] :
    Over (integerScheme K) ⥤ SchemeOver (residue K) :=
  ringBaseChange (IsLocalRing.residue (localIntegers K))

abbrev integralGroup (K : Type u) [Field K] [ValuativeRel K] (G : IntegralGroup.{u}) :=
  (integralBase K).mapGrp.obj G

abbrev specialGroup (K : Type u) [Field K] [ValuativeRel K] (G : IntegralGroup.{u}) :=
  (specialBase K).mapGrp.obj (integralGroup K G)

/-- The canonical comparison of the two special fibres, specified by its projection. -/
structure ResidueComparison (K : Type u) [Field K] [ValuativeRel K] (G : IntegralGroup.{u}) where
  iso : specialGroup K G ≅ (fibre (residue K)).obj G
  overIntegral :
    iso.hom.hom.hom.left ≫ pullback.fst G.X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap Integers (residue K)))) =
    pullback.fst (integralGroup K G).X.hom
      (Spec.map (CommRingCat.ofHom (residueHom (localIntegers K)).hom.toRingHom)) ≫
    pullback.fst G.X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap Integers (localIntegers K))))

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
  {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
  (Y : SplitLevel K c p p' e)

def IsMarkedCentre (C : ResidueComparison K M'.group) (B : ClosedSubgroup (specialGroup K M'.group)) :
    Prop :=
  ∀ R : TestAlgebra (residue K),
    Set.range (fun b : GroupPoints B.group R =>
      forgetFibrePoint M'.group R (b ≫ B.inclusion.hom.hom ≫ C.iso.hom.hom.hom)) =
    markedPositiveBorel Y.ad.localIwahori.residueFibre R

def ResidueComparisonStatement : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] (G : IntegralGroup.{u}),
    Nonempty (ResidueComparison K G)

def MarkedCentreStatement : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
    {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
    {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
    (Y : SplitLevel K c p p' e) (C : ResidueComparison K M'.group),
    (∃ B, IsMarkedCentre Y C B) ∧
    ∀ (B B' : ClosedSubgroup (specialGroup K M'.group)),
      IsMarkedCentre Y C B → IsMarkedCentre Y C B' →
      ∃! j : B.group ≅ B'.group, j.hom ≫ B'.inclusion = B.inclusion

abbrev RootFactors {I : Type u} (L : AdditiveLine.{u}) (l : List I) :=
  product (fun _ : I => L.group.X) l

abbrev PositiveFactors (E : BasedRootDatum.{u}) (L : AdditiveLine.{u}) (l : List E.I) :=
  (splitTorus E).X ⊗ RootFactors L l

abbrev affineSpace (R : Type u) [CommRing R] (n : ℕ) : Over (Spec (CommRingCat.of R)) :=
  (algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R (MvPolynomial (Fin n) R)))

/-- The section setting each negative root parameter to zero. -/
def zeroRoots {I : Type u} (L : AdditiveLine.{u}) :
    (l : List I) → (𝟙_ IntegralScheme.{u}) ⟶ RootFactors L l
  | [] => 𝟙 _
  | _ :: l =>
      letI : GrpObj additiveScheme.{u} := L.operations
      lift (η[additiveScheme.{u}]) (zeroRoots L l)

abbrev zeroInsertion (E : BasedRootDatum.{u}) (L : AdditiveLine.{u}) (negative positive : List E.I) :
    PositiveFactors E L positive ⟶ RootFactors L negative ⊗ PositiveFactors E L positive :=
  lift (toUnit _ ≫ zeroRoots L negative) (𝟙 _)

def chartMap (K : Type u) [Field K] [ValuativeRel K] {E : BasedRootDatum.{u}}
    (M' : Model E) (negative positive : List E.I) :
    (integralBase K).obj (RootFactors M'.line negative) ⊗
      (((integralBase K).obj (splitTorus E).X) ⊗ (integralBase K).obj (RootFactors M'.line positive)) ⟶
      (integralGroup K M'.group).X :=
  (𝟙 _ ⊗ₘ Functor.LaxMonoidal.μ (integralBase K) _ _) ≫
    Functor.LaxMonoidal.μ (integralBase K) _ _ ≫
    (integralBase K).map (cellMap M'.line M'.torus M'.root negative positive)

structure Chart (M' : Model E) (negative positive : List E.I)
    (B : ClosedSubgroup (specialGroup K M'.group)) where
  negativeSpace : (integralBase K).obj (RootFactors M'.line negative) ≅
    affineSpace (localIntegers K) negative.length
  positiveSpace : (integralBase K).obj (RootFactors M'.line positive) ≅
    affineSpace (localIntegers K) positive.length
  openImmersion : IsOpenImmersion (chartMap K M' negative positive).left
  affine : IsAffine ((integralBase K).obj (PositiveFactors E M'.line positive)).left
  smooth : Smooth ((integralBase K).obj (PositiveFactors E M'.line positive)).hom
  connected : GeometricallyConnected ((integralBase K).obj (PositiveFactors E M'.line positive)).hom
  centreIso : (specialBase K).obj ((integralBase K).obj (PositiveFactors E M'.line positive)) ≅ B.group.X
  centreInsertion :
    centreIso.hom ≫ B.inclusion.hom.hom =
      (specialBase K).map ((integralBase K).map (zeroInsertion E M'.line negative positive ≫
        cellMap M'.line M'.torus M'.root negative positive))

def ChartStatement : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
    {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
    {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
    (Y : SplitLevel K c p p' e) (C : ResidueComparison K M'.group)
    (B : ClosedSubgroup (specialGroup K M'.group)), IsMarkedCentre Y C B →
    ∀ (negative positive : List E.I),
      Enumerates negative {i | ¬ E.base.IsPos i} → Enumerates positive {i | E.base.IsPos i} →
      Nonempty (Chart M' negative positive B)

abbrev IntegralSections (K : Type u) [Field K] [ValuativeRel K] (H : Grp (Over (integerScheme K))) :=
  Over.mk (𝟙 (integerScheme K)) ⟶ H.X

def FlatTestProperty (B : ClosedSubgroup (specialGroup K M'.group))
    {H : Grp (Over (integerScheme K))} (f : H ⟶ integralGroup K M'.group) : Prop :=
  ∀ (X : Over (integerScheme K)), Flat X.hom → ∀ g : X ⟶ (integralGroup K M'.group).X,
    (∃ b : (specialBase K).obj X ⟶ B.group.X,
      b ≫ B.inclusion.hom.hom = (specialBase K).map g) ↔
      ∃! x : X ⟶ H.X, x ≫ f.hom.hom = g

def IntegralPointsStatement : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
    {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
    {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
    (Y : SplitLevel K c p p' e) (C : ResidueComparison K M'.group)
    (B : ClosedSubgroup (specialGroup K M'.group)), IsMarkedCentre Y C B →
    ∀ (H : Grp (Over (integerScheme K))), IsAffine H.X.left → Flat H.X.hom →
    ∀ (f : H ⟶ integralGroup K M'.group), FlatTestProperty B f →
    ∃ i : IntegralSections K H ≃* Y.ad.I, ∀ x,
      (i x : FieldPoints M' K).left = genericPoint K ≫ x.left ≫ f.hom.hom.left ≫
        pullback.fst M'.group.X.hom
          (Spec.map (CommRingCat.ofHom (algebraMap Integers (localIntegers K))))

end

end LinearAlgebraicGroups.Specs.SplitIwahoriMarkedChart
