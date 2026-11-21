import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.GroupCochainComparison
import Mathlib.RepresentationTheory.Coinduced
import Mathlib.RepresentationTheory.Rep.Iso

/-! HA-A04, notes/002/advanced-homological-algebra.tex, lines 2988–3020.
Representations are the standard equivalent presentation of left group-algebra
modules. The coefficients, subgroup and commutative ring are unrestricted.
The homogeneous comparison below is part of the statement. -/
noncomputable section
set_option maxHeartbeats 1000000
open CategoryTheory CategoryTheory.Functor
open scoped MonoidAlgebra ModuleCat.Algebra
universe u v w
namespace Specs.AdvancedHomologicalAlgebra.Shapiro
variable (k : Type u) (G : Type v) [CommRing k] [Group G] (H : Subgroup G)

abbrev coindFunctor : Rep.{max u v w} k H ⥤ Rep.{max u v w} k G := Rep.coindFunctor k H.subtype
abbrev coind (L : Rep.{max u v w} k H) : Rep.{max u v w} k G := (coindFunctor k G H).obj L

/-- Homogeneous cochains, with unsigned precomposition by the deletion boundary. -/
abbrev homogeneousFunctor := GroupCochainComparison.Large.repHomogeneousFunctor.{u,v,w} k G

/-- The actual right derived invariants of HA-A01, on the equivalent category Rep. -/
abbrev derivedCohomology (n : ℕ) : Rep.{max u v w} k G ⥤ ModuleCat.{max u v w} k :=
  Rep.toModuleMonoidAlgebra ⋙ GroupDerivedInvariants.cohomology.{u,v,w} k G n

abbrev homogeneousCohomology (n : ℕ) : Rep.{max u v w} k G ⥤ ModuleCat.{max u v w} k :=
  homogeneousFunctor k G ⋙ HomologicalComplex.homologyFunctor (ModuleCat k) (.up ℕ) n

/-- Tuple inclusion, extended k-linearly. -/
def tupleInclusion (n : ℕ) :
    GroupBar.Large.B.{u,v,w} k H n ⟶ Rep.res H.subtype (GroupBar.Large.B.{u,v,w} k G n) :=
  Rep.ofHom
    { __ := MonoidAlgebra.mapDomainLinearMap k k
        (fun c : ULift.{w} (Fin (n+1) → H) => ULift.up fun i => (c.down i : G))
      isIntertwining' h := by
        apply MonoidAlgebra.lhom_ext'
        intro c
        apply LinearMap.ext_ring
        change (MonoidAlgebra.mapDomainLinearMap k k
            (fun c : ULift.{w} (Fin (n+1) → H) => ULift.up fun i => (c.down i : G)))
            ((GroupBar.Large.B.{u,v,w} k H n).ρ h (MonoidAlgebra.single c 1)) =
          (GroupBar.Large.B.{u,v,w} k G n).ρ (h : G)
            ((MonoidAlgebra.mapDomainLinearMap k k
              (fun c : ULift.{w} (Fin (n+1) → H) => ULift.up fun i => (c.down i : G))) (MonoidAlgebra.single c 1))
        rw [Representation.ofMulAction_single, MonoidAlgebra.mapDomainLinearMap_single,
          MonoidAlgebra.mapDomainLinearMap_single, Representation.ofMulAction_single]
        rfl }

/-- Restriction of homogeneous tuples and evaluation at the identity coefficient.
This is defined on Hom cochains, rather than only on cohomology classes. -/
def comparisonComponent (L : Rep.{max u v w} k H) (n : ℕ) :
    (GroupBar.Large.B.{u,v,w} k G n ⟶ coind k G H L) →ₗ[k] (GroupBar.Large.B.{u,v,w} k H n ⟶ L) :=
  (Linear.leftComp k _ (tupleInclusion k G H n)).comp
    (Rep.resCoindHomEquiv.{max u w} H.subtype (GroupBar.Large.B.{u,v,w} k G n) L).symm.toLinearMap

/-- The free resolution assertion includes freeness, not just projectivity. -/
def restrictedFreeType : Prop := ∀ n : ℕ,
  Module.Free k[H] (Rep.res H.subtype (GroupBar.Large.B.{u,v,w} k G n)).ρ.asModule

def restrictedResolutionType : Prop :=
  ∃ P : ProjectiveResolution (GroupBar.Large.trivial.{u,v,w} k H),
    P.complex = ((Rep.resFunctor H.subtype).mapHomologicalComplex (.down ℕ)).obj
      (GroupBar.Large.complex.{u,v,w} k G) ∧
    HEq (P.π.f 0) ((Rep.resFunctor H.subtype).map (GroupBar.Large.augmentation.{u,v,w} k G))

/-- The chosen presentation is exactly Hom over k[H], via the representation/module
 equivalence, with the value on each group-algebra basis vector specified. -/
def coindHomType : Prop := ∀ L : Rep.{max u v w} k H,
  ∃ e : coind k G H L ≃ₗ[k]
      ((Rep.res H.subtype (Rep.leftRegular k G)).ρ.asModule →ₗ[k[H]] L.ρ.asModule),
    ∀ (f : coind k G H L) (g : G),
      (e f) ((Rep.res H.subtype (Rep.leftRegular k G)).ρ.asModuleEquiv.symm
        (MonoidAlgebra.single g 1)) = L.ρ.asModuleEquiv.symm (f.val g)

def actionType : Prop := ∀ (L : Rep.{max u v w} k H) (f : coind k G H L) (g x : G),
  ((coind k G H L).ρ g f).val x = f.val (x * g)

/-- Adjunction with its two inverse formulas and naturality in both variables. -/
def adjunctionType : Prop :=
  ∃ e : ∀ (X : Rep.{max u v w} k G) (L : Rep.{max u v w} k H),
      (X ⟶ coind k G H L) ≃ₗ[k] (Rep.res H.subtype X ⟶ L),
    (∀ X L f x, (e X L f).hom x = (f.hom x).val 1) ∧
    (∀ X L f x g, (((e X L).symm f).hom x).val g = f.hom (X.ρ g x)) ∧
    (∀ (X X' : Rep.{max u v w} k G) (a : X' ⟶ X) (L : Rep.{max u v w} k H) (f : X ⟶ coind k G H L),
      e X' L (a ≫ f) = (Rep.resFunctor H.subtype).map a ≫ e X L f) ∧
    (∀ (X : Rep.{max u v w} k G) (L L' : Rep.{max u v w} k H) (b : L ⟶ L') (f : X ⟶ coind k G H L),
      e X L' (f ≫ (coindFunctor k G H).map b) = e X L f ≫ b)

/-- A single natural cochain comparison in all coefficient modules, with the
source's full homogeneous formula, inducing isomorphisms in every degree. -/
def cochainComparisonType : Prop :=
  ∃ η : coindFunctor k G H ⋙ homogeneousFunctor k G ⟶ homogeneousFunctor k H,
    (∀ (L : Rep.{max u v w} k H) n, (η.app L).f n =
      ModuleCat.ofHom (comparisonComponent k G H L n)) ∧
    (∀ (L : Rep.{max u v w} k H) n (φ : GroupBar.Large.B.{u,v,w} k G n ⟶ coind k G H L)
      (c : Fin (n+1) → H),
      (((η.app L).f n).hom φ).hom (GroupBar.Large.single.{u,v,w} k H c 1) =
        (φ.hom (GroupBar.Large.single.{u,v,w} k G (fun i => (c i : G)) 1)).val 1) ∧
    (∀ L, QuasiIso (η.app L))

local instance standardDerived (A : Type*) [Category A] [Abelian A] :
    HasDerivedCategory A := HasDerivedCategory.standard A

local instance homogeneousFunctor_preservesZeroMorphisms :
    (homogeneousFunctor.{u,v,w} k G).PreservesZeroMorphisms where
  map_zero M L := by
    ext n φ
    change φ ≫ (0 : M ⟶ L) = 0
    exact CategoryTheory.Limits.comp_zero

/-- The degree-zero map on actual group-algebra invariants induced by the
right-derived unit at the ordinary degree-zero stalk. -/
def invariantsUnit :
    GroupDerivedInvariants.invariantsFunctor.{u,v,w} k G ⟶
      GroupDerivedInvariants.cohomology.{u,v,w} k G 0 := by
  let A := GroupDerivedInvariants.GroupModule.{u,v,w} k G
  let B := ModuleCat.{max u v w} k
  let F := GroupDerivedInvariants.invariantsFunctor.{u,v,w} k G
  let stalk : A ⥤ CochainComplex.Plus A :=
    (CochainComplex.plus A).lift (CochainComplex.singleFunctor A 0)
      (fun _ => ⟨0, inferInstance⟩)
  let e : F ⋙ DerivedCategory.Plus.singleFunctor B 0 ≅
      stalk ⋙ F.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q := by
    apply ((FullyFaithful.ofFullyFaithful DerivedCategory.Plus.ι).whiskeringRight A).preimageIso
    change F ⋙ DerivedCategory.singleFunctor B 0 ≅
      CochainComplex.singleFunctor A 0 ⋙ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
    exact isoWhiskerLeft F (DerivedCategory.singleFunctorIsoCompQ B 0) ≪≫
      (associator _ _ _).symm ≪≫
      isoWhiskerRight (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).symm _ ≪≫
      associator _ _ _
  exact (isoWhiskerLeft F (DerivedCategory.singleFunctorCompHomologyFunctorIso B 0)).inv ≫
    whiskerRight (e.hom ≫ whiskerLeft stalk F.rightDerivedFunctorPlusUnit)
      (DerivedCategory.Plus.homologyFunctor B 0)

/-- The normalization in degree zero sends a fixed element to the class of
the cochain obtained by composing with the vertex augmentation. Compatibility
with the actual coefficient boundaries fixes all higher degrees by effacement. -/
structure AugmentedBarComparison where
  iso : ∀ n, derivedCohomology.{u,v,w} k G n ≅ homogeneousCohomology.{u,v,w} k G n
  augmentation : ∀ (M : Rep.{max u v w} k G)
    (m : GroupDerivedInvariants.invariants k G (Rep.toModuleMonoidAlgebra.obj M)),
    let C := (homogeneousFunctor.{u,v,w} k G).obj M
    ∃ z : C.cycles 0,
      (∀ c : Fin 1 → G,
        ((C.iCycles 0).hom z).hom (GroupBar.Large.single.{u,v,w} k G c 1) =
          M.ρ.asModuleEquiv m.val) ∧
      ((iso 0).hom.app M).hom (((invariantsUnit.{u,v,w} k G).app
        (Rep.toModuleMonoidAlgebra.obj M)).hom m) = (C.homologyπ 0).hom z
  cochainExact : ∀ {S : ShortComplex (Rep.{max u v w} k G)},
    S.ShortExact → (S.map (homogeneousFunctor.{u,v,w} k G)).ShortExact
  boundary : ∀ {S : ShortComplex (Rep.{max u v w} k G)} (hS : S.ShortExact) (n : ℕ),
    ClassicalDerivedValues.rightBoundary (GroupDerivedInvariants.invariantsFunctor k G)
        (hS.map_of_exact Rep.toModuleMonoidAlgebra) n ≫ (iso (n+1)).hom.app S.X₁ =
      (iso n).hom.app S.X₃ ≫ (cochainExact hS).δ n (n+1) rfl

/-- The explicit cochain map induces Shapiro's isomorphism on the actual
derived invariants through the augmentation-compatible comparisons. -/
structure ShapiroData where
  cochain : coindFunctor.{u,v,w} k G H ⋙ homogeneousFunctor.{u,v,w} k G ⟶
    homogeneousFunctor.{u,v,w} k H
  component : ∀ (L : Rep.{max u v w} k H) n, (cochain.app L).f n =
    ModuleCat.ofHom (comparisonComponent.{u,v,w} k G H L n)
  sourceBar : AugmentedBarComparison.{u,v,w} k G
  targetBar : AugmentedBarComparison.{u,v,w} k H
  derivedIso : ∀ n, coindFunctor.{u,v,w} k G H ⋙ derivedCohomology.{u,v,w} k G n ≅
    derivedCohomology.{u,v,w} k H n
  comparison : ∀ n,
    (derivedIso n).hom ≫ (targetBar.iso n).hom =
      whiskerLeft (coindFunctor.{u,v,w} k G H) (sourceBar.iso n).hom ≫
        whiskerRight cochain (HomologicalComplex.homologyFunctor (ModuleCat k) (.up ℕ) n)

def shapiroType : Prop := Nonempty (ShapiroData.{u,v,w} k G H)

-- Closed expected types for the implementation targets.
def coindHomExpected : Prop := ∀ (k : Type u) (G : Type v) [CommRing k] [Group G] (H : Subgroup G), coindHomType.{u,v,w} k G H
def actionExpected : Prop := ∀ (k : Type u) (G : Type v) [CommRing k] [Group G] (H : Subgroup G), actionType.{u,v,w} k G H
def adjunctionExpected : Prop := ∀ (k : Type u) (G : Type v) [CommRing k] [Group G] (H : Subgroup G), adjunctionType.{u,v,w} k G H
def restrictedFreeExpected : Prop := ∀ (k : Type u) (G : Type v) [CommRing k] [Group G] (H : Subgroup G), restrictedFreeType.{u,v,w} k G H
def restrictedResolutionExpected : Prop := ∀ (k : Type u) (G : Type v) [CommRing k] [Group G] (H : Subgroup G), restrictedResolutionType.{u,v,w} k G H
def cochainComparisonExpected : Prop := ∀ (k : Type u) (G : Type v) [CommRing k] [Group G] (H : Subgroup G), cochainComparisonType.{u,v,w} k G H
def shapiroExpected : Prop := ∀ (k : Type u) (G : Type v) [CommRing k] [Group G] (H : Subgroup G), shapiroType.{u,v,w} k G H
end Specs.AdvancedHomologicalAlgebra.Shapiro
