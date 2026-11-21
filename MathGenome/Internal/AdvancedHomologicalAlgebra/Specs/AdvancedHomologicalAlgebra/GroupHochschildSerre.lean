import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.GrothendieckEdges
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.GroupQuotientCohomologyAction
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives

/-! HA-A05, notes/002/advanced-homological-algebra.tex, lines 3019–3037
and the edge identifications in its proof. Page 0 in a RowDiagram denotes E₂.
Its indices are filtration degree and total degree. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AdvancedHomologicalAlgebra.GrothendieckSpectralSequence
open AdvancedHomologicalAlgebra.GrothendieckEdges
open AdvancedHomologicalAlgebra.G05FilteredEdges
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
open Specs.AdvancedHomologicalAlgebra.GroupQuotientCohomologyAction
open Specs.AdvancedHomologicalAlgebra.GroupCochainComparison.Large

namespace Specs.AdvancedHomologicalAlgebra.GroupHochschildSerre

universe u v w
variable (k : Type u) (G : Type v) [CommRing k] [Group G] (N : Subgroup G) [N.Normal]

local instance standardDerived (A : Type*) [Category A] [Abelian A] :
    HasDerivedCategory A := HasDerivedCategory.standard A

local instance repInjectives (R : Type u) (H : Type v) [CommRing R] [Group H] :
    EnoughInjectives (Rep.{max u v w} R H) :=
  Rep.equivalenceModuleMonoidAlgebra.enoughInjectives_iff.mpr inferInstance

abbrev subgroupInvariants := normalInvariants.{u,v,w} k G N
abbrev quotientInvariants := Rep.invariantsFunctor.{max u v w} k (G ⧸ N)
abbrev totalInvariants := subgroupInvariants.{u,v,w} k G N ⋙ quotientInvariants.{u,v,w} k G N

instance repHomogeneousFunctor_preservesZeroMorphisms (H : Type v) [Group H] :
    (repHomogeneousFunctor.{u,v,w} k H).PreservesZeroMorphisms where
  map_zero M L := by
    ext n φ
    change φ ≫ (0 : M ⟶ L) = 0
    simp

/-- The spectral sequence and the filtered edge data from the Grothendieck
construction on normal-subgroup and quotient invariants. -/
def CompositionStatement : Prop :=
  ∃ P : Package (subgroupInvariants.{u,v,w} k G N) (quotientInvariants.{u,v,w} k G N),
    Nonempty (ObjectEdges (subgroupInvariants.{u,v,w} k G N) (quotientInvariants.{u,v,w} k G N) P)

/-- Restriction is pullback along the inclusion, on the original tuples. -/
def RestrictionFormula (η : repHomogeneousFunctor.{u,v,w} k G ⟶
    restriction.{u,v,w} k G N ⋙ repHomogeneousFunctor.{u,v,w} k N) : Prop :=
  ∀ (M : Rep.{max u v w} k G) n (φ : GroupBar.Large.B.{u,v,w} k G n ⟶ M)
    (c : Fin (n+1) → N),
    (((η.app M).f n).hom φ).hom (GroupBar.Large.single k N c 1) =
      φ.hom (GroupBar.Large.single k G (fun i => (c i : G)) 1)

/-- Inflation is tuple pullback along the quotient and inclusion of the
normal-invariant coefficient submodule into the original module. -/
def InflationFormula (η : subgroupInvariants.{u,v,w} k G N ⋙ repHomogeneousFunctor.{u,v,w} k (G ⧸ N) ⟶
    repHomogeneousFunctor.{u,v,w} k G) : Prop :=
  ∀ (M : Rep.{max u v w} k G) n
    (φ : GroupBar.Large.B.{u,v,w} k (G ⧸ N) n ⟶ (subgroupInvariants.{u,v,w} k G N).obj M)
    (c : Fin (n+1) → G),
    (((η.app M).f n).hom φ).hom (GroupBar.Large.single k G c 1) =
      (φ.hom (GroupBar.Large.single k (G ⧸ N) (fun i => QuotientGroup.mk' N (c i)) 1)).val

/-- Compatibility with the connecting maps of the actual short exact
sequences of homogeneous cochains. Together with the degree-zero formula
and effacement of the source derived functors, this fixes the comparison
in every degree. -/
def PreservesCochainConnectors {A : Type*} [Category A] [Abelian A]
    (L : A ⥤ CochainComplex (ModuleCat.{max u v w} k) ℕ)
    [L.PreservesZeroMorphisms]
    (V : ℕ → A ⥤ ModuleCat.{max u v w} k)
    (δ : ∀ {S : ShortComplex A}, S.ShortExact → ∀ n : ℕ,
      (V n).obj S.X₃ ⟶ (V (n+1)).obj S.X₁)
    (e : ∀ n : ℕ, V n ≅ L ⋙ HomologicalComplex.homologyFunctor _ (.up ℕ) n) : Prop :=
  ∃ exact : ∀ {S : ShortComplex A}, S.ShortExact → (S.map L).ShortExact,
    ∀ {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ),
      δ hS n ≫ (e (n+1)).hom.app S.X₁ =
        (e n).hom.app S.X₃ ≫ (exact hS).δ n (n+1) rfl

/-- Grade-zero normalization of a comparison to homogeneous bar cochains.
A degree-zero class is tested on the cochain obtained from the indicated
fixed element by the bar augmentation, which sends all vertices to 1. -/
def PreservesAugmentation {A : Type*} [Category A]
    (H : Type v) [Group H] (L : A ⥤ Rep.{max u v w} k H)
    (U V : A ⥤ ModuleCat.{max u v w} k) (unit : U ⟶ V)
    (includeFixed : ∀ M : A, U.obj M → L.obj M)
    (e : V ≅ L ⋙ repHomogeneousCohomology.{u,v,w} k H 0) : Prop :=
  ∀ (M : A) (m : U.obj M),
    let C := (repHomogeneousFunctor.{u,v,w} k H).obj (L.obj M)
    ∃ z : C.cycles 0,
      (∀ c : Fin 1 → H,
        ((C.iCycles 0).hom z).hom (GroupBar.Large.single k H c 1) = includeFixed M m) ∧
      ((e.hom.app M).hom ((unit.app M).hom m)) = (C.homologyπ 0).hom z

abbrev forgetQuotient := forget₂ (Rep.{max u v w} k (G ⧸ N)) (ModuleCat.{max u v w} k)

/-- Natural right-derived identifications, with the conjugation action on
ordinary subgroup cohomology retained before applying quotient cohomology. -/
structure CohomologyModels where
  subgroup : ℕ → Rep.{max u v w} k G ⥤ Rep.{max u v w} k (G ⧸ N)
  subgroupDerived : ∀ q, rightValue (subgroupInvariants.{u,v,w} k G N) q ≅ subgroup q
  underlying : ∀ q, subgroup q ⋙ forget₂ _ (ModuleCat.{max u v w} k) ≅
    restriction.{u,v,w} k G N ⋙ repHomogeneousCohomology.{u,v,w} k N q
  subgroup_carrier : ∀ q M, ((subgroup q) ⋙ forgetQuotient.{u,v,w} k G N).obj M =
    (restriction.{u,v,w} k G N ⋙ repHomogeneousCohomology.{u,v,w} k N q).obj M
  underlying_eq : ∀ q M, (underlying q).app M = eqToIso (subgroup_carrier q M)
  conjugation : ∀ M : Rep.{max u v w} k G,
    ∃ a : G →* End (homogeneousComplex k G N M), ActionFormula k G N M a ∧
      ∀ (q : ℕ) (g : G) (x : (homogeneousComplex k G N M).homology q),
        let t := ((underlying q).hom.app M).hom
        let y := ((underlying q).inv.app M).hom x
        t (((subgroup q).obj M).ρ (QuotientGroup.mk' N g) y) =
          (HomologicalComplex.homologyMap (a g).asHom q).hom x
  quotientDerived : ∀ p, rightValue (quotientInvariants.{u,v,w} k G N) p ≅
    repHomogeneousCohomology.{u,v,w} k (G ⧸ N) p
  totalDerived : ∀ n, rightValue (totalInvariants.{u,v,w} k G N) n ≅ repHomogeneousCohomology.{u,v,w} k G n
  subgroup_augmentation : PreservesAugmentation.{u,v,w} k N (restriction.{u,v,w} k G N)
    (subgroupInvariants.{u,v,w} k G N ⋙ forgetQuotient.{u,v,w} k G N)
    (rightValue (subgroupInvariants.{u,v,w} k G N) 0 ⋙ forgetQuotient.{u,v,w} k G N)
    (whiskerRight (degreeZeroUnit (subgroupInvariants.{u,v,w} k G N)) _)
    (fun _ m => m.val)
    (isoWhiskerRight (subgroupDerived 0) _ ≪≫ underlying 0)
  subgroup_connectors : PreservesCochainConnectors.{u,v,w} k
    (restriction.{u,v,w} k G N ⋙ repHomogeneousFunctor.{u,v,w} k N)
    (fun q => rightValue (subgroupInvariants.{u,v,w} k G N) q ⋙ forgetQuotient.{u,v,w} k G N)
    (fun h n => (forgetQuotient.{u,v,w} k G N).map
      (rightBoundary (subgroupInvariants.{u,v,w} k G N) h n))
    (fun q => isoWhiskerRight (subgroupDerived q) _ ≪≫ underlying q)
  quotient_augmentation : PreservesAugmentation.{u,v,w} k (G ⧸ N) (𝟭 _)
    (quotientInvariants.{u,v,w} k G N) (rightValue (quotientInvariants.{u,v,w} k G N) 0)
    (degreeZeroUnit (quotientInvariants.{u,v,w} k G N))
    (fun _ m => m.val) (quotientDerived 0)
  quotient_connectors : PreservesCochainConnectors.{u,v,w} k
    (repHomogeneousFunctor.{u,v,w} k (G ⧸ N))
    (rightValue (quotientInvariants.{u,v,w} k G N))
    (rightBoundary (quotientInvariants.{u,v,w} k G N)) quotientDerived
  total_augmentation : PreservesAugmentation.{u,v,w} k G (𝟭 _)
    (totalInvariants.{u,v,w} k G N) (rightValue (totalInvariants.{u,v,w} k G N) 0)
    (degreeZeroUnit (totalInvariants.{u,v,w} k G N))
    (fun _ m => m.val.val) (totalDerived 0)
  total_connectors : PreservesCochainConnectors.{u,v,w} k
    (repHomogeneousFunctor.{u,v,w} k G)
    (rightValue (totalInvariants.{u,v,w} k G N))
    (rightBoundary (totalInvariants.{u,v,w} k G N)) totalDerived

variable {k G N}

section Coordinates
variable (C : CohomologyModels.{u,v,w} k G N)
  {P : Package (subgroupInvariants.{u,v,w} k G N) (quotientInvariants.{u,v,w} k G N)}
  (E : ObjectEdges (subgroupInvariants.{u,v,w} k G N) (quotientInvariants.{u,v,w} k G N) P)

/-- The displayed second-page comparison uses the same object-case and
ordinary group cohomology coordinates as the edges and differential. -/
def displayedSecond (p q : ℕ) :
    objectSequence _ _ P ⋙ pageEval 0 (p : ℤ) ((p : ℤ)+(q : ℤ)) ≅
      C.subgroup q ⋙ repHomogeneousCohomology.{u,v,w} k (G ⧸ N) p :=
  E.objectCase.secondIso p q ≪≫
    isoWhiskerRight (C.subgroupDerived q) (rightValue (quotientInvariants.{u,v,w} k G N) p) ≪≫
    isoWhiskerLeft (C.subgroup q) (C.quotientDerived p)

def displayedTarget (n : ℕ) :
    objectSequence _ _ P ⋙ targetEval (n : ℤ) ≅ repHomogeneousCohomology.{u,v,w} k G n :=
  E.objectCase.targetIso n ≪≫ C.totalDerived n

def rowCoordinates (n : ℕ) :
    objectSequence _ _ P ⋙ pageEval 0 (n : ℤ) (n : ℤ) ≅
      subgroupInvariants.{u,v,w} k G N ⋙ repHomogeneousCohomology.{u,v,w} k (G ⧸ N) n :=
  E.rowPage n ≪≫ isoWhiskerLeft (subgroupInvariants.{u,v,w} k G N) (C.quotientDerived n)

def columnCoordinates (n : ℕ) :
    objectSequence _ _ P ⋙ pageEval 0 0 (n : ℤ) ≅ C.subgroup n ⋙ quotientInvariants.{u,v,w} k G N :=
  E.columnPage n ≪≫ isoWhiskerRight (C.subgroupDerived n) (quotientInvariants.{u,v,w} k G N)

/-- The differential d₂ from the displayed E₂^{0,1} to E₂^{2,0}, using the
canonical degree-zero identifications with invariants in its end terms. -/
def ordinaryTransgression (M : Rep.{max u v w} k G) :
    (C.subgroup 1 ⋙ quotientInvariants.{u,v,w} k G N).obj M ⟶
      (subgroupInvariants.{u,v,w} k G N ⋙ repHomogeneousCohomology.{u,v,w} k (G ⧸ N) 2).obj M :=
  (columnCoordinates C E 1).inv.app M ≫ transgression ((objectSequence _ _ P).obj M) ≫
    (rowCoordinates C E 2).hom.app M

end Coordinates

/-- Restriction with its codomain in the fixed submodule of the subgroup
cohomology. Forgetting this codomain refinement recovers tuple pullback. -/
structure RestrictionEdge (C : CohomologyModels.{u,v,w} k G N) where
  cochain : repHomogeneousFunctor.{u,v,w} k G ⟶
    restriction.{u,v,w} k G N ⋙ repHomogeneousFunctor.{u,v,w} k N
  formula : RestrictionFormula k G N cochain
  map : ∀ n, repHomogeneousCohomology.{u,v,w} k G n ⟶ C.subgroup n ⋙ quotientInvariants.{u,v,w} k G N
  ordinary : ∀ (n : ℕ) (M : Rep.{max u v w} k G)
    (x : (repHomogeneousCohomology.{u,v,w} k G n).obj M),
    ((C.underlying n).hom.app M).hom (((map n).app M).hom x).val =
      (HomologicalComplex.homologyMap (cochain.app M) n).hom x

/-- Ordinary inflation and restriction are the two edges of the same
spectral sequence through the natural composition comparisons. -/
structure EdgeIdentifications (C : CohomologyModels.{u,v,w} k G N)
    (P : Package (subgroupInvariants.{u,v,w} k G N) (quotientInvariants.{u,v,w} k G N))
    (E : ObjectEdges (subgroupInvariants.{u,v,w} k G N) (quotientInvariants.{u,v,w} k G N) P) where
  restriction : RestrictionEdge C
  inflationCochain : subgroupInvariants.{u,v,w} k G N ⋙ repHomogeneousFunctor.{u,v,w} k (G ⧸ N) ⟶
    repHomogeneousFunctor.{u,v,w} k G
  inflationFormula : InflationFormula k G N inflationCochain
  inflation_eq : ∀ n,
    (isoWhiskerLeft (subgroupInvariants.{u,v,w} k G N) (C.quotientDerived n)).hom ≫
        (whiskerRight inflationCochain (HomologicalComplex.homologyFunctor _ (.up ℕ) n)) =
      derivedFirstEdge (subgroupInvariants.{u,v,w} k G N) (quotientInvariants.{u,v,w} k G N) P n ≫
        (C.totalDerived n).hom
  restriction_eq : ∀ n,
    (C.totalDerived n).hom ≫ restriction.map n =
      classicalColumn (subgroupInvariants.{u,v,w} k G N) (quotientInvariants.{u,v,w} k G N)
          (E.truncation n) E.degreeZero ≫
        (isoWhiskerRight (C.subgroupDerived n) (quotientInvariants.{u,v,w} k G N)).hom
  row_identification : ∀ n, displayedSecond C E n 0 =
    rowIndexIso _ _ P n ≪≫ rowCoordinates C E n ≪≫
      isoWhiskerRight (E.degreeZeroF ≪≫ C.subgroupDerived 0)
        (repHomogeneousCohomology.{u,v,w} k (G ⧸ N) n)
  column_identification : ∀ n, displayedSecond C E 0 n =
    columnIndexIso _ _ P n ≪≫ columnCoordinates C E n ≪≫
      isoWhiskerLeft (C.subgroup n) (E.degreeZero.symm ≪≫ C.quotientDerived 0)
  inflation_filtered : ∀ n (M : Rep.{max u v w} k G),
    (rowCoordinates C E n).hom.app M ≫ HomologicalComplex.homologyMap (inflationCochain.app M) n =
      (E.filtered M).row n ≫ (displayedTarget C E n).hom.app M
  restriction_filtered : ∀ n (M : Rep.{max u v w} k G),
    (displayedTarget C E n).hom.app M ≫ (restriction.map n).app M =
      (E.filtered M).column n ≫ (columnCoordinates C E n).hom.app M

/-- The source's first-quadrant sequence with its actual finite abutment
filtration, ordinary edges, and five terms ending at H²(G,M). -/
def FullStatement (k : Type u) (G : Type v) [CommRing k] [Group G] (N : Subgroup G) [N.Normal] : Prop :=
  ∃ (P : Package (subgroupInvariants.{u,v,w} k G N) (quotientInvariants.{u,v,w} k G N))
    (E : ObjectEdges (subgroupInvariants.{u,v,w} k G N) (quotientInvariants.{u,v,w} k G N) P)
    (C : CohomologyModels.{u,v,w} k G N) (e : EdgeIdentifications C P E),
    (∀ (M : Rep.{max u v w} k G) (r : ℕ) (p n : ℤ), p < 0 ∨ n < p →
      IsZero (((objectSequence _ _ P).obj M).page r p n)) ∧
    ∀ M : Rep.{max u v w} k G,
      ClassicalFiveTerms (HomologicalComplex.homologyMap (e.inflationCochain.app M) 1)
        ((e.restriction.map 1).app M)
        (ordinaryTransgression C E M)
        (HomologicalComplex.homologyMap (e.inflationCochain.app M) 2)

def compositionExpected : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G] (N : Subgroup G) [N.Normal],
    CompositionStatement.{u,v,w} k G N

def modelsExpected : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G] (N : Subgroup G) [N.Normal],
    Nonempty (CohomologyModels.{u,v,w} k G N)

def fullExpected : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G] (N : Subgroup G) [N.Normal],
    FullStatement.{u,v,w} k G N

end Specs.AdvancedHomologicalAlgebra.GroupHochschildSerre
