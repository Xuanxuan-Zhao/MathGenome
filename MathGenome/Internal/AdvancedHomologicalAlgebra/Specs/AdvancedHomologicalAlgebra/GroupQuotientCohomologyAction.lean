import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.GroupCochainComparison
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Induced
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
HA-A05-Action, notes/002/advanced-homological-algebra.tex:3040–3088.
The chapter convention is an arbitrary commutative ring and arbitrary discrete
 groups, with left modules. `Rep k G` is the category equivalent to left
`k[G]`-modules, not a finite-dimensional or semisimple subcategory.
The ring and group retain independent universes; the coefficient category
can be arbitrarily larger than both.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra
universe u v w
namespace Specs.AdvancedHomologicalAlgebra.GroupQuotientCohomologyAction
variable (k : Type u) (G : Type v) [CommRing k] [Group G] (N : Subgroup G) [N.Normal]

abbrev inflation : Rep.{max u v w} k (G ⧸ N) ⥤ Rep.{max u v w} k G := Rep.resFunctor (QuotientGroup.mk' N)
abbrev normalInvariants : Rep.{max u v w} k G ⥤ Rep.{max u v w} k (G ⧸ N) :=
  Rep.quotientToInvariantsFunctor k N
instance normalInvariants_additive : (normalInvariants.{u,v,w} k G N).Additive where
  map_add := by intros; ext x; rfl

abbrev restriction : Rep.{max u v w} k G ⥤ Rep.{max u v w} k N := Rep.resFunctor N.subtype
abbrev induction : Rep.{max u v w} k N ⥤ Rep.{max u v w} k G := Rep.indFunctor k N.subtype

abbrev homogeneousComplex (M : Rep.{max u v w} k G) : CochainComplex (ModuleCat.{max u v w} k) ℕ :=
  (GroupCochainComparison.Large.repHomogeneousFunctor.{u,v,w} k N).obj (Rep.res N.subtype M)

/-- Evaluation at a homogeneous tuple, with coefficient 1. -/
def evaluate (M : Rep.{max u v w} k G) (j : ℕ)
    (φ : (homogeneousComplex k G N M).X j) (c : Fin (j+1) → N) : M :=
  φ.hom (GroupBar.Large.single.{u,v,w} k N c 1)

/-- The source's actual conjugation formula on homogeneous cochains. -/
def ActionFormula (M : Rep.{max u v w} k G)
    (a : G →* End (homogeneousComplex k G N M)) : Prop :=
  ∀ (g : G) (j : ℕ) (φ : (homogeneousComplex k G N M).X j)
    (c : Fin (j+1) → N),
    evaluate k G N M j (((a g).asHom.f j).hom φ) c =
      M.ρ g (evaluate k G N M j φ (fun i => MulAut.conjNormal g⁻¹ (c i)))

/-- The cochain action exists and commutes with the deletion differential,
encoded by its values being morphisms of the actual homogeneous complex. -/
def CochainAction : Prop := ∀ M : Rep.{max u v w} k G,
  ∃ a : G →* End (homogeneousComplex k G N M), ActionFormula k G N M a

/-- Inflation is exact; N-invariants is its right adjoint and preserves
injectives. Exactness is expressed as preservation of finite limits/colimits. -/
def InvariantsAdjunction : Prop :=
  Nonempty (inflation.{u,v,w} k G N ⊣ normalInvariants.{u,v,w} k G N) ∧
  PreservesFiniteLimits (inflation.{u,v,w} k G N) ∧
  PreservesFiniteColimits (inflation.{u,v,w} k G N) ∧
  (normalInvariants.{u,v,w} k G N).PreservesInjectiveObjects

/-- Exact induction is a left adjoint to restriction; consequently restriction
preserves injectives. No finite-index hypothesis is imposed. -/
def RestrictionInjectives : Prop :=
  Nonempty (induction.{u,v,w} k G N ⊣ restriction.{u,v,w} k G N) ∧
  PreservesFiniteLimits (induction.{u,v,w} k G N) ∧
  PreservesFiniteColimits (induction.{u,v,w} k G N) ∧
  (restriction.{u,v,w} k G N).PreservesInjectiveObjects

/-- A valid N-linear homotopy on the homogeneous bar resolution; precomposition
with it proves that each element of N acts identically on cohomology. -/
def Triviality (M : Rep.{max u v w} k G)
    (a : G →* End (homogeneousComplex k G N M)) : Prop :=
  (∀ b : N, Nonempty (Homotopy (a b).asHom (𝟙 _))) ∧
  (∀ (b : N) (j : ℕ), HomologicalComplex.homologyMap (a b).asHom j = 𝟙 _)

/-- The quotient representation on cohomology is specified by the induced
cochain action, not an arbitrary isomorphic module structure. -/
def QuotientAction (M : Rep.{max u v w} k G)
    (a : G →* End (homogeneousComplex k G N M)) : Prop :=
  ∀ j : ℕ, ∃ ρ : Representation k (G ⧸ N) ((homogeneousComplex k G N M).homology j),
    ∀ g : G, ρ (QuotientGroup.mk' N g) =
      (HomologicalComplex.homologyMap (a g).asHom j).hom

/-- All assertions about the action and its descent concern the same action. -/
def ActionAndDescent : Prop := ∀ M : Rep.{max u v w} k G,
  ∃ a : G →* End (homogeneousComplex k G N M),
    ActionFormula k G N M a ∧ Triviality k G N M a ∧ QuotientAction k G N M a

/-- The action on the actual HA-A01 derived invariant functor, via the
naturally identified homogeneous computation. -/
def OrdinaryCohomologyAction : Prop :=
  ∃ e : ∀ j, GroupCochainComparison.Large.repHomogeneousCohomology.{u,v,w} k N j ≅
      GroupCochainComparison.Large.repDerivedCohomology.{u,v,w} k N j,
    ∀ M : Rep.{max u v w} k G,
      ∃ a : G →* End (homogeneousComplex k G N M), ActionFormula k G N M a ∧
      ∀ j : ℕ, ∃ ρ : Representation k (G ⧸ N)
          ((GroupCochainComparison.Large.repDerivedCohomology.{u,v,w} k N j).obj (Rep.res N.subtype M)),
        ∀ (g : G) (x : (homogeneousComplex k G N M).homology j),
          ρ (QuotientGroup.mk' N g) (((e j).hom.app (Rep.res N.subtype M)).hom x) =
            ((e j).hom.app (Rep.res N.subtype M)).hom
              ((HomologicalComplex.homologyMap (a g).asHom j).hom x)

/-- The invariants of any G-injective resolution, retained as an actual
complex of Q-representations. Its homology carries the canonical Q-action. -/
abbrev invariantResolutionComplex (M : Rep.{max u v w} k G) (I : InjectiveResolution M) :
    CochainComplex (Rep.{max u v w} k (G ⧸ N)) ℕ :=
  ((normalInvariants.{u,v,w} k G N).mapHomologicalComplex (.up ℕ)).obj I.cocomplex

/-- Postcomposition on homogeneous cochains by a coefficient homomorphism. -/
def coefficientCochainMap {M L : Rep.{max u v w} k G} (f : M ⟶ L) :
    homogeneousComplex k G N M ⟶ homogeneousComplex k G N L where
  f j := ModuleCat.ofHom
    { toFun φ := φ ≫ Rep.resMap N.subtype f
      map_add' _ _ := by simp only [Preadditive.add_comp]
      map_smul' _ _ := by simp only [RingHom.id_apply, Linear.smul_comp] }
  comm' _ _ _ := by ext φ; rfl

/-- Agreement with every injective-resolution model by a natural family of
Q-linear comparison isomorphisms. Naturality includes every coefficient map
and every compatible map of resolutions; an underlying-module isomorphism
alone does not satisfy this statement. -/
def InjectiveComparison : Prop :=
  ∃ (a : ∀ M : Rep.{max u v w} k G, G →* End (homogeneousComplex k G N M))
    (ρ : ∀ (M : Rep.{max u v w} k G) (j : ℕ),
      Representation k (G ⧸ N) ((homogeneousComplex k G N M).homology j)),
    (∀ M, ActionFormula k G N M (a M) ∧ Triviality k G N M (a M)) ∧
    (∀ (M : Rep.{max u v w} k G) (j : ℕ) (g : G), ρ M j (QuotientGroup.mk' N g) =
      (HomologicalComplex.homologyMap (a M g).asHom j).hom) ∧
    ∃ e : ∀ (M : Rep.{max u v w} k G) (j : ℕ) (I : InjectiveResolution M),
      Rep.of (ρ M j) ≅ (invariantResolutionComplex k G N M I).homology j,
      ∀ (M L : Rep.{max u v w} k G) (f : M ⟶ L) (j : ℕ)
        (I : InjectiveResolution M) (J : InjectiveResolution L)
        (φ : InjectiveResolution.Hom I J f)
        (x : (homogeneousComplex k G N M).homology j),
        (e L j J).hom.hom
            ((HomologicalComplex.homologyMap (coefficientCochainMap k G N f) j).hom x) =
          (HomologicalComplex.homologyMap
            (((normalInvariants.{u,v,w} k G N).mapHomologicalComplex (.up ℕ)).map φ.hom) j).hom
              ((e M j I).hom.hom x)

/-- The complete assigned obligation, without assuming exact induction,
triviality, or a comparison certificate as hypotheses. -/
def FullStatement : Prop :=
  ActionAndDescent.{u,v,w} k G N ∧ OrdinaryCohomologyAction.{u,v,w} k G N ∧ InvariantsAdjunction.{u,v,w} k G N ∧
  RestrictionInjectives.{u,v,w} k G N ∧ InjectiveComparison.{u,v,w} k G N

-- Closed independent types, usable without importing the implementation.
def cochainActionExpected : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G] (N : Subgroup G) [N.Normal],
    CochainAction.{u,v,w} k G N

def invariantsAdjunctionExpected : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G] (N : Subgroup G) [N.Normal],
    InvariantsAdjunction.{u,v,w} k G N

def restrictionInjectivesExpected : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G] (N : Subgroup G) [N.Normal],
    RestrictionInjectives.{u,v,w} k G N

def actionAndDescentExpected : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G] (N : Subgroup G) [N.Normal],
    ActionAndDescent.{u,v,w} k G N

def ordinaryCohomologyActionExpected : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G] (N : Subgroup G) [N.Normal],
    OrdinaryCohomologyAction.{u,v,w} k G N

def injectiveComparisonExpected : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G] (N : Subgroup G) [N.Normal],
    InjectiveComparison.{u,v,w} k G N

def fullStatementExpected : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G] (N : Subgroup G) [N.Normal],
    FullStatement.{u,v,w} k G N

end Specs.AdvancedHomologicalAlgebra.GroupQuotientCohomologyAction
