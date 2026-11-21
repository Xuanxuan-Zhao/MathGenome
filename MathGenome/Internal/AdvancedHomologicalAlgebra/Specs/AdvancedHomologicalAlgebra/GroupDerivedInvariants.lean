import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.UniversalDeltaFunctors
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.ExtShiftedHom
import Mathlib.RepresentationTheory.Basic
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Linear.Yoneda

/-! HA-A01, source lines 2866–2898. All modules are left modules over k[G].
The trivial module is k with its augmentation action, realized by the trivial
representation. No finiteness or characteristic assumptions are used. -/
noncomputable section
set_option linter.checkUnivs false
universe u uG v
open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra ModuleCat.Algebra

namespace Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants

variable (k : Type u) (G : Type uG) [CommRing k] [Group G]

abbrev GroupModule := ModuleCat.{max u uG v} k[G]

/-- k with the augmentation action. -/
def trivialModule : GroupModule.{u,uG,v} k G :=
  ModuleCat.of k[G] (Representation.trivial k G (ULift.{max uG v} k)).asModule

/-- The scalar a as an element of the trivial module (with universe lift). -/
def trivialElement (a : k) : trivialModule.{u,uG,v} k G :=
  (Representation.trivial k G (ULift.{max uG v} k)).asModuleEquiv.symm (ULift.up a)

/-- Fixed elements under every group element, as an actual k-submodule of M. -/
def invariants (M : GroupModule.{u,uG,v} k G) : Submodule k M where
  carrier := {m | ∀ g : G, MonoidAlgebra.single g (1 : k) • m = m}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy g; simp [smul_add, hx g, hy g]
  smul_mem' := by intro a x hx g; rw [smul_comm, hx g]

def invariantsFunctor : GroupModule.{u,uG,v} k G ⥤ ModuleCat.{max u uG v} k where
  obj M := ModuleCat.of k (invariants k G M)
  map {M N} f := ModuleCat.ofHom
    { toFun m := ⟨f.hom m, fun g => by rw [← f.hom.map_smul, m.property g]⟩
      map_add' := by intros; apply Subtype.ext; exact f.hom.map_add _ _
      map_smul' := by intros; apply Subtype.ext; exact f.hom.map_smul_of_tower _ _ }

instance : (invariantsFunctor.{u,uG,v} k G).Additive where

def homFunctor : GroupModule.{u,uG,v} k G ⥤ ModuleCat.{max u uG v} k :=
  (linearCoyoneda k (GroupModule k G)).obj (Opposite.op (trivialModule k G))

/-- These choices exist for every module category; they impose no hypothesis
on the ring, group, or coefficient module. -/
local instance canonicalDerived (A : Type*) [Category A] [Abelian A] :
    HasDerivedCategory A := HasDerivedCategory.standard A

/-- H^n(G,-) means the actual right derived invariants functor of HA-R09. -/
def cohomology (n : ℕ) : GroupModule.{u,uG,v} k G ⥤ ModuleCat.{max u uG v} k :=
  ClassicalDerivedValues.rightValue (invariantsFunctor k G) n

abbrev groupExt (M : GroupModule.{u,uG,v} k G) (n : ℕ) :=
  ExtShiftedHom.Ext (trivialModule k G) M (n : ℤ)

/-- Evaluation at the element 1 of k, not merely an abstract equivalence. -/
def evaluationType :=
  ∀ (k : Type u) (G : Type uG) [CommRing k] [Group G],
    ∃ e : homFunctor.{u,uG,v} k G ≅ invariantsFunctor k G,
      ∀ (M : GroupModule k G) (f : trivialModule k G ⟶ M),
        ((e.hom.app M).hom f).val = f.hom (trivialElement k G 1)

/-- The invariants functor is left exact over every commutative ring. -/
def leftExactType : Prop :=
  ∀ (k : Type u) (G : Type uG) [CommRing k] [Group G],
    PreservesFiniteLimits (invariantsFunctor.{u,uG,v} k G)

def degreeZeroType : Prop :=
  ∀ (k : Type u) (G : Type uG) [CommRing k] [Group G],
    Nonempty (cohomology.{u,uG,v} k G 0 ≅ invariantsFunctor k G)

def derivedExtType : Prop :=
  ∀ (k : Type u) (G : Type uG) [CommRing k] [Group G] (M : GroupModule.{u,uG,v} k G) (n : ℕ),
    Nonempty (((cohomology k G n).obj M) ≃+ groupExt k G M n)

/-- Every injective resolution of M computes the actual derived invariants. -/
def injectiveComputationType : Prop :=
  ∀ (k : Type u) (G : Type uG) [CommRing k] [Group G] (M : GroupModule.{u,uG,v} k G)
    (I : CochainComplex (GroupModule k G) ℤ) [I.IsStrictlyGE 0]
    (i : (CochainComplex.singleFunctor _ 0).obj M ⟶ I),
    QuasiIso i → (∀ q : ℤ, Injective (I.X q)) → ∀ n : ℕ,
      Nonempty ((cohomology k G n).obj M ≅
        (((invariantsFunctor k G).mapHomologicalComplex (.up ℤ)).obj I).homology (n : ℤ))

/-- The usual Hom cochain complex of any bounded-above projective resolution
of the trivial module computes H^n. Its coordinates and differential are
those of HA-R11, so this is a computation by the supplied resolution. -/
def projectiveComputationType : Prop :=
  ∀ (k : Type u) (G : Type uG) [CommRing k] [Group G] (M : GroupModule.{u,uG,v} k G)
    (P : CochainComplex (GroupModule k G) ℤ) [P.IsStrictlyLE 0]
    (p : P ⟶ (CochainComplex.singleFunctor _ 0).obj (trivialModule k G)),
    QuasiIso p → (∀ q : ℤ, Projective (P.X q)) → ∀ n : ℕ,
      Nonempty (((cohomology k G n).obj M) ≃+
        (CochainComplex.HomComplex P ((CochainComplex.singleFunctor _ 0).obj M)).homology
          (n : ℤ))

end Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants
