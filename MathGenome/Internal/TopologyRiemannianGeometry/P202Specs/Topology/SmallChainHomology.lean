import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.SingularSubdivision
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.RelativeSingularChains
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.Algebra.Homology.QuasiIso

/-! Small singular chains, paper.tex 1211–1217 and 1264–1293.
The complexes are indexed by the nonnegative integers, with zero outgoing
boundary in degree zero, exactly as `SingularChains.complex`.
A restricted cover has only the indices with nonempty intersection.
No local finiteness, separation, nonemptiness or coefficient-field assumption
is part of these definitions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
open scoped Simplicial
universe u v w
namespace P202Specs.SmallChainHomology
open P202Specs.SingularChains P202Specs.SingularSubdivision
open P202Specs.RelativeSingularChains

structure OpenCover (X : TopCat.{v}) (ι : Type w) where
  sets : ι → Set X
  isOpen : ∀ i, IsOpen (sets i)
  covers : ∀ x, ∃ i, x ∈ sets i

variable {X : TopCat.{v}} {ι : Type w}

/-- Only cover members meeting the subspace are retained. -/
def restrictedIndex (U : OpenCover X ι) (A : Set X) :=
  {i : ι // ((Subtype.val : A → X) ⁻¹' U.sets i).Nonempty}

def restrictedCover (U : OpenCover X ι) (A : Set X) :
    OpenCover (TopCat.of A) (restrictedIndex U A) where
  sets i := Subtype.val ⁻¹' U.sets i.val
  isOpen i := (U.isOpen i.val).preimage continuous_subtype_val
  covers x := by
    obtain ⟨i, hi⟩ := U.covers x.val
    exact ⟨⟨i, x, hi⟩, hi⟩

variable (R : Type u) [CommRing R]

/-- This is the span of the subset of the singular simplex basis selected by
smallness, equivalently finite chains all of whose nonzero terms are small. -/
def smallModule (U : OpenCover X ι) (n : ℕ) : Submodule R (Chains R X n) :=
  Finsupp.supported R R {s | ∃ i, Set.range (simplexEquiv X n s) ⊆ U.sets i}

@[simp] lemma mem_smallModule (U : OpenCover X ι) (n : ℕ) (c : Chains R X n) :
    c ∈ smallModule R U n ↔ IsSmall U.sets c := Iff.rfl

lemma boundary_mem_smallModule (U : OpenCover X ι) (n : ℕ)
    (c : Chains R X (n+1)) (hc : c ∈ smallModule R U (n+1)) :
    boundary R R X n c ∈ smallModule R U n := by
  classical
  change ((AlgebraicTopology.AlternatingFaceMapComplex.obj
    (simplicialChains R R X)).d (n+1) n).hom c ∈ _
  rw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq]
  simp only [ModuleCat.hom_sum, ModuleCat.hom_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  change (∑ i : Fin (n+2), (-1 : ℤ)^i.val •
    Finsupp.mapDomain ((TopCat.toSSet.obj X).δ i) c) ∈ smallModule R U n
  apply Submodule.sum_mem
  intro i _
  apply (smallModule R U n).toAddSubgroup.zsmul_mem
  intro q hq
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hq)
  obtain ⟨j, hj⟩ := (mem_smallModule R U (n+1) c).mp hc s hs
  refine ⟨j, ?_⟩
  rintro y ⟨x, rfl⟩
  exact hj ⟨faceInclusion i x, rfl⟩

/-- Ordinary small chains with the differential restricted from singular chains. -/
def smallComplex (U : OpenCover X ι) : ChainComplex (ModuleCat.{max u v} R) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of R (smallModule R U n))
    (fun n => ModuleCat.ofHom (((boundary R R X n).comp
      (smallModule R U (n+1)).subtype).codRestrict (smallModule R U n)
        (fun c => boundary_mem_smallModule R U n c.val c.property)))
    (by
      intro n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      apply Subtype.ext
      exact congrArg (fun f => f c.val) ((complex R R X).d_comp_d (n+2) (n+1) n))

def smallInclusion (U : OpenCover X ι) : smallComplex R U ⟶ complex R R X :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (smallModule R U n).subtype)
    (by intro n; simp only [smallComplex, ChainComplex.of_d]; rfl)

/-- Map on small chains for the inclusion of an arbitrary subspace. -/
def smallSubspaceInclusion (U : OpenCover X ι) (A : Set X) :
    smallComplex R (restrictedCover U A) ⟶ smallComplex R U := by
  classical
  let P : Pair := ⟨X, A⟩
  exact ChainComplex.ofHom
    (fun n => ModuleCat.ofHom ((((chainMap R R P.inclusion).f n).hom.comp
      (smallModule R (restrictedCover U A) n).subtype).codRestrict (smallModule R U n)
        (by
          intro c q hq
          change q ∈ (Finsupp.mapDomain _ c.val).support at hq
          obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hq)
          obtain ⟨i, hi⟩ := (mem_smallModule R (restrictedCover U A) n c.val).mp c.property s hs
          refine ⟨i.val, ?_⟩
          rintro y ⟨x, rfl⟩
          exact hi ⟨x, rfl⟩)))
    (by
      intro n
      simp only [smallComplex, ChainComplex.of_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      apply Subtype.ext
      exact congrArg (fun f => f c.val) ((chainMap R R P.inclusion).comm (n+1) n))

lemma smallSubspace_square (U : OpenCover X ι) (A : Set X) :
    smallSubspaceInclusion R U A ≫ smallInclusion R U =
      smallInclusion R (restrictedCover U A) ≫
        chainMap R R (Pair.inclusion ⟨X, A⟩) := by
  ext n c
  rfl

/-- The relative small complex is the quotient by restricted-cover small chains
in A; it is not the quotient by all chains in A. -/
def smallRelativeComplex (U : OpenCover X ι) (A : Set X) :=
  cokernel (smallSubspaceInclusion R U A)

def smallRelativeInclusion (U : OpenCover X ι) (A : Set X) :
    smallRelativeComplex R U A ⟶ nonnegative R R ⟨X, A⟩ :=
  cokernel.map _ _ (smallInclusion R (restrictedCover U A)) (smallInclusion R U)
    (smallSubspace_square R U A)

/-- Absolute comparison, for every open cover, ring and nonnegative degree. -/
def absoluteComparison_type : Prop :=
  ∀ (R : Type u) [CommRing R] (X : TopCat.{v}) (ι : Type w)
    (U : OpenCover X ι) (n : ℕ), IsIso (homologyMap (smallInclusion R U) n)

/-- Relative comparison for arbitrary subspaces with their subspace topology. -/
def relativeComparison_type : Prop :=
  ∀ (R : Type u) [CommRing R] (X : TopCat.{v}) (ι : Type w)
    (U : OpenCover X ι) (A : Set X) (n : ℕ),
      IsIso (homologyMap (smallRelativeInclusion R U A) n)

/-- Geometric intermediate obligation, expressed in terms of the concrete
upstream subdivision operator and unit-coefficient simplex generators.
The final comparison statements above do not assume this proposition. -/
def generatorSmall_type : Prop :=
  ∀ (R : Type u) [CommRing R] (X : TopCat.{v}) (ι : Type w)
    (U : ι → Set X), (∀ i, IsOpen (U i)) → (∀ x, ∃ i, x ∈ U i) →
    ∀ (n : ℕ) (s : Simplex X n), ∃ m : ℕ,
      IsSmall U (((subdivision R X n)^m) (Finsupp.single s 1))

/-- A conditional assembly lemma, not the final unconditional comparison. -/
def comparison_from_generators_type : Prop :=
  generatorSmall_type.{u,v,w} →
    absoluteComparison_type.{u,v,w} ∧ relativeComparison_type.{u,v,w}

end P202Specs.SmallChainHomology
