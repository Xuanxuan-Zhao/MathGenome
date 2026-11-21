import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.SmallChainEquivalence
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.RelativeSingularChains
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.DerivedCategory.KProjective

import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.SmallChainHomology
/-! Conditional draft of the chain homotopy part of the small-chain comparison.
We use the theorem for quasi-isomorphisms of nonnegative projective complexes.
In particular no acyclic-quotient contraction is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
open scoped Simplicial
universe u v w
namespace P202.SmallChainEquivalence
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.SmallChainHomology P202Specs.SmallChainEquivalence

/-- Killing a collection of basis vectors leaves a projective cokernel.
The map of basis indices need not be injective. -/
lemma projective_cokernel_of_basis {R : Type*} [Ring R]
    {A B : ModuleCat.{v} R} {α β : Type*}
    (a : Module.Basis α R A) (b : Module.Basis β R B)
    (f : A ⟶ B) (g : α → β) (hf : ∀ i, f (a i) = b (g i)) :
    Projective (cokernel f) := by
  classical
  let π := cokernel.π f
  have killed (j : β) (hj : ∃ i, g i = j) : π (b j) = 0 := by
    obtain ⟨i, rfl⟩ := hj
    rw [← hf]
    exact cokernel.condition_apply f (a i)
  constructor
  intro E X q e he
  obtain ⟨lift, hlift⟩ := Classical.axiomOfChoice
    (fun j : β => (ModuleCat.epi_iff_surjective e).mp he (q (π (b j))))
  let value : β → E := fun j => if ∃ i, g i = j then 0 else lift j
  let l : B ⟶ E := ModuleCat.ofHom (b.constr ℕ value)
  have fl : f ≫ l = 0 := by
    apply ModuleCat.hom_ext
    apply a.ext
    intro i
    change l (f (a i)) = 0
    rw [hf]
    simp [l, value]
  refine ⟨cokernel.desc f l fl, ?_⟩
  apply (cancel_epi π).mp
  dsimp only [π]
  rw [← Category.assoc, cokernel.π_desc]
  apply ModuleCat.hom_ext
  apply b.ext
  intro j
  change e (l (b j)) = q (π (b j))
  by_cases hj : ∃ i, g i = j
  · simp [l, value, hj, killed j hj]
  · simpa [l, value, hj] using hlift j

variable (R : Type u) [CommRing R] {X : TopCat.{v}} {ι : Type w}

abbrev SmallSimplex (U : OpenCover X ι) (n : ℕ) :=
  {s : Simplex X n // ∃ i, Set.range (simplexEquiv X n s) ⊆ U.sets i}

/-- The small complex is free on precisely the small simplex generators. -/
def smallBasis (U : OpenCover X ι) (n : ℕ) :
    Module.Basis (SmallSimplex U n) R ((smallComplex R U).X n) :=
  Finsupp.basisSingleOne.map (Finsupp.supportedEquivFinsupp _).symm

lemma smallBasis_coe (U : OpenCover X ι) (n : ℕ) (s : SmallSimplex U n) :
    ((smallBasis R U n s).val : Chains R X n) = Finsupp.single s.val 1 := by
  classical
  exact Finsupp.supportedEquivFinsupp_symm_single _ s 1

instance small_projective (U : OpenCover X ι) (n : ℕ) :
    Projective ((smallComplex R U).X n) :=
  ModuleCat.projective_of_free (smallBasis R U n)

instance singular_projective (n : ℕ) : Projective ((complex R R X).X n) :=
  ModuleCat.projective_of_free Finsupp.basisSingleOne

/-- The subspace inclusion takes each small simplex basis vector to a small
simplex basis vector. This also respects the discarded empty intersections. -/
def smallSimplexInclusion (U : OpenCover X ι) (A : Set X) (n : ℕ) :
    SmallSimplex (restrictedCover U A) n → SmallSimplex U n := by
  intro s
  refine ⟨(TopCat.toSSet.map (Pair.inclusion ⟨X, A⟩)).app (op ⦋n⦌) s.val, ?_⟩
  obtain ⟨i, hi⟩ := s.property
  refine ⟨i.val, ?_⟩
  rintro y ⟨x, rfl⟩
  exact hi ⟨x, rfl⟩

lemma smallSubspace_basis (U : OpenCover X ι) (A : Set X) (n : ℕ)
    (s : SmallSimplex (restrictedCover U A) n) :
    (smallSubspaceInclusion R U A).f n (smallBasis R (restrictedCover U A) n s) =
      smallBasis R U n (smallSimplexInclusion U A n s) := by
  apply Subtype.ext
  change Finsupp.mapDomain _ (smallBasis R (restrictedCover U A) n s).val = _
  rw [smallBasis_coe, smallBasis_coe]
  exact Finsupp.mapDomain_single

instance smallRelative_projective (U : OpenCover X ι) (A : Set X) (n : ℕ) :
    Projective ((smallRelativeComplex R U A).X n) := by
  have h := projective_cokernel_of_basis (smallBasis R (restrictedCover U A) n)
    (smallBasis R U n) ((smallSubspaceInclusion R U A).f n)
    (smallSimplexInclusion U A n) (smallSubspace_basis R U A n)
  exact Projective.of_iso
    (PreservesCokernel.iso (HomologicalComplex.eval (ModuleCat R) _ n)
      (smallSubspaceInclusion R U A)).symm h

instance relative_projective (A : Set X) (n : ℕ) :
    Projective ((nonnegative R R ⟨X, A⟩).X n) := by
  obtain ⟨b, _⟩ := P202.RelativeSingularChains.quotient_basis R ⟨X, A⟩ n
  exact ModuleCat.projective_of_free b

theorem absoluteEquivalence_conditional
    (habs : absoluteComparison_type.{u,v,w})
    (_hgen : comparison_from_generators_type.{u,v,w})
    (_hrel : relativeComparison_type.{u,v,w}) : absoluteEquivalence_type.{u,v,w} := by
  intro R _ X ι U
  refine ⟨?_, habs R X ι U⟩
  apply (ChainComplex.quasiIso_iff_of_projective (smallInclusion R U)).mp
  rw [quasiIso_iff]
  intro n
  exact (quasiIsoAt_iff_isIso_homologyMap _ _).mpr (habs R X ι U n)

theorem relativeEquivalence_conditional
    (_habs : absoluteComparison_type.{u,v,w})
    (_hgen : comparison_from_generators_type.{u,v,w})
    (hrel : relativeComparison_type.{u,v,w}) : relativeEquivalence_type.{u,v,w} := by
  intro R _ X ι U A
  refine ⟨?_, hrel R X ι U A⟩
  apply (ChainComplex.quasiIso_iff_of_projective (smallRelativeInclusion R U A)).mp
  rw [quasiIso_iff]
  intro n
  exact (quasiIsoAt_iff_isIso_homologyMap _ _).mpr (hrel R X ι U A n)

theorem absoluteNaturality_conditional
    (_habs : absoluteComparison_type.{u,v,w})
    (_hgen : comparison_from_generators_type.{u,v,w})
    (_hrel : relativeComparison_type.{u,v,w}) : absoluteNaturality_type.{u,v,w} := by
  intro R _ X Y ι κ U V f hf n
  rw [← homologyMap_comp, ← homologyMap_comp, mapSmall_square]

lemma mapSmallRelative_square {P Q : Pair.{v}} {ι κ : Type w}
    (U : OpenCover P.space ι) (V : OpenCover Q.space κ) (f : P ⟶ Q)
    (hf : CoverCompatible U V f.map) :
    mapSmallRelative R U V f hf ≫ smallRelativeInclusion R V Q.subspace =
      smallRelativeInclusion R U P.subspace ≫ relativeMap (chainFunctor R R) f := by
  apply (cancel_epi (cokernel.π (smallSubspaceInclusion R U P.subspace))).mp
  simp only [mapSmallRelative, smallRelativeInclusion, relativeMap, cokernel.map,
    Category.assoc, cokernel.π_desc_assoc, cokernel.π_desc]
  rw [← Category.assoc, mapSmall_square]
  simp only [Category.assoc]

theorem relativeNaturality_conditional
    (_habs : absoluteComparison_type.{u,v,w})
    (_hgen : comparison_from_generators_type.{u,v,w})
    (_hrel : relativeComparison_type.{u,v,w}) : relativeNaturality_type.{u,v,w} := by
  intro R _ P Q ι κ U V f hf n
  rw [← homologyMap_comp, ← homologyMap_comp, mapSmallRelative_square]

end P202.SmallChainEquivalence

universe v8_closure_c37b785c4126bfbe_u0 v8_closure_c37b785c4126bfbe_u1 v8_closure_c37b785c4126bfbe_u2
theorem _root_.«P202».«SmallChainEquivalence».«absoluteEquivalence» : _root_.«P202Specs».«SmallChainEquivalence».«absoluteEquivalence_type».{v8_closure_c37b785c4126bfbe_u0, v8_closure_c37b785c4126bfbe_u1, v8_closure_c37b785c4126bfbe_u2} :=
  @_root_.«P202».«SmallChainEquivalence».«absoluteEquivalence_conditional».{v8_closure_c37b785c4126bfbe_u0, v8_closure_c37b785c4126bfbe_u1, v8_closure_c37b785c4126bfbe_u2} (@_root_.«P202».«SmallChainHomology».«absoluteComparison».{v8_closure_c37b785c4126bfbe_u0, v8_closure_c37b785c4126bfbe_u1, v8_closure_c37b785c4126bfbe_u2}) (@_root_.«P202».«SmallChainHomology».«comparison_from_generators».{v8_closure_c37b785c4126bfbe_u0, v8_closure_c37b785c4126bfbe_u1, v8_closure_c37b785c4126bfbe_u2}) (@_root_.«P202».«SmallChainHomology».«relativeComparison».{v8_closure_c37b785c4126bfbe_u0, v8_closure_c37b785c4126bfbe_u1, v8_closure_c37b785c4126bfbe_u2})
theorem _root_.«P202».«SmallChainEquivalence».«absoluteNaturality» : _root_.«P202Specs».«SmallChainEquivalence».«absoluteNaturality_type».{v8_closure_c37b785c4126bfbe_u0, v8_closure_c37b785c4126bfbe_u1, v8_closure_c37b785c4126bfbe_u2} :=
  @_root_.«P202».«SmallChainEquivalence».«absoluteNaturality_conditional».{v8_closure_c37b785c4126bfbe_u0, v8_closure_c37b785c4126bfbe_u1, v8_closure_c37b785c4126bfbe_u2} (@_root_.«P202».«SmallChainHomology».«absoluteComparison».{v8_closure_c37b785c4126bfbe_u0, v8_closure_c37b785c4126bfbe_u1, v8_closure_c37b785c4126bfbe_u2}) (@_root_.«P202».«SmallChainHomology».«comparison_from_generators».{v8_closure_c37b785c4126bfbe_u0, v8_closure_c37b785c4126bfbe_u1, v8_closure_c37b785c4126bfbe_u2}) (@_root_.«P202».«SmallChainHomology».«relativeComparison».{v8_closure_c37b785c4126bfbe_u0, v8_closure_c37b785c4126bfbe_u1, v8_closure_c37b785c4126bfbe_u2})
theorem _root_.«P202».«SmallChainEquivalence».«relativeEquivalence» : _root_.«P202Specs».«SmallChainEquivalence».«relativeEquivalence_type».{v8_closure_c37b785c4126bfbe_u0, v8_closure_c37b785c4126bfbe_u1, v8_closure_c37b785c4126bfbe_u2} :=
  @_root_.«P202».«SmallChainEquivalence».«relativeEquivalence_conditional».{v8_closure_c37b785c4126bfbe_u0, v8_closure_c37b785c4126bfbe_u1, v8_closure_c37b785c4126bfbe_u2} (@_root_.«P202».«SmallChainHomology».«absoluteComparison».{v8_closure_c37b785c4126bfbe_u0, v8_closure_c37b785c4126bfbe_u1, v8_closure_c37b785c4126bfbe_u2}) (@_root_.«P202».«SmallChainHomology».«comparison_from_generators».{v8_closure_c37b785c4126bfbe_u0, v8_closure_c37b785c4126bfbe_u1, v8_closure_c37b785c4126bfbe_u2}) (@_root_.«P202».«SmallChainHomology».«relativeComparison».{v8_closure_c37b785c4126bfbe_u0, v8_closure_c37b785c4126bfbe_u1, v8_closure_c37b785c4126bfbe_u2})
theorem _root_.«P202».«SmallChainEquivalence».«relativeNaturality» : _root_.«P202Specs».«SmallChainEquivalence».«relativeNaturality_type».{v8_closure_c37b785c4126bfbe_u0, v8_closure_c37b785c4126bfbe_u1, v8_closure_c37b785c4126bfbe_u2} :=
  @_root_.«P202».«SmallChainEquivalence».«relativeNaturality_conditional».{v8_closure_c37b785c4126bfbe_u0, v8_closure_c37b785c4126bfbe_u1, v8_closure_c37b785c4126bfbe_u2} (@_root_.«P202».«SmallChainHomology».«absoluteComparison».{v8_closure_c37b785c4126bfbe_u0, v8_closure_c37b785c4126bfbe_u1, v8_closure_c37b785c4126bfbe_u2}) (@_root_.«P202».«SmallChainHomology».«comparison_from_generators».{v8_closure_c37b785c4126bfbe_u0, v8_closure_c37b785c4126bfbe_u1, v8_closure_c37b785c4126bfbe_u2}) (@_root_.«P202».«SmallChainHomology».«relativeComparison».{v8_closure_c37b785c4126bfbe_u0, v8_closure_c37b785c4126bfbe_u1, v8_closure_c37b785c4126bfbe_u2})
