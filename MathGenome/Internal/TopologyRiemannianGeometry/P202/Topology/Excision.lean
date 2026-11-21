import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.Excision
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.SmallChainEquivalence
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.RelativeSingularChains

import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.SmallChainEquivalence
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
open scoped Simplicial
universe u v w
namespace P202.Excision
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.SmallChainHomology P202Specs.SmallChainEquivalence
open P202Specs.Excision

/-- A small chain supported in a subspace lifts to small chains of that subspace.
The restricted cover discards empty intersections, as in the frozen interface. -/
lemma lift_small_subspace (R : Type u) [CommRing R] {X : TopCat.{v}}
    {ι : Type w} (U : OpenCover X ι) (A : Set X) (n : ℕ)
    (c : smallModule R U n)
    (hc : ∀ s ∈ c.val.support, InSubspace ⟨X, A⟩ n s) :
    ∃ d : smallModule R (restrictedCover U A) n,
      (smallSubspaceInclusion R U A).f n d = c := by
  classical
  let P : Pair := ⟨X, A⟩
  have hr : c.val ∈ Set.range
      (Finsupp.mapDomain ((TopCat.toSSet.map P.inclusion).app (op ⦋n⦌))) := by
    rw [Finsupp.mem_range_mapDomain_iff _
      (P202.RelativeSingularChains.simplex_injective P n)]
    intro s hs
    apply Finsupp.notMem_support_iff.mp
    intro h
    exact hs ((P202.RelativeSingularChains.simplex_image P n s).mpr (hc s h))
  obtain ⟨d, hd⟩ := hr
  have hdsmall : d ∈ smallModule R (restrictedCover U A) n := by
    intro t ht
    have him : ((TopCat.toSSet.map P.inclusion).app (op ⦋n⦌) t) ∈ c.val.support := by
      rw [← hd, Finsupp.mapDomain_support_of_injective
        (P202.RelativeSingularChains.simplex_injective P n)]
      exact Finset.mem_image.mpr ⟨t, ht, rfl⟩
    obtain ⟨i, hi⟩ := (mem_smallModule R U n c.val).mp c.property _ him
    let x := simplexEquiv P.sub n t (Convexity.StdSimplex.single (0 : Fin (n+1)))
    have hx : x.val ∈ U.sets i := hi ⟨_, rfl⟩
    refine ⟨⟨i, x, hx⟩, ?_⟩
    rintro y ⟨z, rfl⟩
    exact hi ⟨z, rfl⟩
  refine ⟨⟨d, hdsmall⟩, ?_⟩
  apply Subtype.ext
  exact hd

lemma small_subspace_support (R : Type u) [CommRing R] {X : TopCat.{v}}
    {ι : Type w} (U : OpenCover X ι) (A : Set X) (n : ℕ)
    (d : smallModule R (restrictedCover U A) n) :
    ∀ s ∈ ((smallSubspaceInclusion R U A).f n d).val.support,
      InSubspace ⟨X, A⟩ n s := by
  classical
  intro s hs
  change s ∈ (Finsupp.mapDomain _ d.val).support at hs
  obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hs)
  intro x
  exact (simplexEquiv (TopCat.of A) n t x).property

lemma subspace_cover_compatible {X : TopCat.{v}} {ι : Type w}
    (U : OpenCover X ι) (A : Set X) :
    CoverCompatible (restrictedCover U A) U (Pair.inclusion ⟨X, A⟩) := by
  intro i
  exact ⟨i.val, fun _ h => h⟩

lemma mapSmall_subspace {X : TopCat.{v}} {ι : Type w}
    (R : Type u) [CommRing R] (U : OpenCover X ι) (A : Set X) :
    mapSmall R (restrictedCover U A) U (Pair.inclusion ⟨X, A⟩)
      (subspace_cover_compatible U A) = smallSubspaceInclusion R U A := by
  ext n c
  rfl

/-- Pulling an ambient support condition back across a subspace inclusion. -/
lemma small_subspace_reflect (R : Type u) [CommRing R] {X : TopCat.{v}}
    {ι : Type w} (U : OpenCover X ι) (B A : Set X) (n : ℕ)
    (c : smallModule R (restrictedCover U B) n)
    (hc : ∀ s ∈ ((smallSubspaceInclusion R U B).f n c).val.support,
      InSubspace ⟨X, A⟩ n s) :
    ∀ s ∈ c.val.support,
      InSubspace ⟨TopCat.of B, Subtype.val ⁻¹' A⟩ n s := by
  classical
  intro s hs x
  have him : ((TopCat.toSSet.map (Pair.inclusion ⟨X, B⟩)).app (op ⦋n⦌) s) ∈
      ((smallSubspaceInclusion R U B).f n c).val.support := by
    change _ ∈ (Finsupp.mapDomain _ c.val).support
    rw [Finsupp.mapDomain_support_of_injective
      (P202.RelativeSingularChains.simplex_injective ⟨X, B⟩ n)]
    exact Finset.mem_image.mpr ⟨s, hs, rfl⟩
  exact hc _ him x

/-- The elementary quotient criterion used below. It proves both injectivity
and surjectivity of the actual induced cokernel map. -/
lemma cokernel_map_iso {R : Type u} [CommRing R]
    {A B K L : ModuleCat.{v} R} (i : A ⟶ K) (j : B ⟶ L)
    (a : A ⟶ B) (f : K ⟶ L) (sq : i ≫ f = a ≫ j)
    (hpre : ∀ x y, f x = j y → ∃ z, i z = x)
    (hgen : ∀ y, ∃ x z, f x + j z = y) :
    IsIso (cokernel.map i j a f sq) := by
  let q := cokernel.map i j a f sq
  have exj := (ShortComplex.moduleCat_exact_iff _).mp
    (ShortComplex.cokernelSequence_exact j)
  have πi := (ModuleCat.epi_iff_surjective (cokernel.π i)).mp inferInstance
  have πj := (ModuleCat.epi_iff_surjective (cokernel.π j)).mp inferInstance
  have comm (x : K) : q (cokernel.π i x) = cokernel.π j (f x) :=
    congrArg (fun k : K ⟶ cokernel j => k x) (cokernel.π_desc i _ _)
  apply (ConcreteCategory.isIso_iff_bijective q).mpr
  constructor
  · apply (injective_iff_map_eq_zero q.hom).mpr
    intro x hx
    obtain ⟨c, rfl⟩ := πi x
    rw [comm] at hx
    obtain ⟨b, hb⟩ := exj (f c) hx
    obtain ⟨a, ha⟩ := hpre c b hb.symm
    rw [← ha]
    exact congrArg (fun k : A ⟶ cokernel i => k a) (cokernel.condition i)
  · intro y
    obtain ⟨c, rfl⟩ := πj y
    obtain ⟨x, z, h⟩ := hgen c
    refine ⟨cokernel.π i x, ?_⟩
    rw [comm, ← h, map_add]
    have hz : cokernel.π j (j z) = 0 :=
      congrArg (fun k : B ⟶ cokernel j => k z) (cokernel.condition j)
    rw [hz, add_zero]

/-- Degreewise cokernel comparison, without making a noncanonical chain inverse. -/
lemma complex_cokernel_map_iso {R : Type u} [CommRing R]
    {A B K L : ChainComplex (ModuleCat.{v} R) ℕ}
    (i : A ⟶ K) (j : B ⟶ L) (a : A ⟶ B) (f : K ⟶ L)
    (sq : i ≫ f = a ≫ j)
    (hpre : ∀ n x y, f.f n x = j.f n y → ∃ z, i.f n z = x)
    (hgen : ∀ n y, ∃ x z, f.f n x + j.f n z = y) :
    IsIso (cokernel.map i j a f sq) := by
  haveI : ∀ n, IsIso ((cokernel.map i j a f sq).f n) := by
    intro n
    let G := HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ) n
    have sqn : i.f n ≫ f.f n = a.f n ≫ j.f n := congrArg (fun k => k.f n) sq
    haveI := cokernel_map_iso (i.f n) (j.f n) (a.f n) (f.f n)
      sqn (hpre n) (hgen n)
    have h := preserves_cokernel_iso_comp_cokernel_map G i j a f sq
    have he : (cokernel.map i j a f sq).f n =
        ((PreservesCokernel.iso G i).hom ≫
          cokernel.map (i.f n) (j.f n) (a.f n) (f.f n)
            sqn) ≫ (PreservesCokernel.iso G j).inv := by
      apply (Iso.eq_comp_inv (PreservesCokernel.iso G j)).mpr
      exact h.symm
    rw [he]
    infer_instance
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The open cover used in the original proof. -/
def excisionCover (D : Data.{v}) : OpenCover D.pair.space (ULift.{w} Bool) where
  sets i := if i.down then interior D.pair.subspace else (closure D.removed)ᶜ
  isOpen i := by
    rcases i with ⟨b⟩
    cases b
    · exact isClosed_closure.isOpen_compl
    · exact isOpen_interior
  covers x := by
    by_cases hx : x ∈ closure D.removed
    · exact ⟨⟨true⟩, D.closure_subset hx⟩
    · exact ⟨⟨false⟩, hx⟩

lemma excisionCover_alternative (D : Data.{v}) (n : ℕ)
    (s : Simplex D.pair.space n)
    (hs : ∃ i, Set.range (simplexEquiv D.pair.space n s) ⊆
      (excisionCover.{v,w} D).sets i) :
    InSubspace ⟨D.pair.space, D.removedᶜ⟩ n s ∨ InSubspace D.pair n s := by
  obtain ⟨⟨b⟩, hb⟩ := hs
  cases b with
  | false =>
    left
    intro x hx
    exact hb ⟨x, rfl⟩ (subset_closure hx)
  | true =>
    right
    intro x
    exact interior_subset (hb ⟨x, rfl⟩)

/-- The inclusion identifies the two small relative quotients degree by degree. -/
lemma small_excision_iso (R : Type u) [CommRing R] (D : Data.{v}) :
    IsIso (mapSmallRelative R
      (restrictedCover (excisionCover.{v,w} D) D.removedᶜ)
      (excisionCover.{v,w} D) D.inclusion
      (subspace_cover_compatible (excisionCover D) D.removedᶜ)) := by
  classical
  let U := excisionCover.{v,w} D
  let B := D.removedᶜ
  unfold mapSmallRelative
  apply complex_cokernel_map_iso
  · intro n c d h
    have h' : (smallSubspaceInclusion R U B).f n c =
        (smallSubspaceInclusion R U D.pair.subspace).f n d := by
      exact h
    have hc : ∀ s ∈ ((smallSubspaceInclusion R U B).f n c).val.support,
        InSubspace D.pair n s := by
      rw [h']
      exact small_subspace_support R U D.pair.subspace n d
    exact lift_small_subspace R (restrictedCover U B) D.excised.subspace n c
      (small_subspace_reflect R U B D.pair.subspace n c hc)
  · intro n c
    let p := InSubspace ⟨D.pair.space, B⟩ n
    let cB : smallModule R U n := ⟨c.val.filter p, by
      intro s hs
      exact c.property (Finset.mem_filter.mp hs).1⟩
    let cA : smallModule R U n := ⟨c.val.filter (fun s => ¬ p s), by
      intro s hs
      exact c.property (Finset.mem_filter.mp hs).1⟩
    obtain ⟨x, hx⟩ := lift_small_subspace R U B n cB (by
      intro s hs
      exact (Finset.mem_filter.mp hs).2)
    obtain ⟨z, hz⟩ := lift_small_subspace R U D.pair.subspace n cA (by
      intro s hs
      have hs' := Finset.mem_filter.mp hs
      have hsmall := (mem_smallModule R U n c.val).mp c.property s hs'.1
      exact (excisionCover_alternative D n s hsmall).resolve_left hs'.2)
    refine ⟨x, z, ?_⟩
    change (smallSubspaceInclusion R U B).f n x +
      (smallSubspaceInclusion R U D.pair.subspace).f n z = c
    rw [hx, hz]
    apply Subtype.ext
    exact Finsupp.filter_add_filter_not c.val p

/-- Conditional excision: the four ordered premises are exactly the frozen
small-chain interface. Only its relative comparison and naturality are needed. -/
theorem isomorphism_conditional
    (_absolute : absoluteEquivalence_type.{u,v,w})
    (_absoluteNatural : absoluteNaturality_type.{u,v,w})
    (relative : relativeEquivalence_type.{u,v,w})
    (relativeNatural : relativeNaturality_type.{u,v,w}) :
    isomorphism_type.{u,v} := by
  intro R _ D n
  let U := excisionCover.{v,w} D
  let V := restrictedCover U D.removedᶜ
  let hf := subspace_cover_compatible U D.removedᶜ
  haveI := (relative R D.pair.space _ U D.pair.subspace).2 n
  haveI := (relative R D.excised.space _ V D.excised.subspace).2 n
  haveI := small_excision_iso.{u,v,w} R D
  have hn := relativeNatural R D.excised D.pair _ _ V U D.inclusion hf n
  haveI : IsIso (homologyMap (smallRelativeInclusion R V D.excised.subspace) n ≫
      homologyMap (relativeMap (chainFunctor R R) D.inclusion) n) := by
    rw [← hn]
    infer_instance
  exact IsIso.of_isIso_comp_left
    (homologyMap (smallRelativeInclusion R V D.excised.subspace) n) _

theorem naturality_conditional
    (_absolute : absoluteEquivalence_type.{u,v,w})
    (_absoluteNatural : absoluteNaturality_type.{u,v,w})
    (_relative : relativeEquivalence_type.{u,v,w})
    (_relativeNatural : relativeNaturality_type.{u,v,w}) :
    naturality_type.{u,v} := by
  intro R _ D E f n
  rw [← homologyMap_comp, ← homologyMap_comp]
  change homologyMap ((relativeFunctor (chainFunctor R R)).map D.inclusion ≫
    (relativeFunctor (chainFunctor R R)).map f.pairMap) n =
    homologyMap ((relativeFunctor (chainFunctor R R)).map f.excised ≫
      (relativeFunctor (chainFunctor R R)).map E.inclusion) n
  rw [← Functor.map_comp, ← Functor.map_comp, f.square]

end P202.Excision

namespace P202.Excision

/-- The actual inclusion induces an isomorphism in every ordinary degree.
The two-member cover requires only a universe-zero index type. -/
theorem isomorphism : P202Specs.Excision.isomorphism_type.{u,v} :=
  isomorphism_conditional.{u,v,0}
    P202.SmallChainEquivalence.absoluteEquivalence
    P202.SmallChainEquivalence.absoluteNaturality
    P202.SmallChainEquivalence.relativeEquivalence
    P202.SmallChainEquivalence.relativeNaturality

/-- Naturality for continuous maps of excision data. -/
theorem naturality : P202Specs.Excision.naturality_type.{u,v} :=
  naturality_conditional.{u,v,0}
    P202.SmallChainEquivalence.absoluteEquivalence
    P202.SmallChainEquivalence.absoluteNaturality
    P202.SmallChainEquivalence.relativeEquivalence
    P202.SmallChainEquivalence.relativeNaturality

end P202.Excision
