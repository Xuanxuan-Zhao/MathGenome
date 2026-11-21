import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Duality.AlexanderDuality
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Duality.PoincareDuality
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Duality.NeighborhoodCohomology
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Duality.CompactSupportDualityMap
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Homology.SpheresDisks
import Mathlib.Geometry.Manifold.Instances.Sphere

/-! Alexander duality (paper.tex 2483–2535), with finite singular chains
and singular cohomology, including all endpoint degrees. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace HomologicalComplex

namespace P202.AlexanderDuality
open P202Specs.AlexanderDuality P202Specs.SingularChains
open P202Specs.CohomologyPairs P202Specs.RelativeSingularChains
open P202Specs.LocalOrientation P202Specs.CompactSupport
open P202.Duality.NeighborhoodCohomology
universe u v

section ReducedNegative
variable (R : Type u) [CommRing R] (X : TopCat.{v})

/-- Dual augmentation is injective when the space is nonempty. -/
lemma reducedCoboundaryMinusOne_injective [Nonempty X] :
    Function.Injective ((reducedCochains R X).d (-1) 0) := by
  classical
  have hsurj : Function.Surjective ((reducedComplex R R X).d 0 (-1)) := by
    intro a
    let s : Simplex X 0 := (simplexEquiv X 0).symm
      (ContinuousMap.const _ (Classical.choice (inferInstance : Nonempty X)))
    let c := Finsupp.single s ((reducedCoefficientEquiv R R X) a)
    refine ⟨(reducedNonnegativeIso R R X 0).inv c, ?_⟩
    apply (reducedAugmentationIso R R X).toLinearEquiv.injective
    have h := congrArg (fun f => f c) (P202.SingularChains.reduced_augmentation R R X)
    change (reducedAugmentationIso R R X).hom
      ((reducedComplex R R X).d 0 (-1) ((reducedNonnegativeIso R R X 0).inv c)) = _ at h
    change (reducedAugmentationIso R R X).hom
      ((reducedComplex R R X).d 0 (-1) ((reducedNonnegativeIso R R X 0).inv c)) =
      (reducedAugmentationIso R R X).hom a
    rw [h]
    apply ULift.ext
    change (sumCoefficients R R _) c = (reducedCoefficientEquiv R R X) a
    simp [c, sumCoefficients]
  intro a b hab
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := hsurj x
  change a.comp ((reducedComplex R R X).d 0 (-1)).hom =
    b.comp ((reducedComplex R R X).d 0 (-1)).hom at hab
  exact congrArg (fun f : (reducedComplex R R X).X 0 →ₗ[R] R => f y) hab

/-- In particular the augmented dual gives the source's negative-degree zero
convention, including degree -1, rather than assigning an arbitrary group. -/
theorem reducedCohomology_negative [Nonempty X] (q : ℤ) (hq : q < 0) :
    IsZero (reducedCohomology R X q) := by
  by_cases h : q < -1
  · have hX : IsZero ((reducedCochains R X).X q) :=
      P202.CohomologyPairs.dual_isZero R R _
        (P202.SingularChains.reduced_below_minus_one R R X q h).1
    exact ((reducedCochains R X).sc q).isZero_homology_of_isZero_X₂ hX
  · have hq : q = -1 := by omega
    subst q
    let S := (reducedCochains R X).sc (-1)
    have hn : (ComplexShape.down ℤ).symm.next (-1) = 0 :=
      (ComplexShape.down ℤ).symm.next_eq' (by change (-1 : ℤ) + 1 = 0; omega)
    have hp : (ComplexShape.down ℤ).symm.prev (-1) = -2 :=
      (ComplexShape.down ℤ).symm.prev_eq' (by change (-2 : ℤ) + 1 = -1; omega)
    haveI : Mono S.g := by
      change Mono ((reducedCochains R X).d (-1) ((ComplexShape.down ℤ).symm.next (-1)))
      rw [hn]
      exact (ModuleCat.mono_iff_injective _).mpr (reducedCoboundaryMinusOne_injective R X)
    have hX : IsZero ((reducedCochains R X).X (-2)) :=
      P202.CohomologyPairs.dual_isZero R R _
        (P202.SingularChains.reduced_below_minus_one R R X (-2) (by omega)).1
    have hf : S.f = 0 := by
      change (reducedCochains R X).d ((ComplexShape.down ℤ).symm.prev (-1)) (-1) = 0
      rw [hp]
      exact hX.eq_of_src _ _
    exact (S.exact_iff_isZero_homology).mp ((S.exact_iff_mono hf).mpr inferInstance)

end ReducedNegative

section SupportIndex
variable {X : Type v} [TopologicalSpace X] [T2Space X] [CompactSpace X]
variable (K : Set X)

/-- A compact support in the complement gives an open ambient neighborhood
of K by taking its ambient complement. -/
def supportNeighborhood (L : Support (Kᶜ : Set X)) : OpenNeighborhood K where
  val := ⟨(Subtype.val '' (L : Set (Kᶜ : Set X)))ᶜ,
    (L.isCompact.image continuous_subtype_val).isClosed.isOpen_compl⟩
  property := by
    rintro x hx ⟨y, _, rfl⟩
    exact y.property hx

/-- Conversely, the complement of an ambient open neighborhood is an actual
compact subset of the open complement of K. -/
def neighborhoodSupport (N : OpenNeighborhood K) : Support (Kᶜ : Set X) where
  carrier := Subtype.val ⁻¹' (N.val : Set X)ᶜ
  isCompact' := Topology.IsInducing.subtypeVal.isCompact_preimage'
    N.val.isOpen.isClosed_compl.isCompact (by
      intro x hx
      exact ⟨⟨x, fun hxK => hx (N.property hxK)⟩, rfl⟩)

@[simp] lemma neighborhoodSupport_supportNeighborhood (L : Support (Kᶜ : Set X)) :
    neighborhoodSupport K (supportNeighborhood K L) = L := by
  apply Compacts.ext
  ext x
  change (¬¬x.val ∈ Subtype.val '' (L : Set (Kᶜ : Set X))) ↔ x ∈ L
  rw [not_not]
  constructor
  · rintro ⟨y, hy, he⟩
    exact (Subtype.val_injective he) ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

lemma openNeighborhood_ext {N N' : OpenNeighborhood K} (h : N.val = N'.val) : N = N' := by
  cases N
  cases N'
  cases h
  rfl

@[simp] lemma supportNeighborhood_neighborhoodSupport (N : OpenNeighborhood K) :
    supportNeighborhood K (neighborhoodSupport K N) = N := by
  apply openNeighborhood_ext K
  apply Opens.ext
  ext x
  change (¬∃ y : (Kᶜ : Set X), y.val ∉ N.val ∧ y.val = x) ↔ x ∈ N.val
  constructor
  · intro hx
    by_contra hxN
    exact hx ⟨⟨x, fun hxK => hxN (N.property hxK)⟩, hxN, rfl⟩
  · rintro hx ⟨y, hy, rfl⟩
    exact hy hx

/-- Every open neighborhood occurs, with precisely the reverse-inclusion
order used by the already proved singular-cohomology comparison. -/
def supportNeighborhoodOrderIso : Support (Kᶜ : Set X) ≃o OpenNeighborhood K where
  toFun := supportNeighborhood K
  invFun := neighborhoodSupport K
  left_inv := neighborhoodSupport_supportNeighborhood K
  right_inv := supportNeighborhood_neighborhoodSupport K
  map_rel_iff' := by
    intro L L'
    change (Subtype.val '' (L' : Set (Kᶜ : Set X)))ᶜ ⊆
      (Subtype.val '' (L : Set (Kᶜ : Set X)))ᶜ ↔ (L : Set (Kᶜ : Set X)) ⊆ (L' : Set (Kᶜ : Set X))
    rw [Set.compl_subset_compl]
    exact Set.image_subset_image_iff Subtype.val_injective

end SupportIndex

section SupportColimit
variable (R : Type u) [CommRing R] (M : Type v) [TopologicalSpace M]

/-- The categorical diagram underlying the algebraic compact-support limit. -/
def supportPairs : Support M ⥤ Pair.{v}ᵒᵖ where
  obj L := op (supportedPair M L)
  map f := (supportPairMap M (leOfHom f)).op
  map_id L := by rfl
  map_comp f g := by rfl

abbrev supportDiagram (p : ℤ) := supportPairs M ⋙ relativeCohomologyFunctor R R p

def compactSupportCocone (p : ℤ) : Cocone (supportDiagram R M p) where
  pt := ModuleCat.of R (CompactCohomology R M p)
  ι :=
    { app := fun L => ModuleCat.ofHom (ofSupport R M p L)
      naturality := fun L L' f => by
        apply ModuleCat.hom_ext
        ext a
        exact P202.CompactSupport.ofSupport_transition R M p L L' (leOfHom f) a }

/-- Descent to any categorical cocone, written separately so its concrete
representative law is available without unfolding a colimit structure. -/
def compactSupportDesc (p : ℤ) (s : Cocone (supportDiagram R M p)) :
    CompactCohomology R M p →ₗ[R] s.pt :=
  descend R M p (fun L => (s.ι.app L).hom) (by
    intro L L' h a
    exact congrArg (fun f => f a) (s.w (homOfLE h)))

@[simp] lemma compactSupportDesc_ofSupport (p : ℤ) (s : Cocone (supportDiagram R M p))
    (L : Support M) (a : supportedCohomology R M p L) :
    compactSupportDesc R M p s (ofSupport R M p L a) = s.ι.app L a := by
  simp only [compactSupportDesc, descend, ofSupport, Module.DirectLimit.lift_of]
  rfl

/-- The concrete algebraic direct limit has the categorical universal property;
this avoids identifying the two colimit models without a proof. -/
def compactSupportCoconeIsColimit (p : ℤ) : IsColimit (compactSupportCocone R M p) where
  desc s := ModuleCat.ofHom (compactSupportDesc R M p s)
  fac s L := by
    apply ModuleCat.hom_ext
    ext a
    exact compactSupportDesc_ofSupport R M p s L a
  uniq s m hm := by
    apply ModuleCat.hom_ext
    apply P202.CompactSupport.hom_ext R M p
    intro L
    ext a
    simp only [ModuleCat.hom_ofHom, LinearMap.comp_apply, compactSupportDesc_ofSupport]
    exact congrArg (fun f => f a) (hm L)

end SupportColimit

section ComplementComparison
variable (R : Type u) [CommRing R]
variable {X : Type v} [TopologicalSpace X] [T2Space X] [CompactSpace X]
variable (K : Set X) (hK : IsClosed K)

/-- Inverse excision identifies each compact support in the complement with
its corresponding ambient relative group, and respects transition maps. -/
def complementDiagramIso (p : ℤ) :
    supportDiagram R (Kᶜ : Set X) p ≅
      (supportNeighborhoodOrderIso K).equivalence.functor ⋙ relativeDiagram K R R p := by
  haveI (L : Support (Kᶜ : Set X)) :=
    P202.CompactSupport.openExcision R X (Kᶜ : Set X) hK.isOpen_compl L p
  refine NatIso.ofComponents
    (fun L => (asIso (openPullback R X (Kᶜ : Set X) L p)).symm) ?_
  intro L L' f
  apply ModuleCat.hom_ext
  ext a
  exact P202.CompactSupport.extendAt_compatible R X (Kᶜ : Set X)
    hK.isOpen_compl p (leOfHom f) a

/-- The first limit in the source proof, with all compact supports and all
open neighborhoods, is an actual isomorphism in every integer degree. -/
def compactSupportNeighborhoodIso (p : ℤ) :
    ModuleCat.of R (CompactCohomology R (Kᶜ : Set X) p) ≅
      colimit (relativeDiagram K R R p) :=
  (colimit.isoColimitCocone ⟨compactSupportCocone R (Kᶜ : Set X) p,
    compactSupportCoconeIsColimit R (Kᶜ : Set X) p⟩).symm ≪≫
    HasColimit.isoOfNatIso (complementDiagramIso R K hK p) ≪≫
    Functor.Final.colimitIso (supportNeighborhoodOrderIso K).equivalence.functor
      (relativeDiagram K R R p)

/-- Compose with the proved neighborhood restriction comparison. This theorem
still has no manifold or duality-isomorphism hypothesis. -/
def compactSupportRelativeIso (h : HasShrinkingRetraction K) (p : ℤ) :
    ModuleCat.of R (CompactCohomology R (Kᶜ : Set X) p) ≅
      relativeCohomology R R (ambientPair K) p := by
  haveI := P202.Duality.NeighborhoodCohomology.relativeComparison_of_shrinking R R h p
  exact compactSupportNeighborhoodIso R K hK p ≪≫ asIso (relativeComparison K R R p)

/-- The isomorphism is induced by inverse excision at each support, with the
canonical leg into the neighborhood colimit. -/
lemma ofSupport_compactSupportNeighborhoodIso (p : ℤ) (L : Support (Kᶜ : Set X)) :
    ModuleCat.ofHom (ofSupport R (Kᶜ : Set X) p L) ≫
      (compactSupportNeighborhoodIso R K hK p).hom =
    ModuleCat.ofHom (P202.CompactSupport.extendAt R X (Kᶜ : Set X) hK.isOpen_compl L p) ≫
      colimit.ι (relativeDiagram K R R p) (supportNeighborhood K L) := by
  let c : ColimitCocone (supportDiagram R (Kᶜ : Set X) p) :=
    ⟨compactSupportCocone R (Kᶜ : Set X) p,
      compactSupportCoconeIsColimit R (Kᶜ : Set X) p⟩
  let e₁ := colimit.isoColimitCocone c
  let e₂ := HasColimit.isoOfNatIso (complementDiagramIso R K hK p)
  let e₃ := Functor.Final.colimitIso (supportNeighborhoodOrderIso K).equivalence.functor
    (relativeDiagram K R R p)
  have h₁ : c.cocone.ι.app L ≫ e₁.inv = colimit.ι (supportDiagram R (Kᶜ : Set X) p) L :=
    colimit.isoColimitCocone_ι_inv c L
  have h₂ : colimit.ι (supportDiagram R (Kᶜ : Set X) p) L ≫ e₂.hom =
      (complementDiagramIso R K hK p).hom.app L ≫
        colimit.ι ((supportNeighborhoodOrderIso K).equivalence.functor ⋙ relativeDiagram K R R p) L :=
    HasColimit.ι_isoOfNatIso_hom (complementDiagramIso R K hK p) L
  have h₃ : colimit.ι ((supportNeighborhoodOrderIso K).equivalence.functor ⋙
      relativeDiagram K R R p) L ≫ e₃.hom =
      colimit.ι (relativeDiagram K R R p) (supportNeighborhood K L) :=
    Functor.Final.ι_colimitIso_hom _ _ L
  change c.cocone.ι.app L ≫ (e₁.inv ≫ e₂.hom ≫ e₃.hom) = _
  calc
    _ = ((c.cocone.ι.app L ≫ e₁.inv) ≫ e₂.hom) ≫ e₃.hom := by simp only [Category.assoc]
    _ = (colimit.ι (supportDiagram R (Kᶜ : Set X) p) L ≫ e₂.hom) ≫ e₃.hom :=
      congrArg (fun f => (f ≫ e₂.hom) ≫ e₃.hom) h₁
    _ = ((complementDiagramIso R K hK p).hom.app L ≫
        colimit.ι ((supportNeighborhoodOrderIso K).equivalence.functor ⋙ relativeDiagram K R R p) L) ≫ e₃.hom :=
      congrArg (fun f => f ≫ e₃.hom) h₂
    _ = (complementDiagramIso R K hK p).hom.app L ≫
        colimit.ι (relativeDiagram K R R p) (supportNeighborhood K L) := by
      rw [Category.assoc, h₃]
    _ = _ := rfl

/-- The final relative comparison is the restriction of the excised support
class along the actual inclusion (X,K) → (X,N). -/
lemma ofSupport_compactSupportRelativeIso (h : HasShrinkingRetraction K) (p : ℤ)
    (L : Support (Kᶜ : Set X)) :
    ModuleCat.ofHom (ofSupport R (Kᶜ : Set X) p L) ≫
      (compactSupportRelativeIso R K hK h p).hom =
    ModuleCat.ofHom (P202.CompactSupport.extendAt R X (Kᶜ : Set X) hK.isOpen_compl L p) ≫
      (relativeCohomologyFunctor R R p).map
        (ambientPairInclusion (supportNeighborhood K L).property).op := by
  haveI := P202.Duality.NeighborhoodCohomology.relativeComparison_of_shrinking R R h p
  change _ ≫ ((compactSupportNeighborhoodIso R K hK p).hom ≫
    relativeComparison K R R p) = _
  rw [← Category.assoc, ofSupport_compactSupportNeighborhoodIso, Category.assoc]
  change _ ≫ (colimit.ι (relativeDiagram K R R p) (supportNeighborhood K L) ≫
    colimit.desc _ (relativeRestrictionCocone K R R p)) = _
  rw [colimit.ι_desc]
  rfl

end ComplementComparison

section SphereComparison
variable (R : Type u) [CommRing R]

/-- Specialization of the proved support comparison to exactly the subsets
occurring in the original Alexander statement. -/
def sphereCompactSupportRelativeEquiv
    (n : ℕ) (K : Set (Sphere n)) (hn : 1 ≤ n) (hne : K.Nonempty)
    (hproper : K ≠ Set.univ) (hK : IsCompact K) (hLC : LocallyContractibleSpace K)
    (p : ℤ) : CompactCohomology R (Kᶜ : Set (Sphere n)) p ≃ₗ[R]
      relativeCohomology R R (ambientPair K) p :=
  (compactSupportRelativeIso R K hK.isClosed
    (P202.Duality.NeighborhoodCohomology.sphereShrinkingRetraction
      n K hn hne hproper hK hLC) p).toLinearEquiv


/-- Properness supplies the nonempty open complement required at degree zero. -/
lemma complement_nonempty (n : ℕ) (K : Set (Sphere n)) (hproper : K ≠ Set.univ) :
    Nonempty (complement n K) := by
  obtain ⟨x, hx⟩ := Set.ne_univ_iff_exists_notMem K |>.mp hproper
  exact ⟨⟨x, hx⟩⟩

/-- The cohomological side at i=n and i>n is zero with the actual augmented
singular cochain definition. This only uses the nonemptiness of K. -/
theorem shiftedReducedCohomology_isZero (n i : ℕ) (K : Set (Sphere n))
    (hne : K.Nonempty) (hi : n ≤ i) :
    IsZero (reducedCohomology R (TopCat.of K) ((n : ℤ) - (i : ℤ) - 1)) := by
  letI : Nonempty K := hne.to_subtype
  exact reducedCohomology_negative R (TopCat.of K) _ (by omega)

end SphereComparison

/-- The ordinary-homology/relative-cohomology step of the proof, using
the current proved upstream duality theorem.
The ambient space may be any compact Hausdorff space; a manifold structure
and orientation on its open complement are explicit data for this helper.
No original Alexander target is defined by this intermediate construction. -/
def complementHomologyRelativeEquiv
    (R : Type u) [CommRing R] (d : DualityData.{u,v} R)
    {X : Type v} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    (K : Set X) (hK : IsClosed K) (h : HasShrinkingRetraction K)
    (n : ℕ) (A : Manifold n (Kᶜ : Set X)) (o : Orientation R A) (i : ℤ) :
    homology R R (TopCat.of (Kᶜ : Set X)) i ≃ₗ[R]
      relativeCohomology R R (ambientPair K) ((n : ℤ) - i) := by
  let p : ℤ := (n : ℤ) - i
  let e := LinearEquiv.ofBijective (d.D n (Kᶜ : Set X) A o p)
    (P202.PoincareDuality.duality R d n (Kᶜ : Set X) A o p)
  have hi : (n : ℤ) - p = i := by dsimp [p]; omega
  let e' : homology R R (TopCat.of (Kᶜ : Set X)) i ≃ₗ[R]
      CompactCohomology R (Kᶜ : Set X) p := by
    rw [← hi]
    exact e.symm
  exact e'.trans (compactSupportRelativeIso R K hK h p).toLinearEquiv

section ReducedPairs
open HomologicalComplex P202Specs.ChainLES
variable (R : Type u) [CommRing R]

/-- Relative reduced cochains are the dual of the actual augmented quotient.
The extra augmentation cancels in the quotient, even for an empty subspace. -/
abbrev reducedRelativeCochains (P : Pair.{v}) :=
  (dualComplexFunctor R R (.down ℤ)).obj (op (reduced R R P))

abbrev reducedRelativeToAbsolute (P : Pair.{v}) :
    reducedRelativeCochains R P ⟶ reducedCochains R P.space :=
  (dualComplexFunctor R R (.down ℤ)).map (projection (reducedFunctor R R) P).op

abbrev reducedRestriction (P : Pair.{v}) :
    reducedCochains R P.space ⟶ reducedCochains R P.sub :=
  (dualComplexFunctor R R (.down ℤ)).map (inclusion (reducedFunctor R R) P).op

def reducedCochainSequence (P : Pair.{v}) :
    ShortComplex (CochainComplex (ModuleCat.{max u v} R) ℤ) :=
  ShortComplex.mk (reducedRelativeToAbsolute R P) (reducedRestriction R P) (by
    dsimp only [reducedRelativeToAbsolute, reducedRestriction]
    rw [← Functor.map_comp, ← op_comp]
    change (dualComplexFunctor R R (.down ℤ)).map
      ((sequence (reducedFunctor R R) P).f ≫ (sequence (reducedFunctor R R) P).g).op = 0
    rw [ShortComplex.zero, op_zero, Functor.map_zero])

lemma reduced_inclusion_augmentation (P : Pair.{v}) :
    (reducedAugmentationIso R R P.sub).inv ≫
      (inclusion (reducedFunctor R R) P).f (-1) ≫
        (reducedAugmentationIso R R P.space).hom = 𝟙 _ := by
  change (reducedAugmentationIso R R P.sub).inv ≫
    (extendMap (augmentedShiftedMap R R P.inclusion) (degreeEmbedding (-1))).f (-1) ≫
      (reducedAugmentationIso R R P.space).hom = 𝟙 _
  rw [extendMap_f _ _ (show (degreeEmbedding (-1)).f 0 = (-1 : ℤ) from rfl)]
  simp [reducedAugmentationIso, augmentedShiftedMap]

/-- Extension by zero splits restriction on cochains in all degrees; at -1
the chain inclusion is the identity on the coefficient module. -/
lemma reduced_inclusion_split (P : Pair.{v}) (q : ℤ) :
    ∃ r : (reducedComplex R R P.space).X q ⟶ (reducedComplex R R P.sub).X q,
      (inclusion (reducedFunctor R R) P).f q ≫ r = 𝟙 _ := by
  by_cases hq : 0 ≤ q
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hq
    refine ⟨(reducedNonnegativeIso R R P.space n).hom ≫
      ModuleCat.ofHom (P202.CohomologyPairs.chainRetraction R P n) ≫
        (reducedNonnegativeIso R R P.sub n).inv, ?_⟩
    rw [← Category.assoc, ← Category.assoc, reduced_inclusion_degree]
    simp only [Category.assoc]
    have h : (inclusion (chainFunctor R R) P).f n ≫
        ModuleCat.ofHom (P202.CohomologyPairs.chainRetraction R P n) = 𝟙 _ := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      exact P202.CohomologyPairs.chainRetraction_inclusion R P n c
    rw [← Category.assoc ((inclusion (chainFunctor R R) P).f n), h]
    simp
  · by_cases h : q = -1
    · subst q
      refine ⟨(reducedAugmentationIso R R P.space).hom ≫
        (reducedAugmentationIso R R P.sub).inv, ?_⟩
      apply (cancel_epi (reducedAugmentationIso R R P.sub).inv).mp
      change (reducedAugmentationIso R R P.sub).inv ≫
        ((inclusion (reducedFunctor R R) P).f (-1) ≫
          ((reducedAugmentationIso R R P.space).hom ≫
            (reducedAugmentationIso R R P.sub).inv)) =
              (reducedAugmentationIso R R P.sub).inv ≫
                𝟙 ((reducedComplex R R P.sub).X (-1))
      simpa only [Category.assoc, Category.id_comp, Category.comp_id] using
        congrArg (fun f => f ≫ (reducedAugmentationIso R R P.sub).inv)
          (reduced_inclusion_augmentation R P)
    · refine ⟨0, ?_⟩
      exact (P202.SingularChains.reduced_below_minus_one R R P.sub q (by omega)).1.eq_of_src _ _

/-- A genuine short exact sequence, without injectivity assumptions on the
coefficient ring or any topological regularity assumption on the pair. -/
theorem reducedCochainSequence_shortExact (P : Pair.{v}) :
    DegreewiseShortExact (reducedCochainSequence R P) := by
  intro q
  exact P202.CohomologyPairs.dual_shortExact R R
    ((sequence (reducedFunctor R R) P).map (HomologicalComplex.eval _ _ q))
    (P202.RelativeSingularChains.reduced_short_exact R R P q)
    (reduced_inclusion_split R P q)

/-- Dualize the proved isomorphism of ordinary and augmented relative chains.
This comparison leaves absolute reduced cohomology unchanged. -/
def reducedRelativeCohomologyIso (P : Pair.{v}) (q : ℤ) :
    (reducedRelativeCochains R P).homology q ≅ relativeCohomology R R P q :=
  (HomologicalComplex.homologyFunctor _ _ q).mapIso
    ((dualComplexFunctor R R (.down ℤ)).mapIso
      (P202.MayerVietoris.reducedOrdinaryRelativeIso R P).symm.op)

/-- Whenever the two adjacent absolute reduced groups vanish, the connecting
map identifies the reduced cohomology of the subspace with ordinary relative
cohomology. In particular, q=0 uses the quotient by constant cochains. -/
def reducedPairShiftIso (P : Pair.{v}) (q : ℤ)
    (hq : IsZero (reducedCohomology R P.space q))
    (hq' : IsZero (reducedCohomology R P.space (q+1))) :
    reducedCohomology R P.sub q ≅ relativeCohomology R R P (q+1) :=
  (HomologicalComplex.shortExact_of_degreewise_shortExact _
    (reducedCochainSequence_shortExact R P)).δIso q (q+1)
      (by change q+1=q+1; rfl) hq hq' ≪≫ reducedRelativeCohomologyIso R P (q+1)

end ReducedPairs


section SphereOrientation
lemma contractibleSubspace_inclusion_mono (R : Type u) [CommRing R]
    (P : Pair.{v}) [ContractibleSpace P.sub] (j : ℤ) :
    Mono ((homologyFunctor R R j).map P.inclusion) := by
  obtain ⟨p, ⟨H⟩⟩ := id_nullhomotopic P.sub
  let r : P.space ⟶ P.sub := TopCat.ofHom (ContinuousMap.const P.space p)
  have h : (homologyFunctor R R j).map P.inclusion ≫
      (homologyFunctor R R j).map r = 𝟙 _ := by
    rw [← Functor.map_comp]
    have he := (P202.PrismHomotopy.homology R R H j).1
    change (homologyFunctor R R j).map (𝟙 P.sub) =
      (homologyFunctor R R j).map (P.inclusion ≫ r) at he
    rw [← he]
    exact (homologyFunctor R R j).map_id _
  exact mono_of_mono_fac h

lemma contractibleSubspace_projection_isIso (R : Type u) [CommRing R]
    (P : Pair.{v}) [Nonempty P.sub] [ContractibleSpace P.sub]
    (j : ℕ) (hj : 0 < j) :
    IsIso (homologyMap (projection (ordinaryFunctor R R) P) (j : ℤ)) := by
  let S := sequence (ordinaryFunctor R R) P
  let hS := shortExact_of_degreewise_shortExact S
    (P202.RelativeSingularChains.ordinary_short_exact R R P)
  have hz : IsZero (homology R R P.sub (j : ℤ)) :=
    (P202.SingularDegreeZero.reducedPositiveIso R R P.sub j hj).isZero_iff.mp
      (P202.PrismHomotopy.contractible R R P.sub j)
  have hm : Mono (homologyMap S.g (j : ℤ)) :=
    (ShortComplex.exact_iff_mono _ (hz.eq_zero_of_src _)).mp (hS.homology_exact₂ (j : ℤ))
  haveI := hm
  haveI := contractibleSubspace_inclusion_mono R P ((j : ℤ)-1)
  haveI : Mono (homologyMap S.f ((j : ℤ)-1)) := by
    change Mono ((homologyFunctor R R ((j : ℤ)-1)).map P.inclusion)
    infer_instance
  have hd : hS.δ (j : ℤ) ((j : ℤ)-1) (by simp) = 0 := by
    apply (cancel_mono (homologyMap S.f ((j : ℤ)-1))).mp
    simpa only [zero_comp] using hS.δ_comp (j : ℤ) ((j : ℤ)-1) (by simp)
  haveI : Epi (homologyMap S.g (j : ℤ)) :=
    (ShortComplex.exact_iff_epi _ hd).mp (hS.homology_exact₃ (j : ℤ) ((j : ℤ)-1) (by simp))
  change IsIso (homologyMap S.g (j : ℤ))
  exact isIso_of_mono_of_epi _

/-- The actual sphere has a chart cover in the independent full Euclidean model. -/
def sphereManifold (n : ℕ) : Manifold n (Sphere n) where
  hausdorff := inferInstance
  secondCountable := inferInstance
  atlas := Set.range (fun p : Sphere n =>
    (chartAt (EuclideanSpace ℝ (Fin n)) p).transHomeomorph
      (P202.LocalOrientation.coordinateEuclideanHomeomorph n).symm)
  covers p := by
    refine ⟨_, ⟨p, rfl⟩, ?_⟩
    exact mem_chart_source (EuclideanSpace ℝ (Fin n)) p

/-- The puncture is the actual local-pair subspace, with its existing topology. -/
def spherePuncturedHomeomorph (n : ℕ) (p : Sphere n) :
    (localPair (Sphere n) p).sub ≃ₜ EuclideanSpace ℝ (Fin n) := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1))) = n+1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let e := stereographic' n p
  exact (Homeomorph.setCongr (by ext y; simp [e] :
    {y : Sphere n | y ≠ p} = e.source)).trans
    (e.toHomeomorphSourceTarget.trans
      ((Homeomorph.setCongr (stereographic'_target p)).trans (Homeomorph.Set.univ _)))

lemma sphereLocalProjection_isIso (R : Type u) [CommRing R]
    (n : ℕ) (hn : 0 < n) (p : Sphere n) :
    IsIso (homologyMap (projection (ordinaryFunctor R R) (localPair (Sphere n) p)) (n : ℤ)) := by
  letI : ContractibleSpace (localPair (Sphere n) p).sub :=
    (spherePuncturedHomeomorph n p).contractibleSpace
  letI : Nonempty (localPair (Sphere n) p).sub :=
    (spherePuncturedHomeomorph n p).toEquiv.nonempty
  exact contractibleSubspace_projection_isIso R _ n hn

/-- Point values of one supported class are automatically locally compatible
when each of these point values is a generator. -/
def supportedLocalChoice (R : Type u) [CommRing R] {n : ℕ}
    {M : Type v} [TopologicalSpace M] (g : SupportedGroup R M Set.univ n) :
    LocalChoice R n M := fun x => restrictPoint R (Set.mem_univ x) n g

lemma supportedLocalChoice_orientation (R : Type u) [CommRing R] {n : ℕ}
    {M : Type v} [TopologicalSpace M] (A : Manifold n M)
    (g : SupportedGroup R M Set.univ n)
    (hg : ∀ x, IsGenerator R (supportedLocalChoice R g x)) :
    IsOrientation R A (supportedLocalChoice R g) := by
  refine ⟨hg, ?_⟩
  intro x
  obtain ⟨B, hxB, _⟩ := P202.LocalOrientation.coordinateBall_basis A x
    isOpen_univ (Set.mem_univ x)
  let gB : SupportedGroup R M B.closed n :=
    ((relativeHomologyFunctor R R (n : ℤ)).map (supportMap (Set.subset_univ B.closed))) g
  have hval (y : M) (hy : y ∈ B.closed) :
      restrictPoint R hy n gB = supportedLocalChoice R g y := by
    exact P202.LocalOrientation.restrictPoint_support (Set.subset_univ B.closed) hy n g
  refine ⟨B, hxB, gB, ?_, fun y hy => hval y (B.interior_subset_closed hy)⟩
  apply (P202.LocalOrientation.generator_map_iff R
    (P202.LocalOrientation.ballPointEquiv P202.LocalOrientation.ballRestriction R B hxB) gB).mp
  change IsGenerator R (restrictPoint R (B.interior_subset_closed hxB) n gB)
  rw [hval]
  exact hg x

lemma sphereAbsoluteLocalRestriction (R : Type u) [CommRing R]
    (n : ℕ) (p : Sphere n) (μ : homology R R (TopCat.of (Sphere n)) (n : ℤ)) :
    restrictPoint R (Set.mem_univ p) n
      (P202Specs.CompactOrientation.absoluteToSupported R (Sphere n) n μ) =
      homologyMap (projection (ordinaryFunctor R R) (localPair (Sphere n) p)) (n : ℤ) μ := by
  have hs := projection_map (ordinaryFunctor R R) (pointMap (Set.mem_univ p))
  change projection (ordinaryFunctor R R) (supportedPair (Sphere n) Set.univ) ≫
    relativeMap (ordinaryFunctor R R) (pointMap (Set.mem_univ p)) =
      (ordinaryFunctor R R).map (𝟙 (TopCat.of (Sphere n))) ≫
        projection (ordinaryFunctor R R) (localPair (Sphere n) p) at hs
  rw [(ordinaryFunctor R R).map_id, Category.id_comp] at hs
  have h := congrArg (fun f => homologyMap f (n : ℤ)) hs
  simp only [homologyMap_comp] at h
  exact congrArg (fun f => f μ) h

/-- Every coefficient ring has an orientation on the original geometric sphere. -/
def sphereOrientation (R : Type u) [CommRing R] (n : ℕ) (hn : 0 < n) :
    Orientation R (sphereManifold n) := by
  let e := Classical.choice ((P202.SpheresDisks.sphereHomology R R n n).1 rfl)
  let f := (P202.SingularDegreeZero.reducedPositiveIso R R
    (TopCat.of (Sphere n)) n hn).toLinearEquiv
  let μ := Classical.choose (P202.LocalOrientation.exists_generator R (f.symm.trans e))
  have hμ := Classical.choose_spec (P202.LocalOrientation.exists_generator R (f.symm.trans e))
  let g := P202Specs.CompactOrientation.absoluteToSupported R (Sphere n) n μ
  refine ⟨supportedLocalChoice R g, supportedLocalChoice_orientation R (sphereManifold n) g ?_⟩
  intro p
  haveI := sphereLocalProjection_isIso R n hn p
  let l := (asIso (homologyMap (projection (ordinaryFunctor R R)
    (localPair (Sphere n) p)) (n : ℤ))).toLinearEquiv
  change IsGenerator R (restrictPoint R (Set.mem_univ p) n g)
  rw [sphereAbsoluteLocalRestriction]
  exact (P202.LocalOrientation.generator_map_iff R l μ).mpr hμ

lemma sphereOrientation_fundamentalClass (R : Type u) [CommRing R] (n : ℕ) (hn : 0 < n) :
    ∃ μ : homology R R (TopCat.of (Sphere n)) (n : ℤ), IsGenerator R μ ∧
      P202Specs.CompactOrientation.HasLocalValues R (sphereOrientation R n hn).val Set.univ
        (P202Specs.CompactOrientation.absoluteToSupported R (Sphere n) n μ) := by
  let e := Classical.choice ((P202.SpheresDisks.sphereHomology R R n n).1 rfl)
  let f := (P202.SingularDegreeZero.reducedPositiveIso R R
    (TopCat.of (Sphere n)) n hn).toLinearEquiv
  let μ := Classical.choose (P202.LocalOrientation.exists_generator R (f.symm.trans e))
  refine ⟨μ, Classical.choose_spec (P202.LocalOrientation.exists_generator R (f.symm.trans e)), ?_⟩
  intro x hx
  rfl


/-- The sphere complement has its inherited manifold structure. -/
def complementManifold (n : ℕ) (K : Set (Sphere n)) (hK : IsCompact K) :
    Manifold n (Kᶜ : Set (Sphere n)) :=
  P202.CompactSupportMV.openManifold (sphereManifold n) Kᶜ hK.isClosed.isOpen_compl

/-- The original sphere orientation induces the actual local-homology orientation. -/
def complementOrientation (R : Type u) [CommRing R]
    (n : ℕ) (hn : 0 < n) (K : Set (Sphere n)) (hK : IsCompact K) :
    Orientation R (complementManifold n K hK) :=
  P202.CompactSupportMV.openOrientation R (sphereManifold n) (sphereOrientation R n hn)
    Kᶜ hK.isClosed.isOpen_compl (complementManifold n K hK)

lemma complementOrientation_compatible (R : Type u) [CommRing R]
    (n : ℕ) (hn : 0 < n) (K : Set (Sphere n)) (hK : IsCompact K) :
    OpenOrientationCompatible R (Sphere n) (sphereOrientation R n hn).val
      (complementOrientation R n hn K hK).val :=
  P202.CompactSupportMV.openOrientation_compatible R (sphereManifold n)
    (sphereOrientation R n hn) Kᶜ hK.isClosed.isOpen_compl (complementManifold n K hK)

end SphereOrientation

section SphereCohomology
open P202Specs.SpheresDisks
variable (R : Type u) [CommRing R]
lemma reducedComplex_free (X : TopCat.{v}) (q : ℤ) :
    Module.Free R ((reducedComplex R R X).X q) := by
  by_cases hq : 0 ≤ q
  · obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hq
    haveI : Module.Free R ((complex R R X).X j) := by
      change Module.Free R (Chains R X j)
      infer_instance
    exact Module.Free.of_equiv (reducedNonnegativeIso R R X j).symm.toLinearEquiv
  · by_cases hq' : q = -1
    · subst q
      exact Module.Free.of_equiv (reducedCoefficientEquiv R R X).symm
    · haveI : Subsingleton ((reducedComplex R R X).X q) :=
        ModuleCat.subsingleton_of_isZero
          (P202.SingularChains.reduced_below_minus_one R R X q (by omega)).1
      infer_instance

lemma reducedComplex_boundedBelow (X : TopCat.{v}) :
    P202Specs.FreeChainDual.BoundedBelow (reducedComplex R R X) :=
  ⟨-1, fun q hq => (P202.SingularChains.reduced_below_minus_one R R X q hq).1⟩

lemma sphere_reducedHomology_concentrated (n : ℕ) (q : ℤ) (hq : q ≠ (n : ℤ)) :
    IsZero (reducedHomology R R (sphere n) q) := by
  by_cases hq0 : 0 ≤ q
  · obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hq0
    exact (P202.SpheresDisks.sphereHomology R R n j).2 (by omega)
  · haveI : Nonempty (sphere n) :=
      (NormedSpace.sphere_nonempty.mpr (show (0 : ℝ) ≤ 1 by norm_num)).to_subtype
    by_cases hq1 : q < -1
    · exact (P202.SingularChains.reduced_below_minus_one R R _ q hq1).2
    · have hq1 : q = -1 := by omega
      subst q
      exact P202.SingularDegreeZero.nonemptyReducedMinusOne R R _

lemma sphere_reducedCohomology_concentrated (n : ℕ) (q : ℤ) (hq : q ≠ (n : ℤ)) :
    IsZero (reducedCohomology R (sphere n) q) := by
  let K := reducedComplex R R (sphere n)
  obtain ⟨e⟩ := (P202.SpheresDisks.sphereHomology R R n n).1 rfl
  haveI : Module.Free R (K.homology (n : ℤ)) := Module.Free.of_equiv e.symm
  haveI : ∀ j : ℤ, Module.Free R (K.X j) := reducedComplex_free R _
  let c : K.homology (n : ℤ) ⟶ K.cycles (n : ℤ) :=
    Projective.factorThru (𝟙 _) (K.homologyπ (n : ℤ))
  have hc : c ≫ K.homologyπ (n : ℤ) = 𝟙 _ := Projective.factorThru_comp _ _
  haveI : IsIso (c ≫ K.homologyπ (n : ℤ)) := by rw [hc]; infer_instance
  exact P202.PoincareDuality.ConcentratedChains.dualCohomology_isZero R K (n : ℤ)
    (reducedComplex_boundedBelow R _) c
    (sphere_reducedHomology_concentrated R n) q hq


end SphereCohomology

section AugmentationComparison
open HomologicalComplex
variable (R : Type u) [CommRing R]
/-- Forget the augmentation, leaving every finite singular chain unchanged. -/
def forgetAugmentation (X : TopCat.{v}) :
    reducedComplex R R X ⟶ ordinaryComplex R R X where
  f i := match i with
    | .ofNat n => (reducedNonnegativeIso R R X n).hom ≫
        (ordinaryNonnegativeIso R R X n).inv
    | .negSucc _ => 0
  comm' i j hij := by
    cases j with
    | negSucc n =>
      exact (P202.SingularChains.ordinary_negative_chains R R X _ (by omega)).eq_of_tgt _ _
    | ofNat n =>
      have hi : i = ((n+1 : ℕ) : ℤ) := by
        change (n : ℤ) + 1 = i at hij
        omega
      subst i
      change ((reducedNonnegativeIso R R X (n+1)).hom ≫
        (ordinaryNonnegativeIso R R X (n+1)).inv) ≫ _ =
        _ ≫ ((reducedNonnegativeIso R R X n).hom ≫ (ordinaryNonnegativeIso R R X n).inv)
      apply (cancel_epi (reducedNonnegativeIso R R X (n+1)).inv).mp
      apply (cancel_mono (ordinaryNonnegativeIso R R X n).hom).mp
      simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
        Category.comp_id, Int.ofNat_eq_natCast, Int.natCast_add, Int.natCast_one] using
        (P202.SingularChains.ordinary_boundary R R X n).trans
          (P202.SingularChains.reduced_boundary R R X n).symm

lemma forgetAugmentation_naturality {X Y : TopCat.{v}} (f : X ⟶ Y) :
    (reducedFunctor R R).map f ≫ forgetAugmentation R Y =
      forgetAugmentation R X ≫ (ordinaryFunctor R R).map f := by
  apply HomologicalComplex.Hom.ext
  funext i
  cases i with
  | negSucc n =>
    exact (P202.SingularChains.ordinary_negative_chains R R Y _ (by omega)).eq_of_tgt _ _
  | ofNat n =>
    change (extendMap (augmentedShiftedMap R R f) (degreeEmbedding (-1))).f (n : ℤ) ≫
        ((reducedNonnegativeIso R R Y n).hom ≫ (ordinaryNonnegativeIso R R Y n).inv) =
      ((reducedNonnegativeIso R R X n).hom ≫ (ordinaryNonnegativeIso R R X n).inv) ≫
        (extendMap (chainMap R R f) (degreeEmbedding 0)).f (n : ℤ)
    rw [extendMap_f _ _ (show (degreeEmbedding (-1)).f (n+1) = (n : ℤ) by dsimp [degreeEmbedding]; omega),
      extendMap_f _ _ (show (degreeEmbedding 0).f n = (n : ℤ) by dsimp [degreeEmbedding]; omega)]
    simp [reducedNonnegativeIso, ordinaryNonnegativeIso, augmentedShiftedMap]

/-- The canonical relative comparison commutes with quotient projection. -/
lemma forgetAugmentation_projection (P : Pair.{v}) :
    projection (reducedFunctor R R) P ≫
        (P202.MayerVietoris.reducedOrdinaryRelativeIso R P).hom =
      forgetAugmentation R P.space ≫ projection (ordinaryFunctor R R) P := by
  apply HomologicalComplex.Hom.ext
  funext i
  cases i with
  | negSucc n =>
    exact (P202.RelativeSingularChains.ordinary_negative R R P _ (by omega)).1.eq_of_tgt _ _
  | ofNat n =>
    change (projection (reducedFunctor R R) P).f (n : ℤ) ≫
      ((reducedDegreeIso R R P n).hom ≫ (ordinaryDegreeIso R R P n).inv) =
      ((reducedNonnegativeIso R R P.space n).hom ≫ (ordinaryNonnegativeIso R R P.space n).inv) ≫
        (projection (ordinaryFunctor R R) P).f (n : ℤ)
    apply (cancel_mono (ordinaryDegreeIso R R P n).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [P202.RelativeSingularChains.reduced_degree, P202.RelativeSingularChains.ordinary_degree]
    simp

abbrev ordinaryToReducedCochains (X : TopCat.{v}) : ordinaryCochains R R X ⟶ reducedCochains R X :=
  (dualComplexFunctor R R (.down ℤ)).map (forgetAugmentation R X).op

lemma ordinaryToReducedCochains_isIso_f (X : TopCat.{v}) (n : ℕ) :
    IsIso ((ordinaryToReducedCochains R X).f (n : ℤ)) := by
  change IsIso ((dualFunctor R R).map ((forgetAugmentation R X).f (n : ℤ)).op)
  haveI : IsIso ((forgetAugmentation R X).f (n : ℤ)) := by
    change IsIso ((reducedNonnegativeIso R R X n).hom ≫ (ordinaryNonnegativeIso R R X n).inv)
    infer_instance
  exact ((dualFunctor R R).mapIso (asIso ((forgetAugmentation R X).f (n : ℤ))).op).isIso_hom

/-- Positive reduced and ordinary cohomology agree via the canonical map. -/
def positiveReducedCohomologyIso (X : TopCat.{v}) (q : ℕ) (hq : 0 < q) :
    ordinaryCohomology R R X (q : ℤ) ≅ reducedCohomology R X (q : ℤ) := by
  let f := ordinaryToReducedCochains R X
  haveI : IsIso (f.f (((q-1 : ℕ) : ℤ))) := ordinaryToReducedCochains_isIso_f R X (q-1)
  haveI : IsIso (f.f (q : ℤ)) := ordinaryToReducedCochains_isIso_f R X q
  haveI : IsIso (f.f (((q+1 : ℕ) : ℤ))) := ordinaryToReducedCochains_isIso_f R X (q+1)
  have hprev : (ComplexShape.down ℤ).symm.prev (q : ℤ) = ((q-1 : ℕ) : ℤ) := by
    exact (ComplexShape.down ℤ).symm.prev_eq' (by change _ + 1 = _; omega)
  have hnext : (ComplexShape.down ℤ).symm.next (q : ℤ) = ((q+1 : ℕ) : ℤ) := by
    exact (ComplexShape.down ℤ).symm.next_eq' (by change _ + 1 = _; omega)
  haveI : IsIso (f.f ((ComplexShape.down ℤ).symm.prev (q : ℤ))) := by rw [hprev]; infer_instance
  haveI : IsIso (f.f ((ComplexShape.down ℤ).symm.next (q : ℤ))) := by rw [hnext]; infer_instance
  haveI : QuasiIsoAt f (q : ℤ) := by
    rw [quasiIsoAt_iff]
    constructor
    apply ShortComplex.isIso_homologyMap_of_epi_of_isIso_of_mono'
      ((shortComplexFunctor _ _ (q : ℤ)).map f)
    · change Epi (f.f ((ComplexShape.down ℤ).symm.prev (q : ℤ)))
      rw [hprev]
      infer_instance
    · change IsIso (f.f _)
      infer_instance
    · change Mono (f.f ((ComplexShape.down ℤ).symm.next (q : ℤ)))
      rw [hnext]
      infer_instance
  exact asIso (homologyMap f (q : ℤ))

end AugmentationComparison

section KernelAlgebra
variable {R : Type u} [CommRing R]
/-- An injective map in an exact sequence identifies its source with the actual kernel. -/
def exactKernelEquiv (S : ShortComplex (ModuleCat.{v} R))
    (hS : S.Exact) (hf : Function.Injective S.f) :
    S.X₁ ≃ₗ[R] LinearMap.ker S.g.hom :=
  LinearEquiv.ofBijective S.moduleCatToCycles ⟨
    fun _ _ h => hf (congrArg Subtype.val h),
    fun x => by
      obtain ⟨a, ha⟩ := (ShortComplex.moduleCat_exact_iff S).mp hS x.val x.property
      exact ⟨a, Subtype.ext ha⟩⟩

/-- An isomorphism of the two source modules in a commuting square restricts
  to an isomorphism of kernels when the other vertical map is injective. -/
def kernelCongr {A B C D : Type v}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] [AddCommGroup D] [Module R D]
    (f : A →ₗ[R] B) (g : C →ₗ[R] D) (e : A ≃ₗ[R] C)
    (h : B →ₗ[R] D) (hh : Function.Injective h)
    (comm : g.comp e.toLinearMap = h.comp f) :
    LinearMap.ker f ≃ₗ[R] LinearMap.ker g where
  toFun a := ⟨e a, by
    change g (e a.val) = 0
    have hc := LinearMap.congr_fun comm a.val
    change g (e a.val) = h (f a.val) at hc
    rw [hc, a.property, map_zero]⟩
  invFun c := ⟨e.symm c, by
    apply hh
    have hc := LinearMap.congr_fun comm (e.symm c.val)
    change g (e (e.symm c.val)) = h (f (e.symm c.val)) at hc
    rw [e.apply_symm_apply, c.property] at hc
    simpa only [map_zero] using hc.symm⟩
  left_inv a := by apply Subtype.ext; exact e.symm_apply_apply a.val
  right_inv c := by apply Subtype.ext; exact e.apply_symm_apply c.val
  map_add' a b := by apply Subtype.ext; exact e.map_add a.val b.val
  map_smul' r a := by apply Subtype.ext; exact e.map_smul r a.val

end KernelAlgebra

section ReducedKernel
variable (R : Type u) [CommRing R]

lemma reducedCochainProjection_square (P : Pair.{v}) :
    ((dualComplexFunctor R R (.down ℤ)).map
      (P202.MayerVietoris.reducedOrdinaryRelativeIso R P).hom.op) ≫
        reducedRelativeToAbsolute R P =
      relativeToAbsolute R R P ≫ ordinaryToReducedCochains R P.space := by
  change (dualComplexFunctor R R (.down ℤ)).map
      (P202.MayerVietoris.reducedOrdinaryRelativeIso R P).hom.op ≫
        (dualComplexFunctor R R (.down ℤ)).map
          (projection (reducedFunctor R R) P).op =
    (dualComplexFunctor R R (.down ℤ)).map (projection (ordinaryFunctor R R) P).op ≫
      (dualComplexFunctor R R (.down ℤ)).map (forgetAugmentation R P.space).op
  rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp,
    forgetAugmentation_projection]

/-- The reduced connecting map identifies subspace cohomology with precisely
    the kernel of the ordinary relative-to-absolute map. -/
def reducedPairKernelEquiv (P : Pair.{v}) (p : ℕ) (hp : 0 < p)
    (h : IsZero (reducedCohomology R P.space ((p : ℤ)-1))) :
    reducedCohomology R P.sub ((p : ℤ)-1) ≃ₗ[R]
      LinearMap.ker (homologyMap (relativeToAbsolute R R P) (p : ℤ)).hom := by
  let S := reducedCochainSequence R P
  let hS := shortExact_of_degreewise_shortExact S (reducedCochainSequence_shortExact R P)
  let hij : (ComplexShape.down ℤ).symm.Rel ((p : ℤ)-1) (p : ℤ) := by
    change (p : ℤ)-1+1 = p
    omega
  haveI := hS.mono_δ ((p : ℤ)-1) (p : ℤ) hij h
  let T := ShortComplex.mk (hS.δ ((p : ℤ)-1) (p : ℤ) hij)
    (homologyMap S.f (p : ℤ)) (hS.δ_comp ((p : ℤ)-1) (p : ℤ) hij)
  let e₁ : reducedCohomology R P.sub ((p : ℤ)-1) ≃ₗ[R]
      LinearMap.ker (homologyMap S.f (p : ℤ)).hom :=
    exactKernelEquiv T (hS.homology_exact₁ ((p : ℤ)-1) (p : ℤ) hij)
      ((ModuleCat.mono_iff_injective _).mp inferInstance)
  let eRel := (reducedRelativeCohomologyIso R P (p : ℤ)).symm.toLinearEquiv
  let eAbs := (positiveReducedCohomologyIso R P.space p hp).toLinearEquiv
  have hcomm : (homologyMap S.f (p : ℤ)).hom.comp eRel.toLinearMap =
      eAbs.toLinearMap.comp (homologyMap (relativeToAbsolute R R P) (p : ℤ)).hom := by
    have hc := congrArg (fun f => homologyMap f (p : ℤ))
      (reducedCochainProjection_square R P)
    simp only [homologyMap_comp] at hc
    exact congrArg ModuleCat.Hom.hom hc
  exact e₁.trans (kernelCongr
    (homologyMap (relativeToAbsolute R R P) (p : ℤ)).hom
    (homologyMap S.f (p : ℤ)).hom eRel eAbs.toLinearMap eAbs.injective hcomm).symm

end ReducedKernel

section ExtensionComparison
open P202Specs.PoincareDuality
variable (R : Type u) [CommRing R]
lemma extension_ofSupport (d : DualityData.{u,v} R)
    (M : Type v) [TopologicalSpace M] [T2Space M]
    (U : Set M) (hU : IsOpen U) (p : ℤ) (L : Support U)
    (a : supportedCohomology R U p L) :
    d.extend M U hU p (ofSupport R U p L a) =
      ofSupport R M p (ambientSupport M U L)
        (P202.CompactSupport.extendAt R M U hU L p a) := by
  have h := d.extension_represents M U hU p L
    (P202.CompactSupport.extendAt R M U hU L p a)
  rw [P202.CompactSupport.openPullback_extendAt] at h
  exact h

lemma forgetSupport_extension_ofSupport (d : DualityData.{u,v} R)
    (M : Type v) [TopologicalSpace M] [T2Space M]
    (U : Set M) (hU : IsOpen U) (p : ℤ) (L : Support U)
    (a : supportedCohomology R U p L) :
    forgetSupport R M p (d.extend M U hU p (ofSupport R U p L a)) =
      homologyMap (cochainInclusion R M (ambientSupport M U L)) p
        (P202.CompactSupport.extendAt R M U hU L p a) := by
  rw [extension_ofSupport]
  simp only [forgetSupport, descend, ofSupport, Module.DirectLimit.lift_of]

lemma relativeToAbsolute_naturality (P Q : Pair.{v}) (f : P ⟶ Q) (p : ℤ) :
    (relativeCohomologyFunctor R R p).map f.op ≫
        homologyMap (relativeToAbsolute R R P) p =
      homologyMap (relativeToAbsolute R R Q) p ≫
        (ordinaryCohomologyFunctor R R p).map f.map.op := by
  change homologyMap ((relativeCochainFunctor R R).map f.op) p ≫
      homologyMap (relativeToAbsolute R R P) p =
    homologyMap (relativeToAbsolute R R Q) p ≫
      homologyMap ((ordinaryCochainFunctor R R).map f.map.op) p
  have h := congrArg (fun g => homologyMap g p) (cochainSequenceMap R R f).comm₁₂
  dsimp only [cochainSequenceMap, cochainSequence] at h
  simpa only [homologyMap_comp] using h


end ExtensionComparison

section RelativeExtension
open P202Specs.PoincareDuality
variable (R : Type u) [CommRing R] (d : DualityData.{u,v} R)
variable {X : Type v} [TopologicalSpace X] [T2Space X] [CompactSpace X]
variable (K : Set X) (hK : IsClosed K) (h : HasShrinkingRetraction K)

lemma compactSupportRelative_toAbsolute (p : ℤ) :
    (forgetSupport R X p).comp (d.extend X Kᶜ hK.isOpen_compl p) =
      (homologyMap (relativeToAbsolute R R (ambientPair K)) p).hom.comp
        (compactSupportRelativeIso R K hK h p).toLinearEquiv.toLinearMap := by
  apply P202.CompactSupport.hom_ext R (Kᶜ : Set X) p
  intro L
  apply LinearMap.ext
  intro a
  change forgetSupport R X p
      (d.extend X Kᶜ hK.isOpen_compl p (ofSupport R (Kᶜ : Set X) p L a)) =
    homologyMap (relativeToAbsolute R R (ambientPair K)) p
      ((compactSupportRelativeIso R K hK h p).hom (ofSupport R (Kᶜ : Set X) p L a))
  rw [forgetSupport_extension_ofSupport]
  have he := congrArg (fun f => f a) (ofSupport_compactSupportRelativeIso R K hK h p L)
  change (compactSupportRelativeIso R K hK h p).hom (ofSupport R (Kᶜ : Set X) p L a) = _ at he
  rw [he]
  have hn := relativeToAbsolute_naturality R (ambientPair K)
    (ambientPair ((supportNeighborhood K L).val : Set X))
    (ambientPairInclusion (supportNeighborhood K L).property) p
  have hi : (ordinaryCohomologyFunctor R R p).map
      (ambientPairInclusion (supportNeighborhood K L).property).map.op = 𝟙 _ := by
    change (ordinaryCohomologyFunctor R R p).map (𝟙 _) = 𝟙 _
    exact (ordinaryCohomologyFunctor R R p).map_id _
  rw [hi] at hn
  exact (congrArg (fun f => f
    (P202.CompactSupport.extendAt R X Kᶜ hK.isOpen_compl L p a)) hn).symm

end RelativeExtension


section PositiveDegrees
variable (R : Type u) [CommRing R] (d : DualityData.{u,0} R)

/-- All positive homological degrees, including n and every degree above n,
follow from the same reduced pair connecting map. -/
def positiveAlexanderEquiv (n : ℕ) (K : Set (Sphere n))
    (hn : 1 ≤ n) (hne : K.Nonempty) (hproper : K ≠ Set.univ)
    (hK : IsCompact K) (hLC : LocallyContractibleSpace K)
    (i : ℕ) (hi : 0 < i) :
    reducedHomology R R (complement n K) (i : ℤ) ≃ₗ[R]
      reducedCohomology R (TopCat.of K) ((n : ℤ) - (i : ℤ) - 1) := by
  let q : ℤ := (n : ℤ) - (i : ℤ) - 1
  have hqdeg : (n : ℤ) - (i : ℤ) = q + 1 := by dsimp [q]; omega
  let e := complementHomologyRelativeEquiv R d K hK.isClosed
    (P202.Duality.NeighborhoodCohomology.sphereShrinkingRetraction n K hn hne hproper hK hLC)
    n (complementManifold n K hK) (complementOrientation R n (by omega) K hK) (i : ℤ)
  let s : reducedCohomology R (TopCat.of K) q ≅
      relativeCohomology R R (ambientPair K) ((n : ℤ) - (i : ℤ)) := by
    rw [hqdeg]
    exact reducedPairShiftIso R (ambientPair K) q
      (sphere_reducedCohomology_concentrated R n q (by dsimp [q]; omega))
      (sphere_reducedCohomology_concentrated R n (q+1) (by dsimp [q]; omega))
  exact (P202.SingularDegreeZero.reducedPositiveIso R R (complement n K) i hi).toLinearEquiv.trans
    (e.trans s.symm.toLinearEquiv)

end PositiveDegrees


section DegreeZeroKernel
open P202Specs.SingularDegreeZero
variable (R : Type u) [CommRing R]
def componentH0Iso (X : TopCat.{v}) :
    homology R R X 0 ≅ ModuleCat.of R (ComponentSums R X) :=
  (complex R R X).extendHomologyIso (degreeEmbedding 0) (j := 0) rfl ≪≫
    P202.PoincareDuality.DegreeZero.nonnegativeHomologyZeroIso R X

lemma componentH0Iso_class (X : TopCat.{v})
    (z : (ordinaryComplex R R X).cycles 0) :
    (componentH0Iso R X).hom ((ordinaryComplex R R X).homologyπ 0 z) =
      P202.SingularDegreeZero.componentProjection R R X
        ((ordinaryNonnegativeIso R R X 0).hom ((ordinaryComplex R R X).iCycles 0 z)) := by
  let K := complex R R X
  let e := K.extendCyclesIso (degreeEmbedding 0) (j := 0) (by rfl)
  have hn := congrArg (fun f => f z)
    (K.homologyπ_extendHomologyIso_hom (degreeEmbedding 0) (j := 0) (by rfl))
  change (K.extendHomologyIso (degreeEmbedding 0) (j := 0) (by rfl)).hom
      ((ordinaryComplex R R X).homologyπ 0 z) = K.homologyπ 0 (e.hom z) at hn
  change (P202.PoincareDuality.DegreeZero.nonnegativeHomologyZeroIso R X).hom
    ((K.extendHomologyIso (degreeEmbedding 0) (j := 0) (by rfl)).hom
      ((ordinaryComplex R R X).homologyπ 0 z)) = _
  rw [hn, P202.PoincareDuality.DegreeZero.nonnegativeHomologyZeroIso_class]
  congr 1
  exact congrArg (fun f => f z)
    (K.extendCyclesIso_hom_iCycles (degreeEmbedding 0) (j := 0) (by rfl))

lemma componentH0Iso_sum_class (X : TopCat.{v})
    (z : (ordinaryComplex R R X).cycles 0) :
    componentSum R R X ((componentH0Iso R X).hom
      ((ordinaryComplex R R X).homologyπ 0 z)) =
      augmentationLinear R R X
        ((ordinaryNonnegativeIso R R X 0).hom ((ordinaryComplex R R X).iCycles 0 z)) := by
  rw [componentH0Iso_class]
  exact congrArg (fun f => ULift.down (f
    ((ordinaryNonnegativeIso R R X 0).hom ((ordinaryComplex R R X).iCycles 0 z))))
      (P202.SingularDegreeZero.componentProjection_sum R R X)

lemma augmentationH0_map {X Y : TopCat.{v}} [PathConnectedSpace Y] (f : X ⟶ Y)
    (a : homology R R X 0) :
    P202.PoincareDuality.DegreeZero.augmentationH0Equiv R Y
      ((homologyFunctor R R 0).map f a) =
      componentSum R R X ((componentH0Iso R X).hom a) := by
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((ordinaryComplex R R X).homologyπ 0)).mp inferInstance a
  let F := (ordinaryFunctor R R).map f
  have hn := congrArg (fun g => g z) (homologyπ_naturality F 0)
  change (homologyFunctor R R 0).map f ((ordinaryComplex R R X).homologyπ 0 z) =
    (ordinaryComplex R R Y).homologyπ 0 (cyclesMap F 0 z) at hn
  rw [hn, P202.PoincareDuality.DegreeZero.augmentationH0Equiv_class,
    componentH0Iso_sum_class]
  have hc := congrArg (fun g => g z) (cyclesMap_i F 0)
  change (ordinaryComplex R R Y).iCycles 0 (cyclesMap F 0 z) =
    F.f 0 ((ordinaryComplex R R X).iCycles 0 z) at hc
  rw [hc]
  have hf : F.f 0 ≫ (ordinaryNonnegativeIso R R Y 0).hom =
      (ordinaryNonnegativeIso R R X 0).hom ≫ (chainMap R R f).f 0 := by
    change (extendMap (chainMap R R f) (degreeEmbedding 0)).f 0 ≫ _ = _
    rw [extendMap_f _ _ (show (degreeEmbedding 0).f 0 = (0 : ℤ) from rfl)]
    simp [ordinaryNonnegativeIso]
  have he := congrArg (fun g => ULift.down (g
    ((ordinaryNonnegativeIso R R X 0).hom ((ordinaryComplex R R X).iCycles 0 z))))
    (augmentation_naturality R R f)
  change augmentationLinear R R Y ((chainMap R R f).f 0
    ((ordinaryNonnegativeIso R R X 0).hom ((ordinaryComplex R R X).iCycles 0 z))) = _ at he
  have hf' := congrArg (fun g => g ((ordinaryComplex R R X).iCycles 0 z)) hf
  change (ordinaryNonnegativeIso R R Y 0).hom
      (F.f 0 ((ordinaryComplex R R X).iCycles 0 z)) =
    (chainMap R R f).f 0
      ((ordinaryNonnegativeIso R R X 0).hom ((ordinaryComplex R R X).iCycles 0 z)) at hf'
  rw [hf']
  exact he


def componentKernelH0Equiv {X Y : TopCat.{v}} [PathConnectedSpace Y] (f : X ⟶ Y) :
    LinearMap.ker (componentSum R R X) ≃ₗ[R]
      LinearMap.ker ((homologyFunctor R R 0).map f).hom := by
  let e := (componentH0Iso R X).toLinearEquiv
  exact {
    toFun := fun c => ⟨e.symm c.val, by
      apply (P202.PoincareDuality.DegreeZero.augmentationH0Equiv R Y).injective
      change P202.PoincareDuality.DegreeZero.augmentationH0Equiv R Y
        ((homologyFunctor R R 0).map f (e.symm c.val)) =
        P202.PoincareDuality.DegreeZero.augmentationH0Equiv R Y 0
      rw [augmentationH0_map, map_zero]
      change componentSum R R X (e (e.symm c.val)) = 0
      rw [e.apply_symm_apply]
      exact c.property⟩
    invFun := fun a => ⟨e a.val, by
      have h := augmentationH0_map R f a.val
      rw [show (homologyFunctor R R 0).map f a.val = 0 from a.property, map_zero] at h
      exact h.symm⟩
    left_inv := fun c => by
      apply Subtype.ext
      change e (e.symm c.val) = c.val
      exact e.apply_symm_apply c.val
    right_inv := fun a => by
      apply Subtype.ext
      change e.symm (e a.val) = a.val
      exact e.symm_apply_apply a.val
    map_add' := fun a b => by
      apply Subtype.ext
      exact e.symm.map_add _ _
    map_smul' := fun a b => by
      apply Subtype.ext
      exact e.symm.map_smul _ _ }

/-- For any map into a path connected space, reduced degree-zero finite singular
homology is exactly the kernel of its ordinary degree-zero homology map. -/
def reducedH0KernelEquiv {X Y : TopCat.{v}} [PathConnectedSpace Y] (f : X ⟶ Y) :
    reducedHomology R R X 0 ≃ₗ[R]
      LinearMap.ker ((homologyFunctor R R 0).map f).hom :=
  (Classical.choice (P202.SingularDegreeZero.reducedDegreeZero R R X)).trans
    (componentKernelH0Equiv R f)


def reducedH0OpenKernelEquiv (M : Type v) [TopologicalSpace M]
    [PathConnectedSpace M] (U : Set M) :
    reducedHomology R R (TopCat.of U) 0 ≃ₗ[R]
      LinearMap.ker (openHomology R M U 0) :=
  reducedH0KernelEquiv R (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)


end DegreeZeroKernel

section ZeroDegree
open P202Specs.PoincareDuality
variable (R : Type u) [CommRing R] (d : DualityData.{u,0} R)

/-- At degree zero the cap naturality square restricts duality to the two
kernels. Both kernels use their actual singular-theory maps. -/
def zeroAlexanderEquiv (n : ℕ) (K : Set (Sphere n))
    (hn : 1 ≤ n) (hne : K.Nonempty) (hproper : K ≠ Set.univ)
    (hK : IsCompact K) (hLC : LocallyContractibleSpace K) :
    reducedHomology R R (complement n K) 0 ≃ₗ[R]
      reducedCohomology R (TopCat.of K) ((n : ℤ)-1) := by
  haveI : PathConnectedSpace (TopCat.of (Sphere n)) := by
    cases n with
    | zero => omega
    | succ m => exact P202.SpheresDisks.sphere_pathConnected m
  let A := sphereManifold n
  let o := sphereOrientation R n (by omega)
  let AU := complementManifold n K hK
  let oU := complementOrientation R n (by omega) K hK
  let hret := P202.Duality.NeighborhoodCohomology.sphereShrinkingRetraction
    n K hn hne hproper hK hLC
  let eU := LinearEquiv.ofBijective (d.D n (Kᶜ : Set (Sphere n)) AU oU (n : ℤ))
    (P202.PoincareDuality.duality R d n (Kᶜ : Set (Sphere n)) AU oU (n : ℤ))
  let eS := LinearEquiv.ofBijective (d.D n (Sphere n) A o (n : ℤ))
    (P202.PoincareDuality.duality R d n (Sphere n) A o (n : ℤ))
  let sRel := sphereCompactSupportRelativeEquiv R n K hn hne hproper hK hLC (n : ℤ)
  let sAbs := LinearEquiv.ofBijective (forgetSupport R (Sphere n) (n : ℤ))
    (P202.PoincareDuality.forgetSupport_bijective R (Sphere n) isCompact_univ (n : ℤ))
  let e := eU.symm.trans sRel
  let h := eS.symm.trans sAbs
  let f := openHomology R (Sphere n) Kᶜ ((n : ℤ)-(n : ℤ))
  let g := (homologyMap (relativeToAbsolute R R (ambientPair K)) (n : ℤ)).hom
  have hcomm : g.comp e.toLinearMap = h.toLinearMap.comp f := by
    apply LinearMap.ext
    intro a
    change g (sRel (eU.symm a)) = sAbs (eS.symm (f a))
    have hnat := d.naturality n (Sphere n) A o Kᶜ hK.isClosed.isOpen_compl AU oU
      (complementOrientation_compatible R n (by omega) K hK) (n : ℤ) (eU.symm a)
    change f (eU (eU.symm a)) =
      eS (d.extend (Sphere n) Kᶜ hK.isClosed.isOpen_compl (n : ℤ) (eU.symm a)) at hnat
    rw [eU.apply_symm_apply] at hnat
    rw [hnat, eS.symm_apply_apply]
    exact (LinearMap.congr_fun
      (compactSupportRelative_toAbsolute R d K hK.isClosed hret (n : ℤ)) (eU.symm a)).symm
  have kUdegree (q : ℤ) (hq : q = 0) :
      reducedHomology R R (complement n K) 0 ≃ₗ[R]
        LinearMap.ker (openHomology R (Sphere n) Kᶜ q) := by
    subst q
    exact reducedH0KernelEquiv R (TopCat.ofHom
      (show C((Kᶜ : Set (Sphere n)), Sphere n) from ⟨Subtype.val, continuous_subtype_val⟩))
  let kU : reducedHomology R R (complement n K) 0 ≃ₗ[R] LinearMap.ker f :=
    kUdegree _ (sub_self _)
  let kK := reducedPairKernelEquiv R (ambientPair K) n (by omega)
    (sphere_reducedCohomology_concentrated R n ((n : ℤ)-1) (by omega))
  exact kU.trans ((kernelCongr f g e h.toLinearMap h.injective hcomm).trans kK.symm)

end ZeroDegree

/-- Alexander duality for every commutative coefficient ring, hence for both
coefficient choices in the source. -/
theorem holds (R : Type u) [CommRing R] : Holds R := by
  intro n K hn hne hproper hK hLC i
  let d : DualityData.{u,0} R := Classical.choice (P202.CompactSupport.construction R)
  by_cases hi : i = 0
  · subst i
    change Nonempty (reducedHomology R R (complement n K) 0 ≃ₗ[R]
      reducedCohomology R (TopCat.of K) ((n : ℤ)-(0 : ℤ)-1))
    rw [sub_zero]
    exact ⟨zeroAlexanderEquiv R d n K hn hne hproper hK hLC⟩
  · exact ⟨positiveAlexanderEquiv R d n K hn hne hproper hK hLC i (by omega)⟩

/-- Integral Alexander duality, with every endpoint retained. -/
theorem integral : P202Specs.AlexanderDuality.Expected.integral := holds ℤ

/-- Alexander duality with any fixed field coefficients. -/
theorem field : P202Specs.AlexanderDuality.Expected.field.{u} := by
  intro F _
  exact holds F

end P202.AlexanderDuality
