import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.GoodPairQuotient
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.RelativeSingularChains
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.PrismHomotopy
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.SingularDegreeZero
import Mathlib.Topology.Homeomorph.Lemmas

import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.Excision
/-! Conditional proof of paper.tex 1340–1372. Excision is available only as the
explicit ordered premises on conditional helpers; its implementation is
deliberately not imported. The original closed target wrappers are left to
the owner after actual upstream dependency closure. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex Topology
universe u v
namespace P202.GoodPairQuotient
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.GoodPairQuotient

lemma quotient_eq_iff (P : Pair.{v}) (x y : P.space) :
    quotientProjection P x = quotientProjection P y ↔
      x = y ∨ (x ∈ P.subspace ∧ y ∈ P.subspace) :=
  Quotient.eq

lemma quotientProjection_surjective (P : Pair.{v}) :
    Function.Surjective (quotientProjection P) := Quotient.mk_surjective

lemma quotientProjection_isQuotientMap (P : Pair.{v}) :
    IsQuotientMap (quotientProjection P) := isQuotientMap_quot_mk

lemma quotient_preimage_subspace (P : Pair.{v}) :
    quotientProjection P ⁻¹' (quotientPair P).subspace = P.subspace := by
  ext x
  constructor
  · rintro ⟨a, ha, heq⟩
    rcases (quotient_eq_iff P a x).mp heq with rfl | ⟨_, hx⟩
    · exact ha
    · exact hx
  · intro hx
    exact ⟨x, hx, rfl⟩

lemma quotient_subspace_singleton (P : Pair.{v}) (a : P.subspace) :
    (quotientPair P).subspace = {quotientProjection P a} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (quotient_eq_iff P x a).mpr (Or.inr ⟨hx, a.property⟩)
  · rintro rfl
    exact ⟨a.val, a.property, rfl⟩

/-- Closedness of the collapsed singleton needs only closedness of `A`,
not any separation property of `X`. -/
lemma quotient_subspace_closed (P : Pair.{v}) (h : IsClosed P.subspace) :
    IsClosed (quotientPair P).subspace := by
  rw [← (quotientProjection_isQuotientMap P).isClosed_preimage,
    quotient_preimage_subspace]
  exact h

lemma quotient_preimage_neighborhood (P : Pair.{v}) (W : Set P.space)
    (hAW : P.subspace ⊆ W) :
    quotientProjection P ⁻¹' (quotientProjection P '' W) = W := by
  ext x
  constructor
  · rintro ⟨w, hw, heq⟩
    rcases (quotient_eq_iff P w x).mp heq with rfl | ⟨_, hx⟩
    · exact hw
    · exact hAW hx
  · intro hx
    exact ⟨x, hx, rfl⟩

lemma quotient_neighborhood_open (P : Pair.{v}) (W : Set P.space)
    (hAW : P.subspace ⊆ W) (hW : IsOpen W) :
    IsOpen (quotientProjection P '' W) := by
  rw [← (quotientProjection_isQuotientMap P).isOpen_preimage,
    quotient_preimage_neighborhood P W hAW]
  exact hW

/-- The actual restriction of the quotient map off the collapsed subspace. -/
def outsideMap (P : Pair.{v}) :
    {x : P.space // x ∉ P.subspace} →
      {y : quotientSpace P // y ∉ (quotientPair P).subspace} :=
  fun x => ⟨quotientProjection P x.val, by
    intro h
    apply x.property
    have hx : x.val ∈ quotientProjection P ⁻¹' (quotientPair P).subspace := h
    rwa [quotient_preimage_subspace] at hx⟩

lemma outsideMap_injective (P : Pair.{v}) : Function.Injective (outsideMap P) := by
  intro x y h
  have hq := congrArg Subtype.val h
  rcases (quotient_eq_iff P x.val y.val).mp hq with heq | ⟨hx, _⟩
  · exact Subtype.ext heq
  · exact (x.property hx).elim

lemma outsideMap_isQuotientMap (P : Pair.{v}) (hA : IsClosed P.subspace) :
    IsQuotientMap (outsideMap P) := by
  let S := (quotientPair P).subspaceᶜ
  have hS : IsOpen S := (quotient_subspace_closed P hA).isOpen_compl
  have hpre : P.subspaceᶜ = quotientProjection P ⁻¹' S := by
    rw [Set.preimage_compl, quotient_preimage_subspace]
  let e := Homeomorph.setCongr hpre
  exact ((quotientProjection_isQuotientMap P).restrictPreimage_isOpen hS).comp
    e.isQuotientMap

/-- No Hausdorff assumption is used: closedness makes the saturated complement
open, so the restriction is both a quotient map and a bijection. -/
def outsideHomeomorph (P : Pair.{v}) (hA : IsClosed P.subspace) :
    {x : P.space // x ∉ P.subspace} ≃ₜ
      {y : quotientSpace P // y ∉ (quotientPair P).subspace} :=
  (isHomeomorph_iff_isQuotientMap_injective.mpr
    ⟨outsideMap_isQuotientMap P hA, outsideMap_injective P⟩).homeomorph (outsideMap P)

@[simp] lemma outsideHomeomorph_apply (P : Pair.{v}) (hA : IsClosed P.subspace)
    (x : {x : P.space // x ∉ P.subspace}) :
    (outsideHomeomorph P hA x).val = quotientProjection P x.val := rfl

/-- The first excision is exactly removal of `A` from `(X,W)`. -/
def neighborhoodExcision (D : Data.{v}) : P202Specs.Excision.Data.{v} where
  pair := ⟨D.pair.space, D.neighborhood⟩
  removed := D.pair.subspace
  subset := D.subset_neighborhood
  closure_subset := by
    rw [D.closed.closure_eq, D.open_neighborhood.interior_eq]
    exact D.subset_neighborhood

/-- The second excision removes the collapsed singleton from `(X/A,W/A)`. -/
def quotientNeighborhoodExcision (D : Data.{v}) : P202Specs.Excision.Data.{v} where
  pair := ⟨quotientSpace D.pair, quotientProjection D.pair '' D.neighborhood⟩
  removed := (quotientPair D.pair).subspace
  subset := Set.image_mono D.subset_neighborhood
  closure_subset := by
    rw [(quotient_subspace_closed D.pair D.closed).closure_eq,
      (quotient_neighborhood_open D.pair D.neighborhood D.subset_neighborhood
        D.open_neighborhood).interior_eq]
    exact Set.image_mono D.subset_neighborhood

def neighborhoodExcisionMap (D : Data.{v}) :
    P202Specs.Excision.Map (neighborhoodExcision D) (quotientNeighborhoodExcision D) where
  pairMap := ⟨quotientProjection D.pair, fun x hx => ⟨x, hx, rfl⟩⟩
  outside := by
    intro x hx hq
    apply hx
    have h : x ∈ quotientProjection D.pair ⁻¹' (quotientPair D.pair).subspace := hq
    rwa [quotient_preimage_subspace] at h

/-- A homeomorphism respecting the two subspaces is an isomorphism of pairs. -/
def pairIsoOfHomeomorph (P Q : Pair.{v}) (e : P.space ≃ₜ Q.space)
    (he : ∀ x, x ∈ P.subspace ↔ e x ∈ Q.subspace) : P ≅ Q where
  hom := ⟨TopCat.ofHom ⟨e, e.continuous⟩, fun x hx => (he x).mp hx⟩
  inv := ⟨TopCat.ofHom ⟨e.symm, e.symm.continuous⟩, fun y hy =>
    (he (e.symm y)).mpr (by simpa using hy)⟩
  hom_inv_id := by
    apply PairMap.ext
    ext x
    exact e.symm_apply_apply x
  inv_hom_id := by
    apply PairMap.ext
    ext y
    exact e.apply_symm_apply y

/-- The two excised pairs in the source proof are homeomorphic by `q`. -/
def excisedPairIso (D : Data.{v}) :
    (neighborhoodExcision D).excised ≅ (quotientNeighborhoodExcision D).excised :=
  pairIsoOfHomeomorph _ _ (outsideHomeomorph D.pair D.closed) (by
    intro x
    change x.val ∈ D.neighborhood ↔
      quotientProjection D.pair x.val ∈ quotientProjection D.pair '' D.neighborhood
    have h := Set.ext_iff.mp
      (quotient_preimage_neighborhood D.pair D.neighborhood D.subset_neighborhood) x.val
    exact h.symm)

lemma excisedPairIso_hom (D : Data.{v}) :
    (excisedPairIso D).hom = (neighborhoodExcisionMap D).excised := by
  apply PairMap.ext
  rfl

/-- The central excision step: `(X,W) → (X/A,W/A)` induces isomorphisms.
Both conditional assumptions retain their full universally quantified types. -/
theorem neighborhood_quotient_isIso_conditional
    (excision : P202Specs.Excision.isomorphism_type.{u,v})
    (naturality : P202Specs.Excision.naturality_type.{u,v})
    (R : Type u) [CommRing R] (D : Data.{v}) (n : ℕ) :
    IsIso (homologyMap
      (relativeMap (chainFunctor R R) (neighborhoodExcisionMap D).pairMap) n) := by
  haveI : IsIso (neighborhoodExcisionMap D).excised := by
    rw [← excisedPairIso_hom]
    infer_instance
  haveI := excision R (neighborhoodExcision D) n
  haveI := excision R (quotientNeighborhoodExcision D) n
  let F := relativeFunctor (chainFunctor R R) ⋙
    HomologicalComplex.homologyFunctor _ _ n
  haveI : IsIso (homologyMap
      (relativeMap (chainFunctor R R) (neighborhoodExcisionMap D).excised) n) :=
    F.map_isIso _
  haveI : IsIso (homologyMap
      (relativeMap (chainFunctor R R) (neighborhoodExcision D).inclusion) n ≫
      homologyMap (relativeMap (chainFunctor R R) (neighborhoodExcisionMap D).pairMap) n) := by
    rw [naturality R _ _ (neighborhoodExcisionMap D) n]
    infer_instance
  exact IsIso.of_isIso_comp_left
    (homologyMap (relativeMap (chainFunctor R R) (neighborhoodExcision D).inclusion) n) _

/-- The relative projection is a reduced homology isomorphism whenever the
subspace has zero reduced homology. This includes degree zero. -/
lemma reduced_projection_isIso (R : Type u) [CommRing R] (P : Pair.{v})
    (h : ∀ i : ℤ, IsZero (reducedHomology R R P.sub i)) (n : ℤ) :
    IsIso (homologyMap (projection (reducedFunctor R R) P) n) := by
  let hs := HomologicalComplex.shortExact_of_degreewise_shortExact
    (sequence (reducedFunctor R R) P) (P202.RelativeSingularChains.reduced_short_exact R R P)
  haveI : Mono (homologyMap (projection (reducedFunctor R R) P) n) :=
    (hs.homology_exact₂ n).mono_g ((h n).eq_of_src _ _)
  haveI : Epi (homologyMap (projection (reducedFunctor R R) P) n) :=
    (hs.homology_exact₃ n (n-1) (by change n - 1 + 1 = n; omega)).epi_f
      ((h (n-1)).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- The collapsed subspace is an actual nonempty one-point space. -/
lemma quotient_subspace_reduced_isZero (R : Type u) [CommRing R]
    (P : Pair.{v}) (hA : P.subspace.Nonempty) (n : ℤ) :
    IsZero (reducedHomology R R (quotientPair P).sub n) := by
  obtain ⟨a, ha⟩ := hA
  haveI : Nonempty (quotientPair P).sub := ⟨⟨quotientProjection P a, a, ha, rfl⟩⟩
  haveI : Subsingleton (quotientPair P).sub := by
    constructor
    intro x y
    apply Subtype.ext
    have hs := quotient_subspace_singleton P ⟨a, ha⟩
    have hx := (Set.ext_iff.mp hs x.val).mp x.property
    have hy := (Set.ext_iff.mp hs y.val).mp y.property
    exact hx.trans hy.symm
  exact P202.PrismHomotopy.contractible R R (quotientPair P).sub n

lemma quotient_reduced_projection_isIso (R : Type u) [CommRing R]
    (P : Pair.{v}) (hA : P.subspace.Nonempty) (n : ℤ) :
    IsIso (homologyMap (projection (reducedFunctor R R) (quotientPair P)) n) :=
  reduced_projection_isIso R (quotientPair P) (quotient_subspace_reduced_isZero R P hA) n

/-- Restrict `q` to the open neighborhood, keeping its actual image topology. -/
def neighborhoodProjection (D : Data.{v}) :
    C(D.neighborhood, quotientProjection D.pair '' D.neighborhood) :=
  ⟨fun x => ⟨quotientProjection D.pair x.val, x.val, x.property, rfl⟩,
    ((quotientProjection D.pair).hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

lemma neighborhoodProjection_isQuotientMap (D : Data.{v}) :
    IsQuotientMap (neighborhoodProjection D) := by
  let S := quotientProjection D.pair '' D.neighborhood
  have hS : IsOpen S := quotient_neighborhood_open D.pair D.neighborhood
    D.subset_neighborhood D.open_neighborhood
  let e := Homeomorph.setCongr
    (quotient_preimage_neighborhood D.pair D.neighborhood D.subset_neighborhood).symm
  exact ((quotientProjection_isQuotientMap D.pair).restrictPreimage_isOpen hS).comp
    e.isQuotientMap

lemma deformation_respects_fibers (D : Data.{v}) (t : unitInterval)
    (x y : D.neighborhood)
    (h : neighborhoodProjection D x = neighborhoodProjection D y) :
    neighborhoodProjection D (D.deformation (t, x)) =
      neighborhoodProjection D (D.deformation (t, y)) := by
  have hq := congrArg Subtype.val h
  rcases (quotient_eq_iff D.pair x.val y.val).mp hq with heq | ⟨hx, hy⟩
  · have : x = y := Subtype.ext heq
    rw [this]
  · rw [D.fixes t x hx, D.fixes t y hy]
    exact h

/-- A set-theoretic description of the descended deformation. Continuity is
proved below using the quotient property after multiplying by the interval. -/
def quotientDeformationValue (D : Data.{v})
    (p : unitInterval × (quotientProjection D.pair '' D.neighborhood)) :
    quotientProjection D.pair '' D.neighborhood :=
  neighborhoodProjection D (D.deformation (p.1,
    Function.surjInv (neighborhoodProjection_isQuotientMap D).surjective p.2))

lemma quotientDeformationValue_projection (D : Data.{v}) (t : unitInterval)
    (x : D.neighborhood) :
    quotientDeformationValue D (t, neighborhoodProjection D x) =
      neighborhoodProjection D (D.deformation (t, x)) :=
  deformation_respects_fibers D t _ x
    (Function.surjInv_eq (neighborhoodProjection_isQuotientMap D).surjective _)

lemma quotientDeformationValue_continuous (D : Data.{v}) :
    Continuous (quotientDeformationValue D) := by
  apply (neighborhoodProjection_isQuotientMap D).continuous_lift_prod_right
  have h : (fun p : unitInterval × D.neighborhood =>
      quotientDeformationValue D (p.1, neighborhoodProjection D p.2)) =
      fun p => neighborhoodProjection D (D.deformation p) := by
    funext p
    exact quotientDeformationValue_projection D p.1 p.2
  rw [h]
  exact (neighborhoodProjection D).continuous.comp D.deformation.continuous

/-- The strong deformation on `W` descends to a contraction of `W/A`. -/
def quotientNeighborhoodContraction (D : Data.{v}) (a : D.pair.subspace) :
    ContinuousMap.Homotopy
      (ContinuousMap.id (quotientProjection D.pair '' D.neighborhood))
      (ContinuousMap.const _
        (neighborhoodProjection D ⟨a.val, D.subset_neighborhood a.property⟩)) where
  toFun := quotientDeformationValue D
  continuous_toFun := quotientDeformationValue_continuous D
  map_zero_left y := by
    obtain ⟨x, rfl⟩ := (neighborhoodProjection_isQuotientMap D).surjective y
    rw [quotientDeformationValue_projection, D.at_zero]
    rfl
  map_one_left y := by
    obtain ⟨x, rfl⟩ := (neighborhoodProjection_isQuotientMap D).surjective y
    rw [quotientDeformationValue_projection]
    apply Subtype.ext
    exact (quotient_eq_iff D.pair _ a.val).mpr (Or.inr ⟨D.at_one x, a.property⟩)

lemma quotientNeighborhood_contractible (D : Data.{v}) :
    ContractibleSpace (quotientProjection D.pair '' D.neighborhood) := by
  obtain ⟨a, ha⟩ := D.nonempty
  exact (contractible_iff_id_nullhomotopic _).mpr
    ⟨_, ⟨quotientNeighborhoodContraction D ⟨a, ha⟩⟩⟩

lemma nonnegative_homotopy_isIso (R : Type u) [CommRing R]
    {X Y : TopCat.{v}} (f : X ⟶ Y) (g : Y ⟶ X)
    (hfg : TopCat.Homotopy (f ≫ g) (𝟙 X))
    (hgf : TopCat.Homotopy (g ≫ f) (𝟙 Y)) (n : ℕ) :
    IsIso (homologyMap (chainMap R R f) n) := by
  let F := chainFunctor R R ⋙ HomologicalComplex.homologyFunctor _ _ n
  change IsIso (F.map f)
  have h₁ : F.map (f ≫ g) = F.map (𝟙 X) :=
    ((P202.PrismHomotopy.chainPrism R R hfg).homologyMap_eq n).symm
  have h₂ : F.map (g ≫ f) = F.map (𝟙 Y) :=
    ((P202.PrismHomotopy.chainPrism R R hgf).homologyMap_eq n).symm
  exact ⟨⟨F.map g, by simpa using h₁, by simpa using h₂⟩⟩

/-- The five-lemma consequence of the pair sequence, with the actual pair map. -/
lemma relativeMap_isIso_of_absolute (R : Type u) [CommRing R]
    {P Q : Pair.{v}} (f : P ⟶ Q)
    (hsub : ∀ n, IsIso (homologyMap (chainMap R R f.restrict) n))
    (hspace : ∀ n, IsIso (homologyMap (chainMap R R f.map) n)) (n : ℕ) :
    IsIso (homologyMap (relativeMap (chainFunctor R R) f) n) := by
  let hs P := HomologicalComplex.shortExact_of_degreewise_shortExact
    (sequence (chainFunctor R R) P)
    (P202.RelativeSingularChains.sequence_shortExact (chainFunctor R R) P)
  apply HomologicalComplex.HomologySequence.isIso_homologyMap_τ₃
    (sequenceMap (chainFunctor R R) f) (hs P) (hs Q) n
  · have := hsub n
    change Epi (homologyMap (chainMap R R f.restrict) n)
    infer_instance
  · exact hspace n
  · intro j _
    exact hsub j
  · intro j _
    have := hspace j
    change Mono (homologyMap (chainMap R R f.map) j)
    infer_instance

def enlargePairMap (D : Data.{v}) : D.pair ⟶ (neighborhoodExcision D).pair :=
  ⟨𝟙 _, D.subset_neighborhood⟩

def neighborhoodRetraction (D : Data.{v}) :
    (neighborhoodExcision D).pair.sub ⟶ D.pair.sub :=
  TopCat.ofHom ⟨fun x => ⟨(D.deformation (1, x)).val, D.at_one x⟩,
    (continuous_subtype_val.comp
      (D.deformation.continuous.comp (continuous_const.prodMk continuous_id))).subtype_mk _⟩

def neighborhoodRetraction_homotopy (D : Data.{v}) :
    TopCat.Homotopy (𝟙 (neighborhoodExcision D).pair.sub)
      (neighborhoodRetraction D ≫ (enlargePairMap D).restrict) where
  toFun := D.deformation
  continuous_toFun := D.deformation.continuous
  map_zero_left := D.at_zero
  map_one_left _ := by apply Subtype.ext; rfl

def neighborhoodRetraction_restrict_homotopy (D : Data.{v}) :
    TopCat.Homotopy ((enlargePairMap D).restrict ≫ neighborhoodRetraction D)
      (𝟙 D.pair.sub) where
  toFun := fun p => p.2
  continuous_toFun := continuous_snd
  map_zero_left a := by
    apply Subtype.ext
    exact (congrArg Subtype.val
      (D.fixes 1 ⟨a.val, D.subset_neighborhood a.property⟩ a.property)).symm
  map_one_left _ := rfl

lemma enlargePairMap_isIso (R : Type u) [CommRing R] (D : Data.{v}) (n : ℕ) :
    IsIso (homologyMap (relativeMap (chainFunctor R R) (enlargePairMap D)) n) := by
  apply relativeMap_isIso_of_absolute R (enlargePairMap D)
  · intro k
    exact nonnegative_homotopy_isIso R _ (neighborhoodRetraction D)
      (neighborhoodRetraction_restrict_homotopy D)
      (neighborhoodRetraction_homotopy D).symm k
  · intro k
    exact (chainFunctor R R ⋙ HomologicalComplex.homologyFunctor _ _ k).map_isIso
      (𝟙 D.pair.space)

def quotientEnlargePairMap (D : Data.{v}) :
    quotientPair D.pair ⟶ (quotientNeighborhoodExcision D).pair :=
  ⟨𝟙 _, Set.image_mono D.subset_neighborhood⟩

def quotientNeighborhoodRetraction (D : Data.{v}) (a : D.pair.subspace) :
    (quotientNeighborhoodExcision D).pair.sub ⟶ (quotientPair D.pair).sub :=
  TopCat.ofHom (ContinuousMap.const _ ⟨quotientProjection D.pair a.val,
    a.val, a.property, rfl⟩)

def quotientNeighborhoodRetraction_homotopy (D : Data.{v}) (a : D.pair.subspace) :
    TopCat.Homotopy (𝟙 (quotientNeighborhoodExcision D).pair.sub)
      (quotientNeighborhoodRetraction D a ≫ (quotientEnlargePairMap D).restrict) :=
  quotientNeighborhoodContraction D a

def quotientNeighborhoodRetraction_restrict_homotopy (D : Data.{v})
    (a : D.pair.subspace) :
    TopCat.Homotopy ((quotientEnlargePairMap D).restrict ≫ quotientNeighborhoodRetraction D a)
      (𝟙 (quotientPair D.pair).sub) where
  toFun := fun p => p.2
  continuous_toFun := continuous_snd
  map_zero_left y := by
    apply Subtype.ext
    have hy := (Set.ext_iff.mp (quotient_subspace_singleton D.pair a) y.val).mp y.property
    exact hy
  map_one_left _ := rfl

lemma quotientEnlargePairMap_isIso (R : Type u) [CommRing R]
    (D : Data.{v}) (n : ℕ) :
    IsIso (homologyMap (relativeMap (chainFunctor R R) (quotientEnlargePairMap D)) n) := by
  obtain ⟨a, ha⟩ := D.nonempty
  apply relativeMap_isIso_of_absolute R (quotientEnlargePairMap D)
  · intro k
    exact nonnegative_homotopy_isIso R _ (quotientNeighborhoodRetraction D ⟨a, ha⟩)
      (quotientNeighborhoodRetraction_restrict_homotopy D ⟨a, ha⟩)
      (quotientNeighborhoodRetraction_homotopy D ⟨a, ha⟩).symm k
  · intro k
    exact (chainFunctor R R ⋙ HomologicalComplex.homologyFunctor _ _ k).map_isIso
      (𝟙 (quotientSpace D.pair))

/-- The quotient projection induces isomorphisms on ordinary relative homology.
The reduced-absolute identification is assembled below using compatible degree
coordinates, so this intermediate assertion already uses the actual map. -/
theorem relative_quotient_isIso_conditional
    (excision : P202Specs.Excision.isomorphism_type.{u,v})
    (naturality : P202Specs.Excision.naturality_type.{u,v})
    (R : Type u) [CommRing R] (D : Data.{v}) (n : ℕ) :
    IsIso (homologyMap (relativeMap (chainFunctor R R) (quotientPairMap D.pair)) n) := by
  let F := relativeFunctor (chainFunctor R R) ⋙
    HomologicalComplex.homologyFunctor _ _ n
  have hsquare : enlargePairMap D ≫ (neighborhoodExcisionMap D).pairMap =
      quotientPairMap D.pair ≫ quotientEnlargePairMap D := by
    apply PairMap.ext
    rfl
  haveI : IsIso (F.map (enlargePairMap D)) := enlargePairMap_isIso R D n
  haveI : IsIso (F.map (quotientEnlargePairMap D)) := quotientEnlargePairMap_isIso R D n
  haveI : IsIso (F.map (neighborhoodExcisionMap D).pairMap) :=
    neighborhood_quotient_isIso_conditional excision naturality R D n
  haveI : IsIso (F.map (quotientPairMap D.pair) ≫ F.map (quotientEnlargePairMap D)) := by
    rw [← F.map_comp, ← hsquare, F.map_comp]
    infer_instance
  exact IsIso.of_isIso_comp_right (F.map (quotientPairMap D.pair))
    (F.map (quotientEnlargePairMap D))

/-- A complex zero in negative degrees is recovered from its nonnegative
degree coordinates. This bridge retains the specified coordinates. -/
def nonnegativeExtensionIso {C : Type*} [Category* C] [HasZeroMorphisms C]
    [HasZeroObject C] (K : ChainComplex C ℤ) (L : ChainComplex C ℕ)
    (e : ∀ n : ℕ, K.X (n : ℤ) ≅ L.X n)
    (hneg : ∀ i : ℤ, i < 0 → IsZero (K.X i))
    (hd : ∀ n : ℕ, (e (n+1)).inv ≫ K.d ((n+1 : ℕ) : ℤ) (n : ℤ) ≫
      (e n).hom = L.d (n+1) n) : K ≅ L.extend (degreeEmbedding 0) := by
  let E : ∀ i : ℤ, K.X i ≅ (L.extend (degreeEmbedding 0)).X i := fun i =>
    match i with
    | .ofNat n => e n ≪≫ (L.extendXIso (degreeEmbedding 0)
        (show (degreeEmbedding 0).f n = (n : ℤ) by change (0 : ℤ) + n = n; omega)).symm
    | .negSucc n => (hneg _ (by omega)).iso
        (L.isZero_extend_X (degreeEmbedding 0) _ (by
          intro j hj
          change (0 : ℤ) + j = Int.negSucc n at hj
          omega))
  refine HomologicalComplex.Hom.isoOfComponents E ?_
  intro i j hij
  cases j with
  | negSucc k =>
    exact (L.isZero_extend_X (degreeEmbedding 0) _ (by
      intro m hm
      change (0 : ℤ) + m = Int.negSucc k at hm
      omega)).eq_of_tgt _ _
  | ofNat n =>
    have hi : i = ((n+1 : ℕ) : ℤ) := by
      change (n : ℤ) + 1 = i at hij
      omega
    clear hij
    subst i
    change ((e (n+1)).hom ≫ (L.extendXIso (degreeEmbedding 0)
      (show (degreeEmbedding 0).f (n+1) = ((n+1 : ℕ) : ℤ) by
        change (0 : ℤ) + (n+1 : ℕ) = (n+1 : ℕ); omega)).inv) ≫
        (L.extend (degreeEmbedding 0)).d ((n+1 : ℕ) : ℤ) (n : ℤ) =
      K.d ((n+1 : ℕ) : ℤ) (n : ℤ) ≫ (e n).hom ≫
        (L.extendXIso (degreeEmbedding 0)
          (show (degreeEmbedding 0).f n = (n : ℤ) by change (0 : ℤ) + n = n; omega)).inv
    rw [L.extend_d_eq (degreeEmbedding 0)
      (show (degreeEmbedding 0).f (n+1) = ((n+1 : ℕ) : ℤ) by
        change (0 : ℤ) + (n+1 : ℕ) = (n+1 : ℕ); omega)
      (show (degreeEmbedding 0).f n = (n : ℤ) by change (0 : ℤ) + n = n; omega)]
    have hc := congrArg (fun f => (e (n+1)).hom ≫ f) (hd n)
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp] at hc
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
      congrArg (fun f => f ≫ (L.extendXIso (degreeEmbedding 0)
        (show (degreeEmbedding 0).f n = (n : ℤ) by change (0 : ℤ) + n = n; omega)).inv)
        hc.symm

@[simp] lemma nonnegativeExtensionIso_hom_f {C : Type*} [Category* C] [HasZeroMorphisms C]
    [HasZeroObject C] (K : ChainComplex C ℤ) (L : ChainComplex C ℕ)
    (e : ∀ n : ℕ, K.X (n : ℤ) ≅ L.X n)
    (hneg : ∀ i : ℤ, i < 0 → IsZero (K.X i))
    (hd : ∀ n : ℕ, (e (n+1)).inv ≫ K.d ((n+1 : ℕ) : ℤ) (n : ℤ) ≫
      (e n).hom = L.d (n+1) n) (n : ℕ) :
    (nonnegativeExtensionIso K L e hneg hd).hom.f (n : ℤ) =
      (e n).hom ≫ (L.extendXIso (degreeEmbedding 0)
        (show (degreeEmbedding 0).f n = (n : ℤ) by change (0 : ℤ) + n = n; omega)).inv := rfl

def ordinaryRelativeExtensionIso (R : Type u) [CommRing R] (P : Pair.{v}) :
    ordinary R R P ≅ (nonnegative R R P).extend (degreeEmbedding 0) :=
  nonnegativeExtensionIso _ _ (ordinaryDegreeIso R R P)
    (fun i hi => (P202.RelativeSingularChains.ordinary_negative R R P i hi).1)
    (P202.RelativeSingularChains.ordinary_boundary R R P)

def reducedRelativeExtensionIso (R : Type u) [CommRing R] (P : Pair.{v}) :
    reduced R R P ≅ (nonnegative R R P).extend (degreeEmbedding 0) :=
  nonnegativeExtensionIso _ _ (reducedDegreeIso R R P)
    (fun i hi => (P202.RelativeSingularChains.reduced_negative R R P i hi).1)
    (P202.RelativeSingularChains.reduced_boundary R R P)

def relativeComparison (R : Type u) [CommRing R] (P : Pair.{v}) :
    reduced R R P ≅ ordinary R R P :=
  reducedRelativeExtensionIso R P ≪≫ (ordinaryRelativeExtensionIso R P).symm

lemma relativeComparison_coordinates (R : Type u) [CommRing R] (P : Pair.{v}) :
    IsRelativeComparison R P (relativeComparison R P) := by
  intro n
  simp [relativeComparison, reducedRelativeExtensionIso, ordinaryRelativeExtensionIso,
    HomologicalComplex.Hom.isoOfComponents_inv_f, nonnegativeExtensionIso,
    Category.assoc]

lemma reduced_map_degree (R : Type u) [CommRing R] {X Y : TopCat.{v}}
    (f : X ⟶ Y) (n : ℕ) :
    ((reducedFunctor R R).map f).f (n : ℤ) ≫ (reducedNonnegativeIso R R Y n).hom =
      (reducedNonnegativeIso R R X n).hom ≫ (chainMap R R f).f n := by
  change (HomologicalComplex.extendMap (augmentedShiftedMap R R f)
    (degreeEmbedding (-1))).f (n : ℤ) ≫ _ = _
  rw [HomologicalComplex.extendMap_f _ _
    (show (degreeEmbedding (-1)).f (n+1) = (n : ℤ) by
      change (-1 : ℤ) + ((n+1 : ℕ) : ℤ) = n; omega)]
  simp [reducedNonnegativeIso, augmentedShiftedMap]

lemma reduced_relative_map_degree (R : Type u) [CommRing R]
    {P Q : Pair.{v}} (f : P ⟶ Q) (n : ℕ) :
    (relativeMap (reducedFunctor R R) f).f (n : ℤ) ≫ (reducedDegreeIso R R Q n).hom =
      (reducedDegreeIso R R P n).hom ≫ (relativeMap (chainFunctor R R) f).f n := by
  have hr := congrArg (fun k => k.f (n : ℤ)) (projection_map (reducedFunctor R R) f)
  have hn := congrArg (fun k => k.f n) (projection_map (chainFunctor R R) f)
  change (projection (reducedFunctor R R) P).f (n : ℤ) ≫
      (relativeMap (reducedFunctor R R) f).f (n : ℤ) =
    ((reducedFunctor R R).map f.map).f (n : ℤ) ≫
      (projection (reducedFunctor R R) Q).f (n : ℤ) at hr
  change (projection (chainFunctor R R) P).f n ≫
      (relativeMap (chainFunctor R R) f).f n =
    (chainMap R R f.map).f n ≫ (projection (chainFunctor R R) Q).f n at hn
  apply (cancel_epi ((projection (reducedFunctor R R) P).f (n : ℤ))).mp
  calc
    _ = (((reducedFunctor R R).map f.map).f (n : ℤ) ≫
        (projection (reducedFunctor R R) Q).f (n : ℤ)) ≫
        (reducedDegreeIso R R Q n).hom := by rw [← Category.assoc, hr]
    _ = ((reducedNonnegativeIso R R P.space n).hom ≫ (chainMap R R f.map).f n) ≫
        (projection (chainFunctor R R) Q).f n := by
      rw [Category.assoc, P202.RelativeSingularChains.reduced_degree,
        ← Category.assoc, reduced_map_degree]
    _ = ((reducedNonnegativeIso R R P.space n).hom ≫
        (projection (chainFunctor R R) P).f n) ≫
        (relativeMap (chainFunctor R R) f).f n := by
      rw [Category.assoc, ← hn, ← Category.assoc]
    _ = _ := by
      rw [← P202.RelativeSingularChains.reduced_degree, Category.assoc]

lemma reducedRelativeExtensionIso_naturality (R : Type u) [CommRing R]
    {P Q : Pair.{v}} (f : P ⟶ Q) :
    relativeMap (reducedFunctor R R) f ≫ (reducedRelativeExtensionIso R Q).hom =
      (reducedRelativeExtensionIso R P).hom ≫
        HomologicalComplex.extendMap (relativeMap (chainFunctor R R) f) (degreeEmbedding 0) := by
  apply HomologicalComplex.Hom.ext
  funext i
  cases i with
  | negSucc k =>
    exact ((nonnegative R R Q).isZero_extend_X (degreeEmbedding 0) _ (by
      intro m hm
      change (0 : ℤ) + m = Int.negSucc k at hm
      omega)).eq_of_tgt _ _
  | ofNat n =>
    change (relativeMap (reducedFunctor R R) f).f (n : ℤ) ≫
        ((reducedDegreeIso R R Q n).hom ≫
          ((nonnegative R R Q).extendXIso (degreeEmbedding 0)
            (show (degreeEmbedding 0).f n = (n : ℤ) by change (0 : ℤ) + n = n; omega)).inv) =
      ((reducedDegreeIso R R P n).hom ≫
          ((nonnegative R R P).extendXIso (degreeEmbedding 0)
            (show (degreeEmbedding 0).f n = (n : ℤ) by change (0 : ℤ) + n = n; omega)).inv) ≫
        (HomologicalComplex.extendMap (relativeMap (chainFunctor R R) f)
          (degreeEmbedding 0)).f (n : ℤ)
    rw [HomologicalComplex.extendMap_f _ _
      (show (degreeEmbedding 0).f n = (n : ℤ) by change (0 : ℤ) + n = n; omega)]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc, reduced_relative_map_degree]
    simp only [Category.assoc]

lemma reduced_relative_quotient_isIso_conditional
    (excision : P202Specs.Excision.isomorphism_type.{u,v})
    (naturality : P202Specs.Excision.naturality_type.{u,v})
    (R : Type u) [CommRing R] (D : Data.{v}) (n : ℕ) :
    IsIso (homologyMap (relativeMap (reducedFunctor R R) (quotientPairMap D.pair)) (n : ℤ)) := by
  let ψ := relativeMap (chainFunctor R R) (quotientPairMap D.pair)
  have hψ : QuasiIsoAt ψ n := (quasiIsoAt_iff_isIso_homologyMap ψ n).mpr
    (relative_quotient_isIso_conditional excision naturality R D n)
  have hψe : QuasiIsoAt (HomologicalComplex.extendMap ψ (degreeEmbedding 0)) (n : ℤ) :=
    (HomologicalComplex.quasiIsoAt_extendMap_iff ψ (degreeEmbedding 0)
      (show (degreeEmbedding 0).f n = (n : ℤ) by change (0 : ℤ) + n = n; omega)).mpr hψ
  haveI : IsIso (homologyMap (HomologicalComplex.extendMap ψ (degreeEmbedding 0)) (n : ℤ)) :=
    (quasiIsoAt_iff_isIso_homologyMap _ _).mp hψe
  have hs := congrArg (fun k => homologyMap k (n : ℤ))
    (reducedRelativeExtensionIso_naturality R (quotientPairMap D.pair))
  simp only [homologyMap_comp] at hs
  haveI : IsIso (homologyMap (relativeMap (reducedFunctor R R) (quotientPairMap D.pair)) (n : ℤ) ≫
      homologyMap (reducedRelativeExtensionIso R (quotientPair D.pair)).hom (n : ℤ)) := by
    rw [hs]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (homologyMap (reducedRelativeExtensionIso R (quotientPair D.pair)).hom (n : ℤ))

/-- Conditional draft of the full quotient theorem, including degree zero and
the specified quotient-induced map. The closed original wrapper is not defined. -/
theorem isomorphism_conditional
    (excision : P202Specs.Excision.isomorphism_type.{u,v})
    (naturality : P202Specs.Excision.naturality_type.{u,v}) :
    isomorphism_type.{u,v} := by
  intro R _ D
  let c := relativeComparison R D.pair
  refine ⟨c, relativeComparison_coordinates R D.pair, fun n => ?_⟩
  haveI hp := quotient_reduced_projection_isIso R D.pair D.nonempty (n : ℤ)
  haveI hq := reduced_relative_quotient_isIso_conditional excision naturality R D n
  let F := HomologicalComplex.homologyFunctor (ModuleCat.{max u v} R) (ComplexShape.down ℤ) (n : ℤ)
  let e : relativeHomology R R D.pair (n : ℤ) ≅
      reducedHomology R R (quotientSpace D.pair) (n : ℤ) :=
    F.mapIso c.symm ≪≫
      asIso (homologyMap (relativeMap (reducedFunctor R R) (quotientPairMap D.pair)) (n : ℤ)) ≪≫
      (asIso (homologyMap (projection (reducedFunctor R R) (quotientPair D.pair)) (n : ℤ))).symm
  refine ⟨hp, e, ?_⟩
  change F.map c.hom ≫ (F.map c.inv ≫ _ ≫ _) ≫ _ = _
  simp only [← Category.assoc, ← F.map_comp, c.hom_inv_id, F.map_id, Category.id_comp]
  simp

/-- The entire ordinary complex of the empty subspace is zero. -/
lemma empty_inclusion_eq_zero (R : Type u) [CommRing R] (X : TopCat.{v}) :
    inclusion (ordinaryFunctor R R) (emptyPair X) = 0 := by
  letI : IsEmpty (emptyPair X).sub := ⟨fun x => x.property⟩
  apply HomologicalComplex.Hom.ext
  funext n
  exact (P202.SingularDegreeZero.emptyOrdinaryX R R (emptyPair X).sub n).eq_of_src _ _

/-- The inverse of the relative projection is its canonical cokernel descent. -/
def emptyRelativeIso (R : Type u) [CommRing R] (X : TopCat.{v}) :
    ordinary R R (emptyPair X) ≅ ordinaryComplex R R X := by
  have : IsIso (projection (ordinaryFunctor R R) (emptyPair X)) :=
    cokernel.π_of_zero (empty_inclusion_eq_zero R X)
  exact (asIso (projection (ordinaryFunctor R R) (emptyPair X))).symm

lemma emptyRelativeIso_projection (R : Type u) [CommRing R] (X : TopCat.{v}) :
    projection (ordinaryFunctor R R) (emptyPair X) ≫
      (emptyRelativeIso R X).hom = 𝟙 _ := by
  exact (emptyRelativeIso R X).inv_hom_id

/-- The independent empty-subspace obligation, with the exact ordered draft
premises. Neither premise is needed for this boundary case. -/
theorem empty_conditional
    (_excision : P202Specs.Excision.isomorphism_type.{u,v})
    (_naturality : P202Specs.Excision.naturality_type.{u,v}) :
    empty_type.{u,v} := by
  intro R _ X
  exact ⟨emptyRelativeIso R X, emptyRelativeIso_projection R X⟩

end P202.GoodPairQuotient

universe v8_closure_0151c9d094d0c93f_u0 v8_closure_0151c9d094d0c93f_u1
theorem _root_.«P202».«GoodPairQuotient».«empty» : _root_.«P202Specs».«GoodPairQuotient».«empty_type».{v8_closure_0151c9d094d0c93f_u0, v8_closure_0151c9d094d0c93f_u1} :=
  @_root_.«P202».«GoodPairQuotient».«empty_conditional».{v8_closure_0151c9d094d0c93f_u0, v8_closure_0151c9d094d0c93f_u1} (@_root_.«P202».«Excision».«isomorphism».{v8_closure_0151c9d094d0c93f_u0, v8_closure_0151c9d094d0c93f_u1}) (@_root_.«P202».«Excision».«naturality».{v8_closure_0151c9d094d0c93f_u0, v8_closure_0151c9d094d0c93f_u1})
theorem _root_.«P202».«GoodPairQuotient».«isomorphism» : _root_.«P202Specs».«GoodPairQuotient».«isomorphism_type».{v8_closure_0151c9d094d0c93f_u0, v8_closure_0151c9d094d0c93f_u1} :=
  @_root_.«P202».«GoodPairQuotient».«isomorphism_conditional».{v8_closure_0151c9d094d0c93f_u0, v8_closure_0151c9d094d0c93f_u1} (@_root_.«P202».«Excision».«isomorphism».{v8_closure_0151c9d094d0c93f_u0, v8_closure_0151c9d094d0c93f_u1}) (@_root_.«P202».«Excision».«naturality».{v8_closure_0151c9d094d0c93f_u0, v8_closure_0151c9d094d0c93f_u1})
