import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Duality.RelativeFundamentalClass
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Duality.CompactOrientation
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Products.ShuffleChains
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.CategoryTheory.Abelian.CommSq
import Mathlib.Tactic.Linarith
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! The fundamental class and its boundary in T31. The relative class is
characterized by its interior local values. The induced boundary orientation is
defined independently by the outward-normal-first product convention; its
agreement with the actual connecting image follows from the shuffle boundary
formula and geometric collar-box comparisons. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex Topology
open scoped TensorProduct
universe u v w u₁ v₁ w₁
namespace P202.RelativeFundamentalClass
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.LocalOrientation P202Specs.CompactOrientation
open P202Specs.RelativeFundamentalClass

/-- The zero-dimensional half-space model has an empty face, so every
zero-dimensional manifold in this model has empty boundary. -/
theorem manifoldBoundary_zero {M : Type v} [TopologicalSpace M]
    (A : SmoothManifolds.ModelData.TopologicalManifold 0 .halfSpace M) :
    manifoldBoundary A = ∅ := by
  ext x
  simp [manifoldBoundary, SmoothManifolds.ModelData.halfSpaceFace]

namespace Collar
variable {M : Type v} [TopologicalSpace M] {B : Set M} (c : Collar B)

/-- A collar is an open embedding into the original manifold. -/
theorem isOpenMap_map : IsOpenMap c.map :=
  c.isOpen_neighborhood.isOpenMap_subtype_val.comp c.homeomorph.isOpenMap

theorem earlyRegion_isOpen (t : ℝ) : IsOpen (c.earlyRegion t) :=
  isOpenMap_map c _ (isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const)

theorem boundary_subset_earlyRegion {t : ℝ} (ht : 0 < t) : B ⊆ c.earlyRegion t := by
  intro b hb
  exact ⟨(⟨b, hb⟩, collarZero), ht, c.zero_section ⟨b, hb⟩⟩

theorem core_isClosed (t : ℝ) : IsClosed (c.core t) :=
  (earlyRegion_isOpen c t).isClosed_compl

theorem core_subset_interior {t : ℝ} (ht : 0 < t) : c.core t ⊆ Bᶜ := by
  intro x hx hb
  exact hx (boundary_subset_earlyRegion c ht hb)

theorem core_isCompact [CompactSpace M] (t : ℝ) : IsCompact (c.core t) :=
  (core_isClosed c t).isCompact

/-- The compact core is genuinely compact in the open interior, not merely
compact as an ambient set. -/
theorem interiorCore_isCompact [CompactSpace M] {t : ℝ} (ht : 0 < t) :
    IsCompact (c.interiorCore t) := by
  apply Topology.IsInducing.subtypeVal.isCompact_preimage' (core_isCompact c t)
  intro x hx
  exact ⟨⟨x, core_subset_interior c ht hx⟩, rfl⟩

/-- The early collar has no spurious boundary points at positive time. -/
theorem map_mem_boundary_iff (b : B) (t : CollarTime) : c.map (b, t) ∈ B ↔ t = collarZero := by
  constructor
  · intro h
    have he : c.homeomorph (b, t) = c.homeomorph (⟨c.map (b, t), h⟩, collarZero) := by
      apply Subtype.ext
      exact (c.zero_section ⟨c.map (b, t), h⟩).symm
    exact congrArg Prod.snd (c.homeomorph.injective he)
  · intro h
    rw [h]
    change (c.homeomorph (b, collarZero)).val ∈ B
    rw [c.zero_section]
    exact b.property
/-- Compact interior sets eventually lie in every sufficiently thin collar core.
This is the geometric cofinality used in paper.tex 2327--2330. -/
theorem cores_cofinal [T2Space M] (hB : IsCompact B)
    (K : Set (Interior B)) (hK : IsCompact K) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ K ⊆ c.interiorCore t := by
  letI : CompactSpace B := isCompact_iff_compactSpace.mp hB
  let L : Set M := Subtype.val '' K
  have hL : IsClosed L := (hK.image continuous_subtype_val).isClosed
  have hprod : (Set.univ : Set B) ×ˢ {collarZero} ⊆ c.map ⁻¹' Lᶜ := by
    rintro ⟨b, s⟩ ⟨_, hs⟩
    have hs' : s = collarZero := hs
    subst s
    change (c.homeomorph (b, collarZero)).val ∉ L
    rw [c.zero_section]
    rintro ⟨x, _, he⟩
    exact x.property (he.symm ▸ b.property)
  obtain ⟨P, V, _, hV, hP, hzero, hPV⟩ :=
    generalized_tube_lemma (isCompact_univ : IsCompact (Set.univ : Set B))
      isCompact_singleton (hL.isOpen_compl.preimage c.map.continuous) hprod
  obtain ⟨d, hd, hball⟩ := Metric.isOpen_iff.mp hV collarZero (hzero (Set.mem_singleton collarZero))
  refine ⟨min d (1/2), lt_min hd (by norm_num),
    lt_of_le_of_lt (min_le_right _ _) (by norm_num), ?_⟩
  intro x hx
  change x.val ∉ c.earlyRegion (min d (1/2))
  rintro ⟨⟨b, s⟩, hs, he⟩
  have hsV : s ∈ V := by
    apply hball
    change dist s.val (0 : ℝ) < d
    rw [Real.dist_eq, sub_zero, abs_of_nonneg s.property.1]
    exact lt_of_lt_of_le hs (min_le_left _ _)
  have hc : c.map (b, s) ∉ L :=
    hPV (show (b, s) ∈ P ×ˢ V from ⟨hP (Set.mem_univ b), hsV⟩)
  exact hc ⟨x, hx, he.symm⟩

/-- Every point in the early collar lies in the collar neighborhood. -/
theorem earlyRegion_subset_neighborhood (t : ℝ) : c.earlyRegion t ⊆ c.neighborhood := by
  rintro x ⟨y, _, rfl⟩
  exact (c.homeomorph y).property

/-- Inverse collar coordinates on the early collar, with their actual topology. -/
def earlyCoordinates (t : ℝ) : C(c.earlyRegion t, B × CollarTime) :=
  ⟨fun y => c.homeomorph.symm ⟨y.val, earlyRegion_subset_neighborhood c t y.property⟩,
    c.homeomorph.symm.continuous.comp (continuous_subtype_val.subtype_mk _)⟩

theorem earlyCoordinates_lt (t : ℝ) (y : c.earlyRegion t) :
    (earlyCoordinates c t y).2.val < t := by
  obtain ⟨z, hz, he⟩ := y.property
  have hh : c.homeomorph z = ⟨y.val, earlyRegion_subset_neighborhood c t y.property⟩ :=
    Subtype.ext he
  change (c.homeomorph.symm _).2.val < t
  rw [← hh, c.homeomorph.symm_apply_apply]
  exact hz

/-- Retraction of the early collar to its boundary, obtained by forgetting time. -/
def earlyRetraction (t : ℝ) : TopCat.of (c.earlyRegion t) ⟶ TopCat.of B :=
  TopCat.ofHom ⟨fun y => (earlyCoordinates c t y).1,
    continuous_fst.comp (earlyCoordinates c t).continuous⟩

/-- The actual boundary inclusion into the early collar. -/
def boundaryInEarly {t : ℝ} (ht : 0 < t) : TopCat.of B ⟶ TopCat.of (c.earlyRegion t) :=
  TopCat.ofHom ⟨fun b => ⟨b.val, boundary_subset_earlyRegion c ht b.property⟩,
    continuous_subtype_val.subtype_mk _⟩

theorem earlyCoordinates_boundary {t : ℝ} (ht : 0 < t) (b : B) :
    earlyCoordinates c t (boundaryInEarly c ht b) = (b, collarZero) := by
  change c.homeomorph.symm _ = (b, collarZero)
  apply c.homeomorph.injective
  rw [c.homeomorph.apply_symm_apply]
  exact Subtype.ext (c.zero_section b).symm

theorem boundaryInEarly_retraction {t : ℝ} (ht : 0 < t) :
    boundaryInEarly c ht ≫ earlyRetraction c t = 𝟙 (TopCat.of B) := by
  ext b
  exact congrArg (fun y : B × CollarTime => y.1.val) (earlyCoordinates_boundary c ht b)

/-- Scale a collar parameter towards its zero end. -/
def scaleTime (u : unitInterval) (s : CollarTime) : CollarTime :=
  ⟨(1 - u.val) * s.val,
    mul_nonneg (sub_nonneg.mpr u.property.2) s.property.1,
    lt_of_le_of_lt (mul_le_of_le_one_left s.property.1 (by linarith [u.property.1])) s.property.2⟩

theorem scaleTime_le (u : unitInterval) (s : CollarTime) : (scaleTime u s).val ≤ s.val :=
  mul_le_of_le_one_left s.property.1 (by linarith [u.property.1])

/-- The collar deformation retraction, with an explicit continuous homotopy.
It remains inside the early collar at every time. -/
def earlyDeformation {t : ℝ} (ht : 0 < t) :
    TopCat.Homotopy (𝟙 (TopCat.of (c.earlyRegion t)))
      (earlyRetraction c t ≫ boundaryInEarly c ht) where
  toFun z := ⟨c.map ((earlyCoordinates c t z.2).1,
      scaleTime z.1 (earlyCoordinates c t z.2).2),
    ⟨((earlyCoordinates c t z.2).1, scaleTime z.1 (earlyCoordinates c t z.2).2),
      lt_of_le_of_lt (scaleTime_le _ _) (earlyCoordinates_lt c t z.2), rfl⟩⟩
  continuous_toFun := by
    have hc : Continuous (fun z : unitInterval × c.earlyRegion t => earlyCoordinates c t z.2) :=
      (earlyCoordinates c t).continuous.comp continuous_snd
    have hs : Continuous (fun z : unitInterval × c.earlyRegion t =>
        scaleTime z.1 (earlyCoordinates c t z.2).2) :=
      ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
        (continuous_subtype_val.comp (continuous_snd.comp hc))).subtype_mk _
    exact (c.map.continuous.comp ((continuous_fst.comp hc).prodMk hs)).subtype_mk _
  map_zero_left y := by
    apply Subtype.ext
    have hs : scaleTime (0 : unitInterval) (earlyCoordinates c t y).2 =
        (earlyCoordinates c t y).2 := by
      apply Subtype.ext
      simp [scaleTime]
    change c.map ((earlyCoordinates c t y).1, scaleTime 0 (earlyCoordinates c t y).2) = y.val
    rw [hs]
    exact congrArg Subtype.val (c.homeomorph.apply_symm_apply _)
  map_one_left y := by
    apply Subtype.ext
    have hs : scaleTime (1 : unitInterval) (earlyCoordinates c t y).2 = collarZero := by
      apply Subtype.ext
      simp [scaleTime, collarZero]
    change c.map ((earlyCoordinates c t y).1, scaleTime 1 (earlyCoordinates c t y).2) =
      (earlyCoordinates c t y).1.val
    rw [hs]
    exact c.zero_section _

/-- The boundary inclusion into the removed collar portion induces
isomorphisms on ordinary homology in every integer degree. -/
theorem boundaryInEarly_homology_isIso (R : Type u) [CommRing R]
    {t : ℝ} (ht : 0 < t) (j : ℤ) :
    IsIso ((homologyFunctor R R j).map (boundaryInEarly c ht)) := by
  have hfg : TopCat.Homotopy (boundaryInEarly c ht ≫ earlyRetraction c t) (𝟙 _) := by
    rw [boundaryInEarly_retraction]
    exact TopCat.Homotopy.refl _
  exact (P202.PrismHomotopy.equivalence R R (boundaryInEarly c ht) (earlyRetraction c t)
    hfg (earlyDeformation c ht).symm j).1

/-- The map of pairs replacing the boundary by the removed collar portion. -/
def boundaryToEarly {t : ℝ} (ht : 0 < t) :
    boundaryPair M B ⟶ boundaryPair M (c.earlyRegion t) :=
  ⟨𝟙 _, boundary_subset_earlyRegion c ht⟩

/-- The pair sequence proves the collar/core comparison from the explicit
collar deformation. No homological equivalence is assumed in the collar data. -/
theorem relativeToEarly_isIso (R : Type u) [CommRing R]
    {t : ℝ} (ht : 0 < t) (j : ℤ) :
    IsIso ((relativeHomologyFunctor R R j).map (boundaryToEarly c ht)) := by
  let F := ordinaryFunctor R R
  let P := boundaryPair M B
  let Q := boundaryPair M (c.earlyRegion t)
  let f := boundaryToEarly c ht
  let φ := sequenceMap F f
  have hP := HomologicalComplex.shortExact_of_degreewise_shortExact _
    (P202.RelativeSingularChains.sequence_shortExact F P)
  have hQ := HomologicalComplex.shortExact_of_degreewise_shortExact _
    (P202.RelativeSingularChains.sequence_shortExact F Q)
  apply HomologicalComplex.HomologySequence.isIso_homologyMap_τ₃ φ hP hQ j
  · haveI : IsIso (homologyMap φ.τ₁ j) := boundaryInEarly_homology_isIso c R ht j
    infer_instance
  · change IsIso (homologyMap (F.map (𝟙 _)) j)
    infer_instance
  · intro k _
    exact boundaryInEarly_homology_isIso c R ht k
  · intro k _
    change Mono (homologyMap (F.map (𝟙 _)) k)
    infer_instance

/-- The image of the interior core is exactly the original closed core. -/
theorem image_interiorCore {t : ℝ} (ht : 0 < t) :
    Subtype.val '' c.interiorCore t = c.core t := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, core_subset_interior c ht hx⟩, hx, rfl⟩

/-- Equality of the two geometric descriptions of the core pair, expressed
as an identity-on-M pair isomorphism. -/
def corePairIso {t : ℝ} (ht : 0 < t) :
    boundaryPair M (c.earlyRegion t) ≅
      supportedPair M (Subtype.val '' c.interiorCore t) where
  hom := ⟨𝟙 _, by
    intro x hx hy
    rw [image_interiorCore c ht] at hy
    exact hy hx⟩
  inv := ⟨𝟙 _, by
    intro x hx
    by_contra h
    apply hx
    rw [image_interiorCore c ht]
    exact h⟩
  hom_inv_id := PairMap.ext _ _ rfl
  inv_hom_id := PairMap.ext _ _ rfl

/-- The actual restriction of a relative class to any collar core is an
isomorphism, in all nonnegative degrees. -/
theorem relativeToCompact_core_isIso (R : Type u) [CommRing R]
    {t : ℝ} (ht : 0 < t) (j : ℕ) :
    IsIso ((relativeHomologyFunctor R R (j : ℤ)).map
      (relativeToCompact B (c.interiorCore t))) := by
  haveI := relativeToEarly_isIso c R ht (j : ℤ)
  have he : boundaryToEarly c ht ≫ (corePairIso c ht).hom =
      relativeToCompact B (c.interiorCore t) := PairMap.ext _ _ rfl
  rw [← he, Functor.map_comp]
  infer_instance

end Collar

/-- Excision data removing the closed boundary from a compact interior support.
This construction is geometric: compactness and separation prove the closure
condition; no equivalence on homology is supplied as a hypothesis. -/
def compactExcisionData {M : Type v} [TopologicalSpace M] [T2Space M]
    (B : Set M) (hB : IsClosed B) (K : Set (Interior B)) (hK : IsCompact K) :
    P202Specs.Excision.Data.{v} where
  pair := supportedPair M (Subtype.val '' K)
  removed := B
  subset := by
    rintro x hx ⟨y, _, he⟩
    exact y.property (he.symm ▸ hx)
  closure_subset := by
    have hc : IsClosed (Subtype.val '' K) :=
      (hK.image continuous_subtype_val).isClosed
    change closure B ⊆ interior (Subtype.val '' K)ᶜ
    rw [hB.closure_eq, hc.isOpen_compl.interior_eq]
    rintro x hx ⟨y, _, he⟩
    exact y.property (he.symm ▸ hx)

/-- Excision identifies exactly the punctured interior support, with its original
topology; the comparison map is the actual inclusion. -/
def compactExcisionIso {M : Type v} [TopologicalSpace M] [T2Space M]
    (B : Set M) (hB : IsClosed B) (K : Set (Interior B)) (hK : IsCompact K) :
    supportedPair (Interior B) K ≅ (compactExcisionData B hB K hK).excised where
  hom := ⟨TopCat.ofHom ⟨fun x => ⟨x.val, x.property⟩,
    continuous_subtype_val.subtype_mk _⟩, by
    rintro x hx ⟨y, hy, he⟩
    have he' : y = (x : Interior B) := Subtype.ext he
    exact hx (he' ▸ hy)⟩
  inv := ⟨TopCat.ofHom ⟨fun x => ⟨x.val, x.property⟩,
    continuous_subtype_val.subtype_mk _⟩, by
    intro x hx hy
    exact hx ⟨⟨x.val, x.property⟩, hy, rfl⟩⟩
  hom_inv_id := PairMap.ext _ _ rfl
  inv_hom_id := PairMap.ext _ _ rfl

/-- Compact supports in the open interior compute the same actual relative
groups in the ambient space, in every nonnegative degree. -/
theorem compactSupportInclusion_isIso (R : Type u) [CommRing R]
    {M : Type v} [TopologicalSpace M] [T2Space M]
    (B : Set M) (hB : IsClosed B) (K : Set (Interior B)) (hK : IsCompact K) (j : ℕ) :
    IsIso ((relativeHomologyFunctor R R (j : ℤ)).map (compactSupportInclusion B K)) := by
  let D := compactExcisionData B hB K hK
  haveI := P202.LocalOrientation.excision_integer R D j
  have he : (compactExcisionIso B hB K hK).hom ≫ D.inclusion =
      compactSupportInclusion B K := PairMap.ext _ _ rfl
  rw [← he, Functor.map_comp]
  infer_instance

/-- The localization square commutes as maps of pairs, before taking homology. -/
theorem compactPoint_square {M : Type v} [TopologicalSpace M]
    (B : Set M) (K : Set (Interior B)) (x : Interior B) (hx : x ∈ K) :
    compactSupportInclusion B K ≫ pointMap (show x.val ∈ Subtype.val '' K from ⟨x, hx, rfl⟩) =
      pointMap hx ≫ interiorLocalInclusion B x := PairMap.ext _ _ rfl

/-- Localizing a relative class through a compact containing x gives the same
local class as direct localization. -/
theorem relativePoint_square {M : Type v} [TopologicalSpace M]
    (B : Set M) (K : Set (Interior B)) (x : Interior B) (hx : x ∈ K) :
    relativeToCompact B K ≫ pointMap (show x.val ∈ Subtype.val '' K from ⟨x, hx, rfl⟩) =
      interiorPointMap B x := PairMap.ext _ _ rfl

/-- The local comparison is itself excision, without any collar assumption. -/
theorem interiorLocalInclusion_isIso (R : Type u) [CommRing R]
    {M : Type v} [TopologicalSpace M] [T2Space M]
    (B : Set M) (hB : IsClosed B) (x : Interior B) (j : ℕ) :
    IsIso ((relativeHomologyFunctor R R (j : ℤ)).map (interiorLocalInclusion B x)) := by
  let D := P202.LocalOrientation.openLocalExcisionData Bᶜ hB.isOpen_compl x
  haveI := P202.LocalOrientation.excision_integer R D j
  have he : (P202.LocalOrientation.openLocalExcisionIso Bᶜ hB.isOpen_compl x).hom ≫
      D.inclusion = interiorLocalInclusion B x := PairMap.ext _ _ rfl
  rw [← he, Functor.map_comp]
  infer_instance

/-- Agreement with a compact orientation class forces the prescribed local
values at every point in that compact. -/
theorem interiorValue_of_compactAgreement (R : Type u) [CommRing R]
    {M : Type v} [TopologicalSpace M] (B : Set M) (n : ℕ)
    (o : LocalChoice R n (Interior B)) (K : Set (Interior B))
    (g : relativeHomology R R (boundaryPair M B) (n : ℤ))
    (gK : SupportedGroup R (Interior B) K n) (hgK : HasLocalValues R o K gK)
    (hg : AgreesOnCompact R B n K g gK) (x : Interior B) (hx : x ∈ K) :
    ((relativeHomologyFunctor R R (n : ℤ)).map (interiorPointMap B x)) g =
      ((relativeHomologyFunctor R R (n : ℤ)).map (interiorLocalInclusion B x)) (o x) := by
  let F := relativeHomologyFunctor R R (n : ℤ)
  have h := congrArg (fun z => F.map
    (pointMap (show x.val ∈ Subtype.val '' K from ⟨x, hx, rfl⟩)) z) hg
  change F.map _ (F.map _ g) = F.map _ (F.map _ gK) at h
  rw [← ModuleCat.comp_apply, ← F.map_comp, relativePoint_square B K x hx,
    ← ModuleCat.comp_apply, ← F.map_comp, compactPoint_square B K x hx,
    F.map_comp, ModuleCat.comp_apply] at h
  exact h.trans (congrArg (F.map (interiorLocalInclusion B x)) (hgK x hx))

/-- Degree zero has its correct negative-degree connecting target. -/
theorem boundaryHom_zero_dimension (R : Type u) [CommRing R]
    {M : Type v} [TopologicalSpace M] (B : Set M)
    (h : P202Specs.ChainLES.DegreewiseShortExact
      (sequence (ordinaryFunctor R R) (boundaryPair M B))) :
    boundaryHom R B h 0 = 0 := by
  exact (P202.SingularChains.ordinary_negative_homology R R (TopCat.of B)
    ((0 : ℤ) - 1) (by norm_num)).eq_of_tgt _ _

/-- All connecting homomorphisms vanish when the specified boundary is empty. -/
theorem boundaryHom_empty (R : Type u) [CommRing R]
    {M : Type v} [TopologicalSpace M]
    (h : P202Specs.ChainLES.DegreewiseShortExact
      (sequence (ordinaryFunctor R R) (boundaryPair M ∅))) (n : ℕ) :
    boundaryHom R (∅ : Set M) h n = 0 := by
  letI : IsEmpty (∅ : Set M) := ⟨fun x => x.property⟩
  exact (P202.SingularDegreeZero.emptyOrdinary R R
    (TopCat.of (∅ : Set M)) ((n : ℤ) - 1)).eq_of_tgt _ _

/-- For empty boundary the canonical projection really is an isomorphism. -/
theorem emptyAbsoluteToRelative_bijective (R : Type u) [CommRing R]
    (M : Type v) [TopologicalSpace M] (n : ℕ) :
    Function.Bijective (emptyAbsoluteToRelative R M n) := by
  letI : IsEmpty (boundaryPair M ∅).sub := ⟨fun x => x.property⟩
  exact (P202.LocalOrientation.emptySubspaceHomologyIso R
    (boundaryPair M ∅) (n : ℤ)).toLinearEquiv.bijective

/-- Localizing the projection of an absolute class agrees with the direct
projection to the local pair. This is equality of the actual natural maps. -/
theorem absoluteLocalization (R : Type u) [CommRing R]
    {M : Type v} [TopologicalSpace M] (B : Set M) (x : Interior B) (n : ℕ)
    (a : homology R R (TopCat.of M) (n : ℤ)) :
    ((relativeHomologyFunctor R R (n : ℤ)).map (interiorPointMap B x))
      ((homologyMap (projection (ordinaryFunctor R R) (boundaryPair M B)) (n : ℤ)) a) =
    (homologyMap (projection (ordinaryFunctor R R) (localPair M x.val)) (n : ℤ)) a := by
  have h := congrArg (fun f => homologyMap f (n : ℤ))
    (projection_map (ordinaryFunctor R R) (interiorPointMap B x))
  have hid : (ordinaryFunctor R R).map (interiorPointMap B x).map = 𝟙 _ :=
    (ordinaryFunctor R R).map_id _
  rw [hid, Category.id_comp, homologyMap_comp] at h
  exact congrArg (fun f => f a) h

/-- Both empty-boundary local characterizations are given by the direct
projection from ordinary homology into the ambient local groups. -/
theorem emptyAbsolute_values_iff (R : Type u) [CommRing R]
    {M : Type v} [TopologicalSpace M] (n : ℕ) (o : LocalChoice R n M)
    (a : homology R R (TopCat.of M) (n : ℤ)) :
    HasEmptyBoundaryValues R n o (emptyAbsoluteToRelative R M n a) ↔
      HasLocalValues R o Set.univ (absoluteToSupported R M n a) := by
  have he (x : M) :
      ((relativeHomologyFunctor R R (n : ℤ)).map
        (interiorPointMap (∅ : Set M) ⟨x, Set.notMem_empty x⟩))
          (emptyAbsoluteToRelative R M n a) =
      restrictPoint R (Set.mem_univ x) n (absoluteToSupported R M n a) := by
    rw [show emptyAbsoluteToRelative R M n a =
      (homologyMap (projection (ordinaryFunctor R R) (boundaryPair M ∅)) (n : ℤ)) a from rfl,
      absoluteLocalization]
    have h := congrArg (fun f => homologyMap f (n : ℤ))
      (projection_map (ordinaryFunctor R R) (pointMap (Set.mem_univ x)))
    have hid : (ordinaryFunctor R R).map (pointMap (Set.mem_univ x)).map = 𝟙 _ :=
      (ordinaryFunctor R R).map_id _
    rw [hid, Category.id_comp, homologyMap_comp] at h
    exact (congrArg (fun f => f a) h).symm
  constructor
  · intro h x _
    exact (he x).symm.trans (h x)
  · intro h x
    exact (he x).trans (h x (Set.mem_univ x))

/-- Empty-boundary specialization only. All five frozen premises are explicit,
in their supplied order and at the supplied universes. This does not close the
nonempty-boundary target. -/
theorem emptyBoundary_conditional
    (_aboveDimension : P202Specs.CompactOrientation.Expected.aboveDimension.{u,v})
    (_compactClass : P202Specs.CompactOrientation.Expected.compactClass.{u,v})
    (_compatibility : P202Specs.CompactOrientation.Expected.compatibility.{u,v})
    (_localDetection : P202Specs.CompactOrientation.Expected.localDetection.{u,v})
    (ordinaryFundamentalClass :
      P202Specs.CompactOrientation.Expected.ordinaryFundamentalClass.{u,v}) :
    P202Specs.RelativeFundamentalClass.Expected.emptyBoundary.{u,v} := by
  intro R _ n M _ A o hM
  have h := ordinaryFundamentalClass R n M A o hM
  have hb := emptyAbsoluteToRelative_bijective R M n
  obtain ⟨a, ha, hua⟩ := h.2
  refine ⟨hb, emptyAbsoluteToRelative R M n a,
    (emptyAbsolute_values_iff R n o.val a).mpr ha, ?_⟩
  intro g hg
  obtain ⟨b, rfl⟩ := hb.2 g
  exact congrArg (emptyAbsoluteToRelative R M n)
    (hua b ((emptyAbsolute_values_iff R n o.val b).mp hg))

/-- The degree-one first factor gives a minus sign on the second differential.
These are the original signed shuffle chains, not a postulated sign rule. -/
theorem intervalFirst_boundary (R : Type u) [CommRing R] (X Y : TopCat.{v})
    (q : ℕ) (a : Chains R X 1) (c : Chains R Y (q+1)) :
    boundary R R (P202Specs.AlexanderWhitney.productSpace X Y) (0+q+1)
      (P202Specs.ShuffleModel.shuffle R X Y (0+q+1+1)
        (Pi.single (⟨(1,q+1), by omega⟩ : P202Specs.AlexanderWhitney.Diagonal (0+q+1+1))
          (a ⊗ₜ[R] c))) =
    P202Specs.ShuffleModel.shuffle R X Y (0+q+1)
      (Pi.single (⟨(0,q+1), by omega⟩ : P202Specs.AlexanderWhitney.Diagonal (0+q+1))
        (boundary R R X 0 a ⊗ₜ[R] c)) -
    P202Specs.ShuffleModel.shuffle R X Y (0+q+1)
      (Pi.single (⟨(1,q), by omega⟩ : P202Specs.AlexanderWhitney.Diagonal (0+q+1))
        (a ⊗ₜ[R] boundary R R Y q c)) := by
  have h := LinearMap.congr_fun (P202.ShuffleChains.chain_identity R X Y (0+q+1))
    (Pi.single (⟨(1,q+1), by omega⟩ : P202Specs.AlexanderWhitney.Diagonal (0+q+1+1))
      (a ⊗ₜ[R] c))
  change _ = P202Specs.ShuffleModel.shuffle R X Y (0+q+1)
    (P202Specs.AlexanderWhitney.totalBoundary R X Y (0+q+1) _) at h
  have hd := P202.ShuffleBoundary.totalBoundary_single_positive R X Y 0 q (a ⊗ₜ[R] c)
  rw [hd] at h
  change _ = P202Specs.ShuffleModel.shuffle R X Y (0+q+1)
    (Pi.single (⟨(0,q+1), by omega⟩ : P202Specs.AlexanderWhitney.Diagonal (0+q+1))
      (boundary R R X 0 a ⊗ₜ[R] c) +
      (-1 : ℤ) • Pi.single (⟨(1,q), by omega⟩ : P202Specs.AlexanderWhitney.Diagonal (0+q+1))
        (a ⊗ₜ[R] boundary R R Y q c)) at h
  rw [map_add, map_zsmul, neg_one_zsmul] at h
  change @Eq (Chains R (P202Specs.AlexanderWhitney.productSpace X Y) (0+q+1)) _ _
  rw [sub_eq_add_neg]
  convert! h using 1

/-- The ordered one-simplex has terminal endpoint minus initial endpoint.
Thus the lower end of an interval placed first has coefficient -1. -/
theorem intervalSimplex_boundary (R : Type u) [CommRing R] (X : TopCat.{v})
    (σ : Simplex X 1) :
    boundary R R X 0 (Finsupp.single σ (1 : R)) =
      Finsupp.single (face 0 σ) 1 - Finsupp.single (face 1 σ) 1 := by
  have h := P202.SingularChains.boundary_single R R X 0 σ 1
  change _ = ∑ i : Fin 2, (-1 : ℤ)^i.val • Finsupp.single (face i σ) (1 : R) at h
  rw [Fin.sum_univ_two] at h
  norm_num only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul, neg_one_zsmul] at h
  rw [sub_eq_add_neg]
  convert! h using 1

/-- The same first-factor boundary formula includes a zero-dimensional second
factor; there is no differential out of its degree zero. -/
theorem intervalFirst_boundary_zero (R : Type u) [CommRing R] (X Y : TopCat.{v})
    (a : Chains R X 1) (c : Chains R Y 0) :
    boundary R R (P202Specs.AlexanderWhitney.productSpace X Y) 0
      (P202Specs.ShuffleModel.shuffle R X Y 1
        (Pi.single (⟨(1,0), by omega⟩ : P202Specs.AlexanderWhitney.Diagonal 1)
          (a ⊗ₜ[R] c))) =
    P202Specs.ShuffleModel.shuffle R X Y 0
      (Pi.single (⟨(0,0), by omega⟩ : P202Specs.AlexanderWhitney.Diagonal 0)
        (boundary R R X 0 a ⊗ₜ[R] c)) := by
  have h := LinearMap.congr_fun (P202.ShuffleChains.chain_identity R X Y 0)
    (Pi.single (⟨(1,0), by omega⟩ : P202Specs.AlexanderWhitney.Diagonal 1) (a ⊗ₜ[R] c))
  change _ = P202Specs.ShuffleModel.shuffle R X Y 0
    (P202Specs.AlexanderWhitney.totalBoundary R X Y 0 _) at h
  rw [P202.ShuffleBoundary.totalBoundary_single_zero_right R X Y 0] at h
  change _ = P202Specs.ShuffleModel.shuffle R X Y 0
    (Pi.single (⟨(0,0), by omega⟩ : P202Specs.AlexanderWhitney.Diagonal 0)
      (boundary R R X 0 a ⊗ₜ[R] c)) at h
  convert! h using 1

/-- Local characterization implies compatibility with every compact interior
orientation class. This will give independence of collar/core choices once
existence and uniqueness of the relative class have been established. -/
theorem compactAgreement_of_localValuesOn
    (localDetection : P202Specs.CompactOrientation.Expected.localDetection.{u,v})
    (R : Type u) [CommRing R] {M : Type v} [TopologicalSpace M] [T2Space M]
    (B : Set M) (hB : IsClosed B) (n : ℕ) (A : Manifold n (Interior B))
    (o : LocalChoice R n (Interior B))
    (g : relativeHomology R R (boundaryPair M B) (n : ℤ))
    (K : Set (Interior B)) (hK : IsCompact K)
    (hg : ∀ (x : Interior B), x ∈ K →
      ((relativeHomologyFunctor R R (n : ℤ)).map (interiorPointMap B x)) g =
        ((relativeHomologyFunctor R R (n : ℤ)).map (interiorLocalInclusion B x)) (o x))
    (gK : SupportedGroup R (Interior B) K n) (hgK : HasLocalValues R o K gK) :
    AgreesOnCompact R B n K g gK := by
  let F := relativeHomologyFunctor R R (n : ℤ)
  haveI : IsIso (F.map (compactSupportInclusion B K)) :=
    compactSupportInclusion_isIso R B hB K hK n
  let e := (asIso (F.map (compactSupportInclusion B K))).toLinearEquiv
  let q := e.symm (F.map (relativeToCompact B K) g)
  have hq : F.map (compactSupportInclusion B K) q = F.map (relativeToCompact B K) g :=
    e.apply_symm_apply _
  have hlocal (x : Interior B) (hx : x ∈ K) : restrictPoint R hx n q = o x := by
    haveI : IsIso (F.map (interiorLocalInclusion B x)) :=
      interiorLocalInclusion_isIso R B hB x n
    apply (asIso (F.map (interiorLocalInclusion B x))).toLinearEquiv.injective
    change F.map (interiorLocalInclusion B x) (F.map (pointMap hx) q) =
      F.map (interiorLocalInclusion B x) (o x)
    calc
      _ = F.map (pointMap (show x.val ∈ Subtype.val '' K from ⟨x, hx, rfl⟩))
          (F.map (compactSupportInclusion B K) q) := by
        rw [← ModuleCat.comp_apply, ← F.map_comp, ← compactPoint_square B K x hx,
          F.map_comp, ModuleCat.comp_apply]
      _ = F.map (pointMap (show x.val ∈ Subtype.val '' K from ⟨x, hx, rfl⟩))
          (F.map (relativeToCompact B K) g) := congrArg _ hq
      _ = F.map (interiorPointMap B x) g := by
        rw [← ModuleCat.comp_apply, ← F.map_comp, relativePoint_square B K x hx]
      _ = _ := hg x hx
  have heq : q = gK := by
    apply localDetection R n (Interior B) A K hK
    funext x
    exact (hlocal x.val x.property).trans (hgK x.val x.property).symm
  change F.map (relativeToCompact B K) g = F.map (compactSupportInclusion B K) gK
  exact hq.symm.trans (congrArg (F.map (compactSupportInclusion B K)) heq)

/-- A locally characterized relative class agrees with every compact class. -/
theorem compactAgreement_of_interiorValues
    (localDetection : P202Specs.CompactOrientation.Expected.localDetection.{u,v})
    (R : Type u) [CommRing R] {M : Type v} [TopologicalSpace M] [T2Space M]
    (B : Set M) (hB : IsClosed B) (n : ℕ) (A : Manifold n (Interior B))
    (o : LocalChoice R n (Interior B))
    (g : relativeHomology R R (boundaryPair M B) (n : ℤ))
    (hg : HasInteriorValues R B n o g)
    (K : Set (Interior B)) (hK : IsCompact K)
    (gK : SupportedGroup R (Interior B) K n) (hgK : HasLocalValues R o K gK) :
    AgreesOnCompact R B n K g gK :=
  compactAgreement_of_localValuesOn localDetection R B hB n A o g K hK
    (fun x _ => hg x) gK hgK

/-- To verify a relative class locally it suffices to check agreement with
compact orientation classes through every interior point. -/
theorem interiorValues_of_compactAgreement (R : Type u) [CommRing R]
    {M : Type v} [TopologicalSpace M] (B : Set M) (n : ℕ)
    (o : LocalChoice R n (Interior B))
    (g : relativeHomology R R (boundaryPair M B) (n : ℤ))
    (h : ∀ x : Interior B, ∃ (K : Set (Interior B)) (gK : SupportedGroup R (Interior B) K n),
      x ∈ K ∧ HasLocalValues R o K gK ∧ AgreesOnCompact R B n K g gK) :
    HasInteriorValues R B n o g := by
  intro x
  obtain ⟨K, gK, hx, hgK, hg⟩ := h x
  exact interiorValue_of_compactAgreement R B n o K g gK hgK hg x hx

/-- A compact orientation class on a collar core lifts along the actual
collar/core isomorphism. This only prescribes its local values on that core. -/
theorem exists_core_class
    (compactClass : P202Specs.CompactOrientation.Expected.compactClass.{u,v})
    (R : Type u) [CommRing R] {M : Type v} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    (B : Set M) (c : Collar B) (n : ℕ) (A : Manifold n (Interior B))
    (o : Orientation R A) {t : ℝ} (ht : 0 < t) :
    ∃ (g : relativeHomology R R (boundaryPair M B) (n : ℤ))
      (gK : SupportedGroup R (Interior B) (c.interiorCore t) n),
      HasLocalValues R o.val (c.interiorCore t) gK ∧
        AgreesOnCompact R B n (c.interiorCore t) g gK := by
  obtain ⟨gK, hgK, _⟩ := compactClass R n (Interior B) A o (c.interiorCore t)
    (Collar.interiorCore_isCompact c ht)
  let F := relativeHomologyFunctor R R (n : ℤ)
  haveI : IsIso (F.map (relativeToCompact B (c.interiorCore t))) :=
    Collar.relativeToCompact_core_isIso c R ht n
  let e := (asIso (F.map (relativeToCompact B (c.interiorCore t)))).toLinearEquiv
  refine ⟨e.symm (F.map (compactSupportInclusion B (c.interiorCore t)) gK), gK, hgK, ?_⟩
  exact e.apply_symm_apply _

/-- Construction and uniqueness with all prescribed interior values, and
compatibility with every shared compact orientation class. The collar boundary
sign is proved separately below, without an extra premise of this theorem. -/
theorem interiorClass_conditional
    (_aboveDimension : P202Specs.CompactOrientation.Expected.aboveDimension.{u,v})
    (compactClass : P202Specs.CompactOrientation.Expected.compactClass.{u,v})
    (_compatibility : P202Specs.CompactOrientation.Expected.compatibility.{u,v})
    (localDetection : P202Specs.CompactOrientation.Expected.localDetection.{u,v})
    (_ordinaryFundamentalClass :
      P202Specs.CompactOrientation.Expected.ordinaryFundamentalClass.{u,v}) :
    P202Specs.RelativeFundamentalClass.Expected.interiorClass.{u,v} := by
  intro R _ n M _ _ B hB c A o hM
  letI : CompactSpace M := isCompact_univ_iff.mp hM
  obtain ⟨g₀, k₀, hk₀, hg₀⟩ := exists_core_class compactClass R B c n A o
    (show (0 : ℝ) < 1/2 by norm_num)
  haveI : IsIso ((relativeHomologyFunctor R R (n : ℤ)).map
      (relativeToCompact B (c.interiorCore (1/2)))) :=
    Collar.relativeToCompact_core_isIso c R (show (0 : ℝ) < 1/2 by norm_num) n
  let e := (asIso ((relativeHomologyFunctor R R (n : ℤ)).map
    (relativeToCompact B (c.interiorCore (1/2))))).toLinearEquiv
  have hloc : HasInteriorValues R B n o.val g₀ := by
    intro x
    have hcompact : IsCompact (c.interiorCore (1/2) ∪ {x}) :=
      (Collar.interiorCore_isCompact c (show (0 : ℝ) < 1/2 by norm_num)).union isCompact_singleton
    obtain ⟨t, ht, _, hsub⟩ := Collar.cores_cofinal c hB.isCompact _ hcompact
    obtain ⟨g₁, k₁, hk₁, hg₁⟩ := exists_core_class compactClass R B c n A o ht
    have hagree : AgreesOnCompact R B n (c.interiorCore (1/2)) g₁ k₀ := by
      apply compactAgreement_of_localValuesOn localDetection R B hB n A o.val g₁
        (c.interiorCore (1/2)) (Collar.interiorCore_isCompact c (show (0 : ℝ) < 1/2 by norm_num))
        _ k₀ hk₀
      intro y hy
      exact interiorValue_of_compactAgreement R B n o.val (c.interiorCore t)
        g₁ k₁ hk₁ hg₁ y (hsub (Set.mem_union_left _ hy))
    have heq : g₁ = g₀ := e.injective (hagree.trans hg₀.symm)
    rw [← heq]
    exact interiorValue_of_compactAgreement R B n o.val (c.interiorCore t)
      g₁ k₁ hk₁ hg₁ x (hsub (Set.mem_union_right _ (Set.mem_singleton x)))
  refine ⟨⟨g₀, hloc, ?_⟩, ?_⟩
  · intro g hg
    have hagree := compactAgreement_of_interiorValues localDetection R B hB n A o.val
      g hg (c.interiorCore (1/2)) (Collar.interiorCore_isCompact c (show (0 : ℝ) < 1/2 by norm_num))
      k₀ hk₀
    exact e.injective (hagree.trans hg₀.symm)
  · intro g hg K hK gK hgK
    exact compactAgreement_of_interiorValues localDetection R B hB n A o.val g hg K hK gK hgK

/-- Any two classes obtained using any collars/cores coincide once they have
the prescribed local interior values. Only one collar is needed in the proof;
there is no assumed comparison between the construction choices. -/
theorem interiorClass_independent
    (aboveDimension : P202Specs.CompactOrientation.Expected.aboveDimension.{u,v})
    (compactClass : P202Specs.CompactOrientation.Expected.compactClass.{u,v})
    (compatibility : P202Specs.CompactOrientation.Expected.compatibility.{u,v})
    (localDetection : P202Specs.CompactOrientation.Expected.localDetection.{u,v})
    (ordinaryFundamentalClass :
      P202Specs.CompactOrientation.Expected.ordinaryFundamentalClass.{u,v})
    (R : Type u) [CommRing R] (n : ℕ) (M : Type v) [TopologicalSpace M] [T2Space M]
    (B : Set M) (hB : IsClosed B) (c : Collar B)
    (A : Manifold n (Interior B)) (o : Orientation R A) (hM : IsCompact (Set.univ : Set M))
    (g g' : relativeHomology R R (boundaryPair M B) (n : ℤ))
    (hg : HasInteriorValues R B n o.val g) (hg' : HasInteriorValues R B n o.val g') : g = g' := by
  obtain ⟨a, _, hu⟩ := (interiorClass_conditional aboveDimension compactClass compatibility
    localDetection ordinaryFundamentalClass R n M B hB c A o hM).1
  exact (hu g hg).trans (hu g' hg').symm

/-- Construction, uniqueness, and agreement with compact interior classes,
using the proved compact orientation theorem. -/
theorem interiorClass : P202Specs.RelativeFundamentalClass.Expected.interiorClass.{u,v} :=
  interiorClass_conditional P202.CompactOrientation.aboveDimension
    P202.CompactOrientation.compactClass P202.CompactOrientation.compatibility
    P202.CompactOrientation.localDetection P202.CompactOrientation.ordinaryFundamentalClass

/-- The ordinary fundamental class recovered in relative homology for empty boundary. -/
theorem emptyBoundary : P202Specs.RelativeFundamentalClass.Expected.emptyBoundary.{u,v} :=
  emptyBoundary_conditional P202.CompactOrientation.aboveDimension
    P202.CompactOrientation.compactClass P202.CompactOrientation.compatibility
    P202.CompactOrientation.localDetection P202.CompactOrientation.ordinaryFundamentalClass

/-- The concrete relative fundamental class has every prescribed local value.
The choice in its definition depends only on the interior orientation. -/
theorem fundamentalClass_hasInteriorValues (R : Type u) [CommRing R]
    (n : ℕ) (M : Type v) [TopologicalSpace M] [T2Space M]
    (B : Set M) (hB : IsClosed B) (c : Collar B)
    (A : Manifold n (Interior B)) (o : Orientation R A)
    (hM : IsCompact (Set.univ : Set M)) :
    HasInteriorValues R B n o.val (fundamentalClass R B n o.val) :=
  Classical.epsilon_spec (interiorClass R n M B hB c A o hM).1.exists

/-- Any locally characterized construction, using any admissible collar or
core, gives the same concrete relative class. -/
theorem fundamentalClass_eq_of_hasInteriorValues (R : Type u) [CommRing R]
    (n : ℕ) (M : Type v) [TopologicalSpace M] [T2Space M]
    (B : Set M) (hB : IsClosed B) (c : Collar B)
    (A : Manifold n (Interior B)) (o : Orientation R A)
    (hM : IsCompact (Set.univ : Set M))
    (g : relativeHomology R R (boundaryPair M B) (n : ℤ))
    (hg : HasInteriorValues R B n o.val g) : fundamentalClass R B n o.val = g := by
  obtain ⟨a, _, hu⟩ := (interiorClass R n M B hB c A o hM).1
  exact (hu _ (fundamentalClass_hasInteriorValues R n M B hB c A o hM)).trans (hu g hg).symm

/-- The concrete relative class restricts to every shared compact orientation
class under the actual pair inclusions. -/
theorem fundamentalClass_agreesOnCompact (R : Type u) [CommRing R]
    (n : ℕ) (M : Type v) [TopologicalSpace M] [T2Space M]
    (B : Set M) (hB : IsClosed B) (c : Collar B)
    (A : Manifold n (Interior B)) (o : Orientation R A)
    (hM : IsCompact (Set.univ : Set M))
    (K : Set (Interior B)) (hK : IsCompact K)
    (gK : SupportedGroup R (Interior B) K n) (hgK : HasLocalValues R o.val K gK) :
    AgreesOnCompact R B n K (fundamentalClass R B n o.val) gK :=
  (interiorClass R n M B hB c A o hM).2 _
    (fundamentalClass_hasInteriorValues R n M B hB c A o hM) K hK gK hgK

section AbsoluteRecognition
variable (R : Type u) [CommRing R] {n : ℕ} {M : Type v} [TopologicalSpace M]

/-- The local restrictions of a globally supported homology class are compatible;
therefore only the generator condition is needed for them to be an orientation. -/
lemma supported_orientation_iff (A : Manifold n M)
    (g : SupportedGroup R M Set.univ n) :
    IsOrientation R A (fun x => restrictPoint R (Set.mem_univ x) n g) ↔
      ∀ x, IsGenerator R (restrictPoint R (Set.mem_univ x) n g) := by
  constructor
  · exact fun h => h.1
  · intro hg
    refine ⟨hg, ?_⟩
    intro x
    obtain ⟨B, hxB, _⟩ := P202.LocalOrientation.coordinateBall_basis A x
      isOpen_univ (Set.mem_univ x)
    let gB : SupportedGroup R M B.closed n :=
      ((relativeHomologyFunctor R R (n : ℤ)).map
        (supportMap (Set.subset_univ B.closed))) g
    have hlocal (y : M) (hy : y ∈ B.interior) :
        restrictPoint R (B.interior_subset_closed hy) n gB =
          restrictPoint R (Set.mem_univ y) n g := by
      exact P202.LocalOrientation.restrictPoint_support (Set.subset_univ B.closed)
        (B.interior_subset_closed hy) n g
    refine ⟨B, hxB, gB, ?_, hlocal⟩
    let e := LinearEquiv.ofBijective
      (restrictPoint R (B.interior_subset_closed hxB) n)
      ((P202.LocalOrientation.ballRestriction R n M A B).2 x hxB)
    apply (P202.LocalOrientation.generator_map_iff R e gB).mp
    change IsGenerator R (restrictPoint R (B.interior_subset_closed hxB) n gB)
    rw [hlocal x hxB]
    exact hg x

lemma absolute_orientation_iff (A : Manifold n M)
    (a : homology R R (TopCat.of M) (n : ℤ)) :
    IsOrientation R A (fun x => restrictPoint R (Set.mem_univ x) n
      (absoluteToSupported R M n a)) ↔
      ∀ x, IsGenerator R (restrictPoint R (Set.mem_univ x) n
        (absoluteToSupported R M n a)) :=
  supported_orientation_iff R A _

/-- Local restrictions detect absolute classes on a compact manifold. -/
lemma absolute_eq_of_local_eq (A : Manifold n M) (hM : IsCompact (Set.univ : Set M))
    {a b : homology R R (TopCat.of M) (n : ℤ)}
    (hab : ∀ x, restrictPoint R (Set.mem_univ x) n (absoluteToSupported R M n a) =
      restrictPoint R (Set.mem_univ x) n (absoluteToSupported R M n b)) : a = b := by
  apply (P202.CompactOrientation.absoluteToSupported_bijective (M := M) R n).1
  apply P202.CompactOrientation.localDetection R n M A Set.univ hM
  funext x
  exact hab x.val

end AbsoluteRecognition

/-- The local restrictions of a global class give an orientation exactly when
all of them are generators. In particular no separate regularity certificate
is needed after the collar-box generator calculation. -/
theorem absoluteLocalValues_isOrientation_iff (R : Type u) [CommRing R]
    {n : ℕ} {M : Type v} [TopologicalSpace M] (A : Manifold n M)
    (a : homology R R (TopCat.of M) (n : ℤ)) :
    IsOrientation R A (absoluteLocalValues R n a) ↔
      ∀ x, IsGenerator R (absoluteLocalValues R n a x) :=
  absolute_orientation_iff R A a

/-- Applied to the actual connecting image, the preceding criterion reduces
regularity of the boundary orientation to the local generator calculation. -/
theorem connectingLocalValues_isOrientation_iff (R : Type u) [CommRing R]
    {M : Type v} [TopologicalSpace M] (B : Set M)
    (h : P202Specs.ChainLES.DegreewiseShortExact
      (sequence (ordinaryFunctor R R) (boundaryPair M B))) (q : ℕ)
    (A : Manifold q B)
    (g : relativeHomology R R (boundaryPair M B) ((q + 1 : ℕ) : ℤ)) :
    IsOrientation R A (connectingLocalValues R B h q g) ↔
      ∀ x, IsGenerator R (connectingLocalValues R B h q g x) :=
  absoluteLocalValues_isOrientation_iff R A _

/-- Global recognition of the boundary equation once its local collar-box
values have been established. This proves the last uniqueness step of T31;
it does not assume or replace the missing local sign calculation. -/
theorem boundaryRecognition : P202Specs.RelativeFundamentalClass.Expected.boundaryRecognition.{u,v} := by
  intro R _ q M _ B A o hB h g b hb
  constructor
  · intro he
    change absoluteLocalValues R q (boundaryHomSucc R B h q g) = o.val
    rw [he]
    funext x
    exact hb x (Set.mem_univ x)
  · intro he
    apply absolute_eq_of_local_eq R A hB
    intro x
    exact (congrFun he x).trans (hb x (Set.mem_univ x)).symm

namespace Triple
open P202Specs.RelativeFundamentalClass P202Specs.RelativeFundamentalClass.Triple
open P202Specs.RelativeSingularChains P202Specs.SingularChains P202Specs.ChainLES

variable {M : Type v} [TopologicalSpace M]

/-- The nested subspace A within B is canonically homeomorphic to A. -/
def tripleSubspaceIso {A B : Set M} (hAB : A ⊆ B) :
    (subspacePair A B).sub ≅ (boundaryPair M A).sub :=
  TopCat.isoOfHomeo {
    toFun := fun x => ⟨x.val.val, x.property⟩
    invFun := fun x => ⟨⟨x.val, hAB x.property⟩, x.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }

section Categorical
variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {ι : Type w₁} {shape : ComplexShape ι}
  (K : TopCat.{v} ⥤ HomologicalComplex C shape)

lemma tripleInclusion_restrict_isIso {A B : Set M} (hAB : A ⊆ B) :
    IsIso (K.map (tripleInclusion A B).restrict) := by
  change IsIso (K.map (tripleSubspaceIso hAB).hom)
  infer_instance

lemma triple_projection_map {A B : Set M} (hAB : A ⊆ B) :
    projection K (boundaryPair M A) ≫ relativeMap K (tripleProjection hAB) =
      projection K (boundaryPair M B) := by
  rw [projection_map]
  change K.map (𝟙 _) ≫ _ = _
  simp

lemma tripleInclusion_mono {A B : Set M} (hAB : A ⊆ B)
    [Mono (inclusion K (boundaryPair M B))] :
    Mono (relativeMap K (tripleInclusion A B)) := by
  haveI := tripleInclusion_restrict_isIso K hAB
  haveI : Mono (K.map (tripleInclusion A B).map) :=
    inferInstanceAs (Mono (inclusion K (boundaryPair M B)))
  exact Abelian.mono_cokernel_map_of_isPullback
    (IsPullback.of_vert_isIso_mono ⟨inclusion_square K (tripleInclusion A B)⟩)

lemma tripleProjection_epi {A B : Set M} (hAB : A ⊆ B) :
    Epi (relativeMap K (tripleProjection hAB)) := by
  haveI : Epi (projection K (boundaryPair M A) ≫ relativeMap K (tripleProjection hAB)) := by
    rw [triple_projection_map]
    infer_instance
  exact epi_of_epi (projection K (boundaryPair M A)) _

/-- The last actual quotient map has the cokernel universal property of the
first relative inclusion, rather than merely an abstract isomorphism of objects. -/
def triple_isCokernel {A B : Set M} (hAB : A ⊆ B) :
    IsColimit (CokernelCofork.ofπ (relativeMap K (tripleProjection hAB))
      (triple_zero K hAB)) := by
  haveI := tripleProjection_epi K hAB
  refine CokernelCofork.IsColimit.ofπ' _ _ ?_
  intro T k hk
  have hz : inclusion K (boundaryPair M B) ≫ projection K (boundaryPair M A) ≫ k = 0 := by
    have hh := congrArg (fun f => projection K (subspacePair A B) ≫ f) hk
    rw [← Category.assoc, projection_map, comp_zero] at hh
    change (inclusion K (boundaryPair M B) ≫ projection K (boundaryPair M A)) ≫ k = 0 at hh
    simpa only [Category.assoc] using hh
  refine ⟨cokernel.desc (inclusion K (boundaryPair M B))
    (projection K (boundaryPair M A) ≫ k) hz, ?_⟩
  apply (cancel_epi (projection K (boundaryPair M A))).mp
  rw [← Category.assoc, triple_projection_map, cokernel.π_desc]

lemma triple_shortExact {A B : Set M} (hAB : A ⊆ B)
    [Mono (inclusion K (boundaryPair M B))] : (tripleSequence K hAB).ShortExact := by
  haveI := tripleInclusion_mono K hAB
  haveI := tripleProjection_epi K hAB
  exact {
    exact := ShortComplex.exact_of_g_is_cokernel _ (triple_isCokernel K hAB)
    mono_f := (by change Mono (relativeMap K (tripleInclusion A B)); infer_instance)
    epi_g := (by change Epi (relativeMap K (tripleProjection hAB)); infer_instance) }

lemma triple_degreewiseShortExact {A B : Set M} (hAB : A ⊆ B)
    [Mono (inclusion K (boundaryPair M B))] : DegreewiseShortExact (tripleSequence K hAB) :=
  (HomologicalComplex.shortExact_iff_degreewise_shortExact _).mp (triple_shortExact K hAB)

/-- Naturality of the positive boundary-of-a-lift morphism from the original
pair sequence to the localized triple sequence. -/
lemma pairToTriple_connecting {A B D : Set M} (hAD : A ⊆ D) (hBD : B ⊆ D)
    [Mono (inclusion K (boundaryPair M B))] [Mono (inclusion K (boundaryPair M D))]
    (i j : ι) (hij : shape.Rel i j) :
    connecting (P202.RelativeSingularChains.sequence_shortExact K (boundaryPair M B)) i j hij ≫
      homologyMap (pairToTripleFirst K A hBD) j =
    homologyMap (relativeMap K (tripleProjection hBD)) i ≫
      connecting (triple_degreewiseShortExact K hAD) i j hij := by
  exact (P202.ChainLES.naturality (pairToTripleMap K hAD hBD)
    (P202.RelativeSingularChains.sequence_shortExact K (boundaryPair M B))
    (triple_degreewiseShortExact K hAD)).2.2 i j hij

/-- Vanishing of the two adjacent homology groups of the middle relative
complex makes the actual triple connecting map an isomorphism. -/
lemma triple_connecting_isIso {A B : Set M} (hAB : A ⊆ B)
    [Mono (inclusion K (boundaryPair M B))]
    (i j : ι) (hij : shape.Rel i j)
    (hi : IsZero ((relativeComplex K (boundaryPair M A)).homology i))
    (hj : IsZero ((relativeComplex K (boundaryPair M A)).homology j)) :
    IsIso (connecting (triple_degreewiseShortExact K hAB) i j hij) := by
  exact (triple_shortExact K hAB).isIso_δ i j hij hi hj

/-- The isomorphism retains exactly the proved triple connecting map as its
forward morphism, for later generator and sign comparisons. -/
def triple_connectingIso {A B : Set M} (hAB : A ⊆ B)
    [Mono (inclusion K (boundaryPair M B))]
    (i j : ι) (hij : shape.Rel i j)
    (hi : IsZero ((relativeComplex K (boundaryPair M A)).homology i))
    (hj : IsZero ((relativeComplex K (boundaryPair M A)).homology j)) :
    (relativeComplex K (boundaryPair M B)).homology i ≅
      (relativeComplex K (subspacePair A B)).homology j := by
  haveI := triple_connecting_isIso K hAB i j hij hi hj
  exact asIso (connecting (triple_degreewiseShortExact K hAB) i j hij)

@[simp] lemma triple_connectingIso_hom {A B : Set M} (hAB : A ⊆ B)
    [Mono (inclusion K (boundaryPair M B))]
    (i j : ι) (hij : shape.Rel i j)
    (hi : IsZero ((relativeComplex K (boundaryPair M A)).homology i))
    (hj : IsZero ((relativeComplex K (boundaryPair M A)).homology j)) :
    (triple_connectingIso K hAB i j hij hi hj).hom =
      connecting (triple_degreewiseShortExact K hAB) i j hij := rfl


end Categorical

lemma ordinary_triple_degreewiseShortExact (R : Type u) [CommRing R]
    {A B : Set M} (hAB : A ⊆ B) :
    DegreewiseShortExact (tripleSequence (ordinaryFunctor R R) hAB) :=
  triple_degreewiseShortExact (ordinaryFunctor R R) hAB

end Triple

namespace BoxBoundary
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.ShuffleModel P202Specs.AlexanderWhitney

/-- A simplex actually lying in the relative subspace is killed by the actual
categorical relative-chain projection. -/
theorem projection_single_eq_zero (R : Type u) [CommRing R]
    (P : Pair.{v}) (n : ℕ) (σ : Simplex P.space n) (r : R)
    (hσ : InSubspace P n σ) :
    (projection (chainFunctor R R) P).f n (Finsupp.single σ r) = 0 := by
  obtain ⟨τ, hτ⟩ := (P202.RelativeSingularChains.simplex_image P n σ).mpr hσ
  have hmap := P202.SingularChains.chainMap_single R R P.inclusion n τ r
  rw [hτ] at hmap
  rw [← hmap]
  exact congrArg (fun f => f (Finsupp.single τ r))
    (HomologicalComplex.congr_hom (cokernel.condition (inclusion (chainFunctor R R) P)) n)

/-- Shuffle simplices lie in the corresponding product subspace, by their
actual parametrization rather than an assumed support certificate. -/
theorem shuffleSimplex_inSubspace (X Y : TopCat.{v}) (S : Set (X × Y))
    (p q : ℕ) (σ : Simplex X p) (τ : Simplex Y q)
    (h : ∀ x y, (simplexEquiv X p σ x, simplexEquiv Y q τ y) ∈ S)
    (s : LatticePath p q) :
    InSubspace (⟨productSpace X Y, S⟩ : Pair) (p+q) (shuffleSimplex s σ τ) := by
  intro z
  rw [P202.ShuffleChains.simplex_formula]
  exact h _ _

/-- If both simplex factors have product image in the relative subspace, the
entire signed shuffle is killed by the actual quotient map. -/
theorem projection_shuffleComponent_eq_zero (R : Type u) [CommRing R]
    (X Y : TopCat.{v}) (S : Set (X × Y)) (p q : ℕ)
    (σ : Simplex X p) (τ : Simplex Y q) (r t : R)
    (h : ∀ x y, (simplexEquiv X p σ x, simplexEquiv Y q τ y) ∈ S) :
    (projection (chainFunctor R R) (⟨productSpace X Y, S⟩ : Pair)).f (p+q)
      (shuffleComponent R X Y p q (Finsupp.single σ r ⊗ₜ[R] Finsupp.single τ t)) = 0 := by
  rw [P202.ShuffleChains.component_formula]
  simp only [map_smul, map_sum, map_zsmul]
  have hz (s : LatticePath p q) := projection_single_eq_zero R
    (⟨productSpace X Y, S⟩ : Pair) (p+q) (shuffleSimplex s σ τ) 1
      (shuffleSimplex_inSubspace X Y S p q σ τ h s)
  simp only [hz, Finset.sum_const_zero, smul_zero]


/-- The same support statement applies to every finite disk chain, with a
geometric membership hypothesis on its actual simplex support. -/
theorem projection_shuffleComponent_single_tmul_eq_zero (R : Type u) [CommRing R]
    (X Y : TopCat.{v}) (S : Set (X × Y)) (p q : ℕ)
    (σ : Simplex X p) (r : R) (c : Chains R Y q)
    (h : ∀ τ ∈ c.support, ∀ x y,
      (simplexEquiv X p σ x, simplexEquiv Y q τ y) ∈ S) :
    (projection (chainFunctor R R) (⟨productSpace X Y, S⟩ : Pair)).f (p+q)
      (shuffleComponent R X Y p q (Finsupp.single σ r ⊗ₜ[R] c)) = 0 := by
  classical
  rw [← Finsupp.sum_single c]
  simp only [Finsupp.sum, TensorProduct.tmul_sum, map_sum]
  exact Finset.sum_eq_zero (fun τ hτ =>
    projection_shuffleComponent_eq_zero R X Y S p q σ τ r (c τ) (h τ hτ))


/-- Reindexing a zero projected chain does not change it. -/
theorem projection_castChains_eq_zero (R : Type u) [CommRing R]
    (P : Pair.{v}) {n m : ℕ} (h : n = m) (c : Chains R P.space n)
    (hc : (projection (chainFunctor R R) P).f n c = 0) :
    (projection (chainFunctor R R) P).f m (castChains R h c) = 0 := by
  subst m
  exact hc

/-- In the actual quotient by the upper face and lateral faces, the boundary
of the interval-first shuffled chain is minus the lower-face shuffled chain.
All vanishing hypotheses refer only to images of simplices in the actual
finite supports. There is no homology or orientation-sign premise. -/
theorem lowerFace_quotient (R : Type u) [CommRing R]
    (X Y : TopCat.{v}) (S : Set (X × Y)) (q : ℕ)
    (σ : Simplex X 1) (c : Chains R Y (q+1))
    (hUpper : ∀ τ ∈ c.support, ∀ x y,
      (simplexEquiv X 0 (face 0 σ) x, simplexEquiv Y (q+1) τ y) ∈ S)
    (hSide : ∀ τ ∈ (boundary R R Y q c).support, ∀ x y,
      (simplexEquiv X 1 σ x, simplexEquiv Y q τ y) ∈ S) :
    (projection (chainFunctor R R) (⟨productSpace X Y, S⟩ : Pair)).f (0+q+1)
      (boundary R R (productSpace X Y) (0+q+1)
        (shuffle R X Y (0+q+1+1)
          (Pi.single (⟨(1,q+1), by omega⟩ : Diagonal (0+q+1+1))
            (Finsupp.single σ 1 ⊗ₜ[R] c)))) =
    -((projection (chainFunctor R R) (⟨productSpace X Y, S⟩ : Pair)).f (0+q+1)
      (shuffle R X Y (0+q+1)
        (Pi.single (⟨(0,q+1), by omega⟩ : Diagonal (0+q+1))
          (Finsupp.single (face 1 σ) 1 ⊗ₜ[R] c)))) := by
  have hu : (projection (chainFunctor R R) (⟨productSpace X Y, S⟩ : Pair)).f (0+q+1)
      (shuffle R X Y (0+q+1)
        (Pi.single (⟨(0,q+1), by omega⟩ : Diagonal (0+q+1))
          (Finsupp.single (face 0 σ) 1 ⊗ₜ[R] c))) = 0 := by
    rw [P202.ShuffleBoundary.shuffle_single]
    apply projection_castChains_eq_zero
    exact projection_shuffleComponent_single_tmul_eq_zero R X Y S 0 (q+1)
      (face 0 σ) 1 c hUpper
  have hs : (projection (chainFunctor R R) (⟨productSpace X Y, S⟩ : Pair)).f (0+q+1)
      (shuffle R X Y (0+q+1)
        (Pi.single (⟨(1,q), by omega⟩ : Diagonal (0+q+1))
          (Finsupp.single σ 1 ⊗ₜ[R] boundary R R Y q c))) = 0 := by
    rw [P202.ShuffleBoundary.shuffle_single]
    apply projection_castChains_eq_zero
    exact projection_shuffleComponent_single_tmul_eq_zero R X Y S 1 q
      σ 1 (boundary R R Y q c) hSide
  rw [P202.RelativeFundamentalClass.intervalFirst_boundary,
    P202.RelativeFundamentalClass.intervalSimplex_boundary, TensorProduct.sub_tmul,
    Pi.single_sub, map_sub, map_sub, map_sub, hu, hs, zero_sub, sub_zero]

/-- The lower-face identity includes a degree-zero disk chain; ordinary chains
have no augmentation differential out of its degree zero. -/
theorem lowerFace_quotient_zero (R : Type u) [CommRing R]
    (X Y : TopCat.{v}) (S : Set (X × Y))
    (σ : Simplex X 1) (c : Chains R Y 0)
    (hUpper : ∀ τ ∈ c.support, ∀ x y,
      (simplexEquiv X 0 (face 0 σ) x, simplexEquiv Y 0 τ y) ∈ S) :
    (projection (chainFunctor R R) (⟨productSpace X Y, S⟩ : Pair)).f 0
      (boundary R R (productSpace X Y) 0
        (shuffle R X Y 1
          (Pi.single (⟨(1,0), by omega⟩ : Diagonal 1)
            (Finsupp.single σ 1 ⊗ₜ[R] c)))) =
    -((projection (chainFunctor R R) (⟨productSpace X Y, S⟩ : Pair)).f 0
      (shuffle R X Y 0
        (Pi.single (⟨(0,0), by omega⟩ : Diagonal 0)
          (Finsupp.single (face 1 σ) 1 ⊗ₜ[R] c)))) := by
  have hu : (projection (chainFunctor R R) (⟨productSpace X Y, S⟩ : Pair)).f 0
      (shuffle R X Y 0
        (Pi.single (⟨(0,0), by omega⟩ : Diagonal 0)
          (Finsupp.single (face 0 σ) 1 ⊗ₜ[R] c))) = 0 := by
    rw [P202.ShuffleBoundary.shuffle_single]
    apply projection_castChains_eq_zero
    exact projection_shuffleComponent_single_tmul_eq_zero R X Y S 0 0
      (face 0 σ) 1 c hUpper
  rw [P202.RelativeFundamentalClass.intervalFirst_boundary_zero,
    P202.RelativeFundamentalClass.intervalSimplex_boundary, TensorProduct.sub_tmul,
    Pi.single_sub, map_sub, map_sub, hu, zero_sub]

end BoxBoundary

namespace Geometry
open SmoothManifolds.ModelData
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.LocalOrientation

lemma halfSpace_convex (n : ℕ) : Convex ℝ (halfSpaceSet (n+1)) := by
  intro x hx y hy a b ha hb hab
  change 0 ≤ a * x (Fin.last n) + b * y (Fin.last n)
  exact add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)

lemma halfSpace_contractible (n : ℕ) : ContractibleSpace (HalfSpace (n+1)) :=
  (halfSpace_convex n).contractibleSpace ⟨0, by change (0 : ℝ) ≤ 0; exact le_rfl⟩

lemma halfSpace_punctured_starConvex (n : ℕ) (p : Euclidean (n+1))
    (hp : p (Fin.last n) = 0) :
    StarConvex ℝ (fun _ : Fin (n+1) => (1 : ℝ))
      {y : Euclidean (n+1) | y ∈ halfSpaceSet (n+1) ∧ y ≠ p} := by
  intro y hy a b ha hb hab
  constructor
  · change 0 ≤ a * 1 + b * y (Fin.last n)
    exact add_nonneg (mul_nonneg ha zero_le_one) (mul_nonneg hb hy.1)
  · intro he
    have hec := congrFun he (Fin.last n)
    change a * 1 + b * y (Fin.last n) = p (Fin.last n) at hec
    rw [hp] at hec
    have ha0 : a = 0 := by nlinarith [mul_nonneg hb hy.1]
    have hb1 : b = 1 := by linarith
    apply hy.2
    simpa [ha0, hb1] using he

lemma halfSpace_punctured_contractible (n : ℕ) (p : Euclidean (n+1))
    (hp : p (Fin.last n) = 0) :
    ContractibleSpace {y : Euclidean (n+1) | y ∈ halfSpaceSet (n+1) ∧ y ≠ p} := by
  apply (halfSpace_punctured_starConvex n p hp).contractibleSpace
  refine ⟨(fun _ => 1), (by change (0 : ℝ) ≤ 1; exact zero_le_one), ?_⟩
  intro h
  have := congrFun h (Fin.last n)
  simp only [hp] at this
  norm_num at this

def puncturedHalfSpaceHomeomorph (n : ℕ) (p : HalfSpace (n+1)) :
    (localPair (HalfSpace (n+1)) p).sub ≃ₜ
      {y : Euclidean (n+1) | y ∈ halfSpaceSet (n+1) ∧ y ≠ p.val} where
  toFun y := ⟨y.val.val, y.val.property, fun h => y.property (Subtype.ext h)⟩
  invFun y := ⟨⟨y.val, y.property.1⟩, fun h => y.property.2 (congrArg Subtype.val h)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

lemma halfSpace_face_local_isZero (R : Type u) [CommRing R] (n : ℕ)
    (p : HalfSpace (n+1)) (hp : p.val (Fin.last n) = 0) (j : ℕ) :
    IsZero (LocalGroup R (HalfSpace (n+1)) p j) := by
  let P := localPair (HalfSpace (n+1)) p
  let : Nonempty P.space := ⟨p⟩
  let : ContractibleSpace P.space := halfSpace_contractible n
  let h := halfSpace_punctured_contractible n p.val hp
  let : ContractibleSpace P.sub := (puncturedHalfSpaceHomeomorph n p).contractibleSpace_iff.mpr h
  let : Nonempty P.sub := inferInstance
  exact (P202.SpheresDisks.contractiblePairIso R R P (j : ℤ)).isZero_iff.mpr
    (P202.PrismHomotopy.contractible R R P.sub ((j : ℤ)-1))

def halfSpacePositiveHomeomorph (n : ℕ) :
    {z : HalfSpace (n+1) // 0 < z.val (Fin.last n)} ≃ₜ
      {z : Euclidean (n+1) // 0 < z (Fin.last n)} where
  toFun z := ⟨z.val.val, z.property⟩
  invFun z := ⟨⟨z.val, le_of_lt z.property⟩, z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

lemma euclidean_local_rankOne (n : ℕ) (p : Euclidean (n+1)) :
    Nonempty (LocalGroup ℤ (Euclidean (n+1)) p (n+1) ≃ₗ[ℤ] ℤ) := by
  let e0 : Euclidean (n+1) ≃ₜ Coordinate (n+1) := (Homeomorph.Set.univ _).symm
  let e1 := e0.trans (P202.LocalOrientation.coordinateTranslation (n+1) (e0 p))
  have hep : e1 p = coordinateOrigin (n+1) := by
    exact P202.LocalOrientation.coordinateTranslation_center _ _
  let e := P202.LocalOrientation.relativeHomologyEquivOfHomeomorph ℤ
    (localPair (Euclidean (n+1)) p) (localPair (Coordinate (n+1)) (coordinateOrigin (n+1))) e1
    (by
      intro y
      change e1 y ≠ coordinateOrigin (n+1) ↔ y ≠ p
      rw [← hep]
      exact e1.injective.ne_iff) (n+1)
  obtain ⟨f⟩ := (P202.LocalOrientation.localEuclideanPositive ℤ n (n+1)).1 rfl
  exact ⟨e.trans f⟩

lemma halfSpace_interior_local_rankOne (n : ℕ) (p : HalfSpace (n+1))
    (hp : 0 < p.val (Fin.last n)) :
    Nonempty (LocalGroup ℤ (HalfSpace (n+1)) p (n+1) ≃ₗ[ℤ] ℤ) := by
  let U : Set (HalfSpace (n+1)) := {z | 0 < z.val (Fin.last n)}
  let V : Set (Euclidean (n+1)) := {z | 0 < z (Fin.last n)}
  have hU : IsOpen U := isOpen_lt continuous_const
    ((continuous_apply (Fin.last n)).comp continuous_subtype_val)
  have hV : IsOpen V := isOpen_lt continuous_const (continuous_apply (Fin.last n))
  let q : U := ⟨p, hp⟩
  let e1 := (P202.LocalOrientation.openLocalHomologyIso ℤ U hU q (n+1)).symm.toLinearEquiv
  let e2 := P202.LocalOrientation.relativeHomologyEquivOfHomeomorph ℤ
    (localPair U q) (localPair V ((halfSpacePositiveHomeomorph n) q))
    (halfSpacePositiveHomeomorph n) (by
      intro y
      change (halfSpacePositiveHomeomorph n) y ≠ (halfSpacePositiveHomeomorph n) q ↔ y ≠ q
      exact (halfSpacePositiveHomeomorph n).injective.ne_iff) (n+1)
  let e3 := (P202.LocalOrientation.openLocalHomologyIso ℤ V hV
    ((halfSpacePositiveHomeomorph n) q) (n+1)).toLinearEquiv
  obtain ⟨f⟩ := euclidean_local_rankOne n p.val
  exact ⟨e1.trans (e2.trans (e3.trans f))⟩

def chartLocalEquiv (R : Type u) [CommRing R] {n : ℕ} {M : Type v}
    [TopologicalSpace M] [T2Space M] (c : ModelChart n .halfSpace M)
    (p : c.source) (j : ℕ) :
    LocalGroup R M p.val j ≃ₗ[R] LocalGroup R (HalfSpace n) (c p.val) j :=
  P202.LocalOrientation.partialHomeomorphLocalHomologyEquiv_from_bridge R
    (fun P Q e h j => P202.LocalOrientation.relativeHomologyEquivOfHomeomorph R P Q e h j)
    c p j

lemma halfSpace_chart_face_imp {n : ℕ} {M : Type v}
    [TopologicalSpace M] [T2Space M]
    (c d : ModelChart n .halfSpace M) (p : M)
    (hc : p ∈ c.source) (hd : p ∈ d.source)
    (hface : (c p).val ∈ halfSpaceFace n) : (d p).val ∈ halfSpaceFace n := by
  cases n with
  | zero => exact hface.elim
  | succ n =>
    change (c p).val (Fin.last n) = 0 at hface
    change (d p).val (Fin.last n) = 0
    by_contra hnot
    have hpos : 0 < (d p).val (Fin.last n) :=
      lt_of_le_of_ne (d p).property (Ne.symm hnot)
    let ec := chartLocalEquiv ℤ c ⟨p, hc⟩ (n+1)
    let ed := chartLocalEquiv ℤ d ⟨p, hd⟩ (n+1)
    have hcZ := halfSpace_face_local_isZero ℤ n (c p) hface (n+1)
    let : Subsingleton (LocalGroup ℤ (HalfSpace (n+1)) (c p) (n+1)) :=
      ModuleCat.isZero_iff_subsingleton.mp hcZ
    let : Subsingleton (LocalGroup ℤ M p (n+1)) := ec.injective.subsingleton
    obtain ⟨f⟩ := halfSpace_interior_local_rankOne n (d p) hpos
    let : Subsingleton ℤ := (ed.trans f).surjective.subsingleton
    exact zero_ne_one (Subsingleton.elim (0 : ℤ) 1)

lemma halfSpace_chart_face_iff {n : ℕ} {M : Type v}
    [TopologicalSpace M] [T2Space M]
    (c d : ModelChart n .halfSpace M) (p : M)
    (hc : p ∈ c.source) (hd : p ∈ d.source) :
    (c p).val ∈ halfSpaceFace n ↔ (d p).val ∈ halfSpaceFace n :=
  ⟨halfSpace_chart_face_imp c d p hc hd, halfSpace_chart_face_imp d c p hd hc⟩

lemma manifoldBoundary_iff_chart {n : ℕ} {M : Type v} [TopologicalSpace M]
    (A : TopologicalManifold n .halfSpace M) (c : ModelChart n .halfSpace M)
    (hc : c ∈ A.atlas) (p : M) (hp : p ∈ c.source) :
    p ∈ P202Specs.RelativeFundamentalClass.manifoldBoundary A ↔
      (c p).val ∈ halfSpaceFace n := by
  let := A.hausdorff
  constructor
  · rintro ⟨d, _, hpd, hdface⟩
    exact halfSpace_chart_face_imp d c p hpd hp hdface
  · intro hf
    exact ⟨c, hc, hp, hf⟩

lemma halfSpace_face_isClosed (n : ℕ) :
    IsClosed {z : HalfSpace n | z.val ∈ halfSpaceFace n} := by
  cases n with
  | zero => simp [halfSpaceFace]
  | succ n =>
    exact isClosed_eq ((continuous_apply (Fin.last n)).comp continuous_subtype_val) continuous_const

lemma manifoldBoundary_isClosed {n : ℕ} {M : Type v} [TopologicalSpace M]
    (A : TopologicalManifold n .halfSpace M) :
    IsClosed (P202Specs.RelativeFundamentalClass.manifoldBoundary A) := by
  rw [← isOpen_compl_iff]
  apply isOpen_iff_forall_mem_open.mpr
  intro p hp
  obtain ⟨c, hc, hpc⟩ := A.covers p
  let V : Set (HalfSpace n) := {z | z.val ∈ halfSpaceFace n}ᶜ
  refine ⟨c.source ∩ c ⁻¹' V, ?_, ?_, ?_⟩
  · rintro q ⟨hqc, hqV⟩ hqB
    exact hqV ((manifoldBoundary_iff_chart A c hc q hqc).mp hqB)
  · exact c.isOpen_inter_preimage (halfSpace_face_isClosed n).isOpen_compl
  · exact ⟨hpc, fun hf => hp ((manifoldBoundary_iff_chart A c hc p hpc).mpr hf)⟩

def halfSpacePositiveCoordinateHomeomorph (n : ℕ) :
    {z : HalfSpace (n+1) // 0 < z.val (Fin.last n)} ≃ₜ
      {z : Coordinate (n+1) // 0 < z.val (Fin.last n)} where
  toFun z := ⟨⟨z.val.val, Set.mem_univ _⟩, z.property⟩
  invFun z := ⟨⟨z.val.val, le_of_lt z.property⟩, z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _
  continuous_invFun := ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _

def halfSpacePositiveChart (n : ℕ) : ModelChart (n+1) .euclidean (HalfSpace (n+1)) := by
  let U : TopologicalSpace.Opens (HalfSpace (n+1)) :=
    ⟨{z | 0 < z.val (Fin.last n)}, isOpen_lt continuous_const
      ((continuous_apply (Fin.last n)).comp continuous_subtype_val)⟩
  let V : TopologicalSpace.Opens (Coordinate (n+1)) :=
    ⟨{z | 0 < z.val (Fin.last n)}, isOpen_lt continuous_const
      ((continuous_apply (Fin.last n)).comp continuous_subtype_val)⟩
  have hU : Nonempty U := ⟨⟨⟨(fun _ => 1), (by change (0 : ℝ) ≤ 1; norm_num)⟩, by change (0 : ℝ) < 1; norm_num⟩⟩
  have hV : Nonempty V := ⟨⟨⟨(fun _ => 1), Set.mem_univ _⟩, by change (0 : ℝ) < 1; norm_num⟩⟩
  exact (U.openPartialHomeomorphSubtypeCoe hU).symm.trans
    ((halfSpacePositiveCoordinateHomeomorph n).toOpenPartialHomeomorph.trans
      (V.openPartialHomeomorphSubtypeCoe hV))

lemma halfSpacePositiveChart_source (n : ℕ) :
    (halfSpacePositiveChart n).source = {z | 0 < z.val (Fin.last n)} := by
  simp [halfSpacePositiveChart]

def halfSpaceInteriorChart : (n : ℕ) → ModelChart n .euclidean (HalfSpace n)
  | 0 => (Homeomorph.refl (HalfSpace 0)).toOpenPartialHomeomorph
  | n+1 => halfSpacePositiveChart n

lemma halfSpaceInteriorChart_source (n : ℕ) (p : HalfSpace n) :
    p ∈ (halfSpaceInteriorChart n).source ↔ p.val ∉ halfSpaceFace n := by
  cases n with
  | zero => simp [halfSpaceInteriorChart, halfSpaceFace]
  | succ n =>
    rw [halfSpaceInteriorChart, halfSpacePositiveChart_source]
    change 0 < p.val (Fin.last n) ↔ p.val (Fin.last n) ≠ 0
    exact ⟨ne_of_gt, fun h => lt_of_le_of_ne p.property (Ne.symm h)⟩

def interiorChartAt {n : ℕ} {M : Type v} [TopologicalSpace M]
    (A : TopologicalManifold n .halfSpace M)
    (p : P202Specs.RelativeFundamentalClass.Interior
      (P202Specs.RelativeFundamentalClass.manifoldBoundary A)) :
    ModelChart n .euclidean (P202Specs.RelativeFundamentalClass.Interior
      (P202Specs.RelativeFundamentalClass.manifoldBoundary A)) := by
  let U : TopologicalSpace.Opens M :=
    ⟨(P202Specs.RelativeFundamentalClass.manifoldBoundary A)ᶜ,
      (manifoldBoundary_isClosed A).isOpen_compl⟩
  let c := Classical.choose (A.covers p.val)
  exact (c.subtypeRestr (s := U) ⟨p⟩).trans (halfSpaceInteriorChart n)

lemma mem_interiorChartAt_source {n : ℕ} {M : Type v} [TopologicalSpace M]
    (A : TopologicalManifold n .halfSpace M)
    (p : P202Specs.RelativeFundamentalClass.Interior
      (P202Specs.RelativeFundamentalClass.manifoldBoundary A)) :
    p ∈ (interiorChartAt A p).source := by
  let c := Classical.choose (A.covers p.val)
  have hc := (Classical.choose_spec (A.covers p.val)).1
  have hp := (Classical.choose_spec (A.covers p.val)).2
  let U : TopologicalSpace.Opens M :=
    ⟨(P202Specs.RelativeFundamentalClass.manifoldBoundary A)ᶜ,
      (manifoldBoundary_isClosed A).isOpen_compl⟩
  change p ∈ ((c.subtypeRestr (s := U) ⟨p⟩).trans (halfSpaceInteriorChart n)).source
  rw [OpenPartialHomeomorph.trans_source]
  constructor
  · simpa only [OpenPartialHomeomorph.subtypeRestr_source, Set.mem_preimage] using hp
  · rw [OpenPartialHomeomorph.subtypeRestr_coe]
    apply (halfSpaceInteriorChart_source n (c p.val)).mpr
    intro hf
    exact p.property ((manifoldBoundary_iff_chart A c hc p.val hp).mpr hf)

/-- The actual complement of the intrinsic face locus is a boundaryless manifold. -/
def interiorManifold {n : ℕ} {M : Type v} [TopologicalSpace M]
    (A : TopologicalManifold n .halfSpace M) :
    Manifold n (P202Specs.RelativeFundamentalClass.Interior
      (P202Specs.RelativeFundamentalClass.manifoldBoundary A)) := by
  let := A.hausdorff
  let := A.secondCountable
  exact {
    hausdorff := inferInstance
    secondCountable := Topology.IsInducing.subtypeVal.secondCountableTopology
    atlas := Set.range (interiorChartAt A)
    covers := fun p => ⟨interiorChartAt A p, ⟨p, rfl⟩, mem_interiorChartAt_source A p⟩ }

/-- Restrict a chart homeomorphism to a pair of corresponding subspaces.
The result is a homeomorphism on the relative chart domains. -/
def chartSubspaceHomeomorph {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (c : OpenPartialHomeomorph X Y)
    (s : Set X) (t : Set Y) (h : c.IsImage s t) :
    {x : s // x.val ∈ c.source} ≃ₜ {y : t // y.val ∈ c.target} where
  toFun x := ⟨⟨c x.val.val, (h x.property).mpr x.val.property⟩, c.map_source x.property⟩
  invFun y := ⟨⟨c.symm y.val.val, (h.symm y.property).mpr y.val.property⟩,
    c.symm.map_source y.property⟩
  left_inv x := Subtype.ext (Subtype.ext (c.left_inv x.property))
  right_inv y := Subtype.ext (Subtype.ext (c.right_inv y.property))
  continuous_toFun :=
    ((c.continuousOn.comp_continuous
      (continuous_subtype_val.comp continuous_subtype_val) (fun x => x.property)).subtype_mk _).subtype_mk _
  continuous_invFun :=
    ((c.symm.continuousOn.comp_continuous
      (continuous_subtype_val.comp continuous_subtype_val) (fun y => y.property)).subtype_mk _).subtype_mk _

/-- A homeomorphism between open subsets supplies a chart of the ambient spaces. -/
def chartOfOpenHomeomorph {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (U : TopologicalSpace.Opens X) (V : TopologicalSpace.Opens Y)
    (e : U ≃ₜ V) (hU : Nonempty U) : OpenPartialHomeomorph X Y :=
  (U.openPartialHomeomorphSubtypeCoe hU).symm.trans
    (e.toOpenPartialHomeomorph.trans
      (V.openPartialHomeomorphSubtypeCoe (hU.map e)))

lemma chartOfOpenHomeomorph_source {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (U : TopologicalSpace.Opens X) (V : TopologicalSpace.Opens Y)
    (e : U ≃ₜ V) (hU : Nonempty U) :
    (chartOfOpenHomeomorph U V e hU).source = U := by
  simp [chartOfOpenHomeomorph]

lemma chartOfOpenHomeomorph_apply {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (U : TopologicalSpace.Opens X) (V : TopologicalSpace.Opens Y)
    (e : U ≃ₜ V) (hU : Nonempty U) (x : U) :
    chartOfOpenHomeomorph U V e hU x.val = (e x).val := by
  change (e ((U.openPartialHomeomorphSubtypeCoe hU).symm x.val)).val = (e x).val
  exact congrArg (fun z : U => (e z).val)
    ((U.openPartialHomeomorphSubtypeCoe hU).left_inv (Set.mem_univ x))

def faceInsert (n : ℕ) (z : Coordinate n) : HalfSpace (n+1) :=
  ⟨Fin.snoc z.val 0, by simp [halfSpaceSet]⟩

lemma faceInsert_continuous (n : ℕ) : Continuous (faceInsert n) := by
  exact (Continuous.finSnoc (A := fun _ : Fin (n + 1) => ℝ)
    continuous_subtype_val continuous_const).subtype_mk _

def halfSpaceFaceHomeomorph (n : ℕ) :
    {z : HalfSpace (n+1) // z.val (Fin.last n) = 0} ≃ₜ Coordinate n where
  toFun z := ⟨fun i => z.val.val i.castSucc, Set.mem_univ _⟩
  invFun z := ⟨faceInsert n z, by simp [faceInsert]⟩
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    change Fin.snoc (Fin.init z.val.val) 0 = z.val.val
    simpa only [z.property] using (Fin.snoc_init_self z.val.val)
  right_inv z := by
    apply Subtype.ext
    funext i
    simp [faceInsert]
  continuous_toFun :=
    (continuous_pi (fun i => (continuous_apply i.castSucc).comp
      (continuous_subtype_val.comp continuous_subtype_val))).subtype_mk _
  continuous_invFun := (faceInsert_continuous n).subtype_mk _

lemma faceInsert_drop (n : ℕ) (z : {z : HalfSpace (n+1) // z.val (Fin.last n) = 0}) :
    faceInsert n (halfSpaceFaceHomeomorph n z) = z.val := by
  exact congrArg Subtype.val ((halfSpaceFaceHomeomorph n).symm_apply_apply z)

def boundaryFaceChart {n : ℕ} {M : Type v} [TopologicalSpace M]
    (A : TopologicalManifold (n+1) .halfSpace M)
    (c : ModelChart (n+1) .halfSpace M) (hc : c ∈ A.atlas)
    (hU : Nonempty {p : P202Specs.RelativeFundamentalClass.manifoldBoundary A // p.val ∈ c.source}) :
    ModelChart n .euclidean (P202Specs.RelativeFundamentalClass.manifoldBoundary A) := by
  let B := P202Specs.RelativeFundamentalClass.manifoldBoundary A
  let F : Set (HalfSpace (n+1)) := {z | z.val (Fin.last n) = 0}
  let U : TopologicalSpace.Opens B :=
    ⟨Subtype.val ⁻¹' c.source, c.open_source.preimage continuous_subtype_val⟩
  let V : TopologicalSpace.Opens (Coordinate n) :=
    ⟨(faceInsert n) ⁻¹' c.target, c.open_target.preimage (faceInsert_continuous n)⟩
  have hmatch : c.IsImage B F := by
    intro p hp
    exact (manifoldBoundary_iff_chart A c hc p hp).symm
  let e1 := chartSubspaceHomeomorph c B F hmatch
  let e2 : {y : F // y.val ∈ c.target} ≃ₜ V :=
    (halfSpaceFaceHomeomorph n).subtype (fun y => by
      change y.val ∈ c.target ↔ faceInsert n (halfSpaceFaceHomeomorph n y) ∈ c.target
      rw [faceInsert_drop])
  exact chartOfOpenHomeomorph U V (e1.trans e2) hU

lemma boundaryFaceChart_source {n : ℕ} {M : Type v} [TopologicalSpace M]
    (A : TopologicalManifold (n+1) .halfSpace M)
    (c : ModelChart (n+1) .halfSpace M) (hc : c ∈ A.atlas)
    (hU : Nonempty {p : P202Specs.RelativeFundamentalClass.manifoldBoundary A // p.val ∈ c.source}) :
    (boundaryFaceChart A c hc hU).source = Subtype.val ⁻¹' c.source := by
  exact chartOfOpenHomeomorph_source _ _ _ _

def boundaryChartAt {n : ℕ} {M : Type v} [TopologicalSpace M]
    (A : TopologicalManifold (n+1) .halfSpace M)
    (p : P202Specs.RelativeFundamentalClass.manifoldBoundary A) :
    ModelChart n .euclidean (P202Specs.RelativeFundamentalClass.manifoldBoundary A) :=
  boundaryFaceChart A (Classical.choose (A.covers p.val))
    (Classical.choose_spec (A.covers p.val)).1
    ⟨⟨p, (Classical.choose_spec (A.covers p.val)).2⟩⟩

lemma mem_boundaryChartAt_source {n : ℕ} {M : Type v} [TopologicalSpace M]
    (A : TopologicalManifold (n+1) .halfSpace M)
    (p : P202Specs.RelativeFundamentalClass.manifoldBoundary A) :
    p ∈ (boundaryChartAt A p).source := by
  rw [boundaryChartAt, boundaryFaceChart_source]
  exact (Classical.choose_spec (A.covers p.val)).2

/-- The intrinsic boundary has a boundaryless face atlas in its actual subspace topology. -/
def boundaryManifold {n : ℕ} {M : Type v} [TopologicalSpace M]
    (A : TopologicalManifold (n+1) .halfSpace M) :
    Manifold n (P202Specs.RelativeFundamentalClass.manifoldBoundary A) := by
  let := A.hausdorff
  let := A.secondCountable
  exact {
    hausdorff := inferInstance
    secondCountable := Topology.IsInducing.subtypeVal.secondCountableTopology
    atlas := Set.range (boundaryChartAt A)
    covers := fun p => ⟨boundaryChartAt A p, ⟨p, rfl⟩, mem_boundaryChartAt_source A p⟩ }

lemma boundaryFaceChart_apply {n : ℕ} {M : Type v} [TopologicalSpace M]
    (A : TopologicalManifold (n+1) .halfSpace M)
    (c : ModelChart (n+1) .halfSpace M) (hc : c ∈ A.atlas)
    (hU : Nonempty {p : P202Specs.RelativeFundamentalClass.manifoldBoundary A // p.val ∈ c.source})
    (p : P202Specs.RelativeFundamentalClass.manifoldBoundary A) (hp : p.val ∈ c.source) :
    (boundaryFaceChart A c hc hU p).val = fun i : Fin n => (c p.val).val i.castSucc := by
  unfold boundaryFaceChart
  rw [show p = (⟨p, hp⟩ : {p : P202Specs.RelativeFundamentalClass.manifoldBoundary A //
      p.val ∈ c.source}).val from rfl, chartOfOpenHomeomorph_apply]
  rfl

end Geometry

/-- The intrinsic face locus is closed, its complement and (in positive
dimension) its boundary have genuine boundaryless topological manifold atlases. -/
theorem boundaryGeometry : P202Specs.RelativeFundamentalClass.Expected.boundaryGeometry.{v} := by
  refine ⟨?_, ?_, ?_⟩
  · intro n M _ A
    exact ⟨Geometry.manifoldBoundary_isClosed A, ⟨Geometry.interiorManifold A⟩⟩
  · intro q M _ A
    exact ⟨Geometry.boundaryManifold A⟩
  · intro M _ A
    exact manifoldBoundary_zero A

/-- The relative class construction now applies directly to the original
manifold-with-boundary input, including disconnected and zero-dimensional M. -/
theorem intrinsicInteriorClass :
    P202Specs.RelativeFundamentalClass.Expected.intrinsicInteriorClass.{u,v} := by
  intro R _ n M _ A
  dsimp only
  intro c AI o hM
  letI := A.hausdorff
  have hB := Geometry.manifoldBoundary_isClosed A
  exact ⟨fundamentalClass_hasInteriorValues R n M _ hB c AI o hM,
    fun g hg => fundamentalClass_eq_of_hasInteriorValues R n M _ hB c AI o hM g hg,
    fun K hK gK hgK => fundamentalClass_agreesOnCompact R n M _ hB c AI o hM K hK gK hgK⟩

namespace Box
open P202Specs.RelativeFundamentalClass.Box
open P202Specs.SingularChains P202Specs.RelativeSingularChains

variable {D : Type v} [TopologicalSpace D]


def upTime (s t : unitInterval) : unitInterval :=
  ⟨(1-(s : ℝ))*(t : ℝ)+s,
    by have := s.property.1; have := s.property.2
       have := t.property.1; have := t.property.2
       constructor <;> nlinarith⟩

@[simp] lemma upTime_zero (t : unitInterval) : upTime 0 t = t := by
  apply Subtype.ext
  simp [upTime]

@[simp] lemma upTime_one (t : unitInterval) : upTime 1 t = 1 := by
  apply Subtype.ext
  simp [upTime]

@[simp] lemma upTime_top (s : unitInterval) : upTime s 1 = 1 := by
  apply Subtype.ext
  simp [upTime]

lemma continuous_upTime : Continuous (fun st : unitInterval × unitInterval => upTime st.1 st.2) := by
  apply Continuous.subtype_mk
  exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
    (continuous_subtype_val.comp continuous_snd)).add
      (continuous_subtype_val.comp continuous_fst)

/-- Vertical projection onto the top face, landing in the actual upper/lateral subspace. -/
def upperRetraction (S : Set D) : (upperLateralPair S).space ⟶ (upperLateralPair S).sub :=
  TopCat.ofHom ⟨fun z => ⟨(1,z.2), Or.inl rfl⟩,
    (continuous_const.prodMk continuous_snd).subtype_mk _⟩

/-- Every point of the whole box moves vertically to its top face. -/
def boxUpHomotopy (S : Set D) :
    TopCat.Homotopy (𝟙 (upperLateralPair S).space)
      (upperRetraction S ≫ (upperLateralPair S).inclusion) where
  toFun sz := (upTime sz.1 sz.2.1, sz.2.2)
  continuous_toFun := ((continuous_upTime.comp
    (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
      (continuous_snd.comp continuous_snd))
  map_zero_left z := by simp
  map_one_left z := by simp [upperRetraction, Pair.inclusion]

lemma up_preserves (S : Set D) (s : unitInterval) (z : upperLateral S) :
    (upTime s z.val.1, z.val.2) ∈ upperLateral S := by
  rcases z.property with ht | hx
  · exact Or.inl (by rw [ht, upTime_top])
  · exact Or.inr hx

/-- The same vertical deformation preserves the upper and lateral subspace. -/
def upperLateralUpHomotopy (S : Set D) :
    TopCat.Homotopy (𝟙 (upperLateralPair S).sub)
      ((upperLateralPair S).inclusion ≫ upperRetraction S) where
  toFun sz := ⟨(upTime sz.1 sz.2.val.1, sz.2.val.2), up_preserves S sz.1 sz.2⟩
  continuous_toFun := (((continuous_upTime.comp
    (continuous_fst.prodMk (continuous_fst.comp (continuous_subtype_val.comp continuous_snd)))).prodMk
      (continuous_snd.comp (continuous_subtype_val.comp continuous_snd))).subtype_mk _)
  map_zero_left z := by apply Subtype.ext; simp
  map_one_left z := by apply Subtype.ext; simp [upperRetraction, Pair.inclusion]

/-- Inclusion of upper and lateral faces is a homotopy equivalence. -/
lemma upperLateral_inclusion_homology_isIso (R : Type u) [CommRing R]
    (S : Set D) (j : ℤ) :
    IsIso ((homologyFunctor R R j).map (upperLateralPair S).inclusion) :=
  (P202.PrismHomotopy.equivalence R R (upperLateralPair S).inclusion
    (upperRetraction S) (upperLateralUpHomotopy S).symm (boxUpHomotopy S).symm j).1

/-- Consequently the relative homology of the box modulo its upper and
lateral faces vanishes in every integer degree, for arbitrary D and S. -/
lemma upperLateral_relative_isZero (R : Type u) [CommRing R]
    (S : Set D) (j : ℤ) : IsZero (relativeHomology R R (upperLateralPair S) j) := by
  let P := upperLateralPair S
  let K := ordinaryFunctor R R
  let h := HomologicalComplex.shortExact_of_degreewise_shortExact _
    (P202.RelativeSingularChains.sequence_shortExact K P)
  haveI : IsIso (homologyMap (inclusion K P) j) := upperLateral_inclusion_homology_isIso R S j
  haveI : IsIso (homologyMap (inclusion K P) (j-1)) := upperLateral_inclusion_homology_isIso R S (j-1)
  have hπ : homologyMap (projection K P) j = 0 := by
    apply (cancel_epi (homologyMap (inclusion K P) j)).mp
    rw [comp_zero, ← homologyMap_comp, cokernel.condition, homologyMap_zero]
  have hδ : h.δ j (j-1) (by simp) = 0 := by
    apply (cancel_mono (homologyMap (inclusion K P) (j-1))).mp
    rw [zero_comp]
    exact h.δ_comp j (j-1) (by simp)
  exact (h.homology_exact₃ j (j-1) (by simp)).isZero_X₂ hπ hδ

/-- The actual model-prism connecting map is an isomorphism in every integer
degree. This includes a zero-dimensional second factor and all empty cases. -/
def fullBoundaryConnectingIso (R : Type u) [CommRing R] {D : Type v}
    [TopologicalSpace D] (S : Set D) (j : ℤ) :
    relativeHomology R R (boundaryPair (unitInterval × D) (fullBoundary S)) j ≅
      relativeHomology R R (Triple.subspacePair (upperLateral S) (fullBoundary S)) (j-1) :=
  Triple.triple_connectingIso (ordinaryFunctor R R)
    (upperLateral_subset_fullBoundary S) j (j-1) (by simp)
    (upperLateral_relative_isZero R S j) (upperLateral_relative_isZero R S (j-1))

end Box

namespace Disk
open P202Specs.RelativeFundamentalClass.Disk
variable (E : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E]
def diskInclusion : TopCat.of (UnitDisk E) ⟶ TopCat.of E :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
def zeroMap : TopCat.of E ⟶ TopCat.of (UnitDisk E) :=
  TopCat.ofHom (ContinuousMap.const _ (origin E))
def diskContraction : TopCat.Homotopy (zeroMap E ≫ diskInclusion E) (𝟙 _) where
  toFun p := p.1.val • p.2
  continuous_toFun := (continuous_subtype_val.comp continuous_fst).smul continuous_snd
  map_zero_left x := by change (0 : ℝ) • x = (origin E).val; simp [origin]
  map_one_left x := by simp

lemma scale_mem (t : unitInterval) (x : UnitDisk E) :
    t.val • x.val ∈ Metric.closedBall (0 : E) 1 := by
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg t.property.1]
  have hx : ‖x.val‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using x.property
  calc t.val * ‖x.val‖ ≤ 1 * ‖x.val‖ :=
      mul_le_mul_of_nonneg_right t.property.2 (norm_nonneg _)
    _ ≤ 1 := by simpa using hx

def diskScale (t : unitInterval) (x : UnitDisk E) : UnitDisk E :=
  ⟨t.val • x.val, scale_mem E t x⟩

def diskContractionInside : ContinuousMap.Homotopy
    (ContinuousMap.const (UnitDisk E) (origin E)) (ContinuousMap.id (UnitDisk E)) where
  toFun p := diskScale E p.1 p.2
  continuous_toFun := ((continuous_subtype_val.comp continuous_fst).smul
    (continuous_subtype_val.comp continuous_snd)).subtype_mk _
  map_zero_left x := by ext; simp [diskScale, origin]
  map_one_left x := by ext; simp [diskScale]

lemma inclusion_homology_isIso (R : Type u) [CommRing R] (j : ℤ) :
    IsIso ((homologyFunctor R R j).map (diskInclusion E)) :=
  (P202.PrismHomotopy.homologyIso R R (diskInclusion E) (zeroMap E)
    (diskContractionInside E) (diskContraction E) j).1

/-- Radial normalization gives an actual inverse on the punctured ambient space. -/
def normalizeMap : C({x : E // x ≠ 0}, {x : UnitDisk E // ‖x.val‖ = 1}) := {
  toFun := fun x => ⟨⟨‖x.val‖⁻¹ • x.val, by
    have hn : ‖x.val‖ ≠ 0 := norm_ne_zero_iff.mpr x.property
    simp [Metric.mem_closedBall, dist_zero_right, norm_smul, hn]⟩, by
    have hn : ‖x.val‖ ≠ 0 := norm_ne_zero_iff.mpr x.property
    simp [norm_smul, hn]⟩
  continuous_toFun := by
    have hn : ∀ x : {x : E // x ≠ 0}, ‖x.val‖ ≠ 0 :=
      fun x => norm_ne_zero_iff.mpr x.property
    exact (((continuous_subtype_val.norm.inv₀ hn).smul continuous_subtype_val).subtype_mk _).subtype_mk _ }

def normalize : (localPair E 0).sub ⟶ (unitPair E).sub := TopCat.ofHom (normalizeMap E)

lemma boundary_normalize : (toLocal E).restrict ≫ normalize E = 𝟙 _ := by
  ext x
  apply Subtype.ext
  change ‖x.val.val‖⁻¹ • x.val.val = x.val.val
  rw [x.property]
  simp

def radialScale (t : unitInterval) (x : {x : E // x ≠ 0}) : ℝ :=
  (1 - t.val) / ‖x.val‖ + t.val
lemma radialScale_pos (t : unitInterval) (x : {x : E // x ≠ 0}) :
    0 < radialScale E t x := by
  have hn := norm_pos_iff.mpr x.property
  have ht := t.property
  dsimp [radialScale]
  by_cases h : t.val = 0
  · simp [h, hn]
  · exact add_pos_of_nonneg_of_pos
      (div_nonneg (sub_nonneg.mpr ht.2) hn.le) (lt_of_le_of_ne ht.1 (Ne.symm h))
lemma radialScale_continuous :
    Continuous (fun p : unitInterval × {x : E // x ≠ 0} => radialScale E p.1 p.2) := by
  exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).div
    (continuous_subtype_val.comp continuous_snd).norm
    (fun x => norm_ne_zero_iff.mpr x.2.property)).add
      (continuous_subtype_val.comp continuous_fst)

lemma boundary_ne_zero (x : {x : UnitDisk E // ‖x.val‖ = 1}) : x.val.val ≠ 0 := by
  intro he
  have h : ‖x.val.val‖ = 1 := x.property
  simp [he] at h

def sphereInclusionMap : C({x : UnitDisk E // ‖x.val‖ = 1}, {x : E // x ≠ 0}) :=
  ⟨fun x => ⟨x.val.val, boundary_ne_zero E x⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩

def radialHomotopy : ContinuousMap.Homotopy
    ((sphereInclusionMap E).comp (normalizeMap E)) (ContinuousMap.id {x : E // x ≠ 0}) where
  toFun p := ⟨radialScale E p.1 p.2 • (p.2.val : E),
    smul_ne_zero (radialScale_pos E p.1 p.2).ne' p.2.property⟩
  continuous_toFun := ((radialScale_continuous E).smul
    (continuous_subtype_val.comp continuous_snd)).subtype_mk _
  map_zero_left x := by ext; simp [radialScale, sphereInclusionMap, normalizeMap]
  map_one_left x := by ext; simp [radialScale]

lemma boundary_homology_isIso (R : Type u) [CommRing R] (j : ℤ) :
    IsIso ((homologyFunctor R R j).map (toLocal E).restrict) := by
  have H : TopCat.Homotopy ((toLocal E).restrict ≫ normalize E) (𝟙 _) := by
    rw [boundary_normalize]
    exact TopCat.Homotopy.refl _
  exact (P202.PrismHomotopy.homologyIso R R (toLocal E).restrict (normalize E)
    H (radialHomotopy E) j).1

/-- A closed norm ball relative to its sphere computes ambient local homology
at its center, via the actual inclusion, in every integer degree. -/
theorem toLocal_isIso (R : Type u) [CommRing R] (j : ℤ) :
    IsIso ((relativeHomologyFunctor R R j).map (toLocal E)) := by
  apply P202.LocalOrientation.relative_isIso_of_homology_isIso R R (toLocal E)
  · exact boundary_homology_isIso E R
  · exact inclusion_homology_isIso E R
end Disk

namespace BoxBottom
open P202Specs.RelativeFundamentalClass.Box
open P202Specs.RelativeFundamentalClass.BoxBottom
variable {D : Type v} [TopologicalSpace D]
def upperExcision (S : Set D) : P202Specs.Excision.Data.{v} where
  pair := P202Specs.RelativeFundamentalClass.BoxBottom.boundaryPair S
  removed := {z | (1/2 : ℝ) ≤ z.val.1.val}
  subset := by
    intro z hz
    rcases z.property with h0 | hL
    · have hh : z.val.1.val = 0 := congrArg Subtype.val h0
      dsimp at hz
      linarith
    · exact hL
  closure_subset := by
    have hc : IsClosed {z : (P202Specs.RelativeFundamentalClass.BoxBottom.boundaryPair S).space | (1/2 : ℝ) ≤ z.val.1.val} :=
      isClosed_le continuous_const
        (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val))
    rw [hc.closure_eq]
    apply Set.Subset.trans _ (interior_maximal (t := {z : (P202Specs.RelativeFundamentalClass.BoxBottom.boundaryPair S).space | 0 < z.val.1.val}) ?_ ?_)
    · intro z hz
      dsimp at hz ⊢
      linarith
    · intro z hz
      rcases z.property with h0 | hL
      · have hh : z.val.1.val = 0 := congrArg Subtype.val h0
        dsimp at hz
        linarith
      · exact hL
    · exact isOpen_lt continuous_const
        (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val))

def earlyInclusion (S : Set D) : bottomPair S ⟶ (upperExcision S).excised where
  map := TopCat.ofHom {
    toFun := fun d => ⟨⟨(0,d), Or.inl rfl⟩, by
      change ¬ ((1/2 : ℝ) ≤ 0)
      norm_num⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      exact (continuous_const.prodMk continuous_id).subtype_mk _ }
  mapsTo := fun _ h => Or.inr h

lemma early_time_lt (S : Set D) (z : (upperExcision S).excised.space) :
    (z.val.val.1 : ℝ) < 1/2 := lt_of_not_ge z.property

lemma early_bottom_or_side (S : Set D) (z : (upperExcision S).excised.space) :
    z.val.val.1 = 0 ∨ z.val.val.2 ∈ S := by
  rcases z.val.property with h0 | ht | hS
  · exact Or.inl h0
  · have ht' : z.val.val.1.val = 1 := congrArg Subtype.val ht
    have := early_time_lt S z
    linarith
  · exact Or.inr hS

lemma early_side (S : Set D) (z : (upperExcision S).excised.subspace) :
    z.val.val.val.2 ∈ S := by
  rcases z.property with ht | hS
  · have ht' : z.val.val.val.1.val = 1 := congrArg Subtype.val ht
    have := early_time_lt S z.val
    linarith
  · exact hS

def earlyRetraction (S : Set D) : (upperExcision S).excised ⟶ bottomPair S where
  map := TopCat.ofHom ⟨fun z => z.val.val.2,
    continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)⟩
  mapsTo := fun z hz => early_side S ⟨z,hz⟩

def downTime (s t : unitInterval) : unitInterval :=
  ⟨(1-(s : ℝ))*(t : ℝ), by
    have := s.property.1; have := s.property.2
    have := t.property.1; have := t.property.2
    constructor <;> nlinarith⟩
@[simp] lemma downTime_zero (t : unitInterval) : downTime 0 t = t := by
  apply Subtype.ext; simp [downTime]
@[simp] lemma downTime_one (t : unitInterval) : downTime 1 t = 0 := by
  apply Subtype.ext; simp [downTime]
@[simp] lemma downTime_bottom (s : unitInterval) : downTime s 0 = 0 := by
  apply Subtype.ext; simp [downTime]
lemma downTime_le (s t : unitInterval) : (downTime s t : ℝ) ≤ t := by
  dsimp [downTime]
  have := s.property.1; have := t.property.1
  nlinarith
lemma continuous_downTime : Continuous (fun st : unitInterval × unitInterval => downTime st.1 st.2) := by
  exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
    (continuous_subtype_val.comp continuous_snd)).subtype_mk _

def earlyDeformationPoint (S : Set D) (s : unitInterval)
    (z : (upperExcision S).excised.space) : (upperExcision S).excised.space :=
  ⟨⟨(downTime s z.val.val.1, z.val.val.2), by
      rcases early_bottom_or_side S z with h0 | hS
      · exact Or.inl (by rw [h0,downTime_bottom])
      · exact Or.inr (Or.inr hS)⟩,
    not_le_of_gt (lt_of_le_of_lt (downTime_le _ _) (early_time_lt S z))⟩

def earlyDeformation (S : Set D) :
    P202Specs.PrismHomotopy.PairHomotopy (𝟙 (upperExcision S).excised)
      (earlyRetraction S ≫ earlyInclusion S) where
  homotopy := {
    toFun := fun sz => earlyDeformationPoint S sz.1 sz.2
    continuous_toFun := by
      have ht : Continuous (fun sz : unitInterval × (upperExcision S).excised.space =>
          downTime sz.1 sz.2.val.val.1) :=
        continuous_downTime.comp (continuous_fst.prodMk
          (continuous_fst.comp (continuous_subtype_val.comp
            (continuous_subtype_val.comp continuous_snd))))
      exact ((ht.prodMk (continuous_snd.comp (continuous_subtype_val.comp
        (continuous_subtype_val.comp continuous_snd)))).subtype_mk _).subtype_mk _
    map_zero_left := by
      intro z
      apply Subtype.ext; apply Subtype.ext
      change (downTime 0 z.val.val.1, z.val.val.2) = z.val.val
      simp
    map_one_left := by
      intro z
      apply Subtype.ext; apply Subtype.ext
      change (downTime 1 z.val.val.1, z.val.val.2) = (0,z.val.val.2)
      simp
  }
  preserves := by
    intro s z
    exact Or.inr (early_side S z)

lemma earlyInclusion_retraction (S : Set D) :
    earlyInclusion S ≫ earlyRetraction S = 𝟙 (bottomPair S) := by
  apply PairMap.ext
  rfl

lemma earlyInclusion_isIso (R : Type u) [CommRing R] (S : Set D) (j : ℤ) :
    IsIso ((relativeHomologyFunctor R R j).map (earlyInclusion S)) := by
  let H := relativeHomologyFunctor R R j
  refine ⟨⟨H.map (earlyRetraction S), ?_, ?_⟩⟩
  · rw [← H.map_comp,earlyInclusion_retraction,H.map_id]
  · have hh := (P202.PrismHomotopy.relativeHomology R R (earlyDeformation S) j).1
    change H.map (𝟙 _) = H.map (earlyRetraction S ≫ earlyInclusion S) at hh
    simpa only [H.map_id,H.map_comp] using hh.symm

lemma bottomInclusion_factor (S : Set D) :
    earlyInclusion S ≫ (upperExcision S).inclusion = bottomInclusion S := by
  apply PairMap.ext
  rfl

lemma bottomInclusion_nat_isIso (R : Type u) [CommRing R] (S : Set D) (j : ℕ) :
    IsIso ((relativeHomologyFunctor R R (j : ℤ)).map (bottomInclusion S)) := by
  rw [← bottomInclusion_factor,Functor.map_comp]
  haveI := earlyInclusion_isIso R S (j : ℤ)
  haveI := P202.LocalOrientation.excision_integer R (upperExcision S) j
  infer_instance
lemma bottomInclusion_isIso (R : Type u) [CommRing R] (S : Set D) (j : ℤ) :
    IsIso ((relativeHomologyFunctor R R j).map (bottomInclusion S)) := by
  cases j with
  | ofNat j => exact bottomInclusion_nat_isIso R S j
  | negSucc j =>
    exact (P202.RelativeSingularChains.ordinary_negative R R (bottomPair S) _ (by omega)).2.isIso
      (P202.RelativeSingularChains.ordinary_negative R R (P202Specs.RelativeFundamentalClass.BoxBottom.boundaryPair S) _ (by omega)).2 _

def bottomHomologyIso (R : Type u) [CommRing R] (S : Set D) (j : ℤ) :
    relativeHomology R R (bottomPair S) j ≅ relativeHomology R R (P202Specs.RelativeFundamentalClass.BoxBottom.boundaryPair S) j := by
  letI := bottomInclusion_isIso R S j
  exact asIso ((relativeHomologyFunctor R R j).map (bottomInclusion S))

end BoxBottom

namespace CollarLocalization
open P202Specs.RelativeFundamentalClass.CollarLocalization
variable {M : Type v} [TopologicalSpace M]
def unionOpenHomeomorph (A B : Set M) :
    {b : B // b.val ∉ A} ≃ₜ {d : ↥(A ∪ B) // d.val ∉ A} where
  toFun b := ⟨⟨b.val.val, Or.inr b.val.property⟩, b.property⟩
  invFun d := ⟨⟨d.val.val, d.val.property.resolve_left d.property⟩, d.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _
  continuous_invFun := ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _

lemma unionBoundaryLocalInclusion_isIso (R : Type u) [CommRing R]
    [T2Space M] (A B : Set M) (hA : IsClosed A) (y : B) (hy : y.val ∉ A) (j : ℕ) :
    IsIso ((relativeHomologyFunctor R R (j : ℤ)).map
      (unionBoundaryLocalInclusion A B y)) := by
  let U : Set B := Subtype.val ⁻¹' Aᶜ
  let V : Set ↥(A ∪ B) := Subtype.val ⁻¹' Aᶜ
  let yu : U := ⟨y, hy⟩
  let e := unionOpenHomeomorph A B
  haveI := P202.LocalOrientation.openLocalInclusion_isIso R U
    (hA.isOpen_compl.preimage continuous_subtype_val) yu j
  haveI := P202.LocalOrientation.openLocalInclusion_isIso R V
    (hA.isOpen_compl.preimage continuous_subtype_val) (e yu) j
  have hs : P202.LocalOrientation.openLocalInclusion U yu ≫
      unionBoundaryLocalInclusion A B y =
      (P202.LocalOrientation.localPairIsoOfHomeomorph e yu).hom ≫
      P202.LocalOrientation.openLocalInclusion V (e yu) :=
    PairMap.ext _ _ rfl
  let F := relativeHomologyFunctor R R (j : ℤ)
  have he : F.map (P202.LocalOrientation.openLocalInclusion U yu) ≫
      F.map (unionBoundaryLocalInclusion A B y) =
      F.map (P202.LocalOrientation.localPairIsoOfHomeomorph e yu).hom ≫
      F.map (P202.LocalOrientation.openLocalInclusion V (e yu)) := by
    rw [← F.map_comp, hs, F.map_comp]
  haveI : IsIso (F.map (P202.LocalOrientation.openLocalInclusion U yu) ≫
      F.map (unionBoundaryLocalInclusion A B y)) := by
    rw [he]
    infer_instance
  exact IsIso.of_isIso_comp_left (F.map (P202.LocalOrientation.openLocalInclusion U yu)) _


section Categorical
variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {ι : Type w₁} {shape : ComplexShape ι}
  (K : TopCat.{v} ⥤ HomologicalComplex C shape)

lemma pairToTripleFirst_point_square (A B : Set M) (y : B) (hy : y.val ∉ A) :
    Triple.pairToTripleFirst K A (Set.subset_union_right : B ⊆ A ∪ B) ≫
      relativeMap K (triplePointMap A B y hy) =
    projection K (localPair B y) ≫ relativeMap K (unionBoundaryLocalInclusion A B y) := by
  change (K.map (Triple.subspaceInclusion (Set.subset_union_right : B ⊆ A ∪ B)) ≫
    projection K (Triple.subspacePair A (A ∪ B))) ≫
      relativeMap K (triplePointMap A B y hy) = _
  rw [Category.assoc, projection_map, projection_map]
  have hid : K.map (triplePointMap A B y hy).map = 𝟙 _ := K.map_id _
  rw [hid, Category.id_comp]
  rfl

/-- Naturality already identifies the restriction of the original connecting
image with the restriction of the genuine localized triple connecting image.
This equality uses the actual quotient and point maps, with no sign certificate. -/
lemma pairToTriple_connecting_point (A B : Set M) (y : B) (hy : y.val ∉ A)
    [Mono (inclusion K (boundaryPair M B))]
    [Mono (inclusion K (boundaryPair M (A ∪ B)))]
    (i j : ι) (hij : shape.Rel i j) :
    P202Specs.ChainLES.connecting
      (P202.RelativeSingularChains.sequence_shortExact K (boundaryPair M B)) i j hij ≫
      homologyMap (projection K (localPair B y)) j ≫
      homologyMap (relativeMap K (unionBoundaryLocalInclusion A B y)) j =
    homologyMap (relativeMap K (Triple.tripleProjection
        (Set.subset_union_right : B ⊆ A ∪ B))) i ≫
      P202Specs.ChainLES.connecting
        (Triple.triple_degreewiseShortExact K (Set.subset_union_left : A ⊆ A ∪ B)) i j hij ≫
      homologyMap (relativeMap K (triplePointMap A B y hy)) j := by
  have h := congrArg (fun f => f ≫ homologyMap
      (relativeMap K (triplePointMap A B y hy)) j)
    (Triple.pairToTriple_connecting K (Set.subset_union_left : A ⊆ A ∪ B)
      (Set.subset_union_right : B ⊆ A ∪ B) i j hij)
  have hs := congrArg (fun f => homologyMap f j)
    (pairToTripleFirst_point_square K A B y hy)
  simp only [homologyMap_comp] at hs
  rw [← hs]
  simpa only [Category.assoc] using h
end Categorical

lemma absoluteLocalValues_eq_projection (R : Type u) [CommRing R]
    (q : ℕ) {X : Type v} [TopologicalSpace X]
    (a : homology R R (TopCat.of X) (q : ℤ)) (y : X) :
    absoluteLocalValues R q a y =
      homologyMap (projection (ordinaryFunctor R R) (localPair X y)) (q : ℤ) a := by
  change ((relativeHomologyFunctor R R (q : ℤ)).map (pointMap (Set.mem_univ y)))
    (homologyMap (projection (ordinaryFunctor R R) (supportedPair X Set.univ)) (q : ℤ) a) = _
  have h := congrArg (fun f => homologyMap f (q : ℤ))
    (projection_map (ordinaryFunctor R R) (pointMap (Set.mem_univ y)))
  have hid : (ordinaryFunctor R R).map (pointMap (Set.mem_univ y)).map = 𝟙 _ :=
    (ordinaryFunctor R R).map_id _
  rw [hid, Category.id_comp, homologyMap_comp] at h
  exact congrArg (fun f => f a) h


/-- A closed controlling set inside U suffices for excision, provided its
complement is already in the pair's second term. It need not equal the support. -/
def openPairExcisionData (P : Pair.{v}) (U C : Set P.space)
    (hU : IsOpen U) (hC : IsClosed C) (hCU : C ⊆ U)
    (hCA : Cᶜ ⊆ P.subspace) : P202Specs.Excision.Data.{v} where
  pair := P
  removed := Uᶜ
  subset := fun _ hy => hCA (fun hc => hy (hCU hc))
  closure_subset := by
    rw [hU.isClosed_compl.closure_eq]
    exact Set.Subset.trans (fun _ hy hc => hy (hCU hc))
      (interior_maximal hCA hC.isOpen_compl)

def openPairExcisionIso (P : Pair.{v}) (U C : Set P.space)
    (hU : IsOpen U) (hC : IsClosed C) (hCU : C ⊆ U)
    (hCA : Cᶜ ⊆ P.subspace) :
    openPair P U ≅ (openPairExcisionData P U C hU hC hCU hCA).excised where
  hom := ⟨TopCat.ofHom ⟨fun z => ⟨z.val, not_not.mpr z.property⟩,
    continuous_subtype_val.subtype_mk _⟩, fun _ hz => hz⟩
  inv := ⟨TopCat.ofHom ⟨fun z => ⟨z.val, not_not.mp z.property⟩,
    continuous_subtype_val.subtype_mk _⟩, fun _ hz => hz⟩
  hom_inv_id := PairMap.ext _ _ rfl
  inv_hom_id := PairMap.ext _ _ rfl

lemma openPairInclusion_isIso (R : Type u) [CommRing R]
    (P : Pair.{v}) (U C : Set P.space)
    (hU : IsOpen U) (hC : IsClosed C) (hCU : C ⊆ U)
    (hCA : Cᶜ ⊆ P.subspace) (j : ℕ) :
    IsIso ((relativeHomologyFunctor R R (j : ℤ)).map (openPairInclusion P U)) := by
  have he : openPairInclusion P U =
      (openPairExcisionIso P U C hU hC hCU hCA).hom ≫
      (openPairExcisionData P U C hU hC hCU hCA).inclusion := PairMap.ext _ _ rfl
  haveI := P202.LocalOrientation.excision_integer R
    (openPairExcisionData P U C hU hC hCU hCA) j
  rw [he, Functor.map_comp]
  infer_instance

/-- The original closed collar-box localization has the required actual
excision isomorphism whenever C lies in the larger open collar box U. -/
lemma closedBoxExcision_isIso (R : Type u) [CommRing R]
    (C U B : Set M) (hU : IsOpen U) (hC : IsClosed C) (hCU : C ⊆ U) (j : ℕ) :
    IsIso ((relativeHomologyFunctor R R (j : ℤ)).map
      (openPairInclusion (boundaryPair M ((interior C)ᶜ ∪ B)) U)) :=
  openPairInclusion_isIso R (boundaryPair M ((interior C)ᶜ ∪ B)) U C hU hC hCU
    (fun x hy => show x ∈ (interior C)ᶜ ∪ B from
      Or.inl (fun hi => hy (interior_subset hi))) j


lemma connecting_target_congr {C : Type*} [Category* C] [Abelian C]
    {ι : Type*} {shape : ComplexShape ι} {S : ShortComplex (HomologicalComplex C shape)}
    (h : P202Specs.ChainLES.DegreewiseShortExact S) (i j j' : ι)
    (hij : shape.Rel i j) (hij' : shape.Rel i j') (e : j = j') :
    P202Specs.ChainLES.connecting h i j hij ≫
      eqToHom (congrArg (fun k => S.X₁.homology k) e) =
      P202Specs.ChainLES.connecting h i j' hij' := by
  subst j'
  simp

lemma boundaryHomSucc_eq_connecting (R : Type u) [CommRing R]
    (B : Set M)
    (h : P202Specs.ChainLES.DegreewiseShortExact
      (sequence (ordinaryFunctor R R) (boundaryPair M B))) (q : ℕ) :
    boundaryHomSucc R B h q =
      P202Specs.ChainLES.connecting h ((q + 1 : ℕ) : ℤ) (q : ℤ) (by simp) := by
  exact connecting_target_congr h _ _ _ _ _ (by omega)

/-- The original positive connecting image, evaluated at a boundary point,
is computed by the localized triple connecting map followed by its point map. -/
lemma boundaryHomSucc_local_formula (R : Type u) [CommRing R]
    (A B : Set M) (y : B) (hy : y.val ∉ A)
    (h : P202Specs.ChainLES.DegreewiseShortExact
      (sequence (ordinaryFunctor R R) (boundaryPair M B))) (q : ℕ)
    (g : relativeHomology R R (boundaryPair M B) ((q + 1 : ℕ) : ℤ)) :
    ((relativeHomologyFunctor R R (q : ℤ)).map (unionBoundaryLocalInclusion A B y))
      (connectingLocalValues R B h q g y) =
    ((relativeHomologyFunctor R R (q : ℤ)).map (triplePointMap A B y hy))
      (P202Specs.ChainLES.connecting
        (Triple.ordinary_triple_degreewiseShortExact R
          (Set.subset_union_left : A ⊆ A ∪ B))
        ((q + 1 : ℕ) : ℤ) (q : ℤ) (by simp)
        (((relativeHomologyFunctor R R ((q + 1 : ℕ) : ℤ)).map
          (Triple.tripleProjection (Set.subset_union_right : B ⊆ A ∪ B))) g)) := by
  change ((relativeHomologyFunctor R R (q : ℤ)).map (unionBoundaryLocalInclusion A B y))
    (absoluteLocalValues R q (boundaryHomSucc R B h q g) y) = _
  rw [absoluteLocalValues_eq_projection, boundaryHomSucc_eq_connecting]
  exact congrArg (fun f => f g)
    (pairToTriple_connecting_point (ordinaryFunctor R R) A B y hy
      ((q + 1 : ℕ) : ℤ) (q : ℤ) (by simp))

end CollarLocalization

theorem modelComparisons : P202Specs.RelativeFundamentalClass.Expected.modelComparisons.{u,v} := by
  constructor
  · intro R _ D _ S j
    exact BoxBottom.bottomInclusion_isIso R S j
  · intro R _ E _ _ j
    exact Disk.toLocal_isIso E R j

theorem localBoundaryComparison :
    P202Specs.RelativeFundamentalClass.Expected.localBoundaryComparison.{u,v} := by
  intro R _ M _ _ A B hA y hy j
  exact CollarLocalization.unionBoundaryLocalInclusion_isIso R A B hA y hy j

namespace Disk
open P202Specs.RelativeFundamentalClass.Disk
variable (E : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma add_ne_point (p : E) (x : {x : E // x ≠ 0}) : x.val+p ≠ p := by
  intro h
  exact x.property (add_right_cancel (h.trans (zero_add p).symm))

def punctureTranslation (p : E) : {x : E // x ≠ p} ≃ₜ {x : E // x ≠ 0} where
  toFun x := ⟨x.val-p, sub_ne_zero.mpr x.property⟩
  invFun x := ⟨x.val+p, add_ne_point E p x⟩
  left_inv x := Subtype.ext (sub_add_cancel _ _)
  right_inv x := Subtype.ext (add_sub_cancel_right _ _)
  continuous_toFun := (continuous_subtype_val.sub continuous_const).subtype_mk _
  continuous_invFun := (continuous_subtype_val.add continuous_const).subtype_mk _

lemma boundary_shift_ne_zero (p : E) (hp : ‖p‖ < 1) (t : unitInterval)
    (x : {x : UnitDisk E // ‖x.val‖ = 1}) : x.val.val - (1-t.val) • p ≠ 0 := by
  intro he
  have he' : x.val.val = (1-t.val) • p := sub_eq_zero.mp he
  have hx : ‖x.val.val‖ = 1 := x.property
  rw [he', norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr t.property.2)] at hx
  have hh : (1-t.val) * ‖p‖ ≤ ‖p‖ := by
    have := t.property.1
    nlinarith [norm_nonneg p]
  linarith

def boundaryTranslationHomotopy (p : E) (hp : ‖p‖ < 1) :
    ContinuousMap.Homotopy
      ((⟨punctureTranslation E p, (punctureTranslation E p).continuous⟩ : C({x : E // x ≠ p}, {x : E // x ≠ 0})).comp (toLocalAt E p hp).restrict.hom)
      (toLocal E).restrict.hom where
  toFun tx := ⟨tx.2.val.val - (1-tx.1.val) • p, boundary_shift_ne_zero E p hp tx.1 tx.2⟩
  continuous_toFun := ((continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)).sub
    ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul continuous_const)).subtype_mk _
  map_zero_left x := by apply Subtype.ext; change x.val.val - (1-(0:unitInterval).val) • p = x.val.val-p; simp
  map_one_left x := by apply Subtype.ext; change x.val.val - (1-(1:unitInterval).val) • p = x.val.val; simp

lemma boundaryAt_homology_isIso (R : Type u) [CommRing R] (p : E) (hp : ‖p‖ < 1) (j : ℤ) :
    IsIso ((homologyFunctor R R j).map (toLocalAt E p hp).restrict) := by
  let e : (localPair E p).sub ≅ (localPair E 0).sub :=
    TopCat.isoOfHomeo (punctureTranslation E p)
  have he : (homologyFunctor R R j).map ((toLocalAt E p hp).restrict ≫ e.hom) =
      (homologyFunctor R R j).map (toLocal E).restrict :=
    (P202.PrismHomotopy.homology R R (boundaryTranslationHomotopy E p hp) j).1
  haveI : IsIso ((homologyFunctor R R j).map ((toLocalAt E p hp).restrict ≫ e.hom)) := by
    rw [he]
    exact boundary_homology_isIso E R j
  haveI : IsIso ((homologyFunctor R R j).map (toLocalAt E p hp).restrict ≫
      (homologyFunctor R R j).map e.hom) := by rw [← Functor.map_comp]; infer_instance
  exact IsIso.of_isIso_comp_right _ ((homologyFunctor R R j).map e.hom)

/-- The actual closed-ball-to-local map is an isomorphism at every interior
point, in every integer degree and without any positive-dimensional premise. -/
theorem toLocalAt_isIso (R : Type u) [CommRing R] (p : E) (hp : ‖p‖ < 1) (j : ℤ) :
    IsIso ((relativeHomologyFunctor R R j).map (toLocalAt E p hp)) := by
  apply P202.LocalOrientation.relative_isIso_of_homology_isIso R R (toLocalAt E p hp)
  · exact boundaryAt_homology_isIso E R p hp
  · exact inclusion_homology_isIso E R
end Disk

namespace NormPrism
open P202Specs.RelativeFundamentalClass.NormPrism
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.RelativeFundamentalClass.Box P202Specs.LocalOrientation
open P202Specs.RelativeFundamentalClass.Disk
variable (V : Type v) [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma disk_norm_le (v : UnitDisk V) : ‖v.val‖ ≤ 1 := by
  simpa only [Metric.mem_closedBall, dist_zero_right] using v.property

lemma affine_abs_le (t : unitInterval) : |2*(t:ℝ)-1| ≤ 1 := by
  rw [abs_le]
  have := t.property.1
  have := t.property.2
  constructor <;> linarith

lemma affine_abs_eq_iff (t : unitInterval) :
    |2*(t:ℝ)-1| = 1 ↔ t = 0 ∨ t = 1 := by
  constructor
  · intro h
    rcases le_total 0 (2*(t:ℝ)-1) with hp | hn
    · rw [abs_of_nonneg hp] at h
      right; apply Subtype.ext; dsimp; linarith
    · rw [abs_of_nonpos hn] at h
      left; apply Subtype.ext; dsimp; linarith
  · rintro (h | h) <;> norm_num [h]

def ballHomeomorph : (unitInterval × UnitDisk V) ≃ₜ UnitDisk (ℝ × V) where
  toFun z := ⟨(2*(z.1:ℝ)-1,z.2.val), by
    rw [Metric.mem_closedBall, dist_zero_right, norm_prod_le_iff]
    exact ⟨by simpa only [Real.norm_eq_abs] using affine_abs_le z.1, disk_norm_le V z.2⟩⟩
  invFun w :=
    (⟨(w.val.1+1)/2, by
      have ht := (norm_fst_le w.val).trans (disk_norm_le (ℝ × V) w)
      rw [Real.norm_eq_abs, abs_le] at ht
      constructor <;> linarith⟩,
     ⟨w.val.2, by
      rw [Metric.mem_closedBall,dist_zero_right]
      exact (norm_snd_le w.val).trans (disk_norm_le (ℝ × V) w)⟩)
  left_inv z := by
    apply Prod.ext
    · apply Subtype.ext
      dsimp
      ring
    · rfl
  right_inv w := by
    apply Subtype.ext
    apply Prod.ext
    · dsimp; ring
    · rfl
  continuous_toFun := by
    exact (((continuous_const.mul (continuous_subtype_val.comp continuous_fst)).sub
      continuous_const).prodMk (continuous_subtype_val.comp continuous_snd)).subtype_mk _
  continuous_invFun := by
    exact ((((continuous_fst.comp continuous_subtype_val).add continuous_const).div_const 2).subtype_mk _).prodMk
      ((continuous_snd.comp continuous_subtype_val).subtype_mk _)

lemma ballHomeomorph_boundary_iff (z : unitInterval × UnitDisk V) :
    z ∈ fullBoundary (sphereSubset V) ↔ ‖(ballHomeomorph V z).val‖ = 1 := by
  change (z.1 = 0 ∨ z.1 = 1 ∨ ‖z.2.val‖ = 1) ↔ max |2*(z.1:ℝ)-1| ‖z.2.val‖ = 1
  have ht := affine_abs_le z.1
  have hv := disk_norm_le V z.2
  rw [← or_assoc, ← affine_abs_eq_iff z.1]
  constructor
  · rintro (h | h)
    · rw [h,max_eq_left hv]
    · rw [h,max_eq_right ht]
  · intro h
    rcases le_total |2*(z.1:ℝ)-1| ‖z.2.val‖ with hle | hle
    · right; rwa [max_eq_right hle] at h
    · left; rwa [max_eq_left hle] at h

def pairIso : prismPair V ≅ unitPair (ℝ × V) where
  hom := ⟨TopCat.ofHom ⟨ballHomeomorph V, (ballHomeomorph V).continuous⟩,
    fun z hz => (ballHomeomorph_boundary_iff V z).mp hz⟩
  inv := ⟨TopCat.ofHom ⟨(ballHomeomorph V).symm, (ballHomeomorph V).symm.continuous⟩,
    fun w hw => (ballHomeomorph_boundary_iff V ((ballHomeomorph V).symm w)).mpr (by
      change ‖w.val‖ = 1 at hw
      simpa only [Homeomorph.apply_symm_apply] using hw)⟩
  hom_inv_id := PairMap.ext _ _ (by ext z; exact (ballHomeomorph V).symm_apply_apply z)
  inv_hom_id := PairMap.ext _ _ (by ext w; exact (ballHomeomorph V).apply_symm_apply w)

@[simp] lemma ballHomeomorph_center :
    ballHomeomorph V (center V) = origin (ℝ × V) := by
  apply Subtype.ext
  apply Prod.ext <;> norm_num [ballHomeomorph,center,origin]

lemma toAmbientLocal_factor :
    (pairIso V).hom ≫ toLocal (ℝ × V) = toAmbientLocal V := PairMap.ext _ _ rfl

@[simp] lemma toAmbientLocal_apply (z : unitInterval × UnitDisk V) :
    (toAmbientLocal V).map z = (2*(z.1:ℝ)-1,z.2.val) := rfl

theorem toAmbientLocal_isIso (R : Type u) [CommRing R] (j : ℤ) :
    IsIso ((relativeHomologyFunctor R R j).map (toAmbientLocal V)) := by
  rw [← toAmbientLocal_factor,Functor.map_comp]
  haveI := P202.RelativeFundamentalClass.Disk.toLocal_isIso (ℝ × V) R j
  infer_instance

end NormPrism

namespace SubspaceLocal
open P202Specs.RelativeFundamentalClass.SubspaceLocal
open P202Specs.SingularChains P202Specs.RelativeSingularChains P202Specs.LocalOrientation
variable {X : Type v} [TopologicalSpace X] [T2Space X]

def excisionData (T : Set X) (x : T) (hx : x.val ∈ interior T) :
    P202Specs.Excision.Data.{v} where
  pair := localPair X x.val
  removed := Tᶜ
  subset := fun _ hy he => hy (he ▸ x.property)
  closure_subset := by
    have hopen : IsOpen {y : X | y ≠ x.val} := isClosed_singleton.isOpen_compl
    change closure Tᶜ ⊆ interior {y : X | y ≠ x.val}
    rw [hopen.interior_eq,closure_compl]
    intro y hy he
    exact hy (he ▸ hx)

def excisionIso (T : Set X) (x : T) (hx : x.val ∈ interior T) :
    localPair T x ≅ (excisionData T x hx).excised where
  hom := ⟨TopCat.ofHom {
    toFun := fun y => ⟨y.val, by
      change ¬ y.val ∈ Tᶜ
      simpa only [Set.mem_compl_iff, not_not] using y.property⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      exact continuous_subtype_val },
    fun _ hy he => hy (Subtype.ext he)⟩
  inv := ⟨TopCat.ofHom {
    toFun := fun y => ⟨y.val, by
      have hy := y.property
      change ¬ y.val ∈ Tᶜ at hy
      simpa only [Set.mem_compl_iff, not_not] using hy⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      exact continuous_subtype_val },
    fun _ hy he => hy (congrArg Subtype.val he)⟩
  hom_inv_id := PairMap.ext _ _ rfl
  inv_hom_id := PairMap.ext _ _ rfl

lemma inclusion_factor (T : Set X) (x : T) (hx : x.val ∈ interior T) :
    (excisionIso T x hx).hom ≫ (excisionData T x hx).inclusion = localInclusion T x :=
  PairMap.ext _ _ rfl

lemma localInclusion_isIso (R : Type u) [CommRing R] (T : Set X) (x : T)
    (hx : x.val ∈ interior T) (j : ℤ) :
    IsIso ((relativeHomologyFunctor R R j).map (localInclusion T x)) := by
  cases j with
  | ofNat j =>
    rw [← inclusion_factor T x hx,Functor.map_comp]
    haveI := P202.LocalOrientation.excision_integer R (excisionData T x hx) j
    infer_instance
  | negSucc j =>
    exact (P202.RelativeSingularChains.ordinary_negative R R (localPair T x) _ (by omega)).2.isIso
      (P202.RelativeSingularChains.ordinary_negative R R (localPair X x.val) _ (by omega)).2 _
end SubspaceLocal


namespace NormPrism
open P202Specs.RelativeFundamentalClass.NormPrism
open P202Specs.SingularChains P202Specs.RelativeSingularChains P202Specs.LocalOrientation
open P202Specs.RelativeFundamentalClass.Disk
variable (V : Type v) [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma origin_mem_interior_disk : (0 : V) ∈ interior (Metric.closedBall (0 : V) 1) := by
  exact interior_maximal Metric.ball_subset_closedBall Metric.isOpen_ball (by simp)

lemma ballToOwnLocal_isIso (R : Type u) [CommRing R] (j : ℤ) :
    IsIso ((relativeHomologyFunctor R R j).map (ballToOwnLocal V)) := by
  let L := P202Specs.RelativeFundamentalClass.SubspaceLocal.localInclusion (Metric.closedBall (0 : ℝ × V) 1) (origin (ℝ × V))
  haveI : IsIso ((relativeHomologyFunctor R R j).map L) :=
    SubspaceLocal.localInclusion_isIso R _ _ (origin_mem_interior_disk (ℝ × V)) j
  have hf : ballToOwnLocal V ≫ L = toLocal (ℝ × V) := PairMap.ext _ _ rfl
  haveI : IsIso ((relativeHomologyFunctor R R j).map (ballToOwnLocal V) ≫
      (relativeHomologyFunctor R R j).map L) := by
    rw [← Functor.map_comp,hf]
    exact P202.RelativeFundamentalClass.Disk.toLocal_isIso (ℝ × V) R j
  exact IsIso.of_isIso_comp_right _ ((relativeHomologyFunctor R R j).map L)

def ownLocalIso : localPair (unitInterval × UnitDisk V) (center V) ≅
    localPair (UnitDisk (ℝ × V)) (origin (ℝ × V)) where
  hom := ⟨TopCat.ofHom ⟨ballHomeomorph V,(ballHomeomorph V).continuous⟩, by
    intro z hz he
    apply hz
    apply (ballHomeomorph V).injective
    exact he.trans (ballHomeomorph_center V).symm⟩
  inv := ⟨TopCat.ofHom ⟨(ballHomeomorph V).symm,(ballHomeomorph V).symm.continuous⟩, by
    intro w hw he
    apply hw
    calc w = ballHomeomorph V ((ballHomeomorph V).symm w) :=
          ((ballHomeomorph V).apply_symm_apply w).symm
      _ = ballHomeomorph V (center V) := congrArg (ballHomeomorph V) he
      _ = origin (ℝ × V) := ballHomeomorph_center V⟩
  hom_inv_id := PairMap.ext _ _ (by ext z; exact (ballHomeomorph V).symm_apply_apply z)
  inv_hom_id := PairMap.ext _ _ (by ext w; exact (ballHomeomorph V).apply_symm_apply w)

lemma ownLocal_square :
    P202Specs.RelativeFundamentalClass.NormPrism.toOwnLocal V ≫ (ownLocalIso V).hom = (pairIso V).hom ≫ ballToOwnLocal V :=
  PairMap.ext _ _ rfl

lemma toOwnLocal_isIso (R : Type u) [CommRing R] (j : ℤ) :
    IsIso ((relativeHomologyFunctor R R j).map (P202Specs.RelativeFundamentalClass.NormPrism.toOwnLocal V)) := by
  let H := relativeHomologyFunctor R R j
  haveI := ballToOwnLocal_isIso V R j
  haveI : IsIso (H.map (P202Specs.RelativeFundamentalClass.NormPrism.toOwnLocal V) ≫ H.map (ownLocalIso V).hom) := by
    rw [← H.map_comp,ownLocal_square,H.map_comp]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (H.map (ownLocalIso V).hom)

end NormPrism

namespace PrismLift
open P202Specs.RelativeFundamentalClass.PrismLift
open P202Specs.ChainLES
variable {R : Type u} [CommRing R]
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.RelativeFundamentalClass P202Specs.RelativeFundamentalClass.Triple
open P202Specs.AlexanderWhitney P202Specs.ShuffleModel
open scoped TensorProduct

lemma positiveInterval_upper (x : StdSimplex 0) :
    simplexEquiv (TopCat.of unitInterval) 0 (face 0 positiveInterval) x = 1 := by
  rw [P202.SingularChains.simplexEquiv_face]
  apply Subtype.ext
  change ((faceInclusion 0 x).weights 1) = 1
  rw [P202.ShuffleBoundary.simplex_zero_unique x]
  rw [P202.SingularChains.faceInclusion_vertex]
  simp

lemma positiveInterval_lower (x : StdSimplex 0) :
    simplexEquiv (TopCat.of unitInterval) 0 (face 1 positiveInterval) x = 0 := by
  rw [P202.SingularChains.simplexEquiv_face]
  apply Subtype.ext
  change ((faceInclusion 1 x).weights 1) = 0
  rw [P202.ShuffleBoundary.simplex_zero_unique x]
  rw [P202.SingularChains.faceInclusion_vertex]
  simp

@[simp] lemma quotientChain_coordinates (P : Pair.{w}) (n : ℕ) (c : Chains R P.space n) :
    (ordinaryDegreeIso R R P n).hom (quotientChain R P n c) =
      (projection (chainFunctor R R) P).f n c := by
  simp [quotientChain]

lemma quotientChain_boundary (P : Pair.{w}) (n : ℕ) (c : Chains R P.space (n+1)) :
    (ordinary R R P).d (n+1 : ℕ) n (quotientChain R P (n+1) c) =
      quotientChain R P n (boundary R R P.space n c) := by
  apply ((ModuleCat.mono_iff_injective (ordinaryDegreeIso R R P n).hom).mp inferInstance)
  rw [quotientChain_coordinates]
  have h := congrArg (fun f => f ((projection (chainFunctor R R) P).f (n+1) c))
    (P202.RelativeSingularChains.ordinary_boundary R R P n)
  change (ordinaryDegreeIso R R P n).hom
      ((ordinary R R P).d (n+1 : ℕ) n (quotientChain R P (n+1) c)) =
      (nonnegative R R P).d (n+1) n
        ((projection (chainFunctor R R) P).f (n+1) c) at h
  rw [h]
  exact congrArg (fun f => f c) ((projection (chainFunctor R R) P).comm (n+1) n)

lemma quotientChain_naturality {P Q : Pair.{w}} (f : P ⟶ Q) (n : ℕ)
    (c : Chains R P.space n) :
    (relativeMap (ordinaryFunctor R R) f).f (n : ℤ) (quotientChain R P n c) =
      quotientChain R Q n ((chainMap R R f.map).f n c) := by
  apply ((ModuleCat.mono_iff_injective (ordinaryDegreeIso R R Q n).hom).mp inferInstance)
  rw [quotientChain_coordinates]
  have h := congrArg (fun f => f (quotientChain R P n c))
    (P202.MayerVietoris.ordinaryDegreeIso_naturality R f n)
  change (ordinaryDegreeIso R R Q n).hom
      ((relativeMap (ordinaryFunctor R R) f).f (n : ℤ) (quotientChain R P n c)) =
    (relativeMap (chainFunctor R R) f).f n
      ((ordinaryDegreeIso R R P n).hom (quotientChain R P n c)) at h
  rw [h, quotientChain_coordinates]
  exact congrArg (fun f => f c) (HomologicalComplex.congr_hom (projection_map (chainFunctor R R) f) n)

lemma projection_eq_zero_iff_support (P : Pair.{w}) (n : ℕ) (c : Chains R P.space n) :
    (projection (chainFunctor R R) P).f n c = 0 ↔
      ∀ τ ∈ c.support, InSubspace P n τ := by
  classical
  obtain ⟨e, he⟩ := P202.RelativeSingularChains.quotient_coordinates R R P n
  constructor
  · intro hc τ hτ
    by_contra ht
    have hz : outsideProjection R R P n c = 0 := by rw [← he c, hc, map_zero]
    have hzτ := congrArg (fun f => f ⟨τ, ht⟩) hz
    have : c τ = 0 := hzτ
    exact Finsupp.mem_support_iff.mp hτ this
  · intro hc
    apply e.injective
    rw [map_zero, he c]
    ext τ
    change c τ.val = 0
    by_contra ht
    exact τ.property (hc τ.val (Finsupp.mem_support_iff.mpr ht))

lemma cycleClass_congr (K : ChainComplex (ModuleCat.{v} R) ℤ)
    {i j : ℤ} (hj : (ComplexShape.down ℤ).next i = j)
    (z z' : K.X i) (hz : K.d i j z = 0) (hz' : K.d i j z' = 0) (h : z=z') :
    cycleClass K j hj z hz = cycleClass K j hj z' hz' := by
  subst z'
  rfl

lemma cycleClass_map {K L : ChainComplex (ModuleCat.{v} R) ℤ} (f : K ⟶ L)
    {i j : ℤ} (hj : (ComplexShape.down ℤ).next i = j)
    (z : K.X i) (hz : K.d i j z = 0) :
    (homologyMap f i) (cycleClass K j hj z hz) =
      cycleClass L j hj (f.f i z) (by
        change L.d i j (f.f i z) = 0
        have h := congrArg (fun f => f z) (f.comm i j)
        change L.d i j (f.f i z) = f.f j (K.d i j z) at h
        rw [h, hz, map_zero]) := by
  have hc : (cyclesMap f i) (K.cyclesMk z j hj hz) =
      L.cyclesMk (f.f i z) j hj (by
        change L.d i j (f.f i z) = 0
        have h := congrArg (fun f => f z) (f.comm i j)
        change L.d i j (f.f i z) = f.f j (K.d i j z) at h
        rw [h, hz, map_zero]) := by
    apply (ModuleCat.mono_iff_injective (L.iCycles i)).mp inferInstance
    change ((cyclesMap f i) ≫ L.iCycles i) (K.cyclesMk z j hj hz) = _
    rw [cyclesMap_i]
    change (f.f i) ((K.iCycles i) (K.cyclesMk z j hj hz)) = _
    change ((forget₂ (ModuleCat R) Ab).map (f.f i))
      (((forget₂ (ModuleCat R) Ab).map (K.iCycles i)) (K.cyclesMk z j hj hz)) =
      ((forget₂ (ModuleCat R) Ab).map (L.iCycles i)) _
    simp only [i_cyclesMk]
    rfl
  unfold cycleClass
  have hh := congrArg (fun f => f (K.cyclesMk z j hj hz)) (homologyπ_naturality f i)
  change (homologyMap f i) ((K.homologyπ i) (K.cyclesMk z j hj hz)) =
    (L.homologyπ i) ((cyclesMap f i) (K.cyclesMk z j hj hz)) at hh
  rw [hc] at hh
  exact hh

lemma cycleClass_neg (K : ChainComplex (ModuleCat.{v} R) ℤ)
    {i j : ℤ} (hj : (ComplexShape.down ℤ).next i = j)
    (b : K.X i) (hb : K.d i j b = 0) :
    cycleClass K j hj (-b) (by change K.d i j (-b) = 0; simp [hb]) =
      -cycleClass K j hj b hb := by
  have hc : K.cyclesMk (-b) j hj (by change K.d i j (-b) = 0; simp [hb]) =
      -K.cyclesMk b j hj hb := by
    apply (ModuleCat.mono_iff_injective (K.iCycles i)).mp inferInstance
    change (forget₂ (ModuleCat R) Ab).map (K.iCycles i) _ =
      (forget₂ (ModuleCat R) Ab).map (K.iCycles i) _
    simp only [map_neg, i_cyclesMk]
  unfold cycleClass
  rw [hc, map_neg]

/-- A negative boundary identity in the middle complex determines the actual
positive connecting map, because the first chain map is injective. -/
lemma connecting_of_negative_boundary
    (S : ShortComplex (ChainComplex (ModuleCat.{v} R) ℤ))
    (h : DegreewiseShortExact S) (i j : ℤ) (hij : (ComplexShape.down ℤ).Rel i j)
    (p : S.X₂.X i) (b : S.X₁.X j)
    (hboundary : S.X₂.d i j p = -(S.f.f j b)) :
    ∃ (hp : S.X₃.d i j (S.g.f i p) = 0)
      (hb : S.X₁.d j ((ComplexShape.down ℤ).next j) b = 0),
      (connecting h i j hij)
        (cycleClass S.X₃ j ((ComplexShape.down ℤ).next_eq' hij) (S.g.f i p) hp) =
      -cycleClass S.X₁ ((ComplexShape.down ℤ).next j) rfl b hb := by
  have hs := HomologicalComplex.shortExact_of_degreewise_shortExact S h
  have hx : S.f.f j (-b) = S.X₂.d i j p := by simpa only [map_neg] using hboundary.symm
  have hbn : S.X₁.d j ((ComplexShape.down ℤ).next j) (-b) = 0 :=
    hs.d_eq_zero_of_f_eq_d_apply i j p (-b) hx _
  have hb : S.X₁.d j ((ComplexShape.down ℤ).next j) b = 0 := by
    simpa only [map_neg, neg_eq_zero] using hbn
  have hp : S.X₃.d i j (S.g.f i p) = 0 := by
    have hz := congrArg (fun f => f p) (S.g.comm i j)
    change S.X₃.d i j (S.g.f i p) = S.g.f j (S.X₂.d i j p) at hz
    rw [hz, hboundary, map_neg]
    have hfg := congrArg (fun f => f b) (HomologicalComplex.congr_hom S.zero j)
    change S.g.f j (S.f.f j b) = 0 at hfg
    rw [hfg, neg_zero]
  refine ⟨hp, hb, ?_⟩
  rw [← cycleClass_neg S.X₁ rfl b hb]
  exact P202.ChainLES.lift_formula S h i j hij _ hp p rfl (-b) hx hbn

lemma triple_connecting_of_nonnegative_boundary
    {M : Type w} [TopologicalSpace M] {A B : Set M} (hAB : A ⊆ B)
    (n : ℕ) (p : Chains R (TopCat.of M) (n+1))
    (b : Chains R (TopCat.of B) n)
    (hboundary :
      (projection (chainFunctor R R) (boundaryPair M A)).f n
        (boundary R R (TopCat.of M) n p) =
      -((projection (chainFunctor R R) (boundaryPair M A)).f n
        ((chainMap R R (tripleInclusion A B).map).f n b))) :
    ∃ (hp : (ordinary R R (boundaryPair M B)).d (n+1 : ℕ) n
          (quotientChain R (boundaryPair M B) (n+1) p) = 0)
      (hb : (ordinary R R (subspacePair A B)).d (n : ℤ) ((ComplexShape.down ℤ).next (n : ℤ))
          (quotientChain R (subspacePair A B) n b) = 0),
      (connecting (Triple.ordinary_triple_degreewiseShortExact R hAB)
        (n+1 : ℕ) n (by simp))
        (cycleClass (ordinary R R (boundaryPair M B)) (n : ℤ) (by simp)
          (quotientChain R (boundaryPair M B) (n+1) p) hp) =
      -cycleClass (ordinary R R (subspacePair A B)) ((ComplexShape.down ℤ).next (n : ℤ)) rfl
          (quotientChain R (subspacePair A B) n b) hb := by
  let S := tripleSequence (ordinaryFunctor R R) hAB
  have h := Triple.ordinary_triple_degreewiseShortExact R hAB
  have heq : S.X₂.d (n+1 : ℕ) n (quotientChain R (boundaryPair M A) (n+1) p) =
      -(S.f.f (n : ℤ) (quotientChain R (subspacePair A B) n b)) := by
    change (ordinary R R (boundaryPair M A)).d (n+1 : ℕ) n
      (quotientChain R (boundaryPair M A) (n+1) p) =
      -((relativeMap (ordinaryFunctor R R) (tripleInclusion A B)).f (n : ℤ)
        (quotientChain R (subspacePair A B) n b))
    rw [quotientChain_boundary]
    rw [quotientChain_naturality]
    unfold quotientChain
    exact (congrArg ((ordinaryDegreeIso R R (boundaryPair M A) n).inv) hboundary).trans
      (map_neg (ordinaryDegreeIso R R (boundaryPair M A) n).inv.hom _)
  have hprojection : S.g.f (n+1 : ℕ)
      (quotientChain R (boundaryPair M A) (n+1) p) =
      quotientChain R (boundaryPair M B) (n+1) p := by
    change (relativeMap (ordinaryFunctor R R) (tripleProjection hAB)).f (n+1 : ℕ)
      (quotientChain R (boundaryPair M A) (n+1) p) = _
    rw [quotientChain_naturality]
    change quotientChain R (boundaryPair M B) (n+1)
      ((chainMap R R (𝟙 _)).f (n+1) p) = _
    have hid : chainMap R R (𝟙 (boundaryPair M B).space) = 𝟙 _ :=
      (chainFunctor R R).map_id _
    rw [hid]
    rfl
  obtain ⟨hp, hb, hformula⟩ := connecting_of_negative_boundary S h
    (n+1 : ℕ) n (by simp) (quotientChain R (boundaryPair M A) (n+1) p)
    (quotientChain R (subspacePair A B) n b) heq
  simp only [hprojection] at hp hformula
  refine ⟨hp, ?_, ?_⟩
  · simpa [S, tripleSequence] using hb
  · simpa [S, tripleSequence] using hformula

lemma lowerShuffle_eq_bottomChain {D : Type} [TopologicalSpace D]
    (S : Set D) (n : ℕ) (c : Chains R (TopCat.of D) n) :
    shuffle R (TopCat.of unitInterval) (TopCat.of D) n
      (Pi.single (⟨(0,n), by omega⟩ : Diagonal n)
        (Finsupp.single (face 1 positiveInterval) 1 ⊗ₜ[R] c)) =
    (chainMap R R (tripleInclusion (Box.upperLateral S) (Box.fullBoundary S)).map).f n
      (bottomChain R S n c) := by
  have h₁ := LinearMap.congr_fun
    (P202.ShuffleBoundary.component_zero_left_map R (face 1 positiveInterval) n) c
  have hm : (P202Specs.RelativeFundamentalClass.BoxBottom.bottomInclusion S).map ≫
      (tripleInclusion (Box.upperLateral S) (Box.fullBoundary S)).map =
        P202.ShuffleBoundary.insertLeft (face 1 positiveInterval) := by
    ext x
    change (0,x) = (simplexEquiv (TopCat.of unitInterval) 0
      (face 1 positiveInterval) (Convexity.StdSimplex.single 0),x)
    rw [positiveInterval_lower]
  have h₂ := congrArg (fun f => f c)
    (HomologicalComplex.congr_hom ((chainFunctor R R).map_comp
      (P202Specs.RelativeFundamentalClass.BoxBottom.bottomInclusion S).map
      (tripleInclusion (Box.upperLateral S) (Box.fullBoundary S)).map) n)
  change (chainMap R R ((P202Specs.RelativeFundamentalClass.BoxBottom.bottomInclusion S).map ≫
      (tripleInclusion (Box.upperLateral S) (Box.fullBoundary S)).map)).f n c =
    (chainMap R R (tripleInclusion (Box.upperLateral S) (Box.fullBoundary S)).map).f n
      (bottomChain R S n c) at h₂
  rw [hm] at h₂
  rw [P202.ShuffleBoundary.shuffle_single]
  exact h₁.trans h₂

lemma cast_shuffle_single (X Y : TopCat.{w}) {p q n m : ℕ}
    (hpq : p+q=n) (hnm : n=m)
    (z : Chains R X p ⊗[R] Chains R Y q) :
    castChains R hnm (shuffle R X Y n (Pi.single (⟨(p,q), hpq⟩ : Diagonal n) z)) =
      shuffle R X Y m (Pi.single (⟨(p,q), hpq.trans hnm⟩ : Diagonal m) z) := by
  rw [P202.ShuffleBoundary.shuffle_single, P202.ShuffleBoundary.shuffle_single,
    P202.ShuffleBoundary.castChains_comp_castChains]

lemma negativeBoundary_cast (P : Pair.{w}) {n m : ℕ} (hnm : n=m)
    (p : Chains R P.space (n+1)) (b : Chains R P.space n)
    (h : (projection (chainFunctor R R) P).f n (boundary R R P.space n p) =
      -((projection (chainFunctor R R) P).f n b)) :
    (projection (chainFunctor R R) P).f m
      (boundary R R P.space m (castChains R (congrArg (·+1) hnm) p)) =
    -((projection (chainFunctor R R) P).f m (castChains R hnm b)) := by
  subst m
  exact h

/-- Geometric boundary support of the disk chain gives the signed prism boundary
identity in the actual quotient by upper and lateral faces. -/
lemma prismChain_boundary_quotient {D : Type} [TopologicalSpace D]
    (S : Set D) (n : ℕ) (c : Chains R (TopCat.of D) n)
    (hc : ∀ q (hn : n = q+1), ∀ τ ∈ (boundary R R (TopCat.of D) q (hn ▸ c)).support,
      InSubspace (P202Specs.RelativeFundamentalClass.BoxBottom.bottomPair S) q τ) :
    (projection (chainFunctor R R) (boundaryPair (unitInterval × D) (Box.upperLateral S))).f n
      (boundary R R (TopCat.of (unitInterval × D)) n (prismChain R (TopCat.of D) n c)) =
    -((projection (chainFunctor R R) (boundaryPair (unitInterval × D) (Box.upperLateral S))).f n
      ((chainMap R R (tripleInclusion (Box.upperLateral S) (Box.fullBoundary S)).map).f n
        (bottomChain R S n c))) := by
  rw [← lowerShuffle_eq_bottomChain]
  cases n with
  | zero =>
    apply BoxBoundary.lowerFace_quotient_zero R (TopCat.of unitInterval) (TopCat.of D)
      (Box.upperLateral S) positiveInterval c
    intro τ hτ x y
    exact Or.inl (positiveInterval_upper x)
  | succ q =>
    have h := BoxBoundary.lowerFace_quotient R (TopCat.of unitInterval) (TopCat.of D)
      (Box.upperLateral S) q positiveInterval c
      (fun τ hτ x y => Or.inl (positiveInterval_upper x))
      (fun τ hτ x y => Or.inr (hc q rfl τ hτ y))
    have h' := negativeBoundary_cast
      (⟨productSpace (TopCat.of unitInterval) (TopCat.of D), Box.upperLateral S⟩ : Pair)
      (by omega : 0+q+1 = q+1) _ _ h
    simp only [cast_shuffle_single] at h'
    exact h' 

lemma prismChain_boundary_quotient_of_cycle {D : Type} [TopologicalSpace D]
    (S : Set D) (n : ℕ) (c : Chains R (TopCat.of D) n)
    (hc : (ordinary R R (P202Specs.RelativeFundamentalClass.BoxBottom.bottomPair S)).d
      (n : ℤ) ((ComplexShape.down ℤ).next (n : ℤ))
      (quotientChain R (P202Specs.RelativeFundamentalClass.BoxBottom.bottomPair S) n c) = 0) :
    (projection (chainFunctor R R) (boundaryPair (unitInterval × D) (Box.upperLateral S))).f n
      (boundary R R (TopCat.of (unitInterval × D)) n (prismChain R (TopCat.of D) n c)) =
    -((projection (chainFunctor R R) (boundaryPair (unitInterval × D) (Box.upperLateral S))).f n
      ((chainMap R R (tripleInclusion (Box.upperLateral S) (Box.fullBoundary S)).map).f n
        (bottomChain R S n c))) := by
  apply prismChain_boundary_quotient S n c
  intro q hn
  subst n
  have hnext : (ComplexShape.down ℤ).next ((q+1 : ℕ) : ℤ) = (q : ℤ) :=
    (ComplexShape.down ℤ).next_eq' (by simp)
  rw [hnext, quotientChain_boundary] at hc
  have hzero := congrArg
    ((ordinaryDegreeIso R R (P202Specs.RelativeFundamentalClass.BoxBottom.bottomPair S) q).hom) hc
  rw [quotientChain_coordinates, map_zero] at hzero
  exact (projection_eq_zero_iff_support _ q _).mp hzero

/-- The model lower-face sign is the actual ordinary connecting formula.
The only premise is that the chosen disk chain represents a relative cycle. -/
lemma prismChain_connecting {D : Type} [TopologicalSpace D]
    (S : Set D) (n : ℕ) (c : Chains R (TopCat.of D) n)
    (hc : (ordinary R R (P202Specs.RelativeFundamentalClass.BoxBottom.bottomPair S)).d
      (n : ℤ) ((ComplexShape.down ℤ).next (n : ℤ))
      (quotientChain R (P202Specs.RelativeFundamentalClass.BoxBottom.bottomPair S) n c) = 0) :
    ∃ hp : (ordinary R R (boundaryPair (unitInterval × D) (Box.fullBoundary S))).d
      (n+1 : ℕ) n
      (quotientChain R (boundaryPair (unitInterval × D) (Box.fullBoundary S)) (n+1)
        (prismChain R (TopCat.of D) n c)) = 0,
      (connecting (Triple.ordinary_triple_degreewiseShortExact R
          (Box.upperLateral_subset_fullBoundary S)) (n+1 : ℕ) n (by simp))
        (cycleClass (ordinary R R (boundaryPair (unitInterval × D) (Box.fullBoundary S)))
          (n : ℤ) (by simp)
          (quotientChain R (boundaryPair (unitInterval × D) (Box.fullBoundary S)) (n+1)
            (prismChain R (TopCat.of D) n c)) hp) =
      -((homologyMap (relativeMap (ordinaryFunctor R R)
          (P202Specs.RelativeFundamentalClass.BoxBottom.bottomInclusion S)) (n : ℤ))
        (cycleClass (ordinary R R (P202Specs.RelativeFundamentalClass.BoxBottom.bottomPair S))
          ((ComplexShape.down ℤ).next (n : ℤ)) rfl
          (quotientChain R (P202Specs.RelativeFundamentalClass.BoxBottom.bottomPair S) n c) hc)) := by
  obtain ⟨hp, hb, hδ⟩ := triple_connecting_of_nonnegative_boundary
    (Box.upperLateral_subset_fullBoundary S) n (prismChain R (TopCat.of D) n c)
    (bottomChain R S n c) (prismChain_boundary_quotient_of_cycle S n c hc)
  refine ⟨hp, ?_⟩
  have hm := cycleClass_map
    (relativeMap (ordinaryFunctor R R)
      (P202Specs.RelativeFundamentalClass.BoxBottom.bottomInclusion S)) rfl
    (quotientChain R (P202Specs.RelativeFundamentalClass.BoxBottom.bottomPair S) n c) hc
  have hm' := hm.trans (cycleClass_congr _ rfl _ _ _ hb
    (quotientChain_naturality (P202Specs.RelativeFundamentalClass.BoxBottom.bottomInclusion S) n c))
  exact hδ.trans (congrArg Neg.neg hm'.symm)

/-- A bottom relative generator produces a genuine top relative prism generator;
no Künneth or unproved shuffle orientation certificate is needed. -/
lemma prismChain_isGenerator {D : Type} [TopologicalSpace D]
    (S : Set D) (n : ℕ) (c : Chains R (TopCat.of D) n)
    (hc : (ordinary R R (P202Specs.RelativeFundamentalClass.BoxBottom.bottomPair S)).d
      (n : ℤ) ((ComplexShape.down ℤ).next (n : ℤ))
      (quotientChain R (P202Specs.RelativeFundamentalClass.BoxBottom.bottomPair S) n c) = 0)
    (hgen : P202Specs.LocalOrientation.IsGenerator
      (V := (ordinary R R (P202Specs.RelativeFundamentalClass.BoxBottom.bottomPair S)).homology (n : ℤ)) R
      (cycleClass (ordinary R R (P202Specs.RelativeFundamentalClass.BoxBottom.bottomPair S))
        ((ComplexShape.down ℤ).next (n : ℤ)) rfl
        (quotientChain R (P202Specs.RelativeFundamentalClass.BoxBottom.bottomPair S) n c) hc)) :
    ∃ hp : (ordinary R R (boundaryPair (unitInterval × D) (Box.fullBoundary S))).d
      (n+1 : ℕ) n
      (quotientChain R (boundaryPair (unitInterval × D) (Box.fullBoundary S)) (n+1)
        (prismChain R (TopCat.of D) n c)) = 0,
      P202Specs.LocalOrientation.IsGenerator
        (V := (ordinary R R (boundaryPair (unitInterval × D) (Box.fullBoundary S))).homology (n+1 : ℕ)) R
        (cycleClass (ordinary R R (boundaryPair (unitInterval × D) (Box.fullBoundary S)))
          (n : ℤ) (by simp)
          (quotientChain R (boundaryPair (unitInterval × D) (Box.fullBoundary S)) (n+1)
            (prismChain R (TopCat.of D) n c)) hp) := by
  obtain ⟨hp, hδ⟩ := prismChain_connecting S n c hc
  refine ⟨hp, ?_⟩
  have hij : (ComplexShape.down ℤ).Rel ((n+1 : ℕ) : ℤ) (n : ℤ) := by simp
  haveI := Triple.triple_connecting_isIso (ordinaryFunctor R R)
    (Box.upperLateral_subset_fullBoundary S) (n+1 : ℕ) (n : ℤ) hij
    (Box.upperLateral_relative_isZero R S (n+1 : ℕ))
    (Box.upperLateral_relative_isZero R S (n : ℤ))
  apply (P202.LocalOrientation.generator_map_iff R
    (asIso (connecting (Triple.ordinary_triple_degreewiseShortExact R
      (Box.upperLateral_subset_fullBoundary S)) (n+1 : ℕ) (n : ℤ) hij)).toLinearEquiv _).mp
  change P202Specs.LocalOrientation.IsGenerator R
    ((connecting (Triple.ordinary_triple_degreewiseShortExact R
      (Box.upperLateral_subset_fullBoundary S)) (n+1 : ℕ) (n : ℤ) hij) _)
  rw [hδ]
  apply (P202.LocalOrientation.generator_map_iff R (LinearEquiv.neg R) _).mpr
  haveI := BoxBottom.bottomInclusion_isIso R S (n : ℤ)
  exact (P202.LocalOrientation.generator_map_iff R
    (asIso ((relativeHomologyFunctor R R (n : ℤ)).map
      (P202Specs.RelativeFundamentalClass.BoxBottom.bottomInclusion S))).toLinearEquiv _).mpr hgen

/-- Every ordinary relative homology class in nonnegative degree has an actual
finite singular-chain representative in the established quotient complex. -/
lemma exists_chain_representative (P : Pair.{w}) (n : ℕ)
    (g : relativeHomology R R P (n : ℤ)) :
    ∃ (c : Chains R P.space n)
      (hc : (ordinary R R P).d (n : ℤ) ((ComplexShape.down ℤ).next (n : ℤ))
        (quotientChain R P n c) = 0),
      cycleClass (ordinary R R P) ((ComplexShape.down ℤ).next (n : ℤ)) rfl
        (quotientChain R P n c) hc = g := by
  let K := ordinary R R P
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ (n : ℤ))).mp inferInstance g
  obtain ⟨c, hc⟩ :=
    (ModuleCat.epi_iff_surjective ((projection (chainFunctor R R) P).f n)).mp inferInstance
      ((ordinaryDegreeIso R R P n).hom ((K.iCycles (n : ℤ)) z))
  have hchain : quotientChain R P n c = (K.iCycles (n : ℤ)) z := by
    apply (ModuleCat.mono_iff_injective (ordinaryDegreeIso R R P n).hom).mp inferInstance
    rw [quotientChain_coordinates]
    exact hc
  have hcycle : K.d (n : ℤ) ((ComplexShape.down ℤ).next (n : ℤ))
      (quotientChain R P n c) = 0 := by
    rw [hchain]
    exact congrArg (fun f => f z) (K.iCycles_d (n : ℤ) ((ComplexShape.down ℤ).next (n : ℤ)))
  refine ⟨c, hcycle, ?_⟩
  have hcycles : K.cyclesMk (quotientChain R P n c)
      ((ComplexShape.down ℤ).next (n : ℤ)) rfl hcycle = z := by
    apply (ModuleCat.mono_iff_injective (K.iCycles (n : ℤ))).mp inferInstance
    change ((forget₂ (ModuleCat R) Ab).map (K.iCycles (n : ℤ)))
      (K.cyclesMk (quotientChain R P n c) ((ComplexShape.down ℤ).next (n : ℤ)) rfl hcycle) = _
    rw [i_cyclesMk]
    exact hchain
  unfold cycleClass
  change ((forget₂ (ModuleCat R) Ab).map (K.homologyπ (n : ℤ))) _ = g
  rw [hcycles]
  exact hz

end PrismLift

namespace CollarClamp
open P202Specs.RelativeFundamentalClass.CollarClamp
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.LocalOrientation P202Specs.CompactOrientation
open P202Specs.RelativeFundamentalClass

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]

def radialFactor (x : E) : ℝ := (max 1 ‖x‖)⁻¹

lemma maxNorm_pos (x : E) : 0 < max 1 ‖x‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
lemma radialFactor_pos (x : E) : 0 < radialFactor x := inv_pos.mpr (maxNorm_pos x)
lemma radialFactor_le_one (x : E) : radialFactor x ≤ 1 := by
  dsimp [radialFactor]
  exact (inv_le_one₀ (maxNorm_pos x)).mpr (le_max_left _ _)
lemma radialFactor_continuous : Continuous (radialFactor : E → ℝ) :=
  (continuous_const.max continuous_norm).inv₀ (fun x => (maxNorm_pos x).ne')

lemma radialFactor_mul_norm (x : E) : radialFactor x * ‖x‖ ≤ 1 := by
  exact (inv_mul_le_iff₀ (maxNorm_pos x)).mpr (by simpa only [mul_one] using le_max_right (1:ℝ) ‖x‖)

lemma radialFactor_mul_norm_of_one_le {x : E} (hx : 1 ≤ ‖x‖) :
    radialFactor x * ‖x‖ = 1 := by
  simp only [radialFactor, max_eq_right hx]
  exact inv_mul_cancel₀ (ne_of_gt (lt_of_lt_of_le zero_lt_one hx))

lemma radialFactor_of_norm_le {x : E} (hx : ‖x‖ ≤ 1) : radialFactor x = 1 := by
  simp [radialFactor, max_eq_left hx]

def radialClamp (x : E) : Metric.closedBall (0 : E) 1 :=
  ⟨radialFactor x • x, by
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (radialFactor_pos x)]
    exact radialFactor_mul_norm x⟩

lemma radialClamp_continuous : Continuous (radialClamp : E → Metric.closedBall (0 : E) 1) :=
  (radialFactor_continuous.smul continuous_id).subtype_mk _

lemma radialClamp_fixed (x : Metric.closedBall (0 : E) 1) : radialClamp x.val = x := by
  apply Subtype.ext
  have hx : ‖x.val‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using x.property
  simp [radialClamp, radialFactor_of_norm_le hx]

lemma radialClamp_norm_of_one_le {x : E} (hx : 1 ≤ ‖x‖) :
    ‖(radialClamp x).val‖ = 1 := by
  rw [radialClamp, norm_smul, Real.norm_eq_abs, abs_of_pos (radialFactor_pos x)]
  exact radialFactor_mul_norm_of_one_le hx

def radialScale (s : unitInterval) (x : E) : ℝ :=
  (1-(s : ℝ)) * radialFactor x + s

lemma radialScale_nonneg (s : unitInterval) (x : E) : 0 ≤ radialScale s x :=
  add_nonneg (mul_nonneg (sub_nonneg.mpr s.property.2) (radialFactor_pos x).le) s.property.1

lemma radialScale_le_one (s : unitInterval) (x : E) : radialScale s x ≤ 1 := by
  have h := mul_le_mul_of_nonneg_left (radialFactor_le_one x) (sub_nonneg.mpr s.property.2)
  dsimp [radialScale]
  nlinarith

lemma radialScale_norm_le (s : unitInterval) (x : E) :
    ‖radialScale s x • x‖ ≤ ‖x‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (radialScale_nonneg s x)]
  exact mul_le_of_le_one_left (norm_nonneg x) (radialScale_le_one s x)

lemma radialScale_preserves_exterior (s : unitInterval) {x : E} (hx : 1 ≤ ‖x‖) :
    1 ≤ ‖radialScale s x • x‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (radialScale_nonneg s x)]
  have hr := radialFactor_mul_norm_of_one_le hx
  have hs := s.property.1
  dsimp [radialScale]
  nlinarith

lemma radialScale_continuous :
    Continuous (fun sx : unitInterval × E => radialScale sx.1 sx.2) := by
  exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
    (radialFactor_continuous.comp continuous_snd)).add
      (continuous_subtype_val.comp continuous_fst)

def timeClamp (t : OpenTime) : unitInterval :=
  ⟨min 1 t.val, le_min zero_le_one t.property.1, min_le_left _ _⟩

lemma timeClamp_fixed (t : unitInterval) : timeClamp (timeInclusion t) = t := by
  apply Subtype.ext
  exact min_eq_right t.property.2

lemma timeClamp_continuous : Continuous timeClamp :=
  (continuous_const.min continuous_subtype_val).subtype_mk _

def cylinderClamp : C(OpenCylinder E, ClosedPrism E) :=
  ⟨fun z => (timeClamp z.1, radialClamp z.2.val),
    (timeClamp_continuous.comp continuous_fst).prodMk
      (radialClamp_continuous.comp (continuous_subtype_val.comp continuous_snd))⟩

lemma cylinderClamp_prismInclusion (z : ClosedPrism E) :
    cylinderClamp (prismInclusion z) = z := by
  apply Prod.ext
  · exact timeClamp_fixed z.1
  · exact radialClamp_fixed z.2

def cylinderHomotopyTime (s : unitInterval) (t : OpenTime) : OpenTime :=
  ⟨(1-(s : ℝ)) * min 1 t.val + s * t.val, by
    have hs := s.property
    have ht := t.property
    have hmin0 : 0 ≤ min 1 t.val := le_min zero_le_one ht.1
    have hmin2 : min 1 t.val < 2 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    constructor
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr hs.2) hmin0) (mul_nonneg hs.1 ht.1)
    · have hs0 : 0 ≤ (s:ℝ) := hs.1
      have hs1 : (s:ℝ) ≤ 1 := hs.2
      have ht2 : (t:ℝ) < 2 := ht.2
      have hh : min 1 (t:ℝ) ≤ (t:ℝ) := min_le_right _ _
      have hmul := mul_le_mul_of_nonneg_left hh (sub_nonneg.mpr hs1)
      nlinarith⟩

def cylinderHomotopyDisk (s : unitInterval) (x : OpenDisk E) : OpenDisk E :=
  ⟨radialScale s x.val • x.val, by
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_le_of_lt (radialScale_norm_le s x.val) (by simpa only [Metric.mem_ball, dist_zero_right] using x.property)⟩

def cylinderHomotopy : ContinuousMap.Homotopy
    (prismInclusion.comp cylinderClamp : C(OpenCylinder E, OpenCylinder E))
    (ContinuousMap.id (OpenCylinder E)) where
  toFun sz := (cylinderHomotopyTime sz.1 sz.2.1, cylinderHomotopyDisk sz.1 sz.2.2)
  continuous_toFun := by
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
        (continuous_const.min (continuous_subtype_val.comp (continuous_fst.comp continuous_snd)))).add
        ((continuous_subtype_val.comp continuous_fst).mul
          (continuous_subtype_val.comp (continuous_fst.comp continuous_snd)))
    · apply Continuous.subtype_mk
      exact (radialScale_continuous.comp
        (continuous_fst.prodMk (continuous_subtype_val.comp (continuous_snd.comp continuous_snd)))).smul
        (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))
  map_zero_left z := by
    apply Prod.ext
    · apply Subtype.ext
      simp [cylinderHomotopyTime, prismInclusion, cylinderClamp, timeClamp, timeInclusion]
    · apply Subtype.ext
      simp [cylinderHomotopyDisk, radialScale, prismInclusion, cylinderClamp, radialClamp]
  map_one_left z := by
    apply Prod.ext
    · apply Subtype.ext
      simp [cylinderHomotopyTime]
    · apply Subtype.ext
      simp [cylinderHomotopyDisk, radialScale]


lemma cylinderClamp_upper {z : OpenCylinder E} (hz : z ∈ openUpper) :
    cylinderClamp z ∈ closedUpper := by
  rcases hz with ht | hx
  · left
    apply Subtype.ext
    exact min_eq_left ht
  · right
    exact radialClamp_norm_of_one_le hx

lemma cylinderClamp_full {z : OpenCylinder E} (hz : z ∈ openFull) :
    cylinderClamp z ∈ closedFull := by
  rcases hz with ht | hu
  · left
    apply Subtype.ext
    change min 1 z.1.val = 0
    rw [ht]
    exact min_eq_right zero_le_one
  · exact Or.inr (cylinderClamp_upper hu)

lemma cylinderHomotopy_preserves_upper (s : unitInterval) {z : OpenCylinder E}
    (hz : z ∈ openUpper) : cylinderHomotopy (s,z) ∈ openUpper := by
  rcases hz with ht | hx
  · left
    change 1 ≤ (1-(s:ℝ)) * min 1 z.1.val + s * z.1.val
    rw [min_eq_left ht]
    have hs0 := s.property.1
    nlinarith
  · right
    exact radialScale_preserves_exterior s hx

lemma cylinderHomotopy_preserves_full (s : unitInterval) {z : OpenCylinder E}
    (hz : z ∈ openFull) : cylinderHomotopy (s,z) ∈ openFull := by
  rcases hz with ht | hu
  · left
    change (1-(s:ℝ)) * min 1 z.1.val + s * z.1.val = 0
    simp [ht]
  · exact Or.inr (cylinderHomotopy_preserves_upper s hu)

def pairClamp (full : Bool) : openPair (E := E) full ⟶ closedPair (E := E) full :=
  ⟨TopCat.ofHom cylinderClamp, by
    cases full
    · exact fun _ hz => cylinderClamp_upper hz
    · exact fun _ hz => cylinderClamp_full hz⟩

lemma pairInclusion_pairClamp (full : Bool) :
    pairInclusion (E := E) full ≫ pairClamp full = 𝟙 _ := by
  apply PairMap.ext
  ext z
  exact cylinderClamp_prismInclusion z

def pairClampHomotopy (full : Bool) : P202Specs.PrismHomotopy.PairHomotopy
    (pairClamp (E := E) full ≫ pairInclusion full) (𝟙 _) where
  homotopy := cylinderHomotopy
  preserves s z := by
    cases full
    · exact cylinderHomotopy_preserves_upper s z.property
    · exact cylinderHomotopy_preserves_full s z.property

/-- Actual full-boundary and upper-plus-lateral pair inclusions of the smaller
closed prism in the larger open cylinder are isomorphisms on ordinary relative
homology, with the concrete geometric clamp as inverse. -/
lemma pairInclusion_isIso (R : Type u) [CommRing R] (full : Bool) (j : ℤ) :
    IsIso ((relativeHomologyFunctor R R j).map (pairInclusion (E := E) full)) := by
  let F := relativeHomologyFunctor R R j
  have hleft : F.map (pairInclusion (E := E) full) ≫ F.map (pairClamp full) = 𝟙 _ := by
    rw [← F.map_comp, pairInclusion_pairClamp, F.map_id]
  have hright : F.map (pairClamp (E := E) full) ≫ F.map (pairInclusion full) = 𝟙 _ := by
    rw [← F.map_comp]
    have hh := (P202.PrismHomotopy.relativeHomology R R (pairClampHomotopy (E := E) full) j).1
    exact hh.trans ((relativeHomologyFunctor R R j).map_id _)
  exact ⟨⟨F.map (pairClamp full), hleft, hright⟩⟩


def tripleTargetClamp :
    Triple.subspacePair (openUpper (E := E)) openFull ⟶
      Triple.subspacePair (closedUpper (E := E)) closedFull :=
  ⟨TopCat.ofHom ⟨fun z => ⟨cylinderClamp z.val, cylinderClamp_full z.property⟩,
    (cylinderClamp.continuous.comp continuous_subtype_val).subtype_mk _⟩,
    fun _ hz => cylinderClamp_upper hz⟩

lemma tripleTargetInclusion_tripleTargetClamp :
    tripleTargetInclusion (E := E) ≫ tripleTargetClamp = 𝟙 _ := by
  apply PairMap.ext
  apply ConcreteCategory.hom_ext
  intro z
  exact Subtype.ext (cylinderClamp_prismInclusion z.val)

def tripleTargetClampHomotopy : P202Specs.PrismHomotopy.PairHomotopy
    (tripleTargetClamp (E := E) ≫ tripleTargetInclusion) (𝟙 _) where
  homotopy := {
    toFun := fun sz => ⟨cylinderHomotopy (sz.1, sz.2.val),
      cylinderHomotopy_preserves_full sz.1 sz.2.property⟩
    continuous_toFun := (cylinderHomotopy.continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
    map_zero_left := fun z => Subtype.ext (cylinderHomotopy.map_zero_left z.val)
    map_one_left := fun z => Subtype.ext (cylinderHomotopy.map_one_left z.val) }
  preserves := fun s z => cylinderHomotopy_preserves_upper s z.property

lemma tripleTargetInclusion_isIso (R : Type u) [CommRing R] (j : ℤ) :
    IsIso ((relativeHomologyFunctor R R j).map (tripleTargetInclusion (E := E))) := by
  let F := relativeHomologyFunctor R R j
  have hleft : F.map (tripleTargetInclusion (E := E)) ≫ F.map tripleTargetClamp = 𝟙 _ := by
    rw [← F.map_comp, tripleTargetInclusion_tripleTargetClamp, F.map_id]
  have hright : F.map (tripleTargetClamp (E := E)) ≫ F.map tripleTargetInclusion = 𝟙 _ := by
    rw [← F.map_comp]
    have hh := (P202.PrismHomotopy.relativeHomology R R
      (tripleTargetClampHomotopy (E := E)) j).1
    exact hh.trans ((relativeHomologyFunctor R R j).map_id _)
  exact ⟨⟨F.map tripleTargetClamp, hleft, hright⟩⟩

/-- Both squares of the concrete clamp comparison are equalities of pair maps. -/
lemma tripleTargetInclusion_square :
    tripleTargetInclusion (E := E) ≫ Triple.tripleInclusion openUpper openFull =
      Triple.tripleInclusion closedUpper closedFull ≫ pairInclusion false :=
  PairMap.ext _ _ rfl

lemma pairInclusion_projection_square :
    pairInclusion (E := E) false ≫
        Triple.tripleProjection (show openUpper (E := E) ⊆ openFull from fun _ h => Or.inr h) =
      Triple.tripleProjection (show closedUpper (E := E) ⊆ closedFull from fun _ h => Or.inr h) ≫
        pairInclusion true := PairMap.ext _ _ rfl

end CollarClamp

namespace CollarLocalization
open P202Specs.RelativeFundamentalClass.CollarLocalization
variable {M N : Type v} [TopologicalSpace M] [TopologicalSpace N]
variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {ι : Type w₁} {shape : ComplexShape ι}
  (K : TopCat.{v} ⥤ HomologicalComplex C shape)
lemma tripleSequenceMap_connecting (f : C(M, N)) {A D : Set M} {E G : Set N}
    (hAD : A ⊆ D) (hEG : E ⊆ G)
    (hfA : Set.MapsTo f A E) (hfD : Set.MapsTo f D G)
    [Mono (inclusion K (boundaryPair M D))] [Mono (inclusion K (boundaryPair N G))]
    (i j : ι) (hij : shape.Rel i j) :
    P202Specs.ChainLES.connecting (Triple.triple_degreewiseShortExact K hAD) i j hij ≫
      homologyMap (relativeMap K (subspacePairMap f hfA hfD)) j =
    homologyMap (relativeMap K (ambientPairMap f hfD)) i ≫
      P202Specs.ChainLES.connecting (Triple.triple_degreewiseShortExact K hEG) i j hij :=
  (P202.ChainLES.naturality (tripleSequenceMap K f hAD hEG hfA hfD)
    (Triple.triple_degreewiseShortExact K hAD)
    (Triple.triple_degreewiseShortExact K hEG)).2.2 i j hij


end CollarLocalization

theorem prismBoundarySign : P202Specs.RelativeFundamentalClass.Expected.prismBoundarySign.{u} := by
  intro R _ D _ S n c hc hT
  exact PrismLift.prismChain_connecting S n c hc

theorem prismComparisons : P202Specs.RelativeFundamentalClass.Expected.prismComparisons.{u,v} := by
  intro R _ V _ _ j
  exact ⟨NormPrism.toOwnLocal_isIso V R j, NormPrism.toAmbientLocal_isIso V R j⟩

theorem cylinderComparisons : P202Specs.RelativeFundamentalClass.Expected.cylinderComparisons.{u,v} := by
  intro R _ E _ _ j
  exact ⟨fun b => CollarClamp.pairInclusion_isIso R b j, CollarClamp.tripleTargetInclusion_isIso R j⟩

namespace ModelGenerators
open P202Specs.ChainLES
open P202Specs.SingularChains P202Specs.RelativeSingularChains P202Specs.LocalOrientation
open P202Specs.RelativeFundamentalClass
open P202Specs.RelativeFundamentalClass.Disk P202Specs.RelativeFundamentalClass.PrismLift

def functionManifold (n : ℕ) : Manifold n (Fin n → ℝ) where
  hausdorff := inferInstance
  secondCountable := inferInstance
  atlas := {(Homeomorph.Set.univ (Fin n → ℝ)).symm.toOpenPartialHomeomorph}
  covers x := ⟨_, rfl, by simp⟩

lemma unitDisk_rankOne (R : Type u) [CommRing R] (n : ℕ) :
    Nonempty (relativeHomology R R (unitPair (Fin n → ℝ)) (n : ℤ) ≃ₗ[R] R) := by
  obtain ⟨e⟩ := (P202.LocalOrientation.localHomology R n (Fin n → ℝ)
    (functionManifold n) 0 n).1 rfl
  haveI := Disk.toLocal_isIso (Fin n → ℝ) R (n : ℤ)
  exact ⟨(asIso ((relativeHomologyFunctor R R (n : ℤ)).map (toLocal (Fin n → ℝ)))).toLinearEquiv.trans e⟩

lemma exists_bottomGenerator (R : Type u) [CommRing R] (n : ℕ) :
    ∃ (c : Chains R (TopCat.of (UnitDisk (Fin n → ℝ))) n)
      (hc : (ordinary R R (unitPair (Fin n → ℝ))).d (n : ℤ)
        ((ComplexShape.down ℤ).next (n : ℤ)) (quotientChain R (unitPair (Fin n → ℝ)) n c) = 0),
      IsGenerator (V := relativeHomology R R (unitPair (Fin n → ℝ)) (n : ℤ)) R (cycleClass (ordinary R R (unitPair (Fin n → ℝ)))
        ((ComplexShape.down ℤ).next (n : ℤ)) rfl
        (quotientChain R (unitPair (Fin n → ℝ)) n c) hc) := by
  obtain ⟨e⟩ := unitDisk_rankOne R n
  obtain ⟨g, hg⟩ := P202.LocalOrientation.exists_generator R e
  obtain ⟨c, hc, he⟩ := PrismLift.exists_chain_representative (unitPair (Fin n → ℝ)) n g
  exact ⟨c, hc, he.symm ▸ hg⟩
end ModelGenerators

namespace CollarChart
open P202Specs.RelativeFundamentalClass.CollarChart
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.LocalOrientation P202Specs.CompactOrientation
open P202Specs.RelativeFundamentalClass

variable {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {X : Type v} [TopologicalSpace X]

lemma exists_centered_openEmbedding (c : OpenPartialHomeomorph X E) (x : X) (hx : x ∈ c.source) :
    ∃ f : C(E, X), IsOpenEmbedding f ∧ f 0 = x := by
  have hopen := c.open_target
  have hcx := c.map_source hx
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen (c x) hcx
  let d := (OpenPartialHomeomorph.univBall (c x) r).trans c.symm
  have hd : d.source = Set.univ := by
    ext z
    change (z ∈ (OpenPartialHomeomorph.univBall (c x) r).source ∧
      (OpenPartialHomeomorph.univBall (c x) r) z ∈ c.symm.source) ↔ z ∈ Set.univ
    simp only [OpenPartialHomeomorph.univBall_source, Set.mem_univ, true_and, iff_true]
    apply hball
    have hz := (OpenPartialHomeomorph.univBall (c x) r).map_source
      (show z ∈ (OpenPartialHomeomorph.univBall (c x) r).source by simp)
    simpa only [OpenPartialHomeomorph.univBall_target _ hr] using hz
  have he := d.isOpenEmbedding hd
  refine ⟨⟨d, he.continuous⟩, he, ?_⟩
  change c.symm ((OpenPartialHomeomorph.univBall (c x) r) 0) = x
  rw [OpenPartialHomeomorph.univBall_apply_zero]
  exact c.left_inv hx

/-- A boundaryless atlas supplies an honest Euclidean open embedding centered
at the chosen point, with no homology or orientation data. -/
lemma manifold_centered_openEmbedding (q : ℕ) (A : Manifold q X) (x : X) :
    ∃ f : C(EuclideanSpace ℝ (Fin q), X), IsOpenEmbedding f ∧ f 0 = x := by
  obtain ⟨c, hc, hx⟩ := A.covers x
  let d := c.trans (P202.LocalOrientation.coordinateEuclideanHomeomorph q).toOpenPartialHomeomorph
  apply exists_centered_openEmbedding d x
  change x ∈ c.source ∩ c ⁻¹' Set.univ
  exact ⟨hx, Set.mem_univ _⟩


lemma timeScale_isOpenEmbedding : IsOpenEmbedding timeScale :=
  (isOpen_lt continuous_subtype_val continuous_const).isOpenEmbedding_subtypeVal.comp
    timeScaleHomeomorph.isOpenEmbedding

lemma timeScale_zero : timeScale ⟨0, by norm_num⟩ = collarZero := by
  apply Subtype.ext
  norm_num [timeScale, timeScaleHomeomorph, collarZero]

variable {M : Type v} [TopologicalSpace M] {B : Set M}

lemma cylinderMap_isOpenEmbedding (c : Collar B) (f : C(E, B)) (hf : IsOpenEmbedding f) :
    IsOpenEmbedding (cylinderMap c f) := by
  have hc : IsOpenEmbedding c.map :=
    c.isOpen_neighborhood.isOpenEmbedding_subtypeVal.comp c.homeomorph.isOpenEmbedding
  have hsp : IsOpenEmbedding (fun x : Metric.ball (0 : E) 2 => f x.val) :=
    hf.comp Metric.isOpen_ball.isOpenEmbedding_subtypeVal
  exact hc.comp ((hsp.prodMap timeScale_isOpenEmbedding).comp
    (Homeomorph.prodComm NormalizedOpenTime (Metric.ball (0 : E) 2)).isOpenEmbedding)

lemma cylinderMap_bottom (c : Collar B) (f : C(E, B)) (x : Metric.ball (0 : E) 2) :
    cylinderMap c f (⟨0, by norm_num⟩, x) = (f x.val).val := by
  change c.map (f x.val, timeScale ⟨0, by norm_num⟩) = _
  rw [timeScale_zero]
  exact c.zero_section (f x.val)

lemma cylinderMap_boundary_iff (c : Collar B) (f : C(E, B))
    (z : NormalizedOpenTime × Metric.ball (0 : E) 2) :
    cylinderMap c f z ∈ B ↔ z.1.val = 0 := by
  change c.map (f z.2.val, timeScale z.1) ∈ B ↔ _
  rw [P202.RelativeFundamentalClass.Collar.map_mem_boundary_iff]
  constructor
  · intro he
    have hh := congrArg Subtype.val he
    change z.1.val / 4 = 0 at hh
    linarith
  · intro he
    apply Subtype.ext
    change z.1.val / 4 = 0
    rw [he]
    norm_num

end CollarChart

namespace CollarChart
open P202Specs.RelativeFundamentalClass.CollarChart
open P202Specs.RelativeFundamentalClass P202Specs.RelativeFundamentalClass.Disk
open P202Specs.RelativeFundamentalClass.Box
variable {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type v} [TopologicalSpace M] {B : Set M}

lemma boxInclusion_injective : Function.Injective (boxInclusion (E := E)) := by
  intro z w h
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun p : Cylinder (E := E) => p.1.val) h
  · apply Subtype.ext
    exact congrArg (fun p : Cylinder (E := E) => p.2.val) h

lemma boxInclusion_range : Set.range (boxInclusion (E := E)) = closedParameters := by
  ext z
  constructor
  · rintro ⟨w,rfl⟩
    exact ⟨w.1.property.2,by
      change ‖w.2.val‖ ≤ 1
      simpa only [Metric.mem_closedBall,dist_zero_right] using w.2.property⟩
  · intro hz
    refine ⟨(⟨z.1.val,z.1.property.1,hz.1⟩,⟨z.2.val,?_⟩),rfl⟩
    simpa only [Metric.mem_closedBall,dist_zero_right] using hz.2

lemma openParameters_isOpen : IsOpen (openParameters (E := E)) :=
  (isOpen_lt (continuous_subtype_val.comp continuous_fst) continuous_const).inter
    (isOpen_lt (continuous_subtype_val.comp continuous_snd).norm continuous_const)

lemma openParameters_subset_closedParameters :
    openParameters (E := E) ⊆ closedParameters := fun _ h => ⟨h.1.le,h.2.le⟩

lemma boxImage_eq (c : Collar B) (f : C(E,B)) :
    boxImage c f = cylinderMap c f '' closedParameters := by
  rw [boxImage,boxMap,ContinuousMap.coe_comp,Set.range_comp,boxInclusion_range]

lemma boxImage_isCompact [ProperSpace E] (c : Collar B) (f : C(E,B)) :
    IsCompact (boxImage c f) := by
  letI : CompactSpace (UnitDisk E) := isCompact_iff_compactSpace.mp (isCompact_closedBall (0:E) 1)
  exact isCompact_range (boxMap c f).continuous

lemma boxImage_isClosed [ProperSpace E] [T2Space M] (c : Collar B) (f : C(E,B)) :
    IsClosed (boxImage c f) := (boxImage_isCompact c f).isClosed

lemma boxMap_injective (c : Collar B) (f : C(E,B)) (hf : IsOpenEmbedding f) :
    Function.Injective (boxMap c f) :=
  (cylinderMap_isOpenEmbedding c f hf).injective.comp boxInclusion_injective

lemma openParameters_image_subset_interior_boxImage (c : Collar B) (f : C(E,B))
    (hf : IsOpenEmbedding f) :
    cylinderMap c f '' openParameters ⊆ interior (boxImage c f) := by
  rw [boxImage_eq]
  exact interior_maximal (Set.image_mono openParameters_subset_closedParameters)
    ((cylinderMap_isOpenEmbedding c f hf).isOpenMap _ openParameters_isOpen)

lemma boxMap_boundary_iff (c : Collar B) (f : C(E,B)) (z : unitInterval × UnitDisk E) :
    boxMap c f z ∈ B ↔ z.1 = 0 := by
  rw [boxMap,ContinuousMap.comp_apply,cylinderMap_boundary_iff]
  change z.1.val = 0 ↔ z.1 = 0
  exact ⟨fun h => Subtype.ext h,fun h => congrArg Subtype.val h⟩

lemma boxImage_zero_interior (c : Collar B) (f : C(E,B)) (hf : IsOpenEmbedding f) :
    (f 0).val ∈ interior (boxImage c f) := by
  apply openParameters_image_subset_interior_boxImage c f hf
  refine ⟨(⟨0,by norm_num⟩,⟨0,by simp⟩),?_,?_⟩
  · constructor <;> norm_num
  · exact cylinderMap_bottom c f _

lemma closedParameters_interior : interior (closedParameters (E := E)) = openParameters := by
  have ht : interior {t : NormalizedOpenTime | t.val ≤ (1:ℝ)} =
      {t : NormalizedOpenTime | t.val < 1} := by
    let one : NormalizedOpenTime := ⟨1,by norm_num⟩
    change interior (Set.Iic one) = Set.Iio one
    exact interior_Iic
  have hs : interior {x : Metric.ball (0:E) 2 | ‖x.val‖ ≤ 1} =
      {x : Metric.ball (0:E) 2 | ‖x.val‖ < 1} := by
    have h := (Metric.isOpen_ball (x := (0:E)) (ε := 2)).isOpenMap_subtype_val.preimage_interior_eq_interior_preimage
      continuous_subtype_val (Metric.closedBall (0:E) 1)
    rw [interior_closedBall (0:E) (by norm_num)] at h
    simpa only [Set.preimage_setOf_eq,Metric.closedBall,Metric.ball,dist_zero_right] using h.symm
  change interior ({t : NormalizedOpenTime | t.val ≤ (1:ℝ)} ×ˢ
    {x : Metric.ball (0:E) 2 | ‖x.val‖ ≤ 1}) = _
  rw [interior_prod_eq,ht,hs]
  rfl

lemma cylinderMap_preimage_interior_boxImage (c : Collar B) (f : C(E,B))
    (hf : IsOpenEmbedding f) :
    cylinderMap c f ⁻¹' interior (boxImage c f) = openParameters := by
  have he := cylinderMap_isOpenEmbedding c f hf
  rw [he.isOpenMap.preimage_interior_eq_interior_preimage (cylinderMap c f).continuous]
  rw [boxImage_eq,Set.preimage_image_eq _ he.injective,closedParameters_interior]

lemma boxMap_upperLateral_not_interior (c : Collar B) (f : C(E,B)) (hf : IsOpenEmbedding f)
    (z : unitInterval × UnitDisk E) (hz : z ∈ upperLateral (unitPair E).subspace) :
    boxMap c f z ∉ interior (boxImage c f) := by
  intro hi
  have hp : boxInclusion z ∈ openParameters (E := E) := by
    rw [←cylinderMap_preimage_interior_boxImage c f hf]
    exact hi
  have ht : z.1.val < 1 := hp.1
  have hx : ‖z.2.val‖ < 1 := hp.2
  rcases hz with he | he
  · have hh : z.1.val = 1 := congrArg Subtype.val he
    linarith
  · change ‖z.2.val‖ = 1 at he
    linarith

lemma boxMap_fullBoundary (c : Collar B) (f : C(E,B)) (hf : IsOpenEmbedding f)
    (z : unitInterval × UnitDisk E) (hz : z ∈ fullBoundary (unitPair E).subspace) :
    boxMap c f z ∈ (interior (boxImage c f))ᶜ ∪ B := by
  rcases hz with h0 | hL
  · exact Or.inr ((boxMap_boundary_iff c f z).mpr h0)
  · exact Or.inl (boxMap_upperLateral_not_interior c f hf z hL)

lemma interior_boxImage_eq (c : Collar B) (f : C(E,B)) (hf : IsOpenEmbedding f) :
    interior (boxImage c f) = cylinderMap c f '' openParameters := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases interior_subset hx with ⟨z,rfl⟩
    refine ⟨boxInclusion z,?_,rfl⟩
    rw [←cylinderMap_preimage_interior_boxImage c f hf]
    exact hx
  · exact openParameters_image_subset_interior_boxImage c f hf

/-- The chosen boundary atlas and specified collar produce a genuine compact
normalized collar box centered at every boundary point. -/
theorem exists_normalized_compact_box [T2Space M] (c : Collar B) (q : ℕ)
    (A : P202Specs.LocalOrientation.Manifold q B) (y : B) :
    ∃ f : C(EuclideanSpace ℝ (Fin q),B), IsOpenEmbedding f ∧ f 0 = y ∧
      IsCompact (boxImage c f) ∧ IsClosed (boxImage c f) ∧
      y.val ∈ interior (boxImage c f) := by
  obtain ⟨f,hf,hf0⟩ := manifold_centered_openEmbedding q A y
  refine ⟨f,hf,hf0,boxImage_isCompact c f,boxImage_isClosed c f,?_⟩
  simpa only [hf0] using boxImage_zero_interior c f hf

end CollarChart

namespace BottomLocal
open P202Specs.RelativeFundamentalClass.BottomLocal
open P202Specs.SingularChains P202Specs.RelativeSingularChains P202Specs.LocalOrientation
open P202Specs.RelativeFundamentalClass
open P202Specs.RelativeFundamentalClass.Disk
open P202Specs.RelativeFundamentalClass.Box
variable (V : Type v) [NormedAddCommGroup V] [NormedSpace ℝ V]

def bottomHomeomorph : UnitDisk V ≃ₜ bottomSubset V where
  toFun d := ⟨⟨(0,d), Or.inl rfl⟩, rfl⟩
  invFun z := z.val.val.2
  left_inv _ := rfl
  right_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact z.property.symm
    · rfl
  continuous_toFun := ((continuous_const.prodMk continuous_id).subtype_mk _).subtype_mk _
  continuous_invFun := continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)

lemma center_mem_interior_bottom : (center V) ∈ interior (bottomSubset V) := by
  let U : Set (Boundary V) := {z | (z.val.1 : ℝ) < 1/2 ∧ ‖z.val.2.val‖ < 1}
  have hU : IsOpen U :=
    (isOpen_lt ((continuous_subtype_val.comp continuous_fst).comp continuous_subtype_val)
      continuous_const).inter
      (isOpen_lt (((continuous_subtype_val.comp continuous_snd).comp continuous_subtype_val).norm)
        continuous_const)
  have hUT : U ⊆ bottomSubset V := by
    intro z hz
    rcases z.property with h0 | h1 | hs
    · exact h0
    · have hh := congrArg Subtype.val h1
      dsimp [U] at hz
      rw [hh] at hz
      norm_num at hz
    · change ‖z.val.2.val‖ = 1 at hs
      exact (ne_of_lt hz.2 hs).elim
  apply interior_maximal hUT hU
  change (0 : ℝ) < 1/2 ∧ ‖(0 : V)‖ < 1
  norm_num

def bottomOwnLocalIso : localPair (UnitDisk V) (origin V) ≅
    localPair (bottomSubset V) (bottomCenter V) where
  hom := ⟨TopCat.ofHom ⟨bottomHomeomorph V, (bottomHomeomorph V).continuous⟩,
    fun x hx he => hx (congrArg (bottomHomeomorph V).symm he)⟩
  inv := ⟨TopCat.ofHom ⟨(bottomHomeomorph V).symm, (bottomHomeomorph V).symm.continuous⟩,
    fun x hx he => hx (by
      calc x = bottomHomeomorph V ((bottomHomeomorph V).symm x) :=
            ((bottomHomeomorph V).apply_symm_apply x).symm
        _ = bottomHomeomorph V (origin V) := congrArg (bottomHomeomorph V) he
        _ = bottomCenter V := rfl)⟩
  hom_inv_id := PairMap.ext _ _ (by ext z; exact (bottomHomeomorph V).symm_apply_apply z)
  inv_hom_id := PairMap.ext _ _ (by ext z; exact (bottomHomeomorph V).apply_symm_apply z)

lemma bottomLocal_factor :
    (bottomOwnLocalIso V).hom ≫
      P202Specs.RelativeFundamentalClass.SubspaceLocal.localInclusion (bottomSubset V) (bottomCenter V) =
      bottomLocalMap V := PairMap.ext _ _ rfl

lemma bottomLocalMap_isIso (R : Type u) [CommRing R] (j : ℤ) :
    IsIso ((relativeHomologyFunctor R R j).map (bottomLocalMap V)) := by
  rw [← bottomLocal_factor, Functor.map_comp]
  haveI := SubspaceLocal.localInclusion_isIso R (bottomSubset V) (bottomCenter V)
    (center_mem_interior_bottom V) j
  infer_instance

lemma diskPointMap_isIso (R : Type u) [CommRing R] (j : ℤ) :
    IsIso ((relativeHomologyFunctor R R j).map (diskPointMap V)) := by
  let L := P202Specs.RelativeFundamentalClass.SubspaceLocal.localInclusion
    (Metric.closedBall (0 : V) 1) (origin V)
  haveI : IsIso ((relativeHomologyFunctor R R j).map L) :=
    SubspaceLocal.localInclusion_isIso R _ _ (NormPrism.origin_mem_interior_disk V) j
  have hf : diskPointMap V ≫ L = toLocal V := PairMap.ext _ _ rfl
  haveI : IsIso ((relativeHomologyFunctor R R j).map (diskPointMap V) ≫
      (relativeHomologyFunctor R R j).map L) := by
    rw [← Functor.map_comp, hf]
    exact Disk.toLocal_isIso V R j
  exact IsIso.of_isIso_comp_right _ ((relativeHomologyFunctor R R j).map L)

lemma targetPointMap_bottom_square :
    P202Specs.RelativeFundamentalClass.BoxBottom.bottomInclusion (sphereSubset V) ≫
      targetPointMap V = diskPointMap V ≫ bottomLocalMap V := PairMap.ext _ _ rfl

lemma targetPointMap_isIso (R : Type u) [CommRing R] (j : ℤ) :
    IsIso ((relativeHomologyFunctor R R j).map (targetPointMap V)) := by
  let H := relativeHomologyFunctor R R j
  haveI := BoxBottom.bottomInclusion_isIso R (sphereSubset V) j
  haveI := diskPointMap_isIso V R j
  haveI := bottomLocalMap_isIso V R j
  haveI : IsIso (H.map (P202Specs.RelativeFundamentalClass.BoxBottom.bottomInclusion (sphereSubset V)) ≫
      H.map (targetPointMap V)) := by
    rw [← H.map_comp, targetPointMap_bottom_square, H.map_comp]
    infer_instance
  exact IsIso.of_isIso_comp_left
    (H.map (P202Specs.RelativeFundamentalClass.BoxBottom.bottomInclusion (sphereSubset V))) _

end BottomLocal

namespace CollarGlobal
open P202Specs.RelativeFundamentalClass.CollarGlobal
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.LocalOrientation P202Specs.CompactOrientation
open P202Specs.RelativeFundamentalClass
open P202Specs.RelativeFundamentalClass.CollarClamp

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type v} [TopologicalSpace M]

/-- The larger open-cylinder full pair is the pullback of the original localized
pair under the genuine collar chart. -/
def rangePairIso (f : C(OpenCylinder E, M)) (hf : IsOpenEmbedding f) (B : Set M)
    (hB : ∀ z, f z ∈ B ↔ z.1.val = 0) :
    openPair (E := E) true ≅ cylinderRangePair f B where
  hom := ⟨TopCat.ofHom ⟨fun z => ⟨f z, ⟨z,rfl⟩⟩,
    f.continuous.subtype_mk _⟩, by
    intro z hz
    change f z ∈ deletedOutside f ∪ B
    rcases hz with ht | hu
    · exact Or.inr ((hB z).mpr ht)
    · exact Or.inl ((preimage_deletedOutside f hf.injective z).mpr hu)⟩
  inv := ⟨TopCat.ofHom ⟨hf.isEmbedding.toHomeomorph.symm, hf.isEmbedding.toHomeomorph.symm.continuous⟩, by
    intro z hz
    let w := hf.isEmbedding.toHomeomorph.symm z
    have hw : f w = z.val := congrArg Subtype.val (hf.isEmbedding.toHomeomorph.apply_symm_apply z)
    change w ∈ openFull
    rcases hz with hzA | hzB
    · exact Or.inr ((preimage_deletedOutside f hf.injective w).mp (hw.symm ▸ hzA))
    · exact Or.inl ((hB w).mp (hw.symm ▸ hzB))⟩
  hom_inv_id := by
    apply PairMap.ext
    apply ConcreteCategory.hom_ext
    intro z
    exact hf.isEmbedding.toHomeomorph.symm_apply_apply z
  inv_hom_id := by
    apply PairMap.ext
    apply ConcreteCategory.hom_ext
    intro z
    exact hf.isEmbedding.toHomeomorph.apply_symm_apply z


lemma innerCylinder_subset_range_prismInclusion :
    innerCylinder (E := E) ⊆ Set.range (prismInclusion (E := E)) := by
  intro z hz
  refine ⟨(⟨z.1.val, z.1.property.1, hz.1.le⟩,
    ⟨z.2.val, by simpa only [Metric.mem_closedBall, dist_zero_right] using hz.2.le⟩), ?_⟩
  rfl

lemma innerImage_subset_closedCore (f : C(OpenCylinder E, M)) :
    f '' innerCylinder ⊆ closedCore f := by
  rintro x ⟨z,hz,rfl⟩
  obtain ⟨w,hw⟩ := innerCylinder_subset_range_prismInclusion hz
  exact ⟨w, congrArg f hw⟩

lemma closedCore_subset_range (f : C(OpenCylinder E, M)) : closedCore f ⊆ Set.range f := by
  rintro x ⟨z,rfl⟩
  exact ⟨prismInclusion z,rfl⟩

lemma closedCore_isCompact [ProperSpace E] (f : C(OpenCylinder E, M)) :
    IsCompact (closedCore f) := by
  letI : CompactSpace (ClosedDisk E) := isCompact_iff_compactSpace.mp (isCompact_closedBall (0:E) 1)
  exact isCompact_range (f.comp (prismInclusion (E := E))).continuous

lemma deletedOutside_isClosed (f : C(OpenCylinder E, M)) (hf : IsOpenEmbedding f) :
    IsClosed (deletedOutside f) := by
  apply IsOpen.isClosed_compl
  apply hf.isOpenMap
  exact (isOpen_lt (continuous_subtype_val.comp continuous_fst) continuous_const).inter
    (isOpen_lt ((continuous_subtype_val.comp continuous_snd).norm) continuous_const)

lemma fullPairMap_factor (f : C(OpenCylinder E, M)) (hf : IsOpenEmbedding f)
    (B : Set M) (hB : ∀ z, f z ∈ B ↔ z.1.val = 0) :
    fullPairMap f B hf.injective hB =
      (rangePairIso f hf B hB).hom ≫
      P202Specs.RelativeFundamentalClass.CollarLocalization.openPairInclusion
        (boundaryPair M (deletedOutside f ∪ B)) (Set.range f) := PairMap.ext _ _ rfl

/-- Excision compares the actual normalized larger collar-cylinder pair with
the original localized pair (M,A∪B). The controlling closed core is proved
compact from the proper normed spatial model, never assumed homological data. -/
lemma fullPairMap_isIso (R : Type u) [CommRing R] [ProperSpace E] [T2Space M]
    (f : C(OpenCylinder E, M)) (hf : IsOpenEmbedding f)
    (B : Set M) (hB : ∀ z, f z ∈ B ↔ z.1.val = 0) (j : ℕ) :
    IsIso ((relativeHomologyFunctor R R (j:ℤ)).map (fullPairMap f B hf.injective hB)) := by
  let P := boundaryPair M (deletedOutside f ∪ B)
  have hCA : (closedCore f)ᶜ ⊆ P.subspace := by
    intro x hx
    exact Or.inl (fun hz => hx (innerImage_subset_closedCore f hz))
  haveI := P202.RelativeFundamentalClass.CollarLocalization.openPairInclusion_isIso R
    P (Set.range f) (closedCore f) hf.isOpen_range
    (closedCore_isCompact f).isClosed (closedCore_subset_range f) hCA j
  rw [fullPairMap_factor f hf B hB, Functor.map_comp]
  infer_instance

/-- The top closed-prism group maps isomorphically into the original localized
relative group, using the actual geometric inclusion into M. -/
lemma closedFullPairMap_isIso (R : Type u) [CommRing R] [ProperSpace E] [T2Space M]
    (f : C(OpenCylinder E, M)) (hf : IsOpenEmbedding f)
    (B : Set M) (hB : ∀ z, f z ∈ B ↔ z.1.val = 0) (j : ℕ) :
    IsIso ((relativeHomologyFunctor R R (j:ℤ)).map
      (pairInclusion (E := E) true ≫ fullPairMap f B hf.injective hB)) := by
  haveI := CollarClamp.pairInclusion_isIso (E := E) R true (j:ℤ)
  haveI := fullPairMap_isIso R f hf B hB j
  rw [Functor.map_comp]
  infer_instance


def upperRangePairIso (f : C(OpenCylinder E, M)) (hf : IsOpenEmbedding f) :
    openPair (E := E) false ≅
      P202Specs.RelativeFundamentalClass.CollarLocalization.openPair
        (boundaryPair M (deletedOutside f)) (Set.range f) where
  hom := ⟨TopCat.ofHom ⟨fun z => ⟨f z, ⟨z,rfl⟩⟩,
    f.continuous.subtype_mk _⟩,
    fun z hz => (preimage_deletedOutside f hf.injective z).mpr hz⟩
  inv := ⟨TopCat.ofHom ⟨hf.isEmbedding.toHomeomorph.symm, hf.isEmbedding.toHomeomorph.symm.continuous⟩, by
    intro z hz
    let w := hf.isEmbedding.toHomeomorph.symm z
    have hw : f w = z.val := congrArg Subtype.val (hf.isEmbedding.toHomeomorph.apply_symm_apply z)
    exact (preimage_deletedOutside f hf.injective w).mp (hw.symm ▸ hz)⟩
  hom_inv_id := by
    apply PairMap.ext
    apply ConcreteCategory.hom_ext
    intro z
    exact hf.isEmbedding.toHomeomorph.symm_apply_apply z
  inv_hom_id := by
    apply PairMap.ext
    apply ConcreteCategory.hom_ext
    intro z
    exact hf.isEmbedding.toHomeomorph.apply_symm_apply z

lemma upperPairMap_isIso (R : Type u) [CommRing R] [ProperSpace E] [T2Space M]
    (f : C(OpenCylinder E, M)) (hf : IsOpenEmbedding f) (j : ℕ) :
    IsIso ((relativeHomologyFunctor R R (j:ℤ)).map (upperPairMap f hf.injective)) := by
  let P := boundaryPair M (deletedOutside f)
  have hCA : (closedCore f)ᶜ ⊆ P.subspace := by
    intro x hx hz
    exact hx (innerImage_subset_closedCore f hz)
  haveI := P202.RelativeFundamentalClass.CollarLocalization.openPairInclusion_isIso R
    P (Set.range f) (closedCore f) hf.isOpen_range
    (closedCore_isCompact f).isClosed (closedCore_subset_range f) hCA j
  have he : upperPairMap f hf.injective = (upperRangePairIso f hf).hom ≫
      P202Specs.RelativeFundamentalClass.CollarLocalization.openPairInclusion P (Set.range f) :=
    PairMap.ext _ _ rfl
  rw [he, Functor.map_comp]
  infer_instance

lemma closedUpperPairMap_isIso (R : Type u) [CommRing R] [ProperSpace E] [T2Space M]
    (f : C(OpenCylinder E, M)) (hf : IsOpenEmbedding f) (j : ℕ) :
    IsIso ((relativeHomologyFunctor R R (j:ℤ)).map
      (pairInclusion (E := E) false ≫ upperPairMap f hf.injective)) := by
  haveI := CollarClamp.pairInclusion_isIso (E := E) R false (j:ℤ)
  haveI := upperPairMap_isIso R f hf j
  rw [Functor.map_comp]
  infer_instance

lemma deletedOutside_relative_isZero (R : Type u) [CommRing R] [ProperSpace E] [T2Space M]
    (f : C(OpenCylinder E, M)) (hf : IsOpenEmbedding f) (j : ℕ) :
    IsZero (relativeHomology R R (boundaryPair M (deletedOutside f)) (j:ℤ)) := by
  haveI := closedUpperPairMap_isIso R f hf j
  exact (Box.upperLateral_relative_isZero R (rim (E := E)) (j:ℤ)).of_iso
    (asIso ((relativeHomologyFunctor R R (j:ℤ)).map
      (pairInclusion (E := E) false ≫ upperPairMap f hf.injective))).symm

/-- Both actual maps making the morphism of local collar triples. -/
def openTripleMap (R : Type u) [CommRing R]
    (f : C(OpenCylinder E, M)) (hf : Function.Injective f) (B : Set M)
    (hB : ∀ z, f z ∈ B ↔ z.1.val = 0) :=
  P202Specs.RelativeFundamentalClass.CollarLocalization.tripleSequenceMap (ordinaryFunctor R R) f
    (show openUpper (E := E) ⊆ openFull from fun _ h => Or.inr h)
    (Set.subset_union_left : deletedOutside f ⊆ deletedOutside f ∪ B)
    (upperPairMap f hf).mapsTo (fullPairMap f B hf hB).mapsTo


lemma closedTriple_connecting (R : Type u) [CommRing R]
    (f : C(OpenCylinder E, M)) (hf : Function.Injective f)
    (B : Set M) (hB : ∀ z, f z ∈ B ↔ z.1.val = 0)
    (i j : ℤ) (hij : (ComplexShape.down ℤ).Rel i j) :
    P202Specs.ChainLES.connecting
      (Triple.ordinary_triple_degreewiseShortExact R
        (show closedUpper (E := E) ⊆ closedFull from fun _ h => Or.inr h)) i j hij ≫
      ((relativeHomologyFunctor R R j).map (closedTargetMap f hf B hB)) =
    ((relativeHomologyFunctor R R i).map
      (pairInclusion (E := E) true ≫ fullPairMap f B hf hB)) ≫
      P202Specs.ChainLES.connecting
        (Triple.ordinary_triple_degreewiseShortExact R
          (Set.subset_union_left : deletedOutside f ⊆ deletedOutside f ∪ B)) i j hij := by
  have h := P202.RelativeFundamentalClass.CollarLocalization.tripleSequenceMap_connecting
    (ordinaryFunctor R R) (f.comp (prismInclusion (E := E)))
    (show closedUpper (E := E) ⊆ closedFull from fun _ h => Or.inr h)
    (Set.subset_union_left : deletedOutside f ⊆ deletedOutside f ∪ B)
    (pairInclusion (E := E) false ≫ upperPairMap f hf).mapsTo
    (pairInclusion (E := E) true ≫ fullPairMap f B hf hB).mapsTo i j hij
  have he : P202Specs.RelativeFundamentalClass.CollarLocalization.ambientPairMap
      (f.comp (prismInclusion (E := E)))
      (pairInclusion (E := E) true ≫ fullPairMap f B hf hB).mapsTo =
      pairInclusion (E := E) true ≫ fullPairMap f B hf hB := PairMap.ext _ _ rfl
  rw [he] at h
  exact h

lemma ambientConnecting_isIso (R : Type u) [CommRing R] [ProperSpace E] [T2Space M]
    (f : C(OpenCylinder E, M)) (hf : IsOpenEmbedding f) (B : Set M) (q : ℕ) :
    IsIso (P202Specs.ChainLES.connecting
      (Triple.ordinary_triple_degreewiseShortExact R
        (Set.subset_union_left : deletedOutside f ⊆ deletedOutside f ∪ B))
      ((q+1:ℕ):ℤ) (q:ℤ) (by simp)) := by
  exact Triple.triple_connecting_isIso (ordinaryFunctor R R) Set.subset_union_left
    ((q+1:ℕ):ℤ) (q:ℤ) (by simp)
    (deletedOutside_relative_isZero R f hf (q+1)) (deletedOutside_relative_isZero R f hf q)

/-- The localized triple target is identified by the actual closed-prism
inclusion, obtained from the two genuine connecting isomorphisms and naturality. -/
lemma closedTargetMap_isIso (R : Type u) [CommRing R] [ProperSpace E] [T2Space M]
    (f : C(OpenCylinder E, M)) (hf : IsOpenEmbedding f)
    (B : Set M) (hB : ∀ z, f z ∈ B ↔ z.1.val = 0) (q : ℕ) :
    IsIso ((relativeHomologyFunctor R R (q:ℤ)).map (closedTargetMap f hf.injective B hB)) := by
  let δ := P202Specs.ChainLES.connecting
    (Triple.ordinary_triple_degreewiseShortExact R
      (show closedUpper (E := E) ⊆ closedFull from fun _ h => Or.inr h))
    ((q+1:ℕ):ℤ) (q:ℤ) (by simp)
  haveI : IsIso δ := Triple.triple_connecting_isIso (ordinaryFunctor R R)
    (show closedUpper (E := E) ⊆ closedFull from fun _ h => Or.inr h)
    ((q+1:ℕ):ℤ) (q:ℤ) (by simp)
    (Box.upperLateral_relative_isZero R (rim (E := E)) ((q+1:ℕ):ℤ))
    (Box.upperLateral_relative_isZero R (rim (E := E)) (q:ℤ))
  haveI := ambientConnecting_isIso R f hf B q
  haveI := closedFullPairMap_isIso R f hf B hB (q+1)
  haveI : IsIso (δ ≫ (relativeHomologyFunctor R R (q:ℤ)).map (closedTargetMap f hf.injective B hB)) := by
    change IsIso (P202Specs.ChainLES.connecting _ _ _ _ ≫ _)
    rw [closedTriple_connecting R f hf.injective B hB]
    infer_instance
  exact IsIso.of_isIso_comp_left δ _

end CollarGlobal

namespace EmbeddingLocal
open P202Specs.RelativeFundamentalClass.EmbeddingLocal
open P202Specs.SingularChains P202Specs.RelativeSingularChains P202Specs.LocalOrientation
open P202Specs.RelativeFundamentalClass
variable {X Y Z : Type v} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- A homeomorphism gives its actual local-pair isomorphism. -/
def homeomorphLocalIso (e : X ≃ₜ Y) (x : X) : localPair X x ≅ localPair Y (e x) where
  hom := localMap ⟨e,e.continuous⟩ e.injective x
  inv := ⟨TopCat.ofHom ⟨e.symm,e.symm.continuous⟩, by
    intro y hy he
    apply hy
    calc y = e (e.symm y) := (e.apply_symm_apply y).symm
      _ = e x := congrArg e he⟩
  hom_inv_id := PairMap.ext _ _ (by ext z; exact e.symm_apply_apply z)
  inv_hom_id := PairMap.ext _ _ (by ext z; exact e.apply_symm_apply z)

lemma localMap_range_factor (f : C(X,Y)) (hf : IsEmbedding f) (x : X) :
    (homeomorphLocalIso hf.toHomeomorph x).hom ≫
      P202Specs.RelativeFundamentalClass.SubspaceLocal.localInclusion
        (Set.range f) (hf.toHomeomorph x) = localMap f hf.injective x :=
  PairMap.ext _ _ rfl

/-- An embedding induces an isomorphism on local homology wherever its range
contains a neighborhood of the image point. -/
lemma localMap_isIso [T2Space Y] (R : Type u) [CommRing R]
    (f : C(X,Y)) (hf : IsEmbedding f) (x : X)
    (hx : f x ∈ interior (Set.range f)) (j : ℤ) :
    IsIso ((relativeHomologyFunctor R R j).map (localMap f hf.injective x)) := by
  rw [← localMap_range_factor f hf x, Functor.map_comp]
  haveI := SubspaceLocal.localInclusion_isIso R (Set.range f) (hf.toHomeomorph x) hx j
  infer_instance

lemma localMap_openEmbedding_isIso [T2Space Y] (R : Type u) [CommRing R]
    (f : C(X,Y)) (hf : IsOpenEmbedding f) (x : X) (j : ℤ) :
    IsIso ((relativeHomologyFunctor R R j).map (localMap f hf.injective x)) := by
  apply localMap_isIso R f hf.isEmbedding x _ j
  rw [hf.isOpen_range.interior_eq]
  exact Set.mem_range_self x

lemma localMap_comp (f : C(X,Y)) (g : C(Y,Z))
    (hf : Function.Injective f) (hg : Function.Injective g) (x : X) :
    localMap f hf x ≫ localMap g hg (f x) =
      localMap (g.comp f) (hg.comp hf) x := PairMap.ext _ _ rfl

end EmbeddingLocal

namespace CollarClampLocal
open P202Specs.RelativeFundamentalClass.EmbeddingLocal
open P202Specs.SingularChains P202Specs.RelativeSingularChains P202Specs.LocalOrientation
open P202Specs.RelativeFundamentalClass
open P202Specs.RelativeFundamentalClass.CollarClamp
open P202.RelativeFundamentalClass.CollarClamp
variable (V : Type v) [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma prismInclusion_isEmbedding : IsEmbedding (prismInclusion (E := V)) :=
  Topology.IsEmbedding.of_leftInverse (cylinderClamp_prismInclusion (E := V))
    (cylinderClamp (E := V)).continuous (prismInclusion (E := V)).continuous

lemma prismCenter_mem_interior_range :
    prismInclusion (NormPrism.center V) ∈ interior (Set.range (prismInclusion (E := V))) := by
  change P202Specs.RelativeFundamentalClass.CollarChart.boxInclusion
    (NormPrism.center V) ∈ interior (Set.range
      (P202Specs.RelativeFundamentalClass.CollarChart.boxInclusion (E := V)))
  rw [CollarChart.boxInclusion_range]
  apply interior_maximal CollarChart.openParameters_subset_closedParameters
    CollarChart.openParameters_isOpen
  change (1/2 : ℝ) < 1 ∧ ‖(0 : V)‖ < 1
  norm_num

def prismLocalMap : localPair (ClosedPrism V) (NormPrism.center V) ⟶
    localPair (OpenCylinder V) (prismInclusion (NormPrism.center V)) :=
  P202Specs.RelativeFundamentalClass.EmbeddingLocal.localMap (prismInclusion (E := V)) (prismInclusion_isEmbedding V).injective
    (NormPrism.center V)

lemma prismLocalMap_isIso (R : Type u) [CommRing R] (j : ℤ) :
    IsIso ((relativeHomologyFunctor R R j).map (prismLocalMap V)) :=
  EmbeddingLocal.localMap_isIso R (prismInclusion (E := V)) (prismInclusion_isEmbedding V)
    (NormPrism.center V) (prismCenter_mem_interior_range V) j

variable {M : Type v} [TopologicalSpace M] [T2Space M]

/-- The actual closed-prism-to-manifold local map through any open cylinder chart. -/
def cylinderPrismLocalMap (f : C(OpenCylinder V,M)) (hf : IsOpenEmbedding f) :
    localPair (ClosedPrism V) (NormPrism.center V) ⟶
      localPair M (f (prismInclusion (NormPrism.center V))) :=
  P202Specs.RelativeFundamentalClass.EmbeddingLocal.localMap (f.comp (prismInclusion (E := V)))
    (hf.injective.comp (prismInclusion_isEmbedding V).injective) (NormPrism.center V)

lemma cylinderPrismLocalMap_factor (f : C(OpenCylinder V,M)) (hf : IsOpenEmbedding f) :
    prismLocalMap V ≫ P202Specs.RelativeFundamentalClass.EmbeddingLocal.localMap f hf.injective
      (prismInclusion (NormPrism.center V)) = cylinderPrismLocalMap V f hf :=
  PairMap.ext _ _ rfl

lemma cylinderPrismLocalMap_isIso (R : Type u) [CommRing R]
    (f : C(OpenCylinder V,M)) (hf : IsOpenEmbedding f) (j : ℤ) :
    IsIso ((relativeHomologyFunctor R R j).map (cylinderPrismLocalMap V f hf)) := by
  rw [← cylinderPrismLocalMap_factor, Functor.map_comp]
  haveI := prismLocalMap_isIso V R j
  haveI := EmbeddingLocal.localMap_openEmbedding_isIso R f hf
    (prismInclusion (NormPrism.center V)) j
  infer_instance

end CollarClampLocal

namespace CollarGlobal
open P202Specs.RelativeFundamentalClass.CollarGlobal
open P202Specs.RelativeFundamentalClass.CollarClamp
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type v} [TopologicalSpace M]
/-- The actual original boundaryHomSucc is the model connecting image at each
boundary point, once the chosen closed-prism class is identified with the
localized original class. No generator or sign identity is assumed. -/
lemma originalBoundary_local_model_formula (R : Type u) [CommRing R]
    (f : C(OpenCylinder E, M)) (hf : Function.Injective f)
    (B : Set M) (hB : ∀ z, f z ∈ B ↔ z.1.val = 0)
    (y : B) (hy : y.val ∉ deletedOutside f)
    (h : P202Specs.ChainLES.DegreewiseShortExact
      (sequence (ordinaryFunctor R R) (boundaryPair M B))) (q : ℕ)
    (g : relativeHomology R R (boundaryPair M B) ((q+1:ℕ):ℤ))
    (a : relativeHomology R R (closedPair (E := E) true) ((q+1:ℕ):ℤ))
    (ha : ((relativeHomologyFunctor R R ((q+1:ℕ):ℤ)).map
        (pairInclusion (E := E) true ≫ fullPairMap f B hf hB)) a =
      ((relativeHomologyFunctor R R ((q+1:ℕ):ℤ)).map
        (Triple.tripleProjection (Set.subset_union_right : B ⊆ deletedOutside f ∪ B))) g) :
    ((relativeHomologyFunctor R R (q:ℤ)).map
      (P202Specs.RelativeFundamentalClass.CollarLocalization.unionBoundaryLocalInclusion (deletedOutside f) B y))
        (connectingLocalValues R B h q g y) =
    ((relativeHomologyFunctor R R (q:ℤ)).map
      (P202Specs.RelativeFundamentalClass.CollarLocalization.triplePointMap (deletedOutside f) B y hy))
      (((relativeHomologyFunctor R R (q:ℤ)).map (closedTargetMap f hf B hB))
        (P202Specs.ChainLES.connecting
          (Triple.ordinary_triple_degreewiseShortExact R
            (show closedUpper (E := E) ⊆ closedFull from fun _ h => Or.inr h))
          ((q+1:ℕ):ℤ) (q:ℤ) (by simp) a)) := by
  rw [P202.RelativeFundamentalClass.CollarLocalization.boundaryHomSucc_local_formula
    R (deletedOutside f) B y hy h q g]
  rw [← ha]
  have hc := congrArg (fun z => z a)
    (closedTriple_connecting R f hf B hB ((q+1:ℕ):ℤ) (q:ℤ) (by simp))
  exact congrArg (fun z => ((relativeHomologyFunctor R R (q:ℤ)).map
    (P202Specs.RelativeFundamentalClass.CollarLocalization.triplePointMap (deletedOutside f) B y hy)) z) hc.symm


end CollarGlobal

namespace CollarBoundaryLocal
open P202Specs.SingularChains P202Specs.RelativeSingularChains P202Specs.LocalOrientation
open P202Specs.RelativeFundamentalClass
open P202Specs.RelativeFundamentalClass.Disk
open P202Specs.RelativeFundamentalClass.CollarChart
open P202Specs.RelativeFundamentalClass.CollarGlobal
open P202Specs.RelativeFundamentalClass.CollarLocalization
variable {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {M : Type v} [TopologicalSpace M] {B : Set M}

lemma bottomCenter_not_deleted (c : Collar B) (fsp : C(V,B)) :
    (fsp 0).val ∉ deletedOutside (cylinderMap c fsp) := by
  intro hA
  apply hA
  refine ⟨(⟨0,by norm_num⟩,⟨0,by simp⟩),?_,?_⟩
  · change (0:ℝ) < 1 ∧ ‖(0:V)‖ < 1
    norm_num
  · exact CollarChart.cylinderMap_bottom c fsp _

/-- The actual localized triple-target map into the boundary local group. -/
def closedTargetToLocal (c : Collar B) (fsp : C(V,B)) (hfsp : IsOpenEmbedding fsp) :
    P202Specs.RelativeFundamentalClass.BoxBottom.boundaryPair (unitPair V).subspace ⟶
      localPair ↥(deletedOutside (cylinderMap c fsp) ∪ B)
        ⟨(fsp 0).val,Or.inr (fsp 0).property⟩ :=
  closedTargetMap (cylinderMap c fsp)
    (CollarChart.cylinderMap_isOpenEmbedding c fsp hfsp).injective B
    (CollarChart.cylinderMap_boundary_iff c fsp) ≫
  triplePointMap (deletedOutside (cylinderMap c fsp)) B (fsp 0)
    (bottomCenter_not_deleted c fsp)

/-- On the bottom disk this is precisely disk localization, the boundary chart
and the canonical inclusion into the localized union. -/
lemma closedTargetToLocal_bottom_square (c : Collar B) (fsp : C(V,B))
    (hfsp : IsOpenEmbedding fsp) :
    P202Specs.RelativeFundamentalClass.BoxBottom.bottomInclusion (unitPair V).subspace ≫
      closedTargetToLocal c fsp hfsp =
    toLocal V ≫ P202Specs.RelativeFundamentalClass.EmbeddingLocal.localMap fsp hfsp.injective 0 ≫
      unionBoundaryLocalInclusion (deletedOutside (cylinderMap c fsp)) B (fsp 0) := by
  apply PairMap.ext
  ext z
  apply Subtype.ext
  change cylinderMap c fsp
    (P202Specs.RelativeFundamentalClass.CollarClamp.prismInclusion (0,z)) = (fsp z.val).val
  exact CollarChart.cylinderMap_bottom c fsp _

/-- The actual composite from the model triple target to boundary local homology
is an isomorphism. It has no sign or generator premise. -/
lemma closedTargetToLocal_isIso [T2Space M] (R : Type u) [CommRing R]
    (c : Collar B) (fsp : C(V,B)) (hfsp : IsOpenEmbedding fsp) (q : ℕ) :
    IsIso ((relativeHomologyFunctor R R (q:ℤ)).map (closedTargetToLocal c fsp hfsp)) := by
  let H := relativeHomologyFunctor R R (q:ℤ)
  haveI := BoxBottom.bottomInclusion_isIso R (unitPair V).subspace (q:ℤ)
  haveI := Disk.toLocal_isIso V R (q:ℤ)
  haveI := EmbeddingLocal.localMap_openEmbedding_isIso R fsp hfsp 0 (q:ℤ)
  haveI := CollarLocalization.unionBoundaryLocalInclusion_isIso R
    (deletedOutside (cylinderMap c fsp)) B
    (CollarGlobal.deletedOutside_isClosed (cylinderMap c fsp)
      (CollarChart.cylinderMap_isOpenEmbedding c fsp hfsp))
    (fsp 0) (bottomCenter_not_deleted c fsp) q
  haveI : IsIso (H.map (P202Specs.RelativeFundamentalClass.BoxBottom.bottomInclusion
        (unitPair V).subspace) ≫ H.map (closedTargetToLocal c fsp hfsp)) := by
    rw [← H.map_comp, closedTargetToLocal_bottom_square, H.map_comp, H.map_comp]
    infer_instance
  exact IsIso.of_isIso_comp_left
    (H.map (P202Specs.RelativeFundamentalClass.BoxBottom.bottomInclusion (unitPair V).subspace)) _

end CollarBoundaryLocal

namespace PrismLiftGeneric
open P202Specs.RelativeFundamentalClass.PrismLiftGeneric
open P202Specs.ChainLES P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.RelativeFundamentalClass P202Specs.RelativeFundamentalClass.Triple
open P202Specs.AlexanderWhitney P202Specs.ShuffleModel
open P202Specs.RelativeFundamentalClass.PrismLift
open P202.RelativeFundamentalClass.PrismLift
variable {R : Type u} [CommRing R]

lemma positiveInterval_upper (x : StdSimplex 0) :
    simplexEquiv (TopCat.of LiftedInterval.{v}) 0 (face 0 P202Specs.RelativeFundamentalClass.PrismLiftGeneric.positiveInterval) x = ULift.up 1 := by
  rw [P202.SingularChains.simplexEquiv_face]
  apply ULift.ext; apply Subtype.ext
  change ((faceInclusion 0 x).weights 1) = 1
  rw [P202.ShuffleBoundary.simplex_zero_unique x,P202.SingularChains.faceInclusion_vertex]
  simp
lemma positiveInterval_lower (x : StdSimplex 0) :
    simplexEquiv (TopCat.of LiftedInterval.{v}) 0 (face 1 P202Specs.RelativeFundamentalClass.PrismLiftGeneric.positiveInterval) x = ULift.up 0 := by
  rw [P202.SingularChains.simplexEquiv_face]
  apply ULift.ext; apply Subtype.ext
  change ((faceInclusion 1 x).weights 1) = 0
  rw [P202.ShuffleBoundary.simplex_zero_unique x,P202.SingularChains.faceInclusion_vertex]
  simp

variable {D : Type v} [TopologicalSpace D]

lemma down_lowerShuffle_eq_bottomChain (S : Set D) (n : ℕ) (c : Chains R (TopCat.of D) n) :
    (chainMap R R downProduct).f n
      (shuffle R (TopCat.of LiftedInterval.{v}) (TopCat.of D) n
        (Pi.single (⟨(0,n),by omega⟩ : Diagonal n)
          (Finsupp.single (face 1 P202Specs.RelativeFundamentalClass.PrismLiftGeneric.positiveInterval) 1 ⊗ₜ[R] c))) =
    (chainMap R R (tripleInclusion (Box.upperLateral S) (Box.fullBoundary S)).map).f n
      (P202Specs.RelativeFundamentalClass.PrismLiftGeneric.bottomChain R S n c) := by
  have h₁ := LinearMap.congr_fun
    (P202.ShuffleBoundary.component_zero_left_map R (face 1 P202Specs.RelativeFundamentalClass.PrismLiftGeneric.positiveInterval) n) c
  have hm : P202.ShuffleBoundary.insertLeft (Y := TopCat.of D) (face 1 P202Specs.RelativeFundamentalClass.PrismLiftGeneric.positiveInterval) ≫ downProduct =
      (P202Specs.RelativeFundamentalClass.BoxBottom.bottomInclusion S).map ≫
        (tripleInclusion (Box.upperLateral S) (Box.fullBoundary S)).map := by
    apply ConcreteCategory.hom_ext
    intro x
    change ((simplexEquiv (TopCat.of LiftedInterval.{v}) 0 (face 1 P202Specs.RelativeFundamentalClass.PrismLiftGeneric.positiveInterval)
      (Convexity.StdSimplex.single 0)).down,x) = (0,x)
    rw [positiveInterval_lower]
  have h₁' : shuffle R (TopCat.of LiftedInterval.{v}) (TopCat.of D) n
      (Pi.single (⟨(0,n),by omega⟩ : Diagonal n)
        (Finsupp.single (face 1 P202Specs.RelativeFundamentalClass.PrismLiftGeneric.positiveInterval) 1 ⊗ₜ[R] c)) =
      (chainMap R R (P202.ShuffleBoundary.insertLeft (Y := TopCat.of D) (face 1 P202Specs.RelativeFundamentalClass.PrismLiftGeneric.positiveInterval))).f n c := by
    rw [P202.ShuffleBoundary.shuffle_single]
    exact h₁
  have h₂ := congrArg (fun f => f c)
    (HomologicalComplex.congr_hom ((chainFunctor R R).map_comp
      (P202.ShuffleBoundary.insertLeft (Y := TopCat.of D) (face 1 P202Specs.RelativeFundamentalClass.PrismLiftGeneric.positiveInterval)) downProduct) n)
  change (chainMap R R (_ ≫ _)).f n c =
    (chainMap R R downProduct).f n
      ((chainMap R R (P202.ShuffleBoundary.insertLeft (Y := TopCat.of D) (face 1 P202Specs.RelativeFundamentalClass.PrismLiftGeneric.positiveInterval))).f n c) at h₂
  refine (congrArg (fun z => (chainMap R R downProduct).f n z) h₁').trans ?_
  rw [←h₂,hm]
  exact congrArg (fun f => f c)
    (HomologicalComplex.congr_hom ((chainFunctor R R).map_comp
      (P202Specs.RelativeFundamentalClass.BoxBottom.bottomInclusion S).map
      (tripleInclusion (Box.upperLateral S) (Box.fullBoundary S)).map) n)

lemma cast_shuffle_single (X Y : TopCat.{v}) {p q n m : ℕ}
    (hpq : p+q=n) (hnm : n=m) (z : Chains R X p ⊗[R] Chains R Y q) :
    castChains R hnm (shuffle R X Y n (Pi.single (⟨(p,q),hpq⟩ : Diagonal n) z)) =
      shuffle R X Y m (Pi.single (⟨(p,q),hpq.trans hnm⟩ : Diagonal m) z) := by
  rw [P202.ShuffleBoundary.shuffle_single,P202.ShuffleBoundary.shuffle_single,
    P202.ShuffleBoundary.castChains_comp_castChains]

lemma rawPrismChain_boundary_quotient (S : Set D) (n : ℕ) (c : Chains R (TopCat.of D) n)
    (hc : ∀ q (hn : n = q+1), ∀ τ ∈ (boundary R R (TopCat.of D) q (hn ▸ c)).support,
      InSubspace (P202Specs.RelativeFundamentalClass.BoxBottom.bottomPair S) q τ) :
    (projection (chainFunctor R R) (liftedPair S)).f n
      (boundary R R (liftedPair S).space n (rawPrismChain R n c)) =
    -((projection (chainFunctor R R) (liftedPair S)).f n
      (shuffle R (TopCat.of LiftedInterval.{v}) (TopCat.of D) n
        (Pi.single (⟨(0,n),by omega⟩ : Diagonal n)
          (Finsupp.single (face 1 P202Specs.RelativeFundamentalClass.PrismLiftGeneric.positiveInterval) 1 ⊗ₜ[R] c)))) := by
  cases n with
  | zero =>
    apply BoxBoundary.lowerFace_quotient_zero R (TopCat.of LiftedInterval.{v}) (TopCat.of D)
      (liftedUpper S) P202Specs.RelativeFundamentalClass.PrismLiftGeneric.positiveInterval c
    intro τ hτ x y
    exact Or.inl (by change (simplexEquiv (TopCat.of LiftedInterval.{v}) 0 (face 0 P202Specs.RelativeFundamentalClass.PrismLiftGeneric.positiveInterval.{v}) x).down = 1; rw [positiveInterval_upper.{v}])
  | succ q =>
    have h := BoxBoundary.lowerFace_quotient R (TopCat.of LiftedInterval.{v}) (TopCat.of D)
      (liftedUpper S) q P202Specs.RelativeFundamentalClass.PrismLiftGeneric.positiveInterval c
      (fun τ hτ x y => Or.inl (by
        change (simplexEquiv (TopCat.of LiftedInterval.{v}) 0 (face 0 P202Specs.RelativeFundamentalClass.PrismLiftGeneric.positiveInterval.{v}) x).down = 1
        rw [positiveInterval_upper.{v}]))
      (fun τ hτ x y => Or.inr (hc q rfl τ hτ y))
    have h' := PrismLift.negativeBoundary_cast (liftedPair S)
      (by omega : 0+q+1 = q+1) _ _ h
    dsimp only [liftedPair] at h'
    simp only [cast_shuffle_single] at h'
    exact h' 

lemma projection_down (S : Set D) (n : ℕ) (c : Chains R (liftedPair S).space n) :
    (projection (chainFunctor R R) (boundaryPair (unitInterval × D) (Box.upperLateral S))).f n
      ((chainMap R R downProduct).f n c) =
    (relativeMap (chainFunctor R R) (downPairMap S)).f n
      ((projection (chainFunctor R R) (liftedPair S)).f n c) :=
  (congrArg (fun f => f c)
    (HomologicalComplex.congr_hom (projection_map (chainFunctor R R) (downPairMap S)) n)).symm

lemma prismChain_boundary_quotient (S : Set D) (n : ℕ) (c : Chains R (TopCat.of D) n)
    (hc : ∀ q (hn : n = q+1), ∀ τ ∈ (boundary R R (TopCat.of D) q (hn ▸ c)).support,
      InSubspace (P202Specs.RelativeFundamentalClass.BoxBottom.bottomPair S) q τ) :
    (projection (chainFunctor R R) (boundaryPair (unitInterval × D) (Box.upperLateral S))).f n
      (boundary R R (TopCat.of (unitInterval × D)) n (P202Specs.RelativeFundamentalClass.PrismLiftGeneric.prismChain R n c)) =
    -((projection (chainFunctor R R) (boundaryPair (unitInterval × D) (Box.upperLateral S))).f n
      ((chainMap R R (tripleInclusion (Box.upperLateral S) (Box.fullBoundary S)).map).f n
        (P202Specs.RelativeFundamentalClass.PrismLiftGeneric.bottomChain R S n c))) := by
  have hcomm := congrArg (fun f => f (rawPrismChain R n c))
    ((chainMap R R (downProduct (D := D))).comm (n+1) n)
  change boundary R R (TopCat.of (unitInterval × D)) n (P202Specs.RelativeFundamentalClass.PrismLiftGeneric.prismChain R n c) =
    (chainMap R R downProduct).f n (boundary R R (liftedPair S).space n (rawPrismChain R n c)) at hcomm
  rw [hcomm,projection_down,rawPrismChain_boundary_quotient S n c hc,map_neg,←projection_down,
    down_lowerShuffle_eq_bottomChain]

lemma prismChain_boundary_quotient_of_cycle {D : Type v} [TopologicalSpace D]
    (S : Set D) (n : ℕ) (c : Chains R (TopCat.of D) n)
    (hc : (ordinary R R (P202Specs.RelativeFundamentalClass.BoxBottom.bottomPair S)).d
      (n : ℤ) ((ComplexShape.down ℤ).next (n : ℤ))
      (quotientChain R (P202Specs.RelativeFundamentalClass.BoxBottom.bottomPair S) n c) = 0) :
    (projection (chainFunctor R R) (boundaryPair (unitInterval × D) (Box.upperLateral S))).f n
      (boundary R R (TopCat.of (unitInterval × D)) n (P202Specs.RelativeFundamentalClass.PrismLiftGeneric.prismChain R n c)) =
    -((projection (chainFunctor R R) (boundaryPair (unitInterval × D) (Box.upperLateral S))).f n
      ((chainMap R R (tripleInclusion (Box.upperLateral S) (Box.fullBoundary S)).map).f n
        (P202Specs.RelativeFundamentalClass.PrismLiftGeneric.bottomChain R S n c))) := by
  apply prismChain_boundary_quotient S n c
  intro q hn
  subst n
  have hnext : (ComplexShape.down ℤ).next ((q+1 : ℕ) : ℤ) = (q : ℤ) :=
    (ComplexShape.down ℤ).next_eq' (by simp)
  rw [hnext, quotientChain_boundary] at hc
  have hzero := congrArg
    ((ordinaryDegreeIso R R (P202Specs.RelativeFundamentalClass.BoxBottom.bottomPair S) q).hom) hc
  rw [quotientChain_coordinates, map_zero] at hzero
  exact (projection_eq_zero_iff_support _ q _).mp hzero

/-- The model lower-face sign is the actual ordinary connecting formula.
The only premise is that the chosen disk chain represents a relative cycle. -/
lemma prismChain_connecting {D : Type v} [TopologicalSpace D]
    (S : Set D) (n : ℕ) (c : Chains R (TopCat.of D) n)
    (hc : (ordinary R R (P202Specs.RelativeFundamentalClass.BoxBottom.bottomPair S)).d
      (n : ℤ) ((ComplexShape.down ℤ).next (n : ℤ))
      (quotientChain R (P202Specs.RelativeFundamentalClass.BoxBottom.bottomPair S) n c) = 0) :
    ∃ hp : (ordinary R R (boundaryPair (unitInterval × D) (Box.fullBoundary S))).d
      (n+1 : ℕ) n
      (quotientChain R (boundaryPair (unitInterval × D) (Box.fullBoundary S)) (n+1)
        (P202Specs.RelativeFundamentalClass.PrismLiftGeneric.prismChain R n c)) = 0,
      (connecting (Triple.ordinary_triple_degreewiseShortExact R
          (Box.upperLateral_subset_fullBoundary S)) (n+1 : ℕ) n (by simp))
        (cycleClass (ordinary R R (boundaryPair (unitInterval × D) (Box.fullBoundary S)))
          (n : ℤ) (by simp)
          (quotientChain R (boundaryPair (unitInterval × D) (Box.fullBoundary S)) (n+1)
            (P202Specs.RelativeFundamentalClass.PrismLiftGeneric.prismChain R n c)) hp) =
      -((homologyMap (relativeMap (ordinaryFunctor R R)
          (P202Specs.RelativeFundamentalClass.BoxBottom.bottomInclusion S)) (n : ℤ))
        (cycleClass (ordinary R R (P202Specs.RelativeFundamentalClass.BoxBottom.bottomPair S))
          ((ComplexShape.down ℤ).next (n : ℤ)) rfl
          (quotientChain R (P202Specs.RelativeFundamentalClass.BoxBottom.bottomPair S) n c) hc)) := by
  obtain ⟨hp, hb, hδ⟩ := triple_connecting_of_nonnegative_boundary
    (Box.upperLateral_subset_fullBoundary S) n (P202Specs.RelativeFundamentalClass.PrismLiftGeneric.prismChain R n c)
    (P202Specs.RelativeFundamentalClass.PrismLiftGeneric.bottomChain R S n c) (prismChain_boundary_quotient_of_cycle S n c hc)
  refine ⟨hp, ?_⟩
  have hm := cycleClass_map
    (relativeMap (ordinaryFunctor R R)
      (P202Specs.RelativeFundamentalClass.BoxBottom.bottomInclusion S)) rfl
    (quotientChain R (P202Specs.RelativeFundamentalClass.BoxBottom.bottomPair S) n c) hc
  have hm' := hm.trans (cycleClass_congr _ rfl _ _ _ hb
    (quotientChain_naturality (P202Specs.RelativeFundamentalClass.BoxBottom.bottomInclusion S) n c))
  exact hδ.trans (congrArg Neg.neg hm'.symm)

/-- A bottom relative generator produces a genuine top relative prism generator;
no Künneth or unproved shuffle orientation certificate is needed. -/
lemma prismChain_isGenerator {D : Type v} [TopologicalSpace D]
    (S : Set D) (n : ℕ) (c : Chains R (TopCat.of D) n)
    (hc : (ordinary R R (P202Specs.RelativeFundamentalClass.BoxBottom.bottomPair S)).d
      (n : ℤ) ((ComplexShape.down ℤ).next (n : ℤ))
      (quotientChain R (P202Specs.RelativeFundamentalClass.BoxBottom.bottomPair S) n c) = 0)
    (hgen : P202Specs.LocalOrientation.IsGenerator
      (V := (ordinary R R (P202Specs.RelativeFundamentalClass.BoxBottom.bottomPair S)).homology (n : ℤ)) R
      (cycleClass (ordinary R R (P202Specs.RelativeFundamentalClass.BoxBottom.bottomPair S))
        ((ComplexShape.down ℤ).next (n : ℤ)) rfl
        (quotientChain R (P202Specs.RelativeFundamentalClass.BoxBottom.bottomPair S) n c) hc)) :
    ∃ hp : (ordinary R R (boundaryPair (unitInterval × D) (Box.fullBoundary S))).d
      (n+1 : ℕ) n
      (quotientChain R (boundaryPair (unitInterval × D) (Box.fullBoundary S)) (n+1)
        (P202Specs.RelativeFundamentalClass.PrismLiftGeneric.prismChain R n c)) = 0,
      P202Specs.LocalOrientation.IsGenerator
        (V := (ordinary R R (boundaryPair (unitInterval × D) (Box.fullBoundary S))).homology (n+1 : ℕ)) R
        (cycleClass (ordinary R R (boundaryPair (unitInterval × D) (Box.fullBoundary S)))
          (n : ℤ) (by simp)
          (quotientChain R (boundaryPair (unitInterval × D) (Box.fullBoundary S)) (n+1)
            (P202Specs.RelativeFundamentalClass.PrismLiftGeneric.prismChain R n c)) hp) := by
  obtain ⟨hp, hδ⟩ := prismChain_connecting S n c hc
  refine ⟨hp, ?_⟩
  have hij : (ComplexShape.down ℤ).Rel ((n+1 : ℕ) : ℤ) (n : ℤ) := by simp
  haveI := Triple.triple_connecting_isIso (ordinaryFunctor R R)
    (Box.upperLateral_subset_fullBoundary S) (n+1 : ℕ) (n : ℤ) hij
    (Box.upperLateral_relative_isZero R S (n+1 : ℕ))
    (Box.upperLateral_relative_isZero R S (n : ℤ))
  apply (P202.LocalOrientation.generator_map_iff R
    (asIso (connecting (Triple.ordinary_triple_degreewiseShortExact R
      (Box.upperLateral_subset_fullBoundary S)) (n+1 : ℕ) (n : ℤ) hij)).toLinearEquiv _).mp
  change P202Specs.LocalOrientation.IsGenerator R
    ((connecting (Triple.ordinary_triple_degreewiseShortExact R
      (Box.upperLateral_subset_fullBoundary S)) (n+1 : ℕ) (n : ℤ) hij) _)
  rw [hδ]
  apply (P202.LocalOrientation.generator_map_iff R (LinearEquiv.neg R) _).mpr
  haveI := BoxBottom.bottomInclusion_isIso R S (n : ℤ)
  exact (P202.LocalOrientation.generator_map_iff R
    (asIso ((relativeHomologyFunctor R R (n : ℤ)).map
      (P202Specs.RelativeFundamentalClass.BoxBottom.bottomInclusion S))).toLinearEquiv _).mpr hgen


/-- Every top relative box class is a negative interval-first product of an
actual finite bottom relative cycle. No generator assumption is needed. -/
lemma exists_negative_prism_representative (S : Set D) (n : ℕ)
    (a : relativeHomology R R
      (boundaryPair (unitInterval × D) (Box.fullBoundary S)) (n+1 : ℕ)) :
    ∃ (c : Chains R (TopCat.of D) n)
      (hc : (ordinary R R (P202Specs.RelativeFundamentalClass.BoxBottom.bottomPair S)).d
        (n : ℤ) ((ComplexShape.down ℤ).next (n : ℤ))
        (quotientChain R (P202Specs.RelativeFundamentalClass.BoxBottom.bottomPair S) n c) = 0)
      (hp : (ordinary R R (boundaryPair (unitInterval × D) (Box.fullBoundary S))).d
        (n+1 : ℕ) n
        (quotientChain R (boundaryPair (unitInterval × D) (Box.fullBoundary S)) (n+1)
          (P202Specs.RelativeFundamentalClass.PrismLiftGeneric.prismChain R n c)) = 0),
      -(cycleClass (ordinary R R (boundaryPair (unitInterval × D) (Box.fullBoundary S)))
        (n : ℤ) (by simp)
        (quotientChain R (boundaryPair (unitInterval × D) (Box.fullBoundary S)) (n+1)
          (P202Specs.RelativeFundamentalClass.PrismLiftGeneric.prismChain R n c)) hp) = a := by
  let hAB := Box.upperLateral_subset_fullBoundary S
  let δ := connecting (Triple.ordinary_triple_degreewiseShortExact R hAB)
    (n+1 : ℕ) (n : ℤ) (by simp)
  let Hb := (relativeHomologyFunctor R R (n : ℤ)).map
    (P202Specs.RelativeFundamentalClass.BoxBottom.bottomInclusion S)
  haveI : IsIso δ := Triple.triple_connecting_isIso (ordinaryFunctor R R)
    hAB (n+1 : ℕ) (n : ℤ) (by simp)
    (Box.upperLateral_relative_isZero R S (n+1 : ℕ))
    (Box.upperLateral_relative_isZero R S (n : ℤ))
  haveI : IsIso Hb := BoxBottom.bottomInclusion_isIso R S (n : ℤ)
  let b := inv Hb (δ a)
  obtain ⟨c,hc,hrep⟩ := PrismLift.exists_chain_representative
    (P202Specs.RelativeFundamentalClass.BoxBottom.bottomPair S) n b
  obtain ⟨hp,hδ⟩ := prismChain_connecting S n c hc
  refine ⟨c,hc,hp,?_⟩
  apply (ModuleCat.mono_iff_injective δ).mp inferInstance
  change δ (-_) = δ a
  rw [map_neg]
  change δ _ = _ at hδ
  rw [hδ,neg_neg]
  change Hb _ = δ a
  rw [hrep]
  have hh := congrArg (fun f => f (δ a)) (IsIso.inv_hom_id Hb)
  exact hh

end PrismLiftGeneric

namespace BoundaryGenerator
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.LocalOrientation P202Specs.CompactOrientation
open P202Specs.RelativeFundamentalClass
open P202Specs.RelativeFundamentalClass.CollarChart
open P202Specs.RelativeFundamentalClass.CollarClamp
open P202Specs.RelativeFundamentalClass.CollarGlobal
open P202Specs.RelativeFundamentalClass.CollarLocalization

variable {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {M : Type v} [TopologicalSpace M] {B : Set M}

def midpoint (c : Collar B) (fsp : C(V,B)) : M :=
  cylinderMap c fsp (prismInclusion (NormPrism.center V))

lemma midpoint_not_boundary (c : Collar B) (fsp : C(V,B)) : midpoint c fsp ∉ B := by
  rw [midpoint, CollarChart.cylinderMap_boundary_iff]
  change ¬ (1/2 : ℝ) = 0
  norm_num

lemma midpoint_not_deleted (c : Collar B) (fsp : C(V,B)) :
    midpoint c fsp ∉ deletedOutside (cylinderMap c fsp) := by
  intro hA
  apply hA
  refine ⟨prismInclusion (NormPrism.center V), ?_, rfl⟩
  change (1/2 : ℝ) < 1 ∧ ‖(0:V)‖ < 1
  norm_num

lemma midpoint_not_union (c : Collar B) (fsp : C(V,B)) :
    midpoint c fsp ∉ deletedOutside (cylinderMap c fsp) ∪ B := by
  intro h
  exact h.elim (midpoint_not_deleted c fsp) (midpoint_not_boundary c fsp)

/-- The comparison at the interior midpoint is equality of the actual pair maps. -/
lemma midpoint_square [T2Space M] (c : Collar B) (fsp : C(V,B)) (hfsp : IsOpenEmbedding fsp) :
    (pairInclusion (E := V) true ≫
      fullPairMap (cylinderMap c fsp) B
        (CollarChart.cylinderMap_isOpenEmbedding c fsp hfsp).injective
        (CollarChart.cylinderMap_boundary_iff c fsp)) ≫
      interiorPointMap (deletedOutside (cylinderMap c fsp) ∪ B)
        ⟨midpoint c fsp, midpoint_not_union c fsp⟩ =
    NormPrism.toOwnLocal V ≫ CollarClampLocal.cylinderPrismLocalMap V
      (cylinderMap c fsp) (CollarChart.cylinderMap_isOpenEmbedding c fsp hfsp) :=
  PairMap.ext _ _ rfl

lemma original_midpoint_square (c : Collar B) (fsp : C(V,B)) :
    Triple.tripleProjection (Set.subset_union_right : B ⊆ deletedOutside (cylinderMap c fsp) ∪ B) ≫
      interiorPointMap (deletedOutside (cylinderMap c fsp) ∪ B)
        ⟨midpoint c fsp, midpoint_not_union c fsp⟩ =
    interiorPointMap B ⟨midpoint c fsp, midpoint_not_boundary c fsp⟩ :=
  PairMap.ext _ _ rfl

/-- A generator local value of an original relative class at one interior
midpoint forces its actual connecting image to be a boundary local generator.
All collar comparison isomorphisms are proved geometric facts. -/
theorem connectingLocalValues_isGenerator [T2Space M] [ProperSpace V]
    (R : Type u) [CommRing R] (c : Collar B) (fsp : C(V,B)) (hfsp : IsOpenEmbedding fsp)
    (h : P202Specs.ChainLES.DegreewiseShortExact
      (sequence (ordinaryFunctor R R) (boundaryPair M B))) (q : ℕ)
    (g : relativeHomology R R (boundaryPair M B) ((q+1:ℕ):ℤ))
    (hg : IsGenerator R
      (((relativeHomologyFunctor R R ((q+1:ℕ):ℤ)).map
        (interiorPointMap B ⟨midpoint c fsp, midpoint_not_boundary c fsp⟩)) g)) :
    IsGenerator R (connectingLocalValues R B h q g (fsp 0)) := by
  let F := cylinderMap c fsp
  let hF := CollarChart.cylinderMap_isOpenEmbedding c fsp hfsp
  let A := deletedOutside F
  let H := relativeHomologyFunctor R R ((q+1:ℕ):ℤ)
  let P := pairInclusion (E := V) true ≫
    fullPairMap F B hF.injective (CollarChart.cylinderMap_boundary_iff c fsp)
  haveI : IsIso (H.map P) := CollarGlobal.closedFullPairMap_isIso R F hF B
    (CollarChart.cylinderMap_boundary_iff c fsp) (q+1)
  obtain ⟨a, ha⟩ := (asIso (H.map P)).toLinearEquiv.surjective
    ((H.map (Triple.tripleProjection (Set.subset_union_right : B ⊆ A ∪ B))) g)
  change (H.map P) a =
    (H.map (Triple.tripleProjection (Set.subset_union_right : B ⊆ A ∪ B))) g at ha
  let L : closedPair (E := V) true ⟶ localPair M (midpoint c fsp) :=
    NormPrism.toOwnLocal V ≫ CollarClampLocal.cylinderPrismLocalMap V F hF
  haveI := NormPrism.toOwnLocal_isIso V R ((q+1:ℕ):ℤ)
  haveI := CollarClampLocal.cylinderPrismLocalMap_isIso V R F hF ((q+1:ℕ):ℤ)
  haveI : IsIso (H.map L) := by
    dsimp [L]
    rw [H.map_comp]
    infer_instance
  have hlocal : (H.map L) a =
      (H.map (interiorPointMap B ⟨midpoint c fsp, midpoint_not_boundary c fsp⟩)) g := by
    have hs := congrArg H.map (midpoint_square c fsp hfsp)
    have hsmap : H.map L = H.map P ≫
        H.map (interiorPointMap (A ∪ B) ⟨midpoint c fsp, midpoint_not_union c fsp⟩) := by
      rw [← H.map_comp]
      exact hs.symm
    have hs' := congrArg (fun f => f a) hsmap
    change (H.map L) a =
      (H.map (interiorPointMap (A ∪ B) ⟨midpoint c fsp, midpoint_not_union c fsp⟩))
        ((H.map P) a) at hs'
    have hs'' := hs'.trans (congrArg (fun z =>
      (H.map (interiorPointMap (A ∪ B) ⟨midpoint c fsp, midpoint_not_union c fsp⟩)) z) ha)
    have ht := congrArg H.map (original_midpoint_square c fsp)
    rw [H.map_comp] at ht
    exact hs''.trans (congrArg (fun f => f g) ht)
  have hga : IsGenerator R a := by
    apply (P202.LocalOrientation.generator_map_iff R (asIso (H.map L)).toLinearEquiv a).mp
    change IsGenerator R ((H.map L) a)
    rw [hlocal]
    exact hg
  let δ := P202Specs.ChainLES.connecting
    (Triple.ordinary_triple_degreewiseShortExact R
      (show closedUpper (E := V) ⊆ closedFull from fun _ hh => Or.inr hh))
    ((q+1:ℕ):ℤ) (q:ℤ) (by simp)
  haveI : IsIso δ := Triple.triple_connecting_isIso (ordinaryFunctor R R)
    (show closedUpper (E := V) ⊆ closedFull from fun _ hh => Or.inr hh)
    ((q+1:ℕ):ℤ) (q:ℤ) (by simp)
    (Box.upperLateral_relative_isZero R (rim (E := V)) ((q+1:ℕ):ℤ))
    (Box.upperLateral_relative_isZero R (rim (E := V)) (q:ℤ))
  have hgδ : IsGenerator R (δ a) :=
    (P202.LocalOrientation.generator_map_iff R (asIso δ).toLinearEquiv a).mpr hga
  let Hq := relativeHomologyFunctor R R (q:ℤ)
  let Q := CollarBoundaryLocal.closedTargetToLocal c fsp hfsp
  haveI : IsIso (Hq.map Q) := CollarBoundaryLocal.closedTargetToLocal_isIso R c fsp hfsp q
  have hgQ : IsGenerator R ((Hq.map Q) (δ a)) :=
    (P202.LocalOrientation.generator_map_iff R (asIso (Hq.map Q)).toLinearEquiv (δ a)).mpr hgδ
  let U := unionBoundaryLocalInclusion A B (fsp 0)
  haveI : IsIso (Hq.map U) := CollarLocalization.unionBoundaryLocalInclusion_isIso R A B
    (CollarGlobal.deletedOutside_isClosed F hF) (fsp 0)
    (CollarBoundaryLocal.bottomCenter_not_deleted c fsp) q
  apply (P202.LocalOrientation.generator_map_iff R (asIso (Hq.map U)).toLinearEquiv
    (connectingLocalValues R B h q g (fsp 0))).mp
  change IsGenerator R ((Hq.map U) (connectingLocalValues R B h q g (fsp 0)))
  have he := CollarGlobal.originalBoundary_local_model_formula R F hF.injective B
    (CollarChart.cylinderMap_boundary_iff c fsp) (fsp 0)
    (CollarBoundaryLocal.bottomCenter_not_deleted c fsp) h q g a ha
  have hQ : Hq.map Q =
      Hq.map (closedTargetMap F hF.injective B (CollarChart.cylinderMap_boundary_iff c fsp)) ≫
      Hq.map (triplePointMap A B (fsp 0) (CollarBoundaryLocal.bottomCenter_not_deleted c fsp)) :=
    Hq.map_comp _ _
  have he' : (Hq.map U) (connectingLocalValues R B h q g (fsp 0)) = (Hq.map Q) (δ a) :=
    he.trans (congrArg (fun z => z (δ a)) hQ).symm
  rw [he']
  exact hgQ


/-- Apply the local generator result to the actual prescribed interior orientation. -/
theorem connectingLocalValues_isGenerator_of_interiorValues [T2Space M] [ProperSpace V]
    (R : Type u) [CommRing R] (c : Collar B) (hB : IsClosed B)
    (fsp : C(V,B)) (hfsp : IsOpenEmbedding fsp) (q : ℕ)
    (AI : Manifold (q+1) (Interior B)) (o : Orientation R AI)
    (h : P202Specs.ChainLES.DegreewiseShortExact
      (sequence (ordinaryFunctor R R) (boundaryPair M B)))
    (g : relativeHomology R R (boundaryPair M B) ((q+1:ℕ):ℤ))
    (hg : HasInteriorValues R B (q+1) o.val g) :
    IsGenerator R (connectingLocalValues R B h q g (fsp 0)) := by
  apply connectingLocalValues_isGenerator R c fsp hfsp h q g
  let x : Interior B := ⟨midpoint c fsp, midpoint_not_boundary c fsp⟩
  change IsGenerator R (((relativeHomologyFunctor R R ((q+1:ℕ):ℤ)).map (interiorPointMap B x)) g)
  rw [hg x]
  haveI := P202.RelativeFundamentalClass.interiorLocalInclusion_isIso R B hB x (q+1)
  exact (P202.LocalOrientation.generator_map_iff R
    (asIso (((relativeHomologyFunctor R R ((q+1:ℕ):ℤ)).map (interiorLocalInclusion B x)))).toLinearEquiv
    (o.val x)).mpr (o.property.1 x)

/-- Lift the Euclidean chart model to the ambient universe, preserving the
actual centered open embedding. This is solely geometric. -/
lemma manifold_centered_lifted_openEmbedding (q : ℕ) (AB : Manifold q B) (y : B) :
    ∃ fsp : C(ULift.{v} (EuclideanSpace ℝ (Fin q)), B),
      IsOpenEmbedding fsp ∧ fsp 0 = y := by
  obtain ⟨fsp, hfsp, hf0⟩ := CollarChart.manifold_centered_openEmbedding q AB y
  let e : ULift.{v} (EuclideanSpace ℝ (Fin q)) ≃ₜ EuclideanSpace ℝ (Fin q) := Homeomorph.ulift
  refine ⟨fsp.comp ⟨e,e.continuous⟩, hfsp.comp e.isOpenEmbedding, ?_⟩
  exact hf0

/-- The original connecting image is a shared regular boundary orientation.
Regularity follows from its actual local generator values and the already
proved recognition theorem, after the complete geometric collar comparison. -/
theorem connectingLocalValues_isOrientation [T2Space M]
    (R : Type u) [CommRing R] (c : Collar B) (hB : IsClosed B) (q : ℕ)
    (AI : Manifold (q+1) (Interior B)) (o : Orientation R AI) (AB : Manifold q B)
    (h : P202Specs.ChainLES.DegreewiseShortExact
      (sequence (ordinaryFunctor R R) (boundaryPair M B)))
    (g : relativeHomology R R (boundaryPair M B) ((q+1:ℕ):ℤ))
    (hg : HasInteriorValues R B (q+1) o.val g) :
    IsOrientation R AB (connectingLocalValues R B h q g) := by
  apply (P202.RelativeFundamentalClass.connectingLocalValues_isOrientation_iff R B h q AB g).mpr
  intro y
  obtain ⟨fsp,hfsp,hf0⟩ := manifold_centered_lifted_openEmbedding q AB y
  have hh := connectingLocalValues_isGenerator_of_interiorValues R c hB fsp hfsp q AI o h g hg
  exact hf0 ▸ hh

end BoundaryGenerator

theorem boundaryClass_hasLocalValues (R : Type u) [CommRing R]
    (q : ℕ) (B : Type v) [TopologicalSpace B] (AB : Manifold q B)
    (b : Orientation R AB) (hB : IsCompact (Set.univ : Set B)) :
    HasLocalValues R b.val Set.univ (absoluteToSupported R B q (boundaryClass R B q b.val)) := by
  exact Classical.epsilon_spec
    (P202.CompactOrientation.ordinaryFundamentalClass R q B AB b hB).2.exists

theorem zeroBoundary : P202Specs.RelativeFundamentalClass.Expected.zeroBoundary.{u,v} := by
  intro R _ M _ A h
  exact ⟨manifoldBoundary_zero A,
    P202.SingularChains.ordinary_negative_homology R R (TopCat.of (manifoldBoundary A)) (-1) (by omega),
    boundaryHom_zero_dimension R (manifoldBoundary A) h⟩

namespace BoundaryOrientation
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.LocalOrientation P202Specs.CompactOrientation P202Specs.ChainLES
open P202Specs.RelativeFundamentalClass
open P202Specs.RelativeFundamentalClass.BoundaryOrientation
open P202Specs.RelativeFundamentalClass.Disk
open P202Specs.RelativeFundamentalClass.CollarChart
open P202Specs.RelativeFundamentalClass.CollarClamp
open P202Specs.RelativeFundamentalClass.CollarGlobal
open P202Specs.RelativeFundamentalClass.CollarLocalization
open BoundaryGenerator
variable {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {M : Type v} [TopologicalSpace M] {B : Set M}

lemma boxLocalMap_midpoint (c : Collar B) (fsp : C(V,B)) (hfsp : IsOpenEmbedding fsp)
    (hbox : Function.Injective (boxMap c fsp)) :
    boxLocalMap V B c fsp hbox = NormPrism.toOwnLocal V ≫
      CollarClampLocal.cylinderPrismLocalMap V (cylinderMap c fsp)
        (CollarChart.cylinderMap_isOpenEmbedding c fsp hfsp) := PairMap.ext _ _ rfl

lemma boxLocalMap_isIso [T2Space M] (R : Type u) [CommRing R]
    (c : Collar B) (fsp : C(V,B)) (hfsp : IsOpenEmbedding fsp)
    (hbox : Function.Injective (boxMap c fsp)) (j : ℤ) :
    IsIso ((relativeHomologyFunctor R R j).map (boxLocalMap V B c fsp hbox)) := by
  rw [boxLocalMap_midpoint c fsp hfsp hbox, Functor.map_comp]
  haveI := NormPrism.toOwnLocal_isIso V R j
  haveI := CollarClampLocal.cylinderPrismLocalMap_isIso V R
    (cylinderMap c fsp) (CollarChart.cylinderMap_isOpenEmbedding c fsp hfsp) j
  infer_instance

/-- Localizing the actual global-to-model comparison is the original midpoint
localization, through the exact pair squares. -/
lemma model_midpoint_value [T2Space M] (R : Type u) [CommRing R]
    (c : Collar B) (fsp : C(V,B)) (hfsp : IsOpenEmbedding fsp)
    (hbox : Function.Injective (boxMap c fsp)) (q : ℕ)
    (g : relativeHomology R R (boundaryPair M B) ((q+1:ℕ):ℤ))
    (a : relativeHomology R R (NormPrism.prismPair V) ((q+1:ℕ):ℤ))
    (ha : ((relativeHomologyFunctor R R ((q+1:ℕ):ℤ)).map
        (pairInclusion (E := V) true ≫ fullPairMap (cylinderMap c fsp) B
          (CollarChart.cylinderMap_isOpenEmbedding c fsp hfsp).injective
          (CollarChart.cylinderMap_boundary_iff c fsp))) a =
      ((relativeHomologyFunctor R R ((q+1:ℕ):ℤ)).map
        (Triple.tripleProjection (Set.subset_union_right :
          B ⊆ deletedOutside (cylinderMap c fsp) ∪ B))) g) :
    ((relativeHomologyFunctor R R ((q+1:ℕ):ℤ)).map (boxLocalMap V B c fsp hbox)) a =
      ((relativeHomologyFunctor R R ((q+1:ℕ):ℤ)).map
        (interiorPointMap B ⟨boxMap c fsp (NormPrism.center V), midpoint_not_boundary c fsp⟩)) g := by
  let H := relativeHomologyFunctor R R ((q+1:ℕ):ℤ)
  let A := deletedOutside (cylinderMap c fsp)
  have hs : (pairInclusion (E := V) true ≫ fullPairMap (cylinderMap c fsp) B
        (CollarChart.cylinderMap_isOpenEmbedding c fsp hfsp).injective
        (CollarChart.cylinderMap_boundary_iff c fsp)) ≫
      interiorPointMap (A ∪ B) ⟨midpoint c fsp,midpoint_not_union c fsp⟩ =
      boxLocalMap V B c fsp hbox := by
    rw [boxLocalMap_midpoint c fsp hfsp hbox]
    exact midpoint_square c fsp hfsp
  have he := congrArg (fun f => f a) (congrArg H.map hs)
  rw [H.map_comp] at he
  change (H.map (interiorPointMap (A ∪ B) ⟨midpoint c fsp,midpoint_not_union c fsp⟩))
      ((H.map _) a) = (H.map (boxLocalMap V B c fsp hbox)) a at he
  have he' := he.symm.trans (congrArg (fun z =>
    (H.map (interiorPointMap (A ∪ B) ⟨midpoint c fsp,midpoint_not_union c fsp⟩)) z) ha)
  have ht := congrArg H.map (original_midpoint_square c fsp)
  rw [H.map_comp] at ht
  exact he'.trans (congrArg (fun f => f g) ht)

/-- The negative inward shuffle has positive bottom local boundary value. -/
lemma negative_prism_boundary_local [T2Space M] (R : Type u) [CommRing R]
    (c : Collar B) (fsp : C(V,B)) (hfsp : IsOpenEmbedding fsp) (q : ℕ)
    (h : DegreewiseShortExact (sequence (ordinaryFunctor R R) (boundaryPair M B)))
    (g : relativeHomology R R (boundaryPair M B) ((q+1:ℕ):ℤ))
    (a : Chains R (TopCat.of (UnitDisk V)) q)
    (ha : IsDiskCycle R V q a) (hp : IsPrismCycle R V q a)
    (hamodel : ((relativeHomologyFunctor R R ((q+1:ℕ):ℤ)).map
        (pairInclusion (E := V) true ≫ fullPairMap (cylinderMap c fsp) B
          (CollarChart.cylinderMap_isOpenEmbedding c fsp hfsp).injective
          (CollarChart.cylinderMap_boundary_iff c fsp))) (-inwardClass R V q a hp) =
      ((relativeHomologyFunctor R R ((q+1:ℕ):ℤ)).map
        (Triple.tripleProjection (Set.subset_union_right :
          B ⊆ deletedOutside (cylinderMap c fsp) ∪ B))) g) :
    bottomLocalValue R V B fsp hfsp.injective q a ha =
      connectingLocalValues R B h q g (fsp 0) := by
  let F := cylinderMap c fsp
  let hF := CollarChart.cylinderMap_isOpenEmbedding c fsp hfsp
  let A := deletedOutside F
  let Hq := relativeHomologyFunctor R R (q:ℤ)
  let δ := connecting (Triple.ordinary_triple_degreewiseShortExact R
    (Box.upperLateral_subset_fullBoundary (unitPair V).subspace)) ((q+1:ℕ):ℤ) (q:ℤ) (by simp)
  obtain ⟨hp',hδ⟩ := PrismLiftGeneric.prismChain_connecting (unitPair V).subspace q a ha
  change δ (inwardClass R V q a hp) =
    -((Hq.map (P202Specs.RelativeFundamentalClass.BoxBottom.bottomInclusion (unitPair V).subspace))
      (diskClass R V q a ha)) at hδ
  have hδneg : δ (-inwardClass R V q a hp) =
      (Hq.map (P202Specs.RelativeFundamentalClass.BoxBottom.bottomInclusion (unitPair V).subspace))
        (diskClass R V q a ha) := by
    rw [map_neg,hδ,neg_neg]
  let Q := CollarBoundaryLocal.closedTargetToLocal c fsp hfsp
  let U := unionBoundaryLocalInclusion A B (fsp 0)
  haveI : IsIso (Hq.map U) := CollarLocalization.unionBoundaryLocalInclusion_isIso R A B
    (CollarGlobal.deletedOutside_isClosed F hF) (fsp 0)
    (CollarBoundaryLocal.bottomCenter_not_deleted c fsp) q
  apply (ModuleCat.mono_iff_injective (Hq.map U)).mp inferInstance
  have he := CollarGlobal.originalBoundary_local_model_formula R F hF.injective B
    (CollarChart.cylinderMap_boundary_iff c fsp) (fsp 0)
    (CollarBoundaryLocal.bottomCenter_not_deleted c fsp) h q g (-inwardClass R V q a hp) hamodel
  have hQ : Hq.map Q =
      Hq.map (closedTargetMap F hF.injective B (CollarChart.cylinderMap_boundary_iff c fsp)) ≫
      Hq.map (triplePointMap A B (fsp 0) (CollarBoundaryLocal.bottomCenter_not_deleted c fsp)) :=
    Hq.map_comp _ _
  have he' : (Hq.map U) (connectingLocalValues R B h q g (fsp 0)) =
      (Hq.map Q) (δ (-inwardClass R V q a hp)) :=
    he.trans (congrArg (fun z => z (δ (-inwardClass R V q a hp))) hQ).symm
  have hs : Hq.map (P202Specs.RelativeFundamentalClass.BoxBottom.bottomInclusion (unitPair V).subspace) ≫
      Hq.map Q = Hq.map (toLocal V ≫
        P202Specs.RelativeFundamentalClass.EmbeddingLocal.localMap fsp hfsp.injective 0) ≫ Hq.map U := by
    rw [← Hq.map_comp,← Hq.map_comp]
    exact congrArg Hq.map (CollarBoundaryLocal.closedTargetToLocal_bottom_square c fsp hfsp)
  have hs' := congrArg (fun f => f (diskClass R V q a ha)) hs
  change (Hq.map Q)
    ((Hq.map (P202Specs.RelativeFundamentalClass.BoxBottom.bottomInclusion (unitPair V).subspace))
      (diskClass R V q a ha)) = (Hq.map U) (bottomLocalValue R V B fsp hfsp.injective q a ha) at hs'
  exact (he'.trans ((congrArg (Hq.map Q) hδneg).trans hs')).symm

/-- The geometric outward-normal-first condition in an arbitrary collar box is
exactly the local value of the actual positive connecting image. -/
theorem outwardInBox_iff_local_boundary [T2Space M] [ProperSpace V]
    (R : Type u) [CommRing R] (c : Collar B) (q : ℕ)
    (o : LocalChoice R (q+1) (Interior B)) (b : LocalChoice R q B)
    (fsp : C(V,B)) (hfsp : IsOpenEmbedding fsp)
    (h : DegreewiseShortExact (sequence (ordinaryFunctor R R) (boundaryPair M B)))
    (g : relativeHomology R R (boundaryPair M B) ((q+1:ℕ):ℤ))
    (hg : HasInteriorValues R B (q+1) o g) :
    IsOutwardInBox R V B c q o b fsp hfsp ↔
      b (fsp 0) = connectingLocalValues R B h q g (fsp 0) := by
  let F := cylinderMap c fsp
  let hF := CollarChart.cylinderMap_isOpenEmbedding c fsp hfsp
  let A := deletedOutside F
  let H := relativeHomologyFunctor R R ((q+1:ℕ):ℤ)
  let P := pairInclusion (E := V) true ≫
    fullPairMap F B hF.injective (CollarChart.cylinderMap_boundary_iff c fsp)
  haveI : IsIso (H.map P) := CollarGlobal.closedFullPairMap_isIso R F hF B
    (CollarChart.cylinderMap_boundary_iff c fsp) (q+1)
  obtain ⟨α,hα⟩ := (asIso (H.map P)).toLinearEquiv.surjective
    ((H.map (Triple.tripleProjection (Set.subset_union_right : B ⊆ A ∪ B))) g)
  change (H.map P) α =
    (H.map (Triple.tripleProjection (Set.subset_union_right : B ⊆ A ∪ B))) g at hα
  let hbox := CollarChart.boxMap_injective c fsp hfsp
  let hx := midpoint_not_boundary c fsp
  let L := boxLocalMap V B c fsp hbox
  haveI : IsIso (H.map L) := boxLocalMap_isIso R c fsp hfsp hbox ((q+1:ℕ):ℤ)
  have hαlocal := model_midpoint_value R c fsp hfsp hbox q g α hα
  constructor
  · rintro ⟨hbox',hx',a,ha,hp,hbottom,hout⟩
    have hmodel : -inwardClass R V q a hp = α := by
      apply (ModuleCat.mono_iff_injective (H.map L)).mp inferInstance
      exact (hout.trans (hg ⟨boxMap c fsp (NormPrism.center V),hx'⟩).symm).trans hαlocal.symm
    have hamodel := (congrArg (H.map P) hmodel).trans hα
    exact hbottom.symm.trans (negative_prism_boundary_local R c fsp hfsp q h g a ha hp hamodel)
  · intro heq
    obtain ⟨a,ha,hp,hrep⟩ := PrismLiftGeneric.exists_negative_prism_representative
      (unitPair V).subspace q α
    have hrep' : -inwardClass R V q a hp = α := hrep
    have hamodel := (congrArg (H.map P) hrep').trans hα
    refine ⟨hbox,hx,a,ha,hp,?_,?_⟩
    · exact (negative_prism_boundary_local R c fsp hfsp q h g a ha hp hamodel).trans heq.symm
    · exact (model_midpoint_value R c fsp hfsp hbox q g (-inwardClass R V q a hp) hamodel).trans
        (hg ⟨boxMap c fsp (NormPrism.center V),hx⟩)

end BoundaryOrientation

namespace BoundaryOrientation
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.LocalOrientation P202Specs.CompactOrientation
open P202Specs.RelativeFundamentalClass

variable {M : Type v} [TopologicalSpace M] {B : Set M}

/-- Centered spatial charts detect equality of all shared local choices. -/
lemma chartPointValues_eq_iff (R : Type u) [CommRing R] (q : ℕ) (AB : Manifold q B)
    (a b : LocalChoice R q B) :
    (∀ (V : Type v) [NormedAddCommGroup V] [NormedSpace ℝ V] [ProperSpace V]
      (f : C(V,B)) (_hf : IsOpenEmbedding f), a (f 0) = b (f 0)) ↔ a = b := by
  constructor
  · intro h
    funext y
    obtain ⟨f,hf,hf0⟩ := BoundaryGenerator.manifold_centered_lifted_openEmbedding q AB y
    exact hf0 ▸ (h _ f hf)
  · intro h V _ _ _ f hf
    exact congrFun h (f 0)

/-- The independently defined outward-normal-first product convention equals
exactly the actual local values of the positive original connecting image. -/
theorem outwardNormalFirst_iff_connectingLocalValues [T2Space M]
    (R : Type u) [CommRing R] (c : Collar B) (q : ℕ)
    (o : LocalChoice R (q+1) (Interior B)) (b : LocalChoice R q B) (AB : Manifold q B)
    (h : P202Specs.ChainLES.DegreewiseShortExact
      (sequence (ordinaryFunctor R R) (boundaryPair M B)))
    (g : relativeHomology R R (boundaryPair M B) ((q+1:ℕ):ℤ))
    (hg : HasInteriorValues R B (q+1) o g) :
    IsOutwardNormalFirst R B c q o b ↔ b = connectingLocalValues R B h q g := by
  constructor
  · intro hb
    apply (chartPointValues_eq_iff R q AB b (connectingLocalValues R B h q g)).mp
    intro V _ _ _ f hf
    exact (outwardInBox_iff_local_boundary R c q o b f hf h g hg).mp (hb V f hf)
  · intro hb V _ _ _ f hf
    exact (outwardInBox_iff_local_boundary R c q o b f hf h g hg).mpr (congrFun hb (f 0))

/-- Any two geometric collars induce exactly the same outward-normal-first
boundary local choice for the fixed interior orientation. -/
theorem outwardNormalFirst_collar_independent [T2Space M]
    (R : Type u) [CommRing R] (c c' : Collar B) (q : ℕ)
    (o : LocalChoice R (q+1) (Interior B)) (b : LocalChoice R q B) (AB : Manifold q B)
    (h : P202Specs.ChainLES.DegreewiseShortExact
      (sequence (ordinaryFunctor R R) (boundaryPair M B)))
    (g : relativeHomology R R (boundaryPair M B) ((q+1:ℕ):ℤ))
    (hg : HasInteriorValues R B (q+1) o g) :
    IsOutwardNormalFirst R B c q o b ↔ IsOutwardNormalFirst R B c' q o b :=
  (outwardNormalFirst_iff_connectingLocalValues R c q o b AB h g hg).trans
    (outwardNormalFirst_iff_connectingLocalValues R c' q o b AB h g hg).symm

/-- The independent local product convention determines a unique regular
boundary orientation, without a boundary sign/generation certificate. -/
theorem existsUnique_outwardOrientation [T2Space M]
    (R : Type u) [CommRing R] (c : Collar B) (hB : IsClosed B) (q : ℕ)
    (AI : Manifold (q+1) (Interior B)) (o : Orientation R AI) (AB : Manifold q B)
    (h : P202Specs.ChainLES.DegreewiseShortExact
      (sequence (ordinaryFunctor R R) (boundaryPair M B)))
    (g : relativeHomology R R (boundaryPair M B) ((q+1:ℕ):ℤ))
    (hg : HasInteriorValues R B (q+1) o.val g) :
    ∃! b : Orientation R AB, IsOutwardNormalFirst R B c q o.val b.val := by
  let b0 : Orientation R AB := ⟨connectingLocalValues R B h q g,
    BoundaryGenerator.connectingLocalValues_isOrientation R c hB q AI o AB h g hg⟩
  refine ⟨b0, ?_, ?_⟩
  · exact (outwardNormalFirst_iff_connectingLocalValues R c q o.val b0.val AB h g hg).mpr rfl
  · intro b hb
    apply Subtype.ext
    exact (outwardNormalFirst_iff_connectingLocalValues R c q o.val b.val AB h g hg).mp hb

end BoundaryOrientation

theorem inducedBoundary : P202Specs.RelativeFundamentalClass.Expected.inducedBoundary.{u,v} := by
  intro R _ q M _ _ B hB c AI AB o hM
  let g := fundamentalClass R B (q+1) o.val
  have hg : HasInteriorValues R B (q+1) o.val g :=
    fundamentalClass_hasInteriorValues R (q+1) M B hB c AI o hM
  let hseq := P202.RelativeSingularChains.sequence_shortExact (ordinaryFunctor R R) (boundaryPair M B)
  have hCompactB : IsCompact (Set.univ : Set B) := by
    letI : CompactSpace M := isCompact_univ_iff.mp hM
    letI : CompactSpace B := isCompact_iff_compactSpace.mp hB.isCompact
    exact isCompact_univ
  refine ⟨BoundaryOrientation.existsUnique_outwardOrientation R c hB q AI o AB hseq g hg, ?_⟩
  intro b hb h
  have hbclass := boundaryClass_hasLocalValues R q B AB b hCompactB
  refine ⟨hbclass, ?_⟩
  apply (boundaryRecognition R q M B AB b hCompactB h g (boundaryClass R B q b.val) hbclass).mpr
  exact ((BoundaryOrientation.outwardNormalFirst_iff_connectingLocalValues
    R c q o.val b.val AB h g hg).mp hb).symm

theorem collarIndependence : P202Specs.RelativeFundamentalClass.Expected.collarIndependence.{u,v} := by
  intro R _ q M _ _ B hB c₁ c₂ AI AB o hM b₁ b₂ hb₁ hb₂
  let g := fundamentalClass R B (q+1) o.val
  have hg : HasInteriorValues R B (q+1) o.val g :=
    fundamentalClass_hasInteriorValues R (q+1) M B hB c₁ AI o hM
  let hseq := P202.RelativeSingularChains.sequence_shortExact (ordinaryFunctor R R) (boundaryPair M B)
  apply Subtype.ext
  exact ((BoundaryOrientation.outwardNormalFirst_iff_connectingLocalValues
    R c₁ q o.val b₁.val AB hseq g hg).mp hb₁).trans
    ((BoundaryOrientation.outwardNormalFirst_iff_connectingLocalValues
    R c₂ q o.val b₂.val AB hseq g hg).mp hb₂).symm

theorem intrinsicBoundary : P202Specs.RelativeFundamentalClass.Expected.intrinsicBoundary.{u,v} := by
  intro R _ q M _ A
  dsimp only
  intro c AI AB o hM
  letI := A.hausdorff
  exact inducedBoundary R q M (manifoldBoundary A) (Geometry.manifoldBoundary_isClosed A)
    c AI AB o hM

end P202.RelativeFundamentalClass
