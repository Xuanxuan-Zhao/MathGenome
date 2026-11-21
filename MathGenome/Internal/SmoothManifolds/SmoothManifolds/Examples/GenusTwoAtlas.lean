import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Examples.SpheresAndTori
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Examples.PolarCoordinates
import Mathlib.Topology.Piecewise
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Examples.GenusTwoAtlas
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Tactic.NormNum

/-! The literal connected sum of two flat tori. The quotient topology is
retained throughout. Bulk charts come from the angle atlas; signed radial
charts are proved continuous and open using their two ambient polar images.
Local lifts differ by integer translations, and the collar maps have invertible
derivatives, giving smooth compatibility and the fixed maximal structure. -/

namespace SmoothManifolds.GenusTwoAtlas
open ModelData SphereTorusData GenusTwoData SphereTorus Set Topology TopologicalSpace
open Filter
open scoped BigOperators

lemma coordinates_small {x : Euclidean 2}
    (hx : squareSum x < (1 / 8 : ℝ) ^ 2) (j : Fin 2) : |x j| < 1 / 8 := by
  have hs : (x 0) ^ 2 + (x 1) ^ 2 < (1 / 8 : ℝ) ^ 2 := by
    simpa [squareSum, Fin.sum_univ_two] using hx
  apply abs_lt_of_sq_lt_sq _ (by norm_num)
  fin_cases j <;> dsimp <;> nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]

lemma isOpen_removedDisk : IsOpen removedDisk :=
  (quotientProjection_isOpenQuotientMap 2).isOpenMap _
    (isOpen_lt (continuous_squareSum 2) continuous_const)


lemma coordinates_le {x : Euclidean 2}
    (hx : squareSum x ≤ (1 / 8 : ℝ) ^ 2) (j : Fin 2) : |x j| ≤ 1 / 8 := by
  apply abs_le_of_sq_le_sq _ (by norm_num)
  have hs : (x 0) ^ 2 + (x 1) ^ 2 ≤ (1 / 8 : ℝ) ^ 2 := by
    simpa [squareSum, Fin.sum_univ_two] using hx
  fin_cases j <;> dsimp <;> nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]

lemma squareSum_eq_norm_sq (x : Euclidean 2) :
    squareSum x = ‖WithLp.toLp 2 x‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp [squareSum, Real.norm_eq_abs]

lemma closure_coordinateDisk :
    closure {x : Euclidean 2 | squareSum x < (1 / 8 : ℝ) ^ 2} =
      {x : Euclidean 2 | squareSum x ≤ (1 / 8 : ℝ) ^ 2} := by
  let e := (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)).symm
  have he : {x : Euclidean 2 | squareSum x < (1 / 8 : ℝ) ^ 2} =
      e ⁻¹' Metric.ball 0 (1 / 8 : ℝ) := by
    ext x
    simp only [mem_ofPred_eq, mem_preimage, Metric.mem_ball, dist_zero_right]
    rw [squareSum_eq_norm_sq]
    exact sq_lt_sq₀ (norm_nonneg _) (by norm_num)
  rw [he, ← e.preimage_closure, closure_ball 0 (by norm_num : (1 / 8 : ℝ) ≠ 0)]
  ext x
  simp only [mem_ofPred_eq, mem_preimage, Metric.mem_closedBall, dist_zero_right]
  rw [squareSum_eq_norm_sq]
  exact (sq_le_sq₀ (norm_nonneg _) (by norm_num)).symm

lemma isCompact_coordinateClosedDisk :
    IsCompact {x : Euclidean 2 | squareSum x ≤ (1 / 8 : ℝ) ^ 2} := by
  let e := PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)
  have he : {x : Euclidean 2 | squareSum x ≤ (1 / 8 : ℝ) ^ 2} =
      e '' Metric.closedBall 0 (1 / 8 : ℝ) := by
    rw [e.image_eq_preimage_symm]
    ext x
    simp only [mem_ofPred_eq, mem_preimage, Metric.mem_closedBall, dist_zero_right]
    rw [squareSum_eq_norm_sq]
    exact sq_le_sq₀ (norm_nonneg _) (by norm_num)
  rw [he]
  exact (isCompact_closedBall _ _).image e.continuous

lemma closure_removedDisk : closure removedDisk = quotientProjection 2 ''
    {x : Euclidean 2 | squareSum x ≤ (1 / 8 : ℝ) ^ 2} := by
  have hc := (quotientProjection_isOpenQuotientMap 2).continuous
  apply subset_antisymm
  · apply closure_minimal
    · exact image_mono (fun _ hx => show squareSum _ ≤ (1 / 8 : ℝ) ^ 2 from hx.le)
    · exact (isCompact_coordinateClosedDisk.image hc).isClosed
  · rw [← closure_coordinateDisk]
    exact image_closure_subset_closure_image hc

lemma boundaryCircle_eq : boundaryCircle = quotientProjection 2 ''
    {x : Euclidean 2 | squareSum x = (1 / 8 : ℝ) ^ 2} := by
  rw [boundaryCircle, frontier, isOpen_removedDisk.interior_eq, closure_removedDisk]
  ext p
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hn⟩
    refine ⟨x, le_antisymm hx (le_of_not_gt ?_), rfl⟩
    intro h
    exact hn ⟨x, h, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x, hx.le, rfl⟩, ?_⟩
    rintro ⟨y, hy, he⟩
    have hxb : x ∈ angleBox (0 : Euclidean 2) (1 / 3) := by
      intro j
      simpa using lt_of_le_of_lt (coordinates_le hx.le j) (by norm_num : (1:ℝ)/8 < 1/3)
    have hyb : y ∈ angleBox (0 : Euclidean 2) (1 / 3) := by
      intro j
      simpa using lt_trans (coordinates_small hy j) (by norm_num : (1:ℝ)/8 < 1/3)
    have heq := quotientProjection_injOn_box (0 : Euclidean 2)
      (by norm_num : (1 : ℝ) / 3 < 1 / 2) hyb hxb he
    change squareSum y < (1 / 8 : ℝ) ^ 2 at hy
    change squareSum x = (1 / 8 : ℝ) ^ 2 at hx
    rw [heq, hx] at hy
    exact (lt_irrefl _ hy)

lemma reflect_projection (x : Euclidean 2) :
    reflectTorus (quotientProjection 2 x) = quotientProjection 2 (reflectCoordinates x) := by
  funext j
  change (if j = 0 then -(x j : AddCircle (1 : ℝ)) else (x j : AddCircle (1 : ℝ))) =
    ((if j = 0 then -(x j) else x j : ℝ) : AddCircle (1 : ℝ))
  split_ifs <;> simp

lemma squareSum_reflect (x : Euclidean 2) :
    squareSum (reflectCoordinates x) = squareSum x := by
  unfold squareSum reflectCoordinates
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

lemma reflectCoordinates_involutive (x : Euclidean 2) :
    reflectCoordinates (reflectCoordinates x) = x := by
  funext j
  by_cases hj : j = 0 <;> simp [reflectCoordinates, hj]

lemma reflect_mem_removedDisk (p : FlatTorus 2) :
    reflectTorus p ∈ removedDisk ↔ p ∈ removedDisk := by
  have h (q : FlatTorus 2) (hq : q ∈ removedDisk) : reflectTorus q ∈ removedDisk := by
    obtain ⟨x, hx, rfl⟩ := hq
    exact ⟨reflectCoordinates x, by simpa only [mem_ofPred_eq, squareSum_reflect] using hx,
      (reflect_projection x).symm⟩
  exact ⟨fun hp => by simpa using h _ hp, h p⟩

lemma reflect_mem_boundaryCircle (p : FlatTorus 2) :
    reflectTorus p ∈ boundaryCircle ↔ p ∈ boundaryCircle := by
  rw [boundaryCircle_eq]
  have h (q : FlatTorus 2)
      (hq : q ∈ quotientProjection 2 '' {x | squareSum x = (1 / 8 : ℝ) ^ 2}) :
      reflectTorus q ∈ quotientProjection 2 '' {x | squareSum x = (1 / 8 : ℝ) ^ 2} := by
    obtain ⟨x, hx, rfl⟩ := hq
    exact ⟨reflectCoordinates x, by simpa only [mem_ofPred_eq, squareSum_reflect] using hx,
      (reflect_projection x).symm⟩
  exact ⟨fun hp => by simpa using h _ hp, h p⟩

lemma diskGeometry : Specs.SmoothManifolds.Examples.GenusTwoAtlas.diskGeometryType :=
  ⟨isOpen_removedDisk, boundaryCircle_eq, reflect_mem_removedDisk, reflect_mem_boundaryCircle⟩


instance puncturedCompactSpace : CompactSpace PuncturedTorus :=
  isCompact_iff_compactSpace.mp isOpen_removedDisk.isClosed_compl.isCompact

lemma base_notMem_removedDisk :
    quotientProjection 2 ![(1 / 4 : ℝ), 0] ∉ removedDisk := by
  rintro ⟨x, hx, he⟩
  have hxb : x ∈ angleBox (0 : Euclidean 2) (1 / 3) := by
    intro j
    simpa [Pi.zero_apply] using lt_trans (coordinates_small hx j) (by norm_num : (1:ℝ)/8 < 1/3)
  have hbase : ![(1 / 4 : ℝ), 0] ∈ angleBox (0 : Euclidean 2) (1 / 3) := by
    intro j
    fin_cases j <;> norm_num
  have heq := quotientProjection_injOn_box (0 : Euclidean 2)
    (by norm_num : (1 : ℝ) / 3 < 1 / 2) hxb hbase he
  have h := coordinates_small hx 0
  rw [heq] at h
  norm_num at h

instance puncturedNonempty : Nonempty PuncturedTorus :=
  ⟨⟨quotientProjection 2 ![(1 / 4 : ℝ), 0], base_notMem_removedDisk⟩⟩

instance surfaceNonempty : Nonempty Surface :=
  ⟨sideInclusion false (Classical.choice puncturedNonempty)⟩

instance surfaceCompactSpace : CompactSpace Surface := inferInstance

lemma continuous_projection : Continuous projection := continuous_quotient_mk'

lemma projection_surjective : Function.Surjective projection := Quotient.mk_surjective

lemma projection_eq_iff (x y : Pieces) : projection x = projection y ↔ Glued x y :=
  Quotient.eq

lemma sideInclusion_injective (side : Bool) : Function.Injective (sideInclusion side) := by
  intro x y he
  rcases (projection_eq_iff (side, x) (side, y)).mp he with he | ⟨h, _⟩
  · exact congrArg Prod.snd he
  · exact (h rfl).elim

lemma exactFibers : Specs.SmoothManifolds.Examples.GenusTwoAtlas.exactFibersType :=
  ⟨projection_eq_iff, sideInclusion_injective⟩

lemma continuous_reflectTorus : Continuous reflectTorus := by
  apply continuous_pi
  intro j
  change Continuous (fun p : FlatTorus 2 => if j = 0 then -(p j) else p j)
  split_ifs <;> fun_prop

lemma isClosed_glued : IsClosed {p : Pieces × Pieces | Glued p.1 p.2} := by
  apply IsClosed.union (isClosed_eq continuous_fst continuous_snd)
  have hb : IsClosed {p : Pieces × Pieces | p.1.1 ≠ p.2.1} := by
    exact (isClosed_discrete {b : Bool × Bool | b.1 ≠ b.2}).preimage
      (continuous_fst.fst.prodMk continuous_snd.fst)
  have hx : IsClosed {p : Pieces × Pieces | p.1.2.val ∈ boundaryCircle} :=
    isClosed_frontier.preimage (continuous_subtype_val.comp continuous_fst.snd)
  have hy : IsClosed {p : Pieces × Pieces | p.2.2.val ∈ boundaryCircle} :=
    isClosed_frontier.preimage (continuous_subtype_val.comp continuous_snd.snd)
  have he : IsClosed {p : Pieces × Pieces |
      p.2.2.val = reflectTorus p.1.2.val} :=
    isClosed_eq (continuous_subtype_val.comp continuous_snd.snd)
      (continuous_reflectTorus.comp (continuous_subtype_val.comp continuous_fst.snd))
  exact hb.inter (hx.inter (hy.inter he))

/-- Compactness and the closed relation make the quotient map closed. -/
lemma isClosedMap_projection : IsClosedMap projection := by
  intro K hK
  apply isQuotientMap_quotient_mk'.isClosed_preimage.mp
  have he : projection ⁻¹' (projection '' K) =
      Prod.fst '' ({p : Pieces × Pieces | Glued p.1 p.2} ∩ Prod.snd ⁻¹' K) := by
    ext x
    constructor
    · rintro ⟨y, hy, he⟩
      exact ⟨(x, y), ⟨(projection_eq_iff x y).mp he.symm, hy⟩, rfl⟩
    · rintro ⟨⟨z, y⟩, ⟨hzy, hy⟩, rfl⟩
      exact ⟨y, hy, ((projection_eq_iff z y).mpr hzy).symm⟩
  change IsClosed (projection ⁻¹' (projection '' K))
  rw [he]
  exact ((isClosed_glued.inter (hK.preimage continuous_snd)).isCompact.image
    continuous_fst).isClosed

lemma finite_fiber (z : Surface) : (projection ⁻¹' {z}).Finite := by
  obtain ⟨x, rfl⟩ := projection_surjective z
  let f : Pieces → Bool × FlatTorus 2 := fun y => (y.1, y.2.val)
  have hf : Function.Injective f := by
    intro y z h
    exact Prod.ext (congrArg (fun p : Bool × FlatTorus 2 => p.1) h)
      (Subtype.ext (congrArg (fun p : Bool × FlatTorus 2 => p.2) h))
  refine Set.Finite.of_finite_image (f := f) ?_ hf.injOn
  apply Set.Finite.subset (s := {f x} ∪ (Set.univ : Set Bool) ×ˢ {reflectTorus x.2.val})
    (Set.finite_singleton _ |>.union (Set.toFinite _ |>.prod (Set.finite_singleton _)))
  rintro _ ⟨y, hy, rfl⟩
  have hxy : Glued x y := (projection_eq_iff x y).mp hy.symm
  rcases hxy with rfl | ⟨_, _, _, he⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨mem_univ _, he⟩

lemma isProperMap_projection : IsProperMap projection :=
  isProperMap_iff_isClosedMap_and_compact_fibers.mpr
    ⟨continuous_projection, isClosedMap_projection, fun z => (finite_fiber z).isCompact⟩

instance surfaceT2Space : T2Space Surface := by
  apply t2_iff_isClosed_diagonal.mpr
  have hp := isProperMap_projection.prodMap isProperMap_projection
  have hq := hp.isClosedMap.isQuotientMap hp.continuous
    (Function.Surjective.prodMap projection_surjective projection_surjective)
  apply hq.isClosed_preimage.mp
  convert isClosed_glued using 1
  ext p
  exact projection_eq_iff p.1 p.2

/-- Closed continuous surjections with finite fibers preserve second
countability: use kernel images of finite unions of members of a countable
basis. In particular the gluing projection need not be an open map. -/
theorem secondCountableTopology_of_closed_finite_fibers
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [SecondCountableTopology X] {f : X → Y} (hc : Continuous f)
    (hclosed : IsClosedMap f) (hsurj : Function.Surjective f)
    (hf : ∀ y, (f ⁻¹' {y}).Finite) : SecondCountableTopology Y := by
  classical
  let B := countableBasis X
  let C : Set (Set X) := sUnion '' {F : Set (Set X) | F.Finite ∧ F ⊆ B}
  let D : Set (Set Y) := kernImage f '' C
  have hC : C.Countable :=
    (Set.countable_ofPred_finite_subset (countable_countableBasis X)).image sUnion
  have hD : D.Countable := hC.image (kernImage f)
  apply IsTopologicalBasis.secondCountableTopology (b := D) _ hD
  apply isTopologicalBasis_of_isOpen_of_nhds
  · rintro _ ⟨_, ⟨F, ⟨_, hFB⟩, rfl⟩, rfl⟩
    apply (isClosedMap_iff_kernImage.mp hclosed)
    exact isOpen_sUnion (fun U hU => isOpen_of_mem_countableBasis (hFB hU))
  · intro y U hy hU
    have : Finite (f ⁻¹' {y}) := (hf y).to_subtype
    have hchoice : ∀ x : (f ⁻¹' {y}), ∃ V ∈ B,
        x.val ∈ V ∧ V ⊆ f ⁻¹' U := by
      intro x
      exact (isBasis_countableBasis X).exists_subset_of_mem_open
        (by change f x.val ∈ U; rw [show f x.val = y from x.property]; exact hy)
        (hU.preimage hc)
    choose V hVB hxV hVU using hchoice
    let F : Set (Set X) := range V
    have hFB : F ⊆ B := by rintro _ ⟨x, rfl⟩; exact hVB x
    have hF : F.Finite := finite_range V
    refine ⟨kernImage f (⋃₀ F), ⟨⋃₀ F, ⟨F, ⟨hF, hFB⟩, rfl⟩, rfl⟩, ?_, ?_⟩
    · intro x hxy
      exact mem_sUnion.mpr ⟨V ⟨x, hxy⟩, ⟨⟨x, hxy⟩, rfl⟩, hxV ⟨x, hxy⟩⟩
    · intro z hz
      obtain ⟨x, rfl⟩ := hsurj z
      obtain ⟨W, ⟨a, rfl⟩, hxW⟩ := mem_sUnion.mp (hz rfl)
      exact hVU a hxW

instance surfaceSecondCountableTopology : SecondCountableTopology Surface :=
  secondCountableTopology_of_closed_finite_fibers continuous_projection
    isClosedMap_projection projection_surjective finite_fiber

lemma quotientTopology :
    Specs.SmoothManifolds.Examples.GenusTwoAtlas.quotientTopologyType :=
  ⟨surfaceNonempty, surfaceCompactSpace, surfaceT2Space, surfaceSecondCountableTopology⟩

lemma squareSum_smul (a : ℝ) (x : Euclidean 2) :
    squareSum (a • x) = a ^ 2 * squareSum x := by
  simp [squareSum, Pi.smul_apply, smul_eq_mul, mul_pow]
  ring

lemma isConnected_boundaryCircle : IsConnected boundaryCircle := by
  have : ConnectedSpace (Sphere 1) :=
    circleSphereHomeomorph.surjective.connectedSpace circleSphereHomeomorph.continuous
  let f : Sphere 1 → FlatTorus 2 :=
    fun q => quotientProjection 2 ((1 / 8 : ℝ) • q.val)
  have hg : Continuous (fun q : Sphere 1 => (1 / 8 : ℝ) • q.val) := by fun_prop
  have hf : Continuous f := (quotientProjection_isOpenQuotientMap 2).continuous.comp hg
  have he : range f = boundaryCircle := by
    rw [boundaryCircle_eq]
    ext p
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨(1 / 8 : ℝ) • q.val, by change squareSum _ = _; rw [squareSum_smul, q.property, mul_one], rfl⟩
    · rintro ⟨x, hx, rfl⟩
      have hq : squareSum ((8 : ℝ) • x) = 1 := by
        rw [squareSum_smul, hx]
        norm_num
      refine ⟨⟨(8 : ℝ) • x, hq⟩, ?_⟩
      dsimp [f]
      congr 1
      funext j
      simp
  rw [← he]
  exact isConnected_range hf

/-- A connected frontier cannot separate the complement of a nonempty open
set in a preconnected ambient space. This uses closed covers, so no local
path-connectedness assumption is needed. -/
theorem isPreconnected_compl_of_connected_frontier
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    {s : Set X} (hs : IsOpen s) (hsne : s.Nonempty)
    (hfront : IsPreconnected (frontier s)) : IsPreconnected sᶜ := by
  apply (isPreconnected_iff_subset_of_fully_disjoint_closed hs.isClosed_compl).mpr
  intro u v hu hv hcover hdisj
  have hfc : frontier s ⊆ sᶜ := by
    rw [frontier, hs.interior_eq]
    exact sdiff_subset_compl _ _
  have chooseSide (u v : Set X) (hu : IsClosed u) (hv : IsClosed v)
      (hcover : sᶜ ⊆ u ∪ v) (hdisj : Disjoint u v)
      (hfu : frontier s ⊆ u) : sᶜ ⊆ u := by
    let A := (u ∩ sᶜ) ∪ closure s
    let B := v ∩ sᶜ
    have hA : IsClosed A := (hu.inter hs.isClosed_compl).union isClosed_closure
    have hB : IsClosed B := hv.inter hs.isClosed_compl
    have hab : Disjoint A B := by
      apply disjoint_left.mpr
      intro x hxA hxB
      rcases hxA with hxA | hxA
      · exact disjoint_left.mp hdisj hxA.1 hxB.1
      · have hxf : x ∈ frontier s := ⟨hxA, by simpa [hs.interior_eq] using hxB.2⟩
        exact disjoint_left.mp hdisj (hfu hxf) hxB.1
    have hAB : (univ : Set X) ⊆ A ∪ B := by
      intro x _
      by_cases hxs : x ∈ s
      · exact Or.inl (Or.inr (subset_closure hxs))
      · rcases hcover hxs with hxu | hxv
        · exact Or.inl (Or.inl ⟨hxu, hxs⟩)
        · exact Or.inr ⟨hxv, hxs⟩
    have h := (isPreconnected_iff_subset_of_fully_disjoint_closed isClosed_univ).mp
      isPreconnected_univ A B hA hB hAB hab
    have hleft : (univ : Set X) ⊆ A := by
      rcases h with h | h
      · exact h
      · obtain ⟨x, hx⟩ := hsne
        exact (h (mem_univ x)).2 hx |>.elim
    intro x hx
    rcases hleft (mem_univ x) with hxu | hxcl
    · exact hxu.1
    · exact hfu ⟨hxcl, by simpa [hs.interior_eq] using hx⟩
  have h := (isPreconnected_iff_subset_of_fully_disjoint_closed isClosed_frontier).mp
    hfront u v hu hv (hfc.trans hcover) hdisj
  rcases h with h | h
  · exact Or.inl (chooseSide u v hu hv hcover hdisj h)
  · exact Or.inr (chooseSide v u hv hu (hcover.trans (by rw [union_comm])) hdisj.symm h)

instance puncturedConnectedSpace : ConnectedSpace PuncturedTorus := by
  apply Subtype.connectedSpace
  refine ⟨⟨_, base_notMem_removedDisk⟩, ?_⟩
  apply isPreconnected_compl_of_connected_frontier isOpen_removedDisk _
    isConnected_boundaryCircle.isPreconnected
  exact ⟨quotientProjection 2 0, 0, by norm_num [squareSum], rfl⟩

lemma continuous_sideInclusion (side : Bool) : Continuous (sideInclusion side) :=
  continuous_projection.comp (continuous_const.prodMk continuous_id)

lemma isClosedEmbedding_sideInclusion (side : Bool) :
    IsClosedEmbedding (sideInclusion side) :=
  (continuous_sideInclusion side).isClosedEmbedding (sideInclusion_injective side)

/-- A relatively open part of either copy is open in the quotient as soon as
it avoids the gluing circle. In particular this applies to all bulk charts. -/
lemma isOpen_sideImage {U : Set PuncturedTorus} (hU : IsOpen U)
    (hseam : ∀ p ∈ U, p.val ∉ boundaryCircle) (side : Bool) :
    IsOpen (sideInclusion side '' U) := by
  apply isQuotientMap_quotient_mk'.isOpen_preimage.mp
  change IsOpen (projection ⁻¹' (sideInclusion side '' U))
  have he : projection ⁻¹' (sideInclusion side '' U) =
      {x : Pieces | x.1 = side ∧ x.2 ∈ U} := by
    ext x
    constructor
    · rintro ⟨p, hp, he⟩
      rcases (projection_eq_iff x (side, p)).mp he.symm with he | ⟨_, _, hpseam, _⟩
      · cases he
        exact ⟨rfl, hp⟩
      · exact (hseam p hp hpseam).elim
    · rintro ⟨hx, hp⟩
      refine ⟨x.2, hp, ?_⟩
      change projection (side, x.2) = projection x
      congr 1
      exact Prod.ext hx.symm rfl
  rw [he]
  exact ((isOpen_discrete ({side} : Set Bool)).preimage continuous_fst).inter
    (hU.preimage continuous_snd)

lemma boundaryCircle_subset_compl : boundaryCircle ⊆ removedDiskᶜ := by
  rw [boundaryCircle, frontier, isOpen_removedDisk.interior_eq]
  exact sdiff_subset_compl _ _

instance surfaceConnectedSpace : ConnectedSpace Surface := by
  let p : FlatTorus 2 := quotientProjection 2 ![(1 / 8 : ℝ), 0]
  have hp : p ∈ boundaryCircle := by
    rw [boundaryCircle_eq]
    exact ⟨![(1 / 8 : ℝ), 0], by norm_num [squareSum, Fin.sum_univ_two], rfl⟩
  let x : PuncturedTorus := ⟨p, boundaryCircle_subset_compl hp⟩
  have hrp := (reflect_mem_boundaryCircle p).mpr hp
  let y : PuncturedTorus := ⟨reflectTorus p, boundaryCircle_subset_compl hrp⟩
  have hxy : sideInclusion false x = sideInclusion true y :=
    (projection_eq_iff (false, x) (true, y)).mpr (Or.inr ⟨by change false ≠ true; decide, hp, hrp, rfl⟩)
  have hcover : range (sideInclusion false) ∪ range (sideInclusion true) = univ := by
    apply eq_univ_of_forall
    intro z
    obtain ⟨⟨side, p⟩, rfl⟩ := projection_surjective z
    cases side
    · exact Or.inl ⟨p, rfl⟩
    · exact Or.inr ⟨p, rfl⟩
  apply connectedSpace_iff_univ.mpr
  rw [← hcover]
  exact (isConnected_range (continuous_sideInclusion false)).union
    ⟨sideInclusion false x, ⟨x, rfl⟩, ⟨y, hxy.symm⟩⟩
    (isConnected_range (continuous_sideInclusion true))

lemma connected : Specs.SmoothManifolds.Examples.GenusTwoAtlas.connectedType :=
  surfaceConnectedSpace

/-- The bulk is the complement of the closed coordinate disk. -/
lemma isOpen_bulkRegion :
    IsOpen {p : FlatTorus 2 | p ∉ removedDisk ∧ p ∉ boundaryCircle} := by
  have he : {p : FlatTorus 2 | p ∉ removedDisk ∧ p ∉ boundaryCircle} =
      (closure removedDisk)ᶜ := by
    rw [closure_eq_self_union_frontier]
    ext p
    simp [boundaryCircle]
  rw [he]
  exact isClosed_closure.isOpen_compl

noncomputable def bulkLift (c : ModelChart 2 .euclidean (FlatTorus 2))
    (y : ModelSpace 2 .euclidean) : PuncturedTorus := by
  classical
  exact if h : c.symm y ∉ removedDisk then ⟨c.symm y, h⟩
  else Classical.choice puncturedNonempty

lemma bulkLift_val (c : ModelChart 2 .euclidean (FlatTorus 2))
    (y : ModelSpace 2 .euclidean) (hy : c.symm y ∉ removedDisk) :
    (bulkLift c y).val = c.symm y := by
  simp [bulkLift, hy]

lemma continuousOn_sideInverse (side : Bool) :
    ContinuousOn (Function.invFun (sideInclusion side)) (range (sideInclusion side)) := by
  apply (isClosedEmbedding_sideInclusion side).isEmbedding.isInducing.continuousOn_iff.mpr
  apply continuousOn_id.congr
  rintro z ⟨p, rfl⟩
  change sideInclusion side (Function.invFun (sideInclusion side) (sideInclusion side p)) = sideInclusion side p
  rw [Function.leftInverse_invFun (sideInclusion_injective side) p]

/-- Every torus chart has a genuine restriction on either open bulk. -/
noncomputable def interiorChart (side : Bool)
    (c : ModelChart 2 .euclidean (FlatTorus 2)) : ModelChart 2 .euclidean Surface where
  toFun z := c (Function.invFun (sideInclusion side) z).val
  invFun y := sideInclusion side (bulkLift c y)
  source := sideInclusion side ''
    {p : PuncturedTorus | p.val ∈ c.source ∧ p.val ∉ boundaryCircle}
  target := {y | y ∈ c.target ∧ c.symm y ∉ removedDisk ∧ c.symm y ∉ boundaryCircle}
  map_source' := by
    rintro z ⟨p, ⟨hp, hb⟩, rfl⟩
    rw [Function.leftInverse_invFun (sideInclusion_injective side) p]
    exact ⟨c.map_source hp, by rw [c.left_inv hp]; exact p.property,
      by rw [c.left_inv hp]; exact hb⟩
  map_target' := by
    intro y hy
    refine ⟨bulkLift c y, ?_, rfl⟩
    change (bulkLift c y).val ∈ c.source ∧ (bulkLift c y).val ∉ boundaryCircle
    rw [bulkLift_val c y hy.2.1]
    exact ⟨c.map_target hy.1, hy.2.2⟩
  left_inv' := by
    rintro z ⟨p, ⟨hp, hb⟩, rfl⟩
    rw [Function.leftInverse_invFun (sideInclusion_injective side) p]
    congr 1
    apply Subtype.ext
    rw [bulkLift_val c _ (by rw [c.left_inv hp]; exact p.property), c.left_inv hp]
  right_inv' := by
    intro y hy
    rw [Function.leftInverse_invFun (sideInclusion_injective side), bulkLift_val c y hy.2.1]
    exact c.right_inv hy.1
  open_source := by
    apply isOpen_sideImage _ (fun p hp => hp.2)
    exact (c.open_source.preimage continuous_subtype_val).inter
      (isClosed_frontier.isOpen_compl.preimage continuous_subtype_val)
  open_target := c.isOpen_inter_preimage_symm isOpen_bulkRegion
  continuousOn_toFun := by
    apply c.continuousOn.comp
      (continuous_subtype_val.comp_continuousOn ((continuousOn_sideInverse side).mono ?_))
    · rintro z ⟨p, ⟨hp, _⟩, rfl⟩
      change (Function.invFun (sideInclusion side) (sideInclusion side p)).val ∈ c.source
      rwa [Function.leftInverse_invFun (sideInclusion_injective side) p]
    · rintro z ⟨p, _, rfl⟩
      exact ⟨p, rfl⟩
  continuousOn_invFun := by
    apply (continuous_sideInclusion side).comp_continuousOn
    apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
    apply (c.symm.continuousOn.mono (fun y hy => hy.1)).congr
    intro y hy
    exact bulkLift_val c y hy.2.1

lemma interiorChart_spec (side : Bool)
    (c : ModelChart 2 .euclidean (FlatTorus 2)) :
    IsInteriorChart side c (interiorChart side c) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro p hp hb
    change c (Function.invFun (sideInclusion side) (sideInclusion side p)).val = c p.val
    rw [Function.leftInverse_invFun (sideInclusion_injective side) p]
  · intro y hy
    exact ⟨bulkLift c y, bulkLift_val c y hy.2.1, rfl⟩

lemma interiorCharts : ∀ (side : Bool) (c : ModelChart 2 .euclidean (FlatTorus 2)),
    c ∈ angleAtlas 2 → ∃ e, IsInteriorChart side c e :=
  fun side c _ => ⟨interiorChart side c, interiorChart_spec side c⟩

lemma projection_mem_removedDisk_iff {x : Euclidean 2}
    (hx : x ∈ angleBox 0 (1/3)) :
    quotientProjection 2 x ∈ removedDisk ↔ squareSum x < (1/8 : ℝ)^2 := by
  constructor
  · rintro ⟨y, hy, he⟩
    have hyb : y ∈ angleBox 0 (1/3) := by
      intro j
      simpa using lt_trans (coordinates_small hy j) (by norm_num : (1:ℝ)/8 < 1/3)
    have heq := quotientProjection_injOn_box (0 : Euclidean 2)
      (by norm_num : (1:ℝ)/3 < 1/2) hyb hx he
    simpa [heq] using hy
  · intro h
    exact ⟨x, h, rfl⟩

lemma projection_mem_boundaryCircle_iff {x : Euclidean 2}
    (hx : x ∈ angleBox 0 (1/3)) :
    quotientProjection 2 x ∈ boundaryCircle ↔ squareSum x = (1/8 : ℝ)^2 := by
  rw [boundaryCircle_eq]
  constructor
  · rintro ⟨y, hy, he⟩
    have hyb : y ∈ angleBox 0 (1/3) := by
      intro j
      simpa using lt_of_le_of_lt (coordinates_le hy.le j) (by norm_num : (1:ℝ)/8 < 1/3)
    have heq := quotientProjection_injOn_box (0 : Euclidean 2)
      (by norm_num : (1:ℝ)/3 < 1/2) hyb hx he
    simpa [heq] using hy
  · intro h
    exact ⟨x, h, rfl⟩

lemma reflectCoordinates_eq (x : Euclidean 2) :
    reflectCoordinates x = PolarData.reflect x := by
  ext i
  fin_cases i <;> simp [reflectCoordinates, PolarData.reflect]

lemma radialCoordinates_eq (s t : ℝ) :
    radialCoordinates s t = PolarData.polar ![s, 1/8+|t|] := by
  ext i
  fin_cases i <;> simp [radialCoordinates, anglePoint, PolarData.polar]

lemma squareSum_radialCoordinates (s t : ℝ) :
    squareSum (radialCoordinates s t) = (1/8+|t|)^2 := by
  rw [radialCoordinates_eq, PolarCoordinates.polar_squareSum]
  rfl

lemma radialCoordinates_small (s t : ℝ) (ht : |t| < 1/16) :
    radialCoordinates s t ∈ angleBox 0 (1/3) := by
  have hs := squareSum_radialCoordinates s t
  simp only [squareSum, Fin.sum_univ_two] at hs
  intro j
  have hsmall : |radialCoordinates s t j| < 1/3 := by
    apply abs_lt_of_sq_lt_sq _ (by norm_num)
    fin_cases j <;> dsimp <;>
      nlinarith [sq_nonneg (radialCoordinates s t 0), sq_nonneg (radialCoordinates s t 1),
        abs_nonneg t]
  simpa using hsmall

lemma reflectCoordinates_mem_box {x : Euclidean 2}
    (hx : x ∈ angleBox 0 (1/3)) : reflectCoordinates x ∈ angleBox 0 (1/3) := by
  intro j
  have := hx j
  by_cases h : j = 0 <;> simpa [reflectCoordinates, h] using this

lemma signedRadialTorus_notMem_removedDisk (s t : ℝ) (ht : |t| < 1/16) :
    signedRadialTorus s t ∉ removedDisk := by
  have hsq : ¬ squareSum (radialCoordinates s t) < (1/8 : ℝ)^2 := by
    rw [squareSum_radialCoordinates]
    nlinarith [abs_nonneg t]
  unfold signedRadialTorus
  split_ifs
  · rw [projection_mem_removedDisk_iff (reflectCoordinates_mem_box (radialCoordinates_small s t ht)),
      squareSum_reflect]
    exact hsq
  · rwa [projection_mem_removedDisk_iff (radialCoordinates_small s t ht)]

lemma signedRadialTorus_mem_boundaryCircle_iff (s t : ℝ) (ht : |t| < 1/16) :
    signedRadialTorus s t ∈ boundaryCircle ↔ t = 0 := by
  have hsq : squareSum (radialCoordinates s t) = (1/8 : ℝ)^2 ↔ t = 0 := by
    rw [squareSum_radialCoordinates]
    constructor
    · intro h
      have : |t| = 0 := by nlinarith [abs_nonneg t]
      exact abs_eq_zero.mp this
    · rintro rfl
      norm_num
  unfold signedRadialTorus
  split_ifs
  · rwa [projection_mem_boundaryCircle_iff (reflectCoordinates_mem_box (radialCoordinates_small s t ht)),
      squareSum_reflect]
  · rwa [projection_mem_boundaryCircle_iff (radialCoordinates_small s t ht)]

/-- The total function is specified on the entire collar strip. Values outside
that strip are irrelevant to every seam chart. -/
noncomputable def seamPoint (x : Euclidean 2) : Surface :=
  if h : |x 1| < 1/16 then
    sideInclusion (decide (x 1 < 0))
      ⟨signedRadialTorus (x 0) (x 1), signedRadialTorus_notMem_removedDisk _ _ h⟩
  else sideInclusion false (Classical.choice puncturedNonempty)

lemma seamPoint_eq (x : Euclidean 2) (hx : |x 1| < 1/16) :
    seamPoint x = sideInclusion (decide (x 1 < 0))
      ⟨signedRadialTorus (x 0) (x 1), signedRadialTorus_notMem_removedDisk _ _ hx⟩ := by
  simp only [seamPoint, dite_eq_left hx]

lemma seamRepresents_iff (x : Euclidean 2) (hx : |x 1| < 1/16) (z : Surface) :
    SeamRepresents (x 0) (x 1) z ↔ z = seamPoint x := by
  rw [seamPoint_eq x hx]
  constructor
  · rintro ⟨p, hp, rfl⟩
    congr 1
    exact Subtype.ext hp
  · rintro rfl
    exact ⟨_, rfl, rfl⟩

lemma seam_zero (s : ℝ) :
    sideInclusion false
      ⟨quotientProjection 2 (radialCoordinates s 0),
        by simpa [signedRadialTorus] using signedRadialTorus_notMem_removedDisk s 0 (by norm_num)⟩ =
    sideInclusion true
      ⟨quotientProjection 2 (reflectCoordinates (radialCoordinates s 0)), by
        change quotientProjection 2 (reflectCoordinates (radialCoordinates s 0)) ∉ removedDisk
        rw [← reflect_projection, reflect_mem_removedDisk]
        simpa [signedRadialTorus] using signedRadialTorus_notMem_removedDisk s 0 (by norm_num)⟩ := by
  apply (projection_eq_iff _ _).mpr
  apply Or.inr
  have hb : quotientProjection 2 (radialCoordinates s 0) ∈ boundaryCircle := by
    simpa [signedRadialTorus] using
      (signedRadialTorus_mem_boundaryCircle_iff s 0 (by norm_num)).mpr rfl
  refine ⟨by change false ≠ true; decide, hb, ?_, (reflect_projection _).symm⟩
  change quotientProjection 2 (reflectCoordinates (radialCoordinates s 0)) ∈ boundaryCircle
  rw [← reflect_projection]
  exact (reflect_mem_boundaryCircle _).mpr hb

lemma radialCoordinates_injOn {a δ : ℝ} (hδ : δ < 1/4)
    {s t s' t' : ℝ} (hs : |s-a| < δ) (hs' : |s'-a| < δ)
    (he : radialCoordinates s t = radialCoordinates s' t') : s = s' ∧ |t| = |t'| := by
  rw [radialCoordinates_eq, radialCoordinates_eq] at he
  have hi := PolarCoordinates.injective (a-δ) (a+δ) (by linarith)
  have hx : ![s, 1/8+|t|] ∈ {x : Euclidean 2 | a-δ < x 0 ∧ x 0 < a+δ ∧ 0 < x 1} := by
    have := abs_lt.mp hs
    exact ⟨by dsimp; linarith, by dsimp; linarith, by dsimp; positivity⟩
  have hy : ![s', 1/8+|t'|] ∈ {x : Euclidean 2 | a-δ < x 0 ∧ x 0 < a+δ ∧ 0 < x 1} := by
    have := abs_lt.mp hs'
    exact ⟨by dsimp; linarith, by dsimp; linarith, by dsimp; positivity⟩
  have hv := hi hx hy he
  exact ⟨congrFun hv 0, by have := congrFun hv 1; dsimp at this; linarith⟩

lemma seamPoint_injOn (a δ ε : ℝ) (hδ : δ < 1/4) (hε : ε < 1/16) :
    InjOn seamPoint {x : Euclidean 2 | |x 0-a| < δ ∧ |x 1| < ε} := by
  intro x hx y hy he
  rw [seamPoint_eq x (hx.2.trans hε), seamPoint_eq y (hy.2.trans hε)] at he
  have hg := (projection_eq_iff _ _).mp he
  have hb : decide (x 1 < 0) = decide (y 1 < 0) := by
    rcases hg with h | ⟨hn, hxB, hyB, _⟩
    · exact congrArg Prod.fst h
    · have hxt := (signedRadialTorus_mem_boundaryCircle_iff _ _ (hx.2.trans hε)).mp hxB
      have hyt := (signedRadialTorus_mem_boundaryCircle_iff _ _ (hy.2.trans hε)).mp hyB
      simp [hxt, hyt] at hn
  have htor : signedRadialTorus (x 0) (x 1) = signedRadialTorus (y 0) (y 1) := by
    rcases hg with h | ⟨hn, _⟩
    · exact congrArg (fun p : Pieces => p.2.val) h
    · exact (hn hb).elim
  have hsign : (x 1 < 0) ↔ (y 1 < 0) := by simpa using hb
  have hrad : radialCoordinates (x 0) (x 1) = radialCoordinates (y 0) (y 1) := by
    unfold signedRadialTorus at htor
    by_cases ht : x 1 < 0
    · rw [ite_eq_left ht, ite_eq_left (hsign.mp ht)] at htor
      have hc := quotientProjection_injOn_box (0 : Euclidean 2)
        (by norm_num : (1:ℝ)/3 < 1/2)
        (reflectCoordinates_mem_box (radialCoordinates_small _ _ (hx.2.trans hε)))
        (reflectCoordinates_mem_box (radialCoordinates_small _ _ (hy.2.trans hε))) htor
      simpa only [reflectCoordinates_involutive] using congrArg reflectCoordinates hc
    · rw [ite_eq_right ht, ite_eq_right (by simpa [hsign] using ht)] at htor
      exact quotientProjection_injOn_box (0 : Euclidean 2)
        (by norm_num : (1:ℝ)/3 < 1/2)
        (radialCoordinates_small _ _ (hx.2.trans hε))
        (radialCoordinates_small _ _ (hy.2.trans hε)) htor
  obtain ⟨h0, h1⟩ := radialCoordinates_injOn hδ hx.1 hy.1 hrad
  have ht : x 1 = y 1 := by
    by_cases h : x 1 < 0
    · simpa [abs_of_neg h, abs_of_neg (hsign.mp h)] using h1
    · simpa [abs_of_nonneg (le_of_not_gt h), abs_of_nonneg (le_of_not_gt (hsign.not.mp h))] using h1
  funext i
  fin_cases i
  · exact h0
  · exact ht

noncomputable def collarShiftHomeomorph (side : Bool) : Euclidean 2 ≃ₜ Euclidean 2 where
  toFun x := ![x 0, if side then 1/8-x 1 else 1/8+x 1]
  invFun x := ![x 0, if side then 1/8-x 1 else x 1-1/8]
  left_inv := by
    intro x
    ext i
    fin_cases i <;> cases side <;> simp <;> ring
  right_inv := by
    intro x
    ext i
    fin_cases i <;> cases side <;> simp <;> ring
  continuous_toFun := by cases side <;> simp only [Bool.false_eq_true, Bool.true_eq, ite_false, ite_true] <;> fun_prop
  continuous_invFun := by cases side <;> simp only [Bool.false_eq_true, Bool.true_eq, ite_false, ite_true] <;> fun_prop

noncomputable def halfCoordinates (side : Bool) (x : Euclidean 2) : Euclidean 2 :=
  if side then reflectCoordinates (PolarData.polar (collarShiftHomeomorph side x))
  else PolarData.polar (collarShiftHomeomorph side x)

noncomputable def halfTorus (side : Bool) (x : Euclidean 2) : FlatTorus 2 :=
  quotientProjection 2 (halfCoordinates side x)

lemma continuous_reflectCoordinates : Continuous reflectCoordinates := by
  apply continuous_pi
  intro j
  by_cases h : j = 0 <;> simp only [reflectCoordinates, h, ite_true, ite_false] <;> fun_prop

noncomputable def reflectHomeomorph : Euclidean 2 ≃ₜ Euclidean 2 where
  toFun := reflectCoordinates
  invFun := reflectCoordinates
  left_inv := reflectCoordinates_involutive
  right_inv := reflectCoordinates_involutive
  continuous_toFun := continuous_reflectCoordinates
  continuous_invFun := continuous_reflectCoordinates

lemma continuous_halfCoordinates (side : Bool) : Continuous (halfCoordinates side) := by
  cases side
  · exact PolarCoordinates.smooth.continuous.comp (collarShiftHomeomorph false).continuous
  · exact continuous_reflectCoordinates.comp
      (PolarCoordinates.smooth.continuous.comp (collarShiftHomeomorph true).continuous)

lemma continuous_halfTorus (side : Bool) : Continuous (halfTorus side) :=
  (quotientProjection_isOpenQuotientMap 2).continuous.comp (continuous_halfCoordinates side)

lemma halfCoordinates_squareSum (side : Bool) (x : Euclidean 2) :
    squareSum (halfCoordinates side x) =
      (if side then 1/8-x 1 else 1/8+x 1)^2 := by
  cases side <;> simp [halfCoordinates, squareSum_reflect,
    PolarCoordinates.polar_squareSum, collarShiftHomeomorph]

lemma halfCoordinates_small (side : Bool) (x : Euclidean 2) (hx : |x 1| < 1/16) :
    halfCoordinates side x ∈ angleBox 0 (1/3) := by
  have hs := halfCoordinates_squareSum side x
  have ht := abs_lt.mp hx
  simp only [squareSum, Fin.sum_univ_two] at hs
  intro j
  have hsmall : |halfCoordinates side x j| < 1/3 := by
    apply abs_lt_of_sq_lt_sq _ (by norm_num)
    fin_cases j <;> cases side <;> dsimp at hs ⊢ <;>
      nlinarith [sq_nonneg (halfCoordinates false x 0), sq_nonneg (halfCoordinates false x 1),
        sq_nonneg (halfCoordinates true x 0), sq_nonneg (halfCoordinates true x 1)]
  simpa using hsmall

lemma halfTorus_notMem_removedDisk_iff (side : Bool) (x : Euclidean 2)
    (hx : |x 1| < 1/16) :
    halfTorus side x ∉ removedDisk ↔ (if side then x 1 ≤ 0 else 0 ≤ x 1) := by
  rw [halfTorus, projection_mem_removedDisk_iff (halfCoordinates_small side x hx),
    halfCoordinates_squareSum]
  have ht := abs_lt.mp hx
  cases side <;> dsimp <;> rw [not_lt] <;> constructor <;> intro h <;> nlinarith

lemma isOpen_image_halfTorus (side : Bool) {U : Set (Euclidean 2)}
    (hU : IsOpen U) (hstrip : ∀ x ∈ U, |x 1| < 1/16) :
    IsOpen (halfTorus side '' U) := by
  change IsOpen ((quotientProjection 2 ∘ halfCoordinates side) '' U)
  rw [Set.image_comp]
  apply (quotientProjection_isOpenQuotientMap 2).isOpenMap
  change IsOpen (halfCoordinates side '' U)
  have hpos : ∀ x ∈ (collarShiftHomeomorph side) '' U, 0 < x 1 := by
    rintro _ ⟨x, hx, rfl⟩
    have ht := abs_lt.mp (hstrip x hx)
    cases side
    · change 0 < 1/8+x 1
      linarith
    · change 0 < 1/8-x 1
      linarith
  have hopen := PolarCoordinates.isOpen_image_polar
    ((collarShiftHomeomorph side).isOpenMap U hU) hpos
  cases side
  · change IsOpen ((PolarData.polar ∘ collarShiftHomeomorph false) '' U)
    rw [Set.image_comp]
    exact hopen
  · change IsOpen ((reflectCoordinates ∘ PolarData.polar ∘ collarShiftHomeomorph true) '' U)
    rw [Set.image_comp, Set.image_comp]
    exact reflectHomeomorph.isOpenMap _ hopen

noncomputable def halfLift (side : Bool) (x : Euclidean 2) : PuncturedTorus := by
  classical
  exact if h : halfTorus side x ∉ removedDisk then ⟨halfTorus side x, h⟩
    else Classical.choice puncturedNonempty

lemma halfLift_val (side : Bool) (x : Euclidean 2) (hx : halfTorus side x ∉ removedDisk) :
    (halfLift side x).val = halfTorus side x := by
  simp only [halfLift, dite_eq_left hx]

noncomputable def halfPoint (side : Bool) (x : Euclidean 2) : Surface :=
  sideInclusion side (halfLift side x)

lemma continuousOn_halfPoint (side : Bool) :
    ContinuousOn (halfPoint side)
      {x : Euclidean 2 | |x 1| < 1/16 ∧ (if side then x 1 ≤ 0 else 0 ≤ x 1)} := by
  apply (continuous_sideInclusion side).comp_continuousOn
  apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
  apply (continuous_halfTorus side).continuousOn.congr
  intro x hx
  exact halfLift_val side x ((halfTorus_notMem_removedDisk_iff side x hx.1).mpr hx.2)

lemma signedRadialTorus_eq_half (x : Euclidean 2) :
    signedRadialTorus (x 0) (x 1) = halfTorus (decide (x 1 < 0)) x := by
  by_cases hx : x 1 < 0
  · simp [signedRadialTorus, hx, halfTorus, halfCoordinates, radialCoordinates_eq,
      abs_of_neg hx, collarShiftHomeomorph, sub_eq_add_neg]
  · simp [signedRadialTorus, hx, halfTorus, halfCoordinates, radialCoordinates_eq,
      abs_of_nonneg (le_of_not_gt hx), collarShiftHomeomorph]

lemma seamPoint_eq_half (x : Euclidean 2) (hx : |x 1| < 1/16) :
    seamPoint x = if x 1 < 0 then halfPoint true x else halfPoint false x := by
  rw [seamPoint_eq x hx]
  have hn := signedRadialTorus_notMem_removedDisk (x 0) (x 1) hx
  rw [signedRadialTorus_eq_half] at hn
  have hval := halfLift_val (decide (x 1 < 0)) x hn
  have he : sideInclusion (decide (x 1 < 0))
      ⟨signedRadialTorus (x 0) (x 1), signedRadialTorus_notMem_removedDisk _ _ hx⟩ =
      halfPoint (decide (x 1 < 0)) x := by
    unfold halfPoint
    congr 1
    apply Subtype.ext
    exact (signedRadialTorus_eq_half x).trans hval.symm
  rw [he]
  split_ifs with h <;> simp only [h, decide_true, decide_false]

lemma halfPoint_zero (x : Euclidean 2) (hx : x 1 = 0) :
    halfPoint false x = halfPoint true x := by
  have hp : halfTorus false x = quotientProjection 2 (radialCoordinates (x 0) 0) := by
    simp [halfTorus, halfCoordinates, radialCoordinates_eq, collarShiftHomeomorph, hx]
  have hn : halfTorus true x = quotientProjection 2 (reflectCoordinates (radialCoordinates (x 0) 0)) := by
    simp [halfTorus, halfCoordinates, radialCoordinates_eq, collarShiftHomeomorph, hx]
  have hfalse : halfTorus false x ∉ removedDisk :=
    (halfTorus_notMem_removedDisk_iff false x (by simp [hx])).mpr (by simp [hx])
  have htrue : halfTorus true x ∉ removedDisk :=
    (halfTorus_notMem_removedDisk_iff true x (by simp [hx])).mpr (by simp [hx])
  unfold halfPoint
  convert seam_zero (x 0) using 2
  · exact Subtype.ext ((halfLift_val false x hfalse).trans hp)
  · exact Subtype.ext ((halfLift_val true x htrue).trans hn)

lemma continuousOn_seamPoint :
    ContinuousOn seamPoint {x : Euclidean 2 | |x 1| < 1/16} := by
  have h : ContinuousOn (fun x : Euclidean 2 =>
      if x 1 < 0 then halfPoint true x else halfPoint false x)
      {x | |x 1| < 1/16} := by
    apply ContinuousOn.if
    · intro x hx
      have he : x 1 = 0 := frontier_lt_subset_eq (continuous_apply 1) continuous_const hx.2
      exact (halfPoint_zero x he).symm
    · apply (continuousOn_halfPoint true).mono
      rintro x ⟨hx, hc⟩
      exact ⟨hx, closure_lt_subset_le (continuous_apply 1) continuous_const hc⟩
    · apply (continuousOn_halfPoint false).mono
      rintro x ⟨hx, hc⟩
      have hclosed : IsClosed {x : Euclidean 2 | ¬x 1 < 0} := by
        simpa only [not_lt] using isClosed_le continuous_const (continuous_apply 1)
      rw [hclosed.closure_eq] at hc
      exact ⟨hx, le_of_not_gt hc⟩
  exact h.congr (fun x hx => seamPoint_eq_half x hx)

lemma halfPoint_eq_seamPoint (side : Bool) (x : Euclidean 2)
    (hx : |x 1| < 1/16) (hs : if side then x 1 ≤ 0 else 0 ≤ x 1) :
    halfPoint side x = seamPoint x := by
  rw [seamPoint_eq_half x hx]
  cases side
  · rw [ite_eq_right (not_lt.mpr hs)]
  · by_cases h : x 1 < 0
    · rw [ite_eq_left h]
    · have hz : x 1 = 0 := le_antisymm hs (le_of_not_gt h)
      rw [ite_eq_right h]
      exact (halfPoint_zero x hz).symm

lemma halfTorus_true_zero (x : Euclidean 2) (hx : x 1 = 0) :
    halfTorus true x = reflectTorus (halfTorus false x) := by
  rw [halfTorus, halfTorus, reflect_projection]
  simp [halfCoordinates, collarShiftHomeomorph, hx]

lemma seamPoint_fiber_half (side : Bool) (p : PuncturedTorus) (x : Euclidean 2)
    (hx : |x 1| < 1/16) (he : seamPoint x = sideInclusion side p) :
    p.val = halfTorus side x := by
  rw [seamPoint_eq x hx] at he
  have hg := (projection_eq_iff _ _).mp he
  rcases hg with h | ⟨hb, hB, _, hp⟩
  · have hs : decide (x 1 < 0) = side := congrArg Prod.fst h
    have hv := congrArg (fun z : Pieces => z.2.val) h
    change signedRadialTorus (x 0) (x 1) = p.val at hv
    exact hv.symm.trans (by rw [signedRadialTorus_eq_half, hs])
  · have hz := (signedRadialTorus_mem_boundaryCircle_iff _ _ hx).mp hB
    have hs : side = true := by
      have : false ≠ side := by simpa [hz] using hb
      cases side <;> simp_all
    rw [hs, halfTorus_true_zero x hz]
    change p.val = reflectTorus (signedRadialTorus (x 0) (x 1)) at hp
    rw [signedRadialTorus_eq_half, hz] at hp
    simpa only [lt_self_iff_false, decide_false] using hp

lemma projection_preimage_seamPoint_image {U : Set (Euclidean 2)}
    (hstrip : ∀ x ∈ U, |x 1| < 1/16) :
    projection ⁻¹' (seamPoint '' U) =
      {z : Pieces | z.2.val ∈ halfTorus z.1 '' U} := by
  ext z
  constructor
  · rintro ⟨x, hx, he⟩
    exact ⟨x, hx, (seamPoint_fiber_half z.1 z.2 x (hstrip x hx) he).symm⟩
  · rintro ⟨x, hx, hp⟩
    have hnot : halfTorus z.1 x ∉ removedDisk := by
      rw [hp]
      exact z.2.property
    have hs := (halfTorus_notMem_removedDisk_iff z.1 x (hstrip x hx)).mp hnot
    refine ⟨x, hx, ?_⟩
    rw [← halfPoint_eq_seamPoint z.1 x (hstrip x hx) hs]
    change sideInclusion z.1 (halfLift z.1 x) = sideInclusion z.1 z.2
    congr 1
    exact Subtype.ext ((halfLift_val z.1 x hnot).trans hp)

/-- The signed parametrization is open on every open subset of the strip.
The preimage on either copy is the corresponding ambient open polar image,
restricted to the punctured torus. This includes both seam representatives. -/
lemma isOpen_image_seamPoint {U : Set (Euclidean 2)} (hU : IsOpen U)
    (hstrip : ∀ x ∈ U, |x 1| < 1/16) : IsOpen (seamPoint '' U) := by
  apply isQuotientMap_quotient_mk'.isOpen_preimage.mp
  change IsOpen (projection ⁻¹' (seamPoint '' U))
  rw [projection_preimage_seamPoint_image hstrip]
  have h (side : Bool) : IsOpen {z : Pieces | z.1 = side ∧ z.2.val ∈ halfTorus side '' U} :=
    ((isOpen_discrete ({side} : Set Bool)).preimage continuous_fst).inter
      ((isOpen_image_halfTorus side hU hstrip).preimage (continuous_subtype_val.comp continuous_snd))
  have he : {z : Pieces | z.2.val ∈ halfTorus z.1 '' U} =
      {z : Pieces | z.1 = false ∧ z.2.val ∈ halfTorus false '' U} ∪
      {z : Pieces | z.1 = true ∧ z.2.val ∈ halfTorus true '' U} := by
    ext z
    cases hz : z.1 <;> simp [hz]
  rw [he]
  exact (h false).union (h true)

lemma isOpen_seamDomain (a δ ε : ℝ) :
    IsOpen {x : Euclidean 2 | |x 0-a| < δ ∧ |x 1| < ε} :=
  (isOpen_lt (((continuous_apply 0).sub continuous_const).abs) continuous_const).inter
    (isOpen_lt ((continuous_apply 1).abs) continuous_const)

/-- The inverse seam parametrization, as an open partial homeomorphism on the
quotient topology. Its target is the actual image, not an imposed topology. -/
noncomputable def seamParametrization (a δ ε : ℝ) (hδ : δ < 1/4) (hε : ε < 1/16) :
    OpenPartialHomeomorph (Euclidean 2) Surface :=
  OpenPartialHomeomorph.ofContinuousOpenRestrict
    ((seamPoint_injOn a δ ε hδ hε).toPartialEquiv seamPoint
      {x : Euclidean 2 | |x 0-a| < δ ∧ |x 1| < ε})
    (continuousOn_seamPoint.mono (fun _ hx => hx.2.trans hε))
    (by
      change IsOpenMap (({x : Euclidean 2 | |x 0-a| < δ ∧ |x 1| < ε}).domRestrict seamPoint)
      intro U hU
      change IsOpen ((fun x : {x : Euclidean 2 | |x 0-a| < δ ∧ |x 1| < ε} => seamPoint x.val) '' U)
      rw [← image_image]
      exact isOpen_image_seamPoint ((isOpen_seamDomain a δ ε).isOpenMap_subtype_val U hU)
        (by rintro x ⟨y, _, rfl⟩; exact y.property.2.trans hε))
    (isOpen_seamDomain a δ ε)

noncomputable def seamChart (a δ ε : ℝ) (hδ : δ < 1/4) (hε : ε < 1/16) :
    ModelChart 2 .euclidean Surface :=
  (seamParametrization a δ ε hδ hε).symm.trans
    (euclideanModelHomeomorph 2).toOpenPartialHomeomorph

lemma seamChart_spec (a δ ε : ℝ) (hδ : δ < 1/4) (hε : ε < 1/16) :
    IsSeamChart a δ ε (seamChart a δ ε hδ hε) := by
  let d := seamParametrization a δ ε hδ hε
  have hsource : (seamChart a δ ε hδ hε).source = seamPoint ''
      {x : Euclidean 2 | |x 0-a| < δ ∧ |x 1| < ε} := by
    change d.target ∩ d.symm ⁻¹' univ = _
    simp only [Set.preimage_univ, Set.inter_univ]
    rfl
  have htarget : (seamChart a δ ε hδ hε).target = seamRectangle a δ ε := by
    change univ ∩ (euclideanModelHomeomorph 2).symm ⁻¹' d.source = _
    ext y
    simp only [mem_inter_iff, mem_univ, true_and, mem_preimage]
    rfl
  refine ⟨?_, htarget, ?_⟩
  · rw [hsource]
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, mem_univ _⟩, hx, (seamRepresents_iff x (hx.2.trans hε) _).mpr rfl⟩
    · rintro ⟨y, hy, hz⟩
      exact ⟨y.val, hy, ((seamRepresents_iff y.val (hy.2.trans hε) z).mp hz).symm⟩
  · intro y hy
    rw [htarget] at hy
    apply (seamRepresents_iff y.val (hy.2.trans hε) _).mpr
    rfl

lemma seamCharts : ∀ a δ ε : ℝ, 0 < δ → δ < 1/4 → 0 < ε → ε < 1/16 →
    ∃ e, IsSeamChart a δ ε e :=
  fun a δ ε _ hδ _ hε => ⟨seamChart a δ ε hδ hε, seamChart_spec a δ ε hδ hε⟩

lemma anglePoint_surjective : Function.Surjective anglePoint := by
  intro u
  obtain ⟨p, hp⟩ := (periodicAngleHomeomorph 1).surjective (fun _ => u)
  obtain ⟨x, rfl⟩ := (quotientProjection_isOpenQuotientMap 1).surjective p
  rw [periodicAngleHomeomorph_apply] at hp
  exact ⟨x 0, congrFun hp 0⟩

lemma boundaryCircle_parametrized (p : FlatTorus 2) (hp : p ∈ boundaryCircle) :
    ∃ s : ℝ, quotientProjection 2 (radialCoordinates s 0) = p := by
  rw [boundaryCircle_eq] at hp
  obtain ⟨x, hx, rfl⟩ := hp
  have hsq : squareSum ((8 : ℝ) • x) = 1 := by
    rw [squareSum_smul, hx]
    norm_num
  obtain ⟨s, hs⟩ := anglePoint_surjective ⟨(8 : ℝ) • x, hsq⟩
  refine ⟨s, congrArg (quotientProjection 2) ?_⟩
  funext j
  have hj := congrFun (congrArg Subtype.val hs) j
  simp only [radialCoordinates, abs_zero, add_zero]
  change (1/8 : ℝ) * (anglePoint s).val j = x j
  change (anglePoint s).val j = 8*x j at hj
  rw [hj]
  ring

lemma seamPoint_eq_side (side : Bool) (p : PuncturedTorus) (x : Euclidean 2)
    (hx : |x 1| < 1/16) (hp : halfTorus side x = p.val) :
    seamPoint x = sideInclusion side p := by
  have hnot : halfTorus side x ∉ removedDisk := by rw [hp]; exact p.property
  rw [← halfPoint_eq_seamPoint side x hx
    ((halfTorus_notMem_removedDisk_iff side x hx).mp hnot)]
  unfold halfPoint
  congr 1
  exact Subtype.ext ((halfLift_val side x hnot).trans hp)

lemma seam_covers_boundary (side : Bool) (p : PuncturedTorus) (hp : p.val ∈ boundaryCircle) :
    ∃ s : ℝ, seamPoint ![s,0] = sideInclusion side p := by
  cases side
  · obtain ⟨s, hs⟩ := boundaryCircle_parametrized p.val hp
    refine ⟨s, seamPoint_eq_side false p ![s,0] (by norm_num) ?_⟩
    convert hs using 1
    simp [halfTorus, halfCoordinates, collarShiftHomeomorph, radialCoordinates_eq]
  · obtain ⟨s, hs⟩ := boundaryCircle_parametrized (reflectTorus p.val)
      ((reflect_mem_boundaryCircle p.val).mpr hp)
    refine ⟨s, seamPoint_eq_side true p ![s,0] (by norm_num) ?_⟩
    rw [halfTorus_true_zero _ rfl]
    have he : halfTorus false ![s,0] = reflectTorus p.val := by
      convert hs using 1
      simp [halfTorus, halfCoordinates, collarShiftHomeomorph, radialCoordinates_eq]
    rw [he, reflectTorus_involutive]

lemma constructionAtlas_covers : AtlasData.IsAtlas constructionAtlas := by
  intro z
  obtain ⟨⟨side,p⟩, rfl⟩ := projection_surjective z
  by_cases hp : p.val ∈ boundaryCircle
  · obtain ⟨s, hs⟩ := seam_covers_boundary side p hp
    let e := seamChart s (1/8) (1/32) (by norm_num) (by norm_num)
    have he := seamChart_spec s (1/8) (1/32) (by norm_num) (by norm_num)
    refine ⟨e, Or.inr ⟨s, 1/8, 1/32, by norm_num, by norm_num,
      by norm_num, by norm_num, he⟩, ?_⟩
    rw [he.1]
    refine ⟨⟨![s,0], mem_univ _⟩, ?_, ?_⟩
    · change |s-s| < (1:ℝ)/8 ∧ |(0:ℝ)| < 1/32
      norm_num
    · apply (seamRepresents_iff ![s,0] (by norm_num) _).mpr
      exact hs.symm
  · obtain ⟨c, hc, hpc⟩ := (angleAtlas_isContDiffAtlas 2).1 p.val
    refine ⟨interiorChart side c, Or.inl ⟨side, c, hc, interiorChart_spec side c⟩, ?_⟩
    exact ⟨p, ⟨hpc, hp⟩, rfl⟩

/-- The actual quotient already has a covered Euclidean-model topological
manifold structure, before the compatibility proof for the smooth atlas. -/
noncomputable def topologicalManifold : TopologicalManifold 2 .euclidean Surface :=
  ⟨inferInstance, inferInstance, constructionAtlas, constructionAtlas_covers⟩

/-- In the collar strip the only coordinate ambiguity is one full turn of
angle; the signed radial coordinate is unique, including at the seam. -/
lemma seamPoint_fiber {x y : Euclidean 2} (hx : |x 1| < 1/16) (hy : |y 1| < 1/16)
    (he : seamPoint x = seamPoint y) :
    x 1 = y 1 ∧ ∃ k : ℤ, x 0 = y 0 + k := by
  rw [seamPoint_eq x hx, seamPoint_eq y hy] at he
  have hg := (projection_eq_iff _ _).mp he
  have hb : decide (x 1 < 0) = decide (y 1 < 0) := by
    rcases hg with h | ⟨hn, hxB, hyB, _⟩
    · exact congrArg Prod.fst h
    · have hxt := (signedRadialTorus_mem_boundaryCircle_iff _ _ hx).mp hxB
      have hyt := (signedRadialTorus_mem_boundaryCircle_iff _ _ hy).mp hyB
      simp [hxt, hyt] at hn
  have htor : signedRadialTorus (x 0) (x 1) = signedRadialTorus (y 0) (y 1) := by
    rcases hg with h | ⟨hn, _⟩
    · exact congrArg (fun p : Pieces => p.2.val) h
    · exact (hn hb).elim
  have hsign : (x 1 < 0) ↔ (y 1 < 0) := by simpa using hb
  have hrad : radialCoordinates (x 0) (x 1) = radialCoordinates (y 0) (y 1) := by
    unfold signedRadialTorus at htor
    by_cases ht : x 1 < 0
    · rw [ite_eq_left ht, ite_eq_left (hsign.mp ht)] at htor
      have hc := quotientProjection_injOn_box (0 : Euclidean 2)
        (by norm_num : (1:ℝ)/3 < 1/2)
        (reflectCoordinates_mem_box (radialCoordinates_small _ _ hx))
        (reflectCoordinates_mem_box (radialCoordinates_small _ _ hy)) htor
      simpa only [reflectCoordinates_involutive] using congrArg reflectCoordinates hc
    · rw [ite_eq_right ht, ite_eq_right (hsign.not.mp ht)] at htor
      exact quotientProjection_injOn_box (0 : Euclidean 2)
        (by norm_num : (1:ℝ)/3 < 1/2) (radialCoordinates_small _ _ hx)
        (radialCoordinates_small _ _ hy) htor
  rw [radialCoordinates_eq, radialCoordinates_eq] at hrad
  obtain ⟨hr, hk⟩ := (PolarCoordinates.fibers _ _ (by dsimp; positivity) (by dsimp; positivity)).mp hrad
  have habs : |x 1| = |y 1| := by dsimp at hr; linarith
  refine ⟨?_, hk⟩
  by_cases h : x 1 < 0
  · simpa [abs_of_neg h, abs_of_neg (hsign.mp h)] using habs
  · simpa [abs_of_nonneg (le_of_not_gt h), abs_of_nonneg (le_of_not_gt (hsign.not.mp h))] using habs

lemma seamChart_point {a δ ε : ℝ} {e : ModelChart 2 .euclidean Surface}
    (he : IsSeamChart a δ ε e) (hε : ε < 1/16) {p : Surface} (hp : p ∈ e.source) :
    |(e p).val 1| < 1/16 ∧ seamPoint (e p).val = p := by
  have hy : e p ∈ seamRectangle a δ ε := he.2.1 ▸ e.map_source hp
  refine ⟨hy.2.trans hε, ?_⟩
  have hz := he.2.2 (e p) (e.map_source hp)
  rw [e.left_inv hp] at hz
  exact ((seamRepresents_iff _ (hy.2.trans hε) p).mp hz).symm

/-- Continuous local lifts to R^k with the same projection differ locally by
a constant integer vector. This gives an ambient smooth transition. -/
lemma projectedCoordinates_germ {X : Type*} [TopologicalSpace X] {k : ℕ}
    {e d : ModelChart k .euclidean X}
    (hlift : ∀ q, q ∈ e.source → q ∈ d.source →
      quotientProjection k (e q).val = quotientProjection k (d q).val)
    (p : X) (hp : p ∈ e.source) (hp' : p ∈ d.source) :
    ChartContDiffAt (⊤ : ℕ∞) e d id p := by
  let u := (e p).val
  let v := (d p).val
  let F : Euclidean k → Euclidean k := fun y => y + (v-u)
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := by dsimp [F]; fun_prop
  have hecont := continuous_subtype_val.continuousAt.comp (e.continuousAt hp)
  have hdcont := continuous_subtype_val.continuousAt.comp (d.continuousAt hp')
  have hFcont : ContinuousAt (fun q => F (e q).val) p := hF.continuous.continuousAt.comp hecont
  have hFp : F (e p).val = v := by dsimp [F,u,v]; abel
  have hproj : quotientProjection k (v-u) = 0 := by
    funext j
    change (v j : AddCircle (1:ℝ)) - (u j : AddCircle (1:ℝ)) = 0
    exact sub_eq_zero.mpr (congrFun (hlift p hp hp').symm j)
  refine ⟨univ, isOpen_univ, mem_univ _, F, hF.contDiffOn, ?_⟩
  have hbox := (isOpen_angleBox v (1/4)).mem_nhds (mem_angleBox_center v (by norm_num))
  have hFbox : ∀ᶠ q in 𝓝 p, F (e q).val ∈ angleBox v (1/4) :=
    hFcont.preimage_mem_nhds (by simpa [hFp] using hbox)
  have hdbox : ∀ᶠ q in 𝓝 p, (d q).val ∈ angleBox v (1/4) := hdcont.preimage_mem_nhds hbox
  filter_upwards [e.open_source.mem_nhds hp, d.open_source.mem_nhds hp', hFbox, hdbox]
    with q hqe hqd hqF hqdv
  apply quotientProjection_injOn_box v (by norm_num : (1:ℝ)/4 < 1/2) hqF hqdv
  calc
    quotientProjection k (F (e q).val) = quotientProjection k (e q).val := by
      funext j
      change ((e q).val j : AddCircle (1:ℝ)) + ((v j-u j : ℝ) : AddCircle (1:ℝ)) = _
      have hz := congrFun hproj j
      change ((v j-u j : ℝ) : AddCircle (1:ℝ)) = 0 at hz
      rw [hz, add_zero]
      rfl
    _ = _ := hlift q hqe hqd

lemma seamCharts_compatible {e d : ModelChart 2 .euclidean Surface}
    (he : e ∈ seamAtlas) (hd : d ∈ seamAtlas) :
    AtlasData.ContDiffCompatible (⊤ : ℕ∞) e d := by
  rcases he with ⟨a,δ,ε,_,_,_,hε,he⟩
  rcases hd with ⟨b,δ',ε',_,_,_,hε',hd⟩
  have hlift : ∀ q, q ∈ e.source → q ∈ d.source →
      quotientProjection 2 (e q).val = quotientProjection 2 (d q).val := by
    intro q hqe hqd
    obtain ⟨heS, heq⟩ := seamChart_point he hε hqe
    obtain ⟨hdS, hdq⟩ := seamChart_point hd hε' hqd
    obtain ⟨ht,k,hk⟩ := seamPoint_fiber heS hdS (heq.trans hdq.symm)
    apply (quotientProjection_fiber 2 _ _).mpr
    refine ⟨![k,0], ?_⟩
    intro j
    fin_cases j
    · exact hk
    · simpa using ht
  exact contDiffCompatible_of_germs (projectedCoordinates_germ hlift)
    (projectedCoordinates_germ (fun q hqd hqe => (hlift q hqe hqd).symm))

lemma interiorCharts_projection {side side' : Bool}
    {c c' : ModelChart 2 .euclidean (FlatTorus 2)}
    {e d : ModelChart 2 .euclidean Surface}
    (hc : c ∈ angleAtlas 2) (hc' : c' ∈ angleAtlas 2)
    (he : IsInteriorChart side c e) (hd : IsInteriorChart side' c' d)
    {q : Surface} (hqe : q ∈ e.source) (hqd : q ∈ d.source) :
    quotientProjection 2 (e q).val = quotientProjection 2 (d q).val := by
  rw [he.1] at hqe
  rw [hd.1] at hqd
  obtain ⟨p, ⟨hp,hpB⟩, hpeq⟩ := hqe
  obtain ⟨p', ⟨hp',hpB'⟩, hp'eq⟩ := hqd
  have hg := (projection_eq_iff _ _).mp (hpeq.trans hp'eq.symm)
  have hv : p.val = p'.val := by
    rcases hg with hg | ⟨_, hB, _⟩
    · exact congrArg (fun z : Pieces => z.2.val) hg
    · exact (hpB hB).elim
  rw [← hpeq, he.2.2.1 p hp hpB]
  rw [hpeq, ← hp'eq, hd.2.2.1 p' hp' hpB']
  rcases hc with ⟨_,_,_,_,hc⟩
  rcases hc' with ⟨_,_,_,_,hc'⟩
  exact (angleChart_projection hc hp).trans (hv.trans (angleChart_projection hc' hp').symm)

lemma interiorCharts_compatible {e d : ModelChart 2 .euclidean Surface}
    (he : e ∈ bulkAtlas) (hd : d ∈ bulkAtlas) :
    AtlasData.ContDiffCompatible (⊤ : ℕ∞) e d := by
  rcases he with ⟨side,c,hc,he⟩
  rcases hd with ⟨side',c',hc',hd⟩
  exact contDiffCompatible_of_germs
    (projectedCoordinates_germ (fun _ hqe hqd => interiorCharts_projection hc hc' he hd hqe hqd))
    (projectedCoordinates_germ (fun _ hqd hqe => interiorCharts_projection hc' hc hd he hqd hqe))

lemma smooth_halfCoordinates (side : Bool) : ContDiff ℝ (⊤ : ℕ∞) (halfCoordinates side) := by
  cases side
  · exact PolarCoordinates.smooth_positiveCollar
  · have he : halfCoordinates true = PolarData.negativeCollar := by
      funext x
      change reflectCoordinates (PolarData.polar ![x 0,1/8-x 1]) = _
      rw [reflectCoordinates_eq]
      rfl
    rw [he]
    exact PolarCoordinates.smooth_negativeCollar

lemma halfCoordinates_det_ne_zero (side : Bool) (x : Euclidean 2)
    (hx : |x 1| < 1/16) : (fderiv ℝ (halfCoordinates side) x).det ≠ 0 := by
  have ht := abs_lt.mp hx
  have hneg : (fderiv ℝ (halfCoordinates side) x).det < 0 := by
    cases side
    · change (fderiv ℝ PolarData.positiveCollar x).det < 0
      rw [PolarCoordinates.positiveCollar_jacobian]
      have hp : 0 < (1/8 : ℝ)+x 1 := by linarith
      nlinarith [Real.pi_pos]
    · have he : halfCoordinates true = PolarData.negativeCollar := by
        funext y
        change reflectCoordinates (PolarData.polar ![y 0,1/8-y 1]) = _
        rw [reflectCoordinates_eq]
        rfl
      rw [he, PolarCoordinates.negativeCollar_jacobian]
      have hp : 0 < (1/8 : ℝ)-x 1 := by linarith
      nlinarith [Real.pi_pos]
  exact ne_of_lt hneg

noncomputable def halfDerivativeEquiv (side : Bool) (x : Euclidean 2) (hx : |x 1| < 1/16) :
    Euclidean 2 ≃L[ℝ] Euclidean 2 :=
  (LinearMap.equivOfIsUnitDet (f := (fderiv ℝ (halfCoordinates side) x).toLinearMap)
    (isUnit_iff_ne_zero.mpr (halfCoordinates_det_ne_zero side x hx))).toContinuousLinearEquiv

lemma hasFDerivAt_halfCoordinates (side : Bool) (x : Euclidean 2) (hx : |x 1| < 1/16) :
    HasFDerivAt (halfCoordinates side) (halfDerivativeEquiv side x hx : Euclidean 2 →L[ℝ] Euclidean 2) x := by
  have hd := ((smooth_halfCoordinates side).differentiable (by simp) x).hasFDerivAt
  convert hd using 1
  ext y i
  simp [halfDerivativeEquiv]

lemma halfCoordinates_localInverse (side : Bool) (x : Euclidean 2) (hx : |x 1| < 1/16) :
    ∃ e : OpenPartialHomeomorph (Euclidean 2) (Euclidean 2),
      x ∈ e.source ∧ (∀ y, e y = halfCoordinates side y) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target := by
  let e := (smooth_halfCoordinates side).contDiffAt.toOpenPartialHomeomorph
    (halfCoordinates side) (hasFDerivAt_halfCoordinates side x hx) (by simp)
  let U : Set (Euclidean 2) := {y | |y 1| < 1/16}
  have hU : IsOpen U := isOpen_lt ((continuous_apply 1).abs) continuous_const
  let d := e.restr U
  have hd : ∀ y, d y = halfCoordinates side y := fun _ => rfl
  have hpos : ∀ y ∈ d.source, |y 1| < 1/16 :=
    fun y hy => show y ∈ U from interior_subset hy.2
  refine ⟨d, ?_, hd, ?_⟩
  · change x ∈ e.source ∩ interior U
    rw [hU.interior_eq]
    exact ⟨(smooth_halfCoordinates side).contDiffAt.mem_toOpenPartialHomeomorph_source _ _, hx⟩
  · intro y hy
    apply ContDiffAt.contDiffWithinAt
    apply d.contDiffAt_symm hy (f₀' := halfDerivativeEquiv side (d.symm y) (hpos _ (d.map_target hy)))
    · rw [show (d : Euclidean 2 → Euclidean 2) = halfCoordinates side from funext hd]
      exact hasFDerivAt_halfCoordinates side _ _
    · rw [show (d : Euclidean 2 → Euclidean 2) = halfCoordinates side from funext hd]
      exact (smooth_halfCoordinates side).contDiffAt

/-- A smooth local diffeomorphism between two continuous coordinate lifts
induces smooth chart transitions in both directions. -/
lemma coordinateGerms_of_localDiffeomorphism
    {e d : ModelChart 2 .euclidean Surface} {A : Euclidean 2 → Euclidean 2}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) {p : Surface} (hp : p ∈ e.source) (hp' : p ∈ d.source)
    (hproj : ∀ᶠ q in 𝓝 p, quotientProjection 2 (A (e q).val) = quotientProjection 2 (d q).val)
    (hinv : ∃ E : OpenPartialHomeomorph (Euclidean 2) (Euclidean 2),
      (e p).val ∈ E.source ∧ (∀ y, E y = A y) ∧ ContDiffOn ℝ (⊤ : ℕ∞) E.symm E.target) :
    ChartContDiffAt (⊤ : ℕ∞) e d id p ∧ ChartContDiffAt (⊤ : ℕ∞) d e id p := by
  let u := (e p).val
  let v := (d p).val
  let k := v-A u
  let F : Euclidean 2 → Euclidean 2 := fun y => A y+k
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := hA.add contDiff_const
  have hecont := continuous_subtype_val.continuousAt.comp (e.continuousAt hp)
  have hdcont := continuous_subtype_val.continuousAt.comp (d.continuousAt hp')
  have hFcont : ContinuousAt (fun q => F (e q).val) p := hF.continuous.continuousAt.comp hecont
  have hFp : F (e p).val = v := by dsimp [F,k,u,v]; abel
  have hzero : quotientProjection 2 k = 0 := by
    funext j
    change (v j : AddCircle (1:ℝ)) - (A u j : AddCircle (1:ℝ)) = 0
    have hprojAt : quotientProjection 2 (A u) = quotientProjection 2 v :=
      Filter.EventuallyEq.eq_of_nhds hproj
    exact sub_eq_zero.mpr (congrFun hprojAt.symm j)
  have hbox := (isOpen_angleBox v (1/4)).mem_nhds (mem_angleBox_center v (by norm_num))
  have hFbox : ∀ᶠ q in 𝓝 p, F (e q).val ∈ angleBox v (1/4) :=
    hFcont.preimage_mem_nhds (by simpa [hFp] using hbox)
  have hdbox : ∀ᶠ q in 𝓝 p, (d q).val ∈ angleBox v (1/4) := hdcont.preimage_mem_nhds hbox
  have hloc : (fun q => F (e q).val) =ᶠ[𝓝 p] (fun q => (d q).val) := by
    filter_upwards [hproj, hFbox, hdbox] with q hq hqF hqd
    apply quotientProjection_injOn_box v (by norm_num : (1:ℝ)/4 < 1/2) hqF hqd
    calc
      quotientProjection 2 (F (e q).val) = quotientProjection 2 (A (e q).val) := by
        funext j
        change (A (e q).val j : AddCircle (1:ℝ)) + (k j : AddCircle (1:ℝ)) = _
        have hz := congrFun hzero j
        change (k j : AddCircle (1:ℝ)) = 0 at hz
        rw [hz, add_zero]
        rfl
      _ = _ := hq
  refine ⟨⟨univ, isOpen_univ, mem_univ _, F, hF.contDiffOn, hloc⟩, ?_⟩
  obtain ⟨E, hu, hE, hEinv⟩ := hinv
  let U : Set (Euclidean 2) := {y | y-k ∈ E.target}
  have hU : IsOpen U := E.open_target.preimage (continuous_id.sub continuous_const)
  have hv : v ∈ U := by
    change v-k ∈ E.target
    have hvk : v-k = A u := by dsimp [k]; abel
    rw [hvk, ← hE]
    exact E.map_source hu
  refine ⟨U, hU, hv, fun y => E.symm (y-k),
    hEinv.comp (contDiffOn_id.sub contDiffOn_const) (fun _ hy => hy), ?_⟩
  have hnear : ∀ᶠ q in 𝓝 p, (e q).val ∈ E.source := hecont.preimage_mem_nhds (E.open_source.mem_nhds hu)
  filter_upwards [hloc, hnear] with q hq hqE
  have hsub : (d q).val-k = A (e q).val := by rw [← hq]; dsimp [F]; abel
  rw [hsub, ← hE, E.left_inv hqE]
  rfl

lemma interior_seam_projection {side : Bool}
    {c : ModelChart 2 .euclidean (FlatTorus 2)} {e d : ModelChart 2 .euclidean Surface}
    {a δ ε : ℝ} (hc : c ∈ angleAtlas 2)
    (he : IsInteriorChart side c e) (hd : IsSeamChart a δ ε d) (hε : ε < 1/16)
    {q : Surface} (hqe : q ∈ e.source) (hqd : q ∈ d.source) :
    quotientProjection 2 (halfCoordinates side (d q).val) = quotientProjection 2 (e q).val := by
  obtain ⟨hstrip, hpoint⟩ := seamChart_point hd hε hqd
  rw [he.1] at hqe
  obtain ⟨p, ⟨hp,hpB⟩, hpq⟩ := hqe
  have htor := seamPoint_fiber_half side p (d q).val hstrip (hpoint.trans hpq.symm)
  have hecoords : e q = c p.val := by
    rw [← hpq]
    exact he.2.2.1 p hp hpB
  rw [hecoords]
  rcases hc with ⟨_,_,_,_,hc⟩
  exact htor.symm.trans (angleChart_projection hc hp).symm

lemma interior_seam_germs {side : Bool}
    {c : ModelChart 2 .euclidean (FlatTorus 2)} {e d : ModelChart 2 .euclidean Surface}
    {a δ ε : ℝ} (hc : c ∈ angleAtlas 2)
    (he : IsInteriorChart side c e) (hd : IsSeamChart a δ ε d) (hε : ε < 1/16)
    (p : Surface) (hp : p ∈ e.source) (hp' : p ∈ d.source) :
    ChartContDiffAt (⊤ : ℕ∞) d e id p ∧ ChartContDiffAt (⊤ : ℕ∞) e d id p := by
  apply coordinateGerms_of_localDiffeomorphism (smooth_halfCoordinates side) hp' hp
  · filter_upwards [e.open_source.mem_nhds hp, d.open_source.mem_nhds hp'] with q hqe hqd
    exact interior_seam_projection hc he hd hε hqe hqd
  · exact halfCoordinates_localInverse side (d p).val (seamChart_point hd hε hp').1

lemma interior_seam_compatible {e d : ModelChart 2 .euclidean Surface}
    (he : e ∈ bulkAtlas) (hd : d ∈ seamAtlas) :
    AtlasData.ContDiffCompatible (⊤ : ℕ∞) e d := by
  rcases he with ⟨side,c,hc,he⟩
  rcases hd with ⟨a,δ,ε,_,_,_,hε,hd⟩
  exact contDiffCompatible_of_germs
    (fun p hp hp' => (interior_seam_germs hc he hd hε p hp hp').2)
    (fun p hp' hp => (interior_seam_germs hc he hd hε p hp hp').1)

lemma constructionAtlas_isContDiffAtlas :
    AtlasData.IsContDiffAtlas (⊤ : ℕ∞) constructionAtlas := by
  refine ⟨constructionAtlas_covers, ?_⟩
  intro e he d hd
  rcases he with he | he <;> rcases hd with hd | hd
  · exact interiorCharts_compatible he hd
  · exact interior_seam_compatible he hd
  · exact contDiffCompatible_symm (interior_seam_compatible hd he)
  · exact seamCharts_compatible he hd

theorem countableChartCover :
    Specs.SmoothManifolds.Examples.GenusTwoAtlas.countableChartCoverType := by
  have hcover : (univ : Set Surface) ⊆ ⋃ c ∈ constructionAtlas, c.source := by
    intro p _
    obtain ⟨c, hc, hp⟩ := constructionAtlas_covers p
    exact mem_iUnion.mpr ⟨c, mem_iUnion.mpr ⟨hc, hp⟩⟩
  obtain ⟨C, hCA, hC, hcover⟩ := isCompact_univ.elim_finite_subcover_image
    (fun (c : ModelChart 2 .euclidean Surface) (_ : c ∈ constructionAtlas) => c.open_source) hcover
  refine ⟨C, hC.countable, hCA, ?_⟩
  intro p
  obtain ⟨c, hc⟩ := mem_iUnion.mp (hcover (mem_univ p))
  obtain ⟨hcC, hp⟩ := mem_iUnion.mp hc
  exact ⟨c, hcC, hp⟩

/-- The fixed smooth structure on the concrete connected sum. Downstream
orientation and cohomology constructions use this same structure. -/
noncomputable def smoothManifold : AtlasData.SmoothManifold 2 .euclidean Surface where
  topologicalManifold := topologicalManifold
  smoothStructure := ⟨AtlasData.maximalExtension (⊤ : ℕ∞) constructionAtlas,
    maximalExtension_isMaximal constructionAtlas_isContDiffAtlas⟩

@[simp] theorem smoothManifold_generatingAtlas :
    smoothManifold.topologicalManifold.atlas = constructionAtlas := rfl

@[simp] theorem smoothManifold_maximalAtlas :
    smoothManifold.smoothStructure.val = AtlasData.maximalExtension (⊤ : ℕ∞) constructionAtlas := rfl

@[simp] theorem smoothManifold_boundary :
    BoundaryData.intrinsicBoundary smoothManifold = ∅ :=
  intrinsicBoundary_euclidean smoothManifold

/-- All prescribed charts and the maximal smooth structure are realized on
the original quotient topology. No orientation is included in this data. -/
theorem smoothConstruction : Specs.SmoothManifolds.Examples.GenusTwoAtlas.smoothConstructionType :=
  ⟨interiorCharts, seamCharts, constructionAtlas_isContDiffAtlas,
    smoothManifold, smoothManifold_generatingAtlas, smoothManifold_maximalAtlas,
    smoothManifold_boundary⟩

theorem fullConstruction : Specs.SmoothManifolds.Examples.GenusTwoAtlas.fullConstructionType :=
  ⟨diskGeometry, exactFibers, quotientTopology, connected, smoothConstruction⟩

end SmoothManifolds.GenusTwoAtlas

namespace SmoothManifolds
/-- The specific connected sum, retained as the shared surface object. -/
abbrev GenusTwoSurface := GenusTwoData.Surface
end SmoothManifolds
