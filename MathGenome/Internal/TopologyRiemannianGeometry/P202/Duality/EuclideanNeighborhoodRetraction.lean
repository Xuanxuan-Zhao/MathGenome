import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Duality.EuclideanNeighborhoodRetraction
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.Topology.PartitionOfUnity

/-! A shrinking-cover proof of paper.tex, Lemma `lem:p202-enr`.
The independent statement in Specs uses classical local contractibility.
The construction below proves the full result, including the empty set and
zero-dimensional ambient space. -/

noncomputable section
open Set Topology Metric ContinuousMap

namespace P202.Duality

/-- The empty set is a retract of its empty open neighborhood. -/
theorem empty_hasOpenNeighborhoodRetraction (E : Type*) [TopologicalSpace E] :
    HasOpenNeighborhoodRetraction (∅ : Set E) := by
  refine ⟨∅, isOpen_empty, subset_rfl, ContinuousMap.id _, ?_⟩
  intro x
  rfl

/-- Any nonempty set with at most one point is a retract of the whole space. -/
theorem subsingleton_hasOpenNeighborhoodRetraction {E : Type*} [TopologicalSpace E]
    (K : Set E) [Subsingleton K] (hK : K.Nonempty) : HasOpenNeighborhoodRetraction K := by
  obtain ⟨x, hx⟩ := hK
  exact ⟨univ, isOpen_univ, subset_univ K, ContinuousMap.const _ ⟨x, hx⟩,
    fun _ => Subsingleton.elim _ _⟩

/-- Dimension zero needs no compactness or local contractibility hypothesis. -/
theorem zero_dimensional_hasOpenNeighborhoodRetraction
    (K : Set (EuclideanAmbient 0)) : HasOpenNeighborhoodRetraction K := by
  classical
  by_cases hK : K.Nonempty
  · exact subsingleton_hasOpenNeighborhoodRetraction K hK
  · rw [Set.not_nonempty_iff_eq_empty.mp hK]
    exact empty_hasOpenNeighborhoodRetraction _

/-- A nullhomotopic inclusion can be restricted to an open neighborhood.
This uses classical local contractibility, not a contractible-neighborhood basis. -/
theorem exists_open_nullhomotopic_neighborhood {X : Type*} [TopologicalSpace X]
    (hLC : LocallyContractibleSpace X) (x : X) (U : Set X) (hU : U ∈ 𝓝 x) :
    ∃ (V : Set X) (_ : IsOpen V) (_ : x ∈ V) (hVU : V ⊆ U),
      (ContinuousMap.inclusion hVU).Nullhomotopic := by
  obtain ⟨W, hWU, hW, hnull⟩ := hLC x U hU
  obtain ⟨V, hVW, hVopen, hxV⟩ := mem_nhds_iff.mp hW
  refine ⟨V, hVopen, hxV, hVW.trans hWU, ?_⟩
  exact hnull.comp_left (ContinuousMap.inclusion hVW)

/-- Compactness makes the small-nullhomotopy property uniform. Every nonempty
subset with pairwise distances less than `δ` contracts inside a ball of the
prescribed radius. This is the compactness step preceding the small-extension
argument in paper.tex, lines 2403–2412. -/
theorem uniform_small_nullhomotopic_inclusion {X : Type*} [MetricSpace X]
    [CompactSpace X] (hLC : LocallyContractibleSpace X) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ (A : Set X), A.Nonempty →
      (∀ a ∈ A, ∀ b ∈ A, dist a b < δ) →
      ∃ (y : X) (hA : A ⊆ ball y ε), (ContinuousMap.inclusion hA).Nullhomotopic := by
  classical
  have hlocal : ∀ y : X, ∃ (V : Set X) (_ : IsOpen V) (_ : y ∈ V)
      (hV : V ⊆ ball y ε), (ContinuousMap.inclusion hV).Nullhomotopic :=
    fun y => exists_open_nullhomotopic_neighborhood hLC y (ball y ε)
      (ball_mem_nhds y hε)
  choose V hVopen hyV hVball hVnull using hlocal
  obtain ⟨δ, hδ, hcover⟩ := lebesgue_number_lemma_of_metric
    (s := (univ : Set X)) isCompact_univ hVopen (by
      intro x _
      exact mem_iUnion.mpr ⟨x, hyV x⟩)
  refine ⟨δ, hδ, ?_⟩
  intro A hA hdist
  obtain ⟨a, ha⟩ := hA
  obtain ⟨y, hy⟩ := hcover a (mem_univ a)
  have hAV : A ⊆ V y := fun b hb => hy (hdist b hb a ha)
  refine ⟨y, hAV.trans (hVball y), ?_⟩
  exact (hVnull y).comp_left (ContinuousMap.inclusion hAV)

section RadialCone

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The cone parametrization of the closed unit ball, with the cone point at
parameter one. -/
def sphereConeProjection (p : unitInterval × sphere (0 : E) 1) :
    closedBall (0 : E) 1 :=
  ⟨(1 - (p.1 : ℝ)) • p.2.1, by
    have hx : ‖p.2.1‖ = 1 := by
      simpa only [mem_sphere, dist_zero_right] using p.2.2
    rw [mem_closedBall_zero_iff, norm_smul_of_nonneg (sub_nonneg.mpr p.1.2.2), hx, mul_one]
    exact sub_le_self _ p.1.2.1⟩

theorem continuous_sphereConeProjection : Continuous (sphereConeProjection (E := E)) := by
  apply Continuous.subtype_mk
  exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
    (continuous_subtype_val.comp continuous_snd)

@[simp]
theorem norm_sphereConeProjection (p : unitInterval × sphere (0 : E) 1) :
    ‖(sphereConeProjection p).1‖ = 1 - (p.1 : ℝ) := by
  have hx : ‖p.2.1‖ = 1 := by
    simpa only [mem_sphere, dist_zero_right] using p.2.2
  change ‖(1 - (p.1 : ℝ)) • p.2.1‖ = _
  rw [norm_smul_of_nonneg (sub_nonneg.mpr p.1.2.2), hx, mul_one]

/-- In positive dimension the cone parametrization is onto, including its
center. -/
theorem sphereConeProjection_surjective [Nontrivial E] :
    Function.Surjective (sphereConeProjection (E := E)) := by
  intro b
  have hb : ‖b.1‖ ≤ 1 := by
    simpa only [mem_closedBall, dist_zero_right] using b.2
  by_cases hzero : b.1 = 0
  · obtain ⟨v, hv⟩ := exists_norm_eq E (show (0 : ℝ) ≤ 1 by norm_num)
    refine ⟨(1, ⟨v, by simpa only [mem_sphere, dist_zero_right] using hv⟩), ?_⟩
    apply Subtype.ext
    simpa [sphereConeProjection] using hzero.symm
  · refine ⟨(⟨1 - ‖b.1‖, ⟨sub_nonneg.mpr hb, sub_le_self _ (norm_nonneg _)⟩⟩,
      ⟨‖b.1‖⁻¹ • b.1, ?_⟩), ?_⟩
    · simpa [mem_sphere, dist_zero_right] using
        (norm_smul_inv_norm (𝕜 := ℝ) hzero)
    · apply Subtype.ext
      change (1 - (1 - ‖b.1‖)) • (‖b.1‖⁻¹ • b.1) = b.1
      rw [sub_sub_cancel, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hzero), one_smul]

/-- Compactness of the sphere makes the radial cone parametrization a quotient
map in a proper normed space. -/
theorem sphereConeProjection_isQuotientMap [ProperSpace E] [Nontrivial E] :
    IsQuotientMap (sphereConeProjection (E := E)) :=
  continuous_sphereConeProjection.isClosedMap.isQuotientMap
    continuous_sphereConeProjection sphereConeProjection_surjective

/-- A nullhomotopy on a unit sphere gives an extension over the closed ball.
The proof descends the homotopy through the compact radial cone quotient. -/
theorem nullhomotopic_extends_closedBall [ProperSpace E] [Nontrivial E]
    {Y : Type*} [TopologicalSpace Y] (f : C(sphere (0 : E) 1, Y))
    (hf : f.Nullhomotopic) :
    ∃ F : C(closedBall (0 : E) 1, Y),
      ∀ x : sphere (0 : E) 1, F ⟨x.1, sphere_subset_closedBall x.2⟩ = f x := by
  classical
  obtain ⟨y, ⟨H⟩⟩ := hf
  have hH : ∀ (p q : unitInterval × sphere (0 : E) 1),
      sphereConeProjection p = sphereConeProjection q → H p = H q := by
    rintro ⟨t, x⟩ ⟨s, z⟩ heq
    have hnorm := congrArg (fun b : closedBall (0 : E) 1 => ‖b.1‖) heq
    rw [norm_sphereConeProjection, norm_sphereConeProjection] at hnorm
    have hts : t = s := Subtype.ext (by linarith)
    subst s
    by_cases ht : t = 1
    · subst t
      simp only [Homotopy.apply_one, ContinuousMap.const_apply]
    · have hscalar : 1 - (t : ℝ) ≠ 0 := by
        intro h
        apply ht
        apply Subtype.ext
        change (t : ℝ) = 1
        linarith
      have hxz : x = z := Subtype.ext
        (smul_right_injective E hscalar (congrArg Subtype.val heq))
      subst z
      rfl
  let g : closedBall (0 : E) 1 → Y :=
    fun b => H (Function.surjInv sphereConeProjection_surjective b)
  have hgcomp : g ∘ sphereConeProjection = H := by
    funext p
    exact hH _ p (Function.surjInv_eq sphereConeProjection_surjective _)
  have hg : Continuous g := sphereConeProjection_isQuotientMap.continuous_iff.mpr (by
    rw [hgcomp]
    exact H.continuous)
  refine ⟨⟨g, hg⟩, ?_⟩
  intro x
  have hx : sphereConeProjection (0, x) =
      (⟨x.1, sphere_subset_closedBall x.2⟩ : closedBall (0 : E) 1) := by
    apply Subtype.ext
    simp [sphereConeProjection]
  change g _ = f x
  rw [← hx]
  exact (congrFun hgcomp (0, x)).trans (H.apply_zero x)

end RadialCone

/-- Uniform small extension over closed Euclidean balls, in every positive
ambient dimension. The bound on the image is independent of that dimension.
This implements the small-extension input to the source's nerve induction,
using round balls in place of geometrically parametrized simplices. -/
theorem uniform_small_ball_extension {X : Type*} [MetricSpace X] [CompactSpace X]
    (hLC : LocallyContractibleSpace X) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ (n : ℕ) (f : C(sphere (0 : EuclideanAmbient (n + 1)) 1, X)),
      (∀ a b, dist (f a) (f b) < δ) →
      ∃ F : C(closedBall (0 : EuclideanAmbient (n + 1)) 1, X),
        (∀ x : sphere (0 : EuclideanAmbient (n + 1)) 1,
          F ⟨x.1, sphere_subset_closedBall x.2⟩ = f x) ∧
        (∀ a b, dist (F a) (F b) ≤ ε) := by
  obtain ⟨δ, hδ, hsmall⟩ := uniform_small_nullhomotopic_inclusion hLC (ε / 3) (by linarith)
  refine ⟨δ, hδ, ?_⟩
  intro n f hdist
  obtain ⟨v, hv⟩ := exists_norm_eq (EuclideanAmbient (n + 1)) (show (0 : ℝ) ≤ 1 by norm_num)
  let v₀ : sphere (0 : EuclideanAmbient (n + 1)) 1 :=
    ⟨v, by simpa only [mem_sphere, dist_zero_right] using hv⟩
  have hrange : (range f).Nonempty := ⟨f v₀, mem_range_self v₀⟩
  obtain ⟨y, hA, hnull⟩ := hsmall (range f) hrange (by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact hdist a b)
  let fA : C(sphere (0 : EuclideanAmbient (n + 1)) 1, range f) :=
    ⟨fun x => ⟨f x, mem_range_self x⟩, f.continuous.subtype_mk _⟩
  obtain ⟨G, hG⟩ := nullhomotopic_extends_closedBall
    ((ContinuousMap.inclusion hA).comp fA) (hnull.comp_left fA)
  refine ⟨(ContinuousMap.subtypeVal _).comp G, ?_, ?_⟩
  · intro x
    exact congrArg Subtype.val (hG x)
  · intro a b
    have ha : dist (G a).1 y < ε / 3 := (G a).2
    have hb : dist (G b).1 y < ε / 3 := (G b).2
    have htri := dist_triangle (G a).1 y (G b).1
    rw [dist_comm y (G b).1] at htri
    change dist (G a).1 (G b).1 ≤ ε
    linarith

section SimplexCone

open Convexity

/-- The boundary of a finite barycentric simplex. -/
abbrev simplexBoundary (V : Type*) :=
  {p : StdSimplex ℝ V // ∃ i, p.weights i = 0}

/-- A codimension-one face, with its ordinary subspace topology. -/
abbrev simplexFace (V : Type*) (i : V) :=
  {p : StdSimplex ℝ V // p.weights i = 0}

variable {V : Type*} [Fintype V] [Nonempty V]

private def simplexOfCoordinates (w : V → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hs : ∑ i, w i = 1) : StdSimplex ℝ V where
  weights := Finsupp.equivFunOnFinite.symm w
  nonneg i := by simpa using hw i
  total := by simpa [Finsupp.sum_fintype] using hs

omit [Nonempty V] in
@[simp] private theorem simplexOfCoordinates_weights (w : V → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) (i : V) :
    (simplexOfCoordinates w hw hs).weights i = w i := by
  simp [simplexOfCoordinates]

/-- Join a boundary point to the barycenter, with the barycenter at time one. -/
def simplexConeProjection (p : unitInterval × simplexBoundary V) : StdSimplex ℝ V :=
  simplexOfCoordinates
    (fun i => (1 - (p.1 : ℝ)) * p.2.1.weights i + (p.1 : ℝ) / Fintype.card V)
    (fun i => add_nonneg (mul_nonneg (sub_nonneg.mpr p.1.2.2)
      (p.2.1.weights_nonneg i)) (div_nonneg p.1.2.1 (Nat.cast_nonneg _))) (by
      have hc : (Fintype.card V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, StdSimplex.total_of_fintype,
        mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp
      ring)

@[simp] theorem simplexConeProjection_weights (p : unitInterval × simplexBoundary V) (i : V) :
    (simplexConeProjection p).weights i =
      (1 - (p.1 : ℝ)) * p.2.1.weights i + (p.1 : ℝ) / Fintype.card V := by
  simp [simplexConeProjection]

theorem continuous_simplexConeProjection : Continuous (simplexConeProjection (V := V)) := by
  apply (StdSimplex.isEmbedding_toFun_comp_weights ℝ V).continuous_iff.mpr
  apply continuous_pi
  intro i
  simp only [Function.comp_def, simplexConeProjection_weights]
  exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
    ((StdSimplex.continuous_weights_apply ℝ i).comp
      (continuous_subtype_val.comp continuous_snd))).add
    ((continuous_subtype_val.comp continuous_fst).div_const _)

/-- The only nontrivial fiber of the cone map is its top, at the barycenter. -/
theorem simplexConeProjection_fiber (p q : unitInterval × simplexBoundary V)
    (heq : simplexConeProjection p = simplexConeProjection q) :
    p.1 = q.1 ∧ (p.1 = 1 ∨ p.2 = q.2) := by
  have hc : (0 : ℝ) < Fintype.card V := Nat.cast_pos.mpr Fintype.card_pos
  obtain ⟨i, hi⟩ := p.2.2
  obtain ⟨j, hj⟩ := q.2.2
  have hiq := congrArg (fun z : StdSimplex ℝ V => z.weights i) heq
  have hjq := congrArg (fun z : StdSimplex ℝ V => z.weights j) heq
  simp only [simplexConeProjection_weights] at hiq hjq
  rw [hi, mul_zero, zero_add] at hiq
  rw [hj, mul_zero, zero_add] at hjq
  have hle : (q.1 : ℝ) / Fintype.card V ≤ (p.1 : ℝ) / Fintype.card V := by
    rw [hiq]
    exact le_add_of_nonneg_left (mul_nonneg (sub_nonneg.mpr q.1.2.2)
      (q.2.1.weights_nonneg i))
  have hge : (p.1 : ℝ) / Fintype.card V ≤ (q.1 : ℝ) / Fintype.card V := by
    rw [← hjq]
    exact le_add_of_nonneg_left (mul_nonneg (sub_nonneg.mpr p.1.2.2)
      (p.2.1.weights_nonneg j))
  have ht : p.1 = q.1 := Subtype.ext ((div_left_inj' hc.ne').mp (le_antisymm hge hle))
  refine ⟨ht, ?_⟩
  by_cases htop : p.1 = 1
  · exact Or.inl htop
  · right
    apply Subtype.ext
    apply StdSimplex.ext
    ext k
    have hk := congrArg (fun z : StdSimplex ℝ V => z.weights k) heq
    simp only [simplexConeProjection_weights, ← ht] at hk
    have hne : 1 - (p.1 : ℝ) ≠ 0 := by
      intro h
      apply htop
      apply Subtype.ext
      change (p.1 : ℝ) = 1
      linarith
    exact (mul_left_cancel₀ hne (add_right_cancel hk))

omit [Nonempty V] in
theorem isClosed_simplexBoundary :
    IsClosed {p : StdSimplex ℝ V | ∃ i, p.weights i = 0} := by
  convert isClosed_iUnion_of_finite (fun i : V =>
    isClosed_eq (StdSimplex.continuous_weights_apply ℝ i)
      (continuous_const (y := (0 : ℝ)))) using 1
  ext p
  simp

instance simplexBoundary_compactSpace : CompactSpace (simplexBoundary V) :=
  isCompact_iff_compactSpace.mp isClosed_simplexBoundary.isCompact

instance simplexFace_compactSpace (i : V) : CompactSpace (simplexFace V i) :=
  isCompact_iff_compactSpace.mp
    (isClosed_eq (StdSimplex.continuous_weights_apply ℝ i)
      (continuous_const (y := (0 : ℝ)))).isCompact

/-- The finite disjoint family of closed faces covers the boundary. -/
def simplexFaceProjection (p : Σ i : V, simplexFace V i) : simplexBoundary V :=
  ⟨p.2.1, p.1, p.2.2⟩

omit [Nonempty V] in
theorem simplexFaceProjection_isQuotientMap :
    IsQuotientMap (simplexFaceProjection (V := V)) := by
  let : T2Space (StdSimplex ℝ V) := (StdSimplex.isEmbedding_toFun_comp_weights ℝ V).t2Space
  have hc : Continuous (simplexFaceProjection (V := V)) := by
    apply continuous_sigma
    intro i
    exact continuous_subtype_val.subtype_mk _
  have hs : Function.Surjective (simplexFaceProjection (V := V)) := by
    rintro ⟨p, i, hi⟩
    exact ⟨⟨i, p, hi⟩, rfl⟩
  exact hc.isClosedMap.isQuotientMap hc hs

omit [Nonempty V] in
/-- Compatible continuous maps on the closed faces give a unique continuous
map on the boundary. In particular, compatibility suffices for the boundary
map needed at each step of the nerve extension induction. -/
theorem glue_simplexBoundary {Y : Type*} [TopologicalSpace Y]
    (f : ∀ i : V, C(simplexFace V i, Y))
    (hcompat : ∀ (i j : V) (x : simplexFace V i) (z : simplexFace V j),
      x.1 = z.1 → f i x = f j z) :
    ∃! g : C(simplexBoundary V, Y),
      ∀ (i : V) (x : simplexFace V i), g ⟨x.1, i, x.2⟩ = f i x := by
  classical
  let q := simplexFaceProjection (V := V)
  have hq : IsQuotientMap q := simplexFaceProjection_isQuotientMap
  let F : (Σ i : V, simplexFace V i) → Y := fun p => f p.1 p.2
  have hF : Continuous F := continuous_sigma (fun i => (f i).continuous)
  have hfiber : ∀ p z, q p = q z → F p = F z := by
    intro p z heq
    exact hcompat p.1 z.1 p.2 z.2 (congrArg Subtype.val heq)
  let g : simplexBoundary V → Y := fun x => F (Function.surjInv hq.surjective x)
  have hgcomp : g ∘ q = F := by
    funext p
    exact hfiber _ p (Function.surjInv_eq hq.surjective _)
  have hg : Continuous g := hq.continuous_iff.mpr (by rw [hgcomp]; exact hF)
  refine ⟨⟨g, hg⟩, ?_, ?_⟩
  · intro i x
    exact congrFun hgcomp ⟨i, x⟩
  · intro g' hg'
    apply ContinuousMap.ext
    rintro ⟨p, i, hi⟩
    exact (hg' i ⟨p, hi⟩).trans (congrFun hgcomp ⟨i, p, hi⟩).symm

omit [Nonempty V] in
/-- In dimension at least two, any pair of codimension-one faces meets at a
vertex. Consequently, controlling the image on each face controls the whole
boundary with twice the same bound. -/
theorem simplexBoundary_dist_le_two_mul {X : Type*} [MetricSpace X]
    (hcard : 2 < Fintype.card V) (f : simplexBoundary V → X) (ε : ℝ)
    (hface : ∀ (i : V) (x z : simplexFace V i),
      dist (f ⟨x.1, i, x.2⟩) (f ⟨z.1, i, z.2⟩) ≤ ε)
    (x z : simplexBoundary V) : dist (f x) (f z) ≤ 2 * ε := by
  classical
  obtain ⟨i, hi⟩ := x.2
  obtain ⟨j, hj⟩ := z.2
  have hlt : ({i, j} : Finset V).card < (Finset.univ : Finset V).card := by
    have hle : ({i, j} : Finset V).card ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
    simpa using hle.trans_lt hcard
  obtain ⟨k, _, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hki : k ≠ i := fun h => hk (by simp [h])
  have hkj : k ≠ j := fun h => hk (by simp [h])
  have hbi : (StdSimplex.single (R := ℝ) k).weights i = 0 := by simp [hki]
  have hbj : (StdSimplex.single (R := ℝ) k).weights j = 0 := by simp [hkj]
  let b : simplexBoundary V := ⟨.single k, i, hbi⟩
  have hxb : dist (f x) (f b) ≤ ε := hface i ⟨x.1, hi⟩ ⟨.single k, hbi⟩
  have hbz : dist (f b) (f z) ≤ ε := hface j ⟨.single k, hbj⟩ ⟨z.1, hj⟩
  calc
    dist (f x) (f z) ≤ dist (f x) (f b) + dist (f b) (f z) := dist_triangle _ _ _
    _ ≤ ε + ε := add_le_add hxb hbz
    _ = 2 * ε := by ring

omit [Fintype V] [Nonempty V] in
theorem simplexBoundary_nonempty [Nontrivial V] : Nonempty (simplexBoundary V) := by
  classical
  obtain ⟨i, j, hij⟩ := exists_pair_ne V
  exact ⟨⟨.single i, j, by simp [hij]⟩⟩

/-- Every point lies on a segment joining a boundary point to the barycenter. -/
theorem simplexConeProjection_surjective [Nontrivial V] :
    Function.Surjective (simplexConeProjection (V := V)) := by
  classical
  intro p
  obtain ⟨i, hi⟩ := Finite.exists_min (fun i : V => p.weights i)
  let a := p.weights i
  let c : ℝ := Fintype.card V
  have hc : 0 < c := Nat.cast_pos.mpr Fintype.card_pos
  have ha : 0 ≤ a := p.weights_nonneg i
  have hmin (j : V) : a ≤ p.weights j := hi j
  have hca : c * a ≤ 1 := by
    calc
      c * a = ∑ _j : V, a := by simp [c]
      _ ≤ ∑ j : V, p.weights j := Finset.sum_le_sum (fun j _ => hmin j)
      _ = 1 := p.total_of_fintype
  let t : unitInterval := ⟨c * a, mul_nonneg hc.le ha, hca⟩
  by_cases htop : c * a = 1
  · let b : simplexBoundary V := Classical.choice simplexBoundary_nonempty
    refine ⟨(t, b), ?_⟩
    have heqsum : (∑ _j : V, a) = ∑ j : V, p.weights j := by
      simpa [c] using htop.trans p.total_of_fintype.symm
    have hall : ∀ j : V, a = p.weights j := by
      have := (Finset.sum_eq_sum_iff_of_le (fun j (_ : j ∈ (Finset.univ : Finset V)) =>
        hmin j)).mp heqsum
      exact fun j => this j (Finset.mem_univ j)
    ext j
    simp only [simplexConeProjection_weights, t, htop,
      sub_self, zero_mul, zero_add]
    rw [← hall j]
    change 1 / c = a
    apply (div_eq_iff hc.ne').mpr
    linarith [htop]
  · have hden : 0 < 1 - c * a := sub_pos.mpr (lt_of_le_of_ne hca htop)
    let b : StdSimplex ℝ V := simplexOfCoordinates
      (fun j => (p.weights j - a) / (1 - c * a))
      (fun j => div_nonneg (sub_nonneg.mpr (hmin j)) hden.le) (by
        rw [← Finset.sum_div, Finset.sum_sub_distrib, p.total_of_fintype]
        simpa [c] using div_self hden.ne')
    have hb : ∃ j, b.weights j = 0 := ⟨i, by simp [b, a]⟩
    refine ⟨(t, ⟨b, hb⟩), ?_⟩
    ext j
    simp only [simplexConeProjection_weights, t, b,
      simplexOfCoordinates_weights]
    change (1 - c * a) * ((p.weights j - a) / (1 - c * a)) + (c * a) / c =
      p.weights j
    field_simp
    nlinarith [hden.ne', hc.ne']

theorem simplexConeProjection_isQuotientMap [Nontrivial V] :
    IsQuotientMap (simplexConeProjection (V := V)) := by
  let : T2Space (StdSimplex ℝ V) := (StdSimplex.isEmbedding_toFun_comp_weights ℝ V).t2Space
  exact continuous_simplexConeProjection.isClosedMap.isQuotientMap
    continuous_simplexConeProjection simplexConeProjection_surjective

/-- A nullhomotopy on a finite simplex boundary extends over the simplex. -/
theorem nullhomotopic_extends_simplex [Nontrivial V]
    {Y : Type*} [TopologicalSpace Y] (f : C(simplexBoundary V, Y))
    (hf : f.Nullhomotopic) :
    ∃ F : C(StdSimplex ℝ V, Y), ∀ x : simplexBoundary V, F x.1 = f x := by
  classical
  obtain ⟨y, ⟨H⟩⟩ := hf
  have hH : ∀ (p q : unitInterval × simplexBoundary V),
      simplexConeProjection p = simplexConeProjection q → H p = H q := by
    rintro ⟨t, b⟩ ⟨s, c⟩ heq
    obtain ⟨ht, hfiber⟩ := simplexConeProjection_fiber _ _ heq
    change t = s at ht
    subst s
    change t = 1 ∨ b = c at hfiber
    rcases hfiber with htop | hbc
    · subst t
      simp only [Homotopy.apply_one, ContinuousMap.const_apply]
    · subst c
      rfl
  let g : StdSimplex ℝ V → Y :=
    fun p => H (Function.surjInv simplexConeProjection_surjective p)
  have hgcomp : g ∘ simplexConeProjection = H := by
    funext p
    exact hH _ p (Function.surjInv_eq simplexConeProjection_surjective _)
  have hg : Continuous g := simplexConeProjection_isQuotientMap.continuous_iff.mpr (by
    rw [hgcomp]
    exact H.continuous)
  refine ⟨⟨g, hg⟩, ?_⟩
  intro x
  have hx : simplexConeProjection (0, x) = x.1 := by
    ext i
    simp
  change g _ = f x
  rw [← hx]
  exact (congrFun hgcomp (0, x)).trans (H.apply_zero x)

end SimplexCone

/-- The small-extension property in the source, with the same bound for every
positive-dimensional finite barycentric simplex. -/
theorem uniform_small_simplex_extension {X : Type*} [MetricSpace X] [CompactSpace X]
    (hLC : LocallyContractibleSpace X) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ (V : Type*) [Fintype V] [Nontrivial V]
      (f : C(simplexBoundary V, X)),
      (∀ a b, dist (f a) (f b) < δ) →
      ∃ F : C(Convexity.StdSimplex ℝ V, X),
        (∀ x : simplexBoundary V, F x.1 = f x) ∧
        (∀ a b, dist (F a) (F b) ≤ ε) := by
  obtain ⟨δ, hδ, hsmall⟩ := uniform_small_nullhomotopic_inclusion hLC (ε / 3) (by linarith)
  refine ⟨δ, hδ, ?_⟩
  intro V _ _ f hdist
  let v₀ : simplexBoundary V := Classical.choice simplexBoundary_nonempty
  have hrange : (range f).Nonempty := ⟨f v₀, mem_range_self v₀⟩
  obtain ⟨y, hA, hnull⟩ := hsmall (range f) hrange (by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact hdist a b)
  let fA : C(simplexBoundary V, range f) :=
    ⟨fun x => ⟨f x, mem_range_self x⟩, f.continuous.subtype_mk _⟩
  obtain ⟨G, hG⟩ := nullhomotopic_extends_simplex
    ((ContinuousMap.inclusion hA).comp fA) (hnull.comp_left fA)
  refine ⟨(ContinuousMap.subtypeVal _).comp G, ?_, ?_⟩
  · intro x
    exact congrArg Subtype.val (hG x)
  · intro a b
    have ha : dist (G a).1 y < ε / 3 := (G a).2
    have hb : dist (G b).1 y < ε / 3 := (G b).2
    have htri := dist_triangle (G a).1 y (G b).1
    rw [dist_comm y (G b).1] at htri
    change dist (G a).1 (G b).1 ≤ ε
    linarith

/-- The local inductive step of the nerve construction: compatible controlled
maps on the closed faces extend over a simplex of dimension at least two. -/
theorem uniform_small_compatible_face_extension {X : Type*} [MetricSpace X] [CompactSpace X]
    (hLC : LocallyContractibleSpace X) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ (V : Type*) [Fintype V] [Nontrivial V]
      (_hcard : 2 < Fintype.card V) (f : ∀ i : V, C(simplexFace V i, X)),
      (∀ (i j : V) (x : simplexFace V i) (z : simplexFace V j),
        x.1 = z.1 → f i x = f j z) →
      (∀ (i : V) (x z : simplexFace V i), dist (f i x) (f i z) ≤ δ) →
      ∃ F : C(Convexity.StdSimplex ℝ V, X),
        (∀ (i : V) (x : simplexFace V i), F x.1 = f i x) ∧
        (∀ a b, dist (F a) (F b) ≤ ε) := by
  obtain ⟨δ, hδ, hsmall⟩ := uniform_small_simplex_extension hLC ε hε
  refine ⟨δ / 3, by linarith, ?_⟩
  intro V _ _ hcard f hcompat hface
  obtain ⟨g, hg, _⟩ := glue_simplexBoundary f hcompat
  have hgdist : ∀ a b, dist (g a) (g b) < δ := by
    intro a b
    have hle := simplexBoundary_dist_le_two_mul hcard g (δ / 3) (by
      intro i x z
      rw [hg, hg]
      exact hface i x z) a b
    linarith
  obtain ⟨F, hF, hbound⟩ := hsmall V g hgdist
  refine ⟨F, ?_, hbound⟩
  intro i x
  exact (hF ⟨x.1, i, x.2⟩).trans (hg i x)

section ExtensionAcrossClosedSet

variable {E : Type*} [MetricSpace E] {K N : Set E}

/-- Extend a map on a punctured neighborhood by the identity on the closed set. -/
def extendByIdentity (f : ↥(N \ K) → K) (x : N) : K := by
  classical
  exact if hx : x.1 ∈ K then ⟨x.1, hx⟩ else f ⟨x.1, x.2, hx⟩

omit [MetricSpace E] in
@[simp] theorem extendByIdentity_of_mem (f : ↥(N \ K) → K)
    (x : N) (hx : x.1 ∈ K) : extendByIdentity f x = ⟨x.1, hx⟩ := by
  simp [extendByIdentity, hx]

omit [MetricSpace E] in
@[simp] theorem extendByIdentity_of_not_mem (f : ↥(N \ K) → K)
    (x : N) (hx : x.1 ∉ K) : extendByIdentity f x = f ⟨x.1, x.2, hx⟩ := by
  simp [extendByIdentity, hx]

/-- Vanishing displacement near `K` proves continuity across `K`. The modulus
is arbitrary: no linear bound or regularity of the embedding is required. -/
theorem continuous_extendByIdentity (hK : IsClosed K) (f : C(↥(N \ K), K))
    (hsmall : ∀ ε > 0, ∃ δ > 0, ∀ x : ↥(N \ K),
      infDist x.1 K < δ → dist (f x).1 x.1 < ε) :
    Continuous (extendByIdentity f) := by
  classical
  apply continuous_iff_continuousAt.mpr
  intro y
  by_cases hy : y.1 ∈ K
  · apply Metric.continuousAt_iff.mpr
    intro ε hε
    obtain ⟨δ, hδ, hcontrol⟩ := hsmall (ε / 2) (by linarith)
    refine ⟨min δ (ε / 2), lt_min hδ (by linarith), ?_⟩
    intro x hx
    have hxy : dist x.1 y.1 < ε / 2 := lt_of_lt_of_le hx (min_le_right _ _)
    rw [extendByIdentity_of_mem f y hy]
    by_cases hxK : x.1 ∈ K
    · rw [extendByIdentity_of_mem f x hxK]
      exact lt_of_lt_of_le hxy (by linarith)
    · rw [extendByIdentity_of_not_mem f x hxK]
      have hinf : infDist x.1 K < δ :=
        (infDist_le_dist_of_mem hy).trans_lt (lt_of_lt_of_le hx (min_le_left _ _))
      have hfx := hcontrol ⟨x.1, x.2, hxK⟩ hinf
      have htri := dist_triangle (f ⟨x.1, x.2, hxK⟩).1 x.1 y.1
      change dist (f ⟨x.1, x.2, hxK⟩).1 y.1 < ε
      linarith
  · have hopen : IsOpen {x : N | x.1 ∉ K} := hK.isOpen_compl.preimage continuous_subtype_val
    have hnhds : {x : N | x.1 ∉ K} ∈ 𝓝 y := hopen.mem_nhds hy
    let g : N → K := fun x => if hx : x.1 ∈ K then ⟨x.1, hx⟩ else f ⟨x.1, x.2, hx⟩
    have hlocal : ContinuousOn g {x : N | x.1 ∉ K} := by
      rw [continuousOn_iff_continuous_domRestrict]
      have hc : Continuous (fun x : {x : N | x.1 ∉ K} =>
          (⟨x.1.1, x.1.2, x.2⟩ : ↥(N \ K))) :=
        (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      have hcomp := f.continuous.comp hc
      convert hcomp using 1
      funext x
      exact dite_eq_right x.2
    exact hlocal.continuousAt hnhds

/-- Final assembly of a neighborhood retraction from the punctured-neighborhood
map constructed by the nerve argument and its vanishing-displacement estimate. -/
theorem hasOpenNeighborhoodRetraction_of_punctured_map
    (hK : IsClosed K) (hN : IsOpen N) (hKN : K ⊆ N) (f : C(↥(N \ K), K))
    (hsmall : ∀ ε > 0, ∃ δ > 0, ∀ x : ↥(N \ K),
      infDist x.1 K < δ → dist (f x).1 x.1 < ε) :
    HasOpenNeighborhoodRetraction K := by
  refine ⟨N, hN, hKN, ⟨extendByIdentity f, continuous_extendByIdentity hK f hsmall⟩, ?_⟩
  intro x
  exact extendByIdentity_of_mem f ⟨x.1, hKN x.2⟩ x.2

end ExtensionAcrossClosedSet

section ShrinkingCover

variable {E : Type*} [MetricSpace E]

/-- A finite set has a separated subfamily which is a closed-ball net. -/
theorem finite_separated_net (s : Finset E) (r : ℝ) (hr : 0 < r) :
    ∃ t : Finset E, t ⊆ s ∧
      (∀ a ∈ t, ∀ b ∈ t, a ≠ b → r < dist a b) ∧
      ∀ a ∈ s, ∃ b ∈ t, dist a b ≤ r := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨∅, by simp⟩
  | @insert x s hxs ih =>
    obtain ⟨t, hts, hsep, hnet⟩ := ih
    by_cases hx : ∃ b ∈ t, dist x b ≤ r
    · refine ⟨t, hts.trans (Finset.subset_insert _ _), hsep, ?_⟩
      intro a ha
      rcases Finset.mem_insert.mp ha with hax | ha
      · subst a
        exact hx
      · exact hnet a ha
    · have hxt : x ∉ t := by
        intro h
        exact hx ⟨x, h, by simpa using hr.le⟩
      refine ⟨insert x t, Finset.insert_subset_insert _ hts, ?_, ?_⟩
      · intro a ha b hb hab
        by_cases hax : a = x
        · subst a
          have hbt : b ∈ t := Finset.mem_of_mem_insert_of_ne hb hab.symm
          exact lt_of_not_ge (fun h => hx ⟨b, hbt, h⟩)
        · have hat : a ∈ t := Finset.mem_of_mem_insert_of_ne ha hax
          by_cases hbx : b = x
          · subst b
            rw [dist_comm]
            exact lt_of_not_ge (fun h => hx ⟨a, hat, h⟩)
          · exact hsep a hat b (Finset.mem_of_mem_insert_of_ne hb hbx) hab
      · intro a ha
        rcases Finset.mem_insert.mp ha with hax | ha
        · subst a
          exact ⟨x, Finset.mem_insert_self _ _, by simpa using hr.le⟩
        · obtain ⟨b, hb, hab⟩ := hnet a ha
          exact ⟨b, Finset.mem_insert_of_mem hb, hab⟩

/-- A totally bounded set has a finite internal open-ball net with a fixed
separation ratio. This construction requires no nonemptiness hypothesis. -/
theorem totallyBounded_separated_net {A : Set E} (hA : TotallyBounded A)
    (r : ℝ) (hr : 0 < r) :
    ∃ t : Finset E, (↑t : Set E) ⊆ A ∧
      (∀ a ∈ t, ∀ b ∈ t, a ≠ b → r / 2 < dist a b) ∧
      ∀ x ∈ A, ∃ z ∈ t, dist x z < r := by
  classical
  obtain ⟨s, hsA, hs, hcover⟩ :=
    finite_approx_of_totallyBounded hA (r / 4) (by linarith)
  obtain ⟨t, hts, hsep, hnet⟩ := finite_separated_net hs.toFinset (r / 2) (by linarith)
  refine ⟨t, fun x hx => hsA (by simpa using hts hx), hsep, ?_⟩
  intro x hx
  obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.mp (hcover hx)
  obtain ⟨z, hz, haz⟩ := hnet a (by simpa using ha)
  refine ⟨z, hz, ?_⟩
  have htri := dist_triangle x a z
  change dist x a < r / 4 at hxa
  linarith

/-- The radius at dyadic level `j`, starting at the arbitrary upper cutoff `τ`. -/
def dyadicRadius (τ : ℝ) (j : ℕ) : ℝ := τ * (1 / 2 : ℝ) ^ j

theorem dyadicRadius_pos {τ : ℝ} (hτ : 0 < τ) (j : ℕ) : 0 < dyadicRadius τ j :=
  mul_pos hτ (pow_pos (by norm_num) _)

theorem dyadicRadius_antitone {τ : ℝ} (hτ : 0 ≤ τ) : Antitone (dyadicRadius τ) := by
  intro i j hij
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) hij) hτ

/-- Finite separated centers in all dyadic distance bands. The balls of radius
`dyadicRadius τ j` about these centers will cover a punctured neighborhood. -/
theorem exists_dyadic_band_nets [ProperSpace E] {K : Set E}
    (hK : IsCompact K) (hne : K.Nonempty) (τ : ℝ) (hτ : 0 < τ) :
    ∃ C : ℕ → Finset E,
      (∀ j z, z ∈ C j →
        2 * dyadicRadius τ j ≤ infDist z K ∧ infDist z K ≤ 8 * dyadicRadius τ j) ∧
      (∀ j a, a ∈ C j → ∀ b ∈ C j, a ≠ b →
        dyadicRadius τ j / 2 < dist a b) ∧
      (∀ j x, 2 * dyadicRadius τ j ≤ infDist x K →
        infDist x K ≤ 8 * dyadicRadius τ j →
        ∃ z ∈ C j, dist x z < dyadicRadius τ j) := by
  let A (j : ℕ) : Set E := {z | 2 * dyadicRadius τ j ≤ infDist z K ∧
    infDist z K ≤ 8 * dyadicRadius τ j}
  have hA (j : ℕ) : TotallyBounded (A j) := by
    apply (hK.isBounded.thickening (δ := 8 * dyadicRadius τ j + 1)).isCompact_closure.totallyBounded.subset
    intro x hx
    apply subset_closure
    exact (mem_thickening_iff_infDist_lt hne).mpr (by
      have := hx.2
      linarith)
  choose C hCA hsep hnet using
    fun j => totallyBounded_separated_net (hA j) _ (dyadicRadius_pos hτ j)
  exact ⟨C, hCA, hsep, fun j x hlow hupp => hnet j x ⟨hlow, hupp⟩⟩

/-- Finite separated nets in successive bands of distance from a compact set.
The data are constructed below, rather than postulated as an ENR hypothesis. -/
structure DyadicBandCover (K : Set E) (τ : ℝ) where
  centers : ℕ → Finset E
  band : ∀ j z, z ∈ centers j →
    2 * dyadicRadius τ j ≤ infDist z K ∧ infDist z K ≤ 8 * dyadicRadius τ j
  separated : ∀ j a, a ∈ centers j → ∀ b ∈ centers j, a ≠ b →
    dyadicRadius τ j / 2 < dist a b
  net : ∀ j x, 2 * dyadicRadius τ j ≤ infDist x K →
    infDist x K ≤ 8 * dyadicRadius τ j →
    ∃ z ∈ centers j, dist x z < dyadicRadius τ j

theorem nonempty_dyadicBandCover [ProperSpace E] {K : Set E}
    (hK : IsCompact K) (hne : K.Nonempty) {τ : ℝ} (hτ : 0 < τ) :
    Nonempty (DyadicBandCover K τ) := by
  obtain ⟨C, hband, hsep, hnet⟩ := exists_dyadic_band_nets hK hne τ hτ
  exact ⟨⟨C, hband, hsep, hnet⟩⟩

theorem exists_dyadicRadius_near {τ d : ℝ} (hτ : 0 < τ)
    (hd : 0 < d) (hdτ : d < 4 * τ) :
    ∃ j, 2 * dyadicRadius τ j < d ∧ d ≤ 4 * dyadicRadius τ j := by
  obtain ⟨j, hjlow, hjhigh⟩ := exists_nat_pow_near_of_lt_one
    (div_pos hd (by positivity : 0 < 4 * τ))
    (le_of_lt ((div_lt_one (by positivity : 0 < 4 * τ)).mpr hdτ))
    (show (0 : ℝ) < 1 / 2 by norm_num) (show (1 / 2 : ℝ) < 1 by norm_num)
  have hl := (lt_div_iff₀ (by positivity : 0 < 4 * τ)).mp hjlow
  have hh := (div_le_iff₀ (by positivity : 0 < 4 * τ)).mp hjhigh
  refine ⟨j, ?_, ?_⟩ <;> dsimp [dyadicRadius]
  · rw [pow_succ] at hl
    nlinarith
  · nlinarith

namespace DyadicBandCover

variable {K : Set E} {τ : ℝ} (D : DyadicBandCover K τ)

/-- A center is labelled by its level, so centers recurring at other levels
remain distinct vertices of the eventual nerve. -/
abbrev Index := Σ j, {z // z ∈ D.centers j}

def coverBall (i : D.Index) : Set E := ball i.2.1 (dyadicRadius τ i.1)

theorem distance_bounds {i : D.Index} {x : E} (hx : x ∈ D.coverBall i) :
    dyadicRadius τ i.1 < infDist x K ∧ infDist x K < 9 * dyadicRadius τ i.1 := by
  have hb := D.band i.1 i.2.1 i.2.2
  have hl := infDist_le_infDist_add_dist (x := i.2.1) (y := x) (s := K)
  have hh := infDist_le_infDist_add_dist (x := x) (y := i.2.1) (s := K)
  change dist x i.2.1 < dyadicRadius τ i.1 at hx
  rw [dist_comm i.2.1 x] at hl
  constructor <;> linarith [hb.1, hb.2]

theorem coverBall_subset_compl (hτ : 0 < τ) (i : D.Index) : D.coverBall i ⊆ Kᶜ := by
  intro x hx hxK
  have hl := (D.distance_bounds hx).1
  rw [infDist_zero_of_mem hxK] at hl
  exact (dyadicRadius_pos hτ i.1).not_gt hl

/-- Every point of the punctured `4τ`-neighborhood is covered, with no
measure-theoretic exceptional set. -/
theorem covers (hτ : 0 < τ) {x : E} (hx : 0 < infDist x K)
    (hxτ : infDist x K < 4 * τ) : ∃ i : D.Index, x ∈ D.coverBall i := by
  obtain ⟨j, hlow, hhigh⟩ := exists_dyadicRadius_near hτ hx hxτ
  have hr := dyadicRadius_pos hτ j
  obtain ⟨z, hz, hxz⟩ := D.net j x hlow.le (by linarith)
  exact ⟨⟨j, z, hz⟩, hxz⟩

/-- Only finitely many balls meet a sufficiently small neighborhood of a point
outside the closed set. Finiteness holds for the labelled balls, not merely
for their distinct underlying subsets. -/
theorem locallyFinite (hK : IsClosed K) (hne : K.Nonempty) (hτ : 0 < τ) :
    LocallyFinite (fun i : D.Index => {x : ↥(Kᶜ) | x.1 ∈ D.coverBall i}) := by
  classical
  intro x
  have hd : 0 < infDist x.1 K := (hK.notMem_iff_infDist_pos hne).mp x.2
  obtain ⟨J, hJ⟩ := exists_pow_lt_of_lt_one
    (div_pos (half_pos hd) (mul_pos (by norm_num : (0 : ℝ) < 9) hτ))
    (show (1 / 2 : ℝ) < 1 by norm_num)
  have hJsmall : 9 * dyadicRadius τ J < infDist x.1 K / 2 := by
    have := (lt_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 9) hτ)).mp hJ
    dsimp [dyadicRadius]
    nlinarith
  let U : Set ↥(Kᶜ) := {y | infDist x.1 K / 2 < infDist y.1 K}
  have hU : U ∈ 𝓝 x :=
    (isOpen_lt continuous_const
      ((continuous_infDist_pt K).comp continuous_subtype_val)).mem_nhds (by
        dsimp [U]
        linarith)
  refine ⟨U, hU, ?_⟩
  have hfin : (⋃ j ∈ {j : ℕ | j < J},
      range (fun z : ↥(D.centers j) => (⟨j, z⟩ : D.Index))).Finite :=
    (finite_lt_nat J).biUnion (fun j _ => finite_range _)
  apply hfin.subset
  intro i hi
  obtain ⟨y, hyball, hyU⟩ := hi
  have hdist := (D.distance_bounds hyball).2
  have hij : i.1 < J := by
    by_contra h
    have hr := dyadicRadius_antitone hτ.le (Nat.le_of_not_gt h)
    change infDist x.1 K / 2 < infDist y.1 K at hyU
    linarith
  exact mem_iUnion₂.mpr ⟨i.1, hij, mem_range_self i.2⟩

/-- Balls through a common point can involve at most four successive levels. -/
theorem levels_near {i k : D.Index} {x : E}
    (hi : x ∈ D.coverBall i) (hk : x ∈ D.coverBall k) : i.1 < k.1 + 4 := by
  have hi' := D.distance_bounds hi
  have hk' := D.distance_bounds hk
  have hrpos : 0 < dyadicRadius τ i.1 := lt_of_lt_of_le
    (dist_nonneg.trans_lt hi) le_rfl
  have hτ : 0 < τ := by
    by_contra h
    have hnonpos : dyadicRadius τ i.1 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) (by positivity)
    linarith
  by_contra h
  have hr := dyadicRadius_antitone hτ.le (Nat.le_of_not_gt h)
  have heq : dyadicRadius τ (k.1 + 4) = dyadicRadius τ k.1 / 16 := by
    simp only [dyadicRadius, pow_add]
    norm_num
    ring
  rw [heq] at hr
  linarith [hi'.2, hk'.1]

end DyadicBandCover

end ShrinkingCover

end P202.Duality

noncomputable section
open Set Topology Metric ContinuousMap Convexity

namespace P202.Duality

/-- Delete a zero coordinate of a finite standard simplex. -/
def simplexFaceRestriction {V : Type*} (i : V) (p : simplexFace V i) :
    StdSimplex ℝ {v : V // v ≠ i} where
  weights := p.1.weights.subtypeDomain (· ≠ i)
  nonneg v := p.1.weights_nonneg v.1
  total := by
    refine (Finsupp.sum_subtypeDomain_index (h := fun (_ : V) (r : ℝ) => r) ?_).trans p.1.total
    intro v hv hvi
    subst v
    exact (Finsupp.mem_support_iff.mp hv) p.2

@[simp]
theorem simplexFaceRestriction_weights {V : Type*} (i : V)
    (p : simplexFace V i) (v : {v : V // v ≠ i}) :
    (simplexFaceRestriction i p).weights v = p.1.weights v.1 := rfl

/-- Restore the deleted zero coordinate. -/
def simplexFaceInclusion {V : Type*} (i : V)
    (p : StdSimplex ℝ {v : V // v ≠ i}) : simplexFace V i :=
  ⟨p.map Subtype.val, by
    rw [StdSimplex.weights_map, Finsupp.mapDomain_of_notMem_range]
    rintro ⟨v, hv⟩
    exact v.2 hv⟩

@[simp]
theorem simplexFaceInclusion_val {V : Type*} (i : V)
    (p : StdSimplex ℝ {v : V // v ≠ i}) :
    (simplexFaceInclusion i p).1 = p.map Subtype.val := rfl

@[simp]
theorem simplexFaceInclusion_weights {V : Type*} (i : V)
    (p : StdSimplex ℝ {v : V // v ≠ i}) (v : {v : V // v ≠ i}) :
    (simplexFaceInclusion i p).1.weights v.1 = p.weights v := by
  exact Finsupp.mapDomain_apply_of_injective Subtype.val_injective _ v

@[simp]
theorem simplexFaceRestriction_inclusion {V : Type*} (i : V)
    (p : StdSimplex ℝ {v : V // v ≠ i}) :
    simplexFaceRestriction i (simplexFaceInclusion i p) = p := by
  apply StdSimplex.ext
  ext v
  exact simplexFaceInclusion_weights i p v

@[simp]
theorem simplexFaceInclusion_restriction {V : Type*} (i : V)
    (p : simplexFace V i) :
    simplexFaceInclusion i (simplexFaceRestriction i p) = p := by
  apply Subtype.ext
  apply StdSimplex.ext
  ext v
  by_cases hv : v = i
  · subst v
    exact (simplexFaceInclusion i (simplexFaceRestriction i p)).2.trans p.2.symm
  · exact simplexFaceInclusion_weights i (simplexFaceRestriction i p) ⟨v, hv⟩

theorem continuous_simplexFaceRestriction {V : Type*} [Finite V] (i : V) :
    Continuous (simplexFaceRestriction i) := by
  apply (StdSimplex.isEmbedding_toFun_comp_weights ℝ {v : V // v ≠ i}).continuous_iff.mpr
  apply continuous_pi
  intro v
  exact (StdSimplex.continuous_weights_apply ℝ v.1).comp continuous_subtype_val

theorem continuous_simplexFaceInclusion {V : Type*} (i : V) :
    Continuous (simplexFaceInclusion i) :=
  (StdSimplex.continuous_map ℝ (Subtype.val : {v : V // v ≠ i} → V)).subtype_mk _

/-- A coordinate face is the standard simplex on the remaining vertices,
with the ordinary subspace topology on that face. This also handles singleton
vertex sets: both sides are empty. -/
def simplexFaceHomeomorph {V : Type*} [Finite V] (i : V) :
    simplexFace V i ≃ₜ StdSimplex ℝ {v : V // v ≠ i} where
  toFun := simplexFaceRestriction i
  invFun := simplexFaceInclusion i
  left_inv := simplexFaceInclusion_restriction i
  right_inv := simplexFaceRestriction_inclusion i
  continuous_toFun := continuous_simplexFaceRestriction i
  continuous_invFun := continuous_simplexFaceInclusion i

/-- Regard a finitely supported barycentric point as a point of any finite
simplex containing its support. -/
def simplexRestrictToFinset {V : Type*} (p : StdSimplex ℝ V) (s : Finset V)
    (hs : p.weights.support ⊆ s) : StdSimplex ℝ s where
  weights := p.weights.subtypeDomain (· ∈ s)
  nonneg v := p.weights_nonneg v.1
  total := by
    refine (Finsupp.sum_subtypeDomain_index (h := fun (_ : V) (r : ℝ) => r) hs).trans p.total

@[simp]
theorem simplexRestrictToFinset_weights {V : Type*} (p : StdSimplex ℝ V) (s : Finset V)
    (hs : p.weights.support ⊆ s) (v : s) :
    (simplexRestrictToFinset p s hs).weights v = p.weights v.1 := rfl

@[simp]
theorem simplexRestrictToFinset_map_val {V : Type*} (p : StdSimplex ℝ V) (s : Finset V)
    (hs : p.weights.support ⊆ s) :
    (simplexRestrictToFinset p s hs).map Subtype.val = p := by
  classical
  apply StdSimplex.ext
  ext v
  by_cases hv : v ∈ s
  · exact Finsupp.mapDomain_apply_of_injective Subtype.val_injective _ ⟨v, hv⟩
  · have hzero : p.weights v = 0 := Finsupp.notMem_support_iff.mp (fun h => hv (hs h))
    rw [hzero, StdSimplex.weights_map, Finsupp.mapDomain_of_notMem_range]
    simpa only [Subtype.range_coe_subtype, Set.mem_ofPred_eq] using hv

/-- Restriction inverts a finite-simplex chart, independently of which proof
of support containment is supplied. -/
@[simp]
theorem simplexRestrictToFinset_chart {V : Type*} (s : Finset V) (p : StdSimplex ℝ s)
    (hs : (p.map (Subtype.val : s → V)).weights.support ⊆ s) :
    simplexRestrictToFinset (p.map Subtype.val) s hs = p := by
  apply StdSimplex.ext
  ext v
  exact Finsupp.mapDomain_apply_of_injective Subtype.val_injective _ v

/-- Restricting barycentric points into one finite chart is continuous as soon
as the coordinates of those points are continuous. -/
theorem continuous_simplexRestrictToFinset_of_weights {T V : Type*} [TopologicalSpace T]
    (s : Finset V) (f : T → StdSimplex ℝ V)
    (hs : ∀ t, (f t).weights.support ⊆ s)
    (hf : ∀ v : s, Continuous (fun t => (f t).weights v.1)) :
    Continuous (fun t => simplexRestrictToFinset (f t) s (hs t)) := by
  apply (StdSimplex.isEmbedding_toFun_comp_weights ℝ s).continuous_iff.mpr
  exact continuous_pi hf

theorem continuous_simplexRestrictToFinset {T V : Type*} [TopologicalSpace T]
    (s : Finset V) (f : T → StdSimplex ℝ V) (hf : Continuous f)
    (hs : ∀ t, (f t).weights.support ⊆ s) :
    Continuous (fun t => simplexRestrictToFinset (f t) s (hs t)) :=
  continuous_simplexRestrictToFinset_of_weights s f hs
    (fun v => (StdSimplex.continuous_weights_apply ℝ v.1).comp hf)

end P202.Duality

noncomputable section
open Set Metric
open Classical
namespace P202.Duality
section Packing
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A separated collection of centers in a ball has uniformly bounded size. -/
theorem card_le_multiplicity_of_half_radius_separated
    (s : Finset E) (x : E) (r : ℝ) (hr : 0 < r)
    (hball : ∀ z ∈ s, dist z x < r)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → r / 2 < dist a b) :
    s.card ≤ Besicovitch.multiplicity E := by
  classical
  let f : E → E := fun z => (2 / r) • (z - x)
  have hf : Function.Injective f := by
    intro a b hab
    have hcoef : (2 / r : ℝ) ≠ 0 := div_ne_zero (by norm_num) hr.ne'
    exact sub_left_injective (smul_right_injective E hcoef hab)
  have hb : ∀ c ∈ s.image f, ‖c‖ ≤ 2 := by
    intro c hc
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hc
    simp only [f, norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 2 / r)]
    have hz' : ‖z - x‖ < r := by simpa only [dist_eq_norm] using hball z hz
    have := mul_lt_mul_of_pos_left hz' (div_pos (by norm_num : (0 : ℝ) < 2) hr)
    have hmul : (2 / r) * r = 2 := div_mul_cancel₀ 2 hr.ne'
    rw [hmul] at this
    exact this.le
  have hs : ∀ c ∈ s.image f, ∀ d ∈ s.image f, c ≠ d → 1 ≤ ‖c - d‖ := by
    intro c hc d hd hcd
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hd
    have hab : a ≠ b := fun h => hcd (congrArg f h)
    have hab' : r / 2 < ‖a - b‖ := by simpa only [dist_eq_norm] using hsep a ha b hb hab
    have hdiff : f a - f b = (2 / r) • (a - b) := by dsimp [f]; rw [← smul_sub]; congr 1; abel
    rw [hdiff, norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 2 / r)]
    have := mul_lt_mul_of_pos_left hab' (div_pos (by norm_num : (0 : ℝ) < 2) hr)
    have hmul : (2 / r) * (r / 2) = 1 := by field_simp
    rw [hmul] at this
    exact this.le
  have := Besicovitch.card_le_multiplicity hb hs
  rwa [Finset.card_image_of_injective _ hf] at this

namespace DyadicBandCover
variable {K : Set E} {τ : ℝ} (D : DyadicBandCover K τ)

theorem card_active_centers_le (hτ : 0 < τ) (x : E) (j : ℕ) :
    ((D.centers j).filter fun z => x ∈ ball z (dyadicRadius τ j)).card ≤
      Besicovitch.multiplicity E := by
  classical
  apply card_le_multiplicity_of_half_radius_separated _ x _ (dyadicRadius_pos hτ j)
  · intro z hz
    have := (Finset.mem_filter.mp hz).2
    simpa only [mem_ball, dist_comm z x] using this
  · intro a ha b hb hab
    exact D.separated j a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1 hab

/-- The active vertices at a fixed level obey the same packing bound. -/
theorem card_active_level_le (hτ : 0 < τ) (s : Finset D.Index) (x : E)
    (hs : ∀ i ∈ s, x ∈ D.coverBall i) (j : ℕ) :
    (s.filter fun i => i.1 = j).card ≤ Besicovitch.multiplicity E := by
  classical
  let t := s.filter fun i => i.1 = j
  let f : D.Index → E := fun i => i.2.1
  have hinj : Set.InjOn f t := by
    intro i hi k hk heq
    have hi' := (Finset.mem_filter.mp hi).2
    have hk' := (Finset.mem_filter.mp hk).2
    have hlev : i.1 = k.1 := hi'.trans hk'.symm
    cases i with
    | mk i z =>
      cases k with
      | mk k w =>
        dsimp at hlev
        subst k
        have hzw : z = w := Subtype.ext heq
        subst w
        rfl
  have hsub : t.image f ⊆ (D.centers j).filter fun z => x ∈ ball z (dyadicRadius τ j) := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨his, hij⟩ := Finset.mem_filter.mp hi
    apply Finset.mem_filter.mpr
    constructor
    · simpa only [f, hij] using i.2.2
    · simpa only [coverBall, f, hij] using hs i his
  calc
    (s.filter fun i => i.1 = j).card = (t.image f).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ ((D.centers j).filter fun z => x ∈ ball z (dyadicRadius τ j)).card :=
      Finset.card_le_card hsub
    _ ≤ Besicovitch.multiplicity E := D.card_active_centers_le hτ x j

/-- Every finite family of balls through one point has a uniform cardinal bound. -/
theorem card_of_common_point_le (hτ : 0 < τ) (s : Finset D.Index) (x : E)
    (hs : ∀ i ∈ s, x ∈ D.coverBall i) :
    s.card ≤ 4 * Besicovitch.multiplicity E := by
  classical
  by_cases hse : s.Nonempty
  · let L : Finset ℕ := s.image Sigma.fst
    have hL : L.Nonempty := Finset.Nonempty.image hse _
    let l : ℕ := L.min' hL
    obtain ⟨k, hk, hkl⟩ := Finset.mem_image.mp (L.min'_mem hL)
    have hLsub : L ⊆ Finset.Ico l (l + 4) := by
      intro j hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      apply Finset.mem_Ico.mpr
      constructor
      · exact Finset.min'_le L i.1 hj
      · have h := D.levels_near (hs i hi) (hs k hk)
        simpa only [hkl] using h
    have hcardL : L.card ≤ 4 := by
      calc
        L.card ≤ (Finset.Ico l (l + 4)).card := Finset.card_le_card hLsub
        _ = 4 := by simp
    calc
      s.card = ∑ j ∈ L, (s.filter fun i => i.1 = j).card :=
        Finset.card_eq_sum_card_image Sigma.fst s
      _ ≤ ∑ _j ∈ L, Besicovitch.multiplicity E := by
        apply Finset.sum_le_sum
        intro j _
        exact D.card_active_level_le hτ s x hs j
      _ = L.card * Besicovitch.multiplicity E := by simp
      _ ≤ 4 * Besicovitch.multiplicity E := Nat.mul_le_mul_right _ hcardL
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hse, Finset.card_empty, zero_le]

end DyadicBandCover
end Packing
end P202.Duality

noncomputable section
open Set Metric
open Classical
namespace P202.Duality
section Packing
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

namespace DyadicBandCover
variable {K : Set E} {τ : ℝ} (D : DyadicBandCover K τ)

/-- A dimension-only bound for the multiplicity of the shrinking cover. -/
theorem card_of_common_point_le_pow (hτ : 0 < τ) (s : Finset D.Index) (x : E)
    (hs : ∀ i ∈ s, x ∈ D.coverBall i) :
    s.card ≤ 4 * 5 ^ Module.finrank ℝ E :=
  (D.card_of_common_point_le hτ s x hs).trans
    (Nat.mul_le_mul_left 4 (Besicovitch.multiplicity_le (E := E)))

/-- Choose a nearest point of the compact set for every cover vertex. -/
theorem exists_nearest_points (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ p : D.Index → K, ∀ i, dist i.2.1 (p i).1 = infDist i.2.1 K := by
  have hex : ∀ i : D.Index, ∃ p : K, dist i.2.1 p.1 = infDist i.2.1 K := by
    intro i
    obtain ⟨p, hp, heq⟩ := hK.exists_infDist_eq_dist hne i.2.1
    exact ⟨⟨p, hp⟩, heq.symm⟩
  exact Classical.skolem.mp hex

/-- Vertex images stay close to every point of their cover ball. -/
theorem nearest_point_dist_lt {p : D.Index → K}
    (hp : ∀ i, dist i.2.1 (p i).1 = infDist i.2.1 K)
    {i : D.Index} {x : E} (hx : x ∈ D.coverBall i) :
    dist (p i).1 x < 9 * dyadicRadius τ i.1 := by
  have hdist := dist_triangle (p i).1 i.2.1 x
  have hband := (D.band i.1 i.2.1 i.2.2).2
  change dist x i.2.1 < dyadicRadius τ i.1 at hx
  rw [dist_comm (p i).1 i.2.1, hp i, dist_comm i.2.1 x] at hdist
  linarith

end DyadicBandCover
end Packing
end P202.Duality

noncomputable section
open Set Topology Metric ContinuousMap
namespace P202.Duality

/-- Positive bounds may be replaced by decreasing positive bounds. -/
theorem exists_antitone_positive_minorant (a : ℕ → ℝ) (ha : ∀ k, 0 < a k) :
    ∃ b : ℕ → ℝ, (∀ k, 0 < b k) ∧ Antitone b ∧ ∀ k, b k ≤ a k := by
  let b : ℕ → ℝ := fun k => (Finset.range (k + 1)).inf' (by simp) a
  have hb (k) : 0 < b k := by
    exact (Finset.lt_inf'_iff (by simp)).mpr (fun j _ => ha j)
  refine ⟨b, hb, ?_, ?_⟩
  · intro i j hij
    apply (Finset.le_inf'_iff (by simp) a).mpr
    intro k hk
    exact Finset.inf'_le a ((Finset.range_mono (Nat.succ_le_succ hij)) hk)
  · intro k
    exact Finset.inf'_le _ (by simp)

/-- Scale-dependent diameter bounds for a finite skeletal induction. The first
index counts downward from the top dimension. -/
theorem exists_skeletal_diameter_bounds (δ : ℝ → ℝ)
    (hδ : ∀ ε > 0, 0 < δ ε) (_m : ℕ) :
    ∃ e : ℕ → ℕ → ℝ,
      (∀ j k, 0 < e j k) ∧
      (∀ j, Antitone (e j)) ∧
      (∀ j k, e j k ≤ (1 / 2 : ℝ) ^ k) ∧
      (∀ j k, 2 * e (j + 1) k < δ (e j k)) := by
  have hstep (a : ℕ → ℝ) (ha : ∀ k, 0 < a k) :
      ∃ b : ℕ → ℝ, (∀ k, 0 < b k) ∧ Antitone b ∧
        (∀ k, b k ≤ (1 / 2 : ℝ) ^ k) ∧ ∀ k, 2 * b k < δ (a k) := by
    obtain ⟨b, hb, hmono, hle⟩ := exists_antitone_positive_minorant
      (fun k => min ((1 / 2 : ℝ) ^ k) (δ (a k) / 4)) (fun k =>
        lt_min (pow_pos (by norm_num) _) (div_pos (hδ _ (ha k)) (by norm_num)))
    refine ⟨b, hb, hmono, fun k => (hle k).trans (min_le_left _ _), ?_⟩
    intro k
    have := (hle k).trans (min_le_right _ _)
    linarith [hδ _ (ha k)]
  choose next hnext_pos hnext_mono hnext_le hnext_small using hstep
  let A := {a : ℕ → ℝ // ∀ k, 0 < a k}
  let eA : ℕ → A := Nat.rec ⟨fun k => (1 / 2 : ℝ) ^ k,
      fun k => pow_pos (by norm_num) k⟩
    (fun _ a => ⟨next a.1 a.2, hnext_pos a.1 a.2⟩)
  let e : ℕ → ℕ → ℝ := fun j => (eA j).1
  have hpos (j) : ∀ k, 0 < e j k := (eA j).2
  have hrec (j) : e (j+1) = next (e j) (hpos j) := by rfl
  refine ⟨e, hpos, ?_, ?_, ?_⟩
  · intro j
    cases j with
    | zero => exact fun i k hik => pow_le_pow_of_le_one (by norm_num) (by norm_num) hik
    | succ j => rw [hrec]; exact hnext_mono (e j) (hpos j)
  · intro j k
    cases j with
    | zero => exact le_rfl
    | succ j => rw [hrec]; exact hnext_le (e j) (hpos j) k
  · intro j k
    rw [hrec]
    exact hnext_small (e j) (hpos j) k


/-- Reversing the downward bounds gives the bounds in increasing simplex dimension. -/
theorem exists_finite_skeletal_diameter_bounds (δ : ℝ → ℝ)
    (hδ : ∀ ε > 0, 0 < δ ε) (m : ℕ) :
    ∃ ε : ℕ → ℕ → ℝ,
      (∀ d k, 0 < ε d k) ∧
      (∀ d, Antitone (ε d)) ∧
      (∀ d k, ε d k ≤ (1 / 2 : ℝ) ^ k) ∧
      (∀ d < m, ∀ k, 2 * ε d k < δ (ε (d + 1) k)) := by
  obtain ⟨e, hpos, hmono, hle, hsmall⟩ := exists_skeletal_diameter_bounds δ hδ m
  refine ⟨fun d k => e (m - d) k, fun d k => hpos _ _,
    fun d => hmono _, fun d k => hle _ _, ?_⟩
  intro d hd k
  have heq : m - d = (m - (d + 1)) + 1 := by omega
  simpa only [heq] using hsmall (m - (d + 1)) k

/-- Positive upper bounds admit a strictly decreasing cutoff sequence tending to zero. -/
theorem exists_strictAnti_positive_cutoffs (a : ℕ → ℝ) (ha : ∀ k, 0 < a k) :
    ∃ τ : ℕ → ℝ, (∀ k, 0 < τ k) ∧ StrictAnti τ ∧
      (∀ k, τ k ≤ a k) ∧ Filter.Tendsto τ Filter.atTop (𝓝 0) := by
  obtain ⟨b, hb, hmono, hle⟩ := exists_antitone_positive_minorant a ha
  let τ : ℕ → ℝ := fun k => b k * (1 / 2 : ℝ) ^ k
  have hτ (k) : 0 < τ k := mul_pos (hb k) (pow_pos (by norm_num) k)
  have hanti : StrictAnti τ := by
    apply strictAnti_nat_of_succ_lt
    intro k
    have hbk := hmono (Nat.le_succ k)
    have hpow : 0 < (1 / 2 : ℝ) ^ k := pow_pos (by norm_num) k
    dsimp [τ]
    rw [pow_succ]
    nlinarith [mul_le_mul_of_nonneg_right hbk hpow.le,
      mul_pos (hb k) hpow]
  refine ⟨τ, hτ, hanti, ?_, ?_⟩
  · intro k
    calc
      τ k = b k * (1 / 2 : ℝ) ^ k := rfl
      _ ≤ b k * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ (by norm_num) (by norm_num)) (hb k).le
      _ ≤ a k := by simpa only [mul_one] using hle k
  · have hbound (k) : τ k ≤ b 0 * (1 / 2 : ℝ) ^ k :=
      mul_le_mul_of_nonneg_right (hmono (Nat.zero_le k)) (by positivity)
    apply squeeze_zero (fun k => (hτ k).le) hbound
    have hp : Filter.Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) Filter.atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa only [mul_zero] using hp.const_mul (b 0)

end P202.Duality

noncomputable section
open Set Topology Metric ContinuousMap Convexity

namespace P202.Duality

/-- The support of a point in a finite chart consists of vertices of that chart. -/
theorem simplex_map_val_support_subset {V : Type*} (s : Finset V) (p : StdSimplex ℝ s) :
    (p.map (Subtype.val : s → V)).weights.support ⊆ s := by
  classical
  rw [StdSimplex.weights_map,
    Finsupp.mapDomain_support_of_injective Subtype.val_injective]
  intro v hv
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
  exact w.2

theorem simplex_map_val_support_card {V : Type*} (s : Finset V) (p : StdSimplex ℝ s) :
    (p.map (Subtype.val : s → V)).weights.support.card = p.weights.support.card := by
  classical
  rw [StdSimplex.weights_map,
    Finsupp.mapDomain_support_of_injective Subtype.val_injective,
    Finset.card_image_of_injective _ Subtype.val_injective]

/-- An injective map of vertices induces an injective map of barycentric points. -/
theorem simplex_map_injective {V W : Type*} (f : V → W) (hf : Function.Injective f) :
    Function.Injective (StdSimplex.map (R := ℝ) f) := by
  intro p q hpq
  apply StdSimplex.ext
  exact Finsupp.mapDomain_injective hf (congrArg StdSimplex.weights hpq)

/-- The continuous inclusion of one finite barycentric simplex into another. -/
def simplexFinsetInclusion {V : Type*} {s t : Finset V} (h : s ⊆ t) :
    C(StdSimplex ℝ s, StdSimplex ℝ t) :=
  ⟨StdSimplex.map (fun v : s => (⟨v.1, h v.2⟩ : t)),
    StdSimplex.continuous_map ℝ _⟩

@[simp]
theorem simplexFinsetInclusion_map_val {V : Type*} {s t : Finset V} (h : s ⊆ t)
    (p : StdSimplex ℝ s) :
    (simplexFinsetInclusion h p).map (Subtype.val : t → V) = p.map Subtype.val := by
  exact (StdSimplex.map_comp p (fun v : s => (⟨v.1, h v.2⟩ : t)) Subtype.val).symm

/-- Restriction to nested finite charts commutes with the chart inclusion. -/
theorem simplexFinsetInclusion_restrict {V : Type*} (p : StdSimplex ℝ V)
    {s t : Finset V} (h : s ⊆ t) (hs : p.weights.support ⊆ s)
    (ht : p.weights.support ⊆ t) :
    simplexFinsetInclusion h (simplexRestrictToFinset p s hs) =
      simplexRestrictToFinset p t ht := by
  apply simplex_map_injective (Subtype.val : t → V) Subtype.val_injective
  simp

@[simp]
theorem simplexFinsetInclusion_self {V : Type*} (s : Finset V)
    (p : StdSimplex ℝ s) : simplexFinsetInclusion (s := s) (t := s) subset_rfl p = p := by
  change p.map _ = p
  simpa only [StdSimplex.map_id] using congrArg (fun f : s → s => p.map f)
    (show (fun v : s => (⟨v.1, v.2⟩ : s)) = id from rfl)

@[simp]
theorem simplexFinsetInclusion_comp {V : Type*} {s t u : Finset V}
    (hst : s ⊆ t) (htu : t ⊆ u) (p : StdSimplex ℝ s) :
    simplexFinsetInclusion htu (simplexFinsetInclusion hst p) =
      simplexFinsetInclusion (hst.trans htu) p := by
  exact (StdSimplex.map_comp p
    (fun v : s => (⟨v.1, hst v.2⟩ : t))
    (fun v : t => (⟨v.1, htu v.2⟩ : u))).symm

/-- A boundary point has fewer active barycentric coordinates than vertices. -/
theorem simplexBoundary_support_card_lt {V : Type*} [Fintype V]
    (p : simplexBoundary V) : p.1.weights.support.card < Fintype.card V := by
  classical
  obtain ⟨i, hi⟩ := p.2
  have hnot : i ∉ p.1.weights.support := Finsupp.notMem_support_iff.mpr hi
  have hstrict : p.1.weights.support ⊂ Finset.univ := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, ?_⟩
    intro heq
    exact hnot (heq.symm ▸ Finset.mem_univ i)
  simpa using Finset.card_lt_card hstrict

/-- The boundary of a finite chart belongs to the preceding support skeleton. -/
theorem simplexBoundary_chart_support_card_lt {V : Type*} (s : Finset V)
    (p : simplexBoundary s) :
    (p.1.map (Subtype.val : s → V)).weights.support.card < s.card := by
  rw [simplex_map_val_support_card]
  simpa using simplexBoundary_support_card_lt p

end P202.Duality

noncomputable section
open Set Topology Convexity Function

namespace P202.Duality
variable {ι X : Type*} [TopologicalSpace X]

noncomputable def partitionSimplex (ρ : PartitionOfUnity ι X univ) (x : X) :
    StdSimplex ℝ ι where
  weights := Finsupp.ofSupportFinite (fun i => ρ i x) (ρ.locallyFinite.point_finite x)
  nonneg i := ρ.nonneg i x
  total := by
    change ∑ i ∈ ρ.finsupport x, ρ i x = 1
    exact ρ.sum_finsupport (mem_univ x)

@[simp] theorem partitionSimplex_weights (ρ : PartitionOfUnity ι X univ) (x : X) (i : ι) :
    (partitionSimplex ρ x).weights i = ρ i x := rfl

/-- A family of points of a weak simplex is continuous if its coordinate
functions are continuous and locally all supports lie in one finite set. -/
theorem continuous_simplex_of_locally_finite_support (f : X → StdSimplex ℝ ι)
    (hc : ∀ i, Continuous (fun x => (f x).weights i))
    (hloc : ∀ x : X, ∃ I : Finset ι, ∀ᶠ y in 𝓝 x, (f y).weights.support ⊆ I) :
    Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨I, hI⟩ := hloc x
  let A : Set X := {y | (f y).weights.support ⊆ I}
  have hA : A ∈ 𝓝 x := hI
  have hcont : Continuous (fun y : A => simplexRestrictToFinset (f y) I y.2) := by
    apply (StdSimplex.isEmbedding_toFun_comp_weights ℝ I).continuous_iff.mpr
    apply continuous_pi
    intro i
    exact (hc i).comp continuous_subtype_val
  have hh : Continuous (fun y : A => f y.1) := by
    convert (StdSimplex.continuous_map ℝ (Subtype.val : I → ι)).comp hcont using 1
    funext y
    exact (simplexRestrictToFinset_map_val (f y.1) I y.2).symm
  exact ((continuousOn_iff_continuous_domRestrict.mpr hh) x (mem_of_mem_nhds hA)).continuousAt hA

 theorem continuous_partitionSimplex (ρ : PartitionOfUnity ι X univ) :
    Continuous (partitionSimplex ρ) := by
  apply continuous_simplex_of_locally_finite_support
  · intro i
    exact (ρ i).continuous
  · intro x
    refine ⟨ρ.fintsupport x, ?_⟩
    apply (ρ.eventually_finsupport_subset x).mono
    intro y hy
    exact hy

/-- Simplexwise continuity suffices after a map with locally finite
barycentric supports. The finite set of vertices occurring near a point need
not itself span a simplex. -/
theorem continuous_comp_of_simplexwise {Y : Type*} [TopologicalSpace Y]
    (S : Set (Finset ι)) (F : StdSimplex ℝ ι → Y) (b : X → StdSimplex ℝ ι)
    (hF : ∀ s ∈ S, Continuous (F ∘ StdSimplex.map (Subtype.val : s → ι)))
    (hb : ∀ i, Continuous (fun x => (b x).weights i))
    (hloc : ∀ x : X, ∃ I : Finset ι, ∀ᶠ y in 𝓝 x, (b y).weights.support ⊆ I)
    (hS : ∀ x, (b x).weights.support ∈ S) : Continuous (F ∘ b) := by
  classical
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨I, hI⟩ := hloc x
  let A : Set X := {y | (b y).weights.support ⊆ I}
  have hA : A ∈ 𝓝 x := hI
  let J := {s : Finset ι // s ⊆ I ∧ s ∈ S}
  have : Finite J := Finite.of_injective
    (fun s : J => (⟨s.1, Finset.mem_powerset.mpr s.2.1⟩ : I.powerset))
    (fun a c h => Subtype.ext (congrArg (fun z : I.powerset => z.1) h))
  let U (s : J) : Set A := {y | (b y.1).weights.support ⊆ s.1}
  have hUclosed (s : J) : IsClosed (U s) := by
    have heq : U s = ⋂ i : {i : ι // i ∉ s.1},
        {y : A | (b y.1).weights i.1 = 0} := by
      ext y
      simp only [U, mem_ofPred_eq, mem_iInter]
      constructor
      · intro hy i
        exact Finsupp.notMem_support_iff.mp (fun hi => i.2 (hy hi))
      · intro hy i hi
        by_contra his
        exact Finsupp.mem_support_iff.mp hi (hy ⟨i, his⟩)
    rw [heq]
    exact isClosed_iInter (fun i => isClosed_eq ((hb i.1).comp continuous_subtype_val)
      continuous_const)
  have hUcover : ⋃ s : J, U s = univ := by
    apply eq_univ_of_forall
    intro y
    exact mem_iUnion.mpr ⟨⟨(b y.1).weights.support, y.2, hS y.1⟩, Finset.Subset.refl _⟩
  have hUcont (s : J) : ContinuousOn (fun y : A => F (b y.1)) (U s) := by
    rw [continuousOn_iff_continuous_domRestrict]
    let c : U s → StdSimplex ℝ s.1 := fun y =>
      simplexRestrictToFinset (b y.1.1) s.1 y.2
    have hc : Continuous c := by
      apply (StdSimplex.isEmbedding_toFun_comp_weights ℝ s.1).continuous_iff.mpr
      apply continuous_pi
      intro i
      exact ((hb i).comp continuous_subtype_val).comp continuous_subtype_val
    convert (hF s.1 s.2.2).comp hc using 1
    funext y
    exact congrArg F (simplexRestrictToFinset_map_val (b y.1.1) s.1 y.2).symm
  have hh : Continuous (fun y : A => F (b y.1)) :=
    (locallyFinite_of_finite U).continuous hUcover hUclosed hUcont
  exact ((continuousOn_iff_continuous_domRestrict.mpr hh) x
    (mem_of_mem_nhds hA)).continuousAt hA

/-- The preceding criterion applied to the barycentric coordinates of a
partition of unity. -/
theorem continuous_partition_comp_of_simplexwise {Y : Type*} [TopologicalSpace Y]
    (S : Set (Finset ι)) (F : StdSimplex ℝ ι → Y)
    (ρ : PartitionOfUnity ι X univ)
    (hF : ∀ s ∈ S, Continuous (F ∘ StdSimplex.map (Subtype.val : s → ι)))
    (hS : ∀ x, (partitionSimplex ρ x).weights.support ∈ S) :
    Continuous (F ∘ partitionSimplex ρ) := by
  apply continuous_comp_of_simplexwise S F _ hF (fun i => (ρ i).continuous) _ hS
  intro x
  refine ⟨ρ.fintsupport x, ?_⟩
  exact ρ.eventually_finsupport_subset x

/-- A locally finite open cover admits continuous finite barycentric
coordinates subordinate to its members. -/
theorem exists_barycentric_coordinates [NormalSpace X] (U : ι → Set X)
    (ho : ∀ i, IsOpen (U i)) (hl : LocallyFinite U) (hcov : univ ⊆ ⋃ i, U i) :
    ∃ b : X → StdSimplex ℝ ι,
      Continuous b ∧
      (∀ i, Continuous (fun x => (b x).weights i)) ∧
      (∀ x : X, ∃ I : Finset ι, ∀ᶠ y in 𝓝 x, (b y).weights.support ⊆ I) ∧
      ∀ x i, i ∈ (b x).weights.support → x ∈ U i := by
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate_of_locallyFinite
    isClosed_univ U ho hl hcov
  refine ⟨partitionSimplex ρ, continuous_partitionSimplex ρ,
    (fun i => (ρ i).continuous), ?_, ?_⟩
  · intro x
    exact ⟨ρ.fintsupport x, ρ.eventually_finsupport_subset x⟩
  · intro x i hi
    apply hρ i
    apply subset_closure
    exact Finsupp.mem_support_iff.mp hi

end P202.Duality

noncomputable section
open Set Topology Metric ContinuousMap Convexity
open Classical
namespace P202.Duality

/-- An initial map of all barycentric points, prescribed on every vertex.
Only its restriction to the zero skeleton is used before extension. -/
def simplexVertexExtension {V X : Type*} (v : V → X) (p : StdSimplex ℝ V) : X :=
  v (Classical.choose p.support_weights_nonempty)

@[simp]
theorem simplexVertexExtension_single {V X : Type*} (v : V → X) (i : V) :
    simplexVertexExtension v (.single i) = v i := by
  have hi := Classical.choose_spec (StdSimplex.support_weights_nonempty
    (StdSimplex.single (R := ℝ) i))
  have heq : Classical.choose (StdSimplex.single (R := ℝ) i).support_weights_nonempty = i := by
    simpa using hi
  exact congrArg v heq

/-- On a chart with one vertex, the initial map is constant at that vertex. -/
theorem simplexVertexExtension_chart_eq {V X : Type*} (v : V → X) (s : Finset V)
    (hs : s.card = 1) :
    ∃ i ∈ s, ∀ p : StdSimplex ℝ s,
      simplexVertexExtension v (p.map (Subtype.val : s → V)) = v i := by
  obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hs
  refine ⟨i, by simp, ?_⟩
  intro p
  have heq : p = StdSimplex.single (⟨i, by simp⟩ : ({i} : Finset V)) := Subsingleton.elim _ _
  rw [heq, StdSimplex.map_single, simplexVertexExtension_single]

/-- The initial map is continuous on every zero-dimensional chart, including
an empty chart. -/
theorem continuous_simplexVertexExtension_chart {V X : Type*} [TopologicalSpace X]
    (v : V → X) (s : Finset V) (hs : s.card ≤ 1) :
    Continuous (simplexVertexExtension v ∘ StdSimplex.map (Subtype.val : s → V)) := by
  letI : Subsingleton s := Finset.card_le_one_iff_subsingleton_coe.mp hs
  exact continuous_of_discreteTopology

/-- A boundary point of a one-dimensional simplex is one of its vertices. -/
theorem simplexBoundary_eq_single_of_card_two {V : Type*} [Fintype V]
    (hcard : Fintype.card V = 2) (p : simplexBoundary V) :
    ∃ i : V, p.1 = StdSimplex.single i := by
  obtain ⟨i, hi⟩ := p.2
  have hsub : p.1.weights.support ⊆ Finset.univ.erase i := by
    intro j hj
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
    intro hji
    subst j
    exact (Finsupp.mem_support_iff.mp hj) hi
  have hle : p.1.weights.support.card ≤ 1 := by
    have h := Finset.card_le_card hsub
    simpa [Finset.card_erase_of_mem (Finset.mem_univ i), hcard] using h
  have hpos : 0 < p.1.weights.support.card :=
    Finset.card_pos.mpr p.1.support_weights_nonempty
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp (by omega : p.1.weights.support.card = 1)
  exact ⟨j, StdSimplex.support_weights_eq_singleton.mp hj⟩

/-- The boundary of a two-vertex finite chart maps into its ambient vertices. -/
theorem simplexBoundary_chart_eq_single_of_card_two {V : Type*} (s : Finset V)
    (hcard : s.card = 2) (p : simplexBoundary s) :
    ∃ i ∈ s, p.1.map (Subtype.val : s → V) = StdSimplex.single i := by
  obtain ⟨i, hi⟩ := simplexBoundary_eq_single_of_card_two (by simpa using hcard) p
  exact ⟨i.1, i.2, by rw [hi, StdSimplex.map_single]⟩

/-- On an edge, control of the two assigned vertex images controls the whole
boundary map before applying the small-extension theorem. -/
theorem simplexBoundary_edge_dist_lt {V X : Type*} [MetricSpace X]
    (s : Finset V) (hcard : s.card = 2) (F : StdSimplex ℝ V → X) (v : V → X)
    (hF : ∀ i : V, F (StdSimplex.single i) = v i) (δ : ℝ)
    (hvertex : ∀ i ∈ s, ∀ j ∈ s, dist (v i) (v j) < δ)
    (p q : simplexBoundary s) :
    dist (F (p.1.map (Subtype.val : s → V)))
      (F (q.1.map (Subtype.val : s → V))) < δ := by
  obtain ⟨i, his, hi⟩ := simplexBoundary_chart_eq_single_of_card_two s hcard p
  obtain ⟨j, hjs, hj⟩ := simplexBoundary_chart_eq_single_of_card_two s hcard q
  rw [hi, hj, hF i, hF j]
  exact hvertex i his j hjs

end P202.Duality

noncomputable section
open Set Topology Metric ContinuousMap Convexity
namespace P202.Duality
open Classical

/-- The support of a finite-simplex chart lies in its vertex set. -/
theorem simplexChart_support_subset {V : Type*} (s : Finset V) (p : StdSimplex ℝ s) :
    (p.map (Subtype.val : s → V)).weights.support ⊆ s := by
  intro v hv
  obtain ⟨w, _, hw⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hv)
  exact hw ▸ w.2

/-- A coordinate face has ambient support in the vertex set with that vertex
removed. -/
theorem simplexFace_chart_support {V : Type*} (s : Finset V) (i : s)
    (p : simplexFace s i) :
    (p.1.map (Subtype.val : s → V)).weights.support ⊆ s.erase i.1 := by
  intro v hv
  apply Finset.mem_erase.mpr
  refine ⟨?_, simplexChart_support_subset s p.1 hv⟩
  intro hvi
  subst v
  have heq : (p.1.map (Subtype.val : s → V)).weights i.1 = p.1.weights i :=
    Finsupp.mapDomain_apply_of_injective Subtype.val_injective _ i
  exact (Finsupp.mem_support_iff.mp hv) (heq.trans p.2)

/-- Simplexwise continuity on the codimension-one faces implies continuity of
the ambient function restricted to a simplex boundary. -/
theorem continuous_simplexBoundary_of_faces {V X : Type*} [TopologicalSpace X]
    (F : StdSimplex ℝ V → X) (s : Finset V)
    (hc : ∀ i : s, Continuous (F ∘ StdSimplex.map (Subtype.val : s.erase i.1 → V))) :
    Continuous (fun p : simplexBoundary s => F (p.1.map (Subtype.val : s → V))) := by
  have hface (i : s) : Continuous
      (fun p : simplexFace s i => F (p.1.map (Subtype.val : s → V))) := by
    have hres := continuous_simplexRestrictToFinset (s.erase i.1)
      (fun p : simplexFace s i => p.1.map (Subtype.val : s → V))
      ((StdSimplex.continuous_map ℝ (Subtype.val : s → V)).comp continuous_subtype_val)
      (simplexFace_chart_support s i)
    convert (hc i).comp hres using 1
    funext p
    exact congrArg F (simplexRestrictToFinset_map_val _ _ _).symm
  let f (i : s) : C(simplexFace s i, X) := ⟨_, hface i⟩
  obtain ⟨g, hg, _⟩ := glue_simplexBoundary f (by
    intro i j p q hpq
    exact congrArg (fun p : StdSimplex ℝ s => F (p.map Subtype.val)) hpq)
  convert g.continuous using 1
  funext p
  obtain ⟨i, hi⟩ := p.2
  exact (hg i ⟨p.1, hi⟩).symm

/-- If all proper faces already belong to the previous skeleton, its map
restricts continuously to the boundary of each next-dimensional simplex. -/
theorem continuous_simplexBoundary_of_skeleton {V X : Type*} [TopologicalSpace X]
    (S : Set (Finset V))
    (hS : ∀ s ∈ S, ∀ t ⊆ s, t.Nonempty → t ∈ S)
    (F : StdSimplex ℝ V → X) (d : ℕ)
    (hc : ∀ s ∈ S, s.card ≤ d → Continuous (F ∘ StdSimplex.map (Subtype.val : s → V)))
    (s : Finset V) (hs : s ∈ S) (hcard : s.card = d+1) (hd : 0 < d) :
    Continuous (fun p : simplexBoundary s => F (p.1.map (Subtype.val : s → V))) := by
  apply continuous_simplexBoundary_of_faces
  intro i
  have hcard' : (s.erase i.1).card = d := by rw [Finset.card_erase_of_mem i.2, hcard]; omega
  exact hc _ (hS s hs _ (Finset.erase_subset _ _) (Finset.card_pos.mp (by omega))) (by omega)

/-- Replace a function on the next skeleton by chosen extensions on its
maximal simplices. The extensions agree with the old function on boundaries,
so evaluation on every maximal chart is exactly its chosen extension. -/
def extendSkeletonFunction {V X : Type*} (S : Set (Finset V)) (d : ℕ)
    (F : StdSimplex ℝ V → X)
    (G : ∀ (s : Finset V), s ∈ S → s.card = d+1 → StdSimplex ℝ s → X)
    (p : StdSimplex ℝ V) : X :=
  if h : p.weights.support ∈ S ∧ p.weights.support.card = d+1 then
    G p.weights.support h.1 h.2 (simplexRestrictToFinset p p.weights.support Finset.Subset.rfl)
  else F p

@[simp] theorem extendSkeletonFunction_old {V X : Type*}
    (S : Set (Finset V)) (d : ℕ) (F : StdSimplex ℝ V → X)
    (G : ∀ (s : Finset V), s ∈ S → s.card = d+1 → StdSimplex ℝ s → X)
    (p : StdSimplex ℝ V) (hp : p.weights.support.card ≤ d) :
    extendSkeletonFunction S d F G p = F p := by
  simp only [extendSkeletonFunction]
  rw [dite_eq_right]
  omega

/-- On a newly filled closed simplex, the new function is its selected
extension, including all proper faces. -/
theorem extendSkeletonFunction_chart {V X : Type*}
    (S : Set (Finset V)) (d : ℕ) (F : StdSimplex ℝ V → X)
    (G : ∀ (s : Finset V), s ∈ S → s.card = d+1 → StdSimplex ℝ s → X)
    (hG : ∀ (s : Finset V) (hs : s ∈ S) (hc : s.card = d+1)
      (p : simplexBoundary s), G s hs hc p.1 = F (p.1.map (Subtype.val : s → V)))
    (s : Finset V) (hs : s ∈ S) (hc : s.card = d+1) (p : StdSimplex ℝ s) :
    extendSkeletonFunction S d F G (p.map (Subtype.val : s → V)) = G s hs hc p := by
  let q := p.map (Subtype.val : s → V)
  have hsub : q.weights.support ⊆ s := simplexChart_support_subset s p
  by_cases hfull : q.weights.support = s
  · have hrestrict : simplexRestrictToFinset q s hsub = p :=
      simplexRestrictToFinset_chart s p hsub
    have hcalc : extendSkeletonFunction S d F G q =
        G s hs hc (simplexRestrictToFinset q s hsub) := by
      unfold extendSkeletonFunction
      split
      · rename_i h
        have htransport (t u : Finset V) (heq : t = u)
            (ht : t ∈ S) (htc : t.card = d+1) (hu : u ∈ S) (huc : u.card = d+1)
            (hqt : q.weights.support ⊆ t) (hqu : q.weights.support ⊆ u) :
            G t ht htc (simplexRestrictToFinset q t hqt) =
              G u hu huc (simplexRestrictToFinset q u hqu) := by
          subst u
          rfl
        exact htransport _ _ hfull h.1 h.2 hs hc Finset.Subset.rfl hsub
      · rename_i h
        exact (h ⟨hfull.symm ▸ hs, by simpa only [hfull] using hc⟩).elim
    exact hcalc.trans (congrArg (G s hs hc) hrestrict)
  · have hlt : q.weights.support.card < s.card :=
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hfull⟩)
    rw [extendSkeletonFunction_old S d F G q (by omega)]
    have hboundary : ∃ i : s, p.weights i = 0 := by
      obtain ⟨i, his, hi⟩ := Finset.exists_of_ssubset
        (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hfull⟩)
      refine ⟨⟨i, his⟩, ?_⟩
      have hzero := Finsupp.notMem_support_iff.mp hi
      have hw : q.weights i = p.weights ⟨i, his⟩ :=
        Finsupp.mapDomain_apply_of_injective Subtype.val_injective _ ⟨i, his⟩
      exact hw.symm.trans hzero
    exact (hG s hs hc ⟨p, hboundary⟩).symm

end P202.Duality

noncomputable section
open Set Topology Metric ContinuousMap Filter
open Classical
namespace P202.Duality

/-- The largest cutoff level containing every scale of a finite family.
The empty family and a family fitting no cutoff receive the harmless value zero. -/
def cutoffRank {V : Type*} (t : ℕ → ℝ) (r : V → ℝ) (s : Finset V) : ℕ :=
  if s.Nonempty then sSup {k : ℕ | ∀ i ∈ s, r i ≤ t k} else 0

/-- Positive scales and cutoffs tending to zero leave only finitely many admissible levels. -/
theorem finite_cutoff_levels {V : Type*} (t : ℕ → ℝ) (r : V → ℝ)
    (ht : Tendsto t atTop (𝓝 0)) (hr : ∀ i, 0 < r i) (s : Finset V)
    (hs : s.Nonempty) : {k : ℕ | ∀ i ∈ s, r i ≤ t k}.Finite := by
  obtain ⟨i, hi⟩ := hs
  have hsmall : ∀ᶠ k in atTop, t k < r i := ht.eventually (gt_mem_nhds (hr i))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hsmall
  apply (finite_lt_nat N).subset
  intro k hk
  by_contra h
  have hlarge : N ≤ k := Nat.le_of_not_gt h
  exact (hN k hlarge).not_ge (hk i hi)

/-- Every admissible level is below the chosen maximum. -/
theorem le_cutoffRank {V : Type*} (t : ℕ → ℝ) (r : V → ℝ)
    (ht : Tendsto t atTop (𝓝 0)) (hr : ∀ i, 0 < r i) (s : Finset V)
    (hs : s.Nonempty) {k : ℕ} (hk : ∀ i ∈ s, r i ≤ t k) :
    k ≤ cutoffRank t r s := by
  unfold cutoffRank
  rw [ite_eq_left hs]
  exact le_csSup (finite_cutoff_levels t r ht hr s hs).bddAbove hk

/-- A nonempty family fitting the initial cutoff fits its maximal cutoff. -/
theorem cutoffRank_spec {V : Type*} (t : ℕ → ℝ) (r : V → ℝ)
    (ht : Tendsto t atTop (𝓝 0)) (hr : ∀ i, 0 < r i) (s : Finset V)
    (hs : s.Nonempty) (hzero : ∀ i ∈ s, r i ≤ t 0) :
    ∀ i ∈ s, r i ≤ t (cutoffRank t r s) := by
  have hnonempty : {k : ℕ | ∀ i ∈ s, r i ≤ t k}.Nonempty := ⟨0, hzero⟩
  have hmem := hnonempty.csSup_mem (finite_cutoff_levels t r ht hr s hs)
  change ∀ i ∈ s, r i ≤ t (sSup {k : ℕ | ∀ i ∈ s, r i ≤ t k}) at hmem
  simpa only [cutoffRank, ite_eq_left hs] using hmem

/-- Passing to a nonempty face can only increase the cutoff rank. -/
theorem cutoffRank_mono_face {V : Type*} (t : ℕ → ℝ) (r : V → ℝ)
    (ht : Tendsto t atTop (𝓝 0)) (hr : ∀ i, 0 < r i) {s u : Finset V}
    (hu : u.Nonempty) (hus : u ⊆ s) (hzero : ∀ i ∈ s, r i ≤ t 0) :
    cutoffRank t r s ≤ cutoffRank t r u := by
  have hs := hu.mono hus
  apply le_cutoffRank t r ht hr u hu
  intro i hi
  exact cutoffRank_spec t r ht hr s hs hzero i (hus hi)

namespace DyadicBandCover
variable {E : Type*} [MetricSpace E] {K : Set E} {τ : ℝ} (D : DyadicBandCover K τ)

/-- The cutoff rank of a labelled family of shrinking cover balls. -/
abbrev rank (t : ℕ → ℝ) (s : Finset D.Index) : ℕ :=
  cutoffRank t (fun i : D.Index => dyadicRadius τ i.1) s

/-- The original upper radius bounds every selected dyadic radius. -/
theorem radius_le_initial (hτ : 0 < τ) (i : D.Index) : dyadicRadius τ i.1 ≤ τ := by
  calc
    dyadicRadius τ i.1 ≤ dyadicRadius τ 0 := dyadicRadius_antitone hτ.le (Nat.zero_le _)
    _ = τ := by simp only [dyadicRadius, pow_zero, mul_one]

/-- Every simplex fits its maximal cutoff when the initial cutoff retains this cover. -/
theorem rank_spec (hτ : 0 < τ) (t : ℕ → ℝ) (ht : Tendsto t atTop (𝓝 0))
    (hbase : τ ≤ t 0) {s : Finset D.Index} (hs : s.Nonempty) :
    ∀ i ∈ s, dyadicRadius τ i.1 ≤ t (D.rank t s) :=
  cutoffRank_spec t _ ht (fun i => dyadicRadius_pos hτ i.1) s hs
    (fun i _ => (D.radius_le_initial hτ i).trans hbase)

/-- Faces acquire at least the rank of their containing simplex. -/
theorem rank_mono_face (hτ : 0 < τ) (t : ℕ → ℝ) (ht : Tendsto t atTop (𝓝 0))
    (hbase : τ ≤ t 0) {s u : Finset D.Index} (hu : u.Nonempty) (hus : u ⊆ s) :
    D.rank t s ≤ D.rank t u :=
  cutoffRank_mono_face t _ ht (fun i => dyadicRadius_pos hτ i.1) hu hus
    (fun i _ => (D.radius_le_initial hτ i).trans hbase)

/-- Balls contributing at distance at most the k-th cutoff have rank at least k. -/
theorem le_rank_of_distance_le (hτ : 0 < τ) (t : ℕ → ℝ)
    (ht : Tendsto t atTop (𝓝 0)) {s : Finset D.Index} (hs : s.Nonempty)
    (x : E) (hx : ∀ i ∈ s, x ∈ D.coverBall i) {k : ℕ}
    (hdist : infDist x K ≤ t k) : k ≤ D.rank t s := by
  apply le_cutoffRank t _ ht (fun i => dyadicRadius_pos hτ i.1) s hs
  intro i hi
  exact ((D.distance_bounds (hx i hi)).1.le).trans hdist

end DyadicBandCover
end P202.Duality

noncomputable section
open Set Topology Metric ContinuousMap Convexity
open Classical
namespace P202.Duality
universe u v
set_option maxHeartbeats 1000000

/-- Extend controlled vertex data over any bounded-dimensional abstract nerve.
The function is used only on its admissible simplices. -/
theorem exists_controlled_simplexwise_map {V : Type u} {X : Type v} [MetricSpace X]
    (S : Set (Finset V))
    (hS : ∀ s ∈ S, ∀ t ⊆ s, t.Nonempty → t ∈ S)
    (m : ℕ) (hdim : ∀ s ∈ S, s.card ≤ m+1)
    (r : Finset V → ℕ)
    (hr : ∀ s ∈ S, ∀ t ⊆ s, t.Nonempty → r s ≤ r t)
    (ε : ℕ → ℕ → ℝ) (hε : ∀ d k, 0 < ε d k)
    (hanti : ∀ d, Antitone (ε d)) (δ : ℝ → ℝ)
    (hsmall : ∀ e > 0, ∀ (W : Type u) [Fintype W] [Nontrivial W]
      (f : C(simplexBoundary W, X)), (∀ a b, dist (f a) (f b) < δ e) →
      ∃ G : C(StdSimplex ℝ W, X), (∀ p : simplexBoundary W, G p.1 = f p) ∧
        ∀ p q, dist (G p) (G q) ≤ e)
    (hstep : ∀ d < m, ∀ k, 2 * ε d k < δ (ε (d+1) k))
    (v : V → X)
    (hvertex : ∀ s ∈ S, ∀ i ∈ s, ∀ j ∈ s,
      dist (v i) (v j) < δ (ε 1 (r s))) :
    ∃ F : StdSimplex ℝ V → X,
      (∀ i, F (.single i) = v i) ∧
      (∀ s ∈ S, Continuous (F ∘ StdSimplex.map (Subtype.val : s → V))) ∧
      (∀ s ∈ S, 2 ≤ s.card → ∀ p q : StdSimplex ℝ s,
        dist (F (p.map Subtype.val)) (F (q.map Subtype.val)) ≤ ε (s.card - 1) (r s)) := by
  have hind : ∀ d ≤ m, ∃ F : StdSimplex ℝ V → X,
      (∀ i, F (.single i) = v i) ∧
      (∀ s ∈ S, s.card ≤ d+1 → Continuous (F ∘ StdSimplex.map (Subtype.val : s → V))) ∧
      (∀ s ∈ S, s.card ≤ d+1 → 2 ≤ s.card → ∀ p q : StdSimplex ℝ s,
        dist (F (p.map Subtype.val)) (F (q.map Subtype.val)) ≤ ε (s.card - 1) (r s)) := by
    intro d
    induction d with
    | zero =>
      intro _
      refine ⟨simplexVertexExtension v, simplexVertexExtension_single v, ?_, ?_⟩
      · intro s _ hs
        exact continuous_simplexVertexExtension_chart v s hs
      · intro s hs hle hge
        omega
    | succ d ih =>
      intro hd
      obtain ⟨F, hFv, hFc, hFb⟩ := ih (by omega)
      have hext (s : Finset V) (hs : s ∈ S) (hcard : s.card = d+2) :
          ∃ G : C(StdSimplex ℝ s, X),
            (∀ p : simplexBoundary s, G p.1 = F (p.1.map Subtype.val)) ∧
            ∀ p q, dist (G p) (G q) ≤ ε (d+1) (r s) := by
        have hnt : 1 < Fintype.card s := by simpa using (show 1 < s.card by omega)
        letI : Nontrivial s := Fintype.one_lt_card_iff_nontrivial.mp hnt
        have hcont := continuous_simplexBoundary_of_skeleton S hS F (d+1) hFc s hs
          (by omega) (by omega)
        let f : C(simplexBoundary s, X) := ⟨_, hcont⟩
        apply hsmall (ε (d+1) (r s)) (hε _ _) s f
        intro p q
        by_cases hd0 : d = 0
        · subst d
          exact simplexBoundary_edge_dist_lt s (by omega) F v hFv _ (hvertex s hs) p q
        · have hface (i : s) (p q : simplexFace s i) :
              dist (f ⟨p.1, i, p.2⟩) (f ⟨q.1, i, q.2⟩) ≤ ε d (r s) := by
            let t := s.erase i.1
            have htcard : t.card = d+1 := by
              dsimp [t]
              rw [Finset.card_erase_of_mem i.2, hcard]
              omega
            have htne : t.Nonempty := Finset.card_pos.mp (by omega)
            have hts : t ⊆ s := Finset.erase_subset _ _
            have htS : t ∈ S := hS s hs t hts htne
            let a := simplexRestrictToFinset (p.1.map (Subtype.val : s → V)) t
              (simplexFace_chart_support s i p)
            let b := simplexRestrictToFinset (q.1.map (Subtype.val : s → V)) t
              (simplexFace_chart_support s i q)
            have hb := hFb t htS (by omega) (by omega) a b
            have haeq : a.map (Subtype.val : t → V) = p.1.map Subtype.val :=
              simplexRestrictToFinset_map_val _ _ _
            have hbeq : b.map (Subtype.val : t → V) = q.1.map Subtype.val :=
              simplexRestrictToFinset_map_val _ _ _
            rw [haeq, hbeq] at hb
            exact hb.trans (by
              have hmono := hanti d (hr s hs t hts htne)
              simpa only [htcard, Nat.add_sub_cancel] using hmono)
          have hb := simplexBoundary_dist_le_two_mul (by simpa using (show 2 < s.card by omega))
            f (ε d (r s)) hface p q
          exact hb.trans_lt (hstep d (by omega) (r s))
      choose G hG hGb using hext
      let F' := extendSkeletonFunction S (d+1) F (fun s hs hc => (G s hs (by omega)))
      have hchart (s : Finset V) (hs : s ∈ S) (hc : s.card = d+2) (p : StdSimplex ℝ s) :
          F' (p.map Subtype.val) = G s hs hc p := by
        exact extendSkeletonFunction_chart S (d+1) F _
          (fun s hs hc p => hG s hs (by omega) p) s hs (by omega) p
      refine ⟨F', ?_, ?_, ?_⟩
      · intro i
        rw [show F' (.single i) = F (.single i) from
          extendSkeletonFunction_old S (d+1) F _ _ (by simp)]
        exact hFv i
      · intro s hs hle
        by_cases hc : s.card ≤ d+1
        · have heq : F' ∘ StdSimplex.map (Subtype.val : s → V) =
              F ∘ StdSimplex.map (Subtype.val : s → V) := by
            funext p
            dsimp only [Function.comp_def]
            apply extendSkeletonFunction_old
            exact (Finset.card_le_card (simplexChart_support_subset s p)).trans hc
          rw [heq]
          exact hFc s hs hc
        · have hc' : s.card = d+2 := by omega
          have heq : F' ∘ StdSimplex.map (Subtype.val : s → V) = G s hs hc' := by
            funext p
            exact hchart s hs hc' p
          rw [heq]
          exact (G s hs hc').continuous
      · intro s hs hle hge p q
        by_cases hc : s.card ≤ d+1
        · rw [show F' (p.map Subtype.val) = F (p.map Subtype.val) from
            extendSkeletonFunction_old S (d+1) F _ _
              ((Finset.card_le_card (simplexChart_support_subset s p)).trans hc),
            show F' (q.map Subtype.val) = F (q.map Subtype.val) from
            extendSkeletonFunction_old S (d+1) F _ _
              ((Finset.card_le_card (simplexChart_support_subset s q)).trans hc)]
          exact hFb s hs hc hge p q
        · have hc' : s.card = d+2 := by omega
          rw [hchart s hs hc' p, hchart s hs hc' q]
          rw [show s.card - 1 = d+1 by omega]
          exact hGb s hs hc' p q
  obtain ⟨F, hFv, hFc, hFb⟩ := hind m le_rfl
  exact ⟨F, hFv, fun s hs => hFc s hs (hdim s hs),
    fun s hs hge => hFb s hs (hdim s hs) hge⟩
end P202.Duality

noncomputable section
open Set Topology Metric ContinuousMap Convexity
open Classical
namespace P202.Duality

/-- A barycentric point whose support has one vertex is that vertex. -/
theorem simplex_eq_single_of_support_card_le_one {V : Type*} (p : StdSimplex ℝ V)
    (hcard : p.weights.support.card ≤ 1) (i : V) (hi : i ∈ p.weights.support) :
    p = StdSimplex.single i := by
  apply StdSimplex.support_weights_eq_singleton.mp
  apply Finset.eq_singleton_iff_unique_mem.mpr
  refine ⟨hi, ?_⟩
  intro j hj
  exact Finset.card_le_one.mp hcard j hj i hi

/-- A bound on the image of the support chart controls distance to every
assigned support vertex. Singleton support needs no positive-dimensional bound. -/
theorem simplex_dist_vertex_le_of_chart_diameter {V X : Type*} [MetricSpace X]
    (F : StdSimplex ℝ V → X) (v : V → X)
    (hvertex : ∀ i : V, F (StdSimplex.single i) = v i)
    (p : StdSimplex ℝ V) (i : V) (hi : i ∈ p.weights.support)
    (a : ℝ) (ha : 0 ≤ a)
    (hdiam : 2 ≤ p.weights.support.card →
      ∀ q r : StdSimplex ℝ p.weights.support,
        dist (F (q.map (Subtype.val : p.weights.support → V)))
          (F (r.map (Subtype.val : p.weights.support → V))) ≤ a) :
    dist (F p) (v i) ≤ a := by
  by_cases hcard : p.weights.support.card ≤ 1
  · rw [simplex_eq_single_of_support_card_le_one p hcard i hi, hvertex, dist_self]
    exact ha
  · let q := simplexRestrictToFinset p p.weights.support Finset.Subset.rfl
    have h := hdiam (by omega) q (StdSimplex.single ⟨i, hi⟩)
    simpa only [q, simplexRestrictToFinset_map_val, StdSimplex.map_single, hvertex] using h

/-- The scale bounds of the nerve construction imply the required dyadic
control relative to any active vertex. -/
theorem simplex_dist_vertex_le_dyadic {V X : Type*} [MetricSpace X]
    (F : StdSimplex ℝ V → X) (v : V → X)
    (hvertex : ∀ i : V, F (StdSimplex.single i) = v i)
    (ε : ℕ → ℕ → ℝ) (rank : Finset V → ℕ)
    (p : StdSimplex ℝ V) (i : V) (hi : i ∈ p.weights.support)
    (hε : ε (p.weights.support.card - 1) (rank p.weights.support) ≤
      (1 / 2 : ℝ) ^ rank p.weights.support)
    (hdiam : 2 ≤ p.weights.support.card →
      ∀ q r : StdSimplex ℝ p.weights.support,
        dist (F (q.map (Subtype.val : p.weights.support → V)))
          (F (r.map (Subtype.val : p.weights.support → V))) ≤
            ε (p.weights.support.card - 1) (rank p.weights.support)) :
    dist (F p) (v i) ≤ (1 / 2 : ℝ) ^ rank p.weights.support := by
  apply simplex_dist_vertex_le_of_chart_diameter F v hvertex p i hi _ (by positivity)
  intro hcard q r
  exact (hdiam hcard q r).trans hε

/-- Combining the nerve-image bound with an ambient vertex estimate gives
vanishing displacement as the active scale tends to zero. -/
theorem simplex_dist_ambient_le_dyadic_add {V X : Type*} [MetricSpace X]
    (F : StdSimplex ℝ V → X) (v : V → X)
    (hvertex : ∀ i : V, F (StdSimplex.single i) = v i)
    (ε : ℕ → ℕ → ℝ) (rank : Finset V → ℕ)
    (p : StdSimplex ℝ V) (i : V) (hi : i ∈ p.weights.support)
    (hε : ε (p.weights.support.card - 1) (rank p.weights.support) ≤
      (1 / 2 : ℝ) ^ rank p.weights.support)
    (hdiam : 2 ≤ p.weights.support.card →
      ∀ q r : StdSimplex ℝ p.weights.support,
        dist (F (q.map (Subtype.val : p.weights.support → V)))
          (F (r.map (Subtype.val : p.weights.support → V))) ≤
            ε (p.weights.support.card - 1) (rank p.weights.support))
    (x : X) (b : ℝ) (hix : dist (v i) x ≤ b) :
    dist (F p) x ≤ (1 / 2 : ℝ) ^ rank p.weights.support + b := by
  exact (dist_triangle (F p) (v i) x).trans
    (add_le_add (simplex_dist_vertex_le_dyadic F v hvertex ε rank p i hi hε hdiam) hix)

end P202.Duality

noncomputable section
open Set Topology Metric ContinuousMap Convexity

namespace P202.Duality
namespace DyadicBandCover
variable {E : Type*} [MetricSpace E] {K : Set E} {τ : ℝ} (D : DyadicBandCover K τ)

/-- The nerve retains exactly the nonempty finite families of cover balls
with a common point. -/
def nerve : Set (Finset D.Index) :=
  {s | s.Nonempty ∧ ∃ x : E, ∀ i ∈ s, x ∈ D.coverBall i}

 theorem nerve_nonempty {s : Finset D.Index} (hs : s ∈ D.nerve) : s.Nonempty := hs.1

 theorem nerve_face {s t : Finset D.Index} (hs : s ∈ D.nerve)
    (hts : t ⊆ s) (ht : t.Nonempty) : t ∈ D.nerve := by
  obtain ⟨_, x, hx⟩ := hs
  exact ⟨ht, x, fun i hi => hx i (hts hi)⟩

/-- The full ambient `4τ` neighborhood, together with its punctured part. -/
def neighborhood (_D : DyadicBandCover K τ) : Set E := {x | infDist x K < 4 * τ}

 theorem isOpen_neighborhood : IsOpen (D.neighborhood) :=
  isOpen_lt (continuous_infDist_pt K) continuous_const

 theorem subset_neighborhood (hτ : 0 < τ) : K ⊆ D.neighborhood := by
  intro x hx
  change infDist x K < 4 * τ
  rw [infDist_zero_of_mem hx]
  positivity

/-- Local finiteness survives restriction to the punctured neighborhood. -/
theorem locallyFinite_punctured (hK : IsClosed K) (hne : K.Nonempty) (hτ : 0 < τ) :
    LocallyFinite (fun i : D.Index =>
      {x : ↥(D.neighborhood \ K) | x.1 ∈ D.coverBall i}) := by
  let q : ↥(D.neighborhood \ K) → ↥(Kᶜ) := fun x => ⟨x.1, x.2.2⟩
  have hq : Continuous q := continuous_subtype_val.subtype_mk _
  exact (D.locallyFinite hK hne hτ).preimage_continuous hq

/-- The partition coordinates form a simplex of the actual nerve; every
contributing vertex is a ball containing the point. -/
theorem exists_nerve_coordinates (hK : IsClosed K) (hne : K.Nonempty) (hτ : 0 < τ) :
    ∃ b : ↥(D.neighborhood \ K) → StdSimplex ℝ D.Index,
      Continuous b ∧
      (∀ i, Continuous (fun x => (b x).weights i)) ∧
      (∀ x, ∃ I : Finset D.Index, ∀ᶠ y in 𝓝 x, (b y).weights.support ⊆ I) ∧
      (∀ x, (b x).weights.support ∈ D.nerve) ∧
      ∀ x i, i ∈ (b x).weights.support → x.1 ∈ D.coverBall i := by
  let U (i : D.Index) : Set ↥(D.neighborhood \ K) := {x | x.1 ∈ D.coverBall i}
  have ho : ∀ i, IsOpen (U i) := fun i => isOpen_ball.preimage continuous_subtype_val
  have hcov : univ ⊆ ⋃ i, U i := by
    intro x _
    obtain ⟨i, hi⟩ := D.covers hτ
      ((hK.notMem_iff_infDist_pos hne).mp x.2.2) x.2.1
    exact mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨b, hbcont, hbcoord, hbloc, hbU⟩ :=
    exists_barycentric_coordinates U ho (D.locallyFinite_punctured hK hne hτ) hcov
  refine ⟨b, hbcont, hbcoord, hbloc, ?_, hbU⟩
  intro x
  exact ⟨(b x).support_weights_nonempty, x.1, hbU x⟩

/-- Any simplexwise continuous nerve map gives a continuous map on the
punctured ambient neighborhood. Its barycentric support remains explicitly
available for the small-displacement estimate. -/
theorem exists_continuous_nerve_composite {Y : Type*} [TopologicalSpace Y]
    (hK : IsClosed K) (hne : K.Nonempty) (hτ : 0 < τ)
    (F : StdSimplex ℝ D.Index → Y)
    (hF : ∀ s ∈ D.nerve, Continuous (F ∘ StdSimplex.map (Subtype.val : s → D.Index))) :
    ∃ b : ↥(D.neighborhood \ K) → StdSimplex ℝ D.Index,
      Continuous (F ∘ b) ∧
      (∀ x, (b x).weights.support ∈ D.nerve) ∧
      ∀ x i, i ∈ (b x).weights.support → x.1 ∈ D.coverBall i := by
  obtain ⟨b, _, hbcoord, hbloc, hbnerve, hbU⟩ :=
    D.exists_nerve_coordinates hK hne hτ
  exact ⟨b, continuous_comp_of_simplexwise D.nerve F b hF hbcoord hbloc hbnerve,
    hbnerve, hbU⟩

end DyadicBandCover
end P202.Duality

noncomputable section
open Set Metric
namespace P202.Duality.DyadicBandCover
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {K : Set E} {τ : ℝ} (D : DyadicBandCover K τ)

/-- The nerve dimension is bounded independently of the scale cutoff. -/
theorem nerve_card_le (hτ : 0 < τ) {s : Finset D.Index} (hs : s ∈ D.nerve) :
    s.card ≤ 4 * 5 ^ Module.finrank ℝ E := by
  obtain ⟨_, x, hx⟩ := hs
  exact D.card_of_common_point_le_pow hτ s x hx

end P202.Duality.DyadicBandCover

noncomputable section
open Set Topology Metric ContinuousMap Filter
namespace P202.Duality.DyadicBandCover
variable {E : Type*} [MetricSpace E] {K : Set E} {τ : ℝ} (D : DyadicBandCover K τ)

theorem nearest_vertex_dist_lt_nine_mul {p : D.Index → K}
    (hp : ∀ i, dist i.2.1 (p i).1 = infDist i.2.1 K)
    {i : D.Index} {x : E} (hx : x ∈ D.coverBall i) :
    dist (p i).1 x < 9 * dyadicRadius τ i.1 := by
  have hdist := dist_triangle (p i).1 i.2.1 x
  have hband := (D.band i.1 i.2.1 i.2.2).2
  change dist x i.2.1 < dyadicRadius τ i.1 at hx
  rw [dist_comm (p i).1 i.2.1, hp i, dist_comm i.2.1 x] at hdist
  linarith

/-- The images of the vertices of a simplex are close on its maximal cutoff scale. -/
theorem vertex_pair_dist_lt_rank_cutoff (hτ : 0 < τ) (t : ℕ → ℝ)
    (ht : Tendsto t atTop (𝓝 0)) (hbase : τ ≤ t 0)
    (p : D.Index → K) (hp : ∀ i, dist i.2.1 (p i).1 = infDist i.2.1 K)
    {s : Finset D.Index} (x : E) (hs : ∀ i ∈ s, x ∈ D.coverBall i)
    {i j : D.Index} (hi : i ∈ s) (hj : j ∈ s) :
    dist (p i).1 (p j).1 < 18 * t (D.rank t s) := by
  have hne : s.Nonempty := ⟨i, hi⟩
  have hri := D.rank_spec hτ t ht hbase hne i hi
  have hrj := D.rank_spec hτ t ht hbase hne j hj
  have hpi := D.nearest_vertex_dist_lt_nine_mul hp (hs i hi)
  have hpj := D.nearest_vertex_dist_lt_nine_mul hp (hs j hj)
  have htri := dist_triangle (p i).1 x (p j).1
  rw [dist_comm x (p j).1] at htri
  linarith
end P202.Duality.DyadicBandCover

noncomputable section
open Set Topology Metric ContinuousMap Filter
open Classical
namespace P202.Duality.DyadicBandCover

variable {E : Type*} [MetricSpace E] {K : Set E} {τ : ℝ} (D : DyadicBandCover K τ)

/-- Rank-controlled proximity to a vertex implies uniform vanishing displacement.
This is the last estimate in the shrinking-nerve retraction construction. -/
theorem uniform_displacement_of_rank_control (hτ : 0 < τ)
    (t : ℕ → ℝ) (htpos : ∀ k, 0 < t k) (ht : Tendsto t atTop (𝓝 0))
    (p : D.Index → K) (hp : ∀ i, dist i.2.1 (p i).1 = infDist i.2.1 K)
    {A : Set E} (f : A → K)
    (hcontrol : ∀ x : A, ∃ s : Finset D.Index, s.Nonempty ∧
      (∀ i ∈ s, x.1 ∈ D.coverBall i) ∧
      ∃ i ∈ s, dist (f x).1 (p i).1 ≤ (1 / 2 : ℝ) ^ D.rank t s) :
    ∀ ε > 0, ∃ δ > 0, ∀ x : A, infDist x.1 K < δ → dist (f x).1 x.1 < ε := by
  intro ε hε
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (half_pos hε)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  refine ⟨min (t k) (ε / 18), lt_min (htpos k) (by positivity), ?_⟩
  intro x hx
  obtain ⟨s, hs, hactive, i, hi, hclose⟩ := hcontrol x
  have hdist_t : infDist x.1 K ≤ t k := (hx.trans_le (min_le_left _ _)).le
  have hdist_eps : infDist x.1 K < ε / 18 := hx.trans_le (min_le_right _ _)
  have hrank := D.le_rank_of_distance_le hτ t ht hs x.1 hactive hdist_t
  have hpow : (1 / 2 : ℝ) ^ D.rank t s ≤ (1 / 2 : ℝ) ^ k :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hrank
  have hvertex : dist (p i).1 x.1 < 9 * dyadicRadius τ i.1 := by
    have hdist := dist_triangle (p i).1 i.2.1 x.1
    have hband := (D.band i.1 i.2.1 i.2.2).2
    have hxball := hactive i hi
    change dist x.1 i.2.1 < dyadicRadius τ i.1 at hxball
    rw [dist_comm (p i).1 i.2.1, hp i, dist_comm i.2.1 x.1] at hdist
    linarith
  have hradius : dyadicRadius τ i.1 < infDist x.1 K :=
    (D.distance_bounds (hactive i hi)).1
  have htri := dist_triangle (f x).1 (p i).1 x.1
  linarith

end P202.Duality.DyadicBandCover

noncomputable section
open Set Topology Metric ContinuousMap Convexity Filter
open Classical
namespace P202.Duality
universe u
set_option maxHeartbeats 1000000

/-- A compact classically locally contractible subset of a finite-dimensional
real normed space retracts from an open neighborhood. -/
theorem compact_locallyContractible_hasOpenNeighborhoodRetraction
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K : Set E} (hK : IsCompact K) (hLC : LocallyContractibleSpace K) :
    HasOpenNeighborhoodRetraction K := by
  by_cases hne : K.Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    exact empty_hasOpenNeighborhoodRetraction E
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hδexists (e : ℝ) : ∃ δ > 0,
      0 < e → ∀ (W : Type u) [Fintype W] [Nontrivial W]
        (f : C(simplexBoundary W, K)),
        (∀ a b, dist (f a) (f b) < δ) →
        ∃ G : C(StdSimplex ℝ W, K), (∀ p : simplexBoundary W, G p.1 = f p) ∧
          ∀ p q, dist (G p) (G q) ≤ e := by
    by_cases he : 0 < e
    · obtain ⟨δ, hδ, hsmall⟩ := uniform_small_simplex_extension hLC e he
      exact ⟨δ, hδ, fun _ => hsmall⟩
    · exact ⟨1, by norm_num, fun h => (he h).elim⟩
  choose δ hδ hsmall using hδexists
  let m := 4 * 5 ^ Module.finrank ℝ E
  obtain ⟨ε, hε, hanti, hle, hstep⟩ :=
    exists_finite_skeletal_diameter_bounds δ (fun e _ => hδ e) m
  obtain ⟨t, htpos, htanti, htle, httend⟩ :=
    exists_strictAnti_positive_cutoffs (fun k => δ (ε 1 k) / 20)
      (fun k => div_pos (hδ _) (by norm_num))
  let τ := t 0
  have hτ : 0 < τ := htpos 0
  obtain ⟨D⟩ := nonempty_dyadicBandCover hK hne hτ
  obtain ⟨p, hp⟩ := D.exists_nearest_points hK hne
  have hvertex : ∀ s ∈ D.nerve, ∀ i ∈ s, ∀ j ∈ s,
      dist (p i) (p j) < δ (ε 1 (D.rank t s)) := by
    intro s hs i hi j hj
    obtain ⟨_, x, hx⟩ := hs
    have hb := D.vertex_pair_dist_lt_rank_cutoff hτ t httend le_rfl p hp x hx hi hj
    have ht := htle (D.rank t s)
    change dist (p i).1 (p j).1 < δ (ε 1 (D.rank t s))
    linarith [hδ (ε 1 (D.rank t s))]
  obtain ⟨F, hFv, hFc, hFb⟩ := exists_controlled_simplexwise_map
    D.nerve (fun s hs u hus hune => D.nerve_face hs hus hune)
    m (fun s hs => (D.nerve_card_le hτ hs).trans (Nat.le_succ m))
    (D.rank t) (fun s _ u hus hune => D.rank_mono_face hτ t httend le_rfl hune hus)
    ε hε hanti δ hsmall hstep p hvertex
  obtain ⟨b, hbcont, hbS, hbactive⟩ := D.exists_continuous_nerve_composite hK.isClosed hne hτ F hFc
  let f : C(↥(D.neighborhood \ K), K) := ⟨F ∘ b, hbcont⟩
  apply hasOpenNeighborhoodRetraction_of_punctured_map hK.isClosed
    D.isOpen_neighborhood (D.subset_neighborhood hτ) f
  apply D.uniform_displacement_of_rank_control hτ t htpos httend p hp f
  intro x
  let s := (b x).weights.support
  have hs : s.Nonempty := (b x).support_weights_nonempty
  obtain ⟨i, hi⟩ := hs
  refine ⟨s, ⟨i, hi⟩, hbactive x, i, hi, ?_⟩
  exact simplex_dist_vertex_le_dyadic F p hFv ε (D.rank t) (b x) i hi
    (hle _ _) (fun hcard => hFb s (hbS x) hcard)

end P202.Duality

namespace P202.Duality

/-- Every compact classically locally contractible Euclidean subset is a retract
of an ambient open neighborhood (paper.tex, Lemma `lem:p202-enr`). -/
theorem euclideanNeighborhoodRetraction :
    P202Specs.Duality.EuclideanNeighborhoodRetraction.euclideanNeighborhoodRetraction := by
  intro n K hK hLC
  exact compact_locallyContractible_hasOpenNeighborhoodRetraction hK hLC

end P202.Duality
