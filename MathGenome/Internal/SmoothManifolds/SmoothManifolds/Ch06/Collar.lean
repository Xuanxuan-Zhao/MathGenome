import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch06.Collar
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch06.MaximalIntegralCurves
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Tangent.BoundaryCones
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.Boundary
import Mathlib.Analysis.Calculus.ContDiff.Operations
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Localization.Partitions
import Mathlib.Topology.Order.LeftRightNhds
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch04.InjectiveShrinking
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.ODE.ExistUnique
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.BoundaryInverse
import MathGenome.Internal.ODEDynamics.D13Unified.Ch11.Flowbox
import Mathlib.Topology.ContinuousMap.Basic

/-! M06.05, collar clause. A globally smooth inward field gives intrinsic
one-sided trajectories. Their smooth boundary families glue by uniqueness;
the ambient inverse theorem gives relative local inverses near zero.
Injective shrinking and a positive smooth variable width give the collar of
the whole boundary, including the empty-boundary and dimension-zero cases. -/
namespace SmoothManifolds.Collars
open ModelData AtlasData MapData BoundaryData CollarData PartitionData Set Filter
open TangentData TangentBundleData VectorFieldData
open scoped Topology
universe u v w

/-- If the boundary is empty the entire collar source is empty. -/
theorem collarSource_isEmpty {n : ℕ} {kind : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n kind M)
    (h : intrinsicBoundary S = ∅) : IsEmpty (CollarSource S) := by
  refine ⟨fun x => ?_⟩
  have hx := x.1.property
  simp only [h, mem_empty_iff_false] at hx

/-- The empty collar is a smooth diffeomorphism onto the empty open
neighborhood. This proves the full smoothness and inverse assertions, rather
than merely giving an empty function. -/
noncomputable def emptyBoundaryCollar {n : ℕ} {kind : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n kind M)
    (h : intrinsicBoundary S = ∅) : SmoothCollar S := by
  letI := collarSource_isEmpty S h
  let f : CollarSource S ≃ₜ (∅ : Set M) := {
    toEquiv := Equiv.equivOfIsEmpty _ _
    continuous_toFun := by
      exact continuous_iff_continuousAt.mpr (fun x => isEmptyElim x)
    continuous_invFun := by
      exact continuous_iff_continuousAt.mpr (fun x => isEmptyElim x) }
  refine {
    neighborhood := ∅
    isOpen_neighborhood := isOpen_empty
    boundary_subset := by simp only [h, subset_refl]
    toHomeomorph := f
    zero_section := ?_
    smooth_forward := ?_
    smooth_inverse := ?_ }
  · intro q
    exact isEmptyElim ((q, timeZero) : CollarSource S)
  · intro e d he hd x
    exact isEmptyElim x
  · intro d e hd he y
    exact isEmptyElim y

/-- The zero-dimensional convention is implemented by the empty collar. -/
noncomputable def zeroDimensionalCollar {kind : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold 0 kind M) : SmoothCollar S :=
  emptyBoundaryCollar S (intrinsicBoundary_zero S)

/-- Euclidean-model manifolds also have the empty collar. -/
noncomputable def euclideanModelCollar {n : ℕ} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n .euclidean M) : SmoothCollar S :=
  emptyBoundaryCollar S (intrinsicBoundary_euclidean S)

/-- The variable-width one-sided tube before normalization of its time factor. -/
def variableWidthSet {Q : Type v} (ε : Q → ℝ) : Set (Q × ℝ) :=
  {x | 0 ≤ x.2 ∧ x.2 < ε x.1}

/-- Normalize any positive continuous width, with no compactness or uniform
lower bound. This homeomorphism preserves the zero-time section. -/
noncomputable def variableWidthHomeomorph {Q : Type v} [TopologicalSpace Q]
    (ε : Q → ℝ) (hε : Continuous ε) (hpos : ∀ q, 0 < ε q) :
    (Q × CollarTime) ≃ₜ variableWidthSet ε where
  toFun x := ⟨(x.1, ε x.1 * x.2.val),
    mul_nonneg (hpos x.1).le x.2.property.1,
    mul_lt_of_lt_one_right (hpos x.1) x.2.property.2⟩
  invFun x := (x.val.1, ⟨x.val.2 / ε x.val.1,
    div_nonneg x.property.1 (hpos x.val.1).le,
    (div_lt_one (hpos x.val.1)).mpr x.property.2⟩)
  left_inv x := by
    apply Prod.ext
    · rfl
    apply Subtype.ext
    change ε x.1 * x.2.val / ε x.1 = x.2.val
    rw [mul_comm, mul_div_cancel_right₀ _ (hpos x.1).ne']
  right_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    change ε x.val.1 * (x.val.2 / ε x.val.1) = x.val.2
    rw [mul_comm, div_mul_cancel₀ _ (hpos x.val.1).ne']
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_fst.prodMk
      ((hε.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd))
  continuous_invFun := by
    apply Continuous.prodMk
    · exact continuous_fst.comp continuous_subtype_val
    · apply Continuous.subtype_mk
      exact (continuous_snd.comp continuous_subtype_val).div
        (hε.comp (continuous_fst.comp continuous_subtype_val))
        (fun x => (hpos x.val.1).ne')

@[simp] theorem variableWidthHomeomorph_zero {Q : Type v} [TopologicalSpace Q]
    (ε : Q → ℝ) (hε : Continuous ε) (hpos : ∀ q, 0 < ε q) (q : Q) :
    (variableWidthHomeomorph ε hε hpos (q, timeZero)).val = (q, 0) := by
  simp [variableWidthHomeomorph, timeZero]

/-- A locally available positive one-sided width can be chosen smoothly on
any manifold, including a noncompact or disconnected one. Only openness of
the cover and local tube inclusions enter the construction. -/
theorem exists_smooth_width_of_cover {m : ℕ} {a : ModelKind} {Q : Type u}
    [TopologicalSpace Q] (R : SmoothManifold m a Q) {ι : Type v}
    (U : ι → Set Q) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ q, ∃ i, q ∈ U i) (δ : ι → ℝ) (hδ : ∀ i, 0 < δ i)
    (W : Set (Q × ℝ))
    (htube : ∀ i q, q ∈ U i → ∀ t, 0 ≤ t → t < δ i → (q, t) ∈ W) :
    ∃ ε : Q → ℝ, ScalarSmooth R.smoothStructure.val ε ∧
      (∀ q, 0 < ε q) ∧
      ∀ q t, 0 ≤ t → t < ε q → (q, t) ∈ W := by
  classical
  obtain ⟨ρ, hρ, hsub⟩ := exists_smooth_partition R U hU hcover
  let f : ι → Q → ℝ := fun i q => ρ i q * δ i
  have hsupp (i : ι) : sectionSupport (f i) ⊆ sectionSupport (ρ i) := by
    apply closure_mono
    intro q hq
    change ρ i q ≠ 0
    intro hz
    exact hq (by simp [f, hz])
  have hlf : LocallyFinite (fun i => sectionSupport (f i)) :=
    hρ.2.2.1.subset hsupp
  let ε : Q → ℝ := fun q => ∑ᶠ i, f i q
  have hsmooth : ScalarSmooth R.smoothStructure.val ε :=
    scalarContDiff_finsum (fun i => scalarContDiff_mul (hρ.1 i)
      (scalarContDiff_const _ _ (δ i))) hlf
  have hfinite (q : Q) : Function.HasFiniteSupport (fun i => ρ i q) :=
    (hρ.2.2.1.point_finite q).subset (fun i hi => subset_closure hi)
  have hfinitef (q : Q) : Function.HasFiniteSupport (fun i => f i q) :=
    (hlf.point_finite q).subset (fun i hi => subset_closure hi)
  refine ⟨ε, hsmooth, ?_, ?_⟩
  · intro q
    have hex : ∃ i, ρ i q ≠ 0 := by
      by_contra! hz
      have heq := hρ.2.2.2 q
      simp [hz] at heq
    obtain ⟨i, hi⟩ := hex
    exact finsum_pos (fun j => mul_nonneg (hρ.2.1 j q) (hδ j).le)
      ⟨i, mul_pos (lt_of_le_of_ne (hρ.2.1 i q) (Ne.symm hi)) (hδ i)⟩ (hfinitef q)
  · intro q t ht htε
    have hex : ∃ i, ρ i q ≠ 0 ∧ t < δ i := by
      by_contra! hn
      let s := (hfinite q).toFinset
      have hsupport : Function.support (fun i => ρ i q) ⊆ s := by
        intro i hi
        exact (hfinite q).mem_toFinset.mpr hi
      have hsupportf : Function.support (fun i => f i q) ⊆ s := by
        intro i hi
        apply hsupport
        intro hz
        exact hi (by simp [f, hz])
      have hsum : ∑ i ∈ s, ρ i q = 1 :=
        (finsum_eq_sum_of_support_subset _ hsupport).symm.trans (hρ.2.2.2 q)
      have hle : ε q ≤ t := calc
        ε q = ∑ i ∈ s, f i q := finsum_eq_sum_of_support_subset _ hsupportf
        _ ≤ ∑ i ∈ s, ρ i q * t := by
          apply Finset.sum_le_sum
          intro i hi
          exact mul_le_mul_of_nonneg_left (hn i ((hfinite q).mem_toFinset.mp hi)) (hρ.2.1 i q)
        _ = t := by rw [← Finset.sum_mul, hsum, one_mul]
      exact (not_le_of_gt htε) hle
    obtain ⟨i, hi, hti⟩ := hex
    exact htube i q (hsub i (subset_closure hi)) t ht hti

/-- A relatively open neighborhood of the whole zero section in the
one-sided time domain contains a tube of positive smooth variable width. -/
theorem exists_smooth_width {m : ℕ} {a : ModelKind} {Q : Type u}
    [TopologicalSpace Q] (R : SmoothManifold m a Q) (W : Set (Q × ℝ))
    (hW : ∀ q, W ∈ 𝓝[univ ×ˢ Ici (0 : ℝ)] (q, 0)) :
    ∃ ε : Q → ℝ, ScalarSmooth R.smoothStructure.val ε ∧
      (∀ q, 0 < ε q) ∧ variableWidthSet ε ⊆ W := by
  classical
  have hlocal (q : Q) : ∃ U : Set Q, IsOpen U ∧ q ∈ U ∧
      ∃ δ : ℝ, 0 < δ ∧ U ×ˢ Ico 0 δ ⊆ W := by
    obtain ⟨V, hV, T, hT, hVT⟩ := mem_nhdsWithin_prod_iff.mp (hW q)
    rw [nhdsWithin_univ] at hV
    obtain ⟨U, hUV, hU, hqU⟩ := mem_nhds_iff.mp hV
    obtain ⟨δ, hδ, hδT⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp hT
    exact ⟨U, hU, hqU, δ, hδ, (fun x hx => hVT ⟨hUV hx.1, hδT hx.2⟩)⟩
  choose U hU hqU δ hδ htube using hlocal
  obtain ⟨ε, hs, hp, hw⟩ := exists_smooth_width_of_cover R U hU
    (fun q => ⟨q, hqU q⟩) δ hδ W
    (fun i q hqi t ht hti => htube i ⟨hqi, ht, hti⟩)
  exact ⟨ε, hs, hp, fun x hx => hw x.1 x.2 hx.1 hx.2⟩

/-- Zero section of a partially defined one-sided flowout. The domain W
already has its subspace topology, whether or not it is ambient-open. -/
def zeroTimeSection {Q : Type v} (W : Set (Q × ℝ)) : Set W :=
  {x | x.val.2 = 0}

/-- The zero section carries exactly the topology of its base. -/
def zeroSectionHomeomorph {Q : Type v} [TopologicalSpace Q]
    (W : Set (Q × ℝ)) (hW : ∀ q, (q, 0) ∈ W) :
    zeroTimeSection W ≃ₜ Q where
  toFun x := x.val.val.1
  invFun q := ⟨⟨(q, 0), hW q⟩, rfl⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact x.property.symm
  right_inv _ := rfl
  continuous_toFun := continuous_fst.comp
    (continuous_subtype_val.comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_id.prodMk continuous_const

/-- Shrink a continuous partial boundary flowout, locally injective at time
zero, to a globally injective neighborhood of the whole zero section. This
uses closedness of the intrinsic boundary and requires no compactness. -/
theorem exists_injective_boundary_flowout {n : ℕ} {kind : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n kind M)
    (W : Set (intrinsicBoundary S × ℝ)) (hW : ∀ q, (q, 0) ∈ W)
    (F : W → M) (hF : Continuous F)
    (hzero : ∀ q, F ⟨(q, 0), hW q⟩ = q.val)
    (hlocal : ∀ z ∈ zeroTimeSection W,
      ∃ V : Set W, IsOpen V ∧ z ∈ V ∧ InjOn F V) :
    ∃ V : Set W, IsOpen V ∧ zeroTimeSection W ⊆ V ∧ InjOn F V := by
  have htrace : ∀ z : zeroTimeSection W, F z.val = z.val.val.1.val := by
    intro z
    have hz : z.val = ⟨(z.val.val.1, 0), hW z.val.val.1⟩ := by
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · exact z.property
    rw [hz, hzero]
  have hemb : Topology.IsEmbedding (fun z : zeroTimeSection W => F z.val) := by
    have h := Topology.IsEmbedding.subtypeVal.comp
      (zeroSectionHomeomorph W hW).isEmbedding
    convert h using 1
    funext z
    exact htrace z
  have himage : F '' zeroTimeSection W = intrinsicBoundary S := by
    apply Subset.antisymm
    · rintro p ⟨z, hz, rfl⟩
      rw [htrace ⟨z, hz⟩]
      exact z.val.1.property
    · intro p hp
      refine ⟨⟨(⟨p, hp⟩, 0), hW ⟨p, hp⟩⟩, rfl, ?_⟩
      exact hzero ⟨p, hp⟩
  apply injective_shrinking S.topologicalManifold F (zeroTimeSection W) hF hemb
  · rw [himage]
    exact (isClosed_intrinsicBoundary S).isLocallyClosed
  · exact hlocal

/-- A Euclidean trajectory whose normal velocity is strictly positive on an
interval through zero belongs to the half-space exactly at nonnegative times.
It meets the face only at zero. This is the one-sided restriction needed for
an inward field; a two-sided boundary-preserving flow would be incorrect. -/
theorem inward_trajectory_sign {n : ℕ} {a b : ℝ} (ha : a < 0) (hb : 0 < b)
    (γ v : ℝ → Euclidean (n + 1))
    (hγ : ∀ t ∈ Ioo a b, HasDerivAt γ (v t) t)
    (hv : ∀ t ∈ Ioo a b, 0 < v t (Fin.last n))
    (hzero : γ 0 (Fin.last n) = 0) :
    ∀ t ∈ Ioo a b,
      (γ t ∈ halfSpaceSet (n + 1) ↔ 0 ≤ t) ∧
      (γ t ∈ halfSpaceFace (n + 1) ↔ t = 0) := by
  let f : ℝ → ℝ := fun t => γ t (Fin.last n)
  have hd (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt f (v t (Fin.last n)) t :=
    ((ContinuousLinearMap.proj (Fin.last n) : Euclidean (n + 1) →L[ℝ] ℝ).hasFDerivAt
      |>.comp_hasDerivAt t (hγ t ht))
  have hm : StrictMonoOn f (Ioo a b) :=
    strictMonoOn_of_deriv_pos (convex_Ioo a b)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => by rw [(hd t (interior_subset ht)).deriv]; exact hv t (interior_subset ht))
  have h0 : (0 : ℝ) ∈ Ioo a b := ⟨ha, hb⟩
  intro t ht
  change (0 ≤ f t ↔ 0 ≤ t) ∧ (f t = 0 ↔ t = 0)
  have hf0 : f 0 = 0 := hzero
  constructor
  · constructor
    · intro hft
      by_contra hn
      have hlt := hm ht h0 (lt_of_not_ge hn)
      rw [hf0] at hlt
      exact (not_le_of_gt hlt) hft
    · intro htn
      rcases eq_or_lt_of_le htn with heq | hlt
      · simpa only [← heq, hf0] using (le_rfl : (0 : ℝ) ≤ 0)
      · have hft := hm h0 ht hlt
        rw [hf0] at hft
        exact hft.le
  · constructor
    · intro hft
      exact hm.injOn ht h0 (hft.trans hf0.symm)
    · intro ht0
      simpa only [ht0] using hf0

/-- The ambient forward normalization used by the local smoothness tests. -/
theorem contDiffOn_timeScale {m : ℕ} {U : Set (Euclidean m)}
    (ε : Euclidean m → ℝ) (hε : ContDiffOn ℝ (⊤ : ℕ∞) ε U) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : Euclidean m × ℝ => (z.1, ε z.1 * z.2)) (U ×ˢ univ) :=
  contDiffOn_fst.prodMk ((hε.comp contDiffOn_fst (fun _ hz => hz.1)).mul contDiffOn_snd)

/-- The ambient inverse normalization is smooth wherever the width is nonzero. -/
theorem contDiffOn_timeUnscale {m : ℕ} {U : Set (Euclidean m)}
    (ε : Euclidean m → ℝ) (hε : ContDiffOn ℝ (⊤ : ℕ∞) ε U)
    (hne : ∀ q ∈ U, ε q ≠ 0) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : Euclidean m × ℝ => (z.1, z.2 / ε z.1)) (U ×ˢ univ) :=
  contDiffOn_fst.prodMk (contDiffOn_snd.div
    (hε.comp contDiffOn_fst (fun _ hz => hz.1)) (fun z hz => hne z.1 hz.1))

/-- All remaining nontrivial cases are positive-dimensional half-space models.
The reduction retains every manifold, including empty and disconnected ones. -/
theorem collar_exists_iff_positive_halfSpace :
    Specs.SmoothManifolds.Ch06.Collar.collar_existsType.{u} ↔
      ∀ {m : ℕ} {M : Type u} [TopologicalSpace M]
        (S : SmoothManifold (m + 1) .halfSpace M), Nonempty (SmoothCollar S) := by
  constructor
  · intro h m M inst S
    exact h S
  · intro h n kind M inst S
    cases kind with
    | euclidean => exact ⟨euclideanModelCollar S⟩
    | halfSpace =>
      cases n with
      | zero => exact ⟨zeroDimensionalCollar S⟩
      | succ m => exact h S


/-- A chart-constant section, multiplied by a supported smooth weight before
extension by zero. The resulting section has the original intrinsic fibers. -/
noncomputable def weightedChartSection {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
    (ρ : M → ℝ) (v : Euclidean n) : Section S := by
  classical
  exact fun p =>
    if hp : p ∈ e.source then ρ p • (B.fiberCoordinates.equiv e he p hp).symm v else 0

/-- Multiplication by a smooth supported weight makes zero extension smooth,
including at boundary points of the chart source. -/
theorem weightedChartSection_smooth {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
    (ρ : M → ℝ) (hρ : ScalarSmooth S.smoothStructure.val ρ)
    (hsupp : sectionSupport ρ ⊆ e.source) (v : Euclidean n) :
    letI := B.topology
    IsSmoothMap S B.manifold (fun p => ⟨p, weightedChartSection B e he ρ v p⟩) := by
  classical
  letI := B.topology
  intro p
  by_cases hp : p ∈ e.source
  · have hc : ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) S.smoothStructure.val
        (fun _ : M => v) p :=
      ⟨continuousAt_const, fun _ _ _ =>
        ⟨univ, isOpen_univ, mem_univ _, fun _ => v, contDiffOn_const,
          Eventually.of_forall (fun _ => rfl)⟩⟩
    apply TangentBundle.lift_smoothAt_of_coeff S B S
      (fun q => ⟨q, weightedChartSection B e he ρ v q⟩) p e he hp
      (fun q => ρ q • v)
      (manifoldContDiff_id (⊤ : ℕ∞) S.smoothStructure.val
        S.smoothStructure.property.1 p)
      (TangentBundle.euclidean_smul_smoothAt S _ _ p hc (hρ p))
    filter_upwards [e.open_source.mem_nhds hp] with q hq
    exact ⟨hq, by simp [weightedChartSection, hq]⟩
  · have hn : p ∉ sectionSupport ρ := fun h => hp (hsupp h)
    apply manifoldContDiffAt_congr (TangentBundle.zero_smooth S B p)
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hn] with q hq
    have hzero : ρ q = 0 := not_not.mp (fun h => hq (subset_closure h))
    simp [TangentBundleData.zeroSection, weightedChartSection, hzero]

/-- Finite sums of smooth intrinsic sections are smooth in the given tangent
bundle structure. -/
theorem section_sum_smooth {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    {ι : Type v} (s : Finset ι) (X : ι → Section S)
    (hX : ∀ i ∈ s, letI := B.topology
      IsSmoothMap S B.manifold (fun p => ⟨p, X i p⟩)) :
    letI := B.topology
    IsSmoothMap S B.manifold (fun p => ⟨p, ∑ i ∈ s, X i p⟩) := by
  classical
  letI := B.topology
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact TangentBundle.zero_smooth S B
  | @insert i s hi ih =>
    have hadd := (TangentBundle.operations_smooth S B S id (X i)
      (fun p => ∑ j ∈ s, X j p) (fun _ => 0)).1
      (hX i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hX j (Finset.mem_insert_of_mem hj)))
    simpa [hi] using hadd

/-- Locally finite sums also apply to sections with varying intrinsic fibers.
The support control gives one fixed finite sum on a neighborhood of any point. -/
theorem section_finsum_smooth {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    {ι : Type v} (X : ι → Section S) (U : ι → Set M)
    (hlf : LocallyFinite U) (hzero : ∀ i p, p ∉ U i → X i p = 0)
    (hX : ∀ i, letI := B.topology
      IsSmoothMap S B.manifold (fun p => ⟨p, X i p⟩)) :
    letI := B.topology
    IsSmoothMap S B.manifold (fun p => ⟨p, ∑ᶠ i, X i p⟩) := by
  classical
  letI := B.topology
  intro p
  obtain ⟨V, hV, hfin⟩ := hlf p
  apply manifoldContDiffAt_congr
    (section_sum_smooth B hfin.toFinset X (fun i _ => hX i) p)
  filter_upwards [hV] with q hq
  congr 1
  symm
  apply finsum_eq_sum_of_support_subset
  intro i hi
  apply hfin.mem_toFinset.mpr
  refine ⟨q, ?_, hq⟩
  by_contra hn
  exact hi (hzero i q hn)

/-- A smooth field strictly inward along the entire boundary. Positivity is
asserted in every original chart, so no choice of normal coordinates remains
in the conclusion. No compactness or connectedness is used. -/
theorem exists_inward_field {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n + 1) .halfSpace M) (B : TangentBundleStructure S) :
    ∃ X : SmoothField B, ∀ (p : intrinsicBoundary S)
      (e : ModelChart (n + 1) .halfSpace M) (he : e ∈ S.smoothStructure.val)
      (hp : p.val ∈ e.source),
      0 < B.fiberCoordinates.equiv e he p.val hp (X.val p.val) (Fin.last n) := by
  classical
  let ι := {e : ModelChart (n + 1) .halfSpace M // e ∈ S.smoothStructure.val}
  let U : ι → Set M := fun i => i.val.source
  obtain ⟨ρ, hρ, hsub⟩ := exists_smooth_partition S U (fun i => i.val.open_source)
    (fun p => by
      obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
      exact ⟨⟨e, he⟩, hp⟩)
  let V : ι → Section S := fun i =>
    weightedChartSection B i.val i.property (ρ i) (Pi.single (Fin.last n) 1)
  have hVzero (i : ι) (p : M) (hz : ρ i p = 0) : V i p = 0 := by
    simp [V, weightedChartSection, hz]
  have hVsmooth (i : ι) : letI := B.topology
      IsSmoothMap S B.manifold (fun p => ⟨p, V i p⟩) :=
    weightedChartSection_smooth B i.val i.property (ρ i) (hρ.1 i) (hsub i) _
  let X : SmoothField B := ⟨fun p => ∑ᶠ i, V i p,
    section_finsum_smooth B V (fun i => sectionSupport (ρ i)) hρ.2.2.1
      (fun i p hp => hVzero i p (not_not.mp (fun hn => hp (subset_closure hn))))
      hVsmooth⟩
  refine ⟨X, ?_⟩
  intro p e he hp
  have hfinite : Function.HasFiniteSupport (fun i => ρ i p.val) :=
    (hρ.2.2.1.point_finite p.val).subset (fun i hi => subset_closure hi)
  let s := hfinite.toFinset
  have hsp : ∀ i ∈ s, ρ i p.val ≠ 0 := fun i hi => hfinite.mem_toFinset.mp hi
  have hsupport : Function.support (fun i => V i p.val) ⊆ s := by
    intro i hi
    apply hfinite.mem_toFinset.mpr
    exact fun hz => hi (hVzero i p.val hz)
  have hsne : s.Nonempty := by
    have hex : ∃ i, ρ i p.val ≠ 0 := by
      by_contra! hn
      have hh := hρ.2.2.2 p.val
      simp [hn] at hh
    obtain ⟨i, hi⟩ := hex
    exact ⟨i, hfinite.mem_toFinset.mpr hi⟩
  have hpos (i : ι) (hi : i ∈ s) :
      0 < B.fiberCoordinates.equiv e he p.val hp (V i p.val) (Fin.last n) := by
    have hpi : p.val ∈ i.val.source := hsub i (subset_closure (hsp i hi))
    obtain ⟨r, hr, hnormal⟩ := boundary_transition_positive S p i.val e i.property he
      hpi hp (B.fiberCoordinates.equiv i.val i.property p.val hpi)
      (B.fiberCoordinates.equiv e he p.val hp)
      (B.fiberCoordinates.isCoordinates i.val i.property p.val hpi)
      (B.fiberCoordinates.isCoordinates e he p.val hp)
    have hunit := hnormal
      ((B.fiberCoordinates.equiv i.val i.property p.val hpi).symm
        (Pi.single (Fin.last n) 1))
    simp only [LinearEquiv.apply_symm_apply, Pi.single_eq_same, mul_one] at hunit
    change 0 < B.fiberCoordinates.equiv e he p.val hp
      (weightedChartSection B i.val i.property (ρ i) _ p.val) (Fin.last n)
    simp only [weightedChartSection, dite_eq_left hpi, map_smul, Pi.smul_apply,
      smul_eq_mul, hunit]
    exact mul_pos (lt_of_le_of_ne (hρ.2.1 i p.val) (Ne.symm (hsp i hi))) hr
  change 0 < B.fiberCoordinates.equiv e he p.val hp (∑ᶠ i, V i p.val) (Fin.last n)
  rw [finsum_eq_sum_of_support_subset _ hsupport, map_sum, Finset.sum_apply]
  exact Finset.sum_pos hpos hsne

/-- A strictly inward field admits an actual ambient smooth coefficient
extension on an open Euclidean state domain, with strictly positive normal
component throughout that domain. Agreement is required only on the original
half-space; the extension is allowed to leave it. -/
theorem inward_coefficient_extension {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n + 1) .halfSpace M) (B : TangentBundleStructure S)
    (X : SmoothField B) (p : M)
    (e : ModelChart (n + 1) .halfSpace M) (he : e ∈ S.smoothStructure.val)
    (hp : p ∈ e.source)
    (hpos : 0 < B.fiberCoordinates.equiv e he p hp (X.val p) (Fin.last n)) :
    ∃ (U : Set (Euclidean (n + 1))) (F : Euclidean (n + 1) → Euclidean (n + 1)),
      IsOpen U ∧ (e p).val ∈ U ∧ ContDiffOn ℝ (⊤ : ℕ∞) F U ∧
      (∀ z ∈ U, 0 < F z (Fin.last n)) ∧
      ∀ z ∈ U, ∀ hz : z ∈ halfSpaceSet (n + 1),
        (⟨z, hz⟩ : ModelSpace (n + 1) .halfSpace) ∈ e.target ∧
        F z = TangentBundle.chartFiber B e he
          ⟨e.symm ⟨z, hz⟩, X.val (e.symm ⟨z, hz⟩)⟩ := by
  obtain ⟨W, hW, hpW, F, hF, hEq⟩ := VectorFields.field_local_coordinates S B X p e he hp
  obtain ⟨V, hVEq, hV, hpV⟩ := eventually_nhds_iff.mp hEq
  let T : Set (ModelSpace (n + 1) .halfSpace) := e.target ∩ e.symm ⁻¹' V
  have hT : IsOpen T := e.symm.continuousOn.isOpen_inter_preimage e.open_target hV
  obtain ⟨O, hO, hOT⟩ := isOpen_induced_iff.mp hT
  have hpO : (e p).val ∈ O := by
    change e p ∈ Subtype.val ⁻¹' O
    rw [hOT]
    exact ⟨e.map_source hp, by simpa only [mem_preimage, e.left_inv hp] using hpV⟩
  have hpF : 0 < F (e p).val (Fin.last n) := by
    obtain ⟨hp', hEqp⟩ := hEq.self_of_nhds
    rw [hEqp]
    exact hpos
  have hnormal : ContinuousOn (fun z => F z (Fin.last n)) W :=
    (continuous_apply (Fin.last n)).comp_continuousOn hF.continuousOn
  let U := (W ∩ (fun z => F z (Fin.last n)) ⁻¹' Ioi 0) ∩ O
  refine ⟨U, F, (hnormal.isOpen_inter_preimage hW isOpen_Ioi).inter hO,
    ⟨⟨hpW, hpF⟩, hpO⟩, hF.mono (fun _ hz => hz.1.1),
    (fun _ hz => hz.1.2), ?_⟩
  intro z hz hzs
  have hzT : (⟨z, hzs⟩ : ModelSpace (n + 1) .halfSpace) ∈ T := by
    rw [← hOT]
    exact hz.2
  refine ⟨hzT.1, ?_⟩
  obtain ⟨hq, hqF⟩ := hVEq _ hzT.2
  rw [e.right_inv hzT.1] at hqF
  rw [hqF, TangentBundle.chartFiber_eq S B e he _ hq]

/-- Local existence at a boundary initial point is obtained in a genuine open
Euclidean state domain. The resulting ambient curve is in the half-space
exactly for nonnegative time, and solves the intrinsic coefficient equation
there. This assertion never posits a two-sided boundary-preserving flow. -/
theorem local_inward_coordinate_trajectory {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n + 1) .halfSpace M) (B : TangentBundleStructure S)
    (X : SmoothField B) (p : intrinsicBoundary S)
    (e : ModelChart (n + 1) .halfSpace M) (he : e ∈ S.smoothStructure.val)
    (hp : p.val ∈ e.source)
    (hpos : 0 < B.fiberCoordinates.equiv e he p.val hp (X.val p.val) (Fin.last n)) :
    ∃ (a b : ℝ) (x : ℝ → Euclidean (n + 1)),
      a < 0 ∧ 0 < b ∧ x 0 = (e p.val).val ∧
      ContDiffOn ℝ (⊤ : ℕ∞) x (Ioo a b) ∧
      ∀ t ∈ Ioo a b,
        (x t ∈ halfSpaceSet (n + 1) ↔ 0 ≤ t) ∧
        (x t ∈ halfSpaceFace (n + 1) ↔ t = 0) ∧
        ∀ hz : x t ∈ halfSpaceSet (n + 1),
          (⟨x t, hz⟩ : ModelSpace (n + 1) .halfSpace) ∈ e.target ∧ HasDerivAt x
            (TangentBundle.chartFiber B e he
              ⟨e.symm ⟨x t, hz⟩, X.val (e.symm ⟨x t, hz⟩)⟩) t := by
  obtain ⟨U, F, hU, hpU, hF, hFpos, hcoeff⟩ :=
    inward_coefficient_extension S B X p.val e he hp hpos
  let A := IntegralCurves.coordinateODE U hU F hF.continuousOn
  obtain ⟨I, x, hx, _⟩ :=
    D13Unified.Ch03.LocalExistenceUniqueness.local_existence_uniqueness
      A (IntegralCurves.coordinateODE_lipschitz hU hF) 0 (e p.val).val hpU
  have hr : MapsTo x I.carrier U := hx.1.2.1
  have hd (t : ℝ) (ht : t ∈ I.carrier) : HasDerivAt x (F (x t)) t := by
    have h := hx.1.2.2 t ht
    rwa [IntegralCurves.coordinateODE_eval (hU := hU) (hc := hF.continuousOn)
      t (x t) (hr ht)] at h
  obtain ⟨a, b, hab, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (I.isOpen.mem_nhds hx.2.1)
  have hzero : x 0 (Fin.last n) = 0 := by
    rw [hx.2.2]
    have h := (intrinsicBoundary_iff_chart S e he p.val hp).mp p.property
    exact h
  have hsign := inward_trajectory_sign hab.1 hab.2 x (fun t => F (x t))
    (fun t ht => hd t (hsub ht)) (fun t ht => hFpos _ (hr (hsub ht))) hzero
  refine ⟨a, b, x, hab.1, hab.2, hx.2.2,
    (IntegralCurves.smooth_of_autonomous I.isOpen hF hx.1.1.continuousOn hr hd).mono hsub, ?_⟩
  intro t ht
  refine ⟨(hsign t ht).1, (hsign t ht).2, ?_⟩
  intro hz
  have hc := hcoeff (x t) (hr (hsub ht)) hz
  exact ⟨hc.1, hc.2 ▸ hd t (hsub ht)⟩

/-- Euclidean uniqueness at the initial endpoint uses only right derivatives.
Thus local boundary trajectories can be compared without extending either
manifold-valued curve to negative time. -/
theorem local_oneSided_unique {n : ℕ} {U : Set (Euclidean n)} (hU : IsOpen U)
    {F : Euclidean n → Euclidean n} (hF : ContDiffOn ℝ 1 F U)
    {b : ℝ} (hb : 0 < b) {x y : ℝ → Euclidean n}
    (hx : ContinuousOn x (Ico 0 b)) (hy : ContinuousOn y (Ico 0 b))
    (hxd : ∀ t ∈ Ico 0 b, HasDerivWithinAt x (F (x t)) (Ici t) t)
    (hyd : ∀ t ∈ Ico 0 b, HasDerivWithinAt y (F (y t)) (Ici t) t)
    (hxU : x 0 ∈ U) (hzero : x 0 = y 0) :
    ∃ c : ℝ, 0 < c ∧ c ≤ b ∧ EqOn x y (Ico 0 c) := by
  obtain ⟨K, V, hV, hLip⟩ := (hF.contDiffAt (hU.mem_nhds hxU)).exists_lipschitzOnWith
  have hVy : V ∈ 𝓝 (y 0) := hzero ▸ hV
  have hnear : {t | x t ∈ V ∧ y t ∈ V} ∈ 𝓝[Ici (0 : ℝ)] 0 := by
    rw [← nhdsWithin_Ico_eq_nhdsGE hb]
    exact ((hx 0 ⟨le_rfl, hb⟩).eventually hV).and
      ((hy 0 ⟨le_rfl, hb⟩).eventually hVy)
  obtain ⟨δ, hδ, hδV⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp hnear
  refine ⟨min b δ, lt_min hb hδ, min_le_left _ _, ?_⟩
  intro t ht
  have htb : t < b := lt_of_lt_of_le ht.2 (min_le_left _ _)
  have htδ : t < δ := lt_of_lt_of_le ht.2 (min_le_right _ _)
  have hsub : Icc 0 t ⊆ Ico 0 b := fun z hz => ⟨hz.1, hz.2.trans_lt htb⟩
  have hsubδ : Icc 0 t ⊆ Ico 0 δ := fun z hz => ⟨hz.1, hz.2.trans_lt htδ⟩
  exact ODE_solution_unique_of_mem_Icc_right
    (v := fun _ z => F z) (s := fun _ => V)
    (fun _ _ => hLip) (hx.mono hsub)
    (fun z hz => hxd z (hsub (Ico_subset_Icc_self hz)))
    (fun z hz => (hδV (hsubδ (Ico_subset_Icc_self hz))).1)
    (hy.mono hsub) (fun z hz => hyd z (hsub (Ico_subset_Icc_self hz)))
    (fun z hz => (hδV (hsubδ (Ico_subset_Icc_self hz))).2)
    hzero ⟨ht.1, le_rfl⟩

/-- An actual one-sided manifold-valued trajectory. Its coordinate curves have
ambient smooth extensions also at time zero; no negative-time manifold values
are required. In the selected chart its ambient derivative is precisely the
intrinsic field coefficient at every permitted time. -/
theorem local_inward_trajectory {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n + 1) .halfSpace M) (B : TangentBundleStructure S)
    (X : SmoothField B) (p : intrinsicBoundary S)
    (e : ModelChart (n + 1) .halfSpace M) (he : e ∈ S.smoothStructure.val)
    (hp : p.val ∈ e.source)
    (hpos : 0 < B.fiberCoordinates.equiv e he p.val hp (X.val p.val) (Fin.last n)) :
    ∃ (b : ℝ) (hb : 0 < b) (γ : ↥(Ico (0 : ℝ) b) → M),
      Continuous γ ∧ γ ⟨0, le_rfl, hb⟩ = p.val ∧
      (∀ t, γ t ∈ e.source) ∧
      (∀ (d : ModelChart (n + 1) .halfSpace M), d ∈ S.smoothStructure.val →
        ∀ t, γ t ∈ d.source →
          LocalCoordinateExtension (⊤ : ℕ∞) (fun s : ↥(Ico (0 : ℝ) b) =>
            fun _ : Fin 1 => s.val) (fun s => (d (γ s)).val) t) ∧
      ∃ x : ℝ → Euclidean (n + 1), (∀ t, x t.val = (e (γ t)).val) ∧
        ∀ t, ∃ ht : γ t ∈ e.source,
          HasDerivAt x (B.fiberCoordinates.equiv e he (γ t) ht (X.val (γ t))) t.val := by
  classical
  obtain ⟨a, b, x, ha, hb, hx0, hxs, hcurve⟩ :=
    local_inward_coordinate_trajectory S B X p e he hp hpos
  have hsub : Ico 0 b ⊆ Ioo a b := fun t ht => ⟨ha.trans_le ht.1, ht.2⟩
  let z : ↥(Ico (0 : ℝ) b) → ModelSpace (n + 1) .halfSpace := fun t =>
    ⟨x t.val, ((hcurve t.val (hsub t.property)).1).mpr t.property.1⟩
  have hztarget (t : ↥(Ico (0 : ℝ) b)) : z t ∈ e.target :=
    ((hcurve t.val (hsub t.property)).2.2 (z t).property).1
  let γ : ↥(Ico (0 : ℝ) b) → M := fun t => e.symm (z t)
  have hγsource (t : ↥(Ico (0 : ℝ) b)) : γ t ∈ e.source := e.map_target (hztarget t)
  have hγcoords (t : ↥(Ico (0 : ℝ) b)) : (e (γ t)).val = x t.val := by
    change (e (e.symm (z t))).val = x t.val
    rw [e.right_inv (hztarget t)]
  have hxc : Continuous (fun t : ↥(Ico (0 : ℝ) b) => x t.val) :=
    (hxs.continuousOn.mono hsub).domRestrict
  have hzc : Continuous z := hxc.subtype_mk _
  have hγc : Continuous γ := e.symm.continuousOn.comp_continuous hzc hztarget
  refine ⟨b, hb, γ, hγc, ?_, hγsource, ?_, x, fun t => (hγcoords t).symm, ?_⟩
  · change e.symm (z ⟨0, le_rfl, hb⟩) = p.val
    have hz0 : z ⟨0, le_rfl, hb⟩ = e p.val := Subtype.ext hx0
    rw [hz0, e.left_inv hp]
  · intro d hd t hdt
    have httrans := LocalCoordinateExtension.precomp
      (chartContDiffAt_of_compatible (S.smoothStructure.property.1.2 e he d hd)
        (hγsource t) hdt) hγc.continuousAt rfl
    have heq : (fun s => (e (γ s)).val) = (fun s => x s.val) := funext hγcoords
    change LocalCoordinateExtension (⊤ : ℕ∞) (fun s => (e (γ s)).val)
      (fun s => (d (γ s)).val) t at httrans
    rw [heq] at httrans
    apply LocalCoordinateExtension.comp httrans
    refine ⟨(fun v : Euclidean 1 => v 0) ⁻¹' Ioo a b,
      isOpen_Ioo.preimage (continuous_apply 0), hsub t.property,
      (fun v : Euclidean 1 => x (v 0)), ?_, Eventually.of_forall (fun _ => rfl)⟩
    exact hxs.comp
      (ContinuousLinearMap.proj (0 : Fin 1) : Euclidean 1 →L[ℝ] ℝ).contDiff.contDiffOn
      (fun _ hv => hv)
  · intro t
    refine ⟨hγsource t, ?_⟩
    have h := ((hcurve t.val (hsub t.property)).2.2 (z t).property).2
    rwa [TangentBundle.chartFiber_eq S B e he _ (hγsource t)] at h

/-- The linear map obtained by adjoining a transverse vector to the standard
boundary hyperplane is an isomorphism. Its last coordinate determines the
time coefficient, even when the vector also has tangential components. -/
noncomputable def transverseNormalEquiv {n : ℕ} (v : Euclidean (n + 1))
    (hv : v (Fin.last n) ≠ 0) : Euclidean (n + 1) ≃L[ℝ] Euclidean (n + 1) :=
  LinearEquiv.toContinuousLinearEquiv {
    toFun := fun z => Fin.snoc (Fin.init z) 0 + z (Fin.last n) • v
    invFun := fun w => Fin.snoc
      (fun i => w i.castSucc - w (Fin.last n) / v (Fin.last n) * v i.castSucc)
      (w (Fin.last n) / v (Fin.last n))
    left_inv := by
      intro z
      ext i
      cases i using Fin.lastCases with
      | last => simp [hv]
      | cast i => simp [Fin.init, hv]
    right_inv := by
      intro w
      ext i
      cases i using Fin.lastCases with
      | last => simp [hv]
      | cast i => simp [Fin.init]
    map_add' := by
      intro x y
      ext i
      cases i using Fin.lastCases <;> simp [Fin.init, add_mul] <;> ring
    map_smul' := by
      intro r x
      ext i
      cases i using Fin.lastCases <;> simp [Fin.init, mul_add, mul_assoc] }

@[simp] theorem transverseNormalEquiv_apply {n : ℕ} (v : Euclidean (n + 1))
    (hv : v (Fin.last n) ≠ 0) (z : Euclidean (n + 1)) :
    transverseNormalEquiv v hv z =
      Fin.snoc (Fin.init z) 0 + z (Fin.last n) • v := rfl

/-- A smooth Euclidean germ with invertible derivative and the normal-time
sign property restricts to an actual local homeomorphism of half-spaces.
Both coordinate directions have smooth ambient extensions on their entire
relative source and target. This is the local inverse step for a boundary
flowout, without any two-sided manifold trajectory assumption. -/
theorem halfSpace_inverse_of_sign {n : ℕ}
    (g : Euclidean (n + 1) → Euclidean (n + 1))
    (U : Set (Euclidean (n + 1))) (hU : IsOpen U)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g U) (p : HalfSpace (n + 1)) (hp : p.val ∈ U)
    (L : Euclidean (n + 1) ≃L[ℝ] Euclidean (n + 1))
    (hL : HasFDerivAt g (L : Euclidean (n + 1) →L[ℝ] Euclidean (n + 1)) p.val)
    (hsign : ∀ᶠ x in 𝓝 p.val,
      (g x ∈ halfSpaceSet (n + 1) ↔ x ∈ halfSpaceSet (n + 1))) :
    ∃ h : OpenPartialHomeomorph (HalfSpace (n + 1)) (HalfSpace (n + 1)),
      p ∈ h.source ∧
      (∀ x ∈ h.source, (h x).val = g x.val) ∧
      (∀ x ∈ h.source, LocalCoordinateExtension (⊤ : ℕ∞) Subtype.val
        (fun y => (h y).val) x) ∧
      (∀ y ∈ h.target, LocalCoordinateExtension (⊤ : ℕ∞) Subtype.val
        (fun z => (h.symm z).val) y) := by
  obtain ⟨j₀, hpj₀, hj₀, hji₀⟩ := InteriorInverse.euclidean_inverse
    (⊤ : ℕ∞) (by simp) g U hU hg p.val hp _ hL L.bijective
  obtain ⟨W, hWsub, hW, hpW⟩ := mem_nhds_iff.mp hsign
  let j := j₀.restrOpen (U ∩ W) (hU.inter hW)
  have hpj : p.val ∈ j.source := ⟨hpj₀, hp, hpW⟩
  have hj : (j : Euclidean (n + 1) → Euclidean (n + 1)) = g := hj₀
  have hsame : j.IsImage (halfSpaceSet (n + 1)) (halfSpaceSet (n + 1)) := by
    intro x hx
    rw [hj]
    exact hWsub hx.2.2
  let h := BoundaryInverse.restrictInvariant j (halfSpaceSet (n + 1)) hsame p
  have hval (x : HalfSpace (n + 1)) (hx : x ∈ h.source) : (h x).val = g x.val :=
    (BoundaryInverse.restrictInvariant_val j _ hsame p x hx).trans (congrFun hj x.val)
  refine ⟨h, hpj, hval, ?_, ?_⟩
  · intro x hx
    refine ⟨U, hU, hx.2.1, g, hg, ?_⟩
    filter_upwards [h.open_source.mem_nhds hx] with z hz
    exact (hval z hz).symm
  · intro y hy
    refine ⟨j.target, j.open_target, hy, j.symm, hji₀.mono inter_subset_left, ?_⟩
    filter_upwards [h.open_target.mem_nhds hy] with z hz
    exact (BoundaryInverse.restrictInvariant_symm_val j _ hsame p z hz).symm

/-- The globally smooth strictly inward field requires no separately assumed
realization of the tangent bundle. -/
theorem exists_inward_bundle_field {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n + 1) .halfSpace M) :
    ∃ (B : TangentBundleStructure S) (X : SmoothField B),
      ∀ (p : intrinsicBoundary S)
        (e : ModelChart (n + 1) .halfSpace M) (he : e ∈ S.smoothStructure.val)
        (hp : p.val ∈ e.source),
        0 < B.fiberCoordinates.equiv e he p.val hp (X.val p.val) (Fin.last n) := by
  obtain ⟨B⟩ := TangentBundle.exists_bundle S
  obtain ⟨X, hX⟩ := exists_inward_field S B
  exact ⟨B, X, hX⟩

/-- One fixed global inward field supplies an actual one-sided trajectory
from every boundary point, without a prechosen chart. Smoothness is tested in
every smooth chart, including at zero, by ambient local extensions. -/
theorem exists_inward_bundle_field_trajectories {n : ℕ} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold (n + 1) .halfSpace M) :
    ∃ (B : TangentBundleStructure S) (X : SmoothField B),
      (∀ (p : intrinsicBoundary S)
        (e : ModelChart (n + 1) .halfSpace M) (he : e ∈ S.smoothStructure.val)
        (hp : p.val ∈ e.source),
        0 < B.fiberCoordinates.equiv e he p.val hp (X.val p.val) (Fin.last n)) ∧
      ∀ p : intrinsicBoundary S,
        ∃ (e : ModelChart (n + 1) .halfSpace M) (he : e ∈ S.smoothStructure.val)
          (b : ℝ) (hb : 0 < b) (γ : ↥(Ico (0 : ℝ) b) → M),
          Continuous γ ∧ γ ⟨0, le_rfl, hb⟩ = p.val ∧
          (∀ t, γ t ∈ e.source) ∧
          (∀ (d : ModelChart (n + 1) .halfSpace M), d ∈ S.smoothStructure.val →
            ∀ t, γ t ∈ d.source →
              LocalCoordinateExtension (⊤ : ℕ∞)
                (fun s : ↥(Ico (0 : ℝ) b) => fun _ : Fin 1 => s.val)
                (fun s => (d (γ s)).val) t) ∧
          ∃ x : ℝ → Euclidean (n + 1),
            (∀ t, x t.val = (e (γ t)).val) ∧
            ∀ t, ∃ ht : γ t ∈ e.source,
              HasDerivAt x
                (B.fiberCoordinates.equiv e he (γ t) ht (X.val (γ t))) t.val := by
  obtain ⟨B, X, hX⟩ := exists_inward_bundle_field S
  refine ⟨B, X, hX, ?_⟩
  intro p
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p.val
  obtain ⟨b, hb, γ, hγ, hγ0, hγsource, hγsmooth, x, hx, hderiv⟩ :=
    local_inward_trajectory S B X p e he hp (hX p e he hp)
  exact ⟨e, he, b, hb, γ, hγ, hγ0, hγsource, hγsmooth, x, hx, hderiv⟩

/-- A coordinate coefficient extension regarded as an autonomous ODE on its
actual open state domain. -/
def coefficientAutonomousODE {n : ℕ} (U : Set (Euclidean n)) (hU : IsOpen U)
    (F : Euclidean n → Euclidean n) (hc : ContinuousOn F U) :
    D13Unified.AutonomousODE (Euclidean n) where
  domain := U
  isOpen_domain := hU
  field := fun z => F z.val
  continuous_field := hc.domRestrict

@[simp] theorem coefficientAutonomousODE_eval {n : ℕ}
    {U : Set (Euclidean n)} {hU : IsOpen U}
    {F : Euclidean n → Euclidean n} {hc : ContinuousOn F U}
    {z : Euclidean n} (hz : z ∈ U) :
    (coefficientAutonomousODE U hU F hc).eval z = F z := by
  simp [D13Unified.AutonomousODE.eval,
    Specs.D13Unified.Ch01.AutonomousParameters.autonomousEvalValue,
    coefficientAutonomousODE, hz]

/-- Smooth coefficients give a canonical jointly smooth flow on its actual
open maximal domain. -/
theorem coefficient_flow_smooth {n : ℕ} {U : Set (Euclidean n)} (hU : IsOpen U)
    {F : Euclidean n → Euclidean n} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F U) :
    let A := coefficientAutonomousODE U hU F hF.continuousOn
    IsOpen (D13Unified.Ch06.StateDerivative.flowDomain A) ∧
      ContDiffOn ℝ (⊤ : ℕ∞)
        (fun q : ℝ × Euclidean n => D13Unified.Ch06.StateDerivative.flow A q.1 q.2)
        (D13Unified.Ch06.StateDerivative.flowDomain A) := by
  dsimp only
  let A := coefficientAutonomousODE U hU F hF.continuousOn
  have hA : ContDiffOn ℝ (⊤ : ℕ∞) A.eval A.domain :=
    hF.congr (fun _ hz => coefficientAutonomousODE_eval hz)
  have hA1 : ContDiffOn ℝ 1 A.eval A.domain := hA.of_le (by simp)
  refine ⟨D13Unified.Ch06.C1Dependence.isOpen_flowDomain A hA1, ?_⟩
  apply contDiffOn_infty.mpr
  intro k
  by_cases hk : k = 0
  · subst k
    exact (D13Unified.Ch06.CkDependence.autonomous_joint_ck 1 (by decide)
      A hA1).of_le (by simp)
  · exact D13Unified.Ch06.CkDependence.autonomous_joint_ck k
      (Nat.one_le_iff_ne_zero.mpr hk) A (hA.of_le (by simp))

/-- A uniform open time interval and open set of initial states for the ambient
flow. The sign test is for boundary initial states only; negative-time values
are ambient Euclidean states and need not lie in the half-space. -/
theorem local_inward_coordinate_flow {n : ℕ} {U : Set (Euclidean (n + 1))}
    (hU : IsOpen U) {F : Euclidean (n + 1) → Euclidean (n + 1)}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F U)
    (hpos : ∀ z ∈ U, 0 < F z (Fin.last n))
    {p : Euclidean (n + 1)} (hp : p ∈ U) :
    ∃ (b : ℝ) (V : Set (Euclidean (n + 1)))
      (Φ : ℝ × Euclidean (n + 1) → Euclidean (n + 1)),
      0 < b ∧ IsOpen V ∧ p ∈ V ∧ V ⊆ U ∧
      ContDiffOn ℝ (⊤ : ℕ∞) Φ (Ioo (-b) b ×ˢ V) ∧
      (∀ z ∈ V, Φ (0,z) = z) ∧
      (∀ z ∈ V, ∀ t ∈ Ioo (-b) b,
        Φ (t,z) ∈ U ∧ HasDerivAt (fun s => Φ (s,z)) (F (Φ (t,z))) t) ∧
      (∀ z ∈ V, z (Fin.last n) = 0 → ∀ t ∈ Ioo (-b) b,
        (Φ (t,z) ∈ halfSpaceSet (n + 1) ↔ 0 ≤ t) ∧
        (Φ (t,z) ∈ halfSpaceFace (n + 1) ↔ t = 0)) := by
  let A := coefficientAutonomousODE U hU F hF.continuousOn
  let Φ : ℝ × Euclidean (n + 1) → Euclidean (n + 1) := fun q =>
    D13Unified.Ch06.StateDerivative.flow A q.1 q.2
  have hA : ContDiffOn ℝ 1 A.eval A.domain :=
    (hF.of_le (by simp)).congr (fun _ hz => coefficientAutonomousODE_eval hz)
  have hzero := D13Unified.Ch11.Flow.flow_zero A hA p hp
  obtain ⟨hDo, hΦ⟩ := coefficient_flow_smooth hU hF
  obtain ⟨b, hb, hbD⟩ := Metric.mem_nhds_iff.mp (hDo.mem_nhds hzero.1)
  let V := Metric.ball p b
  have htube : Ioo (-b) b ×ˢ V ⊆ D13Unified.Ch06.StateDerivative.flowDomain A := by
    apply Subset.trans _ hbD
    rw [← ball_prod_same]
    exact prod_mono (by simp [Real.ball_eq_Ioo]) Subset.rfl
  have h0 (z : Euclidean (n + 1)) (hz : z ∈ V) :
      (0,z) ∈ D13Unified.Ch06.StateDerivative.flowDomain A :=
    htube ⟨⟨neg_neg_of_pos hb, hb⟩, hz⟩
  have hVU : V ⊆ U := fun z hz => (h0 z hz).1
  have hΦzero (z : Euclidean (n + 1)) (hz : z ∈ V) : Φ (0,z) = z :=
    (D13Unified.Ch11.Flow.flow_zero A hA z (hVU hz)).2
  have hder (z : Euclidean (n + 1)) (hz : z ∈ V) (t : ℝ)
      (ht : t ∈ Ioo (-b) b) :
      Φ (t,z) ∈ U ∧ HasDerivAt (fun s => Φ (s,z)) (F (Φ (t,z))) t := by
    have hIVP := D13Unified.Ch06.StateDerivative.flow_ivp A hA (hVU hz)
    have htI := (htube (a := (t,z)) ⟨ht, hz⟩).2
    have hstate : Φ (t,z) ∈ U := hIVP.1.2.1 t htI
    refine ⟨hstate, ?_⟩
    have hd := hIVP.1.2.2 t htI
    rw [D13Unified.AutonomousODE.toODE_eval] at hd
    change HasDerivAt (fun s => Φ (s,z)) (A.eval (Φ (t,z))) t at hd
    have heval : A.eval (Φ (t,z)) = F (Φ (t,z)) := coefficientAutonomousODE_eval hstate
    rwa [heval] at hd
  refine ⟨b, V, Φ, hb, Metric.isOpen_ball, Metric.mem_ball_self hb,
    hVU, hΦ.mono htube, hΦzero, hder, ?_⟩
  intro z hz hface
  apply inward_trajectory_sign (neg_neg_of_pos hb) hb
    (fun t => Φ (t,z)) (fun t => F (Φ (t,z)))
    (fun t ht => (hder z hz t ht).2)
    (fun t ht => hpos _ (hder z hz t ht).1)
  rw [hΦzero z hz]
  exact hface


/-- Projection onto the boundary hyperplane, keeping the ambient dimension. -/
noncomputable def faceProjection {n : ℕ} :
    Euclidean (n + 1) →L[ℝ] Euclidean (n + 1) :=
  LinearMap.toContinuousLinearMap {
    toFun := fun z => Fin.snoc (Fin.init z) 0
    map_add' := by
      intro x y
      ext i
      cases i using Fin.lastCases <;> simp [Fin.init]
    map_smul' := by
      intro r x
      ext i
      cases i using Fin.lastCases <;> simp [Fin.init] }

@[simp] theorem faceProjection_apply {n : ℕ} (z : Euclidean (n + 1)) :
    faceProjection z = Fin.snoc (Fin.init z) 0 := rfl

/-- The initial-state identity and time derivative determine the full joint
flow derivative at time zero. -/
theorem flow_derivative_zero_of_trace {n : ℕ}
    (Φ : ℝ × Euclidean n → Euclidean n) (p v : Euclidean n)
    (hd : DifferentiableAt ℝ Φ (0, p))
    (htrace : ∀ᶠ z in 𝓝 p, Φ (0,z) = z)
    (ht : HasDerivAt (fun t => Φ (t,p)) v 0) :
    HasFDerivAt Φ
      (((ContinuousLinearMap.id ℝ ℝ).smulRight v).coprod
        (ContinuousLinearMap.id ℝ (Euclidean n))) (0,p) := by
  have h := hd.hasFDerivAt
  have htime := h.comp (0 : ℝ) (hasFDerivAt_prodMk_left (𝕜 := ℝ) (0 : ℝ) p)
  have hstate := h.comp p (hasFDerivAt_prodMk_right (𝕜 := ℝ) (0 : ℝ) p)
  have hstate' : HasFDerivAt (fun z => Φ (0,z)) (ContinuousLinearMap.id ℝ (Euclidean n)) p :=
    (hasFDerivAt_id p).congr_of_eventuallyEq (by filter_upwards [htrace] with z hz; exact hz)
  have hte := htime.unique ht.hasFDerivAt
  have hse := hstate.unique hstate'
  have he : fderiv ℝ Φ (0,p) =
      ((ContinuousLinearMap.id ℝ ℝ).smulRight v).coprod
        (ContinuousLinearMap.id ℝ (Euclidean n)) := by
    apply ContinuousLinearMap.ext
    intro q
    have ha := congrArg (fun L : ℝ →L[ℝ] Euclidean n => L q.1) hte
    have hb := congrArg (fun L : Euclidean n →L[ℝ] Euclidean n => L q.2) hse
    have hs : fderiv ℝ Φ (0,p) q = q.1 • v + q.2 := by
      rw [show q = (q.1,0) + (0,q.2) by simp, map_add]
      simpa using congrArg₂ (fun a b : Euclidean n => a+b) ha hb
    exact hs
  simpa only [he] using h

/-- An ambient flow based on the boundary face has invertible derivative
where its initial velocity is strictly transverse. -/
theorem face_flow_derivative_zero {n : ℕ}
    (Φ : ℝ × Euclidean (n + 1) → Euclidean (n + 1))
    (p v : Euclidean (n + 1)) (hp : p (Fin.last n) = 0)
    (hv : v (Fin.last n) ≠ 0)
    (hd : DifferentiableAt ℝ Φ (0, p))
    (htrace : ∀ᶠ z in 𝓝 p, Φ (0,z) = z)
    (ht : HasDerivAt (fun t => Φ (t,p)) v 0) :
    HasFDerivAt (fun z : Euclidean (n + 1) =>
      Φ (z (Fin.last n), faceProjection z))
      (transverseNormalEquiv v hv : Euclidean (n + 1) →L[ℝ] Euclidean (n + 1)) p := by
  let c : Euclidean (n + 1) →L[ℝ] ℝ × Euclidean (n + 1) :=
    (ContinuousLinearMap.proj (Fin.last n)).prod faceProjection
  have hc : c p = (0,p) := by
    apply Prod.ext
    · exact hp
    · change Fin.snoc (Fin.init p) 0 = p
      rw [← hp, Fin.snoc_init_self]
  have hf := flow_derivative_zero_of_trace Φ p v hd htrace ht
  rw [← hc] at hf
  convert hf.comp p c.hasFDerivAt using 1
  · rfl
  ext z i
  change (Fin.snoc (Fin.init z) 0 + z (Fin.last n) • v) i =
    (z (Fin.last n) • v + faceProjection z) i
  rw [faceProjection_apply, add_comm]

/-- A transverse smooth ambient flow based on a boundary face gives a
relative local diffeomorphism with the actual half-space topology. -/
theorem local_face_flow_inverse {n : ℕ}
    (Φ : ℝ × Euclidean (n + 1) → Euclidean (n + 1))
    {b : ℝ} (hb : 0 < b) (V : Set (Euclidean (n + 1))) (hV : IsOpen V)
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ (Ioo (-b) b ×ˢ V))
    (hzero : ∀ z ∈ V, Φ (0,z) = z)
    (p : HalfSpace (n + 1)) (hp : p.val ∈ V) (hpface : p.val (Fin.last n) = 0)
    (v : Euclidean (n + 1)) (hv : v (Fin.last n) ≠ 0)
    (ht : HasDerivAt (fun t => Φ (t,p.val)) v 0)
    (hsign : ∀ z ∈ V, z (Fin.last n) = 0 → ∀ t ∈ Ioo (-b) b,
      (Φ (t,z) ∈ halfSpaceSet (n + 1) ↔ 0 ≤ t)) :
    ∃ h : OpenPartialHomeomorph (HalfSpace (n + 1)) (HalfSpace (n + 1)),
      p ∈ h.source ∧
      (∀ x ∈ h.source, (h x).val = Φ (x.val (Fin.last n), faceProjection x.val)) ∧
      (∀ x ∈ h.source, LocalCoordinateExtension (⊤ : ℕ∞) Subtype.val
        (fun y => (h y).val) x) ∧
      (∀ y ∈ h.target, LocalCoordinateExtension (⊤ : ℕ∞) Subtype.val
        (fun z => (h.symm z).val) y) := by
  let c : Euclidean (n + 1) →L[ℝ] ℝ × Euclidean (n + 1) :=
    (ContinuousLinearMap.proj (Fin.last n)).prod faceProjection
  let D := c ⁻¹' (Ioo (-b) b ×ˢ V)
  have hD : IsOpen D := (isOpen_Ioo.prod hV).preimage c.continuous
  have hproj : faceProjection p.val = p.val := by
    rw [faceProjection_apply, ← hpface, Fin.snoc_init_self]
  have hcp : c p.val = (0,p.val) := Prod.ext hpface hproj
  have hpD : p.val ∈ D := by
    change c p.val ∈ Ioo (-b) b ×ˢ V
    rw [hcp]
    exact ⟨⟨neg_neg_of_pos hb, hb⟩, hp⟩
  have hΦp : DifferentiableAt ℝ Φ (0,p.val) :=
    (hΦ.contDiffAt ((isOpen_Ioo.prod hV).mem_nhds
      ⟨⟨neg_neg_of_pos hb, hb⟩, hp⟩)).differentiableAt (by simp)
  have htrace : ∀ᶠ z in 𝓝 p.val, Φ (0,z) = z := by
    filter_upwards [hV.mem_nhds hp] with z hz
    exact hzero z hz
  have hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => Φ (c z)) D :=
    hΦ.comp c.contDiff.contDiffOn (fun _ hz => hz)
  apply halfSpace_inverse_of_sign (fun z => Φ (c z)) D hD hg p hpD
    (transverseNormalEquiv v hv)
    (face_flow_derivative_zero Φ p.val v hpface hv hΦp htrace ht)
  filter_upwards [hD.mem_nhds hpD] with x hx
  exact hsign (faceProjection x) hx.2 (by simp) (x (Fin.last n)) hx.1


/-- An ambient coordinate representative solving the intrinsic coefficient
ODE gives the intrinsic right derivative in every smooth chart. -/
theorem oneSided_derivative_of_chart {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    (X : SmoothField B) {b : ℝ} {γ : ℝ → M}
    (hc : ContinuousOn γ (Ico 0 b))
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
    (hr : MapsTo γ (Ico 0 b) e.source)
    (x : ℝ → Euclidean n)
    (hx : ∀ t ∈ Ico 0 b, x t = (e (γ t)).val)
    (hd : ∀ t (ht : t ∈ Ico 0 b), HasDerivAt x
      (B.fiberCoordinates.equiv e he (γ t) (hr ht) (X.val (γ t))) t) :
    ∀ t ∈ Ico 0 b, ∀ (d : ModelChart n a M) (hdm : d ∈ S.smoothStructure.val)
      (hdt : γ t ∈ d.source), HasDerivWithinAt (fun s => (d (γ s)).val)
        (B.fiberCoordinates.equiv d hdm (γ t) hdt (X.val (γ t))) (Ico 0 b) t := by
  intro t ht d hdm hdt
  have hp := hr ht
  have hcompat := S.smoothStructure.property.1.2 e he d hdm
  obtain ⟨U, hU, hpU, F, hF, hrep⟩ :=
    chartContDiffAt_of_compatible hcompat hp hdt
  have hct := hc t ht
  have heq := hrep.comp_tendsto hct
  have hx0 := hx t ht
  have hdx := hd t ht
  change (e (γ t)).val ∈ U at hpU
  have hpx : x t ∈ U := hx0 ▸ hpU
  have hdF := ((hF.contDiffAt (hU.mem_nhds hpx)).differentiableAt
    (by simp)).hasFDerivAt.comp_hasDerivAt t hdx
  have hvel := TangentBundle.transition_jacobian S B.fiberCoordinates e d he hdm
    (γ t) hp hdt U F hU hpU hF hrep (X.val (γ t))
  rw [← hx0] at hvel
  rw [← hvel] at hdF
  apply hdF.hasDerivWithinAt.congr_of_eventuallyEq_of_mem _ ht
  filter_upwards [heq, self_mem_nhdsWithin] with s hs hsI
  exact hs.symm.trans (congrArg F (hx s hsI).symm)


private theorem contDiffOn_snoc {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {m : ℕ} {s : Set X} {r : ℕ∞} {f : X → Euclidean m} {g : X → ℝ}
    (hf : ContDiffOn ℝ r f s) (hg : ContDiffOn ℝ r g s) :
    ContDiffOn ℝ r (fun x => (Fin.snoc (f x) (g x) : Euclidean (m+1))) s := by
  apply contDiffOn_pi.mpr
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using hg
  · simpa using (contDiffOn_pi.mp hf) j

private theorem contDiff_init {m : ℕ} {r : ℕ∞} :
    ContDiff ℝ r (Fin.init : Euclidean (m+1) → Euclidean m) := by
  apply contDiff_pi.mpr
  intro i
  exact contDiff_apply ℝ (fun _ => ℝ) i.castSucc

/-- A scalar germ in the boundary variables may be multiplied into the last
coordinate while retaining one ambient extension on an open neighborhood. -/
theorem localCoordinateExtension_timeScale {X : Type u} [TopologicalSpace X]
    {m : ℕ} {r : ℕ∞} (ι : X → Euclidean m) (τ ε : X → ℝ) (x : X)
    (hε : ∃ U : Set (Euclidean m), IsOpen U ∧ ι x ∈ U ∧
      ∃ E : Euclidean m → ℝ, ContDiffOn ℝ r E U ∧
        (fun y => E (ι y)) =ᶠ[𝓝 x] ε) :
    LocalCoordinateExtension r (fun y => Fin.snoc (ι y) (τ y))
      (fun y => Fin.snoc (ι y) (ε y * τ y)) x := by
  obtain ⟨U, hU, hxU, E, hE, heq⟩ := hε
  let V : Set (Euclidean (m+1)) := Fin.init ⁻¹' U
  refine ⟨V, hU.preimage (contDiff_init (r := r)).continuous, ?_,
    fun z => Fin.snoc (Fin.init z) (E (Fin.init z) * z (Fin.last m)), ?_, ?_⟩
  · simpa [V] using hxU
  · apply contDiffOn_snoc contDiff_init.contDiffOn
    exact (hE.comp contDiff_init.contDiffOn (fun z hz => hz)).mul
      (contDiff_apply ℝ (fun _ => ℝ) (Fin.last m)).contDiffOn
  · filter_upwards [heq] with y hy
    simp [hy]

/-- Replace a source coordinate map by an equal germ. -/
theorem localCoordinateExtension_congr_source {X : Type u} [TopologicalSpace X]
    {n m : ℕ} {r : ℕ∞} {ι κ : X → Euclidean n} {f : X → Euclidean m}
    {x : X} (h : LocalCoordinateExtension r ι f x) (heq : ι =ᶠ[𝓝 x] κ) :
    LocalCoordinateExtension r κ f x := by
  obtain ⟨U, hU, hxU, F, hF, he⟩ := h
  refine ⟨U, hU, ?_, F, hF, (heq.fun_comp F).symm.trans he⟩
  rwa [← heq.eq_of_nhds]

/-- The reverse change of time has a smooth ambient extension whenever its
width is nonzero at the base point. -/
theorem localCoordinateExtension_timeUnscale {X : Type u} [TopologicalSpace X]
    {m : ℕ} {r : ℕ∞} (ι : X → Euclidean m) (τ ε : X → ℝ) (x : X)
    (hε : ∃ U : Set (Euclidean m), IsOpen U ∧ ι x ∈ U ∧
      ∃ E : Euclidean m → ℝ, ContDiffOn ℝ r E U ∧
        (fun y => E (ι y)) =ᶠ[𝓝 x] ε)
    (hne : ε x ≠ 0) :
    LocalCoordinateExtension r (fun y => Fin.snoc (ι y) (τ y))
      (fun y => Fin.snoc (ι y) (τ y / ε y)) x := by
  have hi : ∃ U : Set (Euclidean m), IsOpen U ∧ ι x ∈ U ∧
      ∃ E : Euclidean m → ℝ, ContDiffOn ℝ r E U ∧
        (fun y => E (ι y)) =ᶠ[𝓝 x] (fun y => (ε y)⁻¹) := by
    obtain ⟨U, hU, hxU, E, hE, heq⟩ := hε
    refine ⟨U ∩ E ⁻¹' ({0}ᶜ : Set ℝ),
      hE.continuousOn.isOpen_inter_preimage hU (isClosed_singleton.isOpen_compl),
      ⟨hxU, ?_⟩, fun z => (E z)⁻¹, ?_, heq.fun_comp Inv.inv⟩
    · change E (ι x) ≠ 0
      rwa [heq.eq_of_nhds]
    · exact (hE.mono inter_subset_left).inv (fun z hz => hz.2)
  simpa only [div_eq_mul_inv, mul_comm] using
    localCoordinateExtension_timeScale ι τ (fun y => (ε y)⁻¹) x hi

/-- The specified collar coordinates agree with coordinates of any actual face
restriction of the original chart. -/
theorem collarCoordinates_eq_face {m : ℕ} {kind : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold (m+1) kind M}
    {e : ModelChart (m+1) kind M}
    {b : ModelChart m .euclidean (intrinsicBoundary S)}
    (hb : IsFaceRestriction S e b) {x : CollarSource S}
    (hx : x.1.val ∈ e.source) :
    collarCoordinates e x = Fin.snoc (b x.1).val x.2.val := by
  have hx' : x.1 ∈ b.source := by rw [hb.1]; exact hx
  simp only [collarCoordinates]
  congr 1
  funext i
  exact (hb.2.2 x.1 hx' i).symm

/-- Product coordinates on a possibly variable one-sided time domain. -/
def boundaryTimeCoordinates {m : ℕ} {kind : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold (m+1) kind M}
    (e : ModelChart (m+1) kind M) (x : intrinsicBoundary S × ℝ) : Euclidean (m+1) :=
  Fin.snoc (fun i : Fin m => (e x.1.val).val i.castSucc) x.2

@[simp] theorem boundaryTimeCoordinates_collar {m : ℕ} {kind : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold (m+1) kind M}
    (e : ModelChart (m+1) kind M) (x : CollarSource S) :
    boundaryTimeCoordinates e (x.1, x.2.val) = collarCoordinates e x := rfl

theorem boundaryTimeCoordinates_eq_face {m : ℕ} {kind : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold (m+1) kind M}
    {e : ModelChart (m+1) kind M}
    {b : ModelChart m .euclidean (intrinsicBoundary S)}
    (hb : IsFaceRestriction S e b) {x : intrinsicBoundary S × ℝ}
    (hx : x.1.val ∈ e.source) :
    boundaryTimeCoordinates e x = Fin.snoc (b x.1).val x.2 := by
  have hx' : x.1 ∈ b.source := by rw [hb.1]; exact hx
  unfold boundaryTimeCoordinates
  congr 1
  funext i
  exact (hb.2.2 x.1 hx' i).symm

/-- The time rescaling is smooth in every original ambient boundary chart
whose restriction is a chart of the boundary manifold. -/
theorem localCoordinateExtension_collar_timeScale {m : ℕ} {kind : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold (m+1) kind M}
    (B : SmoothManifold m .euclidean (intrinsicBoundary S))
    (ε : intrinsicBoundary S → ℝ)
    (hε : ScalarSmooth B.smoothStructure.val ε)
    (e : ModelChart (m+1) kind M)
    (b : ModelChart m .euclidean (intrinsicBoundary S))
    (hbB : b ∈ B.smoothStructure.val) (hb : IsFaceRestriction S e b)
    (x : CollarSource S) (hx : x.1.val ∈ e.source) :
    LocalCoordinateExtension (⊤ : ℕ∞) (collarCoordinates e)
      (fun y => boundaryTimeCoordinates e (y.1, ε y.1 * y.2.val)) x := by
  have hx' : x.1 ∈ b.source := by rw [hb.1]; exact hx
  obtain ⟨U, hU, hxU, E, hE, heq⟩ :=
    ((scalarContDiffAt_iff _ _ _ _).mp (hε x.1)).2 b hbB hx'
  have heq' := heq.comp_tendsto (continuous_fst.continuousAt :
    ContinuousAt (Prod.fst : CollarSource S → intrinsicBoundary S) x)
  have hs := localCoordinateExtension_timeScale (fun y : CollarSource S => (b y.1).val)
    (fun y => y.2.val) (fun y => ε y.1) x ⟨U, hU, hxU, E, hE, heq'⟩
  have hevent : ∀ᶠ y : CollarSource S in 𝓝 x, y.1.val ∈ e.source :=
    (continuous_subtype_val.comp continuous_fst).continuousAt.preimage_mem_nhds
      (e.open_source.mem_nhds hx)
  have hsource : (fun y : CollarSource S => Fin.snoc (b y.1).val y.2.val)
      =ᶠ[𝓝 x] collarCoordinates e := by
    filter_upwards [hevent] with y hy
    exact (collarCoordinates_eq_face hb hy).symm
  apply (localCoordinateExtension_congr_source hs hsource).congr
  filter_upwards [hevent] with y hy
  exact (boundaryTimeCoordinates_eq_face hb (x := (y.1, ε y.1 * y.2.val)) hy).symm

/-- Smooth division by the width on any subspace of the boundary-time product.
This supplies the normalization part of the inverse collar test. -/
theorem localCoordinateExtension_boundary_timeUnscale {m : ℕ} {kind : ModelKind}
    {M : Type u} [TopologicalSpace M] {S : SmoothManifold (m+1) kind M}
    (B : SmoothManifold m .euclidean (intrinsicBoundary S))
    (ε : intrinsicBoundary S → ℝ)
    (hε : ScalarSmooth B.smoothStructure.val ε)
    (e : ModelChart (m+1) kind M)
    (b : ModelChart m .euclidean (intrinsicBoundary S))
    (hbB : b ∈ B.smoothStructure.val) (hb : IsFaceRestriction S e b)
    (W : Set (intrinsicBoundary S × ℝ))
    (x : W) (hx : x.val.1.val ∈ e.source) (hne : ε x.val.1 ≠ 0) :
    LocalCoordinateExtension (⊤ : ℕ∞) (fun y : W => boundaryTimeCoordinates e y.val)
      (fun y => boundaryTimeCoordinates e (y.val.1, y.val.2 / ε y.val.1)) x := by
  have hx' : x.val.1 ∈ b.source := by rw [hb.1]; exact hx
  obtain ⟨U, hU, hxU, E, hE, heq⟩ :=
    ((scalarContDiffAt_iff _ _ _ _).mp (hε x.val.1)).2 b hbB hx'
  have heq' := heq.comp_tendsto ((continuous_fst.comp continuous_subtype_val).continuousAt :
    ContinuousAt (fun y : W => y.val.1) x)
  have hs := localCoordinateExtension_timeUnscale (fun y : W => (b y.val.1).val)
    (fun y => y.val.2) (fun y => ε y.val.1) x ⟨U, hU, hxU, E, hE, heq'⟩ hne
  have hevent : ∀ᶠ y : W in 𝓝 x, y.val.1.val ∈ e.source :=
    (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)).continuousAt.preimage_mem_nhds
      (e.open_source.mem_nhds hx)
  have hsource : (fun y : W => Fin.snoc (b y.val.1).val y.val.2)
      =ᶠ[𝓝 x] (fun y : W => boundaryTimeCoordinates e y.val) := by
    filter_upwards [hevent] with y hy
    exact (boundaryTimeCoordinates_eq_face hb (x := y.val) hy).symm
  apply (localCoordinateExtension_congr_source hs hsource).congr
  filter_upwards [hevent] with y hy
  exact (boundaryTimeCoordinates_eq_face hb
    (x := (y.val.1, y.val.2 / ε y.val.1)) hy).symm

/-- Assemble a collar from an open image of a smooth variable-width tube.
The coordinate hypotheses use every original ambient chart in each direction. -/
noncomputable def smoothCollarOfVariableWidthHomeomorph {m : ℕ} {kind : ModelKind}
    {M : Type u} [TopologicalSpace M] (S : SmoothManifold (m+1) kind M)
    (B : SmoothManifold m .euclidean (intrinsicBoundary S))
    (hB : ∀ e ∈ S.smoothStructure.val,
      Nonempty {p : intrinsicBoundary S // p.val ∈ e.source} →
      ∃ b ∈ B.smoothStructure.val, IsFaceRestriction S e b)
    (ε : intrinsicBoundary S → ℝ) (hε : ScalarSmooth B.smoothStructure.val ε)
    (hpos : ∀ q, 0 < ε q)
    (N : Set M) (hN : IsOpen N)
    (f : variableWidthSet ε ≃ₜ N)
    (hzero : ∀ q, (f ⟨(q, 0), le_rfl, hpos q⟩).val = q.val)
    (hf : ∀ (e d : ModelChart (m+1) kind M),
      e ∈ S.smoothStructure.val → d ∈ S.smoothStructure.val →
      ∀ z : variableWidthSet ε, z.val.1.val ∈ e.source →
        (f z).val ∈ d.source →
        LocalCoordinateExtension (⊤ : ℕ∞)
          (fun w : variableWidthSet ε => boundaryTimeCoordinates e w.val)
          (fun w => (d (f w).val).val) z)
    (hi : ∀ (d e : ModelChart (m+1) kind M),
      d ∈ S.smoothStructure.val → e ∈ S.smoothStructure.val →
      ∀ y : N, y.val ∈ d.source → (f.symm y).val.1.val ∈ e.source →
        LocalCoordinateExtension (⊤ : ℕ∞) (fun z : N => (d z.val).val)
          (fun z => boundaryTimeCoordinates e (f.symm z).val) y) : SmoothCollar S := by
  have hcont : Continuous ε := continuous_iff_continuousAt.mpr
    (fun q => ((scalarContDiffAt_iff _ _ _ _).mp (hε q)).1)
  let H := variableWidthHomeomorph ε hcont hpos
  refine {
    neighborhood := N
    isOpen_neighborhood := hN
    boundary_subset := ?_
    toHomeomorph := H.trans f
    zero_section := ?_
    smooth_forward := ?_
    smooth_inverse := ?_
  }
  · intro q hq
    simpa only [hzero] using
      (f ⟨(⟨q, hq⟩, 0), le_rfl, hpos ⟨q, hq⟩⟩).property
  · intro q
    change (f (H (q, timeZero))).val = q.val
    have hz : H (q, timeZero) = ⟨(q, 0), le_rfl, hpos q⟩ := by
      apply Subtype.ext
      exact variableWidthHomeomorph_zero ε hcont hpos q
    rw [hz]
    exact hzero q
  · intro e d he hd x hx hdx
    obtain ⟨b, hbB, hb⟩ := hB e he ⟨⟨x.1, hx⟩⟩
    have hscale := localCoordinateExtension_collar_timeScale B ε hε e b hbB hb x hx
    have hf' := LocalCoordinateExtension.precomp (hf e d he hd (H x) hx hdx)
      H.continuous.continuousAt rfl
    exact LocalCoordinateExtension.comp hf' hscale
  · intro d e hd he y hdy hey
    have hey' : (f.symm y).val.1.val ∈ e.source := hey
    obtain ⟨b, hbB, hb⟩ := hB e he ⟨⟨(f.symm y).val.1, hey'⟩⟩
    have hunscale := localCoordinateExtension_boundary_timeUnscale B ε hε e b hbB hb
      (variableWidthSet ε) (f.symm y) hey' (hpos _).ne'
    have hi' := LocalCoordinateExtension.precomp hunscale f.symm.continuous.continuousAt rfl
    exact LocalCoordinateExtension.comp hi' (hi d e hd he y hdy hey')


/-- An intrinsic integral curve on a one-sided time interval. Values of the
representative outside the interval have no mathematical role. -/
def IsOneSidedIntegralCurveOn {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    (X : SmoothField B) (b : ℝ) (γ : ℝ → M) : Prop :=
  ContinuousOn γ (Ico 0 b) ∧ ∀ t ∈ Ico 0 b,
    ∀ (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
      (ht : γ t ∈ e.source),
      HasDerivWithinAt (fun s => (e (γ s)).val)
        (B.fiberCoordinates.equiv e he (γ t) ht (X.val (γ t))) (Ico 0 b) t

theorem oneSided_integral_mono {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} {B : TangentBundleStructure S}
    {X : SmoothField B} {b c : ℝ} {γ : ℝ → M}
    (hγ : IsOneSidedIntegralCurveOn B X b γ) (hcb : c ≤ b) :
    IsOneSidedIntegralCurveOn B X c γ := by
  have hsub : Ico (0 : ℝ) c ⊆ Ico 0 b := Ico_subset_Ico_right hcb
  exact ⟨hγ.1.mono hsub, fun t ht e he hs => (hγ.2 t (hsub ht) e he hs).mono hsub⟩

/-- Ordinary Euclidean ODE uniqueness applies in a common chart even at time
zero: use right derivatives there, and two-sided derivatives at positive times.
No boundary-preserving negative-time trajectory is assumed. -/
theorem oneSided_local_unique {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (B : TangentBundleStructure S)
    (X : SmoothField B) {b : ℝ} (hb : 0 < b) (γ η : ℝ → M)
    (hγ : IsOneSidedIntegralCurveOn B X b γ)
    (hη : IsOneSidedIntegralCurveOn B X b η)
    (s : ℝ) (hs : s ∈ Ico 0 b) (hmeet : γ s = η s) :
    γ =ᶠ[𝓝[Ico 0 b] s] η := by
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 (γ s)
  obtain ⟨U, hU, hpU, F, hF, hcoeff⟩ :=
    VectorFields.field_local_coordinates S B X (γ s) e he hp
  obtain ⟨K, T, hT, hLip⟩ :=
    ((hF.contDiffAt (hU.mem_nhds hpU)).of_le (by simp)).exists_lipschitzOnWith
  let V : Set M := {q | ∃ hq : q ∈ e.source,
    F (e q).val = B.fiberCoordinates.equiv e he q hq (X.val q) ∧ (e q).val ∈ T}
  have hV : V ∈ 𝓝 (γ s) := by
    filter_upwards [hcoeff,
      (continuous_subtype_val.continuousAt.comp (e.continuousAt hp)).eventually hT]
      with q hq hqT
    exact ⟨hq.1, hq.2, hqT⟩
  have hVη : V ∈ 𝓝 (η s) := hmeet ▸ hV
  have hnear : ∀ᶠ t in 𝓝[Ico 0 b] s,
      t ∈ Ico 0 b ∧ γ t ∈ V ∧ η t ∈ V := by
    filter_upwards [self_mem_nhdsWithin, (hγ.1 s hs).eventually hV,
      (hη.1 s hs).eventually hVη] with t ht hγt hηt
    exact ⟨ht, hγt, hηt⟩
  have hdγ (t : ℝ) (ht : t ∈ Ico 0 b) (hγt : γ t ∈ V) :
      HasDerivWithinAt (fun u => (e (γ u)).val) (F (e (γ t)).val) (Ico 0 b) t := by
    obtain ⟨hq, hqF, _⟩ := hγt
    rw [hqF]
    exact hγ.2 t ht e he hq
  have hdη (t : ℝ) (ht : t ∈ Ico 0 b) (hηt : η t ∈ V) :
      HasDerivWithinAt (fun u => (e (η u)).val) (F (e (η t)).val) (Ico 0 b) t := by
    obtain ⟨hq, hqF, _⟩ := hηt
    rw [hqF]
    exact hη.2 t ht e he hq
  have heq : (e (γ s)).val = (e (η s)).val := congrArg (fun q => (e q).val) hmeet
  by_cases hs0 : s = 0
  · subst s
    rw [nhdsWithin_Ico_eq_nhdsGE hb] at hnear ⊢
    obtain ⟨r, hr, hsub⟩ := mem_nhdsGE_iff_exists_Icc_subset.mp hnear
    have hcontγ : ContinuousOn (fun u => (e (γ u)).val) (Icc 0 r) :=
      (continuous_subtype_val.comp_continuousOn e.continuousOn).comp
        (hγ.1.mono (fun t ht => (hsub ht).1))
        (fun t ht => (hsub ht).2.1.choose)
    have hcontη : ContinuousOn (fun u => (e (η u)).val) (Icc 0 r) :=
      (continuous_subtype_val.comp_continuousOn e.continuousOn).comp
        (hη.1.mono (fun t ht => (hsub ht).1))
        (fun t ht => (hsub ht).2.2.choose)
    have hequal := ODE_solution_unique_of_mem_Icc_right
      (v := fun _ => F) (s := fun _ => T) (fun _ _ => hLip)
      hcontγ
      (fun t ht => (hdγ t (hsub (Ico_subset_Icc_self ht)).1
        (hsub (Ico_subset_Icc_self ht)).2.1).mono_of_mem_nhdsWithin
          (mem_of_superset (Ico_mem_nhdsGE (hsub (Ico_subset_Icc_self ht)).1.2)
            (Ico_subset_Ico_left ht.1)))
      (fun t ht => (hsub (Ico_subset_Icc_self ht)).2.1.choose_spec.2)
      hcontη
      (fun t ht => (hdη t (hsub (Ico_subset_Icc_self ht)).1
        (hsub (Ico_subset_Icc_self ht)).2.2).mono_of_mem_nhdsWithin
          (mem_of_superset (Ico_mem_nhdsGE (hsub (Ico_subset_Icc_self ht)).1.2)
            (Ico_subset_Ico_left ht.1)))
      (fun t ht => (hsub (Ico_subset_Icc_self ht)).2.2.choose_spec.2) heq
    filter_upwards [Icc_mem_nhdsGE hr] with t ht
    apply e.injOn (hsub ht).2.1.choose (hsub ht).2.2.choose
    exact Subtype.ext (hequal ht)
  · have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
    have hmem : Ico (0 : ℝ) b ∈ 𝓝 s :=
      mem_of_superset (Ioo_mem_nhds hspos hs.2) Ioo_subset_Ico_self
    rw [nhdsWithin_eq_nhds.mpr hmem] at hnear
    have hnear' : ∀ᶠ t in 𝓝 s, 0 < t ∧ (t ∈ Ico 0 b ∧ γ t ∈ V ∧ η t ∈ V) := by
      filter_upwards [isOpen_Ioi.mem_nhds hspos, hnear] with t ht hq
      exact ⟨ht, hq⟩
    obtain ⟨l, r, hls, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hnear'
    have hequal := ODE_solution_unique_of_mem_Ioo
      (v := fun _ => F) (s := fun _ => T) (fun _ _ => hLip) hls
      (fun t ht => ⟨(hdγ t (hsub ht).2.1 (hsub ht).2.2.1).hasDerivAt
          (mem_of_superset (Ioo_mem_nhds (hsub ht).1 (hsub ht).2.1.2)
            Ioo_subset_Ico_self), (hsub ht).2.2.1.choose_spec.2⟩)
      (fun t ht => ⟨(hdη t (hsub ht).2.1 (hsub ht).2.2.2).hasDerivAt
          (mem_of_superset (Ioo_mem_nhds (hsub ht).1 (hsub ht).2.1.2)
            Ioo_subset_Ico_self), (hsub ht).2.2.2.choose_spec.2⟩) heq
    apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
    filter_upwards [isOpen_Ioo.mem_nhds hls] with t ht
    apply e.injOn (hsub ht).2.2.1.choose (hsub ht).2.2.2.choose
    exact Subtype.ext (hequal ht)

/-- One-sided integral curves with the same initial boundary value coincide
on their entire common nonnegative time interval. -/
theorem oneSided_overlap_unique {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (B : TangentBundleStructure S)
    (X : SmoothField B) {b c : ℝ} (hb : 0 < b) (hc : 0 < c) (γ η : ℝ → M)
    (hγ : IsOneSidedIntegralCurveOn B X b γ)
    (hη : IsOneSidedIntegralCurveOn B X c η) (hmeet : γ 0 = η 0) :
    EqOn γ η (Ico 0 (min b c)) := by
  letI : T2Space M := S.topologicalManifold.hausdorff
  let d := min b c
  have hd : 0 < d := lt_min hb hc
  have hγd := oneSided_integral_mono hγ (min_le_left b c)
  have hηd := oneSided_integral_mono hη (min_le_right b c)
  let A := Ico (0 : ℝ) d
  letI : PreconnectedSpace A := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ico
  have hclosed : IsClosed {t : A | γ t = η t} :=
    isClosed_eq hγd.1.domRestrict hηd.1.domRestrict
  have hopen : IsOpen {t : A | γ t = η t} := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    exact (oneSided_local_unique S B X hd γ η hγd hηd t t.property ht).comp_tendsto
      (by
        exact le_of_eq (map_nhds_subtype_val t))
  have hall : {t : A | γ t = η t} = univ :=
    (show IsClopen {t : A | γ t = η t} from ⟨hclosed, hopen⟩).eq_univ
      ⟨⟨0, le_rfl, hd⟩, hmeet⟩
  intro t ht
  exact (show (⟨t, ht⟩ : A) ∈ {t : A | γ t = η t} from hall ▸ mem_univ _)

/-- The constructed boundary trajectories give intrinsic one-sided integral
curves in the all-chart interface used for overlap uniqueness. -/
theorem exists_oneSided_integral_curve {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n + 1) .halfSpace M) (B : TangentBundleStructure S)
    (X : SmoothField B) (p : intrinsicBoundary S)
    (hpos : ∀ (e : ModelChart (n + 1) .halfSpace M)
      (he : e ∈ S.smoothStructure.val) (hp : p.val ∈ e.source),
      0 < B.fiberCoordinates.equiv e he p.val hp (X.val p.val) (Fin.last n)) :
    ∃ (b : ℝ), 0 < b ∧ ∃ γ : ℝ → M,
      γ 0 = p.val ∧ IsOneSidedIntegralCurveOn B X b γ := by
  classical
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p.val
  obtain ⟨b, hb, γ, hγc, hγ0, hγsource, _, x, hx, hderiv⟩ :=
    local_inward_trajectory S B X p e he hp (hpos e he hp)
  let Γ : ℝ → M := fun t => if ht : t ∈ Ico 0 b then γ ⟨t, ht⟩ else p.val
  have hΓ (t : ℝ) (ht : t ∈ Ico 0 b) : Γ t = γ ⟨t, ht⟩ := dite_eq_left ht
  have hΓc : ContinuousOn Γ (Ico 0 b) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    convert hγc using 1
    funext t
    exact hΓ t.val t.property
  have hΓsource : MapsTo Γ (Ico 0 b) e.source := by
    intro t ht
    rw [hΓ t ht]
    exact hγsource ⟨t, ht⟩
  refine ⟨b, hb, Γ, ?_, hΓc, ?_⟩
  · rw [hΓ 0 ⟨le_rfl, hb⟩]
    exact hγ0
  · apply oneSided_derivative_of_chart B X hΓc e he hΓsource x
    · intro t ht
      rw [hΓ t ht]
      exact hx ⟨t, ht⟩
    · intro t ht
      obtain ⟨hq, hd⟩ := hderiv ⟨t, ht⟩
      have hvel := congrArg
        (fun q => TangentBundle.chartFiber B e he ⟨q, X.val q⟩) (hΓ t ht)
      rw [TangentBundle.chartFiber_eq S B e he _ (hΓsource ht),
        TangentBundle.chartFiber_eq S B e he _ hq] at hvel
      exact hvel.symm ▸ hd

/-- Around every boundary initial point there is a genuine jointly smooth
one-sided family, with a common local width for nearby boundary initial states.
The total curves are only representatives; all assertions use their Ico domain. -/
theorem local_boundary_family {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n + 1) .halfSpace M) (B : TangentBundleStructure S)
    (X : SmoothField B) (p : intrinsicBoundary S)
    (e : ModelChart (n + 1) .halfSpace M) (he : e ∈ S.smoothStructure.val)
    (hp : p.val ∈ e.source)
    (hpos : 0 < B.fiberCoordinates.equiv e he p.val hp (X.val p.val) (Fin.last n)) :
    ∃ (b : ℝ) (O : Set (intrinsicBoundary S)) (γ : intrinsicBoundary S → ℝ → M),
      0 < b ∧ IsOpen O ∧ p ∈ O ∧
      (∀ q ∈ O, q.val ∈ e.source) ∧
      ContinuousOn (fun x : intrinsicBoundary S × ℝ => γ x.1 x.2) (O ×ˢ Ico 0 b) ∧
      (∀ q ∈ O, γ q 0 = q.val) ∧
      (∀ q ∈ O, MapsTo (γ q) (Ico 0 b) e.source) ∧
      (∀ q ∈ O, ContinuousOn (γ q) (Ico 0 b) ∧
        ∀ t ∈ Ico 0 b, ∀ (d : ModelChart (n + 1) .halfSpace M)
          (hd : d ∈ S.smoothStructure.val) (ht : γ q t ∈ d.source),
          HasDerivWithinAt (fun s => (d (γ q s)).val)
            (B.fiberCoordinates.equiv d hd (γ q t) ht (X.val (γ q t))) (Ico 0 b) t) ∧
      (∀ w : ↥(O ×ˢ Ico (0 : ℝ) b),
        ∀ (d : ModelChart (n + 1) .halfSpace M) (hd : d ∈ S.smoothStructure.val)
          (hwd : γ w.val.1 w.val.2 ∈ d.source),
          LocalCoordinateExtension (⊤ : ℕ∞)
            (fun z : ↥(O ×ˢ Ico (0 : ℝ) b) => boundaryTimeCoordinates e z.val)
            (fun z => (d (γ z.val.1 z.val.2)).val) w) := by
  classical
  obtain ⟨U, F, hU, hpU, hF, hFpos, hcoeff⟩ :=
    inward_coefficient_extension S B X p.val e he hp hpos
  obtain ⟨b, V, Φ, hb, hV, hpV, hVU, hΦ, hΦzero, hΦder, hsign⟩ :=
    local_inward_coordinate_flow hU hF hFpos hpU
  let O : Set (intrinsicBoundary S) :=
    {q | q.val ∈ e.source ∧ (e q.val).val ∈ V}
  have hOc : IsOpen O := by
    have hpre := e.continuousOn.isOpen_inter_preimage e.open_source
      (hV.preimage continuous_subtype_val)
    exact hpre.preimage continuous_subtype_val
  have hpO : p ∈ O := ⟨hp, hpV⟩
  have hqface (q : intrinsicBoundary S) (hq : q ∈ O) :
      (e q.val).val (Fin.last n) = 0 :=
    (intrinsicBoundary_iff_chart S e he q.val hq.1).mp q.property
  let W : Set (intrinsicBoundary S × ℝ) := O ×ˢ Ico 0 b
  have htime {t : ℝ} (ht : t ∈ Ico 0 b) : t ∈ Ioo (-b) b :=
    ⟨(neg_neg_of_pos hb).trans_le ht.1, ht.2⟩
  have hhalf (w : W) : Φ (w.val.2, (e w.val.1.val).val) ∈ halfSpaceSet (n + 1) :=
    ((hsign _ w.property.1.2 (hqface _ w.property.1) _ (htime w.property.2)).1).mpr
      w.property.2.1
  let z : W → ModelSpace (n + 1) .halfSpace :=
    fun w => ⟨Φ (w.val.2, (e w.val.1.val).val), hhalf w⟩
  have hztarget (w : W) : z w ∈ e.target :=
    (hcoeff _ (hΦder _ w.property.1.2 _ (htime w.property.2)).1 (hhalf w)).1
  have hinitc : Continuous (fun w : W => (e w.val.1.val).val) :=
    continuous_subtype_val.comp
      (e.continuousOn.comp_continuous
        (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val))
        (fun w => w.property.1.1))
  have hzc : Continuous z := by
    apply Continuous.subtype_mk
    exact hΦ.continuousOn.comp_continuous
      ((continuous_snd.comp continuous_subtype_val).prodMk hinitc)
      (fun w => ⟨htime w.property.2, w.property.1.2⟩)
  let g : W → M := fun w => e.symm (z w)
  have hgc : Continuous g := e.symm.continuousOn.comp_continuous hzc hztarget
  let γ : intrinsicBoundary S → ℝ → M := fun q t =>
    if h : (q,t) ∈ W then g ⟨(q,t), h⟩ else q.val
  have hγeq (w : W) : γ w.val.1 w.val.2 = g w := by
    simp only [γ, dite_eq_left w.property]
  have hγc : ContinuousOn (fun x : intrinsicBoundary S × ℝ => γ x.1 x.2) W := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact hgc.congr (fun w => (hγeq w).symm)
  have hγsource (q : intrinsicBoundary S) (hq : q ∈ O) (t : ℝ) (ht : t ∈ Ico 0 b) :
      γ q t ∈ e.source := by
    rw [hγeq ⟨(q,t), hq, ht⟩]
    exact e.map_target (hztarget _)
  have hγcoords (q : intrinsicBoundary S) (hq : q ∈ O) (t : ℝ) (ht : t ∈ Ico 0 b) :
      (e (γ q t)).val = Φ (t,(e q.val).val) := by
    rw [hγeq ⟨(q,t), hq, ht⟩]
    exact congrArg Subtype.val (e.right_inv (hztarget _))
  have hγqc (q : intrinsicBoundary S) (hq : q ∈ O) : ContinuousOn (γ q) (Ico 0 b) :=
    hγc.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ ht => ⟨hq, ht⟩)
  refine ⟨b, O, γ, hb, hOc, hpO, (fun _ hq => hq.1), hγc, ?_, hγsource, ?_, ?_⟩
  · intro q hq
    rw [hγeq ⟨(q,0), hq, le_rfl, hb⟩]
    change e.symm (z ⟨(q,0), hq, le_rfl, hb⟩) = q.val
    have hz0 : z ⟨(q,0), hq, le_rfl, hb⟩ = e q.val :=
      Subtype.ext (hΦzero _ hq.2)
    rw [hz0, e.left_inv hq.1]
  · intro q hq
    refine ⟨hγqc q hq, ?_⟩
    apply oneSided_derivative_of_chart B X (hγqc q hq) e he (hγsource q hq)
      (fun t => Φ (t,(e q.val).val)) (fun t ht => (hγcoords q hq t ht).symm)
    intro t ht
    have hder := (hΦder _ hq.2 t (htime ht)).2
    have hco := (hcoeff _ (hΦder _ hq.2 t (htime ht)).1
      (hhalf ⟨(q,t), hq, ht⟩)).2
    have hback : e.symm (z ⟨(q,t), hq, ht⟩) = γ q t := (hγeq _).symm
    change F (Φ (t,(e q.val).val)) = TangentBundle.chartFiber B e he
      ⟨e.symm (z ⟨(q,t), hq, ht⟩), X.val (e.symm (z ⟨(q,t), hq, ht⟩))⟩ at hco
    rw [hback, TangentBundle.chartFiber_eq S B e he _ (hγsource q hq t ht)] at hco
    exact hco ▸ hder
  · intro w d hd hwd
    have htrans := LocalCoordinateExtension.precomp
      (chartContDiffAt_of_compatible (S.smoothStructure.property.1.2 e he d hd)
        (hγsource _ w.property.1 _ w.property.2) hwd)
      hgc.continuousAt (hγeq w).symm
    have hgg : g = (fun w : W => γ w.val.1 w.val.2) := funext (fun w => (hγeq w).symm)
    rw [hgg] at htrans
    apply LocalCoordinateExtension.comp htrans
    let c : Euclidean (n + 1) → ℝ × Euclidean (n + 1) :=
      fun v => (v (Fin.last n), Fin.snoc (Fin.init v) 0)
    have hc : ContDiff ℝ (⊤ : ℕ∞) c :=
      (ContinuousLinearMap.proj (Fin.last n) : Euclidean (n + 1) →L[ℝ] ℝ).contDiff.prodMk
        (faceProjection (n := n)).contDiff
    have hfaceeq (q : intrinsicBoundary S) (hq : q ∈ O) :
        Fin.snoc (fun i : Fin n => (e q.val).val i.castSucc) (0 : ℝ) = (e q.val).val := by
      ext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [hqface q hq]
      · simp
    have hcformula (v : W) : c (boundaryTimeCoordinates e v.val) =
        (v.val.2, (e v.val.1.val).val) := by
      apply Prod.ext
      · simp [c, boundaryTimeCoordinates]
      · simpa [c, boundaryTimeCoordinates] using hfaceeq _ v.property.1
    refine ⟨c ⁻¹' (Ioo (-b) b ×ˢ V), (isOpen_Ioo.prod hV).preimage hc.continuous,
      ?_, Φ ∘ c, hΦ.comp hc.contDiffOn (fun _ hv => hv), ?_⟩
    · change c (boundaryTimeCoordinates e w.val) ∈ Ioo (-b) b ×ˢ V
      rw [hcformula]
      exact ⟨htime w.property.2, w.property.1.2⟩
    · apply Eventually.of_forall
      intro v
      change Φ (c (boundaryTimeCoordinates e v.val)) = (e (γ v.val.1 v.val.2)).val
      rw [hcformula]
      exact (hγcoords _ v.property.1 _ v.property.2).symm


/-- Boundary-product coordinates from any two original ambient charts have
smooth transition germs, with the time coordinate unchanged. -/
theorem boundaryTimeCoordinates_transition {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold (n + 1) a M)
    (e d : ModelChart (n + 1) a M) (he : e ∈ S.smoothStructure.val)
    (hd : d ∈ S.smoothStructure.val) (x : intrinsicBoundary S × ℝ)
    (hxe : x.1.val ∈ e.source) (hxd : x.1.val ∈ d.source) :
    LocalCoordinateExtension (⊤ : ℕ∞) (boundaryTimeCoordinates e)
      (boundaryTimeCoordinates d) x := by
  obtain ⟨U, hU, hxU, F, hF, hrep⟩ :=
    chartContDiffAt_of_compatible (S.smoothStructure.property.1.2 e he d hd) hxe hxd
  have hef : (e x.1.val).val (Fin.last n) = 0 := by
    have h := (intrinsicBoundary_iff_chart S e he x.1.val hxe).mp x.1.property
    cases a with
    | halfSpace => exact h
    | euclidean => exact False.elim h
  have hproj : faceProjection (boundaryTimeCoordinates e x) = (e x.1.val).val := by
    ext i
    cases i using Fin.lastCases <;> simp [faceProjection, boundaryTimeCoordinates, Fin.init, hef]
  let G : Euclidean (n + 1) → Euclidean (n + 1) := fun z =>
    faceProjection (F (faceProjection z)) + z (Fin.last n) • Pi.single (Fin.last n) 1
  have hG : ContDiffOn ℝ (⊤ : ℕ∞) G (faceProjection ⁻¹' U) :=
    ((faceProjection (n := n)).contDiff.contDiffOn.comp
      (hF.comp (faceProjection (n := n)).contDiff.contDiffOn (fun _ hz => hz))
      (fun _ _ => mem_univ _)).add
      (((ContinuousLinearMap.proj (Fin.last n) : Euclidean (n + 1) →L[ℝ] ℝ).contDiff.contDiffOn).smul
        contDiffOn_const)
  refine ⟨faceProjection ⁻¹' U, hU.preimage (faceProjection (n := n)).continuous,
    ?_, G, hG, ?_⟩
  · change faceProjection (boundaryTimeCoordinates e x) ∈ U
    rwa [hproj]
  · have hnear := hrep.comp_tendsto
      (continuous_subtype_val.comp continuous_fst).continuousAt
    have hnearE : ∀ᶠ y : intrinsicBoundary S × ℝ in 𝓝 x, y.1.val ∈ e.source :=
      (continuous_subtype_val.comp continuous_fst).continuousAt.preimage_mem_nhds
        (e.open_source.mem_nhds hxe)
    filter_upwards [hnear, hnearE] with y hy hye
    have hey : (e y.1.val).val (Fin.last n) = 0 := by
      have h := (intrinsicBoundary_iff_chart S e he y.1.val hye).mp y.1.property
      cases a with
      | halfSpace => exact h
      | euclidean => exact False.elim h
    have hprojY : faceProjection (boundaryTimeCoordinates e y) = (e y.1.val).val := by
      ext i
      cases i using Fin.lastCases <;> simp [faceProjection, boundaryTimeCoordinates, Fin.init, hey]
    change G (boundaryTimeCoordinates e y) = boundaryTimeCoordinates d y
    unfold G
    rw [hprojY]
    change F (e y.1.val).val = (d y.1.val).val at hy
    rw [hy]
    ext i
    cases i using Fin.lastCases <;> simp [faceProjection, boundaryTimeCoordinates, Fin.init]


/-- Shrinking a relatively open boundary flowout gives a positive smooth tube
which embeds onto an open image. This handles noncompact zero sections without
a common constant time width. -/
theorem exists_tube_homeomorph {n m : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M)
    (R : SmoothManifold m .euclidean (intrinsicBoundary S))
    (W : Set (intrinsicBoundary S × ℝ))
    (hW : ∀ q, W ∈ 𝓝[univ ×ˢ Ici (0 : ℝ)] (q, 0))
    (hWnonneg : W ⊆ univ ×ˢ Ici (0 : ℝ))
    (F : W → M) (hF : Continuous F) (hFopen : IsOpenMap F)
    (hzero : ∀ q, ∀ hq : (q, 0) ∈ W, F ⟨(q, 0), hq⟩ = q.val)
    (hlocal : ∀ z ∈ zeroTimeSection W,
      ∃ V : Set W, IsOpen V ∧ z ∈ V ∧ InjOn F V) :
    ∃ (ε : intrinsicBoundary S → ℝ), ScalarSmooth R.smoothStructure.val ε ∧
      (∀ q, 0 < ε q) ∧ ∃ (hεW : variableWidthSet ε ⊆ W)
      (N : Set M) (hN : IsOpen N) (f : variableWidthSet ε ≃ₜ N),
      ∀ x, (f x).val = F (Set.inclusion hεW x) := by
  have hWzero (q : intrinsicBoundary S) : (q, (0 : ℝ)) ∈ W := by
    have hz : (q, (0 : ℝ)) ∈ ((univ : Set (intrinsicBoundary S)) ×ˢ Ici (0 : ℝ)) :=
      ⟨mem_univ _, show (0 : ℝ) ≤ 0 from le_rfl⟩
    exact mem_of_mem_nhdsWithin hz (hW q)
  obtain ⟨V, hV, hVzero, hinj⟩ := exists_injective_boundary_flowout S W hWzero F hF
    (fun q => hzero q _) hlocal
  obtain ⟨O, hO, hOV⟩ := isOpen_induced_iff.mp hV
  let J := W ∩ O
  have hJ (q : intrinsicBoundary S) : J ∈ 𝓝[univ ×ˢ Ici (0 : ℝ)] (q, 0) := by
    apply inter_mem (hW q)
    apply mem_nhdsWithin_of_mem_nhds
    apply hO.mem_nhds
    have hz : (⟨(q, 0), hWzero q⟩ : W) ∈ V := hVzero rfl
    rwa [← hOV] at hz
  obtain ⟨ε, hε, hpos, htube⟩ := exists_smooth_width R J hJ
  have hεW : variableWidthSet ε ⊆ W := fun x hx => (htube hx).1
  have hcont : Continuous ε := continuous_iff_continuousAt.mpr
    (fun q => ((scalarContDiffAt_iff _ _ _ _).mp (hε q)).1)
  have hopen : IsOpen (Subtype.val ⁻¹' variableWidthSet ε : Set W) := by
    have heq : (Subtype.val ⁻¹' variableWidthSet ε : Set W) =
        {z : W | z.val.2 < ε z.val.1} := by
      ext z
      exact and_iff_right (hWnonneg z.property).2
    rw [heq]
    exact isOpen_lt (continuous_snd.comp continuous_subtype_val)
      (hcont.comp (continuous_fst.comp continuous_subtype_val))
  have hIncl : Topology.IsOpenEmbedding (Set.inclusion hεW) :=
    Topology.IsOpenEmbedding.inclusion hεW hopen
  let G : variableWidthSet ε → M := F ∘ Set.inclusion hεW
  have hG : Continuous G := hF.comp hIncl.continuous
  have hGo : IsOpenMap G := hFopen.comp hIncl.isOpenMap
  have hGinj : Function.Injective G := by
    intro x y hxy
    apply Subtype.ext
    have hxV : Set.inclusion hεW x ∈ V := by rw [← hOV]; exact (htube x.property).2
    have hyV : Set.inclusion hεW y ∈ V := by rw [← hOV]; exact (htube y.property).2
    exact congrArg (fun z : W => z.val) (hinj hxV hyV hxy)
  let N := Set.range G
  have hN : IsOpen N := by simpa only [image_univ] using hGo univ isOpen_univ
  let e : variableWidthSet ε ≃ N := Equiv.ofInjective G hGinj
  let f : variableWidthSet ε ≃ₜ N := e.toHomeomorphOfContinuousOpen
    (hG.subtype_mk _) (hGo.subtype_mk _)
  exact ⟨ε, hε, hpos, hεW, N, hN, f, fun _ => rfl⟩

/-- Glue maps defined on open source domains, with their original source topology. -/
noncomputable def glueOpenMaps {X : Type u} {Y : Type v} {ι : Type w}
    [TopologicalSpace X] [TopologicalSpace Y]
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (f : ι → X → Y) (hf : ∀ i, ContinuousOn (f i) (U i))
    (hcompat : ∀ i j, EqOn (f i) (f j) (U i ∩ U j)) : C(⋃ i, U i, Y) := by
  let V : ι → Set (⋃ i, U i) := fun i => Subtype.val ⁻¹' U i
  let g : ∀ i, C(V i, Y) := fun i => ⟨fun z => f i z.val.val,
    (hf i).comp_continuous ((continuous_subtype_val.comp continuous_subtype_val))
      (fun z => z.property)⟩
  apply ContinuousMap.liftCover V g
  · intro i j x hxi hxj
    exact hcompat i j ⟨hxi, hxj⟩
  · intro x
    obtain ⟨i, hi⟩ := mem_iUnion.mp x.property
    exact ⟨i, ((hU i).preimage continuous_subtype_val).mem_nhds hi⟩

/-- The glued map agrees with each original map on its full source domain. -/
theorem glueOpenMaps_apply {X : Type u} {Y : Type v} {ι : Type w}
    [TopologicalSpace X] [TopologicalSpace Y]
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (f : ι → X → Y) (hf : ∀ i, ContinuousOn (f i) (U i))
    (hcompat : ∀ i j, EqOn (f i) (f j) (U i ∩ U j))
    (i : ι) (x : ⋃ j, U j) (hx : x.val ∈ U i) :
    glueOpenMaps U hU f hf hcompat x = f i x.val := by
  unfold glueOpenMaps
  exact ContinuousMap.liftCover_coe (x := ⟨x, hx⟩)

/-- The equality is a germ equality, suitable for the local-coordinate calculus. -/
theorem glueOpenMaps_eventuallyEq {X : Type u} {Y : Type v} {ι : Type w}
    [TopologicalSpace X] [TopologicalSpace Y]
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (f : ι → X → Y) (hf : ∀ i, ContinuousOn (f i) (U i))
    (hcompat : ∀ i j, EqOn (f i) (f j) (U i ∩ U j))
    (i : ι) (x : ⋃ j, U j) (hx : x.val ∈ U i) :
    (fun z => glueOpenMaps U hU f hf hcompat z) =ᶠ[𝓝 x]
      (fun z => f i z.val) := by
  filter_upwards [((hU i).preimage continuous_subtype_val).mem_nhds hx] with z hz
  exact glueOpenMaps_apply U hU f hf hcompat i z hz

/-- Openness glues along source domains; injectivity is not needed here. -/
theorem glueOpenMaps_isOpenMap {X : Type u} {Y : Type v} {ι : Type w}
    [TopologicalSpace X] [TopologicalSpace Y]
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (f : ι → X → Y) (hf : ∀ i, ContinuousOn (f i) (U i))
    (hcompat : ∀ i j, EqOn (f i) (f j) (U i ∩ U j))
    (hopen : ∀ i, IsOpenMap (fun z : U i => f i z.val)) :
    IsOpenMap (glueOpenMaps U hU f hf hcompat) := by
  intro V hV
  have heq : glueOpenMaps U hU f hf hcompat '' V =
      ⋃ i, (fun z : U i => f i z.val) ''
        (fun z : U i => (⟨z.val, mem_iUnion.mpr ⟨i, z.property⟩⟩ : ⋃ j, U j)) ⁻¹' V := by
    apply Subset.antisymm
    · rintro y ⟨z, hz, rfl⟩
      obtain ⟨i, hi⟩ := mem_iUnion.mp z.property
      apply mem_iUnion.mpr
      refine ⟨i, ⟨⟨z.val, hi⟩, hz, ?_⟩⟩
      exact (glueOpenMaps_apply U hU f hf hcompat i z hi).symm
    · intro y hy
      obtain ⟨i, z, hz, hzy⟩ := mem_iUnion.mp hy
      refine ⟨⟨z.val, mem_iUnion.mpr ⟨i, z.property⟩⟩, hz, ?_⟩
      exact (glueOpenMaps_apply U hU f hf hcompat i _ z.property).trans hzy
  rw [heq]
  apply isOpen_iUnion
  intro i
  apply hopen i
  exact hV.preimage (continuous_subtype_val.subtype_mk _)

/-- Once the global injective shrinking has been performed, the glued map is
an open embedding, and hence a homeomorphism to its open range. -/
theorem glueOpenMaps_isOpenEmbedding {X : Type u} {Y : Type v} {ι : Type w}
    [TopologicalSpace X] [TopologicalSpace Y]
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (f : ι → X → Y) (hf : ∀ i, ContinuousOn (f i) (U i))
    (hcompat : ∀ i j, EqOn (f i) (f j) (U i ∩ U j))
    (hopen : ∀ i, IsOpenMap (fun z : U i => f i z.val))
    (hinj : Function.Injective (glueOpenMaps U hU f hf hcompat)) :
    Topology.IsOpenEmbedding (glueOpenMaps U hU f hf hcompat) :=
  .of_continuous_injective_isOpenMap (glueOpenMaps U hU f hf hcompat).continuous
    hinj (glueOpenMaps_isOpenMap U hU f hf hcompat hopen)

/-- A homeomorphism agreeing with a local partial homeomorphism has the same
inverse germ. Smooth local inverses may therefore be transferred to the glued
inverse by `LocalCoordinateExtension.congr`. -/
theorem homeomorph_inverse_eventuallyEq_of_local_agreement
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {W : Set X} {N : Set Y} (G : W ≃ₜ N) (p : OpenPartialHomeomorph X Y)
    (hagree : ∀ z : W, z.val ∈ p.source → (G z).val = p z.val)
    (y : N) (hy : (G.symm y).val ∈ p.source) :
    (fun z => (G.symm z).val) =ᶠ[𝓝 y] (fun z => p.symm z.val) := by
  have hevent : ∀ᶠ z : N in 𝓝 y, (G.symm z).val ∈ p.source :=
    (continuous_subtype_val.comp G.symm.continuous).continuousAt.preimage_mem_nhds
      (p.open_source.mem_nhds hy)
  filter_upwards [hevent] with z hz
  calc
    (G.symm z).val = p.symm (p (G.symm z).val) := (p.left_inv hz).symm
    _ = p.symm (G (G.symm z)).val := congrArg p.symm (hagree (G.symm z) hz).symm
    _ = p.symm z.val := by rw [G.apply_symm_apply]

/-- Glue compatible local flowouts given as partial homeomorphisms. Their
union need not itself be injective. -/
noncomputable def glueOpenPartialHomeomorphs {X : Type u} {Y : Type v} {ι : Type w}
    [TopologicalSpace X] [TopologicalSpace Y]
    (p : ι → OpenPartialHomeomorph X Y)
    (hcompat : ∀ i j, EqOn (p i) (p j) ((p i).source ∩ (p j).source)) :
    C(⋃ i, (p i).source, Y) :=
  glueOpenMaps (fun i => (p i).source) (fun i => (p i).open_source)
    (fun i => p i) (fun i => (p i).continuousOn) hcompat

theorem glueOpenPartialHomeomorphs_apply {X : Type u} {Y : Type v} {ι : Type w}
    [TopologicalSpace X] [TopologicalSpace Y]
    (p : ι → OpenPartialHomeomorph X Y)
    (hcompat : ∀ i j, EqOn (p i) (p j) ((p i).source ∩ (p j).source))
    (i : ι) (x : ⋃ j, (p j).source) (hx : x.val ∈ (p i).source) :
    glueOpenPartialHomeomorphs p hcompat x = p i x.val :=
  glueOpenMaps_apply _ _ _ _ hcompat i x hx

theorem glueOpenPartialHomeomorphs_isOpenMap {X : Type u} {Y : Type v} {ι : Type w}
    [TopologicalSpace X] [TopologicalSpace Y]
    (p : ι → OpenPartialHomeomorph X Y)
    (hcompat : ∀ i j, EqOn (p i) (p j) ((p i).source ∩ (p j).source)) :
    IsOpenMap (glueOpenPartialHomeomorphs p hcompat) :=
  glueOpenMaps_isOpenMap _ _ _ _ hcompat
    (fun i => (p i).isOpenEmbedding_restrict.isOpenMap)

/-- The glued flowout is locally injective throughout its source, before any
global injective shrinking. -/
theorem glueOpenPartialHomeomorphs_locally_injective
    {X : Type u} {Y : Type v} {ι : Type w}
    [TopologicalSpace X] [TopologicalSpace Y]
    (p : ι → OpenPartialHomeomorph X Y)
    (hcompat : ∀ i j, EqOn (p i) (p j) ((p i).source ∩ (p j).source))
    (z : ⋃ i, (p i).source) :
    ∃ V : Set (⋃ i, (p i).source), IsOpen V ∧ z ∈ V ∧
      InjOn (glueOpenPartialHomeomorphs p hcompat) V := by
  obtain ⟨i, hi⟩ := mem_iUnion.mp z.property
  refine ⟨Subtype.val ⁻¹' (p i).source,
    (p i).open_source.preimage continuous_subtype_val, hi, ?_⟩
  intro x hx y hy heq
  apply Subtype.ext
  apply (p i).injOn hx hy
  exact (glueOpenPartialHomeomorphs_apply p hcompat i x hx).symm.trans
    (heq.trans (glueOpenPartialHomeomorphs_apply p hcompat i y hy))


/-- The ordinary half-space is the product of its Euclidean face coordinates
and the nonnegative time coordinate. -/
def boundaryTimeModelHomeomorph (n : ℕ) :
    (ModelSpace n .euclidean × ↥(Ici (0 : ℝ))) ≃ₜ HalfSpace (n + 1) where
  toFun z := ⟨Fin.snoc z.1.val z.2.val, by
    simpa only [ModelData.halfSpaceSet, Set.mem_setOf_eq, mem_Ici, Fin.snoc_last] using z.2.property⟩
  invFun z := (⟨Fin.init z.val, mem_univ _⟩,
    ⟨z.val (Fin.last n), z.property⟩)
  left_inv z := by
    apply Prod.ext
    · apply Subtype.ext
      change Fin.init (Fin.snoc z.1.val z.2.val : Euclidean (n+1)) = z.1.val
      simp only [Fin.init_snoc]
    · apply Subtype.ext
      change (Fin.snoc z.1.val z.2.val : Euclidean (n+1)) (Fin.last n) = z.2.val
      simp only [Fin.snoc_last]
  right_inv z := Subtype.ext (Fin.snoc_init_self _)
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last]
      fun_prop
    · simp only [Fin.snoc_castSucc]
      exact (continuous_apply j : Continuous (fun f : Euclidean n => f j)).comp
        ((continuous_subtype_val : Continuous
          (fun z : ModelSpace n .euclidean => z.val)).comp continuous_fst)
  continuous_invFun := by
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      exact continuous_pi fun i =>
        (continuous_apply i.castSucc).comp continuous_subtype_val
    · exact ((continuous_apply (Fin.last n)).comp continuous_subtype_val).subtype_mk _

@[simp] theorem boundaryTimeModelHomeomorph_apply {n : ℕ}
    (z : ModelSpace n .euclidean × ↥(Ici (0 : ℝ))) :
    (boundaryTimeModelHomeomorph n z).val = Fin.snoc z.1.val z.2.val := rfl

@[simp] theorem boundaryTimeModelHomeomorph_symm_apply {n : ℕ} (z : HalfSpace (n+1)) :
    (boundaryTimeModelHomeomorph n).symm z =
      (⟨Fin.init z.val, mem_univ _⟩, ⟨z.val (Fin.last n), z.property⟩) := rfl

/-- An actual relative chart on boundary points times nonnegative time. -/
def boundaryTimeChart {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n+1) .halfSpace M)
    (b : ModelChart n .euclidean (intrinsicBoundary S)) :
    OpenPartialHomeomorph (intrinsicBoundary S × ↥(Ici (0 : ℝ))) (HalfSpace (n+1)) :=
  (b.prod (OpenPartialHomeomorph.refl _)).trans
    (boundaryTimeModelHomeomorph n).toOpenPartialHomeomorph

theorem boundaryTimeChart_source {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold (n+1) .halfSpace M}
    {e : ModelChart (n+1) .halfSpace M}
    {b : ModelChart n .euclidean (intrinsicBoundary S)} (hb : IsFaceRestriction S e b) :
    (boundaryTimeChart S b).source = (Subtype.val ⁻¹' e.source) ×ˢ univ := by
  simp [boundaryTimeChart, OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.prod_source, hb.1]

theorem boundaryTimeChart_apply {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold (n+1) .halfSpace M}
    {e : ModelChart (n+1) .halfSpace M}
    {b : ModelChart n .euclidean (intrinsicBoundary S)} (hb : IsFaceRestriction S e b)
    (x : intrinsicBoundary S × ↥(Ici (0 : ℝ))) (hx : x.1.val ∈ e.source) :
    ((boundaryTimeChart S b) x).val = boundaryTimeCoordinates e (x.1, x.2.val) := by
  change Fin.snoc (b x.1).val x.2.val = boundaryTimeCoordinates e (x.1, x.2.val)
  exact (boundaryTimeCoordinates_eq_face hb (x := (x.1, x.2.val)) hx).symm

@[simp] theorem boundaryTimeChart_symm_apply {n : ℕ} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold (n+1) .halfSpace M)
    (b : ModelChart n .euclidean (intrinsicBoundary S)) (z : HalfSpace (n+1)) :
    (boundaryTimeChart S b).symm z =
      (b.symm ⟨Fin.init z.val, mem_univ _⟩, ⟨z.val (Fin.last n), z.property⟩) := rfl

theorem boundaryTimeChart_target {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n+1) .halfSpace M)
    (b : ModelChart n .euclidean (intrinsicBoundary S)) :
    (boundaryTimeChart S b).target =
      {z | (⟨Fin.init z.val, mem_univ _⟩ : ModelSpace n .euclidean) ∈ b.target} := by
  ext z
  simp [boundaryTimeChart, OpenPartialHomeomorph.trans_target,
    OpenPartialHomeomorph.prod_target, boundaryTimeModelHomeomorph]

/-- Ambient coordinate-extension germs pass from an open subspace to its base. -/
theorem localCoordinateExtension_of_open_restrict {X : Type u} [TopologicalSpace X]
    {n m : ℕ} {r : ℕ∞} {U : Set X} (hU : IsOpen U) (x : U)
    (ι : X → Euclidean n) (f : X → Euclidean m)
    (h : LocalCoordinateExtension r (fun y : U => ι y.val) (fun y => f y.val) x) :
    LocalCoordinateExtension r ι f x.val := by
  obtain ⟨V, hV, hxV, F, hF, heq⟩ := h
  refine ⟨V, hV, hxV, F, hF, ?_⟩
  rw [← hU.isOpenEmbedding_subtypeVal.map_nhds_eq x]
  exact heq

/-- The total representative of a trajectory of a partial boundary flowout. -/
noncomputable def boundaryFlowoutCurve {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M}
    (W : Set (intrinsicBoundary S × ℝ)) (F : W → M)
    (q : intrinsicBoundary S) : ℝ → M := by
  classical
  exact fun t => if h : (q,t) ∈ W then F ⟨(q,t),h⟩ else q.val

/-- Compatible local one-sided boundary trajectories give a single smooth
flowout on a relative neighborhood of the entire boundary zero section. -/
theorem exists_boundary_flowout {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n + 1) .halfSpace M) (B : TangentBundleStructure S)
    (X : SmoothField B)
    (hin : ∀ (q : intrinsicBoundary S) (e : ModelChart (n + 1) .halfSpace M)
      (he : e ∈ S.smoothStructure.val) (hq : q.val ∈ e.source),
      0 < B.fiberCoordinates.equiv e he q.val hq (X.val q.val) (Fin.last n)) :
    ∃ (W : Set (intrinsicBoundary S × ℝ)) (F : W → M),
      W ⊆ univ ×ˢ Ici 0 ∧
      IsOpen ((fun x : intrinsicBoundary S × ↥(Ici (0 : ℝ)) => (x.1,x.2.val)) ⁻¹' W) ∧
      (∀ q, (q, 0) ∈ W) ∧
      (∀ q, W ∈ 𝓝[univ ×ˢ Ici (0 : ℝ)] (q, 0)) ∧
      Continuous F ∧ (∀ q (hq : (q,0) ∈ W), F ⟨(q,0), hq⟩ = q.val) ∧
      (∀ (e d : ModelChart (n + 1) .halfSpace M),
        e ∈ S.smoothStructure.val → d ∈ S.smoothStructure.val →
        ∀ x : W, x.val.1.val ∈ e.source → F x ∈ d.source →
          LocalCoordinateExtension (⊤ : ℕ∞)
            (fun y : W => boundaryTimeCoordinates e y.val)
            (fun y => (d (F y)).val) x) ∧
      (∀ (q : intrinsicBoundary S) (c : ℝ), 0 < c →
        (∀ t ∈ Ico 0 c, (q,t) ∈ W) →
        IsOneSidedIntegralCurveOn B X c (boundaryFlowoutCurve W F q) ∧
          boundaryFlowoutCurve W F q 0 = q.val) ∧
      (∀ x ∈ W, ∃ c : ℝ, 0 < c ∧ x.2 < c ∧
        ∀ t ∈ Ico 0 c, (x.1,t) ∈ W) := by
  classical
  let Q := intrinsicBoundary S
  have hcharts (q : Q) : ∃ e : ModelChart (n + 1) .halfSpace M,
      e ∈ S.smoothStructure.val ∧ q.val ∈ e.source :=
    S.smoothStructure.property.1.1 q.val
  choose e he hpe using hcharts
  choose b O γ hb hO hpO heO hγc hγ0 hγsource hγint hγsmooth using
    (fun q => local_boundary_family S B X q (e q) (he q) (hpe q)
      (hin q (e q) (he q) (hpe q)))
  let R : Q → Set (Q × ℝ) := fun i => O i ×ˢ Ico 0 (b i)
  let W : Set (Q × ℝ) := ⋃ i, R i
  have hRW (i : Q) : R i ⊆ W := subset_iUnion R i
  let A : Q → Set W := fun i => Subtype.val ⁻¹' R i
  have hAo (i : Q) : IsOpen (A i) := by
    have heq : A i = (fun x : W => x.val.1) ⁻¹' O i ∩
        (fun x : W => x.val.2) ⁻¹' Iio (b i) := by
      ext x
      refine and_congr_right (fun hq => ?_)
      have hxnonneg : 0 ≤ x.val.2 := by
        obtain ⟨j,hj⟩ := mem_iUnion.mp x.property
        exact hj.2.1
      simp only [mem_preimage, mem_Iio, mem_Ico, hxnonneg, true_and]
    rw [heq]
    exact ((hO i).preimage (continuous_fst.comp continuous_subtype_val)).inter
      (isOpen_Iio.preimage (continuous_snd.comp continuous_subtype_val))
  have hcompat (i j : Q) : EqOn (fun x : Q × ℝ => γ i x.1 x.2)
      (fun x => γ j x.1 x.2) (R i ∩ R j) := by
    intro x hx
    apply oneSided_overlap_unique S B X (hb i) (hb j) (γ i x.1) (γ j x.1)
      (hγint i x.1 hx.1.1) (hγint j x.1 hx.2.1)
      ((hγ0 i x.1 hx.1.1).trans (hγ0 j x.1 hx.2.1).symm)
    exact ⟨hx.1.2.1, lt_min hx.1.2.2 hx.2.2.2⟩
  let f : ∀ i, C(A i, M) := fun i => ⟨fun x => γ i x.val.val.1 x.val.val.2,
    (hγc i).comp_continuous (continuous_subtype_val.comp continuous_subtype_val)
      (fun x => x.property)⟩
  let F : C(W, M) := ContinuousMap.liftCover A f
    (fun i j x hxi hxj => hcompat i j ⟨hxi,hxj⟩)
    (fun x => by
      obtain ⟨i, hi⟩ := mem_iUnion.mp x.property
      exact ⟨i, (hAo i).mem_nhds hi⟩)
  have hFagree (i : Q) (x : W) (hx : x.val ∈ R i) : F x = γ i x.val.1 x.val.2 := by
    exact ContinuousMap.liftCover_coe (x := ⟨x,hx⟩)
  have hzero (q : Q) : (q,0) ∈ W :=
    hRW q ⟨hpO q, le_rfl, hb q⟩
  refine ⟨W, F, ?_, ?_, hzero, ?_, F.continuous, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    exact ⟨mem_univ _, hi.2.1⟩
  · have heq : (fun x : Q × ↥(Ici (0 : ℝ)) => (x.1,x.2.val)) ⁻¹' W =
        ⋃ i, (fun x : Q × ↥(Ici (0 : ℝ)) => x.1) ⁻¹' O i ∩
          (fun x : Q × ↥(Ici (0 : ℝ)) => x.2.val) ⁻¹' Iio (b i) := by
      ext x
      have hnonneg : 0 ≤ x.2.val := x.2.property
      simp only [mem_preimage, W, mem_iUnion, R, mem_prod, mem_Ico, mem_inter_iff, mem_Iio,
        hnonneg, true_and]
      rfl
    rw [heq]
    apply isOpen_iUnion
    intro i
    exact ((hO i).preimage continuous_fst).inter
      (isOpen_Iio.preimage (continuous_subtype_val.comp continuous_snd))
  · intro q
    apply Filter.mem_of_superset ?_ (hRW q)
    have hprod : O q ×ˢ Iio (b q) ∈ 𝓝 (q,(0 : ℝ)) :=
      prod_mem_nhds ((hO q).mem_nhds (hpO q)) (Iio_mem_nhds (hb q))
    have hinter : (O q ×ˢ Iio (b q)) ∩ (univ ×ˢ Ici (0 : ℝ)) ∈
        𝓝[univ ×ˢ Ici (0 : ℝ)] (q,0) :=
      inter_mem (mem_nhdsWithin_of_mem_nhds hprod) self_mem_nhdsWithin
    exact Filter.mem_of_superset hinter (fun x hx => ⟨hx.1.1,hx.2.2,hx.1.2⟩)
  · intro q hq
    exact (hFagree q _ ⟨hpO q, le_rfl, hb q⟩).trans (hγ0 q q (hpO q))
  · intro d c hd hc x hxd hxc
    obtain ⟨i, hi⟩ := mem_iUnion.mp x.property
    let xi : A i := ⟨x, hi⟩
    let pull : A i → R i := fun z => ⟨z.val.val,z.property⟩
    have hpull : Continuous pull := continuous_subtype_val.comp continuous_subtype_val |>.subtype_mk _
    have hFpoint : F x = γ i x.val.1 x.val.2 := hFagree i x hi
    have hlocal := hγsmooth i (pull xi) c hc (hFpoint ▸ hxc)
    have hlocal' := LocalCoordinateExtension.precomp hlocal hpull.continuousAt rfl
    have htransfer := LocalCoordinateExtension.precomp (p := xi)
      (h := fun z : A i => z.val.val)
      (boundaryTimeCoordinates_transition S d (e i) hd (he i) x.val hxd (heO i _ hi.1))
      (continuous_subtype_val.comp continuous_subtype_val).continuousAt rfl
    have hboth := LocalCoordinateExtension.comp hlocal' htransfer
    have htarget : (fun z : A i => (c (γ i z.val.val.1 z.val.val.2)).val) =
        (fun z : A i => (c (F z.val)).val) := by
      funext z
      rw [hFagree i z.val z.property]
    change LocalCoordinateExtension (⊤ : ℕ∞)
      (fun z : A i => boundaryTimeCoordinates d z.val.val)
      (fun z : A i => (c (γ i z.val.val.1 z.val.val.2)).val) xi at hboth
    rw [htarget] at hboth
    exact localCoordinateExtension_of_open_restrict (hAo i) xi
      (fun y : W => boundaryTimeCoordinates d y.val) (fun y => (c (F y)).val) hboth
  · intro q c hc hrect
    let η := boundaryFlowoutCurve W F q
    have hηeq (t : ℝ) (ht : t ∈ Ico 0 c) : η t = F ⟨(q,t), hrect t ht⟩ := by
      simp only [η, boundaryFlowoutCurve, dite_eq_left (hrect t ht)]
    have hηc : ContinuousOn η (Ico 0 c) := by
      apply continuousOn_iff_continuous_domRestrict.mpr
      have hmap : Continuous (fun t : ↥(Ico (0 : ℝ) c) =>
          (⟨(q,t.val), hrect t.val t.property⟩ : W)) :=
        (continuous_const.prodMk continuous_subtype_val).subtype_mk _
      exact (F.continuous.comp hmap).congr (fun t => (hηeq t.val t.property).symm)
    refine ⟨⟨hηc, ?_⟩, ?_⟩
    · intro t ht d hd hdt
      obtain ⟨i,hi⟩ := mem_iUnion.mp (hrect t ht)
      have hpoint : η t = γ i q t := (hηeq t ht).trans (hFagree i _ hi)
      have hdi : γ i q t ∈ d.source := hpoint ▸ hdt
      have hder := (hγint i q hi.1).2 t hi.2 d hd hdi
      have hset : Ico (0 : ℝ) (b i) ∈ 𝓝[Ico 0 c] t := by
        filter_upwards [self_mem_nhdsWithin,
          mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hi.2.2)] with s hs hsb
        exact ⟨hs.1, hsb⟩
      have hdr := hder.mono_of_mem_nhdsWithin hset
      have hv : B.fiberCoordinates.equiv d hd (γ i q t) hdi (X.val (γ i q t)) =
          B.fiberCoordinates.equiv d hd (η t) hdt (X.val (η t)) := by
        rw [← TangentBundle.chartFiber_eq S B d hd ⟨γ i q t, X.val (γ i q t)⟩ hdi,
          ← TangentBundle.chartFiber_eq S B d hd ⟨η t, X.val (η t)⟩ hdt]
        exact congrArg (fun y => TangentBundle.chartFiber B d hd ⟨y, X.val y⟩) hpoint.symm
      rw [hv] at hdr
      apply hdr.congr_of_eventuallyEq_of_mem _ ht
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hi.2.2)] with s hs hsb
      exact congrArg (fun z => (d z).val)
        ((hηeq s hs).trans (hFagree i _ ⟨hi.1, hs.1, hsb⟩))
    · exact (hηeq 0 ⟨le_rfl,hc⟩).trans
        ((hFagree q _ ⟨hpO q, le_rfl, hb q⟩).trans (hγ0 q q (hpO q)))
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact ⟨b i, hb i, hi.2.2, fun t ht => hRW i ⟨hi.1, ht⟩⟩


/-- The forward local flowout test in one pair of original charts gives the
test in every pair through the actual boundary-product transitions. -/
theorem boundaryFlowout_forward_changeCharts
    {n : ℕ} {a : ModelKind} {M : Type u} {X : Type v}
    [TopologicalSpace M] [TopologicalSpace X] (S : SmoothManifold (n+1) a M)
    (F : X → M) (j : X → intrinsicBoundary S × ℝ) (x : X)
    (hF : ContinuousAt F x) (hj : ContinuousAt j x)
    (e₀ d₀ e d : ModelChart (n+1) a M)
    (he₀ : e₀ ∈ S.smoothStructure.val) (hd₀ : d₀ ∈ S.smoothStructure.val)
    (he : e ∈ S.smoothStructure.val) (hd : d ∈ S.smoothStructure.val)
    (hxe₀ : (j x).1.val ∈ e₀.source) (hxe : (j x).1.val ∈ e.source)
    (hxd₀ : F x ∈ d₀.source) (hxd : F x ∈ d.source)
    (hlocal : LocalCoordinateExtension (⊤ : ℕ∞)
      (fun z => boundaryTimeCoordinates e₀ (j z)) (fun z => (d₀ (F z)).val) x) :
    LocalCoordinateExtension (⊤ : ℕ∞)
      (fun z => boundaryTimeCoordinates e (j z)) (fun z => (d (F z)).val) x := by
  have hsource := LocalCoordinateExtension.precomp
    (boundaryTimeCoordinates_transition S e e₀ he he₀ (j x) hxe hxe₀) hj rfl
  have htarget := LocalCoordinateExtension.precomp
    (chartContDiffAt_of_compatible (S.smoothStructure.property.1.2 d₀ hd₀ d hd) hxd₀ hxd)
    hF rfl
  exact LocalCoordinateExtension.comp htarget (LocalCoordinateExtension.comp hlocal hsource)

/-- One inverse germ in the selected construction charts determines every
ambient-chart and boundary-product-coordinate inverse test. -/
theorem boundaryFlowout_inverse_changeCharts
    {n : ℕ} {a : ModelKind} {M : Type u} {X : Type v}
    [TopologicalSpace M] [TopologicalSpace X] (S : SmoothManifold (n+1) a M)
    (p : OpenPartialHomeomorph X M) (j : X → intrinsicBoundary S × ℝ) (y : M)
    (hyp : y ∈ p.target) (hj : ContinuousAt j (p.symm y))
    (e₀ d₀ e d : ModelChart (n+1) a M)
    (he₀ : e₀ ∈ S.smoothStructure.val) (hd₀ : d₀ ∈ S.smoothStructure.val)
    (he : e ∈ S.smoothStructure.val) (hd : d ∈ S.smoothStructure.val)
    (hye₀ : (j (p.symm y)).1.val ∈ e₀.source)
    (hye : (j (p.symm y)).1.val ∈ e.source)
    (hyd₀ : y ∈ d₀.source) (hyd : y ∈ d.source)
    (hlocal : LocalCoordinateExtension (⊤ : ℕ∞) (fun z => (d₀ z).val)
      (fun z => boundaryTimeCoordinates e₀ (j (p.symm z))) y) :
    LocalCoordinateExtension (⊤ : ℕ∞) (fun z => (d z).val)
      (fun z => boundaryTimeCoordinates e (j (p.symm z))) y := by
  have hsource := chartContDiffAt_of_compatible
    (S.smoothStructure.property.1.2 d hd d₀ hd₀) hyd hyd₀
  have htarget := LocalCoordinateExtension.precomp
    (boundaryTimeCoordinates_transition S e₀ e he₀ he (j (p.symm y)) hye₀ hye)
    (hj.comp (p.symm.continuousAt hyp)) rfl
  exact LocalCoordinateExtension.comp htarget (LocalCoordinateExtension.comp hlocal hsource)


/-- Local partial-homeomorphism descriptions along an open source realization
suffice for the composite map to be open. -/
theorem isOpenMap_of_open_realization_locally_partialHomeomorph
    {A : Type u} {X : Type v} {Y : Type w}
    [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]
    (F : X → Y) (j : A → X) (hj : IsOpenMap j)
    (hlocal : ∀ x : A, ∃ p : OpenPartialHomeomorph X Y,
      j x ∈ p.source ∧ EqOn p F p.source) : IsOpenMap (F ∘ j) := by
  intro V hV
  apply isOpen_iff_mem_nhds.mpr
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨p, hxp, hp⟩ := hlocal x
  have hopen : IsOpen (p '' (j '' V ∩ p.source)) :=
    p.isOpen_image_of_subset_source ((hj V hV).inter p.open_source) inter_subset_right
  have hximage : (F ∘ j) x ∈ p '' (j '' V ∩ p.source) :=
    ⟨j x, ⟨⟨x, hx, rfl⟩, hxp⟩, hp hxp⟩
  apply Filter.mem_of_superset (hopen.mem_nhds hximage)
  rintro z ⟨w, ⟨⟨a, ha, rfl⟩, hw⟩, rfl⟩
  exact ⟨a, ha, (hp hw).symm⟩

/-- A continuous realization of a global source in the local flowout source
allows transfer of its inverse germ, even when the two source types differ. -/
theorem homeomorph_inverse_eventuallyEq_of_local_realization
    {A : Type u} {X : Type v} {Y : Type w}
    [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]
    {N : Set Y} (G : A ≃ₜ N) (j : A → X) (hj : Continuous j)
    (p : OpenPartialHomeomorph X Y)
    (hagree : ∀ z : A, j z ∈ p.source → (G z).val = p (j z))
    (y : N) (hy : j (G.symm y) ∈ p.source) :
    (fun z => j (G.symm z)) =ᶠ[𝓝 y] (fun z => p.symm z.val) := by
  have hevent : ∀ᶠ z : N in 𝓝 y, j (G.symm z) ∈ p.source :=
    (hj.comp G.symm.continuous).continuousAt.preimage_mem_nhds
      (p.open_source.mem_nhds hy)
  filter_upwards [hevent] with z hz
  calc
    j (G.symm z) = p.symm (p (j (G.symm z))) := (p.left_inv hz).symm
    _ = p.symm (G (G.symm z)).val := congrArg p.symm (hagree (G.symm z) hz).symm
    _ = p.symm z.val := by rw [G.apply_symm_apply]

/-- Smooth local inverse coordinates pass to the inverse of a glued global
homeomorphism through the preceding inverse germ equality. -/
theorem homeomorph_inverse_localCoordinateExtension_of_local_realization
    {A : Type u} {X : Type v} {Y : Type w}
    [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]
    {N : Set Y} (G : A ≃ₜ N) (j : A → X) (hj : Continuous j)
    (p : OpenPartialHomeomorph X Y)
    (hagree : ∀ z : A, j z ∈ p.source → (G z).val = p (j z))
    (y : N) (hy : j (G.symm y) ∈ p.source)
    {n m : ℕ} {r : ℕ∞} (ι : Y → Euclidean n) (κ : X → Euclidean m)
    (hlocal : LocalCoordinateExtension r ι (fun z => κ (p.symm z)) y.val) :
    LocalCoordinateExtension r (fun z : N => ι z.val)
      (fun z => κ (j (G.symm z))) y := by
  have heq := homeomorph_inverse_eventuallyEq_of_local_realization G j hj p hagree y hy
  have hs := LocalCoordinateExtension.precomp hlocal continuousAt_subtype_val rfl
  exact hs.congr (heq.fun_comp κ).symm




/-- At time zero the boundary product chart is the original ambient chart. -/
theorem boundaryTimeChart_zero {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n+1) .halfSpace M)
    (e : ModelChart (n+1) .halfSpace M) (he : e ∈ S.smoothStructure.val)
    (b : ModelChart n .euclidean (intrinsicBoundary S)) (hb : IsFaceRestriction S e b)
    (q : intrinsicBoundary S) (hq : q.val ∈ e.source) :
    boundaryTimeChart S b (q, ⟨0, by simp⟩) = e q.val := by
  apply Subtype.ext
  rw [boundaryTimeChart_apply hb _ hq]
  have hface : (e q.val).val (Fin.last n) = 0 :=
    (intrinsicBoundary_iff_chart S e he q.val hq).mp q.property
  change Fin.snoc (Fin.init (e q.val).val) 0 = (e q.val).val
  rw [← hface, Fin.snoc_init_self]

/-- Pull a relative half-space local inverse back to boundary-times-time and
forward through the original ambient chart. -/
def boundaryFlowChart {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n+1) .halfSpace M)
    (e : ModelChart (n+1) .halfSpace M)
    (b : ModelChart n .euclidean (intrinsicBoundary S))
    (g : OpenPartialHomeomorph (HalfSpace (n+1)) (HalfSpace (n+1))) :
    OpenPartialHomeomorph (intrinsicBoundary S × ↥(Ici (0 : ℝ))) M :=
  ((boundaryTimeChart S b).trans g).trans e.symm

theorem boundaryFlowChart_zero_mem {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n+1) .halfSpace M)
    (e : ModelChart (n+1) .halfSpace M) (he : e ∈ S.smoothStructure.val)
    (b : ModelChart n .euclidean (intrinsicBoundary S)) (hb : IsFaceRestriction S e b)
    (g : OpenPartialHomeomorph (HalfSpace (n+1)) (HalfSpace (n+1)))
    (q : intrinsicBoundary S) (hq : q.val ∈ e.source)
    (hgs : e q.val ∈ g.source) (hgzero : g (e q.val) = e q.val) :
    (q, ⟨0, by simp⟩) ∈ (boundaryFlowChart S e b g).source := by
  change ((q, ⟨0, by simp⟩) ∈ (boundaryTimeChart S b).source ∧
    boundaryTimeChart S b (q, ⟨0, by simp⟩) ∈ g.source) ∧
    g (boundaryTimeChart S b (q, ⟨0, by simp⟩)) ∈ e.target
  rw [boundaryTimeChart_zero S e he b hb q hq]
  refine ⟨⟨?_, hgs⟩, by rw [hgzero]; exact e.map_source hq⟩
  rw [boundaryTimeChart_source hb]
  exact ⟨hq, mem_univ _⟩

theorem boundaryFlowChart_smooth {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n+1) .halfSpace M)
    (e : ModelChart (n+1) .halfSpace M)
    (b : ModelChart n .euclidean (intrinsicBoundary S)) (hb : IsFaceRestriction S e b)
    (g : OpenPartialHomeomorph (HalfSpace (n+1)) (HalfSpace (n+1)))
    (hg : ∀ x ∈ g.source, LocalCoordinateExtension (⊤ : ℕ∞) Subtype.val
      (fun z => (g z).val) x)
    (x : intrinsicBoundary S × ↥(Ici (0 : ℝ)))
    (hx : x ∈ (boundaryFlowChart S e b g).source) :
    LocalCoordinateExtension (⊤ : ℕ∞)
      (fun y => boundaryTimeCoordinates e (y.1, y.2.val))
      (fun y => (e (boundaryFlowChart S e b g y)).val) x := by
  let c := boundaryTimeChart S b
  let H := boundaryFlowChart S e b g
  change (x ∈ c.source ∧ c x ∈ g.source) ∧ g (c x) ∈ e.target at hx
  have h := LocalCoordinateExtension.precomp (hg (c x) hx.1.2)
    (c.continuousAt hx.1.1) rfl
  apply localCoordinateExtension_congr_source
    (h.congr ?_) ?_
  · filter_upwards [H.open_source.mem_nhds (show x ∈ H.source from hx)] with y hy
    change (y ∈ c.source ∧ c y ∈ g.source) ∧ g (c y) ∈ e.target at hy
    change (g (c y)).val = (e (e.symm (g (c y)))).val
    rw [e.right_inv hy.2]
  · filter_upwards [c.open_source.mem_nhds hx.1.1] with y hy
    apply boundaryTimeChart_apply hb y
    have hy' : y ∈ (Subtype.val ⁻¹' e.source) ×ˢ univ := by
      rwa [← boundaryTimeChart_source hb]
    exact hy'.1

theorem boundaryFlowChart_inverse_smooth {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n+1) .halfSpace M)
    (e : ModelChart (n+1) .halfSpace M)
    (b : ModelChart n .euclidean (intrinsicBoundary S)) (hb : IsFaceRestriction S e b)
    (g : OpenPartialHomeomorph (HalfSpace (n+1)) (HalfSpace (n+1)))
    (hg : ∀ y ∈ g.target, LocalCoordinateExtension (⊤ : ℕ∞) Subtype.val
      (fun z => (g.symm z).val) y)
    (y : M) (hy : y ∈ (boundaryFlowChart S e b g).target) :
    LocalCoordinateExtension (⊤ : ℕ∞) (fun z => (e z).val)
      (fun z => boundaryTimeCoordinates e
        (((boundaryFlowChart S e b g).symm z).1,
          ((boundaryFlowChart S e b g).symm z).2.val)) y := by
  let c := boundaryTimeChart S b
  let H := boundaryFlowChart S e b g
  change y ∈ e.source ∧ e y ∈ g.target ∧ g.symm (e y) ∈ c.target at hy
  have h := LocalCoordinateExtension.precomp (hg (e y) hy.2.1)
    (e.continuousAt hy.1) rfl
  apply h.congr
  filter_upwards [H.open_target.mem_nhds (show y ∈ H.target from hy)] with z hz
  change z ∈ e.source ∧ e z ∈ g.target ∧ g.symm (e z) ∈ c.target at hz
  have hcs : c.symm (g.symm (e z)) ∈ c.source := c.map_target hz.2.2
  have hsrc : (c.symm (g.symm (e z))).1.val ∈ e.source := by
    have hcs' : c.symm (g.symm (e z)) ∈ (Subtype.val ⁻¹' e.source) ×ˢ univ := by
      rwa [← boundaryTimeChart_source hb]
    exact hcs'.1
  change (g.symm (e z)).val = boundaryTimeCoordinates e
    ((c.symm (g.symm (e z))).1, (c.symm (g.symm (e z))).2.val)
  rw [← boundaryTimeChart_apply hb _ hsrc]
  exact congrArg Subtype.val (c.right_inv hz.2.2).symm

/-- The initial-state part of the boundary product chart is the actual
ambient boundary point in its original chart. -/
theorem boundaryTimeChart_faceProjection {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n+1) .halfSpace M)
    (e : ModelChart (n+1) .halfSpace M) (he : e ∈ S.smoothStructure.val)
    (b : ModelChart n .euclidean (intrinsicBoundary S)) (hb : IsFaceRestriction S e b)
    (x : intrinsicBoundary S × ↥(Ici (0 : ℝ))) (hx : x.1.val ∈ e.source) :
    faceProjection ((boundaryTimeChart S b) x).val = (e x.1.val).val := by
  rw [boundaryTimeChart_apply hb x hx]
  have hface : (e x.1.val).val (Fin.last n) = 0 :=
    (intrinsicBoundary_iff_chart S e he x.1.val hx).mp x.1.property
  change faceProjection (Fin.snoc (Fin.init (e x.1.val).val) x.2.val) = (e x.1.val).val
  rw [faceProjection_apply, Fin.init_snoc]
  exact (congrArg (fun r : ℝ =>
    (Fin.snoc (Fin.init (e x.1.val).val) r : Euclidean (n+1))) hface.symm).trans
      (Fin.snoc_init_self _)

theorem boundaryTimeChart_time {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n+1) .halfSpace M)
    (b : ModelChart n .euclidean (intrinsicBoundary S))
    (x : intrinsicBoundary S × ↥(Ici (0 : ℝ))) :
    ((boundaryTimeChart S b) x).val (Fin.last n) = x.2.val := by
  change (Fin.snoc (b x.1).val x.2.val : Euclidean (n+1)) (Fin.last n) = x.2.val
  exact Fin.snoc_last _ _

/-- The pulled-back local inverse agrees with the actual ambient flow from
the boundary initial state, in the selected chart. -/
theorem boundaryFlowChart_apply_coordinates {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n+1) .halfSpace M)
    (e : ModelChart (n+1) .halfSpace M) (he : e ∈ S.smoothStructure.val)
    (b : ModelChart n .euclidean (intrinsicBoundary S)) (hb : IsFaceRestriction S e b)
    (g : OpenPartialHomeomorph (HalfSpace (n+1)) (HalfSpace (n+1)))
    (Φ : ℝ × Euclidean (n+1) → Euclidean (n+1))
    (hg : ∀ z ∈ g.source,
      (g z).val = Φ (z.val (Fin.last n), faceProjection z.val))
    (x : intrinsicBoundary S × ↥(Ici (0 : ℝ)))
    (hx : x ∈ (boundaryFlowChart S e b g).source) :
    (e (boundaryFlowChart S e b g x)).val = Φ (x.2.val, (e x.1.val).val) := by
  let c := boundaryTimeChart S b
  change (x ∈ c.source ∧ c x ∈ g.source) ∧ g (c x) ∈ e.target at hx
  have hxe : x.1.val ∈ e.source := by
    have hx' : x ∈ (Subtype.val ⁻¹' e.source) ×ˢ univ := by
      rw [← boundaryTimeChart_source hb]
      exact hx.1.1
    exact hx'.1
  change (e (e.symm (g (c x)))).val = _
  rw [e.right_inv hx.2, hg (c x) hx.1.2,
    boundaryTimeChart_time S b x, boundaryTimeChart_faceProjection S e he b hb x hxe]

/-- Restrict a local boundary flow inverse to the initial-state and time
rectangle where a chosen one-sided trajectory family is available. -/
def boundaryFlowChartIn {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n+1) .halfSpace M)
    (e : ModelChart (n+1) .halfSpace M)
    (b : ModelChart n .euclidean (intrinsicBoundary S))
    (g : OpenPartialHomeomorph (HalfSpace (n+1)) (HalfSpace (n+1)))
    (O : Set (intrinsicBoundary S)) (hO : IsOpen O) (τ : ℝ) :
    OpenPartialHomeomorph (intrinsicBoundary S × ↥(Ici (0 : ℝ))) M :=
  (boundaryFlowChart S e b g).restrOpen
    (O ×ˢ ((Subtype.val : ↥(Ici (0 : ℝ)) → ℝ) ⁻¹' Iio τ))
    (hO.prod (isOpen_Iio.preimage continuous_subtype_val))

theorem boundaryFlowChartIn_source {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n+1) .halfSpace M)
    (e : ModelChart (n+1) .halfSpace M)
    (b : ModelChart n .euclidean (intrinsicBoundary S))
    (g : OpenPartialHomeomorph (HalfSpace (n+1)) (HalfSpace (n+1)))
    (O : Set (intrinsicBoundary S)) (hO : IsOpen O) (τ : ℝ) :
    (boundaryFlowChartIn S e b g O hO τ).source =
      (boundaryFlowChart S e b g).source ∩ {x | x.1 ∈ O ∧ x.2.val < τ} := rfl

theorem boundaryFlowChartIn_zero_mem {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n+1) .halfSpace M)
    (e : ModelChart (n+1) .halfSpace M) (he : e ∈ S.smoothStructure.val)
    (b : ModelChart n .euclidean (intrinsicBoundary S)) (hb : IsFaceRestriction S e b)
    (g : OpenPartialHomeomorph (HalfSpace (n+1)) (HalfSpace (n+1)))
    (O : Set (intrinsicBoundary S)) (hO : IsOpen O) (τ : ℝ) (hτ : 0 < τ)
    (q : intrinsicBoundary S) (hq : q.val ∈ e.source) (hqO : q ∈ O)
    (hgs : e q.val ∈ g.source) (hgzero : g (e q.val) = e q.val) :
    (q, ⟨0, by simp⟩) ∈ (boundaryFlowChartIn S e b g O hO τ).source :=
  ⟨boundaryFlowChart_zero_mem S e he b hb g q hq hgs hgzero, hqO, hτ⟩

theorem boundaryFlowChartIn_inverse_smooth {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n+1) .halfSpace M)
    (e : ModelChart (n+1) .halfSpace M)
    (b : ModelChart n .euclidean (intrinsicBoundary S)) (hb : IsFaceRestriction S e b)
    (g : OpenPartialHomeomorph (HalfSpace (n+1)) (HalfSpace (n+1)))
    (hg : ∀ y ∈ g.target, LocalCoordinateExtension (⊤ : ℕ∞) Subtype.val
      (fun z => (g.symm z).val) y)
    (O : Set (intrinsicBoundary S)) (hO : IsOpen O) (τ : ℝ)
    (y : M) (hy : y ∈ (boundaryFlowChartIn S e b g O hO τ).target) :
    LocalCoordinateExtension (⊤ : ℕ∞) (fun z => (e z).val)
      (fun z => boundaryTimeCoordinates e
        (((boundaryFlowChartIn S e b g O hO τ).symm z).1,
          ((boundaryFlowChartIn S e b g O hO τ).symm z).2.val)) y :=
  boundaryFlowChart_inverse_smooth S e b hb g hg y hy.1

/-- Realize a nonnegative real-time domain as its corresponding subspace of
boundary points times the actual nonnegative time subtype. -/
def nonnegativeDomainHomeomorph {Q : Type u} [TopologicalSpace Q]
    (W : Set (Q × ℝ)) (hW : W ⊆ univ ×ˢ Ici (0 : ℝ)) :
    W ≃ₜ ((fun x : Q × ↥(Ici (0 : ℝ)) => (x.1,x.2.val)) ⁻¹' W) where
  toFun x := ⟨(x.val.1, ⟨x.val.2, (hW x.property).2⟩), x.property⟩
  invFun y := ⟨(y.val.1,y.val.2.val), y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def nonnegativeDomainMap {Q : Type u} [TopologicalSpace Q]
    (W : Set (Q × ℝ)) (hW : W ⊆ univ ×ˢ Ici (0 : ℝ)) : W → Q × ↥(Ici (0 : ℝ)) :=
  fun x => (x.val.1, ⟨x.val.2, (hW x.property).2⟩)

theorem nonnegativeDomainMap_isOpenEmbedding {Q : Type u} [TopologicalSpace Q]
    (W : Set (Q × ℝ)) (hW : W ⊆ univ ×ˢ Ici (0 : ℝ))
    (ho : IsOpen ((fun x : Q × ↥(Ici (0 : ℝ)) => (x.1,x.2.val)) ⁻¹' W)) :
    Topology.IsOpenEmbedding (nonnegativeDomainMap W hW) :=
  ho.isOpenEmbedding_subtypeVal.comp (nonnegativeDomainHomeomorph W hW).isOpenEmbedding

/-- Intrinsic uniqueness identifies a local flow chart with the glued flowout.
The global time domain only needs to contain an initial segment through each
of its points; no uniform width on the boundary is used. -/
theorem boundary_flowout_chart_agreement {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n + 1) .halfSpace M) (B : TangentBundleStructure S)
    (X : SmoothField B) (W : Set (intrinsicBoundary S × ℝ))
    (hW : W ⊆ univ ×ˢ Ici (0 : ℝ)) (F : W → M)
    (hsegments : ∀ x ∈ W, ∃ c : ℝ, 0 < c ∧ x.2 < c ∧
      ∀ t ∈ Ico 0 c, (x.1,t) ∈ W)
    (hcurves : ∀ q c, 0 < c → (∀ t ∈ Ico 0 c, (q,t) ∈ W) →
      IsOneSidedIntegralCurveOn B X c (boundaryFlowoutCurve W F q) ∧
        boundaryFlowoutCurve W F q 0 = q.val)
    (O : Set (intrinsicBoundary S)) (b : ℝ) (hb : 0 < b)
    (γ : intrinsicBoundary S → ℝ → M)
    (hγ : ∀ q ∈ O, IsOneSidedIntegralCurveOn B X b (γ q))
    (hγ0 : ∀ q ∈ O, γ q 0 = q.val)
    (p : OpenPartialHomeomorph (intrinsicBoundary S × ↥(Ici (0 : ℝ))) M)
    (hpsource : ∀ x ∈ p.source, x.1 ∈ O ∧ x.2.val < b)
    (hpformula : ∀ x ∈ p.source, p x = γ x.1 x.2.val) :
    ∀ x : W, nonnegativeDomainMap W hW x ∈ p.source →
      p (nonnegativeDomainMap W hW x) = F x := by
  classical
  intro x hx
  obtain ⟨c,hc,htc,hseg⟩ := hsegments x.val x.property
  have hglobal := hcurves x.val.1 c hc hseg
  have hloc := hpsource _ hx
  have huniq := oneSided_overlap_unique S B X hc hb
    (boundaryFlowoutCurve W F x.val.1) (γ x.val.1)
    hglobal.1 (hγ _ hloc.1) (hglobal.2.trans (hγ0 _ hloc.1).symm)
  have htime : x.val.2 ∈ Ico (0 : ℝ) (min c b) :=
    ⟨(hW x.property).2, lt_min htc hloc.2⟩
  calc
    p (nonnegativeDomainMap W hW x) = γ x.val.1 x.val.2 := hpformula _ hx
    _ = boundaryFlowoutCurve W F x.val.1 x.val.2 := (huniq htime).symm
    _ = F x := by simp only [boundaryFlowoutCurve, dite_eq_left x.property]

/-- Pull a half-space-time local chart back to a relatively open nonnegative
real-time domain. The inverse agrees after forgetting the time subtype. -/
theorem pullback_boundary_time_chart {Q : Type u} {M : Type v}
    [TopologicalSpace Q] [TopologicalSpace M]
    (W : Set (Q × ℝ)) (hW : W ⊆ univ ×ˢ Ici (0 : ℝ))
    (ho : IsOpen ((fun x : Q × ↥(Ici (0 : ℝ)) => (x.1,x.2.val)) ⁻¹' W))
    (x₀ : W) (p : OpenPartialHomeomorph (Q × ↥(Ici (0 : ℝ))) M)
    (hp₀ : nonnegativeDomainMap W hW x₀ ∈ p.source) :
    ∃ pW : OpenPartialHomeomorph W M,
      x₀ ∈ pW.source ∧
      (∀ x : W, x ∈ pW.source ↔ nonnegativeDomainMap W hW x ∈ p.source) ∧
      (∀ x : W, pW x = p (nonnegativeDomainMap W hW x)) ∧
      pW.target ⊆ p.target ∧
      (∀ y ∈ pW.target, nonnegativeDomainMap W hW (pW.symm y) = p.symm y) := by
  letI : Nonempty W := ⟨x₀⟩
  let k := (nonnegativeDomainMap_isOpenEmbedding W hW ho).toOpenPartialHomeomorph
    (nonnegativeDomainMap W hW)
  let pW := k.trans p
  have hsource (x : W) : x ∈ pW.source ↔ nonnegativeDomainMap W hW x ∈ p.source := by
    change x ∈ k.source ∧ k x ∈ p.source ↔ _
    simp only [k, Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source,
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_apply, mem_univ, true_and]
  refine ⟨pW, (hsource x₀).mpr hp₀, hsource, (fun _ => rfl),
    (fun _ hy => hy.1), ?_⟩
  intro y hy
  change nonnegativeDomainMap W hW (k.symm (p.symm y)) = p.symm y
  exact k.right_inv hy.2

/-- Coordinate smoothness of a local inverse survives passage from the
nonnegative-time subtype to the equivalent real-time domain. -/
theorem pullback_boundary_time_chart_inverse_smooth {n k : ℕ} {a : ModelKind}
    {M : Type u} [TopologicalSpace M] {S : SmoothManifold (n + 1) a M}
    (e : ModelChart (n + 1) a M)
    (W : Set (intrinsicBoundary S × ℝ)) (hW : W ⊆ univ ×ˢ Ici (0 : ℝ))
    (p : OpenPartialHomeomorph (intrinsicBoundary S × ↥(Ici (0 : ℝ))) M)
    (pW : OpenPartialHomeomorph W M)
    (hsymm : ∀ y ∈ pW.target, nonnegativeDomainMap W hW (pW.symm y) = p.symm y)
    (ι : M → Euclidean k) (y : M) (hy : y ∈ pW.target)
    (hpinv : LocalCoordinateExtension (⊤ : ℕ∞) ι
      (fun z => boundaryTimeCoordinates e ((p.symm z).1,(p.symm z).2.val)) y) :
    LocalCoordinateExtension (⊤ : ℕ∞) ι
      (fun z => boundaryTimeCoordinates e (pW.symm z).val) y := by
  apply hpinv.congr
  filter_upwards [pW.open_target.mem_nhds hy] with z hz
  exact congrArg (fun x => boundaryTimeCoordinates e (x.1,x.2.val)) (hsymm z hz).symm


/-- Local inverse charts are needed only on an open neighborhood of the zero
section. Shrinking into that locus gives a collar without requiring the full
initial flowout to be a local diffeomorphism. -/
theorem collar_of_boundary_flowout_zero {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold (n+1) a M)
    (W : Set (intrinsicBoundary S × ℝ))
    (hW : ∀ q, W ∈ 𝓝[univ ×ˢ Ici (0 : ℝ)] (q, 0))
    (hWnonneg : W ⊆ univ ×ˢ Ici (0 : ℝ))
    (F : W → M) (hF : Continuous F)
    (hzero : ∀ q, ∀ hq : (q, 0) ∈ W, F ⟨(q, 0), hq⟩ = q.val)
    (hforward : ∀ (e d : ModelChart (n+1) a M),
      e ∈ S.smoothStructure.val → d ∈ S.smoothStructure.val →
      ∀ x : W, x.val.1.val ∈ e.source → F x ∈ d.source →
        LocalCoordinateExtension (⊤ : ℕ∞)
          (fun z : W => boundaryTimeCoordinates e z.val)
          (fun z => (d (F z)).val) x)
    (hlocal : ∀ q (hq : (q, 0) ∈ W), ∃ p : OpenPartialHomeomorph W M,
      (⟨(q, 0), hq⟩ : W) ∈ p.source ∧ EqOn p F p.source ∧
      ∀ (d e : ModelChart (n+1) a M),
        d ∈ S.smoothStructure.val → e ∈ S.smoothStructure.val →
        ∀ y ∈ p.target, y ∈ d.source → (p.symm y).val.1.val ∈ e.source →
          LocalCoordinateExtension (⊤ : ℕ∞) (fun z : M => (d z).val)
            (fun z => boundaryTimeCoordinates e (p.symm z).val) y) :
    Nonempty (SmoothCollar S) := by
  classical
  obtain ⟨B, _, hB⟩ := exists_boundary_smoothManifold S
  have hWzero (q : intrinsicBoundary S) : (q, (0 : ℝ)) ∈ W :=
    mem_of_mem_nhdsWithin (show (q, (0 : ℝ)) ∈ (univ ×ˢ Ici (0 : ℝ)) from
      ⟨mem_univ _, show (0 : ℝ) ≤ 0 from le_rfl⟩) (hW q)
  choose p hp hpeq hpi using (fun q => hlocal q (hWzero q))
  let U : Set W := ⋃ q, (p q).source
  have hU : IsOpen U := isOpen_iUnion (fun q => (p q).open_source)
  have hUzero (q : intrinsicBoundary S) : (⟨(q,0), hWzero q⟩ : W) ∈ U :=
    mem_iUnion.mpr ⟨q, hp q⟩
  have hlocinj : ∀ z ∈ zeroTimeSection W,
      ∃ V : Set W, IsOpen V ∧ z ∈ V ∧ InjOn F V := by
    intro z hz
    let q := z.val.1
    have hzq : z = ⟨(q,0), hWzero q⟩ := by
      apply Subtype.ext
      exact Prod.ext rfl hz
    refine ⟨(p q).source, (p q).open_source, ?_, ?_⟩
    · rw [hzq]
      exact hp q
    · intro x hx y hy hxy
      apply (p q).injOn hx hy
      exact (hpeq q hx).trans (hxy.trans (hpeq q hy).symm)
  obtain ⟨V, hV, hVzero, hinj⟩ := exists_injective_boundary_flowout S W hWzero F hF
    (fun q => hzero q _) hlocinj
  let A : Set W := U ∩ V
  have hA : IsOpen A := hU.inter hV
  obtain ⟨O, hO, hOA⟩ := isOpen_induced_iff.mp hA
  let J := W ∩ O
  have hJ (q : intrinsicBoundary S) : J ∈ 𝓝[univ ×ˢ Ici (0 : ℝ)] (q, 0) := by
    apply inter_mem (hW q)
    apply mem_nhdsWithin_of_mem_nhds
    apply hO.mem_nhds
    have hz : (⟨(q,0), hWzero q⟩ : W) ∈ A := ⟨hUzero q, hVzero rfl⟩
    rwa [← hOA] at hz
  obtain ⟨ε, hε, hpos, htube⟩ := exists_smooth_width B J hJ
  have hεW : variableWidthSet ε ⊆ W := fun x hx => (htube hx).1
  have hxA (x : variableWidthSet ε) : Set.inclusion hεW x ∈ A := by
    rw [← hOA]
    exact (htube x.property).2
  have hcont : Continuous ε := continuous_iff_continuousAt.mpr
    (fun q => ((scalarContDiffAt_iff _ _ _ _).mp (hε q)).1)
  have hopen : IsOpen (Subtype.val ⁻¹' variableWidthSet ε : Set W) := by
    have heq : (Subtype.val ⁻¹' variableWidthSet ε : Set W) =
        {z : W | z.val.2 < ε z.val.1} := by
      ext z
      exact and_iff_right (hWnonneg z.property).2
    rw [heq]
    exact isOpen_lt (continuous_snd.comp continuous_subtype_val)
      (hcont.comp (continuous_fst.comp continuous_subtype_val))
  have hj : Topology.IsOpenEmbedding (Set.inclusion hεW) :=
    Topology.IsOpenEmbedding.inclusion hεW hopen
  let G : variableWidthSet ε → M := F ∘ Set.inclusion hεW
  have hG : Continuous G := hF.comp hj.continuous
  have hGo : IsOpenMap G := isOpenMap_of_open_realization_locally_partialHomeomorph
      F (Set.inclusion hεW) hj.isOpenMap (fun x => by
        obtain ⟨q,hq⟩ := mem_iUnion.mp (hxA x).1
        exact ⟨p q, hq, hpeq q⟩)
  have hGinj : Function.Injective G := by
    intro x y hxy
    exact Subtype.ext (congrArg (fun z : W => z.val)
      (hinj (hxA x).2 (hxA y).2 hxy))
  let N := Set.range G
  have hN : IsOpen N := hGo.isOpen_range
  let e := Equiv.ofInjective G hGinj
  let f : variableWidthSet ε ≃ₜ N := e.toHomeomorphOfContinuousOpen
    (hG.subtype_mk _) (hGo.subtype_mk _)
  have hfF (x : variableWidthSet ε) : (f x).val = F (Set.inclusion hεW x) := rfl
  refine ⟨smoothCollarOfVariableWidthHomeomorph S B hB ε hε hpos N hN f ?_ ?_ ?_⟩
  · intro q
    rw [hfF]
    exact hzero q _
  · intro e d he hd x hx hdx
    have hdx' : F (Set.inclusion hεW x) ∈ d.source := by rwa [← hfF]
    have hs := LocalCoordinateExtension.precomp
      (hforward e d he hd (Set.inclusion hεW x) hx hdx') hj.continuous.continuousAt rfl
    apply hs.congr
    exact Filter.Eventually.of_forall (fun z =>
      congrArg (fun w => (d w).val) (hfF z).symm)
  · intro d e hd he y hdy hey
    let j := Set.inclusion hεW
    let x := j (f.symm y)
    obtain ⟨q,hq⟩ := mem_iUnion.mp (hxA (f.symm y)).1
    have hFx : F x = y.val := by
      change F (Set.inclusion hεW (f.symm y)) = y.val
      rw [← hfF, f.apply_symm_apply]
    have hpx : p q x = y.val := (hpeq q hq).trans hFx
    have hpt : y.val ∈ (p q).target := hpx ▸ (p q).map_source hq
    have hpinv : (p q).symm y.val = x := by rw [← hpx, (p q).left_inv hq]
    have hey' : ((p q).symm y.val).val.1.val ∈ e.source := by rwa [hpinv]
    have hs := hpi q d e hd he y.val hpt hdy hey'
    have hagree : ∀ z, j z ∈ (p q).source → (f z).val = p q (j z) := by
      intro z hz
      exact (hfF z).trans (hpeq q hz).symm
    exact homeomorph_inverse_localCoordinateExtension_of_local_realization
      f j hj.continuous (p q) hagree y hq
      (fun z => (d z).val) (fun z : W => boundaryTimeCoordinates e z.val) hs


/-- An actual smooth inward field supplies a local boundary flow inverse
and a full rectangle of intrinsic one-sided trajectories with which it agrees. -/
theorem exists_local_boundary_flow_chart {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n + 1) .halfSpace M) (B : TangentBundleStructure S)
    (X : SmoothField B) (p : intrinsicBoundary S)
    (e : ModelChart (n + 1) .halfSpace M) (he : e ∈ S.smoothStructure.val)
    (hp : p.val ∈ e.source)
    (hpos : 0 < B.fiberCoordinates.equiv e he p.val hp (X.val p.val) (Fin.last n)) :
    ∃ (b : ℝ) (O : Set (intrinsicBoundary S)) (γ : intrinsicBoundary S → ℝ → M)
      (h : OpenPartialHomeomorph (intrinsicBoundary S × ↥(Ici (0 : ℝ))) M),
      0 < b ∧ IsOpen O ∧ p ∈ O ∧
      (∀ q ∈ O, q.val ∈ e.source) ∧
      (∀ q ∈ O, γ q 0 = q.val ∧ IsOneSidedIntegralCurveOn B X b (γ q)) ∧
      (p, ⟨0, by simp⟩) ∈ h.source ∧
      h.source ⊆ {x | x.1 ∈ O ∧ x.2.val < b} ∧
      EqOn h (fun x => γ x.1 x.2.val) h.source ∧
      h.target ⊆ e.source ∧
      (∀ y ∈ h.target, (h.symm y).1.val ∈ e.source) ∧
      ∀ y ∈ h.target, LocalCoordinateExtension (⊤ : ℕ∞) (fun z => (e z).val)
        (fun z => boundaryTimeCoordinates e ((h.symm z).1, (h.symm z).2.val)) y := by
  classical
  obtain ⟨U, F, hU, hpU, hF, hFpos, hcoeff⟩ :=
    inward_coefficient_extension S B X p.val e he hp hpos
  obtain ⟨b, V, Φ, hb, hV, hpV, hVU, hΦ, hΦzero, hΦder, hsign⟩ :=
    local_inward_coordinate_flow hU hF hFpos hpU
  let O : Set (intrinsicBoundary S) :=
    {q | q.val ∈ e.source ∧ (e q.val).val ∈ V}
  have hOc : IsOpen O := by
    have hpre := e.continuousOn.isOpen_inter_preimage e.open_source
      (hV.preimage continuous_subtype_val)
    exact hpre.preimage continuous_subtype_val
  have hpO : p ∈ O := ⟨hp, hpV⟩
  have hqface (q : intrinsicBoundary S) (hq : q ∈ O) :
      (e q.val).val (Fin.last n) = 0 :=
    (intrinsicBoundary_iff_chart S e he q.val hq.1).mp q.property
  let W : Set (intrinsicBoundary S × ℝ) := O ×ˢ Ico 0 b
  have htime {t : ℝ} (ht : t ∈ Ico 0 b) : t ∈ Ioo (-b) b :=
    ⟨(neg_neg_of_pos hb).trans_le ht.1, ht.2⟩
  have hhalf (w : W) : Φ (w.val.2, (e w.val.1.val).val) ∈ halfSpaceSet (n + 1) :=
    ((hsign _ w.property.1.2 (hqface _ w.property.1) _ (htime w.property.2)).1).mpr
      w.property.2.1
  let z : W → ModelSpace (n + 1) .halfSpace :=
    fun w => ⟨Φ (w.val.2, (e w.val.1.val).val), hhalf w⟩
  have hztarget (w : W) : z w ∈ e.target :=
    (hcoeff _ (hΦder _ w.property.1.2 _ (htime w.property.2)).1 (hhalf w)).1
  have hinitc : Continuous (fun w : W => (e w.val.1.val).val) :=
    continuous_subtype_val.comp
      (e.continuousOn.comp_continuous
        (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val))
        (fun w => w.property.1.1))
  have hzc : Continuous z := by
    apply Continuous.subtype_mk
    exact hΦ.continuousOn.comp_continuous
      ((continuous_snd.comp continuous_subtype_val).prodMk hinitc)
      (fun w => ⟨htime w.property.2, w.property.1.2⟩)
  let g : W → M := fun w => e.symm (z w)
  have hgc : Continuous g := e.symm.continuousOn.comp_continuous hzc hztarget
  let γ : intrinsicBoundary S → ℝ → M := fun q t =>
    if h : (q,t) ∈ W then g ⟨(q,t), h⟩ else q.val
  have hγeq (w : W) : γ w.val.1 w.val.2 = g w := by
    simp only [γ, dite_eq_left w.property]
  have hγc : ContinuousOn (fun x : intrinsicBoundary S × ℝ => γ x.1 x.2) W := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact hgc.congr (fun w => (hγeq w).symm)
  have hγsource (q : intrinsicBoundary S) (hq : q ∈ O) (t : ℝ) (ht : t ∈ Ico 0 b) :
      γ q t ∈ e.source := by
    rw [hγeq ⟨(q,t), hq, ht⟩]
    exact e.map_target (hztarget _)
  have hγcoords (q : intrinsicBoundary S) (hq : q ∈ O) (t : ℝ) (ht : t ∈ Ico 0 b) :
      (e (γ q t)).val = Φ (t,(e q.val).val) := by
    rw [hγeq ⟨(q,t), hq, ht⟩]
    exact congrArg Subtype.val (e.right_inv (hztarget _))
  have hγqc (q : intrinsicBoundary S) (hq : q ∈ O) : ContinuousOn (γ q) (Ico 0 b) :=
    hγc.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ ht => ⟨hq, ht⟩)
  have hγzero (q : intrinsicBoundary S) (hq : q ∈ O) : γ q 0 = q.val := by
    rw [hγeq ⟨(q,0), hq, le_rfl, hb⟩]
    change e.symm (z ⟨(q,0), hq, le_rfl, hb⟩) = q.val
    have hz0 : z ⟨(q,0), hq, le_rfl, hb⟩ = e q.val :=
      Subtype.ext (hΦzero _ hq.2)
    rw [hz0, e.left_inv hq.1]
  have hγint (q : intrinsicBoundary S) (hq : q ∈ O) :
      IsOneSidedIntegralCurveOn B X b (γ q) := by
    refine ⟨hγqc q hq, ?_⟩
    apply oneSided_derivative_of_chart B X (hγqc q hq) e he (hγsource q hq)
      (fun t => Φ (t,(e q.val).val)) (fun t ht => (hγcoords q hq t ht).symm)
    intro t ht
    have hder := (hΦder _ hq.2 t (htime ht)).2
    have hco := (hcoeff _ (hΦder _ hq.2 t (htime ht)).1
      (hhalf ⟨(q,t), hq, ht⟩)).2
    have hback : e.symm (z ⟨(q,t), hq, ht⟩) = γ q t := (hγeq _).symm
    change F (Φ (t,(e q.val).val)) = TangentBundle.chartFiber B e he
      ⟨e.symm (z ⟨(q,t), hq, ht⟩), X.val (e.symm (z ⟨(q,t), hq, ht⟩))⟩ at hco
    rw [hback, TangentBundle.chartFiber_eq S B e he _ (hγsource q hq t ht)] at hco
    exact hco ▸ hder
  obtain ⟨C, _, hfacecharts⟩ := exists_boundary_smoothManifold S
  obtain ⟨bface, _, hbface⟩ := hfacecharts e he ⟨⟨p, hp⟩⟩
  have hpface : (e p.val).val (Fin.last n) = 0 := hqface p hpO
  have ht0 : HasDerivAt (fun t => Φ (t, (e p.val).val)) (F (e p.val).val) 0 := by
    have h := (hΦder _ hpV 0 ⟨neg_neg_of_pos hb, hb⟩).2
    rwa [hΦzero _ hpV] at h
  obtain ⟨g, hgp, hgapply, hgforward, hginverse⟩ := local_face_flow_inverse Φ hb V hV
    hΦ hΦzero (e p.val) hpV hpface (F (e p.val).val)
    (ne_of_gt (hFpos _ hpU)) ht0 (fun z hz hf t ht => (hsign z hz hf t ht).1)
  have hgzero : g (e p.val) = e p.val := by
    apply Subtype.ext
    rw [hgapply _ hgp, hpface]
    have hproj : faceProjection (e p.val).val = (e p.val).val := by
      rw [faceProjection_apply, ← hpface, Fin.snoc_init_self]
    rw [hproj]
    exact hΦzero _ hpV
  let h := boundaryFlowChartIn S e bface g O hOc b
  have hsource : h.source ⊆ {x | x.1 ∈ O ∧ x.2.val < b} := fun _ hx => hx.2
  have hagree : EqOn h (fun x => γ x.1 x.2.val) h.source := by
    intro x hx
    have hxbase : x ∈ (boundaryFlowChart S e bface g).source := hx.1
    have hxtime : x.2.val ∈ Ico 0 b := ⟨mem_Ici.mp x.2.property, hx.2.2⟩
    have hxe : h x ∈ e.source := by
      change e.symm (g (boundaryTimeChart S bface x)) ∈ e.source
      exact e.map_target hxbase.2
    apply e.injOn hxe (hγsource x.1 hx.2.1 x.2.val hxtime)
    apply Subtype.ext
    change (e (boundaryFlowChart S e bface g x)).val = (e (γ x.1 x.2.val)).val
    rw [boundaryFlowChart_apply_coordinates S e he bface hbface g Φ hgapply x hxbase,
      hγcoords x.1 hx.2.1 x.2.val hxtime]
  refine ⟨b, O, γ, h, hb, hOc, hpO, (fun _ hq => hq.1),
    (fun q hq => ⟨hγzero q hq, hγint q hq⟩),
    boundaryFlowChartIn_zero_mem S e he bface hbface g O hOc b hb p hp hpO hgp hgzero,
    hsource, hagree, ?_, ?_, ?_⟩
  · intro y hy
    exact hy.1.1
  · intro y hy
    exact ((h.map_target hy).2.1).1
  · intro y hy
    exact boundaryFlowChartIn_inverse_smooth S e bface hbface g hginverse O hOc b y hy

/-- The one-sided flow of a globally inward field gives a collar in every
positive-dimensional ordinary half-space manifold. -/
theorem collar_exists_positive_halfSpace {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n + 1) .halfSpace M) : Nonempty (SmoothCollar S) := by
  classical
  obtain ⟨B⟩ := TangentBundle.exists_bundle S
  obtain ⟨X, hin⟩ := exists_inward_field S B
  obtain ⟨W, F, hWnonneg, hWopen, hWzero, hWnhds, hFc, hFzero, hFforward,
    hFcurves, hsegments⟩ := exists_boundary_flowout S B X hin
  apply collar_of_boundary_flowout_zero S W hWnhds hWnonneg F hFc hFzero hFforward
  intro q hqW
  obtain ⟨e, he, hqe⟩ := S.smoothStructure.property.1.1 q.val
  obtain ⟨b, O, γ, p, hb, hO, hqO, hOe, hγ, hpzero, hpsource, hpformula,
    hptarget, hpinitsource, hpinv⟩ := exists_local_boundary_flow_chart
      S B X q e he hqe (hin q e he hqe)
  let x₀ : W := ⟨(q,0), hqW⟩
  have hp₀ : nonnegativeDomainMap W hWnonneg x₀ ∈ p.source := by
    simpa only [nonnegativeDomainMap, x₀] using hpzero
  obtain ⟨pW, hpWzero, hpWsource, hpWformula, hpWtarget, hpWsymm⟩ :=
    pullback_boundary_time_chart W hWnonneg hWopen x₀ p hp₀
  have hpF := boundary_flowout_chart_agreement S B X W hWnonneg F hsegments hFcurves
    O b hb γ (fun r hr => (hγ r hr).2) (fun r hr => (hγ r hr).1)
    p (fun x hx => hpsource hx) (fun x hx => hpformula hx)
  refine ⟨pW, hpWzero, ?_, ?_⟩
  · intro x hx
    exact (hpWformula x).trans (hpF x ((hpWsource x).mp hx))
  · intro d f hd hf y hy hyd hyf
    have hylocal : LocalCoordinateExtension (⊤ : ℕ∞) (fun z => (e z).val)
        (fun z => boundaryTimeCoordinates e (pW.symm z).val) y :=
      pullback_boundary_time_chart_inverse_smooth e W hWnonneg p pW hpWsymm
        (fun z => (e z).val) y hy (hpinv y (hpWtarget hy))
    have hyinit : (pW.symm y).val.1.val ∈ e.source := by
      change (nonnegativeDomainMap W hWnonneg (pW.symm y)).1.val ∈ e.source
      rw [hpWsymm y hy]
      exact hpinitsource y (hpWtarget hy)
    exact boundaryFlowout_inverse_changeCharts S pW Subtype.val y hy
      continuousAt_subtype_val e e f d he he hf hd hyinit hyf
      (hptarget (hpWtarget hy)) hyd hylocal

/-- Every ordinary smooth manifold has a collar of its entire intrinsic boundary. -/
theorem collar_exists : Specs.SmoothManifolds.Ch06.Collar.collar_existsType.{u} :=
  collar_exists_iff_positive_halfSpace.mpr (fun S => collar_exists_positive_halfSpace S)


end SmoothManifolds.Collars
