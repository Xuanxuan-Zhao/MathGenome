import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch08.Frobenius
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.MapClasses
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch08.DistributionTests
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch06.CommutingFields
import Mathlib.LinearAlgebra.Pi
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! The local Frobenius theorem, paper.tex 1637--1648.
Involutivity is equivalent to adapted coordinates, and every coordinate slice
is an integral submanifold with its inherited topology. The proof uses local
frames, smooth normalization, and simultaneous coordinates for commuting fields.
All tangent fibers and differentials are the original intrinsic objects.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace SmoothManifolds.Frobenius
open ModelData AtlasData MapData TangentData DifferentialData TangentBundleData
  BundleOperationsData CovectorData DistributionData FrobeniusData FiniteRegularityData LieBracketData
  Set Filter
open scoped Topology
universe u

@[simp] theorem mem_coordinatePlane {n k : ℕ} (v : Euclidean n) :
    v ∈ CoordinatePlane k ↔ ∀ j : Fin n, k ≤ j.val → v j = 0 := Iff.rfl

@[simp] theorem coordinatePlane_zero (n : ℕ) :
    @CoordinatePlane n 0 = ⊥ := by
  ext v
  simp only [mem_coordinatePlane, Submodule.mem_bot]
  constructor
  · intro h
    ext j
    exact h j (Nat.zero_le _)
  · intro h j _
    rw [h]
    rfl

@[simp] theorem coordinatePlane_full (n : ℕ) :
    @CoordinatePlane n n = ⊤ := by
  ext v
  simp only [mem_coordinatePlane, Submodule.mem_top, iff_true]
  intro j hj
  omega

/-- A coefficient that vanishes as a germ has zero differential component.
The use of the chart's actual relatively open model domain also works at a
boundary, although only the Euclidean instance is needed below. -/
theorem coordinateDerivative_component_zero
    {n m : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (e : ModelChart n a M) (g : M → Euclidean m) (p : M)
    (hp : p ∈ e.source) (L : Euclidean n →L[ℝ] Euclidean m)
    (hL : HasCoordinateDerivative e g p L) (j : Fin m)
    (hg : ∀ᶠ q in 𝓝 p, g q j = 0) (v : Euclidean n) : L v j = 0 := by
  obtain ⟨F, hF, hFg⟩ := hL
  have hzero : ∀ᶠ q in 𝓝 p, F (e q).val j = 0 := by
    filter_upwards [hFg, hg] with q hq hq0
    rw [hq, hq0]
  obtain ⟨V, hVsub, hV, hpV⟩ := mem_nhds_iff.mp hzero
  let s : Set (ModelSpace n a) := e.target ∩ e.symm ⁻¹' V
  have hs : IsOpen s := e.symm.isOpen_inter_preimage hV
  have heps : e p ∈ s := ⟨e.map_source hp, by
    change e.symm (e p) ∈ V
    rwa [e.left_inv hp]⟩
  have hEq : EqOn (fun x => F x j) (fun _ => (0 : ℝ)) (Subtype.val '' s) := by
    rintro _ ⟨x, hx, rfl⟩
    have hh := hVsub hx.2
    change F (e (e.symm x)).val j = 0 at hh
    simpa only [e.right_inv hx.1] using hh
  have hpoint : (e p).val ∈ Subtype.val '' s := ⟨e p, heps, rfl⟩
  have hd := (ContinuousLinearMap.proj j).hasFDerivAt.comp (e p).val hF
  have heq := (uniqueDiffOn_modelDomain hs).eq hpoint
    hd.hasFDerivWithinAt
    ((hasFDerivAt_const (0 : ℝ) (e p).val).hasFDerivWithinAt.congr' hEq hpoint)
  exact congrArg (fun A : Euclidean n →L[ℝ] ℝ => A v) heq

/-- The coordinate-plane distribution is closed under the actual local
coordinate commutator. No extension to global vector fields is required. -/
theorem local_bracket_mem_of_adapted
    {n k : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {C : CotangentBundle S}
    (D : SmoothDistribution C k) (e : ModelChart n .euclidean M)
    (he : e ∈ S.smoothStructure.val) (hadapt : IsAdaptedChart D e he)
    (U : Set M) (hU : IsOpen U) (X Y Z : VectorFieldData.Section S)
    (hbr : HasLocalBracket C.tangent U X Y Z)
    (hX : ValuesIn D U X) (hY : ValuesIn D U Y)
    (p : M) (hp : p ∈ U) (hpe : p ∈ e.source) : Z p ∈ D.fiber p := by
  apply (hadapt p hpe (Z p)).mpr
  intro j hj
  obtain ⟨L, K, hL, hK⟩ := hbr.1 e he p hp hpe
  have hzX : ∀ᶠ q in 𝓝 p, coefficients C.tangent X e he q j = 0 := by
    filter_upwards [hU.mem_nhds hp, e.open_source.mem_nhds hpe] with q hq hqe
    simpa only [coefficients, dite_eq_left hqe] using
      ((hadapt q hqe (X q)).mp (hX q hq)) j hj
  have hzY : ∀ᶠ q in 𝓝 p, coefficients C.tangent Y e he q j = 0 := by
    filter_upwards [hU.mem_nhds hp, e.open_source.mem_nhds hpe] with q hq hqe
    simpa only [coefficients, dite_eq_left hqe] using
      ((hadapt q hqe (Y q)).mp (hY q hq)) j hj
  have hLj (v : Euclidean n) : L v j = 0 :=
    coordinateDerivative_component_zero e _ p hpe L hL j hzX v
  have hKj (v : Euclidean n) : K v j = 0 :=
    coordinateDerivative_component_zero e _ p hpe K hK j hzY v
  have hformula := hbr.2 e he p hp hpe L K hL hK j
  simpa only [coefficients, dite_eq_left hpe, hLj, hKj, mul_zero, sub_self,
    Finset.sum_const_zero] using hformula

/-- The converse half of Frobenius follows directly on every smaller open
field domain, hence respects the local quantifiers in IsInvolutive. -/
theorem involutive_of_adapted_coordinates
    {n k : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {C : CotangentBundle S}
    (D : SmoothDistribution C k) (h : HasAdaptedCoordinates D) : IsInvolutive D := by
  intro U hU X Y Z _hX _hY hbr hXD hYD p hp
  obtain ⟨e, he, hpe, hadapt⟩ := h p
  exact local_bracket_mem_of_adapted D e he hadapt U hU X Y Z hbr hXD hYD p hp hpe

/-- The longitudinal coordinate projection, with no discarded normal directions. -/
def longitudinalProjection {n k : ℕ} (hk : k ≤ n) : Euclidean n →L[ℝ] Euclidean k :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj ⟨i.val, by omega⟩

/-- Inclusion of the first k coordinates in the n-dimensional model. -/
def longitudinalInclusion {n k : ℕ} (_hk : k ≤ n) : Euclidean k →L[ℝ] Euclidean n :=
  ContinuousLinearMap.pi fun j =>
    if h : j.val < k then ContinuousLinearMap.proj ⟨j.val, h⟩ else 0

@[simp] theorem longitudinalProjection_inclusion {n k : ℕ} (hk : k ≤ n)
    (x : Euclidean k) : longitudinalProjection hk (longitudinalInclusion hk x) = x := by
  ext i
  simp [longitudinalProjection, longitudinalInclusion, i.isLt]

/-- This identifies the zero-transverse coordinate description with the actual
span of the u-coordinate vectors. -/
theorem range_longitudinalInclusion {n k : ℕ} (hk : k ≤ n) :
    LinearMap.range (longitudinalInclusion hk).toLinearMap = CoordinatePlane k := by
  ext v
  constructor
  · rintro ⟨x, rfl⟩ j hj
    simp [longitudinalInclusion, show ¬ j.val < k by omega]
  · intro hv
    refine ⟨longitudinalProjection hk v, ?_⟩
    ext j
    by_cases hj : j.val < k
    · simp [longitudinalInclusion, longitudinalProjection, hj]
    · simpa [longitudinalInclusion, hj] using (hv j (by omega)).symm

/-- The transverse map has exactly the coordinate plane as its kernel. -/
theorem transverseCoordinates_eq_zero_iff {n k : ℕ} (v : Euclidean n) :
    transverseCoordinates k v = 0 ↔ v ∈ CoordinatePlane k := by
  constructor
  · intro hv j hj
    have h := congrFun hv (⟨j.val-k, by omega⟩ : Fin (n-k))
    simpa [transverseCoordinates, Nat.add_sub_cancel' hj] using h
  · intro hv
    ext j
    exact hv ⟨k+j.val, by omega⟩ (by change k ≤ k+j.val; omega)

@[simp] theorem transverseCoordinates_zero_rank {n : ℕ} (x : Euclidean n) :
    transverseCoordinates 0 x = x := by
  ext j
  simp [transverseCoordinates]

@[simp] theorem coordinateSlice_zero_rank {n : ℕ} {M : Type u} [TopologicalSpace M]
    (e : ModelChart n .euclidean M) (p : M) (hp : p ∈ e.source) :
    coordinateSlice e 0 (e p).val = {p} := by
  ext q
  simp only [coordinateSlice, mem_ofPred_eq, transverseCoordinates_zero_rank, mem_singleton_iff]
  constructor
  · rintro ⟨hq, heq⟩
    exact e.injOn hq hp (Subtype.ext heq)
  · rintro rfl
    exact ⟨hp, rfl⟩

@[simp] theorem coordinateSlice_full_rank {n : ℕ} {M : Type u} [TopologicalSpace M]
    (e : ModelChart n .euclidean M) (z : Euclidean (n-n)) :
    coordinateSlice e n z = e.source := by
  ext q
  simp only [coordinateSlice, mem_ofPred_eq, and_iff_left_iff_imp]
  intro _
  funext j
  exact (Nat.not_lt_zero j.val (by simpa using j.isLt)).elim

/-- A zero-dimensional distribution is adapted to every chart. -/
theorem adapted_zero_rank
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {C : CotangentBundle S}
    (D : SmoothDistribution C 0) (e : ModelChart n .euclidean M)
    (he : e ∈ S.smoothStructure.val) : IsAdaptedChart D e he := by
  intro q hq v
  rw [(DistributionTests.extreme_ranks (C := C)).1 D |>.2 q, coordinatePlane_zero]
  simp only [Submodule.mem_bot, LinearEquiv.map_eq_zero_iff]

/-- A full-rank distribution is adapted to every chart. -/
theorem adapted_full_rank
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {C : CotangentBundle S}
    (D : SmoothDistribution C n) (e : ModelChart n .euclidean M)
    (he : e ∈ S.smoothStructure.val) : IsAdaptedChart D e he := by
  intro q hq v
  rw [(DistributionTests.extreme_ranks (C := C)).2 D |>.2 q, coordinatePlane_full]
  simp

/-- Insert fixed transverse coordinates, retaining the k longitudinal variables. -/
def sliceInsertion {n k : ℕ} (hk : k ≤ n) (z : Euclidean (n-k))
    (x : Euclidean k) : Euclidean n := fun j =>
  if h : j.val < k then x ⟨j.val, h⟩ else z ⟨j.val-k, by omega⟩

@[simp] theorem longitudinalProjection_sliceInsertion {n k : ℕ} (hk : k ≤ n)
    (z : Euclidean (n-k)) (x : Euclidean k) :
    longitudinalProjection hk (sliceInsertion hk z x) = x := by
  ext i
  simp [longitudinalProjection, sliceInsertion, i.isLt]

@[simp] theorem transverseCoordinates_sliceInsertion {n k : ℕ} (hk : k ≤ n)
    (z : Euclidean (n-k)) (x : Euclidean k) :
    transverseCoordinates k (sliceInsertion hk z x) = z := by
  ext j
  simp [transverseCoordinates, sliceInsertion, show ¬ k+j.val < k by omega]

/-- The chart coordinates of any point of the slice are reconstructed uniquely. -/
theorem sliceInsertion_projection {n k : ℕ} (hk : k ≤ n)
    (z : Euclidean (n-k)) (x : Euclidean n)
    (hx : transverseCoordinates k x = z) :
    sliceInsertion hk z (longitudinalProjection hk x) = x := by
  ext j
  by_cases hj : j.val < k
  · simp [sliceInsertion, longitudinalProjection, hj]
  · have h := congrFun hx (⟨j.val-k, by omega⟩ : Fin (n-k))
    simp only [transverseCoordinates, Nat.add_sub_cancel' (show k ≤ j.val by omega)] at h
    simpa only [sliceInsertion, dite_eq_right hj] using h.symm

theorem sliceInsertion_eq {n k : ℕ} (hk : k ≤ n)
    (z : Euclidean (n-k)) (x : Euclidean k) :
    sliceInsertion hk z x = longitudinalInclusion hk x + sliceInsertion hk z 0 := by
  ext j
  by_cases hj : j.val < k <;> simp [sliceInsertion, longitudinalInclusion, hj]

theorem contDiff_sliceInsertion {n k : ℕ} (hk : k ≤ n) (z : Euclidean (n-k)) :
    ContDiff ℝ (⊤ : ℕ∞) (sliceInsertion hk z) := by
  have h : sliceInsertion hk z = fun x =>
      longitudinalInclusion hk x + sliceInsertion hk z 0 := funext (sliceInsertion_eq hk z)
  rw [h]
  exact (longitudinalInclusion hk).contDiff.add contDiff_const

theorem hasFDerivAt_sliceInsertion {n k : ℕ} (hk : k ≤ n)
    (z : Euclidean (n-k)) (x : Euclidean k) :
    HasFDerivAt (sliceInsertion hk z) (longitudinalInclusion hk) x := by
  have h := ((longitudinalInclusion hk).hasFDerivAt (x := x)).add_const (sliceInsertion hk z 0)
  exact h.congr_of_eventuallyEq (Eventually.of_forall (sliceInsertion_eq hk z))

/-- The whole Euclidean space as the project's model subtype. -/
def modelPoint {d : ℕ} (x : Euclidean d) : ModelSpace d .euclidean := ⟨x, mem_univ x⟩

theorem continuous_modelPoint (d : ℕ) :
    Continuous (@modelPoint d) := continuous_id.subtype_mk _

/-- The set of longitudinal coordinates whose insertion lies in the chart. -/
def sliceParameterDomain {n k : ℕ} {M : Type u} [TopologicalSpace M]
    (e : ModelChart n .euclidean M) (hk : k ≤ n) (z : Euclidean (n-k)) :
    Set (Euclidean k) := (fun x => modelPoint (sliceInsertion hk z x)) ⁻¹' e.target

theorem sliceParameterDomain_isOpen {n k : ℕ} {M : Type u} [TopologicalSpace M]
    (e : ModelChart n .euclidean M) (hk : k ≤ n) (z : Euclidean (n-k)) :
    IsOpen (sliceParameterDomain e hk z) :=
  e.open_target.preimage ((continuous_modelPoint n).comp (contDiff_sliceInsertion hk z).continuous)

/-- A full chart on a nonempty slice, using its subspace topology. -/
def sliceChart {n k : ℕ} {M : Type u} [TopologicalSpace M]
    (e : ModelChart n .euclidean M) (hk : k ≤ n) (z : Euclidean (n-k))
    [Nonempty (coordinateSlice e k z)] :
    ModelChart k .euclidean (coordinateSlice e k z) := by
  classical
  let f : coordinateSlice e k z → ModelSpace k .euclidean :=
    fun q => modelPoint (longitudinalProjection hk (e q.val).val)
  let g : ModelSpace k .euclidean → coordinateSlice e k z := fun x =>
    if h : x.val ∈ sliceParameterDomain e hk z then
      ⟨e.symm (modelPoint (sliceInsertion hk z x.val)), e.map_target h, by
        rw [e.right_inv h]
        exact transverseCoordinates_sliceInsertion hk z x.val⟩
    else Classical.choice inferInstance
  have hf (q : coordinateSlice e k z) : (f q).val ∈ sliceParameterDomain e hk z := by
    change modelPoint (sliceInsertion hk z (longitudinalProjection hk (e q.val).val)) ∈ e.target
    rw [sliceInsertion_projection hk z _ q.property.2]
    exact e.map_source q.property.1
  have hg (x : ModelSpace k .euclidean) (hx : x.val ∈ sliceParameterDomain e hk z) :
      (g x).val = e.symm (modelPoint (sliceInsertion hk z x.val)) := by
    simp only [g, dite_eq_left hx]
  exact {
    toFun := f
    invFun := g
    source := univ
    target := Subtype.val ⁻¹' sliceParameterDomain e hk z
    map_source' := fun q _ => hf q
    map_target' := fun _ _ => mem_univ _
    left_inv' := by
      intro q _
      apply Subtype.ext
      rw [hg (f q) (hf q)]
      change e.symm (modelPoint (sliceInsertion hk z (longitudinalProjection hk (e q.val).val))) = q.val
      rw [sliceInsertion_projection hk z _ q.property.2]
      exact e.left_inv q.property.1
    right_inv' := by
      intro x hx
      apply Subtype.ext
      change longitudinalProjection hk (e (g x).val).val = x.val
      rw [hg x hx, e.right_inv hx]
      exact longitudinalProjection_sliceInsertion hk z x.val
    open_source := isOpen_univ
    open_target := (sliceParameterDomain_isOpen e hk z).preimage continuous_subtype_val
    continuousOn_toFun := by
      apply Continuous.continuousOn
      apply (continuous_modelPoint k).comp
      apply (longitudinalProjection hk).continuous.comp
      apply continuous_subtype_val.comp
      exact e.continuousOn.comp_continuous continuous_subtype_val
        (fun q => q.property.1)
    continuousOn_invFun := by
      apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
      apply ContinuousOn.congr _ hg
      apply e.symm.continuousOn.comp
        (((continuous_modelPoint n).comp (contDiff_sliceInsertion hk z).continuous).comp
          continuous_subtype_val).continuousOn
      exact fun _ hx => hx }

@[simp] theorem sliceChart_source {n k : ℕ} {M : Type u} [TopologicalSpace M]
    (e : ModelChart n .euclidean M) (hk : k ≤ n) (z : Euclidean (n-k))
    [Nonempty (coordinateSlice e k z)] : (sliceChart e hk z).source = univ := rfl

@[simp] theorem sliceChart_apply {n k : ℕ} {M : Type u} [TopologicalSpace M]
    (e : ModelChart n .euclidean M) (hk : k ≤ n) (z : Euclidean (n-k))
    [Nonempty (coordinateSlice e k z)] (q : coordinateSlice e k z) :
    (sliceChart e hk z q).val = longitudinalProjection hk (e q.val).val := rfl

/-- A full chart supplies a genuine maximal smooth structure on the existing
Hausdorff, second countable topology. -/
theorem smoothManifold_of_fullChart {d : ℕ} {P : Type u} [TopologicalSpace P]
    [T2Space P] [SecondCountableTopology P]
    (c : ModelChart d .euclidean P) (hc : c.source = univ) :
    ∃ T : SmoothManifold d .euclidean P, c ∈ T.smoothStructure.val := by
  have hself : ContDiffCompatible (⊤ : ℕ∞) c c := by
    apply contDiffCompatible_of_germs <;> intro p _ _
    all_goals exact LocalCoordinateExtension.self _ (fun q => (c q).val) p
  have hA : IsContDiffAtlas (⊤ : ℕ∞) ({c} : Set (ModelChart d .euclidean P)) := by
    refine ⟨fun p => ⟨c, mem_singleton c, by rw [hc]; trivial⟩, ?_⟩
    intro e he f hf
    simpa only [mem_singleton_iff.mp he, mem_singleton_iff.mp hf] using hself
  let T : SmoothManifold d .euclidean P := {
    topologicalManifold := {
      hausdorff := inferInstance
      secondCountable := inferInstance
      atlas := {c}
      covers := hA.1 }
    smoothStructure := ⟨maximalExtension (⊤ : ℕ∞) {c}, maximalExtension_isMaximal hA⟩ }
  exact ⟨T, subset_maximalExtension hA (mem_singleton c)⟩

/-- The empty manifold is permitted in every dimension. -/
theorem smoothManifold_of_isEmpty {d : ℕ} {P : Type u} [TopologicalSpace P]
    [IsEmpty P] : Nonempty (SmoothManifold d .euclidean P) := by
  have hA : IsContDiffAtlas (⊤ : ℕ∞) (∅ : Set (ModelChart d .euclidean P)) :=
    ⟨fun p => isEmptyElim p, by simp⟩
  exact ⟨{
    topologicalManifold := {
      hausdorff := inferInstance
      secondCountable := inferInstance
      atlas := ∅
      covers := hA.1 }
    smoothStructure := ⟨maximalExtension (⊤ : ℕ∞) ∅, maximalExtension_isMaximal hA⟩ }⟩

/-- A chart slice has the intrinsic smooth manifold and the full differential
image prescribed by an adapted chart, with its existing subspace topology. -/
theorem integral_slice_of_adapted
    {n k : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {C : CotangentBundle S}
    (D : SmoothDistribution C k) (e : ModelChart n .euclidean M)
    (he : e ∈ S.smoothStructure.val) (hadapt : IsAdaptedChart D e he)
    (z : Euclidean (n-k)) : IsIntegralSlice D (coordinateSlice e k z) := by
  classical
  let A := coordinateSlice e k z
  cases isEmpty_or_nonempty A with
  | inl hempty =>
    let := hempty
    obtain ⟨T⟩ := smoothManifold_of_isEmpty (d := k) (P := A)
    exact ⟨T, (fun p => isEmptyElim p), (fun p => isEmptyElim p),
      (fun p => isEmptyElim p), (fun p => isEmptyElim p), (fun p => isEmptyElim p)⟩
  | inr hnonempty =>
    let := hnonempty
    let := S.topologicalManifold.hausdorff
    let := S.topologicalManifold.secondCountable
    let p₀ : A := Classical.choice hnonempty
    have hk : k ≤ n := (D.smooth p₀.val).1
    let c : ModelChart k .euclidean A := sliceChart e hk z
    obtain ⟨T, hc⟩ := smoothManifold_of_fullChart c (sliceChart_source e hk z)
    have hcoord (q : A) : sliceInsertion hk z (c q).val = (e q.val).val := by
      exact sliceInsertion_projection hk z _ q.property.2
    have hsmooth : IsSmoothMap T S (Subtype.val : A → M) := by
      intro p
      apply (manifoldContDiffAt_iff_oneChart (⊤ : ℕ∞) _ _
        T.smoothStructure.property.1 S.smoothStructure.property.1 _ p).mpr
      exact ⟨continuous_subtype_val.continuousAt, c, hc, e, he, mem_univ p, p.property.1,
        univ, isOpen_univ, mem_univ _, sliceInsertion hk z,
        (contDiff_sliceInsertion hk z).contDiffOn, Eventually.of_forall hcoord⟩
    let L := fun p : A => differential T S Subtype.val hsmooth p
    have hL : ∀ p : A, IsDifferential T S Subtype.val p (L p) :=
      fun p => differential_spec T S Subtype.val hsmooth p
    have hlin (p : A) : Function.Injective (L p) ∧ LinearMap.range (L p) = D.fiber p.val := by
      obtain ⟨E, hE⟩ := FiniteRegularity.exists_smooth_chart_coordinates T p c hc (mem_univ p)
      let F := C.tangent.fiberCoordinates.equiv e he p.val p.property.1
      have hsquare (v : TangentSpace T p) : F (L p v) = longitudinalInclusion hk (E v) := by
        have h := differential_jacobian T S Subtype.val hsmooth p (L p) (hL p)
          c e hc he (mem_univ p) p.property.1 E F hE
          (C.tangent.fiberCoordinates.isCoordinates e he p.val p.property.1)
          univ (sliceInsertion hk z) isOpen_univ (mem_univ _)
          (contDiff_sliceInsertion hk z).contDiffOn (Eventually.of_forall hcoord) v
        rwa [(hasFDerivAt_sliceInsertion hk z (c p).val).fderiv] at h
      constructor
      · intro v w hvw
        apply E.injective
        have h := congrArg (fun x => longitudinalProjection hk (F x)) hvw
        simpa only [hsquare, longitudinalProjection_inclusion] using h
      · ext v
        constructor
        · rintro ⟨w, rfl⟩
          apply (hadapt p.val p.property.1 (L p w)).mpr
          rw [hsquare]
          rw [← range_longitudinalInclusion hk]
          exact ⟨E w, rfl⟩
        · intro hv
          have hplane := (hadapt p.val p.property.1 v).mp hv
          rw [← range_longitudinalInclusion hk] at hplane
          obtain ⟨x, hx⟩ := hplane
          refine ⟨E.symm x, F.injective ?_⟩
          rw [hsquare, LinearEquiv.apply_symm_apply]
          exact hx
    refine ⟨T, hsmooth, ?_, L, hL, fun p => (hlin p).2⟩
    intro p
    exact (MapClasses.smooth_tangent_invariants T S Subtype.val hsmooth p (L p) (hL p)).2.1.mpr
      (hlin p).1

/-- Restricting a chart to an open neighborhood preserves membership in the
original maximal smooth atlas. -/
theorem chart_restr_mem {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (e : ModelChart n .euclidean M)
    (he : e ∈ S.smoothStructure.val) (U : Set M) :
    e.restr U ∈ S.smoothStructure.val := by
  let A := S.smoothStructure.val
  have hmax : maximalExtension (⊤ : ℕ∞) A = A :=
    S.smoothStructure.property.2 _ (maximalExtension_isContDiffAtlas S.smoothStructure.property.1)
      (subset_maximalExtension S.smoothStructure.property.1)
  change e.restr U ∈ A
  rw [← hmax]
  intro d hd
  apply contDiffCompatible_of_germs
  · intro q hq hqd
    exact chartContDiffAt_of_compatible (S.smoothStructure.property.1.2 e he d hd) hq.1 hqd
  · intro q hqd hq
    exact chartContDiffAt_of_compatible (S.smoothStructure.property.1.2 d hd e he) hqd hq.1

/-- Restriction changes no coordinate germ and therefore no tangent coordinate. -/
theorem fiberCoordinates_restr {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (B : TangentBundleStructure S)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    (U : Set M) (q : M) (hq : q ∈ (e.restr U).source) :
    B.fiberCoordinates.equiv (e.restr U) (chart_restr_mem S e he U) q hq =
      B.fiberCoordinates.equiv e he q hq.1 := by
  apply TangentBundle.chartCoordinates_unique
    (B.fiberCoordinates.isCoordinates (e.restr U) (chart_restr_mem S e he U) q hq)
  exact B.fiberCoordinates.isCoordinates e he q hq.1

/-- The coordinate plane is literally the span of the first k coordinate fields. -/
theorem coordinatePlane_eq_span {n k : ℕ} (hk : k ≤ n) :
    CoordinatePlane k = Submodule.span ℝ (Set.range
      (fun i : Fin k => Pi.single (⟨i.val, by omega⟩ : Fin n) (1 : ℝ))) := by
  have himage : (longitudinalInclusion hk).toLinearMap ''
      Set.range (Pi.basisFun ℝ (Fin k)) = Set.range
      (fun i : Fin k => Pi.single (⟨i.val, by omega⟩ : Fin n) (1 : ℝ)) := by
    rw [← Set.range_comp']
    congr 1
    funext i
    ext j
    by_cases hj : j.val < k
    · simp [longitudinalInclusion, Pi.basisFun_apply, hj, Pi.single_apply,
        show (⟨j.val, hj⟩ : Fin k) = i ↔ j = (⟨i.val, by omega⟩ : Fin n) by
          simp only [Fin.ext_iff]]
    · have hji : j ≠ (⟨i.val, by omega⟩ : Fin n) := by
        intro h
        have hval : j.val = i.val := congrArg Fin.val h
        have := i.isLt
        omega
      simp [longitudinalInclusion, hj, Pi.basisFun_apply, hji]
  rw [← range_longitudinalInclusion hk, ← Submodule.map_top,
    ← (Pi.basisFun ℝ (Fin k)).span_eq, Submodule.map_span, himage]

/-- A locally spanning commuting family is enough for the forward coordinate
construction. The neighborhood of spanning may be arbitrarily small; neither
completeness nor global spanning enters this reduction. -/
theorem adapted_chart_of_commuting_frame
    {n k : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {C : CotangentBundle S}
    (D : SmoothDistribution C k)
    (b : VectorFieldData.SmoothField C.tangent → VectorFieldData.SmoothField C.tangent →
      VectorFieldData.SmoothField C.tangent) (hb : BracketOperation b)
    (X : Fin k → VectorFieldData.SmoothField C.tangent)
    (p : M) (hk : k ≤ n)
    (hlin : LinearIndependent ℝ (fun i => (X i).val p))
    (U : Set M) (hU : IsOpen U) (hpU : p ∈ U)
    (hspan : ∀ q ∈ U, Submodule.span ℝ (Set.range (fun i => (X i).val q)) = D.fiber q)
    (hcomm : ∀ i j q, q ∈ U → (b (X i) (X j)).val q = 0) :
    ∃ (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val),
      p ∈ e.source ∧ IsAdaptedChart D e he := by
  obtain ⟨e, he, hp, hX⟩ := CommutingFields.simultaneous_coordinates S C.tangent b hb X p hk hlin
    ⟨U, hU, hpU, hcomm⟩
  let d := e.restr U
  have hd := chart_restr_mem S e he U
  refine ⟨d, hd, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.restr_source']
    exact ⟨hp, hpU⟩
    exact hU
  · intro q hq v
    have hqU : q ∈ U := (hU.interior_eq ▸ hq.2)
    rw [fiberCoordinates_restr C.tangent e he U q hq]
    let E := C.tangent.fiberCoordinates.equiv e he q hq.1
    have hmap : (D.fiber q).map E.toLinearMap = CoordinatePlane k := by
      rw [← hspan q hqU, Submodule.map_span, ← Set.range_comp', coordinatePlane_eq_span hk]
      congr 2
      funext i
      exact hX q hq.1 i
    constructor
    · intro hv
      rw [← hmap]
      exact ⟨v, hv, rfl⟩
    · intro hv
      rw [← hmap] at hv
      obtain ⟨w, hw, heq⟩ := hv
      exact E.injective heq ▸ hw

/-- Derivatives commute with a fixed linear projection in the actual
coordinate-extension model. -/
theorem coordinateDerivative_postcomp
    {n m l : ℕ} {M : Type u} [TopologicalSpace M]
    (e : ModelChart n .euclidean M) (g : M → Euclidean m) (p : M)
    (L : Euclidean n →L[ℝ] Euclidean m) (hL : HasCoordinateDerivative e g p L)
    (P : Euclidean m →L[ℝ] Euclidean l) :
    HasCoordinateDerivative e (fun q => P (g q)) p (P.comp L) := by
  obtain ⟨f, hf, hfg⟩ := hL
  exact ⟨P ∘ f, P.hasFDerivAt.comp (e p).val hf, hfg.fun_comp P⟩

/-- A locally constant projected coefficient has zero projected derivative. -/
theorem coordinateDerivative_projection_zero
    {n m l : ℕ} {M : Type u} [TopologicalSpace M]
    (e : ModelChart n .euclidean M) (g : M → Euclidean m) (p : M)
    (hp : p ∈ e.source) (L : Euclidean n →L[ℝ] Euclidean m)
    (hL : HasCoordinateDerivative e g p L) (P : Euclidean m →L[ℝ] Euclidean l)
    (c : Euclidean l) (hc : ∀ᶠ q in 𝓝 p, P (g q) = c) : P.comp L = 0 := by
  exact FiniteRegularity.extension_independence e (fun q => P (g q)) p hp
    (P.comp L) 0 (coordinateDerivative_postcomp e g p L hL P)
    ⟨fun _ => c, hasFDerivAt_const c (e p).val,
      (show (fun q => P (g q)) =ᶠ[𝓝 p] (fun _ => c) from hc).symm⟩

/-- Expand a linear map in the ordinary standard coordinate basis. -/
theorem linearMap_apply_component {n m : ℕ}
    (L : Euclidean n →L[ℝ] Euclidean m) (v : Euclidean n) (j : Fin m) :
    L v j = ∑ i, v i * L (Pi.single i 1) j := by
  have hv : v = ∑ i, v i • Pi.single i (1 : ℝ) := by
    ext i
    simp [Pi.single_apply]
  conv_lhs => rw [hv]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- The stated component formula is the intrinsic coordinate commutator. -/
theorem local_bracket_coefficients_eq
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (B : TangentBundleStructure S)
    (U : Set M) (X Y Z : VectorFieldData.Section S)
    (hbr : HasLocalBracket B U X Y Z)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ U) (hpe : p ∈ e.source)
    (L K : Euclidean n →L[ℝ] Euclidean n)
    (hL : HasCoordinateDerivative e (coefficients B X e he) p L)
    (hK : HasCoordinateDerivative e (coefficients B Y e he) p K) :
    coefficients B Z e he p = K (coefficients B X e he p) - L (coefficients B Y e he p) := by
  ext j
  rw [Pi.sub_apply, linearMap_apply_component, linearMap_apply_component,
    ← Finset.sum_sub_distrib]
  exact hbr.2 e he p hp hpe L K hL hK j

/-- Projection-normalized D-fields commute: involutivity puts their bracket
in D, while constancy of the projected coefficients puts it in ker P. -/
theorem normalized_bracket_zero
    {n k l : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {C : CotangentBundle S}
    (D : SmoothDistribution C k) (hinv : IsInvolutive D)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    (U : Set M) (hU : IsOpen U) (hUe : U ⊆ e.source)
    (P : Euclidean n →L[ℝ] Euclidean l)
    (hinj : ∀ (q : M) (hq : q ∈ U), ∀ v ∈ D.fiber q,
      P (C.tangent.fiberCoordinates.equiv e he q (hUe hq) v) = 0 → v = 0)
    (X Y Z : VectorFieldData.Section S)
    (hX : IsLocalField C.tangent U X) (hY : IsLocalField C.tangent U Y)
    (hbr : HasLocalBracket C.tangent U X Y Z)
    (hXD : ValuesIn D U X) (hYD : ValuesIn D U Y)
    (a b : Euclidean l)
    (hPX : ∀ q ∈ U, P (coefficients C.tangent X e he q) = a)
    (hPY : ∀ q ∈ U, P (coefficients C.tangent Y e he q) = b) :
    ∀ q ∈ U, Z q = 0 := by
  intro q hq
  apply hinj q hq (Z q) (hinv U hU X Y Z hX hY hbr hXD hYD q hq)
  obtain ⟨L, K, hL, hK⟩ := hbr.1 e he q hq (hUe hq)
  have hPL : P.comp L = 0 := coordinateDerivative_projection_zero e _ q (hUe hq) L hL P a
    (Filter.eventually_of_mem (hU.mem_nhds hq) (fun r hr => hPX r hr))
  have hPK : P.comp K = 0 := coordinateDerivative_projection_zero e _ q (hUe hq) K hK P b
    (Filter.eventually_of_mem (hU.mem_nhds hq) (fun r hr => hPY r hr))
  have h := local_bracket_coefficients_eq C.tangent U X Y Z hbr e he q hq (hUe hq) L K hL hK
  have hzero (w : Euclidean n) : P (K w) = 0 := congrArg (fun A : Euclidean n →L[ℝ] Euclidean l => A w) hPK
  have hzero' (w : Euclidean n) : P (L w) = 0 := congrArg (fun A : Euclidean n →L[ℝ] Euclidean l => A w) hPL
  have hproj := congrArg P h
  simpa only [coefficients, dite_eq_left (hUe hq), map_sub, hzero, hzero', sub_self] using hproj

/-- Smooth normalization of an injective local column map by a fixed
projection. Inverting the projected k-by-k map is restricted to its actual
open invertibility locus. This includes k=0. -/
theorem normalize_local_columns {n k : ℕ}
    (W : Euclidean n → Euclidean k →L[ℝ] Euclidean n)
    (O : Set (Euclidean n)) (hO : IsOpen O)
    (hW : ContDiffOn ℝ (⊤ : ℕ∞) W O)
    (a : Euclidean n) (ha : a ∈ O) (hinj : Function.Injective (W a)) :
    ∃ (P : Euclidean n →L[ℝ] Euclidean k) (V : Set (Euclidean n)),
      IsOpen V ∧ a ∈ V ∧ V ⊆ O ∧
      ∃ Y : Euclidean n → Euclidean k →L[ℝ] Euclidean n,
        ContDiffOn ℝ (⊤ : ℕ∞) Y V ∧
        ∀ x ∈ V, P.comp (Y x) = ContinuousLinearMap.id ℝ (Euclidean k) ∧
          LinearMap.range (Y x).toLinearMap = LinearMap.range (W x).toLinearMap ∧
          ∀ v ∈ LinearMap.range (W x).toLinearMap, P v = 0 → v = 0 := by
  classical
  obtain ⟨P₀, hP₀⟩ := (W a).toLinearMap.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hinj)
  let P := P₀.toContinuousLinearMap
  let A : Euclidean n → Euclidean k →L[ℝ] Euclidean k := fun x => P.comp (W x)
  have hA : ContDiffOn ℝ (⊤ : ℕ∞) A O := contDiffOn_const.clm_comp hW
  have hAa : A a = ContinuousLinearMap.id ℝ (Euclidean k) := by
    apply ContinuousLinearMap.ext
    intro x
    exact congrArg (fun L : Euclidean k →ₗ[ℝ] Euclidean k => L x) hP₀
  let V := O ∩ A ⁻¹' {L | L.IsInvertible}
  have hV : IsOpen V := hA.continuousOn.isOpen_inter_preimage hO
    ContinuousLinearMap.isOpen_setOfPred_isInvertible
  have haV : a ∈ V := by
    refine ⟨ha, ?_⟩
    change (A a).IsInvertible
    rw [hAa]
    exact ContinuousLinearMap.isInvertible_equiv (f := ContinuousLinearEquiv.refl ℝ _)
  have hVA : ∀ x ∈ V, (A x).IsInvertible := fun x hx => hx.2
  have hI : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => ContinuousLinearMap.inverse (A x)) V := by
    have hInv : ContDiffOn ℝ (⊤ : ℕ∞) ContinuousLinearMap.inverse
        {L : Euclidean k →L[ℝ] Euclidean k | L.IsInvertible} :=
      fun L hL => hL.contDiffAt_map_inverse.contDiffWithinAt
    exact hInv.comp (hA.mono inter_subset_left) (fun x hx => hx.2)
  let Y : Euclidean n → Euclidean k →L[ℝ] Euclidean n :=
    fun x => (W x).comp (ContinuousLinearMap.inverse (A x))
  refine ⟨P, V, hV, haV, inter_subset_left, Y,
    (hW.mono inter_subset_left).clm_comp hI, ?_⟩
  intro x hx
  have hAx := hVA x hx
  refine ⟨?_, ?_, ?_⟩
  · change P.comp ((W x).comp (A x).inverse) = _
    rw [← ContinuousLinearMap.comp_assoc]
    exact hAx.self_comp_inverse
  · ext v
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨(A x).inverse u, rfl⟩
    · rintro ⟨u, rfl⟩
      refine ⟨A x u, ?_⟩
      change W x ((A x).inverse (A x u)) = W x u
      rw [hAx.inverse_apply_self]
  · intro v hv hPv
    obtain ⟨u, rfl⟩ := hv
    have hu : A x u = 0 := hPv
    have hu0 : u = 0 := by
      have h := congrArg (A x).inverse hu
      simpa only [hAx.inverse_apply_self, map_zero] using h
    rw [hu0, map_zero]

/-- Extend a smooth Euclidean coordinate germ to an actual global smooth
field using a bump supported inside its coordinate domain. Only germ agreement
is asserted, so this imposes no global spanning or completeness hypothesis. -/
theorem exists_field_with_coordinate_germ
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (B : TangentBundleStructure S)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ e.source)
    (O : Set (Euclidean n)) (hO : IsOpen O) (hpO : (e p).val ∈ O)
    (f : Euclidean n → Euclidean n) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f O) :
    ∃ X : VectorFieldData.SmoothField B,
      ∀ᶠ q in 𝓝 p, coefficients B X.val e he q = f (e q).val := by
  classical
  let U : Set M := e.source ∩ (fun q => (e q).val) ⁻¹' O
  have hU : IsOpen U :=
    (continuous_subtype_val.comp_continuousOn e.continuousOn_toFun).isOpen_inter_preimage
      e.open_source hO
  obtain ⟨β, hβ, _hβbound, hβone, hβsupp, _hβcompact⟩ :=
    exists_local_bump S p U hU ⟨hp, hpO⟩
  let X : VectorFieldData.Section S := fun q =>
    if hq : q ∈ U then β q • (B.fiberCoordinates.equiv e he q hq.1).symm (f (e q).val) else 0
  have hXzero (q : M) (hβq : β q = 0) : X q = 0 := by
    by_cases hq : q ∈ U <;> simp [X, hq, hβq]
  have hX : letI := B.topology
      IsSmoothMap S B.manifold (fun q => (⟨q, X q⟩ : TotalSpace S)) := by
    let := B.topology
    intro q
    by_cases hq : q ∈ U
    · let w : M → Euclidean n := fun r => β r • f (e r).val
      have hw : ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) S.smoothStructure.val w q := by
        apply TangentBundle.euclidean_smoothAt_of_chart S w q e he hq.1
        obtain ⟨V, hV, hqV, G, hG, hGβ⟩ :=
          ((scalarContDiffAt_iff (⊤ : ℕ∞) S.smoothStructure.val β q).mp (hβ q)).2 e he hq.1
        exact ⟨V ∩ O, hV.inter hO, ⟨hqV, hq.2⟩, (fun x => G x • f x),
          (hG.mono inter_subset_left).smul (hf.mono inter_subset_right),
          hGβ.mono (fun r hr => congrArg (fun b => b • f (e r).val) hr)⟩
      apply TangentBundle.lift_smoothAt_of_coeff S B S (fun r => ⟨r, X r⟩) q e he hq.1 w
        (manifoldContDiff_id (⊤ : ℕ∞) _ S.smoothStructure.property.1 q) hw
      filter_upwards [hU.mem_nhds hq] with r hr
      refine ⟨hr.1, ?_⟩
      simp [X, hr, w]
    · have hqsupp : q ∉ sectionSupport β := fun h => hq (hβsupp h)
      have hnear : ∀ᶠ r in 𝓝 q, r ∉ sectionSupport β :=
        (isClosed_closure.isOpen_compl.mem_nhds hqsupp)
      apply manifoldContDiffAt_congr (TangentBundle.zero_smooth S B q)
      filter_upwards [hnear] with r hr
      have hβr : β r = 0 := by
        by_contra h
        exact hr (subset_closure h)
      exact congrArg (fun v => (⟨r, v⟩ : TotalSpace S)) (hXzero r hβr).symm
  refine ⟨⟨X, hX⟩, ?_⟩
  filter_upwards [hU.mem_nhds ⟨hp, hpO⟩, hβone] with q hq hβq
  simp [coefficients, hq.1, X, hq, hβq]

/-- Smooth distribution-frame vectors admit ordinary ambient smooth coordinate
representatives near any point of their open frame domain. -/
theorem frameSection_coordinate_extension
    {n k : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {C : CotangentBundle S}
    {D : SmoothDistribution C k} {U : Set M} {hU : IsOpen U}
    (F : DistributionFrame D U hU) (i : Fin k)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ U) (hpe : p ∈ e.source) :
    LocalCoordinateExtension (⊤ : ℕ∞) (fun q => (e q).val)
      (coefficients C.tangent (frameSection F i) e he) p := by
  classical
  let B := C.tangent
  let := B.topology
  let pU : U := ⟨p, hp⟩
  let d : ModelChart n .euclidean U := e.subtypeRestr (s := ⟨U, hU⟩) ⟨pU⟩
  have hd : d ∈ openSubsetAtlas S.smoothStructure.val U hU := ⟨⟨pU⟩, e, he, rfl⟩
  have hpd : pU ∈ d.source := by
    change pU ∈ (e.subtypeRestr (s := ⟨U, hU⟩) ⟨pU⟩).source
    rw [OpenPartialHomeomorph.subtypeRestr_source]
    exact hpe
  let s : U → TotalSpace S := fun q => ⟨q.val, (F.basis q i).val⟩
  have hps : s pU ∈ (B.chart e he).source := by
    rw [B.chart_source]
    exact hpe
  have h := (F.smooth i pU).2 d hd (B.chart e he) (TangentBundle.chart_mem S B e he) hpd hps
  let L := (ContinuousLinearMap.snd ℝ (Euclidean n) (Euclidean n)).comp
    B.productCoordinates.linearEquiv.symm.toContinuousLinearMap
  have ht := TangentBundle.extension_linear h L
  have heq : (fun q : U => L ((B.chart e he) (s q)).val) =ᶠ[𝓝 pU]
      (coefficients B (frameSection F i) e he ∘ Subtype.val) := by
    filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds
      (e.open_source.mem_nhds hpe)] with q hq
    change L ((B.chart e he) (s q)).val = coefficients B (frameSection F i) e he q.val
    change q.val ∈ e.source at hq
    rw [B.chart_apply e he (s q) hq]
    simp [L, s, frameSection, q.property, coefficients, hq]
  have ht' := LocalCoordinateExtension.congr ht heq
  exact (localCoordinateExtension_open_subtype_iff hU (fun q => (e q).val)
    (coefficients B (frameSection F i) e he) pU).mp ht'

/-- The actual smooth finite matrix of a local distribution frame. -/
theorem frame_coordinate_columns
    {n k : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {C : CotangentBundle S}
    {D : SmoothDistribution C k} {U : Set M} {hU : IsOpen U}
    (F : DistributionFrame D U hU)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ U) (hpe : p ∈ e.source) :
    ∃ (O : Set (Euclidean n)), IsOpen O ∧ (e p).val ∈ O ∧
      ∃ W : Euclidean n → Euclidean k →L[ℝ] Euclidean n,
        ContDiffOn ℝ (⊤ : ℕ∞) W O ∧
        Function.Injective (W (e p).val) ∧
        ∀ᶠ q in 𝓝 p, ∃ hqU : q ∈ U, ∃ hqe : q ∈ e.source,
          ∀ i : Fin k, W (e q).val (Pi.single i 1) =
            C.tangent.fiberCoordinates.equiv e he q hqe ((F.basis ⟨q, hqU⟩ i).val) := by
  classical
  choose O hO hpO f hf hfeq using fun i : Fin k =>
    frameSection_coordinate_extension F i e he p hp hpe
  let V : Set (Euclidean n) := ⋂ i, O i
  let W : Euclidean n → Euclidean k →L[ℝ] Euclidean n := fun x =>
    ∑ i : Fin k, (ContinuousLinearMap.proj i).smulRight (f i x)
  have hWcol (x : Euclidean n) (i : Fin k) : W x (Pi.single i 1) = f i x := by
    simp [W, ContinuousLinearMap.smulRight_apply, Pi.single_apply]
  have hW : ContDiffOn ℝ (⊤ : ℕ∞) W V := by
    apply ContDiffOn.sum
    intro i _
    exact ((ContinuousLinearMap.smulRightL ℝ (Euclidean k) (Euclidean n))
      (ContinuousLinearMap.proj i)).contDiff.comp_contDiffOn ((hf i).mono (iInter_subset _ i))
  have heq : ∀ᶠ q in 𝓝 p, ∃ hqU : q ∈ U, ∃ hqe : q ∈ e.source,
      ∀ i : Fin k, W (e q).val (Pi.single i 1) =
        C.tangent.fiberCoordinates.equiv e he q hqe ((F.basis ⟨q, hqU⟩ i).val) := by
    filter_upwards [Filter.eventually_all.mpr hfeq, hU.mem_nhds hp,
      e.open_source.mem_nhds hpe] with q hq hqU hqe
    refine ⟨hqU, hqe, ?_⟩
    intro i
    rw [hWcol, hq i]
    simp [coefficients, hqe, frameSection, hqU]
  have hcol := Filter.Eventually.self_of_nhds heq
  have hinj : Function.Injective (W (e p).val) := by
    let E := C.tangent.fiberCoordinates.equiv e he p hpe
    let G : Euclidean k →ₗ[ℝ] TangentSpace S p :=
      (D.fiber p).subtype.comp (F.basis ⟨p, hp⟩).equivFun.symm.toLinearMap
    have hWG : (W (e p).val).toLinearMap = E.toLinearMap.comp G := by
      apply (Pi.basisFun ℝ (Fin k)).ext
      intro i
      simpa [G, Pi.basisFun_apply, _root_.Basis.equivFun_symm_single] using hcol.choose_spec.choose_spec i
    change Function.Injective (W (e p).val).toLinearMap
    rw [hWG]
    exact E.injective.comp (Subtype.val_injective.comp (F.basis ⟨p, hp⟩).equivFun.symm.injective)
  exact ⟨V, isOpen_iInter_of_finite hO, mem_iInter.mpr hpO, W, hW, hinj, heq⟩

theorem range_eq_span_columns {n k : ℕ} (W : Euclidean k →L[ℝ] Euclidean n) :
    LinearMap.range W.toLinearMap =
      Submodule.span ℝ (Set.range (fun i : Fin k => W (Pi.single i 1))) := by
  rw [← Submodule.map_top, ← (Pi.basisFun ℝ (Fin k)).span_eq,
    Submodule.map_span, ← Set.range_comp']
  simp only [Pi.basisFun_apply, ContinuousLinearMap.coe_coe]

/-- Mapping a basis of a subspace spans exactly its linear image. -/
theorem span_basis_image {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] {k : ℕ}
    (K : Submodule ℝ V) (b : Module.Basis (Fin k) ℝ K) (E : V →ₗ[ℝ] W) :
    Submodule.span ℝ (Set.range (fun i => E (b i).val)) = K.map E := by
  have hm := Submodule.map_span (E.comp K.subtype) (Set.range b)
  rw [← Set.range_comp', b.span_eq, Submodule.map_top] at hm
  change (E.comp K.subtype).range =
    Submodule.span ℝ (Set.range (fun i => E (b i).val)) at hm
  rw [← hm]
  ext y
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨v.val, v.property, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨⟨v, hv⟩, rfl⟩

/-- A smooth distribution admits, near each point, a smooth frame normalized
by one fixed linear projection of an original coordinate chart. The frame
members are extended globally only as representatives of their local germs. -/
theorem projection_normalized_frame
    {n k : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {C : CotangentBundle S}
    (D : SmoothDistribution C k) (p : M) :
    ∃ (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
      (U : Set M) (hU : IsOpen U), p ∈ U ∧ ∃ hUe : U ⊆ e.source,
      ∃ (P : Euclidean n →L[ℝ] Euclidean k)
        (X : Fin k → VectorFieldData.SmoothField C.tangent),
        (∀ q ∈ U, Submodule.span ℝ (Set.range (fun i => (X i).val q)) = D.fiber q) ∧
        (∀ (q : M) (hq : q ∈ U), ∀ v ∈ D.fiber q,
          P (C.tangent.fiberCoordinates.equiv e he q (hUe hq) v) = 0 → v = 0) ∧
        (∀ i q, q ∈ U → P (coefficients C.tangent (X i).val e he q) = Pi.single i 1) ∧
        LinearIndependent ℝ (fun i => (X i).val p) := by
  classical
  obtain ⟨Fdom, hFdom, hpFdom, ⟨F⟩⟩ := DistributionTests.distribution_frame_exists D p
  obtain ⟨e, he, hpe⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨O, hO, hpO, W, hW, hWinj, hWframe⟩ :=
    frame_coordinate_columns F e he p hpFdom hpe
  obtain ⟨P, V, hV, hpV, _hVO, Y, hY, hNorm⟩ :=
    normalize_local_columns W O hO hW (e p).val hpO hWinj
  have hYcol (i : Fin k) : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => Y x (Pi.single i 1)) V := hY.clm_apply contDiffOn_const
  choose X hX using fun i => exists_field_with_coordinate_germ S C.tangent e he p hpe
    V hV hpV (fun x => Y x (Pi.single i 1)) (hYcol i)
  have hvnear : ∀ᶠ q in 𝓝 p, (e q).val ∈ V :=
    (continuous_subtype_val.continuousAt.comp (e.continuousAt hpe)).preimage_mem_nhds
      (hV.mem_nhds hpV)
  have hnear := hvnear.and (hWframe.and (Filter.eventually_all.mpr hX))
  obtain ⟨U, hUNear, hU, hpU⟩ := mem_nhds_iff.mp hnear
  have hUe : U ⊆ e.source := fun q hq => (hUNear hq).2.1.choose_spec.choose
  have hUY : ∀ q ∈ U, (e q).val ∈ V := fun q hq => (hUNear hq).1
  have hUX (q : M) (hq : q ∈ U) (i : Fin k) :
      C.tangent.fiberCoordinates.equiv e he q (hUe hq) ((X i).val q) =
        Y (e q).val (Pi.single i 1) := by
    simpa only [coefficients, dite_eq_left (hUe hq)] using (hUNear hq).2.2 i
  have hRange (q : M) (hq : q ∈ U) :
      LinearMap.range (Y (e q).val).toLinearMap =
        (D.fiber q).map (C.tangent.fiberCoordinates.equiv e he q (hUe hq)).toLinearMap := by
    let E := C.tangent.fiberCoordinates.equiv e he q (hUe hq)
    obtain ⟨hqF, hqe, hWq⟩ := (hUNear hq).2.1
    have hbspan := span_basis_image (V := TangentSpace S q) (W := Euclidean n)
      (D.fiber q) (F.basis ⟨q, hqF⟩) E.toLinearMap
    have hWcols : (fun i : Fin k => W (e q).val (Pi.single i 1)) =
        (fun i => E ((F.basis ⟨q, hqF⟩ i).val)) := funext hWq
    calc
      LinearMap.range (Y (e q).val).toLinearMap = LinearMap.range (W (e q).val).toLinearMap :=
        (hNorm _ (hUY q hq)).2.1
      _ = Submodule.span ℝ (Set.range (fun i : Fin k => W (e q).val (Pi.single i 1))) :=
        range_eq_span_columns _
      _ = (D.fiber q).map E.toLinearMap := by rw [hWcols]; exact hbspan
  have hSpan (q : M) (hq : q ∈ U) :
      Submodule.span ℝ (Set.range (fun i => (X i).val q)) = D.fiber q := by
    let E := C.tangent.fiberCoordinates.equiv e he q (hUe hq)
    apply Submodule.map_injective_of_injective E.injective
    rw [Submodule.map_span, ← Set.range_comp']
    have hcols : (fun i => E ((X i).val q)) = fun i => Y (e q).val (Pi.single i 1) :=
      funext (hUX q hq)
    change Submodule.span ℝ (Set.range (fun i : Fin k => E ((X i).val q))) =
      (D.fiber q).map E.toLinearMap
    rw [hcols, ← range_eq_span_columns, hRange q hq]
  have hP (i : Fin k) (q : M) (hq : q ∈ U) :
      P (coefficients C.tangent (X i).val e he q) = Pi.single i 1 := by
    rw [coefficients, dite_eq_left (hUe hq), hUX q hq i]
    exact congrArg (fun A : Euclidean k →L[ℝ] Euclidean k => A (Pi.single i 1))
      (hNorm _ (hUY q hq)).1
  refine ⟨e, he, U, hU, hpU, hUe, P, X, hSpan, ?_, hP, ?_⟩
  · intro q hq v hv hPv
    let E := C.tangent.fiberCoordinates.equiv e he q (hUe hq)
    have hvRange : E v ∈ LinearMap.range (W (e q).val).toLinearMap := by
      rw [← (hNorm _ (hUY q hq)).2.1, hRange q hq]
      exact ⟨v, hv, rfl⟩
    have hz := (hNorm _ (hUY q hq)).2.2 (E v) hvRange hPv
    exact E.map_eq_zero_iff.mp hz
  · let L := P.toLinearMap.comp (C.tangent.fiberCoordinates.equiv e he p (hUe hpU)).toLinearMap
    apply LinearIndependent.of_comp L
    have hstd : L ∘ (fun i => (X i).val p) = Pi.basisFun ℝ (Fin k) := by
      funext i
      simpa only [L, Function.comp_apply, LinearMap.comp_apply,
        ContinuousLinearMap.coe_coe, LinearEquiv.coe_coe, coefficients,
        dite_eq_left (hUe hpU), Pi.basisFun_apply] using hP i p hpU
    rw [hstd]
    exact (Pi.basisFun ℝ (Fin k)).linearIndependent

/-- Involutivity produces adapted coordinates via the projection-normalized
local frame. All uses of the auxiliary global fields are confined to U. -/
theorem adapted_coordinates_of_involutive
    {n k : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {C : CotangentBundle S}
    (D : SmoothDistribution C k) (hinv : IsInvolutive D) : HasAdaptedCoordinates D := by
  intro p
  obtain ⟨e, he, U, hU, hpU, hUe, P, X, hSpan, hInj, hProj, hIndependent⟩ :=
    projection_normalized_frame D p
  obtain ⟨b, hb, _hbUnique⟩ := LieBrackets.bracket_exists S C.tangent
  have hValues (i : Fin k) : ValuesIn D U (X i).val := by
    intro q hq
    rw [← hSpan q hq]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hField (i : Fin k) : IsLocalField C.tangent U (X i).val :=
    fun q _ => (X i).smooth q
  have hcomm (i j : Fin k) : ∀ q ∈ U, (b (X i) (X j)).val q = 0 := by
    have hbc := LieBrackets.bracket_coordinates S C.tangent b hb (X i) (X j)
    have hlocal : HasLocalBracket C.tangent U (X i).val (X j).val (b (X i) (X j)).val :=
      ⟨fun d hd q _ hqd => hbc.1 d hd q hqd,
        fun d hd q _ hqd => hbc.2 d hd q hqd⟩
    exact normalized_bracket_zero D hinv e he U hU hUe P hInj
      (X i).val (X j).val (b (X i) (X j)).val (hField i) (hField j)
      hlocal (hValues i) (hValues j) (Pi.single i 1) (Pi.single j 1)
      (hProj i) (hProj j)
  exact adapted_chart_of_commuting_frame D b hb X p (D.smooth p).1 hIndependent
    U hU hpU hSpan (fun i j => hcomm i j)

/-- The full local Frobenius equivalence, including ranks zero and n. -/
theorem adapted_coordinates :
    Specs.SmoothManifolds.Ch08.Frobenius.adapted_coordinatesType.{u} := by
  intro n k M _ S C D
  exact ⟨adapted_coordinates_of_involutive D, involutive_of_adapted_coordinates D⟩

/-- Every slice of any adapted chart is an integral submanifold. -/
theorem integral_slices :
    Specs.SmoothManifolds.Ch08.Frobenius.integral_slicesType.{u} := by
  intro n k M _ S C D e he hadapt z
  exact integral_slice_of_adapted D e he hadapt z

/-- The slice construction gives integral submanifolds in the exact shared
sense of Chapter 8, using the inherited topology as the permitted witness. -/
theorem integralSubmanifold_of_integralSlice
    {n k : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {C : CotangentBundle S}
    {D : SmoothDistribution C k} {A : Set M} (h : IsIntegralSlice D A) :
    IsIntegralSubmanifold D A := by
  obtain ⟨T, hsmooth, himm, L, hL, hrange⟩ := h
  exact ⟨inferInstance, T, hsmooth, himm, L, hL, hrange⟩

/-- Every point belongs to an integral slice of an adapted coordinate chart. -/
theorem integrable_of_adapted_coordinates
    {n k : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {C : CotangentBundle S}
    (D : SmoothDistribution C k) (h : HasAdaptedCoordinates D) : IsIntegrable D := by
  intro p
  obtain ⟨e, he, hp, hadapt⟩ := h p
  let z := transverseCoordinates k (e p).val
  exact ⟨coordinateSlice e k z, ⟨hp, rfl⟩,
    integralSubmanifold_of_integralSlice (integral_slice_of_adapted D e he hadapt z)⟩

end SmoothManifolds.Frobenius
