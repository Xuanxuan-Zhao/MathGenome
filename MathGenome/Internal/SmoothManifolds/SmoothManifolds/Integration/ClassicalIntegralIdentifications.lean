import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Integration.ClassicalIntegralIdentifications
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Integration.Global
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Orientations.MetricVolume
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch07.ExteriorDerivative
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Tangent.EmbeddedComparison
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.MapClasses
import Mathlib.Tactic.Ring
import Mathlib.LinearAlgebra.BilinearForm.Hom
import Mathlib.LinearAlgebra.Matrix.DotProduct

set_option autoImplicit false
noncomputable section
open scoped Classical Topology BigOperators

namespace SmoothManifolds.ClassicalIntegralResults
open ModelData AtlasData TangentData TangentBundleData BundleOperationsData CovectorData ExteriorData
  FormPullbackData OrientationData MetricVolumeData LocalIntegrationData
  GlobalIntegrationData ClassicalIntegralData Set MeasureTheory
universe u

/-- Coordinate evaluation is the determinant pairing, with no factorial. -/
theorem topCoefficient_pairing {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (K : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (p : c.source)
    (ω : Field S n) : topCoefficient K c hc p.val p.property ω =
      pairing p.val (ω p.val) (OrientationData.coordinateVector K c hc p) := by
  change (exteriorPower.alternatingMapLinearEquiv.symm
    ((exteriorPower.pairingDual ℝ (TangentData.TangentSpace S p.val) n) (ω p.val)))
      (fun j => (K.equiv c hc p.val p.property).symm (Pi.single j 1)) = _
  simpa only [pairing, OrientationData.coordinateVector, Pi.basisFun_apply, LinearMap.compAlternatingMap_apply] using
    exteriorPower.alternatingMapLinearEquiv_symm_apply (R := ℝ) (M := TangentData.TangentSpace S p.val) (N := ℝ)
    ((exteriorPower.pairingDual ℝ (TangentData.TangentSpace S p.val) n) (ω p.val))
    (fun j => (K.equiv c hc p.val p.property).symm (Pi.single j 1))

/-- The coefficient of the normalized metric volume in signed coordinates. -/
theorem volume_topCoefficient {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (D : FormBundle C n) (g : Metric C) (o : Orientation S) (ω : Form D)
    (hω : IsMetricVolume g o ω) (s : SignedCharts S) (hs : RepresentsSignedCharts o.val s)
    (K : FiberCoordinates S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (p : c.source) : topCoefficient K c hc p.val p.property ω.field =
      signValue (s.sign c hc p) * Real.sqrt (metricMatrix g K c hc p).det := by
  rw [topCoefficient_pairing]
  rw [MetricVolumeResults.volume_coordinates S C D g o ω hω s hs K c hc p]
  simp only [pairing, map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [show exteriorPower.pairingDual ℝ (TangentSpace S p.val) n
      (coordinateTopForm K c hc p) (OrientationData.coordinateVector K c hc p) = 1 from
    MetricVolumeResults.coordinateTopForm_pairing K c hc p]
  exact mul_one _

/-- Continuity follows from the locally constant sign and the smooth Gram factor. -/
theorem metric_volume_continuous {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (D : FormBundle C n) (g : Metric C) (o : Orientation S) (ω : Form D)
    (hω : IsMetricVolume g o ω) : IsContinuousTopForm ω.field := by
  obtain ⟨s, hs, _⟩ := LocalIntegrationResults.orientation_signs S o
  intro K c hc
  have hg : Continuous (fun p : c.source => Real.sqrt (metricMatrix g K c hc p).det) :=
    continuous_iff_continuousAt.mpr (fun p =>
      (MetricVolumeResults.metric_coefficient_smooth g K c hc p).1)
  have he : (fun p : c.source => topCoefficient K c hc p.val p.property ω.field) =
      fun p => signValue (s.sign c hc p) * Real.sqrt (metricMatrix g K c hc p).det :=
    funext (volume_topCoefficient C D g o ω hω s hs K c hc)
  rw [he]
  exact ((s.locallyConstant c hc).comp signValue).continuous.mul hg

/-- No compactness is required of the unweighted volume section. -/
def scalarVolumeForm {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (D : FormBundle C n) (g : Metric C) (o : Orientation S) (ω : Form D)
    (hω : IsMetricVolume g o ω) (f : M → ℝ) (hf : Continuous f)
    (hfc : IsCompact (ModelData.sectionSupport f)) : CompactTopForm S where
  field := scalarVolume f ω.field
  continuous := by
    intro K c hc
    apply Continuous.congr ((hf.comp continuous_subtype_val).mul
      (metric_volume_continuous C D g o ω hω K c hc))
    intro p
    exact (GlobalIntegrationResults.topCoefficient_weight K c hc p.val p.property f ω.field).symm
  compact_support := hfc.of_isClosed_subset isClosed_closure
    (fun _ hp => (GlobalIntegrationResults.weight_support S n ω.field f hp).1)

theorem scalar_volume_compact :
    Specs.SmoothManifolds.Integration.ClassicalIntegralIdentifications.scalar_volume_compactType.{u} := by
  intro n a M _ S C D g o ω hω f hf hfc
  exact ⟨scalarVolumeForm C D g o ω hω f hf hfc, rfl,
    fun _ hp => (GlobalIntegrationResults.weight_support S n ω.field f hp).1⟩

theorem compact_manifold_support :
    Specs.SmoothManifolds.Integration.ClassicalIntegralIdentifications.compact_manifold_supportType.{u} := by
  intro n a M _ _ S k ω
  exact isClosed_closure.isCompact

theorem scalarVolume_topCoefficient {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (K : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (p : M) (hp : p ∈ c.source)
    (f : M → ℝ) (α : Field S n) :
    topCoefficient K c hc p hp (scalarVolume f α) = f p * topCoefficient K c hc p hp α :=
  GlobalIntegrationResults.topCoefficient_weight K c hc p hp f α

theorem scalar_volume_coefficient :
    Specs.SmoothManifolds.Integration.ClassicalIntegralIdentifications.scalar_volume_coefficientType.{u} := by
  intro n a M _ S C D g o ω hω s hs K c hc f
  funext x
  unfold signedCoordinateCoefficient gramIntegrand extendModel
  split_ifs with hx
  · dsimp only
    unfold modelSignedCoefficient
    split_ifs with ht
    · rw [scalarVolume_topCoefficient,
        volume_topCoefficient C D g o ω hω s hs K c hc
          ⟨c.symm ⟨x, hx⟩, c.map_target ht⟩]
      cases s.sign c hc ⟨c.symm ⟨x, hx⟩, c.map_target ht⟩ <;> simp [signValue]
    · rfl
  · rfl

theorem scalar_volume_local_integral :
    Specs.SmoothManifolds.Integration.ClassicalIntegralIdentifications.scalar_volume_local_integralType.{u} := by
  intro n a M _ S C D g o ω hω f hf hfc
  let η := scalarVolumeForm C D g o ω hω f hf hfc
  refine ⟨η, rfl, ?_⟩
  intro I hI K c hc hsupport
  obtain ⟨s, hs, _⟩ := LocalIntegrationResults.orientation_signs S o
  have hη : ModelData.sectionSupport η.field ⊆ c.source :=
    fun _ hp => hsupport ((GlobalIntegrationResults.weight_support S n ω.field f hp).1)
  have he := scalar_volume_coefficient S C D g o ω hω s hs K c hc f
  have hi := LocalIntegrationResults.integrable S s K c hc η hη
  refine ⟨?_, ?_⟩
  · simpa only [η, scalarVolumeForm, he] using hi
  · rw [hI.2.2 s hs K c hc η hη]
    change (∫ x, signedCoordinateCoefficient s K c hc (scalarVolume f ω.field) x) = _
    rw [he]

theorem weighted_gram_overlap :
    Specs.SmoothManifolds.Integration.ClassicalIntegralIdentifications.weighted_gram_overlapType.{u} := by
  intro n a M _ S C g K c d hc hd f p
  rw [MetricVolumeResults.metric_coefficient_transition g K c d hc hd p]
  ring

theorem scalar_volume_localization :
    Specs.SmoothManifolds.Integration.ClassicalIntegralIdentifications.scalar_volume_localizationType.{u} := by
  intro n a M _ S C D g o ω hω f hf hfc
  let η := scalarVolumeForm C D g o ω hω f hf hfc
  refine ⟨η, rfl, ?_⟩
  intro I hI K ι c hc ρ hρ
  obtain ⟨s, hs, _⟩ := LocalIntegrationResults.orientation_signs S o
  rw [GlobalIntegrationResults.localization S o I hI s hs K c hc ρ η hρ]
  congr 1
  funext i
  have he : (fun p => ρ i p • η.field p) =
      scalarVolume (fun p => ρ i p * f p) ω.field := by
    funext p
    simp only [η, scalarVolumeForm, scalarVolume, mul_smul]
  rw [he, coordinateIntegral,
    scalar_volume_coefficient S C D g o ω hω s hs K (c i) (hc i)]

theorem scalarField_support {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (f : M → ℝ) :
    ModelData.sectionSupport (scalarField S f) = ModelData.sectionSupport f := by
  unfold ModelData.sectionSupport
  congr 1
  ext p
  simp [scalarField]

/-- Compact scalar zero-forms are constructed without an integrability premise. -/
def zeroScalarForm {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold 0 a M) (f : M → ℝ) (hf : Continuous f)
    (hfc : IsCompact (ModelData.sectionSupport f)) : CompactTopForm S where
  field := scalarField S f
  continuous := by
    intro K c hc
    have he : (fun p : c.source => topCoefficient K c hc p.val p.property (scalarField S f)) =
        fun p => f p.val := by
      funext p
      rw [LocalIntegrationResults.topCoefficient_zero]
      simp [zeroCoefficient, scalarField]
    rw [he]
    exact hf.comp continuous_subtype_val
  compact_support := by rw [scalarField_support]; exact hfc

theorem zero_scalar_integral :
    Specs.SmoothManifolds.Integration.ClassicalIntegralIdentifications.zero_scalar_integralType.{u} := by
  intro a M _ S o f hf hfc
  let η := zeroScalarForm S f hf hfc
  refine ⟨η, rfl, ?_⟩
  intro I hI
  obtain ⟨h, he⟩ := GlobalIntegrationResults.zero_finite_sum S o I hI η
  have hs : ModelData.sectionSupport η.field = ModelData.sectionSupport f := scalarField_support S f
  have hh : h.toFinset = (hs ▸ h).toFinset := by
    ext p
    simp only [Set.Finite.mem_toFinset]
    exact Set.ext_iff.mp hs p
  refine ⟨hs ▸ h, ?_⟩
  rw [hh] at he
  simpa only [η, zeroScalarForm, zeroCoefficient, scalarField, LinearEquiv.apply_symm_apply]
    using he

theorem zero_volume_coefficient {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 0 a M} (C : CotangentBundle S) (D : FormBundle C 0)
    (g : Metric C) (o : Orientation S) (ω : Form D) (hω : IsMetricVolume g o ω)
    (p : M) : zeroCoefficient ω.field p = zeroSign o p := by
  obtain ⟨s, hs, _⟩ := LocalIntegrationResults.orientation_signs S o
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
  let K := C.tangent.fiberCoordinates
  rw [← LocalIntegrationResults.topCoefficient_zero K c hc ω.field ⟨p, hp⟩,
    volume_topCoefficient C D g o ω hω s hs K c hc ⟨p, hp⟩,
    LocalIntegrationResults.zeroSign_eq_chartSign o s hs K c hc ⟨p, hp⟩]
  simp [Matrix.det_isEmpty]

theorem zero_metric_integral :
    Specs.SmoothManifolds.Integration.ClassicalIntegralIdentifications.zero_metric_integralType.{u} := by
  intro a M _ S C D g o ω hω f hf hfc
  let η := scalarVolumeForm C D g o ω hω f hf hfc
  refine ⟨η, rfl, ?_⟩
  intro I hI
  obtain ⟨h, he⟩ := GlobalIntegrationResults.zero_finite_sum S o I hI η
  refine ⟨h, he.trans ?_⟩
  apply Finset.sum_congr rfl
  intro p hp
  change zeroSign o p * zeroCoefficient (scalarVolume f ω.field) p = f p
  have hec : zeroCoefficient (scalarVolume f ω.field) p = f p * zeroCoefficient ω.field p := by
    simp [zeroCoefficient, scalarVolume, map_smul]
  rw [hec, zero_volume_coefficient C D g o ω hω p]
  unfold zeroSign
  split_ifs <;> ring

theorem embedded_coefficients_regular :
    Specs.SmoothManifolds.Integration.ClassicalIntegralIdentifications.embedded_coefficients_regularType := by
  intro n N a M _ S j hj A hA c hc p
  obtain ⟨U, H, ⟨hU, hpU, hH, heH⟩, _⟩ := hj p.val c hc p.property
  obtain ⟨V, hV, hpV, F, hF, heF⟩ := hA p.val
  have hHp : H (c p.val).val = j p.val := heH.eq_of_nhds
  have hH' : ContDiffAt ℝ 1 H (c p.val).val :=
    (hH.contDiffAt (hU.mem_nhds hpU)).of_le (by simp)
  have hF' : ContDiffAt ℝ 1 F (H (c p.val).val) := by
    rw [hHp]
    exact hF.contDiffAt (hV.mem_nhds hpV)
  apply ExteriorDerivativeResults.localExtensionAt_of_germ 1 c _ p (F ∘ H)
    (hF'.comp _ hH')
  have hjp : ContinuousAt j p.val := by
    have hcoord : ContinuousAt (fun y => (c y).val) p.val :=
      continuous_subtype_val.continuousAt.comp (c.continuousAt p.property)
    have hcont := (hH.continuousOn.continuousAt (hU.mem_nhds hpU)).comp
      (f := fun y : M => (c y).val) hcoord
    exact hcont.congr_of_eventuallyEq heH.symm
  filter_upwards [c.open_source.mem_nhds p.property,
    hjp.preimage_mem_nhds (hV.mem_nhds hpV), heH] with y hy hyV hyH
  rw [FrameData.totalize_of_mem _ y hy]
  change F (H (c y).val) = A y
  rw [hyH]
  exact heF y hyV

theorem regular_scalar_multiply :
    Specs.SmoothManifolds.Integration.ClassicalIntegralIdentifications.regular_scalar_multiplyType.{u} := by
  intro n a M _ S C k ω hω f hf
  refine ⟨?_, GlobalIntegrationResults.weight_support S k ω f⟩
  intro c hc p
  obtain ⟨U, hU, hpU, F, hF, heF⟩ := hf c hc p
  obtain ⟨V, hV, hpV, G, hG, heG⟩ := hω c hc p
  refine ⟨U ∩ V, hU.inter hV, ⟨hpU, hpV⟩, fun z => F z • G z,
    (hF.mono inter_subset_left).smul (hG.mono inter_subset_right), ?_⟩
  intro q hq
  change F (c q.val).val • G (c q.val).val = _
  rw [heF q hq.1, heG q hq.2]
  funext I
  simp [ExteriorData.coefficients, map_smul]

/-- The full-rank parametrization hypothesis in particular gives continuity. -/
theorem embedded_map_continuousAt {n N : ℕ} {a : ModelKind} {M : Type}
    [TopologicalSpace M] (S : SmoothManifold n a M) (j : M → Euclidean N)
    (hj : EmbeddedData.HasFullRankParametrizations S j) (p : M) : ContinuousAt j p := by
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨U, H, ⟨hU, hpU, hH, heH⟩, _⟩ := hj p c hc hp
  have hcoord : ContinuousAt (fun y => (c y).val) p :=
    continuous_subtype_val.continuousAt.comp (c.continuousAt hp)
  exact ((hH.continuousOn.continuousAt (hU.mem_nhds hpU)).comp
      (f := fun y : M => (c y).val) hcoord).congr_of_eventuallyEq heH.symm

theorem embedded_coordinate_smooth {n N : ℕ} {a : ModelKind} {M : Type}
    [TopologicalSpace M] (S : SmoothManifold n a M) (j : M → Euclidean N)
    (hj : EmbeddedData.HasFullRankParametrizations S j) (i : Fin N) :
    PartitionData.ScalarSmooth S.smoothStructure.val (fun p => j p i) := by
  intro p
  apply (scalarContDiffAt_iff (⊤ : ℕ∞) S.smoothStructure.val _ p).mpr
  refine ⟨(continuous_apply i).continuousAt.comp (embedded_map_continuousAt S j hj p), ?_⟩
  intro c hc hp
  obtain ⟨U, H, ⟨hU, hpU, hH, heH⟩, _⟩ := hj p c hc hp
  exact ⟨U, hU, hpU, fun z => H z i, (contDiffOn_pi.mp hH) i,
    heH.mono (fun _ h => congrFun h i)⟩

theorem embedded_oneform_regular :
    Specs.SmoothManifolds.Integration.ClassicalIntegralIdentifications.embedded_oneform_regularType := by
  intro n N a M _ S C j hj A hA T hT L hL F hF
  let hjc := embedded_coordinate_smooth S j hj
  let θ (i : Fin N) : Field S 1 := fun p =>
    (exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace S p))).symm
      (dFunction S (fun p => j p i) (hjc i) p)
  let ω : Field S 1 := ∑ i : Fin N, fun p => A p i • θ i p
  have hθ (i : Fin N) : ExteriorDerivativeData.IsRegularField C 1 1 (θ i) := by
    letI := (cotangentSpace C).topology
    obtain ⟨B⟩ := BundleOperations.exists_exterior (cotangentSpace C).bundle 1
    apply ExteriorDerivativeResults.smooth_regular C 1 B _ 1
    exact ExteriorDerivativeResults.oneForm_isForm C B _
      (Covectors.differential_smooth S C _ (hjc i))
  have hcoeff (i : Fin N) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) :
      LocallyContDiffAlong 1 (fun p : c.source => (c p.val).val) (fun p => A p.val i) := by
    intro p
    obtain ⟨U, hU, hpU, H, hH, heH⟩ := embedded_coefficients_regular S j hj A hA c hc p
    exact ⟨U, hU, hpU, fun z => H z i, (contDiffOn_pi.mp hH) i,
      fun q hq => congrFun (heH q hq) i⟩
  have hω : ExteriorDerivativeData.IsRegularField C 1 1 ω := by
    have hsum (s : Finset (Fin N)) : ExteriorDerivativeData.IsRegularField C 1 1
        (∑ i ∈ s, fun p => A p i • θ i p) := by
      induction s using Finset.induction_on with
      | empty => simpa using ExteriorDerivativeResults.regularField_zero C 1 1
      | @insert i s hi ih =>
        rw [Finset.sum_insert hi]
        exact ExteriorDerivativeResults.regularField_add C 1 1
          (regular_scalar_multiply S C 1 (θ i) (hθ i) (fun p => A p i) (hcoeff i)).1 ih
    exact hsum Finset.univ
  refine ⟨ω, hω, ?_, ?_⟩
  · apply closure_mono
    intro p hp hzero
    apply hp
    simp [ω, hzero]
  · intro p v
    have hdf (i : Fin N) : dFunction S (fun p => j p i) (hjc i) p v = F p (L p v) i := by
      obtain ⟨coords, hcoords, hFc⟩ := hF p
      rw [hFc]
      apply (hL p v (coords i) (functionGerm S (fun p => j p i) (hjc i) p)
        (fun x => x i) ?_ rfl).symm
      have hh : (fun y : Euclidean N => (EmbeddedData.euclideanChart N y).val i) =
          (fun y => y i) := by
        funext y
        rfl
      have hci := hcoords i
      rw [hh] at hci
      exact hci.symm
    simp only [ω, Finset.sum_apply, map_sum, map_smul, LinearEquiv.apply_symm_apply,
      LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, θ]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hdf i]

@[simp] theorem euclideanOneForm_apply {n N : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M)
    (J : (p : M) → TangentSpace S p →ₗ[ℝ] Euclidean N) (A : M → Euclidean N)
    (p : M) (v : TangentSpace S p) :
    (exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace S p))) (euclideanOneForm S J A p) v =
      ∑ i, A p i * J p v i := by
  simp [euclideanOneForm]

theorem euclidean_oneform_regular :
    Specs.SmoothManifolds.Integration.ClassicalIntegralIdentifications.euclidean_oneform_regularType := by
  intro n N a M _ S C j hj A hA T hT L hL F hF
  obtain ⟨ω, hω, hs, he⟩ := embedded_oneform_regular S C j hj A hA T hT L hL F hF
  have hfield : ω = euclideanOneForm S (fun p => (F p).toLinearMap.comp (L p)) A := by
    funext p
    apply (exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace S p))).injective
    apply LinearMap.ext
    intro v
    rw [he, euclideanOneForm_apply]
    rfl
  rw [hfield] at hω hs
  exact ⟨hω, hs, fun h => h.of_isClosed_subset isClosed_closure hs⟩

theorem ambient_coefficients_local :
    Specs.SmoothManifolds.Integration.ClassicalIntegralIdentifications.ambient_coefficients_localType.{u} := by
  intro N M j U hU hj A hA p
  exact ⟨U, hU, hj p, A, hA, fun _ _ => rfl⟩

/-- Coefficient continuity suffices for top-form continuity, without choosing
an exterior bundle or assuming a compact-top-form certificate. -/
theorem continuous_top_of_coefficients {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (ω : Field S n) (hω : ExteriorDerivativeData.IsContinuousField C n ω) :
    IsContinuousTopForm ω := by
  intro K c hc
  let L := C.tangent.fiberCoordinates
  have he (p : c.source) : topCoefficient K c hc p.val p.property ω =
      ∑ I : Index n n, coefficients C n c hc ω p I * MetricVolumeResults.wedgeWeight n I := by
    rw [LocalIntegrationResults.topCoefficient_coordinates_eq K L,
      topCoefficient_pairing]
    have hexp := ExteriorAlgebraResults.coefficient_expansion C n c hc ω p
    rw [hexp]
    simp only [pairing, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro I hI
    congr 1
    exact MetricVolumeResults.coordinate_wedge_pairing c hc p I
  apply Continuous.congr (continuous_finsetSum _ (fun I _ =>
    (hω c hc I).mul continuous_const))
  exact fun p => (he p).symm

theorem regular_top_form :
    Specs.SmoothManifolds.Integration.ClassicalIntegralIdentifications.regular_top_formType.{u} := by
  intro n a M _ S C ω hω hs
  exact ⟨⟨ω, continuous_top_of_coefficients C ω
    (ExteriorDerivativeResults.regular_continuous C n 1 ω hω), hs⟩, rfl⟩

theorem induced_metric_gram :
    Specs.SmoothManifolds.Integration.ClassicalIntegralIdentifications.induced_metric_gramType.{u} := by
  intro n N a M _ S C g J hJ K c hc p
  ext i j
  simp only [metricMatrix, embeddedGram, Matrix.of_apply, Pi.basisFun_apply,
    CovectorData.coordinateVector]
  exact hJ p.val _ _

theorem arc_length_factor :
    Specs.SmoothManifolds.Integration.ClassicalIntegralIdentifications.arc_length_factorType.{u} := by
  intro N a M _ S J K c hc p
  rw [Matrix.det_fin_one]
  simp only [embeddedGram, Matrix.of_apply, pow_two]

theorem surface_area_factor :
    Specs.SmoothManifolds.Integration.ClassicalIntegralIdentifications.surface_area_factorType.{u} := by
  intro N a M _ S J K c hc p
  dsimp only
  rw [Matrix.det_fin_two]
  simp only [embeddedGram, Matrix.of_apply, pow_two]
  congr 1
  rw [show (∑ l : Fin N,
      J p.val (CovectorData.coordinateVector K c hc p.val p.property 1) l *
      J p.val (CovectorData.coordinateVector K c hc p.val p.property 0) l) =
    ∑ l : Fin N,
      J p.val (CovectorData.coordinateVector K c hc p.val p.property 0) l *
      J p.val (CovectorData.coordinateVector K c hc p.val p.property 1) l from
    Finset.sum_congr rfl (fun _ _ => mul_comm _ _)]

/-- Exterior degree one is the ordinary covector evaluation. -/
theorem evaluate_one {V : Type u} [AddCommGroup V] [Module ℝ V]
    (α : Fiber V 1) (v : Fin 1 → V) :
    evaluate V 1 α v = (exteriorPower.oneEquiv ℝ (Module.Dual ℝ V)) α (v 0) := by
  let l := (exteriorPower.oneEquiv ℝ (Module.Dual ℝ V)) α
  have h : α = exteriorPower.ιMulti ℝ 1 (fun _ => l) := by
    apply (exteriorPower.oneEquiv ℝ (Module.Dual ℝ V)).injective
    simp only [exteriorPower.oneEquiv_ιMulti]
    rfl
  conv_lhs => rw [h]
  rw [ExteriorAlgebraResults.determinant_normalization, Matrix.det_fin_one]
  rfl

theorem line_topCoefficient {N : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold 1 a M) (K : FiberCoordinates S) (c : ModelChart 1 a M)
    (hc : c ∈ S.smoothStructure.val) (J : (p : M) → TangentSpace S p →ₗ[ℝ] Euclidean N)
    (A : M → Euclidean N) (p : c.source) :
    topCoefficient K c hc p.val p.property (euclideanOneForm S J A) =
      ∑ i, A p.val i * J p.val (CovectorData.coordinateVector K c hc p.val p.property 0) i := by
  unfold topCoefficient
  rw [evaluate_one, euclideanOneForm_apply]

theorem line_coefficient :
    Specs.SmoothManifolds.Integration.ClassicalIntegralIdentifications.line_coefficientType.{u} := by
  intro N a M _ S s K c hc J A
  funext x
  unfold signedCoordinateCoefficient lineIntegrand extendModel
  split_ifs with hx
  · dsimp only
    unfold modelSignedCoefficient
    split_ifs with ht
    · rw [line_topCoefficient S K c hc J A ⟨c.symm ⟨x, hx⟩, c.map_target ht⟩]
    · rfl
  · rfl

theorem line_integral :
    Specs.SmoothManifolds.Integration.ClassicalIntegralIdentifications.line_integralType.{u} := by
  intro N a M _ S C o J A hA hAc
  let η : CompactTopForm S := ⟨euclideanOneForm S J A,
    continuous_top_of_coefficients C _ hA, hAc⟩
  have hη : η.field = euclideanOneForm S J A := rfl
  refine ⟨η, hη, ?_⟩
  intro I hI s hs K
  constructor
  · intro c hc hsupport
    have he := line_coefficient S s K c hc J A
    refine ⟨?_, ?_⟩
    · have hi := LocalIntegrationResults.integrable S s K c hc η hsupport
      simpa only [hη, he] using hi
    · rw [hI.2.2 s hs K c hc η hsupport, coordinateIntegral, hη, he]
  · intro ι c hc ρ hρ
    rw [GlobalIntegrationResults.localization S o I hI s hs K c hc ρ η hρ]
    congr 1
    funext i
    have he : (fun p => ρ i p • η.field p) = euclideanOneForm S J (fun p => ρ i p • A p) := by
      rw [hη]
      funext p
      apply (exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace S p))).injective
      apply LinearMap.ext
      intro v
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, euclideanOneForm_apply,
        Pi.smul_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      ring
    rw [he, coordinateIntegral, line_coefficient S s K (c i) (hc i) J]

theorem parametrization_differential :
    Specs.SmoothManifolds.Integration.ClassicalIntegralIdentifications.parametrization_differentialType := by
  intro n N a M _ S j hj T hT p L F hL hF K c hc hp V H hH i
  have hh := differential_jacobian S T j (embedded_differential_exists S j hj T hT).1 p L hL
    c (EmbeddedData.euclideanChart N) hc hT hp (mem_univ _)
    (K.equiv c hc p hp) F (K.isCoordinates c hc p hp) hF
    V H hH.1 hH.2.1 hH.2.2.1 hH.2.2.2
      (CovectorData.coordinateVector K c hc p hp i)
  simpa only [CovectorData.coordinateVector, LinearEquiv.apply_symm_apply] using hh

theorem decomposable_smooth {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ) (B : FormBundle C k)
    (α : Fin k → CovectorField S) (hα : ∀ i, IsOneForm C (α i)) :
    IsForm B (fun p => exteriorPower.ιMulti ℝ k (fun i => α i p)) := by
  induction k with
  | zero =>
    apply (ExteriorAlgebraResults.smooth_iff_coefficients C 0 B _).mpr
    intro c hc I p
    have he : (fun q : c.source => coefficients C 0 c hc
        (fun p => exteriorPower.ιMulti ℝ 0 (fun i => α i p)) q I) = fun _ => (1 : ℝ) := by
      funext q
      simp [coefficients, exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
    rw [he]
    exact FrameData.VectorSmoothAt.const _ _ _
  | succ k ih =>
    letI := (cotangentSpace C).topology
    obtain ⟨D⟩ := BundleOperations.exists_exterior (cotangentSpace C).bundle k
    obtain ⟨E⟩ := BundleOperations.exists_exterior (cotangentSpace C).bundle 1
    have hβ := ih D (fun i : Fin k => α (Fin.castAdd 1 i)) (fun i => hα _)
    have hγ := ExteriorDerivativeResults.oneForm_isForm C E (α (Fin.last k)) (hα _)
    have hw := ExteriorAlgebraResults.wedge_smooth C k 1 D E B _ _ hβ hγ
    convert hw using 1
    funext p
    have he : (fun i : Fin (k+1) => α i p) =
        Fin.append (fun i : Fin k => α (Fin.castAdd 1 i) p) (fun _ : Fin 1 => α (Fin.last k) p) := by
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp
      · have hj : j = 0 := Fin.eq_zero j
        subst j
        simp only [Fin.append_right]
        congr 2
    have hone : (exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace S p))).symm
        (α (Fin.last k) p) = exteriorPower.ιMulti ℝ 1 (fun _ : Fin 1 => α (Fin.last k) p) := by
      apply (exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace S p))).injective
      simp
    rw [he]
    dsimp only [fieldWedge]
    rw [hone, ExteriorAlgebraResults.wedge_decomposable]
theorem embedded_coordinate_differential {n N : ℕ} {a : ModelKind} {M : Type}
    [TopologicalSpace M] (S : SmoothManifold n a M) (j : M → Euclidean N)
    (hj : EmbeddedData.HasFullRankParametrizations S j)
    (T : SmoothManifold N .euclidean (Euclidean N))
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (j p))
    (hL : ∀ p, DifferentialData.IsDifferential S T j p (L p))
    (F : (p : M) → TangentSpace T (j p) ≃ₗ[ℝ] Euclidean N)
    (hF : ∀ p, DifferentialData.IsChartCoordinates T (j p) (EmbeddedData.euclideanChart N) (F p))
    (p : M) (i : Fin N) :
    dFunction S (fun p => j p i) (embedded_coordinate_smooth S j hj i) p =
      (LinearMap.proj i).comp ((F p).toLinearMap.comp (L p)) := by
  apply LinearMap.ext
  intro v
  obtain ⟨coords, hcoords, hFc⟩ := hF p
  change dFunction S (fun p => j p i) (embedded_coordinate_smooth S j hj i) p v = F p (L p v) i
  rw [hFc]
  apply (hL p v (coords i)
    (functionGerm S (fun p => j p i) (embedded_coordinate_smooth S j hj i) p)
    (fun x => x i) ?_ rfl).symm
  have hh : (fun y : Euclidean N => (EmbeddedData.euclideanChart N y).val i) = (fun y => y i) := rfl
  have hci := hcoords i
  rw [hh] at hci
  exact hci.symm

theorem flux_evaluation :
    Specs.SmoothManifolds.Integration.ClassicalIntegralIdentifications.flux_evaluationType.{u} := by
  intro m N a M _ S J X p v
  simp only [euclideanFluxForm, map_sum, map_smul, _root_.sum_apply,
    smul_apply, smul_eq_mul]
  simp_rw [ExteriorAlgebraResults.determinant_normalization (TangentData.TangentSpace S p) N]
  rw [Matrix.det_succ_column_zero]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Matrix.of_apply, Fin.cons_zero, Matrix.submatrix_apply, Fin.cons_succ,
    LinearMap.comp_apply, LinearMap.proj_apply]
  congr 2

theorem euclidean_flux_regular :
    Specs.SmoothManifolds.Integration.ClassicalIntegralIdentifications.euclidean_flux_regularType := by
  intro m N a M _ S C j hj X hX T hT L hL F hF
  let J := fun p => (F p).toLinearMap.comp (L p)
  let α : Fin (N+1) → CovectorField S := fun i p => (LinearMap.proj i).comp (J p)
  have hα (i : Fin (N+1)) : IsOneForm C (α i) := by
    have h := Covectors.differential_smooth S C (fun p => j p i) (embedded_coordinate_smooth S j hj i)
    have he : dFunction S (fun p => j p i) (embedded_coordinate_smooth S j hj i) = α i := by
      funext p
      exact embedded_coordinate_differential S j hj T L hL F hF p i
    rw [he] at h
    exact h
  let β : Fin (N+1) → Field S N := fun i p => exteriorPower.ιMulti ℝ N (fun k => α (i.succAbove k) p)
  have hβ (i : Fin (N+1)) : ExteriorDerivativeData.IsRegularField C 1 N (β i) := by
    letI := (cotangentSpace C).topology
    obtain ⟨B⟩ := BundleOperations.exists_exterior (cotangentSpace C).bundle N
    exact ExteriorDerivativeResults.smooth_regular C N B _ 1
      (decomposable_smooth C N B (fun k => α (i.succAbove k)) (fun _ => hα _))
  have hcoeff (i : Fin (N+1)) (c : ModelChart m a M) (hc : c ∈ S.smoothStructure.val) :
      LocallyContDiffAlong 1 (fun p : c.source => (c p.val).val)
        (fun p => (-1 : ℝ)^i.val * X p.val i) := by
    intro p
    obtain ⟨U, hU, hpU, H, hH, heH⟩ := embedded_coefficients_regular S j hj X hX c hc p
    exact ⟨U, hU, hpU, fun z => (-1 : ℝ)^i.val * H z i,
      contDiffOn_const.mul ((contDiffOn_pi.mp hH) i),
      fun q hq => congrArg ((-1 : ℝ)^i.val * ·) (congrFun (heH q hq) i)⟩
  have hω : ExteriorDerivativeData.IsRegularField C 1 N (euclideanFluxForm S J X) := by
    have hsum (s : Finset (Fin (N+1))) : ExteriorDerivativeData.IsRegularField C 1 N
        (∑ i ∈ s, fun p => ((-1 : ℝ)^i.val * X p i) • β i p) := by
      induction s using Finset.induction_on with
      | empty => simpa using ExteriorDerivativeResults.regularField_zero C 1 N
      | @insert i s hi ih =>
        rw [Finset.sum_insert hi]
        exact ExteriorDerivativeResults.regularField_add C N 1
          (regular_scalar_multiply S C N (β i) (hβ i)
            (fun p => (-1 : ℝ)^i.val * X p i) (hcoeff i)).1 ih
    convert hsum Finset.univ using 1
    funext p
    simp only [euclideanFluxForm, Finset.sum_apply, β, α]
  have hs : ModelData.sectionSupport (euclideanFluxForm S J X) ⊆ ModelData.sectionSupport X := by
    apply closure_mono
    intro p hp hz
    apply hp
    simp [euclideanFluxForm, hz]
  exact ⟨hω, hs, fun h => h.of_isClosed_subset isClosed_closure hs⟩

theorem immersion_parametrizations :
    Specs.SmoothManifolds.Integration.ClassicalIntegralIdentifications.immersion_parametrizationsType := by
  intro n N a M _ S T hT j hj hImm p c hc hp
  obtain ⟨U, hU, hpU, H, hH, heH⟩ := (hj p).2 c hc (EmbeddedData.euclideanChart N) hT hp (mem_univ _)
  refine ⟨U, H, ⟨hU, hpU, hH, ?_⟩, ?_⟩
  · exact heH
  · obtain ⟨L, hL, _⟩ := differential_exists S T j hj p
    have hLi := ((MapClasses.smooth_tangent_invariants S T j hj p L hL).2.1).mp (hImm p)
    let E := coordinateDerivationEquiv S p c hc hp
    let F := coordinateDerivationEquiv T (j p) (EmbeddedData.euclideanChart N) hT (mem_univ _)
    have hJ (v : TangentSpace S p) : F (L v) = fderiv ℝ H (c p).val (E v) :=
      differential_jacobian S T j hj p L hL c (EmbeddedData.euclideanChart N) hc hT hp (mem_univ _)
        E F (coordinateDerivationEquiv_isChartCoordinates S p c hc hp)
        (coordinateDerivationEquiv_isChartCoordinates T (j p) (EmbeddedData.euclideanChart N) hT (mem_univ _))
        U H hU hpU hH heH v
    have hD : Function.Injective (fderiv ℝ H (c p).val).toLinearMap := by
      intro x y hxy
      have hv : L (E.symm x) = L (E.symm y) := by
        apply F.injective
        rw [hJ, hJ, E.apply_symm_apply, E.apply_symm_apply]
        exact hxy
      exact E.symm.injective (hLi hv)
    simpa [ModelData.Euclidean] using LinearMap.finrank_range_of_inj hD

theorem regular_domain_parametrizations :
    Specs.SmoothManifolds.Integration.ClassicalIntegralIdentifications.regular_domain_parametrizationsType := by
  intro n a T hT d S hD
  exact immersion_parametrizations S T hT Subtype.val hD.2.1 hD.2.2.2.1


open BundleMetricData FrameData Filter

private theorem realization_inverse_coordinate {n : ℕ} {a : ModelKind} {M : Type}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (c : TangentIndex S) (p : M) (hp : p ∈ c.val.source) (i : Fin n) :
    letI := C.realization.space.topology
    (C.realization.space.bundle.trivialization c).symm p (Pi.single i 1) =
      CovectorData.coordinateVector C.tangent.fiberCoordinates c.val c.property p hp i := by
  letI := C.realization.space.topology
  have hb : p ∈ C.realization.space.bundle.baseSet c := by rw [C.realization.baseSet]; exact hp
  have hE : C.realization.space.bundle.fiberCoordinates c p hb =
      C.tangent.fiberCoordinates.equiv c.val c.property p hp := by
    apply LinearEquiv.ext
    intro v
    exact C.realization.coordinates c p hp v
  change (C.realization.space.bundle.fiberCoordinates c p hb).symm (Pi.single i 1) = _
  rw [hE]
  rfl

private theorem oneform_triv_evaluation_smooth {n : ℕ} {a : ModelKind} {M : Type}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (α : CovectorField S) (hα : IsOneForm C α) (c : TangentIndex S) (i : Fin n)
    (p : M) (hp : p ∈ c.val.source) :
    letI := C.realization.space.topology
    VectorSmoothAt S.smoothStructure.val
      (fun q => α q ((C.realization.space.bundle.trivialization c).symm q (Pi.single i 1))) p := by
  letI := C.realization.space.topology
  letI := (cotangentSpace C).topology
  have hc := Frames.trivializationCoordinates_smoothAt (cotangentSpace C).bundle c
    (⟨p, α p⟩ : Bundle.TotalSpace (Euclidean n) (CotangentFiber S))
    (by rw [Covectors.cotangent_baseSet]; exact hp)
  have hs := hc.comp (g := fun q => (⟨q, α q⟩ : Bundle.TotalSpace (Euclidean n) (CotangentFiber S)))
    (cotangentSpace C).bundle.totalManifold.smoothStructure.property.1.1 (hα p)
  have hi := hs.postcomp (contDiff_apply ℝ (fun _ : Fin n => ℝ) i)
  apply hi.congr
  filter_upwards [c.val.open_source.mem_nhds hp] with q hq
  rw [Covectors.cotangent_coordinates C c.val c.property q hq (α q)]
  rw [realization_inverse_coordinate C c q hq]

private def metricOfSmoothCovectors {n N : ℕ} {a : ModelKind} {M : Type}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (α : Fin N → CovectorField S) (hα : ∀ i, IsOneForm C (α i))
    (hpos : ∀ p (v : TangentSpace S p), v ≠ 0 → (fun i => α i p v) ≠ 0) : Metric C := by
  letI := C.realization.space.topology
  refine {
  form p := ∑ i, LinearMap.BilinForm.linMulLin (α i p) (α i p)
  symmetric p v w := by simp only [LinearMap.sum_apply, LinearMap.BilinForm.linMulLin_apply, mul_comm]
  positive p v hv := by
    simp only [LinearMap.sum_apply, LinearMap.BilinForm.linMulLin_apply]
    exact lt_of_le_of_ne (Finset.sum_nonneg (fun i _ => mul_self_nonneg _))
      (Ne.symm (dotProduct_self_eq_zero.not.mpr (hpos p v hv)))
  smooth c i j p hp := by
    letI := C.realization.space.topology
    have hpc : p ∈ c.val.source := by rwa [C.realization.baseSet] at hp
    simp only [LinearMap.sum_apply, LinearMap.BilinForm.linMulLin_apply]
    apply VectorSmoothAt.sum
    intro l
    exact ((oneform_triv_evaluation_smooth C (α l) (hα l) c i p hpc).prod
      (oneform_triv_evaluation_smooth C (α l) (hα l) c j p hpc)).postcomp
      (contDiff_fst.mul contDiff_snd)
  }

 theorem induced_metric_exists {n N : ℕ} {a : ModelKind} {M : Type}
    [TopologicalSpace M] (S : SmoothManifold n a M) (C : CotangentBundle S)
    (j : M → Euclidean N) (hj : EmbeddedData.HasFullRankParametrizations S j)
    (T : SmoothManifold N .euclidean (Euclidean N))
    (hT : EmbeddedData.euclideanChart N ∈ T.smoothStructure.val)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (j p))
    (hL : ∀ p, DifferentialData.IsDifferential S T j p (L p))
    (F : (p : M) → TangentSpace T (j p) ≃ₗ[ℝ] Euclidean N)
    (hF : ∀ p, DifferentialData.IsChartCoordinates T (j p) (EmbeddedData.euclideanChart N) (F p)) :
    ∃ g : Metric C, ∀ p v w, metricForm g p v w = ∑ i, F p (L p v) i * F p (L p w) i := by
  let α : Fin N → CovectorField S := fun i =>
    dFunction S (fun p => j p i) (embedded_coordinate_smooth S j hj i)
  have hα (i : Fin N) : IsOneForm C (α i) :=
    Covectors.differential_smooth S C (fun p => j p i) (embedded_coordinate_smooth S j hj i)
  have he (i : Fin N) (p : M) (v : TangentSpace S p) : α i p v = F p (L p v) i := by
    change dFunction S (fun p => j p i) (embedded_coordinate_smooth S j hj i) p v = _
    rw [embedded_coordinate_differential S j hj T L hL F hF p i]
    rfl
  have hpos (p : M) (v : TangentSpace S p) (hv : v ≠ 0) : (fun i => α i p v) ≠ 0 := by
    intro hz
    apply hv
    apply (embedded_tangent_comparison S j hj T hT p (L p) (F p) (hL p) (hF p)).2.1
    ext i
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, map_zero, Pi.zero_apply, ← he i p v]
      using congrFun hz i
  refine ⟨metricOfSmoothCovectors C α hα hpos, ?_⟩
  intro p v w
  simp only [metricForm, metricOfSmoothCovectors, LinearMap.sum_apply,
    LinearMap.BilinForm.linMulLin_apply, he]

theorem gramIntegrand_induced {n N : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (C : CotangentBundle S) (g : Metric C)
    (J : (p : M) → TangentSpace S p →ₗ[ℝ] Euclidean N)
    (hJ : ∀ p v w, metricForm g p v w = ∑ i, J p v i * J p w i)
    (K : FiberCoordinates S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (f : M → ℝ) : gramIntegrand g K c hc f = surfaceIntegrand J K c hc f := by
  funext x
  unfold gramIntegrand surfaceIntegrand
  congr 1
  funext y
  split_ifs with hy
  · rw [induced_metric_gram S C g J hJ]
  · rfl

theorem parametrization_gram {n N : ℕ} {a : ModelKind} {M : Type}
    [TopologicalSpace M] (S : SmoothManifold n a M) (j : M → Euclidean N)
    (hj : EmbeddedData.HasFullRankParametrizations S j)
    (T : SmoothManifold N .euclidean (Euclidean N))
    (hT : EmbeddedData.euclideanChart N ∈ T.smoothStructure.val)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (j p))
    (hL : ∀ p, DifferentialData.IsDifferential S T j p (L p))
    (F : (p : M) → TangentSpace T (j p) ≃ₗ[ℝ] Euclidean N)
    (hF : ∀ p, DifferentialData.IsChartCoordinates T (j p) (EmbeddedData.euclideanChart N) (F p))
    (K : FiberCoordinates S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (p : c.source) (V : Set (Euclidean n)) (H : Euclidean n → Euclidean N)
    (hH : EmbeddedData.IsParametrizationAt j c p.val V H) :
    embeddedGram (fun q => (F q).toLinearMap.comp (L q)) K c hc p =
      Matrix.of (fun i k : Fin n => ∑ l : Fin N,
        fderiv ℝ H (c p.val).val (Pi.single i 1) l *
        fderiv ℝ H (c p.val).val (Pi.single k 1) l) := by
  ext i k
  simp only [embeddedGram, Matrix.of_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [parametrization_differential S j hj T hT p.val (L p.val) (F p.val)
    (hL p.val) (hF p.val) K c hc p.property V H hH i,
    parametrization_differential S j hj T hT p.val (L p.val) (F p.val)
    (hL p.val) (hF p.val) K c hc p.property V H hH k]

theorem embedded_surface_integral :
    Specs.SmoothManifolds.Integration.ClassicalIntegralIdentifications.embedded_surface_integralType := by
  intro n N a M _ S C D o j hj T hT L hL F hF f hf hfc
  obtain ⟨g, hg⟩ := induced_metric_exists S C j hj T hT L hL F hF
  obtain ⟨ω, hω, _⟩ := MetricVolumeResults.volume_exists_unique S C D g o
  let η := scalarVolumeForm C D g o ω hω f hf hfc
  refine ⟨g, hg, ω, hω, η, rfl, ?_⟩
  intro I hI K
  have hJ : ∀ p v w, metricForm g p v w =
      ∑ i, ((F p).toLinearMap.comp (L p)) v i * ((F p).toLinearMap.comp (L p)) w i := hg
  obtain ⟨s, hs, _⟩ := LocalIntegrationResults.orientation_signs S o
  have he (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (f' : M → ℝ) :
      signedCoordinateCoefficient s K c hc (scalarVolume f' ω.field) =
        surfaceIntegrand (fun p => (F p).toLinearMap.comp (L p)) K c hc f' := by
    rw [scalar_volume_coefficient S C D g o ω hω s hs K c hc f',
      gramIntegrand_induced S C g _ hJ]
  constructor
  · intro c hc hsupport
    have hη : sectionSupport η.field ⊆ c.source :=
      fun _ hp => hsupport ((GlobalIntegrationResults.weight_support S n ω.field f hp).1)
    refine ⟨?_, ?_⟩
    · have hi := LocalIntegrationResults.integrable S s K c hc η hη
      simpa only [η, scalarVolumeForm, he] using hi
    · rw [hI.2.2 s hs K c hc η hη, coordinateIntegral]
      change (∫ x, signedCoordinateCoefficient s K c hc (scalarVolume f ω.field) x) = _
      rw [he]
  · intro ι c hc ρ hρ
    rw [GlobalIntegrationResults.localization S o I hI s hs K c hc ρ η hρ]
    congr 1
    funext i
    have hfield : (fun p => ρ i p • η.field p) =
        scalarVolume (fun p => ρ i p * f p) ω.field := by
      funext p
      simp only [η, scalarVolumeForm, scalarVolume, mul_smul]
    rw [hfield, coordinateIntegral, he]


theorem zero_flux_field {m : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold m a M)
    (J : (p : M) → TangentSpace S p →ₗ[ℝ] Euclidean 1) (X : M → Euclidean 1) :
    euclideanFluxForm (N := 0) S J X = scalarField S (fun p => X p 0) := by
  funext p
  apply (exteriorPower.zeroEquiv ℝ (Module.Dual ℝ (TangentSpace S p))).injective
  simp [euclideanFluxForm, scalarField]

theorem zero_vector_support {M : Type u} [TopologicalSpace M] (X : M → Euclidean 1) :
    ModelData.sectionSupport (fun p => X p 0) = ModelData.sectionSupport X := by
  unfold ModelData.sectionSupport
  congr 1
  ext p
  change (X p 0 ≠ 0) ↔ X p ≠ 0
  have hz : X p = 0 ↔ X p 0 = 0 := by
    constructor
    · intro h
      rw [h]
      rfl
    · intro h
      funext i
      have hi : i = 0 := Fin.eq_zero i
      simpa [hi] using h
  exact not_congr hz.symm

theorem zero_flux_metric {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold 0 a M) (C : CotangentBundle S) (D : FormBundle C 0)
    (g : Metric C) (o : Orientation S) (ω : Form D) (hω : IsMetricVolume g o ω)
    (J : (p : M) → TangentSpace S p →ₗ[ℝ] Euclidean 1) (X : M → Euclidean 1) :
    euclideanFluxForm (N := 0) S J X = scalarVolume (fun p => zeroSign o p * X p 0) ω.field := by
  rw [zero_flux_field]
  funext p
  apply (exteriorPower.zeroEquiv ℝ (Module.Dual ℝ (TangentSpace S p))).injective
  have he := zero_volume_coefficient C D g o ω hω p
  change exteriorPower.zeroEquiv ℝ (Module.Dual ℝ (TangentSpace S p)) _ = _ at he
  simp only [scalarField, LinearEquiv.apply_symm_apply, scalarVolume, map_smul,
    smul_eq_mul, he]
  unfold zeroSign
  split_ifs <;> ring

theorem zero_flux_integral {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold 0 a M) (o : Orientation S)
    (J : (p : M) → TangentSpace S p →ₗ[ℝ] Euclidean 1)
    (X : M → Euclidean 1) (hX : Continuous X) (hXc : IsCompact (ModelData.sectionSupport X)) :
    ∃ η : CompactTopForm S, η.field = euclideanFluxForm (N := 0) S J X ∧
      ∀ I : CompactTopForm S → ℝ, IsIntegral o I →
      ∃ h : (ModelData.sectionSupport X).Finite,
        I η = ∑ p ∈ h.toFinset, zeroSign o p * X p 0 := by
  have hs := zero_vector_support X
  have hc : IsCompact (ModelData.sectionSupport (fun p => X p 0)) := hs.symm ▸ hXc
  obtain ⟨η, hη, hI⟩ := zero_scalar_integral S o (fun p => X p 0)
    ((continuous_apply 0).comp hX) hc
  refine ⟨η, hη.trans (zero_flux_field S J X).symm, ?_⟩
  intro I hI'
  obtain ⟨h, he⟩ := hI I hI'
  refine ⟨hs ▸ h, ?_⟩
  have hfin : h.toFinset = (hs ▸ h).toFinset := by
    ext p
    simp only [Set.Finite.mem_toFinset]
    exact Set.ext_iff.mp hs p
  rw [← hfin]
  exact he



open MapData DifferentialData EmbeddedData RegularDomainData

def parametrizationMap {n N : ℕ} {a : ModelKind} {M : Type} [TopologicalSpace M]
    (j : M → Euclidean N) (c : ModelChart n a M) (x : Euclidean n) : Euclidean N :=
  if hx : x ∈ modelSet n a then j (c.symm ⟨x, hx⟩) else 0

@[simp] theorem parametrizationMap_at {n N : ℕ} {a : ModelKind} {M : Type}
    [TopologicalSpace M] (j : M → Euclidean N) (c : ModelChart n a M)
    (x : ModelSpace n a) : parametrizationMap j c x.val = j (c.symm x) := by
  simp [parametrizationMap, x.property]

theorem parametrizationMap_derivative {n N : ℕ} {a : ModelKind} {M : Type}
    [TopologicalSpace M] (j : M → Euclidean N) (c : ModelChart n a M)
    (p : M) (hp : p ∈ c.source) (V : Set (Euclidean n))
    (H : Euclidean n → Euclidean N) (hH : IsParametrizationAt j c p V H) :
    HasFDerivWithinAt (parametrizationMap j c) (fderiv ℝ H (c p).val)
      (Subtype.val '' c.target) (c p).val := by
  obtain ⟨hV, hpV, hd, he⟩ := hH
  have ht : Tendsto c.symm (𝓝 (c p)) (𝓝 p) := by
    simpa only [ContinuousAt, c.left_inv hp] using c.symm.continuousAt (c.map_source hp)
  have hmodel : (fun z : ModelSpace n a => parametrizationMap j c z.val) =ᶠ[𝓝 (c p)]
      (fun z => H z.val) := by
    filter_upwards [he.comp_tendsto ht, c.open_target.mem_nhds (c.map_source hp)] with z hz hzt
    rw [parametrizationMap_at]
    change H (c (c.symm z)).val = j (c.symm z) at hz
    rw [c.right_inv hzt] at hz
    exact hz.symm
  have hamb : parametrizationMap j c =ᶠ[𝓝[modelSet n a] (c p).val] H := by
    rw [← map_nhds_subtype_val (c p)]
    exact hmodel
  have hsub : Subtype.val '' c.target ⊆ modelSet n a := by
    rintro x ⟨y, hy, rfl⟩
    exact y.property
  exact (((hd.differentiableOn (by simp) _ hpV).differentiableAt
    (hV.mem_nhds hpV)).hasFDerivAt.hasFDerivWithinAt).congr_of_eventuallyEq
      (hamb.filter_mono (nhdsWithin_mono _ hsub))
      (by simp only [parametrizationMap_at, c.left_inv hp]; exact he.eq_of_nhds.symm)

theorem sqrt_gram_det {n : ℕ} (D : Euclidean n →L[ℝ] Euclidean n) :
    Real.sqrt (Matrix.of (fun i j : Fin n =>
      ∑ l : Fin n, D (Pi.single i 1) l * D (Pi.single j 1) l)).det = |D.det| := by
  let A := LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin n)) D.toLinearMap
  have hA (i j : Fin n) : A i j = D (Pi.single j 1) i := by
    simp [A, LinearMap.toMatrix_apply]
  have hG : Matrix.of (fun i j : Fin n =>
      ∑ l : Fin n, D (Pi.single i 1) l * D (Pi.single j 1) l) = A.transpose * A := by
    ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, hA]
  rw [hG, Matrix.det_mul, Matrix.det_transpose]
  have hdet : A.det = D.det := by
    exact LinearMap.det_toMatrix (Pi.basisFun ℝ (Fin n)) D.toLinearMap
  rw [hdet, ← pow_two, Real.sqrt_sq_eq_abs]


-- Geometry and differentiation of chart inverse into an actual Euclidean subset.
theorem euclidean_chart_geometry {n : ℕ} {a : ModelKind} (d : Set (Euclidean n))
    (c : ModelChart n a d) :
    InjOn (parametrizationMap (Subtype.val : d → Euclidean n) c) (Subtype.val '' c.target) ∧
      parametrizationMap (Subtype.val : d → Euclidean n) c '' (Subtype.val '' c.target) =
        (Subtype.val : d → Euclidean n) '' c.source := by
  constructor
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ he
    rw [parametrizationMap_at, parametrizationMap_at] at he
    have hxy : c.symm x = c.symm y := Subtype.ext he
    exact congrArg Subtype.val (c.symm.injOn hx hy hxy)
  · ext z
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      rw [parametrizationMap_at]
      exact ⟨c.symm y, c.map_target hy, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      refine ⟨(c p).val, ⟨c p, c.map_source hp, rfl⟩, ?_⟩
      rw [parametrizationMap_at, c.left_inv hp]

theorem euclidean_chart_derivative {n : ℕ} {a : ModelKind} (d : Set (Euclidean n))
    (S : SmoothManifold n a d) (K : FiberCoordinates S)
    (c : ModelChart n a d) (hc : c ∈ S.smoothStructure.val)
    (J : (p : d) → TangentSpace S p →ₗ[ℝ] Euclidean n)
    (hparam : ∀ (p : d) (hp : p ∈ c.source),
      ∃ (V : Set (Euclidean n)) (H : Euclidean n → Euclidean n),
        IsParametrizationAt Subtype.val c p V H ∧
        ∀ i : Fin n, J p (CovectorData.coordinateVector K c hc p hp i) =
          fderiv ℝ H (c p).val (Pi.single i 1)) :
    let ψ := parametrizationMap (Subtype.val : d → Euclidean n) c
    let U := Subtype.val '' c.target
    let D := fderivWithin ℝ ψ U
    (∀ x ∈ U, HasFDerivWithinAt ψ (D x) U x) ∧
    (∀ (y : ModelSpace n a) (hy : y ∈ c.target) (i : Fin n),
      J (c.symm y) (CovectorData.coordinateVector K c hc (c.symm y) (c.map_target hy) i) =
        D y.val (Pi.single i 1)) := by
  dsimp only
  constructor
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨V, H, hpH, hi⟩ := hparam (c.symm y) (c.map_target hy)
    have hd := parametrizationMap_derivative Subtype.val c (c.symm y) (c.map_target hy) V H hpH
    rw [c.right_inv hy] at hd
    exact hd.differentiableWithinAt.hasFDerivWithinAt
  · intro y hy i
    obtain ⟨V, H, hpH, hi⟩ := hparam (c.symm y) (c.map_target hy)
    have hd := parametrizationMap_derivative Subtype.val c (c.symm y) (c.map_target hy) V H hpH
    rw [c.right_inv hy] at hd
    rw [hd.fderivWithin (uniqueDiffOn_modelDomain c.open_target _ ⟨y, hy, rfl⟩)]
    simpa only [c.right_inv hy] using hi i


@[simp] theorem extendScalar_at {n : ℕ} (d : Set (Euclidean n)) (f : d → ℝ) (p : d) :
    extendScalar d f p.val = f p := by simp [extendScalar, p.property]

theorem euclidean_chart_gram_substitution {n : ℕ} {a : ModelKind} (d : Set (Euclidean n))
    (S : SmoothManifold n a d) (C : CotangentBundle S) (g : Metric C)
    (K : FiberCoordinates S) (c : ModelChart n a d) (hc : c ∈ S.smoothStructure.val)
    (J : (p : d) → TangentSpace S p →ₗ[ℝ] Euclidean n)
    (hmetric : ∀ p v w, metricForm g p v w = ∑ i, J p v i * J p w i)
    (hparam : ∀ (p : d) (hp : p ∈ c.source),
      ∃ (V : Set (Euclidean n)) (H : Euclidean n → Euclidean n),
        IsParametrizationAt Subtype.val c p V H ∧
        ∀ i : Fin n, J p (CovectorData.coordinateVector K c hc p hp i) =
          fderiv ℝ H (c p).val (Pi.single i 1)) (f : d → ℝ) :
    ((∫ x, gramIntegrand g K c hc f x) =
      ∫ x in (Subtype.val : d → Euclidean n) '' c.source, extendScalar d f x) ∧
    (Integrable (gramIntegrand g K c hc f) ↔
      IntegrableOn (extendScalar d f) ((Subtype.val : d → Euclidean n) '' c.source)) := by
  let ψ := parametrizationMap (Subtype.val : d → Euclidean n) c
  let U := Subtype.val '' c.target
  let D := fderivWithin ℝ ψ U
  obtain ⟨hD, hDc⟩ := euclidean_chart_derivative d S K c hc J hparam
  have hU : MeasurableSet U := LocalIntegrationResults.ambientDomain_measurable c.open_target
  have hgeometry := euclidean_chart_geometry d c
  have hGram (y : ModelSpace n a) (hy : y ∈ c.target) :
      Real.sqrt (metricMatrix g K c hc ⟨c.symm y, c.map_target hy⟩).det = |(D y.val).det| := by
    have hG : metricMatrix g K c hc ⟨c.symm y, c.map_target hy⟩ =
        Matrix.of (fun i j : Fin n => ∑ l : Fin n,
          D y.val (Pi.single i 1) l * D y.val (Pi.single j 1) l) := by
      ext i j
      simp only [metricMatrix, Matrix.of_apply, Pi.basisFun_apply]
      rw [hmetric]
      change (∑ l, J (c.symm y) (CovectorData.coordinateVector K c hc (c.symm y) (c.map_target hy) i) l *
        J (c.symm y) (CovectorData.coordinateVector K c hc (c.symm y) (c.map_target hy) j) l) = _
      rw [hDc y hy i, hDc y hy j]
    rw [hG, sqrt_gram_det]
  have hcoeff : ∀ x ∈ U,
      gramIntegrand g K c hc f x = |(D x).det| * extendScalar d f (ψ x) := by
    rintro _ ⟨y, hy, rfl⟩
    simp only [gramIntegrand, extendModel, y.property, dite_true, hy, ψ, parametrizationMap_at,
      extendScalar_at, hGram y hy]
    exact mul_comm _ _
  have hsupp : Function.support (gramIntegrand g K c hc f) ⊆ U := by
    intro x hx
    change gramIntegrand g K c hc f x ≠ 0 at hx
    unfold gramIntegrand extendModel at hx
    dsimp only at hx
    split_ifs at hx with hm ht
    · exact ⟨⟨x, hm⟩, ht, rfl⟩
    · exact (hx rfl).elim
    · exact (hx rfl).elim
  have hint : (∫ x in U, gramIntegrand g K c hc f x) = ∫ x, gramIntegrand g K c hc f x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx =>
      not_not.mp (fun hn => hx (hsupp hn)))
  have hsub := integral_image_eq_integral_abs_det_fderiv_smul volume hU hD hgeometry.1
    (extendScalar d f)
  rw [hgeometry.2] at hsub
  constructor
  · rw [← hint, hsub]
    exact setIntegral_congr_fun hU (fun x hx => hcoeff x hx)
  · have hi := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hU hD hgeometry.1
      (extendScalar d f)
    rw [hgeometry.2] at hi
    constructor
    · intro h
      apply hi.mpr
      exact h.integrableOn.congr_fun (fun x hx => hcoeff x hx) hU
    · intro h
      apply (integrableOn_iff_integrable_of_support_subset hsupp).mp
      exact (hi.mp h).congr_fun (fun x hx => (hcoeff x hx).symm) hU


theorem extendScalar_support {n : ℕ} {a : ModelKind} (d : Set (Euclidean n))
    (c : ModelChart n a d) (f : d → ℝ) (hfs : ModelData.sectionSupport f ⊆ c.source) :
    Function.support (extendScalar d f) ⊆ (Subtype.val : d → Euclidean n) '' c.source := by
  intro x hx
  change extendScalar d f x ≠ 0 at hx
  by_cases hxd : x ∈ d
  · refine ⟨⟨x, hxd⟩, hfs (subset_closure ?_), rfl⟩
    change f ⟨x, hxd⟩ ≠ 0
    simpa only [extendScalar, dite_true, hxd] using hx
  · simp [extendScalar, hxd] at hx

theorem euclidean_chart_gram_supported {n : ℕ} {a : ModelKind} (d : Set (Euclidean n))
    (S : SmoothManifold n a d) (C : CotangentBundle S) (g : Metric C)
    (K : FiberCoordinates S) (c : ModelChart n a d) (hc : c ∈ S.smoothStructure.val)
    (J : (p : d) → TangentSpace S p →ₗ[ℝ] Euclidean n)
    (hmetric : ∀ p v w, metricForm g p v w = ∑ i, J p v i * J p w i)
    (hparam : ∀ (p : d) (hp : p ∈ c.source),
      ∃ (V : Set (Euclidean n)) (H : Euclidean n → Euclidean n),
        IsParametrizationAt Subtype.val c p V H ∧
        ∀ i : Fin n, J p (CovectorData.coordinateVector K c hc p hp i) =
          fderiv ℝ H (c p).val (Pi.single i 1))
    (f : d → ℝ) (hfs : ModelData.sectionSupport f ⊆ c.source) :
    ((∫ x, gramIntegrand g K c hc f x) = ∫ x, extendScalar d f x) ∧
      (Integrable (gramIntegrand g K c hc f) ↔ Integrable (extendScalar d f)) := by
  obtain ⟨heq, hint⟩ := euclidean_chart_gram_substitution d S C g K c hc J hmetric hparam f
  have hs := extendScalar_support d c f hfs
  have hi := setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume)
    (fun x hx => not_not.mp (fun hn => hx (hs hn)))
  rw [hi] at heq
  exact ⟨heq, hint.trans (integrableOn_iff_integrable_of_support_subset hs)⟩


theorem regular_domain_scalar_local {n : ℕ} {a : ModelKind}
    (T : SmoothManifold n .euclidean (Euclidean n)) (hT : euclideanChart n ∈ T.smoothStructure.val)
    (d : Set (Euclidean n)) (S : SmoothManifold n a d) (hreg : IsRegularDomain T d S)
    (C : CotangentBundle S) (B : FormBundle C n) (g : Metric C)
    (o : Orientation S) (ω : Form B) (hω : IsMetricVolume g o ω)
    (L : (p : d) → TangentSpace S p →ₗ[ℝ] TangentSpace T p.val)
    (hL : ∀ p, IsDifferential S T Subtype.val p (L p))
    (F : (p : d) → TangentSpace T p.val ≃ₗ[ℝ] Euclidean n)
    (hF : ∀ p, IsChartCoordinates T p.val (euclideanChart n) (F p))
    (hmetric : ∀ p v w, metricForm g p v w = ∑ i, F p (L p v) i * F p (L p w) i)
    (I : CompactTopForm S → ℝ) (hI : IsIntegral o I)
    (f : d → ℝ) (hf : Continuous f) (hfc : IsCompact (ModelData.sectionSupport f))
    (K : FiberCoordinates S) (c : ModelChart n a d) (hc : c ∈ S.smoothStructure.val)
    (hfs : ModelData.sectionSupport f ⊆ c.source) :
    Integrable (extendScalar d f) ∧
      I (ClassicalIntegralResults.scalarVolumeForm C B g o ω hω f hf hfc) =
        ∫ x, extendScalar d f x := by
  let J := fun p => (F p).toLinearMap.comp (L p)
  have hj := ClassicalIntegralResults.regular_domain_parametrizations T hT d S hreg
  have hparam : ∀ (p : d) (hp : p ∈ c.source),
      ∃ (V : Set (Euclidean n)) (H : Euclidean n → Euclidean n),
        IsParametrizationAt Subtype.val c p V H ∧
        ∀ i : Fin n, J p (CovectorData.coordinateVector K c hc p hp i) =
          fderiv ℝ H (c p).val (Pi.single i 1) := by
    intro p hp
    obtain ⟨V, H, hH, _⟩ := hj p c hc hp
    refine ⟨V, H, hH, ?_⟩
    intro i
    exact ClassicalIntegralResults.parametrization_differential S Subtype.val hj T hT p (L p) (F p)
      (hL p) (hF p) K c hc hp V H hH i
  have hmet : ∀ p v w, metricForm g p v w = ∑ i, J p v i * J p w i := hmetric
  obtain ⟨heq, hint⟩ := euclidean_chart_gram_supported d S C g K c hc J hmet hparam f hfs
  let η := ClassicalIntegralResults.scalarVolumeForm C B g o ω hω f hf hfc
  obtain ⟨s, hs, _⟩ := LocalIntegrationResults.orientation_signs S o
  have hη : ModelData.sectionSupport η.field ⊆ c.source :=
    fun _ hp => hfs ((GlobalIntegrationResults.weight_support S n ω.field f hp).1)
  have he := ClassicalIntegralResults.scalar_volume_coefficient S C B g o ω hω s hs K c hc f
  have hi := LocalIntegrationResults.integrable S s K c hc η hη
  have hgram : Integrable (gramIntegrand g K c hc f) := by
    simpa only [η, ClassicalIntegralResults.scalarVolumeForm, he] using hi
  refine ⟨hint.mp hgram, ?_⟩
  rw [hI.2.2 s hs K c hc η hη]
  change (∫ x, signedCoordinateCoefficient s K c hc (scalarVolume f ω.field) x) = _
  rw [he, heq]


theorem metric_volume_ne_zero {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (D : FormBundle C n)
    (g : Metric C) (o : Orientation S) (ω : Form D) (hω : IsMetricVolume g o ω)
    (p : M) : ω.field p ≠ 0 := by
  obtain ⟨s, hs, _⟩ := LocalIntegrationResults.orientation_signs S o
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
  let K := C.tangent.fiberCoordinates
  have hpos := ((MetricVolumeResults.gram S C g K c hc).1 ⟨p, hp⟩).2
  have hsqrt := Real.sqrt_pos.mpr hpos
  have ht := volume_topCoefficient C D g o ω hω s hs K c hc ⟨p, hp⟩
  intro hz
  have hzero : topCoefficient K c hc p hp ω.field = 0 := by
    simp [topCoefficient, hz]
  rw [hzero] at ht
  cases he : s.sign c hc ⟨p, hp⟩ <;> simp [he, signValue] at ht <;> linarith

/-- Nonvanishing of metric volume gives the exact scalar support. -/
theorem scalarVolume_support {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (D : FormBundle C n)
    (g : Metric C) (o : Orientation S) (ω : Form D) (hω : IsMetricVolume g o ω)
    (f : M → ℝ) : sectionSupport (scalarVolume f ω.field) = sectionSupport f := by
  unfold sectionSupport
  have hs : {p | scalarVolume f ω.field p ≠ 0} = {p | f p ≠ 0} := by
    ext p
    simp [scalarVolume, metric_volume_ne_zero C D g o ω hω p]
  exact congrArg closure hs

private theorem scalar_integral_global_of_local {n : ℕ} {a : ModelKind}
    (d : Set (Euclidean n)) (S : SmoothManifold n a d)
    (C : CotangentBundle S) (D : FormBundle C n)
    (g : Metric C) (o : Orientation S) (ω : Form D) (hω : IsMetricVolume g o ω)
    (I : CompactTopForm S → ℝ) (hI : IsIntegral o I)
    (hlocal : ∀ (f : d → ℝ) (hf : Continuous f) (hfc : IsCompact (sectionSupport f))
      (c : ModelChart n a d) (hc : c ∈ S.smoothStructure.val),
      sectionSupport f ⊆ c.source → Integrable (extendScalar d f) ∧
        I (scalarVolumeForm C D g o ω hω f hf hfc) = ∫ x, extendScalar d f x)
    (f : d → ℝ) (hf : Continuous f) (hfc : IsCompact (sectionSupport f)) :
    Integrable (extendScalar d f) ∧
      I (scalarVolumeForm C D g o ω hω f hf hfc) = ∫ x, extendScalar d f x := by
  let η := scalarVolumeForm C D g o ω hω f hf hfc
  obtain ⟨ρ, hρ⟩ := GlobalIntegrationResults.exists_chart_localization S η
  let c : {c : ModelChart n a d // c ∈ S.smoothStructure.val} → ModelChart n a d := fun c => c.val
  obtain ⟨t, ht, hsum⟩ := GlobalIntegrationResults.localization_decomposition c ρ η hρ
  let f' (i : {c : ModelChart n a d // c ∈ S.smoothStructure.val}) : d → ℝ := fun p => ρ i p * f p
  have hf' (i) : Continuous (f' i) := (hρ.1 i).mul hf
  have hfc' (i) : IsCompact (sectionSupport (f' i)) :=
    hfc.of_isClosed_subset isClosed_closure tsupport_mul_subset_right
  have hsupport (i) : sectionSupport (f' i) ⊆ (c i).source :=
    tsupport_mul_subset_left.trans (hρ.2.2.1 i)
  have hloc (i) := hlocal (f' i) (hf' i) (hfc' i) (c i) i.property (hsupport i)
  let ζ := fun i => scalarVolumeForm C D g o ω hω (f' i) (hf' i) (hfc' i)
  have hζsum : η.field = ∑ i ∈ t, (ζ i).field := by
    convert hsum using 1
    apply Finset.sum_congr rfl
    intro i hi
    funext p
    simp only [ζ, η, scalarVolumeForm, scalarVolume, f', mul_smul]
  have hfsum : f = ∑ i ∈ t, f' i := by
    funext p
    apply smul_left_injective ℝ (metric_volume_ne_zero C D g o ω hω p)
    simpa only [η, ζ, scalarVolumeForm, scalarVolume, Finset.sum_apply,
      Finset.sum_smul] using congrFun hζsum p
  have hext : extendScalar d f = fun x => ∑ i ∈ t, extendScalar d (f' i) x := by
    funext x
    unfold extendScalar
    split_ifs with hx
    · simpa only [Finset.sum_apply, dif_pos hx] using congrFun hfsum ⟨x, hx⟩
    · simp [Finset.sum_apply, hx]
  refine ⟨?_, ?_⟩
  · rw [hext]
    exact integrable_finsetSum t (fun i _ => (hloc i).1)
  · calc
      I η = ∑ i ∈ t, I (ζ i) := GlobalIntegrationResults.integral_finset_sum hI t ζ η hζsum
      _ = ∑ i ∈ t, ∫ x, extendScalar d (f' i) x :=
        Finset.sum_congr rfl (fun i _ => (hloc i).2)
      _ = ∫ x, extendScalar d f x := by
        rw [hext]
        simp only [Finset.sum_apply]
        rw [integral_finsetSum t (fun i _ => (hloc i).1)]

theorem regular_domain_scalar_integral {n : ℕ} {a : ModelKind}
    (T : SmoothManifold n .euclidean (Euclidean n)) (hT : euclideanChart n ∈ T.smoothStructure.val)
    (d : Set (Euclidean n)) (S : SmoothManifold n a d) (hreg : IsRegularDomain T d S)
    (C : CotangentBundle S) (B : FormBundle C n) (g : Metric C)
    (o : Orientation S) (ω : Form B) (hω : IsMetricVolume g o ω)
    (L : (p : d) → TangentSpace S p →ₗ[ℝ] TangentSpace T p.val)
    (hL : ∀ p, IsDifferential S T Subtype.val p (L p))
    (F : (p : d) → TangentSpace T p.val ≃ₗ[ℝ] Euclidean n)
    (hF : ∀ p, IsChartCoordinates T p.val (euclideanChart n) (F p))
    (hmetric : ∀ p v w, metricForm g p v w = ∑ i, F p (L p v) i * F p (L p w) i)
    (f : d → ℝ) (hf : Continuous f) (hfc : IsCompact (sectionSupport f)) :
    ∃ η : CompactTopForm S, η.field = scalarVolume f ω.field ∧
      Integrable (extendScalar d f) ∧
      ∀ I : CompactTopForm S → ℝ, IsIntegral o I → I η = ∫ x in d, extendScalar d f x := by
  let η := scalarVolumeForm C B g o ω hω f hf hfc
  have hresult (I : CompactTopForm S → ℝ) (hI : IsIntegral o I) :=
    scalar_integral_global_of_local d S C B g o ω hω I hI
      (fun f' hf' hfc' c hc hfs => regular_domain_scalar_local T hT d S hreg C B g o ω hω
        L hL F hF hmetric I hI f' hf' hfc' C.tangent.fiberCoordinates c hc hfs) f hf hfc
  obtain ⟨I, hI, _⟩ := GlobalIntegrationResults.exists_integral S o
  refine ⟨η, rfl, (hresult I hI).1, ?_⟩
  intro I' hI'
  rw [show (∫ x in d, extendScalar d f x) = ∫ x, extendScalar d f x from
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by simp [extendScalar, hx])]
  exact (hresult I' hI').2

theorem regular_domain_integral :
    Specs.SmoothManifolds.Integration.ClassicalIntegralIdentifications.regular_domain_integralType := by
  intro n a T hT d S hreg C D o f hf hfc
  have hj := regular_domain_parametrizations T hT d S hreg
  have hex := (embedded_differential_exists S Subtype.val hj T hT).2
  choose L F hL hF using hex
  obtain ⟨g, hg⟩ := induced_metric_exists S C Subtype.val hj T hT L hL F hF
  obtain ⟨ω, hω, _⟩ := MetricVolumeResults.volume_exists_unique S C D g o
  obtain ⟨η, hη, hint, hηI⟩ := regular_domain_scalar_integral T hT d S hreg C D g o ω hω
    L hL F hF hg f hf hfc
  exact ⟨L, F, hL, hF, g, hg, ω, hω, η, hη, hint, hηI⟩


theorem euclidean_top_smooth {n : ℕ} {a : ModelKind} {M : Type} [TopologicalSpace M]
    (S : SmoothManifold n a M) (C : CotangentBundle S) (D : FormBundle C n)
    (j : M → Euclidean n) (hj : EmbeddedData.HasFullRankParametrizations S j)
    (T : SmoothManifold n .euclidean (Euclidean n))
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (j p))
    (hL : ∀ p, DifferentialData.IsDifferential S T j p (L p))
    (F : (p : M) → TangentSpace T (j p) ≃ₗ[ℝ] Euclidean n)
    (hF : ∀ p, DifferentialData.IsChartCoordinates T (j p) (EmbeddedData.euclideanChart n) (F p)) :
    IsForm D (fun p => exteriorPower.ιMulti ℝ n
      (fun i => (LinearMap.proj i).comp ((F p).toLinearMap.comp (L p)))) := by
  apply decomposable_smooth C n D
  intro i
  have h := Covectors.differential_smooth S C (fun p => j p i) (embedded_coordinate_smooth S j hj i)
  have he : dFunction S (fun p => j p i) (embedded_coordinate_smooth S j hj i) =
      fun p => (LinearMap.proj i).comp ((F p).toLinearMap.comp (L p)) := by
    funext p
    exact embedded_coordinate_differential S j hj T L hL F hF p i
  rwa [he] at h

theorem metric_volume_of_norm_pairing {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (C : CotangentBundle S) (D : FormBundle C n)
    (g : Metric C) (ω : Form D)
    (hnorm : ∀ p v, determinantNorm g p v = |pairing p (ω.field p) v|) :
    ∃ o : Orientation S, IsMetricVolume g o ω ∧
      ∀ p v, IsPositive (o.val p) v ↔ 0 < pairing p (ω.field p) v := by
  have hω : ∀ p, ω.field p ≠ 0 := by
    intro p hz
    obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
    let K := C.tangent.fiberCoordinates
    have hpos := MetricVolumeResults.determinantNorm_pos g p
      (OrientationData.coordinateVector K c hc ⟨p, hp⟩)
      (MetricVolumeResults.coordinateVector_ne_zero K c hc ⟨p, hp⟩)
    rw [hnorm, hz] at hpos
    simp [pairing] at hpos
  obtain ⟨o, ho, _⟩ := OrientationResults.form_orientation_exists_unique
    ExteriorAlgebraResults.alternating_interpretation ExteriorAlgebraResults.smooth_iff_coefficients
    S C D ⟨ω, hω⟩
  refine ⟨o, ?_, ho⟩
  intro p v hv hn
  have hpos := (ho p v).mp hv
  rw [hnorm, abs_of_pos hpos] at hn
  exact hn

set_option maxHeartbeats 800000 in
theorem induced_determinant_norm {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (C : CotangentBundle S)
    (g : Metric C) (p : M) (J : TangentSpace S p →ₗ[ℝ] Euclidean n)
    (hJ : ∀ v w, metricForm g p v w = ∑ i, J v i * J w i)
    (v : DeterminantLine S p) :
    determinantNorm g p v =
      |pairing p (exteriorPower.ιMulti ℝ n (fun i => (LinearMap.proj i).comp J)) v| := by
  let K := C.tangent.fiberCoordinates
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
  let E := K.equiv c hc p hp
  let A : Matrix (Fin n) (Fin n) ℝ := Matrix.of
    (fun i j => J (E.symm ((Pi.basisFun ℝ (Fin n)) i)) j)
  have hgram : metricMatrix g K c hc ⟨p, hp⟩ = A * A.transpose := by
    ext i j
    exact hJ (E.symm ((Pi.basisFun ℝ (Fin n)) i))
      (E.symm ((Pi.basisFun ℝ (Fin n)) j))
  have hpair : pairing p (exteriorPower.ιMulti ℝ n (fun i => (LinearMap.proj i).comp J))
      (OrientationData.coordinateVector K c hc ⟨p, hp⟩) = A.det := by
    simp only [pairing, OrientationData.coordinateVector, exteriorPower.pairingDual_ιMulti_ιMulti,
      LinearMap.comp_apply, LinearMap.proj_apply]
    rfl
  rw [MetricVolumeResults.coordinate_expansion K c hc ⟨p, hp⟩ v,
    MetricVolumeResults.determinantNorm_smul,
    MetricVolumeResults.gram_formula g K c hc ⟨p, hp⟩, hgram,
    Matrix.det_mul, Matrix.det_transpose, Real.sqrt_mul_self_eq_abs]
  simp only [pairing, map_smul, smul_eq_mul, abs_mul]
  rw [show exteriorPower.pairingDual ℝ (TangentSpace S p) n
    (exteriorPower.ιMulti ℝ n (fun i => (LinearMap.proj i).comp J))
      (OrientationData.coordinateVector K c hc ⟨p, hp⟩) = A.det from hpair]

theorem euclidean_standard_volume {n : ℕ} {a : ModelKind} {M : Type} [TopologicalSpace M]
    (S : SmoothManifold n a M) (C : CotangentBundle S) (D : FormBundle C n)
    (j : M → Euclidean n) (hj : EmbeddedData.HasFullRankParametrizations S j)
    (T : SmoothManifold n .euclidean (Euclidean n))
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (j p))
    (hL : ∀ p, DifferentialData.IsDifferential S T j p (L p))
    (F : (p : M) → TangentSpace T (j p) ≃ₗ[ℝ] Euclidean n)
    (hF : ∀ p, DifferentialData.IsChartCoordinates T (j p) (EmbeddedData.euclideanChart n) (F p))
    (g : Metric C)
    (hJ : ∀ p v w, metricForm g p v w = ∑ i, F p (L p v) i * F p (L p w) i) :
    ∃ (o : Orientation S) (ω : Form D),
      ω.field = (fun p => exteriorPower.ιMulti ℝ n
        (fun i => (LinearMap.proj i).comp ((F p).toLinearMap.comp (L p)))) ∧
      IsMetricVolume g o ω ∧
      ∀ p v, IsPositive (o.val p) v ↔ 0 < pairing p (ω.field p) v := by
  let ω : Form D := ⟨_, euclidean_top_smooth S C D j hj T L hL F hF⟩
  obtain ⟨o, ho, hpos⟩ := metric_volume_of_norm_pairing S C D g ω
    (fun p v => induced_determinant_norm S C g p ((F p).toLinearMap.comp (L p)) (hJ p) v)
  exact ⟨o, ω, rfl, ho, hpos⟩


theorem standard_domain_integral :
    Specs.SmoothManifolds.Integration.ClassicalIntegralIdentifications.standard_domain_integralType := by
  intro n a T hT d S hreg C D f hf hfc
  have hj := regular_domain_parametrizations T hT d S hreg
  have hex := (embedded_differential_exists S Subtype.val hj T hT).2
  choose L F hL hF using hex
  obtain ⟨g, hg⟩ := induced_metric_exists S C Subtype.val hj T hT L hL F hF
  obtain ⟨o, ω, hωfield, hω, hpositive⟩ := euclidean_standard_volume S C D Subtype.val hj T L hL F hF g hg
  obtain ⟨η, hη, hint, hI⟩ := regular_domain_scalar_integral T hT d S hreg C D g o ω hω
    L hL F hF hg f hf hfc
  refine ⟨L, F, hL, hF, o, ?_, η, ?_, hint, hI⟩
  · simpa only [hωfield, euclideanVolumeForm] using hpositive
  · rw [hη, hωfield]
    rfl

theorem compact_coefficient_support :
    Specs.SmoothManifolds.Integration.ClassicalIntegralIdentifications.compact_coefficient_supportType.{u} := by
  intro M F _ _ _ f
  exact isClosed_closure.isCompact

theorem coefficientwise_local_extensions {n q : ℕ} {M : Type u}
    (r : ℕ∞) (j : M → Euclidean n) (A : M → Euclidean q)
    (hA : ∀ i, LocallyContDiffAlong r j (fun p => A p i)) : LocallyContDiffAlong r j A := by
  intro p
  choose U hU hpU H hH heH using fun i => hA i p
  refine ⟨⋂ i, U i, isOpen_iInter_of_finite hU, ?_, fun z i => H i z, ?_, ?_⟩
  · exact mem_iInter.mpr hpU
  · apply contDiffOn_pi.mpr
    intro i
    exact (hH i).mono (iInter_subset U i)
  · intro y hy
    funext i
    exact heH i y (mem_iInter.mp hy i)

theorem ambient_oneform_regular :
    Specs.SmoothManifolds.Integration.ClassicalIntegralIdentifications.ambient_oneform_regularType := by
  intro n N a M _ S C j hj U hU hjU A hA T hT L hL F hF
  have h := euclidean_oneform_regular S C j hj (fun p => A (j p))
    (ambient_coefficients_local j U hU hjU A hA) T hT L hL F hF
  exact ⟨h.1, h.2.1⟩

theorem standard_oriented_domain_integral :
    Specs.SmoothManifolds.Integration.ClassicalIntegralIdentifications.standard_oriented_domain_integralType := by
  intro n a T hT d S hreg C D o L hL F hF hpositive f hf hfc
  have hj := regular_domain_parametrizations T hT d S hreg
  obtain ⟨g, hg⟩ := induced_metric_exists S C Subtype.val hj T hT L hL F hF
  let ω : Form D := ⟨_, euclidean_top_smooth S C D Subtype.val hj T L hL F hF⟩
  have hω : IsMetricVolume g o ω := by
    intro p v hv hn
    have hpos := (hpositive p v).mp hv
    dsimp only [euclideanVolumeForm] at hpos
    have hnorm := induced_determinant_norm S C g p ((F p).toLinearMap.comp (L p)) (hg p) v
    rw [hnorm] at hn
    rw [abs_of_pos hpos] at hn
    exact hn
  obtain ⟨η, hη, hint, hI⟩ := regular_domain_scalar_integral T hT d S hreg C D g o ω hω
    L hL F hF hg f hf hfc
  exact ⟨η, hη, hint, hI⟩

theorem euclidean_oneform_continuous {n N : ℕ} {a : ModelKind} {M : Type}
    [TopologicalSpace M] (S : SmoothManifold n a M) (C : CotangentBundle S)
    (j : M → Euclidean N) (hj : EmbeddedData.HasFullRankParametrizations S j)
    (A : M → Euclidean N) (hA : Continuous A)
    (T : SmoothManifold N .euclidean (Euclidean N))
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (j p))
    (hL : ∀ p, DifferentialData.IsDifferential S T j p (L p))
    (F : (p : M) → TangentSpace T (j p) ≃ₗ[ℝ] Euclidean N)
    (hF : ∀ p, DifferentialData.IsChartCoordinates T (j p) (EmbeddedData.euclideanChart N) (F p)) :
    let ω := euclideanOneForm S (fun p => (F p).toLinearMap.comp (L p)) A
    ExteriorDerivativeData.IsContinuousField C 1 ω ∧
      ModelData.sectionSupport ω ⊆ ModelData.sectionSupport A := by
  let J := fun p => (F p).toLinearMap.comp (L p)
  let α : Fin N → CovectorField S := fun i p => (LinearMap.proj i).comp (J p)
  have hα (i : Fin N) : IsOneForm C (α i) := by
    have h := Covectors.differential_smooth S C (fun p => j p i) (embedded_coordinate_smooth S j hj i)
    have he : dFunction S (fun p => j p i) (embedded_coordinate_smooth S j hj i) = α i := by
      funext p
      exact embedded_coordinate_differential S j hj T L hL F hF p i
    rwa [he] at h
  let θ : Fin N → Field S 1 := fun i p =>
    (exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace S p))).symm (α i p)
  have hθ (i : Fin N) : ExteriorDerivativeData.IsContinuousField C 1 (θ i) := by
    letI := (cotangentSpace C).topology
    obtain ⟨B⟩ := BundleOperations.exists_exterior (cotangentSpace C).bundle 1
    apply ExteriorDerivativeResults.regular_continuous C 1 1
    apply ExteriorDerivativeResults.smooth_regular C 1 B _ 1
    exact ExteriorDerivativeResults.oneForm_isForm C B _ (hα i)
  have hfield : euclideanOneForm S J A = ∑ i : Fin N, fun p => A p i • θ i p := by
    funext p
    simp [euclideanOneForm, θ, α]
  refine ⟨?_, ?_⟩
  · change ExteriorDerivativeData.IsContinuousField C 1 (euclideanOneForm S J A)
    rw [hfield]
    intro c hc I
    have heq : (fun p : c.source => ExteriorData.coefficients C 1 c hc
        (∑ i : Fin N, fun p => A p i • θ i p) p I) =
        fun p => ∑ i : Fin N, A p.val i * ExteriorData.coefficients C 1 c hc (θ i) p I := by
      funext p
      simp [ExteriorData.coefficients, map_sum, map_smul]
    rw [heq]
    apply continuous_finsetSum
    intro i hi
    exact (((continuous_apply i).comp hA).comp continuous_subtype_val).mul (hθ i c hc I)
  · apply closure_mono
    intro p hp hz
    apply hp
    simp [euclideanOneForm, hz]

theorem euclidean_curve_integral {N : ℕ} {a : ModelKind} {M : Type}
    [TopologicalSpace M] (S : SmoothManifold 1 a M) (C : CotangentBundle S)
    (o : Orientation S) (j : M → Euclidean N)
    (hj : EmbeddedData.HasFullRankParametrizations S j)
    (A : M → Euclidean N) (hA : Continuous A)
    (T : SmoothManifold N .euclidean (Euclidean N))
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (j p))
    (hL : ∀ p, DifferentialData.IsDifferential S T j p (L p))
    (F : (p : M) → TangentSpace T (j p) ≃ₗ[ℝ] Euclidean N)
    (hF : ∀ p, DifferentialData.IsChartCoordinates T (j p) (EmbeddedData.euclideanChart N) (F p))
    (hsupp : IsCompact (ModelData.sectionSupport
      (euclideanOneForm S (fun p => (F p).toLinearMap.comp (L p)) A))) :
    let J := fun p => (F p).toLinearMap.comp (L p)
    ∃ η : CompactTopForm S, η.field = euclideanOneForm S J A ∧
      ∀ (I : CompactTopForm S → ℝ), IsIntegral o I →
      ∀ (s : SignedCharts S), RepresentsSignedCharts o.val s →
      ∀ (K : FiberCoordinates S),
      (∀ (c : ModelChart 1 a M) (hc : c ∈ S.smoothStructure.val),
        ModelData.sectionSupport η.field ⊆ c.source →
        Integrable (lineIntegrand s K c hc J A) ∧ I η = ∫ x, lineIntegrand s K c hc J A x) ∧
      (∀ {ι : Type} (c : ι → ModelChart 1 a M) (hc : ∀ i, c i ∈ S.smoothStructure.val)
        (ρ : ι → M → ℝ), IsLocalization c ρ η →
        I η = ∑ᶠ i, ∫ x, lineIntegrand s K (c i) (hc i) J (fun p => ρ i p • A p) x) := by
  exact line_integral S C o (fun p => (F p).toLinearMap.comp (L p)) A
    (euclidean_oneform_continuous S C j hj A hA T L hL F hF).1 hsupp


end SmoothManifolds.ClassicalIntegralResults
