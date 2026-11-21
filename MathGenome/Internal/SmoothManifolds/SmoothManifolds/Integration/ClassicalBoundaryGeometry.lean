import MathGenome.Internal.ODEDynamics.D13Unified.Ch11.RegularConstraints
import MathGenome.Internal.ODEDynamics.D13Unified.Ch06.StateDerivative
import MathGenome.Internal.ODEDynamics.D13Unified.Ch13.Trapping
import MathGenome.Internal.ODEDynamics.D13Unified.Ch21.Collar
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Inverse
import MathGenome.Internal.ODEDynamics.D13Unified.Ch21.SmoothJordan
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Integration.ClassicalBoundaryGeometry
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.Calculus.ContDiff.Operations
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.MapClasses
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.RegularDomains
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.Topology
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Tangent.EmbeddedComparison
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Orientations.Boundary
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Orientations.MetricVolume
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Connected.LocallyConnected

/-! Geometric classical Stokes identifications on the genuine intrinsic fibers.
Domain and surface metric, smooth normal, volume/density and boundary-sign
comparisons are joined by the actual planar local-left characterization and
compact component parametrization, Jordan-side and winding-sign comparisons.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace SmoothManifolds.ClassicalBoundaryResults
open ModelData AtlasData MapData TangentData DifferentialData EmbeddedData
  MapClassData RegularDomainData BoundaryData BoundaryConeData
  BoundaryOrientationData ClassicalBoundaryData OrientationData Set Module
open BundleOperationsData MetricVolumeData FrameData BundleData TangentBundleData Filter
open ExteriorData
open scoped Topology

/-- A normed-vector-valued local extension in one chart suffices, with chart
independence supplied by the actual smooth transition maps. -/
theorem vectorSmoothAt_of_chart {n : ℕ} {a : ModelKind} {M V : Type*}
    [TopologicalSpace M] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (S : SmoothManifold n a M) (f : M → V) (p : M)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (hp : p ∈ c.source)
    (U : Set (Euclidean n)) (hU : IsOpen U) (hpU : (c p).val ∈ U)
    (F : Euclidean n → V) (hF : ContDiffOn ℝ (⊤ : ℕ∞) F U)
    (heF : (fun q => F (c q).val) =ᶠ[𝓝 p] f) :
    VectorSmoothAt S.smoothStructure.val f p := by
  have hcont : ContinuousAt (fun q => (c q).val) p :=
    continuous_subtype_val.continuousAt.comp (c.continuousAt hp)
  refine ⟨((hF.continuousOn.continuousAt (hU.mem_nhds hpU)).comp
    (f := fun q : M => (c q).val) hcont).congr heF, ?_⟩
  intro d hd hpd
  obtain ⟨W, hW, hpW, G, hG, heG⟩ := chartContDiffAt_of_compatible
    (S.smoothStructure.property.1.2 d hd c hc) hpd hp
  refine ⟨W ∩ G ⁻¹' U, hG.continuousOn.isOpen_inter_preimage hW hU,
    ⟨hpW, ?_⟩, F ∘ G, hF.comp (hG.mono inter_subset_left) (fun _ hz => hz.2), ?_⟩
  · change G (d p).val ∈ U
    rw [heG.eq_of_nhds]
    exact hpU
  · exact (heG.fun_comp F).trans heF

theorem chart_coordinates_unique {n : ℕ} {a : ModelKind} {M : Type}
    [TopologicalSpace M] (S : SmoothManifold n a M) (p : M)
    (c : ModelChart n a M) (E F : TangentSpace S p ≃ₗ[ℝ] Euclidean n)
    (hE : IsChartCoordinates S p c E) (hF : IsChartCoordinates S p c F) : E = F := by
  obtain ⟨e, he, hEv⟩ := hE
  obtain ⟨f, hf, hFv⟩ := hF
  have hef (i : Fin n) : e i = f i := Subtype.ext ((he i).trans (hf i).symm)
  ext v i
  rw [hEv, hFv, hef]

theorem euclidean_differential_exists_unique :
    Specs.SmoothManifolds.Integration.ClassicalBoundaryGeometry.euclidean_differential_exists_uniqueType := by
  intro n N a M _ S T j hT hj p
  obtain ⟨L, hL, huniq⟩ := differential_exists S T j hj p
  let F := coordinateDerivationEquiv T (j p) (euclideanChart N) hT (mem_univ _)
  have hF := coordinateDerivationEquiv_isChartCoordinates T (j p)
    (euclideanChart N) hT (mem_univ _)
  refine ⟨F.toLinearMap.comp L, ⟨L, F, hL, hF, rfl⟩, ?_⟩
  rintro J ⟨L', F', hL', hF', rfl⟩
  rw [huniq L' hL', chart_coordinates_unique T (j p) (euclideanChart N) F' F hF' hF]

theorem euclidean_differential_injective {n N : ℕ} {a : ModelKind} {M : Type}
    [TopologicalSpace M] (S : SmoothManifold n a M)
    (T : SmoothManifold N .euclidean (Euclidean N)) (j : M → Euclidean N)
    (hj : IsSmoothEmbedding S T j) (p : M)
    (J : TangentSpace S p →ₗ[ℝ] Euclidean N)
    (hJ : IsEuclideanDifferential S T j p J) : Function.Injective J := by
  obtain ⟨L, F, hL, _, rfl⟩ := hJ
  exact F.injective.comp ((MapClasses.smooth_tangent_invariants S T j hj.1 p L hL).2.1.mp
    (hj.2.2.1 p))

theorem dot_self_positive {N : ℕ} (v : Euclidean N) (hv : v ≠ 0) :
    0 < dotProduct v v := by
  have hnonneg : 0 ≤ dotProduct v v := Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))
  exact lt_of_le_of_ne hnonneg (Ne.symm (dotProduct_self_eq_zero.not.mpr hv))

theorem embedded_metric_positive :
    Specs.SmoothManifolds.Integration.ClassicalBoundaryGeometry.embedded_metric_positiveType := by
  intro n N a M _ S T j hj p J hJ
  have hi := euclidean_differential_injective S T j hj p J hJ
  refine ⟨hi, ?_, ?_⟩
  · intro v w
    exact dotProduct_comm (J v) (J w)
  · intro v hv
    exact dot_self_positive (J v) (fun h => hv (hi (h.trans J.map_zero.symm)))

/-- In a canonical tangent trivialization the actual Euclidean differential
has smooth coefficients: they are the derivatives of local smooth extensions
of the embedding. The germ equality is reused on an open neighborhood, which
is essential at a source boundary point. -/
theorem euclidean_frame_smooth {n N : ℕ} {a : ModelKind} {M : Type}
    [TopologicalSpace M] (S : SmoothManifold n a M)
    (T : SmoothManifold N .euclidean (Euclidean N)) (j : M → Euclidean N)
    (hT : euclideanChart N ∈ T.smoothStructure.val) (hj : IsSmoothMap S T j)
    (C : CotangentBundle S) (J : (p : M) → TangentSpace S p →ₗ[ℝ] Euclidean N)
    (hJ : ∀ p, IsEuclideanDifferential S T j p (J p)) :
    letI := C.realization.space.topology
    ∀ (k : TangentIndex S) (i : Fin n), SmoothOnBase S
      (fun p => J p ((C.realization.space.bundle.trivialization k).symm p (Pi.single i 1)))
      (C.realization.space.bundle.baseSet k) := by
  letI := C.realization.space.topology
  let B := C.realization.space.bundle
  intro k i p hp
  have hpc : p ∈ k.val.source := by simpa only [C.realization.baseSet] using hp
  obtain ⟨U, hU, hpU, H, hH, heH⟩ :=
    (hj p).2 k.val k.property (euclideanChart N) hT hpc (mem_univ _)
  have hcont : ContinuousAt (fun q => (k.val q).val) p :=
    continuous_subtype_val.continuousAt.comp (k.val.continuousAt hpc)
  obtain ⟨W, hWsub, hW, hpW⟩ := mem_nhds_iff.mp heH
  let F : Euclidean n → Euclidean N := fun z => fderiv ℝ H z (Pi.single i 1)
  have hF : ContDiffOn ℝ (⊤ : ℕ∞) F U :=
    (hH.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const
  apply vectorSmoothAt_of_chart S _ p k.val k.property hpc U hU hpU F hF
  filter_upwards [k.val.open_source.mem_nhds hpc, hW.mem_nhds hpW,
    hcont.preimage_mem_nhds (hU.mem_nhds hpU)] with q hqc hqW hqU
  obtain ⟨L, A, hL, hA, heq⟩ := hJ q
  let E := C.tangent.fiberCoordinates.equiv k.val k.property q hqc
  have hE := C.tangent.fiberCoordinates.isCoordinates k.val k.property q hqc
  have heHq : (fun y => H (k.val y).val) =ᶠ[𝓝 q]
      (fun y => (euclideanChart N (j y)).val) :=
    Filter.mem_of_superset (hW.mem_nhds hqW) hWsub
  have hqB : q ∈ B.baseSet k := by
    change q ∈ C.realization.space.bundle.baseSet k
    rw [C.realization.baseSet]
    exact hqc
  have hcoord : B.fiberCoordinates k q hqB = E := by
    apply LinearEquiv.ext
    intro v
    exact C.realization.coordinates k q hqc v
  have hvector : (B.trivialization k).symm q (Pi.single i 1) = E.symm (Pi.single i 1) := by
    rw [← BundleData.SmoothVectorBundle.fiberCoordinates_symm_apply B k q hqB, hcoord]
  have hformula := differential_jacobian S T j hj q L hL k.val (euclideanChart N)
    k.property hT hqc (mem_univ _) E A hE hA U H hU hqU hH heHq
    ((B.trivialization k).symm q (Pi.single i 1))
  change F (k.val q).val = J q ((B.trivialization k).symm q (Pi.single i 1))
  rw [heq]
  change fderiv ℝ H (k.val q).val (Pi.single i 1) =
    A (L ((B.trivialization k).symm q (Pi.single i 1)))
  rw [hformula, hvector, E.apply_symm_apply]

theorem embedded_metric_exists :
    Specs.SmoothManifolds.Integration.ClassicalBoundaryGeometry.embedded_metric_existsType := by
  intro n N a M _ S T j hT hj C J hJ
  letI := C.realization.space.topology
  have hdot : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Euclidean N × Euclidean N => dotProduct z.1 z.2) := by
    apply ContDiff.sum
    intro i _
    exact ((contDiff_apply ℝ (fun _ : Fin N => ℝ) i).comp contDiff_fst).mul
      ((contDiff_apply ℝ (fun _ : Fin N => ℝ) i).comp contDiff_snd)
  refine ⟨{ form := fun p => euclideanPullback (J p)
            symmetric := fun p => (embedded_metric_positive S T j hj p (J p) (hJ p)).2.1
            positive := fun p => (embedded_metric_positive S T j hj p (J p) (hJ p)).2.2
            smooth := ?_ }, fun _ => rfl⟩
  intro k i l p hp
  exact FrameData.VectorSmoothAt.postcomp (FrameData.VectorSmoothAt.prod
    (euclidean_frame_smooth S T j hT hj.1 C J hJ k i p hp)
    (euclidean_frame_smooth S T j hT hj.1 C J hJ k l p hp)) hdot

theorem regular_domain_tangent :
    Specs.SmoothManifolds.Integration.ClassicalBoundaryGeometry.regular_domain_tangentType := by
  intro m a T hT D S hD p
  obtain ⟨J, hJ, _⟩ := euclidean_differential_exists_unique S T Subtype.val hT hD.2.1 p
  have hinj := euclidean_differential_injective S T Subtype.val hD.2 p J hJ
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  let E := coordinateDerivationEquiv S p e he hp
  let A := J.comp E.symm.toLinearMap
  have hA : Function.Bijective A :=
    ⟨hinj.comp E.symm.injective, A.injective_iff_surjective.mp (hinj.comp E.symm.injective)⟩
  let I := E.trans (LinearEquiv.ofBijective A hA)
  refine ⟨I, ?_⟩
  have heq : I.toLinearMap = J := by
    apply LinearMap.ext
    intro v
    change J (E.symm (E v)) = J v
    exact congrArg J (E.symm_apply_apply v)
  rw [heq]
  exact hJ

/-- The Euclidean Riesz representative of a covector, normalized toward its
negative side. This is finite-dimensional dot-product geometry and does not use
the sup norm on the coordinate Banach space. -/
theorem unit_normal_of_covector {N : ℕ} (φ : Euclidean N →ₗ[ℝ] ℝ) (hφ : φ ≠ 0) :
    ∃! ν : Euclidean N,
      dotProduct ν ν = 1 ∧ φ ν < 0 ∧
        LinearMap.ker (dotFunctional ν) = LinearMap.ker φ := by
  classical
  let a : Euclidean N := fun i => φ (Pi.single i 1)
  have hrep : φ = dotFunctional a := by
    apply (Pi.basisFun ℝ (Fin N)).ext
    intro i
    simp [dotFunctional, a, Pi.basisFun_apply]
  have ha : a ≠ 0 := by
    intro hz
    apply hφ
    rw [hrep, hz]
    apply LinearMap.ext
    intro z
    exact zero_dotProduct z
  let d := dotProduct a a
  let s := Real.sqrt d
  have hd : 0 < d := dot_self_positive a ha
  have hs : 0 < s := Real.sqrt_pos.mpr hd
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hss : s * s = d := Real.mul_self_sqrt hd.le
  let ν : Euclidean N := (-s⁻¹) • a
  have hunit : dotProduct ν ν = 1 := by
    simp only [ν, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    change -s⁻¹ * (-s⁻¹ * d) = 1
    rw [← hss]
    field_simp
  have hnegative : φ ν < 0 := by
    rw [hrep]
    change dotProduct a ((-s⁻¹) • a) < 0
    rw [dotProduct_smul, smul_eq_mul]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos (inv_pos.mpr hs)) hd
  have hker : LinearMap.ker (dotFunctional ν) = LinearMap.ker φ := by
    ext z
    change dotProduct ν z = 0 ↔ φ z = 0
    rw [hrep]
    change dotProduct ((-s⁻¹) • a) z = 0 ↔ dotProduct a z = 0
    rw [smul_dotProduct, smul_eq_mul]
    exact mul_eq_zero.trans (or_iff_right (neg_ne_zero.mpr (inv_ne_zero hs0)))
  refine ⟨ν, ⟨hunit, hnegative, hker⟩, ?_⟩
  rintro μ ⟨hμunit, hμnegative, hμker⟩
  let t := dotProduct μ ν
  let w := μ - t • ν
  have hνw : dotProduct ν w = 0 := by
    simp only [w, dotProduct_sub, dotProduct_smul, smul_eq_mul, hunit, mul_one]
    exact sub_eq_zero.mpr (dotProduct_comm ν μ)
  have hμw : dotProduct μ w = 0 := by
    have hw : w ∈ LinearMap.ker (dotFunctional μ) := by
      rw [hμker, ← hker]
      exact hνw
    exact hw
  have ht : t * t = 1 := by
    have hh : 1 - t * t = 0 := by
      simpa only [w, dotProduct_sub, dotProduct_smul, smul_eq_mul, hμunit] using hμw
    linarith
  have hww : dotProduct w w = 0 := by
    simp only [w, sub_dotProduct, dotProduct_sub, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, hμunit, hunit]
    rw [dotProduct_comm ν μ]
    change 1 - t * t - t * (t - t * 1) = 0
    nlinarith
  have hμ : μ = t • ν := sub_eq_zero.mp (dotProduct_self_eq_zero.mp hww)
  have htp : 0 < t := by
    have hh : t * φ ν < 0 := by simpa only [hμ, map_smul, smul_eq_mul] using hμnegative
    nlinarith
  have ht1 : t = 1 := by nlinarith
  simpa [ht1] using hμ

theorem outward_unit_normal_pointwise :
    Specs.SmoothManifolds.Integration.ClassicalBoundaryGeometry.outward_unit_normal_pointwiseType := by
  intro n T hT D S hD
  obtain ⟨B, hB, _⟩ := boundary_tangent_identification S
  refine ⟨B, hB, ?_⟩
  intro p J K hJ hK
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p.val
  let E := coordinateDerivationEquiv S p.val c hc hp
  have hE := coordinateDerivationEquiv_isChartCoordinates S p.val c hc hp
  have hKimage := boundary_inclusion_image S B hB p c hc hp K hK E hE
  let φ : Euclidean (n+1) →ₗ[ℝ] ℝ :=
    (LinearMap.proj (Fin.last n)).comp (E.toLinearMap.comp J.symm.toLinearMap)
  have hφ : φ ≠ 0 := by
    intro hz
    have hh := DFunLike.congr_fun hz (J (E.symm (Pi.single (Fin.last n) 1)))
    simp [φ] at hh
  obtain ⟨ν, hν, huniq⟩ := unit_normal_of_covector φ hφ
  have hout (z : Euclidean (n+1)) :
      IsOutward S p (J.symm z) ↔ φ z < 0 :=
    BoundaryOrientations.outward_iff_coordinate S p c hc hp E hE (J.symm z)
  have himage : LinearMap.range (J.toLinearMap.comp K) = LinearMap.ker φ := by
    ext z
    change (∃ v, J (K v) = z) ↔ E (J.symm z) (Fin.last n) = 0
    rw [← hKimage.2]
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨v, (J.symm_apply_apply (K v)).symm⟩
    · rintro ⟨v, hv⟩
      exact ⟨v, by rw [hv, J.apply_symm_apply]⟩
  refine ⟨hKimage.1, ν, ⟨hν.1, (hout ν).mpr hν.2.1, himage.trans hν.2.2.symm⟩, ?_⟩
  rintro μ ⟨hμunit, hμout, hμimage⟩
  exact huniq μ ⟨hμunit, (hout μ).mp hμout, hμimage.symm.trans himage⟩

theorem regular_domain_normal_field :
    Specs.SmoothManifolds.Integration.ClassicalBoundaryGeometry.regular_domain_normal_fieldType := by
  intro n T hT D S hD
  classical
  obtain ⟨B, hB, hnormal⟩ := outward_unit_normal_pointwise T hT D S hD
  choose J hJ using (regular_domain_tangent T hT D S hD)
  have hexK (p : intrinsicBoundary S) := differential_exists B S Subtype.val hB.1 p
  choose K hK _ using hexK
  have hexν (p : intrinsicBoundary S) := (hnormal p (J p.val) (K p) (hJ p.val) (hK p)).2
  choose ν hν _ using hexν
  exact ⟨B, J, K, ν, hB, hJ, fun p => ⟨hK p, hν p⟩⟩

theorem gramArea_eq_cross_length {V : Type*} [AddCommGroup V] [Module ℝ V]
    (J : V →ₗ[ℝ] Euclidean 3) (u v : V) :
    gramArea J u v = Real.sqrt (dotProduct (crossProduct (J u) (J v))
      (crossProduct (J u) (J v))) := by
  rw [cross_dot_cross]
  unfold gramArea
  rw [dotProduct_comm (J v) (J u)]

theorem gramArea_eq_exterior_norm {V : Type*} [AddCommGroup V] [Module ℝ V]
    (J : V →ₗ[ℝ] Euclidean 3) (u v : V) :
    gramArea J u v = Real.sqrt ((euclideanPullback J).exteriorPower 2
      (exteriorPower.ιMulti ℝ 2 ![u, v]) (exteriorPower.ιMulti ℝ 2 ![u, v])) := by
  simp only [LinearMap.BilinForm.exteriorPower, LinearMap.comp_apply,
    exteriorPower.map_apply_ιMulti, exteriorPower.pairingDual_ιMulti_ιMulti]
  simp only [Matrix.det_fin_two]
  change gramArea J u v = Real.sqrt (dotProduct (J u) (J u) * dotProduct (J v) (J v) -
    dotProduct (J v) (J u) * dotProduct (J u) (J v))
  unfold gramArea
  rw [dotProduct_comm (J v) (J u)]

/-- A two-frame cross product transforms by its signed intrinsic determinant.
This is applied only to the genuine embedding differential below. -/
theorem cross_basis_expansion {V : Type*} [AddCommGroup V] [Module ℝ V]
    (b : Basis (Fin 2) ℝ V) (J : V →ₗ[ℝ] Euclidean 3) (u v : V) :
    crossProduct (J u) (J v) = b.det ![u, v] • crossProduct (J (b 0)) (J (b 1)) := by
  have hu : u = b.repr u 0 • b 0 + b.repr u 1 • b 1 := by
    simpa only [Fin.sum_univ_two] using (b.sum_repr u).symm
  have hv : v = b.repr v 0 • b 0 + b.repr v 1 • b 1 := by
    simpa only [Fin.sum_univ_two] using (b.sum_repr v).symm
  have hdet : b.det ![u, v] = b.repr u 0 * b.repr v 1 - b.repr v 0 * b.repr u 1 := by
    simp [Module.Basis.det_apply, Matrix.det_fin_two, Module.Basis.toMatrix_apply]
  rw [hdet]
  conv_lhs => rw [hu, hv]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, cross_apply]
  fin_cases i <;> simp <;> ring

theorem oriented_plane_normal {V : Type*} [AddCommGroup V] [Module ℝ V]
    (b : Basis (Fin 2) ℝ V) (J : V →ₗ[ℝ] Euclidean 3) (hJ : Function.Injective J)
    (r : Module.Ray ℝ (⋀[ℝ]^2 V)) :
    ∃ ν : Euclidean 3, dotProduct ν ν = 1 ∧
      (∀ w, dotProduct ν (J w) = 0) ∧
      ∀ u v, IsPositive r (exteriorPower.ιMulti ℝ 2 ![u, v]) →
        crossProduct (J u) (J v) = gramArea J u v • ν ∧ 0 < gramArea J u v := by
  classical
  let η := exteriorPower.ιMulti ℝ 2 b
  let c₀ := crossProduct (J (b 0)) (J (b 1))
  have hc₀ : c₀ ≠ 0 := by
    apply crossProduct_ne_zero_iff_linearIndependent.mpr
    have hi := b.linearIndependent.map' J (LinearMap.ker_eq_bot.mpr hJ)
    convert hi using 1
    ext i
    fin_cases i <;> rfl
  have hη : η ≠ 0 := by
    intro hz
    have hh := congrArg (exteriorPower.alternatingMapLinearEquiv b.det) hz
    simp [η, Module.Basis.det_self] at hh
  induction r using Module.Ray.ind with | h x hx =>
  let t := exteriorPower.alternatingMapLinearEquiv b.det x
  have hxrepr : x = t • η := MetricVolumeResults.determinant_expansion b x
  have ht : t ≠ 0 := by
    intro hz
    exact hx (by rw [hxrepr, hz, zero_smul])
  let c := t • c₀
  have hc : c ≠ 0 := smul_ne_zero ht hc₀
  let s := Real.sqrt (dotProduct c c)
  have hs : 0 < s := Real.sqrt_pos.mpr (dot_self_positive c hc)
  have hs0 : s ≠ 0 := hs.ne'
  have hss : s * s = dotProduct c c :=
    Real.mul_self_sqrt (dot_self_positive c hc).le
  let ν := s⁻¹ • c
  have hνunit : dotProduct ν ν = 1 := by
    simp only [ν, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [← hss]
    field_simp
  have hνorth (w : V) : dotProduct ν (J w) = 0 := by
    have hw : w = b.repr w 0 • b 0 + b.repr w 1 • b 1 := by
      simpa only [Fin.sum_univ_two] using (b.sum_repr w).symm
    rw [hw]
    simp only [ν, c, c₀, map_add, map_smul, smul_dotProduct, dotProduct_add,
      dotProduct_smul, smul_eq_mul]
    rw [dotProduct_comm (crossProduct (J (b 0)) (J (b 1))) (J (b 0)),
      dotProduct_comm (crossProduct (J (b 0)) (J (b 1))) (J (b 1)),
      dot_self_cross, dot_cross_self]
    ring
  refine ⟨ν, hνunit, hνorth, ?_⟩
  intro u v hpos
  obtain ⟨k, hk, hxy⟩ := (OrientationResults.positive_iff_pos_smul x hx _).mp hpos
  have hcoeff : b.det ![u, v] = k * t := by
    apply smul_left_injective ℝ hη
    change b.det ![u, v] • exteriorPower.ιMulti ℝ 2 b = (k * t) • η
    rw [← MetricVolumeResults.wedge_basis_expansion b ![u, v], hxy, hxrepr, smul_smul]
  have hcross : crossProduct (J u) (J v) = k • c := by
    rw [cross_basis_expansion b J u v, hcoeff, mul_smul]
  have harea : gramArea J u v = k * s := by
    rw [gramArea_eq_cross_length, hcross]
    simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [← hss]
    have hh : k * (k * (s * s)) = (k * s) * (k * s) := by ring
    rw [hh, Real.sqrt_mul_self (mul_pos hk hs).le]
  refine ⟨?_, by rw [harea]; exact mul_pos hk hs⟩
  rw [hcross, harea]
  simp [ν, smul_smul, hs0]

theorem surface_normal_pointwise :
    Specs.SmoothManifolds.Integration.ClassicalBoundaryGeometry.surface_normal_pointwiseType := by
  intro a M _ S T j hj o p J hJ
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  let E := coordinateDerivationEquiv S p e he hp
  let b := (Pi.basisFun ℝ (Fin 2)).map E.symm
  obtain ⟨ν, hν, horth, hframe⟩ := oriented_plane_normal b J
    (euclidean_differential_injective S T j hj p J hJ) (o.val p)
  refine ⟨ν, hν, horth, ?_⟩
  intro u v huv
  exact ⟨(hframe u v huv).1, (hframe u v huv).2, gramArea_eq_exterior_norm J u v⟩

/-- A cross-product identity on positive frames determines the alternating
identity on every ordered pair, with its signed volume coefficient. -/
theorem surface_cross_all {V : Type*} [AddCommGroup V] [Module ℝ V]
    (b : Basis (Fin 2) ℝ V) (J : V →ₗ[ℝ] Euclidean 3)
    (r : Module.Ray ℝ (⋀[ℝ]^2 V)) (β : (⋀[ℝ]^2 V) →ₗ[ℝ] ℝ)
    (ν : Euclidean 3)
    (hpos : ∀ u v, IsPositive r (exteriorPower.ιMulti ℝ 2 ![u, v]) →
      crossProduct (J u) (J v) = β (exteriorPower.ιMulti ℝ 2 ![u, v]) • ν) :
    ∀ u v, crossProduct (J u) (J v) =
      β (exteriorPower.ιMulti ℝ 2 ![u, v]) • ν := by
  let η := exteriorPower.ιMulti ℝ 2 b
  have hb : crossProduct (J (b 0)) (J (b 1)) = β η • ν := by
    induction r using Module.Ray.ind with | h x hx =>
    let t := exteriorPower.alternatingMapLinearEquiv b.det x
    have hrepr : x = t • η := MetricVolumeResults.determinant_expansion b x
    have ht : t ≠ 0 := by
      intro hz
      exact hx (by rw [hrepr, hz, zero_smul])
    have hscale : exteriorPower.ιMulti ℝ 2 ![t • b 0, b 1] = t • η := by
      convert (exteriorPower.ιMulti ℝ 2).map_vecCons_smul ![b 1] t (b 0) using 1
      congr 1
    have hp : IsPositive (rayOfNeZero ℝ x hx)
        (exteriorPower.ιMulti ℝ 2 ![t • b 0, b 1]) := by
      rw [hscale, ← hrepr]
      exact ⟨hx, rfl⟩
    have he := hpos (t • b 0) (b 1) hp
    rw [hscale, map_smul, map_smul] at he
    have he' := congrArg (fun z : Euclidean 3 => t⁻¹ • z) he
    simpa only [map_smul, LinearMap.smul_apply, smul_eq_mul, smul_smul,
      ← mul_assoc, inv_mul_cancel₀ ht, one_mul, one_smul] using he'
  intro u v
  rw [cross_basis_expansion b J u v, hb,
    MetricVolumeResults.wedge_basis_expansion b ![u, v], map_smul]
  simp only [smul_eq_mul, smul_smul]
  rfl

/-- Smoothness of the compatible surface normal follows from a local formula:
normal = cross(coordinate frame) / signed volume(coordinate frame). The
nonzero denominator is proved using injectivity of the genuine differential. -/
theorem surface_normal_smooth {a : ModelKind} {M : Type} [TopologicalSpace M]
    (S : SmoothManifold 2 a M)
    (T : SmoothManifold 3 .euclidean (Euclidean 3)) (j : M → Euclidean 3)
    (hT : euclideanChart 3 ∈ T.smoothStructure.val) (hj : IsSmoothEmbedding S T j)
    (C : CotangentBundle S) (A : ExteriorData.FormBundle C 2)
    (ω : ExteriorData.Form A)
    (J : (p : M) → TangentSpace S p →ₗ[ℝ] Euclidean 3)
    (hJ : ∀ p, IsEuclideanDifferential S T j p (J p))
    (ν : M → Euclidean 3)
    (hν : ∀ p u v, crossProduct (J p u) (J p v) =
      pairing p (ω.field p) (exteriorPower.ιMulti ℝ 2 ![u, v]) • ν p) :
    VectorSmooth S.smoothStructure.val ν := by
  classical
  letI := C.realization.space.topology
  intro p
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
  let k : TangentIndex S := ⟨c, hc⟩
  let v := fun (q : M) (i : Fin 2) =>
    (C.realization.space.bundle.trivialization k).symm q (Pi.single i 1)
  let f : M → Euclidean 3 := fun q => crossProduct (J q (v q 0)) (J q (v q 1))
  let β : c.source → ℝ := fun q => pairing q.val (ω.field q.val)
    (coordinateVector C.tangent.fiberCoordinates c hc q)
  let b : M → ℝ := FrameData.totalize β
  have hv (q : M) (hq : q ∈ c.source) (i : Fin 2) : v q i =
      (C.tangent.fiberCoordinates.equiv c hc q hq).symm (Pi.single i 1) := by
    let B := C.realization.space.bundle
    have hqB : q ∈ B.baseSet k := by
      change q ∈ C.realization.space.bundle.baseSet k
      rw [C.realization.baseSet]
      exact hq
    change (B.trivialization k).symm q (Pi.single i 1) = _
    rw [← BundleData.SmoothVectorBundle.fiberCoordinates_symm_apply B k q hqB]
    have hcoord : B.fiberCoordinates k q hqB = C.tangent.fiberCoordinates.equiv c hc q hq := by
      apply LinearEquiv.ext
      intro z
      exact C.realization.coordinates k q hq z
    rw [hcoord]
  have hw (q : M) (hq : q ∈ c.source) :
      exteriorPower.ιMulti ℝ 2 ![v q 0, v q 1] =
        coordinateVector C.tangent.fiberCoordinates c hc ⟨q, hq⟩ := by
    unfold coordinateVector
    apply congrArg (exteriorPower.ιMulti ℝ 2)
    funext i
    fin_cases i <;> simp [hv q hq, Pi.basisFun_apply]
  have hformula (q : M) (hq : q ∈ c.source) : f q = b q • ν q := by
    change f q = FrameData.totalize β q • ν q
    rw [FrameData.totalize_of_mem β q hq]
    exact (hν q (v q 0) (v q 1)).trans (by rw [hw q hq])
  have hbp : b p ≠ 0 := by
    have hcross : f p ≠ 0 := by
      apply crossProduct_ne_zero_iff_linearIndependent.mpr
      let E := C.tangent.fiberCoordinates.equiv c hc p hp
      have hb := ((Pi.basisFun ℝ (Fin 2)).map E.symm).linearIndependent.map'
        (J p) (LinearMap.ker_eq_bot.mpr
          (euclidean_differential_injective S T j hj p (J p) (hJ p)))
      convert hb using 1
      funext i
      fin_cases i <;> simp [Function.comp_apply, Module.Basis.map_apply,
        Pi.basisFun_apply, hv p hp, E]
    intro hz
    exact hcross (by rw [hformula p hp, hz, zero_smul])
  have hβ := MetricVolumeResults.coordinate_pairing_smooth
    ExteriorAlgebraResults.coefficient_expansion ExteriorAlgebraResults.smooth_iff_coefficients
    ω c hc ⟨p, hp⟩
  have hb : VectorSmoothAt S.smoothStructure.val b p := hβ.totalize c.open_source
  have hpc : p ∈ C.realization.space.bundle.baseSet k := by
    rw [C.realization.baseSet]
    exact hp
  have hcross : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Euclidean 3 × Euclidean 3 => crossProduct z.1 z.2) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> simp only [cross_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two] <;>
      exact (((contDiff_apply ℝ (fun _ : Fin 3 => ℝ) _).comp contDiff_fst).mul
        ((contDiff_apply ℝ (fun _ : Fin 3 => ℝ) _).comp contDiff_snd)).sub
        (((contDiff_apply ℝ (fun _ : Fin 3 => ℝ) _).comp contDiff_fst).mul
          ((contDiff_apply ℝ (fun _ : Fin 3 => ℝ) _).comp contDiff_snd))
  have hf : VectorSmoothAt S.smoothStructure.val f p :=
    FrameData.VectorSmoothAt.postcomp (FrameData.VectorSmoothAt.prod
      (euclidean_frame_smooth S T j hT hj.1 C J hJ k 0 p hpc)
      (euclidean_frame_smooth S T j hT hj.1 C J hJ k 1 p hpc)) hcross
  have hdiv : VectorSmoothAt S.smoothStructure.val (fun q => (b q)⁻¹ • f q) p := by
    apply (hb.prod hf).postcompOn (h := fun z : ℝ × Euclidean 3 => z.1⁻¹ • z.2)
      (s := {z : ℝ × Euclidean 3 | z.1 ≠ 0})
      (isOpen_ne_fun continuous_fst continuous_const) hbp
    exact (contDiffOn_fst.inv (fun _ hz => hz)).smul contDiffOn_snd
  apply hdiv.congr
  filter_upwards [c.open_source.mem_nhds hp] with q hq
  have hbq : b q ≠ 0 := by
    have hcrossq : f q ≠ 0 := by
      apply crossProduct_ne_zero_iff_linearIndependent.mpr
      let E := C.tangent.fiberCoordinates.equiv c hc q hq
      have hh := ((Pi.basisFun ℝ (Fin 2)).map E.symm).linearIndependent.map'
        (J q) (LinearMap.ker_eq_bot.mpr
          (euclidean_differential_injective S T j hj q (J q) (hJ q)))
      convert hh using 1
      funext i
      fin_cases i <;> simp [Function.comp_apply, Module.Basis.map_apply,
        Pi.basisFun_apply, hv q hq, E]
    intro hz
    exact hcrossq (by rw [hformula q hq, hz, zero_smul])
  rw [hformula q hq, smul_smul, inv_mul_cancel₀ hbq, one_smul]

theorem surface_metric_volume :
    Specs.SmoothManifolds.Integration.ClassicalBoundaryGeometry.surface_metric_volumeType := by
  intro a M _ S T j hT hj o C A
  classical
  choose J hJ _ using euclidean_differential_exists_unique S T j hT hj.1
  obtain ⟨g, hg⟩ := embedded_metric_exists S T j hT hj C J hJ
  obtain ⟨ω, hω, _⟩ := MetricVolumeResults.volume_exists_unique S C A g o
  choose ν hν using (fun p => surface_normal_pointwise S T j hj o p (J p) (hJ p))
  refine ⟨J, g, ω, ν, hJ, hg, hω, ?_⟩
  intro p
  refine ⟨(hν p).1, (hν p).2.1, ?_⟩
  intro u v huv
  have hvol := MetricVolumeResults.metricVolume_evaluate_positive g o ω hω p
    (exteriorPower.ιMulti ℝ 2 ![u, v]) huv
  have hnorm : determinantNorm g p (exteriorPower.ιMulti ℝ 2 ![u, v]) = gramArea (J p) u v := by
    unfold determinantNorm determinantMetric
    rw [hg p]
    exact (gramArea_eq_exterior_norm (J p) u v).symm
  have heval := hvol.trans hnorm
  exact ⟨heval, by rw [heval]; exact ((hν p).2.2 u v huv).1⟩

/-- The final row of the inverse differential. -/
def inverseFinalRow {n : ℕ}
    (L : Euclidean (n+1) →L[ℝ] Euclidean (n+1)) : Euclidean (n+1) :=
  fun i => L.inverse (Pi.single i 1) (Fin.last n)

theorem inverseFinalRow_ne_zero {n : ℕ}
    (L : Euclidean (n+1) →L[ℝ] Euclidean (n+1)) (hL : L.IsInvertible) :
    inverseFinalRow L ≠ 0 := by
  classical
  rcases hL with ⟨A, rfl⟩
  intro hz
  let φ : Euclidean (n+1) →ₗ[ℝ] ℝ :=
    (LinearMap.proj (Fin.last n)).comp A.symm.toLinearEquiv.toLinearMap
  have hφ : φ = 0 := by
    apply (Pi.basisFun ℝ (Fin (n+1))).ext
    intro i
    have hzi := congrFun hz i
    simpa [inverseFinalRow, φ, Pi.basisFun_apply] using hzi
  have hh := DFunLike.congr_fun hφ (A (Pi.single (Fin.last n) 1))
  simp [φ] at hh

theorem inverseFinalRow_contDiffOn {n : ℕ} :
    ContDiffOn ℝ (⊤ : ℕ∞) (@inverseFinalRow n) {L | L.IsInvertible} := by
  intro L hL
  apply contDiffWithinAt_pi.mpr
  intro i
  exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n+1) => ℝ) (Fin.last n)).contDiff.contDiffAt.comp L
    (hL.contDiffAt_map_inverse.clm_apply contDiffAt_const)).contDiffWithinAt

def negativeUnitVector {m : ℕ} (v : Euclidean m) : Euclidean m :=
  (-(Real.sqrt (dotProduct v v))⁻¹) • v

theorem negativeUnitVector_contDiffOn {m : ℕ} :
    ContDiffOn ℝ (⊤ : ℕ∞) (@negativeUnitVector m) {v | v ≠ 0} := by
  have hdot : ContDiff ℝ (⊤ : ℕ∞) (fun v : Euclidean m => dotProduct v v) := by
    apply ContDiff.sum
    intro i _
    exact (contDiff_apply ℝ (fun _ : Fin m => ℝ) i).mul
      (contDiff_apply ℝ (fun _ : Fin m => ℝ) i)
  have hs : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun v : Euclidean m => Real.sqrt (dotProduct v v)) {v | v ≠ 0} :=
    hdot.contDiffOn.sqrt (fun v hv => dotProduct_self_eq_zero.not.mpr hv)
  exact (hs.inv (fun v hv => Real.sqrt_ne_zero'.mpr
    (lt_of_le_of_ne (Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i)))
      (Ne.symm (dotProduct_self_eq_zero.not.mpr hv))))).neg.smul contDiffOn_id

theorem negativeUnitVector_properties {m : ℕ} (a : Euclidean m) (ha : a ≠ 0) :
    dotProduct (negativeUnitVector a) (negativeUnitVector a) = 1 ∧
    dotProduct a (negativeUnitVector a) < 0 ∧
    LinearMap.ker (dotFunctional (negativeUnitVector a)) = LinearMap.ker (dotFunctional a) := by
  let d := dotProduct a a
  let s := Real.sqrt d
  have hd : 0 < d :=
    lt_of_le_of_ne (Finset.sum_nonneg (fun i _ => mul_self_nonneg (a i)))
      (Ne.symm (dotProduct_self_eq_zero.not.mpr ha))
  have hs : 0 < s := Real.sqrt_pos.mpr hd
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hss : s * s = d := Real.mul_self_sqrt hd.le
  change dotProduct ((-s⁻¹) • a) ((-s⁻¹) • a) = 1 ∧
    dotProduct a ((-s⁻¹) • a) < 0 ∧ _
  refine ⟨?_, ?_, ?_⟩
  · simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]
    change -s⁻¹ * (-s⁻¹ * d) = 1
    rw [← hss]
    field_simp
  · rw [dotProduct_smul, smul_eq_mul]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos (inv_pos.mpr hs)) hd
  · ext z
    change dotProduct ((-s⁻¹) • a) z = 0 ↔ dotProduct a z = 0
    rw [smul_dotProduct, smul_eq_mul]
    exact mul_eq_zero.trans (or_iff_right (neg_ne_zero.mpr (inv_ne_zero hs0)))

theorem negative_inverseFinalRow_contDiffOn {n : ℕ} :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun L : Euclidean (n+1) →L[ℝ] Euclidean (n+1) => negativeUnitVector (inverseFinalRow L))
      {L | L.IsInvertible} :=
  negativeUnitVector_contDiffOn.comp inverseFinalRow_contDiffOn
    (fun L hL => inverseFinalRow_ne_zero L hL)


theorem euclidean_differential_chart_operator {m : ℕ} {a : ModelKind} {M : Type}
    [TopologicalSpace M] (S : SmoothManifold m a M)
    (T : SmoothManifold m .euclidean (Euclidean m)) (j : M → Euclidean m)
    (hT : euclideanChart m ∈ T.smoothStructure.val) (hj : IsSmoothMap S T j)
    (q : M) (J : TangentSpace S q ≃ₗ[ℝ] Euclidean m)
    (hJ : IsEuclideanDifferential S T j q J.toLinearMap)
    (c : ModelChart m a M) (hc : c ∈ S.smoothStructure.val) (hq : q ∈ c.source)
    (E : TangentSpace S q ≃ₗ[ℝ] Euclidean m) (hE : IsChartCoordinates S q c E)
    (U : Set (Euclidean m)) (hU : IsOpen U) (hqU : (c q).val ∈ U)
    (H : Euclidean m → Euclidean m) (hH : ContDiffOn ℝ (⊤ : ℕ∞) H U)
    (heH : (fun y => H (c y).val) =ᶠ[𝓝 q] (fun y => (euclideanChart m (j y)).val)) :
    fderiv ℝ H (c q).val = ((E.symm.trans J).toContinuousLinearEquiv).toContinuousLinearMap := by
  obtain ⟨L, F, hL, hF, heq⟩ := hJ
  apply ContinuousLinearMap.ext
  intro z
  have hJac := differential_jacobian S T j hj q L hL c (euclideanChart m)
    hc hT hq (mem_univ _) E F hE hF U H hU hqU hH heH (E.symm z)
  rw [E.apply_symm_apply] at hJac
  change fderiv ℝ H (c q).val z = J (E.symm z)
  rw [← hJac]
  exact (DFunLike.congr_fun heq (E.symm z)).symm


theorem outward_normal_eq_chart_formula {n : ℕ} {M : Type} [TopologicalSpace M]
    (S : SmoothManifold (n+1) .halfSpace M)
    (B : SmoothManifold n .euclidean (intrinsicBoundary S)) (hB : IsNaturalBoundary S B)
    (p : intrinsicBoundary S) (J : TangentSpace S p.val ≃ₗ[ℝ] Euclidean (n+1))
    (K : TangentSpace B p →ₗ[ℝ] TangentSpace S p.val)
    (hK : IsDifferential B S Subtype.val p K)
    (c : ModelChart (n+1) .halfSpace M) (hc : c ∈ S.smoothStructure.val)
    (hp : p.val ∈ c.source) (E : TangentSpace S p.val ≃ₗ[ℝ] Euclidean (n+1))
    (hE : IsChartCoordinates S p.val c E)
    (L : Euclidean (n+1) →L[ℝ] Euclidean (n+1))
    (hL : L = ((E.symm.trans J).toContinuousLinearEquiv).toContinuousLinearMap)
    (ν : Euclidean (n+1))
    (hν : dotProduct ν ν = 1 ∧ IsOutward S p (J.symm ν) ∧
      LinearMap.range (J.toLinearMap.comp K) = LinearMap.ker (dotFunctional ν)) :
    ν = negativeUnitVector (inverseFinalRow L) := by
  classical
  let φ : Euclidean (n+1) →ₗ[ℝ] ℝ :=
    (LinearMap.proj (Fin.last n)).comp (E.toLinearMap.comp J.symm.toLinearMap)
  have hφ : φ ≠ 0 := by
    intro hz
    have hh := DFunLike.congr_fun hz (J (E.symm (Pi.single (Fin.last n) 1)))
    simp [φ] at hh
  have hrow : dotFunctional (inverseFinalRow L) = φ := by
    rw [hL]
    apply (Pi.basisFun ℝ (Fin (n+1))).ext
    intro i
    simp [dotFunctional, inverseFinalRow, φ, Pi.basisFun_apply]
  have hLinv : L.IsInvertible := by
    rw [hL]
    exact ContinuousLinearMap.isInvertible_equiv
  have hcandidate := negativeUnitVector_properties (inverseFinalRow L)
    (inverseFinalRow_ne_zero L hLinv)
  have hKimage := boundary_inclusion_image S B hB p c hc hp K hK E hE
  have himage : LinearMap.range (J.toLinearMap.comp K) = LinearMap.ker φ := by
    ext z
    change (∃ v, J (K v) = z) ↔ E (J.symm z) (Fin.last n) = 0
    rw [← hKimage.2]
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨v, (J.symm_apply_apply (K v)).symm⟩
    · rintro ⟨v, hv⟩
      exact ⟨v, by rw [hv, J.apply_symm_apply]⟩
  have hνφ : dotProduct ν ν = 1 ∧ φ ν < 0 ∧
      LinearMap.ker (dotFunctional ν) = LinearMap.ker φ :=
    ⟨hν.1, (BoundaryOrientations.outward_iff_coordinate S p c hc hp E hE (J.symm ν)).mp
      hν.2.1, hν.2.2.symm.trans himage⟩
  have hcandφ : dotProduct (negativeUnitVector (inverseFinalRow L))
      (negativeUnitVector (inverseFinalRow L)) = 1 ∧
      φ (negativeUnitVector (inverseFinalRow L)) < 0 ∧
      LinearMap.ker (dotFunctional (negativeUnitVector (inverseFinalRow L))) = LinearMap.ker φ := by
    rw [← hrow]
    exact hcandidate
  obtain ⟨w, hw, huniq⟩ := unit_normal_of_covector φ hφ
  exact (huniq ν hνφ).trans (huniq _ hcandφ).symm


theorem regular_domain_normal_smooth_aux {n : ℕ}
    (T : SmoothManifold (n+1) .euclidean (Euclidean (n+1)))
    (hT : euclideanChart (n+1) ∈ T.smoothStructure.val)
    (D : Set (Euclidean (n+1))) (S : SmoothManifold (n+1) .halfSpace D)
    (hj : IsSmoothMap S T Subtype.val)
    (B : SmoothManifold n .euclidean (intrinsicBoundary S)) (hB : IsNaturalBoundary S B)
    (J : (p : D) → TangentSpace S p ≃ₗ[ℝ] Euclidean (n+1))
    (hJ : ∀ p, IsEuclideanDifferential S T Subtype.val p (J p).toLinearMap)
    (K : (p : intrinsicBoundary S) → TangentSpace B p →ₗ[ℝ] TangentSpace S p.val)
    (hK : ∀ p, IsDifferential B S Subtype.val p (K p))
    (ν : intrinsicBoundary S → Euclidean (n+1))
    (hν : ∀ p, dotProduct (ν p) (ν p) = 1 ∧ IsOutward S p ((J p.val).symm (ν p)) ∧
      LinearMap.range ((J p.val).toLinearMap.comp (K p)) = LinearMap.ker (dotFunctional (ν p))) :
    VectorSmooth B.smoothStructure.val ν := by
  intro p
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p.val
  obtain ⟨U, hU, hpU, H, hH, heH⟩ :=
    (hj p.val).2 c hc (euclideanChart (n+1)) hT hp (mem_univ _)
  let E := coordinateDerivationEquiv S p.val c hc hp
  have hE := coordinateDerivationEquiv_isChartCoordinates S p.val c hc hp
  have hA := euclidean_differential_chart_operator S T Subtype.val hT hj p.val
    (J p.val) (hJ p.val) c hc hp E hE U hU hpU H hH heH
  have hinv : (fderiv ℝ H (c p.val).val).IsInvertible := by
    rw [hA]
    exact ContinuousLinearMap.isInvertible_equiv
  have hder : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ H) U :=
    hH.fderiv_of_isOpen hU (by simp)
  let V := U ∩ (fderiv ℝ H) ⁻¹' {L | L.IsInvertible}
  have hV : IsOpen V := hder.continuousOn.isOpen_inter_preimage hU
    ContinuousLinearMap.isOpen_setOfPred_isInvertible
  have hpV : (c p.val).val ∈ V := ⟨hpU, hinv⟩
  let F : Euclidean (n+1) → Euclidean (n+1) :=
    fun z => negativeUnitVector (inverseFinalRow (fderiv ℝ H z))
  have hF : ContDiffOn ℝ (⊤ : ℕ∞) F V :=
    negative_inverseFinalRow_contDiffOn.comp (hder.mono inter_subset_left) (fun _ hz => hz.2)
  let G : D → Euclidean (n+1) := fun q => F (c q).val
  have hG : VectorSmoothAt S.smoothStructure.val G p.val :=
    vectorSmoothAt_of_chart S G p.val c hc hp V hV hpV F hF Filter.EventuallyEq.rfl
  have hGB : VectorSmoothAt B.smoothStructure.val (fun q : intrinsicBoundary S => G q.val) p :=
    hG.comp S.smoothStructure.property.1.1 (hB.1 p)
  apply hGB.congr
  have hcont : ContinuousAt (fun q : D => (c q).val) p.val :=
    continuous_subtype_val.continuousAt.comp (c.continuousAt hp)
  obtain ⟨W, hWsub, hW, hpW⟩ := mem_nhds_iff.mp heH
  have hevent : ∀ᶠ q : D in 𝓝 p.val,
      q ∈ c.source ∧ q ∈ W ∧ (c q).val ∈ U := by
    filter_upwards [c.open_source.mem_nhds hp, hW.mem_nhds hpW,
      hcont.preimage_mem_nhds (hU.mem_nhds hpU)] with q hqc hqW hqU
    exact ⟨hqc, hqW, hqU⟩
  have heventB := (continuous_subtype_val.continuousAt :
    ContinuousAt (Subtype.val : intrinsicBoundary S → D) p).eventually hevent
  filter_upwards [heventB] with q hq
  have heHq : (fun y => H (c y).val) =ᶠ[𝓝 q.val]
      (fun y => (euclideanChart (n+1) (Subtype.val y)).val) :=
    Filter.mem_of_superset (hW.mem_nhds hq.2.1) hWsub
  let Eq := coordinateDerivationEquiv S q.val c hc hq.1
  have hEq := coordinateDerivationEquiv_isChartCoordinates S q.val c hc hq.1
  have hAq := euclidean_differential_chart_operator S T Subtype.val hT hj q.val
    (J q.val) (hJ q.val) c hc hq.1 Eq hEq U hU hq.2.2 H hH heHq
  exact (outward_normal_eq_chart_formula S B hB q (J q.val) (K q) (hK q)
    c hc hq.1 Eq hEq (fderiv ℝ H (c q.val).val) hAq (ν q) (hν q)).symm


/-- The outward unit normal constructed for every regular domain is smooth in
its actual natural boundary structure and the local ambient-extension sense. -/
theorem regular_domain_normal_field_smooth {n : ℕ}
    (T : SmoothManifold (n+1) .euclidean (Euclidean (n+1)))
    (hT : euclideanChart (n+1) ∈ T.smoothStructure.val)
    (D : Set (Euclidean (n+1))) (S : SmoothManifold (n+1) .halfSpace D)
    (hD : IsRegularDomain T D S) :
    ∃ (B : SmoothManifold n .euclidean (intrinsicBoundary S))
      (J : (p : D) → TangentSpace S p ≃ₗ[ℝ] Euclidean (n+1))
      (K : (p : intrinsicBoundary S) → TangentSpace B p →ₗ[ℝ] TangentSpace S p.val)
      (ν : intrinsicBoundary S → Euclidean (n+1)),
      IsNaturalBoundary S B ∧
      (∀ p, IsEuclideanDifferential S T Subtype.val p (J p).toLinearMap) ∧
      VectorSmooth B.smoothStructure.val ν ∧
      ∀ p, IsDifferential B S Subtype.val p (K p) ∧
        dotProduct (ν p) (ν p) = 1 ∧ IsOutward S p ((J p.val).symm (ν p)) ∧
        LinearMap.range ((J p.val).toLinearMap.comp (K p)) =
          LinearMap.ker (dotFunctional (ν p)) := by
  obtain ⟨B, J, K, ν, hB, hJ, hnormal⟩ := regular_domain_normal_field T hT D S hD
  exact ⟨B, J, K, ν, hB, hJ, regular_domain_normal_smooth_aux T hT D S hD.2.1
    B hB J hJ K (fun p => (hnormal p).1) ν (fun p => (hnormal p).2), hnormal⟩

theorem surface_geometry :
    Specs.SmoothManifolds.Integration.ClassicalBoundaryGeometry.surface_geometryType := by
  intro a M _ S T j hT hj o C A
  obtain ⟨J, g, ω, ν, hJ, hg, hω, hν⟩ := surface_metric_volume S T j hT hj o C A
  have hcross (p : M) (u v : TangentSpace S p) :
      crossProduct (J p u) (J p v) =
        pairing p (ω.field p) (exteriorPower.ιMulti ℝ 2 ![u, v]) • ν p := by
    obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
    let E := coordinateDerivationEquiv S p c hc hp
    let b := (Pi.basisFun ℝ (Fin 2)).map E.symm
    exact surface_cross_all b (J p) (o.val p)
      (exteriorPower.pairingDual ℝ (TangentSpace S p) 2 (ω.field p)) (ν p)
      (fun x y hxy => ((hν p).2.2 x y hxy).2) u v
  exact ⟨J, g, ω, ν, hJ, hg, hω,
    surface_normal_smooth S T j hT hj C A ω J hJ ν hcross,
    fun p => ⟨(hν p).1, (hν p).2.1⟩, hcross,
    fun p u v huv => ((hν p).2.2 u v huv).1⟩

def ambientVolumePullback {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (J : V →ₗ[ℝ] Euclidean n) : ExteriorData.Fiber V n :=
  exteriorPower.ιMulti ℝ n (fun i => ((Pi.basisFun ℝ (Fin n)).coord i).comp J)

theorem ambientVolume_pairing {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (J : V →ₗ[ℝ] Euclidean n) :
    exteriorPower.pairingDual ℝ V n (ambientVolumePullback J) =
      (standardAmbientDet n).comp (exteriorPower.map n J) := by
  apply exteriorPower.linearMap_ext
  ext v
  simp [ambientVolumePullback, standardAmbientDet,
    exteriorPower.pairingDual_ιMulti_ιMulti,
    Function.comp_def]
  rfl

theorem ambientVolume_ne_zero {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (J : V ≃ₗ[ℝ] Euclidean n) : ambientVolumePullback J.toLinearMap ≠ 0 := by
  intro hz
  have he := congrArg (fun L : (⋀[ℝ]^n V) →ₗ[ℝ] ℝ =>
      L (exteriorPower.ιMulti ℝ n (fun i => J.symm ((Pi.basisFun ℝ (Fin n)) i))))
    (ambientVolume_pairing J.toLinearMap)
  simp [hz, standardAmbientDet, Function.comp_def] at he
  have hb : (Matrix.detRowAlternating (fun x : Fin n => Pi.single x (1 : ℝ))) = 1 := by
    have hfamily : (fun x : Fin n => Pi.single x (1 : ℝ)) =
        (Pi.basisFun ℝ (Fin n) : Fin n → Euclidean n) := by
      funext i
      exact (Pi.basisFun_apply ℝ (Fin n) i).symm
    rw [hfamily]
    simpa only [Pi.basisFun_det] using
      (Module.Basis.det_self (Pi.basisFun ℝ (Fin n)))
  rw [hb] at he
  exact zero_ne_one he

theorem contDiff_matrix_det (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun A : Fin n → Euclidean n => (Matrix.of A).det) := by
  simp_rw [Matrix.det_apply']
  apply ContDiff.sum
  intro σ _
  apply contDiff_const.mul
  apply contDiff_prod
  intro i _
  exact (contDiff_apply ℝ (fun _ : Fin n => ℝ) i).comp
    (contDiff_apply ℝ (fun _ : Fin n => Euclidean n) (σ i))

theorem ambientVolume_coefficients {n : ℕ} {a : ModelKind} {M : Type}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (J : (p : M) → TangentSpace S p →ₗ[ℝ] Euclidean n)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (p : c.source) (I : ExteriorData.Index n n) :
    coefficients C n c hc (fun p => ambientVolumePullback (J p)) p I =
      (Matrix.of (fun i => J p.val
        ((C.tangent.fiberCoordinates.equiv c hc p.val p.property).symm
          ((Pi.basisFun ℝ (Fin n)) i)))).det := by
  rw [OrientationResults.topIndex_unique I,
    ← OrientationResults.pairing_coordinateVector_eq_coefficients]
  change exteriorPower.pairingDual ℝ (TangentSpace S p.val) n
    (ambientVolumePullback (J p.val))
      (coordinateVector C.tangent.fiberCoordinates c hc p) = _
  rw [ambientVolume_pairing]
  simp [coordinateVector, standardAmbientDet, Function.comp_def]
  rfl

theorem ambientVolume_smooth {n : ℕ} {a : ModelKind} {M : Type}
    [TopologicalSpace M] (S : SmoothManifold n a M)
    (T : SmoothManifold n .euclidean (Euclidean n)) (j : M → Euclidean n)
    (hT : euclideanChart n ∈ T.smoothStructure.val) (hj : IsSmoothMap S T j)
    (C : CotangentBundle S) (D : FormBundle C n)
    (J : (p : M) → TangentSpace S p →ₗ[ℝ] Euclidean n)
    (hJ : ∀ p, IsEuclideanDifferential S T j p (J p)) :
    IsForm D (fun p => ambientVolumePullback (J p)) := by
  apply (ExteriorAlgebraResults.smooth_iff_coefficients C n D _).mpr
  intro c hc I p
  letI := C.realization.space.topology
  let B := C.realization.space.bundle
  let k : TangentIndex S := ⟨c, hc⟩
  have hpB : p.val ∈ B.baseSet k := by
    change p.val ∈ C.realization.space.bundle.baseSet k
    rw [C.realization.baseSet]
    exact p.property
  have heq (q : c.source) (i : Fin n) :
      (B.trivialization k).symm q.val (Pi.single i 1) =
        (C.tangent.fiberCoordinates.equiv c hc q.val q.property).symm
          ((Pi.basisFun ℝ (Fin n)) i) := by
    have hqB : q.val ∈ B.baseSet k := by
      change q.val ∈ C.realization.space.bundle.baseSet k
      rw [C.realization.baseSet]
      exact q.property
    have hcoord : B.fiberCoordinates k q.val hqB =
        C.tangent.fiberCoordinates.equiv c hc q.val q.property := by
      apply LinearEquiv.ext
      intro v
      exact C.realization.coordinates k q.val q.property v
    rw [← BundleData.SmoothVectorBundle.fiberCoordinates_symm_apply B k q.val hqB,
      hcoord, Pi.basisFun_apply]
  have hs : VectorSmoothAt (openSubsetAtlas S.smoothStructure.val c.source c.open_source)
      (fun q : c.source => fun i : Fin n =>
        J q.val ((B.trivialization k).symm q.val (Pi.single i 1))) p := by
    apply FrameData.VectorSmoothAt.pi
    intro i
    exact OrientationResults.vectorSmoothAt_restrict c.source c.open_source p
      (euclidean_frame_smooth S T j hT hj C J hJ k i p.val hpB)
  have hd := hs.postcomp (contDiff_matrix_det n)
  convert hd using 1
  funext q
  rw [ambientVolume_coefficients]
  apply congrArg (fun A : Fin n → Euclidean n => (Matrix.of A).det)
  funext i
  exact congrArg (J q.val) (heq q i).symm

/-- The actual smooth full-dimensional Euclidean differential constructs the
standard orientation. No normal or sign certificate is assumed, and `n = 0`
is included. -/
theorem euclidean_orientation_of_differential {n : ℕ} {a : ModelKind} {M : Type}
    [TopologicalSpace M] (S : SmoothManifold n a M)
    (T : SmoothManifold n .euclidean (Euclidean n)) (j : M → Euclidean n)
    (hT : euclideanChart n ∈ T.smoothStructure.val) (hj : IsSmoothMap S T j)
    (J : (p : M) → TangentSpace S p ≃ₗ[ℝ] Euclidean n)
    (hJ : ∀ p, IsEuclideanDifferential S T j p (J p).toLinearMap) :
    ∃ o : Orientation S, ∀ p (η : DeterminantLine S p),
      IsPositive (o.val p) η ↔
        0 < standardAmbientDet n (exteriorPower.map n (J p).toLinearMap η) := by
  obtain ⟨C⟩ := BundleOperations.exists_cotangent S
  obtain ⟨D⟩ := ExteriorAlgebraResults.exists_formBundle C n
  let ω : NonvanishingTopForm D :=
    ⟨⟨(fun p => ambientVolumePullback (J p).toLinearMap),
      ambientVolume_smooth S T j hT hj C D (fun p => (J p).toLinearMap) hJ⟩,
      fun p => ambientVolume_ne_zero (J p)⟩
  obtain ⟨o, ho, _⟩ := OrientationResults.form_orientation_exists_unique
    ExteriorAlgebraResults.alternating_interpretation
    ExteriorAlgebraResults.smooth_iff_coefficients S C D ω
  refine ⟨o, ?_⟩
  intro p η
  have hh := ho p η
  change IsPositive (o.val p) η ↔
    0 < exteriorPower.pairingDual ℝ (TangentSpace S p) n
      (ambientVolumePullback (J p).toLinearMap) η at hh
  rw [ambientVolume_pairing] at hh
  exact hh

theorem euclidean_orientation_frame {n : ℕ} {a : ModelKind} {M : Type}
    [TopologicalSpace M] (S : SmoothManifold n a M)
    (T : SmoothManifold n .euclidean (Euclidean n)) (j : M → Euclidean n)
    (hT : euclideanChart n ∈ T.smoothStructure.val) (hj : IsSmoothMap S T j)
    (J : (p : M) → TangentSpace S p ≃ₗ[ℝ] Euclidean n)
    (hJ : ∀ p, IsEuclideanDifferential S T j p (J p).toLinearMap) :
    ∃ o : Orientation S, ∀ p (v : Fin n → TangentSpace S p),
      IsPositive (o.val p) (exteriorPower.ιMulti ℝ n v) ↔
        0 < (Matrix.of (fun i => J p (v i))).det := by
  obtain ⟨o, ho⟩ := euclidean_orientation_of_differential S T j hT hj J hJ
  refine ⟨o, ?_⟩
  intro p v
  rw [ho]
  change (0 < standardAmbientDet n (exteriorPower.map n (J p).toLinearMap
    (exteriorPower.ιMulti ℝ n v))) ↔ _
  rw [exteriorPower.map_apply_ιMulti]
  simp only [standardAmbientDet, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    Pi.basisFun_det_apply, Function.comp_def]
  rfl


theorem regular_domain_standard_orientation :
    Specs.SmoothManifolds.Integration.ClassicalBoundaryGeometry.regular_domain_standard_orientationType := by
  intro m a T hT D S hD
  classical
  choose J hJ using regular_domain_tangent T hT D S hD
  obtain ⟨o, ho⟩ := euclidean_orientation_of_differential S T Subtype.val hT hD.2.1 J hJ
  exact ⟨J, o, hJ, ho⟩

theorem normalWedge_one {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (K : W →ₗ[ℝ] V) (u : V) (w : W) :
    normalWedge K u (exteriorPower.ιMulti ℝ 1 ![w]) =
      exteriorPower.ιMulti ℝ 2 ![u, K w] := by
  apply Subtype.ext
  simp [BoundaryOrientations.coe_normalWedge, exteriorPower.ιMulti_apply_coe,
    ExteriorAlgebra.ιMulti_succ_apply]

theorem metricVolume_positive_iff {n : ℕ} {a : ModelKind} {M : Type*}
    [TopologicalSpace M] (S : SmoothManifold n a M) (C : CotangentBundle S)
    (A : FormBundle C n) (g : Metric C) (o : Orientation S) (ω : Form A)
    (hω : IsMetricVolume g o ω) (p : M) (η : DeterminantLine S p) :
    IsPositive (o.val p) η ↔ 0 < pairing p (ω.field p) η := by
  letI := (tangent_dimension S p).1
  apply OrientationResults.positive_ray_characterization
    (OrientationResults.determinant_finrank S p) (o.val p)
    (exteriorPower.pairingDual ℝ (TangentSpace S p) n (ω.field p))
  intro ζ hζ
  change 0 < pairing p (ω.field p) ζ
  rw [MetricVolumeResults.metricVolume_evaluate_positive g o ω hω p ζ hζ]
  exact MetricVolumeResults.determinantNorm_pos g p ζ hζ.choose

/-- Classical surface boundary directions are exactly the directions whose
outward-first ambient cross product has positive component along the
compatible normal. Both differentials are the genuine intrinsic ones. -/
theorem surface_boundary_direction_aux {a : ModelKind} {M : Type} [TopologicalSpace M]
    (S : SmoothManifold 2 a M)
    (B : SmoothManifold 1 .euclidean (intrinsicBoundary S))
    (o : Orientation S) (b : Orientation B) (hb : IsInducedOrientation o b)
    (C : CotangentBundle S) (A : FormBundle C 2) (g : Metric C)
    (ω : Form A) (hω : IsMetricVolume g o ω)
    (J : (p : M) → TangentSpace S p →ₗ[ℝ] Euclidean 3)
    (ν : M → Euclidean 3) (hν : ∀ p, dotProduct (ν p) (ν p) = 1)
    (hcross : ∀ p u v, crossProduct (J p u) (J p v) =
      pairing p (ω.field p) (exteriorPower.ιMulti ℝ 2 ![u, v]) • ν p)
    (p : intrinsicBoundary S)
    (K : TangentSpace B p →ₗ[ℝ] TangentSpace S p.val)
    (hK : IsDifferential B S Subtype.val p K)
    (u : TangentSpace S p.val) (hu : IsOutward S p u)
    (w : TangentSpace B p) :
    IsPositive (b.val p) (exteriorPower.ιMulti ℝ 1 ![w]) ↔
      0 < dotProduct (ν p.val) (crossProduct (J p.val u) (J p.val (K w))) := by
  rw [hb p K hK u hu, normalWedge_one,
    metricVolume_positive_iff S C A g o ω hω p.val,
    hcross, dotProduct_smul, hν]
  simp


/-- Every actual embedded oriented surface with boundary has its intrinsic
outward-first boundary orientation characterized by the ambient cross product.
No compactness is required. The surface normal, metric and volume are concluded.
-/
theorem surface_boundary_direction {a : ModelKind} {M : Type} [TopologicalSpace M]
    (S : SmoothManifold 2 a M)
    (T : SmoothManifold 3 .euclidean (Euclidean 3)) (j : M → Euclidean 3)
    (hT : euclideanChart 3 ∈ T.smoothStructure.val) (hj : IsSmoothEmbedding S T j)
    (o : Orientation S) (C : CotangentBundle S) (A : FormBundle C 2) :
    ∃ (B : SmoothManifold 1 .euclidean (intrinsicBoundary S)) (b : Orientation B)
      (J : (p : M) → TangentSpace S p →ₗ[ℝ] Euclidean 3)
      (g : Metric C) (ω : Form A) (ν : M → Euclidean 3),
      IsNaturalBoundary S B ∧ IsInducedOrientation o b ∧
      (∀ p, IsEuclideanDifferential S T j p (J p)) ∧
      (∀ p, metricForm g p = euclideanPullback (J p)) ∧ IsMetricVolume g o ω ∧
      VectorSmooth S.smoothStructure.val ν ∧
      (∀ p, dotProduct (ν p) (ν p) = 1 ∧ ∀ v, dotProduct (ν p) (J p v) = 0) ∧
      ∀ (p : intrinsicBoundary S)
        (K : TangentSpace B p →ₗ[ℝ] TangentSpace S p.val),
        IsDifferential B S Subtype.val p K →
        ∀ u, IsOutward S p u → ∀ w,
          (IsPositive (b.val p) (exteriorPower.ιMulti ℝ 1 ![w]) ↔
            0 < dotProduct (ν p.val) (crossProduct (J p.val u) (J p.val (K w)))) := by
  classical
  obtain ⟨B, hB⟩ := (BoundaryOrientations.boundary_orientation S o).1
  obtain ⟨b, ⟨hb, _⟩, _⟩ := (BoundaryOrientations.boundary_orientation S o).2 B hB
  obtain ⟨J, g, ω, ν, hJ, hg, hω, hν⟩ := surface_metric_volume S T j hT hj o C A
  have hcross (p : M) (u v : TangentSpace S p) :
      crossProduct (J p u) (J p v) =
        pairing p (ω.field p) (exteriorPower.ιMulti ℝ 2 ![u, v]) • ν p := by
    obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
    let E := coordinateDerivationEquiv S p c hc hp
    let bas := (Pi.basisFun ℝ (Fin 2)).map E.symm
    exact surface_cross_all bas (J p) (o.val p)
      (exteriorPower.pairingDual ℝ (TangentSpace S p) 2 (ω.field p)) (ν p)
      (fun u v huv => ((hν p).2.2 u v huv).2) u v
  refine ⟨B, b, J, g, ω, ν, hB, hb, hJ, hg, hω,
    surface_normal_smooth S T j hT hj C A ω J hJ ν hcross,
    fun p => ⟨(hν p).1, (hν p).2.1⟩, ?_⟩
  intro p K hK u hu w
  exact surface_boundary_direction_aux S B o b hb C A g ω hω J ν
    (fun p => (hν p).1) hcross p K hK u hu w

theorem outward_add_boundary {n : ℕ} {M : Type*} [TopologicalSpace M]
    (S : SmoothManifold (n+1) .halfSpace M)
    (B : SmoothManifold n .euclidean (intrinsicBoundary S)) (hB : IsNaturalBoundary S B)
    (p : intrinsicBoundary S) (K : TangentSpace B p →ₗ[ℝ] TangentSpace S p.val)
    (hK : IsDifferential B S Subtype.val p K)
    (u : TangentSpace S p.val) (hu : IsOutward S p u)
    (t : ℝ) (ht : 0 < t) (w : TangentSpace B p) :
    IsOutward S p (t • u + K w) := by
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p.val
  let E := coordinateDerivationEquiv S p.val c hc hp
  have hE := coordinateDerivationEquiv_isChartCoordinates S p.val c hc hp
  have hu' := (BoundaryOrientations.outward_iff_coordinate S p c hc hp E hE u).mp hu
  have hKw := ((boundary_inclusion_image S B hB p c hc hp K hK E hE).2 (K w)).mp ⟨w, rfl⟩
  apply (BoundaryOrientations.outward_iff_coordinate S p c hc hp E hE _).mpr
  simpa [map_add, map_smul, hKw] using mul_neg_of_pos_of_neg ht hu'


/-- Euclidean outward unit conormal in the genuine surface tangent plane,
constructed by orthogonal projection and normalization. -/
theorem surface_outward_unit_conormal {M : Type} [TopologicalSpace M]
    (S : SmoothManifold 2 .halfSpace M)
    (B : SmoothManifold 1 .euclidean (intrinsicBoundary S)) (hB : IsNaturalBoundary S B)
    (p : intrinsicBoundary S) (K : TangentSpace B p →ₗ[ℝ] TangentSpace S p.val)
    (hK : IsDifferential B S Subtype.val p K)
    (J : TangentSpace S p.val →ₗ[ℝ] Euclidean 3) (hJ : Function.Injective J) :
    ∃ μ : TangentSpace S p.val, IsOutward S p μ ∧ dotProduct (J μ) (J μ) = 1 ∧
      ∀ v, dotProduct (J μ) (J (K v)) = 0 := by
  classical
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p.val
  let E := coordinateDerivationEquiv S p.val c hc hp
  have hE := coordinateDerivationEquiv_isChartCoordinates S p.val c hc hp
  have hKinj := (boundary_inclusion_image S B hB p c hc hp K hK E hE).1
  obtain ⟨d, hd, hpd⟩ := B.smoothStructure.property.1.1 p
  let F := coordinateDerivationEquiv B p d hd hpd
  let w := F.symm (Pi.single 0 1)
  have hw : w ≠ 0 := by
    intro hz
    have hz' := congrArg F hz
    have hz'' := congrArg (fun z : Euclidean 1 => z 0) hz'
    simpa [w] using hz''
  let a := J (K w)
  have ha : a ≠ 0 := by
    intro hz
    apply hw
    apply hKinj
    apply hJ
    simpa only [map_zero] using hz
  let D := dotProduct a a
  have hD : 0 < D := dot_self_positive a ha
  let u := -E.symm (Pi.single (Fin.last 1) 1)
  have hu : IsOutward S p u := by
    apply (BoundaryOrientations.outward_iff_coordinate S p c hc hp E hE u).mpr
    simp [u]
  let q := dotProduct (J u) a / D
  let U := u + K (-q • w)
  have hU : IsOutward S p U := by
    simpa only [one_smul] using outward_add_boundary S B hB p K hK u hu 1
      zero_lt_one (-q • w)
  have horth : dotProduct (J U) a = 0 := by
    simp only [U, map_add, map_smul, add_dotProduct, smul_dotProduct,
      smul_eq_mul, neg_mul]
    change dotProduct (J u) a - q * D = 0
    dsimp only [q]
    rw [div_mul_cancel₀ _ hD.ne']
    ring
  have hU0 : J U ≠ 0 := by
    intro hz
    have hUzero : U = 0 := hJ (by simpa only [map_zero] using hz)
    have hh := (BoundaryOrientations.outward_iff_coordinate S p c hc hp E hE U).mp hU
    simpa [hUzero] using hh
  let r := Real.sqrt (dotProduct (J U) (J U))
  have hr : 0 < r := Real.sqrt_pos.mpr (dot_self_positive (J U) hU0)
  have hrr : r * r = dotProduct (J U) (J U) :=
    Real.mul_self_sqrt (dot_self_positive (J U) hU0).le
  let μ := r⁻¹ • U
  refine ⟨μ, ?_, ?_, ?_⟩
  · simpa only [map_zero, add_zero] using outward_add_boundary S B hB p K hK U hU
      r⁻¹ (inv_pos.mpr hr) 0
  · simp only [μ, map_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [← hrr]
    field_simp
  · intro v
    have hv : v = (F v 0) • w := by
      apply F.injective
      ext i
      fin_cases i
      simp [w]
    rw [hv]
    simp only [μ, map_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    change (F v 0) * (r⁻¹ * dotProduct (J U) a) = 0
    rw [horth]
    ring
theorem surface_unit_conormal {M : Type} [TopologicalSpace M]
    (S : SmoothManifold 2 .halfSpace M)
    (T : SmoothManifold 3 .euclidean (Euclidean 3)) (j : M → Euclidean 3)
    (hj : IsSmoothEmbedding S T j)
    (B : SmoothManifold 1 .euclidean (intrinsicBoundary S)) (hB : IsNaturalBoundary S B)
    (p : intrinsicBoundary S)
    (J : TangentSpace S p.val →ₗ[ℝ] Euclidean 3)
    (K : TangentSpace B p →ₗ[ℝ] TangentSpace S p.val)
    (hJ : IsEuclideanDifferential S T j p.val J)
    (hK : IsDifferential B S Subtype.val p K) :
    ∃ μ : TangentSpace S p.val, IsOutward S p μ ∧ dotProduct (J μ) (J μ) = 1 ∧
      ∀ v, dotProduct (J μ) (J (K v)) = 0 := by
  exact surface_outward_unit_conormal S B hB p K hK J
    (euclidean_differential_injective S T j hj p.val J hJ)

theorem normalWedge_ιMulti {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] {n : ℕ} (K : W →ₗ[ℝ] V) (ν : V)
    (v : Fin n → W) :
    normalWedge K ν (exteriorPower.ιMulti ℝ n v) =
      exteriorPower.ιMulti ℝ (n+1) (Fin.cons ν (fun i => K (v i))) := by
  apply Subtype.ext
  simp only [BoundaryOrientations.coe_normalWedge, exteriorPower.ιMulti_apply_coe,
    ExteriorAlgebra.map_apply_ιMulti, ExteriorAlgebra.ιMulti_succ_apply]
  simp [Matrix.vecTail, Function.comp_def]


/-- The intrinsic outward-first wedge is evaluated by the ordinary ambient
matrix determinant, with the normal in its first row, in every dimension. -/
theorem ambient_determinant_normalWedge {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] {n : ℕ} (J : V ≃ₗ[ℝ] Euclidean (n+1))
    (K : W →ₗ[ℝ] V) (ν : Euclidean (n+1)) (v : Fin n → W) :
    exteriorPower.alternatingMapLinearEquiv ((Pi.basisFun ℝ (Fin (n+1))).det)
      (exteriorPower.map (n+1) J.toLinearMap
        (normalWedge K (J.symm ν) (exteriorPower.ιMulti ℝ n v))) =
      Matrix.det (Fin.cons ν (fun i => J (K (v i)))) := by
  rw [normalWedge_ιMulti, exteriorPower.map_apply_ιMulti,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  have hcons : (fun i : Fin (n+1) => J (Fin.cons (α := fun _ => V) (J.symm ν) (fun i => K (v i)) i)) =
      Fin.cons ν (fun i => J (K (v i))) := by
    funext i
    cases i using Fin.cases <;> simp
  change (Pi.basisFun ℝ (Fin (n+1))).det
    (fun i => J (Fin.cons (α := fun _ => V) (J.symm ν) (fun i => K (v i)) i)) = _
  rw [hcons]
  rw [Module.Basis.det_apply]
  exact Matrix.det_transpose _

theorem regular_domain_normals :
    Specs.SmoothManifolds.Integration.ClassicalBoundaryGeometry.regular_domain_normalsType := by
  intro n a T hT D S hD
  cases a with
  | halfSpace => exact regular_domain_normal_field_smooth T hT D S hD
  | euclidean =>
    classical
    haveI : IsEmpty (intrinsicBoundary S) := by
      refine ⟨fun p => ?_⟩
      have hp := p.property
      simpa only [intrinsicBoundary_euclidean S, Set.mem_empty_iff_false] using hp
    choose J hJ using regular_domain_tangent T hT D S hD
    obtain ⟨B, hB⟩ := exists_boundary_smoothManifold S
    exact ⟨B, J, (fun p => isEmptyElim p), (fun _ => 0), hB, hJ,
      (fun p => isEmptyElim p), (fun p => isEmptyElim p)⟩

theorem zero_volume_of_negative_one {a : ModelKind} {M : Type*}
    [TopologicalSpace M] (S : SmoothManifold 0 a M) (C : CotangentBundle S)
    (D : FormBundle C 0) (g : Metric C) (o : Orientation S)
    (ω : Form D) (hω : IsMetricVolume g o ω) (p : M)
    (hneg : IsPositive (o.val p)
      (-((exteriorPower.zeroEquiv ℝ (TangentSpace S p)).symm 1))) :
    pairing p (ω.field p) ((exteriorPower.zeroEquiv ℝ (TangentSpace S p)).symm 1) = -1 := by
  let one := (exteriorPower.zeroEquiv ℝ (TangentSpace S p)).symm 1
  have hn : determinantNorm g p (-one) = 1 := by
    have he : determinantNorm g p (-one) = determinantNorm g p one := by
      simp only [determinantNorm, map_neg, LinearMap.neg_apply, neg_neg]
    exact he.trans (MetricVolumeResults.zero_norm g p)
  have he := hω p (-one) hneg hn
  change exteriorPower.pairingDual ℝ (TangentSpace S p) 0 (ω.field p) (-one) = 1 at he
  rw [map_neg] at he
  exact neg_eq_iff_eq_neg.mp he

/- The usual positively oriented interval retains signed endpoint volumes,
while its Euclidean zero-dimensional boundary density is one. -/
set_option maxHeartbeats 1600000 in
theorem interval_metric_sign (a b : ℝ) (hab : a < b) :
    ∃ S : SmoothManifold 1 .halfSpace (Icc a b),
    ∃ l r : ModelChart 1 .halfSpace (Icc a b),
      IsStandardInterval a b S l r ∧
      intrinsicBoundary S = {x | x.val = a ∨ x.val = b} ∧
      ∃ (o : Orientation S) (s : SignedCharts S),
        RepresentsSignedCharts o.val s ∧
        (∀ (hl : l ∈ S.smoothStructure.val) p, s.sign l hl p = true) ∧
        (∀ (hr : r ∈ S.smoothStructure.val) p, s.sign r hr p = false) ∧
        ∃ (B : SmoothManifold 0 .euclidean (intrinsicBoundary S)) (q : Orientation B),
          IsNaturalBoundary S B ∧ IsInducedOrientation o q ∧
          (∀ p : intrinsicBoundary S,
            (IsPositive (q.val p)
              ((exteriorPower.zeroEquiv ℝ (TangentSpace B p)).symm 1) ↔ p.val.val = b) ∧
            (IsPositive (q.val p)
              (-((exteriorPower.zeroEquiv ℝ (TangentSpace B p)).symm 1)) ↔ p.val.val = a)) ∧
          ∀ (C : CotangentBundle B) (A : FormBundle C 0) (g : Metric C),
            ∃ (ω : Form A) (ρ : DensityField B),
              IsMetricVolume g q ω ∧ IsMetricDensity g ρ ∧ IsSmoothDensity ρ ∧
              ∀ p : intrinsicBoundary S,
                pairing p (ω.field p)
                  ((exteriorPower.zeroEquiv ℝ (TangentSpace B p)).symm 1) =
                    (if p.val.val = a then -1 else 1) ∧
                (ρ p).val ((exteriorPower.zeroEquiv ℝ (TangentSpace B p)).symm 1) = 1 := by
  obtain ⟨S, l, r, hstd, hboundary, o, s, hos, hl, hr, B, q, hB, hq, hsigns⟩ :=
    BoundaryOrientations.interval_sign a b hab
  refine ⟨S, l, r, hstd, hboundary, o, s, hos, hl, hr, B, q, hB, hq, hsigns, ?_⟩
  intro C A g
  obtain ⟨ω, hω, _⟩ := MetricVolumeResults.volume_exists_unique B C A g q
  obtain ⟨ρ, hρ, _⟩ := MetricVolumeResults.density_exists_unique B C g
  refine ⟨ω, ρ, hω, hρ.1, hρ.2.1, ?_⟩
  intro p
  constructor
  · by_cases ha : p.val.val = a
    · rw [if_pos ha]
      exact zero_volume_of_negative_one B C A g q ω hω p ((hsigns p).2.mpr ha)
    · rw [if_neg ha]
      have hp : p.val.val = a ∨ p.val.val = b := by
        exact (Set.ext_iff.mp hboundary p.val).mp p.property
      exact hω p _ ((hsigns p).1.mpr (hp.resolve_left ha))
        (MetricVolumeResults.zero_norm g p)
  · rw [hρ.1]
    exact MetricVolumeResults.zero_norm g p


/-- Dot-product pullback on a smooth injective family of genuine differentials. -/
theorem euclidean_metric_of_injective {n N : ℕ} {a : ModelKind} {M : Type}
    [TopologicalSpace M] (S : SmoothManifold n a M)
    (T : SmoothManifold N .euclidean (Euclidean N)) (j : M → Euclidean N)
    (hT : euclideanChart N ∈ T.smoothStructure.val) (hj : IsSmoothMap S T j)
    (C : CotangentBundle S) (J : (p : M) → TangentSpace S p →ₗ[ℝ] Euclidean N)
    (hJ : ∀ p, IsEuclideanDifferential S T j p (J p))
    (hinj : ∀ p, Function.Injective (J p)) :
    ∃ g : Metric C, ∀ p, metricForm g p = euclideanPullback (J p) := by
  letI := C.realization.space.topology
  have hdot : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Euclidean N × Euclidean N => dotProduct z.1 z.2) := by
    apply ContDiff.sum
    intro i _
    exact ((contDiff_apply ℝ (fun _ : Fin N => ℝ) i).comp contDiff_fst).mul
      ((contDiff_apply ℝ (fun _ : Fin N => ℝ) i).comp contDiff_snd)
  refine ⟨{ form := fun p => euclideanPullback (J p)
            symmetric := fun p v w => by
              change dotProduct (J p v) (J p w) = dotProduct (J p w) (J p v)
              exact dotProduct_comm _ _
            positive := fun p v hv => dot_self_positive (J p v)
              (fun h => hv (hinj p (h.trans (J p).map_zero.symm)))
            smooth := ?_ }, fun _ => rfl⟩
  intro k i l p hp
  exact FrameData.VectorSmoothAt.postcomp (FrameData.VectorSmoothAt.prod
    (euclidean_frame_smooth S T j hT hj C J hJ k i p hp)
    (euclidean_frame_smooth S T j hT hj C J hJ k l p hp)) hdot

/-- Squaring normal-first determinant gives the tangential Gram determinant.
This includes the empty tangential frame. -/
theorem normal_determinant_sq {n : ℕ} (ν : Euclidean (n+1))
    (v : Fin n → Euclidean (n+1))
    (hunit : dotProduct ν ν = 1) (horth : ∀ i, dotProduct ν (v i) = 0) :
    (Matrix.of (Fin.cons ν v)).det ^ 2 =
      (Matrix.of (fun i j => dotProduct (v i) (v j))).det := by
  let A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ := Matrix.of (Fin.cons ν v)
  have hrow (j : Fin n) : (A * A.transpose) 0 j.succ = 0 := horth j
  have hzero : (A * A.transpose) 0 0 = 1 := hunit
  have hsub : (A * A.transpose).submatrix Fin.succ Fin.succ =
      Matrix.of (fun i j => dotProduct (v i) (v j)) := by rfl
  calc
    _ = (A * A.transpose).det := by
      rw [Matrix.det_mul, Matrix.det_transpose]
      exact pow_two _
    _ = _ := by
      rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
      simp [hzero, hrow, hsub]

/-- The Gram square root is the unsigned normal-first Euclidean determinant. -/
theorem normal_determinant_abs {n : ℕ} (ν : Euclidean (n+1))
    (v : Fin n → Euclidean (n+1))
    (hunit : dotProduct ν ν = 1) (horth : ∀ i, dotProduct ν (v i) = 0) :
    Real.sqrt (Matrix.of (fun i j => dotProduct (v i) (v j))).det =
      |(Matrix.of (Fin.cons ν v)).det| := by
  rw [← normal_determinant_sq ν v hunit horth, Real.sqrt_sq_eq_abs]

/-- The exterior-power bilinear form evaluates to the actual dot-product Gram
matrix, without assuming linear independence of the ordered tangent vectors. -/
theorem pullback_exterior_gram {V : Type*} [AddCommGroup V] [Module ℝ V]
    {n N : ℕ} (J : V →ₗ[ℝ] Euclidean N) (v : Fin n → V) :
    (euclideanPullback J).exteriorPower n (exteriorPower.ιMulti ℝ n v)
      (exteriorPower.ιMulti ℝ n v) =
      (Matrix.of (fun i j => dotProduct (J (v i)) (J (v j)))).det := by
  simp only [LinearMap.BilinForm.exteriorPower, LinearMap.comp_apply,
    exteriorPower.map_apply_ιMulti, exteriorPower.pairingDual_ιMulti_ιMulti]
  change (Matrix.of (fun i j => dotProduct (J (v j)) (J (v i)))).det = _
  exact congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A.det)
    (by funext i j; exact dotProduct_comm (J (v j)) (J (v i)))

theorem regular_domain_boundary_density :
    Specs.SmoothManifolds.Integration.ClassicalBoundaryGeometry.regular_domain_boundary_densityType := by
  intro n a T hT D S hD
  classical
  have hfield := @regular_domain_normals n a T hT D S hD
  rcases hfield with ⟨B, J, K, ν, hB, hJ, hνsmooth, hν⟩
  refine Exists.intro B ?_
  refine Exists.intro J ?_
  refine Exists.intro K ?_
  refine Exists.intro ν ?_
  apply And.intro hB
  apply And.intro hJ
  apply And.intro hνsmooth
  apply And.intro hν
  intro C
  let H := fun p : intrinsicBoundary S => (J p.val).toLinearMap.comp (K p)
  have hH (p : intrinsicBoundary S) :
      IsEuclideanDifferential B T (fun q : intrinsicBoundary S => q.val.val) p (H p) := by
    obtain ⟨L, F, hL, hF, hJL⟩ := hJ p.val
    refine ⟨L.comp (K p), F, differential_comp B S T Subtype.val Subtype.val hB.1 hD.2.1
      p (K p) L (hν p).1 hL, hF, ?_⟩
    dsimp only [H]
    rw [hJL]
    rfl
  have hinj (p : intrinsicBoundary S) : Function.Injective (H p) := by
    cases a with
    | halfSpace =>
      obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p.val
      exact (J p.val).injective.comp (boundary_inclusion_image S B hB p c hc hp (K p)
        (hν p).1 (coordinateDerivationEquiv S p.val c hc hp)
        (coordinateDerivationEquiv_isChartCoordinates S p.val c hc hp)).1
    | euclidean =>
      have hp := p.property
      have hfalse : False := by
        simpa only [intrinsicBoundary_euclidean S, Set.mem_empty_iff_false] using hp
      exact hfalse.elim
  have hj : IsSmoothMap B T (fun q : intrinsicBoundary S => q.val.val) :=
    manifoldContDiff_comp _ _ _ _ S.smoothStructure.property.1.1 _ _ hB.1 hD.2.1
  have hmetric : ∃ g : Metric C, ∀ p, metricForm g p = euclideanPullback (H p) := by
    exact euclidean_metric_of_injective B T (fun q : intrinsicBoundary S => q.val.val)
      hT hj C H hH hinj
  rcases hmetric with ⟨g, hg⟩
  have hdensity : ∃! ρ : DensityField B, IsMetricDensity g ρ ∧ IsSmoothDensity ρ ∧
      IsPositiveDensity ρ ∧ (∀ p, ρ p ≠ 0) ∧
      ∀ (A : FiberCoordinates B) (c : ModelChart n .euclidean (intrinsicBoundary S))
        (hc : c ∈ B.smoothStructure.val) (p : c.source),
        densityCoefficient A c hc p (ρ p.val) = Real.sqrt (metricMatrix g A c hc p).det := by
    exact MetricVolumeResults.density_exists_unique B C g
  rcases hdensity with ⟨ρ, hρ, _⟩
  refine ⟨g, ρ, hg, hρ.1, hρ.2.1, hρ.2.2.1, hρ.2.2.2.1, ?_, ?_⟩
  · intro p v
    calc
      (ρ p).val (exteriorPower.ιMulti ℝ n v) =
          determinantNorm g p (exteriorPower.ιMulti ℝ n v) := hρ.1 p _
      _ = Real.sqrt ((euclideanPullback (H p)).exteriorPower n
          (exteriorPower.ιMulti ℝ n v) (exteriorPower.ιMulti ℝ n v)) :=
        congrArg (fun b : LinearMap.BilinForm ℝ (TangentSpace B p) =>
          Real.sqrt (b.exteriorPower n (exteriorPower.ιMulti ℝ n v)
            (exteriorPower.ιMulti ℝ n v))) (hg p)
      _ = Real.sqrt (Matrix.of (fun i j => dotProduct (H p (v i)) (H p (v j)))).det :=
        congrArg Real.sqrt (pullback_exterior_gram (H p) v)
      _ = _ := ?_
    
    apply normal_determinant_abs (ν p) (fun i => J p.val (K p (v i))) (hν p).2.1
    intro i
    have hmem : H p (v i) ∈ LinearMap.ker (dotFunctional (ν p)) := by
      rw [← (hν p).2.2.2]
      exact ⟨v i, rfl⟩
    exact hmem
  · intro hn
    subst n
    intro p
    simpa [castExterior] using (hρ.1 p _).trans (MetricVolumeResults.zero_norm g p)

/-- The positive metric boundary volume equals insertion of the actual outward
Euclidean unit normal into the standard ambient determinant, on every ordered
boundary tuple, including the empty tuple in bulk dimension one. -/
theorem boundary_volume_comparison {n : ℕ} {a : ModelKind} {M : Type} [TopologicalSpace M]
    (S : SmoothManifold (n+1) a M)
    (B : SmoothManifold n .euclidean (intrinsicBoundary S))
    (o : Orientation S) (b : Orientation B) (hb : IsInducedOrientation o b)
    (C : CotangentBundle B) (A : FormBundle C n) (g : Metric C)
    (ω : Form A) (hω : IsMetricVolume g b ω) (p : intrinsicBoundary S)
    (J : TangentSpace S p.val ≃ₗ[ℝ] Euclidean (n+1))
    (K : TangentSpace B p →ₗ[ℝ] TangentSpace S p.val)
    (hK : IsDifferential B S Subtype.val p K)
    (ν : Euclidean (n+1)) (hνunit : dotProduct ν ν = 1)
    (hνout : IsOutward S p (J.symm ν))
    (hνrange : LinearMap.range (J.toLinearMap.comp K) = LinearMap.ker (dotFunctional ν))
    (hg : metricForm g p = euclideanPullback (J.toLinearMap.comp K))
    (Ω : DeterminantLine S p.val →ₗ[ℝ] ℝ)
    (hΩ : ∀ η, IsPositive (o.val p.val) η ↔ 0 < Ω η)
    (hΩframe : ∀ v : Fin (n+1) → TangentSpace S p.val,
      Ω (exteriorPower.ιMulti ℝ (n+1) v) = (Matrix.of (fun i => J (v i))).det) :
    ∀ v : Fin n → TangentSpace B p,
      pairing p (ω.field p) (exteriorPower.ιMulti ℝ n v) =
        (Matrix.of (Fin.cons ν (fun i => J (K (v i))))).det := by
  classical
  letI := (tangent_dimension B p).1
  let δ : DeterminantLine B p →ₗ[ℝ] ℝ :=
    Ω.comp (BoundaryOrientations.faceWedgeMap rfl K (J.symm ν))
  have hδ (v : Fin n → TangentSpace B p) :
      δ (exteriorPower.ιMulti ℝ n v) =
        (Matrix.of (Fin.cons ν (fun i => J (K (v i))))).det := by
    change Ω (normalWedge K (J.symm ν) (exteriorPower.ιMulti ℝ n v)) = _
    rw [normalWedge_ιMulti, hΩframe]
    have hrow : (fun i : Fin (n+1) => J (Fin.cons (α := fun _ => TangentSpace S p.val) (J.symm ν) (fun i => K (v i)) i)) =
        Fin.cons ν (fun i => J (K (v i))) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
    exact congrArg (fun f : Fin (n+1) → Euclidean (n+1) => (Matrix.of f).det) hrow
  have horth (v : TangentSpace B p) : dotProduct ν (J (K v)) = 0 := by
    have hm : J (K v) ∈ LinearMap.range (J.toLinearMap.comp K) := ⟨v, rfl⟩
    rw [hνrange] at hm
    exact hm
  have hδpos (η : DeterminantLine B p) (hη : IsPositive (b.val p) η) :
      0 < δ η := (hΩ _).mp ((hb p K hK (J.symm ν) hνout η).mp hη)
  obtain ⟨c, hc, hp⟩ := B.smoothStructure.property.1.1 p
  let E := coordinateDerivationEquiv B p c hc hp
  let bas := (Pi.basisFun ℝ (Fin n)).map E.symm
  have hbase : determinantNorm g p (exteriorPower.ιMulti ℝ n bas) =
      |δ (exteriorPower.ιMulti ℝ n bas)| := by
    unfold determinantNorm determinantMetric
    rw [hg, pullback_exterior_gram, hδ]
    exact normal_determinant_abs ν (fun i => J (K (bas i))) hνunit
      (fun i => horth (bas i))
  have hnorm (η : DeterminantLine B p) : determinantNorm g p η = |δ η| := by
    rw [MetricVolumeResults.determinant_expansion bas η,
      MetricVolumeResults.determinantNorm_smul, map_smul]
    simp only [smul_eq_mul, abs_mul, hbase]
  have hex : ∃ x : DeterminantLine B p, IsPositive (b.val p) x := by
    induction b.val p using Module.Ray.ind with | h x hx => exact ⟨x, hx, rfl⟩
  obtain ⟨x, hx⟩ := hex
  have heqx : pairing p (ω.field p) x = δ x := by
    rw [MetricVolumeResults.metricVolume_evaluate_positive g b ω hω p x hx,
      hnorm, abs_of_pos (hδpos x hx)]
  have hall (η : DeterminantLine B p) : pairing p (ω.field p) η = δ η := by
    obtain ⟨t, ht⟩ := exists_smul_eq_of_finrank_eq_one
      (OrientationResults.determinant_finrank B p) hx.1 η
    rw [← ht]
    change exteriorPower.pairingDual ℝ (TangentSpace B p) n (ω.field p) (t • x) = δ (t • x)
    rw [map_smul, map_smul]
    exact congrArg (fun z : ℝ => t • z) heqx
  intro v
  exact (hall _).trans (hδ v)

/-- Specialization of the signed comparison to the ordinary standard ambient
determinant. Its orientation criterion is the one constructed from the genuine
full-dimensional Euclidean differential. -/
theorem boundary_metric_volume_evaluate {n : ℕ} {a : ModelKind} {M : Type} [TopologicalSpace M]
    (S : SmoothManifold (n+1) a M)
    (B : SmoothManifold n .euclidean (intrinsicBoundary S))
    (o : Orientation S) (b : Orientation B) (hb : IsInducedOrientation o b)
    (C : CotangentBundle B) (A : FormBundle C n) (g : Metric C)
    (ω : Form A) (hω : IsMetricVolume g b ω) (p : intrinsicBoundary S)
    (J : TangentSpace S p.val ≃ₗ[ℝ] Euclidean (n+1))
    (K : TangentSpace B p →ₗ[ℝ] TangentSpace S p.val)
    (hK : IsDifferential B S Subtype.val p K)
    (ν : Euclidean (n+1)) (hνunit : dotProduct ν ν = 1)
    (hνout : IsOutward S p (J.symm ν))
    (hνrange : LinearMap.range (J.toLinearMap.comp K) = LinearMap.ker (dotFunctional ν))
    (hg : metricForm g p = euclideanPullback (J.toLinearMap.comp K))
    (hstandard : ∀ η : DeterminantLine S p.val,
      IsPositive (o.val p.val) η ↔
        0 < standardAmbientDet (n+1) (exteriorPower.map (n+1) J.toLinearMap η)) :
    ∀ v : Fin n → TangentSpace B p,
      pairing p (ω.field p) (exteriorPower.ιMulti ℝ n v) =
        (Matrix.of (Fin.cons ν (fun i => J (K (v i))))).det := by
  apply boundary_volume_comparison S B o b hb C A g ω hω p J K hK ν hνunit hνout
    hνrange hg ((standardAmbientDet (n+1)).comp (exteriorPower.map (n+1) J.toLinearMap))
    hstandard
  intro v
  change standardAmbientDet (n+1) (exteriorPower.map (n+1) J.toLinearMap
    (exteriorPower.ιMulti ℝ (n+1) v)) = _
  rw [exteriorPower.map_apply_ιMulti]
  simp only [standardAmbientDet, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    Pi.basisFun_det_apply, Function.comp_def]
  rfl


theorem regular_domain_boundary_geometry :
    Specs.SmoothManifolds.Integration.ClassicalBoundaryGeometry.regular_domain_boundary_geometryType := by
  intro n a T hT D S hD
  classical
  have hdata : ∃ (B : SmoothManifold n .euclidean (intrinsicBoundary S))
      (J : (p : D) → TangentSpace S p ≃ₗ[ℝ] Euclidean (n+1))
      (K : (p : intrinsicBoundary S) → TangentSpace B p →ₗ[ℝ] TangentSpace S p.val)
      (ν : intrinsicBoundary S → Euclidean (n+1)),
      IsNaturalBoundary S B ∧
      (∀ p, IsEuclideanDifferential S T Subtype.val p (J p).toLinearMap) ∧
      FrameData.VectorSmooth B.smoothStructure.val ν ∧
      (∀ p, IsDifferential B S Subtype.val p (K p) ∧
        dotProduct (ν p) (ν p) = 1 ∧ IsOutward S p ((J p.val).symm (ν p)) ∧
        LinearMap.range ((J p.val).toLinearMap.comp (K p)) =
          LinearMap.ker (dotFunctional (ν p))) ∧
      ∀ C : CotangentBundle B, ∃ (g : Metric C) (ρ : DensityField B),
        (∀ p, metricForm g p = euclideanPullback ((J p.val).toLinearMap.comp (K p))) ∧
        IsMetricDensity g ρ ∧ IsSmoothDensity ρ ∧ IsPositiveDensity ρ ∧
        (∀ p, ρ p ≠ 0) ∧
        (∀ p (v : Fin n → TangentSpace B p),
          (ρ p).val (exteriorPower.ιMulti ℝ n v) =
            |(Matrix.of (Fin.cons (ν p) (fun i => J p.val (K p (v i))))).det|) ∧
        (∀ hn : n = 0, ∀ p, (ρ p).val
          (castExterior hn.symm ((exteriorPower.zeroEquiv ℝ (TangentSpace B p)).symm 1)) = 1) := by
    exact regular_domain_boundary_density T hT D S hD
  rcases hdata with ⟨B, J, K, ν, hB, hJ, hνsmooth, hν, hC⟩
  have horientation : ∃ o : Orientation S, ∀ p (η : DeterminantLine S p),
      IsPositive (o.val p) η ↔
        0 < standardAmbientDet (n+1) (exteriorPower.map (n+1) (J p).toLinearMap η) := by
    exact euclidean_orientation_of_differential S T Subtype.val hT hD.2.1 J hJ
  rcases horientation with ⟨o, ho⟩
  have hboundary : ∃! b : Orientation B, IsInducedOrientation o b ∧
      ∃ G : LocalGenerators B, RepresentsGenerators b.val G := by
    exact (BoundaryOrientations.boundary_orientation S o).2 B hB
  rcases hboundary with ⟨b, ⟨hb, _⟩, _⟩
  refine ⟨B, J, K, ν, o, b, hB, hJ, hνsmooth, ho, hb, hν, ?_⟩
  intro C A
  have hmetricdensity : ∃ (g : Metric C) (ρ : DensityField B),
        (∀ p, metricForm g p = euclideanPullback ((J p.val).toLinearMap.comp (K p))) ∧
        IsMetricDensity g ρ ∧ IsSmoothDensity ρ ∧ IsPositiveDensity ρ ∧
        (∀ p, ρ p ≠ 0) ∧
        (∀ p (v : Fin n → TangentSpace B p),
          (ρ p).val (exteriorPower.ιMulti ℝ n v) =
            |(Matrix.of (Fin.cons (ν p) (fun i => J p.val (K p (v i))))).det|) ∧
        (∀ hn : n = 0, ∀ p, (ρ p).val
          (castExterior hn.symm ((exteriorPower.zeroEquiv ℝ (TangentSpace B p)).symm 1)) = 1) := hC C
  rcases hmetricdensity with ⟨g, ρ, hg, hρmetric, hρsmooth, hρpositive, hρnonzero, hdensity, hzero⟩
  have hvolume : ∃! ω : Form A, IsMetricVolume g b ω :=
    MetricVolumeResults.volume_exists_unique B C A g b
  obtain ⟨ω, hω, _⟩ := hvolume
  have hsigned (p : intrinsicBoundary S) (v : Fin n → TangentSpace B p) :
      pairing p (ω.field p) (exteriorPower.ιMulti ℝ n v) =
        (Matrix.of (Fin.cons (ν p) (fun i => J p.val (K p (v i))))).det :=
    boundary_metric_volume_evaluate S B o b hb C A g ω hω p (J p.val) (K p)
      (hν p).1 (ν p) (hν p).2.1 (hν p).2.2.1 (hν p).2.2.2 (hg p) (ho p.val) v
  refine ⟨g, ω, ρ, hg, hω, hρmetric, hρsmooth, hρpositive, hρnonzero,
    (fun p v => ⟨hsigned p v, hdensity p v⟩), ?_⟩
  intro hn
  subst n
  intro p
  constructor
  · have h := hsigned p (fun i => Fin.elim0 i)
    have he : exteriorPower.ιMulti ℝ 0 (fun i : Fin 0 => Fin.elim0 i) =
        (exteriorPower.zeroEquiv ℝ (TangentSpace B p)).symm 1 := by
      apply (exteriorPower.zeroEquiv ℝ (TangentSpace B p)).injective
      simp
    rw [he] at h
    simpa [castExterior, Matrix.det_fin_one] using h
  · exact hzero rfl p

end SmoothManifolds.ClassicalBoundaryResults

set_option maxHeartbeats 1200000

namespace SmoothManifolds.ClassicalBoundaryResults
open ModelData AtlasData MapData TangentData DifferentialData EmbeddedData
  MapClassData RegularDomainData BoundaryData BoundaryConeData
  BoundaryOrientationData ClassicalBoundaryData OrientationData Set Module
open SliceData Filter
open scoped Topology

/-- Every actual regular domain has a local smooth inward defining function,
whose derivative detects the genuine intrinsic outward half-space. -/
theorem regular_domain_local_defining_function {n : ℕ}
    (T : SmoothManifold (n+1) .euclidean (Euclidean (n+1)))
    (hT : euclideanChart (n+1) ∈ T.smoothStructure.val)
    (D : Set (Euclidean (n+1))) (S : SmoothManifold (n+1) .halfSpace D)
    (hD : IsRegularDomain T D S) (p : intrinsicBoundary S)
    (J : TangentSpace S p.val ≃ₗ[ℝ] Euclidean (n+1))
    (hJ : IsEuclideanDifferential S T Subtype.val p.val J.toLinearMap) :
    ∃ (U : Set (Euclidean (n+1))) (f : Euclidean (n+1) → ℝ)
      (L : Euclidean (n+1) →L[ℝ] ℝ),
      IsOpen U ∧ p.val.val ∈ U ∧ ContDiffOn ℝ (⊤ : ℕ∞) f U ∧
      HasFDerivAt f L p.val.val ∧ f p.val.val = 0 ∧
      (∀ q ∈ U, q ∈ D ↔ 0 ≤ f q) ∧
      (∀ v, IsOutward S p (J.symm v) ↔ L v < 0) := by
  have hTi : p.val.val ∈ manifoldInterior T :=
    ⟨euclideanChart (n+1), hT, mem_univ _, by simp [ModelData.modelSet]⟩
  obtain ⟨hmm, c, hc, hp, d, hd, hpd, V, hV, hpV, hVc, hform⟩ :=
    SliceStructures.immersion_coordinates S T Subtype.val hD.2.1 p.val
      (hD.2.2.2.1 p.val) hTi
  have hslice := SliceStructures.sliceEmbedding_self (n+1)
  let cr := c.restrOpen V hV
  obtain ⟨A, hA, hpA, hs⟩ := SliceStructures.localize_embedding_slice
    Subtype.val (SliceStructures.isEmbedding_of_range_homeomorph hD.2.2.2.2) cr d p.val
    (show p.val ∈ cr.source from ⟨hp, hpV⟩) le_rfl (fun _ => Nat.succ_pos _)
    (fun x hx => (hform x hx.2).1) (fun x hx => (hform x hx.2).2)
  let dr := d.restrOpen A hA
  have hsD : IsSliceChart D (n+1) .halfSpace dr := by
    simpa only [Subtype.range_coe] using hs
  obtain ⟨W, hW, hpW, F, hF, heF⟩ :=
    (hd (euclideanChart (n+1)) hT p.val.val hpd (mem_univ _)).2
  have heF' : F =ᶠ[𝓝 p.val.val] (fun x => (d x).val) := by
    exact heF
  obtain ⟨B, hBsub, hB, hpB⟩ := mem_nhds_iff.mp heF'
  let U := W ∩ B ∩ dr.source
  have hU : IsOpen U := (hW.inter hB).inter dr.open_source
  have hpU : p.val.val ∈ U := ⟨⟨hpW, hpB⟩, hpA⟩
  let f : Euclidean (n+1) → ℝ := fun x => F x (Fin.last n)
  let L : Euclidean (n+1) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (Fin.last n)).comp (fderiv ℝ F p.val.val)
  have hFd : HasFDerivAt F (fderiv ℝ F p.val.val) p.val.val :=
    ((hF.contDiffAt (hW.mem_nhds hpW)).differentiableAt (by simp)).hasFDerivAt
  have hfd : HasFDerivAt f L p.val.val :=
    (ContinuousLinearMap.proj (Fin.last n) : Euclidean (n+1) →L[ℝ] ℝ).hasFDerivAt.comp _ hFd
  have hface : (c p.val).val (Fin.last n) = 0 :=
    (intrinsicBoundary_iff_chart S c hc p.val hp).mp p.property
  have hz : f p.val.val = 0 := by
    change F p.val.val (Fin.last n) = 0
    have hFp : F p.val.val = (d p.val.val).val := hBsub hpB
    rw [hFp, (hform p.val hpV).2, hslice]
    exact hface
  have hmem (q : Euclidean (n+1)) (hq : q ∈ U) : q ∈ D ↔ 0 ≤ f q := by
    rw [RegularDomains.mem_iff_slice hsD hq.2, SliceStructures.coordinateSlice_full]
    change 0 ≤ (d q).val (Fin.last n) ↔ 0 ≤ F q (Fin.last n)
    rw [hBsub hq.1.2]
  let E := coordinateDerivationEquiv S p.val c hc hp
  have hE := coordinateDerivationEquiv_isChartCoordinates S p.val c hc hp
  obtain ⟨Q, hQ, hpQ, H, hH, heH⟩ :=
    (hD.2.1 p.val).2 c hc (euclideanChart (n+1)) hT hp (mem_univ _)
  have hdH : HasFDerivAt H (fderiv ℝ H (c p.val).val) (c p.val).val :=
    ((hH.contDiffAt (hQ.mem_nhds hpQ)).differentiableAt (by simp)).hasFDerivAt
  have hHbase : H (c p.val).val = p.val.val := by simpa using heH.eq_of_nhds
  have heFsub : (fun x : D => F x.val) =ᶠ[𝓝 p.val] (fun x => (d x.val).val) :=
    continuous_subtype_val.continuousAt.tendsto.eventually heF'
  have hcompgerm : (fun x : D => (F ∘ H) (c x).val) =ᶠ[𝓝 p.val]
      (fun x => (c x).val) := by
    filter_upwards [heH, heFsub, hV.mem_nhds hpV] with x hx hxF hxV
    change F (H (c x).val) = (c x).val
    change H (c x).val = x.val at hx
    rw [hx, hxF, (hform x hxV).2, hslice]
  have hcompd : HasFDerivAt (F ∘ H)
      ((fderiv ℝ F p.val.val).comp (fderiv ℝ H (c p.val).val)) (c p.val).val := by
    have hFd' : HasFDerivAt F (fderiv ℝ F p.val.val) (H (c p.val).val) := by
      rw [hHbase]
      exact hFd
    exact hFd'.comp _ hdH
  have hinv := FiniteRegularity.coordinateDerivative_eq c (fun x => (c x).val)
    p.val hp _ ⟨F ∘ H, hcompd, hcompgerm⟩
  change FiniteRegularityData.chartDerivative c c id p.val = _ at hinv
  rw [FiniteRegularity.chartDerivative_id c p.val hp] at hinv
  have hderH : fderiv ℝ H (c p.val).val =
      ((E.symm.trans J).toContinuousLinearEquiv).toContinuousLinearMap := by
    obtain ⟨I, G, hI, hG, heq⟩ := hJ
    apply ContinuousLinearMap.ext
    intro z
    have hJac := differential_jacobian S T Subtype.val hD.2.1 p.val I hI c
      (euclideanChart (n+1)) hc hT hp (mem_univ _) E G hE hG Q H hQ hpQ hH heH (E.symm z)
    rw [E.apply_symm_apply] at hJac
    change fderiv ℝ H (c p.val).val z = J (E.symm z)
    rw [← hJac]
    exact (DFunLike.congr_fun heq (E.symm z)).symm
  have hderF (v : Euclidean (n+1)) :
      fderiv ℝ F p.val.val v = E (J.symm v) := by
    have hh := DFunLike.congr_fun hinv (E (J.symm v))
    rw [hderH] at hh
    simpa using hh.symm
  refine ⟨U, f, L, hU, hpU, ?_, hfd, hz, hmem, ?_⟩
  · change ContDiffOn ℝ (⊤ : ℕ∞)
      ((ContinuousLinearMap.proj (Fin.last n) : Euclidean (n+1) →L[ℝ] ℝ) ∘ F) U
    exact ((ContinuousLinearMap.proj (Fin.last n) : Euclidean (n+1) →L[ℝ] ℝ).contDiff.comp_contDiffOn hF).mono
      (fun q hq => hq.1.1)
  · intro v
    change IsOutward S p (J.symm v) ↔ (fderiv ℝ F p.val.val v) (Fin.last n) < 0
    rw [hderF]
    exact BoundaryOrientations.outward_iff_coordinate S p c hc hp E hE (J.symm v)

end SmoothManifolds.ClassicalBoundaryResults

namespace SmoothManifolds.ClassicalBoundaryResults
open ModelData AtlasData MapData TangentData DifferentialData EmbeddedData
  MapClassData RegularDomainData BoundaryData BoundaryConeData
  BoundaryOrientationData ClassicalBoundaryData OrientationData Set Module
open Filter
open scoped Topology

/-- A positive transverse derivative enters the strictly positive side. -/
theorem positive_derivative_eventually_positive {f : ℝ → ℝ} {a : ℝ}
    (hf : HasDerivAt f a 0) (hzero : f 0 = 0) (ha : 0 < a) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < f t := by
  have hs : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t⁻¹ * f t := by
    simpa [hzero] using (tendsto_order.1 hf.tendsto_slope_zero_right).1 0 ha
  filter_upwards [hs, self_mem_nhdsWithin] with t ht htp
  exact (mul_pos_iff_of_pos_left (inv_pos.mpr htp)).mp ht

/-- For a local nonnegative defining function, inward transverse rays enter
actual ambient interior, while outward transverse rays enter the complement. -/
theorem local_defining_function_ray_sides {m : ℕ}
    {D U : Set (Euclidean m)} {p v : Euclidean m}
    {f : Euclidean m → ℝ} {L : Euclidean m →L[ℝ] ℝ}
    (hU : IsOpen U) (hpU : p ∈ U) (hfc : ContinuousOn f U)
    (hf : HasFDerivAt f L p)
    (hzero : f p = 0) (hside : ∀ q ∈ U, q ∈ D ↔ 0 ≤ f q) :
    (0 < L v → ∀ᶠ t in 𝓝[>] (0 : ℝ), p + t • v ∈ interior D) ∧
    (L v < 0 → ∀ᶠ t in 𝓝[>] (0 : ℝ), p + t • v ∉ D) := by
  have hl : HasDerivAt (fun t : ℝ => p + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p
  have hc : HasDerivAt (fun t : ℝ => f (p + t • v)) (L v) 0 := by
    convert hf.comp_hasDerivAt_of_eq 0 hl (by simp) using 1
    rfl
  have hcont : Tendsto (fun t : ℝ => p + t • v) (𝓝[>] 0) (𝓝 p) := by
    simpa using hl.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  constructor
  · intro hv
    have hpos := positive_derivative_eventually_positive hc (by simp [hzero]) hv
    filter_upwards [hpos, hcont.eventually (hU.mem_nhds hpU)] with t ht htU
    apply mem_interior_iff_mem_nhds.mpr
    have hposnbhd : {q | 0 < f q} ∈ 𝓝 (p + t • v) := by
      exact (hfc.continuousAt (hU.mem_nhds htU)).preimage_mem_nhds
        (Ioi_mem_nhds ht)
    exact Filter.mem_of_superset (inter_mem (hU.mem_nhds htU) hposnbhd)
      (fun q hq => (hside q hq.1).mpr hq.2.le)
  · intro hv
    have hneg : ∀ᶠ t in 𝓝[>] (0 : ℝ), f (p + t • v) < 0 := by
      simpa using positive_derivative_eventually_positive hc.neg (by simp [hzero])
        (neg_pos.mpr hv)
    filter_upwards [hneg, hcont.eventually (hU.mem_nhds hpU)] with t ht htU
    exact fun hq => (not_le_of_gt ht) ((hside _ htU).mp hq)

end SmoothManifolds.ClassicalBoundaryResults

namespace SmoothManifolds.ClassicalBoundaryResults
open ModelData AtlasData MapData TangentData DifferentialData EmbeddedData
  MapClassData RegularDomainData BoundaryData BoundaryConeData
  BoundaryOrientationData ClassicalBoundaryData OrientationData Set Module
open Filter
open scoped Topology

/-- The actual ambient ray pointing strictly inward enters the domain interior.
This is derived from the regular embedding, with no defining-function certificate
among the hypotheses. -/
theorem regular_domain_strict_inward_ray {n : ℕ}
    (T : SmoothManifold (n+1) .euclidean (Euclidean (n+1)))
    (hT : euclideanChart (n+1) ∈ T.smoothStructure.val)
    (D : Set (Euclidean (n+1))) (S : SmoothManifold (n+1) .halfSpace D)
    (hD : IsRegularDomain T D S) (p : intrinsicBoundary S)
    (J : TangentSpace S p.val ≃ₗ[ℝ] Euclidean (n+1))
    (hJ : IsEuclideanDifferential S T Subtype.val p.val J.toLinearMap)
    (v : Euclidean (n+1)) (hv : IsOutward S p (J.symm (-v))) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), p.val.val + t • v ∈ interior D := by
  obtain ⟨U, f, L, hU, hpU, hf, hfd, hz, hmem, hout⟩ :=
    regular_domain_local_defining_function T hT D S hD p J hJ
  have hvL : 0 < L v := by
    have h := (hout (-v)).mp hv
    simpa using h
  exact (local_defining_function_ray_sides hU hpU hf.continuousOn hfd hz hmem).1 hvL

/-- The actual ambient outward ray leaves the closed domain immediately. -/
theorem regular_domain_strict_outward_ray {n : ℕ}
    (T : SmoothManifold (n+1) .euclidean (Euclidean (n+1)))
    (hT : euclideanChart (n+1) ∈ T.smoothStructure.val)
    (D : Set (Euclidean (n+1))) (S : SmoothManifold (n+1) .halfSpace D)
    (hD : IsRegularDomain T D S) (p : intrinsicBoundary S)
    (J : TangentSpace S p.val ≃ₗ[ℝ] Euclidean (n+1))
    (hJ : IsEuclideanDifferential S T Subtype.val p.val J.toLinearMap)
    (v : Euclidean (n+1)) (hv : IsOutward S p (J.symm v)) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), p.val.val + t • v ∉ D := by
  obtain ⟨U, f, L, hU, hpU, hf, hfd, hz, hmem, hout⟩ :=
    regular_domain_local_defining_function T hT D S hD p J hJ
  exact (local_defining_function_ray_sides hU hpU hf.continuousOn hfd hz hmem).2
    ((hout v).mp hv)

end SmoothManifolds.ClassicalBoundaryResults

namespace SmoothManifolds.ClassicalBoundaryResults
open ModelData AtlasData BoundaryData BoundaryOrientationData Set

/-- Compact manifolds have finitely many open, compact, path-connected components.
The components are the actual connected subsets of the given topological space. -/
theorem compact_manifold_components {n : ℕ} {a : ModelKind} {M : Type}
    [TopologicalSpace M] (S : SmoothManifold n a M) [CompactSpace M] :
    Finite (ConnectedComponents M) ∧
      (range (connectedComponent (α := M))).Finite ∧
      ∀ p : M, IsOpen (connectedComponent p) ∧
        IsCompact (connectedComponent p) ∧ IsPathConnected (connectedComponent p) := by
  let : LocallyPathConnectedSpace M :=
    TopologicalManifold.locallyPathConnectedSpace S.topologicalManifold
  have : Finite (ConnectedComponents M) := inferInstance
  refine ⟨inferInstance, ?_, fun p => ⟨isOpen_connectedComponent,
    isClosed_connectedComponent.isCompact, TopologicalManifold.isPathConnected_connectedComponent S.topologicalManifold p⟩⟩
  let components : ConnectedComponents M → Set M :=
    Quotient.lift (connectedComponent (α := M)) (fun _ _ h => h)
  have hrange : range (connectedComponent (α := M)) = range components := by
    ext C
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨ConnectedComponents.mk p, rfl⟩
    · rintro ⟨c, rfl⟩
      obtain ⟨p, rfl⟩ := ConnectedComponents.surjective_coe c
      exact ⟨p, rfl⟩
  rw [hrange]
  exact finite_range components

/-- The actual natural boundary of a compact Euclidean subset with its given
full-dimensional smooth structure has finitely many
compact path-connected components. Their images under the actual inclusions
are actual compact path-connected ambient subsets. -/
theorem compact_subset_boundary_components {n : ℕ} {a : ModelKind}
    (D : Set (Euclidean (n+1))) (S : SmoothManifold (n+1) a D)
    (hcompact : IsCompact D) :
    ∃ B : SmoothManifold n .euclidean (intrinsicBoundary S),
      IsNaturalBoundary S B ∧ IsCompact (intrinsicBoundary S) ∧
      Finite (ConnectedComponents (intrinsicBoundary S)) ∧
      (range (connectedComponent (α := intrinsicBoundary S))).Finite ∧
      ∀ p : intrinsicBoundary S,
        IsOpen (connectedComponent p) ∧ IsCompact (connectedComponent p) ∧
        IsPathConnected (connectedComponent p) ∧
        IsCompact ((fun q : intrinsicBoundary S => q.val.val) '' connectedComponent p) ∧
        IsPathConnected ((fun q : intrinsicBoundary S => q.val.val) '' connectedComponent p) := by
  let : CompactSpace D := isCompact_iff_compactSpace.mp hcompact
  have hboundary : IsCompact (intrinsicBoundary S) := (isClosed_intrinsicBoundary S).isCompact
  let : CompactSpace (intrinsicBoundary S) := isCompact_iff_compactSpace.mp hboundary
  obtain ⟨B, hB⟩ := exists_boundary_smoothManifold S
  obtain ⟨hfinite, hsets, hcomponents⟩ := compact_manifold_components B
  refine ⟨B, hB, hboundary, hfinite, hsets, ?_⟩
  intro p
  obtain ⟨hopen, hcompact, hpath⟩ := hcomponents p
  have hc : Continuous (fun q : intrinsicBoundary S => q.val.val) :=
    continuous_subtype_val.comp continuous_subtype_val
  exact ⟨hopen, hcompact, hpath, hcompact.image hc, hpath.image hc⟩

end SmoothManifolds.ClassicalBoundaryResults

namespace SmoothManifolds.ClassicalBoundaryResults
open ModelData AtlasData MapData TangentData DifferentialData EmbeddedData
  MapClassData RegularDomainData BoundaryData BoundaryConeData
  BoundaryOrientationData ClassicalBoundaryData OrientationData Set Module
open BundleOperationsData MetricVolumeData FrameData BundleData TangentBundleData Filter ExteriorData
open scoped Topology
theorem planar_boundary_positive_iff_det {a : ModelKind} {M : Type}
    [TopologicalSpace M] (S : SmoothManifold 2 a M)
    (B : SmoothManifold 1 .euclidean (intrinsicBoundary S))
    (o : Orientation S) (b : Orientation B) (hb : IsInducedOrientation o b)
    (p : intrinsicBoundary S) (J : TangentSpace S p.val ≃ₗ[ℝ] Euclidean 2)
    (K : TangentSpace B p →ₗ[ℝ] TangentSpace S p.val)
    (hK : IsDifferential B S Subtype.val p K) (ν : Euclidean 2)
    (hout : IsOutward S p (J.symm ν))
    (hstandard : ∀ η : DeterminantLine S p.val,
      IsPositive (o.val p.val) η ↔
        0 < standardAmbientDet 2 (exteriorPower.map 2 J.toLinearMap η))
    (w : TangentSpace B p) :
    IsPositive (b.val p) (exteriorPower.ιMulti ℝ 1 ![w]) ↔
      0 < (Matrix.of ![ν, J (K w)]).det := by
  rw [hb p K hK (J.symm ν) hout, hstandard]
  change 0 < exteriorPower.alternatingMapLinearEquiv ((Pi.basisFun ℝ (Fin 2)).det)
    (exteriorPower.map 2 J.toLinearMap
      (normalWedge K (J.symm ν) (exteriorPower.ιMulti ℝ 1 ![w]))) ↔ _
  rw [ambient_determinant_normalWedge]
  rfl
/-- In the standard plane, rotating a boundary tangent to its left is a negative
multiple of the actual outward unit normal. -/
theorem planar_left_eq_normal {ν v : Euclidean 2}
    (hunit : dotProduct ν ν = 1) (horth : dotProduct ν v = 0) :
    rotateLeft v = (- (Matrix.of ![ν, v]).det) • ν := by
  have hu : ν 0 * ν 0 + ν 1 * ν 1 = 1 := by
    simpa [dotProduct, Fin.sum_univ_two] using hunit
  have ho : ν 0 * v 0 + ν 1 * v 1 = 0 := by
    simpa [dotProduct, Fin.sum_univ_two] using horth
  ext i
  fin_cases i
  · simp [rotateLeft, Matrix.det_fin_two, smul_eq_mul]
    linear_combination v 1 * hu - ν 1 * ho
  · simp [rotateLeft, Matrix.det_fin_two, smul_eq_mul]
    linear_combination ν 0 * ho - v 0 * hu

/-- The determinant sign is equivalent to actual local geometric sidedness,
with the domain's defining data derived from its given regular embedding. -/
theorem planar_left_enters_iff_det
    (T : SmoothManifold 2 .euclidean (Euclidean 2))
    (hT : euclideanChart 2 ∈ T.smoothStructure.val)
    (D : Set (Euclidean 2)) (S : SmoothManifold 2 .halfSpace D)
    (hD : IsRegularDomain T D S) (p : intrinsicBoundary S)
    (J : TangentSpace S p.val ≃ₗ[ℝ] Euclidean 2)
    (hJ : IsEuclideanDifferential S T Subtype.val p.val J.toLinearMap)
    (ν v : Euclidean 2) (hunit : dotProduct ν ν = 1)
    (hout : IsOutward S p (J.symm ν)) (horth : dotProduct ν v = 0) :
    0 < (Matrix.of ![ν, v]).det ↔
      ∀ᶠ t in 𝓝[>] (0 : ℝ), p.val.val + t • rotateLeft v ∈ interior D := by
  obtain ⟨U, f, L, hU, hpU, hf, hfd, hz, hmem, hsign⟩ :=
    regular_domain_local_defining_function T hT D S hD p J hJ
  have hνL : L ν < 0 := (hsign ν).mp hout
  have hleft : L (rotateLeft v) = -(Matrix.of ![ν, v]).det * L ν := by
    rw [planar_left_eq_normal hunit horth, map_smul]
    rfl
  have hsides := local_defining_function_ray_sides (v := rotateLeft v)
    hU hpU hf.continuousOn hfd hz hmem
  constructor
  · intro hdet
    apply hsides.1
    rw [hleft]
    exact mul_pos_of_neg_of_neg (neg_neg_of_pos hdet) hνL
  · intro hevent
    by_contra hdet
    rcases lt_or_eq_of_le (le_of_not_gt hdet) with hneg | hzero
    · have hnot := hsides.2 (by
        rw [hleft]
        exact mul_neg_of_pos_of_neg (neg_pos.mpr hneg) hνL)
      have hfalse : ∀ᶠ t in 𝓝[>] (0 : ℝ), False := by
        filter_upwards [hevent, hnot] with t ht ht'
        exact ht' (interior_subset ht)
      obtain ⟨t, ht⟩ := hfalse.exists
      exact ht
    · have hleftzero : rotateLeft v = 0 := by
        rw [planar_left_eq_normal hunit horth, hzero, neg_zero, zero_smul]
      have hpint : p.val.val ∈ interior D := by
        simpa only [hleftzero, smul_zero, add_zero, Filter.eventually_const] using hevent
      have hfrontier : Subtype.val '' intrinsicBoundary S = frontier D :=
        (RegularDomains.regular_domain_inclusion_topology RegularDomains.regular_domain_topology
          T D S (intrinsicBoundary_euclidean T) hD).2
      have hpfront : p.val.val ∈ frontier D := by
        rw [← hfrontier]
        exact ⟨p.val, p.property, rfl⟩
      exact hpfront.2 hpint

/-- The intrinsic outward-first planar boundary orientation is exactly the
orientation that keeps actual local domain interior geometrically on the left. -/
theorem planar_boundary_left :
    Specs.SmoothManifolds.Integration.ClassicalBoundaryGeometry.planar_boundary_leftType := by
  intro a T hT D S hD
  obtain ⟨B, J, K, ν, hB, hJ, hνsmooth, hnormal⟩ :=
    regular_domain_normals T hT D S hD
  have horientation : ∃ o : Orientation S, ∀ p (η : DeterminantLine S p),
      IsPositive (o.val p) η ↔
        0 < standardAmbientDet 2 (exteriorPower.map 2 (J p).toLinearMap η) :=
    euclidean_orientation_of_differential S T Subtype.val hT hD.2.1 J hJ
  obtain ⟨o, ho⟩ := horientation
  obtain ⟨b, ⟨hb, _⟩, _⟩ := (BoundaryOrientations.boundary_orientation S o).2 B hB
  refine ⟨B, J, K, o, b, hB, hJ, ho, hb, ?_⟩
  intro p
  refine ⟨(hnormal p).1, ?_⟩
  intro w
  rw [planar_boundary_positive_iff_det S B o b hb p (J p.val) (K p)
    (hnormal p).1 (ν p) (hnormal p).2.2.1 (ho p.val) w]
  cases a with
  | euclidean =>
    have hfalse : p.val ∈ (∅ : Set D) := by
      simpa only [intrinsicBoundary_euclidean S] using p.property
    exact False.elim hfalse
  | halfSpace =>
    apply planar_left_enters_iff_det T hT D S hD p (J p.val) (hJ p.val)
      (ν p) (J p.val (K p w)) (hnormal p).2.1 (hnormal p).2.2.1
    have hrange : J p.val (K p w) ∈ LinearMap.range ((J p.val).toLinearMap.comp (K p)) :=
      ⟨w, rfl⟩
    rw [(hnormal p).2.2.2] at hrange
    exact hrange

end SmoothManifolds.ClassicalBoundaryResults



set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace SmoothManifolds.ClassicalBoundaryResults
open ModelData AtlasData MapData TangentData DifferentialData EmbeddedData
  MapClassData RegularDomainData BoundaryData BoundaryConeData
  BoundaryOrientationData ClassicalBoundaryData OrientationData Set Module
open FrameData Filter SliceData
open scoped Topology

/-- Every smooth vector-valued map on a genuine embedded manifold has an
ambient smooth extension near each image point. The extension agrees on the
whole part of the image in the ambient neighborhood. -/
theorem embedded_vector_local_extension {n N : ℕ} {a : ModelKind} {M V : Type}
    [TopologicalSpace M] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (S : SmoothManifold n a M)
    (T : SmoothManifold N .euclidean (Euclidean N))
    (hT : euclideanChart N ∈ T.smoothStructure.val)
    (j : M → Euclidean N) (hj : IsSmoothEmbedding S T j)
    (f : M → V) (hf : VectorSmooth S.smoothStructure.val f) (p : M) :
    ∃ U : Set (Euclidean N), IsOpen U ∧ j p ∈ U ∧
      ∃ F : Euclidean N → V, ContDiffOn ℝ (⊤ : ℕ∞) F U ∧
        ∀ q, j q ∈ U → F (j q) = f q := by
  have hpTi : j p ∈ manifoldInterior T :=
    ⟨euclideanChart N, hT, mem_univ _, by simp [ModelData.modelSet]⟩
  obtain ⟨hnN, c, hc, hpc, d, hd, hpd, W, hW, hpW, hWc, hform⟩ :=
    SliceStructures.immersion_coordinates S T j hj.1 p (hj.2.2.1 p) hpTi
  obtain ⟨A, hA, hpA, G, hG, heG⟩ := (hf p).2 c hc hpc
  obtain ⟨B, hB, hpB, H, hH, heH⟩ :=
    (hd (euclideanChart N) hT (j p) hpd (mem_univ _)).2
  have heH' : H =ᶠ[𝓝 (j p)] (fun x => (d x).val) := by exact heH
  let P : Euclidean N → Euclidean n := sliceProjection hnN
  let F : Euclidean N → V := G ∘ P ∘ H
  have hPH : ContDiffOn ℝ (⊤ : ℕ∞) (P ∘ H) B :=
    (SliceStructures.contDiff_sliceProjection hnN).comp_contDiffOn hH
  let O := B ∩ (P ∘ H) ⁻¹' A
  have hO : IsOpen O := hPH.continuousOn.isOpen_inter_preimage hB hA
  have hpO : j p ∈ O := by
    refine ⟨hpB, ?_⟩
    change P (H (j p)) ∈ A
    rw [heH'.eq_of_nhds, (hform p hpW).2]
    simpa [P, SliceStructures.sliceProjection_embedding hnN] using hpA
  have hF : ContDiffOn ℝ (⊤ : ℕ∞) F O :=
    hG.comp (hPH.mono inter_subset_left) (fun _ hx => hx.2)
  have heF : (fun q => F (j q)) =ᶠ[𝓝 p] f := by
    have heHj := (hj.1 p).1.tendsto.eventually heH'
    filter_upwards [heHj, hW.mem_nhds hpW, heG] with q hqH hqW hqG
    change G (P (H (j q))) = f q
    rw [hqH, (hform q hqW).2]
    simpa [P, SliceStructures.sliceProjection_embedding hnN] using hqG
  obtain ⟨W', hW'sub, hW', hpW'⟩ := mem_nhds_iff.mp heF
  have hje : Topology.IsEmbedding j :=
    SliceStructures.isEmbedding_of_range_homeomorph hj.2.2.2
  obtain ⟨A', hA', hpre, _⟩ := SliceStructures.embedding_open_cut hje hW'
  refine ⟨O ∩ A', hO.inter hA', ⟨hpO, ?_⟩, F, hF.mono inter_subset_left, ?_⟩
  · change p ∈ j ⁻¹' A'
    rw [hpre]
    exact hpW'
  · intro q hq
    apply hW'sub
    rw [← hpre]
    exact hq.2
end SmoothManifolds.ClassicalBoundaryResults

namespace SmoothManifolds.ClassicalBoundaryResults
open ModelData AtlasData MapData TangentData DifferentialData EmbeddedData
  MapClassData RegularDomainData BoundaryData BoundaryConeData
  BoundaryOrientationData ClassicalBoundaryData OrientationData Set Module
open FrameData Filter
open scoped Topology

/-- The natural boundary inclusion followed by a genuine embedding is again
an embedding, with its actual intrinsic differential. -/
theorem natural_boundary_embedding {n N : ℕ} {a : ModelKind} {M : Type}
    [TopologicalSpace M] (S : SmoothManifold (n+1) a M)
    (T : SmoothManifold N .euclidean (Euclidean N)) (j : M → Euclidean N)
    (hj : IsSmoothEmbedding S T j)
    (B : SmoothManifold n .euclidean (intrinsicBoundary S)) (hB : IsNaturalBoundary S B) :
    IsSmoothEmbedding B T (fun q : intrinsicBoundary S => j q.val) := by
  let g : intrinsicBoundary S → Euclidean N := fun q => j q.val
  have hg : IsSmoothMap B T g :=
    manifoldContDiff_comp ⊤ B.smoothStructure.val S.smoothStructure.val
      T.smoothStructure.val S.smoothStructure.property.1.1 Subtype.val j hB.1 hj.1
  have hje : Topology.IsEmbedding j :=
    SliceStructures.isEmbedding_of_range_homeomorph hj.2.2.2
  have hge : Topology.IsEmbedding g := hje.comp Topology.IsEmbedding.subtypeVal
  refine ⟨hg, hge.injective, ?_, hge.toHomeomorph, fun _ => rfl⟩
  intro p
  obtain ⟨L, hL, _⟩ := differential_exists B S Subtype.val hB.1 p
  obtain ⟨Q, hQ, _⟩ := differential_exists S T j hj.1 p.val
  have hcomp : IsDifferential B T g p (Q.comp L) :=
    differential_comp B S T Subtype.val j hB.1 hj.1 p L Q hL hQ
  apply (MapClasses.smooth_tangent_invariants B T g hg p (Q.comp L) hcomp).2.1.mpr
  have hQinj := (MapClasses.smooth_tangent_invariants S T j hj.1 p.val Q hQ).2.1.mp
    (hj.2.2.1 p.val)
  apply hQinj.comp
  cases a with
  | euclidean =>
    have hpfalse := p.property
    simp only [intrinsicBoundary_euclidean S, Set.mem_empty_iff_false] at hpfalse
  | halfSpace =>
    obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p.val
    exact (boundary_inclusion_image S B hB p c hc hp L hL
      (coordinateDerivationEquiv S p.val c hc hp)
      (coordinateDerivationEquiv_isChartCoordinates S p.val c hc hp)).1
end SmoothManifolds.ClassicalBoundaryResults

open scoped Manifold ContDiff
open Set Filter Function
namespace CompactSmoothExtension

theorem smooth_extension_of_local
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (K : Set E) (hK : IsCompact K) (f : K → V)
    (hloc : ∀ p : K, ∃ U : Set E, IsOpen U ∧ p.val ∈ U ∧
      ∃ F : E → V, ContDiffOn ℝ (⊤ : ℕ∞) F U ∧
        ∀ q : K, q.val ∈ U → F q.val = f q) :
    ∃ F : E → V, ContDiff ℝ (⊤ : ℕ∞) F ∧ ∀ q : K, F q.val = f q := by
  classical
  choose U hU hpU F hF heq using hloc
  have hcover : K ⊆ ⋃ p : K, U p := by
    intro x hx
    exact mem_iUnion_of_mem (⟨x, hx⟩ : K) (hpU ⟨x, hx⟩)
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (𝓘(ℝ, E)) hK.isClosed U hU hcover
  refine ⟨fun x => ∑ᶠ p : K, ρ p x • F p x, ?_, ?_⟩
  · rw [← contMDiff_iff_contDiff]
    apply ρ.contMDiff_finsum_smul
    intro p x hx
    rw [contMDiffAt_iff_contDiffAt]
    exact (hF p).contDiffAt ((hU p).mem_nhds (hρ p hx))
  · intro q
    calc
      (∑ᶠ p : K, ρ p q.val • F p q.val) = ∑ᶠ p : K, ρ p q.val • f q := by
        apply finsum_congr
        intro p
        by_cases hzero : ρ p q.val = 0
        · simp only [hzero, zero_smul]
        · rw [heq p q (hρ p (subset_tsupport _ hzero))]
      _ = (∑ᶠ p : K, ρ p q.val) • f q := by
        rw [finsum_smul]
      _ = f q := by rw [ρ.sum_eq_one q.property, one_smul]

/-- Compact data admit a globally smooth compactly supported ambient extension. -/
theorem compactly_supported_smooth_extension_of_local
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (K : Set E) (hK : IsCompact K) (f : K → V)
    (hloc : ∀ p : K, ∃ U : Set E, IsOpen U ∧ p.val ∈ U ∧
      ∃ F : E → V, ContDiffOn ℝ (⊤ : ℕ∞) F U ∧
        ∀ q : K, q.val ∈ U → F q.val = f q) :
    ∃ F : E → V, ContDiff ℝ (⊤ : ℕ∞) F ∧ HasCompactSupport F ∧
      ∀ q : K, F q.val = f q := by
  obtain ⟨F, hF, heq⟩ := smooth_extension_of_local K hK f hloc
  obtain ⟨r, hr⟩ := hK.isBounded.subset_ball (0 : E)
  obtain ⟨χ, hχ, _, hsupp, hχone⟩ := exists_contDiff_support_eq_eq_one_iff
    (n := (⊤ : ℕ∞)) Metric.isOpen_ball hK.isClosed hr
  have hχcompact : HasCompactSupport χ := by
    apply Metric.isCompact_of_isClosed_isBounded isClosed_closure
    rw [hsupp]
    exact Metric.isBounded_ball.closure
  refine ⟨fun x => χ x • F x, hχ.smul hF, hχcompact.smul_right, ?_⟩
  intro q
  change χ q.val • F q.val = f q
  rw [(hχone q.val).mp q.property, one_smul, heq]

end CompactSmoothExtension
namespace SmoothManifolds.ClassicalBoundaryResults
open ModelData AtlasData MapData TangentData DifferentialData EmbeddedData
  MapClassData RegularDomainData BoundaryData BoundaryConeData
  BoundaryOrientationData ClassicalBoundaryData OrientationData Set Module
open FrameData Filter ExteriorData
open scoped Topology

/-- Smooth vector-valued data on a compact embedded image admit a compactly
supported smooth ambient extension. -/
theorem embedded_vector_compact_extension {n N : ℕ} {a : ModelKind} {M V : Type}
    [TopologicalSpace M] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (S : SmoothManifold n a M)
    (T : SmoothManifold N .euclidean (Euclidean N))
    (hT : euclideanChart N ∈ T.smoothStructure.val)
    (j : M → Euclidean N) (hj : IsSmoothEmbedding S T j)
    (hcompact : IsCompact (range j))
    (f : M → V) (hf : VectorSmooth S.smoothStructure.val f) :
    ∃ F : Euclidean N → V, ContDiff ℝ (⊤ : ℕ∞) F ∧ HasCompactSupport F ∧
      ∀ p, F (j p) = f p := by
  classical
  let he := SliceStructures.isEmbedding_of_range_homeomorph hj.2.2.2
  let e := he.toHomeomorph
  let g : range j → V := fun q => f (e.symm q)
  have heval (q : range j) : j (e.symm q) = q.val := by
    have hh := congrArg Subtype.val (e.apply_symm_apply q)
    exact hh
  have hloc (q : range j) : ∃ U : Set (Euclidean N), IsOpen U ∧ q.val ∈ U ∧
      ∃ H : Euclidean N → V, ContDiffOn ℝ (⊤ : ℕ∞) H U ∧
        ∀ r : range j, r.val ∈ U → H r.val = g r := by
    obtain ⟨U, hU, hpU, H, hH, hHeq⟩ :=
      embedded_vector_local_extension S T hT j hj f hf (e.symm q)
    refine ⟨U, hU, (heval q) ▸ hpU, H, hH, ?_⟩
    intro r hr
    change H r.val = f (e.symm r)
    rw [← heval r]
    exact hHeq _ ((heval r).symm ▸ hr)
  obtain ⟨F, hF, hFsupport, hFeq⟩ :=
    CompactSmoothExtension.compactly_supported_smooth_extension_of_local
      (range j) hcompact g hloc
  refine ⟨F, hF, hFsupport, ?_⟩
  intro p
  have h := hFeq (e p)
  simpa [g, e, he] using h
end SmoothManifolds.ClassicalBoundaryResults


set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace SmoothManifolds.ClassicalBoundaryResults
open ModelData AtlasData MapData TangentData DifferentialData EmbeddedData
  MapClassData RegularDomainData BoundaryData BoundaryConeData
  BoundaryOrientationData ClassicalBoundaryData OrientationData Set Module
open FrameData Filter ExteriorData
open scoped Topology

lemma rotateLeft_dot_self (v : Euclidean 2) :
    dotProduct (rotateLeft v) (rotateLeft v) = dotProduct v v := by
  simp [rotateLeft, dotProduct, Fin.sum_univ_two]
  ring

lemma dot_rotateLeft (v : Euclidean 2) : dotProduct v (rotateLeft v) = 0 := by
  simp [rotateLeft, dotProduct, Fin.sum_univ_two]
  ring

lemma det_rotateLeft (v : Euclidean 2) :
    (Matrix.of ![v, rotateLeft v]).det = dotProduct v v := by
  simp [rotateLeft, Matrix.det_fin_two, dotProduct, Fin.sum_univ_two]

lemma contDiff_rotateLeft : ContDiff ℝ (⊤ : ℕ∞) rotateLeft := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · simpa [rotateLeft] using (contDiff_apply ℝ (fun _ : Fin 2 => ℝ) 1).neg
  · simpa [rotateLeft] using (contDiff_apply ℝ (fun _ : Fin 2 => ℝ) 0)

/-- A genuine smooth unit tangent, everywhere positive for the actual intrinsic
boundary orientation, exists along every planar regular domain. -/
theorem planar_boundary_unit_tangent {a : ModelKind}
    (T : SmoothManifold 2 .euclidean (Euclidean 2))
    (hT : euclideanChart 2 ∈ T.smoothStructure.val)
    (D : Set (Euclidean 2)) (S : SmoothManifold 2 a D)
    (hD : IsRegularDomain T D S) :
    ∃ (B : SmoothManifold 1 .euclidean (intrinsicBoundary S))
      (J : (p : D) → TangentSpace S p ≃ₗ[ℝ] Euclidean 2)
      (K : (p : intrinsicBoundary S) → TangentSpace B p →ₗ[ℝ] TangentSpace S p.val)
      (o : Orientation S) (b : Orientation B)
      (ν τ : intrinsicBoundary S → Euclidean 2)
      (w : (p : intrinsicBoundary S) → TangentSpace B p),
      IsNaturalBoundary S B ∧
      (∀ p, IsEuclideanDifferential S T Subtype.val p (J p).toLinearMap) ∧
      (∀ p (η : DeterminantLine S p), IsPositive (o.val p) η ↔
        0 < standardAmbientDet 2 (exteriorPower.map 2 (J p).toLinearMap η)) ∧
      IsInducedOrientation o b ∧
      VectorSmooth B.smoothStructure.val ν ∧ VectorSmooth B.smoothStructure.val τ ∧
      ∀ p, IsDifferential B S Subtype.val p (K p) ∧
        dotProduct (ν p) (ν p) = 1 ∧ IsOutward S p ((J p.val).symm (ν p)) ∧
        τ p = rotateLeft (ν p) ∧ dotProduct (τ p) (τ p) = 1 ∧
        J p.val (K p (w p)) = τ p ∧
        IsPositive (b.val p) (exteriorPower.ιMulti ℝ 1 ![w p]) := by
  obtain ⟨B, J, K, ν, hB, hJ, hνsmooth, hnormal⟩ :=
    regular_domain_normals T hT D S hD
  obtain ⟨o, ho⟩ :=
    euclidean_orientation_of_differential S T Subtype.val hT hD.2.1 J hJ
  obtain ⟨b, ⟨hb, _⟩, _⟩ := (BoundaryOrientations.boundary_orientation S o).2 B hB
  have hpre (p : intrinsicBoundary S) :
      ∃ w : TangentSpace B p, J p.val (K p w) = rotateLeft (ν p) := by
    have hrange : rotateLeft (ν p) ∈ LinearMap.range ((J p.val).toLinearMap.comp (K p)) := by
      rw [(hnormal p).2.2.2]
      exact dot_rotateLeft (ν p)
    exact hrange
  choose w hw using hpre
  refine ⟨B, J, K, o, b, ν, fun p => rotateLeft (ν p), w,
    hB, hJ, ho, hb, hνsmooth, fun p => (hνsmooth p).postcomp contDiff_rotateLeft, ?_⟩
  intro p
  refine ⟨(hnormal p).1, (hnormal p).2.1, (hnormal p).2.2.1,
    rfl, (rotateLeft_dot_self (ν p)).trans (hnormal p).2.1, hw p, ?_⟩
  rw [planar_boundary_positive_iff_det S B o b hb p (J p.val) (K p)
    (hnormal p).1 (ν p) (hnormal p).2.2.1 (ho p.val), hw p,
    det_rotateLeft, (hnormal p).2.1]
  norm_num
end SmoothManifolds.ClassicalBoundaryResults
namespace SmoothManifolds.ClassicalBoundaryResults
open ModelData AtlasData MapData TangentData DifferentialData EmbeddedData
  MapClassData RegularDomainData BoundaryData BoundaryConeData
  BoundaryOrientationData ClassicalBoundaryData OrientationData Set Module
open FrameData Filter ExteriorData
open scoped Topology

/-- A compact smooth planar domain admits a globally smooth, compactly supported
ambient vector field whose restriction to its actual boundary is the positive
Euclidean unit tangent. -/
theorem planar_boundary_ambient_tangent {a : ModelKind}
    (T : SmoothManifold 2 .euclidean (Euclidean 2))
    (hT : euclideanChart 2 ∈ T.smoothStructure.val)
    (D : Set (Euclidean 2)) (S : SmoothManifold 2 a D)
    (hD : IsRegularDomain T D S) (hcompact : IsCompact D) :
    ∃ (B : SmoothManifold 1 .euclidean (intrinsicBoundary S))
      (J : (p : D) → TangentSpace S p ≃ₗ[ℝ] Euclidean 2)
      (K : (p : intrinsicBoundary S) → TangentSpace B p →ₗ[ℝ] TangentSpace S p.val)
      (o : Orientation S) (b : Orientation B)
      (ν : intrinsicBoundary S → Euclidean 2)
      (F : Euclidean 2 → Euclidean 2)
      (w : (p : intrinsicBoundary S) → TangentSpace B p),
      IsNaturalBoundary S B ∧
      (∀ p, IsEuclideanDifferential S T Subtype.val p (J p).toLinearMap) ∧
      (∀ p (η : DeterminantLine S p), IsPositive (o.val p) η ↔
        0 < standardAmbientDet 2 (exteriorPower.map 2 (J p).toLinearMap η)) ∧
      IsInducedOrientation o b ∧
      VectorSmooth B.smoothStructure.val ν ∧
      ContDiff ℝ (⊤ : ℕ∞) F ∧ HasCompactSupport F ∧
      ∀ p, IsDifferential B S Subtype.val p (K p) ∧
        dotProduct (ν p) (ν p) = 1 ∧ IsOutward S p ((J p.val).symm (ν p)) ∧
        F p.val.val = rotateLeft (ν p) ∧
        dotProduct (F p.val.val) (F p.val.val) = 1 ∧
        J p.val (K p (w p)) = F p.val.val ∧
        IsPositive (b.val p) (exteriorPower.ιMulti ℝ 1 ![w p]) := by
  obtain ⟨B, J, K, o, b, ν, τ, w, hB, hJ, ho, hb, hν, hτ, hw⟩ :=
    planar_boundary_unit_tangent T hT D S hD
  letI : CompactSpace D := isCompact_iff_compactSpace.mp hcompact
  letI : CompactSpace (intrinsicBoundary S) :=
    isCompact_iff_compactSpace.mp (isClosed_intrinsicBoundary S).isCompact
  have hj : IsSmoothEmbedding B T (fun p : intrinsicBoundary S => p.val.val) :=
    natural_boundary_embedding S T Subtype.val hD.2 B hB
  have hjcompact : IsCompact (range (fun p : intrinsicBoundary S => p.val.val)) :=
    isCompact_range (continuous_subtype_val.comp continuous_subtype_val)
  obtain ⟨F, hF, hsupport, hFeq⟩ :=
    embedded_vector_compact_extension B T hT _ hj hjcompact τ hτ
  refine ⟨B, J, K, o, b, ν, F, w, hB, hJ, ho, hb, hν, hF, hsupport, ?_⟩
  intro p
  obtain ⟨hK, hunit, hout, hrot, hτunit, hτw, hpos⟩ := hw p
  exact ⟨hK, hunit, hout, (hFeq p).trans hrot,
    (by rw [hFeq]; exact hτunit), hτw.trans (hFeq p).symm, hpos⟩
end SmoothManifolds.ClassicalBoundaryResults



set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace SmoothManifolds.ClassicalBoundaryResults
open ModelData AtlasData MapData TangentData DifferentialData EmbeddedData
  MapClassData RegularDomainData BoundaryData BoundaryConeData
  BoundaryOrientationData ClassicalBoundaryData OrientationData Set Module
open FrameData Filter ExteriorData
open scoped Topology

/-- Each component of the actual compact boundary is separated by an ambient
open neighborhood from all other boundary components. -/
theorem compact_boundary_component_isolation {n : ℕ} {a : ModelKind}
    (T : SmoothManifold (n+1) .euclidean (Euclidean (n+1)))
    (D : Set (Euclidean (n+1))) (S : SmoothManifold (n+1) a D)
    (hD : IsRegularDomain T D S) (hcompact : IsCompact D)
    (B : SmoothManifold n .euclidean (intrinsicBoundary S))
    (p : intrinsicBoundary S) :
    let C := (fun q : intrinsicBoundary S => q.val.val) '' connectedComponent p
    C.Nonempty ∧ IsCompact C ∧ IsPathConnected C ∧ C ⊆ frontier D ∧
      IsCompact (frontier D \ C) ∧
      ∃ U : Set (Euclidean (n+1)), IsOpen U ∧ C ⊆ U ∧
        ∀ x ∈ U, x ∈ C ↔ x ∈ frontier D := by
  letI : CompactSpace D := isCompact_iff_compactSpace.mp hcompact
  letI : CompactSpace (intrinsicBoundary S) :=
    isCompact_iff_compactSpace.mp (isClosed_intrinsicBoundary S).isCompact
  let jb := fun q : intrinsicBoundary S => q.val.val
  have hjb : Continuous jb := continuous_subtype_val.comp continuous_subtype_val
  have hjbinj : Function.Injective jb := Subtype.val_injective.comp Subtype.val_injective
  have hrange : range jb = frontier D := by
    have hh := (RegularDomains.regular_domain_inclusion_topology RegularDomains.regular_domain_topology
      T D S (intrinsicBoundary_euclidean T) hD).2
    rw [← hh]
    ext x
    exact ⟨fun ⟨q, hq⟩ => ⟨q.val, q.property, hq⟩,
      fun ⟨q, hq, heq⟩ => ⟨⟨q, hq⟩, heq⟩⟩
  obtain ⟨_, _, hcomponents⟩ := compact_manifold_components B
  obtain ⟨hopen, hc, hpc⟩ := hcomponents p
  let C := jb '' connectedComponent p
  have hCsub : C ⊆ frontier D := by
    intro x hx
    rw [← hrange]
    exact image_subset_range jb _ hx
  have hother : frontier D \ C = jb '' (connectedComponent p)ᶜ := by
    rw [← hrange]
    ext x
    constructor
    · rintro ⟨⟨q, rfl⟩, hq⟩
      exact ⟨q, fun h => hq ⟨q, h, rfl⟩, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      refine ⟨⟨q, rfl⟩, ?_⟩
      rintro ⟨r, hr, heq⟩
      exact hq ((hjbinj heq) ▸ hr)
  have hothercompact : IsCompact (frontier D \ C) := by
    rw [hother]
    exact hopen.isClosed_compl.isCompact.image hjb
  refine ⟨⟨jb p, p, mem_connectedComponent, rfl⟩,
    hc.image hjb, hpc.image hjb, hCsub, hothercompact,
    (frontier D \ C)ᶜ, hothercompact.isClosed.isOpen_compl, ?_, ?_⟩
  · intro x hx hxother
    exact hxother.2 hx
  · intro x hx
    exact ⟨fun h => hCsub h, fun hfront => Classical.byContradiction (fun hnot => hx ⟨hfront, hnot⟩)⟩
end SmoothManifolds.ClassicalBoundaryResults



set_option autoImplicit false
noncomputable section
open Set Filter Function
open scoped Topology
namespace SmoothManifolds.FrontierConstraints
open ModelData AtlasData MapData TangentData DifferentialData EmbeddedData
  MapClassData RegularDomainData BoundaryData BoundaryOrientationData
  ClassicalBoundaryData ClassicalBoundaryResults

/-- The zero set of a regular one-sided local defining function is the actual frontier. -/
theorem frontier_iff_zero_of_local_defining
    {m : ℕ}
    {D U : Set (Euclidean m)} (hD : IsClosed D) (hU : IsOpen U)
    {f : Euclidean m → ℝ} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U)
    (hside : ∀ q ∈ U, q ∈ D ↔ 0 ≤ f q)
    (hreg : ∀ q ∈ U, fderiv ℝ f q ≠ 0) :
    ∀ q ∈ U, q ∈ frontier D ↔ f q = 0 := by
  intro q hqU
  have hfd : HasFDerivAt f (fderiv ℝ f q) q :=
    ((hf.contDiffAt (hU.mem_nhds hqU)).differentiableAt (by simp)).hasFDerivAt
  constructor
  · intro hq
    have hqD : q ∈ D := by simpa only [hD.closure_eq] using hq.1
    have hnonneg := (hside q hqU).mp hqD
    by_contra hz
    have hpos : 0 < f q := lt_of_le_of_ne hnonneg (Ne.symm hz)
    have hi : q ∈ interior D := by
      apply mem_interior_iff_mem_nhds.mpr
      have hp : {x | 0 < f x} ∈ 𝓝 q :=
        (hf.continuousOn.continuousAt (hU.mem_nhds hqU)).preimage_mem_nhds
          (Ioi_mem_nhds hpos)
      exact mem_of_superset (inter_mem (hU.mem_nhds hqU) hp)
        (fun x hx => (hside x hx.1).mpr hx.2.le)
    exact hq.2 hi
  · intro hz
    have hL := hreg q hqU
    obtain ⟨v, hv⟩ : ∃ v : Euclidean m, (fderiv ℝ f q) v ≠ 0 := by
      by_contra! h
      apply hL
      ext v
      simpa using h v
    let w : Euclidean m := (-((fderiv ℝ f q) v)⁻¹) • v
    have hw : (fderiv ℝ f q) w < 0 := by
      simp only [w, map_smul, smul_eq_mul, neg_mul, inv_mul_cancel₀ hv]
      exact neg_one_lt_zero
    have hout := (local_defining_function_ray_sides hU hqU hf.continuousOn
      hfd hz hside (v := w)).2 hw
    refine ⟨subset_closure ((hside q hqU).mpr (by rw [hz])), ?_⟩
    intro hqi
    have hray : Tendsto (fun t : ℝ => q + t • w) (𝓝[>] 0) (𝓝 q) := by
      have hcont : ContinuousAt (fun t : ℝ => q + t • w) 0 := by fun_prop
      simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
    have hin := hray (isOpen_interior.mem_nhds hqi)
    have hfalse : ∀ᶠ t in 𝓝[>] (0 : ℝ), False := by
      filter_upwards [hout, hin] with t ht ht'
      exact ht (interior_subset ht')
    obtain ⟨t, ht⟩ := hfalse.exists
    exact ht

/-- A locally vanishing ambient scalar function annihilates the genuine
ambient differential of every tangent vector. -/
theorem euclidean_differential_annihilates_of_eventually_zero
    {n N : ℕ} {a : ModelKind} {M : Type} [TopologicalSpace M]
    (S : SmoothManifold n a M)
    (T : SmoothManifold N .euclidean (Euclidean N)) (j : M → Euclidean N)
    (hT : euclideanChart N ∈ T.smoothStructure.val) (hj : IsSmoothMap S T j)
    (p : M) (J : TangentSpace S p →ₗ[ℝ] Euclidean N)
    (hJ : IsEuclideanDifferential S T j p J)
    (f : Euclidean N → ℝ) (L : Euclidean N →L[ℝ] ℝ)
    (hf : HasFDerivAt f L (j p))
    (hz : (fun q => f (j q)) =ᶠ[𝓝 p] (fun _ => 0)) :
    ∀ v, L (J v) = 0 := by
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
  let E := coordinateDerivationEquiv S p c hc hp
  have hE := coordinateDerivationEquiv_isChartCoordinates S p c hc hp
  obtain ⟨U, hU, hpU, H, hH, heH⟩ :=
    (hj p).2 c hc (euclideanChart N) hT hp (mem_univ _)
  have hbase : H (c p).val = j p := by simpa using heH.eq_of_nhds
  have hHd : HasFDerivAt H (fderiv ℝ H (c p).val) (c p).val :=
    ((hH.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp)).hasFDerivAt
  have hfd : HasFDerivAt (f ∘ H) (L.comp (fderiv ℝ H (c p).val)) (c p).val := by
    apply HasFDerivAt.comp
    · simpa only [hbase] using hf
    · exact hHd
  let A : Euclidean n →L[ℝ] Euclidean 1 :=
    ContinuousLinearMap.pi (fun _ : Fin 1 => L.comp (fderiv ℝ H (c p).val))
  have hA : HasFDerivAt (fun z => fun _ : Fin 1 => f (H z)) A (c p).val :=
    hasFDerivAt_pi.mpr (fun _ => hfd)
  have heq : (fun q => (fun _ : Fin 1 => f (H (c q).val))) =ᶠ[𝓝 p]
      (fun _ => (0 : Euclidean 1)) := by
    filter_upwards [heH, hz] with q hq hqz
    funext i
    change f (H (c q).val) = 0
    change H (c q).val = j q at hq
    rw [hq]
    exact hqz
  have hAzero : A = 0 :=
    FiniteRegularity.extension_independence c (fun _ => (0 : Euclidean 1)) p hp A 0
      ⟨_, hA, heq⟩ ⟨_, hasFDerivAt_const _ _, Filter.EventuallyEq.rfl⟩
  intro v
  obtain ⟨D, G, hD, hG, hJG⟩ := hJ
  have hJac := differential_jacobian S T j hj p D hD c (euclideanChart N)
    hc hT hp (mem_univ _) E G hE hG U H hU hpU hH heH v
  have hh := congrArg (fun B : Euclidean n →L[ℝ] Euclidean 1 => B (E v) 0) hAzero
  change L (fderiv ℝ H (c p).val (E v)) = 0 at hh
  rw [← hJac] at hh
  rw [hJG]
  exact hh

/-- Genuine regular domains have regular scalar equations for their actual
ambient frontier in a neighborhood of every actual boundary point. -/
theorem regular_domain_frontier_local_equation {n : ℕ}
    (T : SmoothManifold (n+1) .euclidean (Euclidean (n+1)))
    (hT : euclideanChart (n+1) ∈ T.smoothStructure.val)
    (D : Set (Euclidean (n+1))) (S : SmoothManifold (n+1) .halfSpace D)
    (hD : IsRegularDomain T D S) (p : intrinsicBoundary S)
    (J : TangentSpace S p.val ≃ₗ[ℝ] Euclidean (n+1))
    (hJ : IsEuclideanDifferential S T Subtype.val p.val J.toLinearMap) :
    ∃ (U : Set (Euclidean (n+1))) (f : Euclidean (n+1) → ℝ),
      IsOpen U ∧ p.val.val ∈ U ∧ ContDiffOn ℝ (⊤ : ℕ∞) f U ∧
      (∀ q ∈ U, q ∈ frontier D ↔ f q = 0) ∧
      (∀ q ∈ U, fderiv ℝ f q ≠ 0) := by
  obtain ⟨U, f, L, hU, hpU, hf, hfd, hz, hside, hsign⟩ :=
    regular_domain_local_defining_function T hT D S hD p J hJ
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p.val
  let E := coordinateDerivationEquiv S p.val c hc hp
  have hE := coordinateDerivationEquiv_isChartCoordinates S p.val c hc hp
  let u := E.symm (-Pi.single (Fin.last n) 1)
  have hu : IsOutward S p u := by
    apply (BoundaryOrientations.outward_iff_coordinate S p c hc hp E hE u).mpr
    simp [u]
  have hneg : L (J u) < 0 := (hsign (J u)).mp (by simpa using hu)
  have hL : L ≠ 0 := by
    intro h
    have he : L (J u) = 0 := by rw [h]; rfl
    linarith
  have hregp : fderiv ℝ f p.val.val ≠ 0 := by rwa [hfd.fderiv]
  let W : Set (Euclidean (n+1)) := U ∩ (fderiv ℝ f) ⁻¹' {A | A ≠ 0}
  have hW : IsOpen W :=
    (hf.continuousOn_fderiv_of_isOpen hU (by simp)).isOpen_inter_preimage hU
      (isOpen_ne_fun continuous_id continuous_const)
  have hpW : p.val.val ∈ W := ⟨hpU, hregp⟩
  have hfW : ContDiffOn ℝ (⊤ : ℕ∞) f W := hf.mono inter_subset_left
  have hreg : ∀ q ∈ W, fderiv ℝ f q ≠ 0 := fun _ hq => hq.2
  exact ⟨W, f, hW, hpW, hfW,
    frontier_iff_zero_of_local_defining hD.1 hW hfW
      (fun q hq => hside q hq.1) hreg, hreg⟩

/-- A vector in the actual differential image of the actual boundary is
annihilated by every local regular equation of the actual frontier. -/
theorem boundary_tangent_annihilates_frontier_equation {n : ℕ}
    (T : SmoothManifold (n+1) .euclidean (Euclidean (n+1)))
    (hT : euclideanChart (n+1) ∈ T.smoothStructure.val)
    (D : Set (Euclidean (n+1))) (S : SmoothManifold (n+1) .halfSpace D)
    (hD : IsRegularDomain T D S)
    (B : SmoothManifold n .euclidean (intrinsicBoundary S)) (hB : IsNaturalBoundary S B)
    (J : (p : D) → TangentSpace S p ≃ₗ[ℝ] Euclidean (n+1))
    (hJ : ∀ p, IsEuclideanDifferential S T Subtype.val p (J p).toLinearMap)
    (K : (p : intrinsicBoundary S) → TangentSpace B p →ₗ[ℝ] TangentSpace S p.val)
    (hK : ∀ p, IsDifferential B S Subtype.val p (K p))
    {U : Set (Euclidean (n+1))} (hU : IsOpen U)
    (f : Euclidean (n+1) → ℝ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U)
    (heq : ∀ q ∈ U, q ∈ frontier D ↔ f q = 0)
    (p : intrinsicBoundary S) (hp : p.val.val ∈ U) (v : TangentSpace B p) :
    (fderiv ℝ f p.val.val) (J p.val (K p v)) = 0 := by
  let j : intrinsicBoundary S → Euclidean (n+1) := fun q => q.val.val
  have hj : IsSmoothMap B T j :=
    manifoldContDiff_comp _ _ _ _ S.smoothStructure.property.1.1 _ _ hB.1 hD.2.1
  have hboundary : Subtype.val '' intrinsicBoundary S = frontier D :=
    (RegularDomains.regular_domain_inclusion_topology RegularDomains.regular_domain_topology
      T D S (intrinsicBoundary_euclidean T) hD).2
  have hlocal : (fun q => f (j q)) =ᶠ[𝓝 p] (fun _ => 0) := by
    have hjcont : ContinuousAt j p :=
      continuous_subtype_val.continuousAt.comp continuous_subtype_val.continuousAt
    filter_upwards [hjcont.preimage_mem_nhds (hU.mem_nhds hp)] with q hq
    exact (heq (j q) hq).mp (by
      rw [← hboundary]
      exact ⟨q.val, q.property, rfl⟩)
  let H := (J p.val).toLinearMap.comp (K p)
  have hH : IsEuclideanDifferential B T j p H := by
    obtain ⟨L, G, hL, hG, hJL⟩ := hJ p.val
    refine ⟨L.comp (K p), G,
      differential_comp B S T Subtype.val Subtype.val hB.1 hD.2.1 p
        (K p) L (hK p) hL, hG, ?_⟩
    dsimp only [H]
    rw [hJL]
    rfl
  exact euclidean_differential_annihilates_of_eventually_zero B T j hT hj p H hH
    f (fderiv ℝ f p.val.val)
    ((hf.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt hlocal v

/-- An ambient field tangent to the genuine natural boundary satisfies the
regular local scalar-constraint hypotheses at every actual frontier point. -/
theorem regular_domain_tangent_field_local_constraints {n : ℕ}
    (T : SmoothManifold (n+1) .euclidean (Euclidean (n+1)))
    (hT : euclideanChart (n+1) ∈ T.smoothStructure.val)
    (D : Set (Euclidean (n+1))) (S : SmoothManifold (n+1) .halfSpace D)
    (hD : IsRegularDomain T D S)
    (B : SmoothManifold n .euclidean (intrinsicBoundary S)) (hB : IsNaturalBoundary S B)
    (J : (p : D) → TangentSpace S p ≃ₗ[ℝ] Euclidean (n+1))
    (hJ : ∀ p, IsEuclideanDifferential S T Subtype.val p (J p).toLinearMap)
    (K : (p : intrinsicBoundary S) → TangentSpace B p →ₗ[ℝ] TangentSpace S p.val)
    (hK : ∀ p, IsDifferential B S Subtype.val p (K p))
    (F : Euclidean (n+1) → Euclidean (n+1))
    (htangent : ∀ p : intrinsicBoundary S, ∃ v : TangentSpace B p,
      J p.val (K p v) = F p.val.val) :
    ∀ x ∈ frontier D, ∃ (U : Set (Euclidean (n+1))) (f : Euclidean (n+1) → ℝ),
      IsOpen U ∧ x ∈ U ∧ ContDiffOn ℝ (⊤ : ℕ∞) f U ∧
      (∀ q ∈ U, q ∈ frontier D ↔ f q = 0) ∧
      (∀ q ∈ U, fderiv ℝ f q ≠ 0) ∧
      (∀ q ∈ U, q ∈ frontier D → (fderiv ℝ f q) (F q) = 0) := by
  have hboundary : Subtype.val '' intrinsicBoundary S = frontier D :=
    (RegularDomains.regular_domain_inclusion_topology RegularDomains.regular_domain_topology
      T D S (intrinsicBoundary_euclidean T) hD).2
  intro x hx
  obtain ⟨p, hp, rfl⟩ := (show x ∈ Subtype.val '' intrinsicBoundary S by rwa [hboundary])
  let bp : intrinsicBoundary S := ⟨p, hp⟩
  obtain ⟨U, f, hU, hpU, hf, heq, hreg⟩ :=
    regular_domain_frontier_local_equation T hT D S hD bp (J p) (hJ p)
  refine ⟨U, f, hU, hpU, hf, heq, hreg, ?_⟩
  intro q hqU hq
  obtain ⟨r, hr, rfl⟩ := (show q ∈ Subtype.val '' intrinsicBoundary S by rwa [hboundary])
  let br : intrinsicBoundary S := ⟨r, hr⟩
  obtain ⟨v, hv⟩ := htangent br
  rw [← hv]
  exact boundary_tangent_annihilates_frontier_equation T hT D S hD B hB J hJ K hK
    hU f hf heq br hqU v

end SmoothManifolds.FrontierConstraints



set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace SmoothManifolds.ClassicalBoundaryResults
open ModelData AtlasData MapData TangentData DifferentialData EmbeddedData
  MapClassData RegularDomainData BoundaryData BoundaryConeData
  BoundaryOrientationData ClassicalBoundaryData OrientationData Set Module
open FrameData Filter ExteriorData
open scoped Topology

/-- Any defining covector with the actual outward halfspace kills every actual
boundary inclusion tangent. -/
theorem defining_covector_annihilates_boundary
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    (S : SmoothManifold (n+1) .halfSpace M)
    (B : SmoothManifold n .euclidean (intrinsicBoundary S)) (hB : IsNaturalBoundary S B)
    (p : intrinsicBoundary S)
    (J : TangentSpace S p.val ≃ₗ[ℝ] Euclidean (n+1))
    (K : TangentSpace B p →ₗ[ℝ] TangentSpace S p.val)
    (hK : IsDifferential B S Subtype.val p K)
    (L : Euclidean (n+1) →L[ℝ] ℝ)
    (hsign : ∀ v, IsOutward S p (J.symm v) ↔ L v < 0)
    (ν : Euclidean (n+1)) (hout : IsOutward S p (J.symm ν))
    (w : TangentSpace B p) : L (J (K w)) = 0 := by
  have hshift (c : ℝ) : L ν + c * L (J (K w)) < 0 := by
    have hh := outward_add_boundary S B hB p K hK (J.symm ν) hout 1 zero_lt_one (c • w)
    have hh' : IsOutward S p (J.symm (ν + c • J (K w))) := by
      simpa only [one_smul, map_add, map_smul, LinearEquiv.symm_apply_apply] using hh
    simpa only [map_add, map_smul, smul_eq_mul] using (hsign _).mp hh'
  by_contra hne
  have hh := hshift (-L ν / L (J (K w)))
  rw [div_mul_cancel₀ _ hne] at hh
  linarith

/-- The planar oriented-basis identity, expressed in the source's actual ambient plane. -/
theorem planar_determinant_basis_identity (ν τ v : Euclidean 2) :
    (Matrix.of ![ν, τ]).det • v =
      (Matrix.of ![v, τ]).det • ν + (Matrix.of ![ν, v]).det • τ := by
  ext i
  fin_cases i <;> simp [Matrix.det_fin_two, smul_eq_mul] <;> ring

/-- A left transverse ambient vector has positive inward defining derivative. -/
theorem planar_left_transverse_covector_positive
    {ν τ v : Euclidean 2} (L : Euclidean 2 →L[ℝ] ℝ)
    (hν : L ν < 0) (hτ : L τ = 0)
    (hpositive : 0 < (Matrix.of ![ν, τ]).det)
    (hleft : 0 < (Matrix.of ![τ, v]).det) : 0 < L v := by
  have heq := congrArg L (planar_determinant_basis_identity ν τ v)
  simp only [map_smul, map_add, hτ, smul_eq_mul, mul_zero, add_zero] at heq
  have hanti : (Matrix.of ![v, τ]).det = -(Matrix.of ![τ, v]).det := by
    simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    ring
  rw [hanti] at heq
  have hm : 0 < (Matrix.of ![ν, τ]).det * L v := by
    rw [heq]
    exact mul_pos_of_neg_of_neg (neg_neg_of_pos hleft) hν
  exact (mul_pos_iff_of_pos_left hpositive).mp hm

/-- Intrinsic outward-first positive boundary tangents really put any
geometrically left transverse collar ray inside the original domain; the opposite
ray lies outside. The normal, differential and defining data are genuine. -/
theorem regular_domain_positive_boundary_transverse_rays
    (T : SmoothManifold 2 .euclidean (Euclidean 2))
    (hT : euclideanChart 2 ∈ T.smoothStructure.val)
    (D : Set (Euclidean 2)) (S : SmoothManifold 2 .halfSpace D)
    (hD : IsRegularDomain T D S)
    (B : SmoothManifold 1 .euclidean (intrinsicBoundary S)) (hB : IsNaturalBoundary S B)
    (o : Orientation S) (b : Orientation B) (hb : IsInducedOrientation o b)
    (p : intrinsicBoundary S)
    (J : TangentSpace S p.val ≃ₗ[ℝ] Euclidean 2)
    (hJ : IsEuclideanDifferential S T Subtype.val p.val J.toLinearMap)
    (K : TangentSpace B p →ₗ[ℝ] TangentSpace S p.val)
    (hK : IsDifferential B S Subtype.val p K)
    (ν : Euclidean 2) (hout : IsOutward S p (J.symm ν))
    (hstandard : ∀ η : DeterminantLine S p.val,
      IsPositive (o.val p.val) η ↔
        0 < standardAmbientDet 2 (exteriorPower.map 2 J.toLinearMap η))
    (w : TangentSpace B p)
    (hpositive : IsPositive (b.val p) (exteriorPower.ιMulti ℝ 1 ![w]))
    (v : Euclidean 2) (hleft : 0 < (Matrix.of ![J (K w), v]).det) :
    (∀ᶠ t in 𝓝[>] (0 : ℝ), p.val.val + t • v ∈ interior D) ∧
    (∀ᶠ t in 𝓝[>] (0 : ℝ), p.val.val + (-t) • v ∉ D) := by
  obtain ⟨U, f, L, hU, hpU, hf, hfd, hz, hmem, hsign⟩ :=
    regular_domain_local_defining_function T hT D S hD p J hJ
  have hτL := defining_covector_annihilates_boundary S B hB p J K hK L hsign ν hout w
  have hdet := (planar_boundary_positive_iff_det S B o b hb p J K hK ν hout hstandard w).mp hpositive
  have hvL := planar_left_transverse_covector_positive L ((hsign ν).mp hout) hτL hdet hleft
  refine ⟨(local_defining_function_ray_sides hU hpU hf.continuousOn hfd hz hmem).1 hvL, ?_⟩
  have hneg : L (-v) < 0 := by simpa only [map_neg, neg_lt_zero] using hvL
  have hside := (local_defining_function_ray_sides (v := -v) hU hpU hf.continuousOn hfd hz hmem).2 hneg
  simpa only [smul_neg, neg_smul] using hside

end SmoothManifolds.ClassicalBoundaryResults






set_option autoImplicit false
noncomputable section
namespace SmoothManifolds.ClassicalBoundaryResults
open ModelData AtlasData MapData TangentData DifferentialData EmbeddedData
  MapClassData RegularDomainData BoundaryData BoundaryOrientationData
  ClassicalBoundaryData FrontierConstraints Set Module
open scoped Topology

theorem scalar_linear_surjective_of_ne_zero {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℝ) (hL : L ≠ 0) : Function.Surjective L := by
  obtain ⟨v, hv⟩ : ∃ v : E, L v ≠ 0 := by
    by_contra! h
    apply hL
    ext v
    simpa using h v
  intro t
  refine ⟨(t / L v) • v, ?_⟩
  simp only [map_smul, smul_eq_mul, div_mul_cancel₀ t hv]

/-- Every actual compact boundary component, with an ambient field tangent to
that actual boundary, has local regular scalar constraint equations and satisfies
all the hypotheses needed for the canonical constrained ODE argument. -/
theorem regular_domain_boundary_component_constraints {n : ℕ}
    (T : SmoothManifold (n+1) .euclidean (Euclidean (n+1)))
    (hT : euclideanChart (n+1) ∈ T.smoothStructure.val)
    (D : Set (Euclidean (n+1))) (S : SmoothManifold (n+1) .halfSpace D)
    (hD : IsRegularDomain T D S) (hcompact : IsCompact D)
    (B : SmoothManifold n .euclidean (intrinsicBoundary S)) (hB : IsNaturalBoundary S B)
    (J : (p : D) → TangentSpace S p ≃ₗ[ℝ] Euclidean (n+1))
    (hJ : ∀ p, IsEuclideanDifferential S T Subtype.val p (J p).toLinearMap)
    (K : (p : intrinsicBoundary S) → TangentSpace B p →ₗ[ℝ] TangentSpace S p.val)
    (hK : ∀ p, IsDifferential B S Subtype.val p (K p))
    (F : Euclidean (n+1) → Euclidean (n+1))
    (htangent : ∀ p : intrinsicBoundary S, ∃ v : TangentSpace B p,
      J p.val (K p v) = F p.val.val)
    (p : intrinsicBoundary S) :
    let C := (fun q : intrinsicBoundary S => q.val.val) '' connectedComponent p
    C.Nonempty ∧ IsCompact C ∧ IsPathConnected C ∧
      ∀ x ∈ C, ∃ (U : Set (Euclidean (n+1))) (f : Euclidean (n+1) → ℝ),
        IsOpen U ∧ x ∈ U ∧ ContDiffOn ℝ 1 f U ∧
        (∀ q ∈ U, q ∈ C ↔ f q = 0) ∧
        Function.Surjective (fderiv ℝ f x) ∧
        (∀ q ∈ U, q ∈ C → (fderiv ℝ f q) (F q) = 0) := by
  let C := (fun q : intrinsicBoundary S => q.val.val) '' connectedComponent p
  obtain ⟨hCne, hCc, hCp, hCfront, _, U₀, hU₀, hCU₀, hisolate⟩ :=
    compact_boundary_component_isolation T D S hD hcompact B p
  refine ⟨hCne, hCc, hCp, ?_⟩
  intro x hx
  obtain ⟨U₁, f, hU₁, hxU₁, hf, heq, hreg, htan⟩ :=
    regular_domain_tangent_field_local_constraints T hT D S hD B hB J hJ K hK F htangent
      x (hCfront hx)
  refine ⟨U₀ ∩ U₁, f, hU₀.inter hU₁, ⟨hCU₀ hx, hxU₁⟩,
    (hf.mono inter_subset_right).of_le (by simp), ?_,
    scalar_linear_surjective_of_ne_zero _ (hreg x hxU₁), ?_⟩
  · intro q hq
    exact (hisolate q hq.1).trans (heq q hq.2)
  · intro q hq hqC
    exact htan q hq.2 (hCfront hqC)

end SmoothManifolds.ClassicalBoundaryResults



set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace LocalConstraintInvariant
open D13Unified D13Unified.Ch06.StateDerivative
open Specs.D13Unified.Ch11.Invariant
open Specs.D13Unified.Ch01.AutonomousParameters

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Closed subsets admitting local two-sided solutions through each point are
invariant under the actual canonical flow, by ambient uniqueness. -/
theorem invariant_of_local_constrained_solutions (F : AutonomousODE E)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {K : Set E}
    (hKclosed : IsClosed K) (hKD : K ⊆ F.domain)
    (hlocal : ∀ p ∈ K, ∀ s : ℝ, ∃ (J : OpenTimeInterval) (y : ℝ → E),
      IsClassicalAutonomousIVPOn F J y s p ∧ ∀ t ∈ J.carrier, y t ∈ K) :
    invariantValue F K := by
  refine ⟨hKD, ?_⟩
  intro p hp
  let I := flowInterval F p
  let x : ℝ → E := fun t => flow F t p
  have hx : IsClassicalAutonomousIVPOn F I x 0 p := flow_ivp F hF (hKD hp)
  let T : Set I.carrier := {t | x t ∈ K}
  have hTc : IsClosed T := hKclosed.preimage hx.1.1.continuousOn.domRestrict
  have hTo : IsOpen T := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    obtain ⟨J, y, hy, hyK⟩ := hlocal (x t) ht t
    have heq : EqOn x y (I.carrier ∩ J.carrier) :=
      D13Unified.Ch03.LocalExistenceUniqueness.overlap_uniqueness F.toODE
        (F.locallyLipschitzInState_of_contDiffOn hF) I J x y t (x t)
        ⟨hx.1, t.property, rfl⟩ hy
    have hnb : (Subtype.val ⁻¹' J.carrier : Set I.carrier) ∈ 𝓝 t :=
      (J.isOpen.preimage continuous_subtype_val).mem_nhds hy.2.1
    apply mem_of_superset hnb
    intro r hr
    change x r ∈ K
    rw [heq ⟨r.property, hr⟩]
    exact hyK r hr
  let : PreconnectedSpace I.carrier :=
    isPreconnected_iff_preconnectedSpace.mp I.ordConnected.isPreconnected
  have hTne : T.Nonempty := ⟨⟨0, hx.2.1⟩, by change x 0 ∈ K; rwa [hx.2.2]⟩
  have hTu : T = univ := IsClopen.eq_univ ⟨hTc, hTo⟩ hTne
  intro t ht
  exact (show (⟨t, ht⟩ : I.carrier) ∈ T by rw [hTu]; trivial)

/-- A local regular scalar constraint whose kernel contains the ambient field
supplies a genuine two-sided constrained solution of that ambient field. -/
theorem local_constrained_solution (F : AutonomousODE E)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {K : Set E} {p : E}
    (hp : p ∈ K) (hKD : K ⊆ F.domain)
    (U : Set E) (hU : IsOpen U) (hpU : p ∈ U)
    (f : E → ℝ) (hf : ContDiffOn ℝ 1 f U)
    (hlevel : ∀ q ∈ U, q ∈ K ↔ f q = 0)
    (hrank : Function.Surjective (fderiv ℝ f p))
    (htan : ∀ q ∈ U, q ∈ K → (fderiv ℝ f q) (F.eval q) = 0) (s : ℝ) :
    ∃ (J : OpenTimeInterval) (y : ℝ → E),
      IsClassicalAutonomousIVPOn F J y s p ∧ ∀ t ∈ J.carrier, y t ∈ K := by
  let V := U ∩ F.domain
  have hV : IsOpen V := hU.inter F.isOpen_domain
  let G : AutonomousODE E :=
    { domain := V
      isOpen_domain := hV
      field := fun q => F.eval q.val
      continuous_field := (hF.continuousOn.mono inter_subset_right).domRestrict }
  have hGeq (q : E) (hq : q ∈ V) : G.eval q = F.eval q := by
    simp only [AutonomousODE.eval, autonomousEvalValue, G, dif_pos hq]
  have hG : ContDiffOn ℝ 1 G.eval G.domain :=
    (hF.mono inter_subset_right).congr (fun q hq => hGeq q hq)
  obtain ⟨J, y, hy, hyzero⟩ :=
    D13Unified.Ch11.RegularConstraints.constrained_local_solution G hG f
      (hf.mono inter_subset_left) 0
      (fun q hq hqzero => by
        rw [hGeq q hq]
        exact htan q hq.1 ((hlevel q hq.1).mpr hqzero))
      p ⟨hpU, hKD hp⟩ ((hlevel p hpU).mp hp) hrank s
  refine ⟨J, y, ⟨⟨hy.1.1, ?_, ?_⟩, hy.2⟩, ?_⟩
  · intro t ht
    exact (hy.1.2.1 t ht).2
  · intro t ht
    change HasDerivAt y (F.eval (y t)) t
    rw [← hGeq (y t) (hy.1.2.1 t ht)]
    exact hy.1.2.2 t ht
  · intro t ht
    exact (hlevel (y t) (hy.1.2.1 t ht).1).mpr (hyzero t ht)

/-- Tangency to genuine locally defining regular constraints proves invariance;
no global defining function, assumed orbit, or completeness is required. -/
theorem local_regular_constraints_invariant (F : AutonomousODE E)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {K : Set E}
    (hKclosed : IsClosed K) (hKD : K ⊆ F.domain)
    (hlocal : ∀ p ∈ K, ∃ (U : Set E) (f : E → ℝ),
      IsOpen U ∧ p ∈ U ∧ ContDiffOn ℝ 1 f U ∧
      (∀ q ∈ U, q ∈ K ↔ f q = 0) ∧
      Function.Surjective (fderiv ℝ f p) ∧
      ∀ q ∈ U, q ∈ K → (fderiv ℝ f q) (F.eval q) = 0) :
    invariantValue F K := by
  apply invariant_of_local_constrained_solutions F hF hKclosed hKD
  intro p hp s
  obtain ⟨U, f, hU, hpU, hf, hlevel, hrank, htan⟩ := hlocal p hp
  exact local_constrained_solution F hF hp hKD U hU hpU f hf hlevel hrank htan s
end LocalConstraintInvariant

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace BoundaryPeriodic
open D13Unified D13Unified.Ch13.Nullclines D13Unified.Ch06.StateDerivative
open D13Unified.Ch11.Orbits D13Unified.Ch13.PoincareBendixson
open Specs.D13Unified.Ch11.Invariant Specs.D13Unified.Ch13.Nullclines
open Specs.D13Unified.Ch13.OmegaSection

/-- In a plane, a nonzero tangent annihilated by a linear functional is
transverse to every vector on which that functional is nonzero. -/
theorem functional_transverse (L : Plane →L[ℝ] ℝ) (v d : Plane)
    (hv : v ≠ 0) (hLv : L v = 0) (hLd : L d ≠ 0) :
    d.1 * v.2 - d.2 * v.1 ≠ 0 := by
  have hcoord (z : Plane) : L z = z.1 * L (1,0) + z.2 * L (0,1) := by
    have hz : z = z.1 • (1,0) + z.2 • (0,1) := by ext <;> simp
    rw [hz, map_add, map_smul, map_smul]
    simp
  intro hdet
  have he₁ : L d * v.1 = 0 := by
    rw [hcoord d]
    have hh := hLv
    rw [hcoord v] at hh
    linear_combination d.1 * hh - L (0,1) * hdet
  have he₂ : L d * v.2 = 0 := by
    rw [hcoord d]
    have hh := hLv
    rw [hcoord v] at hh
    linear_combination d.2 * hh + L (1,0) * hdet
  have hv₁ : v.1 = 0 := (mul_eq_zero.mp he₁).resolve_left hLd
  have hv₂ : v.2 = 0 := (mul_eq_zero.mp he₂).resolve_left hLd
  exact hv (Prod.ext hv₁ hv₂)

/-- A regular local defining function yields an actual isolated transverse
segment. This hypothesis records ordinary local level-set geometry, not an
orbit or parametrization certificate. -/
theorem isolated_transverse_section_of_defining_function (F : AutonomousODE Plane)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {K : Set Plane} {p : Plane}
    (hpK : p ∈ K) (hpD : p ∈ F.domain)
    (f : Plane → ℝ) (L : Plane →L[ℝ] ℝ)
    (hf : HasFDerivAt f L p) (hfzero : f p = 0)
    (hlocal : ∀ᶠ q in 𝓝 p, q ∈ K → f q = 0)
    (hL : L ≠ 0) (hLv : L (F.eval p) = 0) (hv : F.eval p ≠ 0) :
    ∃ S : TransverseSegment F,
      S.center = p ∧ K ∩ sectionInteriorValue S.toStraightSegment = {p} := by
  obtain ⟨d, hLd⟩ : ∃ d, L d ≠ 0 := by
    by_contra h
    push_neg at h
    apply hL
    apply ContinuousLinearMap.ext
    intro z
    simpa using h z
  have hd : d ≠ 0 := by intro h; apply hLd; simp [h]
  have htrans := functional_transverse L (F.eval p) d hv hLv hLd
  let a : ℝ → Plane := fun t => p + t • d
  have ha : Continuous a := continuous_const.add (continuous_id.smul continuous_const)
  have ha0 : a 0 = p := by simp [a]
  have hda : HasDerivAt a d 0 := by
    have hh := (hasDerivAt_const (0 : ℝ) p).add
      ((hasDerivAt_id (0 : ℝ)).smul_const d)
    change HasDerivAt a (0 + (1 : ℝ) • d) 0 at hh
    simpa only [one_smul, zero_add] using hh
  have hfg : HasDerivAt (fun t => f (a t)) (L d) 0 := by
    have hf' : HasFDerivAt f L (a 0) := by simpa only [ha0] using hf
    exact hf'.comp_hasDerivAt 0 hda
  have hnonzero : ∀ᶠ t in 𝓝 (0 : ℝ), t ≠ 0 → f (a t) ≠ 0 := by
    simpa only [eventually_nhdsWithin_iff, mem_compl_iff, mem_singleton_iff]
      using (hfg.eventually_ne hLd : ∀ᶠ t in 𝓝[≠] (0 : ℝ), f (a t) ≠ 0)
  have hcontF : ContinuousAt F.eval p :=
    hF.continuousOn.continuousAt (F.isOpen_domain.mem_nhds hpD)
  have hnormal : ContinuousAt
      (fun t : ℝ => d.1 * (F.eval (a t)).2 - d.2 * (F.eval (a t)).1) 0 := by
    have hc : ContinuousAt (fun t : ℝ => F.eval (a t)) 0 := by
      have hf0 : ContinuousAt F.eval (a 0) := by rw [ha0]; exact hcontF
      exact hf0.comp (ha.continuousAt : ContinuousAt a 0)
    exact (continuousAt_const.mul hc.snd).sub (continuousAt_const.mul hc.fst)
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ),
      a t ∈ F.domain ∧
      d.1 * (F.eval (a t)).2 - d.2 * (F.eval (a t)).1 ≠ 0 ∧
      (a t ∈ K → f (a t) = 0) ∧ (t ≠ 0 → f (a t) ≠ 0) := by
    have hap : Tendsto a (𝓝 0) (𝓝 p) := by
      rw [← ha0]
      exact ha.continuousAt
    have hD := hap (F.isOpen_domain.mem_nhds hpD)
    have hN := hnormal.eventually_ne (by simpa [ha0] using htrans)
    have hZ := hap hlocal
    filter_upwards [hD, hN, hZ, hnonzero] with t htD htN htZ htn
    exact ⟨htD, htN, htZ, htn⟩
  obtain ⟨ε, hε, hεnear⟩ := Metric.eventually_nhds_iff.mp hnear
  let S : StraightSegment := ⟨p, d, ε/2, by linarith, hd⟩
  have hsmall (t : ℝ) (ht : t ∈ Icc (-S.radius) S.radius) :
      dist t 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_lt]
    change -(ε/2) ≤ t ∧ t ≤ ε/2 at ht
    constructor <;> linarith [ht.1, ht.2]
  have hS : isTransverseValue F S := by
    constructor
    · rintro q ⟨t, ht, rfl⟩
      exact (hεnear (hsmall t ht)).1
    · rintro q ⟨t, ht, rfl⟩
      exact (hεnear (hsmall t ht)).2.1
  refine ⟨⟨S, hS⟩, rfl, ?_⟩
  apply Set.ext
  intro q
  constructor
  · rintro ⟨hqK, t, ht, rfl⟩
    have htnear := hεnear (hsmall t ⟨ht.1.le, ht.2.le⟩)
    have ht0 : t = 0 := by
      by_contra ht0
      exact htnear.2.2.2 ht0 (htnear.2.2.1 hqK)
    simp only [mem_singleton_iff]
    simp [segmentPointValue, S, ht0]
  · rintro rfl
    refine ⟨hpK, 0, ?_, ?_⟩
    · change -(ε/2) < 0 ∧ 0 < ε/2
      constructor <;> linarith
    · simp [segmentPointValue, S]

/-- On a connected invariant planar set with isolated local transverse sections,
any complete periodic orbit is the whole set. -/
theorem periodic_orbit_eq_connected_set (F : AutonomousODE Plane)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {K : Set Plane}
    (hKconn : IsPreconnected K) (hKinv : invariantValue F K)
    (hsections : ∀ y ∈ K, ∃ S : TransverseSegment F,
      S.center = y ∧ K ∩ sectionInteriorValue S.toStraightSegment = {y})
    {p : Plane} (hp : p ∈ K) (hpperiod : HasLeastPeriod F p) : orbit F p = K := by
  have horbit : orbit F p ⊆ K := by
    rintro _ ⟨t, ht, rfl⟩
    exact hKinv.2 p hp t ht
  have hclosed : IsClosed (orbit F p) := (compact_orbit F hF (hKinv.1 hp) hpperiod).isClosed
  letI : PreconnectedSpace K := isPreconnected_iff_preconnectedSpace.mp hKconn
  let A : Set K := Subtype.val ⁻¹' orbit F p
  have hAclosed : IsClosed A := hclosed.preimage continuous_subtype_val
  have hAopen : IsOpen A := by
    apply isOpen_iff_mem_nhds.mpr
    intro y hy
    obtain ⟨S, hSy, hS⟩ := hsections y.val y.property
    have hS' : K ∩ sectionInteriorValue S.toStraightSegment = {S.center} := by
      simpa [hSy] using hS
    obtain ⟨U, hU, hyU, hUorbit⟩ := local_orbit F hF hKinv S hS'
    have heq : orbit F S.center = orbit F p := by
      obtain ⟨t, ht, he⟩ := hy
      rw [hSy, ← he]
      exact orbit_rebase F hF (hKinv.1 hp) ht
    refine Filter.mem_of_superset
      ((hU.preimage continuous_subtype_val).mem_nhds (by simpa [hSy] using hyU)) ?_
    intro z hz
    change z.val ∈ orbit F p
    rw [← heq]
    exact hUorbit z.val ⟨z.property, hz⟩
  have hpA : (⟨p, hp⟩ : K) ∈ A := by
    exact ⟨0, (flow_ivp F hF (hKinv.1 hp)).2.1,
      (flow_ivp F hF (hKinv.1 hp)).2.2⟩
  have hAuniv : A = univ := IsClopen.eq_univ ⟨hAclosed, hAopen⟩ ⟨_, hpA⟩
  refine Subset.antisymm horbit ?_
  intro y hy
  have : (⟨y, hy⟩ : K) ∈ A := by rw [hAuniv]; trivial
  exact this

/-- Compactness and nonvanishing produce the periodic orbit, so a connected
invariant curve with isolated transverse sections is exactly one periodic orbit. -/
theorem connected_compact_invariant_set_is_periodic_orbit (F : AutonomousODE Plane)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {K : Set Plane}
    (hne : K.Nonempty) (hK : IsCompact K) (hKconn : IsPreconnected K)
    (hKinv : invariantValue F K) (hregular : ∀ y ∈ K, F.eval y ≠ 0)
    (hsections : ∀ y ∈ K, ∃ S : TransverseSegment F,
      S.center = y ∧ K ∩ sectionInteriorValue S.toStraightSegment = {y}) :
    ∃ p ∈ K, HasLeastPeriod F p ∧ orbit F p = K := by
  have hpositive : positiveInvariantValue F K :=
    ⟨hKinv.1, fun y hy t ht _ => hKinv.2 y hy t ht⟩
  obtain ⟨_, p, hp, _, hperiod, _⟩ :=
    D13Unified.Ch13.Trapping.trapping F hF K hne hK hpositive hregular
  exact ⟨p, hp, hperiod,
    periodic_orbit_eq_connected_set F hF hKconn hKinv hsections hp hperiod⟩
end BoundaryPeriodic

noncomputable section
open Set Function
namespace PlanarOrbitLoop
open D13Unified D13Unified.Ch06.StateDerivative D13Unified.Ch11.Orbits
open Specs.D13Unified.Ch21.Collar

theorem flow_eq_iff_period_plane (F : AutonomousODE (ℝ × ℝ))
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {x : ℝ × ℝ} (hx : x ∈ F.domain)
    (hc : IsComplete F x) (a b : ℝ) :
    flow F a x = flow F b x ↔ Periodic (fun t => flow F t x) (a-b) := by
  have htime (t : ℝ) : t ∈ (flowInterval F x).carrier := by rw [hc]; trivial
  constructor
  · intro he
    by_cases hab : b = a
    · subst b
      simp only [sub_self]
      exact periodic_with_period_zero (fun t => flow F t x)
    · exact (D13Unified.Ch11.Orbits.self_intersection F hF x hx b (htime b)
        a (htime a) hab he.symm).2
  · intro hp
    simpa using hp b

/-- Conversion of an actual complete least-period planar orbit to the complex
plane used by the smooth Jordan theorem; no flow conjugacy is needed. -/
theorem periodic_orbit_loop_plane (F : AutonomousODE (ℝ × ℝ))
    (hF : ContDiffOn ℝ 1 F.eval F.domain) (x : ℝ × ℝ) (hx : x ∈ F.domain)
    (hp : HasLeastPeriod F x)
    (hreg : ∀ t : ℝ, F.eval (flow F t x) ≠ 0) :
    ∃ (T : ℝ) (γ : Circle → ℂ), 0 < T ∧ RegularEmbeddedLoop γ ∧
      range γ = Complex.equivRealProdCLM.symm '' orbit F x ∧
      (∀ t : ℝ, realLift γ t = Complex.equivRealProdCLM.symm (flow F (T * t) x)) ∧
      (∀ t : ℝ, HasDerivAt (realLift γ)
        (T • Complex.equivRealProdCLM.symm (F.eval (flow F (T * t) x))) t) := by
  obtain ⟨hc, T, hT, hperiod, _hleast, hperiods⟩ := hp
  have htime (t : ℝ) : t ∈ (flowInterval F x).carrier := by rw [hc]; trivial
  let e := Complex.equivRealProdCLM.symm
  let g : ℝ → ℂ := fun t => e (flow F (T*t) x)
  have hgperiod : Periodic g 1 := by
    intro t
    change e (flow F (T*(t+1)) x) = e (flow F (T*t) x)
    rw [mul_add, mul_one]
    exact congrArg e (hperiod _)
  let γ : Circle → ℂ := hgperiod.lift
  have hγlift (t : ℝ) : realLift γ t = g t := hgperiod.lift_coe t
  have hX := flow_ivp F hF hx
  have hcont : ContDiff ℝ 1 (fun t => flow F t x) := by
    apply contDiffOn_univ.mp
    simpa only [show (flowInterval F x).carrier = univ from hc] using hX.1.1
  have hgcont : ContDiff ℝ 1 g :=
    e.contDiff.comp (hcont.comp (contDiff_const.mul contDiff_id))
  have heq (t u : ℝ) : realLift γ t = realLift γ u ↔ ∃ k : ℤ, t-u = (k : ℝ) := by
    rw [hγlift, hγlift]
    change e (flow F (T*t) x) = e (flow F (T*u) x) ↔ _
    rw [e.injective.eq_iff, flow_eq_iff_period_plane F hF hx hc, hperiods]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      have hh : T * (t-u) = T * (k : ℝ) := by nlinarith [hk]
      exact mul_left_cancel₀ (ne_of_gt hT) hh
    · rintro ⟨k, hk⟩
      exact ⟨k, by rw [← hk]; ring⟩
  have hd (t : ℝ) : HasDerivAt (realLift γ)
      (T • e (F.eval (flow F (T*t) x))) t := by
    have hlin : HasDerivAt (fun s : ℝ => T*s) T t := by
      simpa using (hasDerivAt_id t).const_mul T
    have houter : HasDerivAt (fun s : ℝ => flow F s x)
        (F.eval (flow F (T*t) x)) (T*t) := hX.1.2.2 _ (htime _)
    have hd := e.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t (houter.scomp t hlin)
    simpa only [show realLift γ = g from funext hγlift, g, Function.comp_def,
      map_smul, ContinuousLinearEquiv.coe_coe] using hd
  have hγ : RegularEmbeddedLoop γ := by
    apply (D13Unified.Ch21.Collar.regularity_bridge γ).mpr
    refine ⟨?_, heq, ?_⟩
    · simpa only [show realLift γ = g from funext hγlift] using hgcont
    · intro t
      rw [(hd t).deriv]
      apply smul_ne_zero (ne_of_gt hT)
      exact fun h => hreg (T*t) (e.injective (by simpa using h))
  refine ⟨T, γ, hT, hγ, ?_, hγlift, hd⟩
  rw [← D13Unified.Ch21.Collar.lift_trace γ]
  apply Subset.antisymm
  · rintro _ ⟨t, rfl⟩
    exact ⟨flow F (T*t) x, ⟨T*t, htime _, rfl⟩, (hγlift t).symm⟩
  · rintro _ ⟨z, ⟨t, _, rfl⟩, rfl⟩
    refine ⟨t/T, ?_⟩
    rw [hγlift]
    change e (flow F (T*(t/T)) x) = e (flow F t x)
    congr 2
    field_simp
end PlanarOrbitLoop

namespace BoundaryParametrization
open D13Unified D13Unified.Ch13.Nullclines D13Unified.Ch06.StateDerivative
open D13Unified.Ch11.Orbits Specs.D13Unified.Ch21.Collar

/-- A compact connected planar regular level curve, equipped with a genuine
nonzero tangent ambient field, has an injective regular circle parametrization
whose derivative follows that field and whose trace is exactly the curve. -/
theorem regular_embedded_loop_of_local_constraints (F : AutonomousODE Plane)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {K : Set Plane}
    (hKne : K.Nonempty) (hK : IsCompact K) (hKconn : IsPreconnected K)
    (hKD : K ⊆ F.domain) (hregular : ∀ p ∈ K, F.eval p ≠ 0)
    (hlocal : ∀ p ∈ K, ∃ (U : Set Plane) (f : Plane → ℝ),
      IsOpen U ∧ p ∈ U ∧ ContDiffOn ℝ 1 f U ∧
      (∀ q ∈ U, q ∈ K ↔ f q = 0) ∧
      Function.Surjective (fderiv ℝ f p) ∧
      ∀ q ∈ U, q ∈ K → (fderiv ℝ f q) (F.eval q) = 0) :
    ∃ (p : Plane) (T : ℝ) (γ : Circle → ℂ), p ∈ K ∧ 0 < T ∧
      RegularEmbeddedLoop γ ∧ range γ = Complex.equivRealProdCLM.symm '' K ∧
      (∀ t : ℝ, realLift γ t = Complex.equivRealProdCLM.symm (flow F (T * t) p)) ∧
      (∀ t : ℝ, HasDerivAt (realLift γ)
        (T • Complex.equivRealProdCLM.symm (F.eval (flow F (T * t) p))) t) := by
  have hInv := LocalConstraintInvariant.local_regular_constraints_invariant
    F hF hK.isClosed hKD hlocal
  have hsections : ∀ p ∈ K, ∃ S : TransverseSegment F,
      S.center = p ∧ K ∩ Specs.D13Unified.Ch13.OmegaSection.sectionInteriorValue
        S.toStraightSegment = {p} := by
    intro p hp
    obtain ⟨U, f, hU, hpU, hf, hlevel, hrank, htan⟩ := hlocal p hp
    have hfd : HasFDerivAt f (fderiv ℝ f p) p :=
      ((hf.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by norm_num)).hasFDerivAt
    have hL : fderiv ℝ f p ≠ 0 := by
      intro hzero
      obtain ⟨v, hv⟩ := hrank 1
      rw [hzero] at hv
      simp at hv
    have hzero : ∀ᶠ q in 𝓝 p, q ∈ K → f q = 0 := by
      filter_upwards [hU.mem_nhds hpU] with q hq hqK
      exact (hlevel q hq).mp hqK
    exact BoundaryPeriodic.isolated_transverse_section_of_defining_function F hF
      hp (hKD hp) f (fderiv ℝ f p) hfd ((hlevel p hpU).mp hp) hzero hL
      (htan p hpU hp) (hregular p hp)
  obtain ⟨p, hp, hperiod, horbit⟩ :=
    BoundaryPeriodic.connected_compact_invariant_set_is_periodic_orbit
      F hF hKne hK hKconn hInv hregular hsections
  have hreg (t : ℝ) : F.eval (flow F t p) ≠ 0 := by
    apply hregular
    rw [← horbit]
    exact ⟨t, by rw [hperiod.1]; trivial, rfl⟩
  obtain ⟨T, γ, hT, hγ, htrace, hlift, hd⟩ :=
    PlanarOrbitLoop.periodic_orbit_loop_plane F hF p (hKD hp) hperiod hreg
  exact ⟨p, T, γ, hp, hT, hγ, by rwa [horbit] at htrace, hlift, hd⟩
end BoundaryParametrization
namespace BoundaryParametrization
open D13Unified D13Unified.Ch13.Nullclines D13Unified.Ch06.StateDerivative
open D13Unified.Ch11.Orbits Specs.D13Unified.Ch21.Collar

/-- Coordinate-independent version for a globally defined C¹ field on any
real normed plane. The pulled-back lift has its genuine derivative positively
proportional to that field. -/
theorem regular_embedded_loop_of_global_tangent_field
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : E ≃L[ℝ] Plane) (F : E → E) (hF : ContDiff ℝ 1 F) {K : Set E}
    (hKne : K.Nonempty) (hK : IsCompact K) (hKconn : IsPreconnected K)
    (hregular : ∀ p ∈ K, F p ≠ 0)
    (hlocal : ∀ p ∈ K, ∃ (U : Set E) (f : E → ℝ),
      IsOpen U ∧ p ∈ U ∧ ContDiffOn ℝ 1 f U ∧
      (∀ q ∈ U, q ∈ K ↔ f q = 0) ∧
      Function.Surjective (fderiv ℝ f p) ∧
      ∀ q ∈ U, q ∈ K → (fderiv ℝ f q) (F q) = 0) :
    let c : E ≃L[ℝ] ℂ := e.trans Complex.equivRealProdCLM.symm
    ∃ (T : ℝ) (γ : Circle → ℂ), 0 < T ∧ RegularEmbeddedLoop γ ∧ range γ = c '' K ∧
      ∀ t : ℝ, c.symm (realLift γ t) ∈ K ∧
        HasDerivAt (fun s => c.symm (realLift γ s))
          (T • F (c.symm (realLift γ t))) t := by
  classical
  let G : AutonomousODE Plane :=
    { domain := univ
      isOpen_domain := isOpen_univ
      field := fun q => e (F (e.symm q.val))
      continuous_field :=
        e.continuous.comp (hF.continuous.comp (e.symm.continuous.comp continuous_subtype_val)) }
  have hGeq (q : Plane) : G.eval q = e (F (e.symm q)) := by
    simp only [AutonomousODE.eval, Specs.D13Unified.Ch01.AutonomousParameters.autonomousEvalValue,
      G, dite_eq_left (mem_univ q)]
  have hG : ContDiffOn ℝ 1 G.eval G.domain := by
    have hcomp : ContDiff ℝ 1 (fun q => e (F (e.symm q))) :=
      e.contDiff.comp (hF.comp e.symm.contDiff)
    exact hcomp.contDiffOn.congr (fun q _ => hGeq q)
  have hK'reg : ∀ q ∈ e '' K, G.eval q ≠ 0 := by
    rintro q ⟨p, hp, rfl⟩
    rw [hGeq, e.symm_apply_apply]
    exact fun h => hregular p hp (e.injective (by simpa using h))
  have hlocal' : ∀ p ∈ e '' K, ∃ (U : Set Plane) (f : Plane → ℝ),
      IsOpen U ∧ p ∈ U ∧ ContDiffOn ℝ 1 f U ∧
      (∀ q ∈ U, q ∈ e '' K ↔ f q = 0) ∧
      Function.Surjective (fderiv ℝ f p) ∧
      ∀ q ∈ U, q ∈ e '' K → (fderiv ℝ f q) (G.eval q) = 0 := by
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨U, f, hU, hpU, hf, hlevel, hrank, htan⟩ := hlocal p hp
    let V := e.symm ⁻¹' U
    let g : Plane → ℝ := fun q => f (e.symm q)
    have hg : ContDiffOn ℝ 1 g V :=
      hf.comp e.symm.contDiff.contDiffOn (fun _ hq => hq)
    have hd (q : Plane) (hq : q ∈ V) :
        fderiv ℝ g q = (fderiv ℝ f (e.symm q)).comp e.symm.toContinuousLinearMap := by
      exact (((hf.contDiffAt (hU.mem_nhds hq)).differentiableAt (by norm_num)).hasFDerivAt.comp q
        e.symm.toContinuousLinearMap.hasFDerivAt).fderiv
    have heK (q : Plane) : q ∈ e '' K ↔ e.symm q ∈ K := by
      constructor
      · rintro ⟨v, hv, rfl⟩
        simpa using hv
      · intro hq
        exact ⟨e.symm q, hq, e.apply_symm_apply q⟩
    refine ⟨V, g, hU.preimage e.symm.continuous, ?_, hg, ?_, ?_, ?_⟩
    · change e.symm (e p) ∈ U
      simpa using hpU
    · intro q hq
      rw [heK]
      exact hlevel (e.symm q) hq
    · intro a
      obtain ⟨v, hv⟩ := hrank a
      refine ⟨e v, ?_⟩
      rw [hd (e p) (by simpa [V] using hpU)]
      simpa using hv
    · intro q hq hqK
      rw [hd q hq, hGeq]
      simpa using htan (e.symm q) hq ((heK q).mp hqK)
  obtain ⟨p, T, γ, hp, hT, hγ, htrace, hlift, hd⟩ :=
    regular_embedded_loop_of_local_constraints G hG
      (hKne.image e) (hK.image e.continuous) (hKconn.image e e.continuous.continuousOn)
      (subset_univ _) hK'reg hlocal'
  let c : E ≃L[ℝ] ℂ := e.trans Complex.equivRealProdCLM.symm
  refine ⟨T, γ, hT, hγ, ?_, ?_⟩
  · change range γ = (fun x => Complex.equivRealProdCLM.symm (e x)) '' K
    rw [← image_image]
    exact htrace
  · intro t
    have hpt : realLift γ t ∈ range γ := by
      exact ⟨_, rfl⟩
    have hct : c.symm (realLift γ t) ∈ K := by
      have htrace' : range γ = c '' K := by
        change range γ = (fun x => Complex.equivRealProdCLM.symm (e x)) '' K
        rw [← image_image]
        exact htrace
      rw [htrace'] at hpt
      obtain ⟨v, hv, he⟩ := hpt
      rw [← he, c.symm_apply_apply]
      exact hv
    refine ⟨hct, ?_⟩
    have hdc := c.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t (hd t)
    have hcp : c.symm (realLift γ t) = e.symm (flow G (T * t) p) := by
      rw [hlift]
      simp [c]
    change HasDerivAt (fun s => c.symm (realLift γ s))
      (c.symm (T • Complex.equivRealProdCLM.symm (G.eval (flow G (T * t) p)))) t at hdc
    have hval : c.symm (T • Complex.equivRealProdCLM.symm (G.eval (flow G (T * t) p))) =
        T • F (c.symm (realLift γ t)) := by
      rw [map_smul, hGeq, hcp]
      simp [c]
    rw [hval] at hdc
    exact hdc
end BoundaryParametrization



namespace PlanarThinCollar
noncomputable section
open Set Filter
open scoped Topology
open Specs.D13Unified.Ch21.Collar

/-- A connected set missing the frontier cannot change the side of a closed set. -/
theorem connected_avoiding_frontier {X : Type*} [TopologicalSpace X]
    {D A : Set X} (hD : IsClosed D) (hA : IsPreconnected A)
    (havoid : A ⊆ (frontier D)ᶜ) :
    A ⊆ interior D ∨ A ⊆ Dᶜ := by
  apply hA.subset_or_subset isOpen_interior hD.isOpen_compl
  · exact Set.disjoint_left.mpr (fun _ hx hy => hy (interior_subset hx))
  · intro x hx
    by_cases hxin : x ∈ D
    · exact Or.inl (by
        by_contra h
        exact havoid hx (by rw [hD.frontier_eq]; exact ⟨hxin, h⟩))
    · exact Or.inr hxin

/-- One interior witness determines the side of the entire connected set. -/
theorem connected_avoiding_frontier_subset_interior {X : Type*} [TopologicalSpace X]
    {D A : Set X} (hD : IsClosed D) (hA : IsPreconnected A)
    (havoid : A ⊆ (frontier D)ᶜ) (hwitness : (A ∩ interior D).Nonempty) :
    A ⊆ interior D := by
  rcases connected_avoiding_frontier hD hA havoid with h | h
  · exact h
  · obtain ⟨x, hx, hxi⟩ := hwitness
    exact False.elim (h hx (interior_subset hxi))

/-- One exterior witness likewise fixes the exterior side. -/
theorem connected_avoiding_frontier_subset_compl {X : Type*} [TopologicalSpace X]
    {D A : Set X} (hD : IsClosed D) (hA : IsPreconnected A)
    (havoid : A ⊆ (frontier D)ᶜ) (hwitness : (A ∩ Dᶜ).Nonempty) :
    A ⊆ Dᶜ := by
  rcases connected_avoiding_frontier hD hA havoid with h | h
  · obtain ⟨x, hx, hxi⟩ := hwitness
    exact False.elim (hxi (interior_subset (h hx)))
  · exact h

/-- Compactness gives uniform avoidance of any closed set missed by the zero section. -/
theorem uniform_tube_avoids_closed {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] (F : X × ℝ → Y) (hF : Continuous F)
    {K : Set Y} (hK : IsClosed K) (hzero : ∀ x : X, F (x, 0) ∉ K) :
    ∃ b : ℝ, 0 < b ∧ ∀ x r, r ∈ Ioo (-b) b → F (x, r) ∉ K := by
  have hlocal : ∀ x : X, ∀ᶠ z : ℝ × X in 𝓝 ((0 : ℝ), x), F (z.2, z.1) ∉ K := by
    intro x
    exact ((hF.comp continuous_swap).continuousAt (x := ((0 : ℝ), x))).eventually
      (hK.isOpen_compl.mem_nhds (hzero x))
  have huniform : ∀ᶠ r in 𝓝 (0 : ℝ), ∀ x : X, F (x, r) ∉ K := by
    simpa only [mem_univ, forall_const] using
      isCompact_univ.eventually_forall_of_forall_eventually (fun x (_ : x ∈ (univ : Set X)) => hlocal x)
  obtain ⟨b, hb, hball⟩ := Metric.mem_nhds_iff.mp huniform
  refine ⟨b, hb, fun x r hr => hball ?_ x⟩
  simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt, mem_Ioo] using hr

/-- Width monotonicity for collar cylinders. -/
theorem cylinder_mono {b a : ℝ} (hba : b ≤ a) : cylinder b ⊆ cylinder a := by
  intro p hp
  exact ⟨hp.1, lt_of_le_of_lt (neg_le_neg hba) hp.2.1, lt_of_lt_of_le hp.2.2 hba⟩

/-- Every thinner collar has the same two connected sides, still missing the trace. -/
theorem thin_sides_properties {γ v : Circle → ℂ} {a b : ℝ}
    (hγ : CircleC1 γ) (hc : IsCollar γ v a) (hb : 0 < b) (hba : b ≤ a) :
    Disjoint (positiveSide γ v b) (negativeSide γ v b) ∧
    IsPathConnected (positiveSide γ v b) ∧ IsPathConnected (negativeSide γ v b) ∧
    positiveSide γ v b ⊆ (range γ)ᶜ ∧ negativeSide γ v b ⊆ (range γ)ᶜ := by
  obtain ⟨ha, hv, ht, e, hs, he, _⟩ := hc
  apply D13Unified.Ch21.Collar.sides_properties hγ hv hb
  have hi : InjOn (collarMap γ v) (cylinder a) := by
    intro p hp q hq hpq
    apply e.injOn (hs.symm ▸ hp) (hs.symm ▸ hq)
    simpa only [he] using hpq
  exact hi.mono (cylinder_mono hba)

/-- A genuine collar can be shrunk so both sides miss an additional closed set.
The empty additional-set case is included. -/
theorem exists_thin_sides_avoiding_closed {γ v : Circle → ℂ} {a : ℝ}
    (hγ : CircleC1 γ) (hc : IsCollar γ v a) {K : Set ℂ}
    (hK : IsClosed K) (hdisj : Disjoint (range γ) K) :
    ∃ b : ℝ, 0 < b ∧ b ≤ a ∧
      IsPathConnected (positiveSide γ v b) ∧ IsPathConnected (negativeSide γ v b) ∧
      positiveSide γ v b ⊆ (range γ ∪ K)ᶜ ∧
      negativeSide γ v b ⊆ (range γ ∪ K)ᶜ := by
  obtain ⟨d, hd, havoid⟩ := uniform_tube_avoids_closed (collarMap γ v)
    (D13Unified.Ch21.Collar.collarMap_continuous hγ hc.2.1) hK (by
      intro x
      simpa only [collarMap, zero_smul, add_zero] using
        Set.disjoint_left.mp hdisj (show γ x ∈ range γ from ⟨x, rfl⟩))
  let b := min a d
  have hb : 0 < b := lt_min hc.1 hd
  have hba : b ≤ a := min_le_left _ _
  have hbd : b ≤ d := min_le_right _ _
  obtain ⟨_, hpc, hmc, hpt, hmt⟩ := thin_sides_properties hγ hc hb hba
  refine ⟨b, hb, hba, hpc, hmc, ?_, ?_⟩
  · rintro z hz (hzt | hzk)
    · exact hpt hz hzt
    · obtain ⟨⟨x,r⟩, hr, rfl⟩ := hz
      exact havoid x r ⟨by linarith [hr.2.1], lt_of_lt_of_le hr.2.2 hbd⟩ hzk
  · rintro z hz (hzt | hzk)
    · exact hmt hz hzt
    · obtain ⟨⟨x,r⟩, hr, rfl⟩ := hz
      exact havoid x r ⟨lt_of_le_of_lt (neg_le_neg hbd) hr.2.1, by linarith [hr.2.2]⟩ hzk


/-- The image of a thinner collar is an actual ambient open neighborhood of the trace. -/
theorem thin_neighborhood {γ v : Circle → ℂ} {a b : ℝ}
    (hc : IsCollar γ v a) (hb : 0 < b) (hba : b ≤ a) :
    IsOpen (collarMap γ v '' cylinder b) ∧
    collarMap γ v '' cylinder b = range γ ∪ positiveSide γ v b ∪ negativeSide γ v b := by
  obtain ⟨_, _, _, e, hs, he, _⟩ := hc
  have hsub : cylinder b ⊆ e.source := by
    rw [hs]
    exact cylinder_mono hba
  refine ⟨?_, ?_⟩
  · have hh := e.isOpen_image_of_subset_source
      (show IsOpen (cylinder b) from isOpen_univ.prod isOpen_Ioo) hsub
    have hfun : (e : Circle × ℝ → ℂ) = collarMap γ v := funext he
    rwa [hfun] at hh
  · ext z
    constructor
    · rintro ⟨⟨x,r⟩, hr, rfl⟩
      rcases lt_trichotomy r 0 with hneg | hzero | hpos
      · exact Or.inr ⟨(x,r), ⟨mem_univ _, hr.2.1, hneg⟩, rfl⟩
      · exact Or.inl (Or.inl (by subst r; exact ⟨x, by simp [collarMap]⟩))
      · exact Or.inl (Or.inr ⟨(x,r), ⟨mem_univ _, hpos, hr.2.2⟩, rfl⟩)
    · rintro ((⟨x,rfl⟩ | ⟨⟨x,r⟩,hr,rfl⟩) | ⟨⟨x,r⟩,hr,rfl⟩)
      · exact ⟨(x,0), ⟨mem_univ _, neg_neg_of_pos hb, hb⟩, by simp [collarMap]⟩
      · exact ⟨(x,r), ⟨mem_univ _, by linarith [hr.2.1], hr.2.2⟩, rfl⟩
      · exact ⟨(x,r), ⟨mem_univ _, hr.2.1, by linarith [hr.2.2]⟩, rfl⟩

/-- Once the two connected sides have one correct witness each, the actual domain
inside this open collar neighborhood consists precisely of the trace and left side. -/
theorem domain_inter_thin_neighborhood {γ v : Circle → ℂ} {a b : ℝ}
    (hγ : CircleC1 γ) (hc : IsCollar γ v a) (hb : 0 < b) (hba : b ≤ a)
    {D : Set ℂ} (hD : IsClosed D) (htrace : range γ ⊆ D)
    (hpavoid : positiveSide γ v b ⊆ (frontier D)ᶜ)
    (hmavoid : negativeSide γ v b ⊆ (frontier D)ᶜ)
    (hpwitness : (positiveSide γ v b ∩ interior D).Nonempty)
    (hmwitness : (negativeSide γ v b ∩ Dᶜ).Nonempty) :
    IsOpen (collarMap γ v '' cylinder b) ∧
    range γ ⊆ collarMap γ v '' cylinder b ∧
    positiveSide γ v b ⊆ interior D ∧ negativeSide γ v b ⊆ Dᶜ ∧
    D ∩ (collarMap γ v '' cylinder b) = range γ ∪ positiveSide γ v b := by
  obtain ⟨_, hpc, hmc, _, _⟩ := thin_sides_properties hγ hc hb hba
  have hp := connected_avoiding_frontier_subset_interior hD
    hpc.isConnected.isPreconnected hpavoid hpwitness
  have hm := connected_avoiding_frontier_subset_compl hD
    hmc.isConnected.isPreconnected hmavoid hmwitness
  obtain ⟨hNopen, hN⟩ := thin_neighborhood hc hb hba
  refine ⟨hNopen, ?_, hp, hm, ?_⟩
  · rw [hN]
    exact fun _ hz => Or.inl (Or.inl hz)
  · rw [hN]
    ext z
    constructor
    · rintro ⟨hzD, (hzC | hzP) | hzM⟩
      · exact Or.inl hzC
      · exact Or.inr hzP
      · exact False.elim (hm hzM hzD)
    · rintro (hzC | hzP)
      · exact ⟨htrace hzC, Or.inl (Or.inl hzC)⟩
      · exact ⟨interior_subset (hp hzP), Or.inl (Or.inr hzP)⟩

/-- The same open collar equality expresses the domain as the local closure
of whichever Jordan region contains the geometric left side. -/
theorem domain_inter_neighborhood_eq_region_closure
    {D N C P M Ω : Set ℂ}
    (hN : N = C ∪ P ∪ M) (hD : D ∩ N = C ∪ P)
    (hcl : closure Ω = Ω ∪ C) (hP : P ⊆ Ω)
    (hMΩ : Disjoint M Ω) (hMC : Disjoint M C) :
    D ∩ N = N ∩ closure Ω := by
  rw [hD, hN, hcl]
  ext z
  constructor
  · rintro (hzC | hzP)
    · exact ⟨Or.inl (Or.inl hzC), Or.inr hzC⟩
    · exact ⟨Or.inl (Or.inr hzP), Or.inl (hP hzP)⟩
  · rintro ⟨(hzC | hzP) | hzM, hzcl⟩
    · exact Or.inl hzC
    · exact Or.inr hzP
    · rcases hzcl with hzΩ | hzC
      · exact False.elim (Set.disjoint_left.mp hMΩ hzM hzΩ)
      · exact False.elim (Set.disjoint_left.mp hMC hzM hzC)


/-- Actual local rays produce witnesses in arbitrarily thin collar sides. -/
theorem thin_side_witnesses_of_rays {γ v : Circle → ℂ} {b : ℝ} (hb : 0 < b)
    {D : Set ℂ} {x : Circle}
    (hpos : ∀ᶠ r in 𝓝[>] (0 : ℝ), γ x + r • v x ∈ interior D)
    (hneg : ∀ᶠ r in 𝓝[>] (0 : ℝ), γ x + (-r) • v x ∉ D) :
    (positiveSide γ v b ∩ interior D).Nonempty ∧
    (negativeSide γ v b ∩ Dᶜ).Nonempty := by
  constructor
  · obtain ⟨r, hr, hD⟩ := (Filter.Eventually.and (Ioo_mem_nhdsGT hb) hpos).exists
    exact ⟨γ x + r • v x, ⟨(x,r), ⟨mem_univ _, hr⟩, rfl⟩, hD⟩
  · obtain ⟨r, hr, hD⟩ := (Filter.Eventually.and (Ioo_mem_nhdsGT hb) hneg).exists
    exact ⟨γ x + (-r) • v x,
      ⟨(x,-r), ⟨mem_univ _, by simpa using hr.2, neg_neg_of_pos hr.1⟩, rfl⟩, hD⟩

/-- The bounded and unbounded actual components are determined by the trace,
independently of which regular parametrization yielded Jordan separation. -/
theorem jordan_regions_unique {S Ω E Ω' E' : Set ℂ}
    (h : Specs.D13Unified.Ch21.SmoothJordan.TwoComponents S Ω E)
    (h' : Specs.D13Unified.Ch21.SmoothJordan.TwoComponents S Ω' E')
    (hΩb : Bornology.IsBounded Ω) (hE'b : ¬ Bornology.IsBounded E') :
    Ω = Ω' ∧ E = E' := by
  rcases h with ⟨hΩn, _, hdisj, hcover, hΩcomp, hEcomp⟩
  rcases h' with ⟨_, _, hdisj', hcover', hΩcomp', hEcomp'⟩
  obtain ⟨p, hp⟩ := hΩn
  have hpS : p ∈ S := hcover ▸ Or.inl hp
  have heq : Ω = Ω' := by
    rw [← hcover'] at hpS
    rcases hpS with hp' | hp'
    · exact (hΩcomp p hp).symm.trans (hΩcomp' p hp')
    · have hbad : Ω = E' := (hΩcomp p hp).symm.trans (hEcomp' p hp')
      exact False.elim (hE'b (hbad ▸ hΩb))
  refine ⟨heq, ?_⟩
  subst Ω'
  ext z
  constructor
  · intro hz
    have hzS : z ∈ S := hcover ▸ Or.inr hz
    rw [← hcover'] at hzS
    rcases hzS with hzΩ | hzE
    · exact False.elim (Set.disjoint_left.mp hdisj hzΩ hz)
    · exact hzE
  · intro hz
    have hzS : z ∈ S := hcover' ▸ Or.inr hz
    rw [← hcover] at hzS
    rcases hzS with hzΩ | hzE
    · exact False.elim (Set.disjoint_left.mp hdisj' hzΩ hz)
    · exact hzE


/-- Oriented basis identity in the actual complex plane. -/
theorem det_basis_identity (ν τ v : ℂ) :
    det ν τ • v = det v τ • ν + det ν v • τ := by
  apply Complex.ext <;>
    simp [det, Complex.real_smul, Complex.mul_re, Complex.mul_im] <;> ring

/-- For an outward-first positive tangent, every geometrically left transverse
vector has positive inward defining covector. No unit or orthogonality assumptions
are needed for this basis computation. -/
theorem inward_covector_positive_of_left_transverse {ν τ v : ℂ}
    (L : ℂ →L[ℝ] ℝ) (hν : L ν < 0) (hτ : L τ = 0)
    (hpositive : 0 < det ν τ) (hleft : 0 < det τ v) : 0 < L v := by
  have heq := congrArg L (det_basis_identity ν τ v)
  simp only [map_smul, map_add, hτ, smul_eq_mul, mul_zero, add_zero] at heq
  have hanti : det v τ = - det τ v := by simp only [det]; ring
  rw [hanti] at heq
  have hm : 0 < det ν τ * L v := by
    rw [heq]
    exact mul_pos_of_neg_of_neg (neg_neg_of_pos hleft) hν
  exact (mul_pos_iff_of_pos_left hpositive).mp hm


 theorem positiveSide_mono {γ v : Circle → ℂ} {b a : ℝ} (hba : b ≤ a) :
    positiveSide γ v b ⊆ positiveSide γ v a := by
  rintro z ⟨p,hp,rfl⟩
  exact ⟨p, ⟨hp.1, hp.2.1, lt_of_lt_of_le hp.2.2 hba⟩, rfl⟩

 theorem negativeSide_mono {γ v : Circle → ℂ} {b a : ℝ} (hba : b ≤ a) :
    negativeSide γ v b ⊆ negativeSide γ v a := by
  rintro z ⟨p,hp,rfl⟩
  exact ⟨p, ⟨hp.1, lt_of_le_of_lt (neg_le_neg hba) hp.2.1, hp.2.2⟩, rfl⟩

open Specs.D13Unified.Ch21.SmoothJordan
open Specs.D13Unified.Ch21.IndexProperties (index circleLoop)

/-- Conditional global bridge for an actual regular boundary component with
actual local inward/exterior rays. The conclusion identifies outer/inner by
an equality with the actual domain on an ambient open neighborhood and retains
the corresponding winding sign. No parametrization existence is asserted here. -/
theorem local_jordan_domain_and_signed_index
    (γ : Circle → ℂ) (hγ : RegularEmbeddedLoop γ) {v : Circle → ℂ} {a : ℝ}
    (hc : IsCollar γ v a) {D : Set ℂ} (hD : IsClosed D)
    (htrace : range γ ⊆ frontier D) (hother : IsClosed (frontier D \ range γ))
    {x : Circle}
    (hin : ∀ᶠ r in 𝓝[>] (0 : ℝ), γ x + r • v x ∈ interior D)
    (hout : ∀ᶠ r in 𝓝[>] (0 : ℝ), γ x + (-r) • v x ∉ D) :
    ∃ Ω E N : Set ℂ,
      TwoComponents (range γ)ᶜ Ω E ∧
      IsOpen Ω ∧ IsOpen E ∧ IsPathConnected Ω ∧ IsPathConnected E ∧
      Bornology.IsBounded Ω ∧ ¬ Bornology.IsBounded E ∧
      frontier Ω = range γ ∧ frontier E = range γ ∧
      IsOpen N ∧ range γ ⊆ N ∧
      (∀ p ∈ E, index (circleLoop (regularLoopMap γ hγ)) p = 0) ∧
      ((D ∩ N = N ∩ closure Ω ∧
        ∀ p ∈ Ω, index (circleLoop (regularLoopMap γ hγ)) p = 1) ∨
       (D ∩ N = N ∩ closure E ∧
        ∀ p ∈ Ω, index (circleLoop (regularLoopMap γ hγ)) p = -1)) := by
  let γc := regularLoopMap γ hγ
  obtain ⟨P, M, hPM, hPo, hMo, hPc, hMc, hp, hm, hjump⟩ :=
    D13Unified.Ch21.SmoothJordan.collar_components γc hγ v a hc
  obtain ⟨hPf, hMf⟩ :=
    D13Unified.Ch21.SmoothJordan.collar_frontiers hc hPM hPo hMo hp hm
  have hPcl : closure P = P ∪ range γ := by
    rw [closure_eq_self_union_frontier, hPf]
  have hMcl : closure M = M ∪ range γ := by
    rw [closure_eq_self_union_frontier, hMf]
  obtain ⟨b, hb, hba, hpbconn, hmbconn, hpbavoid, hmbavoid⟩ :=
    exists_thin_sides_avoiding_closed hγ.1 hc hother
      (Set.disjoint_left.mpr (fun _ hz hother => hother.2 hz))
  have hwhole : range γ ∪ (frontier D \ range γ) = frontier D := by
    ext z
    constructor
    · rintro (hz | hz)
      · exact htrace hz
      · exact hz.1
    · intro hz
      by_cases hzC : z ∈ range γ
      · exact Or.inl hzC
      · exact Or.inr ⟨hz, hzC⟩
  rw [hwhole] at hpbavoid hmbavoid
  obtain ⟨hpin, hmin⟩ := thin_side_witnesses_of_rays hb hin hout
  obtain ⟨hNopen, hCN, _, _, hDN⟩ := domain_inter_thin_neighborhood hγ.1 hc hb hba
    hD (fun _ hz => hD.closure_eq ▸ (htrace hz).1) hpbavoid hmbavoid hpin hmin
  let N := collarMap γ v '' cylinder b
  have hN : N = range γ ∪ positiveSide γ v b ∪ negativeSide γ v b :=
    (thin_neighborhood hc hb hba).2
  have hpbP : positiveSide γ v b ⊆ P := (positiveSide_mono hba).trans hp
  have hmbM : negativeSide γ v b ⊆ M := (negativeSide_mono hba).trans hm
  have hmbP : Disjoint (negativeSide γ v b) P := by
    exact Set.disjoint_left.mpr (fun _ hz hzP => Set.disjoint_left.mp hPM.2.2.1 hzP (hmbM hz))
  have hmbC : Disjoint (negativeSide γ v b) (range γ) := by
    exact Set.disjoint_left.mpr (fun _ hz hzC => (thin_sides_properties hγ.1 hc hb hba).2.2.2.2 hz hzC)
  have hlocalP : D ∩ N = N ∩ closure P :=
    domain_inter_neighborhood_eq_region_closure hN hDN hPcl hpbP hmbP hmbC
  obtain ⟨Ω, E, k, horder, hΩb, hEb, hE0, hΩk⟩ :=
    D13Unified.Ch21.SmoothJordan.order_components_by_index γc hPM hjump
  rcases horder with ⟨hΩ, hE, hk⟩ | ⟨hΩ, hE, hk⟩
  · subst Ω E k
    exact ⟨P, M, N, hPM, hPo, hMo, hPc, hMc, hΩb, hEb, hPf, hMf,
      hNopen, hCN, hE0, Or.inl ⟨hlocalP, hΩk⟩⟩
  · subst Ω E k
    exact ⟨M, P, N, D13Unified.Ch21.SmoothJordan.twoComponents_swap hPM,
      hMo, hPo, hMc, hPc, hΩb, hEb, hMf, hPf, hNopen, hCN, hE0,
      Or.inr ⟨hlocalP, hΩk⟩⟩

end
end PlanarThinCollar






namespace SmoothManifolds.ClassicalBoundaryResults.PlanarLoopBridge
open SmoothManifolds.ClassicalBoundaryResults
open ModelData AtlasData MapData TangentData DifferentialData EmbeddedData
  MapClassData RegularDomainData BoundaryData BoundaryConeData
  BoundaryOrientationData ClassicalBoundaryData OrientationData Set Module
open FrameData Filter ExteriorData
open scoped Topology
open Specs.D13Unified.Ch21.Collar


@[simp] theorem planeComplexEquiv_re (v : Euclidean 2) : (planeComplexEquiv v).re = v 0 := rfl
@[simp] theorem planeComplexEquiv_im (v : Euclidean 2) : (planeComplexEquiv v).im = v 1 := rfl

@[simp] theorem planeComplexEquiv_det (u v : Euclidean 2) :
    det (planeComplexEquiv u) (planeComplexEquiv v) = (Matrix.of ![u, v]).det := by
  simp [det, Matrix.det_fin_two]


/-- Exact ray hypotheses needed by the local Jordan/index bridge, derived from
one actual intrinsic positive loop velocity in the source's ambient plane. -/
theorem complex_collar_rays_of_intrinsic_positive
    (T : SmoothManifold 2 .euclidean (Euclidean 2))
    (hT : euclideanChart 2 ∈ T.smoothStructure.val)
    (D : Set (Euclidean 2)) (S : SmoothManifold 2 .halfSpace D)
    (hD : IsRegularDomain T D S)
    (B : SmoothManifold 1 .euclidean (intrinsicBoundary S)) (hB : IsNaturalBoundary S B)
    (o : Orientation S) (b : Orientation B) (hb : IsInducedOrientation o b)
    (p : intrinsicBoundary S)
    (J : TangentSpace S p.val ≃ₗ[ℝ] Euclidean 2)
    (hJ : IsEuclideanDifferential S T Subtype.val p.val J.toLinearMap)
    (K : TangentSpace B p →ₗ[ℝ] TangentSpace S p.val)
    (hK : IsDifferential B S Subtype.val p K)
    (ν : Euclidean 2) (hout : IsOutward S p (J.symm ν))
    (hstandard : ∀ η : DeterminantLine S p.val,
      IsPositive (o.val p.val) η ↔
        0 < standardAmbientDet 2 (exteriorPower.map 2 J.toLinearMap η))
    (w : TangentSpace B p)
    (hpositive : IsPositive (b.val p) (exteriorPower.ιMulti ℝ 1 ![w]))
    (γ v : Circle → ℂ) (a : ℝ) (hc : IsCollar γ v a)
    (hpoint : γ (q 0) = planeComplexEquiv p.val.val)
    (hvelocity : deriv (realLift γ) 0 = planeComplexEquiv (J (K w))) :
    (∀ᶠ r in 𝓝[>] (0 : ℝ), γ (q 0) + r • v (q 0) ∈ interior (planeComplexEquiv '' D)) ∧
    (∀ᶠ r in 𝓝[>] (0 : ℝ), γ (q 0) + (-r) • v (q 0) ∉ planeComplexEquiv '' D) := by
  let v' := planeComplexEquiv.symm (v (q 0))
  have hleft : 0 < (Matrix.of ![J (K w), v']).det := by
    rw [← planeComplexEquiv_det]
    have hh := hc.2.2.1 0
    rw [hvelocity] at hh
    simpa only [v', ContinuousLinearEquiv.apply_symm_apply] using hh
  obtain ⟨hin, hout⟩ := regular_domain_positive_boundary_transverse_rays
    T hT D S hD B hB o b hb p J hJ K hK ν hout hstandard w hpositive v' hleft
  have himage (r : ℝ) : planeComplexEquiv (p.val.val + r • v') =
      γ (q 0) + r • v (q 0) := by
    simp only [map_add, map_smul, v', ContinuousLinearEquiv.apply_symm_apply, hpoint]
  constructor
  · filter_upwards [hin] with r hr
    have hmap : planeComplexEquiv '' interior D = interior (planeComplexEquiv '' D) :=
      planeComplexEquiv.toHomeomorph.image_interior D
    exact hmap ▸ (show γ (q 0) + r • v (q 0) ∈ planeComplexEquiv '' interior D from
      ⟨p.val.val + r • v', hr, himage r⟩)
  · filter_upwards [hout] with r hr
    rintro ⟨z, hz, hze⟩
    have heq : z = p.val.val + (-r) • v' :=
      planeComplexEquiv.injective (hze.trans (himage (-r)).symm)
    exact hr (heq ▸ hz)


open Specs.D13Unified.Ch21.SmoothJordan
open Specs.D13Unified.Ch21.IndexProperties (index circleLoop)

/-- Full local-domain/Jordan/index conclusion for an actual positively oriented
regular parametrization whose trace is an isolated actual boundary component.
All parametrization and velocity data here must be concluded by the existence
construction; this is the final conditional bridge. -/
theorem regular_positive_boundary_loop_jordan
    (T : SmoothManifold 2 .euclidean (Euclidean 2))
    (hT : euclideanChart 2 ∈ T.smoothStructure.val)
    (D : Set (Euclidean 2)) (S : SmoothManifold 2 .halfSpace D)
    (hD : IsRegularDomain T D S) (hclosed : IsClosed D)
    (B : SmoothManifold 1 .euclidean (intrinsicBoundary S)) (hB : IsNaturalBoundary S B)
    (o : Orientation S) (b : Orientation B) (hb : IsInducedOrientation o b)
    (J : (p : D) → TangentSpace S p ≃ₗ[ℝ] Euclidean 2)
    (hJ : ∀ p, IsEuclideanDifferential S T Subtype.val p (J p).toLinearMap)
    (K : (p : intrinsicBoundary S) → TangentSpace B p →ₗ[ℝ] TangentSpace S p.val)
    (hK : ∀ p, IsDifferential B S Subtype.val p (K p))
    (ν : intrinsicBoundary S → Euclidean 2)
    (hout : ∀ p, IsOutward S p ((J p.val).symm (ν p)))
    (hstandard : ∀ p (η : DeterminantLine S p),
      IsPositive (o.val p) η ↔
        0 < standardAmbientDet 2 (exteriorPower.map 2 (J p).toLinearMap η))
    (C : Set (Euclidean 2)) (hCfront : C ⊆ frontier D)
    (hother : IsClosed (frontier D \ C))
    (γ : Circle → ℂ) (hγ : RegularEmbeddedLoop γ)
    (htrace : range γ = planeComplexEquiv '' C)
    (hvelocity : ∃ (p : intrinsicBoundary S) (w : TangentSpace B p),
      γ (q 0) = planeComplexEquiv p.val.val ∧
      deriv (realLift γ) 0 = planeComplexEquiv (J p.val (K p w)) ∧
      IsPositive (b.val p) (exteriorPower.ιMulti ℝ 1 ![w])) :
    ∃ Ω E N : Set ℂ,
      TwoComponents (planeComplexEquiv '' C)ᶜ Ω E ∧
      IsOpen Ω ∧ IsOpen E ∧ IsPathConnected Ω ∧ IsPathConnected E ∧
      Bornology.IsBounded Ω ∧ ¬ Bornology.IsBounded E ∧
      frontier Ω = planeComplexEquiv '' C ∧ frontier E = planeComplexEquiv '' C ∧
      IsOpen N ∧ planeComplexEquiv '' C ⊆ N ∧
      (∀ z ∈ E, index (circleLoop (regularLoopMap γ hγ)) z = 0) ∧
      ((planeComplexEquiv '' D ∩ N = N ∩ closure Ω ∧
        ∀ z ∈ Ω, index (circleLoop (regularLoopMap γ hγ)) z = 1) ∨
       (planeComplexEquiv '' D ∩ N = N ∩ closure E ∧
        ∀ z ∈ Ω, index (circleLoop (regularLoopMap γ hγ)) z = -1)) := by
  obtain ⟨v, a, hc⟩ := D13Unified.Ch21.Collar.collar_exists γ hγ
  obtain ⟨p, w, hpoint, hvel, hpos⟩ := hvelocity
  obtain ⟨hinray, houtray⟩ := complex_collar_rays_of_intrinsic_positive
    T hT D S hD B hB o b hb p (J p.val) (hJ p.val) (K p) (hK p)
    (ν p) (hout p) (hstandard p.val) w hpos γ v a hc hpoint hvel
  have hclosed' : IsClosed (planeComplexEquiv '' D) :=
    planeComplexEquiv.toHomeomorph.isClosedMap D hclosed
  have hfrontier : planeComplexEquiv '' frontier D = frontier (planeComplexEquiv '' D) :=
    planeComplexEquiv.toHomeomorph.image_frontier D
  have htracefront : range γ ⊆ frontier (planeComplexEquiv '' D) := by
    rw [htrace, ← hfrontier]
    exact Set.image_mono hCfront
  have hother' : IsClosed (frontier (planeComplexEquiv '' D) \ range γ) := by
    have heq : planeComplexEquiv '' (frontier D \ C) =
        frontier (planeComplexEquiv '' D) \ range γ := by
      rw [Set.image_sdiff planeComplexEquiv.injective, hfrontier, htrace]
    exact heq ▸ planeComplexEquiv.toHomeomorph.isClosedMap (frontier D \ C) hother
  have hresult := PlanarThinCollar.local_jordan_domain_and_signed_index γ hγ hc
    hclosed' htracefront hother' hinray houtray
  simpa only [htrace] using hresult

end SmoothManifolds.ClassicalBoundaryResults.PlanarLoopBridge




namespace SmoothManifolds.ClassicalBoundaryResults
open ModelData AtlasData MapData TangentData DifferentialData EmbeddedData
  MapClassData RegularDomainData BoundaryData BoundaryOrientationData
  ClassicalBoundaryData OrientationData ExteriorData Set Module
open Specs.D13Unified.Ch21.Collar
open scoped Topology

set_option maxHeartbeats 1200000

/-- Each actual compact boundary component admits a regular embedded circle
with its genuine positively oriented intrinsic velocities. -/
theorem compact_boundary_component_positive_parametrization {a : ModelKind}
    (T : SmoothManifold 2 .euclidean (Euclidean 2))
    (hT : euclideanChart 2 ∈ T.smoothStructure.val)
    (D : Set (Euclidean 2)) (S : SmoothManifold 2 a D)
    (hD : IsRegularDomain T D S) (hcompact : IsCompact D)
    (B : SmoothManifold 1 .euclidean (intrinsicBoundary S)) (hB : IsNaturalBoundary S B)
    (J : (p : D) → TangentSpace S p ≃ₗ[ℝ] Euclidean 2)
    (hJ : ∀ p, IsEuclideanDifferential S T Subtype.val p (J p).toLinearMap)
    (K : (p : intrinsicBoundary S) → TangentSpace B p →ₗ[ℝ] TangentSpace S p.val)
    (hK : ∀ p, IsDifferential B S Subtype.val p (K p))
    (b : Orientation B) (F : Euclidean 2 → Euclidean 2) (hF : ContDiff ℝ 1 F)
    (hregular : ∀ p : intrinsicBoundary S, F p.val.val ≠ 0)
    (hpositive : ∀ p : intrinsicBoundary S, ∃ v : TangentSpace B p,
      J p.val (K p v) = F p.val.val ∧
        IsPositive (b.val p) (exteriorPower.ιMulti ℝ 1 ![v]))
    (p : intrinsicBoundary S) :
    let c : Euclidean 2 ≃L[ℝ] ℂ :=
      (LinearEquiv.finTwoArrow ℝ ℝ).toContinuousLinearEquiv.trans Complex.equivRealProdCLM.symm
    ∃ (T₀ : ℝ) (γ : Circle → ℂ), 0 < T₀ ∧ RegularEmbeddedLoop γ ∧
      range γ = c '' ((fun q : intrinsicBoundary S => q.val.val) '' connectedComponent p) ∧
      ∀ t : ℝ, ∃ q : intrinsicBoundary S, q ∈ connectedComponent p ∧
        q.val.val = c.symm (realLift γ t) ∧ γ (Specs.D13Unified.Ch21.Collar.q t) = c q.val.val ∧
        HasDerivAt (fun s => c.symm (realLift γ s)) (T₀ • F q.val.val) t ∧
        ∃ v : TangentSpace B q,
          IsPositive (b.val q) (exteriorPower.ιMulti ℝ 1 ![v]) ∧
          J q.val (K q v) = T₀ • F q.val.val ∧
          deriv (realLift γ) t = c (J q.val (K q v)) := by
  classical
  cases a with
  | euclidean =>
    have : False := by simpa only [intrinsicBoundary_euclidean S, Set.mem_empty_iff_false] using p.property
    exact this.elim
  | halfSpace =>
    let C := (fun q : intrinsicBoundary S => q.val.val) '' connectedComponent p
    let e : Euclidean 2 ≃L[ℝ] (ℝ × ℝ) := (LinearEquiv.finTwoArrow ℝ ℝ).toContinuousLinearEquiv
    let c : Euclidean 2 ≃L[ℝ] ℂ := e.trans Complex.equivRealProdCLM.symm
    have htangent (q : intrinsicBoundary S) : ∃ v : TangentSpace B q,
        J q.val (K q v) = F q.val.val := by
      obtain ⟨v, hv, _⟩ := hpositive q
      exact ⟨v, hv⟩
    obtain ⟨hCne, hCc, hCp, hlocal⟩ :=
      regular_domain_boundary_component_constraints
        T hT D S hD hcompact B hB J hJ K hK F htangent p
    have hCreg : ∀ x ∈ C, F x ≠ 0 := by
      rintro x ⟨q, _, rfl⟩
      exact hregular q
    obtain ⟨T₀, γ, hT₀, hγ, htrace, hd⟩ :=
      BoundaryParametrization.regular_embedded_loop_of_global_tangent_field
        e F hF hCne hCc hCp.isConnected.isPreconnected hCreg hlocal
    refine ⟨T₀, γ, hT₀, hγ, htrace, ?_⟩
    intro t
    obtain ⟨hct, hdt⟩ := hd t
    obtain ⟨q, hq, heq⟩ := hct
    change q.val.val = c.symm (realLift γ t) at heq
    obtain ⟨v₀, hv₀, hpos₀⟩ := hpositive q
    have hds : HasDerivAt (fun s => c.symm (realLift γ s)) (T₀ • F q.val.val) t := by
      simpa only [heq] using hdt
    refine ⟨q, hq, heq, ?_, hds, T₀ • v₀, ?_, ?_, ?_⟩
    · change realLift γ t = c q.val.val
      rw [heq, c.apply_symm_apply]
    · have hscale : exteriorPower.ιMulti ℝ 1 ![T₀ • v₀] =
          T₀ • exteriorPower.ιMulti ℝ 1 ![v₀] := by
        apply (exteriorPower.oneEquiv ℝ (TangentSpace B q)).injective
        simp
      obtain ⟨hne, hray⟩ := hpos₀
      rw [hscale, ← hray]
      exact (OrientationResults.positive_iff_pos_smul _ hne _).mpr ⟨T₀, hT₀, rfl⟩
    · rw [map_smul, map_smul, hv₀]
    · have hdc := c.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hds
      have hdc' : HasDerivAt (realLift γ) (c (T₀ • F q.val.val)) t := by
        simpa only [Function.comp_def, ContinuousLinearEquiv.coe_coe, c.apply_symm_apply] using hdc
      simp only [hdc'.deriv, map_smul, hv₀]
      rfl
end SmoothManifolds.ClassicalBoundaryResults


namespace SmoothManifolds.ClassicalBoundaryResults
open ModelData AtlasData MapData TangentData DifferentialData EmbeddedData
  MapClassData RegularDomainData BoundaryData BoundaryConeData
  BoundaryOrientationData ClassicalBoundaryData OrientationData Set Module
open FrameData Filter ExteriorData
open scoped Topology
open Specs.D13Unified.Ch21.Collar

/-- The actual positive boundary orientation of every compact smooth planar
domain is counterclockwise on each outer component and clockwise on each inner
component, with outer/inner defined by the actual locally occupied Jordan side
and direction measured by the genuine winding index. -/
theorem compact_planar_boundary_components :
    Specs.SmoothManifolds.Integration.ClassicalBoundaryGeometry.compact_planar_boundary_componentsType := by
  intro a T hT D S hD hcompact
  obtain ⟨B, J, K, o, b, ν, F, w, hB, hJ, ho, hb, hνsmooth, hF, hFsupport, hw⟩ :=
    planar_boundary_ambient_tangent T hT D S hD hcompact
  have hK (p : intrinsicBoundary S) : IsDifferential B S Subtype.val p (K p) := (hw p).1
  have hout (p : intrinsicBoundary S) : IsOutward S p ((J p.val).symm (ν p)) := (hw p).2.2.1
  have hnonzero (p : intrinsicBoundary S) : F p.val.val ≠ 0 := by
    obtain ⟨_, _, _, _, hunit, _, _⟩ := hw p
    intro hz
    rw [hz, zero_dotProduct] at hunit
    exact zero_ne_one hunit
  have hpositive (p : intrinsicBoundary S) : ∃ v : TangentSpace B p,
      J p.val (K p v) = F p.val.val ∧
        IsPositive (b.val p) (exteriorPower.ιMulti ℝ 1 ![v]) := by
    obtain ⟨_, _, _, _, _, hvel, hpos⟩ := hw p
    exact ⟨w p, hvel, hpos⟩
  refine ⟨B, J, K, o, b, hB, hJ, ho, hb, hK, ?_⟩
  intro p
  obtain ⟨T₀, γ, hT₀, hγ, htrace, hloop⟩ :=
    compact_boundary_component_positive_parametrization T hT D S hD hcompact B hB
      J hJ K hK b F (hF.of_le (by simp)) hnonzero hpositive p
  change range γ = planeComplexEquiv ''
    ((fun q : intrinsicBoundary S => q.val.val) '' connectedComponent p) at htrace
  refine ⟨γ, hγ, htrace, ?_, ?_⟩
  · intro t
    obtain ⟨q, hq, heq, hpoint, hds, v, hpos, hvel, hd⟩ := hloop t
    refine ⟨q, v, 1, hq, hpoint, zero_lt_one, ?_, hpos⟩
    have hder : HasDerivAt (realLift γ) (deriv (realLift γ) t) t :=
      (hγ.1.differentiable (by norm_num) t).hasDerivAt
    simpa only [one_smul, hd, planeComplexEquiv] using hder
  · cases a with
    | euclidean =>
      have hfalse := p.property
      simp only [intrinsicBoundary_euclidean S, Set.mem_empty_iff_false] at hfalse
    | halfSpace =>
      let C := (fun q : intrinsicBoundary S => q.val.val) '' connectedComponent p
      obtain ⟨_, _, _, hCfront, hother, _⟩ :=
        compact_boundary_component_isolation T D S hD hcompact B p
      have hvelocity : ∃ (q : intrinsicBoundary S) (v : TangentSpace B q),
          γ (Specs.D13Unified.Ch21.Collar.q 0) = planeComplexEquiv q.val.val ∧
          deriv (realLift γ) 0 = planeComplexEquiv (J q.val (K q v)) ∧
          IsPositive (b.val q) (exteriorPower.ιMulti ℝ 1 ![v]) := by
        obtain ⟨q, hq, heq, hpoint, hds, v, hpos, hvel, hd⟩ := hloop 0
        exact ⟨q, v, hpoint, hd, hpos⟩
      have hresult := PlanarLoopBridge.regular_positive_boundary_loop_jordan
        T hT D S hD hD.1 B hB o b hb J hJ K hK ν hout ho C hCfront
        hother.isClosed γ hγ htrace hvelocity
      simpa only [htrace] using hresult
end SmoothManifolds.ClassicalBoundaryResults
