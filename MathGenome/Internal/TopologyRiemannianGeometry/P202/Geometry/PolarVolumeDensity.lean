import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.PolarVolumeDensity
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.JacobiMatrix
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.CutPolarDomain
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.RiemannianVolume
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open scoped Topology ENNReal CompactlySupported
namespace P202.Geometry.PolarVolumeDensity
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.MaximalFlowData SmoothManifolds.DensityIntegrationData
  SmoothManifolds.DensityIntegrationResults P202.MetricData P202.ConnectionData
  P202.CurveConnectionData P202.LeviCivitaData P202.GeodesicData P202.CurvatureData
  P202.ExponentialData P202.ExponentialJacobiData P202.JacobiMatrixData
  P202.CompletenessData P202.CutTimeData P202.CutPolarData P202.PolarVolumeData
open SmoothManifolds.MetricVolumeData SmoothManifolds.MetricVolumeResults
  P202.CompleteExponentialData P202.CutCriterionData
open Set Filter MeasureTheory Module
universe u

/-- Determinant continuity applied to the derivative's slope limit. -/
theorem system_normalization : P202Specs.Geometry.PolarVolumeDensity.system_normalizationType.{u} := by
  intro n r M _ S C R I q h0 D
  have h := (D.derivatives 0 h0).1.tendsto_slope_zero_right
  simp only [zero_add, D.initial_A, sub_zero, D.initial_B] at h
  have hd := ContinuousLinearMap.continuous_det.continuousAt.tendsto.comp h
  simpa only [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_smul,
    LinearMap.det_smul, Module.finrank_pi, Module.finrank_self, mul_one,
    inv_pow, Function.comp_def, ContinuousLinearMap.toLinearMap_one, map_one,
    Fintype.card_fin, mul_comm, div_eq_mul_inv] using hd

/-- A nonvanishing continuous determinant cannot change the positive sign
fixed by its normalized initial limit. -/
private theorem positive_of_normalized_limit {r : ℕ}
    (f : ℝ → ℝ) (t : ℝ) (ht : 0 < t)
    (hcont : ContinuousOn f (Ioc 0 t))
    (hlim : Tendsto (fun s => f s / s ^ r) (𝓝[>] (0 : ℝ)) (𝓝 1))
    (hnz : ∀ s ∈ Ioc 0 t, f s ≠ 0) : 0 < f t := by
  have he : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < f s := by
    have hp := hlim.eventually (Ioi_mem_nhds (show (0:ℝ) < 1 by norm_num))
    filter_upwards [hp, self_mem_nhdsWithin] with s hs hpos
    exact ((div_pos_iff.mp hs).resolve_right
      (fun h => (not_lt_of_ge (pow_nonneg (le_of_lt hpos) r)) h.2)).1
  have hsmall : Iio t ∈ 𝓝[>] (0 : ℝ) := nhdsWithin_le_nhds (Iio_mem_nhds ht)
  have hpos : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s := self_mem_nhdsWithin
  have hex : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s ∧ s < t ∧ 0 < f s := by
    filter_upwards [hpos, hsmall, he] with s hs hst hf
    exact ⟨hs, hst, hf⟩
  obtain ⟨s, hs, hst, hspos⟩ := hex.exists
  by_contra h
  have hft : f t < 0 := lt_of_le_of_ne (le_of_not_gt h) (hnz t ⟨ht, le_rfl⟩)
  obtain ⟨a, ha, hfa⟩ := isPreconnected_Ioc.intermediate_value
    (show t ∈ Ioc 0 t from ⟨ht, le_rfl⟩)
    (show s ∈ Ioc 0 t from ⟨hs, hst.le⟩) hcont
    (show (0:ℝ) ∈ Icc (f t) (f s) from ⟨hft.le, hspos.le⟩)
  exact hnz a ha hfa

/-- The nonconjugacy needed here is supplied by the actual cut-time theorem. -/
theorem system_positive : P202Specs.Geometry.PolarVolumeDensity.system_positiveType.{u} := by
  intro n r M _ _ S g hn hc C hC R hR F hF p v D t ht htc
  let I := F.interval ⟨p, v.val⟩
  let q := F.curve ⟨p, v.val⟩
  have h0 : 0 ∈ I.carrier := (hF ⟨p, v.val⟩).1
  have hq : IsGeodesicOn S C I.carrier q := (hF ⟨p, v.val⟩).2.2.1
  obtain ⟨_, _, htI, _⟩ := CutCriterion.interior_unique_nonconjugate S g
    (by omega) hc C hC R hR F hF p v t ht htc
  have hsub : Ioc 0 t ⊆ I.carrier := by
    intro s hs
    exact I.ordConnected.out h0 htI ⟨hs.1.le, hs.2⟩
  have hcont : ContinuousOn D.A (Ioc 0 t) := by
    intro s hs
    exact (D.derivatives s (hsub hs)).1.continuousAt.continuousWithinAt
  apply positive_of_normalized_limit (r := r) (fun s => (D.A s).det) t ht
    (ContinuousLinearMap.continuous_det.comp_continuousOn hcont)
    (system_normalization S C R I q h0 D)
  intro s hs
  obtain ⟨_, _, hsI, hnc⟩ := CutCriterion.interior_unique_nonconjugate S g
    (by omega) hc C hC R hR F hF p v s hs.1
    ((ENNReal.ofReal_le_ofReal hs.2).trans_lt htc)
  have hbij := JacobiMatrix.invertible S g C hC R hR I q hq h0 D s hs.1 hsI hnc
  exact (LinearEquiv.ofBijective (D.A s).toLinearMap hbij).isUnit_det'.ne_zero


theorem exponentialJacobian_independent {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M}
    (g : RiemannianMetric S) (F : CurveFamily (Phase S)) (p : M)
    (w : TangentSpace S p) (E E' : TangentSpace S p ≃ₗ[ℝ] Euclidean n) :
    exponentialJacobian g F p w E = exponentialJacobian g F p w E' := by
  let b := fiberBasis p E
  let c := fiberBasis p E'
  let L := fiberDifferential S F p w
  let ρ := P202.VolumeData.density g (fiberExponential F p w)
  let σ := P202.VolumeData.density g p
  have hn : tupleEvaluation ρ (fun i => L (b i)) =
      |c.det b| * tupleEvaluation ρ (fun i => L (c i)) := by
    have hh := tuple_basis (fiberPullback L ρ) c b
    rw [SmoothManifolds.DensityIntegrationResults.fiber_pullback,
      SmoothManifolds.DensityIntegrationResults.fiber_pullback] at hh
    exact hh
  have hd := tuple_basis σ c b
  change tupleEvaluation ρ (fun i => L (b i)) / tupleEvaluation σ b =
    tupleEvaluation ρ (fun i => L (c i)) / tupleEvaluation σ c
  rw [hn, hd]
  have hu : IsUnit (c.det b) := @Module.Basis.isUnit_det ℝ _ (TangentSpace S p) _ _ (Fin n) _ _ c b
  have hnz : |c.det b| ≠ 0 := abs_ne_zero.mpr hu.ne_zero
  exact mul_div_mul_left _ _ hnz

theorem frame_compatibility :
    P202Specs.Geometry.PolarVolumeDensity.frame_compatibilityType.{u} := by
  intro n M _ S g C hC R hR I q hq h0 D E hD hE
  have hfield : P202Specs.Geometry.JacobiMatrix.field_representationType.{u} :=
    JacobiMatrix.field_representation
  have hpar := JacobiIVP.global_parallel_ivp C I q hq 0 h0
  let eD := LinearEquiv.ofInjective (D.frame 0) (D.frame_injective 0 h0)
  let K : Euclidean (n-1) →ₗ[ℝ] LinearMap.range (D.frame 0) :=
    (E.frame 0).codRestrict _ (fun x => (hD.2 0 h0 _).mpr
      ((hE.2 0 h0 _).mp ⟨x, rfl⟩))
  let Q' := eD.symm.toLinearMap.comp K
  have hinit' (x : Euclidean (n-1)) : D.frame 0 (Q' x) = E.frame 0 x := by
    exact LinearEquiv.ofInjective_symm_apply (D.frame 0) (h := D.frame_injective 0 h0) (K x)
  have hinj : Function.Injective Q' := by
    intro x y h
    apply E.frame_injective 0 h0
    rw [← hinit', ← hinit', h]
  let Q := LinearEquiv.ofBijective Q'
    ⟨hinj, (LinearMap.injective_iff_surjective (f := Q')).mp hinj⟩
  have hinit (x : Euclidean (n-1)) : D.frame 0 (Q x) = E.frame 0 x := hinit' x
  have hframes (t : ℝ) (ht : t ∈ I.carrier) (x : Euclidean (n-1)) :
      E.frame t x = D.frame t (Q x) := by
    obtain ⟨f, _, _, hu⟩ := hpar (E.frame 0 x)
    exact (hu (fun s => E.frame s x) rfl (E.frame_parallel x) t ht).trans
      (hu (fun s => D.frame s (Q x)) (hinit x) (D.frame_parallel (Q x)) t ht).symm
  refine ⟨Q, ?_, ?_⟩
  · intro x y
    rw [← hD.1 0 h0, hinit, hinit, hE.1 0 h0]
  intro t ht
  have hA (x : Euclidean (n-1)) : D.A t (Q x) = Q (E.A t x) := by
    obtain ⟨hDJ, hD0, hdD, huD⟩ := hfield S g C hC R hR I q hq h0 D (Q x)
    obtain ⟨hEJ, hE0, hdE, _⟩ := hfield S g C hC R hR I q hq h0 E x
    have hh := huD (fun s => E.frame s (E.A s x)) hEJ hE0 (by
      rw [hinit]
      exact hdE) t ht
    rw [hframes t ht] at hh
    exact (D.frame_injective t ht hh).symm
  refine ⟨hframes t ht, hA, ?_⟩
  have hconj : (D.A t).toLinearMap =
      Q.toLinearMap.comp ((E.A t).toLinearMap.comp Q.symm.toLinearMap) := by
    apply LinearMap.ext
    intro x
    change D.A t x = Q (E.A t (Q.symm x))
    rw [← hA, Q.apply_symm_apply]
  rw [hconj, LinearMap.det_conj]

theorem orthonormal_coordinates (r : ℕ) (B : LinearMap.BilinForm ℝ (Fin r → ℝ))
    (hs : ∀ x y, B x y = B y x) (hp : ∀ x, x ≠ 0 → 0 < B x x) :
    ∃ Q : (Fin r → ℝ) ≃ₗ[ℝ] (Fin r → ℝ),
      ∀ x y, B (Q x) (Q y) = ∑ i, x i * y i := by
  letI core : InnerProductSpace.Core ℝ (Fin r → ℝ) := {
    inner := fun x y => B x y
    conj_inner_symm := by intro x y; exact hs y x
    re_inner_nonneg := by
      intro x
      by_cases hx : x = 0
      · subst x; simp
      · exact (hp x hx).le
    add_left := by intro x y z; exact B.map_add₂ x y z
    smul_left := by intro x y a; simp
    definite := by
      intro x h
      by_contra hx
      exact (ne_of_gt (hp x hx)) h }
  letI := core.toNormedAddCommGroup
  letI := InnerProductSpace.ofCore core.toCore
  have hr : Module.finrank ℝ (Fin r → ℝ) = r := by simp
  let b : OrthonormalBasis (Fin r) ℝ (Fin r → ℝ) :=
    (stdOrthonormalBasis ℝ (Fin r → ℝ)).reindex (finCongr hr)
  let Q : (Fin r → ℝ) ≃ₗ[ℝ] (Fin r → ℝ) := b.toBasis.equivFun.symm
  refine ⟨Q, ?_⟩
  intro x y
  change inner ℝ (Q x) (Q y) = _
  have h := b.sum_inner_mul_inner (Q x) (Q y)
  rw [← h]
  apply Finset.sum_congr rfl
  intro i _
  have hx : inner ℝ (b i) (Q x) = x i := by
    have hh := b.repr_apply_apply (Q x) i
    have hc : b.toBasis.repr (Q x) i = x i := by
      change b.toBasis.equivFun (b.toBasis.equivFun.symm x) i = x i
      rw [LinearEquiv.apply_symm_apply]
    simpa only [OrthonormalBasis.coe_toBasis_repr_apply, b.repr_apply_apply] using hc
  have hy : inner ℝ (b i) (Q y) = y i := by
    have hc : b.toBasis.repr (Q y) i = y i := by
      change b.toBasis.equivFun (b.toBasis.equivFun.symm y) i = y i
      rw [LinearEquiv.apply_symm_apply]
    simpa only [OrthonormalBasis.coe_toBasis_repr_apply, b.repr_apply_apply] using hc
  change B (Q x) (b i) * B (b i) (Q y) = _
  rw [hs (Q x) (b i)]
  exact congrArg₂ (fun a b : ℝ => a * b) hx hy

section Reframing
variable {n r : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

noncomputable def reframeSystem
    {C : Connection (tangentBundle S)} {R : CurvatureTensor S}
    {I : D13Unified.OpenTimeInterval} {q : ℝ → Phase S}
    (D : JacobiSystem S C R I q r) (Q : Euclidean r ≃ₗ[ℝ] Euclidean r) :
    JacobiSystem S C R I q r := by
  let Qc := Q.toContinuousLinearEquiv
  let H := Qc.symm.conjContinuousAlgEquiv
  let Hc : Operator r →L[ℝ] Operator r := H.toLinearEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  have hH (L : Operator r) (x : Euclidean r) : Q (H L x) = L (Q x) := by
    change Qc (Qc.symm (L (Qc x))) = _
    exact Qc.apply_symm_apply _
  exact {
    frame := fun t => (D.frame t).comp Q.toLinearMap
    frame_injective := fun t ht => (D.frame_injective t ht).comp Q.injective
    frame_parallel := fun x => D.frame_parallel (Q x)
    curvature := fun t => H (D.curvature t)
    curvature_continuous := Hc.continuous.comp_continuousOn D.curvature_continuous
    curvature_eq := by
      intro t ht x
      change D.frame t (Q (H (D.curvature t) x)) = _
      rw [hH, D.curvature_eq t ht]
      rfl
    A := fun t => H (D.A t)
    B := fun t => H (D.B t)
    initial_A := by rw [D.initial_A, map_zero]
    initial_B := by rw [D.initial_B, map_one]
    derivatives := by
      intro t ht
      constructor
      · exact Hc.hasFDerivAt.comp_hasDerivAt t (D.derivatives t ht).1
      · have hh := Hc.hasFDerivAt.comp_hasDerivAt t (D.derivatives t ht).2
        change HasDerivAt (fun s => H (D.B s)) (H (-(D.curvature t * D.A t))) t at hh
        simpa only [map_neg, map_mul] using hh }

theorem frame_pairing_constant {C : Connection (tangentBundle S)} (g : RiemannianMetric S)
    (hC : IsLeviCivita g C) {R : CurvatureTensor S}
    {I : D13Unified.OpenTimeInterval} {q : ℝ → Phase S}
    (D : JacobiSystem S C R I q r) (h0 : 0 ∈ I.carrier)
    (t : ℝ) (ht : t ∈ I.carrier) (x y : Euclidean r) :
    pairing g (q t).1 (D.frame t x) (D.frame t y) =
      pairing g (q 0).1 (D.frame 0 x) (D.frame 0 y) := by
  have hd (s : ℝ) (hs : s ∈ I.carrier) :
      HasDerivAt (fun s => pairing g (q s).1 (D.frame s x) (D.frame s y)) 0 s := by
    have hh := P202.Geometry.ParallelTransport.metric_pairing_deriv C g hC.2
      (mem_univ s) uniqueDiffWithinAt_univ (D.frame_parallel x s hs) (D.frame_parallel y s hs)
    simpa only [pairing, hasDerivWithinAt_univ, map_zero,
      LinearMap.zero_apply, add_zero] using hh
  exact I.isOpen.is_const_of_deriv_eq_zero I.ordConnected.isPreconnected
    (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => (hd s hs).deriv) ht h0

end Reframing

theorem normal_frame_exists : P202Specs.Geometry.PolarVolumeDensity.normal_frame_existsType.{u} := by
  intro n M _ _ S g hn hc C hC R hR F hF p v
  let I := F.interval ⟨p, v.val⟩
  let q := F.curve ⟨p, v.val⟩
  have h0 : 0 ∈ I.carrier := (hF ⟨p, v.val⟩).1
  have hq : IsGeodesicOn S C I.carrier q := (hF ⟨p, v.val⟩).2.2.1
  have hnorm0 : tangentNorm g (q 0).1 (q 0).2 = 1 := by
    dsimp only [q]
    rw [(hF ⟨p, v.val⟩).2.1]
    exact v.property
  have hunit (t : ℝ) (ht : t ∈ I.carrier) :
      pairing g (q t).1 (q t).2 (q t).2 = 1 := by
    have hh := GeodesicIVP.speed_is_constant g C hC I q hq ht h0
    rw [hnorm0] at hh
    rw [← SmoothMetrics.tangentNorm_sq, hh]
    norm_num
  obtain ⟨D, hD⟩ := JacobiMatrix.normal_construction S g C hC R hR I q hq h0 hunit
  let B := (pairing g (q 0).1).compl₁₂ (D.frame 0) (D.frame 0)
  have hs (x y : Euclidean (n-1)) : B x y = B y x :=
    g.symmetric (q 0).1 (D.frame 0 x) (D.frame 0 y)
  have hp (x : Euclidean (n-1)) (hx : x ≠ 0) : 0 < B x x := by
    apply g.positive
    intro hh
    apply hx
    exact D.frame_injective 0 h0 (hh.trans (D.frame 0).map_zero.symm)
  obtain ⟨Q, hQ⟩ := orthonormal_coordinates (n-1) B hs hp
  refine ⟨reframeSystem D Q, ?_, ?_⟩
  · intro t ht x y
    change pairing g (q t).1 (D.frame t (Q x)) (D.frame t (Q y)) = _
    rw [frame_pairing_constant g hC D h0 t ht]
    exact hQ x y
  · intro t ht w
    constructor
    · rintro ⟨x, hx⟩
      exact (hD t ht w).mp ⟨Q x, hx⟩
    · intro hw
      obtain ⟨x, hx⟩ := (hD t ht w).mpr hw
      refine ⟨Q.symm x, ?_⟩
      change D.frame t (Q (Q.symm x)) = w
      rwa [Q.apply_symm_apply]


theorem tuple_density_gram {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (g : RiemannianMetric S) (p : M)
    (w : Fin n → TangentSpace S p) :
    tupleEvaluation (P202.VolumeData.density g p) w =
      Real.sqrt (Matrix.of (fun i j => pairing g p (w i) (w j))).det := by
  change Real.sqrt ((pairing g p).exteriorPower n
    (exteriorPower.ιMulti ℝ n w) (exteriorPower.ιMulti ℝ n w)) = _
  simp only [LinearMap.BilinForm.exteriorPower, LinearMap.comp_apply,
    exteriorPower.map_apply_ιMulti, exteriorPower.pairingDual_ιMulti_ιMulti]
  congr 1
  exact Matrix.det_transpose _

theorem tuple_density_nonneg {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (g : RiemannianMetric S) (p : M)
    (w : Fin n → TangentSpace S p) :
    0 ≤ tupleEvaluation (P202.VolumeData.density g p) w := by
  rw [tuple_density_gram]
  exact Real.sqrt_nonneg _

theorem fiberVolume_pos {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (g : RiemannianMetric S) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) : 0 < fiberVolume g p E := by
  rw [fiberVolume, tuple_density_gram]
  have hG := SmoothManifolds.MetricVolumeResults.bilinear_gram_posDef
    (V := TangentSpace S p) (n := n) (pairing g p) (g.symmetric p) (g.positive p) (fiberBasis p E)
  exact Real.sqrt_pos.mpr hG.det_pos

theorem exponentialJacobian_nonneg {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (g : RiemannianMetric S)
    (F : CurveFamily (Phase S)) (p : M) (w : TangentSpace S p)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) :
    0 ≤ exponentialJacobian g F p w E := by
  exact div_nonneg (tuple_density_nonneg g _ _) (fiberVolume_pos g p E).le

theorem truncatedDensity_nonneg {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (g : RiemannianMetric S)
    (F : CurveFamily (Phase S)) (p : M) (tv : ℝ × UnitDirection g p) :
    0 ≤ P202.PolarVolumeData.truncatedDensity g F p tv := by
  by_cases htv : tv ∈ polarDomain g F p
  · rw [P202.PolarVolumeData.truncatedDensity, Set.indicator_of_mem htv]
    exact mul_nonneg (pow_nonneg htv.1.le _) (exponentialJacobian_nonneg g F p _ _)
  · simp only [P202.PolarVolumeData.truncatedDensity, Set.indicator_of_notMem htv, le_refl]

/-- The angular differential is the actual Jacobi field; the initial and
terminal fiber identifications are kept explicit. -/
theorem normal_differential {n r : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (v : TangentSpace S p)
    (D : JacobiSystem S C R (F.interval ⟨p,v⟩) (F.curve ⟨p,v⟩) r)
    (x : Euclidean r) (t : ℝ) (ht : t ∈ (F.interval ⟨p,v⟩).carrier) :
    HEq (D.frame t (D.A t x))
      (fiberDifferential S F p (t • v)
        (t • (initialIdentification S C F hF p v).symm (D.frame 0 x))) := by
  obtain ⟨hJ,hJ0,hJd,_⟩ := JacobiMatrix.field_representation S g C hC R hR
    (F.interval ⟨p,v⟩) (F.curve ⟨p,v⟩) (hF ⟨p,v⟩).2.2.1 (hF ⟨p,v⟩).1 D x
  apply ExponentialJacobi.differential_formula S g C hC R hR F hF p v
    ((initialIdentification S C F hF p v).symm (D.frame 0 x))
    (fun s => D.frame s (D.A s x)) hJ hJ0 _ t ht
  simpa only [LinearEquiv.apply_symm_apply] using hJd

/-- Compute volume in radial and normal orthonormal coordinates. -/
theorem exponentialJacobian_in_orthonormal_frames {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (g : RiemannianMetric S)
    (F : CurveFamily (Phase S)) (p : M) (w : TangentSpace S p)
    (E : Euclidean n ≃ₗ[ℝ] TangentSpace S p)
    (H : Euclidean n ≃ₗ[ℝ] TangentSpace S (fiberExponential F p w))
    (K : Euclidean n →ₗ[ℝ] Euclidean n)
    (hE : Matrix.of (fun i j => pairing g p
      (E ((Pi.basisFun ℝ (Fin n)) i)) (E ((Pi.basisFun ℝ (Fin n)) j))) = 1)
    (hH : Matrix.of (fun i j => pairing g (fiberExponential F p w)
      (H ((Pi.basisFun ℝ (Fin n)) i)) (H ((Pi.basisFun ℝ (Fin n)) j))) = 1)
    (hK : ∀ x, fiberDifferential S F p w (E x) = H (K x)) :
    exponentialJacobian g F p w E.symm = |K.det| := by
  let b := (Pi.basisFun ℝ (Fin n)).map E
  let c := (Pi.basisFun ℝ (Fin n)).map H
  have hb : tupleEvaluation (P202.VolumeData.density g p) b = 1 := by
    rw [tuple_density_gram]
    change Real.sqrt (Matrix.of (fun i j => pairing g p
      (E ((Pi.basisFun ℝ (Fin n)) i)) (E ((Pi.basisFun ℝ (Fin n)) j)))).det = 1
    rw [hE]
    simp
  have hc : tupleEvaluation (P202.VolumeData.density g (fiberExponential F p w)) c = 1 := by
    rw [tuple_density_gram]
    change Real.sqrt (Matrix.of (fun i j => pairing g (fiberExponential F p w)
      (H ((Pi.basisFun ℝ (Fin n)) i)) (H ((Pi.basisFun ℝ (Fin n)) j)))).det = 1
    rw [hH]
    simp
  have hdet : c.det (fun i => fiberDifferential S F p w (b i)) = K.det := by
    dsimp only [c]
    rw [Basis.det_map]
    have heq : (H.symm ∘ fun i => fiberDifferential S F p w (b i)) =
        K ∘ (Pi.basisFun ℝ (Fin n)) := by
      funext i
      change H.symm (fiberDifferential S F p w (E ((Pi.basisFun ℝ (Fin n)) i))) = _
      rw [hK, H.symm_apply_apply]
      rfl
    rw [heq, Basis.det_comp, Basis.det_self, mul_one]
  change tupleEvaluation (P202.VolumeData.density g (fiberExponential F p w))
    (fun i => fiberDifferential S F p w (b i)) / tupleEvaluation (P202.VolumeData.density g p) b = _
  rw [tuple_basis _ c, hdet, hc, hb, mul_one, div_one]

section Completion
variable {r : ℕ} {V : Type u} [AddCommGroup V] [Module ℝ V]
def radialFrame (v : V) (N : (Fin r → ℝ) →ₗ[ℝ] V) :
    (ℝ × (Fin r → ℝ)) →ₗ[ℝ] V :=
  (LinearMap.smulRight (LinearMap.fst ℝ ℝ (Fin r → ℝ)) v) +
    N.comp (LinearMap.snd ℝ ℝ (Fin r → ℝ))

theorem radialFrame_bijective (B : LinearMap.BilinForm ℝ V)
    (v : V) (N : (Fin r → ℝ) →ₗ[ℝ] V)
    (hB : ∀ x y, B x y = B y x) (hv : B v v = 1)
    (hN : Function.Injective N)
    (hrange : ∀ w, (∃ x, N x = w) ↔ B w v = 0) :
    Function.Bijective (radialFrame v N) := by
  have horth (x : Fin r → ℝ) : B (N x) v = 0 := (hrange _).mp ⟨x,rfl⟩
  constructor
  · intro x y h
    have hfirst := congrArg (fun z => B z v) h
    change B (x.1 • v + N x.2) v = B (y.1 • v + N y.2) v at hfirst
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      horth, hv, smul_eq_mul, mul_one, add_zero] at hfirst
    apply Prod.ext hfirst
    apply hN
    change x.1 • v + N x.2 = y.1 • v + N y.2 at h
    rw [hfirst] at h
    exact add_left_cancel h
  · intro w
    have hnorm : B (w - B w v • v) v = 0 := by
      simp [map_sub, map_smul, hv]
    obtain ⟨x,hx⟩ := (hrange _).mpr hnorm
    refine ⟨(B w v,x),?_⟩
    change B w v • v + N x = w
    rw [hx]
    abel

def radialEquiv (B : LinearMap.BilinForm ℝ V)
    (v : V) (N : (Fin r → ℝ) →ₗ[ℝ] V)
    (hB : ∀ x y, B x y = B y x) (hv : B v v = 1)
    (hN : Function.Injective N)
    (hrange : ∀ w, (∃ x, N x = w) ↔ B w v = 0) :
    (Fin (r+1) → ℝ) ≃ₗ[ℝ] V :=
  (Fin.consLinearEquiv ℝ (fun _ : Fin (r+1) => ℝ)).symm.trans
    (LinearEquiv.ofBijective (radialFrame v N)
      (radialFrame_bijective B v N hB hv hN hrange))

theorem radialEquiv_pairing (B : LinearMap.BilinForm ℝ V)
    (v : V) (N : (Fin r → ℝ) →ₗ[ℝ] V)
    (hB : ∀ x y, B x y = B y x) (hv : B v v = 1)
    (hN : Function.Injective N)
    (hrange : ∀ w, (∃ x, N x = w) ↔ B w v = 0)
    (hpair : ∀ x y, B (N x) (N y) = ∑ i, x i * y i)
    (x y : Fin (r+1) → ℝ) :
    B (radialEquiv B v N hB hv hN hrange x)
      (radialEquiv B v N hB hv hN hrange y) = ∑ i, x i * y i := by
  have horth (z : Fin r → ℝ) : B (N z) v = 0 := (hrange _).mp ⟨z,rfl⟩
  change B (x 0 • v + N (Fin.tail x)) (y 0 • v + N (Fin.tail y)) = _
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, horth, hv, mul_one, mul_zero, zero_add, hB v (N _), hpair, add_zero]
  rw [Fin.sum_univ_succ, mul_comm (y 0) (x 0)]
  rfl

theorem radialEquiv_gram (B : LinearMap.BilinForm ℝ V)
    (v : V) (N : (Fin r → ℝ) →ₗ[ℝ] V)
    (hB : ∀ x y, B x y = B y x) (hv : B v v = 1)
    (hN : Function.Injective N)
    (hrange : ∀ w, (∃ x, N x = w) ↔ B w v = 0)
    (hpair : ∀ x y, B (N x) (N y) = ∑ i, x i * y i) :
    Matrix.of (fun i j =>
      B (((Pi.basisFun ℝ (Fin (r+1))).map (radialEquiv B v N hB hv hN hrange)) i)
        (((Pi.basisFun ℝ (Fin (r+1))).map (radialEquiv B v N hB hv hN hrange)) j)) = 1 := by
  ext i j
  change B (radialEquiv B v N hB hv hN hrange ((Pi.basisFun ℝ (Fin (r+1))) i))
    (radialEquiv B v N hB hv hN hrange ((Pi.basisFun ℝ (Fin (r+1))) j)) = _
  rw [radialEquiv_pairing B v N hB hv hN hrange hpair]
  simp only [Pi.basisFun_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst j
    simp [Pi.single_apply]
  · rw [Finset.sum_eq_zero]
    · simp [hij]
    · intro k hk
      by_cases hki : i = k
      · subst k; simp [Pi.single_apply, hij, Ne.symm hij]
      · simp [Pi.single_apply, hki]

def normalExtension (A : (Fin r → ℝ) →ₗ[ℝ] (Fin r → ℝ)) :
    (Fin (r+1) → ℝ) →ₗ[ℝ] (Fin (r+1) → ℝ) :=
  let C := Fin.consLinearEquiv ℝ (fun _ : Fin (r+1) => ℝ)
  C.toLinearMap.comp ((LinearMap.id.prodMap A).comp C.symm.toLinearMap)

theorem normalExtension_det (A : (Fin r → ℝ) →ₗ[ℝ] (Fin r → ℝ)) :
    LinearMap.det (normalExtension A) = LinearMap.det A := by
  unfold normalExtension
  rw [LinearMap.det_conj, LinearMap.det_prodMap, LinearMap.det_id, one_mul]

end Completion
section Radial
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}
theorem radial_differential (C : Connection (tangentBundle S))
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (v : TangentSpace S p) (t : ℝ)
    (ht : t ∈ (F.interval ⟨p,v⟩).carrier) :
    HEq (fiberDifferential S F p (t • v) v) (F.curve ⟨p,v⟩ t).2 := by
  let q := F.curve ⟨p,v⟩
  let e := (selectedChart S p).val
  have he := (selectedChart S p).property.1
  have hp := (selectedChart S p).property.2
  let E := selectedCoordinates S p
  let z := fiberExponential F p (t • v)
  let d := (selectedChart S z).val
  have hd := (selectedChart S z).property.1
  have hz := (selectedChart S z).property.2
  have hrad := ExponentialNormalCoordinates.radial_identity_at C F hF p v t ht
  have hqt : (q t).1 ∈ d.source := by rw [← hrad.2]; exact hz
  let D := selectedCoordinates S z
  let D' := (tangentStructure S).fiberCoordinates.equiv d hd (q t).1 hqt
  let f : Euclidean n → Euclidean n :=
    fun x => (d (fiberExponential F p (E.symm x))).val
  have hf : DifferentiableAt ℝ f (E (t • v)) := by
    apply (ExponentialNormalCoordinates.fiberExponential_contDiffAt
      C F hF p e he hp d hd (E (t • v))
      (by simpa only [E, selectedCoordinates, e, LinearEquiv.symm_apply_apply] using hrad.1)
      (by simpa only [E, selectedCoordinates, e, LinearEquiv.symm_apply_apply] using hz)).differentiableAt
    simp
  have hline : HasDerivAt (fun s : ℝ => s • E v) (E v) t := by
    simpa only [one_smul, id_eq] using! (hasDerivAt_id t).smul_const (E v)
  have hchain := hf.hasFDerivAt.comp_hasDerivAt_of_eq t hline (by simp only [map_smul])
  have hvel := ((hF ⟨p,v⟩).2.2.1 t ht).1
  have hder := CurveCovariantDerivative.velocity_coordinates hvel (mem_univ t) d hd hqt
  rw [hasDerivWithinAt_univ] at hder
  have heq : (fun s : ℝ => f (s • E v)) =ᶠ[𝓝 t] (fun s => (d (q s).1).val) := by
    filter_upwards [(F.interval ⟨p,v⟩).isOpen.mem_nhds ht] with s hs
    simp only [f, map_smul, LinearEquiv.symm_apply_apply]
    exact congrArg (fun a : M => (d a).val)
      (ExponentialNormalCoordinates.radial_identity_at C F hF p v s hs).2
  have hval : (fderiv ℝ f (E (t • v))) (E v) = D' (q t).2 :=
    (hchain.congr_of_eventuallyEq heq.symm).unique hder
  have hcast (a b : M) (h : a = b) (ha : a ∈ d.source) (hb : b ∈ d.source)
      (w : TangentSpace S a) :
      (tangentStructure S).fiberCoordinates.equiv d hd b hb (castTangent S h w) =
        (tangentStructure S).fiberCoordinates.equiv d hd a ha w := by
    subst b
    rfl
  have hterminal : castTangent S hrad.2 (fiberDifferential S F p (t • v) v) = (q t).2 := by
    apply D'.injective
    rw [hcast z (q t).1 hrad.2 hz hqt]
    change D (D.symm ((fderiv ℝ f (E (t • v))) (E v))) = _
    rw [D.apply_symm_apply]
    exact hval
  exact (ExponentialJacobi.castTangent_heq hrad.2 _).symm.trans (heq_of_eq hterminal)
end Radial

theorem pairing_cast_symm {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (g : RiemannianMetric S)
    {p q : M} (h : p = q) (x y : TangentSpace S q) :
    pairing g p ((castTangent S h).symm x) ((castTangent S h).symm y) =
      pairing g q x y := by
  subst q
  rfl

theorem jacobi_density : P202Specs.Geometry.PolarVolumeDensity.jacobi_densityType.{u} := by
  intro n M _ _ S g hn hc C hC R hR F hF p v D hD t ht htc
  obtain ⟨r,hr⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  subst n
  let I := F.interval ⟨p,v.val⟩
  let q := F.curve ⟨p,v.val⟩
  have h0 : 0 ∈ I.carrier := (hF ⟨p,v.val⟩).1
  have hq : IsGeodesicOn S C I.carrier q := (hF ⟨p,v.val⟩).2.2.1
  obtain ⟨_,_,htI,_⟩ := CutCriterion.interior_unique_nonconjugate S g
    (by omega) hc C hC R hR F hF p v t ht htc
  have hrad := (ExponentialNormalCoordinates.radial_identity_at C F hF p v.val t htI).2
  let A0 := initialIdentification S C F hF p v.val
  let At := castTangent S hrad
  have hunit (s : ℝ) (hs : s ∈ I.carrier) : pairing g (q s).1 (q s).2 (q s).2 = 1 := by
    have hz : tangentNorm g (q 0).1 (q 0).2 = 1 := by
      dsimp only [q]
      rw [(hF ⟨p,v.val⟩).2.1]
      exact v.property
    have hspeed := GeodesicIVP.speed_is_constant g C hC I q hq hs h0
    rw [hz] at hspeed
    rw [← SmoothMetrics.tangentNorm_sq, hspeed]
    norm_num
  have hA0v : A0.symm (q 0).2 = v.val := by
    have hgen (z : Phase S) (h : z = ⟨p,v.val⟩) :
        (castTangent S (congrArg Sigma.fst h).symm).symm z.2 = v.val := by
      subst z
      rfl
    exact hgen _ (hF ⟨p,v.val⟩).2.1
  let E0 := radialEquiv (pairing g (q 0).1) (q 0).2 (D.frame 0)
    (g.symmetric _) (hunit 0 h0) (D.frame_injective 0 h0) (hD.2 0 h0)
  let Et := radialEquiv (pairing g (q t).1) (q t).2 (D.frame t)
    (g.symmetric _) (hunit t htI) (D.frame_injective t htI) (hD.2 t htI)
  let Es := E0.trans A0.symm
  let H := Et.trans At.symm
  let L := At.toLinearMap.comp (fiberDifferential S F p (t • v.val))
  have hLrad : L v.val = (q t).2 := by
    exact eq_of_heq ((ExponentialJacobi.castTangent_heq hrad _).trans
      (radial_differential C F hF p v.val t htI))
  have hLnormal (x : Euclidean r) :
      L (A0.symm (D.frame 0 x)) = t⁻¹ • D.frame t (D.A t x) := by
    have hh : L (t • A0.symm (D.frame 0 x)) = D.frame t (D.A t x) := by
      exact eq_of_heq ((ExponentialJacobi.castTangent_heq hrad _).trans
        (normal_differential g C hC R hR F hF p v.val D x t htI).symm)
    rw [map_smul] at hh
    rw [← hh, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
  have hEs : Matrix.of (fun i j => pairing g p
      (Es ((Pi.basisFun ℝ (Fin (r+1))) i)) (Es ((Pi.basisFun ℝ (Fin (r+1))) j))) = 1 := by
    have hgram := radialEquiv_gram (pairing g (q 0).1) (q 0).2 (D.frame 0)
      (g.symmetric _) (hunit 0 h0) (D.frame_injective 0 h0) (hD.2 0 h0) (hD.1 0 h0)
    ext i j
    change pairing g p (A0.symm (E0 ((Pi.basisFun ℝ (Fin (r+1))) i)))
      (A0.symm (E0 ((Pi.basisFun ℝ (Fin (r+1))) j))) = _
    rw [show pairing g p (A0.symm (E0 ((Pi.basisFun ℝ (Fin (r+1))) i)))
      (A0.symm (E0 ((Pi.basisFun ℝ (Fin (r+1))) j))) =
      pairing g (q 0).1 (E0 ((Pi.basisFun ℝ (Fin (r+1))) i))
        (E0 ((Pi.basisFun ℝ (Fin (r+1))) j)) from
      pairing_cast_symm (S := S) g (congrArg Sigma.fst (hF ⟨p,v.val⟩).2.1).symm _ _]
    exact congrFun (congrFun hgram i) j
  have hH : Matrix.of (fun i j => pairing g (fiberExponential F p (t • v.val))
      (H ((Pi.basisFun ℝ (Fin (r+1))) i)) (H ((Pi.basisFun ℝ (Fin (r+1))) j))) = 1 := by
    have hgram := radialEquiv_gram (pairing g (q t).1) (q t).2 (D.frame t)
      (g.symmetric _) (hunit t htI) (D.frame_injective t htI) (hD.2 t htI) (hD.1 t htI)
    ext i j
    change pairing g (fiberExponential F p (t • v.val))
      (At.symm (Et ((Pi.basisFun ℝ (Fin (r+1))) i)))
      (At.symm (Et ((Pi.basisFun ℝ (Fin (r+1))) j))) = _
    rw [pairing_cast_symm]
    exact congrFun (congrFun hgram i) j
  have hK (x : Euclidean (r+1)) :
      fiberDifferential S F p (t • v.val) (Es x) =
        H (normalExtension (t⁻¹ • (D.A t).toLinearMap) x) := by
    apply At.injective
    change L (A0.symm (E0 x)) = At (At.symm (Et (normalExtension (t⁻¹ • (D.A t).toLinearMap) x)))
    rw [At.apply_symm_apply]
    change L (A0.symm (x 0 • (q 0).2 + D.frame 0 (Fin.tail x))) =
      x 0 • (q t).2 + D.frame t (t⁻¹ • D.A t (Fin.tail x))
    simp only [map_add, map_smul, hA0v, hLrad, hLnormal]
  have hJ := exponentialJacobian_in_orthonormal_frames g F p (t • v.val)
    Es H (normalExtension (t⁻¹ • (D.A t).toLinearMap)) hEs hH hK
  have hpos := system_positive S g hn hc C hC R hR F hF p v D t ht htc
  have hvalue : |LinearMap.det (normalExtension (t⁻¹ • (D.A t).toLinearMap))| =
      (t ^ r)⁻¹ * LinearMap.det (D.A t).toLinearMap := by
    rw [normalExtension_det, LinearMap.det_smul]
    simp only [Module.finrank_pi, Module.finrank_self, mul_one, Fintype.card_fin, Nat.succ_sub_one]
    rw [abs_mul, abs_pow, abs_inv, abs_of_pos ht]
    erw [abs_of_pos hpos]
    rw [inv_pow]
    rfl
  have hj : P202.PolarVolumeData.radialDensity g F p (t,v) = LinearMap.det (D.A t).toLinearMap := by
    rw [P202.PolarVolumeData.radialDensity, exponentialJacobian_independent g F p (t • v.val)
      (selectedCoordinates S p) Es.symm, hJ]
    erw [hvalue]
    change t ^ r * ((t ^ r)⁻¹ * LinearMap.det (D.A t).toLinearMap) = _
    rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ht.ne'), one_mul]
  exact ⟨hj, hj.symm ▸ hpos⟩


section DensityRegularity
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

set_option maxHeartbeats 3000000 in
/-- The scalar expression for the intrinsic Jacobian in one fixed target chart. -/
theorem exponentialJacobian_coordinates
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (w : TangentSpace S p)
    (hw : (⟨p,w⟩ : Phase S) ∈ exponentialDomain (S := S) F)
    (d : ModelChart n .euclidean M) (hd : d ∈ S.smoothStructure.val)
    (hq : fiberExponential (S := S) F p w ∈ d.source) :
    exponentialJacobian (S := S) g F p w (selectedCoordinates S p) =
      |(fderiv ℝ (fun x : Euclidean n =>
        (d (fiberExponential (S := S) F p ((selectedCoordinates S p).symm x))).val)
        (selectedCoordinates S p w)).det| *
        densityCoefficient (tangentStructure S).fiberCoordinates d hd
          ⟨fiberExponential (S := S) F p w,hq⟩ (P202.VolumeData.density (S := S) g (fiberExponential (S := S) F p w)) /
          fiberVolume (S := S) g p (selectedCoordinates S p) := by
  let K := (tangentStructure S).fiberCoordinates
  let E := selectedCoordinates S p
  let D := K.equiv d hd (fiberExponential (S := S) F p w) hq
  let b := coordinateBasis K d hd ⟨fiberExponential (S := S) F p w,hq⟩
  let L := fderiv ℝ (fun x : Euclidean n =>
    (d (fiberExponential (S := S) F p (E.symm x))).val) (E w)
  have hcoord (z : TangentSpace S p) :
      D (fiberDifferential S F p w z) = L (E z) := by
    exact ExponentialJacobi.differential_coordinates S C F hF p w hw
      (selectedChart S p).val d (selectedChart S p).property.1 hd
      (selectedChart S p).property.2 hq z
  have hdet : b.det (fun i => fiberDifferential S F p w (fiberBasis (S := S) p E i)) = L.det := by
    dsimp only [b, coordinateBasis]
    rw [Basis.det_map]
    simp only [LinearEquiv.symm_symm]
    have heq : (D ∘ fun i => fiberDifferential S F p w (fiberBasis (S := S) p E i)) =
        L ∘ (Pi.basisFun ℝ (Fin n)) := by
      funext i
      rw [Function.comp_apply, hcoord]
      simp only [fiberBasis, Basis.coe_map, Function.comp_apply, E.apply_symm_apply]
    rw [heq]
    change (Pi.basisFun ℝ (Fin n)).det
      (L.toLinearMap ∘ Pi.basisFun ℝ (Fin n)) = L.det
    rw [Basis.det_comp, Basis.det_self, mul_one]
  unfold exponentialJacobian
  rw [tuple_basis _ b, hdet]
  rfl

/-- Completeness makes the fiber exponential globally smooth, hence its unsigned
metric volume Jacobian is globally continuous in fixed linear coordinates. -/
theorem exponentialJacobian_continuous
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (hfull : FullExponentialAt (S := S) F p) :
    Continuous (fun x : Euclidean n =>
      exponentialJacobian (S := S) g F p ((selectedCoordinates S p).symm x)
        (selectedCoordinates S p)) := by
  let E := selectedCoordinates S p
  let f : Euclidean n → M := fun x => fiberExponential (S := S) F p (E.symm x)
  have hfc : Continuous f :=
    CompleteExponentialMinimizers.exponential_coordinates_continuous (S := S) C F hF p hfull E
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨d,hd,hxd⟩ := S.smoothStructure.property.1.1 (f x)
  let V := f ⁻¹' d.source
  have hV : IsOpen V := d.open_source.preimage hfc
  have hxV : x ∈ V := hxd
  let G : Euclidean n → Euclidean n := fun y => (d (f y)).val
  let K := (tangentStructure S).fiberCoordinates
  have hρ := smooth_density_continuous (P202.VolumeData.density (S := S) g)
    (metricDensity_smooth (P202.VolumeData.libraryMetric (S := S) g)) K d hd
  have hcoef : Continuous (fun y : V => densityCoefficient K d hd
      ⟨f y.val,y.property⟩ (P202.VolumeData.density (S := S) g (f y.val))) :=
    hρ.comp ((hfc.comp continuous_subtype_val).subtype_mk (fun y => y.property))
  have hdf : ContinuousOn (fun y => (fderiv ℝ G y).det) V := by
    intro y hy
    have hs := ExponentialNormalCoordinates.fiberExponential_contDiffAt_basis
      C F hF p E d hd y (hfull _) hy
    exact ContinuousLinearMap.continuous_det.continuousAt.comp
      (hs.continuousAt_fderiv (by simp)) |>.continuousWithinAt
  have hlocal : ContinuousOn (fun y =>
      exponentialJacobian (S := S) g F p (E.symm y) E) V := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hdet : Continuous (fun y : V => |(fderiv ℝ G y.val).det|) :=
      (continuousOn_iff_continuous_domRestrict.mp hdf).abs
    have hh := (hdet.mul hcoef).div_const (fiberVolume (S := S) g p E)
    apply hh.congr
    intro y
    have he := exponentialJacobian_coordinates (S := S) g C F hF p (E.symm y.val)
      (hfull _) d hd y.property
    simpa only [E, G, f, K, LinearEquiv.apply_symm_apply, Pi.mul_apply,
      Set.domRestrict_apply] using he.symm
  exact (hlocal x hxV).continuousAt (hV.mem_nhds hxV)

/-- Joint continuity follows by composing the metric exponential Jacobian
with the continuous vector map (t,v) ↦ t v. -/
theorem radialDensity_continuousOn :
    P202Specs.Geometry.PolarVolumeDensity.continuityType.{u} := by
  intro n M _ _ S g hn hc C hC R hR F hF p
  have hfull : FullExponentialAt (S := S) F p :=
    HopfRinow.full_exponential_of_geodesicallyComplete (S := S) C
      ((HopfRinow.hopf_rinow S g C hC).1.mp hc) F hF p
  let E := selectedCoordinates S p
  have hdir : Continuous (fun v : UnitDirection (S := S) g p => E v.val) := continuous_induced_dom
  have hv : Continuous (fun tv : ℝ × UnitDirection (S := S) g p => tv.1 • E tv.2.val) :=
    continuous_fst.smul (hdir.comp continuous_snd)
  have hJ := (exponentialJacobian_continuous (S := S) g C F hF p hfull).comp hv
  have hh := (continuous_fst.pow (n-1)).mul hJ
  apply hh.continuousOn.congr
  intro tv htv
  simp only [radialDensity, Function.comp_def, E, map_smul,
    LinearEquiv.symm_apply_apply] at *
  exact rfl

theorem sphere_coordinates_embedding (g : RiemannianMetric S) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) :
    Topology.IsClosedEmbedding (fun v : UnitDirection g p => E v.val) := by
  let E₀ := selectedCoordinates S p
  have hN := (CutCriterion.fiber_norm_compact_coordinates g p E).1
  have hE : Topology.IsEmbedding (fun v : UnitDirection g p => E₀ v.val) := by
    refine ⟨⟨rfl⟩, ?_⟩
    intro v w h
    exact Subtype.ext (E₀.injective h)
  have h : Topology.IsEmbedding (fun v : UnitDirection g p => E v.val) := by
    convert (E₀.symm.trans E).toContinuousLinearEquiv.toHomeomorph.isEmbedding.comp hE using 1
    funext v
    exact congrArg E (E₀.symm_apply_apply v.val).symm
  refine ⟨h, ?_⟩
  have heq : Set.range (fun v : UnitDirection g p => E v.val) =
      {x : Euclidean n | tangentNorm g p (E.symm x) = 1} := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      change tangentNorm g p (E.symm (E v.val)) = 1
      simpa only [E.symm_apply_apply] using v.property
    · intro hx
      exact ⟨⟨E.symm x, hx⟩, E.apply_symm_apply x⟩
  rw [heq]
  exact isClosed_eq hN continuous_const

theorem normalization_measurable (g : RiemannianMetric S) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) :
    Measurable (fun x : Euclidean n => (tangentNorm g p (E.symm x))⁻¹ • x) := by
  exact (CutCriterion.fiber_norm_compact_coordinates g p E).1.measurable.inv.smul measurable_id

theorem normalization_cone (g : RiemannianMetric S) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) (B : Set (UnitDirection g p)) :
    (fun x : Euclidean n => (tangentNorm g p (E.symm x))⁻¹ • x) ⁻¹'
      ((fun v : UnitDirection g p => E v.val) '' B) ∩
      {x | tangentNorm g p (E.symm x) < 1} = unitCone g p E B := by
  ext x
  let N := tangentNorm g p (E.symm x)
  constructor
  · rintro ⟨⟨v, hv, heq⟩, hx⟩
    change E v.val = N⁻¹ • x at heq
    have hpos : 0 < N := by
      have hn := SmoothMetrics.tangentNorm_nonneg g p (E.symm x)
      by_contra hnpos
      have hzero : N = 0 := le_antisymm (le_of_not_gt hnpos) hn
      have hvec : v.val = 0 := E.injective (by simpa [N, hzero] using heq)
      have hnorm := v.property
      rw [hvec, SmoothMetrics.tangentNorm_zero] at hnorm
      norm_num at hnorm
    refine ⟨N, ⟨hpos, hx⟩, v, hv, ?_⟩
    have hh := congrArg (fun y : Euclidean n => N • y) heq
    simpa only [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul] using hh.symm
  · rintro ⟨r, hr, v, hv, rfl⟩
    have hnorm : tangentNorm g p (E.symm (r • E v.val)) = r := by
      rw [map_smul, E.symm_apply_apply, SmoothMetrics.tangentNorm_smul, v.property,
        mul_one, abs_of_pos hr.1]
    refine ⟨⟨v, hv, ?_⟩, ?_⟩
    · change E v.val = (tangentNorm g p (E.symm (r • E v.val)))⁻¹ • (r • E v.val)
      rw [hnorm, smul_smul, inv_mul_cancel₀ hr.1.ne', one_smul]
    · change tangentNorm g p (E.symm (r • E v.val)) < 1
      rw [hnorm]
      exact hr.2

theorem sphere_selected_cone (g : RiemannianMetric S) (p : M)
    (B : Set (UnitDirection g p)) (hB : MeasurableSet B) :
    sphereMeasure g p B =
      ENNReal.ofReal ((n : ℝ) * fiberVolume g p (selectedCoordinates S p)) *
        volume (unitCone g p (selectedCoordinates S p) B) := by
  let E := selectedCoordinates S p
  have he := (sphere_coordinates_embedding g p E).measurableEmbedding
  change (_ • (Measure.map _ _).comap _) B = _
  rw [Measure.smul_apply, he.comap_apply, Measure.map_apply (normalization_measurable g p E)
    (he.measurableSet_image.mpr hB)]
  rw [Measure.restrict_apply ((normalization_measurable g p E) (he.measurableSet_image.mpr hB))]
  rw [normalization_cone]
  rfl

theorem fiberVolume_change (g : RiemannianMetric S) (p : M)
    (E₀ E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) :
    fiberVolume g p E =
      |LinearMap.det (E.symm.trans E₀).toLinearMap| * fiberVolume g p E₀ := by
  have hd := tuple_basis (P202.VolumeData.density g p) (fiberBasis p E₀) (fiberBasis p E)
  change fiberVolume g p E = _ at hd
  rw [hd]
  congr 2
  rw [fiberBasis, Module.Basis.det_map]
  change (Pi.basisFun ℝ (Fin n)).det
    ((E.symm.trans E₀).toLinearMap ∘ (Pi.basisFun ℝ (Fin n))) = _
  rw [Module.Basis.det_comp, Module.Basis.det_self, mul_one]

theorem cone_change (g : RiemannianMetric S) (p : M)
    (E₀ E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) (B : Set (UnitDirection g p)) :
    unitCone g p E₀ B =
      (E.symm.trans E₀).toLinearMap '' unitCone g p E B := by
  ext x
  constructor
  · rintro ⟨r, hr, v, hv, rfl⟩
    refine ⟨r • E v.val, ⟨r, hr, v, hv, rfl⟩, ?_⟩
    change E₀ (E.symm (r • E v.val)) = r • E₀ v.val
    rw [map_smul, E.symm_apply_apply, map_smul]
  · rintro ⟨y, ⟨r, hr, v, hv, rfl⟩, rfl⟩
    refine ⟨r, hr, v, hv, ?_⟩
    change E₀ (E.symm (r • E v.val)) = r • E₀ v.val
    rw [map_smul, E.symm_apply_apply, map_smul]

theorem sphere_cone (g : RiemannianMetric S) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) (B : Set (UnitDirection g p))
    (hB : MeasurableSet B) :
    sphereMeasure g p B =
      ENNReal.ofReal ((n : ℝ) * fiberVolume g p E) * volume (unitCone g p E B) := by
  rw [sphere_selected_cone g p B hB,
    cone_change g p (selectedCoordinates S p) E B,
    Measure.addHaar_image_linearMap,
    fiberVolume_change g p (selectedCoordinates S p) E]
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg n),
    ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_mul (abs_nonneg _)]
  ac_rfl

theorem sphere_finite (g : RiemannianMetric S) (p : M) :
    IsFiniteMeasure (sphereMeasure g p) := by
  let E := selectedCoordinates S p
  have hsub : unitCone g p E univ ⊆
      {x | tangentNorm g p (E.symm x) ≤ 1} := by
    rintro x ⟨r, hr, v, _, rfl⟩
    simp only [mem_ofPred_eq, map_smul, E.symm_apply_apply,
      SmoothMetrics.tangentNorm_smul, v.property, mul_one, abs_of_pos hr.1]
    exact hr.2.le
  refine ⟨?_⟩
  rw [sphere_selected_cone g p univ MeasurableSet.univ]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    ((measure_mono hsub).trans_lt
      ((CutCriterion.fiber_norm_compact_coordinates g p E).2 1).measure_lt_top)

theorem cone_univ (g : RiemannianMetric S) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) :
    unitCone g p E univ =
      {x : Euclidean n | 0 < tangentNorm g p (E.symm x) ∧
        tangentNorm g p (E.symm x) < 1} := by
  ext x
  constructor
  · rintro ⟨r, hr, v, _, rfl⟩
    simpa only [mem_ofPred_eq, mem_Ioo, map_smul, E.symm_apply_apply,
      SmoothMetrics.tangentNorm_smul, v.property, mul_one, abs_of_pos hr.1] using hr
  · intro hx
    refine ⟨tangentNorm g p (E.symm x), hx,
      CutPolarDomain.normalizedDirection g p (E.symm x) hx.1, mem_univ _, ?_⟩
    rw [← map_smul]
    simpa only [E.apply_symm_apply] using
      congrArg E (CutPolarDomain.norm_smul_normalizedDirection g p (E.symm x) hx.1).symm

theorem sphere_nonzero (g : RiemannianMetric S) (hn : 2 ≤ n) (p : M) :
    sphereMeasure g p univ ≠ 0 := by
  let E := selectedCoordinates S p
  let N : Euclidean n → ℝ := fun x => tangentNorm g p (E.symm x)
  have hN : Continuous N := (CutCriterion.fiber_norm_compact_coordinates g p E).1
  have hcone : IsOpen (unitCone g p E univ) := by
    rw [cone_univ]
    exact (isOpen_lt continuous_const hN).inter (isOpen_lt hN continuous_const)
  have hnonempty : (unitCone g p E univ).Nonempty := by
    letI : NeZero n := ⟨by omega⟩
    obtain ⟨x, hx⟩ := exists_ne (0 : Euclidean n)
    have hw : E.symm x ≠ 0 := by
      intro h
      apply hx
      simpa only [map_zero, E.apply_symm_apply] using congrArg E h
    have hpos : 0 < N x := lt_of_le_of_ne
      (SmoothMetrics.tangentNorm_nonneg g p (E.symm x))
      (fun h => hw ((SmoothMetrics.tangentNorm_eq_zero_iff g p (E.symm x)).mp h.symm))
    let v := CutPolarDomain.normalizedDirection g p (E.symm x) hpos
    exact ⟨(1 / 2 : ℝ) • E v.val, 1 / 2, by norm_num, v, mem_univ _, rfl⟩
  rw [sphere_selected_cone g p univ MeasurableSet.univ]
  exact mul_ne_zero (ne_of_gt (ENNReal.ofReal_pos.mpr
    (mul_pos (by exact_mod_cast (show 0 < n by omega)) (fiberVolume_pos g p E))))
    (hcone.measure_ne_zero volume hnonempty)

theorem sphere_measure : P202Specs.Geometry.PolarVolumeDensity.sphere_measureType.{u} := by
  intro n M _ S g hn p
  exact ⟨sphere_finite g p, sphere_nonzero g hn p, sphere_cone g p⟩
theorem orthonormal_norm_toLp (g : RiemannianMetric S) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) (hE : IsOrthonormalCoordinates g p E)
    (x : Euclidean n) :
    ‖WithLp.toLp 2 x‖ = tangentNorm g p (E.symm x) := by
  rw [EuclideanSpace.norm_eq, ExponentialNormalCoordinates.orthonormal_norm_formula g p E hE]
  simp only [Real.norm_eq_abs, sq_abs, PiLp.toLp_apply]

noncomputable def directionSphereHomeomorph (g : RiemannianMetric S) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) (hE : IsOrthonormalCoordinates g p E) :
    UnitDirection g p ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
  let e : UnitDirection g p ≃ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := {
    toFun := fun v => ⟨WithLp.toLp 2 (E v.val), by
      rw [mem_sphere_zero_iff_norm, orthonormal_norm_toLp g p E hE,
        E.symm_apply_apply]
      exact v.property⟩
    invFun := fun y => ⟨E.symm (WithLp.ofLp y.val), by
      rw [← orthonormal_norm_toLp g p E hE]
      simpa only [WithLp.toLp_ofLp, mem_sphere_zero_iff_norm] using y.property⟩
    left_inv := fun v => Subtype.ext (E.symm_apply_apply _)
    right_inv := fun y => Subtype.ext (by
      simp only [E.apply_symm_apply, WithLp.toLp_ofLp]) }
  refine ⟨e, ?_, ?_⟩
  · change Continuous (fun v : UnitDirection g p => e v)
    apply Continuous.subtype_mk
    exact (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp
      (sphere_coordinates_embedding g p E).continuous
  · apply (sphere_coordinates_embedding g p E).isInducing.continuous_iff.mpr
    change Continuous (fun y : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
      E (E.symm (WithLp.ofLp y.val)))
    have hc : Continuous (fun y : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
        WithLp.ofLp y.val) :=
      (PiLp.continuous_ofLp 2 (fun _ : Fin n => ℝ)).comp continuous_subtype_val
    simpa only [E.apply_symm_apply] using hc

open scoped Pointwise

theorem direction_cone_toLp (g : RiemannianMetric S) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) (hE : IsOrthonormalCoordinates g p E)
    (B : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) :
    unitCone g p E ((directionSphereHomeomorph g p E hE) ⁻¹' B) =
      WithLp.toLp 2 ⁻¹' (Ioo (0 : ℝ) 1 • (Subtype.val '' B)) := by
  let H := directionSphereHomeomorph g p E hE
  ext x
  constructor
  · rintro ⟨r, hr, v, hv, rfl⟩
    exact ⟨r, hr, (H v).val, ⟨H v, hv, rfl⟩, rfl⟩
  · rintro ⟨r, hr, y, ⟨v, hv, rfl⟩, heq⟩
    refine ⟨r, hr, H.symm v, ?_, ?_⟩
    · change H (H.symm v) ∈ B
      rwa [H.apply_symm_apply]
    · have hh := congrArg (@WithLp.ofLp 2 (Fin n → ℝ)) heq
      change r • WithLp.ofLp v.val = x at hh
      change x = r • E (E.symm (WithLp.ofLp v.val))
      rw [E.apply_symm_apply]
      exact hh.symm

theorem map_directionSphereHomeomorph (g : RiemannianMetric S) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) (hE : IsOrthonormalCoordinates g p E)
    (hV : fiberVolume g p E = 1) :
    Measure.map (directionSphereHomeomorph g p E hE) (sphereMeasure g p) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere := by
  ext B hB
  rw [Measure.map_apply (directionSphereHomeomorph g p E hE).measurable hB,
    sphere_cone g p E _ ((directionSphereHomeomorph g p E hE).measurable hB),
    hV, mul_one, Measure.toSphere_apply' _ hB, direction_cone_toLp g p E hE]
  rw [(PiLp.volume_preserving_toLp (Fin n)).measure_preimage_emb
    (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).symm.measurableEmbedding]
  simp only [finrank_euclideanSpace, Fintype.card_fin, ENNReal.ofReal_natCast]


theorem orthonormal_polar_measurePreserving (g : RiemannianMetric S) (hn : 0 < n) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) (hE : IsOrthonormalCoordinates g p E)
    (hV : fiberVolume g p E = 1) :
    MeasurePreserving
      (fun tv : UnitDirection g p × Ioi (0 : ℝ) => tv.2.val • E tv.1.val)
      ((sphereMeasure g p).prod (Measure.volumeIoiPow (n - 1))) volume := by
  let V := EuclideanSpace ℝ (Fin n)
  letI : NeZero n := ⟨by omega⟩
  letI := sphere_finite g p
  let H := directionSphereHomeomorph g p E hE
  have hH : MeasurePreserving H (sphereMeasure g p) (volume : Measure V).toSphere :=
    ⟨H.measurable, map_directionSphereHomeomorph g p E hE hV⟩
  have hprod := hH.prod (MeasurePreserving.id (Measure.volumeIoiPow (n - 1)))
  have hs := MeasurePreserving.symm (homeomorphUnitSphereProd V).toMeasurableEquiv
    ((volume : Measure V).measurePreserving_homeomorphUnitSphereProd)
  have hrest : (volume : Measure V).restrict ({0}ᶜ : Set V) = volume := by
    apply Measure.restrict_eq_self_of_ae_mem
    rw [ae_iff]
    simp
  have hcoe : MeasurePreserving (Subtype.val : ({0}ᶜ : Set V) → V)
      ((volume : Measure V).comap Subtype.val) volume := by
    simpa only [hrest] using
      (measurePreserving_subtype_coe (μa := (volume : Measure V))
        (measurableSet_singleton (0 : V)).compl)
  have hrad : MeasurePreserving
      (fun tv : Metric.sphere (0 : V) 1 × Ioi (0 : ℝ) => tv.2.val • tv.1.val)
      ((volume : Measure V).toSphere.prod (Measure.volumeIoiPow (n - 1))) volume := by
    simpa only [V, finrank_euclideanSpace, Fintype.card_fin, Function.comp_def,
      Homeomorph.toMeasurableEquiv_symm_coe, homeomorphUnitSphereProd_symm_apply_coe] using hcoe.comp hs
  have hcomp := (PiLp.volume_preserving_ofLp (Fin n)).comp (hrad.comp hprod)
  change MeasurePreserving
      (fun tv : UnitDirection g p × Ioi (0 : ℝ) => tv.2.val • E tv.1.val)
      ((sphereMeasure g p).prod (Measure.volumeIoiPow (n - 1))) volume at hcomp
  exact hcomp


theorem polar_measurePreserving_from_orthonormal (g : RiemannianMetric S)
    (hn : 0 < n) (p : M)
    (E₀ : TangentSpace S p ≃ₗ[ℝ] Euclidean n)
    (hE₀ : IsOrthonormalCoordinates g p E₀) (hV₀ : fiberVolume g p E₀ = 1)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) :
    MeasurePreserving
      (fun tv : UnitDirection g p × Ioi (0 : ℝ) => tv.2.val • E tv.1.val)
      ((sphereMeasure g p).prod (Measure.volumeIoiPow (n - 1)))
      (ENNReal.ofReal (fiberVolume g p E) • volume) := by
  let A := E₀.symm.trans E
  have hfv : fiberVolume g p E = |LinearMap.det A.symm.toLinearMap| := by
    simpa only [A, LinearEquiv.trans_symm, LinearEquiv.symm_symm, hV₀, mul_one] using
      fiberVolume_change g p E₀ E
  have hA : MeasurePreserving A.toLinearMap volume
      (ENNReal.ofReal (fiberVolume g p E) • volume) := by
    refine ⟨A.toContinuousLinearEquiv.continuous.measurable, ?_⟩
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume A.isUnit_det'.ne_zero]
    rw [← LinearEquiv.det_coe_symm, ← hfv]
  have hcomp := hA.comp (orthonormal_polar_measurePreserving g hn p E₀ hE₀ hV₀)
  convert hcomp using 1
  funext tv
  change tv.2.val • E tv.1.val = E (E₀.symm (tv.2.val • E₀ tv.1.val))
  rw [map_smul, E₀.symm_apply_apply, map_smul]


theorem map_volumeIoiPow (m : ℕ) :
    Measure.map (Subtype.val : Ioi (0 : ℝ) → ℝ) (Measure.volumeIoiPow m) =
      (volume.restrict (Ioi (0 : ℝ))).withDensity (fun t => ENNReal.ofReal (t ^ m)) := by
  ext B hB
  rw [Measure.map_apply measurable_subtype_coe hB, Measure.volumeIoiPow,
    withDensity_apply _ (measurable_subtype_coe hB),
    setLIntegral_subtype measurableSet_Ioi _ (fun t : ℝ => ENNReal.ofReal (t ^ m)),
    withDensity_apply _ hB, Measure.restrict_restrict hB]
  rw [Set.image_preimage_eq_inter_range, Subtype.range_coe]

theorem map_positiveRadius_product (g : RiemannianMetric S) (p : M) (m : ℕ) :
    Measure.map (Prod.map (Subtype.val : Ioi (0 : ℝ) → ℝ) id)
      ((Measure.volumeIoiPow m).prod (sphereMeasure g p)) =
      ((volume.restrict (Ioi (0 : ℝ))).prod (sphereMeasure g p)).withDensity
        (fun tv => ENNReal.ofReal (tv.1 ^ m)) := by
  letI := sphere_finite g p
  rw [← Measure.map_prod_map _ _ measurable_subtype_coe measurable_id,
    map_volumeIoiPow, Measure.map_id, prod_withDensity_left]
  exact ENNReal.measurable_ofReal.comp (measurable_id.pow_const m)


theorem polar_coordinate_map_from_orthonormal (g : RiemannianMetric S)
    (hn : 0 < n) (p : M)
    (E₀ : TangentSpace S p ≃ₗ[ℝ] Euclidean n)
    (hE₀ : IsOrthonormalCoordinates g p E₀) (hV₀ : fiberVolume g p E₀ = 1)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) :
    Measure.map (fun tv : ℝ × UnitDirection g p => tv.1 • E tv.2.val)
      (((volume.restrict (Ioi (0 : ℝ))).prod (sphereMeasure g p)).withDensity
        (fun tv => ENNReal.ofReal (tv.1 ^ (n - 1)))) =
      ENNReal.ofReal (fiberVolume g p E) • volume := by
  letI := sphere_finite g p
  have hP : Measurable (fun tv : ℝ × UnitDirection g p => tv.1 • E tv.2.val) :=
    (continuous_fst.smul ((sphere_coordinates_embedding g p E).continuous.comp
      continuous_snd)).measurable
  rw [← map_positiveRadius_product g p (n - 1), Measure.map_map hP
    (by fun_prop)]
  have hc := (polar_measurePreserving_from_orthonormal g hn p E₀ hE₀ hV₀ E).comp
    (Measure.measurePreserving_swap (μ := Measure.volumeIoiPow (n - 1)) (ν := sphereMeasure g p))
  exact hc.map_eq


theorem fiberVolume_orthonormal (g : RiemannianMetric S) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) (hE : IsOrthonormalCoordinates g p E) :
    fiberVolume g p E = 1 := by
  have hG : Matrix.of (fun i j => pairing g p (fiberBasis p E i) (fiberBasis p E j)) =
      (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    simpa only [fiberBasis, Module.Basis.map_apply, Pi.basisFun_apply,
      Matrix.of_apply, Matrix.one_apply] using hE i j
  have hd : fiberVolume g p E = Real.sqrt
      (Matrix.of (fun i j => pairing g p (fiberBasis p E i) (fiberBasis p E j))).det := by
    change Real.sqrt ((pairing g p).exteriorPower n
      (exteriorPower.ιMulti ℝ n (fiberBasis p E))
      (exteriorPower.ιMulti ℝ n (fiberBasis p E))) = _
    simp only [LinearMap.BilinForm.exteriorPower, LinearMap.comp_apply,
      exteriorPower.map_apply_ιMulti, exteriorPower.pairingDual_ιMulti_ιMulti]
    congr 1
    exact Matrix.det_transpose _
  rw [hd, hG, Matrix.det_one, Real.sqrt_one]

theorem polar_coordinate_map (g : RiemannianMetric S) (hn : 0 < n) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) :
    Measure.map (fun tv : ℝ × UnitDirection g p => tv.1 • E tv.2.val)
      (((volume.restrict (Ioi (0 : ℝ))).prod (sphereMeasure g p)).withDensity
        (fun tv => ENNReal.ofReal (tv.1 ^ (n - 1)))) =
      ENNReal.ofReal (fiberVolume g p E) • volume := by
  obtain ⟨E₀, hE₀⟩ := ExponentialNormalCoordinates.orthonormal_coordinates_exist g p
  exact polar_coordinate_map_from_orthonormal g hn p E₀ hE₀
    (fiberVolume_orthonormal g p E₀ hE₀) E


theorem polar_coordinate_map_indicator (g : RiemannianMetric S) (hn : 0 < n) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) :
    Measure.map (fun tv : ℝ × UnitDirection g p => tv.1 • E tv.2.val)
      ((volume.prod (sphereMeasure g p)).withDensity
        ((Ioi (0 : ℝ) ×ˢ univ).indicator (fun tv => ENNReal.ofReal (tv.1 ^ (n - 1))))) =
      ENNReal.ofReal (fiberVolume g p E) • volume := by
  letI := sphere_finite g p
  rw [withDensity_indicator (measurableSet_Ioi.prod MeasurableSet.univ),
    ← Measure.restrict_prod_eq_prod_univ]
  exact polar_coordinate_map g hn p E


/-- Analytic local transport through the tangent polar coordinates. The sole
geometric input is the displayed pointwise density identity. -/
theorem local_polar_transport {Y : Type*} [MeasurableSpace Y]
    (g : RiemannianMetric S) (hn : 0 < n) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n)
    (P : ℝ × UnitDirection g p → Y) (hP : Measurable P)
    (f : Euclidean n → Y) (hf : Measurable f)
    (hfactor : P = f ∘ (fun tv : ℝ × UnitDirection g p => tv.1 • E tv.2.val))
    (j : ℝ × UnitDirection g p → ℝ≥0∞) (U : Set Y) (hU : MeasurableSet U)
    (H : Euclidean n → ℝ≥0∞) (hH : Measurable H)
    (hden : ∀ tv : ℝ × UnitDirection g p,
      (P ⁻¹' U).indicator j tv =
        (Ioi (0 : ℝ) ×ˢ univ).indicator
          (fun su : ℝ × UnitDirection g p => ENNReal.ofReal (su.1 ^ (n - 1))) tv *
          ((ENNReal.ofReal (fiberVolume g p E))⁻¹ * H (tv.1 • E tv.2.val))) :
    (Measure.map P ((volume.prod (sphereMeasure g p)).withDensity j)).restrict U =
      Measure.map f (volume.withDensity H) := by
  let ν : Measure (ℝ × UnitDirection g p) := volume.prod (sphereMeasure g p)
  let a : ℝ × UnitDirection g p → ℝ≥0∞ :=
    (Ioi (0 : ℝ) ×ˢ univ).indicator (fun tv => ENNReal.ofReal (tv.1 ^ (n - 1)))
  let R : ℝ × UnitDirection g p → Euclidean n := fun tv => tv.1 • E tv.2.val
  let c := ENNReal.ofReal (fiberVolume g p E)
  let G : Euclidean n → ℝ≥0∞ := fun x => c⁻¹ * H x
  have hR : Measurable R :=
    (continuous_fst.smul ((sphere_coordinates_embedding g p E).continuous.comp
      continuous_snd)).measurable
  have ha : Measurable a :=
    (ENNReal.measurable_ofReal.comp (measurable_fst.pow_const (n - 1))).indicator
      (measurableSet_Ioi.prod MeasurableSet.univ)
  have hG : Measurable G := measurable_const.mul hH
  have hj : (P ⁻¹' U).indicator j = fun tv => a tv * G (R tv) := funext hden
  have hmap (ρ : Measure (ℝ × UnitDirection g p)) :
      Measure.map R (ρ.withDensity (G ∘ R)) =
        (Measure.map R ρ).withDensity G := by
    ext B hB
    rw [Measure.map_apply hR hB, withDensity_apply _ (hR hB), withDensity_apply _ hB,
      ← lintegral_indicator hB, lintegral_map (hG.indicator hB) hR]
    rw [← lintegral_indicator (hR hB)]
    apply lintegral_congr
    intro tv
    by_cases htv : R tv ∈ B <;> simp [htv]
  rw [Measure.restrict_map hP hU, restrict_withDensity (hP hU),
    ← withDensity_indicator (hP hU), hj]
  change Measure.map P (ν.withDensity (a * (G ∘ R))) = _
  rw [withDensity_mul ν ha (hG.comp hR), hfactor,
    ← Measure.map_map hf hR, hmap]
  change Measure.map f ((Measure.map R (ν.withDensity a)).withDensity G) = _
  rw [polar_coordinate_map_indicator g hn p E]
  congr 1
  change (c • volume).withDensity (c⁻¹ • H) = volume.withDensity H
  rw [withDensity_smul_measure, withDensity_smul _ hH, smul_smul,
    ENNReal.mul_inv_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr (fiberVolume_pos g p E)))
      ENNReal.ofReal_ne_top, one_smul]


end DensityRegularity

/-- Joint measurability follows from continuity on the open polar domain;
the extension by zero includes every finite cut endpoint. The initial limit
uses the Jacobi determinant identity and the already proved system limit. -/
theorem regularity : P202Specs.Geometry.PolarVolumeDensity.regularityType.{u} := by
  classical
  intro n M _ _ S g hn hc C hC R hR F hF p
  have hcont := radialDensity_continuousOn S g hn hc C hC R hR F hF p
  have hopen := CutPolarDomain.polar_domain_open g (by omega) hc C hC R hR F hF p
    (selectedCoordinates S p)
  have hm : Measurable (P202.PolarVolumeData.truncatedDensity g F p) := by
    exact hcont.measurable_piecewise continuousOn_const hopen.measurableSet
  refine ⟨?_, hcont, hm, ?_, ?_⟩
  · intro v
    obtain ⟨D, hD⟩ := normal_frame_exists S g hn hc C hC R hR F hF p v
    have hcpos : 0 < cutTime g F p v :=
      (CutTime.cut_time_interval S g (by omega) hc C hC F hF p v).2.1
    have hcut : ∀ᶠ t in 𝓝 (0 : ℝ), ENNReal.ofReal t < cutTime g F p v := by
      have htend : Tendsto ENNReal.ofReal (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
        simpa only [ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.tendsto (0 : ℝ)
      exact htend.eventually (Iio_mem_nhds hcpos)
    apply Filter.Tendsto.congr' ?_
      (system_normalization S C R (F.interval ⟨p, v.val⟩) (F.curve ⟨p, v.val⟩)
        (hF ⟨p, v.val⟩).1 D)
    filter_upwards [hcut.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t htc ht
    rw [(jacobi_density S g hn hc C hC R hR F hF p v D hD t ht htc).1]
  · intro tv
    exact truncatedDensity_nonneg g F p tv
  · intro w E
    exact exponentialJacobian_independent g F p w E (selectedCoordinates S p)

section PolarMeasure
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

open private chartEmbedding chartEmbedding_measurableEmbedding chartWeight measure_chart_local from MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.RiemannianVolume


theorem restrict_eq_of_locally_restrict_eq {X : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] [MeasurableSpace X]
    (μ ν : Measure X) (U : Set X)
    (hlocal : ∀ x ∈ U, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      μ.restrict V = ν.restrict V) :
    μ.restrict U = ν.restrict U := by
  classical
  choose V hVo hxV hVU heq using (fun x : U => hlocal x.val x.property)
  have hUnion : (⋃ x : U, V x) = U := by
    apply Subset.antisymm
    · exact iUnion_subset fun x => hVU x
    · intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩
  obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable V hVo
  rw [← hUnion, ← hT]
  exact Measure.restrict_biUnion_congr hTc |>.mpr (fun x _ => heq x)

/-- Truncating a nonnegative density is exactly restriction of its weighted measure. -/
theorem withDensity_indicator_real {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (U : Set X) (hU : MeasurableSet U) (j : X → ℝ) :
    ν.withDensity (fun x => ENNReal.ofReal (U.indicator j x)) =
      (ν.withDensity (fun x => ENNReal.ofReal (j x))).restrict U := by
  have he : (fun x => ENNReal.ofReal (U.indicator j x)) =
      U.indicator (fun x => ENNReal.ofReal (j x)) := by
    funext x
    by_cases hx : x ∈ U <;> simp [hx]
  rw [he, withDensity_indicator hU, ← restrict_withDensity hU]

/-- A truncated pushforward gives no mass outside the image domain. -/
theorem map_withDensity_indicator_real_restrict {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (ν : Measure X) (f : X → Y) (hf : Measurable f)
    (U : Set X) (hU : MeasurableSet U) (W : Set Y) (hW : MeasurableSet W)
    (hmap : MapsTo f U W) (j : X → ℝ) :
    (Measure.map f (ν.withDensity (fun x => ENNReal.ofReal (U.indicator j x)))).restrict W =
      Measure.map f (ν.withDensity (fun x => ENNReal.ofReal (U.indicator j x))) := by
  rw [withDensity_indicator_real ν U hU j, Measure.restrict_map hf hW,
    Measure.restrict_restrict (hf hW), inter_eq_right.mpr (show U ⊆ f ⁻¹' W from hmap)]

/-- The final global measure identity reduces to local chart identities. -/
theorem map_withDensity_eq_restrict_of_local {X Y : Type*}
    [MeasurableSpace X] [TopologicalSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y]
    (ν : Measure X) (μ : Measure Y) (f : X → Y) (hf : Measurable f)
    (U : Set X) (hU : MeasurableSet U) (W : Set Y) (hW : MeasurableSet W)
    (hmap : MapsTo f U W) (j : X → ℝ)
    (hlocal : ∀ y ∈ W, ∃ V : Set Y, IsOpen V ∧ y ∈ V ∧ V ⊆ W ∧
      (Measure.map f (ν.withDensity (fun x => ENNReal.ofReal (U.indicator j x)))).restrict V =
        μ.restrict V) :
    Measure.map f (ν.withDensity (fun x => ENNReal.ofReal (U.indicator j x))) =
      μ.restrict W := by
  exact (map_withDensity_indicator_real_restrict ν f hf U hU W hW hmap j).symm.trans
    (restrict_eq_of_locally_restrict_eq _ μ W hlocal)



theorem map_withDensity_comp {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (ν : Measure X) (f : X → Y) (hf : Measurable f)
    (g : Y → ℝ≥0∞) (hg : Measurable g) :
    Measure.map f (ν.withDensity (fun x => g (f x))) =
      (Measure.map f ν).withDensity g := by
  ext s hs
  rw [Measure.map_apply hf hs, withDensity_apply _ (hf hs), withDensity_apply _ hs,
    ← lintegral_indicator hs, lintegral_map (hg.indicator hs) hf]
  rw [← lintegral_indicator (hf hs)]
  apply lintegral_congr
  intro x
  by_cases hx : f x ∈ s <;> simp [hx]



theorem map_comap_withDensity_extend {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (ν : Measure Y) (e : X → Y) (he : MeasurableEmbedding e)
    (g : X → ℝ≥0∞) (hg : Measurable g) :
    Measure.map e ((ν.comap e).withDensity g) =
      ν.withDensity (Function.extend e g 0) := by
  let G : Y → ℝ≥0∞ := Function.extend e g 0
  have hG : Measurable G := he.measurable_extend hg measurable_const
  have hcomp : (fun x => G (e x)) = g := by
    funext x
    exact he.injective.extend_apply g 0 x
  have hind : (Set.range e).indicator G = G := by
    funext y
    by_cases hy : y ∈ Set.range e
    · simp only [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy]
      exact (Function.extend_apply' (f := e) g (0 : Y → ℝ≥0∞) y hy).symm
  calc
    Measure.map e ((ν.comap e).withDensity g) =
        (Measure.map e (ν.comap e)).withDensity G := by
      simpa only [hcomp] using map_withDensity_comp (ν.comap e) e he.measurable G hG
    _ = ν.withDensity G := by
      rw [he.map_comap, ← withDensity_indicator he.measurableSet_range, hind]


/-- The given measure in polar_measure, not a substituted measure, has the
local metric-density formula on every smooth chart. -/
theorem riemannianMeasure_chart_comap
    [MeasurableSpace M] [BorelSpace M]
    (g : RiemannianMetric S) (μ : Measure M) [μ.Regular]
    (hμ : ∀ f : CompactlySupportedContinuousMap M ℝ,
      (∫ x, f x ∂μ) = P202.VolumeData.integral g f)
    (K : SmoothManifolds.TangentBundleData.FiberCoordinates S)
    (c : ModelChart n .euclidean M) (hc : c ∈ S.smoothStructure.val) :
    μ.comap (Subtype.val : c.source → M) =
      (volume.comap (fun q : c.source => (c q.val).val)).withDensity
        (fun q => ENNReal.ofReal
          (densityCoefficient K c hc q (P202.VolumeData.density g q.val))) := by
  exact measure_chart_local g μ hμ K c hc



/-- Coordinate differential formula for every source linear equivalence,
with the target still the actual intrinsic tangent chart. -/
theorem fiberDifferential_coordinates_basis
    (C : Connection (tangentBundle S))
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (w : TangentSpace S p)
    (hw : (⟨p, w⟩ : Phase S) ∈ exponentialDomain F)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n)
    (d : ModelChart n .euclidean M) (hd : d ∈ S.smoothStructure.val)
    (hq : fiberExponential F p w ∈ d.source) (z : TangentSpace S p) :
    (tangentStructure S).fiberCoordinates.equiv d hd (fiberExponential F p w) hq
      (fiberDifferential S F p w z) =
      fderiv ℝ (fun x : Euclidean n => (d (fiberExponential F p (E.symm x))).val)
        (E w) (E z) := by
  let Es := selectedCoordinates S p
  let L := (E.symm.trans Es).toContinuousLinearEquiv
  have hL (x : Euclidean n) : L x = Es (E.symm x) := rfl
  let H : Euclidean n → Euclidean n := fun x =>
    (d (fiberExponential F p (Es.symm x))).val
  have hH : DifferentiableAt ℝ H (Es w) := by
    exact (P202.Geometry.ExponentialNormalCoordinates.fiberExponential_contDiffAt_basis
      C F hF p Es d hd (Es w)
      (by simpa only [Es.symm_apply_apply] using hw)
      (by simpa only [Es.symm_apply_apply] using hq)).differentiableAt (by simp)
  have hHL : HasFDerivAt H (fderiv ℝ H (Es w)) (L (E w)) := by
    rw [hL, E.symm_apply_apply]
    exact hH.hasFDerivAt
  have hchain : HasFDerivAt
      (fun x : Euclidean n => (d (fiberExponential F p (E.symm x))).val)
      ((fderiv ℝ H (Es w)).comp L.toContinuousLinearMap) (E w) := by
    simpa only [Function.comp_def, H, hL, Es.symm_apply_apply] using
      hHL.comp (E w) L.hasFDerivAt
  rw [hchain.fderiv]
  change _ = (fderiv ℝ H (Es w)) (L (E z))
  rw [hL, E.symm_apply_apply]
  exact P202.Geometry.ExponentialJacobi.differential_coordinates S C F hF p w hw
    (selectedChart S p).val d (selectedChart S p).property.1 hd
    (selectedChart S p).property.2 hq z

/-- In an exponential inverse chart, the ambient coordinate expression of
exp is the identity on a neighborhood of its chosen source vector. -/
theorem exponentialInverse_coordinate_germ
    (F : CurveFamily (Phase S)) (p : M) (w : TangentSpace S p)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n)
    (c : ModelChart n .euclidean M) (hinv : IsExponentialInverseAt F p w E c) :
    (fun x : Euclidean n => (c (fiberExponential F p (E.symm x))).val) =ᶠ[𝓝 (E w)]
      (fun x => x) := by
  let A : Euclidean n → ModelSpace n .euclidean := fun x => ⟨x, mem_univ x⟩
  have hA : Continuous A := continuous_id.subtype_mk _
  have ho : IsOpen (A ⁻¹' c.target) := c.open_target.preimage hA
  have hx : E w ∈ A ⁻¹' c.target := by
    have heq : A (E w) = c (fiberExponential F p w) := by
      apply Subtype.ext
      exact hinv.2.2.1.symm
    change A (E w) ∈ c.target
    rw [heq]
    exact c.map_source hinv.2.1
  filter_upwards [ho.mem_nhds hx] with x hx
  change A x ∈ c.target at hx
  rw [show E.symm x = E.symm (A x).val from rfl, hinv.2.2.2 (A x) hx]
  exact congrArg Subtype.val (c.right_inv hx)



/-- An exponential inverse chart is an inverse chart at every point of its
source; the corresponding initial vector is read from that same chart. -/
theorem exponentialInverse_at_source
    (F : CurveFamily (Phase S)) (p : M) (w : TangentSpace S p)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n)
    (c : ModelChart n .euclidean M) (hinv : IsExponentialInverseAt F p w E c)
    (y : M) (hy : y ∈ c.source) :
    IsExponentialInverseAt F p (E.symm (c y).val) E c := by
  have he : fiberExponential F p (E.symm (c y).val) = y :=
    (hinv.2.2.2 (c y) (c.map_source hy)).trans (c.left_inv hy)
  refine ⟨hinv.1, he.symm ▸ hy, ?_, hinv.2.2.2⟩
  rw [he, E.apply_symm_apply]

/-- The exponential inverse chart turns its intrinsic differential into E. -/
theorem fiberDifferential_exponentialInverse_coordinates
    (C : Connection (tangentBundle S))
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (w : TangentSpace S p)
    (hw : (⟨p, w⟩ : Phase S) ∈ exponentialDomain F)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n)
    (c : ModelChart n .euclidean M) (hinv : IsExponentialInverseAt F p w E c)
    (z : TangentSpace S p) :
    (tangentStructure S).fiberCoordinates.equiv c hinv.1 (fiberExponential F p w) hinv.2.1
      (fiberDifferential S F p w z) = E z := by
  rw [fiberDifferential_coordinates_basis C F hF p w hw E c hinv.1 hinv.2.1 z,
    (exponentialInverse_coordinate_germ F p w E c hinv).fderiv_eq, fderiv_fun_id]
  rfl

/-- In exponential inverse coordinates the dexp numerator is exactly the
intrinsic target density coefficient, for any source linear coordinates E. -/
theorem exponentialInverse_density_coefficient
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (w : TangentSpace S p)
    (hw : (⟨p, w⟩ : Phase S) ∈ exponentialDomain F)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n)
    (c : ModelChart n .euclidean M) (hinv : IsExponentialInverseAt F p w E c) :
    tupleEvaluation (P202.VolumeData.density g (fiberExponential F p w))
      (fun i => fiberDifferential S F p w (fiberBasis p E i)) =
      densityCoefficient (tangentStructure S).fiberCoordinates c hinv.1
        ⟨fiberExponential F p w, hinv.2.1⟩
        (P202.VolumeData.density g (fiberExponential F p w)) := by
  let K := (tangentStructure S).fiberCoordinates
  let D := K.equiv c hinv.1 (fiberExponential F p w) hinv.2.1
  let b := SmoothManifolds.MetricVolumeResults.coordinateBasis K c hinv.1
    ⟨fiberExponential F p w, hinv.2.1⟩
  have htuple : (fun i => fiberDifferential S F p w (fiberBasis p E i)) = b := by
    funext i
    apply D.injective
    rw [fiberDifferential_exponentialInverse_coordinates C F hF p w hw E c hinv]
    simp only [b, SmoothManifolds.MetricVolumeResults.coordinateBasis,
      fiberBasis, Module.Basis.coe_map, Function.comp_apply,
      E.apply_symm_apply, D, K, LinearEquiv.apply_symm_apply]
  exact congrArg
    (fun v : Fin n → TangentSpace S (fiberExponential F p w) =>
      tupleEvaluation (P202.VolumeData.density g (fiberExponential F p w)) v) htuple


/-- The metric Jacobian in an actual exponential inverse chart is the chart
coefficient divided by the volume of the same source coordinate basis. -/
theorem exponentialInverse_jacobian
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (w : TangentSpace S p)
    (hw : (⟨p, w⟩ : Phase S) ∈ exponentialDomain F)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n)
    (c : ModelChart n .euclidean M) (hinv : IsExponentialInverseAt F p w E c) :
    exponentialJacobian g F p w E =
      densityCoefficient (tangentStructure S).fiberCoordinates c hinv.1
        ⟨fiberExponential F p w, hinv.2.1⟩
        (P202.VolumeData.density g (fiberExponential F p w)) / fiberVolume g p E := by
  exact congrArg (fun a : ℝ => a / fiberVolume g p E)
    (exponentialInverse_density_coefficient g C F hF p w hw E c hinv)


/-- Actual Riemannian chart measure is pushed to μ by the actual exponential
inverse, expressed through its ambient source coordinates. -/
theorem exponentialInverse_pushforward_chart
    [MeasurableSpace M] [BorelSpace M]
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (hfull : FullExponentialAt F p)
    (w : TangentSpace S p) (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n)
    (c : ModelChart n .euclidean M) (hinv : IsExponentialInverseAt F p w E c)
    (μ : Measure M) [μ.Regular]
    (hμ : ∀ f : CompactlySupportedContinuousMap M ℝ,
      (∫ x, f x ∂μ) = P202.VolumeData.integral g f)
    (K : SmoothManifolds.TangentBundleData.FiberCoordinates S) :
    Measure.map (fun x : Euclidean n => fiberExponential F p (E.symm x))
      (Measure.map (fun q : c.source => (c q.val).val)
        ((volume.comap (fun q : c.source => (c q.val).val)).withDensity
          (fun q => ENNReal.ofReal
            (densityCoefficient K c hinv.1 q (P202.VolumeData.density g q.val))))) =
      μ.restrict c.source := by
  let f : Euclidean n → M := fun x => fiberExponential F p (E.symm x)
  let e : c.source → Euclidean n := fun q => (c q.val).val
  have hf : Measurable f :=
    (P202.Geometry.CompleteExponentialMinimizers.exponential_coordinates_continuous
      C F hF p hfull E).measurable
  have he : MeasurableEmbedding e := chartEmbedding_measurableEmbedding c
  rw [Measure.map_map hf he.measurable]
  have hfe : f ∘ e = (Subtype.val : c.source → M) := by
    funext q
    exact (hinv.2.2.2 (c q.val) (c.map_source q.property)).trans (c.left_inv q.property)
  change Measure.map (f ∘ e) _ = _
  rw [hfe, ← riemannianMeasure_chart_comap g μ hμ K c hinv.1,
    (MeasurableEmbedding.subtype_coe c.open_source.measurableSet).map_comap]
  simp only [Subtype.range_coe]


/-- Nonnegative chart coefficient on U, extended by zero to ambient space. -/
def chartDensityExtension
    (g : RiemannianMetric S) (K : SmoothManifolds.TangentBundleData.FiberCoordinates S)
    (c : ModelChart n .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (U : Set M) : Euclidean n → ℝ≥0∞ :=
  Function.extend (fun q : c.source => (c q.val).val)
    ((Subtype.val ⁻¹' U).indicator
      (fun q => ENNReal.ofReal (densityCoefficient K c hc q (P202.VolumeData.density g q.val)))) 0

theorem chartDensityExtension_measurable
    [MeasurableSpace M] [BorelSpace M]
    (g : RiemannianMetric S) (K : SmoothManifolds.TangentBundleData.FiberCoordinates S)
    (c : ModelChart n .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (U : Set M) (hU : MeasurableSet U) : Measurable (chartDensityExtension g K c hc U) := by
  exact (chartEmbedding_measurableEmbedding c).measurable_extend
    (((P202.Geometry.RiemannianVolume.density_properties g).2.2.1 K c hc).measurable.ennreal_ofReal.indicator
      (measurable_subtype_coe hU)) measurable_const


/-- Evaluation of the ambient chart density at an actual chart point. -/
theorem chartDensityExtension_apply
    (g : RiemannianMetric S) (K : SmoothManifolds.TangentBundleData.FiberCoordinates S)
    (c : ModelChart n .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (U : Set M) (y : M) (hy : y ∈ c.source) :
    chartDensityExtension g K c hc U (c y).val =
      (Subtype.val ⁻¹' U).indicator
        (fun q : c.source => ENNReal.ofReal
          (densityCoefficient K c hc q (P202.VolumeData.density g q.val))) ⟨y, hy⟩ := by
  let e : c.source → Euclidean n := fun q => (c q.val).val
  have he : Function.Injective e := by
    intro a b hab
    apply Subtype.ext
    apply c.injOn a.property b.property
    exact Subtype.ext hab
  exact he.extend_apply _ 0 ⟨y, hy⟩

/-- The zero-extended chart density is supported inside the ambient image of U. -/
theorem chartDensityExtension_zero_off_image
    (g : RiemannianMetric S) (K : SmoothManifolds.TangentBundleData.FiberCoordinates S)
    (c : ModelChart n .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (U : Set M) (x : Euclidean n)
    (hx : x ∉ (fun y : M => (c y).val) '' U) :
    chartDensityExtension g K c hc U x = 0 := by
  classical
  by_cases hr : ∃ q : c.source, (c q.val).val = x
  · obtain ⟨q, rfl⟩ := hr
    rw [chartDensityExtension_apply g K c hc U q.val q.property]
    apply Set.indicator_of_notMem
    intro hq
    exact hx ⟨q.val, hq, rfl⟩
  · exact Function.extend_apply' (f := fun q : c.source => (c q.val).val) _ 0 x hr

/-- The exponential inverse pushes the ambient, zero-extended chart density
on U to the actual Riemannian measure restricted to U. -/
theorem exponentialInverse_pushforward_density
    [MeasurableSpace M] [BorelSpace M]
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (hfull : FullExponentialAt F p)
    (w : TangentSpace S p) (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n)
    (c : ModelChart n .euclidean M) (hinv : IsExponentialInverseAt F p w E c)
    (μ : Measure M) [μ.Regular]
    (hμ : ∀ f : CompactlySupportedContinuousMap M ℝ,
      (∫ x, f x ∂μ) = P202.VolumeData.integral g f)
    (K : SmoothManifolds.TangentBundleData.FiberCoordinates S)
    (U : Set M) (hU : MeasurableSet U) (hUs : U ⊆ c.source) :
    Measure.map (fun x : Euclidean n => fiberExponential F p (E.symm x))
      (volume.withDensity (chartDensityExtension g K c hinv.1 U)) = μ.restrict U := by
  let f : Euclidean n → M := fun x => fiberExponential F p (E.symm x)
  let e : c.source → Euclidean n := fun q => (c q.val).val
  let W : c.source → ℝ≥0∞ := fun q => ENNReal.ofReal
    (densityCoefficient K c hinv.1 q (P202.VolumeData.density g q.val))
  have hf : Measurable f :=
    (P202.Geometry.CompleteExponentialMinimizers.exponential_coordinates_continuous
      C F hF p hfull E).measurable
  have he : MeasurableEmbedding e := chartEmbedding_measurableEmbedding c
  have hW : Measurable W :=
    ((P202.Geometry.RiemannianVolume.density_properties g).2.2.1 K c hinv.1).measurable.ennreal_ofReal
  have hpre : MeasurableSet (Subtype.val ⁻¹' U : Set c.source) := measurable_subtype_coe hU
  have hm := map_comap_withDensity_extend volume e he
    ((Subtype.val ⁻¹' U).indicator W) (hW.indicator hpre)
  change Measure.map f (volume.withDensity (Function.extend e ((Subtype.val ⁻¹' U).indicator W) 0)) = _
  rw [← hm, Measure.map_map hf he.measurable]
  have hfe : f ∘ e = (Subtype.val : c.source → M) := by
    funext q
    exact (hinv.2.2.2 (c q.val) (c.map_source q.property)).trans (c.left_inv q.property)
  rw [hfe, withDensity_indicator hpre, ← restrict_withDensity hpre]
  change Measure.map Subtype.val
    (((volume.comap e).withDensity W).restrict (Subtype.val ⁻¹' U)) = _
  rw [← riemannianMeasure_chart_comap g μ hμ K c hinv.1,
    ← Measure.restrict_map measurable_subtype_coe hU,
    (MeasurableEmbedding.subtype_coe c.open_source.measurableSet).map_comap]
  simp only [Subtype.range_coe]
  rw [Measure.restrict_restrict hU, inter_eq_left.mpr hUs]

/-- Full completeness makes the globally defined polar map continuous, even
outside the polar domain. This is useful for its Borel pushforward. -/
theorem polarMap_continuous
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (hfull : FullExponentialAt F p) :
    Continuous (polarMap g F p) := by
  let E := selectedCoordinates S p
  have hcoords : Continuous (fun tv : ℝ × UnitDirection g p => tv.1 • E tv.2.val) :=
    continuous_fst.smul
      ((P202.Geometry.CutPolarDomain.direction_coordinates_continuous g p E E).comp continuous_snd)
  have h :=
    (P202.Geometry.CompleteExponentialMinimizers.exponential_coordinates_continuous
      C F hF p hfull E).comp hcoords
  change Continuous (fun tv : ℝ × UnitDirection g p => fiberExponential F p (tv.1 • tv.2.val))
  simpa only [Function.comp_def, map_smul, E.symm_apply_apply] using h

/-- The polar source density already removes all points omitted by the
polar diffeomorphism. This uses no cut-locus nullity assertion. -/
theorem polarPushforward_restrict_regular [ConnectedSpace M]
    (g : RiemannianMetric S) (hn : 0 < n) (hc : LengthMetricComplete g)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F) (p : M) :
    letI : MeasurableSpace M := borel M
    let ν := Measure.map (polarMap g F p)
      ((volume.prod (sphereMeasure g p)).withDensity
        (fun tv => ENNReal.ofReal (truncatedDensity g F p tv)))
    ν.restrict (regularDomain g F p) = ν := by
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  have hfull : FullExponentialAt F p :=
    P202.Geometry.HopfRinow.full_exponential_of_geodesicallyComplete C
      ((P202.Geometry.HopfRinow.hopf_rinow S g C hC).1.mp hc) F hF p
  have hpolar := P202.Geometry.CutPolarDomain.polar_bijection S g hn hc C hC R hR F hF p
  exact map_withDensity_indicator_real_restrict _ _
    (polarMap_continuous g C F hF p hfull).measurable _
    (P202.Geometry.CutPolarDomain.polar_domain_open g hn hc C hC R hR F hF p
      (selectedCoordinates S p)).measurableSet _
    (P202.Geometry.CutPolarDomain.regular_domain_open g hn hc C hC R hR F hF p).measurableSet
    hpolar.1 (radialDensity g F p)

/-- It suffices to prove the actual polar identity in neighborhoods of the
regular points. The manifold's second countability supplies the countable
localization needed to assemble equality of measures. -/
theorem polar_measure_of_local [ConnectedSpace M]
    (g : RiemannianMetric S) (hn : 0 < n) (hc : LengthMetricComplete g)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F) (p : M) :
    letI : MeasurableSpace M := borel M
    ∀ μ : Measure M,
    let ν := Measure.map (polarMap g F p)
      ((volume.prod (sphereMeasure g p)).withDensity
        (fun tv => ENNReal.ofReal (truncatedDensity g F p tv)))
    (∀ y ∈ regularDomain g F p, ∃ V : Set M,
      IsOpen V ∧ y ∈ V ∧ V ⊆ regularDomain g F p ∧ ν.restrict V = μ.restrict V) →
      ν = μ.restrict (regularDomain g F p) := by
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  letI : SecondCountableTopology M := S.topologicalManifold.secondCountable
  intro μ ν hlocal
  exact (polarPushforward_restrict_regular g hn hc C hC R hR F hF p).symm.trans
    (restrict_eq_of_locally_restrict_eq ν μ _ hlocal)

theorem polar_local_coordinate_preimage
    (g : RiemannianMetric S) (F : CurveFamily (Phase S)) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n)
    (c : ModelChart n .euclidean M) (U : Set M)
    (hbij : BijOn (polarMap (S := S) g F p) (polarDomain (S := S) g F p) (regularDomain (S := S) g F p))
    (hlocal : ∀ y ∈ U, ∃ su ∈ polarDomain (S := S) g F p,
      su.1 • su.2.val = E.symm (c y).val ∧ polarMap (S := S) g F p su = y)
    (tv : ℝ × UnitDirection g p) (htv : 0 < tv.1) :
    (tv ∈ polarDomain (S := S) g F p ∧ polarMap (S := S) g F p tv ∈ U) ↔
      tv.1 • E tv.2.val ∈ (fun y : M => (c y).val) '' U := by
  constructor
  · rintro ⟨htD,hyU⟩
    obtain ⟨su,hsu,hvec,hsy⟩ := hlocal _ hyU
    have hts : tv = su := hbij.2.1 htD hsu hsy.symm
    refine ⟨polarMap (S := S) g F p tv,hyU,?_⟩
    have hv := congrArg E hvec
    simpa only [← hts, map_smul, E.apply_symm_apply] using hv.symm
  · rintro ⟨y,hyU,hy⟩
    obtain ⟨su,hsu,hvec,hsy⟩ := hlocal y hyU
    have htvec : tv.1 • tv.2.val = E.symm (c y).val := by
      apply E.injective
      simpa only [map_smul, E.apply_symm_apply] using hy.symm
    have hts : tv = su := CutPolarDomain.polar_vector_injective g p htv hsu.1
      (htvec.trans hvec.symm)
    rw [hts]
    exact ⟨hsu,hsy.symm ▸ hyU⟩

theorem chart_coordinate_image_open
    (c : ModelChart n .euclidean M) (U : Set M)
    (hU : IsOpen U) (hsub : U ⊆ c.source) :
    IsOpen ((fun y : M => (c y).val) '' U) := by
  have hc : IsOpen (c '' U) := c.isOpen_image_of_subset_source hU hsub
  have hm : IsOpen (modelSet n .euclidean) := isOpen_univ
  simpa only [image_image, Function.comp_def] using hm.isOpenMap_subtype_val (c '' U) hc

open SmoothManifolds.MetricVolumeData P202.ConnectionData P202.CompleteExponentialData P202.CutCriterionData
open MeasureTheory
open scoped ENNReal


theorem polar_local_density_identity
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (hfull : P202.CompleteExponentialData.FullExponentialAt F p)
    (w : TangentSpace S p) (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n)
    (c : ModelChart n .euclidean M) (hinv : IsExponentialInverseAt F p w E c)
    (U : Set M) (hUs : U ⊆ c.source)
    (hbij : BijOn (polarMap (S := S) g F p) (polarDomain (S := S) g F p) (regularDomain (S := S) g F p))
    (hlocal : ∀ y ∈ U, ∃ su ∈ polarDomain (S := S) g F p,
      su.1 • su.2.val = E.symm (c y).val ∧ polarMap (S := S) g F p su = y)
    (tv : ℝ × UnitDirection g p) :
    ((polarMap (S := S) g F p) ⁻¹' U).indicator
      (fun tv => ENNReal.ofReal (P202.PolarVolumeData.truncatedDensity (S := S) g F p tv)) tv =
      ((Ioi (0 : ℝ)) ×ˢ (univ : Set (UnitDirection g p))).indicator
        (fun tv => ENNReal.ofReal (tv.1 ^ (n-1))) tv *
      ((ENNReal.ofReal (fiberVolume (S := S) g p E))⁻¹ *
        chartDensityExtension (S := S) g (tangentStructure S).fiberCoordinates c hinv.1 U
          (tv.1 • E tv.2.val)) := by
  classical
  by_cases ht : 0 < tv.1
  · rw [Set.indicator_of_mem (show tv ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (UnitDirection g p)) from
      ⟨ht,mem_univ _⟩)]
    by_cases hgood : tv ∈ polarDomain (S := S) g F p ∧ polarMap (S := S) g F p tv ∈ U
    · obtain ⟨su,hsu,hvec,hsy⟩ := hlocal _ hgood.2
      have hts : tv = su := hbij.2.1 hgood.1 hsu hsy.symm
      have htvec : tv.1 • tv.2.val = E.symm (c (polarMap (S := S) g F p tv)).val := by
        simpa only [← hts] using hvec
      have hEvec : tv.1 • E tv.2.val = (c (polarMap (S := S) g F p tv)).val := by
        simpa only [map_smul,E.apply_symm_apply] using congrArg E htvec
      have htvSource : polarMap (S := S) g F p tv ∈ c.source := hUs hgood.2
      have htvInv : IsExponentialInverseAt F p (tv.1 • tv.2.val) E c := by
        rw [htvec]
        exact exponentialInverse_at_source (S := S) F p w E c hinv _ htvSource
      have hJ := exponentialInverse_jacobian (S := S) g C F hF p (tv.1 • tv.2.val)
        (hfull _) E c htvInv
      let B : ℝ := densityCoefficient (tangentStructure S).fiberCoordinates c hinv.1
        ⟨polarMap (S := S) g F p tv,htvSource⟩
        (P202.VolumeData.density (S := S) g (polarMap (S := S) g F p tv))
      have hJE : exponentialJacobian (S := S) g F p (tv.1 • tv.2.val)
          (selectedCoordinates S p) = B / fiberVolume (S := S) g p E := by
        exact (P202.Geometry.PolarVolumeDensity.exponentialJacobian_independent (S := S)
          g F p (tv.1 • tv.2.val) (selectedCoordinates S p) E).trans hJ
      let H := chartDensityExtension (S := S) g (tangentStructure S).fiberCoordinates c hinv.1 U
      have hH : H (tv.1 • E tv.2.val) = ENNReal.ofReal B := by
        calc
          H (tv.1 • E tv.2.val) = H (c (polarMap (S := S) g F p tv)).val := congrArg H hEvec
          _ = _ := chartDensityExtension_apply (S := S) g
            (tangentStructure S).fiberCoordinates c hinv.1 U _ htvSource
          _ = ENNReal.ofReal B := Set.indicator_of_mem
            (show (⟨polarMap (S := S) g F p tv,htvSource⟩ : c.source) ∈
              Subtype.val ⁻¹' U from hgood.2) _
      have hleft : ((polarMap (S := S) g F p) ⁻¹' U).indicator
          (fun su => ENNReal.ofReal (P202.PolarVolumeData.truncatedDensity (S := S) g F p su)) tv =
          ENNReal.ofReal (tv.1 ^ (n-1) * (B / fiberVolume (S := S) g p E)) := by
        rw [Set.indicator_of_mem (show tv ∈ (polarMap (S := S) g F p) ⁻¹' U from hgood.2),
          P202.PolarVolumeData.truncatedDensity, Set.indicator_of_mem hgood.1]
        exact congrArg (fun a : ℝ => ENNReal.ofReal (tv.1 ^ (n-1) * a)) hJE
      calc
        _ = ENNReal.ofReal (tv.1 ^ (n-1) * (B / fiberVolume (S := S) g p E)) := hleft
        _ = ENNReal.ofReal (tv.1 ^ (n-1)) *
            ((ENNReal.ofReal (fiberVolume (S := S) g p E))⁻¹ * ENNReal.ofReal B) := by
          rw [ENNReal.ofReal_mul (pow_nonneg ht.le _), ENNReal.ofReal_div_of_pos
            (P202.Geometry.PolarVolumeDensity.fiberVolume_pos (S := S) g p E), div_eq_mul_inv]
          ac_rfl
        _ = _ := congrArg (fun a => ENNReal.ofReal (tv.1 ^ (n-1)) *
          ((ENNReal.ofReal (fiberVolume (S := S) g p E))⁻¹ * a)) hH.symm
    · have hx : tv.1 • E tv.2.val ∉ (fun y : M => (c y).val) '' U := by
        intro hx
        exact hgood ((polar_local_coordinate_preimage (S := S) g F p E c U hbij hlocal tv ht).mpr hx)
      rw [chartDensityExtension_zero_off_image (S := S) g (tangentStructure S).fiberCoordinates c hinv.1 U _ hx,
        mul_zero, mul_zero]
      by_cases hmap : polarMap (S := S) g F p tv ∈ U
      · rw [Set.indicator_of_mem (show tv ∈ (polarMap (S := S) g F p) ⁻¹' U from hmap)]
        have hnotD : tv ∉ polarDomain (S := S) g F p := fun hd => hgood ⟨hd,hmap⟩
        simp only [P202.PolarVolumeData.truncatedDensity, Set.indicator_of_notMem hnotD,
          ENNReal.ofReal_zero]
      · exact Set.indicator_of_notMem
          (show tv ∉ (polarMap (S := S) g F p) ⁻¹' U from hmap) _
  · have hnotD : tv ∉ polarDomain (S := S) g F p := fun hd => ht hd.1
    have hnotP : tv ∉ Ioi (0 : ℝ) ×ˢ (univ : Set (UnitDirection g p)) := fun hp => ht hp.1
    rw [Set.indicator_of_notMem hnotP, zero_mul]
    by_cases hmap : tv ∈ (polarMap (S := S) g F p) ⁻¹' U
    · rw [Set.indicator_of_mem hmap, P202.PolarVolumeData.truncatedDensity,
        Set.indicator_of_notMem hnotD, ENNReal.ofReal_zero]
    · exact Set.indicator_of_notMem hmap _

/-- Exact assembly of the full measure theorem from the local scalar identity.
The identity is supplied as an ordinary proved lemma; no axiom is introduced. -/
theorem polar_measure_of_density_identity
    (hdensity : ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
      {S : SmoothManifold n .euclidean M}
      (g : RiemannianMetric S) (C : Connection (tangentBundle S))
      (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
      (p : M) (hfull : FullExponentialAt F p)
      (w : TangentSpace S p) (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n)
      (c : ModelChart n .euclidean M) (hinv : IsExponentialInverseAt F p w E c)
      (U : Set M) (hUs : U ⊆ c.source)
      (hbij : BijOn (polarMap g F p) (polarDomain g F p) (regularDomain g F p))
      (hlocal : ∀ y ∈ U, ∃ su ∈ polarDomain g F p,
        su.1 • su.2.val = E.symm (c y).val ∧ polarMap g F p su = y)
      (tv : ℝ × UnitDirection g p),
      ((polarMap g F p) ⁻¹' U).indicator
        (fun su => ENNReal.ofReal (P202.PolarVolumeData.truncatedDensity g F p su)) tv =
        (Ioi (0 : ℝ) ×ˢ (univ : Set (UnitDirection g p))).indicator
          (fun su => ENNReal.ofReal (su.1 ^ (n-1))) tv *
          ((ENNReal.ofReal (fiberVolume g p E))⁻¹ *
            chartDensityExtension g (tangentStructure S).fiberCoordinates c hinv.1 U
              (tv.1 • E tv.2.val))) :
    P202Specs.Geometry.PolarVolumeDensity.polar_measureType.{u} := by
  intro n M _ _ S g hn hc C hC R hR F hF p
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  intro μ hμ hregular _
  letI : μ.Regular := hregular
  have hnpos : 0 < n := by omega
  have hfull : FullExponentialAt F p :=
    P202.Geometry.HopfRinow.full_exponential_of_geodesicallyComplete C
      ((P202.Geometry.HopfRinow.hopf_rinow S g C hC).1.mp hc) F hF p
  have hbij := CutPolarDomain.polar_bijection S g hnpos hc C hC R hR F hF p
  have hP : Measurable (polarMap g F p) := (polarMap_continuous g C F hF p hfull).measurable
  apply polar_measure_of_local g hnpos hc C hC R hR F hF p μ
  intro y hy
  obtain ⟨w, E, c, U, _, hinv, hU, hyU, hUs, hlocal⟩ :=
    CutPolarDomain.regular_inverse_chart g hnpos hc C hC R hR F hF p y hy
  refine ⟨U, hU, hyU, (fun z hz => (hUs hz).1), ?_⟩
  let f : Euclidean n → M := fun x => fiberExponential F p (E.symm x)
  have hf : Measurable f :=
    (P202.Geometry.CompleteExponentialMinimizers.exponential_coordinates_continuous
      C F hF p hfull E).measurable
  have hfactor : polarMap g F p = f ∘ (fun tv : ℝ × UnitDirection g p => tv.1 • E tv.2.val) := by
    funext tv
    simp only [polarMap, Function.comp_def, f, ← map_smul, E.symm_apply_apply]
  have hden := hdensity g C F hF p hfull w E c hinv U (fun z hz => (hUs hz).2)
    hbij hlocal
  have htransport := local_polar_transport g hnpos p E
    (polarMap g F p) hP f hf hfactor
    (fun tv => ENNReal.ofReal (P202.PolarVolumeData.truncatedDensity g F p tv))
    U hU.measurableSet
    (chartDensityExtension g (tangentStructure S).fiberCoordinates c hinv.1 U)
    (chartDensityExtension_measurable g (tangentStructure S).fiberCoordinates c hinv.1 U hU.measurableSet)
    hden
  exact htransport.trans
    (exponentialInverse_pushforward_density g C F hF p hfull w E c hinv μ hμ
      (tangentStructure S).fiberCoordinates U hU.measurableSet (fun z hz => (hUs hz).2))

/-- The polar diffeomorphism pulls Riemannian volume back to the canonical
Jacobi density times radial Lebesgue measure and metric sphere measure. -/
theorem polar_measure : P202Specs.Geometry.PolarVolumeDensity.polar_measureType.{u} :=
  polar_measure_of_density_identity polar_local_density_identity

end PolarMeasure

/-- The frame-free density used by downstream integration statements. -/
abbrev radialDensity : P202Specs.Geometry.PolarVolumeDensity.radialDensityType.{u} :=
  P202Specs.Geometry.PolarVolumeDensity.radialDensityValue

abbrev truncatedDensity : P202Specs.Geometry.PolarVolumeDensity.radialDensityType.{u} :=
  P202Specs.Geometry.PolarVolumeDensity.truncatedDensityValue

abbrev sphereMeasure : P202Specs.Geometry.PolarVolumeDensity.sphereMeasureType.{u} :=
  P202Specs.Geometry.PolarVolumeDensity.sphereMeasureValue

end P202.Geometry.PolarVolumeDensity
