import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch07.PeriodCriterion
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.Topology
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch05.Covectors
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch07.ExteriorAlgebra
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch07.PathIntegration
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Tangent.HadamardLocal
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Examples.SpheresAndTori
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-! The period criterion, uniqueness of primitives, and the angular circle example.
The integral identities use the established path-integration theorems.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
noncomputable section

namespace SmoothManifolds.PeriodCriterion
open ModelData AtlasData PartitionData CovectorData PathIntegrationData
  TangentData BundleOperationsData PeriodData Set Filter
open scoped Topology
universe u

variable {n : ℕ} {k : ModelKind} {M : Type u} [TopologicalSpace M]

/-- A one-piece subdivision. -/
def singleSubdivision (a b : ℝ) (hab : a < b) : Subdivision a b where
  count := 1
  point i := if i = 0 then a else b
  first := by simp
  last := by simp
  increasing := by
    intro i hi j hj hij
    change 0 ≤ i ∧ i ≤ 1 at hi
    change 0 ≤ j ∧ j ≤ 1 at hj
    have hi0 : i = 0 := by omega
    have hj1 : j = 1 := by omega
    simp [hi0, hj1, hab]

/-- A smooth scalar map is piecewise smooth on every nontrivial interval. -/
theorem scalarPiecewiseSmoothOn_of_contDiff (φ : ℝ → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (a b : ℝ) (hab : a < b) :
    ScalarPiecewiseSmoothOn φ a b := by
  refine ⟨hab.le, hφ.continuous.continuousOn, singleSubdivision a b hab, ?_⟩
  intro i hi
  have hi0 : i = 0 := by change i < 1 at hi; omega
  subst i
  change ScalarSmoothOnInterval φ a b
  exact ⟨hab.le, fun _ _ =>
    ⟨univ, isOpen_univ, mem_univ _, φ, hφ.contDiffOn, fun _ _ => rfl⟩⟩

/-- Re-time any increasing interval, even a point, onto an adjacent unit interval. -/
theorem affine_reparametrization (a b r : ℝ) (hab : a ≤ b) :
    IsReparametrization (fun t => a + (b - a) * (t - r)) r (r + 1) a b := by
  let φ : ℝ → ℝ := fun t => a + (b - a) * (t - r)
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ :=
    contDiff_const.add (contDiff_const.mul (contDiff_id.sub contDiff_const))
  have hm : MonotoneOn φ (Icc r (r + 1)) := by
    intro x hx y hy hxy
    dsimp [φ]
    exact add_le_add (le_refl a) (mul_le_mul_of_nonneg_left (sub_le_sub_right hxy r)
      (sub_nonneg.mpr hab))
  refine ⟨hab, scalarPiecewiseSmoothOn_of_contDiff φ hφ r (r + 1) (by linarith), hm, ?_⟩
  simpa [φ] using hφ.continuous.continuousOn.image_Icc_of_monotoneOn
    (show r ≤ r + 1 by linarith) hm

/-- No regularity is required of a total function to traverse a singleton. -/
theorem piecewiseSmoothOn_singleton (S : SmoothManifold n k M) (γ : ℝ → M) (a : ℝ) :
    PiecewiseSmoothOn S γ a a := by
  refine ⟨le_rfl, ?_, ⟨0, fun _ => a, rfl, rfl, ?_⟩, ?_⟩
  · simpa only [Icc_self] using continuousOn_singleton γ a
  · intro i hi j hj hij
    change 0 ≤ i ∧ i ≤ 0 at hi
    change 0 ≤ j ∧ j ≤ 0 at hj
    omega
  · intro i hi
    exact (Nat.not_lt_zero i hi).elim

theorem exact_implies_zero_periods
    (hFTC : Specs.SmoothManifolds.Ch07.PathIntegration.integral_dFunctionType.{u})
    (S : SmoothManifold n k M) (α : CovectorField S) :
    Exact S α → ZeroPeriods S α := by
  rintro ⟨f, hf, rfl⟩ γ a b hγ hclosed
  rw [hFTC S f hf γ a b hγ, hclosed, sub_self]

theorem exact_implies_path_independent
    (hFTC : Specs.SmoothManifolds.Ch07.PathIntegration.integral_dFunctionType.{u})
    (S : SmoothManifold n k M) (α : CovectorField S) :
    Exact S α → PathIndependent S α := by
  rintro ⟨f, hf, rfl⟩ γ η a b c d hγ hη hstart hend
  rw [hFTC S f hf γ a b hγ, hFTC S f hf η c d hη, hstart, hend]

theorem path_independent_implies_zero_periods (S : SmoothManifold n k M)
    (α : CovectorField S) (h : PathIndependent S α) : ZeroPeriods S α := by
  intro γ a b hγ hclosed
  have hi := h γ γ a b a a hγ (piecewiseSmoothOn_singleton S γ a) rfl hclosed.symm
  simpa only [pathIntegral, intervalIntegral.integral_same] using hi

theorem zero_periods_implies_path_independent
    (hconcat : Specs.SmoothManifolds.Ch07.PathIntegration.concatenationType.{u})
    (hreparam : Specs.SmoothManifolds.Ch07.PathIntegration.reparametrizationType.{u})
    (hrev : Specs.SmoothManifolds.Ch07.PathIntegration.reversalType.{u})
    (S : SmoothManifold n k M) (C : CotangentBundle S) (α : OneForm C)
    (hzero : ZeroPeriods S α.field) : PathIndependent S α.field := by
  intro γ η a b c d hγ hη hstart hend
  let ρ : ℝ → M := reverse η c d
  have hr := hrev S C α η c d hη
  let φ : ℝ → ℝ := fun t => c + (d - c) * (t - b)
  have hp := hreparam S C α ρ φ c d b (b + 1) hr.1
    (affine_reparametrization c d b hη.1)
  have hφb : φ b = c := by simp [φ]
  have hφend : φ (b + 1) = d := by dsimp [φ]; ring
  have hρc : ρ c = η d := by simp [ρ, reverse]
  have hρd : ρ d = η c := by simp [ρ, reverse]
  have hjoin : γ b = (ρ ∘ φ) b := by simp [hφb, hρc, hend]
  have hc := hconcat S C α γ (ρ ∘ φ) a b (b + 1) hγ hp.1 hjoin
  have hclosed : concatenate γ (ρ ∘ φ) b a = concatenate γ (ρ ∘ φ) b (b + 1) := by
    have hb : ¬ b + 1 ≤ b := by linarith
    simpa [concatenate, hγ.1, hb, hφend, hρd] using hstart
  have hz := hzero (concatenate γ (ρ ∘ φ) b) a (b + 1) hc.1 hclosed
  rw [hc.2, hp.2, hr.2] at hz
  linarith

theorem locally_constant_smooth (S : SmoothManifold n k M) (f : M → ℝ)
    (hf : IsLocallyConstant f) : ScalarSmooth S.smoothStructure.val f := by
  intro p
  refine ⟨continuousAt_pi.mpr (fun _ => hf.continuous.continuousAt), ?_⟩
  intro c hc hp
  refine ⟨univ, isOpen_univ, mem_univ _, fun _ _ => f p, contDiffOn_const, ?_⟩
  filter_upwards [hf.eventually_eq p] with q hq
  exact funext (fun _ => hq.symm)

theorem locally_constant_components_statement :
    Specs.SmoothManifolds.Ch07.PeriodCriterion.locally_constant_componentsType.{u} := by
  intro n k M _ S f
  constructor
  · intro hf
    refine ⟨locally_constant_smooth S f hf, ?_⟩
    intro p q hq
    exact hf.apply_eq_of_isPreconnected isPreconnected_connectedComponent hq mem_connectedComponent
  · intro hf
    exact (IsLocallyConstant.iff_exists_open f).mpr fun p =>
      ⟨connectedComponent p, _root_.SmoothManifolds.TopologicalManifold.isOpen_connectedComponent S.topologicalManifold p,
        mem_connectedComponent, fun q hq => hf.2 p q hq⟩

theorem dFunction_sub (S : SmoothManifold n k M) (f g : M → ℝ)
    (hf : ScalarSmooth S.smoothStructure.val f) (hg : ScalarSmooth S.smoothStructure.val g)
    (hfg : ScalarSmooth S.smoothStructure.val (fun p => f p - g p)) :
    dFunction S (fun p => f p - g p) hfg = dFunction S f hf - dFunction S g hg := by
  funext p
  apply LinearMap.ext
  intro v
  change v.val (functionGerm S (fun p => f p - g p) hfg p) =
    v.val (functionGerm S f hf p) - v.val (functionGerm S g hg p)
  have hgerm : functionGerm S (fun p => f p - g p) hfg p =
      functionGerm S f hf p - functionGerm S g hg p := Subtype.ext rfl
  rw [hgerm, map_sub]

theorem locally_constant_dFunction_zero (S : SmoothManifold n k M) (f : M → ℝ)
    (hf : ScalarSmooth S.smoothStructure.val f) (hlc : IsLocallyConstant f) :
    dFunction S f hf = 0 := by
  funext p
  apply LinearMap.ext
  intro v
  have hgerm : functionGerm S f hf p = algebraMap ℝ (SmoothGerm S p) (f p) := by
    apply Subtype.ext
    exact Germ.coe_eq.mpr (hlc.eventually_eq p)
  change v.val (functionGerm S f hf p) = 0
  rw [hgerm]
  exact _root_.SmoothManifolds.derivation_kills_constants (germEvaluation S p) v (f p)

/-- Vanishing of the full intrinsic differential forces local constancy, also
at a boundary: the mean-value argument takes place in a convex relative ball. -/
theorem locally_constant_of_dFunction_zero (S : SmoothManifold n k M)
    (C : CotangentBundle S) (f : M → ℝ)
    (hf : ScalarSmooth S.smoothStructure.val f) (hdf : dFunction S f hf = 0) :
    IsLocallyConstant f := by
  apply (IsLocallyConstant.iff_eventually_eq f).mpr
  intro p
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨_, hext⟩ := (_root_.SmoothManifolds.scalarContDiffAt_iff _ _ f p).mp (hf p)
  obtain ⟨U, hU, hcpU, F, hF, heq⟩ := hext c hc hp
  obtain ⟨W, hWmem, hWopen, hpW⟩ := eventually_nhds_iff.mp heq
  have hVopen := c.isOpen_inter_preimage_symm hWopen
  obtain ⟨O, hO, hOeq⟩ := isOpen_induced_iff.mp hVopen
  have hcpO : (c p).val ∈ O := by
    have hv : c p ∈ c.target ∩ c.symm ⁻¹' W :=
      ⟨c.map_source hp, by simpa only [mem_preimage, c.left_inv hp] using hpW⟩
    rw [← hOeq] at hv
    exact hv
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (hU.inter hO) (c p).val ⟨hcpU, hcpO⟩
  let B : Set (Euclidean n) := Metric.ball (c p).val r ∩ modelSet n k
  have hBc : (c p).val ∈ B := ⟨Metric.mem_ball_self hr, (c p).property⟩
  have hBconv : Convex ℝ B := (convex_ball _ _).inter (convex_modelSet n k)
  have hBU : B ⊆ U := fun y hy => (hball hy.1).1
  have hFderiv (y : Euclidean n) (hy : y ∈ B) : fderiv ℝ F y = 0 := by
    let z : ModelSpace n k := ⟨y, hy.2⟩
    have hz : z ∈ c.target ∩ c.symm ⁻¹' W := by
      rw [← hOeq]
      exact (hball hy.1).2
    let q := c.symm z
    have hq : q ∈ c.source := c.map_target hz.1
    have hcy : c q = z := c.right_inv hz.1
    have heq_q : (fun x => F (c x).val) =ᶠ[𝓝 q] f :=
      mem_of_superset (hWopen.mem_nhds hz.2) hWmem
    have hG : GermChartExtension S q c (functionGerm S f hf q) F :=
      ⟨⟨U, hU, by simpa only [hcy] using hBU hy, hF⟩, heq_q.germ_eq⟩
    have hcoord := (_root_.SmoothManifolds.Covectors.differential_coordinates S C f hf c hc q hq F hG).1
    have hsingle (i : Fin n) : fderiv ℝ F y (Pi.single i 1) = 0 := by
      have hi := hcoord i
      rw [hdf] at hi
      simpa only [hcy, Pi.zero_apply, LinearMap.zero_apply] using hi.symm
    apply ContinuousLinearMap.ext
    intro v
    have hv : v = ∑ i : Fin n, v i • Pi.single i (1 : ℝ) := by
      ext j
      simp [Pi.single_apply]
    rw [hv, map_sum]
    simp only [map_smul, hsingle, smul_zero, Finset.sum_const_zero,
      ContinuousLinearMap.zero_apply]
  have hFat (y : Euclidean n) (hy : y ∈ B) : DifferentiableAt ℝ F y :=
    ((hF.differentiableOn (by simp)) y (hBU hy)).differentiableAt (hU.mem_nhds (hBU hy))
  have hconst : ∀ y ∈ B, F y = F (c p).val := by
    intro y hy
    have hbound := hBconv.norm_image_sub_le_of_norm_fderiv_le hFat
      (fun z hz => show ‖fderiv ℝ F z‖ ≤ (0 : ℝ) by rw [hFderiv z hz]; simp) hBc hy
    simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using hbound
  have hneigh : ∀ᶠ q in 𝓝 p, (c q).val ∈ Metric.ball (c p).val r :=
    ((continuous_subtype_val.continuousAt).comp
      (c.continuousAt hp)).eventually (Metric.ball_mem_nhds _ hr)
  filter_upwards [hneigh, heq] with q hq hqeq
  rw [← hqeq, ← heq.self_of_nhds]
  exact hconst (c q).val ⟨hq, (c q).property⟩

theorem primitive_difference_statement :
    Specs.SmoothManifolds.Ch07.PeriodCriterion.primitive_differenceType.{u} := by
  intro n k M _ S f g hf hg
  have hfg : ScalarSmooth S.smoothStructure.val (fun p => f p - g p) :=
    fun p => _root_.SmoothManifolds.ScalarContDiffAt.add (hf p)
      (_root_.SmoothManifolds.ScalarContDiffAt.neg (hg p))
  rw [← sub_eq_zero (a := dFunction S f hf), ← dFunction_sub S f g hf hg hfg]
  constructor
  · intro h
    obtain ⟨C⟩ := _root_.SmoothManifolds.BundleOperations.exists_cotangent S
    exact locally_constant_of_dFunction_zero S C _ hfg h
  · exact locally_constant_dFunction_zero S _ hfg

/-- Every one-form on a one-dimensional manifold is closed; the degree-two
fiber is zero. This assertion does not require existence of a global d operator. -/
theorem closed_in_dimension_one {M : Type u} [TopologicalSpace M]
    {k : ModelKind} (S : SmoothManifold 1 k M) (C : CotangentBundle S)
    (α : CovectorField S) :
    ExteriorDerivativeData.HasExteriorDerivative C (oneField S α) 0 := by
  intro c hc p hp
  let e := C.tangent.fiberCoordinates.equiv c hc p hp
  letI : FiniteDimensional ℝ (TangentSpace S p) :=
    FiniteDimensional.of_injective e.toLinearMap e.injective
  have hd : Module.finrank ℝ (TangentSpace S p) = 1 := by
    simpa [ModelData.Euclidean, Module.finrank_pi] using e.finrank_eq
  exact (ExteriorAlgebraResults.above_dimension (TangentSpace S p) 2
    (by rw [hd]; omega) _).symm

theorem oneForm_scalar_combination (S : SmoothManifold n k M) (C : CotangentBundle S)
    (f g : M → ℝ) (hf : ScalarSmooth S.smoothStructure.val f)
    (hg : ScalarSmooth S.smoothStructure.val g) (α β : CovectorField S)
    (hα : IsOneForm C α) (hβ : IsOneForm C β) :
    IsOneForm C (fun p => f p • α p - g p • β p) := by
  letI := (cotangentSpace C).topology
  intro p
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
  let B := (cotangentSpace C).bundle
  have hi : p ∈ B.baseSet ⟨c, hc⟩ := by rw [Covectors.cotangent_baseSet]; exact hp
  let a : M → Euclidean n := fun q => ((B.trivialization ⟨c, hc⟩) ⟨q, α q⟩).2
  let b : M → Euclidean n := fun q => ((B.trivialization ⟨c, hc⟩) ⟨q, β q⟩).2
  have ha : FrameData.VectorSmoothAt S.smoothStructure.val a p :=
    FrameData.VectorSmoothAt.comp (g := fun q => (⟨q, α q⟩ : Bundle.TotalSpace (Euclidean n) (CotangentFiber S)))
      B.totalManifold.smoothStructure.property.1.1
      (Frames.trivializationCoordinates_smoothAt B ⟨c, hc⟩ ⟨p, α p⟩ hi) (hα p)
  have hb : FrameData.VectorSmoothAt S.smoothStructure.val b p :=
    FrameData.VectorSmoothAt.comp (g := fun q => (⟨q, β q⟩ : Bundle.TotalSpace (Euclidean n) (CotangentFiber S)))
      B.totalManifold.smoothStructure.property.1.1
      (Frames.trivializationCoordinates_smoothAt B ⟨c, hc⟩ ⟨p, β p⟩ hi) (hβ p)
  have hf' : FrameData.VectorSmoothAt S.smoothStructure.val f p :=
    (scalarContDiffAt_iff _ _ _ _).mp (hf p)
  have hg' : FrameData.VectorSmoothAt S.smoothStructure.val g p :=
    (scalarContDiffAt_iff _ _ _ _).mp (hg p)
  have hv : FrameData.VectorSmoothAt S.smoothStructure.val
      (fun q => f q • a q - g q • b q) p :=
    ((hf'.prod ha).prod (hg'.prod hb)).postcomp
      ((contDiff_fst.fst.smul contDiff_fst.snd).sub (contDiff_snd.fst.smul contDiff_snd.snd))
  apply Frames.smoothAt_from_trivialization B S.smoothStructure.property.1 ⟨c, hc⟩ hi
    ((manifoldContDiff_id _ _ S.smoothStructure.property.1) p) hv (fun _ => rfl)
  filter_upwards [c.open_source.mem_nhds hp] with q hq
  ext j
  rw [Covectors.cotangent_coordinates C c hc q hq]
  simp only [Pi.sub_apply, Pi.smul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul]
  dsimp only [a, b, B]
  rw [Covectors.cotangent_coordinates C c hc q hq,
    Covectors.cotangent_coordinates C c hc q hq]

open SphereTorusData

theorem sphere_coordinate_smooth (S : SmoothManifold 1 .euclidean (Sphere 1))
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (hemisphereAtlas 1))
    (j : Fin 2) : ScalarSmooth S.smoothStructure.val (fun p => p.val j) := by
  intro p
  obtain ⟨i, s, hp⟩ := SphereTorus.hemisphere_cover 1 p
  let c := SphereTorus.hemisphereChart i s
  have hc : c ∈ S.smoothStructure.val := by
    rw [hS]
    exact subset_maximalExtension (SphereTorus.hemisphereAtlas_isContDiffAtlas 1)
      ⟨i, s, SphereTorus.hemisphereChart_spec i s⟩
  apply scalarContDiffAt_of_chart S.smoothStructure.property.1 hc hp
  refine ⟨{y | squareSum y < 1}, isOpen_lt (SphereTorus.continuous_squareSum 1) continuous_const,
    SphereTorus.hemisphere_omit_mem i s p hp, fun y => insertRoot i s y j,
    (contDiffOn_pi.mp (SphereTorus.contDiffOn_insertRoot i s)) j, ?_⟩
  filter_upwards [c.open_source.mem_nhds hp] with q hq
  exact congrFun (SphereTorus.insertRoot_omit i s q hq) j

theorem circleLoop_val_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun t => (circleLoop t).val) := by
  apply contDiff_pi.mpr
  intro j
  fin_cases j
  · simpa [circleLoop] using Real.contDiff_cos
  · simpa [circleLoop] using Real.contDiff_sin

theorem circleLoop_continuous : Continuous circleLoop :=
  circleLoop_val_smooth.continuous.subtype_mk _

theorem circleLoop_smooth_at (S : SmoothManifold 1 .euclidean (Sphere 1))
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (hemisphereAtlas 1))
    (side : CurveSide) (t : ℝ) :
    CurveSmoothAt S (circleLoop t) side (fun h => circleLoop (t + h)) := by
  have hct : Continuous (fun h : ℝ => circleLoop (t + h)) :=
    circleLoop_continuous.comp (continuous_const.add continuous_id)
  have htend : Tendsto (fun h => circleLoop (t + h)) (𝓝 0) (𝓝 (circleLoop t)) := by
    simpa only [ContinuousAt, add_zero] using hct.continuousAt (x := (0 : ℝ))
  refine ⟨by simp, ?_, ?_⟩
  · simpa only [ContinuousWithinAt, add_zero] using
      htend.mono_left (nhdsWithin_le_nhds (s := curveParameterSet side))
  · intro d hd hpd
    obtain ⟨i, s, hp⟩ := SphereTorus.hemisphere_cover 1 (circleLoop t)
    let c := SphereTorus.hemisphereChart i s
    have hc : c ∈ S.smoothStructure.val := by
      rw [hS]
      exact subset_maximalExtension (SphereTorus.hemisphereAtlas_isContDiffAtlas 1)
        ⟨i, s, SphereTorus.hemisphereChart_spec i s⟩
    obtain ⟨U, hU, hcp, G, hG, heq⟩ := chartContDiffAt_of_compatible
      (S.smoothStructure.property.1.2 c hc d hd) hp hpd
    let H : ℝ → Euclidean 1 := fun h => omitCoordinate i (circleLoop (t + h)).val
    have hH : ContDiff ℝ (⊤ : ℕ∞) H := by
      apply contDiff_pi.mpr
      intro j
      exact (contDiff_pi.mp (circleLoop_val_smooth.comp (contDiff_const.add contDiff_id)) (i.succAbove j))
    refine ⟨H ⁻¹' U, hU.preimage hH.continuous, ?_, G ∘ H,
      hG.comp hH.contDiffOn (fun _ hy => hy), ?_⟩
    · simpa [H, c, SphereTorus.hemisphereChart] using hcp
    · have h := (heq.comp_tendsto htend).symm.filter_mono
        (nhdsWithin_le_nhds (s := TangentData.curveParameterSet side))
      exact h

/-- The actual chosen velocity represents every smooth translated curve.
This follows directly from the already proved intrinsic curve construction. -/
theorem velocity_represents_smooth_curve (S : SmoothManifold n k M) (γ : ℝ → M)
    (side : CurveSide) (t : ℝ)
    (hγ : CurveSmoothAt S (γ t) side (fun h => γ (t + h))) :
    CurveRepresentsDerivation S (γ t) side (fun h => γ (t + h)) (velocity S γ side t) := by
  classical
  have hex : ∃ v, CurveRepresentsDerivation S (γ t) side (fun h => γ (t + h)) v :=
    (_root_.SmoothManifolds.smooth_curve_defines_derivation S (γ t) side _ hγ).exists
  unfold velocity
  rw [dif_pos hex]
  exact hex.choose_spec

theorem scalar_derivative_of_velocity (S : SmoothManifold n k M) (f : M → ℝ)
    (hf : ScalarSmooth S.smoothStructure.val f) (γ : ℝ → M) (t : ℝ)
    (v : TangentSpace S (γ t))
    (hv : CurveRepresentsDerivation S (γ t) .twoSided (fun h => γ (t + h)) v) :
    HasDerivAt (fun h => f (γ (t + h))) (dFunction S f hf (γ t) v) 0 := by
  have hd := hv.2 (functionGerm S f hf (γ t)) f rfl
  change HasDerivWithinAt (fun h => f (γ (t + h)))
    (dFunction S f hf (γ t) v) Set.univ 0 at hd
  exact hasDerivWithinAt_univ.mp hd

theorem circleLoop_piecewise_smooth (S : SmoothManifold 1 .euclidean (Sphere 1))
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (hemisphereAtlas 1)) :
    PiecewiseSmoothOn S circleLoop 0 (2 * Real.pi) := by
  have hp : (0 : ℝ) < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  refine ⟨hp.le, circleLoop_continuous.continuousOn,
    singleSubdivision 0 (2 * Real.pi) hp, ?_⟩
  intro i hi
  have hi0 : i = 0 := by change i < 1 at hi; omega
  subst i
  change SmoothOnInterval S circleLoop 0 (2 * Real.pi)
  exact ⟨hp.le, circleLoop_continuous.continuousOn,
    fun t _ _ => circleLoop_smooth_at S hS _ t⟩

theorem circleLoop_closed : circleLoop 0 = circleLoop (2 * Real.pi) := by
  apply Subtype.ext
  simp [circleLoop]

theorem circleForm_coefficient (S : SmoothManifold 1 .euclidean (Sphere 1))
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (hemisphereAtlas 1))
    (hx : ScalarSmooth S.smoothStructure.val circleX)
    (hy : ScalarSmooth S.smoothStructure.val circleY) (t : ℝ) :
    coefficient S (circleForm S hx hy) circleLoop t = 1 := by
  have hv := velocity_represents_smooth_curve S circleLoop .twoSided t
    (circleLoop_smooth_at S hS .twoSided t)
  have hdx := scalar_derivative_of_velocity S circleX hx circleLoop t _ hv
  have hdy := scalar_derivative_of_velocity S circleY hy circleLoop t _ hv
  have hxderiv : HasDerivAt (fun h => circleX (circleLoop (t + h))) (-Real.sin t) 0 := by
    simpa [circleX, circleLoop, Function.comp_def] using
      (Real.hasDerivAt_cos (t + 0)).comp 0 ((hasDerivAt_const 0 t).add (hasDerivAt_id 0))
  have hyderiv : HasDerivAt (fun h => circleY (circleLoop (t + h))) (Real.cos t) 0 := by
    simpa [circleY, circleLoop, Function.comp_def] using
      (Real.hasDerivAt_sin (t + 0)).comp 0 ((hasDerivAt_const 0 t).add (hasDerivAt_id 0))
  have hdx' := hdx.unique hxderiv
  have hdy' := hdy.unique hyderiv
  change circleX (circleLoop t) * dFunction S circleY hy _ _ -
    circleY (circleLoop t) * dFunction S circleX hx _ _ = 1
  rw [hdx', hdy']
  dsimp [circleX, circleY, circleLoop]
  nlinarith [Real.cos_sq_add_sin_sq t]

theorem circleForm_period (S : SmoothManifold 1 .euclidean (Sphere 1))
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (hemisphereAtlas 1))
    (hx : ScalarSmooth S.smoothStructure.val circleX)
    (hy : ScalarSmooth S.smoothStructure.val circleY) :
    pathIntegral S (circleForm S hx hy) circleLoop 0 (2 * Real.pi) = 2 * Real.pi := by
  unfold pathIntegral
  simp only [circleForm_coefficient S hS hx hy]
  simp

theorem circleForm_not_exact (S : SmoothManifold 1 .euclidean (Sphere 1))
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (hemisphereAtlas 1))
    (hx : ScalarSmooth S.smoothStructure.val circleX)
    (hy : ScalarSmooth S.smoothStructure.val circleY) : ¬ Exact S (circleForm S hx hy) := by
  rintro ⟨f, hf, heq⟩
  have hderiv (t : ℝ) : HasDerivAt (fun s => f (circleLoop s)) 1 t := by
    have hv := velocity_represents_smooth_curve S circleLoop .twoSided t
      (circleLoop_smooth_at S hS .twoSided t)
    have hd := scalar_derivative_of_velocity S f hf circleLoop t _ hv
    have heval : dFunction S f hf (circleLoop t) (velocity S circleLoop .twoSided t) = 1 := by
      rw [heq]
      exact circleForm_coefficient S hS hx hy t
    have h0 : HasDerivAt (fun h => f (circleLoop (t + h))) 1 0 := heval ▸ hd
    have h0' : HasDerivAt (fun h => f (circleLoop (t + h))) 1 (-t + t) := by
      simpa only [neg_add_cancel] using h0
    simpa only [← add_assoc, add_neg_cancel, zero_add] using h0'.comp_const_add (-t) t
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 2 * Real.pi) (fun t _ => hderiv t) intervalIntegrable_const
  rw [← circleLoop_closed] at hi
  have hpi : 2 * Real.pi = 0 := by simpa using hi
  linarith [Real.pi_pos]

theorem circle_example_statement : Specs.SmoothManifolds.Ch07.PeriodCriterion.circle_exampleType := by
  intro S hS C
  have hx := sphere_coordinate_smooth S hS 0
  have hy := sphere_coordinate_smooth S hS 1
  refine ⟨hx, hy, ?_, closed_in_dimension_one S C _, circleLoop_piecewise_smooth S hS,
    circleLoop_closed, circleForm_period S hS hx hy, circleForm_not_exact S hS hx hy⟩
  exact oneForm_scalar_combination S C circleX circleY hx hy
    (dFunction S circleY hy) (dFunction S circleX hx)
    (Covectors.differential_smooth S C circleY hy) (Covectors.differential_smooth S C circleX hx)

/-- Concatenate paths on unrelated parameter intervals by an affine re-timing.
This records endpoints as well as the integral identity. -/
theorem append_retimed_paths
    (hconcat : Specs.SmoothManifolds.Ch07.PathIntegration.concatenationType.{u})
    (hreparam : Specs.SmoothManifolds.Ch07.PathIntegration.reparametrizationType.{u})
    (S : SmoothManifold n k M) (C : CotangentBundle S) (α : OneForm C)
    (γ η : ℝ → M) (a b c d : ℝ)
    (hγ : PiecewiseSmoothOn S γ a b) (hη : PiecewiseSmoothOn S η c d)
    (hjoin : γ b = η c) :
    ∃ (κ : ℝ → M) (e : ℝ), PiecewiseSmoothOn S κ a e ∧
      κ a = γ a ∧ κ e = η d ∧
      pathIntegral S α.field κ a e =
        pathIntegral S α.field γ a b + pathIntegral S α.field η c d := by
  let φ : ℝ → ℝ := fun t => c + (d - c) * (t - b)
  have hp := hreparam S C α η φ c d b (b + 1) hη
    (affine_reparametrization c d b hη.1)
  have hφb : φ b = c := by simp [φ]
  have hφend : φ (b + 1) = d := by dsimp [φ]; ring
  have hc := hconcat S C α γ (η ∘ φ) a b (b + 1) hγ hp.1
    (by simpa [hφb] using hjoin)
  refine ⟨concatenate γ (η ∘ φ) b, b + 1, hc.1, ?_, ?_, hc.2.trans ?_⟩
  · simp only [concatenate, if_pos hγ.1]
  · have hb : ¬ b + 1 ≤ b := by linarith
    simp only [concatenate, if_neg hb, Function.comp_apply, hφend]
  · rw [hp.2]

/-- Reachability by a finite-piece smooth path. -/
def Reachable (S : SmoothManifold n k M) (p q : M) : Prop :=
  ∃ (γ : ℝ → M) (a b : ℝ), PiecewiseSmoothOn S γ a b ∧ γ a = p ∧ γ b = q

theorem reachable_refl (S : SmoothManifold n k M) (p : M) : Reachable S p p :=
  ⟨fun _ => p, 0, 0, piecewiseSmoothOn_singleton S _ 0, rfl, rfl⟩

theorem reachable_symm
    (hrev : Specs.SmoothManifolds.Ch07.PathIntegration.reversalType.{u})
    (S : SmoothManifold n k M) (C : CotangentBundle S) (α : OneForm C)
    {p q : M} (h : Reachable S p q) : Reachable S q p := by
  obtain ⟨γ, a, b, hγ, hp, hq⟩ := h
  exact ⟨reverse γ a b, a, b, (hrev S C α γ a b hγ).1,
    by simpa [reverse] using hq, by simpa [reverse] using hp⟩

theorem reachable_trans
    (hconcat : Specs.SmoothManifolds.Ch07.PathIntegration.concatenationType.{u})
    (hreparam : Specs.SmoothManifolds.Ch07.PathIntegration.reparametrizationType.{u})
    (S : SmoothManifold n k M) (C : CotangentBundle S) (α : OneForm C)
    {p q r : M} (hpq : Reachable S p q) (hqr : Reachable S q r) : Reachable S p r := by
  obtain ⟨γ, a, b, hγ, hγa, hγb⟩ := hpq
  obtain ⟨η, c, d, hη, hηc, hηd⟩ := hqr
  obtain ⟨κ, e, hκ, hκa, hκe, _⟩ :=
    append_retimed_paths hconcat hreparam S C α γ η a b c d hγ hη (hγb.trans hηc.symm)
  exact ⟨κ, a, e, hκ, hκa.trans hγa, hκe.trans hηd⟩

/-- The global algebraic construction of a potential, independently on each
smooth-path class. This does not yet assert its local smoothness. In particular,
the construction does not choose a point on an empty manifold. -/
theorem exists_integral_potential
    (hconcat : Specs.SmoothManifolds.Ch07.PathIntegration.concatenationType.{u})
    (hreparam : Specs.SmoothManifolds.Ch07.PathIntegration.reparametrizationType.{u})
    (hrev : Specs.SmoothManifolds.Ch07.PathIntegration.reversalType.{u})
    (S : SmoothManifold n k M) (C : CotangentBundle S) (α : OneForm C)
    (hpi : PathIndependent S α.field) :
    ∃ f : M → ℝ, ∀ (γ : ℝ → M) (a b : ℝ), PiecewiseSmoothOn S γ a b →
      pathIntegral S α.field γ a b = f (γ b) - f (γ a) := by
  classical
  let R : Setoid M := {
    r := Reachable S
    iseqv := ⟨reachable_refl S, reachable_symm hrev S C α,
      reachable_trans hconcat hreparam S C α⟩ }
  let base (p : M) : M := (Quotient.mk R p).out
  have hb (p : M) : Reachable S (base p) p := Quotient.mk_out p
  choose γ a b hγ hstart hend using hb
  let f (p : M) : ℝ := pathIntegral S α.field (γ p) (a p) (b p)
  refine ⟨f, ?_⟩
  intro η c d hη
  have hbase : base (η c) = base (η d) :=
    congrArg Quotient.out (Quotient.sound (show R (η c) (η d) from ⟨η, c, d, hη, rfl, rfl⟩))
  obtain ⟨κ, e, hκ, hκa, hκe, hκint⟩ :=
    append_retimed_paths hconcat hreparam S C α (γ (η c)) η (a (η c)) (b (η c)) c d
      (hγ (η c)) hη (hend (η c))
  have hi := hpi κ (γ (η d)) (a (η c)) e (a (η d)) (b (η d)) hκ (hγ (η d))
    (hκa.trans ((hstart (η c)).trans (hbase.trans (hstart (η d)).symm)))
    (hκe.trans (hend (η d)).symm)
  rw [hκint] at hi
  dsimp [f]
  linarith

/-- A coordinate path with a smooth ambient extension is a genuine smooth
path, even when it meets the boundary of the model. -/
theorem smoothOnInterval_of_chart_coordinates (S : SmoothManifold n k M)
    (c : ModelChart n k M) (hc : c ∈ S.smoothStructure.val)
    (γ : ℝ → M) (a b : ℝ) (hab : a ≤ b)
    (hγ : ContinuousOn γ (Icc a b))
    (hsource : ∀ t ∈ Icc a b, γ t ∈ c.source)
    (v : ℝ → Euclidean n) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (he : EqOn (fun t => (c (γ t)).val) v (Icc a b)) :
    SmoothOnInterval S γ a b := by
  refine ⟨hab, hγ, ?_⟩
  intro t ht hab'
  have hadd := PathIntegration.add_tendsto_interval hab' ht
  have hlim : Tendsto (fun h => γ (t+h))
      (𝓝[curveParameterSet (sideAt a b t)] 0) (𝓝 (γ t)) :=
    (hγ t ht).tendsto.comp hadd
  refine ⟨by simp, by simpa only [ContinuousWithinAt, add_zero] using hlim, ?_⟩
  intro d hd hdt
  obtain ⟨U, hU, hUpt, G, hG, heG⟩ := chartContDiffAt_of_compatible
    (S.smoothStructure.property.1.2 c hc d hd) (hsource t ht) hdt
  let H : ℝ → Euclidean n := fun h => v (t+h)
  have hH : ContDiff ℝ (⊤ : ℕ∞) H :=
    hv.comp (contDiff_const.add contDiff_id)
  refine ⟨H ⁻¹' U, hU.preimage hH.continuous, ?_, G ∘ H,
    hG.comp hH.contDiffOn (fun _ hy => hy), ?_⟩
  · simpa [H, ← he ht] using hUpt
  · have heG' := heG.comp_tendsto hlim
    have hint : ∀ᶠ h in 𝓝[curveParameterSet (sideAt a b t)] 0, t+h ∈ Icc a b :=
      hadd.eventually self_mem_nhdsWithin
    filter_upwards [heG', hint] with h hh hi
    simpa only [Function.comp_apply, H, id_eq, ← he hi] using hh.symm

/-- Integrating along a chart segment evaluates precisely the extended
cotangent coefficients, including one-sided endpoint velocities. -/
theorem chart_segment_integral (S : SmoothManifold n k M) (C : CotangentBundle S)
    (α : OneForm C) (c : ModelChart n k M) (hc : c ∈ S.smoothStructure.val)
    (x y : ModelSpace n k)
    (hseg : ∀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1),
      (⟨x.val + t • (y.val-x.val),
        (convex_modelSet n k).add_smul_mem x.property (by simpa using y.property) ht⟩ :
        ModelSpace n k) ∈ c.target)
    (A : Euclidean n → Euclidean n)
    (hA : ∀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1),
      let z : ModelSpace n k := ⟨x.val + t • (y.val-x.val),
        (convex_modelSet n k).add_smul_mem x.property (by simpa using y.property) ht⟩
      ∀ j, A z.val j = α.field (c.symm z)
        (coordinateVector C.tangent.fiberCoordinates c hc (c.symm z)
          (c.map_target (hseg t ht)) j)) :
    ∃ γ : ℝ → M, PiecewiseSmoothOn S γ 0 1 ∧ γ 0 = c.symm x ∧ γ 1 = c.symm y ∧
      pathIntegral S α.field γ 0 1 =
        ∫ t in (0 : ℝ)..1, ∑ j, (y.val j-x.val j) * A (x.val+t • (y.val-x.val)) j := by
  let z : ℝ → ModelSpace n k := fun t =>
    ⟨x.val + (projIcc 0 1 zero_le_one t).val • (y.val-x.val),
      (convex_modelSet n k).add_smul_mem x.property (by simpa using y.property)
        (projIcc 0 1 zero_le_one t).property⟩
  have hzcont : Continuous z := by
    apply Continuous.subtype_mk
    exact continuous_const.add
      ((continuous_subtype_val.comp continuous_projIcc).smul continuous_const)
  have hzT (t : ℝ) : z t ∈ c.target :=
    hseg _ (projIcc 0 1 zero_le_one t).property
  let γ : ℝ → M := c.symm ∘ z
  have hγcont : Continuous γ :=
    c.continuousOn_symm.comp_continuous hzcont hzT
  have hcoord (t : ℝ) : c (γ t) = z t := c.right_inv (hzT t)
  have hval (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (c (γ t)).val = x.val+t • (y.val-x.val) := by
    rw [hcoord]
    simp only [z, projIcc_of_mem zero_le_one ht]
  let v : ℝ → Euclidean n := fun t => x.val+t • (y.val-x.val)
  have hv : ContDiff ℝ (⊤ : ℕ∞) v :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  have hsource (t : ℝ) : γ t ∈ c.source := c.map_target (hzT t)
  have hs : SmoothOnInterval S γ 0 1 :=
    smoothOnInterval_of_chart_coordinates S c hc γ 0 1 zero_le_one hγcont.continuousOn
      (fun t _ => hsource t) v hv hval
  have hpw : PiecewiseSmoothOn S γ 0 1 := by
    refine ⟨zero_le_one, hγcont.continuousOn, singleSubdivision 0 1 zero_lt_one, ?_⟩
    intro i hi
    have : i = 0 := by change i < 1 at hi; omega
    subst i
    exact hs
  refine ⟨γ, hpw, ?_, ?_, ?_⟩
  · simp [γ, z]
  · simp [γ, z]
  · rw [← PathIntegration.pieceIntegral_eq S α.field γ zero_le_one]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa [uIcc_of_le zero_le_one] using ht
    let K := C.tangent.fiberCoordinates
    let w := velocity S γ (sideAt 0 1 t) t
    have hw (j : Fin n) : K.equiv c hc (γ t) (hsource t) w j = y.val j-x.val j := by
      rw [PathIntegration.velocity_coordinates_within S γ zero_lt_one hs ht' K c hc (hsource t)]
      have hd : HasDerivWithinAt (fun s => (c (γ s)).val j) (y.val j-x.val j) (Icc 0 1) t := by
        have hbase : HasDerivWithinAt (fun s : ℝ => x.val j+s*(y.val j-x.val j))
            (y.val j-x.val j) (Icc 0 1) t := by
          simpa only [one_mul, id_eq] using
            ((((hasDerivAt_id t).mul_const (y.val j-x.val j)).const_add (x.val j)).hasDerivWithinAt
              (s := Icc 0 1))
        apply hbase.congr
        · intro s hs
          exact congrFun (hval s hs) j
        · exact congrFun (hval t ht') j
      exact hd.derivWithin (uniqueDiffOn_Icc zero_lt_one t ht')
    have hexp := Covectors.covector_expansion K c hc (γ t) (hsource t) (α.field (γ t))
    have ha (j : Fin n) : α.field (γ t) (coordinateVector K c hc (γ t) (hsource t) j) =
        A (x.val+t • (y.val-x.val)) j := by
      have h := hA t ht' j
      have hz : z t = (⟨x.val + t • (y.val-x.val),
        (convex_modelSet n k).add_smul_mem x.property (by simpa using y.property) ht'⟩ : ModelSpace n k) := by
        apply Subtype.ext
        simp only [z, projIcc_of_mem zero_le_one ht']
      let Q : c.target → ℝ := fun q => α.field (c.symm q.val)
        (coordinateVector K c hc (c.symm q.val) (c.map_target q.property) j)
      have hz' : (⟨z t, hzT t⟩ : c.target) =
          ⟨⟨x.val+t • (y.val-x.val),
            (convex_modelSet n k).add_smul_mem x.property (by simpa using y.property) ht'⟩,
              hseg t ht'⟩ := Subtype.ext hz
      change Q ⟨z t, hzT t⟩ = _
      rw [hz']
      exact h.symm
    change α.field (γ t) w = _
    rw [hexp]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      coordinateCovector, LinearMap.comp_apply, LinearMap.proj_apply, LinearEquiv.coe_coe]
    apply Finset.sum_congr rfl
    intro j _
    rw [ha, hw, mul_comm]

/-- A smooth vector field has smooth radial average coefficients on each small ball. -/
theorem radial_average_smooth {n : ℕ} (A : Euclidean n → Euclidean n)
    (U : Set (Euclidean n)) (hU : IsOpen U)
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) A U)
    (x : Euclidean n) (r : ℝ) (hr : 0 < r) (hball : Metric.ball x r ⊆ U) :
    ∀ j : Fin n, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y => ∫ t in (0 : ℝ)..1, A (x + t • (y-x)) j) (Metric.ball x r) := by
  let seg : Euclidean n × ℝ → Euclidean n := fun p => x + p.2 • (p.1-x)
  have hseg : ContDiff ℝ (⊤ : ℕ∞) seg := by dsimp [seg]; fun_prop
  let W := seg ⁻¹' U
  have hW : IsOpen W := hU.preimage hseg.continuous
  have hVW (y : Euclidean n) (hy : y ∈ Metric.ball x r) (t : ℝ)
      (ht : t ∈ Icc (0 : ℝ) 1) : (y,t) ∈ W := by
    apply hball
    exact (convex_ball x r).add_smul_mem (Metric.mem_ball_self hr) (by simpa using hy) ht
  intro j
  have hAj : ContDiffOn ℝ (⊤ : ℕ∞) (fun y => A y j) U :=
    (contDiff_apply ℝ (fun _ : Fin n => ℝ) j).comp_contDiffOn hA
  exact Hadamard.contDiffOn_integral W hW _
    (hAj.comp hseg.contDiffOn (fun _ hz => hz)) _ Metric.isOpen_ball hVW

/-- The radial primitive is smooth, and its derivative at its base is A(x). -/
theorem radial_primitive_smooth_derivative {n : ℕ} (A : Euclidean n → Euclidean n)
    (U : Set (Euclidean n)) (hU : IsOpen U)
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) A U)
    (x : Euclidean n) (r : ℝ) (hr : 0 < r) (hball : Metric.ball x r ⊆ U)
    (v : ℝ) :
    ∃ F : Euclidean n → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) F (Metric.ball x r) ∧
      (∀ y ∈ Metric.ball x r, F y = v + ∫ t in (0 : ℝ)..1,
        ∑ j, (y j-x j) * A (x+t • (y-x)) j) ∧
      (∀ j, fderiv ℝ F x (Pi.single j 1) = A x j) := by
  let g : Fin n → Euclidean n → ℝ :=
    fun j y => ∫ t in (0 : ℝ)..1, A (x+t • (y-x)) j
  have hg (j : Fin n) : ContDiffOn ℝ (⊤ : ℕ∞) (g j) (Metric.ball x r) :=
    radial_average_smooth A U hU hA x r hr hball j
  have hgx (j : Fin n) : g j x = A x j := by simp [g]
  let F : Euclidean n → ℝ := fun y => v + ∑ j, (y j-x j) * g j y
  refine ⟨F, ?_, ?_, ?_⟩
  · exact contDiffOn_const.add (ContDiffOn.sum fun j _ =>
      ((contDiff_apply ℝ (fun _ : Fin n => ℝ) j).contDiffOn.sub contDiffOn_const).mul (hg j))
  · intro y hy
    dsimp [F]
    congr 1
    rw [intervalIntegral.integral_finsetSum]
    · simp only [g, intervalIntegral.integral_const_mul]
    · intro j _
      apply IntervalIntegrable.const_mul
      have hseg : Continuous (fun t : ℝ => x+t • (y-x)) := by fun_prop
      have hcomp : ContinuousOn (fun t : ℝ => A (x+t • (y-x)) j) (Icc (0 : ℝ) 1) :=
        ((contDiff_apply ℝ (fun _ : Fin n => ℝ) j).comp_contDiffOn hA).continuousOn.comp hseg.continuousOn (by
          intro t ht
          exact hball ((convex_ball x r).add_smul_mem (Metric.mem_ball_self hr) (by simpa using hy) ht))
      exact hcomp.intervalIntegrable_of_Icc zero_le_one
  · intro j
    have hx : x ∈ Metric.ball x r := Metric.mem_ball_self hr
    have hdg (i : Fin n) : HasFDerivAt (g i) (fderiv ℝ (g i) x) x :=
      ((hg i).contDiffAt (Metric.isOpen_ball.mem_nhds hx)).differentiableAt (by simp) |>.hasFDerivAt
    have hd (i : Fin n) := (((ContinuousLinearMap.proj i : Euclidean n →L[ℝ] ℝ).hasFDerivAt).sub_const (x i)).mul (hdg i)
    have hDF : HasFDerivAt F
        (∑ i : Fin n, (g i x) • (ContinuousLinearMap.proj i : Euclidean n →L[ℝ] ℝ)) x := by
      convert (HasFDerivAt.sum fun i (_ : i ∈ Finset.univ) => hd i).const_add v using 1 <;>
        simp [F]
    rw [hDF.fderiv]
    simp [hgx, Pi.single_apply]

theorem oneForm_coefficient_extension (S : SmoothManifold n k M)
    (C : CotangentBundle S) (α : OneForm C) (p : M)
    (c : ModelChart n k M) (hc : c ∈ S.smoothStructure.val) (hp : p ∈ c.source) :
    ∃ (r : ℝ), 0 < r ∧ ∃ A : Euclidean n → Euclidean n,
      ContDiffOn ℝ (⊤ : ℕ∞) A (Metric.ball (c p).val r) ∧
      ∀ (z : ModelSpace n k) (hz : z.val ∈ Metric.ball (c p).val r),
        ∃ hzt : z ∈ c.target, ∀ j,
          A z.val j = α.field (c.symm z)
            (coordinateVector C.tangent.fiberCoordinates c hc (c.symm z) (c.map_target hzt) j) := by
  letI := (cotangentSpace C).topology
  let B := (cotangentSpace C).bundle
  have hi : p ∈ B.baseSet ⟨c, hc⟩ := by rw [Covectors.cotangent_baseSet]; exact hp
  let a : M → Euclidean n := fun q => ((B.trivialization ⟨c, hc⟩) ⟨q, α.field q⟩).2
  have ha : FrameData.VectorSmoothAt S.smoothStructure.val a p :=
    FrameData.VectorSmoothAt.comp
      (g := fun q => (⟨q, α.field q⟩ : Bundle.TotalSpace (Euclidean n) (CotangentFiber S)))
      B.totalManifold.smoothStructure.property.1.1
      (Frames.trivializationCoordinates_smoothAt B ⟨c, hc⟩ ⟨p, α.field p⟩ hi) (α.smooth p)
  obtain ⟨U, hU, hcpU, A, hA, heq⟩ := ha.2 c hc hp
  obtain ⟨W, hWmem, hWopen, hpW⟩ := eventually_nhds_iff.mp heq
  have hVopen := c.isOpen_inter_preimage_symm hWopen
  obtain ⟨O, hO, hOeq⟩ := isOpen_induced_iff.mp hVopen
  have hcpO : (c p).val ∈ O := by
    have hv : c p ∈ c.target ∩ c.symm ⁻¹' W :=
      ⟨c.map_source hp, by simpa only [mem_preimage, c.left_inv hp] using hpW⟩
    rw [← hOeq] at hv
    exact hv
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (hU.inter hO) (c p).val ⟨hcpU, hcpO⟩
  refine ⟨r, hr, A, hA.mono (fun y hy => (hball hy).1), ?_⟩
  intro z hz
  have hzt : z ∈ c.target ∩ c.symm ⁻¹' W := by
    rw [← hOeq]
    exact (hball hz).2
  refine ⟨hzt.1, ?_⟩
  intro j
  have he := congrFun (hWmem (c.symm z) hzt.2) j
  have hzcoord : c (c.symm z) = z := c.right_inv hzt.1
  dsimp only at he
  rw [hzcoord] at he
  exact he.trans (Covectors.cotangent_coordinates C c hc (c.symm z) (c.map_target hzt.1) (α.field (c.symm z)) j)


/-- A global endpoint integral potential has an actual smooth chart extension,
whose full ambient differential is the prescribed covector at its basepoint. -/
theorem integral_potential_chart_extension (S : SmoothManifold n k M)
    (C : CotangentBundle S) (α : OneForm C) (f : M → ℝ)
    (hint : ∀ (γ : ℝ → M) (a b : ℝ), PiecewiseSmoothOn S γ a b →
      pathIntegral S α.field γ a b = f (γ b) - f (γ a))
    (p : M) (c : ModelChart n k M) (hc : c ∈ S.smoothStructure.val) (hp : p ∈ c.source) :
    ∃ (r : ℝ), 0 < r ∧ ∃ F : Euclidean n → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) F (Metric.ball (c p).val r) ∧
      ((fun q => F (c q).val) =ᶠ[𝓝 p] f) ∧
      (∀ j, fderiv ℝ F (c p).val (Pi.single j 1) = α.field p
        (coordinateVector C.tangent.fiberCoordinates c hc p hp j)) := by
  obtain ⟨r, hr, A, hA, hcoeff⟩ := oneForm_coefficient_extension S C α p c hc hp
  let x := c p
  obtain ⟨F, hF, hformula, hDF⟩ := radial_primitive_smooth_derivative A
    (Metric.ball x.val r) Metric.isOpen_ball hA x.val r hr (fun _ hy => hy) (f p)
  have hlocal (q : M) (hqs : q ∈ c.source) (hq : (c q).val ∈ Metric.ball x.val r) :
      F (c q).val = f q := by
    let y := c q
    have hsegball (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
        x.val + t • (y.val-x.val) ∈ Metric.ball x.val r :=
      (convex_ball x.val r).add_smul_mem (Metric.mem_ball_self hr) (by simpa [y] using hq) ht
    have hseg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
        (⟨x.val + t • (y.val-x.val),
          (convex_modelSet n k).add_smul_mem x.property (by simpa using y.property) ht⟩ :
          ModelSpace n k) ∈ c.target :=
      (hcoeff _ (hsegball t ht)).choose
    have hAseg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
        let z : ModelSpace n k :=
          ⟨x.val + t • (y.val-x.val),
            (convex_modelSet n k).add_smul_mem x.property (by simpa using y.property) ht⟩
        ∀ j, A z.val j = α.field (c.symm z)
          (coordinateVector C.tangent.fiberCoordinates c hc (c.symm z) (c.map_target (hseg t ht)) j) :=
      (hcoeff _ (hsegball t ht)).choose_spec
    obtain ⟨γ, hγ, hγ0, hγ1, hiγ⟩ :=
      chart_segment_integral S C α c hc x y hseg A hAseg
    have hi := hint γ 0 1 hγ
    rw [hγ0, hγ1] at hi
    have hxinv : c.symm x = p := c.left_inv hp
    have hyinv : c.symm y = q := c.left_inv hqs
    rw [hxinv, hyinv] at hi
    rw [hformula (c q).val hq, ← hiγ, hi]
    ring
  refine ⟨r, hr, F, hF, ?_, ?_⟩
  · have hneigh : ∀ᶠ q in 𝓝 p, (c q).val ∈ Metric.ball x.val r :=
      ((continuous_subtype_val.continuousAt).comp
        (c.continuousAt hp)).eventually (Metric.ball_mem_nhds _ hr)
    filter_upwards [c.open_source.mem_nhds hp, hneigh] with q hqs hq
    exact hlocal q hqs hq
  · intro j
    rw [hDF]
    have hbase := (hcoeff (c p) (Metric.mem_ball_self hr)).choose_spec j
    have heval (q : M) (hq : q ∈ c.source) (hqp : q = p) :
        α.field q (coordinateVector C.tangent.fiberCoordinates c hc q hq j) =
          α.field p (coordinateVector C.tangent.fiberCoordinates c hc p hp j) := by
      subst q
      rfl
    exact hbase.trans (heval _ _ (c.left_inv hp))


theorem exact_of_chart_extensions (S : SmoothManifold n k M)
    (C : CotangentBundle S) (α : CovectorField S) (f : M → ℝ)
    (hext : ∀ (p : M) (c : ModelChart n k M) (hc : c ∈ S.smoothStructure.val)
      (hp : p ∈ c.source),
      ∃ (r : ℝ), 0 < r ∧ ∃ F : Euclidean n → ℝ,
        ContDiffOn ℝ (⊤ : ℕ∞) F (Metric.ball (c p).val r) ∧
        (fun q => F (c q).val) =ᶠ[𝓝 p] f ∧
        ∀ j, fderiv ℝ F (c p).val (Pi.single j 1) =
          α p (coordinateVector C.tangent.fiberCoordinates c hc p hp j)) :
    Exact S α := by
  have hf : ScalarSmooth S.smoothStructure.val f := by
    intro p
    obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
    obtain ⟨r, hr, F, hF, heq, hder⟩ := hext p c hc hp
    exact scalarContDiffAt_of_chart S.smoothStructure.property.1 hc hp
      ⟨Metric.ball (c p).val r, Metric.isOpen_ball, Metric.mem_ball_self hr, F, hF, heq⟩
  refine ⟨f, hf, ?_⟩
  funext p
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨r, hr, F, hF, heq, hder⟩ := hext p c hc hp
  have hG : GermChartExtension S p c (functionGerm S f hf p) F :=
    ⟨⟨Metric.ball (c p).val r, Metric.isOpen_ball, Metric.mem_ball_self hr, hF⟩,
      heq.germ_eq⟩
  rw [(Covectors.differential_coordinates S C f hf c hc p hp F hG).2,
    Covectors.covector_expansion C.tangent.fiberCoordinates c hc p hp (α p)]
  simp_rw [hder]

/-- Zero periods give a smooth global primitive, component by component. -/
theorem zero_periods_exact_statement :
    Specs.SmoothManifolds.Ch07.PeriodCriterion.zero_periods_exactType.{u} := by
  intro n k M _ S C α hz
  have hpi := zero_periods_implies_path_independent
    (fun S => PathIntegration.concatenation S)
    (fun S => PathIntegration.reparametrization S)
    (fun S => PathIntegration.reversal S) S C α hz
  obtain ⟨f, hint⟩ := exists_integral_potential
    (fun S => PathIntegration.concatenation S)
    (fun S => PathIntegration.reparametrization S)
    (fun S => PathIntegration.reversal S) S C α hpi
  exact exact_of_chart_extensions S C α.field f
    (integral_potential_chart_extension S C α f hint)

/-- Every exact smooth one-form has zero integral around every closed path. -/
theorem exact_zero_periods :
    Specs.SmoothManifolds.Ch07.PeriodCriterion.exact_zero_periodsType.{u} := by
  intro n k M _ S C α h
  exact exact_implies_zero_periods (fun S => PathIntegration.integral_dFunction S) S α.field h

/-- Vanishing periods are sufficient for a smooth global primitive. -/
theorem zero_periods_exact :
    Specs.SmoothManifolds.Ch07.PeriodCriterion.zero_periods_exactType.{u} :=
  zero_periods_exact_statement

/-- Vanishing periods are equivalent to dependence only on endpoints. -/
theorem zero_periods_iff_path_independent :
    Specs.SmoothManifolds.Ch07.PeriodCriterion.zero_periods_iff_path_independentType.{u} := by
  intro n k M _ S C α
  exact ⟨zero_periods_implies_path_independent (fun S => PathIntegration.concatenation S)
    (fun S => PathIntegration.reparametrization S) (fun S => PathIntegration.reversal S) S C α,
    path_independent_implies_zero_periods S α.field⟩

/-- Primitives differ precisely by a locally constant function. -/
theorem primitive_difference :
    Specs.SmoothManifolds.Ch07.PeriodCriterion.primitive_differenceType.{u} :=
  primitive_difference_statement

/-- Local constancy is equivalent to independent constants on connected components. -/
theorem locally_constant_components :
    Specs.SmoothManifolds.Ch07.PeriodCriterion.locally_constant_componentsType.{u} :=
  locally_constant_components_statement

/-- The angular circle form is closed, has period 2π, and is not exact. -/
theorem circle_example :
    Specs.SmoothManifolds.Ch07.PeriodCriterion.circle_exampleType :=
  circle_example_statement

end SmoothManifolds.PeriodCriterion
