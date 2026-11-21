import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Integration.ClosedOneFormLocalPrimitives
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Tangent.HadamardLocal
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch07.ExteriorDerivative
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace SmoothManifolds.ClosedOneFormLocalPrimitives
open ModelData AtlasData PartitionData CovectorData TangentData ExteriorData
  ExteriorDerivativeData ExteriorDerivativeResults BundleOperationsData Set Filter
open scoped Topology
universe u

/-- Turn the alternating coefficient representation of a one-form into its
continuous linear representation. -/
def coefficientOneLinear (n : ℕ) :
    (Index n 1 → ℝ) →L[ℝ] (Euclidean n →L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap {
    toFun := fun a => (Euclidean.coefficientAlternatingEquiv n 1 a).toContinuousLinearMap
      (fun _ => 0) 0
    map_add' := by intros; ext v; simp [ContinuousAlternatingMap.toContinuousLinearMap]
    map_smul' := by intros; ext v; simp [ContinuousAlternatingMap.toContinuousLinearMap] }

lemma coefficientOneLinear_apply (n : ℕ) (a : Index n 1 → ℝ) (v : Euclidean n) :
    coefficientOneLinear n a v =
      Euclidean.coefficientAlternatingEquiv n 1 a (fun _ => v) := by
  change Euclidean.coefficientAlternatingEquiv n 1 a (Function.update (fun _ => 0) 0 v) = _
  congr 1
  ext i
  have : i = 0 := Subsingleton.elim _ _
  subst i
  simp

/-- Evaluation of a degree-one intrinsic exterior element is the original covector. -/
lemma evaluate_one {V : Type u} [AddCommGroup V] [Module ℝ V]
    (α : Module.Dual ℝ V) (v : Fin 1 → V) :
    evaluate V 1 ((exteriorPower.oneEquiv ℝ (Module.Dual ℝ V)).symm α) v = α (v 0) := by
  rw [show (exteriorPower.oneEquiv ℝ (Module.Dual ℝ V)).symm α =
    exteriorPower.ιMulti ℝ 1 (fun _ => α) by
      apply (exteriorPower.oneEquiv ℝ (Module.Dual ℝ V)).injective
      simp]
  rw [ExteriorAlgebraResults.determinant_normalization]
  simp

/-- Closedness of the alternating one-form is symmetry of the derivative of
its linear representation. This is an ambient statement at the specified point. -/
lemma symmetric_of_extDeriv_zero {n : ℕ}
    (F : Euclidean n → Index n 1 → ℝ) (x : Euclidean n)
    (hF : DifferentiableAt ℝ F x)
    (hz : ∀ v : Fin 2 → Euclidean n,
      extDeriv (fun z => Euclidean.coefficientAlternatingEquiv n 1 (F z)) x v = 0) :
    ∀ u v : Euclidean n,
      fderiv ℝ (fun z => coefficientOneLinear n (F z)) x u v =
      fderiv ℝ (fun z => coefficientOneLinear n (F z)) x v u := by
  let ω := fun z => coefficientOneLinear n (F z)
  have hω : DifferentiableAt ℝ ω x := (coefficientOneLinear n).differentiableAt.comp x hF
  have heval (w : Euclidean n) :
      fderiv ℝ (fun z => Euclidean.coefficientAlternatingEquiv n 1 (F z) (fun _ => w)) x =
      (ContinuousLinearMap.apply ℝ ℝ w).comp (fderiv ℝ ω x) := by
    simp_rw [← coefficientOneLinear_apply]
    exact ((ContinuousLinearMap.apply ℝ ℝ w).hasFDerivAt.comp x hω.hasFDerivAt).fderiv
  have hθ : DifferentiableAt ℝ
      (fun z => Euclidean.coefficientAlternatingEquiv n 1 (F z)) x :=
    (Euclidean.coefficientAlternatingEquiv n 1).differentiableAt.comp x hF
  intro u v
  have h0 : (0 : Fin 2).removeNth ![u, v] = (fun _ => v) := by
    ext i
    have : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  have h1 : (1 : Fin 2).removeNth ![u, v] = (fun _ => u) := by
    ext i
    have : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  have h := hz ![u, v]
  rw [extDeriv_apply hθ] at h
  rw [Fin.sum_univ_two] at h
  simp only [h0, h1, heval, Fin.val_zero, pow_zero, one_smul,
    Fin.val_one, pow_one, neg_smul, Matrix.cons_val_zero, Matrix.cons_val_one,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply] at h
  exact sub_eq_zero.mp h

/-- The radial integral has a smooth ambient extension, regardless of whether
closedness holds outside the model. -/
lemma radial_integral_smooth {n : ℕ}
    (ω : Euclidean n → Euclidean n →L[ℝ] ℝ)
    (U : Set (Euclidean n)) (hU : IsOpen U) (hω : ContDiffOn ℝ (⊤ : ℕ∞) ω U)
    (x : Euclidean n) (r : ℝ) (hr : 0 < r) (hball : Metric.ball x r ⊆ U) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y => curveIntegral ω (Path.segment x y)) (Metric.ball x r) := by
  let seg : Euclidean n × ℝ → Euclidean n := fun p => x + p.2 • (p.1-x)
  have hseg : ContDiff ℝ (⊤ : ℕ∞) seg := by dsimp [seg]; fun_prop
  let W := seg ⁻¹' U
  have hW : IsOpen W := hU.preimage hseg.continuous
  have hdiff : ContDiff ℝ (⊤ : ℕ∞) (fun p : Euclidean n × ℝ => p.1-x) := by fun_prop
  have hInt := Hadamard.contDiffOn_integral W hW
    (fun p : Euclidean n × ℝ => ω (seg p) (p.1-x))
    ((hω.comp hseg.contDiffOn (fun _ hz => hz)).clm_apply hdiff.contDiffOn)
    (Metric.ball x r) Metric.isOpen_ball (by
      intro y hy t ht
      exact hball ((convex_ball x r).add_smul_mem (Metric.mem_ball_self hr) (by simpa using hy) ht))
  convert hInt using 1
  funext y
  rw [curveIntegral_segment]
  congr 1
  funext t
  simp only [AffineMap.lineMap_apply_module', seg, add_comm]


lemma linear_coefficients {n : ℕ} {k : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n k M} (C : CotangentBundle S)
    (c : ModelChart n k M) (hc : c ∈ S.smoothStructure.val)
    (α : CovectorField S) (q : c.source) (v : Euclidean n) :
    coefficientOneLinear n
      (fun I => coefficients C 1 c hc (PeriodData.oneField S α) q I) v =
      α q.val ((C.tangent.fiberCoordinates.equiv c hc q.val q.property).symm v) := by
  rw [coefficientOneLinear_apply]
  change Euclidean.coefficientAlternatingEquiv n 1
    (((((Pi.basisFun ℝ (Fin n)).map
      (C.tangent.fiberCoordinates.equiv c hc q.val q.property).symm).dualBasis.exteriorPower 1).equivFun)
      (PeriodData.oneField S α q.val)) (fun _ => v) = _
  have hh := @coefficientAlternating_evaluate.{u} (TangentSpace S q.val) _ _ n 1
    (C.tangent.fiberCoordinates.equiv c hc q.val q.property)
    (PeriodData.oneField S α q.val) (fun _ => v)
  rw [hh]
  change evaluate (TangentSpace S q.val) 1
    ((exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace S q.val))).symm (α q.val))
    (fun _ => (C.tangent.fiberCoordinates.equiv c hc q.val q.property).symm v) = _
  rw [evaluate_one]

/-- A closed intrinsic one-form has a smooth ambient chart potential whose
ambient derivative is correct at every point of a relative ball. -/
theorem chart_primitive {n : ℕ} {k : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n k M) (C : CotangentBundle S) (α : OneForm C)
    (hclosed : HasExteriorDerivative C (PeriodData.oneField S α.field) 0)
    (c : ModelChart n k M) (hc : c ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ c.source) :
    ∃ (r : ℝ), 0 < r ∧ ∃ P : Euclidean n → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) P (Metric.ball (c p).val r) ∧
      ∀ (z : ModelSpace n k) (hz : z.val ∈ Metric.ball (c p).val r),
        ∃ hzt : z ∈ c.target, ∀ j,
          fderiv ℝ P z.val (Pi.single j 1) =
            α.field (c.symm z) (coordinateVector C.tangent.fiberCoordinates c hc
              (c.symm z) (c.map_target hzt) j) := by
  obtain ⟨B⟩ := ExteriorAlgebraResults.exists_formBundle C 1
  have hα := oneForm_isForm C B α.field α.smooth
  have hreg := (smooth_coefficients C 1 B (PeriodData.oneField S α.field)).mp hα
  obtain ⟨U, hU, hpU, F, hF, heF⟩ := hreg c hc ⟨p, hp⟩
  obtain ⟨O, hO, hOeq⟩ := isOpen_induced_iff.mp c.open_target
  have hpO : (c p).val ∈ O := by
    have hh := c.map_source hp
    rw [← hOeq] at hh
    exact hh
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (hU.inter hO) (c p).val ⟨hpU, hpO⟩
  let ω : Euclidean n → Euclidean n →L[ℝ] ℝ := fun y => coefficientOneLinear n (F y)
  have hω : ContDiffOn ℝ (⊤ : ℕ∞) ω U := (coefficientOneLinear n).contDiff.comp_contDiffOn hF
  let s : Set (Euclidean n) := modelSet n k ∩ Metric.ball (c p).val r
  have hs : Convex ℝ s := (convex_modelSet n k).inter (convex_ball _ _)
  have htarget (z : ModelSpace n k) (hz : z.val ∈ Metric.ball (c p).val r) : z ∈ c.target := by
    rw [← hOeq]
    exact (hball hz).2
  have hsymm : ∀ y ∈ s, ∀ u v : Euclidean n,
      fderiv ℝ ω y u v = fderiv ℝ ω y v u := by
    intro y hy
    let z : ModelSpace n k := ⟨y, hy.1⟩
    have hzt := htarget z hy.2
    have hq := c.map_target hzt
    apply symmetric_of_extDeriv_zero F y
      ((hF.contDiffAt (hU.mem_nhds (hball hy.2).1)).differentiableAt (by simp))
    intro v
    have hh := coordinateDerivative_evaluate_extension C 1 c hc
      (PeriodData.oneField S α.field) (c.symm z) hq U hU
      (by simpa only [c.right_inv hzt] using (hball hy.2).1)
      F (hF.of_le (by simp)) heF v
    rw [← hclosed c hc (c.symm z) hq] at hh
    simpa only [Pi.zero_apply, map_zero, zero_apply, c.right_inv hzt] using hh.symm
  let P : Euclidean n → ℝ := fun y => curveIntegral ω (Path.segment (c p).val y)
  have hP : ContDiffOn ℝ (⊤ : ℕ∞) P (Metric.ball (c p).val r) :=
    radial_integral_smooth ω U hU hω (c p).val r hr (fun y hy => (hball hy).1)
  have hder (y : Euclidean n) (hy : y ∈ s) : fderiv ℝ P y = ω y := by
    have hd := hs.hasFDerivWithinAt_curveIntegral_segment_of_hasFDerivWithinAt_symmetric
      (ω := ω) (dω := fderiv ℝ ω)
      (fun y hy => ((hω.contDiffAt (hU.mem_nhds (hball hy.2).1)).differentiableAt
        (by simp)).hasFDerivAt.hasFDerivWithinAt)
      (fun y hy u _ v _ => hsymm y hy u v)
      ⟨(c p).property, Metric.mem_ball_self hr⟩ hy
    exact ((uniqueDiffOn_modelSet n k).inter Metric.isOpen_ball y hy).eq
      (((hP.contDiffAt (Metric.isOpen_ball.mem_nhds hy.2)).differentiableAt
        (by simp)).hasFDerivAt.hasFDerivWithinAt) hd
  refine ⟨r, hr, P, hP, ?_⟩
  intro z hz
  have hzt := htarget z hz
  refine ⟨hzt, ?_⟩
  intro j
  rw [hder z.val ⟨z.property, hz⟩]
  change coefficientOneLinear n (F z.val) (Pi.single j 1) = _
  have he := heF ⟨c.symm z, c.map_target hzt⟩
    (by simpa only [c.right_inv hzt] using (hball hz).1)
  dsimp only at he
  rw [c.right_inv hzt] at he
  rw [he]
  exact linear_coefficients C c hc α.field ⟨c.symm z, c.map_target hzt⟩ (Pi.single j 1)

/-- A global smooth representative of the local potential gives the required
local exactness, including points on a half-space face. -/
theorem local_primitives :
    Specs.SmoothManifolds.Integration.ClosedOneFormLocalPrimitives.local_primitivesType.{u} := by
  intro n k M _ S C α hclosed p
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨r, hr, P, hP, hder⟩ := chart_primitive S C α hclosed c hc p hp
  let f : M → ℝ := fun q => P (c q).val
  have hf : ScalarContDiffAt (⊤ : ℕ∞) S.smoothStructure.val f p := by
    apply scalarContDiffAt_of_chart S.smoothStructure.property.1 hc hp
    exact ⟨Metric.ball (c p).val r, Metric.isOpen_ball, Metric.mem_ball_self hr,
      P, hP, Filter.EventuallyEq.rfl⟩
  obtain ⟨g, hg, heq⟩ := exists_global_representative S p f hf
  have hcoord : ContinuousAt (fun q => (c q).val) p :=
    continuous_subtype_val.continuousAt.comp (c.continuousAt hp)
  have hev : ∀ᶠ q in 𝓝 p, q ∈ c.source ∧ (c q).val ∈ Metric.ball (c p).val r ∧
      g =ᶠ[𝓝 q] f := by
    filter_upwards [c.open_source.mem_nhds hp,
      hcoord.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr)),
      heq.eventuallyEq_nhds] with q hqc hqb hq
    exact ⟨hqc, hqb, hq⟩
  obtain ⟨V, hV, hVopen, hpV⟩ := eventually_nhds_iff.mp hev
  refine ⟨V, g, hg, hVopen, hpV, ?_⟩
  intro q hqV
  obtain ⟨hqc, hqb, hqeq⟩ := hV q hqV
  have hG : GermChartExtension S q c (functionGerm S g hg q) P :=
    ⟨⟨Metric.ball (c p).val r, Metric.isOpen_ball, hqb, hP⟩, hqeq.symm.germ_eq⟩
  obtain ⟨hqt, hqder⟩ := hder (c q) hqb
  have hqder' (j : Fin n) : fderiv ℝ P (c q).val (Pi.single j 1) =
      α.field q (coordinateVector C.tangent.fiberCoordinates c hc q hqc j) := by
    let Q : c.source → ℝ := fun w => α.field w.val
      (coordinateVector C.tangent.fiberCoordinates c hc w.val w.property j)
    have hsub : (⟨c.symm (c q), c.map_target hqt⟩ : c.source) = ⟨q, hqc⟩ :=
      Subtype.ext (c.left_inv hqc)
    have hh := hqder j
    change fderiv ℝ P (c q).val (Pi.single j 1) = Q ⟨c.symm (c q), c.map_target hqt⟩ at hh
    rw [hsub] at hh
    exact hh
  rw [(Covectors.differential_coordinates S C g hg c hc q hqc P hG).2,
    Covectors.covector_expansion C.tangent.fiberCoordinates c hc q hqc (α.field q)]
  simp_rw [hqder']

end SmoothManifolds.ClosedOneFormLocalPrimitives
