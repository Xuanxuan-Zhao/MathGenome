import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.SurfaceConnectionForm
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.LeviCivita
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.CurvatureAlgebra
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.ConnectionForms
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.SmoothMetrics
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.SurfaceBoundaryGeometry
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

/-! Smooth positive moving frames and their literal scalar connection form,
for paper.tex 4937–4951. All tangent fibers and differentials are the shared
intrinsic ones. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
open Set Filter
open scoped Topology BigOperators ContDiff
namespace P202.SurfaceConnectionForm
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
open P202.ConnectionData P202.MetricData P202.CurvatureData P202.SurfaceBoundaryData
open P202Specs.PlanarRegionTopology P202Specs.SurfaceConnectionForm
universe u v
variable {M : Type u} [TopologicalSpace M] {S : SmoothManifold 2 .euclidean M}

theorem referencePair_independent (g : RiemannianMetric S) (p : M) :
    LinearIndependent ℝ ![referenceBasis g p 0, referenceBasis g p 1] := by
  have he : ![referenceBasis g p 0, referenceBasis g p 1] = referenceBasis g p := by
    funext i
    fin_cases i <;> rfl
  rw [he]
  exact (referenceBasis g p).linearIndependent

/-- The scalar in the independent Specs is literal sectional curvature. -/
theorem gaussianCurvature_eq_referenceSectional (g : RiemannianMetric S)
    (T : CurvatureTensor S) (p : M) :
    gaussianCurvature g T p = sectionalCurvature g T p
      (referenceBasis g p 0) (referenceBasis g p 1) (referencePair_independent g p) := rfl

/-- Its value is independent of the chosen tangent two-plane basis. This
connects the target's Gaussian scalar to the upstream curvature convention. -/
theorem gaussianCurvature_eq_sectional (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : P202.LeviCivitaData.IsLeviCivita g C)
    (T : CurvatureTensor S) (hT : RepresentsCurvature C T) (p : M)
    (X Y : TangentSpace S p) (hXY : LinearIndependent ℝ ![X,Y]) :
    gaussianCurvature g T p = sectionalCurvature g T p X Y hXY := by
  rw [gaussianCurvature_eq_referenceSectional]
  apply P202.Geometry.CurvatureAlgebra.sectional_basis_independent g C hC T hT p
  have hdim : Fintype.card (Fin 2) = Module.finrank ℝ (TangentSpace S p) := by
    simpa using (SmoothManifolds.tangent_dimension S p).2.symm
  have hleft := (referenceBasis g p).span_eq
  rw [← show ![referenceBasis g p 0, referenceBasis g p 1] = referenceBasis g p by
    funext i; fin_cases i <;> rfl] at hleft
  have hright : Submodule.span ℝ (Set.range ![X,Y]) = ⊤ :=
    LinearIndependent.span_eq_top_of_card_eq_finrank (K := ℝ) (V := TangentSpace S p)
      (ι := Fin 2) hXY hdim
  simpa only [Matrix.range_cons_cons_empty] using hleft.trans hright.symm

/-- In an orthonormal pair, the coefficient of R(e₁,e₂)e₁ along e₂ is
minus K. This is the curvature-sign part of dω = -K dA; identifying that
coefficient with dω still requires the local connection calculation. -/
theorem curvature_coefficient_sign (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : P202.LeviCivitaData.IsLeviCivita g C)
    (T : CurvatureTensor S) (hT : RepresentsCurvature C T) (p : M)
    (X Y : TangentSpace S p) (hXY : LinearIndependent ℝ ![X,Y])
    (hXX : pairing g p X X = 1) (hYY : pairing g p Y Y = 1)
    (horth : pairing g p X Y = 0) :
    curvatureForm g T p X Y X Y = -gaussianCurvature g T p := by
  rw [gaussianCurvature_eq_sectional g C hC T hT p X Y hXY]
  have hskew := (P202.Geometry.CurvatureAlgebra.symmetries g C hC T hT p X Y X Y).2.1
  simpa only [P202.CurvatureData.sectionalCurvature, hXX, hYY, horth,
    zero_pow (by decide : 2 ≠ 0), mul_one, sub_zero, div_one] using hskew

section LocalOrthonormalFrame
open SmoothManifolds.BundleData

theorem scalarDerivative_eq_zero_of_eventually_const (f : M → ℝ) (p : M) (a : ℝ)
    (hf : f =ᶠ[𝓝 p] (fun _ => a)) (v : TangentSpace S p) :
    scalarDerivative S f p v = 0 := by
  let aS : SmoothManifolds.GlobalSmooth S := algebraMap ℝ (SmoothManifolds.GlobalSmooth S) a
  have haS : aS.val =ᶠ[𝓝 p] f := hf.symm
  rw [P202.Geometry.ConnectionForms.scalarDerivative_representative f aS p haS]
  change v.val (SmoothManifolds.globalToGerm S p (algebraMap ℝ (SmoothManifolds.GlobalSmooth S) a)) = 0
  rw [(SmoothManifolds.globalToGerm S p).commutes]
  exact SmoothManifolds.derivation_kills_constants _ v a


theorem orthonormalFrame_coefficient (g : RiemannianMetric S)
    {U : Set M} {hU : IsOpen U} (b : LocalFrame (tangentBundle S) U hU)
    (hon : ∀ p i j, pairing g p.val (b.section_ i p) (b.section_ j p) =
      if i = j then 1 else 0) (p : U) (v : TangentSpace S p.val) (i : Fin 2) :
    (b.basis p).equivFun v i = pairing g p.val v (b.section_ i p) := by
  have he := (b.basis p).equivFun_symm_apply ((b.basis p).equivFun v)
  rw [LinearEquiv.symm_apply_apply] at he
  symm
  calc
    pairing g p.val v (b.section_ i p) =
        pairing g p.val (∑ k, (b.basis p).equivFun v k • b.section_ k p) (b.section_ i p) := by
      apply congrArg (fun w => pairing g p.val w (b.section_ i p))
      simpa only [b.basis_eq] using he
    _ = (b.basis p).equivFun v i := by
      simp only [LinearMap.BilinForm.sum_left, LinearMap.BilinForm.smul_left, hon]
      simp

theorem local_metric_derivative_of_constant (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : P202.LeviCivitaData.IsMetricCompatible g C)
    {U : Set M} (hU : IsOpen U)
    (s t : LocalSection (tangentBundle S) U hU) (a : ℝ)
    (hconst : ∀ q : U, pairing g q.val (s.val q) (t.val q) = a)
    (p : U) (v : TangentSpace S p.val) :
    pairing g p.val
        (pointDerivative C (SmoothManifolds.SectionExtension.totalSection s.val) p.val v)
        (t.val p) +
      pairing g p.val (s.val p)
        (pointDerivative C (SmoothManifolds.SectionExtension.totalSection t.val) p.val v) = 0 := by
  obtain ⟨s', hs⟩ := P202.Geometry.ConnectionForms.exists_section_representative
    (tangentBundle S) U hU (SmoothManifolds.SectionExtension.totalSection s.val)
    (SmoothManifolds.SectionExtension.totalSection_smooth (tangentBundle S) hU _ s.property)
    p.val p.property
  obtain ⟨t', ht⟩ := P202.Geometry.ConnectionForms.exists_section_representative
    (tangentBundle S) U hU (SmoothManifolds.SectionExtension.totalSection t.val)
    (SmoothManifolds.SectionExtension.totalSection_smooth (tangentBundle S) hU _ t.property)
    p.val p.property
  have hsval : s'.val p.val = s.val p := by
    simpa using hs.self_of_nhds
  have htval : t'.val p.val = t.val p := by
    simpa using ht.self_of_nhds
  have hsD := P202.Geometry.ConnectionForms.pointDerivative_congr (tangentBundle S) C
    s'.val (SmoothManifolds.SectionExtension.totalSection s.val) p.val
    ⟨s', Filter.Eventually.of_forall (fun _ => rfl)⟩ hs
  have htD := P202.Geometry.ConnectionForms.pointDerivative_congr (tangentBundle S) C
    t'.val (SmoothManifolds.SectionExtension.totalSection t.val) p.val
    ⟨t', Filter.Eventually.of_forall (fun _ => rfl)⟩ ht
  change pointDerivative C s'.val p.val =
    pointDerivative C (SmoothManifolds.SectionExtension.totalSection s.val) p.val at hsD
  change pointDerivative C t'.val p.val =
    pointDerivative C (SmoothManifolds.SectionExtension.totalSection t.val) p.val at htD
  obtain ⟨X, hX⟩ := P202.Geometry.ConnectionForms.section_evaluation_surjective
    (tangentBundle S) p.val v
  have hconst' : (fun q => pairing g q (s'.val q) (t'.val q)) =ᶠ[𝓝 p.val]
      (fun _ => a) := by
    filter_upwards [hs, ht, hU.mem_nhds p.property] with q hsq htq hq
    rw [hsq, htq]
    simpa only [SmoothManifolds.SectionExtension.totalSection_of_mem _ q hq] using hconst ⟨q, hq⟩
  have hm := hC X s' t' p.val
  rw [scalarDerivative_eq_zero_of_eventually_const _ _ a hconst'] at hm
  rw [← hsD, ← htD, ← hsval, ← htval, ← hX,
    P202.Geometry.ConnectionForms.pointDerivative_global,
    P202.Geometry.ConnectionForms.pointDerivative_global]
  exact hm.symm

theorem orthonormalFrame_connectionForm_skew (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : P202.LeviCivitaData.IsMetricCompatible g C)
    {U : Set M} {hU : IsOpen U} (b : LocalFrame (tangentBundle S) U hU)
    (hon : ∀ p i j, pairing g p.val (b.section_ i p) (b.section_ j p) =
      if i = j then 1 else 0) (p : U) (v : TangentSpace S p.val) (i j : Fin 2) :
    connectionForm C b p i j v = -connectionForm C b p j i v := by
  have hm := local_metric_derivative_of_constant g C hC hU
    ⟨b.section_ j, b.smooth j⟩ ⟨b.section_ i, b.smooth i⟩
    (if j = i then 1 else 0) (fun q => hon q j i) p v
  change pairing g p.val
      (pointDerivative C (SmoothManifolds.SectionExtension.totalSection (b.section_ j)) p.val v)
      (b.section_ i p) +
    pairing g p.val (b.section_ j p)
      (pointDerivative C (SmoothManifolds.SectionExtension.totalSection (b.section_ i)) p.val v) = 0 at hm
  change (b.basis p).equivFun
    (pointDerivative C (SmoothManifolds.SectionExtension.totalSection (b.section_ j)) p.val v) i =
    -(b.basis p).equivFun
      (pointDerivative C (SmoothManifolds.SectionExtension.totalSection (b.section_ i)) p.val v) j
  rw [orthonormalFrame_coefficient g b hon p _ i,
    orthonormalFrame_coefficient g b hon p _ j]
  have hsym := g.symmetric p.val (b.section_ j p)
    (pointDerivative C (SmoothManifolds.SectionExtension.totalSection (b.section_ i)) p.val v)
  change pairing g p.val (b.section_ j p) _ = pairing g p.val _ (b.section_ j p) at hsym
  rw [hsym] at hm
  linarith

theorem scalarDerivative_congr_germ (f g : M → ℝ) (p : M)
    (hfg : f =ᶠ[𝓝 p] g) : scalarDerivative S f p = scalarDerivative S g p := by
  have hsmooth : SmoothManifolds.PartitionData.ScalarContDiffAt (⊤ : ℕ∞)
      S.smoothStructure.val f p ↔
    SmoothManifolds.PartitionData.ScalarContDiffAt (⊤ : ℕ∞)
      S.smoothStructure.val g p := by
    constructor
    · intro hf
      have hf' : SmoothManifolds.FrameData.VectorSmoothAt S.smoothStructure.val f p :=
        (SmoothManifolds.scalarContDiffAt_iff _ _ _ _).mp hf
      exact (SmoothManifolds.scalarContDiffAt_iff _ _ _ _).mpr (hf'.congr hfg)
    · intro hg
      have hg' : SmoothManifolds.FrameData.VectorSmoothAt S.smoothStructure.val g p :=
        (SmoothManifolds.scalarContDiffAt_iff _ _ _ _).mp hg
      exact (SmoothManifolds.scalarContDiffAt_iff _ _ _ _).mpr (hg'.congr hfg.symm)
  have hG : scalarGerm S f p = scalarGerm S g p := by
    by_cases hf : SmoothManifolds.PartitionData.ScalarContDiffAt (⊤ : ℕ∞)
        S.smoothStructure.val f p
    · have hg := hsmooth.mp hf
      simp only [scalarGerm, dite_eq_left hf, dite_eq_left hg]
      apply Subtype.ext
      exact Germ.coe_eq.mpr hfg
    · have hg := not_iff_not.mpr hsmooth |>.mp hf
      simp only [scalarGerm, dite_eq_right hf, dite_eq_right hg]
  unfold scalarDerivative
  rw [hG]

theorem orthonormalFrame_connectionForm_diagonal (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : P202.LeviCivitaData.IsMetricCompatible g C)
    {U : Set M} {hU : IsOpen U} (b : LocalFrame (tangentBundle S) U hU)
    (hon : ∀ p i j, pairing g p.val (b.section_ i p) (b.section_ j p) =
      if i = j then 1 else 0) (p : U) (v : TangentSpace S p.val) (i : Fin 2) :
    connectionForm C b p i i v = 0 := by
  linarith [orthonormalFrame_connectionForm_skew g C hC b hon p v i i]

theorem orthonormalFrame_derivative_first (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : P202.LeviCivitaData.IsMetricCompatible g C)
    {U : Set M} {hU : IsOpen U} (b : LocalFrame (tangentBundle S) U hU)
    (hon : ∀ p i j, pairing g p.val (b.section_ i p) (b.section_ j p) =
      if i = j then 1 else 0) (p : U) (v : TangentSpace S p.val) :
    pointDerivative C (SmoothManifolds.SectionExtension.totalSection (b.section_ 0)) p.val v =
      connectionForm C b p 1 0 v • b.section_ 1 p := by
  let D := pointDerivative C (SmoothManifolds.SectionExtension.totalSection (b.section_ 0)) p.val v
  have he := (b.basis p).equivFun_symm_apply ((b.basis p).equivFun D)
  rw [LinearEquiv.symm_apply_apply, Fin.sum_univ_two] at he
  have h00 : (b.basis p).equivFun D 0 = 0 :=
    orthonormalFrame_connectionForm_diagonal g C hC b hon p v 0
  change D = (b.basis p).equivFun D 1 • b.section_ 1 p
  simpa only [h00, zero_smul, zero_add, b.basis_eq] using he

theorem orthonormalFrame_derivative_second (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : P202.LeviCivitaData.IsMetricCompatible g C)
    {U : Set M} {hU : IsOpen U} (b : LocalFrame (tangentBundle S) U hU)
    (hon : ∀ p i j, pairing g p.val (b.section_ i p) (b.section_ j p) =
      if i = j then 1 else 0) (p : U) (v : TangentSpace S p.val) :
    pointDerivative C (SmoothManifolds.SectionExtension.totalSection (b.section_ 1)) p.val v =
      (-connectionForm C b p 1 0 v) • b.section_ 0 p := by
  let D := pointDerivative C (SmoothManifolds.SectionExtension.totalSection (b.section_ 1)) p.val v
  have he := (b.basis p).equivFun_symm_apply ((b.basis p).equivFun D)
  rw [LinearEquiv.symm_apply_apply, Fin.sum_univ_two] at he
  have h11 : (b.basis p).equivFun D 1 = 0 :=
    orthonormalFrame_connectionForm_diagonal g C hC b hon p v 1
  have h01 : (b.basis p).equivFun D 0 = -connectionForm C b p 1 0 v :=
    orthonormalFrame_connectionForm_skew g C hC b hon p v 0 1
  simpa only [h11, h01, zero_smul, add_zero, b.basis_eq] using he

/-- Evaluation of the local scalar connection form on a globally smooth field.
The zero extension is only used through its germ inside the frame domain. -/
def frameConnectionEvaluation (C : Connection (tangentBundle S))
    {U : Set M} {hU : IsOpen U} (b : LocalFrame (tangentBundle S) U hU)
    (X : Field S) : M → ℝ :=
  SmoothManifolds.FrameData.totalize
    (fun q : U => connectionForm C b q 1 0 (X.val q.val))

set_option maxHeartbeats 800000 in
/-- The two-dimensional local curvature coefficient, before passing to chart
coordinates. The displayed differential is the intrinsic differential of
actual local connection coefficients. -/
theorem orthonormalFrame_curvature_coefficient (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : P202.LeviCivitaData.IsMetricCompatible g C)
    (T : CurvatureTensor S) (hT : RepresentsCurvature C T)
    {U : Set M} {hU : IsOpen U} (b : LocalFrame (tangentBundle S) U hU)
    (hon : ∀ p i j, pairing g p.val (b.section_ i p) (b.section_ j p) =
      if i = j then 1 else 0) (X Y : Field S) (p : U) :
    curvatureForm g T p.val (X.val p.val) (Y.val p.val)
        (b.section_ 0 p) (b.section_ 1 p) =
      scalarDerivative S (frameConnectionEvaluation C b Y) p.val (X.val p.val) -
      scalarDerivative S (frameConnectionEvaluation C b X) p.val (Y.val p.val) -
      connectionForm C b p 1 0 ((P202.TorsionMetricData.bracket X Y).val p.val) := by
  obtain ⟨e, he⟩ := P202.Geometry.ConnectionForms.local_frame_representative
    (tangentBundle S) b p
  have heval (i : Fin 2) : (e i).val p.val = b.section_ i p := by
    simpa using (he i).self_of_nhds
  have hD (i : Fin 2) : ∀ᶠ q in 𝓝 p.val,
      pointDerivative C (e i).val q =
        pointDerivative C (SmoothManifolds.SectionExtension.totalSection (b.section_ i)) q := by
    filter_upwards [eventually_eventually_nhds.mpr (he i)] with q hq
    exact P202.Geometry.ConnectionForms.pointDerivative_congr (tangentBundle S) C _ _ q
      ⟨e i, Filter.Eventually.of_forall (fun _ => rfl)⟩ hq
  have hCov0 (Z : Field S) : ∀ᶠ q in 𝓝 p.val,
      (C.cov Z (e 0)).val q = frameConnectionEvaluation C b Z q • (e 1).val q := by
    filter_upwards [hD 0, he 1, hU.mem_nhds p.property] with q hDq heq hq
    calc
      (C.cov Z (e 0)).val q = pointDerivative C (e 0).val q (Z.val q) :=
        (P202.Geometry.ConnectionForms.pointDerivative_global (tangentBundle S) C (e 0) q Z).symm
      _ = pointDerivative C
          (SmoothManifolds.SectionExtension.totalSection (b.section_ 0)) q (Z.val q) :=
        congrArg (fun D => D (Z.val q)) hDq
      _ = connectionForm C b ⟨q, hq⟩ 1 0 (Z.val q) • b.section_ 1 ⟨q, hq⟩ :=
        orthonormalFrame_derivative_first g C hC b hon ⟨q, hq⟩ (Z.val q)
      _ = frameConnectionEvaluation C b Z q • (e 1).val q := by
        rw [heq]
        simp only [frameConnectionEvaluation, SmoothManifolds.FrameData.totalize_of_mem _ q hq,
          SmoothManifolds.SectionExtension.totalSection_of_mem _ q hq]
  have hCov1 (Z : Field S) : ∀ᶠ q in 𝓝 p.val,
      (C.cov Z (e 1)).val q = (-frameConnectionEvaluation C b Z q) • (e 0).val q := by
    filter_upwards [hD 1, he 0, hU.mem_nhds p.property] with q hDq heq hq
    calc
      (C.cov Z (e 1)).val q = pointDerivative C (e 1).val q (Z.val q) :=
        (P202.Geometry.ConnectionForms.pointDerivative_global (tangentBundle S) C (e 1) q Z).symm
      _ = pointDerivative C
          (SmoothManifolds.SectionExtension.totalSection (b.section_ 1)) q (Z.val q) :=
        congrArg (fun D => D (Z.val q)) hDq
      _ = (-connectionForm C b ⟨q, hq⟩ 1 0 (Z.val q)) • b.section_ 0 ⟨q, hq⟩ :=
        orthonormalFrame_derivative_second g C hC b hon ⟨q, hq⟩ (Z.val q)
      _ = (-frameConnectionEvaluation C b Z q) • (e 0).val q := by
        rw [heq]
        simp only [frameConnectionEvaluation, SmoothManifolds.FrameData.totalize_of_mem _ q hq,
          SmoothManifolds.SectionExtension.totalSection_of_mem _ q hq]
  have hω (Z : Field S) :
      (fun q => pairing g q ((C.cov Z (e 0)).val q) ((e 1).val q)) =ᶠ[𝓝 p.val]
        frameConnectionEvaluation C b Z := by
    filter_upwards [hCov0 Z, he 1, hU.mem_nhds p.property] with q hCq heq hq
    rw [hCq, heq, SmoothManifolds.SectionExtension.totalSection_of_mem _ q hq]
    rw [LinearMap.BilinForm.smul_left]
    have h11 : pairing g q (b.section_ 1 ⟨q, hq⟩) (b.section_ 1 ⟨q, hq⟩) = 1 := by
      simpa only [ite_true] using hon ⟨q, hq⟩ 1 1
    rw [h11, mul_one]
  have hquadratic (Z W : Field S) :
      pairing g p.val ((C.cov Z (e 0)).val p.val) ((C.cov W (e 1)).val p.val) = 0 := by
    rw [(hCov0 Z).self_of_nhds, (hCov1 W).self_of_nhds, heval 0, heval 1]
    simp only [LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right,
      hon, (by decide : (1 : Fin 2) ≠ 0), ite_false, mul_zero]
  have hmXY := hC X (C.cov Y (e 0)) (e 1) p.val
  have hmYX := hC Y (C.cov X (e 0)) (e 1) p.val
  rw [scalarDerivative_congr_germ _ _ p.val (hω Y), hquadratic Y X, add_zero] at hmXY
  rw [scalarDerivative_congr_germ _ _ p.val (hω X), hquadratic X Y, add_zero] at hmYX
  have hbr := (hω (P202.TorsionMetricData.bracket X Y)).self_of_nhds
  simp only [frameConnectionEvaluation, SmoothManifolds.FrameData.totalize_of_mem _ p.val p.property] at hbr
  unfold curvatureForm
  rw [← heval 0, ← heval 1, hT X Y (e 0) p.val,
    P202.Geometry.CurvatureAlgebra.curvature_apply]
  simp only [P202.Geometry.LeviCivita.tangent_sub_as_add,
    LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left]
  rw [← hmXY, ← hmYX, hbr]
  ring

end LocalOrthonormalFrame

section GramSchmidtFrames
set_option maxHeartbeats 800000
open Module SmoothManifolds.BundleData SmoothManifolds.FrameData SmoothManifolds.MapData

def gramResidual (g : RiemannianMetric S) (p : M)
    (b : Basis (Fin 2) ℝ (TangentSpace S p)) : TangentSpace S p :=
  b 1 + (-(pairing g p (b 0) (b 1) / pairing g p (b 0) (b 0))) • b 0

theorem gramResidual_ne_zero (g : RiemannianMetric S) (p : M)
    (b : Basis (Fin 2) ℝ (TangentSpace S p)) : gramResidual g p b ≠ 0 := by
  intro h
  have h' := congrArg (fun v => b.repr v 1) h
  simp only [gramResidual, map_add, map_smul, b.repr_self, Finsupp.add_apply,
    Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, ite_true,
    show (0 : Fin 2) ≠ 1 from by decide, ite_false, mul_zero, add_zero, map_zero,
    Finsupp.zero_apply, one_ne_zero] at h'

theorem gramResidual_orthogonal (g : RiemannianMetric S) (p : M)
    (b : Basis (Fin 2) ℝ (TangentSpace S p)) :
    pairing g p (b 0) (gramResidual g p b) = 0 := by
  have hE : pairing g p (b 0) (b 0) ≠ 0 := ne_of_gt (g.positive p (b 0) (b.ne_zero 0))
  simp only [gramResidual, LinearMap.BilinForm.add_right,
    LinearMap.BilinForm.smul_right]
  field_simp [hE]
  ring

theorem gramResidual_sq (g : RiemannianMetric S) (p : M)
    (b : Basis (Fin 2) ℝ (TangentSpace S p)) :
    pairing g p (gramResidual g p b) (gramResidual g p b) =
      pairing g p (b 1) (b 1) -
        pairing g p (b 0) (b 1) ^ 2 / pairing g p (b 0) (b 0) := by
  have hE : pairing g p (b 0) (b 0) ≠ 0 := ne_of_gt (g.positive p (b 0) (b.ne_zero 0))
  have hsym : pairing g p (b 1) (b 0) = pairing g p (b 0) (b 1) :=
    g.symmetric p _ _
  simp only [gramResidual, LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
    LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hsym]
  field_simp [hE]
  ring

theorem schurComplement_pos (g : RiemannianMetric S) (p : M)
    (b : Basis (Fin 2) ℝ (TangentSpace S p)) :
    0 < pairing g p (b 1) (b 1) -
      pairing g p (b 0) (b 1) ^ 2 / pairing g p (b 0) (b 0) := by
  rw [← gramResidual_sq]
  exact g.positive p _ (gramResidual_ne_zero g p b)

def gramSchmidtPair (g : RiemannianMetric S) (p : M)
    (b : Basis (Fin 2) ℝ (TangentSpace S p)) : Fin 2 → TangentSpace S p :=
  ![(tangentNorm g p (b 0))⁻¹ • b 0,
    (tangentNorm g p (gramResidual g p b))⁻¹ • gramResidual g p b]

theorem normalize_pairing_self (g : RiemannianMetric S) (p : M)
    (v : TangentSpace S p) (hv : v ≠ 0) :
    pairing g p ((tangentNorm g p v)⁻¹ • v) ((tangentNorm g p v)⁻¹ • v) = 1 := by
  have hE : 0 < pairing g p v v := g.positive p v hv
  have hn : tangentNorm g p v ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hE)
  have hsq : tangentNorm g p v ^ 2 = pairing g p v v := Real.sq_sqrt hE.le
  simp only [LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right]
  field_simp [hn]
  exact hsq.symm

theorem gramSchmidtPair_orthonormal (g : RiemannianMetric S) (p : M)
    (b : Basis (Fin 2) ℝ (TangentSpace S p)) (i j : Fin 2) :
    pairing g p (gramSchmidtPair g p b i) (gramSchmidtPair g p b j) =
      if i = j then 1 else 0 := by
  have h01 := gramResidual_orthogonal g p b
  have h10 : pairing g p (gramResidual g p b) (b 0) = 0 :=
    (g.symmetric p _ _).trans h01
  fin_cases i <;> fin_cases j
  · exact normalize_pairing_self g p _ (b.ne_zero 0)
  · change pairing g p ((tangentNorm g p (b 0))⁻¹ • b 0)
      ((tangentNorm g p (gramResidual g p b))⁻¹ • gramResidual g p b) = 0
    simp only [LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, h01, mul_zero]
  · change pairing g p ((tangentNorm g p (gramResidual g p b))⁻¹ • gramResidual g p b)
      ((tangentNorm g p (b 0))⁻¹ • b 0) = 0
    simp only [LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, h10, mul_zero]
  · exact normalize_pairing_self g p _ (gramResidual_ne_zero g p b)

theorem bilinear_orthonormal_linearIndependent {V : Type*} [AddCommMonoid V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V) (f : Fin 2 → V)
    (hf : ∀ i j, B (f i) (f j) = if i = j then 1 else 0) :
    LinearIndependent ℝ f := by
  classical
  apply (Fintype.linearIndependent_iffₛ (R := ℝ) (v := f)).mpr
  intro w z hw j
  have hj := congrArg (fun v => B v (f j)) hw
  simpa only [LinearMap.BilinForm.sum_left, LinearMap.BilinForm.smul_left,
    hf, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using hj

theorem gramSchmidtPair_linearIndependent (g : RiemannianMetric S) (p : M)
    (b : Basis (Fin 2) ℝ (TangentSpace S p)) :
    LinearIndependent ℝ (gramSchmidtPair g p b) :=
  bilinear_orthonormal_linearIndependent (pairing g p) _
    (gramSchmidtPair_orthonormal g p b)

theorem gramSchmidtPair_span (g : RiemannianMetric S) (p : M)
    (b : Basis (Fin 2) ℝ (TangentSpace S p)) :
    ⊤ ≤ Submodule.span ℝ (Set.range (gramSchmidtPair g p b)) := by
  let W := Submodule.span ℝ (Set.range (gramSchmidtPair g p b))
  have h0 : b 0 ∈ W := by
    have he : gramSchmidtPair g p b 0 ∈ W := Submodule.subset_span ⟨0, rfl⟩
    have hn : tangentNorm g p (b 0) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr (g.positive p _ (b.ne_zero 0)))
    have hscale : tangentNorm g p (b 0) • gramSchmidtPair g p b 0 = b 0 := by
      change tangentNorm g p (b 0) • ((tangentNorm g p (b 0))⁻¹ • b 0) = b 0
      rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
    rw [← hscale]
    exact W.smul_mem _ he
  have hr : gramResidual g p b ∈ W := by
    have he : gramSchmidtPair g p b 1 ∈ W := Submodule.subset_span ⟨1, rfl⟩
    have hn : tangentNorm g p (gramResidual g p b) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr (g.positive p _ (gramResidual_ne_zero g p b)))
    have hscale : tangentNorm g p (gramResidual g p b) • gramSchmidtPair g p b 1 =
        gramResidual g p b := by
      change tangentNorm g p (gramResidual g p b) •
        ((tangentNorm g p (gramResidual g p b))⁻¹ • gramResidual g p b) = _
      rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
    rw [← hscale]
    exact W.smul_mem _ he
  have h1 : b 1 ∈ W := by
    have heq : b 1 = gramResidual g p b +
        (pairing g p (b 0) (b 1) / pairing g p (b 0) (b 0)) • b 0 := by
      simp only [gramResidual, add_assoc, ← add_smul, neg_add_cancel, zero_smul, add_zero]
    rw [heq]
    exact W.add_mem hr (W.smul_mem _ h0)
  rw [← b.span_eq]
  apply Submodule.span_le.mpr
  rintro v ⟨i, rfl⟩
  fin_cases i
  · exact h0
  · exact h1

def gramSchmidtBasis (g : RiemannianMetric S) (p : M)
    (b : Basis (Fin 2) ℝ (TangentSpace S p)) : Basis (Fin 2) ℝ (TangentSpace S p) :=
  Basis.mk (gramSchmidtPair_linearIndependent g p b) (gramSchmidtPair_span g p b)

@[simp] theorem gramSchmidtBasis_apply (g : RiemannianMetric S) (p : M)
    (b : Basis (Fin 2) ℝ (TangentSpace S p)) (i : Fin 2) :
    gramSchmidtBasis g p b i = gramSchmidtPair g p b i := Basis.mk_apply _ _ _

theorem gramSchmidt_diagonal_product (g : RiemannianMetric S) (p : M)
    (b : Basis (Fin 2) ℝ (TangentSpace S p)) :
    tangentNorm g p (b 0) * tangentNorm g p (gramResidual g p b) =
      Real.sqrt (pairing g p (b 0) (b 0) * pairing g p (b 1) (b 1) -
        pairing g p (b 0) (b 1) ^ 2) := by
  have hE : 0 < pairing g p (b 0) (b 0) := g.positive p _ (b.ne_zero 0)
  have heq : pairing g p (b 0) (b 0) *
      pairing g p (gramResidual g p b) (gramResidual g p b) =
      pairing g p (b 0) (b 0) * pairing g p (b 1) (b 1) -
        pairing g p (b 0) (b 1) ^ 2 := by
    rw [gramResidual_sq]
    field_simp [ne_of_gt hE]
  rw [← heq, Real.sqrt_mul hE.le]
  rfl

/-- A smooth metric evaluated on the actual smooth members of a local frame
has smooth Gram coefficients in the restricted manifold atlas. -/
theorem localFrame_pairing_smooth (g : RiemannianMetric S)
    {U : Set M} {hU : IsOpen U} (b : LocalFrame (tangentBundle S) U hU)
    (i j : Fin 2) :
    VectorSmooth (openSubsetAtlas S.smoothStructure.val U hU)
      (fun p : U => pairing g p.val (b.section_ i p) (b.section_ j p)) := by
  intro p
  obtain ⟨e, he⟩ := P202.Geometry.ConnectionForms.local_frame_representative
    (tangentBundle S) b p
  have hsm := P202.Geometry.SmoothMetrics.metric_pairing_smoothAt S
    (tangentBundle S) g id (fun q => (e i).val q) (fun q => (e j).val q) p.val
    (SmoothManifolds.manifoldContDiff_id (⊤ : ℕ∞) _ S.smoothStructure.property.1 p.val)
    ((e i).property p.val) ((e j).property p.val)
  have hres := SmoothManifolds.OrientationResults.vectorSmoothAt_restrict U hU p hsm
  apply hres.congr
  filter_upwards [continuousAt_subtype_val.eventually (he i),
    continuousAt_subtype_val.eventually (he j)] with q hi hj
  rw [SmoothManifolds.SectionExtension.totalSection_of_mem _ q.val q.property] at hi hj
  exact congrArg₂ (fun v w => pairing g q.val v w) hi hj

theorem scalarSmoothAt_inv {n : ℕ} {a : SmoothManifolds.ModelKind} {X : Type*}
    [TopologicalSpace X] {A : Set (ModelChart n a X)} {f : X → ℝ} {p : X}
    (hf : VectorSmoothAt A f p) (hp : f p ≠ 0) :
    VectorSmoothAt A (fun q => (f q)⁻¹) p := by
  apply hf.postcompOn (isClosed_singleton.isOpen_compl) hp
  intro r hr
  exact (contDiffAt_id.inv hr).contDiffWithinAt

theorem scalarSmoothAt_sqrt {n : ℕ} {a : SmoothManifolds.ModelKind} {X : Type*}
    [TopologicalSpace X] {A : Set (ModelChart n a X)} {f : X → ℝ} {p : X}
    (hf : VectorSmoothAt A f p) (hp : 0 < f p) :
    VectorSmoothAt A (fun q => Real.sqrt (f q)) p := by
  apply hf.postcompOn isOpen_Ioi hp
  intro r hr
  exact (Real.contDiffAt_sqrt (ne_of_gt hr)).contDiffWithinAt

/-- The explicit Gram–Schmidt basis varies smoothly in the original tangent
bundle when the input local frame does. -/
theorem gramSchmidtPair_smooth (g : RiemannianMetric S)
    {U : Set M} {hU : IsOpen U} (b : LocalFrame (tangentBundle S) U hU)
    (i : Fin 2) :
    ManifoldSmooth (openSubsetAtlas S.smoothStructure.val U hU)
      (tangentBundle S).totalManifold.smoothStructure.val
      (fun p : U => (⟨p.val, gramSchmidtPair g p.val (b.basis p) i⟩ :
        Bundle.TotalSpace (Euclidean 2) (TangentSpace S))) := by
  apply (SmoothManifolds.Frames.smooth_section_iff_coefficients
    (tangentBundle S) U hU b _).mpr
  intro j p
  have hE := localFrame_pairing_smooth g b 0 0 p
  have hF := localFrame_pairing_smooth g b 0 1 p
  have hG := localFrame_pairing_smooth g b 1 1 p
  simp only [← b.basis_eq] at hE hF hG
  have hEp : 0 < pairing g p.val (b.basis p 0) (b.basis p 0) :=
    g.positive p.val _ ((b.basis p).ne_zero 0)
  have hiE := scalarSmoothAt_inv hE (ne_of_gt hEp)
  have hquot := (hF.prod hiE).postcomp (contDiff_fst.mul contDiff_snd)
  have hFF := (hF.prod hF).postcomp (contDiff_fst.mul contDiff_snd)
  have hFFdiv := (hFF.prod hiE).postcomp (contDiff_fst.mul contDiff_snd)
  have hH := (hG.prod hFFdiv).postcomp (contDiff_fst.sub contDiff_snd)
  have hHp : 0 < pairing g p.val (b.basis p 1) (b.basis p 1) -
      pairing g p.val (b.basis p 0) (b.basis p 1) *
        pairing g p.val (b.basis p 0) (b.basis p 1) *
          (pairing g p.val (b.basis p 0) (b.basis p 0))⁻¹ := by
    simpa only [pow_two, div_eq_mul_inv] using schurComplement_pos g p.val (b.basis p)
  have ha := scalarSmoothAt_inv (scalarSmoothAt_sqrt hE hEp)
    (ne_of_gt (Real.sqrt_pos.mpr hEp))
  have hd := scalarSmoothAt_inv (scalarSmoothAt_sqrt hH hHp)
    (ne_of_gt (Real.sqrt_pos.mpr hHp))
  have hcoeff (q : U) : coefficients b
      (fun q => gramSchmidtPair g q.val (b.basis q) i) q j =
      if i = 0 then
        (tangentNorm g q.val (b.basis q 0))⁻¹ * (if j = 0 then 1 else 0)
      else (tangentNorm g q.val (gramResidual g q.val (b.basis q)))⁻¹ *
        ((if j = 1 then 1 else 0) -
          (pairing g q.val (b.basis q 0) (b.basis q 1) /
            pairing g q.val (b.basis q 0) (b.basis q 0)) * (if j = 0 then 1 else 0)) := by
    fin_cases i <;> fin_cases j <;>
      simp [coefficients, gramSchmidtPair, gramResidual, map_add, map_smul,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [hcoeff]
  fin_cases i <;> fin_cases j
  · simpa [tangentNorm] using ha
  · simpa using (VectorSmoothAt.const _ (0 : ℝ) p)
  · have hnegquot := hquot.postcomp contDiff_neg
    have hmul := (hd.prod hnegquot).postcomp (contDiff_fst.mul contDiff_snd)
    convert hmul using 1
    funext q
    simp [tangentNorm, gramResidual_sq, div_eq_mul_inv, pow_two]
  · convert hd using 1
    funext q
    simp [tangentNorm, gramResidual_sq, div_eq_mul_inv, pow_two]

def gramSchmidtFrame (g : RiemannianMetric S)
    {U : Set M} {hU : IsOpen U} (b : LocalFrame (tangentBundle S) U hU) :
    LocalFrame (tangentBundle S) U hU where
  section_ i p := gramSchmidtPair g p.val (b.basis p) i
  basis p := gramSchmidtBasis g p.val (b.basis p)
  basis_eq p i := gramSchmidtBasis_apply g p.val (b.basis p) i
  smooth i := gramSchmidtPair_smooth g b i

theorem gramSchmidtFrame_orthonormal (g : RiemannianMetric S)
    {U : Set M} {hU : IsOpen U} (b : LocalFrame (tangentBundle S) U hU)
    (p : U) (i j : Fin 2) :
    pairing g p.val ((gramSchmidtFrame g b).section_ i p)
      ((gramSchmidtFrame g b).section_ j p) = if i = j then 1 else 0 :=
  gramSchmidtPair_orthonormal g p.val (b.basis p) i j

end GramSchmidtFrames

section GramSchmidtCoordinates
set_option maxHeartbeats 800000
open Module SmoothManifolds.BundleData SmoothManifolds.FrameData SmoothManifolds.MapData

theorem gramSchmidtBasis_coefficient (g : RiemannianMetric S) (p : M)
    (b : Basis (Fin 2) ℝ (TangentSpace S p)) (v : TangentSpace S p) (i : Fin 2) :
    (gramSchmidtBasis g p b).equivFun v i =
      pairing g p v (gramSchmidtPair g p b i) := by
  let e := gramSchmidtBasis g p b
  have he := e.equivFun_symm_apply (e.equivFun v)
  rw [LinearEquiv.symm_apply_apply] at he
  symm
  calc
    pairing g p v (gramSchmidtPair g p b i) =
      pairing g p (∑ k, e.equivFun v k • gramSchmidtPair g p b k)
        (gramSchmidtPair g p b i) := by
      apply congrArg (fun w => pairing g p w (gramSchmidtPair g p b i))
      simpa only [e, gramSchmidtBasis_apply] using he
    _ = e.equivFun v i := by
      simp only [LinearMap.BilinForm.sum_left, LinearMap.BilinForm.smul_left,
        gramSchmidtPair_orthonormal]
      simp

theorem gramSchmidtBasis_coordinates (g : RiemannianMetric S) (p : M)
    (b : Basis (Fin 2) ℝ (TangentSpace S p)) (x y : ℝ) :
    (gramSchmidtBasis g p b).equivFun (x • b 0 + y • b 1) =
      ![tangentNorm g p (b 0) * x +
          (pairing g p (b 0) (b 1) / tangentNorm g p (b 0)) * y,
        tangentNorm g p (gramResidual g p b) * y] := by
  have hE : 0 < pairing g p (b 0) (b 0) := g.positive p _ (b.ne_zero 0)
  have hH : 0 < pairing g p (gramResidual g p b) (gramResidual g p b) :=
    g.positive p _ (gramResidual_ne_zero g p b)
  have hnE : tangentNorm g p (b 0) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hE)
  have hnH : tangentNorm g p (gramResidual g p b) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hH)
  have hsE : tangentNorm g p (b 0) ^ 2 = pairing g p (b 0) (b 0) :=
    Real.sq_sqrt hE.le
  have hsH : tangentNorm g p (gramResidual g p b) ^ 2 =
      pairing g p (gramResidual g p b) (gramResidual g p b) := Real.sq_sqrt hH.le
  have h01 := gramResidual_orthogonal g p b
  have h10 : pairing g p (b 1) (b 0) = pairing g p (b 0) (b 1) :=
    g.symmetric p _ _
  have h1r : pairing g p (b 1) (gramResidual g p b) =
      pairing g p (gramResidual g p b) (gramResidual g p b) := by
    rw [gramResidual_sq]
    simp only [gramResidual, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.smul_right, h10]
    ring
  ext i
  rw [gramSchmidtBasis_coefficient]
  fin_cases i
  · change pairing g p (x • b 0 + y • b 1)
      ((tangentNorm g p (b 0))⁻¹ • b 0) =
        tangentNorm g p (b 0) * x +
          (pairing g p (b 0) (b 1) / tangentNorm g p (b 0)) * y
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left,
      LinearMap.BilinForm.smul_right, h10]
    rw [← hsE]
    field_simp [hnE]
  · change pairing g p (x • b 0 + y • b 1)
      ((tangentNorm g p (gramResidual g p b))⁻¹ • gramResidual g p b) =
        tangentNorm g p (gramResidual g p b) * y
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left,
      LinearMap.BilinForm.smul_right, h01, h1r, mul_zero, zero_add]
    rw [← hsH]
    field_simp [hnH]

theorem alternatingPair_shear {V W : Type*} [AddCommMonoid V] [Module ℝ V]
    [AddCommMonoid W] [Module ℝ W] (f : V [⋀^Fin 2]→ₗ[ℝ] W)
    (v w : V) (r : ℝ) : f ![v, w + r • v] = f ![v, w] := by
  classical
  have hu (z : V) : Function.update ![v,w] (1 : Fin 2) z = ![v,z] := by
    funext i
    fin_cases i <;> simp
  have hadd := f.map_update_add ![v,w] 1 w (r • v)
  have hsmul := f.map_update_smul ![v,w] 1 r v
  have hz : f ![v,v] = 0 := f.map_eq_zero_of_eq ![v,v]
    (i := 0) (j := 1) rfl (by decide)
  simp only [hu] at hadd hsmul
  rw [hsmul, hz, smul_zero, add_zero] at hadd
  exact hadd

theorem alternatingPair_smul {V W : Type*} [AddCommMonoid V] [Module ℝ V]
    [AddCommMonoid W] [Module ℝ W] (f : V [⋀^Fin 2]→ₗ[ℝ] W)
    (v w : V) (a d : ℝ) : f ![a • v, d • w] = (a*d) • f ![v,w] := by
  have heq : (fun i : Fin 2 => ![a,d] i • ![v,w] i) = ![a • v,d • w] := by
    funext i
    fin_cases i <;> rfl
  have hs := f.map_smul_univ ![a,d] ![v,w]
  rw [heq] at hs
  simpa only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] using hs

theorem gramSchmidtPair_wedge (g : RiemannianMetric S) (p : M)
    (b : Basis (Fin 2) ℝ (TangentSpace S p)) :
    exteriorPower.ιMulti ℝ 2 (gramSchmidtPair g p b) =
      ((tangentNorm g p (b 0))⁻¹ *
        (tangentNorm g p (gramResidual g p b))⁻¹) • exteriorPower.ιMulti ℝ 2 b := by
  change exteriorPower.ιMulti ℝ 2
    ![(tangentNorm g p (b 0))⁻¹ • b 0,
      (tangentNorm g p (gramResidual g p b))⁻¹ • gramResidual g p b] = _
  rw [alternatingPair_smul]
  unfold gramResidual
  rw [alternatingPair_shear]
  congr 1

/-- Gram–Schmidt preserves the given intrinsic determinant ray. -/
theorem gramSchmidtPair_positive (g : RiemannianMetric S) (p : M)
    (b : Basis (Fin 2) ℝ (TangentSpace S p))
    (o : SmoothManifolds.OrientationData.Orientation S)
    (hb : SmoothManifolds.OrientationData.IsPositive (o.val p)
      (exteriorPower.ιMulti ℝ 2 b)) :
    SmoothManifolds.OrientationData.IsPositive (o.val p)
      (exteriorPower.ιMulti ℝ 2 (gramSchmidtPair g p b)) := by
  obtain ⟨hb0, hbray⟩ := hb
  rw [← hbray]
  apply (SmoothManifolds.OrientationResults.positive_iff_pos_smul _ hb0 _).mpr
  refine ⟨_, mul_pos ?_ ?_, gramSchmidtPair_wedge g p b⟩
  · exact inv_pos.mpr (Real.sqrt_pos.mpr (g.positive p _ (b.ne_zero 0)))
  · exact inv_pos.mpr (Real.sqrt_pos.mpr (g.positive p _ (gramResidual_ne_zero g p b)))

theorem gramSchmidtBasis_equivFun_coordinates (g : RiemannianMetric S) (p : M)
    (b : Basis (Fin 2) ℝ (TangentSpace S p)) (v : TangentSpace S p) :
    (gramSchmidtBasis g p b).equivFun v =
      ![tangentNorm g p (b 0) * b.equivFun v 0 +
          (pairing g p (b 0) (b 1) / tangentNorm g p (b 0)) * b.equivFun v 1,
        tangentNorm g p (gramResidual g p b) * b.equivFun v 1] := by
  have hv : b.equivFun v 0 • b 0 + b.equivFun v 1 • b 1 = v := by
    simpa only [Fin.sum_univ_two] using b.sum_equivFun v
  calc
    (gramSchmidtBasis g p b).equivFun v =
        (gramSchmidtBasis g p b).equivFun (b.equivFun v 0 • b 0 + b.equivFun v 1 • b 1) :=
      congrArg _ hv.symm
    _ = _ := gramSchmidtBasis_coordinates g p b _ _

theorem gramSchmidtFrame_positive (g : RiemannianMetric S)
    {U : Set M} {hU : IsOpen U} (b : LocalFrame (tangentBundle S) U hU)
    (o : SmoothManifolds.OrientationData.Orientation S)
    (hb : ∀ p : U, SmoothManifolds.OrientationData.IsPositive (o.val p.val)
      (exteriorPower.ιMulti ℝ 2 (b.basis p))) (p : U) :
    SmoothManifolds.OrientationData.IsPositive (o.val p.val)
      (exteriorPower.ιMulti ℝ 2 ((gramSchmidtFrame g b).basis p)) := by
  have heq : (((gramSchmidtFrame g b).basis p) : Fin 2 → TangentSpace S p.val) =
      gramSchmidtPair g p.val (b.basis p) := by
    funext i
    exact gramSchmidtBasis_apply g p.val (b.basis p) i
  rw [heq]
  exact gramSchmidtPair_positive g p.val (b.basis p) o (hb p)

end GramSchmidtCoordinates

section ChartFrames
open Module SmoothManifolds.BundleData SmoothManifolds.FrameData SmoothManifolds.MapData
open SmoothManifolds.BundleOperationsData

/-- The canonical bundle trivialization has the original tangent coordinates. -/
theorem tangentCoordinates_eq (c : ModelChart 2 .euclidean M)
    (hc : c ∈ S.smoothStructure.val) (p : c.source) :
    (tangentBundle S).fiberCoordinates ⟨c, hc⟩ p.val
      (by rw [(tangentRealization S).baseSet]; exact p.property) =
      (tangentStructure S).fiberCoordinates.equiv c hc p.val p.property := by
  apply LinearEquiv.ext
  intro v
  exact (tangentRealization S).coordinates ⟨c, hc⟩ p.val p.property v

/-- An actual smooth local frame with the literal tangent coordinate basis. -/
def chartCoordinateFrame (c : ModelChart 2 .euclidean M)
    (hc : c ∈ S.smoothStructure.val) :
    LocalFrame (tangentBundle S) c.source c.open_source where
  section_ j p := coordinateBasis c hc p j
  basis p := coordinateBasis c hc p
  basis_eq _ _ := rfl
  smooth j := by
    let b := SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) ⟨c,hc⟩
    let d := restrictFrame (hU := c.open_source) b
      (by intro p hp; rw [(tangentRealization S).baseSet]; exact hp)
    have hd (p : c.source) : d.section_ j p = coordinateBasis c hc p j := by
      change ((Pi.basisFun ℝ (Fin 2)).map
        ((tangentBundle S).fiberCoordinates ⟨c,hc⟩ p.val _).symm) j = _
      rw [tangentCoordinates_eq]
      rfl
    simpa only [hd] using d.smooth j

/-- Gram–Schmidt of the actual coordinate frame, smooth on the whole source. -/
def chartOrthonormalFrame (g : RiemannianMetric S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val) :
    LocalFrame (tangentBundle S) c.source c.open_source :=
  gramSchmidtFrame g (chartCoordinateFrame c hc)

theorem chartOrthonormalFrame_orthonormal (g : RiemannianMetric S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (p : c.source) (i j : Fin 2) :
    pairing g p.val ((chartOrthonormalFrame g c hc).section_ i p)
      ((chartOrthonormalFrame g c hc).section_ j p) = if i = j then 1 else 0 :=
  gramSchmidtFrame_orthonormal g (chartCoordinateFrame c hc) p i j

theorem chartOrthonormalFrame_positive (g : RiemannianMetric S)
    (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (ho : P202Specs.ChartRegionStokes.PositiveChart (P202.VolumeData.cotangentBundle S) o c hc)
    (p : c.source) :
    SmoothManifolds.OrientationData.IsPositive (o.val p.val)
      (exteriorPower.ιMulti ℝ 2 ((chartOrthonormalFrame g c hc).basis p)) := by
  apply gramSchmidtFrame_positive g (chartCoordinateFrame c hc) o _ p
  intro q
  exact ho q

theorem chartVector_coordinateFrame (c : ModelChart 2 .euclidean M)
    (hc : c ∈ S.smoothStructure.val) (x : Plane)
    (hx : x ∈ P202Specs.ChartRegionStokes.chartTarget c) (i : Fin 2) :
    chartVector c hc x (P202Specs.ChartRegionStokes.coordinateFrame i) =
      coordinateBasis c hc ⟨chartPoint c x, c.map_target hx⟩ i := by
  change P202Specs.ChartRegionStokes.modelPoint x ∈ c.target at hx
  simp only [chartVector, dif_pos hx, coordinateBasis, Basis.map_apply]
  congr 1
  ext j
  simp [P202Specs.ChartRegionStokes.coordinateFrame, Pi.basisFun_apply,
    PiLp.single_apply, Pi.single_apply]

theorem gramE_eq (g : RiemannianMetric S) (c : ModelChart 2 .euclidean M)
    (hc : c ∈ S.smoothStructure.val) (x : Plane)
    (hx : x ∈ P202Specs.ChartRegionStokes.chartTarget c) :
    gramE g c hc x = pairing g (chartPoint c x)
      (coordinateBasis c hc ⟨chartPoint c x, c.map_target hx⟩ 0)
      (coordinateBasis c hc ⟨chartPoint c x, c.map_target hx⟩ 0) := by
  unfold gramE
  simp only [chartVector_coordinateFrame c hc x hx]

theorem gramF_eq (g : RiemannianMetric S) (c : ModelChart 2 .euclidean M)
    (hc : c ∈ S.smoothStructure.val) (x : Plane)
    (hx : x ∈ P202Specs.ChartRegionStokes.chartTarget c) :
    gramF g c hc x = pairing g (chartPoint c x)
      (coordinateBasis c hc ⟨chartPoint c x, c.map_target hx⟩ 0)
      (coordinateBasis c hc ⟨chartPoint c x, c.map_target hx⟩ 1) := by
  unfold gramF
  simp only [chartVector_coordinateFrame c hc x hx]

theorem gramG_eq (g : RiemannianMetric S) (c : ModelChart 2 .euclidean M)
    (hc : c ∈ S.smoothStructure.val) (x : Plane)
    (hx : x ∈ P202Specs.ChartRegionStokes.chartTarget c) :
    gramG g c hc x = pairing g (chartPoint c x)
      (coordinateBasis c hc ⟨chartPoint c x, c.map_target hx⟩ 1)
      (coordinateBasis c hc ⟨chartPoint c x, c.map_target hx⟩ 1) := by
  unfold gramG
  simp only [chartVector_coordinateFrame c hc x hx]

theorem triangularA_eq (g : RiemannianMetric S) (c : ModelChart 2 .euclidean M)
    (hc : c ∈ S.smoothStructure.val) (x : Plane)
    (hx : x ∈ P202Specs.ChartRegionStokes.chartTarget c) :
    triangularA g c hc x = tangentNorm g (chartPoint c x)
      (coordinateBasis c hc ⟨chartPoint c x, c.map_target hx⟩ 0) := by
  rw [triangularA, gramE_eq g c hc x hx]
  rfl

theorem triangularD_eq (g : RiemannianMetric S) (c : ModelChart 2 .euclidean M)
    (hc : c ∈ S.smoothStructure.val) (x : Plane)
    (hx : x ∈ P202Specs.ChartRegionStokes.chartTarget c) :
    triangularD g c hc x = tangentNorm g (chartPoint c x)
      (gramResidual g (chartPoint c x)
        (coordinateBasis c hc ⟨chartPoint c x, c.map_target hx⟩)) := by
  rw [triangularD, gramE_eq g c hc x hx, gramF_eq g c hc x hx, gramG_eq g c hc x hx]
  unfold tangentNorm
  rw [gramResidual_sq]

theorem triangularA_pos (g : RiemannianMetric S) (c : ModelChart 2 .euclidean M)
    (hc : c ∈ S.smoothStructure.val) (x : Plane)
    (hx : x ∈ P202Specs.ChartRegionStokes.chartTarget c) : 0 < triangularA g c hc x := by
  rw [triangularA_eq g c hc x hx]
  exact Real.sqrt_pos.mpr (g.positive _ _ ((coordinateBasis c hc _).ne_zero 0))

theorem triangularD_pos (g : RiemannianMetric S) (c : ModelChart 2 .euclidean M)
    (hc : c ∈ S.smoothStructure.val) (x : Plane)
    (hx : x ∈ P202Specs.ChartRegionStokes.chartTarget c) : 0 < triangularD g c hc x := by
  rw [triangularD_eq g c hc x hx]
  exact Real.sqrt_pos.mpr (g.positive _ _ (gramResidual_ne_zero g _ _))

theorem triangular_diagonal_product (g : RiemannianMetric S) (c : ModelChart 2 .euclidean M)
    (hc : c ∈ S.smoothStructure.val) (x : Plane)
    (hx : x ∈ P202Specs.ChartRegionStokes.chartTarget c) :
    triangularA g c hc x * triangularD g c hc x = areaWeight g c hc x := by
  rw [triangularA_eq g c hc x hx, triangularD_eq g c hc x hx, gramSchmidt_diagonal_product]
  change P202Specs.ChartRegionStokes.modelPoint x ∈ c.target at hx
  unfold areaWeight
  rw [dif_pos hx, Matrix.det_fin_two]
  congr 1
  change _ = pairing g (chartPoint c x) _ _ * pairing g (chartPoint c x) _ _ -
    pairing g (chartPoint c x) _ _ * pairing g (chartPoint c x) _ _
  simp only [coordinateBasis, Basis.map_apply]
  have hsym := g.symmetric (chartPoint c x)
    (((tangentStructure S).fiberCoordinates.equiv c hc (chartPoint c x)
      (c.map_target hx)).symm ((Pi.basisFun ℝ (Fin 2)) 1))
    (((tangentStructure S).fiberCoordinates.equiv c hc (chartPoint c x)
      (c.map_target hx)).symm ((Pi.basisFun ℝ (Fin 2)) 0))
  change pairing g _ _ _ = pairing g _ _ _ at hsym
  rw [pow_two]
  congr 2
  exact hsym.symm

theorem chartOrthonormalFrame_coordinates (g : RiemannianMetric S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val) (x : Plane)
    (hx : x ∈ P202Specs.ChartRegionStokes.chartTarget c) (v : Plane) :
    ((chartOrthonormalFrame g c hc).basis ⟨chartPoint c x, c.map_target hx⟩).equivFun
      (chartVector c hc x v) =
        ![triangularA g c hc x * v 0 + triangularBeta g c hc x * v 1,
          triangularD g c hc x * v 1] := by
  change (gramSchmidtBasis g _ (coordinateBasis c hc _)).equivFun _ = _
  rw [gramSchmidtBasis_equivFun_coordinates]
  have hcoords : (coordinateBasis c hc ⟨chartPoint c x, c.map_target hx⟩).equivFun
      (chartVector c hc x v) = EuclideanSpace.equiv (Fin 2) ℝ v := by
    change P202Specs.ChartRegionStokes.modelPoint x ∈ c.target at hx
    simp only [chartVector, dif_pos hx]
    apply (coordinateBasis c hc ⟨chartPoint c x, c.map_target hx⟩).equivFun.symm.injective
    rw [LinearEquiv.symm_apply_apply]
    simp only [coordinateBasis, Basis.equivFun_symm_apply, Basis.map_apply,
      ← map_smul, ← map_sum]
    congr 1
    exact ((Pi.basisFun ℝ (Fin 2)).sum_equivFun _).symm
  rw [hcoords, triangularA_eq g c hc x hx, triangularD_eq g c hc x hx]
  rw [triangularBeta, triangularA_eq g c hc x hx, gramF_eq g c hc x hx]
  rfl

end ChartFrames

section ChartCalculus
open Module SmoothManifolds.BundleData SmoothManifolds.FrameData SmoothManifolds.MapData

abbrev flatPoint (z : Euclidean 2) : ModelSpace 2 .euclidean := ⟨z, mem_univ _⟩

theorem inverseChart_continuousAt (c : ModelChart 2 .euclidean M) (z : Euclidean 2)
    (hz : flatPoint z ∈ c.target) :
    ContinuousAt (fun y : Euclidean 2 => c.symm (flatPoint y)) z := by
  exact (c.symm.continuousAt hz).comp (continuous_id.subtype_mk _).continuousAt

theorem scalar_pullback_contDiffAt {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (f : M → V) (z : Euclidean 2) (hz : flatPoint z ∈ c.target)
    (hf : VectorSmoothAt S.smoothStructure.val f (c.symm (flatPoint z))) :
    ContDiffAt ℝ ∞ (fun y : Euclidean 2 => f (c.symm (flatPoint y))) z := by
  have hp := c.map_target hz
  obtain ⟨U, hU, hpU, F, hF, heF⟩ := hf.2 c hc hp
  have hright : (c (c.symm (flatPoint z))).val = z := congrArg Subtype.val (c.right_inv hz)
  rw [hright] at hpU
  apply (hF.contDiffAt (hU.mem_nhds hpU)).congr_of_eventuallyEq
  have hct := inverseChart_continuousAt c z hz
  have ht : ∀ᶠ y : Euclidean 2 in 𝓝 z, flatPoint y ∈ c.target :=
    (continuous_id.subtype_mk _).continuousAt.eventually (c.open_target.mem_nhds hz)
  filter_upwards [heF.comp_tendsto hct, ht] with y he hy
  change F (c (c.symm (flatPoint y))).val = f (c.symm (flatPoint y)) at he
  simpa only [show (c (c.symm (flatPoint y))).val = y from
    congrArg Subtype.val (c.right_inv hy)] using he.symm


def coordinateConnectionCoefficient (C : Connection (tangentBundle S))
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (b : LocalFrame (tangentBundle S) c.source c.open_source) (j : Fin 2) : M → ℝ :=
  totalize (fun p : c.source => connectionForm C b p 1 0 (coordinateBasis c hc p j))

theorem coordinateConnectionCoefficient_smooth (C : Connection (tangentBundle S))
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (b : LocalFrame (tangentBundle S) c.source c.open_source) (j : Fin 2)
    (p : c.source) : VectorSmoothAt S.smoothStructure.val
      (coordinateConnectionCoefficient C c hc b j) p.val := by
  let α := SmoothManifolds.SectionExtension.totalSection
    (E := fun q => Module.Dual ℝ (TangentSpace S q))
    (fun q : c.source => connectionForm C b q 1 0)
  have hs := P202.Geometry.ConnectionForms.connectionForm_smooth (tangentBundle S) C
    c.open_source b 1 0 p.val p.property
  have hp : p.val ∈ (tangentBundle S).baseSet ⟨c, hc⟩ := by
    rw [(tangentRealization S).baseSet]; exact p.property
  have hd : p.val ∈ (cotangentBundle S).baseSet ⟨c, hc⟩ := by
    rw [(cotangentDual S).baseSet]; exact hp
  have hco := SmoothManifolds.SectionExtension.coordinates_smoothAt (cotangentBundle S)
    ⟨c,hc⟩ hd hs
  have hj := hco.postcomp (ContinuousLinearMap.proj (R := ℝ) j).contDiff
  apply hj.congr
  filter_upwards [c.open_source.mem_nhds p.property] with q hq
  change (((cotangentDual S).space.bundle.trivialization ⟨c,hc⟩) ⟨q, α q⟩).2 j = _
  rw [(cotangentDual S).coordinates ⟨c,hc⟩ q
    (by rw [(tangentRealization S).baseSet]; exact hq)]
  simp only [SmoothManifolds.SectionExtension.totalSection_of_mem _ q hq,
    coordinateConnectionCoefficient, totalize_of_mem _ q hq, α]
  congr 1
  apply ((tangentStructure S).fiberCoordinates.equiv c hc q hq).injective
  have ht := (tangentRealization S).coordinates ⟨c,hc⟩ q hq
    (((tangentBundle S).trivialization ⟨c,hc⟩).symm q (Pi.single j 1))
  rw [← ht]
  have hqB : q ∈ (tangentBundle S).baseSet ⟨c,hc⟩ := by
    rw [(tangentRealization S).baseSet]; exact hq
  change ((tangentBundle S).fiberCoordinates ⟨c,hc⟩ q hqB)
    (((tangentBundle S).fiberCoordinates ⟨c,hc⟩ q hqB).symm (Pi.single j 1)) = _
  rw [LinearEquiv.apply_symm_apply]
  simp only [coordinateBasis, Module.Basis.map_apply, LinearEquiv.apply_symm_apply,
    Pi.basisFun_apply]


/-- Coordinate differentiation of a local scalar germ, without a global representative. -/
theorem scalarDerivative_chart (c : ModelChart 2 .euclidean M)
    (hc : c ∈ S.smoothStructure.val) (f : M → ℝ) (z : Euclidean 2)
    (hz : flatPoint z ∈ c.target)
    (hf : VectorSmoothAt S.smoothStructure.val f (c.symm (flatPoint z)))
    (v : TangentSpace S (c.symm (flatPoint z))) :
    scalarDerivative S f (c.symm (flatPoint z)) v =
      fderiv ℝ (fun y : Euclidean 2 => f (c.symm (flatPoint y))) z
        ((tangentStructure S).fiberCoordinates.equiv c hc _ (c.map_target hz) v) := by
  let p := c.symm (flatPoint z)
  have hp : p ∈ c.source := c.map_target hz
  obtain ⟨U, hU, hpU, F, hF, heF⟩ := hf.2 c hc hp
  have hright : (c p).val = z := congrArg Subtype.val (c.right_inv hz)
  have hf' : SmoothManifolds.PartitionData.ScalarContDiffAt (⊤ : ℕ∞)
      S.smoothStructure.val f p := (SmoothManifolds.scalarContDiffAt_iff _ _ _ _).mpr hf
  have hG : SmoothManifolds.TangentData.GermChartExtension S p c (scalarGerm S f p) F := by
    refine ⟨⟨U, hU, hpU, hF⟩, ?_⟩
    simp only [scalarGerm, dif_pos hf']
    exact Germ.coe_eq.mpr heF
  have hder := SmoothManifolds.VectorFields.tangent_action_coordinates S
    (tangentStructure S).fiberCoordinates p c hc hp v (scalarGerm S f p) F hG
  change scalarDerivative S f p v = _
  change v.val (scalarGerm S f p) = _
  rw [hder, hright]
  have heq : F =ᶠ[𝓝 z] (fun y : Euclidean 2 => f (c.symm (flatPoint y))) := by
    have hct := inverseChart_continuousAt c z hz
    have ht : ∀ᶠ y : Euclidean 2 in 𝓝 z, flatPoint y ∈ c.target :=
      (continuous_id.subtype_mk _).continuousAt.eventually (c.open_target.mem_nhds hz)
    filter_upwards [heF.comp_tendsto hct, ht] with y he hy
    change F (c (c.symm (flatPoint y))).val = f (c.symm (flatPoint y)) at he
    simpa only [show (c (c.symm (flatPoint y))).val = y from
      congrArg Subtype.val (c.right_inv hy)] using he
  rw [heq.fderiv_eq]

theorem chartTarget_isOpen (c : ModelChart 2 .euclidean M) :
    IsOpen (P202Specs.ChartRegionStokes.chartTarget c) := by
  exact c.open_target.preimage
    ((EuclideanSpace.equiv (Fin 2) ℝ).toContinuousLinearEquiv.continuous.subtype_mk _) -- to be checked


end ChartCalculus

section CoordinateSmoothness
open Module SmoothManifolds.BundleData SmoothManifolds.FrameData SmoothManifolds.MapData
theorem chart_pullback_contDiffAt {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (f : M → V) (x : Plane) (hx : x ∈ P202Specs.ChartRegionStokes.chartTarget c)
    (hf : VectorSmoothAt S.smoothStructure.val f (chartPoint c x)) :
    ContDiffAt ℝ ∞ (fun y => f (chartPoint c y)) x := by
  have h := scalar_pullback_contDiffAt c hc f (EuclideanSpace.equiv (Fin 2) ℝ x) hx hf
  exact h.comp x (EuclideanSpace.equiv (Fin 2) ℝ).toContinuousLinearEquiv.contDiff.contDiffAt

theorem gramEntry_smooth (g : RiemannianMetric S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val) (i j : Fin 2) :
    ContDiffOn ℝ ∞ (fun x => pairing g (chartPoint c x)
      (chartVector c hc x (P202Specs.ChartRegionStokes.coordinateFrame i))
      (chartVector c hc x (P202Specs.ChartRegionStokes.coordinateFrame j)))
      (P202Specs.ChartRegionStokes.chartTarget c) := by
  let f : c.source → ℝ := fun p => pairing g p.val
    ((chartCoordinateFrame c hc).section_ i p) ((chartCoordinateFrame c hc).section_ j p)
  have hs := localFrame_pairing_smooth g (chartCoordinateFrame c hc) i j
  have ht : ContDiffOn ℝ ∞ (fun x => totalize f (chartPoint c x))
      (P202Specs.ChartRegionStokes.chartTarget c) := by
    intro x hx
    apply (chart_pullback_contDiffAt c hc (totalize f) x hx _).contDiffWithinAt
    exact (hs ⟨chartPoint c x, c.map_target hx⟩).totalize c.open_source
  apply ht.congr
  intro x hx
  rw [chartVector_coordinateFrame c hc x hx i, chartVector_coordinateFrame c hc x hx j]
  change _ = totalize f (chartPoint c x)
  rw [totalize_of_mem f (chartPoint c x) (show chartPoint c x ∈ c.source from c.map_target hx)]
  rfl

theorem triangular_coefficients_smooth (g : RiemannianMetric S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val) :
    ContDiffOn ℝ ∞ (triangularA g c hc) (P202Specs.ChartRegionStokes.chartTarget c) ∧
    ContDiffOn ℝ ∞ (triangularBeta g c hc) (P202Specs.ChartRegionStokes.chartTarget c) ∧
    ContDiffOn ℝ ∞ (triangularD g c hc) (P202Specs.ChartRegionStokes.chartTarget c) := by
  have hE : ContDiffOn ℝ ∞ (gramE g c hc) _ := gramEntry_smooth g c hc 0 0
  have hF : ContDiffOn ℝ ∞ (gramF g c hc) _ := gramEntry_smooth g c hc 0 1
  have hG : ContDiffOn ℝ ∞ (gramG g c hc) _ := gramEntry_smooth g c hc 1 1
  have hEp (x : Plane) (hx : x ∈ P202Specs.ChartRegionStokes.chartTarget c) :
      0 < gramE g c hc x := by
    rw [gramE_eq g c hc x hx]
    exact g.positive _ _ ((coordinateBasis c hc _).ne_zero 0)
  have hHp (x : Plane) (hx : x ∈ P202Specs.ChartRegionStokes.chartTarget c) :
      0 < gramG g c hc x - gramF g c hc x ^ 2 / gramE g c hc x := by
    rw [gramE_eq g c hc x hx, gramF_eq g c hc x hx, gramG_eq g c hc x hx]
    exact schurComplement_pos g _ _
  have ha : ContDiffOn ℝ ∞ (triangularA g c hc) _ :=
    hE.sqrt (fun x hx => ne_of_gt (hEp x hx))
  refine ⟨ha, hF.div ha (fun x hx => ne_of_gt (triangularA_pos g c hc x hx)), ?_⟩
  exact (hG.sub ((hF.pow 2).div hE (fun x hx => ne_of_gt (hEp x hx)))).sqrt
    (fun x hx => ne_of_gt (hHp x hx))

theorem chartOrthonormalFrame_properties (g : RiemannianMetric S)
    (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (ho : P202Specs.ChartRegionStokes.PositiveChart (P202.VolumeData.cotangentBundle S) o c hc) :
    IsChartFrame g o c hc (chartOrthonormalFrame g c hc) := by
  refine ⟨fun _ => rfl, fun _ => rfl, chartOrthonormalFrame_orthonormal g c hc,
    chartOrthonormalFrame_positive g o c hc ho, ?_⟩
  rcases triangular_coefficients_smooth g c hc with ⟨ha,hb,hd⟩
  refine ⟨ha,hb,hd,?_⟩
  intro x hx
  exact ⟨triangularA_pos g c hc x hx, triangularD_pos g c hc x hx,
    triangular_diagonal_product g c hc x hx, chartOrthonormalFrame_coordinates g c hc x hx⟩


/-- The two ordinary coefficients of the literal pulled-back connection form. -/
theorem omega_apply (C : Connection (tangentBundle S))
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (b : LocalFrame (tangentBundle S) c.source c.open_source) (x : Plane)
    (hx : x ∈ P202Specs.ChartRegionStokes.chartTarget c) (v : Plane) :
    omega C c hc b x v = ∑ j : Fin 2,
      coordinateConnectionCoefficient C c hc b j (chartPoint c x) * v j := by
  change P202Specs.ChartRegionStokes.modelPoint x ∈ c.target at hx
  unfold omega
  rw [dif_pos hx]
  change connectionForm C b ⟨chartPoint c x, c.map_target hx⟩ 1 0
    (((tangentStructure S).fiberCoordinates.equiv c hc _ _).symm
      (EuclideanSpace.equiv (Fin 2) ℝ v)) = _
  have hv : EuclideanSpace.equiv (Fin 2) ℝ v =
      ∑ j : Fin 2, v j • (Pi.basisFun ℝ (Fin 2)) j := by
    ext j
    fin_cases j <;> simp [Pi.basisFun_apply]
  rw [hv, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [coordinateConnectionCoefficient]
  rw [totalize_of_mem _ (chartPoint c x) (show chartPoint c x ∈ c.source from c.map_target hx)]
  simp only [map_smul, smul_eq_mul, coordinateBasis, Basis.map_apply]
  ring

def coordinateCovector (j : Fin 2) : Plane →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj j).comp
    (EuclideanSpace.equiv (Fin 2) ℝ).toContinuousLinearEquiv.toContinuousLinearMap

theorem omega_smooth (C : Connection (tangentBundle S))
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (b : LocalFrame (tangentBundle S) c.source c.open_source) :
    ContDiffOn ℝ ∞ (omega C c hc b) (P202Specs.ChartRegionStokes.chartTarget c) := by
  have hcoeff (j : Fin 2) : ContDiffOn ℝ ∞
      (fun x => coordinateConnectionCoefficient C c hc b j (chartPoint c x))
      (P202Specs.ChartRegionStokes.chartTarget c) := by
    intro x hx
    exact (chart_pullback_contDiffAt c hc _ x hx
      (coordinateConnectionCoefficient_smooth C c hc b j
        ⟨chartPoint c x, c.map_target hx⟩)).contDiffWithinAt
  have hs : ContDiffOn ℝ ∞ (fun x => ∑ j : Fin 2,
      coordinateConnectionCoefficient C c hc b j (chartPoint c x) • coordinateCovector j)
      (P202Specs.ChartRegionStokes.chartTarget c) :=
    ContDiffOn.sum (fun j _ => (hcoeff j).smul contDiffOn_const)
  apply hs.congr
  intro x hx
  ext v
  rw [omega_apply C c hc b x hx]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    coordinateCovector, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
  rfl


end CoordinateSmoothness

section CurvatureBridge
open Module SmoothManifolds.BundleData SmoothManifolds.FrameData SmoothManifolds.MapData
theorem curvature_density_coefficient (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : P202.LeviCivitaData.IsLeviCivita g C)
    (T : CurvatureTensor S) (hT : RepresentsCurvature C T)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val) (x : Plane)
    (hx : x ∈ P202Specs.ChartRegionStokes.chartTarget c) :
    let b := chartOrthonormalFrame g c hc
    let p : c.source := ⟨chartPoint c x, c.map_target hx⟩
    curvatureForm g T p.val (coordinateBasis c hc p 0) (coordinateBasis c hc p 1)
      (b.section_ 0 p) (b.section_ 1 p) =
      -gaussianCurvature g T (chartPoint c x) * areaWeight g c hc x := by
  change P202Specs.ChartRegionStokes.modelPoint x ∈ c.target at hx
  let b := chartOrthonormalFrame g c hc
  let p : c.source := ⟨chartPoint c x, c.map_target hx⟩
  change curvatureForm g T p.val (coordinateBasis c hc p 0) (coordinateBasis c hc p 1)
    (b.section_ 0 p) (b.section_ 1 p) = _
  have hon := chartOrthonormalFrame_orthonormal g c hc
  have hpair : LinearIndependent ℝ ![b.section_ 0 p, b.section_ 1 p] := by
    convert (b.basis p).linearIndependent using 1
    funext i
    fin_cases i <;> exact (b.basis_eq p _).symm
  have hsign := curvature_coefficient_sign g C hC T hT p.val
    (b.section_ 0 p) (b.section_ 1 p) hpair (by simpa using hon p 0 0)
    (by simpa using hon p 1 1) (by simpa using hon p 0 1)
  have hzero : curvatureForm g T p.val (b.section_ 0 p) (b.section_ 0 p)
      (b.section_ 0 p) (b.section_ 1 p) = 0 := by
    have h := (P202.Geometry.CurvatureAlgebra.symmetries g C hC T hT p.val
      (b.section_ 0 p) (b.section_ 0 p) (b.section_ 0 p) (b.section_ 1 p)).1
    linarith
  have hcoords (i : Fin 2) := chartOrthonormalFrame_coordinates g c hc x hx
    (P202Specs.ChartRegionStokes.coordinateFrame i)
  simp_rw [chartVector_coordinateFrame c hc x hx] at hcoords
  have hexp (i : Fin 2) : coordinateBasis c hc p i =
      (b.basis p).equivFun (coordinateBasis c hc p i) 0 • b.section_ 0 p +
        (b.basis p).equivFun (coordinateBasis c hc p i) 1 • b.section_ 1 p := by
    simpa only [Fin.sum_univ_two, b.basis_eq] using
      ((b.basis p).sum_equivFun (coordinateBasis c hc p i)).symm
  have h0 : coordinateBasis c hc p 0 = triangularA g c hc x • b.section_ 0 p := by
    rw [hexp 0, hcoords 0]
    simp [P202Specs.ChartRegionStokes.coordinateFrame, PiLp.single_apply]
  have h1 : coordinateBasis c hc p 1 = triangularBeta g c hc x • b.section_ 0 p +
      triangularD g c hc x • b.section_ 1 p := by
    rw [hexp 1, hcoords 1]
    simp [P202Specs.ChartRegionStokes.coordinateFrame, PiLp.single_apply]
  rw [h0,h1]
  unfold curvatureForm at hsign hzero ⊢
  simp only [map_smul, map_add, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.BilinForm.smul_left, LinearMap.BilinForm.add_left]
  rw [hzero, hsign]
  rw [← triangular_diagonal_product g c hc x hx]
  ring


theorem omega_coordinate (C : Connection (tangentBundle S))
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (b : LocalFrame (tangentBundle S) c.source c.open_source) (x : Plane)
    (hx : x ∈ P202Specs.ChartRegionStokes.chartTarget c) (i : Fin 2) :
    omega C c hc b x (P202Specs.ChartRegionStokes.coordinateFrame i) =
      coordinateConnectionCoefficient C c hc b i (chartPoint c x) := by
  rw [omega_apply C c hc b x hx]
  fin_cases i <;> simp [Fin.sum_univ_two, P202Specs.ChartRegionStokes.coordinateFrame,
    PiLp.single_apply]

theorem coordinateConnectionDerivative (C : Connection (tangentBundle S))
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (b : LocalFrame (tangentBundle S) c.source c.open_source) (x : Plane)
    (hx : x ∈ P202Specs.ChartRegionStokes.chartTarget c) (i j : Fin 2) :
    scalarDerivative S (coordinateConnectionCoefficient C c hc b j) (chartPoint c x)
      (coordinateBasis c hc ⟨chartPoint c x, c.map_target hx⟩ i) =
      fderiv ℝ (fun y => omega C c hc b y (P202Specs.ChartRegionStokes.coordinateFrame j)) x
        (P202Specs.ChartRegionStokes.coordinateFrame i) := by
  change P202Specs.ChartRegionStokes.modelPoint x ∈ c.target at hx
  let f := coordinateConnectionCoefficient C c hc b j
  let F : Euclidean 2 → ℝ := fun z => f (c.symm (flatPoint z))
  let L := (EuclideanSpace.equiv (Fin 2) ℝ).toContinuousLinearEquiv
  have hf := coordinateConnectionCoefficient_smooth C c hc b j ⟨chartPoint c x, c.map_target hx⟩
  have hscalar := scalarDerivative_chart c hc f (L x) hx hf
    (coordinateBasis c hc ⟨chartPoint c x, c.map_target hx⟩ i)
  have hF : ContDiffAt ℝ ∞ F (L x) := scalar_pullback_contDiffAt c hc f (L x) hx hf
  have hcomp := (hF.differentiableAt (by simp)).hasFDerivAt.comp x L.hasFDerivAt
  have heq : (fun y => omega C c hc b y (P202Specs.ChartRegionStokes.coordinateFrame j)) =ᶠ[𝓝 x]
      (F ∘ L) := by
    filter_upwards [(chartTarget_isOpen c).mem_nhds hx] with y hy
    exact omega_coordinate C c hc b y hy j
  rw [heq.fderiv_eq, hcomp.fderiv]
  change _ = fderiv ℝ F (L x) (L (P202Specs.ChartRegionStokes.coordinateFrame i))
  change scalarDerivative S f (chartPoint c x) _ = fderiv ℝ F (L x)
    (((tangentStructure S).fiberCoordinates.equiv c hc (chartPoint c x) (c.map_target hx))
      (coordinateBasis c hc ⟨chartPoint c x, c.map_target hx⟩ i)) at hscalar
  simp only [coordinateBasis, Basis.map_apply, LinearEquiv.apply_symm_apply] at hscalar
  have hLi : L (P202Specs.ChartRegionStokes.coordinateFrame i) = (Pi.basisFun ℝ (Fin 2)) i := by
    ext k
    simp [L, P202Specs.ChartRegionStokes.coordinateFrame, Pi.basisFun_apply, PiLp.single_apply, Pi.single_apply, eq_comm]
  rw [hLi]
  exact hscalar

theorem omega_fderiv_evaluation (C : Connection (tangentBundle S))
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (b : LocalFrame (tangentBundle S) c.source c.open_source) (x : Plane)
    (hx : x ∈ P202Specs.ChartRegionStokes.chartTarget c) (i j : Fin 2) :
    fderiv ℝ (omega C c hc b) x (P202Specs.ChartRegionStokes.coordinateFrame i)
      (P202Specs.ChartRegionStokes.coordinateFrame j) =
      fderiv ℝ (fun y => omega C c hc b y (P202Specs.ChartRegionStokes.coordinateFrame j)) x
        (P202Specs.ChartRegionStokes.coordinateFrame i) := by
  have hω := ((omega_smooth C c hc b x hx).contDiffAt
    ((chartTarget_isOpen c).mem_nhds hx)).differentiableAt (by simp)
  have hd := hω.hasFDerivAt.clm_apply
    (hasFDerivAt_const (P202Specs.ChartRegionStokes.coordinateFrame j) x)
  rw [hd.fderiv]
  simp


theorem coordinateBasis_eq_coordinateVector (c : ModelChart 2 .euclidean M)
    (hc : c ∈ S.smoothStructure.val) (p : c.source) (i : Fin 2) :
    coordinateBasis c hc p i = P202.LeviCivitaData.coordinateVector ⟨c,hc⟩ i p.val := by
  unfold coordinateBasis
  rw [Basis.map_apply, ← tangentCoordinates_eq c hc p]
  simp only [Pi.basisFun_apply, SmoothVectorBundle.fiberCoordinates_symm_apply]
  rfl

theorem coordinate_frame_curvature_coefficient (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : P202.LeviCivitaData.IsMetricCompatible g C)
    (T : CurvatureTensor S) (hT : RepresentsCurvature C T)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (b : LocalFrame (tangentBundle S) c.source c.open_source)
    (hon : ∀ p i j, pairing g p.val (b.section_ i p) (b.section_ j p) = if i = j then 1 else 0)
    (p : c.source) :
    curvatureForm g T p.val (coordinateBasis c hc p 0) (coordinateBasis c hc p 1)
      (b.section_ 0 p) (b.section_ 1 p) =
    scalarDerivative S (coordinateConnectionCoefficient C c hc b 1) p.val
      (coordinateBasis c hc p 0) -
    scalarDerivative S (coordinateConnectionCoefficient C c hc b 0) p.val
      (coordinateBasis c hc p 1) := by
  obtain ⟨e, he⟩ := P202.Geometry.ConnectionForms.local_frame_representative
    (tangentBundle S) (chartCoordinateFrame c hc) p
  have hval (i : Fin 2) : (e i).val p.val = coordinateBasis c hc p i := by
    simpa only [SmoothManifolds.SectionExtension.totalSection_of_mem _ p.val p.property,
      chartCoordinateFrame] using (he i).self_of_nhds
  have hecoord (i : Fin 2) : ∀ᶠ q in 𝓝 p.val, (e i).val q =
      P202.LeviCivitaData.coordinateVector ⟨c,hc⟩ i q := by
    filter_upwards [he i, c.open_source.mem_nhds p.property] with q heq hq
    rw [heq, SmoothManifolds.SectionExtension.totalSection_of_mem _ q hq]
    exact coordinateBasis_eq_coordinateVector c hc ⟨q,hq⟩ i
  have hbr := P202.Geometry.LeviCivita.coordinate_bracket_zero ⟨c,hc⟩ p.val
    (by rw [(tangentRealization S).baseSet]; exact p.property)
    0 1 (e 0) (e 1) (hecoord 0) (hecoord 1)
  have hco (i : Fin 2) : frameConnectionEvaluation C b (e i) =ᶠ[𝓝 p.val]
      coordinateConnectionCoefficient C c hc b i := by
    filter_upwards [he i, c.open_source.mem_nhds p.property] with q heq hq
    simp only [frameConnectionEvaluation, coordinateConnectionCoefficient, totalize_of_mem _ q hq]
    rw [heq, SmoothManifolds.SectionExtension.totalSection_of_mem _ q hq]
    rfl
  have hcurv := orthonormalFrame_curvature_coefficient g C hC T hT b hon (e 0) (e 1) p
  rw [scalarDerivative_congr_germ _ _ p.val (hco 1),
    scalarDerivative_congr_germ _ _ p.val (hco 0), hbr, map_zero, sub_zero,
    hval 0, hval 1] at hcurv
  exact hcurv



/-- Literal evaluation on the inverse-chart tangent vector. -/
theorem omega_eq_connectionForm (C : Connection (tangentBundle S))
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (b : LocalFrame (tangentBundle S) c.source c.open_source) (x : Plane)
    (hx : x ∈ P202Specs.ChartRegionStokes.chartTarget c) (v : Plane) :
    omega C c hc b x v = connectionForm C b ⟨chartPoint c x, c.map_target hx⟩ 1 0
      (chartVector c hc x v) := by
  change P202Specs.ChartRegionStokes.modelPoint x ∈ c.target at hx
  simp only [omega, chartVector, dif_pos hx]
  rfl

/-- The chart exterior derivative is the genuine intrinsic curvature coefficient. -/
theorem exteriorCoefficient_eq_curvature (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : P202.LeviCivitaData.IsMetricCompatible g C)
    (T : CurvatureTensor S) (hT : RepresentsCurvature C T)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (b : LocalFrame (tangentBundle S) c.source c.open_source)
    (hon : ∀ p i j, pairing g p.val (b.section_ i p) (b.section_ j p) = if i = j then 1 else 0)
    (x : Plane) (hx : x ∈ P202Specs.ChartRegionStokes.chartTarget c) :
    P202Specs.ChartRegionStokes.exteriorCoefficient (omega C c hc b) x =
      curvatureForm g T (chartPoint c x)
        (coordinateBasis c hc ⟨chartPoint c x, c.map_target hx⟩ 0)
        (coordinateBasis c hc ⟨chartPoint c x, c.map_target hx⟩ 1)
        (b.section_ 0 ⟨chartPoint c x, c.map_target hx⟩)
        (b.section_ 1 ⟨chartPoint c x, c.map_target hx⟩) := by
  unfold P202Specs.ChartRegionStokes.exteriorCoefficient
  rw [omega_fderiv_evaluation C c hc b x hx 0 1,
    omega_fderiv_evaluation C c hc b x hx 1 0,
    ← coordinateConnectionDerivative C c hc b x hx 0 1,
    ← coordinateConnectionDerivative C c hc b x hx 1 0]
  exact (coordinate_frame_curvature_coefficient g C hC T hT c hc b hon
    ⟨chartPoint c x, c.map_target hx⟩).symm

/-- Smooth positive Gram–Schmidt frame, literal pulled-back connection form,
and the curvature identity with the source's sign and metric density. -/
theorem surfaceConnectionForm : P202Specs.SurfaceConnectionForm.Expected.surfaceConnectionForm.{u} := by
  intro M _ S g C hC T hT o c hc ho
  refine ⟨chartOrthonormalFrame g c hc, chartOrthonormalFrame_properties g o c hc ho,
    omega_smooth C c hc _, ?_⟩
  intro x hx
  rw [exteriorCoefficient_eq_curvature g C hC.2 T hT c hc _
    (chartOrthonormalFrame_orthonormal g c hc) x hx]
  exact curvature_density_coefficient g C hC T hT c hc x hx

end CurvatureBridge
end P202.SurfaceConnectionForm
