import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.LocalGaussBonnet
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.CurvatureAlgebra
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.PlanarRegionEuler
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.PlaneTurning
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.ChartRegionStokes
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.ConnectionForms
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.SmoothMetrics
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.CurveCovariantDerivative
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.SurfaceBoundaryGeometry
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.SurfaceConnectionForm
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.MetricBoundaryTurning
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Tactic.FinCases

/-! Local Gauss–Bonnet with noncuspidal corners, paper.tex 4919–4994.
The actual chart connection form and intrinsic boundary calculus are supplied
by the authorized upstream modules; induced component signs, corner Stokes,
and the rational homological Euler invariant give the full formula. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
open Set Filter
open scoped Topology
open scoped BigOperators unitInterval ContDiff

namespace P202.LocalGaussBonnet
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
open P202.ConnectionData P202.MetricData P202.CurvatureData P202.SurfaceBoundaryData
open P202Specs.PlanarRegionTopology P202Specs.LocalGaussBonnet
universe u
variable {M : Type u} [TopologicalSpace M] {S : SmoothManifold 2 .euclidean M}

/-- The shared reference basis really is an independent pair. -/
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

/-- An upper triangular change of vector coordinates. -/
def upperTriangular (a b d : ℝ) : Plane →ₗ[ℝ] Plane where
  toFun v := !₂[a * v 0 + b * v 1, d * v 1]
  map_add' v w := by ext i; fin_cases i <;> simp <;> ring
  map_smul' r v := by ext i; fin_cases i <;> simp <;> ring

/-- Straight interpolation used for a positive Gram–Schmidt coordinate change. -/
def triangularPath (a b d t : ℝ) : Plane →ₗ[ℝ] Plane :=
  upperTriangular (1 - t + t * a) (t * b) (1 - t + t * d)

theorem diagonalInterpolation_pos {a t : ℝ} (ha : 0 < a) (ht : t ∈ Icc (0 : ℝ) 1) :
    0 < 1 - t + t * a := by
  by_cases ht0 : t = 0
  · simp [ht0]
  · exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr ht.2)
      (mul_pos (lt_of_le_of_ne ht.1 (Ne.symm ht0)) ha)

theorem upperTriangular_injective {a b d : ℝ} (ha : a ≠ 0) (hd : d ≠ 0) :
    Function.Injective (upperTriangular a b d) := by
  intro v w h
  have h0 := congrArg (fun z : Plane => z 0) h
  have h1 := congrArg (fun z : Plane => z 1) h
  simp only [upperTriangular, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  have hvw1 : v 1 = w 1 := mul_left_cancel₀ hd h1
  rw [hvw1] at h0
  have hvw0 : v 0 = w 0 := mul_left_cancel₀ ha (add_right_cancel h0)
  ext i
  fin_cases i <;> assumption

theorem triangularPath_injective {a b d t : ℝ} (ha : 0 < a) (hd : 0 < d)
    (ht : t ∈ Icc (0 : ℝ) 1) : Function.Injective (triangularPath a b d t) :=
  upperTriangular_injective (diagonalInterpolation_pos ha ht).ne'
    (diagonalInterpolation_pos hd ht).ne'

@[simp] theorem triangularPath_zero (a b d : ℝ) : triangularPath a b d 0 = LinearMap.id := by
  ext v i
  fin_cases i <;> simp [triangularPath, upperTriangular]

@[simp] theorem triangularPath_one (a b d : ℝ) :
    triangularPath a b d 1 = upperTriangular a b d := by
  simp [triangularPath]

/-- Explicit orientation determinant, including every intermediate map. -/
theorem upperTriangular_area (a b d : ℝ) (v w : Plane) :
    upperTriangular a b d v 0 * upperTriangular a b d w 1 -
      upperTriangular a b d v 1 * upperTriangular a b d w 0 =
        a * d * (v 0 * w 1 - v 1 * w 0) := by
  simp only [upperTriangular, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- The determinant multiplier stays positive throughout the interpolation. -/
theorem triangularPath_positive {a d t : ℝ} (ha : 0 < a) (hd : 0 < d)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    0 < (1 - t + t * a) * (1 - t + t * d) :=
  mul_pos (diagonalInterpolation_pos ha ht) (diagonalInterpolation_pos hd ht)

/-- Nonzero directions stay nonzero under the whole frame interpolation. -/
theorem triangularPath_ne_zero {a b d t : ℝ} (ha : 0 < a) (hd : 0 < d)
    (ht : t ∈ Icc (0 : ℝ) 1) {v : Plane} (hv : v ≠ 0) :
    triangularPath a b d t v ≠ 0 := by
  intro h
  exact hv (triangularPath_injective ha hd ht (h.trans (map_zero _).symm))

/-- Equality of normalized nonzero vectors is equality up to positive scale. -/
theorem normalize_eq_iff_pos_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) :
    NormedSpace.normalize x = NormedSpace.normalize y ↔
      ∃ r : ℝ, 0 < r ∧ x = r • y := by
  constructor
  · intro h
    refine ⟨‖x‖ / ‖y‖, div_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr hy), ?_⟩
    have hh := congrArg (fun z : E => ‖x‖ • z) h
    rw [NormedSpace.norm_smul_normalize] at hh
    simpa only [NormedSpace.normalize, smul_smul, div_eq_mul_inv] using hh
  · rintro ⟨r, hr, rfl⟩
    exact NormedSpace.normalize_smul_of_pos hr y

/-- An injective linear change cannot create a cusp. This handles independent
one-sided tangents as well as equal tangent directions. -/
theorem linearMap_preserves_noncuspidality
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E →ₗ[ℝ] F) (hf : Function.Injective f)
    {x y : E} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : NormedSpace.normalize x ≠ -NormedSpace.normalize y) :
    NormedSpace.normalize (f x) ≠ -NormedSpace.normalize (f y) := by
  have hfx : f x ≠ 0 := fun h => hx (hf (h.trans (map_zero f).symm))
  have hfy : -f y ≠ 0 := neg_ne_zero.mpr
    (fun h => hy (hf (h.trans (map_zero f).symm)))
  intro h
  rw [← NormedSpace.normalize_neg] at h
  obtain ⟨r, hr, he⟩ := (normalize_eq_iff_pos_smul hfx hfy).mp h
  have he' : x = r • (-y) := hf (by simpa using he)
  apply hxy
  rw [he', NormedSpace.normalize_smul_of_pos hr, NormedSpace.normalize_neg]

/-- In particular the entire positive triangular interpolation remains away
from the antipodal branch cut of the short signed corner rotation. -/
theorem triangularPath_preserves_noncuspidality {a b d t : ℝ}
    (ha : 0 < a) (hd : 0 < d) (ht : t ∈ Icc (0 : ℝ) 1)
    {v w : Plane} (hv : v ≠ 0) (hw : w ≠ 0)
    (hvw : NormedSpace.normalize v ≠ -NormedSpace.normalize w) :
    NormedSpace.normalize (triangularPath a b d t v) ≠
      -NormedSpace.normalize (triangularPath a b d t w) :=
  linearMap_preserves_noncuspidality _ (triangularPath_injective ha hd ht) hv hw hvw

section FrameHomotopy
variable {X : Type*} [TopologicalSpace X]

/-- Normalization of a continuous nonvanishing vector field. -/
def normalizedMap (v : C(X, Plane)) (hv : ∀ x, v x ≠ 0) : C(X, Plane) where
  toFun x := NormedSpace.normalize (v x)
  continuous_toFun := (v.continuous.norm.inv₀ (fun x => norm_ne_zero_iff.mpr (hv x))).smul
    v.continuous

/-- A spatially varying upper triangular frame change on actual vectors. -/
def transformedMap (a b d : C(X, ℝ)) (v : C(X, Plane)) : C(X, Plane) where
  toFun x := upperTriangular (a x) (b x) (d x) (v x)
  continuous_toFun := by
    change Continuous (fun x => !₂[a x * v x 0 + b x * v x 1, d x * v x 1])
    fun_prop

theorem transformedMap_ne_zero (a b d : C(X, ℝ)) (v : C(X, Plane))
    (ha : ∀ x, 0 < a x) (hd : ∀ x, 0 < d x) (hv : ∀ x, v x ≠ 0) (x : X) :
    transformedMap a b d v x ≠ 0 := by
  intro h
  exact hv x (upperTriangular_injective (ha x).ne' (hd x).ne'
    (h.trans (map_zero _).symm))

/-- The actual normalization homotopy for a positive triangular frame field.
Taking X to be the parameter circle gives a free homotopy of unit-vector
loops. This statement does not yet identify the transformed corner paths
with their metric short-rotation replacements. -/
def triangularHomotopy (a b d : C(X, ℝ)) (v : C(X, Plane))
    (ha : ∀ x, 0 < a x) (hd : ∀ x, 0 < d x) (hv : ∀ x, v x ≠ 0) :
    ContinuousMap.Homotopy (normalizedMap v hv)
      (normalizedMap (transformedMap a b d v) (transformedMap_ne_zero a b d v ha hd hv)) where
  toFun p := NormedSpace.normalize (triangularPath (a p.2) (b p.2) (d p.2) p.1 (v p.2))
  continuous_toFun := by
    have hc : Continuous (fun p : unitInterval × X =>
        triangularPath (a p.2) (b p.2) (d p.2) p.1 (v p.2)) := by
      change Continuous (fun p : unitInterval × X =>
        !₂[(1 - (p.1 : ℝ) + (p.1 : ℝ) * a p.2) * v p.2 0 +
          ((p.1 : ℝ) * b p.2) * v p.2 1,
          (1 - (p.1 : ℝ) + (p.1 : ℝ) * d p.2) * v p.2 1])
      fun_prop
    exact (hc.norm.inv₀ (fun p => norm_ne_zero_iff.mpr
      (triangularPath_ne_zero (ha p.2) (hd p.2) p.1.property (hv p.2)))).smul hc
  map_zero_left x := by
    change NormedSpace.normalize (triangularPath (a x) (b x) (d x) 0 (v x)) =
      NormedSpace.normalize (v x)
    rw [triangularPath_zero]
    rfl
  map_one_left x := by simp [normalizedMap, transformedMap]

/-- The homotopy stays in the unit circle, not merely in the whole plane. -/
theorem triangularHomotopy_unit (a b d : C(X, ℝ)) (v : C(X, Plane))
    (ha : ∀ x, 0 < a x) (hd : ∀ x, 0 < d x) (hv : ∀ x, v x ≠ 0)
    (p : unitInterval × X) : ‖triangularHomotopy a b d v ha hd hv p‖ = 1 :=
  NormedSpace.norm_normalize
    (triangularPath_ne_zero (ha p.2) (hd p.2) p.1.property (hv p.2))

end FrameHomotopy

section UnitLoops
open P202Specs.PlaneTurning

lemma unitLoop_ne_zero (T : UnitDirectionLoop) (t : unitInterval) : T.map t ≠ 0 := by
  intro h
  have hu := T.unit t
  simpa [h] using hu

/-- A genuine closed unit-direction loop after a positive triangular frame
change whose coefficients agree at the closing parameter. -/
def triangularLoop (T : UnitDirectionLoop) (a b d : C(unitInterval, ℝ))
    (ha : ∀ t, 0 < a t) (hd : ∀ t, 0 < d t)
    (hclose : a 1 = a 0 ∧ b 1 = b 0 ∧ d 1 = d 0) : UnitDirectionLoop where
  map := normalizedMap (transformedMap a b d T.map)
    (transformedMap_ne_zero a b d T.map ha hd (unitLoop_ne_zero T))
  unit t := NormedSpace.norm_normalize
    (transformedMap_ne_zero a b d T.map ha hd (unitLoop_ne_zero T) t)
  closed := by
    change NormedSpace.normalize (upperTriangular (a 1) (b 1) (d 1) (T.map 1)) =
      NormedSpace.normalize (upperTriangular (a 0) (b 0) (d 0) (T.map 0))
    rw [hclose.1, hclose.2.1, hclose.2.2, T.closed]

/-- The closedness and unit-norm requirements of the upstream winding API
hold along the entire straight frame interpolation, including its endpoints. -/
def triangularLoopHomotopy (T : UnitDirectionLoop) (a b d : C(unitInterval, ℝ))
    (ha : ∀ t, 0 < a t) (hd : ∀ t, 0 < d t)
    (hclose : a 1 = a 0 ∧ b 1 = b 0 ∧ d 1 = d 0) :
    UnitDirectionHomotopy T (triangularLoop T a b d ha hd hclose) where
  map := (triangularHomotopy a b d T.map ha hd (unitLoop_ne_zero T)).toContinuousMap
  unit t u := triangularHomotopy_unit a b d T.map ha hd (unitLoop_ne_zero T) (t,u)
  at_zero t := by
    change NormedSpace.normalize (triangularPath (a t) (b t) (d t) 0 (T.map t)) = _
    rw [triangularPath_zero]
    exact NormedSpace.normalize_eq_self_of_norm_eq_one (T.unit t)
  at_one t := by
    change NormedSpace.normalize (triangularPath (a t) (b t) (d t) 1 (T.map t)) = _
    rw [triangularPath_one]
    rfl
  closed t := by
    change NormedSpace.normalize (triangularPath (a 1) (b 1) (d 1) t (T.map 1)) =
      NormedSpace.normalize (triangularPath (a 0) (b 0) (d 0) t (T.map 0))
    rw [hclose.1, hclose.2.1, hclose.2.2, T.closed]

/-- Hence the actual circle winding is unchanged. To apply this to literal
metric short rotations one must additionally compare the corner paths. -/
theorem triangularLoop_winding (o : Orientation ℝ Plane (Fin 2))
    (T : UnitDirectionLoop) (a b d : C(unitInterval, ℝ))
    (ha : ∀ t, 0 < a t) (hd : ∀ t, 0 < d t)
    (hclose : a 1 = a 0 ∧ b 1 = b 0 ∧ d 1 = d 0) :
    P202Specs.PlaneTangentComparison.winding o T =
      P202Specs.PlaneTangentComparison.winding o (triangularLoop T a b d ha hd hclose) :=
  P202.PlaneTangentComparison.homotopyWinding o T _
    (triangularLoopHomotopy T a b d ha hd hclose)

end UnitLoops

section ShortRotationTransport
open _root_.Topology

lemma noncuspidal_oangle_ne_pi (o : Orientation ℝ Plane (Fin 2))
    {v w : Plane} (hv : v ≠ 0) (hw : w ≠ 0)
    (hn : NormedSpace.normalize v ≠ -NormedSpace.normalize w) :
    o.oangle v w ≠ (Real.pi : Real.Angle) := by
  intro h
  have hr := (o.oangle_eq_pi_iff_sameRay_neg.mp h).2.2
  have he := hr.inv_norm_smul_eq hv (neg_ne_zero.mpr hw)
  exact hn (by simpa only [NormedSpace.normalize, norm_neg, smul_neg] using he)

/-- Literal short rotations between continuously varying noncuspidal directions
are continuous jointly in the direction parameter and the rotation parameter. -/
def shortRotationFamily {X : Type*} [TopologicalSpace X]
    (o : Orientation ℝ Plane (Fin 2)) (v w : C(X, Plane))
    (hv : ∀ x, v x ≠ 0) (hw : ∀ x, w x ≠ 0)
    (hn : ∀ x, NormedSpace.normalize (v x) ≠ -NormedSpace.normalize (w x)) :
    C(X × unitInterval, Plane) where
  toFun z := o.rotation ((z.2 : ℝ) * (o.oangle (v z.1) (w z.1)).toReal : ℝ)
    (NormedSpace.normalize (v z.1))
  continuous_toFun := by
    have ha : Continuous (fun x : X => (o.oangle (v x) (w x)).toReal) := by
      apply continuous_iff_continuousAt.mpr
      intro x
      exact ContinuousAt.comp (f := fun y : X => (v y, w y))
        (P202.PlaneTangentComparison.short_angle_continuousAt o (hv x) (hw x)
          (noncuspidal_oangle_ne_pi o (hv x) (hw x) (hn x)))
        (v.continuous.prodMk w.continuous).continuousAt
    have hnrm : Continuous (fun x : X => NormedSpace.normalize (v x)) :=
      (normalizedMap v hv).continuous
    simp only [Orientation.rotation_apply, Real.Angle.cos_coe, Real.Angle.sin_coe]
    have harg : Continuous (fun z : X × unitInterval =>
        (z.2 : ℝ) * (o.oangle (v z.1) (w z.1)).toReal) :=
      (continuous_subtype_val.comp continuous_snd).mul (ha.comp continuous_fst)
    exact ((Real.continuous_cos.comp harg).smul (hnrm.comp continuous_fst)).add
      ((Real.continuous_sin.comp harg).smul
        (o.rightAngleRotation.continuous.comp (hnrm.comp continuous_fst)))

lemma shortRotationFamily_unit {X : Type*} [TopologicalSpace X]
    (o : Orientation ℝ Plane (Fin 2)) (v w : C(X, Plane))
    (hv : ∀ x, v x ≠ 0) (hw : ∀ x, w x ≠ 0)
    (hn : ∀ x, NormedSpace.normalize (v x) ≠ -NormedSpace.normalize (w x))
    (z : X × unitInterval) :
    ‖shortRotationFamily o v w hv hw hn z‖ = 1 := by
  change ‖o.rotation _ (NormedSpace.normalize (v z.1))‖ = 1
  rw [LinearIsometryEquiv.norm_map]
  exact NormedSpace.norm_normalize (hv z.1)

lemma shortRotationFamily_start {X : Type*} [TopologicalSpace X]
    (o : Orientation ℝ Plane (Fin 2)) (v w : C(X, Plane))
    (hv : ∀ x, v x ≠ 0) (hw : ∀ x, w x ≠ 0)
    (hn : ∀ x, NormedSpace.normalize (v x) ≠ -NormedSpace.normalize (w x)) (x : X) :
    shortRotationFamily o v w hv hw hn (x, 0) = NormedSpace.normalize (v x) := by
  simp [shortRotationFamily, o.rotation_zero]

lemma shortRotationFamily_end {X : Type*} [TopologicalSpace X]
    (o : Orientation ℝ Plane (Fin 2)) (v w : C(X, Plane))
    (hv : ∀ x, v x ≠ 0) (hw : ∀ x, w x ≠ 0)
    (hn : ∀ x, NormedSpace.normalize (v x) ≠ -NormedSpace.normalize (w x)) (x : X) :
    shortRotationFamily o v w hv hw hn (x, 1) = NormedSpace.normalize (w x) := by
  have hangle : o.oangle (NormedSpace.normalize (v x)) (NormedSpace.normalize (w x)) =
      o.oangle (v x) (w x) := by
    rw [NormedSpace.normalize, NormedSpace.normalize]
    rw [o.oangle_smul_left_of_pos _ _ (inv_pos.mpr (norm_pos_iff.mpr (hv x))),
      o.oangle_smul_right_of_pos _ _ (inv_pos.mpr (norm_pos_iff.mpr (hw x)))]
  change o.rotation ((1 : ℝ) * (o.oangle (v x) (w x)).toReal : ℝ) _ = _
  rw [one_mul, Real.Angle.coe_toReal, ← hangle]
  exact (o.rotation_oangle_eq_iff_norm_eq _ _).mpr
    ((NormedSpace.norm_normalize (hv x)).trans (NormedSpace.norm_normalize (hw x)).symm)

/-- A positive triangular map cannot turn a nonzero vector through pi:
its diagonal entries are positive, so it has no negative real eigenvalue. -/
lemma upperTriangular_self_noncuspidal {a b d : ℝ}
    (ha : 0 < a) (hd : 0 < d) {v : Plane} (hv : v ≠ 0) :
    NormedSpace.normalize v ≠ -NormedSpace.normalize (upperTriangular a b d v) := by
  have hfv : upperTriangular a b d v ≠ 0 := by
    intro h
    exact hv (upperTriangular_injective ha.ne' hd.ne' (h.trans (map_zero _).symm))
  intro h
  rw [← NormedSpace.normalize_neg] at h
  obtain ⟨r, hr, he⟩ := (normalize_eq_iff_pos_smul hv (neg_ne_zero.mpr hfv)).mp h
  have h0 := congrArg (fun z : Plane => z 0) he
  have h1 := congrArg (fun z : Plane => z 1) he
  simp only [upperTriangular, LinearMap.coe_mk, AddHom.coe_mk,
    PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul, Matrix.cons_val_zero,
    Matrix.cons_val_one] at h0 h1
  have hv1 : v 1 = 0 := by
    have hp : (1 + r * d) * v 1 = 0 := by nlinarith [h1]
    exact (mul_eq_zero.mp hp).resolve_left (by positivity)
  have hv0 : v 0 = 0 := by
    rw [hv1] at h0
    have hp : (1 + r * a) * v 0 = 0 := by nlinarith [h0]
    exact (mul_eq_zero.mp hp).resolve_left (by positivity)
  apply hv
  ext i
  fin_cases i <;> assumption

lemma triangularPath_self_noncuspidal {a b d : ℝ}
    (ha : 0 < a) (hd : 0 < d) {v : Plane} (hv : v ≠ 0) (t : unitInterval) :
    NormedSpace.normalize v ≠ -NormedSpace.normalize (triangularPath a b d t v) :=
  upperTriangular_self_noncuspidal (diagonalInterpolation_pos ha t.property)
    (diagonalInterpolation_pos hd t.property) hv

/-- The path of an actual nonzero vector under the straight frame change. -/
def triangularVectorPath (a b d : ℝ) (v : Plane) : C(unitInterval, Plane) :=
  ⟨fun t => triangularPath a b d t v, by
    change Continuous (fun t : unitInterval =>
      !₂[(1 - (t : ℝ) + (t : ℝ) * a) * v 0 + ((t : ℝ) * b) * v 1,
        (1 - (t : ℝ) + (t : ℝ) * d) * v 1])
    fun_prop⟩

/-- Principal turns under a positive triangular frame change differ by the
endpoint direction corrections. No winding number is assumed in this identity. -/
lemma upperTriangular_corner_correction (o : Orientation ℝ Plane (Fin 2))
    {a b d : ℝ} (ha : 0 < a) (hd : 0 < d) {v w : Plane}
    (hv : v ≠ 0) (hw : w ≠ 0)
    (hn : NormedSpace.normalize v ≠ -NormedSpace.normalize w) :
    (o.oangle (upperTriangular a b d v) (upperTriangular a b d w)).toReal =
      (o.oangle v w).toReal + (o.oangle w (upperTriangular a b d w)).toReal -
        (o.oangle v (upperTriangular a b d v)).toReal := by
  let V := triangularVectorPath a b d v
  let W := triangularVectorPath a b d w
  have hV : ∀ s, V s ≠ 0 := fun s => triangularPath_ne_zero ha hd s.property hv
  have hW : ∀ s, W s ≠ 0 := fun s => triangularPath_ne_zero ha hd s.property hw
  have hVW : ∀ s, NormedSpace.normalize (V s) ≠ -NormedSpace.normalize (W s) :=
    fun s => triangularPath_preserves_noncuspidality ha hd s.property hv hw hn
  have hcv : Continuous (fun s => (o.oangle v (V s)).toReal) := by
    apply continuous_iff_continuousAt.mpr
    intro s
    exact ContinuousAt.comp (f := fun t => (v, V t))
      (P202.PlaneTangentComparison.short_angle_continuousAt o hv (hV s)
        (noncuspidal_oangle_ne_pi o hv (hV s)
          (triangularPath_self_noncuspidal ha hd hv s)))
      (continuous_const.prodMk V.continuous).continuousAt
  have hcw : Continuous (fun s => (o.oangle w (W s)).toReal) := by
    apply continuous_iff_continuousAt.mpr
    intro s
    exact ContinuousAt.comp (f := fun t => (w, W t))
      (P202.PlaneTangentComparison.short_angle_continuousAt o hw (hW s)
        (noncuspidal_oangle_ne_pi o hw (hW s)
          (triangularPath_self_noncuspidal ha hd hw s)))
      (continuous_const.prodMk W.continuous).continuousAt
  have hcVW : Continuous (fun s => (o.oangle (V s) (W s)).toReal) := by
    apply continuous_iff_continuousAt.mpr
    intro s
    exact ContinuousAt.comp (f := fun t => (V t, W t))
      (P202.PlaneTangentComparison.short_angle_continuousAt o (hV s) (hW s)
        (noncuspidal_oangle_ne_pi o (hV s) (hW s) (hVW s)))
      (V.continuous.prodMk W.continuous).continuousAt
  let D : C(unitInterval, ℝ) :=
    ⟨fun s => (o.oangle (V s) (W s)).toReal - (o.oangle v w).toReal -
      (o.oangle w (W s)).toReal + (o.oangle v (V s)).toReal,
      ((hcVW.sub continuous_const).sub hcw).add hcv⟩
  have hD (s : unitInterval) : (D s : Real.Angle) = 0 := by
    change (((o.oangle (V s) (W s)).toReal - (o.oangle v w).toReal -
      (o.oangle w (W s)).toReal + (o.oangle v (V s)).toReal : ℝ) : Real.Angle) = 0
    rw [Real.Angle.coe_add, Real.Angle.coe_sub, Real.Angle.coe_sub]
    simp only [Real.Angle.coe_toReal]
    have hx := o.oangle_add hv hw (hW s)
    have hy := o.oangle_add hv (hV s) (hW s)
    rw [← hx] at hy
    have hz : o.oangle (V s) (W s) =
        o.oangle v w + o.oangle w (W s) - o.oangle v (V s) := by
      apply eq_sub_iff_add_eq.mpr
      simpa only [add_comm] using hy
    rw [hz]
    abel
  have he := P202.PlaneTurning.radianCovering.const_of_comp D.continuous
    (fun s t => (hD s).trans (hD t).symm) (0 : unitInterval) 1
  have h0 : D 0 = 0 := by
    simp [D, V, W, triangularVectorPath, triangularPath_zero]
  have h1 : D 1 = 0 := he.symm.trans h0
  change (o.oangle (triangularPath a b d 1 v) (triangularPath a b d 1 w)).toReal -
    (o.oangle v w).toReal - (o.oangle w (triangularPath a b d 1 w)).toReal +
    (o.oangle v (triangularPath a b d 1 v)).toReal = 0 at h1
  rw [triangularPath_one] at h1
  linarith

/-- The canonical continuous real correction to the vector angle under a
positive triangular field of frames. -/
def triangularAngleCorrection {X : Type*} [TopologicalSpace X]
    (o : Orientation ℝ Plane (Fin 2)) (a b d : C(X, ℝ)) (v : C(X, Plane))
    (ha : ∀ x, 0 < a x) (hd : ∀ x, 0 < d x) (hv : ∀ x, v x ≠ 0) : C(X, ℝ) where
  toFun x := (o.oangle (v x) (upperTriangular (a x) (b x) (d x) (v x))).toReal
  continuous_toFun := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact ContinuousAt.comp (f := fun y => (v y, transformedMap a b d v y))
      (P202.PlaneTangentComparison.short_angle_continuousAt o (hv x)
        (transformedMap_ne_zero a b d v ha hd hv x)
        (noncuspidal_oangle_ne_pi o (hv x)
          (transformedMap_ne_zero a b d v ha hd hv x)
          (upperTriangular_self_noncuspidal (ha x) (hd x) (hv x))))
      (v.continuous.prodMk (transformedMap a b d v).continuous).continuousAt

/-- Adding the continuous correction transports any real angle lift to the
literal transformed vector directions. -/
lemma triangularAngleCorrection_lift {X : Type*} [TopologicalSpace X]
    (o : Orientation ℝ Plane (Fin 2)) (a b d : C(X, ℝ)) (v : C(X, Plane))
    (ha : ∀ x, 0 < a x) (hd : ∀ x, 0 < d x) (hv : ∀ x, v x ≠ 0)
    (r : Plane) (hr : r ≠ 0) (θ : C(X, ℝ))
    (hθ : ∀ x, (θ x : Real.Angle) = o.oangle r (v x)) (x : X) :
    ((θ x + triangularAngleCorrection o a b d v ha hd hv x : ℝ) : Real.Angle) =
      o.oangle r (upperTriangular (a x) (b x) (d x) (v x)) := by
  rw [Real.Angle.coe_add, hθ]
  change o.oangle r (v x) +
    (((o.oangle (v x) (upperTriangular (a x) (b x) (d x) (v x))).toReal : ℝ) :
      Real.Angle) = _
  rw [Real.Angle.coe_toReal]
  exact o.oangle_add hr (hv x) (transformedMap_ne_zero a b d v ha hd hv x)

/-- Smooth angle increments plus literal short corner turns are invariant
under a positive triangular frame field that agrees at each joined endpoint.
The continuous angle correction above provides the corrected angle choices. -/
lemma upperTriangular_totalTurning_invariant {ι : Type*} [Fintype ι]
    (o : Orientation ℝ Plane (Fin 2)) (rotateIndex : Equiv.Perm ι)
    (v w : ι → Plane) (hv : ∀ i : ι, v i ≠ 0) (hw : ∀ i : ι, w i ≠ 0)
    (hn : ∀ i : ι, NormedSpace.normalize (w i) ≠ -NormedSpace.normalize (v (rotateIndex i)))
    (a0 b0 d0 a1 b1 d1 : ι → ℝ)
    (ha1 : ∀ i : ι, 0 < a1 i) (hd1 : ∀ i : ι, 0 < d1 i)
    (hjoin : ∀ i : ι, a1 i = a0 (rotateIndex i) ∧ b1 i = b0 (rotateIndex i) ∧ d1 i = d0 (rotateIndex i))
    (start finish : ι → ℝ) :
    (∑ i : ι, ((finish i + (o.oangle (w i) (upperTriangular (a1 i) (b1 i) (d1 i) (w i))).toReal) -
      (start i + (o.oangle (v i) (upperTriangular (a0 i) (b0 i) (d0 i) (v i))).toReal) +
      (o.oangle (upperTriangular (a1 i) (b1 i) (d1 i) (w i))
        (upperTriangular (a1 i) (b1 i) (d1 i) (v (rotateIndex i)))).toReal)) =
      ∑ i : ι, (finish i - start i + (o.oangle (w i) (v (rotateIndex i))).toReal) := by
  classical
  let δ : ι → ℝ := fun i =>
    (o.oangle (v i) (upperTriangular (a0 i) (b0 i) (d0 i) (v i))).toReal
  have he (i : ι) :
      (finish i + (o.oangle (w i) (upperTriangular (a1 i) (b1 i) (d1 i) (w i))).toReal) -
      (start i + (o.oangle (v i) (upperTriangular (a0 i) (b0 i) (d0 i) (v i))).toReal) +
      (o.oangle (upperTriangular (a1 i) (b1 i) (d1 i) (w i))
        (upperTriangular (a1 i) (b1 i) (d1 i) (v (rotateIndex i)))).toReal =
      (finish i - start i + (o.oangle (w i) (v (rotateIndex i))).toReal) +
        (δ (rotateIndex i) - δ i) := by
    rw [upperTriangular_corner_correction o (ha1 i) (hd1 i) (hw i) (hv (rotateIndex i)) (hn i)]
    rw [(hjoin i).1, (hjoin i).2.1, (hjoin i).2.2]
    dsimp [δ]
    ring
  simp_rw [he, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [Equiv.sum_comp rotateIndex δ, sub_self, add_zero]

end ShortRotationTransport

/-- Every boundary arc in a presentation is an arc of the original region. -/
theorem arc_mem_carrier (R : PlanarRegion)
    (A : ∀ i, P202Specs.PlaneTurning.ArcPresentation (R.curve i))
    (i : Fin R.boundaryCount) (j : Fin (A i).count) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    (A i).arc j t ∈ R.carrier := by
  have htrace : (A i).arc j t ∈ (R.curve i).trace := by
    rw [(A i).agrees j t ht]
    exact ⟨_, rfl⟩
  have hbd : (A i).arc j t ∈ R.boundary := by
    change (A i).arc j t ∈ frontier R.domain
    rw [R.boundary_eq]
    exact mem_iUnion.mpr ⟨i, htrace⟩
  exact frontier_subset_closure hbd

/-- The actual inverse chart differential is injective at a chart point. -/
theorem chartVector_ne_zero (c : ModelChart 2 .euclidean M)
    (hc : c ∈ S.smoothStructure.val) (x v : Plane)
    (hx : P202Specs.ChartRegionStokes.modelPoint x ∈ c.target) (hv : v ≠ 0) :
    chartVector c hc x v ≠ 0 := by
  rw [chartVector, dite_eq_left hx]
  intro h
  have hh := congrArg ((tangentStructure S).fiberCoordinates.equiv c hc (chartPoint c x)
    (c.map_target hx)) h
  simp only [LinearEquiv.apply_symm_apply, map_zero] at hh
  exact hv ((EuclideanSpace.equiv (Fin 2) ℝ).injective (hh.trans (map_zero _).symm))

/-- Regular coordinate arcs have strictly positive intrinsic metric speed,
including both endpoint velocities used at a corner. -/
theorem arcSpeed_pos (g : RiemannianMetric S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (R : PlanarRegion) (hR : R.carrier ⊆ P202Specs.ChartRegionStokes.chartTarget c)
    (A : ∀ i, P202Specs.PlaneTurning.ArcPresentation (R.curve i))
    (i : Fin R.boundaryCount) (j : Fin (A i).count) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    0 < arcSpeed g c hc (A i) j t := by
  apply Real.sqrt_pos.mpr
  apply g.positive
  exact chartVector_ne_zero c hc _ _ (hR (arc_mem_carrier R A i j t ht))
    ((A i).regular j t ht)

/-- Removing the speed factors gives the intrinsic curvature one-form along
an actual boundary arc; only strict positivity of the actual speed is used. -/
theorem geodesicIntegrand_eq_pairing (g : RiemannianMetric S)
    (C : Connection (tangentBundle S))
    (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (R : PlanarRegion) (hR : R.carrier ⊆ P202Specs.ChartRegionStokes.chartTarget c)
    (A : ∀ i, P202Specs.PlaneTurning.ArcPresentation (R.curve i))
    (i : Fin R.boundaryCount) (j : Fin (A i).count) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    geodesicIntegrand g C o c hc (A i) j t =
      pairing g (surfaceArc c (A i) j t)
        (P202.CurveConnectionData.covariantDerivative C (surfaceArc c (A i) j)
          (unitTangent g (surfaceArc c (A i) j) (arcVelocity c hc (A i) j)) t)
        (rotation g o (surfaceArc c (A i) j t)
          (unitTangent g (surfaceArc c (A i) j) (arcVelocity c hc (A i) j) t)) := by
  have hs := (arcSpeed_pos g c hc R hR A i j t ht).ne'
  unfold geodesicIntegrand signedCurveCurvature signedCurvature curvatureVector
  simp only [pairing, LinearMap.BilinForm.smul_left]
  field_simp

/-- The source curves admit finite smooth presentations without any new
regularity or existence premise. -/
theorem boundaryPresentations (R : PlanarRegion) :
    Nonempty (∀ i, P202Specs.PlaneTurning.ArcPresentation (R.curve i)) := by
  classical
  exact ⟨fun i => Classical.choice (P202.PlaneTurning.presentationExists (R.curve i))⟩

/-- The principal angle stays strictly within (-π,π) after any injective
linear change of coordinates. The target metric need not be the source metric. -/
theorem mappedAngle_bounds {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [Fact (Module.finrank ℝ F = 2)]
    (o : Orientation ℝ F (Fin 2)) (f : Plane →ₗ[ℝ] F)
    (hf : Function.Injective f) {v w : Plane} (hv : v ≠ 0) (hw : w ≠ 0)
    (hvw : NormedSpace.normalize v ≠ -NormedSpace.normalize w) :
    -Real.pi < (o.oangle (f v) (f w)).toReal ∧
      (o.oangle (f v) (f w)).toReal < Real.pi := by
  have hfv : f v ≠ 0 := fun h => hv (hf (h.trans (map_zero _).symm))
  have hfw : f w ≠ 0 := fun h => hw (hf (h.trans (map_zero _).symm))
  have hn := linearMap_preserves_noncuspidality f hf hv hw hvw
  have hpi : o.oangle (f v) (f w) ≠ (Real.pi : Real.Angle) := by
    intro h
    have hr := (o.oangle_eq_pi_iff_sameRay_neg.mp h).2.2
    have he := hr.inv_norm_smul_eq hfv (neg_ne_zero.mpr hfw)
    exact hn (by simpa only [NormedSpace.normalize, norm_neg, smul_neg] using he)
  exact ⟨Real.Angle.neg_pi_lt_toReal _,
    (Real.Angle.toReal_le_pi _).lt_of_ne
      (fun h => hpi (Real.Angle.toReal_eq_pi_iff.mp h))⟩

/-- Noncuspidality is retained by the actual inverse chart differential and
the actual Riemannian norm, at the common endpoint of each pair of arcs. -/
theorem metricCornerAngle_bounds (g : RiemannianMetric S)
    (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (R : PlanarRegion) (hR : R.carrier ⊆ P202Specs.ChartRegionStokes.chartTarget c)
    (A : ∀ i, P202Specs.PlaneTurning.ArcPresentation (R.curve i))
    (i : Fin R.boundaryCount) (j : Fin (A i).count) :
    -Real.pi < metricCornerAngle g o c hc (A i) j ∧
      metricCornerAngle g o c hc (A i) j < Real.pi := by
  let x := (A i).arc j 1
  have hx : P202Specs.ChartRegionStokes.modelPoint x ∈ c.target :=
    hR (arc_mem_carrier R A i j 1 (by simp))
  let p := chartPoint c x
  letI := (metricCore g p).toNormedAddCommGroup
  letI := InnerProductSpace.ofCore (metricCore g p).toCore
  letI := (SmoothManifolds.tangent_dimension S p).1
  letI : Fact (Module.finrank ℝ (TangentSpace S p) = 2) :=
    ⟨(SmoothManifolds.tangent_dimension S p).2⟩
  let f : Plane ≃ₗ[ℝ] TangentSpace S p :=
    (EuclideanSpace.equiv (Fin 2) ℝ).toLinearEquiv.trans
      ((tangentStructure S).fiberCoordinates.equiv c hc p (c.map_target hx)).symm
  have he (v : Plane) : chartVector c hc x v = f v := by
    simp only [chartVector, dite_eq_left hx]
    rfl
  change -Real.pi < ((planeOrientation g o p).oangle
      (chartVector c hc x (P202Specs.PlaneTurning.velocity (A i) j 1))
      (chartVector c hc x (P202Specs.PlaneTurning.velocity (A i)
        (finRotate (A i).count j) 0))).toReal ∧
    ((planeOrientation g o p).oangle
      (chartVector c hc x (P202Specs.PlaneTurning.velocity (A i) j 1))
      (chartVector c hc x (P202Specs.PlaneTurning.velocity (A i)
        (finRotate (A i).count j) 0))).toReal < Real.pi
  simp only [he]
  exact mappedAngle_bounds (planeOrientation g o p) f.toLinearMap f.injective
    ((A i).regular j 1 (by simp))
    ((A i).regular (finRotate (A i).count j) 0 (by simp)) ((A i).noncuspidal j)

/-- Every induced traversal, including an inner boundary, gives a strict
interior angle in (0,2π). No convexity restriction is used. -/
theorem interiorAngle_bounds (g : RiemannianMetric S)
    (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (R : PlanarRegion) (hR : R.carrier ⊆ P202Specs.ChartRegionStokes.chartTarget c)
    (A : ∀ i, P202Specs.PlaneTurning.ArcPresentation (R.curve i))
    (s : Fin R.boundaryCount → ℝ) (hs : IsInducedBoundaryOrientation R s)
    (i : Fin R.boundaryCount) (j : Fin (A i).count) :
    0 < interiorAngle g o c hc (A i) (s i) j ∧
      interiorAngle g o c hc (A i) (s i) j < 2 * Real.pi := by
  obtain ⟨hl, hu⟩ := metricCornerAngle_bounds g o c hc R hR A i j
  rcases (hs i).1 with h | h <;> simp only [interiorAngle, h] <;>
    constructor <;> linarith

/-- The corner contribution is the signed principal turn, with the same
boundary sign as the geodesic-curvature integral. -/
theorem exteriorAngleSum_eq_signed (g : RiemannianMetric S)
    (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (R : PlanarRegion) (A : ∀ i, P202Specs.PlaneTurning.ArcPresentation (R.curve i))
    (s : Fin R.boundaryCount → ℝ) :
    exteriorAngleSum g o c hc R A s =
      ∑ i, s i * ∑ j, metricCornerAngle g o c hc (A i) j := by
  simp only [exteriorAngleSum, interiorAngle, sub_sub_cancel, Finset.mul_sum]

section BoundaryArcIntegration
open MeasureTheory P202Specs.PlaneTurning
open P202Specs.ChartRegionStokes (OneForm)

/-- Affine changes of a regular arc preserve the actual one-form integral.
Only the interior derivatives are compared, so corner endpoints are allowed. -/
theorem arcIntegral_eq_parameterIntegral {c : RegularJordanCurve}
    (A : ArcPresentation c) (j : Fin A.count) (omega : OneForm) :
    (∫ t in (0 : ℝ)..1, omega (A.arc j t) (velocity A j t)) =
      ∫ y in A.time j.castSucc..A.time j.succ,
        omega (realLift c.parametrization y) (deriv (realLift c.parametrization) y) := by
  let a := A.time j.castSucc
  let b := A.time j.succ
  let d := b - a
  have hab : a < b := A.strictMono j.castSucc_lt_succ
  have hd : 0 < d := sub_pos.mpr hab
  let f : ℝ → Plane := fun y => A.arc j ((y - a) / d)
  have he : EqOn f (realLift c.parametrization) (Ioo a b) := by
    intro y hy
    have ht : (y - a) / d ∈ Icc (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg (sub_nonneg.mpr hy.1.le) hd.le
      · exact (div_le_one hd).mpr (by dsimp [d]; linarith [hy.2])
    change A.arc j ((y - a) / d) = _
    rw [A.agrees j _ ht]
    congr 1
    change a + d * ((y - a) / d) = y
    field_simp
    ring
  have hder (y : ℝ) (hy : y ∈ Ioo a b) :
      deriv (realLift c.parametrization) y = d⁻¹ • velocity A j ((y - a) / d) := by
    obtain ⟨δ, hδ, hsm⟩ := A.smooth j
    have ht : (y - a) / d ∈ Ioo (-δ) (1 + δ) := by
      have ht0 : 0 < (y - a) / d := div_pos (sub_pos.mpr hy.1) hd
      have ht1 : (y - a) / d < 1 := (div_lt_one hd).mpr (by dsimp [d]; linarith [hy.2])
      constructor <;> linarith
    have hA := (hsm.contDiffAt (isOpen_Ioo.mem_nhds ht)).differentiableAt (by simp)
    have hf : HasDerivAt f (d⁻¹ • velocity A j ((y - a) / d)) y := by
      convert! hA.hasDerivAt.scomp y
        (((hasDerivAt_id y).sub_const a).mul_const d⁻¹) using 1
      simp [velocity, div_eq_mul_inv]
    exact (he.deriv isOpen_Ioo hy).symm.trans hf.deriv
  have hchange :
      (∫ t in (0 : ℝ)..1, omega (A.arc j t) (velocity A j t)) =
      d * ∫ t in (0 : ℝ)..1,
        omega (realLift c.parametrization (a + d * t))
          (deriv (realLift c.parametrization) (a + d * t)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
    intro t ht
    have hy : a + d * t ∈ Ioo a b := by
      constructor
      · linarith [mul_pos hd ht.1]
      · have hdt : d * t < d := mul_lt_of_lt_one_right hd ht.2
        dsimp [d] at hdt
        linarith
    dsimp only
    rw [hder _ hy]
    have harg : (a + d * t - a) / d = t := by field_simp; ring
    rw [harg, ← A.agrees j t ⟨ht.1.le, ht.2.le⟩]
    simp only [map_smul, smul_eq_mul]
    field_simp
  rw [hchange]
  have hi := intervalIntegral.smul_integral_comp_add_mul
    (fun y => omega (realLift c.parametrization y) (deriv (realLift c.parametrization) y))
    (a := (0 : ℝ)) (b := (1 : ℝ)) d a
  simpa [smul_eq_mul, d] using hi


/-- A finite positive partition of a period splits an integrable function. -/
theorem integral_eq_sum_presentation {c : RegularJordanCurve} (A : ArcPresentation c)
    {f : ℝ → ℝ} (hint : IntervalIntegrable f volume 0 1) :
    (∫ t in (0 : ℝ)..1, f t) =
      ∑ j : Fin A.count, ∫ t in A.time j.castSucc..A.time j.succ, f t := by
  have htime (k : Fin (A.count + 1)) : A.time k ∈ Icc (0 : ℝ) 1 := by
    constructor
    · rw [← A.first]
      exact A.strictMono.monotone (Fin.zero_le k)
    · rw [← A.last]
      exact A.strictMono.monotone (Fin.le_last k)
  have hi (k : Fin (A.count + 1)) : IntervalIntegrable f volume 0 (A.time k) :=
    hint.mono_set (uIcc_subset_uIcc (by simp)
      (by simpa only [uIcc_of_le zero_le_one] using htime k))
  let F : ℝ → ℝ := fun y => ∫ t in (0 : ℝ)..y, f t
  have harc (j : Fin A.count) :
      (∫ t in A.time j.castSucc..A.time j.succ, f t) =
        F (A.time j.succ) - F (A.time j.castSucc) :=
    (intervalIntegral.integral_interval_sub_left (hi j.succ) (hi j.castSucc)).symm
  simp_rw [harc]
  rw [Finset.sum_sub_distrib]
  have hleft := Fin.sum_univ_succ (fun k : Fin (A.count + 1) => F (A.time k))
  have hright := Fin.sum_univ_castSucc (fun k : Fin (A.count + 1) => F (A.time k))
  simp only [A.first, A.last, F, intervalIntegral.integral_same] at hleft hright
  linarith


/-- The periodic Stokes integral equals the sum over any presentation of
that original curve. Only the finitely many endpoint values are omitted. -/
theorem componentIntegral_eq_arcs (R : PlanarRegion) {U : Set Plane}
    (hRU : R.carrier ⊆ U) {omega : P202Specs.ChartRegionStokes.OneForm}
    (homega : ContinuousOn omega U)
    (i : Fin R.boundaryCount) (A : ArcPresentation (R.curve i)) :
    P202Specs.ChartRegionStokes.componentIntegral omega (R.curve i) =
      ∑ j, ∫ t in (0 : ℝ)..1, omega (A.arc j t) (velocity A j t) := by
  have hint := (P202.ChartRegionStokes.boundary_integrable R hRU homega i).congr_ae
    (by simpa only [uIoc_of_le zero_le_one] using
      P202.ChartRegionStokes.boundaryIntegrand_ae_eq omega (R.curve i))
  rw [P202.ChartRegionStokes.componentIntegral_eq_unmasked]
  rw [integral_eq_sum_presentation A hint]
  apply Finset.sum_congr rfl
  intro j hj
  exact (arcIntegral_eq_parameterIntegral A j omega).symm

/-- Every induced boundary sign acts on the same finite arc decomposition. -/
theorem boundaryIntegral_eq_arcs (R : PlanarRegion) {U : Set Plane}
    (hRU : R.carrier ⊆ U) {omega : P202Specs.ChartRegionStokes.OneForm}
    (homega : ContinuousOn omega U)
    (A : ∀ i, ArcPresentation (R.curve i)) (s : Fin R.boundaryCount → ℝ) :
    P202Specs.ChartRegionStokes.boundaryIntegral R omega s =
      ∑ i, s i * ∑ j, ∫ t in (0 : ℝ)..1, omega ((A i).arc j t) (velocity (A i) j t) := by
  unfold P202Specs.ChartRegionStokes.boundaryIntegral
  simp_rw [componentIntegral_eq_arcs R hRU homega _ (A _)]

end BoundaryArcIntegration

/-- The final arithmetic uses the previously proved topological Euler
invariant, including its finite-type domain, rather than defining χ = 2-b. -/
theorem formula_of_boundaryCount (R : PlanarRegion) (bulk boundary corners : ℝ)
    (h : bulk + boundary + corners = 2 * Real.pi * (2 - (R.boundaryCount : ℝ))) :
    (∃ e : P202Specs.EulerPoincare.HomologyFiniteType ℚ R.carrier,
      bulk + boundary + corners =
        2 * Real.pi * (P202Specs.EulerPoincare.topologicalEuler R.carrier e : ℝ)) ∧
    (R.boundaryCount = 1 → bulk + boundary + corners = 2 * Real.pi) := by
  obtain ⟨e, he, _⟩ := P202.PlanarRegionEuler.planarRegionEuler R
  constructor
  · refine ⟨e, ?_⟩
    rw [he]
    exact_mod_cast h
  · intro hb
    norm_num [hb] at h
    exact h

/-- The induced outer sign agrees with the bounded-left sign, and every
inner sign is opposite. The existence of `outer : Fin b` already implies b>0. -/
theorem weighted_sign_sum {b : ℕ} (outer : Fin b) (s : Fin b → ℝ)
    (hs : ∀ i, s i = 1 ∨ s i = -1) :
    (∑ i, s i * (if i = outer then s i else -s i)) = 2 - (b : ℝ) := by
  calc
    _ = ∑ i : Fin b, ((if i = outer then (2 : ℝ) else 0) - 1) := by
      apply Finset.sum_congr rfl
      intro i hi
      rcases hs i with h | h <;> rw [h] <;>
        by_cases hoi : i = outer <;> norm_num [hoi]
    _ = 2 - (b : ℝ) := by
      rw [Finset.sum_sub_distrib]
      simp

/-- Componentwise boundary transport gives the complete signed boundary
identity before Stokes or an Euler characteristic is used. -/
theorem weighted_component_assembly {b : ℕ} (outer : Fin b) (s : Fin b → ℝ)
    (hs : ∀ i, s i = 1 ∨ s i = -1)
    (kg corners omega : Fin b → ℝ) (k : ℝ)
    (hcomp : ∀ i, kg i + corners i =
      k * (if i = outer then s i else -s i) + omega i) :
    (∑ i, s i * kg i) + (∑ i, s i * corners i) =
      k * (2 - (b : ℝ)) + ∑ i, s i * omega i := by
  calc
    _ = ∑ i, s i * (kg i + corners i) := by
      simp only [mul_add, Finset.sum_add_distrib]
    _ = ∑ i, (k * (s i * (if i = outer then s i else -s i)) + s i * omega i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hcomp i]
      ring
    _ = k * (∑ i, s i * (if i = outer then s i else -s i)) +
        ∑ i, s i * omega i := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = _ := by rw [weighted_sign_sum outer s hs]

section RegionBoundaryAssembly
open MeasureTheory

/-- Specialization to the original boundary integrals and metric corner sum. -/
theorem region_boundary_assembly
    {M : Type u} [TopologicalSpace M] {S : SmoothManifold 2 .euclidean M}
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (R : PlanarRegion) (outer : Fin R.boundaryCount)
    (A : ∀ i, P202Specs.PlaneTurning.ArcPresentation (R.curve i))
    (s : Fin R.boundaryCount → ℝ) (hs : ∀ i, s i = 1 ∨ s i = -1)
    (omega : P202Specs.ChartRegionStokes.OneForm)
    (hcomp : ∀ i,
      (∑ j, ∫ t in (0 : ℝ)..1, geodesicIntegrand g C o c hc (A i) j t) +
        (∑ j, metricCornerAngle g o c hc (A i) j) =
      2 * Real.pi * (if i = outer then s i else -s i) +
        P202Specs.ChartRegionStokes.componentIntegral omega (R.curve i)) :
    geodesicIntegral g C o c hc R A s + exteriorAngleSum g o c hc R A s =
      2 * Real.pi * (2 - (R.boundaryCount : ℝ)) +
        P202Specs.ChartRegionStokes.boundaryIntegral R omega s := by
  simpa only [geodesicIntegral, exteriorAngleSum, interiorAngle, sub_sub_cancel,
    Finset.mul_sum, P202Specs.ChartRegionStokes.boundaryIntegral] using
    weighted_component_assembly outer s hs
      (fun i => ∑ j, ∫ t in (0 : ℝ)..1, geodesicIntegrand g C o c hc (A i) j t)
      (fun i => ∑ j, metricCornerAngle g o c hc (A i) j)
      (fun i => P202Specs.ChartRegionStokes.componentIntegral omega (R.curve i))
      (2 * Real.pi) hcomp

end RegionBoundaryAssembly

/-- Once the two geometric calculations have been proved for an actual
smooth connection form, Stokes gives integrability and the full Euler and
disk identities. This is only an assembly lemma: neither geometric premise
is assumed by `Expected.localGaussBonnet`. -/
theorem connectionForm_assembly (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (T : CurvatureTensor S)
    (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (R : PlanarRegion) (A : ∀ i, P202Specs.PlaneTurning.ArcPresentation (R.curve i))
    (s : Fin R.boundaryCount → ℝ) (hs : IsInducedBoundaryOrientation R s)
    (U : Set Plane) (hU : IsOpen U) (hRU : R.carrier ⊆ U)
    (omega : P202Specs.ChartRegionStokes.OneForm) (hsm : ContDiffOn ℝ ∞ omega U)
    (hK : ∀ x ∈ R.carrier, P202Specs.ChartRegionStokes.exteriorCoefficient omega x =
      -curvatureIntegrand g T c hc x)
    (hturn : geodesicIntegral g C o c hc R A s + exteriorAngleSum g o c hc R A s =
      2 * Real.pi * (2 - (R.boundaryCount : ℝ)) +
        P202Specs.ChartRegionStokes.boundaryIntegral R omega s) :
    MeasureTheory.IntegrableOn (curvatureIntegrand g T c hc) R.carrier ∧
      (∃ e : P202Specs.EulerPoincare.HomologyFiniteType ℚ R.carrier,
        curvatureIntegral g T c hc R + geodesicIntegral g C o c hc R A s +
          exteriorAngleSum g o c hc R A s =
            2 * Real.pi * (P202Specs.EulerPoincare.topologicalEuler R.carrier e : ℝ)) ∧
      (R.boundaryCount = 1 →
        curvatureIntegral g T c hc R + geodesicIntegral g C o c hc R A s +
          exteriorAngleSum g o c hc R A s = 2 * Real.pi) := by
  have hst := P202.ChartRegionStokes.stokes R U omega hU hRU hsm s hs
  have hmeas : MeasurableSet R.carrier := isClosed_closure.measurableSet
  have hint : MeasureTheory.IntegrableOn (curvatureIntegrand g T c hc) R.carrier :=
    hst.1.neg.congr_fun (fun x hx => by
      change -P202Specs.ChartRegionStokes.exteriorCoefficient omega x =
        curvatureIntegrand g T c hc x
      rw [hK x hx, neg_neg]) hmeas
  have hbulk : P202Specs.ChartRegionStokes.bulkIntegral R omega =
      -curvatureIntegral g T c hc R := by
    unfold P202Specs.ChartRegionStokes.bulkIntegral curvatureIntegral
    rw [← MeasureTheory.integral_neg]
    exact MeasureTheory.setIntegral_congr_fun hmeas hK
  have hformula : curvatureIntegral g T c hc R + geodesicIntegral g C o c hc R A s +
      exteriorAngleSum g o c hc R A s = 2 * Real.pi * (2 - (R.boundaryCount : ℝ)) := by
    linarith [hst.2.2, hbulk]
  exact ⟨hint, formula_of_boundaryCount R _ _ _ hformula⟩


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


section AngleLiftDifferentiation
/-- A continuous real angle is differentiable whenever its sine and cosine
are differentiable. This is local and requires no preselected principal branch. -/
theorem hasDerivAt_angle_of_cos_sin {θ : ℝ → ℝ} {t c' s' : ℝ}
    (hcont : ContinuousAt θ t)
    (hcos : HasDerivAt (fun s => Real.cos (θ s)) c' t)
    (hsin : HasDerivAt (fun s => Real.sin (θ s)) s' t) :
    HasDerivAt θ (Real.cos (θ t) * s' - Real.sin (θ t) * c') t := by
  let f : ℝ → ℝ := fun s => Real.sin (θ s) * Real.cos (θ t) -
    Real.cos (θ s) * Real.sin (θ t)
  have hf : HasDerivAt f (Real.cos (θ t) * s' - Real.sin (θ t) * c') t := by
    convert (hsin.mul_const (Real.cos (θ t))).sub (hcos.mul_const (Real.sin (θ t))) using 1 <;> ring
  have hft : f t = 0 := by dsimp [f]; ring
  have ha : HasDerivAt Real.arcsin 1 (f t) := by
    rw [hft]
    simpa using Real.hasDerivAt_arcsin (by norm_num : (0 : ℝ) ≠ -1)
      (by norm_num : (0 : ℝ) ≠ 1)
  have hg := (ha.comp t hf).add_const (θ t)
  simp only [one_mul] at hg
  apply hg.congr_of_eventuallyEq
  have hn : ∀ᶠ s in 𝓝 t, θ s - θ t ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    (hcont.sub_const (θ t)).eventually
      (isOpen_Ioo.mem_nhds (by simp only [sub_self, mem_Ioo]; constructor <;> linarith [Real.pi_pos]))
  filter_upwards [hn] with s hs
  dsimp [f]
  rw [← Real.sin_sub, Real.arcsin_sin hs.1.le hs.2.le]
  ring

/-- The same local inverse argument works for one-sided arc endpoints. -/
theorem hasDerivWithinAt_angle_of_cos_sin {θ : ℝ → ℝ} {J : Set ℝ} {t c' s' : ℝ}
    (hcont : ContinuousWithinAt θ J t)
    (hcos : HasDerivWithinAt (fun s => Real.cos (θ s)) c' J t)
    (hsin : HasDerivWithinAt (fun s => Real.sin (θ s)) s' J t) :
    HasDerivWithinAt θ (Real.cos (θ t) * s' - Real.sin (θ t) * c') J t := by
  let f : ℝ → ℝ := fun s => Real.sin (θ s) * Real.cos (θ t) -
    Real.cos (θ s) * Real.sin (θ t)
  have hf : HasDerivWithinAt f (Real.cos (θ t) * s' - Real.sin (θ t) * c') J t := by
    convert (hsin.mul_const (Real.cos (θ t))).sub (hcos.mul_const (Real.sin (θ t))) using 1 <;> ring
  have hft : f t = 0 := by dsimp [f]; ring
  have ha : HasDerivAt Real.arcsin 1 (f t) := by
    rw [hft]
    simpa using Real.hasDerivAt_arcsin (by norm_num : (0 : ℝ) ≠ -1)
      (by norm_num : (0 : ℝ) ≠ 1)
  have hg := (ha.comp_hasDerivWithinAt t hf).add_const (θ t)
  simp only [one_mul] at hg
  apply hg.congr_of_eventuallyEq _ (by change θ t = Real.arcsin (f t) + θ t; rw [hft, Real.arcsin_zero, zero_add])
  have hn : ∀ᶠ s in 𝓝[J] t, θ s - θ t ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    (hcont.sub_const (θ t)).eventually
      (isOpen_Ioo.mem_nhds (by simp only [sub_self, mem_Ioo]; constructor <;> linarith [Real.pi_pos]))
  filter_upwards [hn] with s hs
  dsimp [f]
  rw [← Real.sin_sub, Real.arcsin_sin hs.1.le hs.2.le]
  ring

end AngleLiftDifferentiation

section IntrinsicBoundaryCalculus
open scoped RealInnerProductSpace
open SmoothManifolds.BundleData SmoothManifolds.BundleOperationsData
open P202.CurveConnectionData

/-- Actual positive orthonormal tangent vectors have the prescribed rotation. -/
theorem rotation_of_positive_orthonormal_pair (g : RiemannianMetric S)
    (o : SmoothManifolds.OrientationData.Orientation S) (p : M)
    (X Y : TangentSpace S p)
    (hXX : pairing g p X X = 1) (hYY : pairing g p Y Y = 1)
    (hXY : pairing g p X Y = 0)
    (hpos : PositiveBoundaryOrientation o p X Y) :
    rotation g o p X = Y := by
  letI := (metricCore g p).toNormedAddCommGroup
  letI := InnerProductSpace.ofCore (metricCore g p).toCore
  letI := (SmoothManifolds.tangent_dimension S p).1
  letI : Fact (Module.finrank ℝ (TangentSpace S p) = 2) :=
    ⟨(SmoothManifolds.tangent_dimension S p).2⟩
  let q := planeOrientation g o p
  have hTT : ⟪X, X⟫ = 1 := hXX
  have hNN : ⟪Y, Y⟫ = 1 := hYY
  have hTN : ⟪X, Y⟫ = 0 := hXY
  have ha : 0 < q.areaForm X Y := (P202.Geometry.SurfaceBoundaryGeometry.orientation_bridge g p o X Y).mp hpos
  have he := q.inner_sq_add_areaForm_sq X Y
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, hTT, hNN, hTN] at he
  have ha1 : q.areaForm X Y = 1 := by nlinarith
  have hJN : ⟪q.rightAngleRotation X, Y⟫ = 1 := by
    rw [q.inner_rightAngleRotation_left, ha1]
  have hNJ : ⟪Y, q.rightAngleRotation X⟫ = 1 := by rw [real_inner_comm]; exact hJN
  have hz : ⟪Y - q.rightAngleRotation X, Y - q.rightAngleRotation X⟫ = 0 := by
    rw [inner_sub_sub_self, hNN, hNJ, hJN, q.inner_comp_rightAngleRotation, hTT]
    norm_num
  exact (sub_eq_zero.mp (inner_self_eq_zero.mp hz)).symm

open SmoothManifolds.BundleData

theorem orthonormalFrame_rotation_first (g : RiemannianMetric S)
    (o : SmoothManifolds.OrientationData.Orientation S)
    {U : Set M} {hU : IsOpen U} (b : LocalFrame (tangentBundle S) U hU)
    (hon : ∀ p i j, pairing g p.val (b.section_ i p) (b.section_ j p) =
      if i = j then 1 else 0)
    (p : U)
    (hpos : PositiveBoundaryOrientation o p.val (b.section_ 0 p) (b.section_ 1 p)) :
    rotation g o p.val (b.section_ 0 p) = b.section_ 1 p := by
  exact rotation_of_positive_orthonormal_pair g o p.val _ _
    (by simpa using hon p 0 0) (by simpa using hon p 1 1)
    (by simpa using hon p 0 1) hpos


/-- The actual intrinsic curve derivative in an orthonormal frame has the
moving-frame coefficient θ′ + Γ₁₀(γ′). The coefficient hypothesis is local at
the parameter, so it applies to genuine tangent-angle lifts on each smooth arc. -/
theorem frame_trig_covariantDerivative
    (C : Connection (tangentBundle S))
    {U : Set M} {hU : IsOpen U} (b : LocalFrame (tangentBundle S) U hU)
    {c : ℝ → M} {f : (s : ℝ) → TangentSpace S (c s)} {t : ℝ}
    (hp : c t ∈ U) {V : TangentSpace S (c t)}
    (hV : HasVelocityWithinAt S c univ t V)
    (hdiag : ∀ i : Fin 2, connectionForm C b ⟨c t, hp⟩ i i V = 0)
    (hskew : connectionForm C b ⟨c t, hp⟩ 0 1 V =
      -connectionForm C b ⟨c t, hp⟩ 1 0 V)
    {θ : ℝ → ℝ} {θ' : ℝ} (hθ : HasDerivAt θ θ' t)
    (hcoeff : coefficientsAlong b c f =ᶠ[𝓝 t]
      (fun s => ![Real.cos (θ s), Real.sin (θ s)])) :
    covariantDerivative C c f t =
      (θ' + connectionForm C b ⟨c t, hp⟩ 1 0 V) •
        ((-Real.sin (θ t)) • b.section_ 0 ⟨c t, hp⟩ +
          Real.cos (θ t) • b.section_ 1 ⟨c t, hp⟩) := by
  let v' : Euclidean 2 := ![-Real.sin (θ t) * θ', Real.cos (θ t) * θ']
  have hv : HasDerivAt (coefficientsAlong b c f) v' t := by
    have hh : HasDerivAt (fun s => ![Real.cos (θ s), Real.sin (θ s)]) v' t := by
      apply hasDerivAt_pi.mpr
      intro i
      fin_cases i
      · exact hθ.cos
      · exact hθ.sin
    exact hh.congr_of_eventuallyEq hcoeff
  have hD : HasCovariantDerivativeAt C c f t
      (frameDerivative C b c f t hp V v') :=
    ⟨V, hV, U, hU, b, hp, v', hv.hasDerivWithinAt, rfl⟩
  dsimp only [covariantDerivative]
  rw [P202.Geometry.CurveCovariantDerivative.covariantDerivativeWithin_eq C
    (mem_univ t) (uniqueDiffWithinAt_univ) hD]
  apply (b.basis ⟨c t, hp⟩).equivFun.injective
  simp only [frameDerivative, LinearEquiv.apply_symm_apply, map_smul, map_add]
  have hfval := hcoeff.eq_of_nhds
  rw [hfval]
  ext i
  fin_cases i <;>
    simp [v', Matrix.mulVec, dotProduct, Fin.sum_univ_two, connectionMatrix,
      ← b.basis_eq, hdiag, hskew] <;> ring

/-- The positive-frame rotation acts on the actual field, as read from its
literal frame coefficients. -/
theorem frame_trig_rotation (g : RiemannianMetric S)
    (o : SmoothManifolds.OrientationData.Orientation S)
    {U : Set M} {hU : IsOpen U} (b : LocalFrame (tangentBundle S) U hU)
    {c : ℝ → M} {f : (s : ℝ) → TangentSpace S (c s)} {t : ℝ}
    (hp : c t ∈ U) {θ : ℝ → ℝ}
    (hcoeff : coefficientsAlong b c f =ᶠ[𝓝 t]
      (fun s => ![Real.cos (θ s), Real.sin (θ s)]))
    (hrot0 : rotation g o (c t) (b.section_ 0 ⟨c t, hp⟩) = b.section_ 1 ⟨c t, hp⟩) :
    rotation g o (c t) (f t) =
      (-Real.sin (θ t)) • b.section_ 0 ⟨c t, hp⟩ +
        Real.cos (θ t) • b.section_ 1 ⟨c t, hp⟩ := by
  have hrot1 : rotation g o (c t) (b.section_ 1 ⟨c t, hp⟩) =
      -b.section_ 0 ⟨c t, hp⟩ := by
    letI := (metricCore g (c t)).toNormedAddCommGroup
    letI := InnerProductSpace.ofCore (metricCore g (c t)).toCore
    letI := (SmoothManifolds.tangent_dimension S (c t)).1
    letI : Fact (Module.finrank ℝ (TangentSpace S (c t)) = 2) :=
      ⟨(SmoothManifolds.tangent_dimension S (c t)).2⟩
    have hJ := (planeOrientation g o (c t)).rightAngleRotation_rightAngleRotation
      (b.section_ 0 ⟨c t, hp⟩)
    change rotation g o (c t) (rotation g o (c t) (b.section_ 0 ⟨c t, hp⟩)) =
      -b.section_ 0 ⟨c t, hp⟩ at hJ
    rwa [hrot0] at hJ
  have hval := hcoeff.eq_of_nhds
  rw [P202.Geometry.CurveCovariantDerivative.coefficientsAlong_of_mem b c f t hp] at hval
  have he := (b.basis ⟨c t, hp⟩).equivFun_symm_apply
    ((b.basis ⟨c t, hp⟩).equivFun (f t))
  rw [LinearEquiv.symm_apply_apply, hval, Fin.sum_univ_two] at he
  have hf : f t = Real.cos (θ t) • b.section_ 0 ⟨c t, hp⟩ +
      Real.sin (θ t) • b.section_ 1 ⟨c t, hp⟩ := by
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, b.basis_eq] using he
  rw [hf, map_add, map_smul, map_smul, hrot0, hrot1]
  apply Subtype.ext
  apply LinearMap.ext
  intro z
  change Real.cos (θ t) * (b.section_ 1 ⟨c t, hp⟩).val z +
    Real.sin (θ t) * (-(b.section_ 0 ⟨c t, hp⟩).val z) =
    (-Real.sin (θ t)) * (b.section_ 0 ⟨c t, hp⟩).val z +
    Real.cos (θ t) * (b.section_ 1 ⟨c t, hp⟩).val z
  ring

/-- In a positive orthonormal frame the intrinsic geodesic-curvature pairing
is the derivative of the real angle plus the actual connection form. -/
theorem frame_trig_geodesic_pairing (g : RiemannianMetric S)
    (C : Connection (tangentBundle S))
    (o : SmoothManifolds.OrientationData.Orientation S)
    {U : Set M} {hU : IsOpen U} (b : LocalFrame (tangentBundle S) U hU)
    (hon : ∀ p i j, pairing g p.val (b.section_ i p) (b.section_ j p) =
      if i = j then 1 else 0)
    {c : ℝ → M} {f : (s : ℝ) → TangentSpace S (c s)} {t : ℝ}
    (hp : c t ∈ U) {V : TangentSpace S (c t)}
    (hV : HasVelocityWithinAt S c univ t V)
    (hdiag : ∀ i : Fin 2, connectionForm C b ⟨c t, hp⟩ i i V = 0)
    (hskew : connectionForm C b ⟨c t, hp⟩ 0 1 V =
      -connectionForm C b ⟨c t, hp⟩ 1 0 V)
    {θ : ℝ → ℝ} {θ' : ℝ} (hθ : HasDerivAt θ θ' t)
    (hcoeff : coefficientsAlong b c f =ᶠ[𝓝 t]
      (fun s => ![Real.cos (θ s), Real.sin (θ s)]))
    (hrot0 : rotation g o (c t) (b.section_ 0 ⟨c t, hp⟩) =
      b.section_ 1 ⟨c t, hp⟩) :
    pairing g (c t) (covariantDerivative C c f t) (rotation g o (c t) (f t)) =
      θ' + connectionForm C b ⟨c t, hp⟩ 1 0 V := by
  rw [frame_trig_covariantDerivative C b hp hV hdiag hskew hθ hcoeff,
    frame_trig_rotation g o b hp hcoeff hrot0]
  have hn : pairing g (c t)
      ((-Real.sin (θ t)) • b.section_ 0 ⟨c t, hp⟩ +
        Real.cos (θ t) • b.section_ 1 ⟨c t, hp⟩)
      ((-Real.sin (θ t)) • b.section_ 0 ⟨c t, hp⟩ +
        Real.cos (θ t) • b.section_ 1 ⟨c t, hp⟩) = 1 := by
    simp only [pairing, LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right]
    change (-Real.sin (θ t)) * ((-Real.sin (θ t)) * pairing g (c t) _ _ +
      Real.cos (θ t) * pairing g (c t) _ _) +
      Real.cos (θ t) * ((-Real.sin (θ t)) * pairing g (c t) _ _ +
      Real.cos (θ t) * pairing g (c t) _ _) = 1
    rw [hon ⟨c t, hp⟩ 0 0, hon ⟨c t, hp⟩ 0 1,
      hon ⟨c t, hp⟩ 1 0, hon ⟨c t, hp⟩ 1 1]
    norm_num
    nlinarith [Real.sin_sq_add_cos_sq (θ t)]
  simp only [pairing, LinearMap.BilinForm.smul_left] at hn ⊢
  rw [hn, mul_one]


/-- The actual metric-compatible connection and positive frame discharge
all connection-matrix and rotation premises in the moving-frame formula. -/
theorem orthonormalFrame_trig_geodesic_pairing (g : RiemannianMetric S)
    (C : Connection (tangentBundle S))
    (hC : P202.LeviCivitaData.IsMetricCompatible g C)
    (o : SmoothManifolds.OrientationData.Orientation S)
    {U : Set M} {hU : IsOpen U} (b : LocalFrame (tangentBundle S) U hU)
    (hon : ∀ p i j, pairing g p.val (b.section_ i p) (b.section_ j p) =
      if i = j then 1 else 0)
    {c : ℝ → M} {f : (s : ℝ) → TangentSpace S (c s)} {t : ℝ}
    (hp : c t ∈ U) {V : TangentSpace S (c t)}
    (hV : HasVelocityWithinAt S c univ t V)
    {θ : ℝ → ℝ} {θ' : ℝ} (hθ : HasDerivAt θ θ' t)
    (hcoeff : coefficientsAlong b c f =ᶠ[𝓝 t]
      (fun s => ![Real.cos (θ s), Real.sin (θ s)]))
    (hpos : PositiveBoundaryOrientation o (c t)
      (b.section_ 0 ⟨c t, hp⟩) (b.section_ 1 ⟨c t, hp⟩)) :
    pairing g (c t) (covariantDerivative C c f t) (rotation g o (c t) (f t)) =
      θ' + connectionForm C b ⟨c t, hp⟩ 1 0 V := by
  exact frame_trig_geodesic_pairing g C o b hon hp hV
    (orthonormalFrame_connectionForm_diagonal g C hC b hon ⟨c t, hp⟩ V)
    (orthonormalFrame_connectionForm_skew g C hC b hon ⟨c t, hp⟩ V 0 1)
    hθ hcoeff (orthonormalFrame_rotation_first g o b hon ⟨c t, hp⟩ hpos)

end IntrinsicBoundaryCalculus

section SignedBoundaryTurning
open MeasureTheory P202Specs.PlaneTurning

/-- Real tangent-angle choices reverse sign when the orientation of the
ambient plane is reversed. This does not reverse the curve parameter. -/
def negateAngleChoices {q : RegularJordanCurve} {o : Orientation ℝ Plane (Fin 2)}
    {A : ArcPresentation q} (θ : AngleChoices o A) : AngleChoices (-o) A where
  angle i := -(θ.angle i)
  lifts i t := by
    change (-(θ.angle i t) : Real.Angle) = (-o).oangle reference (velocity A i t)
    rw [θ.lifts, o.oangle_neg_orientation_eq_neg]
    rfl

lemma cornerAngle_negOrientation {q : RegularJordanCurve}
    (o : Orientation ℝ Plane (Fin 2)) (A : ArcPresentation q) (i : Fin A.count) :
    cornerAngle (-o) A i = -cornerAngle o A i := by
  unfold cornerAngle
  rw [o.oangle_neg_orientation_eq_neg]
  exact Real.Angle.toReal_neg_eq_neg_toReal_iff.mpr
    (P202.PlaneTurning.corner_not_pi o A i)

lemma totalTurning_negOrientation {q : RegularJordanCurve}
    {o : Orientation ℝ Plane (Fin 2)} {A : ArcPresentation q} (θ : AngleChoices o A) :
    totalTurning (negateAngleChoices θ) = -totalTurning θ := by
  simp only [totalTurning, negateAngleChoices, ContinuousMap.neg_apply,
    cornerAngle_negOrientation, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The plane has an orientation whose positive right-angle rotation is the
literal coordinate quarter turn used to define induced boundary signs. -/
theorem exists_coordinateOrientation :
    ∃ o : Orientation ℝ Plane (Fin 2), ∀ v : Plane,
      o.rightAngleRotation v = quarterTurn v := by
  let o := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation
  obtain ⟨sign, hsign, hrot⟩ :=
    P202.FineInscribedCollarGraphs.rotation_eq_signed_quarterTurn o
  rcases hsign with hsign | hsign
  · exact ⟨o, fun v => by simpa only [hsign, one_smul] using hrot v⟩
  · refine ⟨-o, fun v => ?_⟩
    rw [o.rightAngleRotation_neg_orientation, hrot v, hsign, neg_one_smul, neg_neg]

/-- Turning for either directed traversal, using the actual bounded side
and the chosen curve parametrization. No turning sum is an input. -/
theorem totalTurning_of_sideSign (q : RegularJordanCurve)
    (o : Orientation ℝ Plane (Fin 2)) (ho : ∀ v, o.rightAngleRotation v = quarterTurn v)
    (U : Set Plane) (hU : IsBoundedSide q U) (r : ℝ) (hr : r = 1 ∨ r = -1)
    (hleft : HasSideOnLeft U q r) (A : ArcPresentation q) (θ : AngleChoices o A) :
    totalTurning θ = 2 * Real.pi * r := by
  rcases hr with hr | hr
  · subst r
    have hl : HasBoundedSideOnLeft q o U := by
      intro t ht
      obtain ⟨ε, hε, he⟩ := hleft t ht
      exact ⟨ε, hε, fun r hr hεr => by simpa only [ho, one_smul] using he r hr hεr⟩
    simpa only [mul_one] using (P202.PlaneTurning.turning q o U hU hl A θ).1
  · subst r
    have hl : HasBoundedSideOnLeft q (-o) U := by
      intro t ht
      obtain ⟨ε, hε, he⟩ := hleft t ht
      exact ⟨ε, hε, fun r hr hεr => by
        simpa only [o.rightAngleRotation_neg_orientation, ho, neg_one_smul] using he r hr hεr⟩
    have h := (P202.PlaneTurning.turning q (-o) U hU hl A (negateAngleChoices θ)).1
    rw [totalTurning_negOrientation] at h
    linarith

/-- The planar-region orientation theorem identifies the sign in the plane
turning theorem for every component of every induced traversal. -/
theorem region_plane_turning (R : PlanarRegion)
    (o : Orientation ℝ Plane (Fin 2)) (ho : ∀ v, o.rightAngleRotation v = quarterTurn v)
    (A : ∀ i, ArcPresentation (R.curve i))
    (s : Fin R.boundaryCount → ℝ) (hs : IsInducedBoundaryOrientation R s) :
    ∃ outer : Fin R.boundaryCount,
      ∀ i (θ : AngleChoices o (A i)),
        totalTurning θ = 2 * Real.pi * (if i = outer then s i else -s i) := by
  obtain ⟨e, he, B, hB⟩ := P202.PlanarRegionEuler.planarRegionEuler R
  refine ⟨B.sides.outer, fun i θ => ?_⟩
  have hbounded : IsBoundedSide (R.curve i) (B.sides.boundedSide i) :=
    ⟨B.sides.bounded_open i, B.sides.bounded_connected i, B.sides.bounded i,
      B.sides.bounded_frontier i⟩
  have hsign : (if i = B.sides.outer then s i else -s i) = 1 ∨
      (if i = B.sides.outer then s i else -s i) = -1 := by
    by_cases hi : i = B.sides.outer
    · simpa only [if_pos hi] using (hs i).1
    · rcases (hs i).1 with h | h <;> simp [hi, h]
  apply totalTurning_of_sideSign (R.curve i) o ho (B.sides.boundedSide i) hbounded
    _ hsign _ (A i) θ
  by_cases hi : i = B.sides.outer
  · simpa only [if_pos hi] using (hB.2 s hs i).1.mpr hi
  · simpa only [if_neg hi] using (hB.2 s hs i).2.mpr hi

/-- Final local formula from the two actual geometric calculations. The
coordinate turning values, induced signs, Stokes identity, Euler invariant,
corner bounds, and disk specialization are supplied by proved results here.
Only constructing the frame/form and its intrinsic boundary calculus remain
separate obligations. This is not the unconditional target declaration. -/
theorem chartFormula_of_componentCalculus
    {M : Type*} [TopologicalSpace M]
    {S : SmoothManifold 2 .euclidean M}
    (g : P202.MetricData.RiemannianMetric S)
    (C : P202.ConnectionData.Connection (tangentBundle S))
    (T : P202.CurvatureData.CurvatureTensor S)
    (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M)
    (hc : c ∈ S.smoothStructure.val)
    (R : PlanarRegion) (hR : R.carrier ⊆ P202Specs.ChartRegionStokes.chartTarget c)
    (A : ∀ i, ArcPresentation (R.curve i))
    (s : Fin R.boundaryCount → ℝ) (hs : IsInducedBoundaryOrientation R s)
    (op : Orientation ℝ Plane (Fin 2))
    (hop : ∀ v, op.rightAngleRotation v = quarterTurn v)
    (U : Set Plane) (hU : IsOpen U) (hRU : R.carrier ⊆ U)
    (omega : P202Specs.ChartRegionStokes.OneForm) (hsm : ContDiffOn ℝ ∞ omega U)
    (hK : ∀ x ∈ R.carrier, P202Specs.ChartRegionStokes.exteriorCoefficient omega x =
      -P202Specs.LocalGaussBonnet.curvatureIntegrand g T c hc x)
    (hgeo : ∀ i j, IntervalIntegrable
      (P202Specs.LocalGaussBonnet.geodesicIntegrand g C o c hc (A i) j) volume 0 1)
    (hcomp : ∀ i (θ : AngleChoices op (A i)),
      (∑ j, ∫ t in (0 : ℝ)..1,
        P202Specs.LocalGaussBonnet.geodesicIntegrand g C o c hc (A i) j t) +
        (∑ j, P202Specs.LocalGaussBonnet.metricCornerAngle g o c hc (A i) j) =
      totalTurning θ + P202Specs.ChartRegionStokes.componentIntegral omega (R.curve i)) :
    IntegrableOn (P202Specs.LocalGaussBonnet.curvatureIntegrand g T c hc) R.carrier ∧
      (∀ i j, IntervalIntegrable
        (P202Specs.LocalGaussBonnet.geodesicIntegrand g C o c hc (A i) j) volume 0 1) ∧
      (∀ i j, 0 < P202Specs.LocalGaussBonnet.interiorAngle g o c hc (A i) (s i) j ∧
        P202Specs.LocalGaussBonnet.interiorAngle g o c hc (A i) (s i) j < 2 * Real.pi) ∧
      (∃ e : P202Specs.EulerPoincare.HomologyFiniteType ℚ R.carrier,
        P202Specs.LocalGaussBonnet.curvatureIntegral g T c hc R +
          P202Specs.LocalGaussBonnet.geodesicIntegral g C o c hc R A s +
          P202Specs.LocalGaussBonnet.exteriorAngleSum g o c hc R A s =
            2 * Real.pi * (P202Specs.EulerPoincare.topologicalEuler R.carrier e : ℝ)) ∧
      (R.boundaryCount = 1 →
        P202Specs.LocalGaussBonnet.curvatureIntegral g T c hc R +
          P202Specs.LocalGaussBonnet.geodesicIntegral g C o c hc R A s +
          P202Specs.LocalGaussBonnet.exteriorAngleSum g o c hc R A s = 2 * Real.pi) := by
  obtain ⟨outer, ht⟩ := region_plane_turning R op hop A s hs
  have hturn := region_boundary_assembly g C o c hc R outer A s (fun i => (hs i).1)
    omega (fun i => by
      obtain ⟨θ⟩ := P202.PlaneTurning.choicesExist (R.curve i) op (A i)
      rw [hcomp i θ, ht i θ])
  obtain ⟨hcurv, heuler, hdisk⟩ :=
    connectionForm_assembly g C T o c hc R A s hs U hU hRU omega hsm hK hturn
  exact ⟨hcurv, hgeo, interiorAngle_bounds g o c hc R hR A s hs, heuler, hdisk⟩


end SignedBoundaryTurning


section FinalAssembly
open SmoothManifolds.BundleData

theorem frameCoefficients_of_isChartFrame
    (g : RiemannianMetric S) (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (b : LocalFrame (tangentBundle S) c.source c.open_source)
    (hb : P202Specs.SurfaceConnectionForm.IsChartFrame g o c hc b) :
    P202Specs.MetricBoundaryTurning.FrameCoefficients g o c hc b
      (P202Specs.SurfaceConnectionForm.triangularA g c hc)
      (P202Specs.SurfaceConnectionForm.triangularBeta g c hc)
      (P202Specs.SurfaceConnectionForm.triangularD g c hc) := by
  rcases hb with ⟨_, _, hon, hpos, ha, hbeta, hd, hcoeff⟩
  refine ⟨hon, ?_, ha, hbeta, hd, ?_, ?_, ?_⟩
  · intro p
    unfold PositiveBoundaryOrientation
    have he : ![b.section_ 0 p, b.section_ 1 p] = b.basis p := by
      funext i
      fin_cases i <;> exact (b.basis_eq p _).symm
    rw [he]
    exact hpos p
  · intro x hx
    exact (hcoeff x hx).1
  · intro x hx
    exact (hcoeff x hx).2.1
  · intro x hx v
    exact (hcoeff x hx).2.2.2 v

theorem omega_eq_frameOneForm
    (C : Connection (tangentBundle S)) (c : ModelChart 2 .euclidean M)
    (hc : c ∈ S.smoothStructure.val)
    (b : LocalFrame (tangentBundle S) c.source c.open_source) :
    P202Specs.SurfaceConnectionForm.omega C c hc b =
      P202Specs.MetricBoundaryTurning.frameOneForm C c hc b := rfl

/-- Every original component lies in the chart containing the region. -/
theorem boundaryTrace_subset_chartTarget (R : PlanarRegion)
    (c : ModelChart 2 .euclidean M)
    (hR : R.carrier ⊆ P202Specs.ChartRegionStokes.chartTarget c)
    (i : Fin R.boundaryCount) :
    (R.curve i).trace ⊆ P202Specs.ChartRegionStokes.chartTarget c := by
  intro x hx
  apply hR
  apply frontier_subset_closure
  rw [R.boundary_eq]
  exact mem_iUnion.mpr ⟨i, hx⟩

/-- Local Gauss–Bonnet for every original chart region and every smooth arc
presentation, with intrinsic curvature, the actual occupied corner sectors,
induced boundary signs, and the rational homological Euler invariant. -/
theorem localGaussBonnet : P202Specs.LocalGaussBonnet.Expected.localGaussBonnet.{u} := by
  intro M inst S g C hC T hT o c hc hpositive R hR
  refine ⟨boundaryPresentations R, ?_⟩
  intro A s hs
  obtain ⟨b, hb, hform, hK⟩ :=
    P202.SurfaceConnectionForm.surfaceConnectionForm S g C hC T hT o c hc hpositive
  have H := frameCoefficients_of_isChartFrame g o c hc b hb
  obtain ⟨_, hcomponents, hsector⟩ :=
    P202.MetricBoundaryTurning.boundaryCalculus S g C hC o c hc hpositive b
      (P202Specs.SurfaceConnectionForm.triangularA g c hc)
      (P202Specs.SurfaceConnectionForm.triangularBeta g c hc)
      (P202Specs.SurfaceConnectionForm.triangularD g c hc) H
  obtain ⟨op, hop⟩ := exists_coordinateOrientation
  have hcomponent (i : Fin R.boundaryCount) :=
    hcomponents (R.curve i) (boundaryTrace_subset_chartTarget R c hR i) (A i)
  obtain ⟨hcurv, hgeo, hbounds, heuler, hdisk⟩ :=
    chartFormula_of_componentCalculus g C T o c hc R hR A s hs op hop
      (P202Specs.ChartRegionStokes.chartTarget c)
      (P202.SurfaceConnectionForm.chartTarget_isOpen c) hR
      (P202Specs.SurfaceConnectionForm.omega C c hc b) hform
      (fun x hx => by
        calc
          _ = -P202Specs.SurfaceConnectionForm.gaussianCurvature g T
                (P202Specs.SurfaceConnectionForm.chartPoint c x) *
              P202Specs.SurfaceConnectionForm.areaWeight g c hc x := hK x (hR hx)
          _ = -(P202Specs.SurfaceConnectionForm.gaussianCurvature g T
                (P202Specs.SurfaceConnectionForm.chartPoint c x) *
              P202Specs.SurfaceConnectionForm.areaWeight g c hc x) := neg_mul _ _
          _ = _ := rfl)
      (fun i j => (hcomponent i).2.2.1 j)
      (fun i theta => (hcomponent i).2.2.2.2.2 op hop theta)
  exact ⟨hcurv, hgeo, hbounds, (fun i j => hsector R hR s hs i (A i) j), heuler, hdisk⟩

end FinalAssembly

end P202.LocalGaussBonnet
