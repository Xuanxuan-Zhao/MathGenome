import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.JacobiMatrix
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.JacobiIVP
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Asymptotics.Ring
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Tactic.FunProp

import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.ExponentialJacobi
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000
namespace P202.Geometry.JacobiMatrix
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  P202.ConnectionData P202.MetricData P202.CurveConnectionData P202.LeviCivitaData
  P202.GeodesicData P202.CurvatureData P202.JacobiData P202.ExponentialJacobiData
  P202.JacobiMatrixData
open Set Filter
open scoped Topology
universe u
variable {n r : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

/-- Solve the matrix ODE itself, using left composition by the actual radial
curvature operator as the coefficient of an ODE on the operator space. -/
private theorem construct_system
    (C : Connection (tangentBundle S)) (R : CurvatureTensor S)
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q) (h0 : 0 ∈ I.carrier) :
    ∃ D : JacobiSystem S C R I q n,
      ∀ t ∈ I.carrier, Function.Bijective (D.frame t) := by
  let P := JacobiIVP.intervalParallelEquiv C I q hq 0 h0
  let K := JacobiIVP.radialCoordinateOperator R q P
  have hP (t : ℝ) (ht : t ∈ I.carrier) (i : Fin n) :
      HasCovariantDerivativeAt C (fun s => (q s).1)
        (fun s => P s (Pi.single i 1)) t 0 :=
    JacobiIVP.intervalParallelEquiv_parallel C I q hq 0 h0 (Pi.single i 1) t ht
  have hK : ContinuousOn K I.carrier :=
    JacobiIVP.radialCoordinateOperator_continuousOn C R I.carrier q hq P hP
  let L : ℝ → Operator n →L[ℝ] Operator n :=
    fun t => ContinuousLinearMap.mul ℝ (Operator n) (K t)
  have hL : ContinuousOn L I.carrier :=
    (ContinuousLinearMap.mul ℝ (Operator n)).continuous.comp_continuousOn hK
  obtain ⟨A, B, hA0, hB0, hd, _⟩ :=
    JacobiIVP.second_order_linear_ivp I L hL 0 h0 0 1
  let D : JacobiSystem S C R I q n := {
    frame := fun t => (P t).toLinearMap
    frame_injective := fun t _ => (P t).injective
    frame_parallel := fun x => JacobiIVP.intervalParallelEquiv_parallel C I q hq 0 h0 x
    curvature := K
    curvature_continuous := hK
    curvature_eq := fun t _ x => JacobiIVP.radialCoordinateOperator_apply R q P t x
    A := A
    B := B
    initial_A := hA0
    initial_B := hB0
    derivatives := by simpa only [L, ContinuousLinearMap.mul_apply'] using hd }
  exact ⟨D, fun t _ => (P t).bijective⟩

/-- Finite parallel expansions differentiate in the intrinsic fibers. This
also applies to a frame of the normal subbundle, which is not surjective. -/
theorem derivative_in_frame
    (C : Connection (tangentBundle S)) {c : ℝ → M}
    (P : (s : ℝ) → Euclidean r →ₗ[ℝ] TangentSpace S (c s))
    {t : ℝ} {V : TangentSpace S (c t)}
    (hc : HasVelocityWithinAt S c univ t V)
    (hP : ∀ i : Fin r, HasCovariantDerivativeAt C c
      (fun s => P s (Pi.single i 1)) t 0)
    {j : ℝ → Euclidean r} {w : Euclidean r} (hj : HasDerivAt j w t) :
    HasCovariantDerivativeAt C c (fun s => P s (j s)) t (P t w) := by
  have expand (s : ℝ) (x : Euclidean r) :
      P s x = ∑ i : Fin r, x i • P s (Pi.single i 1) := by
    simpa only [map_sum, map_smul, Pi.basisFun_apply,
      Pi.basisFun_equivFun, LinearEquiv.refl_apply] using
      congrArg (P s) ((Pi.basisFun ℝ (Fin r)).sum_equivFun x).symm
  have hd := ParallelTransport.derivative_field_finset_sum C (mem_univ t)
    uniqueDiffWithinAt_univ hc Finset.univ
    (fun i s => j s i • P s (Pi.single i 1))
    (fun i => w i • P t (Pi.single i 1)) (fun i _ => by
      simpa only [smul_zero, add_zero] using
        CurveCovariantDerivative.derivative_smul C (hP i)
          ((hasDerivAt_pi.mp hj i).hasDerivWithinAt))
  have heq : (fun s => ∑ i : Fin r, j s i • P s (Pi.single i 1)) =
      (fun s => P s (j s)) := funext (fun s => (expand s (j s)).symm)
  rw [heq, ← expand t w] at hd
  exact hd

/-- The two intrinsic derivative relations for a column combination of A. -/
theorem system_field_derivatives
    (C : Connection (tangentBundle S)) (R : CurvatureTensor S)
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q) (D : JacobiSystem S C R I q r)
    (x : Euclidean r) (t : ℝ) (ht : t ∈ I.carrier) :
    HasCovariantDerivativeAt C (fun s => (q s).1)
      (fun s => D.frame s (D.A s x)) t (D.frame t (D.B t x)) ∧
    HasCovariantDerivativeAt C (fun s => (q s).1)
      (fun s => D.frame s (D.B s x)) t
      (-(R.val (q t).1 (D.frame t (D.A t x)) (q t).2 (q t).2)) := by
  have hA : HasDerivAt (fun s => D.A s x) (D.B t x) t := by
    simpa only [map_zero, add_zero] using
      (D.derivatives t ht).1.clm_apply (hasDerivAt_const t x)
  have hB : HasDerivAt (fun s => D.B s x) (-(D.curvature t (D.A t x))) t := by
    simpa only [map_zero, add_zero, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.mul_apply] using
      (D.derivatives t ht).2.clm_apply (hasDerivAt_const t x)
  constructor
  · exact derivative_in_frame C D.frame (hq t ht).1
      (fun i => D.frame_parallel (Pi.single i 1) t ht) hA
  · have hd := derivative_in_frame C D.frame (hq t ht).1
      (fun i => D.frame_parallel (Pi.single i 1) t ht) hB
    simpa only [map_neg, D.curvature_eq t ht] using hd

private theorem field_representation_proof :
    P202Specs.Geometry.JacobiMatrix.field_representationType.{u} := by
  intro n r M _ S g C hC R hR I q hq h0 D x
  let J := fun t => D.frame t (D.A t x)
  have hJ : IsJacobiField C R I.carrier q J :=
    ⟨fun t => D.frame t (D.B t x), system_field_derivatives C R I q hq D x⟩
  have hJ0 : J 0 = 0 := by simp [J, D.initial_A]
  have hd0 : HasCovariantDerivativeAt C (fun s => (q s).1) J 0 (D.frame 0 x) := by
    simpa only [D.initial_B, ContinuousLinearMap.one_apply] using
      (system_field_derivatives C R I q hq D x 0 h0).1
  refine ⟨hJ, hJ0, hd0, ?_⟩
  obtain ⟨F, hF, hF0, hdF0, huniq⟩ := JacobiIVP.exists_unique S g C hC R hR I q hq
    0 h0 0 (D.frame 0 x)
  intro K hK hK0 hdK0 t ht
  exact (huniq K hK hK0 hdK0 t ht).trans (huniq J hJ hJ0 hd0 t ht).symm

-- Conditional draft helpers. The nine premise types and their order are
-- frozen by the owner contract, including those unused in a particular proof.

theorem construction_conditional
    (_conjugacy_singularity : P202Specs.Geometry.ExponentialJacobi.conjugacy_singularityType.{u})
    (_differential_coordinates : P202Specs.Geometry.ExponentialJacobi.differential_coordinatesType.{u})
    (_differential_formula : P202Specs.Geometry.ExponentialJacobi.differential_formulaType.{u})
    (_differential_zero : P202Specs.Geometry.ExponentialJacobi.differential_zeroType.{u})
    (_endpoint_space : P202Specs.Geometry.ExponentialJacobi.endpoint_spaceType.{u})
    (_kernel_equivalence : P202Specs.Geometry.ExponentialJacobi.kernel_equivalenceType.{u})
    (_multiplicity_finite : P202Specs.Geometry.ExponentialJacobi.multiplicity_finiteType.{u})
    (_radial_field : P202Specs.Geometry.ExponentialJacobi.radial_fieldType.{u})
    (_two_zeros_normal : P202Specs.Geometry.ExponentialJacobi.two_zeros_normalType.{u})
    : P202Specs.Geometry.JacobiMatrix.constructionType.{u} := by
  intro n M _ S g C hC R hR I q hq h0
  exact construct_system C R I q hq h0

theorem field_representation_conditional
    (_conjugacy_singularity : P202Specs.Geometry.ExponentialJacobi.conjugacy_singularityType.{u})
    (_differential_coordinates : P202Specs.Geometry.ExponentialJacobi.differential_coordinatesType.{u})
    (_differential_formula : P202Specs.Geometry.ExponentialJacobi.differential_formulaType.{u})
    (_differential_zero : P202Specs.Geometry.ExponentialJacobi.differential_zeroType.{u})
    (_endpoint_space : P202Specs.Geometry.ExponentialJacobi.endpoint_spaceType.{u})
    (_kernel_equivalence : P202Specs.Geometry.ExponentialJacobi.kernel_equivalenceType.{u})
    (_multiplicity_finite : P202Specs.Geometry.ExponentialJacobi.multiplicity_finiteType.{u})
    (_radial_field : P202Specs.Geometry.ExponentialJacobi.radial_fieldType.{u})
    (_two_zeros_normal : P202Specs.Geometry.ExponentialJacobi.two_zeros_normalType.{u})
    : P202Specs.Geometry.JacobiMatrix.field_representationType.{u} := field_representation_proof


private theorem invertible_proof : P202Specs.Geometry.JacobiMatrix.invertibleType.{u} := by
  intro n r M _ S g C hC R hR I q hq h0 D t hpos ht hnc
  have hker (x : Euclidean r) (hx : D.A t x = 0) : x = 0 := by
    let J := fun s => D.frame s (D.A s x)
    obtain ⟨hJ, hJ0, hdJ0, _⟩ := field_representation_proof S g C hC R hR I q hq h0 D x
    let j : RestrictedField S I q := fun s => J s.val
    have hjmem : j ∈ EndpointFields S C R I q ⟨0, h0⟩ ⟨t, ht⟩ := by
      refine ⟨⟨J, hJ, fun _ => rfl⟩, hJ0, ?_⟩
      change D.frame t (D.A t x) = 0
      rw [hx, map_zero]
    have hj0 : j = 0 := by
      by_contra h
      exact hnc ⟨j, hjmem, h⟩
    have hJzero (s : ℝ) (hs : s ∈ I.carrier) : J s = 0 :=
      congrFun hj0 ⟨s, hs⟩
    have hd : HasCovariantDerivativeAt C (fun s => (q s).1)
        (fun _ => 0) 0 (D.frame 0 x) := by
      apply ParallelTransport.derivative_field_congr C (mem_univ 0) _ hdJ0
      rw [nhdsWithin_univ]
      filter_upwards [I.isOpen.mem_nhds h0] with s hs
      exact hJzero s hs
    have hdz : HasCovariantDerivativeAt C (fun s => (q s).1) (fun _ => 0) 0 0 := by
      simpa only [zero_smul] using
        CurveCovariantDerivative.derivative_const_smul C (hq 0 h0).2 0
    have heq := CurveCovariantDerivative.covariantDerivative_unique C
      (mem_univ 0) uniqueDiffWithinAt_univ hd hdz
    exact D.frame_injective 0 h0 (by simpa only [map_zero] using heq)
  have hinj : Function.Injective (D.A t) := by
    intro x y hxy
    have h : D.A t (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    exact sub_eq_zero.mp (hker (x - y) h)
  exact ⟨hinj, (LinearMap.injective_iff_surjective (f := (D.A t).toLinearMap)).mp hinj⟩

/-- The radial curvature operator is symmetric on the full tangent fiber,
including its tangential zero direction. -/
theorem radial_curvature_symmetric
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    (p : M) (X Y T : TangentSpace S p) :
    pairing g p (R.val p X T T) Y = pairing g p X (R.val p Y T T) := by
  have h1 := CurvatureAlgebra.form_pair_exchange C g hC R hR p X T T Y
  have h2 := CurvatureAlgebra.form_skew_first C g R hR p T Y X T
  have h3 := CurvatureAlgebra.form_skew_last C g hC.2 R hR p Y T X T
  change pairing g p (R.val p X T T) Y = pairing g p (R.val p T Y X) T at h1
  change pairing g p (R.val p T Y X) T = -pairing g p (R.val p Y T X) T at h2
  change pairing g p (R.val p Y T X) T = -pairing g p (R.val p Y T T) X at h3
  have h4 : pairing g p (R.val p Y T T) X = pairing g p X (R.val p Y T T) :=
    g.symmetric p _ _
  linarith

private theorem wronskian_proof : P202Specs.Geometry.JacobiMatrix.wronskianType.{u} := by
  intro n r M _ S g C hC R hR I q hq h0 D t ht x y
  let J := fun s => D.frame s (D.A s x)
  let K := fun s => D.frame s (D.A s y)
  let V := fun s => D.frame s (D.B s x)
  let W := fun s => D.frame s (D.B s y)
  let f := fun s => pairing g (q s).1 (J s) (W s) - pairing g (q s).1 (V s) (K s)
  have hd (s : ℝ) (hs : s ∈ I.carrier) : HasDerivAt f 0 s := by
    obtain ⟨hJ, hV⟩ := system_field_derivatives C R I q hq D x s hs
    obtain ⟨hK, hW⟩ := system_field_derivatives C R I q hq D y s hs
    have h1 := ParallelTransport.metric_pairing_deriv C g hC.2
      (mem_univ s) uniqueDiffWithinAt_univ hJ hW
    have h2 := ParallelTransport.metric_pairing_deriv C g hC.2
      (mem_univ s) uniqueDiffWithinAt_univ hV hK
    have hsym := radial_curvature_symmetric g C hC R hR (q s).1 (J s) (K s) (q s).2
    have hz : (pairing g (q s).1 (V s) (W s) +
          pairing g (q s).1 (J s) (-(R.val (q s).1 (K s) (q s).2 (q s).2))) -
        (pairing g (q s).1 (-(R.val (q s).1 (J s) (q s).2 (q s).2)) (K s) +
          pairing g (q s).1 (V s) (W s)) = 0 := by
      rw [LinearMap.BilinForm.neg_left (R₁ := ℝ) (M₁ := TangentSpace S (q s).1)
          (B₁ := pairing g (q s).1),
        LinearMap.BilinForm.neg_right (R₁ := ℝ) (M₁ := TangentSpace S (q s).1)
          (B₁ := pairing g (q s).1), hsym]
      ring
    have h := (hasDerivWithinAt_univ.mp h1).sub (hasDerivWithinAt_univ.mp h2)
    change HasDerivAt f _ s at h
    exact hz ▸ h
  obtain ⟨a, ha⟩ := I.isOpen.exists_is_const_of_deriv_eq_zero I.ordConnected.isPreconnected
    (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => (hd s hs).deriv)
  have hf0 : f 0 = 0 := by simp [f, J, K, D.initial_A, pairing]
  have hft : f t = 0 := (ha t ht).trans ((ha 0 h0).symm.trans hf0)
  exact sub_eq_zero.mp hft

theorem invertible_conditional
    (_conjugacy_singularity : P202Specs.Geometry.ExponentialJacobi.conjugacy_singularityType.{u})
    (_differential_coordinates : P202Specs.Geometry.ExponentialJacobi.differential_coordinatesType.{u})
    (_differential_formula : P202Specs.Geometry.ExponentialJacobi.differential_formulaType.{u})
    (_differential_zero : P202Specs.Geometry.ExponentialJacobi.differential_zeroType.{u})
    (_endpoint_space : P202Specs.Geometry.ExponentialJacobi.endpoint_spaceType.{u})
    (_kernel_equivalence : P202Specs.Geometry.ExponentialJacobi.kernel_equivalenceType.{u})
    (_multiplicity_finite : P202Specs.Geometry.ExponentialJacobi.multiplicity_finiteType.{u})
    (_radial_field : P202Specs.Geometry.ExponentialJacobi.radial_fieldType.{u})
    (_two_zeros_normal : P202Specs.Geometry.ExponentialJacobi.two_zeros_normalType.{u})
    : P202Specs.Geometry.JacobiMatrix.invertibleType.{u} := invertible_proof

theorem wronskian_conditional
    (_conjugacy_singularity : P202Specs.Geometry.ExponentialJacobi.conjugacy_singularityType.{u})
    (_differential_coordinates : P202Specs.Geometry.ExponentialJacobi.differential_coordinatesType.{u})
    (_differential_formula : P202Specs.Geometry.ExponentialJacobi.differential_formulaType.{u})
    (_differential_zero : P202Specs.Geometry.ExponentialJacobi.differential_zeroType.{u})
    (_endpoint_space : P202Specs.Geometry.ExponentialJacobi.endpoint_spaceType.{u})
    (_kernel_equivalence : P202Specs.Geometry.ExponentialJacobi.kernel_equivalenceType.{u})
    (_multiplicity_finite : P202Specs.Geometry.ExponentialJacobi.multiplicity_finiteType.{u})
    (_radial_field : P202Specs.Geometry.ExponentialJacobi.radial_fieldType.{u})
    (_two_zeros_normal : P202Specs.Geometry.ExponentialJacobi.two_zeros_normalType.{u})
    : P202Specs.Geometry.JacobiMatrix.wronskianType.{u} := wronskian_proof


section Analytic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma bigO_primitive {f g : ℝ → E} (m : ℕ) (h0 : f 0 = 0)
    (hf : ∀ᶠ t in 𝓝 0, HasDerivAt f (g t) t)
    (hg : Asymptotics.IsBigO (𝓝 0) g (fun t : ℝ => t ^ m)) :
    Asymptotics.IsBigO (𝓝 0) f (fun t : ℝ => t ^ (m+1)) := by
  obtain ⟨C, hC, hgC⟩ := hg.exists_pos
  obtain ⟨δ, hδ, hh⟩ := Metric.eventually_nhds_iff.mp (hf.and hgC.bound)
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with t ht
  have htδ : ‖t‖ < δ := by simpa [Metric.mem_ball, dist_zero_right] using ht
  have hmem (s : ℝ) (hs : s ∈ Metric.closedBall (0 : ℝ) ‖t‖) :
      HasDerivAt f (g s) s ∧ ‖g s‖ ≤ C * ‖s ^ m‖ := by
    apply hh
    have hs' : ‖s‖ ≤ ‖t‖ := by simpa [Metric.mem_closedBall, dist_zero_right] using hs
    simpa [dist_zero_right] using hs'.trans_lt htδ
  have hb (s : ℝ) (hs : s ∈ Metric.closedBall (0 : ℝ) ‖t‖) :
      ‖g s‖ ≤ C * ‖t‖ ^ m := by
    have hs' : ‖s‖ ≤ ‖t‖ := by simpa [Metric.mem_closedBall, dist_zero_right] using hs
    exact (hmem s hs).2.trans (by
      rw [norm_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg s) hs' m) hC.le)
  have hn := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s hs => (hmem s hs).1.hasDerivWithinAt) hb (convex_closedBall (0 : ℝ) ‖t‖)
    (x := (0 : ℝ)) (y := t) (by simp) (by simp)
  simpa only [h0, sub_zero, pow_succ, norm_mul, norm_pow, mul_assoc] using hn

end Analytic
private theorem near_zero_proof : P202Specs.Geometry.JacobiMatrix.near_zeroType.{u} := by
  intro n r M _ S C R I q h0 D
  have hA : Asymptotics.IsBigO (𝓝 0) D.A (fun t : ℝ => t) := by
    simpa only [D.initial_A, sub_zero] using (D.derivatives 0 h0).1.isBigO_sub
  have hK : Asymptotics.IsBigO (𝓝 0) D.curvature (fun _ : ℝ => (1 : ℝ)) :=
    (D.curvature_continuous.continuousAt (I.isOpen.mem_nhds h0)).isBigO_one ℝ
  have hKA : Asymptotics.IsBigO (𝓝 0)
      (fun t => -(D.curvature t * D.A t)) (fun t : ℝ => t ^ 1) := by
    simpa only [one_mul, pow_one] using (hK.mul hA).neg_left
  have hB : Asymptotics.IsBigO (𝓝 0) (fun t => D.B t - (1 : Operator r))
      (fun t : ℝ => t ^ 2) := by
    apply bigO_primitive 1 (by rw [D.initial_B, sub_self]) _ hKA
    filter_upwards [I.isOpen.mem_nhds h0] with t ht
    convert (D.derivatives t ht).2.sub (hasDerivAt_const t (1 : Operator r)) using 1 <;> simp only [sub_zero]
  refine ⟨?_, hB⟩
  apply bigO_primitive 2 (by simp only [D.initial_A, zero_smul, sub_self]) _ hB
  filter_upwards [I.isOpen.mem_nhds h0] with t ht
  have hd : HasDerivAt (fun s : ℝ => s • (1 : Operator r)) (1 : Operator r) t := by
    simpa only [id_eq, one_smul] using (hasDerivAt_id t).smul_const (1 : Operator r)
  exact (D.derivatives t ht).1.sub hd

theorem near_zero_conditional
    (_conjugacy_singularity : P202Specs.Geometry.ExponentialJacobi.conjugacy_singularityType.{u})
    (_differential_coordinates : P202Specs.Geometry.ExponentialJacobi.differential_coordinatesType.{u})
    (_differential_formula : P202Specs.Geometry.ExponentialJacobi.differential_formulaType.{u})
    (_differential_zero : P202Specs.Geometry.ExponentialJacobi.differential_zeroType.{u})
    (_endpoint_space : P202Specs.Geometry.ExponentialJacobi.endpoint_spaceType.{u})
    (_kernel_equivalence : P202Specs.Geometry.ExponentialJacobi.kernel_equivalenceType.{u})
    (_multiplicity_finite : P202Specs.Geometry.ExponentialJacobi.multiplicity_finiteType.{u})
    (_radial_field : P202Specs.Geometry.ExponentialJacobi.radial_fieldType.{u})
    (_two_zeros_normal : P202Specs.Geometry.ExponentialJacobi.two_zeros_normalType.{u})
    : P202Specs.Geometry.JacobiMatrix.near_zeroType.{u} := near_zero_proof


private theorem normal_construction_proof :
    P202Specs.Geometry.JacobiMatrix.normal_constructionType.{u} := by
  intro n M _ S g C hC R hR I q hq h0 hunit
  let P := JacobiIVP.intervalParallelEquiv C I q hq 0 h0
  let K := JacobiIVP.radialCoordinateOperator R q P
  have hP (x : Euclidean n) (t : ℝ) (ht : t ∈ I.carrier) :=
    JacobiIVP.intervalParallelEquiv_parallel C I q hq 0 h0 x t ht
  have hK : ContinuousOn K I.carrier :=
    JacobiIVP.radialCoordinateOperator_continuousOn C R I.carrier q hq P
      (fun t ht i => hP (Pi.single i 1) t ht)
  let l : Euclidean n →ₗ[ℝ] ℝ :=
    ((pairing g (q 0).1).flip (q 0).2).comp (P 0).toLinearMap
  let v₀ := (P 0).symm (q 0).2
  have hlv : l v₀ = 1 := by
    change pairing g (q 0).1 (P 0 ((P 0).symm (q 0).2)) (q 0).2 = 1
    rw [LinearEquiv.apply_symm_apply]
    exact hunit 0 h0
  have hl (t : ℝ) (ht : t ∈ I.carrier) (x : Euclidean n) :
      pairing g (q t).1 (P t x) (q t).2 = l x := by
    have hd (s : ℝ) (hs : s ∈ I.carrier) :
        HasDerivAt (fun s => pairing g (q s).1 (P s x) (q s).2) 0 s := by
      have h := ParallelTransport.metric_pairing_deriv C g hC.2
        (mem_univ s) uniqueDiffWithinAt_univ (hP x s hs) (hq s hs).2
      simpa only [pairing, hasDerivWithinAt_univ, map_zero,
        LinearMap.zero_apply, add_zero] using h
    obtain ⟨a, ha⟩ := I.isOpen.exists_is_const_of_deriv_eq_zero I.ordConnected.isPreconnected
      (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
      (fun s hs => (hd s hs).deriv)
    exact (ha t ht).trans (ha 0 h0).symm
  let N := LinearMap.ker l
  have hdim : Module.finrank ℝ N = n - 1 := by
    have hsurj : Function.Surjective l := by
      intro a
      exact ⟨a • v₀, by rw [map_smul, hlv, smul_eq_mul, mul_one]⟩
    have h := l.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at h
    have hn : Module.finrank ℝ (Euclidean n) = n := by simp [Euclidean]
    rw [hn, CommSemiring.finrank_self] at h
    dsimp [N]
    omega
  let e : Euclidean (n-1) ≃ₗ[ℝ] N :=
    LinearEquiv.ofFinrankEq _ _ (by simpa [Euclidean] using hdim.symm)
  let E : Euclidean (n-1) →L[ℝ] Euclidean n :=
    (N.subtype.comp e.toLinearMap).toContinuousLinearMap
  let proj : Euclidean n →ₗ[ℝ] N := {
    toFun := fun x => ⟨x - l x • v₀, by
      change l (x - l x • v₀) = 0
      rw [map_sub, map_smul, hlv, smul_eq_mul, mul_one, sub_self]⟩
    map_add' := by
      intro x y
      apply Subtype.ext
      change x + y - l (x + y) • v₀ = (x - l x • v₀) + (y - l y • v₀)
      rw [map_add, add_smul]
      abel
    map_smul' := by
      intro a x
      apply Subtype.ext
      change a • x - l (a • x) • v₀ = a • (x - l x • v₀)
      simp only [map_smul, smul_sub, smul_smul, smul_eq_mul] }
  let Q : Euclidean n →L[ℝ] Euclidean (n-1) :=
    (e.symm.toLinearMap.comp proj).toContinuousLinearMap
  have hEQ (x : Euclidean n) (hx : l x = 0) : E (Q x) = x := by
    change (e (e.symm (proj x))).val = x
    rw [LinearEquiv.apply_symm_apply]
    change x - l x • v₀ = x
    rw [hx, zero_smul, sub_zero]
  have hE_inj : Function.Injective E :=
    fun x y h => e.injective (Subtype.ext h)
  have hEK (t : ℝ) (ht : t ∈ I.carrier) (x : Euclidean (n-1)) :
      E (Q (K t (E x))) = K t (E x) := by
    apply hEQ
    rw [← hl t ht, JacobiIVP.radialCoordinateOperator_apply]
    exact JacobiIVP.curvature_radial_orthogonal g C hC R hR (q t).1 (P t (E x)) (q t).2
  let K' : ℝ → Operator (n-1) := fun t => Q.comp ((K t).comp E)
  have hK' : ContinuousOn K' I.carrier :=
    continuousOn_const.clm_comp (hK.clm_comp continuousOn_const)
  let L : ℝ → Operator (n-1) →L[ℝ] Operator (n-1) :=
    fun t => ContinuousLinearMap.mul ℝ (Operator (n-1)) (K' t)
  have hL : ContinuousOn L I.carrier :=
    (ContinuousLinearMap.mul ℝ (Operator (n-1))).continuous.comp_continuousOn hK'
  obtain ⟨A, B, hA0, hB0, hd, _⟩ :=
    JacobiIVP.second_order_linear_ivp I L hL 0 h0 0 1
  let D : JacobiSystem S C R I q (n-1) := {
    frame := fun t => (P t).toLinearMap.comp E.toLinearMap
    frame_injective := fun t _ => (P t).injective.comp hE_inj
    frame_parallel := fun x => hP (E x)
    curvature := K'
    curvature_continuous := hK'
    curvature_eq := by
      intro t ht x
      change P t (E (Q (K t (E x)))) = _
      rw [hEK t ht, JacobiIVP.radialCoordinateOperator_apply]
      rfl
    A := A
    B := B
    initial_A := hA0
    initial_B := hB0
    derivatives := by simpa only [L, ContinuousLinearMap.mul_apply'] using hd }
  refine ⟨D, ?_⟩
  intro t ht v
  constructor
  · rintro ⟨x, rfl⟩
    change pairing g (q t).1 (P t (E x)) (q t).2 = 0
    rw [hl t ht]
    exact (e x).property
  · intro hv
    let z : N := ⟨(P t).symm v, by
      change l ((P t).symm v) = 0
      rw [← hl t ht, LinearEquiv.apply_symm_apply, hv]⟩
    refine ⟨e.symm z, ?_⟩
    change P t (E (e.symm z)) = v
    change P t ((e (e.symm z)).val) = v
    rw [LinearEquiv.apply_symm_apply]
    exact (P t).apply_symm_apply v

theorem riccati_derivative_of_bijective
    {C : Connection (tangentBundle S)} {R : CurvatureTensor S}
    {I : D13Unified.OpenTimeInterval} {q : ℝ → Phase S}
    (D : JacobiSystem S C R I q r) (t : ℝ) (ht : t ∈ I.carrier)
    (hbij : Function.Bijective (D.A t)) :
    HasDerivAt (riccati D) (-(riccati D t * riccati D t + D.curvature t)) t := by
  have hu : IsUnit (D.A t) := ContinuousLinearMap.isUnit_iff_bijective.mpr hbij
  have hi : HasDerivAt (fun s => Ring.inverse (D.A s))
      (-(Ring.inverse (D.A t) * D.B t * Ring.inverse (D.A t))) t := by
    have h := (hasFDerivAt_ringInverse (𝕜 := ℝ) hu.unit)
    rw [hu.unit_spec] at h
    convert h.comp_hasDerivAt t (D.derivatives t ht).1 using 1
    · rfl
    · simp only [neg_apply, ContinuousLinearMap.mulLeftRight_apply,
        ← Ring.inverse_unit hu.unit, hu.unit_spec]
  have hd := (D.derivatives t ht).2.mul hi
  have hh : -(D.curvature t * D.A t) * Ring.inverse (D.A t) +
      D.B t * -(Ring.inverse (D.A t) * D.B t * Ring.inverse (D.A t)) =
      -(riccati D t * riccati D t + D.curvature t) := by
    calc
      _ = -(D.curvature t * D.A t * Ring.inverse (D.A t)) +
          -(D.B t * (Ring.inverse (D.A t) * D.B t * Ring.inverse (D.A t))) := by
        rw [neg_mul (D.curvature t * D.A t) (Ring.inverse (D.A t)),
          mul_neg (D.B t) (Ring.inverse (D.A t) * D.B t * Ring.inverse (D.A t))]
      _ = -D.curvature t + -(riccati D t * riccati D t) := by
        rw [mul_assoc (D.curvature t) (D.A t), Ring.mul_inverse_cancel (D.A t) hu, mul_one]
        congr 2
      _ = _ := by rw [neg_add]; abel
  exact hh ▸ hd

theorem riccati_self_adjoint_of_bijective
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q) (h0 : 0 ∈ I.carrier)
    (D : JacobiSystem S C R I q r) (t : ℝ) (ht : t ∈ I.carrier)
    (hbij : Function.Bijective (D.A t)) (x y : Euclidean r) :
    pairing g (q t).1 (D.frame t (riccati D t x)) (D.frame t y) =
      pairing g (q t).1 (D.frame t x) (D.frame t (riccati D t y)) := by
  obtain ⟨a, ha⟩ := hbij.2 x
  obtain ⟨b, hb⟩ := hbij.2 y
  have hu : IsUnit (D.A t) := ContinuousLinearMap.isUnit_iff_bijective.mpr hbij
  have hUA (z : Euclidean r) : riccati D t (D.A t z) = D.B t z := by
    change ((D.B t * Ring.inverse (D.A t)) * D.A t) z = _
    rw [Ring.inverse_mul_cancel_right (D.A t) (D.B t) hu]
  rw [← ha, ← hb, hUA, hUA]
  exact (wronskian_proof S g C hC R hR I q hq h0 D t ht a b).symm

theorem normal_construction_conditional
    (_conjugacy_singularity : P202Specs.Geometry.ExponentialJacobi.conjugacy_singularityType.{u})
    (_differential_coordinates : P202Specs.Geometry.ExponentialJacobi.differential_coordinatesType.{u})
    (_differential_formula : P202Specs.Geometry.ExponentialJacobi.differential_formulaType.{u})
    (_differential_zero : P202Specs.Geometry.ExponentialJacobi.differential_zeroType.{u})
    (_endpoint_space : P202Specs.Geometry.ExponentialJacobi.endpoint_spaceType.{u})
    (_kernel_equivalence : P202Specs.Geometry.ExponentialJacobi.kernel_equivalenceType.{u})
    (_multiplicity_finite : P202Specs.Geometry.ExponentialJacobi.multiplicity_finiteType.{u})
    (_radial_field : P202Specs.Geometry.ExponentialJacobi.radial_fieldType.{u})
    (_two_zeros_normal : P202Specs.Geometry.ExponentialJacobi.two_zeros_normalType.{u})
    : P202Specs.Geometry.JacobiMatrix.normal_constructionType.{u} := normal_construction_proof


section Determinant
open scoped Matrix.Norms.Elementwise
private theorem hasDerivAt_det_one_add_smul (U : Matrix (Fin r) (Fin r) ℝ) :
    HasDerivAt (fun s : ℝ => Matrix.det (1 + s • U)) (Matrix.trace U) 0 := by
  let p : Polynomial ℝ := Matrix.det ((1 : Matrix (Fin r) (Fin r) (Polynomial ℝ)) + (Polynomial.X : Polynomial ℝ) • U.map (Polynomial.C : ℝ →+* Polynomial ℝ))
  have heval (s : ℝ) : p.eval s = Matrix.det (1 + s • U) := by
    change (Polynomial.evalRingHom s) (Matrix.det _) = _
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp [RingHom.mapMatrix_apply, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply]
    split_ifs <;> simp only [Polynomial.eval_one, Polynomial.eval_zero] <;> ring
  have hd := p.hasDerivAt 0
  rw [Matrix.derivative_det_one_add_X_smul] at hd
  simpa only [heval] using hd

private theorem differentiable_det :
    Differentiable ℝ (Matrix.det : Matrix (Fin r) (Fin r) ℝ → ℝ) := by
  classical
  have heq : (Matrix.det : Matrix (Fin r) (Fin r) ℝ → ℝ) =
      (fun M => ∑ σ : Equiv.Perm (Fin r), (Equiv.Perm.sign σ : ℝ) * ∏ i, M (σ i) i) :=
    funext Matrix.det_apply'
  rw [heq]
  fun_prop

private theorem hasDerivAt_matrix_det {A : ℝ → Matrix (Fin r) (Fin r) ℝ}
    {B : Matrix (Fin r) (Fin r) ℝ} {t : ℝ} (hA : HasDerivAt A B t)
    (U : Matrix (Fin r) (Fin r) ℝ) (hUB : U * A t = B) :
    HasDerivAt (fun s => Matrix.det (A s)) (Matrix.trace U * Matrix.det (A t)) t := by
  let H := fderiv ℝ (Matrix.det : Matrix (Fin r) (Fin r) ℝ → ℝ) (A t)
  have hd : HasDerivAt (fun s => Matrix.det (A s)) (H B) t :=
    by simpa only [Function.comp_def] using
      (differentiable_det (A t)).hasFDerivAt.comp_hasDerivAt t hA
  have hcurve : HasDerivAt (fun s : ℝ => A t + s • B) B 0 := by
    convert (hasDerivAt_const (0 : ℝ) (A t)).add
      ((hasDerivAt_id (0 : ℝ)).smul_const B) using 1
    all_goals first | rfl | exact ((zero_add ((1 : ℝ) • B)).trans (one_smul ℝ B)).symm
  have h1 : HasDerivAt (fun s : ℝ => Matrix.det (A t + s • B)) (H B) 0 := by
    have h := (differentiable_det (A t + (0 : ℝ) • B)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hcurve
    simpa only [zero_smul, add_zero, Function.comp_def] using h
  have h2 := (hasDerivAt_det_one_add_smul U).mul_const (Matrix.det (A t))
  have heq (s : ℝ) : Matrix.det (A t + s • B) =
      Matrix.det (1 + s • U) * Matrix.det (A t) := by
    rw [← Matrix.det_mul, add_mul, one_mul, smul_mul_assoc, hUB]
  have h2' : HasDerivAt (fun s : ℝ => Matrix.det (A t + s • B))
      (Matrix.trace U * Matrix.det (A t)) 0 := by
    simpa only [← heq] using h2
  exact h1.unique h2' ▸ hd

theorem logarithmic_determinant_derivative
    {C : Connection (tangentBundle S)} {R : CurvatureTensor S}
    {I : D13Unified.OpenTimeInterval} {q : ℝ → Phase S}
    (D : JacobiSystem S C R I q r) (t : ℝ) (ht : t ∈ I.carrier)
    (hbij : Function.Bijective (D.A t)) (hpos : 0 < LinearMap.det (D.A t).toLinearMap) :
    HasDerivAt (fun s => Real.log (LinearMap.det (D.A s).toLinearMap))
      (LinearMap.trace ℝ (Euclidean r) (riccati D t).toLinearMap) t := by
  let a : ℝ → Matrix (Fin r) (Fin r) ℝ := fun s => LinearMap.toMatrix' (D.A s).toLinearMap
  let b : Matrix (Fin r) (Fin r) ℝ := LinearMap.toMatrix' (D.B t).toLinearMap
  let v : Matrix (Fin r) (Fin r) ℝ := LinearMap.toMatrix' (riccati D t).toLinearMap
  have ha : HasDerivAt a b t := by
    apply hasDerivAt_pi.mpr
    intro i
    apply hasDerivAt_pi.mpr
    intro j
    change HasDerivAt (fun s => D.A s (Pi.single j 1) i) (D.B t (Pi.single j 1) i) t
    have hd : HasDerivAt (fun s => D.A s (Pi.single j 1)) (D.B t (Pi.single j 1)) t := by
      simpa only [map_zero, add_zero] using
        (D.derivatives t ht).1.clm_apply (hasDerivAt_const t (Pi.single j 1))
    exact hasDerivAt_pi.mp hd i
  have hu : IsUnit (D.A t) := ContinuousLinearMap.isUnit_iff_bijective.mpr hbij
  have hv : v * a t = b := by
    rw [← LinearMap.toMatrix'_mul]
    congr 1
    change ((D.B t * Ring.inverse (D.A t)) * D.A t).toLinearMap = (D.B t).toLinearMap
    rw [Ring.inverse_mul_cancel_right (D.A t) (D.B t) hu]
  have hd := hasDerivAt_matrix_det ha v hv
  have htrace : Matrix.trace v = LinearMap.trace ℝ (Euclidean r) (riccati D t).toLinearMap := by
    simpa only [LinearMap.toMatrix_eq_toMatrix'] using
      (LinearMap.trace_eq_matrix_trace ℝ (Pi.basisFun ℝ (Fin r)) (riccati D t).toLinearMap).symm
  have hdet (s : ℝ) : Matrix.det (a s) = LinearMap.det (D.A s).toLinearMap :=
    LinearMap.det_toMatrix' _
  have hd' : HasDerivAt (fun s => LinearMap.det (D.A s).toLinearMap)
      (LinearMap.trace ℝ (Euclidean r) (riccati D t).toLinearMap *
        LinearMap.det (D.A t).toLinearMap) t := by
    simpa only [htrace, hdet] using hd
  have hlog := hd'.log (ne_of_gt hpos)
  simpa only [mul_div_cancel_right₀ _ (ne_of_gt hpos)] using hlog

end Determinant

private theorem regular_interval_proof :
    P202Specs.Geometry.JacobiMatrix.regular_intervalType.{u} := by
  intro n r M _ S g C hC R hR I q hq h0 D L hsub hpos hnc t ht
  have hti : t ∈ I.carrier := hsub ht
  have hbij := invertible_proof S g C hC R hR I q hq h0 D t (hpos t ht) hti (hnc t ht hti)
  exact ⟨hbij,
    riccati_self_adjoint_of_bijective g C hC R hR I q hq h0 D t hti hbij,
    riccati_derivative_of_bijective D t hti hbij,
    logarithmic_determinant_derivative D t hti hbij⟩

theorem regular_interval_conditional
    (_conjugacy_singularity : P202Specs.Geometry.ExponentialJacobi.conjugacy_singularityType.{u})
    (_differential_coordinates : P202Specs.Geometry.ExponentialJacobi.differential_coordinatesType.{u})
    (_differential_formula : P202Specs.Geometry.ExponentialJacobi.differential_formulaType.{u})
    (_differential_zero : P202Specs.Geometry.ExponentialJacobi.differential_zeroType.{u})
    (_endpoint_space : P202Specs.Geometry.ExponentialJacobi.endpoint_spaceType.{u})
    (_kernel_equivalence : P202Specs.Geometry.ExponentialJacobi.kernel_equivalenceType.{u})
    (_multiplicity_finite : P202Specs.Geometry.ExponentialJacobi.multiplicity_finiteType.{u})
    (_radial_field : P202Specs.Geometry.ExponentialJacobi.radial_fieldType.{u})
    (_two_zeros_normal : P202Specs.Geometry.ExponentialJacobi.two_zeros_normalType.{u})
    : P202Specs.Geometry.JacobiMatrix.regular_intervalType.{u} := regular_interval_proof

end P202.Geometry.JacobiMatrix

universe v8_closure_7021153364b7efc4_u0
theorem _root_.«P202».«Geometry».«JacobiMatrix».«construction» : _root_.«P202Specs».«Geometry».«JacobiMatrix».«constructionType».{v8_closure_7021153364b7efc4_u0} :=
  @_root_.«P202».«Geometry».«JacobiMatrix».«construction_conditional».{v8_closure_7021153364b7efc4_u0} (@_root_.«P202».«Geometry».«ExponentialJacobi».«conjugacy_singularity».{v8_closure_7021153364b7efc4_u0}) (@_root_.«P202».«Geometry».«ExponentialJacobi».«differential_coordinates».{v8_closure_7021153364b7efc4_u0}) (@_root_.«P202».«Geometry».«ExponentialJacobi».«differential_formula».{v8_closure_7021153364b7efc4_u0}) (@_root_.«P202».«Geometry».«ExponentialJacobi».«differential_zero».{v8_closure_7021153364b7efc4_u0}) (@_root_.«P202».«Geometry».«ExponentialJacobi».«endpoint_space».{v8_closure_7021153364b7efc4_u0}) (@_root_.«P202».«Geometry».«ExponentialJacobi».«kernel_equivalence».{v8_closure_7021153364b7efc4_u0}) (@_root_.«P202».«Geometry».«ExponentialJacobi».«multiplicity_finite».{v8_closure_7021153364b7efc4_u0}) (@_root_.«P202».«Geometry».«ExponentialJacobi».«radial_field».{v8_closure_7021153364b7efc4_u0}) (@_root_.«P202».«Geometry».«ExponentialJacobi».«two_zeros_normal».{v8_closure_7021153364b7efc4_u0})
theorem _root_.«P202».«Geometry».«JacobiMatrix».«field_representation» : _root_.«P202Specs».«Geometry».«JacobiMatrix».«field_representationType».{v8_closure_7021153364b7efc4_u0} :=
  @_root_.«P202».«Geometry».«JacobiMatrix».«field_representation_conditional».{v8_closure_7021153364b7efc4_u0} (@_root_.«P202».«Geometry».«ExponentialJacobi».«conjugacy_singularity».{v8_closure_7021153364b7efc4_u0}) (@_root_.«P202».«Geometry».«ExponentialJacobi».«differential_coordinates».{v8_closure_7021153364b7efc4_u0}) (@_root_.«P202».«Geometry».«ExponentialJacobi».«differential_formula».{v8_closure_7021153364b7efc4_u0}) (@_root_.«P202».«Geometry».«ExponentialJacobi».«differential_zero».{v8_closure_7021153364b7efc4_u0}) (@_root_.«P202».«Geometry».«ExponentialJacobi».«endpoint_space».{v8_closure_7021153364b7efc4_u0}) (@_root_.«P202».«Geometry».«ExponentialJacobi».«kernel_equivalence».{v8_closure_7021153364b7efc4_u0}) (@_root_.«P202».«Geometry».«ExponentialJacobi».«multiplicity_finite».{v8_closure_7021153364b7efc4_u0}) (@_root_.«P202».«Geometry».«ExponentialJacobi».«radial_field».{v8_closure_7021153364b7efc4_u0}) (@_root_.«P202».«Geometry».«ExponentialJacobi».«two_zeros_normal».{v8_closure_7021153364b7efc4_u0})
theorem _root_.«P202».«Geometry».«JacobiMatrix».«invertible» : _root_.«P202Specs».«Geometry».«JacobiMatrix».«invertibleType».{v8_closure_7021153364b7efc4_u0} :=
  @_root_.«P202».«Geometry».«JacobiMatrix».«invertible_conditional».{v8_closure_7021153364b7efc4_u0} (@_root_.«P202».«Geometry».«ExponentialJacobi».«conjugacy_singularity».{v8_closure_7021153364b7efc4_u0}) (@_root_.«P202».«Geometry».«ExponentialJacobi».«differential_coordinates».{v8_closure_7021153364b7efc4_u0}) (@_root_.«P202».«Geometry».«ExponentialJacobi».«differential_formula».{v8_closure_7021153364b7efc4_u0}) (@_root_.«P202».«Geometry».«ExponentialJacobi».«differential_zero».{v8_closure_7021153364b7efc4_u0}) (@_root_.«P202».«Geometry».«ExponentialJacobi».«endpoint_space».{v8_closure_7021153364b7efc4_u0}) (@_root_.«P202».«Geometry».«ExponentialJacobi».«kernel_equivalence».{v8_closure_7021153364b7efc4_u0}) (@_root_.«P202».«Geometry».«ExponentialJacobi».«multiplicity_finite».{v8_closure_7021153364b7efc4_u0}) (@_root_.«P202».«Geometry».«ExponentialJacobi».«radial_field».{v8_closure_7021153364b7efc4_u0}) (@_root_.«P202».«Geometry».«ExponentialJacobi».«two_zeros_normal».{v8_closure_7021153364b7efc4_u0})
theorem _root_.«P202».«Geometry».«JacobiMatrix».«near_zero» : _root_.«P202Specs».«Geometry».«JacobiMatrix».«near_zeroType».{v8_closure_7021153364b7efc4_u0} :=
  @_root_.«P202».«Geometry».«JacobiMatrix».«near_zero_conditional».{v8_closure_7021153364b7efc4_u0} (@_root_.«P202».«Geometry».«ExponentialJacobi».«conjugacy_singularity».{v8_closure_7021153364b7efc4_u0}) (@_root_.«P202».«Geometry».«ExponentialJacobi».«differential_coordinates».{v8_closure_7021153364b7efc4_u0}) (@_root_.«P202».«Geometry».«ExponentialJacobi».«differential_formula».{v8_closure_7021153364b7efc4_u0}) (@_root_.«P202».«Geometry».«ExponentialJacobi».«differential_zero».{v8_closure_7021153364b7efc4_u0}) (@_root_.«P202».«Geometry».«ExponentialJacobi».«endpoint_space».{v8_closure_7021153364b7efc4_u0}) (@_root_.«P202».«Geometry».«ExponentialJacobi».«kernel_equivalence».{v8_closure_7021153364b7efc4_u0}) (@_root_.«P202».«Geometry».«ExponentialJacobi».«multiplicity_finite».{v8_closure_7021153364b7efc4_u0}) (@_root_.«P202».«Geometry».«ExponentialJacobi».«radial_field».{v8_closure_7021153364b7efc4_u0}) (@_root_.«P202».«Geometry».«ExponentialJacobi».«two_zeros_normal».{v8_closure_7021153364b7efc4_u0})
theorem _root_.«P202».«Geometry».«JacobiMatrix».«normal_construction» : _root_.«P202Specs».«Geometry».«JacobiMatrix».«normal_constructionType».{v8_closure_7021153364b7efc4_u0} :=
  @_root_.«P202».«Geometry».«JacobiMatrix».«normal_construction_conditional».{v8_closure_7021153364b7efc4_u0} (@_root_.«P202».«Geometry».«ExponentialJacobi».«conjugacy_singularity».{v8_closure_7021153364b7efc4_u0}) (@_root_.«P202».«Geometry».«ExponentialJacobi».«differential_coordinates».{v8_closure_7021153364b7efc4_u0}) (@_root_.«P202».«Geometry».«ExponentialJacobi».«differential_formula».{v8_closure_7021153364b7efc4_u0}) (@_root_.«P202».«Geometry».«ExponentialJacobi».«differential_zero».{v8_closure_7021153364b7efc4_u0}) (@_root_.«P202».«Geometry».«ExponentialJacobi».«endpoint_space».{v8_closure_7021153364b7efc4_u0}) (@_root_.«P202».«Geometry».«ExponentialJacobi».«kernel_equivalence».{v8_closure_7021153364b7efc4_u0}) (@_root_.«P202».«Geometry».«ExponentialJacobi».«multiplicity_finite».{v8_closure_7021153364b7efc4_u0}) (@_root_.«P202».«Geometry».«ExponentialJacobi».«radial_field».{v8_closure_7021153364b7efc4_u0}) (@_root_.«P202».«Geometry».«ExponentialJacobi».«two_zeros_normal».{v8_closure_7021153364b7efc4_u0})
theorem _root_.«P202».«Geometry».«JacobiMatrix».«regular_interval» : _root_.«P202Specs».«Geometry».«JacobiMatrix».«regular_intervalType».{v8_closure_7021153364b7efc4_u0} :=
  @_root_.«P202».«Geometry».«JacobiMatrix».«regular_interval_conditional».{v8_closure_7021153364b7efc4_u0} (@_root_.«P202».«Geometry».«ExponentialJacobi».«conjugacy_singularity».{v8_closure_7021153364b7efc4_u0}) (@_root_.«P202».«Geometry».«ExponentialJacobi».«differential_coordinates».{v8_closure_7021153364b7efc4_u0}) (@_root_.«P202».«Geometry».«ExponentialJacobi».«differential_formula».{v8_closure_7021153364b7efc4_u0}) (@_root_.«P202».«Geometry».«ExponentialJacobi».«differential_zero».{v8_closure_7021153364b7efc4_u0}) (@_root_.«P202».«Geometry».«ExponentialJacobi».«endpoint_space».{v8_closure_7021153364b7efc4_u0}) (@_root_.«P202».«Geometry».«ExponentialJacobi».«kernel_equivalence».{v8_closure_7021153364b7efc4_u0}) (@_root_.«P202».«Geometry».«ExponentialJacobi».«multiplicity_finite».{v8_closure_7021153364b7efc4_u0}) (@_root_.«P202».«Geometry».«ExponentialJacobi».«radial_field».{v8_closure_7021153364b7efc4_u0}) (@_root_.«P202».«Geometry».«ExponentialJacobi».«two_zeros_normal».{v8_closure_7021153364b7efc4_u0})
theorem _root_.«P202».«Geometry».«JacobiMatrix».«wronskian» : _root_.«P202Specs».«Geometry».«JacobiMatrix».«wronskianType».{v8_closure_7021153364b7efc4_u0} :=
  @_root_.«P202».«Geometry».«JacobiMatrix».«wronskian_conditional».{v8_closure_7021153364b7efc4_u0} (@_root_.«P202».«Geometry».«ExponentialJacobi».«conjugacy_singularity».{v8_closure_7021153364b7efc4_u0}) (@_root_.«P202».«Geometry».«ExponentialJacobi».«differential_coordinates».{v8_closure_7021153364b7efc4_u0}) (@_root_.«P202».«Geometry».«ExponentialJacobi».«differential_formula».{v8_closure_7021153364b7efc4_u0}) (@_root_.«P202».«Geometry».«ExponentialJacobi».«differential_zero».{v8_closure_7021153364b7efc4_u0}) (@_root_.«P202».«Geometry».«ExponentialJacobi».«endpoint_space».{v8_closure_7021153364b7efc4_u0}) (@_root_.«P202».«Geometry».«ExponentialJacobi».«kernel_equivalence».{v8_closure_7021153364b7efc4_u0}) (@_root_.«P202».«Geometry».«ExponentialJacobi».«multiplicity_finite».{v8_closure_7021153364b7efc4_u0}) (@_root_.«P202».«Geometry».«ExponentialJacobi».«radial_field».{v8_closure_7021153364b7efc4_u0}) (@_root_.«P202».«Geometry».«ExponentialJacobi».«two_zeros_normal».{v8_closure_7021153364b7efc4_u0})
