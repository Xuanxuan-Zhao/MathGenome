import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C12.ClassicalIntegralCalibrations
import MathGenome.Internal.MultivariableAnalysis.D04.C12.GaussDivergenceTheorem
import MathGenome.Internal.MultivariableAnalysis.D04.C12.DiskHemisphereAndBoxSigns
import MathGenome.Internal.MultivariableAnalysis.D04.C10.SphereAreaFlux
import MathGenome.Internal.MultivariableAnalysis.D04.C07.LinearVolume
import MathGenome.Internal.MultivariableAnalysis.D04.C09.LineIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! Explicit calibrations for paper.tex, d04:12:calibration. Sphere flux is
reused on its canonical surface integral. Ball volume follows from Gauss after
constructing its defining function and outward normal. Disk area is evaluated
by slicing and an antiderivative, and its work is the canonical Chapter 9 line
integral on one traversal. Box calculations use the actual positive face Gram
factors and outward normals, including at their edges. -/
noncomputable section
open Set Filter Topology
open scoped RealInnerProductSpace BigOperators ContDiff
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace D04.Calibrations
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C11.EuclideanVectorOperators.Model
open Specs.D04.C06.DarbouxIntegral.Model
open Specs.D04.C06.JordanRegions.Model
open Specs.D04.C10.PatchGeometryGram.Model
open Specs.D04.C10.AreaIntegral.Model
open Specs.D04.C10.SurfaceAssembly.Model
open Specs.D04.C10.SphereAreaFlux.Model
open Specs.D04.C12.DiskHemisphereAndBoxSigns.Model
open Specs.D04.C12.ClassicalIntegralCalibrations
open Model
local notation "Eucl" => Specs.D04.C01.EuclideanInterfaces.Model.E
open Specs.D04.C13.OrientedEuclideanDictionary.Model
open Specs.D04.C15.CellsChainsAndIntegrals.Model

private lemma ext3 {x y : Eucl 3} (h0 : x 0 = y 0) (h1 : x 1 = y 1)
    (h2 : x 2 = y 2) : x = y := by
  apply PiLp.ext
  intro i
  fin_cases i <;> assumption

private lemma basis_apply {n : ℕ} (i j : Fin n) :
    Specs.D04.C01.EuclideanInterfaces.Model.standardBasis n i j = if i = j then 1 else 0 := by
  simp [Specs.D04.C01.EuclideanInterfaces.Model.standardBasis, EuclideanSpace.basisFun_apply, PiLp.single_apply, eq_comm]

private lemma inner3 (x y : Eucl 3) :
    ⟪x,y⟫ = x 0*y 0 + x 1*y 1 + x 2*y 2 := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ]
  ring

theorem radial_divergence (x : Eucl 3) :
    Specs.D04.C11.EuclideanVectorOperators.Model.divergence (fun y : Eucl 3 => y) x = 3 := by
  simp [Specs.D04.C11.EuclideanVectorOperators.Model.divergence, Specs.D04.C02.DerivativeInterfaces.Model.totalDerivative, fderiv_id, LinearMap.trace_id]

theorem sphere_calibration : sphere_calibrationType := D04.SphereAreaFlux.sphere_flux

private def rotationLinear : Eucl 3 →ₗ[ℝ] Eucl 3 where
  toFun := rotationField
  map_add' x y := by apply ext3 <;> simp [rotationField] <;> ring
  map_smul' t x := by apply ext3 <;> simp [rotationField] <;> ring

private lemma rotation_derivative (x : Eucl 3) :
    fderiv ℝ rotationField x = rotationLinear.toContinuousLinearMap :=
  rotationLinear.toContinuousLinearMap.hasFDerivAt.fderiv

theorem rotation_curl (x : Eucl 3) : Specs.D04.C11.EuclideanVectorOperators.Model.curl rotationField x =
    Specs.D04.C01.EuclideanInterfaces.Model.standardBasis 3 2 := by
  have hj (i j : Fin 3) :
      Specs.D04.C02.DerivativeBridge.Model.jacobian rotationField x i j =
        rotationField (Specs.D04.C01.EuclideanInterfaces.Model.standardBasis 3 j) i := by
    change Specs.D04.C01.EuclideanInterfaces.Model.matrixOfLinearMap
      (fderiv ℝ rotationField x).toLinearMap i j = _
    rw [rotation_derivative]
    exact D04.matrixOfLinearMap_apply rotationLinear i j
  apply ext3 <;>
    simp [Specs.D04.C11.EuclideanVectorOperators.Model.curl, hj, rotationField, basis_apply] <;> norm_num

lemma circle_work_value (R t : ℝ) : circleWork R t = R^2/2 := by
  have hd := D04.SignExamples.circle_derivative R t
  rw [circleWork, hd.deriv, inner3]
  simp [rotationField, circle, basis_apply]
  nlinarith [Real.sin_sq_add_cos_sq t]

private lemma constant_riemann (C a b : ℝ) (hab : a ≤ b) :
    ∃ h : Specs.SingleVariableAnalysis.Ch08.Integral.realIntegrableValue
      (fun _ : ℝ => C) a b,
      Specs.SingleVariableAnalysis.Ch08.Integral.realIntegralValue (fun _ : ℝ => C) h =
        C*(b-a) := by
  have h := D04.C09.riemann_integrable_of_continuousOn hab
    (continuousOn_const : ContinuousOn (fun _ : ℝ => C) (Icc a b))
  refine ⟨h, ?_⟩
  have hv := SingleVariableAnalysis.Riemann.real_ftc_second
    (fun t => C*t) (fun _ => C) a b hab (by fun_prop)
    (fun t _ => by simpa using (hasDerivAt_id t).const_mul C) h
  exact hv.trans (by ring)

theorem circle_work : circle_workType := by
  intro R hR
  refine ⟨circle_work_value R, ?_⟩
  have he : circleWork R = fun _ => R^2/2 := funext (circle_work_value R)
  rw [he]
  obtain ⟨h,hv⟩ := constant_riemann (R^2/2) 0 (2*Real.pi) (by positivity)
  exact ⟨h, hv.trans (by ring)⟩

lemma reversed_work_value (R t : ℝ) : reversedWork R t = -(R^2/2) := by
  have hv : deriv (reversedCircle R) t =
      -deriv (circle R) (2*Real.pi-t) := deriv_comp_const_sub (circle R) (2*Real.pi) t
  rw [reversedWork, hv, inner_neg_right]
  exact congrArg Neg.neg (circle_work_value R (2*Real.pi-t))

theorem reversal : reversalType := by
  intro R hR
  refine ⟨?_, reversed_work_value R, ?_⟩
  · intro x hx
    have h := (D04.SignExamples.disk_signs R hR x hx).2.2.1
    change euclideanCross (-(Specs.D04.C01.EuclideanInterfaces.Model.standardBasis 3 2)) (radial R x) = _
    apply ext3 <;> simp_all [euclideanCross, crossProduct, basis_apply, ccw, radial, div_eq_mul_inv] <;> ring
  · have he : reversedWork R = fun _ => -(R^2/2) := funext (reversed_work_value R)
    rw [he]
    obtain ⟨h,hv⟩ := constant_riemann (-(R^2/2)) 0 (2*Real.pi) (by positivity)
    exact ⟨h, hv.trans (by ring)⟩


open Specs.D04.C12.ClassicalRegularDomains.Model
open Specs.D04.C12.GaussDivergenceTheorem.Model

private def ballRho (R : ℝ) (x : Eucl 3) : ℝ := ‖x‖^2 - R^2

private lemma ballRho_derivative (R : ℝ) (x : Eucl 3) :
    HasFDerivAt (ballRho R) ((2 : ℝ) • innerSL ℝ x) x := by
  convert (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sub_const (R^2) using 1
  all_goals first | rfl | simp [two_nsmul, two_smul]

lemma ball_frontier (R : ℝ) (hR : 0 < R) :
    frontier (Metric.ball (0 : Eucl 3) R) = sphere R := by
  rw [frontier_ball _ hR.ne']
  ext x
  simp [Metric.mem_sphere, sphere, dist_zero_right]

lemma ball_defining (R : ℝ) (hR : 0 < R) :
    IsDefiningFunction (Metric.ball (0 : Eucl 3) R) univ (ballRho R) := by
  refine ⟨isOpen_univ, ?_, ?_, ?_, ?_⟩
  · exact ((contDiff_norm_sq ℝ).sub contDiff_const).contDiffOn
  · intro x _
    simp only [Metric.mem_ball, dist_zero_right, ballRho]
    constructor <;> intro h <;> nlinarith [norm_nonneg x]
  · intro x _
    rw [ball_frontier R hR]
    change ‖x‖ = R ↔ ‖x‖^2-R^2=0
    constructor <;> intro h <;> nlinarith [norm_nonneg x]
  · intro x _ hx he
    have hv := congrArg (fun A : Eucl 3 →L[ℝ] ℝ => A x) he
    rw [(ballRho_derivative R x).fderiv] at hv
    simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply,
      smul_eq_mul, ContinuousLinearMap.zero_apply, real_inner_self_eq_norm_sq] at hv
    dsimp [ballRho] at hx
    nlinarith

lemma ball_regular (R : ℝ) (hR : 0 < R) :
    IsClassicalRegularDomain (Metric.ball (0 : Eucl 3) R) := by
  exact ⟨by norm_num, Metric.isBounded_ball, Metric.isOpen_ball,
    fun p hp => ⟨univ,ballRho R, mem_univ p,ball_defining R hR⟩⟩

private lemma ball_gradient (R : ℝ) (x : Eucl 3) :
    Specs.D04.C02.DerivativeBridge.Model.scalarGradient (ballRho R) x = (2 : ℝ) • x := by
  apply ext_inner_right ℝ
  intro v
  have he := D04.scalarGradient_represents (ballRho R) x v
  exact he.symm.trans (by
    change fderiv ℝ (ballRho R) x v = _
    rw [(ballRho_derivative R x).fderiv]; simp [real_inner_smul_left])

lemma ball_normal (R : ℝ) (hR : 0 < R)
    (x : frontier (Metric.ball (0 : Eucl 3) R)) :
    outwardNormal (ball_regular R hR) x = R⁻¹ • (x : Eucl 3) := by
  rw [D04.ClassicalRegularDomains.outwardNormal_formula
    (ball_regular R hR) x (ball_defining R hR) (mem_univ _)]
  change ‖Specs.D04.C02.DerivativeBridge.Model.scalarGradient (ballRho R) x‖⁻¹ •
    Specs.D04.C02.DerivativeBridge.Model.scalarGradient (ballRho R) x = _
  rw [ball_gradient, norm_smul]
  have hx : ‖(x : Eucl 3)‖ = R := by
    exact (ball_frontier R hR).subset x.property
  rw [hx]
  norm_num
  rw [smul_smul]
  congr 1
  field_simp

private lemma region_constant {n : ℕ} {S : Set (Specs.D04.C01.EuclideanInterfaces.Model.E n)}
    (hS : Jordan S) (C : ℝ) :
    RegionIntegrable (fun _ : S => C) ∧ regionIntegral (fun _ : S => C) = C * volume S := by
  simpa only [mul_one, D04.JordanRegions.regionIntegral_one] using
    D04.SlicingAndMoments.region_smul (D04.JordanRegions.jordan_bounded hS)
      (fun _ : S => (1 : ℝ)) (D04.LinearVolume.region_one_integrable hS) C

lemma density_value {M : Set (Eucl 3)} (f : M → ℝ) (I : ℝ)
    (h : HasDensityIntegral (d := 2) f I) : surfaceIntegral M f = I := by
  unfold surfaceIntegral
  rw [dif_pos h.2.2.1]
  exact (h.2.2.2 (Classical.choice h.2.2.1)).2

theorem ball_calibration : ball_calibrationType := by
  intro R hR
  have hD := ball_regular R hR
  have hj := (D04.RegularDomainGeometry.jordan_domain_and_closure hD).1
  obtain ⟨hi,hg⟩ := D04.Gauss.gauss hD univ (fun x : Eucl 3 => x)
    isOpen_univ (subset_univ _) (by
      change D04.CrOn 1 univ (fun x : Eucl 3 => x)
      exact (D04.crOn_iff_contDiffOn 1 _ _ isOpen_univ).mpr contDiffOn_id)
  have hv := density_value _ _ hg
  have hnormal : normalFlux (fun x : Eucl 3 => x) (outwardNormal hD) =
      fun x : frontier (Metric.ball (0 : Eucl 3) R) => ⟪(x : Eucl 3), R⁻¹ • (x : Eucl 3)⟫ := by
    funext x
    change ⟪(x : Eucl 3), outwardNormal hD x⟫ = _
    rw [ball_normal R hR]
  rw [hnormal] at hv
  have hsurface : surfaceIntegral (frontier (Metric.ball (0 : Eucl 3) R))
      (fun x => ⟪(x : Eucl 3), R⁻¹ • (x : Eucl 3)⟫) =
      surfaceIntegral (sphere R) (fun x => ⟪(x : Eucl 3), radialNormal R x⟫) := by
    exact congrArg (fun M : Set (Eucl 3) => surfaceIntegral M
      (fun x => ⟪(x : Eucl 3), R⁻¹ • (x : Eucl 3)⟫)) (ball_frontier R hR)
  rw [hsurface] at hv
  have hconst := region_constant hj 3
  have hdiv : (fun x : Metric.ball (0 : Eucl 3) R => Specs.D04.C11.EuclideanVectorOperators.Model.divergence (fun y : Eucl 3 => y) x) =
      fun _ => (3 : ℝ) := funext (fun x => radial_divergence x)
  refine ⟨hj, ?_, hi, hv.symm⟩
  rw [hdiv, hconst.2] at hv
  rw [sphere_calibration R hR] at hv
  linarith


private def diskBase (R : ℝ) (hR : 0 < R) : Box 1 :=
  intervalBox (-R) R (by linarith)
private def diskHeight (R : ℝ) (u : Eucl 1) : ℝ := Real.sqrt (R^2-u 0^2)

lemma disk_slicing (R : ℝ) (hR : 0 < R) :
    diskParameters R = Specs.D04.C06.SlicingAndMoments.Model.between
      (carrier (diskBase R hR)) (fun x => -diskHeight R x) (diskHeight R) := by
  ext z
  change z 0^2+z 1^2 ≤ R^2 ↔ _
  simp only [Specs.D04.C06.SlicingAndMoments.Model.between,
    Specs.D04.C06.SlicingAndMoments.Model.basePoint,
    Specs.D04.C06.SlicingAndMoments.Model.height, mem_setOf_eq, WithLp.ofLp_toLp,
    ↓reduceIte]
  have hb : (WithLp.toLp 2 (fun i : Fin 1 => z (Fin.castAdd 1 i))) ∈ carrier (diskBase R hR) ↔
      -R ≤ z 0 ∧ z 0 ≤ R := by
    change (∀ i : Fin 1, -R ≤ z (Fin.castAdd 1 i) ∧ z (Fin.castAdd 1 i) ≤ R) ↔ _
    simp [Fin.forall_fin_one]
  rw [hb]
  change _ ↔ (-R ≤ z 0 ∧ z 0 ≤ R) ∧
    -Real.sqrt (R^2-z 0^2) ≤ z 1 ∧ z 1 ≤ Real.sqrt (R^2-z 0^2)
  constructor
  · intro hz
    have hh : 0 ≤ R^2-z 0^2 := by nlinarith [sq_nonneg (z 1)]
    have hs := Real.sq_sqrt hh
    have hp := Real.sqrt_nonneg (R^2-z 0^2)
    exact ⟨⟨by nlinarith,by nlinarith⟩,by nlinarith,by nlinarith⟩
  · rintro ⟨hx,hy⟩
    have hh : 0 ≤ R^2-z 0^2 := by nlinarith
    have hs := Real.sq_sqrt hh
    nlinarith [mul_nonneg (sub_nonneg.mpr hy.2) (sub_nonneg.mpr hy.1)]

private def diskPrimitive (R t : ℝ) : ℝ :=
  t * Real.sqrt (R^2-t^2) + R^2 * Real.arcsin (t/R)

lemma diskPrimitive_deriv (R : ℝ) (hR : 0 < R) (t : ℝ) (ht : t ∈ Ioo (-R) R) :
    HasDerivAt (diskPrimitive R) (2*Real.sqrt (R^2-t^2)) t := by
  have hp : 0 < R^2-t^2 := by nlinarith [ht.1,ht.2]
  have hs : 0 < Real.sqrt (R^2-t^2) := Real.sqrt_pos.mpr hp
  have hsq := Real.sq_sqrt hp.le
  have hlow : -1 < t/R := (lt_div_iff₀ hR).mpr (by linarith [ht.1])
  have hhigh : t/R < 1 := (div_lt_iff₀ hR).mpr (by linarith [ht.2])
  have hroot : Real.sqrt (1-(t/R)^2) = Real.sqrt (R^2-t^2)/R := by
    have he : 1-(t/R)^2 = (Real.sqrt (R^2-t^2)/R)^2 := by
      field_simp
      nlinarith
    rw [he,Real.sqrt_sq (le_of_lt (div_pos hs hR))]
  have hd := ((hasDerivAt_id t).mul
    (((hasDerivAt_const t (R^2)).sub ((hasDerivAt_id t).pow 2)).sqrt hp.ne')).add
    (((Real.hasDerivAt_arcsin (ne_of_gt hlow) (ne_of_lt hhigh)).comp t
      ((hasDerivAt_id t).div_const R)).const_mul (R^2))
  convert hd using 1
  · rfl
  · dsimp
    rw [hroot]
    field_simp
    nlinarith


lemma disk_volume (R : ℝ) (hR : 0 < R) :
    Jordan (diskParameters R) ∧ volume (diskParameters R) = Real.pi*R^2 := by
  let Q := diskBase R hR
  have hj := D04.OneCoordinate.Boxes.jordan_carrier Q
  have hlo : ContinuousOn (fun x : Eucl 1 => -diskHeight R x) (closure (carrier Q)) := by
    apply Continuous.continuousOn
    unfold diskHeight
    fun_prop
  have hhi : ContinuousOn (diskHeight R) (closure (carrier Q)) := by
    apply Continuous.continuousOn
    unfold diskHeight
    fun_prop
  have hab : ∀ x ∈ closure (carrier Q), -diskHeight R x ≤ diskHeight R x := by
    intro x hx
    exact neg_le_self (Real.sqrt_nonneg _)
  have hjd := D04.SlicingAndMoments.between_jordan (carrier Q) hj
    (fun x => -diskHeight R x) (diskHeight R) hlo hhi hab
  have hv := D04.SlicingAndMoments.between_volume (carrier Q)
    (fun x => -diskHeight R x) (diskHeight R) hj hlo hhi hab
  change Jordan (Specs.D04.C06.SlicingAndMoments.Model.between
    (carrier (diskBase R hR)) (fun x => -diskHeight R x) (diskHeight R)) at hjd
  change RegionIntegrable (fun x : carrier Q => diskHeight R x - -diskHeight R x) ∧
    volume (Specs.D04.C06.SlicingAndMoments.Model.between
      (carrier (diskBase R hR)) (fun x => -diskHeight R x) (diskHeight R)) = _ at hv
  rw [← disk_slicing R hR] at hjd hv
  refine ⟨hjd, hv.2.trans ?_⟩
  have hfun : (fun x : carrier Q => diskHeight R x - -diskHeight R x) =
      fun x : carrier Q => 2*Real.sqrt (R^2-(x : Eucl 1) 0^2) := by funext x; dsimp [diskHeight]; ring
  rw [hfun]
  have hi : RegionIntegrable (fun x : carrier Q => 2*Real.sqrt (R^2-(x : Eucl 1) 0^2)) := by
    rw [← hfun]; exact hv.1
  have he := D04.SphereAreaFlux.regionIntegral_closedBox (by norm_num) Q
    (by intro i; fin_cases i; change -R < R; linarith)
    (fun x : Eucl 1 => 2*Real.sqrt (R^2-x 0^2)) hi
  refine he.trans ?_
  have hbox := D04.SlicingAndMoments.continuous_box_integrable
    (fun x : Eucl 1 => 2*Real.sqrt (R^2-x 0^2)) (by fun_prop) Q
  obtain ⟨hs,hval⟩ := (D04.Darboux.scalar_integral _ (-R) R (by linarith)).2 hbox
  have hftc := SingleVariableAnalysis.Riemann.real_ftc_second (diskPrimitive R)
    (fun t => 2*Real.sqrt (R^2-t^2)) (-R) R (by linarith)
    (by unfold diskPrimitive; fun_prop) (fun t ht => diskPrimitive_deriv R hR t ht) hs
  exact hval.trans (hftc.trans (by
    simp [diskPrimitive, hR.ne', div_self, Real.arcsin_one, Real.arcsin_neg_one]
    <;> ring))


private def planeLinear : Eucl 2 →ₗ[ℝ] Eucl 3 where
  toFun := plane
  map_add' u v := by apply ext3 <;> simp [plane]
  map_smul' t u := by apply ext3 <;> simp [plane]

lemma plane_derivative (u : Eucl 2) : fderiv ℝ plane u = planeLinear.toContinuousLinearMap :=
  planeLinear.toContinuousLinearMap.hasFDerivAt.fderiv

lemma plane_injective : Function.Injective plane := by
  intro u v he
  apply PiLp.ext
  intro i
  fin_cases i
  · exact congrArg (fun x : Eucl 3 => x 0) he
  · exact congrArg (fun x : Eucl 3 => x 1) he

lemma plane_areaVector (u : Eucl 2) : areaVector plane u = Specs.D04.C01.EuclideanInterfaces.Model.standardBasis 3 2 := by
  apply ext3 <;>
    simp [areaVector, columns, plane_derivative, planeLinear, plane, cross, basis_apply,
      crossProduct]

lemma plane_density (u : Eucl 2) : patchJacobian plane u = 1 := by
  change gramFactor _ = _
  have hg := D04.PatchGeometryGram.gram_cross (fderiv ℝ plane u).toLinearMap
  change gramFactor _ = _ at hg
  rw [hg]
  change ‖areaVector plane u‖ = 1
  rw [plane_areaVector]
  simp [Specs.D04.C01.EuclideanInterfaces.Model.standardBasis]

theorem disk_geometry : disk_geometryType := by
  intro R hR
  refine ⟨?_, plane_injective, ?_, plane_areaVector, (disk_volume R hR).1⟩
  · ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨rfl,hu⟩
    · rintro ⟨hz,hs⟩
      refine ⟨WithLp.toLp 2 ![x 0,x 1], hs, ?_⟩
      apply ext3 <;> simp [plane,hz]
  · refine ⟨isOpen_univ, planeLinear.toContinuousLinearMap.contDiff.contDiffOn, ?_⟩
    intro u hu
    rw [plane_derivative]
    exact plane_injective

theorem disk_flux : disk_fluxType := by
  intro R hR
  have hj := (disk_volume R hR).1
  have hv := (disk_volume R hR).2
  have hi := (region_constant hj 1).1
  have hcoef : fluxIntegrand (diskParameters R) plane (fun x => Specs.D04.C11.EuclideanVectorOperators.Model.curl rotationField x) =
      fun _ => (1 : ℝ) := by
    funext u
    rw [fluxIntegrand, rotation_curl, plane_areaVector]
    simp [Specs.D04.C01.EuclideanInterfaces.Model.standardBasis]
  have hvalue : fluxIntegral (diskParameters R) plane (fun x => Specs.D04.C11.EuclideanVectorOperators.Model.curl rotationField x) =
      Real.pi*R^2 := by
    unfold fluxIntegral
    rw [hcoef]
    exact (D04.JordanRegions.regionIntegral_one _).trans hv
  refine ⟨⟨?_, ?_⟩, hvalue, ?_, ?_⟩
  · refine ⟨1, fun x => ?_⟩
    change ‖Specs.D04.C11.EuclideanVectorOperators.Model.curl rotationField (x : Eucl 3)‖ ≤ 1
    rw [rotation_curl]
    simp [Specs.D04.C01.EuclideanInterfaces.Model.standardBasis]
  · rw [hcoef]; exact hi
  · change regionIntegral (fun u : diskParameters R =>
      ⟪Specs.D04.C11.EuclideanVectorOperators.Model.curl rotationField (imagePoint (diskParameters R) plane u), Specs.D04.C01.EuclideanInterfaces.Model.standardBasis 3 2⟫ *
        patchJacobian plane u) = _
    simp only [rotation_curl,plane_density]
    simpa [Specs.D04.C01.EuclideanInterfaces.Model.standardBasis] using (region_constant hj 1).2.trans (by simpa using hv)
  · change regionIntegral (fun u : diskParameters R =>
      ⟪Specs.D04.C11.EuclideanVectorOperators.Model.curl rotationField (imagePoint (diskParameters R) plane u), -Specs.D04.C01.EuclideanInterfaces.Model.standardBasis 3 2⟫ *
        patchJacobian plane u) = _
    simp only [rotation_curl,plane_density,inner_neg_right]
    simpa [Specs.D04.C01.EuclideanInterfaces.Model.standardBasis,hv] using (region_constant hj (-1)).2

lemma face_areaVector (a b c : ℝ) (i : Fin 3) (upper : Bool) (u : Eucl 2) :
    areaVector (boxFace 0 (lengths a b c) i upper) u =
      ((-1 : ℝ)^i.val * ∏ j : Fin 2, lengths a b c (i.succAbove j)) • Specs.D04.C01.EuclideanInterfaces.Model.standardBasis 3 i := by
  unfold areaVector columns
  change cross (Specs.D04.C02.DerivativeInterfaces.Model.totalDerivative _ u (Specs.D04.C01.EuclideanInterfaces.Model.standardBasis 2 0))
    (Specs.D04.C02.DerivativeInterfaces.Model.totalDerivative _ u (Specs.D04.C01.EuclideanInterfaces.Model.standardBasis 2 1)) = _
  rw [D04.SignExamples.box_face_derivative,D04.SignExamples.box_face_derivative]
  fin_cases i <;> apply ext3 <;>
    norm_num [cross, crossProduct, basis_apply, lengths, Fin.prod_univ_succ, Fin.succAbove] <;> ring

lemma face_density (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (i : Fin 3) (upper : Bool) (u : Eucl 2) :
    patchJacobian (boxFace 0 (lengths a b c) i upper) u =
      ∏ j : Fin 2, lengths a b c (i.succAbove j) := by
  change gramFactor _ = _
  have hg := D04.PatchGeometryGram.gram_cross (fderiv ℝ (boxFace 0 (lengths a b c) i upper) u).toLinearMap
  change gramFactor _ = _ at hg
  rw [hg]
  change ‖areaVector (boxFace 0 (lengths a b c) i upper) u‖ = _
  rw [face_areaVector, norm_smul]
  have hl : ∀ j : Fin 3, 0 < lengths a b c j := by
    intro j; fin_cases j <;> assumption
  have hp : 0 < ∏ j : Fin 2, lengths a b c (i.succAbove j) :=
    Finset.prod_pos (fun _ _ => hl _)
  simp [Real.norm_eq_abs, abs_mul, abs_of_pos hp, Specs.D04.C01.EuclideanInterfaces.Model.standardBasis]
  rw [abs_of_pos (hl _),abs_of_pos (hl _)]

lemma face_coefficient (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (i : Fin 3) (upper : Bool) (u : Eucl 2) :
    ⟪boxFace 0 (lengths a b c) i upper u,
      (if upper then Specs.D04.C01.EuclideanInterfaces.Model.standardBasis 3 i else -Specs.D04.C01.EuclideanInterfaces.Model.standardBasis 3 i)⟫ *
      patchJacobian (boxFace 0 (lengths a b c) i upper) u =
      if upper then a*b*c else 0 := by
  rw [face_density a b c ha hb hc]
  rw [inner3]
  fin_cases i <;> cases upper <;>
    norm_num [boxFace,boxMap, faceInsertion, basis_apply,
      lengths, Fin.prod_univ_succ, Fin.succAbove, Fin.insertNth] <;> ring

lemma cube_constant (C : ℝ) : RegionIntegrable (fun _ : cube 2 => C) ∧
    regionIntegral (fun _ : cube 2 => C) = C := by
  have hj := D04.OneCoordinate.Boxes.jordan_carrier (cubeBox 2)
  have hi := (region_constant hj C).1
  refine ⟨hi, ?_⟩
  have he := D04.SphereAreaFlux.regionIntegral_closedBox (by norm_num) (cubeBox 2)
    (by intro i; norm_num [cubeBox]) (fun _ => C) hi
  exact he.trans ((D04.Darboux.constant_integrals (cubeBox 2) C).1.trans (by
    simp [Specs.D04.C06.DarbouxIntegral.Model.content, cubeBox]))

theorem box_faces : box_facesType := by
  intro a b c ha hb hc
  have hcoef (i : Fin 3) (upper : Bool) :
      (fun u : cube 2 => ⟪boxFace 0 (lengths a b c) i upper u,
        (if upper then Specs.D04.C01.EuclideanInterfaces.Model.standardBasis 3 i else -Specs.D04.C01.EuclideanInterfaces.Model.standardBasis 3 i)⟫ *
        patchJacobian (boxFace 0 (lengths a b c) i upper) u) =
      fun _ => if upper then a*b*c else 0 :=
    funext (fun u => face_coefficient a b c ha hb hc i upper u)
  constructor
  · intro i
    constructor <;> unfold faceFlux normalFluxIntegral parameterAreaIntegral
    · change regionIntegral (fun u : cube 2 => ⟪boxFace 0 (lengths a b c) i false u,
        -Specs.D04.C01.EuclideanInterfaces.Model.standardBasis 3 i⟫ *
        patchJacobian (boxFace 0 (lengths a b c) i false) u) = 0
      have hh := hcoef i false
      simp only [Bool.false_eq_true, ↓reduceIte] at hh
      rw [hh]; exact (cube_constant 0).2
    · change regionIntegral (fun u : cube 2 => ⟪boxFace 0 (lengths a b c) i true u,
        Specs.D04.C01.EuclideanInterfaces.Model.standardBasis 3 i⟫ *
        patchJacobian (boxFace 0 (lengths a b c) i true) u) = a*b*c
      have hh := hcoef i true
      simp only [↓reduceIte] at hh
      rw [hh]; exact (cube_constant (a*b*c)).2
  · intro i upper
    rw [hcoef]
    exact (cube_constant _).1

theorem box_total : box_totalType := by
  intro a b c ha hb hc
  have he : (fun x : Eucl 3 => Specs.D04.C11.EuclideanVectorOperators.Model.divergence (fun y : Eucl 3 => y) x) = fun _ => (3:ℝ) :=
    funext radial_divergence
  have hf := (box_faces a b c ha hb hc).1
  have hs : (∑ i : Fin 3, (faceFlux a b c i true + faceFlux a b c i false)) = 3*a*b*c := by
    simp only [hf,add_zero,Fin.sum_univ_succ,Fin.sum_univ_zero]
    ring
  refine ⟨?_, hs, ?_⟩
  · rw [he]; exact D04.Darboux.integrable_const _ _
  · rw [he, hs]
    exact (D04.Darboux.constant_integrals (rectangle a b c ha hb hc) 3).1.trans (by
      simp [rectangle, content, lengths, Fin.prod_univ_succ]
      ring)


open Specs.D04.C09.PathsLength.Model
open Specs.D04.C09.LineIntegrals.Model

lemma circle_interval_image (R : ℝ) (hR : 0 < R) :
    circle R '' Icc 0 (2*Real.pi) = equator R := by
  apply Subset.antisymm
  · rintro x ⟨t,ht,rfl⟩
    exact ((D04.SignExamples.circle_traversal R hR).1 t).1
  · intro x hx
    obtain ⟨c,hc,himage,_⟩ := D04.SignExamples.hemisphere_seam R hR
    have hx' : x ∈ Set.range (fun u : cube 1 => (c.toFun u).val) := himage.symm ▸ hx
    obtain ⟨u,hu⟩ := hx'
    refine ⟨2*Real.pi*u.val 0, ?_, ?_⟩
    · have hb := (D04.Cells.mem_cube u.val).mp u.property (0 : Fin 1)
      constructor
      · exact mul_nonneg (by positivity) hb.1
      · nlinarith [Real.pi_pos,hb.2]
    · change circle R (2*Real.pi*u.val 0) = x
      rw [← hc u]
      exact hu

theorem boundary_circulation : boundary_circulationType := by
  intro R hR
  let γ : IntervalPath 3 0 (2*Real.pi) := {
    ordered := by positivity
    toFun := circle R
    continuousOn := (continuous_iff_continuousAt.mpr
      (fun t => (D04.SignExamples.circle_derivative R t).continuousAt)).continuousOn }
  let P : SingleVariableAnalysis.Riemann.PartitionData 0 (2*Real.pi) := {
    n := 1
    point := ![0,2*Real.pi]
    strictMono := by
      intro i j hij
      fin_cases i <;> fin_cases j
      · exact (lt_irrefl _ hij).elim
      · exact mul_pos (by norm_num) Real.pi_pos
      · norm_num at hij
      · exact (lt_irrefl _ hij).elim
    first := rfl
    last := rfl }
  have hvcont : Continuous (deriv (circle R)) := by
    have he : deriv (circle R) = fun t =>
        (-R*Real.sin t) • Specs.D04.C01.EuclideanInterfaces.Model.standardBasis 3 0 +
        (R*Real.cos t) • Specs.D04.C01.EuclideanInterfaces.Model.standardBasis 3 1 :=
      funext (fun t => (D04.SignExamples.circle_derivative R t).deriv)
    rw [he]
    fun_prop
  let d : PiecewiseC1Data γ := {
    partition := P
    velocity := fun _ => deriv (circle R)
    smooth := by
      intro i
      refine ⟨hvcont.continuousOn, ?_⟩
      intro t ht
      have hd := D04.SignExamples.circle_derivative R t
      rw [← hd.deriv] at hd
      exact hd.hasDerivWithinAt }
  obtain ⟨h,hvalue⟩ := (circle_work R hR).2
  have hi : WorkIntegrable d rotationField := by
    intro i
    fin_cases i
    exact h
  have hwork : workLineIntegral d rotationField hi = Real.pi*R^2 := by
    change (∑ i : Fin 1, Specs.SingleVariableAnalysis.Ch08.Integral.realIntegralValue
      (circleWork R) (hi i)) = _
    simpa only [Fin.sum_univ_one] using hvalue
  refine ⟨γ, fun _ => rfl, circle_interval_image R hR,
    D04.SignExamples.circle_single_traversal R hR,
    (D04.SignExamples.circle_traversal R hR).2.2.symm, ?_, d, hi, hwork, ?_⟩
  · intro x hx
    have hx' : x ∈ equator R := (circle_interval_image R hR).subset hx
    have hs := D04.SignExamples.disk_signs R hR x hx'
    exact ⟨hs.2.1,hs.2.2.1⟩
  · exact hwork.trans (disk_flux R hR).2.2.1.symm

end D04.Calibrations
