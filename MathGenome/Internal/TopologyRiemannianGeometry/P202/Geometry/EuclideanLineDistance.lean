import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.EuclideanLineDistance
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.LocalCurveTrapping
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap

set_option autoImplicit false
namespace P202.Geometry.EuclideanLineDistance
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.TangentBundleData
  SmoothManifolds.BundleOperationsData SmoothManifolds.FrameData
  P202.MetricData P202.ConnectionData P202.CurveData P202.DistanceData
  P202.CompleteExponentialData P202.CompletenessData Set Filter
open scoped Topology

variable {S : SmoothManifold 1 .euclidean ℝ}

/-- The intrinsic scalar differential of the standard coordinate is its
component in every tangent trivialization supplied by that chart. -/
theorem scalar_coordinate (e : ModelChart 1 .euclidean ℝ)
    (he : e ∈ S.smoothStructure.val) (hcoord : ∀ x : ℝ, (e x).val 0 = x)
    (x : ℝ) (hx : x ∈ e.source) (v : TangentSpace S x) :
    scalarDerivative S (fun y : ℝ => y) x v =
      (tangentStructure S).fiberCoordinates.equiv e he x hx v 0 := by
  classical
  have hs : SmoothManifolds.PartitionData.ScalarContDiffAt (⊤ : ℕ∞)
      S.smoothStructure.val (fun y : ℝ => y) x := by
    have h := SmoothManifolds.scalarContDiffAt_of_chart
      S.smoothStructure.property.1 he hx
      (show ∃ U, IsOpen U ∧ (e x).val ∈ U ∧
        ∃ F : Euclidean 1 → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) F U ∧
          (fun y => F (e y).val) =ᶠ[𝓝 x] (fun y : ℝ => y) from
        ⟨univ, isOpen_univ, mem_univ _, (fun z => z 0),
          (contDiff_apply ℝ (fun _ : Fin 1 => ℝ) 0).contDiffOn,
          Eventually.of_forall hcoord⟩)
    exact h
  obtain ⟨coords, hcoords, hval⟩ :=
    (tangentStructure S).fiberCoordinates.isCoordinates e he x hx
  have hg : scalarGerm S (fun y : ℝ => y) x = coords 0 := by
    apply Subtype.ext
    simp only [scalarGerm, dite_eq_left hs]
    rw [hcoords]
    exact congrArg Germ.ofFun (funext hcoord).symm
  change (v.val (scalarGerm S (fun y : ℝ => y) x)) = _
  rw [hg, hval]

theorem norm_one (v : Euclidean 1) : ‖v‖ = |v 0| := by
  have hv : v = fun _ => v 0 := by ext i; exact congrArg v (Subsingleton.elim i 0)
  rw [hv]
  simp

theorem tangentNorm_coordinate (g : RiemannianMetric S)
    (hg : ∀ (x : ℝ) (v w : TangentSpace S x), pairing g x v w =
      scalarDerivative S (fun y : ℝ => y) x v * scalarDerivative S (fun y : ℝ => y) x w)
    (e : ModelChart 1 .euclidean ℝ) (he : e ∈ S.smoothStructure.val)
    (hcoord : ∀ x : ℝ, (e x).val 0 = x) (x : ℝ) (hx : x ∈ e.source)
    (v : TangentSpace S x) :
    tangentNorm g x v = ‖(tangentStructure S).fiberCoordinates.equiv e he x hx v‖ := by
  rw [norm_one, ← scalar_coordinate e he hcoord]
  unfold tangentNorm
  rw [hg, ← pow_two, Real.sqrt_sq_eq_abs]

/-- Every one of the original compact-interval curves has at least the
absolute displacement as its integral length. -/
theorem displacement_le_length (g : RiemannianMetric S)
    (hg : ∀ (x : ℝ) (v w : TangentSpace S x), pairing g x v w =
      scalarDerivative S (fun y : ℝ => y) x v * scalarDerivative S (fun y : ℝ => y) x w)
    (e : ModelChart 1 .euclidean ℝ) (he : e ∈ S.smoothStructure.val)
    (hsource : e.source = univ) (hcoord : ∀ x : ℝ, (e x).val 0 = x)
    {a b : ℝ} (c : PiecewiseC1Curve S a b) : |c b - c a| ≤ length g c := by
  have hp (x : ℝ) : x ∈ e.source := by rw [hsource]; exact mem_univ _
  have h := LocalCurveTrapping.coordinate_displacement_le_length g ⟨e, he⟩
    (by norm_num : (0 : ℝ) ≤ 1) c c.ordered le_rfl
    (fun t _ => hp (c t)) (fun t ht v => by
      rw [tangentNorm_coordinate g hg e he hcoord (c t) (hp (c t)) v, one_mul])
  simpa only [norm_one, Pi.sub_apply, hcoord, one_mul] using h

/-- The global affine segment is an actual curve of the upstream type and
attains the displacement lower bound. -/
theorem affine_segment (g : RiemannianMetric S)
    (hg : ∀ (x : ℝ) (v w : TangentSpace S x), pairing g x v w =
      scalarDerivative S (fun y : ℝ => y) x v * scalarDerivative S (fun y : ℝ => y) x w)
    (e : ModelChart 1 .euclidean ℝ) (he : e ∈ S.smoothStructure.val)
    (hsource : e.source = univ) (hcoord : ∀ x : ℝ, (e x).val 0 = x)
    (x y : ℝ) :
    ∃ c : PiecewiseC1Curve S 0 1, c 0 = x ∧ c 1 = y ∧ length g c = |x - y| := by
  let f : ℝ → ℝ := AffineMap.lineMap x y
  have hp (z : ℝ) : z ∈ e.source := by rw [hsource]; exact mem_univ _
  have hcoords (z : ℝ) : (e z).val = fun _ => z := by
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    simpa only [hi] using hcoord z
  have hf : ContDiff ℝ 1 f := AffineMap.contDiff_lineMap x y
  have hfc : ContDiff ℝ 1 (fun t => (e (f t)).val) := by
    simp only [hcoords]
    exact contDiff_pi.mpr (fun _ => hf)
  have hd (t : ℝ) : HasDerivAt (fun s => (e (f s)).val) (fun _ => y - x) t := by
    simp only [hcoords]
    exact hasDerivAt_pi.mpr (fun _ => AffineMap.hasDerivAt_lineMap)
  let c : PiecewiseC1Curve S 0 1 := {
    ordered := by norm_num
    toFun := f
    continuousOn := hf.continuous.continuousOn
    pieces := 1
    node := ![0, 1]
    monotone_node := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> norm_num at *
    first_node := rfl
    last_node := rfl
    regular := by
      intro i t ht
      refine ⟨e, he, hp (f t), (fun s => (e (f s)).val), hfc.contDiffAt, rfl, ?_⟩
      exact EventuallyEq.rfl }
  have hv (t : ℝ) : velocity S f t =
      ((tangentStructure S).fiberCoordinates.equiv e he (f t) (hp (f t))).symm
        (fun _ => y - x) := by
    apply PiecewiseCurves.velocity_eq
    refine ⟨hf.continuous.continuousAt, e, he, hp (f t), ?_⟩
    simpa only [LinearEquiv.apply_symm_apply] using hd t
  have hspeed (t : ℝ) : speed g c t = |y - x| := by
    change tangentNorm g (f t) (velocity S f t) = _
    rw [tangentNorm_coordinate g hg e he hcoord (f t) (hp (f t)),
      hv, LinearEquiv.apply_symm_apply, norm_one]
  refine ⟨c, AffineMap.lineMap_apply_zero x y, AffineMap.lineMap_apply_one x y, ?_⟩
  change (∫ t in (0 : ℝ)..1, speed g c t) = _
  simp only [hspeed, intervalIntegral.integral_const, sub_zero, one_smul, abs_sub_comm]

/-- All three original conclusions, universally quantified over the specified
standard-coordinate smooth structures and metrics. -/
theorem euclidean_line_distance :
    P202Specs.Geometry.EuclideanLineDistance.euclidean_line_distanceType := by
  intro S g hchart hg
  obtain ⟨e, he, hsource, _htarget, hcoord⟩ := hchart
  have hformula (x y : ℝ) : lengthDistance g x y = |x - y| := by
    obtain ⟨c, hc0, hc1, hlen⟩ := affine_segment g hg e he hsource hcoord x y
    have hmem : |x - y| ∈ pathLengths g x y := ⟨0, 1, c, hc0, hc1, hlen.symm⟩
    have hlower : ∀ L ∈ pathLengths g x y, |x - y| ≤ L := by
      rintro L ⟨a, b, d, hd0, hd1, rfl⟩
      have h := displacement_le_length g hg e he hsource hcoord d
      simpa only [hd0, hd1, abs_sub_comm] using h
    exact le_antisymm (csInf_le ⟨|x - y|, hlower⟩ hmem)
      (le_csInf ⟨|x - y|, hmem⟩ hlower)
  refine ⟨hformula, ?_, ?_⟩
  · refine ⟨inferInstance, rfl, ?_, inferInstance⟩
    intro x y
    change dist x y = lengthDistance g x y
    rw [hformula, Real.dist_eq]
  · intro A hA
    refine ⟨0, A + 1, ?_⟩
    rw [hformula, zero_sub, abs_neg, abs_of_pos (by linarith : 0 < A + 1)]
    linarith

end P202.Geometry.EuclideanLineDistance
