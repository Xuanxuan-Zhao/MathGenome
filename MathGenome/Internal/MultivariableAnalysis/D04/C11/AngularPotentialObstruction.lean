import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C11.AngularPotentialObstruction
import MathGenome.Internal.MultivariableAnalysis.D04.C11.LocalAndStarShapedPotentials
import MathGenome.Internal.MultivariableAnalysis.D04.C13.ClosedAndExactForms
import MathGenome.Internal.MultivariableAnalysis.D04.C09.CircleMultiplicity
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

noncomputable section
open Set Filter Topology
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
namespace D04.C11.AngularPotentialObstruction
open D04 D04.Dictionary D04.C09
open D04.C09.CircleMultiplicity

abbrev angularForm := Specs.D04.C11.AngularPotentialObstruction.Model.angularForm
abbrev angularSlit := Specs.D04.C11.AngularPotentialObstruction.Model.angularSlit
abbrev slitAngle := Specs.D04.C11.AngularPotentialObstruction.Model.slitAngle
abbrev IsAngleBranch := Specs.D04.C11.AngularPotentialObstruction.Model.IsAngleBranch

theorem angularForm_apply (x : E 2) (v : Fin 1 → E 2) :
    angularForm x v = (-x 1 * v 0 0 + x 0 * v 0 1) / ((x 0)^2 + (x 1)^2) := by
  change inner ℝ (angularField x) (v 0) = _
  rw [inner_coordinates]
  simp only [Fin.sum_univ_two, angularField,
    Specs.D04.C09.CircleMultiplicity.Model.angularField, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem angularField_smooth (r : ℕ) : CrOn r puncturedPlane angularField := by
  apply (crOn_iff_contDiffOn r puncturedPlane angularField puncturedPlane_open).mpr
  intro x hx
  apply ContDiffAt.contDiffWithinAt
  apply contDiffAt_euclidean.mpr
  have h0 := (contDiff_piLp_apply 2 : ContDiff ℝ r (fun x : E 2 => x (0 : Fin 2))).contDiffAt (x := x)
  have h1 := (contDiff_piLp_apply 2 : ContDiff ℝ r (fun x : E 2 => x (1 : Fin 2))).contDiffAt (x := x)
  have hq := (h0.pow 2).add (h1.pow 2)
  intro i
  fin_cases i
  · exact h1.neg.div hq (denominator_ne_zero x hx)
  · exact h0.div hq (denominator_ne_zero x hx)

lemma angularField_symmetricPartials : D04.C11.SymmetricPartials puncturedPlane angularField := by
  intro x hx i j
  fin_cases i <;> fin_cases j
  · rfl
  · exact angularField_cross_partials x hx
  · exact (angularField_cross_partials x hx).symm
  · rfl

theorem angularField_symmetric (x : E 2) (hx : x ∈ puncturedPlane) :
    (jacobian angularField x).IsSymm :=
  (D04.C11.symmetry_iff_jacobian puncturedPlane angularField puncturedPlane_open
    (angularField_smooth 1)).mp angularField_symmetricPartials x hx

theorem angularForm_closed : IsClosedForm puncturedPlane angularForm :=
  ⟨alpha_isCr 1 _ _ puncturedPlane_open (angularField_smooth 1),
    (exterior_alpha_closed_iff _ _ puncturedPlane_open (angularField_smooth 1)).mpr
      angularField_symmetric⟩

theorem angularField_local_potential : ∀ x ∈ puncturedPlane,
    ∃ r > 0, Metric.ball x r ⊆ puncturedPlane ∧ HasPotential (Metric.ball x r) angularField :=
  D04.C11.local_potential _ _ puncturedPlane_open (angularField_smooth 1)
    angularField_symmetricPartials


/-- The local potentials also give local C¹ zero-form primitives. -/
theorem angularForm_locally_exact : ∀ x ∈ puncturedPlane,
    ∃ r > 0, Metric.ball x r ⊆ puncturedPlane ∧ IsExactForm (Metric.ball x r) angularForm := by
  intro x hx
  obtain ⟨r, hr, hsub, f, hf⟩ := angularField_local_potential x hx
  refine ⟨r, hr, hsub, (fun y => scalarCovector (V := E 2) (f y)),
    (isCrForm_zero_iff (some 1) _ f).mpr ⟨Metric.isOpen_ball, hf.1⟩, ?_⟩
  intro y hy
  change alpha angularField y = exteriorDerivative (fun z => scalarCovector (V := E 2) (f z)) y
  rw [differential_alpha_gradient _ f Metric.isOpen_ball hf.1 y hy]
  ext v
  rw [alpha_apply, alpha_apply]
  exact congrArg (fun w : E 2 => inner ℝ w (v 0)) (hf.2 hy).symm

theorem angular_circle_integral (d : PiecewiseC1Data (circlePath 1)) :
    ∃ h : WorkIntegrable d angularField, workLineIntegral d angularField h = 2 * Real.pi := by
  simpa using circle_work_integral 1 d

theorem angularForm_circle_integral (d : PiecewiseC1Data (circlePath 1)) :
    ∃ h : OneFormIntegrable d angularForm, oneFormIntegral d angularForm h = 2 * Real.pi :=
  angular_circle_integral d

theorem angularField_no_global_potential : ¬ HasPotential puncturedPlane angularField := by
  rintro ⟨f, hf, hg⟩
  exact angularField_no_potential ⟨f, hf, hg⟩

theorem angularForm_not_exact : ¬ IsExactForm puncturedPlane angularForm := by
  rintro ⟨η, hη, hd⟩
  let f : E 2 → ℝ := fun x => scalarCovector.symm (η x)
  have hrepr : (fun x => scalarCovector (V := E 2) (f x)) = η := by
    funext x
    exact scalarCovector.apply_symm_apply (η x)
  have hf : CrOn 1 puncturedPlane f :=
    ((isCrForm_zero_iff (some 1) puncturedPlane f).mp (hrepr ▸ hη)).2
  apply angularField_no_global_potential
  refine ⟨f, hf, ?_⟩
  intro x hx
  apply ext_inner_right ℝ
  intro v
  have he := hd hx
  rw [← hrepr] at he
  change alpha angularField x = exteriorDerivative (fun y => scalarCovector (V := E 2) (f y)) x at he
  rw [differential_alpha_gradient puncturedPlane f puncturedPlane_open hf x hx] at he
  exact (congrArg (fun A : Covector (E 2) 1 => A (fun _ => v)) he).symm

/-- The existing real coordinate equivalence, regarded as a continuous map. -/
def planeComplex : E 2 →L[ℝ] ℂ :=
  complexCoordinates.symm.toLinearMap.toContinuousLinearMap

@[simp] lemma planeComplex_re (x : E 2) : (planeComplex x).re = x 0 := rfl
@[simp] lemma planeComplex_im (x : E 2) : (planeComplex x).im = x 1 := rfl

lemma planeComplex_ne_zero (x : E 2) (hx : x ∈ puncturedPlane) : planeComplex x ≠ 0 := by
  intro h
  apply hx
  exact complexCoordinates.symm.injective h

lemma rotation_cancel (α : ℝ) :
    Complex.exp ((α : ℂ) * Complex.I) * Complex.exp (-(α : ℂ) * Complex.I) = 1 := by
  rw [← Complex.exp_add, ← add_mul, add_neg_cancel, zero_mul, Complex.exp_zero]

theorem angularSlit_open (α : ℝ) : IsOpen (angularSlit α) :=
  Complex.isOpen_slitPlane.preimage
    ((continuous_const.mul planeComplex.continuous) : Continuous
      (fun x => Complex.exp (-(α : ℂ) * Complex.I) * planeComplex x))

theorem angularSlit_subset (α : ℝ) : angularSlit α ⊆ puncturedPlane := by
  intro x hx hz
  have hh := Complex.slitPlane_ne_zero hx
  apply hh
  change Complex.exp (-(α : ℂ) * Complex.I) * planeComplex x = 0
  rw [hz, map_zero, mul_zero]

lemma slitAngle_contDiffAt (α : ℝ) (x : E 2) (hx : x ∈ angularSlit α) (r : ℕ) :
    ContDiffAt ℝ r (slitAngle α) x := by
  have hrot : ContDiff ℝ r (fun x : E 2 =>
      Complex.exp (-(α : ℂ) * Complex.I) * planeComplex x) :=
    contDiff_const.mul planeComplex.contDiff
  have hl := ((Complex.contDiffAt_log hx (n := r)).restrict_scalars ℝ).comp x hrot.contDiffAt
  have hi := Complex.imCLM.contDiff.contDiffAt.comp x hl
  change ContDiffAt ℝ r (fun y : E 2 => α +
    Complex.arg (Complex.exp (-(α : ℂ) * Complex.I) * planeComplex y)) x
  simpa only [Function.comp_def, Complex.imCLM_apply, Complex.log_im] using!
    (contDiffAt_const (c := α)).add hi

lemma slitAngle_hasFDerivAt (α : ℝ) (x : E 2) (hx : x ∈ angularSlit α) :
    HasFDerivAt (slitAngle α)
      (Complex.imCLM.comp ((planeComplex x)⁻¹ • planeComplex)) x := by
  let c : ℂ := Complex.exp (-(α : ℂ) * Complex.I)
  have hc : c ≠ 0 := Complex.exp_ne_zero _
  have hrot : HasFDerivAt (fun y : E 2 => c * planeComplex y) (c • planeComplex) x := by
    exact (c • planeComplex).hasFDerivAt
  have hl := (Complex.hasStrictFDerivAt_log_real hx).hasFDerivAt.comp x hrot
  have hi := Complex.imCLM.hasFDerivAt.comp x hl
  have he : (Complex.imCLM.comp
      (((c * planeComplex x)⁻¹ • (1 : ℂ →L[ℝ] ℂ)).comp (c • planeComplex))) =
      Complex.imCLM.comp ((planeComplex x)⁻¹ • planeComplex) := by
    ext v
    simp only [ContinuousLinearMap.comp_apply, smul_apply,
      one_apply_eq_self, smul_eq_mul]
    rw [mul_inv_rev]
    congr 1
    field_simp
  change HasFDerivAt (fun y => (Complex.log (c * planeComplex y)).im)
    (Complex.imCLM.comp (((c * planeComplex x)⁻¹ • (1 : ℂ →L[ℝ] ℂ)).comp
      (c • planeComplex))) x at hi
  rw [he] at hi
  simpa only [Function.comp_def, Complex.log_im] using! hi.const_add α

lemma inverse_im_work (x v : E 2) :
    ((planeComplex x)⁻¹ * planeComplex v).im = inner ℝ (angularField x) v := by
  rw [inner_coordinates]
  simp only [Complex.mul_im, Complex.inv_re, Complex.inv_im, planeComplex_re, planeComplex_im,
    Complex.normSq_apply, Fin.sum_univ_two, angularField,
    Specs.D04.C09.CircleMultiplicity.Model.angularField, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem slitAngle_potential (α : ℝ) :
    IsPotential (angularSlit α) angularField (slitAngle α) := by
  refine ⟨(crOn_iff_contDiffOn 1 _ _ (angularSlit_open α)).mpr
    (fun x hx => (slitAngle_contDiffAt α x hx 1).contDiffWithinAt), ?_⟩
  intro x hx
  apply ext_inner_right ℝ
  intro v
  change inner ℝ (scalarGradient (slitAngle α) x) v = _
  rw [← scalarGradient_represents]
  change (fderiv ℝ (slitAngle α) x) v = _
  rw [(slitAngle_hasFDerivAt α x hx).fderiv]
  exact inverse_im_work x v

theorem angularSlit_ray (α : ℝ) (x : E 2) :
    x ∉ angularSlit α ↔
      ∃ r : ℝ, 0 ≤ r ∧ complexCoordinates.symm x = -(r : ℂ) * Complex.exp ((α : ℂ) * Complex.I) := by
  let z : ℂ := planeComplex x
  change Complex.exp (-(α : ℂ) * Complex.I) * z ∉ Complex.slitPlane ↔ _
  let c := Complex.exp ((α : ℂ) * Complex.I)
  let d := Complex.exp (-(α : ℂ) * Complex.I)
  have hcd : c*d = 1 := rotation_cancel α
  have hdc : d*c = 1 := by rw [mul_comm]; exact hcd
  constructor
  · intro hz
    have hw : (d*z).re ≤ 0 ∧ (d*z).im = 0 := by
      simpa only [Complex.mem_slitPlane_iff, not_or, not_lt, not_not] using hz
    refine ⟨-(d*z).re, neg_nonneg.mpr hw.1, ?_⟩
    have he : d*z = ((d*z).re : ℂ) := by
      apply Complex.ext
      · rfl
      · simpa using hw.2
    change z = -((-(d*z).re : ℝ) : ℂ) * c
    calc
      z = c*(d*z) := by rw [← mul_assoc, hcd, one_mul]
      _ = c*((d*z).re : ℂ) := congrArg (c * ·) he
      _ = -((-(d*z).re : ℝ) : ℂ) * c := by push_cast; ring
  · rintro ⟨r, hr, hz⟩
    change z = -(r : ℂ)*c at hz
    change d*z ∉ Complex.slitPlane
    rw [hz]
    have he : d * (-(r : ℂ) * c) = -(r : ℂ) := by
      calc
        _ = -(r : ℂ)*(d*c) := by ring
        _ = -(r : ℂ) := by rw [hdc, mul_one]
    rw [he]
    simpa using not_lt.mpr (neg_nonpos.mpr hr)


theorem slitAngle_branch (α : ℝ) : IsAngleBranch (angularSlit α) (slitAngle α) := by
  refine ⟨fun x hx => (slitAngle_contDiffAt α x hx 1).continuousAt.continuousWithinAt, ?_⟩
  intro x _
  let z := planeComplex x
  let c := Complex.exp ((α : ℂ)*Complex.I)
  let d := Complex.exp (-(α : ℂ)*Complex.I)
  have hcd : c*d = 1 := rotation_cancel α
  have hn : ‖d*z‖ = ‖z‖ := by
    simp [d, Complex.norm_exp, Complex.mul_re]
  change (‖z‖ : ℂ) * Complex.exp (((α + Complex.arg (d*z) : ℝ) : ℂ) * Complex.I) = z
  rw [Complex.ofReal_add, add_mul, Complex.exp_add]
  change (‖z‖ : ℂ) * (c * Complex.exp ((Complex.arg (d*z) : ℂ)*Complex.I)) = z
  calc
    _ = c*((‖d*z‖ : ℂ)*Complex.exp ((Complex.arg (d*z) : ℂ)*Complex.I)) := by rw [hn]; ring
    _ = c*(d*z) := by rw [Complex.norm_mul_exp_arg_mul_I]
    _ = z := by rw [← mul_assoc,hcd,one_mul]

/-- Continuity alone makes two lifts of the same argument differ locally
by a constant. Local injectivity of exp in a strip proves this directly. -/
lemma angle_branches_eventuallyEq {U : Set (E 2)} (hU : IsOpen U)
    (hsub : U ⊆ puncturedPlane) (a b : E 2 → ℝ)
    (ha : IsAngleBranch U a) (hb : IsAngleBranch U b) (x : E 2) (hx : x ∈ U) :
    a =ᶠ[𝓝 x] fun y => b y + (a x - b x) := by
  have he (y : E 2) (hy : y ∈ U) :
      Complex.exp ((a y : ℂ)*Complex.I) = Complex.exp ((b y : ℂ)*Complex.I) := by
    apply mul_left_cancel₀ (show (‖planeComplex y‖ : ℂ) ≠ 0 from
      Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (planeComplex_ne_zero y (hsub hy))))
    exact (ha.2 y hy).trans (hb.2 y hy).symm
  let g : E 2 → ℝ := fun y => a y - b y
  have hg : ContinuousAt g x := (ha.1 x hx).continuousAt (hU.mem_nhds hx) |>.sub
    ((hb.1 x hx).continuousAt (hU.mem_nhds hx))
  have hzero : g x - g x ∈ Ioo (-Real.pi) Real.pi := by
    simpa using (show -Real.pi < (0 : ℝ) ∧ (0 : ℝ) < Real.pi by
      constructor <;> linarith [Real.pi_pos])
  have hnear := (hg.sub continuousAt_const).preimage_mem_nhds (Ioo_mem_nhds hzero.1 hzero.2)
  have hgexp (y : E 2) (hy : y ∈ U) : Complex.exp ((g y : ℂ) * Complex.I) = 1 := by
    simp only [g, Complex.ofReal_sub, sub_mul, Complex.exp_sub]
    rw [he y hy, div_self (Complex.exp_ne_zero _)]
  filter_upwards [hU.mem_nhds hx, hnear] with y hy hn
  have heq : Complex.exp (((g y - g x : ℝ) : ℂ) * Complex.I) = Complex.exp 0 := by
    rw [Complex.ofReal_sub, sub_mul, Complex.exp_sub, hgexp y hy, hgexp x hx]
    simp
  have hz := Complex.exp_inj_of_neg_pi_lt_of_le_pi
    (x := ((g y - g x : ℝ) : ℂ) * Complex.I) (y := 0)
    (by simpa using hn.1) (by simpa using hn.2.le)
    (by simpa using neg_neg_of_pos Real.pi_pos) (by simpa using Real.pi_pos.le) heq
  have hz' : g y - g x = 0 := by simpa using congrArg Complex.im hz
  dsimp [g] at hz'
  linarith

theorem continuous_angle_branch_potential (α : ℝ) (a : E 2 → ℝ)
    (ha : IsAngleBranch (angularSlit α) a) : IsPotential (angularSlit α) angularField a := by
  have he (x : E 2) (hx : x ∈ angularSlit α) := angle_branches_eventuallyEq
    (angularSlit_open α) (angularSlit_subset α) a (slitAngle α) ha (slitAngle_branch α) x hx
  refine ⟨(crOn_iff_contDiffOn 1 _ _ (angularSlit_open α)).mpr ?_, ?_⟩
  · intro x hx
    exact (((slitAngle_contDiffAt α x hx 1).add contDiffAt_const).congr_of_eventuallyEq
      (he x hx)).contDiffWithinAt
  · intro x hx
    have hd := (he x hx).fderiv_eq (𝕜 := ℝ)
    have hc : fderiv ℝ (fun y => slitAngle α y + (a x - slitAngle α x)) x =
        fderiv ℝ (slitAngle α) x := fderiv_add_const _
    change (InnerProductSpace.toDual ℝ (E 2)).symm (fderiv ℝ a x) = angularField x
    rw [hd, hc]
    exact (slitAngle_potential α).2 hx

end D04.C11.AngularPotentialObstruction
