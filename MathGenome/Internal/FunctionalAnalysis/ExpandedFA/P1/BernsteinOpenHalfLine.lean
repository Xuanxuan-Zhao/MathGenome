import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.BernsteinOpenHalfLine
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.Bernstein
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith

noncomputable section
namespace ExpandedFA.P1.BernsteinOpenHalfLine
open Set MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal

@[simp] theorem realExtension_positive (f : OpenFunction) (t : ℝ) (ht : 0 < t) :
    realExtension f t = (f ⟨t, ht⟩ : ℝ) := dite_eq_left ht

@[simp] theorem advance_val (t : PositiveTime) (h : ℝ≥0) :
    (advance t h).val = t.val + h := rfl

@[simp] theorem advance_zero (t : PositiveTime) : advance t 0 = t := by
  apply Subtype.ext
  simp

theorem advance_advance (t : PositiveTime) (h k : ℝ≥0) :
    advance (advance t h) k = advance t (h + k) := by
  apply Subtype.ext
  simp [add_assoc]

/-- The shift fed to the accepted closed-half-line theorem. -/
def shiftedFunction (f : OpenFunction) (a : PositiveTime) : Bernstein.FunctionSpace :=
  fun t => f (advance a t)

theorem shifted_difference (hs : List ℝ≥0) (f : OpenFunction) (a : PositiveTime)
    (t : ℝ≥0) :
    Bernstein.alternatingDifference hs (shiftedFunction f a) t =
      openDifference hs f (advance a t) := by
  induction hs generalizing t with
  | nil => rfl
  | cons h hs ih =>
    simp only [Bernstein.difference_cons, openDifference, ih, advance_advance]

theorem shifted_completelyMonotone (f : OpenFunction) (hf : FiniteDifferenceCondition f)
    (a : PositiveTime) : Bernstein.CompletelyMonotone (shiftedFunction f a) := by
  intro hs hh t
  rw [shifted_difference]
  exact hf hs hh _

theorem open_antitone (f : OpenFunction) (hf : FiniteDifferenceCondition f) :
    Antitone f := by
  intro t u htu
  by_cases heq : t = u
  · simp [heq]
  · have hlt : t.val < u.val := lt_of_le_of_ne htu (fun h => heq (Subtype.ext h))
    let h : ℝ≥0 := ⟨u.val - t.val, sub_nonneg.mpr htu⟩
    have hh : 0 < h := sub_pos.mpr hlt
    have hadv : advance t h = u := Subtype.ext (by change t.val + (u.val - t.val) = u.val; ring)
    have hd := hf [h] (by simpa using hh) t
    change 0 ≤ (f t : ℝ) - (f (advance t h) : ℝ) at hd
    rw [hadv] at hd
    exact_mod_cast (sub_nonneg.mp hd)

/-- On every positive time, the arbitrary-measure Laplace transform is an MGF
of the nonpositive rate variable. The MGF API has no finite-measure premise. -/
theorem laplace_eq_mgf (ν : Measure ℝ≥0) :
    openLaplaceTransform ν = mgf (fun r : ℝ≥0 => -(r : ℝ)) ν := by
  funext t
  simp only [openLaplaceTransform, openKernel, mgf]
  congr 1
  funext r
  congr 1
  ring

theorem positive_mem_integrableExpSet_interior (ν : Measure ℝ≥0)
    (hi : ∀ t : ℝ, 0 < t → Integrable (openKernel t) ν) {t : ℝ} (ht : 0 < t) :
    t ∈ interior (integrableExpSet (fun r : ℝ≥0 => -(r : ℝ)) ν) := by
  apply interior_mono (s := Ioi (0 : ℝ)) ?_ (by simpa using ht)
  intro u hu
  change Integrable (fun r : ℝ≥0 => Real.exp (u * -(r : ℝ))) ν
  have hh := hi u hu
  change Integrable (fun r : ℝ≥0 => Real.exp (-(r : ℝ) * u)) ν at hh
  simpa only [mul_comm u] using hh

theorem laplace_analytic (ν : Measure ℝ≥0)
    (hi : ∀ t : ℝ, 0 < t → Integrable (openKernel t) ν) :
    AnalyticOnNhd ℝ (openLaplaceTransform ν) (Ioi 0) := by
  rw [laplace_eq_mgf]
  intro t ht
  exact analyticAt_mgf (positive_mem_integrableExpSet_interior ν hi ht)

theorem laplace_iteratedDeriv (ν : Measure ℝ≥0)
    (hi : ∀ t : ℝ, 0 < t → Integrable (openKernel t) ν)
    (m : ℕ) {t : ℝ} (ht : 0 < t) :
    iteratedDeriv m (openLaplaceTransform ν) t =
      ∫ r : ℝ≥0, (-(r : ℝ)) ^ m * openKernel t r ∂ν := by
  rw [laplace_eq_mgf, iteratedDeriv_mgf (positive_mem_integrableExpSet_interior ν hi ht)]
  simp only [openKernel, mul_comm t]

theorem laplace_derivative_sign (ν : Measure ℝ≥0)
    (hi : ∀ t : ℝ, 0 < t → Integrable (openKernel t) ν)
    (m : ℕ) {t : ℝ} (ht : 0 < t) :
    0 ≤ (-1 : ℝ) ^ m * iteratedDeriv m (openLaplaceTransform ν) t := by
  rw [laplace_iteratedDeriv ν hi m ht, ← integral_const_mul]
  apply integral_nonneg
  intro r
  dsimp only
  have hp : (-1 : ℝ) ^ m * (-(r : ℝ)) ^ m = (r : ℝ) ^ m := by
    rw [← mul_pow]
    simp
  rw [← mul_assoc, hp]
  exact mul_nonneg (pow_nonneg r.coe_nonneg m) (Real.exp_pos _).le

theorem represents_smooth (f : OpenFunction) (ν : Measure ℝ≥0) (hν : Represents f ν) :
    SmoothCondition f := by
  have hi : ∀ t : ℝ, 0 < t → Integrable (openKernel t) ν := fun t ht => hν.1 ⟨t, ht⟩
  have heq : EqOn (realExtension f) (openLaplaceTransform ν) (Ioi 0) := by
    intro t ht
    rw [realExtension_positive f t ht]
    exact hν.2 ⟨t, ht⟩
  constructor
  · exact (laplace_analytic ν hi).contDiffOn_of_completeSpace.congr heq
  · intro m t ht
    have hevent : realExtension f =ᶠ[𝓝 t] openLaplaceTransform ν :=
      Filter.eventuallyEq_of_mem (isOpen_Ioi.mem_nhds ht) heq
    rw [hevent.iteratedDeriv_eq m]
    exact laplace_derivative_sign ν hi m ht

/-- Smoothness of ordinary iterated derivatives on the open domain. -/
theorem smooth_iteratedDeriv {g : ℝ → ℝ}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (Ioi 0)) (m : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (iteratedDeriv m g) (Ioi 0) := by
  induction m with
  | zero => simpa only [iteratedDeriv_zero] using hg
  | succ m ih =>
    rw [iteratedDeriv_succ]
    exact ih.deriv_of_isOpen isOpen_Ioi (by simp)

/-- Each signed derivative is decreasing, by the sign of the next derivative. -/
theorem signed_derivative_antitone {g : ℝ → ℝ}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (Ioi 0))
    (hsign : ∀ (m : ℕ) (t : ℝ), 0 < t →
      0 ≤ (-1 : ℝ) ^ m * iteratedDeriv m g t) (m : ℕ) :
    AntitoneOn (fun t => (-1 : ℝ) ^ m * iteratedDeriv m g t) (Ioi 0) := by
  have hd := smooth_iteratedDeriv hg m
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
    ((contDiffOn_const.mul hd).continuousOn)
    ((contDiffOn_const.mul hd).differentiableOn (by simp) |>.mono interior_subset)
  intro x hx
  have hx' : 0 < x := interior_subset hx
  have hdx : DifferentiableAt ℝ (iteratedDeriv m g) x :=
    (hd.contDiffAt (isOpen_Ioi.mem_nhds hx')).differentiableAt (by simp)
  rw [(hdx.hasDerivAt.const_mul ((-1 : ℝ) ^ m)).deriv]
  have heq : (-1 : ℝ) ^ m * deriv (iteratedDeriv m g) x =
      -((-1 : ℝ) ^ (m + 1) * iteratedDeriv (m + 1) g x) := by
    rw [iteratedDeriv_succ, pow_succ]
    ring
  rw [heq]
  exact neg_nonpos.mpr (hsign (m + 1) x hx')

/-- A forward difference preserves smooth complete monotonicity. -/
theorem smooth_difference {g : ℝ → ℝ}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (Ioi 0))
    (hsign : ∀ (m : ℕ) (t : ℝ), 0 < t →
      0 ≤ (-1 : ℝ) ^ m * iteratedDeriv m g t) (h : ℝ≥0) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun t => g t - g (t + h)) (Ioi 0) ∧
    ∀ (m : ℕ) (t : ℝ), 0 < t →
      0 ≤ (-1 : ℝ) ^ m * iteratedDeriv m (fun t => g t - g (t + h)) t := by
  have hshift : ContDiffOn ℝ (⊤ : ℕ∞) (fun t => g (t + h)) (Ioi 0) :=
    hg.comp (contDiffOn_id.add contDiffOn_const)
      (fun x hx => add_pos_of_pos_of_nonneg hx h.coe_nonneg)
  refine ⟨hg.sub hshift, fun m t ht => ?_⟩
  rw [iteratedDeriv_fun_sub
    ((hg.contDiffAt (isOpen_Ioi.mem_nhds ht)).of_le (by simp))
    ((hshift.contDiffAt (isOpen_Ioi.mem_nhds ht)).of_le (by simp)),
    iteratedDeriv_comp_add_const]
  rw [mul_sub]
  exact sub_nonneg.mpr (signed_derivative_antitone hg hsign m ht
    (add_pos_of_pos_of_nonneg ht h.coe_nonneg) (le_add_of_nonneg_right h.coe_nonneg))

/-- A real-valued version used only inside the calculus argument. -/
def realDifference : List ℝ≥0 → (ℝ → ℝ) → ℝ → ℝ
  | [], g => g
  | h :: hs, g => fun t => realDifference hs g t - realDifference hs g (t + h)

theorem realDifference_smooth_signs {g : ℝ → ℝ}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (Ioi 0))
    (hsign : ∀ (m : ℕ) (t : ℝ), 0 < t →
      0 ≤ (-1 : ℝ) ^ m * iteratedDeriv m g t) (hs : List ℝ≥0) :
    ContDiffOn ℝ (⊤ : ℕ∞) (realDifference hs g) (Ioi 0) ∧
    ∀ (m : ℕ) (t : ℝ), 0 < t →
      0 ≤ (-1 : ℝ) ^ m * iteratedDeriv m (realDifference hs g) t := by
  induction hs with
  | nil => exact ⟨hg, hsign⟩
  | cons h hs ih => exact smooth_difference ih.1 ih.2 h

theorem realDifference_extension (hs : List ℝ≥0) (f : OpenFunction) (t : PositiveTime) :
    realDifference hs (realExtension f) t.val = openDifference hs f t := by
  induction hs generalizing t with
  | nil => exact realExtension_positive f t.val t.property
  | cons h hs ih =>
    change realDifference hs (realExtension f) t.val -
      realDifference hs (realExtension f) (advance t h).val = _
    rw [ih, ih]
    rfl

/-- Mean-value arguments suffice; the source's rectangle integral is not needed. -/
theorem smooth_finiteDifferences (f : OpenFunction) (hf : SmoothCondition f) :
    FiniteDifferenceCondition f := by
  intro hs _ t
  have h := (realDifference_smooth_signs hf.1 hf.2 hs).2 0 t.val t.property
  simpa only [pow_zero, iteratedDeriv_zero, one_mul, realDifference_extension] using h

theorem represents_finiteDifferences (f : OpenFunction) (ν : Measure ℝ≥0)
    (hν : Represents f ν) : FiniteDifferenceCondition f :=
  smooth_finiteDifferences f (represents_smooth f ν hν)

/-- The compactified kernel is continuous in time away from time zero,
including at the infinite rate. -/
theorem compactKernel_continuousAt {t : ℝ≥0} (ht : 0 < t) (r : ℝ≥0∞) :
    ContinuousAt (fun u : ℝ≥0 => Bernstein.laplaceKernel u r) t := by
  induction r using ENNReal.recTopCoe with
  | coe r =>
    simp only [Bernstein.kernel_interpretation.1]
    exact (Real.continuous_exp.comp (continuous_const.mul NNReal.continuous_coe)).continuousAt
  | top =>
    have heq : (fun u : ℝ≥0 => Bernstein.laplaceKernel u ∞) =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [isOpen_Ioi.mem_nhds ht] with u hu
      simp [Bernstein.kernel_interpretation.2, ne_of_gt (show 0 < u from hu)]
    exact continuousAt_const.congr_of_eventuallyEq heq

theorem compactTransform_continuousAt (μ : Measure ℝ≥0∞) [IsFiniteMeasure μ]
    {t : ℝ≥0} (ht : 0 < t) : ContinuousAt (Bernstein.laplaceTransform μ) t := by
  apply continuousAt_of_dominated
    (Eventually.of_forall fun u => (Bernstein.kernel_continuous u).aestronglyMeasurable)
    (Eventually.of_forall fun u => Eventually.of_forall fun r => Bernstein.kernel_norm_le_one u r)
    (integrable_const (1 : ℝ))
  exact Eventually.of_forall (compactKernel_continuousAt ht)

/-- Interior continuity is obtained from the accepted compactified theorem,
using a smaller positive shift. No continuity assumption is added to `f`. -/
theorem shifted_right_continuous (f : OpenFunction) (hf : FiniteDifferenceCondition f)
    (a : PositiveTime) :
    Tendsto (shiftedFunction f a) (𝓝[>] (0 : ℝ≥0)) (𝓝 (shiftedFunction f a 0)) := by
  let b : PositiveTime := ⟨a.val / 2, by change 0 < a.val / 2; exact half_pos a.property⟩
  let c : ℝ≥0 := ⟨a.val / 2, (half_pos a.property).le⟩
  obtain ⟨μ, hμ, heq⟩ := Bernstein.representation_exists (shiftedFunction f b)
    (shifted_completelyMonotone f hf b)
  let := hμ
  have hc : 0 < c := by change 0 < a.val / 2; exact half_pos a.property
  have hid : ∀ t : ℝ≥0, advance b (t + c) = advance a t := by
    intro t
    apply Subtype.ext
    change a.val / 2 + ((t : ℝ) + a.val / 2) = a.val + t
    ring
  have hrepr : shiftedFunction f a = fun t : ℝ≥0 => Bernstein.laplaceTransform μ (t + c) := by
    funext t
    rw [← heq]
    simp only [shiftedFunction, hid]
  have hcont : ContinuousAt (shiftedFunction f a) 0 := by
    rw [hrepr]
    have hc' : ContinuousAt (Bernstein.laplaceTransform μ) ((0 : ℝ≥0) + c) := by
      simpa only [zero_add] using compactTransform_continuousAt μ hc
    exact hc'.comp (f := fun t : ℝ≥0 => t + c)
      ((continuous_id.add continuous_const).continuousAt)
  exact hcont.tendsto.mono_left nhdsWithin_le_nhds

theorem shifted_finite_representation (f : OpenFunction) (hf : FiniteDifferenceCondition f)
    (a : PositiveTime) :
    ∃! μ : Measure ℝ≥0, IsFiniteMeasure μ ∧ shiftedFunction f a = Bernstein.finiteLaplaceTransform μ :=
  (Bernstein.classical_representation _ (shifted_completelyMonotone f hf a)).mp
    (shifted_right_continuous f hf a)

/-- Exponential weighting, allowing either sign of the real exponent. -/
def exponentialWeight (a : ℝ) (r : ℝ≥0) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (a * r))

def exponentialTilt (μ : Measure ℝ≥0) (a : ℝ) : Measure ℝ≥0 :=
  μ.withDensity (exponentialWeight a)

theorem weight_measurable (a : ℝ) : Measurable (exponentialWeight a) := by
  exact (Real.continuous_exp.comp (continuous_const.mul NNReal.continuous_coe)).measurable.ennreal_ofReal

@[simp] theorem tilt_zero (μ : Measure ℝ≥0) : exponentialTilt μ 0 = μ := by
  change μ.withDensity (fun r : ℝ≥0 => ENNReal.ofReal (Real.exp (0 * r))) = μ
  simp

theorem tilt_add (μ : Measure ℝ≥0) (a b : ℝ) :
    exponentialTilt (exponentialTilt μ a) b = exponentialTilt μ (a + b) := by
  rw [exponentialTilt, exponentialTilt, ← withDensity_mul μ
    (weight_measurable a) (weight_measurable b)]
  congr 1
  funext r
  simp only [Pi.mul_apply, exponentialWeight, add_mul, Real.exp_add]
  exact (ENNReal.ofReal_mul (Real.exp_pos _).le).symm

@[simp] theorem tilt_cancel (μ : Measure ℝ≥0) (a : ℝ) :
    exponentialTilt (exponentialTilt μ a) (-a) = μ := by
  rw [tilt_add, add_neg_cancel, tilt_zero]

theorem tilt_injective (a : ℝ) : Function.Injective (fun μ : Measure ℝ≥0 => exponentialTilt μ a) := by
  intro μ ν h
  have := congrArg (fun η => exponentialTilt η (-a)) h
  simpa only [tilt_cancel] using this

theorem weight_toReal (a : ℝ) (r : ℝ≥0) :
    (exponentialWeight a r).toReal = Real.exp (a * r) :=
  ENNReal.toReal_ofReal (Real.exp_pos _).le

theorem weight_mul_kernel (a t : ℝ) (r : ℝ≥0) :
    (exponentialWeight a r).toReal * openKernel t r = openKernel (t - a) r := by
  rw [weight_toReal, openKernel, ← Real.exp_add, openKernel]
  congr 1
  ring

theorem tilt_integral (μ : Measure ℝ≥0) (a t : ℝ) :
    openLaplaceTransform (exponentialTilt μ a) t = openLaplaceTransform μ (t - a) := by
  rw [openLaplaceTransform, exponentialTilt,
    integral_withDensity_eq_integral_toReal_smul (weight_measurable a)
      (Eventually.of_forall fun r => ENNReal.ofReal_lt_top)]
  simp only [smul_eq_mul, weight_mul_kernel, openLaplaceTransform]

theorem tilt_integrable_iff (μ : Measure ℝ≥0) (a t : ℝ) :
    Integrable (openKernel t) (exponentialTilt μ a) ↔ Integrable (openKernel (t - a)) μ := by
  rw [exponentialTilt, integrable_withDensity_iff_integrable_smul' (weight_measurable a)
    (Eventually.of_forall fun r => ENNReal.ofReal_lt_top)]
  simp only [smul_eq_mul, weight_mul_kernel]

theorem kernel_continuous (t : ℝ) : Continuous (openKernel t) :=
  Real.continuous_exp.comp (NNReal.continuous_coe.neg.mul continuous_const)

theorem kernel_integrable_finite (μ : Measure ℝ≥0) [IsFiniteMeasure μ]
    {t : ℝ} (ht : 0 ≤ t) : Integrable (openKernel t) μ := by
  apply (integrable_const (1 : ℝ)).mono' (kernel_continuous t).aestronglyMeasurable
  exact Eventually.of_forall fun r => by
    change ‖Real.exp (-(r : ℝ) * t)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr r.coe_nonneg) ht)

theorem tilt_finite_of_integrable (μ : Measure ℝ≥0) (a : ℝ)
    (hi : Integrable (openKernel (-a)) μ) : IsFiniteMeasure (exponentialTilt μ a) := by
  apply (integrable_const_iff_isFiniteMeasure (one_ne_zero : (1 : ℝ) ≠ 0)).mp
  rw [exponentialTilt, integrable_withDensity_iff_integrable_smul' (weight_measurable a)
    (Eventually.of_forall fun r => ENNReal.ofReal_lt_top)]
  change Integrable (fun r : ℝ≥0 => Real.exp (-(r : ℝ) * -a)) μ at hi
  simpa only [weight_toReal, smul_eq_mul, mul_one, neg_mul_neg, mul_comm a] using hi

/-- Compatibility of finite representatives at two ordered positive shifts. -/
theorem shifted_measures_compatible (f : OpenFunction) (a b : PositiveTime)
    (hab : a.val ≤ b.val) (μ η : Measure ℝ≥0) [IsFiniteMeasure μ] [IsFiniteMeasure η]
    (hμ : shiftedFunction f a = Bernstein.finiteLaplaceTransform μ)
    (hη : shiftedFunction f b = Bernstein.finiteLaplaceTransform η) :
    η = exponentialTilt μ (a.val - b.val) := by
  have hfinite : IsFiniteMeasure (exponentialTilt μ (a.val - b.val)) :=
    tilt_finite_of_integrable μ _ (kernel_integrable_finite μ (by linarith))
  let := hfinite
  apply Bernstein.finiteTransform_injective
  funext t
  change openLaplaceTransform η (t : ℝ) = openLaplaceTransform (exponentialTilt μ _) (t : ℝ)
  rw [tilt_integral]
  let u : ℝ≥0 := ⟨(t : ℝ) - (a.val - b.val), by linarith [t.coe_nonneg]⟩
  have htime : advance b t = advance a u := by
    apply Subtype.ext
    change b.val + t = a.val + ((t : ℝ) - (a.val - b.val))
    ring
  calc
    openLaplaceTransform η (t : ℝ) = (f (advance b t) : ℝ) := (congrFun hη t).symm
    _ = (f (advance a u) : ℝ) := congrArg (fun x => (f x : ℝ)) htime
    _ = openLaplaceTransform μ ((t : ℝ) - (a.val - b.val)) := congrFun hμ u

/-- Removing the shift yields the same, potentially infinite, measure. -/
theorem unweighted_shifted_measures_eq (f : OpenFunction) (a b : PositiveTime)
    (μ η : Measure ℝ≥0) [IsFiniteMeasure μ] [IsFiniteMeasure η]
    (hμ : shiftedFunction f a = Bernstein.finiteLaplaceTransform μ)
    (hη : shiftedFunction f b = Bernstein.finiteLaplaceTransform η) :
    exponentialTilt μ a.val = exponentialTilt η b.val := by
  rcases le_total a.val b.val with hab | hba
  · rw [shifted_measures_compatible f a b hab μ η hμ hη, tilt_add]
    congr 1
    ring
  · rw [shifted_measures_compatible f b a hba η μ hη hμ, tilt_add]
    congr 1
    ring

theorem representation_exists (f : OpenFunction) (hf : FiniteDifferenceCondition f) :
    ∃ ν : Measure ℝ≥0, Represents f ν := by
  let one : PositiveTime := ⟨1, by norm_num⟩
  obtain ⟨μ, ⟨hμ, hrepr⟩, _⟩ := shifted_finite_representation f hf one
  let := hμ
  let ν := exponentialTilt μ 1
  have hlocal (t : PositiveTime) :
      Integrable (openKernel t.val) ν ∧ (f t : ℝ) = openLaplaceTransform ν t.val := by
    let a : PositiveTime := ⟨t.val / 2, by change 0 < t.val / 2; exact half_pos t.property⟩
    let u : ℝ≥0 := ⟨t.val / 2, (half_pos t.property).le⟩
    obtain ⟨η, ⟨hη, hηrepr⟩, _⟩ := shifted_finite_representation f hf a
    let := hη
    have heq : ν = exponentialTilt η a.val :=
      unweighted_shifted_measures_eq f one a μ η hrepr hηrepr
    have htime : advance a u = t := by
      apply Subtype.ext
      change t.val / 2 + t.val / 2 = t.val
      ring
    have hdiff : t.val - a.val = (u : ℝ) := by
      change t.val - t.val / 2 = t.val / 2
      ring
    constructor
    · rw [heq, tilt_integrable_iff, hdiff]
      exact kernel_integrable_finite η u.coe_nonneg
    · rw [heq, tilt_integral, hdiff]
      have hu := congrFun hηrepr u
      change (f (advance a u) : ℝ) = openLaplaceTransform η (u : ℝ) at hu
      rwa [htime] at hu
  exact ⟨ν, (fun t => (hlocal t).1), fun t => (hlocal t).2⟩

/-- Every arbitrary representative becomes a finite representative after tilting. -/
theorem representing_tilt (f : OpenFunction) (ν : Measure ℝ≥0) (hν : Represents f ν)
    (a : PositiveTime) :
    IsFiniteMeasure (exponentialTilt ν (-a.val)) ∧
      shiftedFunction f a = Bernstein.finiteLaplaceTransform (exponentialTilt ν (-a.val)) := by
  constructor
  · apply tilt_finite_of_integrable
    simpa only [neg_neg] using hν.1 a
  · funext t
    change (f (advance a t) : ℝ) = openLaplaceTransform (exponentialTilt ν (-a.val)) (t : ℝ)
    rw [tilt_integral]
    have heq : (advance a t).val = (t : ℝ) - -a.val := by
      simp only [advance_val]
      ring
    rw [← heq]
    exact hν.2 (advance a t)

theorem representation_unique (f : OpenFunction) (μ ν : Measure ℝ≥0)
    (hμ : Represents f μ) (hν : Represents f ν) : μ = ν := by
  let one : PositiveTime := ⟨1, by norm_num⟩
  obtain ⟨hμf, hμeq⟩ := representing_tilt f μ hμ one
  obtain ⟨hνf, hνeq⟩ := representing_tilt f ν hν one
  let := hμf
  let := hνf
  apply tilt_injective (-one.val)
  exact Bernstein.finiteTransform_injective _ _ (hμeq.symm.trans hνeq)

theorem equivalence : Specs.ExpandedFA.P1.BernsteinOpenHalfLine.Equivalence := by
  intro f
  have hr : FiniteDifferenceCondition f ↔ ∃! ν : Measure ℝ≥0, Represents f ν := by
    constructor
    · intro hf
      obtain ⟨ν, hν⟩ := representation_exists f hf
      exact ⟨ν, hν, fun μ hμ => representation_unique f μ ν hμ hν⟩
    · rintro ⟨ν, hν, _⟩
      exact represents_finiteDifferences f ν hν
  refine ⟨⟨?_, smooth_finiteDifferences f⟩, hr⟩
  intro hf
  obtain ⟨ν, hν⟩ := representation_exists f hf
  exact represents_smooth f ν hν

/-- An integrable exponential bounds the measure of every bounded rate interval. -/
theorem local_finiteness : Specs.ExpandedFA.P1.BernsteinOpenHalfLine.LocalFiniteness := by
  intro f ν hν R
  have hi := (hν.1 ⟨1, by norm_num⟩).const_mul (Real.exp (R : ℝ))
  have hnonneg : 0 ≤ᵐ[ν] (fun r : ℝ≥0 => Real.exp (R : ℝ) * openKernel 1 r) :=
    Eventually.of_forall fun r => mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  have hbound : ν (Icc 0 R) ≤ ENNReal.ofReal
      (∫ r : ℝ≥0, Real.exp (R : ℝ) * openKernel 1 r ∂ν) := by
    apply hi.measure_le_integral hnonneg
    intro r hr
    rw [openKernel, ← Real.exp_add]
    apply Real.one_le_exp_iff.mpr
    have hle : (r : ℝ) ≤ (R : ℝ) := hr.2
    linarith
  exact hbound.trans_lt ENNReal.ofReal_lt_top

/-- A nonnegative exponential transform tends to total mass, possibly infinite.
Fatou gives the lower bound on the limit and the bound by one gives the upper
bound; no finite-measure or sigma-finiteness hypothesis is used. -/
theorem laplace_mass_limit (ν : Measure ℝ≥0) :
    Tendsto (fun t : ℝ => ∫⁻ r : ℝ≥0, ENNReal.ofReal (openKernel t r) ∂ν)
      (𝓝[>] (0 : ℝ)) (𝓝 (ν univ)) := by
  let F : ℝ → ℝ≥0 → ℝ≥0∞ := fun t r => ENNReal.ofReal (openKernel t r)
  have hlim (r : ℝ≥0) : Tendsto (fun t => F t r) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hc : Continuous (fun t : ℝ => Real.exp (-(r : ℝ) * t)) := by fun_prop
    simpa only [F, openKernel, mul_zero, Real.exp_zero, ENNReal.ofReal_one] using
      (ENNReal.tendsto_ofReal ((hc.continuousAt (x := 0)).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))))
  have hlower : ν univ ≤ liminf (fun t => ∫⁻ r, F t r ∂ν) (𝓝[>] (0 : ℝ)) := by
    have hfatou := lintegral_liminf_le (μ := ν) (u := 𝓝[>] (0 : ℝ))
      (f := F) (fun t => (kernel_continuous t).measurable.ennreal_ofReal)
    simpa only [(hlim _).liminf_eq, lintegral_one] using hfatou
  have hupper : limsup (fun t => ∫⁻ r, F t r ∂ν) (𝓝[>] (0 : ℝ)) ≤ ν univ := by
    apply limsup_le_of_le (by isBoundedDefault)
    filter_upwards [self_mem_nhdsWithin] with t ht
    calc
      (∫⁻ r, F t r ∂ν) ≤ ∫⁻ _r : ℝ≥0, (1 : ℝ≥0∞) ∂ν := by
        apply lintegral_mono
        intro r
        change ENNReal.ofReal (Real.exp (-(r : ℝ) * t)) ≤ 1
        rw [← ENNReal.ofReal_one]
        apply ENNReal.ofReal_le_ofReal
        exact Real.exp_le_one_iff.mpr
          (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr r.coe_nonneg) (le_of_lt ht))
      _ = ν univ := lintegral_one
  exact tendsto_of_le_liminf_of_limsup_le hlower hupper

theorem realExtension_nonneg (f : OpenFunction) (t : ℝ) : 0 ≤ realExtension f t := by
  unfold realExtension
  split_ifs
  · exact NNReal.coe_nonneg _
  · exact le_rfl

theorem represents_mass_limit (f : OpenFunction) (ν : Measure ℝ≥0) (hν : Represents f ν) :
    Tendsto (fun t : ℝ => ENNReal.ofReal (realExtension f t))
      (𝓝[>] (0 : ℝ)) (𝓝 (ν univ)) := by
  apply (laplace_mass_limit ν).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [realExtension_positive f t ht, hν.2 ⟨t, ht⟩]
  exact (ofReal_integral_eq_lintegral_ofReal (hν.1 ⟨t, ht⟩)
    (Eventually.of_forall fun r => (Real.exp_pos _).le)).symm

theorem endpoint_mass : Specs.ExpandedFA.P1.BernsteinOpenHalfLine.EndpointMass := by
  intro f ν hν
  have hlim := represents_mass_limit f ν hν
  have heq (L : ℝ≥0)
      (hL : Tendsto (realExtension f) (𝓝[>] (0 : ℝ)) (𝓝 (L : ℝ))) :
      ν univ = (L : ℝ≥0∞) := by
    have := tendsto_nhds_unique hlim (ENNReal.tendsto_ofReal hL)
    simpa only [ENNReal.ofReal_coe_nnreal] using this
  refine ⟨hlim, ⟨?_, ?_⟩, heq⟩
  · intro hfinite
    let := hfinite
    refine ⟨⟨(ν univ).toReal, ENNReal.toReal_nonneg⟩, ?_⟩
    change Tendsto (realExtension f) (𝓝[>] (0 : ℝ)) (𝓝 (ν univ).toReal)
    have htoReal := (ENNReal.tendsto_toReal (measure_ne_top ν univ)).comp hlim
    simpa only [Function.comp_def, ENNReal.toReal_ofReal (realExtension_nonneg f _)] using htoReal
  · rintro ⟨L, hL⟩
    constructor
    rw [heq L hL]
    exact ENNReal.coe_lt_top

end ExpandedFA.P1.BernsteinOpenHalfLine
