import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch10.RegularProblem

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal ComplexConjugate

namespace D13Unified.Ch10.RegularProblem

abbrev Problem := Specs.D13Unified.Ch10.RegularProblem.Problem
abbrev BoundaryCoefficients := Specs.D13Unified.Ch10.RegularProblem.BoundaryCoefficients
abbrev interval := Specs.D13Unified.Ch10.RegularProblem.intervalValue
abbrev baseMeasure := Specs.D13Unified.Ch10.RegularProblem.baseMeasureValue
abbrev weightedMeasure := Specs.D13Unified.Ch10.RegularProblem.weightedMeasureValue
abbrev Hilbert := Specs.D13Unified.Ch10.RegularProblem.hilbertValue
abbrev derivative := Specs.D13Unified.Ch10.RegularProblem.derivativeValue
abbrev expression := Specs.D13Unified.Ch10.RegularProblem.expressionValue
abbrev SatisfiesBoundary := Specs.D13Unified.Ch10.RegularProblem.satisfiesBoundaryValue
abbrev dirichlet := Specs.D13Unified.Ch10.RegularProblem.dirichletValue
abbrev IsClassicalEigenfunction := Specs.D13Unified.Ch10.RegularProblem.classicalEigenfunctionValue
abbrev toHilbert := Specs.D13Unified.Ch10.RegularProblem.toHilbertValue
abbrev paperInner := Specs.D13Unified.Ch10.RegularProblem.paperInnerValue

private theorem density_measurable (P : Problem) :
    AEMeasurable (fun x => ENNReal.ofReal (P.w x)) (baseMeasure P) :=
  (P.w_continuous.aemeasurable measurableSet_Icc).ennreal_ofReal

/-- Positive weight gives exactly the same null sets as Lebesgue measure on the interval. -/
theorem weighted_ae (P : Problem) (R : ℝ → Prop) :
    (∀ᵐ x ∂weightedMeasure P, R x) ↔ ∀ᵐ x ∂baseMeasure P, R x := by
  rw [weightedMeasure, Specs.D13Unified.Ch10.RegularProblem.weightedMeasureValue,
    ae_withDensity_iff' (density_measurable P)]
  apply eventually_congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  simp [ne_of_gt (ENNReal.ofReal_pos.mpr (P.w_positive x hx))]

theorem hilbert_complete (P : Problem) : CompleteSpace (Hilbert P) := inferInstance
theorem hilbert_innerProductSpace (P : Problem) : Nonempty (InnerProductSpace ℂ (Hilbert P)) := ⟨inferInstance⟩

/-- The chosen representative of a quotient class agrees AE with the input function. -/
theorem representative_ae (P : Problem) (f : ℝ → ℂ) (hf : MemLp f 2 (weightedMeasure P)) :
    (toHilbert P f hf : ℝ → ℂ) =ᵐ[weightedMeasure P] f := hf.coeFn_toLp

theorem quotient_equality (P : Problem) (f g : ℝ → ℂ)
    (hf : MemLp f 2 (weightedMeasure P)) (hg : MemLp g 2 (weightedMeasure P)) :
    toHilbert P f hf = toHilbert P g hg ↔ f =ᵐ[baseMeasure P] g := by
  change hf.toLp f = hg.toLp g ↔ _
  rw [hf.toLp_eq_toLp_iff hg]
  exact weighted_ae P _

theorem hilbert_equality (P : Problem) (u v : Hilbert P) :
    u = v ↔ (u : ℝ → ℂ) =ᵐ[baseMeasure P] v := by
  constructor
  · rintro rfl; exact EventuallyEq.rfl
  · intro h; exact Lp.ext ((weighted_ae P _).mpr h)

theorem all_represented (P : Problem) (u : Hilbert P) :
    ∃ (f : ℝ → ℂ) (hf : MemLp f 2 (weightedMeasure P)), toHilbert P f hf = u :=
  ⟨u, Lp.memLp u, Lp.toLp_coeFn u (Lp.memLp u)⟩

/-- Change from the weighted measure to the paper's integral against w dx. -/
theorem integral_density (P : Problem) (f : ℝ → ℂ) :
    (∫ x, f x ∂weightedMeasure P) = ∫ x in interval P, f x * (P.w x : ℂ) := by
  rw [weightedMeasure, Specs.D13Unified.Ch10.RegularProblem.weightedMeasureValue,
    integral_withDensity_eq_integral_toReal_smul₀ (density_measurable P)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) f]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  simp [ENNReal.toReal_ofReal (le_of_lt (P.w_positive x hx)), mul_comm]

theorem inner_integral (P : Problem) (u v : Hilbert P) :
    paperInner P u v = ∫ x in interval P, u x * conj (v x) * (P.w x : ℂ) := by
  change inner ℂ v u = _
  rw [L2.inner_def, integral_density]
  simp only [RCLike.inner_apply, mul_comm]

/-- The weighted product is integrable, not merely a formal Bochner integral. -/
theorem inner_integrable (P : Problem) (u v : Hilbert P) :
    Integrable (fun x => u x * conj (v x) * (P.w x : ℂ)) (baseMeasure P) := by
  have hi := L2.integrable_inner (𝕜 := ℂ) v u
  have hw := (integrable_withDensity_iff_integrable_smul₀' (density_measurable P)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mp hi
  apply hw.congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  simp [RCLike.inner_apply, ENNReal.toReal_ofReal (P.w_positive x hx).le,
    mul_comm, mul_left_comm]

theorem inner_intervalIntegral (P : Problem) (u v : Hilbert P) :
    paperInner P u v = ∫ x in P.a..P.b, u x * conj (v x) * (P.w x : ℂ) := by
  rw [inner_integral, intervalIntegral.integral_of_le P.a_lt_b.le]
  exact integral_Icc_eq_integral_Ioc

theorem inner_representatives (P : Problem) (f g : ℝ → ℂ)
    (hf : MemLp f 2 (weightedMeasure P)) (hg : MemLp g 2 (weightedMeasure P)) :
    paperInner P (toHilbert P f hf) (toHilbert P g hg) =
      ∫ x in interval P, f x * conj (g x) * (P.w x : ℂ) := by
  rw [inner_integral]
  apply integral_congr_ae
  filter_upwards [(weighted_ae P _).mp hf.coeFn_toLp,
    (weighted_ae P _).mp hg.coeFn_toLp] with x hx hy
  simpa only [toHilbert, Specs.D13Unified.Ch10.RegularProblem.toHilbertValue] using
    congrArg₂ (fun a b : ℂ => a * conj b * (P.w x : ℂ)) hx hy

theorem inner_linear_first (P : Problem) (c : ℂ) (u v : Hilbert P) :
    paperInner P (c • u) v = c * paperInner P u v := inner_smul_right _ _ _

theorem inner_conjugate_second (P : Problem) (c : ℂ) (u v : Hilbert P) :
    paperInner P u (c • v) = conj c * paperInner P u v := inner_smul_left _ _ _

theorem inner_norm (P : Problem) (u : Hilbert P) :
    paperInner P u u = (‖u‖ ^ 2 : ℝ) := by
  change inner ℂ u u = _
  rw [inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]
  rfl

theorem dirichlet_boundary (P : Problem) (y : ℝ → ℂ) :
    SatisfiesBoundary P dirichlet y ↔ y P.a = 0 ∧ y P.b = 0 := by
  simp [SatisfiesBoundary, dirichlet, Specs.D13Unified.Ch10.RegularProblem.satisfiesBoundaryValue,
    Specs.D13Unified.Ch10.RegularProblem.dirichletValue]

/-- The continuous weight has finite integral on the compact interval. -/
theorem weightedMeasure_finite (P : Problem) : IsFiniteMeasure (weightedMeasure P) := by
  apply isFiniteMeasure_withDensity
  have hi : Integrable P.w (baseMeasure P) := P.w_continuous.integrableOn_Icc
  have hn : ∀ᵐ x ∂baseMeasure P, 0 ≤ P.w x := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact (P.w_positive x hx).le
  exact ne_of_lt ((hasFiniteIntegral_iff_ofReal hn).mp hi.hasFiniteIntegral)

/-- Every continuous representative on [a,b] is genuinely square integrable. -/
theorem continuous_memLp (P : Problem) (f : ℝ → ℂ)
    (hf : ContinuousOn f (interval P)) : MemLp f 2 (weightedMeasure P) := by
  haveI := weightedMeasure_finite P
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  apply MemLp.of_bound (μ := weightedMeasure P) (p := 2)
    ((hf.aestronglyMeasurable measurableSet_Icc).mono_ac
      (withDensity_absolutelyContinuous (baseMeasure P) (fun x => ENNReal.ofReal (P.w x)))) C
  apply (weighted_ae P _).mpr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  exact hC x hx

/-- Passing to L² loses only values outside the interval for continuous functions. -/
theorem continuous_equality (P : Problem) (f g : ℝ → ℂ)
    (hf : ContinuousOn f (interval P)) (hg : ContinuousOn g (interval P))
    (hf2 : MemLp f 2 (weightedMeasure P)) (hg2 : MemLp g 2 (weightedMeasure P)) :
    toHilbert P f hf2 = toHilbert P g hg2 ↔ EqOn f g (interval P) := by
  rw [quotient_equality]
  constructor
  · intro h
    exact Measure.eqOn_Icc_of_ae_eq volume (ne_of_lt P.a_lt_b) h hf hg
  · intro h
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact h hx

theorem continuous_nonzero (P : Problem) (f : ℝ → ℂ)
    (hf : ContinuousOn f (interval P)) (hf2 : MemLp f 2 (weightedMeasure P)) :
    toHilbert P f hf2 ≠ 0 ↔ ∃ x ∈ interval P, f x ≠ 0 := by
  have hzero : toHilbert P (fun _ => 0) (continuous_memLp P _ continuousOn_const) = 0 := rfl
  rw [← hzero, ne_eq, continuous_equality P f (fun _ => 0) hf continuousOn_const]
  simp only [EqOn, not_forall, exists_prop]

/-- A classical eigenfunction is an actual C² function; its Hilbert class is nonzero. -/
theorem eigenfunction_hilbert (P : Problem) (B : BoundaryCoefficients)
    (lam : ℂ) (y : ℝ → ℂ) (hy : IsClassicalEigenfunction P B lam y) :
    ∃ hy2 : MemLp y 2 (weightedMeasure P), toHilbert P y hy2 ≠ 0 := by
  have hc := hy.1.continuousOn
  exact ⟨continuous_memLp P y hc, (continuous_nonzero P y hc _).mpr hy.2.1⟩

end D13Unified.Ch10.RegularProblem
