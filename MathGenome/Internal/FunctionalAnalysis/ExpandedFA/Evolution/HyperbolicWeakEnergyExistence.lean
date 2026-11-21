import Mathlib.Tactic.Choose
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Analysis.InnerProductSpace.Dual
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Evolution.HyperbolicWeakEnergyExistence
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Evolution.HyperbolicFormBoundsAndCarrier
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Evolution.HilbertTripleTrace
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Weak-energy Galerkin existence in the original real Hilbert triple.
The construction uses finite mass systems, an absolutely continuous energy
estimate, simultaneous weak L² limits, and linear endpoint moments. It proves
the shifted-energy and original-norm estimates, weakly continuous states, and
strong initial traces, including the prescribed-data zero-duration case.
No separability, compact embedding, or ambient operator-C¹ premise is added.
-/
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
universe u v w

namespace ExpandedFA.Evolution.HyperbolicWeakEnergyExistence
open HilbertTripleSpec HyperbolicFormSpec HyperbolicWeakEnergySpec

variable {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

@[simp] theorem shiftedForm_apply (j : HilbertTriple V H) (a : ℝ → Form V)
    (κ t : ℝ) (x y : V) :
    shiftedForm j a κ t x y = a t x y + κ * inner ℝ (j.embedding x) (j.embedding y) := by
  change a t x y + κ * intoDual j x y = _
  rw [intoDual_apply]

@[simp] theorem shiftedEnergy_eq (j : HilbertTriple V H) (a : ℝ → Form V)
    (κ t : ℝ) (x : V) (y : H) :
    shiftedEnergy j a κ t x y = ‖y‖ ^ 2 + a t x x + κ * ‖j.embedding x‖ ^ 2 := by
  simp only [shiftedEnergy, shiftedForm_apply, real_inner_self_eq_norm_sq]
  ring

theorem shiftedForm_coercive (j : HilbertTriple V H) (T : ℝ)
    (a : ℝ → Form V) (α C : ℝ) (ha : FormHypotheses j T a α C)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) (x : V) :
    α * ‖x‖ ^ 2 ≤ shiftedForm j a C t x x := by
  rw [shiftedForm_apply, real_inner_self_eq_norm_sq]
  linarith [ha.garding t ht x]

theorem shiftedForm_symmetric (j : HilbertTriple V H) (T : ℝ)
    (a : ℝ → Form V) (α C : ℝ) (ha : FormHypotheses j T a α C)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) (x y : V) :
    shiftedForm j a C t x y = shiftedForm j a C t y x := by
  simp only [shiftedForm_apply, ha.symmetric t ht x y,
    real_inner_comm (j.embedding x) (j.embedding y)]

theorem shiftedEnergy_nonneg (j : HilbertTriple V H) (T : ℝ)
    (a : ℝ → Form V) (α C : ℝ) (ha : FormHypotheses j T a α C)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) (x : V) (y : H) :
    0 ≤ shiftedEnergy j a C t x y := by
  have h := shiftedForm_coercive j T a α C ha ht x
  have hx : 0 ≤ α * ‖x‖ ^ 2 := mul_nonneg ha.alpha_pos.le (sq_nonneg _)
  dsimp [shiftedEnergy]
  linarith [sq_nonneg ‖y‖]

theorem shifted_bounds : ShiftedBounds (V := V) (H := H) := by
  intro j T a α C ha
  obtain ⟨M, hM, hbound⟩ :=
    HyperbolicFormBoundsAndCarrier.form_values_bounded T a ha.scalarC1
  refine ⟨M + C * ‖j.embedding‖ ^ 2,
    add_nonneg hM (mul_nonneg ha.shift_nonneg (sq_nonneg _)), ?_⟩
  intro t ht x y
  constructor
  · change ‖y‖ ^ 2 + α * ‖x‖ ^ 2 ≤ ‖y‖ ^ 2 + shiftedForm j a C t x x
    linarith [shiftedForm_coercive j T a α C ha ht x]
  · have hform : a t x x ≤ M * ‖x‖ ^ 2 := by
      calc
        a t x x ≤ ‖a t x x‖ := le_abs_self _
        _ ≤ ‖a t‖ * ‖x‖ * ‖x‖ := (a t).le_opNorm₂ x x
        _ ≤ M * ‖x‖ * ‖x‖ := by gcongr; exact hbound t ht
        _ = M * ‖x‖ ^ 2 := by ring
    have hemb : ‖j.embedding x‖ ^ 2 ≤ ‖j.embedding‖ ^ 2 * ‖x‖ ^ 2 := by
      calc
        ‖j.embedding x‖ ^ 2 ≤ (‖j.embedding‖ * ‖x‖) ^ 2 := by
          gcongr; exact j.embedding.le_opNorm x
        _ = _ := by ring
    rw [shiftedEnergy_eq]
    nlinarith [mul_le_mul_of_nonneg_left hemb ha.shift_nonneg]

theorem energy_rhs_bound : EnergyRhsBound (V := V) (H := H) := by
  intro j T a α C ha
  obtain ⟨M, hM, hbound, _⟩ :=
    HyperbolicFormBoundsAndCarrier.uniform_bounds T a ha.scalarC1
  let D : ℝ := M + C * ‖j.embedding‖ ^ 2
  have hD : 0 ≤ D := add_nonneg hM (mul_nonneg ha.shift_nonneg (sq_nonneg _))
  refine ⟨1 + C + D / α,
    add_nonneg (by linarith [ha.shift_nonneg]) (div_nonneg hD ha.alpha_pos.le), ?_⟩
  intro t ht x y h
  have hder : derivWithin (fun r => a r x x) (Set.Icc 0 T) t ≤ M * ‖x‖ ^ 2 := by
    have hb := hbound t ht x x
    have hle := le_abs_self (derivWithin (fun r => a r x x) (Set.Icc 0 T) t)
    nlinarith [abs_nonneg (a t x x)]
  have hhy : 2 * inner ℝ h y ≤ ‖h‖ ^ 2 + ‖y‖ ^ 2 := by
    nlinarith [sq_nonneg ‖h - y‖, norm_sub_sq_real h y]
  have hxy : 2 * inner ℝ (j.embedding x) y ≤
      ‖j.embedding x‖ ^ 2 + ‖y‖ ^ 2 := by
    nlinarith [sq_nonneg ‖j.embedding x - y‖, norm_sub_sq_real (j.embedding x) y]
  have hemb : ‖j.embedding x‖ ^ 2 ≤ ‖j.embedding‖ ^ 2 * ‖x‖ ^ 2 := by
    calc
      ‖j.embedding x‖ ^ 2 ≤ (‖j.embedding‖ * ‖x‖) ^ 2 := by
        gcongr; exact j.embedding.le_opNorm x
      _ = _ := by ring
  have hE := shiftedEnergy_nonneg j T a α C ha ht x y
  have hcoer := shiftedForm_coercive j T a α C ha ht x
  have hu : α * ‖x‖ ^ 2 ≤ shiftedEnergy j a C t x y := by
    dsimp [shiftedEnergy]
    linarith [sq_nonneg ‖y‖]
  have hv : ‖y‖ ^ 2 ≤ shiftedEnergy j a C t x y := by
    have hnn := mul_nonneg ha.alpha_pos.le (sq_nonneg ‖x‖)
    dsimp [shiftedEnergy]
    linarith
  have hDx : D * ‖x‖ ^ 2 ≤ (D / α) * shiftedEnergy j a C t x y := by
    have hm := mul_le_mul_of_nonneg_left hu (div_nonneg hD ha.alpha_pos.le)
    have heq : D / α * (α * ‖x‖ ^ 2) = D * ‖x‖ ^ 2 := by
      field_simp [ha.alpha_pos.ne']
    rwa [heq] at hm
  have hCy := mul_le_mul_of_nonneg_left hv (show 0 ≤ 1 + C by linarith [ha.shift_nonneg])
  have hCx := mul_le_mul_of_nonneg_left hemb ha.shift_nonneg
  have hCxy := mul_le_mul_of_nonneg_left hxy ha.shift_nonneg
  dsimp [D] at hDx
  nlinarith

/-- Polarization in an arbitrary symmetric coercive energy form. This proves
strong convergence from weak convergence and an energy upper bound, without
asserting that weak compactness by itself supplies norm convergence. -/
theorem strong_of_energy_upper {I : Type w} {l : Filter I}
    (b : Form V) (α : ℝ) (hα : 0 < α)
    (hsymm : ∀ x y, b x y = b y x)
    (hcoer : ∀ x, α * ‖x‖ ^ 2 ≤ b x x)
    (x : I → V) (y : I → H) (x₀ : V) (y₀ : H) (e : I → ℝ)
    (he : Tendsto e l (𝓝 (‖y₀‖ ^ 2 + b x₀ x₀)))
    (hcross : Tendsto (fun i => b (x i) x₀ + inner ℝ (y i) y₀)
      l (𝓝 (b x₀ x₀ + ‖y₀‖ ^ 2)))
    (hupper : ∀ᶠ i in l, ‖y i‖ ^ 2 + b (x i) (x i) ≤ e i) :
    Tendsto x l (𝓝 x₀) ∧ Tendsto y l (𝓝 y₀) := by
  let gap : I → ℝ := fun i => e i -
    2 * (b (x i) x₀ + inner ℝ (y i) y₀) + (‖y₀‖ ^ 2 + b x₀ x₀)
  have hgap : Tendsto gap l (𝓝 0) := by
    have h := (he.sub (hcross.const_mul 2)).add_const (‖y₀‖ ^ 2 + b x₀ x₀)
    have hz : (‖y₀‖ ^ 2 + b x₀ x₀) - 2 * (b x₀ x₀ + ‖y₀‖ ^ 2) +
        (‖y₀‖ ^ 2 + b x₀ x₀) = 0 := by ring
    simpa only [hz] using h
  have hdist : ∀ᶠ i in l,
      α * ‖x i - x₀‖ ^ 2 + ‖y i - y₀‖ ^ 2 ≤ gap i := by
    filter_upwards [hupper] with i hi
    have hb : b (x i - x₀) (x i - x₀) =
        b (x i) (x i) - 2 * b (x i) x₀ + b x₀ x₀ := by
      simp only [map_sub, sub_apply]
      rw [hsymm x₀ (x i)]
      ring
    have hc := hcoer (x i - x₀)
    rw [hb] at hc
    rw [norm_sub_sq_real (y i) y₀]
    dsimp [gap]
    linarith
  constructor
  · apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hεα : 0 < α * ε ^ 2 := mul_pos hα (sq_pos_of_pos hε)
    filter_upwards [hdist, hgap.eventually_lt_const hεα] with i hi hlt
    rw [dist_eq_norm]
    by_contra hn
    have hn' : ε ≤ ‖x i - x₀‖ := le_of_not_gt hn
    have hs : ε ^ 2 ≤ ‖x i - x₀‖ ^ 2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hs hα.le
    linarith [sq_nonneg ‖y i - y₀‖]
  · apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hdist, hgap.eventually_lt_const (sq_pos_of_pos hε)] with i hi hlt
    rw [dist_eq_norm]
    by_contra hn
    have hn' : ε ≤ ‖y i - y₀‖ := le_of_not_gt hn
    have hs : ε ^ 2 ≤ ‖y i - y₀‖ ^ 2 := by nlinarith
    have hnn : 0 ≤ α * ‖x i - x₀‖ ^ 2 := mul_nonneg hα.le (sq_nonneg _)
    linarith

/-- Freeze the form at zero. Its variation is O(t) on a uniformly bounded
state, so polarization in that fixed coercive form gives the strong trace. -/
theorem initial_trace_criterion : InitialTraceCriterion (V := V) (H := H) := by
  intro j T hT a α C ha x y hx hy R hR hbound g hg hupper
  have h0 : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, hT⟩
  obtain ⟨M, hM, hLip⟩ :=
    HyperbolicFormBoundsAndCarrier.form_secants_bounded T a ha.scalarC1
  let b : Form V := shiftedForm j a C 0
  let e : ℝ → ℝ := fun t => g t + M * |t| * R ^ 2
  have htend : Tendsto (fun t : ℝ => |t|) (𝓝[Set.Icc 0 T] 0) (𝓝 0) := by
    simpa using (continuous_abs.continuousAt.tendsto.mono_left nhdsWithin_le_nhds :
      Tendsto (fun t : ℝ => |t|) (𝓝[Set.Icc 0 T] 0) (𝓝 |(0 : ℝ)|))
  have he : Tendsto e (𝓝[Set.Icc 0 T] 0) (𝓝 (‖y 0‖ ^ 2 + b (x 0) (x 0))) := by
    simpa [e, shiftedEnergy, b] using hg.add ((htend.const_mul M).mul_const (R ^ 2))
  have hbweak : Tendsto (fun t => b (x t) (x 0)) (𝓝[Set.Icc 0 T] 0)
      (𝓝 (b (x 0) (x 0))) := by
    exact (hx (b.flip (x 0)) 0 h0).tendsto
  have hyweak : Tendsto (fun t => inner ℝ (y t) (y 0)) (𝓝[Set.Icc 0 T] 0)
      (𝓝 (‖y 0‖ ^ 2)) := by
    simpa only [InnerProductSpace.toDual_apply_apply,
      real_inner_comm (y 0), real_inner_self_eq_norm_sq] using
      (hy (InnerProductSpace.toDual ℝ H (y 0)) 0 h0).tendsto
  apply strong_of_energy_upper b α ha.alpha_pos
    (shiftedForm_symmetric j T a α C ha h0)
    (shiftedForm_coercive j T a α C ha h0) x y (x 0) (y 0) e he
    (hbweak.add hyweak)
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hnorm : ‖a 0 - a t‖ ≤ M * |t| := by
    simpa only [zero_sub, norm_neg, Real.norm_eq_abs] using hLip t ht 0 h0
  have hquad : b (x t) (x t) - shiftedForm j a C t (x t) (x t) ≤
      M * |t| * R ^ 2 := by
    calc
      b (x t) (x t) - shiftedForm j a C t (x t) (x t) =
          (a 0 - a t) (x t) (x t) := by simp [b]
      _ ≤ ‖(a 0 - a t) (x t) (x t)‖ := le_abs_self _
      _ ≤ ‖a 0 - a t‖ * ‖x t‖ * ‖x t‖ := (a 0 - a t).le_opNorm₂ _ _
      _ ≤ (M * |t|) * R * R := by gcongr <;> exact hbound t ht
      _ = M * |t| * R ^ 2 := by ring
  have hu := hupper t ht
  dsimp [shiftedEnergy] at hu
  dsimp [e]
  linarith

/-- Approximate each V′ test by a pivot test and use the same V bound at
both times. This is uniform approximation of scalar continuous functions. -/
theorem weak_continuity_from_pivot : WeakContinuityFromPivot (V := V) (H := H) := by
  intro j S x R hR hbound hJ L t₀ ht₀
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨h, hh⟩ := (pivotInjection_denseRange j).exists_dist_lt L
    (show 0 < ε / (4 * (R + 1)) by positivity)
  rw [dist_eq_norm] at hh
  have hh' : ‖L - pivotInjection j h‖ * (4 * (R + 1)) < ε :=
    (lt_div_iff₀ (by positivity)).mp hh
  have herr (r : ℝ) (hr : r ∈ S) :
      dist (L (x r)) (inner ℝ h (j.embedding (x r))) < ε / 4 := by
    have hsmall : ‖L - pivotInjection j h‖ * R < ε / 4 := by
      nlinarith [norm_nonneg (L - pivotInjection j h)]
    calc
      dist (L (x r)) (inner ℝ h (j.embedding (x r))) =
          ‖(L - pivotInjection j h) (x r)‖ := by
            rw [dist_eq_norm, sub_apply, pivotInjection_apply]
      _ ≤ ‖L - pivotInjection j h‖ * ‖x r‖ := (L - pivotInjection j h).le_opNorm _
      _ ≤ ‖L - pivotInjection j h‖ * R :=
        mul_le_mul_of_nonneg_left (hbound r hr) (norm_nonneg _)
      _ < ε / 4 := hsmall
  have hpcont : ContinuousOn (fun t => inner ℝ h (j.embedding (x t))) S :=
    continuousOn_const.inner hJ
  have hp := Metric.tendsto_nhds.mp (hpcont t₀ ht₀) (ε / 2) (by positivity)
  filter_upwards [self_mem_nhdsWithin, hp] with t ht hpt
  calc
    dist (L (x t)) (L (x t₀)) ≤
        dist (L (x t)) (inner ℝ h (j.embedding (x t))) +
          dist (inner ℝ h (j.embedding (x t))) (L (x t₀)) := dist_triangle _ _ _
    _ ≤ dist (L (x t)) (inner ℝ h (j.embedding (x t))) +
        (dist (inner ℝ h (j.embedding (x t))) (inner ℝ h (j.embedding (x t₀))) +
          dist (inner ℝ h (j.embedding (x t₀))) (L (x t₀))) := by
      gcongr; exact dist_triangle _ _ _
    _ < ε := by
      have he₀ := herr t₀ ht₀
      have het := herr t ht
      rw [dist_comm (L (x t₀))] at he₀
      linarith

theorem forcing_integral_continuousOn (T : ℝ) (hT : 0 ≤ T) (f : timeLpValue H 2 T) :
    ContinuousOn (fun t => ∫ r in 0..t, ‖f r‖ ^ 2) (Set.Icc 0 T) := by
  have hi : Integrable (fun r => ‖f r‖ ^ 2) (volume.restrict (Set.Ioo 0 T)) :=
    (Lp.memLp f).norm.integrable_sq
  rw [restrict_Ioo_eq_restrict_Icc] at hi
  have hi' : IntegrableOn (fun r => ‖f r‖ ^ 2) (Set.uIcc 0 T) volume := by
    simpa only [IntegrableOn, Set.uIcc_of_le hT] using hi
  simpa only [Set.uIcc_of_le hT] using intervalIntegral.continuousOn_primitive_interval hi'

/-- The right hand side of the source's Gronwall estimate has exactly the
initial energy as its limit, since the forcing is genuinely L². -/
theorem gronwall_bound_initial_limit (T : ℝ) (hT : 0 ≤ T)
    (f : timeLpValue H 2 T) (c E₀ : ℝ) :
    Tendsto (fun t => Real.exp (c * t) * (E₀ + ∫ r in 0..t, ‖f r‖ ^ 2))
      (𝓝[Set.Icc 0 T] 0) (𝓝 E₀) := by
  have hI := (forcing_integral_continuousOn T hT f 0 ⟨le_rfl, hT⟩).tendsto
  have hExp : Tendsto (fun t : ℝ => Real.exp (c * t))
      (𝓝[Set.Icc 0 T] 0) (𝓝 1) := by
    simpa using ((continuous_const.mul continuous_id).rexp.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds : Tendsto (fun t : ℝ => Real.exp (c * t))
        (𝓝[Set.Icc 0 T] 0) (𝓝 (Real.exp (c * 0))))
  simpa using hExp.mul (hI.const_add E₀)

theorem strong_trace_of_gronwall (j : HilbertTriple V H) (T : ℝ) (hT : 0 ≤ T)
    (a : ℝ → Form V) (α C : ℝ) (ha : FormHypotheses j T a α C)
    (u₀ : V) (v₀ : H) (f : timeLpValue H 2 T)
    (z : WeakEnergySolution j T a u₀ v₀ f) (c R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ t ∈ Set.Icc 0 T, ‖z.displacement t‖ ≤ R)
    (henergy : ∀ t ∈ Set.Icc 0 T,
      shiftedEnergy j a C t (z.displacement t) (z.velocity t) ≤
        Real.exp (c * t) * (shiftedEnergy j a C 0 u₀ v₀ + ∫ r in 0..t, ‖f r‖ ^ 2)) :
    Tendsto z.displacement (𝓝[Set.Icc 0 T] 0) (𝓝 u₀) ∧
    Tendsto z.velocity (𝓝[Set.Icc 0 T] 0) (𝓝 v₀) := by
  have hi := gronwall_bound_initial_limit T hT f c (shiftedEnergy j a C 0 u₀ v₀)
  have h := initial_trace_criterion j T hT a α C ha z.displacement z.velocity
    z.displacement_weak z.velocity_weak R hR hbound _
    (by simpa only [z.initial_displacement, z.initial_velocity] using hi) henergy
  simpa only [z.initial_displacement, z.initial_velocity] using h

@[simp] theorem timeMeasure_zero : timeMeasureValue 0 = 0 := by
  simp [timeMeasureValue]

theorem derivative_zero_time {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u g : ℝ → E) : derivativeValue 0 u g := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    exact (not_lt_of_ge ht.1.le ht.2).elim
  · intro t ht
    exact (not_lt_of_ge ht.1.le ht.2).elim
  · intro φ hφ
    simp [timeMeasure_zero]

theorem zero_time_solution : ZeroTimeSolution (V := V) (H := H) := by
  intro j a u₀ v₀ f
  let z : WeakEnergySolution j 0 a u₀ v₀ f := {
    displacement := fun _ => u₀
    velocity := fun _ => v₀
    acceleration := fun _ => 0
    displacement_mem := by simp
    pivot_displacement_mem := by simp
    velocity_mem := by simp
    dual_velocity_mem := by simp
    acceleration_mem := by simp
    displacement_derivative := derivative_zero_time _ _
    velocity_derivative := derivative_zero_time _ _
    equation := by simp
    displacement_weak := fun _ => continuousOn_const
    velocity_weak := fun _ => continuousOn_const
    initial_displacement := rfl
    initial_velocity := rfl }
  exact ⟨z, fun _ _ => ⟨rfl, rfl⟩, tendsto_const_nhds, tendsto_const_nhds⟩

/-- A bounded linear image of a Hilbert closed ball is norm closed, even
when the operator has nonclosed range. Banach–Alaoglu is applied through
Riesz representation, so no countable basis or compact embedding is needed. -/
theorem isClosed_image_hilbert_closedBall {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (A : V →L[ℝ] E) (R : ℝ) :
    IsClosed (A '' Metric.closedBall 0 R) := by
  let F : WeakDual ℝ V → WeakSpace ℝ E := fun w =>
    toWeakSpace ℝ E (A ((InnerProductSpace.toDual ℝ V).symm w.toStrongDual))
  have hF : Continuous F := by
    apply WeakBilin.continuous_of_continuous_eval
    intro L
    have heq : (fun w : WeakDual ℝ V => L (A
        ((InnerProductSpace.toDual ℝ V).symm w.toStrongDual))) =
        (fun w : WeakDual ℝ V =>
          w ((InnerProductSpace.toDual ℝ V).symm (L.comp A))) := by
      funext w
      change (L.comp A) ((InnerProductSpace.toDual ℝ V).symm w.toStrongDual) = _
      rw [← InnerProductSpace.toDual_symm_apply (𝕜 := ℝ)
        (y := L.comp A), real_inner_comm, InnerProductSpace.toDual_symm_apply]
      rfl
    change Continuous (fun w : WeakDual ℝ V => L (A
      ((InnerProductSpace.toDual ℝ V).symm w.toStrongDual)))
    rw [heq]
    exact WeakDual.eval_continuous _
  have himage : F '' (WeakDual.toStrongDual ⁻¹'
      Metric.closedBall (0 : StrongDual ℝ V) R) =
      toWeakSpace ℝ E '' (A '' Metric.closedBall 0 R) := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨_, ⟨_, ?_, rfl⟩, rfl⟩
      simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right,
        LinearIsometryEquiv.norm_map] using hw
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨((InnerProductSpace.toDual ℝ V) x).toWeakDual, ?_, ?_⟩
      · simpa only [Set.mem_preimage, StrongDual.toStrongDual_toWeakDual,
          Metric.mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map] using hx
      · simp [F]
  have hc := ((WeakDual.isCompact_closedBall
    (0 : StrongDual ℝ V) R).image hF).isClosed
  rw [himage] at hc
  have hp := hc.preimage (toWeakSpaceCLM ℝ E).continuous
  change IsClosed ((toWeakSpace ℝ E) ⁻¹'
    (toWeakSpace ℝ E) '' (A '' Metric.closedBall 0 R)) at hp
  simpa only [Set.preimage_image_eq _ (toWeakSpace ℝ E).injective] using hp

/-- Closed conditions on a continuous curve that hold a.e. on a positive
open time interval hold at every point of the closed interval. -/
theorem continuousOn_mem_closed_of_ae {E : Type*} [TopologicalSpace E]
    (T : ℝ) (hT : 0 < T) (P : ℝ → E) (hP : ContinuousOn P (Set.Icc 0 T))
    (D : Set E) (hD : IsClosed D)
    (hmem : ∀ᵐ t ∂timeMeasureValue T, P t ∈ D) :
    ∀ t ∈ Set.Icc 0 T, P t ∈ D := by
  let F : Set ℝ := Set.Icc 0 T ∩ P ⁻¹' D
  have hF : IsClosed F := hP.preimage_isClosed_of_isClosed isClosed_Icc hD
  have hae : ∀ᵐ t ∂volume, t ∈ Set.Ioo 0 T → t ∈ F := by
    apply (ae_restrict_iff' measurableSet_Ioo).mp
    filter_upwards [hmem, ae_restrict_mem measurableSet_Ioo] with t ht hti
    exact ⟨Set.Ioo_subset_Icc_self hti, ht⟩
  have hzero : volume (Set.Ioo 0 T \ F) = 0 := by
    change volume {t | t ∈ Set.Ioo 0 T ∧ t ∉ F} = 0
    simpa only [ae_iff, not_imp] using hae
  have hempty : Set.Ioo 0 T \ F = ∅ :=
    (isOpen_Ioo.inter hF.isOpen_compl).eq_empty_of_measure_zero hzero
  have hsub : Set.Ioo 0 T ⊆ F := Set.sdiff_eq_empty.mp hempty
  have hclosed := closure_minimal hsub hF
  rw [closure_Ioo (ne_of_lt hT)] at hclosed
  exact fun t ht => (hclosed ht).2

/-- A continuous representative after injection lifts to an everywhere
bounded representative in the original Hilbert space. The injection need
not have closed range. -/
theorem bounded_lift_of_ae {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : V →L[ℝ] E) (hA : Function.Injective A)
    (T : ℝ) (hT : 0 < T) (u : ℝ → V) (P : ℝ → E) (R : ℝ)
    (hbound : ∀ᵐ t ∂timeMeasureValue T, ‖u t‖ ≤ R)
    (hrep : (fun t => A (u t)) =ᵐ[timeMeasureValue T] P)
    (hP : ContinuousOn P (Set.Icc 0 T)) :
    ∃ x : ℝ → V, x =ᵐ[timeMeasureValue T] u ∧
      (∀ t ∈ Set.Icc 0 T, A (x t) = P t ∧ ‖x t‖ ≤ R) ∧
      ContinuousOn (fun t => A (x t)) (Set.Icc 0 T) := by
  have hmem : ∀ t ∈ Set.Icc 0 T, P t ∈ A '' Metric.closedBall 0 R := by
    apply continuousOn_mem_closed_of_ae T hT P hP _
      (isClosed_image_hilbert_closedBall A R)
    filter_upwards [hbound, hrep] with t ht heq
    exact ⟨u t, by simpa using ht, heq⟩
  have hex : ∀ t : ℝ, ∃ x : V,
      t ∈ Set.Icc 0 T → A x = P t ∧ ‖x‖ ≤ R := by
    intro t
    by_cases ht : t ∈ Set.Icc 0 T
    · obtain ⟨x, hx, hAx⟩ := hmem t ht
      exact ⟨x, fun _ => ⟨hAx, by simpa using hx⟩⟩
    · exact ⟨0, fun h => (ht h).elim⟩
  choose x hx using hex
  refine ⟨x, ?_, hx, ?_⟩
  · filter_upwards [hrep, ae_restrict_mem measurableSet_Ioo] with t ht hti
    apply hA
    exact ((hx t (Set.Ioo_subset_Icc_self hti)).1).trans ht.symm
  · exact hP.congr (fun t ht => (hx t ht).1)


/-- Continuous V′ representatives and a uniform H bound imply weak H
continuity. The dense tests are J(V), with the original H norm. -/
theorem weak_continuity_from_dual_pivot (j : HilbertTriple V H)
    (S : Set ℝ) (y : ℝ → H) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ t ∈ S, ‖y t‖ ≤ R)
    (hP : ContinuousOn (fun t => pivotValue j (y t)) S) :
    WeaklyContinuousOn y S := by
  intro L t₀ ht₀
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let h : H := (InnerProductSpace.toDual ℝ H).symm L
  obtain ⟨w, hw⟩ := j.denseRange.exists_dist_lt h
    (show 0 < ε / (4 * (R + 1)) by positivity)
  rw [dist_eq_norm] at hw
  have hw' : ‖h - j.embedding w‖ * (4 * (R + 1)) < ε :=
    (lt_div_iff₀ (by positivity)).mp hw
  have herr (r : ℝ) (hr : r ∈ S) :
      dist (L (y r)) (pivotValue j (y r) w) < ε / 4 := by
    have hsmall : ‖h - j.embedding w‖ * R < ε / 4 := by
      nlinarith [norm_nonneg (h - j.embedding w)]
    calc
      dist (L (y r)) (pivotValue j (y r) w) =
          ‖inner ℝ (h - j.embedding w) (y r)‖ := by
        rw [dist_eq_norm]
        change ‖L (y r) - pivotInjection j (y r) w‖ = _
        dsimp only [h]
        rw [pivotInjection_apply, inner_sub_left,
          InnerProductSpace.toDual_symm_apply, real_inner_comm (j.embedding w)]

      _ ≤ ‖h - j.embedding w‖ * ‖y r‖ := norm_inner_le_norm _ _
      _ ≤ ‖h - j.embedding w‖ * R :=
        mul_le_mul_of_nonneg_left (hbound r hr) (norm_nonneg _)
      _ < ε / 4 := hsmall
  have hpcont : ContinuousOn (fun t => pivotValue j (y t) w) S :=
    (ContinuousLinearMap.apply ℝ ℝ w).continuous.comp_continuousOn hP
  have hp := Metric.tendsto_nhds.mp (hpcont t₀ ht₀) (ε / 2) (by positivity)
  filter_upwards [self_mem_nhdsWithin, hp] with t ht hpt
  calc
    dist (L (y t)) (L (y t₀)) ≤
        dist (L (y t)) (pivotValue j (y t) w) +
          dist (pivotValue j (y t) w) (L (y t₀)) := dist_triangle _ _ _
    _ ≤ dist (L (y t)) (pivotValue j (y t) w) +
        (dist (pivotValue j (y t) w) (pivotValue j (y t₀) w) +
          dist (pivotValue j (y t₀) w) (L (y t₀))) := by
      gcongr; exact dist_triangle _ _ _
    _ < ε := by
      have he₀ := herr t₀ ht₀
      have het := herr t ht
      rw [dist_comm (L (y t₀))] at he₀
      linarith

/-- Recover the V×H weak state from its two vector distributional graphs.
The accepted primitive theorem is used in H and V′, then bounded Hilbert
balls supply the values in V and H at every time, including endpoints. -/
theorem weak_representatives : WeakRepresentatives (V := V) (H := H) := by
  intro j T hT u v g R S hR hS hu hv hg hub hvb hdu hdv
  let : IsFiniteMeasure (timeMeasureValue T) :=
    inferInstanceAs (IsFiniteMeasure (volume.restrict (Set.Ioo 0 T)))
  have huJ : MemLp (fun t => j.embedding (u t)) ∞ (timeMeasureValue T) :=
    j.embedding.comp_memLp' hu
  have hvP : MemLp (fun t => pivotValue j (v t)) ∞ (timeMeasureValue T) :=
    (pivotValue j).comp_memLp' hv
  obtain ⟨P, hPc, hPae, hPinc⟩ := hasTimeDerivative_continuous_primitive
    T _ v (huJ.integrable (by simp)) (hv.integrable (by simp)) hdu
  obtain ⟨Q, hQc, hQae, hQinc⟩ := hasTimeDerivative_continuous_primitive
    T _ g (hvP.integrable (by simp)) (hg.integrable (by norm_num)) hdv
  obtain ⟨x, hxae, hx, hxJ⟩ := bounded_lift_of_ae
    j.embedding j.injective T hT u P R hub hPae hPc.continuousOn
  obtain ⟨y, hyae, hy, hyP⟩ := bounded_lift_of_ae
    (pivotValue j) (pivotInjection_injective j) T hT v Q S hvb hQae hQc.continuousOn
  have hxb : ∀ t ∈ Set.Icc 0 T, ‖x t‖ ≤ R := fun t ht => (hx t ht).2
  have hyb : ∀ t ∈ Set.Icc 0 T, ‖y t‖ ≤ S := fun t ht => (hy t ht).2
  refine ⟨x, y, hxae, hyae, fun t ht => ⟨hxb t ht, hyb t ht⟩,
    weak_continuity_from_pivot j _ x R hR hxb hxJ,
    weak_continuity_from_dual_pivot j _ y S hS hyb hyP, hxJ, hyP, ?_, ?_⟩
  · intro s t
    rw [(hx t t.property).1, (hx s s.property).1]
    exact hPinc s t
  · intro s t
    rw [(hy t t.property).1, (hy s s.property).1]
    exact hQinc s t

/-- Polarization supplies a continuous scalar lower support for the energy
at each fixed time. The a.e. bound on that scalar support extends to the
endpoints, giving the bound for the energy of the weak representatives. -/
theorem energy_bound_everywhere : EnergyBoundEverywhere (V := V) (H := H) := by
  intro j T hT a α C ha x y hx hy R hR hxb G hG hupper s hs
  obtain ⟨M, hM, hLip⟩ :=
    HyperbolicFormBoundsAndCarrier.form_secants_bounded T a ha.scalarC1
  let b : Form V := shiftedForm j a C s
  let E₀ : ℝ := ‖y s‖ ^ 2 + b (x s) (x s)
  let cross : ℝ → ℝ := fun t => b (x t) (x s) + inner ℝ (y t) (y s)
  let lower : ℝ → ℝ := fun t => 2 * cross t - E₀ - M * |t - s| * R ^ 2
  have hcross : ContinuousOn cross (Set.Icc 0 T) := by
    have hv := hy (InnerProductSpace.toDual ℝ H (y s))
    have hv' : ContinuousOn (fun t => inner ℝ (y t) (y s)) (Set.Icc 0 T) := by
      simpa only [InnerProductSpace.toDual_apply_apply, real_inner_comm (y s)] using hv
    exact (hx (b.flip (x s))).add hv'
  have hlower : ContinuousOn lower (Set.Icc 0 T) := by
    exact ((continuousOn_const.mul hcross).sub continuousOn_const).sub
      ((continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).abs)).mul
        continuousOn_const)
  have hsupport : ∀ t ∈ Set.Icc 0 T,
      lower t ≤ shiftedEnergy j a C t (x t) (y t) := by
    intro t ht
    have hb : b (x t - x s) (x t - x s) =
        b (x t) (x t) - 2 * b (x t) (x s) + b (x s) (x s) := by
      simp only [map_sub, sub_apply]
      rw [shiftedForm_symmetric j T a α C ha hs (x s) (x t)]
      ring
    have hpos := shiftedForm_coercive j T a α C ha hs (x t - x s)
    change α * ‖x t - x s‖ ^ 2 ≤ b (x t - x s) (x t - x s) at hpos
    rw [hb] at hpos
    have hαsq := mul_nonneg ha.alpha_pos.le (sq_nonneg ‖x t - x s‖)
    have hnorm : ‖a s - a t‖ ≤ M * |t - s| := by
      simpa only [Real.norm_eq_abs, abs_sub_comm] using hLip t ht s hs
    have hquad : b (x t) (x t) - shiftedForm j a C t (x t) (x t) ≤
        M * |t - s| * R ^ 2 := by
      calc
        b (x t) (x t) - shiftedForm j a C t (x t) (x t) =
            (a s - a t) (x t) (x t) := by simp [b]
        _ ≤ ‖(a s - a t) (x t) (x t)‖ := le_abs_self _
        _ ≤ ‖a s - a t‖ * ‖x t‖ * ‖x t‖ := (a s - a t).le_opNorm₂ _ _
        _ ≤ (M * |t - s|) * R * R := by gcongr <;> exact hxb t ht
        _ = M * |t - s| * R ^ 2 := by ring
    have hysq := sq_nonneg ‖y t - y s‖
    rw [norm_sub_sq_real] at hysq
    dsimp [lower, cross, E₀, shiftedEnergy]
    linarith
  have hae : ∀ᵐ t ∂timeMeasureValue T, lower t - G t ∈ Set.Iic (0 : ℝ) := by
    filter_upwards [hupper, ae_restrict_mem measurableSet_Ioo] with t ht hti
    exact sub_nonpos.mpr ((hsupport t (Set.Ioo_subset_Icc_self hti)).trans ht)
  have hall := continuousOn_mem_closed_of_ae T hT (fun t => lower t - G t)
    (hlower.sub hG) (Set.Iic 0) isClosed_Iic hae
  have h := hall s hs
  change lower s - G s ≤ 0 at h
  dsimp [lower, cross, E₀, b] at h
  simp only [sub_self, abs_zero, mul_zero, zero_mul, sub_zero,
    real_inner_self_eq_norm_sq] at h
  dsimp [shiftedEnergy]
  linarith

/-- The L² forcing contributes at most its squared Bochner norm on
any initial subinterval. -/
theorem forcing_integral_bound (T : ℝ) (hT : 0 ≤ T) (f : timeLpValue H 2 T)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    0 ≤ (∫ r in 0..t, ‖f r‖ ^ 2) ∧ (∫ r in 0..t, ‖f r‖ ^ 2) ≤ ‖f‖ ^ 2 := by
  have hi : IntegrableOn (fun r => ‖f r‖ ^ 2) (Set.Ioc 0 T) := by
    have h := (Lp.memLp f).norm.integrable_sq
    simpa only [IntegrableOn, timeMeasureValue, restrict_Ioo_eq_restrict_Ioc] using h
  have hii : IntervalIntegrable (fun r => ‖f r‖ ^ 2) volume 0 T :=
    intervalIntegrable_iff_integrableOn_Ioc_of_le hT |>.mpr hi
  have hwhole : (∫ r in 0..T, ‖f r‖ ^ 2) = ‖f‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le hT]
    have h := timeLp_integral_norm_sq T f
    simpa only [timeMeasure, timeMeasureValue, restrict_Ioo_eq_restrict_Ioc] using h
  constructor
  · exact intervalIntegral.integral_nonneg_of_forall ht.1 (fun r => sq_nonneg _)
  · rw [← hwhole]
    exact intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
      (Eventually.of_forall fun r => sq_nonneg _) hii

theorem state_bound_of_gronwall (j : HilbertTriple V H) (T : ℝ) (hT : 0 ≤ T)
    (a : ℝ → Form V) (α C : ℝ) (ha : FormHypotheses j T a α C)
    (c : ℝ) (hc : 0 ≤ c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (u₀ : V) (v₀ : H) (f : timeLpValue H 2 T)
      (x : ℝ → V) (y : ℝ → H),
      (∀ t ∈ Set.Icc 0 T, shiftedEnergy j a C t (x t) (y t) ≤
        Real.exp (c * t) * (shiftedEnergy j a C 0 u₀ v₀ + ∫ r in 0..t, ‖f r‖ ^ 2)) →
      ∀ t ∈ Set.Icc 0 T, ‖x t‖ ^ 2 + ‖y t‖ ^ 2 ≤
        K * (‖u₀‖ ^ 2 + ‖v₀‖ ^ 2 + ‖f‖ ^ 2) := by
  obtain ⟨B, hB, hb⟩ := shifted_bounds j T a α C ha
  let K : ℝ := (1 + 1 / α) * Real.exp (c * T) * (1 + B)
  have hinv : 0 ≤ 1 / α := div_nonneg zero_le_one ha.alpha_pos.le
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro u₀ v₀ f x y henergy t ht
  let E := shiftedEnergy j a C t (x t) (y t)
  let D := ‖u₀‖ ^ 2 + ‖v₀‖ ^ 2 + ‖f‖ ^ 2
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hlow := (hb t ht (x t) (y t)).1
  have hαx : α * ‖x t‖ ^ 2 ≤ E := by dsimp [E]; linarith [sq_nonneg ‖y t‖]
  have hEy : ‖y t‖ ^ 2 ≤ E := by
    have hn := mul_nonneg ha.alpha_pos.le (sq_nonneg ‖x t‖)
    dsimp [E]; linarith
  have hxy : ‖x t‖ ^ 2 + ‖y t‖ ^ 2 ≤ (1 + 1 / α) * E := by
    have h := mul_le_mul_of_nonneg_left hαx hinv
    have heq : 1 / α * (α * ‖x t‖ ^ 2) = ‖x t‖ ^ 2 := by
      field_simp [ha.alpha_pos.ne']
    rw [heq] at h
    nlinarith
  have hi := forcing_integral_bound T hT f ht
  have hinit := (hb 0 ⟨le_rfl, hT⟩ u₀ v₀).2
  have hdata : shiftedEnergy j a C 0 u₀ v₀ + (∫ r in 0..t, ‖f r‖ ^ 2) ≤
      (1 + B) * D := by
    dsimp [D]
    nlinarith [sq_nonneg ‖u₀‖, sq_nonneg ‖v₀‖, sq_nonneg ‖f‖]
  have hexp : Real.exp (c * t) ≤ Real.exp (c * T) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left ht.2 hc
  have hE : E ≤ Real.exp (c * T) * ((1 + B) * D) := by
    calc
      E ≤ Real.exp (c * t) *
          (shiftedEnergy j a C 0 u₀ v₀ + ∫ r in 0..t, ‖f r‖ ^ 2) := henergy t ht
      _ ≤ Real.exp (c * t) * ((1 + B) * D) :=
        mul_le_mul_of_nonneg_left hdata (Real.exp_pos _).le
      _ ≤ Real.exp (c * T) * ((1 + B) * D) :=
        mul_le_mul_of_nonneg_right hexp (mul_nonneg (by linarith) hD)
  calc
    ‖x t‖ ^ 2 + ‖y t‖ ^ 2 ≤ (1 + 1 / α) * E := hxy
    _ ≤ (1 + 1 / α) * (Real.exp (c * T) * ((1 + B) * D)) := by
      gcongr
    _ = K * D := by dsimp [K]; ring

/-- An averaged primitive identity fixes the initial endpoint without
pointwise convergence of approximating solutions. -/
theorem initial_value_of_integral_anchor {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : ℝ) (hT : 0 < T) (U g P : ℝ → E) (e₀ : E)
    (hrep : U =ᵐ[timeMeasureValue T] P)
    (hinc : ∀ s t : Set.Icc 0 T,
      P t - P s = ∫ r in s.val..t.val, g r)
    (hanchor : (∫ t, (U t - ∫ r in 0..t, g r) ∂timeMeasureValue T) = T • e₀) :
    P 0 = e₀ := by
  let z : Set.Icc (0 : ℝ) T := ⟨0, le_rfl, hT.le⟩
  have hae : (fun t => U t - ∫ r in 0..t, g r) =ᵐ[timeMeasureValue T]
      fun _ => P 0 := by
    filter_upwards [hrep, ae_restrict_mem measurableSet_Ioo] with t ht hti
    have hi := hinc z ⟨t, Set.Ioo_subset_Icc_self hti⟩
    change P t - P 0 = ∫ r in 0..t, g r at hi
    rw [ht, ← hi]
    exact sub_sub_cancel _ _
  have hconst : (∫ t, (U t - ∫ r in 0..t, g r) ∂timeMeasureValue T) =
      T • P 0 := by
    rw [integral_congr_ae hae]
    simp [timeMeasureValue, hT.le]
  have hscalar : T • P 0 = T • e₀ := hconst.symm.trans hanchor
  exact (smul_right_injective E hT.ne') hscalar




/-- Complete a raw weak limit once the Galerkin graphs, integral initial
anchors and a.e. energy ceiling have been proved. This theorem constructs
representatives; its hypotheses do not presume an energy solution. -/
theorem solution_of_weak_limit (j : HilbertTriple V H) (T : ℝ) (hT : 0 < T)
    (a : ℝ → Form V) (α C : ℝ) (ha : FormHypotheses j T a α C)
    (u₀ : V) (v₀ : H) (f : timeLpValue H 2 T)
    (u : ℝ → V) (v : ℝ → H) (g : ℝ → StrongDual ℝ V)
    (R S c : ℝ) (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hu : MemLp u ∞ (timeMeasureValue T))
    (hv : MemLp v ∞ (timeMeasureValue T))
    (hg : MemLp g 2 (timeMeasureValue T))
    (hub : ∀ᵐ t ∂timeMeasureValue T, ‖u t‖ ≤ R)
    (hvb : ∀ᵐ t ∂timeMeasureValue T, ‖v t‖ ≤ S)
    (hdu : derivativeValue T (fun t => j.embedding (u t)) v)
    (hdv : derivativeValue T (fun t => pivotValue j (v t)) g)
    (heq : ∀ᵐ t ∂timeMeasureValue T, g t + a t (u t) = pivotValue j (f t))
    (hanchorU : (∫ t, (j.embedding (u t) - ∫ r in 0..t, v r)
      ∂timeMeasureValue T) = T • j.embedding u₀)
    (hanchorV : (∫ t, (pivotValue j (v t) - ∫ r in 0..t, g r)
      ∂timeMeasureValue T) = T • pivotValue j v₀)
    (henergy : ∀ᵐ t ∂timeMeasureValue T,
      shiftedEnergy j a C t (u t) (v t) ≤ Real.exp (c * t) *
        (shiftedEnergy j a C 0 u₀ v₀ + ∫ r in 0..t, ‖f r‖ ^ 2)) :
    ∃ z : WeakEnergySolution j T a u₀ v₀ f,
      (∀ t ∈ Set.Icc 0 T, ‖z.displacement t‖ ≤ R ∧ ‖z.velocity t‖ ≤ S) ∧
      (∀ t ∈ Set.Icc 0 T,
        shiftedEnergy j a C t (z.displacement t) (z.velocity t) ≤
          Real.exp (c * t) *
            (shiftedEnergy j a C 0 u₀ v₀ + ∫ r in 0..t, ‖f r‖ ^ 2)) ∧
      Tendsto z.displacement (𝓝[Set.Icc 0 T] 0) (𝓝 u₀) ∧
      Tendsto z.velocity (𝓝[Set.Icc 0 T] 0) (𝓝 v₀) := by
  let : IsFiniteMeasure (timeMeasureValue T) :=
    inferInstanceAs (IsFiniteMeasure (volume.restrict (Set.Ioo 0 T)))
  obtain ⟨x, y, hxae, hyae, hbound, hxw, hyw, hxJ, hyP, hxinc, hyinc⟩ :=
    weak_representatives j T hT u v g R S hR hS hu hv hg hub hvb hdu hdv
  have hx0 : x 0 = u₀ := by
    apply j.injective
    apply initial_value_of_integral_anchor T hT (fun t => j.embedding (u t)) v
      (fun t => j.embedding (x t)) (j.embedding u₀)
      (hxae.symm.mono fun t ht => congrArg j.embedding ht) hxinc hanchorU
  have hy0 : y 0 = v₀ := by
    apply pivotInjection_injective j
    apply initial_value_of_integral_anchor T hT (fun t => pivotValue j (v t)) g
      (fun t => pivotValue j (y t)) (pivotValue j v₀)
      (hyae.symm.mono fun t ht => congrArg (pivotValue j) ht) hyinc hanchorV
  have hxmem : MemLp x ∞ (timeMeasureValue T) := (memLp_congr_ae hxae).mpr hu
  have hymem : MemLp y ∞ (timeMeasureValue T) := (memLp_congr_ae hyae).mpr hv
  let z : WeakEnergySolution j T a u₀ v₀ f := {
    displacement := x
    velocity := y
    acceleration := g
    displacement_mem := hxmem
    pivot_displacement_mem := j.embedding.comp_memLp' hxmem
    velocity_mem := hymem
    dual_velocity_mem := ((pivotValue j).comp_memLp' hymem).mono_exponent (by simp)
    acceleration_mem := hg
    displacement_derivative := (hasTimeDerivative_congr T _ _ _ _
      (hxae.symm.mono fun t ht => congrArg j.embedding ht) hyae.symm).mp hdu
    velocity_derivative := (hasTimeDerivative_congr T _ _ _ _
      (hyae.symm.mono fun t ht => congrArg (pivotValue j) ht) EventuallyEq.rfl).mp hdv
    equation := by
      filter_upwards [heq, hxae] with t ht hx
      simpa only [hx] using ht
    displacement_weak := hxw
    velocity_weak := hyw
    initial_displacement := hx0
    initial_velocity := hy0 }
  have hG : ContinuousOn (fun t => Real.exp (c * t) *
      (shiftedEnergy j a C 0 u₀ v₀ + ∫ r in 0..t, ‖f r‖ ^ 2)) (Set.Icc 0 T) :=
    ((continuous_const.mul continuous_id).rexp.continuousOn).mul
      (continuousOn_const.add (forcing_integral_continuousOn T hT.le f))
  have hupper : ∀ t ∈ Set.Icc 0 T,
      shiftedEnergy j a C t (z.displacement t) (z.velocity t) ≤ Real.exp (c * t) *
        (shiftedEnergy j a C 0 u₀ v₀ + ∫ r in 0..t, ‖f r‖ ^ 2) := by
    apply energy_bound_everywhere j T hT a α C ha x y hxw hyw R hR
      (fun t ht => (hbound t ht).1) _ hG
    filter_upwards [henergy, hxae, hyae] with t ht hx hy
    simpa only [hx, hy] using ht
  refine ⟨z, hbound, hupper, ?_⟩
  exact strong_trace_of_gronwall j T hT.le a α C ha u₀ v₀ f z c R hR
    (fun t ht => (hbound t ht).1) hupper


/-- Apply the time-dependent form to a genuinely Bochner measurable state.
Scalar C¹ regularity suffices; no separability premise is imposed. -/
theorem form_apply_memLp (T : ℝ) (a : ℝ → Form V) (ha : ScalarC1 T a)
    (u : ℝ → V) {p : ℝ≥0∞} (hu : MemLp u p (timeMeasureValue T)) :
    MemLp (fun t => a t (u t)) p (timeMeasureValue T) := by
  obtain ⟨M, hM, _, hLip⟩ :=
    ExpandedFA.Evolution.HyperbolicFormBoundsAndCarrier.uniform_bounds T a ha
  have haC : ContinuousOn (fun t => representingOperator (a t)) (Set.Icc 0 T) := by
    have hl : LipschitzOnWith ⟨M, hM⟩
        (fun t => representingOperator (a t)) (Set.Icc 0 T) := by
      apply lipschitzOnWith_iff_norm_sub_le.mpr
      intro t ht s hs
      change ‖representingOperator (a t) - representingOperator (a s)‖ ≤ M * ‖t - s‖
      simpa only [Real.norm_eq_abs] using hLip s hs t ht
    exact hl.continuousOn
  have ham : AEStronglyMeasurable (fun t => representingOperator (a t))
      (timeMeasureValue T) :=
    (haC.mono Set.Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo
  have haum' : AEStronglyMeasurable (fun t => representingOperator (a t) (u t))
      (timeMeasureValue T) :=
    (ContinuousLinearMap.apply ℝ V).flip.aestronglyMeasurable_comp₂ ham hu.aestronglyMeasurable
  have haum : AEStronglyMeasurable (fun t => a t (u t)) (timeMeasureValue T) := by
    convert (InnerProductSpace.toDual ℝ V).continuous.comp_aestronglyMeasurable haum' using 1
    funext t
    ext w
    simp only [InnerProductSpace.toDual_apply_apply,
      HyperbolicFormBoundsAndCarrier.representingOperator_inner]
  obtain ⟨B, hB, hab⟩ :=
    ExpandedFA.Evolution.HyperbolicFormBoundsAndCarrier.form_values_bounded T a ha
  apply ((hu.norm).const_mul B).of_le haum
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  calc
    ‖a t (u t)‖ ≤ ‖a t‖ * ‖u t‖ := (a t).le_opNorm _
    _ ≤ B * ‖u t‖ := mul_le_mul_of_nonneg_right (hab t (Set.Ioo_subset_Icc_self ht)) (norm_nonneg _)
    _ = ‖B * ‖u t‖‖ := by rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hB (norm_nonneg _))]

theorem acceleration_memLp (j : HilbertTriple V H) (T : ℝ) (a : ℝ → Form V)
    (ha : ScalarC1 T a) (u : ℝ → V) (f : timeLpValue H 2 T)
    (hu : MemLp u ∞ (timeMeasureValue T)) :
    MemLp (fun t => pivotValue j (f t) - a t (u t)) 2 (timeMeasureValue T) := by
  let : IsFiniteMeasure (timeMeasureValue T) :=
    inferInstanceAs (IsFiniteMeasure (volume.restrict (Set.Ioo 0 T)))
  exact ((pivotValue j).comp_memLp' (Lp.memLp f)).sub
    (form_apply_memLp T a ha u (hu.mono_exponent (by simp)))

omit [CompleteSpace V] in
theorem derivativeValue_of_evaluations (T : ℝ)
    (b g : ℝ → StrongDual ℝ V)
    (hb : Integrable b (timeMeasureValue T))
    (hg : Integrable g (timeMeasureValue T))
    (heval : ∀ w : V, derivativeValue T (fun t => b t w) (fun t => g t w)) :
    derivativeValue T b g := by
  refine ⟨(show IntegrableOn b (Set.Ioo 0 T) volume from hb).locallyIntegrableOn,
    (show IntegrableOn g (Set.Ioo 0 T) volume from hg).locallyIntegrableOn, ?_⟩
  intro φ hφ
  have hi₁ : Integrable (fun t => deriv φ t • b t) (timeMeasureValue T) :=
    hb.smul_of_top_right ((hφ.1.continuous_deriv (by simp)).memLp_top_of_hasCompactSupport
      hφ.2.1.deriv (timeMeasureValue T))
  have hi₂ : Integrable (fun t => φ t • g t) (timeMeasureValue T) :=
    hg.smul_of_top_right (hφ.1.continuous.memLp_top_of_hasCompactSupport
      hφ.2.1 (timeMeasureValue T))
  apply ContinuousLinearMap.ext
  intro w
  rw [ContinuousLinearMap.integral_apply hi₁, neg_apply,
    ContinuousLinearMap.integral_apply hi₂]
  exact (heval w).2.2 φ hφ

theorem velocity_derivative_of_wave_tests (j : HilbertTriple V H) (T : ℝ)
    (a : ℝ → Form V) (ha : ScalarC1 T a)
    (u : ℝ → V) (v : ℝ → H) (f : timeLpValue H 2 T)
    (hu : MemLp u ∞ (timeMeasureValue T))
    (hv : MemLp v ∞ (timeMeasureValue T))
    (heq : WaveTestEquation j T a u v f) :
    derivativeValue T (fun t => pivotValue j (v t))
      (fun t => pivotValue j (f t) - a t (u t)) := by
  let : IsFiniteMeasure (timeMeasureValue T) :=
    inferInstanceAs (IsFiniteMeasure (volume.restrict (Set.Ioo 0 T)))
  apply derivativeValue_of_evaluations
  · exact ((pivotValue j).comp_memLp' hv).integrable (by simp)
  · exact (acceleration_memLp j T a ha u f hu).integrable (by norm_num)
  · intro w
    change derivativeValue T (fun t => pivotInjection j (v t) w)
      (fun t => (pivotInjection j (f t) - a t (u t)) w)
    simpa only [pivotInjection_apply, sub_apply] using heq w


/-- The complete existence and estimate conclusion at zero duration. The
prescribed data determine the singleton state, so this needs no coercivity. -/
theorem weak_existence_zero (j : HilbertTriple V H) (a : ℝ → Form V) (C : ℝ) :
    ∃ c K : ℝ, 0 ≤ c ∧ 0 ≤ K ∧
      ∀ (u₀ : V) (v₀ : H) (f : timeLpValue H 2 0),
        ∃ z : WeakEnergySolution j 0 a u₀ v₀ f,
          (∀ t ∈ Set.Icc (0 : ℝ) 0,
            shiftedEnergy j a C t (z.displacement t) (z.velocity t) ≤
              Real.exp (c * t) *
                (shiftedEnergy j a C 0 u₀ v₀ + ∫ r in 0..t, ‖f r‖ ^ 2)) ∧
          (∀ t ∈ Set.Icc (0 : ℝ) 0,
            ‖z.displacement t‖ ^ 2 + ‖z.velocity t‖ ^ 2 ≤
              K * (‖u₀‖ ^ 2 + ‖v₀‖ ^ 2 + ‖f‖ ^ 2)) ∧
          Tendsto z.displacement (𝓝[Set.Icc 0 0] 0) (𝓝 u₀) ∧
          Tendsto z.velocity (𝓝[Set.Icc 0 0] 0) (𝓝 v₀) := by
  refine ⟨0, 1, le_rfl, zero_le_one, ?_⟩
  intro u₀ v₀ f
  obtain ⟨z, _, hx, hy⟩ := zero_time_solution j a u₀ v₀ f
  refine ⟨z, ?_, ?_, hx, hy⟩
  · intro t ht
    have ht0 : t = 0 := le_antisymm ht.2 ht.1
    subst t
    simp [z.initial_displacement, z.initial_velocity]
  · intro t ht
    have ht0 : t = 0 := le_antisymm ht.2 ht.1
    subst t
    simp only [z.initial_displacement, z.initial_velocity, one_mul]
    exact le_add_of_nonneg_right (sq_nonneg ‖f‖)

section WeakGraph


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The actual vector-valued integral against an L² scalar test is continuous linear on L². -/
def testIntegralCLM (T : ℝ) (φ : ℝ → ℝ)
    (hφ : MemLp φ 2 (timeMeasureValue T)) :
    Lp E 2 (timeMeasureValue T) →L[ℝ] E :=
  (ContinuousLinearMap.lsmul ℝ ℝ).lpPairing (timeMeasureValue T) 2 2 (hφ.toLp φ)

theorem testIntegralCLM_eq (T : ℝ) (φ : ℝ → ℝ)
    (hφ : MemLp φ 2 (timeMeasureValue T)) (u : Lp E 2 (timeMeasureValue T)) :
    testIntegralCLM T φ hφ u = ∫ t, φ t • u t ∂timeMeasureValue T := by
  rw [testIntegralCLM, ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [hφ.coeFn_toLp] with t ht
  simp only [ContinuousLinearMap.lsmul_apply, ht]

/-- The distributional derivative graph is closed under simultaneous weak L² limits. -/
theorem derivativeValue_of_weak_L2_limits {ι : Type*} (F : Filter ι) [NeBot F]
    (T : ℝ)
    (u g : ι → Lp E 2 (timeMeasureValue T))
    (x y : Lp E 2 (timeMeasureValue T))
    (hu : ∀ L : StrongDual ℝ (Lp E 2 (timeMeasureValue T)),
      Tendsto (fun i => L (u i)) F (𝓝 (L x)))
    (hg : ∀ L : StrongDual ℝ (Lp E 2 (timeMeasureValue T)),
      Tendsto (fun i => L (g i)) F (𝓝 (L y)))
    (hgraph : ∀ᶠ i in F, derivativeValue T (u i) (g i)) :
    derivativeValue T x y := by
  let : IsFiniteMeasure (timeMeasureValue T) :=
    inferInstanceAs (IsFiniteMeasure (volume.restrict (Set.Ioo 0 T)))
  have hx : Integrable x (timeMeasureValue T) := (Lp.memLp x).integrable (by norm_num)
  have hy : Integrable y (timeMeasureValue T) := (Lp.memLp y).integrable (by norm_num)
  refine ⟨(show IntegrableOn x (Set.Ioo 0 T) volume from hx).locallyIntegrableOn,
    (show IntegrableOn y (Set.Ioo 0 T) volume from hy).locallyIntegrableOn, ?_⟩
  intro φ hφ
  have hφ₂ : MemLp φ 2 (timeMeasureValue T) :=
    (hφ.1.continuous.memLp_top_of_hasCompactSupport hφ.2.1 _).mono_exponent (by simp)
  have hdφ₂ : MemLp (deriv φ) 2 (timeMeasureValue T) :=
    ((hφ.1.continuous_deriv (by simp)).memLp_top_of_hasCompactSupport
      hφ.2.1.deriv _).mono_exponent (by simp)
  let A : Lp E 2 (timeMeasureValue T) →L[ℝ] E := testIntegralCLM T (deriv φ) hdφ₂
  let B : Lp E 2 (timeMeasureValue T) →L[ℝ] E := testIntegralCLM T φ hφ₂
  have hA (v : Lp E 2 (timeMeasureValue T)) :
      A v = ∫ t, deriv φ t • v t ∂timeMeasureValue T := testIntegralCLM_eq _ _ _ _
  have hB (v : Lp E 2 (timeMeasureValue T)) :
      B v = ∫ t, φ t • v t ∂timeMeasureValue T := testIntegralCLM_eq _ _ _ _
  rw [← hA, ← hB]
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
  intro L
  rw [map_neg]
  have he : ∀ᶠ i in F, (L.comp A) (u i) = -((L.comp B) (g i)) := by
    filter_upwards [hgraph] with i hi
    change L (A (u i)) = -(L (B (g i)))
    rw [hA, hB, (hi.2.2 φ hφ), map_neg]
  exact tendsto_nhds_unique ((hu (L.comp A)).congr' he) ((hg (L.comp B)).neg)


end WeakGraph

/- Weak compactness and integrated quadratic-energy passage. -/

open Filter
open scoped Topology ENNReal

namespace WeakCompactness
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Every uniformly bounded Hilbert-valued net has a weakly convergent
ultrafilter refinement, without any separability hypothesis. -/
theorem exists_weak_limit {ι : Type*} (F : Filter ι) [NeBot F]
    (z : ι → E) (R : ℝ) (hz : ∀ᶠ i in F, ‖z i‖ ≤ R) :
    ∃ (x : E) (U : Ultrafilter ι), U ≤ F ∧ ‖x‖ ≤ R ∧
      ∀ L : StrongDual ℝ E, Tendsto (fun i => L (z i)) U (𝓝 (L x)) := by
  let w : ι → WeakDual ℝ E := fun i => ((InnerProductSpace.toDual ℝ E) (z i)).toWeakDual
  have hw : ∀ᶠ i in F, w i ∈ WeakDual.toStrongDual ⁻¹'
      Metric.closedBall (0 : StrongDual ℝ E) R := by
    filter_upwards [hz] with i hi
    simpa only [w, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right,
      StrongDual.toStrongDual_toWeakDual, LinearIsometryEquiv.norm_map] using hi
  obtain ⟨p, hp, hpc⟩ := (WeakDual.isCompact_closedBall
    (0 : StrongDual ℝ E) R).exists_mapClusterPt (Filter.le_principal_iff.mpr hw)
  obtain ⟨U, hUF, hU⟩ := mapClusterPt_iff_ultrafilter.mp hpc
  let x : E := (InnerProductSpace.toDual ℝ E).symm p.toStrongDual
  refine ⟨x, U, hUF, ?_, ?_⟩
  · simpa only [x, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right,
      LinearIsometryEquiv.norm_map] using hp
  · intro L
    have he : Tendsto (fun i => w i ((InnerProductSpace.toDual ℝ E).symm L))
        U (𝓝 (p ((InnerProductSpace.toDual ℝ E).symm L))) :=
      (WeakDual.eval_continuous _).continuousAt.tendsto.comp hU
    convert he using 1
    · funext i
      change L (z i) = inner ℝ (z i) ((InnerProductSpace.toDual ℝ E).symm L)
      rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
    · congr 1
      change L ((InnerProductSpace.toDual ℝ E).symm p.toStrongDual) = _
      rw [← InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (y := L), real_inner_comm,
        InnerProductSpace.toDual_symm_apply]
      rfl

/-- A common refinement gives simultaneous weak limits in two original Hilbert spaces. -/
theorem exists_weak_pair_limit {B : Type*}
    [NormedAddCommGroup B] [InnerProductSpace ℝ B] [CompleteSpace B]
    {ι : Type*} (F : Filter ι) [NeBot F]
    (z : ι → E) (w : ι → B) (R S : ℝ)
    (hz : ∀ᶠ i in F, ‖z i‖ ≤ R) (hw : ∀ᶠ i in F, ‖w i‖ ≤ S) :
    ∃ (x : E) (y : B) (U : Ultrafilter ι), U ≤ F ∧ ‖x‖ ≤ R ∧ ‖y‖ ≤ S ∧
      (∀ L : StrongDual ℝ E, Tendsto (fun i => L (z i)) U (𝓝 (L x))) ∧
      (∀ L : StrongDual ℝ B, Tendsto (fun i => L (w i)) U (𝓝 (L y))) := by
  obtain ⟨x, U, hUF, hx, hzx⟩ := exists_weak_limit F z R hz
  obtain ⟨y, W, hWU, hy, hwy⟩ := exists_weak_limit (U : Filter ι) w S (hw.filter_mono hUF)
  exact ⟨x, y, W, hWU.trans hUF, hx, hy, fun L => (hzx L).mono_left hWU, hwy⟩

/-- Positivity supplies affine lower supports for a symmetric continuous
bilinear quadratic form. Thus weak limits inherit converging upper bounds. -/
theorem quadratic_bound_of_weak_limit {Q : Type*}
    [NormedAddCommGroup Q] [NormedSpace ℝ Q] {ι : Type*} (F : Filter ι) [NeBot F]
    (b : Q →L[ℝ] Q →L[ℝ] ℝ)
    (hsymm : ∀ x y, b x y = b y x) (hpos : ∀ x, 0 ≤ b x x)
    (z : ι → Q) (x : Q)
    (hweak : ∀ L : StrongDual ℝ Q, Tendsto (fun i => L (z i)) F (𝓝 (L x)))
    (G : ι → ℝ) (r : ℝ) (hG : Tendsto G F (𝓝 r))
    (hbound : ∀ᶠ i in F, b (z i) (z i) ≤ G i) : b x x ≤ r := by
  have hsupp : ∀ y, 2 * b y x - b x x ≤ b y y := by
    intro y
    have hp := hpos (y - x)
    simp only [map_sub, sub_apply] at hp
    rw [hsymm x y] at hp
    linarith
  have ht : Tendsto (fun i => 2 * b (z i) x - b x x) F (𝓝 (b x x)) := by
    convert ((hweak (b.flip x)).const_mul 2).sub_const (b x x) using 1 <;> simp <;> ring
  have hle : ∀ᶠ i in F, 2 * b (z i) x - b x x ≤ G i := by
    filter_upwards [hbound] with i hi
    exact (hsupp (z i)).trans hi
  exact le_of_tendsto_of_tendsto ht hG hle

section ClosedConvex
variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]

/-- A norm-closed convex condition survives weak convergence. -/
theorem mem_closed_convex_of_weak_limit {ι : Type*} (F : Filter ι) [NeBot F]
    (D : Set B) (hD : IsClosed D) (hc : Convex ℝ D)
    (z : ι → B) (x : B)
    (hweak : ∀ L : StrongDual ℝ B, Tendsto (fun i => L (z i)) F (𝓝 (L x)))
    (hmem : ∀ᶠ i in F, z i ∈ D) : x ∈ D := by
  by_contra hx
  obtain ⟨L, r, hL, hxr⟩ := geometric_hahn_banach_closed_point hc hD hx
  have hle : L x ≤ r := le_of_tendsto (hweak L) <| hmem.mono fun i hi => (hL _ hi).le
  exact hxr.not_ge hle

open MeasureTheory
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Almost-everywhere membership in a closed target is closed for Lp norm convergence. -/
theorem isClosed_ae_mem (D : Set B) (hD : IsClosed D) :
    IsClosed {f : Lp B p μ | ∀ᵐ t ∂μ, f t ∈ D} := by
  apply IsSeqClosed.isClosed
  intro f x hf hfx
  obtain ⟨φ, _, hφ⟩ := (tendstoInMeasure_of_tendsto_Lp hfx).exists_seq_tendsto_ae
  filter_upwards [countable_iInter_mem.mpr hf, hφ] with t ht hφt
  exact hD.mem_of_tendsto hφt (Eventually.of_forall fun n => Set.mem_iInter.mp ht (φ n))

/-- Almost-everywhere membership in a convex target is convex in Lp. -/
theorem convex_ae_mem (D : Set B) (hD : Convex ℝ D) :
    Convex ℝ {f : Lp B p μ | ∀ᵐ t ∂μ, f t ∈ D} := by
  intro f hf g hg a b ha hb hab
  filter_upwards [hf, hg, Lp.coeFn_add (a • f) (b • g),
    Lp.coeFn_smul a f, Lp.coeFn_smul b g] with t hft hgt hadd haeq hbeq
  rw [hadd, Pi.add_apply, haeq, hbeq]
  exact hD hft hgt ha hb hab

/-- Weak Lp limits preserve an a.e. bound in the target norm. -/
theorem ae_norm_le_of_weak_limit {ι : Type*} (F : Filter ι) [NeBot F]
    (z : ι → Lp B p μ) (x : Lp B p μ) (R : ℝ)
    (hweak : ∀ L : StrongDual ℝ (Lp B p μ),
      Tendsto (fun i => L (z i)) F (𝓝 (L x)))
    (hbound : ∀ᶠ i in F, ∀ᵐ t ∂μ, ‖z i t‖ ≤ R) :
    ∀ᵐ t ∂μ, ‖x t‖ ≤ R := by
  simpa only [Set.mem_ofPred_eq, Metric.mem_closedBall, dist_zero_right] using
    (mem_closed_convex_of_weak_limit F
    {f : Lp B p μ | ∀ᵐ t ∂μ, f t ∈ Metric.closedBall 0 R}
    (isClosed_ae_mem _ Metric.isClosed_closedBall) (convex_ae_mem _ (convex_closedBall 0 R))
    z x hweak (by simpa only [Set.mem_ofPred_eq, Metric.mem_closedBall, dist_zero_right] using hbound))

end ClosedConvex

end WeakCompactness

open MeasureTheory Filter
open scoped Topology ENNReal
namespace WeakCompactness

variable {V Ω : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [MeasurableSpace Ω] {μ : Measure Ω}

/-- The bounded, strongly measurable variable form induces an integrated
continuous bilinear form on L² of the original Hilbert space. -/
def integratedForm (a : Lp (V →L[ℝ] V →L[ℝ] ℝ) ∞ μ) :
    Lp V 2 μ →L[ℝ] Lp V 2 μ →L[ℝ] ℝ :=
  ((ContinuousLinearMap.id ℝ (V →L[ℝ] ℝ)).lpPairing μ 2 2).comp
    ((ContinuousLinearMap.id ℝ (V →L[ℝ] V →L[ℝ] ℝ)).holderL μ ∞ 2 2 a)

theorem integratedForm_eq_integral (a : Lp (V →L[ℝ] V →L[ℝ] ℝ) ∞ μ)
    (u v : Lp V 2 μ) :
    integratedForm a u v = ∫ t, a t (u t) (v t) ∂μ := by
  rw [integratedForm, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [ContinuousLinearMap.coeFn_holder (𝕜 := ℝ)
    (E := V →L[ℝ] V →L[ℝ] ℝ) (F := V) (G := V →L[ℝ] ℝ)
    (p := ∞) (q := 2) (r := 2)
    (ContinuousLinearMap.id ℝ (V →L[ℝ] V →L[ℝ] ℝ)) a u] with t ht
  simpa only [ContinuousLinearMap.id_apply, ContinuousLinearMap.holderL_apply_apply] using
    congrArg (fun p : V →L[ℝ] ℝ => p (v t)) ht

theorem integratedForm_symmetric (a : Lp (V →L[ℝ] V →L[ℝ] ℝ) ∞ μ)
    (ha : ∀ᵐ t ∂μ, ∀ x y, a t x y = a t y x) (u v : Lp V 2 μ) :
    integratedForm a u v = integratedForm a v u := by
  rw [integratedForm_eq_integral, integratedForm_eq_integral]
  exact integral_congr_ae (ha.mono fun t ht => ht _ _)

theorem integratedForm_nonneg (a : Lp (V →L[ℝ] V →L[ℝ] ℝ) ∞ μ)
    (ha : ∀ᵐ t ∂μ, ∀ x, 0 ≤ a t x x) (u : Lp V 2 μ) :
    0 ≤ integratedForm a u u := by
  rw [integratedForm_eq_integral]
  exact integral_nonneg_of_ae (ha.mono fun t ht => ht _)

theorem integratedForm_bound_of_weak_limit {ι : Type*}
    (F : Filter ι) [NeBot F]
    (a : Lp (V →L[ℝ] V →L[ℝ] ℝ) ∞ μ)
    (hsymm : ∀ᵐ t ∂μ, ∀ x y, a t x y = a t y x)
    (hpos : ∀ᵐ t ∂μ, ∀ x, 0 ≤ a t x x)
    (u : ι → Lp V 2 μ) (x : Lp V 2 μ)
    (hweak : ∀ L : StrongDual ℝ (Lp V 2 μ),
      Tendsto (fun i => L (u i)) F (𝓝 (L x)))
    (G : ι → ℝ) (r : ℝ) (hG : Tendsto G F (𝓝 r))
    (hbound : ∀ᶠ i in F, (∫ t, a t (u i t) (u i t) ∂μ) ≤ G i) :
    (∫ t, a t (x t) (x t) ∂μ) ≤ r := by
  rw [← integratedForm_eq_integral]
  apply quadratic_bound_of_weak_limit F (integratedForm a)
    (integratedForm_symmetric a hsymm) (integratedForm_nonneg a hpos)
    u x hweak G r hG
  simpa only [integratedForm_eq_integral] using hbound

set_option maxHeartbeats 800000 in
/-- The quadratic density is genuinely Bochner integrable. -/
theorem integrable_quadratic (a : Lp (V →L[ℝ] V →L[ℝ] ℝ) ∞ μ)
    (u : Lp V 2 μ) : Integrable (fun t => a t (u t) (u t)) μ := by
  have hAu : MemLp (fun t => a t (u t)) 2 μ :=
    ContinuousLinearMap.memLp_of_bilin (𝕜 := ℝ)
      (E := V →L[ℝ] V →L[ℝ] ℝ) (F := V) (G := V →L[ℝ] ℝ)
      (p := ∞) (q := 2) (r := 2)
      (ContinuousLinearMap.id ℝ (V →L[ℝ] V →L[ℝ] ℝ)) (Lp.memLp a) (Lp.memLp u)
  exact memLp_one_iff_integrable.mp <|
    ContinuousLinearMap.memLp_of_bilin (𝕜 := ℝ)
      (E := V →L[ℝ] ℝ) (F := V) (G := ℝ)
      (p := 2) (q := 2) (r := 1)
      (ContinuousLinearMap.id ℝ (V →L[ℝ] ℝ)) hAu (Lp.memLp u)

/-- Localize the coefficient, leaving weak convergence on the original L² space. -/
def indicatorForm (a : Lp (V →L[ℝ] V →L[ℝ] ℝ) ∞ μ)
    (s : Set Ω) (hs : MeasurableSet s) : Lp (V →L[ℝ] V →L[ℝ] ℝ) ∞ μ :=
  (MemLp.indicator hs.nullMeasurableSet (Lp.memLp a)).toLp (s.indicator a)

theorem coeFn_indicatorForm (a : Lp (V →L[ℝ] V →L[ℝ] ℝ) ∞ μ)
    (s : Set Ω) (hs : MeasurableSet s) :
    indicatorForm a s hs =ᵐ[μ] s.indicator a :=
  MemLp.coeFn_toLp _

theorem integral_indicatorForm (a : Lp (V →L[ℝ] V →L[ℝ] ℝ) ∞ μ)
    (s : Set Ω) (hs : MeasurableSet s) (u : Lp V 2 μ) :
    (∫ t, indicatorForm a s hs t (u t) (u t) ∂μ) = ∫ t in s, a t (u t) (u t) ∂μ := by
  rw [← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [coeFn_indicatorForm a s hs] with t ht
  rw [ht]
  by_cases hts : t ∈ s <;> simp [Set.indicator_apply, hts]

/-- Positive quadratic energy bounds pass from a weak L² Galerkin limit
through every measurable time subset, hence hold almost everywhere. -/
theorem ae_quadratic_bound_of_weak_limit {ι : Type*} (F : Filter ι) [NeBot F]
    (a : Lp (V →L[ℝ] V →L[ℝ] ℝ) ∞ μ)
    (hsymm : ∀ᵐ t ∂μ, ∀ x y, a t x y = a t y x)
    (hpos : ∀ᵐ t ∂μ, ∀ x, 0 ≤ a t x x)
    (u : ι → Lp V 2 μ) (x : Lp V 2 μ)
    (hweak : ∀ L : StrongDual ℝ (Lp V 2 μ),
      Tendsto (fun i => L (u i)) F (𝓝 (L x)))
    (G : Ω → ℝ) (hG : Integrable G μ)
    (hbound : ∀ᶠ i in F, ∀ᵐ t ∂μ, a t (u i t) (u i t) ≤ G t) :
    ∀ᵐ t ∂μ, a t (x t) (x t) ≤ G t := by
  apply ae_le_of_forall_setIntegral_le (integrable_quadratic a x) hG
  intro s hs _
  have hasymm : ∀ᵐ t ∂μ, ∀ v w,
      indicatorForm a s hs t v w = indicatorForm a s hs t w v := by
    filter_upwards [coeFn_indicatorForm a s hs, hsymm] with t ht ht'
    rw [ht]
    by_cases hts : t ∈ s
    · simpa only [Set.indicator_of_mem hts] using ht'
    · simp [Set.indicator_of_notMem hts]
  have hapos : ∀ᵐ t ∂μ, ∀ v, 0 ≤ indicatorForm a s hs t v v := by
    filter_upwards [coeFn_indicatorForm a s hs, hpos] with t ht ht'
    rw [ht]
    by_cases hts : t ∈ s
    · simpa only [Set.indicator_of_mem hts] using ht'
    · simp [Set.indicator_of_notMem hts]
  have hbound' : ∀ᶠ i in F,
      (∫ t, indicatorForm a s hs t (u i t) (u i t) ∂μ) ≤ ∫ t in s, G t ∂μ := by
    filter_upwards [hbound] with i hi
    rw [integral_indicatorForm]
    exact integral_mono_ae (integrable_quadratic a (u i)).integrableOn
      hG.integrableOn (ae_restrict_of_ae hi)
  have h := integratedForm_bound_of_weak_limit F (indicatorForm a s hs) hasymm hapos
    u x hweak (fun _ => ∫ t in s, G t ∂μ) _ tendsto_const_nhds hbound'
  rwa [integral_indicatorForm] at h

end WeakCompactness

/- Finite mass systems, including the original scalar-C¹ form specialization. -/
section FiniteConstruction

open Function intervalIntegral MeasureTheory Metric Set Filter
open scoped Nat NNReal Topology
namespace Volterra
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {T : ℝ} (hT : 0 ≤ T)
local notation "I" => Set.Icc (0 : ℝ) T

def extend (u : C(I,E)) (t : ℝ) : E := u (projIcc 0 T hT t)

lemma continuous_extend (u : C(I,E)) : Continuous (extend hT u) :=
  u.continuous.comp continuous_projIcc

lemma extend_of_mem (u : C(I,E)) {t : ℝ} (ht : t ∈ I) :
    extend hT u t = u ⟨t,ht⟩ := by simp [extend, projIcc_of_mem hT ht]

variable (f : ℝ → E → E) (g : ℝ → E) (x₀ : E)
variable (hf : ContinuousOn (uncurry f) ((Set.Icc (0 : ℝ) T) ×ˢ univ))
variable (hg : IntervalIntegrable g volume 0 T)
include hf hg

omit hg in
lemma integrable_drift (u : C(I,E)) :
    IntervalIntegrable (fun t => f t (extend hT u t)) volume 0 T := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hT]
  exact hf.comp (continuousOn_id.prodMk (continuous_extend hT u).continuousOn)
    (fun _ ht => ⟨ht, mem_univ _⟩)

lemma integrable_integrand (u : C(I,E)) :
    IntervalIntegrable (fun t => f t (extend hT u t) + g t) volume 0 T :=
  (integrable_drift hT f hf u).add hg

def next (hf : ContinuousOn (uncurry f) ((Set.Icc (0 : ℝ) T) ×ˢ univ))
    (hg : IntervalIntegrable g volume 0 T) (u : C(I,E)) : C(I,E) where
  toFun t := x₀ + ∫ r in 0..t.val, f r (extend hT u r) + g r
  continuous_toFun := by
    have hi : ContinuousOn (fun t : ℝ => x₀ + ∫ r in 0..t, f r (extend hT u r) + g r) I := by
      apply continuousOn_const.add
      simpa [uIcc_of_le hT] using
        continuousOn_primitive_interval' (integrable_integrand hT f g hf hg u)
          (left_mem_uIcc : (0 : ℝ) ∈ uIcc 0 T)
    exact hi.comp_continuous continuous_subtype_val (fun t => t.2)

@[simp] lemma next_apply (u : C(I,E)) (t : I) :
    next hT f g x₀ hf hg u t = x₀ + ∫ r in 0..t.val, f r (extend hT u r) + g r := rfl

variable {f g x₀ hf hg}
variable {K : ℝ≥0} (hK : ∀ t ∈ Set.Icc (0 : ℝ) T, LipschitzWith K (f t))
include hT hK

lemma dist_iterate_next_apply_le (u v : C(I,E)) (n : ℕ) (t : I) :
    dist (((next hT f g x₀ hf hg)^[n] u) t) (((next hT f g x₀ hf hg)^[n] v) t) ≤
      (K * |t.val|) ^ n / n ! * dist u v := by
  induction n generalizing t with
  | zero => simpa using ContinuousMap.dist_apply_le_dist (f := u) (g := v) t
  | succ n hn =>
    rw [iterate_succ_apply', iterate_succ_apply', dist_eq_norm, next_apply,
      next_apply, add_sub_add_left_eq_sub,
      ← intervalIntegral.integral_sub
        ((integrable_integrand hT f g hf hg _).mono_set (by simpa [uIcc_of_le hT] using uIcc_subset_Icc ⟨le_rfl,hT⟩ t.2))
        ((integrable_integrand hT f g hf hg _).mono_set (by simpa [uIcc_of_le hT] using uIcc_subset_Icc ⟨le_rfl,hT⟩ t.2))]
    calc
      _ ≤ ∫ r in uIoc 0 t.val, K ^ (n + 1) * |r| ^ n / n ! * dist u v := by
        rw [intervalIntegral.norm_intervalIntegral_eq]
        apply MeasureTheory.norm_integral_le_of_norm_le (Continuous.integrableOn_uIoc (by fun_prop))
        apply ae_restrict_mem measurableSet_Ioc |>.mono
        intro r hr
        have hrI : r ∈ I := subset_trans uIoc_subset_uIcc
          (uIcc_subset_Icc ⟨le_rfl,hT⟩ t.2) hr
        rw [add_sub_add_right_eq_sub, ← dist_eq_norm, extend_of_mem _ _ hrI,
          extend_of_mem _ _ hrI]
        calc
          _ ≤ K * dist (((next hT f g x₀ hf hg)^[n] u) ⟨r,hrI⟩)
            (((next hT f g x₀ hf hg)^[n] v) ⟨r,hrI⟩) := (hK r hrI).dist_le_mul _ _
          _ ≤ K ^ (n + 1) * |r| ^ n / n ! * dist u v := by
            rw [pow_succ', mul_assoc, mul_div_assoc, mul_assoc]
            gcongr
            simpa [← mul_pow] using hn ⟨r,hrI⟩
      _ ≤ (K * |t.val|) ^ (n + 1) / (n + 1) ! * dist u v := by
        apply le_of_abs_le
        rw [← intervalIntegral.abs_intervalIntegral_eq, intervalIntegral.integral_mul_const,
          intervalIntegral.integral_div, intervalIntegral.integral_const_mul, abs_mul, abs_div,
          abs_mul, intervalIntegral.abs_intervalIntegral_eq]
        have hp := integral_pow_abs_sub_uIoc (a := (0 : ℝ)) (b := t.val) n
        simp only [sub_zero] at hp
        rw [hp, abs_div, abs_pow, abs_pow, abs_dist, NNReal.abs_eq, abs_abs,
          mul_div, div_div, ← abs_mul, ← Nat.cast_succ, ← Nat.cast_mul,
          ← Nat.factorial_succ, Nat.abs_cast, ← mul_pow]

lemma dist_iterate_next_le (u v : C(I,E)) (n : ℕ) :
    dist ((next hT f g x₀ hf hg)^[n] u) ((next hT f g x₀ hf hg)^[n] v) ≤
      (K * T) ^ n / n ! * dist u v := by
  rw [ContinuousMap.dist_le]
  · intro t
    apply (dist_iterate_next_apply_le hT hK u v n t).trans
    gcongr
    exact (abs_le.mpr ⟨by linarith [t.2.1],t.2.2⟩)
  · positivity

lemma exists_solution : ∃ u : C(I,E), ∀ t : I,
    u t = x₀ + ∫ r in 0..t.val, f r (extend hT u r) + g r := by
  obtain ⟨n, hn⟩ := FloorSemiring.tendsto_pow_div_factorial_atTop (K * T)
    |>.eventually (gt_mem_nhds zero_lt_one) |>.exists
  have hnonneg : 0 ≤ (K * T) ^ n / (n ! : ℝ) := by positivity
  have hc : ContractingWith ⟨_,hnonneg⟩ (next hT f g x₀ hf hg)^[n] :=
    ⟨hn,LipschitzWith.of_dist_le_mul fun u v => dist_iterate_next_le hT hK u v n⟩
  refine ⟨_,fun t => (congrArg (fun u : C(I,E) => u t) hc.isFixedPt_fixedPoint_iterate).symm⟩

lemma exists_solution_real : ∃ u : ℝ → E, Continuous u ∧ u 0 = x₀ ∧
    (∀ t ∈ I, u t = x₀ + ∫ r in 0..t, f r (u r) + g r) ∧
    (∀ s ∈ I, ∀ t ∈ I, u t - u s = ∫ r in s..t, f r (u r) + g r) := by
  obtain ⟨u,hu⟩ := exists_solution hT (hf := hf) (hg := hg) (x₀ := x₀) hK
  have heq : ∀ t ∈ I, extend hT u t = x₀ + ∫ r in 0..t, f r (extend hT u r) + g r := by
    intro t ht
    rw [extend_of_mem hT u ht]
    exact hu ⟨t,ht⟩
  refine ⟨extend hT u,continuous_extend hT u,?_,heq,?_⟩
  · simpa using heq 0 ⟨le_rfl,hT⟩
  · intro s hs t ht
    rw [heq t ht,heq s hs,add_sub_add_left_eq_sub]
    apply integral_interval_sub_left
    · exact (integrable_integrand hT f g hf hg u).mono_set
        (by simpa [uIcc_of_le hT] using uIcc_subset_Icc ⟨le_rfl,hT⟩ ht)
    · exact (integrable_integrand hT f g hf hg u).mono_set
        (by simpa [uIcc_of_le hT] using uIcc_subset_Icc ⟨le_rfl,hT⟩ hs)

omit hf hg hK in
lemma linear_exists_solution (A : ℝ → E →L[ℝ] E)
    (hA : ContinuousOn A I) (g : ℝ → E) (hg : IntervalIntegrable g volume 0 T) (x₀ : E) :
    ∃ u : ℝ → E, Continuous u ∧ u 0 = x₀ ∧
      (∀ t ∈ I, u t = x₀ + ∫ r in 0..t, A r (u r) + g r) ∧
      (∀ s ∈ I, ∀ t ∈ I, u t - u s = ∫ r in s..t, A r (u r) + g r) := by
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hA
  have hB0 : 0 ≤ B := (norm_nonneg (A 0)).trans (hB 0 ⟨le_rfl,hT⟩)
  let K : ℝ≥0 := ⟨B,hB0⟩
  have hK : ∀ t ∈ I, LipschitzWith K (fun x => A t x) := by
    intro t ht
    apply (A t).lipschitzWith.weaken
    exact hB t ht
  have hf : ContinuousOn (uncurry (fun t x => A t x)) (I ×ˢ (univ : Set E)) := by
    exact (hA.comp continuousOn_fst (fun _ ht => ht.1)).clm_apply continuousOn_snd
  exact exists_solution_real hT (hf := hf) (hg := hg) (x₀ := x₀) hK

omit hf hg hK hT in
def phaseOperator (A : E →L[ℝ] E) : E × E →L[ℝ] E × E :=
  (ContinuousLinearMap.snd ℝ E E).prod (-(A.comp (ContinuousLinearMap.fst ℝ E E)))

omit hf hg hK hT in
@[simp] lemma phaseOperator_apply (A : E →L[ℝ] E) (p : E × E) :
    phaseOperator A p = (p.2, -(A p.1)) := rfl

omit hf hg hK in
lemma wave_exists_solution (A : ℝ → E →L[ℝ] E) (hA : ContinuousOn A I)
    (g : ℝ → E) (hg : IntervalIntegrable g volume 0 T) (u₀ v₀ : E) :
    ∃ u v : ℝ → E, Continuous u ∧ Continuous v ∧ u 0 = u₀ ∧ v 0 = v₀ ∧
      (∀ s ∈ I, ∀ t ∈ I, u t - u s = ∫ r in s..t, v r) ∧
      (∀ s ∈ I, ∀ t ∈ I, v t - v s = ∫ r in s..t, -(A r (u r)) + g r) := by
  have hP : ContinuousOn (fun t => phaseOperator (A t)) I := by
    have hc : ContinuousOn (fun t => -(A t).comp (ContinuousLinearMap.fst ℝ E E)) I := by
      fun_prop
    exact (ContinuousLinearMap.prodₗᵢ ℝ).continuous.comp_continuousOn
      (continuousOn_const.prodMk hc)
  have hgP : IntervalIntegrable (fun t => ((0 : E), g t)) volume 0 T :=
    ⟨(integrable_const (0 : E)).prodMk hg.1,(integrable_const (0 : E)).prodMk hg.2⟩
  obtain ⟨z,hzc,hz0,hz,hzi⟩ :=
    linear_exists_solution hT (fun t => phaseOperator (A t)) hP _ hgP (u₀,v₀)
  refine ⟨fun t => (z t).1,fun t => (z t).2,hzc.fst,hzc.snd,?_,?_,?_,?_⟩
  · exact congrArg Prod.fst hz0
  · exact congrArg Prod.snd hz0
  · intro s hs t ht
    have hint : IntervalIntegrable (fun r => phaseOperator (A r) (z r) + (0,g r)) volume s t :=
      ((hP.clm_apply hzc.continuousOn).mono (uIcc_subset_Icc hs ht)).intervalIntegrable.add (hgP.mono_set
          (by simpa [uIcc_of_le hT] using uIcc_subset_Icc hs ht))
    have h := congrArg Prod.fst (hzi s hs t ht)
    simpa using h.trans ((ContinuousLinearMap.fst ℝ E E).intervalIntegral_comp_comm hint).symm
  · intro s hs t ht
    have hint : IntervalIntegrable (fun r => phaseOperator (A r) (z r) + (0,g r)) volume s t :=
      ((hP.clm_apply hzc.continuousOn).mono (uIcc_subset_Icc hs ht)).intervalIntegrable.add (hgP.mono_set
          (by simpa [uIcc_of_le hT] using uIcc_subset_Icc hs ht))
    have h := congrArg Prod.snd (hzi s hs t ht)
    simpa using h.trans ((ContinuousLinearMap.snd ℝ E E).intervalIntegral_comp_comm hint).symm

end Volterra

namespace MassWave
variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The positive definite mass operator, with the original trial-space norm. -/
def massEquiv (J : E →L[ℝ] H) (hJ : Function.Injective J) : E ≃L[ℝ] E :=
  (LinearEquiv.ofInjectiveEndo (J.adjoint.comp J).toLinearMap
    (J.adjoint_comp_self_injective_iff.mpr hJ)).toContinuousLinearEquiv

@[simp] lemma massEquiv_apply (J : E →L[ℝ] H) (hJ : Function.Injective J) (x : E) :
    massEquiv J hJ x = J.adjoint (J x) := rfl

lemma mass_inner (J : E →L[ℝ] H) (hJ : Function.Injective J) (x w : E) :
    inner ℝ (massEquiv J hJ x) w = inner ℝ (J x) (J w) := by
  exact J.adjoint_inner_left w (J x)

lemma inverse_mass_inner (J : E →L[ℝ] H) (hJ : Function.Injective J) (x w : E) :
    inner ℝ (J ((massEquiv J hJ).symm x)) (J w) = inner ℝ x w := by
  rw [← mass_inner J hJ, (massEquiv J hJ).apply_symm_apply]

lemma exists_mass_wave (T : ℝ) (hT : 0 ≤ T) (J : E →L[ℝ] H) (hJ : Function.Injective J)
    (B : ℝ → E →L[ℝ] E) (hB : ContinuousOn B (Set.Icc 0 T))
    (f : ℝ → H) (hf : IntervalIntegrable f volume 0 T) (u₀ v₀ : E) :
    ∃ u v q : ℝ → E,
      Continuous u ∧ Continuous v ∧ u 0 = u₀ ∧ v 0 = v₀ ∧
      (∀ s ∈ Set.Icc 0 T, ∀ t ∈ Set.Icc 0 T, u t - u s = ∫ r in s..t, v r) ∧
      (∀ s ∈ Set.Icc 0 T, ∀ t ∈ Set.Icc 0 T, v t - v s = ∫ r in s..t, q r) ∧
      (∀ t, ∀ w : E, inner ℝ (J (q t)) (J w) + inner ℝ (B t (u t)) w =
        inner ℝ (f t) (J w)) := by
  let N : E →L[ℝ] E := (massEquiv J hJ).symm.toContinuousLinearMap
  let F : H →L[ℝ] E := N.comp J.adjoint
  have hA : ContinuousOn (fun t => N.comp (B t)) (Set.Icc 0 T) := by fun_prop
  have hF : IntervalIntegrable (fun t => F (f t)) volume 0 T :=
    ⟨F.integrable_comp hf.1,F.integrable_comp hf.2⟩
  obtain ⟨u,v,huc,hvc,hu₀,hv₀,hu,hv⟩ :=
    Volterra.wave_exists_solution hT _ hA _ hF u₀ v₀
  let q : ℝ → E := fun t => -(N (B t (u t))) + F (f t)
  refine ⟨u,v,q,huc,hvc,hu₀,hv₀,hu,hv,?_⟩
  intro t w
  change inner ℝ (J (-(N (B t (u t))) + N (J.adjoint (f t)))) (J w) +
      inner ℝ (B t (u t)) w = _
  rw [← map_neg, ← map_add]
  change inner ℝ (J ((massEquiv J hJ).symm (-(B t (u t)) + J.adjoint (f t)))) (J w) + _ = _
  rw [inverse_mass_inner J hJ,inner_add_left,inner_neg_left,J.adjoint_inner_left]
  ring

lemma continuousOn_memLp_Ioo {T : ℝ} {p : ENNReal} {z : ℝ → E}
    (hz : ContinuousOn z (Set.Icc 0 T)) : MemLp z p (volume.restrict (Set.Ioo 0 T)) := by
  obtain ⟨R,hR⟩ := isCompact_Icc.exists_bound_of_continuousOn hz
  apply MemLp.of_bound ((hz.mono Set.Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo) R
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact hR t (Set.Ioo_subset_Icc_self ht)

lemma exists_mass_wave_L2 (T : ℝ) (hT : 0 ≤ T) (J : E →L[ℝ] H) (hJ : Function.Injective J)
    (B : ℝ → E →L[ℝ] E) (hB : ContinuousOn B (Set.Icc 0 T))
    (f : ℝ → H) (hf : MemLp f 2 (volume.restrict (Set.Ioo 0 T))) (u₀ v₀ : E) :
    ∃ u v q : ℝ → E,
      Continuous u ∧ Continuous v ∧ u 0 = u₀ ∧ v 0 = v₀ ∧
      MemLp q 2 (volume.restrict (Set.Ioo 0 T)) ∧
      (∀ s ∈ Set.Icc 0 T, ∀ t ∈ Set.Icc 0 T, u t - u s = ∫ r in s..t, v r) ∧
      (∀ s ∈ Set.Icc 0 T, ∀ t ∈ Set.Icc 0 T, v t - v s = ∫ r in s..t, q r) ∧
      (∀ t, ∀ w : E, inner ℝ (J (q t)) (J w) + inner ℝ (B t (u t)) w =
        inner ℝ (f t) (J w)) := by
  have hfi : IntervalIntegrable f volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hT).mpr (hf.integrable (by norm_num))
  obtain ⟨u,v,q,huc,hvc,hu₀,hv₀,hu,hv,hq⟩ := exists_mass_wave T hT J hJ B hB f hfi u₀ v₀
  have heq : ∀ t, q t = (massEquiv J hJ).symm (J.adjoint (f t) - B t (u t)) := by
    intro t
    apply (massEquiv J hJ).injective
    rw [(massEquiv J hJ).apply_symm_apply]
    apply ext_inner_right ℝ
    intro w
    rw [mass_inner,inner_sub_left,J.adjoint_inner_left]
    linarith [hq t w]
  have hBm : MemLp (fun t => B t (u t)) 2 (volume.restrict (Set.Ioo 0 T)) :=
    continuousOn_memLp_Ioo (hB.clm_apply huc.continuousOn)
  have hqm : MemLp q 2 (volume.restrict (Set.Ioo 0 T)) := by
    have hm : MemLp (fun t => (massEquiv J hJ).symm (J.adjoint (f t) - B t (u t)))
        2 (volume.restrict (Set.Ioo 0 T)) :=
      (massEquiv J hJ).symm.toContinuousLinearMap.comp_memLp'
      ((J.adjoint.comp_memLp' hf).sub hBm)
    rw [show q = (fun t => (massEquiv J hJ).symm (J.adjoint (f t) - B t (u t))) from funext heq]
    exact hm
  exact ⟨u,v,q,huc,hvc,hu₀,hv₀,hqm,hu,hv,hq⟩

end MassWave

namespace Galerkin
variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

lemma exists_subspace_mass_wave (T : ℝ) (hT : 0 ≤ T)
    (J : V →L[ℝ] H) (hJ : Function.Injective J) (E : Submodule ℝ V)
    [FiniteDimensional ℝ E] (B : ℝ → V →L[ℝ] V) (hB : ContinuousOn B (Set.Icc 0 T))
    (f : ℝ → H) (hf : IntervalIntegrable f volume 0 T) (u₀ v₀ : E) :
    ∃ u v q : ℝ → E,
      Continuous u ∧ Continuous v ∧ u 0 = u₀ ∧ v 0 = v₀ ∧
      (∀ s ∈ Set.Icc 0 T, ∀ t ∈ Set.Icc 0 T, u t - u s = ∫ r in s..t, v r) ∧
      (∀ s ∈ Set.Icc 0 T, ∀ t ∈ Set.Icc 0 T, v t - v s = ∫ r in s..t, q r) ∧
      (∀ t, ∀ w : E, inner ℝ (J (q t)) (J w) + inner ℝ (B t (u t)) (w : V) =
        inner ℝ (f t) (J w)) := by
  let JE : E →L[ℝ] H := J.comp E.subtypeL
  have hJE : Function.Injective JE := hJ.comp Subtype.coe_injective
  let BE : ℝ → E →L[ℝ] E := fun t => E.orthogonalProjectionOnto.comp ((B t).comp E.subtypeL)
  have hBE : ContinuousOn BE (Set.Icc 0 T) := by dsimp [BE]; fun_prop
  obtain ⟨u,v,q,huc,hvc,hu₀,hv₀,hu,hv,hq⟩ :=
    MassWave.exists_mass_wave T hT JE hJE BE hBE f hf u₀ v₀
  refine ⟨u,v,q,huc,hvc,hu₀,hv₀,hu,hv,?_⟩
  intro t w
  simpa [JE,BE] using hq t w

lemma exists_subspace_mass_wave_L2 (T : ℝ) (hT : 0 ≤ T)
    (J : V →L[ℝ] H) (hJ : Function.Injective J) (E : Submodule ℝ V)
    [FiniteDimensional ℝ E] (B : ℝ → V →L[ℝ] V) (hB : ContinuousOn B (Set.Icc 0 T))
    (f : ℝ → H) (hf : MemLp f 2 (volume.restrict (Set.Ioo 0 T))) (u₀ v₀ : E) :
    ∃ u v q : ℝ → E,
      Continuous u ∧ Continuous v ∧ u 0 = u₀ ∧ v 0 = v₀ ∧
      MemLp q 2 (volume.restrict (Set.Ioo 0 T)) ∧
      (∀ s ∈ Set.Icc 0 T, ∀ t ∈ Set.Icc 0 T, u t - u s = ∫ r in s..t, v r) ∧
      (∀ s ∈ Set.Icc 0 T, ∀ t ∈ Set.Icc 0 T, v t - v s = ∫ r in s..t, q r) ∧
      (∀ t, ∀ w : E, inner ℝ (J (q t)) (J w) + inner ℝ (B t (u t)) (w : V) =
        inner ℝ (f t) (J w)) := by
  let JE : E →L[ℝ] H := J.comp E.subtypeL
  have hJE : Function.Injective JE := hJ.comp Subtype.coe_injective
  let BE : ℝ → E →L[ℝ] E := fun t => E.orthogonalProjectionOnto.comp ((B t).comp E.subtypeL)
  have hBE : ContinuousOn BE (Set.Icc 0 T) := by dsimp [BE]; fun_prop
  obtain ⟨u,v,q,huc,hvc,hu₀,hv₀,hqm,hu,hv,hq⟩ :=
    MassWave.exists_mass_wave_L2 T hT JE hJE BE hBE f hf u₀ v₀
  refine ⟨u,v,q,huc,hvc,hu₀,hv₀,hqm,hu,hv,?_⟩
  intro t w
  simpa [JE,BE] using hq t w

end Galerkin

/-- Every finite trial space has a genuine mass-matrix solution for the
source's scalar-C¹ forms and Bochner L² forcing. The trial acceleration is
L², and both primitive identities retain all endpoints. -/
theorem finite_galerkin_solution (j : HilbertTriple V H) (T : ℝ) (hT : 0 ≤ T)
    (a : ℝ → Form V) (ha : ScalarC1 T a) (E : Submodule ℝ V)
    [FiniteDimensional ℝ E] (f : timeLpValue H 2 T) (u₀ v₀ : E) :
    ∃ u v q : ℝ → E,
      Continuous u ∧ Continuous v ∧ u 0 = u₀ ∧ v 0 = v₀ ∧
      MemLp q 2 (timeMeasureValue T) ∧
      (∀ s ∈ Set.Icc 0 T, ∀ t ∈ Set.Icc 0 T, u t - u s = ∫ r in s..t, v r) ∧
      (∀ s ∈ Set.Icc 0 T, ∀ t ∈ Set.Icc 0 T, v t - v s = ∫ r in s..t, q r) ∧
      (∀ t, ∀ w : E, inner ℝ (j.embedding (q t)) (j.embedding w) + a t (u t) w =
        inner ℝ (f t) (j.embedding w)) := by
  obtain ⟨M,hM,_,hLip⟩ := HyperbolicFormBoundsAndCarrier.uniform_bounds T a ha
  have hBc : ContinuousOn (fun t => representingOperator (a t)) (Set.Icc 0 T) := by
    have hlip : LipschitzOnWith ⟨M,hM⟩ (fun t => representingOperator (a t)) (Set.Icc 0 T) := by
      apply lipschitzOnWith_iff_norm_sub_le.mpr
      intro s hs t ht
      change ‖representingOperator (a s) - representingOperator (a t)‖ ≤ M * ‖s - t‖
      simpa [Real.norm_eq_abs] using hLip t ht s hs
    exact hlip.continuousOn
  obtain ⟨u,v,q,huc,hvc,hu₀,hv₀,hqm,hu,hv,hq⟩ :=
    Galerkin.exists_subspace_mass_wave_L2 T hT j.embedding j.injective E
      (fun t => representingOperator (a t)) hBc f (Lp.memLp f) u₀ v₀
  refine ⟨u,v,q,huc,hvc,hu₀,hv₀,hqm,hu,hv,?_⟩
  intro t w
  simpa only [HyperbolicFormBoundsAndCarrier.representingOperator_inner] using hq t w


end FiniteConstruction

/- Endpoint moments and a nonseparable directed Galerkin family. -/
section EndpointMoments
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem integral_eq_timeIntegral (T : ℝ) (hT : 0 ≤ T) (g : ℝ → E) :
    (∫ t in 0..T, g t) = ∫ t, g t ∂timeMeasureValue T := by
  rw [intervalIntegral.integral_of_le hT, ← integral_Icc_eq_integral_Ioc,
    ← restrict_Ioo_eq_restrict_Icc]
  rfl

theorem continuousOn_time_memLp {T : ℝ} {p : ENNReal} {z : ℝ → E}
    (hz : ContinuousOn z (Set.Icc 0 T)) : MemLp z p (timeMeasureValue T) := by
  obtain ⟨R,hR⟩ := isCompact_Icc.exists_bound_of_continuousOn hz
  apply MemLp.of_bound ((hz.mono Set.Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo) R
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact hR t (Set.Ioo_subset_Icc_self ht)

/-- Endpoint data are linear moments of a primitive and its density. -/
theorem primitive_endpoint_moment (T : ℝ) (hT : 0 ≤ T) (U g : ℝ → E)
    (hg : Integrable g (timeMeasureValue T))
    (hinc : ∀ s t : Set.Icc 0 T, U t - U s = ∫ r in s.val..t.val, g r) :
    (∫ t, U t ∂timeMeasureValue T) -
      (∫ t, (T-t) • g t ∂timeMeasureValue T) = T • U 0 := by
  let G := (Set.Ioo 0 T).indicator g
  have hG : Integrable G volume := (integrable_indicator_iff measurableSet_Ioo).mpr hg
  have hi (s t : ℝ) : IntervalIntegrable G volume s t := hG.intervalIntegrable
  let Q : ℝ → E := fun t => U 0 + ∫ r in 0..t, G r
  have hQ : Continuous Q := continuous_const.add (intervalIntegral.continuous_primitive hi 0)
  have hQac (s t : ℝ) : AbsolutelyContinuousOnInterval Q s t :=
    by
      have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => U 0) s t :=
        (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => U 0)).contDiffOn.absolutelyContinuousOnInterval
      convert! hc.add
        (Sobolev.OneDimensional.integral_primitive_absolutelyContinuous hi s t 0) using 1
  have hQd : ∀ᵐ t ∂volume, HasDerivAt Q (G t) t := by
    filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hG.locallyIntegrable] with t ht
    convert! (hasDerivAt_const t (U 0)).add (ht 0) using 1 <;> simp
  have hQU : ∀ t ∈ Set.Icc 0 T, Q t = U t := by
    intro t ht
    have he := hinc ⟨0, le_rfl, hT⟩ ⟨t, ht⟩
    change U t - U 0 = ∫ r in 0..t, g r at he
    have hc : (∫ r in 0..t, G r) = ∫ r in 0..t, g r :=
      time_integral_congr_ae T
        (by filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
            exact Set.indicator_of_mem hr g) ⟨0, le_rfl, hT⟩ ⟨t, ht⟩
    dsimp [Q]
    rw [hc, ← he]
    exact add_sub_cancel _ _
  have hwac : AbsolutelyContinuousOnInterval (fun t : ℝ => T-t) 0 T :=
    (contDiff_const.sub contDiff_id : ContDiff ℝ 1 (fun t : ℝ => T-t)).contDiffOn.absolutelyContinuousOnInterval
  have hprod : AbsolutelyContinuousOnInterval (fun t => (T-t) • Q t) 0 T := hwac.smul (hQac 0 T)
  have hdensity : LocallyIntegrable (fun t => -Q t + (T-t) • G t) volume :=
    hQ.neg.locallyIntegrable.add <|
      hG.locallyIntegrable.continuous_smul (continuous_const.sub continuous_id)
  have hd : ∀ᵐ t ∂volume, t ∈ Set.uIcc 0 T →
      HasDerivAt (fun t => (T-t) • Q t) (-Q t + (T-t) • G t) t := by
    filter_upwards [hQd] with t ht _
    convert! ((hasDerivAt_const t T).sub (hasDerivAt_id t)).smul ht using 1 <;> simp [add_comm]
  have hFTC := Sobolev.OneDimensional.integral_eq_sub_of_absolutelyContinuous_of_ae_hasDerivAt
    hprod hdensity hd
  have hQi : IntervalIntegrable Q volume 0 T := hQ.intervalIntegrable 0 T
  have hwGi : IntervalIntegrable (fun t => (T-t) • G t) volume 0 T :=
    (hG.locallyIntegrable.continuous_smul (continuous_const.sub continuous_id)).integrableOn_isCompact
      isCompact_uIcc |>.intervalIntegrable
  rw [intervalIntegral.integral_add (f := fun t => -Q t) hQi.neg hwGi,
    intervalIntegral.integral_neg] at hFTC
  have hQ0 : Q 0 = U 0 := by simp [Q]
  simp only [sub_self, zero_smul, hQ0, sub_zero, zero_sub] at hFTC
  have hQUae : Q =ᵐ[timeMeasureValue T] U := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact hQU t (Set.Ioo_subset_Icc_self ht)
  have hGUae : (fun t => (T-t) • G t) =ᵐ[timeMeasureValue T] fun t => (T-t) • g t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    simp only [G, Set.indicator_of_mem ht]
  rw [integral_eq_timeIntegral T hT, integral_eq_timeIntegral T hT,
    integral_congr_ae hQUae, integral_congr_ae hGUae] at hFTC
  apply neg_inj.mp
  simpa [sub_eq_add_neg, add_comm] using hFTC

/-- The mean of the zero-based primitive is a bounded weighted moment of its density. -/
theorem mean_primitive_eq_weighted (T : ℝ) (hT : 0 ≤ T) (g : ℝ → E)
    (hg : Integrable g (timeMeasureValue T)) :
    (∫ t, (∫ r in 0..t, g r) ∂timeMeasureValue T) =
      ∫ t, (T-t) • g t ∂timeMeasureValue T := by
  have hi : IntervalIntegrable g volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hT).mpr hg
  have hinc : ∀ s t : Set.Icc 0 T,
      (∫ r in 0..t.val, g r) - (∫ r in 0..s.val, g r) =
        ∫ r in s.val..t.val, g r := by
    intro s t
    apply intervalIntegral.integral_interval_sub_left
    · exact hi.mono_set (by simpa only [Set.uIcc_of_le hT, Set.uIcc_of_le t.property.1] using
        (Set.Icc_subset_Icc_right t.property.2 : Set.Icc (0:ℝ) t.val ⊆ Set.Icc 0 T))
    · exact hi.mono_set (by simpa only [Set.uIcc_of_le hT, Set.uIcc_of_le s.property.1] using
        (Set.Icc_subset_Icc_right s.property.2 : Set.Icc (0:ℝ) s.val ⊆ Set.Icc 0 T))
  have hm := primitive_endpoint_moment T hT (fun t => ∫ r in 0..t, g r) g hg hinc
  simpa only [intervalIntegral.integral_same, smul_zero, sub_eq_zero] using hm

theorem integral_anchor_of_moment (T : ℝ) (hT : 0 ≤ T) (U g : ℝ → E) (e₀ : E)
    (hU : Integrable U (timeMeasureValue T)) (hg : Integrable g (timeMeasureValue T))
    (hm : (∫ t, U t ∂timeMeasureValue T) -
      (∫ t, (T-t) • g t ∂timeMeasureValue T) = T • e₀) :
    (∫ t, (U t - ∫ r in 0..t, g r) ∂timeMeasureValue T) = T • e₀ := by
  let G := (Set.Ioo 0 T).indicator g
  have hG : Integrable G volume := (integrable_indicator_iff measurableSet_Ioo).mpr hg
  have hi (s t : ℝ) : IntervalIntegrable G volume s t := hG.intervalIntegrable
  have hPmem : MemLp (fun t => ∫ r in 0..t, G r) 2 (timeMeasureValue T) :=
    continuousOn_time_memLp (intervalIntegral.continuous_primitive hi 0).continuousOn
  have hPae : (fun t => ∫ r in 0..t, G r) =ᵐ[timeMeasureValue T]
      fun t => ∫ r in 0..t, g r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact time_integral_congr_ae T
      (by filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
          exact Set.indicator_of_mem hr g) ⟨0, le_rfl, hT⟩ ⟨t, Set.Ioo_subset_Icc_self ht⟩
  letI : IsFiniteMeasure (timeMeasureValue T) :=
    inferInstanceAs (IsFiniteMeasure (volume.restrict (Set.Ioo 0 T)))
  have hP : Integrable (fun t => ∫ r in 0..t, g r) (timeMeasureValue T) :=
    (hPmem.integrable (by norm_num)).congr hPae
  rw [integral_sub hU hP, mean_primitive_eq_weighted T hT g hg]
  exact hm

/-- Endpoint moments are continuous linear maps on the two L² graph components. -/
def endpointMomentCLM (T : ℝ) :
    (Lp E 2 (timeMeasureValue T) × Lp E 2 (timeMeasureValue T)) →L[ℝ] E :=
  let h₁ : MemLp (fun _ : ℝ => (1 : ℝ)) 2 (timeMeasureValue T) :=
    continuousOn_time_memLp continuousOn_const
  let hw : MemLp (fun t : ℝ => T-t) 2 (timeMeasureValue T) :=
    continuousOn_time_memLp (continuous_const.sub continuous_id).continuousOn
  (testIntegralCLM T _ h₁).comp (ContinuousLinearMap.fst ℝ _ _) -
    (testIntegralCLM T _ hw).comp (ContinuousLinearMap.snd ℝ _ _)

theorem endpointMomentCLM_eq (T : ℝ)
    (U g : Lp E 2 (timeMeasureValue T)) :
    endpointMomentCLM T (U,g) = (∫ t, U t ∂timeMeasureValue T) -
      (∫ t, (T-t) • g t ∂timeMeasureValue T) := by
  change testIntegralCLM T _ _ U - testIntegralCLM T _ _ g = _
  rw [testIntegralCLM_eq, testIntegralCLM_eq]
  simp only [one_smul]


/-- Weak L² convergence preserves the initial moment as initial data converge strongly. -/
theorem endpoint_moment_of_weak_L2_limits {ι : Type*} (F : Filter ι) [NeBot F]
    (T : ℝ) (U g : ι → Lp E 2 (timeMeasureValue T))
    (x y : Lp E 2 (timeMeasureValue T))
    (hU : ∀ L : StrongDual ℝ (Lp E 2 (timeMeasureValue T)),
      Tendsto (fun i => L (U i)) F (𝓝 (L x)))
    (hg : ∀ L : StrongDual ℝ (Lp E 2 (timeMeasureValue T)),
      Tendsto (fun i => L (g i)) F (𝓝 (L y)))
    (e : ι → E) (e₀ : E) (he : Tendsto e F (𝓝 e₀))
    (hm : ∀ᶠ i in F, (∫ t, U i t ∂timeMeasureValue T) -
      (∫ t, (T-t) • g i t ∂timeMeasureValue T) = T • e i) :
    (∫ t, x t ∂timeMeasureValue T) -
      (∫ t, (T-t) • y t ∂timeMeasureValue T) = T • e₀ := by
  let A : Lp E 2 (timeMeasureValue T) →L[ℝ] E :=
    testIntegralCLM T (fun _ : ℝ => (1 : ℝ))
      (continuousOn_time_memLp continuousOn_const)
  let B : Lp E 2 (timeMeasureValue T) →L[ℝ] E :=
    testIntegralCLM T (fun t : ℝ => T-t)
      (continuousOn_time_memLp (continuous_const.sub continuous_id).continuousOn)
  have hA (z : Lp E 2 (timeMeasureValue T)) :
      A z = ∫ t, z t ∂timeMeasureValue T := by
    change testIntegralCLM T _ _ z = _
    rw [testIntegralCLM_eq]
    simp only [one_smul]
  have hB (z : Lp E 2 (timeMeasureValue T)) :
      B z = ∫ t, (T-t) • z t ∂timeMeasureValue T := testIntegralCLM_eq _ _ _ _
  rw [← hA, ← hB]
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
  intro L
  rw [map_sub]
  have hm' : ∀ᶠ i in F,
      (L.comp A) (U i) - (L.comp B) (g i) = L (T • e i) := by
    filter_upwards [hm] with i hi
    change L (A (U i)) - L (B (g i)) = _
    rw [← map_sub, hA, hB, hi]
  exact tendsto_nhds_unique (((hU (L.comp A)).sub (hg (L.comp B))).congr' hm')
    (L.continuous.tendsto _ |>.comp (he.const_smul T))

end EndpointMoments
namespace GalerkinNet
variable {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The directed family contains the prescribed displacement exactly. -/
def trialSpace (u₀ : V) (s : Finset V) : Submodule ℝ V := by
  classical
  exact Submodule.span ℝ (↑(insert u₀ s) : Set V)

instance finiteDimensional_trialSpace (u₀ : V) (s : Finset V) :
    FiniteDimensional ℝ (trialSpace u₀ s) := by
  classical
  exact FiniteDimensional.span_of_finite ℝ (Finset.finite_toSet (insert u₀ s))

theorem initial_mem_trialSpace (u₀ : V) (s : Finset V) : u₀ ∈ trialSpace u₀ s := by
  classical
  exact Submodule.subset_span (Finset.mem_insert_self _ _)

theorem trialSpace_mono (u₀ : V) : Monotone (trialSpace u₀) := by
  classical
  intro s t hst
  apply Submodule.span_mono
  intro w hw
  simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hw ⊢
  exact hw.imp_right (fun h => hst h)

theorem eventually_mem_trialSpace (u₀ w : V) :
    ∀ᶠ s : Finset V in atTop, w ∈ trialSpace u₀ s := by
  classical
  filter_upwards [eventually_ge_atTop ({w} : Finset V)] with s hs
  apply Submodule.subset_span
  exact Finset.mem_insert_of_mem (hs (Finset.mem_singleton_self _))

/-- Its image has the H inner product and admits a genuine H projection. -/
def pivotTrialSpace (j : HilbertTriple V H) (u₀ : V) (s : Finset V) : Submodule ℝ H :=
  (trialSpace u₀ s).map j.embedding.toLinearMap

instance finiteDimensional_pivotTrialSpace (j : HilbertTriple V H) (u₀ : V) (s : Finset V) :
    FiniteDimensional ℝ (pivotTrialSpace j u₀ s) := by
  exact Module.Finite.map (trialSpace u₀ s) j.embedding.toLinearMap

theorem pivotTrialSpace_mono (j : HilbertTriple V H) (u₀ : V) :
    Monotone (pivotTrialSpace j u₀) :=
  fun _ _ h => Submodule.map_mono (trialSpace_mono u₀ h)

theorem range_subset_iSup_pivotTrialSpace (j : HilbertTriple V H) (u₀ : V) :
    Set.range j.embedding ⊆ (⨆ s, pivotTrialSpace j u₀ s : Submodule ℝ H) := by
  rintro _ ⟨w, rfl⟩
  have hw : w ∈ trialSpace u₀ {w} := by
    classical
    exact Submodule.subset_span (by simp)
  exact (le_iSup (pivotTrialSpace j u₀) {w}) (Submodule.mem_map.mpr ⟨w, hw, rfl⟩)

theorem dense_iSup_pivotTrialSpace (j : HilbertTriple V H) (u₀ : V) :
    ⊤ ≤ (⨆ s, pivotTrialSpace j u₀ s).topologicalClosure := by
  intro h _
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
  have hcl := closure_mono (range_subset_iSup_pivotTrialSpace j u₀)
  rw [j.denseRange.closure_range] at hcl
  exact hcl (Set.mem_univ h)

/-- Orthogonal projected initial velocities converge in the original H norm. -/
theorem projected_velocity_tendsto (j : HilbertTriple V H) (u₀ : V) (v₀ : H) :
    Tendsto (fun s : Finset V => (pivotTrialSpace j u₀ s).starProjection v₀)
      atTop (𝓝 v₀) :=
  Submodule.starProjection_tendsto_self (pivotTrialSpace j u₀)
    (pivotTrialSpace_mono j u₀) v₀ (dense_iSup_pivotTrialSpace j u₀)

def initialDisplacement (u₀ : V) (s : Finset V) : trialSpace u₀ s :=
  ⟨u₀, initial_mem_trialSpace u₀ s⟩

theorem exists_initialVelocity (j : HilbertTriple V H) (u₀ : V) (v₀ : H) (s : Finset V) :
    ∃ v : trialSpace u₀ s, j.embedding v = (pivotTrialSpace j u₀ s).starProjection v₀ := by
  have hp := ((pivotTrialSpace j u₀ s).orthogonalProjectionOnto v₀).property
  obtain ⟨v, hv, he⟩ := Submodule.mem_map.mp hp
  exact ⟨⟨v,hv⟩, he⟩

def initialVelocity (j : HilbertTriple V H) (u₀ : V) (v₀ : H) (s : Finset V) :
    trialSpace u₀ s := (exists_initialVelocity j u₀ v₀ s).choose

@[simp] theorem embedding_initialVelocity (j : HilbertTriple V H)
    (u₀ : V) (v₀ : H) (s : Finset V) :
    j.embedding (initialVelocity j u₀ v₀ s) = (pivotTrialSpace j u₀ s).starProjection v₀ :=
  (exists_initialVelocity j u₀ v₀ s).choose_spec

theorem embedding_initialVelocity_norm_le (j : HilbertTriple V H)
    (u₀ : V) (v₀ : H) (s : Finset V) :
    ‖j.embedding (initialVelocity j u₀ v₀ s)‖ ≤ ‖v₀‖ := by
  rw [embedding_initialVelocity]
  exact (pivotTrialSpace j u₀ s).norm_starProjection_apply_le v₀

theorem embedding_initialVelocity_tendsto (j : HilbertTriple V H) (u₀ : V) (v₀ : H) :
    Tendsto (fun s : Finset V => j.embedding (initialVelocity j u₀ v₀ s))
      atTop (𝓝 v₀) := by
  simpa only [embedding_initialVelocity] using projected_velocity_tendsto j u₀ v₀

@[simp] theorem coe_initialDisplacement (u₀ : V) (s : Finset V) :
    (initialDisplacement u₀ s : V) = u₀ := rfl

/-- Projection is contractive only in H; this is the estimate needed by energy. -/
theorem initial_energy_le (j : HilbertTriple V H) (u₀ : V) (v₀ : H)
    (b : V → V → ℝ) (s : Finset V) :
    ‖j.embedding (initialVelocity j u₀ v₀ s)‖ ^ 2 +
        b (initialDisplacement u₀ s) (initialDisplacement u₀ s) ≤
      ‖v₀‖ ^ 2 + b u₀ u₀ := by
  exact add_le_add
    (pow_le_pow_left₀ (norm_nonneg _) (embedding_initialVelocity_norm_le j u₀ v₀ s) 2) le_rfl

/-- Every test already in the trial space sees exactly the prescribed initial velocity. -/
theorem initialVelocity_pairing (j : HilbertTriple V H)
    (u₀ : V) (v₀ : H) (s : Finset V) (w : trialSpace u₀ s) :
    inner ℝ (j.embedding (initialVelocity j u₀ v₀ s)) (j.embedding w) =
      inner ℝ v₀ (j.embedding w) := by
  rw [embedding_initialVelocity]
  have hw : j.embedding w ∈ pivotTrialSpace j u₀ s :=
    Submodule.mem_map.mpr ⟨w, w.property, rfl⟩
  have he := (pivotTrialSpace j u₀ s).starProjection_inner_eq_zero v₀ (j.embedding w) hw
  rw [inner_sub_left, sub_eq_zero] at he
  exact he.symm

end GalerkinNet

/- Physical product energy and compactness of uniformly bounded states. -/
/-- Pull a continuous bilinear form back to the first component of the state. -/
def firstStateFormL : Form V →L[ℝ] Form (V × H) :=
  let p := ContinuousLinearMap.fst ℝ V H
  let q : (V →L[ℝ] ℝ) →L[ℝ] (V × H →L[ℝ] ℝ) := p.precomp ℝ
  let r : Form V →L[ℝ] (V × H →L[ℝ] V →L[ℝ] ℝ) := p.precomp (V →L[ℝ] ℝ)
  (q.postcomp (V × H)).comp r

@[simp] theorem firstStateFormL_apply (b : Form V) (z w : V × H) :
    firstStateFormL (H := H) b z w = b z.1 w.1 := rfl

/-- The original shifted energy as a bilinear form on the original product norm. -/
def stateEnergyForm (j : HilbertTriple V H) (a : ℝ → Form V) (κ t : ℝ) :
    Form (V × H) :=
  let h : Form (V × H) :=
    (InnerProductSpace.toDual ℝ H).toContinuousLinearEquiv.toContinuousLinearMap.bilinearComp
      (ContinuousLinearMap.snd ℝ V H) (ContinuousLinearMap.snd ℝ V H)
  firstStateFormL (H := H) (shiftedForm j a κ t) + h

@[simp] theorem stateEnergyForm_apply (j : HilbertTriple V H) (a : ℝ → Form V)
    (κ t : ℝ) (z w : V × H) :
    stateEnergyForm j a κ t z w = shiftedForm j a κ t z.1 w.1 + inner ℝ z.2 w.2 := rfl

@[simp] theorem stateEnergyForm_self (j : HilbertTriple V H) (a : ℝ → Form V)
    (κ t : ℝ) (z : V × H) :
    stateEnergyForm j a κ t z z = shiftedEnergy j a κ t z.1 z.2 := by
  rw [stateEnergyForm_apply, real_inner_self_eq_norm_sq, shiftedEnergy]
  exact add_comm _ _

 theorem form_continuousOn_of_scalarC1 (T : ℝ) (a : ℝ → Form V) (ha : ScalarC1 T a) :
    ContinuousOn a (Set.Icc 0 T) := by
  obtain ⟨M, hM, hbound⟩ := HyperbolicFormBoundsAndCarrier.form_secants_bounded T a ha
  have hl : LipschitzOnWith ⟨M, hM⟩ a (Set.Icc 0 T) := by
    apply lipschitzOnWith_iff_norm_sub_le.mpr
    intro t ht s hs
    exact hbound s hs t ht
  exact hl.continuousOn

 theorem stateEnergyForm_continuousOn (j : HilbertTriple V H) (T : ℝ)
    (a : ℝ → Form V) (ha : ScalarC1 T a) (κ : ℝ) :
    ContinuousOn (stateEnergyForm j a κ) (Set.Icc 0 T) := by
  letI : ContinuousAdd (Form V) :=
    (inferInstance : IsTopologicalAddGroup (Form V)).toContinuousAdd
  letI : ContinuousAdd (Form (V × H)) :=
    (inferInstance : IsTopologicalAddGroup (Form (V × H))).toContinuousAdd
  have hshift : ContinuousOn (shiftedForm j a κ) (Set.Icc 0 T) :=
    (form_continuousOn_of_scalarC1 T a ha).add continuousOn_const
  exact ((firstStateFormL (V := V) (H := H)).continuous.comp_continuousOn hshift).add
    continuousOn_const

 theorem stateEnergyForm_memLp_top (j : HilbertTriple V H) (T : ℝ)
    (a : ℝ → Form V) (ha : ScalarC1 T a) (κ : ℝ) :
    MemLp (stateEnergyForm j a κ) ∞ (timeMeasureValue T) := by
  letI : NormedAddCommGroup (Form (V × H)) := inferInstance
  have hc := stateEnergyForm_continuousOn j T a ha κ
  have hm : AEStronglyMeasurable (stateEnergyForm j a κ) (timeMeasureValue T) :=
    (hc.mono Set.Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  apply memLp_top_of_bound hm B
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact hB t (Set.Ioo_subset_Icc_self ht)

/-- The coefficient is an actual strongly measurable, bounded Bochner form. -/
def stateEnergyCoefficient (j : HilbertTriple V H) (T : ℝ)
    (a : ℝ → Form V) (ha : ScalarC1 T a) (κ : ℝ) :
    Lp (Form (V × H)) ∞ (timeMeasureValue T) :=
  (stateEnergyForm_memLp_top j T a ha κ).toLp (stateEnergyForm j a κ)

 theorem coeFn_stateEnergyCoefficient (j : HilbertTriple V H) (T : ℝ)
    (a : ℝ → Form V) (ha : ScalarC1 T a) (κ : ℝ) :
    stateEnergyCoefficient j T a ha κ =ᵐ[timeMeasureValue T] stateEnergyForm j a κ :=
  MemLp.coeFn_toLp _


/-- Scalar C¹ coefficients belong to genuine Bochner L∞ in operator norm. -/
theorem form_memLp_top (T : ℝ) (a : ℝ → Form V) (ha : ScalarC1 T a) :
    MemLp a ∞ (timeMeasureValue T) := by
  letI : NormedAddCommGroup (Form V) := inferInstance
  have hc := form_continuousOn_of_scalarC1 T a ha
  have hm : AEStronglyMeasurable a (timeMeasureValue T) :=
    (hc.mono Set.Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  apply memLp_top_of_bound hm B
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact hB t (Set.Ioo_subset_Icc_self ht)

def formCoefficient (T : ℝ) (a : ℝ → Form V) (ha : ScalarC1 T a) :
    Lp (Form V) ∞ (timeMeasureValue T) :=
  (form_memLp_top T a ha).toLp a

theorem coeFn_formCoefficient (T : ℝ) (a : ℝ → Form V) (ha : ScalarC1 T a) :
    formCoefficient T a ha =ᵐ[timeMeasureValue T] a := MemLp.coeFn_toLp _

/-- Time-dependent multiplication is continuous linear on L². -/
def formMultiplier (T : ℝ) (a : ℝ → Form V) (ha : ScalarC1 T a) :
    Lp V 2 (timeMeasureValue T) →L[ℝ] Lp (StrongDual ℝ V) 2 (timeMeasureValue T) :=
  (ContinuousLinearMap.id ℝ (Form V)).holderL (timeMeasureValue T) ∞ 2 2
    (formCoefficient T a ha)

theorem coeFn_formMultiplier (T : ℝ) (a : ℝ → Form V) (ha : ScalarC1 T a)
    (u : Lp V 2 (timeMeasureValue T)) :
    formMultiplier T a ha u =ᵐ[timeMeasureValue T] fun t => a t (u t) := by
  have hmul := ContinuousLinearMap.coeFn_holder (𝕜 := ℝ)
    (E := Form V) (F := V) (G := StrongDual ℝ V) (p := ∞) (q := 2) (r := 2)
    (ContinuousLinearMap.id ℝ (Form V)) (formCoefficient T a ha) u
  filter_upwards [hmul, coeFn_formCoefficient T a ha] with t ht hcoef
  simpa only [formMultiplier, ContinuousLinearMap.holderL_apply_apply,
    ContinuousLinearMap.id_apply, hcoef] using ht

/-- Package the two Bochner states without changing either original norm. -/
def stateLp (T : ℝ) (u : Lp V 2 (timeMeasureValue T))
    (v : Lp H 2 (timeMeasureValue T)) : Lp (V × H) 2 (timeMeasureValue T) :=
  (ContinuousLinearMap.inl ℝ V H).compLpL 2 (timeMeasureValue T) u +
    (ContinuousLinearMap.inr ℝ V H).compLpL 2 (timeMeasureValue T) v

 theorem coeFn_stateLp (T : ℝ) (u : Lp V 2 (timeMeasureValue T))
    (v : Lp H 2 (timeMeasureValue T)) :
    stateLp T u v =ᵐ[timeMeasureValue T] fun t => (u t, v t) := by
  filter_upwards [Lp.coeFn_add
    ((ContinuousLinearMap.inl ℝ V H).compLpL 2 (timeMeasureValue T) u)
    ((ContinuousLinearMap.inr ℝ V H).compLpL 2 (timeMeasureValue T) v),
    ContinuousLinearMap.coeFn_compLpL (ContinuousLinearMap.inl ℝ V H) u,
    ContinuousLinearMap.coeFn_compLpL (ContinuousLinearMap.inr ℝ V H) v] with t ha hb hc
  change _ = _ at ha
  change (stateLp T u v) t = _
  unfold stateLp
  rw [ha, Pi.add_apply, hb, hc]
  simp

 theorem stateLp_weak_limit {ι : Type*} (F : Filter ι) (T : ℝ)
    (u : ι → Lp V 2 (timeMeasureValue T)) (v : ι → Lp H 2 (timeMeasureValue T))
    (x : Lp V 2 (timeMeasureValue T)) (y : Lp H 2 (timeMeasureValue T))
    (hu : ∀ L : StrongDual ℝ (Lp V 2 (timeMeasureValue T)),
      Tendsto (fun i => L (u i)) F (𝓝 (L x)))
    (hv : ∀ L : StrongDual ℝ (Lp H 2 (timeMeasureValue T)),
      Tendsto (fun i => L (v i)) F (𝓝 (L y))) :
    ∀ L : StrongDual ℝ (Lp (V × H) 2 (timeMeasureValue T)),
      Tendsto (fun i => L (stateLp T (u i) (v i))) F (𝓝 (L (stateLp T x y))) := by
  intro L
  have h₁ := hu (L.comp ((ContinuousLinearMap.inl ℝ V H).compLpL 2 (timeMeasureValue T)))
  have h₂ := hv (L.comp ((ContinuousLinearMap.inr ℝ V H).compLpL 2 (timeMeasureValue T)))
  simpa only [stateLp, map_add, ContinuousLinearMap.comp_apply] using h₁.add h₂

/-- The exact physical shifted-energy inequality survives a weak L² pair limit. -/
 theorem ae_shiftedEnergy_bound_of_weak_pair_limit {ι : Type*} (F : Filter ι) [NeBot F]
    (j : HilbertTriple V H) (T : ℝ) (a : ℝ → Form V) (α C : ℝ)
    (ha : FormHypotheses j T a α C)
    (u : ι → Lp V 2 (timeMeasureValue T)) (v : ι → Lp H 2 (timeMeasureValue T))
    (x : Lp V 2 (timeMeasureValue T)) (y : Lp H 2 (timeMeasureValue T))
    (hu : ∀ L : StrongDual ℝ (Lp V 2 (timeMeasureValue T)),
      Tendsto (fun i => L (u i)) F (𝓝 (L x)))
    (hv : ∀ L : StrongDual ℝ (Lp H 2 (timeMeasureValue T)),
      Tendsto (fun i => L (v i)) F (𝓝 (L y)))
    (G : ℝ → ℝ) (hG : Integrable G (timeMeasureValue T))
    (hbound : ∀ᶠ i in F, ∀ᵐ t ∂timeMeasureValue T,
      shiftedEnergy j a C t (u i t) (v i t) ≤ G t) :
    ∀ᵐ t ∂timeMeasureValue T, shiftedEnergy j a C t (x t) (y t) ≤ G t := by
  let b := stateEnergyCoefficient j T a ha.scalarC1 C
  have hb : b =ᵐ[timeMeasureValue T] stateEnergyForm j a C :=
    coeFn_stateEnergyCoefficient j T a ha.scalarC1 C
  have hsymm : ∀ᵐ t ∂timeMeasureValue T, ∀ z w, b t z w = b t w z := by
    filter_upwards [hb, ae_restrict_mem measurableSet_Ioo] with t hbt ht
    intro z w
    rw [hbt, stateEnergyForm_apply, stateEnergyForm_apply,
      shiftedForm_symmetric j T a α C ha (Set.Ioo_subset_Icc_self ht), real_inner_comm z.2 w.2]
  have hpos : ∀ᵐ t ∂timeMeasureValue T, ∀ z, 0 ≤ b t z z := by
    filter_upwards [hb, ae_restrict_mem measurableSet_Ioo] with t hbt ht
    intro z
    rw [hbt, stateEnergyForm_self]
    exact shiftedEnergy_nonneg j T a α C ha (Set.Ioo_subset_Icc_self ht) z.1 z.2
  have hbound' : ∀ᶠ i in F, ∀ᵐ t ∂timeMeasureValue T,
      b t (stateLp T (u i) (v i) t) (stateLp T (u i) (v i) t) ≤ G t := by
    filter_upwards [hbound] with i hi
    filter_upwards [hi, hb, coeFn_stateLp T (u i) (v i)] with t ht hbt hst
    simpa only [hbt, hst, stateEnergyForm_self] using ht
  have hlim := WeakCompactness.ae_quadratic_bound_of_weak_limit F b hsymm hpos
    (fun i => stateLp T (u i) (v i)) (stateLp T x y)
    (stateLp_weak_limit F T u v x y hu hv) G hG hbound'
  filter_upwards [hlim, hb, coeFn_stateLp T x y] with t ht hbt hst
  simpa only [hbt, hst, stateEnergyForm_self] using ht

namespace WeakCompactness
variable {E : Type u} {B : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [CompleteSpace B]

/-- Uniform target norm bounds give simultaneous Bochner L² weak limits
which retain the same L∞ bounds. No separability premise is needed. -/
theorem exists_weak_pair_limit_of_ae_bound {ι : Type*} (F : Filter ι) [NeBot F]
    (T : ℝ) (z : ι → Lp E 2 (timeMeasureValue T))
    (w : ι → Lp B 2 (timeMeasureValue T)) (R S : ℝ) (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hz : ∀ᶠ i in F, ∀ᵐ t ∂timeMeasureValue T, ‖z i t‖ ≤ R)
    (hw : ∀ᶠ i in F, ∀ᵐ t ∂timeMeasureValue T, ‖w i t‖ ≤ S) :
    ∃ (x : Lp E 2 (timeMeasureValue T)) (y : Lp B 2 (timeMeasureValue T))
      (U : Ultrafilter ι), U ≤ F ∧
      (∀ᵐ t ∂timeMeasureValue T, ‖x t‖ ≤ R) ∧
      (∀ᵐ t ∂timeMeasureValue T, ‖y t‖ ≤ S) ∧
      MemLp x ∞ (timeMeasureValue T) ∧ MemLp y ∞ (timeMeasureValue T) ∧
      (∀ L : StrongDual ℝ (Lp E 2 (timeMeasureValue T)),
        Tendsto (fun i => L (z i)) U (𝓝 (L x))) ∧
      (∀ L : StrongDual ℝ (Lp B 2 (timeMeasureValue T)),
        Tendsto (fun i => L (w i)) U (𝓝 (L y))) := by
  letI : IsFiniteMeasure (timeMeasureValue T) :=
    inferInstanceAs (IsFiniteMeasure (volume.restrict (Set.Ioo 0 T)))
  have hz' : ∀ᶠ i in F,
      ‖z i‖ ≤ (measureUnivNNReal (timeMeasureValue T) : ℝ) ^ (2:ℝ≥0∞).toReal⁻¹ * R :=
    hz.mono fun _ hi => Lp.norm_le_of_ae_bound hR hi
  have hw' : ∀ᶠ i in F,
      ‖w i‖ ≤ (measureUnivNNReal (timeMeasureValue T) : ℝ) ^ (2:ℝ≥0∞).toReal⁻¹ * S :=
    hw.mono fun _ hi => Lp.norm_le_of_ae_bound hS hi
  obtain ⟨x,y,U,hUF,_,_,hx,hy⟩ := exists_weak_pair_limit F z w _ _ hz' hw'
  have hxb := ae_norm_le_of_weak_limit (U : Filter ι) z x R hx (hz.filter_mono hUF)
  have hyb := ae_norm_le_of_weak_limit (U : Filter ι) w y S hy (hw.filter_mono hUF)
  exact ⟨x,y,U,hUF,hxb,hyb,memLp_top_of_bound (Lp.aestronglyMeasurable x) R hxb,
    memLp_top_of_bound (Lp.aestronglyMeasurable y) S hyb,hx,hy⟩
end WeakCompactness

end ExpandedFA.Evolution.HyperbolicWeakEnergyExistence

/- Finite shifted energy and the uniform source estimate. -/

noncomputable section
section FiniteEnergyContext
open MeasureTheory Set Filter intervalIntegral
open scoped Topology

namespace ExpandedFA.Evolution.HyperbolicWeakEnergyExistence.FiniteEnergy

/-- Gronwall with an L¹ error, valid for absolutely continuous energies. -/
theorem ac_gronwall {T c : ℝ} (hT : 0 ≤ T) (hc : 0 ≤ c)
    {E d g : ℝ → ℝ} (hE : AbsolutelyContinuousOnInterval E 0 T)
    (hg : IntervalIntegrable g volume 0 T)
    (hgn : ∀ᵐ t ∂volume, t ∈ Icc 0 T → 0 ≤ g t)
    (hd : ∀ᵐ t ∂volume, t ∈ Icc 0 T →
      HasDerivAt E (d t) t ∧ d t ≤ c * E t + g t) :
    ∀ t ∈ Icc 0 T, E t ≤ Real.exp (c * t) * (E 0 + ∫ r in 0..t, g r) := by
  intro t ht
  have hu : uIcc (0 : ℝ) t ⊆ uIcc (0 : ℝ) T := by
    simpa [uIcc_of_le hT, uIcc_of_le ht.1] using Icc_subset_Icc_right ht.2
  have hEt := hE.mono hu
  have hgc := hg.mono_set hu
  let q : ℝ → ℝ := fun r => Real.exp (-c * r) * E r
  have he : ContDiff ℝ 1 (fun r : ℝ => Real.exp (-c * r)) := by fun_prop
  have hq : AbsolutelyContinuousOnInterval q 0 t :=
    he.contDiffOn.absolutelyContinuousOnInterval.fun_mul hEt
  have hmul : IntervalIntegrable (fun r => Real.exp (-c * r) * g r) volume 0 t :=
    hgc.continuousOn_mul he.continuous.continuousOn
  have hder : ∀ᵐ r ∂volume, r ∈ uIcc (0 : ℝ) t →
      deriv q r ≤ Real.exp (-c * r) * g r := by
    filter_upwards [hd] with r hr hrt
    have hrT : r ∈ Icc 0 T := by simpa [uIcc_of_le hT] using hu hrt
    have hqe : HasDerivAt q
        (Real.exp (-c * r) * (-c) * E r + Real.exp (-c * r) * d r) r := by
      convert (((hasDerivAt_id r).const_mul (-c)).exp).mul (hr hrT).1 using 1 <;> try simp [q]
      ext r; rfl
    rw [hqe.deriv]
    nlinarith [mul_le_mul_of_nonneg_left (hr hrT).2 (Real.exp_pos (-c * r)).le]
  have hle : q t - q 0 ≤ ∫ r in 0..t, Real.exp (-c * r) * g r := by
    rw [← hq.integral_deriv_eq_sub]
    apply intervalIntegral.integral_mono_ae_restrict ht.1 hq.intervalIntegrable_deriv hmul
    filter_upwards [ae_restrict_of_ae hder, ae_restrict_mem measurableSet_Icc] with r hr hri
    exact hr (by simpa [uIcc_of_le ht.1] using hri)
  have hle' : (∫ r in 0..t, Real.exp (-c * r) * g r) ≤ ∫ r in 0..t, g r := by
    apply intervalIntegral.integral_mono_ae_restrict ht.1 hmul hgc
    filter_upwards [ae_restrict_of_ae hgn, ae_restrict_mem measurableSet_Icc] with r hr hrI
    have hrg : 0 ≤ g r := hr ⟨hrI.1,hrI.2.trans ht.2⟩
    exact mul_le_of_le_one_left hrg (Real.exp_le_one_iff.mpr (by nlinarith [hrI.1]))
  have hraw : Real.exp (-c * t) * E t ≤ E 0 + ∫ r in 0..t, g r := by
    have hx := hle.trans hle'
    dsimp [q] at hx
    simp only [mul_zero, Real.exp_zero, one_mul] at hx
    linarith
  have hm := mul_le_mul_of_nonneg_left hraw (Real.exp_pos (c * t)).le
  simpa [← mul_assoc, ← Real.exp_add] using hm

end ExpandedFA.Evolution.HyperbolicWeakEnergyExistence.FiniteEnergy

namespace ExpandedFA.Evolution.HyperbolicWeakEnergyExistence.FiniteEnergy

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- Vector primitives of locally integrable densities are AC on the local interval. -/
lemma vector_primitive_ac {a b : ℝ} {g : ℝ → X}
    (hg : IntervalIntegrable g volume a b) :
    AbsolutelyContinuousOnInterval (fun x => ∫ r in a..x, g r) a b := by
  have hn := hg.norm.absolutelyContinuousOnInterval_intervalIntegral
    (left_mem_uIcc : a ∈ uIcc a b)
  change Tendsto _ _ _ at hn ⊢
  apply squeeze_zero' (.of_forall fun q => Finset.sum_nonneg (fun _ _ => dist_nonneg)) ?_ hn
  rw [eventually_inf_principal]
  filter_upwards with q hq
  apply Finset.sum_le_sum
  intro i hi
  have hmem₁ : (q.2 i).1 ∈ uIcc a b := (hq.1 i hi).1
  have hmem₂ : (q.2 i).2 ∈ uIcc a b := (hq.1 i hi).2
  have h₁ : IntervalIntegrable g volume a (q.2 i).1 :=
    hg.mono_set (uIcc_subset_uIcc left_mem_uIcc hmem₁)
  have h₂ : IntervalIntegrable g volume a (q.2 i).2 :=
    hg.mono_set (uIcc_subset_uIcc left_mem_uIcc hmem₂)
  rw [dist_eq_norm, intervalIntegral.integral_interval_sub_left h₁ h₂,
    Real.dist_eq, intervalIntegral.integral_interval_sub_left h₁.norm h₂.norm]
  exact intervalIntegral.norm_integral_le_abs_integral_norm

end ExpandedFA.Evolution.HyperbolicWeakEnergyExistence.FiniteEnergy

namespace ExpandedFA.Evolution.HyperbolicWeakEnergyExistence.FiniteEnergy
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

lemma continuous_primitive_c1 {g : ℝ → X} (hg : Continuous g) (a : ℝ) :
    ContDiff ℝ 1 (fun x => ∫ r in a..x, g r) := by
  have hd (x : ℝ) : HasDerivAt (fun x => ∫ r in a..x, g r) (g x) x :=
    intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable _ _)
      hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x => (hd x).differentiableAt, ?_⟩
  convert hg using 1
  ext x
  exact (hd x).deriv

lemma primitive_increment_c1 {a b : ℝ} {z g : ℝ → X} (hg : Continuous g)
    (hz : ∀ t ∈ uIcc a b, z t - z a = ∫ r in a..t, g r) :
    ContDiffOn ℝ 1 z (uIcc a b) := by
  apply ((continuous_primitive_c1 hg a).add contDiff_const).contDiffOn.congr
  intro t ht
  exact sub_eq_iff_eq_add.mp (hz t ht)

lemma primitive_increment_ac {a b : ℝ} {z g : ℝ → X}
    (hg : IntervalIntegrable g volume a b)
    (hz : ∀ t ∈ uIcc a b, z t - z a = ∫ r in a..t, g r) :
    AbsolutelyContinuousOnInterval z a b := by
  exact ((vector_primitive_ac hg).add (by simpa using
    (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => z a)).contDiffOn.absolutelyContinuousOnInterval)).congr
    (fun t ht => (sub_eq_iff_eq_add.mp (hz t ht)).symm)

lemma primitive_increment_ae_deriv {a b : ℝ} (hab : a ≤ b) {z g : ℝ → X}
    (hg : IntervalIntegrable g volume a b)
    (hz : ∀ t ∈ Icc a b, z t - z a = ∫ r in a..t, g r) :
    ∀ᵐ t ∂volume, t ∈ Icc a b → HasDerivAt z (g t) t := by
  have hn₁ : ∀ᵐ t ∂volume, t ≠ a := by simp [ae_iff, measure_singleton]
  have hn₂ : ∀ᵐ t ∂volume, t ≠ b := by simp [ae_iff, measure_singleton]
  filter_upwards [hg.ae_hasDerivAt_integral,hn₁,hn₂] with t ht hta htb hti
  have hi : t ∈ Ioo a b := ⟨lt_of_le_of_ne hti.1 (Ne.symm hta),lt_of_le_of_ne hti.2 htb⟩
  have hp := (ht (by simpa [uIcc_of_le hab] using hti) a left_mem_uIcc).const_add (z a)
  apply hp.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hi.1 hi.2] with r hr
  simpa [add_comm] using sub_eq_iff_eq_add.mp (hz r (Ioo_subset_Icc_self hr))

end ExpandedFA.Evolution.HyperbolicWeakEnergyExistence.FiniteEnergy

namespace ExpandedFA.Evolution.HyperbolicWeakEnergyExistence.FiniteEnergy
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

abbrev BilinearForm (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] :=
  X →L[ℝ] X →L[ℝ] ℝ

def energy (J : X →L[ℝ] Y) (b : ℝ → BilinearForm X) (C : ℝ)
    (u v : ℝ → X) (t : ℝ) : ℝ :=
  ‖J (v t)‖ ^ 2 + b t (u t) (u t) + C * ‖J (u t)‖ ^ 2

/-- Scalar C¹ coefficients give C¹ operator coefficients on a finite trial space. -/
lemma finite_form_c1 [FiniteDimensional ℝ X] {T : ℝ} {b : ℝ → BilinearForm X}
    (hb : ∀ x y, ContDiffOn ℝ 1 (fun t => b t x y) (Icc 0 T)) :
    ContDiffOn ℝ 1 b (Icc 0 T) := by
  apply contDiffOn_clm_apply.mpr
  intro x
  exact contDiffOn_clm_apply.mpr (hb x)

lemma energy_ac {T : ℝ} (hT : 0 ≤ T) (J : X →L[ℝ] Y)
    {b : ℝ → BilinearForm X} (hb : ContDiffOn ℝ 1 b (Icc 0 T))
    (C : ℝ) {u v : ℝ → X} (hu : ContDiffOn ℝ 1 u (Icc 0 T))
    (hv : AbsolutelyContinuousOnInterval v 0 T) :
    AbsolutelyContinuousOnInterval (energy J b C u v) 0 T := by
  have hnv : AbsolutelyContinuousOnInterval (fun t => ‖J (v t)‖) 0 T :=
    lipschitzWith_one_norm.comp_absolutelyContinuousOnInterval
      (J.lipschitzWith.comp_absolutelyContinuousOnInterval hv)
  have hkin : AbsolutelyContinuousOnInterval (fun t => ‖J (v t)‖ ^ 2) 0 T := by
    simpa only [sq] using hnv.fun_mul hnv
  have hpot : AbsolutelyContinuousOnInterval (fun t => b t (u t) (u t)) 0 T := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le hT] using (hb.clm_apply hu).clm_apply hu
  have hshift : AbsolutelyContinuousOnInterval (fun t => C * ‖J (u t)‖ ^ 2) 0 T := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le hT, Function.comp_apply] using
      (contDiffOn_const.mul ((J.contDiff.comp_contDiffOn hu).norm_sq ℝ))
  exact (hkin.add hpot).add hshift

lemma energy_ae_deriv {T : ℝ} (J : X →L[ℝ] Y)
    {b : ℝ → BilinearForm X} (hb : ContDiffOn ℝ 1 b (Icc 0 T))
    (C : ℝ) {u v q : ℝ → X}
    (hbsy : ∀ t ∈ Icc 0 T, ∀ x y, b t x y = b t y x)
    (hdu : ∀ᵐ t ∂volume, t ∈ Icc 0 T → HasDerivAt u (v t) t)
    (hdv : ∀ᵐ t ∂volume, t ∈ Icc 0 T → HasDerivAt v (q t) t) :
    ∀ᵐ t ∂volume, t ∈ Icc 0 T →
      HasDerivAt (energy J b C u v)
        (2 * inner ℝ (J (q t)) (J (v t)) +
          2 * b t (u t) (v t) +
          derivWithin (fun r => b r (u t) (u t)) (Icc 0 T) t +
          2 * C * inner ℝ (J (u t)) (J (v t))) t := by
  have hn₁ : ∀ᵐ (t : ℝ) ∂volume, t ≠ 0 := by simp [ae_iff, measure_singleton]
  have hn₂ : ∀ᵐ t ∂volume, t ≠ T := by simp [ae_iff, measure_singleton]
  filter_upwards [hdu,hdv,hn₁,hn₂] with t hut hvt ht0 htT ht
  have hti : t ∈ Ioo 0 T :=
    ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0),lt_of_le_of_ne ht.2 htT⟩
  have hI : Icc (0 : ℝ) T ∈ 𝓝 t := Icc_mem_nhds hti.1 hti.2
  have hb' : HasDerivAt b (derivWithin b (Icc 0 T) t) t :=
    ((hb.differentiableOn (by simp) t ht).hasDerivWithinAt).hasDerivAt hI
  have hscalar : derivWithin (fun r => b r (u t) (u t)) (Icc 0 T) t =
      derivWithin b (Icc 0 T) t (u t) (u t) := by
    have h := (hb'.clm_apply (hasDerivAt_const t (u t))).clm_apply (hasDerivAt_const t (u t))
    simpa using h.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_of_mem_nhds hI)
  have hpot := (hb'.clm_apply (hut ht)).clm_apply (hut ht)
  have huJ := J.hasFDerivAt.comp_hasDerivAt t (hut ht)
  have hvJ := J.hasFDerivAt.comp_hasDerivAt t (hvt ht)
  convert ((hvJ.norm_sq.add hpot).add (huJ.norm_sq.const_mul C)) using 1
  · rfl
  · simp only [Function.comp_apply]
    rw [hscalar,add_apply,hbsy t ht (v t) (u t),
      real_inner_comm (J (v t)) (J (q t))]
    ring

end ExpandedFA.Evolution.HyperbolicWeakEnergyExistence.FiniteEnergy

namespace ExpandedFA.Evolution.HyperbolicWeakEnergyExistence
open HilbertTripleSpec HyperbolicFormSpec HyperbolicWeakEnergySpec FiniteEnergy

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The same energy constant works on every finite trial space and for all L² data. -/
theorem finite_galerkin_energy_bound (j : HilbertTriple V H) (T : ℝ) (hT : 0 ≤ T)
    (a : ℝ → Form V) (α C : ℝ) (ha : FormHypotheses j T a α C) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (E : Submodule ℝ V) [FiniteDimensional ℝ E]
      (f : timeLpValue H 2 T) (u v q : ℝ → E),
      Continuous v → MemLp q 2 (timeMeasureValue T) →
      (∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, u t - u s = ∫ r in s..t, v r) →
      (∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, v t - v s = ∫ r in s..t, q r) →
      (∀ t, ∀ w : E, inner ℝ (j.embedding (q t)) (j.embedding w) + a t (u t) w =
        inner ℝ (f t) (j.embedding w)) →
      ∀ t ∈ Icc 0 T,
        shiftedEnergy j a C t (u t) (j.embedding (v t)) ≤
          Real.exp (c * t) *
            (shiftedEnergy j a C 0 (u 0) (j.embedding (v 0)) + ∫ r in 0..t, ‖f r‖ ^ 2) := by
  obtain ⟨c,hc,hbound⟩ := energy_rhs_bound j T a α C ha
  refine ⟨c,hc,?_⟩
  intro E _ f u v q hvc hqm hu hv hmass
  let : IsFiniteMeasure (timeMeasureValue T) :=
    inferInstanceAs (IsFiniteMeasure (volume.restrict (Ioo 0 T)))
  let J : E →L[ℝ] H := j.embedding.comp E.subtypeL
  let b : ℝ → BilinearForm E := fun t => (a t).bilinearComp E.subtypeL E.subtypeL
  have hb : ContDiffOn ℝ 1 b (Icc 0 T) := by
    apply finite_form_c1
    intro x y
    exact ha.scalarC1 x y
  have hu' : ∀ t ∈ uIcc (0 : ℝ) T, u t - u 0 = ∫ r in 0..t, v r := by
    simpa only [uIcc_of_le hT] using hu 0 ⟨le_rfl,hT⟩
  have hqint : IntervalIntegrable q volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hT).mpr (hqm.integrable (by norm_num))
  have hv' : ∀ t ∈ uIcc (0 : ℝ) T, v t - v 0 = ∫ r in 0..t, q r := by
    simpa only [uIcc_of_le hT] using hv 0 ⟨le_rfl,hT⟩
  have huC : ContDiffOn ℝ 1 u (Icc 0 T) := by
    simpa only [uIcc_of_le hT] using primitive_increment_c1 hvc hu'
  have hvAC := primitive_increment_ac hqint hv'
  have henergyAC := energy_ac hT J hb C huC hvAC
  have hdU := primitive_increment_ae_deriv hT (hvc.intervalIntegrable 0 T) (hu 0 ⟨le_rfl,hT⟩)
  have hdV := primitive_increment_ae_deriv hT hqint (hv 0 ⟨le_rfl,hT⟩)
  have hsym : ∀ t ∈ Icc (0 : ℝ) T, ∀ x y : E, b t x y = b t y x := by
    intro t ht x y
    exact ha.symmetric t ht x y
  have hdE := energy_ae_deriv J hb C hsym hdU hdV
  have hEq (t : ℝ) : energy J b C u v t = shiftedEnergy j a C t (u t) (j.embedding (v t)) := by
    rw [shiftedEnergy_eq]
    rfl
  have hg : IntervalIntegrable (fun t => ‖f t‖ ^ 2) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hT).mpr (Lp.memLp f).norm.integrable_sq
  let D : ℝ → ℝ := fun t =>
    2 * inner ℝ (J (q t)) (J (v t)) + 2 * b t (u t) (v t) +
      derivWithin (fun r => b r (u t) (u t)) (Icc 0 T) t +
      2 * C * inner ℝ (J (u t)) (J (v t))
  have hD : ∀ᵐ t ∂volume, t ∈ Icc 0 T →
      HasDerivAt (energy J b C u v) (D t) t ∧
      D t ≤ c * energy J b C u v t + ‖f t‖ ^ 2 := by
    filter_upwards [hdE] with t ht hti
    refine ⟨ht hti,?_⟩
    have hB := hbound t hti (u t) (j.embedding (v t)) (f t)
    have hm := hmass t (v t)
    rw [← hEq t] at hB
    dsimp [D,J,b]
    linarith
  have hgron := ac_gronwall hT hc henergyAC hg
    (Eventually.of_forall fun t ht => sq_nonneg ‖f t‖) hD
  simpa only [hEq] using hgron

end ExpandedFA.Evolution.HyperbolicWeakEnergyExistence

namespace ExpandedFA.Evolution.HyperbolicWeakEnergyExistence
open HilbertTripleSpec HyperbolicFormSpec HyperbolicWeakEnergySpec FiniteEnergy

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Finite trial-space solutions, with the uniform source energy estimate. -/
theorem finite_galerkin_solution_energy (j : HilbertTriple V H) (T : ℝ) (hT : 0 ≤ T)
    (a : ℝ → Form V) (α C : ℝ) (ha : FormHypotheses j T a α C) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (E : Submodule ℝ V) [FiniteDimensional ℝ E]
      (f : timeLpValue H 2 T) (u₀ v₀ : E),
      ∃ u v q : ℝ → E,
        Continuous u ∧ Continuous v ∧ u 0 = u₀ ∧ v 0 = v₀ ∧
        MemLp q 2 (timeMeasureValue T) ∧
        (∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, u t - u s = ∫ r in s..t, v r) ∧
        (∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, v t - v s = ∫ r in s..t, q r) ∧
        (∀ t, ∀ w : E, inner ℝ (j.embedding (q t)) (j.embedding w) + a t (u t) w =
          inner ℝ (f t) (j.embedding w)) ∧
        (∀ t ∈ Icc 0 T, shiftedEnergy j a C t (u t) (j.embedding (v t)) ≤
          Real.exp (c * t) *
            (shiftedEnergy j a C 0 u₀ (j.embedding v₀) + ∫ r in 0..t, ‖f r‖ ^ 2)) := by
  obtain ⟨c,hc,hbound⟩ := finite_galerkin_energy_bound j T hT a α C ha
  refine ⟨c,hc,?_⟩
  intro E _ f u₀ v₀
  obtain ⟨u,v,q,huc,hvc,hu₀,hv₀,hqm,hu,hv,hq⟩ :=
    finite_galerkin_solution j T hT a ha.scalarC1 E f u₀ v₀
  refine ⟨u,v,q,huc,hvc,hu₀,hv₀,hqm,hu,hv,hq,?_⟩
  simpa only [hu₀,hv₀] using hbound E f u v q hvc hqm hu hv hq

end ExpandedFA.Evolution.HyperbolicWeakEnergyExistence

end FiniteEnergyContext

/- Finite scalar test equations and initial moments. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
namespace ExpandedFA.Evolution.HyperbolicWeakEnergyExistence.GalerkinNet
open HilbertTripleSpec HyperbolicFormSpec HyperbolicWeakEnergySpec

/-- An integral solution with merely integrable derivative satisfies the genuine vector graph. -/
theorem derivativeValue_of_integral_increments {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : ℝ) (hT : 0 ≤ T) (U g : ℝ → E)
    (hU : Integrable U (timeMeasureValue T)) (hg : Integrable g (timeMeasureValue T))
    (hinc : ∀ s t : Set.Icc 0 T, U t - U s = ∫ r in s.val..t.val, g r) :
    derivativeValue T U g := by
  refine ⟨(show IntegrableOn U (Set.Ioo 0 T) volume from hU).locallyIntegrableOn,
    (show IntegrableOn g (Set.Ioo 0 T) volume from hg).locallyIntegrableOn, ?_⟩
  intro φ hφ
  let G := (Set.Ioo 0 T).indicator g
  have hG : Integrable G volume := (integrable_indicator_iff measurableSet_Ioo).mpr hg
  have hi (a b : ℝ) : IntervalIntegrable G volume a b := hG.intervalIntegrable
  let P : ℝ → E := fun t => ∫ r in 0..t, G r
  have hP : Continuous P := intervalIntegral.continuous_primitive hi 0
  have hGP : G =ᵐ[timeMeasureValue T] g := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact Set.indicator_of_mem ht g
  have hUP : U =ᵐ[timeMeasureValue T] (fun t => U 0 + P t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have he := hinc ⟨0,le_rfl,hT⟩ ⟨t, Set.Ioo_subset_Icc_self ht⟩
    have heq := time_integral_congr_ae T hGP ⟨0,le_rfl,hT⟩ ⟨t,Set.Ioo_subset_Icc_self ht⟩
    change U t - U 0 = ∫ r in 0..t, g r at he
    change P t = ∫ r in 0..t, g r at heq
    rw [← heq] at he
    exact (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)
  have hdφ : Continuous (deriv φ) := hφ.1.continuous_deriv (by simp)
  have hdφint : Integrable (deriv φ) volume := hdφ.integrable_of_hasCompactSupport hφ.2.1.deriv
  have hφzero : (∫ t, deriv φ t ∂timeMeasureValue T) = 0 := by
    change (∫ t in Set.Ioo 0 T, deriv φ t) = 0
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hT]
    rw [intervalIntegral.integral_deriv_eq_sub
      (fun _ _ => hφ.1.differentiable (by simp) _)
      (hdφ.intervalIntegrable 0 T)]
    have hzero : φ 0 = 0 := image_eq_zero_of_notMem_tsupport (fun h => (hφ.2.2 h).1.false)
    have hlast : φ T = 0 := image_eq_zero_of_notMem_tsupport (fun h => (hφ.2.2 h).2.false)
    rw [hzero, hlast, sub_self]
  have hpint : Integrable (fun t => deriv φ t • P t) volume :=
    (hdφ.smul hP).integrable_of_hasCompactSupport hφ.2.1.deriv.smul_right
  have hconstint : Integrable (fun t => deriv φ t • U 0) (timeMeasureValue T) :=
    hdφint.integrableOn.smul_const _
  have hpsupport : Function.support (fun t => deriv φ t • P t) ⊆ Set.Ioo 0 T := by
    intro t ht
    apply hφ.2.2
    apply support_deriv_subset
    exact (smul_ne_zero_iff.mp ht).1
  have hfull : (∫ t, deriv φ t • P t ∂timeMeasureValue T) =
      ∫ t, deriv φ t • P t :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => by
      have hz : t ∉ Function.support (fun r => deriv φ r • P r) :=
        fun hm => ht (hpsupport hm)
      exact Function.notMem_support.mp hz
  rw [integral_congr_ae (hUP.mono fun _ h => congrArg (fun z => deriv φ _ • z) h)]
  simp_rw [smul_add]
  rw [integral_add hconstint hpint.integrableOn, integral_smul_const, hφzero, zero_smul,
    zero_add, hfull]
  have he := integral_test_smul_primitive hG.locallyIntegrable 0 hφ.1 hφ.2.1
  change (∫ t, deriv φ t • P t) = -(∫ t, φ t • G t) at he
  rw [he]
  congr 1
  simp only [G, ← Set.indicator_smul_apply, integral_indicator measurableSet_Ioo,
    timeMeasureValue]

section FiniteTests
variable {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

def trialPairing (j : HilbertTriple V H) (E : Submodule ℝ V) (w : E) : E →L[ℝ] ℝ :=
  ((innerSL ℝ) (j.embedding w)).comp (j.embedding.comp E.subtypeL)

@[simp] theorem trialPairing_apply (j : HilbertTriple V H)
    (E : Submodule ℝ V) (w z : E) :
    trialPairing j E w z = inner ℝ (j.embedding z) (j.embedding w) := by
  simp only [trialPairing, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    Submodule.subtypeL_apply, real_inner_comm]

/-- Scalar equations use only the tested trial acceleration. -/
theorem finite_galerkin_test_derivative (j : HilbertTriple V H) (T : ℝ) (hT : 0 ≤ T)
    (a : ℝ → Form V) (E : Submodule ℝ V) [FiniteDimensional ℝ E]
    (u v q : ℝ → E) (f : ℝ → H) (hvc : Continuous v)
    (hqm : MemLp q 2 (timeMeasureValue T))
    (hinc : ∀ s t : Set.Icc 0 T, v t - v s = ∫ r in s.val..t.val, q r)
    (hmass : ∀ t, ∀ w : E, inner ℝ (j.embedding (q t)) (j.embedding w) + a t (u t) w =
      inner ℝ (f t) (j.embedding w)) (w : E) :
    derivativeValue T (fun t => inner ℝ (j.embedding (v t)) (j.embedding w))
      (fun t => inner ℝ (f t) (j.embedding w) - a t (u t) w) := by
  letI : IsFiniteMeasure (timeMeasureValue T) :=
    inferInstanceAs (IsFiniteMeasure (volume.restrict (Set.Ioo 0 T)))
  have hgraph : derivativeValue T v q :=
    derivativeValue_of_integral_increments T hT v q
      ((continuousOn_time_memLp hvc.continuousOn : MemLp v 2 _).integrable (by norm_num))
      (hqm.integrable (by norm_num)) hinc
  have he (t : ℝ) : trialPairing j E w (q t) =
      inner ℝ (f t) (j.embedding w) - a t (u t) w := by
    rw [trialPairing_apply]
    linarith [hmass t w]
  simpa only [HasTimeDerivative, trialPairing_apply, he] using
    hasTimeDerivative_map (trialPairing j E w) T v q hgraph

/-- The tested endpoint moment is independent of the trial acceleration after using its equation. -/
theorem finite_galerkin_test_moment (j : HilbertTriple V H) (T : ℝ) (hT : 0 ≤ T)
    (a : ℝ → Form V) (E : Submodule ℝ V) [FiniteDimensional ℝ E]
    (u v q : ℝ → E) (f : ℝ → H)
    (hqm : MemLp q 2 (timeMeasureValue T))
    (hinc : ∀ s t : Set.Icc 0 T, v t - v s = ∫ r in s.val..t.val, q r)
    (hmass : ∀ t, ∀ w : E, inner ℝ (j.embedding (q t)) (j.embedding w) + a t (u t) w =
      inner ℝ (f t) (j.embedding w)) (w : E) :
    (∫ t, inner ℝ (j.embedding (v t)) (j.embedding w) ∂timeMeasureValue T) -
      (∫ t, (T-t) * (inner ℝ (f t) (j.embedding w) - a t (u t) w)
        ∂timeMeasureValue T) = T * inner ℝ (j.embedding (v 0)) (j.embedding w) := by
  letI : IsFiniteMeasure (timeMeasureValue T) :=
    inferInstanceAs (IsFiniteMeasure (volume.restrict (Set.Ioo 0 T)))
  have hqi : Integrable q (timeMeasureValue T) := hqm.integrable (by norm_num)
  have hqI : IntervalIntegrable q volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hT).mpr hqi
  have hLinc : ∀ s t : Set.Icc 0 T,
      trialPairing j E w (v t) - trialPairing j E w (v s) =
        ∫ r in s.val..t.val, trialPairing j E w (q r) := by
    intro s t
    rw [← map_sub, hinc]
    apply ((trialPairing j E w).intervalIntegral_comp_comm ?_).symm
    exact hqI.mono_set (by simpa only [Set.uIcc_of_le hT] using (Set.uIcc_subset_Icc s.property t.property))
  have he (t : ℝ) : trialPairing j E w (q t) =
      inner ℝ (f t) (j.embedding w) - a t (u t) w := by
    rw [trialPairing_apply]
    linarith [hmass t w]
  simpa only [trialPairing_apply, he, smul_eq_mul] using
    primitive_endpoint_moment T hT (fun t => trialPairing j E w (v t))
      (fun t => trialPairing j E w (q t)) ((trialPairing j E w).integrable_comp hqi) hLinc

end FiniteTests
end ExpandedFA.Evolution.HyperbolicWeakEnergyExistence.GalerkinNet

/- Weak passage through the fixed embedding and initial moments. -/
namespace ExpandedFA.Evolution.HyperbolicWeakEnergyExistence
open HilbertTripleSpec

section MappedWeakGraph
variable {E : Type u} {B : Type v}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

/-- A constant spatial continuous linear map preserves weak Bochner L² convergence. -/
theorem weak_L2_map {ι : Type*} (F : Filter ι) (T : ℝ) (A : E →L[ℝ] B)
    (u : ι → Lp E 2 (timeMeasureValue T)) (x : Lp E 2 (timeMeasureValue T))
    (hu : ∀ L : StrongDual ℝ (Lp E 2 (timeMeasureValue T)),
      Tendsto (fun i => L (u i)) F (𝓝 (L x))) :
    ∀ L : StrongDual ℝ (Lp B 2 (timeMeasureValue T)),
      Tendsto (fun i => L (A.compLpL 2 (timeMeasureValue T) (u i))) F
        (𝓝 (L (A.compLpL 2 (timeMeasureValue T) x))) := by
  intro L
  exact hu (L.comp (A.compLpL 2 (timeMeasureValue T)))

/-- Weak L² limits preserve a derivative graph after a fixed spatial map. -/
theorem mapped_derivativeValue_of_weak_L2_limits {ι : Type*} (F : Filter ι) [NeBot F]
    (T : ℝ) (A : E →L[ℝ] B)
    (u : ι → Lp E 2 (timeMeasureValue T)) (v : ι → Lp B 2 (timeMeasureValue T))
    (x : Lp E 2 (timeMeasureValue T)) (y : Lp B 2 (timeMeasureValue T))
    (hu : ∀ L : StrongDual ℝ (Lp E 2 (timeMeasureValue T)),
      Tendsto (fun i => L (u i)) F (𝓝 (L x)))
    (hv : ∀ L : StrongDual ℝ (Lp B 2 (timeMeasureValue T)),
      Tendsto (fun i => L (v i)) F (𝓝 (L y)))
    (hgraph : ∀ᶠ i in F, derivativeValue T (fun t => A (u i t)) (v i)) :
    derivativeValue T (fun t => A (x t)) y := by
  have hg : ∀ᶠ i in F,
      derivativeValue T (A.compLpL 2 (timeMeasureValue T) (u i)) (v i) := by
    filter_upwards [hgraph] with i hi
    exact (hasTimeDerivative_congr T _ _ _ _
      (A.coeFn_compLpL (u i)) EventuallyEq.rfl).mpr hi
  have hd := derivativeValue_of_weak_L2_limits F T
    (fun i => A.compLpL 2 (timeMeasureValue T) (u i)) v
    (A.compLpL 2 (timeMeasureValue T) x) y (weak_L2_map F T A u x hu) hv hg
  exact (hasTimeDerivative_congr T _ _ _ _
    (A.coeFn_compLpL x) EventuallyEq.rfl).mp hd

/-- The mapped initial endpoint moment passes to weak L² limits. -/
theorem mapped_endpoint_moment_of_weak_L2_limits {ι : Type*} (F : Filter ι) [NeBot F]
    (T : ℝ) (A : E →L[ℝ] B)
    (u : ι → Lp E 2 (timeMeasureValue T)) (v : ι → Lp B 2 (timeMeasureValue T))
    (x : Lp E 2 (timeMeasureValue T)) (y : Lp B 2 (timeMeasureValue T))
    (hu : ∀ L : StrongDual ℝ (Lp E 2 (timeMeasureValue T)),
      Tendsto (fun i => L (u i)) F (𝓝 (L x)))
    (hv : ∀ L : StrongDual ℝ (Lp B 2 (timeMeasureValue T)),
      Tendsto (fun i => L (v i)) F (𝓝 (L y)))
    (e : ι → B) (e₀ : B) (he : Tendsto e F (𝓝 e₀))
    (hm : ∀ᶠ i in F, (∫ t, A (u i t) ∂timeMeasureValue T) -
      (∫ t, (T-t) • v i t ∂timeMeasureValue T) = T • e i) :
    (∫ t, A (x t) ∂timeMeasureValue T) -
      (∫ t, (T-t) • y t ∂timeMeasureValue T) = T • e₀ := by
  have hm' : ∀ᶠ i in F,
      (∫ t, (A.compLpL 2 (timeMeasureValue T) (u i)) t ∂timeMeasureValue T) -
      (∫ t, (T-t) • v i t ∂timeMeasureValue T) = T • e i := by
    filter_upwards [hm] with i hi
    rw [integral_congr_ae (A.coeFn_compLpL (u i))]
    exact hi
  have hlim := endpoint_moment_of_weak_L2_limits F T
    (fun i => A.compLpL 2 (timeMeasureValue T) (u i)) v
    (A.compLpL 2 (timeMeasureValue T) x) y (weak_L2_map F T A u x hu) hv e e₀ he hm'
  rwa [integral_congr_ae (A.coeFn_compLpL x)] at hlim

end MappedWeakGraph
end ExpandedFA.Evolution.HyperbolicWeakEnergyExistence

namespace ExpandedFA.Evolution.HyperbolicWeakEnergyExistence.GalerkinNet
open HilbertTripleSpec HyperbolicFormSpec HyperbolicWeakEnergySpec
section WeakScalarTests
variable {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
def scalarVelocityCLM (j : HilbertTriple V H) (T : ℝ) (w : V) :
    Lp H 2 (timeMeasureValue T) →L[ℝ] Lp ℝ 2 (timeMeasureValue T) :=
  ((innerSL ℝ) (j.embedding w)).compLpL 2 (timeMeasureValue T)

theorem coeFn_scalarVelocityCLM (j : HilbertTriple V H) (T : ℝ) (w : V)
    (v : Lp H 2 (timeMeasureValue T)) :
    scalarVelocityCLM j T w v =ᵐ[timeMeasureValue T]
      fun t => inner ℝ (v t) (j.embedding w) := by
  filter_upwards [((innerSL ℝ) (j.embedding w)).coeFn_compLpL v] with t ht
  simpa only [scalarVelocityCLM, innerSL_apply_apply, real_inner_comm] using ht

def scalarDualCLM (T : ℝ) (w : V) :
    Lp (StrongDual ℝ V) 2 (timeMeasureValue T) →L[ℝ] Lp ℝ 2 (timeMeasureValue T) :=
  (ContinuousLinearMap.apply ℝ ℝ w).compLpL 2 (timeMeasureValue T)

theorem coeFn_scalarDualCLM (T : ℝ) (w : V)
    (g : Lp (StrongDual ℝ V) 2 (timeMeasureValue T)) :
    scalarDualCLM T w g =ᵐ[timeMeasureValue T] fun t => g t w := by
  exact (ContinuousLinearMap.apply ℝ ℝ w).coeFn_compLpL g

/-- Pass the mass equation using only weak displacement and velocity limits.
The form multiplier is an actual continuous linear map with its a.e. coefficient law. -/
theorem wave_tests_of_weak_L2_limits {ι : Type*} (F : Filter ι) [NeBot F]
    (j : HilbertTriple V H) (T : ℝ) (a : ℝ → Form V)
    (M : Lp V 2 (timeMeasureValue T) →L[ℝ] Lp (StrongDual ℝ V) 2 (timeMeasureValue T))
    (hM : ∀ z : Lp V 2 (timeMeasureValue T),
      M z =ᵐ[timeMeasureValue T] fun t => a t (z t))
    (u : ι → Lp V 2 (timeMeasureValue T)) (v : ι → Lp H 2 (timeMeasureValue T))
    (x : Lp V 2 (timeMeasureValue T)) (y f : Lp H 2 (timeMeasureValue T))
    (hu : ∀ L : StrongDual ℝ (Lp V 2 (timeMeasureValue T)),
      Tendsto (fun i => L (u i)) F (𝓝 (L x)))
    (hv : ∀ L : StrongDual ℝ (Lp H 2 (timeMeasureValue T)),
      Tendsto (fun i => L (v i)) F (𝓝 (L y)))
    (hgraph : ∀ w : V, ∀ᶠ i in F,
      derivativeValue T (fun t => inner ℝ (v i t) (j.embedding w))
        (fun t => inner ℝ (f t) (j.embedding w) - a t (u i t) w)) :
    WaveTestEquation j T a x y f := by
  intro w
  let P := scalarVelocityCLM j T w
  let Q := (scalarDualCLM T w).comp M
  let r := P f
  have hP (z : Lp H 2 (timeMeasureValue T)) :
      P z =ᵐ[timeMeasureValue T] fun t => inner ℝ (z t) (j.embedding w) :=
    coeFn_scalarVelocityCLM j T w z
  have hQ (z : Lp V 2 (timeMeasureValue T)) :
      Q z =ᵐ[timeMeasureValue T] fun t => a t (z t) w := by
    filter_upwards [coeFn_scalarDualCLM T w (M z), hM z] with t ht hm
    simpa only [Q, ContinuousLinearMap.comp_apply, hm] using ht
  have hG (z : Lp V 2 (timeMeasureValue T)) :
      r - Q z =ᵐ[timeMeasureValue T]
        fun t => inner ℝ (f t) (j.embedding w) - a t (z t) w := by
    filter_upwards [Lp.coeFn_sub r (Q z), hP f, hQ z] with t ht hp hq
    simpa only [r, Pi.sub_apply, hp, hq] using ht
  have hgraph' : ∀ᶠ i in F, derivativeValue T (P (v i))
      ((r - Q (u i) : Lp ℝ 2 (timeMeasureValue T)) : ℝ → ℝ) := by
    filter_upwards [hgraph w] with i hi
    exact (hasTimeDerivative_congr T _ _ _ _ (hP (v i)).symm (hG (u i)).symm).mp hi
  have hweakP (L : StrongDual ℝ (Lp ℝ 2 (timeMeasureValue T))) :
      Tendsto (fun i => L (P (v i))) F (𝓝 (L (P y))) := hv (L.comp P)
  have hweakQ (L : StrongDual ℝ (Lp ℝ 2 (timeMeasureValue T))) :
      Tendsto (fun i => L (r - Q (u i))) F (𝓝 (L (r - Q x))) := by
    simp only [map_sub]
    exact tendsto_const_nhds.sub (hu (L.comp Q))
  have hlim := derivativeValue_of_weak_L2_limits F T
    (fun i => P (v i)) (fun i => r - Q (u i)) (P y) (r-Q x) hweakP hweakQ hgraph'
  exact (hasTimeDerivative_congr T _ _ _ _ (hP y) (hG x)).mp hlim

end WeakScalarTests
end ExpandedFA.Evolution.HyperbolicWeakEnergyExistence.GalerkinNet

namespace ExpandedFA.Evolution.HyperbolicWeakEnergyExistence.GalerkinNet
open HilbertTripleSpec HyperbolicFormSpec HyperbolicWeakEnergySpec
variable {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
/-- The initial velocity moment passes through weak L² limits, with only eventual membership
of each fixed spatial test in the Galerkin spaces. -/
theorem scalar_velocity_moment_of_weak_L2_limits {ι : Type*} (F : Filter ι) [NeBot F]
    (j : HilbertTriple V H) (T : ℝ) (a : ℝ → Form V)
    (M : Lp V 2 (timeMeasureValue T) →L[ℝ] Lp (StrongDual ℝ V) 2 (timeMeasureValue T))
    (hM : ∀ z : Lp V 2 (timeMeasureValue T),
      M z =ᵐ[timeMeasureValue T] fun t => a t (z t))
    (u : ι → Lp V 2 (timeMeasureValue T)) (v : ι → Lp H 2 (timeMeasureValue T))
    (x : Lp V 2 (timeMeasureValue T)) (y f : Lp H 2 (timeMeasureValue T)) (v₀ : H)
    (hu : ∀ L : StrongDual ℝ (Lp V 2 (timeMeasureValue T)),
      Tendsto (fun i => L (u i)) F (𝓝 (L x)))
    (hv : ∀ L : StrongDual ℝ (Lp H 2 (timeMeasureValue T)),
      Tendsto (fun i => L (v i)) F (𝓝 (L y)))
    (hmoment : ∀ w : V, ∀ᶠ i in F,
      (∫ t, inner ℝ (v i t) (j.embedding w) ∂timeMeasureValue T) -
        (∫ t, (T-t) * (inner ℝ (f t) (j.embedding w) - a t (u i t) w)
          ∂timeMeasureValue T) = T * inner ℝ v₀ (j.embedding w)) :
    ∀ w : V, (∫ t, inner ℝ (y t) (j.embedding w) ∂timeMeasureValue T) -
      (∫ t, (T-t) * (inner ℝ (f t) (j.embedding w) - a t (x t) w)
        ∂timeMeasureValue T) = T * inner ℝ v₀ (j.embedding w) := by
  intro w
  let P := scalarVelocityCLM j T w
  let Q := (scalarDualCLM T w).comp M
  let r := P f
  have hP (z : Lp H 2 (timeMeasureValue T)) :
      P z =ᵐ[timeMeasureValue T] fun t => inner ℝ (z t) (j.embedding w) :=
    coeFn_scalarVelocityCLM j T w z
  have hQ (z : Lp V 2 (timeMeasureValue T)) :
      Q z =ᵐ[timeMeasureValue T] fun t => a t (z t) w := by
    filter_upwards [coeFn_scalarDualCLM T w (M z), hM z] with t ht hm
    simpa only [Q, ContinuousLinearMap.comp_apply, hm] using ht
  have hG (z : Lp V 2 (timeMeasureValue T)) :
      r - Q z =ᵐ[timeMeasureValue T]
        fun t => inner ℝ (f t) (j.embedding w) - a t (z t) w := by
    filter_upwards [Lp.coeFn_sub r (Q z), hP f, hQ z] with t ht hp hq
    simpa only [r, Pi.sub_apply, hp, hq] using ht
  have hweakP (L : StrongDual ℝ (Lp ℝ 2 (timeMeasureValue T))) :
      Tendsto (fun i => L (P (v i))) F (𝓝 (L (P y))) := hv (L.comp P)
  have hweakQ (L : StrongDual ℝ (Lp ℝ 2 (timeMeasureValue T))) :
      Tendsto (fun i => L (r - Q (u i))) F (𝓝 (L (r - Q x))) := by
    simp only [map_sub]
    exact tendsto_const_nhds.sub (hu (L.comp Q))
  have hm' : ∀ᶠ i in F,
      (∫ t, P (v i) t ∂timeMeasureValue T) -
        (∫ t, (T-t) • (r - Q (u i) : Lp ℝ 2 (timeMeasureValue T)) t
          ∂timeMeasureValue T) = T • inner ℝ v₀ (j.embedding w) := by
    filter_upwards [hmoment w] with i hi
    rw [integral_congr_ae (hP (v i)), integral_congr_ae ((hG (u i)).mono
      fun t ht => congrArg (fun z : ℝ => (T-t) • z) ht)]
    exact hi
  have hlim := endpoint_moment_of_weak_L2_limits F T
    (fun i => P (v i)) (fun i => r - Q (u i)) (P y) (r-Q x)
    hweakP hweakQ (fun _ => inner ℝ v₀ (j.embedding w))
    (inner ℝ v₀ (j.embedding w)) tendsto_const_nhds hm'
  rw [integral_congr_ae (hP y), integral_congr_ae ((hG x).mono
    fun t ht => congrArg (fun z : ℝ => (T-t) • z) ht)] at hlim
  exact hlim

/-- Scalar moments recover the vector V′ moment, using genuine integrability. -/
theorem dual_moment_of_scalar_moments (j : HilbertTriple V H) (T : ℝ)
    (a : ℝ → Form V) (u : ℝ → V) (v f : ℝ → H) (v₀ : H)
    (hv : MemLp v 2 (timeMeasureValue T))
    (hg : MemLp (fun t => pivotValue j (f t) - a t (u t)) 2 (timeMeasureValue T))
    (hm : ∀ w : V,
      (∫ t, inner ℝ (v t) (j.embedding w) ∂timeMeasureValue T) -
        (∫ t, (T-t) * (inner ℝ (f t) (j.embedding w) - a t (u t) w)
          ∂timeMeasureValue T) = T * inner ℝ v₀ (j.embedding w)) :
    (∫ t, pivotValue j (v t) ∂timeMeasureValue T) -
      (∫ t, (T-t) • (pivotValue j (f t) - a t (u t)) ∂timeMeasureValue T) =
      T • pivotValue j v₀ := by
  let : IsFiniteMeasure (timeMeasureValue T) :=
    inferInstanceAs (IsFiniteMeasure (volume.restrict (Set.Ioo 0 T)))
  have hvi : Integrable (fun t => pivotValue j (v t)) (timeMeasureValue T) :=
    ((pivotValue j).comp_memLp' hv).integrable (by norm_num)
  have hgi : Integrable (fun t => (T-t) • (pivotValue j (f t) - a t (u t)))
      (timeMeasureValue T) :=
    (hg.integrable (by norm_num)).smul_of_top_right
      (continuousOn_time_memLp (continuous_const.sub continuous_id).continuousOn)
  apply ContinuousLinearMap.ext
  intro w
  rw [sub_apply, ContinuousLinearMap.integral_apply hvi,
    ContinuousLinearMap.integral_apply hgi]
  have hpair (h : H) : pivotValue j h w = inner ℝ h (j.embedding w) :=
    pivotInjection_apply j h w
  simpa only [hpair, smul_apply, sub_apply, smul_eq_mul] using hm w

/-- The complete vector initial velocity moment follows from the Galerkin scalar moments. -/
theorem velocity_moment_of_weak_L2_limits {ι : Type*} (F : Filter ι) [NeBot F]
    (j : HilbertTriple V H) (T : ℝ) (a : ℝ → Form V) (ha : ScalarC1 T a)
    (u : ι → Lp V 2 (timeMeasureValue T)) (v : ι → Lp H 2 (timeMeasureValue T))
    (x : Lp V 2 (timeMeasureValue T)) (y f : Lp H 2 (timeMeasureValue T)) (v₀ : H)
    (hu : ∀ L : StrongDual ℝ (Lp V 2 (timeMeasureValue T)),
      Tendsto (fun i => L (u i)) F (𝓝 (L x)))
    (hv : ∀ L : StrongDual ℝ (Lp H 2 (timeMeasureValue T)),
      Tendsto (fun i => L (v i)) F (𝓝 (L y)))
    (hmoment : ∀ w : V, ∀ᶠ i in F,
      (∫ t, inner ℝ (v i t) (j.embedding w) ∂timeMeasureValue T) -
        (∫ t, (T-t) * (inner ℝ (f t) (j.embedding w) - a t (u i t) w)
          ∂timeMeasureValue T) = T * inner ℝ v₀ (j.embedding w)) :
    (∫ t, pivotValue j (y t) ∂timeMeasureValue T) -
      (∫ t, (T-t) • (pivotValue j (f t) - a t (x t)) ∂timeMeasureValue T) =
      T • pivotValue j v₀ := by
  have hg : MemLp (fun t => pivotValue j (f t) - a t (x t)) 2 (timeMeasureValue T) :=
    ((pivotValue j).comp_memLp' (Lp.memLp f)).sub (form_apply_memLp T a ha x (Lp.memLp x))
  exact dual_moment_of_scalar_moments j T a x y f v₀ (Lp.memLp y) hg
    (scalar_velocity_moment_of_weak_L2_limits F j T a (formMultiplier T a ha)
      (coeFn_formMultiplier T a ha) u v x y f v₀ hu hv hmoment)

end ExpandedFA.Evolution.HyperbolicWeakEnergyExistence.GalerkinNet


namespace ExpandedFA.Evolution.HyperbolicWeakEnergyExistence.GalerkinNet
open HilbertTripleSpec HyperbolicFormSpec HyperbolicWeakEnergySpec
variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem exists_uniform_galerkin_L2_family (j : HilbertTriple V H) (T : ℝ) (hT : 0 ≤ T)
    (a : ℝ → Form V) (α C : ℝ) (ha : FormHypotheses j T a α C) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (u₀ : V) (v₀ : H) (f : timeLpValue H 2 T),
      ∃ (R : ℝ) (U : Finset V → Lp V 2 (timeMeasureValue T))
        (W : Finset V → Lp H 2 (timeMeasureValue T)),
        0 ≤ R ∧
        (∀ s, ∀ᵐ t ∂timeMeasureValue T, ‖U s t‖ ≤ R) ∧
        (∀ s, ∀ᵐ t ∂timeMeasureValue T, ‖W s t‖ ≤ R) ∧
        (∀ s, ∀ᵐ t ∂timeMeasureValue T,
          shiftedEnergy j a C t (U s t) (W s t) ≤
            Real.exp (c * t) *
              (shiftedEnergy j a C 0 u₀ v₀ + ∫ r in 0..t, ‖f r‖ ^ 2)) ∧
        (∀ s, derivativeValue T (fun t => j.embedding (U s t)) (W s)) ∧
        (∀ s, (∫ t, j.embedding (U s t) ∂timeMeasureValue T) -
          (∫ t, (T-t) • W s t ∂timeMeasureValue T) = T • j.embedding u₀) ∧
        (∀ w : V, ∀ᶠ s : Finset V in atTop,
          derivativeValue T (fun t => inner ℝ (W s t) (j.embedding w))
            (fun t => inner ℝ (f t) (j.embedding w) - a t (U s t) w) ∧
          ((∫ t, inner ℝ (W s t) (j.embedding w) ∂timeMeasureValue T) -
            (∫ t, (T-t) * (inner ℝ (f t) (j.embedding w) - a t (U s t) w)
              ∂timeMeasureValue T) = T * inner ℝ v₀ (j.embedding w))) := by
  classical
  obtain ⟨c,hc,hsol⟩ := finite_galerkin_solution_energy j T hT a α C ha
  obtain ⟨K,hK,hstate⟩ := state_bound_of_gronwall j T hT a α C ha c hc
  refine ⟨c,hc,?_⟩
  intro u₀ v₀ f
  let : IsFiniteMeasure (timeMeasureValue T) :=
    inferInstanceAs (IsFiniteMeasure (volume.restrict (Set.Ioo 0 T)))
  have hsols (s : Finset V) :=
    hsol (trialSpace u₀ s) f (initialDisplacement u₀ s) (initialVelocity j u₀ v₀ s)
  choose u v q huc hvc hu₀ hv₀ hqm hu hv hmass henergy using hsols
  let x : Finset V → ℝ → V := fun s t => (u s t : V)
  let y : Finset V → ℝ → H := fun s t => j.embedding (v s t)
  have hxc (s : Finset V) : Continuous (x s) :=
    (trialSpace u₀ s).subtypeL.continuous.comp (huc s)
  have hyc (s : Finset V) : Continuous (y s) :=
    j.embedding.continuous.comp ((trialSpace u₀ s).subtypeL.continuous.comp (hvc s))
  have hxM (s : Finset V) : MemLp (x s) 2 (timeMeasureValue T) :=
    continuousOn_time_memLp (hxc s).continuousOn
  have hyM (s : Finset V) : MemLp (y s) 2 (timeMeasureValue T) :=
    continuousOn_time_memLp (hyc s).continuousOn
  let U : Finset V → Lp V 2 (timeMeasureValue T) := fun s => (hxM s).toLp (x s)
  let W : Finset V → Lp H 2 (timeMeasureValue T) := fun s => (hyM s).toLp (y s)
  have hU (s : Finset V) : U s =ᵐ[timeMeasureValue T] x s := (hxM s).coeFn_toLp
  have hW (s : Finset V) : W s =ᵐ[timeMeasureValue T] y s := (hyM s).coeFn_toLp
  have hcommon (s : Finset V) : ∀ t ∈ Set.Icc 0 T,
      shiftedEnergy j a C t (x s t) (y s t) ≤
        Real.exp (c*t) * (shiftedEnergy j a C 0 u₀ v₀ + ∫ r in 0..t, ‖f r‖ ^ 2) := by
    intro t ht
    apply (henergy s t ht).trans
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    exact add_le_add (initial_energy_le j u₀ v₀ (fun x y => shiftedForm j a C 0 x y) s) le_rfl
  let D := K * (‖u₀‖ ^ 2 + ‖v₀‖ ^ 2 + ‖f‖ ^ 2)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let R := Real.sqrt D
  have hR : 0 ≤ R := Real.sqrt_nonneg D
  have hrawBound (s : Finset V) (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
      ‖x s t‖ ≤ R ∧ ‖y s t‖ ≤ R := by
    have h := hstate u₀ v₀ f (x s) (y s) (hcommon s) t ht
    have hsq : R ^ 2 = D := Real.sq_sqrt hD
    constructor <;> nlinarith [sq_nonneg ‖x s t‖, sq_nonneg ‖y s t‖]
  have hyI (s : Finset V) : Integrable (y s) (timeMeasureValue T) := (hyM s).integrable (by norm_num)
  have hxJI (s : Finset V) : Integrable (fun t => j.embedding (x s t)) (timeMeasureValue T) :=
    j.embedding.integrable_comp ((hxM s).integrable (by norm_num))
  have hxInc (s : Finset V) : ∀ r t : Set.Icc 0 T,
      j.embedding (x s t) - j.embedding (x s r) = ∫ z in r.val..t.val, y s z := by
    intro r t
    let J : trialSpace u₀ s →L[ℝ] H := j.embedding.comp (trialSpace u₀ s).subtypeL
    change J (u s t) - J (u s r) = ∫ z in r.val..t.val, J (v s z)
    rw [← map_sub, hu s r r.property t t.property]
    exact (J.intervalIntegral_comp_comm ((hvc s).intervalIntegrable _ _)).symm
  have hxDer (s : Finset V) : derivativeValue T (fun t => j.embedding (x s t)) (y s) :=
    derivativeValue_of_integral_increments T hT _ _ (hxJI s) (hyI s) (hxInc s)
  have hxMom (s : Finset V) : (∫ t, j.embedding (x s t) ∂timeMeasureValue T) -
      (∫ t, (T-t) • y s t ∂timeMeasureValue T) = T • j.embedding u₀ := by
    have h := primitive_endpoint_moment T hT (fun t => j.embedding (x s t)) (y s) (hyI s) (hxInc s)
    simpa only [x, hu₀,coe_initialDisplacement] using h
  refine ⟨R,U,W,hR,?_,?_,?_,?_,?_,?_⟩
  · intro s
    filter_upwards [hU s,ae_restrict_mem measurableSet_Ioo] with t ht hti
    rw [ht]
    exact (hrawBound s t (Set.Ioo_subset_Icc_self hti)).1
  · intro s
    filter_upwards [hW s,ae_restrict_mem measurableSet_Ioo] with t ht hti
    rw [ht]
    exact (hrawBound s t (Set.Ioo_subset_Icc_self hti)).2
  · intro s
    filter_upwards [hU s,hW s,ae_restrict_mem measurableSet_Ioo] with t hut hwt hti
    rw [hut,hwt]
    exact hcommon s t (Set.Ioo_subset_Icc_self hti)
  · intro s
    apply (hasTimeDerivative_congr T _ _ _ _ ?_ (hW s).symm).mp (hxDer s)
    exact (hU s).symm.mono fun t ht => congrArg j.embedding ht
  · intro s
    rw [integral_congr_ae ((hU s).mono fun t ht => congrArg j.embedding ht),
      integral_congr_ae ((hW s).mono fun t ht => congrArg (fun z => (T-t) • z) ht)]
    exact hxMom s
  · intro w
    filter_upwards [eventually_mem_trialSpace u₀ w] with s hws
    let wE : trialSpace u₀ s := ⟨w,hws⟩
    have hinc : ∀ r t : Set.Icc 0 T, v s t - v s r = ∫ z in r.val..t.val, q s z := by
      intro r t; exact hv s r r.property t t.property
    have hd := finite_galerkin_test_derivative j T hT a (trialSpace u₀ s)
      (u s) (v s) (q s) f (hvc s) (hqm s) hinc (hmass s) wE
    have hm := finite_galerkin_test_moment j T hT a (trialSpace u₀ s)
      (u s) (v s) (q s) f (hqm s) hinc (hmass s) wE
    have hw₀ : inner ℝ (j.embedding (v s 0)) (j.embedding w) = inner ℝ v₀ (j.embedding w) := by
      rw [hv₀ s]
      exact initialVelocity_pairing j u₀ v₀ s wE
    have hleft : (fun t => inner ℝ (y s t) (j.embedding w)) =ᵐ[timeMeasureValue T]
        (fun t => inner ℝ (W s t) (j.embedding w)) := by
      exact (hW s).symm.mono fun t ht => congrArg (fun z => inner ℝ z (j.embedding w)) ht
    have hright : (fun t => inner ℝ (f t) (j.embedding w) - a t (x s t) w) =ᵐ[timeMeasureValue T]
        (fun t => inner ℝ (f t) (j.embedding w) - a t (U s t) w) := by
      exact (hU s).symm.mono fun t ht => congrArg (fun z => inner ℝ (f t) (j.embedding w) - a t z w) ht
    constructor
    · exact (hasTimeDerivative_congr T _ _ _ _ hleft hright).mp hd
    · rw [← integral_congr_ae hleft,
        ← integral_congr_ae (hright.mono fun t ht => congrArg (fun z => (T-t) * z) ht)]
      change _ = T * inner ℝ (j.embedding (v s 0)) (j.embedding w) at hm
      rw [hw₀] at hm
      exact hm

end ExpandedFA.Evolution.HyperbolicWeakEnergyExistence.GalerkinNet


namespace ExpandedFA.Evolution.HyperbolicWeakEnergyExistence
open HilbertTripleSpec HyperbolicFormSpec HyperbolicWeakEnergySpec
variable {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Construct the source weak-energy solution from genuine finite-state L² approximations.
The hypotheses are the linear identities and uniform estimates established by finite systems. -/
theorem solution_of_galerkin_L2_family {ι : Type*} (F : Filter ι) [NeBot F]
    (j : HilbertTriple V H) (T : ℝ) (hT : 0 < T)
    (a : ℝ → Form V) (α C : ℝ) (ha : FormHypotheses j T a α C)
    (u₀ : V) (v₀ : H) (f : timeLpValue H 2 T) (c R : ℝ) (hR : 0 ≤ R)
    (U : ι → Lp V 2 (timeMeasureValue T)) (W : ι → Lp H 2 (timeMeasureValue T))
    (hU : ∀ᶠ i in F, ∀ᵐ t ∂timeMeasureValue T, ‖U i t‖ ≤ R)
    (hW : ∀ᶠ i in F, ∀ᵐ t ∂timeMeasureValue T, ‖W i t‖ ≤ R)
    (hE : ∀ᶠ i in F, ∀ᵐ t ∂timeMeasureValue T,
      shiftedEnergy j a C t (U i t) (W i t) ≤ Real.exp (c*t) *
        (shiftedEnergy j a C 0 u₀ v₀ + ∫ r in 0..t, ‖f r‖ ^ 2))
    (hd : ∀ᶠ i in F, derivativeValue T (fun t => j.embedding (U i t)) (W i))
    (hMom : ∀ᶠ i in F, (∫ t, j.embedding (U i t) ∂timeMeasureValue T) -
      (∫ t, (T-t) • W i t ∂timeMeasureValue T) = T • j.embedding u₀)
    (hTests : ∀ w : V, ∀ᶠ i in F,
      derivativeValue T (fun t => inner ℝ (W i t) (j.embedding w))
        (fun t => inner ℝ (f t) (j.embedding w) - a t (U i t) w) ∧
      ((∫ t, inner ℝ (W i t) (j.embedding w) ∂timeMeasureValue T) -
        (∫ t, (T-t) * (inner ℝ (f t) (j.embedding w) - a t (U i t) w)
          ∂timeMeasureValue T) = T * inner ℝ v₀ (j.embedding w))) :
    ∃ z : WeakEnergySolution j T a u₀ v₀ f,
      (∀ t ∈ Set.Icc 0 T, ‖z.displacement t‖ ≤ R ∧ ‖z.velocity t‖ ≤ R) ∧
      (∀ t ∈ Set.Icc 0 T,
        shiftedEnergy j a C t (z.displacement t) (z.velocity t) ≤ Real.exp (c*t) *
          (shiftedEnergy j a C 0 u₀ v₀ + ∫ r in 0..t, ‖f r‖ ^ 2)) ∧
      Tendsto z.displacement (𝓝[Set.Icc 0 T] 0) (𝓝 u₀) ∧
      Tendsto z.velocity (𝓝[Set.Icc 0 T] 0) (𝓝 v₀) := by
  letI : IsFiniteMeasure (timeMeasureValue T) :=
    inferInstanceAs (IsFiniteMeasure (volume.restrict (Set.Ioo 0 T)))
  obtain ⟨x,y,L,hLF,hxb,hyb,hxm,hym,hx,hy⟩ :=
    WeakCompactness.exists_weak_pair_limit_of_ae_bound F T U W R R hR hR hU hW
  have hdx : derivativeValue T (fun t => j.embedding (x t)) y :=
    mapped_derivativeValue_of_weak_L2_limits (L : Filter ι) T j.embedding U W x y hx hy
      (hd.filter_mono hLF)
  have hmx : (∫ t, j.embedding (x t) ∂timeMeasureValue T) -
      (∫ t, (T-t) • y t ∂timeMeasureValue T) = T • j.embedding u₀ :=
    mapped_endpoint_moment_of_weak_L2_limits (L : Filter ι) T j.embedding U W x y hx hy
      (fun _ => j.embedding u₀) (j.embedding u₀) tendsto_const_nhds (hMom.filter_mono hLF)
  have htest : WaveTestEquation j T a x y f :=
    GalerkinNet.wave_tests_of_weak_L2_limits (L : Filter ι) j T a
      (formMultiplier T a ha.scalarC1) (coeFn_formMultiplier T a ha.scalarC1)
      U W x y f hx hy (fun w => ((hTests w).mono fun _ hi => hi.1).filter_mono hLF)
  let g : ℝ → StrongDual ℝ V := fun t => pivotValue j (f t) - a t (x t)
  have hgm : MemLp g 2 (timeMeasureValue T) := acceleration_memLp j T a ha.scalarC1 x f hxm
  have hdy : derivativeValue T (fun t => pivotValue j (y t)) g :=
    velocity_derivative_of_wave_tests j T a ha.scalarC1 x y f hxm hym htest
  have hmy : (∫ t, pivotValue j (y t) ∂timeMeasureValue T) -
      (∫ t, (T-t) • g t ∂timeMeasureValue T) = T • pivotValue j v₀ := by
    apply GalerkinNet.velocity_moment_of_weak_L2_limits
      (L : Filter ι) j T a ha.scalarC1 U W x y f v₀ hx hy
    intro w
    exact ((hTests w).mono fun _ hi => hi.2).filter_mono hLF
  have hax : (∫ t, (j.embedding (x t) - ∫ r in 0..t, y r) ∂timeMeasureValue T) =
      T • j.embedding u₀ := integral_anchor_of_moment T hT.le _ _ _
        (j.embedding.integrable_comp ((Lp.memLp x).integrable (by norm_num)))
        ((Lp.memLp y).integrable (by norm_num)) hmx
  have hay : (∫ t, (pivotValue j (y t) - ∫ r in 0..t, g r) ∂timeMeasureValue T) =
      T • pivotValue j v₀ := integral_anchor_of_moment T hT.le _ _ _
        ((pivotValue j).integrable_comp ((Lp.memLp y).integrable (by norm_num)))
        (hgm.integrable (by norm_num)) hmy
  have hGc : ContinuousOn (fun t => Real.exp (c*t) *
      (shiftedEnergy j a C 0 u₀ v₀ + ∫ r in 0..t, ‖f r‖ ^ 2)) (Set.Icc 0 T) :=
    ((continuous_const.mul continuous_id).rexp.continuousOn).mul
      (continuousOn_const.add (forcing_integral_continuousOn T hT.le f))
  have hGi : Integrable (fun t => Real.exp (c*t) *
      (shiftedEnergy j a C 0 u₀ v₀ + ∫ r in 0..t, ‖f r‖ ^ 2)) (timeMeasureValue T) :=
    (continuousOn_time_memLp hGc : MemLp _ 1 _).integrable le_rfl
  have henergy := ae_shiftedEnergy_bound_of_weak_pair_limit (L : Filter ι)
    j T a α C ha U W x y hx hy _ hGi (hE.filter_mono hLF)
  exact solution_of_weak_limit j T hT a α C ha u₀ v₀ f x y g R R c hR hR hxm hym hgm
    hxb hyb hdx hdy (Eventually.of_forall fun t => sub_add_cancel _ _) hax hay henergy

end ExpandedFA.Evolution.HyperbolicWeakEnergyExistence


namespace ExpandedFA.Evolution.HyperbolicWeakEnergyExistence
open HilbertTripleSpec HyperbolicFormSpec HyperbolicWeakEnergySpec

/-- Galerkin weak-energy existence in the original real Hilbert triple, including
zero duration, with uniform constants and strong traces at the starting time. -/
theorem weak_existence {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] :
    WeakExistence (V := V) (H := H) := by
  intro j T hT a α C ha
  by_cases hzero : T = 0
  · subst T
    exact weak_existence_zero j a C
  have hpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hzero)
  obtain ⟨c,hc,hfamily⟩ := GalerkinNet.exists_uniform_galerkin_L2_family j T hT a α C ha
  obtain ⟨K,hK,hstate⟩ := state_bound_of_gronwall j T hT a α C ha c hc
  refine ⟨c,K,hc,hK,?_⟩
  intro u₀ v₀ f
  obtain ⟨R,U,W,hR,hU,hW,hE,hd,hMom,hTests⟩ := hfamily u₀ v₀ f
  obtain ⟨z,_,henergy,htraceU,htraceV⟩ :=
    solution_of_galerkin_L2_family (atTop : Filter (Finset V)) j T hpos a α C ha
      u₀ v₀ f c R hR U W (Eventually.of_forall hU) (Eventually.of_forall hW)
      (Eventually.of_forall hE) (Eventually.of_forall hd) (Eventually.of_forall hMom) hTests
  exact ⟨z,henergy,hstate u₀ v₀ f z.displacement z.velocity henergy,htraceU,htraceV⟩

end ExpandedFA.Evolution.HyperbolicWeakEnergyExistence

/- Mathlib proof attribution
Adapted portion near line 1279:
The induction and factorial estimate for the iterated approximation in the
hyperbolic energy construction.

Upstream: Mathlib/Analysis/ODE/PicardLindelof.lean (around line 329)
Revision: 56a005855ea17e0b0958f73ec801ae140b0a1679
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Winston Yin

See THIRD_PARTY_NOTICES.md for source links and the Apache 2.0 license.
-/
