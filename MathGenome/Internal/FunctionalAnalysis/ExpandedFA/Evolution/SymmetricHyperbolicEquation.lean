import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Evolution.SymmetricHyperbolicEquation
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Evolution.HyperbolicWeakEnergyUniqueness
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
universe u v

namespace ExpandedFA.Evolution.SymmetricHyperbolicEquation
open HilbertTripleSpec HyperbolicFormSpec HyperbolicWeakEnergySpec
open SymmetricHyperbolicSpec
open HyperbolicWeakEnergyExistence HyperbolicWeakEnergyUniqueness

variable {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Uniform quantitative strong well-posedness from weak existence and
weak-class uniqueness/restarting. All derivative fields are the actual
upstream distributional graphs. -/
theorem well_posedness : WellPosedness (V := V) (H := H) := by
  intro j T hT a α C ha
  obtain ⟨c, K, hc, hK, hz⟩ := weak_existence j T hT a α C ha
  refine ⟨K, hK, ?_⟩
  intro u₀ v₀ f
  obtain ⟨z, _, hb, _, _⟩ := hz u₀ v₀ f
  exact ⟨z, strong_state_continuity j T hT a α C ha u₀ v₀ f z,
    hb, fun w => weak_uniqueness j T hT a α C ha u₀ v₀ f z w⟩

/-- Quantitative well-posedness and the independent energy identity assemble
the complete source theorem. -/
theorem assemble (henergy : EnergyIdentity (V := V) (H := H)) :
    SymmetricHyperbolicSpec.SymmetricHyperbolicEquation (V := V) (H := H) := by
  intro j T hT a α C ha
  obtain ⟨K, hK, hz⟩ := well_posedness j T hT a α C ha
  refine ⟨K, hK, ?_⟩
  intro u₀ v₀ f
  obtain ⟨z, hc, hb, hu⟩ := hz u₀ v₀ f
  exact ⟨z, hc, henergy j T hT a α C ha u₀ v₀ f z, hb, hu⟩

theorem zero_time_energy_identity (j : HilbertTriple V H) (a : ℝ → Form V)
    (u₀ : V) (v₀ : H) (f : timeLpValue H 2 0)
    (z : WeakEnergySolution j 0 a u₀ v₀ f) : HasEnergyIdentity z := by
  intro s hs t ht
  have hs0 : s = 0 := le_antisymm hs.2 hs.1
  have ht0 : t = 0 := le_antisymm ht.2 ht.1
  subst s
  subst t
  simp

/-- Scalar time differentiation retains bilinearity in the two fixed vectors.
No assertion of operator-norm differentiability of a is made. -/
def derivativeLinearForm (T : ℝ) (a : ℝ → Form V) (ha : ScalarC1 T a)
    (t : ℝ) (ht : t ∈ Set.Icc 0 T) : V →ₗ[ℝ] V →ₗ[ℝ] ℝ := by
  have hd (x y : V) := ((ha x y).differentiableOn (by simp) t ht)
  refine LinearMap.mk₂ ℝ
    (fun x y => derivWithin (fun r => a r x y) (Set.Icc 0 T) t) ?_ ?_ ?_ ?_
  · intro x y z
    simp only [map_add, add_apply]
    exact derivWithin_add (hd x z) (hd y z)
  · intro c x y
    simp only [map_smul, smul_apply, smul_eq_mul]
    exact derivWithin_const_mul c (hd x y)
  · intro x y z
    simp only [map_add]
    exact derivWithin_add (hd x y) (hd x z)
  · intro c x y
    simp only [map_smul, smul_eq_mul]
    exact derivWithin_const_mul c (hd x y)

/-- A bounded form representing the scalar time derivative, at each time.
This definition is only used on the closed time interval. -/
def derivativeForm (T : ℝ) (a : ℝ → Form V) (ha : ScalarC1 T a)
    (t : ℝ) : Form V := by
  classical
  by_cases ht : t ∈ Set.Icc 0 T
  · let M := Classical.choose (HyperbolicFormBoundsAndCarrier.uniform_bounds T a ha)
    have hM := (Classical.choose_spec
      (HyperbolicFormBoundsAndCarrier.uniform_bounds T a ha)).2.1
    exact (derivativeLinearForm T a ha t ht).mkContinuous₂ M (fun x y => by
      change ‖derivWithin (fun r => a r x y) (Set.Icc 0 T) t‖ ≤ M * ‖x‖ * ‖y‖
      rw [Real.norm_eq_abs]
      exact (le_add_of_nonneg_left (abs_nonneg _)).trans (hM t ht x y))
  · exact 0

@[simp] theorem derivativeForm_apply (T : ℝ) (a : ℝ → Form V) (ha : ScalarC1 T a)
    (t : ℝ) (ht : t ∈ Set.Icc 0 T) (x y : V) :
    derivativeForm T a ha t x y = derivWithin (fun r => a r x y) (Set.Icc 0 T) t := by
  simp only [derivativeForm, dite_eq_left ht, LinearMap.mkContinuous₂_apply,
    derivativeLinearForm, LinearMap.mk₂_apply]

/-- Uniform boundedness of the derivative forms. -/
theorem derivativeForm_bounded (T : ℝ) (a : ℝ → Form V) (ha : ScalarC1 T a) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Set.Icc 0 T, ‖derivativeForm T a ha t‖ ≤ M := by
  obtain ⟨M, hM, hb, _⟩ := HyperbolicFormBoundsAndCarrier.uniform_bounds T a ha
  refine ⟨M, hM, ?_⟩
  intro t ht
  apply ContinuousLinearMap.opNorm_le_bound₂ _ hM
  intro x y
  rw [derivativeForm_apply T a ha t ht, Real.norm_eq_abs]
  exact (le_add_of_nonneg_left (abs_nonneg _)).trans (hb t ht x y)

/-- Weak continuity of a uniformly bounded bilinear family suffices for
continuity of its value on two norm-continuous curves. -/
theorem continuousOn_form_apply (S : Set ℝ) (b : ℝ → Form V)
    (hscalar : ∀ x y, ContinuousOn (fun r => b r x y) S)
    (M : ℝ) (hbound : ∀ r ∈ S, ‖b r‖ ≤ M)
    (x y : ℝ → V) (hx : ContinuousOn x S) (hy : ContinuousOn y S) :
    ContinuousOn (fun r => b r (x r) (y r)) S := by
  intro t ht
  have hx₀ := hx t ht
  have hy₀ := hy t ht
  have hxlim : Tendsto (fun r => ‖x r - x t‖) (𝓝[S] t) (𝓝 0) := by
    simpa using (hx₀.sub_const (x t)).norm
  have hylim : Tendsto (fun r => ‖y r - y t‖) (𝓝[S] t) (𝓝 0) := by
    simpa using (hy₀.sub_const (y t)).norm
  have h₁ : Tendsto (fun r => b r (x r - x t) (y r)) (𝓝[S] t) (𝓝 0) := by
    apply squeeze_zero_norm' ?_ (by simpa using (hxlim.const_mul M).mul hy₀.norm)
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (b r).le_of_opNorm₂_le_of_le (hbound r hr) le_rfl le_rfl
  have h₂ : Tendsto (fun r => b r (x t) (y r - y t)) (𝓝[S] t) (𝓝 0) := by
    apply squeeze_zero_norm' ?_ (by simpa using hylim.const_mul (M * ‖x t‖))
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (b r).le_of_opNorm₂_le_of_le (hbound r hr) le_rfl le_rfl
  have h₃ := hscalar (x t) (y t) t ht
  have h := (h₁.add h₂).add h₃
  simp only [zero_add] at h
  change Tendsto _ _ _
  convert h using 1
  ext r
  simp only [map_sub, sub_apply]
  ring

/-- The form-power integrand is continuous despite assuming only scalar C¹
regularity, rather than C¹ regularity in operator norm. -/
theorem formPower_continuousOn (T : ℝ) (hT : 0 < T) (a : ℝ → Form V)
    (ha : ScalarC1 T a) (x : ℝ → V) (hx : ContinuousOn x (Set.Icc 0 T)) :
    ContinuousOn (formPower T a x) (Set.Icc 0 T) := by
  obtain ⟨M, _, hb⟩ := derivativeForm_bounded T a ha
  have hc (u v : V) : ContinuousOn (fun r => derivativeForm T a ha r u v)
      (Set.Icc 0 T) := by
    apply ((ha u v).continuousOn_derivWithin (uniqueDiffOn_Icc hT) (by simp)).congr
    intro t ht
    exact derivativeForm_apply T a ha t ht u v
  exact (continuousOn_form_apply (Set.Icc 0 T) _ hc M hb x x hx hx).congr
    (fun t ht => (derivativeForm_apply T a ha t ht (x t) (x t)).symm)

theorem energy_continuousOn (T : ℝ) (a : ℝ → Form V)
    (ha : ScalarC1 T a) (x : ℝ → V) (y : ℝ → H)
    (hx : ContinuousOn x (Set.Icc 0 T)) (hy : ContinuousOn y (Set.Icc 0 T)) :
    ContinuousOn (energy a x y) (Set.Icc 0 T) := by
  obtain ⟨M, _, hb⟩ := HyperbolicFormBoundsAndCarrier.form_values_bounded T a ha
  have hquad := continuousOn_form_apply (Set.Icc 0 T) a
    (fun u v => (ha u v).continuousOn) M hb x x hx hx
  exact (hy.norm.pow 2).add hquad

/-- L² forcing paired with a continuous velocity has an honest L¹ integral. -/
theorem forceWork_integrable (T : ℝ) (f : timeLpValue H 2 T) (y : ℝ → H)
    (hy : ContinuousOn y (Set.Icc 0 T)) :
    Integrable (fun r => inner ℝ (f r) (y r)) (timeMeasureValue T) := by
  have hyMem : MemLp y 2 (timeMeasureValue T) := continuousOn_time_memLp hy
  exact memLp_one_iff_integrable.mp
    ((innerSL ℝ).memLp_of_bilin 1 (Lp.memLp f) hyMem)

/-- All terms needed for endpoint integration are integrable separately. -/
theorem energy_terms_integrable (j : HilbertTriple V H) (T : ℝ) (hT : 0 < T)
    (a : ℝ → Form V) (α C : ℝ) (ha : FormHypotheses j T a α C)
    (u₀ : V) (v₀ : H) (f : timeLpValue H 2 T)
    (z : WeakEnergySolution j T a u₀ v₀ f) :
    Integrable (energy a z.displacement z.velocity) (timeMeasureValue T) ∧
    Integrable (fun r => inner ℝ (f r) (z.velocity r)) (timeMeasureValue T) ∧
    Integrable (formPower T a z.displacement) (timeMeasureValue T) := by
  let : IsFiniteMeasure (timeMeasureValue T) :=
    inferInstanceAs (IsFiniteMeasure (volume.restrict (Set.Ioo 0 T)))
  obtain ⟨hx, hy⟩ := strong_state_continuity j T hT.le a α C ha u₀ v₀ f z
  refine ⟨?_, forceWork_integrable T f z.velocity hy, ?_⟩
  · exact (continuousOn_time_memLp
      (energy_continuousOn T a ha.scalarC1 _ _ hx hy) : MemLp _ 1 _).integrable le_rfl
  · exact (continuousOn_time_memLp
      (formPower_continuousOn T hT a ha.scalarC1 _ hx) : MemLp _ 1 _).integrable le_rfl

/-- The positive-time endpoint identity reduces to the scalar distributional
chain rule. Continuity identifies the primitive with the given energy at
all times, so no exceptional endpoints are discarded. -/
theorem energy_identity_of_derivative
    (hderivative : EnergyDerivative (V := V) (H := H)) :
    EnergyIdentity (V := V) (H := H) := by
  intro j T hT a α C ha u₀ v₀ f z
  by_cases hzero : T = 0
  · subst T
    exact zero_time_energy_identity j a u₀ v₀ f z
  have hpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hzero)
  obtain ⟨hx, hy⟩ := strong_state_continuity j T hT a α C ha u₀ v₀ f z
  obtain ⟨he, hf, hp⟩ := energy_terms_integrable j T hpos a α C ha u₀ v₀ f z
  have hR := (hf.const_mul 2).add hp
  have hcont := energy_continuousOn T a ha.scalarC1 z.displacement z.velocity hx hy
  have hweak : WeaklyContinuousOn (energy a z.displacement z.velocity) (Set.Icc 0 T) :=
    fun L => L.continuous.comp_continuousOn hcont
  have hprimitive := (primitive_of_weaklyContinuousOn T hpos
    (energy a z.displacement z.velocity) _ he hR
    (hderivative j T hpos a α C ha u₀ v₀ f z) hweak).2
  intro s hs t ht
  have hfi := intervalIntegrable_of_timeIntegrable T hf ⟨s, hs⟩ ⟨t, ht⟩
  have hpi := intervalIntegrable_of_timeIntegrable T hp ⟨s, hs⟩ ⟨t, ht⟩
  refine ⟨hfi, hpi, ?_⟩
  rw [hprimitive ⟨s, hs⟩ ⟨t, ht⟩]
  change (∫ r in s..t, 2 * inner ℝ (f r) (z.velocity r) +
    formPower T a z.displacement r) = _
  rw [intervalIntegral.integral_add (hfi.const_mul 2) hpi,
    intervalIntegral.integral_const_mul]

/-- Assembly using the interior distributional chain rule. -/
theorem assemble_of_derivative (hderivative : EnergyDerivative (V := V) (H := H)) :
    SymmetricHyperbolicSpec.SymmetricHyperbolicEquation (V := V) (H := H) :=
  assemble (energy_identity_of_derivative hderivative)

/-- Forward Steklov average, used only with a positive averaging length. -/
def timeAverage {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : ℝ → E) (h t : ℝ) : E := h⁻¹ • ∫ r in t..t+h, x r

/-- The discrepancy between applying the current form and averaging its
trajectory. This is a V′-valued error, not an additional equation hypothesis. -/
def formCommutator (a : ℝ → Form V) (x : ℝ → V) (h t : ℝ) : StrongDual ℝ V :=
  a t (timeAverage x h t) - timeAverage (fun r => a r (x r)) h t

/-- An elementary commutator bound for Steklov averages. No derivative of
an operator-valued trajectory, and no separability assumption, is needed. -/
theorem formCommutator_bound (a : ℝ → Form V) (x : ℝ → V) (h t M R : ℝ)
    (hh : 0 < h) (hM : 0 ≤ M) (_hR : 0 ≤ R)
    (hx : ContinuousOn x (Set.Icc t (t+h)))
    (ha : ContinuousOn a (Set.Icc t (t+h)))
    (hbound : ∀ r ∈ Set.Icc t (t+h), ‖x r‖ ≤ R)
    (hsec : ∀ r ∈ Set.Icc t (t+h), ‖a t - a r‖ ≤ M * |r-t|) :
    ‖formCommutator a x h t‖ ≤ M * h * R := by
  have hth : t ≤ t+h := by linarith
  have hxi : IntervalIntegrable x volume t (t+h) :=
    (hx.mono (by rw [Set.uIcc_of_le hth])).intervalIntegrable
  have hai : IntervalIntegrable (fun r => a r (x r)) volume t (t+h) :=
    ((ha.clm_apply hx).mono (by rw [Set.uIcc_of_le hth])).intervalIntegrable
  have hfixed : IntervalIntegrable (fun r => a t (x r)) volume t (t+h) :=
    ((a t).continuous.comp_continuousOn
      (hx.mono (by rw [Set.uIcc_of_le hth]))).intervalIntegrable
  have heq : formCommutator a x h t =
      h⁻¹ • ∫ r in t..t+h, (a t - a r) (x r) := by
    unfold formCommutator timeAverage
    calc
      _ = h⁻¹ • ((a t) (∫ r in t..t+h, x r) - ∫ r in t..t+h, a r (x r)) := by
        simp only [map_smul, smul_sub]
      _ = _ := by
        congr 1
        rw [← (a t).intervalIntegral_comp_comm hxi,
          ← intervalIntegral.integral_sub hfixed hai]
        rfl
  have hi : ‖∫ r in t..t+h, (a t - a r) (x r)‖ ≤ (M * h * R) * h := by
    convert intervalIntegral.norm_integral_le_of_norm_le_const (C := M * h * R) ?_ using 1
    · rw [add_sub_cancel_left, abs_of_pos hh]
    · intro r hr
      have hr' : r ∈ Set.Icc t (t+h) := by
        rw [Set.uIoc_of_le hth] at hr
        exact Set.Ioc_subset_Icc_self hr
      have hrt : |r-t| ≤ h := by
        rw [abs_of_nonneg (sub_nonneg.mpr hr'.1)]
        linarith [hr'.2]
      calc
        ‖(a t - a r) (x r)‖ ≤ ‖a t - a r‖ * ‖x r‖ :=
          (a t-a r).le_opNorm (x r)
        _ ≤ (M * h) * R := by
          gcongr
          exact (hsec r hr').trans (mul_le_mul_of_nonneg_left hrt hM)
          exact hbound r hr'
        _ = M * h * R := rfl
  rw [heq, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hh]
  calc
    h⁻¹ * ‖∫ r in t..t+h, (a t-a r) (x r)‖ ≤ h⁻¹ * ((M*h*R)*h) := by
      gcongr
    _ = M*h*R := by field_simp

/-- Cancellation of the averaging length in the commutator work. The right
side tends uniformly to zero for a continuous state on a compact interval. -/
theorem formCommutator_work_bound (a : ℝ → Form V) (x : ℝ → V) (h t M R : ℝ)
    (hh : 0 < h) (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hx : ContinuousOn x (Set.Icc t (t+h)))
    (ha : ContinuousOn a (Set.Icc t (t+h)))
    (hbound : ∀ r ∈ Set.Icc t (t+h), ‖x r‖ ≤ R)
    (hsec : ∀ r ∈ Set.Icc t (t+h), ‖a t - a r‖ ≤ M * |r-t|) :
    |formCommutator a x h t (h⁻¹ • (x (t+h)-x t))| ≤
      M * R * ‖x (t+h)-x t‖ := by
  calc
    _ ≤ ‖formCommutator a x h t‖ * ‖h⁻¹ • (x (t+h)-x t)‖ := by
      simpa only [Real.norm_eq_abs] using
        (formCommutator a x h t).le_opNorm (h⁻¹ • (x (t+h)-x t))
    _ ≤ (M*h*R) * ‖h⁻¹ • (x (t+h)-x t)‖ := by
      gcongr
      exact formCommutator_bound a x h t M R hh hM hR hx ha hbound hsec
    _ = M*R*‖x (t+h)-x t‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hh]
      field_simp

/-- Uniform disappearance of the commutator work on every admissible
forward averaging interval. This is the small-error step needed when passing
the regularized energy balance to the continuous energy state. -/
theorem commutator_work_small (T : ℝ) (hT : 0 ≤ T) (a : ℝ → Form V)
    (ha : ScalarC1 T a) (x : ℝ → V) (hx : ContinuousOn x (Set.Icc 0 T)) :
    ∀ ε > 0, ∃ δ > 0, ∀ h : ℝ, 0 < h → h < δ →
      ∀ t ∈ Set.Icc 0 T, t+h ≤ T →
        |formCommutator a x h t (h⁻¹ • (x (t+h)-x t))| < ε := by
  obtain ⟨M, hM, hsec⟩ := HyperbolicFormBoundsAndCarrier.form_secants_bounded T a ha
  obtain ⟨R₀, hR₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hx
  let R := max R₀ 0
  have hR : 0 ≤ R := le_max_right _ _
  have hbound : ∀ r ∈ Set.Icc 0 T, ‖x r‖ ≤ R :=
    fun r hr => (hR₀ r hr).trans (le_max_left _ _)
  have hac : ContinuousOn a (Set.Icc 0 T) := by
    have hac₀ : AbsolutelyContinuousOnInterval a 0 T := scalarC1_form_ac T hT a ha
    have hac₁ : ContinuousOn a (Set.uIcc 0 T) :=
      @AbsolutelyContinuousOnInterval.continuousOn (Form V) inferInstance 0 T a hac₀
    simpa only [Set.uIcc_of_le hT] using hac₁
  have hL : 0 < M*R+1 := by positivity
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := (Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hx)) (ε / (M*R+1))
      (div_pos hε hL)
  refine ⟨δ, hδ, ?_⟩
  intro h hh hhδ t ht htop
  have hsub : Set.Icc t (t+h) ⊆ Set.Icc 0 T := Set.Icc_subset_Icc ht.1 htop
  have hth : t+h ∈ Set.Icc 0 T := ⟨by linarith [ht.1], htop⟩
  have hdist : ‖x (t+h)-x t‖ < ε/(M*R+1) := by
    have hsmall : dist (t+h) t < δ := by
      simpa only [Real.dist_eq, add_sub_cancel_left, abs_of_pos hh] using hhδ
    simpa only [dist_eq_norm] using hd (t+h) hth t ht hsmall
  have hb := formCommutator_work_bound a x h t M R hh hM hR
    (hx.mono hsub) (hac.mono hsub) (fun r hr => hbound r (hsub hr))
    (fun r hr => by
      simpa only [Real.norm_eq_abs, abs_sub_comm] using hsec r (hsub hr) t ht)
  calc
    _ ≤ M*R*‖x (t+h)-x t‖ := hb
    _ ≤ (M*R+1)*‖x (t+h)-x t‖ := by gcongr; linarith
    _ < (M*R+1)*(ε/(M*R+1)) := mul_lt_mul_of_pos_left hdist hL
    _ = ε := mul_div_cancel₀ ε (ne_of_gt hL)


section Averaging
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Continuous curves have continuously differentiable forward averages. -/
theorem timeAverage_contDiff {x : ℝ → E} (hx : Continuous x) (h : ℝ) :
    ContDiff ℝ 1 (timeAverage x h) := by
  have hp := FiniteEnergy.continuous_primitive_c1 hx 0
  have heq : timeAverage x h = fun t => h⁻¹ •
      ((∫ r in 0..t+h, x r) - ∫ r in 0..t, x r) := by
    funext t
    rw [timeAverage, intervalIntegral.integral_interval_sub_left
      (hx.intervalIntegrable _ _) (hx.intervalIntegrable _ _)]
  rw [heq]
  exact contDiff_const.smul ((hp.comp (contDiff_id.add contDiff_const)).sub hp)

/-- Differentiating an average uses only continuity of the original curve. -/
theorem timeAverage_hasDerivAt {x : ℝ → E} (hx : Continuous x) (h t : ℝ) :
    HasDerivAt (timeAverage x h) (h⁻¹ • (x (t+h) - x t)) t := by
  have hp (s : ℝ) := intervalIntegral.integral_hasDerivAt_right
    (hx.intervalIntegrable 0 s) hx.aestronglyMeasurable.stronglyMeasurableAtFilter
    (hx.continuousAt (x := s))
  have hd := HasDerivAt.const_smul h⁻¹
    (((hp (t+h)).scomp t ((hasDerivAt_id t).add_const h)).sub (hp t))
  simpa only [one_smul] using hd.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun r => by
      change h⁻¹ • (∫ s in r..r+h, x s) = h⁻¹ • ((∫ s in 0..r+h, x s) - ∫ s in 0..r, x s)
      rw [ intervalIntegral.integral_interval_sub_left
        (hx.intervalIntegrable _ _) (hx.intervalIntegrable _ _)])

/-- The continuous extension is only used to justify differentiation and AC;
on each admissible averaging interval its integral equals the original one. -/
theorem timeAverage_regular {T B h : ℝ} (hT : 0 ≤ T) (hB : 0 ≤ B)
    (hh : 0 ≤ h) (hBh : B+h ≤ T) {x : ℝ → E}
    (hx : ContinuousOn x (Set.Icc 0 T)) :
    AbsolutelyContinuousOnInterval (timeAverage x h) 0 B ∧
    (∀ᵐ t ∂volume, t ∈ Set.Icc 0 B →
      HasDerivAt (timeAverage x h) (h⁻¹ • (x (t+h)-x t)) t) := by
  let X : ℝ → E := Volterra.extend hT ⟨fun t => x t, hx.domRestrict⟩
  have hX : Continuous X := Volterra.continuous_extend hT _
  have heq (t : ℝ) (ht : t ∈ Set.Icc 0 B) :
      timeAverage X h t = timeAverage x h t := by
    unfold timeAverage
    congr 1
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r ∈ Set.Icc 0 T := by
      rw [Set.uIcc_of_le (by linarith : t ≤ t+h)] at hr
      exact ⟨by linarith [ht.1, hr.1], by linarith [ht.2, hr.2]⟩
    exact Volterra.extend_of_mem hT _ hr'
  constructor
  · exact ((timeAverage_contDiff hX h).contDiffOn.absolutelyContinuousOnInterval).congr
      (fun t ht => heq t (by simpa [Set.uIcc_of_le hB] using ht))
  · have hn₀ : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := by simp [ae_iff, measure_singleton]
    have hnB : ∀ᵐ t : ℝ ∂volume, t ≠ B := by simp [ae_iff, measure_singleton]
    filter_upwards [hn₀, hnB] with t ht0 htB ht
    have hti : t ∈ Set.Ioo 0 B :=
      ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 htB⟩
    have hd := timeAverage_hasDerivAt hX h t
    have htT : t ∈ Set.Icc 0 T := ⟨ht.1, by linarith [ht.2]⟩
    have hthT : t+h ∈ Set.Icc 0 T := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hx₀ : X t = x t := Volterra.extend_of_mem hT _ htT
    have hx₁ : X (t+h) = x (t+h) := Volterra.extend_of_mem hT _ hthT
    rw [hx₀, hx₁] at hd
    apply hd.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hti.1 hti.2] with r hr
    exact (heq r (Set.Ioo_subset_Icc_self hr)).symm

/-- Averages of an integrable function are continuous on admissible intervals. -/
theorem timeAverage_continuousOn {T B h : ℝ} (hB : 0 ≤ B)
    (hh : 0 ≤ h) (hBh : B+h ≤ T) {x : ℝ → E}
    (hx : IntervalIntegrable x volume 0 T) :
    ContinuousOn (timeAverage x h) (Set.Icc 0 B) := by
  have hT : 0 ≤ T := by linarith
  have hp : ContinuousOn (fun t => ∫ r in 0..t, x r) (Set.Icc 0 T) := by
    simpa [Set.uIcc_of_le hT] using
      intervalIntegral.continuousOn_primitive_interval' hx Set.left_mem_uIcc
  have hsub : Set.Icc 0 B ⊆ Set.Icc 0 T := Set.Icc_subset_Icc le_rfl (by linarith)
  have hp' := hp.comp (continuousOn_id.add continuousOn_const)
    (show Set.MapsTo (fun t : ℝ => t+h) (Set.Icc 0 B) (Set.Icc 0 T) from
      fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  apply ((continuousOn_const : ContinuousOn (fun _ : ℝ => h⁻¹) (Set.Icc 0 B)).smul (hp'.sub (hp.mono hsub))).congr
  intro t ht
  have ht₀ : t ∈ Set.uIcc 0 T := by simpa [Set.uIcc_of_le hT] using hsub ht
  have ht₁ : t+h ∈ Set.uIcc 0 T := by
    rw [Set.uIcc_of_le hT]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  exact congrArg (h⁻¹ • ·) (intervalIntegral.integral_interval_sub_left
    (hx.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc ht₁))
    (hx.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc ht₀))).symm

end Averaging

/-- Averaging preserves the actual kinematic identity in the pivot space. -/
theorem averaged_kinematics (j : HilbertTriple V H) (T : ℝ) (hT : 0 < T)
    (a : ℝ → Form V) (u₀ : V) (v₀ : H) (f : timeLpValue H 2 T)
    (z : WeakEnergySolution j T a u₀ v₀ f)
    (h t : ℝ) (ht : t ∈ Set.Icc 0 T) (hth : t+h ∈ Set.Icc 0 T) :
    j.embedding (h⁻¹ • (z.displacement (t+h)-z.displacement t)) =
      timeAverage z.velocity h t := by
  obtain ⟨_, _, hu, _⟩ := primitive_representatives j T hT a u₀ v₀ f z
  simp only [map_smul, map_sub, timeAverage]
  rw [hu ⟨t, ht⟩ ⟨t+h, hth⟩]

/-- The averaged equation holds everywhere, since its acceleration is the
increment of the prescribed primitive of the dual velocity. -/
theorem averaged_equation (j : HilbertTriple V H) (T : ℝ) (hT : 0 < T)
    (a : ℝ → Form V) (α C : ℝ) (ha : FormHypotheses j T a α C)
    (u₀ : V) (v₀ : H) (f : timeLpValue H 2 T)
    (z : WeakEnergySolution j T a u₀ v₀ f)
    (h t : ℝ) (hh : 0 ≤ h) (ht : t ∈ Set.Icc 0 T)
    (hth : t+h ∈ Set.Icc 0 T) :
    pivotValue j (h⁻¹ • (z.velocity (t+h)-z.velocity t)) +
      a t (timeAverage z.displacement h t) =
    pivotValue j (timeAverage (fun r => f r) h t) +
      formCommutator a z.displacement h t := by
  let : IsFiniteMeasure (timeMeasureValue T) :=
    inferInstanceAs (IsFiniteMeasure (volume.restrict (Set.Ioo 0 T)))
  obtain ⟨_, _, _, hv⟩ := primitive_representatives j T hT a u₀ v₀ f z
  obtain ⟨hx, _⟩ := strong_state_continuity j T hT.le a α C ha u₀ v₀ f z
  have hsub : Set.uIcc t (t+h) ⊆ Set.Icc 0 T := Set.uIcc_subset_Icc ht hth
  have hac : ContinuousOn a (Set.Icc 0 T) := by
    simpa [Set.uIcc_of_le hT.le] using
      (@AbsolutelyContinuousOnInterval.continuousOn (Form V) inferInstance 0 T a
        (scalarC1_form_ac T hT.le a ha.scalarC1))
  have hai : IntervalIntegrable (fun r => a r (z.displacement r)) volume t (t+h) :=
    ((hac.clm_apply hx).mono hsub).intervalIntegrable
  have hfi : IntervalIntegrable (fun r => f r) volume t (t+h) :=
    intervalIntegrable_of_timeIntegrable T ((Lp.memLp f).integrable (by norm_num))
      ⟨t, ht⟩ ⟨t+h, hth⟩
  have hgi : IntervalIntegrable z.acceleration volume t (t+h) :=
    intervalIntegrable_of_timeIntegrable T (z.acceleration_mem.integrable (by norm_num))
      ⟨t, ht⟩ ⟨t+h, hth⟩
  have hei : (∫ r in t..t+h, z.acceleration r + a r (z.displacement r)) =
      ∫ r in t..t+h, pivotValue j (f r) := by
    apply intervalIntegral.integral_congr_ae_restrict
    have heq : ∀ᵐ r ∂volume.restrict (Set.Icc 0 T),
        z.acceleration r + a r (z.displacement r) = pivotValue j (f r) := by
      rw [← restrict_Ioo_eq_restrict_Icc]
      exact z.equation
    exact ae_restrict_of_ae_restrict_of_subset (Set.Subset.trans
      Set.uIoc_subset_uIcc hsub) heq
  rw [intervalIntegral.integral_add hgi hai,
    (pivotValue j).intervalIntegral_comp_comm hfi,
    ← hv ⟨t, ht⟩ ⟨t+h, hth⟩] at hei
  have heis := congrArg (h⁻¹ • ·) hei
  simp only [smul_add, ← map_smul, ← map_sub] at heis
  simp only [formCommutator, timeAverage, map_smul, map_sub] at heis ⊢
  rw [← heis]
  abel


/-- Restriction of the scalar derivative preserves its value even at the
one-sided endpoints of a nondegenerate subinterval. -/
theorem formPower_restrict (T B : ℝ) (hB : 0 < B) (hBT : B ≤ T)
    (a : ℝ → Form V) (ha : ScalarC1 T a) (x : ℝ → V)
    (t : ℝ) (ht : t ∈ Set.Icc 0 B) :
    formPower B a x t = formPower T a x t := by
  apply derivWithin_subset (Set.Icc_subset_Icc le_rfl hBT)
    (uniqueDiffOn_Icc hB t ht)
  exact (ha (x t) (x t)).differentiableOn (by simp) t
    ⟨ht.1, ht.2.trans hBT⟩

/-- Exact energy balance for a regularized state with genuine Banach-valued
product rules. The error is explicitly retained on the right. -/
theorem regularized_balance_of_graphs (j : HilbertTriple V H)
    (T B : ℝ) (hB : 0 < B) (hBT : B ≤ T)
    (a : ℝ → Form V) (ha : ScalarC1 T a)
    (hsym : ∀ t ∈ Set.Icc 0 T, ∀ x y, a t x y = a t y x)
    (x q : ℝ → V) (y d F : ℝ → H) (c : ℝ → StrongDual ℝ V)
    (hx : AbsolutelyContinuousOnInterval x 0 B)
    (hy : AbsolutelyContinuousOnInterval y 0 B)
    (hdx : ∀ᵐ t ∂volume, t ∈ Set.Icc 0 B → HasDerivAt x (q t) t)
    (hdy : ∀ᵐ t ∂volume, t ∈ Set.Icc 0 B → HasDerivAt y (d t) t)
    (hkin : ∀ t ∈ Set.Icc 0 B, j.embedding (q t) = y t)
    (heq : ∀ t ∈ Set.Icc 0 B,
      pivotValue j (d t) + a t (x t) = pivotValue j (F t) + c t)
    (hFi : IntervalIntegrable (fun t => inner ℝ (F t) (y t)) volume 0 B)
    (hci : IntervalIntegrable (fun t => c t (q t)) volume 0 B) :
    energy a x y B - energy a x y 0 =
      2 * (∫ r in 0..B, inner ℝ (F r) (y r)) +
      (∫ r in 0..B, formPower T a x r) + 2 * ∫ r in 0..B, c r (q r) := by
  have hsub : Set.Icc 0 B ⊆ Set.Icc 0 T := Set.Icc_subset_Icc le_rfl hBT
  have haB : ScalarC1 B a := fun u v => (ha u v).mono hsub
  have hsB := fun t ht => hsym t (hsub ht)
  have hk := bilinear_integral_derivative (innerSL ℝ : H →L[ℝ] H →L[ℝ] ℝ)
    hB.le hy hy hdy hdy
  change IntervalIntegrable (fun r => inner ℝ (y r) (d r) + inner ℝ (d r) (y r)) volume 0 B ∧
    (∫ r in 0..B, inner ℝ (y r) (d r) + inner ℝ (d r) (y r)) =
      inner ℝ (y B) (y B) - inner ℝ (y 0) (y 0) at hk
  have hp := varying_form_integral_derivative B hB.le a haB hsB hx hdx
    (show (0 : ℝ) ∈ Set.Icc 0 B from ⟨le_rfl, hB.le⟩)
    (show B ∈ Set.Icc 0 B from ⟨hB.le, le_rfl⟩)
  change IntervalIntegrable (fun r => formPower B a x r + 2 * a r (q r) (x r)) volume 0 B ∧
    (∫ r in 0..B, formPower B a x r + 2 * a r (q r) (x r)) =
      a B (x B) (x B) - a 0 (x 0) (x 0) at hp
  have hxc : ContinuousOn x (Set.Icc 0 B) := by
    simpa [Set.uIcc_of_le hB.le] using hx.continuousOn
  have hpi : IntervalIntegrable (formPower T a x) volume 0 B := by
    have hc := formPower_continuousOn B hB a haB x hxc
    exact ((hc.congr (fun t ht => (formPower_restrict T B hB hBT a ha x t ht).symm)).mono
      (by rw [Set.uIcc_of_le hB.le])).intervalIntegrable
  calc
    _ = (∫ r in 0..B, inner ℝ (y r) (d r) + inner ℝ (d r) (y r)) +
        ∫ r in 0..B, formPower B a x r + 2 * a r (q r) (x r) := by
      rw [hk.2, hp.2]
      simp only [energy, real_inner_self_eq_norm_sq]
      ring
    _ = ∫ r in 0..B, 2 * inner ℝ (F r) (y r) +
        formPower T a x r + 2 * c r (q r) := by
      rw [← intervalIntegral.integral_add hk.1 hp.1]
      apply intervalIntegral.integral_congr
      intro r hr
      rw [Set.uIcc_of_le hB.le] at hr
      have he := congrArg (fun L : StrongDual ℝ V => L (q r)) (heq r hr)
      simp only [add_apply] at he
      rw [show pivotValue j (d r) (q r) = inner ℝ (d r) (j.embedding (q r)) from
        pivotInjection_apply j (d r) (q r),
        show pivotValue j (F r) (q r) = inner ℝ (F r) (j.embedding (q r)) from
        pivotInjection_apply j (F r) (q r)] at he
      change inner ℝ (d r) (j.embedding (q r)) + a r (x r) (q r) =
        inner ℝ (F r) (j.embedding (q r)) + c r (q r) at he
      rw [hkin r hr] at he
      dsimp only
      rw [formPower_restrict T B hB hBT a ha x r hr,
        hsym r (hsub hr) (q r) (x r), real_inner_comm (y r) (d r)]
      linarith [real_inner_comm (d r) (y r)]
    _ = _ := by
      rw [intervalIntegral.integral_add ((hFi.const_mul 2).add hpi) (hci.const_mul 2),
        intervalIntegral.integral_add (hFi.const_mul 2) hpi,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

end ExpandedFA.Evolution.SymmetricHyperbolicEquation

namespace ExpandedFA.Evolution.SymmetricHyperbolicEquation
open HilbertTripleSpec HyperbolicFormSpec HyperbolicWeakEnergySpec
open SymmetricHyperbolicSpec
open HyperbolicWeakEnergyExistence HyperbolicWeakEnergyUniqueness

variable {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The exact Steklov energy identity, with its commutator work retained. -/
theorem regularized_energy_balance (j : HilbertTriple V H)
    (T B h : ℝ) (hB : 0 < B) (hh : 0 < h) (hBh : B+h ≤ T)
    (a : ℝ → Form V) (α C : ℝ) (ha : FormHypotheses j T a α C)
    (u₀ : V) (v₀ : H) (f : timeLpValue H 2 T)
    (z : WeakEnergySolution j T a u₀ v₀ f) :
    energy a (timeAverage z.displacement h) (timeAverage z.velocity h) B -
      energy a (timeAverage z.displacement h) (timeAverage z.velocity h) 0 =
      2 * (∫ r in 0..B, inner ℝ (timeAverage (fun r => f r) h r)
        (timeAverage z.velocity h r)) +
      (∫ r in 0..B, formPower T a (timeAverage z.displacement h) r) +
      2 * ∫ r in 0..B, formCommutator a z.displacement h r
        (h⁻¹ • (z.displacement (r+h)-z.displacement r)) := by
  have hT : 0 < T := by linarith
  have hBT : B ≤ T := by linarith
  let : IsFiniteMeasure (timeMeasureValue T) :=
    inferInstanceAs (IsFiniteMeasure (volume.restrict (Set.Ioo 0 T)))
  obtain ⟨huc,hvc⟩ := strong_state_continuity j T hT.le a α C ha u₀ v₀ f z
  obtain ⟨hxa,hdx⟩ := timeAverage_regular hT.le hB.le hh.le hBh huc
  obtain ⟨hya,hdy⟩ := timeAverage_regular hT.le hB.le hh.le hBh hvc
  have hsub : Set.Icc 0 B ⊆ Set.Icc 0 T := Set.Icc_subset_Icc le_rfl hBT
  have hth (t : ℝ) (ht : t ∈ Set.Icc 0 B) : t+h ∈ Set.Icc 0 T :=
    ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have hxc : ContinuousOn (timeAverage z.displacement h) (Set.Icc 0 B) := by
    simpa only [Set.uIcc_of_le hB.le] using hxa.continuousOn
  have hyc : ContinuousOn (timeAverage z.velocity h) (Set.Icc 0 B) := by
    simpa only [Set.uIcc_of_le hB.le] using hya.continuousOn
  have hac : ContinuousOn a (Set.Icc 0 T) := by
    simpa only [Set.uIcc_of_le hT.le] using
      (@AbsolutelyContinuousOnInterval.continuousOn (Form V) inferInstance 0 T a
        (scalarC1_form_ac T hT.le a ha.scalarC1))
  have hq : ContinuousOn (fun r => h⁻¹ •
      (z.displacement (r+h)-z.displacement r)) (Set.Icc 0 B) := by
    apply continuousOn_const.smul
    apply ContinuousOn.sub _ (huc.mono hsub)
    exact huc.comp (continuousOn_id.add continuousOn_const) hth
  have hau : IntervalIntegrable (fun r => a r (z.displacement r)) volume 0 T :=
    ((hac.clm_apply huc).mono (by rw [Set.uIcc_of_le hT.le])).intervalIntegrable
  have hca : ContinuousOn (formCommutator a z.displacement h) (Set.Icc 0 B) :=
    ((hac.mono hsub).clm_apply hxc).sub
      (timeAverage_continuousOn hB.le hh.le hBh hau)
  have hfi : IntervalIntegrable (fun r => f r) volume 0 T :=
    intervalIntegrable_of_timeIntegrable T ((Lp.memLp f).integrable (by norm_num))
      ⟨0,⟨le_rfl,hT.le⟩⟩ ⟨T,⟨hT.le,le_rfl⟩⟩
  have hFc := timeAverage_continuousOn hB.le hh.le hBh hfi
  exact regularized_balance_of_graphs j T B hB hBT a ha.scalarC1 ha.symmetric
    (timeAverage z.displacement h)
    (fun r => h⁻¹ • (z.displacement (r+h)-z.displacement r))
    (timeAverage z.velocity h)
    (fun r => h⁻¹ • (z.velocity (r+h)-z.velocity r))
    (timeAverage (fun r => f r) h) (formCommutator a z.displacement h)
    hxa hya hdx hdy
    (fun r hr => averaged_kinematics j T hT a u₀ v₀ f z h r (hsub hr) (hth r hr))
    (fun r hr => averaged_equation j T hT a α C ha u₀ v₀ f z h r hh.le
      (hsub hr) (hth r hr))
    ((hFc.inner hyc).mono (by rw [Set.uIcc_of_le hB.le])).intervalIntegrable
    ((hca.clm_apply hq).mono (by rw [Set.uIcc_of_le hB.le])).intervalIntegrable

end ExpandedFA.Evolution.SymmetricHyperbolicEquation

namespace ExpandedFA.Evolution.SymmetricHyperbolicEquation
open HilbertTripleSpec HyperbolicFormSpec HyperbolicWeakEnergySpec
open SymmetricHyperbolicSpec
open HyperbolicWeakEnergyExistence HyperbolicWeakEnergyUniqueness

variable {V : Type u}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- The integral of the commutator work vanishes with the averaging length. -/
theorem commutator_work_integral_tendsto (T B : ℝ) (hB : 0 ≤ B) (hBT : B < T)
    (a : ℝ → Form V) (ha : ScalarC1 T a)
    (x : ℝ → V) (hx : ContinuousOn x (Set.Icc 0 T)) :
    Tendsto (fun h : ℝ => ∫ r in 0..B,
      formCommutator a x h r (h⁻¹ • (x (r+h)-x r))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hT : 0 ≤ T := le_trans hB hBT.le
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hB1 : 0 < B+1 := by linarith
  obtain ⟨δ,hδ,hsmall⟩ := commutator_work_small T hT a ha x hx
    (ε / (B+1)) (div_pos hε hB1)
  have hhpos : ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h := self_mem_nhdsWithin
  have hδmem : ∀ᶠ h : ℝ in 𝓝[>] 0, h < δ :=
    (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0) (Iio_mem_nhds hδ)
  have hTmem : ∀ᶠ h : ℝ in 𝓝[>] 0, h < T-B :=
    (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
      (Iio_mem_nhds (sub_pos.mpr hBT))
  filter_upwards [hhpos,hδmem,hTmem] with h hh hhδ hhtop
  have hi : ‖∫ r in 0..B, formCommutator a x h r
      (h⁻¹ • (x (r+h)-x r))‖ ≤ (ε / (B+1)) * B := by
    simpa only [sub_zero, abs_of_nonneg hB] using
      (intervalIntegral.norm_integral_le_of_norm_le_const
        (a := 0) (b := B) (C := ε/(B+1)) (fun r hr => by
          rw [Set.uIoc_of_le hB] at hr
          rw [Real.norm_eq_abs]
          exact (hsmall h hh hhδ r ⟨hr.1.le,hr.2.trans hBT.le⟩
            (by linarith [hr.2])).le))
  rw [dist_eq_norm, sub_zero]
  calc
    _ ≤ (ε/(B+1))*B := hi
    _ < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hB1]
      nlinarith

end ExpandedFA.Evolution.SymmetricHyperbolicEquation

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace ExpandedFA.Evolution.SymmetricHyperbolicEquation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem timeAverage_sub_bound (x : ℝ → E) {h t ε : ℝ} (hh : 0 < h)
    (hx : ContinuousOn x (Set.Icc t (t+h)))
    (hb : ∀ r ∈ Set.Icc t (t+h), ‖x r-x t‖ ≤ ε) :
    ‖timeAverage x h t-x t‖ ≤ ε := by
  have hth : t ≤ t+h := by linarith
  have hxi : IntervalIntegrable x volume t (t+h) :=
    (hx.mono (by rw [Set.uIcc_of_le hth])).intervalIntegrable
  have heq : timeAverage x h t-x t = h⁻¹ • ∫ r in t..t+h, (x r-x t) := by
    rw [intervalIntegral.integral_sub hxi intervalIntegrable_const,
      intervalIntegral.integral_const, add_sub_cancel_left, smul_sub, smul_smul,
      inv_mul_cancel₀ (ne_of_gt hh), one_smul]
    rfl
  rw [heq, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hh]
  calc
    _ ≤ h⁻¹ * (ε*h) := by
      gcongr
      convert intervalIntegral.norm_integral_le_of_norm_le_const (C := ε) ?_ using 1
      · rw [add_sub_cancel_left, abs_of_pos hh]
      · intro r hr
        rw [Set.uIoc_of_le hth] at hr
        exact hb r (Set.Ioc_subset_Icc_self hr)
    _ = ε := by field_simp

theorem timeAverage_approximation {T : ℝ} {x : ℝ → E}
    (hx : ContinuousOn x (Set.Icc 0 T)) :
    ∀ ε > 0, ∃ δ > 0, ∀ h : ℝ, 0 < h → h < δ →
      ∀ t ∈ Set.Icc 0 T, t+h ≤ T → ‖timeAverage x h t-x t‖ < ε := by
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := (Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hx)) (ε/2) (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro h hh hhδ t ht htop
  have hsub : Set.Icc t (t+h) ⊆ Set.Icc 0 T := Set.Icc_subset_Icc ht.1 htop
  apply lt_of_le_of_lt (timeAverage_sub_bound x hh (hx.mono hsub) ?_) (half_lt_self hε)
  intro r hr
  apply le_of_lt
  have hsmall : dist r t < δ := by
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hr.1)]
    linarith [hr.2]
  simpa only [dist_eq_norm] using hd r (hsub hr) t ht hsmall

theorem timeAverage_tendstoUniformlyOn {T B : ℝ} (hBT : B < T) {x : ℝ → E}
    (hx : ContinuousOn x (Set.Icc 0 T)) :
    TendstoUniformlyOn (fun h => timeAverage x h) x (𝓝[Set.Ioi 0] 0) (Set.Icc 0 B) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := timeAverage_approximation hx ε hε
  have hpos : ∀ᶠ h : ℝ in 𝓝[Set.Ioi 0] 0, 0 < h := self_mem_nhdsWithin
  have hsmall : ∀ᶠ h : ℝ in 𝓝[Set.Ioi 0] 0, h < min δ (T-B) :=
    (eventually_lt_nhds (lt_min hδ (sub_pos.mpr hBT))).filter_mono nhdsWithin_le_nhds
  filter_upwards [hpos,hsmall] with h hh hs t ht
  have htop : t+h ≤ T := by linarith [ht.2, (lt_min_iff.mp hs).2]
  have htT : t ∈ Set.Icc 0 T := ⟨ht.1, ht.2.trans hBT.le⟩
  simpa only [dist_eq_norm, norm_sub_rev] using hd h hh (lt_min_iff.mp hs).1 t htT htop
end ExpandedFA.Evolution.SymmetricHyperbolicEquation

namespace ExpandedFA.Evolution.SymmetricHyperbolicEquation
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem quadraticForms_tendstoUniformlyOn {ι : Type*} {l : Filter ι} {S : Set ℝ}
    {X : ι → ℝ → V} {x : ℝ → V} {b : ℝ → V →L[ℝ] V →L[ℝ] ℝ}
    (hX : TendstoUniformlyOn X x l S)
    {M R : ℝ} (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hb : ∀ t ∈ S, ‖b t‖ ≤ M) (hx : ∀ t ∈ S, ‖x t‖ ≤ R) :
    TendstoUniformlyOn (fun i t => b t (X i t) (X i t))
      (fun t => b t (x t) (x t)) l S := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hL : 0 < M*(2*R+1)+1 := by positivity
  have hδ : 0 < min (ε/(M*(2*R+1)+1)) 1 := by positivity
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hX _ hδ] with i hi t ht
  have herr : ‖X i t-x t‖ < min (ε/(M*(2*R+1)+1)) 1 := by
    simpa only [dist_eq_norm, norm_sub_rev] using hi t ht
  have hXi : ‖X i t‖ ≤ R+1 := by
    calc
      ‖X i t‖ = ‖(X i t-x t)+x t‖ := by rw [sub_add_cancel]
      _ ≤ ‖X i t-x t‖ + ‖x t‖ := norm_add_le _ _
      _ ≤ R+1 := by linarith [hx t ht, (lt_min_iff.mp herr).2]
  have heq : b t (X i t) (X i t) - b t (x t) (x t) =
      b t (X i t-x t) (X i t) + b t (x t) (X i t-x t) := by
    simp only [map_sub, sub_apply]
    ring
  have hbound : ‖b t (X i t) (X i t) - b t (x t) (x t)‖ ≤
      M*(2*R+1)*‖X i t-x t‖ := by
    rw [heq]
    calc
      _ ≤ ‖b t (X i t-x t) (X i t)‖ + ‖b t (x t) (X i t-x t)‖ := norm_add_le _ _
      _ ≤ M*‖X i t-x t‖*(R+1) + M*R*‖X i t-x t‖ := by
        gcongr
        exact (b t).le_of_opNorm₂_le_of_le (hb t ht) le_rfl hXi
        exact (b t).le_of_opNorm₂_le_of_le (hb t ht) (hx t ht) le_rfl
      _ = _ := by ring
  rw [dist_eq_norm, norm_sub_rev]
  calc
    _ ≤ M*(2*R+1)*‖X i t-x t‖ := hbound
    _ ≤ (M*(2*R+1)+1)*‖X i t-x t‖ := by gcongr; linarith
    _ < (M*(2*R+1)+1)*(ε/(M*(2*R+1)+1)) :=
      mul_lt_mul_of_pos_left (lt_min_iff.mp herr).1 hL
    _ = ε := mul_div_cancel₀ ε (ne_of_gt hL)
end ExpandedFA.Evolution.SymmetricHyperbolicEquation

namespace ExpandedFA.Evolution.SymmetricHyperbolicEquation
open HilbertTripleSpec HyperbolicFormSpec HyperbolicWeakEnergySpec SymmetricHyperbolicSpec
variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

theorem formPower_continuousOn_subinterval {T B : ℝ} (hT : 0 < T) (hBT : B ≤ T)
    (a : ℝ → Form V) (ha : ScalarC1 T a) (x : ℝ → V)
    (hx : ContinuousOn x (Set.Icc 0 B)) :
    ContinuousOn (formPower T a x) (Set.Icc 0 B) := by
  have hsub : Set.Icc 0 B ⊆ Set.Icc 0 T := Set.Icc_subset_Icc le_rfl hBT
  obtain ⟨M, _, hb⟩ := derivativeForm_bounded T a ha
  have hc (u v : V) : ContinuousOn (fun r => derivativeForm T a ha r u v)
      (Set.Icc 0 B) := by
    apply (((ha u v).continuousOn_derivWithin (uniqueDiffOn_Icc hT) (by simp)).mono hsub).congr
    intro t ht
    exact derivativeForm_apply T a ha t (hsub ht) u v
  exact (continuousOn_form_apply (Set.Icc 0 B) _ hc M
    (fun r hr => hb r (hsub hr)) x x hx hx).congr
    (fun t ht => (derivativeForm_apply T a ha t (hsub ht) (x t) (x t)).symm)

theorem formPower_timeAverage_tendstoUniformlyOn {T B : ℝ} (hBT : B < T)
    (a : ℝ → Form V) (ha : ScalarC1 T a) {x : ℝ → V}
    (hx : ContinuousOn x (Set.Icc 0 T)) :
    TendstoUniformlyOn (fun h => formPower T a (timeAverage x h))
      (formPower T a x) (𝓝[Set.Ioi 0] 0) (Set.Icc 0 B) := by
  have hsub : Set.Icc 0 B ⊆ Set.Icc 0 T := Set.Icc_subset_Icc le_rfl hBT.le
  obtain ⟨M, hM, hb⟩ := derivativeForm_bounded T a ha
  obtain ⟨R₀, hR₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hx
  let R := max R₀ 0
  have hR : 0 ≤ R := le_max_right _ _
  have hbound : ∀ r ∈ Set.Icc 0 B, ‖x r‖ ≤ R :=
    fun r hr => (hR₀ r (hsub hr)).trans (le_max_left _ _)
  have hu := quadraticForms_tendstoUniformlyOn
    (b := derivativeForm T a ha) (timeAverage_tendstoUniformlyOn hBT hx)
    hM hR (fun r hr => hb r (hsub hr)) hbound
  apply (hu.congr_right ?_).congr
  · exact Filter.Eventually.of_forall fun h t ht =>
      derivativeForm_apply T a ha t (hsub ht) (timeAverage x h t) (timeAverage x h t)
  · intro t ht
    exact derivativeForm_apply T a ha t (hsub ht) (x t) (x t)

theorem formPower_timeAverage_integral_tendsto {T B : ℝ} (hB : 0 ≤ B) (hBT : B < T)
    (a : ℝ → Form V) (ha : ScalarC1 T a) {x : ℝ → V}
    (hx : ContinuousOn x (Set.Icc 0 T)) :
    Tendsto (fun h => ∫ t in 0..B, formPower T a (timeAverage x h) t)
      (𝓝[Set.Ioi 0] 0) (𝓝 (∫ t in 0..B, formPower T a x t)) := by
  have hT : 0 < T := lt_of_le_of_lt hB hBT
  have hi : IntervalIntegrable x volume 0 T :=
    (hx.mono (by rw [Set.uIcc_of_le hT.le])).intervalIntegrable
  have hu := formPower_timeAverage_tendstoUniformlyOn hBT a ha hx
  apply TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn
    (μ := volume) ?_ (by simpa [Set.uIcc_of_le hB] using hu)
  have hpos : ∀ᶠ h : ℝ in 𝓝[Set.Ioi 0] 0, 0 < h := self_mem_nhdsWithin
  have hsmall : ∀ᶠ h : ℝ in 𝓝[Set.Ioi 0] 0, h < T-B :=
    (eventually_lt_nhds (sub_pos.mpr hBT)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hpos,hsmall] with h hh hs
  have hc := timeAverage_continuousOn hB hh.le (by linarith : B+h ≤ T) hi
  simpa [Set.uIcc_of_le hB] using
    formPower_continuousOn_subinterval hT hBT.le a ha (timeAverage x h) hc
end ExpandedFA.Evolution.SymmetricHyperbolicEquation

namespace ExpandedFA.Evolution.SymmetricHyperbolicEquation
open HilbertTripleSpec HyperbolicFormSpec HyperbolicWeakEnergySpec SymmetricHyperbolicSpec
open HyperbolicWeakEnergyExistence HyperbolicWeakEnergyUniqueness
variable {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- An interior balance determines all oriented endpoint balances by continuity. -/
theorem energy_identity_of_interior_balances (j : HilbertTriple V H) (T : ℝ) (hT : 0 < T)
    (a : ℝ → Form V) (α C : ℝ) (ha : FormHypotheses j T a α C)
    (u₀ : V) (v₀ : H) (f : timeLpValue H 2 T)
    (z : WeakEnergySolution j T a u₀ v₀ f)
    (hbalance : ∀ B : ℝ, 0 < B → B < T →
      energy a z.displacement z.velocity B - energy a z.displacement z.velocity 0 =
      2 * (∫ r in 0..B, inner ℝ (f r) (z.velocity r)) +
      ∫ r in 0..B, formPower T a z.displacement r) : HasEnergyIdentity z := by
  obtain ⟨hx, hy⟩ := strong_state_continuity j T hT.le a α C ha u₀ v₀ f z
  obtain ⟨_, hf, hp⟩ := energy_terms_integrable j T hT a α C ha u₀ v₀ f z
  have hfi : IntervalIntegrable (fun r => inner ℝ (f r) (z.velocity r)) volume 0 T :=
    intervalIntegrable_of_timeIntegrable T hf ⟨0, ⟨le_rfl, hT.le⟩⟩ ⟨T, ⟨hT.le, le_rfl⟩⟩
  have hpi : IntervalIntegrable (formPower T a z.displacement) volume 0 T :=
    intervalIntegrable_of_timeIntegrable T hp ⟨0, ⟨le_rfl, hT.le⟩⟩ ⟨T, ⟨hT.le, le_rfl⟩⟩
  have hfc : ContinuousOn (fun t => ∫ r in 0..t, inner ℝ (f r) (z.velocity r))
      (Set.Icc 0 T) := by
    simpa [Set.uIcc_of_le hT.le] using
      intervalIntegral.continuousOn_primitive_interval' hfi Set.left_mem_uIcc
  have hpc : ContinuousOn (fun t => ∫ r in 0..t, formPower T a z.displacement r)
      (Set.Icc 0 T) := by
    simpa [Set.uIcc_of_le hT.le] using
      intervalIntegral.continuousOn_primitive_interval' hpi Set.left_mem_uIcc
  have hall : ∀ t ∈ Set.Icc 0 T,
      energy a z.displacement z.velocity t - energy a z.displacement z.velocity 0 =
      2 * (∫ r in 0..t, inner ℝ (f r) (z.velocity r)) +
      ∫ r in 0..t, formPower T a z.displacement r := by
    apply Set.EqOn.of_subset_closure (s := Set.Ioo 0 T)
      (fun t ht => hbalance t ht.1 ht.2)
      ((energy_continuousOn T a ha.scalarC1 _ _ hx hy).sub continuousOn_const)
      ((continuousOn_const.mul hfc).add hpc) Set.Ioo_subset_Icc_self
    rw [closure_Ioo hT.ne]
  intro s hs t ht
  have hf0s := intervalIntegrable_of_timeIntegrable T hf ⟨0, ⟨le_rfl,hT.le⟩⟩ ⟨s,hs⟩
  have hf0t := intervalIntegrable_of_timeIntegrable T hf ⟨0, ⟨le_rfl,hT.le⟩⟩ ⟨t,ht⟩
  have hp0s := intervalIntegrable_of_timeIntegrable T hp ⟨0, ⟨le_rfl,hT.le⟩⟩ ⟨s,hs⟩
  have hp0t := intervalIntegrable_of_timeIntegrable T hp ⟨0, ⟨le_rfl,hT.le⟩⟩ ⟨t,ht⟩
  refine ⟨intervalIntegrable_of_timeIntegrable T hf ⟨s,hs⟩ ⟨t,ht⟩,
    intervalIntegrable_of_timeIntegrable T hp ⟨s,hs⟩ ⟨t,ht⟩, ?_⟩
  rw [← intervalIntegral.integral_interval_sub_left hf0t hf0s,
    ← intervalIntegral.integral_interval_sub_left hp0t hp0s]
  linarith [hall s hs, hall t ht]

end ExpandedFA.Evolution.SymmetricHyperbolicEquation

namespace ExpandedFA.Evolution.SymmetricHyperbolicEquation
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def translationError (f : ℝ → E) (r : ℝ) : ℝ :=
  ∫ t, ‖f (t+r) - f t‖

theorem translationError_continuous (f : ℝ → E) (hf : Integrable f volume) :
    Continuous (translationError f) := by
  let F : Lp E 1 volume := hf.toL1 f
  let shift (r : ℝ) : C(ℝ, ℝ) := ⟨fun t => t+r, continuous_id.add continuous_const⟩
  have hshift : Continuous shift :=
    ContinuousMap.continuous_of_continuous_uncurry shift (continuous_snd.add continuous_fst)
  have hmp (r : ℝ) : MeasurePreserving (shift r) volume volume :=
    measurePreserving_add_right volume r
  have hc : Continuous (fun r => Lp.compMeasurePreserving (shift r) (hmp r) F) :=
    (continuous_const : Continuous (fun _ : ℝ => F)).compMeasurePreservingLp
      hshift hmp (by norm_num)
  apply ((hc.sub continuous_const).norm).congr
  intro r
  rw [L1.norm_eq_integral_norm]
  apply integral_congr_ae
  have hF := hf.coeFn_toL1
  have hFr := (hmp r).quasiMeasurePreserving.ae hF
  filter_upwards [Lp.coeFn_sub (Lp.compMeasurePreserving (shift r) (hmp r) F) F,
    Lp.coeFn_compMeasurePreserving F (hmp r), hF, hFr] with t ht hs hf₀ hf₁
  simp only [Function.comp_def] at hs
  change ‖(Lp.compMeasurePreserving (shift r) (hmp r) F - F) t‖ = ‖f (t+r)-f t‖
  rw [ht]
  change ‖(Lp.compMeasurePreserving (shift r) (hmp r) F) t - F t‖ = _
  rw [hs, hf₀]
  exact congrArg (fun z : E => ‖z-f t‖) hf₁



theorem timeAverage_continuous (f : ℝ → E) (hf : Integrable f volume) (h : ℝ) :
    Continuous (timeAverage f h) := by
  have hp := intervalIntegral.continuous_primitive (fun _ _ => hf.intervalIntegrable) 0
  have heq : timeAverage f h = fun t => h⁻¹ •
      ((∫ r in 0..t+h, f r) - ∫ r in 0..t, f r) := by
    funext t
    rw [timeAverage, intervalIntegral.integral_interval_sub_left
      hf.intervalIntegrable hf.intervalIntegrable]
  rw [heq]
  exact continuous_const.smul ((hp.comp (continuous_id.add continuous_const)).sub hp)

theorem timeAverage_error_eq (f : ℝ → E) (hf : Integrable f volume) (h : ℝ) (hh : h ≠ 0)
    (t : ℝ) :
    timeAverage f h t - f t = h⁻¹ • ∫ r in 0..h, (f (t+r)-f t) := by
  have hi : IntervalIntegrable (fun r => f (t+r)) volume 0 h :=
    ((measurePreserving_add_left volume t).integrable_comp_of_integrable hf).intervalIntegrable
  rw [intervalIntegral.integral_sub (f := fun r => f (t+r)) (g := fun _ => f t) hi
      intervalIntegrable_const,
    intervalIntegral.integral_comp_add_left,
    intervalIntegral.integral_const]
  simp only [add_zero, zero_add, sub_zero, smul_sub, smul_smul, inv_mul_cancel₀ hh, one_smul, timeAverage]

theorem average_translationError_tendsto (f : ℝ → E) (hf : Integrable f volume) :
    Tendsto (fun h : ℝ => h⁻¹ * ∫ r in 0..h, translationError f r)
      (𝓝[>] 0) (𝓝 0) := by
  have hc := translationError_continuous f hf
  have hd := intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable 0 0) hc.aestronglyMeasurable.stronglyMeasurableAtFilter
    (hc.continuousAt (x := 0))
  simpa [translationError] using hd.tendsto_slope_zero_right

/-- Translation increments of an L¹ function are jointly integrable on a rectangle. -/
theorem integrable_shift_sub_rectangle (f : ℝ → E) (hf : Integrable f volume)
    (B h : ℝ) :
    Integrable (fun p : ℝ × ℝ => f (p.1+p.2) - f p.1)
      ((volume.restrict (Ioc 0 B)).prod (volume.restrict (Ioc 0 h))) := by
  let ν : Measure ℝ := volume.restrict (Ioc 0 h)
  have hfst : Integrable (fun p : ℝ × ℝ => f p.1) (volume.prod ν) := hf.comp_fst ν
  have hshift : Integrable (fun p : ℝ × ℝ => f (p.1+p.2)) (volume.prod ν) := by
    exact (measurePreserving_add_prod volume ν).integrable_comp_of_integrable hfst
  exact (hshift.sub hfst).mono_measure
    (Measure.prod_mono Measure.restrict_le_self le_rfl)


theorem timeAverage_L1_error_bound (f : ℝ → E) (hf : Integrable f volume)
    (B h : ℝ) (hB : 0 ≤ B) (hh : 0 < h) :
    (∫ t in 0..B, ‖timeAverage f h t - f t‖) ≤
      h⁻¹ * ∫ r in 0..h, translationError f r := by
  have hj := integrable_shift_sub_rectangle f hf B h
  have hji : IntegrableOn (fun p : ℝ × ℝ => ‖f (p.1+p.2)-f p.1‖)
      (Set.uIoc 0 B ×ˢ Set.uIoc 0 h) := by
    rw [IntegrableOn, Set.uIoc_of_le hB, Set.uIoc_of_le hh.le,
      Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact hj.norm
  have hnorm := hj.integral_norm_prod_left
  have hnorm' : IntervalIntegrable (fun t => ∫ r in 0..h, ‖f (t+r)-f t‖) volume 0 B := by
    rw [IntervalIntegrable, Ioc_eq_empty hB.not_gt]
    simp only [integrableOn_empty, and_true]
    simpa only [intervalIntegral.integral_of_le hh.le, IntegrableOn] using hnorm
  have herror : IntervalIntegrable (fun t => ‖timeAverage f h t-f t‖) volume 0 B :=
    (((timeAverage_continuous f hf h).intervalIntegrable 0 B).sub hf.intervalIntegrable).norm
  calc
    _ ≤ ∫ t in 0..B, h⁻¹ * ∫ r in 0..h, ‖f (t+r)-f t‖ := by
      apply intervalIntegral.integral_mono_on hB herror (hnorm'.const_mul _) 
      intro t ht
      rw [timeAverage_error_eq f hf h hh.ne' t, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr hh.le)]
      exact mul_le_mul_of_nonneg_left (intervalIntegral.norm_integral_le_integral_norm hh.le)
        (inv_nonneg.mpr hh.le)
    _ = h⁻¹ * ∫ r in 0..h, ∫ t in 0..B, ‖f (t+r)-f t‖ := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral_intervalIntegral_swap (F := fun t r => ‖f (t+r)-f t‖) hji]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hh.le)
      apply intervalIntegral.integral_mono_on hh.le
      · have hi := hj.integral_norm_prod_right
        rw [IntervalIntegrable, Ioc_eq_empty hh.le.not_gt]
        simp only [integrableOn_empty, and_true]
        simpa only [intervalIntegral.integral_of_le hB, IntegrableOn] using hi
      · exact (translationError_continuous f hf).intervalIntegrable _ _
      · intro r hr
        rw [intervalIntegral.integral_of_le hB]
        apply setIntegral_le_integral
        · exact (measurePreserving_add_right volume r).integrable_comp_of_integrable hf |>.sub hf |>.norm
        · exact Filter.Eventually.of_forall fun _ => norm_nonneg _


theorem timeAverage_L1_tendsto (f : ℝ → E) (hf : Integrable f volume)
    (B : ℝ) (hB : 0 ≤ B) :
    Tendsto (fun h : ℝ => ∫ t in 0..B, ‖timeAverage f h t - f t‖)
      (𝓝[>] 0) (𝓝 0) := by
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun h => intervalIntegral.integral_nonneg hB
      (fun _ _ => norm_nonneg _))
    (Filter.eventually_of_mem self_mem_nhdsWithin fun h hh => timeAverage_L1_error_bound f hf B h hB hh)
  exact average_translationError_tendsto f hf

end ExpandedFA.Evolution.SymmetricHyperbolicEquation

namespace ExpandedFA.Evolution.SymmetricHyperbolicEquation
open HilbertTripleSpec
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem timeLp_zeroExtension_integrable (T : ℝ) (f : timeLpValue E 2 T) :
    Integrable ((Set.Ioo 0 T).indicator (fun t => f t)) volume := by
  let : IsFiniteMeasure (timeMeasureValue T) :=
    inferInstanceAs (IsFiniteMeasure (volume.restrict (Set.Ioo 0 T)))
  exact (integrable_indicator_iff measurableSet_Ioo).mpr
    ((Lp.memLp f).integrable (by norm_num))

theorem timeAverage_zeroExtension (T : ℝ) (f : ℝ → E)
    {h t : ℝ} (hh : 0 < h) (ht : 0 ≤ t) (hth : t+h ≤ T) :
    timeAverage ((Set.Ioo 0 T).indicator f) h t = timeAverage f h t := by
  unfold timeAverage
  congr 1
  apply intervalIntegral.integral_congr_ae
  filter_upwards [show ∀ᵐ r : ℝ ∂volume, r ≠ T from by simp [ae_iff, measure_singleton]] with r hr hmem
  have hmem' : r ∈ Set.Ioc t (t+h) := by
    simpa only [Set.uIoc_of_le (by linarith : t ≤ t+h)] using hmem
  exact Set.indicator_of_mem (show r ∈ Set.Ioo 0 T from
    ⟨lt_of_le_of_lt ht hmem'.1, lt_of_le_of_ne (hmem'.2.trans hth) hr⟩) f

end ExpandedFA.Evolution.SymmetricHyperbolicEquation


namespace ExpandedFA.Evolution.SymmetricHyperbolicEquation
open HilbertTripleSpec HyperbolicFormSpec HyperbolicWeakEnergySpec SymmetricHyperbolicSpec
variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem energy_timeAverage_tendsto {T B t : ℝ} (hBT : B < T)
    (ht : t ∈ Set.Icc 0 B) (a : ℝ → Form V) {x : ℝ → V} {y : ℝ → H}
    (hx : ContinuousOn x (Set.Icc 0 T)) (hy : ContinuousOn y (Set.Icc 0 T)) :
    Tendsto (fun h => energy a (timeAverage x h) (timeAverage y h) t)
      (𝓝[Set.Ioi 0] 0) (𝓝 (energy a x y t)) := by
  have hxlim := (timeAverage_tendstoUniformlyOn hBT hx).tendsto_at ht
  have hylim := (timeAverage_tendstoUniformlyOn hBT hy).tendsto_at ht
  have hquad : Continuous (fun z : V => a t z z) :=
    ((a t).continuous.comp continuous_id).clm_apply continuous_id
  exact (hylim.norm.pow 2).add ((hquad.tendsto (x t)).comp hxlim)
end ExpandedFA.Evolution.SymmetricHyperbolicEquation


namespace ExpandedFA.Evolution.SymmetricHyperbolicEquation
open HilbertTripleSpec HyperbolicFormSpec HyperbolicWeakEnergySpec SymmetricHyperbolicSpec
open HyperbolicWeakEnergyExistence HyperbolicWeakEnergyUniqueness
variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem interior_energy_balance_of_forcing_limit (j : HilbertTriple V H)
    (T B : ℝ) (hB : 0 < B) (hBT : B < T)
    (a : ℝ → Form V) (α C : ℝ) (ha : FormHypotheses j T a α C)
    (u₀ : V) (v₀ : H) (f : timeLpValue H 2 T)
    (z : WeakEnergySolution j T a u₀ v₀ f)
    (hforcing : Tendsto (fun h => ∫ r in 0..B,
      inner ℝ (timeAverage (fun r => f r) h r) (timeAverage z.velocity h r))
      (𝓝[Set.Ioi 0] 0) (𝓝 (∫ r in 0..B, inner ℝ (f r) (z.velocity r)))) :
    energy a z.displacement z.velocity B - energy a z.displacement z.velocity 0 =
      2 * (∫ r in 0..B, inner ℝ (f r) (z.velocity r)) +
      ∫ r in 0..B, formPower T a z.displacement r := by
  have hT : 0 < T := hB.trans hBT
  obtain ⟨hx, hy⟩ := strong_state_continuity j T hT.le a α C ha u₀ v₀ f z
  have hleft :=
    (energy_timeAverage_tendsto hBT (show B ∈ Set.Icc 0 B from ⟨hB.le, le_rfl⟩) a hx hy).sub
    (energy_timeAverage_tendsto hBT (show (0 : ℝ) ∈ Set.Icc 0 B from ⟨le_rfl, hB.le⟩) a hx hy)
  have hpower := formPower_timeAverage_integral_tendsto hB.le hBT a ha.scalarC1 hx
  have herror := commutator_work_integral_tendsto T B hB.le hBT a ha.scalarC1
    z.displacement hx
  have hright := ((hforcing.const_mul 2).add hpower).add (herror.const_mul 2)
  simp only [mul_zero, add_zero] at hright
  have heq : (fun h =>
      energy a (timeAverage z.displacement h) (timeAverage z.velocity h) B -
      energy a (timeAverage z.displacement h) (timeAverage z.velocity h) 0) =ᶠ[𝓝[Set.Ioi 0] 0]
      (fun h => 2 * (∫ r in 0..B,
        inner ℝ (timeAverage (fun r => f r) h r) (timeAverage z.velocity h r)) +
        (∫ r in 0..B, formPower T a (timeAverage z.displacement h) r) +
        2 * ∫ r in 0..B, formCommutator a z.displacement h r
          (h⁻¹ • (z.displacement (r+h)-z.displacement r))) := by
    have hpos : ∀ᶠ h : ℝ in 𝓝[Set.Ioi 0] 0, 0 < h := self_mem_nhdsWithin
    have hsmall : ∀ᶠ h : ℝ in 𝓝[Set.Ioi 0] 0, h < T-B :=
      (eventually_lt_nhds (sub_pos.mpr hBT)).filter_mono nhdsWithin_le_nhds
    filter_upwards [hpos,hsmall] with h hh hs
    exact regularized_energy_balance j T B h hB hh (by linarith) a α C ha u₀ v₀ f z
  exact tendsto_nhds_unique hleft (hright.congr' heq.symm)
end ExpandedFA.Evolution.SymmetricHyperbolicEquation

namespace ExpandedFA.Evolution.SymmetricHyperbolicEquation
open HyperbolicWeakEnergyUniqueness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- L¹ convergence of the averaged forcing and uniform convergence of the
averaged velocity suffice to pass the forcing work to the limit. -/
theorem forcing_work_tendsto_of_L1_average (T B : ℝ) (hB : 0 ≤ B) (hBT : B < T)
    (F : ℝ → H) (hF : Integrable F volume)
    (y : ℝ → H) (hy : ContinuousOn y (Set.Icc 0 T))
    (hL1 : Tendsto (fun h : ℝ => ∫ t in 0..B, ‖timeAverage F h t-F t‖)
      (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto (fun h : ℝ => ∫ t in 0..B,
      inner ℝ (timeAverage F h t) (timeAverage y h t))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ t in 0..B, inner ℝ (F t) (y t))) := by
  have hT : 0 < T := lt_of_le_of_lt hB hBT
  have hsub : Set.Icc 0 B ⊆ Set.Icc 0 T := Set.Icc_subset_Icc le_rfl hBT.le
  have hyB : ContinuousOn y (Set.Icc 0 B) := hy.mono hsub
  obtain ⟨R₀,hR₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hyB
  let R := max R₀ 0
  have hR : 0 ≤ R := le_max_right _ _
  have hyR : ∀ t ∈ Set.Icc 0 B, ‖y t‖ ≤ R :=
    fun t ht => (hR₀ t ht).trans (le_max_left _ _)
  have hFi : IntervalIntegrable F volume 0 B := hF.intervalIntegrable
  have hFn : IntervalIntegrable (fun t => ‖F t‖) volume 0 B := hFi.norm
  let I := ∫ t in 0..B, ‖F t‖
  have hI : 0 ≤ I := intervalIntegral.integral_nonneg hB (fun t _ => norm_nonneg _)
  have hYdual : ContinuousOn (fun t => (innerSL ℝ : H →L[ℝ] H →L[ℝ] ℝ) (y t))
      (Set.uIcc 0 B) :=
    (innerSL ℝ).continuous.comp_continuousOn (hyB.mono (by rw [Set.uIcc_of_le hB]))
  have hwork : IntervalIntegrable (fun t => inner ℝ (F t) (y t)) volume 0 B := by
    have hw := intervalIntegrable_dual_pairing hYdual hFi
    exact hw.congr (fun t _ => (real_inner_comm (y t) (F t)).symm)
  have hY := timeAverage_tendstoUniformlyOn hBT hy
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := ε / (R+I+2)
  have hK : 0 < R+I+2 := by positivity
  have hδ : 0 < δ := div_pos hε hK
  have hδε : (R+I+2)*δ = ε := mul_div_cancel₀ ε (ne_of_gt hK)
  have hδY := Metric.tendstoUniformlyOn_iff.mp hY (min δ 1) (lt_min hδ zero_lt_one)
  have hδF : ∀ᶠ h : ℝ in 𝓝[>] 0,
      (∫ t in 0..B, ‖timeAverage F h t-F t‖) < δ := hL1.eventually (Iio_mem_nhds hδ)
  have hhpos : ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h := self_mem_nhdsWithin
  have hhtop : ∀ᶠ h : ℝ in 𝓝[>] 0, h < T-B :=
    (eventually_lt_nhds (sub_pos.mpr hBT)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hδY,hδF,hhpos,hhtop] with h hYu hFu hh hhtop
  have hBh : B+h ≤ T := by linarith
  have hFc := timeAverage_continuousOn hB hh.le hBh (hF.intervalIntegrable (a := 0) (b := T))
  have hyi : IntervalIntegrable y volume 0 T :=
    (hy.mono (by rw [Set.uIcc_of_le hT.le])).intervalIntegrable
  have hYc := timeAverage_continuousOn hB hh.le hBh hyi
  have hFhi : IntervalIntegrable (timeAverage F h) volume 0 B :=
    (hFc.mono (by rw [Set.uIcc_of_le hB])).intervalIntegrable
  have hdiffi : IntervalIntegrable (fun t => ‖timeAverage F h t-F t‖) volume 0 B :=
    (hFhi.sub hFi).norm
  have hworkh : IntervalIntegrable (fun t => inner ℝ (timeAverage F h t)
      (timeAverage y h t)) volume 0 B :=
    ((hFc.inner hYc).mono (by rw [Set.uIcc_of_le hB])).intervalIntegrable
  have hYerr (t : ℝ) (ht : t ∈ Set.Icc 0 B) :
      ‖timeAverage y h t-y t‖ < min δ 1 := by
    simpa only [dist_eq_norm,norm_sub_rev] using hYu t ht
  have hYR (t : ℝ) (ht : t ∈ Set.Icc 0 B) : ‖timeAverage y h t‖ ≤ R+1 := by
    calc
      _ = ‖(timeAverage y h t-y t)+y t‖ := by rw [sub_add_cancel]
      _ ≤ ‖timeAverage y h t-y t‖ + ‖y t‖ := norm_add_le _ _
      _ ≤ R+1 := by linarith [hyR t ht,(lt_min_iff.mp (hYerr t ht)).2]
  have hbound (t : ℝ) (ht : t ∈ Set.Icc 0 B) :
      ‖inner ℝ (timeAverage F h t) (timeAverage y h t) - inner ℝ (F t) (y t)‖ ≤
        (R+1)*‖timeAverage F h t-F t‖ + δ*‖F t‖ := by
    have heq : inner ℝ (timeAverage F h t) (timeAverage y h t) - inner ℝ (F t) (y t) =
        inner ℝ (timeAverage F h t-F t) (timeAverage y h t) +
          inner ℝ (F t) (timeAverage y h t-y t) := by
      simp only [inner_sub_left,inner_sub_right]
      ring
    rw [heq]
    calc
      _ ≤ ‖inner ℝ (timeAverage F h t-F t) (timeAverage y h t)‖ +
          ‖inner ℝ (F t) (timeAverage y h t-y t)‖ := norm_add_le _ _
      _ ≤ ‖timeAverage F h t-F t‖*‖timeAverage y h t‖ +
          ‖F t‖*‖timeAverage y h t-y t‖ :=
        add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
      _ ≤ ‖timeAverage F h t-F t‖*(R+1) + ‖F t‖*δ := by
        gcongr
        · exact hYR t ht
        · exact (lt_min_iff.mp (hYerr t ht)).1.le
      _ = _ := by ring
  have hi := intervalIntegral.norm_integral_le_of_norm_le hB
    (ae_of_all volume fun t ht => hbound t (Set.Ioc_subset_Icc_self ht))
    ((hdiffi.const_mul (R+1)).add (hFn.const_mul δ))
  rw [intervalIntegral.integral_add (hdiffi.const_mul (R+1)) (hFn.const_mul δ),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at hi
  rw [dist_eq_norm,← intervalIntegral.integral_sub hworkh hwork]
  calc
    _ ≤ (R+1)*(∫ t in 0..B, ‖timeAverage F h t-F t‖) + δ*I := hi
    _ ≤ (R+1)*δ+δ*I := by gcongr
    _ < ε := by nlinarith

end ExpandedFA.Evolution.SymmetricHyperbolicEquation

namespace ExpandedFA.Evolution.SymmetricHyperbolicEquation
open HilbertTripleSpec HyperbolicFormSpec HyperbolicWeakEnergySpec SymmetricHyperbolicSpec
open HyperbolicWeakEnergyExistence HyperbolicWeakEnergyUniqueness
variable {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Cutting off the forcing outside the evolution interval does not change its work. -/
theorem forcing_zeroExtension_work (T B : ℝ) (hB : 0 ≤ B) (hBT : B ≤ T)
    (f y : ℝ → H) :
    (∫ r in 0..B, inner ℝ ((Set.Ioo 0 T).indicator f r) (y r)) =
    ∫ r in 0..B, inner ℝ (f r) (y r) := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [show ∀ᵐ r : ℝ ∂volume, r ≠ T from by simp [ae_iff, measure_singleton]] with r hr hmem
  rw [Set.uIoc_of_le hB] at hmem
  rw [Set.indicator_of_mem (show r ∈ Set.Ioo 0 T from
    ⟨hmem.1, lt_of_le_of_ne (hmem.2.trans hBT) hr⟩)]

/-- Cutting off the forcing outside the evolution interval does not change admissible averages. -/
theorem forcing_zeroExtension_average_work (T B : ℝ) (hB : 0 ≤ B) (hBT : B < T)
    (f y : ℝ → H) :
    (fun h => ∫ r in 0..B, inner ℝ (timeAverage ((Set.Ioo 0 T).indicator f) h r)
      (timeAverage y h r)) =ᶠ[𝓝[>] (0 : ℝ)]
    (fun h => ∫ r in 0..B, inner ℝ (timeAverage f h r) (timeAverage y h r)) := by
  have hpos : ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h := self_mem_nhdsWithin
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0, h < T-B :=
    (eventually_lt_nhds (sub_pos.mpr hBT)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hpos, hsmall] with h hh hs
  apply intervalIntegral.integral_congr
  intro r hr
  rw [Set.uIcc_of_le hB] at hr
  dsimp only
  rw [timeAverage_zeroExtension T f hh hr.1 (by linarith [hr.2])]

end ExpandedFA.Evolution.SymmetricHyperbolicEquation

namespace ExpandedFA.Evolution.SymmetricHyperbolicEquation
open HilbertTripleSpec HyperbolicFormSpec HyperbolicWeakEnergySpec SymmetricHyperbolicSpec
open HyperbolicWeakEnergyExistence HyperbolicWeakEnergyUniqueness
variable {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The work of the averaged forcing converges for the original Bochner L² data. -/
theorem forcing_work_timeAverage_tendsto (T B : ℝ) (hB : 0 ≤ B) (hBT : B < T)
    (f : timeLpValue H 2 T) (y : ℝ → H) (hy : ContinuousOn y (Set.Icc 0 T)) :
    Tendsto (fun h : ℝ => ∫ r in 0..B,
      inner ℝ (timeAverage (fun r => f r) h r) (timeAverage y h r))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ r in 0..B, inner ℝ (f r) (y r))) := by
  let F : ℝ → H := (Set.Ioo 0 T).indicator (fun r => f r)
  have hF : Integrable F volume := timeLp_zeroExtension_integrable T f
  have hlim := forcing_work_tendsto_of_L1_average T B hB hBT F hF y hy
    (timeAverage_L1_tendsto F hF B hB)
  change Tendsto (fun h : ℝ => ∫ r in 0..B,
      inner ℝ (timeAverage ((Set.Ioo 0 T).indicator (fun r => f r)) h r) (timeAverage y h r))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ r in 0..B,
        inner ℝ ((Set.Ioo 0 T).indicator (fun r => f r) r) (y r))) at hlim
  rw [forcing_zeroExtension_work T B hB hBT.le (fun r => f r) y] at hlim
  exact hlim.congr' (forcing_zeroExtension_average_work T B hB hBT (fun r => f r) y)

/-- Exact unshifted energy identity for every weak-energy solution and every
oriented pair of times, including both endpoints and the singleton horizon. -/
theorem energy_identity : EnergyIdentity (V := V) (H := H) := by
  intro j T hT a α C ha u₀ v₀ f z
  by_cases hzero : T = 0
  · subst T
    exact zero_time_energy_identity j a u₀ v₀ f z
  have hpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hzero)
  apply energy_identity_of_interior_balances j T hpos a α C ha u₀ v₀ f z
  intro B hB hBT
  exact interior_energy_balance_of_forcing_limit j T B hB hBT a α C ha u₀ v₀ f z
    (forcing_work_timeAverage_tendsto T B hB.le hBT f z.velocity
      (strong_state_continuity j T hT a α C ha u₀ v₀ f z).2)

/-- The full nonautonomous symmetric hyperbolic theorem on the original real
Hilbert triple, with quantitative well-posedness and the exact energy identity. -/
theorem symmetric_hyperbolic_equation :
    SymmetricHyperbolicSpec.SymmetricHyperbolicEquation (V := V) (H := H) :=
  assemble energy_identity

end ExpandedFA.Evolution.SymmetricHyperbolicEquation

namespace ExpandedFA.Evolution.SymmetricHyperbolicEquation
open HilbertTripleSpec HyperbolicFormSpec HyperbolicWeakEnergySpec SymmetricHyperbolicSpec
open HyperbolicWeakEnergyExistence HyperbolicWeakEnergyUniqueness
variable {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A common scalar form bound supplies an explicit energy growth rate. -/
theorem uniform_energy_rhs_bound (j : HilbertTriple V H) (T : ℝ)
    (a : ℝ → Form V) (α C M : ℝ) (ha : FormHypotheses j T a α C)
    (hM : 0 ≤ M) (hb : CommonFormBounds T a M)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) (x : V) (y h : H) :
    2 * inner ℝ h y + derivWithin (fun r => a r x x) (Set.Icc 0 T) t +
      2 * C * inner ℝ (j.embedding x) y ≤
        (1 + C + (M + C * ‖j.embedding‖ ^ 2) / α) *
          shiftedEnergy j a C t x y + ‖h‖ ^ 2 := by
  let D : ℝ := M + C * ‖j.embedding‖ ^ 2
  have hD : 0 ≤ D := add_nonneg hM (mul_nonneg ha.shift_nonneg (sq_nonneg _))
  have hder : derivWithin (fun r => a r x x) (Set.Icc 0 T) t ≤ M * ‖x‖ ^ 2 := by
    have hbound := hb t ht x x
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

/-- The shifted energy has a common upper bound in the original norms. -/
theorem uniform_shifted_energy_upper (j : HilbertTriple V H) (T : ℝ)
    (a : ℝ → Form V) (C M : ℝ) (hC : 0 ≤ C)
    (hb : CommonFormBounds T a M) {t : ℝ} (ht : t ∈ Set.Icc 0 T) (x : V) (y : H) :
    shiftedEnergy j a C t x y ≤ ‖y‖ ^ 2 + (M + C * ‖j.embedding‖ ^ 2) * ‖x‖ ^ 2 := by
  have hform : a t x x ≤ M * ‖x‖ ^ 2 := by
    have h := hb t ht x x
    nlinarith [le_abs_self (a t x x),
      abs_nonneg (derivWithin (fun r => a r x x) (Set.Icc 0 T) t)]
  have hemb : ‖j.embedding x‖ ^ 2 ≤ ‖j.embedding‖ ^ 2 * ‖x‖ ^ 2 := by
    calc
      ‖j.embedding x‖ ^ 2 ≤ (‖j.embedding‖ * ‖x‖) ^ 2 := by
        gcongr; exact j.embedding.le_opNorm x
      _ = _ := by ring
  rw [shiftedEnergy_eq]
  nlinarith [mul_le_mul_of_nonneg_left hemb hC]

/-- Explicit conversion of Gronwall's bound, uniform in the form family. -/
theorem uniform_state_bound_of_gronwall (j : HilbertTriple V H) (T : ℝ) (hT : 0 ≤ T)
    (a : ℝ → Form V) (α C M : ℝ) (ha : FormHypotheses j T a α C)
    (hM : 0 ≤ M) (hb : CommonFormBounds T a M) (c : ℝ) (hc : 0 ≤ c)
    (u₀ : V) (v₀ : H) (f : timeLpValue H 2 T) (x : ℝ → V) (y : ℝ → H)
    (henergy : ∀ t ∈ Set.Icc 0 T, shiftedEnergy j a C t (x t) (y t) ≤
      Real.exp (c * t) * (shiftedEnergy j a C 0 u₀ v₀ + ∫ r in 0..t, ‖f r‖ ^ 2))
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    ‖x t‖ ^ 2 + ‖y t‖ ^ 2 ≤
      ((1 + 1 / α) * Real.exp (c * T) * (1 + M + C * ‖j.embedding‖ ^ 2)) *
        (‖u₀‖ ^ 2 + ‖v₀‖ ^ 2 + ‖f‖ ^ 2) := by
  let B : ℝ := M + C * ‖j.embedding‖ ^ 2
  have hB : 0 ≤ B := add_nonneg hM (mul_nonneg ha.shift_nonneg (sq_nonneg _))
  have hinv : 0 ≤ 1 / α := div_nonneg zero_le_one ha.alpha_pos.le
  let E := shiftedEnergy j a C t (x t) (y t)
  let D := ‖u₀‖ ^ 2 + ‖v₀‖ ^ 2 + ‖f‖ ^ 2
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hlow := shiftedForm_coercive j T a α C ha ht (x t)
  have hαx : α * ‖x t‖ ^ 2 ≤ E := by dsimp [E, shiftedEnergy]; linarith [sq_nonneg ‖y t‖]
  have hEy : ‖y t‖ ^ 2 ≤ E := by
    have hn := mul_nonneg ha.alpha_pos.le (sq_nonneg ‖x t‖)
    dsimp [E, shiftedEnergy]; linarith
  have hxy : ‖x t‖ ^ 2 + ‖y t‖ ^ 2 ≤ (1 + 1 / α) * E := by
    have h := mul_le_mul_of_nonneg_left hαx hinv
    have heq : 1 / α * (α * ‖x t‖ ^ 2) = ‖x t‖ ^ 2 := by
      field_simp [ha.alpha_pos.ne']
    rw [heq] at h
    nlinarith
  have hi := forcing_integral_bound T hT f ht
  have hinit := uniform_shifted_energy_upper j T a C M ha.shift_nonneg hb ⟨le_rfl,hT⟩ u₀ v₀
  have hdata : shiftedEnergy j a C 0 u₀ v₀ + (∫ r in 0..t, ‖f r‖ ^ 2) ≤ (1 + B) * D := by
    dsimp [D]
    change shiftedEnergy j a C 0 u₀ v₀ ≤ ‖v₀‖ ^ 2 + B * ‖u₀‖ ^ 2 at hinit
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
    _ ≤ (1 + 1 / α) * (Real.exp (c * T) * ((1 + B) * D)) := by gcongr
    _ = _ := by dsimp [B,D]; ring


open HyperbolicWeakEnergyExistence.FiniteEnergy

/-- The exact energy identity gives the shifted energy Gronwall estimate with
any common, explicitly supplied bound on its scalar right hand side. -/
theorem shifted_energy_gronwall_of_rhs (j : HilbertTriple V H) (T : ℝ) (hT : 0 ≤ T)
    (a : ℝ → Form V) (α C : ℝ) (ha : FormHypotheses j T a α C)
    (c : ℝ) (hc : 0 ≤ c)
    (hbound : ∀ t ∈ Set.Icc 0 T, ∀ (x : V) (y h : H),
      2 * inner ℝ h y + derivWithin (fun r => a r x x) (Set.Icc 0 T) t +
        2 * C * inner ℝ (j.embedding x) y ≤
          c * shiftedEnergy j a C t x y + ‖h‖ ^ 2)
    (u₀ : V) (v₀ : H) (f : timeLpValue H 2 T)
    (z : WeakEnergySolution j T a u₀ v₀ f) :
    ∀ t ∈ Set.Icc 0 T,
      shiftedEnergy j a C t (z.displacement t) (z.velocity t) ≤
        Real.exp (c * t) *
          (shiftedEnergy j a C 0 u₀ v₀ + ∫ r in 0..t, ‖f r‖ ^ 2) := by
  by_cases hzero : T = 0
  · subst T
    intro t ht
    have ht0 : t = 0 := le_antisymm ht.2 ht.1
    subst t
    simp [z.initial_displacement, z.initial_velocity]
  have hpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hzero)
  have h0 : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, hT⟩
  have hTT : T ∈ Set.Icc 0 T := ⟨hT, le_rfl⟩
  obtain ⟨hx, hy⟩ := strong_state_continuity j T hT a α C ha u₀ v₀ f z
  have hEI := energy_identity j T hT a α C ha u₀ v₀ f z
  let E : ℝ → ℝ := SymmetricHyperbolicSpec.energy a z.displacement z.velocity
  let R : ℝ → ℝ := fun r =>
    2 * inner ℝ (f r) (z.velocity r) + formPower T a z.displacement r
  have hRi : IntervalIntegrable R volume 0 T :=
    ((hEI 0 h0 T hTT).1.const_mul 2).add (hEI 0 h0 T hTT).2.1
  have hEinc : ∀ t ∈ Set.Icc 0 T, E t - E 0 = ∫ r in 0..t, R r := by
    intro t ht
    obtain ⟨hfi, hpi, hei⟩ := hEI 0 h0 t ht
    simpa only [R, intervalIntegral.integral_add (hfi.const_mul 2) hpi,
      intervalIntegral.integral_const_mul] using hei
  have hEac : AbsolutelyContinuousOnInterval E 0 T :=
    primitive_increment_ac hRi (by simpa only [Set.uIcc_of_le hT] using hEinc)
  have hdE := primitive_increment_ae_deriv hT hRi hEinc
  obtain ⟨_, _, hu, _⟩ := primitive_representatives j T hpos a u₀ v₀ f z
  let X : ℝ → H := fun t => j.embedding (z.displacement t)
  have hyi : IntervalIntegrable z.velocity volume 0 T :=
    hy.intervalIntegrable_of_Icc hT
  have hXinc : ∀ t ∈ Set.Icc 0 T, X t - X 0 = ∫ r in 0..t, z.velocity r :=
    fun t ht => hu ⟨0, h0⟩ ⟨t, ht⟩
  have hXac : AbsolutelyContinuousOnInterval X 0 T :=
    primitive_increment_ac hyi (by simpa only [Set.uIcc_of_le hT] using hXinc)
  have hdX := primitive_increment_ae_deriv hT hyi hXinc
  have hnX := lipschitzWith_one_norm.comp_absolutelyContinuousOnInterval hXac
  have hsqX : AbsolutelyContinuousOnInterval (fun t => ‖X t‖ ^ 2) 0 T := by
    simpa only [sq, Function.comp_apply] using hnX.fun_mul hnX
  let Q : ℝ → ℝ := fun t => E t + C * ‖X t‖ ^ 2
  have hQac : AbsolutelyContinuousOnInterval Q 0 T := hEac.add (hsqX.const_mul C)
  have hQeq (t : ℝ) : Q t = shiftedEnergy j a C t (z.displacement t) (z.velocity t) := by
    rw [shiftedEnergy_eq]
    rfl
  let D : ℝ → ℝ := fun t => R t + 2 * C * inner ℝ (X t) (z.velocity t)
  have hD : ∀ᵐ t ∂volume, t ∈ Set.Icc 0 T →
      HasDerivAt Q (D t) t ∧ D t ≤ c * Q t + ‖f t‖ ^ 2 := by
    filter_upwards [hdE, hdX] with t hEt hXt ht
    constructor
    · convert (hEt ht).add ((hXt ht).norm_sq.const_mul C) using 1
      dsimp [Q, D]
      ring
    · rw [hQeq]
      exact hbound t ht (z.displacement t) (z.velocity t) (f t)
  have hgi : IntervalIntegrable (fun t => ‖f t‖ ^ 2) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hT).mpr (Lp.memLp f).norm.integrable_sq
  have hgron := ac_gronwall hT hc hQac hgi
    (Eventually.of_forall fun t ht => sq_nonneg ‖f t‖) hD
  intro t ht
  simpa only [hQeq, z.initial_displacement, z.initial_velocity] using hgron t ht


/-- A single constant works for every form family sharing the fixed embedding,
time horizon, Gårding parameters and common magnitude/derivative bound.
The solution retains the exact energy identity and weak-class uniqueness. -/
theorem uniform_symmetric_hyperbolic_equation :
    UniformSymmetricHyperbolicEquation (V := V) (H := H) := by
  intro j T hT α C M hα hC hM
  let c : ℝ := 1 + C + (M + C * ‖j.embedding‖ ^ 2) / α
  have hc : 0 ≤ c := by dsimp [c]; positivity
  let K : ℝ := (1 + 1 / α) * Real.exp (c * T) * (1 + M + C * ‖j.embedding‖ ^ 2)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro a ha hb u₀ v₀ f
  obtain ⟨_, _, hz⟩ := well_posedness j T hT a α C ha
  obtain ⟨z, hstate, _, hunique⟩ := hz u₀ v₀ f
  refine ⟨z, hstate, energy_identity j T hT a α C ha u₀ v₀ f z, ?_, hunique⟩
  have henergy := shifted_energy_gronwall_of_rhs j T hT a α C ha c hc
    (fun t ht x y h => uniform_energy_rhs_bound j T a α C M ha hM hb ht x y h)
    u₀ v₀ f z
  intro t ht
  exact uniform_state_bound_of_gronwall j T hT a α C M ha hM hb c hc
    u₀ v₀ f z.displacement z.velocity henergy ht

end ExpandedFA.Evolution.SymmetricHyperbolicEquation
