import MathGenome.Internal.LinearPDE.P201Specs.Heat.ParabolicForms
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Evolution.ParabolicForms

import MathGenome.Internal.LinearPDE.P201.Common.TimeTrace
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
universe u v

namespace P201.Heat.ParabolicForms
open ExpandedFA.Evolution
open HilbertTripleSpec HilbertTripleTraceSpec ParabolicGalerkinSpec ParabolicGalerkin
open P201Specs.Heat.ParabolicForms

section Solutions
variable {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Evaluation of a strongly measurable dual trajectory supplies the scalar
measurability required by the pinned theorem. -/
theorem form_hypotheses {j : HilbertTriple V H} {T : ℝ}
    {a : BilinearForms V} {M α c₀ : ℝ} (hα : 0 < α)
    (ha : FormAssumptions j T a M α c₀) : FormHypotheses j T a M α c₀ := by
  refine ⟨hα, ?_, ha.bounds, ha.strong_measurable⟩
  intro x y
  have hm := (ContinuousLinearMap.apply ℝ ℝ y).continuous.comp_aestronglyMeasurable
    (ha.strong_measurable x)
  apply hm.aemeasurable.congr
  filter_upwards [ha.bounds] with t ht
  exact formOperator_apply a M t ht.1 x y

/-- The supplied trace assumption identifies the solution curve and yields
its energy identity at every pair of times. -/
theorem solution_energy_rule
    (htrace : P201Specs.Common.TimeTrace.TimeTraceTheorem.{u,v})
    {j : HilbertTriple V H} {T : ℝ} (hT : 0 < T)
    {a : BilinearForms V} {M : ℝ}
    {f : timeLpValue (StrongDual ℝ V) 2 T} {u₀ : H}
    (z : WeakSolution j T hT.le a M f u₀) :
    ∀ s t : Set.Icc 0 T,
      ‖z.curve t‖ ^ 2 - ‖z.curve s‖ ^ 2 =
        2 * ∫ r in s.val..t.val, z.derivative r (z.value r) := by
  obtain ⟨tr, _, huniq, _, he, _⟩ := htrace j T hT
  let q : energySpaceValue j T := ⟨(z.value, z.derivative), z.has_derivative⟩
  have hc := huniq q z.curve z.represents
  intro s t
  simpa only [← hc, q, energyDensity] using (he q s t).2

/-- A Bochner-integrable function remains interval integrable at the endpoints. -/
theorem time_interval_integrable {q : ℝ → ℝ} {T : ℝ}
    (hq : Integrable q (timeMeasureValue T)) (s t : Set.Icc 0 T) :
    IntervalIntegrable q volume s.val t.val := by
  have hi : IntegrableOn q (Set.Icc 0 T) := by
    simpa only [IntegrableOn, timeMeasureValue, restrict_Ioo_eq_restrict_Icc] using hq
  exact (hi.mono_set (Set.uIcc_subset_Icc s.property t.property)).intervalIntegrable

/-- The equation and trace energy rule give the original exact form identity. -/
theorem solution_energy_identity
    (htrace : P201Specs.Common.TimeTrace.TimeTraceTheorem.{u,v})
    {j : HilbertTriple V H} {T : ℝ} (hT : 0 < T)
    {a : BilinearForms V} {M α c₀ : ℝ} (ha : FormHypotheses j T a M α c₀)
    {f : timeLpValue (StrongDual ℝ V) 2 T} {u₀ : H}
    (z : WeakSolution j T hT.le a M f u₀) : EnergyIdentity z := by
  obtain ⟨L, _, hL⟩ := operator_action T a M
    (ha.bounds.mono fun _ ht => ht.1) ha.strong_measurable
  have hform : (fun s => (L z.value) s (z.value s)) =ᵐ[timeMeasureValue T]
      fun s => a s (z.value s) (z.value s) := by
    filter_upwards [hL z.value, ha.bounds] with s hs hb
    rw [hs, formOperator_apply a M s hb.1]
  have hfi : Integrable (fun s => a s (z.value s) (z.value s))
      (timeMeasureValue T) := (triple_pairing_integrable T z.value (L z.value)).congr hform
  have hrhs : (fun s => z.derivative s (z.value s)) =ᵐ[timeMeasureValue T]
      fun s => f s (z.value s) - a s (z.value s) (z.value s) := by
    filter_upwards [z.equation, ha.bounds] with s hs hb
    rw [hs, sub_apply, formOperator_apply a M s hb.1]
  intro t
  let s : Set.Icc 0 T := ⟨0, by simp [hT.le]⟩
  have hai := time_interval_integrable hfi s t
  have hffi := triple_pairing_intervalIntegrable T z.value f s t
  change IntervalIntegrable (fun r => f r (z.value r)) volume s.val t.val at hffi
  have he := solution_energy_rule htrace hT z s t
  have hint := time_integral_congr_ae T hrhs s t
  change (∫ r in 0..t.val, z.derivative r (z.value r)) = _ at hint
  rw [hint, intervalIntegral.integral_sub hffi hai] at he
  have hz0 : z.curve s = u₀ := z.initial
  rw [hz0] at he
  refine ⟨hai, hffi, ?_⟩
  dsimp only [s] at he
  linarith

/-- The derivative bound uses the bounded multiplication map on L², without
any operator-norm measurability assumption. -/
theorem solution_derivative_norm
    {j : HilbertTriple V H} {T : ℝ} {hT : 0 ≤ T}
    {a : BilinearForms V} {M α c₀ : ℝ} (ha : FormHypotheses j T a M α c₀)
    {f : timeLpValue (StrongDual ℝ V) 2 T} {u₀ : H}
    (z : WeakSolution j T hT a M f u₀) :
    ‖z.derivative‖ ≤ ‖f‖ + max M 0 * ‖z.value‖ := by
  obtain ⟨L, hLn, hL⟩ := operator_action T a M
    (ha.bounds.mono fun _ ht => ht.1) ha.strong_measurable
  have hz : z.derivative = f - L z.value := by
    apply Lp.ext
    filter_upwards [z.equation, hL z.value, Lp.coeFn_sub f (L z.value)] with t he hl hs
    simp only [hs, Pi.sub_apply, he, hl]
  rw [hz]
  exact (norm_sub_le _ _).trans (add_le_add le_rfl
    ((L.le_opNorm z.value).trans
      (mul_le_mul_of_nonneg_right hLn (norm_nonneg z.value))))

/-- A completely explicit coefficient depending only on the source parameters. -/
def energyConstant (T M α c₀ : ℝ) : ℝ :=
  let Q := 1 + α⁻¹
  let B := Real.exp (2 * max c₀ 0 * T)
  let U := (1 + 2 * max c₀ 0 * T * B) / α
  Q * B + Q * U + 2 + 2 * (max M 0) ^ 2 * (Q * U)

theorem energyConstant_nonneg {T M α c₀ : ℝ} (hT : 0 ≤ T) (hα : 0 < α) :
    0 ≤ energyConstant T M α c₀ := by
  dsimp [energyConstant]
  positivity

/-- Squared estimate with a coefficient uniform even over the embedding.
The first two bounds come directly from the integrated energy inequality;
the third follows from u' = f - Au in the original dual norm. -/
theorem solution_squared_estimate
    (htrace : P201Specs.Common.TimeTrace.TimeTraceTheorem.{u,v})
    {j : HilbertTriple V H} {T : ℝ} (hT : 0 < T)
    {a : BilinearForms V} {M α c₀ : ℝ} (ha : FormHypotheses j T a M α c₀)
    {f : timeLpValue (StrongDual ℝ V) 2 T} {u₀ : H}
    (z : WeakSolution j T hT.le a M f u₀) :
    ‖z.curve‖ ^ 2 + ‖z.value‖ ^ 2 + ‖z.derivative‖ ^ 2 ≤
      energyConstant T M α c₀ * (‖u₀‖ ^ 2 + ‖f‖ ^ 2) := by
  let Q := 1 + α⁻¹
  let B := Real.exp (2 * max c₀ 0 * T)
  let U := (1 + 2 * max c₀ 0 * T * B) / α
  let D := ‖u₀‖ ^ 2 + α⁻¹ * ‖f‖ ^ 2
  let S := ‖u₀‖ ^ 2 + ‖f‖ ^ 2
  let m := max M 0
  have hα := ha.alpha_pos
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hB : 0 ≤ B := (Real.exp_pos _).le
  have hU : 0 ≤ U := by dsimp [U, B]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hm : 0 ≤ m := le_max_right M 0
  have hDS : D ≤ Q * S := by
    dsimp [D, Q, S]
    nlinarith [mul_nonneg (inv_nonneg.mpr hα.le) (sq_nonneg ‖u₀‖), sq_nonneg ‖f‖]
  obtain ⟨hcsq, husq⟩ := parabolic_energy_sq_bounds j T hT.le a M α c₀ ha
    z.value f z.derivative z.curve u₀ z.represents (by rw [z.initial])
    z.equation (solution_energy_rule htrace hT z)
  have hcsq' : ∀ t, ‖z.curve t‖ ^ 2 ≤ D * B := hcsq
  have hcbroot : ‖z.curve‖ ≤ Real.sqrt (D * B) := by
    apply (ContinuousMap.norm_le z.curve (Real.sqrt_nonneg _)).mpr
    intro t
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (mul_nonneg hD hB)]
    exact hcsq' t
  have hcb : ‖z.curve‖ ^ 2 ≤ (Q * B) * S := by
    calc
      ‖z.curve‖ ^ 2 ≤ (Real.sqrt (D * B)) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mpr hcbroot
      _ = D * B := Real.sq_sqrt (mul_nonneg hD hB)
      _ ≤ (Q * S) * B := mul_le_mul_of_nonneg_right hDS hB
      _ = (Q * B) * S := by ring
  have hub : ‖z.value‖ ^ 2 ≤ (Q * U) * S := by
    have huD : ‖z.value‖ ^ 2 ≤ D * U := by
      apply (mul_le_mul_iff_right₀ hα).mp
      calc
        α * ‖z.value‖ ^ 2 ≤ D * (1 + 2 * max c₀ 0 * T * B) := husq
        _ = α * (D * U) := by dsimp [U]; field_simp
    calc
      ‖z.value‖ ^ 2 ≤ D * U := huD
      _ ≤ (Q * S) * U := mul_le_mul_of_nonneg_right hDS hU
      _ = (Q * U) * S := by ring
  have hgn := solution_derivative_norm ha z
  have hgnsq : ‖z.derivative‖ ^ 2 ≤ (‖f‖ + m * ‖z.value‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hgn
  have hgsq : ‖z.derivative‖ ^ 2 ≤
      2 * ‖f‖ ^ 2 + 2 * m ^ 2 * ‖z.value‖ ^ 2 := by
    nlinarith [sq_nonneg (‖f‖ - m * ‖z.value‖)]
  have hgfinal : ‖z.derivative‖ ^ 2 ≤
      (2 + 2 * m ^ 2 * (Q * U)) * S := by
    have hff : ‖f‖ ^ 2 ≤ S := by dsimp [S]; nlinarith [sq_nonneg ‖u₀‖]
    have hmul := mul_le_mul_of_nonneg_left hub (by positivity : 0 ≤ 2 * m ^ 2)
    nlinarith
  change _ ≤ (Q * B + Q * U + 2 + 2 * m ^ 2 * (Q * U)) * S
  nlinarith

end Solutions
end P201.Heat.ParabolicForms

namespace P201.Heat.ParabolicForms
open ExpandedFA.Evolution
open HilbertTripleSpec ParabolicGalerkinSpec
open P201Specs.Heat.ParabolicForms

/-- General form theorem, conditional only on the full original time-trace
proposition; the original target itself is deliberately not declared. -/
theorem general_conditional
    (htrace : P201Specs.Common.TimeTrace.TimeTraceTheorem.{u,v}) :
    GeneralTheorem.{u,v} := by
  intro T M α c₀ hT hα _hc₀
  refine ⟨energyConstant T M α c₀, energyConstant_nonneg hT.le hα, ?_⟩
  intro V H _ _ _ _ _ _ j a ha f u₀
  have hform := form_hypotheses hα ha
  obtain ⟨_, _, hex⟩ := ExpandedFA.Evolution.ParabolicForms.parabolic_wellposedness
    j T hT.le M α c₀
  obtain ⟨z, _, huniq⟩ := hex a hform f u₀
  exact ⟨z, solution_energy_identity htrace hT hform z,
    solution_squared_estimate htrace hT hform z, huniq⟩

/-- Taking the constant form trajectory and zero Gårding shift gives the
bounded coercive autonomous case, with no extra measurability condition. -/
theorem autonomous_of_general (hgeneral : GeneralTheorem.{u,v}) :
    AutonomousTheorem.{u,v} := by
  intro T M α hT hα
  obtain ⟨K, hK, hex⟩ := hgeneral T M α 0 hT hα le_rfl
  refine ⟨K, hK, ?_⟩
  intro V H _ _ _ _ _ _ j a hbound hcoerc f u₀
  apply hex j (fun _ => a) _ f u₀
  refine ⟨?_, Eventually.of_forall fun t => ⟨hbound, ?_⟩⟩
  · intro x
    change AEStronglyMeasurable
      (fun _ : ℝ => formOperator (fun _ => a) M 0 x) (timeMeasureValue T)
    exact aestronglyMeasurable_const
  · intro x
    simpa only [zero_mul, sub_zero] using hcoerc x

/-- Conditional draft of the entire H05 theorem. The sole explicit premise
is exactly the ordered frozen C06 proposition, with both universe parameters.
A closed `parabolic_forms` wrapper awaits the real upstream proof. -/
theorem parabolic_forms_conditional
    (htrace : P201Specs.Common.TimeTrace.TimeTraceTheorem.{u,v}) :
    P201Specs.Heat.ParabolicForms.ParabolicFormsTheorem.{u,v} := by
  have hg := general_conditional htrace
  exact ⟨hg, autonomous_of_general hg,
    ExpandedFA.Evolution.ParabolicForms.separable_operator_measurability⟩

end P201.Heat.ParabolicForms

universe v8_closure_50ee329204533aaa_u0 v8_closure_50ee329204533aaa_u1
theorem _root_.«P201».«Heat».«ParabolicForms».«parabolic_forms» : _root_.«P201Specs».«Heat».«ParabolicForms».«ParabolicFormsTheorem».{v8_closure_50ee329204533aaa_u0, v8_closure_50ee329204533aaa_u1} :=
  @_root_.«P201».«Heat».«ParabolicForms».«parabolic_forms_conditional».{v8_closure_50ee329204533aaa_u0, v8_closure_50ee329204533aaa_u1} (@_root_.«P201».«Common».«TimeTrace».«time_trace».{v8_closure_50ee329204533aaa_u0, v8_closure_50ee329204533aaa_u1})
