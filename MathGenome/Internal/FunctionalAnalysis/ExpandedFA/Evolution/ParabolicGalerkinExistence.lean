import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.ContinuousMap.Interval
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Evolution.ParabolicGalerkinExistence
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Evolution.HilbertTripleTrace
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.ProjIcc
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support

/-! Nonautonomous Galerkin existence on a dense real Hilbert triple. The proofs
use strong measurability in the strong operator topology, not in operator
norm. They therefore apply to the nonseparable spaces of the source. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
universe u v w

namespace ExpandedFA.Evolution
namespace ParabolicGalerkin

open ParabolicGalerkinSpec

section OperatorMeasurability
variable {X : Type w} [MeasurableSpace X] {μ : Measure X}
  {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Strong-operator measurable families act measurably on strongly measurable
vectors. No separability or operator-norm measurability is used. -/
theorem aestronglyMeasurable_apply_of_strong_operator
    (A : X → E →L[ℝ] F)
    (hA : ∀ x, AEStronglyMeasurable (fun t => A t x) μ)
    {z : X → E} (hz : AEStronglyMeasurable z μ) :
    AEStronglyMeasurable (fun t => A t (z t)) μ := by
  classical
  have hs (s : SimpleFunc X E) : AEStronglyMeasurable (fun t => A t (s t)) μ := by
    induction s with
    | const c => exact hA c
    | @pcw f g s hs hf hg =>
      have hh := AEStronglyMeasurable.piecewise hs.nullMeasurableSet hf.restrict hg.restrict
      convert hh using 1
      funext t
      by_cases ht : t ∈ s <;> simp [SimpleFunc.coe_piecewise, ht]
  have hlim : AEStronglyMeasurable (fun t => A t (hz.mk z t)) μ := by
    apply aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => hs (hz.stronglyMeasurable_mk.approx n))
    exact Eventually.of_forall fun t =>
      (A t).continuous.continuousAt.tendsto.comp
        (hz.stronglyMeasurable_mk.tendsto_approx t)
  exact hlim.congr (hz.ae_eq_mk.symm.mono fun t ht => congrArg (A t) ht)

/-- The induced action on any Lᵖ space, including p=∞. The uniform bound is
only a.e.; all finite-simple-function approximation happens in the vector
variable. -/
theorem memLp_apply_of_strong_operator (A : X → E →L[ℝ] F)
    (hA : ∀ x, AEStronglyMeasurable (fun t => A t x) μ)
    {B : ℝ} (hB : ∀ᵐ t ∂μ, ‖A t‖ ≤ B)
    {p : ℝ≥0∞} {z : X → E} (hz : MemLp z p μ) :
    MemLp (fun t => A t (z t)) p μ := by
  apply hz.of_le_mul (aestronglyMeasurable_apply_of_strong_operator A hA
    hz.aestronglyMeasurable)
  exact hB.mono fun t ht => (A t).le_of_opNorm_le ht _

/-- The bounded time-multiplication map on the quotient, with its a.e.
representative and the exact operator bound. -/
theorem exists_lp_operator_of_strong_operator (A : X → E →L[ℝ] F)
    (hA : ∀ x, AEStronglyMeasurable (fun t => A t x) μ)
    {B : ℝ} (hB₀ : 0 ≤ B) (hB : ∀ᵐ t ∂μ, ‖A t‖ ≤ B)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ∃ L : Lp E p μ →L[ℝ] Lp F p μ, ‖L‖ ≤ B ∧
      ∀ z, (L z : X → F) =ᵐ[μ] fun t => A t (z t) := by
  let hz (z : Lp E p μ) := memLp_apply_of_strong_operator A hA hB (Lp.memLp z)
  let L₀ : Lp E p μ →ₗ[ℝ] Lp F p μ :=
    { toFun := fun z => (hz z).toLp (fun t => A t (z t))
      map_add' := by
        intro x y
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (hz (x + y)), MemLp.coeFn_toLp (hz x),
          MemLp.coeFn_toLp (hz y), Lp.coeFn_add x y,
          Lp.coeFn_add ((hz x).toLp _) ((hz y).toLp _)] with t hxy hx hy hsum hsum'
        simpa only [hxy, hsum, hsum', Pi.add_apply, hx, hy] using (A t).map_add (x t) (y t)
      map_smul' := by
        intro c x
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (hz (c • x)), MemLp.coeFn_toLp (hz x),
          Lp.coeFn_smul c x, Lp.coeFn_smul c ((hz x).toLp _)] with t hcx hx hs hs'
        simp only [RingHom.id_apply]
        simpa only [hcx, hs, hs', Pi.smul_apply, hx] using (A t).map_smul c (x t) }
  have hL (z : Lp E p μ) : ‖L₀ z‖ ≤ B * ‖z‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [MemLp.coeFn_toLp (hz z), hB] with t ht hb
    change ‖((hz z).toLp _ : X → F) t‖ ≤ _
    rw [ht]
    exact (A t).le_of_opNorm_le hb _
  refine ⟨L₀.mkContinuous B hL, L₀.mkContinuous_norm_le hB₀ hL, ?_⟩
  intro z
  exact MemLp.coeFn_toLp (hz z)

end OperatorMeasurability

section WeakCompactness
variable {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [CompleteSpace X] {I : Type w} {l : Filter I} [l.NeBot]

/-- A bounded Hilbert-space net has a weakly convergent refining filter.
The limit stays in the same closed ball. There is no countability condition
on either the Hilbert space or the original filter. -/
theorem exists_weak_limit_of_eventually_norm_le (z : I → X) (R : ℝ)
    (hz : ∀ᶠ i in l, ‖z i‖ ≤ R) :
    ∃ x : X, ‖x‖ ≤ R ∧ ∃ F : Filter I, F.NeBot ∧ F ≤ l ∧
      ∀ ℓ : StrongDual ℝ X, Tendsto (fun i => ℓ (z i)) F (𝓝 (ℓ x)) := by
  let d : I → WeakDual ℝ X := fun i =>
    StrongDual.toWeakDual (InnerProductSpace.toDual ℝ X (z i))
  have hb : ∀ᶠ i in l,
      d i ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ X) R := by
    filter_upwards [hz] with i hi
    simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, d,
      StrongDual.toStrongDual_toWeakDual, LinearIsometryEquiv.norm_map] using hi
  obtain ⟨q, hq, hcluster⟩ :=
    (WeakDual.isCompact_closedBall (0 : StrongDual ℝ X) R).exists_mapClusterPt_of_frequently
      hb.frequently
  obtain ⟨F, hFl, hF⟩ := mapClusterPt_iff_ultrafilter.mp hcluster
  let x : X := (InnerProductSpace.toDual ℝ X).symm q.toStrongDual
  refine ⟨x, ?_, F, inferInstance, hFl, ?_⟩
  · simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right,
      ← LinearIsometryEquiv.norm_map (InnerProductSpace.toDual ℝ X).symm] using hq
  · intro ℓ
    let y : X := (InnerProductSpace.toDual ℝ X).symm ℓ
    have hp := ((WeakDual.eval_continuous y).tendsto q).comp hF
    have hd (i : I) : d i y = ℓ (z i) := by
      change inner ℝ (z i) y = _
      rw [real_inner_comm]
      exact InnerProductSpace.toDual_symm_apply
    have hxy : q y = ℓ x := by
      change q.toStrongDual y = _
      calc
        q.toStrongDual y = inner ℝ x y :=
          (InnerProductSpace.toDual_symm_apply (x := y) (y := q.toStrongDual)).symm
        _ = inner ℝ y x := real_inner_comm _ _
        _ = ℓ x := InnerProductSpace.toDual_symm_apply
    change Tendsto (fun i => d i y) _ (𝓝 (q y)) at hp
    simpa only [hd, hxy] using hp

end WeakCompactness

/-- Integral Gronwall with a dissipative term. The comparison primitive is
C¹ even when the dissipative term is merely integrable. -/
private theorem integrated_energy_bound_continuous
    (T α β D : ℝ) (h k : ℝ → ℝ) (hT : 0 ≤ T) (hα : 0 < α)
    (hβ : 0 ≤ β) (hD : 0 ≤ D) (hc : Continuous h)
    (hh : ∀ t ∈ Set.Icc 0 T, 0 ≤ h t)
    (_hk : IntervalIntegrable k volume 0 T)
    (hk₀ : ∀ t ∈ Set.Icc 0 T, 0 ≤ k t)
    (he : ∀ t ∈ Set.Icc 0 T,
      h t + α * (∫ r in 0..t, k r) ≤ D + β * (∫ r in 0..t, h r)) :
    (∀ t ∈ Set.Icc 0 T, h t ≤ D * Real.exp (β * T)) ∧
      α * (∫ r in 0..T, k r) ≤ D * (1 + β * T * Real.exp (β * T)) := by
  let P : ℝ → ℝ := fun t => D + β * ∫ r in 0..t, h r
  have hle (t : ℝ) (ht : t ∈ Set.Icc 0 T) : h t ≤ P t := by
    have hki : 0 ≤ ∫ r in 0..t, k r :=
      intervalIntegral.integral_nonneg ht.1 (fun r hr => hk₀ r ⟨hr.1, hr.2.trans ht.2⟩)
    have ha := mul_nonneg hα.le hki
    exact (le_add_of_nonneg_right ha).trans (he t ht)
  have hP₀ (t : ℝ) (ht : t ∈ Set.Icc 0 T) : 0 ≤ P t :=
    (hh t ht).trans (hle t ht)
  have hPc : Continuous P := continuous_const.add
    (continuous_const.mul (intervalIntegral.continuous_primitive
      (fun a b => hc.intervalIntegrable a b) 0))
  have hPd (t : ℝ) : HasDerivAt P (β * h t) t := by
    simpa only [mul_one] using
      ((intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
        hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_mul β).const_add D
  have hPb (t : ℝ) (ht : t ∈ Set.Ico 0 T) : ‖β * h t‖ ≤ β * ‖P t‖ + 0 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hβ (hh t ⟨ht.1, ht.2.le⟩)),
      Real.norm_eq_abs, abs_of_nonneg (hP₀ t ⟨ht.1, ht.2.le⟩), add_zero]
    exact mul_le_mul_of_nonneg_left (hle t ⟨ht.1, ht.2.le⟩) hβ
  have hb (t : ℝ) (ht : t ∈ Set.Icc 0 T) : h t ≤ D * Real.exp (β * T) := by
    have hg := norm_le_gronwallBound_of_norm_deriv_right_le hPc.continuousOn
      (fun t _ => (hPd t).hasDerivWithinAt) (δ := D) (by simp [P, abs_of_nonneg hD]) hPb t ht
    rw [gronwallBound_ε0, sub_zero, Real.norm_eq_abs, abs_of_nonneg (hP₀ t ht)] at hg
    exact (hle t ht).trans (hg.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hβ)) hD))
  refine ⟨hb, ?_⟩
  have hi : (∫ r in 0..T, h r) ≤ T * (D * Real.exp (β * T)) := by
    have hp := intervalIntegral.integral_mono_on hT (hc.intervalIntegrable 0 T)
      (intervalIntegrable_const (μ := volume) (c := D * Real.exp (β * T))) hb
    simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] using hp
  have heT := he T ⟨hT, le_rfl⟩
  have hhT := hh T ⟨hT, le_rfl⟩
  nlinarith [mul_le_mul_of_nonneg_left hi hβ]

/-- Closed-interval form of the scalar integrated energy estimate. -/
theorem integrated_energy_bound
    (T α β D : ℝ) (h k : ℝ → ℝ) (hT : 0 ≤ T) (hα : 0 < α)
    (hβ : 0 ≤ β) (hD : 0 ≤ D) (hc : ContinuousOn h (Set.Icc 0 T))
    (hh : ∀ t ∈ Set.Icc 0 T, 0 ≤ h t)
    (hk : IntervalIntegrable k volume 0 T)
    (hk₀ : ∀ t ∈ Set.Icc 0 T, 0 ≤ k t)
    (he : ∀ t ∈ Set.Icc 0 T,
      h t + α * (∫ r in 0..t, k r) ≤ D + β * (∫ r in 0..t, h r)) :
    (∀ t ∈ Set.Icc 0 T, h t ≤ D * Real.exp (β * T)) ∧
      α * (∫ r in 0..T, k r) ≤ D * (1 + β * T * Real.exp (β * T)) := by
  let H : ℝ → ℝ := fun t => h (Set.projIcc 0 T hT t)
  have hHc : Continuous H := hc.comp_continuous
    (continuous_subtype_val.comp continuous_projIcc) (fun _ => (Set.projIcc 0 T hT _).property)
  have hH (t : ℝ) (ht : t ∈ Set.Icc 0 T) : H t = h t := by
    simp only [H, Set.projIcc_of_mem hT ht]
  have hint (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
      (∫ r in 0..t, H r) = ∫ r in 0..t, h r := by
    apply intervalIntegral.integral_congr
    rw [Set.uIcc_of_le ht.1]
    intro r hr
    exact hH r ⟨hr.1, hr.2.trans ht.2⟩
  have hb := integrated_energy_bound_continuous T α β D H k hT hα hβ hD hHc
    (fun t ht => by rw [hH t ht]; exact hh t ht) hk hk₀
    (fun t ht => by rw [hH t ht, hint t ht]; exact he t ht)
  exact ⟨fun t ht => by rw [← hH t ht]; exact hb.1 t ht, hb.2⟩


section ScalarFunctionalGeneralSupport
open HilbertTripleSpec
section ScalarFunctionalGeneral
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem scalar_time_test_functional_of_memLp (T : ℝ) (ψ : ℝ → ℝ)
    (hmem : MemLp ψ 2 (timeMeasureValue T)) (e : StrongDual ℝ E) :
    ∃ F : StrongDual ℝ (timeLpValue E 2 T), ∀ z,
      F z = ∫ t, ψ t * e (z t) ∂timeMeasureValue T := by
  let q := hmem.toLp ψ
  let B : E →L[ℝ] ℝ →L[ℝ] ℝ := (ContinuousLinearMap.mul ℝ ℝ).comp e
  let P := B.lpPairing (timeMeasureValue T) 2 2
  refine ⟨P.flip q, ?_⟩
  intro z
  change P z q = _
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp hmem] with t ht
  change e (z t) * q t = _
  rw [ht, mul_comm]

theorem memLp_time_of_continuousOn (T : ℝ) {ψ : ℝ → ℝ}
    (hψ : ContinuousOn ψ (Set.Icc 0 T)) : MemLp ψ 2 (timeMeasureValue T) := by
  let : IsFiniteMeasure (timeMeasureValue T) := ⟨by simp [timeMeasureValue, Real.volume_Ioo]⟩
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hψ.norm
  apply MemLp.of_bound ((hψ.mono Set.Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo) C
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact hC ⟨t, Set.Ioo_subset_Icc_self ht, rfl⟩

theorem scalar_time_test_functional_of_continuousOn (T : ℝ) (ψ : ℝ → ℝ)
    (hψ : ContinuousOn ψ (Set.Icc 0 T)) (e : StrongDual ℝ E) :
    ∃ F : StrongDual ℝ (timeLpValue E 2 T), ∀ z,
      F z = ∫ t, ψ t * e (z t) ∂timeMeasureValue T :=
  scalar_time_test_functional_of_memLp T ψ (memLp_time_of_continuousOn T hψ) e
end ScalarFunctionalGeneral
end ScalarFunctionalGeneralSupport

section WeakEquationSupport
open HilbertTripleSpec

section ScalarFunctional
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem scalar_time_test_functional (T : ℝ) (ψ : ℝ → ℝ)
    (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) (e : StrongDual ℝ E) :
    ∃ F : StrongDual ℝ (timeLpValue E 2 T), ∀ z,
      F z = ∫ t, ψ t * e (z t) ∂timeMeasureValue T := by
  let : IsLocallyFiniteMeasure (timeMeasureValue T) := by
    dsimp [timeMeasureValue]
    infer_instance
  have hmem : MemLp ψ 2 (timeMeasureValue T) := hψ.memLp_of_hasCompactSupport hcψ
  let q := hmem.toLp ψ
  let B : E →L[ℝ] ℝ →L[ℝ] ℝ := (ContinuousLinearMap.mul ℝ ℝ).comp e
  let P := B.lpPairing (timeMeasureValue T) 2 2
  refine ⟨P.flip q, ?_⟩
  intro z
  change P z q = _
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp hmem] with t ht
  change e (z t) * q t = _
  rw [ht, mul_comm]

end ScalarFunctional

section WeakEquation
variable {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem tripleDerivative_of_weak_limit {I : Type w} {l : Filter I} [l.NeBot]
    (j : HilbertTriple V H) (T : ℝ)
    (L : timeLpValue V 2 T →L[ℝ] timeLpValue (StrongDual ℝ V) 2 T)
    (f : timeLpValue (StrongDual ℝ V) 2 T)
    (z : I → timeLpValue V 2 T) (u : timeLpValue V 2 T)
    (hz : ∀ e : StrongDual ℝ (timeLpValue V 2 T),
      Tendsto (fun i => e (z i)) l (𝓝 (e u)))
    (hid : ∀ (v : V) (φ : ℝ → ℝ), testValue T φ → ∀ᶠ i in l,
      (∫ t, deriv φ t * inner ℝ (j.embedding (z i t)) (j.embedding v)
          ∂timeMeasureValue T) +
        (∫ t, φ t * f t v ∂timeMeasureValue T) =
        ∫ t, φ t * L (z i) t v ∂timeMeasureValue T) :
    tripleDerivativeValue j T u (f - L u) := by
  let : IsLocallyFiniteMeasure (timeMeasureValue T) := by
    dsimp [timeMeasureValue]
    infer_instance
  have hdu : MemLp (fun t => intoDualValue j (u t)) 2 (timeMeasureValue T) :=
    (intoDualValue j).comp_memLp u
  have hglocal := (Lp.memLp (f - L u)).locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hdlocal := hdu.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  refine ⟨locallyIntegrableOn_of_locallyIntegrable_restrict hdlocal,
    locallyIntegrableOn_of_locallyIntegrable_restrict hglocal, ?_⟩
  intro φ hφ
  have hdφ : Continuous (deriv φ) := hφ.1.continuous_deriv (by simp)
  have hcdφ : HasCompactSupport (deriv φ) := hφ.2.1.deriv
  have hleft := hdlocal.integrable_smul_left_of_hasCompactSupport hdφ hcdφ
  have hright := hglocal.integrable_smul_left_of_hasCompactSupport hφ.1.continuous hφ.2.1
  apply ContinuousLinearMap.ext
  intro v
  rw [ContinuousLinearMap.integral_apply hleft, neg_apply,
    ContinuousLinearMap.integral_apply hright]
  simp only [smul_apply, smul_eq_mul]
  let e : StrongDual ℝ V := (ContinuousLinearMap.apply ℝ ℝ v).comp (intoDualValue j)
  have he (x : V) : e x = inner ℝ (j.embedding x) (j.embedding v) := by
    change inner ℝ (j.embedding.adjoint (j.embedding x)) v = _
    exact j.embedding.adjoint_inner_left v (j.embedding x)
  obtain ⟨Fd, hFd⟩ := scalar_time_test_functional T (deriv φ) hdφ hcdφ e
  obtain ⟨Fφ, hFφ⟩ := scalar_time_test_functional T φ hφ.1.continuous hφ.2.1
    (ContinuousLinearMap.apply ℝ ℝ v)
  have hconvleft := hz Fd
  have hconvright := hz (Fφ.comp L)
  simp only [hFd, he] at hconvleft
  change Tendsto (fun i => Fφ (L (z i))) l (𝓝 (Fφ (L u))) at hconvright
  simp only [hFφ] at hconvright
  have heq := tendsto_nhds_unique
    ((hconvleft.add tendsto_const_nhds).congr' (hid v φ hφ)) hconvright
  have hi (a : timeLpValue (StrongDual ℝ V) 2 T) :
      Integrable (fun t => φ t * a t v) (timeMeasureValue T) := by
    have hl := ((ContinuousLinearMap.apply ℝ ℝ v).comp_memLp a).locallyIntegrable
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    exact hl.integrable_smul_left_of_hasCompactSupport hφ.1.continuous hφ.2.1
  have hsub : (∫ t, φ t * (f - L u) t v ∂timeMeasureValue T) =
      (∫ t, φ t * f t v ∂timeMeasureValue T) -
        (∫ t, φ t * L u t v ∂timeMeasureValue T) := by
    rw [← integral_sub (hi f) (hi (L u))]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub f (L u)] with t ht
    simp only [ht, Pi.sub_apply, sub_apply, mul_sub]
  have hpair (x : V) : intoDualValue j x v =
      inner ℝ (j.embedding x) (j.embedding v) := he x
  simp only [hpair]
  rw [hsub, neg_sub]
  exact eq_sub_of_add_eq heq

end WeakEquation

end WeakEquationSupport

section MeasurableODE
open Set
open scoped NNReal Nat
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Picard existence for a bounded measurable linear equation on an arbitrary compact interval. -/
theorem exists_integral_curve {a b : ℝ} (hab : a ≤ b)
    (A : ℝ → E →L[ℝ] E) (f : ℝ → E) (K : ℝ≥0) (x : E)
    (hA : ∀ r ∈ Icc a b, ‖A r‖ ≤ K)
    (hInt : ∀ c : C(Icc a b, E),
      IntervalIntegrable (fun r => f r + A r (c (projIcc a b hab r))) volume a b) :
    ∃ c : C(Icc a b, E),
      c ⟨a, left_mem_Icc.mpr hab⟩ = x ∧
      ∀ s t : Icc a b, c t - c s =
        ∫ r in s.val..t.val, f r + A r (c (projIcc a b hab r)) := by
  let F : C(Icc a b, E) → C(Icc a b, E) := fun c =>
    ⟨fun t => x + ∫ r in a..t.val, f r + A r (c (projIcc a b hab r)), by
      apply continuous_const.add
      have hc : ContinuousOn (fun t : ℝ => ∫ r in a..t, f r + A r (c (projIcc a b hab r))) (Icc a b) := by
        simpa only [uIcc_of_le hab] using
          intervalIntegral.continuousOn_primitive_interval' (hInt c) left_mem_uIcc
      exact hc.comp_continuous continuous_subtype_val (fun t => t.property)⟩
  have hF_apply (c : C(Icc a b, E)) (t : Icc a b) :
      F c t = x + ∫ r in a..t.val, f r + A r (c (projIcc a b hab r)) := rfl
  have hct (c : C(Icc a b, E)) (t : Icc a b) : IntervalIntegrable
      (fun r => f r + A r (c (projIcc a b hab r))) volume a t.val :=
    (hInt c).mono_set (by simpa only [uIcc_of_le hab] using uIcc_subset_Icc (left_mem_Icc.mpr hab) t.property)
  have hiter (c d : C(Icc a b, E)) (n : ℕ) (t : Icc a b) :
      dist (F^[n] c t) (F^[n] d t) ≤
        ((K : ℝ) * |t.val - a|) ^ n / n ! * dist c d := by
    induction n generalizing t with
    | zero => simpa using ContinuousMap.dist_apply_le_dist (f := c) (g := d) t
    | succ n hn =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', dist_eq_norm,
        hF_apply, hF_apply, add_sub_add_left_eq_sub,
        ← intervalIntegral.integral_sub (hct _ t) (hct _ t)]
      calc
        _ ≤ ∫ r in uIoc a t.val,
            (K : ℝ) ^ (n + 1) * |r - a| ^ n / n ! * dist c d := by
          rw [intervalIntegral.norm_intervalIntegral_eq]
          apply MeasureTheory.norm_integral_le_of_norm_le
            (Continuous.integrableOn_uIoc (by fun_prop))
          apply (ae_restrict_mem measurableSet_Ioc).mono
          intro r hr
          have hr' : r ∈ Icc a b :=
            (uIcc_subset_Icc (left_mem_Icc.mpr hab) t.property) (uIoc_subset_uIcc hr)
          simp only [add_sub_add_left_eq_sub, ← map_sub]
          calc
            ‖A r (F^[n] c (projIcc a b hab r) - F^[n] d (projIcc a b hab r))‖ ≤
                (K : ℝ) * dist (F^[n] c (projIcc a b hab r)) (F^[n] d (projIcc a b hab r)) := by
              rw [dist_eq_norm]
              exact (A r).le_of_opNorm_le (hA r hr') _
            _ ≤ (K : ℝ) ^ (n + 1) * |r - a| ^ n / n ! * dist c d := by
              have hh := hn (projIcc a b hab r)
              have hproj : (projIcc a b hab r).val = r := by simp [projIcc, hr'.1, hr'.2]
              rw [hproj] at hh
              rw [pow_succ', mul_assoc, mul_div_assoc, mul_assoc]
              gcongr
              rwa [← mul_pow]
        _ ≤ ((K : ℝ) * |t.val - a|) ^ (n + 1) / (n + 1) ! * dist c d := by
          apply le_of_abs_le
          rw [← intervalIntegral.abs_intervalIntegral_eq, intervalIntegral.integral_mul_const,
            intervalIntegral.integral_div, intervalIntegral.integral_const_mul, abs_mul, abs_div,
            abs_mul, intervalIntegral.abs_intervalIntegral_eq, integral_pow_abs_sub_uIoc, abs_div,
            abs_pow, abs_pow, abs_dist, NNReal.abs_eq, abs_abs, mul_div, div_div, ← abs_mul,
            ← Nat.cast_succ, ← Nat.cast_mul, ← Nat.factorial_succ, Nat.abs_cast, ← mul_pow]
  obtain ⟨n, hn⟩ := FloorSemiring.tendsto_pow_div_factorial_atTop ((K : ℝ) * (b - a))
    |>.eventually (gt_mem_nhds zero_lt_one) |>.exists
  have hkn : 0 ≤ ((K : ℝ) * (b - a)) ^ n / n ! := by positivity
  let k : ℝ≥0 := ⟨((K : ℝ) * (b - a)) ^ n / n !, hkn⟩
  have hF : ContractingWith k F^[n] := by
    constructor
    · exact_mod_cast hn
    · apply LipschitzWith.of_dist_le_mul
      intro c d
      apply (ContinuousMap.dist_le (mul_nonneg k.coe_nonneg dist_nonneg)).mpr
      intro t
      apply (hiter c d n t).trans
      change ((K : ℝ) * |t.val - a|) ^ n / n ! * dist c d ≤
        ((K : ℝ) * (b - a)) ^ n / n ! * dist c d
      gcongr
      rw [abs_of_nonneg (sub_nonneg.mpr t.property.1)]
      exact sub_le_sub_right t.property.2 a
  let c := hF.fixedPoint F^[n]
  have hc : F c = c := hF.isFixedPt_fixedPoint_iterate
  have hcval (t : Icc a b) :
      c t = x + ∫ r in a..t.val, f r + A r (c (projIcc a b hab r)) :=
    (congrArg (fun z : C(Icc a b, E) => z t) hc).symm
  refine ⟨c, ?_, ?_⟩
  · rw [hcval]; simp
  · intro s t
    rw [hcval t, hcval s, add_sub_add_left_eq_sub]
    exact intervalIntegral.integral_interval_sub_left (hct c t) (hct c s)

/-- Global integral-equation existence under strong-operator measurability.
This does not require norm measurability of the operator family. -/
theorem exists_integral_curve_of_strong_operator {a b : ℝ} (hab : a ≤ b)
    (A : ℝ → E →L[ℝ] E) (f : ℝ → E) (K : ℝ≥0) (x : E)
    (hA : ∀ r ∈ Icc a b, ‖A r‖ ≤ K)
    (hAm : ∀ y, AEStronglyMeasurable (fun r => A r y) (volume.restrict (Icc a b)))
    (hf : IntervalIntegrable f volume a b) :
    ∃ c : C(Icc a b, E),
      c ⟨a, left_mem_Icc.mpr hab⟩ = x ∧
      ∀ s t : Icc a b, c t - c s =
        ∫ r in s.val..t.val, f r + A r (c (projIcc a b hab r)) := by
  apply exists_integral_curve hab A f K x hA
  intro c
  apply hf.add
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  have hcm : AEStronglyMeasurable (fun r => c (projIcc a b hab r))
      (volume.restrict (Icc a b)) :=
    (c.continuous.comp continuous_projIcc).aestronglyMeasurable
  apply (integrable_const ((K : ℝ) * ‖c‖)).mono'
    (aestronglyMeasurable_apply_of_strong_operator A hAm hcm)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
  exact ((A r).le_of_opNorm_le (hA r hr) _).trans
    (mul_le_mul_of_nonneg_left (c.norm_coe_le_norm _) K.coe_nonneg)

/-- An L² solution and L² velocity of a bounded strongly measurable linear ODE.
The all-time identity records absolute continuity without claiming C¹ coefficients. -/
theorem exists_lp_integral_curve_of_strong_operator {a b : ℝ} (hab : a ≤ b)
    (A : ℝ → E →L[ℝ] E) (f : ℝ → E) (K : ℝ≥0) (x : E)
    (hA : ∀ r ∈ Icc a b, ‖A r‖ ≤ K)
    (hAm : ∀ y, AEStronglyMeasurable (fun r => A r y) (volume.restrict (Ioo a b)))
    (hf : MemLp f 2 (volume.restrict (Ioo a b))) :
    ∃ c : C(Icc a b, E), ∃ u v : Lp E 2 (volume.restrict (Ioo a b)),
      (u : ℝ → E) =ᵐ[volume.restrict (Ioo a b)] (fun r => c (projIcc a b hab r)) ∧
      (v : ℝ → E) =ᵐ[volume.restrict (Ioo a b)] (fun r => f r + A r (u r)) ∧
      c ⟨a, left_mem_Icc.mpr hab⟩ = x ∧
      ∀ s t : Icc a b, c t - c s = ∫ r in s.val..t.val, v r := by
  have hAmcc : ∀ y, AEStronglyMeasurable (fun r => A r y) (volume.restrict (Icc a b)) := by
    simpa only [restrict_Ioo_eq_restrict_Icc] using hAm
  have hfint : IntervalIntegrable f volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    simpa only [IntegrableOn, restrict_Ioo_eq_restrict_Icc] using hf.integrable (by norm_num)
  obtain ⟨c, hc0, hc⟩ := exists_integral_curve_of_strong_operator hab A f K x hA hAmcc hfint
  have hcm : AEStronglyMeasurable (fun r => c (projIcc a b hab r))
      (volume.restrict (Ioo a b)) :=
    (c.continuous.comp continuous_projIcc).aestronglyMeasurable
  have hclp : MemLp (fun r => c (projIcc a b hab r)) 2 (volume.restrict (Ioo a b)) :=
    MemLp.of_bound hcm ‖c‖ (Eventually.of_forall fun r => c.norm_coe_le_norm _)
  have hAlp : MemLp (fun r => A r (c (projIcc a b hab r))) 2 (volume.restrict (Ioo a b)) := by
    apply MemLp.of_bound (aestronglyMeasurable_apply_of_strong_operator A hAm hcm) ((K : ℝ) * ‖c‖)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact ((A r).le_of_opNorm_le (hA r ⟨hr.1.le, hr.2.le⟩) _).trans
      (mul_le_mul_of_nonneg_left (c.norm_coe_le_norm _) K.coe_nonneg)
  let u := hclp.toLp _
  let v := (hf.add hAlp).toLp _
  have hu : (u : ℝ → E) =ᵐ[volume.restrict (Ioo a b)] (fun r => c (projIcc a b hab r)) :=
    hclp.coeFn_toLp
  have hv : (v : ℝ → E) =ᵐ[volume.restrict (Ioo a b)]
      (fun r => f r + A r (c (projIcc a b hab r))) := (hf.add hAlp).coeFn_toLp
  refine ⟨c, u, v, hu, ?_, hc0, ?_⟩
  · filter_upwards [hu, hv] with r hur hvr
    rw [hvr, hur]
  · intro s t
    rw [hc]
    apply intervalIntegral.integral_congr_ae
    have hvcc : (v : ℝ → E) =ᵐ[volume.restrict (Icc a b)]
        (fun r => f r + A r (c (projIcc a b hab r))) := by
      simpa only [restrict_Ioo_eq_restrict_Icc] using hv
    filter_upwards [ae_imp_of_ae_restrict hvcc] with r hr hrst
    exact (hr ((uIcc_subset_Icc s.property t.property) (uIoc_subset_uIcc hrst))).symm

end MeasurableODE

theorem integral_smul_primitive_boundary {E : Type w}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {G : ℝ → E} (hG : Integrable G volume) (c : E) (T : ℝ)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ) :
    (∫ t in 0..T, deriv φ t • (c + ∫ r in 0..t, G r)) +
      (∫ t in 0..T, φ t • G t) =
      φ T • (c + ∫ r in 0..T, G r) - φ 0 • c := by
  let P : ℝ → E := fun t => c + ∫ r in 0..t, G r
  have hi (a b : ℝ) : IntervalIntegrable G volume a b := hG.intervalIntegrable
  have hP : Continuous P := continuous_const.add (intervalIntegral.continuous_primitive hi 0)
  have hPac : AbsolutelyContinuousOnInterval P 0 T :=
    ((contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => c)).contDiffOn.absolutelyContinuousOnInterval).add
      (Sobolev.OneDimensional.integral_primitive_absolutelyContinuous hi 0 T 0)
  have hQac : AbsolutelyContinuousOnInterval (fun t => φ t • P t) 0 T := by
    exact hφ.contDiffOn.absolutelyContinuousOnInterval.smul hPac
  have hleft : LocallyIntegrable (fun t => deriv φ t • P t) volume :=
    ((hφ.continuous_deriv (by norm_num)).smul hP).locallyIntegrable
  have hright : LocallyIntegrable (fun t => φ t • G t) volume :=
    hG.locallyIntegrable.continuous_smul hφ.continuous
  have hQd : ∀ᵐ t ∂volume, t ∈ Set.uIcc 0 T →
      HasDerivAt (fun t => φ t • P t)
        (deriv φ t • P t + φ t • G t) t := by
    filter_upwards [_root_.LocallyIntegrable.ae_hasDerivAt_integral hG.locallyIntegrable]
      with t ht _
    have hPd : HasDerivAt P (G t) t := by
      simpa only [P, zero_add] using (ht 0).const_add c
    convert! (hφ.differentiable (by norm_num) t).hasDerivAt.smul hPd using 1 <;>
      simp only [Pi.smul_apply, add_comm]
  have he := Sobolev.OneDimensional.integral_eq_sub_of_absolutelyContinuous_of_ae_hasDerivAt
    hQac (hleft.add hright) hQd
  simp only [Pi.add_apply] at he
  rw [intervalIntegral.integral_add
    ((hleft.integrableOn_isCompact isCompact_uIcc).intervalIntegrable)
    ((hright.integrableOn_isCompact isCompact_uIcc).intervalIntegrable)] at he
  simpa only [P, intervalIntegral.integral_same, add_zero] using he


/-- The full boundary integration-by-parts identity follows from the genuine
Banach-valued derivative and any continuous representative. -/
theorem derivative_trace_boundary_identity {E : Type w}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : ℝ) (hT : 0 < T) (u g : ℝ → E)
    (hu : Integrable u (timeMeasure T)) (hg : Integrable g (timeMeasure T))
    (hd : HasTimeDerivative T u g) (c : HilbertTripleTraceSpec.TraceCurve E T)
    (hc : HilbertTripleTraceSpec.extendCurve c =ᵐ[timeMeasure T] u)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ) :
    (∫ t, deriv φ t • u t ∂timeMeasure T) +
      (∫ t, φ t • g t ∂timeMeasure T) =
      φ T • c ⟨T, by simp [hT.le]⟩ - φ 0 • c ⟨0, by simp [hT.le]⟩ := by
  classical
  obtain ⟨d, hdu⟩ := hasTimeDerivative_ae_eq_primitive T u g hu hg hd
  let G := (Set.Ioo 0 T).indicator g
  let P : ℝ → E := fun t => d + ∫ r in 0..t, G r
  have hG : Integrable G volume := (integrable_indicator_iff measurableSet_Ioo).mpr hg
  have hP : Continuous P := continuous_const.add
    (intervalIntegral.continuous_primitive (fun a b => hG.intervalIntegrable) 0)
  have hext : ContinuousOn (HilbertTripleTraceSpec.extendCurve c) (Set.Icc 0 T) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have he : (Set.Icc 0 T).domRestrict (HilbertTripleTraceSpec.extendCurve c) = c := by
      funext t
      simp [HilbertTripleTraceSpec.extendCurve, t.property]
    rw [he]
    exact c.continuous
  have hae : HilbertTripleTraceSpec.extendCurve c =ᵐ[volume.restrict (Set.Icc 0 T)] P := by
    simpa only [timeMeasure, HilbertTripleSpec.timeMeasureValue,
      restrict_Ioo_eq_restrict_Icc] using hc.trans hdu
  have heq := Measure.eqOn_Icc_of_ae_eq volume (ne_of_lt hT) hae hext hP.continuousOn
  have hendpoint (t : Set.Icc 0 T) : P t = c t := by
    have ht := heq t.property
    simpa [HilbertTripleTraceSpec.extendCurve, t.property] using ht.symm
  have hleft : (∫ t, deriv φ t • u t ∂timeMeasure T) =
      ∫ t, deriv φ t • P t ∂timeMeasure T :=
    integral_congr_ae (hdu.mono fun t ht => congrArg (deriv φ t • ·) ht)
  have hright : (∫ t, φ t • G t ∂timeMeasure T) =
      ∫ t, φ t • g t ∂timeMeasure T := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [show G t = g t from Set.indicator_of_mem ht g]
  have hid := integral_smul_primitive_boundary hG d T φ hφ
  have htime (q : ℝ → E) : (∫ t in 0..T, q t) = ∫ t, q t ∂timeMeasure T := by
    rw [intervalIntegral.integral_of_le hT.le, ← restrict_Ioo_eq_restrict_Ioc]
    rfl
  rw [htime (fun t => deriv φ t • (d + ∫ r in 0..t, G r)),
    htime (fun t => φ t • G t)] at hid
  change (∫ t, deriv φ t • P t ∂timeMeasure T) +
      (∫ t, φ t • G t ∂timeMeasure T) = φ T • P T - φ 0 • d at hid
  rw [← hleft, hright] at hid
  have h0 : d = c ⟨0, by simp [hT.le]⟩ := by
    simpa [P] using hendpoint ⟨0, by simp [hT.le]⟩
  rw [h0, hendpoint ⟨T, by simp [hT.le]⟩] at hid
  exact hid


section TripleBoundary
variable {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
open HilbertTripleSpec HilbertTripleTraceSpec

theorem triple_trace_boundary_identity (j : HilbertTriple V H) (T : ℝ) (hT : 0 < T)
    (u : timeLpValue V 2 T) (g : timeLpValue (StrongDual ℝ V) 2 T)
    (hd : tripleDerivativeValue j T u g) (c : TraceCurve H T)
    (hc : Represents j T u c) (v : V) (φ : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ) :
    (∫ t, deriv φ t * inner ℝ (j.embedding (u t)) (j.embedding v) ∂timeMeasure T) +
      (∫ t, φ t * g t v ∂timeMeasure T) =
      φ T * inner ℝ (c ⟨T, by simp [hT.le]⟩) (j.embedding v) -
        φ 0 * inner ℝ (c ⟨0, by simp [hT.le]⟩) (j.embedding v) := by
  let : IsFiniteMeasure (timeMeasureValue T) := ⟨by
    simp [timeMeasure, timeMeasureValue, Real.volume_Ioo]⟩
  let e := ContinuousLinearMap.apply ℝ ℝ v
  have hder : HasTimeDerivative T (fun t => intoDual j (u t)) g := hd
  have hmap := hasTimeDerivative_map e T _ _ hder
  let cs : TraceCurve ℝ T :=
    ⟨fun t => inner ℝ (c t) (j.embedding v), c.continuous.inner continuous_const⟩
  have hrep : extendCurve cs =ᵐ[timeMeasure T] fun t => e (intoDual j (u t)) := by
    filter_upwards [hc, ae_restrict_mem measurableSet_Ioo] with t ht hti
    have hcc : t ∈ Set.Icc 0 T := Set.Ioo_subset_Icc_self hti
    change extendCurve c t = j.embedding (u t) at ht
    simp only [extendCurve, dite_eq_left hcc] at ht ⊢
    change inner ℝ (c ⟨t, hcc⟩) (j.embedding v) = _
    rw [ht]
    exact (intoDual_apply j (u t) v).symm
  have hu : Integrable (fun t => e (intoDual j (u t))) (timeMeasure T) :=
    (e.comp (intoDual j)).comp_memLp u |>.integrable (by norm_num)
  have hg : Integrable (fun t => e (g t)) (timeMeasure T) :=
    e.comp_memLp g |>.integrable (by norm_num)
  have hb := derivative_trace_boundary_identity T hT _ _ hu hg hmap cs hrep φ hφ
  simpa only [cs, ContinuousMap.coe_mk, e, ContinuousLinearMap.apply_apply,
    intoDual_apply, smul_eq_mul] using hb

theorem initial_trace_of_affine_identity (j : HilbertTriple V H) (T : ℝ) (hT : 0 < T)
    (u : timeLpValue V 2 T) (g : timeLpValue (StrongDual ℝ V) 2 T)
    (hd : tripleDerivativeValue j T u g) (c : TraceCurve H T)
    (hc : Represents j T u c) (u₀ : H)
    (hid : ∀ v : V,
      (∫ t, -(T⁻¹) * inner ℝ (j.embedding (u t)) (j.embedding v) ∂timeMeasure T) +
        (∫ t, (1 - t / T) * g t v ∂timeMeasure T) = -inner ℝ u₀ (j.embedding v)) :
    c ⟨0, by simp [hT.le]⟩ = u₀ := by
  let φ : ℝ → ℝ := fun t => 1 - t / T
  have hφ : ContDiff ℝ 1 φ := contDiff_const.sub (contDiff_id.div_const T)
  have hderiv (t : ℝ) : deriv φ t = -(T⁻¹) := by
    have hh : HasDerivAt φ (-(T⁻¹)) t := by
      convert! (hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id t).div_const T) using 1 <;>
        simp [φ, one_div]
    exact hh.deriv
  apply Dense.eq_of_inner_left (𝕜 := ℝ) j.denseRange
  rintro _ ⟨v, rfl⟩
  have hb := triple_trace_boundary_identity j T hT u g hd c hc v φ hφ
  simp only [hderiv] at hb
  simp [φ, hT.ne'] at hb
  exact neg_injective (hb.symm.trans (by simpa only [neg_mul] using hid v))

theorem initial_trace_of_weak_limit_affine_identity {I : Type w} {l : Filter I} [l.NeBot]
    (j : HilbertTriple V H) (T : ℝ) (hT : 0 < T)
    (L : timeLpValue V 2 T →L[ℝ] timeLpValue (StrongDual ℝ V) 2 T)
    (f : timeLpValue (StrongDual ℝ V) 2 T)
    (z : I → timeLpValue V 2 T) (u : timeLpValue V 2 T)
    (hz : ∀ e : StrongDual ℝ (timeLpValue V 2 T),
      Tendsto (fun i => e (z i)) l (𝓝 (e u)))
    (hd : tripleDerivativeValue j T u (f - L u)) (c : TraceCurve H T)
    (hc : Represents j T u c) (u₀ : H)
    (hid : ∀ v : V, ∀ᶠ i in l,
      (∫ t, -(T⁻¹) * inner ℝ (j.embedding (z i t)) (j.embedding v) ∂timeMeasure T) +
        (∫ t, (1 - t / T) * f t v ∂timeMeasure T) -
        (∫ t, (1 - t / T) * L (z i) t v ∂timeMeasure T) = -inner ℝ u₀ (j.embedding v)) :
    c ⟨0, by simp [hT.le]⟩ = u₀ := by
  apply initial_trace_of_affine_identity j T hT u (f - L u) hd c hc u₀
  intro v
  let e : StrongDual ℝ V := (ContinuousLinearMap.apply ℝ ℝ v).comp (intoDualValue j)
  have he (x : V) : e x = inner ℝ (j.embedding x) (j.embedding v) := by
    change inner ℝ (j.embedding.adjoint (j.embedding x)) v = _
    exact j.embedding.adjoint_inner_left v (j.embedding x)
  have hψ : ContinuousOn (fun _ : ℝ => -(T⁻¹)) (Set.Icc 0 T) := continuous_const.continuousOn
  have hφ : ContinuousOn (fun t : ℝ => 1 - t / T) (Set.Icc 0 T) :=
    (continuous_const.sub (continuous_id.div_const T)).continuousOn
  obtain ⟨Fd, hFd⟩ := scalar_time_test_functional_of_continuousOn T _ hψ e
  obtain ⟨Fφ, hFφ⟩ := scalar_time_test_functional_of_continuousOn T _ hφ
    (ContinuousLinearMap.apply ℝ ℝ v)
  have hconvleft := hz Fd
  have hconvright := hz (Fφ.comp L)
  simp only [hFd, he] at hconvleft
  change Tendsto (fun i => Fφ (L (z i))) l (𝓝 (Fφ (L u))) at hconvright
  simp only [hFφ, ContinuousLinearMap.apply_apply] at hconvright
  have heq := tendsto_nhds_unique
    (((hconvleft.add tendsto_const_nhds).sub hconvright).congr' (hid v))
    tendsto_const_nhds
  have hi (a : timeLpValue (StrongDual ℝ V) 2 T) :
      Integrable (fun t => (1 - t / T) * a t v) (timeMeasure T) := by
    exact memLp_one_iff_integrable.mp ((ContinuousLinearMap.mul ℝ ℝ).memLp_of_bilin 1
      (memLp_time_of_continuousOn T hφ) ((ContinuousLinearMap.apply ℝ ℝ v).comp_memLp a))
  have hsub : (∫ t, (1 - t / T) * (f - L u) t v ∂timeMeasure T) =
      (∫ t, (1 - t / T) * f t v ∂timeMeasure T) -
        (∫ t, (1 - t / T) * L u t v ∂timeMeasure T) := by
    rw [← integral_sub (hi f) (hi (L u))]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub f (L u)] with t ht
    simp only [ht, Pi.sub_apply, sub_apply, mul_sub]
  rw [hsub]
  simpa only [timeMeasure, add_sub_assoc] using heq

end TripleBoundary

section Forms
variable {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem formOperator_apply (a : BilinearForms V) (M t : ℝ)
    (ht : BoundedAt a M t) (x y : V) : formOperator a M t x y = a t x y := by
  rw [formOperator, dite_eq_left ht]
  rfl

/-- This bound is valid even at exceptional times and for negative M. -/
theorem formOperator_norm_le (a : BilinearForms V) (M t : ℝ) :
    ‖formOperator a M t‖ ≤ max M 0 := by
  classical
  by_cases ht : BoundedAt a M t
  · simpa only [formOperator, dite_eq_left ht] using (a t).mkContinuous₂_norm_le' ht
  · rw [formOperator, dite_eq_right ht]
    change ‖(0 : V →L[ℝ] StrongDual ℝ V)‖ ≤ max M 0
    rw [ContinuousLinearMap.opNorm_zero]
    exact le_max_right M 0

/-- The canonical total operator recovers the original form simultaneously
for all vectors, on the source's single conull set. -/
theorem formOperator_ae_eq (j : HilbertTriple V H) (T : ℝ)
    (a : BilinearForms V) (M α C : ℝ) (ha : FormHypotheses j T a M α C) :
    ∀ᵐ t ∂HilbertTripleSpec.timeMeasureValue T,
      ∀ x y : V, formOperator a M t x y = a t x y :=
  ha.bounds.mono fun t ht x y => formOperator_apply a M t ht.1 x y

theorem operator_action : OperatorActionExpected.{u} := by
  intro V _ _ _ T a M _hbound hstrong
  exact exists_lp_operator_of_strong_operator (formOperator a M) hstrong
    (le_max_right M 0) (Eventually.of_forall (formOperator_norm_le a M)) 2

instance finiteSubspace_nonempty : Nonempty (FiniteSubspace V) :=
  ⟨⟨⊥, inferInstance⟩⟩

instance finiteSubspace_directed : IsDirectedOrder (FiniteSubspace V) where
  directed E F := ⟨⟨E.val ⊔ F.val, inferInstance⟩,
    (show E.val ≤ E.val ⊔ F.val from le_sup_left),
    (show F.val ≤ E.val ⊔ F.val from le_sup_right)⟩

/-- Each test vector belongs to every sufficiently large Galerkin space. -/
theorem eventually_mem_finiteSubspace (x : V) :
    ∀ᶠ E : FiniteSubspace V in atTop, x ∈ E.val := by
  let E₀ : FiniteSubspace V := ⟨Submodule.span ℝ {x}, inferInstance⟩
  filter_upwards [eventually_ge_atTop E₀] with E hE
  exact hE (Submodule.mem_span_singleton_self x)

theorem initialProjection_norm_le (j : HilbertTriple V H)
    (E : FiniteSubspace V) (h : H) : ‖initialProjection j E h‖ ≤ ‖h‖ :=
  (imageSubspace j E).norm_starProjection_apply_le h

theorem initialProjection_eq_self (j : HilbertTriple V H)
    (E : FiniteSubspace V) (x : V) (hx : x ∈ E.val) :
    initialProjection j E (j.embedding x) = j.embedding x := by
  apply Submodule.starProjection_eq_self_iff.mpr
  exact ⟨x, hx, rfl⟩

/-- Density of JV and contractivity of H-projections prove convergence of
the whole inclusion-directed net, with no countable basis. -/
theorem initialProjection_tendsto (j : HilbertTriple V H) (h : H) :
    Tendsto (fun E : FiniteSubspace V => initialProjection j E h) atTop (𝓝 h) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨x, hx⟩ := j.denseRange.exists_dist_lt h (half_pos hε)
  filter_upwards [eventually_mem_finiteSubspace x] with E hE
  have heq := initialProjection_eq_self j E x hE
  have hdist : dist (initialProjection j E h) (initialProjection j E (j.embedding x)) ≤
      dist h (j.embedding x) := by
    simpa only [dist_eq_norm, ← map_sub] using
      initialProjection_norm_le j E (h - j.embedding x)
  calc
    dist (initialProjection j E h) h ≤
        dist (initialProjection j E h) (initialProjection j E (j.embedding x)) +
          dist (initialProjection j E (j.embedding x)) h := dist_triangle _ _ _
    _ ≤ dist h (j.embedding x) + dist (j.embedding x) h := by
      rw [heq]
      rw [heq] at hdist
      linarith
    _ < ε := by rw [dist_comm (j.embedding x) h]; linarith

theorem projection_convergence : ProjectionConvergenceExpected.{u,v} := by
  intro V H _ _ _ _ _ _ j
  exact ⟨inferInstance, initialProjection_tendsto j⟩

-- Use the inherited inner-product normed structure consistently on the
-- finite-dimensional subspace and on its continuous dual.
local instance finiteSubspaceNormedSpace (E : FiniteSubspace V) : NormedSpace ℝ E.val :=
  (inferInstance : InnerProductSpace ℝ E.val).toNormedSpace

/-- The finite-dimensional injection carries the original V norm in its
domain and the original H norm in its codomain. -/
def finiteEmbedding (j : HilbertTriple V H) (E : FiniteSubspace V) : E.val →L[ℝ] H :=
  j.embedding.comp E.val.subtypeL

theorem finiteEmbedding_injective (j : HilbertTriple V H) (E : FiniteSubspace V) :
    Function.Injective (finiteEmbedding j E) :=
  j.injective.comp Subtype.val_injective

/-- The H mass matrix, written without a choice of basis. -/
def finiteGram (j : HilbertTriple V H) (E : FiniteSubspace V) : E.val →L[ℝ] E.val :=
  (finiteEmbedding j E).adjoint.comp (finiteEmbedding j E)

@[simp] theorem finiteGram_inner (j : HilbertTriple V H) (E : FiniteSubspace V)
    (x y : E.val) :
    inner ℝ (finiteGram j E x) y = inner ℝ (j.embedding x) (j.embedding y) :=
  (finiteEmbedding j E).adjoint_inner_left y (finiteEmbedding j E x)

theorem finiteGram_injective (j : HilbertTriple V H) (E : FiniteSubspace V) :
    Function.Injective (finiteGram j E) := by
  apply (injective_iff_map_eq_zero (finiteGram j E)).mpr
  intro x hx
  have hzero : finiteEmbedding j E x = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    have he := finiteGram_inner j E x x
    rw [hx, inner_zero_left] at he
    exact he.symm
  exact (finiteEmbedding_injective j E) (hzero.trans (map_zero _).symm)

/-- Positive definiteness plus finite dimension gives an actual continuous
inverse of the mass matrix, also for the zero space. -/
def finiteGramEquiv (j : HilbertTriple V H) (E : FiniteSubspace V) : E.val ≃L[ℝ] E.val :=
  (LinearEquiv.ofBijective (finiteGram j E).toLinearMap
    ⟨finiteGram_injective j E,
      LinearMap.injective_iff_surjective.mp (finiteGram_injective j E)⟩).toContinuousLinearEquiv

@[simp] theorem finiteGramEquiv_apply (j : HilbertTriple V H) (E : FiniteSubspace V)
    (x : E.val) : finiteGramEquiv j E x = finiteGram j E x := rfl

/-- Inverse mass map: a restricted dual forcing determines the Galerkin
velocity. Its continuity constants may depend on E. -/
def inverseMass (j : HilbertTriple V H) (E : FiniteSubspace V) :
    StrongDual ℝ E.val ≃L[ℝ] E.val :=
  (InnerProductSpace.toDual ℝ E.val).symm.toContinuousLinearEquiv.trans
    (finiteGramEquiv j E).symm

@[simp] theorem inverseMass_pairing (j : HilbertTriple V H) (E : FiniteSubspace V)
    (f : StrongDual ℝ E.val) (x : E.val) :
    inner ℝ (j.embedding (inverseMass j E f)) (j.embedding x) = f x := by
  rw [← finiteGram_inner]
  change inner ℝ (finiteGramEquiv j E
    ((finiteGramEquiv j E).symm ((InnerProductSpace.toDual ℝ E.val).symm f))) x = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact InnerProductSpace.toDual_symm_apply

/-- Restriction of the original dual forcing to E, with the original V
norm, is itself a bounded linear operation. -/
def dualRestriction (E : FiniteSubspace V) : StrongDual ℝ V →L[ℝ] StrongDual ℝ E.val :=
  (ContinuousLinearMap.compL ℝ E.val V ℝ).flip E.val.subtypeL

@[simp] theorem dualRestriction_apply (E : FiniteSubspace V)
    (f : StrongDual ℝ V) (x : E.val) : dualRestriction E f x = f x := rfl

theorem dualRestriction_norm_le (E : FiniteSubspace V) : ‖dualRestriction E‖ ≤ 1 := by
  apply (dualRestriction E).opNorm_le_bound zero_le_one
  intro f
  rw [one_mul]
  apply ((dualRestriction E) f).opNorm_le_bound (norm_nonneg f)
  intro x
  exact f.le_opNorm x

/-- The measurable ODE's bounded coefficient operator after mass inversion. -/
def finiteCoefficient (j : HilbertTriple V H) (E : FiniteSubspace V)
    (a : BilinearForms V) (M t : ℝ) : E.val →L[ℝ] E.val :=
  (inverseMass j E).toContinuousLinearMap.comp
    ((dualRestriction E).comp ((formOperator a M t).comp E.val.subtypeL))

theorem finiteCoefficient_pairing (j : HilbertTriple V H) (E : FiniteSubspace V)
    (a : BilinearForms V) (M t : ℝ) (ht : BoundedAt a M t) (x y : E.val) :
    inner ℝ (j.embedding (finiteCoefficient j E a M t x)) (j.embedding y) =
      a t x y := by
  change inner ℝ (j.embedding (inverseMass j E _)) (j.embedding y) = _
  rw [inverseMass_pairing]
  exact formOperator_apply a M t ht x y

theorem finiteCoefficient_stronglyMeasurable (j : HilbertTriple V H)
    (E : FiniteSubspace V) (T : ℝ) (a : BilinearForms V) (M : ℝ)
    (hA : ∀ x, AEStronglyMeasurable (fun t => formOperator a M t x)
      (HilbertTripleSpec.timeMeasureValue T)) (x : E.val) :
    AEStronglyMeasurable (fun t => finiteCoefficient j E a M t x)
      (HilbertTripleSpec.timeMeasureValue T) :=
  ((inverseMass j E).continuous.comp_aestronglyMeasurable
    ((dualRestriction E).continuous.comp_aestronglyMeasurable (hA x)))

theorem finiteCoefficient_norm_le (j : HilbertTriple V H) (E : FiniteSubspace V)
    (a : BilinearForms V) (M t : ℝ) :
    ‖finiteCoefficient j E a M t‖ ≤
      ‖(inverseMass j E).toContinuousLinearMap‖ * max M 0 := by
  apply (finiteCoefficient j E a M t).opNorm_le_bound (by positivity)
  intro x
  calc
    ‖finiteCoefficient j E a M t x‖ ≤
        ‖(inverseMass j E).toContinuousLinearMap‖ *
          ‖dualRestriction E (formOperator a M t x)‖ :=
      (inverseMass j E).toContinuousLinearMap.le_opNorm _
    _ ≤ ‖(inverseMass j E).toContinuousLinearMap‖ * ‖formOperator a M t x‖ := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg ((inverseMass j E).toContinuousLinearMap))
      simpa only [one_mul] using
        (dualRestriction E).le_of_opNorm_le (dualRestriction_norm_le E)
          (formOperator a M t x)
    _ ≤ ‖(inverseMass j E).toContinuousLinearMap‖ * (max M 0 * ‖x‖) :=
      mul_le_mul_of_nonneg_left
        ((formOperator a M t).le_of_opNorm_le (formOperator_norm_le a M t) x)
        (norm_nonneg ((inverseMass j E).toContinuousLinearMap))
    _ = _ := (mul_assoc _ _ _).symm

/-- The projected initial datum expressed in E with its original norm. -/
def finiteInitial (j : HilbertTriple V H) (E : FiniteSubspace V) : H →L[ℝ] E.val :=
  (finiteGramEquiv j E).symm.toContinuousLinearMap.comp (finiteEmbedding j E).adjoint

theorem finiteInitial_pairing (j : HilbertTriple V H) (E : FiniteSubspace V)
    (u₀ : H) (x : E.val) :
    inner ℝ (j.embedding (finiteInitial j E u₀)) (j.embedding x) =
      inner ℝ u₀ (j.embedding x) := by
  rw [← finiteGram_inner]
  change inner ℝ ((finiteGramEquiv j E)
    ((finiteGramEquiv j E).symm ((finiteEmbedding j E).adjoint u₀))) x = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact (finiteEmbedding j E).adjoint_inner_left x u₀

theorem finiteInitial_projection (j : HilbertTriple V H) (E : FiniteSubspace V)
    (u₀ : H) : j.embedding (finiteInitial j E u₀) = initialProjection j E u₀ := by
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (K := imageSubspace j E)
  · exact ⟨_, (finiteInitial j E u₀).property, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [inner_sub_left]
    exact sub_eq_zero.mpr (finiteInitial_pairing j E u₀ ⟨x, hx⟩).symm

/-- The finite-dimensional Galerkin equation has an absolutely continuous
solution for measurable form coefficients, including zero time and dimension. -/
theorem exists_galerkinSolution (j : HilbertTriple V H) (T : ℝ) (hT : 0 ≤ T)
    (a : BilinearForms V) (M α C : ℝ) (ha : FormHypotheses j T a M α C)
    (f : HilbertTripleSpec.timeLpValue (StrongDual ℝ V) 2 T) (u₀ : H)
    (E : FiniteSubspace V) : Nonempty (GalerkinSolution j T hT a f u₀ E) := by
  let F : StrongDual ℝ V →L[ℝ] E.val :=
    (inverseMass j E).toContinuousLinearMap.comp (dualRestriction E)
  let A : ℝ → E.val →L[ℝ] E.val := fun t => -finiteCoefficient j E a M t
  let K : NNReal := ⟨‖(inverseMass j E).toContinuousLinearMap‖ * max M 0, by positivity⟩
  have hA : ∀ r ∈ Set.Icc 0 T, ‖A r‖ ≤ K := by
    intro r _
    change ‖-finiteCoefficient j E a M r‖ ≤ ‖(inverseMass j E).toContinuousLinearMap‖ * max M 0
    simpa only [norm_neg] using finiteCoefficient_norm_le j E a M r
  have hAm : ∀ y, AEStronglyMeasurable (fun r => A r y) (volume.restrict (Set.Ioo 0 T)) := by
    intro y
    exact (finiteCoefficient_stronglyMeasurable j E T a M ha.strong_measurable y).neg
  have hf : MemLp (fun t => F (f t)) 2 (volume.restrict (Set.Ioo 0 T)) :=
    F.comp_memLp f
  obtain ⟨c, u, v, hu, hv, hc0, hc⟩ :=
    exists_lp_integral_curve_of_strong_operator hT A (fun t => F (f t)) K
      (finiteInitial j E u₀) hA hAm hf
  let z : HilbertTripleSpec.timeLpValue V 2 T := E.val.subtypeL.compLp u
  have hz : (z : ℝ → V) =ᵐ[HilbertTripleSpec.timeMeasureValue T] fun t => (u t : V) :=
    E.val.subtypeL.coeFn_compLp u
  refine ⟨{
    curve := c
    value := z
    velocity := v
    represents := ?_
    integral_equation := hc
    equation := ?_
    initial := ?_ }⟩
  · filter_upwards [hz, hu, ae_restrict_mem measurableSet_Ioo] with t hzt hut ht
    have htcc : t ∈ Set.Icc 0 T := ⟨ht.1.le, ht.2.le⟩
    have hproj : Set.projIcc 0 T hT t = ⟨t, htcc⟩ := by
      apply Subtype.ext
      simp [Set.projIcc, htcc.1, htcc.2]
    simp only [extendSubspaceCurve, dite_eq_left htcc]
    rw [hzt, hut, hproj]
  · filter_upwards [hz, hv, ha.bounds] with t hzt hvt ht
    intro y
    change inner ℝ (j.embedding ((v t : E.val) : V)) (j.embedding y) + a t (z t) y = f t y
    have hvel : v t = F (f t) -
        finiteCoefficient j E a M t (u t) := by
      simpa only [A, neg_apply, sub_eq_add_neg] using hvt
    rw [hzt, hvel]
    simp only [Submodule.coe_sub, map_sub, inner_sub_left,
      finiteCoefficient_pairing j E a M t ht.1, sub_add_cancel]
    exact inverseMass_pairing j E (dualRestriction E (f t)) y
  · intro y
    rw [hc0, inner_sub_left, finiteInitial_pairing]
    exact sub_self _

theorem finite_mass_solvability : FiniteMassSolvabilityExpected.{u,v} := by
  intro V H _ _ _ _ _ _ j E
  exact ⟨inverseMass j E, inverseMass_pairing j E⟩

theorem weak_lp_extraction : WeakLpExtractionExpected.{u,v} := by
  intro V _ _ _ T I l _ z R hz
  exact exists_weak_limit_of_eventually_norm_le z R hz

/-- Young's inequality in the exact constants of the manuscript. -/
theorem dual_young (α : ℝ) (hα : 0 < α) (x : V) (g : StrongDual ℝ V) :
    g x ≤ (α / 2) * ‖x‖ ^ 2 + (2 * α)⁻¹ * ‖g‖ ^ 2 := by
  have hg : g x ≤ ‖g‖ * ‖x‖ := (le_abs_self (g x)).trans (g.le_opNorm x)
  have hsq := sq_nonneg (α * ‖x‖ - ‖g‖)
  have hcancel : (2 * α) * ((2 * α)⁻¹ * ‖g‖ ^ 2) = ‖g‖ ^ 2 := by
    rw [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
  have hh : ‖g‖ * ‖x‖ ≤ (α / 2) * ‖x‖ ^ 2 + (2 * α)⁻¹ * ‖g‖ ^ 2 := by
    nlinarith
  exact hg.trans hh

theorem energy_inequality : EnergyInequalityExpected.{u,v} := by
  intro V H _ _ _ _ _ _ j T a M α C ha
  filter_upwards [ha.bounds] with t ht x g
  have hy := dual_young α ha.alpha_pos x g
  have hc := ht.2 x
  linarith

theorem form_test_functional : FormTestFunctionalExpected.{u,v} := by
  intro V H _ _ _ _ _ _ j T a M α C ha w
  obtain ⟨L, _hLnorm, hL⟩ := operator_action T a M
    (ha.bounds.mono fun _ ht => ht.1) ha.strong_measurable
  let P := (ContinuousLinearMap.id ℝ (StrongDual ℝ V)).lpPairing
    (HilbertTripleSpec.timeMeasureValue T) 2 2
  refine ⟨(P.flip w).comp L, ?_⟩
  intro z
  change P (L z) w = _
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [hL z, formOperator_ae_eq j T a M α C ha] with t ht heq
  change L z t (w t) = _
  rw [ht, heq]

/-- Hence weak convergence passes through the form term for any fixed L²
test vector. This avoids an unjustified measurability claim about A(t)'. -/
theorem form_test_tendsto {I : Type w} {l : Filter I}
    (j : HilbertTriple V H) (T : ℝ) (a : BilinearForms V) (M α C : ℝ)
    (ha : FormHypotheses j T a M α C)
    (z : I → HilbertTripleSpec.timeLpValue V 2 T)
    (u : HilbertTripleSpec.timeLpValue V 2 T)
    (hz : ∀ ℓ : StrongDual ℝ (HilbertTripleSpec.timeLpValue V 2 T),
      Tendsto (fun i => ℓ (z i)) l (𝓝 (ℓ u)))
    (w : HilbertTripleSpec.timeLpValue V 2 T) :
    Tendsto (fun i => ∫ t, a t (z i t) (w t) ∂HilbertTripleSpec.timeMeasureValue T)
      l (𝓝 (∫ t, a t (u t) (w t) ∂HilbertTripleSpec.timeMeasureValue T)) := by
  obtain ⟨ℓ, hℓ⟩ := form_test_functional j T a M α C ha w
  simpa only [hℓ] using hz ℓ

theorem zero_time_solution : ZeroTimeSolutionExpected.{u,v} := by
  intro V H _ _ _ _ _ _ j a M f u₀
  have hμ : HilbertTripleSpec.timeMeasureValue 0 = 0 := by
    simp [HilbertTripleSpec.timeMeasureValue]
  let z : WeakSolution j 0 le_rfl a M f u₀ :=
    { value := 0
      derivative := 0
      curve := ContinuousMap.const _ u₀
      represents := by
        simp [HilbertTripleTraceSpec.Represents, hμ, Filter.EventuallyEq]
      has_derivative := by
        refine ⟨?_, ?_, ?_⟩
        · intro t ht
          exfalso
          linarith [ht.1, ht.2]
        · intro t ht
          exfalso
          linarith [ht.1, ht.2]
        · intro φ _hφ
          simp [hμ]
      equation := by simp [hμ]
      initial := rfl }
  refine ⟨z, rfl, rfl, ?_⟩
  apply (ContinuousMap.norm_le _ (norm_nonneg u₀)).mpr
  intro t
  exact le_rfl

open HilbertTripleTraceSpec

private theorem derivative_of_primitive {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {T : ℝ} (hT : 0 ≤ T) (g : ℝ → E)
    (hg : Integrable g (timeMeasure T)) (c : E) :
    HasTimeDerivative T
      (fun t => c + ∫ r in 0..t, (Set.Ioo 0 T).indicator g r) g := by
  let G := (Set.Ioo 0 T).indicator g
  let P := fun t => ∫ r in 0..t, G r
  have hG : Integrable G volume := (integrable_indicator_iff measurableSet_Ioo).mpr hg
  have hP : Continuous P := intervalIntegral.continuous_primitive
    (fun a b => hG.intervalIntegrable) 0
  refine ⟨(continuous_const.add hP).locallyIntegrable.locallyIntegrableOn _,
    (show IntegrableOn g (Set.Ioo 0 T) volume from hg).locallyIntegrableOn, ?_⟩
  intro φ hφ
  have hφ0 : φ 0 = 0 := by
    apply Function.notMem_support.mp
    intro h
    exact (hφ.2.2 (subset_tsupport _ h)).1.false
  have hφT : φ T = 0 := by
    apply Function.notMem_support.mp
    intro h
    exact (hφ.2.2 (subset_tsupport _ h)).2.false
  have hconst : (∫ t, deriv φ t • c ∂timeMeasure T) = 0 := by
    rw [integral_smul_const]
    have he : (∫ t, deriv φ t ∂timeMeasure T) = ∫ t in 0..T, deriv φ t := by
      rw [intervalIntegral.integral_of_le hT, integral_Ioc_eq_integral_Ioo]
      rfl
    rw [he, intervalIntegral.integral_deriv_eq_sub
      (fun _ _ => (hφ.1.differentiable (by simp)).differentiableAt)
      ((hφ.1.continuous_deriv (by simp)).intervalIntegrable _ _), hφT, hφ0]
    simp
  have hprim := integral_test_smul_primitive hG.locallyIntegrable 0 hφ.1 hφ.2.1
  have hsupp : Function.support (fun t => deriv φ t • P t) ⊆ Set.Ioo 0 T := by
    intro t ht
    apply hφ.2.2
    apply tsupport_deriv_subset
    apply subset_tsupport
    intro h
    exact ht (by simp [h])
  have hprim' : (∫ t, deriv φ t • P t ∂timeMeasure T) =
      -(∫ t, φ t • g t ∂timeMeasure T) := by
    change (∫ t in Set.Ioo 0 T, deriv φ t • P t) = _
    rw [← integral_indicator measurableSet_Ioo, Set.indicator_eq_self.mpr hsupp]
    change (∫ t, deriv φ t • P t) = -(∫ t in Set.Ioo 0 T, φ t • g t)
    rw [← integral_indicator measurableSet_Ioo]
    simpa only [G, P, Set.indicator_smul_apply] using hprim
  have hic : Integrable (fun t => deriv φ t • c) (timeMeasure T) :=
    ((hφ.1.continuous_deriv (by simp)).integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self |>.smul_const c
  have hip : Integrable (fun t => deriv φ t • P t) (timeMeasure T) :=
    (((hφ.1.continuous_deriv (by simp)).smul hP).integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
  simp only [smul_add]
  change (∫ t, deriv φ t • c + deriv φ t • P t ∂timeMeasure T) = _
  rw [integral_add hic hip, hconst, zero_add]
  exact hprim'

section GalerkinEnergy
variable {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem galerkin_hasTimeDerivative
    (j : HilbertTriple V H) (T : ℝ) (hT : 0 ≤ T)
    (a : BilinearForms V) (f : HilbertTripleSpec.timeLpValue (StrongDual ℝ V) 2 T)
    (u₀ : H) (E : FiniteSubspace V) (G : GalerkinSolution j T hT a f u₀ E) :
    HasTimeDerivative T (G.value : ℝ → V) (fun t => (G.velocity t : V)) := by
  let : IsFiniteMeasure (HilbertTripleSpec.timeMeasureValue T) :=
    inferInstanceAs (IsFiniteMeasure (volume.restrict (Set.Ioo 0 T)))
  let g : ℝ → V := fun t => (G.velocity t : V)
  have hgE : Integrable (G.velocity : ℝ → E.val) (timeMeasure T) :=
    (Lp.memLp G.velocity).integrable (by norm_num)
  have hg : Integrable g (timeMeasure T) := E.val.subtypeL.integrable_comp hgE
  have hiE (s t : Set.Icc 0 T) :
      IntervalIntegrable (G.velocity : ℝ → E.val) volume s.val t.val := by
    have hh : IntegrableOn (G.velocity : ℝ → E.val) (Set.Icc 0 T) volume := by
      simpa only [IntegrableOn, timeMeasure, HilbertTripleSpec.timeMeasureValue,
        restrict_Ioo_eq_restrict_Icc] using hgE
    rw [intervalIntegrable_iff']
    exact hh.mono_set (Set.uIcc_subset_Icc s.property t.property)
  let c₀ : V := G.curve ⟨0, by simp [hT]⟩
  let P : ℝ → V := fun t => c₀ + ∫ r in 0..t, (Set.Ioo 0 T).indicator g r
  have hPeq (t : Set.Icc 0 T) : (G.curve t : V) = P t := by
    have heq := congrArg E.val.subtypeL
      (G.integral_equation ⟨0, by simp [hT]⟩ t)
    rw [map_sub, ← E.val.subtypeL.intervalIntegral_comp_comm
      (hiE ⟨0, by simp [hT]⟩ t)] at heq
    have heq' : (∫ r in 0..t.val, (Set.Ioo 0 T).indicator g r) = ∫ r in 0..t.val, g r := by
      apply intervalIntegral.integral_congr_ae_restrict
      have hh : (Set.Ioo 0 T).indicator g =ᵐ[volume.restrict (Set.Icc 0 T)] g := by
        rw [← restrict_Ioo_eq_restrict_Icc]
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
        exact Set.indicator_of_mem hr g
      exact ae_restrict_of_ae_restrict_of_subset
        (Set.uIoc_subset_uIcc.trans (Set.uIcc_subset_Icc (by simp [hT]) t.property)) hh
    dsimp [P]
    rw [heq']
    change (G.curve t : V) - c₀ = ∫ r in 0..t.val, g r at heq
    exact (sub_eq_iff_eq_add).mp heq |>.trans (add_comm _ _)
  have hu : (G.value : ℝ → V) =ᵐ[timeMeasure T] P := by
    filter_upwards [G.represents, ae_restrict_mem measurableSet_Ioo] with t ht hti
    have htcc : t ∈ Set.Icc 0 T := ⟨hti.1.le, hti.2.le⟩
    rw [ht, extendSubspaceCurve, dite_eq_left htcc]
    exact hPeq ⟨t, htcc⟩
  exact (hasTimeDerivative_congr T P G.value g g hu.symm (Eventually.of_forall fun _ => rfl)).mp
    (derivative_of_primitive hT g hg c₀)

theorem galerkin_energy_identity
    (j : HilbertTriple V H) (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (a : BilinearForms V) (f : HilbertTripleSpec.timeLpValue (StrongDual ℝ V) 2 T)
    (u₀ : H) (E : FiniteSubspace V) (G : GalerkinSolution j T hT a f u₀ E)
    (s t : Set.Icc 0 T) :
    IntervalIntegrable (fun r => inner ℝ (j.embedding (G.velocity r))
      (j.embedding (G.value r))) volume s.val t.val ∧
    ‖embeddedCurve j E G.curve t‖ ^ 2 - ‖embeddedCurve j E G.curve s‖ ^ 2 =
      2 * ∫ r in s.val..t.val,
        inner ℝ (j.embedding (G.velocity r)) (j.embedding (G.value r)) := by
  let B : E.val →L[ℝ] StrongDual ℝ V := (intoDual j).comp E.val.subtypeL
  let D : HilbertTripleSpec.timeLpValue (StrongDual ℝ V) 2 T := B.compLp G.velocity
  have hd : HilbertTripleSpec.tripleDerivativeValue j T G.value D := by
    have hm := hasTimeDerivative_map (intoDual j) T (G.value : ℝ → V)
      (fun r => (G.velocity r : V)) (galerkin_hasTimeDerivative j T hT a f u₀ E G)
    have hDeq : (D : ℝ → StrongDual ℝ V) =ᵐ[timeMeasure T]
        fun r => intoDual j (G.velocity r) := B.coeFn_compLp G.velocity
    exact (hasTimeDerivative_congr T (fun r => intoDual j (G.value r))
      (fun r => intoDual j (G.value r))
      (fun r => intoDual j (G.velocity r)) (D : ℝ → StrongDual ℝ V)
      (Eventually.of_forall fun _ => rfl) hDeq.symm).mp hm
  let z : HilbertTripleSpec.energySpaceValue j T := ⟨(G.value, D), hd⟩
  obtain ⟨tr, hrep, huniq, _hb, he⟩ := hilbertTriple_trace j T hTpos
  have hc : Represents j T G.value (embeddedCurve j E G.curve) := by
    filter_upwards [G.represents, ae_restrict_mem measurableSet_Ioo] with r hr hri
    have hrcc : r ∈ Set.Icc 0 T := ⟨hri.1.le, hri.2.le⟩
    change extendCurve (embeddedCurve j E G.curve) r = j.embedding (G.value r)
    rw [extendCurve, dite_eq_left hrcc, hr, extendSubspaceCurve, dite_eq_left hrcc]
    rfl
  have hcurve : embeddedCurve j E G.curve = tr z := huniq z _ hc
  have heq : energyDensity T G.value D =ᵐ[volume.restrict (Set.Icc 0 T)]
      fun r => inner ℝ (j.embedding (G.velocity r)) (j.embedding (G.value r)) := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    filter_upwards [B.coeFn_compLp G.velocity] with r hr
    change D r (G.value r) = _
    rw [hr]
    exact intoDual_apply j _ _
  have heqst := ae_restrict_of_ae_restrict_of_subset
    (Set.uIoc_subset_uIcc.trans (Set.uIcc_subset_Icc s.property t.property)) heq
  have hh := he z s t
  refine ⟨hh.1.congr_ae heqst, ?_⟩
  rw [hcurve, hh.2]
  rw [intervalIntegral.integral_congr_ae_restrict heqst]


end GalerkinEnergy

lemma time_intervalIntegral_mono (T t : ℝ) (ht : t ∈ Set.Icc 0 T)
    {q r : ℝ → ℝ} (hq : Integrable q (HilbertTripleSpec.timeMeasureValue T))
    (hr : Integrable r (HilbertTripleSpec.timeMeasureValue T))
    (hle : q ≤ᵐ[HilbertTripleSpec.timeMeasureValue T] r) :
    (∫ s in 0..t, q s) ≤ ∫ s in 0..t, r s := by
  have hsub : Set.Icc 0 t ⊆ Set.Icc 0 T := Set.Icc_subset_Icc le_rfl ht.2
  have hqi : IntegrableOn q (Set.Icc 0 T) := by
    simpa only [IntegrableOn, HilbertTripleSpec.timeMeasureValue,
      restrict_Ioo_eq_restrict_Icc] using hq
  have hri : IntegrableOn r (Set.Icc 0 T) := by
    simpa only [IntegrableOn, HilbertTripleSpec.timeMeasureValue,
      restrict_Ioo_eq_restrict_Icc] using hr
  have hle' : q ≤ᵐ[volume.restrict (Set.Icc 0 t)] r := by
    have hh : q ≤ᵐ[volume.restrict (Set.Icc 0 T)] r := by
      simpa only [HilbertTripleSpec.timeMeasureValue,
        restrict_Ioo_eq_restrict_Icc] using hle
    exact hh.filter_mono (ae_mono (Measure.restrict_mono_set _ hsub))
  exact intervalIntegral.integral_mono_ae_restrict ht.1
    (by simpa only [Set.uIcc_of_le ht.1] using hqi.mono_set hsub :
      IntegrableOn q (Set.uIcc 0 t)).intervalIntegrable
    (by simpa only [Set.uIcc_of_le ht.1] using hri.mono_set hsub :
      IntegrableOn r (Set.uIcc 0 t)).intervalIntegrable hle' 

lemma parabolic_energy_sq_bounds (j : HilbertTriple V H) (T : ℝ) (hT : 0 ≤ T)
    (a : BilinearForms V) (M α C : ℝ) (ha : FormHypotheses j T a M α C)
    (u : HilbertTripleSpec.timeLpValue V 2 T)
    (f g : HilbertTripleSpec.timeLpValue (StrongDual ℝ V) 2 T)
    (c : TraceCurve H T) (u₀ : H) (hc : Represents j T u c)
    (hinit : ‖c ⟨0, by simp [hT]⟩‖ ≤ ‖u₀‖)
    (heq : ∀ᵐ t ∂HilbertTripleSpec.timeMeasureValue T,
      g t = f t - formOperator a M t (u t))
    (he : ∀ s t : Set.Icc 0 T,
      ‖c t‖ ^ 2 - ‖c s‖ ^ 2 = 2 * ∫ r in s.val..t.val, g r (u r)) :
    (∀ t : Set.Icc 0 T,
      ‖c t‖ ^ 2 ≤ (‖u₀‖ ^ 2 + α⁻¹ * ‖f‖ ^ 2) * Real.exp (2 * max C 0 * T)) ∧
    α * ‖u‖ ^ 2 ≤ (‖u₀‖ ^ 2 + α⁻¹ * ‖f‖ ^ 2) *
      (1 + 2 * max C 0 * T * Real.exp (2 * max C 0 * T)) := by
  let μ := HilbertTripleSpec.timeMeasureValue T
  let h : ℝ → ℝ := fun t => ‖extendCurve c t‖ ^ 2
  let k : ℝ → ℝ := fun t => ‖u t‖ ^ 2
  let q : ℝ → ℝ := fun t => ‖f t‖ ^ 2
  let d : ℝ → ℝ := fun t => g t (u t)
  let D : ℝ := ‖u₀‖ ^ 2 + α⁻¹ * ‖f‖ ^ 2
  let β : ℝ := 2 * max C 0
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have hα : 0 < α := ha.alpha_pos
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hki : Integrable k μ := (Lp.memLp u).integrable_norm_pow (by norm_num)
  have hqi : Integrable q μ := (Lp.memLp f).integrable_norm_pow (by norm_num)
  have hdi : Integrable d μ := triple_pairing_integrable T u g
  have hhi : Integrable h μ := by
    have hh' : Integrable (fun t => ‖j.embedding (u t)‖ ^ 2) μ :=
      (j.embedding.comp_memLp u).integrable_norm_pow (by norm_num)
    exact hh'.congr (hc.fun_comp (fun x => ‖x‖ ^ 2)).symm
  have hpoint : (fun t => 2 * d t + α * k t) ≤ᵐ[μ]
      fun t => β * h t + α⁻¹ * q t := by
    filter_upwards [energy_inequality j T a M α C ha,
      formOperator_ae_eq j T a M α C ha, hc, heq] with t ht hform hct hgt
    have hy := ht (u t) (f t)
    have hC : C * ‖j.embedding (u t)‖ ^ 2 ≤ max C 0 * ‖j.embedding (u t)‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_left C 0) (sq_nonneg _)
    have hinv : 2 * (2 * α)⁻¹ = α⁻¹ := by field_simp
    dsimp only [d, k, h, β, q]
    rw [hct, hgt]
    simp only [sub_apply, hform] at *
    nlinarith
  have h0 : ‖c ⟨0, by simp [hT]⟩‖ ^ 2 ≤ ‖u₀‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hinit
  have hint (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
      h t + α * (∫ r in 0..t, k r) ≤ D + β * (∫ r in 0..t, h r) := by
    have hb := time_intervalIntegral_mono T t ht
      ((hdi.const_mul 2).add (hki.const_mul α))
      ((hhi.const_mul β).add (hqi.const_mul α⁻¹)) hpoint
    have hsub : Set.uIcc 0 t ⊆ Set.Icc 0 T :=
      Set.uIcc_subset_Icc ⟨le_rfl, hT⟩ ht
    have ii {z : ℝ → ℝ} (hz : Integrable z μ) : IntervalIntegrable z volume 0 t := by
      have hi : IntegrableOn z (Set.Icc 0 T) := by
        simpa only [IntegrableOn, μ, HilbertTripleSpec.timeMeasureValue,
          restrict_Ioo_eq_restrict_Icc] using hz
      exact (hi.mono_set hsub).intervalIntegrable
    simp only [Pi.add_apply] at hb
    rw [intervalIntegral.integral_add ((ii hdi).const_mul 2) ((ii hki).const_mul α),
      intervalIntegral.integral_add ((ii hhi).const_mul β) ((ii hqi).const_mul α⁻¹)] at hb
    simp only [intervalIntegral.integral_const_mul] at hb
    have hid := he ⟨0, by simp [hT]⟩ ⟨t, ht⟩
    have hqt : (∫ r in 0..t, q r) ≤ ‖f‖ ^ 2 := by
      have hq₀ : 0 ≤ᵐ[volume.restrict (Set.Ioc 0 T)] q :=
        Eventually.of_forall (fun _ => sq_nonneg _)
      have hqii : IntervalIntegrable q volume 0 T := by
        have hi : IntegrableOn q (Set.Icc 0 T) := by
          simpa only [IntegrableOn, μ, HilbertTripleSpec.timeMeasureValue,
            restrict_Ioo_eq_restrict_Icc] using hqi
        exact (by simpa only [Set.uIcc_of_le hT] using hi :
          IntegrableOn _ (Set.uIcc 0 T)).intervalIntegrable
      have hmono := intervalIntegral.integral_mono_interval (a := 0) (b := t)
        (c := 0) (d := T) le_rfl ht.1 ht.2 hq₀ hqii
      have hfull : (∫ r in 0..T, q r) = ‖f‖ ^ 2 := by
        rw [intervalIntegral.integral_of_le hT, integral_Ioc_eq_integral_Ioo]
        change (∫ r, ‖f r‖ ^ 2 ∂μ) = ‖f‖ ^ 2
        rw [lp_two_norm_eq_sqrt_integral, Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)]
      exact hmono.trans_eq hfull
    have hht : h t = ‖c ⟨t, ht⟩‖ ^ 2 := by simp only [h, extendCurve, dite_eq_left ht]
    dsimp only [d] at hb
    rw [hht]
    dsimp only [D]
    have hiα : 0 ≤ α⁻¹ := inv_nonneg.mpr ha.alpha_pos.le
    nlinarith [mul_le_mul_of_nonneg_left hqt hiα]
  have hkii : IntervalIntegrable k volume 0 T := by
    have hi : IntegrableOn k (Set.Icc 0 T) := by
      simpa only [IntegrableOn, μ, HilbertTripleSpec.timeMeasureValue,
        restrict_Ioo_eq_restrict_Icc] using hki
    exact (by simpa only [Set.uIcc_of_le hT] using hi :
          IntegrableOn _ (Set.uIcc 0 T)).intervalIntegrable
  have hb := integrated_energy_bound T α β D h k hT ha.alpha_pos hβ hD
    ((extendCurve_continuousOn c).norm.pow 2) (fun _ _ => sq_nonneg _) hkii
    (fun _ _ => sq_nonneg _) hint
  refine ⟨?_, ?_⟩
  · intro t
    simpa only [h, extendCurve, dite_eq_left t.property, D, β] using hb.1 t t.property
  · have hkfull : (∫ r in 0..T, k r) = ‖u‖ ^ 2 := by
      rw [intervalIntegral.integral_of_le hT, integral_Ioc_eq_integral_Ioo]
      exact timeLp_integral_norm_sq T u
    simpa only [hkfull, D, β] using hb.2
/-- A constant uniform in the data and the approximation space. Only the
energy identity and the original form hypotheses enter this estimate. -/
theorem parabolic_curve_bound_uniform (j : HilbertTriple V H) (T : ℝ) (hT : 0 ≤ T)
    (M α C : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (a : BilinearForms V), FormHypotheses j T a M α C →
      ∀ (u : HilbertTripleSpec.timeLpValue V 2 T)
        (f g : HilbertTripleSpec.timeLpValue (StrongDual ℝ V) 2 T)
        (c : TraceCurve H T) (u₀ : H),
        Represents j T u c → ‖c ⟨0, by simp [hT]⟩‖ ≤ ‖u₀‖ →
        (∀ᵐ t ∂HilbertTripleSpec.timeMeasureValue T,
          g t = f t - formOperator a M t (u t)) →
        (∀ s t : Set.Icc 0 T,
          ‖c t‖ ^ 2 - ‖c s‖ ^ 2 = 2 * ∫ r in s.val..t.val, g r (u r)) →
        ‖c‖ + ‖u‖ ≤ K * (‖u₀‖ + ‖f‖) := by
  by_cases hα : 0 < α
  ·
    let β := 2 * max C 0
    let Q := 1 + α⁻¹
    let B := Real.exp (β * T)
    let W := 1 + β * T * B
    let Kc := Real.sqrt (Q * B)
    let Ku := Real.sqrt (Q * W / α)
    have hβ : 0 ≤ β := by dsimp [β]; positivity
    have hQ : 0 ≤ Q := by dsimp [Q]; positivity
    have hB : 0 < B := Real.exp_pos _
    have hW : 0 ≤ W := by dsimp [W]; positivity
    have hKc : 0 ≤ Kc := Real.sqrt_nonneg _
    have hKu : 0 ≤ Ku := Real.sqrt_nonneg _
    refine ⟨Kc + Ku, add_nonneg hKc hKu, ?_⟩
    intro a ha u f g c u₀ hc hi hge he
    obtain ⟨hcsq, husq⟩ := parabolic_energy_sq_bounds j T hT a M α C ha u f g c u₀ hc hi hge he
    let S := ‖u₀‖ + ‖f‖
    let D := ‖u₀‖ ^ 2 + α⁻¹ * ‖f‖ ^ 2
    have hS : 0 ≤ S := add_nonneg (norm_nonneg _) (norm_nonneg _)
    have hD : D ≤ Q * S ^ 2 := by
      have hiα : 0 ≤ α⁻¹ := inv_nonneg.mpr hα.le
      dsimp only [D, Q, S]
      nlinarith [sq_nonneg ‖u₀‖, sq_nonneg ‖f‖,
        mul_nonneg hiα (sq_nonneg ‖u₀‖),
        mul_nonneg (norm_nonneg u₀) (norm_nonneg f),
        mul_nonneg hiα (mul_nonneg (norm_nonneg u₀) (norm_nonneg f))]
    have hcb : ‖c‖ ≤ Kc * S := by
      apply (ContinuousMap.norm_le c (mul_nonneg hKc hS)).mpr
      intro t
      apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hKc hS)).mp
      calc
        ‖c t‖ ^ 2 ≤ D * B := hcsq t
        _ ≤ Q * S ^ 2 * B := mul_le_mul_of_nonneg_right hD hB.le
        _ = (Kc * S) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (mul_nonneg hQ hB.le)]
          ring
    have hub : ‖u‖ ≤ Ku * S := by
      apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hKu hS)).mp
      have hQW : 0 ≤ Q * W / α := by positivity
      have hsqrt : Ku ^ 2 = Q * W / α := Real.sq_sqrt hQW
      apply (mul_le_mul_iff_right₀ hα).mp
      calc
        α * ‖u‖ ^ 2 ≤ D * W := husq
        _ ≤ Q * S ^ 2 * W := mul_le_mul_of_nonneg_right hD hW
        _ = α * (Ku * S) ^ 2 := by rw [mul_pow, hsqrt]; field_simp
    dsimp only [S] at hcb hub
    nlinarith
  
  · exact ⟨0, le_rfl, fun a ha => False.elim (hα ha.alpha_pos)⟩

theorem parabolic_curve_bound (j : HilbertTriple V H) (T : ℝ) (hT : 0 ≤ T)
    (a : BilinearForms V) (M α C : ℝ) (ha : FormHypotheses j T a M α C) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (u : HilbertTripleSpec.timeLpValue V 2 T)
        (f g : HilbertTripleSpec.timeLpValue (StrongDual ℝ V) 2 T)
        (c : TraceCurve H T) (u₀ : H),
        Represents j T u c → ‖c ⟨0, by simp [hT]⟩‖ ≤ ‖u₀‖ →
        (∀ᵐ t ∂HilbertTripleSpec.timeMeasureValue T,
          g t = f t - formOperator a M t (u t)) →
        (∀ s t : Set.Icc 0 T,
          ‖c t‖ ^ 2 - ‖c s‖ ^ 2 = 2 * ∫ r in s.val..t.val, g r (u r)) →
        ‖c‖ + ‖u‖ ≤ K * (‖u₀‖ + ‖f‖) := by
  obtain ⟨K, hK, hb⟩ := parabolic_curve_bound_uniform j T hT M α C
  exact ⟨K, hK, hb a ha⟩

section GalerkinTests
variable {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem galerkin_test_identity
    (j : HilbertTriple V H) (T : ℝ) (hT : 0 ≤ T)
    (a : BilinearForms V) (M α C : ℝ) (ha : FormHypotheses j T a M α C)
    (f : HilbertTripleSpec.timeLpValue (StrongDual ℝ V) 2 T) (u₀ : H)
    (L : HilbertTripleSpec.timeLpValue V 2 T →L[ℝ]
      HilbertTripleSpec.timeLpValue (StrongDual ℝ V) 2 T)
    (hL : ∀ z, (L z : ℝ → StrongDual ℝ V) =ᵐ[HilbertTripleSpec.timeMeasureValue T]
      fun t => formOperator a M t (z t))
    (E : FiniteSubspace V) (G : GalerkinSolution j T hT a f u₀ E)
    (x : E.val) (φ : ℝ → ℝ) (hφ : HilbertTripleSpec.testValue T φ) :
    (∫ t, deriv φ t * inner ℝ (j.embedding (G.value t)) (j.embedding x)
        ∂HilbertTripleSpec.timeMeasureValue T) +
      (∫ t, φ t * f t x ∂HilbertTripleSpec.timeMeasureValue T) =
      ∫ t, φ t * L G.value t x ∂HilbertTripleSpec.timeMeasureValue T := by
  let : IsLocallyFiniteMeasure (HilbertTripleSpec.timeMeasureValue T) := by
    dsimp [HilbertTripleSpec.timeMeasureValue]
    infer_instance
  let e : StrongDual ℝ V := (ContinuousLinearMap.apply ℝ ℝ (x : V)).comp (intoDual j)
  have he (v : V) : e v = inner ℝ (j.embedding v) (j.embedding x) := intoDual_apply j v x
  have hd := hasTimeDerivative_map e T (G.value : ℝ → V)
    (fun t => (G.velocity t : V)) (galerkin_hasTimeDerivative j T hT a f u₀ E G)
  have hparts := hd.2.2 φ hφ
  simp only [smul_eq_mul, he] at hparts
  have hv := (hasTimeDerivative_test_integrable T _ _ hd φ hφ).2
  simp only [smul_eq_mul, he] at hv
  have hf : Integrable (fun t => φ t * f t x)
      (HilbertTripleSpec.timeMeasureValue T) := by
    have hl := ((ContinuousLinearMap.apply ℝ ℝ (x : V)).comp_memLp f).locallyIntegrable
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    exact hl.integrable_smul_left_of_hasCompactSupport hφ.1.continuous hφ.2.1
  have hscalar : (fun t => φ t * L G.value t x) =ᵐ[HilbertTripleSpec.timeMeasureValue T]
      fun t => φ t * f t x - φ t * inner ℝ (j.embedding (G.velocity t)) (j.embedding x) := by
    filter_upwards [G.equation, hL G.value, formOperator_ae_eq j T a M α C ha]
      with t hgt hLt hAt
    rw [hLt, hAt, ← mul_sub]
    congr 1
    linarith [hgt x]
  rw [integral_congr_ae hscalar, integral_sub hf hv]
  linarith

theorem eventually_galerkin_test_identity
    (j : HilbertTriple V H) (T : ℝ) (hT : 0 ≤ T)
    (a : BilinearForms V) (M α C : ℝ) (ha : FormHypotheses j T a M α C)
    (f : HilbertTripleSpec.timeLpValue (StrongDual ℝ V) 2 T) (u₀ : H)
    (L : HilbertTripleSpec.timeLpValue V 2 T →L[ℝ]
      HilbertTripleSpec.timeLpValue (StrongDual ℝ V) 2 T)
    (hL : ∀ z, (L z : ℝ → StrongDual ℝ V) =ᵐ[HilbertTripleSpec.timeMeasureValue T]
      fun t => formOperator a M t (z t))
    (G : (E : FiniteSubspace V) → GalerkinSolution j T hT a f u₀ E)
    (v : V) (φ : ℝ → ℝ) (hφ : HilbertTripleSpec.testValue T φ) :
    ∀ᶠ E : FiniteSubspace V in atTop,
      (∫ t, deriv φ t * inner ℝ (j.embedding ((G E).value t)) (j.embedding v)
          ∂HilbertTripleSpec.timeMeasureValue T) +
        (∫ t, φ t * f t v ∂HilbertTripleSpec.timeMeasureValue T) =
        ∫ t, φ t * L (G E).value t v ∂HilbertTripleSpec.timeMeasureValue T := by
  filter_upwards [eventually_mem_finiteSubspace v] with E hE
  exact galerkin_test_identity j T hT a M α C ha f u₀ L hL E (G E) ⟨v, hE⟩ φ hφ

end GalerkinTests


theorem galerkin_initial_projection (j : HilbertTriple V H) (T : ℝ) (hT : 0 ≤ T)
    (a : BilinearForms V) (f : HilbertTripleSpec.timeLpValue (StrongDual ℝ V) 2 T)
    (u₀ : H) (E : FiniteSubspace V) (G : GalerkinSolution j T hT a f u₀ E) :
    j.embedding (G.curve ⟨0, by simp [hT]⟩) = initialProjection j E u₀ := by
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (K := imageSubspace j E)
  · exact ⟨_, (G.curve ⟨0, by simp [hT]⟩).property, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hh := G.initial ⟨x, hx⟩
    rw [inner_sub_left] at hh ⊢
    change inner ℝ (j.embedding (G.curve ⟨0, by simp [hT]⟩)) (j.embedding x) -
      inner ℝ u₀ (j.embedding x) = 0 at hh
    exact sub_eq_zero.mpr (sub_eq_zero.mp hh).symm

theorem galerkin_represents (j : HilbertTriple V H) (T : ℝ) (hT : 0 ≤ T)
    (a : BilinearForms V) (f : HilbertTripleSpec.timeLpValue (StrongDual ℝ V) 2 T)
    (u₀ : H) (E : FiniteSubspace V) (G : GalerkinSolution j T hT a f u₀ E) :
    Represents j T G.value (embeddedCurve j E G.curve) := by
  filter_upwards [G.represents, ae_restrict_mem measurableSet_Ioo] with r hr hri
  have hrcc : r ∈ Set.Icc 0 T := ⟨hri.1.le, hri.2.le⟩
  change extendCurve (embeddedCurve j E G.curve) r = j.embedding (G.value r)
  rw [extendCurve, dite_eq_left hrcc, hr, extendSubspaceCurve, dite_eq_left hrcc]
  rfl

theorem galerkin_uniform_bound_pos_uniform (j : HilbertTriple V H) (T : ℝ) (hT : 0 ≤ T)
    (hTpos : 0 < T) (M α C : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (a : BilinearForms V), FormHypotheses j T a M α C →
      ∀ (f : HilbertTripleSpec.timeLpValue (StrongDual ℝ V) 2 T) (u₀ : H)
        (E : FiniteSubspace V) (G : GalerkinSolution j T hT a f u₀ E),
        ‖embeddedCurve j E G.curve‖ + ‖G.value‖ ≤ K * (‖u₀‖ + ‖f‖) := by
  obtain ⟨K, hK, hbound⟩ := parabolic_curve_bound_uniform j T hT M α C
  refine ⟨K, hK, ?_⟩
  intro a ha f u₀ E G
  obtain ⟨L, _hLn, hL⟩ := operator_action T a M (ha.bounds.mono fun _ ht => ht.1) ha.strong_measurable
  let g := f - L G.value
  have hge : ∀ᵐ t ∂HilbertTripleSpec.timeMeasureValue T,
      g t = f t - formOperator a M t (G.value t) := by
    filter_upwards [Lp.coeFn_sub f (L G.value), hL G.value] with t ht hLt
    simpa only [Pi.sub_apply, hLt] using ht
  have henergyPair : (fun r => inner ℝ (j.embedding (G.velocity r))
      (j.embedding (G.value r))) =ᵐ[HilbertTripleSpec.timeMeasureValue T]
      fun r => g r (G.value r) := by
    filter_upwards [G.represents, G.equation, ha.bounds, hge,
      ae_restrict_mem measurableSet_Ioo] with t hrep heq hform hg ht
    have htcc : t ∈ Set.Icc 0 T := ⟨ht.1.le, ht.2.le⟩
    have hmem : G.value t ∈ E.val := by
      rw [hrep, extendSubspaceCurve, dite_eq_left htcc]
      exact (G.curve ⟨t, htcc⟩).property
    have heq' := heq ⟨G.value t, hmem⟩
    rw [hg]
    simp only [sub_apply, formOperator_apply a M t hform.1]
    exact eq_sub_of_add_eq heq'
  have he (s t : Set.Icc 0 T) :
      ‖embeddedCurve j E G.curve t‖ ^ 2 - ‖embeddedCurve j E G.curve s‖ ^ 2 =
        2 * ∫ r in s.val..t.val, g r (G.value r) := by
    have hh := (galerkin_energy_identity j T hT hTpos a f u₀ E G s t).2
    rw [hh]
    congr 1
    apply intervalIntegral.integral_congr_ae_restrict
    have hecc : (fun r => inner ℝ (j.embedding (G.velocity r)) (j.embedding (G.value r)))
        =ᵐ[volume.restrict (Set.Icc 0 T)] (fun r => g r (G.value r)) := by
      simpa only [HilbertTripleSpec.timeMeasureValue, restrict_Ioo_eq_restrict_Icc] using henergyPair
    exact ae_restrict_of_ae_restrict_of_subset
      (Set.uIoc_subset_uIcc.trans (Set.uIcc_subset_Icc s.property t.property)) hecc
  apply hbound a ha G.value f g (embeddedCurve j E G.curve) u₀
    (galerkin_represents j T hT a f u₀ E G) _ hge he
  change ‖j.embedding (G.curve ⟨0, by simp [hT]⟩)‖ ≤ ‖u₀‖
  rw [galerkin_initial_projection]
  exact initialProjection_norm_le j E u₀


section GalerkinBoundary
variable {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

private theorem time_mul_integrable {T : ℝ} {q : ℝ → ℝ}
    (hq : Integrable q (timeMeasure T)) (ψ : ℝ → ℝ) (hψ : Continuous ψ) :
    Integrable (fun t => ψ t * q t) (timeMeasure T) := by
  exact (show IntegrableOn q (Set.Ioo 0 T) volume from hq).continuousOn_mul_of_subset
    hψ.continuousOn isCompact_Icc measurableSet_Ioo Set.Ioo_subset_Icc_self

theorem galerkin_boundary_test_identity
    (j : HilbertTriple V H) (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (a : BilinearForms V) (M α C : ℝ) (ha : FormHypotheses j T a M α C)
    (f : HilbertTripleSpec.timeLpValue (StrongDual ℝ V) 2 T) (u₀ : H)
    (L : HilbertTripleSpec.timeLpValue V 2 T →L[ℝ]
      HilbertTripleSpec.timeLpValue (StrongDual ℝ V) 2 T)
    (hL : ∀ z, (L z : ℝ → StrongDual ℝ V) =ᵐ[HilbertTripleSpec.timeMeasureValue T]
      fun t => formOperator a M t (z t))
    (E : FiniteSubspace V) (G : GalerkinSolution j T hT a f u₀ E)
    (x : E.val) (φ : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ) (hφ0 : φ 0 = 1) (hφT : φ T = 0) :
    (∫ t, deriv φ t * inner ℝ (j.embedding (G.value t)) (j.embedding x)
        ∂HilbertTripleSpec.timeMeasureValue T) +
      (∫ t, φ t * f t x ∂HilbertTripleSpec.timeMeasureValue T) -
      (∫ t, φ t * L G.value t x ∂HilbertTripleSpec.timeMeasureValue T) =
      -inner ℝ u₀ (j.embedding x) := by
  let : IsFiniteMeasure (HilbertTripleSpec.timeMeasureValue T) :=
    inferInstanceAs (IsFiniteMeasure (volume.restrict (Set.Ioo 0 T)))
  let e : StrongDual ℝ V := (ContinuousLinearMap.apply ℝ ℝ (x : V)).comp (intoDual j)
  have he (v : V) : e v = inner ℝ (j.embedding v) (j.embedding x) := intoDual_apply j v x
  have hd := hasTimeDerivative_map e T (G.value : ℝ → V)
    (fun t => (G.velocity t : V)) (galerkin_hasTimeDerivative j T hT a f u₀ E G)
  let cs : TraceCurve ℝ T :=
    ⟨fun t => e (G.curve t), e.continuous.comp
      (continuous_subtype_val.comp G.curve.continuous)⟩
  have hrep : extendCurve cs =ᵐ[timeMeasure T] fun t => e (G.value t) := by
    filter_upwards [G.represents, ae_restrict_mem measurableSet_Ioo] with t ht hti
    have hcc : t ∈ Set.Icc 0 T := Set.Ioo_subset_Icc_self hti
    rw [extendCurve, dite_eq_left hcc, ht, extendSubspaceCurve, dite_eq_left hcc]
    rfl
  have hu : Integrable (fun t => e (G.value t)) (timeMeasure T) :=
    e.comp_memLp G.value |>.integrable (by norm_num)
  have hg : Integrable (fun t => e (G.velocity t)) (timeMeasure T) :=
    (e.comp E.val.subtypeL).comp_memLp G.velocity |>.integrable (by norm_num)
  have hb := derivative_trace_boundary_identity T hTpos _ _ hu hg hd cs hrep φ hφ
  simp only [smul_eq_mul, he, hφ0, hφT, zero_mul, one_mul, zero_sub] at hb
  have hinit : inner ℝ (j.embedding (G.curve ⟨0, by simp [hT]⟩)) (j.embedding x) =
      inner ℝ u₀ (j.embedding x) := by
    have hh := G.initial x
    rw [inner_sub_left] at hh
    exact sub_eq_zero.mp hh
  change _ = - e (G.curve ⟨0, by simp [hT]⟩) at hb
  rw [he, hinit] at hb
  simp only [timeMeasure] at hb
  have hf := time_mul_integrable
    ((ContinuousLinearMap.apply ℝ ℝ (x : V)).comp_memLp f |>.integrable (by norm_num)) φ hφ.continuous
  change Integrable (fun t => φ t * f t x) (HilbertTripleSpec.timeMeasureValue T) at hf
  have hv := time_mul_integrable hg φ hφ.continuous
  simp only [he, timeMeasure] at hv
  have hscalar : (fun t => φ t * L G.value t x) =ᵐ[HilbertTripleSpec.timeMeasureValue T]
      fun t => φ t * f t x - φ t * inner ℝ (j.embedding (G.velocity t)) (j.embedding x) := by
    filter_upwards [G.equation, hL G.value, formOperator_ae_eq j T a M α C ha]
      with t hgt hLt hAt
    rw [hLt, hAt, ← mul_sub]
    congr 1
    linarith [hgt x]
  rw [integral_congr_ae hscalar, integral_sub hf hv]
  linarith

theorem eventually_galerkin_affine_identity
    (j : HilbertTriple V H) (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (a : BilinearForms V) (M α C : ℝ) (ha : FormHypotheses j T a M α C)
    (f : HilbertTripleSpec.timeLpValue (StrongDual ℝ V) 2 T) (u₀ : H)
    (L : HilbertTripleSpec.timeLpValue V 2 T →L[ℝ]
      HilbertTripleSpec.timeLpValue (StrongDual ℝ V) 2 T)
    (hL : ∀ z, (L z : ℝ → StrongDual ℝ V) =ᵐ[HilbertTripleSpec.timeMeasureValue T]
      fun t => formOperator a M t (z t))
    (G : (E : FiniteSubspace V) → GalerkinSolution j T hT a f u₀ E)
    (v : V) : ∀ᶠ E : FiniteSubspace V in atTop,
      (∫ t, -(T⁻¹) * inner ℝ (j.embedding ((G E).value t)) (j.embedding v)
          ∂HilbertTripleSpec.timeMeasureValue T) +
        (∫ t, (1 - t / T) * f t v ∂HilbertTripleSpec.timeMeasureValue T) -
        (∫ t, (1 - t / T) * L (G E).value t v ∂HilbertTripleSpec.timeMeasureValue T) =
        -inner ℝ u₀ (j.embedding v) := by
  let φ : ℝ → ℝ := fun t => 1 - t / T
  have hφ : ContDiff ℝ 1 φ := contDiff_const.sub (contDiff_id.div_const T)
  have hderiv (t : ℝ) : deriv φ t = -(T⁻¹) := by
    have hh : HasDerivAt φ (-(T⁻¹)) t := by
      convert! (hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id t).div_const T) using 1 <;>
        simp [φ, one_div]
    exact hh.deriv
  filter_upwards [eventually_mem_finiteSubspace v] with E hE
  have hb := galerkin_boundary_test_identity j T hT hTpos a M α C ha f u₀ L hL E (G E)
    ⟨v, hE⟩ φ hφ (by simp [φ]) (by simp [φ, hTpos.ne'])
  simpa only [hderiv, φ] using hb

end GalerkinBoundary

theorem galerkin_uniform_bound_pos (j : HilbertTriple V H) (T : ℝ) (hT : 0 ≤ T)
    (hTpos : 0 < T) (a : BilinearForms V) (M α C : ℝ) (ha : FormHypotheses j T a M α C) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (f : HilbertTripleSpec.timeLpValue (StrongDual ℝ V) 2 T) (u₀ : H)
        (E : FiniteSubspace V) (G : GalerkinSolution j T hT a f u₀ E),
        ‖embeddedCurve j E G.curve‖ + ‖G.value‖ ≤ K * (‖u₀‖ + ‖f‖) := by
  obtain ⟨K, hK, hb⟩ := galerkin_uniform_bound_pos_uniform j T hT hTpos M α C
  exact ⟨K, hK, hb a ha⟩

theorem galerkin_existence_zero (j : HilbertTriple V H)
    (M α C : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (a : BilinearForms V), FormHypotheses j 0 a M α C →
      ∀ (f : HilbertTripleSpec.timeLpValue (StrongDual ℝ V) 2 0) (u₀ : H),
      ∃ G : (E : FiniteSubspace V) → GalerkinSolution j 0 le_rfl a f u₀ E,
      ∃ z : WeakSolution j 0 le_rfl a M f u₀,
        (∀ E, ‖embeddedCurve j E (G E).curve‖ + ‖(G E).value‖ ≤ K * (‖u₀‖ + ‖f‖)) ∧
        (‖z.curve‖ + ‖z.value‖ + ‖z.derivative‖ ≤ K * (‖u₀‖ + ‖f‖)) ∧
        ∃ F : Filter (FiniteSubspace V), F.NeBot ∧ F ≤ atTop ∧
          ∀ ℓ : StrongDual ℝ (HilbertTripleSpec.timeLpValue V 2 0),
            Tendsto (fun E => ℓ (G E).value) F (𝓝 (ℓ z.value)) := by
  classical
  refine ⟨1, zero_le_one, ?_⟩
  intro a ha f u₀
  let G (E : FiniteSubspace V) := (exists_galerkinSolution j 0 le_rfl a M α C ha f u₀ E).some
  obtain ⟨z, hzv, hzd, hzc⟩ := zero_time_solution j a M f u₀
  have hμ : HilbertTripleSpec.timeMeasureValue 0 = 0 := by
    simp [HilbertTripleSpec.timeMeasureValue]
  have hzero (q : HilbertTripleSpec.timeLpValue V 2 0) : q = 0 := by
    apply Lp.ext
    change ∀ᵐ t ∂HilbertTripleSpec.timeMeasureValue 0, _
    have hbot : ae (HilbertTripleSpec.timeMeasureValue 0) = ⊥ := by simp [hμ]
    rw [hbot]
    exact Filter.eventually_bot
  refine ⟨G, z, ?_, ?_, atTop, inferInstance, le_rfl, ?_⟩
  · intro E
    rw [hzero (G E).value, norm_zero, add_zero, one_mul]
    have hc : ‖embeddedCurve j E (G E).curve‖ ≤ ‖u₀‖ := by
      apply (ContinuousMap.norm_le _ (norm_nonneg u₀)).mpr
      intro t
      have ht : t = ⟨0, by simp⟩ := Subtype.ext (le_antisymm t.property.2 t.property.1)
      rw [ht]
      change ‖j.embedding ((G E).curve ⟨0, by simp⟩)‖ ≤ ‖u₀‖
      have hinit := (G E).initial ((G E).curve ⟨0, by simp⟩)
      rw [inner_sub_left, real_inner_self_eq_norm_sq] at hinit
      have hcs := real_inner_le_norm u₀ (j.embedding ((G E).curve ⟨0, by simp⟩))
      nlinarith [norm_nonneg (j.embedding ((G E).curve ⟨0, by simp⟩)), norm_nonneg u₀]
    exact hc.trans (le_add_of_nonneg_right (norm_nonneg f))
  · rw [hzv, hzd, norm_zero, norm_zero, add_zero, add_zero, one_mul]
    exact hzc.trans (le_add_of_nonneg_right (norm_nonneg f))
  · intro ℓ
    simp only [hzero (G _).value, hzv, map_zero]
    exact tendsto_const_nhds

theorem galerkin_existence_pos (j : HilbertTriple V H)
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T) (M α C : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (a : BilinearForms V), FormHypotheses j T a M α C →
      ∀ (f : HilbertTripleSpec.timeLpValue (StrongDual ℝ V) 2 T) (u₀ : H),
      ∃ G : (E : FiniteSubspace V) → GalerkinSolution j T hT a f u₀ E,
      ∃ z : WeakSolution j T hT a M f u₀,
        (∀ E, ‖embeddedCurve j E (G E).curve‖ + ‖(G E).value‖ ≤ K * (‖u₀‖ + ‖f‖)) ∧
        (‖z.curve‖ + ‖z.value‖ + ‖z.derivative‖ ≤ K * (‖u₀‖ + ‖f‖)) ∧
        ∃ F : Filter (FiniteSubspace V), F.NeBot ∧ F ≤ atTop ∧
          ∀ ℓ : StrongDual ℝ (HilbertTripleSpec.timeLpValue V 2 T),
            Tendsto (fun E => ℓ (G E).value) F (𝓝 (ℓ z.value)) := by
  classical
  obtain ⟨KG, hKG, hGb⟩ := galerkin_uniform_bound_pos_uniform j T hT hTpos M α C
  let B : ℝ := Real.sqrt (T⁻¹ * ‖j.embedding‖ ^ 2 + 1)
  let D : ℝ := 1 + (1 + max M 0) * KG
  let KW : ℝ := (B + 1) * D
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hKW : 0 ≤ KW := by dsimp [KW]; positivity
  refine ⟨KG + KW, add_nonneg hKG hKW, ?_⟩
  intro a ha f u₀
  let S : ℝ := ‖u₀‖ + ‖f‖
  have hS : 0 ≤ S := add_nonneg (norm_nonneg _) (norm_nonneg _)
  let G (E : FiniteSubspace V) := (exists_galerkinSolution j T hT a M α C ha f u₀ E).some
  have hbound (E : FiniteSubspace V) :
      ‖embeddedCurve j E (G E).curve‖ + ‖(G E).value‖ ≤ KG * S :=
    hGb a ha f u₀ E (G E)
  have hzbound : ∀ᶠ E : FiniteSubspace V in atTop, ‖(G E).value‖ ≤ KG * S :=
    Eventually.of_forall fun E => (le_add_of_nonneg_left (norm_nonneg _)).trans (hbound E)
  obtain ⟨u, hu, F, hF, hFl, hweak⟩ :=
    exists_weak_limit_of_eventually_norm_le (fun E => (G E).value) (KG * S) hzbound
  let : F.NeBot := hF
  obtain ⟨L, hLn, hL⟩ := operator_action T a M
    (ha.bounds.mono fun _ ht => ht.1) ha.strong_measurable
  let g := f - L u
  have hd : HilbertTripleSpec.tripleDerivativeValue j T u g := by
    apply tripleDerivative_of_weak_limit j T L f (fun E => (G E).value) u hweak
    intro v φ hφ
    exact (eventually_galerkin_test_identity j T hT a M α C ha f u₀ L hL G v φ hφ).filter_mono hFl
  obtain ⟨tr, hrep, _huniq, _htrbound, he⟩ := hilbertTriple_trace j T hTpos
  let zz : HilbertTripleSpec.energySpaceValue j T := ⟨(u, g), hd⟩
  let c := tr zz
  have hc : Represents j T u c := hrep zz
  have hinit : c ⟨0, by simp [hT]⟩ = u₀ := by
    apply initial_trace_of_weak_limit_affine_identity j T hTpos L f
      (fun E => (G E).value) u hweak hd c hc u₀
    intro v
    exact (eventually_galerkin_affine_identity j T hT hTpos a M α C ha f u₀ L hL G v).filter_mono hFl
  have hge : ∀ᵐ t ∂HilbertTripleSpec.timeMeasureValue T,
      g t = f t - formOperator a M t (u t) := by
    filter_upwards [Lp.coeFn_sub f (L u), hL u] with t ht hLt
    simpa only [g, Pi.sub_apply, hLt] using ht
  let z : WeakSolution j T hT a M f u₀ :=
    { value := u
      derivative := g
      curve := c
      represents := hc
      has_derivative := hd
      equation := hge
      initial := hinit }
  refine ⟨G, z, ?_, ?_, F, hF, hFl, hweak⟩
  · intro E
    exact (hbound E).trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right hKW) hS)
  · have hgn : ‖g‖ ≤ ‖f‖ + max M 0 * ‖u‖ := by
      exact (norm_sub_le _ _).trans (add_le_add le_rfl
        ((L.le_opNorm u).trans (mul_le_mul_of_nonneg_right hLn (norm_nonneg u))))
    have hcn : ‖c‖ ≤ B * (‖u‖ + ‖g‖) :=
      triple_curve_norm_bound_of_energy j T hTpos u g c hc (fun s t => (he zz s t).2)
    have hug : ‖u‖ + ‖g‖ ≤ D * S := by
      have hm : 0 ≤ max M 0 := le_max_right _ _
      have hfs : ‖f‖ ≤ S := le_add_of_nonneg_left (norm_nonneg u₀)
      dsimp only [D]
      nlinarith [mul_le_mul_of_nonneg_left hu (add_nonneg zero_le_one hm)]
    change ‖c‖ + ‖u‖ + ‖g‖ ≤ (KG + KW) * S
    calc
      ‖c‖ + ‖u‖ + ‖g‖ ≤ (B + 1) * (‖u‖ + ‖g‖) := by nlinarith
      _ ≤ (B + 1) * (D * S) :=
        mul_le_mul_of_nonneg_left hug (by positivity)
      _ = KW * S := by dsimp only [KW]; ring
      _ ≤ (KG + KW) * S := mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left hKG) hS

/-- The complete inclusion-directed Galerkin existence theorem, including
zero time and a bound uniform over all forms with the displayed parameters. -/
theorem galerkin_existence : GalerkinExistenceExpected.{u,v} := by
  intro V H _ _ _ _ _ _ j T hT M α C
  rcases eq_or_lt_of_le hT with hTzero | hTpos
  · subst T
    exact galerkin_existence_zero j M α C
  · exact galerkin_existence_pos j T hT hTpos M α C

end Forms
end ParabolicGalerkin
end ExpandedFA.Evolution

/- Mathlib proof attribution
Adapted portion near line 434:
The factorial estimate for the iterated approximation in the parabolic
Galerkin construction.

Upstream: Mathlib/Analysis/ODE/PicardLindelof.lean (around line 329)
Revision: 56a005855ea17e0b0958f73ec801ae140b0a1679
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Winston Yin

See THIRD_PARTY_NOTICES.md for source links and the Apache 2.0 license.
-/
