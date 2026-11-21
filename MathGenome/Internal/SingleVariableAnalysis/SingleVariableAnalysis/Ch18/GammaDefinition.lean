import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch18.GammaDefinition
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch10.SeveralEndpoints
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch10.PTest
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Existence of the real Gamma integral on its positive parameter domain.
Proof provenance: Mathlib's `Real.GammaIntegral_convergent` proves the
near-zero power bound and exponential tail domination. We transfer its
measure-integrability result to independent proper Darboux limits, using
the upstream Darboux Newton–Leibniz theorem for each regular truncation.
-/
noncomputable section
namespace SingleVariableAnalysis
open Set Filter MeasureTheory
open scoped Topology
open Riemann Riemann.Improper
namespace GSpec
export Specs.SingleVariableAnalysis.Ch18.GammaDefinition
  (gammaKernelValue gammaIntegralValue properTruncations independentLimits
    absoluteConvergence hasIntegral eqRealGamma positive)
end GSpec

def gammaKernel : ℝ → ℝ → ℝ := GSpec.gammaKernelValue
def gammaIntegral (s : ℝ) (hs : 0 < s) : ℝ := GSpec.gammaIntegralValue s hs

theorem gammaKernel_continuousAt (s t : ℝ) (ht : 0 < t) :
    ContinuousAt (gammaKernel s) t :=
  (Real.continuousAt_rpow_const t (s - 1) (Or.inl ht.ne')).mul
    (Real.continuous_exp.continuousAt.comp continuousAt_id.neg)

theorem gammaKernel_pos (s t : ℝ) (ht : 0 < t) : 0 < gammaKernel s t :=
  mul_pos (Real.rpow_pos_of_pos ht _) (Real.exp_pos _)

/-- On regular positive intervals the Darboux integral agrees with the
interval integral. The proof applies Newton–Leibniz to the latter's primitive. -/
theorem positive_continuous_darboux {f : ℝ → ℝ}
    (hf : ∀ x : ℝ, 0 < x → ContinuousAt f x)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ h : RealIntegrable f a b, realIntegral f h = ∫ x in a..b, f x := by
  have hc : ContinuousOn f (Ioi 0) := fun x hx => (hf x hx).continuousWithinAt
  have hmeas := ContinuousOn.stronglyMeasurableAtFilter (μ := volume) isOpen_Ioi hc
  obtain ⟨h, hh⟩ := PTest.integral_of_continuous_derivative hab
    (hc.mono (fun x hx => ha.trans_le hx.1))
    (F := fun y => ∫ x in a..y, f x) (fun y hy =>
      intervalIntegral.integral_hasDerivAt_right
        ((hc.mono (fun x hx => ha.trans_le ((le_min le_rfl hy.1).trans hx.1))).intervalIntegrable)
        (hmeas y (ha.trans_le hy.1)) (hf y (ha.trans_le hy.1)))
  exact ⟨h, by simpa using hh⟩

theorem gamma_proper_truncations : GSpec.properTruncations := by
  intro s u v hu huv
  exact positive_continuous_darboux (gammaKernel_continuousAt s) hu huv

theorem gammaKernel_integrable {s : ℝ} (hs : 0 < s) :
    IntegrableOn (gammaKernel s) (Ioi 0) := by
  change IntegrableOn (fun x : ℝ => x ^ (s - 1) * Real.exp (-x)) (Ioi 0)
  simpa only [mul_comm] using Real.GammaIntegral_convergent hs

theorem gamma_left_regular (s : ℝ) :
    LeftRegular .real (gammaKernel s) (0 : WithBot ℝ) 1 :=
  ⟨WithBot.coe_lt_coe.mpr zero_lt_one, fun t =>
    (gamma_proper_truncations s t.val 1
      (WithBot.coe_lt_coe.mp t.property.1) t.property.2.le).choose⟩

theorem gamma_right_regular (s : ℝ) :
    RightRegular .real (gammaKernel s) 1 ⊤ :=
  ⟨WithTop.coe_lt_top _, fun t =>
    (gamma_proper_truncations s 1 t.val zero_lt_one t.property.1.le).choose⟩

/-- Integrability and continuity on the positive half-line yield two
independent finite limits of proper Darboux integrals. -/
theorem positive_integrable_independent {f : ℝ → ℝ}
    (hf : ∀ x : ℝ, 0 < x → ContinuousAt f x)
    (hi : IntegrableOn f (Ioi 0)) :
    LeftHasIntegral .real f (0 : WithBot ℝ) 1 (show ℝ from ∫ x in (0 : ℝ)..1, f x) ∧
    RightHasIntegral .real f 1 ⊤ (show ℝ from ∫ x in Ioi (1 : ℝ), f x) := by
  have hp {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
      ∃ h : RealIntegrable f a b, realIntegral f h = ∫ x in a..b, f x :=
    positive_continuous_darboux hf ha hab
  have hleft : LeftRegular .real f (0 : WithBot ℝ) 1 :=
    ⟨WithBot.coe_lt_coe.mpr zero_lt_one, fun t =>
      (hp (WithBot.coe_lt_coe.mp t.property.1) t.property.2.le).choose⟩
  have hright : RightRegular .real f 1 ⊤ :=
    ⟨WithTop.coe_lt_top _, fun t => (hp zero_lt_one t.property.1.le).choose⟩
  have h01 : IntervalIntegrable f volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
      (hi.mono_set Ioc_subset_Ioi_self)
  have h01' : IntegrableOn f (uIcc (0 : ℝ) 1) := by
    simpa only [uIcc_of_le zero_le_one] using
      (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp h01
  have hl : Tendsto (fun t : ℝ => ∫ x in t..1, f x)
      (𝓝[>] 0) (𝓝 (∫ x in (0 : ℝ)..1, f x)) := by
    have hc := (intervalIntegral.continuousOn_primitive_interval_left h01') 0
      (show (0 : ℝ) ∈ uIcc (0 : ℝ) 1 from left_mem_uIcc)
    change Tendsto _ (𝓝[uIcc (0 : ℝ) 1] 0) _ at hc
    rw [uIcc_of_le zero_le_one, nhdsWithin_Icc_eq_nhdsGE zero_lt_one] at hc
    exact hc.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
  constructor
  · apply PTest.left_has_of_tendsto hleft _ hl
    intro t
    exact (hp (WithBot.coe_lt_coe.mp t.property.1) t.property.2.le).choose_spec
  · apply PTest.right_has_of_tendsto hright _
      (intervalIntegral_tendsto_integral_Ioi 1
        (hi.mono_set (Ioi_subset_Ioi zero_le_one)) tendsto_id)
    intro t
    exact (hp zero_lt_one t.property.1.le).choose_spec

theorem gamma_independent_limits : GSpec.independentLimits := by
  intro s hs
  exact positive_integrable_independent (gammaKernel_continuousAt s) (gammaKernel_integrable hs)

theorem gamma_absolute_convergence : GSpec.absoluteConvergence := by
  intro s hs
  obtain ⟨hl, hr⟩ := positive_integrable_independent
    (fun x hx => (gammaKernel_continuousAt s x hx).abs) (gammaKernel_integrable hs).abs
  exact ⟨⟨_, hl⟩, ⟨_, hr⟩⟩

theorem gamma_hasIntegral : GSpec.hasIntegral := by
  intro s hs
  refine ⟨?_, ⟨1, WithBot.coe_lt_coe.mpr zero_lt_one, WithTop.coe_lt_top _⟩, ?_⟩
  · intro u v hu huv _
    exact (gamma_proper_truncations s u v (WithBot.coe_lt_coe.mp hu) huv).choose
  · obtain ⟨hl, hr⟩ := gamma_independent_limits s hs
    exact ⟨_, _, hl, hr, rfl⟩

theorem gamma_eq_realGamma : GSpec.eqRealGamma := by
  intro s hs
  have hi := gammaKernel_integrable hs
  have he := intervalIntegral.integral_interval_add_Ioi hi
    (hi.mono_set (Ioi_subset_Ioi zero_le_one))
  change (∫ t in (0 : ℝ)..1, gammaKernel s t) +
    (∫ t in Ioi (1 : ℝ), gammaKernel s t) = Real.Gamma s
  rw [he, Real.Gamma_eq_integral hs]
  congr 1
  funext t
  exact mul_comm _ _

theorem gamma_positive : GSpec.positive := by
  intro s hs
  rw [gamma_eq_realGamma s hs]
  exact Real.Gamma_pos_of_pos hs

end SingleVariableAnalysis
