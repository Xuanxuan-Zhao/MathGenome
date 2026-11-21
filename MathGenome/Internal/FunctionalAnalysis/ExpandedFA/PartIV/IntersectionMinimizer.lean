import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.IntersectionMinimizer
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.Order.IsLUB
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C05BidualIsometry

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace ExpandedFA.PartIV.IntersectionMinimizer

theorem sum_norm : Spec.SumNorm := by
  intro u
  exact WithLp.prod_norm_eq_of_L1 u.val

/-- The two coordinates represent the same function a.e. -/
theorem compatible_ae (u : E) : (toL1 u : ℝ → ℝ) =ᵐ[volume] (toL2 u : ℝ → ℝ) := by
  exact Filter.EventuallyEq.of_eq (congrArg (fun f : ℝ →ₘ[volume] ℝ => (f : ℝ → ℝ)) u.property)

/-- Identifies limits in the two Lp spaces using uniqueness of convergence in measure. -/
theorem compatiblePairs_closed : IsClosed (compatiblePairs : Set Ambient) := by
  apply isSeqClosed_iff_isClosed.mp
  intro s p hs hlim
  have h1 := tendstoInMeasure_of_tendsto_Lp
    ((WithLp.continuous_fst 1 RealL1 RealL2 : Continuous (fun q : Ambient => q.fst)).tendsto p |>.comp hlim)
  have h2 := tendstoInMeasure_of_tendsto_Lp
    ((WithLp.continuous_snd 1 RealL1 RealL2 : Continuous (fun q : Ambient => q.snd)).tendsto p |>.comp hlim)
  have heq (n : ℕ) : ((s n).fst : ℝ → ℝ) =ᵐ[volume] ((s n).snd : ℝ → ℝ) :=
    Filter.EventuallyEq.of_eq (congrArg (fun f : ℝ →ₘ[volume] ℝ => (f : ℝ → ℝ)) (hs n))
  exact AEEqFun.ext (tendstoInMeasure_ae_unique (h1.congr_left heq) h2)

/-- Completeness is for the displayed sum norm, including its native uniformity. -/
theorem intersection_complete : Spec.Completeness :=
  compatiblePairs_closed.completeSpace_coe

/-- The ordinary mass is a bounded linear functional on the intersection. -/
def massCLM : E →L[ℝ] ℝ :=
  (L1.integralCLM (α := ℝ) (E := ℝ) (μ := volume)).comp toL1

theorem massCLM_apply (u : E) : massCLM u = mass u := by
  exact (L1.integral_eq (toL1 u)).symm.trans (L1.integral_eq_integral _)

theorem toL2_injective : Function.Injective toL2 := by
  intro u v h
  apply Subtype.ext
  apply (WithLp.equiv 1 (RealL1 × RealL2)).injective
  apply Prod.ext
  · apply Subtype.ext
    exact u.property.trans ((congrArg Subtype.val h).trans v.property.symm)
  · exact h

theorem representative_integrable (u : E) : Integrable (representative u) :=
  L1.integrable_coeFn (toL1 u)

theorem mass_abs_le (u : E) : |mass u| ≤ ‖toL1 u‖ := by
  simpa [mass, representative, ← L1.integral_eq_integral] using L1.norm_integral_le (toL1 u)

theorem mass_norm_le_one : ‖massCLM‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  rw [massCLM_apply, Real.norm_eq_abs, one_mul, sum_norm u]
  exact (mass_abs_le u).trans (le_add_of_nonneg_right (norm_nonneg _))

theorem mass_abs_lt (u : E) (hu : u ≠ 0) : |mass u| < ‖u‖ := by
  have h2 : toL2 u ≠ 0 := fun h => hu (toL2_injective (h.trans (map_zero toL2).symm))
  rw [sum_norm u]
  exact lt_of_le_of_lt (mass_abs_le u) (lt_add_of_pos_right _ (norm_pos_iff.mpr h2))

/-- The interval test used for the norm of mass. Its length is r², so its
L² norm is r, with no limiting square-root manipulation needed. -/
def intervalBlock (r : ℝ) : E :=
  ofFunction ((Set.Icc 0 (r ^ 2)).indicator (fun _ => (1 : ℝ)))
    (memLp_indicator_const 1 measurableSet_Icc.nullMeasurableSet 1
      (Or.inr (measure_Icc_lt_top.ne)))
    (memLp_indicator_const 2 measurableSet_Icc.nullMeasurableSet 1
      (Or.inr (measure_Icc_lt_top.ne)))

theorem intervalBlock_mass (r : ℝ) : mass (intervalBlock r) = r ^ 2 := by
  rw [mass]
  have heq : representative (intervalBlock r) =ᵐ[volume]
      (Set.Icc 0 (r ^ 2)).indicator (fun _ => (1 : ℝ)) :=
    MemLp.coeFn_toLp (memLp_indicator_const 1 measurableSet_Icc.nullMeasurableSet 1
      (Or.inr measure_Icc_lt_top.ne))
  rw [integral_congr_ae heq, integral_indicator measurableSet_Icc]
  simp [Real.volume_Icc, measureReal_def, ENNReal.toReal_ofReal (sq_nonneg r)]

theorem intervalBlock_norm (r : ℝ) (hr : 0 ≤ r) :
    ‖intervalBlock r‖ = r ^ 2 + r := by
  rw [sum_norm]
  change ‖indicatorConstLp 1 measurableSet_Icc (measure_Icc_lt_top.ne) (1 : ℝ)‖ +
    ‖indicatorConstLp 2 measurableSet_Icc (measure_Icc_lt_top.ne) (1 : ℝ)‖ = _
  rw [norm_indicatorConstLp (by simp) (by simp), norm_indicatorConstLp (by simp) (by simp)]
  simp only [norm_one, one_mul, ENNReal.toReal_one, div_one, Real.rpow_one,
    ENNReal.toReal_ofNat]
  have hm : (volume : Measure ℝ).real (Set.Icc 0 (r ^ 2)) = r ^ 2 := by
    simp [measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (sq_nonneg r)]
  rw [hm, ← Real.sqrt_eq_rpow, Real.sqrt_sq hr]

theorem mass_norm : ‖massCLM‖ = 1 := by
  apply le_antisymm mass_norm_le_one
  by_contra! h
  let r : ℝ := (‖massCLM‖ + 1) / (1 - ‖massCLM‖)
  have hden : 0 < 1 - ‖massCLM‖ := sub_pos.mpr h
  have hr : 0 < r := div_pos (by positivity) hden
  have he : (1 - ‖massCLM‖) * r = ‖massCLM‖ + 1 := by
    dsimp [r]
    field_simp
  have hb := massCLM.le_opNorm (intervalBlock r)
  rw [massCLM_apply, intervalBlock_mass, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
    intervalBlock_norm r hr.le] at hb
  nlinarith

/-- Reflexivity would turn a Hahn–Banach normer of the mass functional into
an element attaining its norm, contradicting `mass_abs_lt`. -/
theorem intersection_nonreflexive : Spec.Nonreflexivity := by
  intro h
  obtain ⟨G, hG, hGL⟩ := ExpandedFA.P1.C05Norming.norming_functional
    ℝ (E →L[ℝ] ℝ) massCLM
  obtain ⟨u, hu⟩ := h G
  have hnorm : ‖u‖ ≤ 1 := by
    have hn := ExpandedFA.P1.C05BidualIsometry.canonicalEvaluation_norm ℝ E u
    rw [hu] at hn
    exact hn ▸ hG
  have hmass : mass u = 1 := by
    have hv := congrArg (fun f : (E →L[ℝ] ℝ) →L[ℝ] ℝ => f massCLM) hu
    change massCLM u = G massCLM at hv
    rw [massCLM_apply, hGL, mass_norm] at hv
    exact hv
  have hu0 : u ≠ 0 := by
    intro hu0
    have : mass u = 0 := by rw [← massCLM_apply, hu0, map_zero]
    linarith
  have := mass_abs_lt u hu0
  rw [hmass, abs_one] at this
  exact (this.trans_le hnorm).false

@[fun_prop] theorem weight_measurable (α : ℝ) : Measurable (weight α) :=
  (continuous_abs.measurable : Measurable (fun x : ℝ => |x|)).pow_const _

theorem weight_nonneg (α x : ℝ) : 0 ≤ weight α x := Real.rpow_nonneg (abs_nonneg _) _

/-- The only singular integrability estimate needed is 2α < 1 in dimension one. -/
theorem local_weight : Spec.LocalWeight := by
  intro α _ hα R _
  have hm : AEStronglyMeasurable (fun x => weight α x ^ 2) (volume : Measure ℝ) :=
    ((weight_measurable α).pow_const 2).aestronglyMeasurable
  have hi : LocallyIntegrable (fun x => weight α x ^ 2) (volume : Measure ℝ) := by
    apply locallyIntegrable_of_norm_le_rpow (C := 1) (α := 2 * α) (by simp)
    · simpa using (show 2 * α < 1 by linarith)
    · filter_upwards [] with x
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), one_mul, Real.norm_eq_abs]
      exact le_of_eq (by
        unfold weight
        rw [← Real.rpow_mul_natCast (abs_nonneg x)]
        congr 1
        ring)
    · exact hm
  apply (memLp_two_iff_integrable_sq ((weight_measurable α).indicator measurableSet_Icc
    |>.aestronglyMeasurable)).mpr
  have hint := hi.integrableOn_isCompact (isCompact_Icc (a := -R) (b := R))
  convert hint.integrable_indicator measurableSet_Icc using 1
  ext x
  by_cases hx : x ∈ Set.Icc (-R) R <;> simp [hx]

def nearWeight (α R : ℝ) : ℝ → ℝ := (Set.Icc (-R) R).indicator (weight α)
def farWeight (α R : ℝ) : ℝ → ℝ := (Set.Icc (-R) R)ᶜ.indicator (weight α)

theorem weight_split (α R x : ℝ) : weight α x = nearWeight α R x + farWeight α R x := by
  classical
  by_cases hx : x ∈ Set.Icc (-R) R <;> simp [nearWeight, farWeight, hx]

theorem farWeight_nonneg (α R x : ℝ) : 0 ≤ farWeight α R x := by
  exact Set.indicator_nonneg (fun _ _ => weight_nonneg _ _) _

theorem farWeight_bound {α R : ℝ} (hα : 0 < α) (hR : 0 < R) (x : ℝ) :
    ‖farWeight α R x‖ ≤ R ^ (-α) := by
  rw [Real.norm_eq_abs, abs_of_nonneg (farWeight_nonneg _ _ _)]
  by_cases hx : x ∈ Set.Icc (-R) R
  · simpa [farWeight, hx] using Real.rpow_nonneg hR.le (-α)
  · simp only [farWeight, Set.indicator_of_mem (Set.mem_compl hx)]
    apply Real.rpow_le_rpow_of_nonpos hR
    · exact le_of_not_gt fun h => hx ⟨(abs_lt.mp h).1.le, (abs_lt.mp h).2.le⟩
    · linarith

theorem farPairing_integrable {α R : ℝ} (hα : 0 < α) (hR : 0 < R) (u : E) :
    Integrable (fun x => farWeight α R x * representative u x) :=
  (representative_integrable u).bdd_mul
    ((weight_measurable α).indicator measurableSet_Icc.compl).aestronglyMeasurable
    (Filter.Eventually.of_forall (farWeight_bound hα hR))

theorem farPairing_norm_le {α R : ℝ} (hα : 0 < α) (hR : 0 < R) (u : E) :
    ‖∫ x, farWeight α R x * representative u x‖ ≤ R ^ (-α) * ‖toL1 u‖ := by
  calc
    _ ≤ ∫ x, R ^ (-α) * ‖representative u x‖ := by
      apply norm_integral_le_of_norm_le ((representative_integrable u).norm.const_mul _)
      filter_upwards [] with x
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (farWeight_bound hα hR x) (norm_nonneg _)
    _ = _ := by
      rw [integral_const_mul]
      exact congrArg (fun t => R ^ (-α) * t) (L1.norm_eq_integral_norm (toL1 u)).symm

/-- Uniform far-tail control uses only positivity and the mass constraint. -/
theorem uniform_tail : Spec.UniformTail := by
  intro α hα _ R hR u hu
  have hfi := farPairing_integrable hα hR u
  have heq : (fun x => farWeight α R x * representative u x) =
      (Set.Icc (-R) R)ᶜ.indicator (fun x => weight α x * representative u x) := by
    ext x
    by_cases hx : x ∈ (Set.Icc (-R) R)ᶜ <;> simp [farWeight, hx]
  have hi : IntegrableOn (fun x => weight α x * representative u x) (Set.Icc (-R) R)ᶜ := by
    rw [← integrable_indicator_iff measurableSet_Icc.compl]
    rwa [← heq]
  refine ⟨hi, integral_nonneg_of_ae ?_, ?_⟩
  · exact (ae_restrict_of_ae hu.1).mono fun x hx => mul_nonneg (weight_nonneg _ _) hx
  · rw [← integral_indicator measurableSet_Icc.compl, ← heq]
    calc
      _ ≤ ∫ x, R ^ (-α) * representative u x := by
        apply integral_mono_ae hfi ((representative_integrable u).const_mul _)
        filter_upwards [hu.1] with x hx
        apply mul_le_mul_of_nonneg_right _ hx
        exact (le_abs_self _).trans (farWeight_bound hα hR x)
      _ = R ^ (-α) * mass u := by rw [integral_const_mul]; rfl
      _ ≤ R ^ (-α) := by
        simpa using mul_le_mul_of_nonneg_left hu.2 (Real.rpow_nonneg hR.le (-α))

/-- The near part is an ordinary continuous L² pairing. -/
def nearPairingCLM (α : ℝ) (hα : 0 < α) (ha : α < 1 / 2) (R : ℝ) (hR : 0 < R) :
    E →L[ℝ] ℝ :=
  (innerSL ℝ ((local_weight α hα ha R hR).toLp (nearWeight α R))).comp toL2

theorem nearPairingCLM_apply (α : ℝ) (hα : 0 < α) (ha : α < 1 / 2)
    (R : ℝ) (hR : 0 < R) (u : E) :
    nearPairingCLM α hα ha R hR u = ∫ x, nearWeight α R x * representative u x := by
  change inner ℝ ((local_weight α hα ha R hR).toLp (nearWeight α R)) (toL2 u) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(local_weight α hα ha R hR).coeFn_toLp, compatible_ae u] with x hx hu
  change ((local_weight α hα ha R hR).toLp (nearWeight α R)) x = nearWeight α R x at hx
  simp [hx, hu, representative, RCLike.inner_apply, mul_comm]

theorem nearPairing_integrable (α : ℝ) (hα : 0 < α) (ha : α < 1 / 2)
    (R : ℝ) (hR : 0 < R) (u : E) :
    Integrable (fun x => nearWeight α R x * representative u x) := by
  have h2 : MemLp (representative u) 2 (volume : Measure ℝ) :=
    (memLp_congr_ae (compatible_ae u)).mpr (Lp.memLp (toL2 u))
  exact (local_weight α hα ha R hR).integrable_mul h2

/-- In particular, the full Bochner integral is finite for every element of E. -/
theorem pairing_integrable (α : ℝ) (hα : 0 < α) (ha : α < 1 / 2) (u : E) :
    Integrable (fun x => weight α x * representative u x) := by
  have := (nearPairing_integrable α hα ha 1 zero_lt_one u).add
    (farPairing_integrable hα zero_lt_one u)
  convert this using 1
  ext x
  rw [weight_split α 1, add_mul]
  rfl

/-- Boundedness of the far part, as a linear functional on the sum-norm space. -/
def farPairingCLM (α : ℝ) (hα : 0 < α) : E →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun u => ∫ x, farWeight α 1 x * representative u x
      map_add' := by
        intro u v
        rw [← integral_add (farPairing_integrable hα zero_lt_one u)
          (farPairing_integrable hα zero_lt_one v)]
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_add (toL1 u) (toL1 v)] with x hx
        change farWeight α 1 x * (toL1 (u + v)) x = _
        rw [map_add, hx, Pi.add_apply, mul_add]
        rfl
      map_smul' := by
        intro c u
        rw [← integral_smul]
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_smul c (toL1 u)] with x hx
        change farWeight α 1 x * (toL1 (c • u)) x = _
        rw [map_smul, hx]
        simp [mul_left_comm, representative] }
    1 (by
      intro u
      have hb := farPairing_norm_le hα zero_lt_one u
      simp only [Real.one_rpow, one_mul] at hb ⊢
      exact hb.trans (by rw [sum_norm]; exact le_add_of_nonneg_right (norm_nonneg _)))

theorem pairing_continuity : Spec.PairingContinuity := by
  intro α hα ha
  refine ⟨pairing_integrable α hα ha, nearPairingCLM α hα ha 1 zero_lt_one +
    farPairingCLM α hα, ?_⟩
  intro u
  rw [add_apply, nearPairingCLM_apply]
  change (∫ x, nearWeight α 1 x * representative u x) +
    (∫ x, farWeight α 1 x * representative u x) = _
  rw [← integral_add (nearPairing_integrable α hα ha 1 zero_lt_one u)
    (farPairing_integrable hα zero_lt_one u)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by dsimp only; rw [← add_mul, ← weight_split]

theorem nonneg_eLpNorm_one {v : ℝ → ℝ} (hv : Integrable v)
    (hp : ∀ᵐ x, 0 ≤ v x) : eLpNorm v 1 volume = ENNReal.ofReal (∫ x, v x) := by
  rw [(memLp_one_iff_integrable.mpr hv).eLpNorm_eq_integral_rpow_norm
    one_ne_zero ENNReal.one_ne_top]
  simp only [ENNReal.toReal_one, Real.rpow_one, inv_one]
  congr 1
  apply integral_congr_ae
  exact hp.mono fun x hx => Real.norm_of_nonneg hx

theorem l2Feasible_iff (v : RealL2) :
    L2Feasible v ↔ (∀ᵐ x, 0 ≤ v x) ∧ eLpNorm (fun x => v x) 1 volume ≤ 1 := by
  constructor
  · rintro ⟨hp, hi, hm⟩
    refine ⟨hp, ?_⟩
    rw [nonneg_eLpNorm_one hi hp]
    simpa using ENNReal.ofReal_le_ofReal hm
  · rintro ⟨hp, hb⟩
    have hi : Integrable (fun x => v x) :=
      memLp_one_iff_integrable.mp (hb.trans_lt (by simp))
    refine ⟨hp, hi, ?_⟩
    rw [nonneg_eLpNorm_one hi hp] at hb
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity : (0 : ℝ) ≤ 1)).mp (by simpa using hb)

/-- The mass bound is closed in L² even though the mass functional itself is
not defined continuously on all of L²(ℝ). -/
theorem l2Feasible_closed : IsClosed {v : RealL2 | L2Feasible v} := by
  apply isSeqClosed_iff_isClosed.mp
  intro v z hv hz
  have hm := tendstoInMeasure_of_tendsto_Lp hz
  have hb : eLpNorm (fun x => z x) 1 volume ≤ 1 := by
    apply eLpNorm_le_of_tendstoInMeasure
      (Filter.Eventually.of_forall fun n => ((l2Feasible_iff (v n)).mp (hv n)).2)
      hm (fun n => Lp.aestronglyMeasurable _)
  obtain ⟨k, _, hae⟩ := hm.exists_seq_tendsto_ae
  apply (l2Feasible_iff z).mpr
  refine ⟨?_, hb⟩
  filter_upwards [hae, ae_all_iff.mpr (fun n => (hv (k n)).1)] with x hx hp
  exact ge_of_tendsto hx (Filter.Eventually.of_forall hp)

theorem l2Feasible_convex : Convex ℝ {v : RealL2 | L2Feasible v} := by
  intro v hv z hz a b ha hb hab
  have heq : (fun x => (a • v + b • z) x) =ᵐ[volume] (fun x => a * v x + b * z x) := by
    filter_upwards [Lp.coeFn_add (a • v) (b • z), Lp.coeFn_smul a v, Lp.coeFn_smul b z]
      with x hadd h1 h2
    calc
      _ = (a • v) x + (b • z) x := hadd
      _ = _ := by rw [h1, h2]; rfl
  refine ⟨?_, ((hv.2.1.const_mul a).add (hz.2.1.const_mul b)).congr heq.symm, ?_⟩
  · filter_upwards [heq, hv.1, hz.1] with x he hp hq
    rw [he]
    positivity
  · rw [integral_congr_ae heq, integral_add (hv.2.1.const_mul a) (hz.2.1.const_mul b),
      integral_const_mul, integral_const_mul]
    calc
      _ ≤ a * 1 + b * 1 := add_le_add (mul_le_mul_of_nonneg_left hv.2.2 ha)
        (mul_le_mul_of_nonneg_left hz.2.2 hb)
      _ = 1 := by simpa using hab

/-- Transfer the norm-closed convex constraint set to the weak topology.
This proves both integrability and the mass bound of a weak limit. -/
theorem weak_feasibility : Spec.WeakFeasibility := by
  intro v z hv hz
  have hi : Function.Injective (topDualPairing ℝ RealL2).flip := by
    intro x y h
    apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
    intro f
    exact congrArg (fun l : (RealL2 →L[ℝ] ℝ) →ₗ[ℝ] ℝ => l f) h
  have ht : Tendsto (fun n => toWeakSpace ℝ RealL2 (v n)) atTop
      (𝓝 (toWeakSpace ℝ RealL2 z)) :=
    (WeakBilin.tendsto_iff_forall_eval_tendsto _ hi).mpr hz
  have hc : IsClosed (toWeakSpace ℝ RealL2 '' {v : RealL2 | L2Feasible v}) := by
    apply isClosed_of_closure_subset
    rw [← l2Feasible_convex.toWeakSpace_closure ℝ, l2Feasible_closed.closure_eq]
  obtain ⟨w, hw, he⟩ := hc.mem_of_tendsto ht
    (Filter.Eventually.of_forall fun n => ⟨v n, hv n, rfl⟩)
  exact (toWeakSpace ℝ RealL2).injective he ▸ hw

/-- Truncation error on feasible elements. -/
theorem pairing_near_error (α : ℝ) (hα : 0 < α) (ha : α < 1 / 2)
    (R : ℝ) (hR : 0 < R) (u : E) (hu : Feasible u) :
    |pairing α u - nearPairingCLM α hα ha R hR u| ≤ R ^ (-α) := by
  have he : pairing α u - nearPairingCLM α hα ha R hR u =
      ∫ x in (Set.Icc (-R) R)ᶜ, weight α x * representative u x := by
    rw [nearPairingCLM_apply, ← integral_indicator measurableSet_Icc.compl]
    have hi := farPairing_integrable hα hR u
    have hn := nearPairing_integrable α hα ha R hR u
    change (∫ x, weight α x * representative u x) -
      (∫ x, nearWeight α R x * representative u x) = _
    rw [← integral_sub (pairing_integrable α hα ha u) hn]
    apply integral_congr_ae
    filter_upwards [] with x
    change weight α x * representative u x - nearWeight α R x * representative u x = _
    rw [weight_split α R]
    by_cases hx : x ∈ Set.Icc (-R) R <;> simp [nearWeight, farWeight, hx]
  rw [he, abs_of_nonneg (uniform_tail α hα ha R hR u hu).2.1]
  exact (uniform_tail α hα ha R hR u hu).2.2

/-- Uniform tail control upgrades convergence of every truncated L² pairing. -/
theorem weak_pairing : Spec.WeakPairing := by
  intro α hα ha u z hu hz hw
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hb := (tendsto_rpow_neg_atTop hα).eventually
    (gt_mem_nhds (show (0 : ℝ) < ε / 3 by positivity))
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.1
    (hb.and (eventually_gt_atTop (0 : ℝ)))
  have hRpos : 0 < R := (hR R le_rfl).2
  have hRsmall : R ^ (-α) < ε / 3 := (hR R le_rfl).1
  let w : RealL2 := (local_weight α hα ha R hRpos).toLp (nearWeight α R)
  have ht := hw (innerSL ℝ w)
  have htest := (Metric.tendsto_atTop.mp ht) (ε / 3) (by positivity)
  obtain ⟨N, hN⟩ := htest
  refine ⟨N, fun n hn => ?_⟩
  have hh := hN n hn
  change dist (nearPairingCLM α hα ha R hRpos (u n))
    (nearPairingCLM α hα ha R hRpos z) < ε / 3 at hh
  have he1 := pairing_near_error α hα ha R hRpos (u n) (hu n)
  have he2 := pairing_near_error α hα ha R hRpos z hz
  rw [Real.dist_eq] at hh ⊢
  calc
    _ ≤ |pairing α (u n) - nearPairingCLM α hα ha R hRpos (u n)| +
        |nearPairingCLM α hα ha R hRpos (u n) - nearPairingCLM α hα ha R hRpos z| +
        |pairing α z - nearPairingCLM α hα ha R hRpos z| := by
      simpa only [Real.dist_eq, abs_sub_comm] using dist_triangle4 (pairing α (u n))
        (nearPairingCLM α hα ha R hRpos (u n)) (nearPairingCLM α hα ha R hRpos z) (pairing α z)
    _ < ε := by linarith

theorem feasible_iff_toL2 (u : E) : Feasible u ↔ L2Feasible (toL2 u) := by
  have he := compatible_ae u
  have hi : Integrable (fun x => toL2 u x) := (representative_integrable u).congr he
  have hm : mass u = ∫ x, toL2 u x := integral_congr_ae he
  constructor
  · rintro ⟨hp, hb⟩
    refine ⟨?_, hi, hm ▸ hb⟩
    filter_upwards [hp, he] with x hp hx
    rwa [← hx]
  · rintro ⟨hp, _, hb⟩
    refine ⟨?_, hm.symm ▸ hb⟩
    filter_upwards [hp, he] with x hp hx
    change 0 ≤ (toL1 u) x
    rwa [hx]

/-- Every feasible L² limit canonically belongs to the intersection. -/
def fromL2 (v : RealL2) (hv : L2Feasible v) : E :=
  ofFunction v (memLp_one_iff_integrable.mpr hv.2.1) (Lp.memLp v)

theorem toL2_fromL2 (v : RealL2) (hv : L2Feasible v) : toL2 (fromL2 v hv) = v :=
  Lp.ext (MemLp.coeFn_toLp (Lp.memLp v))

theorem fromL2_feasible (v : RealL2) (hv : L2Feasible v) : Feasible (fromL2 v hv) := by
  rw [feasible_iff_toL2, toL2_fromL2]
  exact hv

theorem feasible_convex : Convex ℝ {u : E | Feasible u} := by
  have heq : {u : E | Feasible u} = toL2 ⁻¹' {v : RealL2 | L2Feasible v} :=
    Set.ext fun u => feasible_iff_toL2 u
  rw [heq]
  exact l2Feasible_convex.linear_preimage toL2.toLinearMap

theorem feasible_zero : Feasible 0 := by
  refine ⟨?_, ?_⟩
  · change ∀ᵐ x, 0 ≤ (toL1 (0 : E)) x
    rw [map_zero]
    exact (Lp.coeFn_zero (α := ℝ) (E := ℝ) (p := 1) (μ := volume)).mono (fun _ h => by rw [h]; rfl)
  · rw [← massCLM_apply, map_zero]
    norm_num

def nearNorm (α : ℝ) (hα : 0 < α) (ha : α < 1 / 2) : ℝ :=
  ‖(local_weight α hα ha 1 zero_lt_one).toLp (nearWeight α 1)‖

theorem pairing_upper (α : ℝ) (hα : 0 < α) (ha : α < 1 / 2) (u : E) (hu : Feasible u) :
    pairing α u ≤ nearNorm α hα ha * ‖toL2 u‖ + 1 := by
  have he := pairing_near_error α hα ha 1 zero_lt_one u hu
  simp only [Real.one_rpow] at he
  have hn := real_inner_le_norm
    ((local_weight α hα ha 1 zero_lt_one).toLp (nearWeight α 1)) (toL2 u)
  change nearPairingCLM α hα ha 1 zero_lt_one u ≤ nearNorm α hα ha * ‖toL2 u‖ at hn
  have := le_abs_self (pairing α u - nearPairingCLM α hα ha 1 zero_lt_one u)
  linarith

theorem energy_lower (α : ℝ) (hα : 0 < α) (ha : α < 1 / 2) (u : E) (hu : Feasible u) :
    -(nearNorm α hα ha) ^ 2 - 1 ≤ energy α u := by
  have hp := pairing_upper α hα ha u hu
  have hn : 0 ≤ nearNorm α hα ha := norm_nonneg _
  have hr := norm_nonneg (toL2 u)
  dsimp only [energy]
  nlinarith [sq_nonneg (‖toL2 u‖ - nearNorm α hα ha)]

/-- A fixed energy sublevel is bounded in L², independently of the E norm. -/
theorem energy_sublevel_bound (α : ℝ) (hα : 0 < α) (ha : α < 1 / 2)
    (c : ℝ) (u : E) (hu : Feasible u) (he : energy α u ≤ c) :
    ‖toL2 u‖ ≤ nearNorm α hα ha + |c| + 2 := by
  have hp := pairing_upper α hα ha u hu
  have hn : 0 ≤ nearNorm α hα ha := norm_nonneg _
  have hc := le_abs_self c
  dsimp only [energy] at he
  by_contra! hb
  have h1 : 0 ≤ ‖toL2 u‖ - 1 := by linarith [abs_nonneg c]
  have h2 : 0 ≤ ‖toL2 u‖ - nearNorm α hα ha := by linarith [abs_nonneg c]
  nlinarith [mul_nonneg h1 h2]

/-- Sequential weak compactness in the real Hilbert space L², obtained from
Riesz representation and sequential Banach–Alaoglu. No reflexivity of E is used. -/
theorem l2_weak_subsequence (v : ℕ → RealL2) (C : ℝ) (hb : ∀ n, ‖v n‖ ≤ C) :
    ∃ (z : RealL2) (k : ℕ → ℕ), StrictMono k ∧ WeakL2Converges (v ∘ k) z := by
  have : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let j := InnerProductSpace.toDual ℝ RealL2
  let q : ℕ → WeakDual ℝ RealL2 := fun n => (j (v n)).toWeakDual
  have hq : ∀ n, q n ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 C := by
    intro n
    change dist (j (v n)) 0 ≤ C
    simpa using hb n
  obtain ⟨g, _, k, hk, ht⟩ :=
    (WeakDual.isSeqCompact_closedBall (𝕜 := ℝ) (E := RealL2) 0 C) hq
  let z := j.symm (WeakDual.toStrongDual g)
  refine ⟨z, k, hk, ?_⟩
  intro f
  have hx := (WeakDual.eval_continuous (𝕜 := ℝ) (j.symm f)).tendsto g |>.comp ht
  convert hx using 1
  · ext n
    change f (v (k n)) = inner ℝ (v (k n)) (j.symm f)
    rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
  · change 𝓝 (f z) = 𝓝 (WeakDual.toStrongDual g (j.symm f))
    congr 1
    rw [← InnerProductSpace.toDual_symm_apply, real_inner_comm]
    exact (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (y := WeakDual.toStrongDual g))

/-- The squared L² norm is lower semicontinuous along weak sequences. -/
theorem norm_sq_le_of_weak_limit (v : ℕ → RealL2) (z : RealL2) (c : ℝ)
    (hw : WeakL2Converges v z) (hc : Tendsto (fun n => ‖v n‖ ^ 2) atTop (𝓝 c)) :
    ‖z‖ ^ 2 ≤ c := by
  have ht := hw (innerSL ℝ z)
  have hleft : Tendsto (fun n => 2 * inner ℝ z (v n)) atTop (𝓝 (2 * ‖z‖ ^ 2)) := by
    simpa using ht.const_mul 2
  have hright := hc.const_add (‖z‖ ^ 2)
  have hle : 2 * ‖z‖ ^ 2 ≤ ‖z‖ ^ 2 + c :=
    le_of_tendsto_of_tendsto hleft hright (Filter.Eventually.of_forall fun n => by
      have hi := real_inner_le_norm z (v n)
      nlinarith [sq_nonneg (‖z‖ - ‖v n‖)])
  linarith

/-- The complete direct method takes place in L². -/
theorem minimizer_exists (α : ℝ) (hα : 0 < α) (ha : α < 1 / 2) :
    ∃ u : E, Feasible u ∧ ∀ v : E, Feasible v → energy α u ≤ energy α v := by
  let S : Set ℝ := energy α '' {u : E | Feasible u}
  have hS : S.Nonempty := ⟨energy α 0, 0, feasible_zero, rfl⟩
  have hSb : BddBelow S := ⟨-(nearNorm α hα ha)^2 - 1, by
    rintro _ ⟨u, hu, rfl⟩
    exact energy_lower α hα ha u hu⟩
  obtain ⟨e, heanti, helim, heS⟩ := exists_seq_tendsto_sInf hS hSb
  choose u hu heu using heS
  have hbound (n : ℕ) : ‖toL2 (u n)‖ ≤ nearNorm α hα ha + |e 0| + 2 := by
    apply energy_sublevel_bound α hα ha (e 0) (u n) (hu n)
    rw [heu n]
    exact heanti (Nat.zero_le n)
  obtain ⟨z, k, hk, hw⟩ := l2_weak_subsequence (fun n => toL2 (u n)) _ hbound
  have hz : L2Feasible z := weak_feasibility _ _
    (fun n => (feasible_iff_toL2 _).mp (hu (k n))) hw
  let w := fromL2 z hz
  have hweq : toL2 w = z := toL2_fromL2 z hz
  have hwfeas : Feasible w := fromL2_feasible z hz
  have hweak : WeakL2Converges (fun n => toL2 (u (k n))) (toL2 w) := hweq.symm ▸ hw
  have hpair := weak_pairing α hα ha (u ∘ k) w (fun n => hu _) hwfeas hweak
  have henergy : Tendsto (fun n => energy α (u (k n))) atTop (𝓝 (sInf S)) := by
    convert helim.comp hk.tendsto_atTop using 1
    ext n
    exact heu (k n)
  have hnormsq : Tendsto (fun n => ‖toL2 (u (k n))‖ ^ 2) atTop
      (𝓝 (sInf S + pairing α w)) := by
    convert henergy.add hpair using 1
    ext n
    dsimp [energy, Function.comp_def]
    ring
  have hls := norm_sq_le_of_weak_limit _ _ _ hweak hnormsq
  refine ⟨w, hwfeas, fun v hv => ?_⟩
  have hinf : sInf S ≤ energy α v := csInf_le hSb ⟨v, hv, rfl⟩
  dsimp only [energy] at hinf ⊢
  linarith

/-- The quadratic part has the exact strictly convex midpoint identity. -/
theorem energy_midpoint (α : ℝ) (hα : 0 < α) (ha : α < 1 / 2) (u v : E) :
    energy α ((1 / 2 : ℝ) • (u + v)) =
      (energy α u + energy α v) / 2 - ‖toL2 u - toL2 v‖ ^ 2 / 4 := by
  obtain ⟨_, L, hL⟩ := pairing_continuity α hα ha
  have hp : pairing α ((1 / 2 : ℝ) • (u + v)) =
      (pairing α u + pairing α v) / 2 := by
    rw [← hL, map_smul, map_add, hL, hL]
    simp [smul_eq_mul, div_eq_mul_inv, mul_comm]
  have hn : ‖toL2 ((1 / 2 : ℝ) • (u + v))‖ ^ 2 = ‖toL2 u + toL2 v‖ ^ 2 / 4 := by
    rw [map_smul, map_add, norm_smul]
    norm_num
    ring
  have hpar := parallelogram_law_with_norm ℝ (toL2 u) (toL2 v)
  dsimp only [energy]
  rw [hp, hn]
  nlinarith

/-- Strict convexity gives uniqueness for every 0 < α < 1/2. -/
theorem unique_minimizer : Spec.UniqueMinimizer := by
  intro α hα ha
  obtain ⟨u, hu, hmin⟩ := minimizer_exists α hα ha
  refine ⟨u, ⟨hu, hmin⟩, ?_⟩
  rintro v ⟨hv, hvmin⟩
  have hm : Feasible ((1 / 2 : ℝ) • (u + v)) := by
    have hh := feasible_convex hu hv (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
    change Feasible ((1 / 2 : ℝ) • u + (1 / 2 : ℝ) • v) at hh
    simpa only [smul_add] using hh
  have h1 := hmin _ hm
  have h2 := hmin v hv
  have h3 := hvmin u hu
  rw [energy_midpoint α hα ha] at h1
  have hn : ‖toL2 u - toL2 v‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖toL2 u - toL2 v‖]
  exact (toL2_injective (sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hn)))).symm

end ExpandedFA.PartIV.IntersectionMinimizer
