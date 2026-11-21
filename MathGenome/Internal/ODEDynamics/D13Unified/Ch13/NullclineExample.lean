import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch13.NullclineExample
import MathGenome.Internal.ODEDynamics.D13Unified.Ch13.Nullclines
import MathGenome.Internal.ODEDynamics.D13Unified.Ch02.ScalarLinear
import Mathlib.Analysis.Calculus.Deriv.Inverse

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace D13Unified.Ch13.NullclineExample
open Ch13.Nullclines Ch06.StateDerivative
open Specs.D13Unified.Ch13.NullclineExample

/-- The two polynomial components from the example. -/
def field : FieldType := fieldValue

/-- The autonomous equation on the full plane. -/
def equation : EquationType := equationValue

@[simp] lemma eval_equation (a : ℝ) (p : Plane) :
    (equation a).eval p = field a p := by
  simp [equation, AutonomousODE.eval,
    Specs.D13Unified.Ch01.AutonomousParameters.autonomousEvalValue, equationValue, field]

@[simp] lemma eval_equationValue (a : ℝ) (p : Plane) :
    Specs.D13Unified.Ch01.AutonomousParameters.autonomousEvalValue (equationValue a) p =
      fieldValue a p := eval_equation a p

@[simp] lemma equationValue_domain (a : ℝ) : (equationValue a).domain = univ := rfl

theorem regularity : Regularity := by
  intro a
  rw [show Specs.D13Unified.Ch01.AutonomousParameters.autonomousEvalValue
    (equationValue a) = fieldValue a from funext (eval_equationValue a)]
  exact (contDiff_fst.mul ((contDiff_const.sub contDiff_fst).sub contDiff_snd)).prodMk
    (contDiff_snd.mul (contDiff_fst.sub contDiff_const))

theorem nullclines : Nullclines := by
  intro a
  constructor
  · ext p
    simp only [Specs.D13Unified.Ch13.Nullclines.nullclineXValue, equationValue_domain,
      mem_ofPred_eq, mem_univ, true_and, eval_equationValue, fieldValue, mul_eq_zero]
    constructor
    · rintro (hx | hy)
      · exact Or.inl hx
      · exact Or.inr (by linarith)
    · rintro (hx | hy)
      · exact Or.inl hx
      · exact Or.inr (by linarith)
  · ext p
    simp only [Specs.D13Unified.Ch13.Nullclines.nullclineYValue, equationValue_domain,
      mem_ofPred_eq, mem_univ, true_and, eval_equationValue, fieldValue, mul_eq_zero,
      sub_eq_zero]

theorem equilibria : Equilibria := by
  intro a ha ha1
  ext p
  simp only [mem_ofPred_eq, eval_equationValue, fieldValue, Prod.mk_eq_zero,
    mul_eq_zero, sub_eq_zero, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨hx, hy, hF, hG⟩
    rcases hF with hF | hF <;> rcases hG with hG | hG
    · exact Or.inl (Prod.ext hF hG)
    · exact False.elim (by linarith)
    · exact Or.inr (Or.inl (Prod.ext (by linarith) hG))
    · exact Or.inr (Or.inr (Prod.ext hG (by linarith)))
  · rintro (rfl | rfl | rfl)
    · norm_num
    · norm_num
    · dsimp
      exact ⟨ha.le, (sub_pos.mpr ha1).le, Or.inr (by ring), Or.inr rfl⟩

theorem signs : Signs := by
  intro a p hx hy
  simp only [eval_equationValue, fieldValue, sign_mul,
    sign_pos hx, sign_pos hy, one_mul, and_self]

theorem phase_regions : PhaseRegions := by
  intro a p hx hy sx sy
  have hxp : 0 < p.1 * (1 - p.1 - p.2) ↔ p.2 < 1 - p.1 := by
    rw [mul_pos_iff_of_pos_left hx]
    constructor <;> intro h <;> linarith
  have hxn : p.1 * (1 - p.1 - p.2) < 0 ↔ 1 - p.1 < p.2 := by
    rw [← mul_zero p.1, mul_lt_mul_iff_right₀ hx]
    constructor <;> intro h <;> linarith
  have hyp : 0 < p.2 * (p.1 - a) ↔ a < p.1 := by
    rw [mul_pos_iff_of_pos_left hy, sub_pos]
  have hyn : p.2 * (p.1 - a) < 0 ↔ p.1 < a := by
    rw [← mul_zero p.2, mul_lt_mul_iff_right₀ hy, sub_neg]
  cases sx <;> cases sy <;>
    simpa only [Specs.D13Unified.Ch13.Nullclines.phaseRegionValue,
      Specs.D13Unified.Ch13.Nullclines.openQuadrantValue, equationValue_domain,
      mem_inter_iff, mem_univ, true_and, mem_preimage, mem_ofPred_eq,
      eval_equationValue, fieldValue, Bool.false_eq_true, ↓reduceIte] using
        (and_congr (by assumption) (by assumption))

/-- An integrating-factor consequence with no division by the unknown coordinate.
It therefore includes a zero initial coordinate and either orientation of time. -/
lemma homogeneous_formula (I : OpenTimeInterval) (u c : ℝ → ℝ)
    (hu : ContinuousOn u I.carrier) (hc : ContinuousOn c I.carrier)
    (h0 : 0 ∈ I.carrier)
    (hd : ∀ t ∈ I.carrier, HasDerivAt u (c t * u t) t) :
    ∀ t ∈ I.carrier, u t = u 0 * Real.exp (∫ s in (0 : ℝ)..t, c s) := by
  have hivp : ScalarLinear.IsIVP I.toTimeInterval c (fun _ => 0) 0 (u 0) u :=
    ⟨hu, h0, rfl, fun t ht => by simpa using (hd t ht).hasDerivWithinAt⟩
  have he := ScalarLinear.eq_variation_of_isIVP I.toTimeInterval c (fun _ => 0)
    0 (u 0) hc continuousOn_const hivp
  intro t ht
  simpa [ScalarLinear.variation, ScalarLinear.primitive, ← Real.exp_eq_exp_ℝ, mul_comm]
    using he ht

set_option backward.isDefEq.respectTransparency false in
lemma coordinate_derivatives (a : ℝ) (I : OpenTimeInterval) (z : ℝ → Plane)
    (hz : Specs.D13Unified.Ch01.AutonomousParameters.classicalAutonomousSolutionOnValue
      (equationValue a) I z) (t : ℝ) (ht : t ∈ I.carrier) :
    HasDerivAt (fun s => (z s).1) ((z t).1 * (1 - (z t).1 - (z t).2)) t ∧
    HasDerivAt (fun s => (z s).2) ((z t).2 * ((z t).1 - a)) t := by
  have hd := hz.2.2 t ht
  have hx := (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hd
  have hy := (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hd
  constructor
  · convert! hx using 1
    simp [fieldValue]
  · convert! hy using 1
    simp [fieldValue]

theorem solution_formulas : SolutionFormulas := by
  intro a I z hz h0 t ht
  have hx := hz.1.continuousOn.fst
  have hy := hz.1.continuousOn.snd
  constructor
  · exact homogeneous_formula I (fun s => (z s).1) (fun s => 1 - (z s).1 - (z s).2)
      hx ((continuousOn_const.sub hx).sub hy) h0
      (fun r hr => by simpa [mul_comm] using (coordinate_derivatives a I z hz r hr).1) t ht
  · exact homogeneous_formula I (fun s => (z s).2) (fun s => (z s).1 - a)
      hy (hx.sub continuousOn_const) h0
      (fun r hr => by simpa [mul_comm] using (coordinate_derivatives a I z hz r hr).2) t ht

theorem coordinate_invariance : CoordinateInvariance := by
  intro a I z hz h0 t ht
  obtain ⟨hx, hy⟩ := solution_formulas a I z hz h0 t ht
  rw [hx, hy]
  simp only [mul_pos_iff_of_pos_right (Real.exp_pos _), mul_eq_zero,
    Real.exp_ne_zero, or_false, and_self]

lemma equation_contDiffOn (a : ℝ) : ContDiffOn ℝ 1 (equation a).eval (equation a).domain :=
  ((regularity a).of_le (by simp)).contDiffOn

lemma maximal_ivp (a : ℝ) (p : Plane) :
    Specs.D13Unified.Ch01.AutonomousParameters.classicalAutonomousIVPOnValue
      (equationValue a) (flowInterval (equationValue a) p)
      (fun s => flow (equationValue a) s p) 0 p := by
  have h := flow_ivp (equation a) (equation_contDiffOn a) (ξ := p) (mem_univ p)
  exact (classicalAutonomousIVPOn_iff (equation a) _ _ 0 p).mpr h

theorem maximal_formulas : MaximalFormulas := by
  intro a p t ht
  have hz := maximal_ivp a p
  have hf := solution_formulas a _ _ hz.1 hz.2.1 t ht
  have hi := coordinate_invariance a _ _ hz.1 hz.2.1 t ht
  simpa only [hz.2.2] using And.intro hf.1 (And.intro hf.2 hi)

/-- At the sloping nullcline the vertical velocity points strictly below it.
A nonzero derivative of its defining function gives departure for all
sufficiently small nonzero times, not just at a sequence of times. -/
theorem departure : Departure := by
  intro a ha ha1
  dsimp only
  have hneg : (1 - a / 2) * (a / 2 - a) < 0 :=
    mul_neg_of_pos_of_neg (by linarith) (by linarith)
  have hNx : (a / 2, 1 - a / 2) ∈
      Specs.D13Unified.Ch13.Nullclines.nullclineXValue (equationValue a) := by
    rw [(nullclines a).1]
    exact Or.inr rfl
  refine ⟨hNx, ?_, ?_, ?_⟩
  · simp only [eval_equationValue, fieldValue]
    ring
  · simpa only [eval_equationValue, fieldValue] using ne_of_lt hneg
  · intro I z hz h0 hz0
    have hd := ((coordinate_derivatives a I z hz 0 h0).1.add
      (coordinate_derivatives a I z hz 0 h0).2).sub_const 1
    have hd' : HasDerivAt (fun t => (z t).1 + (z t).2 - 1)
        ((1 - a / 2) * (a / 2 - a)) 0 := by
      convert hd using 1
      rw [hz0]
      dsimp
      ring
    refine ⟨hd', hneg, ?_⟩
    have hsum : ∀ᶠ t in 𝓝[≠] (0 : ℝ), (z t).1 + (z t).2 - 1 ≠ 0 :=
      hd'.eventually_ne (ne_of_lt hneg)
    have hc : ContinuousAt (fun t => (z t).1) 0 :=
      (hz.1.continuousOn.continuousAt (I.isOpen.mem_nhds h0)).fst
    have hx : ∀ᶠ t in 𝓝[≠] (0 : ℝ), (z t).1 ≠ 0 :=
      (hc.eventually_ne (by rw [hz0]; exact ne_of_gt (by dsimp; linarith))).filter_mono
        nhdsWithin_le_nhds
    have hI : ∀ᶠ t in 𝓝[≠] (0 : ℝ), t ∈ I.carrier :=
      mem_nhdsWithin_of_mem_nhds (I.isOpen.mem_nhds h0)
    filter_upwards [hI, hx, hsum] with t ht hxt hst
    refine ⟨ht, ?_⟩
    rw [(nullclines a).1]
    rintro (hx0 | hy0)
    · exact hxt hx0
    · apply hst
      rw [hy0]
      ring

theorem noninvariance : Noninvariance := by
  intro a ha ha1
  have hz := maximal_ivp a (a / 2, 1 - a / 2)
  have h := departure a ha ha1
  obtain ⟨hd, hneg, hleave⟩ := h.2.2.2 _ _ hz.1 hz.2.1 hz.2.2
  exact ⟨h.1, hd.deriv ▸ ne_of_lt hneg, hleave⟩

end D13Unified.Ch13.NullclineExample
