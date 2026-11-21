import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Ordered.ConcreteCones
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Ordered.PositiveAutomaticContinuity
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.ContinuousMap.Ordered
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
open Set Filter Topology
open scoped ContDiff

namespace ExpandedFA.Ordered.ConcreteCones

open Specs.ExpandedFA.Ordered.ConcreteCones
open Specs.ExpandedFA.Ordered.PositiveAutomaticContinuity (differenceSubspace)

private theorem extend_of_mem (u : CInterval) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    extend u x = u ⟨x, hx⟩ := extend_coe u ⟨x, hx⟩

/-- Positive and negative parts generate every continuous function. -/
theorem continuous_positive_decomposition (u : CInterval) :
    ∃ v ∈ positiveCone, ∃ w ∈ positiveCone, u = v - w := by
  refine ⟨u ⊔ 0, (fun t => le_max_right _ _), (-u) ⊔ 0,
    (fun t => le_max_right _ _), ?_⟩
  ext t
  change u t = max (u t) 0 - max (-u t) 0
  rcases le_total 0 (u t) with h | h
  · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]; ring
  · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]; ring

/-- The order unit gives the exact source estimate. -/
theorem positive_functional_bound (f : CInterval →ₗ[ℝ] ℝ)
    (hf : ∀ u ∈ positiveCone, 0 ≤ f u) (u : CInterval) :
    |f u| ≤ ‖u‖ * f 1 := by
  have hplus : ‖u‖ • (1 : CInterval) + u ∈ positiveCone := by
    intro t
    change 0 ≤ ‖u‖ * 1 + u t
    linarith [u.neg_norm_le_apply t]
  have hminus : ‖u‖ • (1 : CInterval) - u ∈ positiveCone := by
    intro t
    change 0 ≤ ‖u‖ * 1 - u t
    linarith [u.apply_le_norm t]
  have hp := hf _ hplus
  have hm := hf _ hminus
  simp only [map_add, map_sub, map_smul, smul_eq_mul] at hp hm
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem continuous_of_positive (f : CInterval →ₗ[ℝ] ℝ)
    (hf : ∀ u ∈ positiveCone, 0 ≤ f u) : Continuous f := by
  exact (f.mkContinuous (f 1) (fun u => by
    simpa [Real.norm_eq_abs, mul_comm] using positive_functional_bound f hf u)).continuous

/-- Positive/negative parts preserve both zero endpoint conditions. -/
theorem endpoint_positive_decomposition (u : CInterval) (hu : u ∈ endpointSubspace) :
    ∃ v ∈ endpointCone, ∃ w ∈ endpointCone, u = v - w := by
  refine ⟨u ⊔ 0, ⟨(fun t => le_max_right _ _), ?_⟩,
    (-u) ⊔ 0, ⟨(fun t => le_max_right _ _), ?_⟩, ?_⟩
  · constructor <;> simp [hu.1, hu.2]
  · constructor <;> simp [hu.1, hu.2]
  · ext t
    change u t = max (u t) 0 - max (-u t) 0
    rcases le_total 0 (u t) with h | h
    · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]; ring
    · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]; ring

theorem endpoint_difference_eq :
    differenceSubspace endpointCone ⟨0, by simp [endpointCone, endpointSubspace]⟩ =
      endpointSubspace := by
  ext u
  constructor
  · rintro ⟨v, hv, w, hw, rfl⟩
    exact endpointSubspace.sub_mem hv.2 hw.2
  · exact endpoint_positive_decomposition u

theorem endpoint_subspace_closed : IsClosed (endpointSubspace : Set CInterval) := by
  exact (isClosed_eq (ContinuousMap.evalCLM ℝ leftEnd).continuous continuous_const).inter
    (isClosed_eq (ContinuousMap.evalCLM ℝ rightEnd).continuous continuous_const)

private def endpointEvaluation : CInterval →ₗ[ℝ] (ℝ × ℝ) :=
  (ContinuousMap.evalCLM ℝ leftEnd).toLinearMap.prod
    (ContinuousMap.evalCLM ℝ rightEnd).toLinearMap

private theorem endpointEvaluation_surjective : Function.Surjective endpointEvaluation := by
  rintro ⟨a, b⟩
  refine ⟨⟨fun t => (1 - (t : ℝ)) * a + (t : ℝ) * b, by fun_prop⟩, ?_⟩
  ext <;> simp [endpointEvaluation, leftEnd, rightEnd]

private theorem endpointEvaluation_ker : endpointEvaluation.ker = endpointSubspace := by
  ext u
  simp [endpointEvaluation, endpointSubspace, LinearMap.mem_ker]

/-- The two independent endpoint evaluations identify the quotient with ℝ². -/
theorem endpoint_codimension_two :
    Module.finrank ℝ (CInterval ⧸ endpointSubspace) = 2 := by
  rw [← endpointEvaluation_ker,
    (endpointEvaluation.quotKerEquivOfSurjective endpointEvaluation_surjective).finrank_eq]
  simp [Module.finrank_prod]

private theorem endpoint_quotient_finite : FiniteDimensional ℝ (CInterval ⧸ endpointSubspace) := by
  rw [← endpointEvaluation_ker]
  exact (endpointEvaluation.quotKerEquivOfSurjective endpointEvaluation_surjective).symm.finiteDimensional

private theorem endpoint_cone_closed : IsClosed (endpointCone : Set CInterval) := by
  have h : IsClosed {u : CInterval | ∀ t, 0 ≤ u t} :=
    by
      simpa only [Set.ofPred_forall, ContinuousMap.evalCLM_apply] using
        (isClosed_iInter (fun t => isClosed_le (f := fun _ : CInterval => (0 : ℝ))
          continuous_const (ContinuousMap.evalCLM ℝ t).continuous))
  exact h.inter endpoint_subspace_closed

theorem continuous_of_endpoint_positive (f : CInterval →ₗ[ℝ] ℝ)
    (hf : ∀ u ∈ endpointCone, 0 ≤ f u) : Continuous f := by
  apply PositiveAutomaticContinuity.positive_continuous_of_closed_finite_codimension
    endpointCone ⟨0, by simp [endpointCone, endpointSubspace]⟩ endpoint_cone_closed
  · rw [endpoint_difference_eq]
    exact endpoint_subspace_closed
  · rw [endpoint_difference_eq]
    exact endpoint_quotient_finite
  · exact hf


/-- The graph representation has exactly the usual one-sided endpoint and
interior derivatives; no extension regularity outside [0,1] is imposed. -/
theorem c1_graph_iff (p : CInterval × CInterval) :
    p ∈ c1ZeroSubspace ↔
      p.1 leftEnd = 0 ∧ p.1 rightEnd = 0 ∧
      ∀ t : UnitInterval, HasDerivWithinAt (extend p.1) (p.2 t)
        (Icc (0 : ℝ) 1) t := by
  constructor
  · intro hp
    refine ⟨?_, hp.2, ?_⟩
    · rw [hp.1]
      simp [primitive, leftEnd]
    · intro t
      have hd := ((continuous_extend p.2).integral_hasStrictDerivAt 0 t).hasDerivAt.hasDerivWithinAt (s := Icc (0 : ℝ) 1)
      rw [extend_coe] at hd
      apply hd.congr_of_mem _ t.property
      intro x hx
      rw [show extend p.1 x = p.1 ⟨x, hx⟩ from extend_coe p.1 ⟨x, hx⟩, hp.1]
      rfl
  · rintro ⟨h0, h1, hd⟩
    refine ⟨?_, h1⟩
    ext t
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le t.property.1
      (continuous_extend p.1).continuousOn
      (fun x hx => by
        rw [extend_of_mem p.2 ⟨hx.1.le, hx.2.le.trans t.property.2⟩]
        exact (hd ⟨x, ⟨hx.1.le, hx.2.le.trans t.property.2⟩⟩).hasDerivAt
          (Icc_mem_nhds hx.1 (hx.2.trans_le t.property.2)))
      ((continuous_extend p.2).intervalIntegrable 0 t)
    simp only [extend_coe] at hi
    have hleft : extend p.1 0 = 0 := by
      simpa only [show (0 : ℝ) = (leftEnd : ℝ) from rfl, extend_coe] using h0
    simpa [primitive, hleft] using hi.symm

/-- The usual C¹ functions with zero endpoint values all occur in this model. -/
theorem c1_of_contDiffOn (u : CInterval)
    (hu : ContDiffOn ℝ 1 (extend u) (Icc (0 : ℝ) 1))
    (h0 : u leftEnd = 0) (h1 : u rightEnd = 0) :
    ∃ v : C1Zero, v.val.1 = u := by
  have hs : UniqueDiffOn ℝ (Icc (0 : ℝ) 1) := uniqueDiffOn_Icc zero_lt_one
  let g : CInterval := ⟨fun t => derivWithin (extend u) (Icc (0 : ℝ) 1) t,
    (continuousOn_iff_continuous_domRestrict.mp
      (hu.derivWithin hs (by norm_num : (0 : ℕ∞ω) + 1 ≤ 1)).continuousOn)⟩
  refine ⟨⟨(u, g), (c1_graph_iff (u, g)).mpr ⟨h0, h1, ?_⟩⟩, rfl⟩
  intro t
  exact (hu.differentiableOn (by norm_num) t t.property).hasDerivWithinAt

/-- Every represented function is genuinely C¹ on the closed interval. -/
theorem c1_contDiffOn (u : C1Zero) :
    ContDiffOn ℝ 1 (extend u.val.1) (Icc (0 : ℝ) 1) := by
  have hs : UniqueDiffOn ℝ (Icc (0 : ℝ) 1) := uniqueDiffOn_Icc zero_lt_one
  have hd := (c1_graph_iff u.val).mp u.property
  apply (contDiffOn_one_iff_derivWithin hs).mpr
  refine ⟨fun t ht => (hd.2.2 ⟨t, ht⟩).differentiableWithinAt, ?_⟩
  apply (continuous_extend u.val.2).continuousOn.congr
  intro t ht
  rw [extend_of_mem _ ht]
  exact (hd.2.2 ⟨t, ht⟩).derivWithin (hs t ht)

/-- The graph is closed in C([0,1]) × C([0,1]). -/
theorem c1_subspace_closed : IsClosed (c1ZeroSubspace : Set (CInterval × CInterval)) := by
  exact (isClosed_eq continuous_fst (primitive.continuous.comp continuous_snd)).inter
    (isClosed_eq ((ContinuousMap.evalCLM ℝ rightEnd).continuous.comp continuous_fst)
      continuous_const)

instance : CompleteSpace C1Zero := c1_subspace_closed.isComplete.completeSpace_coe

theorem c1_complete : CompleteSpace C1Zero := inferInstance

theorem c1_norm (u : C1Zero) : ‖u‖ = max ‖u.val.1‖ ‖u.val.2‖ := rfl

/-- The derivative bound from each endpoint gives the source's quadratic
barrier, with the explicit choice C = 2‖u'‖∞. -/
theorem c1_barrier_bound (u : C1Zero) (t : UnitInterval) :
    |u.val.1 t| ≤ (2 * ‖u.val.2‖) * ((t : ℝ) * (1 - (t : ℝ))) := by
  have hu := (c1_graph_iff u.val).mp u.property
  have hd : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (extend u.val.1)
      (extend u.val.2 x) (Icc (0 : ℝ) 1) x := by
    intro x hx
    rw [extend_of_mem _ hx]
    exact hu.2.2 ⟨x, hx⟩
  have hbound : ∀ x ∈ Icc (0 : ℝ) 1, ‖extend u.val.2 x‖ ≤ ‖u.val.2‖ :=
    fun x _ => u.val.2.norm_coe_le_norm _
  have hleft := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hbound
    (convex_Icc (0 : ℝ) 1) leftEnd.property t.property
  have hright := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hbound
    (convex_Icc (0 : ℝ) 1) rightEnd.property t.property
  have he0 : extend u.val.1 0 = 0 := by
    change extend u.val.1 (leftEnd : ℝ) = 0
    rw [extend_coe, hu.1]
  have he1 : extend u.val.1 1 = 0 := by
    change extend u.val.1 (rightEnd : ℝ) = 0
    rw [extend_coe, hu.2.1]
  simp only [extend_coe, leftEnd, he0, sub_zero, Real.norm_eq_abs,
    abs_of_nonneg t.property.1] at hleft
  simp only [extend_coe, rightEnd, he1, sub_zero, Real.norm_eq_abs,
    abs_of_nonpos (sub_nonpos.mpr t.property.2), neg_sub] at hright
  have hm : |u.val.1 t| ≤ ‖u.val.2‖ * min (t : ℝ) (1 - (t : ℝ)) := by
    rw [mul_min_of_nonneg _ _ (norm_nonneg _)]
    exact le_min hleft hright
  have hmin : min (t : ℝ) (1 - (t : ℝ)) ≤ 2 * ((t : ℝ) * (1 - (t : ℝ))) := by
    rcases le_total (t : ℝ) (1 - (t : ℝ)) with h | h
    · rw [min_eq_left h]
      nlinarith [t.property.1]
    · rw [min_eq_right h]
      nlinarith [t.property.2]
  exact hm.trans (by nlinarith [mul_le_mul_of_nonneg_left hmin (norm_nonneg u.val.2)])

private def barrier : C1Zero :=
  ⟨(⟨fun t => (t : ℝ) * (1 - (t : ℝ)), by fun_prop⟩,
      ⟨fun t => 1 - 2 * (t : ℝ), by fun_prop⟩),
    (c1_graph_iff _).mpr ⟨by simp [leftEnd], by simp [rightEnd], by
      intro t
      have hd : HasDerivAt (fun x : ℝ => x * (1 - x)) (1 - 2 * (t : ℝ)) t := by
        convert (hasDerivAt_id (t : ℝ)).mul
          ((hasDerivAt_const (t : ℝ) 1).sub (hasDerivAt_id (t : ℝ))) using 1 <;> (try funext x) <;> (try dsimp) <;> ring
      apply hd.hasDerivWithinAt.congr_of_mem _ t.property
      intro x hx
      exact extend_coe _ ⟨x, hx⟩⟩⟩

theorem c1_positive_decomposition (u : C1Zero) :
    ∃ v ∈ c1PositiveCone, ∃ w ∈ c1PositiveCone, u = v - w := by
  let C := 2 * ‖u.val.2‖
  have hC : 0 ≤ C := by positivity
  have hb : C • barrier ∈ c1PositiveCone := by
    intro t
    exact mul_nonneg hC (mul_nonneg t.property.1 (sub_nonneg.mpr t.property.2))
  refine ⟨u + C • barrier, ?_, C • barrier, hb, by abel⟩
  intro t
  have h := c1_barrier_bound u t
  change 0 ≤ u.val.1 t + C * ((t : ℝ) * (1 - (t : ℝ)))
  linarith [(abs_le.mp h).1]

private theorem c1_positive_cone_closed : IsClosed (c1PositiveCone : Set C1Zero) := by
  simpa only [c1PositiveCone, ConvexCone.coe_mk, Set.ofPred_forall,
    Function.comp_apply, ContinuousMap.evalCLM_apply] using
    (isClosed_iInter (fun t : UnitInterval =>
      isClosed_le (f := fun _ : C1Zero => (0 : ℝ)) continuous_const
        ((ContinuousMap.evalCLM ℝ t).continuous.comp
          (continuous_fst.comp continuous_subtype_val))))

theorem c1_continuous_of_positive (f : C1Zero →ₗ[ℝ] ℝ)
    (hf : ∀ u ∈ c1PositiveCone, 0 ≤ f u) : Continuous f :=
  PositiveAutomaticContinuity.continuous_of_positive_of_generating (X := C1Zero)
    c1PositiveCone c1_positive_cone_closed c1_positive_decomposition f hf


/-- A positive endpoint-zero function has nonnegative right derivative at zero. -/
theorem endpointDerivative_positive (u : C1Zero) (hu : u ∈ c1PositiveCone) :
    0 ≤ endpointDerivative u := by
  have hgraph := (c1_graph_iff u.val).mp u.property
  have h0 : extend u.val.1 0 = 0 := by
    change extend u.val.1 (leftEnd : ℝ) = 0
    rw [extend_coe, hgraph.1]
  have hmin : IsMinOn (extend u.val.1) (Icc (0 : ℝ) 1) 0 := by
    intro t ht
    change extend u.val.1 0 ≤ extend u.val.1 t
    rw [h0, extend_of_mem _ ht]
    exact hu ⟨t, ht⟩
  have htan : (1 : ℝ) ∈ posTangentConeAt (Icc (0 : ℝ) 1) 0 := by
    simpa using (sub_mem_posTangentConeAt_of_segment_subset
      (show segment ℝ (0 : ℝ) 1 ⊆ Icc 0 1 by rw [segment_eq_Icc zero_le_one]))
  have hh := hmin.isLocalMinOn.hasFDerivWithinAt_nonneg
    (hgraph.2.2 leftEnd).hasFDerivWithinAt htan
  simpa [endpointDerivative] using hh

private def witnessDeriv (n : ℕ) (t : ℝ) : ℝ :=
  (1 - 2 * t - (n : ℝ) * (t * (1 - t))) * Real.exp (-(n : ℝ) * t)

private theorem witness_hasDerivAt (n : ℕ) (t : ℝ) :
    HasDerivAt (witnessFunction n) (witnessDeriv n t) t := by
  have hp : HasDerivAt (fun x : ℝ => x * (1 - x)) (1 - 2 * t) t := by
    convert (hasDerivAt_id t).mul ((hasDerivAt_const t 1).sub (hasDerivAt_id t)) using 1 <;>
      (try funext x) <;> (try dsimp) <;> ring
  have he := ((hasDerivAt_const t (-(n : ℝ))).mul (hasDerivAt_id t)).exp
  convert hp.mul he using 1 <;> (try funext x) <;> (try dsimp [witnessFunction, witnessDeriv]) <;> ring

private def witness (n : ℕ) : C1Zero :=
  ⟨(⟨fun t => witnessFunction n t, by dsimp [witnessFunction]; fun_prop⟩,
      ⟨fun t => witnessDeriv n t, by dsimp [witnessDeriv]; fun_prop⟩),
    (c1_graph_iff _).mpr ⟨by simp [witnessFunction, leftEnd],
      by simp [witnessFunction, rightEnd], by
      intro t
      apply (witness_hasDerivAt n t).hasDerivWithinAt.congr_of_mem _ t.property
      intro x hx
      exact extend_coe _ ⟨x, hx⟩⟩⟩

private theorem witness_positive (n : ℕ) : witness n ∈ c1PositiveCone := by
  intro t
  exact mul_nonneg (mul_nonneg t.property.1 (sub_nonneg.mpr t.property.2))
    (Real.exp_pos _).le

private theorem witness_endpointDerivative (n : ℕ) : endpointDerivative (witness n) = 1 := by
  simp [endpointDerivative, witness, witnessDeriv, leftEnd]

private theorem witness_norm_bound (n : ℕ) (hn : 0 < n) :
    supNorm (witness n) ≤ (n : ℝ)⁻¹ := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  change ‖witnessFunction n t‖ ≤ (n : ℝ)⁻¹
  have hnonneg : 0 ≤ witnessFunction n t := witness_positive n t
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  have hexp : Real.exp (-1) ≤ 1 := by simp
  have hprod : ((n : ℝ) * (t : ℝ)) * Real.exp (-((n : ℝ) * (t : ℝ))) ≤ 1 :=
    (Real.mul_exp_neg_le_exp_neg_one _).trans hexp
  have hdrop : witnessFunction n t ≤ (t : ℝ) * Real.exp (-(n : ℝ) * (t : ℝ)) := by
    dsimp [witnessFunction]
    gcongr
    exact mul_le_of_le_one_right t.property.1 (sub_le_self 1 t.property.1)
  apply hdrop.trans
  rw [← one_div]
  apply (le_div_iff₀ (by exact_mod_cast hn)).mpr
  rw [neg_mul]
  nlinarith [hprod]

/-- The actual manuscript witnesses are positive C¹ functions with derivative
one at zero and supremum norm tending to zero. -/
theorem supnorm_counterexample :
    ∃ u : ℕ → C1Zero,
      (∀ n, ∀ t : UnitInterval, (u n).val.1 t = witnessFunction n t) ∧
      (∀ n, u n ∈ c1PositiveCone) ∧
      (∀ n, endpointDerivative (u n) = 1) ∧
      Tendsto (fun n => supNorm (u n)) atTop (𝓝 0) := by
  refine ⟨witness, (fun _ _ => rfl), witness_positive, witness_endpointDerivative, ?_⟩
  apply squeeze_zero' (Eventually.of_forall (fun n => norm_nonneg (witness n).val.1))
    (eventually_atTop.mpr ⟨1, fun n hn => witness_norm_bound n hn⟩)
  exact tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop

/-- No bound in the inherited supremum norm is possible. -/
theorem endpointDerivative_unbounded :
    ¬ ∃ C : ℝ, ∀ u : C1Zero, |endpointDerivative u| ≤ C * supNorm u := by
  rintro ⟨C, hC⟩
  obtain ⟨u, _, _, hder, hnorm⟩ := supnorm_counterexample
  have hlim : Tendsto (fun n => C * supNorm (u n)) atTop (𝓝 0) := by
    simpa using hnorm.const_mul C
  have hh : (1 : ℝ) ≤ 0 := ge_of_tendsto' hlim (fun n => by simpa [hder n] using hC (u n))
  norm_num at hh

/-- The same algebraic functional is discontinuous for the topology induced
by the supremum norm on the function coordinate. -/
theorem endpointDerivative_not_continuous_sup :
    ¬ @Continuous C1Zero ℝ
      (TopologicalSpace.induced (fun u : C1Zero => u.val.1) inferInstance)
      inferInstance endpointDerivative := by
  intro hc
  obtain ⟨u, _, _, hder, hnorm⟩ := supnorm_counterexample
  have hfirst : Tendsto (fun n => (u n).val.1) atTop (𝓝 0) := by
    exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  have hu : Tendsto u atTop
      (@nhds C1Zero (TopologicalSpace.induced (fun u : C1Zero => u.val.1) inferInstance) 0) := by
    rw [nhds_induced]
    exact tendsto_comap_iff.mpr hfirst
  have hh := (@Continuous.tendsto C1Zero ℝ
    (TopologicalSpace.induced (fun u : C1Zero => u.val.1) inferInstance)
    inferInstance endpointDerivative hc 0).comp hu
  have hbad : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, hder, map_zero] using hh
  have : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hbad
  norm_num at this


/-- The function coordinate determines its continuous derivative uniquely,
so the graph model adds no extra data to a C¹ function. -/
theorem c1_function_injective : Function.Injective (fun u : C1Zero => u.val.1) := by
  intro u v huv
  change u.val.1 = v.val.1 at huv
  apply Subtype.ext
  apply Prod.ext huv
  ext t
  have hu := ((c1_graph_iff u.val).mp u.property).2.2 t
  have hv := ((c1_graph_iff v.val).mp v.property).2.2 t
  rw [huv] at hu
  exact (uniqueDiffOn_Icc zero_lt_one t t.property).eq_deriv _ hu hv

private def forgetDerivative : C1Zero →L[ℝ] CInterval :=
  (ContinuousLinearMap.fst ℝ CInterval CInterval).comp c1ZeroSubspace.subtypeL

/-- The endpoint-zero C¹ functions form an incomplete subspace in the
inherited supremum norm. -/
theorem c1_incomplete_sup :
    ¬ IsComplete (Set.range (fun u : C1Zero => u.val.1)) := by
  intro hcomplete
  have hinj : Function.Injective forgetDerivative := c1_function_injective
  have hcl : IsClosed (Set.range forgetDerivative) := hcomplete.isClosed
  obtain ⟨K, hK⟩ := ContinuousLinearMap.antilipschitz_of_injective_of_isClosed_range
    (𝕜 := ℝ) (E := C1Zero) (F := CInterval) forgetDerivative hinj hcl
  apply endpointDerivative_unbounded
  refine ⟨K, fun u => ?_⟩
  have hd : |endpointDerivative u| ≤ ‖u‖ := by
    exact (u.val.2.norm_coe_le_norm leftEnd).trans (le_max_right _ _)
  apply hd.trans
  simpa [forgetDerivative, supNorm, dist_zero_right] using hK.le_mul_dist u 0


/-- The algebraic functional is precisely the right derivative at the endpoint. -/
theorem endpointDerivative_eq_derivWithin (u : C1Zero) :
    endpointDerivative u = derivWithin (extend u.val.1) (Icc (0 : ℝ) 1) 0 := by
  exact (((c1_graph_iff u.val).mp u.property).2.2 leftEnd).derivWithin
    (uniqueDiffOn_Icc zero_lt_one 0 leftEnd.property) |>.symm


/-- Explicit bridge between the product norm and the manuscript's sum C¹ norm. -/
theorem c1_sum_norm_comparison (u : C1Zero) :
    ‖u‖ ≤ c1SumNorm u ∧ c1SumNorm u ≤ 2 * ‖u‖ := by
  rw [c1_norm]
  dsimp [c1SumNorm]
  constructor
  · exact max_le (le_add_of_nonneg_right (norm_nonneg _))
      (le_add_of_nonneg_left (norm_nonneg _))
  · nlinarith [le_max_left ‖u.val.1‖ ‖u.val.2‖,
      le_max_right ‖u.val.1‖ ‖u.val.2‖]

set_option maxHeartbeats 800000 in
/-- Completeness in the displayed sum C¹ norm, without changing the topology
or assuming completeness in that norm. -/
theorem c1_sum_norm_complete (u : ℕ → C1Zero)
    (hu : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      c1SumNorm (u m - u n) < ε) :
    ∃ v : C1Zero, Tendsto (fun n => c1SumNorm (u n - v)) atTop (𝓝 0) := by
  have hc : CauchySeq u := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hu ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [dist_eq_norm]
    exact ((c1_sum_norm_comparison (u m - u n)).1).trans_lt (hN m hm n hn)
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨v, ?_⟩
  have hnorm : Tendsto (fun n => ‖u n - v‖) atTop (𝓝 0) := by
    exact tendsto_iff_norm_sub_tendsto_zero.mp hv
  apply squeeze_zero (fun n => by dsimp [c1SumNorm]; positivity)
    (fun n => (c1_sum_norm_comparison (u n - v)).2)
  simpa using hnorm.const_mul 2

/-- Positivity yields a bound also for the manuscript's exact sum norm. -/
theorem c1_positive_bound_sum_norm (f : C1Zero →ₗ[ℝ] ℝ)
    (hf : ∀ u ∈ c1PositiveCone, 0 ≤ f u) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : C1Zero, |f u| ≤ C * c1SumNorm u := by
  obtain ⟨C, hC, hb⟩ := SemilinearMapClass.bound_of_continuous (σ₁₂ := RingHom.id ℝ) f
    (c1_continuous_of_positive f hf)
  refine ⟨C, hC, fun u => ?_⟩
  simpa only [Real.norm_eq_abs] using
    (hb u).trans (mul_le_mul_of_nonneg_left (c1_sum_norm_comparison u).1 hC.le)

end ExpandedFA.Ordered.ConcreteCones
