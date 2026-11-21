import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C15BasisCriterion
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C15PartialSums
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

open Filter Topology
open scoped BigOperators
noncomputable section
universe u v
namespace ExpandedFA.P1.C15BasisCriterion
namespace BasisCriterionProof
open ExpandedFA.P1.C15Basis.Spec ExpandedFA.P1.C15BasisCriterion.Spec
variable {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A finite coefficient family has eventually constant ordered partial sums. -/
theorem finite_stabilizes (e : ℕ → E) (a : ℕ →₀ 𝕜) :
    ∃ N, ∀ n, N ≤ n → orderedPartialSum e a n = Finsupp.linearCombination 𝕜 e a := by
  classical
  obtain ⟨N, hN⟩ := Finset.exists_nat_subset_range a.support
  refine ⟨N, fun n hn => ?_⟩
  symm
  exact a.sum_of_support_subset (hN.trans (Finset.range_mono hn)) _ (fun i _ => zero_smul 𝕜 (e i))

/-- The finite prefix estimate bounds truncation relative to synthesis, without
first assuming independence or the existence of algebraic coordinates. -/
theorem prefix_bound {e : ℕ → E} {C : ℝ}
    (hb : ∀ (a : ℕ → 𝕜) (m N : ℕ), m ≤ N →
      ‖orderedPartialSum e a m‖ ≤ C * ‖orderedPartialSum e a N‖)
    (a : ℕ →₀ 𝕜) (m : ℕ) :
    ‖orderedPartialSum e a m‖ ≤ C * ‖Finsupp.linearCombination 𝕜 e a‖ := by
  obtain ⟨N, hN⟩ := finite_stabilizes e a
  simpa only [hN (max m N) (le_max_right _ _)] using hb a m (max m N) (le_max_left _ _)

/-- Nonzero vectors turn the difference of successive prefixes into a bound
on each coefficient, even before independence has been established. -/
theorem coefficient_bound {e : ℕ → E} (he : ∀ i, e i ≠ 0) {C : ℝ}
    (hb : ∀ (a : ℕ → 𝕜) (m N : ℕ), m ≤ N →
      ‖orderedPartialSum e a m‖ ≤ C * ‖orderedPartialSum e a N‖)
    (i : ℕ) (a : ℕ →₀ 𝕜) :
    ‖a i‖ ≤ (2 * C / ‖e i‖) * ‖Finsupp.linearCombination 𝕜 e a‖ := by
  have hi : 0 < ‖e i‖ := norm_pos_iff.mpr (he i)
  have hincr : orderedPartialSum e a (i + 1) - orderedPartialSum e a i = a i • e i := by
    simp [orderedPartialSum, ExpandedFA.P1.C15Basis.Spec.orderedPartialSum, Finset.sum_range_succ]
  have hh : ‖a i‖ * ‖e i‖ ≤ 2 * C * ‖Finsupp.linearCombination 𝕜 e a‖ := by
    rw [← norm_smul, ← hincr]
    exact (norm_sub_le _ _).trans (by
      linarith [prefix_bound hb a (i + 1), prefix_bound hb a i])
  calc
    ‖a i‖ ≤ (2 * C * ‖Finsupp.linearCombination 𝕜 e a‖) / ‖e i‖ :=
      (le_div_iff₀ hi).mpr hh
    _ = (2 * C / ‖e i‖) * ‖Finsupp.linearCombination 𝕜 e a‖ := by ring

/-- Continuous biorthogonal coordinates give uniqueness of every ordered
expansion, not merely the selected coordinate expansion. -/
theorem unique_expansion {e : ℕ → E} (f : ℕ → E →L[𝕜] 𝕜)
    (ho : ∀ i j, f i (e j) = (Pi.single j (1 : 𝕜) : ℕ → 𝕜) i)
    {x : E} {a : ℕ → 𝕜} (ha : Tendsto (orderedPartialSum e a) atTop (𝓝 x)) :
    a = fun i => f i x := by
  classical
  funext i
  have hh : ∀ᶠ N : ℕ in atTop, f i (orderedPartialSum e a N) = a i := by
    filter_upwards [eventually_gt_atTop i] with N hN
    simp [orderedPartialSum, ExpandedFA.P1.C15Basis.Spec.orderedPartialSum, map_sum, map_smul,
      ho, Pi.single_apply, hN]
  exact tendsto_nhds_unique (tendsto_const_nhds.congr' (hh.mono fun _ h => h.symm))
    ((f i).continuous.tendsto x |>.comp ha)

/-- Sufficiency is constructed from the bound on finite coefficients. -/
theorem basis_of_prefix_bound [CompleteSpace E] {e : ℕ → E}
    (he : ∀ i, e i ≠ 0) (hd : Dense (Submodule.span 𝕜 (Set.range e) : Set E))
    (hbound : UniformPrefixBound (𝕜 := 𝕜) e) :
    IsRawSchauderBasis (𝕜 := 𝕜) e := by
  classical
  obtain ⟨C₀, hC₀⟩ := hbound
  let C : ℝ := max C₀ 0
  have hC : 0 ≤ C := le_max_right _ _
  have hb (a : ℕ → 𝕜) (m N : ℕ) (hmN : m ≤ N) :
      ‖orderedPartialSum e a m‖ ≤ C * ‖orderedPartialSum e a N‖ :=
    (hC₀ a m N hmN).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  let S : (ℕ →₀ 𝕜) →ₗ[𝕜] E := Finsupp.linearCombination 𝕜 e
  have hdS : DenseRange S := by
    simpa only [S, DenseRange, ← LinearMap.coe_range, Finsupp.range_linearCombination] using hd
  let f (i : ℕ) : E →L[𝕜] 𝕜 := (Finsupp.lapply i : (ℕ →₀ 𝕜) →ₗ[𝕜] 𝕜).extendOfNorm S
  have hf (i : ℕ) (a : ℕ →₀ 𝕜) : f i (S a) = a i :=
    LinearMap.extendOfNorm_eq hdS ⟨2 * C / ‖e i‖, coefficient_bound he hb i⟩ a
  have ho (i j : ℕ) : f i (e j) = (Pi.single j (1 : 𝕜) : ℕ → 𝕜) i := by
    simpa only [S, Finsupp.linearCombination_single, one_smul, Finsupp.single_apply,
      Pi.single_apply, eq_comm] using hf i (Finsupp.single j 1)
  let P (m : ℕ) : E →L[𝕜] E := ∑ i ∈ Finset.range m, (f i).smulRight (e i)
  have hPx (m : ℕ) (x : E) : P m x = orderedPartialSum e (fun i => f i x) m := by
    simp [P, orderedPartialSum, ExpandedFA.P1.C15Basis.Spec.orderedPartialSum]
  have hPa (m : ℕ) (a : ℕ →₀ 𝕜) : P m (S a) = orderedPartialSum e a m := by
    simp only [hPx, hf]
  have hnorm (m : ℕ) (x : E) : ‖P m x‖ ≤ C * ‖x‖ := by
    refine hdS.induction_on x (isClosed_le ((P m).continuous.norm)
      (continuous_const.mul continuous_norm)) ?_
    intro a
    rw [hPa]
    exact prefix_bound hb a m
  have hp (x : E) : Tendsto (fun m => P m x) atTop (𝓝 x) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨a, hxz⟩ := hdS.exists_dist_lt x (div_pos hε (by linarith : 0 < C + 1))
    obtain ⟨N, hN⟩ := finite_stabilizes e a
    refine ⟨N, fun m hm => ?_⟩
    have hfix : P m (S a) = S a := (hPa m a).trans (hN m hm)
    rw [dist_eq_norm] at hxz ⊢
    have hh : ‖P m x - x‖ ≤ (C + 1) * ‖x - S a‖ := by
      calc
        ‖P m x - x‖ = ‖P m (x - S a) + (S a - x)‖ := by rw [map_sub, hfix]; congr 1; abel
        _ ≤ ‖P m (x - S a)‖ + ‖S a - x‖ := norm_add_le _ _
        _ ≤ C * ‖x - S a‖ + ‖S a - x‖ := add_le_add (hnorm m _) le_rfl
        _ = (C + 1) * ‖x - S a‖ := by rw [norm_sub_rev (S a) x]; ring
    apply hh.trans_lt
    simpa only [mul_comm] using (lt_div_iff₀ (by linarith : 0 < C + 1)).mp hxz
  refine ⟨he, fun x => ⟨fun i => f i x, ?_, ?_⟩⟩
  · simpa only [hPx] using hp x
  · intro a ha
    exact unique_expansion f ho ha

end BasisCriterionProof
/-- The source criterion, with unique norm-convergent expansions and no
continuity hypothesis on coordinate maps. -/
theorem schauder_basis_criterion : Spec.BasisCriterion := by
  intro 𝕜 E _ _ _ _ e he hd
  constructor
  · intro h
    obtain ⟨T, _, hfinite, _⟩ := ExpandedFA.P1.C15PartialSums.raw_partial_sum_bounds h
    exact ⟨ExpandedFA.P1.C15PartialSums.Spec.basisConstant T, hfinite⟩
  · exact BasisCriterionProof.basis_of_prefix_bound he hd

/-- In particular the finite estimate cannot hide a finite linear relation. -/
theorem prefix_bound_linearIndependent : Spec.PrefixBoundIndependence := by
  intro 𝕜 E _ _ _ e he hb
  obtain ⟨C, hC⟩ := hb
  apply linearIndependent_iff.mpr
  intro a ha
  apply Finsupp.ext
  intro i
  have hh := BasisCriterionProof.coefficient_bound he hC i a
  rw [ha, norm_zero, mul_zero] at hh
  exact norm_le_zero_iff.mp hh

end ExpandedFA.P1.C15BasisCriterion
