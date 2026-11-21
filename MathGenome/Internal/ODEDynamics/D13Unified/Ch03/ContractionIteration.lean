import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch03.ContractionIteration
import Mathlib.Topology.MetricSpace.Contracting

/-! The contraction iteration lemma, with its quantitative estimate. -/

open Filter Function
open scoped Topology

universe u

namespace D13Unified.Ch03.ContractionIteration

/-- Lemma d13:03:contraction. Closedness gives completeness of the subtype;
Mathlib's metric contraction theorem then applies to the original self-map. -/
theorem contraction_iteration :
    Specs.D13Unified.Ch03.ContractionIteration.contractionIteration_type.{u} := by
  intro E _ _ X hX hclosed K q hq hq1 hK
  let : Nonempty X := hX.to_subtype
  let : CompleteSpace X := hclosed.isComplete.completeSpace_coe
  let c : NNReal := NNReal.mk q hq
  have hc : ContractingWith c K := by
    constructor
    · change q < 1
      exact hq1
    · apply LipschitzWith.of_dist_le_mul
      intro u v
      simpa only [Subtype.dist_eq, dist_eq_norm, c, NNReal.coe_mk] using hK u v
  refine ⟨hc.fixedPoint K, hc.fixedPoint_isFixedPt, ?_, ?_⟩
  · intro v hv
    exact hc.fixedPoint_unique hv
  · intro u0
    constructor
    · exact (continuous_subtype_val.tendsto _).comp (hc.tendsto_iterate_fixedPoint u0)
    · intro j
      calc
        ‖(K^[j] u0 : E) - ((hc.fixedPoint K : X) : E)‖ ≤
            ‖(u0 : E) - (K u0 : E)‖ * q ^ j / (1 - q) := by
          simpa only [Subtype.dist_eq, dist_eq_norm, c, NNReal.coe_mk] using
            hc.apriori_dist_iterate_fixedPoint_le u0 j
        _ = q ^ j / (1 - q) * ‖(K u0 : E) - (u0 : E)‖ := by
          rw [norm_sub_rev (u0 : E) (K u0 : E), div_mul_eq_mul_div, mul_comm (q ^ j)]

/-- The recurrence formulation follows by induction identifying every term
with the corresponding function iterate, including the zeroth term. -/
theorem contraction_sequence :
    Specs.D13Unified.Ch03.ContractionIteration.contractionSequence_type.{u} := by
  intro E _ _ X hX hclosed K q hq hq1 hK
  obtain ⟨uStar, hfix, huniq, hiter⟩ := contraction_iteration X hX hclosed K q hq hq1 hK
  refine ⟨uStar, hfix, huniq, ?_⟩
  intro u hstep
  have hu : ∀ j : ℕ, u j = K^[j] (u 0) := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih => rw [hstep, ih, Function.iterate_succ_apply']
  obtain ⟨hlim, hbound⟩ := hiter (u 0)
  constructor
  · have hvalues : (fun j : ℕ => (u j : E)) =
        (fun j : ℕ => (K^[j] (u 0) : E)) := by
      funext j
      exact congrArg Subtype.val (hu j)
    rw [hvalues]
    exact hlim
  · intro j
    simpa only [← hu j, ← hstep 0] using hbound j

end D13Unified.Ch03.ContractionIteration
