import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch15.RsParts
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch15.RsExistence
import Mathlib.Tactic.Ring

/-! Stieltjes integration by parts for continuous real BV functions.
The finite product identity uses left tags in the first sum and right tags in
the second. A common refinement lets both limits be applied to that identity.
No assertion about discontinuous jump corrections is used. -/
namespace SingleVariableAnalysis.Stieltjes
open Riemann
open scoped BigOperators

/-- The left endpoint is a permitted closed-cell tag. -/
def leftEndpointTags {a b : ℝ} (P : Partition a b) : Tagging P :=
  fun i => ⟨P.point i.castSucc, le_rfl, (P.strictMono Fin.castSucc_lt_succ).le⟩

/-- The right endpoint is a permitted closed-cell tag. -/
def rightEndpointTags {a b : ℝ} (P : Partition a b) : Tagging P :=
  fun i => ⟨P.point i.succ, (P.strictMono Fin.castSucc_lt_succ).le, le_rfl⟩

/-- The exact finite product identity, valid without regularity assumptions. -/
theorem endpoint_sum_parts {a b : ℝ} (P : Partition a b) (f α : ℝ → ℝ) :
    taggedSum P (leftEndpointTags P) f α +
      taggedSum P (rightEndpointTags P) α f = f b * α b - f a * α a := by
  change (∑ i : Fin P.n,
      (α (P.point i.succ) - α (P.point i.castSucc)) * f (P.point i.castSucc)) +
    (∑ i : Fin P.n,
      (f (P.point i.succ) - f (P.point i.castSucc)) * α (P.point i.succ)) = _
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ i : Fin P.n,
        (f (P.point i.succ) * α (P.point i.succ) -
          f (P.point i.castSucc) * α (P.point i.castSucc)) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = f b * α b - f a * α a := by
      rw [sum_fin_increments (fun i => f (P.point i) * α (P.point i)), P.last, P.first]

/-- Any pair of refinement limits in the opposite slots satisfies the parts
identity. Existence, rather than extra regularity, is what this step uses. -/
theorem refinementLimit_parts {a b : ℝ} {f α : ℝ → ℝ} {I J : ℝ}
    (hI : RefinementLimit a b f α I) (hJ : RefinementLimit a b α f J) :
    I + J = f b * α b - f a * α a := by
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨P, hP⟩ := hI (ε / 2) (half_pos hε)
  obtain ⟨Q, hQ⟩ := hJ (ε / 2) (half_pos hε)
  obtain ⟨R, _, hRP, hRQ⟩ := common_refinement P Q
  have hi := hP R hRP (leftEndpointTags R)
  have hj := hQ R hRQ (rightEndpointTags R)
  have he := endpoint_sum_parts R f α
  have ht := norm_add_le
    (taggedSum R (leftEndpointTags R) f α - I)
    (taggedSum R (rightEndpointTags R) α f - J)
  have hid :
      (taggedSum R (leftEndpointTags R) f α - I) +
        (taggedSum R (rightEndpointTags R) α f - J) =
      (f b * α b - f a * α a) - (I + J) := by linarith
  rw [hid, norm_sub_rev] at ht
  linarith

/-- K03.15.rs_parts, including existence of both refinement integrals. -/
theorem continuous_bv_integration_by_parts :
    Specs.SingleVariableAnalysis.Ch15.RsParts.integrationByParts := by
  intro a b hab f α hf hα hvf hvα
  obtain ⟨I, hI, _⟩ := real_continuous_bv_integral a b hab f α hf hvα
  obtain ⟨J, hJ, _⟩ := real_continuous_bv_integral a b hab α f hα hvf
  refine ⟨I, J, hI, hJ, ?_⟩
  exact refinementLimit_parts
    ((integral_iff_of_le a b hab f α I).mp hI).2.2
    ((integral_iff_of_le a b hab α f J).mp hJ).2.2

end SingleVariableAnalysis.Stieltjes
