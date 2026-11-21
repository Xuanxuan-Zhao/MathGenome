import MathGenome.Internal.Specs.D07.Ch10.EuclideanPid
import MathGenome.Internal.D07.Ch10.EuclideanDefinition
import MathGenome.Internal.D07.Ch10.PidDefinition
import Mathlib.Order.WellFounded

/-! Every Euclidean domain is a PID, K07.10.euclidean_pid.
The proof uses only well-founded remainder decrease, without adding any
multiplicative compatibility condition to the Euclidean relation.
-/

universe u

namespace D07.Ch10.EuclideanPid

theorem euclidean_implies_pid (R : Type u) [CommRing R] [IsDomain R]
    (h : EuclideanDefinition.IsEuclidean R) : PidDefinition.IsPID R := by
  classical
  obtain ⟨smaller, hwf, hdiv⟩ := h
  refine ⟨inferInstance, fun I => ?_⟩
  by_cases hI : I = ⊥
  · exact ⟨0, hI.trans Ideal.span_singleton_zero.symm⟩
  · have hnonempty : Set.Nonempty {x : R | x ∈ I ∧ x ≠ 0} :=
      Submodule.exists_mem_ne_zero_of_ne_bot hI
    obtain ⟨d, ⟨hdI, hd0⟩, hminimal⟩ := hwf.has_min _ hnonempty
    refine ⟨d, le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem I).mpr hdI)⟩
    intro a ha
    obtain ⟨q, r, heq, hr⟩ := hdiv a d hd0
    have hrI : r ∈ I := by
      have heqr : a - q * d = r := sub_eq_iff_eq_add.mpr (heq.trans (add_comm _ _))
      rw [← heqr]
      exact I.sub_mem ha (I.mul_mem_left q hdI)
    have hr0 : r = 0 := by
      rcases hr with hr0 | hrlt
      · exact hr0
      · by_contra hr0
        exact hminimal r ⟨hrI, hr0⟩ hrlt
    apply Ideal.mem_span_singleton'.mpr
    exact ⟨q, by simpa only [hr0, add_zero] using heq.symm⟩

end D07.Ch10.EuclideanPid
