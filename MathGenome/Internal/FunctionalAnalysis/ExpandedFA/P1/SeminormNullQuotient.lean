import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.SeminormNullQuotient
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C01Norm

/-! The norm on the algebraic quotient by the null space of a seminorm. -/

namespace ExpandedFA.P1.SeminormNullQuotient
open C01Norm

/-- The canonical seminorm pseudometric has exactly the manuscript distance. -/
theorem seminorm_pseudometric : Spec.Pseudometric := by
  intro 𝕜 E _ _ _ p
  let := seminormedGroup p
  exact ⟨inferInstance, dist_eq_norm⟩

/-- The carrier of the constructed linear subspace is exactly the null set. -/
theorem seminorm_null_space : Spec.NullSpace := by
  intro 𝕜 E _ _ _ p x
  rfl

/-- Apply the triangle inequality in each direction, using p(-n) = p(n). -/
theorem seminorm_add_null : Spec.Translation := by
  intro 𝕜 E _ _ _ p x n hn
  apply le_antisymm
  · simpa only [hn, add_zero] using map_add_le_add p x n
  · have h := map_add_le_add p (x + n) (-n)
    simpa only [add_neg_cancel_right, map_neg_eq_map, hn, add_zero] using h

/-- Seminorm values agree whenever the two vectors represent the same coset. -/
theorem seminorm_null_representatives : Spec.Representatives := by
  intro 𝕜 E _ _ _ p x y
  refine ⟨?_, ?_⟩
  · exact Submodule.Quotient.eq (nullSubspace p)
  · intro h
    have hxy : p (x - y) = 0 := (Submodule.Quotient.eq (nullSubspace p)).mp h
    have hv := seminorm_add_null 𝕜 E p y (x - y) hxy
    simpa only [add_sub_cancel] using hv

/-- In particular, the chosen representative in quotientValue gives p(x)
for every representative x. This is the well-definedness bridge. -/
theorem seminorm_null_quotient_value : Spec.ValueOnRepresentatives := by
  intro 𝕜 E _ _ _ p x
  apply (seminorm_null_representatives 𝕜 E p _ x).2
  exact Quotient.out_eq _

/-- Transfer the seminorm axioms along the surjective quotient map. Its zero
coset consists precisely of the null vectors, which proves definiteness. -/
theorem seminorm_null_quotient_axioms : Spec.QuotientNormAxioms := by
  intro 𝕜 E _ _ _ p
  have hv := seminorm_null_quotient_value 𝕜 E p
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro z
    exact apply_nonneg p _
  · intro a z
    induction z using Submodule.Quotient.induction_on with
    | _ x =>
      change quotientValue p (quotientMap p (a • x)) = ‖a‖ * quotientValue p (quotientMap p x)
      rw [hv, hv, map_smul_eq_mul]
  · intro z w
    induction z using Submodule.Quotient.induction_on with
    | _ x =>
      induction w using Submodule.Quotient.induction_on with
      | _ y =>
        change quotientValue p (quotientMap p (x + y)) ≤
          quotientValue p (quotientMap p x) + quotientValue p (quotientMap p y)
        rw [hv, hv, hv]
        exact map_add_le_add p x y
  · intro z
    induction z using Submodule.Quotient.induction_on with
    | _ x =>
      change quotientValue p (quotientMap p x) = 0 ↔ quotientMap p x = 0
      rw [hv]
      exact (Submodule.Quotient.mk_eq_zero (p := nullSubspace p)).symm

/-- Construct the standard normed-space structure from the descended value.
The construction preserves the algebraic quotient's additive and scalar operations. -/
theorem seminorm_null_quotient_normed_space : Spec.QuotientNormedSpace := by
  intro 𝕜 E _ _ _ p
  have h := seminorm_null_quotient_axioms 𝕜 E p
  let s : Seminorm 𝕜 (Space p) := Seminorm.of (quotientValue p) h.1.2.2 h.1.2.1
  have hd : ∀ z, s z = 0 → z = 0 := fun z hz => (h.2 z).mp hz
  refine ⟨s, hd, ?_⟩
  let := normedGroup s hd
  refine ⟨(norm_realization 𝕜 (Space p) s hd).1, fun _ => rfl, ?_⟩
  exact seminorm_null_quotient_value 𝕜 E p

/-- The canonical map is linear by construction, onto, and has exactly N as
its kernel. Together with the norm formula this identifies the required quotient. -/
theorem seminorm_null_quotient_map : Spec.QuotientMapProperties := by
  intro 𝕜 E _ _ _ p
  refine ⟨Submodule.Quotient.mk_surjective (nullSubspace p), ?_⟩
  ext x
  exact Submodule.Quotient.mk_eq_zero (p := nullSubspace p)

end ExpandedFA.P1.SeminormNullQuotient
