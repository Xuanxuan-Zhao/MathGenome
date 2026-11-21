import MathGenome.Internal.Specs.D05.M12.ConventionBridge
import MathGenome.Internal.D05.M12.InnerProduct

/-! K05.12.convention_bridge: change of linearity convention on the same module. -/

namespace D05.M12.ConventionBridge

theorem swap_eq_conjugate : Specs.D05.M12.ConventionBridge.swap_eq_conjugate := by
  intro F V _ _ _ h hh u v
  exact hh.2.1 u v

theorem swap_conjugate_linear_first :
    Specs.D05.M12.ConventionBridge.swap_conjugate_linear_first := by
  intro F V _ _ _ h hh a b u v w
  exact InnerProduct.second_slot_of_axioms h hh a b w u v

theorem swap_linear_second : Specs.D05.M12.ConventionBridge.swap_linear_second := by
  intro F V _ _ _ h hh a b u v w
  exact hh.1 a b v w u

theorem swap_hermitian : Specs.D05.M12.ConventionBridge.swap_hermitian := by
  intro F V _ _ _ h hh u v
  exact hh.2.1 v u

theorem swap_diagonal : Specs.D05.M12.ConventionBridge.swap_diagonal := by
  intro F V _ _ _ h hh v
  exact ⟨rfl, hh.2.2.1 v, hh.2.2.2 v⟩

theorem axioms_iff_swap : Specs.D05.M12.ConventionBridge.axioms_iff_swap := by
  intro F V _ _ _ h
  constructor
  · intro hh
    exact ⟨swap_conjugate_linear_first h hh, swap_linear_second h hh,
      swap_hermitian h hh, hh.2.2.1, hh.2.2.2⟩
  · rintro ⟨_, hl, hs, hi, hp⟩
    exact ⟨fun a b u v w => hl a b w u v, fun u v => hs v u, hi, hp⟩

theorem swap_involutive : Specs.D05.M12.ConventionBridge.swap_involutive := by
  intro F V h
  rfl

theorem norm_preserved : Specs.D05.M12.ConventionBridge.norm_preserved := by
  intro F V _ h v
  rfl

theorem orthogonality_preserved :
    Specs.D05.M12.ConventionBridge.orthogonality_preserved := by
  intro F V _ _ _ h hh u v
  rw [swap_eq_conjugate h hh u v]
  exact map_eq_zero (starRingEnd F)

theorem coefficient_translation :
    Specs.D05.M12.ConventionBridge.coefficient_translation := by
  intro F V h v e
  rfl

theorem finite_expansion_translation :
    Specs.D05.M12.ConventionBridge.finite_expansion_translation := by
  intro F V ι _ _ _ h s e v
  rfl

theorem swap_firstInner_eq_inner :
    Specs.D05.M12.ConventionBridge.swap_firstInner_eq_inner := by
  intro F V _
  rfl

theorem canonical_norm : Specs.D05.M12.ConventionBridge.canonical_norm := by
  intro F V _ _ _ v
  exact ⟨(norm_eq_sqrt_re_inner (𝕜 := F) v).symm,
    (norm_eq_sqrt_re_inner (𝕜 := F) v).symm⟩

theorem canonical_orthogonality :
    Specs.D05.M12.ConventionBridge.canonical_orthogonality := by
  intro F V _ _ _ u v
  exact (orthogonality_preserved _ InnerProduct.firstInner_axioms u v).symm

end D05.M12.ConventionBridge
