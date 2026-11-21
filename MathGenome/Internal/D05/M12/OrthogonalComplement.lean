import MathGenome.Internal.Specs.D05.M12.OrthogonalComplement

/-! K05.12.orthogonal_complement: the canonical subspace and its basic properties. -/

namespace D05.M12.OrthogonalComplement

/-- The manuscript's complement, using the existing Mathlib submodule. -/
abbrev orthogonalComplement :
    Specs.D05.M12.OrthogonalComplement.orthogonalComplement_type :=
  @Submodule.orthogonal

theorem mem_orthogonalComplement :
    Specs.D05.M12.OrthogonalComplement.mem_orthogonalComplement := by
  intro F V _ _ _ U v
  rfl

theorem orthogonal_is_subspace :
    Specs.D05.M12.OrthogonalComplement.orthogonal_is_subspace := by
  intro F V _ _ _ U
  exact ⟨U.orthogonal, rfl⟩

theorem inf_orthogonal_eq_bot :
    Specs.D05.M12.OrthogonalComplement.inf_orthogonal_eq_bot := by
  intro F V _ _ _ U
  exact U.inf_orthogonal_eq_bot

theorem le_double_orthogonal :
    Specs.D05.M12.OrthogonalComplement.le_double_orthogonal := by
  intro F V _ _ _ U
  exact U.le_orthogonal_orthogonal

end D05.M12.OrthogonalComplement
