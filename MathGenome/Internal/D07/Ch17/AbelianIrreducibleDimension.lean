import MathGenome.Internal.D07.Ch17.SchurScalar
import MathGenome.Internal.Specs.D07.Ch17.AbelianIrreducibleDimension

/-! Irreducible representations of arbitrary abelian groups.
The action operators belong to the commutant, so scalar Schur makes every
line invariant. A nonzero line is then the entire irreducible space.
-/
namespace D07.Ch17.AbelianIrreducibleDimension

universe u v w

open Specs.D07.Ch17.AbelianIrreducibleDimension

theorem scalar_action : ScalarAction.{u,v,w} := by
  intro K G V _ _ _ _ _ _ ρ hρ g
  let T : SchurNonscalar.endomorphismAlgebra K G V ρ :=
    ⟨ρ g, by
      change ρ g ∈ Subalgebra.centralizer K (Set.range ρ)
      rw [Subalgebra.mem_centralizer_iff]
      rintro _ ⟨h, rfl⟩
      rw [← map_mul, ← map_mul, mul_comm h g]⟩
  exact SchurScalar.unique_scalar K G V ρ hρ T

theorem line_invariant : LineInvariant.{u,v,w} := by
  intro K G V _ _ _ _ _ _ ρ hρ v g x hx
  obtain ⟨a, ha, _⟩ := scalar_action K G V ρ hρ g
  rw [ha]
  change a • x ∈ Submodule.span K {v}
  exact Submodule.smul_mem _ a hx

theorem line_spans : LineSpans.{u,v,w} := by
  intro K G V _ _ _ _ _ _ ρ hρ v hv
  rcases ((IrreducibleDefinition.irreducibility_characterization K G V ρ).mp hρ).2
    (Submodule.span K {v}) (line_invariant K G V ρ hρ v) with hbot | htop
  · have hmem := Submodule.mem_span_singleton_self v (R := K)
    rw [hbot, Submodule.mem_bot] at hmem
    exact (hv hmem).elim
  · exact htop

theorem dimension_one : DimensionOne.{u,v,w} := by
  intro K G V _ _ _ _ _ _ ρ hρ
  have : Nontrivial V := IrreducibleDefinition.irreducible_nontrivial hρ
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  exact (finrank_eq_one_iff_of_nonzero v hv).mpr (line_spans K G V ρ hρ v hv)

end D07.Ch17.AbelianIrreducibleDimension
