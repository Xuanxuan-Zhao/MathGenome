import MathGenome.Internal.Specs.D05.M02.VectorSpace

/-! K05.02.vector_space: canonical modules, elementary laws, and scalar restriction. -/

namespace D05.M02.VectorSpace

/-- A vector space is a module over the stated field; this is a transparent synonym. -/
abbrev vectorSpace (K V : Type*) [Field K] [AddCommGroup V] := Module K V

/-- Faithfulness of `Module` to the paper's four-axiom definition. -/
theorem module_iff_axioms : Specs.D05.M02.VectorSpace.module_iff_axioms := by
  intro K V _ _ s
  constructor
  · rintro ⟨m, hm⟩
    let _ : Module K V := m
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a u v
      simpa only [hm] using (smul_add a u v)
    · intro a b v
      simpa only [hm] using (add_smul a b v)
    · intro a b v
      simpa only [hm] using (mul_smul a b v)
    · intro v
      simpa only [hm] using (one_smul K v)
  · rintro ⟨hadd, hscalar, hmul, hone⟩
    let _ : SMul K V := ⟨s⟩
    exact ⟨Module.ofMinimalAxioms hadd hscalar hmul hone, fun _ _ => rfl⟩

theorem zero_scalar : Specs.D05.M02.VectorSpace.zero_scalar := by
  intro K V _ _ _ v
  exact zero_smul K v

theorem scalar_zero : Specs.D05.M02.VectorSpace.scalar_zero := by
  intro K V _ _ _ a
  exact smul_zero a

theorem neg_scalar : Specs.D05.M02.VectorSpace.neg_scalar := by
  intro K V _ _ _ a v
  exact neg_smul a v

theorem eq_zero_of_smul_eq_zero : Specs.D05.M02.VectorSpace.eq_zero_of_smul_eq_zero := by
  intro K V _ _ _ a v hav ha
  calc
    v = (1 : K) • v := (one_smul K v).symm
    _ = (a⁻¹ * a) • v := by rw [inv_mul_cancel₀ ha]
    _ = a⁻¹ • (a • v) := mul_smul a⁻¹ a v
    _ = 0 := by rw [hav, smul_zero]

theorem complex_as_real : Specs.D05.M02.VectorSpace.complex_as_real := by
  intro V _ _
  exact ⟨Module.complexToReal V, fun _ _ => rfl⟩

theorem real_smul_eq_complex : Specs.D05.M02.VectorSpace.real_smul_eq_complex := by
  intro V _ _ a v
  exact (Complex.coe_smul a v).symm

theorem scalar_field_dimension_example :
    Specs.D05.M02.VectorSpace.scalar_field_dimension_example := by
  refine ⟨Complex.finrank_real_complex, Module.finrank_self ℂ, ?_⟩
  rw [Complex.finrank_real_complex, Module.finrank_self]
  decide

end D05.M02.VectorSpace
