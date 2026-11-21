import MathGenome.Internal.Specs.D07.Ch09.MaximalExistence

/-! Existence of maximal ideals, K07.09.maximal_existence. -/

universe u

namespace D07.Ch09.MaximalExistence

/-- Krull's maximal-ideal existence theorem, specialized to the source's
commutative rings. The library theorem uses choice through coatomicity
of the ideal lattice and requires only the properness of `I`. -/
theorem existsMaximal :
    Specs.D07.Ch09.MaximalExistence.MaximalExistence.{u} := by
  intro R _ I hI
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hI
  exact ⟨M, hIM, hM⟩

end D07.Ch09.MaximalExistence
