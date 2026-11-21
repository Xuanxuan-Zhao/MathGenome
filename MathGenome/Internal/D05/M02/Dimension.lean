import MathGenome.Internal.Specs.D05.M02.Dimension
import MathGenome.Internal.D05.M02.BasisExtension
import MathGenome.Internal.D05.M02.Exchange

/-! K05.02.dimension: finite spanning families, basis length, and zero dimension. -/

namespace D05.M02.Dimension

/-- Reuse finite generation over the stated field. -/
abbrev finiteDimensional (K V : Type*) [Field K] [AddCommGroup V] [Module K V] :=
  FiniteDimensional K V

theorem finite_basis_of_finite_spanning :
    Specs.D05.M02.Dimension.finite_basis_of_finite_spanning := by
  intro K V _ _ _ n w hw
  classical
  obtain ⟨t, b, _⟩ := D05.M02.BasisExtension.finite_spanning_contains_basis n w hw
  exact ⟨Fintype.card t, ⟨b.reindex (Fintype.equivFin t)⟩⟩

theorem finiteDimensional_iff_finite_spanning :
    Specs.D05.M02.Dimension.finiteDimensional_iff_finite_spanning := by
  intro K V _ _ _
  constructor
  · intro h
    letI := h
    exact ⟨Module.finrank K V, Module.finBasis K V, (Module.finBasis K V).span_eq⟩
  · rintro ⟨n, w, hw⟩
    obtain ⟨m, ⟨b⟩⟩ := finite_basis_of_finite_spanning n w hw
    exact b.finiteDimensional_of_finite

theorem finiteDimensional_iff_finite_basis :
    Specs.D05.M02.Dimension.finiteDimensional_iff_finite_basis := by
  intro K V _ _ _
  constructor
  · intro h
    obtain ⟨n, w, hw⟩ := finiteDimensional_iff_finite_spanning.mp h
    exact finite_basis_of_finite_spanning n w hw
  · rintro ⟨n, ⟨b⟩⟩
    exact b.finiteDimensional_of_finite

/-- This proof uses the upstream exchange inequality in each direction. -/
theorem finite_bases_equal_length : Specs.D05.M02.Dimension.finite_bases_equal_length := by
  intro K V I J _ _ _ _ _ b c
  let b' := b.reindex (Fintype.equivFin I)
  let c' := c.reindex (Fintype.equivFin J)
  exact Nat.le_antisymm
    (D05.M02.Exchange.exchange _ _ b' c' b'.linearIndependent c'.span_eq).1
    (D05.M02.Exchange.exchange _ _ c' b' c'.linearIndependent b'.span_eq).1

/-- The common finite basis length, expressed by Mathlib's canonical finrank. -/
noncomputable abbrev dimension (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] : ℕ := Module.finrank K V

theorem dimension_eq_card_basis : Specs.D05.M02.Dimension.dimension_eq_card_basis := by
  intro K V I _ _ _ _ _ b
  exact Module.finrank_eq_card_basis b

theorem exists_basis_dimension : Specs.D05.M02.Dimension.exists_basis_dimension := by
  intro K V _ _ _ _
  exact ⟨Module.finBasis K V⟩

theorem empty_basis_iff_zero_space : Specs.D05.M02.Dimension.empty_basis_iff_zero_space := by
  intro K V _ _ _
  constructor
  · rintro ⟨b⟩ x
    exact b.repr.injective (Subsingleton.elim _ _)
  · intro hzero
    letI : Subsingleton V := ⟨fun x y => (hzero x).trans (hzero y).symm⟩
    exact ⟨Module.Basis.empty V⟩

theorem zero_space_dimension : Specs.D05.M02.Dimension.zero_space_dimension := by
  intro K V _ _ _ _
  let b : Module.Basis (Fin 0) K V := Module.Basis.empty V
  exact ⟨b.finiteDimensional_of_finite, by simpa using Module.finrank_eq_card_basis b⟩

theorem dimension_zero_iff_zero_space :
    Specs.D05.M02.Dimension.dimension_zero_iff_zero_space := by
  intro K V _ _ _ _
  constructor
  · intro hzero
    exact (empty_basis_iff_zero_space (K := K)).mp ⟨Module.finBasisOfFinrankEq K V hzero⟩
  · intro hzero
    obtain ⟨b⟩ := (empty_basis_iff_zero_space (K := K)).mpr hzero
    simpa using Module.finrank_eq_card_basis b

end D05.M02.Dimension
