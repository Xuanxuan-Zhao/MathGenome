import MathGenome.Internal.Specs.D07.Ch20.GenericGroupAnyCharacteristic
import MathGenome.Internal.D07.Ch15.GenericUnsolvability

/-!
The characteristic-free generic symmetric group, paper.tex:6136–6152.
The upstream rational-function construction proves the model with elementary
symmetric coefficients in arbitrary characteristic. Its coefficient transport
sends any prescribed independent tuple to those elementary symmetric functions
and maps the alternating polynomial itself. Separability and degree descend
along that isomorphism; splitting-field transport identifies the automorphisms.
The automorphism cardinality then gives the degree of any splitting field.
-/

universe u v w
noncomputable section

namespace D07.Ch20.GenericGroupAnyCharacteristic

open Specs.D07.Ch20.GenericGroupAnyCharacteristic
open Specs.D07.Ch15.GenericUnsolvabilitySymmetricRationalFixedField

/-- Separability follows from the distinct formal roots in the model, rather
than from characteristic zero or from an invertible factorial. -/
theorem generic_polynomial_properties : GenericPolynomialProperties.{u, v} := by
  intro K M _ _ _ n hn s hs
  obtain ⟨e, _, he⟩ :=
    D07.Ch15.GenericUnsolvabilitySymmetricRationalFixedField.coefficient_polynomial_transport
      K M n s hs
  have h := D07.Ch15.GenericUnsolvabilitySymmetricRationalFixedField.separable_splitting_field
    K n hn
  refine ⟨(Polynomial.monic_map_iff (f := e.toRingHom)).mp ?_, ?_,
    (Polynomial.separable_map e.toRingHom).mp ?_⟩
  · rw [he]
    exact h.1
  · rw [← Polynomial.natDegree_map e.toRingHom, he]
    exact h.2.1
  · rw [he]
    exact h.2.2.1

/-- Removing the characteristic-zero binder from the older generic theorem is
justified by its characteristic-free coefficient and splitting-field transport. -/
theorem generic_galois_group : GenericGaloisGroup.{u, v} := by
  intro K M _ _ _ n hn s hs
  obtain ⟨e, _, he⟩ :=
    D07.Ch15.GenericUnsolvabilitySymmetricRationalFixedField.coefficient_polynomial_transport
      K M n s hs
  let : Polynomial.IsSplittingField (coefficients K n) (Rational K n)
      (genericPolynomial K n) :=
    (D07.Ch15.GenericUnsolvabilitySymmetricRationalFixedField.separable_splitting_field
      K n hn).2.2.2
  have : Polynomial.IsSplittingField (coefficients K n) (Rational K n)
      ((tuplePolynomial K n M s).map e.toRingHom) := by
    rw [he]
    infer_instance
  obtain ⟨g, _⟩ :=
    D07.Ch15.GenericUnsolvabilitySymmetricRationalFixedField.automorphism_group K n hn
  exact ⟨(D07.Ch15.GenericUnsolvability.galoisGroupBaseChange (Rational K n)
    e.toRingEquiv (tuplePolynomial K n M s)).trans g.symm⟩

/-- The finite separable splitting field has as many automorphisms as its
vector-space dimension; the computed symmetric group has order n!. -/
theorem generic_splitting_field_degree : GenericSplittingFieldDegree.{u, v, w} := by
  intro K M _ _ _ n hn s hs L _ _ _
  have hp := (generic_polynomial_properties K M n hn s hs).2.2
  let : FiniteDimensional (IntermediateField.adjoin K (Set.range s)) L :=
    Polynomial.IsSplittingField.finiteDimensional L (tuplePolynomial K n M s)
  refine ⟨inferInstance, IsGalois.of_separable_splitting_field hp, ?_⟩
  obtain ⟨g⟩ := generic_galois_group K M n hn s hs
  calc
    Module.finrank (IntermediateField.adjoin K (Set.range s)) L =
        Module.finrank (IntermediateField.adjoin K (Set.range s))
          (tuplePolynomial K n M s).SplittingField :=
      (Polynomial.IsSplittingField.algEquiv L (tuplePolynomial K n M s)).toLinearEquiv.finrank_eq
    _ = Nat.card (tuplePolynomial K n M s).Gal :=
      (Polynomial.Gal.card_of_separable hp).symm
    _ = Nat.card (Equiv.Perm (Fin n)) := Nat.card_congr g.toEquiv
    _ = n.factorial := by simp [Fintype.card_perm]

end D07.Ch20.GenericGroupAnyCharacteristic
