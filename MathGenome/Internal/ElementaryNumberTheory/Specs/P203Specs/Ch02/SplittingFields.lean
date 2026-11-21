import Mathlib.FieldTheory.SplittingField.IsSplittingField

/-!
Independent statements for paper.tex:410–446: the distinct-root bound and
Lemma 2.2 (splitting fields). The fields carry specified `Algebra` structures,
so `algebraMap` is the base embedding and `AlgEquiv` fixes that embedding.
For a nonconstant polynomial, `rootSet` is precisely its set of zeros;
`IntermediateField.adjoin` expresses generation as a field over the base.
-/

namespace P203Specs.Ch02

universe u v w

/-- A nonzero polynomial has at most its degree many distinct zeros, even
in an arbitrary field extension. Finiteness is included explicitly. -/
def rootBoundStatement : Prop :=
  ∀ (K : Type u) [Field K] (L : Type v) [Field L] [Algebra K L]
    (f : Polynomial K), f ≠ 0 →
      {x : L | Polynomial.aeval x f = 0}.Finite ∧
      Set.ncard {x : L | Polynomial.aeval x f = 0} ≤ f.natDegree

/-- Existence uses no prescribed ambient field. The witness retains both
its field structure and its embedding of the base field. -/
def splittingFieldExistenceStatement : Prop :=
  ∀ (K : Type u) [Field K] (f : Polynomial K), 0 < f.natDegree →
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L),
      (f.map (algebraMap K L)).Splits ∧
      IntermediateField.adjoin K (f.rootSet L) = ⊤

/-- Any two fields with these properties are isomorphic over the specified
base field. Only existence of the isomorphism is asserted. -/
def splittingFieldUniquenessStatement : Prop :=
  ∀ (K : Type u) [Field K] (f : Polynomial K), 0 < f.natDegree →
    ∀ (L : Type v) [Field L] [Algebra K L]
      (M : Type w) [Field M] [Algebra K M],
      (f.map (algebraMap K L)).Splits →
      IntermediateField.adjoin K (f.rootSet L) = ⊤ →
      (f.map (algebraMap K M)).Splits →
      IntermediateField.adjoin K (f.rootSet M) = ⊤ →
      Nonempty (L ≃ₐ[K] M)

end P203Specs.Ch02
