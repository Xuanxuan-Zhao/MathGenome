import MathGenome.Internal.Specs.D07.Ch07.ClassificationDataConversion

/-!
Independent statements for K07.07.classification_isomorphism_test,
paper.tex:3477–3483. The elementary datum records, for each actual prime,
the multiset of strictly positive exponents. Invariant factors form a list
of integers at least two in increasing divisibility order. Both models
are finite products of the additive cyclic groups `ZMod n`; empty data
are permitted. The counterexamples about insufficient invariants have
their own upstream obligation.
-/
namespace Specs.D07.Ch07.ClassificationIsomorphismTest

universe u v
open D07.Ch07.ClassificationDataConversion

/-- A normalized elementary-divisor presentation of an additive group. -/
def HasElementaryData (A : Type u) [AddCommGroup A] (E : ElementaryData) : Prop :=
  IsElementary E ∧ Nonempty (A ≃+ ElementaryGroup E)

/-- A normalized invariant-factor presentation of an additive group. -/
def HasInvariantFactors (A : Type u) [AddCommGroup A] (d : List ℕ) : Prop :=
  IsInvariant d ∧ Nonempty (A ≃+ InvariantGroup d)

/-- Neither test requires an extra hypothesis that a presentation exists. -/
def NormalizedDataExistence : Prop :=
  ∀ (A : Type u) [AddCommGroup A] [Finite A],
    (∃ E, HasElementaryData A E) ∧ (∃ d, HasInvariantFactors A d)

/-- Any normalized elementary presentations can be compared by equality. -/
def ElementaryDataTest : Prop :=
  ∀ (A : Type u) (B : Type v) [AddCommGroup A] [AddCommGroup B]
    [Finite A] [Finite B] (E F : ElementaryData),
    HasElementaryData A E → HasElementaryData B F →
      (Nonempty (A ≃+ B) ↔ E = F)

/-- Any normalized invariant-factor presentations can be compared by equality. -/
def InvariantFactorTest : Prop :=
  ∀ (A : Type u) (B : Type v) [AddCommGroup A] [AddCommGroup B]
    [Finite A] [Finite B] (d e : List ℕ),
    HasInvariantFactors A d → HasInvariantFactors B e →
      (Nonempty (A ≃+ B) ↔ d = e)

/-- Isomorphism is equivalent to having common normalized elementary data,
and equivalently to having a common normalized invariant-factor list. -/
def ClassificationTest : Prop :=
  ∀ (A : Type u) (B : Type v) [AddCommGroup A] [AddCommGroup B]
    [Finite A] [Finite B],
    (Nonempty (A ≃+ B) ↔
      ∃ E, HasElementaryData A E ∧ HasElementaryData B E) ∧
    (Nonempty (A ≃+ B) ↔
      ∃ d, HasInvariantFactors A d ∧ HasInvariantFactors B d)

end Specs.D07.Ch07.ClassificationIsomorphismTest
