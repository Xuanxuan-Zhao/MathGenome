import MathGenome.Internal.Specs.D07.Ch07.ClassificationIsomorphismTest
import MathGenome.Internal.D07.Ch07.InvariantFactorExistence
import MathGenome.Internal.D07.Ch07.InvariantFactorUniqueness

/-!
The classification tests of paper.tex:3477–3483. Existence supplies a
normalized product model. An isomorphism transports two presentations to
an isomorphism of their models, so upstream uniqueness identifies the data.
Conversely equal data supply a common model through which the two
presentation isomorphisms compose. This includes the empty products.
-/
namespace D07.Ch07.ClassificationIsomorphismTest

universe u v
open D07.Ch07.ClassificationDataConversion
open Specs.D07.Ch07.ClassificationIsomorphismTest

theorem normalized_data_exist : NormalizedDataExistence.{u} := by
  intro A _ _
  exact ⟨D07.Ch07.InvariantFactorExistence.elementary_model A,
    D07.Ch07.InvariantFactorExistence.invariant_factor_existence A⟩

theorem iso_iff_elementary_data_eq : ElementaryDataTest.{u, v} := by
  rintro A B _ _ _ _ E F ⟨hE, ⟨a⟩⟩ ⟨hF, ⟨b⟩⟩
  constructor
  · rintro ⟨f⟩
    exact D07.Ch07.InvariantFactorUniqueness.elementary_data_unique E F hE hF
      (a.symm.trans (f.trans b))
  · rintro rfl
    exact ⟨a.trans b.symm⟩

theorem iso_iff_invariant_factors_eq : InvariantFactorTest.{u, v} := by
  rintro A B _ _ _ _ d e ⟨hd, ⟨a⟩⟩ ⟨he, ⟨b⟩⟩
  constructor
  · rintro ⟨f⟩
    exact D07.Ch07.InvariantFactorUniqueness.invariant_factor_uniqueness d e hd he
      (a.symm.trans (f.trans b))
  · rintro rfl
    exact ⟨a.trans b.symm⟩

theorem classification_isomorphism_test : ClassificationTest.{u, v} := by
  intro A B _ _ _ _
  constructor
  · constructor
    · rintro ⟨f⟩
      obtain ⟨E, hE, ⟨a⟩⟩ := (normalized_data_exist A).1
      exact ⟨E, ⟨hE, ⟨a⟩⟩, ⟨hE, ⟨f.symm.trans a⟩⟩⟩
    · rintro ⟨E, hA, hB⟩
      exact (iso_iff_elementary_data_eq A B E E hA hB).mpr rfl
  · constructor
    · rintro ⟨f⟩
      obtain ⟨d, hd, ⟨a⟩⟩ := (normalized_data_exist A).2
      exact ⟨d, ⟨hd, ⟨a⟩⟩, ⟨hd, ⟨f.symm.trans a⟩⟩⟩
    · rintro ⟨d, hA, hB⟩
      exact (iso_iff_invariant_factors_eq A B d d hA hB).mpr rfl

end D07.Ch07.ClassificationIsomorphismTest
