import MathGenome.Internal.Specs.D07.Ch20.ArtinSchreier
import MathGenome.Internal.D07.Ch20.ArtinSchreierTranslationDichotomy
import MathGenome.Internal.D07.Ch20.ArtinSchreierCyclicDegreePConverse
import MathGenome.Internal.D07.Ch20.ArtinSchreierParameterClassification

/-!
K07.20.artin_schreier: the complete characteristic-p dichotomy,
cyclic converse, and parameter classification. The constituent proofs use
root translations, finite Galois theory, and additive Hilbert 90 without
dividing by p. Here they are assembled with the source's quantifiers.
-/

noncomputable section
universe u v
namespace D07.Ch20.ArtinSchreier
open Polynomial
open Specs.D07.Ch20.ArtinSchreier
open Specs.D07.Ch20.ArtinSchreierTranslationDichotomy (asPolynomial)

/-- Splitting into p distinct factors or nontrivial irreducibility. -/
theorem polynomial_dichotomy : PolynomialDichotomy.{u} := by
  classical
  intro K _ p _ _ a
  by_cases ha : ∃ θ : K, θ ^ p - θ = a
  · obtain ⟨θ, hθ⟩ := ha
    obtain ⟨hinj, _, hprod⟩ :=
      ArtinSchreierTranslationDichotomy.translated_roots K p a θ hθ
    have hs :=
      (ArtinSchreierTranslationDichotomy.splits_iff_parameter_in_image K p a).mpr ⟨θ, hθ⟩
    have hd := (ArtinSchreierTranslationDichotomy.degree_and_separability K p a).2.1
    exact Or.inl ⟨θ, hθ, hinj, hprod, (hs.natDegree_eq_card_roots).symm.trans hd⟩
  · exact Or.inr ⟨ha,
      ArtinSchreierTranslationDichotomy.irreducible_of_parameter_not_in_image K p a ha⟩

theorem splits_iff : SplitsIff.{u} :=
  ArtinSchreierTranslationDichotomy.splits_iff_parameter_in_image

theorem root_extension : RootExtension.{u, v} :=
  ArtinSchreierTranslationDichotomy.nontrivial_root_extension

/-- Choose a generator of the cyclic group, then apply the proved converse. -/
theorem cyclic_converse : CyclicConverse.{u, v} := by
  intro K L _ _ _ p _ _ _ _ _ hd
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := L ≃ₐ[K] L)
  obtain ⟨θ, a, _, hθ, ha, hgen⟩ :=
    ArtinSchreierCyclicDegreePConverse.cyclic_degree_p_converse K L p hd σ hσ
  have ha' : ¬ ∃ u : K, u ^ p - u = a := by
    rintro ⟨u, hu⟩
    exact ha ⟨u, hu.symm⟩
  exact ⟨θ, a, ha', hθ, hgen,
    ArtinSchreierTranslationDichotomy.root_minpoly a θ hθ ha'⟩

theorem root_fields_classification : RootFieldsClassification.{u, v} := by
  intro K Ω _ _ _ p _ _ a b θ η ha hb hθ hη
  have hi := ArtinSchreierParameterClassification.root_fields_isomorphic_iff_equal
    K Ω p a b θ η ha hb hθ hη
  have hp := ArtinSchreierParameterClassification.root_fields_equal_iff
    K Ω p a b θ η ha hb hθ hη
  exact ⟨hi.symm, hi.trans hp⟩

theorem common_closure_classification : CommonClosureClassification.{u} :=
  ArtinSchreierParameterClassification.common_closure_classification

/-- The full theorem, with all conclusions and the original applicability. -/
theorem artin_schreier : ArtinSchreierTheorem.{u, v} :=
  ⟨polynomial_dichotomy, splits_iff, root_extension, cyclic_converse,
    root_fields_classification, common_closure_classification⟩

end D07.Ch20.ArtinSchreier
