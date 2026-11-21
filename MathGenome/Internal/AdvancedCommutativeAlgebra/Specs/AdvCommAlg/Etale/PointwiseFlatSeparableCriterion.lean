import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Etale.LocalResidueFields
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Etale.FieldAlgebraClassification
import Mathlib.RingTheory.Flat.Localization

/-! ET-18, paper.tex 1999–2029. All scalar structures are the canonical
ones induced by the structural map and contraction of the prime. -/
namespace Specs.AdvCommAlg.Etale.PointwiseFlatSeparableCriterion

universe u v
open scoped TensorProduct

/-- The three conditions on the local map, with finiteness retained explicitly. -/
def LocalConditions (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B] (q : PrimeSpectrum B) : Prop :=
  letI := Localization.AtPrime.algebraOfLiesOver (q.asIdeal.under A) q.asIdeal
  Module.Flat (Localization.AtPrime (q.asIdeal.under A)) (Localization.AtPrime q.asIdeal) ∧
    (q.asIdeal.under A).map (algebraMap A (Localization.AtPrime q.asIdeal)) =
      q.asIdeal.map (algebraMap B (Localization.AtPrime q.asIdeal)) ∧
    Module.Finite (q.asIdeal.under A).ResidueField q.asIdeal.ResidueField ∧
    Algebra.IsSeparable (q.asIdeal.under A).ResidueField q.asIdeal.ResidueField

/-- The left side means existence of an étale principal neighborhood. -/
def pointwiseCriterion : Prop := ∀ (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B] [Algebra.FinitePresentation A B]
    (q : PrimeSpectrum B),
    StandardAndPointwise.isEtaleAtValue A B q ↔ LocalConditions A B q

/-- A finite product with a possibly empty set of field factors. -/
def fibersFiniteSeparableProduct : Prop := ∀ (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B], etaleValue A B →
    ∀ p : PrimeSpectrum A,
      FieldAlgebraClassification.FiniteSeparableProduct p.asIdeal.ResidueField
        (p.asIdeal.ResidueField ⊗[A] B)

/-- For a zero fiber the decomposition can explicitly have no factors. -/
def zeroFiberEmptyProduct : Prop := ∀ (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B], etaleValue A B →
    ∀ (p : PrimeSpectrum A) [Subsingleton (p.asIdeal.ResidueField ⊗[A] B)],
      Nonempty ((p.asIdeal.ResidueField ⊗[A] B) ≃ₐ[p.asIdeal.ResidueField]
        (PEmpty.{max u v + 1} → p.asIdeal.ResidueField))

end Specs.AdvCommAlg.Etale.PointwiseFlatSeparableCriterion
