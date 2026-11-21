import MathGenome.Internal.Specs.D07.Ch23.RealSchur
import MathGenome.Internal.D07.Ch17.SchurNonscalar
import MathGenome.Internal.D07.Ch23.Frobenius
import Mathlib.Algebra.Field.Basic

/-! The real form of Schur's lemma. The concrete commutant inherits its
finite dimension from the ambient linear endomorphism algebra. Schur's
zero-or-isomorphism lemma supplies inverses, so Frobenius applies. -/

noncomputable section
universe u v
namespace D07.Ch23.RealSchur

open Specs.D07.Ch23.RealSchur

/-- No finiteness assumption on G is needed. All algebra equivalences concern
the original centralizer algebra, with its inherited operations and scalars. -/
theorem real_schur : EndomorphismAlternative.{u,v} := by
  intro G V _ _ _ _ ρ hρ
  classical
  let D := Specs.D07.Ch17.SchurNonscalar.endomorphismAlgebraValue ℝ G V ρ
  obtain ⟨hD, hunit⟩ := D07.Ch17.SchurNonscalar.division_algebra ℝ G V ρ hρ
  let : Nontrivial D := hD
  let : DivisionRing D := DivisionRing.ofIsUnitOrEqZero (fun a => by
    by_cases ha : a = 0
    · exact Or.inr ha
    · exact Or.inl (hunit a ha))
  have : FiniteDimensional ℝ D := inferInstance
  exact Frobenius.existence D (fun x => IsAlgebraic.of_finite ℝ x)

end D07.Ch23.RealSchur
