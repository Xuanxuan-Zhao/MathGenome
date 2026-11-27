import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.ProjectiveCechComparison
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.LaurentCechCohomology
import Mathlib.Algebra.Homology.Embedding.Restriction

noncomputable section

open CategoryTheory
open AdvancedHomologicalAlgebra.Cech
open DerivedFormalization.ProjectiveTwists (Index chart)
open DerivedFormalization.LaurentCechCohomology
open Specs.DerivedFormalization.OrderedCechComparison
open Specs.DerivedFormalization.ProjectiveCechComparison

namespace Specs.DerivedFormalization.ProjectiveChartComplexBridge

universe u

/-- The ordered localized polynomial complex and the geometric Čech complex
agree over the ground field, with the same localized coordinates on cycles. -/
def comparisonType : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ), 1 ≤ n → ∀ (m : ℤ)
    (c : Cover (globalOpen k n) (Index n)) (T : TwistFamily k n)
    (w : SectionCoordinates k n T) (d : LocalizedCoordinates k n c T),
    c.opens = chart k n →
    TwistCoordinates k n w → LocalizedTerms k n c w d → LocalizedDifferential k n c d →
    ∀ (sq : ∀ p, (differential k n m (p + 1)).comp (differential k n m p) = 0)
      (e : ∀ p : ℤ, Term k n m p ≃ₗ[k] LocalizedTerm k n m p),
      (∀ p x (J : Faces n (p + 1)),
        (e (p + 1) (differential k n m p x) J).val = localizedDeleteSum k n m p (e p x) J) →
      let K := orderedComplex k n m sq
      let C := GroundComplex k n c (T m)
      ∃ (φ : K.restriction ComplexShape.embeddingUpNat ≅ C)
        (β : ∀ q : ℕ, K.homology (q : ℤ) ≅ C.homology q)
        (g : ∀ q : ℕ, K.cycles (q : ℤ) ⟶ C.cycles q),
        ∀ (q : ℕ) (z : K.cycles (q : ℤ)),
          (β q).hom (K.homologyπ (q : ℤ) z) = C.homologyπ q (g q z) ∧
          C.iCycles q (g q z) = φ.hom.f q (K.iCycles (q : ℤ) z) ∧
          ∀ t : IncreasingTuple (Index n) q,
            ∃ h : ((tupleIndices n t.val).card : ℤ) = (q : ℤ) + 1 ∧
                (tupleIndices n t.val).Nonempty,
              let J : Faces n (q : ℤ) := ⟨tupleIndices n t.val, h⟩
              let s : IncreasingCochains (R k n) c (T m).val q := C.iCycles q (g q z)
              chartToLaurent k n (tupleIndices n t.val) ((d m q t.val).symm (s t)).val =
                chartToLaurent k n J.val (e (q : ℤ) (K.iCycles (q : ℤ) z) J).val

end Specs.DerivedFormalization.ProjectiveChartComplexBridge
