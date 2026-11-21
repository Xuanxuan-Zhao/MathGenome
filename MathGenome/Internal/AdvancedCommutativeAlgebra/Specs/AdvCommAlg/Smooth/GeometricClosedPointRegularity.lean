import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Smooth.StandardPresentation
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs

/-! The closed-point assertion of SM-12, paper.tex:1312–1320, 1331–1353.
The displayed presentation, rather than an arbitrarily chosen smooth chart,
determines the two counts. No nonzero-fiber hypothesis is needed: the zero
ring has no maximal ideals. The regular-local predicate includes locality
and Noetherianity. -/
namespace Specs.AdvCommAlg.Smooth

universe u v w z
open scoped TensorProduct

/-- The local algebra step in the source proof, independent of the geometric
presentation. Linear independence is a hypothesis only of this helper. -/
def regularQuotientOfCotangentIndependent : Prop :=
  ∀ {R : Type u} [CommRing R] [IsRegularLocalRing R] {n c : ℕ},
    ringKrullDim R = (n : WithBot ℕ∞) →
    ∀ (f : Fin c → IsLocalRing.maximalIdeal R),
      LinearIndependent (IsLocalRing.ResidueField R)
        (fun i => (IsLocalRing.maximalIdeal R).toCotangent (f i)) →
      IsRegularLocalRing (R ⧸ Ideal.span (Set.range (fun i => (f i : R)))) ∧
        ringKrullDim (R ⧸ Ideal.span (Set.range (fun i => (f i : R)))) =
          ((n - c : ℕ) : WithBot ℕ∞)

def geometricClosedPointRegularity : Prop :=
  ∀ {A : Type u} {B : Type v} {F : Type w} {L : Type z}
    [CommRing A] [CommRing B] [Field F] [Field L]
    [Algebra A B] [Algebra A F] [Algebra F L] [IsAlgClosure F L]
    [Algebra A L] [IsScalarTower A F L] {n c : ℕ}
    (P : Algebra.Presentation A B (Fin n) (Fin c)),
    presentationStandardSmooth P →
    ∀ (m : Ideal (L ⊗[A] B)) (hm : m.IsMaximal),
      letI : m.IsPrime := hm.isPrime
      IsRegularLocalRing (Localization.AtPrime m) ∧
        ringKrullDim (Localization.AtPrime m) = ((n - c : ℕ) : WithBot ℕ∞)

end Specs.AdvCommAlg.Smooth
