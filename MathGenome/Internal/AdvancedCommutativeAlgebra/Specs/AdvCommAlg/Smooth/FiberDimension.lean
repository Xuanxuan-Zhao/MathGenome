import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Smooth.GeometricClosedPointRegularity

/-! SM-12, paper.tex:1312–1357. The global dimension statement requires
the field fiber to be nonzero. The geometric closed-point assertion does not:
the zero ring has no maximal ideals. All counts refer to the given presentation.
-/
namespace Specs.AdvCommAlg.Smooth

universe u v w z
open scoped TensorProduct

def standardSmoothFiberDimension : Prop :=
  ∀ {A : Type u} {B : Type v} {F : Type w}
    [CommRing A] [CommRing B] [Field F] [Algebra A B] [Algebra A F]
    {n c : ℕ} (P : Algebra.Presentation A B (Fin n) (Fin c)),
    presentationStandardSmooth P →
    Nontrivial (F ⊗[A] B) →
    ringKrullDim (F ⊗[A] B) = ((n - c : ℕ) : WithBot ℕ∞)

/-- The complete geometric part, with arbitrary compatible scalar structures
and an arbitrary chosen algebraic closure. -/
def standardSmoothGeometricFiber : Prop :=
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
