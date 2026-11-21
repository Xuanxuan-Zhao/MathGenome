import MathGenome.Internal.AlgebraCore.Specs.P103.Ch08.SplitFourierTransform
import Mathlib.GroupTheory.Exponent
import Mathlib.Algebra.Polynomial.Splits

/-! The abelian assertions of paper.tex 1637–1644, with the nonzero
irreducibility convention of Chapter 8. Splitting uses the shared scalar
Schur-ring condition. Neither assertion assumes finite dimension. -/
universe u v w
namespace P103.Ch08.AbelianIrreducibles.Specs

/-- Over any splitting field of nonmodular characteristic, an irreducible
representation of a finite abelian group has dimension one. -/
def splitFieldType : Prop :=
  ∀ {k : Type u} {G : Type v} {V : Type w}
    [Field k] [CommGroup G] [Finite G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V),
    (Nat.card G : k) ≠ 0 → SplitFourierTransform.Splits k G →
    Irreducible k G V ρ →
    FiniteDimensional k V ∧ Module.finrank k V = 1

/-- The explicitly stated sufficient roots-of-unity condition. -/
def rootsOfUnityType : Prop :=
  ∀ {k : Type u} {G : Type v} {V : Type w}
    [Field k] [CommGroup G] [Finite G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V),
    (Nat.card G : k) ≠ 0 →
    (Polynomial.X ^ Monoid.exponent G - 1 : Polynomial k).Splits →
    Irreducible k G V ρ →
    FiniteDimensional k V ∧ Module.finrank k V = 1

end P103.Ch08.AbelianIrreducibles.Specs
