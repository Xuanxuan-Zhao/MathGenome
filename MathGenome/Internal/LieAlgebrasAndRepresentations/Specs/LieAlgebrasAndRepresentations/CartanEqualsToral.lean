import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.MaximalTori
import Mathlib.Algebra.Lie.CartanSubalgebra

/-! LA-D07 (Cartan characterization), source lines 1880–1912.
The chapter convention is finite-dimensional complex semisimple Lie algebras.
Cartan means nilpotent and self-normalizing, with no splitting assumption.
Semisimplicity means the solvable radical vanishes. The zero algebra is included.
Conjugacy is allocated separately to LA-D07. -/

universe u
namespace Specs.LieAlgebrasAndRepresentations.CartanEqualsToral

def IsCartan_value {L : Type u} [LieRing L] [LieAlgebra ℂ L]
    (H : LieSubalgebra ℂ L) : Prop :=
  LieRing.IsNilpotent H ∧ H.normalizer = H

def IsCartan_type :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L], LieSubalgebra ℂ L → Prop

/-- Compatibility with the canonical nilpotent, self-normalizing Cartan class. -/
def isCartan_iff_isCartanSubalgebra_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] (H : LieSubalgebra ℂ L),
    IsCartan_value H ↔ H.IsCartanSubalgebra

def isCartan_iff_maximal_toral_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ H : LieSubalgebra ℂ L,
      IsCartan_value H ↔ MaximalTori.IsMaximalToral_value H

def zero_algebra_cartan_type : Prop :=
  ∀ (L : Type u) [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    [Subsingleton L], IsCartan_value (⊥ : LieSubalgebra ℂ L)

end Specs.LieAlgebrasAndRepresentations.CartanEqualsToral
