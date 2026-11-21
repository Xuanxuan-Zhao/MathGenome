import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.LeviDecomposition
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.Nilradical
import Mathlib.Algebra.Lie.Derivation.Basic

/-! LA-I07, first assertion, source lines 4267–4315. The field is arbitrary
of characteristic zero. A Levi factor is a semisimple subalgebra complementary
to the actual solvable radical. The automorphism acts on the whole algebra.
The final reductive assertion is allocated separately. -/

noncomputable section
universe u v
namespace Specs.LieAlgebrasAndRepresentations.LeviConjugacy

/-- The source's Levi factors, without a choice of quotient isomorphism. -/
def IsLeviFactor (k : Type u) (L : Type v) [Field k] [LieRing L]
    [LieAlgebra k L] (S : LieSubalgebra k L) : Prop :=
  SolvableRadical.IsSemisimple_value k S ∧
    IsCompl S.toSubmodule (SolvableRadical.radical_value k L).toSubmodule

/-- The usual exponential polynomial, evaluated at the ambient adjoint. -/
def adjointExponential (k : Type u) (L : Type v) [Field k] [CharZero k]
    [LieRing L] [LieAlgebra k L] (z : L) : Module.End k L :=
  ∑ i ∈ Finset.range (nilpotencyClass (LieAlgebra.ad k L z)),
    ((i.factorial : k)⁻¹) • (LieAlgebra.ad k L z) ^ i

/-- Nilpotence is on all of L, and the exponential is the usual finite sum. -/
def finiteExponentialType : Prop :=
  ∀ (k : Type u) (L : Type v) [Field k] [CharZero k]
    [LieRing L] [LieAlgebra k L] [FiniteDimensional k L]
    (z : L), z ∈ Nilradical.nilradical_value k L →
    IsNilpotent (LieAlgebra.ad k L z) ∧
      ∃ (N : ℕ) (E : L ≃ₗ⁅k⁆ L),
        (LieAlgebra.ad k L z) ^ N = 0 ∧
        E.toLinearMap = adjointExponential k L z ∧
        E.toLinearMap = ∑ i ∈ Finset.range N,
          ((i.factorial : k)⁻¹) • (LieAlgebra.ad k L z) ^ i

/-- Initial graph reduction used in the conjugacy argument. -/
def leviFactorsEquivType : Prop :=
  ∀ (k : Type u) (L : Type v) [Field k] [CharZero k]
    [LieRing L] [LieAlgebra k L] [FiniteDimensional k L]
    (S T : LieSubalgebra k L), IsLeviFactor k L S → IsLeviFactor k L T →
    ∃ e : S ≃ₗ⁅k⁆ T, ∀ x : S,
      (e x : L) - (x : L) ∈ Nilradical.nilradical_value k L

/-- A single inner exponential sends the second given Levi factor to the first. -/
def conjugacyType : Prop :=
  ∀ (k : Type u) (L : Type v) [Field k] [CharZero k]
    [LieRing L] [LieAlgebra k L] [FiniteDimensional k L]
    (S T : LieSubalgebra k L), IsLeviFactor k L S → IsLeviFactor k L T →
    ∃ z : L, z ∈ Nilradical.nilradical_value k L ∧
      IsNilpotent (LieAlgebra.ad k L z) ∧
      ∃ E : L ≃ₗ⁅k⁆ L,
        E.toLinearMap = adjointExponential k L z ∧
        T.map E.toLieHom = S

end Specs.LieAlgebrasAndRepresentations.LeviConjugacy
