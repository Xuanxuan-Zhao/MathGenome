import MathGenome.Internal.Specs.D07.Ch12.DegreeDefinition
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finiteness

/-!
Independent specification for K07.13.prime_power_cardinality,
paper.tex:3869–3875. Fields are nontrivial and commutative. `Finite F`
means a finite underlying set; finite extension degree is separately expressed
by `FiniteDimensional` or equality of cardinal dimension with a natural number.

The prime field is `ZMod p` with its canonical characteristic-p structure map
`ZMod.algebra F p`. Thus the exponent is the degree over the actual prime-field
embedding, rather than an unspecified exponent in a prime-power factorization.
No algebraic closure or identification of abstract finite fields is needed for
this entry; the embedded fields discussed in the chapter are constructed later.
-/

universe u v

namespace Specs.D07.Ch13.PrimePowerCardinality

def CharacteristicPrime : Prop :=
  ∀ (F : Type u) [Field F] [Finite F], Nat.Prime (ringChar F)

/-- The exponent is positive and is the cardinal degree of the extension over
the canonically embedded prime field. Finite dimension is a conclusion. -/
def FiniteFieldCardinality : Prop :=
  ∀ (F : Type u) [Field F] [Finite F],
    ∃ (p n : ℕ) (hp : p.Prime) (hc : CharP F p),
      letI : Fact p.Prime := ⟨hp⟩
      letI : CharP F p := hc
      letI := ZMod.algebra F p
      FiniteDimensional (ZMod p) F ∧
        1 ≤ n ∧ Module.rank (ZMod p) F = (n : Cardinal.{u}) ∧ Nat.card F = p ^ n

/-- A finite-degree extension of a finite base has a finite underlying set.
Its positive degree determines its cardinality. The supplied Algebra retains
the specified base embedding. -/
def ExtensionCardinality : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [Finite K] [FiniteDimensional K L],
    Finite L ∧ 1 ≤ Module.finrank K L ∧
      Nat.card L = Nat.card K ^ Module.finrank K L

/-- The literal q,n formulation, using the upstream cardinal-valued degree
interface, without assuming finiteness of L or merely using its default
natural cardinality. In particular n = 0 is ruled out by the conclusion. -/
def ExtensionCardinalityOfDegree : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] [Finite K]
    (q n : ℕ), Nat.card K = q → Module.rank K L = (n : Cardinal.{v}) →
    Finite L ∧ 1 ≤ n ∧ Nat.card L = q ^ n

end Specs.D07.Ch13.PrimePowerCardinality
