import MathGenome.Internal.Specs.D07.Ch12.TowerLaw
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs

/-!
Independent specification of K07.12.degree_divisibility, paper.tex:3647–3654.
The Algebra structures are the chosen embeddings, and IsScalarTower asserts
their compatibility. Finiteness is imposed only on the total extension L/K;
finiteness of both intermediate extensions is part of the conclusion.
For finite-dimensional vector spaces finrank is their cardinal degree viewed
as a natural number. CardinalIntermediateDegrees also states that identification
explicitly, starting from the source's cardinal definition of finite degree.
In the abstract tower, equality with an endpoint means surjectivity of its
specified embedding. For literal intermediate fields it is equality with bot
(the image of K) or top (all of L).
-/

universe u v w

namespace Specs.D07.Ch12.DegreeDivisibility

noncomputable section

def IntermediateDegrees : Prop :=
  ∀ (K : Type u) (E : Type v) (L : Type w)
    [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]
    [FiniteDimensional K L],
    FiniteDimensional K E ∧ FiniteDimensional E L ∧
      0 < Module.finrank K E ∧ 0 < Module.finrank E L ∧
      Module.finrank K E ∣ Module.finrank K L ∧
      Module.finrank E L ∣ Module.finrank K L

def CardinalIntermediateDegrees : Prop :=
  ∀ (K : Type u) (E : Type v) (L : Type w)
    [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]
    (d : ℕ), Module.rank K L = (d : Cardinal.{w}) →
    ∃ m n : ℕ,
      Module.rank K E = (m : Cardinal.{v}) ∧
      Module.rank E L = (n : Cardinal.{w}) ∧
      0 < m ∧ 0 < n ∧ m ∣ d ∧ n ∣ d

def PrimeDegreeEndpoints : Prop :=
  ∀ (K : Type u) (E : Type v) (L : Type w)
    [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]
    [FiniteDimensional K L],
    Nat.Prime (Module.finrank K L) →
      Function.Surjective (algebraMap K E) ∨ Function.Surjective (algebraMap E L)

def PrimeDegreeNoProperIntermediate : Prop :=
  ∀ (K : Type u) (L : Type w) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L],
    Nat.Prime (Module.finrank K L) →
      ∀ E : IntermediateField K L, E = ⊥ ∨ E = ⊤

end

end Specs.D07.Ch12.DegreeDivisibility
