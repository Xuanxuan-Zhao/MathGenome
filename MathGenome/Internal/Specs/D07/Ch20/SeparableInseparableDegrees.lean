import MathGenome.Internal.Specs.D07.Ch20.SeparablePart
import MathGenome.Internal.Specs.D07.Ch20.SeparableInseparableDegreesRestrictionEmbeddingFibres

/-!
Independent statements for K07.20.separable_inseparable_degrees,
paper.tex:5848–5866. The separable part is the canonical intermediate
field `separableClosure K L`, whose carrier consists of separable elements.
`Field.finSepDegree` counts embeddings into `AlgebraicClosure L`; the
embedding-count statement identifies this with the finite count in any
algebraically closed K-field, in particular an algebraic closure of K.
`Field.finInsepDegree` is the degree of L over its separable part.
All natural-number degrees below concern finite extensions, and no
separability or perfection of the base field is assumed. Tower actions
are explicitly compatible.
-/

universe u v w z

namespace Specs.D07.Ch20.SeparableInseparableDegrees

/-- Both natural cardinalities and the interpretation in a chosen closure
are justified without assuming separability. -/
def EmbeddingCount : Prop :=
  ∀ (K : Type u) (L : Type v) (Ω : Type w)
    [Field K] [Field L] [Field Ω] [Algebra K L] [Algebra K Ω]
    [FiniteDimensional K L] [IsAlgClosed Ω],
    Finite (L →ₐ[K] Ω) ∧ Nat.card (L →ₐ[K] Ω) = Field.finSepDegree K L

/-- Actual restriction to S bijects embeddings; it is not just an equality
between two unnamed finite sets. -/
def RestrictionBijection : Prop :=
  ∀ (K : Type u) (L : Type v) (Ω : Type w)
    [Field K] [Field L] [Field Ω] [Algebra K L] [Algebra K Ω]
    [FiniteDimensional K L] [IsAlgClosed Ω],
    Function.Bijective (fun σ : L →ₐ[K] Ω => σ.domRestrict (separableClosure K L))

def SeparableDegreePart : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L],
    Field.finSepDegree K L = Module.finrank K (separableClosure K L)

def InseparableDegreePart : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L],
    Field.finInsepDegree K L = Module.finrank (separableClosure K L) L

def DegreeFactorization : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L],
    Module.finrank K L = Field.finSepDegree K L * Field.finInsepDegree K L ∧
    0 < Field.finSepDegree K L ∧ 0 < Field.finInsepDegree K L

def PositiveCharacteristic : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (p : ℕ) [CharP K p], p.Prime →
    ∃ r : ℕ, Field.finInsepDegree K L = p ^ r

def CharacteristicZero : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [CharZero K], Field.finInsepDegree K L = 1

def SeparableDegreeTower : Prop :=
  ∀ (K : Type u) (M : Type v) (L : Type w)
    [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra M L] [Algebra K L] [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional M L],
    Field.finSepDegree K L = Field.finSepDegree M L * Field.finSepDegree K M

def InseparableDegreeTower : Prop :=
  ∀ (K : Type u) (M : Type v) (L : Type w)
    [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra M L] [Algebra K L] [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional M L],
    Field.finInsepDegree K L = Field.finInsepDegree M L * Field.finInsepDegree K M

end Specs.D07.Ch20.SeparableInseparableDegrees
