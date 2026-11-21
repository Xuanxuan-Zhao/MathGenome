import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Int.ModEq

/-! The integer construction preceding equation `eq:nt-four-square-product`,
`paper.tex:1553–1575`, and Lagrange's theorem `nt:D05`, `paper.tex:1577–1580`.
Coordinates 0,1,2,3 represent the scalar followed by the three-vector.
The signed minors below are the usual three-dimensional cross product.
Integrality of all output coordinates is part of the construction's codomain. -/
namespace P203Specs.Ch04.FourSquares

abbrev FourVector := Fin 4 → ℤ

def SquaredNormType : Type := FourVector → ℤ

def squaredNorm : SquaredNormType := fun A =>
  A 0 ^ 2 + A 1 ^ 2 + A 2 ^ 2 + A 3 ^ 2

def ConstructionType : Type := FourVector → FourVector → FourVector

/-- `(a₀b₀ + a·b, b₀a - a₀b - a×b)`, with integer coordinates. -/
def construction : ConstructionType := fun A B =>
  ![A 0 * B 0 + A 1 * B 1 + A 2 * B 2 + A 3 * B 3,
    B 0 * A 1 - A 0 * B 1 - (A 2 * B 3 - A 3 * B 2),
    B 0 * A 2 - A 0 * B 2 - (A 3 * B 1 - A 1 * B 3),
    B 0 * A 3 - A 0 * B 3 - (A 1 * B 2 - A 2 * B 1)]

def NormMultiplicative : Prop :=
  ∀ A B : FourVector,
    squaredNorm (construction A B) = squaredNorm A * squaredNorm B

/-- The positive-modulus convention includes modulus one and arbitrary signed inputs. -/
def ConstructionCongruences : Prop :=
  ∀ (m : ℤ), 0 < m → ∀ A B : FourVector,
    (∀ i, A i ≡ B i [ZMOD m]) →
    (∀ i : Fin 3, construction A B i.succ ≡ 0 [ZMOD m]) ∧
      construction A B 0 ≡ squaredNorm B [ZMOD m]

/-- Natural witnesses express precisely nonnegative integer witnesses, including at zero. -/
def LagrangeFourSquares : Prop :=
  ∀ n : ℕ, ∃ a b c d : ℕ, n = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2

end P203Specs.Ch04.FourSquares
