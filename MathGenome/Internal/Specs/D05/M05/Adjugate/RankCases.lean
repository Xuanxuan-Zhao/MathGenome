import MathGenome.Internal.Specs.D05.M05.Adjugate.RankMinors
import MathGenome.Internal.Specs.D05.M05.Adjugate

/-! Independent statements for the field rank cases, paper.tex:846–876.
The canonical adjugate is the transpose of the signed deleted-minor matrix.
Rank is `Matrix.rank`, the dimension of the column-map range. The lower-rank
case requires `2 ≤ n`, so subtraction in ℕ does not introduce spurious cases.
No determinant or iteration formula for the adjugate is assumed here. -/

namespace Specs.D05.M05.Adjugate.RankCases

open _root_.D05.M05

def full_rank : Prop :=
  ∀ {K : Type*} [Field K] {n : ℕ} (_hn : 1 ≤ n)
    (A : Matrix (Fin n) (Fin n) K),
    A.rank = n → (adjugate A).rank = n

def corank_one : Prop :=
  ∀ {K : Type*} [Field K] {n : ℕ} (_hn : 1 ≤ n)
    (A : Matrix (Fin n) (Fin n) K),
    A.rank = n - 1 → (adjugate A).rank = 1

def corank_at_least_two : Prop :=
  ∀ {K : Type*} [Field K] {n : ℕ} (_hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) K),
    A.rank ≤ n - 2 → (adjugate A).rank = 0

/-- In size one, including the zero matrix, the empty cofactor is one. -/
def singleton_zero_adjugate : Prop :=
  ∀ {K : Type*} [Field K],
    adjugate (0 : Matrix (Fin 1) (Fin 1) K) = 1

def singleton_zero_rank : Prop :=
  ∀ {K : Type*} [Field K],
    (adjugate (0 : Matrix (Fin 1) (Fin 1) K)).rank = 1

end Specs.D05.M05.Adjugate.RankCases
