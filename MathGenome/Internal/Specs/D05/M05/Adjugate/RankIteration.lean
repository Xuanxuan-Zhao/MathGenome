import MathGenome.Internal.Specs.D05.M05.Adjugate.RankCases

/-!
Independent statements for the corollary at paper.tex:846–876.
The determinant is the shared Leibniz determinant, the adjugate is the shared
transpose of the signed deleted-minor matrix, and rank is `Matrix.rank`.
All statements here are over arbitrary fields, with no characteristic or
invertibility restriction. The lowest rank case uses `rank A + 2 ≤ n`,
so natural subtraction cannot introduce a false size-one case.
-/

namespace Specs.D05.M05.Adjugate.RankIteration

open _root_.D05.M05

/-- First branch of the rank formula, in positive size. -/
def full_rank : Prop :=
  ∀ {K : Type*} [Field K] {n : ℕ} (_hn : 1 ≤ n)
    (A : Matrix (Fin n) (Fin n) K),
    A.rank = n → (adjugate A).rank = n

/-- The corank-one branch includes the size-one zero matrix. -/
def corank_one : Prop :=
  ∀ {K : Type*} [Field K] {n : ℕ} (_hn : 1 ≤ n)
    (A : Matrix (Fin n) (Fin n) K),
    A.rank = n - 1 → (adjugate A).rank = 1

/-- The integer-bound interpretation of rank at most n−2. -/
def corank_at_least_two : Prop :=
  ∀ {K : Type*} [Field K] {n : ℕ} (_hn : 1 ≤ n)
    (A : Matrix (Fin n) (Fin n) K),
    A.rank + 2 ≤ n → (adjugate A).rank = 0

/-- This includes singular A and the zeroth power at n=1. -/
def det_adjugate : Prop :=
  ∀ {K : Type*} [Field K] {n : ℕ} (_hn : 1 ≤ n)
    (A : Matrix (Fin n) (Fin n) K),
    determinant (adjugate A) = (determinant A) ^ (n - 1)

/-- This includes singular A, in particular the zeroth power at n=2. -/
def adjugate_adjugate : Prop :=
  ∀ {K : Type*} [Field K] {n : ℕ} (_hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) K),
    adjugate (adjugate A) = (determinant A) ^ (n - 2) • A

end Specs.D05.M05.Adjugate.RankIteration
