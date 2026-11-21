import MathGenome.Internal.Specs.D05.M04.RankBridge

/-!
Independent specifications for K05.04.rank_factorization, paper.tex:705–711.
The factors have precisely the rank as their inner size. Columns and rows
are the actual entry functions, using the accepted column-coordinate convention.
There are no positivity or square-size assumptions, and the field is arbitrary.
-/

namespace Specs.D05.M04.RankFactorization

/-- Full-rank column-row factorization with the prescribed rank as inner size. -/
def rank_factorization : Prop :=
  ∀ {K : Type*} [Field K] {m n r : ℕ}
    (A : Matrix (Fin m) (Fin n) K), A.rank = r →
    ∃ (C : Matrix (Fin m) (Fin r) K) (R : Matrix (Fin r) (Fin n) K),
      A = C * R ∧ LinearIndependent K C.col ∧ LinearIndependent K R.row

/-- At rank zero the factors may be the unique empty matrices. -/
def zero_rank_factorization : Prop :=
  ∀ {K : Type*} [Field K] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K), A.rank = 0 →
    A = 0 ∧
      A = (0 : Matrix (Fin m) (Fin 0) K) * (0 : Matrix (Fin 0) (Fin n) K) ∧
      LinearIndependent K (0 : Matrix (Fin m) (Fin 0) K).col ∧
      LinearIndependent K (0 : Matrix (Fin 0) (Fin n) K).row

end Specs.D05.M04.RankFactorization
