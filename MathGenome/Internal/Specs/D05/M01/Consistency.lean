import MathGenome.Internal.Specs.D05.M01.Elimination
import MathGenome.Internal.Specs.D05.M01.SolutionInvariance
import MathGenome.Internal.Specs.D05.M04.RankBridge

/-!
Independent statements for K05.01.consistency, paper.tex:754–760.
All matrices have ordered finite indices, including zero rows or unknowns.
A contradiction row means that every coefficient entry vanishes while the
last entry is nonzero. No consistency or solution certificate is assumed.
-/
namespace D05.M01.ConsistencySpec

open D05.M01.Elimination D05.M01.RowOps
universe u

/-- For an echelon augmentation, the absence of contradiction rows is both
necessary and sufficient for a solution. -/
def echelon_consistent_iff : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K),
    (SystemSpec.augmentedMatrixValue A b).IsRowEchelon →
    ((∃ x, SystemSpec.IsSolutionValue A b x) ↔
      ∀ i, A i = 0 → b i = 0)

/-- Any echelon form reached by permitted operations on the entire
augmentation tests consistency of the original system. -/
def echelon_form_criterion : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K)
    (ops : List (RowOperation K m)),
    (applyOps ops (SystemSpec.augmentedMatrixValue A b)).IsRowEchelon →
    ((∃ x, SystemSpec.IsSolutionValue A b x) ↔
      ∀ i, (∀ j : Fin n,
        applyOps ops (SystemSpec.augmentedMatrixValue A b) i j.castSucc = 0) →
        applyOps ops (SystemSpec.augmentedMatrixValue A b) i (Fin.last n) = 0)

/-- Such a test form always exists; no echelon-form hypothesis is imposed on A. -/
def exists_echelon_test : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K),
    ∃ ops : List (RowOperation K m),
      (applyOps ops (SystemSpec.augmentedMatrixValue A b)).IsRowEchelon ∧
      ((∃ x, SystemSpec.IsSolutionValue A b x) ↔
        ∀ i, (∀ j : Fin n,
          applyOps ops (SystemSpec.augmentedMatrixValue A b) i j.castSucc = 0) →
          applyOps ops (SystemSpec.augmentedMatrixValue A b) i (Fin.last n) = 0)

/-- Equivalently the right-hand side is in the span of the actual columns of A. -/
def consistent_iff_mem_column_span : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K),
    (∃ x, SystemSpec.IsSolutionValue A b x) ↔
      b ∈ Submodule.span K (Set.range A.col)

end D05.M01.ConsistencySpec
