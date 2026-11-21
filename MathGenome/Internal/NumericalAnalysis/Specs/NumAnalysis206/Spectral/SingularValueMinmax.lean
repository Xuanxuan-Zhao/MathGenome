import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.MatrixData

/-! The domain-space min--max formula used in W40, paper.tex 1506--1518.
The index is one based and the trial dimension is n-i+1. Using `IsGreatest`
and `IsLeast` records attainment as well as the numerical extremal values. -/
noncomputable section

namespace NumAnalysis206.SingularValueMinmaxDefinitions
open MatrixDefinitions

/-- Image norms on the unit sphere of the actual Euclidean subspace. -/
def unitImageNorms {K : Type*} [RCLike K] {m n : ℕ}
    (A : Mat K m n) (S : Submodule K (Vec K n)) : Set ℝ :=
  {r | ∃ x ∈ S, ‖x‖ = 1 ∧ ‖A.toEuclideanLin x‖ = r}

/-- Maximal image norms, for subspaces of the specified dimension. -/
def subspaceMaxima {K : Type*} [RCLike K] {m n : ℕ}
    (A : Mat K m n) (d : ℕ) : Set ℝ :=
  {r | ∃ S : Submodule K (Vec K n), Module.finrank K S = d ∧
    IsGreatest (unitImageNorms A S) r}

end NumAnalysis206.SingularValueMinmaxDefinitions

namespace Specs.NumAnalysis206.SingularValueMinmax
open _root_.NumAnalysis206.MatrixDefinitions
open _root_.NumAnalysis206.SingularValueMinmaxDefinitions

/-- Both inner and outer extrema are attained, including all zero directions. -/
def minmax : Prop :=
  ∀ {K : Type*} [RCLike K] {m n : ℕ} (A : Mat K m n)
    (i : ℕ), 1 ≤ i → i ≤ n →
      (∀ S : Submodule K (Vec K n), Module.finrank K S = n - i + 1 →
        ∃ r : ℝ, IsGreatest (unitImageNorms A S) r) ∧
      IsLeast (subspaceMaxima A (n - i + 1)) (singularValue A i)

/-- Literal conditional-infimum version of the displayed source formula. -/
def minmax_eq_sInf : Prop :=
  ∀ {K : Type*} [RCLike K] {m n : ℕ} (A : Mat K m n)
    (i : ℕ), 1 ≤ i → i ≤ n →
      singularValue A i = sInf {r : ℝ | ∃ S : Submodule K (Vec K n),
        Module.finrank K S = n - i + 1 ∧ sSup (unitImageNorms A S) = r}

end Specs.NumAnalysis206.SingularValueMinmax
