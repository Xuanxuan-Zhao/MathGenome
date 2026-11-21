import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.MatrixData
import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Rounding.Operations
import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Rounding.GammaProducts

/-! The real columnwise Cholesky kernel in W26. `PrimitiveTrace` records the
executed operations, independently of success; `SafeTrace` adds precisely the
per-primitive relative-model and successful-execution hypotheses. Natural state
indices count completed products, so column j has j.val products. -/
noncomputable section
open scoped BigOperators
namespace NumAnalysis206.LinearAlgebra.CholeskyData
open NumAnalysis206.MatrixDefinitions

/-- Zero extension is used only to make the residual sequences total. -/
def entry {n : ℕ} (L : Mat ℝ n n) (i : Fin n) (t : ℕ) : ℝ :=
  if h : t < n then L i ⟨t, h⟩ else 0

structure PrimitiveTrace {n : ℕ} (round : ℝ → ℝ) (A L : Mat ℝ n n)
    (s : Fin n → Fin n → ℕ → ℝ) : Prop where
  lower : IsLowerTriangular L
  initial : ∀ i j, j ≤ i → s i j 0 = A i j
  step : ∀ i j, j ≤ i → ∀ t < j.val,
    s i j (t + 1) = round (s i j t - round (entry L i t * entry L j t))
  diagonal : ∀ j, L j j = round (Real.sqrt (s j j j.val))
  offDiagonal : ∀ i j, j < i → L i j = round (s i j j.val / L j j)

structure SafeTrace {n : ℕ} (round : ℝ → ℝ) (u : ℝ) (D : Set ℝ)
    (A L : Mat ℝ n n) (s : Fin n → Fin n → ℕ → ℝ) : Prop where
  primitive : PrimitiveTrace round A L s
  model : NumAnalysis206.Rounding.Specs.RelativeModelValue round u D
  positive : ∀ j, 0 < s j j j.val
  nonzero : ∀ i j, j < i → L j j ≠ 0
  mul_safe : ∀ i j, j ≤ i → ∀ t < j.val, entry L i t * entry L j t ∈ D
  sub_safe : ∀ i j, j ≤ i → ∀ t < j.val,
    s i j t - round (entry L i t * entry L j t) ∈ D
  sqrt_safe : ∀ j, Real.sqrt (s j j j.val) ∈ D
  div_safe : ∀ i j, j < i → s i j j.val / L j j ∈ D

end NumAnalysis206.LinearAlgebra.CholeskyData

namespace Specs.NumAnalysis206.LinearAlgebra.CholeskyBackward
open NumAnalysis206.MatrixDefinitions
open NumAnalysis206.LinearAlgebra.CholeskyData

def backward : Prop :=
  ∀ (n : ℕ) (round : ℝ → ℝ) (u : ℝ) (D : Set ℝ)
    (A L : Mat ℝ n n) (s : Fin n → Fin n → ℕ → ℝ),
    A.IsSymm → SafeTrace round u D A L s → ((3 * n + 3 : ℕ) : ℝ) * u < 1 →
    ∃ Δ : Mat ℝ n n, A + Δ = L * adjoint L ∧
      EntrywiseLE (entrywiseAbs Δ)
        (fun i j => Specs.NumAnalysis206.Rounding.gammaValue (3 * n + 3) u *
          (entrywiseAbs L * entrywiseAbs (adjoint L)) i j)

end Specs.NumAnalysis206.LinearAlgebra.CholeskyBackward
