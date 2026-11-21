import MathGenome.Internal.LinearPDE.P201Specs.Common.Operators
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.QuadraticForm.Signature

/-! Independent statements of paper.tex, Proposition `prop:pde-symbol-types`.
`sigPos` and `sigNeg` are the maximal dimensions of positive and negative
subspaces. Thus the signature hypotheses include every negative direction and
exclude a radical; they do not postulate the time-direction conclusion. -/
noncomputable section
open scoped BigOperators
namespace P201Specs.QuadraticClassification
open P201Specs P201Specs.Operators

/-- The quadratic form of the actual second-order principal matrix, on the
shared Euclidean space. -/
def matrixForm {n : ℕ} (a : Matrix (Fin n) (Fin n) ℝ) : QuadraticForm ℝ (Space n) :=
  (Matrix.toBilin (EuclideanSpace.basisFun (Fin n) ℝ).toBasis a).toQuadraticMap

def matrixFormRealizationStatement : Prop :=
  ∀ {n : ℕ} (a : Matrix (Fin n) (Fin n) ℝ) (ξ : Space n),
    matrixForm a ξ = quadraticPrincipal a ξ

/-- For second order the principal symbol is -q, so this is exactly scalar
ellipticity for a fixed real symmetric principal matrix. Universal quantification
in a also permits specialization at every spatial point. -/
def ellipticIffDefiniteStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ (a : Matrix (Fin n) (Fin n) ℝ), a.IsSymm →
    ((∀ ξ : Space n, ξ ≠ 0 → -quadraticPrincipal a ξ ≠ 0) ↔
      (∀ ξ : Space n, ξ ≠ 0 → 0 < quadraticPrincipal a ξ) ∨
      (∀ ξ : Space n, ξ ≠ 0 → quadraticPrincipal a ξ < 0))

/-- Every positive time covector, and every covector not in its span, has
exactly two distinct real characteristic roots. This includes dimension one,
where the nonproportionality condition cannot hold. -/
def timeDirectionRootsStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ Q : QuadraticForm ℝ (Space n),
    sigPos Q = 1 → sigNeg Q = n - 1 →
    ∀ e : Space n, 0 < Q e → ∀ η : Space n, (¬ ∃ c : ℝ, η = c • e) →
      ∃ r₁ r₂ : ℝ, r₁ < r₂ ∧
        ∀ τ : ℝ, Q (η + τ • e) = 0 ↔ τ = r₁ ∨ τ = r₂
end P201Specs.QuadraticClassification
