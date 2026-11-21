import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.DirichletEigenbasis

/-! The attained Courant–Fischer minimum for paper.tex,
`pde:elliptic-dirichlet-spectrum`. Index `k` denotes manuscript index `k+1`.
The quantified subspaces are subspaces of the actual full-norm H¹₀ space;
the denominator is the L² norm of its canonical inclusion. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology InnerProductSpace ENNReal Matrix.Norms.Elementwise
namespace P201Specs.DirichletMinMax
open P201Specs.Dirichlet P201Specs.DirichletEigenbasis

def rayleigh {n : ℕ} (Ω : Domain n) (A : MatrixField n) (u : H10 ℝ Ω) : ℝ :=
  ellipticEnergyForm Ω A u.val u.val / ‖hZeroUnderlying Ω u‖ ^ 2

/-- A genuine maximum, with a nonzero maximizing vector. -/
def Maximum {n : ℕ} (Ω : Domain n) (A : MatrixField n)
    (W : Submodule ℝ (H10 ℝ Ω)) (r : ℝ) : Prop :=
  (∃ u ∈ W, u ≠ 0 ∧ rayleigh Ω A u = r) ∧
  ∀ u ∈ W, u ≠ 0 → rayleigh Ω A u ≤ r

def firstSpace {V : Type*} [AddCommGroup V] [Module ℝ V]
    (v : ℕ → V) (k : ℕ) : Submodule ℝ V :=
  Submodule.span ℝ (Set.range (fun i : Fin (k + 1) => v i))

/-- This is the attained minimum of the attained maxima: the designated
subspace has dimension k+1 and maximum ev k, and every subspace of that
same dimension has a maximum at least ev k. Multiplicities are preserved. -/
def MinMaxData {n : ℕ} (Ω : Domain n) (A : MatrixField n)
    (ev : ℕ → ℝ) (v : ℕ → H10 ℝ Ω) : Prop :=
  ∀ k : ℕ,
    Module.finrank ℝ (firstSpace v k) = k + 1 ∧
    Maximum Ω A (firstSpace v k) (ev k) ∧
    ∀ W : Submodule ℝ (H10 ℝ Ω), Module.finrank ℝ W = k + 1 →
      ∃ r : ℝ, Maximum Ω A W r ∧ ev k ≤ r

/-- Explicit infimum equality, together with `MinMaxData` giving attainment
of every inner maximum and of the outer infimum. -/
def InfimumFormula {n : ℕ} (Ω : Domain n) (A : MatrixField n) (ev : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, ev k = sInf {r : ℝ | ∃ W : Submodule ℝ (H10 ℝ Ω),
    Module.finrank ℝ W = k + 1 ∧ Maximum Ω A W r}

/-- Compact positive self-adjoint inverse of this exact associated operator. -/
def InverseData {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (a : P201.Elliptic.DenseForm ℝ H) (S : H →L[ℝ] H) : Prop :=
  (∀ u f, (u, f) ∈ a.associatedOperator.graph ↔ S f = u) ∧
  IsCompactOperator S ∧ S.adjoint = S ∧
  (∀ f, 0 ≤ inner ℝ f (S f)) ∧ Function.Injective S ∧ DenseRange S

/-- Complete Dirichlet spectrum and min–max conclusion, with no spectral
hypotheses: all data are constructed from the original Ω and A. -/
def Statement : Prop :=
  ∀ (m : ℕ) (Ω : Domain (m + 1)), IsBoundedLipschitzOpen Ω →
    (Ω : Set (Space (m + 1))).Nonempty →
    ∀ A : MatrixField (m + 1), MemLp A ∞ (domainMeasure Ω) →
      ∀ lam : ℝ, 0 < lam → Elliptic Ω A lam → Symmetric Ω A →
        ∃ (a : P201.Elliptic.DenseForm ℝ (Lp ℝ Ω 2))
          (T : Lp ℝ Ω 2 →L[ℝ] H10 ℝ Ω)
          (e : HilbertBasis ℕ ℝ (Lp ℝ Ω 2)) (ev : ℕ → ℝ) (v : ℕ → H10 ℝ Ω),
          IsCoefficientForm Ω A a ∧
          InverseData a ((hZeroUnderlying Ω).comp T) ∧
          OperatorData Ω a e ev v ∧ FormData Ω A e ev v ∧
          MinMaxData Ω A ev v ∧ InfimumFormula Ω A ev

end P201Specs.DirichletMinMax
