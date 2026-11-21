import MathGenome.Internal.LinearPDE.P201Specs.Common.ExactTrace
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Independent statements for paper.tex §E01, including the unnumbered
symmetric energy paragraph. All bulk norms are the canonical full H¹ norms.
The matrix L∞ norm in the estimate is the essential supremum of the
Euclidean operator norm. Matrix measurability uses the usual finite product topology.
-/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace P201Specs.Dirichlet

abbrev MatrixField (n : ℕ) := Space n → Matrix (Fin n) (Fin n) ℝ

/-- The actual action of a matrix on Euclidean space, with its operator norm. -/
def matrixOperator {n : ℕ} :
    Matrix (Fin n) (Fin n) ℝ →L[ℝ] (Space n →L[ℝ] Space n) :=
  (Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap).toLinearMap.toContinuousLinearMap

def CoefficientNorm {n : ℕ} (Ω : Domain n) (A : MatrixField n) : ℝ :=
  (eLpNorm (fun x => matrixOperator (A x)) ∞ (domainMeasure Ω)).toReal

/-- A single exceptional null set for all vectors, as in the source. -/
def Elliptic {n : ℕ} (Ω : Domain n) (A : MatrixField n) (lam : ℝ) : Prop :=
  ∀ᵐ x ∂domainMeasure Ω, ∀ ξ : Space n,
    lam * ‖ξ‖ ^ 2 ≤ ∑ i, ∑ j, A x i j * ξ j * ξ i

/-- Symmetry is only required for the energy assertion. -/
def Symmetric {n : ℕ} (Ω : Domain n) (A : MatrixField n) : Prop :=
  ∀ᵐ x ∂domainMeasure Ω, ∀ i j, A x i j = A x j i

abbrev zeroInclusion {n : ℕ} (Ω : Domain n) : H10 ℝ Ω →L[ℝ] H ℝ Ω 1 :=
  (hZeroSubmodule ℝ Ω).subtypeL

def Solves {n : ℕ} (Ω : Domain n) (A : MatrixField n)
    (f : Hminus1 ℝ Ω) (u : H ℝ Ω 1) : Prop :=
  ∀ v : H10 ℝ Ω, ellipticEnergyForm Ω A u v.val = f v

/-- The affine functional is parameterized by z, so f is only applied on H₀¹. -/
def AffineEnergy {n : ℕ} (Ω : Domain n) (A : MatrixField n)
    (f : Hminus1 ℝ Ω) (w : H ℝ Ω 1) (z : H10 ℝ Ω) : ℝ :=
  (1 / 2 : ℝ) * ellipticEnergyForm Ω A (w + z.val) (w + z.val) - f z

/-- Concrete form bridge. Constants are independent of A and lam; no boundary
regularity or symmetry is required. Norm equivalence is on the actual closure. -/
def FormBridgeStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ (Ω : Domain n),
    Bornology.IsBounded (Ω : Set (Space n)) →
    ∃ C : ℝ, 0 < C ∧
      (∀ u : H10 ℝ Ω, ‖u‖ ≤ C * ‖hGradient u.val‖) ∧
      ∀ (A : MatrixField n), MemLp A ∞ (domainMeasure Ω) →
        ∃ B : H ℝ Ω 1 →L[ℝ] H ℝ Ω 1 →L[ℝ] ℝ,
          (∀ u v, B u v = ellipticEnergyForm Ω A u v) ∧
          (∀ u v, ‖B u v‖ ≤ C * CoefficientNorm Ω A * ‖u‖ * ‖v‖) ∧
          ∀ lam : ℝ, 0 < lam → Elliptic Ω A lam →
            ∀ u : H10 ℝ Ω, (lam / C ^ 2) * ‖u‖ ^ 2 ≤ B u.val u.val

def HomogeneousStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ (Ω : Domain n),
    Bornology.IsBounded (Ω : Set (Space n)) →
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : MatrixField n), MemLp A ∞ (domainMeasure Ω) →
        ∀ lam : ℝ, 0 < lam → Elliptic Ω A lam →
          ∀ f : Hminus1 ℝ Ω,
            ∃ u : H10 ℝ Ω,
              Solves Ω A f u.val ∧ ‖u‖ ≤ C * lam⁻¹ * ‖f‖ ∧
              ∀ v : H10 ℝ Ω, Solves Ω A f v.val → v = u

/-- The trace and lifting operators are chosen once per domain and agree with
smooth restrictions. This states the same trace-g problem in every n ≥ 1. -/
def NonhomogeneousStatement : Prop :=
  ∀ (m : ℕ) (Ω : Domain (m + 1)) (hΩ : IsBoundedLipschitzOpen Ω),
    ∃ (T : H ℝ Ω 1 →L[ℝ] Hhalf Ω hΩ)
      (L : Hhalf Ω hΩ →L[ℝ] H ℝ Ω 1) (C : ℝ),
      Trace.AgreesWithSmooth T ∧ (∀ g, T (L g) = g) ∧
      T.ker = hZeroSubmodule ℝ Ω ∧ 0 < C ∧
      ∀ (A : MatrixField (m + 1)), MemLp A ∞ (domainMeasure Ω) →
        ∀ lam : ℝ, 0 < lam → Elliptic Ω A lam →
          ∀ (f : Hminus1 ℝ Ω) (g : Hhalf Ω hΩ),
            ∃ u : H ℝ Ω 1,
              (T u = g ∧ Solves Ω A f u) ∧
              ‖u‖ ≤ C * (lam⁻¹ * ‖f‖ +
                (1 + lam⁻¹ * CoefficientNorm Ω A) * ‖g‖) ∧
              ∀ v : H ℝ Ω 1, T v = g ∧ Solves Ω A f v → v = u

/-- Lift change, the exact energy increment, and uniqueness among ALL affine
competitors. The affine class is represented without applying f to H¹. -/
def SymmetricEnergyStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ (Ω : Domain n),
    Bornology.IsBounded (Ω : Set (Space n)) →
    ∀ (A : MatrixField n), MemLp A ∞ (domainMeasure Ω) →
      ∀ lam : ℝ, 0 < lam → Elliptic Ω A lam → Symmetric Ω A →
        ∀ (f : Hminus1 ℝ Ω) (w : H ℝ Ω 1),
          (∀ (q z : H10 ℝ Ω),
            AffineEnergy Ω A f (w + q.val) (z - q) =
              AffineEnergy Ω A f w z + f q) ∧
          ∃ z : H10 ℝ Ω,
            Solves Ω A f (w + z.val) ∧
            (∀ v : H10 ℝ Ω,
              AffineEnergy Ω A f w (z + v) - AffineEnergy Ω A f w z =
                (1 / 2 : ℝ) * ellipticEnergyForm Ω A v.val v.val) ∧
            (∀ y : H10 ℝ Ω, AffineEnergy Ω A f w z ≤ AffineEnergy Ω A f w y) ∧
            ∀ y : H10 ℝ Ω,
              (∀ v : H10 ℝ Ω, AffineEnergy Ω A f w y ≤ AffineEnergy Ω A f w v) → y = z

end P201Specs.Dirichlet
