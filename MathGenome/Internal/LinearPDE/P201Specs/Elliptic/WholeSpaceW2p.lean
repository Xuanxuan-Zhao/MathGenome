import MathGenome.Internal.LinearPDE.P201Specs.Common.SpatialInterfaces
import MathGenome.Internal.FourierSobolev.Specs.P102.U3.RieszTransforms
import MathGenome.Internal.FourierSobolev.P102.U3.RieszL2Multiplier

/-! Independent statements for the whole-space assertion of
`pde:elliptic-poisson-w2p`. The Hessian norm is the sum of the Lᵖ norms
of its n² entries (a concrete, standard finite-product norm). All derivatives
are the shared ordinary multi-index derivatives, with Euclidean volume. -/
noncomputable section
open MeasureTheory
open scoped ContDiff FourierTransform ENNReal

namespace P201Specs.Elliptic.WholeSpaceW2p

abbrev HessianEntry {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (u : Space n → 𝕜) (i j : Fin n) : Space n → 𝕜 :=
  multiPartial u ({i, j} : MultiIndex n)

def hessianLpNorm {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (p : ℝ≥0∞) (u : Space n → 𝕜) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, (eLpNorm (HessianEntry u i j) p volume).toReal

/-- Bundled ordinary Hessian entries, for the Fourier/L² calculation. -/
def schwartzHessian {n : ℕ} (u : SchwartzMap (Space n) ℂ) (i j : Fin n) :
    SchwartzMap (Space n) ℂ := P102.U3.coordinatePartial ![i, j] u

/-- Bundled -Δ, with the shared positive-elliptic sign. -/
def negativeLaplacianSchwartz {n : ℕ} (u : SchwartzMap (Space n) ℂ) :
    SchwartzMap (Space n) ℂ := -∑ i : Fin n, schwartzHessian u i i

/-- No multiplier or PDE identity is assumed. -/
def L2RepresentationStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (u : SchwartzMap (Space n) ℂ) (i j : Fin n),
    P102.U3.Riesz.rieszL2 i
      (P102.U3.Riesz.rieszL2 j ((negativeLaplacianSchwartz u).toLp 2)) =
        (schwartzHessian u i j).toLp 2

/-- Agreement with L² is required on the entire intersection, not just tests.
The result identifies the composed Lᵖ action with the ordinary Hessian. -/
def LpRepresentationStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (p : P102.U2.CZLpData.Exponent)
    (R : Fin n → P102.U2.CZLpData.StrongOperator n p),
    (∀ i, P102.U2.CZLpData.Agrees (P102.U3.Riesz.rieszL2 i) p (R i)) →
    ∀ (u : SchwartzMap (Space n) ℂ) (i j : Fin n),
      R i (R j ((negativeLaplacianSchwartz u).toLp p.val)) =
        (schwartzHessian u i j).toLp p.val

def SchwartzBridgeStatement : Prop :=
  ∀ (n : ℕ) (u : SchwartzMap (Space n) ℂ),
    (∀ (i j : Fin n) (x : Space n),
      schwartzHessian u i j x = HessianEntry (u : Space n → ℂ) i j x) ∧
    (∀ x : Space n, negativeLaplacianSchwartz u x = -laplacian (u : Space n → ℂ) x)

/-- Quantification over real p retains exactly 1 < p < ∞; every real p is finite.
Membership is explicit so the finite norm is never a totalized infinite norm. -/
def ComplexEstimateStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (p : ℝ), 1 < p →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : Space n → ℂ),
      ContDiff ℝ (⊤ : ℕ∞) u → HasCompactSupport u →
      (∀ i j : Fin n, MemLp (HessianEntry u i j) (ENNReal.ofReal p) volume) ∧
      MemLp (laplacian u) (ENNReal.ofReal p) volume ∧
      hessianLpNorm (ENNReal.ofReal p) u ≤
        C * (eLpNorm (laplacian u) (ENNReal.ofReal p) volume).toReal

/-- The original real scalar assertion, including n=1. -/
def RealEstimateStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (p : ℝ), 1 < p →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : Space n → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) u → HasCompactSupport u →
      (∀ i j : Fin n, MemLp (HessianEntry u i j) (ENNReal.ofReal p) volume) ∧
      MemLp (laplacian u) (ENNReal.ofReal p) volume ∧
      hessianLpNorm (ENNReal.ofReal p) u ≤
        C * (eLpNorm (laplacian u) (ENNReal.ofReal p) volume).toReal

/-- The usual Frobenius Hessian, flattened into a Euclidean vector.
Its pointwise norm is sqrt(Σᵢⱼ |∂ᵢ∂ⱼu|²). -/
def hessian {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (u : Space n → 𝕜)
    (x : Space n) : EuclideanSpace 𝕜 (Fin n × Fin n) :=
  WithLp.toLp 2 (fun ij => HessianEntry u ij.1 ij.2 x)

def FrobeniusEstimateStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (p : ℝ), 1 < p →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : Space n → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) u → HasCompactSupport u →
      MemLp (hessian u) (ENNReal.ofReal p) volume ∧
      MemLp (laplacian u) (ENNReal.ofReal p) volume ∧
      (eLpNorm (hessian u) (ENNReal.ofReal p) volume).toReal ≤
        C * (eLpNorm (laplacian u) (ENNReal.ofReal p) volume).toReal

end P201Specs.Elliptic.WholeSpaceW2p
