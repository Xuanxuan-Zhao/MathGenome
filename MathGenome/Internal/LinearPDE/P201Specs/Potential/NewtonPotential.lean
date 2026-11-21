import MathGenome.Internal.LinearPDE.P201Specs.Potential.Fundamental
import MathGenome.Internal.FourierSobolev.P102.U4.DistributionConvolution

noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ContDiff
namespace P201Specs

/-- The ordinary Newton integral, with the kernel fixed by the fundamental-solution goal. -/
def newtonPotential {n : ℕ} (f : Test ℝ (⊤ : Domain n)) (x : Space n) : ℝ :=
  ∫ y, fundamentalKernel n y * f (x - y)

def newtonPotentialType := {n : ℕ} → Test ℝ (⊤ : Domain n) → Space n → ℝ

/-- The compactness witness is essential: the inner pairing is then an actual test. -/
def newtonDistribution {n : ℕ} (F : Distribution ℝ (⊤ : Domain n))
    (hF : IsCompact (P102.U4.relativeSupport F)) : Distribution ℝ (⊤ : Domain n) :=
  P102.U4.rightCompactConvolution (regularDistribution ⊤ (fundamentalKernel n)) F hF

def newtonDistributionType := {n : ℕ} → (F : Distribution ℝ (⊤ : Domain n)) →
  IsCompact (P102.U4.relativeSupport F) → Distribution ℝ (⊤ : Domain n)

def newtonIntegrableStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ f : Test ℝ (⊤ : Domain n), ∀ x : Space n,
    Integrable (fun y => fundamentalKernel n y * f (x - y)) volume

def newtonSmoothStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ f : Test ℝ (⊤ : Domain n),
    ContDiff ℝ (⊤ : ℕ∞) (newtonPotential f)

def newtonEquationStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ f : Test ℝ (⊤ : Domain n),
    ∀ x : Space n, -laplacian (newtonPotential f) x = f x

def newtonDistributionEquationStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ (F : Distribution ℝ (⊤ : Domain n))
    (hF : IsCompact (P102.U4.relativeSupport F)),
    -distributionLaplacian (newtonDistribution F hF) = F

/-- All conclusions of the normalized fundamental-solution theorem, in every positive dimension. -/
def normalizedNewtonTheoremStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    LocallyIntegrable (fundamentalKernel n) volume ∧
    -distributionLaplacian (regularDistribution (⊤ : Domain n) (fundamentalKernel n)) =
      originDirac n ∧
    (∀ f : Test ℝ (⊤ : Domain n),
      ContDiff ℝ (⊤ : ℕ∞) (newtonPotential f) ∧
      ∀ x : Space n, -laplacian (newtonPotential f) x = f x) ∧
    ∀ (F : Distribution ℝ (⊤ : Domain n))
      (hF : IsCompact (P102.U4.relativeSupport F)),
      -distributionLaplacian (newtonDistribution F hF) = F

end P201Specs
