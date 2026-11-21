import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.Herglotz
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.BlaschkeProducts

/-! Independent statements for paper.tex, `fa2:p5:blaschke-interpolation`,
lines 23475–23512 in the adopted source. Repeated nodes are permitted; no
separation, nonemptiness or strict modulus condition is imposed on the data. -/
noncomputable section
open Set MeasureTheory

namespace ExpandedFA.PartV.BlaschkeInterpolation
open ExpandedFA.PartIV.PositiveHarmonic
open ExpandedFA.PartIV.BlaschkeProducts

/-- An actual finite product, including an empty zero list and repeated zeros.
The normalization of each factor agrees with the upstream Blaschke interface. -/
structure FiniteBlaschke where
  degree : ℕ
  phase : ℂ
  phase_norm : ‖phase‖ = 1
  zeros : Fin degree → ℂ
  zeros_mem : ∀ i, zeros i ∈ unitDisk

def FiniteBlaschke.eval (B : FiniteBlaschke) (z : ℂ) : ℂ :=
  B.phase * ∏ i, factor (B.zeros i) z

/-- The admissible holomorphic functions of the proposition, only constrained
on the open disk. This includes constants of modulus one. -/
def Schur (f : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ f unitDisk ∧ ∀ z ∈ unitDisk, ‖f z‖ ≤ 1

def Feasible {n : ℕ} (z w : Fin n → ℂ) : Prop :=
  ∃ f : ℂ → ℂ, Schur f ∧ ∀ j, f (z j) = w j

namespace Spec

def Interpolation : Prop :=
  ∀ (n : ℕ) (z w : Fin n → ℂ), (∀ j, z j ∈ unitDisk) → Feasible z w →
    ∃ B : FiniteBlaschke, ∀ j, B.eval (z j) = w j

/-- Finite atomic Herglotz reduction: the same probability weights work at
every node, with at most 2n+1 circle points. Zero weights/repeated points do
not increase the actual support. This is also valid for n=0. -/
def AtomicHerglotzSamples : Prop :=
  ∀ (n : ℕ) (z : Fin n → ℂ), (∀ j, z j ∈ unitDisk) →
    ∀ (μ : Measure Circle), IsProbabilityMeasure μ →
    ∃ m ≤ 2 * n + 1, ∃ (ζ : Fin m → Circle) (w : Fin m → ℝ),
      (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧
      ∀ j, ∑ i, (w i : ℂ) * (((ζ i : Circle) : ℂ) + z j) /
          (((ζ i : Circle) : ℂ) - z j) =
        ∫ ξ : Circle, ((ξ : ℂ) + z j) / ((ξ : ℂ) - z j) ∂μ

/-- The unnormalized version retains zero measures and their zero total mass. -/
def FiniteMeasureSamples : Prop :=
  ∀ (n : ℕ) (z : Fin n → ℂ), (∀ j, z j ∈ unitDisk) →
    ∀ (μ : Measure Circle), IsFiniteMeasure μ →
    ∃ m ≤ 2 * n + 1, ∃ (ζ : Fin m → Circle) (w : Fin m → ℝ),
      (∀ i, 0 ≤ w i) ∧ ∑ i, w i = μ.real univ ∧
      ∀ j, ∑ i, (w i : ℂ) * (((ζ i : Circle) : ℂ) + z j) /
          (((ζ i : Circle) : ℂ) - z j) =
        ∫ ξ : Circle, ((ξ : ℂ) + z j) / ((ξ : ℂ) - z j) ∂μ

/-- A generic bridge sufficient for the remaining construction. The values
at circle atoms must be filled by holomorphic extension, not pointwise 0/0. -/
def AtomicCayleyExtension : Prop :=
  ∀ (m : ℕ) (ζ : Fin m → Circle) (w : Fin m → ℝ) (c : ℝ),
    (∀ i, 0 ≤ w i) → 0 < ∑ i, w i →
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G (Metric.closedBall 0 1) ∧
      (∀ z : ℂ, ‖z‖ = 1 → ‖G z‖ = 1) ∧
      ∀ z ∈ unitDisk, G z =
        ((Complex.I * (c : ℂ) + ∑ i, (w i : ℂ) *
            (((ζ i : Circle) : ℂ) + z) / (((ζ i : Circle) : ℂ) - z)) - 1) /
        ((Complex.I * (c : ℂ) + ∑ i, (w i : ℂ) *
            (((ζ i : Circle) : ℂ) + z) / (((ζ i : Circle) : ℂ) - z)) + 1)

/-- The factorization bridge includes degree zero; the equality is needed
only on the disk. Analyticity on a neighborhood of the closed disk is enough
for the atomic construction, so no extra rationality hypothesis is needed. -/
def ClosedDiskFactorization : Prop :=
  ∀ G : ℂ → ℂ, AnalyticOnNhd ℂ G (Metric.closedBall 0 1) →
    (∀ z : ℂ, ‖z‖ = 1 → ‖G z‖ = 1) →
    ∃ B : FiniteBlaschke, Set.EqOn B.eval G unitDisk

/-- Explicitly conditional assembly, not the unconditional interpolation target. -/
def BridgeAssembly : Prop := AtomicCayleyExtension → ClosedDiskFactorization → Interpolation

def EmptyData : Prop :=
  ∃ B : FiniteBlaschke, B.degree = 0 ∧ ∀ z : ℂ, B.eval z = 1

def RepeatedConsistency : Prop :=
  ∀ (n : ℕ) (z w : Fin n → ℂ), Feasible z w →
    ∀ i j, z i = z j → w i = w j

def BoundaryConstant : Prop :=
  ∀ f : ℂ → ℂ, Schur f → ∀ a ∈ unitDisk, ‖f a‖ = 1 →
    ∀ z ∈ unitDisk, f z = f a

def BoundaryInterpolation : Prop :=
  ∀ (n : ℕ) (z w : Fin n → ℂ), (∀ j, z j ∈ unitDisk) → Feasible z w →
    (∃ j, ‖w j‖ = 1) →
    ∃ B : FiniteBlaschke, B.degree = 0 ∧ ∀ j, B.eval (z j) = w j

def ProductGeometry : Prop :=
  ∀ B : FiniteBlaschke, Schur B.eval ∧
    ∀ z : ℂ, ‖z‖ = 1 → ‖B.eval z‖ = 1

end Spec
end ExpandedFA.PartV.BlaschkeInterpolation
