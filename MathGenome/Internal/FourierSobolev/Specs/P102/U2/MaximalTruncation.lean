import MathGenome.Internal.FourierSobolev.Specs.P102.U2.CZLp
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SingularIntegrals.MaximalWeakBound
import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-!
Independent statements for the maximal/Cotlar stage of Theorem p102:U2-05,
paper.tex:990–1007 (parts/u2.tex:202–219). General-input principal-value
convergence is assigned to P102.U2.PrincipalValues, not asserted as a premise here.
All functions and Lp classes use native Euclidean volume, as in CZLp.
-/
noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology

namespace P102.U2.MaximalTruncationData
open CZWeak CZLpData

abbrev Tests (d : ℕ) :=
  ExpandedFA.SingularIntegrals.StandardConvolution.Tests ℂ d

/-- C¹, positive-dilation homogeneity, spherical cancellation, and the stated
coordinate-gradient bound. The value at the origin is unrestricted. Sphere
measure is the polar-coordinate surface measure induced by Euclidean volume;
in dimension one this gives mass one to each of the two unit vectors. -/
structure KernelRegularity {d : ℕ} (K : Point d → ℂ) (B : ℝ≥0) : Prop where
  contDiff : ContDiffOn ℝ 1 K ({0}ᶜ : Set (Point d))
  homogeneous : ∀ (r : ℝ), 0 < r → ∀ z : Point d, z ≠ 0 →
    K (r • z) = ((r ^ d)⁻¹ : ℝ) • K z
  sphereMeanZero :
    (∫ z : sphere (0 : Point d) 1, K z ∂(volume : Measure (Point d)).toSphere) = 0
  gradient : ∀ z ≠ 0, gradientNorm K z ≤ (B : ℝ) / ‖z‖ ^ (d + 1)

/-- Ordinary complex Lebesgue truncation. Absolute existence is a theorem
conclusion below, so the totalized integral does not stand for convergence. -/
def truncated {d : ℕ} (K f : Point d → ℂ) (ε : ℝ) (x : Point d) : ℂ :=
  ∫ y in {y : Point d | ε < ‖x - y‖}, K (x - y) * f y

/-- Extended values preserve possibly infinite maximal truncations. -/
def maximalTruncation {d : ℕ} (K f : Point d → ℂ) (x : Point d) : ℝ≥0∞ :=
  ⨆ (ε : ℝ) (_ : 0 < ε), ‖truncated K f ε x‖ₑ

/-- The candidate smooth principal value; existence and convergence to this
value are proved in `smooth_principal_value`, not assumed by this definition. -/
def principalValue {d : ℕ} (K : Point d → ℂ) (φ : Tests d) (x : Point d) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) (fun ε => truncated K φ ε x)

/-- The source L² assumption only identifies the bounded operator with the
principal-value action on smooth compactly supported inputs. -/
def SmoothL2Action {d : ℕ} (T : Operator d) (K : Point d → ℂ) : Prop :=
  ∀ φ : Tests d,
    (T (ExpandedFA.SingularIntegrals.StandardConvolution.testL2 φ) : Point d → ℂ)
      =ᵐ[volume] principalValue K φ

/-- Centered Hardy–Littlewood maximal function on the same native volume.
Its lintegral definition also applies before local integrability is known. -/
abbrev centeredMaximal {d : ℕ} {F : Type} [NormedAddCommGroup F]
    (f : Point d → F) : Point d → ℝ≥0∞ :=
  ExpandedFA.SingularIntegrals.MaximalWeakBoundSpec.MaximalValue volume f

end P102.U2.MaximalTruncationData

namespace Specs.P102.U2.MaximalTruncation
open _root_.P102.U2.CZWeak _root_.P102.U2.CZLpData
open _root_.P102.U2.MaximalTruncationData

/-- Smooth-input convergence at every point, without an L² assumption. -/
def smooth_principal_value : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (K : Point d → ℂ) (B : ℝ≥0),
    KernelRegularity K B → ∀ (φ : Tests d) (x : Point d),
      (∀ ε : ℝ, 0 < ε →
        IntegrableOn (fun y => K (x - y) * φ y) {y | ε < ‖x - y‖} volume) ∧
      Tendsto (fun ε => truncated K φ ε x) (𝓝[>] 0) (𝓝 (principalValue K φ x))

/-- The full compact-L² representation needed by CZLp is a conclusion, not
an assumption. The dimension-only difference constant is uniform in K and T.
Absolute existence outside every a.e. compact support is also explicit. -/
def kernel_representation : Prop :=
  ∃ C : ℕ → ℝ≥0, ∀ (d : ℕ), 0 < d →
    ∀ (K : Point d → ℂ) (B : ℝ≥0) (T : Operator d),
      KernelRegularity K B → SmoothL2Action T K →
      KernelHypotheses T K (C d * B) ∧
      ∀ (b : Point d → ℂ), MemLp b 2 volume → ∀ S : Set (Point d),
        IsCompact S → (∀ᵐ y ∂volume, y ∉ S → b y = 0) →
        ∀ x ∉ S, Integrable (fun y => K (x - y) * b y) volume

/-- The substantive Cotlar estimate with all 0<δ<1. Constants are uniform in
T at a fixed L² norm and depend only on dimension, δ, and the kernel data. -/
def cotlar : Prop :=
  ∃ C : (d : ℕ) → (Point d → ℂ) → ℝ≥0 → ℝ≥0 → ℝ → ℝ≥0,
    ∀ (d : ℕ), 0 < d → ∀ (K : Point d → ℂ) (B : ℝ≥0) (T : Operator d),
      KernelRegularity K B → SmoothL2Action T K →
      ∀ (δ : ℝ), 0 < δ → δ < 1 → ∀ φ : Tests d,
        ∀ᵐ x ∂volume, maximalTruncation K φ x ≤ (C d K B ‖T‖₊ δ : ℝ≥0∞) *
          ((centeredMaximal (fun y => ‖T
            (ExpandedFA.SingularIntegrals.StandardConvolution.testL2 φ) y‖ ^ δ) x) ^
              (1 / δ) + centeredMaximal (φ : Point d → ℂ) x)

/-- Measurable, absolutely existing realization on every Lp, without needing
the L² assumption or a maximal bound. Rational radii suffice for the supremum,
but all integrability and continuity assertions retain arbitrary real radii. -/
def truncation_realization : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (K : Point d → ℂ) (B : ℝ≥0),
    KernelRegularity K B →
    ∀ (p : Exponent) (f : Point d → ℂ), MemLp f p.val volume →
      (∀ (ε : ℝ), 0 < ε → ∀ x,
        IntegrableOn (fun y => K (x - y) * f y) {y | ε < ‖x - y‖} volume) ∧
      Measurable (maximalTruncation K f) ∧
      (∀ x, ContinuousOn (fun ε => truncated K f ε x) (Ioi 0)) ∧
      (∀ x, maximalTruncation K f x =
        ⨆ (q : ℚ) (_ : 0 < q), ‖truncated K f (q : ℝ) x‖ₑ) ∧
      (∀ g : Point d → ℂ, f =ᵐ[volume] g →
        (∀ (ε : ℝ) (x : Point d), truncated K f ε x = truncated K g ε x) ∧
        maximalTruncation K f = maximalTruncation K g)

/-- The strong maximal estimate on every finite Lp above one, with uniform
constants at fixed kernel data and L² norm. The extended moment estimate
retains infinite values until a.e. finiteness is proved. -/
def maximal_bound : Prop :=
  ∃ C : (d : ℕ) → (Point d → ℂ) → ℝ≥0 → ℝ≥0 → Exponent → ℝ≥0,
    ∀ (d : ℕ), 0 < d → ∀ (K : Point d → ℂ) (B : ℝ≥0) (T : Operator d),
      KernelRegularity K B → SmoothL2Action T K →
      ∀ (p : Exponent) (f : Point d → ℂ), MemLp f p.val volume →
        ((∫⁻ x, maximalTruncation K f x ^ p.val.toReal) ^ (1 / p.val.toReal) ≤
          (C d K B ‖T‖₊ p : ℝ≥0∞) * eLpNorm f p.val volume) ∧
        (∀ᵐ x ∂volume, maximalTruncation K f x < ∞) ∧
        MemLp (fun x => (maximalTruncation K f x).toReal) p.val volume ∧
        eLpNorm (fun x => (maximalTruncation K f x).toReal) p.val volume ≤
          (C d K B ‖T‖₊ p : ℝ≥0∞) * eLpNorm f p.val volume

end Specs.P102.U2.MaximalTruncation
