import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch03.PathsChains
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.BvDefinition
import Mathlib.Topology.UniformSpace.UniformConvergence

/-! Polygonal length and the estimates of paper.tex:586–619. Length is the
literal strict endpoint-partition supremum, represented in ℝ≥0∞ before taking
its real value. Finiteness is a theorem, not a premise or a certificate.
All speed integrals retain the one-sided derivatives on the original C1 pieces.
-/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ENNReal

namespace D12Complex
namespace ComplexPath

def polygonalLength (γ : ComplexPath) : ℝ :=
  (Specs.D11.Ch12.variation_value (γ : ℝ → ℂ) γ.a γ.b).toReal

end ComplexPath
namespace C1Partition

def speedIntegral {γ : ComplexPath} (P : C1Partition γ) : ℝ :=
  ∑ i : Fin P.count, ∫ t in P.node i.castSucc..P.node i.succ,
    ‖derivWithin γ (P.pieceSet i) t‖

def weightedSpeedIntegral {γ : ComplexPath} (P : C1Partition γ) (f : ℂ → ℂ) : ℝ :=
  ∑ i : Fin P.count, ∫ t in P.node i.castSucc..P.node i.succ,
    ‖f (γ t)‖ * ‖derivWithin γ (P.pieceSet i) t‖

end C1Partition
namespace PiecewiseC1Path

def length (γ : PiecewiseC1Path) : ℝ := γ.path.polygonalLength

def traceSupNorm (γ : PiecewiseC1Path) (f : ℂ → ℂ) : ℝ :=
  sSup ((fun z => ‖f z‖) '' γ.trace)

end PiecewiseC1Path
namespace IntegralChain

def lengthBound (Γ : IntegralChain) : ℝ :=
  ∑ γ ∈ Γ.support, |(Γ γ : ℝ)| * γ.length

def traceSupNorm (Γ : IntegralChain) (f : ℂ → ℂ) : ℝ :=
  sSup ((fun z => ‖f z‖) '' Γ.trace)

end IntegralChain
end D12Complex

namespace Specs.D12Complex.Ch03.PiecewiseC1Length
open _root_.D12Complex

def polygonalLength_type := ComplexPath → ℝ
def polygonalLength_value : polygonalLength_type := ComplexPath.polygonalLength

def speedIntegral_type := {γ : ComplexPath} → C1Partition γ → ℝ
def speedIntegral_value : speedIntegral_type := C1Partition.speedIntegral

def weightedSpeedIntegral_type := {γ : ComplexPath} → C1Partition γ → (ℂ → ℂ) → ℝ
def weightedSpeedIntegral_value : weightedSpeedIntegral_type := C1Partition.weightedSpeedIntegral

def length_type := PiecewiseC1Path → ℝ
def length_value : length_type := PiecewiseC1Path.length

def traceSupNorm_type := PiecewiseC1Path → (ℂ → ℂ) → ℝ
def traceSupNorm_value : traceSupNorm_type := PiecewiseC1Path.traceSupNorm

def chainLengthBound_type := IntegralChain → ℝ
def chainLengthBound_value : chainLengthBound_type := IntegralChain.lengthBound

def chainTraceSupNorm_type := IntegralChain → (ℂ → ℂ) → ℝ
def chainTraceSupNorm_value : chainTraceSupNorm_type := IntegralChain.traceSupNorm

/-- The actual supremum is finite and equals the speed integral for every
valid smooth partition. This also states independence of the chosen pieces. -/
def variation_eq_speedIntegral_type : Prop :=
  ∀ {γ : ComplexPath} (P : C1Partition γ),
    Specs.D11.Ch12.variation_value (γ : ℝ → ℂ) γ.a γ.b =
      ENNReal.ofReal P.speedIntegral

def polygonalLength_eq_iSup_type : Prop :=
  ∀ γ : PiecewiseC1Path, γ.length =
    ⨆ p : _root_.D11.Ch12.IntervalPartition γ.path.a γ.path.b,
      ∑ i ∈ Finset.range p.length, ‖γ (p.point (i + 1)) - γ (p.point i)‖

def length_eq_speedIntegral_type : Prop :=
  ∀ (γ : PiecewiseC1Path) (P : C1Partition γ.path), γ.length = P.speedIntegral

def speedIntegral_independent_type : Prop :=
  ∀ {γ : ComplexPath} (P Q : C1Partition γ), P.speedIntegral = Q.speedIntegral

def length_eq_integral_norm_deriv_type : Prop :=
  ∀ γ : PiecewiseC1Path,
    γ.length = ∫ t in γ.path.a..γ.path.b, ‖deriv γ t‖

def length_degenerate_type : Prop :=
  ∀ γ : PiecewiseC1Path, γ.path.a = γ.path.b → γ.length = 0

def length_constant_type : Prop :=
  ∀ (γ : PiecewiseC1Path) (z : ℂ),
    (∀ t ∈ Icc γ.path.a γ.path.b, γ t = z) → γ.length = 0

def norm_integral_le_weightedSpeedIntegral_type : Prop :=
  ∀ (γ : PiecewiseC1Path) (P : C1Partition γ.path) (f : ℂ → ℂ),
    ContinuousOn f γ.trace → ‖γ.integral f‖ ≤ P.weightedSpeedIntegral f

def weightedSpeedIntegral_le_length_mul_type : Prop :=
  ∀ (γ : PiecewiseC1Path) (P : C1Partition γ.path) (f : ℂ → ℂ),
    ContinuousOn f γ.trace →
    P.weightedSpeedIntegral f ≤ γ.length * γ.traceSupNorm f

def contour_estimates_type : Prop :=
  ∀ (γ : PiecewiseC1Path) (f : ℂ → ℂ), ContinuousOn f γ.trace →
    ‖γ.integral f‖ ≤ (∫ t in γ.path.a..γ.path.b, ‖f (γ t)‖ * ‖deriv γ t‖) ∧
    (∫ t in γ.path.a..γ.path.b, ‖f (γ t)‖ * ‖deriv γ t‖) ≤
      γ.length * γ.traceSupNorm f

def norm_integral_le_length_mul_type : Prop :=
  ∀ (γ : PiecewiseC1Path) (f : ℂ → ℂ), ContinuousOn f γ.trace →
    ‖γ.integral f‖ ≤ γ.length * γ.traceSupNorm f

def integral_tendsto_uniform_type : Prop :=
  ∀ (γ : PiecewiseC1Path) (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ),
    (∀ n, ContinuousOn (F n) γ.trace) →
    TendstoUniformlyOn F f atTop γ.trace →
    Tendsto (fun n => γ.integral (F n)) atTop (𝓝 (γ.integral f))

def chain_norm_integral_le_sum_type : Prop :=
  ∀ (Γ : IntegralChain) (f : ℂ → ℂ), ContinuousOn f Γ.trace →
    ‖Γ.integral f‖ ≤ ∑ γ ∈ Γ.support,
      |(Γ γ : ℝ)| * (γ.length * γ.traceSupNorm f)

def chain_norm_integral_le_length_mul_type : Prop :=
  ∀ (Γ : IntegralChain) (f : ℂ → ℂ), ContinuousOn f Γ.trace →
    ‖Γ.integral f‖ ≤ Γ.lengthBound * Γ.traceSupNorm f

def chain_integral_tendsto_uniform_type : Prop :=
  ∀ (Γ : IntegralChain) (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ),
    (∀ n, ContinuousOn (F n) Γ.trace) →
    TendstoUniformlyOn F f atTop Γ.trace →
    Tendsto (fun n => Γ.integral (F n)) atTop (𝓝 (Γ.integral f))

end Specs.D12Complex.Ch03.PiecewiseC1Length
