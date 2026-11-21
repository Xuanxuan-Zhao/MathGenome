import MathGenome.Internal.FourierSobolev.Specs.P102.U2.MaximalTruncation

/-! The remaining conclusions of Theorem p102:U2-05 (paper.tex:990–1011).
The input assumptions and actual truncations are those of MaximalTruncation.
Convergence is along all positive real radii. The limit is identified with every
bounded extension agreeing with the original L² action, hence in particular with
the compatible family supplied by CZLp. -/
noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology

namespace Specs.P102.U2.PrincipalValues
open _root_.P102.U2.CZWeak _root_.P102.U2.CZLpData
open _root_.P102.U2.MaximalTruncationData

/-- Both senses of convergence, with membership at every positive radius.
The eLpNorm expression is the norm of the difference in the actual Lp space,
written on representatives so it does not require a choice of truncation class. -/
def Convergence {d : ℕ} (K : Point d → ℂ) (p : Exponent)
    (R : StrongOperator d p) : Prop :=
  ∀ (f : Point d → ℂ) (hf : MemLp f p.val volume),
    (∀ ε : ℝ, 0 < ε → MemLp (truncated K f ε) p.val volume) ∧
    (∀ᵐ x ∂volume, Tendsto (fun ε => truncated K f ε x) (𝓝[>] 0)
      (𝓝 ((R (hf.toLp f) : Point d → ℂ) x))) ∧
    Tendsto (fun ε => eLpNorm
      (fun x => truncated K f ε x - (R (hf.toLp f) : Point d → ℂ) x) p.val volume)
      (𝓝[>] 0) (𝓝 0)

def convergence : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (K : Point d → ℂ) (B : ℝ≥0) (T : Operator d),
    KernelRegularity K B → SmoothL2Action T K →
    ∀ (p : Exponent) (R : StrongOperator d p), Agrees T p R → Convergence K p R

/-- The full result, including a compatible family and the strong maximal
estimate. Absolute existence, measurable/rational realization and representative
independence are retained explicitly in the last conjunct. -/
def full_theorem : Prop :=
  ∃ C : (d : ℕ) → (Point d → ℂ) → ℝ≥0 → ℝ≥0 → Exponent → ℝ≥0,
    ∀ (d : ℕ), 0 < d → ∀ (K : Point d → ℂ) (B : ℝ≥0) (T : Operator d),
      KernelRegularity K B → SmoothL2Action T K →
      ∃ R : ∀ p : Exponent, StrongOperator d p,
        (∀ p, Agrees T p (R p)) ∧ PairwiseCompatible R ∧
        (∀ p, Convergence K p (R p)) ∧
        (∀ (p : Exponent) (f : Point d → ℂ), MemLp f p.val volume →
          ((∫⁻ x, maximalTruncation K f x ^ p.val.toReal) ^ (1 / p.val.toReal) ≤
            (C d K B ‖T‖₊ p : ℝ≥0∞) * eLpNorm f p.val volume) ∧
          (∀ᵐ x ∂volume, maximalTruncation K f x < ∞) ∧
          MemLp (fun x => (maximalTruncation K f x).toReal) p.val volume ∧
          eLpNorm (fun x => (maximalTruncation K f x).toReal) p.val volume ≤
            (C d K B ‖T‖₊ p : ℝ≥0∞) * eLpNorm f p.val volume) ∧
        (∀ (p : Exponent) (f : Point d → ℂ), MemLp f p.val volume →
          (∀ (ε : ℝ), 0 < ε → ∀ x,
            IntegrableOn (fun y => K (x - y) * f y) {y | ε < ‖x - y‖} volume) ∧
          Measurable (maximalTruncation K f) ∧
          (∀ x, ContinuousOn (fun ε => truncated K f ε x) (Ioi 0)) ∧
          (∀ x, maximalTruncation K f x =
            ⨆ (q : ℚ) (_ : 0 < q), ‖truncated K f (q : ℝ) x‖ₑ) ∧
          (∀ g : Point d → ℂ, f =ᵐ[volume] g →
            (∀ (ε : ℝ) (x : Point d), truncated K f ε x = truncated K g ε x) ∧
            maximalTruncation K f = maximalTruncation K g))

end Specs.P102.U2.PrincipalValues
