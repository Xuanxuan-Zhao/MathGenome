import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.HardyLowpass

/-!
Independent specification for paper.tex, `fa2:p4:hardy-compact-transfer`.
The chapter's convention is d ≥ 1. The lowpass is the actual Schwartz
function supplied by HardyLowpass; no transfer or cancellation estimate is
included in its hypotheses. Constants are chosen before f, x, ψ, t and z.
The real-valued estimates use `toReal` only under the explicit finiteness
hypothesis on the pointwise ENNReal Peetre supremum.
-/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace ExpandedFA.PartIV.HardyCompactTransferSpec
open ExpandedFA.Fourier HardyMaximalSpec HardyLowpassSpec

/-- The common support and coordinate C^N bounds for a family of tests. -/
def IsUniformTest {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (N : ℕ) (a B : ℝ)
    (ψ : Euclidean d → 𝕜) : Prop :=
  ContDiff ℝ ∞ ψ ∧ tsupport ψ ⊆ Metric.ball 0 a ∧
    ∀ (k : ℕ), k ≤ N → ∀ (v : Fin k → Fin d) (x : Euclidean d),
      ‖coordinatePartial v ψ x‖ ≤ B

/-- One constant for the entire unit test class and every positive scale. -/
def TransferEstimate {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (η : Schwartz 𝕜 d) (N : ℕ) (C : ℝ) : Prop :=
  ∀ (f : Euclidean d → 𝕜), Integrable f →
    ∀ x, peetre η f x < ⊤ → ∀ (ψ : Tests 𝕜 d N) (t : ℝ), 0 < t →
      ∀ z, ‖convolve (dilate t ψ.val) f z‖ ≤
        C * (peetre η f x).toReal * (1 + ‖x - z‖ / t) ^ peetreExponent d

/-- The principal compact-test assertion, for any lowpass having the
specified Fourier support and value one near zero. -/
def CompactTransfer : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] {d : ℕ}, 0 < d →
    ∀ (N : ℕ), AdmissibleOrder d N →
      ∀ (η : Schwartz 𝕜 d) (R : ℝ), IsLowpass η R →
        ∃ C : ℝ, 0 ≤ C ∧ TransferEstimate η N C

/-- Uniformity for every family with one support radius and one C^N bound.
Quantifying over all tests with those bounds includes arbitrary indexed
families, without any countability hypothesis on their index set. -/
def UniformTransfer : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] {d : ℕ}, 0 < d →
    ∀ (N : ℕ), AdmissibleOrder d N →
      ∀ (η : Schwartz 𝕜 d) (R : ℝ), IsLowpass η R →
        ∀ a B : ℝ, 0 < a → 0 ≤ B →
          ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Euclidean d → 𝕜), Integrable f →
            ∀ x, peetre η f x < ⊤ → ∀ (ψ : Euclidean d → 𝕜),
              IsUniformTest N a B ψ → ∀ t : ℝ, 0 < t → ∀ z,
                ‖convolve (dilate t ψ) f z‖ ≤
                  C * (peetre η f x).toReal *
                    (1 + ‖x - z‖ / t) ^ peetreExponent d

/-- The actual supremum estimate. Infinite Peetre values are retained; no
measurability or countable-test replacement is needed to take this supremum. -/
def GrandTransfer : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] {d : ℕ}, 0 < d →
    ∀ (N : ℕ), AdmissibleOrder d N →
      ∀ (η : Schwartz 𝕜 d) (R : ℝ), IsLowpass η R →
        ∃ C : ℝ, 0 < C ∧ ∀ (f : Euclidean d → 𝕜), Integrable f →
          ∀ x, grand N f x ≤ ENNReal.ofReal C * peetre η f x

/-- A proved supremum step can be reused independently of the analytic
construction of the uniform transfer constant. -/
def GrandFromEstimate : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] {d N : ℕ} (η : Schwartz 𝕜 d) (C : ℝ),
    0 < C → TransferEstimate η N C →
      ∀ (f : Euclidean d → 𝕜), Integrable f →
        ∀ x, grand N f x ≤ ENNReal.ofReal C * peetre η f x

def UniformFromCompact : Prop := CompactTransfer → UniformTransfer

def GrandFromCompact : Prop := CompactTransfer → GrandTransfer

/-- Literal dyadic physical-space dilations of the lowpass. -/
def dyadicLowpass {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (η : Schwartz 𝕜 d) (j : ℤ) : Euclidean d → 𝕜 :=
  dilate ((2 : ℝ) ^ (-j)) η

def dyadicDifference {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (η : Schwartz 𝕜 d) (j : ℤ) : Euclidean d → 𝕜 :=
  dyadicLowpass η j - dyadicLowpass η (j - 1)

/-- The precise weight needed to insert the Peetre bound at z-w. -/
def weightedIntegrand {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (u : Euclidean d → 𝕜) (j : ℤ) (x z w : Euclidean d) : ℝ :=
  ‖u w‖ * (1 + (2 : ℝ) ^ j * ‖x - (z - w)‖) ^ peetreExponent d

/-- The quantitative analytic estimate used by the dyadic proof.
There is no f or Peetre supremum in this assertion. The high-frequency
bound incorporates a summable geometric majorant, including the shifted
weight at the finer reproducing scale. -/
def WeightedKernelBounds : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] {d : ℕ}, 0 < d →
    ∀ (N : ℕ), AdmissibleOrder d N →
      ∀ (η : Schwartz 𝕜 d) (R : ℝ), IsLowpass η R →
        ∃ D : ℝ, 0 ≤ D ∧ ∀ (ψ : Tests 𝕜 d N) (t : ℝ), 0 < t →
          ∀ j : ℤ, (2 : ℝ) ^ (-j) ≤ t → t < 2 * (2 : ℝ) ^ (-j) →
            ∀ x z : Euclidean d,
              (Integrable (weightedIntegrand (dilate t ψ.val) j x z) ∧
                (∫ w, weightedIntegrand (dilate t ψ.val) j x z w) ≤
                  D * (1 + ‖x - z‖ / t) ^ peetreExponent d) ∧
              ∀ k : ℕ,
                Integrable (weightedIntegrand
                  (convolve (dilate t ψ.val) (dyadicDifference η (j + (k : ℤ) + 1)))
                  (j + (k : ℤ) + 2) x z) ∧
                (∫ w, weightedIntegrand
                  (convolve (dilate t ψ.val) (dyadicDifference η (j + (k : ℤ) + 1)))
                  (j + (k : ℤ) + 2) x z w) ≤
                  D * (1 + ‖x - z‖ / t) ^ peetreExponent d * (1 / 2 : ℝ) ^ k

/-- Reconstruction: convergence after convolution
with a bounded compact smooth test. Each partial sum is the original
lowpass telescoping sum with the finer lowpass inserted by Fourier support.
No estimate or convergence is postulated as part of the lowpass definition. -/
def Reconstruction : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] {d : ℕ}, 0 < d →
    ∀ (η : Schwartz 𝕜 d) (R : ℝ), IsLowpass η R →
      ∀ (N : ℕ) (ψ : Tests 𝕜 d N) (t : ℝ), 0 < t →
        ∀ (f : Euclidean d → 𝕜), Integrable f → ∀ (j : ℤ) (z : Euclidean d),
          Tendsto (fun m : ℕ =>
            convolve (dilate t ψ.val) (convolve (dyadicLowpass η j) f) z +
              ∑ k ∈ Finset.range m,
                convolve
                  (convolve (dilate t ψ.val) (dyadicDifference η (j + (k : ℤ) + 1)))
                  (convolve (dyadicLowpass η (j + (k : ℤ) + 2)) f) z)
            atTop (𝓝 (convolve (dilate t ψ.val) f z))

def CompactFromAnalyticInputs : Prop :=
  WeightedKernelBounds → Reconstruction → CompactTransfer

/-- Final assembly once the independent weighted kernel obligation is proved.
This conditional interface does not replace the unconditional principal Specs. -/
def TransferTheoremsFromWeightedBounds : Prop :=
  WeightedKernelBounds → CompactTransfer ∧ UniformTransfer ∧ GrandTransfer

end ExpandedFA.PartIV.HardyCompactTransferSpec
