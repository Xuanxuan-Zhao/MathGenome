import MathGenome.Internal.FourierSobolev.Specs.P102.U4.TestSpace
import MathGenome.Internal.FourierSobolev.Specs.P102.U3.SchwartzFourier

/-! Independent statements for paper.tex:1362–1367 (p102:U4-01).
The standard Euclidean model is shared with U3; pairings are scalar-linear.
The strong dual uses bounded convergence, and the weak dual uses pointwise testing.
All statements include dimension zero as well as the manuscript's positive dimensions.
-/
noncomputable section
open Set TopologicalSpace Filter
open scoped SchwartzMap ContDiff Topology

namespace P102.U4

abbrev WholeTests (d : ℕ) (𝕜 : Type) [RCLike 𝕜] :=
  TestSpace 𝕜 (⊤ : Opens (Space d))
abbrev SchwartzTests (d : ℕ) (𝕜 : Type) [RCLike 𝕜] := SchwartzMap (Space d) 𝕜

/-- The canonical inclusion preserves the ambient function exactly. -/
def testToSchwartz (d : ℕ) (𝕜 : Type) [RCLike 𝕜] :
    WholeTests d 𝕜 →ₗ[𝕜] SchwartzTests d 𝕜 where
  toFun f := f.hasCompactSupport.toSchwartzMap (f.contDiff.of_le (by simp))
  map_add' f g := by ext x; rfl
  map_smul' c f := by ext x; rfl

/-- Multiplication by χ(x/R). The pointwise formula and compact support for R ≠ 0
are included in the approximation obligation, not assumed in this definition. -/
def cutoffSchwartz {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (χ : WholeTests d 𝕜) (f : SchwartzTests d 𝕜) (R : ℝ) : SchwartzTests d 𝕜 :=
  SchwartzMap.smulLeftCLM 𝕜 (fun x => χ (R⁻¹ • x)) f

namespace RestrictionExpected

def Inclusion : Prop := ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜],
  Continuous (testToSchwartz d 𝕜) ∧ Function.Injective (testToSchwartz d 𝕜) ∧
    DenseRange (testToSchwartz d 𝕜)

def CutoffApproximation : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (χ : WholeTests d 𝕜),
    (∃ U : Opens (Space d), Metric.closedBall (0 : Space d) 1 ⊆ (U : Set (Space d)) ∧ ∀ x ∈ U, χ x = 1) →
    ∀ f : SchwartzTests d 𝕜,
      (∀ R x, cutoffSchwartz χ f R x = χ (R⁻¹ • x) * f x) ∧
      (∀ R : ℝ, R ≠ 0 → HasCompactSupport (cutoffSchwartz χ f R : Space d → 𝕜)) ∧
      Tendsto (cutoffSchwartz χ f) atTop (𝓝 f) ∧
      ∀ k n : ℕ, Tendsto
        (fun R : ℝ => SchwartzMap.seminorm 𝕜 k n (cutoffSchwartz χ f R - f))
        atTop (𝓝 0)

/-- The coordinate/radial seminorms from the manuscript also tend to zero. -/
def ManuscriptCutoffApproximation : Prop :=
  ∀ (d : ℕ) (χ : WholeTests d ℂ),
    (∃ U : Opens (Space d), Metric.closedBall (0 : Space d) 1 ⊆ (U : Set (Space d)) ∧ ∀ x ∈ U, χ x = 1) →
    ∀ (f : P102.Specs.U3.Test d) (N k : ℕ), Tendsto
      (fun R : ℝ => P102.U3.manuscriptSeminorm N k (cutoffSchwartz χ f R - f))
      atTop (𝓝 0)

/-- The transpose is continuous for both specified dual topologies, with exactly
its bilinear testing formula. Injectivity is asserted for both realizations. -/
def DualRestriction : Prop := ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜],
  (∃ r : (SchwartzTests d 𝕜 →L[𝕜] 𝕜) →L[𝕜] (WholeTests d 𝕜 →L[𝕜] 𝕜),
    (∀ T f, r T f = T (testToSchwartz d 𝕜 f)) ∧ Function.Injective r) ∧
  (∃ r : (SchwartzTests d 𝕜 →Lₚₜ[𝕜] 𝕜) →L[𝕜]
      (WholeTests d 𝕜 →Lₚₜ[𝕜] 𝕜),
    (∀ T f, r T f = T (testToSchwartz d 𝕜 f)) ∧ Function.Injective r)

/-- Compatibility with ordinary distributions on real tests with complex values.
The two real-linear transpose maps remain injective and continuous for each dual
topology; the complex-test restriction is reconstructed from real and imaginary parts. -/
def RealTestBridge : Prop := ∀ d : ℕ,
  (∃ r : (SchwartzTests d ℂ →L[ℂ] ℂ) →L[ℝ] (WholeTests d ℝ →L[ℝ] ℂ),
    (∀ T f, r T f = T (testToSchwartz d ℂ (complexifyTest ⊤ f))) ∧
    Function.Injective r ∧
    ∀ T f, T (testToSchwartz d ℂ f) =
      r T (realPart ⊤ f) + Complex.I * r T (imagPart ⊤ f)) ∧
  (∃ r : (SchwartzTests d ℂ →Lₚₜ[ℂ] ℂ) →L[ℝ]
      (WholeTests d ℝ →Lₚₜ[ℝ] ℂ),
    (∀ T f, r T f = T (testToSchwartz d ℂ (complexifyTest ⊤ f))) ∧
    Function.Injective r ∧
    ∀ T f, T (testToSchwartz d ℂ f) =
      r T (realPart ⊤ f) + Complex.I * r T (imagPart ⊤ f))

end RestrictionExpected
end P102.U4
