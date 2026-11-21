import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.ScalarRieszMarkov
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.VectorMeasure.WithDensity
import Mathlib.MeasureTheory.Function.L1Space.AEEqFun

/-! Independent statements for the smooth part of `fa2:p4:measure-approximation`,
paper.tex:19879–19920, with the adopted dimensional erratum. The functions are
genuine ambient smooth functions with compact support contained in the open
set. The measure on a subtype is unnormalized restricted Lebesgue measure.
No assertion about adding an arbitrary point mass is assumed or required. -/

noncomputable section

namespace ExpandedFA.PartIV.MeasureSmoothApproximationSpec

open Set MeasureTheory Filter
open scoped Topology ZeroAtInfty
open ExpandedFA.FunctionSpaces.ScalarRieszMarkovSpec
open ExpandedFA.FunctionSpaces.PositiveRadonRepresentationSpec

attribute [local instance] MeasureTheory.Measure.Subtype.measureSpace

abbrev Euclidean (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Ambient realization of `C_c^∞(Ω,𝕜)`, using real differentiability for
both real and complex scalars. -/
structure SmoothDensity {d : ℕ} (Ω : Set (Euclidean d)) (𝕜 : Type*) [RCLike 𝕜] where
  toFun : Euclidean d → 𝕜
  smooth : ContDiff ℝ (⊤ : ℕ∞) toFun
  compact : HasCompactSupport toFun
  support_subset : tsupport toFun ⊆ Ω

instance {d : ℕ} {Ω : Set (Euclidean d)} {𝕜 : Type*} [RCLike 𝕜] :
    CoeFun (SmoothDensity Ω 𝕜) (fun _ => Euclidean d → 𝕜) := ⟨SmoothDensity.toFun⟩

/-- The actual inclusion of the open set into its closure. -/
def intoClosure {d : ℕ} (Ω : Set (Euclidean d)) : Ω → closure Ω :=
  fun x => ⟨x, subset_closure x.property⟩

/-- The scalar measure `u dx` on the open set. The approximation statements
include integrability, so the library's nonintegrable default is never used. -/
def openDensity {d : ℕ} (Ω : Set (Euclidean d)) {𝕜 : Type*} [RCLike 𝕜]
    (u : Ω → 𝕜) : VectorMeasure Ω 𝕜 :=
  (volume : Measure Ω).withDensityᵥ u

/-- Extension of `u dx` by zero to the closure, via pushforward under the
inclusion. This includes empty sets without choosing a default point. -/
def closureDensity {d : ℕ} (Ω : Set (Euclidean d)) {𝕜 : Type*} [RCLike 𝕜]
    (u : Ω → 𝕜) : VectorMeasure (closure Ω) 𝕜 :=
  (openDensity Ω u).map (intoClosure Ω)

/-- Exact-norm smooth approximation against every continuous test on the
closure. No positivity, nonzero, nonempty, or positive-dimension assumption. -/
def ClosureApproximation : Prop :=
  ∀ (d : ℕ) (Ω : Set (Euclidean d)), IsOpen Ω → Bornology.IsBounded Ω →
    ∀ (𝕜 : Type) [RCLike 𝕜] (μ : VectorMeasure (closure Ω) 𝕜),
      FiniteScalarRadon μ →
      ∃ u : ℕ → SmoothDensity Ω 𝕜,
        (∀ n, Integrable (fun x : Ω => u n x) ∧
          FiniteScalarRadon (closureDensity Ω (fun x => u n x)) ∧
          (∫ x : Ω, ‖u n x‖) = μ.variation.real univ) ∧
        ∀ f : C(closure Ω, 𝕜),
          Tendsto (fun n => scalarIntegral (closureDensity Ω (fun x => u n x)) f)
            atTop (𝓝 (scalarIntegral μ f))

/-- Positivity is native positivity of the original measure and pointwise
nonnegativity of the smooth densities; all scalar continuous tests are covered. -/
def PositiveClosureApproximation : Prop :=
  ∀ (d : ℕ) (Ω : Set (Euclidean d)), IsOpen Ω → Bornology.IsBounded Ω →
    ∀ (μ : Measure (closure Ω)), IsFiniteMeasure μ → PositiveRadon μ →
      ∃ u : ℕ → SmoothDensity Ω ℝ,
        (∀ n, Integrable (fun x : Ω => u n x) ∧
          (∀ x, 0 ≤ u n x) ∧ (∫ x : Ω, ‖u n x‖) = μ.real univ) ∧
        ∀ (𝕜 : Type) [RCLike 𝕜] (f : C(closure Ω, 𝕜)),
          Tendsto (fun n => ∫ x : Ω, (u n x : 𝕜) * f (intoClosure Ω x))
            atTop (𝓝 (∫ x, f x ∂μ))

/-- The corresponding assertion for the actual finite scalar Radon measures
on the open set, using every test vanishing at infinity. -/
def OpenApproximation : Prop :=
  ∀ (d : ℕ) (Ω : Set (Euclidean d)), IsOpen Ω → Bornology.IsBounded Ω →
    ∀ (𝕜 : Type) [RCLike 𝕜] (μ : VectorMeasure Ω 𝕜), FiniteScalarRadon μ →
      ∃ u : ℕ → SmoothDensity Ω 𝕜,
        (∀ n, Integrable (fun x : Ω => u n x) ∧
          FiniteScalarRadon (openDensity Ω (fun x => u n x)) ∧
          (∫ x : Ω, ‖u n x‖) = μ.variation.real univ) ∧
        ∀ f : C₀(Ω, 𝕜),
          Tendsto (fun n => scalarIntegral (openDensity Ω (fun x => u n x)) f)
            atTop (𝓝 (scalarIntegral μ f))

def PositiveOpenApproximation : Prop :=
  ∀ (d : ℕ) (Ω : Set (Euclidean d)), IsOpen Ω → Bornology.IsBounded Ω →
    ∀ (μ : Measure Ω), IsFiniteMeasure μ → PositiveRadon μ →
      ∃ u : ℕ → SmoothDensity Ω ℝ,
        (∀ n, Integrable (fun x : Ω => u n x) ∧
          (∀ x, 0 ≤ u n x) ∧ (∫ x : Ω, ‖u n x‖) = μ.real univ) ∧
        ∀ (𝕜 : Type) [RCLike 𝕜] (f : C₀(Ω, 𝕜)),
          Tendsto (fun n => ∫ x : Ω, (u n x : 𝕜) * f x)
            atTop (𝓝 (∫ x, f x ∂μ))

/-- A scalar-linear injective map from the genuine a.e.-quotient `L¹(Ω)` to
the genuine scalar Radon measures on the closure. The variation equality is
the isometry assertion, without installing a new norm on vector measures. -/
def L1Embedding : Prop :=
  ∀ (d : ℕ) (Ω : Set (Euclidean d)), IsOpen Ω → Bornology.IsBounded Ω →
    ∀ (𝕜 : Type) [RCLike 𝕜],
      ∃ T : Lp 𝕜 1 (volume : Measure Ω) →ₗ[𝕜] VectorMeasure (closure Ω) 𝕜,
        (∀ u, T u = closureDensity Ω u) ∧
        (∀ u, FiniteScalarRadon (T u) ∧ (T u).variation.real univ = ‖u‖) ∧
        Function.Injective T

/-- The same approximation stated directly for bounded scalar-linear
functionals, with the operator norm as the exact `L¹` norm. -/
def OpenDualApproximation (𝕜 : Type) [RCLike 𝕜] : Prop :=
  ∀ (d : ℕ) (Ω : Set (Euclidean d)), IsOpen Ω → Bornology.IsBounded Ω →
    ∀ L : C₀(Ω, 𝕜) →L[𝕜] 𝕜,
      ∃ u : ℕ → SmoothDensity Ω 𝕜,
        (∀ n, Integrable (fun x : Ω => u n x) ∧ (∫ x : Ω, ‖u n x‖) = ‖L‖) ∧
        ∀ f : C₀(Ω, 𝕜),
          Tendsto (fun n => ∫ x : Ω, f x * u n x) atTop (𝓝 (L f))

def RealOpenDualApproximation : Prop := OpenDualApproximation ℝ

def ComplexOpenDualApproximation : Prop := OpenDualApproximation ℂ

end ExpandedFA.PartIV.MeasureSmoothApproximationSpec
