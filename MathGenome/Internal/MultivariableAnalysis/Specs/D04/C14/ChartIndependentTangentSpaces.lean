import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary
import Mathlib.Analysis.Calculus.Deriv.Comp

/-! Tangent spaces in the shared embedded Euclidean chart model.
The full derivative at a half-space point is the unique derivative within its
relatively open source. Curve velocities are germs of C¹ curves, with the
one-sided convention given by C¹ regularity within [0,ε). -/
noncomputable section
open Set
open scoped ContDiff
namespace Specs.D04.C14.ChartIndependentTangentSpaces
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.Model
namespace Model

def chartDifferential {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (c : EmbeddedChart r k n M) (u : E k) : E k →L[ℝ] E n :=
  fderivWithin ℝ c.toFun c.source u

/-- The supremum avoids choosing a chart. The chart formula below proves that
all summands at a manifold point are the same k-dimensional subspace. -/
def tangentSpace (r : ℕ∞ω) (k : ℕ) {n : ℕ} (M : Set (E n)) (x : E n) :
    Submodule ℝ (E n) :=
  ⨆ (c : EmbeddedChart r k n M) (u : E k) (_ : u ∈ c.source)
    (_ : c.toFun u = x), LinearMap.range (chartDifferential c u).toLinearMap

def twoSidedVelocities {n : ℕ} (M : Set (E n)) (x : E n) : Set (E n) :=
  {v | ∃ (γ : ℝ → E n) (ε : ℝ), 0 < ε ∧ γ 0 = x ∧
    ContDiffOn ℝ 1 γ (Ioo (-ε) ε) ∧ MapsTo γ (Ioo (-ε) ε) M ∧
    HasDerivAt γ v 0}

def oneSidedVelocities {n : ℕ} (M : Set (E n)) (x : E n) : Set (E n) :=
  {v | ∃ (γ : ℝ → E n) (ε : ℝ), 0 < ε ∧ γ 0 = x ∧
    ContDiffOn ℝ 1 γ (Ico 0 ε) ∧ MapsTo γ (Ico 0 ε) M ∧
    HasDerivWithinAt γ v (Ici 0) 0}
end Model
open Model

abbrev chartDifferentialType := {r : ℕ∞ω} → {k n : ℕ} → {M : Set (E n)} →
  EmbeddedChart r k n M → E k → (E k →L[ℝ] E n)
def chartDifferentialValue : chartDifferentialType := @Model.chartDifferential
abbrev tangentSpaceType := ℕ∞ω → ℕ → {n : ℕ} → Set (E n) → E n → Submodule ℝ (E n)
def tangentSpaceValue : tangentSpaceType := @Model.tangentSpace
abbrev velocitiesType := {n : ℕ} → Set (E n) → E n → Set (E n)
def twoSidedVelocitiesValue : velocitiesType := @Model.twoSidedVelocities
def oneSidedVelocitiesValue : velocitiesType := @Model.oneSidedVelocities

/-- In particular the result is independent of the Euclidean extension used
in a boundary chart. -/
def chartDifferential_extensionType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)} (c : EmbeddedChart r k n M),
  ManifoldRegularity r → ∀ u ∈ c.source, ∀ (W : Set (E k)) (g : E k → E n),
    IsOpen W → u ∈ W → EqOn g c.toFun (c.source ∩ W) →
    DifferentiableAt ℝ g u → chartDifferential c u = fderiv ℝ g u

def tangentSpace_chartType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)} (c : EmbeddedChart r k n M),
    ManifoldRegularity r → k ≤ n → ∀ u ∈ c.source,
      tangentSpace r k M (c.toFun u) = LinearMap.range (chartDifferential c u).toLinearMap

def chart_independenceType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)} (c d : EmbeddedChart r k n M),
    ManifoldRegularity r → k ≤ n → ∀ u ∈ c.source, ∀ v ∈ d.source,
      c.toFun u = d.toFun v →
      LinearMap.range (chartDifferential c u).toLinearMap =
        LinearMap.range (chartDifferential d v).toLinearMap

def tangentSpace_finrankType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}, IsEmbeddedManifold r k M →
    ∀ x ∈ M, Module.finrank ℝ (tangentSpace r k M x) = k

def tangentSpace_interior_velocitiesType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}, IsEmbeddedManifold r k M →
    ∀ x ∈ M, x ∉ intrinsicBoundary r k M →
      (tangentSpace r k M x : Set (E n)) = twoSidedVelocities M x

def tangentSpace_boundary_velocitiesType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}, IsEmbeddedManifold r k M →
    ∀ x ∈ intrinsicBoundary r k M,
      tangentSpace r k M x = Submodule.span ℝ (oneSidedVelocities M x)

def tangentSpace_regular_levelType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} (O : Set (E n)) (g : E n → E (n-k)),
    ManifoldRegularity r → k ≤ n → IsOpen O → ContDiffOn ℝ r g O →
    (∀ x ∈ O, g x = 0 → Function.Surjective (fderiv ℝ g x)) →
    ∀ x ∈ O ∩ g ⁻¹' {0},
      tangentSpace r k (O ∩ g ⁻¹' {0}) x = (fderiv ℝ g x).ker

def tangentSpace_intrinsic_boundaryType : Prop :=
  ∀ {r : ℕ∞ω} {d n : ℕ} {M : Set (E n)} (c : EmbeddedChart r (d+1) n M),
    ManifoldRegularity r → d+1 ≤ n → c.half = true →
    ∀ u ∈ c.source, u ∈ flatBoundary (d+1) →
      (tangentSpace r d (intrinsicBoundary r (d+1) M) (c.toFun u) : Set (E n)) =
        chartDifferential c u '' flatBoundary (d+1)

def tangentSpace_zeroType : Prop :=
  ∀ {r : ℕ∞ω} {n : ℕ} {M : Set (E n)}, IsEmbeddedManifold r 0 M →
    ∀ x ∈ M, tangentSpace r 0 M x = ⊥

/-- The kernel formula also holds for a local defining equation of an
existing manifold. Only surjectivity at the marked point is needed. -/
def tangentSpace_local_regular_levelType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}, IsEmbeddedManifold r k M →
    ∀ (O : Set (E n)) (g : E n → E (n-k)), IsOpen O → ContDiffOn ℝ r g O →
      M ∩ O = O ∩ g ⁻¹' {0} → ∀ x ∈ M ∩ O,
        Function.Surjective (fderiv ℝ g x) →
          tangentSpace r k M x = (fderiv ℝ g x).ker

end Specs.D04.C14.ChartIndependentTangentSpaces
