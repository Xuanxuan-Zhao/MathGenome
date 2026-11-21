import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.Spaces
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Order.LocalExtr

noncomputable section
open MeasureTheory TopologicalSpace Set
open scoped InnerProductSpace

namespace VariationalNotes.Classical.GraphArea
open VariationalNotes.Sobolev

/-- The finite exponent 1, for the scalar Sobolev space in the proposition. -/
def one : Exponent := ⟨1, le_rfl⟩
abbrev W11 {d : ℕ} (Ω : Opens (Domain d)) := W1p Ω 1 one

def density {d : ℕ} (z : Gradient 1 d) : ℝ := Real.sqrt (1 + ‖z‖ ^ 2)
def densityVariation {d : ℕ} (z w : Gradient 1 d) : ℝ :=
  frobenius z w / density z

/-- Real graph area. Integrability, proved below for every W11 function on a
bounded domain, ensures that this is the finite Lebesgue integral. -/
def area {d : ℕ} (Ω : Opens (Domain d)) (u : W11 Ω) : ℝ :=
  ∫ x, density (gradient Ω 1 one u x) ∂domainMeasure Ω

def firstVariation {d : ℕ} (Ω : Opens (Domain d)) (u v : W11 Ω) : ℝ :=
  ∫ x, densityVariation (gradient Ω 1 one u x) (gradient Ω 1 one v x)
    ∂domainMeasure Ω

/-- Standard scalar embedding into the one-dimensional Euclidean target. -/
def scalarTest {d : ℕ} (Ω : Opens (Domain d)) (φ : P102.U4.TestSpace ℝ Ω) :
    VectorTest Ω 1 :=
  TestFunction.postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ
    (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))) φ

/-- The classical gradient of a scalar test, with the same flattened matrix
indices as the weak gradient. `partialWord [j]` is its ordinary j-th derivative. -/
def testGradient {d : ℕ} (Ω : Opens (Domain d)) (φ : P102.U4.TestSpace ℝ Ω)
    (x : Domain d) : Gradient 1 d :=
  WithLp.toLp 2 (fun ij => P102.U4.partialWord (φ : Domain d → ℝ) [ij.2] x)

def scalarVariation {d : ℕ} (Ω : Opens (Domain d)) (u : W11 Ω)
    (φ : P102.U4.TestSpace ℝ Ω) : ℝ :=
  ∫ x, densityVariation (gradient Ω 1 one u x) (testGradient Ω φ x) ∂domainMeasure Ω

/-- Every smooth compactly supported test is represented by its Sobolev class.
Using its value class avoids any extra choice of representatives or derivatives. -/
def RepresentsTest {d : ℕ} (Ω : Opens (Domain d))
    (φ : P102.U4.TestSpace ℝ Ω) (v : W11 Ω) : Prop :=
  value Ω 1 one v = testToValueLp Ω 1 one (scalarTest Ω φ)

/-- A local minimum along each smooth test, with a full real neighborhood of
zero; thus both signs of the variation parameter are allowed. -/
def TestLocalMinimum {d : ℕ} (Ω : Opens (Domain d)) (u : W11 Ω) : Prop :=
  ∀ (φ : P102.U4.TestSpace ℝ Ω) (v : W11 Ω), RepresentsTest Ω φ v →
    IsLocalMin (fun t : ℝ => area Ω (u + t • v)) 0

/-- The weak minimal-surface equation, tested against every C_c^∞ function. -/
def WeakMinimalSurface {d : ℕ} (Ω : Opens (Domain d)) (u : W11 Ω) : Prop :=
  ∀ φ : P102.U4.TestSpace ℝ Ω, scalarVariation Ω u φ = 0

namespace Expected

def AreaFinite : Prop :=
  ∀ {d : ℕ} (Ω : Opens (Domain d)), Bornology.IsBounded (Ω : Set (Domain d)) →
    ∀ u : W11 Ω, Integrable (fun x => density (gradient Ω 1 one u x)) (domainMeasure Ω)

def VariationFormula : Prop :=
  ∀ {d : ℕ} (Ω : Opens (Domain d)), Bornology.IsBounded (Ω : Set (Domain d)) →
    ∀ u v : W11 Ω,
      Integrable (fun x => densityVariation (gradient Ω 1 one u x)
        (gradient Ω 1 one v x)) (domainMeasure Ω) ∧
      HasDerivAt (fun t : ℝ => area Ω (u + t • v)) (firstVariation Ω u v) 0

def SmoothTests : Prop :=
  ∀ {d : ℕ} (Ω : Opens (Domain d)), Bornology.IsBounded (Ω : Set (Domain d)) →
    ∀ (u : W11 Ω) (φ : P102.U4.TestSpace ℝ Ω),
      ∃ v : W11 Ω, RepresentsTest Ω φ v ∧
        (gradient Ω 1 one v : Domain d → Gradient 1 d) =ᵐ[domainMeasure Ω] testGradient Ω φ ∧
        Integrable (fun x => densityVariation (gradient Ω 1 one u x)
          (testGradient Ω φ x)) (domainMeasure Ω) ∧
        HasDerivAt (fun t : ℝ => area Ω (u + t • v)) (scalarVariation Ω u φ) 0

def Stationarity : Prop :=
  ∀ {d : ℕ} (Ω : Opens (Domain d)), Bornology.IsBounded (Ω : Set (Domain d)) →
    ∀ u : W11 Ω, TestLocalMinimum Ω u → WeakMinimalSurface Ω u

end Expected
end VariationalNotes.Classical.GraphArea
