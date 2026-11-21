import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachAlgebra.Conventions
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Analytic.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
Independent interface for paper.tex:10090–10109,10126–10128.
A finite cycle is a finite collection of C¹ arcs, with a permutation matching
endpoints. The permutation decomposes into closed, piecewise C¹ curves. Arcs
are parametrized by [0,1]; their actual within-derivative is used, including
at endpoints. No Cauchy theorem or existence certificate is built into a cycle.
The winding number is the normalized scalar contour integral. Positive
orientation means winding zero or one off the trace. Admissibility
requires winding one on an open neighborhood of the compact set and zero
off the stated open holomorphy domain. Domains and spectra may be disconnected.
-/

noncomputable section

namespace ExpandedFA.BanachAlgebra.ContourCalculus

open Set MeasureTheory Filter
open scoped Topology

universe u

/-- One C¹ arc on the closed parameter interval. -/
structure C1Arc where
  path : ℝ → ℂ
  smooth : ContDiffOn ℝ 1 path (Icc 0 1)

/-- Finite closed contour chains, including multiple components and the empty cycle. -/
structure Cycle where
  count : ℕ
  arc : Fin count → C1Arc
  next : Equiv.Perm (Fin count)
  joins : ∀ i, (arc i).path 1 = (arc (next i)).path 0

def C1Arc.velocity (γ : C1Arc) : ℝ → ℂ := derivWithin γ.path (Icc 0 1)

def Cycle.trace (Γ : Cycle) : Set ℂ := ⋃ i, (Γ.arc i).path '' Icc 0 1

def Cycle.length (Γ : Cycle) : ℝ :=
  ∑ i, ∫ t in (0 : ℝ)..1, ‖(Γ.arc i).velocity t‖

/-- The ordinary Banach-valued contour integral, a finite sum of Bochner integrals. -/
def cycleIntegral {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (Γ : Cycle) (h : ℂ → X) : X :=
  ∑ i, ∫ t in (0 : ℝ)..1, (Γ.arc i).velocity t • h ((Γ.arc i).path t)

/-- Complex-valued index, with its usual meaning off the trace. -/
def Cycle.winding (Γ : Cycle) (z : ℂ) : ℂ :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ * cycleIntegral Γ (fun w => (w - z)⁻¹)

def Cycle.Positive (Γ : Cycle) : Prop :=
  ∀ z ∉ Γ.trace, Γ.winding z = 0 ∨ Γ.winding z = 1

def Cycle.Admissible (Γ : Cycle) (K U : Set ℂ) : Prop :=
  Γ.trace ⊆ U \ K ∧ Γ.Positive ∧
  (∃ V : Set ℂ, IsOpen V ∧ K ⊆ V ∧ Disjoint V Γ.trace ∧
    ∀ z ∈ V, Γ.winding z = 1) ∧
  ∀ z ∉ U, Γ.winding z = 0

/-- The empty closed chain is useful for an empty compact set and total definitions. -/
def Cycle.empty : Cycle where
  count := 0
  arc := Fin.elim0
  next := Equiv.refl _
  joins i := Fin.elim0 i

instance : Inhabited Cycle := ⟨Cycle.empty⟩

namespace Spec

open Specs.ExpandedFA.BanachAlgebra.Conventions

def ContourValueType :=
  ∀ (A : Type u) [NormedRing A] [NormedAlgebra ℂ A], Cycle → A → (ℂ → ℂ) → A

def ContourValueValue : ContourValueType.{u} := fun A _ _ Γ a f =>
  (2 * Real.pi * Complex.I : ℂ)⁻¹ •
    cycleIntegral Γ (fun z => f z • AlgebraResolventValue ℂ A a z)

/-- No existence premise is placed on the output of the construction. -/
def AdmissibleCyclesExist : Prop :=
  ∀ (K U : Set ℂ), IsCompact K → IsOpen U → K ⊆ U →
    ∃ Γ : Cycle, Γ.Admissible K U

/-- Scalar homological Cauchy theorem in its equivalent equal-index formulation.
No simply connected domain hypothesis, contour positivity, or holomorphic
primitive is assumed. -/
def HomologicalCauchy : Prop :=
  ∀ (U : Set ℂ) (Γ Δ : Cycle) (h : ℂ → ℂ), IsOpen U →
    Γ.trace ⊆ U → Δ.trace ⊆ U →
    (∀ z ∉ U, Γ.winding z = Δ.winding z) →
    DifferentiableOn ℂ h U → cycleIntegral Γ h = cycleIntegral Δ h

/-- A total choice, justified as an admissible contour only by the existence theorem. -/
def SelectedCycleType := Set ℂ → Set ℂ → Cycle

def SelectedCycleValue : SelectedCycleType :=
  fun K U => Classical.epsilon (fun Γ : Cycle => Γ.Admissible K U)

def HolomorphicValueType :=
  ∀ (A : Type u) [NormedRing A] [NormedAlgebra ℂ A], A → Set ℂ → (ℂ → ℂ) → A

def HolomorphicValueValue : HolomorphicValueType.{u} := fun A _ _ a U f =>
  ContourValueValue A (SelectedCycleValue (AlgebraSpectrumValue ℂ A a) U) a f

/-- In particular the selected contour exists in every original allowed case. -/
def SelectedCycleAdmissible : Prop :=
  ∀ (A : Type u) [NormedRing A] [NormedAlgebra ℂ A], IsUnitalBanachAlgebraValue A →
    ∀ (a : A) (U : Set ℂ), IsOpen U → AlgebraSpectrumValue ℂ A a ⊆ U →
      (SelectedCycleValue (AlgebraSpectrumValue ℂ A a) U).Admissible
        (AlgebraSpectrumValue ℂ A a) U

/-- The chosen value has the stated formula for every admissible contour. -/
def HolomorphicFormula : Prop :=
  ∀ (A : Type u) [NormedRing A] [NormedAlgebra ℂ A], IsUnitalBanachAlgebraValue A →
    ∀ (a : A) (U : Set ℂ) (f : ℂ → ℂ), IsOpen U → AlgebraSpectrumValue ℂ A a ⊆ U →
      DifferentiableOn ℂ f U → ∀ Γ : Cycle,
        Γ.Admissible (AlgebraSpectrumValue ℂ A a) U →
        HolomorphicValueValue A a U f = ContourValueValue A Γ a f

/-- Full independence for arbitrary admissible cycles on a fixed neighborhood. -/
def CycleIndependence : Prop :=
  ∀ (A : Type u) [NormedRing A] [NormedAlgebra ℂ A], IsUnitalBanachAlgebraValue A →
    ∀ (a : A) (U : Set ℂ) (f : ℂ → ℂ), IsOpen U → AlgebraSpectrumValue ℂ A a ⊆ U →
      DifferentiableOn ℂ f U → ∀ Γ Δ : Cycle,
        Γ.Admissible (AlgebraSpectrumValue ℂ A a) U →
        Δ.Admissible (AlgebraSpectrumValue ℂ A a) U →
        ContourValueValue A Γ a f = ContourValueValue A Δ a f

/-- Both neighborhood independence and invariance under a change of representative germ. -/
def NeighborhoodIndependence : Prop :=
  ∀ (A : Type u) [NormedRing A] [NormedAlgebra ℂ A], IsUnitalBanachAlgebraValue A →
    ∀ (a : A) (U V W : Set ℂ) (f g : ℂ → ℂ),
      IsOpen U → IsOpen V → IsOpen W →
      AlgebraSpectrumValue ℂ A a ⊆ W → W ⊆ U ∩ V →
      DifferentiableOn ℂ f U → DifferentiableOn ℂ g V → EqOn f g W →
      ∀ Γ Δ : Cycle, Γ.Admissible (AlgebraSpectrumValue ℂ A a) U →
        Δ.Admissible (AlgebraSpectrumValue ℂ A a) V →
        ContourValueValue A Γ a f = ContourValueValue A Δ a g

/-- The length/resolvent estimate used for continuity on a fixed contour. -/
def ContourNormEstimate : Prop :=
  ∀ (A : Type u) [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    (Γ : Cycle) (a : A) (f g : ℂ → ℂ) (M ε : ℝ),
    Γ.trace ⊆ AlgebraResolventSetValue ℂ A a →
    ContinuousOn f Γ.trace → ContinuousOn g Γ.trace →
    0 ≤ M → 0 ≤ ε →
    (∀ z ∈ Γ.trace, ‖AlgebraResolventValue ℂ A a z‖ ≤ M) →
    (∀ z ∈ Γ.trace, ‖f z - g z‖ ≤ ε) →
    ‖ContourValueValue A Γ a f - ContourValueValue A Γ a g‖ ≤
      ‖(2 * Real.pi * Complex.I : ℂ)⁻¹‖ * Γ.length * M * ε

/-- Holomorphy of the approximants is not needed for this analytic estimate. -/
def FixedContourConvergence : Prop :=
  ∀ (A : Type u) [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    (Γ : Cycle) (a : A) (f : ℂ → ℂ) (F : ℕ → ℂ → ℂ),
    Γ.trace ⊆ AlgebraResolventSetValue ℂ A a →
    ContinuousOn f Γ.trace → (∀ n, ContinuousOn (F n) Γ.trace) →
    TendstoUniformlyOn F f atTop Γ.trace →
    Tendsto (fun n => ContourValueValue A Γ a (F n)) atTop
      (𝓝 (ContourValueValue A Γ a f))

end Spec
end ExpandedFA.BanachAlgebra.ContourCalculus
