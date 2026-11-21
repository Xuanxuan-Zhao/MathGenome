import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch11.Orbits
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch21.DomainInterior
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C12.GreenCirculationAndFlux

/-! Independent specification for paper.tex, d13:13:dulac.
The real Euclidean plane is the shared plane ℂ. The field and its canonical
maximal trajectories are the Chapter 11 objects, including actual domains.
The scalar B is arbitrary C¹ on D and is not required to be nonzero. -/
noncomputable section
open Set

namespace Specs.D13Unified.Ch13.Dulac
open _root_.D13Unified _root_.D13Unified.Ch06.StateDerivative
open _root_.D13Unified.Ch11.Orbits
open Ch01.AutonomousParameters Ch21.Collar Ch21.SmoothJordan Ch21.DomainInterior

def planeCoordinatesType := ℂ ≃L[ℝ] EuclideanSpace ℝ (Fin 2)
def planeCoordinatesValue : planeCoordinatesType :=
  Complex.orthonormalBasisOneI.repr.toContinuousLinearEquiv

def divergenceType := (ℂ → ℂ) → ℂ → ℝ
def divergenceValue : divergenceType := fun g z =>
  (fderiv ℝ g z 1).re + (fderiv ℝ g z Complex.I).im

/-- A least-period parametrization descends to an actual regular embedded
unit-circle loop; its timing, tangent, and full orbit trace are retained. -/
def PeriodicOrbitLoop : Prop :=
  ∀ (F : AutonomousODE ℂ), ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain →
    ∀ x ∈ F.domain, ¬ IsConstant F x → HasLeastPeriod F x →
    ∃ (T : ℝ) (γ : Circle → ℂ), 0 < T ∧ RegularEmbeddedLoop γ ∧
      range γ = orbit F x ∧
      (∀ t : ℝ, realLift γ t = flow F (T * t) x) ∧
      (∀ t : ℝ, HasDerivAt (realLift γ)
        (T • autonomousEvalValue F (realLift γ t)) t)

/-- The bounded Jordan component is nonempty and regular, and its entire
compact closure lies in the original simply connected domain. -/
def PeriodicOrbitInterior : Prop :=
  ∀ (F : AutonomousODE ℂ), ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain →
    ∀ (D : Set ℂ), IsOpen D → SourceSimplyConnected D →
    ∀ x ∈ F.domain, ¬ IsConstant F x → HasLeastPeriod F x → orbit F x ⊆ D →
    ∃ (T : ℝ) (γ : Circle → ℂ) (V : Set ℂ),
      0 < T ∧ RegularEmbeddedLoop γ ∧ range γ = orbit F x ∧
      (∀ t : ℝ, realLift γ t = flow F (T * t) x) ∧
      (∀ t : ℝ, HasDerivAt (realLift γ)
        (T • autonomousEvalValue F (realLift γ t)) t) ∧
      V.Nonempty ∧ IsOpen V ∧ Bornology.IsBounded V ∧
      HasC1Boundary V ∧ frontier V = range γ ∧
      closure V = V ∪ range γ ∧ IsCompact (closure V) ∧ closure V ⊆ D

/-- Full Bendixson--Dulac conclusion, with strict sign on all of D. -/
def BendixsonDulac : Prop :=
  ∀ (F : AutonomousODE ℂ), ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain →
    ∀ (D : Set ℂ), IsOpen D → SourceSimplyConnected D → D ⊆ F.domain →
    ∀ (B : ℂ → ℝ), ContDiffOn ℝ 1 B D →
      ((∀ z ∈ D, 0 < divergenceValue (fun w => B w • autonomousEvalValue F w) z) ∨
       (∀ z ∈ D, divergenceValue (fun w => B w • autonomousEvalValue F w) z < 0)) →
      ∀ x ∈ F.domain, orbit F x ⊆ D → ¬ IsConstant F x → ¬ HasLeastPeriod F x

/-- Direct exclusion of any self-return at two distinct times in the actual
maximal interval; no least-period hypothesis is required in this corollary. -/
def DulacOrbitInjective : Prop :=
  ∀ (F : AutonomousODE ℂ), ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain →
    ∀ (D : Set ℂ), IsOpen D → SourceSimplyConnected D → D ⊆ F.domain →
    ∀ (B : ℂ → ℝ), ContDiffOn ℝ 1 B D →
      ((∀ z ∈ D, 0 < divergenceValue (fun w => B w • autonomousEvalValue F w) z) ∨
       (∀ z ∈ D, divergenceValue (fun w => B w • autonomousEvalValue F w) z < 0)) →
      ∀ x ∈ F.domain, orbit F x ⊆ D → ¬ IsConstant F x →
        InjOn (fun t => flow F t x) (flowInterval F x).carrier

/-- Bendixson's specialization B=1, under exactly the same domain conditions. -/
def Bendixson : Prop :=
  ∀ (F : AutonomousODE ℂ), ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain →
    ∀ (D : Set ℂ), IsOpen D → SourceSimplyConnected D → D ⊆ F.domain →
      ((∀ z ∈ D, 0 < divergenceValue (autonomousEvalValue F) z) ∨
       (∀ z ∈ D, divergenceValue (autonomousEvalValue F) z < 0)) →
      ∀ x ∈ F.domain, orbit F x ⊆ D → ¬ IsConstant F x → ¬ HasLeastPeriod F x

/-- Analytic Green flux obstruction, independent of the dynamical and Jordan
representations. The normal is the actual defining-function outward normal. -/
def RegularDomainFluxContradiction : Prop :=
  let E := Specs.D04.C01.EuclideanInterfaces.Model.E 2
  ∀ (V : Set E)
    (hV : Specs.D04.C12.ClassicalRegularDomains.Model.IsClassicalRegularDomain V),
    V.Nonempty → ∀ (U : Set E) (P Q : E → ℝ), IsOpen U → closure V ⊆ U →
    Specs.D04.C02.DerivativeInterfaces.Model.CrOn 1 U P →
    Specs.D04.C02.DerivativeInterfaces.Model.CrOn 1 U Q →
    (∀ p : frontier V,
      P p * Specs.D04.C12.ClassicalRegularDomains.Model.outwardNormal hV p 0 +
      Q p * Specs.D04.C12.ClassicalRegularDomains.Model.outwardNormal hV p 1 = 0) →
    ((∀ z ∈ U, 0 < Specs.D04.C12.GreenCirculationAndFlux.Model.divergenceDensity P Q z) ∨
      (∀ z ∈ U, Specs.D04.C12.GreenCirculationAndFlux.Model.divergenceDensity P Q z < 0)) →
    False

end Specs.D13Unified.Ch13.Dulac
