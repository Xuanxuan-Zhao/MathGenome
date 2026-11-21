import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch06.HolomorphicDependence
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch05.OpenDomain

/-! Independent coordinate-series statement of the local part of
`paper.tex`, d13:06:real-analytic. Real coordinates use the maximum norm;
the original ParameterODE and its canonical maximal solutions are retained. -/
noncomputable section
namespace D13Unified.Ch06.RealAnalytic
open Metric Set
open Specs.D13Unified.Ch01.AutonomousParameters
open Specs.D13Unified.Ch04.MaximalSolutionMap

/-- Local absolutely convergent real coordinate power series, in all finite
source and target dimensions, including zero. -/
def CoordinateRealAnalyticOn {d n : ℕ} (V : Set (Fin d → ℝ))
    (f : (Fin d → ℝ) → Fin n → ℝ) : Prop :=
  ∀ a ∈ V, ∃ r : ℝ, 0 < r ∧ ball a r ⊆ V ∧
    ∀ i : Fin n, ∃ c : (Fin d → ℕ) → ℝ,
      ∀ z ∈ ball a r,
        Summable (fun α => ‖c α * ∏ j : Fin d, (z j - a j) ^ α j‖) ∧
        HasSum (fun α => c α * ∏ j : Fin d, (z j - a j) ^ α j) (f z i)

def complexifyPoint {d : ℕ} (x : Fin d → ℝ) : Fin d → ℂ := fun i => (x i : ℂ)
def conjugatePoint {d : ℕ} (z : Fin d → ℂ) : Fin d → ℂ := fun i => star (z i)

def realFieldPoint {n m : ℕ} (t : ℝ) (x : Fin n → ℝ) (p : Fin m → ℝ) :
    Fin (n + m + 1) → ℝ := Fin.cons t (Fin.append x p)

/-- The original association of triples is `((t,x),p)`. -/
def fieldData {n m : ℕ} (q : Fin (n + m + 1) → ℝ) :
    (ℝ × (Fin n → ℝ)) × (Fin m → ℝ) :=
  ((q 0, fun i => Fin.tail q (Fin.castAdd m i)),
    fun i => Fin.tail q (Fin.natAdd n i))

def fieldInCoordinates {n m : ℕ} (F : ParameterODE (Fin n → ℝ) (Fin m → ℝ))
    (q : Fin (n + m + 1) → ℝ) : Fin n → ℝ :=
  parameterEvalValue F (fieldData q).1.1 (fieldData q).1.2 (fieldData q).2

def solutionDomainInCoordinates {n m : ℕ}
    (F : ParameterODE (Fin n → ℝ) (Fin m → ℝ)) : Set (Fin (n + m + 2) → ℝ) :=
  {q | (q 0, fieldData (Fin.tail q)) ∈ parameterSolutionDomainValue F}

def solutionInCoordinates {n m : ℕ}
    (F : ParameterODE (Fin n → ℝ) (Fin m → ℝ))
    (q : Fin (n + m + 2) → ℝ) : Fin n → ℝ :=
  parameterSolutionValueValue F (q 0) (fieldData (Fin.tail q)).1.1
    (fieldData (Fin.tail q)).1.2 (fieldData (Fin.tail q)).2

end D13Unified.Ch06.RealAnalytic

namespace Specs.D13Unified.Ch06.RealAnalyticLocal
open Metric Set
open _root_.D13Unified _root_.D13Unified.Ch06.RealAnalytic
open _root_.D13Unified.Ch06.HolomorphicLimits
open _root_.D13Unified.Ch06.HolomorphicDependence

/-- The local diagonal assertion includes both actual-domain containment and
joint real analyticity throughout one positive-radius moving-data ball. -/
def localRealAnalyticDependence_type : Prop :=
  ∀ {n m : ℕ} (F : ParameterODE (Fin n → ℝ) (Fin m → ℝ)),
    CoordinateRealAnalyticOn (fieldData ⁻¹' F.domain) (fieldInCoordinates F) →
    ∀ (s : ℝ) (ξ : Fin n → ℝ) (p : Fin m → ℝ), ((s, ξ), p) ∈ F.domain →
      ∃ r : ℝ, 0 < r ∧
        ball (Fin.cons s (realFieldPoint s ξ p)) r ⊆ solutionDomainInCoordinates F ∧
        CoordinateRealAnalyticOn (ball (Fin.cons s (realFieldPoint s ξ p)) r)
          (solutionInCoordinates F)

/-- A real series supplies a local holomorphic extension with conjugation
symmetry. Neither the extension nor its reality is an input assumption. -/
def localComplexification_type : Prop :=
  ∀ {d n : ℕ} {V : Set (Fin d → ℝ)} {f : (Fin d → ℝ) → Fin n → ℝ},
    CoordinateRealAnalyticOn V f → ∀ a ∈ V,
      ∃ r : ℝ, 0 < r ∧ ball a r ⊆ V ∧
        ∃ g : (Fin d → ℂ) → Fin n → ℂ,
          CoordinateHolomorphicOn (ball (complexifyPoint a) r) g ∧
          (∀ x ∈ ball a r, g (complexifyPoint x) = complexifyPoint (f x)) ∧
          (∀ z, g (conjugatePoint z) = conjugatePoint (g z))


/-- Analyticity supplies the local uniqueness hypothesis on the actual field
domain, uniformly in nearby times and parameters. -/
def analyticFieldLocallyLipschitz_type : Prop :=
  ∀ {n m : ℕ} (F : ParameterODE (Fin n → ℝ) (Fin m → ℝ)),
    CoordinateRealAnalyticOn (fieldData ⁻¹' F.domain) (fieldInCoordinates F) →
    Specs.D13Unified.Ch03.LocalLipschitz.parameterLocallyLipschitzInStateValue F

def analyticSolutionDomainOpen_type : Prop :=
  ∀ {n m : ℕ} (F : ParameterODE (Fin n → ℝ) (Fin m → ℝ)),
    CoordinateRealAnalyticOn (fieldData ⁻¹' F.domain) (fieldInCoordinates F) →
    IsOpen (solutionDomainInCoordinates F)

end Specs.D13Unified.Ch06.RealAnalyticLocal
