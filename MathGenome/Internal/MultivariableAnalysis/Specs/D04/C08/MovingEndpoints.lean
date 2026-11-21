import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C02.DerivativeInterfaces
import MathGenome.SingleVariableAnalysis.RiemannIntegral

/-! The vector-parameter Leibniz rule, paper.tex `d04:08:endpoints`.
Ambient functions represent functions restricted to the displayed open sets.
Only the parameter derivative of the integrand is assumed to exist.
The integral below is the coordinatewise oriented scalar Darboux integral.
Its totalization outside the integrable case is irrelevant to the theorem. -/
noncomputable section
open Set
namespace Specs.D04.C08.MovingEndpoints
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
namespace Model
def orientedIntegral {k : ℕ} (f : ℝ → E k) (a b : ℝ) : E k := by
  classical
  exact WithLp.toLp 2 (fun i =>
    if h : SingleVariableAnalysis.Riemann.OrientedRealIntegrable (fun t => f t i) a b
    then SingleVariableAnalysis.Riemann.orientedRealIntegral (fun t => f t i) h else 0)
end Model

abbrev orientedIntegralType := {k : ℕ} → (ℝ → E k) → ℝ → ℝ → E k
def orientedIntegralValue : orientedIntegralType := @Model.orientedIntegral

def moving_endpointsType : Prop := ∀ {m k : ℕ} {I : Set ℝ} {P : Set (E m)},
  IsOpen I → OrdConnected I → IsOpen P →
  ∀ (f : ℝ → E m → E k) (A : ℝ → E m → E m →L[ℝ] E k),
  ContinuousOn (fun z : ℝ × E m => f z.1 z.2) (I ×ˢ P) →
  ContinuousOn (fun z : ℝ × E m => A z.1 z.2) (I ×ˢ P) →
  (∀ t ∈ I, ∀ p ∈ P, HasFDerivAt (f t) (A t p) p) →
  ∀ (a b : E m → ℝ), CrOn 1 P a → CrOn 1 P b →
  MapsTo a P I → MapsTo b P I →
  let F := fun p => Model.orientedIntegral (fun t => f t p) (a p) (b p)
  (∀ p ∈ P, SingleVariableAnalysis.Riemann.OrientedRealVectorIntegrable k
    (fun t => f t p) (a p) (b p) ∧ ∀ h : E m,
    SingleVariableAnalysis.Riemann.OrientedRealVectorIntegrable k
      (fun t => A t p h) (a p) (b p)) ∧
  CrOn 1 P F ∧ ∀ p ∈ P,
    DifferentiableAt ℝ F p ∧ ∀ h : E m,
    fderiv ℝ F p h =
      Model.orientedIntegral (fun t => A t p h) (a p) (b p) +
      (fderiv ℝ b p h) • f (b p) p - (fderiv ℝ a p h) • f (a p) p

end Specs.D04.C08.MovingEndpoints
