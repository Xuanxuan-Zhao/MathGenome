import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C03.HigherInterfaces

/-! Pointwise crossed partials (d04:03:crossed-partials).
Ambient functions represent their restrictions to U. The first partials need
exist only on one neighborhood; their total derivatives are required only at a.
All dimensions include zero: quantification over Fin 0 is empty. -/
noncomputable section
open Set
namespace Specs.D04.C03.CrossedPartials
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C02.DerivativeBridge.Model
open Specs.D04.C03.HigherInterfaces.Model

def crossed_partialsType : Prop :=
  ∀ {n m : ℕ} (U : Set (E n)) (f : E n → E m) (a : E n)
    (hU : IsOpen U) (ha : a ∈ U)
    (hfirst : ∃ V : Set (E n), IsOpen V ∧ a ∈ V ∧ V ⊆ U ∧
      ∀ x ∈ V, ∀ i : Fin n, ∃ d, HasPartialDerivative f x i d)
    (hsecond : ∀ i : Fin n, TotalDifferentiableAt U (fun x => partialDerivative f x i) a),
    ∀ i j : Fin n,
      partialDerivative (fun x => partialDerivative f x i) a j =
      partialDerivative (fun x => partialDerivative f x j) a i

def twiceDifferentiable_crossed_partialsType : Prop :=
  ∀ {n m : ℕ} (U : Set (E n)) (f : E n → E m) (a : E n)
    (hf : TimesDifferentiableAt 2 U f a),
    ∀ i j : Fin n,
      partialDerivative (fun x => partialDerivative f x i) a j =
      partialDerivative (fun x => partialDerivative f x j) a i

end Specs.D04.C03.CrossedPartials
