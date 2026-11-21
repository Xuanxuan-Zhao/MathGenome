import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C02.DerivativeInterfaces

/-! Independent statements of d04:02:continuous-partials. Existence near a
point is separate from the derivative selector, and continuity is relative
to the original open domain. All dimensions, including zero, are allowed. -/
noncomputable section
open Set Filter Topology
namespace Specs.D04.C02.ContinuousPartials
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model

abbrev partialDerivativeMapType :=
  {n m : ℕ} → (E n → E m) → E n → E n →L[ℝ] E m

def partialDerivativeMapValue : partialDerivativeMapType :=
  fun {n m} f a => LinearMap.toContinuousLinearMap
    ((standardBasis n).constr ℝ (partialDerivative f a))

def partialDerivativeMap_applyType : Prop :=
  ∀ {n m : ℕ} (f : E n → E m) (a h : E n),
    partialDerivativeMapValue f a h = ∑ j : Fin n, h j • partialDerivative f a j

def partialDerivativeMap_columnType : Prop :=
  ∀ {n m : ℕ} (f : E n → E m) (a : E n) (j : Fin n),
    partialDerivativeMapValue f a (standardBasis n j) = partialDerivative f a j

/-- Existence of the coordinate partials in some neighborhood, with continuity
only at the specified point, gives the total derivative with these columns. -/
def continuous_partials_hasTotalDerivativeType : Prop :=
  ∀ {n m : ℕ} (U : Set (E n)) (f : E n → E m) (a : E n)
    (hU : IsOpen U) (ha : a ∈ U)
    (hd : ∀ᶠ x in 𝓝 a, ∀ j : Fin n, ∃ d, HasPartialDerivative f x j d)
    (hc : ∀ j : Fin n, ContinuousWithinAt (fun x => partialDerivative f x j) U a),
    HasTotalDerivative U f (partialDerivativeMapValue f a) a

def continuous_partials_continuous_totalDerivativeType : Prop :=
  ∀ {n m : ℕ} (U : Set (E n)) (f : E n → E m) (hU : IsOpen U)
    (hd : ∀ x ∈ U, ∀ j : Fin n, ∃ d, HasPartialDerivative f x j d)
    (hc : ∀ j : Fin n, ContinuousOn (fun x => partialDerivative f x j) U),
    TotalDifferentiableOn U f ∧ ContinuousOn (totalDerivative f) U

end Specs.D04.C02.ContinuousPartials
