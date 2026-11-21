import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C13.ExteriorDerivative
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C13.PullbackCalculus

/-! The three identities of d04:13:d-rules, on their original open domains.
The transports only reconcile equal natural-number degrees. No condition is
imposed on the ambient representatives outside their stated domains. -/
noncomputable section
namespace Specs.D04.C13.DifferentialIdentities
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C13.NormalizedFormsAndWedge.Model
open Specs.D04.C13.ExteriorDerivative.Model
open Specs.D04.C13.PullbackCalculus.Model

def exteriorDerivative_wedgeType : Prop :=
  ∀ {n p q : ℕ} (U : Set (E n)) (α : FormField n p) (β : FormField n q),
    IsCrForm (some 1) U α → IsCrForm (some 1) U β → ∀ x ∈ U,
      exteriorDerivative (fun y => wedge (α y) (β y)) x =
        castCovector (by omega : (p + 1) + q = (p + q) + 1)
          (wedge (exteriorDerivative α x) (β x)) +
        (-1 : ℝ) ^ p • castCovector (by omega : p + (q + 1) = (p + q) + 1)
          (wedge (α x) (exteriorDerivative β x))

def exteriorDerivative_squaredType : Prop :=
  ∀ {n k : ℕ} (U : Set (E n)) (ω : FormField n k),
    IsCrForm (some 2) U ω → ∀ x ∈ U,
      exteriorDerivative (exteriorDerivative ω) x = 0

def pullback_C1Type : Prop :=
  ∀ {m n k : ℕ} (U : Set (E m)) (V : Set (E n))
    (f : E m → E n) (ω : FormField n k),
    IsOpen U → Set.MapsTo f U V → CrOn 2 U f → IsCrForm (some 1) V ω →
      IsCrForm (some 1) U (pullback f ω)

def exteriorDerivative_pullbackType : Prop :=
  ∀ {m n k : ℕ} (U : Set (E m)) (V : Set (E n))
    (f : E m → E n) (ω : FormField n k),
    IsOpen U → Set.MapsTo f U V → CrOn 2 U f → IsCrForm (some 1) V ω →
      ∀ x ∈ U, exteriorDerivative (pullback f ω) x = pullback f (exteriorDerivative ω) x

end Specs.D04.C13.DifferentialIdentities
