import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C05.ExtremaInterfaces
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C02.DerivativeBridge
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C04.RegularLevel

/-! Independent statements for d04:05:lagrange. Ambient representatives are
restricted to the open set U, as in the shared derivative interfaces. Covectors
are continuous linear maps; in finite dimension these are all linear covectors.
The multiplier is held fixed when differentiating the Lagrangian. -/
noncomputable section
open Set
open scoped BigOperators
namespace Specs.D04.C05.LagrangeMultipliers
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C02.DerivativeBridge.Model
open Specs.D04.C05.ExtremaInterfaces.Model
open Specs.D04.C04.RegularLevel.Model
namespace Model

def lagrangian {n q : ℕ} (f : E n → ℝ) (g : E n → E q)
    (ℓ : E q →L[ℝ] ℝ) (x : E n) : ℝ :=
  f x - ∑ i : Fin q, ℓ (standardBasis q i) * g x i

/-- The covector equation, its actual gradient expression, and the existing
zero derivative of the Lagrangian, with the paper's minus sign. -/
def MultiplierEquations {n q : ℕ} (f : E n → ℝ) (g : E n → E q)
    (a : E n) (ℓ : E q →L[ℝ] ℝ) : Prop :=
  totalDerivative f a = ℓ.comp (totalDerivative g a) ∧
  scalarGradient f a = ∑ i : Fin q,
    ℓ (standardBasis q i) • scalarGradient (fun x => g x i) a ∧
  HasTotalDerivative (Set.univ : Set (E n)) (lagrangian f g ℓ) 0 a

end Model
open Model

abbrev lagrangianType := {n q : ℕ} → (E n → ℝ) → (E n → E q) →
  (E q →L[ℝ] ℝ) → E n → ℝ
def lagrangianValue : lagrangianType := @Model.lagrangian

def covector_coordinatesType : Prop :=
  ∀ {q : ℕ} (ℓ : E q →L[ℝ] ℝ) (y : E q),
    ℓ y = ∑ i : Fin q, ℓ (standardBasis q i) * y i

def lagrange_multipliersType : Prop :=
  ∀ {n q : ℕ} (U : Set (E n)) (f : E n → ℝ) (g : E n → E q)
    (c : E q) (a : E n),
    IsOpen U → ContDiffOn ℝ 1 f U → ContDiffOn ℝ 1 g U →
    a ∈ level U g c →
    (LocalMinimumOn (level U g c) f a ∨ LocalMaximumOn (level U g c) f a) →
    Function.Surjective (totalDerivative g a) →
    ∃! ℓ : E q →L[ℝ] ℝ, MultiplierEquations f g a ℓ

def zero_constraints_fermatType : Prop :=
  ∀ {n : ℕ} (U : Set (E n)) (f : E n → ℝ) (g : E n → E 0)
    (c : E 0) (a : E n),
    IsOpen U → ContDiffOn ℝ 1 f U → ContDiffOn ℝ 1 g U → a ∈ U →
    (LocalMinimumOn U f a ∨ LocalMaximumOn U f a) →
    totalDerivative f a = 0 ∧ scalarGradient f a = 0 ∧
    (∀ x, lagrangian f g 0 x = f x) ∧
    ∃! ℓ : E 0 →L[ℝ] ℝ, MultiplierEquations f g a ℓ

def full_codimension_multipliersType : Prop :=
  ∀ {n : ℕ} (U : Set (E n)) (f : E n → ℝ) (g : E n → E n)
    (c a : E n),
    IsOpen U → ContDiffOn ℝ 1 f U → ContDiffOn ℝ 1 g U →
    a ∈ level U g c → Function.Surjective (totalDerivative g a) →
    (∃ O, IsOpen O ∧ a ∈ O ∧ level U g c ∩ O = {a}) ∧
    StrictLocalMinimumOn (level U g c) f a ∧
    StrictLocalMaximumOn (level U g c) f a ∧
    ∃! ℓ : E n →L[ℝ] ℝ, MultiplierEquations f g a ℓ

end Specs.D04.C05.LagrangeMultipliers
