import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C02.DerivativeBridge

/-! Independent propositions for chapters/02.tex, `d04:02:chain-rule`.

Functions on open subsets are represented by ambient extensions, as in the
upstream derivative interfaces. Both derivative predicates below already
include openness and membership of the basepoint. Only differentiability at
the two displayed basepoints is required. The generic pointwise forms need
no global image restriction; the bundled Euclidean statement retains the
source's `f : U → V` condition explicitly. All dimensions range over ℕ,
including zero. The Jacobian is the shared matrix in standard column bases.
-/
noncomputable section
open Set
namespace Specs.D04.C02.ChainRule
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C02.DerivativeBridge.Model

def hasTotalDerivative_compType : Prop :=
  ∀ {X Y Z : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (U : Set X) (V : Set Y) (f : X → Y) (g : Y → Z) (a : X)
    (A : X →L[ℝ] Y) (B : Y →L[ℝ] Z),
    HasTotalDerivative U f A a → HasTotalDerivative V g B (f a) →
      HasTotalDerivative U (g ∘ f) (B.comp A) a

def totalDifferentiableAt_compType : Prop :=
  ∀ {X Y Z : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (U : Set X) (V : Set Y) (f : X → Y) (g : Y → Z) (a : X),
    TotalDifferentiableAt U f a → TotalDifferentiableAt V g (f a) →
      TotalDifferentiableAt U (g ∘ f) a

def totalDerivative_compType : Prop :=
  ∀ {X Y Z : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (U : Set X) (V : Set Y) (f : X → Y) (g : Y → Z) (a : X),
    TotalDifferentiableAt U f a → TotalDifferentiableAt V g (f a) →
      totalDerivative (g ∘ f) a = (totalDerivative g (f a)).comp (totalDerivative f a)

def jacobian_compType : Prop :=
  ∀ {n m p : ℕ} (U : Set (E n)) (V : Set (E m))
    (f : E n → E m) (g : E m → E p) (a : E n),
    TotalDifferentiableAt U f a → TotalDifferentiableAt V g (f a) →
      jacobian (g ∘ f) a = jacobian g (f a) * jacobian f a

def chain_ruleType : Prop :=
  ∀ {n m p : ℕ} (U : Set (E n)) (V : Set (E m))
    (f : E n → E m) (g : E m → E p) (a : E n),
    MapsTo f U V →
    TotalDifferentiableAt U f a → TotalDifferentiableAt V g (f a) →
      TotalDifferentiableAt U (g ∘ f) a ∧
      totalDerivative (g ∘ f) a = (totalDerivative g (f a)).comp (totalDerivative f a) ∧
      jacobian (g ∘ f) a = jacobian g (f a) * jacobian f a

end Specs.D04.C02.ChainRule
