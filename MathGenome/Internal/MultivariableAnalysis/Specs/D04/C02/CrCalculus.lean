import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C02.DerivativeInterfaces

/-! Independent specification of d04:02:cr-calculus. Iteration is ordered,
and derivative existence is separate from the total derivative selector.
The empty list denotes order zero. Closure is stated for the recursive
finite classes and, separately, their intersection `SmoothOn`. -/
noncomputable section
open Set
namespace Specs.D04.C02.CrCalculus
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model

namespace Model
/-- Read a list from left to right: first take its head partial, then its tail. -/
def iteratedPartial {n m : ℕ} (f : E n → E m) : List (Fin n) → E n → E m
  | [] => f
  | j :: js => iteratedPartial (fun x => partialDerivative f x j) js

/-- All orders through r are continuous, and every next partial through r
actually exists. No permutation or symmetry is built into this predicate. -/
def HasContinuousOrderedPartials {n m : ℕ} (r : ℕ) (U : Set (E n))
    (f : E n → E m) : Prop :=
  (∀ js : List (Fin n), js.length ≤ r → ContinuousOn (iteratedPartial f js) U) ∧
  (∀ js : List (Fin n), js.length < r → ∀ x ∈ U, ∀ j : Fin n,
    ∃ d, HasPartialDerivative (iteratedPartial f js) x j d)
end Model

abbrev iteratedPartialType := {n m : ℕ} → (E n → E m) → List (Fin n) → E n → E m
def iteratedPartialValue : iteratedPartialType := @Model.iteratedPartial
abbrev HasContinuousOrderedPartialsType :=
  {n m : ℕ} → ℕ → Set (E n) → (E n → E m) → Prop
def HasContinuousOrderedPartialsValue : HasContinuousOrderedPartialsType :=
  @Model.HasContinuousOrderedPartials

def crOn_iff_ordered_partialsType : Prop :=
  ∀ {n m : ℕ} (r : ℕ) (U : Set (E n)) (f : E n → E m), IsOpen U →
    (CrOn r U f ↔ Model.HasContinuousOrderedPartials r U f)

def crOn_sumType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y],
  ∀ (r : ℕ) {ι : Type} (s : Finset ι) (U : Set X) (f : ι → X → Y),
    IsOpen U → (∀ i ∈ s, CrOn r U (f i)) → CrOn r U (fun x => ∑ i ∈ s, f i x)

def crOn_const_smulType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y],
  ∀ (r : ℕ) (U : Set X) (f : X → Y) (c : ℝ),
    IsOpen U → CrOn r U f → CrOn r U (fun x => c • f x)

def crOn_compType : Prop :=
  ∀ {X Y Z : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z],
  ∀ (r : ℕ) (U : Set X) (V : Set Y) (f : X → Y) (g : Y → Z),
    IsOpen U → IsOpen V → MapsTo f U V → CrOn r U f → CrOn r V g →
    CrOn r U (g ∘ f)

def crOn_reciprocalType : Prop :=
  ∀ {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X],
  ∀ (r : ℕ) (U : Set X) (q : X → ℝ),
    IsOpen U → CrOn r U q → (∀ x ∈ U, q x ≠ 0) →
    CrOn r U (fun x => (q x)⁻¹)

/-- Scalar division of a vector is multiplication by the inverse scalar. -/
def crOn_quotientType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y],
  ∀ (r : ℕ) (U : Set X) (f : X → Y) (q : X → ℝ),
    IsOpen U → CrOn r U f → CrOn r U q → (∀ x ∈ U, q x ≠ 0) →
    CrOn r U (fun x => (q x)⁻¹ • f x)

def smoothOn_sumType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y],
  ∀ {ι : Type} (s : Finset ι) (U : Set X) (f : ι → X → Y),
    IsOpen U → (∀ i ∈ s, SmoothOn U (f i)) → SmoothOn U (fun x => ∑ i ∈ s, f i x)

def smoothOn_const_smulType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y],
  ∀ (U : Set X) (f : X → Y) (c : ℝ),
    IsOpen U → SmoothOn U f → SmoothOn U (fun x => c • f x)

def smoothOn_compType : Prop :=
  ∀ {X Y Z : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z],
  ∀ (U : Set X) (V : Set Y) (f : X → Y) (g : Y → Z),
    IsOpen U → IsOpen V → MapsTo f U V → SmoothOn U f → SmoothOn V g →
    SmoothOn U (g ∘ f)

def smoothOn_reciprocalType : Prop :=
  ∀ {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X],
  ∀ (U : Set X) (q : X → ℝ),
    IsOpen U → SmoothOn U q → (∀ x ∈ U, q x ≠ 0) →
    SmoothOn U (fun x => (q x)⁻¹)

def smoothOn_quotientType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y],
  ∀ (U : Set X) (f : X → Y) (q : X → ℝ),
    IsOpen U → SmoothOn U f → SmoothOn U q → (∀ x ∈ U, q x ≠ 0) →
    SmoothOn U (fun x => (q x)⁻¹ • f x)

/-- Arbitrary finite arity, heterogeneous finite-dimensional input spaces,
and algebraic multilinear maps: continuity is not an extra hypothesis. -/
def crOn_multilinearType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y],
  ∀ (r k : ℕ) (V : Fin k → Type) [∀ i, NormedAddCommGroup (V i)]
    [∀ i, NormedSpace ℝ (V i)] [∀ i, FiniteDimensional ℝ (V i)]
    (B : MultilinearMap ℝ V Y) (U : Set X) (f : (i : Fin k) → X → V i),
    IsOpen U → (∀ i, CrOn r U (f i)) → CrOn r U (fun x => B (fun i => f i x))

def smoothOn_multilinearType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y],
  ∀ (k : ℕ) (V : Fin k → Type) [∀ i, NormedAddCommGroup (V i)]
    [∀ i, NormedSpace ℝ (V i)] [∀ i, FiniteDimensional ℝ (V i)]
    (B : MultilinearMap ℝ V Y) (U : Set X) (f : (i : Fin k) → X → V i),
    IsOpen U → (∀ i, SmoothOn U (f i)) → SmoothOn U (fun x => B (fun i => f i x))
end Specs.D04.C02.CrCalculus
