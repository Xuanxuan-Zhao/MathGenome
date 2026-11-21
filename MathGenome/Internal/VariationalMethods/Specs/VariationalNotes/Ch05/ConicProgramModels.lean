import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexGeometry.PolarsBipolar
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
Models for paper.tex §5.3, equation `eq:conic-primal-dual` and the
complementary pairing (lines 2398–2411), with the positive-dual convention
of the preface and §1.5. Values are extended real, so infeasibility and
unboundedness are allowed. The definitions and gap results work for every
set K; hence they apply in particular to all closed convex cones containing
zero, without interior, full-dimensionality or pointedness assumptions.
The inner-product positive dual is the preimage of the shared continuous-dual
positive dual under the Riesz map, rather than a separate sign convention.
-/
noncomputable section
universe u v
namespace VariationalNotes.Ch05.ConicProgramModels.Specs

def innerPositiveDual {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (K : Set X) : Set X :=
  (InnerProductSpace.toDualMap ℝ X) ⁻¹' VariationalNotes.ConvexGeometry.Specs.positiveDual K

def innerPositiveDualType : Type (u + 1) :=
  ∀ {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X], Set X → Set X

def primalFeasible {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    {Y : Type v} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
    (K : Set X) (A : X →ₗ[ℝ] Y) (b : Y) : Set X :=
  {x | x ∈ K ∧ A x = b}

def primalFeasibleType : Type (max u v + 1) :=
  ∀ {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    {Y : Type v} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y], Set X → (X →ₗ[ℝ] Y) → Y → Set X

def dualFeasible {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    {Y : Type v} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
    (K : Set X) (A : X →ₗ[ℝ] Y) (c : X) : Set Y :=
  {y | c - A.adjoint y ∈ innerPositiveDual K}

def dualFeasibleType : Type (max u v + 1) :=
  ∀ {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    {Y : Type v} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y], Set X → (X →ₗ[ℝ] Y) → X → Set Y

def primalValue {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    {Y : Type v} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
    (K : Set X) (A : X →ₗ[ℝ] Y) (b : Y) (c : X) : EReal :=
  ⨅ x ∈ primalFeasible K A b, (inner ℝ c x : EReal)

def primalValueType : Type (max u v + 1) :=
  ∀ {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    {Y : Type v} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y], Set X → (X →ₗ[ℝ] Y) → Y → X → EReal

def dualValue {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    {Y : Type v} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
    (K : Set X) (A : X →ₗ[ℝ] Y) (b : Y) (c : X) : EReal :=
  ⨆ y ∈ dualFeasible K A c, (inner ℝ b y : EReal)

def dualValueType : Type (max u v + 1) :=
  ∀ {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    {Y : Type v} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y], Set X → (X →ₗ[ℝ] Y) → Y → X → EReal

def mem_innerPositiveDual : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X],
  ∀ (K : Set X) (s : X), s ∈ innerPositiveDual K ↔ ∀ x ∈ K, 0 ≤ inner ℝ s x

def gap_identity : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    {Y : Type v} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y],
  ∀ (K : Set X) (A : X →ₗ[ℝ] Y) (b : Y) (c x : X) (y : Y),
    x ∈ primalFeasible K A b →
    inner ℝ c x - inner ℝ b y = inner ℝ (c - A.adjoint y) x

def gap_nonneg : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    {Y : Type v} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y],
  ∀ (K : Set X) (A : X →ₗ[ℝ] Y) (b : Y) (c x : X) (y : Y),
    x ∈ primalFeasible K A b → y ∈ dualFeasible K A c →
    0 ≤ inner ℝ (c - A.adjoint y) x

def weak_duality : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    {Y : Type v} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y],
  ∀ (K : Set X) (A : X →ₗ[ℝ] Y) (b : Y) (c x : X) (y : Y),
    x ∈ primalFeasible K A b → y ∈ dualFeasible K A c →
    inner ℝ b y ≤ inner ℝ c x

def zero_gap_iff : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    {Y : Type v} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y],
  ∀ (K : Set X) (A : X →ₗ[ℝ] Y) (b : Y) (c x : X) (y : Y),
    x ∈ primalFeasible K A b → y ∈ dualFeasible K A c →
    (inner ℝ c x - inner ℝ b y = 0 ↔ inner ℝ (c - A.adjoint y) x = 0)

def equal_objectives_iff : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    {Y : Type v} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y],
  ∀ (K : Set X) (A : X →ₗ[ℝ] Y) (b : Y) (c x : X) (y : Y),
    x ∈ primalFeasible K A b → y ∈ dualFeasible K A c →
    (inner ℝ c x = inner ℝ b y ↔ inner ℝ (c - A.adjoint y) x = 0)

def value_weak_duality : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    {Y : Type v} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y],
  ∀ (K : Set X) (A : X →ₗ[ℝ] Y) (b : Y) (c : X),
    dualValue K A b c ≤ primalValue K A b c

end VariationalNotes.Ch05.ConicProgramModels.Specs
