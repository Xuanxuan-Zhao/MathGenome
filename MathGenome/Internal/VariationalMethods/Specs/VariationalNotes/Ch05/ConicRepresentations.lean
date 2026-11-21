import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch05.OrthantLorentzCones
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch05.SingularSchurComplement

/-!
The representations following `prop:singular-schur`, paper.tex §v05-04.
Euclidean norms and the shared Lorentz and Schur-block objects are used.
All finite index types, including the empty type, are allowed. The standard
form has variable (x,z), cone X × K, equation z - A x = d, and cost (c,0).
The equivalences hold for every K; closed convex cones are preserved by the
construction. No feasibility, boundedness, or strict feasibility is assumed.
-/
noncomputable section
open scoped InnerProductSpace
universe u v
namespace VariationalNotes.Ch05.ConicRepresentations.Specs

section Models
variable {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
variable {Y : Type v} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

/-- The full-space factor retains the unrestricted original variable. -/
def standardCone (K : Set Y) : Set (WithLp 2 (X × Y)) :=
  WithLp.ofLp ⁻¹' (Set.univ ×ˢ K)

def standardMap (A : X →ₗ[ℝ] Y) : WithLp 2 (X × Y) →ₗ[ℝ] Y :=
  WithLp.sndₗ 2 ℝ X Y - A.comp (WithLp.fstₗ 2 ℝ X Y)

def standardLift (A : X →ₗ[ℝ] Y) (d : Y) (x : X) : WithLp 2 (X × Y) :=
  WithLp.toLp 2 (x, A x + d)

def standardCost (c : X) : WithLp 2 (X × Y) := WithLp.toLp 2 (c, 0)
end Models

def standardConeType : Type (max u v + 1) :=
  ∀ {X : Type u} {Y : Type v}, Set Y → Set (WithLp 2 (X × Y))

def standardMapType : Type (max u v + 1) :=
  ∀ {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    {Y : Type v} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y],
    (X →ₗ[ℝ] Y) → WithLp 2 (X × Y) →ₗ[ℝ] Y

def standardLiftType : Type (max u v + 1) :=
  ∀ {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    {Y : Type v} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y],
    (X →ₗ[ℝ] Y) → Y → X → WithLp 2 (X × Y)

def standardCostType : Type (max u v + 1) :=
  ∀ {X : Type u} {Y : Type v} [NormedAddCommGroup Y], X → WithLp 2 (X × Y)

def lorentz_representation : Prop :=
  ∀ {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    (B : EuclideanSpace ℝ m →ₗ[ℝ] EuclideanSpace ℝ n)
    (d : EuclideanSpace ℝ n) (a x : EuclideanSpace ℝ m) (β : ℝ),
    ‖B x + d‖ ≤ inner ℝ a x + β ↔
      WithLp.toLp 2 (inner ℝ a x + β, B x + d) ∈ OrthantLorentzCones.Specs.lorentzCone

def squared_norm_representation : Prop :=
  ∀ {m : Type u} {n : Type v} [Fintype m] [Fintype n] [DecidableEq n]
    (B : EuclideanSpace ℝ m →ₗ[ℝ] EuclideanSpace ℝ n)
    (d : EuclideanSpace ℝ n) (x : EuclideanSpace ℝ m) (t : ℝ),
    ‖B x + d‖ ^ 2 ≤ t ↔
      (SingularSchurComplement.Specs.schurBlock (1 : Matrix n n ℝ) t (B x + d)).PosSemidef

def standardCone_properties : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    {Y : Type v} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] (K : Set Y),
    IsClosed K → VariationalNotes.ConvexGeometry.Specs.IsCone K →
    IsClosed (standardCone (X := X) K) ∧ Convex ℝ (standardCone (X := X) K) ∧
      VariationalNotes.ConvexGeometry.Specs.IsCone (standardCone (X := X) K)

-- The statement explicitly identifies every standard feasible point, as well
-- as providing a standard feasible point from every original feasible point.
def standard_feasibility : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    {Y : Type v} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y],
  ∀ (K : Set Y) (A : X →ₗ[ℝ] Y) (d : Y) (p : WithLp 2 (X × Y)),
    p ∈ ConicProgramModels.Specs.primalFeasible (standardCone K) (standardMap A) d ↔
      A p.fst + d ∈ K ∧ p = standardLift A d p.fst

def standard_feasible_lift : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    {Y : Type v} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y],
  ∀ (K : Set Y) (A : X →ₗ[ℝ] Y) (d : Y) (x : X),
    A x + d ∈ K ↔ standardLift A d x ∈
      ConicProgramModels.Specs.primalFeasible (standardCone K) (standardMap A) d

def standard_feasible_exists : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    {Y : Type v} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y],
  ∀ (K : Set Y) (A : X →ₗ[ℝ] Y) (d : Y),
    (∃ x : X, A x + d ∈ K) ↔
      (ConicProgramModels.Specs.primalFeasible (standardCone K) (standardMap A) d).Nonempty

def standard_objective : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    {Y : Type v} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y],
  ∀ (c : X) (p : WithLp 2 (X × Y)),
    inner ℝ (standardCost c) p = inner ℝ c p.fst

-- Extended real values also cover infeasibility and unboundedness.
def standard_value : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    {Y : Type v} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y],
  ∀ (K : Set Y) (A : X →ₗ[ℝ] Y) (d : Y) (c : X),
    ConicProgramModels.Specs.primalValue (standardCone K) (standardMap A) d (standardCost c) =
      ⨅ x : X, ⨅ (_ : A x + d ∈ K), (inner ℝ c x : EReal)

end VariationalNotes.Ch05.ConicRepresentations.Specs
