import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.InfinitesimalDeformations
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-! LA-I03 (obstruction part), expanded source lines 4124–4173.
All coefficients are alternating, the action is adjoint, and the Jacobiator
is left-nested. Sequences are extended by zero past their truncation. -/
noncomputable section
universe u v
namespace LieAlgebrasAndRepresentations.DeformationObstructions
open LieModule.Cohomology AdvancedHomologicalAlgebra.CE
variable {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]

/-- The fixed undeformed Lie bracket as an alternating bilinear map. -/
def originalBracket : twoCochain k g g :=
  ⟨{ toFun := fun x =>
       { toFun := fun y => ⁅x,y⁆
         map_add' := lie_add x
         map_smul' := by intros; apply lie_smul }
     map_add' := by intros; ext; apply add_lie
     map_smul' := by intros; ext; apply smul_lie }, lie_self⟩

/-- Insertion of a binary alternating map into another, with cyclic signs. -/
def insertion (a b : twoCochain k g g) (x y z : g) : g :=
  a (b x y) z + a (b y z) x + a (b z x) y

/-- The coefficient of tⁿ in the left-nested Jacobiator. -/
def jacobiCoefficient (c : ℕ → twoCochain k g g) (n : ℕ) (x y z : g) : g :=
  ∑ p ∈ Finset.antidiagonal n, insertion (c p.1) (c p.2) x y z

/-- The actual displayed obstruction (9.2), with both indices positive. -/
def obstruction (c : ℕ → twoCochain k g g) (n : ℕ) (x y z : g) : g :=
  ∑ p ∈ (Finset.antidiagonal n).filter (fun p => 0 < p.1 ∧ 0 < p.2),
    insertion (c p.1) (c p.2) x y z

/-- Exactly a bracket μ+…+t^(N−1)c_(N−1) satisfying Jacobi modulo tᴺ. -/
structure TruncatedDeformation (N : ℕ) where
  coeff : ℕ → twoCochain k g g
  base : coeff 0 = originalBracket
  cutoff : ∀ i, N ≤ i → coeff i = 0
  jacobi : ∀ n, n < N → ∀ x y z, jacobiCoefficient coeff n x y z = 0

/-- An extension keeps all lower coefficients and adds the single coefficient cᴺ. -/
def Extends {N : ℕ} (c : TruncatedDeformation (k := k) (g := g) N)
    (b : twoCochain k g g) : Prop :=
  ∀ n, n < N+1 → ∀ x y z,
    jacobiCoefficient (Function.update c.coeff N b) n x y z = 0

/-- The degree-three CE formula for the adjoint module. -/
def dThree (T : g → g → g → g) (x y z w : g) : g :=
  ⁅x,T y z w⁆ - ⁅y,T x z w⁆ + ⁅z,T x y w⁆ - ⁅w,T x y z⁆ -
  T ⁅x,y⁆ z w + T ⁅x,z⁆ y w - T ⁅x,w⁆ y z -
  T ⁅y,z⁆ x w + T ⁅y,w⁆ x z - T ⁅z,w⁆ x y

/-- Boundaries inside the cycles of the ordinary exterior-power CE complex. -/
def thirdBoundaries
    (δ : ∀ n, (W k g n →ₗ[k] g) →ₗ[k] (W k g (n+1) →ₗ[k] g)) :
    Submodule k (LinearMap.ker (δ 3)) :=
  (LinearMap.range (δ 2)).comap (LinearMap.ker (δ 3)).subtype

abbrev ThirdCohomology
    (δ : ∀ n, (W k g n →ₗ[k] g) →ₗ[k] (W k g (n+1) →ₗ[k] g)) :=
  LinearMap.ker (δ 3) ⧸ thirdBoundaries δ

end LieAlgebrasAndRepresentations.DeformationObstructions

namespace Specs.LieAlgebrasAndRepresentations.DeformationObstructions
open _root_.LieAlgebrasAndRepresentations.DeformationObstructions
open _root_.LieAlgebrasAndRepresentations.AbelianExtensions
open LieModule.Cohomology _root_.AdvancedHomologicalAlgebra.CE
variable (k : Type u) (g : Type v) [Field k] [CharZero k] [LieRing g] [LieAlgebra k g]

/-- Full closure, not an assumed certificate. -/
def closureStatement : Prop :=
  ∀ (N : ℕ), 1 ≤ N → ∀ c : TruncatedDeformation (k := k) (g := g) N,
    ∀ x y z w, dThree (obstruction c.coeff N) x y z w = 0

/-- The source sign convention fixes the exact extension equation. -/
def extensionEquationStatement : Prop :=
  ∀ (N : ℕ), 1 ≤ N → ∀ (c : TruncatedDeformation (k := k) (g := g) N)
    (b : twoCochain k g g),
    Extends c b ↔ ∀ x y z, d₂₃ k g g b x y z = obstruction c.coeff N x y z

/-- The obstruction is an actual alternating CE three-cocycle, and its class
vanishes exactly when a next coefficient exists. The differential is quantified
with its full ordinary CE formula, as in the accepted upstream interface. -/
def cohomologyStatement : Prop :=
  ∀ (δ : ∀ n, (W k g n →ₗ[k] g) →ₗ[k] (W k g (n+1) →ₗ[k] g)),
    (∀ n, (δ (n+1)).comp (δ n) = 0) → HasLieCEFormula δ →
    ∀ (N : ℕ), 1 ≤ N → ∀ c : TruncatedDeformation (k := k) (g := g) N,
    ∃ O : LinearMap.ker (δ 3),
      (∀ x y z, O.1 (wedge k g 3 ![x,y,z]) = obstruction c.coeff N x y z) ∧
      ((Submodule.Quotient.mk O : ThirdCohomology δ) = 0 ↔
        ∃ b : twoCochain k g g, Extends c b)

def closureExpected : Prop :=
  ∀ {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g] [CharZero k],
    closureStatement k g

def extensionEquationExpected : Prop :=
  ∀ {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g] [CharZero k],
    extensionEquationStatement k g

def cohomologyExpected : Prop :=
  ∀ {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g] [CharZero k],
    cohomologyStatement k g

end Specs.LieAlgebrasAndRepresentations.DeformationObstructions
