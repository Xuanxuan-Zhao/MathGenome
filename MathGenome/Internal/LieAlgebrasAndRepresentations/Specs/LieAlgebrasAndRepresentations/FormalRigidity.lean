import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.InfinitesimalDeformations
import Mathlib.RingTheory.PowerSeries.Basic

/-! LA-I03, formal-rigidity clause, source lines 4169–4182.
`Series g = ℕ → g` is the coefficient model of g[[t]], including when g has
infinite dimension. Scalar multiplication is the usual finite Cauchy sum.
Commutation with multiplication by t, together with k-linearity, is an equivalent
way to express k[[t]]-linearity here: it implies preservation of every t-adic
filtration and hence commutation with every scalar series. No convergence in k,
finite-rank hypothesis, or polynomial restriction is imposed.
The H² hypothesis below uses the ordinary exterior CE complex of the upstream
Specs. The computational low-degree quotient is only used internally. -/
noncomputable section
universe u v
namespace LieAlgebrasAndRepresentations.FormalRigidity
open LieModule.Cohomology
variable (k : Type u) (g : Type v) [Field k] [LieRing g] [LieAlgebra k g]
abbrev Series := ℕ → g

/-- Multiplication by t^n on vector-valued formal series. -/
def shift (n : ℕ) : Series g →ₗ[k] Series g where
  toFun x i := if n ≤ i then x (i-n) else 0
  map_add' x y := by funext i; dsimp; split <;> simp
  map_smul' a x := by funext i; dsimp; split <;> simp

/-- Inclusion of constant vector-valued series. -/
def constant : g →ₗ[k] Series g where
  toFun x i := if i = 0 then x else 0
  map_add' x y := by funext i; dsimp; split <;> simp
  map_smul' a x := by funext i; dsimp; split <;> simp

/-- Extend a k-linear endomorphism coefficient by coefficient. -/
def lift (a : g →ₗ[k] g) : Series g →ₗ[k] Series g where
  toFun x i := a (x i)
  map_add' x y := by funext i; exact a.map_add _ _
  map_smul' r x := by funext i; exact a.map_smul _ _

variable {k g}

/-- The standard k[[t]] scalar action, expressed in coefficients. -/
def scalar (a : PowerSeries k) (x : Series g) : Series g :=
  fun n => ∑ i ∈ Finset.range (n+1), PowerSeries.coeff i a • x (n-i)

variable (k g)

/-- The constant bracket μ extended to formal series by the Cauchy rule. -/
def standard : Series g →ₗ[k] Series g →ₗ[k] Series g where
  toFun x :=
    { toFun := fun y n => ∑ i ∈ Finset.range (n+1), ⁅x i,y (n-i)⁆
      map_add' := by
        intro y z; funext n
        simp [lie_add, Finset.sum_add_distrib]
      map_smul' := by
        intro a y; funext n
        simp [lie_smul, Finset.smul_sum] }
  map_add' := by
    intro x y; ext z n
    simp [add_lie, Finset.sum_add_distrib]
  map_smul' := by
    intro a x; ext y n
    simp [smul_lie, Finset.smul_sum]

/-- All formal brackets reducing to μ. The shift equations express bilinearity
in the formal parameter, not a restriction on the deformation coefficients. -/
structure Deformation where
  bracket : Series g →ₗ[k] Series g →ₗ[k] Series g
  shift_left : ∀ x y, bracket (shift k g 1 x) y = shift k g 1 (bracket x y)
  shift_right : ∀ x y, bracket x (shift k g 1 y) = shift k g 1 (bracket x y)
  alternating : ∀ x, bracket x x = 0
  jacobi : ∀ x y z, bracket x (bracket y z) + bracket y (bracket z x) +
    bracket z (bracket x y) = 0
  reduction : ∀ x y, bracket x y 0 = ⁅x 0,y 0⁆

variable {k g}
/-- A coordinate change and the successive composition converging to it.
The nth partial product already intertwines through degree n. The stabilization
clause states coefficientwise t-adic convergence with an explicit bound. -/
def Trivialization (B : Deformation k g) : Prop :=
  ∃ (T : Series g ≃ₗ[k] Series g) (a : ℕ → g →ₗ[k] g)
    (P : ℕ → Series g →ₗ[k] Series g),
    (∀ (r : PowerSeries k) (x : Series g), T (scalar r x) = scalar r (T x)) ∧
    (∀ x, T x 0 = x 0) ∧
    (∀ x y, B.bracket (T x) (T y) = T (standard k g x y)) ∧
    P 0 = LinearMap.id ∧
    (∀ n, P (n+1) = (P n).comp
      (LinearMap.id + (shift k g (n+1)).comp (lift k g (a n)))) ∧
    (∀ n x i, i ≤ n → P n x i = T x i) ∧
    (∀ n x y i, i ≤ n → B.bracket (P n x) (P n y) i = P n (standard k g x y) i)

end LieAlgebrasAndRepresentations.FormalRigidity

namespace Specs.LieAlgebrasAndRepresentations.FormalRigidity
open _root_.LieAlgebrasAndRepresentations.FormalRigidity
open _root_.LieAlgebrasAndRepresentations.AbelianExtensions
open _root_.AdvancedHomologicalAlgebra.CE

/-- Formal rigidity for vanishing ordinary adjoint CE H², for every field of
characteristic zero and every Lie algebra, with no dimension assumption. -/
def rigidityExpected : Prop :=
  ∀ {k : Type u} {g : Type v} [Field k] [CharZero k] [LieRing g] [LieAlgebra k g]
    (δ : ∀ n, (W k g n →ₗ[k] g) →ₗ[k] (W k g (n+1) →ₗ[k] g)),
    (∀ n, (δ (n+1)).comp (δ n) = 0) → HasLieCEFormula δ →
    Subsingleton (CEH2 δ) → ∀ B : Deformation k g, Trivialization B

/-- The formal-parameter linearity bridge for our coefficient representation. -/
def scalarLinearityExpected : Prop :=
  ∀ {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]
    (B : Deformation k g) (r : PowerSeries k) (x y : Series g),
    B.bracket (scalar r x) y = scalar r (B.bracket x y) ∧
      B.bracket x (scalar r y) = scalar r (B.bracket x y)

end Specs.LieAlgebrasAndRepresentations.FormalRigidity
