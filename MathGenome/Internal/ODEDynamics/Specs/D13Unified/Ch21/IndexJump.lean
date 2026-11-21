import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch21.IndexProperties
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch21.Collar

/-! Independent specification of paper.tex, Lemma d13:21:jump.
The plane, circle quotient, determinant, collar, and winding convention are
exactly the shared upstream objects. No separation theorem is used. -/
namespace Specs.D13Unified.Ch21.IndexJump
noncomputable section
open Set Filter
open scoped Topology
open Specs.D13Unified.Ch21.IndexProperties
open Specs.D13Unified.Ch21.Collar

/-- The full original conclusion for every positively oriented collar. -/
def index_jumpStatement : Prop :=
  ∀ (γ : C(Circle, ℂ)), RegularEmbeddedLoop γ →
    ∀ (v : Circle → ℂ) (a : ℝ), IsCollar γ v a →
      ∀ pPlus ∈ positiveSide γ v a, ∀ pMinus ∈ negativeSide γ v a,
        index (circleLoop γ) pPlus - index (circleLoop γ) pMinus = 1

/-- Local constancy extends over every connected subset of the complement. -/
def index_constant_on_preconnectedStatement : Prop :=
  ∀ (α : Loop) (S : Set ℂ), IsPreconnected S →
    S ⊆ (range α)ᶜ → ∀ p ∈ S, ∀ q ∈ S, index α p = index α q

/-- In particular both collar sides have a single index value. -/
def collar_side_index_constantStatement : Prop :=
  ∀ (γ : C(Circle, ℂ)) (v : Circle → ℂ) (a : ℝ), IsCollar γ v a →
    (∀ p ∈ positiveSide γ v a, ∀ q ∈ positiveSide γ v a,
      index (circleLoop γ) p = index (circleLoop γ) q) ∧
    (∀ p ∈ negativeSide γ v a, ∀ q ∈ negativeSide γ v a,
      index (circleLoop γ) p = index (circleLoop γ) q)

/-- A single actual pair of points suffices after the local jump is proved. -/
def index_jump_of_one_pairStatement : Prop :=
  ∀ (γ : C(Circle, ℂ)) (v : Circle → ℂ) (a : ℝ), IsCollar γ v a →
    ∀ xPlus ∈ positiveSide γ v a, ∀ xMinus ∈ negativeSide γ v a,
      index (circleLoop γ) xPlus - index (circleLoop γ) xMinus = 1 →
      ∀ pPlus ∈ positiveSide γ v a, ∀ pMinus ∈ negativeSide γ v a,
        index (circleLoop γ) pPlus - index (circleLoop γ) pMinus = 1

/-- Logarithm charts continuous through a local arc when the reference point
is respectively above or below it. -/
def upperReferenceLog (z : ℂ) : ℂ :=
  Complex.log (Complex.I * z) - Complex.log Complex.I

def lowerReferenceLog (z : ℂ) : ℂ :=
  Complex.log (-Complex.I * z) - Complex.log (-Complex.I)

/-- The signed endpoint calculation underlying the angular jump. -/
def local_log_increment_limitStatement : Prop :=
  ∀ zLeft zRight : ℂ, zLeft.re < 0 → 0 < zRight.re →
    Tendsto (fun ε : ℝ =>
      (upperReferenceLog (zRight - (ε : ℂ) * Complex.I) -
        upperReferenceLog (zLeft - (ε : ℂ) * Complex.I)) -
      (lowerReferenceLog (zRight + (ε : ℂ) * Complex.I) -
        lowerReferenceLog (zLeft + (ε : ℂ) * Complex.I)))
      (𝓝 0) (𝓝 period)

end
end Specs.D13Unified.Ch21.IndexJump
