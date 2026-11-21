import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.HilbertCharacterization.RadialCriterion
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.LinearAlgebra.Dimension.Constructions

noncomputable section

namespace ExpandedFA.HilbertCharacterization

/-- Birkhoff orthogonality, including zero vectors. -/
def BirkhoffOrthogonal {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (x y : X) : Prop := ∀ t : ℝ, ‖x‖ ≤ ‖x + t • y‖

/-- The equivalence has no dimension or completeness hypothesis. -/
def BirkhoffRadialStatement : Prop :=
  ∀ (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X],
    (∀ x y : X, ‖radialRetraction x - radialRetraction y‖ ≤ ‖x - y‖) ↔
      (∀ x y : X, BirkhoffOrthogonal x y → BirkhoffOrthogonal y x)

/-- A separate copy of the coordinate plane, carrying the hexagonal norm. -/
def HexPlane := ℝ × ℝ
  deriving AddCommGroup, Module ℝ

namespace HexPlane

def coords (x : HexPlane) : ℝ × ℝ := x

def ofCoords (s t : ℝ) : HexPlane := (s, t)

/-- The max norm on the three coordinates s, t, s+t induces the required norm. -/
def embedding : HexPlane →ₗ[ℝ] (ℝ × ℝ) × ℝ where
  toFun x := (coords x, (coords x).1 + (coords x).2)
  map_add' x y := by
    change ((x.1+y.1, x.2+y.2), (x.1+y.1)+(x.2+y.2)) =
      ((x.1+y.1, x.2+y.2), (x.1+x.2)+(y.1+y.2))
    congr 1
    ring
  map_smul' a x := by
    change ((a*x.1, a*x.2), a*x.1+a*x.2) =
      ((a*x.1, a*x.2), a*(x.1+x.2))
    congr 1
    ring

instance : NormedAddCommGroup HexPlane :=
  NormedAddCommGroup.induced _ _ embedding (by
    intro x y h
    exact congrArg Prod.fst h)

instance : NormedSpace ℝ HexPlane := NormedSpace.induced ℝ _ _ embedding

/-- The standard alternating area form, with no rescaling. -/
def det (x y : HexPlane) : ℝ :=
  (coords x).1 * (coords y).2 - (coords x).2 * (coords y).1

/-- Antinorm for this area form and the closed hexagonal unit ball. -/
noncomputable def antinorm (y : HexPlane) : ℝ :=
  sSup {r : ℝ | ∃ x : HexPlane, ‖x‖ ≤ 1 ∧ r = |det x y|}

end HexPlane

/-- All assertions about the planar example, using its induced normed-space structure. -/
def HexPlaneExceptionStatement : Prop :=
  (∀ s t : ℝ, ‖HexPlane.ofCoords s t‖ = max (max |s| |t|) |s+t|) ∧
  (∀ y : HexPlane, HexPlane.antinorm y = ‖y‖) ∧
  (∀ x y : HexPlane, BirkhoffOrthogonal x y → BirkhoffOrthogonal y x) ∧
  (∀ x y : HexPlane, ‖radialRetraction x - radialRetraction y‖ ≤ ‖x-y‖) ∧
  (∃ x y : HexPlane, ‖x+y‖^2 + ‖x-y‖^2 ≠ 2*‖x‖^2 + 2*‖y‖^2) ∧
  Module.finrank ℝ HexPlane = 2 ∧
  ¬ Nonempty (InnerProductSpace ℝ HexPlane)

end ExpandedFA.HilbertCharacterization
