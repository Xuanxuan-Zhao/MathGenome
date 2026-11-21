import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C01.EuclideanInterfaces

/-! The canonical objects and independent statements of `d04:01:path-tests`.
`value` is a total extension used only on the displayed approach sets. The
source's function `f` has exactly the punctured-plane domain. Scalars in the
shared relative-limit interface are represented by their single real coordinate. -/
noncomputable section
open Set
namespace D04.ApproachDomainExample
open Specs.D04.C01.EuclideanInterfaces.Model

def point (x y : ℝ) : E 2 := WithLp.toLp 2 ![x, y]
def puncturedPlane : Set (E 2) := {p | p ≠ 0}
def value (p : E 2) : ℝ := p 0 ^ 2 * p 1 / (p 0 ^ 4 + p 1 ^ 2)
def f (p : puncturedPlane) : ℝ := value p

def lineSet (m : ℝ) : Set (E 2) := {p | p ≠ 0 ∧ p 1 = m * p 0}
def verticalSet : Set (E 2) := {p | p ≠ 0 ∧ p 0 = 0}
def positiveParabola : Set (E 2) := {p | 0 < p 0 ∧ p 1 = p 0 ^ 2}
def horizontalSet : Set (E 2) := lineSet 0

def scalar (b : ℝ) : E 1 := WithLp.toLp 2 ![b]
def limitOn (A : Set (E 2)) (b : ℝ) : Prop :=
  RelativeLimit A (fun p => scalar (value p)) 0 (scalar b)
end D04.ApproachDomainExample

namespace Specs.D04.C01.ApproachDomainExample
open D04.ApproachDomainExample

def line_limitType : Prop := ∀ m : ℝ, limitOn (lineSet m) 0
def vertical_valueType : Prop :=
  ∀ p : puncturedPlane, (p : EuclideanInterfaces.Model.E 2) 0 = 0 → f p = 0
def vertical_limitType : Prop := limitOn verticalSet 0
def parabola_valueType : Prop := ∀ x : ℝ, x ≠ 0 → value (point x (x ^ 2)) = 1 / 2
def positiveParabola_limitType : Prop := limitOn positiveParabola (1 / 2)
def horizontal_limitType : Prop := limitOn horizontalSet 0
def no_plane_limitType : Prop := ¬ ∃ b : ℝ, limitOn puncturedPlane b

end Specs.D04.C01.ApproachDomainExample
