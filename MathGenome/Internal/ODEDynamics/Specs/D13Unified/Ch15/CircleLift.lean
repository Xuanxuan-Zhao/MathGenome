import Mathlib.Analysis.Normed.Group.AddCircle
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch15.DiscreteDefinitions

/-!
Independent specification of `paper.tex`, Definition `d13:15:circle-lift`.
The positive orientation on ℝ/ℤ is expressed by triples with representatives
`x < y < z < x + 1`. No differentiability or metric bound on a lift is imposed.
-/
namespace Specs.D13Unified.Ch15.CircleLift

noncomputable section

abbrev Circle := AddCircle (1 : ℝ)
def CircleType := Type

def quotientMapType := ℝ → Circle
def quotientMap : quotientMapType := fun x => (x : AddCircle (1 : ℝ))

/-- Exactly an increasing real homeomorphism commuting with unit translation. -/
structure IncreasingLift where
  toHomeomorph : ℝ ≃ₜ ℝ
  strictMono' : StrictMono toHomeomorph
  map_add_one' : ∀ x : ℝ, toHomeomorph (x + 1) = toHomeomorph x + 1

instance : CoeFun IncreasingLift (fun _ => ℝ → ℝ) := ⟨fun L => L.toHomeomorph⟩

def IncreasingLiftType := Type

/-- Value used to compare the shared structure as a type-valued definition. -/
def IncreasingLiftValue : IncreasingLiftType := IncreasingLift

def inverseLiftType := IncreasingLift → IncreasingLift

def inverseLift : inverseLiftType := fun L =>
  { toHomeomorph := L.toHomeomorph.symm
    strictMono' := fun a b hab => L.strictMono'.lt_iff_lt.mp (by simpa using hab)
    map_add_one' := fun x => by
      apply L.toHomeomorph.injective
      rw [L.toHomeomorph.apply_symm_apply, L.map_add_one',
        L.toHomeomorph.apply_symm_apply] }

def circleMapType := IncreasingLift → Circle → Circle

/-- Descent by the ordinary quotient of a periodic function. -/
def circleMap : circleMapType := fun L =>
  (show Function.Periodic (fun x : ℝ => quotientMap (L x)) (1 : ℝ) from by
    intro x
    change quotientMap (L.toHomeomorph (x + 1)) = quotientMap (L.toHomeomorph x)
    rw [L.map_add_one']
    exact AddCircle.coe_add_period _ _).lift

def PositivelyOrderedType := Circle → Circle → Circle → Prop

def PositivelyOrdered : PositivelyOrderedType := fun a b c =>
  ∃ x y z : ℝ, quotientMap x = a ∧ quotientMap y = b ∧ quotientMap z = c ∧
    x < y ∧ y < z ∧ z < x + 1

def OrientationPreservingType := (Circle → Circle) → Prop

def OrientationPreserving : OrientationPreservingType := fun F =>
  ∀ a b c, PositivelyOrdered a b c ↔ PositivelyOrdered (F a) (F b) (F c)

/-- For a homeomorphism, monotone and strictly increasing give the same lift class. -/
def increasingLift_iffStatement : Prop :=
  ∀ h : ℝ ≃ₜ ℝ, (∃ L : IncreasingLift, L.toHomeomorph = h) ↔
    Monotone h ∧ ∀ x : ℝ, h (x + 1) = h x + 1

def quotientMap_surjectiveStatement : Prop := Function.Surjective quotientMap

def quotientMap_eq_iffStatement : Prop :=
  ∀ x y : ℝ, quotientMap x = quotientMap y ↔ ∃ k : ℤ, x = y + (k : ℝ)

def circle_dist_eq_iInfStatement : Prop :=
  ∀ x y : ℝ, dist (quotientMap x) (quotientMap y) = ⨅ k : ℤ, |x - y - (k : ℝ)|

def map_add_intStatement : Prop :=
  ∀ (L : IncreasingLift) (x : ℝ) (k : ℤ), L (x + (k : ℝ)) = L x + (k : ℝ)

def lift_well_definedStatement : Prop :=
  ∀ (L : IncreasingLift) (x y : ℝ), quotientMap x = quotientMap y →
    quotientMap (L x) = quotientMap (L y)

def circleMap_quotientStatement : Prop :=
  ∀ (L : IncreasingLift) (x : ℝ), circleMap L (quotientMap x) = quotientMap (L x)

def circleMap_inverseStatement : Prop :=
  ∀ (L : IncreasingLift) (a : Circle),
    circleMap (inverseLift L) (circleMap L a) = a ∧
    circleMap L (circleMap (inverseLift L) a) = a

def circleMap_isHomeomorphStatement : Prop :=
  ∀ L : IncreasingLift, IsHomeomorph (circleMap L)

def circleMap_orientationPreservingStatement : Prop :=
  ∀ L : IncreasingLift, OrientationPreserving (circleMap L)

/-- The induced homeomorphism is constructed, orientation preserving, and unique. -/
def exists_unique_inducedHomeomorphStatement : Prop :=
  ∀ L : IncreasingLift, ∃! F : Circle ≃ₜ Circle,
    (∀ x : ℝ, F (quotientMap x) = quotientMap (L x)) ∧ OrientationPreserving F

def circleMap_iterateStatement : Prop :=
  ∀ (L : IncreasingLift) (n : ℕ) (x : ℝ),
    (circleMap L)^[n] (quotientMap x) = quotientMap ((L : ℝ → ℝ)^[n] x)

/-- Signed iteration uses the actual real and circle homeomorphisms. -/
def inducedHomeomorph_integerIterateStatement : Prop :=
  ∀ (L : IncreasingLift) (F : Circle ≃ₜ Circle),
    (∀ x : ℝ, F (quotientMap x) = quotientMap (L x)) →
    ∀ (n : ℤ) (x : ℝ),
      Specs.D13Unified.Ch15.DiscreteDefinitions.integerIterate F.toEquiv n (quotientMap x) =
      quotientMap (Specs.D13Unified.Ch15.DiscreteDefinitions.integerIterate
        L.toHomeomorph.toEquiv n x)

end
end Specs.D13Unified.Ch15.CircleLift
