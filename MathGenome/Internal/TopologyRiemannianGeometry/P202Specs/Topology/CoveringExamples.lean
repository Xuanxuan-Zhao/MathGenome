import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.BasicFundamentalGroups
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.DeckGroup
import Mathlib.Data.ZMod.Basic

/-! Example 1.11, paper.tex 470–482. The circle and spheres are the actual
upstream unit spheres. Real projective space is the antipodal quotient of that
sphere, equipped with the quotient topology (the definition in the source).
Sheet numbers count the entire fiber at every point. -/
namespace P202Specs.Topology.CoveringExamples
open BasicFundamentalGroups
open scoped unitInterval
noncomputable section

def circlePower (m : ℕ) : C(Circle, Circle) :=
  ⟨fun z => z ^ m, continuous_id.pow m⟩

def circlePowerPointed (m : ℕ) : PointedMap Circle Circle 1 1 :=
  ⟨circlePower m, one_pow m⟩

/-- The actual m-th roots of unity on the complex unit circle. -/
abbrev CircleRoots (m : ℕ) := (powMonoidHom (α := Circle) m).ker

/-- Normalization by the endpoint of the exponential lift, so the isomorphism
used to identify the image subgroup really is winding number. -/
def WindingFormula (w : Pi1 Circle 1 ≃* Multiplicative ℤ) : Prop :=
  ∀ (a : SourcePath (1 : Circle) 1) (L : C(unitInterval, ℝ)),
    (∀ t, circleCover (L t) = a t) → L 0 = 0 →
      ((w (loopClass a)).toAdd : ℝ) = L 1

def antipodalSetoid (n : ℕ) : Setoid (Sphere n) where
  r x y := x = y ∨ x = -y
  iseqv := ⟨fun _ => Or.inl rfl,
    by intro x y h; rcases h with h | h
       · exact Or.inl h.symm
       · exact Or.inr (by rw [h, neg_neg]),
    by intro x y z h k; rcases h with rfl | h <;> rcases k with rfl | k
       · exact Or.inl rfl
       · exact Or.inr k
       · exact Or.inr h
       · exact Or.inl (by rw [h, k, neg_neg])⟩

/-- Real projective n-space with its antipodal quotient topology. -/
def RealProjective (n : ℕ) := Quotient (antipodalSetoid n)

instance (n : ℕ) : TopologicalSpace (RealProjective n) :=
  inferInstanceAs (TopologicalSpace (Quotient (antipodalSetoid n)))

def antipodalProjection (n : ℕ) : C(Sphere n, RealProjective n) :=
  ⟨Quotient.mk _, continuous_quot_mk⟩

def antipodalPointed (n : ℕ) (x : Sphere n) :
    PointedMap (Sphere n) (RealProjective n) x (antipodalProjection n x) :=
  ⟨antipodalProjection n, rfl⟩

namespace Expected

def circleCovering : Prop :=
  ∀ m : ℕ, 1 ≤ m → Covering (circlePower m) ∧
    ∀ z : Circle, Nat.card (Fiber (circlePower m) z) = m

def circleSubgroup : Prop :=
  ∃ w : Pi1 Circle 1 ≃* Multiplicative ℤ, WindingFormula w ∧
    ∀ m : ℕ, 1 ≤ m → ∀ a : Pi1 Circle 1,
      a ∈ (circlePowerPointed m).induced.range ↔ (m : ℤ) ∣ (w a).toAdd

def circleDeckTransformations : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    (∀ F : DeckGroup (circlePower m),
      ∃ r : CircleRoots m, ∀ z : Circle, F.val z = r.val * z) ∧
    (∀ r : CircleRoots m, ∃ F : DeckGroup (circlePower m),
      ∀ z : Circle, F.val z = r.val * z)

def circleDeckGroup : Prop :=
  ∀ m : ℕ, 1 ≤ m → Nonempty (DeckGroup (circlePower m) ≃* Multiplicative (ZMod m))

def projectiveCovering : Prop :=
  ∀ n : ℕ, 2 ≤ n → Covering (antipodalProjection n) ∧
    SimplyConnectedSpace (Sphere n) ∧
    ∀ b : RealProjective n, Nat.card (Fiber (antipodalProjection n) b) = 2

def projectiveSubgroup : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ x : Sphere n, (antipodalPointed n x).induced.range = ⊥

def projectiveFundamentalGroup : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ b : RealProjective n,
    Nonempty (Pi1 (RealProjective n) b ≃* Multiplicative (ZMod 2))

end Expected
end
end P202Specs.Topology.CoveringExamples
