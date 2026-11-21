import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch16.C0Algebra

/-! Independent statements for `paper.tex`, d10:16:stone-weierstrass-c0.
The algebra is nonunital. The norm on the canonical bundled C₀ space is
the supremum norm inherited from bounded continuous functions, and hence
the approximation and density below are uniform. Compact and empty domains
are included in the quantifiers. -/
noncomputable section
open Set
universe u

namespace Specs.D10Topology.Ch16.StoneWeierstrassC0
open C0Algebra
open Specs.D10Topology.Ch11.LocalCompactConventions

def stone_weierstrass_c0_real : Prop :=
  ∀ {X : Type u} [TopologicalSpace X], LCH X →
    ∀ (A : NonUnitalSubalgebra ℝ (RealC0 X)),
    (∀ x y : X, x ≠ y → ∃ a ∈ A, a x ≠ a y) →
    (∀ x : X, ∃ a ∈ A, a x ≠ 0) →
    ∀ (f : RealC0 X) (ε : ℝ), 0 < ε → ∃ a ∈ A, ‖f - a‖ < ε

def stone_weierstrass_c0_complex : Prop :=
  ∀ {X : Type u} [TopologicalSpace X], LCH X →
    ∀ (A : NonUnitalSubalgebra ℂ (ComplexC0 X)),
    (∀ x y : X, x ≠ y → ∃ a ∈ A, a x ≠ a y) →
    (∀ x : X, ∃ a ∈ A, a x ≠ 0) →
    (∀ a ∈ A, star a ∈ A) →
    ∀ (f : ComplexC0 X) (ε : ℝ), 0 < ε → ∃ a ∈ A, ‖f - a‖ < ε

def stone_weierstrass_c0_real_dense : Prop :=
  ∀ {X : Type u} [TopologicalSpace X], LCH X →
    ∀ (A : NonUnitalSubalgebra ℝ (RealC0 X)),
    (∀ x y : X, x ≠ y → ∃ a ∈ A, a x ≠ a y) →
    (∀ x : X, ∃ a ∈ A, a x ≠ 0) → Dense (A : Set (RealC0 X))

def stone_weierstrass_c0_complex_dense : Prop :=
  ∀ {X : Type u} [TopologicalSpace X], LCH X →
    ∀ (A : NonUnitalSubalgebra ℂ (ComplexC0 X)),
    (∀ x y : X, x ≠ y → ∃ a ∈ A, a x ≠ a y) →
    (∀ x : X, ∃ a ∈ A, a x ≠ 0) →
    (∀ a ∈ A, star a ∈ A) → Dense (A : Set (ComplexC0 X))

end Specs.D10Topology.Ch16.StoneWeierstrassC0
