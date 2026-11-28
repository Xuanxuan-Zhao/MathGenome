import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Quiver.Forms

/-! Isomorphism classes in a fixed dimension vector. -/

namespace RepTheorySurvey.Quiver.DimensionOrbitsSpec

universe u v w d

open FormsSpec

/-- The part of the finite-dimensional isomorphism-class space realized in dimension `x`. -/
abbrev FixedDimensionClass (k : Type w) {Q : Type u} [Field k] [Quiver.{v} Q]
    (x : DimensionVector Q) :=
  { c : RepresentationClass.{u, v, w, d} k Q //
    ∃ V : FiniteRepresentation.{u, v, w, d} k Q, Quotient.mk _ V = c ∧ dimensionVector V = x }

/-- A nonzero nonnegative vector of nonpositive Tits value has infinitely many classes. -/
abbrev InfiniteFixedDimensionClasses : Prop :=
  ∀ (k : Type w) {Q : Type u} [Field k] [Infinite k] [Quiver.{v} Q] [Fintype Q]
    [Fintype (RM03.Arrow Q)], ¬ RM03.HasOrientedCycle Q →
    ∀ x : DimensionVector Q, x ≠ 0 → (∀ i, 0 ≤ x i) → titsForm x ≤ 0 →
      Infinite (FixedDimensionClass.{u, v, w, max w d} k x)

end RepTheorySurvey.Quiver.DimensionOrbitsSpec
