import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.GlobalPlaces

noncomputable section

open scoped RestrictedProduct

namespace LinearAlgebraicGroups.Arithmetic

universe u v

variable {K : Type u} [Field K] (D : GlobalFieldData.{u, v} K)

/-- The distinguished local subring is the valuation ring at finite places and the whole
completion at infinite places. -/
def GlobalFieldData.localIntegerSubring (w : D.Place) : Subring (D.Completion w) :=
  match w with
  | .inl w => (D.integers w).toSubring
  | .inr _ => ⊤

/-- Scalar adeles with the specified places removed, equipped with the restricted product
topology. -/
abbrev GlobalFieldData.AwayAdeleRing (S : Set D.Place) :=
  Πʳ w : (Sᶜ : Set D.Place), [D.Completion w.1, D.localIntegerSubring w.1]

/-- The rational diagonal in the restricted product away from a set of places. -/
def GlobalFieldData.awayDiagonalRange (S : Set D.Place) : Set (D.AwayAdeleRing S) :=
  {a | ∃ x : K, ∀ w : (Sᶜ : Set D.Place), a w = D.embedding w.1 x}

namespace AdditiveStrongApproximationSpec

/-- Strong approximation for scalars with just one place omitted. -/
def singlePlace : Prop :=
  ∀ {K : Type u} [Field K] (D : GlobalFieldData.{u, v} K) (w : D.Place),
    Dense (D.awayDiagonalRange {w})

/-- Simultaneous approximation at specified places, with integrality at every other
nonarchimedean place outside the omitted set. -/
def finiteTuples : Prop :=
  ∀ {K : Type u} [Field K] (D : GlobalFieldData.{u, v} K)
    (S : Set D.Place), S.Nonempty →
    ∀ (T : Finset (Sᶜ : Set D.Place))
      (U : ∀ w : (↑T : Set (Sᶜ : Set D.Place)), Set (D.Completion w.1.1)),
      (∀ w, IsOpen (U w)) → (∀ w, (U w).Nonempty) →
      ∃ x : K, (∀ w, D.embedding w.1.1 x ∈ U w) ∧
        ∀ w : (Sᶜ : Set D.Place), w ∉ T → D.embedding w.1 x ∈ D.localIntegerSubring w.1

end AdditiveStrongApproximationSpec

end LinearAlgebraicGroups.Arithmetic
