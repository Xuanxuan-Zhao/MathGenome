import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.ClosedSubgroups
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.FiniteWordClosure

noncomputable section

variable {k : Type u} [Field k]

/-- The (m)-fold product over the base field, with the empty product the base scheme. -/
@[reducible] def power (X : SchemeOver k) : ℕ → SchemeOver k
  | 0 => 𝟙_ (SchemeOver k)
  | m + 1 => X ⊗ power X m

/-- A word of length (n) has two inputs from (X) for each of its (n) factors. -/
abbrev wordDomain (X : SchemeOver k) (n : ℕ) : SchemeOver k :=
  power X (2 * n)

/-- Evaluate the ordered product of the signed pairs on sections over (T). -/
def evaluate {G : GroupScheme k} {X T : SchemeOver k} (f : X ⟶ G.X) :
    (n : ℕ) → (T ⟶ wordDomain X n) → (T ⟶ G.X)
  | 0, _ => 1
  | n + 1, p =>
    let a := p ≫ fst X (X ⊗ wordDomain X n)
    let q := p ≫ snd X (X ⊗ wordDomain X n)
    let b := q ≫ fst X (wordDomain X n)
    let r := q ≫ snd X (wordDomain X n)
    ((a ≫ f) * (b ≫ f)⁻¹) * evaluate f n r

/-- Conjugation stability on every test scheme over the field. -/
def ConjugationStable {G : GroupScheme k} {X : SchemeOver k} (f : X ⟶ G.X) : Prop :=
  ∀ (T : SchemeOver k) (g : T ⟶ G.X) (x : T ⟶ X),
    ∃ y : T ⟶ X, y ≫ f = g * (x ≫ f) * g⁻¹

def ExistsFiniteWordClosure : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) (X : SchemeOver k)
    (f : X ⟶ G.val.X) (x₀ : 𝟙_ (SchemeOver k) ⟶ X),
    IsAffine X.left → LocallyOfFiniteType X.hom → QuasiCompact X.hom →
    x₀ ≫ f = 1 → (∀ m, IsIntegral (power X m).left) → ConjugationStable f →
    ∃ (N : ClosedSubgroup G.val) (n : ℕ) (w : wordDomain X n ⟶ N.group.X),
      0 < n ∧ IsNormalSubgroup N.inclusion ∧ IsSchemeTheoreticallyDominant w.left ∧
      (∃ fN : X ⟶ N.group.X, fN ≫ N.inclusion.hom.hom = f) ∧
      (∀ (H : ClosedSubgroup G.val), (∃ fH : X ⟶ H.group.X, fH ≫ H.inclusion.hom.hom = f) →
        ∃ j : N.group ⟶ H.group, j ≫ H.inclusion = N.inclusion) ∧
      ∀ (T : SchemeOver k) (p : T ⟶ wordDomain X n),
        p ≫ w ≫ N.inclusion.hom.hom = evaluate f n p

end

end LinearAlgebraicGroups.Specs.FiniteWordClosure
