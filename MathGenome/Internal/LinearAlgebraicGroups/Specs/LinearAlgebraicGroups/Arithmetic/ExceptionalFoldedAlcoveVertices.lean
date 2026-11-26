import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalAffineRootSystems

namespace LinearAlgebraicGroups.Specs.ExceptionalFoldedAlcoveVertices

open ExceptionalAffineRootSystems (ApartmentRoots FoldedRootDirection normalizedFoldedRoot unfoldApartment)

universe u

/-- The closed normalized dual F₄ alcove has a unique vertex opposite
each of its signed bounding walls. The base point lies near the origin
on the ray with equal absolute simple-root coordinates. -/
def Statement : Prop :=
  ∀ {V : Type u} [AddCommGroup V] [Module ℚ V]
    (A : ApartmentRoots ℚ V FoldedRootDirection) (e : (Fin 4 → ℚ) ≃ₗ[ℚ] V),
    (∀ a x, A.root a (e x) = normalizedFoldedRoot ℚ a x) →
    A.ReducedDirections →
    ∀ (c : ℚ), 0 < c →
    let p := e (unfoldApartment (fun _ : Fin 6 => c))
    (∀ a, |A.root a p| < 1) →
    ∀ a : A.SimpleWall p, ∃! x : V,
      (∀ b : FoldedRootDirection × ℤ, A.positive p b → 0 ≤ A.wallValue b x) ∧
      ∀ b : A.SimpleWall p, A.wallValue b.val x = 0 ↔ b ≠ a

end LinearAlgebraicGroups.Specs.ExceptionalFoldedAlcoveVertices
