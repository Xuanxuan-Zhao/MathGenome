import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.GeometricRadicals
import Mathlib.RingTheory.Localization.Away.Basic

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace LinearAlgebraicGroups.Specs.TorusNormCovers

open GeometricRadicals (IsTorus)
noncomputable section

/-- The principal open cut out by the nonvanishing of a polynomial over the ground field. -/
abbrev PrincipalOpen {k : Type u} [Field k] {σ : Type u} (p : MvPolynomial σ k) :
    SchemeOver k :=
  (testSpec k).obj (op (CommAlgCat.of k (Localization.Away p)))

/-- A torus in characteristic zero is covered on algebraically closed extension points
by a morphism from a finite product of polynomial principal opens. -/
def TorusCoversByProducts : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (T : AffineAlgebraicGroup k), IsTorus T.val →
    ∃ (m : ℕ) (n : Fin m → ℕ) (p : ∀ i, MvPolynomial (ULift.{u} (Fin (n i))) k)
      (_ : ∀ i, p i ≠ 0) (f : (∏ᶜ fun i => PrincipalOpen (p i)) ⟶ T.val.X),
      ∀ (E : Type u) [Field E] [Algebra k E] [IsAlgClosed E],
        Function.Surjective (fun x : Points (∏ᶜ fun i => PrincipalOpen (p i))
          (CommAlgCat.of k E) => x ≫ f)

end

end LinearAlgebraicGroups.Specs.TorusNormCovers
