import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Duality.NeighborhoodCohomology
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.SingularChains

/-!
Alexander duality, paper.tex 2483–2535 (T32).

The sphere is the unit sphere in Euclidean (n+1)-space, with its subspace
topology. Homology is the shared augmented finite singular chain theory.
Reduced cohomology is the cohomology of the algebraic dual of that augmented
complex. Thus degree zero is reduced, and negative cohomology vanishes on
nonempty spaces. No neighborhood limit or Čech cohomology replaces the
singular cohomology of K in these statements.
-/
noncomputable section
open CategoryTheory Opposite

namespace P202Specs.AlexanderDuality
open P202Specs.SingularChains P202Specs.CohomologyPairs
open P202.Duality.NeighborhoodCohomology
universe u v

/-- Algebraic dual of the shared augmented, integer-indexed finite chains. -/
abbrev reducedCochains (R : Type u) [CommRing R] (X : TopCat.{v}) :=
  (dualComplexFunctor R R (ComplexShape.down ℤ)).obj (op (reducedComplex R R X))

abbrev reducedCohomology (R : Type u) [CommRing R] (X : TopCat.{v}) (q : ℤ) :=
  (reducedCochains R X).homology q

/-- The open complement has its actual subspace topology. -/
abbrev complement (n : ℕ) (K : Set (Sphere n)) : TopCat := TopCat.of (Kᶜ : Set (Sphere n))

/-- The full assertion with a specified coefficient ring. This definition adds
no finiteness, connectedness, manifold, or orientability premise about K. -/
def Holds (R : Type u) [CommRing R] : Prop :=
  ∀ (n : ℕ) (K : Set (Sphere n)), 1 ≤ n → K.Nonempty → K ≠ Set.univ →
    IsCompact K → LocallyContractibleSpace K → ∀ i : ℕ,
    Nonempty (reducedHomology R R (complement n K) (i : ℤ) ≃ₗ[R]
      reducedCohomology R (TopCat.of K) ((n : ℤ) - (i : ℤ) - 1))

namespace Expected

def integral : Prop := Holds ℤ

/-- Every fixed field, with itself as coefficient module, in every universe. -/
def field : Prop := ∀ (F : Type u) [Field F], Holds F

end Expected
end P202Specs.AlexanderDuality
