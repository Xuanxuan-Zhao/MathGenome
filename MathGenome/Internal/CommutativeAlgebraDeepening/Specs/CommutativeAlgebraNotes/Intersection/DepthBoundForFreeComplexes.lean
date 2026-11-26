import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.Definitions
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Homology.Additive
import Mathlib.RingTheory.FiniteLength

/-! The depth bound for bounded finite free complexes and its Cohen–Macaulay
specialization (Proposition 7.14). -/

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace Specs.CommutativeAlgebraNotes.Intersection.DepthBoundForFreeComplexes

universe u

/-- If the homology of the termwise tensor product with a nonzero finite module
has finite length in every degree and is nonzero in some degree, the length of
the free complex bounds the local depth of the coefficient module. -/
def depthBoundType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (F : ChainComplex (ModuleCat.{u} R) ℕ) (s : ℕ)
    (U : ModuleCat.{u} R) [Module.Finite R U] [Nontrivial U],
    (∀ i, Module.Free R (F.X i)) →
    (∀ i, Module.Finite R (F.X i)) →
    (∀ i, s < i → IsZero (F.X i)) →
    let K := ((tensorRight U).mapHomologicalComplex (ComplexShape.down ℕ)).obj F
    (∀ i, IsFiniteLength R (K.homology i)) →
    (∃ i, Nontrivial (K.homology i)) →
    AdvCommAlg.Depth.depth R U ≤ (s : ℕ∞)

/-- Over a Cohen–Macaulay local ring, a nonexact finite free complex with
finite-length homology has length at least the Krull dimension. The support
interval may start at any integer. -/
def dimensionBoundType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (F : ChainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) (s : ℕ),
    AdvCommAlg.CohenMacaulay.LocalCohenMacaulay R R →
    (∀ i, Module.Free R (F.X i)) →
    (∀ i, Module.Finite R (F.X i)) →
    (∀ i, i < a ∨ a + (s : ℤ) < i → IsZero (F.X i)) →
    (∀ i, IsFiniteLength R (F.homology i)) →
    (∃ i, Nontrivial (F.homology i)) →
    ringKrullDim R ≤ ((s : ℕ∞) : WithBot ℕ∞)

end Specs.CommutativeAlgebraNotes.Intersection.DepthBoundForFreeComplexes
