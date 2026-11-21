import Mathlib.Algebra.Module.LinearMap.Polynomial
import Mathlib.Algebra.Lie.AdjointAction.Derivation
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Order.Lattice.Nat
import Mathlib.Analysis.Complex.Basic

/-!
The polynomial-locus part of LA-D06, source lines 1799–1833, with the
chapter convention at 1559–1562. Algebraic multiplicity means multiplicity
in the characteristic polynomial, not the dimension of the ordinary kernel.
The assertions here hold without the source's semisimplicity hypothesis.
Any Hausdorff finite-dimensional complex vector-space topology is the ordinary topology.
There is no nontriviality or positive-rank hypothesis.
-/

universe u

namespace Specs.LieAlgebrasAndRepresentations.MinimalZeroMultiplicityLocus

attribute [local instance 100] LieRing.ofAssociativeRing

variable (G : Type u) [LieRing G] [LieAlgebra ℂ G] [FiniteDimensional ℂ G]

/-- Algebraic multiplicity of the eigenvalue zero of the adjoint operator. -/
noncomputable def zeroMultiplicity (x : G) : ℕ :=
  (LieAlgebra.ad ℂ G x).charpoly.rootMultiplicity 0

/-- The minimum exists since the set of values is a nonempty set of naturals. -/
noncomputable def minimalZeroMultiplicity : ℕ :=
  sInf (Set.range (zeroMultiplicity G))

def minimalMultiplicityLocus : Set G :=
  {x | zeroMultiplicity G x = minimalZeroMultiplicity G}

/-- The coefficient of t^r in the universal adjoint characteristic polynomial. -/
noncomputable def regularPolynomial :
    MvPolynomial (Fin (Module.finrank ℂ G)) ℂ :=
  ((LieAlgebra.ad ℂ G).toLinearMap.polyCharpoly (Module.finBasis ℂ G)).coeff
    (minimalZeroMultiplicity G)

def minimum_type : Prop :=
  ∀ (G : Type u) [LieRing G] [LieAlgebra ℂ G] [FiniteDimensional ℂ G],
    (∃ x : G, zeroMultiplicity G x = minimalZeroMultiplicity G) ∧
    ∀ x : G, minimalZeroMultiplicity G ≤ zeroMultiplicity G x

def polynomial_locus_type : Prop :=
  ∀ (G : Type u) [LieRing G] [LieAlgebra ℂ G] [FiniteDimensional ℂ G],
    regularPolynomial G ≠ 0 ∧
    minimalMultiplicityLocus G =
      {x | MvPolynomial.eval ((Module.finBasis ℂ G).repr x) (regularPolynomial G) ≠ 0}

def topology_type : Prop :=
  ∀ (G : Type u) [LieRing G] [LieAlgebra ℂ G]
    [TopologicalSpace G] [IsTopologicalAddGroup G] [ContinuousSMul ℂ G]
    [T2Space G] [FiniteDimensional ℂ G],
    IsOpen (minimalMultiplicityLocus G) ∧
    Dense (minimalMultiplicityLocus G) ∧
    IsPathConnected (minimalMultiplicityLocus G)

/-- In particular the zero algebra has r = 0 and its entire singleton space is regular. -/
def zero_algebra_type : Prop :=
  ∀ (G : Type u) [LieRing G] [LieAlgebra ℂ G] [FiniteDimensional ℂ G]
    [Subsingleton G],
    (∀ x : G, zeroMultiplicity G x = 0) ∧
    minimalZeroMultiplicity G = 0 ∧ minimalMultiplicityLocus G = Set.univ

end Specs.LieAlgebrasAndRepresentations.MinimalZeroMultiplicityLocus
