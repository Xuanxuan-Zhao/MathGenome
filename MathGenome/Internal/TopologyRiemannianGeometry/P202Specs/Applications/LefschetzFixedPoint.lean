import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Homology.SimplicialComparison
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.SimplicialApproximation
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.BigOperators.Finprod

/-! Independent statements for paper.tex, T35 (2903–2955).

A finite polyhedron is any space homeomorphic to the weak realization of a
finite abstract simplicial complex. Neither connectedness nor nonemptiness is
required. Homology and its maps are the previously specified singular objects,
with rational coefficients. `finsum` is the algebraic finite-support sum; the
finiteness statement below supplies its mathematical justification.
-/

noncomputable section
open CategoryTheory HomologicalComplex
open scoped BigOperators
universe u v w

namespace P202Specs.LefschetzFixedPoint
open P202.Cellular P202.Cellular.AbstractSimplicialComplex

def IsFinitePolyhedron (X : TopCat.{w}) : Prop :=
  ∃ (V : Type w) (K : AbstractSimplicialComplex V),
    K.IsFinite ∧ Nonempty (X ≃ₜ K.Realization)

abbrev rationalHomology (X : TopCat.{w}) (n : ℕ) :=
  (P202Specs.SingularChains.complex ℚ ℚ X).homology n

abbrev rationalHomologyMap {X Y : TopCat.{w}} (f : X ⟶ Y) (n : ℕ) :=
  homologyMap (P202Specs.SingularChains.chainMap ℚ ℚ f) n

def lefschetzNumber {X : TopCat.{w}} (f : X ⟶ X) : ℚ :=
  ∑ᶠ n : ℕ, (-1 : ℚ) ^ n *
    LinearMap.trace ℚ (rationalHomology X n) (rationalHomologyMap f n).hom

/- The unused type markers retain independent coefficient universe parameters
for the conditional interface. They disappear by definitional reduction and
add no hypothesis or mathematical quantifier to any statement below. -/

/-- The groups whose endomorphism traces occur in the sum really are finite
dimensional, and vanish above one uniform bound. -/
def homologyFiniteness_type : Prop :=
  let _ : Type u := ULift.{u} Unit
  let _ : Type v := ULift.{v} Unit
  ∀ (X : TopCat.{w}), IsFinitePolyhedron X →
    (∀ n, FiniteDimensional ℚ (rationalHomology X n)) ∧
    ∃ N : ℕ, ∀ n, N ≤ n → Subsingleton (rationalHomology X n)

/-- This also specifies the finite sum represented by the algebraic finsum. -/
def lefschetzSum_type : Prop :=
  let _ : Type u := ULift.{u} Unit
  let _ : Type v := ULift.{v} Unit
  ∀ (X : TopCat.{w}), IsFinitePolyhedron X →
    ∃ N : ℕ, ∀ f : X ⟶ X,
      Function.support (fun n : ℕ => (-1 : ℚ) ^ n *
        LinearMap.trace ℚ (rationalHomology X n) (rationalHomologyMap f n).hom)
          ⊆ ↑(Finset.range N) ∧
      lefschetzNumber f = ∑ n ∈ Finset.range N, (-1 : ℚ) ^ n *
        LinearMap.trace ℚ (rationalHomology X n) (rationalHomologyMap f n).hom

/-- The full fixed point theorem, for every continuous self-map of every finite
polyhedron, with the Lefschetz number on singular rational homology. -/
def fixedPoint_type : Prop :=
  let _ : Type u := ULift.{u} Unit
  let _ : Type v := ULift.{v} Unit
  ∀ (X : TopCat.{w}), IsFinitePolyhedron X →
    ∀ f : X ⟶ X, lefschetzNumber f ≠ 0 → ∃ x : X, f x = x

end P202Specs.LefschetzFixedPoint
