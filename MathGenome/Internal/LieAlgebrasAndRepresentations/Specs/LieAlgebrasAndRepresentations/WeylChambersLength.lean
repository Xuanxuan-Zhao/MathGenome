import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SimpleRoots
import Mathlib.Topology.Connected.Basic
import Mathlib.Data.Set.Card
import Mathlib.Order.Lattice.Nat
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! LA-E03-Length. Chambers are actual connected components of the complement
of all root hyperplanes. Length is the minimum length of a word in the given
simple reflections, independently of the inversion count. -/
noncomputable section
namespace LieAlgebrasAndRepresentations
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def rootHyperplaneComplement (R : Set E) : Set E := {x | RootRegular R x}

def simpleChamber (R : Set E) (v : E) : Set E :=
  {x | ∀ a ∈ simpleRoots R v, 0 < inner ℝ x a}

def IsWeylChamber (R : Set E) (C : Set E) : Prop :=
  ∃ x ∈ rootHyperplaneComplement R, C = connectedComponentIn (rootHyperplaneComplement R) x

def weylWordProduct {R : Set E} {v : E} (l : List (simpleRoots R v)) : E ≃ₗ[ℝ] E :=
  (l.map (fun a => rootReflectionEquiv (a : E))).prod

def weylWordLength (R : Set E) (v : E) (w : rootWeylGroup R) : ℕ :=
  sInf {n | ∃ l : List (simpleRoots R v), l.length = n ∧ weylWordProduct l = w.val}

def inversionRoots (R : Set E) (v : E) (w : E ≃ₗ[ℝ] E) : Set E :=
  {a | a ∈ positiveRoots R v ∧ inner ℝ v (w a) < 0}

namespace WeylChamberLengthSpecs
universe u

def chamberType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
  ∀ (R : Set E), IsRootSystem R → ∀ v, RootRegular R v →
    simpleChamber R v = connectedComponentIn (rootHyperplaneComplement R) v

def actionType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
  ∀ (R : Set E), IsRootSystem R → ∀ (w : rootWeylGroup R) C,
    IsWeylChamber R C → IsWeylChamber R (w.val '' C)

def simplyTransitiveType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
  ∀ (R : Set E), IsRootSystem R → ∀ v, RootRegular R v →
  ∀ C D, IsWeylChamber R C → IsWeylChamber R D →
    ∃! w : rootWeylGroup R, w.val '' C = D

def shortestWordType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
  ∀ (R : Set E), IsRootSystem R → ∀ v, RootRegular R v →
  ∀ w : rootWeylGroup R, ∃ l : List (simpleRoots R v),
    weylWordProduct l = w.val ∧ l.length = weylWordLength R v w ∧
    ∀ k : List (simpleRoots R v), weylWordProduct k = w.val → l.length ≤ k.length

def lengthType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
  ∀ (R : Set E), IsRootSystem R → ∀ v, RootRegular R v →
  ∀ w : rootWeylGroup R,
    weylWordLength R v w = (inversionRoots R v w.val).ncard

end WeylChamberLengthSpecs
end LieAlgebrasAndRepresentations
