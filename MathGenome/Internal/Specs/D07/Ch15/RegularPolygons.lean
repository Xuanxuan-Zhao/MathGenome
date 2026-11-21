import MathGenome.Internal.Specs.D07.Ch15.ConstructibleDefinition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-! The ordinary unit data and actual regular polygon vertices. A nonzero
complex scale permits every positive radius and every orientation; the center
and scale in the existence predicate are not assumed constructible. -/
namespace D07.Ch15.RegularPolygonGeometry
open D07.Ch15.StraightedgeCompass

def unitData : InitialData where
  points := {origin, unitPoint}
  finite_points := Set.toFinite _
  origin_mem := Set.mem_insert _ _
  unitPoint_mem := Set.mem_insert_of_mem _ rfl

noncomputable def root (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

def point (z : ℂ) : Point := (z.re, z.im)

noncomputable def vertex (n : ℕ) (center scale : ℂ) (j : ℕ) : Point :=
  point (center + scale * root n ^ j)

/-- Every vertex is obtained in a single finite permitted construction. -/
def ConstructibleRegularPolygon (n : ℕ) : Prop :=
  ∃ center scale : ℂ, scale ≠ 0 ∧
    ∃ S : Set Point, Construction unitData S ∧
      ∀ j : Fin n, vertex n center scale j.val ∈ S

end D07.Ch15.RegularPolygonGeometry

namespace Specs.D07.Ch15.RegularPolygons
open D07.Ch15.StraightedgeCompass D07.Ch15.RegularPolygonGeometry
open Specs.D07.Ch15.ConstructibleDefinition
open scoped BigOperators

def Normalization : Prop := ∀ n : ℕ, 3 ≤ n →
  (ConstructibleRegularPolygon n ↔ isConstructibleValue unitData (point (root n)))

def PrimitiveRootCriterion : Prop := ∀ (n : ℕ), 0 < n →
  ∀ ζ : ℂ, IsPrimitiveRoot ζ n →
    (isConstructibleValue unitData (point ζ) ↔ ∃ k : ℕ, Nat.totient n = 2 ^ k)

def TotientCriterion : Prop := ∀ n : ℕ, 3 ≤ n →
  (ConstructibleRegularPolygon n ↔ ∃ k : ℕ, Nat.totient n = 2 ^ k)

def FermatPrimeCriterion : Prop := ∀ n : ℕ, 3 ≤ n →
  (ConstructibleRegularPolygon n ↔
    ∃ (a : ℕ) (s : Finset ℕ), n = 2 ^ a * ∏ p ∈ s, p ∧
      ∀ p ∈ s, Nat.Prime p ∧ Odd p ∧ ∃ b : ℕ, p = 1 + 2 ^ (2 ^ b))

end Specs.D07.Ch15.RegularPolygons
