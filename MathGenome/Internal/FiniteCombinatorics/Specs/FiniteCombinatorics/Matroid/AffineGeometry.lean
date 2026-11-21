import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.VectorRepresentation
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.ParallelClasses
import Mathlib.Data.Fintype.Card

/-! W75: affine points in homogeneous coordinates. The product `K × (Fin d → K)`
is the coordinate space with one distinguished first coordinate and d further
coordinates. Simplicity is stated explicitly as independence of every singleton
and every pair of distinct points. -/
namespace FiniteCombinatorics.Matroid.Expected
open Set Submodule
universe u

/-- The normalized homogeneous column of an affine point. -/
def affineColumn (K : Type u) [Field K] (d : ℕ) (x : Fin d → K) :
    K × (Fin d → K) := (1, x)

/-- All affine points, retaining the point itself as its column index. -/
def affineMatroid (K : Type u) [Field K] [Fintype K] (d : ℕ) :
    _root_.Matroid (Fin d → K) :=
  vectorMatroid K univ (finite_univ) (affineColumn K d)

instance (K : Type u) [Field K] [Fintype K] (d : ℕ) :
    (affineMatroid K d).Finite := by unfold affineMatroid; infer_instance

/-- A line through x with direction a; the line theorems require a ≠ 0. -/
def affineLine {K : Type u} [Field K] {d : ℕ} (x a : Fin d → K) : Set (Fin d → K) :=
  range (fun t : K => x + t • a)

def affineColumnType := ∀ (K : Type u) [Field K] (d : ℕ),
  (Fin d → K) → K × (Fin d → K)
def affineMatroidType := ∀ (K : Type u) [Field K] [Fintype K] (d : ℕ),
  _root_.Matroid (Fin d → K)
def affineLineType := ∀ {K : Type u} [Field K] {d : ℕ},
  (Fin d → K) → (Fin d → K) → Set (Fin d → K)

def affineGround : Prop := ∀ (K : Type u) [Field K] [Fintype K] (d : ℕ),
  (affineMatroid K d).E = univ

def affineFinite : Prop := ∀ (K : Type u) [Field K] [Fintype K] (d : ℕ),
  (affineMatroid K d).Finite

def affineIndep : Prop := ∀ (K : Type u) [Field K] [Fintype K] (d : ℕ)
  (I : Set (Fin d → K)),
  (affineMatroid K d).Indep I ↔ LinearIndepOn K (affineColumn K d) I

def affineSimple : Prop := ∀ (K : Type u) [Field K] [Fintype K] (d : ℕ),
  (∀ x : Fin d → K, (affineMatroid K d).Indep {x}) ∧
  ∀ x y : Fin d → K, x ≠ y → (affineMatroid K d).Indep {x, y}

/-- Simplicity in the paper's convention: no loops and no distinct parallel points. -/
def affineNoLoopsParallel : Prop := ∀ (K : Type u) [Field K] [Fintype K] (d : ℕ),
  (∀ x : Fin d → K, ¬ (affineMatroid K d).IsLoop x) ∧
  ∀ x y : Fin d → K, x ≠ y → ¬ ParallelRelated (affineMatroid K d) x y

def affineSpan : Prop := ∀ (K : Type u) [Field K] (d : ℕ),
  span K (range (affineColumn K d)) = ⊤

def affineRank : Prop := ∀ (K : Type u) [Field K] [Fintype K] (d : ℕ),
  rank (affineMatroid K d) (affineMatroid K d).E = ((d + 1 : ℕ) : ℤ)

def affinePointCount : Prop := ∀ (K : Type u) [Field K] [Fintype K] (d : ℕ),
  (affineMatroid K d).E.ncard = Fintype.card K ^ d

def affineLineInjective : Prop := ∀ (K : Type u) [Field K] (d : ℕ)
  (x a : Fin d → K), a ≠ 0 → Function.Injective (fun t : K => x + t • a)

def affineLineCard : Prop := ∀ (K : Type u) [Field K] [Fintype K] (d : ℕ)
  (x a : Fin d → K), a ≠ 0 → (affineLine x a).ncard = Fintype.card K

/-- Equality of the normalized columns on the line and the first-coordinate-one
slice of its homogeneous span (two-dimensional for nonzero direction).
This equality holds even for zero direction. -/
def affineLineNormalized : Prop := ∀ (K : Type u) [Field K] (d : ℕ)
  (x a : Fin d → K),
  affineColumn K d '' affineLine x a =
    {v | v.1 = 1 ∧ v ∈ span K {affineColumn K d x, (0, a)}}

def affineDimensionZero : Prop := ∀ (K : Type u) [Field K] [Fintype K],
  (affineMatroid K 0).E = {0} ∧
  rank (affineMatroid K 0) (affineMatroid K 0).E = 1

end FiniteCombinatorics.Matroid.Expected
