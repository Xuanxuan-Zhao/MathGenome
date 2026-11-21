import MathGenome.Internal.ExtremalOptimization.Specs.P205.Matroids.Models
import Mathlib.Analysis.Convex.Extreme

/-! Independent statements for paper.tex, Theorem 9.3 (W45).
The coordinates are indexed by the actual ground, and only that ground is finite.
The convex hull is the ordinary convex hull, without taking a closure. -/
namespace Specs.P205.Matroids
open _root_.P205.Matroids
universe u

def BasePolytopeEquality : Prop :=
  ∀ {α : Type u} (M : Matroid α) [M.Finite],
    convexHull ℝ (basisIndicatorsValue M) = baseInequalitiesValue M

def BasePolytopeExtremePoints : Prop :=
  ∀ {α : Type u} (M : Matroid α) [M.Finite],
    (baseInequalitiesValue M).extremePoints ℝ = basisIndicatorsValue M

def BasePolytopeZeroOne : Prop :=
  ∀ {α : Type u} (M : Matroid α) [M.Finite] (x : Coordinates M),
    x ∈ (baseInequalitiesValue M).extremePoints ℝ →
    ∀ e : M.E, x e = 0 ∨ x e = 1

def BasePolytopeIntegral : Prop :=
  ∀ {α : Type u} (M : Matroid α) [M.Finite] (x : Coordinates M),
    x ∈ (baseInequalitiesValue M).extremePoints ℝ →
    ∃ z : M.E → ℤ, ∀ e, x e = (z e : ℝ)

end Specs.P205.Matroids
