import MathGenome.Internal.Specs.D07.Ch15.ConstructibleDefinition
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Analysis.Real.Sqrt

/-! Doubling the unit cube, paper.tex:4544–4551.
The initial data may contain any finite collection of rational points, in
addition to the required origin and unit point. Constructibility is the
original finite history of permitted intersections. A positive side `a`
doubles unit volume exactly when `a ^ 3 = 2`.
-/
namespace Specs.D07.Ch15.DoubleCube

open Polynomial IntermediateField D07.Ch15.StraightedgeCompass
open Specs.D07.Ch15.ConstructibleDefinition

def CubePolynomialIrreducible : Prop :=
  Irreducible (X ^ 3 - C (2 : ℚ))

def CubeRootDegree : Prop :=
  ∀ a : ℝ, a ^ 3 = 2 →
    IsIntegral ℚ a ∧ minpoly ℚ a = X ^ 3 - C (2 : ℚ) ∧
      Module.finrank ℚ ℚ⟮a⟯ = 3

/-- No real solution of the volume equation is a constructible length. -/
def CubeRootNotConstructible : Prop :=
  ∀ P : InitialData,
    (∀ p ∈ P.points, ∃ x y : ℚ, p = ((x : ℝ), (y : ℝ))) →
    ∀ a : ℝ, a ^ 3 = 2 → ¬ isConstructibleRealValue P a

/-- The requested positive side of a doubled unit cube cannot be constructed
with the paper's unmarked straightedge and compass from rational unit data. -/
def NoDoubling : Prop :=
  ∀ P : InitialData,
    (∀ p ∈ P.points, ∃ x y : ℚ, p = ((x : ℝ), (y : ℝ))) →
    ¬ ∃ a : ℝ, 0 < a ∧ isConstructibleRealValue P a ∧ a ^ 3 = 2

/-- Equivalently, no segment between two constructed points has the required
side length. The distance is the nonnegative Euclidean distance, expressed
using the shared squared-distance definition. -/
def NoDoublingBySegment : Prop :=
  ∀ P : InitialData,
    (∀ p ∈ P.points, ∃ x y : ℚ, p = ((x : ℝ), (y : ℝ))) →
    ¬ ∃ p q : Point, isConstructibleValue P p ∧ isConstructibleValue P q ∧
      (Real.sqrt (squaredDistance p q)) ^ 3 = 2

end Specs.D07.Ch15.DoubleCube
