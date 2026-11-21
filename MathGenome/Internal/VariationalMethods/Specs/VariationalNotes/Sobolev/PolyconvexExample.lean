import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.PolyconvexExistence
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! Independent statements for the unnumbered example in paper.tex 4179–4188.
The matrix norm is Frobenius; the energy is the signed extended integral from
`Spaces`, not the totalized Bochner integral. The last assertion supplies a
specific compactly supported map in a planar disk for every 2 < p < 4. -/
noncomputable section
open MeasureTheory TopologicalSpace Set
namespace VariationalNotes.Sobolev.PolyconvexExample
open Minors

/-- The example's exact density. -/
def integrand (p γ : ℝ) (Z : Gradient 2 2) : ℝ :=
  ‖Z‖ ^ p + (Polyconvex.determinant Z - γ) ^ 2

/-- The displayed representation uses an independent determinant coordinate. -/
def matrixRepresentation (p γ : ℝ) (z : Gradient 2 2 × ℝ) : ℝ :=
  ‖z.1‖ ^ p + (z.2 - γ) ^ 2

def determinantIndex : AllIndex 2 2 :=
  ⟨⟨1, by norm_num⟩, (⟨id, strictMono_id⟩, ⟨id, strictMono_id⟩)⟩

/-- The same representation in the canonical space of all independent minors. -/
def minorRepresentation (p γ : ℝ) (_x : Domain 2) (_s : Vector 2)
    (z : Coordinates 2 2) : ℝ :=
  ‖firstMatrix (by decide) (by decide) z‖ ^ p + (z determinantIndex - γ) ^ 2

/-- The actual real matrix tI in the canonical flattened entry convention. -/
def scalarIdentity (t : ℝ) : Gradient 2 2 :=
  WithLp.toLp 2 (fun ij => if ij.1 = ij.2 then t else 0)

/-- A bounded planar disk containing the compact support of the singular example. -/
def disk : Opens (Domain 2) := ⟨Metric.ball 0 2, Metric.isOpen_ball⟩

/-- A fixed smooth cutoff, equal to one on the half-unit disk and zero
outside the unit disk. Its radii fully specify the standard library bump. -/
def radialCutoff : ContDiffBump (0 : Domain 2) :=
  ⟨1 / 2, 1, by norm_num, by norm_num⟩

/-- A concrete compactly cut-off radial map; in particular its value at zero
is zero. On the half-unit disk it is exactly |x|^(-1/2) x. -/
def radialMap (x : Domain 2) : Vector 2 :=
  (radialCutoff x * ‖x‖ ^ (-(1 / 2 : ℝ))) • x

namespace Expected

def Representation : Prop := ∀ (p γ : ℝ), 2 < p → 0 < γ →
  (∀ Z, integrand p γ Z = matrixRepresentation p γ (Z, Polyconvex.determinant Z)) ∧
  ConvexOn ℝ univ (matrixRepresentation p γ) ∧
  IsPolyconvexRepresentation (fun _ _ Z => integrand p γ Z) (minorRepresentation p γ)

def Coercivity : Prop := ∀ (p γ : ℝ),
  (∀ Z, ‖Z‖ ^ p ≤ integrand p γ Z) ∧
  (∀ (Z : Gradient 2 2) (t : ℝ), ‖Z‖ ^ p ≤ matrixRepresentation p γ (Z,t)) ∧
  (∀ x s z, ‖firstMatrix (by decide) (by decide) z‖ ^ p ≤
    minorRepresentation p γ x s z)

def LineBehavior : Prop := ∀ (p γ : ℝ), 2 < p → 0 < γ →
  (∀ t, integrand p γ (scalarIdentity t) - integrand p γ 0 =
    (2 : ℝ) ^ (p / 2) * |t| ^ p - 2 * γ * t ^ 2 + t ^ 4) ∧
  (∀ t, integrand p γ (scalarIdentity (-t)) = integrand p γ (scalarIdentity t)) ∧
  (∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < |t| → |t| < δ →
    integrand p γ (scalarIdentity t) - integrand p γ 0 < 0) ∧
  ¬ ConvexOn ℝ univ (integrand p γ)

def ZeroCompetitor : Prop := ∀ (Ω : Opens (Domain 2)) (p : Exponent) (γ : ℝ),
  Bornology.IsBounded (Ω : Set (Domain 2)) →
  (0 : W1p Ω 2 p) ∈ affineClass Ω 2 p 0 ∧
  energy Ω 2 p (fun _ _ Z => integrand p.real γ Z) 0 =
    ((γ ^ 2 * (volume (Ω : Set (Domain 2))).toReal : ℝ) : EReal)

/-- Conditional use of the polyconvex theorem gives finite attainment on every
bounded open set, hence also on every bounded Lipschitz open set. -/
def Attainment : Prop := ∀ (Ω : Opens (Domain 2)) (p : Exponent) (γ : ℝ),
  Bornology.IsBounded (Ω : Set (Domain 2)) → 2 < p.real → 0 < γ →
  Polyconvex.FiniteMinimum Ω p 0 (fun _ _ Z => integrand p.real γ Z)

/-- This is a Sobolev map with genuine weak derivatives in the adopted graph
space, lying in the closure of smooth compactly supported maps. Its determinant
is not square integrable, and its actual extended energy is positive infinity. -/
def InfiniteCompetitor : Prop := ∀ (p : Exponent) (γ : ℝ),
  2 < p.real → p.real < 4 → 0 < γ →
  ∃ u : W1p disk 2 p, u ∈ zeroSubmodule disk 2 p ∧
    (value disk 2 p u : Domain 2 → Vector 2) =ᵐ[domainMeasure disk] radialMap ∧
    ¬ MemLp (fun x => Polyconvex.determinant (gradient disk 2 p u x)) 2
      (domainMeasure disk) ∧
    energy disk 2 p (fun _ _ Z => integrand p.real γ Z) u = ⊤

end Expected
end VariationalNotes.Sobolev.PolyconvexExample
