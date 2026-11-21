import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch22.ProjectivePlaneTopology
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch22.HalfPeriodValues
import Mathlib.Topology.OpenPartialHomeomorph.Composition

/-! Independent interface for the literal projective cubic and its finite charts
(paper.tex:3943–3952,3971–3981). Connectedness and the point at infinity are
intentionally separate downstream obligations. -/
noncomputable section
open Set

namespace D12Complex.CubicFiniteCharts
open ProjectivePlaneTopology

/-- Homogeneous equation, in coordinate order Z,X,Y. -/
def homogeneousEquation (g₂ g₃ : ℂ) (v : Fin 3 → ℂ) : ℂ :=
  v 2 ^ 2 * v 0 - 4 * v 1 ^ 3 + g₂ * v 1 * v 0 ^ 2 + g₃ * v 0 ^ 3

/-- Membership uses the actual scalar-orbit quotient, with no chosen section. -/
def OnCubic (g₂ g₃ : ℂ) (p : ComplexProjectivePlane) : Prop :=
  ∃ v : HomogeneousVector, projection v = p ∧ homogeneousEquation g₂ g₃ v.val = 0

/-- The curve has the inherited projective topology. -/
def Cubic (g₂ g₃ : ℂ) := {p : ComplexProjectivePlane // OnCubic g₂ g₃ p}
instance (g₂ g₃ : ℂ) : TopologicalSpace (Cubic g₂ g₃) :=
  inferInstanceAs (TopologicalSpace {p : ComplexProjectivePlane // OnCubic g₂ g₃ p})

def q (g₂ g₃ x : ℂ) : ℂ := 4 * x ^ 3 - g₂ * x - g₃

def finiteX (p : ComplexProjectivePlane) : ℂ := coordinateRatio 0 1 p
def finiteY (p : ComplexProjectivePlane) : ℂ := coordinateRatio 0 2 p

def affinePoint (x y : ℂ) : ComplexProjectivePlane := affineParam 0 ![x,y]

def finitePatch (g₂ g₃ : ℂ) : Set (Cubic g₂ g₃) :=
  {p | p.val ∈ coordinatePatch 0}

/-- `true` selects x as coordinate, `false` selects y. -/
def coordinate (axis : Bool) (p : ComplexProjectivePlane) : ℂ :=
  if axis then finiteX p else finiteY p

/-- An actual open partial homeomorphism whose inverse has holomorphic ambient
coordinates. This does not assert connectedness of the whole cubic. -/
def IsFiniteChart (g₂ g₃ : ℂ) (axis : Bool)
    (e : OpenPartialHomeomorph (Cubic g₂ g₃) ℂ) : Prop :=
  e.source ⊆ finitePatch g₂ g₃ ∧
  (∀ p ∈ e.source, e p = coordinate axis p.val) ∧
  D12Complex.HolomorphicOn e.target (fun z => finiteX (e.symm z).val) ∧
  D12Complex.HolomorphicOn e.target (fun z => finiteY (e.symm z).val)

end D12Complex.CubicFiniteCharts

namespace Specs.D12Complex.Ch22.CubicFiniteCharts
open _root_.D12Complex _root_.D12Complex.CubicFiniteCharts
open _root_.D12Complex.ProjectivePlaneTopology
open WeierstrassEquations (g₂ g₃)
open Specs.D12Complex.Ch22.HalfPeriodValues (branchValue)

def homogeneousEquation_type := ℂ → ℂ → (Fin 3 → ℂ) → ℂ
def homogeneousEquation_value : homogeneousEquation_type := fun g₂ g₃ v =>
  v 2 ^ 2 * v 0 - 4 * v 1 ^ 3 + g₂ * v 1 * v 0 ^ 2 + g₃ * v 0 ^ 3
def OnCubic_type := ℂ → ℂ → ComplexProjectivePlane → Prop
def OnCubic_value : OnCubic_type := fun g₂ g₃ p =>
  ∃ v : HomogeneousVector, projection v = p ∧ homogeneousEquation g₂ g₃ v.val = 0
def Cubic_type := ℂ → ℂ → Type
def Cubic_value : Cubic_type := fun g₂ g₃ =>
  {p : ComplexProjectivePlane // OnCubic g₂ g₃ p}

def q_type := ℂ → ℂ → ℂ → ℂ
def q_value : q_type := fun g₂ g₃ x => 4 * x ^ 3 - g₂ * x - g₃
def finiteX_type := ComplexProjectivePlane → ℂ
def finiteX_value : finiteX_type := coordinateRatio 0 1
def finiteY_type := ComplexProjectivePlane → ℂ
def finiteY_value : finiteY_type := coordinateRatio 0 2
def affinePoint_type := ℂ → ℂ → ComplexProjectivePlane
def affinePoint_value : affinePoint_type := fun x y => affineParam 0 ![x,y]
def finitePatch_type := (g₂ g₃ : ℂ) → Set (Cubic g₂ g₃)
def finitePatch_value : finitePatch_type := fun _ _ => {p | p.val ∈ coordinatePatch 0}
def coordinate_type := Bool → ComplexProjectivePlane → ℂ
def coordinate_value : coordinate_type := fun axis p => if axis then finiteX p else finiteY p
def IsFiniteChart_type := (g₂ g₃ : ℂ) → Bool →
  OpenPartialHomeomorph (Cubic g₂ g₃) ℂ → Prop
def IsFiniteChart_value : IsFiniteChart_type := fun g₂ g₃ axis e =>
  e.source ⊆ finitePatch g₂ g₃ ∧
  (∀ p ∈ e.source, e p = coordinate axis p.val) ∧
  HolomorphicOn e.target (fun z => finiteX (e.symm z).val) ∧
  HolomorphicOn e.target (fun z => finiteY (e.symm z).val)

def hasDerivAt_q_type : Prop := ∀ G H a : ℂ,
  HasDerivAt (q G H) (12 * a ^ 2 - G) a

def well_defined_type : Prop := ∀ g₂ g₃ v,
  OnCubic g₂ g₃ (projection v) ↔ homogeneousEquation g₂ g₃ v.val = 0

def closed_type : Prop := ∀ g₂ g₃, IsClosed {p | OnCubic g₂ g₃ p}

def topology_type : Prop := ∀ g₂ g₃ : ℂ,
  CompactSpace (Cubic g₂ g₃) ∧ T2Space (Cubic g₂ g₃) ∧
    SecondCountableTopology (Cubic g₂ g₃)

def affine_equation_type : Prop := ∀ g₂ g₃ p,
  p ∈ coordinatePatch 0 →
  (OnCubic g₂ g₃ p ↔ finiteY p ^ 2 = q g₂ g₃ (finiteX p))

def nonsingular_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im → ∀ x y : ℂ,
    y ^ 2 = q (g₂ ω₁ ω₂) (g₃ ω₁ ω₂) x →
    y ≠ 0 ∨ 12 * x ^ 2 - g₂ ω₁ ω₂ ≠ 0

def branch_simple_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
    (∀ x, q (g₂ ω₁ ω₂) (g₃ ω₁ ω₂) x = 0 ↔
      ∃ i, x = branchValue ω₁ ω₂ i) ∧
    ∀ i, 12 * branchValue ω₁ ω₂ i ^ 2 - g₂ ω₁ ω₂ ≠ 0

/-- Explicit x-coordinate inverse parametrization near every point with y≠0. -/
def x_chart_type : Prop := ∀ g₂ g₃ a b : ℂ,
  b ^ 2 = q g₂ g₃ a → b ≠ 0 →
  ∃ (U V : Set ℂ) (f : ℂ → ℂ)
    (e : OpenPartialHomeomorph (Cubic g₂ g₃) ℂ),
    IsOpen U ∧ a ∈ U ∧ IsOpen V ∧ b ∈ V ∧
    HolomorphicOn U f ∧ f a = b ∧ MapsTo f U V ∧
    (∀ x ∈ U, ∀ y ∈ V, y ^ 2 = q g₂ g₃ x ↔ y = f x) ∧
    IsFiniteChart g₂ g₃ true e ∧ e.target = U ∧
    e.source = {p | p ∈ finitePatch g₂ g₃ ∧ finiteX p.val ∈ U ∧ finiteY p.val ∈ V} ∧
    (∀ t ∈ U, (e.symm t).val = affinePoint t (f t))

/-- Explicit y-coordinate inverse parametrization at every simple branch root. -/
def y_chart_type : Prop := ∀ g₂ g₃ a : ℂ,
  q g₂ g₃ a = 0 → 12 * a ^ 2 - g₂ ≠ 0 →
  ∃ (U V : Set ℂ) (f : ℂ → ℂ)
    (e : OpenPartialHomeomorph (Cubic g₂ g₃) ℂ),
    IsOpen U ∧ (0 : ℂ) ∈ U ∧ IsOpen V ∧ a ∈ V ∧
    HolomorphicOn U f ∧ f 0 = a ∧ MapsTo f U V ∧
    (∀ y ∈ U, ∀ x ∈ V, y ^ 2 = q g₂ g₃ x ↔ x = f y) ∧
    IsFiniteChart g₂ g₃ false e ∧ e.target = U ∧
    e.source = {p | p ∈ finitePatch g₂ g₃ ∧ finiteY p.val ∈ U ∧ finiteX p.val ∈ V} ∧
    (∀ t ∈ U, (e.symm t).val = affinePoint (f t) t)

def finite_charts_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
    ∀ p : Cubic (g₂ ω₁ ω₂) (g₃ ω₁ ω₂), p ∈ finitePatch _ _ →
    ∃ e : OpenPartialHomeomorph (Cubic (g₂ ω₁ ω₂) (g₃ ω₁ ω₂)) ℂ,
      p ∈ e.source ∧ IsFiniteChart _ _ (if finiteY p.val = 0 then false else true) e

/-- Compatibility uses the actual overlap and the canonical weak holomorphy. -/
def transitions_type : Prop :=
  ∀ g₂ g₃ axis₁ axis₂ (e f : OpenPartialHomeomorph (Cubic g₂ g₃) ℂ),
    IsFiniteChart g₂ g₃ axis₁ e → IsFiniteChart g₂ g₃ axis₂ f →
    let t := e.symm.trans f
    BiholomorphicPair t.source t.target t t.symm

end Specs.D12Complex.Ch22.CubicFiniteCharts
