import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch22.SecantAddition
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch22.TangentAddition
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch22.ExceptionalAddition
import Mathlib.Algebra.Group.TransferInstance

/-! The full chord–tangent group law, paper.tex:4070–4121.
The cubic and torus are the actual shared projective curve and quotient group.
The equivalence is quantified, with existence and uniqueness proved below;
compatibility requires that it is literally Φ, not an arbitrary parametrization.
The affine relation is independent of any group operation. The intersection
geometry specification records why its formulas are the reflected third
intersections, including coincident intersections with their multiplicities. -/
noncomputable section
open scoped Classical

namespace D12Complex.ChordTangentGroup
open TorusSurface CubicFiniteCharts CubicInfinityChart ExceptionalAddition
open Specs.D12Complex.Ch22.WeierstrassEquations (g₂ g₃)

abbrev E (ω₁ ω₂ : ℂ) := Cubic (g₂ ω₁ ω₂) (g₃ ω₁ ω₂)


end D12Complex.ChordTangentGroup

namespace Specs.D12Complex.Ch22.ChordTangentGroup
open _root_.D12Complex _root_.D12Complex.ChordTangentGroup
open _root_.D12Complex.TorusSurface _root_.D12Complex.CubicFiniteCharts
open _root_.D12Complex.CubicInfinityChart _root_.D12Complex.ExceptionalAddition
open _root_.D12Complex.TorusCubicLocalMap (phi)
open _root_.D12Complex.ProjectivePlaneTopology (HomogeneousVector)
open WeierstrassEquations (g₂ g₃)

-- Independent expected values for the new definitions.
def secantCoordinates_type := ℂ → ℂ → ℂ → ℂ → ℂ × ℂ
def secantCoordinates_value : secantCoordinates_type := fun x y u v =>
  let m := (y-v)/(x-u)
  let a := -x-u+m^2/4
  (a, -y+m*(x-a))
def tangentCoordinates_type := ℂ → ℂ → ℂ → ℂ × ℂ
def tangentCoordinates_value : tangentCoordinates_type := fun G x y =>
  let m := (12*x^2-G)/(2*y)
  let a := -2*x+m^2/4
  (a, -y+m*(x-a))
def GeometricSum_type := {ω₁ ω₂ : ℂ} → E ω₁ ω₂ → E ω₁ ω₂ → E ω₁ ω₂ → Prop
def GeometricSum_value : GeometricSum_type := fun {ω₁ ω₂} P Q R =>
  (P.val = O ∧ R = Q) ∨
  (Q.val = O ∧ R = P) ∨
  (∃ x y : ℂ, P.val = affinePoint x y ∧ Q.val = affinePoint x (-y) ∧ R.val = O) ∨
  (∃ x y u v : ℂ, P.val = affinePoint x y ∧ Q.val = affinePoint u v ∧ x ≠ u ∧
    R.val = affinePoint (secantCoordinates_value x y u v).1 (secantCoordinates_value x y u v).2) ∨
  (∃ x y : ℂ, P.val = affinePoint x y ∧ Q = P ∧ y ≠ 0 ∧
    R.val = affinePoint (tangentCoordinates_value (g₂ ω₁ ω₂) x y).1
      (tangentCoordinates_value (g₂ ω₁ ω₂) x y).2)
def groupStructure_type := {ω₁ ω₂ : ℂ} → (Torus ω₁ ω₂ ≃ E ω₁ ω₂) → AddCommGroup (E ω₁ ω₂)
def groupStructure_value : groupStructure_type := fun e => e.symm.addCommGroup

/-- There is exactly one equivalence with the actual Φ values. -/
def equivalence_exists_unique_type : Prop := ∀ ω₁ ω₂ : ℂ,
  ω₁ ≠ 0 → 0 < (ω₂/ω₁).im →
  ∃! e : Torus ω₁ ω₂ ≃ E ω₁ ω₂, ∀ t, (e t).val = phi ω₁ ω₂ t

/-- The group operations agree with the previously shared transport definitions;
all abelian group axioms are consequences of the torus group. -/
def group_laws_type : Prop := ∀ ω₁ ω₂ : ℂ, ∀ e : Torus ω₁ ω₂ ≃ E ω₁ ω₂,
  letI := groupStructure_value e
  (∀ P Q : E ω₁ ω₂, P+Q = transportedAdd e P Q) ∧
  (0 : E ω₁ ω₂) = e 0 ∧
  (∀ P : E ω₁ ω₂, -P = transportedNeg e P) ∧
  (∀ P Q R : E ω₁ ω₂, (P+Q)+R = P+(Q+R)) ∧
  (∀ P Q : E ω₁ ω₂, P+Q = Q+P) ∧
  ∀ P : E ω₁ ω₂, 0+P=P ∧ P+0=P ∧ -P+P=0 ∧ P+ -P=0

def group_isomorphism_type : Prop := ∀ ω₁ ω₂ : ℂ,
  ∀ e : Torus ω₁ ω₂ ≃ E ω₁ ω₂,
  letI := groupStructure_value e
  ∃ F : Torus ω₁ ω₂ ≃+ E ω₁ ω₂, F.toEquiv = e

/-- All five geometric rules, for all pairs of literal cubic points. -/
def geometric_addition_type : Prop := ∀ ω₁ ω₂ : ℂ,
  ω₁ ≠ 0 → 0 < (ω₂/ω₁).im →
  ∀ e : Torus ω₁ ω₂ ≃ E ω₁ ω₂, (∀ t, (e t).val = phi ω₁ ω₂ t) →
  ∀ P Q R : E ω₁ ω₂, GeometricSum_value P Q R ↔ R = transportedAdd e P Q

def geometric_total_unique_type : Prop := ∀ ω₁ ω₂ : ℂ,
  ω₁ ≠ 0 → 0 < (ω₂/ω₁).im →
  ∀ P Q : E ω₁ ω₂, ∃! R : E ω₁ ω₂, GeometricSum_value P Q R

/-- Coordinates [Z:X:Y] ↦ [Z:X:−Y], for every homogeneous representative. -/
def inversion_homogeneous_type : Prop := ∀ ω₁ ω₂ : ℂ,
  ω₁ ≠ 0 → 0 < (ω₂/ω₁).im →
  ∀ e : Torus ω₁ ω₂ ≃ E ω₁ ω₂, (∀ t, (e t).val = phi ω₁ ω₂ t) →
  ∀ (P : E ω₁ ω₂) (v : HomogeneousVector),
    ProjectivePlaneTopology.projection v = P.val →
    ∃ hv : (![v.val 0,v.val 1,-v.val 2] : Fin 3 → ℂ) ≠ 0,
      (transportedNeg e P).val = ProjectivePlaneTopology.projection ⟨_,hv⟩

/-- Identity O, inverses, and the three named nonzero half-period cases. -/
def exceptional_rules_type : Prop :=
  ExceptionalAddition.identity_type ∧ ExceptionalAddition.inverse_finite_type ∧
  ExceptionalAddition.opposites_type ∧ ExceptionalAddition.half_period_type

/-- Complete secant and tangent intersection geometry. The line pullbacks are
actual meromorphic functions. Their local orders include repeated third points
and flexes. Vertical and infinity polynomials are restrictions of the literal
homogeneous equation, and their multiplicities are asserted separately. -/
def intersection_geometry_type : Prop :=
  SecantAddition.secant_intersections_type ∧
  TangentAddition.projective_line_type ∧ TangentAddition.tangent_slope_type ∧
  TangentAddition.tangent_intersections_type ∧ TangentAddition.tangent_polynomial_type ∧
  TangentAddition.tangent_doubling_type ∧ TangentAddition.tangent_projective_intersections_type ∧
  ExceptionalAddition.tangent_differential_type ∧ ExceptionalAddition.line_restrictions_type ∧
  ExceptionalAddition.vertical_intersections_type ∧ ExceptionalAddition.vertical_multiplicities_type ∧
  ExceptionalAddition.vertical_tangent_type ∧ ExceptionalAddition.line_through_origin_type ∧
  ExceptionalAddition.infinity_tangent_type

/-- Nonzero finite denominator, with finiteness of z+w as a conclusion. -/
def addition_formula_type : Prop := SecantAddition.addition_formula_type

/-- Equal punctured meromorphic germs at all exceptional arguments, in both variables. -/
def meromorphic_identity_type : Prop := SecantAddition.meromorphic_identity_type

/-- Φ itself, with identity O and the verified geometric law, is an isomorphism. -/
def chord_tangent_group_type : Prop := ∀ ω₁ ω₂ : ℂ,
  ω₁ ≠ 0 → 0 < (ω₂/ω₁).im →
  ∃ e : Torus ω₁ ω₂ ≃ E ω₁ ω₂,
    (∀ t, (e t).val = phi ω₁ ω₂ t) ∧
    letI := groupStructure_value e
    (0 : E ω₁ ω₂).val = O ∧
    (∃ F : Torus ω₁ ω₂ ≃+ E ω₁ ω₂,
      F.toEquiv = e ∧ ∀ t, (F t).val = phi ω₁ ω₂ t) ∧
    (∀ P Q R : E ω₁ ω₂, GeometricSum_value P Q R ↔ R=P+Q) ∧
    ∀ (P : E ω₁ ω₂) (v : HomogeneousVector),
      ProjectivePlaneTopology.projection v = P.val →
      ∃ hv : (![v.val 0,v.val 1,-v.val 2] : Fin 3 → ℂ) ≠ 0,
        (-P).val = ProjectivePlaneTopology.projection ⟨_,hv⟩

end Specs.D12Complex.Ch22.ChordTangentGroup
