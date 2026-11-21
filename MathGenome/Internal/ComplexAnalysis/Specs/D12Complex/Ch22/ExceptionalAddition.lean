import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch22.TorusCubicBiholomorphism
import Mathlib.Algebra.Polynomial.RingDivision

/-! Exceptional chord--tangent cases, paper.tex:4111–4119.
Coordinates are the shared [Z:X:Y] projective coordinates. A line is given by
its nonzero coefficient vector (scalar multiples represent the same line).
Line/curve intersection multiplicities are the root multiplicities of the
homogeneous cubic restricted to that line in the stated affine parameters:
[1:a:t] at finite points, [s:a*s:1] at O on a vertical line, and [0:s:1]
at O on the infinity tangent. Restriction identities below connect the
polynomials to the literal homogeneous cubic; no intersection certificate is
assumed. The operation is transported along any equivalence equal to the
actual Phi. Its existence is a conclusion, and all such choices agree. -/
noncomputable section
open Set Polynomial
open scoped Classical BigOperators

namespace D12Complex.ExceptionalAddition
open ProjectivePlaneTopology CubicFiniteCharts CubicInfinityChart TorusSurface

def lineValue (L v : Fin 3 → ℂ) : ℂ := ∑ i, L i * v i

def OnLine (L : Fin 3 → ℂ) (p : ComplexProjectivePlane) : Prop :=
  ∃ v : HomogeneousVector, ProjectivePlaneTopology.projection v = p ∧ lineValue L v.val = 0

def verticalForm (a : ℂ) : Fin 3 → ℂ := ![-a,1,0]
def infinityForm : Fin 3 → ℂ := ![1,0,0]

/-- The gradient of the actual homogeneous equation, in order Z,X,Y. -/
def tangentForm (G H : ℂ) (v : Fin 3 → ℂ) : Fin 3 → ℂ :=
  ![v 2 ^ 2 + 2*G*v 1*v 0 + 3*H*v 0^2, -12*v 1^2+G*v 0^2, 2*v 2*v 0]

def verticalFinitePolynomial (G H a : ℂ) : ℂ[X] := X^2-C (q G H a)
def verticalInfinityPolynomial (G H a : ℂ) : ℂ[X] := X*(1-C (q G H a)*X^2)
def infinityTangentPolynomial : ℂ[X] := C (-4)*X^3

/-- Transported addition on the actual projective cubic. -/
def transportedAdd {ω₁ ω₂ G H : ℂ} (e : Torus ω₁ ω₂ ≃ Cubic G H)
    (P Q : Cubic G H) : Cubic G H := e (e.symm P + e.symm Q)
def transportedNeg {ω₁ ω₂ G H : ℂ} (e : Torus ω₁ ω₂ ≃ Cubic G H)
    (P : Cubic G H) : Cubic G H := e (-e.symm P)

end D12Complex.ExceptionalAddition

namespace Specs.D12Complex.Ch22.ExceptionalAddition
open _root_.D12Complex _root_.D12Complex.ExceptionalAddition
open _root_.D12Complex.ProjectivePlaneTopology _root_.D12Complex.CubicFiniteCharts
open _root_.D12Complex.CubicInfinityChart _root_.D12Complex.TorusSurface
open _root_.D12Complex.TorusCubicLocalMap (phi)
open WeierstrassEquations (g₂ g₃)
open HalfPeriodValues (halfPeriod branchValue)

def lineValue_type := (Fin 3 → ℂ) → (Fin 3 → ℂ) → ℂ
def lineValue_value : lineValue_type := fun L v => ∑ i, L i * v i

def OnLine_type := (Fin 3 → ℂ) → ComplexProjectivePlane → Prop
def OnLine_value : OnLine_type := fun L p =>
  ∃ v : HomogeneousVector, ProjectivePlaneTopology.projection v = p ∧ lineValue L v.val = 0

def verticalForm_type := ℂ → (Fin 3 → ℂ)
def verticalForm_value : verticalForm_type := fun a => ![-a,1,0]
def infinityForm_type := Fin 3 → ℂ
def infinityForm_value : infinityForm_type := ![1,0,0]
def tangentForm_type := ℂ → ℂ → (Fin 3 → ℂ) → (Fin 3 → ℂ)
def tangentForm_value : tangentForm_type := fun G H v =>
  ![v 2 ^ 2 + 2*G*v 1*v 0 + 3*H*v 0^2, -12*v 1^2+G*v 0^2, 2*v 2*v 0]
def verticalFinitePolynomial_type := ℂ → ℂ → ℂ → ℂ[X]
def verticalFinitePolynomial_value : verticalFinitePolynomial_type := fun G H a => X^2-C (q G H a)
def verticalInfinityPolynomial_type := ℂ → ℂ → ℂ → ℂ[X]
def verticalInfinityPolynomial_value : verticalInfinityPolynomial_type := fun G H a => X*(1-C (q G H a)*X^2)
def infinityTangentPolynomial_type := ℂ[X]
def infinityTangentPolynomial_value : infinityTangentPolynomial_type := C (-4)*X^3

def transportedAdd_type := {ω₁ ω₂ G H : ℂ} →
  (Torus ω₁ ω₂ ≃ Cubic G H) → Cubic G H → Cubic G H → Cubic G H
def transportedAdd_value : transportedAdd_type := fun e P Q => e (e.symm P + e.symm Q)
def transportedNeg_type := {ω₁ ω₂ G H : ℂ} →
  (Torus ω₁ ω₂ ≃ Cubic G H) → Cubic G H → Cubic G H
def transportedNeg_value : transportedNeg_type := fun e P => e (-e.symm P)

/-- The line form is the actual first differential of the homogeneous cubic. -/
def tangent_differential_type : Prop := ∀ (G H : ℂ) (v w : Fin 3 → ℂ),
  HasDerivAt (fun t : ℂ => homogeneousEquation G H (v+t • w))
    (lineValue (tangentForm G H v) w) 0

def line_restrictions_type : Prop := ∀ G H a : ℂ,
  (∀ t : ℂ, (verticalFinitePolynomial G H a).eval t = homogeneousEquation G H ![1,a,t]) ∧
  (∀ s : ℂ, (verticalInfinityPolynomial G H a).eval s = homogeneousEquation G H ![s,a*s,1]) ∧
  ∀ s : ℂ, infinityTangentPolynomial.eval s = homogeneousEquation G H ![0,s,1]

def vertical_intersections_type : Prop := ∀ G H a b : ℂ, b^2 = q G H a →
  verticalForm a ≠ 0 ∧
  (∀ s t : ℂ, homogeneousEquation G H ![s,a*s,t] = s*(t-b*s)*(t+b*s)) ∧
  ∀ p : ComplexProjectivePlane, OnCubic G H p →
    (OnLine (verticalForm a) p ↔ p = affinePoint a b ∨ p = affinePoint a (-b) ∨ p = O)

/-- The two finite roots each contribute one, even when they coincide.
The point O contributes one in its line coordinate s=Z/Y. -/
def vertical_multiplicities_type : Prop := ∀ G H a b : ℂ, b^2 = q G H a →
  (∀ c : ℂ, rootMultiplicity c (verticalFinitePolynomial G H a) =
    (if c=b then 1 else 0) + (if c=-b then 1 else 0)) ∧
  rootMultiplicity (0 : ℂ) (verticalInfinityPolynomial G H a) = 1

def vertical_tangent_type : Prop := ∀ ω₁ ω₂ : ℂ,
  ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im → ∀ a : ℂ,
  q (g₂ ω₁ ω₂) (g₃ ω₁ ω₂) a = 0 →
    ∃ k : ℂ, k ≠ 0 ∧
      tangentForm (g₂ ω₁ ω₂) (g₃ ω₁ ω₂) ![1,a,0] = k • verticalForm a ∧
      rootMultiplicity (0 : ℂ) (verticalFinitePolynomial (g₂ ω₁ ω₂) (g₃ ω₁ ω₂) a) = 2

/-- Every line through O and a finite point is the displayed vertical line. -/
def line_through_origin_type : Prop := ∀ (L : Fin 3 → ℂ) (a b : ℂ),
  L ≠ 0 → OnLine L O → OnLine L (affinePoint a b) →
    ∃ k : ℂ, k ≠ 0 ∧ L = k • verticalForm a

def infinity_tangent_type : Prop := ∀ G H : ℂ,
  tangentForm G H ![0,0,1] = infinityForm ∧ infinityForm ≠ 0 ∧
  (∀ p : ComplexProjectivePlane, OnCubic G H p → (OnLine infinityForm p ↔ p=O)) ∧
  rootMultiplicity (0 : ℂ) infinityTangentPolynomial = 3

/-- Existence prevents the universal transport statements from being vacuous. -/
def equivalence_exists_type : Prop := ∀ ω₁ ω₂ : ℂ,
  ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
  ∃ e : Torus ω₁ ω₂ ≃ Cubic (g₂ ω₁ ω₂) (g₃ ω₁ ω₂),
    ∀ t, (e t).val = phi ω₁ ω₂ t

def addition_agreement_type : Prop := ∀ ω₁ ω₂ : ℂ,
  ∀ e : Torus ω₁ ω₂ ≃ Cubic (g₂ ω₁ ω₂) (g₃ ω₁ ω₂),
  (∀ t, (e t).val = phi ω₁ ω₂ t) → ∀ t s,
    (transportedAdd e (e t) (e s)).val = phi ω₁ ω₂ (t+s)

def inverse_finite_type : Prop := ∀ ω₁ ω₂ : ℂ,
  ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
  ∀ e : Torus ω₁ ω₂ ≃ Cubic (g₂ ω₁ ω₂) (g₃ ω₁ ω₂),
  (∀ t, (e t).val = phi ω₁ ω₂ t) →
  ∀ (P : Cubic (g₂ ω₁ ω₂) (g₃ ω₁ ω₂)) (x y : ℂ), P.val = affinePoint x y →
    (transportedNeg e P).val = affinePoint x (-y) ∧
    (transportedAdd e P (transportedNeg e P)).val = O ∧
    (transportedAdd e (transportedNeg e P) P).val = O

def opposites_type : Prop := ∀ ω₁ ω₂ : ℂ,
  ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
  ∀ e : Torus ω₁ ω₂ ≃ Cubic (g₂ ω₁ ω₂) (g₃ ω₁ ω₂),
  (∀ t, (e t).val = phi ω₁ ω₂ t) →
  ∀ (P Q : Cubic (g₂ ω₁ ω₂) (g₃ ω₁ ω₂)) (x y : ℂ),
    P.val = affinePoint x y → Q.val = affinePoint x (-y) →
      (transportedAdd e P Q).val = O

def identity_type : Prop := ∀ ω₁ ω₂ : ℂ,
  ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
  ∀ e : Torus ω₁ ω₂ ≃ Cubic (g₂ ω₁ ω₂) (g₃ ω₁ ω₂),
  (∀ t, (e t).val = phi ω₁ ω₂ t) →
  ∀ (P₀ : Cubic (g₂ ω₁ ω₂) (g₃ ω₁ ω₂)), P₀.val = O →
    (∀ P, transportedAdd e P₀ P = P ∧ transportedAdd e P P₀ = P) ∧
    transportedAdd e P₀ P₀ = P₀

def half_period_type : Prop := ∀ ω₁ ω₂ : ℂ,
  ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
  ∀ e : Torus ω₁ ω₂ ≃ Cubic (g₂ ω₁ ω₂) (g₃ ω₁ ω₂),
  (∀ t, (e t).val = phi ω₁ ω₂ t) →
  (∀ (P : Cubic (g₂ ω₁ ω₂) (g₃ ω₁ ω₂)) (x : ℂ), P.val = affinePoint x 0 →
    (transportedAdd e P P).val = O ∧
      ∃ i : Fin 3, P = e (TorusSurface.projection ω₁ ω₂ (halfPeriod ω₁ ω₂ i))) ∧
  ∀ i : Fin 3,
    (e (TorusSurface.projection ω₁ ω₂ (halfPeriod ω₁ ω₂ i))).val =
      affinePoint (branchValue ω₁ ω₂ i) 0 ∧
    (transportedAdd e (e (TorusSurface.projection ω₁ ω₂ (halfPeriod ω₁ ω₂ i)))
      (e (TorusSurface.projection ω₁ ω₂ (halfPeriod ω₁ ω₂ i)))).val = O

end Specs.D12Complex.Ch22.ExceptionalAddition
