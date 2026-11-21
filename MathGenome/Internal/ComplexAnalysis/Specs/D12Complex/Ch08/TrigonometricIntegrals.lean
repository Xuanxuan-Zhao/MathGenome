import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch08.Residue
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Algebra.MvPolynomial.CommRing

/-! Trigonometric rational functions are represented after the substitution
`z = exp(it)` by a reduced member of ℂ(X). Evaluation therefore fills every
removable singularity before taking the real integral. The original two-variable
polynomial numerator and denominator can be supplied to `rationalize` below.
Its denominator must not become the zero rational function: an expression
undefined identically on the circle is not a meromorphic function there.
-/
noncomputable section
open Set
open scoped BigOperators

namespace D12Complex.TrigonometricIntegrals

/-- Rational substitution for a polynomial in cosine (variable 0) and sine
(variable 1). All arithmetic here takes place in the rational-function field. -/
def substitute (p : MvPolynomial (Fin 2) ℂ) : RatFunc ℂ :=
  MvPolynomial.eval₂Hom RatFunc.C
    (fun j => if j = 0 then (RatFunc.X + RatFunc.X⁻¹) / 2
      else (RatFunc.X - RatFunc.X⁻¹) / (2 * RatFunc.C Complex.I)) p

def rationalize (p q : MvPolynomial (Fin 2) ℂ) : RatFunc ℂ :=
  substitute p / substitute q

/-- Reduced rational evaluation; this is explicitly evaluation after cancellation. -/
def value (r : RatFunc ℂ) (z : ℂ) : ℂ := RatFunc.eval (RingHom.id ℂ) z r

/-- The canceled trigonometric integrand. -/
def angularValue (r : RatFunc ℂ) (t : ℝ) : ℂ := value r (circleMap 0 1 t)

/-- Absence of poles on the real parameter line, checked on the reduced denominator. -/
def NoCirclePoles (r : RatFunc ℂ) : Prop :=
  ∀ t : ℝ, r.denom.eval (circleMap 0 1 t) ≠ 0

/-- The coefficient of the substituted differential. Its value at zero is
irrelevant: residues and contour integrals depend only on the punctured germ.
Cancellation has already been performed in r. -/
def transform (r : RatFunc ℂ) (z : ℂ) : ℂ := value r z / (Complex.I * z)

/-- A finite list of all possible singularities, including zero. Removable
points contribute their actual (zero) residue. -/
def singularities (r : RatFunc ℂ) : Finset ℂ :=
  insert 0 r.denom.roots.toFinset

end D12Complex.TrigonometricIntegrals

namespace Specs.D12Complex.Ch08.TrigonometricIntegrals
open _root_.D12Complex.TrigonometricIntegrals

def substitute_type := MvPolynomial (Fin 2) ℂ → RatFunc ℂ
def substitute_value : substitute_type := fun p =>
  MvPolynomial.eval₂Hom RatFunc.C
    (fun j => if j = 0 then (RatFunc.X + RatFunc.X⁻¹) / 2
      else (RatFunc.X - RatFunc.X⁻¹) / (2 * RatFunc.C Complex.I)) p

def rationalize_type := MvPolynomial (Fin 2) ℂ → MvPolynomial (Fin 2) ℂ → RatFunc ℂ
def rationalize_value : rationalize_type := fun p q => substitute p / substitute q

def value_type := RatFunc ℂ → ℂ → ℂ
def value_value : value_type := fun r z => RatFunc.eval (RingHom.id ℂ) z r

def angularValue_type := RatFunc ℂ → ℝ → ℂ
def angularValue_value : angularValue_type := fun r t => value r (circleMap 0 1 t)

def NoCirclePoles_type := RatFunc ℂ → Prop
def NoCirclePoles_value : NoCirclePoles_type := fun r =>
  ∀ t : ℝ, r.denom.eval (circleMap 0 1 t) ≠ 0

def transform_type := RatFunc ℂ → ℂ → ℂ
def transform_value : transform_type := fun r z => value r z / (Complex.I * z)

def singularities_type := RatFunc ℂ → Finset ℂ
def singularities_value : singularities_type := fun r => insert 0 r.denom.roots.toFinset

def transform_no_unit_circle_pole_type : Prop :=
  ∀ r : RatFunc ℂ, NoCirclePoles r →
    ∀ z : ℂ, ‖z‖ = 1 → DifferentiableAt ℂ (transform r) z

def circle_substitution_type : Prop :=
  ∀ r : RatFunc ℂ,
    (∫ t in (0 : ℝ)..2 * Real.pi, angularValue r t) =
      circleIntegral (transform r) 0 1

def trigonometric_residue_formula_type : Prop :=
  ∀ r : RatFunc ℂ, NoCirclePoles r →
    (∫ t in (0 : ℝ)..2 * Real.pi, angularValue r t) =
      (2 * Real.pi * Complex.I : ℂ) *
        ∑ a ∈ (singularities r).filter (fun a => ‖a‖ < 1),
          _root_.D12Complex.Residue.residue (transform r) a

/-- The original rational expression, with cancellation performed only after
substituting the displayed cosine and sine rational functions. -/
def rational_expression_formula_type : Prop :=
  ∀ p q : MvPolynomial (Fin 2) ℂ, substitute q ≠ 0 →
    NoCirclePoles (rationalize p q) →
    (∫ t in (0 : ℝ)..2 * Real.pi, angularValue (rationalize p q) t) =
      (2 * Real.pi * Complex.I : ℂ) *
        ∑ a ∈ (singularities (rationalize p q)).filter (fun a => ‖a‖ < 1),
          _root_.D12Complex.Residue.residue (transform (rationalize p q)) a

def integral_inv_affine_cos_type : Prop :=
  ∀ a b : ℝ, |b| < a →
    (∫ t in (0 : ℝ)..2 * Real.pi, (a + b * Real.cos t)⁻¹) =
      2 * Real.pi / Real.sqrt (a^2 - b^2)

def angularValue_intervalIntegrable_type : Prop :=
  ∀ r : RatFunc ℂ, NoCirclePoles r →
    IntervalIntegrable (angularValue r) MeasureTheory.volume 0 (2*Real.pi)

def transform_rational_type : Prop :=
  ∀ r : RatFunc ℂ, ∃ P Q : Polynomial ℂ, Q ≠ 0 ∧
    transform r = fun z => P.eval z / Q.eval z

/-- Agreement with the original polynomial quotient wherever it is defined.
At its removable parameter values the formula uses the canceled rational
representative instead; there is no nonvanishing assumption on the raw
trigonometric denominator in the residue formula above. -/
def rationalize_value_type : Prop :=
  ∀ (p q : MvPolynomial (Fin 2) ℂ) (t : ℝ),
    MvPolynomial.eval₂Hom (RingHom.id ℂ)
      (fun i : Fin 2 => if i = 0 then (Real.cos t : ℂ) else (Real.sin t : ℂ)) q ≠ 0 →
    angularValue (rationalize p q) t =
      MvPolynomial.eval₂Hom (RingHom.id ℂ)
        (fun i : Fin 2 => if i = 0 then (Real.cos t : ℂ) else (Real.sin t : ℂ)) p /
      MvPolynomial.eval₂Hom (RingHom.id ℂ)
        (fun i : Fin 2 => if i = 0 then (Real.cos t : ℂ) else (Real.sin t : ℂ)) q

def residue_transform_zero_off_singularities_type : Prop :=
  ∀ (r : RatFunc ℂ) (a : ℂ), a ∉ singularities r →
    _root_.D12Complex.Residue.residue (transform r) a = 0

end Specs.D12Complex.Ch08.TrigonometricIntegrals
