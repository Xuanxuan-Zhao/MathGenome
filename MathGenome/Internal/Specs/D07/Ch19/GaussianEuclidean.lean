import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import MathGenome.Internal.Specs.D07.Ch10.EuclideanDefinition
import MathGenome.Internal.Specs.D07.Ch10.PidDefinition
import MathGenome.Internal.Specs.D07.Ch10.PidUfd

/-!
Independent specifications for K07.19.gaussian_euclidean (paper.tex:5666–5680).
`GaussianInt = Zsqrtd (-1)` is the integer-coordinate model. The first
statement identifies it with exactly the indicated subring of ℂ. The norm
is integer-valued, and corresponds to complex norm *squared*.
The quotient is the library's nearest-coordinate quotient; its rounding
and the sharper half-norm remainder estimate are both explicit obligations.
-/

namespace Specs.D07.Ch19.GaussianEuclidean

def ComplexEmbedding : Prop :=
  Function.Injective GaussianInt.toComplex ∧
    ∀ c : ℂ, (∃ z : GaussianInt, GaussianInt.toComplex z = c) ↔
      ∃ a b : ℤ, c = (a : ℂ) + (b : ℂ) * Complex.I

def NormProperties : Prop :=
  ∀ z : GaussianInt,
    z.norm = z.re ^ 2 + z.im ^ 2 ∧
    0 ≤ z.norm ∧ (z.norm = 0 ↔ z = 0) ∧ (0 < z.norm ↔ z ≠ 0) ∧
    (z.norm : GaussianInt) = z * star z ∧
    (z.norm : ℝ) = Complex.normSq (GaussianInt.toComplex z) ∧
    GaussianInt.toComplex (star z) = star (GaussianInt.toComplex z)

def NormMultiplicative : Prop :=
  ∀ z w : GaussianInt, (z * w).norm = z.norm * w.norm

def Units : Prop :=
  ∀ z : GaussianInt,
    (IsUnit z ↔ z.norm = 1) ∧
    (z.norm = 1 ↔ z = 1 ∨ z = -1 ∨
      z = (⟨0, 1⟩ : GaussianInt) ∨ z = -(⟨0, 1⟩ : GaussianInt)) ∧
    (IsUnit z → z * star z = 1 ∧ star z * z = 1)

/-- Both rounded coordinates are nearest integers, including ties. -/
def QuotientRounding : Prop :=
  ∀ z w : GaussianInt,
    let u : ℂ := GaussianInt.toComplex z / GaussianInt.toComplex w
    let q : GaussianInt := z / w
    q.re = round u.re ∧ q.im = round u.im ∧
    |u.re - (q.re : ℝ)| ≤ 1 / 2 ∧
    |u.im - (q.im : ℝ)| ≤ 1 / 2 ∧
    Complex.normSq (u - GaussianInt.toComplex q) ≤ 1 / 2

/-- The zero remainder is allowed; only the divisor must be nonzero. -/
def DivisionEstimate : Prop :=
  ∀ z w : GaussianInt, w ≠ 0 →
    let q : GaussianInt := z / w
    let r : GaussianInt := z - q * w
    z = q * w + r ∧
    (r.norm : ℝ) = (w.norm : ℝ) *
      Complex.normSq (GaussianInt.toComplex z / GaussianInt.toComplex w -
        GaussianInt.toComplex q) ∧
    (r.norm : ℝ) ≤ (w.norm : ℝ) / 2 ∧ r.norm < w.norm

/-- Chosen data use the natural-valued version of precisely the norm above. -/
def NormEuclideanData : Prop :=
  ∃ d : Specs.D07.Ch10.EuclideanDefinition.EuclideanData GaussianInt,
    d.smaller = (fun a b => a.norm.natAbs < b.norm.natAbs) ∧
    d.quotient = (fun a b => a / b) ∧
    d.remainder = (fun a b => a - (a / b) * b)

def Euclidean : Prop :=
  Specs.D07.Ch10.EuclideanDefinition.IsEuclidean GaussianInt

def PrincipalIdealDomain : Prop :=
  Specs.D07.Ch10.PidDefinition.pidPredicateValue GaussianInt

/-- Includes existence and uniqueness with multiplicities, up to units and order. -/
def UniqueFactorization : Prop :=
  UniqueFactorizationMonoid GaussianInt ∧
    Specs.D07.Ch10.PidUfd.FactorizationProperty GaussianInt

end Specs.D07.Ch19.GaussianEuclidean
