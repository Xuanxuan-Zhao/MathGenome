import MathGenome.Internal.Specs.D07.Ch19.GaussianEuclidean

/-!
Independent statements for the arithmetic part of Theorem 4.3 (`nt:D03`),
`paper.tex:1465–1490`. Rational-prime splitting is allocated to D03Primes.
The ring throughout is the canonical `GaussianInt = Zsqrtd (-1)` with integer
coordinates; `star` is conjugation and `.norm` is the integer-valued squared norm.
-/

namespace P203Specs.Ch04.GaussianArithmetic

/-- Identify the coordinate ring with precisely the Gaussian integers in ℂ,
including its coordinate formula and conjugation. -/
def CanonicalModel : Prop :=
  Specs.D07.Ch19.GaussianEuclidean.ComplexEmbedding ∧
    ∀ z : GaussianInt,
      GaussianInt.toComplex z = (z.re : ℂ) + (z.im : ℂ) * Complex.I ∧
      star z = (⟨z.re, -z.im⟩ : GaussianInt)

def NormProperties : Prop :=
  ∀ z : GaussianInt,
    z.norm = z.re ^ 2 + z.im ^ 2 ∧
    0 ≤ z.norm ∧ (z.norm = 0 ↔ z = 0) ∧ (0 < z.norm ↔ z ≠ 0) ∧
    (z.norm : GaussianInt) = z * star z ∧
    (z.norm : ℝ) = Complex.normSq (GaussianInt.toComplex z) ∧
    GaussianInt.toComplex (star z) = star (GaussianInt.toComplex z)

def NormMultiplicative : Prop :=
  ∀ z w : GaussianInt, (z * w).norm = z.norm * w.norm

/-- Chosen Euclidean data for exactly this norm, quotient, and remainder.
The upstream independent definition specifies the relation
`a.norm.natAbs < b.norm.natAbs`, not an unrelated Euclidean structure. -/
def NormEuclideanData : Prop :=
  Specs.D07.Ch19.GaussianEuclidean.NormEuclideanData

/-- Includes strict norm decrease for every nonzero divisor, with the explicit
half-norm bound from rounding, and permits a zero remainder. -/
def DivisionEstimate : Prop :=
  ∀ z w : GaussianInt, w ≠ 0 →
    let q : GaussianInt := z / w
    let r : GaussianInt := z - q * w
    z = q * w + r ∧
    (r.norm : ℝ) = (w.norm : ℝ) *
      Complex.normSq (GaussianInt.toComplex z / GaussianInt.toComplex w -
        GaussianInt.toComplex q) ∧
    (r.norm : ℝ) ≤ (w.norm : ℝ) / 2 ∧ r.norm < w.norm

def Units : Prop :=
  ∀ z : GaussianInt,
    (IsUnit z ↔ z.norm = 1) ∧
    (z.norm = 1 ↔ z = 1 ∨ z = -1 ∨
      z = (⟨0, 1⟩ : GaussianInt) ∨ z = -(⟨0, 1⟩ : GaussianInt)) ∧
    (IsUnit z → z * star z = 1 ∧ star z * z = 1)

/-- Prime products, with an explicit unit, and uniqueness matching all
occurrences of factors. The last clause identifies exactly the elements
represented by the empty prime product. `Multiset.Rel Associated` permits
reordering and unit changes of individual factors, preserving multiplicities. -/
def UniqueFactorization : Prop :=
  UniqueFactorizationMonoid GaussianInt ∧
  (∀ a : GaussianInt, a ≠ 0 → ∃ f : Multiset GaussianInt,
    (∀ p ∈ f, Prime p) ∧ ∃ u : GaussianIntˣ, a = (u : GaussianInt) * f.prod) ∧
  (∀ f g : Multiset GaussianInt,
    (∀ p ∈ f, Prime p) → (∀ q ∈ g, Prime q) →
    Associated f.prod g.prod →
    f.card = g.card ∧ Multiset.Rel Associated f g) ∧
  (∀ a : GaussianInt, IsUnit a ↔ Associated (0 : Multiset GaussianInt).prod a)

end P203Specs.Ch04.GaussianArithmetic
