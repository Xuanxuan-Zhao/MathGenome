import MathGenome.Internal.FourierSobolev.Specs.P102.Periodic.Foundation
import Mathlib.Analysis.Fourier.ZMod

/-! Independent specifications for the probability-normalized cyclic Fourier transform.
`NeZero m` for a natural number is exactly the source's hypothesis `m ≥ 1`.
Both spatial and frequency indices are residue classes. Integer-cast formulas
below specify the value for every integer representative, including negative ones. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal

namespace P102.Periodic.CyclicData

variable (m : ℕ) [NeZero m]

def counting (m : ℕ) [NeZero m] : Measure (ZMod m) := (m : ℝ≥0∞)⁻¹ • Measure.count

def character (k j : ZMod m) : ℂ := ZMod.stdAddChar (k * j)

def coefficient (f : ZMod m → ℂ) (k : ZMod m) : ℂ :=
  (m : ℂ)⁻¹ * ∑ j, f j * conj (character m k j)

def convolution (f g : ZMod m → ℂ) (j : ZMod m) : ℂ :=
  (m : ℂ)⁻¹ * ∑ l, f (j - l) * g l

/-- The homomorphism identifies the cyclic group with its image subgroup. -/
def sample (T : ℝ) [hT : Fact (0 < T)] : ZMod m →+ AddCircle T :=
  (AddCircle.equivAddCircle (1 : ℝ) T one_ne_zero hT.out.ne').toAddMonoidHom.comp
    ZMod.toAddCircle

end P102.Periodic.CyclicData

namespace P102.Periodic.CyclicExpected
open CyclicData

def countingType := ∀ (m : ℕ) [NeZero m], Measure (ZMod m)
def countingValue := CyclicData.counting

def characterType := ∀ (m : ℕ) [NeZero m], ZMod m → ZMod m → ℂ
def characterValue := CyclicData.character

def coefficientType := ∀ (m : ℕ) [NeZero m], (ZMod m → ℂ) → ZMod m → ℂ
def coefficientValue := CyclicData.coefficient

def convolutionType := ∀ (m : ℕ) [NeZero m], (ZMod m → ℂ) → (ZMod m → ℂ) → ZMod m → ℂ
def convolutionValue := CyclicData.convolution

def sampleType := ∀ (m : ℕ) [NeZero m] (T : ℝ) [Fact (0 < T)], ZMod m →+ AddCircle T
def sampleValue := CyclicData.sample

def countingProbability : Prop := ∀ (m : ℕ) [NeZero m], counting m Set.univ = 1

def countingSingleton : Prop := ∀ (m : ℕ) [NeZero m] (j : ZMod m),
  counting m {j} = (m : ℝ≥0∞)⁻¹

def averageIntegral : Prop := ∀ (m : ℕ) [NeZero m] (f : ZMod m → ℂ),
  (∫ j, f j ∂counting m) = (m : ℂ)⁻¹ * ∑ j, f j

def characterFormula : Prop := ∀ (m : ℕ) [NeZero m] (k j : ℤ),
  character m (k : ZMod m) (j : ZMod m) =
    Complex.exp (2 * Real.pi * Complex.I * k * j / m)

def characterOrthonormal : Prop := ∀ (m : ℕ) [NeZero m] (k l : ZMod m),
  (m : ℂ)⁻¹ * ∑ j, character m k j * conj (character m l j) =
    if k = l then 1 else 0

def inversion : Prop := ∀ (m : ℕ) [NeZero m] (f : ZMod m → ℂ) (j : ZMod m),
  f j = ∑ k, coefficient m f k * character m k j

def parseval : Prop := ∀ (m : ℕ) [NeZero m] (f : ZMod m → ℂ),
  (m : ℝ)⁻¹ * ∑ j, ‖f j‖ ^ 2 = ∑ k, ‖coefficient m f k‖ ^ 2

def convolutionProduct : Prop := ∀ (m : ℕ) [NeZero m] (f g : ZMod m → ℂ) (k : ZMod m),
  coefficient m (convolution m f g) k = coefficient m f k * coefficient m g k

def sampleInjective : Prop := ∀ (m : ℕ) [NeZero m] (T : ℝ) [Fact (0 < T)],
  Function.Injective (sample m T)

def sampleFormula : Prop := ∀ (m : ℕ) [NeZero m] (T : ℝ) [Fact (0 < T)] (j : ℤ),
  sample m T (j : ZMod m) = ((T * j / m : ℝ) : AddCircle T)

def modeRestriction : Prop := ∀ (m : ℕ) [NeZero m] (T : ℝ) [Fact (0 < T)]
  (k : ℤ) (j : ZMod m),
  Expected.mode T k (sample m T j) = character m (k : ZMod m) j

/-- The trivial group is included; these are the exact scalar specializations. -/
def trivialGroup : Prop :=
  (∀ k j : ZMod 1, character 1 k j = 1) ∧
  (∀ (f : ZMod 1 → ℂ) k, coefficient 1 f k = f 0) ∧
  (∀ (f g : ZMod 1 → ℂ) j, convolution 1 f g j = f 0 * g 0)

end P102.Periodic.CyclicExpected
