import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch19.PeriodicSetup

/-! K03.19.periodic_setup and the real/complex part of K03.19.normalization_bridge.
All integrals below are the upstream proper Darboux integrals. The weighted
integrability arguments are witnesses, whose existence for every integrable
input is provided by PeriodicSetup; they impose no additional regularity.
The range sum uses k+1 for precisely the positive indices 1,...,N.
Finite changes are allowed anywhere on a closed period, including both seams.
-/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch19.Representation
open Ch08.Integral PeriodicSetup
open scoped BigOperators

abbrev ComplexWeights (f : ℝ → ℂ) := ∀ n : ℤ,
  complexIntegrableValue (fun x => f x * modeValue (-n) x) (-Real.pi) Real.pi
abbrev CosineWeights (f : ℝ → ℝ) := ∀ n : ℕ+,
  realIntegrableValue (fun x => f x * Real.cos ((n : ℝ) * x)) (-Real.pi) Real.pi
abbrev SineWeights (f : ℝ → ℝ) := ∀ n : ℕ+,
  realIntegrableValue (fun x => f x * Real.sin ((n : ℝ) * x)) (-Real.pi) Real.pi

def zeroCoefficient : Prop := ∀ (f : ℝ → ℝ) (hf : periodicRealValue f)
  (h : ComplexWeights (fun x => (f x : ℂ))),
  coefficientValue (fun x => (f x : ℂ)) 0 (h 0) = (aZeroValue f hf.2 : ℂ) / 2

def positiveCoefficient : Prop := ∀ (f : ℝ → ℝ) (_hf : periodicRealValue f)
  (h : ComplexWeights (fun x => (f x : ℂ)))
  (ha : CosineWeights f) (hb : SineWeights f) (n : ℕ+),
  coefficientValue (fun x => (f x : ℂ)) (n : ℤ) (h n) =
    ((cosineCoefficientValue f n (ha n) : ℂ) -
      Complex.I * (sineCoefficientValue f n (hb n) : ℂ)) / 2

def negativeCoefficient : Prop := ∀ (f : ℝ → ℝ) (_hf : periodicRealValue f)
  (h : ComplexWeights (fun x => (f x : ℂ)))
  (ha : CosineWeights f) (hb : SineWeights f) (n : ℕ+),
  coefficientValue (fun x => (f x : ℂ)) (-(n : ℤ)) (h (-n)) =
    ((cosineCoefficientValue f n (ha n) : ℂ) +
      Complex.I * (sineCoefficientValue f n (hb n) : ℂ)) / 2

def finitePartialSum : Prop := ∀ (f : ℝ → ℝ) (hf : periodicRealValue f)
  (h : ComplexWeights (fun x => (f x : ℂ)))
  (ha : CosineWeights f) (hb : SineWeights f) (N : ℕ) (x : ℝ),
  partialSumValue (fun t => (f t : ℂ)) h N x =
    ((aZeroValue f hf.2 / 2 + ∑ k ∈ Finset.range N,
      (cosineCoefficientValue f ⟨k+1, Nat.succ_pos k⟩ (ha _) * Real.cos (((k+1 : ℕ) : ℝ) * x) +
      sineCoefficientValue f ⟨k+1, Nat.succ_pos k⟩ (hb _) * Real.sin (((k+1 : ℕ) : ℝ) * x)) : ℝ) : ℂ)

def finiteChangesIntegrable : Prop := ∀ (f g : ℝ → ℂ),
  periodicComplexValue f → Function.Periodic g (2 * Real.pi) →
  {x | x ∈ Set.Icc (-Real.pi) Real.pi ∧ f x ≠ g x}.Finite →
  periodicComplexValue g

def coefficientsFiniteChanges : Prop := ∀ (f g : ℝ → ℂ),
  periodicComplexValue f → periodicComplexValue g →
  {x | x ∈ Set.Icc (-Real.pi) Real.pi ∧ f x ≠ g x}.Finite →
  ∀ (h : ComplexWeights f) (j : ComplexWeights g) (n : ℤ),
    coefficientValue f n (h n) = coefficientValue g n (j n)

def realCoefficientsFiniteChanges : Prop := ∀ (f g : ℝ → ℝ)
  (hf : periodicRealValue f) (hg : periodicRealValue g),
  {x | x ∈ Set.Icc (-Real.pi) Real.pi ∧ f x ≠ g x}.Finite →
  ∀ (ha : CosineWeights f) (hb : SineWeights f)
    (ja : CosineWeights g) (jb : SineWeights g),
    aZeroValue f hf.2 = aZeroValue g hg.2 ∧
    ∀ n : ℕ+, cosineCoefficientValue f n (ha n) = cosineCoefficientValue g n (ja n) ∧
      sineCoefficientValue f n (hb n) = sineCoefficientValue g n (jb n)

end Specs.SingleVariableAnalysis.Ch19.Representation
