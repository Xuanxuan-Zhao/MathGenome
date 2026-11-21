import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Rounding.Operations
import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Rounding.GammaProducts
import Mathlib.Algebra.BigOperators.Fin

noncomputable section
open scoped BigOperators
namespace NumAnalysis206.Rounding.DotSpecs

/-- A prefix of the exact stored real input sequences. Only indices below n are read.
`fused = false` stores rounded products, and assigns the first product directly.
`fused = true` rounds the exact multiply-add once per term, starting at zero. -/
def trace (fused : Bool) (round : ℝ → ℝ) (x y : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => round (x 0 * y 0)
  | n + 2 => round (trace fused round x y (n + 1) +
      if fused then x (n + 1) * y (n + 1) else round (x (n + 1) * y (n + 1)))

/-- Exactly the range checks for the executed primitives. There is no addition
check at length one, and no separate product check for an FMA. -/
def safe (fused : Bool) (round : ℝ → ℝ) (D : Set ℝ) (x y : ℕ → ℝ) : ℕ → Prop
  | 0 => True
  | 1 => x 0 * y 0 ∈ D
  | n + 2 => safe fused round D x y (n + 1) ∧
      (if fused then True else x (n + 1) * y (n + 1) ∈ D) ∧
      trace fused round x y (n + 1) +
        (if fused then x (n + 1) * y (n + 1) else round (x (n + 1) * y (n + 1))) ∈ D

abbrev TraceType := Bool → (ℝ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → ℕ → ℝ
abbrev SafeType := Bool → (ℝ → ℝ) → Set ℝ → (ℕ → ℝ) → (ℕ → ℝ) → ℕ → Prop

def conclusion (fused : Bool) (round : ℝ → ℝ) (x y : ℕ → ℝ) (n : ℕ) (u : ℝ) : Prop :=
  (∃ θ : ℕ → ℝ,
    trace fused round x y n = ∑ i ∈ Finset.range n, x i * y i * (1 + θ i) ∧
    ∀ i < n, |θ i| ≤ _root_.Specs.NumAnalysis206.Rounding.gammaValue n u) ∧
  |trace fused round x y n - ∑ i ∈ Finset.range n, x i * y i| ≤
    _root_.Specs.NumAnalysis206.Rounding.gammaValue n u * ∑ i ∈ Finset.range n, |x i * y i|

def sequentialDotProduct : Prop := ∀ (fused : Bool) (round : ℝ → ℝ)
    (x y : ℕ → ℝ) (n : ℕ) (u : ℝ) (D : Set ℝ),
  Specs.RelativeModelValue round u D → (n : ℝ) * u < 1 →
  safe fused round D x y n → conclusion fused round x y n u

def boundaryCases : Prop := ∀ (fused : Bool) (round : ℝ → ℝ) (x y : ℕ → ℝ),
  trace fused round x y 0 = 0 ∧ trace fused round x y 1 = round (x 0 * y 0)

def fusedRecurrence : Prop := ∀ (round : ℝ → ℝ) (x y : ℕ → ℝ) (n : ℕ),
  trace true round x y (n + 1) = round (x n * y n + trace true round x y n)

def separateRecurrence : Prop := ∀ (round : ℝ → ℝ) (x y : ℕ → ℝ) (n : ℕ),
  trace false round x y (n + 2) =
    round (trace false round x y (n + 1) + round (x (n + 1) * y (n + 1)))

/-- A coarser budget is used only on its own admissible domain, including N=2n. -/
def coarseEstimate : Prop := ∀ (fused : Bool) (round : ℝ → ℝ)
    (x y : ℕ → ℝ) (n N : ℕ) (u : ℝ) (D : Set ℝ),
  Specs.RelativeModelValue round u D → n ≤ N →
  _root_.Specs.NumAnalysis206.Rounding.budgetDomainValue N u →
  safe fused round D x y n →
  |trace fused round x y n - ∑ i ∈ Finset.range n, x i * y i| ≤
    _root_.Specs.NumAnalysis206.Rounding.gammaValue N u * ∑ i ∈ Finset.range n, |x i * y i|
/-- Zero extension is only an interface from a finite vector to prefix traces. -/
def extendVector {n : ℕ} (x : Fin n → ℝ) (i : ℕ) : ℝ :=
  if h : i < n then x ⟨i, h⟩ else 0

abbrev FiniteTraceType := Bool → (ℝ → ℝ) → {n : ℕ} → (Fin n → ℝ) → (Fin n → ℝ) → ℝ
def finiteTrace : FiniteTraceType := fun fused round {n} x y =>
  trace fused round (extendVector x) (extendVector y) n

abbrev FiniteSafeType := Bool → (ℝ → ℝ) → Set ℝ → {n : ℕ} →
  (Fin n → ℝ) → (Fin n → ℝ) → Prop
def finiteSafe : FiniteSafeType := fun fused round D {n} x y =>
  safe fused round D (extendVector x) (extendVector y) n

def finiteConclusion (fused : Bool) (round : ℝ → ℝ) {n : ℕ}
    (x y : Fin n → ℝ) (u : ℝ) : Prop :=
  (∃ θ : Fin n → ℝ,
    finiteTrace fused round x y = ∑ i, x i * y i * (1 + θ i) ∧
    ∀ i, |θ i| ≤ _root_.Specs.NumAnalysis206.Rounding.gammaValue n u) ∧
  |finiteTrace fused round x y - ∑ i, x i * y i| ≤
    _root_.Specs.NumAnalysis206.Rounding.gammaValue n u * ∑ i, |x i * y i|

def finiteSequentialDotProduct : Prop := ∀ (fused : Bool) (round : ℝ → ℝ)
    (n : ℕ) (x y : Fin n → ℝ) (u : ℝ) (D : Set ℝ),
  Specs.RelativeModelValue round u D → (n : ℝ) * u < 1 →
  finiteSafe fused round D x y → finiteConclusion fused round x y u

/-- The original stored-input specialization uses each stored number's exact real value. -/
def storedDotProduct : Prop := ∀ (P : RadixFormat) (fused : Bool) (n : ℕ)
    (x y : Fin n → Specs.StoredValue P) (u : ℝ) (D : Set ℝ),
  Specs.RelativeModelValue (Specs.flValue P) u D → (n : ℝ) * u < 1 →
  finiteSafe fused (Specs.flValue P) D (fun i => (x i).val) (fun i => (y i).val) →
  finiteConclusion fused (Specs.flValue P) (fun i => (x i).val) (fun i => (y i).val) u
end NumAnalysis206.Rounding.DotSpecs
