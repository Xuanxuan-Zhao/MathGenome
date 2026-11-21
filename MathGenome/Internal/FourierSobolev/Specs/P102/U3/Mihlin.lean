import MathGenome.Internal.FourierSobolev.Specs.P102.U3.MihlinDyadicKernels
import MathGenome.Internal.FourierSobolev.Specs.P102.U2.CZLp

/-! Independent statement of the complete classical Mihlin theorem,
paper.tex:1206–1234. `SymbolBound` uses exactly floor(d/2)+1 coordinate
derivatives, including order zero. A Fourier identity on all L² inputs
specifies the canonical multiplier without making any choice at frequency zero.
The extension agrees on the entire L²/Lᵖ intersection and is unique among all
bounded complex-linear maps with that agreement, regardless of their bounds. -/
noncomputable section
open MeasureTheory Filter
open scoped FourierTransform Topology NNReal

namespace P102.U3.Mihlin
open P102.Specs.U3 (Euclidean)
open P102.U2.CZWeak (Operator)
open P102.U2.CZLpData (Exponent StrongOperator Agrees PairwiseCompatible)

/-- Actual canonical Plancherel multiplier identity. -/
def HasL2Symbol {d : ℕ} (T : Operator d) (m : Euclidean d → ℂ) : Prop :=
  ∀ f : Lp (α := Euclidean d) ℂ 2 volume,
    ((𝓕 (T f) : Lp (α := Euclidean d) ℂ 2 volume) : Euclidean d → ℂ)
      =ᵐ[volume] fun ξ => m ξ * (𝓕 f : Lp (α := Euclidean d) ℂ 2 volume) ξ

/-- The exhausting finite scale intervals used in the source's limit argument. -/
def scales (M : ℕ) : Finset ℤ := Finset.Icc (-(M : ℤ)) (M : ℤ)

end P102.U3.Mihlin

namespace P102.Specs.U3.Mihlin
open P102.U3.Mihlin
open P102.U2.CZWeak (Operator)
open P102.U2.CZLpData (Exponent StrongOperator Agrees PairwiseCompatible)

def l2ExistenceType : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (m : Euclidean d → ℂ) (A : ℝ),
    SymbolBound m A → ∃ T : Operator d, HasL2Symbol T m ∧ ‖T‖ ≤ A

def l2UniquenessType : Prop :=
  ∀ (d : ℕ) (m : Euclidean d → ℂ) (T U : Operator d),
    HasL2Symbol T m → HasL2Symbol U m → T = U

def originIrrelevanceType : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (m n : Euclidean d → ℂ),
    (∀ ξ, ξ ≠ 0 → m ξ = n ξ) → ∀ T : Operator d,
      HasL2Symbol T m ↔ HasL2Symbol T n

def dyadicConvergenceType : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (χ : Euclidean d → ℝ), IsCutoff χ → IsPartition χ →
    ∀ (m : Euclidean d → ℂ) (A : ℝ), SymbolBound m A →
    ∀ (T : Operator d) (U : ℕ → Operator d), HasL2Symbol T m →
      (∀ M, HasL2Symbol (U M) (finiteSymbol χ m (scales M))) →
      ∀ f : Lp (α := Euclidean d) ℂ 2 volume,
        Tendsto (fun M => U M f) atTop (𝓝 (T f))

def theoremType : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∃ C : Exponent → ℝ≥0,
    ∀ (m : Euclidean d → ℂ) (A : ℝ), 0 ≤ A → SymbolBound m A →
      ∃ (T : Operator d), HasL2Symbol T m ∧ ‖T‖ ≤ A ∧
      ∃ R : ∀ p : Exponent, StrongOperator d p,
        (∀ p, ‖R p‖ ≤ (C p : ℝ) * A) ∧
        (∀ p, Agrees T p (R p)) ∧ PairwiseCompatible R ∧
        (∀ (p : Exponent) (S : StrongOperator d p), Agrees T p S → S = R p)

end P102.Specs.U3.Mihlin
