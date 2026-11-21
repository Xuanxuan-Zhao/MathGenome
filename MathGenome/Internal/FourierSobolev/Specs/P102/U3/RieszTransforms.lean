import MathGenome.Internal.FourierSobolev.Specs.P102.U3.RieszL2Multiplier
import MathGenome.Internal.FourierSobolev.Specs.P102.U2.CZLp

/-! The complete Hilbert/Riesz assertion, paper.tex:1161–1184.
The kernel, multiplier, Euclidean volume and Fourier convention are inherited
from the independent upstream Specs. The convergence assertion uses ordinary
physical truncations along every positive real radius. -/
noncomputable section
open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace P102.Specs.U3.RieszTransforms
open P102.Specs.U3 (Euclidean)
open P102.Specs.U3.Riesz
open P102.U2.CZWeak P102.U2.CZLpData

/-- Both convergence modes, with absolute existence and Lp membership at every
positive radius. The limit is the bounded extension on the original Lp class. -/
def Convergence {d : ℕ} (j : Fin d) (p : Exponent)
    (R : StrongOperator d p) : Prop :=
  ∀ (f : Euclidean d → ℂ) (hf : MemLp f p.val volume),
    (∀ ε : ℝ, 0 < ε → ∀ x : Euclidean d,
      IntegrableOn (fun z => (kernelValue d j z : ℂ) * f (x - z))
        {z : Euclidean d | ε < ‖z‖} volume) ∧
    (∀ ε : ℝ, 0 < ε → MemLp (truncation j ε f) p.val volume) ∧
    (∀ᵐ x ∂volume, Tendsto (fun ε => truncation j ε f x) (𝓝[>] 0)
      (𝓝 ((R (hf.toLp f) : Euclidean d → ℂ) x))) ∧
    Tendsto (fun ε => eLpNorm
      (fun x => truncation j ε f x - (R (hf.toLp f) : Euclidean d → ℂ) x)
        p.val volume) (𝓝[>] 0) (𝓝 0)

/-- No endpoint or convergence certificate is assumed. The existential L²
action is the unique multiplier for every value at the null origin. All pairwise
Lp intersections and the weak endpoint agree with that action. -/
def Result (d : ℕ) (j : Fin d) : Prop :=
  ∃ (T : Operator d) (S : Extension d)
    (R : ∀ p : Exponent, StrongOperator d p)
    (C₁ : ℝ≥0) (C : Exponent → ℝ≥0),
    (∀ a : ℂ, IsMultiplier j a T) ∧ ‖T‖ ≤ 1 ∧
    Compatible T S ∧ WeakBound S C₁ ∧ UniqueWeakExtension T S ∧
    (∀ p, ‖R p‖ ≤ C p) ∧ (∀ p, Agrees T p (R p)) ∧
    PairwiseCompatible R ∧ EndpointCompatible S R ∧
    (∀ p, Convergence j p (R p)) ∧
    (∀ (a : ℂ) (U : Operator d), IsMultiplier j a U → U = T)

def full_theorem : Prop := ∀ d : ℕ, 1 ≤ d → ∀ j : Fin d, Result d j

/-- The one-dimensional conclusion includes the exact Hilbert kernel and sign
symbol, as well as all endpoint, strong and convergence assertions above.
`line` is the canonical orthonormal coordinate identification of ℝ with ℝ¹. -/
def hilbert_theorem : Prop := oneDimensionalStatement ∧ Result 1 0

end P102.Specs.U3.RieszTransforms
