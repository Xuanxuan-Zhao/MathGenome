import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch12.Uniform
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
Independent specification of `K03.12.sup_norm`, paper.tex:1204–1212.
The domain is any type (a subset is represented by its subtype), possibly empty.
`ℝ≥0∞` is the nonnegative extended real interval `[0, ∞]`. The complete-lattice
supremum of the nonnegative errors is defined even for unbounded differences;
its value on an empty domain is zero. No function boundedness is assumed.
Convergence of these extended errors uses their canonical order topology.
Indices follow Uniform: `F n` represents the manuscript's term `n + 1`.
-/

namespace Specs.SingleVariableAnalysis.Ch12.SupNorm

open scoped Topology ENNReal
universe u

def realSupErrorType : Type (u + 1) :=
  {E : Type u} → (ℕ → E → ℝ) → (E → ℝ) → ℕ → ℝ≥0∞

noncomputable def realSupErrorValue : realSupErrorType :=
  fun F f n => ⨆ x, ENNReal.ofReal |F n x - f x|

def complexSupErrorType : Type (u + 1) :=
  {E : Type u} → (ℕ → E → ℂ) → (E → ℂ) → ℕ → ℝ≥0∞

noncomputable def complexSupErrorValue : complexSupErrorType :=
  fun F f n => ⨆ x, ENNReal.ofReal ‖F n x - f x‖

def realSupErrorIsLUB : Prop :=
  ∀ {E : Type u} (F : ℕ → E → ℝ) (f : E → ℝ) (n : ℕ),
    IsLUB (Set.range (fun x => ENNReal.ofReal |F n x - f x|)) (realSupErrorValue F f n)

def complexSupErrorIsLUB : Prop :=
  ∀ {E : Type u} (F : ℕ → E → ℂ) (f : E → ℂ) (n : ℕ),
    IsLUB (Set.range (fun x => ENNReal.ofReal ‖F n x - f x‖)) (complexSupErrorValue F f n)

def realSupErrorEmpty : Prop :=
  ∀ {E : Type u} [IsEmpty E] (F : ℕ → E → ℝ) (f : E → ℝ) (n : ℕ),
    realSupErrorValue F f n = 0

def complexSupErrorEmpty : Prop :=
  ∀ {E : Type u} [IsEmpty E] (F : ℕ → E → ℂ) (f : E → ℂ) (n : ℕ),
    complexSupErrorValue F f n = 0

def realUniformConvergesIffSupError : Prop :=
  ∀ {E : Type u} (F : ℕ → E → ℝ) (f : E → ℝ),
    Uniform.realUniformConvergesValue F f ↔
      Filter.Tendsto (realSupErrorValue F f) Filter.atTop (𝓝 0)

def complexUniformConvergesIffSupError : Prop :=
  ∀ {E : Type u} (F : ℕ → E → ℂ) (f : E → ℂ),
    Uniform.complexUniformConvergesValue F f ↔
      Filter.Tendsto (complexSupErrorValue F f) Filter.atTop (𝓝 0)

def realSupErrorEventuallyFinite : Prop :=
  ∀ {E : Type u} (F : ℕ → E → ℝ) (f : E → ℝ),
    Uniform.realUniformConvergesValue F f →
      ∃ N : ℕ, ∀ n ≥ N, realSupErrorValue F f n < ⊤

def complexSupErrorEventuallyFinite : Prop :=
  ∀ {E : Type u} (F : ℕ → E → ℂ) (f : E → ℂ),
    Uniform.complexUniformConvergesValue F f →
      ∃ N : ℕ, ∀ n ≥ N, complexSupErrorValue F f n < ⊤

end Specs.SingleVariableAnalysis.Ch12.SupNorm
