import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.C0SemigroupAndGenerator
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C02HilbertSum
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
The first example at `fa2:p3:growth-spectral-gap`, paper.tex 14627–14656.
Block number `n : ℕ` represents manuscript block number `n+1`, so no
zero-dimensional block is substituted for the first block. The direct sum
is precisely the canonical upstream `lp Block 2`, with its square-sum norm.

The blockwise operator is initially defined on its maximal square-summable
image domain. `DomainIdentification` is the additional obligation that this
domain equals the weighted domain displayed in the manuscript. No generation,
resolvent, or estimate is a field of this construction.
-/

noncomputable section
open scoped ENNReal NNReal

namespace ExpandedFA.Semigroups.GrowthGap

abbrev Block (n : ℕ) := EuclideanSpace ℂ (Fin (n + 1))
abbrev Space := P1.C02HilbertSum.Spec.Space Block

/-- The forward shift sends the first coordinate to zero and shifts the rest. -/
def shiftLinear (n : ℕ) : Block n →ₗ[ℂ] Block n where
  toFun x := WithLp.toLp 2 (fun j =>
    if h : 0 < j.val then x ⟨j.val - 1, by omega⟩ else 0)
  map_add' x y := by
    ext j
    dsimp
    split <;> simp
  map_smul' c x := by
    ext j
    dsimp
    split <;> simp

def shift (n : ℕ) : Block n →L[ℂ] Block n :=
  (shiftLinear n).toContinuousLinearMap

/-- The eigenvalue in manuscript block `n+1`. -/
def eigenvalue (n : ℕ) : ℂ := -1 + (n + 1 : ℕ) * Complex.I

def blockGenerator (n : ℕ) : Block n →L[ℂ] Block n :=
  eigenvalue n • ContinuousLinearMap.id ℂ (Block n) + shift n

def domain : Submodule ℂ Space where
  carrier := {x | Memℓp (fun n => blockGenerator n (x n)) 2}
  zero_mem' := by
    change Memℓp (fun n => blockGenerator n ((0 : Space) n)) 2
    convert (zero_memℓp : Memℓp (0 : ∀ n, Block n) 2) using 1
    ext n
    simp
  add_mem' := by
    intro x y hx hy
    change Memℓp (fun n => blockGenerator n ((x + y) n)) 2
    convert hx.add hy using 1
    ext n
    simp
  smul_mem' := by
    intro c x hx
    change Memℓp (fun n => blockGenerator n ((c • x) n)) 2
    convert hx.const_smul c using 1
    ext n
    simp

def operator : Unbounded.Operator ℂ Space Space where
  domain := domain
  toFun :=
    { toFun := fun x => ⟨fun n => blockGenerator n (x.val n), x.property⟩
      map_add' := by intro x y; apply lp.ext; funext n; exact map_add _ _ _
      map_smul' := by intro c x; apply lp.ext; funext n; exact (blockGenerator n).map_smul c (x.val n) }

/-- The exact (unrestricted) weighted square-summability condition. -/
def weightedDomain : Set Space :=
  {x | Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ 2 * ‖x n‖ ^ 2)}

namespace Spec

def ShiftContractive : Prop := ∀ n (x : Block n), ‖shift n x‖ ≤ ‖x‖
def ShiftNilpotent : Prop := ∀ n, (shift n) ^ (n + 1) = 0
def DomainIdentification : Prop := (operator.domain : Set Space) = weightedDomain
def SpectrumIdentification : Prop :=
  C0SemigroupSpec.spectrumValue operator = Set.range eigenvalue
def SpectralBound : Prop :=
  C0SemigroupSpec.spectralBoundValue operator = (-1 : EReal)

/-- All required infinite-dimensional semigroup conclusions, including
equality with the concrete exact-domain generator,
contractivity, the exact norm at time zero as well, and the growth bound. -/
def SemigroupConclusion : Prop :=
  ∃ T : C0Semigroup ℂ Space,
    C0SemigroupSpec.generatesValue operator T ∧
    C0SemigroupSpec.exponentialBoundValue T 1 0 ∧
    (∀ t : ℝ≥0, ‖T.operators t‖ = 1) ∧
    C0SemigroupSpec.growthBoundValue T = (0 : EReal)

def Counterexample : Prop :=
  DomainIdentification ∧ SpectrumIdentification ∧ SpectralBound ∧ SemigroupConclusion

end Spec
end ExpandedFA.Semigroups.GrowthGap
