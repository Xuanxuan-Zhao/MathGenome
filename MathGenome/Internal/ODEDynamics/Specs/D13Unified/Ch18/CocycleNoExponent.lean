import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch18.GrowthDefinitions
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch17.ShiftSpaces
import Mathlib.Data.Nat.Find
import Mathlib.Analysis.SpecialFunctions.Exp

/-! The blocks are numbered from zero internally: block `j` has the paper's
length L_(j+1) = 2^(2^(j+1)). The first block is zero. -/
noncomputable section
open Filter
open scoped Topology BigOperators
namespace Specs.D13Unified.Ch18.CocycleNoExponent
open Specs.D13Unified.Ch17.ShiftSpaces
open Specs.D13Unified.Ch18.GrowthDefinitions

def blockLength (j : ℕ) : ℕ := 2 ^ (2 ^ (j + 1))
def endpoint (j : ℕ) : ℕ := ∑ k ∈ Finset.range j, blockLength k

def blockIndex (i : ℕ) : ℕ := Nat.findGreatest (fun j => endpoint j ≤ i) i

def basePoint : OneSided := fun i => ⟨blockIndex i % 2, Nat.mod_lt _ (by decide)⟩

def scalar (s : OneSided) : ℝ := Real.exp ((s 0).val : ℝ)
def generator (s : OneSided) : ℝ →L[ℝ] ℝ := scalar s • ContinuousLinearMap.id ℝ ℝ

def logAverage (s : OneSided) (n : ℕ) : ℝ :=
  Real.log (∏ k ∈ Finset.range n, scalar (shiftPlus^[k] s)) / n

def blockLengthType := ℕ → ℕ
def endpointType := ℕ → ℕ
def blockIndexType := ℕ → ℕ
def basePointType := OneSided
def scalarType := OneSided → ℝ
def generatorType := OneSided → ℝ →L[ℝ] ℝ
def logAverageType := OneSided → ℕ → ℝ

def regularityStatement : Prop :=
  Continuous scalar ∧ Continuous generator ∧
  (∀ s, 1 ≤ scalar s ∧ scalar s ≤ Real.exp 1) ∧
  (∀ s, Function.Bijective (generator s)) ∧
  (∃ C : ℝ, ∀ s, ‖generator s‖ ≤ C) ∧
  (∃ C : ℝ, ∀ s, ‖(scalar s)⁻¹ • ContinuousLinearMap.id ℝ ℝ‖ ≤ C)

def blocksStatement : Prop :=
  ∀ j i, endpoint j ≤ i → i < endpoint (j+1) → (basePoint i).val = j % 2

def earlierProportionStatement : Prop :=
  Tendsto (fun j => (endpoint j : ℝ) / blockLength j) atTop (𝓝 0)

def productFormulaStatement : Prop :=
  ∀ (s : OneSided) (n : ℕ) (v : ℝ),
    cocycleProduct shiftPlus generator n s v =
      Real.exp (∑ k ∈ Finset.range n, ((s k).val : ℝ)) * v

def rateFormulaStatement : Prop :=
  ∀ (s : OneSided) (v : ℝ) (hv : v ≠ 0) (n : ℕ) (hn : 0 < n),
    cocycleDirectionalRate shiftPlus generator s v hv n hn = (logAverage s n : EReal)

def subsequencesStatement : Prop :=
  Tendsto (fun j => endpoint (2*j+1)) atTop atTop ∧
  Tendsto (fun j => endpoint (2*j+2)) atTop atTop ∧
  Tendsto (fun j => logAverage basePoint (endpoint (2*j+1))) atTop (𝓝 0) ∧
  Tendsto (fun j => logAverage basePoint (endpoint (2*j+2))) atTop (𝓝 1)

def noExponentStatement : Prop :=
  ∀ (v : ℝ) (hv : v ≠ 0),
    (¬ ∃ a : EReal, HasCocycleDirectionalExponent shiftPlus generator basePoint v hv a) ∧
    cocycleDirectionalExponent shiftPlus generator basePoint v hv = none
end Specs.D13Unified.Ch18.CocycleNoExponent
