import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.AcDefinition
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.BvDefinition
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Independent obligations for paper.tex:3994–4022. The variation is the
accepted classical partition variation, with its real value after finiteness
has been proved. All scalar closure statements include both ℝ and ℂ. -/

open Set
open scoped BigOperators NNReal

namespace Specs.D11.Ch12.AcBasic

abbrev AC {𝕂 : Type*} [RCLike 𝕂] (F : ℝ → 𝕂) (a b : ℝ) :=
  Specs.D11.Ch12.absolutelyContinuousOnIntervalValue F a b

def uniformContinuousOn : Prop :=
  ∀ {𝕂 : Type*} [RCLike 𝕂] {F : ℝ → 𝕂} {a b : ℝ}, a ≤ b → AC F a b →
    UniformContinuousOn F (Icc a b)

def bv : Prop :=
  ∀ {𝕂 : Type*} [RCLike 𝕂] {F : ℝ → 𝕂} {a b : ℝ}, a ≤ b → AC F a b →
    Specs.D11.Ch12.BV_value F a b

/-- No BV hypothesis is added; it follows from AC. On the interval all
variation values are finite, so `toReal` is the source real variation function. -/
def variation_ac : Prop :=
  ∀ {𝕂 : Type*} [RCLike 𝕂] {F : ℝ → 𝕂} {a b : ℝ}, a ≤ b → AC F a b →
    AC (fun x => (Specs.D11.Ch12.variationFunction_value F a x).toReal) a b

def add : Prop :=
  ∀ {𝕂 : Type*} [RCLike 𝕂] {F G : ℝ → 𝕂} {a b : ℝ}, a ≤ b →
    AC F a b → AC G a b → AC (fun x => F x + G x) a b

def const_mul : Prop :=
  ∀ {𝕂 : Type*} [RCLike 𝕂] (c : 𝕂) {F : ℝ → 𝕂} {a b : ℝ}, a ≤ b →
    AC F a b → AC (fun x => c * F x) a b

def finite_linear_combination : Prop :=
  ∀ {𝕂 : Type*} [RCLike 𝕂] {ι : Type*} (t : Finset ι) (c : ι → 𝕂)
    (F : ι → ℝ → 𝕂) {a b : ℝ}, a ≤ b → (∀ i ∈ t, AC (F i) a b) →
      AC (fun x => ∑ i ∈ t, c i * F i x) a b

def mul : Prop :=
  ∀ {𝕂 : Type*} [RCLike 𝕂] {F G : ℝ → 𝕂} {a b : ℝ}, a ≤ b →
    AC F a b → AC G a b → AC (fun x => F x * G x) a b

/-- Arbitrary real domains include compact intervals and the whole real line. -/
def lipschitzOn : Prop :=
  ∀ {𝕂 : Type*} [RCLike 𝕂] {F : ℝ → 𝕂} {s : Set ℝ} {L : ℝ≥0},
    LipschitzOnWith L F s → Specs.D11.Ch12.absolutelyContinuousOnValue F s

def sqrt_ac : Prop := AC Real.sqrt 0 1

def sqrt_not_lipschitz : Prop :=
  ¬ ∃ L : ℝ≥0, LipschitzOnWith L Real.sqrt (Icc (0 : ℝ) 1)

end Specs.D11.Ch12.AcBasic
