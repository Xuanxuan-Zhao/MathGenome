import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Integral
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Independent specification of K03.09.minkowski (paper.tex:2640–2662).
The integral is the proper Darboux integral on an ordered compact interval,
including a singleton. Real exponents p ≥ 1 are allowed, and no positivity
of any integral or seminorm is assumed. Values are defined on actual functions.
The point-supported examples use nondegenerate intervals and have a nonzero
value at the left endpoint, while every p-seminorm vanishes.
-/
namespace Specs.SingleVariableAnalysis.Ch09.Minkowski
open Specs.SingleVariableAnalysis.Ch08.Integral

abbrev lpSeminormType := {K : Type} → [Norm K] → (f : ℝ → K) →
  {a b : ℝ} → (p : ℝ) → realIntegrableValue (fun x => ‖f x‖ ^ p) a b → ℝ

noncomputable def lpSeminormValue : lpSeminormType := fun {_} [_] f {_ _} p hf =>
  realIntegralValue (fun x => ‖f x‖ ^ p) hf ^ (1 / p)

/-- The algebraic seminorm properties in addition to the triangle inequality. -/
def seminormLaws : Prop :=
  ∀ {K : Type} [NormedField K] (p : ℝ), 1 ≤ p →
    ∀ {f : ℝ → K} {a b : ℝ}
      (hf : realIntegrableValue (fun x => ‖f x‖ ^ p) a b),
      0 ≤ lpSeminormValue f p hf ∧
      ∀ c : K, ∃ hc : realIntegrableValue (fun x => ‖c * f x‖ ^ p) a b,
        lpSeminormValue (fun x => c * f x) p hc = ‖c‖ * lpSeminormValue f p hf

def zeroSeminorm : Prop :=
  ∀ {K : Type} [NormedField K] (p : ℝ), 1 ≤ p →
    ∀ {a b : ℝ}, a ≤ b →
      ∃ hz : realIntegrableValue (fun _ : ℝ => ‖(0 : K)‖ ^ p) a b,
        lpSeminormValue (fun _ => (0 : K)) p hz = 0

def minkowskiEstimate {K : Type} [Norm K] (f g : ℝ → K)
    [Add K] (a b p : ℝ) : Prop :=
  ∃ hf : realIntegrableValue (fun x => ‖f x‖ ^ p) a b,
  ∃ hg : realIntegrableValue (fun x => ‖g x‖ ^ p) a b,
  ∃ hs : realIntegrableValue (fun x => ‖f x + g x‖ ^ p) a b,
    lpSeminormValue (fun x => f x + g x) p hs ≤
      lpSeminormValue f p hf + lpSeminormValue g p hg

def realMinkowski : Prop :=
  ∀ p : ℝ, 1 ≤ p → ∀ {f g : ℝ → ℝ} {a b : ℝ},
    realIntegrableValue f a b → realIntegrableValue g a b →
    minkowskiEstimate f g a b p

def complexMinkowski : Prop :=
  ∀ p : ℝ, 1 ≤ p → ∀ {f g : ℝ → ℂ} {a b : ℝ},
    complexIntegrableValue f a b → complexIntegrableValue g a b →
    minkowskiEstimate f g a b p

abbrev pointSpikeType := {K : Type} → [Zero K] → K → ℝ → ℝ → K
noncomputable def pointSpikeValue : pointSpikeType := fun {_} [_] c a x =>
  if x = a then c else 0

def realPointSpike : Prop :=
  ∀ a b : ℝ, a < b → ∀ c : ℝ, c ≠ 0 →
    pointSpikeValue c a a ≠ 0 ∧
    (∀ x : ℝ, x ≠ a → pointSpikeValue c a x = 0) ∧
    ∃ _hi : realIntegrableValue (pointSpikeValue c a) a b,
      ∀ p : ℝ, 1 ≤ p →
        ∃ hp : realIntegrableValue (fun x => ‖pointSpikeValue c a x‖ ^ p) a b,
          lpSeminormValue (pointSpikeValue c a) p hp = 0

def complexPointSpike : Prop :=
  ∀ a b : ℝ, a < b → ∀ c : ℂ, c ≠ 0 →
    pointSpikeValue c a a ≠ 0 ∧
    (∀ x : ℝ, x ≠ a → pointSpikeValue c a x = 0) ∧
    ∃ _hi : complexIntegrableValue (pointSpikeValue c a) a b,
      ∀ p : ℝ, 1 ≤ p →
        ∃ hp : realIntegrableValue (fun x => ‖pointSpikeValue c a x‖ ^ p) a b,
          lpSeminormValue (pointSpikeValue c a) p hp = 0

end Specs.SingleVariableAnalysis.Ch09.Minkowski
