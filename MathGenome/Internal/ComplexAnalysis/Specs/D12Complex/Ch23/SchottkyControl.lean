import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Sqrt

/-!
Independent statement of Schottky control, paper.tex:4213–4245.
All regularity and omitted-value conditions concern the open source disk.
The conclusion includes its proper closed subdisks, including radius zero.
The bound is an ordinary real number given by the source's explicit formula.
-/

noncomputable section

namespace Specs.D12Complex.Ch23.SchottkyControl
open _root_.D12Complex Metric

def Astar_type := ℝ → ℝ
def Astar_value : Astar_type := fun A => max 2 A

def C0_type := ℝ → ℝ
def C0_value : C0_type := fun A => 1 + Real.log (Astar_value A) / (2 * Real.pi)

def K_type := ℝ → ℝ
def K_value : K_type := fun A => Real.sqrt (C0_value A) + Real.sqrt (C0_value A + 1)

def C_type := ℝ → ℝ → ℝ
def C_value : C_type := fun A r =>
  1 + Real.exp (Real.pi * Real.exp
    (2 * (Real.log (K_value A) + Real.pi + 128 * r / (1 - r))))

def constant_gt_one_type : Prop := ∀ A r : ℝ, 1 < C_value A r

def unit_disk_type : Prop :=
  ∀ (A r : ℝ), 0 < A → 0 ≤ r → r < 1 →
    ∀ f : ℂ → ℂ, HolomorphicOn (ball 0 1) f →
      (∀ z ∈ ball (0 : ℂ) 1, f z ≠ 0) →
      (∀ z ∈ ball (0 : ℂ) 1, f z ≠ 1) →
      ‖f 0‖ ≤ A → ∀ z : ℂ, ‖z‖ ≤ r → ‖f z‖ ≤ C_value A r

def scaled_type : Prop :=
  ∀ (a : ℂ) (R A r : ℝ), 0 < R → 0 < A → 0 ≤ r → r < 1 →
    ∀ f : ℂ → ℂ, HolomorphicOn (ball a R) f →
      (∀ z ∈ ball a R, f z ≠ 0) →
      (∀ z ∈ ball a R, f z ≠ 1) →
      ‖f a‖ ≤ A → ∀ z : ℂ, ‖z - a‖ ≤ r * R → ‖f z‖ ≤ C_value A r

end Specs.D12Complex.Ch23.SchottkyControl
