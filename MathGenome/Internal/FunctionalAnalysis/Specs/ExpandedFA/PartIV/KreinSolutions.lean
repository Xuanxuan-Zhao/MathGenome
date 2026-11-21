import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.BigOperators.Fin

/-! Independent statements for the scalar functions preceding `fa2:p4:krein-kernel`.
Positive definiteness below is the real scalar notion, including symmetry.
It is a condition on a kernel, not a claim about every continuous even function. -/
noncomputable section
open scoped BigOperators

namespace ExpandedFA.PartIV.KreinSolutions.Specs

def CValue (μ t : ℝ) : ℝ :=
  if μ < 0 then Real.cos (Real.sqrt (-μ) * t)
  else if μ = 0 then 1 else Real.cosh (Real.sqrt μ * t)

def SValue (μ t : ℝ) : ℝ :=
  if μ < 0 then Real.sin (Real.sqrt (-μ) * t) / Real.sqrt (-μ)
  else if μ = 0 then t else Real.sinh (Real.sqrt μ * t) / Real.sqrt μ

def KernelPlusValue (F : ℝ → ℝ) (s t : ℝ) : ℝ := (F (s - t) + F (s + t)) / 2

def KernelMinusValue (F : ℝ → ℝ) (s t : ℝ) : ℝ := (F (s - t) - F (s + t)) / 2

/-- Nonnegative finite quadratic sums together with real Hermitian symmetry. -/
def PositiveDefiniteValue (K : ℝ → ℝ → ℝ) : Prop :=
  (∀ s t, K s t = K t s) ∧
  ∀ (n : ℕ) (x a : Fin n → ℝ), 0 ≤ ∑ i, ∑ j, a i * a j * K (x i) (x j)

def ScalarFunctionType := ℝ → ℝ → ℝ

def KernelType := (ℝ → ℝ) → ℝ → ℝ → ℝ

def PositiveDefiniteType := (ℝ → ℝ → ℝ) → Prop

def Parity : Prop := ∀ μ, Function.Even (CValue μ) ∧ Function.Odd (SValue μ)

def FirstDerivatives : Prop := ∀ μ t,
  HasDerivAt (CValue μ) (μ * SValue μ t) t ∧ HasDerivAt (SValue μ) (CValue μ t) t

def SecondDerivatives : Prop := ∀ μ t,
  HasDerivAt (deriv (CValue μ)) (μ * CValue μ t) t ∧
  HasDerivAt (deriv (SValue μ)) (μ * SValue μ t) t

def InitialData : Prop := ∀ μ,
  CValue μ 0 = 1 ∧ deriv (CValue μ) 0 = 0 ∧
  SValue μ 0 = 0 ∧ deriv (SValue μ) 0 = 1

def AdditionSum : Prop := ∀ μ s t,
  CValue μ (s - t) + CValue μ (s + t) = 2 * CValue μ s * CValue μ t

def AdditionDifference : Prop := ∀ μ s t,
  CValue μ (s - t) - CValue μ (s + t) = -2 * μ * SValue μ s * SValue μ t

def KernelRegularity : Prop := ∀ (F : ℝ → ℝ), Continuous F → Function.Even F →
  (Continuous (fun p : ℝ × ℝ => KernelPlusValue F p.1 p.2) ∧
    ∀ s t, KernelPlusValue F s t = KernelPlusValue F t s) ∧
  (Continuous (fun p : ℝ × ℝ => KernelMinusValue F p.1 p.2) ∧
    ∀ s t, KernelMinusValue F s t = KernelMinusValue F t s)

end ExpandedFA.PartIV.KreinSolutions.Specs
