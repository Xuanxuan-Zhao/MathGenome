import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch08.Residue
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! Independent statements for the real rational integral in
paper.tex:2020–2029, 2042–2049 and 2068–2070 (D12.08.04).

The degree inequality uses `degree`, including the zero polynomial.
For a reduced quotient, absence of real poles is exactly nonvanishing of
the denominator on the real axis. The finite residue sum uses distinct
denominator roots, so repeated poles occur once, with their full residue.
The ordinary one-sided limits are stated explicitly, also for the norm.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace Specs.D12Complex.Ch08.RationalIntegrals
open _root_.D12Complex

def rational_integrable_type : Prop :=
  ∀ P Q : Polynomial ℂ, IsCoprime P Q →
    (∀ x : ℝ, Q.eval (x : ℂ) ≠ 0) → P.degree + 2 ≤ Q.degree →
    Integrable (fun x : ℝ => P.eval (x : ℂ) / Q.eval (x : ℂ))

/-- This statement specifies both ordinary tails at every splitting point,
and the absolute convergence of each, rather than only symmetric cutoffs. -/
def rational_improper_tails_type : Prop :=
  ∀ P Q : Polynomial ℂ, IsCoprime P Q →
    (∀ x : ℝ, Q.eval (x : ℂ) ≠ 0) → P.degree + 2 ≤ Q.degree →
    ∀ c : ℝ,
      Tendsto (fun a : ℝ => ∫ x in a..c, P.eval (x : ℂ) / Q.eval (x : ℂ))
        atBot (𝓝 (∫ x in Iic c, P.eval (x : ℂ) / Q.eval (x : ℂ))) ∧
      Tendsto (fun b : ℝ => ∫ x in c..b, P.eval (x : ℂ) / Q.eval (x : ℂ))
        atTop (𝓝 (∫ x in Ioi c, P.eval (x : ℂ) / Q.eval (x : ℂ))) ∧
      Tendsto (fun a : ℝ => ∫ x in a..c, ‖P.eval (x : ℂ) / Q.eval (x : ℂ)‖)
        atBot (𝓝 (∫ x in Iic c, ‖P.eval (x : ℂ) / Q.eval (x : ℂ)‖)) ∧
      Tendsto (fun b : ℝ => ∫ x in c..b, ‖P.eval (x : ℂ) / Q.eval (x : ℂ)‖)
        atTop (𝓝 (∫ x in Ioi c, ‖P.eval (x : ℂ) / Q.eval (x : ℂ)‖)) ∧
      (∫ x : ℝ, P.eval (x : ℂ) / Q.eval (x : ℂ)) =
        (∫ x in Iic c, P.eval (x : ℂ) / Q.eval (x : ℂ)) +
        (∫ x in Ioi c, P.eval (x : ℂ) / Q.eval (x : ℂ))

def rational_integral_residues_type : Prop :=
  ∀ P Q : Polynomial ℂ, IsCoprime P Q →
    (∀ x : ℝ, Q.eval (x : ℂ) ≠ 0) → P.degree + 2 ≤ Q.degree →
    (∫ x : ℝ, P.eval (x : ℂ) / Q.eval (x : ℂ)) =
      (2 * Real.pi * Complex.I : ℂ) *
        ∑ a ∈ Q.roots.toFinset.filter (fun a => 0 < a.im),
          Residue.residue (fun z => P.eval z / Q.eval z) a

def cauchy_kernel_integrable_type : Prop :=
  Integrable (fun x : ℝ => (1 + x ^ 2)⁻¹)

def cauchy_kernel_integral_type : Prop :=
  (∫ x : ℝ, (1 + x ^ 2)⁻¹) = Real.pi

end Specs.D12Complex.Ch08.RationalIntegrals
