import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch08.RationalIntegrals

/-! Independent statements of paper.tex:2091–2126, D12.08.05.
The conditional integral is represented by its two ordinary tails, each
with its own cutoff. No Bochner integral of a conditionally integrable
function, or principal value in place of an ordinary integral, is used.
For a reduced rational quotient, no real poles means the denominator
does not vanish anywhere on the real axis. Distinct denominator roots
index the residue sums, including poles of arbitrary multiplicity. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace Specs.D12Complex.Ch08.OscillatoryIntegrals
open _root_.D12Complex

def oscillatory_tails_exist_type : Prop :=
  ∀ P Q : Polynomial ℂ, IsCoprime P Q →
    (∀ x : ℝ, Q.eval (x : ℂ) ≠ 0) → P.degree < Q.degree →
    ∀ c : ℝ, c ≠ 0 → ∀ d : ℝ, ∃ Lminus Lplus : ℂ,
      Tendsto (fun a : ℝ => ∫ x in a..d,
        Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) *
          (P.eval (x : ℂ) / Q.eval (x : ℂ))) atBot (𝓝 Lminus) ∧
      Tendsto (fun b : ℝ => ∫ x in d..b,
        Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) *
          (P.eval (x : ℂ) / Q.eval (x : ℂ))) atTop (𝓝 Lplus)

def oscillatory_upper_residues_type : Prop :=
  ∀ P Q : Polynomial ℂ, IsCoprime P Q →
    (∀ x : ℝ, Q.eval (x : ℂ) ≠ 0) → P.degree < Q.degree →
    ∀ c : ℝ, 0 < c → ∀ (d : ℝ) (Lminus Lplus : ℂ),
      Tendsto (fun a : ℝ => ∫ x in a..d,
        Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) *
          (P.eval (x : ℂ) / Q.eval (x : ℂ))) atBot (𝓝 Lminus) →
      Tendsto (fun b : ℝ => ∫ x in d..b,
        Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) *
          (P.eval (x : ℂ) / Q.eval (x : ℂ))) atTop (𝓝 Lplus) →
      Lminus + Lplus = (2 * Real.pi * Complex.I : ℂ) *
        ∑ a ∈ Q.roots.toFinset.filter (fun a => 0 < a.im),
          Residue.residue
            (fun z => Complex.exp (Complex.I * (c : ℂ) * z) * (P.eval z / Q.eval z)) a

def oscillatory_lower_residues_type : Prop :=
  ∀ P Q : Polynomial ℂ, IsCoprime P Q →
    (∀ x : ℝ, Q.eval (x : ℂ) ≠ 0) → P.degree < Q.degree →
    ∀ c : ℝ, c < 0 → ∀ (d : ℝ) (Lminus Lplus : ℂ),
      Tendsto (fun a : ℝ => ∫ x in a..d,
        Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) *
          (P.eval (x : ℂ) / Q.eval (x : ℂ))) atBot (𝓝 Lminus) →
      Tendsto (fun b : ℝ => ∫ x in d..b,
        Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) *
          (P.eval (x : ℂ) / Q.eval (x : ℂ))) atTop (𝓝 Lplus) →
      Lminus + Lplus = -(2 * Real.pi * Complex.I : ℂ) *
        ∑ a ∈ Q.roots.toFinset.filter (fun a => a.im < 0),
          Residue.residue
            (fun z => Complex.exp (Complex.I * (c : ℂ) * z) * (P.eval z / Q.eval z)) a

/-- Absolute convergence, with no restriction on the real frequency. -/
def oscillatory_integrable_type : Prop :=
  ∀ P Q : Polynomial ℂ, IsCoprime P Q →
    (∀ x : ℝ, Q.eval (x : ℂ) ≠ 0) → P.degree + 2 ≤ Q.degree →
    ∀ c : ℝ, Integrable (fun x : ℝ =>
      Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) *
        (P.eval (x : ℂ) / Q.eval (x : ℂ)))

/-- Both norm tails converge independently in the absolutely convergent case. -/
def oscillatory_absolute_tails_type : Prop :=
  ∀ P Q : Polynomial ℂ, IsCoprime P Q →
    (∀ x : ℝ, Q.eval (x : ℂ) ≠ 0) → P.degree + 2 ≤ Q.degree →
    ∀ c d : ℝ,
      Tendsto (fun a : ℝ => ∫ x in a..d,
        ‖Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) *
          (P.eval (x : ℂ) / Q.eval (x : ℂ))‖) atBot
        (𝓝 (∫ x in Iic d, ‖P.eval (x : ℂ) / Q.eval (x : ℂ)‖)) ∧
      Tendsto (fun b : ℝ => ∫ x in d..b,
        ‖Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) *
          (P.eval (x : ℂ) / Q.eval (x : ℂ))‖) atTop
        (𝓝 (∫ x in Ioi d, ‖P.eval (x : ℂ) / Q.eval (x : ℂ)‖))

/-- This formula includes c = 0, and uses an absolutely convergent integral. -/
def cosine_kernel_type : Prop :=
  ∀ b : ℝ, 0 < b → ∀ c : ℝ,
    Integrable (fun x : ℝ => Real.cos (c * x) / (x ^ 2 + b ^ 2)) ∧
    (∫ x : ℝ, Real.cos (c * x) / (x ^ 2 + b ^ 2)) =
      (Real.pi / b) * Real.exp (-b * |c|)

end Specs.D12Complex.Ch08.OscillatoryIntegrals
