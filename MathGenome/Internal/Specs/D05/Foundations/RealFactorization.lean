import MathGenome.Internal.Specs.D05.Foundations.Fta
import MathGenome.Internal.Specs.D05.Foundations.Factorization

/-! Independent statements for the real-factorization paragraph, paper.tex:417.
All products are multiset products of formal polynomials, retaining repetitions.
The scalar and empty products include every nonzero constant polynomial. -/

noncomputable section

namespace D05.Foundations
open Polynomial

/-- The real quadratic obtained by pairing a complex number with its conjugate. -/
def conjugateQuadratic (z : ℂ) : Polynomial ℝ :=
  X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2)

end D05.Foundations

namespace D05.Specs.RealFactorization
open Polynomial D05.Foundations

def conjugateRoots : Prop := ∀ (p : Polynomial ℝ) (z : ℂ),
  (p.map (algebraMap ℝ ℂ)).IsRoot (starRingEnd ℂ z) ↔
    (p.map (algebraMap ℝ ℂ)).IsRoot z

def conjugateMultiplicity : Prop := ∀ (p : Polynomial ℝ) (z : ℂ),
  (p.map (algebraMap ℝ ℂ)).rootMultiplicity (starRingEnd ℂ z) =
    (p.map (algebraMap ℝ ℂ)).rootMultiplicity z

def conjugatePair : Prop := ∀ z : ℂ,
  (conjugateQuadratic z).map (algebraMap ℝ ℂ) =
    (X - C z) * (X - C (starRingEnd ℂ z))

def quadraticProperties : Prop := ∀ z : ℂ, z.im ≠ 0 →
  (conjugateQuadratic z).Monic ∧ (conjugateQuadratic z).natDegree = 2 ∧
    (2 * z.re) ^ 2 - 4 * ‖z‖ ^ 2 < 0

def realFactorization : Prop := ∀ p : Polynomial ℝ, p ≠ 0 →
  ∃ (c : ℝ) (rs : Multiset ℝ) (zs : Multiset ℂ),
    c ≠ 0 ∧ (∀ z ∈ zs, z.im ≠ 0) ∧
      p = C c * (rs.map (fun r => (X : Polynomial ℝ) - C r)).prod *
        (zs.map conjugateQuadratic).prod

/-- Nonzero constants have the requested factorization with both lists empty. -/
def constantFactorization : Prop := ∀ c : ℝ, c ≠ 0 →
  C c = C c * ((0 : Multiset ℝ).map
    (fun r => (X : Polynomial ℝ) - C r)).prod *
      ((0 : Multiset ℂ).map conjugateQuadratic).prod

end D05.Specs.RealFactorization
