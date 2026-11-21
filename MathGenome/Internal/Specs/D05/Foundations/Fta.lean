import MathGenome.Internal.Specs.D05.Foundations.FtaMinimum
import Mathlib.Algebra.Polynomial.Roots

/-! Independent obligations for paper.tex:399–422. Nonconstancy is positive
natural degree; all polynomials are formal coefficient objects. The intermediate
expansion and descent retain the elementary first-term argument. -/
namespace D05.Specs.Fta
open Polynomial Filter

def coercivity : Prop := ∀ p : Polynomial ℂ, 0 < p.natDegree →
  Tendsto (fun z : ℂ => ‖p.eval z‖) (comap (fun z : ℂ => ‖z‖) atTop) atTop

def globalMinimum : Prop := ∀ p : Polynomial ℂ, 0 < p.natDegree →
  ∃ z₀ : ℂ, ∀ z : ℂ, ‖p.eval z₀‖ ≤ ‖p.eval z‖

/-- The normalized translated polynomial has a first nonconstant term and
an actual polynomial remainder beginning one degree later. -/
def firstTermExpansion : Prop := ∀ (p : Polynomial ℂ), 0 < p.natDegree →
  ∀ z₀ : ℂ, p.eval z₀ ≠ 0 →
  ∃ (m : ℕ) (a : ℂ) (r : Polynomial ℂ), 0 < m ∧ a ≠ 0 ∧
    C (p.eval z₀)⁻¹ * p.comp (X + C z₀) =
      1 + C a * X ^ m + X ^ (m + 1) * r

/-- A complex m-th root selects a direction of decrease. The constant bounds
the entire polynomial tail uniformly for real parameters between zero and one. -/
def descentEstimate : Prop := ∀ (m : ℕ) (a : ℂ) (r : Polynomial ℂ),
  0 < m → a ≠ 0 → ∃ (u : ℂ) (B : ℝ),
  a * u ^ m = -1 ∧ 0 ≤ B ∧ ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    ‖1 + a * ((t : ℂ) * u) ^ m +
      ((t : ℂ) * u) ^ (m + 1) * r.eval ((t : ℂ) * u)‖ ≤
      1 - t ^ m + B * t ^ (m + 1)

def strictDescent : Prop := ∀ (p : Polynomial ℂ), 0 < p.natDegree →
  ∀ z₀ : ℂ, p.eval z₀ ≠ 0 → ∃ z : ℂ, ‖p.eval z‖ < ‖p.eval z₀‖

def minimumZero : Prop := ∀ (p : Polynomial ℂ), 0 < p.natDegree →
  ∀ z₀ : ℂ, (∀ z : ℂ, ‖p.eval z₀‖ ≤ ‖p.eval z‖) → p.eval z₀ = 0

def existsRoot : Prop := ∀ (p : Polynomial ℂ), 0 < p.natDegree →
  ∃ z : ℂ, p.eval z = 0

/-- Multiplicities are retained by the multiset. Nonzero constants are included
with an empty product and their leading scalar; zero is explicitly excluded. -/
def linearFactorization : Prop := ∀ (p : Polynomial ℂ), p ≠ 0 →
  ∃ zs : Multiset ℂ, zs.card = p.natDegree ∧
    p = C p.leadingCoeff * (zs.map (fun z => (X : Polynomial ℂ) - C z)).prod

end D05.Specs.Fta
