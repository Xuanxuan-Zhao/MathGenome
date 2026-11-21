import Mathlib.Basic.Complex.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
Independent specification of `thm:algebraic-fta`, paper.tex:7596–7614.
The field is the usual constructed complex field. Algebraic closedness is
a conclusion, never a hypothesis. Positive degree excludes both zero and
constant polynomials. The multiset in the factorization has exactly the
specified degree; repetitions are allowed and each factor `X - C z` is
monic linear. The scalar is the polynomial's nonzero leading coefficient.
These declarations state propositions only; they do not import a complex
FTA proof or a candidate implementation.
-/

namespace Specs.D07.Appendix.AlgebraicFta

open Polynomial

/-- Every positive-degree complex polynomial has a complex zero. -/
def RootExistence : Prop :=
  ∀ f : Polynomial ℂ, 0 < f.degree → ∃ z : ℂ, f.eval z = 0

/-- The same assertion with nonconstancy expressed without a degree convention. -/
def NonconstantRootExistence : Prop :=
  ∀ f : Polynomial ℂ, (∀ c : ℂ, f ≠ C c) → ∃ z : ℂ, f.eval z = 0

def AlgebraicClosedness : Prop := IsAlgClosed ℂ

/-- Exactly `n` monic linear factors, including repeated roots. -/
def LinearFactorization : Prop :=
  ∀ (f : Polynomial ℂ) (n : ℕ), 1 ≤ n → f.natDegree = n →
    f.leadingCoeff ≠ 0 ∧ ∃ s : Multiset ℂ,
      s.card = n ∧ (∀ z ∈ s, f.eval z = 0) ∧
      f = C f.leadingCoeff * (s.map (fun z => X - C z)).prod

def RootIffAlgebraicClosedness : Prop := RootExistence ↔ AlgebraicClosedness

def RootIffLinearFactorization : Prop := RootExistence ↔ LinearFactorization

end Specs.D07.Appendix.AlgebraicFta
