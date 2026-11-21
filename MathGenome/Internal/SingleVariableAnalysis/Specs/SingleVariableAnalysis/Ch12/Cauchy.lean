import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch12.Uniform

/-!
Independent specification of `K03.12.cauchy` (paper.tex:1212–1219).
The domain is any type, so an arbitrary set is represented by its subtype.
There is no nonemptiness, boundedness, continuity, or topology hypothesis
on the domain or the functions. In particular the empty set is included.
Indices follow the upstream convention: `F n` is term `n + 1`.
The limit is a function with values in the same canonical scalar field.
-/

namespace Specs.SingleVariableAnalysis.Ch12.Cauchy

universe u

def realUniformCauchyCriterion : Prop :=
  ∀ {E : Type u} (F : ℕ → E → ℝ),
    (∃ f : E → ℝ, Uniform.realUniformConvergesValue F f) ↔
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
        ∀ m ≥ N, ∀ n ≥ N, ∀ x, |F n x - F m x| < ε

def complexUniformCauchyCriterion : Prop :=
  ∀ {E : Type u} (F : ℕ → E → ℂ),
    (∃ f : E → ℂ, Uniform.complexUniformConvergesValue F f) ↔
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
        ∀ m ≥ N, ∀ n ≥ N, ∀ x, ‖F n x - F m x‖ < ε

def realUniformLimitExistsEmpty : Prop :=
  ∀ {E : Type u} [IsEmpty E] (F : ℕ → E → ℝ),
    ∃ f : E → ℝ, Uniform.realUniformConvergesValue F f

def complexUniformLimitExistsEmpty : Prop :=
  ∀ {E : Type u} [IsEmpty E] (F : ℕ → E → ℂ),
    ∃ f : E → ℂ, Uniform.complexUniformConvergesValue F f

end Specs.SingleVariableAnalysis.Ch12.Cauchy
