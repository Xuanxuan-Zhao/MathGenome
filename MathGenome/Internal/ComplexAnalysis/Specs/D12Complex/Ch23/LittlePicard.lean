import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.Basic

/-!
Independent statements of Little Picard, paper.tex:4199–4211 (D12.23.02).
Entire means the canonical weak holomorphy predicate on the whole complex
plane. Nonconstancy excludes every constant function. The last conclusion
says directly that the set of omitted finite values has at most one member.
Neither growth bounds nor normality hypotheses are imposed.
-/

namespace Specs.D12Complex.Ch23.LittlePicard
open _root_.D12Complex

def omits_zero_one_constant_type : Prop :=
  ∀ (f : ℂ → ℂ), HolomorphicOn Set.univ f →
    (∀ z : ℂ, f z ≠ 0) → (∀ z : ℂ, f z ≠ 1) →
    ∃ c : ℂ, ∀ z : ℂ, f z = c

def omits_two_constant_type : Prop :=
  ∀ (f : ℂ → ℂ) (a b : ℂ), HolomorphicOn Set.univ f → a ≠ b →
    (∀ z : ℂ, f z ≠ a) → (∀ z : ℂ, f z ≠ b) →
    ∃ c : ℂ, ∀ z : ℂ, f z = c

def little_picard_type : Prop :=
  ∀ (f : ℂ → ℂ), HolomorphicOn Set.univ f →
    (¬ ∃ c : ℂ, ∀ z : ℂ, f z = c) →
    Set.Subsingleton ((Set.range f)ᶜ)

end Specs.D12Complex.Ch23.LittlePicard
