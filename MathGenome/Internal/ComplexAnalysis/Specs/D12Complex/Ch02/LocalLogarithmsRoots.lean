import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch02.PrincipalLogarithm

/-! Independent statements of the local branches theorem, paper.tex:471–488.
The ambient holomorphy set is open but need not be connected. The branches
are total representatives, with their identities restricted to neighborhoods.
The inverse statements include both inverse laws and both range inclusions. -/

namespace Specs.D12Complex.Ch02.LocalLogarithmsRoots

open _root_.D12Complex

def local_logarithm_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℂ → ℂ) (a c : ℂ),
    HolomorphicOn Ω f → a ∈ Ω → f a ≠ 0 → E c = f a →
    ∃ (U : Set ℂ) (L : ℂ → ℂ),
      a ∈ U ∧ U ⊆ Ω ∧ HolomorphicOn U L ∧ L a = c ∧
      (∀ z ∈ U, E (L z) = f z) ∧
      (∀ z ∈ U, HasDerivAt L (deriv f z / f z) z)

def local_root_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℂ → ℂ) (a : ℂ) (n : ℕ) (c₀ : ℂ),
    HolomorphicOn Ω f → a ∈ Ω → f a ≠ 0 → 0 < n → c₀ ^ n = f a →
    ∃ (U : Set ℂ) (g : ℂ → ℂ),
      a ∈ U ∧ U ⊆ Ω ∧ HolomorphicOn U g ∧ g a = c₀ ∧
      ∀ z ∈ U, (g z) ^ n = f z

def exponential_local_inverse_type : Prop :=
  ∀ (b c : ℂ), E c = b →
    ∃ (U V : Set ℂ) (L : ℂ → ℂ),
      c ∈ U ∧ b ∈ V ∧ L b = c ∧
      BiholomorphicPair U V E L ∧
      ∀ w ∈ V, HasDerivAt L (1 / w) w

def power_local_inverse_type : Prop :=
  ∀ (n : ℕ) (c₀ : ℂ), 0 < n → c₀ ≠ 0 →
    ∃ (U V : Set ℂ) (g : ℂ → ℂ),
      c₀ ∈ U ∧ c₀ ^ n ∈ V ∧ g (c₀ ^ n) = c₀ ∧
      BiholomorphicPair U V (fun z => z ^ n) g

end Specs.D12Complex.Ch02.LocalLogarithmsRoots
