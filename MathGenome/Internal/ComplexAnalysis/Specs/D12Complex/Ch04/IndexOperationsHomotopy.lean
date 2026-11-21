import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch04.WindingIndex
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch04.HomotopyIntegrals

/-! Index operations, paper.tex:975–1002. Path index is the index of the
one-term integral chain, using exactly the canonical integral-based index.
All meaningful index comparisons are made off the participating traces.
Arbitrary compact parameter intervals and degenerate intervals are allowed.
The homotopy has only continuity and the closed-loop side condition. -/
noncomputable section
open Set
open scoped unitInterval

namespace D12Complex.PiecewiseC1Path

def index (γ : PiecewiseC1Path) (a : ℂ) : ℂ :=
  IntegralChain.index (Finsupp.single γ (1 : ℤ)) a

end D12Complex.PiecewiseC1Path

namespace Specs.D12Complex.Ch04.IndexOperationsHomotopy
open _root_.D12Complex

def pathIndex_type := PiecewiseC1Path → ℂ → ℂ

def pathIndex_value : pathIndex_type := fun γ a =>
  IntegralChain.index (Finsupp.single γ (1 : ℤ)) a

def path_index_eq_integral_type : Prop :=
  ∀ (γ : PiecewiseC1Path) (a : ℂ), a ∉ γ.trace →
    γ.index a = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
      γ.integral (fun z => 1 / (z - a))

def chain_index_add_type : Prop :=
  ∀ (Γ Δ : IntegralChain) (a : ℂ), a ∉ Γ.trace → a ∉ Δ.trace →
    IntegralChain.index (Γ + Δ) a = Γ.index a + Δ.index a

def chain_index_neg_type : Prop :=
  ∀ (Γ : IntegralChain) (a : ℂ), a ∉ Γ.trace →
    IntegralChain.index (-Γ) a = -Γ.index a

def chain_index_sub_type : Prop :=
  ∀ (Γ Δ : IntegralChain) (a : ℂ), a ∉ Γ.trace → a ∉ Δ.trace →
    IntegralChain.index (Γ - Δ) a = Γ.index a - Δ.index a

def chain_zero_index_type : Prop := ∀ a : ℂ, (0 : IntegralChain).index a = 0

def cycle_zero_index_type : Prop := ∀ a : ℂ, (0 : IntegralCycle).index a = 0

def path_index_const_type : Prop :=
  ∀ (u v : ℝ) (huv : u ≤ v) (z a : ℂ), a ≠ z →
    (PiecewiseC1Path.const u v huv z).index a = 0

def path_index_degenerate_type : Prop :=
  ∀ (γ : PiecewiseC1Path) (a : ℂ), γ.path.a = γ.path.b → a ∉ γ.trace →
    γ.index a = 0

/-- Every representative of the reverse traversal has opposite index.
The assertion holds even without closedness of the input path. -/
def path_index_reversal_type : Prop :=
  ∀ (γ η : PiecewiseC1Path) (a : ℂ),
    η.path.a = γ.path.a → η.path.b = γ.path.b →
    EqOn η (fun t => γ (γ.path.a + γ.path.b - t)) (Icc η.path.a η.path.b) →
    a ∉ γ.trace → η.index a = -γ.index a

/-- Concatenation by arbitrary nonnegative affine traversals, including flat
and zero-duration pieces. This stronger statement also covers open paths. -/
def path_index_concatenation_type : Prop :=
  ∀ (γ₁ γ₂ η : PiecewiseC1Path) (c p₁ q₁ p₂ q₂ : ℝ) (a : ℂ),
    c ∈ Icc η.path.a η.path.b → 0 ≤ q₁ → 0 ≤ q₂ →
    γ₁.path.target = γ₂.path.source →
    p₁ + q₁ * η.path.a = γ₁.path.a → p₁ + q₁ * c = γ₁.path.b →
    p₂ + q₂ * c = γ₂.path.a → p₂ + q₂ * η.path.b = γ₂.path.b →
    EqOn η (fun t => γ₁ (p₁ + q₁ * t)) (Icc η.path.a c) →
    EqOn η (fun t => γ₂ (p₂ + q₂ * t)) (Icc c η.path.b) →
    a ∉ γ₁.trace → a ∉ γ₂.trace → η.index a = γ₁.index a + γ₂.index a

/-- A reversed closed path exists, avoids the same point, and has opposite index. -/
def closed_reversal_exists_type : Prop :=
  ∀ (γ : PiecewiseC1Path) (a : ℂ), γ.IsClosed → a ∉ γ.trace →
    ∃ η : PiecewiseC1Path, η.path.a = γ.path.a ∧ η.path.b = γ.path.b ∧
      EqOn η (fun t => γ (γ.path.a + γ.path.b - t)) (Icc γ.path.a γ.path.b) ∧
      η.IsClosed ∧ a ∉ η.trace ∧ η.index a = -γ.index a

/-- Compatible closed paths admit a closed concatenation avoiding a. -/
def closed_concatenation_exists_type : Prop :=
  ∀ (γ₁ γ₂ : PiecewiseC1Path) (a : ℂ), γ₁.IsClosed → γ₂.IsClosed →
    γ₁.path.target = γ₂.path.source → a ∉ γ₁.trace → a ∉ γ₂.trace →
    ∃ η : PiecewiseC1Path, η.path.a = 0 ∧ η.path.b = 2 ∧
      EqOn η (fun t => γ₁ (γ₁.path.a + (γ₁.path.b - γ₁.path.a) * t)) (Icc 0 1) ∧
      EqOn η (fun t => γ₂ (γ₂.path.a + (γ₂.path.b - γ₂.path.a) * (t - 1))) (Icc 1 2) ∧
      η.IsClosed ∧ a ∉ η.trace ∧ η.index a = γ₁.index a + γ₂.index a

def free_loop_index_type : Prop :=
  ∀ (γ₀ γ₁ : PiecewiseC1Path) (a : ℂ),
    a ∉ γ₀.trace → a ∉ γ₁.trace → γ₀.IsClosed → γ₁.IsClosed →
    ∀ H : C(I × I, ℂ), (∀ p, H p ≠ a) →
      (∀ t : I, H (0, t) = γ₀ (γ₀.path.a + (γ₀.path.b - γ₀.path.a) * (t : ℝ))) →
      (∀ t : I, H (1, t) = γ₁ (γ₁.path.a + (γ₁.path.b - γ₁.path.a) * (t : ℝ))) →
      (∀ s : I, H (s, 0) = H (s, 1)) → γ₀.index a = γ₁.index a

end Specs.D12Complex.Ch04.IndexOperationsHomotopy
