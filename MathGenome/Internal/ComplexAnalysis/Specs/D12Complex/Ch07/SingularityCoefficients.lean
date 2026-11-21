import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch07.Laurent
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch07.Singularities

/-! Coefficient classification in paper.tex:1678–1700. The outer radius may be
infinite. The coefficient hypothesis is an actual two-sided Laurent expansion;
no extension or finite principal part is included in that hypothesis. -/
open scoped ENNReal

namespace Specs.D12Complex.Ch07.SingularityCoefficients
open _root_.D12Complex _root_.D12Complex.Laurent

def removable_iff_type : Prop :=
  ∀ (f : ℂ → ℂ) (a : ℂ) (R : ℝ≥0∞) (c : ℤ → ℂ),
    0 < R → HolomorphicOn (annulus a 0 R) f → HasLaurentSeriesOn f a 0 R c →
    (RemovableSingularityAt f a ↔ ∀ n : ℤ, n < 0 → c n = 0)

def poleOfOrder_iff_type : Prop :=
  ∀ (f : ℂ → ℂ) (a : ℂ) (R : ℝ≥0∞) (c : ℤ → ℂ),
    0 < R → HolomorphicOn (annulus a 0 R) f → HasLaurentSeriesOn f a 0 R c →
    ∀ m : ℕ, 1 ≤ m →
      (PoleOfOrderAt f a m ↔ c (-(m : ℤ)) ≠ 0 ∧
        ∀ n : ℤ, n < -(m : ℤ) → c n = 0)

def essential_iff_type : Prop :=
  ∀ (f : ℂ → ℂ) (a : ℂ) (R : ℝ≥0∞) (c : ℤ → ℂ),
    0 < R → HolomorphicOn (annulus a 0 R) f → HasLaurentSeriesOn f a 0 R c →
    (EssentialSingularityAt f a ↔ {n : ℤ | n < 0 ∧ c n ≠ 0}.Infinite)

def pole_order_unique_type : Prop :=
  ∀ (f : ℂ → ℂ) (a : ℂ) (m k : ℕ),
    PoleOfOrderAt f a m → PoleOfOrderAt f a k → m = k

/-- The alternatives are pairwise exclusive; the pole has a unique exact order. -/
def singularity_trichotomy_type : Prop :=
  ∀ (f : ℂ → ℂ) (a : ℂ), IsolatedSingularityAt f a →
    (RemovableSingularityAt f a ∧ ¬PoleAt f a ∧ ¬EssentialSingularityAt f a) ∨
    ((∃! m : ℕ, PoleOfOrderAt f a m) ∧ ¬RemovableSingularityAt f a ∧
      ¬EssentialSingularityAt f a) ∨
    (EssentialSingularityAt f a ∧ ¬RemovableSingularityAt f a ∧ ¬PoleAt f a)

end Specs.D12Complex.Ch07.SingularityCoefficients
