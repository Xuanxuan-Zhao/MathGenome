import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Rounding.Enclosures

/-! Independent statements for paper.tex, W05 (Outward interval operations).
All operands are exact real values. Directed endpoints are supplied with their
own inequalities; there is no nearest-rounding assumption. Finite-format
endpoint existence is conditional on the two defining sets being nonempty.
-/
namespace NumAnalysis206.Rounding.Specs

def interval_addition : Prop :=
  ∀ (a b c d : ℝ), a ≤ b → c ≤ d →
    ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc c d,
      x + y ∈ Set.Icc (a + c) (b + d)

def interval_subtraction : Prop :=
  ∀ (a b c d : ℝ), a ≤ b → c ≤ d →
    ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc c d,
      x - y ∈ Set.Icc (a - d) (b - c)

def interval_multiplication : Prop :=
  ∀ (a b c d : ℝ), a ≤ b → c ≤ d →
    ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc c d,
      x * y ∈ Set.Icc (min (min (a*c) (a*d)) (min (b*c) (b*d)))
        (max (max (a*c) (a*d)) (max (b*c) (b*d)))

def interval_reciprocal : Prop :=
  ∀ (c d : ℝ), c ≤ d → (0 : ℝ) ∉ Set.Icc c d →
    ∀ y ∈ Set.Icc c d, y ≠ 0 ∧ 1 / y ∈ Set.Icc (1 / d) (1 / c)

def interval_division : Prop :=
  ∀ (a b c d rlo rhi : ℝ), a ≤ b → c ≤ d →
    (0 : ℝ) ∉ Set.Icc c d → rlo ≤ 1 / d → 1 / c ≤ rhi →
    ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc c d, y ≠ 0 →
      x / y ∈ Set.Icc (min (min (a*rlo) (a*rhi)) (min (b*rlo) (b*rhi)))
        (max (max (a*rlo) (a*rhi)) (max (b*rlo) (b*rhi)))

def outward_interval : Prop :=
  ∀ (l u lo hi : ℝ), lo ≤ l → u ≤ hi →
    Set.Icc l u ⊆ Set.Icc lo hi

def outward_addition : Prop :=
  ∀ (a b c d lo hi : ℝ), a ≤ b → c ≤ d →
    lo ≤ a + c → b + d ≤ hi →
    ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc c d, x + y ∈ Set.Icc lo hi

def outward_subtraction : Prop :=
  ∀ (a b c d lo hi : ℝ), a ≤ b → c ≤ d →
    lo ≤ a - d → b - c ≤ hi →
    ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc c d, x - y ∈ Set.Icc lo hi

def outward_multiplication : Prop :=
  ∀ (a b c d lo hi : ℝ), a ≤ b → c ≤ d →
    lo ≤ min (min (a*c) (a*d)) (min (b*c) (b*d)) →
    max (max (a*c) (a*d)) (max (b*c) (b*d)) ≤ hi →
    ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc c d, x * y ∈ Set.Icc lo hi

def outward_reciprocal : Prop :=
  ∀ (c d lo hi : ℝ), c ≤ d → (0 : ℝ) ∉ Set.Icc c d →
    lo ≤ 1 / d → 1 / c ≤ hi →
    ∀ y ∈ Set.Icc c d, y ≠ 0 ∧ 1 / y ∈ Set.Icc lo hi

def outward_division : Prop :=
  ∀ (a b c d rlo rhi lo hi : ℝ), a ≤ b → c ≤ d →
    (0 : ℝ) ∉ Set.Icc c d → rlo ≤ 1 / d → 1 / c ≤ rhi →
    lo ≤ min (min (a*rlo) (a*rhi)) (min (b*rlo) (b*rhi)) →
    max (max (a*rlo) (a*rhi)) (max (b*rlo) (b*rhi)) ≤ hi →
    ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc c d, y ≠ 0 → x / y ∈ Set.Icc lo hi

def finite_outward_interval : Prop :=
  ∀ (P : RadixFormat) (l u : ℝ),
    {z : ℝ | z ∈ FValue P ∧ z ≤ l}.Nonempty →
    {z : ℝ | z ∈ FValue P ∧ u ≤ z}.Nonempty →
    ∃ lo hi : ℝ,
      IsGreatest {z : ℝ | z ∈ FValue P ∧ z ≤ l} lo ∧
      IsLeast {z : ℝ | z ∈ FValue P ∧ u ≤ z} hi ∧
      Set.Icc l u ⊆ Set.Icc lo hi

end NumAnalysis206.Rounding.Specs
