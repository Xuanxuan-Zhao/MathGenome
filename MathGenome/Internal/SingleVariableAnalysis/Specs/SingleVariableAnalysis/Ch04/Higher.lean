import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch04.OneSided
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch04.Peano
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! Independent specification of K03.04.higher (paper.tex:718–725).
All derivatives have base field ℝ, including complex-valued functions.
k-times differentiability requires existence through order k, not continuity
of the highest derivative. Compact regularity uses continuous derivative
extensions with within derivative relations; endpoint and interior bridges
below specify their meaning independently of the implementation. -/

namespace Specs.SingleVariableAnalysis.Ch04.Higher
open Set Filter
open scoped Topology ContDiff
universe u
set_option linter.unusedVariables false

def realIteratedDerivativeType : Type (u + 1) :=
  ∀ {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (j : ℕ) (f : ℝ → F), ℝ → F

noncomputable def realIteratedDerivativeValue {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (j : ℕ) (f : ℝ → F) : ℝ → F := iteratedDeriv j f

def kTimesDifferentiableOnType : Type (u + 1) :=
  ∀ {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (k : ℕ) (f : ℝ → F) (I : Set ℝ), Prop

noncomputable def kTimesDifferentiableOnValue {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (k : ℕ) (f : ℝ → F) (I : Set ℝ) : Prop :=
  ∀ j : ℕ, j < k → ∀ x ∈ I, DifferentiableAt ℝ (realIteratedDerivativeValue j f) x

def ckOnType : Type (u + 1) :=
  ∀ {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (k : ℕ) (f : ℝ → F) (I : Set ℝ), Prop

noncomputable def ckOnValue {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (k : ℕ) (f : ℝ → F) (I : Set ℝ) : Prop :=
  kTimesDifferentiableOnValue k f I ∧
    ∀ j : ℕ, j ≤ k → ContinuousOn (realIteratedDerivativeValue j f) I

def smoothOnType : Type (u + 1) :=
  ∀ {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : ℝ → F) (I : Set ℝ), Prop

noncomputable def smoothOnValue {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : ℝ → F) (I : Set ℝ) : Prop := ∀ k : ℕ, ckOnValue k f I

def closedDerivativeFamilyType : Type (u + 1) :=
  ∀ {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (k : ℕ) (f : ℝ → F) (a b : ℝ) (D : ℕ → ℝ → F), Prop

noncomputable def closedDerivativeFamilyValue {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (k : ℕ) (f : ℝ → F) (a b : ℝ) (D : ℕ → ℝ → F) : Prop :=
  EqOn (D 0) f (Icc a b) ∧
    (∀ j : ℕ, j ≤ k → ContinuousOn (D j) (Icc a b)) ∧
    ∀ j : ℕ, j < k → ∀ x ∈ Icc a b, HasDerivWithinAt (D j) (D (j + 1) x) (Icc a b) x

def ckOnClosedType : Type (u + 1) :=
  ∀ {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (k : ℕ) (f : ℝ → F) (a b : ℝ), Prop

noncomputable def ckOnClosedValue {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (k : ℕ) (f : ℝ → F) (a b : ℝ) : Prop :=
  ∃ D : ℕ → ℝ → F, closedDerivativeFamilyValue k f a b D

def smoothOnClosedType : Type (u + 1) :=
  ∀ {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : ℝ → F) (a b : ℝ), Prop

noncomputable def smoothOnClosedValue {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : ℝ → F) (a b : ℝ) : Prop := ∀ k : ℕ, ckOnClosedValue k f a b

def realIteratedDerivative_zero : Prop :=
  ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F),
    realIteratedDerivativeValue 0 f = f

def realIteratedDerivative_succ : Prop :=
  ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (j : ℕ) (f : ℝ → F),
    realIteratedDerivativeValue (j + 1) f = deriv (realIteratedDerivativeValue j f)

def kTimesDifferentiableOn_zero : Prop :=
  ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (I : Set ℝ),
    kTimesDifferentiableOnValue 0 f I

def kTimesDifferentiableOn_succ_iff : Prop :=
  ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (k : ℕ) (f : ℝ → F) (I : Set ℝ),
    kTimesDifferentiableOnValue (k + 1) f I ↔
      kTimesDifferentiableOnValue k f I ∧
        ∀ x ∈ I, DifferentiableAt ℝ (realIteratedDerivativeValue k f) x

def kTimesDifferentiableOn_iff_increment : Prop :=
  ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (k : ℕ) (f : ℝ → F) (I : Set ℝ),
    kTimesDifferentiableOnValue k f I ↔
      ∀ j : ℕ, j < k → ∀ x ∈ I,
        Derivative.hasRealIncrementDerivativeValue (realIteratedDerivativeValue j f)
          (realIteratedDerivativeValue (j + 1) f x) x

def kTimesDifferentiableOn_continuous_lower : Prop :=
  ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (k : ℕ) (f : ℝ → F) (I : Set ℝ)
    (h : kTimesDifferentiableOnValue k f I) (j : ℕ) (hj : j < k),
    ContinuousOn (realIteratedDerivativeValue j f) I

def ckOn_iff_contDiffOn : Prop :=
  ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (k : ℕ) (f : ℝ → F) (I : Set ℝ) (hI : IsOpen I),
    ckOnValue k f I ↔ ContDiffOn ℝ k f I

def smoothOn_iff_contDiffOn : Prop :=
  ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (I : Set ℝ) (hI : IsOpen I),
    smoothOnValue f I ↔ ContDiffOn ℝ ∞ f I

def ckOn_zero_iff : Prop :=
  ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (I : Set ℝ),
    ckOnValue 0 f I ↔ ContinuousOn f I

def withinIncrementDerivative_iff_hasDerivWithinAt : Prop :=
  ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (L : F)
    (I : Set ℝ) (x : ℝ),
    Derivative.hasRealIncrementDerivativeWithinValue f L I x ↔ HasDerivWithinAt f L I x

def closedDerivativeFamily_iff_sides : Prop :=
  ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (k : ℕ) (f : ℝ → F) (a b : ℝ)
    (hab : a < b) (D : ℕ → ℝ → F),
    closedDerivativeFamilyValue k f a b D ↔
      EqOn (D 0) f (Icc a b) ∧
        (∀ j : ℕ, j ≤ k → ContinuousOn (D j) (Icc a b)) ∧
        ∀ j : ℕ, j < k →
          (∀ x ∈ Ioo a b, HasDerivAt (D j) (D (j + 1) x) x) ∧
          OneSided.hasRightRealIncrementDerivativeWithinValue (D j) (D (j + 1) a) (Icc a b) a ∧
          OneSided.hasLeftRealIncrementDerivativeWithinValue (D j) (D (j + 1) b) (Icc a b) b

def closedDerivativeFamily_eq_iteratedDerivWithin : Prop :=
  ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (k : ℕ) (f : ℝ → F)
    (a b : ℝ) (hab : a < b) (D : ℕ → ℝ → F)
    (h : closedDerivativeFamilyValue k f a b D) (j : ℕ) (hj : j ≤ k),
    EqOn (D j) (iteratedDerivWithin j f (Icc a b)) (Icc a b)

def closedDerivativeFamily_eq_interior : Prop :=
  ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (k : ℕ) (f : ℝ → F) (a b : ℝ)
    (D : ℕ → ℝ → F) (h : closedDerivativeFamilyValue k f a b D) (j : ℕ) (hj : j ≤ k),
    EqOn (D j) (realIteratedDerivativeValue j f) (Ioo a b)

def ckOnClosed_iff_contDiffOn : Prop :=
  ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (k : ℕ) (f : ℝ → F) (a b : ℝ) (hab : a < b),
    ckOnClosedValue k f a b ↔ ContDiffOn ℝ k f (Icc a b)

def smoothOnClosed_iff_contDiffOn : Prop :=
  ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (a b : ℝ) (hab : a < b),
    smoothOnClosedValue f a b ↔ ContDiffOn ℝ ∞ f (Icc a b)

def ckOnClosed_zero_iff : Prop :=
  ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (a b : ℝ),
    ckOnClosedValue 0 f a b ↔ ContinuousOn f (Icc a b)

def realIteratedDerivative_congr_on_open : Prop :=
  ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f g : ℝ → F) (I : Set ℝ)
    (hI : IsOpen I) (hfg : EqOn f g I) (j : ℕ),
    EqOn (realIteratedDerivativeValue j f) (realIteratedDerivativeValue j g) I

def kTimesDifferentiableOn_congr : Prop :=
  ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (k : ℕ) (f g : ℝ → F) (I : Set ℝ)
    (hI : IsOpen I) (hfg : EqOn f g I),
    kTimesDifferentiableOnValue k f I ↔ kTimesDifferentiableOnValue k g I

def ckOn_congr : Prop :=
  ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (k : ℕ) (f g : ℝ → F) (I : Set ℝ)
    (hI : IsOpen I) (hfg : EqOn f g I),
    ckOnValue k f I ↔ ckOnValue k g I

def ckOnClosed_congr : Prop :=
  ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (k : ℕ) (f g : ℝ → F) (a b : ℝ)
    (hfg : EqOn f g (Icc a b)),
    ckOnClosedValue k f a b ↔ ckOnClosedValue k g a b

def ckOnClosed_singleton : Prop :=
  ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (k : ℕ) (f : ℝ → F) (a : ℝ),
    ckOnClosedValue k f a a

def ckOnClosed_iff_contDiffOn_le : Prop :=
  ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (k : ℕ) (f : ℝ → F) (a b : ℝ) (hab : a ≤ b),
    ckOnClosedValue k f a b ↔ ContDiffOn ℝ k f (Icc a b)

def smoothOnClosed_iff_contDiffOn_le : Prop :=
  ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (a b : ℝ) (hab : a ≤ b),
    smoothOnClosedValue f a b ↔ ContDiffOn ℝ ∞ f (Icc a b)

end Specs.SingleVariableAnalysis.Ch04.Higher
