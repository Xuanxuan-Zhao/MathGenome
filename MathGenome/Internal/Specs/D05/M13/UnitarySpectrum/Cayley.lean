import MathGenome.Internal.Specs.D05.M13.UnitarySpectrum
import Mathlib.Algebra.GroupWithZero.Units.Basic

/-! Independent statements for the Cayley supplement, paper.tex:2321–2341.
`Ring.inverse` is the total ring inverse; each denominator is proved to be a
unit under exactly the hypotheses of the source. No positive dimension is assumed. -/
noncomputable section
namespace Specs.D05.M13.UnitarySpectrum.Cayley
universe u

abbrev transform_type : Type (u + 1) :=
  {V : Type u} → [NormedAddCommGroup V] → [InnerProductSpace ℂ V] →
    Module.End ℂ V → Module.End ℂ V

def cayley_value : transform_type := fun T =>
  (T - Complex.I • 1) * Ring.inverse (T + Complex.I • 1)

def inverseCayley_value : transform_type := fun U =>
  Complex.I • ((1 + U) * Ring.inverse (1 - U))

def alternate_value : transform_type := fun T =>
  (1 - Complex.I • T) * Ring.inverse (1 + Complex.I • T)

def forward : Prop :=
  ∀ {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : Module.End ℂ V),
    _root_.D05.selfAdjoint T →
      IsUnit (T + Complex.I • 1) ∧
      _root_.D05.IsUnitaryMap (cayley_value T) ∧ IsUnit (1 - cayley_value T)

def backward : Prop :=
  ∀ {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (U : Module.End ℂ V),
    _root_.D05.IsUnitaryMap U → IsUnit (1 - U) →
      _root_.D05.selfAdjoint (inverseCayley_value U)

def left_inverse : Prop :=
  ∀ {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : Module.End ℂ V),
    _root_.D05.selfAdjoint T → inverseCayley_value (cayley_value T) = T

def right_inverse : Prop :=
  ∀ {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (U : Module.End ℂ V),
    _root_.D05.IsUnitaryMap U → IsUnit (1 - U) →
      cayley_value (inverseCayley_value U) = U

/-- A bijection with precisely the displayed formulas in both directions. -/
def bijection : Prop :=
  ∀ (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V],
    ∃ e : {T : Module.End ℂ V // _root_.D05.selfAdjoint T} ≃
      {U : Module.End ℂ V // _root_.D05.IsUnitaryMap U ∧ IsUnit (1 - U)},
      (∀ T, (e T).val = cayley_value T.val) ∧
      (∀ U, (e.symm U).val = inverseCayley_value U.val)

def alternate_forward : Prop :=
  ∀ {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : Module.End ℂ V),
    _root_.D05.selfAdjoint T → IsUnit (1 + Complex.I • T) ∧
      _root_.D05.IsUnitaryMap (alternate_value T) ∧ IsUnit (1 + alternate_value T)

def excluded_eigenvalues : Prop :=
  ∀ {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : Module.End ℂ V),
    _root_.D05.selfAdjoint T →
      ¬ (cayley_value T).HasEigenvalue 1 ∧ ¬ (alternate_value T).HasEigenvalue (-1)

end Specs.D05.M13.UnitarySpectrum.Cayley
