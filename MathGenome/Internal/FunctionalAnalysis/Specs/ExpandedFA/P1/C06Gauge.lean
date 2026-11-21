import Mathlib.Analysis.Convex.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic

/-!
Independent specification of the Minkowski functional,
`paper.tex:1041–1047`, definition `fa2:p1:c06:gauge`.

The ambient space is an arbitrary real vector space. Dilations are images
under real scalar multiplication, and the infimum uses strictly positive
scales. Absorption has precisely the manuscript's meaning: one such scale
exists for each vector. The admissibility predicate records absorption,
real convexity, and membership of zero, without a topology or a norm.

The defining formula is totalized to arbitrary sets using the real `sInf`.
For absorbing sets its scale set is nonempty and bounded below by zero;
`gaugeIsGLBType` specifies that it is then the ordinary real infimum.
-/

namespace ExpandedFA.P1.C06GaugeSpec

universe u
open scoped Pointwise

/-- Type of the positive dilation scales. -/
def scalesType : Type (u + 1) :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E], Set E → E → Set ℝ

/-- `tU` is the image of `U` under `y ↦ t • y`. -/
def scalesValue : scalesType.{u} :=
  fun {_} _ _ U x => {t : ℝ | 0 < t ∧ x ∈ t • U}

/-- Type of a predicate on subsets of an arbitrary real vector space. -/
def setPredicateType : Type (u + 1) :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E], Set E → Prop

/-- The manuscript's absorption condition. -/
def absorbingValue : setPredicateType.{u} :=
  fun {_} _ _ U => ∀ x, ({t : ℝ | 0 < t ∧ x ∈ t • U}).Nonempty

/-- Exactly the hypotheses of the source definition. -/
def admissibleValue : setPredicateType.{u} :=
  fun {E} _ _ U =>
    (∀ x, ({t : ℝ | 0 < t ∧ x ∈ t • U}).Nonempty) ∧
      Convex ℝ U ∧ (0 : E) ∈ U

/-- Type of the real-valued Minkowski functional. -/
def gaugeType : Type (u + 1) :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E], Set E → E → ℝ

/-- The prescribed positive-scale infimum. -/
noncomputable def gaugeValue : gaugeType.{u} :=
  fun {_} _ _ U x => sInf {t : ℝ | 0 < t ∧ x ∈ t • U}

/-- On the source domain the formula is a greatest lower bound in `ℝ`.
Absorption alone suffices for this well-definedness assertion. -/
def gaugeIsGLBType : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] (U : Set E),
    (∀ x, ({t : ℝ | 0 < t ∧ x ∈ t • U}).Nonempty) →
    ∀ x, IsGLB {t : ℝ | 0 < t ∧ x ∈ t • U} (gaugeValue U x)

end ExpandedFA.P1.C06GaugeSpec
