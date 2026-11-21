import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.ClosedForm
import Mathlib.Analysis.Normed.Operator.Bilinear

noncomputable section
open scoped InnerProductSpace
universe u v
namespace P201.Heat

/-- A bounded symmetric coercive real form on a densely and continuously
embedded Hilbert space. No compactness or separability is required. -/
structure CoerciveForm (V : Type u) (H : Type v)
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] where
  j : V →L[ℝ] H
  injective : Function.Injective j
  dense : DenseRange j
  a : V →L[ℝ] V →L[ℝ] ℝ
  symmetric : ∀ x y, a x y = a y x
  coercive : ∃ c : ℝ, 0 < c ∧ ∀ x, c * ‖x‖ ^ 2 ≤ a x x

namespace CoerciveForm
variable {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  (d : CoerciveForm V H)

/-- The range is given its ambient subspace structure at this stage. -/
def rangeEquiv : V ≃ₗ[ℝ] LinearMap.range d.j.toLinearMap :=
  LinearEquiv.ofInjective d.j.toLinearMap d.injective

/-- The paper's form transported to its actual image in H. -/
def denseForm : P201.Elliptic.DenseForm ℝ H where
  domain := LinearMap.range d.j.toLinearMap
  dense := d.dense
  form := LinearMap.mk₂ ℝ
    (fun x y => d.a (d.rangeEquiv.symm x) (d.rangeEquiv.symm y))
    (by intros; simp) (by intros; simp) (by intros; simp) (by intros; simp)

theorem denseForm_hermitian : d.denseForm.IsHermitian := by
  intro x y
  exact d.symmetric _ _

theorem denseForm_nonnegative : d.denseForm.IsNonnegative := by
  intro x
  obtain ⟨c, hc, hb⟩ := d.coercive
  exact le_trans (mul_nonneg hc.le (sq_nonneg _)) (hb _)

/-- The shared energy space carries the shifted form norm. -/
def energyForm := d.denseForm.toNonnegative d.denseForm_hermitian d.denseForm_nonnegative

/-- Algebraic transport; continuity in the energy norm is a conclusion. -/
def toEnergy : V ≃ₗ[ℝ] d.energyForm.EnergySpace := d.rangeEquiv

/-- The very same canonical associated operator used for closed forms. -/
def operator : ExpandedFA.Unbounded.Operator ℝ H H := d.denseForm.associatedOperator

end CoerciveForm

namespace FormOperatorExpected
variable {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Exact graph, domain, action and uniqueness, using the original injection. -/
def ExactOperator (d : CoerciveForm V H) : Prop :=
  (∀ x h : H, (x, h) ∈ d.operator.graph ↔
    ∃ v : V, d.j v = x ∧ ∀ w : V, d.a v w = inner ℝ (d.j w) h) ∧
  (∀ x : H, x ∈ d.operator.domain ↔
    ∃ v : V, d.j v = x ∧ ∃ h : H, ∀ w : V, d.a v w = inner ℝ (d.j w) h) ∧
  (∀ (v : V) (h k : H),
    (∀ w : V, d.a v w = inner ℝ (d.j w) h) →
    (∀ w : V, d.a v w = inner ℝ (d.j w) k) → h = k) ∧
  (∀ (v : V) (h : H) (hv : d.j v ∈ d.operator.domain),
    (∀ w : V, d.a v w = inner ℝ (d.j w) h) → d.operator ⟨d.j v, hv⟩ = h)

/-- Equivalence with the original V norm, exact energy identity and completeness. -/
def EnergyIdentification (d : CoerciveForm V H) : Prop :=
  (∃ e : V ≃L[ℝ] d.energyForm.EnergySpace,
    (∀ v : V, e v = d.toEnergy v) ∧
    (∀ v : V, d.energyForm.inclusion (e v) = d.j v) ∧
    (∀ v : V, ‖e v‖ ^ 2 = d.a v v + ‖d.j v‖ ^ 2)) ∧
  d.energyForm.IsClosed

/-- Operator properties and the actual shifted inverse bounded into V.
The final condition uses compactness of the original injection. -/
def Representation [CompleteSpace H] (d : CoerciveForm V H) : Prop :=
  Dense (d.operator.domain : Set H) ∧
  d.operator = d.operator.adjoint ∧
  (∀ x : d.operator.domain, 0 ≤ inner ℝ (x : H) (d.operator x)) ∧
  ∃ K : H →L[ℝ] V,
    (∀ (f : H) (v : V),
      (∀ w : V, d.a v w + inner ℝ (d.j w) (d.j v) = inner ℝ (d.j w) f) ↔ v = K f) ∧
    (∀ x f : H, (x, f - x) ∈ d.operator.graph ↔ d.j (K f) = x) ∧
    (IsCompactOperator d.j → IsCompactOperator (d.j.comp K))

/-- Universally quantified exact-operator obligation. -/
def ExactTheorem : Prop :=
  ∀ {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (d : CoerciveForm V H), ExactOperator d

/-- Universally quantified completeness and norm-equivalence obligation. -/
def EnergyTheorem : Prop :=
  ∀ {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (d : CoerciveForm V H), EnergyIdentification d

/-- The full operator/compactness stage for arbitrary real Hilbert embeddings. -/
def RepresentationTheorem : Prop :=
  ∀ {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (d : CoerciveForm V H), Representation d

end FormOperatorExpected
end P201.Heat
