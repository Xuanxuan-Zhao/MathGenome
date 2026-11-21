import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.TimeReversal
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.Ring

open scoped BigOperators
open MeasureTheory

universe u
namespace P207.Markov
noncomputable section

/-- Real functions on the finite state space, with the weighted Hilbert norm.
The positive-mass hypothesis is part of the space's parameter. -/
def WeightedSpace {S : Type u} (π : ProbabilityLaw S) (_hπ : ∀ i, 0 < π i) := S → ℝ

namespace WeightedSpace
variable {S : Type u} [Fintype S] (π : ProbabilityLaw S) (hπ : ∀ i, 0 < π i)
instance : AddCommGroup (WeightedSpace π hπ) := inferInstanceAs (AddCommGroup (S → ℝ))
instance : Module ℝ (WeightedSpace π hπ) := inferInstanceAs (Module ℝ (S → ℝ))
instance : CoeFun (WeightedSpace π hπ) (fun _ => S → ℝ) := ⟨fun f => f⟩

/-- The ordinary finite-sum weighted inner product. -/
def weightedInner (f g : WeightedSpace π hπ) : ℝ := ∑ i, (π i).toReal * f i * g i

@[instance_reducible] private def core : InnerProductSpace.Core ℝ (WeightedSpace π hπ) where
  inner := weightedInner π hπ
  conj_inner_symm f g := by
    simp only [weightedInner, conj_trivial]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  re_inner_nonneg f := by
    change 0 ≤ ∑ i, (π i).toReal * f i * f i
    exact Finset.sum_nonneg fun i _ => by
      simpa only [sq, mul_assoc] using mul_nonneg (ENNReal.toReal_nonneg (a := π i)) (sq_nonneg (f i))
  add_left f g k := by
    change (∑ i, (π i).toReal * (f i + g i) * k i) = _
    simp [weightedInner, add_mul, mul_add, Finset.sum_add_distrib]
  smul_left f g r := by
    change (∑ i, (π i).toReal * (r * f i) * g i) = r * _
    simp only [weightedInner, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  definite f hf := by
    change (∑ i, (π i).toReal * f i * f i) = 0 at hf
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ Finset.univ) =>
      show 0 ≤ (π i).toReal * f i * f i by
        simpa only [sq, mul_assoc] using
          mul_nonneg (ENNReal.toReal_nonneg (a := π i)) (sq_nonneg (f i)))).mp hf
    funext i
    have hi := hz i (Finset.mem_univ i)
    have hp : 0 < (π i).toReal := ENNReal.toReal_pos (ne_of_gt (hπ i)) (π.apply_ne_top i)
    change f i = 0
    exact mul_self_eq_zero.mp
      ((mul_eq_zero.mp (by simpa only [mul_assoc] using hi)).resolve_left (ne_of_gt hp))

instance : NormedAddCommGroup (WeightedSpace π hπ) := (core π hπ).toNormedAddCommGroup
instance : InnerProductSpace ℝ (WeightedSpace π hπ) :=
  InnerProductSpace.ofCore (core π hπ).toCore
instance : FiniteDimensional ℝ (WeightedSpace π hπ) :=
  inferInstanceAs (FiniteDimensional ℝ (S → ℝ))
instance : CompleteSpace (WeightedSpace π hπ) := FiniteDimensional.complete ℝ _

/-- The row convention agrees with the original kernel: current state first. -/
def transitionLinear (P : StochasticMatrix S) : WeightedSpace π hπ →ₗ[ℝ] WeightedSpace π hπ where
  toFun f i := ∑ j, realMatrix P i j * f j
  map_add' f g := by
    funext i
    change (∑ j, realMatrix P i j * (f j + g j)) = (∑ j, realMatrix P i j * f j) + ∑ j, realMatrix P i j * g j
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' r f := by
    funext i
    change (∑ j, realMatrix P i j * (r * f j)) = r * _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring

/-- The transition operator on the weighted finite-dimensional space. -/
def transitionOperator (P : StochasticMatrix S) : WeightedSpace π hπ →L[ℝ] WeightedSpace π hπ :=
  (transitionLinear π hπ P).toContinuousLinearMap

/-- The Dirichlet form, with no symmetry assumption built into its definition. -/
def dirichletForm (P : StochasticMatrix S) (f g : WeightedSpace π hπ) : ℝ :=
  inner ℝ f (g - transitionOperator π hπ P g)
end WeightedSpace

namespace ReversibleDirichletFormSpec
open WeightedSpace

def weighted_inner : Prop := ∀ {S : Type u} [Fintype S] (π : ProbabilityLaw S)
  (hπ : ∀ i, 0 < π i) (f g : WeightedSpace π hπ),
  inner ℝ f g = ∑ i, (π i).toReal * f i * g i

def weighted_norm_sq : Prop := ∀ {S : Type u} [Fintype S] (π : ProbabilityLaw S)
  (hπ : ∀ i, 0 < π i) (f : WeightedSpace π hπ),
  ‖f‖ ^ 2 = ∑ i, (π i).toReal * f i * f i

def transition_apply : Prop := ∀ {S : Type u} [Fintype S] (π : ProbabilityLaw S)
  (hπ : ∀ i, 0 < π i) (P : StochasticMatrix S) (f : WeightedSpace π hπ) (i : S),
  transitionOperator π hπ P f i = ∑ j, realMatrix P i j * f j

def reversible_form : Prop := ∀ {S : Type u} [Fintype S] [Nonempty S]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]
  (P : StochasticMatrix S) (π : ProbabilityLaw S) (hπ : ∀ i, 0 < π i),
  Irreducible P → IsReversible P π →
  IsSelfAdjoint (transitionOperator π hπ P) ∧
  ‖transitionOperator π hπ P‖ ≤ 1 ∧
  (∀ f g : WeightedSpace π hπ,
    dirichletForm π hπ P f g = (1 / 2 : ℝ) *
      ∑ x, ∑ y, (π x).toReal * realMatrix P x y * (f x - f y) * (g x - g y)) ∧
  (∀ f : WeightedSpace π hπ, 0 ≤ dirichletForm π hπ P f f) ∧
  (∀ f : WeightedSpace π hπ,
    f ∈ LinearMap.ker (LinearMap.id - transitionLinear π hπ P) ↔
      ∃ c : ℝ, ∀ x, f x = c)

-- The canonical definitions above are shared; these values explicitly bind
-- their intended mathematical content without importing implementation proofs.
def WeightedSpaceType := {S : Type u} → (π : ProbabilityLaw S) → (∀ i, 0 < π i) → Type u
def WeightedSpaceValue : WeightedSpaceType := @WeightedSpace

def weightedInnerType := {S : Type u} → [Fintype S] → (π : ProbabilityLaw S) →
  (hπ : ∀ i, 0 < π i) → WeightedSpace π hπ → WeightedSpace π hπ → ℝ
def weightedInnerValue : weightedInnerType := @weightedInner

def transitionLinearType := {S : Type u} → [Fintype S] → (π : ProbabilityLaw S) →
  (hπ : ∀ i, 0 < π i) → StochasticMatrix S → WeightedSpace π hπ →ₗ[ℝ] WeightedSpace π hπ
def transitionLinearValue : transitionLinearType := @transitionLinear

def transitionOperatorType := {S : Type u} → [Fintype S] → (π : ProbabilityLaw S) →
  (hπ : ∀ i, 0 < π i) → StochasticMatrix S → WeightedSpace π hπ →L[ℝ] WeightedSpace π hπ
def transitionOperatorValue : transitionOperatorType := @transitionOperator

def dirichletFormType := {S : Type u} → [Fintype S] → (π : ProbabilityLaw S) →
  (hπ : ∀ i, 0 < π i) → StochasticMatrix S → WeightedSpace π hπ → WeightedSpace π hπ → ℝ
def dirichletFormValue : dirichletFormType := @dirichletForm
end ReversibleDirichletFormSpec
end
end P207.Markov
