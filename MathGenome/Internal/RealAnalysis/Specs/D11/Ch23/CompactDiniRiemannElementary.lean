import MathGenome.Internal.RealAnalysis.Specs.D11.Ch23.ElementaryIntegral
import Mathlib.Topology.UniformSpace.Dini
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Order.ProjIcc
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Continuous
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Linearity

/-!
Independent statements for the compact-space and Riemann portions of
paper.tex:6314–6316. The compact-support portion has a separate allocation.
The canonical domain is a subspace of actual continuous functions. The integral
is the calculus foundation's proper Darboux integral, not a measure integral.
The constant extension outside the interval only adapts its domain to the
foundation API; on the interval it is exactly the original function.
-/
universe u
open Filter Topology
open SingleVariableAnalysis SingleVariableAnalysis.Riemann

namespace D11.Ch23.Specs

/-- All continuous real functions as a subspace of actual functions. -/
def continuousFunctions (X : Type u) [TopologicalSpace X] : Submodule ℝ (X → ℝ) where
  carrier := {f | Continuous f}
  zero_mem' := continuous_const
  add_mem' := fun hf hg => hf.add hg
  smul_mem' := fun _ _ hf => continuous_const.smul hf

/-- The usual continuous map attached to a member of the canonical subspace. -/
def asContinuousMap {X : Type u} [TopologicalSpace X]
    (f : continuousFunctions X) : C(X, ℝ) := ⟨f.val, f.property⟩

/-- Continuous functions on the closed interval are Darboux integrable.
This uses only the single-variable calculus foundation. -/
theorem interval_continuous_integrable {a b : ℝ} (hab : a ≤ b)
    (f : continuousFunctions (Set.Icc a b)) :
    RealIntegrable (Set.IccExtend hab f.val) a b := by
  apply real_continuous_integrable _ hab
  intro x hx
  apply (relativeContinuousAt_within_iff _ _ _).mpr
  exact (f.property.comp (continuous_projIcc (a := a) (b := b) (h := hab))).continuousOn x hx

/-- The classical Riemann functional, bundled using the calculus linearity laws. -/
noncomputable def riemannFunctional {a b : ℝ} (hab : a ≤ b) :
    continuousFunctions (Set.Icc a b) →ₗ[ℝ] ℝ where
  toFun f := realIntegral (Set.IccExtend hab f.val) (interval_continuous_integrable hab f)
  map_add' f g := by
    obtain ⟨h, he⟩ := real_add_value
      (interval_continuous_integrable hab f) (interval_continuous_integrable hab g)
    exact he
  map_smul' c f := by
    obtain ⟨h, he⟩ := real_mul_value (interval_continuous_integrable hab f) c
    exact he

def ContinuousFunctionsType :=
  ∀ (X : Type u) [TopologicalSpace X], Submodule ℝ (X → ℝ)

def RiemannFunctionalType :=
  ∀ {a b : ℝ}, a ≤ b → continuousFunctions (Set.Icc a b) →ₗ[ℝ] ℝ

/-- Dini's theorem with the source hypotheses, allowing an empty space. -/
def CompactDini : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (f : ℕ → X → ℝ),
    (∀ n, Continuous (f n)) → (∀ n x, 0 ≤ f n x) →
    (∀ x, Antitone (fun n => f n x)) →
    (∀ x, Tendsto (fun n => f n x) atTop (𝓝 0)) →
    TendstoUniformly f (fun _ => 0) atTop

/-- The continuous-function lattice contains a unit and satisfies Stone truncation. -/
def ContinuousFunctionsStone : Prop :=
  ∀ (X : Type u) [TopologicalSpace X],
    IsVectorLattice (continuousFunctions X) ∧ IsStone (continuousFunctions X) ∧
      (fun _ : X => (1 : ℝ)) ∈ continuousFunctions X

/-- Quantitative calculus bound for the actual Riemann functional. -/
def RiemannNormBound : Prop :=
  ∀ {a b : ℝ} (hab : a ≤ b) (f : continuousFunctions (Set.Icc a b)),
    |riemannFunctional hab f| ≤ (b - a) * ‖asContinuousMap f‖

/-- Positivity and pointwise order continuity of the classical functional. -/
def RiemannElementary : Prop :=
  ∀ {a b : ℝ} (hab : a ≤ b),
    IsElementaryIntegral (continuousFunctions (Set.Icc a b)) (riemannFunctional hab)

/-- The singleton-interval functional is zero on every continuous function. -/
def RiemannDegenerate : Prop :=
  ∀ (a : ℝ) (f : continuousFunctions (Set.Icc a a)), riemannFunctional (le_refl a) f = 0

end D11.Ch23.Specs
