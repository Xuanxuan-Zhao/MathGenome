import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.MetricSpace.HolderNorm
import Mathlib.Analysis.Normed.Group.Seminorm

/-! Canonical spaces for paper.tex, lines 5802–5839.
All differentiation is real differentiation *within* the closed interval.
The zero extension below is only a representative for `ContDiffOn` and
`iteratedDerivWithin`; no differentiability across the endpoints is required.
-/
noncomputable section
open Set
open scoped NNReal

namespace ExpandedFA.Supplements.HolderSpacesSpec

abbrev Interval (a b : ℝ) := Set.Icc a b

/-- A representative on ℝ of an interval function, used only within the interval. -/
def intervalExtend {𝕜 : Type*} [Zero 𝕜] [TopologicalSpace 𝕜] {a b : ℝ} (f : C(Interval a b, 𝕜)) : ℝ → 𝕜 :=
  fun x => if hx : x ∈ Set.Icc a b then f ⟨x, hx⟩ else 0

@[simp] theorem intervalExtend_apply {𝕜 : Type*} [Zero 𝕜] [TopologicalSpace 𝕜] {a b : ℝ}
    (f : C(Interval a b, 𝕜)) (x : Interval a b) : intervalExtend f x = f x := by
  simp [intervalExtend, x.property]

@[simp] theorem intervalExtend_zero {𝕜 : Type*} [RCLike 𝕜] {a b : ℝ} :
    intervalExtend (0 : C(Interval a b, 𝕜)) = 0 := by
  funext x; simp [intervalExtend]

@[simp] theorem intervalExtend_add {𝕜 : Type*} [RCLike 𝕜] {a b : ℝ}
    (f g : C(Interval a b, 𝕜)) : intervalExtend (f + g) = intervalExtend f + intervalExtend g := by
  funext x; by_cases hx : x ∈ Set.Icc a b <;> simp [intervalExtend, hx]

@[simp] theorem intervalExtend_smul {𝕜 : Type*} [RCLike 𝕜] {a b : ℝ}
    (c : 𝕜) (f : C(Interval a b, 𝕜)) : intervalExtend (c • f) = c • intervalExtend f := by
  funext x; by_cases hx : x ∈ Set.Icc a b <;> simp [intervalExtend, hx]

/-- The continuous interval functions with m continuous interval derivatives. -/
def cmSubmodule (𝕜 : Type*) [RCLike 𝕜] (m : ℕ) (a b : ℝ) :
    Submodule 𝕜 C(Interval a b, 𝕜) where
  carrier := {f | ContDiffOn ℝ m (intervalExtend f) (Set.Icc a b)}
  zero_mem' := by simp only [mem_ofPred_eq, intervalExtend_zero]; exact contDiffOn_const
  add_mem' := by intro f g hf hg; change ContDiffOn ℝ m (intervalExtend (f + g)) (Set.Icc a b); rw [intervalExtend_add]; exact hf.add hg
  smul_mem' := by intro c f hf; change ContDiffOn ℝ m (intervalExtend (c • f)) (Set.Icc a b); rw [intervalExtend_smul]; exact hf.const_smul c

/-- C^m([a,b],𝕜), for a<b. `hab` fixes the intended nondegenerate domain. -/
def Cm (𝕜 : Type*) [RCLike 𝕜] (m : ℕ) {a b : ℝ} (_hab : a < b) :=
  ↥(cmSubmodule 𝕜 m a b)

namespace Cm
variable {𝕜 : Type*} [RCLike 𝕜] {m : ℕ} {a b : ℝ} {hab : a < b}
instance : AddCommGroup (Cm 𝕜 m hab) := inferInstanceAs (AddCommGroup ↥(cmSubmodule 𝕜 m a b))
instance : Module 𝕜 (Cm 𝕜 m hab) := inferInstanceAs (Module 𝕜 ↥(cmSubmodule 𝕜 m a b))
instance : CoeFun (Cm 𝕜 m hab) (fun _ => Interval a b → 𝕜) := ⟨fun f => f.val⟩

/-- The j-th interval derivative, bundled as the established continuous-map object. -/
def derivative (f : Cm 𝕜 m hab) (j : Fin (m + 1)) : C(Interval a b, 𝕜) where
  toFun x := iteratedDerivWithin j.val (intervalExtend f.val) (Set.Icc a b) x
  continuous_toFun :=
    (f.property.continuousOn_iteratedDerivWithin (by exact_mod_cast Nat.le_of_lt_succ j.isLt)
      (uniqueDiffOn_Icc hab)).domRestrict

@[simp] theorem derivative_zero_order (f : Cm 𝕜 m hab) : derivative f ⟨0, Nat.zero_lt_succ m⟩ = f.val := by
  ext x; simp [derivative]

@[simp] theorem derivative_zero (j : Fin (m + 1)) : derivative (0 : Cm 𝕜 m hab) j = 0 := by
  ext x
  change iteratedDerivWithin j.val (intervalExtend (0 : C(Interval a b, 𝕜))) (Set.Icc a b) x = 0
  simp

@[simp] theorem derivative_add (f g : Cm 𝕜 m hab) (j : Fin (m + 1)) :
    derivative (f + g) j = derivative f j + derivative g j := by
  ext x
  change iteratedDerivWithin j.val (intervalExtend (f.val + g.val)) (Set.Icc a b) x = _
  rw [intervalExtend_add, iteratedDerivWithin_add x.property (uniqueDiffOn_Icc hab)]
  · rfl
  · exact (f.property.of_le (by exact_mod_cast Nat.le_of_lt_succ j.isLt)) x x.property
  · exact (g.property.of_le (by exact_mod_cast Nat.le_of_lt_succ j.isLt)) x x.property

@[simp] theorem derivative_smul (c : 𝕜) (f : Cm 𝕜 m hab) (j : Fin (m + 1)) :
    derivative (c • f) j = c • derivative f j := by
  ext x
  change iteratedDerivWithin j.val (intervalExtend (c • f.val)) (Set.Icc a b) x = _
  rw [intervalExtend_smul, iteratedDerivWithin_const_smul_field]
  rfl

/-- The specified sum norm, not the maximum norm on a finite product. -/
def normValue (f : Cm 𝕜 m hab) : ℝ := ∑ j : Fin (m + 1), ‖derivative f j‖

theorem uniformNorm_le (f : Cm 𝕜 m hab) : ‖f.val‖ ≤ normValue f := by
  rw [← derivative_zero_order f]
  exact Finset.single_le_sum (fun j _ => norm_nonneg (derivative f j)) (Finset.mem_univ _)

/-- The actual additive group norm associated to the displayed sum. -/
def groupNorm : AddGroupNorm (Cm 𝕜 m hab) where
  toFun := normValue
  map_zero' := by simp [normValue]
  add_le' f g := by
    simpa only [normValue, derivative_add, Finset.sum_add_distrib] using
      Finset.sum_le_sum (fun (j : Fin (m + 1)) _ => norm_add_le (derivative f j) (derivative g j))
  neg' f := by
    have hn : -f = (-1 : 𝕜) • f := by simp
    rw [hn]
    simp only [normValue, derivative_smul, norm_smul, norm_neg, norm_one, one_mul]
  eq_zero_of_map_eq_zero' f hf := by
    apply Subtype.ext
    exact norm_eq_zero.mp (le_antisymm (hf ▸ uniformNorm_le f) (norm_nonneg _))

instance : NormedAddCommGroup (Cm 𝕜 m hab) := groupNorm.toNormedAddCommGroup

@[simp] theorem norm_eq (f : Cm 𝕜 m hab) : ‖f‖ = ∑ j : Fin (m + 1), ‖derivative f j‖ := rfl

instance : NormedSpace 𝕜 (Cm 𝕜 m hab) where
  norm_smul_le c f := by
    simp only [norm_eq, derivative_smul, norm_smul, Finset.mul_sum, le_refl]

end Cm


/-- The exponents in the manuscript: precisely 0 < α ≤ 1. -/
abbrev HolderExponent := Set.Ioc (0 : ℝ≥0) 1

/-- Nonnegative Hölder seminorm (the least Hölder constant). -/
def holderSeminorm {X 𝕜 : Type*} [MetricSpace X] [RCLike 𝕜]
    (α : HolderExponent) (f : X → 𝕜) : ℝ := nnHolderNorm α.val f

/-- Difference quotients, with 0 adjoined to implement the empty-supremum convention. -/
def holderQuotients {X 𝕜 : Type*} [MetricSpace X] [RCLike 𝕜]
    (α : HolderExponent) (f : X → 𝕜) : Set ℝ :=
  insert 0 {q | ∃ s t : X, s ≠ t ∧ q = ‖f s - f t‖ / dist s t ^ (α.val : ℝ)}

section HolderDomain
variable {𝕜 E X : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [MetricSpace X]

/-- A general graph domain for imposing Hölder control on a linear observable. -/
def holderSubmodule (T : E →ₗ[𝕜] (X → 𝕜)) (α : HolderExponent) : Submodule 𝕜 E where
  carrier := {f | MemHolder α.val (T f)}
  zero_mem' := by simp
  add_mem' := by intro f g hf hg; simpa using hf.add hg
  smul_mem' := by intro c f hf; simpa using hf.smul (c := c)

/-- Domain equipped with the sum of the base norm and the observable's Hölder seminorm. -/
def HolderDomain (T : E →ₗ[𝕜] (X → 𝕜)) (α : HolderExponent) := ↥(holderSubmodule T α)

namespace HolderDomain
variable {T : E →ₗ[𝕜] (X → 𝕜)} {α : HolderExponent}
instance : AddCommGroup (HolderDomain T α) :=
  inferInstanceAs (AddCommGroup ↥(holderSubmodule T α))
instance : Module 𝕜 (HolderDomain T α) := inferInstanceAs (Module 𝕜 ↥(holderSubmodule T α))

def normValue (f : HolderDomain T α) : ℝ := ‖f.val‖ + holderSeminorm α (T f.val)

def groupNorm : AddGroupNorm (HolderDomain T α) where
  toFun := normValue
  map_zero' := by
    change ‖(0 : E)‖ + holderSeminorm α (T 0) = 0
    simp [holderSeminorm]
  add_le' f g := by
    have h := f.property.nnHolderNorm_add_le g.property
    have h' : holderSeminorm α (T (f.val + g.val)) ≤
        holderSeminorm α (T f.val) + holderSeminorm α (T g.val) := by
      simpa only [map_add, holderSeminorm, NNReal.coe_add] using (NNReal.coe_le_coe.mpr h)
    change ‖f.val + g.val‖ + holderSeminorm α (T (f.val + g.val)) ≤ _
    have hn := norm_add_le f.val g.val
    unfold normValue
    linarith
  neg' f := by
    change ‖-f.val‖ + holderSeminorm α (T (-f.val)) = _
    have h := f.property.nnHolderNorm_smul (-1 : 𝕜)
    have h' : holderSeminorm α (T (-f.val)) = holderSeminorm α (T f.val) := by
      simpa [holderSeminorm] using congrArg (fun r : ℝ≥0 => (r : ℝ)) h
    simp only [norm_neg, h', normValue]
  eq_zero_of_map_eq_zero' f hf := by
    apply Subtype.ext
    have hp : 0 ≤ holderSeminorm α (T f.val) := NNReal.coe_nonneg _
    have hn := norm_nonneg f.val
    change ‖f.val‖ + holderSeminorm α (T f.val) = 0 at hf
    have hz : ‖f.val‖ = 0 := by linarith
    exact norm_eq_zero.mp hz

instance : NormedAddCommGroup (HolderDomain T α) := groupNorm.toNormedAddCommGroup

@[simp] theorem norm_eq (f : HolderDomain T α) :
    ‖f‖ = ‖f.val‖ + holderSeminorm α (T f.val) := rfl

instance : NormedSpace 𝕜 (HolderDomain T α) where
  norm_smul_le c f := by
    have h := f.property.nnHolderNorm_smul c
    have h' : holderSeminorm α (T (c • f.val)) = ‖c‖ * holderSeminorm α (T f.val) := by
      simpa only [map_smul, holderSeminorm, NNReal.coe_mul, coe_nnnorm] using
        congrArg (fun r : ℝ≥0 => (r : ℝ)) h
    change ‖c • f.val‖ + holderSeminorm α (T (c • f.val)) ≤ _
    rw [norm_smul, h', norm_eq, mul_add]

end HolderDomain
end HolderDomain

/-- Evaluation of a bounded continuous function as a function, a linear map. -/
def boundedFunctionLinearMap (X 𝕜 : Type*) [MetricSpace X] [RCLike 𝕜] :
    BoundedContinuousFunction X 𝕜 →ₗ[𝕜] (X → 𝕜) where
  toFun f := f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Bounded α-Hölder functions on any metric space, with norm ‖f‖∞ + [f]α.
There is no compactness, boundedness or nonemptiness assumption on X. -/
abbrev BoundedHolder (X 𝕜 : Type*) [MetricSpace X] [RCLike 𝕜] (α : HolderExponent) :=
  HolderDomain (boundedFunctionLinearMap X 𝕜) α

namespace BoundedHolder
variable {X 𝕜 : Type*} [MetricSpace X] [RCLike 𝕜] {α : HolderExponent}
instance : CoeFun (BoundedHolder X 𝕜 α) (fun _ => X → 𝕜) := ⟨fun f => f.val⟩
end BoundedHolder

/-- The top derivative observable, using Mathlib's interval derivatives. -/
def Cm.topDerivativeLinearMap (𝕜 : Type*) [RCLike 𝕜] (m : ℕ) {a b : ℝ} (hab : a < b) :
    Cm 𝕜 m hab →ₗ[𝕜] (Interval a b → 𝕜) where
  toFun f := Cm.derivative f ⟨m, Nat.lt_succ_self m⟩
  map_add' f g := by ext x; exact congrArg (fun h : C(Interval a b, 𝕜) => h x) (Cm.derivative_add f g _)
  map_smul' c f := by ext x; exact congrArg (fun h : C(Interval a b, 𝕜) => h x) (Cm.derivative_smul c f _)

/-- C^{m,α}([a,b],𝕜), equipped with the specified sum norm plus top seminorm. -/
abbrev CmHolder (𝕜 : Type*) [RCLike 𝕜] (m : ℕ) {a b : ℝ} (hab : a < b)
    (α : HolderExponent) := HolderDomain (Cm.topDerivativeLinearMap 𝕜 m hab) α

namespace CmHolder
variable {𝕜 : Type*} [RCLike 𝕜] {m : ℕ} {a b : ℝ} {hab : a < b} {α : HolderExponent}
instance : CoeFun (CmHolder 𝕜 m hab α) (fun _ => Interval a b → 𝕜) := ⟨fun f => f.val⟩
end CmHolder



/-! Expected theorem statements. They impose no certificates on the spaces. -/
def CmNormFormula : Prop :=
  ∀ (𝕜 : Type*) [RCLike 𝕜] (m : ℕ) (a b : ℝ) (hab : a < b) (f : Cm 𝕜 m hab),
    ‖f‖ = ∑ j : Fin (m + 1), ‖Cm.derivative f j‖

def CmHolderNormFormula : Prop :=
  ∀ (𝕜 : Type*) [RCLike 𝕜] (m : ℕ) (a b : ℝ) (hab : a < b)
    (α : HolderExponent) (f : CmHolder 𝕜 m hab α),
    ‖f‖ = (∑ j : Fin (m + 1), ‖Cm.derivative f.val j‖) +
      holderSeminorm α (Cm.derivative f.val ⟨m, Nat.lt_succ_self m⟩)

def BoundedHolderNormFormula : Prop :=
  ∀ (X 𝕜 : Type*) [MetricSpace X] [RCLike 𝕜] (α : HolderExponent)
    (f : BoundedHolder X 𝕜 α), ‖f‖ = ‖f.val‖ + holderSeminorm α f

def QuotientSupremumFormula : Prop :=
  ∀ (X 𝕜 : Type*) [MetricSpace X] [RCLike 𝕜] (α : HolderExponent)
    (f : X → 𝕜), MemHolder α.val f →
    holderSeminorm α f = sSup (holderQuotients α f)

def EmptyQuotientConvention : Prop :=
  ∀ (X 𝕜 : Type*) [MetricSpace X] [RCLike 𝕜] [Subsingleton X]
    (α : HolderExponent) (f : X → 𝕜), holderSeminorm α f = 0

def BoundedHolderMembership : Prop :=
  ∀ (X 𝕜 : Type*) [MetricSpace X] [RCLike 𝕜] (α : HolderExponent) (f : X → 𝕜),
    (∃ g : BoundedHolder X 𝕜 α, (g : X → 𝕜) = f) ↔
      (∃ M : ℝ, ∀ x, ‖f x‖ ≤ M) ∧ MemHolder α.val f

-- Expected types for the definitional bindings. Universes are kept general.
universe u v

def CmType := (𝕜 : Type u) → [RCLike 𝕜] → (m : ℕ) → {a b : ℝ} → a < b → Type u

def CmHolderType := (𝕜 : Type u) → [RCLike 𝕜] → (m : ℕ) → {a b : ℝ} →
  a < b → HolderExponent → Type u

def BoundedHolderType := (X : Type u) → (𝕜 : Type v) → [MetricSpace X] →
  [RCLike 𝕜] → HolderExponent → Type (max u v)

def HolderSeminormType := {X : Type u} → {𝕜 : Type v} → [MetricSpace X] →
  [RCLike 𝕜] → HolderExponent → (X → 𝕜) → ℝ

def DerivativeType := {𝕜 : Type u} → [RCLike 𝕜] → {m : ℕ} → {a b : ℝ} →
  {hab : a < b} → Cm 𝕜 m hab → Fin (m + 1) → C(Interval a b, 𝕜)

end ExpandedFA.Supplements.HolderSpacesSpec
