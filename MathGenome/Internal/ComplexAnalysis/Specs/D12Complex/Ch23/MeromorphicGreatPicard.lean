import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch23.ThreeOmissionsPunctureExtension
import Mathlib.Data.Set.Card

/-!
Great Picard for meromorphic maps, paper.tex:4320–4351, d12:23-06.
All functions are total representatives. Values at the puncture and outside a
witnessing punctured disk are ignored. Finite fibers are sets of distinct
points; the fiber of `sphereInfty` includes every pole. Essentiality means
failure of a holomorphic sphere-valued extension on any positive disk.
-/
noncomputable section
open Set

namespace D12Complex

/-- A local sphere-valued extension, without prescribing the representative's
value at the puncture. -/
def SpherePunctureExtensionAt (f : ℂ → RiemannSphere) (a : ℂ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∃ F : ℂ → RiemannSphere,
    PlaneSphereHolomorphicOn (Metric.ball a r) F ∧ EqOn F f (puncturedDisk a r)

/-- Values having only finitely many distinct preimages in some punctured
neighborhood. The existential radius makes this a property of the germ. -/
def finitePreimageValues {α : Type*} (f : ℂ → α) (a : ℂ) : Set α :=
  {v | ∃ r : ℝ, 0 < r ∧ {z | z ∈ puncturedDisk a r ∧ f z = v}.Finite}

end D12Complex

namespace Specs.D12Complex.Ch23.MeromorphicGreatPicard
open _root_.D12Complex

universe u

def SpherePunctureExtensionAt_type := (ℂ → RiemannSphere) → ℂ → Prop
def SpherePunctureExtensionAt_value : SpherePunctureExtensionAt_type :=
  fun f a => ∃ r : ℝ, 0 < r ∧ ∃ F : ℂ → RiemannSphere,
    PlaneSphereHolomorphicOn (Metric.ball a r) F ∧ EqOn F f (puncturedDisk a r)

def finitePreimageValues_type := {α : Type u} → (ℂ → α) → ℂ → Set α
def finitePreimageValues_value : finitePreimageValues_type :=
  fun f a => {v | ∃ r : ℝ, 0 < r ∧ {z | z ∈ puncturedDisk a r ∧ f z = v}.Finite}

/-- Exact equivalence of the finite-exception and every-radius formulations. -/
def not_mem_finitePreimageValues_iff_type : Prop :=
  ∀ {α : Type u} (f : ℂ → α) (a : ℂ) (v : α),
    v ∉ finitePreimageValues f a ↔
      ∀ r : ℝ, 0 < r → {z | z ∈ puncturedDisk a r ∧ f z = v}.Infinite

/-- Sphere holomorphy suffices; identically infinite maps need no special
exclusion because they have a local sphere-valued extension. -/
def sphere_great_picard_type : Prop :=
  ∀ (a : ℂ) (R : ℝ) (f : ℂ → RiemannSphere), 0 < R →
    PlaneSphereHolomorphicOn (puncturedDisk a R) f →
    ¬ SpherePunctureExtensionAt f a →
    (finitePreimageValues f a).encard ≤ 2 ∧
      ∀ v ∉ finitePreimageValues f a, ∀ r : ℝ, 0 < r →
        {z | z ∈ puncturedDisk a r ∧ f z = v}.Infinite

/-- The scalar meromorphic predicate retains its actual infinite pole values. -/
def meromorphic_great_picard_type : Prop :=
  ∀ (a : ℂ) (R : ℝ) (f : ℂ → RiemannSphere), 0 < R →
    ScalarMeromorphicOn (puncturedDisk a R) f →
    ¬ SpherePunctureExtensionAt f a →
    (finitePreimageValues f a).encard ≤ 2 ∧
      ∀ v ∉ finitePreimageValues f a, ∀ r : ℝ, 0 < r →
        {z | z ∈ puncturedDisk a r ∧ f z = v}.Infinite

/-- If infinity is omitted, it already uses one of the two sphere exceptions. -/
def sphere_great_picard_omitting_infty_type : Prop :=
  ∀ (a : ℂ) (R : ℝ) (f : ℂ → RiemannSphere), 0 < R →
    PlaneSphereHolomorphicOn (puncturedDisk a R) f →
    ¬ SpherePunctureExtensionAt f a →
    (∀ z ∈ puncturedDisk a R, f z ≠ sphereInfty) →
    (sphereFinite ⁻¹' finitePreimageValues f a).encard ≤ 1 ∧
      ∀ v ∉ sphereFinite ⁻¹' finitePreimageValues f a, ∀ r : ℝ, 0 < r →
        {z | z ∈ puncturedDisk a r ∧ f z = sphereFinite v}.Infinite

/-- Scalar specialization with the canonical scalar essential-singularity
predicate: neither removable nor a finite-order pole. -/
def holomorphic_great_picard_type : Prop :=
  ∀ (f : ℂ → ℂ) (a : ℂ), EssentialSingularityAt f a →
    (finitePreimageValues f a).encard ≤ 1 ∧
      ∀ v ∉ finitePreimageValues f a, ∀ r : ℝ, 0 < r →
        {z | z ∈ puncturedDisk a r ∧ f z = v}.Infinite

end Specs.D12Complex.Ch23.MeromorphicGreatPicard
