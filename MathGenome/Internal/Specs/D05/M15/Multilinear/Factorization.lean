import MathGenome.Internal.Specs.D05.M15.TensorUniversal
import MathGenome.Internal.Specs.D05.M11.Radicals
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

/-!
Independent interface for the factorization supplement, paper.tex:2708–2709.
All four vector spaces are arbitrary algebraic vector spaces over a field.
`TensorProduct.lift` is the canonical linearization from the upstream tensor
interface. Classical basis extension is permitted for extending the map on its
image; neither finite dimension nor radical inclusions are hypotheses.
-/
namespace Specs.D05.M15.Multilinear.Factorization

open scoped TensorProduct

section General
variable {K V W G H : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [AddCommGroup G] [Module K G] [AddCommGroup H] [Module K H]

/-- The equation to be solved, with the original two input slots. -/
def Factors (b : V →ₗ[K] W →ₗ[K] G) (c : V →ₗ[K] W →ₗ[K] H)
    (f : G →ₗ[K] H) : Prop := ∀ v w, f (b v w) = c v w

/-- The solution set with its inherited affine structure. It may be empty. -/
def solutions (b : V →ₗ[K] W →ₗ[K] G) (c : V →ₗ[K] W →ₗ[K] H) :
    AffineSubspace K (G →ₗ[K] H) where
  carrier := {f | Factors b c f}
  smul_vsub_vadd_mem' a f g h hf hg hh := by
    intro v w
    change a • (f (b v w) - g (b v w)) + h (b v w) = c v w
    rw [hf v w, hg v w, hh v w, sub_self, smul_zero, zero_add]

/-- Homogeneous differences of solutions. -/
def vanishing (b : V →ₗ[K] W →ₗ[K] G) : Submodule K (G →ₗ[K] H) where
  carrier := {d | ∀ v w, d (b v w) = 0}
  zero_mem' := by simp
  add_mem' hf hg := by intro v w; simp [hf v w, hg v w]
  smul_mem' a f hf := by intro v w; simp [hf v w]

end General

/-- The tensor equation and the original bilinear equation are equivalent. -/
def linearization_composition : Prop :=
  ∀ {K V W G H : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup G] [Module K G] [AddCommGroup H] [Module K H],
  ∀ (b : V →ₗ[K] W →ₗ[K] G) (c : V →ₗ[K] W →ₗ[K] H) (f : G →ₗ[K] H),
    Factors b c f ↔ f.comp (TensorProduct.lift b) = TensorProduct.lift c

/-- The induced map on the image has the prescribed values and is unique. -/
def image_factorization : Prop :=
  ∀ {K V W G H : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup G] [Module K G] [AddCommGroup H] [Module K H],
  ∀ (b : V →ₗ[K] W →ₗ[K] G) (c : V →ₗ[K] W →ₗ[K] H),
    LinearMap.ker (TensorProduct.lift b) ≤ LinearMap.ker (TensorProduct.lift c) →
    ∃! f₀ : LinearMap.range (TensorProduct.lift b) →ₗ[K] H,
      ∀ t, f₀ ((TensorProduct.lift b).rangeRestrict t) = TensorProduct.lift c t

/-- The exact existence test, in arbitrary dimension. -/
def factorization_iff_kernel : Prop :=
  ∀ {K V W G H : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup G] [Module K G] [AddCommGroup H] [Module K H],
  ∀ (b : V →ₗ[K] W →ₗ[K] G) (c : V →ₗ[K] W →ₗ[K] H),
    (∃ f : G →ₗ[K] H, Factors b c f) ↔
      LinearMap.ker (TensorProduct.lift b) ≤ LinearMap.ker (TensorProduct.lift c)

/-- Every solution differs from a given one by a unique quotient map. -/
def difference_quotient : Prop :=
  ∀ {K V W G H : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup G] [Module K G] [AddCommGroup H] [Module K H],
  ∀ (b : V →ₗ[K] W →ₗ[K] G) (c : V →ₗ[K] W →ₗ[K] H)
    (f₀ : G →ₗ[K] H), Factors b c f₀ → ∀ f : G →ₗ[K] H,
    Factors b c f ↔ ∃! d : (G ⧸ LinearMap.range (TensorProduct.lift b)) →ₗ[K] H,
      f = f₀ + d.comp (LinearMap.range (TensorProduct.lift b)).mkQ

/-- The direction of a nonempty solution affine subspace is the homogeneous space. -/
def solution_direction : Prop :=
  ∀ {K V W G H : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup G] [Module K G] [AddCommGroup H] [Module K H],
  ∀ (b : V →ₗ[K] W →ₗ[K] G) (c : V →ₗ[K] W →ₗ[K] H)
    (f₀ : G →ₗ[K] H), Factors b c f₀ →
    (solutions b c).direction = vanishing (H := H) b

/-- The quotient Hom space identifies linearly with the direction, by pullback. -/
def quotient_model : Prop :=
  ∀ {K V W G H : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup G] [Module K G] [AddCommGroup H] [Module K H],
  ∀ b : V →ₗ[K] W →ₗ[K] G,
    ∃ E : ((G ⧸ LinearMap.range (TensorProduct.lift b)) →ₗ[K] H) ≃ₗ[K]
      vanishing (H := H) b,
      ∀ d, (E d : G →ₗ[K] H) = d.comp (LinearMap.range (TensorProduct.lift b)).mkQ

/-- Choosing any solution gives affine coordinates on all solutions. The formula
fixes the translation, including its origin; the direction identification above
is linear, so this is an affine-space parametrization, not just a cardinality claim. -/
def affine_parametrization : Prop :=
  ∀ {K V W G H : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup G] [Module K G] [AddCommGroup H] [Module K H],
  ∀ (b : V →ₗ[K] W →ₗ[K] G) (c : V →ₗ[K] W →ₗ[K] H)
    (f₀ : G →ₗ[K] H), Factors b c f₀ →
    ∃ E : ((G ⧸ LinearMap.range (TensorProduct.lift b)) →ₗ[K] H) ≃ solutions b c,
      (∀ d, (E d : G →ₗ[K] H) = f₀ + d.comp (LinearMap.range (TensorProduct.lift b)).mkQ) ∧
      (∀ d e, (E (d + e) : G →ₗ[K] H) =
        (E d : G →ₗ[K] H) + e.comp (LinearMap.range (TensorProduct.lift b)).mkQ)

/-- The solution set is an affine space over the quotient Hom model, with
its actual inherited affine structure and the specified origin and pullback. -/
def affine_equivalence : Prop :=
  ∀ {K V W G H : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup G] [Module K G] [AddCommGroup H] [Module K H],
  ∀ (b : V →ₗ[K] W →ₗ[K] G) (c : V →ₗ[K] W →ₗ[K] H)
    (f₀ : G →ₗ[K] H) (hf₀ : Factors b c f₀),
    letI : Nonempty (solutions b c) := ⟨⟨f₀, hf₀⟩⟩
    ∃ E : ((G ⧸ LinearMap.range (TensorProduct.lift b)) →ₗ[K] H) ≃ᵃ[K] solutions b c,
      (∀ d, (E d : G →ₗ[K] H) = f₀ + d.comp (LinearMap.range (TensorProduct.lift b)).mkQ) ∧
      (∀ d, (E.linear d : G →ₗ[K] H) = d.comp (LinearMap.range (TensorProduct.lift b)).mkQ)

/-- Uniqueness, when a solution exists, is exactly the vanishing of the model. -/
def uniqueness_iff_model_zero : Prop :=
  ∀ {K V W G H : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup G] [Module K G] [AddCommGroup H] [Module K H],
  ∀ (b : V →ₗ[K] W →ₗ[K] G) (c : V →ₗ[K] W →ₗ[K] H)
    (f₀ : G →ₗ[K] H), Factors b c f₀ →
    ((∀ f : G →ₗ[K] H, Factors b c f → f = f₀) ↔
      ∀ d : (G ⧸ LinearMap.range (TensorProduct.lift b)) →ₗ[K] H, d = 0)

/-- An unconditional exact test for the existence of a unique solution. -/
def unique_factorization_iff : Prop :=
  ∀ {K V W G H : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup G] [Module K G] [AddCommGroup H] [Module K H],
  ∀ (b : V →ₗ[K] W →ₗ[K] G) (c : V →ₗ[K] W →ₗ[K] H),
    (∃! f : G →ₗ[K] H, Factors b c f) ↔
      LinearMap.ker (TensorProduct.lift b) ≤ LinearMap.ker (TensorProduct.lift c) ∧
      ∀ d : (G ⧸ LinearMap.range (TensorProduct.lift b)) →ₗ[K] H, d = 0

/-- The inherited zero is a solution exactly for the homogeneous problem. -/
def zero_solution_iff : Prop :=
  ∀ {K V W G H : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup G] [Module K G] [AddCommGroup H] [Module K H],
  ∀ (b : V →ₗ[K] W →ₗ[K] G) (c : V →ₗ[K] W →ₗ[K] H),
    (0 : G →ₗ[K] H) ∈ solutions b c ↔ c = 0
/-- The two specific real forms in the source counterexample. -/
noncomputable def exampleB : LinearMap.BilinForm ℝ (Fin 2 → ℝ) :=
  (!![1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ).toBilin'
noncomputable def exampleC : LinearMap.BilinForm ℝ (Fin 2 → ℝ) :=
  (!![1, 0; 0, 2] : Matrix (Fin 2) (Fin 2) ℝ).toBilin'

def example_evaluation : Prop := ∀ x y : Fin 2 → ℝ,
  exampleB x y = x 0 * y 0 + x 1 * y 1 ∧
  exampleC x y = x 0 * y 0 + 2 * (x 1 * y 1)

/-- Both separate radical inclusions hold (indeed all radicals vanish),
but there is no linear scalar map taking b to c. -/
def radical_counterexample : Prop :=
  Specs.D05.M11.Radicals.leftRadical_value exampleB = ⊥ ∧
  Specs.D05.M11.Radicals.rightRadical_value exampleB = ⊥ ∧
  Specs.D05.M11.Radicals.leftRadical_value exampleC = ⊥ ∧
  Specs.D05.M11.Radicals.rightRadical_value exampleC = ⊥ ∧
  ¬ ∃ f : ℝ →ₗ[ℝ] ℝ, Factors exampleB exampleC f

end Specs.D05.M15.Multilinear.Factorization
