import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01Norm
import Mathlib.LinearAlgebra.Quotient.Defs

/-!
Independent specification for paper.tex lines 151–157. The ambient vector space
has no prior norm or topology. These are the algebraic null-space quotient and
its representative seminorm, not a distance quotient by an arbitrary subspace.
-/

namespace ExpandedFA.P1.SeminormNullQuotient
open C01Norm

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- The null space, with exactly the prescribed carrier. -/
def nullSubspace (p : Seminorm 𝕜 E) : Submodule 𝕜 E where
  carrier := {x | p x = 0}
  zero_mem' := map_zero p
  add_mem' := by
    intro x y hx hy
    change p x = 0 at hx
    change p y = 0 at hy
    exact le_antisymm (by simpa only [hx, hy, add_zero] using map_add_le_add p x y)
      (apply_nonneg p _)
  smul_mem' := by
    intro a x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [map_smul_eq_mul, hx, mul_zero]

/-- The ordinary algebraic quotient, retaining its usual vector-space operations. -/
abbrev Space (p : Seminorm 𝕜 E) := E ⧸ nullSubspace p

/-- The canonical quotient map is bundled as a linear map. -/
def quotientMap (p : Seminorm 𝕜 E) : E →ₗ[𝕜] Space p :=
  (nullSubspace p).mkQ

/-- A representative-based value; the implementation must prove that every
representative gives the same answer, and that this value is a genuine norm. -/
noncomputable def quotientValue (p : Seminorm 𝕜 E) (z : Space p) : ℝ :=
  p (Quotient.out z)

namespace Spec

/-- The distance p(x-y) is realized by a bundled pseudometric, including all
pseudometric axioms and without any definiteness assumption. -/
def Pseudometric : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    (p : Seminorm 𝕜 E),
    ∃ d : PseudoMetricSpace E, ∀ x y : E, @dist E d.toDist x y = p (x - y)

def NullSpace : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    (p : Seminorm 𝕜 E) (x : E), x ∈ nullSubspace p ↔ p x = 0

def Translation : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    (p : Seminorm 𝕜 E) (x n : E), p n = 0 → p (x + n) = p x

/-- Coset equality is precisely equality modulo the null space, and the value
of the seminorm is constant on every coset. -/
def Representatives : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    (p : Seminorm 𝕜 E) (x y : E),
    (quotientMap p x = quotientMap p y ↔ p (x - y) = 0) ∧
    (quotientMap p x = quotientMap p y → p x = p y)

def ValueOnRepresentatives : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    (p : Seminorm 𝕜 E) (x : E), quotientValue p (quotientMap p x) = p x

/-- All axioms, including nonnegativity, absolute homogeneity, the triangle
inequality, and definiteness, on every element of the algebraic quotient. -/
def QuotientNormAxioms : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    (p : Seminorm 𝕜 E), NormAxioms 𝕜 (quotientValue p)

/-- Realize that very value as the norm in a standard normed vector space,
with the original algebraic quotient module, and the exact quotient-map formula.
This existential construction requires no topology, closedness, completeness,
or nontriviality hypothesis on E. -/
def QuotientNormedSpace : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    (p : Seminorm 𝕜 E),
    ∃ s : Seminorm 𝕜 (Space p),
    ∃ h : ∀ z, s z = 0 → z = 0,
      letI := normedGroup s h
      (∃ n : NormedSpace 𝕜 (Space p),
        n.toModule = (inferInstance : Module 𝕜 (Space p))) ∧
      (∀ z : Space p, ‖z‖ = quotientValue p z) ∧
      (∀ x : E, ‖quotientMap p x‖ = p x)

def QuotientMapProperties : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    (p : Seminorm 𝕜 E),
    Function.Surjective (quotientMap p) ∧ LinearMap.ker (quotientMap p) = nullSubspace p

end Spec
end ExpandedFA.P1.SeminormNullQuotient
