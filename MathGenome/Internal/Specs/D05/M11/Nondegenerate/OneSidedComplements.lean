import MathGenome.Internal.Specs.D05.M11.Nondegenerate
import MathGenome.Internal.Specs.D05.M11.Hermitian
import MathGenome.Internal.Specs.D05.M06.Projection
import Mathlib.LinearAlgebra.SesquilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
K05.11.nondegenerate, paper.tex:1658–1670. Only W is finite dimensional.
We use the canonical semibilinear map with scalar automorphisms σ, τ. The
paper's bilinear case is σ = τ = RingEquiv.refl K; its real/complex
sesquilinear case is σ = refl K, τ = starRingAut. The generalization also
allows the slots to be flipped without imposing symmetry. Nondegeneracy is
Mathlib's conjunction of both separation conditions on the actual restriction.
The right complement is `W.orthogonalBilin B`; the left is the same construction
for `B.flip`. These are submodules, without any positive inner product.
-/
namespace Specs.D05.M11.Nondegenerate.OneSidedComplements

open Module Matrix
open scoped BigOperators

/-- The defining equations retain the paper's order of slots. -/
def complement_membership : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V],
  ∀ (σ τ : K ≃+* K) (B : V →ₛₗ[σ.toRingHom] V →ₛₗ[τ.toRingHom] K)
    (W : Submodule K V) (v : V),
    (v ∈ W.orthogonalBilin B ↔ ∀ w ∈ W, B w v = 0) ∧
    (v ∈ W.orthogonalBilin B.flip ↔ ∀ w ∈ W, B v w = 0)

/-- Unique expressions in the two actual subspaces, as in the shared direct-sum convention. -/
def right_direct_sum : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V],
  ∀ (σ τ : K ≃+* K) (B : V →ₛₗ[σ.toRingHom] V →ₛₗ[τ.toRingHom] K)
    (W : Submodule K V) [FiniteDimensional K W],
    (B.domRestrict₁₂ W W).Nondegenerate →
      Specs.D05.M06.DirectSum.UniqueDecomposition
        (fun b : Bool => if b then W.orthogonalBilin B else W)

def left_direct_sum : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V],
  ∀ (σ τ : K ≃+* K) (B : V →ₛₗ[σ.toRingHom] V →ₛₗ[τ.toRingHom] K)
    (W : Submodule K V) [FiniteDimensional K W],
    (B.domRestrict₁₂ W W).Nondegenerate →
      Specs.D05.M06.DirectSum.UniqueDecomposition
        (fun b : Bool => if b then W.orthogonalBilin B.flip else W)

/-- Both directions of the intersection criterion, including nonsymmetric forms. -/
def right_intersection_iff : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V],
  ∀ (σ τ : K ≃+* K) (B : V →ₛₗ[σ.toRingHom] V →ₛₗ[τ.toRingHom] K)
    (W : Submodule K V) [FiniteDimensional K W],
    W ⊓ W.orthogonalBilin B = ⊥ ↔ (B.domRestrict₁₂ W W).Nondegenerate

def left_intersection_iff : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V],
  ∀ (σ τ : K ≃+* K) (B : V →ₛₗ[σ.toRingHom] V →ₛₗ[τ.toRingHom] K)
    (W : Submodule K V) [FiniteDimensional K W],
    W ⊓ W.orthogonalBilin B.flip = ⊥ ↔ (B.domRestrict₁₂ W W).Nondegenerate

/-- Algebraic complements, with no finiteness assumption on V. -/
def right_complement : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V],
  ∀ (σ τ : K ≃+* K) (B : V →ₛₗ[σ.toRingHom] V →ₛₗ[τ.toRingHom] K)
    (W : Submodule K V) [FiniteDimensional K W],
    (B.domRestrict₁₂ W W).Nondegenerate → IsCompl W (W.orthogonalBilin B)

def left_complement : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V],
  ∀ (σ τ : K ≃+* K) (B : V →ₛₗ[σ.toRingHom] V →ₛₗ[τ.toRingHom] K)
    (W : Submodule K V) [FiniteDimensional K W],
    (B.domRestrict₁₂ W W).Nondegenerate → IsCompl W (W.orthogonalBilin B.flip)

/-- The idempotent is uniquely determined by its image and kernel; it fixes W,
its residual is right-perpendicular, and it preserves every value B(w,v). -/
def right_projection : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V],
  ∀ (σ τ : K ≃+* K) (B : V →ₛₗ[σ.toRingHom] V →ₛₗ[τ.toRingHom] K)
    (W : Submodule K V) [FiniteDimensional K W],
    (B.domRestrict₁₂ W W).Nondegenerate →
    ∃! E : Module.End K V,
      E ^ 2 = E ∧ E.range = W ∧ E.ker = W.orthogonalBilin B ∧
      (∀ w ∈ W, E w = w) ∧
      (∀ v, v - E v ∈ W.orthogonalBilin B) ∧
      (∀ w ∈ W, ∀ v, B w (E v) = B w v)

def left_projection : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V],
  ∀ (σ τ : K ≃+* K) (B : V →ₛₗ[σ.toRingHom] V →ₛₗ[τ.toRingHom] K)
    (W : Submodule K V) [FiniteDimensional K W],
    (B.domRestrict₁₂ W W).Nondegenerate →
    ∃! E : Module.End K V,
      E ^ 2 = E ∧ E.range = W ∧ E.ker = W.orthogonalBilin B.flip ∧
      (∀ w ∈ W, E w = w) ∧
      (∀ v, v - E v ∈ W.orthogonalBilin B.flip) ∧
      (∀ w ∈ W, ∀ v, B (E v) w = B v w)

/-- Nonsingularity of the actual restriction matrix H_ij = B(e_i,e_j). -/
def matrix_criterion : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V],
  ∀ (σ τ : K ≃+* K) (B : V →ₛₗ[σ.toRingHom] V →ₛₗ[τ.toRingHom] K)
    (W : Submodule K V) {n : ℕ} (e : Basis (Fin n) K W),
    (B.domRestrict₁₂ W W).Nondegenerate ↔
      IsUnit (Matrix.of (fun i j => B (e i) (e j)))

/-- The paper's coordinate solution, including conjugation in its second slot.
For τ = star this reads a = conjugate(H⁻¹ b(v)); for τ = id there is no conjugation.
The formula is required for any linear projection with the stated image/kernel. -/
def projection_coordinates : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V],
  ∀ (σ τ : K ≃+* K) (B : V →ₛₗ[σ.toRingHom] V →ₛₗ[τ.toRingHom] K)
    (W : Submodule K V) {n : ℕ} (e : Basis (Fin n) K W),
    (B.domRestrict₁₂ W W).Nondegenerate →
    ∀ (E : Module.End K V), E ^ 2 = E → E.range = W →
      E.ker = W.orthogonalBilin B → ∀ (v : V) (hv : E v ∈ W) (j : Fin n),
      e.repr ⟨E v, hv⟩ j = τ.symm
        (((Matrix.of (fun i k => B (e i) (e k)))⁻¹ *ᵥ
          (fun i => B (e i) v)) j)

/-- Empty equations: the complement is all V and the unique projection is zero. -/
def zero_subspace : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V],
  ∀ (σ τ : K ≃+* K) (B : V →ₛₗ[σ.toRingHom] V →ₛₗ[τ.toRingHom] K),
    (⊥ : Submodule K V).orthogonalBilin B = ⊤ ∧
    (⊥ : Submodule K V).orthogonalBilin B.flip = ⊤ ∧
    ∀ (E : Module.End K V), E.range = ⊥ → E = 0

/-- Explicitly identify the original two conventions with this general interface. -/
def bilinear_specialization : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V],
  ∀ (B : LinearMap.BilinForm K V) (W : Submodule K V) [FiniteDimensional K W],
    (B.restrict W).Nondegenerate →
      IsCompl W (W.orthogonalBilin B) ∧ IsCompl W (W.orthogonalBilin B.flip)

def sesquilinear_specialization : Prop :=
  ∀ {𝕂 X : Type*} [RCLike 𝕂] [AddCommGroup X] [Module 𝕂 X]
    (B : Specs.D05.M11.Hermitian.sesquilinearForm_value 𝕂 X)
    (W : Submodule 𝕂 X) [FiniteDimensional 𝕂 W],
    (B.domRestrict₁₂ W W).Nondegenerate →
      IsCompl W (W.orthogonalBilin B) ∧ IsCompl W (W.orthogonalBilin B.flip)

/-- Even with nondegenerate restriction, the two complements can be different.
Reuse the upstream form B(x,y)=x₀y₁ and take W=span((1,1)). -/
def complements_can_differ : Prop :=
  ∀ (K : Type*) [Field K],
    let B := Specs.D05.M11.Radicals.exampleForm K
    let W : Submodule K (Fin 2 → K) := K ∙ (fun _ => 1)
    (B.restrict W).Nondegenerate ∧ W.orthogonalBilin B ≠ W.orthogonalBilin B.flip

end Specs.D05.M11.Nondegenerate.OneSidedComplements
