import MathGenome.Internal.Specs.D05.M03.Image
import MathGenome.Internal.Specs.D05.M03.Kernel
import MathGenome.Internal.Specs.D05.M06.DirectSum

/-!
Independent statements for K05.06.projection, paper.tex:981–987.
Endomorphisms, images and kernels are the canonical Mathlib objects used by
the upstream goals. Binary direct sums use the upstream unique-expression
predicate, with `false` indexing the image and `true` the kernel.
All spaces are arbitrary vector spaces over the named field; in particular
there is no finite-dimensional or inner-product hypothesis.
-/

namespace Specs.D05.M06.Projection

/-- An idempotent fixes exactly the vectors in its image. -/
def range_iff_fixed : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (P : Module.End K V), P ^ 2 = P →
      ∀ v : V, v ∈ LinearMap.range P ↔ P v = v

/-- The explicit image/kernel decomposition in the source proof. -/
def decomposition_formula : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (P : Module.End K V), P ^ 2 = P → ∀ v : V,
      P v ∈ LinearMap.range P ∧ v - P v ∈ LinearMap.ker P ∧
        v = P v + (v - P v)

/-- The forward conclusion, using the actual image and kernel as summands. -/
def range_kernel_direct_sum : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (P : Module.End K V), P ^ 2 = P →
      Specs.D05.M06.DirectSum.UniqueDecomposition
        (fun b : Bool => if b then LinearMap.ker P else LinearMap.range P)

/-- Every specified internal decomposition determines one and only one
idempotent endomorphism having exactly those image and kernel subspaces. -/
def projection_exists_unique : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U W : Submodule K V),
    Specs.D05.M06.DirectSum.UniqueDecomposition
      (fun b : Bool => if b then W else U) →
    ∃! P : Module.End K V,
      P ^ 2 = P ∧ LinearMap.range P = U ∧ LinearMap.ker P = W

/-- The determined endomorphism sends a component sum to its U-component. -/
def projection_apply_sum : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U W : Submodule K V) (P : Module.End K V),
    P ^ 2 = P → LinearMap.range P = U → LinearMap.ker P = W →
      ∀ (u w : V), u ∈ U → w ∈ W → P (u + w) = u

end Specs.D05.M06.Projection
