import MathGenome.Internal.Specs.D05.M15.ExteriorDirectSum.GradedProduct
import MathGenome.Internal.Specs.D05.M15.TensorDirectSum

/-!
K05.15.exterior_direct_sum, paper.tex:3110–3119.
The signed tensor algebra, its Koszul multiplication, and its total homogeneous
spans are the canonical objects from the graded-product prerequisite. The first
statement requires an actual graded algebra equivalence with the prescribed
forward and inverse maps. The second requires the full fixed-degree external
sum, with its inverse specified on elementary tensors in every summand.
There is no dimension, characteristic, or nonzero-space hypothesis.
-/
noncomputable section
namespace Specs.D05.M15.ExteriorDirectSum

open scoped TensorProduct DirectSum
universe u v w

/-- The ordered degree pairs occurring in the paper's sum `i + j = n`. -/
abbrev DegreePairs (n : ℕ) := {ij : ℕ × ℕ // ij.1 + ij.2 = n}

abbrev DegreePiece (K : Type u) (V : Type v) (W : Type w)
    [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (ij : ℕ × ℕ) := (⋀[K]^ij.1 V) ⊗[K] (⋀[K]^ij.2 W)

/-- Both formulas and compatibility with the actual homogeneous submodules. -/
def algebra_equivalence : Prop :=
  ∀ (K : Type u) (V : Type v) (W : Type w)
    [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W],
    ∃ e : _root_.ExteriorAlgebra K (V × W) ≃ₐ[K]
        GradedProduct.gradedTensor_value K V W,
      (∀ (v : V) (w : W), e (_root_.ExteriorAlgebra.ι K (v, w)) =
        GradedProduct.generator_value K V W (v, w)) ∧
      (∀ (a : _root_.ExteriorAlgebra K V) (b : _root_.ExteriorAlgebra K W),
        e.symm (GradedTensorProduct.tmul K a b) =
          _root_.ExteriorAlgebra.map (LinearMap.inl K V W) a *
            _root_.ExteriorAlgebra.map (LinearMap.inr K V W) b) ∧
      (∀ (n : ℕ) (x : _root_.ExteriorAlgebra K (V × W)),
        e x ∈ GradedProduct.homogeneousPart_value K V W n ↔ x ∈ ⋀[K]^n (V × W))

/-- The inverse wedges the left factors before the right factors. Degree zero
is included, with the usual scalar units; the sum is always finitely supported. -/
def degree_decomposition : Prop :=
  ∀ (K : Type u) (V : Type v) (W : Type w)
    [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (n : ℕ),
    ∃ e : (⋀[K]^n (V × W)) ≃ₗ[K]
        ⨁ ij : DegreePairs n, DegreePiece K V W ij.val,
      ∀ (ij : DegreePairs n) (a : ⋀[K]^ij.val.1 V) (b : ⋀[K]^ij.val.2 W),
        ((e.symm (DirectSum.lof K (DegreePairs n)
          (fun ij => DegreePiece K V W ij.val) ij (a ⊗ₜ[K] b)) :
            ⋀[K]^n (V × W)) : _root_.ExteriorAlgebra K (V × W)) =
          _root_.ExteriorAlgebra.map (LinearMap.inl K V W) a.val *
            _root_.ExteriorAlgebra.map (LinearMap.inr K V W) b.val

end Specs.D05.M15.ExteriorDirectSum
