import MathGenome.Internal.Specs.D05.M15.ExteriorDirectSum.GradedProduct
import MathGenome.Internal.D05.M15.WedgeSign
import Mathlib.LinearAlgebra.ExteriorAlgebra.Product
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

noncomputable section
namespace D05.M15.ExteriorDirectSum.GradedProduct

universe u v w
open scoped TensorProduct
open Specs.D05.M15.ExteriorDirectSum.GradedProduct

abbrev gradedTensor : gradedTensor_type := @gradedTensor_value

variable (K : Type u) (V : Type v) (W : Type w)
  [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

abbrev tensorEquiv : tensorEquiv_type K V W := tensorEquiv_value K V W
abbrev multiplication : multiplication_type K V W := multiplication_value K V W
abbrev homogeneousPart : homogeneousPart_type K V W := homogeneousPart_value K V W
abbrev generator : generator_type K V W := generator_value K V W

variable {K V W}

theorem underlying_tensor : underlying_tensor (K := K) (V := V) (W := W) := by
  intro a b
  rfl

theorem homogeneous_product : homogeneous_product (K := K) (V := V) (W := W) := by
  intro q r a b c d
  simpa only [Units.smul_def, Units.val_pow_eq_pow_val, Units.val_neg,
    Units.val_one, ← Int.cast_smul_eq_zsmul K, Int.cast_pow, Int.cast_neg,
    Int.cast_one] using
    (GradedTensorProduct.tmul_coe_mul_coe_tmul
      (fun p : ℕ => ⋀[K]^p V) (fun p : ℕ => ⋀[K]^p W) a b c d)

theorem bilinear_extension : bilinear_extension (K := K) (V := V) (W := W) := by
  intro x y
  rfl

theorem associative : associative (K := K) (V := V) (W := W) := by
  exact mul_assoc

theorem tensor_unit : tensor_unit (K := K) (V := V) (W := W) := by
  exact ⟨rfl, fun x => ⟨one_mul x, mul_one x⟩⟩

theorem generator_formula : generator_formula (K := K) (V := V) (W := W) := by
  intro v w
  rfl

/-- The scalar unit has total degree zero. -/
theorem one_mem : (1 : gradedTensor K V W) ∈ homogeneousPart K V W 0 := by
  apply Submodule.subset_span
  exact ⟨0, 0, rfl, ⟨1, SetLike.one_mem_graded _⟩,
    ⟨1, SetLike.one_mem_graded _⟩, rfl⟩

theorem tmul_mem (p q : ℕ) (a : ⋀[K]^p V) (b : ⋀[K]^q W) :
    GradedTensorProduct.tmul K a.val b.val ∈ homogeneousPart K V W (p + q) :=
  Submodule.subset_span ⟨p, q, rfl, a, b, rfl⟩

theorem generator_degree_one : generator_degree_one (K := K) (V := V) (W := W) := by
  intro v w
  apply Submodule.add_mem
  · exact tmul_mem 1 0 ⟨_root_.ExteriorAlgebra.ι K v, by simp⟩
      ⟨1, SetLike.one_mem_graded _⟩
  · exact tmul_mem 0 1 ⟨1, SetLike.one_mem_graded _⟩
      ⟨_root_.ExteriorAlgebra.ι K w, by simp⟩

/-- Equality of linear maps can be tested on homogeneous elementary tensors. -/
theorem hom_ext_homogeneous {H : Type*} [AddCommGroup H] [Module K H]
    {f g : gradedTensor K V W →ₗ[K] H}
    (h : ∀ (p q : ℕ) (a : ⋀[K]^p V) (b : ⋀[K]^q W),
      f (GradedTensorProduct.tmul K a.val b.val) =
        g (GradedTensorProduct.tmul K a.val b.val)) : f = g := by
  apply GradedTensorProduct.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro b
  change f (GradedTensorProduct.tmul K a b) = g (GradedTensorProduct.tmul K a b)
  induction a using DirectSum.Decomposition.inductionOn (fun p : ℕ => ⋀[K]^p V) with
  | zero => simp [GradedTensorProduct.tmul]
  | add a a' ha ha' => simp_all [GradedTensorProduct.tmul, TensorProduct.add_tmul]
  | @homogeneous p a =>
    induction b using DirectSum.Decomposition.inductionOn (fun q : ℕ => ⋀[K]^q W) with
    | zero => simp [GradedTensorProduct.tmul]
    | add b b' hb hb' => simp_all [GradedTensorProduct.tmul, TensorProduct.tmul_add]
    | @homogeneous q b =>
      exact h p q a b

theorem unique_bilinear_extension :
    unique_bilinear_extension (K := K) (V := V) (W := W) := by
  intro f hf
  apply hom_ext_homogeneous
  intro p q a b
  apply hom_ext_homogeneous
  intro r s c d
  exact (hf p q r s a b c d).trans (homogeneous_product q r a.val b c d.val).symm

theorem homogeneous_multiplication :
    homogeneous_multiplication (K := K) (V := V) (W := W) := by
  intro m n x y hx hy
  refine Submodule.span_induction₂ (p := fun x y _ _ =>
    x * y ∈ homogeneousPart K V W (m + n)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨p, q, hpq, a, b, rfl⟩ ⟨r, s, hrs, c, d, rfl⟩
    rw [homogeneous_product]
    apply Submodule.smul_mem
    have h := tmul_mem (p + r) (q + s)
      ⟨a.val * c.val, SetLike.mul_mem_graded a.property c.property⟩
      ⟨b.val * d.val, SetLike.mul_mem_graded b.property d.property⟩
    have heq : m + n = (p + r) + (q + s) := by omega
    simpa only [heq] using h
  all_goals simp_all [add_mul, mul_add, Submodule.add_mem, Submodule.smul_mem]

/-- The standard product equivalence is used only to establish directness of
our explicitly defined homogeneous spans, not as a hypothesis of the product. -/
private abbrev comparison := _root_.ExteriorAlgebra.prodEquivTensor K V W

private theorem comparison_homogeneous (n : ℕ)
    (x : _root_.ExteriorAlgebra K (V × W)) (hx : x ∈ ⋀[K]^n (V × W)) :
    comparison (K := K) (V := V) (W := W) x ∈ homogeneousPart K V W n := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [AlgEquiv.commutes]
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (homogeneousPart K V W 0).smul_mem r one_mem
  | add x y n hx hy ihx ihy =>
    rw [map_add]
    exact Submodule.add_mem _ ihx ihy
  | mem_mul m hm n x hx ih =>
    obtain ⟨⟨v, w⟩, rfl⟩ := hm
    rw [map_mul]
    have hgen : comparison (K := K) (V := V) (W := W)
        (_root_.ExteriorAlgebra.ι K (v, w)) = generator K V W (v, w) :=
      _root_.ExteriorAlgebra.prodEquivTensorForward_ι_apply K V W (v, w)
    rw [hgen]
    simpa only [Nat.add_comm 1 n] using
      (homogeneous_multiplication 1 n _ _ (generator_degree_one v w) ih)

private theorem homogeneousPart_eq_map (n : ℕ) :
    homogeneousPart K V W n = (⋀[K]^n (V × W)).map
      (comparison (K := K) (V := V) (W := W)).toLinearMap := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro t ⟨p, q, hpq, a, b, rfl⟩
    refine ⟨(comparison (K := K) (V := V) (W := W)).symm
      (GradedTensorProduct.tmul K a.val b.val), ?_, by simp⟩
    rw [_root_.ExteriorAlgebra.prodEquivTensor_symm_tmul]
    subst n
    exact SetLike.mul_mem_graded
      (D05.M15.WedgeSign.degree_preserved (LinearMap.inl K V W) p a.val a.property)
      (D05.M15.WedgeSign.degree_preserved (LinearMap.inr K V W) q b.val b.property)
  · rintro t ⟨x, hx, rfl⟩
    exact comparison_homogeneous n x hx

/-- A genuine total-degree grading of the signed tensor-product algebra. -/
theorem graded_structure : graded_structure (K := K) (V := V) (W := W) := by
  classical
  let e := comparison (K := K) (V := V) (W := W)
  have h := DirectSum.Decomposition.isInternal (fun n : ℕ => ⋀[K]^n (V × W))
  have heq : homogeneousPart K V W = fun n => (⋀[K]^n (V × W)).map e.toLinearMap :=
    funext homogeneousPart_eq_map
  have hind : iSupIndep (homogeneousPart K V W) := by
    rw [heq]
    exact LinearMap.iSupIndep_map e.toLinearMap e.injective h.submodule_iSupIndep
  have htop : iSup (homogeneousPart K V W) = ⊤ := by
    rw [heq]
    rw [← Submodule.map_iSup, h.submodule_iSup_eq_top]
    exact Submodule.map_top e.toLinearMap |>.trans (LinearMap.range_eq_top.mpr e.surjective)
  letI : SetLike.GradedMonoid (homogeneousPart K V W) :=
    { one_mem := one_mem
      mul_mem := fun i j x y hx hy => homogeneous_multiplication i j x y hx hy }
  exact ⟨(DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop).gradedAlgebra⟩

theorem generator_square_zero : generator_square_zero (K := K) (V := V) (W := W) := by
  intro v w
  let a : ⋀[K]^1 V := ⟨_root_.ExteriorAlgebra.ι K v, by simp⟩
  let b : ⋀[K]^1 W := ⟨_root_.ExteriorAlgebra.ι K w, by simp⟩
  change ((GradedTensorProduct.tmul K a.val 1 : gradedTensor K V W) +
    GradedTensorProduct.tmul K 1 b.val) *
    (GradedTensorProduct.tmul K a.val 1 + GradedTensorProduct.tmul K 1 b.val) = 0
  rw [add_mul, mul_add, mul_add, GradedTensorProduct.tmul_one_mul_coe_tmul,
    GradedTensorProduct.tmul_one_mul_one_tmul, GradedTensorProduct.tmul_coe_mul_coe_tmul,
    GradedTensorProduct.tmul_coe_mul_one_tmul]
  simp [a, b, Units.neg_smul, GradedTensorProduct.tmul]

end D05.M15.ExteriorDirectSum.GradedProduct
