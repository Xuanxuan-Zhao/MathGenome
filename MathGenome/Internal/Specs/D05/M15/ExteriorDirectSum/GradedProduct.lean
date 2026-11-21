import MathGenome.Internal.Specs.D05.M15.WedgeSign
import Mathlib.LinearAlgebra.TensorProduct.Graded.Internal

/-!
K05.15.exterior_direct_sum, paper.tex:3110–3119, the graded-product stage.
The factors are the upstream exterior algebras, without dimension or characteristic
restrictions. `GradedTensorProduct` is the underlying algebraic tensor module with
Koszul multiplication, rather than the unsigned tensor-product ring. Total degree
is defined by the span of the homogeneous elementary tensors. In particular the
existence of a decomposition is a theorem below, not an assumed certificate.
-/

noncomputable section
namespace Specs.D05.M15.ExteriorDirectSum.GradedProduct

universe u v w
open scoped TensorProduct

abbrev gradedTensor_type := (K : Type u) → (V : Type v) → (W : Type w) →
  [Field K] → [AddCommGroup V] → [Module K V] →
  [AddCommGroup W] → [Module K W] → Type (max u v w)

abbrev gradedTensor_value : gradedTensor_type := fun K V W _ _ _ _ _ =>
  GradedTensorProduct K (fun p : ℕ => ⋀[K]^p V) (fun q : ℕ => ⋀[K]^q W)

variable (K : Type u) (V : Type v) (W : Type w)
  [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

abbrev tensorEquiv_value :
    (_root_.ExteriorAlgebra K V ⊗[K] _root_.ExteriorAlgebra K W) ≃ₗ[K]
      gradedTensor_value K V W :=
  GradedTensorProduct.of K _ _

abbrev multiplication_value : gradedTensor_value K V W →ₗ[K]
    gradedTensor_value K V W →ₗ[K] gradedTensor_value K V W :=
  GradedTensorProduct.mulHom _ _

/-- The paper's total-degree homogeneous part, defined by generators. -/
def homogeneousPart_value (n : ℕ) : Submodule K (gradedTensor_value K V W) :=
  Submodule.span K {t | ∃ (p q : ℕ), p + q = n ∧
    ∃ (a : ⋀[K]^p V) (b : ⋀[K]^q W), t = GradedTensorProduct.tmul K a.val b.val}

/-- The linear map (v,w) ↦ ι(v) ⊗ 1 + 1 ⊗ ι(w). -/
def generator_value : V × W →ₗ[K] gradedTensor_value K V W :=
  ((GradedTensorProduct.includeLeft _ _).toLinearMap.comp
    ((_root_.ExteriorAlgebra.ι K).comp (LinearMap.fst K V W))) +
  ((GradedTensorProduct.includeRight _ _).toLinearMap.comp
    ((_root_.ExteriorAlgebra.ι K).comp (LinearMap.snd K V W)))

abbrev tensorEquiv_type :=
  (_root_.ExteriorAlgebra K V ⊗[K] _root_.ExteriorAlgebra K W) ≃ₗ[K]
    gradedTensor_value K V W
abbrev multiplication_type := gradedTensor_value K V W →ₗ[K]
  gradedTensor_value K V W →ₗ[K] gradedTensor_value K V W
abbrev homogeneousPart_type := ℕ → Submodule K (gradedTensor_value K V W)
abbrev generator_type := V × W →ₗ[K] gradedTensor_value K V W

variable {K V W}

def underlying_tensor : Prop :=
  ∀ (a : _root_.ExteriorAlgebra K V) (b : _root_.ExteriorAlgebra K W),
    tensorEquiv_value K V W (a ⊗ₜ[K] b) = GradedTensorProduct.tmul K a b

def homogeneous_product : Prop :=
  ∀ (q r : ℕ) (a : _root_.ExteriorAlgebra K V) (b : ⋀[K]^q W)
    (c : ⋀[K]^r V) (d : _root_.ExteriorAlgebra K W),
    (GradedTensorProduct.tmul K a b.val : gradedTensor_value K V W) *
      GradedTensorProduct.tmul K c.val d =
      (-1 : K) ^ (q * r) • GradedTensorProduct.tmul K (a * c.val) (b.val * d)

def bilinear_extension : Prop :=
  ∀ x y : gradedTensor_value K V W, multiplication_value K V W x y = x * y

/-- The homogeneous rule determines the product on the whole tensor module. -/
def unique_bilinear_extension : Prop :=
  ∀ f : gradedTensor_value K V W →ₗ[K]
      gradedTensor_value K V W →ₗ[K] gradedTensor_value K V W,
    (∀ (p q r s : ℕ) (a : ⋀[K]^p V) (b : ⋀[K]^q W)
      (c : ⋀[K]^r V) (d : ⋀[K]^s W),
      f (GradedTensorProduct.tmul K a.val b.val) (GradedTensorProduct.tmul K c.val d.val) =
        (-1 : K) ^ (q * r) • GradedTensorProduct.tmul K (a.val * c.val) (b.val * d.val)) →
    f = multiplication_value K V W

def associative : Prop :=
  ∀ x y z : gradedTensor_value K V W, (x * y) * z = x * (y * z)

def tensor_unit : Prop :=
  tensorEquiv_value K V W ((1 : _root_.ExteriorAlgebra K V) ⊗ₜ[K]
    (1 : _root_.ExteriorAlgebra K W)) = 1 ∧
  ∀ x : gradedTensor_value K V W, 1 * x = x ∧ x * 1 = x

def homogeneous_multiplication : Prop :=
  ∀ (m n : ℕ) (x y : gradedTensor_value K V W),
    x ∈ homogeneousPart_value K V W m → y ∈ homogeneousPart_value K V W n →
      x * y ∈ homogeneousPart_value K V W (m + n)

def graded_structure : Prop := Nonempty (GradedAlgebra (homogeneousPart_value K V W))

def generator_formula : Prop :=
  ∀ (v : V) (w : W), generator_value K V W (v, w) =
    GradedTensorProduct.tmul K (_root_.ExteriorAlgebra.ι K v) 1 +
      GradedTensorProduct.tmul K 1 (_root_.ExteriorAlgebra.ι K w)

def generator_degree_one : Prop :=
  ∀ (v : V) (w : W), generator_value K V W (v, w) ∈ homogeneousPart_value K V W 1

def generator_square_zero : Prop :=
  ∀ (v : V) (w : W), generator_value K V W (v, w) * generator_value K V W (v, w) = 0

end Specs.D05.M15.ExteriorDirectSum.GradedProduct

/-! Closed expected declaration types. These quantify the scalar field and both
spaces, so bindings check the complete declarations rather than one fixed fiber. -/
namespace Specs.D05.M15.ExteriorDirectSum.GradedProduct.Expected

universe u v w
abbrev tensorEquiv_type := ∀ (K : Type u) (V : Type v) (W : Type w)
  [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W],
  GradedProduct.tensorEquiv_type K V W
abbrev tensorEquiv_value : tensorEquiv_type := @GradedProduct.tensorEquiv_value
abbrev multiplication_type := ∀ (K : Type u) (V : Type v) (W : Type w)
  [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W],
  GradedProduct.multiplication_type K V W
abbrev multiplication_value : multiplication_type := @GradedProduct.multiplication_value
abbrev homogeneousPart_type := ∀ (K : Type u) (V : Type v) (W : Type w)
  [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W],
  GradedProduct.homogeneousPart_type K V W
abbrev homogeneousPart_value : homogeneousPart_type := @GradedProduct.homogeneousPart_value
abbrev generator_type := ∀ (K : Type u) (V : Type v) (W : Type w)
  [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W],
  GradedProduct.generator_type K V W
abbrev generator_value : generator_type := @GradedProduct.generator_value

def underlying_tensor : Prop :=
  ∀ {K : Type u} {V : Type v} {W : Type w}
    [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W],
    GradedProduct.underlying_tensor (K := K) (V := V) (W := W)

def homogeneous_product : Prop :=
  ∀ {K : Type u} {V : Type v} {W : Type w}
    [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W],
    GradedProduct.homogeneous_product (K := K) (V := V) (W := W)

def bilinear_extension : Prop :=
  ∀ {K : Type u} {V : Type v} {W : Type w}
    [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W],
    GradedProduct.bilinear_extension (K := K) (V := V) (W := W)

def unique_bilinear_extension : Prop :=
  ∀ {K : Type u} {V : Type v} {W : Type w}
    [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W],
    GradedProduct.unique_bilinear_extension (K := K) (V := V) (W := W)

def associative : Prop :=
  ∀ {K : Type u} {V : Type v} {W : Type w}
    [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W],
    GradedProduct.associative (K := K) (V := V) (W := W)

def tensor_unit : Prop :=
  ∀ {K : Type u} {V : Type v} {W : Type w}
    [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W],
    GradedProduct.tensor_unit (K := K) (V := V) (W := W)

def homogeneous_multiplication : Prop :=
  ∀ {K : Type u} {V : Type v} {W : Type w}
    [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W],
    GradedProduct.homogeneous_multiplication (K := K) (V := V) (W := W)

def graded_structure : Prop :=
  ∀ {K : Type u} {V : Type v} {W : Type w}
    [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W],
    GradedProduct.graded_structure (K := K) (V := V) (W := W)

def generator_formula : Prop :=
  ∀ {K : Type u} {V : Type v} {W : Type w}
    [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W],
    GradedProduct.generator_formula (K := K) (V := V) (W := W)

def generator_degree_one : Prop :=
  ∀ {K : Type u} {V : Type v} {W : Type w}
    [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W],
    GradedProduct.generator_degree_one (K := K) (V := V) (W := W)

def generator_square_zero : Prop :=
  ∀ {K : Type u} {V : Type v} {W : Type w}
    [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W],
    GradedProduct.generator_square_zero (K := K) (V := V) (W := W)

end Specs.D05.M15.ExteriorDirectSum.GradedProduct.Expected
