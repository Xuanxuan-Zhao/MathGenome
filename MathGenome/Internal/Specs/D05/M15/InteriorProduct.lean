import MathGenome.Internal.Specs.D05.M15.Exterior
import MathGenome.Internal.Specs.D05.M07.Dual
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorPower.Pairing

/-! Independent specifications for K05.15.interior_product, paper.tex:3121–3136.
All fields and arbitrary-dimensional vector spaces are allowed. The tensor and
exterior algebras, quotient, and homogeneous submodules are the canonical upstream
objects. The tensor construction uses the free-algebra action on two copies of
T(V); its second component records signed deletion. No conclusion is assumed.
-/
noncomputable section
namespace Specs.D05.M15.InteriorProduct
universe u v
variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

/-- A generator acts on `(word, deletion)` by prepending itself. -/
def tensorAction (φ : Module.Dual K V) :
    V →ₗ[K] Module.End K (_root_.TensorAlgebra K V × _root_.TensorAlgebra K V) where
  toFun v :=
    { toFun := fun z => (_root_.TensorAlgebra.ι K v * z.1,
        φ v • z.1 - _root_.TensorAlgebra.ι K v * z.2)
      map_add' := by intros; ext <;> simp [mul_add, smul_add, sub_add_sub_comm]
      map_smul' := by intros; ext <;> simp [smul_sub, smul_smul, mul_comm] }
  map_add' := by intros; ext <;> simp [add_mul, add_smul]; abel
  map_smul' := by intros; ext <;> simp [smul_smul]

/-- The tensor-algebra signed contraction. -/
def tensorInterior (φ : Module.Dual K V) :
    _root_.TensorAlgebra K V →ₗ[K] _root_.TensorAlgebra K V where
  toFun t := ((_root_.TensorAlgebra.lift K (tensorAction φ) t) (1, 0)).2
  map_add' := by intros; simp
  map_smul' := by intros; simp

/-- The exterior contraction, without division by two or a factorial. -/
def interior : Module.Dual K V →ₗ[K]
    _root_.ExteriorAlgebra K V →ₗ[K] _root_.ExteriorAlgebra K V :=
  CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm K V))

/-- A word in an algebra, in its original order; the empty word is one. -/
def word {A : Type*} [Ring A] [Algebra K A] (ι : V →ₗ[K] A) (l : List V) : A :=
  (l.map ι).prod

/-- Literal signed deletion of each occurrence, indexed from zero. -/
def deletion {A : Type*} [Ring A] [Algebra K A]
    (ι : V →ₗ[K] A) (φ : Module.Dual K V) (l : List V) : A :=
  ∑ j : Fin l.length, ((-1 : K) ^ (j : ℕ) * φ (l.get j)) • word ι (l.eraseIdx j)

abbrev tensorInterior_type := (K : Type u) → (V : Type v) → [Field K] →
  [AddCommGroup V] → [Module K V] → Module.Dual K V →
    (_root_.TensorAlgebra K V →ₗ[K] _root_.TensorAlgebra K V)
abbrev tensorInterior_value : tensorInterior_type := fun _ _ _ _ _ => tensorInterior
abbrev interior_type := (K : Type u) → (V : Type v) → [Field K] →
  [AddCommGroup V] → [Module K V] → (Module.Dual K V →ₗ[K]
    _root_.ExteriorAlgebra K V →ₗ[K] _root_.ExteriorAlgebra K V)
abbrev interior_value : interior_type := fun _ _ _ _ _ => interior

-- Expected theorems are full propositions, not assumed certificates.
def tensor_one : Prop := ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V]
  [Module K V] (φ : Module.Dual K V), tensorInterior φ 1 = 0

def exterior_one : Prop := ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V]
  [Module K V] (φ : Module.Dual K V), interior φ 1 = 0

def tensor_word : Prop := ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V]
  [Module K V] (φ : Module.Dual K V) (l : List V),
  tensorInterior φ (word (_root_.TensorAlgebra.ι K) l) =
    deletion (_root_.TensorAlgebra.ι K) φ l

def exterior_word : Prop := ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V]
  [Module K V] (φ : Module.Dual K V) (l : List V),
  interior φ (word (_root_.ExteriorAlgebra.ι K) l) =
    deletion (_root_.ExteriorAlgebra.ι K) φ l

def tensor_leibniz : Prop := ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V]
  [Module K V] (φ : Module.Dual K V) (p : ℕ) (a b : _root_.TensorAlgebra K V),
  a ∈ LinearMap.range (_root_.TensorAlgebra.ι K (M := V)) ^ p →
  tensorInterior φ (a * b) = tensorInterior φ a * b + (-1 : K)^p • (a * tensorInterior φ b)

def exterior_leibniz : Prop := ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V]
  [Module K V] (φ : Module.Dual K V) (p : ℕ) (a b : _root_.ExteriorAlgebra K V),
  a ∈ ⋀[K]^p V →
  interior φ (a * b) = interior φ a * b + (-1 : K)^p • (a * interior φ b)

def tensor_degree : Prop := ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V]
  [Module K V] (φ : Module.Dual K V) (p : ℕ) (a : _root_.TensorAlgebra K V),
  a ∈ LinearMap.range (_root_.TensorAlgebra.ι K (M := V)) ^ (p+1) →
  tensorInterior φ a ∈ LinearMap.range (_root_.TensorAlgebra.ι K (M := V)) ^ p

def exterior_degree : Prop := ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V]
  [Module K V] (φ : Module.Dual K V) (p : ℕ) (a : _root_.ExteriorAlgebra K V),
  a ∈ ⋀[K]^(p+1) V → interior φ a ∈ ⋀[K]^p V

def tensor_square_generator : Prop := ∀ {K : Type u} {V : Type v} [Field K]
  [AddCommGroup V] [Module K V] (φ : Module.Dual K V) (v : V),
  tensorInterior φ (_root_.TensorAlgebra.ι K v * _root_.TensorAlgebra.ι K v) = 0

def quotient_compatibility : Prop := ∀ {K : Type u} {V : Type v} [Field K]
  [AddCommGroup V] [Module K V] (φ : Module.Dual K V) (t : _root_.TensorAlgebra K V),
  _root_.TensorAlgebra.toExterior (tensorInterior φ t) =
    interior φ (_root_.TensorAlgebra.toExterior t)

def preserves_ideal : Prop := ∀ {K : Type u} {V : Type v} [Field K]
  [AddCommGroup V] [Module K V] (φ : Module.Dual K V) (t : _root_.TensorAlgebra K V),
  t ∈ Specs.D05.M15.Exterior.definingIdeal_value K V →
    tensorInterior φ t ∈ Specs.D05.M15.Exterior.definingIdeal_value K V

def descent_unique : Prop := ∀ {K : Type u} {V : Type v} [Field K]
  [AddCommGroup V] [Module K V] (φ : Module.Dual K V),
  ∃! D : _root_.ExteriorAlgebra K V →ₗ[K] _root_.ExteriorAlgebra K V,
    ∀ t, D (_root_.TensorAlgebra.toExterior t) =
      _root_.TensorAlgebra.toExterior (tensorInterior φ t)

def tensor_square_zero : Prop := ∀ {K : Type u} {V : Type v} [Field K]
  [AddCommGroup V] [Module K V] (φ : Module.Dual K V) (a : _root_.TensorAlgebra K V),
  tensorInterior φ (tensorInterior φ a) = 0

def exterior_square_zero : Prop := ∀ {K : Type u} {V : Type v} [Field K]
  [AddCommGroup V] [Module K V] (φ : Module.Dual K V) (a : _root_.ExteriorAlgebra K V),
  interior φ (interior φ a) = 0

def tensor_anticommutation : Prop := ∀ {K : Type u} {V : Type v} [Field K]
  [AddCommGroup V] [Module K V] (φ ψ : Module.Dual K V) (a : _root_.TensorAlgebra K V),
  tensorInterior φ (tensorInterior ψ a) + tensorInterior ψ (tensorInterior φ a) = 0

def exterior_anticommutation : Prop := ∀ {K : Type u} {V : Type v} [Field K]
  [AddCommGroup V] [Module K V] (φ ψ : Module.Dual K V) (a : _root_.ExteriorAlgebra K V),
  interior φ (interior ψ a) + interior ψ (interior φ a) = 0

def cartan_identity : Prop := ∀ {K : Type u} {V : Type v} [Field K]
  [AddCommGroup V] [Module K V] (φ : Module.Dual K V) (v : V) (a : _root_.ExteriorAlgebra K V),
  interior φ (_root_.ExteriorAlgebra.ι K v * a) +
    _root_.ExteriorAlgebra.ι K v * interior φ a = φ v • a

/-- The exterior universal property turns contraction into an algebra map to
opposite endomorphisms. Opposite multiplication fixes the order of composition. -/
def higherInteriorOpp : _root_.ExteriorAlgebra K (Module.Dual K V) →ₐ[K]
    (Module.End K (_root_.ExteriorAlgebra K V))ᵐᵒᵖ :=
  _root_.ExteriorAlgebra.lift K ⟨(MulOpposite.opLinearEquiv K).toLinearMap.comp interior,
    fun φ => by
      apply MulOpposite.unop_injective
      change interior φ * interior φ = 0
      apply LinearMap.ext
      intro a
      exact CliffordAlgebra.contractLeft_contractLeft φ a⟩

/-- Contraction by any exterior covector, with reverse composition order. -/
def higherInterior : _root_.ExteriorAlgebra K (Module.Dual K V) →ₗ[K]
    Module.End K (_root_.ExteriorAlgebra K V) :=
  (MulOpposite.opLinearEquiv K).symm.toLinearMap.comp higherInteriorOpp.toLinearMap

abbrev higherInterior_type := (K : Type u) → (V : Type v) → [Field K] →
  [AddCommGroup V] → [Module K V] → (_root_.ExteriorAlgebra K (Module.Dual K V) →ₗ[K]
    Module.End K (_root_.ExteriorAlgebra K V))
abbrev higherInterior_value : higherInterior_type := fun _ _ _ _ _ => higherInterior

def higher_generator : Prop := ∀ {K : Type u} {V : Type v} [Field K]
  [AddCommGroup V] [Module K V] (φ : Module.Dual K V),
  higherInterior (_root_.ExteriorAlgebra.ι K φ) = interior φ

def higher_product : Prop := ∀ {K : Type u} {V : Type v} [Field K]
  [AddCommGroup V] [Module K V] (α β : _root_.ExteriorAlgebra K (Module.Dual K V)),
  higherInterior (α * β) = (higherInterior β).comp (higherInterior α)

def higher_unit : Prop := ∀ {K : Type u} {V : Type v} [Field K]
  [AddCommGroup V] [Module K V], higherInterior (1 : _root_.ExteriorAlgebra K (Module.Dual K V)) =
    LinearMap.id

/-- A dual pair gives the paper's concrete counterexample to the proposed
minus-one antiderivation identity for a contraction of degree minus two. -/
def higher_guard : Prop := ∀ {K : Type u} {V : Type v} [Field K]
  [AddCommGroup V] [Module K V] (φ ψ : Module.Dual K V) (v w : V),
  φ v = 1 → φ w = 0 → ψ v = 0 → ψ w = 1 →
  let D := higherInterior (_root_.ExteriorAlgebra.ι K φ * _root_.ExteriorAlgebra.ι K ψ)
  let a := _root_.ExteriorAlgebra.ι K v
  let b := _root_.ExteriorAlgebra.ι K w
  D (a*b) = 1 ∧ D a = 0 ∧ D b = 0 ∧ D (a*b) ≠ D a*b - a*D b

/-- Restriction to a tensor power is a linear map with exactly the stated word formula. -/
def tensor_power_formula : Prop := ∀ {K : Type u} {V : Type v} [Field K]
  [AddCommGroup V] [Module K V] (φ : Module.Dual K V) (p : ℕ) (x : Fin p → V),
  tensorInterior φ (TensorPower.toTensorAlgebra (PiTensorProduct.tprod K x)) =
    deletion (_root_.TensorAlgebra.ι K) φ (List.ofFn x)

def exterior_power_formula : Prop := ∀ {K : Type u} {V : Type v} [Field K]
  [AddCommGroup V] [Module K V] (φ : Module.Dual K V) (p : ℕ) (x : Fin p → V),
  interior φ (_root_.ExteriorAlgebra.ιMulti K p x) =
    deletion (_root_.ExteriorAlgebra.ι K) φ (List.ofFn x)

def higher_word : Prop := ∀ {K : Type u} {V : Type v} [Field K]
  [AddCommGroup V] [Module K V] (l : List (Module.Dual K V)) (a : _root_.ExteriorAlgebra K V),
  higherInterior (word (_root_.ExteriorAlgebra.ι K) l) a =
    l.foldl (fun a φ => interior φ a) a

/-- The higher-contraction guard has an actual instance over every field. -/
def higher_counterexample : Prop := ∀ {K : Type u} [Field K],
  ∃ (α : _root_.ExteriorAlgebra K (Module.Dual K (K × K)))
    (a b : _root_.ExteriorAlgebra K (K × K)),
    higherInterior α (a*b) ≠ higherInterior α a*b - a*higherInterior α b

/-- Higher contraction is adjoint to left wedge multiplication for the determinant
pairing. The existential includes the homogeneous restriction of its output.
No factorial is used; degrees zero and arbitrary characteristic are included. -/
def higher_pairing : Prop := ∀ {K : Type u} {V : Type v} [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] (r q : ℕ)
  (α : ⋀[K]^r (Module.Dual K V)) (β : ⋀[K]^q (Module.Dual K V))
  (u : ⋀[K]^(r+q) V),
  ∃ v : ⋀[K]^q V, (v : _root_.ExteriorAlgebra K V) = higherInterior α u ∧
    exteriorPower.pairingDual K V q β v =
      exteriorPower.pairingDual K V (r+q)
        ⟨(α : _root_.ExteriorAlgebra K (Module.Dual K V)) * β,
          SetLike.GradedMul.mul_mem α.property β.property⟩ u

end Specs.D05.M15.InteriorProduct
