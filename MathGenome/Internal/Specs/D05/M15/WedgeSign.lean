import MathGenome.Internal.Specs.D05.M15.Exterior
import MathGenome.Internal.Specs.D05.M15.TensorMaps

/-!
Independent statements for K05.15.wedge_sign, paper.tex:2922–2926.
The algebra and its homogeneous parts are exactly the upstream square-relation
quotient and submodules. Multiplication denotes wedge multiplication. The sign
is a scalar in the arbitrary field K; no characteristic or dimension restriction
is imposed. The tensor map, quotient descent, and degree restrictions are linked
by commuting diagrams and elementary formulas, including the empty word.
-/

noncomputable section
namespace Specs.D05.M15.WedgeSign

universe u v w x
open scoped TensorProduct

abbrev tensorMap_type :=
  ∀ {K : Type u} {V : Type v} {W : Type w} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W],
  (V →ₗ[K] W) → (_root_.TensorAlgebra K V →ₐ[K] _root_.TensorAlgebra K W)

abbrev tensorMap_value : tensorMap_type :=
  fun {K _ _} _ _ _ _ _ T => _root_.TensorAlgebra.lift K ((_root_.TensorAlgebra.ι K).comp T)

abbrev exteriorMap_type :=
  ∀ {K : Type u} {V : Type v} {W : Type w} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W],
  (V →ₗ[K] W) → (_root_.ExteriorAlgebra K V →ₐ[K] _root_.ExteriorAlgebra K W)

abbrev exteriorMap_value : exteriorMap_type :=
  fun {_ _ _} _ _ _ _ _ T => _root_.ExteriorAlgebra.map T

abbrev powerMap_type :=
  ∀ {K : Type u} {V : Type v} {W : Type w} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W],
  (p : ℕ) → (V →ₗ[K] W) → ((⋀[K]^p V) →ₗ[K] (⋀[K]^p W))

abbrev powerMap_value : powerMap_type :=
  fun {_ _ _} _ _ _ _ _ p T => exteriorPower.map p T

def elementary_sign : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (p q : ℕ) (a : Fin p → V) (b : Fin q → V),
    _root_.ExteriorAlgebra.ιMulti K p a * _root_.ExteriorAlgebra.ιMulti K q b =
      (-1 : K) ^ (p * q) •
        (_root_.ExteriorAlgebra.ιMulti K q b * _root_.ExteriorAlgebra.ιMulti K p a)

def graded_comm : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (p q : ℕ) (a b : _root_.ExteriorAlgebra K V),
    a ∈ Specs.D05.M15.Exterior.homogeneousPart_value K V p →
    b ∈ Specs.D05.M15.Exterior.homogeneousPart_value K V q →
      a * b = (-1 : K) ^ (p * q) • (b * a)

def tensor_map_generator : Prop :=
  ∀ {K : Type u} {V : Type v} {W : Type w} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W],
  ∀ (T : V →ₗ[K] W) (v : V),
    tensorMap_value T (_root_.TensorAlgebra.ι K v) = _root_.TensorAlgebra.ι K (T v)

def tensor_map_word : Prop :=
  ∀ {K : Type u} {V : Type v} {W : Type w} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W],
  ∀ (T : V →ₗ[K] W) (p : ℕ) (a : Fin p → V),
    tensorMap_value T (TensorPower.toTensorAlgebra (PiTensorProduct.tprod K a)) =
      TensorPower.toTensorAlgebra (PiTensorProduct.tprod K (T ∘ a))

def tensor_map_homogeneous : Prop :=
  ∀ {K : Type u} {V : Type v} {W : Type w} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W],
  ∀ (T : V →ₗ[K] W) (p : ℕ) (a : TensorPower K p V),
    tensorMap_value T (TensorPower.toTensorAlgebra a) =
      TensorPower.toTensorAlgebra (PiTensorProduct.map (fun _ : Fin p => T) a)

def tensor_map_square : Prop :=
  ∀ {K : Type u} {V : Type v} {W : Type w} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W],
  ∀ (T : V →ₗ[K] W) (v : V),
    tensorMap_value T (_root_.TensorAlgebra.ι K v * _root_.TensorAlgebra.ι K v) =
      _root_.TensorAlgebra.ι K (T v) * _root_.TensorAlgebra.ι K (T v)

def ideal_preserved : Prop :=
  ∀ {K : Type u} {V : Type v} {W : Type w} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W],
  ∀ (T : V →ₗ[K] W) (a : _root_.TensorAlgebra K V),
    a ∈ Specs.D05.M15.Exterior.definingIdeal_value K V →
      tensorMap_value T a ∈ Specs.D05.M15.Exterior.definingIdeal_value K W

def quotient_naturality : Prop :=
  ∀ {K : Type u} {V : Type v} {W : Type w} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W],
  ∀ T : V →ₗ[K] W,
    (exteriorMap_value T).comp (Specs.D05.M15.Exterior.quotientMap_value K V) =
      (Specs.D05.M15.Exterior.quotientMap_value K W).comp (tensorMap_value T)

def exterior_map_generator : Prop :=
  ∀ {K : Type u} {V : Type v} {W : Type w} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W],
  ∀ (T : V →ₗ[K] W) (v : V),
    exteriorMap_value T (_root_.ExteriorAlgebra.ι K v) = _root_.ExteriorAlgebra.ι K (T v)

def exterior_map_word : Prop :=
  ∀ {K : Type u} {V : Type v} {W : Type w} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W],
  ∀ (T : V →ₗ[K] W) (p : ℕ) (a : Fin p → V),
    exteriorMap_value T (_root_.ExteriorAlgebra.ιMulti K p a) =
      _root_.ExteriorAlgebra.ιMulti K p (T ∘ a)

def exterior_map_unique : Prop :=
  ∀ {K : Type u} {V : Type v} {W : Type w} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W],
  ∀ (T : V →ₗ[K] W) (F : _root_.ExteriorAlgebra K V →ₐ[K] _root_.ExteriorAlgebra K W),
    (∀ v, F (_root_.ExteriorAlgebra.ι K v) = _root_.ExteriorAlgebra.ι K (T v)) →
      F = exteriorMap_value T

def degree_preserved : Prop :=
  ∀ {K : Type u} {V : Type v} {W : Type w} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W],
  ∀ (T : V →ₗ[K] W) (p : ℕ) (a : _root_.ExteriorAlgebra K V),
    a ∈ Specs.D05.M15.Exterior.homogeneousPart_value K V p →
      exteriorMap_value T a ∈ Specs.D05.M15.Exterior.homogeneousPart_value K W p

def power_restriction : Prop :=
  ∀ {K : Type u} {V : Type v} {W : Type w} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W],
  ∀ (T : V →ₗ[K] W) (p : ℕ) (a : ⋀[K]^p V),
    (powerMap_value p T a : _root_.ExteriorAlgebra K W) = exteriorMap_value T a

def power_map_elementary : Prop :=
  ∀ {K : Type u} {V : Type v} {W : Type w} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W],
  ∀ (T : V →ₗ[K] W) (p : ℕ) (a : Fin p → V),
    powerMap_value p T (exteriorPower.ιMulti K p a) = exteriorPower.ιMulti K p (T ∘ a)

def power_map_comp : Prop :=
  ∀ {K : Type u} {V : Type v} {W : Type w} {X : Type x} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] [AddCommGroup X] [Module K X],
  ∀ (T : V →ₗ[K] W) (S : W →ₗ[K] X) (p : ℕ),
    powerMap_value p (S.comp T) = (powerMap_value p S).comp (powerMap_value p T)

def power_map_id : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ p : ℕ, powerMap_value p (LinearMap.id : V →ₗ[K] V) = LinearMap.id

def exterior_map_comp : Prop :=
  ∀ {K : Type u} {V : Type v} {W : Type w} {X : Type x} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] [AddCommGroup X] [Module K X],
  ∀ (T : V →ₗ[K] W) (S : W →ₗ[K] X),
    exteriorMap_value (S.comp T) = (exteriorMap_value S).comp (exteriorMap_value T)

def exterior_map_id : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  exteriorMap_value (LinearMap.id : V →ₗ[K] V) = AlgHom.id K (_root_.ExteriorAlgebra K V)

def power_map_zero : Prop :=
  ∀ {K : Type u} {V : Type v} {W : Type w} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W],
  ∀ (T : V →ₗ[K] W) (a : ⋀[K]^0 V),
    exteriorPower.zeroEquiv K W (powerMap_value 0 T a) = exteriorPower.zeroEquiv K V a

def exterior_map_scalar : Prop :=
  ∀ {K : Type u} {V : Type v} {W : Type w} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W],
  ∀ (T : V →ₗ[K] W) (c : K),
    exteriorMap_value T (algebraMap K (_root_.ExteriorAlgebra K V) c) =
      algebraMap K (_root_.ExteriorAlgebra K W) c

end Specs.D05.M15.WedgeSign
