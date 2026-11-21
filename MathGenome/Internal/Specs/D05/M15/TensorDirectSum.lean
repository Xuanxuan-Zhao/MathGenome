import MathGenome.Internal.Specs.D05.M06.ExternalSum
import MathGenome.Internal.Specs.D05.M06.Complement
import MathGenome.Internal.Specs.D05.M02.BasisExtension.Choice
import MathGenome.Internal.Specs.D05.M15.TensorMaps

/-!
Independent statements for K05.15.tensor_direct_sum, paper.tex:2771–2772.
All spaces are algebraic over an arbitrary field, with no dimension assumption
on any tensor factor. Finite index types include the empty type. Direct sums
are the same dependent finitely supported sums used by the upstream interface.
Internal decompositions use its unique-expression predicate; the projection
isomorphism is a conclusion, not an additional hypothesis.

The unrestricted retraction assertion uses the declared classical basis-choice
principle. The finite-dimensional assertion is stated separately, and can be
proved from the finite complement theorem. No characteristic restriction occurs.
-/

namespace Specs.D05.M15.TensorDirectSum

open scoped TensorProduct

/-- Distribution in the first variable, including the actual inverse sum. -/
def external_left : Prop := by
  classical
  exact
  ∀ {K W ι : Type*} [Field K] [AddCommGroup W] [Module K W] [Fintype ι]
    (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)],
    ∃ e : ((_root_.DirectSum ι M) ⊗[K] W) ≃ₗ[K]
        _root_.DirectSum ι (fun i => M i ⊗[K] W),
      (∀ (v : _root_.DirectSum ι M) (w : W) (i : ι),
        e (v ⊗ₜ[K] w) i = v i ⊗ₜ[K] w) ∧
      ∀ t, e.symm t = ∑ i, TensorProduct.map (_root_.DirectSum.lof K ι M i)
        (LinearMap.id : W →ₗ[K] W) (t i)

/-- Distribution in the second variable, with the same component convention. -/
def external_right : Prop := by
  classical
  exact
  ∀ {K W ι : Type*} [Field K] [AddCommGroup W] [Module K W] [Fintype ι]
    (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)],
    ∃ e : (W ⊗[K] (_root_.DirectSum ι M)) ≃ₗ[K]
        _root_.DirectSum ι (fun i => W ⊗[K] M i),
      (∀ (w : W) (v : _root_.DirectSum ι M) (i : ι),
        e (w ⊗ₜ[K] v) i = w ⊗ₜ[K] v i) ∧
      ∀ t, e.symm t = ∑ i, TensorProduct.map (LinearMap.id : W →ₗ[K] W)
        (_root_.DirectSum.lof K ι M i) (t i)

/-- Internal decomposition: the components of `d v` are the actual projections
onto the stated subspaces; the inverse adds their tensor inclusions. -/
def internal_left : Prop :=
  ∀ {K V W ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [Fintype ι] (U : ι → Submodule K V),
    Specs.D05.M06.DirectSum.UniqueDecomposition U →
    ∃ d : V ≃ₗ[K] (∀ i, U i),
      (∀ c, d.symm c = ∑ i, (c i : V)) ∧
      ∃ e : (V ⊗[K] W) ≃ₗ[K] _root_.DirectSum ι (fun i => U i ⊗[K] W),
        (∀ v w i, e (v ⊗ₜ[K] w) i = d v i ⊗ₜ[K] w) ∧
        ∀ t, e.symm t = ∑ i, TensorProduct.map (U i).subtype
          (LinearMap.id : W →ₗ[K] W) (t i)

/-- The internal decomposition also distributes in the other variable. -/
def internal_right : Prop :=
  ∀ {K V W ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [Fintype ι] (U : ι → Submodule K V),
    Specs.D05.M06.DirectSum.UniqueDecomposition U →
    ∃ d : V ≃ₗ[K] (∀ i, U i),
      (∀ c, d.symm c = ∑ i, (c i : V)) ∧
      ∃ e : (W ⊗[K] V) ≃ₗ[K] _root_.DirectSum ι (fun i => W ⊗[K] U i),
        (∀ w v i, e (w ⊗ₜ[K] v) i = w ⊗ₜ[K] d v i) ∧
        ∀ t, e.symm t = ∑ i, TensorProduct.map (LinearMap.id : W →ₗ[K] W)
          (U i).subtype (t i)

/-- Tensoring a left inverse gives a left inverse, on either side. -/
def tensor_left_inverse : Prop :=
  ∀ {K U V W : Type*} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (f : U →ₗ[K] V) (r : V →ₗ[K] U), r.comp f = LinearMap.id →
      (TensorProduct.map r (LinearMap.id : W →ₗ[K] W)).comp
        (TensorProduct.map f (LinearMap.id : W →ₗ[K] W)) = LinearMap.id ∧
      (TensorProduct.map (LinearMap.id : W →ₗ[K] W) r).comp
        (TensorProduct.map (LinearMap.id : W →ₗ[K] W) f) = LinearMap.id

/-- The subspace inclusion has a linear retraction (unrestricted basis choice). -/
def subspace_retraction : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (U : Submodule K V),
    ∃ r : V →ₗ[K] U, r.comp U.subtype = LinearMap.id

/-- Both natural tensor inclusions are split injections, without dimension bounds. -/
def subspace_tensor_inclusions : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (U : Submodule K V),
    (∃ r : (V ⊗[K] W) →ₗ[K] (U ⊗[K] W), r.comp
      (TensorProduct.map U.subtype (LinearMap.id : W →ₗ[K] W)) = LinearMap.id) ∧
    (∃ r : (W ⊗[K] V) →ₗ[K] (W ⊗[K] U), r.comp
      (TensorProduct.map (LinearMap.id : W →ₗ[K] W) U.subtype) = LinearMap.id) ∧
    Function.Injective (TensorProduct.map U.subtype (LinearMap.id : W →ₗ[K] W)) ∧
    Function.Injective (TensorProduct.map (LinearMap.id : W →ₗ[K] W) U.subtype)

/-- Finite-dimensional ambient space needs only the finite complement result;
`W` remains unrestricted, including zero. -/
def finite_subspace_tensor_inclusions : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] (U : Submodule K V),
    (∃ r : (V ⊗[K] W) →ₗ[K] (U ⊗[K] W), r.comp
      (TensorProduct.map U.subtype (LinearMap.id : W →ₗ[K] W)) = LinearMap.id) ∧
    (∃ r : (W ⊗[K] V) →ₗ[K] (W ⊗[K] U), r.comp
      (TensorProduct.map (LinearMap.id : W →ₗ[K] W) U.subtype) = LinearMap.id) ∧
    Function.Injective (TensorProduct.map U.subtype (LinearMap.id : W →ₗ[K] W)) ∧
    Function.Injective (TensorProduct.map (LinearMap.id : W →ₗ[K] W) U.subtype)

end Specs.D05.M15.TensorDirectSum
