import MathGenome.Internal.Specs.D05.M06.DirectSum
import MathGenome.Internal.Specs.D05.M03.Isomorphism

/-!
Independent statements for K05.06.external_sum, paper.tex:968–971.
The external space is the canonical dependent finitely supported direct sum.
It retains arbitrary index types and arbitrary component dimensions. Its tuple
interpretation is characterized in both directions, so finite support is the
only restriction on the product. Finite products compare by an actual linear
map, and the internal comparison uses the upstream unique-expression predicate.
-/

namespace Specs.D05.M06.ExternalSum

universe u v w

/-- Canonical finite-product comparison, without a chosen enumeration in the API. -/
noncomputable def finiteProductMap (K : Type*) (ι : Type*) (M : ι → Type*)
    [Field K] [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)] [Finite ι] :
    _root_.DirectSum ι M ≃ₗ[K] (∀ i, M i) := by
  classical
  letI := Fintype.ofFinite ι
  exact _root_.DirectSum.linearEquivFunOnFintype K ι M

/-- Add the included subspace components. The finite-support construction even
makes this map meaningful for an arbitrary index type. -/
noncomputable def summationMap {K V ι : Type*} [Field K] [AddCommGroup V]
    [Module K V] (U : ι → Submodule K V) :
    _root_.DirectSum ι (fun i => U i) →ₗ[K] V := by
  classical
  exact _root_.DirectSum.coeLinearMap U

def externalSum_type : Type (max (u+1) (v+1)) :=
  (ι : Type u) → (M : ι → Type v) → [∀ i, AddCommGroup (M i)] → Type (max u v)

def externalSum_value : externalSum_type.{u,v} :=
  fun ι M _ => _root_.DirectSum ι M

def finiteProductEquiv_type : Type (max (u+1) (v+1) (w+1)) :=
  (K : Type u) → (ι : Type v) → (M : ι → Type w) → [Field K] →
    [∀ i, AddCommGroup (M i)] → [∀ i, Module K (M i)] → [Finite ι] →
    (_root_.DirectSum ι M ≃ₗ[K] (∀ i, M i))

noncomputable def finiteProductEquiv_value : finiteProductEquiv_type.{u,v,w} :=
  fun K ι M _ _ _ _ => finiteProductMap K ι M

def summation_type : Type (max (u+1) (v+1) (w+1)) :=
  (K : Type u) → (V : Type v) → (ι : Type w) → [Field K] →
    [AddCommGroup V] → [Module K V] → (U : ι → Submodule K V) →
    (_root_.DirectSum ι (fun i => U i) →ₗ[K] V)

noncomputable def summation_value : summation_type.{u,v,w} :=
  fun _ _ _ _ _ _ U => summationMap U

/-- The canonical operations give a vector space over the same field. -/
def vector_space : Prop :=
  ∀ {K ι : Type*} {M : ι → Type*} [Field K] [∀ i, AddCommGroup (M i)]
    [∀ i, Module K (M i)], Nonempty (Module K (_root_.DirectSum ι M))

def componentwise_operations : Prop :=
  ∀ {K ι : Type*} {M : ι → Type*} [Field K] [∀ i, AddCommGroup (M i)]
    [∀ i, Module K (M i)] (a : K) (x y : _root_.DirectSum ι M) (i : ι),
    (0 : _root_.DirectSum ι M) i = 0 ∧ (x + y) i = x i + y i ∧
      (a • x) i = a • x i ∧ (-x) i = -(x i)

def finite_support : Prop :=
  ∀ {ι : Type*} {M : ι → Type*} [∀ i, AddCommGroup (M i)]
    (x : _root_.DirectSum ι M), Set.Finite {i | x i ≠ 0}

/-- Conversely every finitely supported tuple occurs, with unique components. -/
def tuple_iff_finite_support : Prop :=
  ∀ {ι : Type*} {M : ι → Type*} [∀ i, AddCommGroup (M i)] (f : ∀ i, M i),
    (∃ x : _root_.DirectSum ι M, ∀ i, x i = f i) ↔ Set.Finite {i | f i ≠ 0}

def extensionality : Prop :=
  ∀ {ι : Type*} {M : ι → Type*} [∀ i, AddCommGroup (M i)]
    (x y : _root_.DirectSum ι M), (∀ i, x i = y i) ↔ x = y

def support_add_subset : Prop :=
  ∀ {ι : Type*} {M : ι → Type*} [∀ i, AddCommGroup (M i)]
    (x y : _root_.DirectSum ι M),
    {i | (x + y) i ≠ 0} ⊆ {i | x i ≠ 0} ∪ {i | y i ≠ 0}

def support_smul_subset : Prop :=
  ∀ {K ι : Type*} {M : ι → Type*} [Field K] [∀ i, AddCommGroup (M i)]
    [∀ i, Module K (M i)] (a : K) (x : _root_.DirectSum ι M),
    {i | (a • x) i ≠ 0} ⊆ {i | x i ≠ 0}

/-- The finite comparison is exactly the inclusion into tuples. -/
def finiteProductEquiv_apply : Prop :=
  ∀ {K ι : Type*} {M : ι → Type*} [Field K] [∀ i, AddCommGroup (M i)]
    [∀ i, Module K (M i)] [Finite ι] (x : _root_.DirectSum ι M) (i : ι),
    finiteProductMap K ι M x i = x i

def finiteProductEquiv_symm_apply : Prop :=
  ∀ {K ι : Type*} {M : ι → Type*} [Field K] [∀ i, AddCommGroup (M i)]
    [∀ i, Module K (M i)] [Finite ι] (f : ∀ i, M i) (i : ι),
    ((finiteProductMap K ι M).symm f) i = f i

/-- On a finite family, external summation is the finite sum of components. -/
def summation_apply : Prop :=
  ∀ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype ι]
    (U : ι → Submodule K V) (x : _root_.DirectSum ι (fun i => U i)),
    summationMap U x = ∑ i, (x i : V)

/-- The range is the subspace sum; this stronger form allows arbitrary indices. -/
def range_summation : Prop :=
  ∀ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U : ι → Submodule K V), LinearMap.range (summationMap U) = ⨆ i, U i

def surjective_iff_spanning : Prop :=
  ∀ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U : ι → Submodule K V),
    Function.Surjective (summationMap U) ↔ (⨆ i, U i) = ⊤

def mem_kernel_iff_zero_sum : Prop :=
  ∀ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype ι]
    (U : ι → Submodule K V) (x : _root_.DirectSum ι (fun i => U i)),
    x ∈ LinearMap.ker (summationMap U) ↔ (∑ i, (x i : V)) = 0

def bijective_iff_internal : Prop :=
  ∀ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype ι]
    (U : ι → Submodule K V),
    Function.Bijective (summationMap U) ↔ Specs.D05.M06.DirectSum.UniqueDecomposition U

/-- An isomorphism with precisely the external summation map as its forward map
exists exactly for an internal direct sum. This does not identify the sets. -/
def isomorphism_iff_internal : Prop :=
  ∀ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype ι]
    (U : ι → Submodule K V),
    (∃ e : _root_.DirectSum ι (fun i => U i) ≃ₗ[K] V,
      e.toLinearMap = summationMap U) ↔ Specs.D05.M06.DirectSum.UniqueDecomposition U

end Specs.D05.M06.ExternalSum
