import MathGenome.Internal.Specs.D05.M15.TensorDualHom
import MathGenome.Internal.Specs.D05.M04.Trace
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
K05.15.contraction, paper.tex:3052–3068. All tensor powers below are the
canonical finite tensor products from TensorUniversal. `p` and `q` in the
contraction map count the factors *remaining*: its source has bidegree
(p+1,q+1), and its target has bidegree (p,q). `Fin.removeNth` retains the
order of the uncontracted slots. No dimension or characteristic restriction
is used in constructing the map. Finite dimension is used only for the
coordinate and trace identifications. The nullary powers are explicitly
identified with K by the equivalence taking the empty tensor to 1.
-/
namespace Specs.D05.M15.Contraction

open scoped TensorProduct BigOperators Classical

abbrev Power (K M : Type*) [Field K] [AddCommGroup M] [Module K M] (n : ℕ) :=
  PiTensorProduct K (fun _ : Fin n => M)

abbrev Mixed (K V : Type*) [Field K] [AddCommGroup V] [Module K V] (p q : ℕ) :=
  Power K (Module.Dual K V) p ⊗[K] Power K V q

def elementary {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {p q : ℕ} (f : Fin p → Module.Dual K V) (v : Fin q → V) : Mixed K V p q :=
  PiTensorProduct.tprod K f ⊗ₜ[K] PiTensorProduct.tprod K v

/-- Separating one slot by the finite multilinear universal property. -/
def splitSlot {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    {n : ℕ} (r : Fin (n+1)) : Power K M (n+1) →ₗ[K] M ⊗[K] Power K M n :=
  PiTensorProduct.lift (LinearMap.uncurryMid r
    { toFun := fun a => (TensorProduct.mk K M (Power K M n) a).compMultilinearMap
        (PiTensorProduct.tprod K)
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp })

/-- A basis-free map: separate, interchange the middle factors, evaluate,
then apply the scalar unit map. -/
def contract {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {p q : ℕ} (r : Fin (p+1)) (s : Fin (q+1)) :
    Mixed K V (p+1) (q+1) →ₗ[K] Mixed K V p q :=
  (TensorProduct.lid K (Mixed K V p q)).toLinearMap ∘ₗ
    TensorProduct.map (contractLeft K V) LinearMap.id ∘ₗ
    (TensorProduct.tensorTensorTensorComm K (Module.Dual K V)
      (Power K (Module.Dual K V) p) V (Power K V q)).toLinearMap ∘ₗ
    TensorProduct.map (splitSlot r) (splitSlot s)

def contract_type :=
  {K V : Type*} → [Field K] → [AddCommGroup V] → [Module K V] →
    {p q : ℕ} → Fin (p+1) → Fin (q+1) →
      Mixed K V (p+1) (q+1) →ₗ[K] Mixed K V p q

def contract_value : contract_type := @contract

/-- The scalar interpretation of the two nullary tensor powers. -/
def zeroEquiv {K V : Type*} [Field K] [AddCommGroup V] [Module K V] :
    Mixed K V 0 0 ≃ₗ[K] K :=
  TensorProduct.congr (PiTensorProduct.isEmptyEquiv (Fin 0))
    (PiTensorProduct.isEmptyEquiv (Fin 0)) ≪≫ₗ TensorProduct.lid K K

/-- The usual binary tensor product is precisely the bidegree (1,1) model. -/
def oneEquiv {K V : Type*} [Field K] [AddCommGroup V] [Module K V] :
    Mixed K V 1 1 ≃ₗ[K] (Module.Dual K V ⊗[K] V) :=
  TensorProduct.congr (PiTensorProduct.subsingletonEquiv (0 : Fin 1))
    (PiTensorProduct.subsingletonEquiv (0 : Fin 1))

def contraction_tprod : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {p q : ℕ} (r : Fin (p+1)) (s : Fin (q+1))
    (f : Fin (p+1) → Module.Dual K V) (v : Fin (q+1) → V),
    contract r s (elementary f v) =
      f r (v s) • elementary (r.removeNth f) (s.removeNth v)

/-- Existence and uniqueness among all linear maps, with only the stated
value on elementary tensors prescribed. -/
def contraction_universal : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {p q : ℕ} (r : Fin (p+1)) (s : Fin (q+1)),
    ∃! L : Mixed K V (p+1) (q+1) →ₗ[K] Mixed K V p q,
      ∀ f v, L (elementary f v) =
        f r (v s) • elementary (r.removeNth f) (s.removeNth v)

def nullary_unit : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (f : Fin 0 → Module.Dual K V) (v : Fin 0 → V),
    (zeroEquiv (K := K) (V := V)) (elementary f v) = 1

/-- The dual/primal product basis, including either empty list of slots
and including a zero-dimensional underlying vector space. -/
noncomputable def mixedBasis {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype I] (b : Module.Basis I K V) (p q : ℕ) :
    Module.Basis ((Fin p → I) × (Fin q → I)) K (Mixed K V p q) :=
  (Basis.piTensorProduct (fun _ : Fin p => b.dualBasis)).tensorProduct
    (Basis.piTensorProduct (fun _ : Fin q => b))

def basis_contraction : Prop :=
  ∀ {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype I] (b : Module.Basis I K V) {p q : ℕ}
    (r : Fin (p+1)) (s : Fin (q+1))
    (i : Fin (p+1) → I) (j : Fin (q+1) → I),
    contract r s (mixedBasis b (p+1) (q+1) (i,j)) =
      (if i r = j s then (1 : K) else 0) •
        mixedBasis b p q (r.removeNth i, s.removeNth j)

/-- Actual coordinates of an arbitrary tensor: insert the *same* index in
the two contracted slots and sum. This is derived from evaluation, rather
than used to define contraction. -/
def coordinate_contraction : Prop :=
  ∀ {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype I] (b : Module.Basis I K V) {p q : ℕ}
    (r : Fin (p+1)) (s : Fin (q+1)) (t : Mixed K V (p+1) (q+1))
    (i : Fin p → I) (j : Fin q → I),
    (mixedBasis b p q).repr (contract r s t) (i,j) =
      ∑ k : I, (mixedBasis b (p+1) (q+1)).repr t
        (r.insertNth k i, s.insertNth k j)

def rank_one_trace : Prop :=
  ∀ {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype I] (b : Module.Basis I K V) (f : Module.Dual K V) (v : V),
    LinearMap.trace K V (TensorDualHom.phi K V V (f ⊗ₜ[K] v)) =
      ∑ i, f (b i) * b.coord i v
    ∧ (∑ i, f (b i) * b.coord i v) = f v

/-- The normalized degree-(1,1) contraction equals trace under the upstream
canonical tensor–Hom identification. Zero-dimensional spaces are included. -/
def contraction_trace : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (t : Mixed K V 1 1),
    zeroEquiv (contract (0 : Fin 1) (0 : Fin 1) t) =
      LinearMap.trace K V (TensorDualHom.phi K V V (oneEquiv t))

/-- The change of variables on covectors is composition with g⁻¹. -/
def mixedAction {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (g : V ≃ₗ[K] V) (p q : ℕ) : Mixed K V p q →ₗ[K] Mixed K V p q :=
  TensorProduct.map
    (PiTensorProduct.map (fun _ : Fin p => g.symm.toLinearMap.dualMap))
    (PiTensorProduct.map (fun _ : Fin q => g.toLinearMap))

def action_tprod : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (g : V ≃ₗ[K] V) {p q : ℕ} (f : Fin p → Module.Dual K V) (v : Fin q → V),
    mixedAction g p q (elementary f v) =
      elementary (fun i => (f i).comp g.symm.toLinearMap) (fun j => g (v j))

def action_identity : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (p q : ℕ),
    mixedAction (LinearEquiv.refl K V) p q = LinearMap.id

def action_composition : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (g h : V ≃ₗ[K] V) (p q : ℕ),
    mixedAction (h.trans g) p q = (mixedAction g p q).comp (mixedAction h p q)

/-- In particular every action map is an automorphism, with the expected inverse. -/
def action_inverse : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (g : V ≃ₗ[K] V) (p q : ℕ),
    (mixedAction g.symm p q).comp (mixedAction g p q) = LinearMap.id ∧
      (mixedAction g p q).comp (mixedAction g.symm p q) = LinearMap.id

def contraction_equivariant : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (g : V ≃ₗ[K] V) {p q : ℕ} (r : Fin (p+1)) (s : Fin (q+1)),
    (contract r s).comp (mixedAction g (p+1) (q+1)) =
      (mixedAction g p q).comp (contract r s)

end Specs.D05.M15.Contraction
