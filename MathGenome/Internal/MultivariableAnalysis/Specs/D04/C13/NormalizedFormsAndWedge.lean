import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C02.DerivativeInterfaces
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Alternating.DomCoprod

/-! Independent objects for d04:13:forms and d04:13:wedge.
Covectors are alternating maps on vectors, not exterior powers of vectors.
`none` denotes infinite regularity and `some r` finite regularity. Fields are
represented by ambient functions, with conditions imposed only on the open domain. -/
noncomputable section
open scoped BigOperators TensorProduct
open Module
namespace Specs.D04.C13.NormalizedFormsAndWedge
namespace Model
universe u
abbrev Covector (V : Type u) [AddCommGroup V] [Module ℝ V] (k : ℕ) :=
  V [⋀^Fin k]→ₗ[ℝ] ℝ
abbrev MultiIndex (n k : ℕ) := Set.powersetCard (Fin n) k

def indexTuple {n k : ℕ} (I : MultiIndex n k) : Fin k ↪o Fin n :=
  Set.powersetCard.ofFinEmbEquiv.symm I

def scalarCovector {V : Type u} [AddCommGroup V] [Module ℝ V] :
    ℝ ≃ₗ[ℝ] Covector V 0 := AlternatingMap.constLinearEquivOfIsEmpty

def covectorBasis {V : Type u} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (b : Basis (Fin n) ℝ V) (k : ℕ) : Basis (MultiIndex n k) ℝ (Covector V k) :=
  (b.exteriorPower k).dualBasis.map (exteriorPower.alternatingMapLinearEquiv (R := ℝ) (n := k)).symm

def dx {V : Type u} [AddCommGroup V] [Module ℝ V] {n k : ℕ}
    (b : Basis (Fin n) ℝ V) (I : MultiIndex n k) : Covector V k := covectorBasis b k I

def coefficient {V : Type u} [AddCommGroup V] [Module ℝ V] {n k : ℕ}
    (b : Basis (Fin n) ℝ V) (ω : Covector V k) (I : MultiIndex n k) : ℝ :=
  ω (fun j => b (indexTuple I j))

/-- The ordinary tensor product, evaluated by multiplication in ℝ. -/
def covectorTensor {V : Type u} [AddCommGroup V] [Module ℝ V] {p q : ℕ}
    (α : Covector V p) (β : Covector V q) :
    MultilinearMap ℝ (fun _ : Fin (p + q) => V) ℝ :=
  (LinearMap.mul' ℝ ℝ).compMultilinearMap
    ((MultilinearMap.domCoprod α.toMultilinearMap β.toMultilinearMap).domDomCongr
      finSumFinEquiv)

/-- Averaged alternation (the library alternatization is an unnormalized sum). -/
def averageAlternation {V : Type u} [AddCommGroup V] [Module ℝ V] {k : ℕ}
    (T : MultilinearMap ℝ (fun _ : Fin k => V) ℝ) : Covector V k :=
  (k.factorial : ℝ)⁻¹ • MultilinearMap.alternatization T

/-- Normalization 1/(p!q!), including either empty block. -/
def wedge {V : Type u} [AddCommGroup V] [Module ℝ V] {p q : ℕ}
    (α : Covector V p) (β : Covector V q) : Covector V (p + q) :=
  ((p.factorial : ℝ) * (q.factorial : ℝ))⁻¹ •
    MultilinearMap.alternatization (covectorTensor α β)

def linearCovector {V : Type u} [AddCommGroup V] [Module ℝ V]
    (f : Module.Dual ℝ V) : Covector V 1 :=
  AlternatingMap.ofSubsingleton ℝ V ℝ (0 : Fin 1) f

/-- Left-associated wedge of one-covectors; its empty value is the scalar 1. -/
def wedgeList {V : Type u} [AddCommGroup V] [Module ℝ V] :
    (k : ℕ) → (Fin k → Module.Dual ℝ V) → Covector V k
  | 0, _ => scalarCovector 1
  | k + 1, f => wedge (wedgeList k (Fin.init f)) (linearCovector (f (Fin.last k)))

/-- Increasing shuffle representatives, with zero-based Fin indices. -/
def IsShuffle (p q : ℕ) (σ : Equiv.Perm (Fin (p + q))) : Prop :=
  StrictMono (fun i : Fin p => σ (Fin.castAdd q i)) ∧
    StrictMono (fun j : Fin q => σ (Fin.natAdd p j))

def shuffleProduct {V : Type u} [AddCommGroup V] [Module ℝ V] {p q : ℕ}
    (α : Covector V p) (β : Covector V q) (v : Fin (p + q) → V) : ℝ := by
  classical
  exact ∑ σ : {σ : Equiv.Perm (Fin (p + q)) // IsShuffle p q σ},
    Equiv.Perm.sign σ.val •
      (α (fun i => v (σ.val (Fin.castAdd q i))) *
        β (fun j => v (σ.val (Fin.natAdd p j))))

/-- Equality of forms of different but equal natural-number degrees. -/
def castCovector {V : Type u} [AddCommGroup V] [Module ℝ V] {p q : ℕ}
    (h : p = q) (ω : Covector V p) : Covector V q := h ▸ ω

open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
abbrev FormField (n k : ℕ) := E n → Covector (E n) k

def IsCrForm (r : Option ℕ) {n k : ℕ} (U : Set (E n)) (ω : FormField n k) : Prop :=
  IsOpen U ∧ ∀ I : MultiIndex n k,
    match r with
    | some s => CrOn s U (fun x => coefficient (standardBasis n) (ω x) I)
    | none => SmoothOn U (fun x => coefficient (standardBasis n) (ω x) I)
end Model

/-! Expected types and values; no candidate implementation is imported. -/
open Model
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open scoped Classical
universe u

abbrev CovectorType := (V : Type u) → [AddCommGroup V] → [Module ℝ V] → ℕ → Type u
def CovectorValue : CovectorType := @Model.Covector

abbrev MultiIndexType := (n k : ℕ) → Set (Finset (Fin n))
def MultiIndexValue : MultiIndexType := @Model.MultiIndex

abbrev indexTupleType := {n k : ℕ} → MultiIndex n k → (Fin k ↪o Fin n)
def indexTupleValue : indexTupleType := @Model.indexTuple

abbrev scalarCovectorType := {V : Type u} → [AddCommGroup V] → [Module ℝ V] → (ℝ ≃ₗ[ℝ] Covector V 0)
def scalarCovectorValue : scalarCovectorType := @Model.scalarCovector

abbrev covectorBasisType := {V : Type u} → [AddCommGroup V] → [Module ℝ V] → {n : ℕ} → Basis (Fin n) ℝ V → (k : ℕ) → Basis (MultiIndex n k) ℝ (Covector V k)
def covectorBasisValue : covectorBasisType := @Model.covectorBasis

abbrev dxType := {V : Type u} → [AddCommGroup V] → [Module ℝ V] → {n k : ℕ} → Basis (Fin n) ℝ V → MultiIndex n k → Covector V k
def dxValue : dxType := @Model.dx

abbrev coefficientType := {V : Type u} → [AddCommGroup V] → [Module ℝ V] → {n k : ℕ} → Basis (Fin n) ℝ V → Covector V k → MultiIndex n k → ℝ
def coefficientValue : coefficientType := @Model.coefficient

abbrev covectorTensorType := {V : Type u} → [AddCommGroup V] → [Module ℝ V] → {p q : ℕ} → Covector V p → Covector V q → MultilinearMap ℝ (fun _ : Fin (p + q) => V) ℝ
def covectorTensorValue : covectorTensorType := @Model.covectorTensor

abbrev averageAlternationType := {V : Type u} → [AddCommGroup V] → [Module ℝ V] → {k : ℕ} → MultilinearMap ℝ (fun _ : Fin k => V) ℝ → Covector V k
def averageAlternationValue : averageAlternationType := @Model.averageAlternation

abbrev wedgeType := {V : Type u} → [AddCommGroup V] → [Module ℝ V] → {p q : ℕ} → Covector V p → Covector V q → Covector V (p + q)
def wedgeValue : wedgeType := @Model.wedge

abbrev linearCovectorType := {V : Type u} → [AddCommGroup V] → [Module ℝ V] → Module.Dual ℝ V → Covector V 1
def linearCovectorValue : linearCovectorType := @Model.linearCovector

abbrev wedgeListType := {V : Type u} → [AddCommGroup V] → [Module ℝ V] → (k : ℕ) → (Fin k → Module.Dual ℝ V) → Covector V k
def wedgeListValue : wedgeListType := @Model.wedgeList

abbrev IsShuffleType := (p q : ℕ) → Equiv.Perm (Fin (p + q)) → Prop
def IsShuffleValue : IsShuffleType := @Model.IsShuffle

abbrev shuffleProductType := {V : Type u} → [AddCommGroup V] → [Module ℝ V] → {p q : ℕ} → Covector V p → Covector V q → (Fin (p + q) → V) → ℝ
def shuffleProductValue : shuffleProductType := @Model.shuffleProduct

abbrev castCovectorType := {V : Type u} → [AddCommGroup V] → [Module ℝ V] → {p q : ℕ} → p = q → Covector V p → Covector V q
def castCovectorValue : castCovectorType := @Model.castCovector

abbrev FormFieldType := ℕ → ℕ → Type
def FormFieldValue : FormFieldType := @Model.FormField

abbrev IsCrFormType := Option ℕ → {n k : ℕ} → Set (E n) → FormField n k → Prop
def IsCrFormValue : IsCrFormType := @Model.IsCrForm

def scalarCovector_applyType : Prop :=
  ∀ {V : Type u} [AddCommGroup V] [Module ℝ V] (a : ℝ) (v : Fin 0 → V),
  scalarCovector (V := V) a v = a

def scalarCovector_symm_applyType : Prop :=
  ∀ {V : Type u} [AddCommGroup V] [Module ℝ V] (ω : Covector V 0),
  scalarCovector.symm ω = ω 0

def covector_swapType : Prop :=
  ∀ {V : Type u} [AddCommGroup V] [Module ℝ V] {k : ℕ} (ω : Covector V k) (v : Fin k → V)
    {i j : Fin k} (hij : i ≠ j),
  ω (v ∘ Equiv.swap i j) = -ω v

def dx_applyType : Prop :=
  ∀ {V : Type u} [AddCommGroup V] [Module ℝ V] {n : ℕ} {k : ℕ} (b : Basis (Fin n) ℝ V) (I : MultiIndex n k) (v : Fin k → V),
  dx b I v = Matrix.det (fun i j => b.repr (v j) (indexTuple I i))

def coefficient_eq_reprType : Prop :=
  ∀ {V : Type u} [AddCommGroup V] [Module ℝ V] {n : ℕ} {k : ℕ} (b : Basis (Fin n) ℝ V) (ω : Covector V k)
    (I : MultiIndex n k),
  coefficient b ω I = (covectorBasis b k).repr ω I

def covector_expansionType : Prop :=
  ∀ {V : Type u} [AddCommGroup V] [Module ℝ V] {n : ℕ} {k : ℕ} (b : Basis (Fin n) ℝ V) (ω : Covector V k),
  ω = ∑ I : MultiIndex n k, coefficient b ω I • dx b I

def covector_expansion_uniqueType : Prop :=
  ∀ {V : Type u} [AddCommGroup V] [Module ℝ V] {n : ℕ} {k : ℕ} (b : Basis (Fin n) ℝ V) (ω : Covector V k)
    (a : MultiIndex n k → ℝ),
  (ω = ∑ I, a I • dx b I) ↔ a = coefficient b ω

def coefficient_dxType : Prop :=
  ∀ {V : Type u} [AddCommGroup V] [Module ℝ V] {n : ℕ} {k : ℕ} (b : Basis (Fin n) ℝ V) (I J : MultiIndex n k),
  coefficient b (dx b I) J = if I = J then 1 else 0

def dx_degree_zeroType : Prop :=
  ∀ {V : Type u} [AddCommGroup V] [Module ℝ V] {n : ℕ} (b : Basis (Fin n) ℝ V) (I : MultiIndex n 0)
    (v : Fin 0 → V),
  dx b I v = 1

def covector_eq_zero_above_dimensionType : Prop :=
  ∀ {V : Type u} [AddCommGroup V] [Module ℝ V] {k : ℕ} [FiniteDimensional ℝ V]
    (hk : Module.finrank ℝ V < k) (ω : Covector V k),
  ω = 0

def covectorTensor_applyType : Prop :=
  ∀ {V : Type u} [AddCommGroup V] [Module ℝ V] {p : ℕ} {q : ℕ} (α : Covector V p) (β : Covector V q)
    (v : Fin (p + q) → V),
  covectorTensor α β v =
      α (fun i => v (Fin.castAdd q i)) * β (fun j => v (Fin.natAdd p j))

def wedge_applyType : Prop :=
  ∀ {V : Type u} [AddCommGroup V] [Module ℝ V] {p : ℕ} {q : ℕ} (α : Covector V p) (β : Covector V q) (v : Fin (p + q) → V),
  wedge α β v = ((p.factorial : ℝ) * (q.factorial : ℝ))⁻¹ *
      ∑ σ : Equiv.Perm (Fin (p + q)), Equiv.Perm.sign σ •
        (α (fun i => v (σ (Fin.castAdd q i))) *
          β (fun j => v (σ (Fin.natAdd p j))))

def wedge_add_leftType : Prop :=
  ∀ {V : Type u} [AddCommGroup V] [Module ℝ V] {p : ℕ} {q : ℕ} (α α' : Covector V p) (β : Covector V q),
  wedge (α + α') β = wedge α β + wedge α' β

def wedge_add_rightType : Prop :=
  ∀ {V : Type u} [AddCommGroup V] [Module ℝ V] {p : ℕ} {q : ℕ} (α : Covector V p) (β β' : Covector V q),
  wedge α (β + β') = wedge α β + wedge α β'

def wedge_smul_leftType : Prop :=
  ∀ {V : Type u} [AddCommGroup V] [Module ℝ V] {p : ℕ} {q : ℕ} (c : ℝ) (α : Covector V p) (β : Covector V q),
  wedge (c • α) β = c • wedge α β

def wedge_smul_rightType : Prop :=
  ∀ {V : Type u} [AddCommGroup V] [Module ℝ V] {p : ℕ} {q : ℕ} (c : ℝ) (α : Covector V p) (β : Covector V q),
  wedge α (c • β) = c • wedge α β

def wedge_eq_averageType : Prop :=
  ∀ {V : Type u} [AddCommGroup V] [Module ℝ V] {p : ℕ} {q : ℕ} (α : Covector V p) (β : Covector V q),
  wedge α β =
      (((p + q).factorial : ℝ) / ((p.factorial : ℝ) * (q.factorial : ℝ))) •
        averageAlternation (covectorTensor α β)

def averageAlternation_covectorType : Prop :=
  ∀ {V : Type u} [AddCommGroup V] [Module ℝ V] {k : ℕ} (ω : Covector V k),
  averageAlternation ω.toMultilinearMap = ω

def wedge_scalar_rightType : Prop :=
  ∀ {V : Type u} [AddCommGroup V] [Module ℝ V] {p : ℕ} (c : ℝ) (α : Covector V p),
  wedge α (scalarCovector c) = c • α

def castCovector_eq_domDomCongrType : Prop :=
  ∀ {V : Type u} [AddCommGroup V] [Module ℝ V] {r s : ℕ} (h : r = s) (ω : Covector V r),
  castCovector h ω = ω.domDomCongr (finCongr h)

def wedge_assocType : Prop :=
  ∀ {V : Type u} [AddCommGroup V] [Module ℝ V] {p : ℕ} {q : ℕ} [FiniteDimensional ℝ V] {r : ℕ}
    (α : Covector V p) (β : Covector V q) (γ : Covector V r),
  castCovector (Nat.add_assoc p q r) (wedge (wedge α β) γ) = wedge α (wedge β γ)

def wedge_commType : Prop :=
  ∀ {V : Type u} [AddCommGroup V] [Module ℝ V] {p : ℕ} {q : ℕ} [FiniteDimensional ℝ V] (α : Covector V p) (β : Covector V q),
  wedge α β = (-1 : ℝ) ^ (p * q) • castCovector (Nat.add_comm q p) (wedge β α)

def wedge_shuffle_sumType : Prop :=
  ∀ {V : Type u} [AddCommGroup V] [Module ℝ V] {p : ℕ} {q : ℕ} (α : Covector V p) (β : Covector V q)
    (v : Fin (p + q) → V),
  wedge α β v = ∑ σ : {σ : Equiv.Perm (Fin (p + q)) // IsShuffle p q σ},
      Equiv.Perm.sign σ.val •
        (α (fun i => v (σ.val (Fin.castAdd q i))) *
          β (fun j => v (σ.val (Fin.natAdd p j))))

def wedge_shuffleProductType : Prop :=
  ∀ {V : Type u} [AddCommGroup V] [Module ℝ V] {p : ℕ} {q : ℕ} (α : Covector V p) (β : Covector V q)
    (v : Fin (p + q) → V),
  wedge α β v = shuffleProduct α β v

def castCovector_transType : Prop :=
  ∀ {V : Type u} [AddCommGroup V] [Module ℝ V] {a b c : ℕ} (h : a = b) (h' : b = c) (ω : Covector V a),
  castCovector h' (castCovector h ω) = castCovector (h.trans h') ω

def wedge_scalar_leftType : Prop :=
  ∀ {V : Type u} [AddCommGroup V] [Module ℝ V] {q : ℕ} [FiniteDimensional ℝ V] (c : ℝ) (β : Covector V q),
  castCovector (Nat.zero_add q) (wedge (scalarCovector c) β) = c • β

def covector_exterior_dual_equivType : Prop :=
  ∀ {V : Type u} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] (k : ℕ),
  ∃ e : (⋀[ℝ]^k (Module.Dual ℝ V)) ≃ₗ[ℝ] Covector V k,
      ∀ a v, e a v = exteriorPower.pairingDual ℝ V k a (exteriorPower.ιMulti ℝ k v)

def linearCovector_applyType : Prop :=
  ∀ {V : Type u} [AddCommGroup V] [Module ℝ V] (f : Module.Dual ℝ V) (v : Fin 1 → V),
  linearCovector f v = f (v 0)

def wedgeList_applyType : Prop :=
  ∀ {V : Type u} [AddCommGroup V] [Module ℝ V] (k : ℕ) (f : Fin k → Module.Dual ℝ V) (v : Fin k → V),
  wedgeList k f v = Matrix.det (fun i j => f i (v j))

def coordinate_wedgeType : Prop :=
  ∀ {V : Type u} [AddCommGroup V] [Module ℝ V] {n : ℕ} {k : ℕ} (b : Basis (Fin n) ℝ V) (I : MultiIndex n k),
  wedgeList k (fun i => b.coord (indexTuple I i)) = dx b I

def isCrForm_finite_iffType : Prop :=
  ∀ {n k : ℕ} (r : ℕ) (U : Set (E n)) (ω : FormField n k),
  IsCrForm (some r) U ω ↔ IsOpen U ∧
      ∀ I : MultiIndex n k, CrOn r U (fun x => coefficient (standardBasis n) (ω x) I)

def isCrForm_smooth_iffType : Prop :=
  ∀ {n k : ℕ} (U : Set (E n)) (ω : FormField n k),
  IsCrForm none U ω ↔ IsOpen U ∧
      ∀ I : MultiIndex n k, SmoothOn U (fun x => coefficient (standardBasis n) (ω x) I)

def isCrForm_finite_contDiffOnType : Prop :=
  ∀ {n k : ℕ} (r : ℕ) (U : Set (E n))
    (ω : FormField n k) (hU : IsOpen U),
  IsCrForm (some r) U ω ↔
      ∀ I : MultiIndex n k, ContDiffOn ℝ (r : WithTop ℕ∞)
        (fun x => coefficient (standardBasis n) (ω x) I) U

def isCrForm_zero_iffType : Prop :=
  ∀ {n : ℕ} (r : Option ℕ) (U : Set (E n)) (f : E n → ℝ),
  IsCrForm r U (fun x => scalarCovector (V := E n) (f x)) ↔
      IsOpen U ∧ match r with
        | some s => CrOn s U f
        | none => SmoothOn U f

end Specs.D04.C13.NormalizedFormsAndWedge
