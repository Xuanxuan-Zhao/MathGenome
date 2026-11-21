import MathGenome.Internal.Specs.D05.M15.PolynomialPolarization.ShuffleProduct
import MathGenome.Internal.D05.M15.SymmetricBasis.PerfectPairing
import Mathlib.Algebra.Algebra.TransferInstance

noncomputable section
set_option maxHeartbeats 800000
open scoped Classical DirectSum
namespace D05.M15.PolynomialPolarization.ShuffleProduct
open Specs.D05.M15.Symmetric
open Specs.D05.M15.SymmetricBasis
open Specs.D05.M15.SymmetricBasis.PerfectPairing
open Specs.D05.M15.PolynomialPolarization.ShuffleProduct
open D05.M15.SymmetricBasis.PerfectPairing
universe u v
variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

/-- Pull a quotient functional back along the elementary symmetric tensor. -/
def dualToForm (p : ℕ) :
    Module.Dual K (symmetricPower K V p) →ₗ[K] symmetricForms K V p where
  toFun L := ⟨L.compMultilinearMap (elementary K V p), by
    intro x σ
    change L (elementary K V p (x ∘ σ)) = L (elementary K V p x)
    rw [D05.M15.Symmetric.elementary_symmetric]⟩
  map_add' _ _ := by rfl
  map_smul' _ _ := by rfl

theorem dualToForm_bijective (p : ℕ) :
    Function.Bijective (dualToForm (K := K) (V := V) p) := by
  constructor
  · intro L M h
    apply power_ext p
    intro x
    exact congrArg (fun B : symmetricForms K V p => B.val x) h
  · intro B
    obtain ⟨L, hL, _⟩ := (D05.M15.Symmetric.power_universal p B.val).mp B.property
    refine ⟨L, ?_⟩
    apply Subtype.ext
    exact MultilinearMap.ext hL

/-- The universal property identifies symmetric forms with the algebraic dual
of the actual symmetric quotient, in every characteristic and dimension. -/
def dualFormEquiv (p : ℕ) :
    Module.Dual K (symmetricPower K V p) ≃ₗ[K] symmetricForms K V p :=
  LinearEquiv.ofBijective (dualToForm p) (dualToForm_bijective p)

/-- Compose the perfect permanent pairing with the universal-property equivalence. -/
def permanentEquiv [CharZero K] [FiniteDimensional K V] (p : ℕ) :
    symmetricPower K (Module.Dual K V) p ≃ₗ[K] symmetricForms K V p :=
  (LinearEquiv.ofBijective (pairing p)
    (D05.M15.SymmetricBasis.PerfectPairing.characteristic_zero p (pairing p)
      (pairing_elementary p)).1).trans (dualFormEquiv p)

@[simp] theorem permanentEquiv_elementary [CharZero K] [FiniteDimensional K V]
    (p : ℕ) (φ : Fin p → Module.Dual K V) (x : Fin p → V) :
    (permanentEquiv p (elementary K (Module.Dual K V) p φ)).val x = permanent φ x :=
  pairing_elementary p φ x

theorem permanent_isomorphism :
    Specs.D05.M15.PolynomialPolarization.ShuffleProduct.permanent_isomorphism := by
  intro K V _ _ _ _ _ p
  exact ⟨permanentEquiv p, permanentEquiv_elementary p⟩

@[simp] theorem blockProduct_apply {p q : ℕ}
    (B : MultilinearMap K (fun _ : Fin p => V) K)
    (C : MultilinearMap K (fun _ : Fin q => V) K) (x : Fin p ⊕ Fin q → V) :
    blockProduct B C x = B (x ∘ Sum.inl) * C (x ∘ Sum.inr) := rfl

/-- Permuting the arguments within either selected block has no effect. -/
theorem blockProduct_internal {p q : ℕ} (B : symmetricForms K V p)
    (C : symmetricForms K V q) (σ : Equiv.Perm (Fin p ⊕ Fin q))
    (τ : Equiv.Perm (Fin p) × Equiv.Perm (Fin q)) :
    (blockProduct B.val C.val).domDomCongr
      (σ * Equiv.Perm.sumCongrHom _ _ τ) =
    (blockProduct B.val C.val).domDomCongr σ := by
  ext x
  change B.val ((x ∘ σ ∘ Sum.inl) ∘ τ.1) * C.val ((x ∘ σ ∘ Sum.inr) ∘ τ.2) =
    B.val (x ∘ σ ∘ Sum.inl) * C.val (x ∘ σ ∘ Sum.inr)
  rw [B.property, C.property]

theorem blockProduct_coset {p q : ℕ} (B : symmetricForms K V p)
    (C : symmetricForms K V q) (σ τ : Equiv.Perm (Fin p ⊕ Fin q))
    (h : QuotientGroup.leftRel (Equiv.Perm.sumCongrHom (Fin p) (Fin q)).range σ τ) :
    (blockProduct B.val C.val).domDomCongr σ =
      (blockProduct B.val C.val).domDomCongr τ := by
  obtain ⟨ρ, hρ⟩ := QuotientGroup.leftRel_apply.mp h
  have heq : τ = σ * Equiv.Perm.sumCongrHom _ _ ρ :=
    (inv_mul_eq_iff_eq_mul.mp hρ.symm)
  rw [heq, blockProduct_internal]

theorem representative_independent :
    Specs.D05.M15.PolynomialPolarization.ShuffleProduct.representative_independent := by
  intro K V _ _ _ p q B C σ
  unfold shuffleSummand
  apply blockProduct_coset
  exact Quotient.exact (Quotient.out_eq _)

/-- Partition full permutations into right cosets of the internal block group.
Every coset has p!q! elements, all with the same value on symmetric forms. -/
theorem permutation_partition :
    Specs.D05.M15.PolynomialPolarization.ShuffleProduct.permutation_partition := by
  intro K V _ _ _ p q B C
  rw [Finset.sum_partition
    (QuotientGroup.leftRel (Equiv.Perm.sumCongrHom (Fin p) (Fin q)).range)]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro s _
  induction s using Quotient.inductionOn' with
  | h σ =>
    let f := Equiv.Perm.sumCongrHom (Fin p) (Fin q)
    calc
      ∑ τ ∈ _, (blockProduct B.val C.val).domDomCongr τ =
          ∑ τ ∈ {τ | τ⁻¹ * σ ∈ f.range}, (blockProduct B.val C.val).domDomCongr τ := by
        simp [QuotientGroup.leftRel_apply, f, Quotient.eq]
      _ = ∑ τ ∈ {τ | τ⁻¹ ∈ f.range},
          (blockProduct B.val C.val).domDomCongr (σ * τ) := by
        conv_lhs => rw [← Finset.map_univ_equiv (Equiv.mulLeft σ),
          Finset.filter_map, Finset.sum_map]
        simp [Function.comp_def, -MonoidHom.mem_range]
      _ = ∑ τ, (blockProduct B.val C.val).domDomCongr (σ * f τ) := by
        simp_rw [f, Subgroup.inv_mem_iff, MonoidHom.mem_range, Finset.univ_filter_exists,
          Finset.sum_image Equiv.Perm.sumCongrHom_injective.injOn]
      _ = _ := by
        simp only [f, blockProduct_internal, Finset.sum_const, Finset.card_univ,
          Fintype.card_prod, Fintype.card_perm, Fintype.card_fin]
        rw [representative_independent]

/-- Symmetrization commutes with an arbitrary change of finite index type. -/
theorem sum_reindex {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (e : I ≃ J) (F : MultilinearMap K (fun _ : I => V) K) :
    (∑ σ : Equiv.Perm I, F.domDomCongr σ).domDomCongr e =
      ∑ τ : Equiv.Perm J, (F.domDomCongr e).domDomCongr τ := by
  ext x
  simp only [MultilinearMap.domDomCongr_apply, _root_.sum_apply]
  apply Fintype.sum_equiv (Equiv.permCongr e)
  intro σ
  congr 1
  funext i
  exact congrArg (fun j => x (e (σ j))) (e.symm_apply_apply i).symm

/-- Each permutation occurs exactly p!q! times when its internal orders are
forgotten. This is the counting identity transported to consecutive Fin slots. -/
theorem factorial_smul_shuffle {p q : ℕ} (B : symmetricForms K V p)
    (C : symmetricForms K V q) :
    ((p.factorial : K) * (q.factorial : K)) • shuffle B C =
      ∑ σ : Equiv.Perm (Fin (p+q)),
        ((blockProduct B.val C.val).domDomCongr finSumFinEquiv).domDomCongr σ := by
  ext x
  let e : Fin p ⊕ Fin q ≃ Fin (p+q) := finSumFinEquiv
  have h := congrArg (fun F => F (x ∘ e)) (permutation_partition B C)
  have hr := congrArg (fun F => F x)
    (sum_reindex e (blockProduct B.val C.val))
  simpa only [shuffle, MultilinearMap.domDomCongr_apply, _root_.smul_apply,
    nsmul_eq_mul, Nat.cast_mul, smul_eq_mul, e, Function.comp_def] using h.symm.trans hr

theorem permutation_sum_symmetric {I : Type*} [Fintype I] [DecidableEq I]
    (F : MultilinearMap K (fun _ : I => V) K) (x : I → V) (τ : Equiv.Perm I) :
    (∑ σ : Equiv.Perm I, F.domDomCongr σ) (x ∘ τ) =
      (∑ σ : Equiv.Perm I, F.domDomCongr σ) x := by
  simp only [_root_.sum_apply, MultilinearMap.domDomCongr_apply]
  exact Fintype.sum_equiv (Equiv.mulLeft τ) _ _ (fun σ => rfl)

theorem shuffle_symmetric :
    Specs.D05.M15.PolynomialPolarization.ShuffleProduct.shuffle_symmetric := by
  intro K V _ _ _ _ p q B C x τ
  have h := factorial_smul_shuffle B C
  have hx := congrArg (fun F => F (x ∘ τ)) h
  have hy := congrArg (fun F => F x) h
  have heq := hx.trans ((permutation_sum_symmetric
    ((blockProduct B.val C.val).domDomCongr finSumFinEquiv) x τ).trans hy.symm)
  exact mul_left_cancel₀ (mul_ne_zero
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero p))
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero q))) heq

theorem normalization :
    Specs.D05.M15.PolynomialPolarization.ShuffleProduct.normalization := by
  intro K V _ _ _ _ p q B C
  rw [averagedProduct, ← factorial_smul_shuffle, smul_smul, smul_smul]
  have hn : ((p+q).factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hp : (p.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hq : (q.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hc : (((p+q).factorial : K) / ((p.factorial : K) * (q.factorial : K))) *
      ((p+q).factorial : K)⁻¹ * ((p.factorial : K) * (q.factorial : K)) = 1 := by
    field_simp
  rw [hc, one_smul]

/-- Unnormalized symmetrization as an actual symmetric form. -/
def symmetricSum (p : ℕ) (F : MultilinearMap K (fun _ : Fin p => V) K) :
    symmetricForms K V p :=
  ⟨∑ σ : Equiv.Perm (Fin p), F.domDomCongr σ, permutation_sum_symmetric F⟩

/-- Internal permutations expand each factor, while the coset chooses the
partition of arguments. Together they enumerate every permutation once. -/
theorem symmetrize_block {p q : ℕ}
    (B : MultilinearMap K (fun _ : Fin p => V) K)
    (C : MultilinearMap K (fun _ : Fin q => V) K) :
    ∑ σ : Equiv.Perm (Fin p ⊕ Fin q), (blockProduct B C).domDomCongr σ =
      ∑ s : Equiv.Perm.ModSumCongr (Fin p) (Fin q),
        shuffleSummand (symmetricSum p B) (symmetricSum q C) s := by
  rw [Finset.sum_partition
    (QuotientGroup.leftRel (Equiv.Perm.sumCongrHom (Fin p) (Fin q)).range)]
  apply Finset.sum_congr rfl
  intro s _
  induction s using Quotient.inductionOn' with
  | h σ =>
    let f := Equiv.Perm.sumCongrHom (Fin p) (Fin q)
    calc
      ∑ τ ∈ _, (blockProduct B C).domDomCongr τ =
          ∑ τ ∈ {τ | τ⁻¹ * σ ∈ f.range}, (blockProduct B C).domDomCongr τ := by
        simp [QuotientGroup.leftRel_apply, f, Quotient.eq]
      _ = ∑ τ ∈ {τ | τ⁻¹ ∈ f.range}, (blockProduct B C).domDomCongr (σ * τ) := by
        conv_lhs => rw [← Finset.map_univ_equiv (Equiv.mulLeft σ),
          Finset.filter_map, Finset.sum_map]
        simp [Function.comp_def, -MonoidHom.mem_range]
      _ = ∑ τ, (blockProduct B C).domDomCongr (σ * f τ) := by
        simp_rw [f, Subgroup.inv_mem_iff, MonoidHom.mem_range, Finset.univ_filter_exists,
          Finset.sum_image Equiv.Perm.sumCongrHom_injective.injOn]
      _ = _ := by
        rw [representative_independent]
        ext x
        simp only [_root_.sum_apply, symmetricSum, blockProduct_apply,
          MultilinearMap.domDomCongr_apply, Fintype.sum_prod_type, Finset.sum_mul,
          Finset.mul_sum]
        rw [Finset.sum_comm]
        rfl

/-- An ordered product of covectors, before symmetrization. -/
def monomialForm {p : ℕ} (φ : Fin p → Module.Dual K V) :
    MultilinearMap K (fun _ : Fin p => V) K :=
  (MultilinearMap.mkPiAlgebra K (Fin p) K).compLinearMap φ

@[simp] theorem monomialForm_apply {p : ℕ} (φ : Fin p → Module.Dual K V) (x : Fin p → V) :
    monomialForm φ x = ∏ i, φ i (x i) := rfl

theorem permanentEquiv_symmetricSum [CharZero K] [FiniteDimensional K V]
    (p : ℕ) (φ : Fin p → Module.Dual K V) :
    permanentEquiv p (elementary K (Module.Dual K V) p φ) = symmetricSum p (monomialForm φ) := by
  apply Subtype.ext
  ext x
  rw [permanentEquiv_elementary]
  simp only [symmetricSum, _root_.sum_apply, MultilinearMap.domDomCongr_apply,
    monomialForm_apply, permanent]

theorem monomialForm_append {p q : ℕ}
    (φ : Fin p → Module.Dual K V) (ψ : Fin q → Module.Dual K V) :
    monomialForm (Fin.append φ ψ) =
      (blockProduct (monomialForm φ) (monomialForm ψ)).domDomCongr finSumFinEquiv := by
  ext x
  simp only [monomialForm_apply, MultilinearMap.domDomCongr_apply, blockProduct_apply,
    Fin.prod_univ_add, Fin.append_left, Fin.append_right, Function.comp_apply,
    finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]

/-- Multiplicativity on elementary symmetric covectors, with no factorial
rescaling on either side. -/
theorem permanent_append [CharZero K] [FiniteDimensional K V] {p q : ℕ}
    (φ : Fin p → Module.Dual K V) (ψ : Fin q → Module.Dual K V) :
    (permanentEquiv (p+q) (elementary K (Module.Dual K V) (p+q) (Fin.append φ ψ))).val =
      shuffle (permanentEquiv p (elementary K (Module.Dual K V) p φ))
        (permanentEquiv q (elementary K (Module.Dual K V) q ψ)) := by
  rw [permanentEquiv_symmetricSum, permanentEquiv_symmetricSum, permanentEquiv_symmetricSum]
  change (∑ σ : Equiv.Perm (Fin (p+q)),
      (monomialForm (Fin.append φ ψ)).domDomCongr σ) = _
  rw [monomialForm_append]
  exact (sum_reindex finSumFinEquiv
    (blockProduct (monomialForm φ) (monomialForm ψ))).symm.trans
      (congrArg (MultilinearMap.domDomCongrLinearEquiv
        (R := K) (S := K) (M₂ := V) (M₃ := K) finSumFinEquiv)
        (symmetrize_block (monomialForm φ) (monomialForm ψ)))

section QuotientProduct
open scoped TensorProduct
variable {W : Type*} [AddCommGroup W] [Module K W]

/-- Tensor concatenation followed by the symmetric quotient. -/
def tensorMul (p q : ℕ) : TensorPower K p W →ₗ[K] TensorPower K q W →ₗ[K]
    symmetricPower K W (p+q) :=
  (TensorProduct.mk K _ _).compr₂
    ((adjacentRelations K W (p+q)).mkQ.comp
      (TensorPower.mulEquiv (R := K) (M := W) (n := p) (m := q)).toLinearMap)

@[simp] theorem tensorMul_tprod (p q : ℕ) (x : Fin p → W) (y : Fin q → W) :
    tensorMul p q (PiTensorProduct.tprod K x) (PiTensorProduct.tprod K y) =
      elementary K W (p+q) (Fin.append x y) := by
  change (adjacentRelations K W (p+q)).mkQ
    ((TensorPower.mulEquiv (R := K) (M := W) (n := p) (m := q))
      (PiTensorProduct.tprod K x ⊗ₜ[K] PiTensorProduct.tprod K y)) = _
  exact congrArg (adjacentRelations K W (p+q)).mkQ (TensorPower.tprod_mul_tprod K x y)

theorem tensorMul_left (p q : ℕ) :
    adjacentRelations K W p ≤ (tensorMul (K := K) (W := W) p q).ker := by
  intro r hr
  apply LinearMap.mem_ker.mpr
  apply PiTensorProduct.ext
  ext y
  change (adjacentRelations K W (p+q)).mkQ
    (D05.M15.Symmetric.tensorRight y r) = 0
  exact (Submodule.Quotient.mk_eq_zero _).mpr (D05.M15.Symmetric.tensorRight_relation y r hr)

def leftMul (p q : ℕ) : symmetricPower K W p →ₗ[K] TensorPower K q W →ₗ[K]
    symmetricPower K W (p+q) :=
  (adjacentRelations K W p).liftQ (tensorMul p q) (tensorMul_left p q)

theorem leftMul_right (p q : ℕ) :
    adjacentRelations K W q ≤ (leftMul (K := K) (W := W) p q).flip.ker := by
  intro r hr
  apply LinearMap.mem_ker.mpr
  apply LinearMap.ext
  intro a
  obtain ⟨a, rfl⟩ := (adjacentRelations K W p).mkQ_surjective a
  have h : (tensorMul (K := K) (W := W) p q).flip r = 0 := by
    apply PiTensorProduct.ext
    ext x
    change (adjacentRelations K W (p+q)).mkQ
      (D05.M15.Symmetric.tensorLeft x r) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr (D05.M15.Symmetric.tensorLeft_relation x r hr)
  exact LinearMap.congr_fun h a

/-- Ordinary symmetric quotient multiplication, without averaging. -/
def powerMul (p q : ℕ) : symmetricPower K W p →ₗ[K] symmetricPower K W q →ₗ[K]
    symmetricPower K W (p+q) :=
  ((adjacentRelations K W q).liftQ (leftMul p q).flip (leftMul_right p q)).flip

@[simp] theorem powerMul_elementary (p q : ℕ) (x : Fin p → W) (y : Fin q → W) :
    powerMul (K := K) (W := W) p q (elementary K W p x) (elementary K W q y) =
      elementary K W (p+q) (Fin.append x y) := tensorMul_tprod p q x y

theorem powerMul_inclusion (p q : ℕ) (a : symmetricPower K W p) (b : symmetricPower K W q) :
    powerInclusion (K := K) (V := W) (p+q) (powerMul (K := K) (W := W) p q a b) = powerInclusion (K := K) (V := W) p a * powerInclusion (K := K) (V := W) q b := by
  have h : (powerMul (K := K) (W := W) p q).compr₂ (powerInclusion (K := K) (V := W) (p+q)) =
      (LinearMap.mul K (symmetricAlgebra K W)).compl₁₂ (powerInclusion (K := K) (V := W) p) (powerInclusion (K := K) (V := W) q) := by
    apply power_ext p
    intro x
    apply power_ext q
    intro y
    change powerInclusion (K := K) (V := W) (p+q) (powerMul (K := K) (W := W) p q (elementary K W p x) (elementary K W q y)) =
      powerInclusion (K := K) (V := W) p (elementary K W p x) *
      powerInclusion (K := K) (V := W) q (elementary K W q y)
    rw [powerMul_elementary, D05.M15.SymmetricBasis.inclusion_elementary,
      D05.M15.SymmetricBasis.inclusion_elementary, D05.M15.SymmetricBasis.inclusion_elementary]
    simp only [Fin.prod_univ_add, Fin.append_left, Fin.append_right]
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b
end QuotientProduct

/-- Shuffle multiplication is bilinear in its two form arguments. -/
def shuffleLinear (p q : ℕ) : symmetricForms K V p →ₗ[K] symmetricForms K V q →ₗ[K]
    MultilinearMap K (fun _ : Fin (p+q) => V) K :=
  LinearMap.mk₂ K shuffle
    (by intro B D C; ext x
        simp [shuffle, shuffleSummand, blockProduct_apply,
          MultilinearMap.domDomCongr_apply, add_mul, Finset.sum_add_distrib])
    (by intro c B C; ext x
        simp [shuffle, shuffleSummand, blockProduct_apply,
          MultilinearMap.domDomCongr_apply, Finset.mul_sum, mul_assoc])
    (by intro B C D; ext x
        simp [shuffle, shuffleSummand, blockProduct_apply,
          MultilinearMap.domDomCongr_apply, mul_add, Finset.sum_add_distrib])
    (by intro c B C; ext x
        simp [shuffle, shuffleSummand, blockProduct_apply,
          MultilinearMap.domDomCongr_apply, Finset.mul_sum, mul_left_comm])

theorem permanentEquiv_mul [CharZero K] [FiniteDimensional K V] (p q : ℕ)
    (a : symmetricPower K (Module.Dual K V) p) (b : symmetricPower K (Module.Dual K V) q) :
    (permanentEquiv (p+q) (powerMul (K := K) (W := Module.Dual K V) p q a b)).val =
      shuffle (permanentEquiv p a) (permanentEquiv q b) := by
  have h : (powerMul (K := K) (W := Module.Dual K V) p q).compr₂
      ((symmetricForms K V (p+q)).subtype.comp (permanentEquiv (p+q)).toLinearMap) =
      (shuffleLinear p q).compl₁₂ (permanentEquiv p).toLinearMap (permanentEquiv q).toLinearMap := by
    apply power_ext (K := K) (V := Module.Dual K V)
      (W := symmetricPower K (Module.Dual K V) q →ₗ[K]
        MultilinearMap K (fun _ : Fin (p+q) => V) K) p
    intro φ
    apply power_ext (K := K) (V := Module.Dual K V) q
    intro ψ
    change (permanentEquiv (p+q) (powerMul (K := K) (W := Module.Dual K V) p q (elementary K (Module.Dual K V) p φ)
      (elementary K (Module.Dual K V) q ψ))).val = _
    rw [powerMul_elementary]
    exact permanent_append φ ψ
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

theorem multiplication : Specs.D05.M15.PolynomialPolarization.ShuffleProduct.multiplication := by
  intro K V _ _ _ _ _
  refine ⟨permanentEquiv, powerMul, permanentEquiv_elementary, ?_⟩
  intro p q a b
  exact ⟨powerMul_inclusion p q a b, permanentEquiv_mul p q a b⟩

theorem degree_zero : Specs.D05.M15.PolynomialPolarization.ShuffleProduct.degree_zero := by
  intro K V _ _ _ B C x
  have hs (s : Equiv.Perm.ModSumCongr (Fin 0) (Fin 0)) :
      shuffleSummand B C s (x ∘ finSumFinEquiv) =
        B.val (fun i => Fin.elim0 i) * C.val (fun i => Fin.elim0 i) := by
    change B.val _ * C.val _ = _
    congr 1 <;> exact congrArg _ (Subsingleton.elim _ _)
  change (∑ s, shuffleSummand B C s) (x ∘ finSumFinEquiv) = _
  haveI : Subsingleton (Equiv.Perm (Fin 0 ⊕ Fin 0)) :=
    ⟨fun σ τ => Equiv.ext fun i => isEmptyElim i⟩
  haveI : Subsingleton (Equiv.Perm.ModSumCongr (Fin 0) (Fin 0)) :=
    ⟨fun s t => Quotient.inductionOn₂ s t
      (fun σ τ => congrArg Quotient.mk'' (Subsingleton.elim σ τ))⟩
  simp only [_root_.sum_apply, hs, Finset.sum_const, Finset.card_univ]
  have hc : Fintype.card (Equiv.Perm.ModSumCongr (Fin 0) (Fin 0)) = 1 :=
    Fintype.card_eq_one_iff.mpr ⟨Quotient.mk'' (Equiv.refl _), fun s => Subsingleton.elim _ _⟩
  rw [hc, one_nsmul]

attribute [local instance] MvPolynomial.decomposition

/-- The original symmetric algebra is the direct sum of its actual quotient
powers. Polynomial coordinates prove this decomposition, but the component
inclusions are the canonical upstream maps. -/
def powerDirectSumEquiv {W : Type*} [AddCommGroup W] [Module K W] {n : ℕ}
    (b : Module.Basis (Fin n) K W) :
    symmetricAlgebra K W ≃ₗ[K] (⨁ p : ℕ, symmetricPower K W p) :=
  (polynomialEquiv b).toLinearEquiv |>.trans
    ((DirectSum.decomposeLinearEquiv (MvPolynomial.homogeneousSubmodule (Fin n) K)).trans
      (DirectSum.congrLinearEquiv (fun p => (D05.M15.SymmetricBasis.powerPolynomialEquiv b p).symm)))

theorem powerDirectSumEquiv_inclusion {W : Type*} [AddCommGroup W] [Module K W]
    {n : ℕ} (b : Module.Basis (Fin n) K W) (p : ℕ) (a : symmetricPower K W p) :
    powerDirectSumEquiv b (powerInclusion (K := K) (V := W) p a) =
      DirectSum.lof K ℕ (fun p => symmetricPower K W p) p a := by
  change (DirectSum.congrLinearEquiv
      (fun p => (D05.M15.SymmetricBasis.powerPolynomialEquiv b p).symm))
    (DirectSum.decomposeLinearEquiv (MvPolynomial.homogeneousSubmodule (Fin n) K)
      (polynomialEquiv b (powerInclusion (K := K) (V := W) p a))) = _
  rw [← D05.M15.SymmetricBasis.powerPolynomialEquiv_apply,
    DirectSum.decomposeLinearEquiv_apply_coe]
  simp [DirectSum.coe_congrLinearEquiv, DirectSum.lmap_lof]

/-- The direct sum of the degreewise permanent isomorphisms. -/
def formsEquiv [CharZero K] [FiniteDimensional K V] :
    symmetricAlgebra K (Module.Dual K V) ≃ₗ[K] formAlgebra K V :=
  (powerDirectSumEquiv (Module.finBasis K (Module.Dual K V))).trans
    (DirectSum.congrLinearEquiv (fun p => permanentEquiv p))

theorem formsEquiv_inclusion [CharZero K] [FiniteDimensional K V]
    (p : ℕ) (a : symmetricPower K (Module.Dual K V) p) :
    formsEquiv (K := K) (V := V) (powerInclusion (K := K) (V := Module.Dual K V) p a) = formSingle p (permanentEquiv p a) := by
  change DirectSum.congrLinearEquiv (fun p => permanentEquiv p)
    (powerDirectSumEquiv (Module.finBasis K (Module.Dual K V)) (powerInclusion (K := K) (V := Module.Dual K V) p a)) = _
  rw [powerDirectSumEquiv_inclusion]
  simp [DirectSum.coe_congrLinearEquiv, DirectSum.lmap_lof, formSingle]

theorem graded_algebra_isomorphism :
    Specs.D05.M15.PolynomialPolarization.ShuffleProduct.graded_algebra_isomorphism := by
  intro K V _ _ _ _ _
  let e := formsEquiv (K := K) (V := V)
  let e' := e.symm.toEquiv
  let A : CommRing (formAlgebra K V) := e'.commRing
  letI := A
  let AK : Algebra K (formAlgebra K V) := e'.algebra K
  letI := AK
  let E : symmetricAlgebra K (Module.Dual K V) ≃ₐ[K] formAlgebra K V :=
    (e'.algEquiv K).symm
  have hE (p : ℕ) (a : symmetricPower K (Module.Dual K V) p) :
      E (powerInclusion (K := K) (V := Module.Dual K V) p a) = formSingle p (permanentEquiv p a) :=
    formsEquiv_inclusion p a
  refine ⟨A, AK, E, permanentEquiv, ?_, ?_, permanentEquiv_elementary, hE, ?_, ?_⟩
  · intro x y
    change e (e.symm x + e.symm y) = formAdd x y
    rw [e.map_add, e.apply_symm_apply, e.apply_symm_apply]
    rfl
  · intro c x
    change e (c • e.symm x) = formSmul c x
    rw [e.map_smul, e.apply_symm_apply]
    rfl
  · intro p q B C
    let a := (permanentEquiv p).symm B
    let b := (permanentEquiv q).symm C
    let d := powerMul (K := K) (W := Module.Dual K V) p q a b
    refine ⟨permanentEquiv (p+q) d, ?_, ?_⟩
    · simpa only [a, b, LinearEquiv.apply_symm_apply] using permanentEquiv_mul p q a b
    · have ha : formSingle p B = E (powerInclusion (K := K) (V := Module.Dual K V) p a) := by
        simpa only [a, LinearEquiv.apply_symm_apply] using (hE p a).symm
      have hb : formSingle q C = E (powerInclusion (K := K) (V := Module.Dual K V) q b) := by
        simpa only [b, LinearEquiv.apply_symm_apply] using (hE q b).symm
      rw [ha, hb, ← map_mul, ← powerMul_inclusion, hE]
  · let a := elementary K (Module.Dual K V) 0 (fun i => Fin.elim0 i)
    refine ⟨permanentEquiv 0 a, ?_, ?_⟩
    · intro x
      simp [a, permanentEquiv_elementary, permanent]
    · have ha : powerInclusion (K := K) (V := Module.Dual K V) 0 a = 1 := by
        change powerInclusion (K := K) (V := Module.Dual K V) 0
          (elementary K (Module.Dual K V) 0 (fun i => Fin.elim0 i)) = 1
        rw [D05.M15.SymmetricBasis.inclusion_elementary (K := K) (V := Module.Dual K V)]
        exact Finset.prod_empty
      exact (map_one E).symm.trans ((congrArg E ha).symm.trans (hE 0 a))

end D05.M15.PolynomialPolarization.ShuffleProduct
