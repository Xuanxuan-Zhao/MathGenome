import MathGenome.Internal.Specs.D05.M15.SymmetricBasis.PairingContractions
import MathGenome.Internal.D05.M15.SymmetricBasis.PerfectPairing
import MathGenome.Internal.D05.M15.SymmetricDerivation
import MathGenome.Internal.D05.M15.PermutationActions
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic.Ring

noncomputable section
open scoped Classical
namespace D05.M15.SymmetricBasis.PairingContractions
open Specs.D05.M15.Symmetric
open Specs.D05.M15.SymmetricBasis
open Specs.D05.M15.SymmetricBasis.PerfectPairing
open Specs.D05.M15.SymmetricBasis.PairingContractions
open D05.M15.SymmetricBasis.PerfectPairing
universe u v
variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

/-- The proved quotient/homogeneous-space equivalence, without coordinates. -/
def homogeneousEquiv (p : ℕ) : symmetricPower K V p ≃ₗ[K]
    LinearMap.range (homogeneousMap K V p) :=
  Classical.choose (D05.M15.Symmetric.power_equiv_homogeneous (K := K) (V := V) p)

theorem homogeneousEquiv_coe (p : ℕ) (α : symmetricPower K V p) :
    (homogeneousEquiv (K := K) (V := V) p α : _root_.SymmetricAlgebra K V) = powerInclusion (K := K) (V := V) p α := by
  have h : (LinearMap.range (homogeneousMap K V p)).subtype.comp
      (homogeneousEquiv (K := K) (V := V) p).toLinearMap = powerInclusion (K := K) (V := V) p := by
    apply power_ext
    intro x
    exact (Classical.choose_spec (D05.M15.Symmetric.power_equiv_homogeneous p)) x
  exact LinearMap.congr_fun h α

def contractionMap (v : V) (p : ℕ) :
    symmetricPower K (Module.Dual K V) (p+1) →ₗ[K] symmetricPower K (Module.Dual K V) p :=
  (homogeneousEquiv p).symm.toLinearMap.comp
    ((((SymmetricDerivation.contraction (evaluation (K := K) v)).comp
      (LinearMap.range (homogeneousMap K (Module.Dual K V) (p+1))).subtype).codRestrict
        (LinearMap.range (homogeneousMap K (Module.Dual K V) p))
        (fun α => SymmetricDerivation.contraction_homogeneous (evaluation (K := K) v) p α α.property)).comp
      (homogeneousEquiv (p+1)).toLinearMap)

def multiplicationMap (v : V) (p : ℕ) : symmetricPower K V p →ₗ[K] symmetricPower K V (p+1) :=
  (homogeneousEquiv (p+1)).symm.toLinearMap.comp
    (({ toFun := fun α => ⟨_root_.SymmetricAlgebra.ι K V v * α.val,
          SymmetricDerivation.generator_mul_mem v p α.val α.property⟩
        map_add' := fun _a _b => Subtype.ext (mul_add _ _ _)
        map_smul' := fun _a _b => Subtype.ext (mul_smul_comm _ _ _) } :
        LinearMap.range (homogeneousMap K V p) →ₗ[K] LinearMap.range (homogeneousMap K V (p+1))).comp
      (homogeneousEquiv p).toLinearMap)

theorem contractionMap_bridge (v : V) (p : ℕ) : IsContraction (K := K) v p (contractionMap v p) := by
  intro α
  rw [← homogeneousEquiv_coe]
  change ((homogeneousEquiv (K := K) (V := Module.Dual K V) p) ((homogeneousEquiv (K := K) (V := Module.Dual K V) p).symm _) : _root_.SymmetricAlgebra K (Module.Dual K V)) = _
  rw [LinearEquiv.apply_symm_apply]
  exact congrArg (SymmetricDerivation.contraction (evaluation (K := K) v)) (homogeneousEquiv_coe (p+1) α)

theorem multiplicationMap_bridge (v : V) (p : ℕ) : IsMultiplication (K := K) v p (multiplicationMap v p) := by
  intro x
  rw [← homogeneousEquiv_coe]
  change ((homogeneousEquiv (K := K) (V := V) (p+1)) ((homogeneousEquiv (K := K) (V := V) (p+1)).symm _) : _root_.SymmetricAlgebra K V) = _
  rw [LinearEquiv.apply_symm_apply]
  exact congrArg (_root_.SymmetricAlgebra.ι K V v * ·) (homogeneousEquiv_coe p x)

theorem operators_exist : Specs.D05.M15.SymmetricBasis.PairingContractions.operators_exist := by
  intro K V _ _ _ v p
  constructor
  · refine ⟨contractionMap v p, contractionMap_bridge v p, ?_⟩
    intro C hC
    apply LinearMap.ext
    intro α
    apply inclusion_injective p
    exact (hC α).trans (contractionMap_bridge v p α).symm
  · refine ⟨multiplicationMap v p, multiplicationMap_bridge v p, ?_⟩
    intro M hM
    apply LinearMap.ext
    intro x
    apply inclusion_injective (p+1)
    exact (hM x).trans (multiplicationMap_bridge v p x).symm

theorem degree_zero : Specs.D05.M15.SymmetricBasis.PairingContractions.degree_zero := by
  intro K V _ _ _ v α
  apply SymmetricDerivation.contraction_homogeneous_zero (evaluation (K := K) v)
  rw [← homogeneousEquiv_coe]
  exact (homogeneousEquiv (K := K) (V := Module.Dual K V) 0 α).property

theorem multiplication_formula : Specs.D05.M15.SymmetricBasis.PairingContractions.multiplication_formula := by
  intro K V _ _ _ v p M hM x
  apply inclusion_injective (p+1)
  rw [hM, inclusion_elementary, inclusion_elementary, Fin.prod_univ_succ]
  rfl

/-- Permuting the product by the inverse permutation transposes evaluation. -/
theorem permanent_transpose (p : ℕ) (φ : Fin p → Module.Dual K V) (x : Fin p → V) :
    permanent φ x = ∑ σ : Equiv.Perm (Fin p), ∏ i, φ (σ i) (x i) := by
  unfold permanent
  apply Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin p)))
  intro σ
  change (∏ i, φ i (x (σ i))) = ∏ i, φ (σ.symm i) (x i)
  simpa only [Equiv.apply_symm_apply] using
    (Equiv.prod_comp σ.symm (fun i => φ i (x (σ i)))).symm

/-- Expand by the functional evaluated on the newly adjoined vector. -/
theorem permanent_cons (p : ℕ) (φ : Fin (p+1) → Module.Dual K V) (v : V) (x : Fin p → V) :
    permanent φ (Fin.cons v x) =
      ∑ j, φ j v * permanent (fun i => φ (Equiv.swap 0 j i.succ)) x := by
  rw [permanent_transpose]
  rw [← Equiv.sum_comp (Equiv.Perm.decomposeFin (n := p)).symm]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Fin.prod_univ_succ, Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_succ, Fin.cons_zero, Fin.cons_succ]
  rw [← Finset.mul_sum]
  congr 1
  exact (permanent_transpose p (fun i => φ (Equiv.swap 0 j i.succ)) x).symm

/-- Swapping the removed occurrence to the first slot enumerates its complement. -/
theorem prod_erase_swap_tail {A : Type*} [CommMonoid A] (p : ℕ) (f : Fin (p+1) → A)
    (j : Fin (p+1)) :
    (∏ i : Fin p, f (Equiv.swap 0 j i.succ)) = ∏ i ∈ Finset.univ.erase j, f i := by
  apply Finset.prod_bij (fun i _ => Equiv.swap 0 j i.succ)
  · intro i _
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    intro h
    have hh := (Equiv.swap 0 j).injective (h.trans (Equiv.swap_apply_left 0 j).symm)
    exact Fin.succ_ne_zero i hh
  · intro i _ k _ h
    exact Fin.succ_injective _ ((Equiv.swap 0 j).injective h)
  · intro k hk
    have h0 : Equiv.swap 0 j k ≠ 0 := by
      intro h
      have hh := congrArg (Equiv.swap 0 j) h
      apply Finset.ne_of_mem_erase hk
      simpa using hh
    obtain ⟨i, hi⟩ := Fin.exists_succ_eq.mpr h0
    refine ⟨i, Finset.mem_univ _, ?_⟩
    rw [hi]
    simp
  · intro i _
    rfl

theorem contraction_formula : Specs.D05.M15.SymmetricBasis.PairingContractions.contraction_formula := by
  intro K V _ _ _ v p C hC φ
  apply inclusion_injective p
  rw [hC, inclusion_elementary]
  change SymmetricDerivation.contraction (evaluation (K := K) v) (SymmetricDerivation.word (p+1) φ) = _
  rw [SymmetricDerivation.contraction_word, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, inclusion_elementary]
  change φ j v • (∏ i ∈ Finset.univ.erase j, _root_.SymmetricAlgebra.ι K _ (φ i)) = _
  rw [prod_erase_swap_tail p (fun i => _root_.SymmetricAlgebra.ι K _ (φ i)) j]

/-- Bilinearity extends the elementary column expansion to the whole quotients. -/
theorem adjoint : Specs.D05.M15.SymmetricBasis.PairingContractions.adjoint := by
  intro K V _ _ _ v p C M hC hM P Q hP hQ
  dsimp [IsPermanentPairing] at hP hQ
  have h : P.comp C = Q.compl₂ M := by
    apply power_ext
    intro φ
    apply power_ext
    intro x
    change P (C (elementary K (Module.Dual K V) (p+1) φ)) (elementary K V p x) =
      Q (elementary K (Module.Dual K V) (p+1) φ) (M (elementary K V p x))
    rw [contraction_formula v p C hC, multiplication_formula v p M hM, hQ]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hP, smul_eq_mul]
    exact (permanent_cons p φ v x).symm
  intro α x
  exact LinearMap.congr_fun (LinearMap.congr_fun h α) x

theorem contractions_commute : Specs.D05.M15.SymmetricBasis.PairingContractions.contractions_commute := by
  intro K V _ _ _ v w α
  induction α using _root_.SymmetricAlgebra.induction with
  | algebraMap a => simp only [SymmetricDerivation.contraction_scalar, map_zero]
  | ι φ => simp only [SymmetricDerivation.contraction_generator, SymmetricDerivation.contraction_scalar]
  | add a b ha hb => simp only [map_add, ha, hb]
  | mul a b ha hb =>
    simp only [SymmetricDerivation.contraction_mul, map_add, ha, hb]
    ring

theorem iterated_adjoint : Specs.D05.M15.SymmetricBasis.PairingContractions.iterated_adjoint := by
  intro K V _ _ _ vs p P hP
  induction vs with
  | nil =>
    refine ⟨LinearMap.id, LinearMap.id, ?_, ?_, ?_⟩
    · intro α; rfl
    · intro x; simp
    · intro α x; rfl
  | cons v vs ih =>
    obtain ⟨C, M, hC, hM, hp⟩ := ih
    refine ⟨C.comp (contractionMap v (p+vs.length)),
      (multiplicationMap v (p+vs.length)).comp M, ?_, ?_, ?_⟩
    · intro α
      rw [LinearMap.comp_apply, hC]
      change iterated (K := K) vs (powerInclusion (K := K) (V := Module.Dual K V) (p+vs.length)
        (contractionMap v (p+vs.length) α)) = _
      rw [contractionMap_bridge]
      rfl
    · intro x
      simp only [List.length_cons, Nat.add_succ]
      rw [LinearMap.comp_apply, multiplicationMap_bridge, hM]
      simp only [List.map_cons, List.prod_cons]
      exact (mul_assoc _ _ _).symm
    · intro α x
      rw [LinearMap.comp_apply, hp]
      exact adjoint v (p+vs.length) _ _ (contractionMap_bridge v _) (multiplicationMap_bridge v _)
        _ _ (hP _) (hP _) α (M x)

/-- The permanent pairing agrees with the unnormalized tensor evaluation sum. -/
theorem quotient_tensorPairing (p : ℕ)
    (P : symmetricPower K (Module.Dual K V) p →ₗ[K] symmetricPower K V p →ₗ[K] K)
    (hP : IsPermanentPairing p P)
    (α : TensorPower K p (Module.Dual K V)) (x : TensorPower K p V) :
    P (Submodule.Quotient.mk α : symmetricPower K (Module.Dual K V) p)
      (Submodule.Quotient.mk x : symmetricPower K V p) = tensorPairing p α x := by
  induction α using PiTensorProduct.induction_on with
  | smul_tprod a φ =>
    induction x using PiTensorProduct.induction_on with
    | smul_tprod b x =>
      simp only [Submodule.Quotient.mk_smul, map_smul, LinearMap.smul_apply]
      change b • (a • P (elementary K (Module.Dual K V) p φ) (elementary K V p x)) = _
      rw [hP, tensorPairing_tprod]
    | add x y hx hy =>
      simp only [Submodule.Quotient.mk_add, map_add, hx, hy]
  | add α β hα hβ =>
    simp only [Submodule.Quotient.mk_add, map_add, LinearMap.add_apply, hα, hβ]

/-- The quotient is unchanged by averaging, with just the degree factorial hypothesis. -/
theorem quotient_average (p : ℕ) (hp : (p.factorial : K) ≠ 0) (t : TensorPower K p V) :
    (adjacentRelations K V p).mkQ
      (Specs.D05.M15.Symmetrizers.symmetricProjector (K := K) (V := V) p hp t) =
      (adjacentRelations K V p).mkQ t := by
  have he (σ : Equiv.Perm (Fin p)) :
      (adjacentRelations K V p).mkQ
        (Specs.D05.M15.PermutationActions.permutationOperator p σ t) =
      (adjacentRelations K V p).mkQ t := by
    have hh : (adjacentRelations K V p).mkQ.comp
        (Specs.D05.M15.PermutationActions.permutationOperator p σ) =
        (adjacentRelations K V p).mkQ := by
      apply PiTensorProduct.ext
      apply MultilinearMap.ext
      intro x
      change (adjacentRelations K V p).mkQ
        (Specs.D05.M15.PermutationActions.permutationOperator p σ (PiTensorProduct.tprod K x)) = _
      rw [D05.M15.PermutationActions.operator_apply]
      exact D05.M15.Symmetric.elementary_symmetric p x σ⁻¹
    exact LinearMap.congr_fun hh t
  simp only [Specs.D05.M15.Symmetrizers.symmetricProjector, LinearMap.smul_apply,
    LinearMap.sum_apply, map_smul, map_sum, he, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ hp, one_smul]

/-- One vector-side average is the inverse factorial times the tensor permanent. -/
theorem evaluate_average_right (p : ℕ) (hp : (p.factorial : K) ≠ 0)
    (α : TensorPower K p (Module.Dual K V)) (x : TensorPower K p V) :
    PiTensorProduct.dualDistrib (R := K) (M := fun _ : Fin p => V) α
      (Specs.D05.M15.Symmetrizers.symmetricProjector (K := K) (V := V) p hp x) =
    (p.factorial : K)⁻¹ * tensorPairing p α x := by
  simp only [Specs.D05.M15.Symmetrizers.symmetricProjector, LinearMap.smul_apply,
    LinearMap.sum_apply, map_smul, map_sum, smul_eq_mul,
    tensorPairing, LinearMap.compl₂_apply]
  congr 1
  apply Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin p)))
  intro σ
  rfl

theorem averaged_pairing : Specs.D05.M15.SymmetricBasis.PairingContractions.averaged_pairing := by
  intro K V _ _ _ p hp P hP α x
  rw [evaluate_average_right]
  rw [← quotient_tensorPairing p P hP]
  have hq := quotient_average (K := K) (V := Module.Dual K V) p hp α
  change (Submodule.Quotient.mk
    (Specs.D05.M15.Symmetrizers.symmetricProjector (K := K) (V := Module.Dual K V) p hp α) :
    symmetricPower K (Module.Dual K V) p) = Submodule.Quotient.mk α at hq
  rw [hq]
  rfl

theorem degree_contractions_commute : Specs.D05.M15.SymmetricBasis.PairingContractions.degree_contractions_commute := by
  intro K V _ _ _ v w p Cv Cw Cv' Cw' hCv hCw hCv' hCw'
  apply LinearMap.ext
  intro α
  apply inclusion_injective p
  simp only [LinearMap.comp_apply]
  rw [hCv, hCw, hCw', hCv']
  exact contractions_commute v w _

end D05.M15.SymmetricBasis.PairingContractions
