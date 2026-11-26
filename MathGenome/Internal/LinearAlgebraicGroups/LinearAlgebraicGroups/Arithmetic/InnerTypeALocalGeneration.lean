import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.InnerTypeALocalGeneration
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalNormOneCommutators
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Logic.Equiv.Fin.Basic
import Batteries.Tactic.OpenPrivate

noncomputable section

open scoped WithZero commutatorElement
open RM03.CSA Matrix
open LinearAlgebraicGroups.Arithmetic.LocalNormOneCommutators
open LinearAlgebraicGroups.Arithmetic.LocalNormOneCommutators.Spec

open private commutator_of_mul_eq norm_algEquiv linear_coordinate_continuous
  reindex_mem_elementaryGroup localField_of_complete_discrete
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalNormOneCommutators

namespace LinearAlgebraicGroups.Arithmetic.InnerTypeALocalGeneration

open Spec

universe u v

section Elementary

variable {B ι : Type*} [Ring B] [Fintype ι] [DecidableEq ι]

private theorem elementary_commutator (i j k : ι) (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (a : B) :
    ⁅elementary i j hij a, elementary j k hjk 1⁆ = elementary i k hik a := by
  apply commutator_of_mul_eq
  apply Units.ext
  simp only [Units.val_mul, val_elementary, add_mul, mul_add, one_mul, mul_one,
    Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne _ _ _ _ hik.symm _,
    Matrix.single_mul_single_of_ne _ _ _ _ hjk.symm _, add_zero]
  abel

private theorem elementary_sum_mem (C : Subgroup (Matrix ι ι B)ˣ)
    {i j : ι} (hij : i ≠ j) {α : Type*} (s : Finset α) (a : α → B)
    (ha : ∀ k ∈ s, elementary i j hij (a k) ∈ C) :
    elementary i j hij (∑ k ∈ s, a k) ∈ C := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hz : elementary i j hij (0 : B) = 1 := Units.ext (by simp)
    simpa only [Finset.sum_empty, hz] using C.one_mem
  | @insert k s hk ih =>
    rw [Finset.sum_insert hk, ← elementary_mul]
    exact C.mul_mem (ha k (Finset.mem_insert_self _ _))
      (ih fun l hl => ha l (Finset.mem_insert_of_mem hl))

private theorem elementary_le {G : Type*} [Group G]
    (f : (Matrix ι ι B)ˣ →* G) (C : Subgroup G)
    (hf : ∀ (i j : ι) (hij : i ≠ j) (a : B), f (elementary i j hij a) ∈ C) :
    elementaryGroup ι ≤ C.comap f := by
  apply (Subgroup.closure_le _).2
  rintro _ ⟨i, j, hij, a, rfl⟩
  exact hf i j hij a

end Elementary

section Coefficients

variable {F A B ι : Type*} [Field F] [Ring A] [Ring B] [Algebra F A] [Algebra F B]
  [Fintype ι] [DecidableEq ι]

private theorem mapMatrix_elementary (e : A ≃ₐ[F] B)
    (i j : ι) (hij : i ≠ j) (a : A) :
    Units.map e.mapMatrix.toMonoidHom (elementary i j hij a) = elementary i j hij (e a) := by
  apply Units.ext
  change e.mapMatrix (1 + single i j a) = 1 + single i j (e a)
  rw [map_add, map_one]
  congr 1
  ext k l
  simp [Matrix.single_apply, apply_ite e]

private theorem mapMatrix_mem_elementary (e : A ≃ₐ[F] B) (x : (Matrix ι ι A)ˣ) :
    Units.map e.mapMatrix.toMonoidHom x ∈ elementaryGroup ι ↔ x ∈ elementaryGroup ι := by
  have forward (f : A ≃ₐ[F] B) :
      elementaryGroup ι ≤ (elementaryGroup ι).comap (Units.map f.mapMatrix.toMonoidHom) := by
    apply elementary_le
    intro i j hij a
    rw [mapMatrix_elementary]
    exact elementary_mem_elementaryGroup i j hij (f a)
  have backward :
      elementaryGroup ι ≤ (elementaryGroup ι).comap (Units.map e.symm.mapMatrix.toMonoidHom) := by
    apply elementary_le
    intro i j hij a
    rw [mapMatrix_elementary]
    exact elementary_mem_elementaryGroup i j hij (e.symm a)
  constructor
  · intro hx
    have h := backward hx
    change Units.map e.symm.mapMatrix.toMonoidHom (Units.map e.mapMatrix.toMonoidHom x) ∈ elementaryGroup (B := A) ι at h
    have he : Units.map e.symm.mapMatrix.toMonoidHom (Units.map e.mapMatrix.toMonoidHom x) = x :=
      Units.ext (e.mapMatrix.symm_apply_apply (x : Matrix ι ι A))
    rwa [he] at h
  · intro hx
    exact (forward e) hx

end Coefficients

section Blocks

variable {F B : Type*} [Field F] [DivisionRing B] [Algebra F B] {m s : ℕ}

private theorem flatten_single (i j : Fin m) (hij : i ≠ j)
    (k l : Fin s) (a : B) :
    Units.map (compAlgEquiv (Fin m) (Fin s) B F).toMonoidHom
      (elementary i j hij (single k l a)) =
        elementary (i, k) (j, l) (fun h => hij (congrArg Prod.fst h)) a := by
  apply Units.ext
  change compAlgEquiv (Fin m) (Fin s) B F (1 + single i j (single k l a)) =
    1 + single (i, k) (j, l) a
  rw [map_add, map_one, compAlgEquiv_apply, comp_single_single]

private theorem flatten_mem_elementary (hm : 2 ≤ m)
    (x : (Matrix (Fin m) (Fin m) (Matrix (Fin s) (Fin s) B))ˣ) :
    Units.map (compAlgEquiv (Fin m) (Fin s) B F).toMonoidHom x ∈
      elementaryGroup (Fin m × Fin s) ↔ x ∈ elementaryGroup (Fin m) := by
  classical
  let e := Units.mapEquiv (compAlgEquiv (Fin m) (Fin s) B F).toMulEquiv
  change e x ∈ elementaryGroup (Fin m × Fin s) ↔ x ∈ elementaryGroup (Fin m)
  have forward : elementaryGroup (Fin m) ≤ (elementaryGroup (Fin m × Fin s)).comap e.toMonoidHom := by
    apply elementary_le
    intro i j hij M
    let C := (elementaryGroup (B := B) (Fin m × Fin s)).comap e.toMonoidHom
    change elementary i j hij M ∈ C
    rw [matrix_eq_sum_single M]
    apply elementary_sum_mem C hij
    intro k _
    apply elementary_sum_mem C hij
    intro l _
    change e (elementary i j hij (single k l (M k l))) ∈ elementaryGroup (Fin m × Fin s)
    rw [show e (elementary i j hij (single k l (M k l))) = _ from
      flatten_single (F := F) i j hij k l (M k l)]
    exact elementary_mem_elementaryGroup _ _ _ _
  let H := (elementaryGroup (B := Matrix (Fin s) (Fin s) B) (Fin m)).comap e.symm.toMonoidHom
  have across (p q : Fin m × Fin s) (h : p.1 ≠ q.1) (a : B) :
      elementary p q (fun hpq => h (congrArg Prod.fst hpq)) a ∈ H := by
    change e.symm (elementary p q _ a) ∈ elementaryGroup (Fin m)
    rw [← flatten_single (F := F) p.1 q.1 h p.2 q.2 a]
    change e.symm (e (elementary p.1 q.1 h (single p.2 q.2 a))) ∈ elementaryGroup (Fin m)
    rw [e.symm_apply_apply]
    exact elementary_mem_elementaryGroup _ _ _ _
  have backward : elementaryGroup (Fin m × Fin s) ≤ H := by
    apply elementary_le
    intro p q hpq a
    by_cases h : p.1 = q.1
    · let : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
      obtain ⟨k, hk⟩ := exists_ne p.1
      let r := (k, p.2)
      have hpr : p.1 ≠ r.1 := hk.symm
      have hrq : r.1 ≠ q.1 := h ▸ hk
      rw [← elementary_commutator p r q (fun he => hpr (congrArg Prod.fst he))
        (fun he => hrq (congrArg Prod.fst he)) hpq a]
      exact H.mul_mem (H.mul_mem (H.mul_mem (across p r hpr a) (across r q hrq 1))
        (H.inv_mem (across p r hpr a))) (H.inv_mem (across r q hrq 1))
    · exact across p q h a
  constructor
  · intro hx
    have he := backward hx
    change e.symm (e x) ∈ elementaryGroup (Fin m) at he
    rwa [e.symm_apply_apply] at he
  · intro hx
    exact forward hx

private theorem reindex_mem_iff {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (r : ι ≃ κ) (x : (Matrix ι ι B)ˣ) :
    Units.map (reindexAlgEquiv F B r).toMonoidHom x ∈ elementaryGroup κ ↔
      x ∈ elementaryGroup ι := by
  let y := Units.map (reindexAlgEquiv ℤ B r).toMonoidHom x
  have he : Units.map (reindexAlgEquiv F B r).toMonoidHom x = y := Units.ext rfl
  rw [he]
  constructor
  · intro hy
    have hx := reindex_mem_elementaryGroup r.symm y hy
    have hxy : Units.map (reindexAlgEquiv ℤ B r.symm).toMonoidHom y = x := by
      apply Units.ext
      ext i j
      change (x : Matrix ι ι B) (r.symm (r i)) (r.symm (r j)) = (x : Matrix ι ι B) i j
      simp
    rwa [hxy] at hx
  · intro hx
    exact reindex_mem_elementaryGroup r x hx

variable {A : Type*} [Ring A] [Algebra F A]

private def flattenBlocks (e : A ≃ₐ[F] Matrix (Fin s) (Fin s) B) :
    Matrix (Fin m) (Fin m) A ≃ₐ[F] Matrix (Fin (m * s)) (Fin (m * s)) B :=
  e.mapMatrix.trans ((compAlgEquiv (Fin m) (Fin s) B F).trans
    (reindexAlgEquiv F B finProdFinEquiv))

private theorem flattenBlocks_mem (hm : 2 ≤ m) (e : A ≃ₐ[F] Matrix (Fin s) (Fin s) B)
    (x : (Matrix (Fin m) (Fin m) A)ˣ) :
    Units.map (flattenBlocks (m := m) e).toMonoidHom x ∈ elementaryGroup (Fin (m * s)) ↔
      x ∈ elementaryGroup (Fin m) := by
  let y := Units.map e.mapMatrix.toMonoidHom x
  let z := Units.map (compAlgEquiv (Fin m) (Fin s) B F).toMonoidHom y
  change Units.map (reindexAlgEquiv F B finProdFinEquiv).toMonoidHom z ∈ _ ↔ _
  exact (reindex_mem_iff finProdFinEquiv z).trans
    ((flatten_mem_elementary hm y).trans (mapMatrix_mem_elementary e x))

end Blocks

section Density

variable {F A B : Type*} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F]
  [Infinite F] [Ring A] [Algebra F A] [DivisionRing B] [Algebra F B]

private theorem blockDensity (hA : IsCentralSimple F A) (hB : IsCentralSimple F B)
    (h : denseCommutators hB) {m s : ℕ} (hm : 2 ≤ m) (hs : 0 < s)
    (p : A ≃ₐ[F] Matrix (Fin s) (Fin s) B) :
    BlockDensity hA m hm := by
  classical
  have hn := hm.trans (Nat.le_mul_of_pos_right m hs)
  let hM := matrixCentralSimple hA (by omega : 0 < m)
  let hN := matrixCentralSimple hB (by omega : 0 < m * s)
  let e := flattenBlocks (m := m) p
  let f := Units.mapEquiv e.toMulEquiv
  have hmem (x : (Matrix (Fin m) (Fin m) A)ˣ) :
      f x ∈ elementaryGroup (Fin (m * s)) ↔ x ∈ elementaryGroup (Fin m) :=
    flattenBlocks_mem hm p x
  have hnorm (x : (Matrix (Fin m) (Fin m) A)ˣ) :
      x ∈ normOne hM ↔ f x ∈ normOne hN := by
    change reducedNorm hM (x : Matrix _ _ A) = 1 ↔ reducedNorm hN (e (x : Matrix _ _ A)) = 1
    rw [norm_algEquiv hM hN e]
  obtain ⟨hsub, hdense⟩ := (matrixTransfer hB h (m * s) (by omega) hN).2 hn
  refine ⟨fun x hx => (hnorm x).mpr (hsub ((hmem x).mpr hx)), ?_⟩
  intro b
  let := coordinateTopology b
  let := hN.2.2
  let c := Module.finBasis F (Matrix (Fin (m * s)) (Fin (m * s)) B)
  let := coordinateTopology c
  have hc : Continuous f.symm :=
    (linear_coordinate_continuous c b e.symm.toLinearMap).units_map e.symm.toMonoidHom
  intro x hx
  have hh : (elementaryGroup (B := B) (Fin (m * s)) :
      Set (Matrix (Fin (m * s)) (Fin (m * s)) B)ˣ) ⊆
      f.symm ⁻¹' closure (elementaryGroup (B := A) (Fin m) : Set (Matrix (Fin m) (Fin m) A)ˣ) := by
    intro y hy
    apply subset_closure
    apply (hmem (f.symm y)).mp
    rw [f.apply_symm_apply]
    exact hy
  have hin := closure_minimal hh (isClosed_closure.preimage hc) (hdense c ((hnorm x).mp hx))
  change f.symm (f x) ∈ closure (elementaryGroup (B := A) (Fin m) :
    Set (Matrix (Fin m) (Fin m) A)ˣ) at hin
  rwa [f.symm_apply_apply] at hin

private theorem blockDensity_of_division {C : Type v} [Ring C] [Algebra F C]
    (hC : IsCentralSimple F C)
    (h : ∀ {D : Type v} [DivisionRing D] [Algebra F D] (hD : IsCentralSimple F D),
      denseCommutators hD) (m : ℕ) (hm : 2 ≤ m) :
    BlockDensity hC m hm := by
  obtain ⟨s, D, _, _, hD, hs, ⟨e⟩⟩ := MatrixDivision.exists_presentation F C hC
  let hD' := isCentralSimple_of_isCentralDivision F D hD
  exact blockDensity hC hD' (h hD') hm hs e

end Density

theorem localBlockGeneration : LocalBlockGeneration.{u,v} := by
  refine ⟨?_, ?_, ?_⟩
  · intro F _ _ _ _ A _ _ hA m hm
    let : Infinite ℤᵐ⁰ := Infinite.of_injective WithZero.exp WithZero.exp_injective
    let : Infinite F := Infinite.of_surjective _
      ((IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F).surjective.comp
        (ValuativeRel.valuation_surjective (K := F)))
    exact blockDensity_of_division hA nonarchimedeanDivision m hm
  · intro A _ _ hA m hm
    apply blockDensity_of_division hA _ m hm
    intro B _ _ hB b
    let := coordinateTopology b
    intro x hx
    obtain ⟨a, b, rfl⟩ := realDivision hB x hx
    exact subset_closure (Subgroup.commutator_mem_commutator (by trivial) (by trivial))
  · intro A _ _ hA m hm
    apply blockDensity_of_division hA _ m hm
    intro B _ _ hB b
    let := coordinateTopology b
    intro x hx
    rw [complexDivision hB x hx]
    exact subset_closure ((commutator Bˣ).one_mem)

theorem completeDiscreteBlockGeneration : CompleteDiscreteBlockGeneration.{u,v} := by
  intro F _ _ _ _ _ _ _ he A _ _ hA m hm
  obtain ⟨e⟩ := he
  let := localField_of_complete_discrete e
  exact localBlockGeneration.1 hA m hm

theorem splitElementaryGeneration : SplitElementaryGeneration.{u} := by
  intro F _ n hn
  let E := elementaryGroup (B := F) (Fin n)
  let det : (Matrix (Fin n) (Fin n) F)ˣ →* F := Matrix.detMonoidHom.comp (Units.coeHom _)
  have hdet : E ≤ det.ker := by
    apply (Subgroup.closure_le _).2
    rintro _ ⟨i, j, hij, a, rfl⟩
    exact det_transvection_of_ne i j hij a
  ext x
  change x ∈ E ↔ (x : Matrix (Fin n) (Fin n) F).det = 1
  refine ⟨fun hx => hdet hx, ?_⟩
  intro hx
  let j : Fin n := ⟨0, by omega⟩
  obtain ⟨L, hL, R, hR, a, ha⟩ := elementary_single_diagonal j x
  have hLa : det L = 1 := hdet hL
  have hRa : det R = 1 := hdet hR
  have hs : det (diagonalSlot j a) = 1 := by
    rw [← ha, map_mul, map_mul, hLa, hRa, one_mul, mul_one]
    exact hx
  change (diagonalSlot j a : Matrix (Fin n) (Fin n) F).det = 1 at hs
  rw [val_diagonalSlot, Matrix.det_diagonal, Fintype.prod_ite_eq'] at hs
  have hunit : a = 1 := Units.ext hs
  have he : x = L⁻¹ * R⁻¹ := by
    rw [hunit, map_one] at ha
    calc
      x = L⁻¹ * (L * x * R) * R⁻¹ := by group
      _ = L⁻¹ * R⁻¹ := by rw [ha, mul_one]
  rw [he]
  exact E.mul_mem (E.inv_mem hL) (E.inv_mem hR)

theorem splitBlockGeneration : SplitBlockGeneration.{u,v} := by
  intro F _ A _ _ hA m hm s hs p
  let hM := matrixCentralSimple hA (by omega : 0 < m)
  let e := flattenBlocks (m := m) p
  have hn := hm.trans (Nat.le_mul_of_pos_right m hs)
  have hdeg := degree_eq_matrix_size hM ((Algebra.TensorProduct.lid F _).trans e)
  let e' := e.trans (reindexAlgEquiv F F (finCongr hdeg.symm))
  ext x
  have hdet : reducedNorm hM (x : Matrix _ _ A) = (e (x : Matrix _ _ A)).det := by
    rw [reducedNorm_eq_det hM _ e']
    exact det_reindex_self (finCongr hdeg.symm) (e (x : Matrix (Fin m) (Fin m) A))
  change x ∈ elementaryGroup (Fin m) ↔ reducedNorm hM (x : Matrix _ _ A) = 1
  rw [hdet, ← flattenBlocks_mem hm p x]
  exact Set.ext_iff.mp (splitElementaryGeneration (m * s) hn) _

end LinearAlgebraicGroups.Arithmetic.InnerTypeALocalGeneration
