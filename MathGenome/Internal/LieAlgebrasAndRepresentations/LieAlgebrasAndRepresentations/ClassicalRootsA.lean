import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ClassicalRootsA
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RootDecomposition
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Convert

namespace LieAlgebrasAndRepresentations.ClassicalRootsA
open Specs.LieAlgebrasAndRepresentations.ClassicalRootsA

variable {n : ℕ}

@[simp] theorem root_apply (i j : Fin (n+1)) (h : cartan n) :
    root n i j h = h.val.val i i - h.val.val j j := rfl

@[simp] theorem coroot_apply (i j a b : Fin (n+1)) :
    (coroot n i j).val.val a b =
      Matrix.single i i (1 : ℂ) a b - Matrix.single j j (1 : ℂ) a b := rfl

@[simp] theorem rootVector_apply (i j : Fin (n+1)) (hij : i ≠ j) (a b) :
    (rootVector n i j hij).val a b = Matrix.single i j (1 : ℂ) a b := rfl

/-- Entrywise adjoint action of a diagonal traceless matrix. -/
theorem bracket_entry (h : cartan n) (X : sl n) (a b : Fin (n+1)) :
    (⁅(h : sl n), X⁆ : sl n).val a b =
      (h.val.val a a - h.val.val b b) * X.val a b := by
  change (h.val.val * X.val - X.val * h.val.val) a b = _
  have hd := h.property.diagonal_diag
  rw [← hd]
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.sub_apply, Matrix.diag_apply, Matrix.diagonal_apply_eq]
  ring

theorem mem_space_iff (α : Module.Dual ℂ (cartan n)) (X : sl n) :
    X ∈ rootSpace (cartan n) α ↔
      ∀ (h : cartan n) (a b : Fin (n+1)),
        (h.val.val a a - h.val.val b b) * X.val a b = α h * X.val a b := by
  rw [mem_rootSpace]
  constructor
  · intro hx h a b
    have hh := congrArg (fun Y : sl n => Y.val a b) (hx h)
    change (⁅(h : sl n), X⁆ : sl n).val a b = α h * X.val a b at hh
    rwa [bracket_entry] at hh
  · intro hx h
    apply Subtype.ext
    ext a b
    change (⁅(h : sl n), X⁆ : sl n).val a b = α h * X.val a b
    rw [bracket_entry]
    exact hx h a b

theorem root_ne_zero (i j : Fin (n+1)) (hij : i ≠ j) : root n i j ≠ 0 := by
  intro hz
  have h := congrArg (fun α : Module.Dual ℂ (cartan n) => α (coroot n i j)) hz
  norm_num [root_apply, Matrix.single, hij, hij.symm] at h

theorem root_injective (i j k l : Fin (n+1)) (hij : i ≠ j) (hkl : k ≠ l)
    (he : root n i j = root n k l) : i = k ∧ j = l := by
  have h := congrArg (fun α : Module.Dual ℂ (cartan n) => α (coroot n i j)) he
  simp only [root_apply, coroot_apply, Matrix.single_apply] at h
  norm_num at h
  split_ifs at h <;> norm_num at h <;> aesop

theorem rootVector_ne_zero (i j : Fin (n+1)) (hij : i ≠ j) :
    rootVector n i j hij ≠ 0 := by
  intro he
  have h := congrArg (fun X : sl n => X.val i j) he
  simp [Matrix.single] at h

theorem rootVector_mem (i j : Fin (n+1)) (hij : i ≠ j) :
    rootVector n i j hij ∈ rootSpace (cartan n) (root n i j) := by
  rw [mem_space_iff]
  intro h a b
  by_cases hai : i = a <;> by_cases hbj : j = b <;>
    simp_all [Matrix.single]

/-- A nonzero entry of a weight vector determines its entire weight. -/
theorem weight_of_entry (α : Module.Dual ℂ (cartan n)) (X : sl n)
    (hX : X ∈ rootSpace (cartan n) α) (a b : Fin (n+1)) (hab : X.val a b ≠ 0) :
    α = root n a b := by
  ext h
  exact (mul_right_cancel₀ hab ((mem_space_iff α X).mp hX h a b)).symm

theorem root_space (n : ℕ) (i j : Fin (n+1)) (hij : i ≠ j) :
    rootSpace (cartan n) (root n i j) = Submodule.span ℂ {rootVector n i j hij} := by
  apply le_antisymm
  · intro X hX
    have he : X = X.val i j • rootVector n i j hij := by
      apply Subtype.ext
      ext a b
      by_cases hab : X.val a b = 0
      · by_cases hai : a = i <;> by_cases hbj : b = j <;>
          simp_all [Matrix.single]
      · have hw := weight_of_entry _ X hX a b hab
        have hab' : a ≠ b := by
          intro he
          subst b
          apply root_ne_zero i j hij
          simpa [root, epsilon] using hw
        obtain ⟨ha, hb⟩ := root_injective i j a b hij hab' hw
        subst a; subst b
        simp [Matrix.single]
    rw [he]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (rootVector_mem i j hij))

theorem zero_space (n : ℕ) :
    rootSpace (cartan n) 0 = (cartan n).toSubmodule := by
  ext X
  constructor
  · intro hX
    change X.val.IsDiag
    intro a b hab
    by_contra hnz
    have hw := weight_of_entry 0 X hX a b hnz
    exact root_ne_zero a b hab hw.symm
  · intro hX
    rw [mem_space_iff]
    intro h a b
    by_cases hab : a = b
    · subst b; simp
    · have hz := hX hab
      simp [hz]

theorem root_set (n : ℕ) (α : Module.Dual ℂ (cartan n)) :
    α ∈ rootSet (cartan n) ↔ ∃ i j : Fin (n+1), i ≠ j ∧ α = root n i j := by
  constructor
  · rintro ⟨hα, hspace⟩
    obtain ⟨X, hX, hnz⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hspace
    have he : ∃ a b, X.val a b ≠ 0 := by
      by_contra! hz
      apply hnz
      apply Subtype.ext
      ext a b
      exact hz a b
    obtain ⟨a, b, hab⟩ := he
    have hw := weight_of_entry α X hX a b hab
    refine ⟨a, b, ?_, hw⟩
    intro he
    subst b
    apply hα
    simpa [root] using hw
  · rintro ⟨i, j, hij, rfl⟩
    refine ⟨root_ne_zero i j hij, ?_⟩
    intro hz
    have hv := rootVector_mem i j hij
    change rootSpace (cartan n) (root n i j) = ⊥ at hz
    rw [hz] at hv
    exact rootVector_ne_zero i j hij hv

/-- A traceless one-by-one matrix is zero since its trace is its only entry. -/
theorem rank_zero_matrix (X : sl 0) : X = 0 := by
  have htrace : Matrix.trace X.val = 0 := X.property
  apply Subtype.ext
  ext a b
  rw [Fin.eq_zero a, Fin.eq_zero b]
  change X.val 0 0 = 0
  exact (Matrix.trace_fin_one X.val).symm.trans htrace

theorem rank_zero_cartan (h : cartan 0) : h = 0 :=
  Subtype.ext (rank_zero_matrix (h : sl 0))

theorem rank_zero_root_set : rootSet (cartan 0) = ∅ := by
  ext α
  constructor
  · intro hα
    obtain ⟨i, j, hij, _⟩ := (root_set 0 α).mp hα
    exact (hij (Subsingleton.elim (α := Fin 1) i j)).elim
  · simp

theorem root_dimension (n : ℕ) (i j : Fin (n+1)) (hij : i ≠ j) :
    Module.finrank ℂ (rootSpace (cartan n) (root n i j)) = 1 := by
  rw [root_space n i j hij]
  exact finrank_span_singleton (rootVector_ne_zero i j hij)

instance cartan_abelian (n : ℕ) : IsLieAbelian (cartan n) := by
  constructor
  intro X Y
  apply Subtype.ext
  apply Subtype.ext
  ext a b
  change (⁅(X : sl n), (Y : sl n)⁆ : sl n).val a b = 0
  rw [bracket_entry]
  by_cases hab : a = b
  · subst b; simp
  · rw [Y.property hab, mul_zero]

theorem cartan_isCartan (n : ℕ) : (cartan n).IsCartanSubalgebra := by
  refine ⟨inferInstance, le_antisymm ?_ (cartan n).le_normalizer⟩
  intro X hX
  change X.val.IsDiag
  intro a b hab
  have hm := ((cartan n).mem_normalizer_iff' X).mp hX
    (coroot n a b) (coroot n a b).property
  have hz := hm hab
  change (⁅(coroot n a b : sl n), X⁆ : sl n).val a b = 0 at hz
  rw [bracket_entry] at hz
  norm_num [Matrix.single, hab, hab.symm] at hz
  exact hz

theorem opposite_bracket (i j : Fin (n+1)) (hij : i ≠ j) :
    ⁅rootVector n i j hij, rootVector n j i hij.symm⁆ = (coroot n i j : sl n) := by
  apply Subtype.ext
  change Matrix.single i j (1 : ℂ) * Matrix.single j i 1 -
    Matrix.single j i 1 * Matrix.single i j 1 = _
  simp only [Matrix.single_mul_single_same, one_mul]
  rfl

theorem root_triple (n : ℕ) (i j : Fin (n+1)) (hij : i ≠ j) :
    ⁅rootVector n i j hij, rootVector n j i hij.symm⁆ = (coroot n i j : sl n) ∧
    ⁅(coroot n i j : sl n), rootVector n i j hij⁆ = (2 : ℂ) • rootVector n i j hij ∧
    ⁅(coroot n i j : sl n), rootVector n j i hij.symm⁆ = (-2 : ℂ) • rootVector n j i hij.symm := by
  refine ⟨opposite_bracket i j hij, ?_, ?_⟩
  · have hm := (mem_rootSpace _ _ _).mp (rootVector_mem i j hij) (coroot n i j)
    convert hm using 1; norm_num [Matrix.single, hij, hij.symm]
  · have hm := (mem_rootSpace _ _ _).mp (rootVector_mem j i hij.symm) (coroot n i j)
    convert hm using 1; norm_num [Matrix.single, hij, hij.symm]

private def diagonalPart (X : sl n) : cartan n :=
  ⟨⟨Matrix.diagonal (Matrix.diag X.val), by
      change Matrix.trace (Matrix.diagonal (Matrix.diag X.val)) = 0
      have hx : Matrix.trace X.val = 0 := X.property
      simpa only [Matrix.trace_diagonal, Matrix.trace, Matrix.diag_apply, Matrix.diagonal_apply_eq] using hx⟩,
    Matrix.isDiag_diagonal _⟩

private def entryPart (X : sl n) (a b : Fin (n+1)) : sl n :=
  if hab : a ≠ b then X.val a b • rootVector n a b hab else 0

private theorem matrix_expansion (X : sl n) :
    X = (diagonalPart X : sl n) + ∑ a, ∑ b, entryPart X a b := by
  classical
  have he (a b i j : Fin (n+1)) : (entryPart X a b).val i j =
      if a = i ∧ b = j ∧ a ≠ b then X.val a b else 0 := by
    by_cases hab : a ≠ b
    · rw [entryPart, dite_eq_left hab]
      change X.val a b * (rootVector n a b hab).val i j = _
      simp only [rootVector_apply, Matrix.single_apply]
      split_ifs <;> simp_all
    · rw [entryPart, dite_eq_right hab, ite_eq_right (by tauto)]
      rfl
  apply Subtype.ext
  ext i j
  change X.val i j = (diagonalPart X).val.val i j +
    ((sl n).subtype (∑ a, ∑ b, entryPart X a b)) i j
  rw [map_sum]
  simp only [map_sum, Matrix.sum_apply]
  change X.val i j = (diagonalPart X).val.val i j + ∑ a, ∑ b, (entryPart X a b).val i j
  simp only [he]
  by_cases hij : i = j
  · subst j
    simp [diagonalPart, ite_and]
  · simp [diagonalPart, hij, ite_and]

private theorem all_weight_spaces_span (n : ℕ) :
    (⨆ α : Module.Dual ℂ (cartan n), rootSpace (cartan n) α) = ⊤ := by
  apply top_unique
  intro X _
  rw [matrix_expansion X]
  apply Submodule.add_mem
  · apply (le_iSup (rootSpace (cartan n)) 0)
    rw [zero_space n]
    exact (diagonalPart X).property
  · apply Submodule.sum_mem
    intro a _
    apply Submodule.sum_mem
    intro b _
    dsimp only [entryPart]
    split_ifs with hab
    · apply (le_iSup (rootSpace (cartan n)) (root n a b))
      exact Submodule.smul_mem _ _ (rootVector_mem a b hab)
    · exact Submodule.zero_mem _

private theorem spaces_independent (n : ℕ) : iSupIndep (rootSpace (cartan n)) := by
  have hi := (LieSubmodule.iSupIndep_toSubmodule.mpr
    (LieModule.iSupIndep_genWeightSpace ℂ (cartan n) (sl n))).comp
      (show Function.Injective (fun α : Module.Dual ℂ (cartan n) => (α : cartan n → ℂ)) from
        DFunLike.coe_injective)
  apply hi.mono
  intro α X hX
  exact LieModule.weightSpace_le_genWeightSpace (sl n) (α : cartan n → ℂ) hX

noncomputable local instance : DecidableEq (Option (rootSet (cartan n))) := Classical.decEq _

theorem root_decomposition (n : ℕ) :
    DirectSum.IsInternal (rootSummand (cartan n)) := by
  classical
  let f : Option (rootSet (cartan n)) → Module.Dual ℂ (cartan n) :=
    fun i => i.elim 0 Subtype.val
  have hf : Function.Injective f := by
    intro i j hij
    cases i with
    | none =>
      cases j with
      | none => rfl
      | some β => exact False.elim (β.property.1 hij.symm)
    | some α =>
      cases j with
      | none => exact False.elim (α.property.1 hij)
      | some β => exact congrArg some (Subtype.ext hij)
  have he : rootSummand (cartan n) = fun i => rootSpace (cartan n) (f i) := by
    funext i
    cases i with
    | none => exact (zero_space n).symm
    | some α => rfl
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · rw [he]
    exact (spaces_independent n).comp hf
  · apply top_unique
    rw [← all_weight_spaces_span n]
    refine iSup_le fun α => ?_
    by_cases hα : α = 0
    · subst α
      rw [zero_space n]
      exact le_iSup (rootSummand (cartan n)) none
    · by_cases ha : rootSpace (cartan n) α = ⊥
      · simp [ha]
      · exact le_iSup (rootSummand (cartan n)) (some ⟨α, hα, ha⟩)

theorem coroot_coordinates (n : ℕ) (i j : Fin (n+1)) (hij : i ≠ j) :
    let α := euclideanRoot n i j
    (∑ a, α a * α a) = 2 ∧
    (fun a => (coroot n i j).val.val a a) =
      coordinateEmbedding n ((2 / (∑ a, α a * α a)) • α) := by
  dsimp only
  have hnorm : (∑ a, euclideanRoot n i j a * euclideanRoot n i j a) = 2 := by
    simp only [euclideanRoot, Pi.sub_apply, sub_mul, mul_sub]
    norm_num [Pi.single_apply, hij, hij.symm, Finset.sum_sub_distrib, eq_comm]
  refine ⟨hnorm, ?_⟩
  rw [hnorm]
  ext a
  simp only [coordinateEmbedding, euclideanRoot, Pi.single_apply, Matrix.single_apply,
    coroot_apply, LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, Complex.ofReal_sub, Complex.ofReal_mul]
  split_ifs <;> norm_num <;> aesop

/-- Evaluation at one matrix entry is a linear functional on sl. -/
def entryFunctional (a b : Fin (n+1)) : sl n →ₗ[ℂ] ℂ where
  toFun X := X.val a b
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem entryFunctional_apply (a b : Fin (n+1)) (X : sl n) :
    entryFunctional a b X = X.val a b := rfl

private noncomputable def adjointEntry (h k : cartan n) (a b : Fin (n+1)) :
    Module.End ℂ (sl n) :=
  if hab : a ≠ b then
    ((h.val.val a a - h.val.val b b) * (k.val.val a a - k.val.val b b)) •
      (entryFunctional a b).smulRight (rootVector n a b hab)
  else 0

private theorem adjoint_expansion (h k : cartan n) :
    LieAlgebra.ad ℂ (sl n) (h : sl n) * LieAlgebra.ad ℂ (sl n) (k : sl n) =
      ∑ a, ∑ b, adjointEntry h k a b := by
  classical
  have he (a b i j : Fin (n+1)) (X : sl n) :
      ((adjointEntry h k a b) X).val i j =
      if a = i ∧ b = j ∧ a ≠ b then
        (h.val.val a a - h.val.val b b) *
          (k.val.val a a - k.val.val b b) * X.val a b else 0 := by
    by_cases hab : a ≠ b
    · rw [adjointEntry, dite_eq_left hab]
      change ((h.val.val a a - h.val.val b b) * (k.val.val a a - k.val.val b b)) *
        (X.val a b * (rootVector n a b hab).val i j) = _
      simp only [rootVector_apply, Matrix.single_apply]
      split_ifs <;> simp_all [mul_assoc]
    · rw [adjointEntry, dite_eq_right hab, ite_eq_right (by tauto)]
      rfl
  ext X : 1
  apply Subtype.ext
  ext i j
  change (⁅(h : sl n), ⁅(k : sl n), X⁆⁆ : sl n).val i j = _
  rw [bracket_entry, bracket_entry]
  simp only [LinearMap.sum_apply]
  change _ = ((sl n).subtype (∑ a, ∑ b, adjointEntry h k a b X)) i j
  simp only [map_sum, Matrix.sum_apply]
  change _ = ∑ a, ∑ b, (adjointEntry h k a b X).val i j
  simp only [he]
  by_cases hij : i = j
  · subst j; simp [ite_and]
  · simp [ite_and, hij, mul_assoc]

/-- Killing form on diagonal matrices, computed as the trace of their adjoint action. -/
theorem killing_diagonal_sum (h k : cartan n) :
    killingForm ℂ (sl n) (h : sl n) (k : sl n) =
      ∑ a, ∑ b, (h.val.val a a - h.val.val b b) *
        (k.val.val a a - k.val.val b b) := by
  classical
  rw [killingForm_apply, adjoint_expansion, map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hab : a ≠ b
  · simp [adjointEntry, hab, LinearMap.trace_smulRight, Matrix.single]
  · simp [adjointEntry, not_ne_iff.mp hab]

private theorem trace_zero (h : cartan n) : (∑ a, h.val.val a a) = 0 := by
  exact h.val.property

/-- The familiar factor 2(n+1) is retained; the form is not rescaled. -/
theorem killing_diagonal (h k : cartan n) :
    killingForm ℂ (sl n) (h : sl n) (k : sl n) =
      (2 * (n+1) : ℂ) * ∑ a, h.val.val a a * k.val.val a a := by
  rw [killing_diagonal_sum]
  simp_rw [sub_mul, mul_sub]
  simp only [Finset.sum_sub_distrib]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  simp only [trace_zero, mul_zero, zero_mul, sub_zero, zero_sub,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one]
  have he : (∑ x, h.val.val x x * (((n : ℂ)+1) * k.val.val x x)) =
      ((n : ℂ)+1) * ∑ x, h.val.val x x * k.val.val x x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [he]
  ring

private theorem rank_factor_ne_zero : (2 * (n+1) : ℂ) ≠ 0 := by
  apply mul_ne_zero (by norm_num)
  exact_mod_cast Nat.succ_ne_zero n

theorem killing_coroot_pairing (i j : Fin (n+1)) (h : cartan n) :
    killingForm ℂ (sl n) (coroot n i j : sl n) (h : sl n) =
      (2 * (n+1) : ℂ) * root n i j h := by
  rw [killing_diagonal]
  simp [Matrix.single_apply, sub_mul, Finset.sum_sub_distrib]

private theorem cartan_killing_nondegenerate (n : ℕ) :
    ((killingForm ℂ (sl n)).restrict (cartan n).toSubmodule).Nondegenerate := by
  let B := (killingForm ℂ (sl n)).restrict (cartan n).toSubmodule
  have hs : ∀ x : cartan n, (∀ y : cartan n, B x y = 0) → x = 0 := by
    intro x hx
    have he (i j : Fin (n+1)) : x.val.val i i = x.val.val j j := by
      have hh := hx (coroot n i j)
      change killingForm ℂ (sl n) (x : sl n) (coroot n i j : sl n) = 0 at hh
      rw [killingForm_symmetric, killing_coroot_pairing] at hh
      exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left rank_factor_ne_zero)
    have hz : x.val.val 0 0 = 0 := by
      have ht := trace_zero x
      simp_rw [he _ 0] at ht
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at ht
      exact (mul_eq_zero.mp ht).resolve_left (by exact_mod_cast Nat.succ_ne_zero n)
    apply Subtype.ext
    apply Subtype.ext
    ext a b
    by_cases hab : a = b
    · subst b
      exact (he a 0).trans hz
    · exact x.property hab
  refine ⟨hs, ?_⟩
  intro x hx
  apply hs x
  intro y
  change killingForm ℂ (sl n) (x : sl n) (y : sl n) = 0
  rw [killingForm_symmetric]
  exact hx y

/-- The explicit coroot equals the original Killing-normalized coroot. -/
theorem killing_coroot (n : ℕ) (i j : Fin (n+1)) (hij : i ≠ j) :
    Specs.LieAlgebrasAndRepresentations.RootForm.coroot_value (cartan n) (root n i j) =
      coroot n i j := by
  classical
  let B := (killingForm ℂ (sl n)).restrict (cartan n).toSubmodule
  let c : ℂ := 2 * (n+1)
  have hc : c ≠ 0 := rank_factor_ne_zero
  have hB : B.Nondegenerate := cartan_killing_nondegenerate n
  let t : cartan n := c⁻¹ • coroot n i j
  have ht (h : cartan n) : B t h = root n i j h := by
    change killingForm ℂ (sl n) (c⁻¹ • (coroot n i j : sl n)) (h : sl n) = _
    rw [map_smul, LinearMap.smul_apply, killing_coroot_pairing]
    change c⁻¹ * (c * root n i j h) = _
    rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  have hte : Specs.LieAlgebrasAndRepresentations.RootForm.tAlpha_value
      (cartan n) (root n i j) = t := by
    unfold Specs.LieAlgebrasAndRepresentations.RootForm.tAlpha_value
      Specs.LieAlgebrasAndRepresentations.RootForm.rootDualMap_value
    change (if h : B.Nondegenerate then (B.toDual h).symm.toLinearMap else 0) (root n i j) = t
    rw [dite_eq_left hB]
    apply (B.toDual hB).injective
    ext h
    change (B.toDual hB) ((B.toDual hB).symm (root n i j)) h = B t h
    rw [LinearEquiv.apply_symm_apply, ht]
  have hself : root n i j (coroot n i j) = 2 := by
    norm_num [Matrix.single_apply, hij, hij.symm]
  have hform : Specs.LieAlgebrasAndRepresentations.RootForm.rootForm_value
      (cartan n) (root n i j) (root n i j) = c⁻¹ * 2 := by
    change B (Specs.LieAlgebrasAndRepresentations.RootForm.tAlpha_value _ _)
      (Specs.LieAlgebrasAndRepresentations.RootForm.tAlpha_value _ _) = _
    rw [hte, ht]
    change root n i j (c⁻¹ • coroot n i j) = _
    rw [map_smul, smul_eq_mul, hself]
  unfold Specs.LieAlgebrasAndRepresentations.RootForm.coroot_value
  rw [hform, hte]
  change (2 / (c⁻¹ * 2)) • (c⁻¹ • coroot n i j) = _
  rw [smul_smul]
  have hscalar : 2 / (c⁻¹ * 2) * c⁻¹ = 1 := by field_simp
  rw [hscalar, one_smul]

theorem root_coordinates (n : ℕ) (i j : Fin (n+1)) (h : cartan n) :
    (∑ a, coordinateEmbedding n (euclideanRoot n i j) a * h.val.val a a) = root n i j h := by
  have he (a : Fin (n+1)) : coordinateEmbedding n (euclideanRoot n i j) a =
      (if a = i then (1 : ℂ) else 0) - (if a = j then 1 else 0) := by
    change ((((Pi.single i (1 : ℝ) - Pi.single j 1) : Fin (n+1) → ℝ) a) : ℂ) = _
    simp only [Pi.sub_apply, Pi.single_apply]
    split_ifs <;> norm_num
  simp_rw [he, sub_mul, ite_mul]
  simp [Finset.sum_sub_distrib]

end LieAlgebrasAndRepresentations.ClassicalRootsA
