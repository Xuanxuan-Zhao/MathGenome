import MathGenome.Internal.Specs.D05.M11.Hermitian.TriangularGram
import MathGenome.Internal.D05.M11.Hermitian.TriangularGram.FlagProjection
import MathGenome.Internal.D05.M11.Hermitian
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Basis.Flag

noncomputable section
namespace D05.M11.Hermitian.TriangularGram
open Module Matrix
open scoped BigOperators
open Specs.D05.M11.Hermitian
open Specs.D05.M11.Hermitian.TriangularGram
open Specs.D05.M11.Hermitian.TriangularGram.FlagProjection

variable {K V : Type*} [RCLike K] [AddCommGroup V] [Module K V] {n : ℕ}

lemma flag_eq_basis_flag (e : Basis (Fin n) K V) (k : Fin (n+1)) :
    flag e k = e.flag k := by
  unfold flag Basis.flag
  congr 1
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨Fin.castLE (Nat.le_of_lt_succ k.isLt) i, i.isLt, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i.val, hi⟩, congrArg e (Fin.ext rfl)⟩

lemma mem_flag_iff (e : Basis (Fin n) K V) (k : Fin (n+1)) (x : V) :
    x ∈ flag e k ↔ ∀ i : Fin n, k.val ≤ i.val → e.repr x i = 0 := by
  rw [flag_eq_basis_flag, e.mem_flag_iff_repr_eq_zero]
  rfl

@[simp] lemma repr_columns (e : Basis (Fin n) K V)
    (P : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    e.repr (columns e P j) i = P i j := by
  classical
  simp [columns, map_sum, map_smul, Finsupp.single_apply]

theorem gram_of_columns : Specs.D05.M11.Hermitian.TriangularGram.gram_of_columns := by
  intro K V _ _ _ n e B P i j
  rw [D05.M11.Hermitian.matrix_formula e B]
  simp only [repr_columns]
  simp only [gramTransform, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

lemma unitUpper_iff (e : Basis (Fin n) K V) (P : Matrix (Fin n) (Fin n) K) :
    UnitUpper P ↔ ∀ j, columns e P j - e j ∈ flag e j.castSucc := by
  classical
  simp only [mem_flag_iff, map_sub, Finsupp.sub_apply, repr_columns, Basis.repr_self,
    Finsupp.single_apply]
  constructor
  · rintro ⟨hu, hd⟩ j i hi
    by_cases hij : i = j
    · subst i; simp [hd]
    · rw [ite_eq_right (Ne.symm hij), hu i j (lt_of_le_of_ne hi (Ne.symm hij)), sub_zero]
  · intro h
    constructor
    · intro i j hij
      simpa [ne_of_gt hij, ne_of_lt hij] using h j i (le_of_lt hij)
    · intro i
      exact sub_eq_zero.mp (by simpa using h i i le_rfl)

lemma det_unitUpper {P : Matrix (Fin n) (Fin n) K} (h : UnitUpper P) : P.det = 1 := by
  rw [Matrix.det_of_isUpperTriangular h.1]
  simp [h.2]

/-- Prefix spans for any family with the prescribed leading coefficient one. -/
lemma prefix_span_eq (e : Basis (Fin n) K V) (v : Fin n → V)
    (hv : ∀ j, v j - e j ∈ flag e j.castSucc) (k : Fin (n+1)) :
    Submodule.span K (v '' {i | i.castSucc < k}) = flag e k := by
  simp_rw [flag_eq_basis_flag] at hv ⊢
  induction k using Fin.induction with
  | zero => simp
  | succ j ih =>
    have hspan : Submodule.span K (v '' {i | i.castSucc < j.succ}) =
        K ∙ v j ⊔ Submodule.span K (v '' {i | i.castSucc < j.castSucc}) := by
      simp [Fin.castSucc_lt_castSucc_iff, le_iff_eq_or_lt, Set.ofPred_or,
        Submodule.span_insert]
    rw [hspan, ih, Basis.flag_succ]
    apply le_antisymm
    · apply sup_le _ le_sup_right
      rw [Submodule.span_singleton_le_iff_mem]
      have he : e j ∈ K ∙ e j ⊔ e.flag j.castSucc :=
        (le_sup_left : K ∙ e j ≤ K ∙ e j ⊔ e.flag j.castSucc)
          (Submodule.mem_span_singleton_self (e j))
      have hd := (le_sup_right : e.flag j.castSucc ≤ K ∙ e j ⊔ e.flag j.castSucc) (hv j)
      simpa using (K ∙ e j ⊔ e.flag j.castSucc).add_mem hd he
    · apply sup_le _ le_sup_right
      rw [Submodule.span_singleton_le_iff_mem]
      have he : v j ∈ K ∙ v j ⊔ e.flag j.castSucc :=
        (le_sup_left : K ∙ v j ≤ K ∙ v j ⊔ e.flag j.castSucc)
          (Submodule.mem_span_singleton_self (v j))
      have hd := (le_sup_right : e.flag j.castSucc ≤ K ∙ v j ⊔ e.flag j.castSucc) (hv j)
      simpa using (K ∙ v j ⊔ e.flag j.castSucc).sub_mem he hd

lemma columns_mem_flag (e : Basis (Fin n) K V) (v : Fin n → V)
    (hv : ∀ j, v j - e j ∈ flag e j.castSucc) {i j : Fin n} (hij : i < j) :
    v i ∈ flag e j.castSucc := by
  have hm : flag e i.castSucc ≤ flag e j.castSucc := by
    simp_rw [flag_eq_basis_flag]
    exact e.flag_mono (le_of_lt (Fin.castSucc_lt_castSucc_iff.mpr hij))
  have he : e i ∈ flag e j.castSucc := by
    rw [flag_eq_basis_flag]
    exact e.self_mem_flag (Fin.castSucc_lt_castSucc_iff.mpr hij)
  simpa using (flag e j.castSucc).add_mem (hm (hv i)) he

theorem exists_unique : Specs.D05.M11.Hermitian.TriangularGram.exists_unique := by
  intro K V _ _ _ n e B h
  classical
  obtain ⟨E, _, _, _, hr⟩ := FlagProjection.flag_projections e B h
  let v : Fin n → V := fun j => e j - E j.castSucc (e j)
  have hv : ∀ j, v j - e j ∈ flag e j.castSucc := fun j => (hr j).1
  let P : Matrix (Fin n) (Fin n) K := fun i j => e.repr (v j) i
  have hc : ∀ j, columns e P j = v j := fun j => e.sum_repr (v j)
  refine ⟨P, ⟨(unitUpper_iff e P).mpr (by simpa only [hc] using hv), ?_⟩, ?_⟩
  · intro i j hij
    rw [← gram_of_columns e B, hc, hc]
    exact (hr j).2.1 (v i) (columns_mem_flag e v hv hij)
  · intro Q hQ
    have hq := (unitUpper_iff e Q).mp hQ.1
    have hcol : ∀ j, columns e Q j = v j := by
      intro j
      apply (hr j).2.2 _ (hq j)
      intro w hw
      have hs : flag e j.castSucc ≤ (B.flip (columns e Q j)).ker := by
        rw [← prefix_span_eq e (columns e Q) hq j.castSucc]
        apply Submodule.span_le.mpr
        rintro _ ⟨i, hi, rfl⟩
        change B (columns e Q i) (columns e Q j) = 0
        rw [gram_of_columns e B]
        exact hQ.2 i j hi
      exact hs hw
    ext i j
    simpa only [repr_columns] using congrArg (fun x => e.repr x i) (hcol j)

theorem solution_basis : Specs.D05.M11.Hermitian.TriangularGram.solution_basis := by
  intro K V _ _ _ n e B P hP hL
  have hd := det_unitUpper hP
  have hu : IsUnit P.det := hd ▸ isUnit_one
  let f : V ≃ₗ[K] V := Matrix.toLinOfInv e e
    (Matrix.mul_nonsing_inv P hu) (Matrix.nonsing_inv_mul P hu)
  let v := e.map f
  have hv : ∀ j, v j = columns e P j := by
    intro j
    change P.toLin e e (e j) = _
    exact Matrix.toLin_self e e P j
  refine ⟨hd, (Matrix.isUnit_iff_isUnit_det P).mpr hu, v, hv, ?_, ?_⟩
  · simpa only [hv] using (unitUpper_iff e P).mp hP
  · intro i j hij
    rw [hv, hv, gram_of_columns e B]
    exact hL i j hij

theorem convention_bridge : Specs.D05.M11.Hermitian.TriangularGram.convention_bridge := by
  intro K _ n H
  have ht : ∀ P, (gramTransform H P)ᵀ = P.conjTranspose * Hᵀ * P := by
    intro P
    simp only [gramTransform, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.conjTranspose, Matrix.transpose_map, Matrix.mul_assoc]
  refine ⟨ht, ?_, ?_⟩
  · intro k
    exact Matrix.det_transpose _
  · have he : ∀ P, Lower (gramTransform H P) ↔
        Upper (P.conjTranspose * Hᵀ * P) := by
      intro P
      rw [← ht P]
      exact ⟨fun h i j hij => h j i hij, fun h i j hij => h j i hij⟩
    simp_rw [he]

theorem real_convention_bridge :
    Specs.D05.M11.Hermitian.TriangularGram.real_convention_bridge := by
  intro n H
  have hg : ∀ P : Matrix (Fin n) (Fin n) ℝ, gramTransform H P = Pᵀ * H * P := by
    intro P
    have hs : P.map star = P := by ext i j; simp
    rw [gramTransform, hs]
  refine ⟨Matrix.conjTranspose_eq_transpose_of_trivial, ?_, ?_⟩
  · simpa only [hg, Matrix.conjTranspose_eq_transpose_of_trivial] using
      (convention_bridge H).1
  · simpa only [hg, Matrix.conjTranspose_eq_transpose_of_trivial] using
      (convention_bridge H).2.2

theorem hoffman_kunze : Specs.D05.M11.Hermitian.TriangularGram.hoffman_kunze := by
  intro K V _ _ _ n e B h
  exact (convention_bridge (formMatrix_value e B)).2.2.mp (exists_unique e B h)

/-- Over R the same underlying bilinear function has the sesquilinear type. -/
def realSesquilinear {V : Type*} [AddCommGroup V] [Module ℝ V] (B : LinearMap.BilinForm ℝ V) :
    V →ₗ[ℝ] V →ₗ⋆[ℝ] ℝ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℝ) (starRingEnd ℝ) (fun x y => B x y)
    (fun x x' y => B.map_add₂ x x' y)
    (fun a x y => by simp)
    (fun x y y' => (B x).map_add y y')
    (fun a x y => by simp)

lemma real_transform {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (e : Basis (Fin n) ℝ V) (B : LinearMap.BilinForm ℝ V)
    (P : Matrix (Fin n) (Fin n) ℝ) :
    gramTransform (formMatrix_value e (realSesquilinear B)) P =
      Pᵀ * Matrix.of (fun i j => B (e i) (e j)) * P := by
  have hm : formMatrix_value e (realSesquilinear B) =
      Matrix.of (fun i j => B (e i) (e j)) := rfl
  have hs : P.map star = P := by ext i j; simp
  rw [gramTransform, hm, hs]

theorem real_bilinear : Specs.D05.M11.Hermitian.TriangularGram.real_bilinear := by
  intro V _ _ n e B h
  have hb : LeadingNonzero e (realSesquilinear B) := h
  simpa only [real_transform] using exists_unique e (realSesquilinear B) hb

theorem real_solution_basis : Specs.D05.M11.Hermitian.TriangularGram.real_solution_basis := by
  intro V _ _ n e B P hu hl
  apply solution_basis e (realSesquilinear B) P hu
  simpa only [real_transform] using hl

theorem empty_case : Specs.D05.M11.Hermitian.TriangularGram.empty_case := by
  intro K _ H
  have hu : UnitUpper (1 : Matrix (Fin 0) (Fin 0) K) :=
    ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  refine ⟨⟨1, ⟨hu, fun i => Fin.elim0 i⟩, fun P _ => Subsingleton.elim _ _⟩,
    fun P => ⟨Subsingleton.elim _ _, Matrix.det_isEmpty⟩, ?_⟩
  intro k
  simp

theorem hermitian_specialization :
    Specs.D05.M11.Hermitian.TriangularGram.hermitian_specialization := by
  intro K V _ _ _ n e B P hB hL
  have hs : ∀ i j, gramTransform (formMatrix_value e B) P j i =
      star (gramTransform (formMatrix_value e B) P i j) := by
    intro i j
    rw [← gram_of_columns e B, ← gram_of_columns e B]
    exact hB _ _
  constructor
  · intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hL i j h
    · rw [hs, hL j i h, star_zero]
  · intro i
    exact RCLike.conj_eq_iff_real.mp (hs i i).symm

theorem real_symmetric_specialization :
    Specs.D05.M11.Hermitian.TriangularGram.real_symmetric_specialization := by
  intro V _ _ n e B P hB hL
  have hb : isHermitian_value (realSesquilinear B) := by
    intro x y
    simpa [realSesquilinear] using hB x y
  have hl : Lower (gramTransform (formMatrix_value e (realSesquilinear B)) P) := by
    simpa only [real_transform] using hL
  simpa only [real_transform] using
    (hermitian_specialization e (realSesquilinear B) P hb hl).1

end D05.M11.Hermitian.TriangularGram
