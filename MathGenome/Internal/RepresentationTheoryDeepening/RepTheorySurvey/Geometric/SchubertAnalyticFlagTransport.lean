import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.SchubertAnalyticFlagTransport
import Batteries.Tactic.OpenPrivate
import Mathlib.LinearAlgebra.Matrix.Bilinear
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Topology.Algebra.Affine
import Mathlib.Topology.LocalAtTarget

namespace RepTheorySurvey.Geometric.SchubertAnalyticFlagTransport

open AlgebraicGeometry CategoryTheory Set Topology
open LinearAlgebraicGroups (Points SchemeOver)
open LinearAlgebraicGroups.Specs.GrassmannianCharts
open LatticeModelSpecs SchubertAnalyticFlagTransportSpecs
open scoped Matrix.Norms.Elementwise

noncomputable section

section Charts

open Matrix

variable {V ι : Type} [AddCommGroup V] [Module ℂ V] [Fintype ι] [DecidableEq ι]
variable {d : ℕ}

private theorem chartPoint_injective (b : Module.Basis ι ℂ V)
    (hd : d ≤ Module.finrank ℂ V) (I : Pivot ι d) :
    Function.Injective (grassmannianChartPoint b hd I) := by
  let h := (grassmannianCharts b hd).openChart I
  let : Mono ((grassmannianCharts b hd).chart I).left := inferInstance
  let : Mono ((grassmannianCharts b hd).chart I) := Over.mono_of_mono_left _
  intro A B hAB
  exact (LinearAlgebraicGroups.GrassmannianCharts.chartMatrixEquiv I complexAlgebra).symm.injective
    ((cancel_mono _).mp hAB)

private theorem chartPoint_continuous (b : Module.Basis ι ℂ V)
    (hd : d ≤ Module.finrank ℂ V) (I : Pivot ι d) :
    Continuous (grassmannianChartPoint b hd I) := by
  apply continuous_iff_coinduced_le.mpr
  change _ ≤ ⨆ J : Pivot ι d, TopologicalSpace.coinduced
    (grassmannianChartPoint b hd J) inferInstance
  exact le_iSup (fun J ↦ TopologicalSpace.coinduced (grassmannianChartPoint b hd J) inferInstance) I

private theorem matrix_range_reindex_columns {ι κ ξ : Type}
    [Fintype κ] [Fintype ξ] (C : Matrix ι κ ℂ) (e : ξ ≃ κ) :
    ((C.submatrix id e).mulVecLin).range = C.mulVecLin.range := by
  have hid : LinearMap.funLeft ℂ ℂ (id : ι → ι) = LinearMap.id :=
    LinearMap.ext fun _ ↦ rfl
  have hs : Function.Surjective (LinearMap.funLeft ℂ ℂ e.symm) :=
    (LinearEquiv.funCongrLeft ℂ ℂ e.symm).surjective
  rw [Matrix.mulVecLin_submatrix, hid, LinearMap.id_comp,
    LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hs)]

private def pivotRows (J : Pivot ι d) (C : Matrix ι (Inside J) ℂ) :
    Matrix (Inside J) (Inside J) ℂ := C.submatrix Subtype.val id

private def normalizeGraph (J : Pivot ι d) (C : Matrix ι (Inside J) ℂ) :
    Matrix (Outside J) (Inside J) ℂ := C.submatrix Subtype.val id * (pivotRows J C)⁻¹

omit [Fintype ι] in
private theorem normalizeGraph_range (J : Pivot ι d) (C : Matrix ι (Inside J) ℂ)
    (h : IsUnit (pivotRows J C).det) :
    (graphMatrix J (normalizeGraph J C)).mulVecLin.range = C.mulVecLin.range := by
  have he : graphMatrix J (normalizeGraph J C) = C * (pivotRows J C)⁻¹ := by
    ext i j
    by_cases hi : i ∈ J.val
    · have hm := congrFun (congrFun
        (Matrix.mul_nonsing_inv (pivotRows J C) h) (⟨i, hi⟩ : Inside J)) j
      change (C * (pivotRows J C)⁻¹) i j = (1 : Matrix (Inside J) (Inside J) ℂ) ⟨i, hi⟩ j at hm
      rw [hm, Matrix.one_apply, graphMatrix, Matrix.of_apply, dite_eq_left hi]
      simp only [Subtype.ext_iff]
    · simp only [graphMatrix, Matrix.of_apply, dite_eq_right hi]
      rfl
  rw [he]
  change (Matrix.toLin' (C * (pivotRows J C)⁻¹)).range = _
  have hs : Function.Surjective ((pivotRows J C)⁻¹).mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_nonsing_inv_det _ h))
  have htop : (Matrix.toLin' ((pivotRows J C)⁻¹)).range = ⊤ := LinearMap.range_eq_top.mpr hs
  rw [Matrix.toLin'_mul, LinearMap.range_comp_of_range_eq_top _ htop]
  rfl

omit [Fintype ι] in
private theorem isUnit_pivotRows_of_range (J : Pivot ι d) (C : Matrix ι (Inside J) ℂ)
    (A : Matrix (Outside J) (Inside J) ℂ)
    (h : C.mulVecLin.range = (graphMatrix J A).mulVecLin.range) :
    IsUnit (pivotRows J C).det := by
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_surjective_iff_isUnit.mp
  intro u
  have hv : (graphMatrix J A *ᵥ u) ∈ C.mulVecLin.range := by
    rw [h]
    exact ⟨u, rfl⟩
  obtain ⟨x, hx⟩ := hv
  refine ⟨x, funext fun j ↦ ?_⟩
  change (C *ᵥ x) j.val = u j
  exact (congrFun hx j.val).trans (graphMatrix_inside J A u j)

private theorem analyticAt_matrix_det {E κ : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [Fintype κ] [DecidableEq κ] {C : E → Matrix κ κ ℂ} {x : E}
    (h : ∀ i j, AnalyticAt ℂ (fun a ↦ C a i j) x) :
    AnalyticAt ℂ (fun a ↦ (C a).det) x := by
  simp only [Matrix.det_apply']
  apply Finset.analyticAt_fun_sum
  intro σ _
  apply analyticAt_const.mul
  exact Finset.analyticAt_fun_prod _ (fun i _ ↦ h (σ i) i)

private theorem analyticAt_normalizeGraph {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (J : Pivot ι d) {C : E → Matrix ι (Inside J) ℂ} {x : E}
    (h : ∀ i j, AnalyticAt ℂ (fun a ↦ C a i j) x)
    (hn : (pivotRows J (C x)).det ≠ 0) :
    AnalyticAt ℂ (fun a ↦ normalizeGraph J (C a)) x := by
  let D := fun a ↦ pivotRows J (C a)
  have hD (i j : Inside J) : AnalyticAt ℂ (fun a ↦ D a i j) x := h i.val j
  have hi (i j : Inside J) : AnalyticAt ℂ (fun a ↦ ((D a)⁻¹) i j) x := by
    simp only [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv, smul_eq_mul]
    apply ((analyticAt_matrix_det hD).inv hn).mul
    simp only [Matrix.adjugate_apply]
    apply analyticAt_matrix_det
    intro k l
    by_cases hk : k = j
    · subst k
      simp only [Matrix.updateRow_self]
      exact analyticAt_const
    · simp only [Matrix.updateRow_ne hk]
      exact hD k l
  change AnalyticAt ℂ (fun a (i : Outside J) (j : Inside J) ↦ normalizeGraph J (C a) i j) x
  apply AnalyticAt.pi
  intro i
  apply AnalyticAt.pi
  intro j
  simp only [normalizeGraph, Matrix.mul_apply, Matrix.submatrix_apply, id_eq]
  exact Finset.analyticAt_fun_sum _ (fun k _ ↦ (h i.val k).mul (hi k j))

set_option maxHeartbeats 800000 in
theorem graphChartAnalyticTransitions : GraphChartAnalyticTransitions := by
  intro V ι _ _ _ _ b d hd I J
  let e : Inside J ≃ Inside I := (pivotOrder J).trans (pivotOrder I).symm
  let C (A : Matrix (Outside I) (Inside I) ℂ) := (graphMatrix I A).submatrix id e
  let D (A : Matrix (Outside I) (Inside I) ℂ) := pivotRows J (C A)
  let F (A : Matrix (Outside I) (Inside I) ℂ) := normalizeGraph J (C A)
  have hC (A : Matrix (Outside I) (Inside I) ℂ) :
      (C A).mulVecLin.range = (graphMatrix I A).mulVecLin.range :=
    matrix_range_reindex_columns _ e
  have hnorm (A : Matrix (Outside I) (Inside I) ℂ) (hA : (D A).det ≠ 0) :
      grassmannianChartPoint b hd J (F A) = grassmannianChartPoint b hd I A := by
    apply grassmannianSubspace_injective b hd
    apply Submodule.map_injective_of_injective b.equivFun.injective
    rw [grassmannianChartSubspace, grassmannianChartSubspace]
    exact (normalizeGraph_range J (C A) (isUnit_iff_ne_zero.mpr hA)).trans (hC A)
  have hU : grassmannianChartPoint b hd I ⁻¹' Set.range (grassmannianChartPoint b hd J) =
      {A | (D A).det ≠ 0} := by
    ext A
    constructor
    · rintro ⟨B, hB⟩
      apply IsUnit.ne_zero
      apply isUnit_pivotRows_of_range J (C A) B
      have he := congrArg (fun p ↦ (grassmannianSubspace b hd p).map b.equivFun.toLinearMap) hB
      rw [grassmannianChartSubspace, grassmannianChartSubspace] at he
      exact (hC A).trans he.symm
    · intro hA
      exact ⟨F A, hnorm A hA⟩
  have hC' (A : Matrix (Outside I) (Inside I) ℂ) (i : ι) (j : Inside J) :
      AnalyticAt ℂ (fun z ↦ C z i j) A := by
    simp only [C, Matrix.submatrix_apply, id_eq, graphMatrix, Matrix.of_apply]
    by_cases hi : i ∈ I.val
    · simp only [dite_eq_left hi]
      exact analyticAt_const
    · simp only [dite_eq_right hi]
      exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Inside I ↦ ℂ) (e j)).analyticAt _).comp
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Outside I ↦ Inside I → ℂ)
          ⟨i, hi⟩).analyticAt _)
  change IsOpen _ ∧ ∃ F', AnalyticOnNhd ℂ F' _ ∧ _
  rw [hU]
  refine ⟨isOpen_ne.preimage ?_, F, fun A hA ↦ ?_, hnorm⟩
  · exact continuous_iff_continuousAt.mpr fun A ↦
      (analyticAt_matrix_det (C := D) (fun i j ↦ hC' A i.val j)).continuousAt
  · exact analyticAt_normalizeGraph J (hC' A) hA

theorem graphChartOpenEmbeddings : GraphChartOpenEmbeddings := by
  intro V ι _ _ _ _ b d hd I
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
    (chartPoint_continuous b hd I) (chartPoint_injective b hd I)
  intro s hs
  change @IsOpen _ (⨆ J : Pivot ι d, TopologicalSpace.coinduced
    (grassmannianChartPoint b hd J) inferInstance) _
  rw [isOpen_iSup_iff]
  intro J
  rw [isOpen_coinduced]
  obtain ⟨hU, F, hF, htransition⟩ := graphChartAnalyticTransitions b hd J I
  have he : grassmannianChartPoint b hd J ⁻¹' (grassmannianChartPoint b hd I '' s) =
      (grassmannianChartPoint b hd J ⁻¹' Set.range (grassmannianChartPoint b hd I)) ∩ F ⁻¹' s := by
    ext A
    constructor
    · rintro ⟨B, hB, he⟩
      have hA : grassmannianChartPoint b hd J A ∈ Set.range (grassmannianChartPoint b hd I) :=
        ⟨B, he⟩
      refine ⟨hA, ?_⟩
      have hFB := chartPoint_injective b hd I ((htransition A hA).trans he.symm)
      change F A ∈ s
      rwa [hFB]
    · rintro ⟨hA, hFA⟩
      exact ⟨F A, hFA, htransition A hA⟩
  rw [he]
  exact hF.continuousOn.isOpen_inter_preimage hU hs

set_option maxHeartbeats 900000 in
/-- A continuously varying spanning family of fixed rank is continuous in graph coordinates. -/
private theorem continuous_of_spanning_matrices {X κ : Type} [TopologicalSpace X] [Fintype κ]
    (b : Module.Basis ι ℂ V) (hd : d ≤ Module.finrank ℂ V)
    (f : X → GrassmannianPoints b hd) (C : X → Matrix ι κ ℂ) (hC : Continuous C)
    (hr : ∀ x, (grassmannianSubspace b hd (f x)).map b.equivFun.toLinearMap =
      (C x).mulVecLin.range) :
    Continuous f := by
  classical
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨J, A, hA⟩ := grassmannianChartPoint_cover b hd (f x)
  let P : (ι → ℂ) →ₗ[ℂ] (Inside J → ℂ) := LinearMap.funLeft ℂ ℂ Subtype.val
  have he : (C x).mulVecLin.range = (graphMatrix J A).mulVecLin.range := by
    rw [← hr, ← hA, grassmannianChartSubspace]
    rfl
  have hsurj : Function.Surjective (P.comp (C x).mulVecLin) := by
    intro u
    have hu : graphMatrix J A *ᵥ u ∈ (C x).mulVecLin.range := by
      rw [he]
      exact ⟨u, rfl⟩
    obtain ⟨v, hv⟩ := hu
    refine ⟨v, funext fun j ↦ ?_⟩
    exact (congrFun hv j.val).trans (graphMatrix_inside J A u j)
  obtain ⟨r, hright⟩ := (P.comp (C x).mulVecLin).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hsurj)
  let R := LinearMap.toMatrix' r
  let D (y : X) := C y * R
  have hD : Continuous D := hC.matrix_mul continuous_const
  have hrow : pivotRows J (D x) = 1 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_one]
    change P.comp (Matrix.toLin' (D x)) = _
    rw [show D x = C x * R from rfl, Matrix.toLin'_mul, Matrix.toLin'_toMatrix',
      ← LinearMap.comp_assoc]
    exact hright
  have hdet : Continuous (fun y ↦ (pivotRows J (D y)).det) :=
    (hD.matrix_submatrix _ _).matrix_det
  have hunit : (pivotRows J (D x)).det ≠ 0 := by simp [hrow]
  have hN : ContinuousAt (fun y ↦ normalizeGraph J (D y)) x := by
    have hInv : ContinuousAt (fun y ↦ (pivotRows J (D y))⁻¹) x := by
      apply (continuousAt_matrix_inv _ ?_).comp
        (hD.matrix_submatrix (fun j : Inside J ↦ j.val) id).continuousAt
      rw [show (Ring.inverse : ℂ → ℂ) = Inv.inv from funext Ring.inverse_eq_inv]
      exact continuousAt_inv₀ hunit
    let M₁ := Matrix (Outside J) (Inside J) ℂ
    let M₂ := Matrix (Inside J) (Inside J) ℂ
    have hc : Continuous (fun p : M₁ × M₂ ↦ p.1 * p.2) :=
      continuous_fst.matrix_mul continuous_snd
    exact hc.continuousAt.comp
      ((hD.matrix_submatrix (fun j : Outside J ↦ j.val) id).continuousAt.prodMk hInv)
  apply ((chartPoint_continuous b hd J).continuousAt.comp hN).congr_of_eventuallyEq
  filter_upwards [hdet.continuousAt.eventually_ne hunit] with y hy
  apply grassmannianSubspace_injective b hd
  apply Submodule.map_injective_of_injective b.equivFun.injective
  simp only [Function.comp_apply]
  rw [hr, grassmannianChartSubspace, Matrix.toLin'_apply',
    normalizeGraph_range J (D y) (isUnit_iff_ne_zero.mpr hy)]
  symm
  apply Submodule.eq_of_le_of_finrank_le
  · change (Matrix.toLin' (C y * R)).range ≤ _
    rw [Matrix.toLin'_mul]
    exact LinearMap.range_comp_le_range _ _
  · have hdim : Module.finrank ℂ (C y).mulVecLin.range = d := by
      rw [← hr]
      exact ((grassmannianSubspace b hd (f y)).equivMapOfInjective _
        b.equivFun.injective).finrank_eq.symm.trans (grassmannianSubspace_finrank b hd (f y))
    let F := normalizeGraph J (D y)
    have hh := grassmannianChartSubspace b hd J F
    rw [Matrix.toLin'_apply', normalizeGraph_range J (D y) (isUnit_iff_ne_zero.mpr hy)] at hh
    have hd' : Module.finrank ℂ (D y).mulVecLin.range = d := by
      rw [← hh]
      exact ((grassmannianSubspace b hd (grassmannianChartPoint b hd J F)).equivMapOfInjective
        _ b.equivFun.injective).finrank_eq.symm.trans
          (grassmannianSubspace_finrank b hd (grassmannianChartPoint b hd J F))
    exact (hdim.trans hd'.symm).le

omit [Fintype ι] in
private theorem continuous_graphMatrix (I : Pivot ι d) :
    Continuous (graphMatrix I : Matrix (Outside I) (Inside I) ℂ → Matrix ι (Inside I) ℂ) := by
  apply continuous_matrix
  intro i j
  simp only [graphMatrix, Matrix.of_apply]
  by_cases hi : i ∈ I.val
  · simp only [dite_eq_left hi]
    exact continuous_const
  · simp only [dite_eq_right hi]
    exact continuous_apply_apply (⟨i, hi⟩ : Outside I) j

end Charts

section Flags

open Matrix

private def graphVariation {ι : Type} [DecidableEq ι] {d : ℕ} (I : Pivot ι d) :
    Matrix (Outside I) (Inside I) ℂ →ₗ[ℂ] Matrix ι (Inside I) ℂ where
  toFun M := Matrix.of fun i j ↦ if hi : i ∈ I.val then 0 else M ⟨i, hi⟩ j
  map_add' M N := by
    ext i j
    by_cases hi : i ∈ I.val <;> simp [hi]
  map_smul' c M := by
    ext i j
    by_cases hi : i ∈ I.val <;> simp [hi]

private theorem graphMatrix_eq_variation_add {ι : Type} [DecidableEq ι]
    {d : ℕ} (I : Pivot ι d) (M : Matrix (Outside I) (Inside I) ℂ) :
    graphMatrix I M = graphVariation I M + graphMatrix I (0 : Matrix (Outside I) (Inside I) ℂ) := by
  ext i j
  have hv : graphVariation I M i j = (if hi : i ∈ I.val then 0 else M ⟨i, hi⟩ j) := rfl
  rw [Matrix.add_apply, hv]
  by_cases hi : i ∈ I.val <;> simp [graphMatrix, hi]

private theorem graphMatrix_mem_range {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (I : Pivot ι d) (M : Matrix (Outside I) (Inside I) ℂ) (v : ι → ℂ) :
    v ∈ (graphMatrix I M).mulVecLin.range ↔
      (fun j : Outside I ↦ v j.val) = M *ᵥ (fun i : Inside I ↦ v i.val) := by
  constructor
  · rintro ⟨u, rfl⟩
    funext j
    simp only [Matrix.mulVecLin_apply, graphMatrix_inside, graphMatrix_outside]
  · intro h
    refine ⟨fun i : Inside I ↦ v i.val, funext fun j ↦ ?_⟩
    change (graphMatrix I M *ᵥ (fun i : Inside I ↦ v i.val)) j = v j
    by_cases hj : j ∈ I.val
    · exact graphMatrix_inside I M _ ⟨j, hj⟩
    · exact (graphMatrix_outside I M _ ⟨j, hj⟩).trans (congrFun h ⟨j, hj⟩).symm

private theorem graphMatrix_range_contains {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] {d : ℕ} (I : Pivot ι d)
    (M : Matrix (Outside I) (Inside I) ℂ) (C : Matrix ι κ ℂ) :
    C.mulVecLin.range ≤ (graphMatrix I M).mulVecLin.range ↔
      C.submatrix (fun j : Outside I ↦ j.val) id =
        M * C.submatrix (fun i : Inside I ↦ i.val) id := by
  rw [← Matrix.toLin'.injective.eq_iff, Matrix.toLin'_mul]
  constructor
  · intro h
    apply LinearMap.ext
    intro u
    have hu := (graphMatrix_mem_range I M (C *ᵥ u)).mp (h ⟨u, rfl⟩)
    exact hu
  · intro h v hv
    obtain ⟨u, rfl⟩ := hv
    exact (graphMatrix_mem_range I M _).mpr (DFunLike.congr_fun h u)

set_option maxHeartbeats 800000 in
theorem grassmannianFlagChartEquations : GrassmannianFlagChartEquations := by
  intro V ι _ _ _ _ A B _ b d hd I
  classical
  let P := A.map b.equivFun.toLinearMap
  let Q := B.map b.equivFun.toLinearMap
  let bP := Module.finBasis ℂ P
  let bQ := Module.finBasis ℂ ((ι → ℂ) ⧸ Q)
  let C := LinearMap.toMatrix' (P.subtype.comp bP.equivFun.symm.toLinearMap)
  let T := LinearMap.toMatrix' (bQ.equivFun.toLinearMap.comp Q.mkQ)
  let Cₒ := C.submatrix (fun j : Outside I ↦ j.val) id
  let Cᵢ := C.submatrix (fun i : Inside I ↦ i.val) id
  have hC : C.mulVecLin.range = P := by
    rw [← Matrix.toLin'_apply', Matrix.toLin'_toMatrix', LinearMap.range_comp_of_range_eq_top _
      bP.equivFun.symm.range, Submodule.range_subtype]
  have hT : T.mulVecLin.ker = Q := by
    rw [← Matrix.toLin'_apply', Matrix.toLin'_toMatrix',
      LinearMap.ker_comp_of_ker_eq_bot _ (LinearMap.ker_eq_bot.mpr bQ.equivFun.injective),
      Submodule.ker_mkQ]
  let L₁ := -(mulRightLinearMap (Outside I) ℂ Cᵢ)
  let L₂ := (mulLeftLinearMap (Inside I) ℂ T).comp (graphVariation I)
  let L := L₁.prod L₂
  let c := (Cₒ, T * graphMatrix I (0 : Matrix (Outside I) (Inside I) ℂ))
  let D := Matrix (Outside I) (Fin (Module.finrank ℂ P)) ℂ ×
    Matrix (Fin (Module.finrank ℂ ((ι → ℂ) ⧸ Q))) (Inside I) ℂ
  let F := (Module.finBasis ℂ D).equivFun
  let f : AffineMap ℂ (Matrix (Outside I) (Inside I) ℂ) (Fin (Module.finrank ℂ D) → ℂ) :=
    F.toLinearMap.toAffineMap.comp
      (L.toAffineMap +ᵥ AffineMap.const ℂ (Matrix (Outside I) (Inside I) ℂ) (c : D))
  refine ⟨_, f, ?_⟩
  intro M
  have hf : f M = F (Cₒ - M * Cᵢ, T * graphMatrix I M) := by
    change F (-(M * Cᵢ) + Cₒ, T * graphVariation I M + T * graphMatrix I 0) = _
    rw [← Matrix.mul_add, ← graphMatrix_eq_variation_add, sub_eq_add_neg, add_comm Cₒ]
  change (A ≤ grassmannianSubspace b hd (grassmannianChartPoint b hd I M) ∧
    grassmannianSubspace b hd (grassmannianChartPoint b hd I M) ≤ B) ↔ f M = 0
  rw [hf, ← F.map_zero, F.injective.eq_iff, Prod.mk_eq_zero,
    ← Submodule.map_le_map_iff_of_injective b.equivFun.injective A,
    ← Submodule.map_le_map_iff_of_injective b.equivFun.injective _ B,
    grassmannianChartSubspace, Matrix.toLin'_apply']
  change (P ≤ (graphMatrix I M).mulVecLin.range ∧ (graphMatrix I M).mulVecLin.range ≤ Q) ↔ _
  have hp : (P ≤ (graphMatrix I M).mulVecLin.range) ↔
      (C.mulVecLin.range ≤ (graphMatrix I M).mulVecLin.range) := by rw [hC]
  have hq : ((graphMatrix I M).mulVecLin.range ≤ Q) ↔
      ((graphMatrix I M).mulVecLin.range ≤ T.mulVecLin.ker) := by rw [hT]
  refine and_congr (hp.trans ?_) (hq.trans ?_)
  · rw [graphMatrix_range_contains, sub_eq_zero]
  · rw [LinearMap.range_le_ker_iff, ← Matrix.toLin'_apply' T,
      ← Matrix.toLin'_apply' (graphMatrix I M), ← Matrix.toLin'_mul,
      ← Matrix.toLin'.map_zero, Matrix.toLin'.injective.eq_iff]

private theorem isClosed_flag_locus {V ι : Type} [AddCommGroup V] [Module ℂ V]
    [Fintype ι] [DecidableEq ι] (A B : Submodule ℂ V) (hAB : A ≤ B)
    (b : Module.Basis ι ℂ V) {d : ℕ} (hd : d ≤ Module.finrank ℂ V) :
    IsClosed {p | A ≤ grassmannianSubspace b hd p ∧ grassmannianSubspace b hd p ≤ B} := by
  change @IsClosed _ (⨆ I : Pivot ι d, TopologicalSpace.coinduced
    (grassmannianChartPoint b hd I) inferInstance) _
  rw [isClosed_iSup_iff]
  intro I
  rw [isClosed_coinduced]
  obtain ⟨n, F, hF⟩ := grassmannianFlagChartEquations A B hAB b hd I
  have h : (grassmannianChartPoint b hd I ⁻¹'
      {p | A ≤ grassmannianSubspace b hd p ∧ grassmannianSubspace b hd p ≤ B}) =
      {M | F M = 0} := Set.ext hF
  rw [h]
  exact isClosed_eq F.continuous_of_finiteDimensional continuous_const

end Flags

section SplitFlags

open Matrix

private theorem continuous_from_open_cover {α β J : Type} [TopologicalSpace α] [TopologicalSpace β]
    {U : J → Type} [∀ i, TopologicalSpace (U i)]
    (c : ∀ i, U i → α) (hc : ∀ i, IsOpenEmbedding (c i))
    (hcover : ∀ x, ∃ i y, c i y = x) (f : α → β) (hf : ∀ i, Continuous (f ∘ c i)) :
    Continuous f := by
  rw [continuous_def]
  intro s hs
  have he : f ⁻¹' s = ⋃ i, c i '' ((f ∘ c i) ⁻¹' s) := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, y, rfl⟩ := hcover x
      exact Set.mem_iUnion.mpr ⟨i, y, hx, rfl⟩
    · intro hx
      obtain ⟨i, y, hy, rfl⟩ := Set.mem_iUnion.mp hx
      exact hy
  rw [he]
  exact isOpen_iUnion fun i ↦ (hc i).isOpenMap _ (hs.preimage (hf i))

private theorem matrix_range_fromCols {ι κ τ : Type} [Fintype κ] [Fintype τ]
    (C : Matrix ι κ ℂ) (D : Matrix ι τ ℂ) :
    (Matrix.fromCols C D).mulVecLin.range = C.mulVecLin.range ⊔ D.mulVecLin.range := by
  ext v
  constructor
  · rintro ⟨z, rfl⟩
    change Matrix.fromCols C D *ᵥ z ∈ _
    rw [Matrix.fromCols_mulVec]
    exact Submodule.mem_sup.mpr ⟨_, ⟨_, rfl⟩, _, ⟨_, rfl⟩, rfl⟩
  · intro hv
    obtain ⟨_, ⟨x, rfl⟩, _, ⟨y, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hv
    exact ⟨Sum.elim x y, Matrix.fromCols_mulVec_sumElim C D x y⟩

set_option maxHeartbeats 900000 in
private theorem continuous_of_flag_chart {U V ι κ X : Type}
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [TopologicalSpace X]
    (b : Module.Basis ι ℂ U) (c : Module.Basis κ ℂ V)
    {d e : ℕ} (hd : d ≤ Module.finrank ℂ U) (he : e ≤ Module.finrank ℂ V)
    (I : Pivot ι d) (p : X → Matrix (Outside I) (Inside I) ℂ)
    (hp : Continuous p) (f : X → GrassmannianPoints c he)
    (A : Submodule ℂ V) (l : U →ₗ[ℂ] V)
    (hf : ∀ x, grassmannianSubspace c he (f x) =
      A ⊔ (grassmannianSubspace b hd (grassmannianChartPoint b hd I (p x))).map l) :
    Continuous f := by
  let : FiniteDimensional ℂ V := Module.Finite.of_basis c
  let T := LinearMap.toMatrix'
    (c.equivFun.toLinearMap.comp (l.comp b.equivFun.symm.toLinearMap))
  let a := Module.finBasis ℂ A
  let C := LinearMap.toMatrix'
    (c.equivFun.toLinearMap.comp (A.subtype.comp a.equivFun.symm.toLinearMap))
  have hC : C.mulVecLin.range = A.map c.equivFun.toLinearMap := by
    rw [← Matrix.toLin'_apply', Matrix.toLin'_toMatrix', LinearMap.range_comp,
      LinearMap.range_comp_of_range_eq_top _ a.equivFun.symm.range, Submodule.range_subtype]
  let F (z : X) : Matrix κ
      (Fin (Module.finrank ℂ A) ⊕ Inside I) ℂ :=
    Matrix.fromCols C (T * graphMatrix I (p z))
  have hcont : Continuous F := by
    apply continuous_matrix
    intro j k
    cases k with
    | inl k => exact continuous_const
    | inr k =>
      exact (continuous_const.matrix_mul
        ((continuous_graphMatrix I).comp hp)).matrix_elem j k
  apply continuous_of_spanning_matrices c he f F hcont
  intro z
  rw [hf, Submodule.map_sup, matrix_range_fromCols, hC]
  congr 1
  have hT : (Matrix.toLin' T).comp b.equivFun.toLinearMap = c.equivFun.toLinearMap.comp l := by
    rw [Matrix.toLin'_toMatrix', LinearMap.comp_assoc, LinearMap.comp_assoc,
      LinearEquiv.symm_comp, LinearMap.comp_id]
  rw [← Submodule.map_comp, ← hT, Submodule.map_comp]
  change ((grassmannianSubspace b hd (grassmannianChartPoint b hd I (p z))).map
    b.equivFun.toLinearMap).map (Matrix.toLin' T) = _
  rw [grassmannianChartSubspace, ← LinearMap.range_comp, ← Matrix.toLin'_mul]
  rfl

private theorem continuous_of_flag_formula {U V ι κ : Type}
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (b : Module.Basis ι ℂ U) (c : Module.Basis κ ℂ V)
    {d e : ℕ} (hd : d ≤ Module.finrank ℂ U) (he : e ≤ Module.finrank ℂ V)
    (S : Set (GrassmannianPoints b hd)) (f : S → GrassmannianPoints c he)
    (A : Submodule ℂ V) (l : U →ₗ[ℂ] V)
    (hf : ∀ p, grassmannianSubspace c he (f p) =
      A ⊔ (grassmannianSubspace b hd p.val).map l) :
    Continuous f := by
  let chart (I : Pivot ι d) := S.restrictPreimage (grassmannianChartPoint b hd I)
  apply continuous_from_open_cover chart
    (fun I ↦ (graphChartOpenEmbeddings b hd I).restrictPreimage S)
  · intro p
    obtain ⟨I, M, hM⟩ := grassmannianChartPoint_cover b hd p.val
    have hm : grassmannianChartPoint b hd I M ∈ S := hM.symm ▸ p.property
    exact ⟨I, ⟨M, hm⟩, Subtype.ext hM⟩
  · intro I
    exact continuous_of_flag_chart b c hd he I Subtype.val continuous_subtype_val
      (f ∘ chart I) A l (fun x ↦ hf (chart I x))

private theorem mem_split_flag {U V : Type} [AddCommGroup U] [Module ℂ U]
    [AddCommGroup V] [Module ℂ V] {A : Submodule ℂ V}
    {l : U →ₗ[ℂ] V} {q : V →ₗ[ℂ] U}
    (hql : q.comp l = LinearMap.id) (hA : A ≤ q.ker)
    (P : Submodule ℂ U) (v : V) :
    v ∈ A ⊔ P.map l ↔ v ∈ A ⊔ l.range ∧ q v ∈ P := by
  have hq (u : U) : q (l u) = u := DFunLike.congr_fun hql u
  constructor
  · intro hv
    obtain ⟨a, ha, _, ⟨u, hu, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hv
    refine ⟨Submodule.mem_sup.mpr ⟨a, ha, l u, ⟨u, rfl⟩, rfl⟩, ?_⟩
    rw [map_add, LinearMap.mem_ker.mp (hA ha), zero_add, hq]
    exact hu
  · rintro ⟨hv, hP⟩
    obtain ⟨a, ha, _, ⟨u, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hv
    refine Submodule.mem_sup.mpr ⟨a, ha, l u, ⟨u, ?_, rfl⟩, rfl⟩
    rw [map_add, LinearMap.mem_ker.mp (hA ha), zero_add, hq] at hP
    exact hP

set_option maxHeartbeats 1000000 in
private theorem splitFlagEmbedding {U V ι κ : Type} [AddCommGroup U] [Module ℂ U]
    [AddCommGroup V] [Module ℂ V] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (b : Module.Basis ι ℂ U) (c : Module.Basis κ ℂ V) {d : ℕ} (hd : d ≤ Module.finrank ℂ U)
    (A : Submodule ℂ V) (l : U →ₗ[ℂ] V) (q : V →ₗ[ℂ] U)
    (hql : q.comp l = LinearMap.id) (hA : A ≤ q.ker) :
    ∃ (hD : d + Module.finrank ℂ A ≤ Module.finrank ℂ V)
      (f : GrassmannianPoints b hd → GrassmannianPoints c hD),
      IsClosedEmbedding f ∧
      (∀ p, grassmannianSubspace c hD (f p) =
        A ⊔ (grassmannianSubspace b hd p).map l) ∧
      Set.range f = {p | A ≤ grassmannianSubspace c hD p ∧
        grassmannianSubspace c hD p ≤ A ⊔ l.range} := by
  let : FiniteDimensional ℂ U := Module.Finite.of_basis b
  let : FiniteDimensional ℂ V := Module.Finite.of_basis c
  let B := A ⊔ l.range
  let lift (P : Submodule ℂ U) := A ⊔ P.map l
  have hq (u : U) : q (l u) = u := DFunLike.congr_fun hql u
  have hl : Function.Injective l := (show Function.LeftInverse q l from hq).injective
  have hdis (P : Submodule ℂ U) : Disjoint A (P.map l) := by
    rw [disjoint_iff_inf_le]
    rintro _ ⟨ha, u, _, rfl⟩
    have h := (LinearMap.mem_ker.mp (hA ha))
    rw [hq] at h
    simp [h]
  have hdim (P : Submodule ℂ U) :
      Module.finrank ℂ (lift P) = Module.finrank ℂ P + Module.finrank ℂ A := by
    have hr := Submodule.finrank_sup_add_finrank_inf_eq A (P.map l)
    rw [(hdis P).eq_bot, finrank_bot, add_zero,
      ← (P.equivMapOfInjective l hl).finrank_eq, add_comm] at hr
    exact hr
  have hrank := (grassmannianSubspace_finrank b hd)
  have hD : d + Module.finrank ℂ A ≤ Module.finrank ℂ V := by
    have htop := (lift (⊤ : Submodule ℂ U)).finrank_le
    rw [hdim, finrank_top] at htop
    omega
  let f (p : GrassmannianPoints b hd) := subspacePoint c hD (lift (grassmannianSubspace b hd p))
    ((hdim _).trans (congrArg (· + Module.finrank ℂ A) (hrank p)))
  have hf (p) : grassmannianSubspace c hD (f p) = lift (grassmannianSubspace b hd p) :=
    subspacePoint_subspace _ _ _ _
  have hproj (P : Submodule ℂ U) : (lift P).map q = P := by
    change (A ⊔ P.map l).map q = P
    rw [Submodule.map_sup, (LinearMap.le_ker_iff_map.mp hA), bot_sup_eq,
      ← Submodule.map_comp, hql, Submodule.map_id]
  have hinv (P : Submodule ℂ V) (hAP : A ≤ P) (hPB : P ≤ B) : lift (P.map q) = P := by
    ext v
    rw [mem_split_flag hql hA]
    refine ⟨?_, fun hv ↦ ⟨hPB hv, ⟨v, hv, rfl⟩⟩⟩
    rintro ⟨hv, w, hw, he⟩
    have hPB' (z : V) (hz : z ∈ B) : z - l (q z) ∈ A := by
      obtain ⟨a, ha, _, ⟨u, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hz
      simpa only [map_add, LinearMap.mem_ker.mp (hA ha), zero_add, hq, add_sub_cancel_right] using ha
    have ht : v - w ∈ A := by
      have hm := A.sub_mem (hPB' v hv) (hPB' w (hPB hw))
      rw [he, sub_sub_sub_cancel_right] at hm
      exact hm
    simpa using P.add_mem (hAP ht) hw
  let S : Set (GrassmannianPoints c hD) := {p |
    A ≤ grassmannianSubspace c hD p ∧ grassmannianSubspace c hD p ≤ B}
  have hfS (p : GrassmannianPoints b hd) : f p ∈ S := by
    change A ≤ grassmannianSubspace c hD (f p) ∧ grassmannianSubspace c hD (f p) ≤ B
    rw [hf]
    refine ⟨le_sup_left, sup_le_sup_left ?_ _⟩
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, rfl⟩
  let g (p : S) : GrassmannianPoints b hd :=
    subspacePoint b hd ((grassmannianSubspace c hD p.val).map q) (by
      have h := grassmannianSubspace_finrank c hD p.val
      have hh := hdim ((grassmannianSubspace c hD p.val).map q)
      rw [hinv _ p.property.1 p.property.2, h] at hh
      omega)
  have hg (p : S) :
      grassmannianSubspace b hd (g p) = (grassmannianSubspace c hD p.val).map q :=
    subspacePoint_subspace _ _ _ _
  let E : GrassmannianPoints b hd ≃ S :=
    { toFun := fun p ↦ ⟨f p, hfS p⟩
      invFun := g
      left_inv := fun p ↦ by
        apply grassmannianSubspace_injective b hd
        change grassmannianSubspace b hd (g ⟨f p, hfS p⟩) = _
        rw [hg, hf, hproj]
      right_inv := fun p ↦ by
        apply Subtype.ext
        apply grassmannianSubspace_injective c hD
        change grassmannianSubspace c hD (f (g p)) = _
        rw [hf, hg, hinv _ p.property.1 p.property.2] }
  have hfc : Continuous f := by
    change @Continuous _ _ (⨆ I : Pivot ι d, TopologicalSpace.coinduced
      (grassmannianChartPoint b hd I) inferInstance) _ f
    rw [continuous_iSup_dom]
    intro I
    rw [continuous_coinduced_dom]
    exact continuous_of_flag_chart b c hd hD I id continuous_id
      (f ∘ grassmannianChartPoint b hd I) A l (fun x ↦ hf (grassmannianChartPoint b hd I x))
  have hgc : Continuous g := continuous_of_flag_formula c b hD hd S g ⊥ q
    (fun p ↦ (hg p).trans (bot_sup_eq _).symm)
  let H : GrassmannianPoints b hd ≃ₜ S :=
    { toEquiv := E
      continuous_toFun := hfc.subtype_mk hfS
      continuous_invFun := hgc }
  have hrange : Set.range f = S := by
    ext p
    constructor
    · rintro ⟨q, rfl⟩
      exact hfS q
    · intro hp
      obtain ⟨q, hq⟩ := E.surjective ⟨p, hp⟩
      exact ⟨q, congrArg Subtype.val hq⟩
  refine ⟨hD, f, ⟨IsEmbedding.subtypeVal.comp H.isEmbedding, ?_⟩, hf, hrange⟩
  rw [hrange]
  exact isClosed_flag_locus A B le_sup_left c hD

set_option maxHeartbeats 900000 in
theorem grassmannianFlagIncidence : GrassmannianFlagIncidence := by
  intro V ι κ _ _ _ _ _ _ A B hAB b bQ d hd
  let Q := (A.comap B.subtype).mkQ
  obtain ⟨s, hs⟩ := Q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr
    (Submodule.mkQ_surjective _))
  obtain ⟨r, hr⟩ := B.subtype.exists_leftInverse_of_injective B.ker_subtype
  let l := B.subtype.comp s
  let q := Q.comp r
  have hql : q.comp l = LinearMap.id := by
    apply LinearMap.ext
    intro u
    change Q (r (B.subtype (s u))) = u
    rw [show r (B.subtype (s u)) = s u from DFunLike.congr_fun hr (s u)]
    exact DFunLike.congr_fun hs u
  have hrQ (x : B) : q x.val = Q x :=
    congrArg Q (DFunLike.congr_fun hr x)
  have hA : A ≤ q.ker := by
    intro v hv
    have h := hrQ ⟨v, hAB hv⟩
    exact LinearMap.mem_ker.mpr (h.trans (Submodule.Quotient.mk_eq_zero _ |>.mpr hv))
  have hB : A ⊔ l.range = B := by
    refine le_antisymm (sup_le hAB ?_) ?_
    · rintro _ ⟨v, rfl⟩
      exact (s v).property
    · intro v hv
      let x : B := ⟨v, hv⟩
      have hker : Q (x - s (Q x)) = 0 := by
        rw [map_sub, show Q (s (Q x)) = Q x from DFunLike.congr_fun hs (Q x), sub_self]
      have ha : v - l (Q x) ∈ A := by
        have h := LinearMap.mem_ker.mpr hker
        rw [Submodule.ker_mkQ] at h
        exact h
      exact Submodule.mem_sup.mpr ⟨_, ha, _, ⟨_, rfl⟩, sub_add_cancel _ _⟩
  obtain ⟨hD, f, hf, hsub, hrange⟩ := splitFlagEmbedding bQ b hd A l q hql hA
  refine ⟨hD, f, hf, ?_, ?_⟩
  · intro p v
    rw [hsub, mem_split_flag hql hA, hB]
    exact ⟨fun h ↦ ⟨⟨v, h.1⟩, rfl, hrQ ⟨v, h.1⟩ ▸ h.2⟩,
      fun ⟨x, hx, h⟩ ↦ ⟨hx ▸ x.property, hx ▸ (hrQ x).symm ▸ h⟩⟩
  · rwa [hB] at hrange

end SplitFlags

section Windows

open private LatticeModelSpecs.quotientEquivOfKernel
  from MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.LatticeModels

private def windowRepresentative {r : ℕ} (b : ℤ) (k : ℕ) (x : Fin r → O) :
    Window r b k :=
  (@Submodule.mkQ O ((scalarLattice r b).val : Type)
    inferInstance inferInstance inferInstance (windowLower r b k)) (shiftedCoordinates r b x)

set_option maxHeartbeats 650000 in
private theorem windowRepresentative_surjective (r : ℕ) (b : ℤ) (k : ℕ) :
    Function.Surjective (windowRepresentative (r := r) b k) :=
  (Submodule.mkQ_surjective _).comp (shiftedCoordinates r b).surjective

set_option maxHeartbeats 600000 in
private theorem windowRepresentative_coeff {r k : ℕ} {b : ℤ} (x : Fin r → O)
    (i : Fin r) (j : Fin k) :
    windowCoordinates r b k (windowRepresentative b k x) (i, j) =
      PowerSeries.coeff j.val (x i) := by
  have h : windowJets r b k (windowRepresentative b k x) =
      windowReduction r b k (shiftedCoordinates r b x) := by
    simp only [windowRepresentative, windowJets, LatticeModelSpecs.quotientEquivOfKernel,
      LinearEquiv.trans_apply, Submodule.mkQ_apply, Submodule.quotEquivOfEq_mk,
      LinearMap.quotKerEquivOfSurjective_apply_mk]
  change jetCoefficients k (windowJets r b k (windowRepresentative b k x) i) j = _
  rw [h]
  change jetCoefficients k (jetReduction k ((shiftedCoordinates r b).symm
    (shiftedCoordinates r b x) i)) j = _
  rw [LinearEquiv.symm_apply_apply, jetCoefficients_reduce]

private theorem mem_windowSubspace_iff {r k : ℕ} {b : ℤ} (L : Lattice r) (w : Window r b k) :
    w ∈ latticeSubspace b k L ↔
      ∃ x : Fin r → O, shiftedInclusion r b x ∈ L.val ∧ windowRepresentative b k x = w := by
  change (∃ v : (scalarLattice r b).val,
    v.val ∈ L.val ∧ (windowLower r b k).mkQ v = w) ↔ _
  constructor
  · rintro ⟨v, hv, he⟩
    obtain ⟨x, rfl⟩ := (shiftedCoordinates r b).surjective v
    exact ⟨x, hv, he⟩
  · rintro ⟨x, hx, he⟩
    exact ⟨shiftedCoordinates r b x, hx, he⟩

private theorem shiftedInclusion_mem_scalar_iff {r n : ℕ} {b : ℤ} (x : Fin r → O) :
    shiftedInclusion r b x ∈ (scalarLattice r (b + (n : ℤ))).val ↔
      ∀ i, t ^ n ∣ x i := by
  rw [scalarLattice_val, LinearMap.mem_range]
  constructor
  · rintro ⟨y, hy⟩ i
    rw [shiftedInclusion_add_nat] at hy
    exact ⟨y i, (congrFun (shiftedInclusion_injective r b hy) i).symm⟩
  · intro h
    choose y hy using h
    refine ⟨y, ?_⟩
    rw [shiftedInclusion_add_nat]
    exact congrArg (shiftedInclusion r b) (funext fun i ↦ (hy i).symm)

set_option maxHeartbeats 600000 in
private theorem mem_windowScalar_iff {r k n : ℕ} {b : ℤ} (hn : n ≤ k) (w : Window r b k) :
    w ∈ latticeSubspace b k (scalarLattice r (b + (n : ℤ))) ↔
      ∀ (i : Fin r) (j : Fin k), j.val < n → windowCoordinates r b k w (i, j) = 0 := by
  rw [mem_windowSubspace_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩ i j hj
    rw [windowRepresentative_coeff]
    exact PowerSeries.X_pow_dvd_iff.mp ((shiftedInclusion_mem_scalar_iff x).mp hx i) _ hj
  · intro hw
    obtain ⟨x, rfl⟩ := windowRepresentative_surjective r b k w
    refine ⟨x, (shiftedInclusion_mem_scalar_iff x).mpr ?_, rfl⟩
    intro i
    apply PowerSeries.X_pow_dvd_iff.mpr
    intro j hj
    have hh := hw i ⟨j, hj.trans_le hn⟩ hj
    rwa [windowRepresentative_coeff] at hh

private abbrev Coefficients (r m : ℕ) := Fin r × Fin m → ℂ

private def sliceCoefficients (r k s m : ℕ) (h : s + m ≤ k) :
    Coefficients r k →ₗ[ℂ] Coefficients r m :=
  LinearMap.pi fun ij ↦ LinearMap.proj
    (ij.1, (⟨s + ij.2.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left ij.2.isLt s) h⟩ : Fin k))

private def insertCoefficients (r k s m : ℕ) : Coefficients r m →ₗ[ℂ] Coefficients r k where
  toFun x ij :=
    if h : s ≤ ij.2.val ∧ ij.2.val < s + m then x (ij.1, ⟨ij.2.val - s, by omega⟩) else 0
  map_add' x y := by
    funext ij
    change (if h : s ≤ ij.2.val ∧ ij.2.val < s + m then
      (x + y) (ij.1, ⟨ij.2.val - s, by omega⟩) else 0) = _
    by_cases h : s ≤ ij.2.val ∧ ij.2.val < s + m <;> simp [h]
  map_smul' c x := by
    funext ij
    change (if h : s ≤ ij.2.val ∧ ij.2.val < s + m then
      (c • x) (ij.1, ⟨ij.2.val - s, by omega⟩) else 0) = _
    by_cases h : s ≤ ij.2.val ∧ ij.2.val < s + m <;> simp [h]

private def windowSlice (r : ℕ) (b a : ℤ) (k s m : ℕ) (h : s + m ≤ k) :
    Window r b k →ₗ[ℂ] Window r a m :=
  (windowCoordinates r a m).symm.toLinearMap.comp
    ((sliceCoefficients r k s m h).comp (windowCoordinates r b k).toLinearMap)

private def windowInsert (r : ℕ) (b a : ℤ) (k s m : ℕ) :
    Window r a m →ₗ[ℂ] Window r b k :=
  (windowCoordinates r b k).symm.toLinearMap.comp
    ((insertCoefficients r k s m).comp (windowCoordinates r a m).toLinearMap)

private theorem windowInsert_coeff {r k s m : ℕ} {a b : ℤ} (x : Window r a m)
    (i : Fin r) (j : Fin k) :
    windowCoordinates r b k (windowInsert r b a k s m x) (i, j) =
      if h : s ≤ j.val ∧ j.val < s + m then
        windowCoordinates r a m x (i, ⟨j.val - s, by omega⟩) else 0 := by
  unfold windowInsert
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rfl

private theorem windowSlice_coeff {r k s m : ℕ} {a b : ℤ} (h : s + m ≤ k) (w : Window r b k)
    (i : Fin r) (j : Fin m) :
    windowCoordinates r a m (windowSlice r b a k s m h w) (i, j) =
      windowCoordinates r b k w (i, ⟨s + j.val, by have := j.isLt; omega⟩) := by
  simp only [windowSlice, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rfl

private theorem windowSlice_insert {r k s m : ℕ} {a b : ℤ} (h : s + m ≤ k) :
    (windowSlice r b a k s m h).comp (windowInsert r b a k s m) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  apply (windowCoordinates r a m).injective
  funext ij
  obtain ⟨i, j⟩ := ij
  rw [windowSlice_coeff, windowInsert_coeff]
  have hj : s ≤ s + j.val ∧ s + j.val < s + m :=
    ⟨Nat.le_add_right .., Nat.add_lt_add_left j.isLt s⟩
  rw [dite_eq_left hj]
  have he : (⟨s + j.val - s, by omega⟩ : Fin m) = j :=
    Fin.ext (Nat.add_sub_cancel_left s j.val)
  rw [he]

private theorem windowInsert_tail_range {r k s m : ℕ} {a b : ℤ} (h : s + m = k) :
    (windowInsert r b a k s m).range = latticeSubspace b k (scalarLattice r (b + (s : ℤ))) := by
  ext w
  rw [mem_windowScalar_iff (by omega : s ≤ k)]
  constructor
  · rintro ⟨x, rfl⟩ i j hj
    rw [windowInsert_coeff, dite_eq_right (fun h' ↦ (not_le_of_gt hj) h'.1)]
  · intro hw
    refine ⟨windowSlice r b a k s m h.le w, (windowCoordinates r b k).injective ?_⟩
    funext ij
    obtain ⟨i, j⟩ := ij
    rw [windowInsert_coeff]
    by_cases hj : s ≤ j.val
    · rw [dite_eq_left ⟨hj, h ▸ j.isLt⟩, windowSlice_coeff]
      have he : (⟨s + (j.val - s), by omega⟩ : Fin k) = j :=
        Fin.ext (Nat.add_sub_of_le hj)
      rw [he]
    · rw [dite_eq_right (fun h' ↦ hj h'.1), hw i j (Nat.lt_of_not_ge hj)]

set_option maxHeartbeats 600000 in
private theorem windowScalar_finrank_tail (r : ℕ) (b : ℤ) (k s : ℕ) (h : s ≤ k) :
    Module.finrank ℂ (latticeSubspace b k (scalarLattice r (b + (s : ℤ)))) = r * (k - s) := by
  let m := k - s
  have hm : s + m = k := Nat.add_sub_of_le h
  let l := windowInsert r b b k s m
  have hl : Function.Injective l :=
    (show Function.LeftInverse (windowSlice r b b k s m hm.le) l from fun x ↦
      DFunLike.congr_fun (windowSlice_insert hm.le) x).injective
  have he : Module.finrank ℂ l.range = Module.finrank ℂ (Window r b m) :=
    (LinearEquiv.ofInjective l hl).finrank_eq.symm
  rw [windowInsert_tail_range hm] at he
  rw [he, (windowCoordinates r b m).finrank_eq]
  simp [Module.finrank_fintype_fun_eq_card, m]

set_option maxHeartbeats 600000 in
private theorem windowScalar_finrank_head (r : ℕ) (b : ℤ) (k s : ℕ) (h : s ≤ k) :
    Module.finrank ℂ (Window r b k ⧸ latticeSubspace b k (scalarLattice r (b + (s : ℤ)))) =
      r * s := by
  let h' : 0 + s ≤ k := by omega
  let q := windowSlice r b b k 0 s h'
  have hs : Function.Surjective q := fun x ↦
    ⟨windowInsert r b b k 0 s x, DFunLike.congr_fun (windowSlice_insert h') x⟩
  have hq : q.ker = latticeSubspace b k (scalarLattice r (b + (s : ℤ))) := by
    ext w
    rw [mem_windowScalar_iff h, LinearMap.mem_ker]
    constructor
    · intro hw i j hj
      have hh := congrFun (congrArg (windowCoordinates r b s) hw) (i, (⟨j.val, hj⟩ : Fin s))
      rw [windowSlice_coeff, map_zero] at hh
      simpa using hh
    · intro hw
      apply (windowCoordinates r b s).injective
      rw [map_zero]
      funext ij
      obtain ⟨i, j⟩ := ij
      rw [windowSlice_coeff]
      exact hw i _ (by simp)
  rw [← hq, (q.quotKerEquivOfSurjective hs).finrank_eq, (windowCoordinates r b s).finrank_eq]
  simp [Module.finrank_fintype_fun_eq_card]

private theorem coeff_smul_power {r : ℕ} (s j : ℕ) (y : Fin r → O) (i : Fin r) :
    PowerSeries.coeff j ((t ^ s • y) i) =
      if s ≤ j then PowerSeries.coeff (j - s) (y i) else 0 :=
  PowerSeries.coeff_X_pow_mul' (y i) s j

set_option maxHeartbeats 1000000 in
private theorem mem_windowSubspace_slice {r k s m : ℕ} {a b : ℤ}
    (h : s + m ≤ k) (hab : b + (s : ℤ) = a) (L : Lattice r)
    (hL : (scalarLattice r (a + (m : ℤ))).val ≤ L.val)
    (hU : L.val ≤ (scalarLattice r a).val) (w : Window r b k) :
    w ∈ latticeSubspace b k L ↔
      w ∈ latticeSubspace b k (scalarLattice r a) ∧
      windowSlice r b a k s m h w ∈ latticeSubspace a m L := by
  have hshift (y : Fin r → O) : shiftedInclusion r b (t ^ s • y) = shiftedInclusion r a y := by
    rw [← hab, shiftedInclusion_add_nat]
  have hrep (y : Fin r → O) :
      windowSlice r b a k s m h (windowRepresentative b k (t ^ s • y)) =
        windowRepresentative a m y := by
    apply (windowCoordinates r a m).injective
    funext ij
    obtain ⟨i, j⟩ := ij
    rw [windowSlice_coeff, windowRepresentative_coeff, windowRepresentative_coeff,
      coeff_smul_power, ite_eq_left (Nat.le_add_right s j.val), Nat.add_sub_cancel_left]
  constructor
  · intro hw
    obtain ⟨x, hx, rfl⟩ := (mem_windowSubspace_iff L w).mp hw
    have hx' := hU hx
    rw [scalarLattice_val, LinearMap.mem_range] at hx'
    obtain ⟨y, hy⟩ := hx'
    have he : t ^ s • y = x := shiftedInclusion_injective r b ((hshift y).trans hy)
    refine ⟨(mem_windowSubspace_iff _ _).mpr ⟨x, hU hx, rfl⟩, ?_⟩
    rw [← he, hrep]
    exact (mem_windowSubspace_iff _ _).mpr ⟨y, hy ▸ hx, rfl⟩
  · rintro ⟨hw, hw'⟩
    obtain ⟨x, rfl⟩ := windowRepresentative_surjective r b k w
    obtain ⟨y, hy, he⟩ := (mem_windowSubspace_iff _ _).mp hw'
    have hlow (i : Fin r) (j : ℕ) (hj : j < s) : PowerSeries.coeff j (x i) = 0 := by
      have hh := (mem_windowScalar_iff (by omega : s ≤ k)
        (windowRepresentative b k x)).mp (hab.symm ▸ hw) i ⟨j, by omega⟩ hj
      rwa [windowRepresentative_coeff] at hh
    have hmid (i : Fin r) (j : Fin m) :
        PowerSeries.coeff (s + j.val) (x i) = PowerSeries.coeff j.val (y i) := by
      have hh := congrFun (congrArg (windowCoordinates r a m) he) (i, j)
      rw [windowRepresentative_coeff, windowSlice_coeff, windowRepresentative_coeff] at hh
      exact hh.symm
    have hz : shiftedInclusion r b (x - t ^ s • y) ∈
        (scalarLattice r (a + (m : ℤ))).val := by
      rw [← hab, add_assoc, ← Nat.cast_add, shiftedInclusion_mem_scalar_iff]
      intro i
      apply PowerSeries.X_pow_dvd_iff.mpr
      intro j hj
      change PowerSeries.coeff j (x i - (t ^ s • y) i) = 0
      rw [map_sub, coeff_smul_power]
      by_cases hj' : s ≤ j
      · rw [ite_eq_left hj']
        have hh := hmid i ⟨j - s, by omega⟩
        change PowerSeries.coeff (s + (j - s)) (x i) = _ at hh
        rwa [Nat.add_sub_of_le hj', ← sub_eq_zero] at hh
      · rw [ite_eq_right hj', hlow i j (Nat.lt_of_not_ge hj'), sub_self]
    apply (mem_windowSubspace_iff _ _).mpr
    refine ⟨x, ?_, rfl⟩
    have h := L.val.add_mem (hL hz) hy
    rw [map_sub, hshift, sub_add_cancel] at h
    exact h

set_option maxHeartbeats 1100000 in
theorem windowFlagIncidence : WindowFlagIncidence := by
  intro r a b m k hba hab
  let s := (a - b).toNat
  let tlen := (b + (k : ℤ) - (a + (m : ℤ))).toNat
  let A := latticeSubspace b k (scalarLattice r (a + (m : ℤ)))
  let B := latticeSubspace b k (scalarLattice r a)
  have ha : b + (s : ℤ) = a := by dsimp [s]; omega
  have h : s + m ≤ k := by omega
  have ht : k - (s + m) = tlen := by dsimp [tlen]; omega
  have hA : ∀ w : Window r b k, w ∈ A ↔
      ∀ (i : Fin r) (j : Fin k), j.val < s + m → windowCoordinates r b k w (i, j) = 0 := by
    intro w
    change w ∈ latticeSubspace b k (scalarLattice r (a + (m : ℤ))) ↔ _
    rw [← ha, add_assoc, ← Nat.cast_add]
    exact mem_windowScalar_iff h w
  have hB : ∀ w : Window r b k, w ∈ B ↔
      ∀ (i : Fin r) (j : Fin k), j.val < s → windowCoordinates r b k w (i, j) = 0 := by
    intro w
    change w ∈ latticeSubspace b k (scalarLattice r a) ↔ _
    rw [← ha]
    exact mem_windowScalar_iff (by omega) w
  have hAB : A ≤ B := fun w hw ↦ (hB w).mpr fun i j hj ↦
    (hA w).mp hw i j (by omega)
  have hdA : Module.finrank ℂ A = r * tlen := by
    change Module.finrank ℂ (latticeSubspace b k (scalarLattice r (a + (m : ℤ)))) = _
    rw [← ha, add_assoc, ← Nat.cast_add, windowScalar_finrank_tail r b k (s + m) h, ht]
  have hdB : Module.finrank ℂ (Window r b k ⧸ B) = r * s := by
    change Module.finrank ℂ (Window r b k ⧸ latticeSubspace b k (scalarLattice r a)) = _
    rw [← ha]
    exact windowScalar_finrank_head r b k s (by omega)
  let l := windowInsert r b a k s m
  let q := windowSlice r b a k s m h
  have hql : q.comp l = LinearMap.id := windowSlice_insert h
  have hker : A ≤ q.ker := by
    intro w hw
    apply LinearMap.mem_ker.mpr
    apply (windowCoordinates r a m).injective
    rw [map_zero]
    funext ij
    obtain ⟨i, j⟩ := ij
    rw [show q w = windowSlice r b a k s m h w from rfl, windowSlice_coeff]
    exact (hA w).mp hw i _ (Nat.add_lt_add_left j.isLt s)
  have hsum : A ⊔ l.range = B := by
    refine le_antisymm (sup_le hAB ?_) ?_
    · rintro _ ⟨x, rfl⟩
      apply (hB _).mpr
      intro i j hj
      rw [show l x = windowInsert r b a k s m x from rfl, windowInsert_coeff,
        dite_eq_right (fun hn ↦ (not_le_of_gt hj) hn.1)]
    · intro w hw
      refine Submodule.mem_sup.mpr ⟨w - l (q w), ?_, l (q w), ⟨q w, rfl⟩, sub_add_cancel _ _⟩
      apply (hA _).mpr
      intro i j hj
      rw [map_sub, Pi.sub_apply, show l (q w) = windowInsert r b a k s m (q w) from rfl,
        windowInsert_coeff]
      by_cases hj' : s ≤ j.val
      · rw [dite_eq_left ⟨hj', hj⟩, show q w = windowSlice r b a k s m h w from rfl,
          windowSlice_coeff]
        have hj'' : (⟨s + (j.val - s), by omega⟩ : Fin k) = j :=
          Fin.ext (Nat.add_sub_of_le hj')
        rw [hj'', sub_self]
      · rw [dite_eq_right (fun hn ↦ hj' hn.1), (hB w).mp hw i j (Nat.lt_of_not_ge hj'), sub_self]
  refine ⟨h, hAB, hdA, hdB, ?_⟩
  intro d
  obtain ⟨hD, f, hf, hsub, hr⟩ := splitFlagEmbedding (windowBasis r a m)
    (windowBasis r b k) (windowDimension_le d) A l q hql hker
  let D : WindowDimension r b k := ⟨d.val + Module.finrank ℂ A, Nat.lt_succ_of_le hD⟩
  have hmem (p : WindowPoints r a m d) (w : Window r b k) :
      w ∈ grassmannianSubspace (windowBasis r b k) (windowDimension_le D) (f p) ↔
        w ∈ B ∧ q w ∈ grassmannianSubspace (windowBasis r a m) (windowDimension_le d) p := by
    rw [hsub, mem_split_flag hql hker, hsum]
  refine ⟨D, f, congrArg (d.val + ·) hdA, hf, ?_, ?_, ?_⟩
  · rw [hsum] at hr
    exact hr
  · intro p w
    rw [hmem, hB]
    rfl
  · intro L p hL hU hp
    ext w
    rw [hmem, hp]
    exact (mem_windowSubspace_slice h ha L hL hU w).symm

end Windows

section Transport

private theorem boundedPoint_subspace {N : ℕ} (L : BoundedLattice 2 N) :
    grassmannianSubspace (windowBasis 2 (-(N : ℤ)) (2 * N))
      (windowDimension_le (boundedPoint L).1) (boundedPoint L).2.val = boundedSubspace L :=
  subspacePoint_subspace _ _ _ rfl

private theorem boundedPoint_dimension {N : ℕ} (L : BoundedLattice 2 N) :
    (boundedPoint L).1.val = Module.finrank ℂ (boundedSubspace L) := rfl

private theorem boundedPoint_eq_of_subspace_eq {N : ℕ} {L M : BoundedLattice 2 N}
    (h : boundedSubspace L = boundedSubspace M) : boundedPoint L = boundedPoint M := by
  have hd : (boundedPoint L).1 = (boundedPoint M).1 := by
    apply Fin.ext
    rw [boundedPoint_dimension, boundedPoint_dimension]
    exact (congrArg (fun P : Submodule ℂ (BoundedWindow 2 N) ↦ Module.finrank ℂ P) h)
  have hL := boundedPoint_subspace L
  have hM := boundedPoint_subspace M
  generalize boundedPoint L = p at hd hL ⊢
  generalize boundedPoint M = q at hd hM ⊢
  obtain ⟨e, p⟩ := p
  obtain ⟨d, q⟩ := q
  change e = d at hd
  subst e
  have hpq : p = q := Subtype.ext
    (grassmannianSubspace_injective _ _ (hL.trans (h.trans hM.symm)))
  exact congrArg (Sigma.mk d) hpq

private theorem sigma_cast_snd {α : Type} {β : α → Type} (p : Sigma β)
    {a : α} (h : p.1 = a) : Sigma.mk a (h ▸ p.2) = p := by
  cases p
  cases h
  rfl

set_option maxHeartbeats 600000 in
theorem boundedPointTransport : BoundedPointTransport := by
  intro N d S X j hj hinj hd hrange
  let G := WindowPoints 2 (-(N : ℤ)) (2 * N) d
  let U (e : BoundedDimension N) :=
    StablePoints (windowBasis 2 (-(N : ℤ)) (2 * N)) (windowDimension_le e)
      (windowOperator 2 (-(N : ℤ)) (2 * N))
  let : ∀ e, TopologicalSpace (U e) := fun e ↦
    stablePointsTopology _ (windowDimension_le e) _
  let s (L : S) : U d := hd L.val L.property ▸ (boundedPoint L.val).2
  have hstage (L : S) : (⟨d, s L⟩ : BoundedStage 2 N) = boundedPoint L.val :=
    sigma_cast_snd (boundedPoint L.val) (hd L.val L.property)
  let g : S → G := fun L ↦ (s L).val
  have hgsub (L : S) :
      grassmannianSubspace (windowBasis 2 (-(N : ℤ)) (2 * N))
        (windowDimension_le d) (g L) = boundedSubspace L.val := by
    have h := boundedPoint_subspace L.val
    rw [← hstage L] at h
    exact h
  have hbounded : IsEmbedding (boundedPoint (r := 2) (N := N)) :=
    hinj.isEmbedding_induced
  have hs : IsEmbedding s := by
    have hm : IsEmbedding (Sigma.mk (β := U) d) := IsEmbedding.sigmaMk
    apply hm.of_comp_iff.mp
    have he : Sigma.mk (β := U) d ∘ s = boundedPoint ∘ ((↑) : S → BoundedLattice 2 N) :=
      funext hstage
    rw [he]
    exact hbounded.comp IsEmbedding.subtypeVal
  have hg : IsEmbedding g := IsEmbedding.subtypeVal.comp hs
  let : TopologicalSpace (Points X complexAlgebra) := pointTopology j
  let f : Points X complexAlgebra → G := fun p ↦ p ≫ j
  have hfm : Mono j.left := by
    let := hj
    infer_instance
  let : Mono j := Over.mono_of_mono_left j
  have hf : IsEmbedding f := Function.Injective.isEmbedding_induced
    (fun p q hpq ↦ (cancel_mono j).mp hpq)
  have hr : Set.range f = Set.range g := by
    rw [hrange]
    ext p
    constructor
    · rintro ⟨L, hL, he⟩
      exact ⟨⟨L, hL⟩, grassmannianSubspace_injective _ _ ((hgsub ⟨L, hL⟩).trans he.symm)⟩
    · rintro ⟨L, rfl⟩
      exact ⟨L.val, L.property, hgsub L⟩
  let E := hf.toHomeomorph.trans ((Homeomorph.setCongr hr).trans hg.toHomeomorph.symm)
  have hE (p : Points X complexAlgebra) : g (E p) = f p := by
    exact congrArg Subtype.val (hg.toHomeomorph.apply_symm_apply
      ((Homeomorph.setCongr hr) (hf.toHomeomorph p)))
  refine ⟨E, fun p ↦ ?_⟩
  change grassmannianSubspace _ (windowDimension_le d) (f p) = _
  rw [← hE p, hgsub]

set_option maxHeartbeats 600000 in
theorem boundedPointTransportCompatibility : BoundedPointTransportCompatibility := by
  intro N d e h S T X Y jX jY i hi hinj eX eY hX hY
  subst e
  simp only [eqToHom_refl, Category.comp_id] at hi
  let : TopologicalSpace (Points X complexAlgebra) := pointTopology jX
  let : TopologicalSpace (Points Y complexAlgebra) := pointTopology jY
  let f : Points X complexAlgebra → Points Y complexAlgebra := fun p ↦ p ≫ i
  have he (p : Points X complexAlgebra) : (eY (f p)).val = (eX p).val := by
    apply hinj (boundedPoint_eq_of_subspace_eq ?_)
    rw [← hY, ← hX]
    unfold pointSubspace f
    rw [Category.assoc, hi]
  have hST : S ⊆ T := by
    intro L hL
    let p := eX.symm ⟨L, hL⟩
    have hp : (eX p).val = L := congrArg Subtype.val (eX.apply_symm_apply ⟨L, hL⟩)
    exact (he p |>.trans hp) ▸ (eY (f p)).property
  refine ⟨hST, he, ?_, ?_⟩
  · apply (IsEmbedding.subtypeVal.comp eY.isEmbedding).of_comp_iff.mp
    have heq : ((↑) : T → BoundedLattice 2 N) ∘ eY ∘ f =
        ((↑) : S → BoundedLattice 2 N) ∘ eX := funext he
    change IsEmbedding (((↑) : T → BoundedLattice 2 N) ∘ eY ∘ f)
    rw [heq]
    exact IsEmbedding.subtypeVal.comp eX.isEmbedding
  · ext L
    change L ∈ Set.range (eY ∘ f) ↔ L.val ∈ S
    constructor
    · rintro ⟨p, rfl⟩
      exact (he p).symm ▸ (eX p).property
    · intro hL
      refine ⟨eX.symm ⟨L.val, hL⟩, Subtype.ext ?_⟩
      rw [Function.comp_apply, he, eX.apply_symm_apply]

end Transport

end
end RepTheorySurvey.Geometric.SchubertAnalyticFlagTransport
