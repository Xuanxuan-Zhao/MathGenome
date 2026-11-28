import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.GrassmannianIncidenceTopology
import Mathlib.Data.Matrix.ColumnRowPartitioned

namespace RepTheorySurvey.Geometric.GrassmannianIncidenceTopology

open LatticeModelSpecs GrassmannianIncidenceTopologySpecs
open LinearAlgebraicGroups.Specs.GrassmannianCharts (Pivot Inside Outside)
open Topology Matrix Module

noncomputable section

theorem restrictClosedEmbedding : RestrictClosedEmbedding := by
  intro X Y _ _ f S T hf hS h
  apply IsClosedEmbedding.of_comp IsEmbedding.subtypeVal
  exact hf.comp hS.isClosedEmbedding_subtypeVal

theorem sigmaClosedEmbedding : SigmaClosedEmbedding := by
  intro I J X Y _ _ shift f hshift hf
  refine ⟨(isEmbedding_sigmaMap hshift).mpr (fun i ↦ (hf i).isEmbedding), ?_⟩
  rw [isClosed_sigma_iff]
  intro j
  by_cases hj : j ∈ Set.range shift
  · obtain ⟨i, rfl⟩ := hj
    convert (hf i).isClosed_range using 1
    ext y
    constructor
    · rintro ⟨⟨k, x⟩, hx⟩
      have hki : k = i := hshift (congrArg Sigma.fst hx)
      subst k
      exact ⟨x, sigma_mk_injective hx⟩
    · rintro ⟨x, rfl⟩
      exact ⟨⟨i, x⟩, rfl⟩
  · convert isClosed_empty using 1
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro y ⟨⟨i, x⟩, hx⟩
    exact hj ⟨i, congrArg Sigma.fst hx⟩

section GraphCharts

variable {V ι : Type} [AddCommGroup V] [Module ℂ V] [Fintype ι] [DecidableEq ι]
  (b : Basis ι ℂ V) {d : ℕ} (hd : d ≤ finrank ℂ V)

private theorem continuous_chartPoint (I : Pivot ι d) :
    Continuous (grassmannianChartPoint b hd I) := by
  change Continuous[_, ⨆ J : Pivot ι d, TopologicalSpace.coinduced
    (grassmannianChartPoint b hd J) inferInstance] _
  exact continuous_iSup_rng (i := I) continuous_coinduced_rng

private theorem continuous_fromCharts {X : Type} [TopologicalSpace X]
    (f : GrassmannianPoints b hd → X)
    (hf : ∀ I : Pivot ι d, Continuous (f ∘ grassmannianChartPoint b hd I)) :
    Continuous f := by
  change Continuous[⨆ I : Pivot ι d, TopologicalSpace.coinduced
    (grassmannianChartPoint b hd I) inferInstance, _] _
  rw [continuous_iSup_dom]
  intro I
  exact continuous_coinduced_dom.mpr (hf I)

private theorem isClosed_fromCharts (S : Set (GrassmannianPoints b hd))
    (hS : ∀ I : Pivot ι d, IsClosed (grassmannianChartPoint b hd I ⁻¹' S)) :
    IsClosed S := by
  change @IsClosed _ (⨆ I : Pivot ι d, TopologicalSpace.coinduced
    (grassmannianChartPoint b hd I) inferInstance) S
  rw [isClosed_iSup_iff]
  intro I
  exact isClosed_coinduced.mpr (hS I)

omit [AddCommGroup V] [Module ℂ V] [Fintype ι] in
private theorem continuous_graphMatrix (I : Pivot ι d) :
    Continuous (graphMatrix (R := ℂ) I) := by
  apply continuous_matrix
  intro i j
  by_cases hi : i ∈ I.val
  · simp only [graphMatrix, Matrix.of_apply, dite_eq_left hi]
    exact continuous_const
  · simp only [graphMatrix, Matrix.of_apply, dite_eq_right hi]
    exact continuous_id.matrix_elem (⟨i, hi⟩ : Outside I) j

omit [AddCommGroup V] [Module ℂ V] [Fintype ι] in
private theorem graphMatrix_range_iff (I : Pivot ι d) (D : Matrix (Outside I) (Inside I) ℂ)
    (v : ι → ℂ) :
    v ∈ (graphMatrix I D).mulVecLin.range ↔ graphMatrix I D *ᵥ (fun i : Inside I ↦ v i) = v := by
  constructor
  · rintro ⟨x, rfl⟩
    congr 1
    funext i
    exact graphMatrix_inside I D x i
  · intro hv
    exact ⟨_, hv⟩

omit [AddCommGroup V] [Module ℂ V] [Fintype ι] in
private theorem normalizedGraph_range (J : Pivot ι d) (N : Matrix ι (Inside J) ℂ)
    (h : IsUnit (N.submatrix Subtype.val id).det) :
    (graphMatrix J (N.submatrix Subtype.val id * (N.submatrix Subtype.val id)⁻¹)).mulVecLin.range =
      N.mulVecLin.range := by
  classical
  let P : Matrix (Inside J) (Inside J) ℂ := N.submatrix Subtype.val id
  have hmul : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ h
  have hG : graphMatrix J (N.submatrix Subtype.val id * P⁻¹) = N * P⁻¹ := by
    ext i j
    by_cases hi : i ∈ J.val
    · have hentry := congrFun (congrFun hmul (⟨i, hi⟩ : Inside J)) j
      change (graphMatrix J (N.submatrix Subtype.val id * P⁻¹)) i j = (P * P⁻¹) ⟨i, hi⟩ j
      rw [hentry]
      simp [graphMatrix, hi, Matrix.one_apply, Subtype.ext_iff]
    · simp only [graphMatrix, Matrix.of_apply, dite_eq_right hi]
      rfl
  have hs : Function.Surjective P⁻¹.mulVecLin := by
    intro x
    refine ⟨P *ᵥ x, ?_⟩
    change P⁻¹ *ᵥ (P *ᵥ x) = x
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h, Matrix.one_mulVec]
  change (graphMatrix J (N.submatrix Subtype.val id * P⁻¹)).mulVecLin.range = _
  rw [hG, Matrix.mulVecLin_mul, LinearMap.range_comp, LinearMap.range_eq_top.mpr hs,
    Submodule.map_top]

set_option maxHeartbeats 900000 in
/-- A continuous family of matrices determines a continuous family of planes
when the column ranges are the specified Grassmannian points. -/
private theorem continuous_of_columnRange {X σ : Type} [TopologicalSpace X] [Fintype σ]
    (f : X → GrassmannianPoints b hd) (M : X → Matrix ι σ ℂ) (hM : Continuous M)
    (hrange : ∀ x, (grassmannianSubspace b hd (f x)).map b.equivFun.toLinearMap =
      (M x).mulVecLin.range) : Continuous f := by
  classical
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨J, D, hJ⟩ := grassmannianChartPoint_cover b hd (f x)
  have hr : (graphMatrix J D).mulVecLin.range = (M x).mulVecLin.range := by
    rw [← hrange, ← hJ, grassmannianChartSubspace]
    rfl
  have hcols (j : Inside J) :
      ∃ u : σ → ℂ, M x *ᵥ u = (graphMatrix J D).col j := by
    change ∃ u, (M x).mulVecLin u = _
    apply LinearMap.mem_range.mp
    rw [← hr]
    exact ⟨Pi.single j 1, by
      change graphMatrix J D *ᵥ Pi.single j 1 = _
      rw [Matrix.mulVec_single_one]⟩
  choose u hu using hcols
  let B : Matrix σ (Inside J) ℂ := Matrix.of fun i j ↦ u j i
  let N (y : X) := M y * B
  let P (y : X) : Matrix (Inside J) (Inside J) ℂ := (N y).submatrix Subtype.val id
  have hN : Continuous N := hM.matrix_mul continuous_const
  have hP : Continuous P := hN.matrix_submatrix _ _
  have hNx : N x = graphMatrix J D := by
    ext i j
    exact congrFun (hu j) i
  have hPx : P x = 1 := by
    dsimp only [P]
    rw [hNx]
    apply Matrix.ext
    intro i j
    simp only [Matrix.submatrix_apply, id_eq, graphMatrix, Matrix.of_apply,
      dite_eq_left i.property, Matrix.one_apply, Subtype.ext_iff]
  have hdet : (P x).det ≠ 0 := by rw [hPx, Matrix.det_one]; exact one_ne_zero
  let E (y : X) : Matrix (Outside J) (Inside J) ℂ :=
    (N y).submatrix Subtype.val id * (P y)⁻¹
  have hE : ContinuousAt E x := by
    have hinv : ContinuousAt (fun y ↦ (P y)⁻¹) x := by
      apply (continuousAt_matrix_inv (P x) ?_).comp hP.continuousAt
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ hdet
    let mul (p : Matrix (Outside J) (Inside J) ℂ × Matrix (Inside J) (Inside J) ℂ) :=
      p.1 * p.2
    have hmul : Continuous mul := continuous_fst.matrix_mul continuous_snd
    exact hmul.continuousAt.comp
      ((hN.matrix_submatrix Subtype.val id).continuousAt.prodMk hinv)
  have hlocal : ∀ᶠ y in nhds x, grassmannianChartPoint b hd J (E y) = f y := by
    filter_upwards [(isOpen_ne_fun hP.matrix_det continuous_const).mem_nhds hdet] with y hy
    have hunit : IsUnit (P y).det := isUnit_iff_ne_zero.mpr hy
    have hgraph :
        (grassmannianSubspace b hd (grassmannianChartPoint b hd J (E y))).map
          b.equivFun.toLinearMap = (N y).mulVecLin.range := by
      rw [grassmannianChartSubspace]
      exact normalizedGraph_range J (N y) hunit
    have hle : (N y).mulVecLin.range ≤ (M y).mulVecLin.range := by
      dsimp only [N]
      rw [Matrix.mulVecLin_mul]
      exact LinearMap.range_comp_le_range _ _
    apply grassmannianSubspace_injective b hd
    apply Submodule.map_injective_of_injective b.equivFun.injective
    apply Submodule.eq_of_le_of_finrank_le
    · rw [hgraph, hrange]
      exact hle
    · rw [LinearEquiv.finrank_map_eq, LinearEquiv.finrank_map_eq,
        grassmannianSubspace_finrank, grassmannianSubspace_finrank]
  exact ((continuous_chartPoint b hd J).continuousAt.comp hE).congr hlocal

private theorem chartPlane_eq_range (I : Pivot ι d) (D : Matrix (Outside I) (Inside I) ℂ) :
    grassmannianSubspace b hd (grassmannianChartPoint b hd I D) =
      (b.equivFun.symm.toLinearMap.comp (graphMatrix I D).mulVecLin).range := by
  rw [LinearMap.range_comp]
  change _ = (Matrix.toLin' (graphMatrix I D)).range.map b.equivFun.symm.toLinearMap
  rw [← grassmannianChartSubspace b hd I D, ← Submodule.map_comp,
    LinearEquiv.symm_comp, Submodule.map_id]

private theorem mem_chartPlane_iff (I : Pivot ι d) (D : Matrix (Outside I) (Inside I) ℂ) (v : V) :
    v ∈ grassmannianSubspace b hd (grassmannianChartPoint b hd I D) ↔
      b.equivFun v ∈ (graphMatrix I D).mulVecLin.range := by
  change _ ↔ b.equivFun v ∈ (Matrix.toLin' (graphMatrix I D)).range
  rw [← grassmannianChartSubspace b hd I D, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]

end GraphCharts


section Incidence

variable {U W A C : Type}
  [AddCommGroup U] [Module ℂ U] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup A] [Module ℂ A] [AddCommGroup C] [Module ℂ C]
  (e : W ≃ₗ[ℂ] U × (A × C))

private def lowerSubspace : Submodule ℂ W :=
  ((⊥ : Submodule ℂ U).prod ((⊤ : Submodule ℂ A).prod (⊥ : Submodule ℂ C))).comap e.toLinearMap

private def upperSubspace : Submodule ℂ W :=
  ((⊤ : Submodule ℂ U).prod ((⊤ : Submodule ℂ A).prod (⊥ : Submodule ℂ C))).comap e.toLinearMap

private def projectedCoordinate : W →ₗ[ℂ] U :=
  (LinearMap.fst ℂ U (A × C)).comp e.toLinearMap

private theorem mem_lowerSubspace (w : W) :
    w ∈ lowerSubspace e ↔ (e w).1 = 0 ∧ (e w).2.2 = 0 := by
  simp [lowerSubspace, Submodule.mem_prod]

private theorem mem_upperSubspace (w : W) :
    w ∈ upperSubspace e ↔ (e w).2.2 = 0 := by
  simp [upperSubspace, Submodule.mem_prod]

private theorem incidence_decompose (Q : Submodule ℂ W)
    (hlo : lowerSubspace e ≤ Q) (hhi : Q ≤ upperSubspace e) (w : W) :
    w ∈ Q ↔ (e w).1 ∈ Q.map (projectedCoordinate e) ∧ (e w).2.2 = 0 := by
  constructor
  · intro hw
    exact ⟨⟨w, hw, rfl⟩, (mem_upperSubspace e w).mp (hhi hw)⟩
  · rintro ⟨⟨v, hv, h₁⟩, h₃⟩
    have hv₃ := (mem_upperSubspace e v).mp (hhi hv)
    have hdif : w - v ∈ lowerSubspace e := by
      apply (mem_lowerSubspace e _).mpr
      change (e v).1 = (e w).1 at h₁
      simpa only [map_sub, Prod.fst_sub, Prod.snd_sub, sub_eq_zero] using
        (show (e w).1 = (e v).1 ∧ (e w).2.2 = (e v).2.2 from ⟨h₁.symm, h₃.trans hv₃.symm⟩)
    simpa only [sub_add_cancel] using Q.add_mem (hlo hdif) hv

private theorem incidence_finrank [FiniteDimensional ℂ U] [FiniteDimensional ℂ A]
    [FiniteDimensional ℂ C] (Q : Submodule ℂ W)
    (hlo : lowerSubspace e ≤ Q) (hhi : Q ≤ upperSubspace e) :
    finrank ℂ Q = finrank ℂ (Q.map (projectedCoordinate e)) + finrank ℂ A := by
  let P := Q.map (projectedCoordinate e)
  let B := (⊤ : Submodule ℂ A).prod (⊥ : Submodule ℂ C)
  have hQ : Q.map e.toLinearMap = P.prod B := by
    ext x
    rw [Submodule.mem_map_equiv]
    simpa [P, B, Submodule.mem_prod] using incidence_decompose e Q hlo hhi (e.symm x)
  have hB : finrank ℂ B = finrank ℂ A := by
    change finrank ℂ ((⊤ : Submodule ℂ A).prod (⊥ : Submodule ℂ C)) = _
    rw [(Submodule.prodEquiv _ _).finrank_eq, Module.finrank_prod,
      finrank_top, finrank_bot, add_zero]
  rw [← LinearEquiv.finrank_map_eq e Q, hQ, (Submodule.prodEquiv P B).finrank_eq,
    Module.finrank_prod, hB]

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  (bU : Basis ι ℂ U) (bW : Basis κ ℂ W)
  {d d' : ℕ} (hd : d ≤ finrank ℂ U) (hd' : d' ≤ finrank ℂ W)
  (f : GrassmannianPoints bU hd → GrassmannianPoints bW hd')
  (hf : ∀ p w, w ∈ grassmannianSubspace bW hd' (f p) ↔
    (e w).1 ∈ grassmannianSubspace bU hd p ∧ (e w).2.2 = 0)

private def incidencePoints : Set (GrassmannianPoints bW hd') :=
  {q | lowerSubspace e ≤ grassmannianSubspace bW hd' q ∧
    grassmannianSubspace bW hd' q ≤ upperSubspace e}

include hf in
private theorem mapsTo_incidencePoints : Set.MapsTo f Set.univ (incidencePoints e bW hd') := by
  intro p _
  constructor
  · intro w hw
    obtain ⟨h₁, h₃⟩ := (mem_lowerSubspace e w).mp hw
    exact (hf p w).mpr ⟨h₁.symm ▸ (grassmannianSubspace bU hd p).zero_mem, h₃⟩
  · intro w hw
    exact (mem_upperSubspace e w).mpr ((hf p w).mp hw).2

include hf in
private theorem project_image (p : GrassmannianPoints bU hd) :
    (grassmannianSubspace bW hd' (f p)).map (projectedCoordinate e) =
      grassmannianSubspace bU hd p := by
  ext u
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ((hf p w).mp hw).1
  · intro hu
    refine ⟨e.symm (u, 0, 0), (hf p _).mpr ?_, ?_⟩
    · simpa only [LinearEquiv.apply_symm_apply] using
        (show u ∈ grassmannianSubspace bU hd p ∧ (0 : C) = 0 from ⟨hu, rfl⟩)
    · change (e (e.symm (u, 0, 0))).1 = u
      rw [LinearEquiv.apply_symm_apply]

include hf in
private theorem injective_incidence : Function.Injective f := by
  intro p q hpq
  apply grassmannianSubspace_injective bU hd
  rw [← project_image e bU bW hd hd' f hf p, ← project_image e bU bW hd hd' f hf q, hpq]

variable [FiniteDimensional ℂ A] [FiniteDimensional ℂ C]

private def incidenceInverse (hDim : d' = d + finrank ℂ A) (q : incidencePoints e bW hd') :
    GrassmannianPoints bU hd := by
  letI : FiniteDimensional ℂ U := Module.Finite.of_basis bU
  let Q := grassmannianSubspace bW hd' q.val
  let P := Q.map (projectedCoordinate e)
  refine subspacePoint bU hd P ?_
  have h := incidence_finrank e Q q.property.1 q.property.2
  have hQ : finrank ℂ Q = d' := grassmannianSubspace_finrank bW hd' q.val
  exact Nat.add_right_cancel (h.symm.trans (hQ.trans hDim))

private theorem incidenceInverse_subspace (hDim : d' = d + finrank ℂ A)
    (q : incidencePoints e bW hd') :
    grassmannianSubspace bU hd (incidenceInverse e bU bW hd hd' hDim q) =
      (grassmannianSubspace bW hd' q.val).map (projectedCoordinate e) :=
  subspacePoint_subspace bU hd _ _

include hf in
private theorem incidenceInverse_right (hDim : d' = d + finrank ℂ A)
    (q : incidencePoints e bW hd') : f (incidenceInverse e bU bW hd hd' hDim q) = q.val := by
  apply grassmannianSubspace_injective bW hd'
  ext w
  rw [hf, incidenceInverse_subspace]
  exact (incidence_decompose e _ q.property.1 q.property.2 w).symm

omit [FiniteDimensional ℂ A] in
private theorem isClosed_incidenceChart (J : Pivot κ d') :
    IsClosed (grassmannianChartPoint bW hd' J ⁻¹' incidencePoints e bW hd') := by
  classical
  let fixed (a : A) : κ → ℂ := bW.equivFun (e.symm (0, a, 0))
  let cutoff : (κ → ℂ) →ₗ[ℂ] (Fin (finrank ℂ C) → ℂ) :=
    (Module.finBasis ℂ C).equivFun.toLinearMap.comp
      ((LinearMap.snd ℂ A C).comp ((LinearMap.snd ℂ U (A × C)).comp
        (e.toLinearMap.comp bW.equivFun.symm.toLinearMap)))
  have hcut (v : κ → ℂ) : cutoff v = 0 ↔ (e (bW.equivFun.symm v)).2.2 = 0 :=
    (Module.finBasis ℂ C).equivFun.map_eq_zero_iff
  let L : Set (Matrix (Outside J) (Inside J) ℂ) :=
    ⋂ a : A, {D | graphMatrix J D *ᵥ (fun i : Inside J ↦ fixed a i) = fixed a}
  let H : Set (Matrix (Outside J) (Inside J) ℂ) :=
    ⋂ v : Inside J → ℂ, {D | cutoff (graphMatrix J D *ᵥ v) = 0}
  have hset : grassmannianChartPoint bW hd' J ⁻¹' incidencePoints e bW hd' = L ∩ H := by
    ext D
    change (_ ≤ grassmannianSubspace bW hd' (grassmannianChartPoint bW hd' J D) ∧
      grassmannianSubspace bW hd' (grassmannianChartPoint bW hd' J D) ≤ _) ↔ D ∈ L ∩ H
    simp only [Set.mem_inter_iff, L, H, Set.mem_iInter, Set.mem_ofPred_eq, hcut]
    constructor
    · rintro ⟨hL, hH⟩
      constructor
      · intro a
        apply (graphMatrix_range_iff J D _).mp
        apply (mem_chartPlane_iff bW hd' J D _).mp
        apply hL
        exact (mem_lowerSubspace e _).mpr (by simp)
      · intro v
        apply (mem_upperSubspace e _).mp
        apply hH
        rw [chartPlane_eq_range bW hd' J D]
        exact LinearMap.mem_range_self _ v
    · rintro ⟨hL, hH⟩
      constructor
      · intro w hw
        obtain ⟨h₁, h₃⟩ := (mem_lowerSubspace e w).mp hw
        have h : e.symm (0, (e w).2.1, 0) = w := by
          apply e.injective
          rw [LinearEquiv.apply_symm_apply]
          exact Prod.ext h₁.symm (Prod.ext rfl h₃.symm)
        rw [← h]
        apply (mem_chartPlane_iff bW hd' J D _).mpr
        exact (graphMatrix_range_iff J D _).mpr (hL (e w).2.1)
      · intro w hw
        rw [chartPlane_eq_range bW hd' J D] at hw
        obtain ⟨v, rfl⟩ := hw
        exact (mem_upperSubspace e _).mpr (hH v)
  rw [hset]
  have hg := continuous_graphMatrix J
  have hc : Continuous cutoff := by
    have h : Continuous (cutoff.toMatrix').mulVecLin :=
      continuous_const.matrix_mulVec continuous_id
    rwa [← Matrix.toLin'_apply', Matrix.toLin'_toMatrix'] at h
  refine (isClosed_iInter fun a ↦ ?_).inter (isClosed_iInter fun v ↦ ?_)
  · exact isClosed_eq (hg.matrix_mulVec continuous_const) continuous_const
  · exact isClosed_eq (hc.comp (hg.matrix_mulVec continuous_const)) continuous_const

private theorem toMatrix_mulVec {ι₁ ι₂ : Type} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂]
    (T : (ι₁ → ℂ) →ₗ[ℂ] ι₂ → ℂ) (v : ι₁ → ℂ) : T.toMatrix' *ᵥ v = T v := by
  change Matrix.toLin' T.toMatrix' v = T v
  rw [Matrix.toLin'_toMatrix']

omit [FiniteDimensional ℂ C] in
include hf in
set_option maxHeartbeats 1200000 in
private theorem continuous_incidence : Continuous f := by
  classical
  apply continuous_fromCharts bU hd f
  intro I
  let bA := (Module.finBasis ℂ A).equivFun
  let L : (ι → ℂ) →ₗ[ℂ] κ → ℂ :=
    bW.equivFun.toLinearMap.comp (e.symm.toLinearMap.comp
      ((LinearMap.inl ℂ U (A × C)).comp bU.equivFun.symm.toLinearMap))
  let R : (Fin (finrank ℂ A) → ℂ) →ₗ[ℂ] κ → ℂ :=
    bW.equivFun.toLinearMap.comp (e.symm.toLinearMap.comp
      ((LinearMap.inr ℂ U (A × C)).comp
        ((LinearMap.inl ℂ A C).comp bA.symm.toLinearMap)))
  let M (D : Matrix (Outside I) (Inside I) ℂ) : Matrix κ (Inside I ⊕ Fin (finrank ℂ A)) ℂ :=
    Matrix.fromCols (L.toMatrix' * graphMatrix I D) R.toMatrix'
  have hL : Continuous (fun D : Matrix (Outside I) (Inside I) ℂ ↦
      L.toMatrix' * graphMatrix I D) := continuous_const.matrix_mul (continuous_graphMatrix I)
  have hM : Continuous M := by
    apply continuous_matrix
    intro i j
    cases j with
    | inl j =>
      change Continuous (fun D : Matrix (Outside I) (Inside I) ℂ ↦
        (L.toMatrix' * graphMatrix I D) i j)
      exact hL.matrix_elem i j
    | inr j =>
      change Continuous (fun _ : Matrix (Outside I) (Inside I) ℂ ↦ R.toMatrix' i j)
      exact continuous_const
  have happly (D : Matrix (Outside I) (Inside I) ℂ) (x : Inside I ⊕ Fin (finrank ℂ A) → ℂ) :
      e (bW.equivFun.symm (M D *ᵥ x)) =
        (bU.equivFun.symm (graphMatrix I D *ᵥ (x ∘ Sum.inl)), bA.symm (x ∘ Sum.inr), 0) := by
    change e (bW.equivFun.symm (Matrix.fromCols _ _ *ᵥ x)) = _
    rw [Matrix.fromCols_mulVec, ← Matrix.mulVec_mulVec, toMatrix_mulVec, toMatrix_mulVec]
    change e (bW.equivFun.symm
      (bW.equivFun (e.symm (_, 0, 0)) + bW.equivFun (e.symm (0, _, 0)))) = _
    rw [← map_add, LinearEquiv.symm_apply_apply, ← map_add, LinearEquiv.apply_symm_apply]
    simp only [Prod.mk_add_mk, add_zero, zero_add]
    rfl
  apply continuous_of_columnRange bW hd' _ M hM
  intro D
  ext z
  change z ∈ (grassmannianSubspace bW hd' (f (grassmannianChartPoint bU hd I D))).map
    bW.equivFun.toLinearMap ↔ z ∈ (M D).mulVecLin.range
  rw [Submodule.mem_map_equiv, hf]
  constructor
  · rintro ⟨hu, hc⟩
    rw [chartPlane_eq_range bU hd I D] at hu
    obtain ⟨u, hu⟩ := hu
    refine ⟨Sum.elim u (bA (e (bW.equivFun.symm z)).2.1), ?_⟩
    apply bW.equivFun.symm.injective
    apply e.injective
    change e (bW.equivFun.symm (M D *ᵥ _)) = _
    rw [happly]
    simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr, LinearEquiv.symm_apply_apply]
    exact Prod.ext hu (Prod.ext rfl hc.symm)
  · rintro ⟨x, hx⟩
    change M D *ᵥ x = z at hx
    rw [← hx, happly]
    refine ⟨?_, rfl⟩
    rw [chartPlane_eq_range bU hd I D]
    exact LinearMap.mem_range_self _ (x ∘ Sum.inl)

private theorem continuous_incidenceInverse_chart (hDim : d' = d + finrank ℂ A)
    (J : Pivot κ d') :
    Continuous (fun D : grassmannianChartPoint bW hd' J ⁻¹' incidencePoints e bW hd' ↦
      incidenceInverse e bU bW hd hd' hDim ⟨grassmannianChartPoint bW hd' J D.val, D.property⟩) := by
  classical
  let T : (κ → ℂ) →ₗ[ℂ] ι → ℂ :=
    bU.equivFun.toLinearMap.comp ((projectedCoordinate e).comp bW.equivFun.symm.toLinearMap)
  let M (D : grassmannianChartPoint bW hd' J ⁻¹' incidencePoints e bW hd') :=
    T.toMatrix' * graphMatrix J D.val
  have hM : Continuous M :=
    continuous_const.matrix_mul ((continuous_graphMatrix J).comp continuous_subtype_val)
  apply continuous_of_columnRange bU hd _ M hM
  intro D
  rw [incidenceInverse_subspace]
  change ((grassmannianSubspace bW hd' (grassmannianChartPoint bW hd' J D.val)).map
    (projectedCoordinate e)).map bU.equivFun.toLinearMap = _
  rw [chartPlane_eq_range bW hd' J D.val, LinearMap.range_comp, ← Submodule.map_comp,
    ← Submodule.map_comp]
  dsimp only [M]
  rw [Matrix.mulVecLin_mul, ← Matrix.toLin'_apply' T.toMatrix', Matrix.toLin'_toMatrix',
    LinearMap.range_comp]
  rfl

include hf in
set_option maxHeartbeats 1000000 in
private theorem isClosedMap_incidence (hDim : d' = d + finrank ℂ A) : IsClosedMap f := by
  intro S hS
  apply isClosed_fromCharts bW hd'
  intro J
  let c := grassmannianChartPoint bW hd' J
  let D := c ⁻¹' incidencePoints e bW hd'
  let q (x : D) : incidencePoints e bW hd' := ⟨c x.val, x.property⟩
  let g (x : D) : GrassmannianPoints bU hd := incidenceInverse e bU bW hd hd' hDim (q x)
  have hg : Continuous g := continuous_incidenceInverse_chart e bU bW hd hd' hDim J
  have hD : IsClosed D := isClosed_incidenceChart e bW hd' J
  have hinj := injective_incidence e bU bW hd hd' f hf
  have hfg (x : D) : f (g x) = c x.val :=
    incidenceInverse_right e bU bW hd hd' f hf hDim (q x)
  -- The image of a closed source set pulls back to a closed set inside the chart locus.
  have hset : c ⁻¹' (f '' S) = Subtype.val '' (g ⁻¹' S) := by
    ext x
    constructor
    · rintro ⟨p, hp, heq⟩
      have hx : x ∈ D := by
        change c x ∈ incidencePoints e bW hd'
        rw [← heq]
        exact mapsTo_incidencePoints e bU bW hd hd' f hf (Set.mem_univ p)
      refine ⟨⟨x, hx⟩, ?_, rfl⟩
      change g ⟨x, hx⟩ ∈ S
      rw [hinj ((hfg ⟨x, hx⟩).trans heq.symm)]
      exact hp
    · rintro ⟨y, hy, rfl⟩
      exact ⟨g y, hy, hfg y⟩
  change IsClosed (c ⁻¹' (f '' S))
  rw [hset]
  exact hD.isClosedEmbedding_subtypeVal.isClosedMap _ (hS.preimage hg)

end Incidence

theorem incidenceClosedEmbedding : IncidenceClosedEmbedding := by
  intro U W A C ι κ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bU bW e d d' hd hd' hDim f hf
  refine ⟨IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_incidence e bU bW hd hd' f hf)
    (injective_incidence e bU bW hd hd' f hf)
    (isClosedMap_incidence e bU bW hd hd' f hf hDim), ?_⟩
  change Set.range f = incidencePoints e bW hd'
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    exact mapsTo_incidencePoints e bU bW hd hd' f hf (Set.mem_univ p)
  · intro hq
    let y : incidencePoints e bW hd' := ⟨q, hq⟩
    exact ⟨incidenceInverse e bU bW hd hd' hDim y,
      incidenceInverse_right e bU bW hd hd' f hf hDim y⟩

end
end RepTheorySurvey.Geometric.GrassmannianIncidenceTopology
