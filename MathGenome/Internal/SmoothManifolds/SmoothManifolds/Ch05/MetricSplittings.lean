import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch05.BundleOperations
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch05.MetricSplittings

import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch05.BundleMetrics
namespace SmoothManifolds.MetricSplittings
open ModelData AtlasData MapData ProductData BundleData FrameData BundleMetricData
  ConstantRankData BundleOperationsData MetricSplittingData Bundle Set Filter Module
open scoped Topology
universe u v w z t x y

section Morphisms
variable {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {κ : Type t}
  {E : M → Type w} {F : M → Type z}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [∀ p, AddCommGroup (F p)] [∀ p, Module ℝ (F p)]
  [TopologicalSpace (TotalSpace (Euclidean r) E)]
  [TopologicalSpace (TotalSpace (Euclidean s) F)]
  (B : SmoothVectorBundle S r ι E) (D : SmoothVectorBundle S s κ F)

/-- A fiberwise linear map is smooth when its coordinate columns are smooth.
Only a neighborhood of each base point is tested. -/
theorem smooth_of_columns (L : (p : M) → E p →ₗ[ℝ] F p)
    (hL : ∀ p, ∃ i j, p ∈ B.baseSet i ∧ p ∈ D.baseSet j ∧
      ∀ l : Fin r, VectorSmoothAt S.smoothStructure.val
        (fun x => ((D.trivialization j) ⟨x, L x
          ((B.trivialization i).symm x (Pi.single l 1))⟩).2) p) :
    IsSmoothMap B.totalManifold D.totalManifold
      (fun q => (⟨q.proj, L q.proj q.snd⟩ : TotalSpace (Euclidean s) F)) := by
  classical
  intro q
  obtain ⟨i, j, hi, hj, hcol⟩ := hL q.proj
  let T : M → Euclidean r →L[ℝ] Euclidean s := fun x =>
    QuotientBundles.columnOperator (fun l => ((D.trivialization j)
      ⟨x, L x ((B.trivialization i).symm x (Pi.single l 1))⟩).2)
  have hT := BundleOperations.columnOperator_smooth hcol
  have ht := hT.comp S.smoothStructure.property.1.1 (B.projection_smooth q)
  have hv := ht.clm_apply (Frames.trivializationCoordinates_smoothAt B i q hi)
  apply Frames.smoothAt_from_trivialization D B.totalManifold.smoothStructure.property.1
    j hj (B.projection_smooth q) hv (fun _ => rfl)
  have hiO : IsOpen (B.baseSet i) :=
    B.trivialization_baseSet i ▸ (B.trivialization i).open_baseSet
  have hjO : IsOpen (D.baseSet j) :=
    D.trivialization_baseSet j ▸ (D.trivialization j).open_baseSet
  filter_upwards [(B.projection_smooth q).1.preimage_mem_nhds
    ((hiO.inter hjO).mem_nhds ⟨hi, hj⟩)] with y hy
  change D.fiberCoordinates j y.proj hy.2 (L y.proj y.snd) =
    T y.proj (B.fiberCoordinates i y.proj hy.1 y.snd)
  let e := B.fiberCoordinates i y.proj hy.1
  have he : y.snd = ∑ l : Fin r, (e y.snd) l • e.symm (Pi.single l 1) := by
    simpa using (congrArg e.symm ((Pi.basisFun ℝ (Fin r)).sum_equivFun (e y.snd))).symm
  conv_lhs => rw [he]
  simp only [map_sum, map_smul, T, QuotientBundles.columnOperator_apply,
    BundleData.SmoothVectorBundle.fiberCoordinates_apply,
    BundleData.SmoothVectorBundle.fiberCoordinates_symm_apply]
  rfl

/-- A smooth fiberwise linear bijection has smooth inverse. This is matrix
inversion on the open set of invertible rectangular operators; equality of the
fiber dimensions follows from the given equivalences, rather than a hypothesis. -/
theorem inverse_smooth (e : (p : M) → E p ≃ₗ[ℝ] F p)
    (he : IsSmoothMap B.totalManifold D.totalManifold
      (fun q => (⟨q.proj, e q.proj q.snd⟩ : TotalSpace (Euclidean s) F))) :
    IsSmoothMap D.totalManifold B.totalManifold
      (fun q => (⟨q.proj, (e q.proj).symm q.snd⟩ : TotalSpace (Euclidean r) E)) := by
  let A : SmoothBundleMorphism B D := ⟨fun p => (e p).toLinearMap, he⟩
  apply smooth_of_columns D B (fun p => (e p).symm.toLinearMap)
  intro p
  obtain ⟨i, hi⟩ := B.covers p
  obtain ⟨j, hj⟩ := D.covers p
  let T := ConstantRankBundles.morphismMatrix B D A i j
  have hT := ConstantRankBundles.morphismMatrix_smoothAt B D A i j p hi hj
  let c (x : M) (hxi : x ∈ B.baseSet i) (hxj : x ∈ D.baseSet j) :=
    ((B.fiberCoordinates i x hxi).symm.trans (e x)).trans
      (D.fiberCoordinates j x hxj)
  have hTc (x : M) (hxi : x ∈ B.baseSet i) (hxj : x ∈ D.baseSet j) :
      T x = (c x hxi hxj).toContinuousLinearEquiv.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro v
    exact ConstantRankBundles.morphismMatrix_apply B D A i j x hxi hxj v
  have hInv : (T p).IsInvertible := by
    rw [hTc p hi hj]
    exact ContinuousLinearMap.isInvertible_equiv
  have hTi := hT.inverse hInv
  refine ⟨j, i, hj, hi, fun l => ?_⟩
  have hs := hTi.clm_apply (FrameData.VectorSmoothAt.const _ (Pi.single l 1) p)
  apply hs.congr
  have hiO : IsOpen (B.baseSet i) := B.trivialization_baseSet i ▸ (B.trivialization i).open_baseSet
  have hjO : IsOpen (D.baseSet j) := D.trivialization_baseSet j ▸ (D.trivialization j).open_baseSet
  filter_upwards [(hiO.inter hjO).mem_nhds ⟨hi, hj⟩] with x hx
  change (T x).inverse (Pi.single l 1) = _
  rw [hTc x hx.1 hx.2, ContinuousLinearMap.inverse_equiv]
  rfl

end Morphisms

section DualMaps
variable {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {κ : Type t}
  {E : M → Type w} {F : M → Type z}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [∀ p, AddCommGroup (F p)] [∀ p, Module ℝ (F p)]
  [TopologicalSpace (TotalSpace (Euclidean r) E)]
  [TopologicalSpace (TotalSpace (Euclidean s) F)]
  (B : SmoothVectorBundle S r ι E) (D : SmoothVectorBundle S s κ F)

 theorem dual_fiberCoordinates (BD : DualBundle B) (i : ι) (p : M)
    (hp : p ∈ B.baseSet i) :
    letI := BD.space.topology
    BD.space.bundle.fiberCoordinates i p ((BD.baseSet i).symm ▸ hp) =
      BundleOperations.dualCoordinates (B.fiberCoordinates i p hp) := by
  letI := BD.space.topology
  apply LinearEquiv.ext
  intro lam
  funext j
  rw [BundleOperations.dualCoordinates_apply]
  exact BD.coordinates i p hp lam j

/-- Transposition preserves smooth bundle morphisms, with the canonical dual
structures rather than newly chosen dual coordinates. -/
theorem dual_map_smooth (A : SmoothBundleMorphism B D)
    (BD : DualBundle B) (DD : DualBundle D) :
    letI := BD.space.topology; letI := DD.space.topology
    IsSmoothMap DD.space.bundle.totalManifold BD.space.bundle.totalManifold
      (fun q => (⟨q.proj, (A.linearMap q.proj).dualMap q.snd⟩ :
        TotalSpace (Euclidean r) (fun p => Module.Dual ℝ (E p)))) := by
  classical
  letI := BD.space.topology
  letI := DD.space.topology
  apply smooth_of_columns DD.space.bundle BD.space.bundle (fun p => (A.linearMap p).dualMap)
  intro p
  obtain ⟨i, hi⟩ := B.covers p
  obtain ⟨j, hj⟩ := D.covers p
  refine ⟨j, i, (DD.baseSet j).symm ▸ hj, (BD.baseSet i).symm ▸ hi, fun l => ?_⟩
  have hT := ConstantRankBundles.morphismMatrix_smoothAt B D A i j p hi hj
  have hs := FrameData.VectorSmoothAt.pi (fun k : Fin r =>
    (hT.clm_apply (FrameData.VectorSmoothAt.const _ (Pi.single k 1) p)).postcomp
      (ContinuousLinearMap.proj l).contDiff)
  apply hs.congr
  have hiO : IsOpen (B.baseSet i) := B.trivialization_baseSet i ▸ (B.trivialization i).open_baseSet
  have hjO : IsOpen (D.baseSet j) := D.trivialization_baseSet j ▸ (D.trivialization j).open_baseSet
  filter_upwards [(hiO.inter hjO).mem_nhds ⟨hi, hj⟩] with x hx
  funext k
  rw [ConstantRankBundles.morphismMatrix_apply B D A i j x hx.1 hx.2]
  rw [BD.coordinates i x hx.1]
  change D.fiberCoordinates j x hx.2
      (A.linearMap x ((B.trivialization i).symm x (Pi.single k 1))) l =
    (DD.space.bundle.fiberCoordinates j x ((DD.baseSet j).symm ▸ hx.2)).symm
      (Pi.single l 1) (A.linearMap x ((B.trivialization i).symm x (Pi.single k 1)))
  rw [dual_fiberCoordinates D DD j x hx.2, BundleOperations.dualCoordinates_symm_apply]
  simp [Pi.single_apply]

end DualMaps

section Subbundle
variable {n r k : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E) (K : (p : M) → Submodule ℝ (E p))

/-- Chosen adapted ambient frames are construction data, never extra assumptions. -/
structure SubbundleCover where
  domain : M → Set M
  isOpen_domain : ∀ i, IsOpen (domain i)
  mem_domain : ∀ i, i ∈ domain i
  rank_le : ∀ i : M, k ≤ r
  frame : ∀ i, LocalFrame B (domain i) (isOpen_domain i)
  adapted : ∀ i (p : domain i) (v : E p.val),
    v ∈ K p.val ↔ ∀ j : Fin r, k ≤ j.val → ((frame i).basis p).equivFun v j = 0

noncomputable def subbundleCover (hK : IsSmoothSubbundle B k K) :
    SubbundleCover B K (k := k) := by
  classical
  choose hk U hU hp b hb using hK
  exact ⟨U, hU, hp, hk, b, hb⟩

namespace SubbundleCover
variable {B K}
variable (C : SubbundleCover B K (k := k))

noncomputable def coord (i : M) (p : M) (hp : p ∈ C.domain i) : K p ≃ₗ[ℝ] Euclidean k :=
  BundleOperations.adaptedCoordinates ((C.frame i).basis ⟨p, hp⟩) (K p)
    (C.rank_le i) (C.adapted i ⟨p, hp⟩)

/-- Analysis in an ambient adapted frame supplies the subbundle transition
columns. Totalization only gives irrelevant values outside the chart domains. -/
noncomputable def column (i j : M) (l : Fin k) (p : C.domain i) : Euclidean k :=
  fun m => (frameAnalysis (C.frame j)
    (⟨p.val, (C.frame i).section_ (l.castLE (C.rank_le i)) p⟩ :
      TotalSpace (Euclidean r) E)).2 (m.castLE (C.rank_le j))

theorem column_smooth (i j : M) (l : Fin k) (p : C.domain i)
    (hp : p.val ∈ C.domain j) :
    VectorSmoothAt (openSubsetAtlas S.smoothStructure.val (C.domain i) (C.isOpen_domain i))
      (C.column i j l) p := by
  have hs := (C.frame i).smooth (l.castLE (C.rank_le i)) p
  have ha := Frames.frameAnalysis_smooth B (C.domain j) (C.isOpen_domain j) (C.frame j)
    (⟨p.val, (C.frame i).section_ (l.castLE (C.rank_le i)) p⟩ : TotalSpace (Euclidean r) E) hp
  have hc := manifoldContDiffAt_comp B.totalManifold.smoothStructure.property.1.1 hs ha
  have hv := (Frames.trivialAtlas_snd_smooth B _).comp (Frames.trivialAtlas_isContDiffAtlas B).1 hc
  exact hv.postcomp (ContinuousLinearMap.pi (fun m : Fin k =>
    ContinuousLinearMap.proj (m.castLE (C.rank_le j)))).contDiff

theorem column_eq (i j : M) (p : M) (hi : p ∈ C.domain i) (hj : p ∈ C.domain j)
    (l : Fin k) :
    C.column i j l ⟨p, hi⟩ = C.coord j p hj ((C.coord i p hi).symm (Pi.single l 1)) := by
  funext m
  rw [show (C.column i j l ⟨p, hi⟩) m =
    (frameAnalysis (C.frame j) (⟨p, (C.frame i).section_ (l.castLE (C.rank_le i)) ⟨p,hi⟩⟩ :
      TotalSpace (Euclidean r) E)).2 (m.castLE (C.rank_le j)) from rfl]
  rw [Frames.frameAnalysis_of_mem B (C.domain j) (C.isOpen_domain j) (C.frame j) _ hj]
  change ((C.frame j).basis ⟨p,hj⟩).equivFun
    ((C.frame i).section_ (l.castLE (C.rank_le i)) ⟨p,hi⟩) (m.castLE (C.rank_le j)) = _
  change _ = ((C.frame j).basis ⟨p,hj⟩).equivFun
    ((C.coord i p hi).symm (Pi.single l 1)).val (m.castLE (C.rank_le j))
  rw [coord, BundleOperations.adaptedCoordinates_symm_basis, (C.frame i).basis_eq]

noncomputable def presentation : BundleOperations.CoordinatePresentation S k M (fun p => K p) where
  domain := C.domain
  isOpen_domain := C.isOpen_domain
  covers p := ⟨p, C.mem_domain p⟩
  coord := C.coord
  transition i j p := QuotientBundles.columnOperator (fun l => totalize (C.column i j l) p)
  transition_eq i j p hi hj v := by
    classical
    rw [QuotientBundles.columnOperator_apply]
    simp only [totalize_of_mem _ _ hi, C.column_eq i j p hi hj]
    have he := (Pi.basisFun ℝ (Fin k)).sum_equivFun v
    conv_rhs => rw [← he]
    simp only [map_sum, map_smul, Pi.basisFun_equivFun, LinearEquiv.refl_apply,
      Pi.basisFun_apply]
  smooth i j p hi hj := BundleOperations.columnOperator_smooth
    (fun l => (C.column_smooth i j l ⟨p,hi⟩ hj).totalize (C.isOpen_domain i))

include C
/-- The induced bundle on the actual subspaces has a smooth inclusion. -/
theorem exists_induced_bundle :
    ∃ V : BundleSpace S k M (fun p => K p), letI := V.topology
    IsSmoothMap V.bundle.totalManifold B.totalManifold
      (fun q => (⟨q.proj, q.snd.val⟩ : TotalSpace (Euclidean r) E)) := by
  classical
  obtain ⟨V, hbase, hcoord⟩ := BundleOperations.CoordinatePresentation.exists_bundle (presentation C)
  dsimp only [presentation] at hbase hcoord
  letI := V.topology
  refine ⟨V, ?_⟩
  apply smooth_of_columns V.bundle B (fun p => (K p).subtype)
  intro p
  obtain ⟨j, hj⟩ := B.covers p
  let i := p
  have hi : p ∈ C.domain i := C.mem_domain p
  refine ⟨i, j, (hbase i).symm ▸ hi, hj, fun l => ?_⟩
  let f : (x : C.domain i) → E x.val :=
    (C.frame i).section_ (l.castLE (C.rank_le i))
  have hs := (Frames.sectionCoordinates_smoothAt B (C.domain i) (C.isOpen_domain i)
    j f ⟨p,hi⟩ hj ((C.frame i).smooth (l.castLE (C.rank_le i)) ⟨p,hi⟩)).totalize
      (C.isOpen_domain i)
  apply hs.congr
  filter_upwards [(C.isOpen_domain i).mem_nhds hi] with x hx
  rw [totalize_of_mem _ _ hx]
  have he : (V.bundle.trivialization i).symm x (Pi.single l 1) =
      (C.coord i x hx).symm (Pi.single l 1) := by
    change (V.bundle.fiberCoordinates i x ((hbase i).symm ▸ hx)).symm _ = _
    apply (V.bundle.fiberCoordinates i x ((hbase i).symm ▸ hx)).injective
    rw [LinearEquiv.apply_symm_apply]
    change _ = ((V.bundle.trivialization i) ⟨x, _⟩).2
    rw [hcoord i x hx, LinearEquiv.apply_symm_apply]
  rw [he]
  change ((B.trivialization j) ⟨x, f ⟨x,hx⟩⟩).2 = _
  change ((B.trivialization j) ⟨x, f ⟨x,hx⟩⟩).2 =
    ((B.trivialization j) ⟨x, ((C.coord i x hx).symm (Pi.single l 1)).val⟩).2
  rw [coord, BundleOperations.adaptedCoordinates_symm_basis, (C.frame i).basis_eq]


end SubbundleCover
end Subbundle

section Sums
variable {n l r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {κ : Type t} {τ : Type*}
  {L : M → Type*} {E : M → Type w} {F : M → Type z}
  [∀ p, AddCommGroup (L p)] [∀ p, Module ℝ (L p)]
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [∀ p, AddCommGroup (F p)] [∀ p, Module ℝ (F p)]
  [TopologicalSpace (TotalSpace (Euclidean l) L)]
  [TopologicalSpace (TotalSpace (Euclidean r) E)]
  [TopologicalSpace (TotalSpace (Euclidean s) F)]
  (A : SmoothVectorBundle S l ι L) (B : SmoothVectorBundle S r κ E)
  (D : SmoothVectorBundle S s τ F)

/-- The prescribed coordinate blocks determine the entire direct-sum chart. -/
theorem sum_fiberCoordinates (V : DirectSumBundle A D) (i : ι) (j : τ) (p : M)
    (hi : p ∈ A.baseSet i) (hj : p ∈ D.baseSet j) :
    letI := V.space.topology
    V.space.bundle.fiberCoordinates (i,j) p ((V.baseSet (i,j)).symm ▸ ⟨hi,hj⟩) =
      ((A.fiberCoordinates i p hi).prodCongr (D.fiberCoordinates j p hj)).trans
        (BundleOperations.sumCoordinates l s) := by
  letI := V.space.topology
  apply LinearEquiv.ext
  intro v
  funext m
  refine Fin.addCases (fun m => ?_) (fun m => ?_) m
  · rw [LinearEquiv.trans_apply, BundleOperations.sumCoordinates_left]
    exact V.coordinates_left (i,j) p ((V.baseSet (i,j)).symm ▸ ⟨hi,hj⟩) v m
  · rw [LinearEquiv.trans_apply, BundleOperations.sumCoordinates_right]
    exact V.coordinates_right (i,j) p ((V.baseSet (i,j)).symm ▸ ⟨hi,hj⟩) v m

/-- The sum of two smooth fiberwise linear maps is smooth on the canonical
bundle direct sum. -/
theorem coprod_smooth (I : SmoothBundleMorphism A B) (J : SmoothBundleMorphism D B)
    (V : DirectSumBundle A D) :
    letI := V.space.topology
    IsSmoothMap V.space.bundle.totalManifold B.totalManifold
      (fun q => (⟨q.proj, I.linearMap q.proj q.snd.1 + J.linearMap q.proj q.snd.2⟩ :
        TotalSpace (Euclidean r) E)) := by
  letI := V.space.topology
  apply smooth_of_columns V.space.bundle B
    (fun p => (I.linearMap p).coprod (J.linearMap p))
  intro p
  obtain ⟨i, hi⟩ := A.covers p
  obtain ⟨j, hj⟩ := D.covers p
  obtain ⟨k, hk⟩ := B.covers p
  refine ⟨(i,j), k, (V.baseSet (i,j)).symm ▸ ⟨hi,hj⟩, hk, fun m => ?_⟩
  let v := (BundleOperations.sumCoordinates l s).symm (Pi.single m 1)
  have hI := (ConstantRankBundles.morphismMatrix_smoothAt A B I i k p hi hk).clm_apply
    (FrameData.VectorSmoothAt.const _ v.1 p)
  have hJ := (ConstantRankBundles.morphismMatrix_smoothAt D B J j k p hj hk).clm_apply
    (FrameData.VectorSmoothAt.const _ v.2 p)
  have hs := (hI.prod hJ).postcomp (contDiff_fst.add contDiff_snd)
  apply hs.congr
  have hAO : IsOpen (A.baseSet i) := A.trivialization_baseSet i ▸ (A.trivialization i).open_baseSet
  have hDO : IsOpen (D.baseSet j) := D.trivialization_baseSet j ▸ (D.trivialization j).open_baseSet
  have hBO : IsOpen (B.baseSet k) := B.trivialization_baseSet k ▸ (B.trivialization k).open_baseSet
  filter_upwards [((hAO.inter hDO).inter hBO).mem_nhds ⟨⟨hi,hj⟩,hk⟩] with x hx
  rw [ConstantRankBundles.morphismMatrix_apply A B I i k x hx.1.1 hx.2,
    ConstantRankBundles.morphismMatrix_apply D B J j k x hx.1.2 hx.2, ← map_add]
  have hpair : (V.space.bundle.trivialization (i,j)).symm x (Pi.single m 1) =
      ((A.fiberCoordinates i x hx.1.1).symm v.1,
       (D.fiberCoordinates j x hx.1.2).symm v.2) := by
    change (V.space.bundle.fiberCoordinates (i,j) x
      ((V.baseSet (i,j)).symm ▸ hx.1)).symm _ = _
    rw [sum_fiberCoordinates A D V i j x hx.1.1 hx.1.2]
    rfl
  rw [hpair]
  rfl

end Sums

section Metric
variable {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E) (g : SmoothFiberMetric B)

theorem metric_nondegenerate (p : M) : (g.form p).Nondegenerate := by
  constructor
  · intro x hx
    by_contra h
    exact (ne_of_gt (g.positive p x h)) (hx x)
  · intro x hx
    by_contra h
    exact (ne_of_gt (g.positive p x h)) (hx x)

noncomputable def metricEquiv (p : M) : E p ≃ₗ[ℝ] Module.Dual ℝ (E p) := by
  letI := ConstantRankBundles.finite_fiber B p
  exact (g.form p).toDual (metric_nondegenerate B g p)

@[simp] theorem metricEquiv_apply (p : M) (x y : E p) :
    metricEquiv B g p x y = g.form p x y := rfl

/-- Gram coefficients are precisely the columns of the metric-to-dual map. -/
theorem metric_map_smooth (D : DualBundle B) :
    letI := D.space.topology
    IsSmoothMap B.totalManifold D.space.bundle.totalManifold
      (fun q => (⟨q.proj, metricEquiv B g q.proj q.snd⟩ :
        TotalSpace (Euclidean r) (fun p => Module.Dual ℝ (E p)))) := by
  letI := D.space.topology
  apply smooth_of_columns B D.space.bundle (fun p => (metricEquiv B g p).toLinearMap)
  intro p
  obtain ⟨i, hi⟩ := B.covers p
  refine ⟨i, i, hi, (D.baseSet i).symm ▸ hi, fun l => ?_⟩
  apply (FrameData.VectorSmoothAt.pi (fun k => g.smooth i l k p hi)).congr
  have hO : IsOpen (B.baseSet i) := B.trivialization_baseSet i ▸ (B.trivialization i).open_baseSet
  filter_upwards [hO.mem_nhds hi] with x hx
  funext k
  exact (D.coordinates i x hx _ k).symm

noncomputable def metricIso (D : DualBundle B) :
    letI := D.space.topology; SmoothBundleIso B D.space.bundle := by
  letI := D.space.topology
  exact ⟨metricEquiv B g, metric_map_smooth B g D,
    inverse_smooth B D.space.bundle (metricEquiv B g) (metric_map_smooth B g D)⟩

end Metric

section Orthogonal
variable {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E) (g : SmoothFiberMetric B)
  (K : (p : M) → Submodule ℝ (E p))

theorem metric_isCompl (p : M) : IsCompl (K p) (orthogonal B g K p) := by
  letI := ConstantRankBundles.finite_fiber B p
  apply (LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint
    (B := g.form p) (LinearMap.BilinForm.IsSymm.isRefl ⟨g.symmetric p⟩)).mpr
  rw [disjoint_iff_inf_le]
  intro v hv
  change v = 0
  by_contra hn
  exact (ne_of_gt (g.positive p v hn)) (hv.2 v hv.1)

/-- All the construction uses the prescribed metric. Restriction to the dual
of K is surjective, so its constant-rank kernel is exactly K-perp. -/
theorem orthogonal_splitting_of_metric {k : ℕ} (hK : IsSmoothSubbundle B k K) :
    Nonempty (OrthogonalSplitting B g K k) := by
  classical
  obtain ⟨L, hL⟩ := (subbundleCover B K hK).exists_induced_bundle
  letI := L.topology
  let i : SmoothBundleMorphism L.bundle B := ⟨fun p => (K p).subtype, hL⟩
  obtain ⟨BD⟩ := BundleOperations.exists_dual B
  obtain ⟨LD⟩ := BundleOperations.exists_dual L.bundle
  letI := BD.space.topology
  letI := LD.space.topology
  let R : SmoothBundleMorphism B LD.space.bundle := {
    linearMap p := ((K p).subtype.dualMap).comp (metricEquiv B g p).toLinearMap
    smooth := by
      intro q
      exact manifoldContDiffAt_comp BD.space.bundle.totalManifold.smoothStructure.property.1.1
        (metric_map_smooth B g BD q) (dual_map_smooth L.bundle B i LD BD _) }
  have hsurj (p : M) : Function.Surjective (R.linearMap p) :=
    (LinearMap.dualMap_surjective_of_injective (K p).injective_subtype).comp
      (metricEquiv B g p).surjective
  have hrank (p : M) : finrank ℝ (LinearMap.range (R.linearMap p)) = k := by
    rw [LinearMap.range_eq_top.mpr (hsurj p), finrank_top]
    exact ConstantRankBundles.finrank_fiber LD.space.bundle p
  have hker (p : M) : LinearMap.ker (R.linearMap p) = orthogonal B g K p := by
    ext v
    constructor
    · intro hv y hy
      have h := LinearMap.congr_fun (LinearMap.mem_ker.mp hv) (⟨y,hy⟩ : K p)
      change g.form p v y = 0 at h
      rw [g.symmetric p]
      exact h
    · intro hv
      apply LinearMap.mem_ker.mpr
      apply LinearMap.ext
      intro y
      change g.form p v y.val = 0
      rw [g.symmetric p]
      exact hv y.val y.property
  have hperp : IsSmoothSubbundle B (r-k) (orthogonal B g K) := by
    simpa only [hker] using
      (ConstantRankBundles.kernel_image_subbundles B LD.space.bundle R k hrank).1
  obtain ⟨P, hP⟩ := (subbundleCover B (orthogonal B g K) hperp).exists_induced_bundle
  letI := P.topology
  obtain ⟨V⟩ := BundleOperations.exists_directSum L.bundle P.bundle
  letI := V.space.topology
  let j : SmoothBundleMorphism P.bundle B := ⟨fun p => (orthogonal B g K p).subtype, hP⟩
  let e (p : M) : (K p × orthogonal B g K p) ≃ₗ[ℝ] E p :=
    Submodule.prodEquivOfIsCompl _ _ (metric_isCompl B g K p)
  have he : IsSmoothMap V.space.bundle.totalManifold B.totalManifold
      (fun q => (⟨q.proj, e q.proj q.snd⟩ : TotalSpace (Euclidean r) E)) :=
    coprod_smooth L.bundle B P.bundle i j V
  exact ⟨{
    complement_smooth := hperp
    complementary := metric_isCompl B g K
    left := L
    right := P
    left_inclusion := hL
    right_inclusion := hP
    sum := V
    iso := ⟨e, he, inverse_smooth V.space.bundle B e he⟩
    canonical := fun _ _ => rfl }⟩

end Orthogonal

/-- The metric orthogonal complement gives the canonical smooth splitting. -/
theorem orthogonal_splitting :
    Specs.SmoothManifolds.Ch05.MetricSplittings.orthogonal_splittingType.{u,v,w} := by
  intro n r a M _ S ι E _ _ _ B g K k hK
  exact orthogonal_splitting_of_metric B g K hK

section Algebra
variable {V W : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W]

/-- Restricting a surjection to a complement of its kernel is bijective. -/
theorem restriction_bijective (q : V →ₗ[ℝ] W) (hq : Function.Surjective q)
    (P : Submodule ℝ V) (hP : IsCompl (LinearMap.ker q) P) :
    Function.Bijective (q.comp P.subtype) := by
  constructor
  · intro x y h
    apply Subtype.ext
    apply sub_eq_zero.mp
    have hker : x.val-y.val ∈ LinearMap.ker q := by
      change q (x.val-y.val) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr h
    have hz : x.val-y.val ∈ (⊥ : Submodule ℝ V) := by
      rw [← hP.inf_eq_bot]
      exact ⟨hker, P.sub_mem x.property y.property⟩
    exact hz
  · intro y
    obtain ⟨v, hv⟩ := hq y
    let e := Submodule.prodEquivOfIsCompl _ _ hP
    let d := e.symm v
    refine ⟨d.2, ?_⟩
    have hd : d.1.val + d.2.val = v := e.apply_symm_apply v
    have hk : q d.1.val = 0 := d.1.property
    have hh := congrArg q hd
    rw [map_add, hk, zero_add, hv] at hh
    exact hh

/-- A right inverse and fiberwise exactness give the canonical split linear
isomorphism, with no dimension or positive-rank restrictions. -/
theorem split_coprod_bijective {U : Type*} [AddCommGroup U] [Module ℝ U]
    (i : U →ₗ[ℝ] V) (q : V →ₗ[ℝ] W) (t : W →ₗ[ℝ] V)
    (hi : Function.Injective i) (he : LinearMap.range i = LinearMap.ker q)
    (ht : q.comp t = LinearMap.id) : Function.Bijective (i.coprod t) := by
  have hqi (x : U) : q (i x) = 0 := by
    apply LinearMap.mem_ker.mp
    rw [← he]
    exact ⟨x,rfl⟩
  have hqt (x : W) : q (t x) = x := LinearMap.congr_fun ht x
  constructor
  · intro x y h
    have h₂ : x.2 = y.2 := by
      have hh := congrArg q h
      simpa only [LinearMap.coprod_apply, map_add, hqi, hqt, zero_add] using hh
    have h₁ : x.1 = y.1 := hi (by
      simpa only [LinearMap.coprod_apply, h₂, add_left_inj] using h)
    exact Prod.ext h₁ h₂
  · intro v
    have hk : v - t (q v) ∈ LinearMap.range i := by
      rw [he]
      change q (v-t (q v)) = 0
      rw [map_sub, hqt, sub_self]
    obtain ⟨x,hx⟩ := hk
    refine ⟨(x,q v), ?_⟩
    change i x + t (q v) = v
    rw [hx, sub_add_cancel]

end Algebra

/-- Every smooth short exact sequence splits, with the prescribed sum map. -/
theorem shortExact_splitting :
  ∀ {n l r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type t} {κ : Type v} {τ : Type y}
    {L : M → Type z} {E : M → Type w} {F : M → Type x}
    [∀ p, AddCommGroup (L p)] [∀ p, Module ℝ (L p)]
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [∀ p, AddCommGroup (F p)] [∀ p, Module ℝ (F p)]
    [TopologicalSpace (TotalSpace (Euclidean l) L)]
    [TopologicalSpace (TotalSpace (Euclidean r) E)]
    [TopologicalSpace (TotalSpace (Euclidean s) F)]
    (A : SmoothVectorBundle S l ι L) (B : SmoothVectorBundle S r κ E)
    (D : SmoothVectorBundle S s τ F)
    (i : SmoothBundleMorphism A B) (q : SmoothBundleMorphism B D),
    (∀ p, Function.Injective (i.linearMap p)) →
    (∀ p, Function.Surjective (q.linearMap p)) →
    (∀ p, LinearMap.range (i.linearMap p) = LinearMap.ker (q.linearMap p)) →
    ∃ t : SmoothBundleMorphism D B,
      (∀ p, (q.linearMap p).comp (t.linearMap p) = LinearMap.id) ∧
      ∀ V : DirectSumBundle A D, letI := V.space.topology
      ∃ e : SmoothBundleIso V.space.bundle B,
        ∀ p v, e.equiv p v = i.linearMap p v.1 + t.linearMap p v.2 := by
  intro n l r s a M _ S ι κ τ L E F _ _ _ _ _ _ _ _ _ A B D i q hi hq he
  classical
  obtain ⟨g⟩ := BundleMetrics.exists_smoothFiberMetric B
  have hrank (p : M) : finrank ℝ (LinearMap.range (q.linearMap p)) = s := by
    rw [LinearMap.range_eq_top.mpr (hq p), finrank_top]
    exact ConstantRankBundles.finrank_fiber D p
  have hK := (ConstantRankBundles.kernel_image_subbundles B D q s hrank).1
  obtain ⟨W⟩ := orthogonal_splitting_of_metric B g (fun p => LinearMap.ker (q.linearMap p)) hK
  letI := W.right.topology
  let P (p : M) := orthogonal B g (fun p => LinearMap.ker (q.linearMap p)) p
  let rho (p : M) : P p ≃ₗ[ℝ] F p :=
    LinearEquiv.ofBijective ((q.linearMap p).comp (P p).subtype)
      (restriction_bijective (q.linearMap p) (hq p) (P p) (W.complementary p))
  have hrho : IsSmoothMap W.right.bundle.totalManifold D.totalManifold
      (fun x => (⟨x.proj, rho x.proj x.snd⟩ : TotalSpace (Euclidean s) F)) := by
    intro x
    exact manifoldContDiffAt_comp B.totalManifold.smoothStructure.property.1.1
      (W.right_inclusion x) (q.smooth _)
  have hri := inverse_smooth W.right.bundle D rho hrho
  let t : SmoothBundleMorphism D B := {
    linearMap p := (P p).subtype.comp (rho p).symm.toLinearMap
    smooth := by
      intro x
      exact manifoldContDiffAt_comp W.right.bundle.totalManifold.smoothStructure.property.1.1
        (hri x) (W.right_inclusion _) }
  have ht (p : M) : (q.linearMap p).comp (t.linearMap p) = LinearMap.id := by
    apply LinearMap.ext
    intro v
    exact (rho p).apply_symm_apply v
  refine ⟨t, ht, ?_⟩
  intro V
  letI := V.space.topology
  let e (p : M) : (L p × F p) ≃ₗ[ℝ] E p :=
    LinearEquiv.ofBijective ((i.linearMap p).coprod (t.linearMap p))
      (split_coprod_bijective (i.linearMap p) (q.linearMap p) (t.linearMap p)
        (hi p) (he p) (ht p))
  have hs := coprod_smooth A B D i t V
  exact ⟨⟨e, hs, inverse_smooth V.space.bundle B e hs⟩, fun _ _ => rfl⟩

/-- The prescribed metric map and its inverse are smooth, also for TM and T*M. -/
theorem metric_duality :
    Specs.SmoothManifolds.Ch05.MetricSplittings.metric_dualityType.{u,v,w} := by
  constructor
  · intro n r a M _ S ι E _ _ _ B g D
    exact ⟨metricIso B g D, fun _ _ _ => rfl⟩
  · intro n a M _ S C g
    letI := C.realization.space.topology
    letI := C.tangent.topology
    letI := C.dual.space.topology
    let e := metricIso C.realization.space.bundle g C.dual
    refine ⟨e.equiv, (fun _ _ _ => rfl), ?_, ?_⟩
    · intro q
      exact manifoldContDiffAt_comp C.realization.space.bundle.totalManifold.smoothStructure.property.1.1
        (C.realization.smooth_from_original q) (e.smooth _)
    · intro q
      exact manifoldContDiffAt_comp C.realization.space.bundle.totalManifold.smoothStructure.property.1.1
        (e.inverse_smooth q) (C.realization.smooth_to_original _)

end SmoothManifolds.MetricSplittings
