import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Tangent.Differential
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.Products
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Tangent.Models

/-! Intrinsic differentials constructed by pulling back smooth germs.
The chart model identifies this construction with every ambient Jacobian. -/
namespace SmoothManifolds
open ModelData AtlasData MapData PartitionData TangentData ProductData DifferentialData
open Set Filter
open scoped Topology
universe u

private theorem scalar_comp_at {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    {f : M → N} {r : N → ℝ} {p : M}
    (hf : ManifoldSmoothAt S.smoothStructure.val T.smoothStructure.val f p)
    (hr : ScalarContDiffAt (⊤ : ℕ∞) T.smoothStructure.val r (f p)) :
    ScalarContDiffAt (⊤ : ℕ∞) S.smoothStructure.val (r ∘ f) p := by
  refine ⟨hr.1.comp hf.1, ?_⟩
  intro e he hp
  obtain ⟨d, hd, hdp⟩ := T.smoothStructure.property.1.1 (f p)
  exact LocalCoordinateExtension.comp
    (LocalCoordinateExtension.precomp (hr.2 d hd hdp) hf.1 rfl)
    (hf.2 e he d hd hp hdp)

private def germPullbackRaw {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    (f : M → N) (p : M) (hf : ContinuousAt f p) :
    Germ (𝓝 (f p)) ℝ →ₐ[ℝ] Germ (𝓝 p) ℝ where
  toFun h := h.compTendsto f hf
  map_zero' := rfl
  map_one' := rfl
  map_add' h k := by
    induction h using Germ.inductionOn with | _ r =>
      induction k using Germ.inductionOn with | _ s => rfl
  map_mul' h k := by
    induction h using Germ.inductionOn with | _ r =>
      induction k using Germ.inductionOn with | _ s => rfl
  commutes' _ := rfl

private def smoothGermPullback
    (hmem : Specs.SmoothManifolds.Tangent.Models.mem_smoothGermAlgebra_iffType.{u})
    {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (f : M → N) (hf : IsSmoothMap S T f) (p : M) :
    SmoothGerm T (f p) →ₐ[ℝ] SmoothGerm S p where
  toFun h := ⟨germPullbackRaw f p (hf p).1 h.val, by
    obtain ⟨r, hr, he⟩ := (hmem T (f p) h.val).mp h.property
    rw [he]
    exact Algebra.subset_adjoin ⟨r ∘ f, scalar_comp_at (hf p) hr, rfl⟩⟩
  map_zero' := Subtype.ext (map_zero (germPullbackRaw f p (hf p).1))
  map_one' := Subtype.ext (map_one (germPullbackRaw f p (hf p).1))
  map_add' h k := Subtype.ext (map_add (germPullbackRaw f p (hf p).1) h.val k.val)
  map_mul' h k := Subtype.ext (map_mul (germPullbackRaw f p (hf p).1) h.val k.val)
  commutes' r := Subtype.ext ((germPullbackRaw f p (hf p).1).commutes r)

private theorem smoothGermPullback_rep
    (hmem : Specs.SmoothManifolds.Tangent.Models.mem_smoothGermAlgebra_iffType.{u})
    {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (f : M → N) (hf : IsSmoothMap S T f) (p : M)
    (h : SmoothGerm T (f p)) (r : N → ℝ) (hr : Germ.ofFun r = h.val) :
    (smoothGermPullback hmem S T f hf p h).val = Germ.ofFun (r ∘ f) := by
  change germPullbackRaw f p (hf p).1 h.val = _
  rw [← hr]
  rfl

private def tangentPush
    (hmem : Specs.SmoothManifolds.Tangent.Models.mem_smoothGermAlgebra_iffType.{u})
    {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (f : M → N) (hf : IsSmoothMap S T f) (p : M) :
    TangentSpace S p →ₗ[ℝ] TangentSpace T (f p) where
  toFun v := ⟨v.val.comp (smoothGermPullback hmem S T f hf p).toLinearMap, by
    intro h k
    change v.val (smoothGermPullback hmem S T f hf p (h * k)) = _
    rw [map_mul, v.property]
    have heval (j : SmoothGerm T (f p)) :
        germEvaluation S p (smoothGermPullback hmem S T f hf p j) =
          germEvaluation T (f p) j := by
      change (germPullbackRaw f p (hf p).1 j.val).value = j.val.value
      induction j.val using Germ.inductionOn with | _ r => rfl
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, heval]⟩
  map_add' v w := by
    apply Subtype.ext
    apply LinearMap.ext
    intro h
    rfl
  map_smul' r v := by
    apply Subtype.ext
    apply LinearMap.ext
    intro h
    rfl

private theorem tangentPush_spec
    (hmem : Specs.SmoothManifolds.Tangent.Models.mem_smoothGermAlgebra_iffType.{u})
    {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (f : M → N) (hf : IsSmoothMap S T f) (p : M) :
    IsDifferential S T f p (tangentPush hmem S T f hf p) := by
  intro v h k r hr hk
  change v.val (smoothGermPullback hmem S T f hf p h) = v.val k
  congr 1
  exact Subtype.ext ((smoothGermPullback_rep hmem S T f hf p h r hr).trans hk)

private theorem differential_unique
    (hmem : Specs.SmoothManifolds.Tangent.Models.mem_smoothGermAlgebra_iffType.{u})
    {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (f : M → N) (hf : IsSmoothMap S T f) (p : M)
    (L K : TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (hL : IsDifferential S T f p L) (hK : IsDifferential S T f p K) : L = K := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  apply LinearMap.ext
  intro h
  obtain ⟨r, _, hr⟩ := (hmem T (f p) h.val).mp h.property
  let k := smoothGermPullback hmem S T f hf p h
  have hk := (smoothGermPullback_rep hmem S T f hf p h r hr.symm).symm
  exact (hL v h k r hr.symm hk).trans (hK v h k r hr.symm hk).symm

private theorem differential_exists_proof
    (hmem : Specs.SmoothManifolds.Tangent.Models.mem_smoothGermAlgebra_iffType.{u}) :
    Specs.SmoothManifolds.Tangent.Differential.differential_existsType.{u} := by
  intro n m a b M N _ _ S T f hf p
  exact ⟨tangentPush hmem S T f hf p, tangentPush_spec hmem S T f hf p,
    fun L hL => differential_unique hmem S T f hf p L _ hL (tangentPush_spec hmem S T f hf p)⟩

private theorem differential_id_proof :
    Specs.SmoothManifolds.Tangent.Differential.differential_idType.{u} := by
  intro n a M _ S p v h k r hr hk
  have he : h = k := Subtype.ext (hr.symm.trans hk)
  exact congrArg v.val he

private theorem differential_comp_proof
    (hmem : Specs.SmoothManifolds.Tangent.Models.mem_smoothGermAlgebra_iffType.{u}) :
    Specs.SmoothManifolds.Tangent.Differential.differential_compType.{u} := by
  intro n m l a b c M N Q _ _ _ S T U f g hf hg p L K hL hK v h k r hr hk
  let j := smoothGermPullback hmem T U g hg (f p) h
  have hj := (smoothGermPullback_rep hmem T U g hg (f p) h r hr).symm
  exact (hK (L v) h j r hr hj).trans (hL v j k (r ∘ g) hj hk)

private theorem differential_jacobian_proof
    (hcoord : Specs.SmoothManifolds.Tangent.Models.coordinate_tangent_modelType.{u})
    (hmem : Specs.SmoothManifolds.Tangent.Models.mem_smoothGermAlgebra_iffType.{u}) :
    Specs.SmoothManifolds.Tangent.Differential.differential_jacobianType.{u} := by
  intro n m a b M N _ _ S T f hf p L hL e d he hd hp hfp E F hE hF V H hV hpV hH heH v
  obtain ⟨xs, bs, ES, hxs, hES, _, hformula⟩ := hcoord S p e he hp
  obtain ⟨xs', hxs', hE⟩ := hE
  obtain ⟨ys, hys, hF⟩ := hF
  have hsame (i : Fin n) : xs i = xs' i :=
    Subtype.ext ((hxs i).trans (hxs' i).symm)
  have hv : E v = ∑ i, (v.val (xs i)) • Pi.single i (1 : ℝ) := by
    ext j
    simp [hE, hsame, Pi.single_apply]
  have hHd : DifferentiableAt ℝ H (e p).val :=
    (hH.contDiffAt (hV.mem_nhds hpV)).differentiableAt (by simp)
  ext j
  let k := smoothGermPullback hmem S T f hf p (ys j)
  have hk : Germ.ofFun ((fun z => (d z).val j) ∘ f) = k.val :=
    (smoothGermPullback_rep hmem S T f hf p (ys j) _ (hys j).symm).symm
  have hkH : GermChartExtension S p e k (fun z => H z j) := by
    refine ⟨⟨V, hV, hpV, (contDiffOn_pi.mp hH) j⟩, ?_⟩
    exact (Germ.coe_eq.mpr (heH.mono (fun _ hy => congrFun hy j))).trans hk
  calc
    F (L v) j = (L v).val (ys j) := hF _ _
    _ = v.val k := hL v (ys j) k _ (hys j).symm hk
    _ = ∑ i, v.val (xs i) * fderiv ℝ (fun z => H z j) (e p).val (Pi.single i 1) :=
      hformula v k _ hkH
    _ = fderiv ℝ (fun z => H z j) (e p).val (E v) := by
      rw [hv, map_sum]
      simp only [map_smul, smul_eq_mul]
    _ = (fderiv ℝ H (e p).val (E v)) j := by
      rw [fderiv_apply hHd]
      rfl

private theorem curve_smooth_comp {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (f : M → N) (hf : IsSmoothMap S T f) (p : M)
    (side : CurveSide) (c : ℝ → M) (hc : CurveSmoothAt S p side c) :
    CurveSmoothAt T (f p) side (f ∘ c) := by
  have hct : Tendsto c (𝓝[curveParameterSet side] 0) (𝓝 p) := by
    simpa only [hc.1] using hc.2.1.tendsto
  refine ⟨congrArg f hc.1, ?_, ?_⟩
  · exact (hf p).1.comp_continuousWithinAt_of_eq hc.2.1 hc.1
  intro d hd hdp
  obtain ⟨e, he, hep⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨W, hW, h0W, G, hG, heG⟩ := hc.2.2 e he hep
  obtain ⟨V, hV, hpV, H, hH, heH⟩ := (hf p).2 e he d hd hep hdp
  have h0side : (0 : ℝ) ∈ curveParameterSet side := by cases side <;> simp [TangentData.curveParameterSet]
  have hG0 : G 0 = (e p).val := by
    simpa only [hc.1] using (heG.eq_of_nhdsWithin h0side).symm
  refine ⟨W ∩ G ⁻¹' V, hG.continuousOn.isOpen_inter_preimage hW hV,
    ⟨h0W, by simpa only [mem_preimage, hG0] using hpV⟩,
    H ∘ G, hH.comp (hG.mono inter_subset_left) (fun _ hx => hx.2), ?_⟩
  exact ((heH.comp_tendsto hct).symm.trans (heG.fun_comp H))

private theorem differential_curve_proof
    (hmem : Specs.SmoothManifolds.Tangent.Models.mem_smoothGermAlgebra_iffType.{u}) :
    Specs.SmoothManifolds.Tangent.Differential.differential_curveType.{u} := by
  intro n m a b M N _ _ S T f hf p L hL side c v hc
  refine ⟨curve_smooth_comp S T f hf p side c hc.1, ?_⟩
  intro h r hr
  let k := smoothGermPullback hmem S T f hf p h
  have hk := (smoothGermPullback_rep hmem S T f hf p h r hr).symm
  have hd := hc.2 k (r ∘ f) hk
  rw [← hL v h k r hr hk] at hd
  exact hd

private theorem product_chart_mem {n m : ℕ} {a b k : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (C : ProductCoordinates n a m b k) (P : SmoothManifold (n + m) k (M × N))
    (hP : P.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (productAtlas C S.smoothStructure.val T.smoothStructure.val))
    (e : ModelChart n a M) (d : ModelChart m b N)
    (he : e ∈ S.smoothStructure.val) (hd : d ∈ T.smoothStructure.val) :
    productChart C e d ∈ P.smoothStructure.val := by
  rw [hP]
  exact subset_maximalExtension (productAtlas_isContDiffAtlas C _ _ _
    S.smoothStructure.property.1 T.smoothStructure.property.1) ⟨e, he, d, hd, rfl⟩

private theorem product_projections_smooth {n m : ℕ} {a b k : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (C : ProductCoordinates n a m b k) (P : SmoothManifold (n + m) k (M × N))
    (hP : P.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (productAtlas C S.smoothStructure.val T.smoothStructure.val)) :
    IsSmoothMap P S Prod.fst ∧ IsSmoothMap P T Prod.snd := by
  constructor
  · intro p
    obtain ⟨e, he, hep⟩ := S.smoothStructure.property.1.1 p.1
    obtain ⟨d, hd, hdp⟩ := T.smoothStructure.property.1.1 p.2
    apply (manifoldContDiffAt_iff_oneChart _ _ _ P.smoothStructure.property.1
      S.smoothStructure.property.1 _ p).mpr
    refine ⟨continuous_fst.continuousAt, productChart C e d,
      product_chart_mem S T C P hP e d he hd, e, he, ?_, hep, ?_⟩
    · simpa only [productChart_source, Set.mem_prod] using And.intro hep hdp
    · exact ⟨univ, isOpen_univ, mem_univ _, fun z => (C.linearEquiv.symm z).1,
        C.linearEquiv.symm.contDiff.fst.contDiffOn,
        Eventually.of_forall (fun q => by simp only [productChart_val,
          C.linearEquiv.symm_apply_apply])⟩
  · intro p
    obtain ⟨e, he, hep⟩ := S.smoothStructure.property.1.1 p.1
    obtain ⟨d, hd, hdp⟩ := T.smoothStructure.property.1.1 p.2
    apply (manifoldContDiffAt_iff_oneChart _ _ _ P.smoothStructure.property.1
      T.smoothStructure.property.1 _ p).mpr
    refine ⟨continuous_snd.continuousAt, productChart C e d,
      product_chart_mem S T C P hP e d he hd, d, hd, ?_, hdp, ?_⟩
    · simpa only [productChart_source, Set.mem_prod] using And.intro hep hdp
    · exact ⟨univ, isOpen_univ, mem_univ _, fun z => (C.linearEquiv.symm z).2,
        C.linearEquiv.symm.contDiff.snd.contDiffOn,
        Eventually.of_forall (fun q => by simp only [productChart_val,
          C.linearEquiv.symm_apply_apply])⟩

private theorem pair_smooth {n m l : ℕ} {a b c k : ModelKind} {M N Q : Type u}
    [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace Q]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (U : SmoothManifold l c Q) (C : ProductCoordinates n a m b k)
    (P : SmoothManifold (n + m) k (M × N))
    (hP : P.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (productAtlas C S.smoothStructure.val T.smoothStructure.val))
    (f : Q → M) (g : Q → N) (hf : IsSmoothMap U S f) (hg : IsSmoothMap U T g) :
    IsSmoothMap U P (fun x => (f x, g x)) := by
  intro p
  obtain ⟨e, he, hep⟩ := U.smoothStructure.property.1.1 p
  obtain ⟨d, hd, hdp⟩ := S.smoothStructure.property.1.1 (f p)
  obtain ⟨j, hj, hjp⟩ := T.smoothStructure.property.1.1 (g p)
  apply (manifoldContDiffAt_iff_oneChart _ _ _ U.smoothStructure.property.1
    P.smoothStructure.property.1 _ p).mpr
  refine ⟨(hf p).1.prodMk (hg p).1, e, he, productChart C d j,
    product_chart_mem S T C P hP d j hd hj, hep, ?_, ?_⟩
  · simpa only [productChart_source, Set.mem_prod] using And.intro hdp hjp
  obtain ⟨V, hV, hpV, F, hF, heF⟩ := (hf p).2 e he d hd hep hdp
  obtain ⟨W, hW, hpW, G, hG, heG⟩ := (hg p).2 e he j hj hep hjp
  refine ⟨V ∩ W, hV.inter hW, ⟨hpV, hpW⟩,
    fun z => C.linearEquiv (F z, G z),
    C.linearEquiv.contDiff.contDiffOn.comp
      ((hF.mono inter_subset_left).prodMk (hG.mono inter_subset_right))
      (mapsTo_univ _ _), ?_⟩
  filter_upwards [heF, heG] with q hqF hqG
  simp only [productChart_val, hqF, hqG]

private theorem differential_product_proof
    (hcoord : Specs.SmoothManifolds.Tangent.Models.coordinate_tangent_modelType.{u})
    (hmem : Specs.SmoothManifolds.Tangent.Models.mem_smoothGermAlgebra_iffType.{u}) :
    Specs.SmoothManifolds.Tangent.Differential.differential_productType.{u} := by
  intro n m a b k M N _ _ S T C P hP
  obtain ⟨hfst, hsnd⟩ := product_projections_smooth S T C P hP
  refine ⟨hfst, hsnd, ?_⟩
  intro p
  obtain ⟨e, he, hep⟩ := S.smoothStructure.property.1.1 p.1
  obtain ⟨d, hd, hdp⟩ := T.smoothStructure.property.1.1 p.2
  have hedp : p ∈ (productChart C e d).source := by
    simpa only [productChart_source, Set.mem_prod] using And.intro hep hdp
  have hed := product_chart_mem S T C P hP e d he hd
  obtain ⟨xs, bs, ES, hxs, hES, _, _⟩ := hcoord S p.1 e he hep
  obtain ⟨ys, bt, ET, hys, hET, _, _⟩ := hcoord T p.2 d hd hdp
  obtain ⟨zs, bp, EP, hzs, hEP, _, _⟩ := hcoord P p (productChart C e d) hed hedp
  let E := (EP.trans C.linearEquiv.symm.toLinearEquiv).trans (ES.symm.prodCongr ET.symm)
  let Lf := tangentPush hmem P S Prod.fst hfst p
  let Lg := tangentPush hmem P T Prod.snd hsnd p
  have hf : IsDifferential P S Prod.fst p Lf := tangentPush_spec hmem P S _ hfst p
  have hg : IsDifferential P T Prod.snd p Lg := tangentPush_spec hmem P T _ hsnd p
  let A : Euclidean (n + m) →L[ℝ] Euclidean n :=
    (ContinuousLinearMap.fst ℝ (Euclidean n) (Euclidean m)).comp C.linearEquiv.symm.toContinuousLinearMap
  let B : Euclidean (n + m) →L[ℝ] Euclidean m :=
    (ContinuousLinearMap.snd ℝ (Euclidean n) (Euclidean m)).comp C.linearEquiv.symm.toContinuousLinearMap
  have hA : ∀ v, ES (Lf v) = A (EP v) := by
    intro v
    have hx := differential_jacobian_proof hcoord hmem P S Prod.fst hfst p Lf hf
      (productChart C e d) e hed he hedp hep EP ES ⟨zs, hzs, hEP⟩ ⟨xs, hxs, hES⟩
      univ A isOpen_univ (mem_univ _) A.contDiff.contDiffOn
      (Eventually.of_forall (fun q => by simp [A, productChart_val])) v
    simpa only [A.fderiv] using hx
  have hB : ∀ v, ET (Lg v) = B (EP v) := by
    intro v
    have hx := differential_jacobian_proof hcoord hmem P T Prod.snd hsnd p Lg hg
      (productChart C e d) d hed hd hedp hdp EP ET ⟨zs, hzs, hEP⟩ ⟨ys, hys, hET⟩
      univ B isOpen_univ (mem_univ _) B.contDiff.contDiffOn
      (Eventually.of_forall (fun q => by simp [B, productChart_val])) v
    simpa only [B.fderiv] using hx
  have hEf : (LinearMap.fst ℝ _ _).comp E.toLinearMap = Lf := by
    apply LinearMap.ext
    intro v
    apply ES.injective
    change ES (ES.symm ((C.linearEquiv.symm (EP v)).1)) = ES (Lf v)
    rw [ES.apply_symm_apply, hA]
    rfl
  have hEg : (LinearMap.snd ℝ _ _).comp E.toLinearMap = Lg := by
    apply LinearMap.ext
    intro v
    apply ET.injective
    change ET (ET.symm ((C.linearEquiv.symm (EP v)).2)) = ET (Lg v)
    rw [ET.apply_symm_apply, hB]
    rfl
  exact ⟨E, hEf ▸ hf, hEg ▸ hg⟩

private theorem differential_pair_proof
    (hmem : Specs.SmoothManifolds.Tangent.Models.mem_smoothGermAlgebra_iffType.{u}) :
    Specs.SmoothManifolds.Tangent.Differential.differential_pairType.{u} := by
  intro n m l a b c k M N Q _ _ _ S T U C P hP f g hf hg
  have hpair := pair_smooth S T U C P hP f g hf hg
  obtain ⟨hfst, hsnd⟩ := product_projections_smooth S T C P hP
  refine ⟨hpair, ?_⟩
  intro p Lf Lg L E hLf hLg hL hEf hEg
  have h1 := differential_comp_proof hmem U P S (fun x => (f x, g x)) Prod.fst
    hpair hfst p L ((LinearMap.fst ℝ _ _).comp E.toLinearMap) hL hEf
  have h2 := differential_comp_proof hmem U P T (fun x => (f x, g x)) Prod.snd
    hpair hsnd p L ((LinearMap.snd ℝ _ _).comp E.toLinearMap) hL hEg
  have he1 := differential_unique hmem U S f hf p _ Lf h1 hLf
  have he2 := differential_unique hmem U T g hg p _ Lg h2 hLg
  apply LinearMap.ext
  intro v
  exact Prod.ext (congrArg (fun A => A v) he1) (congrArg (fun A => A v) he2)

private theorem rebased_differential_exists
    (hmem : Specs.SmoothManifolds.Tangent.Models.mem_smoothGermAlgebra_iffType.{u})
    {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (f : M → N) (hf : IsSmoothMap S T f) (p : M) (q : N) (hpq : f p = q) :
    ∃ L : TangentSpace S p →ₗ[ℝ] TangentSpace T q,
      ∀ (v : TangentSpace S p) (h : SmoothGerm T q) (k : SmoothGerm S p)
        (r : N → ℝ), Germ.ofFun r = h.val → Germ.ofFun (r ∘ f) = k.val →
          (L v).val h = v.val k := by
  subst q
  exact ⟨tangentPush hmem S T f hf p, tangentPush_spec hmem S T f hf p⟩

private theorem differential_diffeomorph_proof
    (hmem : Specs.SmoothManifolds.Tangent.Models.mem_smoothGermAlgebra_iffType.{u}) :
    Specs.SmoothManifolds.Tangent.Differential.differential_diffeomorphType.{u} := by
  intro n m a b M N _ _ S T h p
  let f := h.toEquiv
  let g := h.toEquiv.symm
  have hf : IsSmoothMap S T f := h.contDiff_toFun
  have hg : IsSmoothMap T S g := h.contDiff_invFun
  let L := tangentPush hmem S T f hf p
  have hL := tangentPush_spec hmem S T f hf p
  obtain ⟨K, hK⟩ := rebased_differential_exists hmem T S g hg (f p) p
    (h.toEquiv.symm_apply_apply p)
  have hKL : K.comp L = LinearMap.id := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    apply LinearMap.ext
    intro k
    obtain ⟨r, hr, hrk⟩ := (hmem S p k.val).mp k.property
    have hr' : ScalarContDiffAt (⊤ : ℕ∞) S.smoothStructure.val r (g (f p)) := by
      simpa only [g, f, h.toEquiv.symm_apply_apply] using hr
    let j : SmoothGerm T (f p) := ⟨Germ.ofFun (r ∘ g),
      Algebra.subset_adjoin ⟨r ∘ g, scalar_comp_at (hg (f p)) hr', rfl⟩⟩
    have hcomp : Germ.ofFun ((r ∘ g) ∘ f) = k.val := by
      rw [show (r ∘ g) ∘ f = r from funext (fun x => congrArg r (h.toEquiv.symm_apply_apply x))]
      exact hrk.symm
    exact (hK (L v) k j r hrk.symm rfl).trans (hL v j k (r ∘ g) rfl hcomp)
  have hLK : L.comp K = LinearMap.id := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    apply LinearMap.ext
    intro j
    obtain ⟨r, _, hrj⟩ := (hmem T (f p) j.val).mp j.property
    let k := smoothGermPullback hmem S T f hf p j
    have hk := (smoothGermPullback_rep hmem S T f hf p j r hrj.symm).symm
    have hcomp : Germ.ofFun ((r ∘ f) ∘ g) = j.val := by
      rw [show (r ∘ f) ∘ g = r from funext (fun x => congrArg r (h.toEquiv.apply_symm_apply x))]
      exact hrj.symm
    exact (hL (K w) j k r hrj.symm hk).trans (hK w k j (r ∘ f) hk hcomp)
  exact ⟨LinearEquiv.ofLinearMap L K hLK hKL, hL⟩


/-- The intrinsic differential, obtained by precomposing a derivation with
pullback of smooth germs. -/
def differential {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (f : M → N) (hf : IsSmoothMap S T f) (p : M) :
    TangentSpace S p →ₗ[ℝ] TangentSpace T (f p) :=
  tangentPush (@mem_smoothGermAlgebra_iff.{u}) S T f hf p

/-- Evaluation of the differential is composition on smooth germs. -/
theorem differential_spec {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (f : M → N) (hf : IsSmoothMap S T f) (p : M) :
    IsDifferential S T f p (differential S T f hf p) :=
  tangentPush_spec (@mem_smoothGermAlgebra_iff.{u}) S T f hf p

/-- Existence and uniqueness for the intrinsic differential. -/
theorem differential_exists :
    Specs.SmoothManifolds.Tangent.Differential.differential_existsType.{u} :=
  differential_exists_proof (@mem_smoothGermAlgebra_iff.{u})

/-- The identity formula for the intrinsic differential. -/
theorem differential_id :
    Specs.SmoothManifolds.Tangent.Differential.differential_idType.{u} :=
  differential_id_proof

/-- The chain rule for the intrinsic differential. -/
theorem differential_comp :
    Specs.SmoothManifolds.Tangent.Differential.differential_compType.{u} :=
  differential_comp_proof (@mem_smoothGermAlgebra_iff.{u})

/-- The chart Jacobian formula for the intrinsic differential. -/
theorem differential_jacobian :
    Specs.SmoothManifolds.Tangent.Differential.differential_jacobianType.{u} :=
  differential_jacobian_proof (@coordinate_tangent_model.{u}) (@mem_smoothGermAlgebra_iff.{u})

/-- Transport of curve velocities for the intrinsic differential. -/
theorem differential_curve :
    Specs.SmoothManifolds.Tangent.Differential.differential_curveType.{u} :=
  differential_curve_proof (@mem_smoothGermAlgebra_iff.{u})

/-- The projection-induced product equivalence for the intrinsic differential. -/
theorem differential_product :
    Specs.SmoothManifolds.Tangent.Differential.differential_productType.{u} :=
  differential_product_proof (@coordinate_tangent_model.{u}) (@mem_smoothGermAlgebra_iff.{u})

/-- The pair formula for the intrinsic differential. -/
theorem differential_pair :
    Specs.SmoothManifolds.Tangent.Differential.differential_pairType.{u} :=
  differential_pair_proof (@mem_smoothGermAlgebra_iff.{u})

/-- Fiberwise linear isomorphisms under diffeomorphisms for the intrinsic differential. -/
theorem differential_diffeomorph :
    Specs.SmoothManifolds.Tangent.Differential.differential_diffeomorphType.{u} :=
  differential_diffeomorph_proof (@mem_smoothGermAlgebra_iff.{u})

end SmoothManifolds
