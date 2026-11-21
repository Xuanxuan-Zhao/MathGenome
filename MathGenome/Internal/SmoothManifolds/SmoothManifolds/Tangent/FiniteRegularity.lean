import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Tangent.FiniteRegularity
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.SmoothMaps
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Tangent.Differential
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations

namespace SmoothManifolds.FiniteRegularity
open ModelData AtlasData MapData FiniteRegularityData Set Filter
open scoped Topology ContDiff
universe u v w


/-- Equality on a manifold neighborhood becomes equality on a relatively open
model domain. Unique differentiability of that domain includes its face. -/
theorem extension_independence :
    Specs.SmoothManifolds.Tangent.FiniteRegularity.extension_independenceType.{u} := by
  intro n m a M _ e g p hp L K hL hK
  obtain ⟨F, hF, heF⟩ := hL
  obtain ⟨G, hG, heG⟩ := hK
  obtain ⟨V, hVsub, hV, hpV⟩ := mem_nhds_iff.mp (heF.trans heG.symm)
  let s : Set (ModelSpace n a) := e.target ∩ e.symm ⁻¹' V
  have hs : IsOpen s := e.symm.isOpen_inter_preimage hV
  have heps : e p ∈ s := ⟨e.map_source hp, by
    change e.symm (e p) ∈ V
    rwa [e.left_inv hp]⟩
  have hFG : EqOn F G (Subtype.val '' s) := by
    rintro _ ⟨x, hx, rfl⟩
    have hh := hVsub hx.2
    change F (e (e.symm x)).val = G (e (e.symm x)).val at hh
    simpa only [e.right_inv hx.1] using hh
  have hpoint : (e p).val ∈ Subtype.val '' s := ⟨e p, heps, rfl⟩
  exact (uniqueDiffOn_modelDomain hs).eq hpoint
    hF.hasFDerivWithinAt (hG.hasFDerivWithinAt.congr' hFG hpoint)

theorem coordinateDerivative_eq :
    Specs.SmoothManifolds.Tangent.FiniteRegularity.coordinateDerivative_eqType.{u} := by
  intro n m a M _ e g p hp L hL
  classical
  have h : ∃ L, HasCoordinateDerivative e g p L := ⟨L, hL⟩
  unfold coordinateDerivative
  rw [dite_eq_left h]
  exact extension_independence e g p hp _ L (Classical.choose_spec h) hL

theorem chartDerivative_exists :
    Specs.SmoothManifolds.Tangent.FiniteRegularity.chartDerivative_existsType.{u,v} := by
  intro n m a b M N _ _ r hr e d f p hf
  obtain ⟨U, hU, hpU, F, hF, heF⟩ := hf
  have hFd := (hF.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by decide : (0 : ℕ∞) < 1) hr)))
  have h : ∃ L, HasCoordinateDerivative e (fun y => (d (f y)).val) p L :=
    ⟨fderiv ℝ F (e p).val, F, hFd.hasFDerivAt, heF⟩
  classical
  unfold chartDerivative coordinateDerivative
  rw [dite_eq_left h]
  exact Classical.choose_spec h

theorem chartDerivative_id :
    Specs.SmoothManifolds.Tangent.FiniteRegularity.chartDerivative_idType.{u} := by
  intro n a M _ e p hp
  exact coordinateDerivative_eq e _ p hp _
    ⟨id, hasFDerivAt_id _, Eventually.of_forall (fun _ => rfl)⟩

theorem chartDerivative_comp :
    Specs.SmoothManifolds.Tangent.FiniteRegularity.chartDerivative_compType.{u,v,w} := by
  intro n m l a b c M N P _ _ _ r hr e d k f g p hp hf hfe hgd
  obtain ⟨F, hF, heF⟩ := chartDerivative_exists r hr e d f p hfe
  obtain ⟨G, hG, heG⟩ := chartDerivative_exists r hr d k g (f p) hgd
  apply coordinateDerivative_eq e _ p hp
  refine ⟨G ∘ F, ?_, ?_⟩
  · have hbase : F (e p).val = (d (f p)).val := heF.eq_of_nhds
    exact (hbase ▸ hG).comp (e p).val hF
  · exact (heF.fun_comp G).trans (heG.comp_tendsto hf)

theorem derivative_cocycle :
    Specs.SmoothManifolds.Tangent.FiniteRegularity.derivative_cocycleType.{u} := by
  intro n a M _ r hr A hA e d k he hd hk p hp hpd hpk
  exact chartDerivative_comp r hr e d k id id p hp continuousAt_id
    (chartContDiffAt_of_compatible (hA.2 e he d hd) hp hpd)
    (chartContDiffAt_of_compatible (hA.2 d hd k hk) hpd hpk)

theorem ambientTangentMap_regular :
    Specs.SmoothManifolds.Tangent.FiniteRegularity.ambientTangentMap_regularType := by
  intro n m r hr U F hU hF
  have horder : (r - 1 : ℕ) + 1 = r := Nat.sub_add_cancel hr
  have hle : ((r - 1 : ℕ) : ℕ∞ω) + 1 ≤ (r : ℕ∞ω) := by
    exact_mod_cast horder.le
  have hDF := hF.fderiv_of_isOpen hU hle
  have hfst : ContDiffOn ℝ (r - 1 : ℕ) Prod.fst (U ×ˢ (univ : Set (Euclidean n))) :=
    contDiff_fst.contDiffOn
  have hsnd : ContDiffOn ℝ (r - 1 : ℕ) Prod.snd (U ×ˢ (univ : Set (Euclidean n))) :=
    contDiff_snd.contDiffOn
  exact ((hF.of_le (by exact_mod_cast Nat.sub_le r 1)).comp hfst
    (fun _ hz => hz.1)).prodMk
    ((hDF.comp hfst (fun _ hz => hz.1)).clm_apply hsnd)

section QuotientConstruction
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  (r : ℕ∞) (hr : 1 ≤ r) (A : Set (ModelChart n a M)) (hA : IsContDiffAtlas r A)
  (p : M)

/-- Coordinates descend to the raw quotient by the derivative cocycle. -/
noncomputable def quotientCoordinates (e : ModelChart n a M) (he : e ∈ A)
    (hp : p ∈ e.source) : CoordinateTangent A p ≃ Euclidean n where
  toFun := Quot.lift (fun v : CoordinateRepresentative A p =>
    chartDerivative v.1.val e id p v.2) (by
      intro v w hvw
      have hc := derivative_cocycle r hr A hA v.1.val w.1.val e
        v.1.property.1 w.1.property.1 he p v.1.property.2 w.1.property.2 hp
      rw [hc, ContinuousLinearMap.comp_apply, hvw])
  invFun := tangentClass A p e he hp
  left_inv := by
    intro v
    induction v using Quot.inductionOn with
    | h v => exact (Quot.sound (show RepresentativeRel A p v
        (⟨e, he, hp⟩, chartDerivative v.1.val e id p v.2) from rfl)).symm
  right_inv := by
    intro v
    change chartDerivative e e id p v = v
    rw [chartDerivative_id e p hp, ContinuousLinearMap.id_apply]

@[simp] theorem quotientCoordinates_class (e d : ModelChart n a M)
    (he : e ∈ A) (hd : d ∈ A) (hp : p ∈ e.source) (hpd : p ∈ d.source)
    (v : Euclidean n) :
    quotientCoordinates r hr A hA p d hd hpd (tangentClass A p e he hp v) =
      chartDerivative e d id p v := rfl

/-- Reversing the two charts gives the inverse derivative, also at a face. -/
noncomputable def transitionLinearEquiv (e d : ModelChart n a M)
    (he : e ∈ A) (hd : d ∈ A) (hp : p ∈ e.source) (hpd : p ∈ d.source) :
    Euclidean n ≃ₗ[ℝ] Euclidean n where
  toLinearMap := (chartDerivative e d id p).toLinearMap
  invFun := chartDerivative d e id p
  left_inv v := by
    have hc := derivative_cocycle r hr A hA e d e he hd he p hp hpd hp
    have hv := congrArg (fun L : Euclidean n →L[ℝ] Euclidean n => L v) hc
    rw [chartDerivative_id e p hp] at hv
    exact hv.symm
  right_inv v := by
    have hc := derivative_cocycle r hr A hA d e d hd he hd p hpd hp hpd
    have hv := congrArg (fun L : Euclidean n →L[ℝ] Euclidean n => L v) hc
    rw [chartDerivative_id d p hpd] at hv
    exact hv.symm

end QuotientConstruction

theorem tangentClass_eq_iff :
    Specs.SmoothManifolds.Tangent.FiniteRegularity.tangentClass_eq_iffType.{u} := by
  intro n a M _ r hr A hA p e d he hd hp hpd v w
  constructor
  · intro h
    have hh := congrArg (quotientCoordinates r hr A hA p d hd hpd) h
    simpa only [quotientCoordinates_class, chartDerivative_id d p hpd,
      ContinuousLinearMap.id_apply] using hh
  · exact fun h => Quot.sound h

/-- Transport the ordinary real vector space structure through one quotient
chart. The cocycle then makes every other quotient chart a linear equivalence. -/
theorem fiberModel_exists :
    Specs.SmoothManifolds.Tangent.FiniteRegularity.fiberModel_existsType.{u} := by
  intro n a M _ r hr A hA p
  obtain ⟨b, hb, hpb⟩ := hA.1 p
  let E := quotientCoordinates r hr A hA p b hb hpb
  letI := E.addCommGroup
  letI := E.addEquiv.module ℝ
  let EL : CoordinateTangent A p ≃ₗ[ℝ] Euclidean n := E.addEquiv.linearEquiv ℝ
  refine ⟨{
    group := inferInstance
    «module» := inferInstance
    coordinates := fun e he hp => EL.trans (transitionLinearEquiv r hr A hA p b e hb he hpb hp)
    coordinates_class := ?_ }⟩
  intro e d he hd hp hpd v
  change chartDerivative b d id p (chartDerivative e b id p v) = chartDerivative e d id p v
  rw [derivative_cocycle r hr A hA e b d he hb hd p hp hpb hpd]
  rfl

/-- Every quotient vector is represented in each available chart. -/
theorem fiber_coordinates_class_self {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (r : ℕ∞) (_hr : 1 ≤ r) (A : Set (ModelChart n a M))
    (p : M) (S : FiberModel A p) (e : ModelChart n a M) (he : e ∈ A)
    (hp : p ∈ e.source) (v : Euclidean n) :
    S.coordinates e he hp (tangentClass A p e he hp v) = v := by
  rw [S.coordinates_class e e he he hp hp, chartDerivative_id e p hp]
  rfl

/-- Changing coordinates of a quotient vector is its transition derivative. -/
theorem fiber_coordinates_change {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (r : ℕ∞) (hr : 1 ≤ r) (A : Set (ModelChart n a M))
    (p : M) (S : FiberModel A p) (e d : ModelChart n a M) (he : e ∈ A)
    (hd : d ∈ A) (hp : p ∈ e.source) (hpd : p ∈ d.source)
    (v : CoordinateTangent A p) :
    S.coordinates d hd hpd v = chartDerivative e d id p (S.coordinates e he hp v) := by
  let := S.group
  let := S.module
  have hv : tangentClass A p e he hp (S.coordinates e he hp v) = v := by
    apply (S.coordinates e he hp).injective
    exact fiber_coordinates_class_self r hr A p S e he hp _
  rw [← hv, S.coordinates_class e d he hd hp hpd]
  rw [fiber_coordinates_class_self r hr A p S e he hp]

/-- The C^(r-1) extension is valid at every fiber vector, with a base
neighborhood that is independent of that vector. -/
theorem tangentMap_local_regular :
    Specs.SmoothManifolds.Tangent.FiniteRegularity.tangentMap_local_regularType.{u,v} := by
  intro n m a b M N _ _ r hr e d f p hp hf
  obtain ⟨U, hU, hpU, F, hF, heF⟩ := hf
  refine ⟨U, F, hU, hpU, hF, ambientTangentMap_regular r hr U F hU hF, ?_⟩
  have hevent : ∀ᶠ y in 𝓝 p,
      (e y).val ∈ U ∧ y ∈ e.source ∧
        (fun z => F (e z).val) =ᶠ[𝓝 y] (fun z => (d (f z)).val) := by
    filter_upwards [(continuous_subtype_val.continuousAt.comp (e.continuousAt hp)).preimage_mem_nhds
      (hU.mem_nhds hpU), e.open_source.mem_nhds hp, heF.eventuallyEq_nhds] with y hyU hy heq
    exact ⟨hyU, hy, heq⟩
  filter_upwards [hevent] with y hy
  refine ⟨hy.1, fun v => ?_⟩
  have hFd := (hF.contDiffAt (hU.mem_nhds hy.1)).differentiableAt (by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by decide : (0 : ℕ) < 1) hr)))
  have hD := coordinateDerivative_eq e (fun z => (d (f z)).val) y hy.2.1
    (fderiv ℝ F (e y).val) ⟨F, hFd.hasFDerivAt, hy.2.2⟩
  change (F (e y).val, fderiv ℝ F (e y).val v) = _
  rw [hy.2.2.eq_of_nhds]
  exact Prod.ext rfl (congrArg (fun L : Euclidean n →L[ℝ] Euclidean m => L v) hD.symm)

theorem tangentTransition_local_regular :
    Specs.SmoothManifolds.Tangent.FiniteRegularity.tangentTransition_local_regularType.{u} := by
  intro n a M _ r hr A hA e d he hd p hp hpd
  exact tangentMap_local_regular r hr e d id p hp
    (chartContDiffAt_of_compatible (hA.2 e he d hd) hp hpd)

/-- Transformation law for the Jacobian under independent changes of source
and target charts. -/
theorem chartDerivative_changeCharts {n m : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N] (r : ℕ∞) (hr : 1 ≤ r)
    (A : Set (ModelChart n a M)) (B : Set (ModelChart m b N))
    (hA : IsContDiffAtlas r A) (hB : IsContDiffAtlas r B)
    (f : M → N) (hf : ManifoldContDiff r A B f) (p : M)
    (e e' : ModelChart n a M) (d d' : ModelChart m b N)
    (he : e ∈ A) (he' : e' ∈ A) (hd : d ∈ B) (hd' : d' ∈ B)
    (hp : p ∈ e.source) (hp' : p ∈ e'.source)
    (hfp : f p ∈ d.source) (hfp' : f p ∈ d'.source) :
    chartDerivative e d f p = (chartDerivative d' d id (f p)).comp
      ((chartDerivative e' d' f p).comp (chartDerivative e e' id p)) := by
  have h1 := chartDerivative_comp r hr e d' d f id p hp (hf p).1
    ((hf p).2 e he d' hd' hp hfp')
    (chartContDiffAt_of_compatible (hB.2 d' hd' d hd) hfp' hfp)
  have h2 := chartDerivative_comp r hr e e' d' id f p hp continuousAt_id
    (chartContDiffAt_of_compatible (hA.2 e he e' he') hp hp')
    ((hf p).2 e' he' d' hd' hp' hfp')
  change chartDerivative e d f p = _ at h1
  rw [h1]
  change chartDerivative e d' f p = _ at h2
  rw [h2]
  rfl

/-- Existence of the differential follows by conjugating a Jacobian by one
pair of quotient charts; the transformation law verifies every other pair. -/
theorem coordinateDifferential_exists :
    Specs.SmoothManifolds.Tangent.FiniteRegularity.coordinateDifferential_existsType.{u,v} := by
  intro n m a b M N _ _ r hr A B hA hB f hf p S T
  let := S.group
  let := S.module
  let := T.group
  let := T.module
  obtain ⟨e₀, he₀, hp₀⟩ := hA.1 p
  obtain ⟨d₀, hd₀, hfp₀⟩ := hB.1 (f p)
  let E := S.coordinates e₀ he₀ hp₀
  let D := T.coordinates d₀ hd₀ hfp₀
  let L : CoordinateTangent A p →ₗ[ℝ] CoordinateTangent B (f p) :=
    D.symm.toLinearMap.comp ((chartDerivative e₀ d₀ f p).toLinearMap.comp E.toLinearMap)
  have hL : IsCoordinateDifferential f p S T L := by
    intro e d he hd hp hfp v
    rw [fiber_coordinates_change r hr B (f p) T d₀ d hd₀ hd hfp₀ hfp]
    have hbase : D (L v) = chartDerivative e₀ d₀ f p (E v) :=
      D.apply_symm_apply _
    change chartDerivative d₀ d id (f p) (D (L v)) = _
    rw [hbase]
    have hsrc := fiber_coordinates_change r hr A p S e e₀ he he₀ hp hp₀ v
    change E v = _ at hsrc
    rw [hsrc, chartDerivative_changeCharts r hr A B hA hB f hf p e e₀ d d₀
      he he₀ hd hd₀ hp hp₀ hfp hfp₀]
    rfl
  refine ⟨L, hL, ?_⟩
  intro K hK
  apply LinearMap.ext
  intro v
  apply D.injective
  exact (hK e₀ d₀ he₀ hd₀ hp₀ hfp₀ v).trans (hL e₀ d₀ he₀ hd₀ hp₀ hfp₀ v).symm

theorem coordinateDifferential_id :
    Specs.SmoothManifolds.Tangent.FiniteRegularity.coordinateDifferential_idType.{u} := by
  intro n a M _ r hr A _ p S e d he hd hp hpd v
  exact fiber_coordinates_change r hr A p S e d he hd hp hpd v

theorem coordinateDifferential_comp :
    Specs.SmoothManifolds.Tangent.FiniteRegularity.coordinateDifferential_compType.{u,v,w} := by
  intro n m l a b c M N P _ _ _ r hr A B C _ hB _ f g hf hg p S T U L K hL hK
  obtain ⟨d, hd, hfp⟩ := hB.1 (f p)
  intro e k he hk hp hgp v
  change U.coordinates k hk hgp (K (L v)) = _
  rw [hK d k hd hk hfp hgp, hL e d he hd hp hfp]
  rw [chartDerivative_comp r hr e d k f g p hp (hf p).1
    ((hf p).2 e he d hd hp hfp) ((hg (f p)).2 d hd k hk hfp hgp)]
  rfl

/-- The accepted smooth tangent fiber has a coordinate realization in each
smooth chart. This helper is used only for the final compatibility comparison. -/
theorem exists_smooth_chart_coordinates {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (p : M) (e : ModelChart n a M)
    (he : e ∈ S.smoothStructure.val) (hp : p ∈ e.source) :
    ∃ E : TangentData.TangentSpace S p ≃ₗ[ℝ] Euclidean n,
      DifferentialData.IsChartCoordinates S p e E := by
  obtain ⟨coords, _, E, hcoords, hE, _⟩ := coordinate_tangent_model S p e he hp
  exact ⟨E, coords, hcoords, hE⟩

/-- The smooth Jacobian theorem and the coordinate derivative defined here
use the same actual ambient derivative, including on the boundary. -/
theorem smooth_jacobian_coordinateDerivative {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N) (f : M → N)
    (hf : IsSmoothMap S T f) (p : M)
    (L : TangentData.TangentSpace S p →ₗ[ℝ] TangentData.TangentSpace T (f p))
    (hL : DifferentialData.IsDifferential S T f p L)
    (e : ModelChart n a M) (d : ModelChart m b N)
    (he : e ∈ S.smoothStructure.val) (hd : d ∈ T.smoothStructure.val)
    (hp : p ∈ e.source) (hfp : f p ∈ d.source)
    (E : TangentData.TangentSpace S p ≃ₗ[ℝ] Euclidean n)
    (D : TangentData.TangentSpace T (f p) ≃ₗ[ℝ] Euclidean m)
    (hE : DifferentialData.IsChartCoordinates S p e E)
    (hD : DifferentialData.IsChartCoordinates T (f p) d D) (v : TangentData.TangentSpace S p) :
    D (L v) = chartDerivative e d f p (E v) := by
  obtain ⟨U, hU, hpU, H, hH, heH⟩ := (hf p).2 e he d hd hp hfp
  have hderiv : chartDerivative e d f p = fderiv ℝ H (e p).val :=
    coordinateDerivative_eq e _ p hp _
      ⟨H, ((hH.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp)).hasFDerivAt, heH⟩
  rw [hderiv]
  exact differential_jacobian S T f hf p L hL e d he hd hp hfp E D hE hD
    U H hU hpU hH heH v

theorem smooth_compatibility :
    Specs.SmoothManifolds.Tangent.FiniteRegularity.smooth_compatibilityType.{u} := by
  intro n a M _ S p F
  let := F.group
  let := F.module
  obtain ⟨e₀, he₀, hp₀⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨E₀, hE₀⟩ := exists_smooth_chart_coordinates S p e₀ he₀ hp₀
  let E := (F.coordinates e₀ he₀ hp₀).trans E₀.symm
  refine ⟨E, ?_⟩
  intro e he hp C hC v
  have hsid : IsSmoothMap S S id :=
    manifoldContDiff_id (⊤ : ℕ∞) S.smoothStructure.val S.smoothStructure.property.1
  have hh := smooth_jacobian_coordinateDerivative S S id hsid p LinearMap.id
    (differential_id S p) e₀ e he₀ he hp₀ hp E₀ C hE₀ hC (E v)
  have hcoord : E₀ (E v) = F.coordinates e₀ he₀ hp₀ v := E₀.apply_symm_apply _
  change C (E v) = _ at hh
  rw [hcoord] at hh
  exact hh.trans (fiber_coordinates_change (⊤ : ℕ∞) (by simp) S.smoothStructure.val p F
    e₀ e he₀ he hp₀ hp v).symm

theorem smooth_differential_compatibility :
    Specs.SmoothManifolds.Tangent.FiniteRegularity.smooth_differential_compatibilityType.{u} := by
  intro n m a b M N _ _ S T f hf p F G E H hE hH L K hL hK v
  let := F.group
  let := F.module
  let := G.group
  let := G.module
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨d, hd, hfp⟩ := T.smoothStructure.property.1.1 (f p)
  obtain ⟨C, hC⟩ := exists_smooth_chart_coordinates S p e he hp
  obtain ⟨D, hD⟩ := exists_smooth_chart_coordinates T (f p) d hd hfp
  apply D.injective
  rw [hH d hd hfp D hD,
    smooth_jacobian_coordinateDerivative S T f hf p K hK e d he hd hp hfp C D hC hD,
    hE e he hp C hC]
  exact hL e d he hd hp hfp v

abbrev HasCoordinateDerivative := @FiniteRegularityData.HasCoordinateDerivative
noncomputable abbrev coordinateDerivative := @FiniteRegularityData.coordinateDerivative
noncomputable abbrev chartDerivative := @FiniteRegularityData.chartDerivative
abbrev CoordinateRepresentative := @FiniteRegularityData.CoordinateRepresentative
abbrev RepresentativeRel := @FiniteRegularityData.RepresentativeRel
abbrev CoordinateTangent := @FiniteRegularityData.CoordinateTangent
abbrev tangentClass := @FiniteRegularityData.tangentClass
abbrev FiberModel := @FiniteRegularityData.FiberModel
abbrev IsCoordinateDifferential := @FiniteRegularityData.IsCoordinateDifferential
noncomputable abbrev ambientTangentMap := @FiniteRegularityData.ambientTangentMap

end SmoothManifolds.FiniteRegularity
