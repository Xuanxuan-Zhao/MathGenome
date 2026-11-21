import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Integration.EmbeddedBoundary
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Integration.EmbeddedAtlas
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Orientations.Boundary
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch07.FormPullback
import MathGenome.Internal.MultivariableAnalysis.D04.C14.OutwardFirstBoundaryOrientation
import Mathlib.Analysis.Normed.Ring.Units

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
noncomputable section
open scoped ContDiff SmoothManifolds.BoundaryConeData

namespace SmoothManifolds.EmbeddedBoundaryResults
open ModelData AtlasData BoundaryData TangentData DifferentialData
  EmbeddedCalculusData EmbeddedAtlasData BoundaryOrientationData ExteriorData
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model (EmbeddedChart IsEmbeddedManifold)
open Specs.D04.C14.ChartIndependentTangentSpaces.Model (tangentSpace chartDifferential)
open Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.Model (IsBoundaryParameter)
open Specs.D04.C14.OutwardFirstBoundaryOrientation.Model
universe u v

/-- An embedded parametrization gives an intrinsic chart in its own model.
The arbitrary point is used only to totalize the partial inverse. -/
private theorem embedded_model_chart {n N : ℕ} {M : Set (E N)}
    (c : EmbeddedChart ∞ n N M) (p₀ : M) (hp₀ : p₀.val ∈ c.ambient) :
    ∃ e : ModelChart n (if c.half then .halfSpace else .euclidean) M,
      e.source = {p : M | p.val ∈ c.ambient} ∧
      MatchesEmbeddedChart e c := by
  classical
  let a : ModelKind := if c.half then .halfSpace else .euclidean
  have hmodel (z : E n) :
      z ∈ Specs.D04.C14.EmbeddedManifoldCharts.Model.parameterSpace n c.half ↔
        piCoordinates n z ∈ modelSet n a := by
    cases hh : c.half <;> cases n <;>
      simp [a, hh, Specs.D04.C14.EmbeddedManifoldCharts.Model.parameterSpace,
        Specs.D04.C14.EmbeddedManifoldCharts.Model.halfSpace, ModelData.modelSet, ModelData.halfSpaceSet,
        piCoordinates, EuclideanSpace.equiv]
  let U : Set M := {p | p.val ∈ c.ambient}
  have hU : IsOpen U := c.ambient_open.preimage continuous_subtype_val
  let V : Set (ModelSpace n a) :=
    {z | (piCoordinates n).symm z.val ∈ c.source}
  have hV : IsOpen V := by
    obtain ⟨W, hW, hcW⟩ := c.source_open
    have heq : V = {z : ModelSpace n a | (piCoordinates n).symm z.val ∈ W} := by
      ext z
      change (piCoordinates n).symm z.val ∈ c.source ↔ _
      rw [hcW]
      exact and_iff_right ((hmodel _).mpr (by simpa only [ContinuousLinearEquiv.apply_symm_apply] using z.property))
    rw [heq]
    exact hW.preimage ((piCoordinates n).symm.continuous.comp continuous_subtype_val)
  let h : U ≃ₜ V := {
    toFun := fun p =>
      ⟨⟨piCoordinates n (c.invFun p.val.val),
        (hmodel _).mp (by
          obtain ⟨W, hW, hcw⟩ := c.source_open
          have ht := c.map_target ⟨p.val.property, p.property⟩
          rw [hcw] at ht
          exact ht.1)⟩, by
            change (piCoordinates n).symm (piCoordinates n (c.invFun p.val.val)) ∈ c.source
            rw [ContinuousLinearEquiv.symm_apply_apply]
            exact c.map_target ⟨p.val.property, p.property⟩⟩
    invFun := fun z =>
      ⟨⟨c.toFun ((piCoordinates n).symm z.val.val), (c.map_source z.property).1⟩,
        (c.map_source z.property).2⟩
    left_inv := by
      intro p
      apply Subtype.ext
      apply Subtype.ext
      simpa using c.right_inv p.val.val ⟨p.val.property, p.property⟩
    right_inv := by
      intro z
      apply Subtype.ext
      apply Subtype.ext
      change piCoordinates n (c.invFun (c.toFun ((piCoordinates n).symm z.val.val))) = z.val.val
      rw [c.left_inv _ z.property, ContinuousLinearEquiv.apply_symm_apply]
    continuous_toFun := by
      apply continuous_induced_rng.mpr
      apply continuous_induced_rng.mpr
      exact (piCoordinates n).continuous.comp
        (c.continuous_invFun.comp_continuous (by fun_prop)
          (fun p => ⟨p.val.property, p.property⟩))
    continuous_invFun := by
      apply continuous_induced_rng.mpr
      apply continuous_induced_rng.mpr
      exact c.continuous_toFun.comp_continuous
        ((piCoordinates n).symm.continuous.comp (by fun_prop)) (fun z => z.property) }
  let iU := (⟨U, hU⟩ : TopologicalSpace.Opens M).openPartialHomeomorphSubtypeCoe
    ⟨⟨p₀, hp₀⟩⟩
  let iV := (⟨V, hV⟩ : TopologicalSpace.Opens (ModelSpace n a)).openPartialHomeomorphSubtypeCoe
    ⟨h ⟨p₀, hp₀⟩⟩
  let e := iU.symm.trans (h.toOpenPartialHomeomorph.trans iV)
  have hsource : e.source = U := by
    ext p
    simp [e, iU, iV]
  refine ⟨e, hsource, ?_⟩
  intro p hp
  have hpU : p ∈ U := hsource ▸ hp
  have hi : iU.symm p = ⟨p, hpU⟩ := by
    have hh := iU.left_inv (x := (⟨p, hpU⟩ : U)) (by simp [iU])
    exact hh
  refine ⟨hpU, ?_⟩
  change (h (iU.symm p)).val.val = _
  rw [hi]
  rfl

/-- Literal matching with a smooth D04 chart supplies the raw smooth
full-rank extension condition, rather than assuming a tangent certificate. -/
private theorem raw_of_matching {n N : ℕ} {a : ModelKind} {M : Set (E N)}
    (e : ModelChart n a M) (c : EmbeddedChart ∞ n N M)
    (hm : MatchesEmbeddedChart e c) : IsRawEmbeddedChart e := by
  open Set Filter Topology in
  intro p hp
  let u := c.invFun p.val
  have hu : u ∈ c.source := c.map_target ⟨p.property, (hm p hp).1⟩
  obtain ⟨W, G, hW, huW, heq, hG, hinj⟩ := c.regular u hu
  let V : Set (Euclidean n) := (piCoordinates n).symm ⁻¹' W
  let H : Euclidean n → Euclidean N := parameterExtension G
  have hpV : (e p).val ∈ V := by
    change (piCoordinates n).symm (e p).val ∈ W
    rw [(hm p hp).2, ContinuousLinearEquiv.symm_apply_apply]
    exact huW
  have hV : IsOpen V := hW.preimage (piCoordinates n).symm.continuous
  have hH : ContDiffOn ℝ (⊤ : ℕ∞) H V :=
    (piCoordinates N).contDiff.comp_contDiffOn
      (hG.comp (piCoordinates n).symm.contDiff.contDiffOn (fun _ hz => hz))
  refine ⟨V, H, hV, hpV, hH, ?_, ?_⟩
  · have hcont : ContinuousAt (fun y : M => (e y).val) p :=
      continuous_subtype_val.continuousAt.comp (e.continuousAt hp)
    filter_upwards [e.open_source.mem_nhds hp, hcont (hV.mem_nhds hpV)] with q hq hqV
    change piCoordinates N (G ((piCoordinates n).symm (e q).val)) = _
    rw [(hm q hq).2, ContinuousLinearEquiv.symm_apply_apply]
    have hqsource := c.map_target ⟨q.property, (hm q hq).1⟩
    have hqW : c.invFun q.val ∈ W := by
      change (piCoordinates n).symm (e q).val ∈ W at hqV
      simpa only [(hm q hq).2, ContinuousLinearEquiv.symm_apply_apply] using hqV
    rw [heq ⟨hqsource, hqW⟩, c.right_inv q.val ⟨q.property, (hm q hq).1⟩]
    rfl
  · have hGp : HasFDerivAt G (fderiv ℝ G u) u :=
      ((hG.contDiffAt (hW.mem_nhds huW)).differentiableAt (by simp)).hasFDerivAt
    have hpcoord : (piCoordinates n).symm (e p).val = u := by
      rw [(hm p hp).2, ContinuousLinearEquiv.symm_apply_apply]
    have hh : fderiv ℝ H (e p).val =
        (piCoordinates N).toContinuousLinearMap.comp
          ((fderiv ℝ G u).comp (piCoordinates n).symm.toContinuousLinearMap) := by
      apply HasFDerivAt.fderiv
      unfold H parameterExtension
      have hGp' : HasFDerivAt G (fderiv ℝ G u) ((piCoordinates n).symm (e p).val) := by
        rw [hpcoord]
        exact hGp
      exact (piCoordinates N).hasFDerivAt.comp _
        (hGp'.comp _ (piCoordinates n).symm.hasFDerivAt)
    rw [hh]
    exact (piCoordinates N).injective.comp ((hinj u huW).comp (piCoordinates n).symm.injective)

/-- Two raw charts have mutually smooth identity-coordinate germs, including
when their model kinds differ. -/
private theorem raw_chart_transition
    (inverse : Specs.SmoothManifolds.Integration.EmbeddedAtlas.raw_chart_inverseType)
    {n N : ℕ} {a b : ModelKind} {M : Set (E N)}
    (e : ModelChart n a M) (d : ModelChart n b M)
    (he : IsRawEmbeddedChart e) (hd : IsRawEmbeddedChart d)
    (p : M) (hp : p ∈ e.source) (hpd : p ∈ d.source) :
    MapData.ChartContDiffAt (⊤ : ℕ∞) e d id p := by
  obtain ⟨V, H, hV, hpV, hH, hEq, hinj⟩ := he p hp
  exact LocalCoordinateExtension.comp (inverse d hd p hpd) ⟨V, hV, hpV, H, hH, hEq⟩

/-- Positivity of a nonzero alternating top form exactly detects the
orientation ray it represents, by evaluation on an actual ordered basis. -/
private theorem basis_orientation_iff_positive {W : Type v}
    [AddCommGroup W] [Module ℝ W] {n : ℕ}
    (α : W [⋀^Fin n]→ₗ[ℝ] ℝ) (hα : α ≠ 0)
    (b : Module.Basis (Fin n) ℝ W) :
    b.orientation = rayOfNeZero ℝ α hα ↔ 0 < α b := by
  exact D04BoundaryOrientation.basis_orientation_ray_iff α hα b

private theorem determinant_duality_proof :
    Specs.SmoothManifolds.Integration.EmbeddedBoundary.determinant_dualityType.{u,v} := by
  intro V W _ _ _ _ _ _ n hdim I r
  letI : Module.Free ℝ V := Module.Free.of_divisionRing ℝ V
  letI : Module.Free ℝ (⋀[ℝ]^n V) := Module.Free.of_divisionRing ℝ _
  have hline : Module.finrank ℝ (⋀[ℝ]^n V) = 1 := by
    rw [exteriorPower.finrank_eq, hdim, Nat.choose_self]
  induction r using Module.Ray.ind with | h x hx =>
  obtain ⟨φ, hφx⟩ := Module.Projective.exists_dual_eq_one ℝ hx
  have hφ : φ ≠ 0 := by
    intro hz
    simpa [hz] using hφx
  have hpos : ∀ η, OrientationData.IsPositive (rayOfNeZero ℝ x hx) η ↔ 0 < φ η := by
    apply OrientationResults.positive_ray_characterization hline
    intro η hη
    obtain ⟨t, ht, rfl⟩ := (OrientationResults.positive_iff_pos_smul x hx η).mp hη
    simpa only [map_smul, hφx, smul_eq_mul, mul_one] using ht
  let K := exteriorPower.map n I.symm.toLinearMap
  have hK : Function.Surjective K := exteriorPower.map_surjective I.symm.surjective
  let ψ := φ.comp K
  have hψ : ψ ≠ 0 := by
    intro hz
    apply hφ
    apply LinearMap.ext
    intro η
    obtain ⟨ζ, rfl⟩ := hK η
    exact DFunLike.congr_fun hz ζ
  let α : W [⋀^Fin n]→ₗ[ℝ] ℝ := exteriorPower.alternatingMapLinearEquiv.symm ψ
  have hα : α ≠ 0 := by
    intro hz
    apply hψ
    exact exteriorPower.alternatingMapLinearEquiv.symm.injective
      (by simpa only [map_zero] using hz)
  let o := rayOfNeZero ℝ α hα
  have hchar (b : Module.Basis (Fin n) ℝ W) :
      b.orientation = o ↔ OrientationData.IsPositive (rayOfNeZero ℝ x hx)
        (exteriorPower.ιMulti ℝ n (fun j => I.symm (b j))) := by
    rw [basis_orientation_iff_positive α hα b, hpos]
    simp only [α, ψ, K, exteriorPower.alternatingMapLinearEquiv_symm_apply,
      LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      exteriorPower.map_apply_ιMulti, LinearEquiv.coe_coe, Function.comp_def]
  refine ⟨o, hchar, ?_⟩
  intro o' ho'
  let b := Module.finBasisOfFinrankEq ℝ W (I.symm.finrank_eq.trans hdim)
  by_cases hb : b.orientation = o'
  · exact hb.symm.trans ((hchar b).mpr ((ho' b).mp hb))
  · have hbo : o ≠ b.orientation := by
      intro hh
      exact hb ((ho' b).mpr ((hchar b).mp hh.symm))
    exact ((b.orientation_ne_iff_eq_neg o').mp (Ne.symm hb)).trans
      ((b.orientation_ne_iff_eq_neg o).mp hbo).symm

/-- The canonical boundary identification and outward geometry in matching charts. -/
theorem matching_boundary_geometry :
    Specs.SmoothManifolds.Integration.EmbeddedBoundary.matching_boundary_geometryType := by
  intro d N M hM S hS I hI C e he c hm u hu hb p hpe
  let c₂ := lowerChart c (by simp : (2 : ℕ∞ω) ≤ ∞)
  let A := C.tangent.fiberCoordinates.equiv e he p hpe
  have hA := C.tangent.fiberCoordinates.isCoordinates e he p hpe
  have hcoord := (EmbeddedAtlasResults.matching_chart_pullback S hS I hI C e he c hm u hu hpe).1
  have hformula (v : TangentSpace S p) :
      (I p v).val = chartDifferential c₂ u ((piCoordinates (d+1)).symm (A v)) := by
    have hh := congrArg Subtype.val (hcoord ((piCoordinates (d+1)).symm (A v)))
    change (I p (A.symm ((piCoordinates (d+1))
      ((piCoordinates (d+1)).symm (A v))))).val =
      chartDifferential c₂ u ((piCoordinates (d+1)).symm (A v)) at hh
    rw [ContinuousLinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply] at hh
    exact hh
  have hp : p ∈ intrinsicBoundary S := by
    apply (intrinsicBoundary_iff_chart S e he p hpe).mpr
    change (e p).val (Fin.last d) = 0
    rw [(hm p hpe).2]
    have hh := c.left_inv u hu
    change piCoordinates (d+1) (c.invFun (c.toFun u)) (Fin.last d) = 0
    rw [hh]
    exact hb.2
  have hq : p.val ∈ Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 (d+1) M :=
    ⟨p.property, c₂, u, hb.1, hu, hb.2, rfl⟩
  have hM₂ := (EmbeddedAtlasResults.smooth_c2_tangents hM).1
  have hout (v : TangentSpace S p) : IsOutward S ⟨p, hp⟩ v ↔
      IsOutwardVector 2 d M p.val (I p v).val := by
    rw [BoundaryOrientations.outward_iff_coordinate S ⟨p, hp⟩ e he hpe A hA, hformula]
    exact (D04BoundaryOrientation.outward_chart_independent hM₂ c₂ u hu hb ((piCoordinates (d+1)).symm (A v))).symm
  refine ⟨hp, hq, ?_⟩
  intro B hB L hL
  have hLimage := boundary_inclusion_image S B hB ⟨p, hp⟩ e he hpe L hL A hA
  let K : TangentSpace B ⟨p, hp⟩ →ₗ[ℝ] E N :=
    (tangentSpace 2 (d+1) M p.val).subtype.comp ((I p).toLinearMap.comp L)
  have hK : Function.Injective K :=
    Subtype.val_injective.comp ((I p).injective.comp hLimage.1)
  have hrange : LinearMap.range K =
      tangentSpace 2 d (Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 (d+1) M) p.val := by
    apply SetLike.coe_injective
    change (LinearMap.range K : Set (E N)) =
      (tangentSpace 2 d (Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary
        2 (d+1) M) (c₂.toFun u) : Set (E N))
    rw [D04.tangentSpace_intrinsic_boundary c₂ hM₂.1 hM₂.2.1 hb.1 u hu hb.2]
    ext z
    constructor
    · rintro ⟨v, rfl⟩
      refine ⟨(piCoordinates (d+1)).symm (A (L v)), ?_, hformula (L v) |>.symm⟩
      exact (hLimage.2 (L v)).mp ⟨v, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      have hw' : A (A.symm (piCoordinates (d+1) w)) (Fin.last d) = 0 := by
        rw [A.apply_symm_apply]
        exact hw
      obtain ⟨v, hv⟩ := (hLimage.2 (A.symm (piCoordinates (d+1) w))).mpr hw'
      refine ⟨v, ?_⟩
      change (I p (L v)).val = _
      rw [hformula, hv, A.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply]
  let J := (LinearEquiv.ofInjective K hK).trans (LinearEquiv.ofEq _ _ hrange)
  have hJ (v) : (J v).val = (I p (L v)).val := rfl
  have hnormal : ∃! ν : TangentSpace S p,
      IsOutwardUnitConormal 2 d M p.val (I p ν).val ∧ IsOutward S ⟨p, hp⟩ ν := by
    obtain ⟨z, hz, huniq⟩ := D04BoundaryOrientation.conormal_exists_unique hM₂ p.val hq
    let zT : tangentSpace 2 (d+1) M p.val := ⟨z, hz.1⟩
    refine ⟨(I p).symm zT, ⟨?_, ?_⟩, ?_⟩
    · simpa only [LinearEquiv.apply_symm_apply] using hz
    · apply (hout _).mpr
      simpa only [LinearEquiv.apply_symm_apply] using hz.2.2.2
    · intro v hv
      apply (I p).injective
      apply Subtype.ext
      simpa only [LinearEquiv.apply_symm_apply] using huniq (I p v).val hv.1
  have hle := D04BoundaryOrientation.boundary_tangent_le hM₂ ⟨p.val, hq⟩
  let inc := Specs.D04.C15.GeneralizedStokes.Model.boundaryTangentInclusion 2 d M ⟨p.val, hq⟩
  have hsquare (v) : I p (L v) = inc (J v) := by
    apply Subtype.ext
    dsimp only [inc, Specs.D04.C15.GeneralizedStokes.Model.boundaryTangentInclusion]
    rw [dite_eq_left hle]
    exact (hJ v).symm
  refine ⟨J, ⟨hJ, hout, hnormal, ?_⟩, ?_⟩
  · intro k η
    apply AlternatingMap.ext
    intro z
    change evaluate (TangentSpace B ⟨p, hp⟩) k (FormPullbackData.fiberPullback k L η)
      (fun j => J.symm (z j)) = evaluate (TangentSpace S p) k η
        (fun j => (I p).symm (inc (z j)))
    rw [FormPullbackResults.evaluate_fiberPullback]
    congr 1
    funext j
    apply (I p).injective
    rw [hsquare, J.apply_symm_apply, LinearEquiv.apply_symm_apply]
  · intro J' hJ'
    apply LinearEquiv.ext
    intro v
    apply Subtype.ext
    exact (hJ'.1 v).trans (hJ v).symm

/-- D04 outward vectors and the intrinsic quotient define the same strict ray.
This uses the genuine boundary differential, not an assumed ray certificate. -/
theorem matching_outward_rays :
    Specs.SmoothManifolds.Integration.EmbeddedBoundary.matching_outward_raysType := by
  intro d N M hM S hS I hI C e he c hm u hu hb p hpe
  obtain ⟨hp, hq, hgeo⟩ := matching_boundary_geometry
     hM S hS I hI C e he c hm u hu hb hpe
  refine ⟨hp, ?_⟩
  intro B hB L hL
  obtain ⟨J, hJ, _⟩ := hgeo B hB L hL
  have hout := hJ.2.1
  let A := C.tangent.fiberCoordinates.equiv e he p hpe
  have hA := C.tangent.fiberCoordinates.isCoordinates e he p hpe
  obtain ⟨_, _, Q, hQ, hdim, hin, ho⟩ :=
    BoundaryOrientations.normal_rays S B hB ⟨p, hp⟩ L hL e he hpe A hA
  refine ⟨Q, hdim, ho, ?_, ?_, ?_⟩
  · change Submodule.Quotient.mk '' {v | IsOutward S ⟨p, hp⟩ v} = _
    congr 1
    exact Set.ext hout
  · obtain ⟨ν, hν, _⟩ := hJ.2.2.1
    exact ⟨ν, hν.1, ν, hν.2, rfl⟩
  · intro v w hv hw
    exact BoundaryOrientations.outward_independent S B hB ⟨p, hp⟩ L hL v w
      ((hout v).mpr hv) ((hout w).mpr hw)

/-- The separate dimension-zero convention is literal emptiness on both bases. -/
theorem boundary_zero :
    Specs.SmoothManifolds.Integration.EmbeddedBoundary.boundary_zeroType := by
  intro N a M S
  exact ⟨intrinsicBoundary_zero S, D04.intrinsic_boundary_zero 2 M⟩


/-- Global equality of the two actual intrinsic boundaries, for both model
kinds and in every dimension. No matching-chart assumption is imposed. -/
theorem boundary_set :
    Specs.SmoothManifolds.Integration.EmbeddedBoundary.boundary_setType := by
  intro n N a M hM S hS
  ext p
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  have heRaw : IsRawEmbeddedChart e := by
    change S.smoothStructure.val = _ at hS
    rw [hS] at he
    exact he
  obtain ⟨c, u, hu, hcu⟩ := hM.2.2 p.val p.property
  have hpambient : p.val ∈ c.ambient := by
    rw [← hcu]
    exact (c.map_source hu.1).2
  obtain ⟨d, hdsource, hmatch⟩ := embedded_model_chart c p hpambient
  have hpd : p ∈ d.source := by rw [hdsource]; exact hpambient
  have hdRaw := raw_of_matching d c hmatch
  have hcompare := modelFace_chart_independent e d p hp hpd
    (raw_chart_transition EmbeddedAtlasResults.raw_chart_inverse e d heRaw hdRaw p hp hpd)
    (raw_chart_transition EmbeddedAtlasResults.raw_chart_inverse d e hdRaw heRaw p hpd hp)
  have hdcoord : (d p).val = piCoordinates n u := by
    rw [(hmatch p hpd).2, ← hcu, c.left_inv u hu.1]
  have hface : (d p).val ∈ modelFace n (if c.half then .halfSpace else .euclidean) ↔
      IsBoundaryParameter c u := by
    rw [hdcoord]
    cases hh : c.half <;> cases n <;>
      simp [hh, BoundaryData.modelFace, ModelData.halfSpaceFace,
        Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.Model.IsBoundaryParameter,
        Specs.D04.C14.EmbeddedManifoldCharts.Model.flatBoundary, piCoordinates,
        EuclideanSpace.equiv]
  let c₂ := lowerChart c (by simp : (2 : ℕ∞ω) ≤ ∞)
  have hM₂ := (EmbeddedAtlasResults.smooth_c2_tangents hM).1
  have hD := D04.chart_intrinsicBoundary c₂ hM₂.1 hM₂.2.1 u hu.1
  change c.toFun u ∈ Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 n M ↔
    IsBoundaryParameter c u at hD
  rw [hcu] at hD
  exact (intrinsicBoundary_iff_chart S e he p hp).trans
    (hcompare.trans (hface.trans hD.symm))

/-- The matching charts needed by the comparison are derived from the
original embedded cover and the raw maximal smooth atlas. -/
theorem boundary_matching_chart :
    Specs.SmoothManifolds.Integration.EmbeddedBoundary.boundary_matching_chartType := by
  intro d N M hM S hS p
  have hset := boundary_set  hM S hS
  have hq : p.val.val ∈ Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 (d+1) M := by
    exact (Set.ext_iff.mp hset p.val).mp p.property
  obtain ⟨c, u, hu, hcu⟩ := hM.2.2 p.val.val p.val.property
  have hpambient : p.val.val ∈ c.ambient := by
    rw [← hcu]
    exact (c.map_source hu.1).2
  let c₂ := lowerChart c (by simp : (2 : ℕ∞ω) ≤ ∞)
  have hM₂ := (EmbeddedAtlasResults.smooth_c2_tangents hM).1
  have hb : IsBoundaryParameter c u := by
    apply (D04.chart_intrinsicBoundary c₂ hM₂.1 hM₂.2.1 u hu.1).mp
    change c.toFun u ∈ _
    rwa [hcu]
  have hhalf : c.half = true := hb.1
  have hchart : ∃ e : ModelChart (d+1) .halfSpace M,
      e.source = {q : M | q.val ∈ c.ambient} ∧ MatchesEmbeddedChart e c := by
    have hk : (if c.half then ModelKind.halfSpace else ModelKind.euclidean) = .halfSpace := by
      simp [hhalf]
    have hc := embedded_model_chart c p.val hpambient
    rw [hk] at hc
    exact hc
  obtain ⟨e, hs, hm⟩ := hchart
  have he : e ∈ S.smoothStructure.val := by
    change S.smoothStructure.val = _ at hS
    rw [hS]
    exact raw_of_matching e c hm
  exact ⟨c, u, hu.1, e, he, hm, hb, hcu, by rw [hs]; exact hpambient⟩

/-- Globalization uses a derived matching chart, and then uniqueness removes
all the auxiliary chart choices from the boundary tangent identification. -/
theorem boundary_geometry :
    Specs.SmoothManifolds.Integration.EmbeddedBoundary.boundary_geometryType := by
  intro d N a M hM S hS I hI C p
  cases a with
  | euclidean =>
    have hp := p.property
    change p.val ∈ _root_.SmoothManifolds.intrinsicBoundary S at hp
    rw [intrinsicBoundary_euclidean S] at hp
    exact hp.elim
  | halfSpace =>
    obtain ⟨c, u, hu, e, he, hm, hb, hcu, hpe⟩ :=
      boundary_matching_chart  hM S hS p
    rcases p with ⟨p, hp⟩
    have hpEq : (⟨c.toFun u, (c.map_source hu).1⟩ : M) = p := Subtype.ext hcu
    subst p
    obtain ⟨hp', hq, hgeo⟩ := matching_boundary_geometry
       hM S hS I hI C e he c hm u hu hb hpe
    exact ⟨hq, hgeo⟩


/-- Canonical determinant duality, including degree zero. -/
theorem determinant_duality :
    Specs.SmoothManifolds.Integration.EmbeddedBoundary.determinant_dualityType.{u,v} :=
  determinant_duality_proof

/-- The pointwise comparison assembles into the actual restriction field.
Differentials exist by smoothness of the natural boundary inclusion. -/
theorem boundary_restriction :
    Specs.SmoothManifolds.Integration.EmbeddedBoundary.boundary_restrictionType := by
  intro d N a M hM S hS I hI C B hB
  classical
  have hdiff (p : intrinsicBoundary S) :=
    differential_exists B S Subtype.val hB.1 p
  choose L hL hLunique using hdiff
  have hgeo (p : intrinsicBoundary S) := boundary_geometry
     hM S hS I hI C p
  choose hq hgeo using hgeo
  have hJ (p : intrinsicBoundary S) := hgeo p B hB (L p) (hL p)
  choose J hJ hJunique using hJ
  refine ⟨hq, L, hL, J, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact fun p => (hJ p).1
  · intro k η p
    exact (hJ p).2.2.2 k (η p.val)
  · intro η p
    exact (hJ p).2.2.2 d (η p.val)
  · intro J' hJ'
    funext p
    apply LinearEquiv.ext
    intro v
    apply Subtype.ext
    exact (hJ'.1 p v).trans ((hJ p).1 v).symm

section RawChartConstruction
open Set Filter Topology
open Specs.D04.C14.EmbeddedManifoldCharts.Model
private theorem injective_fderiv_eventually {n N : ℕ}
    {H : Euclidean n → Euclidean N} {V : Set (Euclidean n)}
    (hV : IsOpen V) {x : Euclidean n} (hx : x ∈ V)
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H V)
    (hinj : Function.Injective (fderiv ℝ H x)) :
    ∀ᶠ y in 𝓝 x, Function.Injective (fderiv ℝ H y) := by
  obtain ⟨A, hA⟩ := (fderiv ℝ H x).toLinearMap.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hinj)
  let B : Euclidean N →L[ℝ] Euclidean n := LinearMap.toContinuousLinearMap A
  have hBx : B.comp (fderiv ℝ H x) = 1 := by
    apply ContinuousLinearMap.ext
    intro v
    exact DFunLike.congr_fun hA v
  have hcont : ContinuousAt (fun y => B.comp (fderiv ℝ H y)) x := by
    exact ((ContinuousLinearMap.compL ℝ (Euclidean n) (Euclidean N) (Euclidean n) B).continuous.continuousAt.comp
      (((hH.continuousOn_fderiv_of_isOpen hV (by simp)) x hx).continuousAt (hV.mem_nhds hx)))
  have hh : ∀ᶠ y in 𝓝 x, IsUnit (B.comp (fderiv ℝ H y)) := by
    apply hcont (Units.isOpen.mem_nhds ?_)
    change IsUnit (B.comp (fderiv ℝ H x))
    rw [hBx]
    exact isUnit_one
  filter_upwards [hh] with y hy
  intro v w hvw
  apply (ContinuousLinearMap.isUnit_iff_bijective.mp hy).injective
  exact congrArg B hvw

/-- An actual D04 chart realizing an intrinsic raw chart, without assuming any
boundary or differential comparison. -/
theorem embedded_chart_of_raw {n N : ℕ} {a : ModelKind} {M : Set (E N)}
    (e : ModelChart n a M) (he : IsRawEmbeddedChart e)
    (p₀ : M) (hp₀ : p₀ ∈ e.source) :
    ∃ c : EmbeddedChart ∞ n N M,
      MatchesEmbeddedChart e c ∧
      (∀ (u : E n) (hu : u ∈ c.source),
        (⟨c.toFun u, (c.map_source hu).1⟩ : M) ∈ e.source) ∧
      p₀.val ∈ c.ambient := by
  classical
  obtain ⟨O, hO, hOe⟩ := isOpen_induced_iff.mp e.open_source
  obtain ⟨V, hV, hVe⟩ := isOpen_induced_iff.mp e.open_target
  let b : Bool := match a, n with | .halfSpace, _+1 => true | _, _ => false
  have hmodel (z : E n) : z ∈ parameterSpace n b ↔ piCoordinates n z ∈ modelSet n a := by
    cases a <;> cases n <;>
      simp [b, parameterSpace, halfSpace, ModelData.modelSet, ModelData.halfSpaceSet,
        piCoordinates, EuclideanSpace.equiv]
  let D : Set (E n) := parameterSpace n b ∩ piCoordinates n ⁻¹' V
  let ψ : E n → M := fun z =>
    if hz : piCoordinates n z ∈ modelSet n a then e.symm ⟨piCoordinates n z, hz⟩ else p₀
  let χ : E N → E n := fun x =>
    if hx : x ∈ M then (piCoordinates n).symm (e ⟨x, hx⟩).val
      else (piCoordinates n).symm (e p₀).val
  have hψ (z : E n) (hz : z ∈ D) :
      ψ z = e.symm ⟨piCoordinates n z, (hmodel z).mp hz.1⟩ := by
    simp [ψ, (hmodel z).mp hz.1]
  have ht (z : E n) (hz : z ∈ D) :
      (⟨piCoordinates n z, (hmodel z).mp hz.1⟩ : ModelSpace n a) ∈ e.target := by
    rw [← hVe]
    exact hz.2
  have hψsource (z : E n) (hz : z ∈ D) : ψ z ∈ e.source := by
    rw [hψ z hz]
    exact e.symm.map_source (ht z hz)
  have hχ (x : M) : χ x.val = (piCoordinates n).symm (e x).val := by simp [χ]
  have hχD (x : M) (hx : x ∈ e.source) : χ x.val ∈ D := by
    rw [hχ]
    refine ⟨(hmodel _).mpr ?_, ?_⟩
    · simpa only [ContinuousLinearEquiv.apply_symm_apply] using (e x).property
    · change piCoordinates n ((piCoordinates n).symm (e x).val) ∈ V
      rw [ContinuousLinearEquiv.apply_symm_apply]
      change e x ∈ Subtype.val ⁻¹' V
      rw [hVe]
      exact e.map_source hx
  have hleft (z : E n) (hz : z ∈ D) : χ (ψ z).val = z := by
    rw [hχ, hψ z hz, e.right_inv (ht z hz), ContinuousLinearEquiv.symm_apply_apply]
  have hright (x : M) (hx : x ∈ e.source) : ψ (χ x.val) = x := by
    rw [hψ _ (hχD x hx)]
    have htEq : (⟨piCoordinates n (χ x.val), (hmodel _).mp (hχD x hx).1⟩ : ModelSpace n a) = e x := by
      apply Subtype.ext
      simp only [hχ, ContinuousLinearEquiv.apply_symm_apply]
    rw [htEq, e.left_inv hx]
  have hψcont : ContinuousOn ψ D := by
    rw [continuousOn_iff_continuous_domRestrict]
    let f : D → ModelSpace n a := fun z => ⟨piCoordinates n z.val, (hmodel _).mp z.property.1⟩
    have hf : Continuous f := by fun_prop
    have hh := e.symm.continuousOn.comp_continuous hf (fun z => ht z.val z.property)
    apply hh.congr
    intro z
    exact (hψ z.val z.property).symm
  have hχcont : ContinuousOn χ (M ∩ O) := by
    rw [continuousOn_iff_continuous_domRestrict]
    let f : (M ∩ O : Set (E N)) → M := fun x => ⟨x.val, x.property.1⟩
    have hf : Continuous f := by fun_prop
    have hfx (x : (M ∩ O : Set (E N))) : f x ∈ e.source := by
      rw [← hOe]
      exact x.property.2
    have hh := (piCoordinates n).symm.continuous.comp
      (continuous_subtype_val.comp (e.continuousOn.comp_continuous hf hfx))
    apply hh.congr
    intro x
    exact (hχ (f x)).symm
  have hregular : FullRankLocalExtension ∞ D (fun z => (ψ z).val) := by
    intro z hz
    let p := ψ z
    have hp := hψsource z hz
    have hep : (e p).val = piCoordinates n z := by
      dsimp [p]
      rw [hψ z hz, e.right_inv (ht z hz)]
    obtain ⟨U, H, hU, hpU, hH, heq, hinj⟩ := he p hp
    obtain ⟨T, hTsub, hT, hpT⟩ := mem_nhds_iff.mp heq
    obtain ⟨Z, hZ, hZe⟩ := isOpen_induced_iff.mp (e.symm.isOpen_inter_preimage hT)
    have hzZ : piCoordinates n z ∈ Z := by
      change (⟨piCoordinates n z, (hmodel z).mp hz.1⟩ : ModelSpace n a) ∈ Subtype.val ⁻¹' Z
      rw [hZe]
      refine ⟨ht z hz, ?_⟩
      change e.symm ⟨piCoordinates n z, (hmodel z).mp hz.1⟩ ∈ T
      rw [← hψ z hz]
      exact hpT
    have hfull := injective_fderiv_eventually hU hpU hH hinj
    obtain ⟨R, hRsub, hR, hpR⟩ := mem_nhds_iff.mp hfull
    let W : Set (E n) := piCoordinates n ⁻¹' (U ∩ Z ∩ R)
    let G : E n → E N := fun v => (piCoordinates N).symm (H (piCoordinates n v))
    have hzW : z ∈ W := by
      refine ⟨⟨?_, hzZ⟩, ?_⟩ <;> rwa [← hep]
    have hW : IsOpen W := ((hU.inter hZ).inter hR).preimage (piCoordinates n).continuous
    have hG : ContDiffOn ℝ ∞ G W := by
      exact (piCoordinates N).symm.contDiff.comp_contDiffOn
        (hH.comp (piCoordinates n).contDiff.contDiffOn (fun v hv => hv.1.1))
    refine ⟨W, G, hW, hzW, ?_, hG, ?_⟩
    · intro v hv
      rcases hv with ⟨hvD, hvW⟩
      have hvZ : (⟨piCoordinates n v, (hmodel v).mp hvD.1⟩ : ModelSpace n a) ∈
          e.symm.source ∩ e.symm ⁻¹' T := by
        rw [← hZe]
        exact hvW.1.2
      have hqT : ψ v ∈ T := by
        rw [hψ v hvD]
        exact hvZ.2
      have hh := hTsub hqT
      change H (e (ψ v)).val = piCoordinates N (ψ v).val at hh
      have hep' : (e (ψ v)).val = piCoordinates n v := by
        rw [hψ v hvD, e.right_inv (ht v hvD)]
      change (piCoordinates N).symm (H (piCoordinates n v)) = (ψ v).val
      rw [← hep', hh, ContinuousLinearEquiv.symm_apply_apply]
    · intro v hv
      have hvU := hv.1.1
      have hHv := ((hH.contDiffAt (hU.mem_nhds hvU)).differentiableAt (by simp)).hasFDerivAt
      have hderiv : fderiv ℝ G v = (piCoordinates N).symm.toContinuousLinearMap.comp
          ((fderiv ℝ H (piCoordinates n v)).comp (piCoordinates n).toContinuousLinearMap) := by
        exact ((piCoordinates N).symm.hasFDerivAt.comp _
          (hHv.comp _ (piCoordinates n).hasFDerivAt)).fderiv
      rw [hderiv]
      exact (piCoordinates N).symm.injective.comp ((hRsub hv.2).comp (piCoordinates n).injective)
  let c : EmbeddedChart ∞ n N M := {
    half := b
    half_pos := by cases a <;> cases n <;> simp_all [b]
    source := D
    source_open := ⟨piCoordinates n ⁻¹' V, hV.preimage (piCoordinates n).continuous, rfl⟩
    ambient := O
    ambient_open := hO
    toFun := fun z => (ψ z).val
    invFun := χ
    map_source := by
      intro z hz
      refine ⟨(ψ z).property, ?_⟩
      change ψ z ∈ Subtype.val ⁻¹' O
      rw [hOe]
      exact hψsource z hz
    map_target := by
      intro x hx
      apply hχD ⟨x, hx.1⟩
      rw [← hOe]
      exact hx.2
    left_inv := hleft
    right_inv := by
      intro x hx
      exact congrArg Subtype.val (hright ⟨x, hx.1⟩ (by rw [← hOe]; exact hx.2))
    continuous_toFun := continuous_subtype_val.comp_continuousOn hψcont
    continuous_invFun := hχcont
    regular := hregular }
  refine ⟨c, ?_, ?_, ?_⟩
  · intro p hp
    refine ⟨?_, ?_⟩
    · change p ∈ Subtype.val ⁻¹' O
      rwa [hOe]
    · change (e p).val = piCoordinates n (χ p.val)
      rw [hχ, ContinuousLinearEquiv.apply_symm_apply]
  · exact hψsource
  · change p₀ ∈ Subtype.val ⁻¹' O
    rwa [hOe]

end RawChartConstruction

section OrientationTransport
open Set Filter Topology TangentBundleData OrientationData
open Specs.D04.C14.OrientationsAndChartSigns.Model
theorem orientation_chart_sign
    (matching : Specs.SmoothManifolds.Integration.EmbeddedAtlas.matching_chart_pullbackType)
    {n N : ℕ} {a : ModelKind} {M : Set (E N)} (hM : IsEmbeddedManifold ∞ n M)
    (S : SmoothManifold n a M) (hS : IsInducedSmoothStructure S)
    (I : (p : M) → TangentSpace S p ≃ₗ[ℝ] tangentSpace 2 n M p.val)
    (hI : IsInclusionIdentification S I) (C : BundleOperationsData.CotangentBundle S)
    (o : OrientationData.Orientation S)
    (O : TangentOrientationField 2 n M)
    (hO : ∀ (p : M) (b : Module.Basis (Fin n) ℝ (tangentSpace 2 n M p.val)),
      b.orientation = O p.val p.property ↔
        IsPositive (o.val p) (exteriorPower.ιMulti ℝ n (fun j => (I p).symm (b j))))
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
    (c : EmbeddedChart ∞ n N M) (hm : MatchesEmbeddedChart e c)
    (hsource : ∀ (u : E n) (hu : u ∈ c.source),
      (⟨c.toFun u, (c.map_source hu).1⟩ : M) ∈ e.source) :
    IsLocallyConstant (fun u : c.source =>
      chartSign O (lowerChart c (by simp : (2 : ℕ∞ω) ≤ ∞)) u u.property) := by
  classical
  let c₂ := lowerChart c (by simp : (2 : ℕ∞ω) ≤ ∞)
  obtain ⟨s, hs, _⟩ := (OrientationResults.signed_charts S o.val).mp o.property
  let f : c.source → e.source := fun u =>
    ⟨⟨c.toFun u, (c.map_source u.property).1⟩, hsource u u.property⟩
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    exact c.continuous_toFun.domRestrict.subtype_mk _
  have hlocal := (s.locallyConstant e he).comp_continuous hf
  have heq : (fun u : c.source => chartSign O c₂ u u.property) =
      (fun u : c.source => signValue (s.sign e he (f u))) := by
    funext u
    let p : M := ⟨c.toFun u, (c.map_source u.property).1⟩
    let hp := hsource u u.property
    let K := C.tangent.fiberCoordinates
    let A := K.equiv e he p hp
    let b : Module.Basis (Fin n) ℝ (tangentSpace 2 n M p.val) := D04.Orientations.chartBasis c₂ (by constructor <;> norm_num) hM.2.1 u u.property
    have hcoord := (matching S hS I hI C e he c hm u u.property hp).1
    have hvec (j : Fin n) : (I p).symm (b j) = A.symm ((Pi.basisFun ℝ (Fin n)) j) := by
      apply (I p).injective
      rw [LinearEquiv.apply_symm_apply]
      have hb : b j = Specs.D04.C15.IntrinsicExteriorDerivative.Model.chartTangentMap c₂ u u.property (standardBasis n j) := rfl
      rw [hb, ← hcoord]
      congr 1
    have hpos := (BoundaryOrientations.positive_signed_generator_iff (o.val p)
      (coordinateVector K e he ⟨p, hp⟩) (s.sign e he ⟨p, hp⟩) (hs K e he ⟨p, hp⟩)).1
    have hbpos : b.orientation = O p.val p.property ↔ s.sign e he (f u) = true := by
      rw [hO p b]
      simpa only [hvec, coordinateVector] using hpos
    have hsign : chartSign O c₂ u u.property = 1 ↔ s.sign e he (f u) = true := by
      exact (D04.Orientations.chartSign_basis O c₂ u u.property b (fun _ => rfl)).trans hbpos
    rcases D04.Orientations.chartSign_values O c₂ (by constructor <;> norm_num) hM.2.1 u u.property with hv | hv
    · rw [hv, (hsign.mp hv)]
      rfl
    · have hfalse : s.sign e he (f u) = false := by
        cases h : s.sign e he (f u)
        · rfl
        · have hh := hsign.mpr h
          linarith
      rw [hv, hfalse]
      rfl
  rw [heq]
  exact hlocal.comp signValue



theorem orientation_transport_proof
    (matching : Specs.SmoothManifolds.Integration.EmbeddedAtlas.matching_chart_pullbackType)
    (lowerTangents : Specs.SmoothManifolds.Integration.EmbeddedAtlas.smooth_c2_tangentsType)
    {n N : ℕ} {a : ModelKind} {M : Set (E N)} (hn : 0 < n)
    (hM : IsEmbeddedManifold ∞ n M)
    (S : SmoothManifold n a M) (hS : IsInducedSmoothStructure S)
    (I : (p : M) → TangentSpace S p ≃ₗ[ℝ] tangentSpace 2 n M p.val)
    (hI : IsInclusionIdentification S I) (C : BundleOperationsData.CotangentBundle S)
    (o : OrientationData.Orientation S) :
    ∃! O : PositiveManifoldOrientation 2 n M,
      ∀ (p : M) (b : Module.Basis (Fin n) ℝ (tangentSpace 2 n M p.val)),
        b.orientation = O.atPoint p.val p.property ↔
          IsPositive (o.val p) (exteriorPower.ιMulti ℝ n (fun j => (I p).symm (b j))) := by
  classical
  have hdual (p : M) : ∃! O : _root_.Orientation ℝ (tangentSpace 2 n M p.val) (Fin n),
      ∀ b : Module.Basis (Fin n) ℝ (tangentSpace 2 n M p.val),
        b.orientation = O ↔
          IsPositive (o.val p) (exteriorPower.ιMulti ℝ n (fun j => (I p).symm (b j))) := by
    letI := (tangent_dimension S p).1
    exact determinant_duality_proof n (tangent_dimension S p).2 (I p) (o.val p)
  choose O hO hOunique using hdual
  let F : TangentOrientationField 2 n M := fun x hx => O ⟨x, hx⟩
  have hM₂ := (lowerTangents hM).1
  have hlocal (c : EmbeddedChart 2 n N M) :
      IsLocallyConstant (fun u : c.source => chartSign F c u u.property) := by
    apply (IsLocallyConstant.iff_exists_open _).mpr
    intro u
    let p : M := ⟨c.toFun u, (c.map_source u.property).1⟩
    obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
    have heRaw : IsRawEmbeddedChart e := by
      change S.smoothStructure.val = _ at hS
      rw [hS] at he
      exact he
    obtain ⟨d, hm, hs, hd⟩ := embedded_chart_of_raw e heRaw p hp
    have ha := orientation_chart_sign matching hM S hS I hI C o F hO e he d hm hs
    exact D04BoundaryOrientation.field_sign_locally_constant hM₂ F c
      (lowerChart d (by simp : (2 : ℕ∞ω) ≤ ∞)) ha u hd
  let res : PositiveManifoldOrientation 2 n M := ⟨hn, hM₂, F, hlocal⟩
  refine ⟨res, hO, ?_⟩
  intro O' hO'
  apply D04BoundaryOrientation.manifoldOrientation_ext
  funext x hx
  exact hOunique ⟨x, hx⟩ (O'.atPoint x hx) (hO' ⟨x, hx⟩)

end OrientationTransport

/-- Canonical transport includes the full D04 local constancy requirement. -/
theorem orientation_transport :
    Specs.SmoothManifolds.Integration.EmbeddedBoundary.orientation_transportType := by
  intro n N a M hn hM S hS I hI C o
  exact orientation_transport_proof EmbeddedAtlasResults.matching_chart_pullback EmbeddedAtlasResults.smooth_c2_tangents hn hM S hS I hI C o

theorem boundary_outward_rays :
    Specs.SmoothManifolds.Integration.EmbeddedBoundary.boundary_outward_raysType := by
  intro d N a M hM S hS I hI C p
  cases a with
  | euclidean =>
    have hp := p.property
    change p.val ∈ _root_.SmoothManifolds.intrinsicBoundary S at hp
    rw [intrinsicBoundary_euclidean S] at hp
    exact hp.elim
  | halfSpace =>
    obtain ⟨c, u, hu, e, he, hm, hb, hcu, hpe⟩ :=
      EmbeddedBoundaryResults.boundary_matching_chart  hM S hS p
    rcases p with ⟨p, hp⟩
    have hpEq : (⟨c.toFun u, (c.map_source hu).1⟩ : M) = p := Subtype.ext hcu
    subst p
    obtain ⟨hp', hgeo⟩ := EmbeddedBoundaryResults.matching_outward_rays
       hM S hS I hI C e he c hm u hu hb hpe
    exact hgeo


theorem boundary_tangent_hyperplane :
    Specs.SmoothManifolds.Integration.EmbeddedBoundary.boundary_tangent_hyperplaneType := by
  intro d N a M hM S hS I hI C c u hu hb
  let p : M := ⟨c.toFun u, (c.map_source hu).1⟩
  let c₂ := lowerChart c (by simp : (2 : ℕ∞ω) ≤ ∞)
  have hq : p.val ∈ Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 (d+1) M :=
    ⟨p.property, c₂, u, hb.1, hu, hb.2, rfl⟩
  have hset := EmbeddedBoundaryResults.boundary_set
     hM S hS
  have hp : p ∈ intrinsicBoundary S := (Set.ext_iff.mp hset p).mpr hq
  refine ⟨hp, ?_⟩
  intro B hB L hL
  obtain ⟨hq', hgeo⟩ := EmbeddedBoundaryResults.boundary_geometry
     hM S hS I hI C ⟨p, hp⟩
  obtain ⟨J, hJ, hJunique⟩ := hgeo B hB L hL
  let K : TangentSpace B ⟨p, hp⟩ →ₗ[ℝ] E N :=
    (tangentSpace 2 (d+1) M p.val).subtype.comp ((I p).toLinearMap.comp L)
  have hrange : LinearMap.range K =
      tangentSpace 2 d (Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 (d+1) M) p.val := by
    ext z
    constructor
    · rintro ⟨v, rfl⟩
      change (I p (L v)).val ∈ tangentSpace 2 d
        (Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 (d+1) M) p.val
      rw [← hJ.1 v]
      exact (J v).property
    · intro hz
      obtain ⟨v, hv⟩ := J.surjective ⟨z, hz⟩
      refine ⟨v, ?_⟩
      change (I p (L v)).val = z
      exact (hJ.1 v).symm.trans (congrArg Subtype.val hv)
  refine ⟨hrange, ?_⟩
  rw [hrange]
  have hM₂ := (EmbeddedAtlasResults.smooth_c2_tangents hM).1
  exact D04.tangentSpace_intrinsic_boundary c₂ hM₂.1 hM₂.2.1 hb.1 u hu hb.2

private def boundaryBaseHomeomorph {n N : ℕ} {a : ModelKind} {M : Set (E N)}
    (S : SmoothManifold n a M)
    (h : intrinsicBoundary S = Subtype.val ⁻¹'
      Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 n M) :
    intrinsicBoundary S ≃ₜ Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 n M where
  toFun p := ⟨p.val.val, by
    exact (Set.ext_iff.mp h p.val).mp p.property⟩
  invFun q := ⟨⟨q.val, q.property.1⟩, by
    exact (Set.ext_iff.mp h ⟨q.val, q.property.1⟩).mpr q.property⟩
  left_inv p := by apply Subtype.ext; rfl
  right_inv q := by apply Subtype.ext; rfl
  continuous_toFun := by
    fun_prop
  continuous_invFun := by
    fun_prop


theorem boundary_base :
    Specs.SmoothManifolds.Integration.EmbeddedBoundary.boundary_baseType := by
  intro n N a M hM S hS
  have h := boundary_set  hM S hS
  refine ⟨boundaryBaseHomeomorph S h, (fun p => rfl), ?_⟩
  intro β hβ
  apply Homeomorph.ext
  intro p
  apply Subtype.ext
  exact hβ p

end SmoothManifolds.EmbeddedBoundaryResults

namespace SmoothManifolds.EmbeddedBoundaryOrientation
open BoundaryOrientationData OrientationData
universe u v
theorem normalWedge_ιMulti {V : Type u} {W : Type v}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    {n : ℕ} (L : W →ₗ[ℝ] V) (v : V) (b : Fin n → W) :
    normalWedge L v (exteriorPower.ιMulti ℝ n b) =
      exteriorPower.ιMulti ℝ (n+1) (Fin.cons v (fun i => L (b i))) := by
  apply Subtype.ext
  simp only [BoundaryOrientations.coe_normalWedge, exteriorPower.ιMulti_apply_coe,
    ExteriorAlgebra.map_apply_ιMulti, ExteriorAlgebra.ιMulti_succ_apply]
  rfl


open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.ChartIndependentTangentSpaces.Model
open Specs.D04.C14.OrientationsAndChartSigns.Model
open Specs.D04.C14.OutwardFirstBoundaryOrientation.Model

/-- Pointwise agreement with the actual D04 outward-first basis test. -/
theorem positiveWithOutward_iff_intrinsic
    {V : Type u} {W : Type v} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] {d N : ℕ} {M : Set (E N)}
    (O : PositiveManifoldOrientation 2 (d+1) M)
    (x : Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 (d+1) M) (ν : E N)
    (hν : IsOutwardUnitConormal 2 d M x ν)
    (I : V ≃ₗ[ℝ] tangentSpace 2 (d+1) M x)
    (J : W ≃ₗ[ℝ] tangentSpace 2 d (Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 (d+1) M) x)
    (L : W →ₗ[ℝ] V) (hJ : ∀ w, (J w).val = (I (L w)).val)
    (r : Module.Ray ℝ (⋀[ℝ]^(d+1) V))
    (hO : ∀ BB : Module.Basis (Fin (d+1)) ℝ (tangentSpace 2 (d+1) M x),
      BB.orientation = O.atPoint x x.property.1 ↔
        IsPositive r (exteriorPower.ιMulti ℝ (d+1) (fun i => I.symm (BB i))))
    (b : Module.Basis (Fin d) ℝ
      (tangentSpace 2 d (Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 (d+1) M) x)) :
    PositiveWithOutward O x ν b ↔
      IsPositive r (normalWedge L (I.symm ⟨ν, hν.1⟩)
        (exteriorPower.ιMulti ℝ d (fun i => J.symm (b i)))) := by
  let BB := D04BoundaryOrientation.extendedBoundaryBasis O.manifold x ν hν b
  have htest : PositiveWithOutward O x ν b ↔ BB.orientation = O.atPoint x x.property.1 := by
    constructor
    · rintro ⟨C, h0, hs, hC⟩
      have heq : BB = C := by
        apply DFunLike.ext
        intro i
        dsimp only [BB]
        rw [D04BoundaryOrientation.extendedBoundaryBasis_apply]
        refine Fin.cases ?_ (fun j => ?_) i
        · exact Subtype.ext h0.symm
        · exact Subtype.ext (hs j).symm
      simpa only [heq] using hC
    · intro hBB
      refine ⟨BB, ?_, ?_, hBB⟩
      · dsimp only [BB]
        rw [D04BoundaryOrientation.extendedBoundaryBasis_apply]
        rfl
      · intro i
        dsimp only [BB]
        rw [D04BoundaryOrientation.extendedBoundaryBasis_apply]
        rfl
  rw [htest, hO, normalWedge_ιMulti]
  have heq : (fun i => I.symm (BB i)) =
      Fin.cons (I.symm ⟨ν, hν.1⟩) (fun i => L (J.symm (b i))) := by
    funext i
    dsimp only [BB]
    rw [D04BoundaryOrientation.extendedBoundaryBasis_apply]
    refine Fin.cases rfl (fun j => ?_) i
    apply I.injective
    simp only [LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    exact (by simpa using hJ (J.symm (b j)))
  rw [heq]


/-- Once the geometric inclusion identifications are proved, the existing D04
boundary orientation is precisely the transported intrinsic induced orientation.
The D04 local constancy is supplied by its actual boundary_orientation theorem. -/
theorem boundary_orientation_comparison
    {d N : ℕ} {a : _root_.SmoothManifolds.ModelKind} {M : Set (E N)}
    (S : SmoothManifolds.AtlasData.SmoothManifold (d+2) a M)
    (B : SmoothManifolds.AtlasData.SmoothManifold (d+1) .euclidean
      (SmoothManifolds.BoundaryData.intrinsicBoundary S))
    (o : SmoothManifolds.OrientationData.Orientation S)
    (q : SmoothManifolds.OrientationData.Orientation B)
    (hind : IsInducedOrientation o q)
    (I : (p : M) → SmoothManifolds.TangentData.TangentSpace S p ≃ₗ[ℝ]
      tangentSpace 2 (d+2) M p.val)
    (hq : ∀ p : SmoothManifolds.BoundaryData.intrinsicBoundary S,
      p.val.val ∈ Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 (d+2) M)
    (L : (p : SmoothManifolds.BoundaryData.intrinsicBoundary S) →
      SmoothManifolds.TangentData.TangentSpace B p →ₗ[ℝ]
      SmoothManifolds.TangentData.TangentSpace S p.val)
    (hL : ∀ p, SmoothManifolds.DifferentialData.IsDifferential B S Subtype.val p (L p))
    (J : (p : SmoothManifolds.BoundaryData.intrinsicBoundary S) →
      SmoothManifolds.TangentData.TangentSpace B p ≃ₗ[ℝ]
      tangentSpace 2 (d+1) (Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 (d+2) M) p.val.val)
    (hJ : ∀ p w, (J p w).val = (I p.val (L p w)).val)
    (hout : ∀ p v, IsOutward S p v ↔ IsOutwardVector 2 (d+1) M p.val.val (I p.val v).val)
    (O : PositiveManifoldOrientation 2 (d+2) M)
    (hO : ∀ (p : SmoothManifolds.BoundaryData.intrinsicBoundary S)
      (BB : Module.Basis (Fin (d+2)) ℝ (tangentSpace 2 (d+2) M p.val.val)),
      BB.orientation = O.atPoint p.val.val p.val.property ↔
        IsPositive (o.val p.val) (exteriorPower.ιMulti ℝ (d+2) (fun i => (I p.val).symm (BB i))))
    (ν : Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 (d+2) M → E N)
    (hν : ∀ x : Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 (d+2) M,
      IsOutwardUnitConormal 2 (d+1) M x (ν x)) :
    ∃! bO : PositiveManifoldOrientation 2 (d+1) (Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 (d+2) M),
      (∀ (x : Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 (d+2) M)
        (b : Module.Basis (Fin (d+1)) ℝ (tangentSpace 2 (d+1) (Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 (d+2) M) x)),
        b.orientation = bO.atPoint x x.property ↔ PositiveWithOutward O x (ν x) b) ∧
      (∀ (p : SmoothManifolds.BoundaryData.intrinsicBoundary S)
        (b : Module.Basis (Fin (d+1)) ℝ
          (tangentSpace 2 (d+1) (Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 (d+2) M) p.val.val)),
        b.orientation = bO.atPoint p.val.val (hq p) ↔
          IsPositive (q.val p)
            (exteriorPower.ιMulti ℝ (d+1) (fun i => (J p).symm (b i)))) := by
  obtain ⟨bO, hbO, huniq⟩ := D04BoundaryOrientation.boundary_orientation O ν hν
  refine ⟨bO, ⟨hbO, ?_⟩, ?_⟩
  · intro p b
    let x : Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 (d+2) M := ⟨p.val.val, hq p⟩
    let v := (I p.val).symm ⟨ν x, (hν x).1⟩
    have hv : IsOutward S p v := by
      apply (hout p v).mpr
      simpa only [v, LinearEquiv.apply_symm_apply] using (hν x).2.2.2
    rw [hbO x b,
      positiveWithOutward_iff_intrinsic
        (V := SmoothManifolds.TangentData.TangentSpace S p.val)
        (W := SmoothManifolds.TangentData.TangentSpace B p)
        O x (ν x) (hν x) (I p.val) (J p) (L p) (hJ p)
        (o.val p.val) (hO p)]
    exact (hind p (L p) (hL p) v hv _).symm
  · intro bO' hbO'
    exact huniq bO' hbO'.1

end SmoothManifolds.EmbeddedBoundaryOrientation

namespace SmoothManifolds.EmbeddedBoundaryResults
open ModelData AtlasData BoundaryData TangentData DifferentialData EmbeddedCalculusData
  EmbeddedAtlasData BoundaryOrientationData ExteriorData OrientationData
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model (IsEmbeddedManifold)
open Specs.D04.C14.ChartIndependentTangentSpaces.Model (tangentSpace)
open Specs.D04.C14.OrientationsAndChartSigns.Model
universe u v
theorem boundary_orientation_proof
    (transport : Specs.SmoothManifolds.Integration.EmbeddedBoundary.orientation_transportType)
    (geometry : Specs.SmoothManifolds.Integration.EmbeddedBoundary.boundary_geometryType) :
    Specs.SmoothManifolds.Integration.EmbeddedBoundary.boundary_orientationType := by
  intro d N a M hM S hS I hI C o
  classical
  obtain ⟨O, hO, hOunique⟩ := transport (by omega) hM S hS I hI C o
  refine ⟨O, hO, ?_⟩
  intro B hB q hind
  have hdiff (p : intrinsicBoundary S) :=
    SmoothManifolds.differential_exists B S Subtype.val hB.1 p
  choose L hL hLunique using hdiff
  have hgeo (p : intrinsicBoundary S) := geometry hM S hS I hI C p
  choose hq hgeo using hgeo
  have hJ (p : intrinsicBoundary S) := hgeo p B hB (L p) (hL p)
  choose J hJ hJunique using hJ
  refine ⟨hq, L, J, hL, (fun p => (hJ p).1), ?_⟩
  intro ν hν
  exact EmbeddedBoundaryOrientation.boundary_orientation_comparison S B o q hind I hq L hL J
    (fun p => (hJ p).1) (fun p => (hJ p).2.1) O (fun p => hO p.val) ν hν
/-- The original orientation hypotheses produce both actual continuous D04
orientations and their outward-first agreement; no compatibility is assumed. -/
theorem boundary_orientation :
    Specs.SmoothManifolds.Integration.EmbeddedBoundary.boundary_orientationType :=
  boundary_orientation_proof
    orientation_transport
    boundary_geometry

end SmoothManifolds.EmbeddedBoundaryResults

namespace SmoothManifolds.EmbeddedBoundaryPointOrientation
open ModelData AtlasData TangentData OrientationData BoundaryData BoundaryOrientationData
  DifferentialData EmbeddedCalculusData EmbeddedAtlasData
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model (IsEmbeddedManifold)
open Specs.D04.C14.ChartIndependentTangentSpaces.Model (tangentSpace)
open Specs.D04.C14.OrientationsAndChartSigns.Model
open Specs.D04.C14.OutwardFirstBoundaryOrientation.Model
universe u v
theorem zero_orientation_transport_along {X : Type u} [TopologicalSpace X]
    {Y : Type v} {a : SmoothManifolds.ModelKind}
    (S : SmoothManifolds.AtlasData.SmoothManifold 0 a X) (β : X ≃ Y) :
    ∃ F : Orientation S ≃ (Y → PointSign),
      ∀ (o : Orientation S) (p : X),
        ((F o (β p)).val = 1 ↔ IsPositive (o.val p)
          ((exteriorPower.zeroEquiv ℝ (TangentSpace S p)).symm 1)) := by
  classical
  obtain ⟨e, he⟩ := SmoothManifolds.OrientationResults.zero_dimension S
  let eSign : Bool ≃ PointSign := {
    toFun := fun b => if b then ⟨1, Or.inl rfl⟩ else ⟨-1, Or.inr rfl⟩
    invFun := fun s => decide (s.val = 1)
    left_inv := by intro b; cases b <;> norm_num
    right_inv := by
      intro s
      rcases s.property with h | h
      · apply Subtype.ext
        simp [h]
      · apply Subtype.ext
        norm_num [h] }
  let H : (X → PointSign) ≃ (Y → PointSign) :=
    Equiv.arrowCongr β (Equiv.refl _)
  refine ⟨(e.trans (Equiv.piCongrRight fun _ => eSign)).trans H, ?_⟩
  intro o p
  change ((eSign (e o (β.symm (β p)))).val = 1 ↔ _)
  rw [β.symm_apply_apply, ← he]
  cases h : e o p <;> norm_num [eSign, h]

/-- Literal Euclidean-base version, including the empty manifold. -/
theorem zero_orientation_transport {N : ℕ} {a : SmoothManifolds.ModelKind} (M : Set (E N))
    (S : SmoothManifolds.AtlasData.SmoothManifold 0 a M) :
    ∃ F : Orientation S ≃ ZeroManifoldOrientation M,
      ∀ (o : Orientation S) (p : M),
        ((F o p).val = 1 ↔ IsPositive (o.val p)
          ((exteriorPower.zeroEquiv ℝ (TangentSpace S p)).symm 1)) := by
  exact zero_orientation_transport_along S (Equiv.refl _)

theorem normalWedge_zero_unit {V : Type u} {W : Type v}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (L : W →ₗ[ℝ] V) (v : V) :
    normalWedge L v ((exteriorPower.zeroEquiv ℝ W).symm 1) =
      exteriorPower.ιMulti ℝ 1 (fun _ => v) := by
  apply Subtype.ext
  simp [normalWedge, castExterior, exteriorPower.wedge,
    DirectSum.gMulLHom_apply_apply, SetLike.coe_gMul,
    exteriorPower.zeroEquiv_symm_apply, exteriorPower.ιMulti_apply_coe]


/-- This is the dimension-one specialization of the actual induced orientation
comparison. The only orientation hypothesis is the defining basis criterion of
canonical determinant duality; outwardness and the inclusion differential are
actual geometric data. -/
theorem induced_point_sign_iff {N : ℕ} {a : SmoothManifolds.ModelKind} {M : Set (E N)}
    (S : SmoothManifolds.AtlasData.SmoothManifold 1 a M)
    (I : (p : M) → TangentSpace S p ≃ₗ[ℝ] tangentSpace 2 1 M p.val)
    (o : Orientation S) (O : PositiveManifoldOrientation 2 1 M)
    (B : SmoothManifolds.AtlasData.SmoothManifold 0 .euclidean (intrinsicBoundary S))
    (q : Orientation B) (hi : IsInducedOrientation o q)
    (p : intrinsicBoundary S)
    (hq : p.val.val ∈ Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 1 M)
    (L : TangentSpace B p →ₗ[ℝ] TangentSpace S p.val)
    (hL : SmoothManifolds.DifferentialData.IsDifferential B S Subtype.val p L)
    (v : TangentSpace S p.val) (hv : IsOutward S p v)
    (hν : IsOutwardUnitConormal 2 0 M p.val.val (I p.val v).val)
    (hmatch : ∀ b : Module.Basis (Fin 1) ℝ (tangentSpace 2 1 M p.val.val),
      b.orientation = O.atPoint p.val.val p.val.property ↔
        IsPositive (o.val p.val)
          (exteriorPower.ιMulti ℝ 1 (fun j => (I p.val).symm (b j)))) :
    IsPositive (q.val p)
      ((exteriorPower.zeroEquiv ℝ (TangentSpace B p)).symm 1) ↔
      PositiveOutwardLine O ⟨p.val.val, hq⟩ (I p.val v).val := by
  rw [hi p L hL v hv, normalWedge_zero_unit]
  obtain ⟨b, hb⟩ := D04BoundaryOrientation.line_basis_exists O.manifold
    ⟨p.val.val, hq⟩ (I p.val v).val hν
  have hbv : b 0 = I p.val v := Subtype.ext hb
  have heval : (fun j => (I p.val).symm (b j)) = (fun _ : Fin 1 => v) := by
    funext j
    have hj : j = 0 := Subsingleton.elim j 0
    rw [hj, hbv, LinearEquiv.symm_apply_apply]
  rw [← heval, ← hmatch b]
  constructor
  · intro hbpos
    exact ⟨b, hb, hbpos⟩
  · rintro ⟨c, hc, hcpos⟩
    have hcb : c = b := by
      apply DFunLike.ext
      intro j
      have hj : j = 0 := Subsingleton.elim j 0
      rw [hj]
      exact Subtype.ext (hc.trans hb.symm)
    rwa [hcb] at hcpos


theorem boundary_point_comparison_proof
    (ht : Specs.SmoothManifolds.Integration.EmbeddedBoundary.orientation_transportType)
    (hg : Specs.SmoothManifolds.Integration.EmbeddedBoundary.boundary_geometryType) :
    Specs.SmoothManifolds.Integration.EmbeddedBoundary.boundary_point_comparisonType := by
  intro N a M hM S hS I hI C o
  classical
  obtain ⟨O, hO, _⟩ := ht (by omega) hM S hS I hI C o
  refine ⟨O, hO, ?_⟩
  intro B hB q hind
  have hgeo (p : intrinsicBoundary S) := hg hM S hS I hI C p
  choose hq hgeo using hgeo
  refine ⟨hq, ?_⟩
  intro ν hν
  obtain ⟨s, hs, hsuniq⟩ := D04BoundaryOrientation.boundary_point_sign O ν hν
  refine ⟨s, ⟨hs, ?_⟩, ?_⟩
  · intro p
    obtain ⟨L, hL, _⟩ := SmoothManifolds.differential_exists B S Subtype.val hB.1 p
    obtain ⟨J, hJ, _⟩ := hgeo p B hB L hL
    let x : Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 1 M :=
      ⟨p.val.val, hq p⟩
    let v : TangentSpace S p.val := (I p.val).symm ⟨ν x, (hν x).1⟩
    have hvimage : (I p.val v).val = ν x := by
      dsimp [v]
      rw [LinearEquiv.apply_symm_apply]
    have hconormal : IsOutwardUnitConormal 2 0 M p.val.val (I p.val v).val := by
      rw [hvimage]
      exact hν x
    have hv : IsOutward S p v := (hJ.2.1 v).mpr (hconormal.2.2.2)
    have hh := induced_point_sign_iff S I o O B q hind p (hq p) L hL v hv hconormal
      (hO p.val)
    rw [hvimage] at hh
    exact (hs x).1.trans hh.symm
  · intro s' hs'
    exact hsuniq s' hs'.1

end SmoothManifolds.EmbeddedBoundaryPointOrientation

namespace SmoothManifolds.EmbeddedBoundaryResults
universe u v

theorem zero_orientation_transport :
    Specs.SmoothManifolds.Integration.EmbeddedBoundary.zero_orientation_transportType :=
  EmbeddedBoundaryPointOrientation.zero_orientation_transport

theorem boundary_point_comparison :
    Specs.SmoothManifolds.Integration.EmbeddedBoundary.boundary_point_comparisonType :=
  EmbeddedBoundaryPointOrientation.boundary_point_comparison_proof
    orientation_transport
    boundary_geometry

end SmoothManifolds.EmbeddedBoundaryResults

namespace SmoothManifolds.EmbeddedBoundaryPointOrientation
open ModelData AtlasData TangentData OrientationData BoundaryData BoundaryOrientationData
  DifferentialData EmbeddedCalculusData EmbeddedAtlasData Set
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model (IsEmbeddedManifold ManifoldRegularity parameterSpace EmbeddedChart flatBoundary)
open Specs.D04.C14.ChartIndependentTangentSpaces.Model (tangentSpace)
open Specs.D04.C14.OrientationsAndChartSigns.Model
open Specs.D04.C14.OutwardFirstBoundaryOrientation.Model
theorem pointSign_eq_of_one_iff (s t : PointSign)
    (h : (s.val = 1 ↔ t.val = 1)) : s = t := by
  apply Subtype.ext
  by_cases hs : s.val = 1
  · exact hs.trans (h.mp hs).symm
  · have ht : t.val ≠ 1 := fun ht => hs (h.mpr ht)
    exact (s.property.resolve_left hs).trans (t.property.resolve_left ht).symm

private def interiorChart (r : ℕ∞ω) (a b : ℝ) :
    EmbeddedChart r 1 1 {x : E 1 | a ≤ x 0 ∧ x 0 ≤ b} where
  half := false
  half_pos := by simp
  source := {x | a < x 0 ∧ x 0 < b}
  source_open := ⟨{x | a < x 0 ∧ x 0 < b},
    (isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous).inter
      (isOpen_lt (EuclideanSpace.proj 0).continuous continuous_const), by simp [parameterSpace]⟩
  ambient := {x | a < x 0 ∧ x 0 < b}
  ambient_open := (isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous).inter
    (isOpen_lt (EuclideanSpace.proj 0).continuous continuous_const)
  toFun := id
  invFun := id
  map_source := by intro x hx; exact ⟨⟨hx.1.le, hx.2.le⟩, hx⟩
  map_target := by intro x hx; exact hx.2
  left_inv := by intros; rfl
  right_inv := by intros; rfl
  continuous_toFun := continuous_id.continuousOn
  continuous_invFun := continuous_id.continuousOn
  regular := by
    intro u hu
    refine ⟨univ, id, isOpen_univ, mem_univ _, fun _ _ => rfl,
      contDiff_id.contDiffOn, ?_⟩
    intro v hv
    simpa using (Function.injective_id : Function.Injective (id : E 1 → E 1))

theorem interval_embedded (r : ℕ∞ω) (hr : ManifoldRegularity r)
    (a b : ℝ) (hab : a < b) :
    IsEmbeddedManifold r 1 {x : E 1 | a ≤ x 0 ∧ x 0 ≤ b} := by
  refine ⟨hr, le_rfl, ?_⟩
  intro x hx
  by_cases hxa : x 0 = a
  · let c := D04BoundaryOrientation.endpointChart r a b hab false
    refine ⟨c, 0, ⟨?_, ?_⟩, ?_⟩
    · change 0 ≤ (0 : E 1) 0 ∧ (0 : E 1) 0 < b-a
      simp only [PiLp.zero_apply, le_refl, true_and]
      linarith
    · intro hc
      simp [flatBoundary]
    · ext i
      have hi : i = 0 := Subsingleton.elim i 0
      subst i
      simpa [c, D04BoundaryOrientation.endpointChart] using hxa.symm
  · by_cases hxb : x 0 = b
    · let c := D04BoundaryOrientation.endpointChart r a b hab true
      refine ⟨c, 0, ⟨?_, ?_⟩, ?_⟩
      · change 0 ≤ (0 : E 1) 0 ∧ (0 : E 1) 0 < b-a
        simp only [PiLp.zero_apply, le_refl, true_and]
        linarith
      · intro hc
        simp [flatBoundary]
      · ext i
        have hi : i = 0 := Subsingleton.elim i 0
        subst i
        simpa [c, D04BoundaryOrientation.endpointChart] using hxb.symm
    · exact ⟨interiorChart r a b, x,
        ⟨⟨lt_of_le_of_ne hx.1 (Ne.symm hxa), lt_of_le_of_ne hx.2 hxb⟩, by simp [interiorChart]⟩,
        rfl⟩


set_option maxHeartbeats 5000000 in
theorem interval_comparison_proof
    (hp : Specs.SmoothManifolds.Integration.EmbeddedBoundary.boundary_point_comparisonType)
    (hb : Specs.SmoothManifolds.Integration.EmbeddedBoundary.boundary_baseType) :
    Specs.SmoothManifolds.Integration.EmbeddedBoundary.interval_comparisonType := by
  intro a b hab S hS I hI C o
  classical
  have hM := interval_embedded ∞ (by norm_num [ManifoldRegularity]) a b hab
  obtain ⟨O, hO, hpoint⟩ := hp hM S hS I hI C o
  obtain ⟨ε, hε, hdir, hdata⟩ :=
    D04BoundaryOrientation.oriented_interval_endpoint_signs (r := 2) a b hab O
  refine ⟨O, hO, ε, hε, ?_, ?_⟩
  · intro p c
    exact (hO p c).symm.trans (hdir p.val p.property c)
  · intro B hB q hind
    have hbase := hb (n := 1) (N := 1) (a := .halfSpace)
      (M := {x : E 1 | a ≤ x 0 ∧ x 0 ≤ b}) hM S hS
    rcases hbase with ⟨β, hβ, _⟩
    have hzero := zero_orientation_transport_along
      (X := intrinsicBoundary S)
      (Y := Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 1
        {x : E 1 | a ≤ x 0 ∧ x 0 ≤ b})
      (a := .euclidean) B β.toEquiv
    rcases hzero with ⟨F, hF⟩
    obtain ⟨hq, hpoint⟩ := hpoint B hB q hind
    rcases hdata with ⟨ha, hb, ν, s₀, hrest⟩
    have hν := hrest.2.1
    obtain ⟨s, hs, _⟩ := hpoint ν hν
    have hss : s = s₀ := by
      funext x
      exact pointSign_eq_of_one_iff _ _ ((hs.1 x).1.trans (hrest.2.2.1 x).symm)
    have heq : F q = s := by
      funext x
      obtain ⟨p, rfl⟩ := β.surjective x
      apply pointSign_eq_of_one_iff
      have hβp : β p = ⟨p.val.val, hq p⟩ := Subtype.ext (hβ p)
      exact (hF q p).trans (by simpa only [hβp] using (hs.2 p).symm)
    refine ⟨β, hβ, F, hF, ν, s, hrest.1, hν, hs.1, heq, ha, hb, ?_, ?_, ?_⟩
    · simpa only [hss] using hrest.2.2.2.1
    · simpa only [hss] using hrest.2.2.2.2
    · intro hεone
      constructor
      · simpa only [hss, hεone] using hrest.2.2.2.1
      · simpa only [hss, hεone] using hrest.2.2.2.2


theorem interval_positive_proof
    (comparison : Specs.SmoothManifolds.Integration.EmbeddedBoundary.interval_comparisonType) :
    Specs.SmoothManifolds.Integration.EmbeddedBoundary.interval_positiveType := by
  intro a b hab S hS I hI C o hpositive
  obtain ⟨O, hO, ε, hε, hdir, hcmp⟩ := comparison a b hab S hS I hI C o
  let x : Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 1
      {x : E 1 | a ≤ x 0 ∧ x 0 ≤ b} :=
    ⟨D04BoundaryOrientation.linePoint b,
      D04BoundaryOrientation.endpoint_mem_boundary 2 a b hab true⟩
  have hn : IsOutwardUnitConormal 2 0 {x : E 1 | a ≤ x 0 ∧ x 0 ≤ b}
      x (standardBasis 1 0) := by
    simpa only [x, ↓reduceIte] using
      D04BoundaryOrientation.endpoint_conormal a b hab O.manifold true
  obtain ⟨B, hB⟩ := D04BoundaryOrientation.line_basis_exists O.manifold x (standardBasis 1 0) hn
  let p : {x : E 1 | a ≤ x 0 ∧ x 0 ≤ b} := ⟨x.val, x.property.1⟩
  have hc : (B 0).val 0 = 1 := by
    rw [hB]
    simp [standardBasis, EuclideanSpace.basisFun_apply]
  have hp := (hpositive p B).mpr (by rw [hc]; norm_num)
  have hepspos := (hdir p B).mp hp
  rw [hc, mul_one] at hepspos
  have heps : ε = 1 := hε.resolve_right (by intro h; linarith)
  subst ε
  exact ⟨O, hO, hcmp⟩
end SmoothManifolds.EmbeddedBoundaryPointOrientation

namespace SmoothManifolds.EmbeddedBoundaryResults
universe u v

theorem interval_comparison :
    Specs.SmoothManifolds.Integration.EmbeddedBoundary.interval_comparisonType :=
  EmbeddedBoundaryPointOrientation.interval_comparison_proof
    boundary_point_comparison
    boundary_base

theorem interval_positive :
    Specs.SmoothManifolds.Integration.EmbeddedBoundary.interval_positiveType :=
  EmbeddedBoundaryPointOrientation.interval_positive_proof
    interval_comparison

end SmoothManifolds.EmbeddedBoundaryResults
