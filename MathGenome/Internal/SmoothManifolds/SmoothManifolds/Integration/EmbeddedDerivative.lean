import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Integration.EmbeddedDerivative
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch07.ExteriorDerivative
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Integration.EmbeddedAtlas
import MathGenome.Internal.MultivariableAnalysis.D04.C15.IntrinsicExteriorDerivative
import MathGenome.Internal.MultivariableAnalysis.D04.C13.EuclideanPoincareLemma
import Mathlib.Topology.TietzeExtension

/-! The analytic comparison of M10.08. The independent statements are in Specs.
The atlas comparison supplies the canonical form identities. Local ambient
representatives give the regularity bridges for every C² embedded test chart. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SmoothManifolds.EmbeddedDerivativeResults
open ModelData AtlasData TangentData BundleOperationsData ExteriorData
  ExteriorDerivativeData EmbeddedCalculusData EmbeddedAtlasData
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.ChartIndependentTangentSpaces.Model
open Specs.D04.C13.NormalizedFormsAndWedge.Model
open Set Filter Topology
open scoped BigOperators ContDiff

/-- Reconstruct a D04 form from its increasing-index coefficient vector. -/
private def coefficientForm {n k : ℕ} (f : E n → Index n k → ℝ) : FormField n k :=
  fun z => ∑ J : Index n k, f z J • dx (standardBasis n) J

private theorem coefficient_coefficientForm {n k : ℕ} (f : E n → Index n k → ℝ)
    (z : E n) (J : Index n k) :
    coefficient (standardBasis n) (coefficientForm f z) J = f z J := by
  exact congrFun ((D04.covector_expansion_unique (standardBasis n)
    (coefficientForm f z) (f z)).mp rfl).symm J

/-- The reconstruction uses the literal D04 finite-regularity predicate,
rather than replacing it by a new regularity convention. -/
private theorem coefficientForm_isCr {n k r : ℕ} {W : Set (E n)} (hW : IsOpen W)
    (f : E n → Index n k → ℝ) (hf : ContDiffOn ℝ r f W) :
    IsCrForm (some r) W (coefficientForm f) := by
  refine ⟨hW, ?_⟩
  intro J
  change Specs.D04.C02.DerivativeInterfaces.Model.CrOn r W _
  apply (D04.crOn_iff_contDiffOn r W _ hW).mpr
  simpa only [coefficient_coefficientForm] using (contDiffOn_pi.mp hf J)

/-- A genuine local extension of the vector of coefficients reconstructs a
local C¹ extension of the D04 coordinate form, including on a flat face. The
norm change is explicit; no extension by zero is differentiated. -/
theorem chartPullback_extension_of_coefficients {n N k : ℕ} {M : Set (E N)}
    (c : EmbeddedChart 2 n N M)
    (ξ : Specs.D04.C15.IntrinsicExteriorDerivative.Model.IntrinsicForm (k := n) M k)
    (u : E n) (hu : u ∈ c.source)
    (U : Set (Euclidean n)) (hU : IsOpen U) (huU : piCoordinates n u ∈ U)
    (F : Euclidean n → Index n k → ℝ) (hF : ContDiffOn ℝ 1 F U)
    (he : ∀ z ∈ c.source, piCoordinates n z ∈ U → ∀ J : Index n k,
      coefficient (standardBasis n)
        (Specs.D04.C15.IntrinsicExteriorDerivative.Model.chartPullback c ξ z) J =
          F (piCoordinates n z) J) :
    ∃ (W : Set (E n)) (α : FormField n k), IsOpen W ∧ u ∈ W ∧
      IsCrForm (some 1) W α ∧
      EqOn α (Specs.D04.C15.IntrinsicExteriorDerivative.Model.chartPullback c ξ)
        (c.source ∩ W) := by
  let W := (piCoordinates n) ⁻¹' U
  let f : E n → Index n k → ℝ := fun z => F (piCoordinates n z)
  refine ⟨W, coefficientForm f, hU.preimage (piCoordinates n).continuous, huU,
    coefficientForm_isCr (hU.preimage (piCoordinates n).continuous) f ?_, ?_⟩
  · exact hF.comp (piCoordinates n).contDiff.contDiffOn (fun _ hz => hz)
  · intro z hz
    apply (D04.covector_expansion_unique (standardBasis n)
      (Specs.D04.C15.IntrinsicExteriorDerivative.Model.chartPullback c ξ z) (f z)).mpr
        (funext (fun J => (he z hz.1 hz.2 J).symm)) |>.symm

/-- The same extension computes the literal within exterior derivative.
This statement uses the original chart source and thus applies at the face. -/
theorem chartPullback_derivative_of_coefficients {n N k : ℕ} {M : Set (E N)}
    (c : EmbeddedChart 2 n N M)
    (ξ : Specs.D04.C15.IntrinsicExteriorDerivative.Model.IntrinsicForm (k := n) M k)
    (u : E n) (hu : u ∈ c.source)
    (U : Set (Euclidean n)) (hU : IsOpen U) (huU : piCoordinates n u ∈ U)
    (F : Euclidean n → Index n k → ℝ) (hF : ContDiffOn ℝ 1 F U)
    (he : ∀ z ∈ c.source, piCoordinates n z ∈ U → ∀ J : Index n k,
      coefficient (standardBasis n)
        (Specs.D04.C15.IntrinsicExteriorDerivative.Model.chartPullback c ξ z) J =
          F (piCoordinates n z) J) :
    Specs.D04.C15.IntrinsicExteriorDerivative.Model.withinExteriorDerivative
        c.source (Specs.D04.C15.IntrinsicExteriorDerivative.Model.chartPullback c ξ) u =
      Specs.D04.C13.ExteriorDerivative.Model.exteriorDerivative
        (coefficientForm (fun z => F (piCoordinates n z))) u := by
  apply D04.Intrinsic.withinExteriorDerivative_extension c hu
    (hU.preimage (piCoordinates n).continuous) huU
  · exact coefficientForm_isCr (hU.preimage (piCoordinates n).continuous) _
      (hF.comp (piCoordinates n).contDiff.contDiffOn (fun _ hz => hz))
  · intro z hz
    exact ((D04.covector_expansion_unique (standardBasis n)
      (Specs.D04.C15.IntrinsicExteriorDerivative.Model.chartPullback c ξ z)
      (fun J => F (piCoordinates n z) J)).mpr
        (funext (fun J => (he z hz.1 hz.2 J).symm))).symm

/-- C² local reparametrization preserves C¹ extendibility and computes the
within derivative when the pullback agrees on the relative chart source. -/
theorem c2_pullback_local_extension {n N m k : ℕ} {M : Set (E N)}
    (c : EmbeddedChart 2 n N M) (u : E n) (hu : u ∈ c.source)
    (W : Set (E n)) (V : Set (E m)) (H : E n → E m)
    (α : FormField m k) (β : FormField n k)
    (hW : IsOpen W) (huW : u ∈ W) (hH : ContDiffOn ℝ 2 H W)
    (hmap : MapsTo H W V) (hα : IsCrForm (some 1) V α)
    (he : EqOn (D04.pullback H α) β (c.source ∩ W)) :
    (∃ (U : Set (E n)) (γ : FormField n k), IsOpen U ∧ u ∈ U ∧
      IsCrForm (some 1) U γ ∧ EqOn γ β (c.source ∩ U)) ∧
    Specs.D04.C15.IntrinsicExteriorDerivative.Model.withinExteriorDerivative
      c.source β u =
      D04.pullback H (Specs.D04.C13.ExteriorDerivative.Model.exteriorDerivative α) u := by
  have hH' := (D04.crOn_iff_contDiffOn 2 W H hW).mpr hH
  have hpb := D04.pullback_C1 W V H α hW hmap hH' hα
  exact ⟨⟨W, D04.pullback H α, hW, huW, hpb, he⟩,
    (D04.Intrinsic.withinExteriorDerivative_extension c hu hW huW _ _ hpb he).trans
      (D04.exteriorDerivative_pullback W V H α hW hmap hH' hα u huW)⟩

/-- On a zero-dimensional intrinsic manifold every field has constant
coefficients on each individual chart, including scalar fields of degree zero. -/
theorem zero_dimension_regular {a : ModelKind} {M : Type*} [TopologicalSpace M]
    {S : SmoothManifold 0 a M} (C : CotangentBundle S) (r : ℕ∞) (k : ℕ)
    (ξ : Field S k) : IsRegularField C r k ξ := by
  intro e he p
  refine ⟨univ, isOpen_univ, mem_univ _,
    fun _ => fun J => coefficients C k e he ξ p J, contDiffOn_const, ?_⟩
  intro q _
  have hqp : q = p := Subtype.ext (e.injOn q.property p.property (Subsingleton.elim _ _))
  subst q
  rfl

/-- Every chart of the raw induced atlas is itself a genuine smooth embedded
parametrization after the explicit coordinate norm change. The ambient open
set comes from the subspace topology, not from a compatibility assumption. -/
theorem embeddedChart_of_raw {n N : ℕ} {a : ModelKind} {M : Set (E N)}
    (e : ModelChart n a M) (he : IsRawEmbeddedChart e) :
    ∃ c : EmbeddedChart ∞ n N M, MatchesEmbeddedChart e c ∧
      (∀ z (hz : z ∈ c.source),
        (⟨c.toFun z, (c.map_source hz).1⟩ : M) ∈ e.source) := by
  classical
  let b : Bool := a == .halfSpace && decide (0 < n)
  have hb (z : E n) : piCoordinates n z ∈ modelSet n a ↔ z ∈ parameterSpace n b := by
    cases a <;> cases n <;>
      simp [b, ModelData.modelSet, ModelData.halfSpaceSet, parameterSpace, halfSpace, piCoordinates]
  obtain ⟨O, hO, hOe⟩ := isOpen_induced_iff.mp e.open_source
  obtain ⟨V, hV, hVe⟩ := isOpen_induced_iff.mp e.open_target
  let s : Set (E n) := parameterSpace n b ∩ (piCoordinates n) ⁻¹' V
  have hs (z : E n) : z ∈ s ↔ ∃ hz : piCoordinates n z ∈ modelSet n a,
      (⟨piCoordinates n z, hz⟩ : ModelSpace n a) ∈ e.target := by
    constructor
    · intro hz
      refine ⟨(hb z).mpr hz.1, ?_⟩
      rw [← hVe]
      exact hz.2
    · rintro ⟨hz, ht⟩
      refine ⟨(hb z).mp hz, ?_⟩
      rw [← hVe] at ht
      exact ht
  let f : E n → E N := fun z =>
    if hz : piCoordinates n z ∈ modelSet n a then
      (e.symm ⟨piCoordinates n z, hz⟩).val else 0
  let g : E N → E n := fun x =>
    if hx : x ∈ M then (piCoordinates n).symm (e ⟨x, hx⟩).val else 0
  have hf (z : E n) (hz : z ∈ s) :
      f z = (e.symm ⟨piCoordinates n z, ((hs z).mp hz).choose⟩).val := by
    dsimp [f]
    rw [dif_pos ((hs z).mp hz).choose]
  have hg (p : M) : g p.val = (piCoordinates n).symm (e p).val := by
    dsimp [g]
    rw [dif_pos p.property]
  have hfsource (z : E n) (hz : z ∈ s) :
      e.symm ⟨piCoordinates n z, ((hs z).mp hz).choose⟩ ∈ e.source :=
    e.map_target ((hs z).mp hz).choose_spec
  have hfs : MapsTo f s (M ∩ O) := by
    intro z hz
    rw [hf z hz]
    refine ⟨(e.symm _).property, ?_⟩
    have hp := hfsource z hz
    rw [← hOe] at hp
    exact hp
  have hgt (x : E N) (hx : x ∈ M ∩ O) : g x ∈ s := by
    rw [show g x = (piCoordinates n).symm (e ⟨x, hx.1⟩).val from hg ⟨x, hx.1⟩]
    apply (hs _).mpr
    refine ⟨by simpa only [ContinuousLinearEquiv.apply_symm_apply] using (e ⟨x, hx.1⟩).property, ?_⟩
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using
      e.map_source (show (⟨x, hx.1⟩ : M) ∈ e.source from by rw [← hOe]; exact hx.2)
  have hleft (z : E n) (hz : z ∈ s) : g (f z) = z := by
    rw [hf z hz, hg (e.symm _), e.right_inv ((hs z).mp hz).choose_spec,
      ContinuousLinearEquiv.symm_apply_apply]
  have hright (x : E N) (hx : x ∈ M ∩ O) : f (g x) = x := by
    have hp : (⟨x, hx.1⟩ : M) ∈ e.source := by rw [← hOe]; exact hx.2
    rw [hf _ (hgt x hx)]
    change (e.symm _).val = (⟨x, hx.1⟩ : M).val
    congr 1
    apply (e.injOn (e.map_target ((hs _).mp (hgt x hx)).choose_spec) hp)
    rw [e.right_inv ((hs _).mp (hgt x hx)).choose_spec]
    apply Subtype.ext
    change piCoordinates n (g x) = (e (⟨x, hx.1⟩ : M)).val
    rw [hg ⟨x, hx.1⟩, ContinuousLinearEquiv.apply_symm_apply]
  have hfcont : ContinuousOn f s := by
    apply continuousOn_iff_continuous_restrict.mpr
    have hcoord : Continuous (fun z : s =>
        (⟨piCoordinates n z.val, ((hs z.val).mp z.property).choose⟩ : ModelSpace n a)) :=
      ((piCoordinates n).continuous.comp continuous_subtype_val).subtype_mk _
    have h := continuous_subtype_val.comp (e.symm.continuousOn.comp_continuous hcoord
      (fun z => ((hs z.val).mp z.property).choose_spec))
    exact h.congr (fun z => (hf z.val z.property).symm)
  have hgcont : ContinuousOn g (M ∩ O) := by
    apply continuousOn_iff_continuous_restrict.mpr
    have hp : Continuous (fun x : ↥(M ∩ O) => (⟨x.val, x.property.1⟩ : M)) :=
      continuous_subtype_val.subtype_mk _
    have h := (piCoordinates n).symm.continuous.comp (continuous_subtype_val.comp
      (e.continuousOn.comp_continuous hp (fun x => by rw [← hOe]; exact x.property.2)))
    exact h.congr (fun x => (hg ⟨x.val, x.property.1⟩).symm)
  have hreg : FullRankLocalExtension ∞ s f := by
    intro u hu
    let p : M := e.symm ⟨piCoordinates n u, ((hs u).mp hu).choose⟩
    have hp : p ∈ e.source := hfsource u hu
    have heu : (e p).val = piCoordinates n u := congrArg Subtype.val (e.right_inv ((hs u).mp hu).choose_spec)
    obtain ⟨U, H, hU, hpU, hH, heH, hinj⟩ := he p hp
    let G := EmbeddedAtlasResults.l2ParameterExtension H
    let U₂ := (piCoordinates n) ⁻¹' U
    have hU₂ : IsOpen U₂ := hU.preimage (piCoordinates n).continuous
    have huU : u ∈ U₂ := by change piCoordinates n u ∈ U; rwa [← heu]
    have hG : ContDiffOn ℝ ∞ G U₂ := EmbeddedAtlasResults.l2ParameterExtension_contDiffOn hH
    have hdH := (hH.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp)
    have hdH' : HasFDerivAt H (fderiv ℝ H (e p).val) (piCoordinates n u) := by
      simpa only [heu] using hdH.hasFDerivAt
    have hdG : HasFDerivAt G ((piCoordinates N).symm.toContinuousLinearMap.comp
        ((fderiv ℝ H (e p).val).comp (piCoordinates n).toContinuousLinearMap)) u :=
      (piCoordinates N).symm.hasFDerivAt.comp u
        (hdH'.comp u (piCoordinates n).hasFDerivAt)
    have hinjG : Function.Injective (fderiv ℝ G u) := by
      rw [hdG.fderiv]
      exact (piCoordinates N).symm.injective.comp (hinj.comp (piCoordinates n).injective)
    have hnear : ∀ᶠ z in 𝓝 u, Function.Injective (fderiv ℝ G z) :=
      ((hG.continuousOn_fderiv_of_isOpen hU₂ (by simp)).continuousAt
        (hU₂.mem_nhds huU)).preimage_mem_nhds
          (ContinuousLinearMap.isOpen_injective.mem_nhds hinjG)
    let t : E n → ModelSpace n a := fun z =>
      if hz : piCoordinates n z ∈ modelSet n a then ⟨piCoordinates n z, hz⟩ else e p
    have ht (z : E n) (hz : z ∈ s) :
        t z = ⟨piCoordinates n z, ((hs z).mp hz).choose⟩ := by
      dsimp [t]
      rw [dif_pos ((hs z).mp hz).choose]
    have htcont : ContinuousWithinAt t s u := by
      rw [continuousWithinAt_iff_continuousAt_domRestrict _ hu]
      have hh : Continuous (fun z : s =>
          (⟨piCoordinates n z.val, ((hs z.val).mp z.property).choose⟩ : ModelSpace n a)) :=
        ((piCoordinates n).continuous.comp continuous_subtype_val).subtype_mk _
      exact (hh.congr (fun z => (ht z.val z.property).symm)).continuousAt
    have htu : e.symm (t u) = p := congrArg e.symm (ht u hu)
    have hevent : ∀ᶠ z in 𝓝[s] u, G z = f z := by
      have hcont : Tendsto (fun z => e.symm (t z)) (𝓝[s] u) (𝓝 p) := by
        rw [← htu]
        apply ContinuousAt.comp_continuousWithinAt _ htcont
        rw [ht u hu]
        exact e.symm.continuousAt ((hs u).mp hu).choose_spec
      have hh := hcont.eventually heH
      filter_upwards [self_mem_nhdsWithin, hh] with z hz hHz
      rw [ht z hz] at hHz
      have hc : (e (e.symm ⟨piCoordinates n z, ((hs z).mp hz).choose⟩)).val =
          piCoordinates n z :=
        congrArg Subtype.val (e.right_inv ((hs z).mp hz).choose_spec)
      change (piCoordinates N).symm (H (piCoordinates n z)) = _
      rw [← hc, hHz]
      exact (hf z hz).symm
    obtain ⟨A, hAsub, hA, huA⟩ := mem_nhds_iff.mp
      (eventually_nhdsWithin_iff.mp hevent)
    obtain ⟨B, hBsub, hB, huB⟩ := mem_nhds_iff.mp hnear
    refine ⟨U₂ ∩ A ∩ B, G, (hU₂.inter hA).inter hB, ⟨⟨huU, huA⟩, huB⟩,
      ?_, hG.mono (fun _ hz => hz.1.1), ?_⟩
    · intro z hz
      exact hAsub hz.2.1.2 hz.1
    · intro z hz
      exact hBsub hz.2
  let c : EmbeddedChart ∞ n N M := {
    half := b
    half_pos := by simp only [b, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]; tauto
    source := s
    source_open := ⟨(piCoordinates n) ⁻¹' V, hV.preimage (piCoordinates n).continuous, rfl⟩
    ambient := O
    ambient_open := hO
    toFun := f
    invFun := g
    map_source := hfs
    map_target := hgt
    left_inv := hleft
    right_inv := hright
    continuous_toFun := hfcont
    continuous_invFun := hgcont
    regular := hreg }
  refine ⟨c, ?_, ?_⟩
  · intro p hp
    refine ⟨?_, ?_⟩
    · change p.val ∈ O
      rw [← hOe] at hp
      exact hp
    · exact ((piCoordinates n).apply_symm_apply (e p).val).symm.trans
        (congrArg (piCoordinates n) (hg p).symm)
  · intro z hz
    change (⟨f z, (hfs hz).1⟩ : M) ∈ e.source
    rw [← hOe]
    exact (hfs hz).2

/-- In every matching smooth chart, intrinsic C¹ coefficient extensions give
literal D04 C¹ extensions. The cover hypothesis supplies raw source membership.
The global bridge uses local ambient representatives for arbitrary C² charts. -/
theorem matchingChart_c1_extension {n N : ℕ} {a : ModelKind} {M : Set (E N)}
    (S : SmoothManifold n a M) (hS : IsInducedSmoothStructure S)
    (I : (p : M) → TangentSpace S p ≃ₗ[ℝ] tangentSpace 2 n M p.val)
    (hI : IsInclusionIdentification S I) (C : CotangentBundle S)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
    (c : EmbeddedChart ∞ n N M) (hm : MatchesEmbeddedChart e c)
    (hcover : ∀ z (hz : z ∈ c.source),
      (⟨c.toFun z, (c.map_source hz).1⟩ : M) ∈ e.source)
    (k : ℕ) (ξ : Field S k) (hξ : IsRegularField C 1 k ξ)
    (u : E n) (hu : u ∈ c.source) :
    let c₂ := lowerChart c (by simp : (2 : ℕ∞ω) ≤ ∞)
    ∃ (W : Set (E n)) (α : FormField n k), IsOpen W ∧ u ∈ W ∧
      IsCrForm (some 1) W α ∧
      EqOn α (Specs.D04.C15.IntrinsicExteriorDerivative.Model.chartPullback c₂
        (transportField S I k ξ)) (c₂.source ∩ W) := by
  let p : M := ⟨c.toFun u, (c.map_source hu).1⟩
  have hp : p ∈ e.source := hcover u hu
  have hcoord (z : E n) (hz : z ∈ c.source) :
      (e (⟨c.toFun z, (c.map_source hz).1⟩ : M)).val = piCoordinates n z := by
    rw [(hm _ (hcover z hz)).2, c.left_inv z hz]
  obtain ⟨U, hU, hpU, F, hF, hF_eq⟩ := hξ e he ⟨p, hp⟩
  have huU : piCoordinates n u ∈ U := by
    simpa only [p, hcoord u hu] using hpU
  apply chartPullback_extension_of_coefficients
    (lowerChart c (by simp)) (transportField S I k ξ) u hu U hU huU F hF
  intro z hz hzU J
  have hcoeff := (EmbeddedAtlasResults.matching_chart_pullback S hS I hI C e he c hm z hz
    (hcover z hz)).2 k ξ |>.2 J
  rw [hcoeff]
  have hf := congrFun (hF_eq ⟨_, hcover z hz⟩
    (by simpa only [hcoord z hz] using hzU)) J
  simpa only [hcoord z hz] using hf.symm

/-- D04's all-C²-chart regularity supplies intrinsic coefficient extensions
on every matching smooth chart. -/
theorem matchingChart_regular_of_intrinsicC1 {n N : ℕ} {a : ModelKind}
    {M : Set (E N)} (S : SmoothManifold n a M) (hS : IsInducedSmoothStructure S)
    (I : (p : M) → TangentSpace S p ≃ₗ[ℝ] tangentSpace 2 n M p.val)
    (hI : IsInclusionIdentification S I) (C : CotangentBundle S)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
    (c : EmbeddedChart ∞ n N M) (hm : MatchesEmbeddedChart e c)
    (k : ℕ) (ξ : Field S k)
    (hξ : Specs.D04.C15.IntrinsicExteriorDerivative.Model.IntrinsicC1
      (transportField S I k ξ)) :
    LocallyContDiffAlong 1 (fun p : e.source => (e p.val).val)
      (fun p => fun J : Index n k => coefficients C k e he ξ p J) := by
  intro p
  let z := c.invFun p.val.val
  have hz : z ∈ c.source := c.map_target ⟨p.val.property, (hm p.val p.property).1⟩
  have hpz : (⟨c.toFun z, (c.map_source hz).1⟩ : M) = p.val :=
    Subtype.ext (c.right_inv p.val.val ⟨p.val.property, (hm p.val p.property).1⟩)
  let c₂ := lowerChart c (by simp : (2 : ℕ∞ω) ≤ ∞)
  obtain ⟨W, α, hW, hzW, hα, hαeq⟩ := hξ c₂ z hz
  let U := (piCoordinates n).symm ⁻¹' W
  let F : Euclidean n → Index n k → ℝ := fun y J =>
    coefficient (standardBasis n) (α ((piCoordinates n).symm y)) J
  have hU : IsOpen U := hW.preimage (piCoordinates n).symm.continuous
  refine ⟨U, hU, ?_, F, ?_, ?_⟩
  · change (piCoordinates n).symm (e p.val).val ∈ W
    rw [(hm p.val p.property).2, ContinuousLinearEquiv.symm_apply_apply]
    exact hzW
  · apply contDiffOn_pi.mpr
    intro J
    have hc := (D04.crOn_iff_contDiffOn 1 W
      (fun y => coefficient (standardBasis n) (α y) J) hW).mp (hα.2 J)
    exact hc.comp (piCoordinates n).symm.contDiff.contDiffOn (fun _ hy => hy)
  · intro q hqU
    let v := c.invFun q.val.val
    have hv : v ∈ c.source := c.map_target ⟨q.val.property, (hm q.val q.property).1⟩
    have hqv : (⟨c.toFun v, (c.map_source hv).1⟩ : M) = q.val :=
      Subtype.ext (c.right_inv q.val.val ⟨q.val.property, (hm q.val q.property).1⟩)
    have hvW : v ∈ W := by
      change (piCoordinates n).symm (e q.val).val ∈ W at hqU
      rw [(hm q.val q.property).2, ContinuousLinearEquiv.symm_apply_apply] at hqU
      exact hqU
    funext J
    change coefficient (standardBasis n) (α ((piCoordinates n).symm (e q.val).val)) J = _
    rw [(hm q.val q.property).2, ContinuousLinearEquiv.symm_apply_apply]
    rw [hαeq ⟨hv, hvW⟩]
    have hc := (EmbeddedAtlasResults.matching_chart_pullback S hS I hI C e he c hm v hv
      (by simpa only [hqv] using q.property)).2 k ξ |>.2 J
    simpa only [hqv] using hc


/-- One extendible coordinate form supplies a local ambient representative.
Only one chart at the point is required; C¹ regularity in other C² charts
is consequently derived, rather than used as a premise. -/
theorem local_ambient_of_chart_extension {n N k r : ℕ} {M : Set (E N)}
    (hM : IsEmbeddedManifold 2 n M) (hr : r ≤ 1)
    (ξ : Specs.D04.C15.IntrinsicExteriorDerivative.Model.IntrinsicForm (k := n) M k)
    (c : EmbeddedChart 2 n N M) (u : E n) (hu : u ∈ c.source)
    (W : Set (E n)) (α : FormField n k) (hW : IsOpen W) (huW : u ∈ W)
    (hα : IsCrForm (some r) W α)
    (heα : EqOn α (Specs.D04.C15.IntrinsicExteriorDerivative.Model.chartPullback c ξ)
      (c.source ∩ W)) :
    ∃ (O : Set (E N)) (Ω : FormField N k), IsOpen O ∧ c.toFun u ∈ O ∧
      IsCrForm (some r) O Ω ∧ ∀ y : M, y.val ∈ O →
        Specs.D04.C15.IntrinsicExteriorDerivative.Model.ambientRestriction M Ω y = ξ y := by
  obtain ⟨V, J, hV, hxV, hJ, heJ⟩ := D04.chart_inverse_extension c hM.1 hM.2.1 u hu
  have hJu : J (c.toFun u) = u := by rw [heJ ⟨c.map_source hu, hxV⟩, c.left_inv _ hu]
  let O := (V ∩ J ⁻¹' W) ∩ c.ambient
  have hO : IsOpen O := (hJ.continuousOn.isOpen_inter_preimage hV hW).inter c.ambient_open
  have hxO : c.toFun u ∈ O :=
    ⟨⟨hxV, by change J (c.toFun u) ∈ W; rwa [hJu]⟩, (c.map_source hu).2⟩
  have hJO : Specs.D04.C02.DerivativeInterfaces.Model.CrOn (r+1) O J :=
    (D04.crOn_iff_contDiffOn (r+1) O J hO).mpr
      ((hJ.of_le (by exact_mod_cast (show r+1 ≤ 2 by omega))).mono
        (inter_subset_left.trans inter_subset_left))
  refine ⟨O, D04.pullback J α, hO, hxO,
    D04.pullback_isCrForm r O W J α hO (fun y hy => hy.1.2) hJO hα, ?_⟩
  intro y hy
  have hyc : y.val ∈ M ∩ c.ambient := ⟨y.property, hy.2⟩
  let v := c.invFun y
  have hv : v ∈ c.source := c.map_target hyc
  have hcv : c.toFun v = y.val := c.right_inv _ hyc
  have hvV : c.toFun v ∈ V := hcv ▸ hy.1.1
  have hJv : J (c.toFun v) = v := by rw [heJ ⟨c.map_source hv, hvV⟩, c.left_inv _ hv]
  have hvW : v ∈ W := by
    have hh : J y.val = v := heJ ⟨hyc, hy.1.1⟩
    exact hh ▸ hy.1.2
  have hd := D04.Intrinsic.chart_inverse_differential hM c hv V J hV hvV hJ heJ
  have he : Specs.D04.C15.IntrinsicExteriorDerivative.Model.chartPullback c
      (Specs.D04.C15.IntrinsicExteriorDerivative.Model.ambientRestriction M (D04.pullback J α)) v =
      Specs.D04.C15.IntrinsicExteriorDerivative.Model.chartPullback c ξ v :=
    (D04.Intrinsic.chartPullback_inverse c hv J α hJv hd).trans (heα ⟨hv, hvW⟩)
  simp only [Specs.D04.C15.IntrinsicExteriorDerivative.Model.chartPullback,
    dif_pos hv] at he
  have hh := AlternatingMap.compLinearMap_injective _
    (D04.Intrinsic.chartTangentMap_surjective hM c hv) he
  have hxy : (⟨c.toFun v, (c.map_source hv).1⟩ : M) = y := Subtype.ext hcv
  rw [hxy] at hh
  exact hh

/-- Local ambient C¹ representatives imply D04's literal all-C²-chart test. -/
theorem intrinsicC1_of_local_ambient {n N k : ℕ} {M : Set (E N)}
    (ξ : Specs.D04.C15.IntrinsicExteriorDerivative.Model.IntrinsicForm (k := n) M k)
    (hξ : ∀ x : M, ∃ (O : Set (E N)) (Ω : FormField N k), IsOpen O ∧ x.val ∈ O ∧
      IsCrForm (some 1) O Ω ∧ ∀ y : M, y.val ∈ O →
        Specs.D04.C15.IntrinsicExteriorDerivative.Model.ambientRestriction M Ω y = ξ y) :
    Specs.D04.C15.IntrinsicExteriorDerivative.Model.IntrinsicC1 ξ := by
  intro c u hu
  obtain ⟨O, Ω, hO, hxO, hΩ, heΩ⟩ := hξ ⟨c.toFun u, (c.map_source hu).1⟩
  obtain ⟨W, g, hW, huW, hmap, hg, he⟩ :=
    D04.Intrinsic.chart_ambient_local c hu O hO hxO
  have hev := D04.Intrinsic.chartPullback_eventuallyEq c hu
    (Specs.D04.C15.IntrinsicExteriorDerivative.Model.ambientRestriction M Ω) ξ O hO hxO heΩ
  obtain ⟨A, hAsub, hA, huA⟩ := mem_nhds_iff.mp (eventually_nhdsWithin_iff.mp hev)
  refine ⟨W ∩ A, D04.pullback g Ω, hW.inter hA, ⟨huW, huA⟩,
    D04.Intrinsic.isCrForm_mono 1 (D04.pullback_C1 W O g Ω hW hmap hg hΩ)
      (hW.inter hA) inter_subset_left, ?_⟩
  intro v hv
  exact (he k Ω ⟨hv.1, hv.2.1⟩).trans (hAsub hv.2.2 hv.1)


/-- Intrinsic coefficient regularity is equivalent to the literal all-C²-chart test. -/
theorem regularity_transport :
    Specs.SmoothManifolds.Integration.EmbeddedDerivative.regularity_transportType := by
  intro n N a M hM S hS I hI C k ξ
  have hM₂ := (EmbeddedAtlasResults.smooth_c2_tangents hM).1
  constructor
  · intro hξ
    apply intrinsicC1_of_local_ambient
    intro p
    obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
    have hraw : IsRawEmbeddedChart e := by rw [hS] at he; exact he
    obtain ⟨c, hm, hcover⟩ := embeddedChart_of_raw e hraw
    let u := c.invFun p.val
    have hpc : p.val ∈ M ∩ c.ambient := ⟨p.property, (hm p hp).1⟩
    have hu : u ∈ c.source := c.map_target hpc
    have hcu : c.toFun u = p.val := c.right_inv p.val hpc
    obtain ⟨W, α, hW, huW, hα, heα⟩ :=
      matchingChart_c1_extension S hS I hI C e he c hm hcover k ξ hξ u hu
    obtain ⟨O, Ω, hO, hcuO, hΩ, heΩ⟩ := local_ambient_of_chart_extension hM₂
      (by rfl : 1 ≤ 1) (transportField S I k ξ) (lowerChart c (by simp)) u hu
      W α hW huW hα heα
    refine ⟨O, Ω, hO, ?_, hΩ, heΩ⟩
    change c.toFun u ∈ O at hcuO
    rwa [hcu] at hcuO
  · intro hξ e he
    have hraw : IsRawEmbeddedChart e := by rw [hS] at he; exact he
    obtain ⟨c, hm, _⟩ := embeddedChart_of_raw e hraw
    exact matchingChart_regular_of_intrinsicC1 S hS I hI C e he c hm k ξ hξ

end SmoothManifolds.EmbeddedDerivativeResults

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
open scoped BigOperators
namespace D04
open Poincare

theorem exteriorDerivative_reconstruction {n k : ℕ} (f : E n → MultiIndex n k → ℝ)
    (x : E n) (hf : DifferentiableAt ℝ f x) :
    exteriorDerivative (fun y => ∑ I : MultiIndex n k, f y I • dx (standardBasis n) I) x =
      ∑ I : MultiIndex n k, prependCovector
        (linearCovector (fderiv ℝ (fun y => f y I) x).toLinearMap) (dx (standardBasis n) I) := by
  rw [exteriorDerivative_sum_smul_const (fun I y => f y I)
    (fun I => dx (standardBasis n) I) x (fun I => differentiableAt_pi.mp hf I)]
  apply Finset.sum_congr rfl
  intro I _
  have hl : linearCovector (fderiv ℝ (fun y => f y I) x).toLinearMap =
      ∑ j : Fin n, scalarPartialDerivative (fun y => f y I) x j • coordinateOneForm n j := by
    ext v
    simp only [linearCovector_apply, sum_apply, smul_apply, coordinateOneForm_apply,
      scalarPartialDerivative_eq_fderiv _ _ (differentiableAt_pi.mp hf I), smul_eq_mul]
    conv_lhs => rw [← (standardBasis n).sum_repr (v 0)]
    simp only [map_sum, map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_comm]
    rfl
  rw [hl]
  simp only [prependCovector, wedge_sum_left, wedge_smul_left,
    castCovector_sum, castCovector_smul]
end D04

open scoped BigOperators
open SmoothManifolds.ModelData SmoothManifolds.ExteriorData
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C13.NormalizedFormsAndWedge.Model
namespace SmoothManifolds.EmbeddedCoefficientCalculus

theorem determinant_normalization (n k : ℕ) (α : Fin k → Module.Dual ℝ (SmoothManifolds.ModelData.Euclidean n))
    (v : Fin k → SmoothManifolds.ModelData.Euclidean n) :
    evaluate (SmoothManifolds.ModelData.Euclidean n) k (exteriorPower.ιMulti ℝ k α) v =
      (Matrix.of (fun i j => α i (v j))).det := by
  change exteriorPower.pairingDual ℝ (SmoothManifolds.ModelData.Euclidean n) k (exteriorPower.ιMulti ℝ k α)
    (exteriorPower.ιMulti ℝ k v) = _
  rw [exteriorPower.pairingDual_ιMulti_ιMulti, ← Matrix.det_transpose]
  rfl

theorem dx_evaluate {n k : ℕ} (J : Index n k) (v : Fin k → E n) :
    dx (standardBasis n) J v =
      evaluate (SmoothManifolds.ModelData.Euclidean n) k (exteriorPower.ιMulti ℝ k
        (fun i => (Pi.basisFun ℝ (Fin n)).dualBasis (Set.powersetCard.ofFinEmbEquiv.symm J i)))
          (fun i => EmbeddedCalculusData.piCoordinates n (v i)) := by
  rw [D04.dx_apply, determinant_normalization]
  congr 1
  ext i j
  simp [standardBasis, Specs.D04.C01.EuclideanInterfaces.Model.standardBasis,
    D04.indexTuple, Specs.D04.C13.NormalizedFormsAndWedge.Model.indexTuple, EmbeddedCalculusData.piCoordinates]

theorem evaluate_cons {n k : ℕ} (α : Module.Dual ℝ (SmoothManifolds.ModelData.Euclidean n))
    (β : Fin k → Module.Dual ℝ (SmoothManifolds.ModelData.Euclidean n)) (v : Fin (k+1) → SmoothManifolds.ModelData.Euclidean n) :
    evaluate (SmoothManifolds.ModelData.Euclidean n) (k+1) (exteriorPower.ιMulti ℝ (k+1) (Fin.cons α β)) v =
      ∑ i : Fin (k+1), (-1 : ℝ)^i.val * α (v i) *
        evaluate (SmoothManifolds.ModelData.Euclidean n) k (exteriorPower.ιMulti ℝ k β) (i.removeNth v) := by
  rw [determinant_normalization]
  rw [Matrix.det_succ_row_zero]
  apply Finset.sum_congr rfl
  intro i _
  rw [determinant_normalization]
  congr 2


theorem derivative_reconstruction_evaluate {n k : ℕ}
    (F : SmoothManifolds.ModelData.Euclidean n → Index n k → ℝ) (u : E n)
    (hF : DifferentiableAt ℝ F (EmbeddedCalculusData.piCoordinates n u)) (v : Fin (k+1) → E n) :
    D04.exteriorDerivative (fun z => ∑ I : Index n k,
      F (EmbeddedCalculusData.piCoordinates n z) I • dx (standardBasis n) I) u v =
      evaluate (SmoothManifolds.ModelData.Euclidean n) (k+1) (∑ I : Index n k,
        exteriorPower.ιMulti ℝ (k+1)
          (Fin.cons (fderiv ℝ (fun z => F z I) (EmbeddedCalculusData.piCoordinates n u)).toLinearMap
            (fun j => (Pi.basisFun ℝ (Fin n)).dualBasis
              (Set.powersetCard.ofFinEmbEquiv.symm I j)))) (fun i => EmbeddedCalculusData.piCoordinates n (v i)) := by
  have hf : DifferentiableAt ℝ (fun z => F (EmbeddedCalculusData.piCoordinates n z)) u := hF.comp u (EmbeddedCalculusData.piCoordinates n).differentiableAt
  have hd (I : Index n k) :
      fderiv ℝ (fun z => F (EmbeddedCalculusData.piCoordinates n z) I) u =
        (fderiv ℝ (fun z => F z I) (EmbeddedCalculusData.piCoordinates n u)).comp (EmbeddedCalculusData.piCoordinates n).toContinuousLinearMap := by
    exact ((differentiableAt_pi.mp hF I).hasFDerivAt.comp u (EmbeddedCalculusData.piCoordinates n).hasFDerivAt).fderiv
  erw [D04.exteriorDerivative_reconstruction _ _ hf]
  simp only [sum_apply, D04.Poincare.prependCovector_apply, map_sum, evaluate_cons,
    ContinuousLinearMap.coe_coe, hd, ContinuousLinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro I _
  apply Finset.sum_congr rfl
  intro i _
  erw [dx_evaluate]
  rfl

end SmoothManifolds.EmbeddedCoefficientCalculus

namespace SmoothManifolds.EmbeddedDerivativeResults
open ModelData AtlasData TangentData BundleOperationsData ExteriorData
  ExteriorDerivativeData EmbeddedCalculusData EmbeddedAtlasData
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.ChartIndependentTangentSpaces.Model
open Specs.D04.C13.NormalizedFormsAndWedge.Model
open Set Filter Topology
open scoped BigOperators ContDiff

theorem derivative_reconstruction_extDeriv {n k : ℕ}
    (F : SmoothManifolds.ModelData.Euclidean n → Index n k → ℝ) (u : E n)
    (hF : DifferentiableAt ℝ F (piCoordinates n u)) (v : Fin (k+1) → E n) :
    D04.exteriorDerivative (coefficientForm (fun z => F (piCoordinates n z))) u v =
      extDeriv (fun z => ExteriorDerivativeResults.Euclidean.coefficientAlternatingEquiv n k (F z))
        (piCoordinates n u) (fun i => piCoordinates n (v i)) := by
  have hh (y : SmoothManifolds.ModelData.Euclidean n) :
      ExteriorDerivativeResults.Euclidean.coefficientAlternatingEquiv n k (F y) =
        ∑ I : Index n k, F y I • ExteriorDerivativeResults.Euclidean.evaluateContinuous n k
          (exteriorPower.ιMulti ℝ k (fun j => (Pi.basisFun ℝ (Fin n)).dualBasis
            (Set.powersetCard.ofFinEmbEquiv.symm I j))) := by
    change ExteriorDerivativeResults.Euclidean.coefficientAlternating n k (F y) = _
    rw [ExteriorDerivativeResults.Euclidean.coefficientAlternating_apply]
    apply Finset.sum_congr rfl
    intro I _
    congr 2
    exact exteriorPower.basis_apply ℝ k (Pi.basisFun ℝ (Fin n)).dualBasis I
  rw [show (fun z => ExteriorDerivativeResults.Euclidean.coefficientAlternatingEquiv n k (F z)) = _ from funext hh]
  rw [ExteriorDerivativeResults.Euclidean.extDeriv_sum_coefficients]
  · exact SmoothManifolds.EmbeddedCoefficientCalculus.derivative_reconstruction_evaluate F u hF v
  · intro I
    exact differentiableAt_pi.mp hF I

/-- The two coordinate derivatives evaluate equally on every tangent tuple. -/
theorem matchingChart_derivative_evaluate {n N : ℕ} {a : ModelKind} {M : Set (E N)}
    (S : SmoothManifold n a M) (hS : IsInducedSmoothStructure S)
    (I : (p : M) → TangentSpace S p ≃ₗ[ℝ] tangentSpace 2 n M p.val)
    (hI : IsInclusionIdentification S I) (C : CotangentBundle S)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
    (c : EmbeddedChart ∞ n N M) (hm : MatchesEmbeddedChart e c)
    (hcover : ∀ z (hz : z ∈ c.source),
      (⟨c.toFun z, (c.map_source hz).1⟩ : M) ∈ e.source)
    (k : ℕ) (ξ : Field S k) (hξ : IsRegularField C 1 k ξ)
    (u : E n) (hu : u ∈ c.source)
    (hp : (⟨c.toFun u, (c.map_source hu).1⟩ : M) ∈ e.source)
    (v : Fin (k+1) → E n) :
    let p : M := ⟨c.toFun u, (c.map_source hu).1⟩
    let c₂ := lowerChart c (by simp : (2 : ℕ∞ω) ≤ ∞)
    Specs.D04.C15.IntrinsicExteriorDerivative.Model.withinExteriorDerivative c₂.source
      (Specs.D04.C15.IntrinsicExteriorDerivative.Model.chartPullback c₂ (transportField S I k ξ)) u v =
    evaluate (TangentSpace S p) (k+1) (coordinateDerivative C k e he ξ p hp)
      (fun j => (C.tangent.fiberCoordinates.equiv e he p hp).symm (piCoordinates n (v j))) := by
  let p : M := ⟨c.toFun u, (c.map_source hu).1⟩
  have hcoord (z : E n) (hz : z ∈ c.source) :
      (e (⟨c.toFun z, (c.map_source hz).1⟩ : M)).val = piCoordinates n z := by
    rw [(hm _ (hcover z hz)).2, c.left_inv z hz]
  obtain ⟨U, hU, hpU, F, hF, hF_eq⟩ := hξ e he ⟨p, hp⟩
  have huU : piCoordinates n u ∈ U := by simpa only [p, hcoord u hu] using hpU
  have heF : ∀ z ∈ c.source, piCoordinates n z ∈ U → ∀ J : Index n k,
      coefficient (standardBasis n)
        (Specs.D04.C15.IntrinsicExteriorDerivative.Model.chartPullback (lowerChart c (by simp))
          (transportField S I k ξ) z) J = F (piCoordinates n z) J := by
    intro z hz hzU J
    have hcoeff := (EmbeddedAtlasResults.matching_chart_pullback S hS I hI C e he c hm z hz
      (hcover z hz)).2 k ξ |>.2 J
    rw [hcoeff]
    have hf := congrFun (hF_eq ⟨_, hcover z hz⟩
      (by simpa only [hcoord z hz] using hzU)) J
    simpa only [hcoord z hz] using hf.symm
  have hder := chartPullback_derivative_of_coefficients (lowerChart c (by simp))
    (transportField S I k ξ) u hu U hU huU F hF heF
  change _ = _
  rw [hder]
  have hd := ExteriorDerivativeResults.coordinateDerivative_evaluate_extension C k e he ξ p hp U hU hpU F hF hF_eq
    (fun j => piCoordinates n (v j))
  rw [show (e p).val = piCoordinates n u from hcoord u hu] at hd
  exact (derivative_reconstruction_extDeriv F u
    ((hF.contDiffAt (hU.mem_nhds huU)).differentiableAt (by norm_num)) v).trans hd.symm
end SmoothManifolds.EmbeddedDerivativeResults

namespace SmoothManifolds.EmbeddedDerivativeResults
open ModelData AtlasData TangentData BundleOperationsData ExteriorData
  ExteriorDerivativeData EmbeddedCalculusData EmbeddedAtlasData
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.ChartIndependentTangentSpaces.Model
open Specs.D04.C13.NormalizedFormsAndWedge.Model
open Set Filter Topology
open scoped BigOperators ContDiff

/-- The D04 all-chart characterization implies the original intrinsic one,
by evaluating on the matching smooth parametrization of each raw chart. -/
theorem hasDerivative_of_intrinsic {n N : ℕ} {a : ModelKind} {M : Set (E N)}
    (S : SmoothManifold n a M) (hS : IsInducedSmoothStructure S)
    (I : (p : M) → TangentSpace S p ≃ₗ[ℝ] tangentSpace 2 n M p.val)
    (hI : IsInclusionIdentification S I) (C : CotangentBundle S)
    (k : ℕ) (ξ : Field S k) (η : Field S (k+1)) (hξ : IsRegularField C 1 k ξ)
    (hη : Specs.D04.C15.IntrinsicExteriorDerivative.Model.HasIntrinsicExteriorDerivative
      (transportField S I k ξ) (transportField S I (k+1) η)) :
    HasExteriorDerivative C ξ η := by
  intro e he p hp
  have hraw : IsRawEmbeddedChart e := by rw [hS] at he; exact he
  obtain ⟨c, hm, hcover⟩ := embeddedChart_of_raw e hraw
  let u := c.invFun p.val
  have hpc : p.val ∈ M ∩ c.ambient := ⟨p.property, (hm p hp).1⟩
  have hu : u ∈ c.source := c.map_target hpc
  let q : M := ⟨c.toFun u, (c.map_source hu).1⟩
  have hq : q ∈ e.source := hcover u hu
  have hqp : q = p := Subtype.ext (c.right_inv p.val hpc)
  have hlocal : η q = coordinateDerivative C k e he ξ q hq := by
    letI := (tangent_dimension S q).1
    apply (ExteriorAlgebraResults.alternating_interpretation (TangentSpace S q) (k+1)).1
    apply AlternatingMap.ext
    intro v
    let w : Fin (k+1) → E n := fun j => (piCoordinates n).symm
      (C.tangent.fiberCoordinates.equiv e he q hq (v j))
    have hpb := (EmbeddedAtlasResults.matching_chart_pullback S hS I hI C e he c hm u hu
      hq).2 (k+1) η |>.1 w
    have hd := congrArg (fun A => A w) (hη (lowerChart c (by simp)) u hu)
    have hcalc := matchingChart_derivative_evaluate S hS I hI C e he c hm hcover
      k ξ hξ u hu hq w
    rw [hpb, hcalc] at hd
    change evaluate (TangentSpace S q) (k+1) (η q)
        (fun j => (C.tangent.fiberCoordinates.equiv e he q hq).symm
          (piCoordinates n (w j))) =
      evaluate (TangentSpace S q) (k+1) (coordinateDerivative C k e he ξ q hq)
        (fun j => (C.tangent.fiberCoordinates.equiv e he q hq).symm
          (piCoordinates n (w j))) at hd
    simpa only [w, ContinuousLinearEquiv.apply_symm_apply,
      LinearEquiv.symm_apply_apply] using hd
  have hbase : (⟨q, hq⟩ : e.source) = ⟨p, hp⟩ := Subtype.ext hqp
  exact Eq.mp (congrArg (fun z : e.source =>
    η z.val = coordinateDerivative C k e he ξ z.val z.property) hbase) hlocal

/-- Full equivalence of the original chart characterizations. The actual D04
selector supplies a derivative whose inverse transport is characterized in all
intrinsic charts; uniqueness then gives the forward direction as well. -/
theorem hasDerivative_transport :
    Specs.SmoothManifolds.Integration.EmbeddedDerivative.hasDerivative_transportType := by
  intro n N a M hM S hS I hI C k ξ η hξ
  have hM₂ := (EmbeddedAtlasResults.smooth_c2_tangents hM).1
  have hrξ := (regularity_transport hM S hS I hI C k ξ).mp hξ
  have hsel := D04.Intrinsic.intrinsicExteriorDerivative_spec hM₂
    (transportField S I k ξ) hrξ
  obtain ⟨ζ, hζsel⟩ := (EmbeddedAtlasResults.transportField_bijective S I (k+1)).2
    (Specs.D04.C15.IntrinsicExteriorDerivative.Model.intrinsicExteriorDerivative
      (transportField S I k ξ))
  have hζD : Specs.D04.C15.IntrinsicExteriorDerivative.Model.HasIntrinsicExteriorDerivative
      (transportField S I k ξ) (transportField S I (k+1) ζ) := by
    rw [hζsel]
    exact hsel.2
  have hζ := hasDerivative_of_intrinsic S hS I hI C k ξ ζ hξ hζD
  constructor
  · intro hη
    have heq : η = ζ := ExteriorDerivativeResults.derivative_unique C k ξ η ζ hη hζ
    rw [heq]
    refine ⟨?_, hζD⟩
    rw [hζsel]
    exact hsel.1
  · rintro ⟨_, hη⟩
    exact hasDerivative_of_intrinsic S hS I hI C k ξ η hξ hη

/-- The comparison with the literal D04 selector follows from existence and
uniqueness of the two original derivative characterizations. -/
theorem intrinsicExteriorDerivative_transport :
    Specs.SmoothManifolds.Integration.EmbeddedDerivative.intrinsicExteriorDerivative_transportType := by
  intro n N a M hM S hS I hI C k ξ hξ
  have hM₂ := (EmbeddedAtlasResults.smooth_c2_tangents hM).1
  obtain ⟨η, hη, hcη⟩ := ExteriorDerivativeResults.c1_derivative_exists C k ξ hξ
  have hdη := (hasDerivative_transport hM S hS I hI C k ξ η hξ).mp hη
  have hrξ := (regularity_transport hM S hS I hI C k ξ).mp hξ
  have hsel := D04.Intrinsic.intrinsicExteriorDerivative_spec hM₂
    (transportField S I k ξ) hrξ
  refine ⟨η, ⟨hcη, hη, ?_⟩, ?_⟩
  · exact D04.Intrinsic.intrinsic_exteriorDerivative_unique hM₂
      (transportField S I k ξ) (transportField S I (k+1) η)
      (Specs.D04.C15.IntrinsicExteriorDerivative.Model.intrinsicExteriorDerivative
        (transportField S I k ξ)) hdη.2 hsel.2
  · intro ζ hζ
    exact ExteriorDerivativeResults.derivative_unique C k ξ ζ η hζ.2.1 hη

/-- A continuous coefficient vector on a model chart admits local C⁰ extensions. -/
theorem continuous_locally_extendible {n : ℕ} {a : ModelKind}
    {M : Type*} [TopologicalSpace M] {ι : Type*} [Fintype ι]
    (e : ModelChart n a M) (f : e.source → ι → ℝ) (hf : Continuous f) :
    LocallyContDiffAlong 0 (fun p : e.source => (e p.val).val) f := by
  classical
  obtain ⟨V, hV, hVe⟩ := isOpen_induced_iff.mp e.open_target
  let t : Set V := Subtype.val ⁻¹' modelSet n a
  have ht : IsClosed t := (isClosed_modelSet n a).preimage continuous_subtype_val
  let j : t → ModelSpace n a := fun z => ⟨z.val.val, z.property⟩
  have hj : Continuous j := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have hjt (z : t) : j z ∈ e.target := by
    rw [← hVe]
    exact z.val.property
  let i : t → e.source := fun z => ⟨e.symm (j z), e.map_target (hjt z)⟩
  have hi : Continuous i := (e.symm.continuousOn.comp_continuous hj hjt).subtype_mk _
  obtain ⟨g, hg⟩ := (ContinuousMap.mk (f ∘ i) (hf.comp hi)).exists_restrict_eq ht
  let F : Euclidean n → ι → ℝ := fun x => if hx : x ∈ V then g ⟨x, hx⟩ else 0
  have hF : ContinuousOn F V := by
    apply continuousOn_iff_continuous_restrict.mpr
    exact g.continuous.congr (fun x => by
      change g x = F x.val
      dsimp [F]
      rw [dif_pos x.property])
  intro p
  have hpV : (e p.val).val ∈ V := by
    have hp := e.map_source p.property
    rwa [← hVe] at hp
  refine ⟨V, hV, hpV, F, (contDiffOn_zero).mpr hF, ?_⟩
  intro q hqV
  dsimp [F]
  rw [dif_pos hqV]
  have heq := congrArg (fun h : C(t, ι → ℝ) =>
    h (⟨⟨(e q.val).val, hqV⟩, (e q.val).property⟩ : t)) hg
  change g ⟨(e q.val).val, hqV⟩ = f (i _) at heq
  rw [heq]
  congr 1
  apply Subtype.ext
  exact e.left_inv q.property


theorem chartPullback_extension_of_regular_coefficients {n N k r : ℕ} {M : Set (E N)}
    (c : EmbeddedChart 2 n N M)
    (ξ : Specs.D04.C15.IntrinsicExteriorDerivative.Model.IntrinsicForm (k := n) M k)
    (u : E n) (hu : u ∈ c.source)
    (U : Set (Euclidean n)) (hU : IsOpen U) (huU : piCoordinates n u ∈ U)
    (F : Euclidean n → Index n k → ℝ) (hF : ContDiffOn ℝ r F U)
    (he : ∀ z ∈ c.source, piCoordinates n z ∈ U → ∀ J : Index n k,
      coefficient (standardBasis n)
        (Specs.D04.C15.IntrinsicExteriorDerivative.Model.chartPullback c ξ z) J =
          F (piCoordinates n z) J) :
    ∃ (W : Set (E n)) (α : FormField n k), IsOpen W ∧ u ∈ W ∧
      IsCrForm (some r) W α ∧
      EqOn α (Specs.D04.C15.IntrinsicExteriorDerivative.Model.chartPullback c ξ)
        (c.source ∩ W) := by
  let W := (piCoordinates n) ⁻¹' U
  let f : E n → Index n k → ℝ := fun z => F (piCoordinates n z)
  refine ⟨W, coefficientForm f, hU.preimage (piCoordinates n).continuous, huU,
    coefficientForm_isCr (hU.preimage (piCoordinates n).continuous) f ?_, ?_⟩
  · exact hF.comp (piCoordinates n).contDiff.contDiffOn (fun _ hz => hz)
  · intro z hz
    apply (D04.covector_expansion_unique (standardBasis n)
      (Specs.D04.C15.IntrinsicExteriorDerivative.Model.chartPullback c ξ z) (f z)).mpr
        (funext (fun J => (he z hz.1 hz.2 J).symm)) |>.symm


theorem matchingChart_regular_extension {n N r : ℕ} {a : ModelKind} {M : Set (E N)}
    (S : SmoothManifold n a M) (hS : IsInducedSmoothStructure S)
    (I : (p : M) → TangentSpace S p ≃ₗ[ℝ] tangentSpace 2 n M p.val)
    (hI : IsInclusionIdentification S I) (C : CotangentBundle S)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
    (c : EmbeddedChart ∞ n N M) (hm : MatchesEmbeddedChart e c)
    (hcover : ∀ z (hz : z ∈ c.source),
      (⟨c.toFun z, (c.map_source hz).1⟩ : M) ∈ e.source)
    (k : ℕ) (ξ : Field S k) (hξ : IsRegularField C r k ξ)
    (u : E n) (hu : u ∈ c.source) :
    let c₂ := lowerChart c (by simp : (2 : ℕ∞ω) ≤ ∞)
    ∃ (W : Set (E n)) (α : FormField n k), IsOpen W ∧ u ∈ W ∧
      IsCrForm (some r) W α ∧
      EqOn α (Specs.D04.C15.IntrinsicExteriorDerivative.Model.chartPullback c₂
        (transportField S I k ξ)) (c₂.source ∩ W) := by
  let p : M := ⟨c.toFun u, (c.map_source hu).1⟩
  have hp : p ∈ e.source := hcover u hu
  have hcoord (z : E n) (hz : z ∈ c.source) :
      (e (⟨c.toFun z, (c.map_source hz).1⟩ : M)).val = piCoordinates n z := by
    rw [(hm _ (hcover z hz)).2, c.left_inv z hz]
  obtain ⟨U, hU, hpU, F, hF, hF_eq⟩ := hξ e he ⟨p, hp⟩
  have huU : piCoordinates n u ∈ U := by
    simpa only [p, hcoord u hu] using hpU
  apply chartPullback_extension_of_regular_coefficients
    (lowerChart c (by simp)) (transportField S I k ξ) u hu U hU huU F hF
  intro z hz hzU J
  have hcoeff := (EmbeddedAtlasResults.matching_chart_pullback S hS I hI C e he c hm z hz
    (hcover z hz)).2 k ξ |>.2 J
  rw [hcoeff]
  have hf := congrFun (hF_eq ⟨_, hcover z hz⟩
    (by simpa only [hcoord z hz] using hzU)) J
  simpa only [hcoord z hz] using hf.symm



/-- Coefficient continuity suffices for local C⁰ extension in every intrinsic chart. -/
theorem regular_zero_of_continuous {n : ℕ} {a : ModelKind}
    {M : Type*} [TopologicalSpace M] {S : SmoothManifold n a M}
    (C : CotangentBundle S) (k : ℕ) (ξ : Field S k)
    (hξ : IsContinuousField C k ξ) : IsRegularField C 0 k ξ := by
  intro e he
  exact continuous_locally_extendible e _ (continuous_pi (fun J => hξ e he J))

/-- Continuous local ambient representatives imply the literal all-C²-chart
continuity condition. The parameter maps are genuinely C². -/
theorem intrinsicContinuous_of_local_ambient {n N k : ℕ} {M : Set (E N)}
    (ξ : Specs.D04.C15.IntrinsicExteriorDerivative.Model.IntrinsicForm (k := n) M k)
    (hξ : ∀ x : M, ∃ (O : Set (E N)) (Ω : FormField N k), IsOpen O ∧ x.val ∈ O ∧
      IsCrForm (some 0) O Ω ∧ ∀ y : M, y.val ∈ O →
        Specs.D04.C15.IntrinsicExteriorDerivative.Model.ambientRestriction M Ω y = ξ y) :
    Specs.D04.C15.IntrinsicExteriorDerivative.Model.IntrinsicContinuous ξ := by
  intro c J
  apply continuousOn_of_locally_continuousOn
  intro u hu
  obtain ⟨O, Ω, hO, hxO, hΩ, heΩ⟩ := hξ ⟨c.toFun u, (c.map_source hu).1⟩
  obtain ⟨W, g, hW, huW, hmap, hg, he⟩ :=
    D04.Intrinsic.chart_ambient_local c hu O hO hxO
  have hg1 : Specs.D04.C02.DerivativeInterfaces.Model.CrOn 1 W g :=
    (D04.crOn_iff_contDiffOn 1 W g hW).mpr
      (((D04.crOn_iff_contDiffOn 2 W g hW).mp hg).of_le (by norm_num))
  have hc := (D04.pullback_continuous W O g Ω hW hmap hg1 hΩ).2 J
  have hev := D04.Intrinsic.chartPullback_eventuallyEq c hu
    (Specs.D04.C15.IntrinsicExteriorDerivative.Model.ambientRestriction M Ω) ξ O hO hxO heΩ
  obtain ⟨A, hAsub, hA, huA⟩ := mem_nhds_iff.mp (eventually_nhdsWithin_iff.mp hev)
  refine ⟨W ∩ A, hW.inter hA, ⟨huW, huA⟩, ?_⟩
  apply (hc.mono (inter_subset_right.trans inter_subset_left)).congr
  intro v hv
  exact congrArg (fun α => coefficient (standardBasis n) α J)
    ((he k Ω ⟨hv.1, hv.2.1⟩).trans (hAsub hv.2.2 hv.1)).symm

/-- D04 continuity pulls back to every matching intrinsic chart. -/
theorem matchingChart_continuous_of_intrinsicContinuous {n N : ℕ} {a : ModelKind}
    {M : Set (E N)} (S : SmoothManifold n a M) (hS : IsInducedSmoothStructure S)
    (I : (p : M) → TangentSpace S p ≃ₗ[ℝ] tangentSpace 2 n M p.val)
    (hI : IsInclusionIdentification S I) (C : CotangentBundle S)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
    (c : EmbeddedChart ∞ n N M) (hm : MatchesEmbeddedChart e c)
    (k : ℕ) (ξ : Field S k)
    (hξ : Specs.D04.C15.IntrinsicExteriorDerivative.Model.IntrinsicContinuous
      (transportField S I k ξ)) (J : Index n k) :
    Continuous (fun p : e.source => coefficients C k e he ξ p J) := by
  let c₂ := lowerChart c (by simp : (2 : ℕ∞ω) ≤ ∞)
  let f : e.source → c₂.source := fun p =>
    ⟨c.invFun p.val.val, c.map_target ⟨p.val.property, (hm p.val p.property).1⟩⟩
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    exact c.continuous_invFun.comp_continuous
      (continuous_subtype_val.comp continuous_subtype_val)
      (fun p => ⟨p.val.property, (hm p.val p.property).1⟩)
  have hc := continuousOn_iff_continuous_restrict.mp (hξ c₂ J)
  apply (hc.comp hf).congr
  intro p
  let z := c.invFun p.val.val
  have hz : z ∈ c.source := c.map_target ⟨p.val.property, (hm p.val p.property).1⟩
  have hpz : (⟨c.toFun z, (c.map_source hz).1⟩ : M) = p.val :=
    Subtype.ext (c.right_inv p.val.val ⟨p.val.property, (hm p.val p.property).1⟩)
  have hcoeff := (EmbeddedAtlasResults.matching_chart_pullback S hS I hI C e he c hm z hz
    (by simpa only [hpz] using p.property)).2 k ξ |>.2 J
  change coefficient (standardBasis n)
    (Specs.D04.C15.IntrinsicExteriorDerivative.Model.chartPullback c₂
      (transportField S I k ξ) z) J = _
  simpa only [hpz] using hcoeff

/-- The continuity bridge, on all D04 C² test charts. -/
theorem continuous_transport :
    Specs.SmoothManifolds.Integration.EmbeddedDerivative.continuous_transportType := by
  intro n N a M hM S hS I hI C k ξ
  constructor
  · intro hξ
    have hR := regular_zero_of_continuous C k ξ hξ
    have hM₂ : IsEmbeddedManifold 2 n M :=
      EmbeddedAtlasResults.lower_manifold hM (by simp) (by constructor <;> norm_num)
    apply intrinsicContinuous_of_local_ambient
    intro x
    obtain ⟨e, he, hxe⟩ := S.smoothStructure.property.1.1 x
    have hraw : IsRawEmbeddedChart e := by rw [hS] at he; exact he
    obtain ⟨c, hm, hcover⟩ := embeddedChart_of_raw e hraw
    let u := c.invFun x.val
    have hu : u ∈ c.source := c.map_target ⟨x.property, (hm x hxe).1⟩
    have hcu : c.toFun u = x.val := c.right_inv x.val ⟨x.property, (hm x hxe).1⟩
    obtain ⟨W, α, hW, huW, hα, heα⟩ :=
      matchingChart_regular_extension S hS I hI C e he c hm hcover k ξ hR u hu
    obtain ⟨O, Ω, hO, hxO, hΩ, heΩ⟩ :=
      local_ambient_of_chart_extension hM₂ (by omega : 0 ≤ 1)
        (transportField S I k ξ) (lowerChart c (by simp)) u hu W α hW huW hα heα
    change c.toFun u ∈ O at hxO
    rw [hcu] at hxO
    exact ⟨O, Ω, hO, hxO, hΩ, heΩ⟩
  · intro hξ e he J
    have hraw : IsRawEmbeddedChart e := by rw [hS] at he; exact he
    obtain ⟨c, hm, _⟩ := embeddedChart_of_raw e hraw
    exact matchingChart_continuous_of_intrinsicContinuous S hS I hI C e he c hm k ξ hξ J


end SmoothManifolds.EmbeddedDerivativeResults
