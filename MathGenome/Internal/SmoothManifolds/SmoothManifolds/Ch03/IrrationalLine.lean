import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch03.IrrationalLine
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.MapClasses
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Examples.SpheresAndTori
import Mathlib.Topology.Sequences

namespace SmoothManifolds.IrrationalLine
open ModelData AtlasData MapData SphereTorusData FiniteRegularityData MapClassData
  IrrationalLineData Set Filter
open scoped Topology

lemma lineLinear_apply (α : ℝ) (x : Euclidean 1) :
    lineLinear α x = ![x 0, α * x 0] := by
  ext i
  fin_cases i <;> simp [IrrationalLineData.lineLinear, ContinuousLinearMap.pi_apply]

lemma lineLinear_injective (α : ℝ) : Function.Injective (lineLinear α) := by
  intro x y h
  have h0 := congrFun h 0
  simp only [lineLinear_apply, Matrix.cons_val_zero] at h0
  ext i
  have hi : i = 0 := Subsingleton.elim _ _
  simpa [hi] using h0

lemma continuous_line (α : ℝ) : Continuous (irrationalLine α) := by
  apply (SphereTorus.quotientProjection_isOpenQuotientMap 2).continuous.comp
  change Continuous (fun t : ℝ => ![t, α * t])
  fun_prop

lemma line_sub (α x y : ℝ) :
    irrationalLine α (x - y) = irrationalLine α x - irrationalLine α y := by
  ext i
  fin_cases i <;>
    simp [IrrationalLineData.irrationalLine, SphereTorusData.quotientProjection, lineLift, mul_sub]

@[simp] lemma line_zero (α : ℝ) : irrationalLine α 0 = 0 := by
  ext i
  fin_cases i <;> simp [IrrationalLineData.irrationalLine, SphereTorusData.quotientProjection, lineLift]

theorem injective : Specs.SmoothManifolds.Ch03.IrrationalLine.injectiveType := by
  intro α hα x y hxy
  obtain ⟨z, hz⟩ := (SphereTorus.quotientProjection_fiber 2 _ _).mp hxy
  have h0 : x = y + (z 0 : ℝ) := by simpa [lineLift] using hz 0
  have h1 : α * x = α * y + (z 1 : ℝ) := by simpa [lineLift] using hz 1
  by_cases h : z 0 = 0
  · simpa [h] using h0
  · exfalso
    apply hα.ne_rational (z 1) (z 0)
    apply (eq_div_iff (by exact_mod_cast h : (z 0 : ℝ) ≠ 0)).mpr
    rw [h0, mul_add] at h1
    linarith

lemma realAtlas_smooth : IsContDiffAtlas (⊤ : ℕ∞) realAtlas := by
  refine ⟨fun p => ⟨realChart, rfl, mem_univ p⟩, ?_⟩
  intro c hc d hd
  have hc' : c = realChart := mem_singleton_iff.mp hc
  have hd' : d = realChart := mem_singleton_iff.mp hd
  subst c; subst d
  apply contDiffCompatible_of_germs
  all_goals
    intro p hp hp'
    exact ⟨univ, isOpen_univ, mem_univ _, id, contDiff_id.contDiffOn,
      Eventually.of_forall (fun _ => rfl)⟩

theorem standardManifolds : Specs.SmoothManifolds.Ch03.IrrationalLine.standardManifoldsType := by
  constructor
  · exact ⟨⟨⟨inferInstance, inferInstance, realAtlas, realAtlas_smooth.1⟩,
      ⟨_, maximalExtension_isMaximal realAtlas_smooth⟩⟩, rfl⟩
  · obtain ⟨Q, _, hQ⟩ := (SphereTorus.angleManifold 2).2.2
    exact ⟨Q, hQ⟩

/-- A local lift of the line in any quotient chart differs from its ordinary
lift by a constant lattice vector. -/
lemma quotient_germ (α t : ℝ) (a : Euclidean 2) (ε : ℝ)
    (d : ModelChart 2 .euclidean (FlatTorus 2)) (hd : IsAngleChart a ε d)
    (ht : irrationalLine α t ∈ d.source) :
    (fun s => lineLift α s + ((d (irrationalLine α t)).val - lineLift α t))
      =ᶠ[𝓝 t] (fun s => (d (irrationalLine α s)).val) := by
  let v := (d (irrationalLine α t)).val
  let F : ℝ → Euclidean 2 := fun s => lineLift α s + (v - lineLift α t)
  have hF : Continuous F := by dsimp [F, lineLift]; fun_prop
  have hFp : F t = v := by dsimp [F]; abel
  have hdcont := continuous_subtype_val.continuousAt.comp
    ((d.continuousAt ht).comp (continuous_line α).continuousAt)
  have hvbox := (SphereTorus.isOpen_angleBox v (1 / 4)).mem_nhds
    (SphereTorus.mem_angleBox_center v (by norm_num))
  have hFbox : ∀ᶠ s in 𝓝 t, F s ∈ angleBox v (1 / 4) :=
    hF.continuousAt.preimage_mem_nhds (by simpa [hFp] using hvbox)
  have hdbox : ∀ᶠ s in 𝓝 t, (d (irrationalLine α s)).val ∈ angleBox v (1 / 4) :=
    hdcont.preimage_mem_nhds hvbox
  have hsource : ∀ᶠ s in 𝓝 t, irrationalLine α s ∈ d.source :=
    (continuous_line α).continuousAt.preimage_mem_nhds (d.open_source.mem_nhds ht)
  have hproj : quotientProjection 2 (v - lineLift α t) = 0 := by
    have hv := SphereTorus.angleChart_projection hd ht
    ext j
    change (v j : AddCircle (1 : ℝ)) - ((lineLift α t) j : AddCircle (1 : ℝ)) = 0
    exact sub_eq_zero.mpr (congrFun hv j)
  filter_upwards [hFbox, hdbox, hsource] with s hsF hsd hs
  apply SphereTorus.quotientProjection_injOn_box v
    (by norm_num : (1 : ℝ) / 4 < 1 / 2) hsF hsd
  have he : quotientProjection 2 (F s) = irrationalLine α s := by
    ext j
    change ((lineLift α s) j : AddCircle (1 : ℝ)) +
      ((v - lineLift α t) j : AddCircle (1 : ℝ)) = _
    have hzero := congrFun hproj j
    change ((v - lineLift α t) j : AddCircle (1 : ℝ)) = 0 at hzero
    rw [hzero, add_zero]
    rfl
  exact he.trans (SphereTorus.angleChart_projection hd hs).symm

lemma quotient_chart_smooth (α t : ℝ) (a : Euclidean 2) (ε : ℝ)
    (d : ModelChart 2 .euclidean (FlatTorus 2)) (hd : IsAngleChart a ε d)
    (ht : irrationalLine α t ∈ d.source) :
    ChartContDiffAt (⊤ : ℕ∞) realChart d (irrationalLine α) t := by
  let c := (d (irrationalLine α t)).val - lineLift α t
  refine ⟨univ, isOpen_univ, mem_univ _, fun x => lineLinear α x + c,
    ((lineLinear α).contDiff.add contDiff_const).contDiffOn, ?_⟩
  simpa [lineLinear_apply, IrrationalLineData.realChart, realCoordinates, lineLift, c] using quotient_germ α t a ε d hd ht

theorem quotientDerivative : Specs.SmoothManifolds.Ch03.IrrationalLine.quotientDerivativeType := by
  intro α t a ε d hd ht
  have hder : chartDerivative realChart d (irrationalLine α) t = lineLinear α := by
    apply FiniteRegularity.coordinateDerivative_eq realChart _ t (mem_univ _) (lineLinear α)
    refine ⟨fun x => lineLinear α x +
      ((d (irrationalLine α t)).val - lineLift α t), ?_, ?_⟩
    · exact (lineLinear α).hasFDerivAt.add_const _
    · simpa [lineLinear_apply, IrrationalLineData.realChart, realCoordinates, lineLift] using quotient_germ α t a ε d hd ht
  refine ⟨hder, by simp [lineLinear_apply], ?_⟩
  intro hzero
  have h := congrFun hzero 0
  norm_num [lineLinear_apply] at h

lemma line_smooth_generated (α : ℝ) :
    ManifoldContDiff (⊤ : ℕ∞) realAtlas (angleAtlas 2) (irrationalLine α) := by
  intro t
  refine ⟨(continuous_line α).continuousAt, ?_⟩
  rintro e he d ⟨a, ε, _, _, hd⟩ _ ht
  have he' : e = realChart := mem_singleton_iff.mp he
  subst e
  exact quotient_chart_smooth α t a ε d hd ht

theorem smoothImmersion : Specs.SmoothManifolds.Ch03.IrrationalLine.smoothImmersionType := by
  intro α S Q hS hQ
  have hs : IsSmoothMap S Q (irrationalLine α) := by
    change ManifoldContDiff (⊤ : ℕ∞) _ _ _
    rw [hS, hQ]
    exact (manifoldContDiff_maximalExtension_iff _ _ _ realAtlas_smooth
      (SphereTorus.angleAtlas_isContDiffAtlas 2) _).mpr (line_smooth_generated α)
  refine ⟨hs, fun t => ?_⟩
  have hs1 := manifoldContDiff_of_le (⊤ : ℕ∞) 1 _ _ _ (by simp) hs
  obtain ⟨d, hd, ht⟩ := (SphereTorus.angleAtlas_isContDiffAtlas 2).1 (irrationalLine α t)
  have he : realChart ∈ S.smoothStructure.val := by
    rw [hS]; exact subset_maximalExtension realAtlas_smooth rfl
  have hd' : d ∈ Q.smoothStructure.val := by
    rw [hQ]; exact subset_maximalExtension (SphereTorus.angleAtlas_isContDiffAtlas 2) hd
  apply (MapClasses.chart_invariants S Q _ hs1 t realChart d he hd' (mem_univ _) ht).2.1.mpr
  obtain ⟨a, ε, _, _, hangle⟩ := hd
  rw [(quotientDerivative α t a ε d hangle ht).1]
  exact lineLinear_injective α

/-- Compactness alone rules out an embedding for every slope. -/
lemma not_isEmbedding (α : ℝ) : ¬ Topology.IsEmbedding (irrationalLine α) := by
  intro he
  obtain ⟨p, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq
    (fun n : ℕ => irrationalLine α (n : ℝ))
  have hlim' : Tendsto (fun n => irrationalLine α (φ (n + 1) : ℝ)) atTop (𝓝 p) :=
    hlim.comp (tendsto_add_atTop_nat 1)
  have hd : Tendsto (fun n => irrationalLine α ((φ (n + 1) : ℝ) - (φ n : ℝ)))
      atTop (𝓝 (irrationalLine α 0)) := by
    simpa only [line_sub, sub_self, line_zero, Function.comp_def] using hlim'.sub hlim
  have hreal : Tendsto (fun n => (φ (n + 1) : ℝ) - (φ n : ℝ)) atTop (𝓝 0) :=
    he.tendsto_nhds_iff.mpr hd
  have hsmall : ∀ᶠ n : ℕ in atTop, (φ (n + 1) : ℝ) - (φ n : ℝ) < 1 :=
    hreal.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨n, hn⟩ := hsmall.exists
  have hstep : φ n + 1 ≤ φ (n + 1) := hφ (Nat.lt_succ_self n)
  have hstep' : (φ n : ℝ) + 1 ≤ (φ (n + 1) : ℝ) := by exact_mod_cast hstep
  linarith

theorem notHomeomorph : Specs.SmoothManifolds.Ch03.IrrationalLine.notHomeomorphType := by
  rintro α ⟨h, hh⟩
  apply not_isEmbedding α
  have hcomp := Topology.IsEmbedding.subtypeVal.comp h.isEmbedding
  have heq : (Subtype.val ∘ h) = irrationalLine α := funext hh
  rwa [heq] at hcomp

theorem notEmbedding : Specs.SmoothManifolds.Ch03.IrrationalLine.notEmbeddingType := by
  rintro α S Q ⟨_, _, _, hh⟩
  exact notHomeomorph α hh

lemma rangeParam_bijective (α : ℝ) (hα : Irrational α) :
    Function.Bijective (rangeParam α) := by
  constructor
  · intro x y hxy
    exact injective α hα (congrArg Subtype.val hxy)
  · rintro ⟨y, t, rfl⟩
    exact ⟨t, rfl⟩

noncomputable def rangeHomeomorph (α : ℝ) (hα : Irrational α) :
    @Homeomorph ℝ (lineRange α) inferInstance (immersedTopology α) := by
  letI : TopologicalSpace (lineRange α) := immersedTopology α
  let e := Equiv.ofBijective (rangeParam α) (rangeParam_bijective α hα)
  refine { e with continuous_toFun := continuous_coinduced_rng, continuous_invFun := ?_ }
  apply continuous_coinduced_dom.mpr
  change Continuous (fun x => e.symm (e x))
  have he : (fun x => e.symm (e x)) = id := funext e.symm_apply_apply
  rw [he]
  exact continuous_id

lemma immersedTopology_strict (α : ℝ) (hα : Irrational α) :
    immersedTopology α < (inferInstance : TopologicalSpace (lineRange α)) := by
  have hcont : Continuous (rangeParam α) := (continuous_line α).subtype_mk _
  refine lt_of_le_of_ne hcont.coinduced_le ?_
  intro heq
  let e := Equiv.ofBijective (rangeParam α) (rangeParam_bijective α hα)
  have hc₀ : @Continuous (lineRange α) ℝ (immersedTopology α) inferInstance e.symm := by
    apply continuous_coinduced_dom.mpr
    change Continuous (fun x => e.symm (e x))
    have hid : (fun x => e.symm (e x)) = id := funext e.symm_apply_apply
    rw [hid]
    exact continuous_id
  have hc : Continuous e.symm := by
    exact (congrArg (fun top : TopologicalSpace (lineRange α) =>
      @Continuous (lineRange α) ℝ top inferInstance e.symm) heq).mp hc₀
  exact notHomeomorph α ⟨{ e with continuous_toFun := hcont, continuous_invFun := hc },
    fun _ => rfl⟩

/-- Smoothness is unchanged by transporting the parametrization's source. -/
lemma transported_line_smooth {X : Type} [TopologicalSpace X]
    (α : ℝ) (h : ℝ ≃ₜ X) (f : X → FlatTorus 2)
    (hf : ∀ x, f x = irrationalLine α (h.symm x)) :
    ManifoldContDiff (⊤ : ℕ∞) (transportAtlas h realAtlas) (angleAtlas 2) f := by
  intro x
  have hcont : Continuous f := by
    have heq : f = irrationalLine α ∘ h.symm := funext hf
    rw [heq]
    exact (continuous_line α).comp h.symm.continuous
  refine ⟨hcont.continuousAt, ?_⟩
  rintro e ⟨e₀, he₀, rfl⟩ d ⟨a, ε, _, _, hd⟩ _ hfx
  have he₀' : e₀ = realChart := mem_singleton_iff.mp he₀
  subst e₀
  have hfx' : irrationalLine α (h.symm x) ∈ d.source := by rwa [hf] at hfx
  have hg := LocalCoordinateExtension.precomp
    (quotient_chart_smooth α (h.symm x) a ε d hd hfx') h.symm.continuous.continuousAt rfl
  change LocalCoordinateExtension _ _ _ _ at hg ⊢
  simpa only [transportedChart_apply, Function.comp_def, ← hf] using hg

lemma transported_line_derivative {X : Type} [TopologicalSpace X]
    (α : ℝ) (h : ℝ ≃ₜ X) (f : X → FlatTorus 2)
    (hf : ∀ x, f x = irrationalLine α (h.symm x))
    (x : X) (a : Euclidean 2) (ε : ℝ)
    (d : ModelChart 2 .euclidean (FlatTorus 2)) (hd : IsAngleChart a ε d)
    (hfx : f x ∈ d.source) :
    chartDerivative (h.symm.toOpenPartialHomeomorph.trans realChart) d f x = lineLinear α := by
  let e := h.symm.toOpenPartialHomeomorph.trans realChart
  have he : x ∈ e.source := ⟨mem_univ _, mem_univ _⟩
  apply FiniteRegularity.coordinateDerivative_eq e _ x he (lineLinear α)
  let c := (d (irrationalLine α (h.symm x))).val - lineLift α (h.symm x)
  refine ⟨fun y => lineLinear α y + c, (lineLinear α).hasFDerivAt.add_const _, ?_⟩
  have hfx' : irrationalLine α (h.symm x) ∈ d.source := by rwa [hf] at hfx
  have hg := (quotient_germ α (h.symm x) a ε d hd hfx').comp_tendsto h.symm.continuous.continuousAt
  simpa [Function.comp_def, lineLinear_apply, e, c, IrrationalLineData.realChart, realCoordinates, lineLift, hf] using hg

theorem immersedRange : Specs.SmoothManifolds.Ch03.IrrationalLine.immersedRangeType := by
  intro α hα S Q _ hQ
  refine ⟨immersedTopology_strict α hα, ?_⟩
  letI : TopologicalSpace (lineRange α) := immersedTopology α
  let h := rangeHomeomorph α hα
  have hh : ∀ t, h t = rangeParam α t := fun _ => rfl
  refine ⟨h, hh, ?_⟩
  letI : T2Space (lineRange α) := h.t2Space
  letI : SecondCountableTopology (lineRange α) := h.symm.secondCountableTopology
  let A := transportAtlas h realAtlas
  have hA : IsContDiffAtlas (⊤ : ℕ∞) A :=
    transportAtlas_isContDiffAtlas _ _ h realAtlas_smooth
  let R : SmoothManifold 1 .euclidean (lineRange α) :=
    ⟨⟨inferInstance, inferInstance, A, hA.1⟩, ⟨_, maximalExtension_isMaximal hA⟩⟩
  have hval : ∀ x : lineRange α, x.val = irrationalLine α (h.symm x) := by
    intro x
    have hx := congrArg Subtype.val (h.apply_symm_apply x)
    exact hx.symm
  have hs : IsSmoothMap R Q Subtype.val := by
    change ManifoldContDiff (⊤ : ℕ∞) (maximalExtension _ A) Q.smoothStructure.val _
    rw [hQ]
    apply (manifoldContDiff_maximalExtension_iff _ _ _ hA
      (SphereTorus.angleAtlas_isContDiffAtlas 2) _).mpr
    exact transported_line_smooth α h Subtype.val hval
  refine ⟨R, rfl, hs, fun x => ?_⟩
  have hs1 := manifoldContDiff_of_le (⊤ : ℕ∞) 1 _ _ _ (by simp) hs
  obtain ⟨d, hd, hx⟩ := (SphereTorus.angleAtlas_isContDiffAtlas 2).1 x.val
  let e := h.symm.toOpenPartialHomeomorph.trans realChart
  have heA : e ∈ A := ⟨realChart, rfl, rfl⟩
  have heR : e ∈ R.smoothStructure.val := subset_maximalExtension hA heA
  have hdQ : d ∈ Q.smoothStructure.val := by
    rw [hQ]; exact subset_maximalExtension (SphereTorus.angleAtlas_isContDiffAtlas 2) hd
  apply (MapClasses.chart_invariants R Q Subtype.val hs1 x e d heR hdQ
    ⟨mem_univ _, mem_univ _⟩ hx).2.1.mpr
  obtain ⟨a, ε, _, _, hangle⟩ := hd
  rw [transported_line_derivative α h Subtype.val hval x a ε d hangle hx]
  exact lineLinear_injective α

-- Public aliases of the canonical objects, shared with the independent Specs.
abbrev irrationalLine := IrrationalLineData.irrationalLine
abbrev lineLift := IrrationalLineData.lineLift
noncomputable abbrev lineLinear := IrrationalLineData.lineLinear
abbrev realAtlas := IrrationalLineData.realAtlas
abbrev lineRange := IrrationalLineData.lineRange
abbrev rangeParam := IrrationalLineData.rangeParam
abbrev immersedTopology := IrrationalLineData.immersedTopology

end SmoothManifolds.IrrationalLine
