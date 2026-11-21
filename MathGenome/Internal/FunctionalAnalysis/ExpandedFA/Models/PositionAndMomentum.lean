import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Models.PositionAndMomentum
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Multiplication.MultiplierTranspose
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.FourierHilbertScale

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory Filter
open scoped SchwartzMap FourierTransform ComplexConjugate Topology

namespace ExpandedFA.Models.PositionMomentum
open ExpandedFA.Fourier Multiplication Unbounded Sobolev Sobolev.FourierScale

/-- Position with its full maximal multiplication domain. -/
abbrev position : Operator ℂ H H := canonicalPosition

/-- Momentum as the unitary pullback of multiplication by `2πξ`.
The weak graph theorem below identifies its exact distributional domain. -/
abbrev momentum : Operator ℂ H H := canonicalMomentum

/-- The one-dimensional coordinate model is the ordinary measured real line. -/
def realLineCoordinates : Euclidean 1 ≃ₗᵢ[ℝ] ℝ where
  __ := (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)).toLinearEquiv
  norm_map' x := by
    change ‖x 0‖ = ‖x‖
    rw [EuclideanSpace.norm_eq]
    simp [Real.sqrt_sq_eq_abs]

@[simp] theorem realLineCoordinates_apply (x : Euclidean 1) : realLineCoordinates x = x 0 := rfl

theorem realLineCoordinates_measurePreserving :
    MeasurePreserving (fun x : Euclidean 1 => x 0) volume volume :=
  realLineCoordinates.measurePreserving

theorem realLine_inner (x y : Euclidean 1) : inner ℝ x y = x 0 * y 0 := by
  simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]

section Pullback
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (U : E ≃ₗᵢ[ℂ] E) (A : Operator ℂ E E)

@[simp] theorem unitaryPullback_domain (f : E) :
    f ∈ (unitaryPullback U A).domain ↔ U f ∈ A.domain := Iff.rfl

@[simp] theorem unitaryPullback_apply (f : (unitaryPullback U A).domain) :
    unitaryPullback U A f = U.symm (A ⟨U (f : E), f.2⟩) := rfl

theorem unitaryPullback_graph (f g : E) :
    (f, g) ∈ (unitaryPullback U A).graph ↔ (U f, U g) ∈ A.graph := by
  rw [show (f, g) ∈ (unitaryPullback U A).graph ↔
      ∃ hf : f ∈ (unitaryPullback U A).domain, unitaryPullback U A ⟨f, hf⟩ = g from
      Unbounded.mem_graph_iff _ _,
    show (U f, U g) ∈ A.graph ↔ ∃ hf : U f ∈ A.domain, A ⟨U f, hf⟩ = U g from
      Unbounded.mem_graph_iff _ _]
  constructor
  · rintro ⟨hf, hg⟩
    refine ⟨hf, ?_⟩
    simpa using congrArg U hg
  · rintro ⟨hf, hg⟩
    refine ⟨hf, ?_⟩
    simpa using congrArg U.symm hg

theorem unitaryPullback_cancel :
    unitaryPullback U.symm (unitaryPullback U A) = A := by
  apply LinearPMap.eq_of_eq_graph
  ext z
  rcases z with ⟨f, g⟩
  simp only [unitaryPullback_graph, U.apply_symm_apply]

theorem unitaryPullback_dense (hA : Dense (A.domain : Set E)) :
    Dense ((unitaryPullback U A).domain : Set E) := by
  change Dense (U ⁻¹' (A.domain : Set E))
  exact U.toHomeomorph.isOpenQuotientMap.dense_preimage_iff.mpr hA

theorem unitaryPullback_selfAdjoint [CompleteSpace E]
    (hd : Dense (A.domain : Set E)) (hs : IsSelfAdjoint A) :
    IsSelfAdjoint (unitaryPullback U A) := by
  apply LinearPMap.isSelfAdjoint_def.mpr
  apply LinearPMap.eq_of_eq_graph
  ext z
  rcases z with ⟨f, g⟩
  rw [← show hilbertAdjoint (unitaryPullback U A) =
      (unitaryPullback U A).adjoint from rfl,
    mem_hilbertAdjoint_graph_iff _ (unitaryPullback_dense U A hd),
    unitaryPullback_graph]
  have heq : hilbertAdjoint A = A := LinearPMap.isSelfAdjoint_def.mp hs
  have htest : (U f, U g) ∈ A.graph ↔
      ∀ x : A.domain, inner ℂ (A x) (U f) = inner ℂ (x : E) (U g) := by
    conv_lhs => rw [← heq]
    exact mem_hilbertAdjoint_graph_iff A hd _ _
  rw [htest]
  constructor
  · intro h x
    let y : (unitaryPullback U A).domain := ⟨U.symm (x : E), by simpa using x.2⟩
    have hy := h y
    have hx : (⟨U (y : E), y.2⟩ : A.domain) = x := Subtype.ext (by simp [y])
    have ht := U.inner_map_map (unitaryPullback U A y) f
    rw [unitaryPullback_apply, U.apply_symm_apply, hx] at ht
    calc
      inner ℂ (A x) (U f) = inner ℂ (unitaryPullback U A y) f := by
        simpa only [unitaryPullback_apply, hx] using ht
      _ = inner ℂ (y : E) g := hy
      _ = inner ℂ (x : E) (U g) := by
        rw [← U.inner_map_map (y : E) g]
        simp [y]
  · intro h y
    have hy := h ⟨U (y : E), y.2⟩
    rw [← U.inner_map_map (unitaryPullback U A y) f,
      unitaryPullback_apply, U.apply_symm_apply, hy, U.inner_map_map]

end Pullback

theorem position_domain : Spec.PositionDomain := by intro f; rfl

theorem position_apply : Spec.PositionApply := maximalLpMultiplier_apply volume 2 _

theorem position_selfAdjoint : IsSelfAdjoint position := by
  apply multiplier_real_selfAdjoint volume
  · exact Complex.continuous_ofReal.measurable.comp (by fun_prop)
  · exact Eventually.of_forall fun _ => rfl

theorem frequencyPosition_selfAdjoint : IsSelfAdjoint frequencyPosition := by
  apply multiplier_real_selfAdjoint volume
  · fun_prop
  · exact Eventually.of_forall fun _ => rfl

theorem frequencyPosition_dense : Dense (frequencyPosition.domain : Set H) := by
  apply maximalLpMultiplier_denselyDefined volume 2 (by norm_num)
  fun_prop

theorem momentum_selfAdjoint : IsSelfAdjoint momentum :=
  unitaryPullback_selfAdjoint (l2Fourier 1) frequencyPosition
    frequencyPosition_dense frequencyPosition_selfAdjoint

theorem selfAdjoint : Spec.SelfAdjoint := ⟨position_selfAdjoint, momentum_selfAdjoint⟩

theorem fourier_conjugation : Spec.FourierConjugation :=
  unitaryPullback_cancel (l2Fourier 1) frequencyPosition

theorem weakDerivative_iff_tempered (f g : H) :
    HasWeakDerivative f g ↔ Lp.toTemperedDistribution g =
      temperedPartial 0 (Lp.toTemperedDistribution f) := by
  constructor
  · intro h
    simpa only [temperedWordDerivative] using weak_to_regular_tempered_word f g [0] h
  · intro h
    apply regular_tempered_word_to_weak f g [0]
    simpa only [temperedWordDerivative] using h

theorem weakDerivative_fourier (f g : H) :
    HasWeakDerivative f g ↔
      (l2Fourier 1 g : Euclidean 1 → ℂ) =ᵐ[volume]
        fun ξ => (2 * Real.pi * Complex.I) * (ξ 0 : ℂ) * l2Fourier 1 f ξ := by
  have hp : (fun ξ : Euclidean 1 => (2 * Real.pi * Complex.I) * (ξ 0 : ℂ)).HasTemperateGrowth :=
    (Function.HasTemperateGrowth.const _).mul (coordinate_growth (𝕜 := ℂ) 0)
  rw [weakDerivative_iff_tempered]
  constructor
  · intro h
    apply regularMultiplier_ae_eq _ hp
    have hf := congrArg (fun T : Tempered ℂ 1 => temperedFourier T) h
    rw [fourier_temperedPartial_symbol] at hf
    change 𝓕 (Lp.toTemperedDistribution g) =
      TemperedDistribution.smulLeftCLM ℂ _ (𝓕 (Lp.toTemperedDistribution f)) at hf
    rw [Lp.fourier_toTemperedDistribution_eq, Lp.fourier_toTemperedDistribution_eq] at hf
    exact hf
  · intro h
    have heq : temperedFourier (Lp.toTemperedDistribution g) =
        temperedFourier (temperedPartial 0 (Lp.toTemperedDistribution f)) := by
      rw [fourier_temperedPartial_symbol]
      change 𝓕 (Lp.toTemperedDistribution g) =
        TemperedDistribution.smulLeftCLM ℂ _ (𝓕 (Lp.toTemperedDistribution f))
      rw [Lp.fourier_toTemperedDistribution_eq, Lp.fourier_toTemperedDistribution_eq]
      ext φ
      rw [TemperedDistribution.smulLeftCLM_apply_apply,
        Lp.toTemperedDistribution_apply, Lp.toTemperedDistribution_apply]
      simp only [SchwartzMap.smulLeftCLM_apply_apply hp]
      apply integral_congr_ae
      filter_upwards [h] with ξ hξ
      change φ ξ * l2Fourier 1 g ξ =
        (((2 * Real.pi * Complex.I) * (ξ 0 : ℂ)) * φ ξ) * l2Fourier 1 f ξ
      rw [hξ]
      ring
    ext φ
    have hi := congrArg (fun T : Tempered ℂ 1 => T (𝓕⁻ φ)) heq
    simpa only [temperedFourier, ContinuousLinearMap.comp_apply, schwartzFourier,
      FourierTransform.fourierCLM_apply, FourierTransform.fourier_fourierInv_eq] using hi

theorem weak_graph : Spec.WeakGraph := by
  intro f g
  rw [show (f, g) ∈ momentum.graph ↔
      (l2Fourier 1 f, l2Fourier 1 g) ∈ frequencyPosition.graph from
      unitaryPullback_graph _ _ f g,
    frequencyPosition, mem_maximalMultiplier_graph_iff, weakDerivative_fourier]
  have heq : l2Fourier 1 (Complex.I • g) = Complex.I • l2Fourier 1 g := map_smul _ _ _
  rw [heq]
  constructor
  · intro h
    filter_upwards [h, Lp.coeFn_smul Complex.I (l2Fourier 1 g)] with ξ hξ hsmul
    rw [hsmul]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hξ]
    push_cast
    ring
  · intro h
    filter_upwards [h, Lp.coeFn_smul Complex.I (l2Fourier 1 g)] with ξ hξ hsmul
    rw [hsmul] at hξ
    simp only [Pi.smul_apply, smul_eq_mul] at hξ
    apply mul_left_cancel₀ (a := Complex.I) Complex.I_ne_zero
    rw [hξ]
    push_cast
    ring

theorem momentum_domain : Spec.MomentumDomain := by
  intro f
  constructor
  · intro hf
    exact ⟨Complex.I • momentum ⟨f, hf⟩, (weak_graph f _).mp (momentum.mem_graph ⟨f, hf⟩)⟩
  · rintro ⟨g, hg⟩
    have hi : Complex.I • ((-Complex.I) • g) = g := by
      rw [smul_smul]
      simp
    have hgraph := (weak_graph f ((-Complex.I) • g)).mpr (by rwa [hi])
    obtain ⟨v, hv, _⟩ := momentum.mem_graph_iff.mp hgraph
    simpa only [hv] using v.2

theorem momentum_apply : Spec.MomentumApply := by
  intro f g hg
  have hi : Complex.I • ((-Complex.I) • g) = g := by rw [smul_smul]; simp
  have hgraph := (weak_graph (f : H) ((-Complex.I) • g)).mpr (by rwa [hi])
  obtain ⟨v, hv, hvg⟩ := momentum.mem_graph_iff.mp hgraph
  have heq : v = f := Subtype.ext hv
  rwa [heq] at hvg

theorem schwartz_weakDerivative (φ : S) :
    HasWeakDerivative (φ.toLp 2 volume)
      ((LineDeriv.lineDerivOpCLM ℂ S (basisVector (d := 1) 0) φ).toLp 2 volume) := by
  rw [weakDerivative_iff_tempered]
  rw [Lp.toTemperedDistribution_toLp_eq,
    Lp.toTemperedDistribution_toLp_eq]
  have h := (TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq
    (μ := volume) φ (basisVector 0)).symm
  ext ψ
  have hh := congrArg (fun T : TemperedDistribution (Euclidean 1) ℂ => T ψ) h
  change _ = -((SchwartzMap.toTemperedDistributionCLM (Euclidean 1) ℂ volume) φ
    (LineDeriv.lineDerivOpCLM ℂ S (basisVector (d := 1) 0) ψ))
  simpa only [TemperedDistribution.lineDerivOp_apply_apply, LineDeriv.lineDerivOpCLM_apply, map_neg] using hh

theorem invariance : Spec.Invariance := by
  intro φ
  constructor
  · change (φ.toLp 2 volume, (schwartzPosition φ).toLp 2 volume) ∈
      (maximalMultiplier volume 2 (fun x : Euclidean 1 => (x 0 : ℂ))).graph
    rw [mem_maximalMultiplier_graph_iff]
    filter_upwards [(schwartzPosition φ).coeFn_toLp 2 volume, φ.coeFn_toLp 2 volume]
      with x hx hφ
    rw [hx, hφ]
    exact SchwartzMap.smulLeftCLM_apply_apply (F := ℂ) (coordinate_growth (𝕜 := ℂ) (d := 1) 0) φ x
  · rw [weak_graph]
    have hm : (schwartzMomentum φ).toLp 2 volume =
        (-Complex.I) • ((LineDeriv.lineDerivOpCLM ℂ S (basisVector (d := 1) 0) φ).toLp 2 volume) :=
      (SchwartzMap.toLpCLM ℂ ℂ (E := Euclidean 1) 2 volume).map_smul _ _
    rw [hm, smul_smul]
    simpa using schwartz_weakDerivative φ

theorem h1_iff_sobolev (f : H) : H1 f ↔ ∃ v : IntegerSobolev 1 1,
    v.val (zeroIndex 1 1) = euclideanToDomainL2 1 f := by
  rw [sobolev_membership]
  constructor
  · rintro ⟨g, hg⟩ α hα
    change lpDistribution (euclideanToDomainL2 1 g) =
      Distributions.distributionDerivative ℂ 1 ⊤ [0]
        (lpDistribution (euclideanToDomainL2 1 f)) at hg
    have ha : α 0 ≤ 1 := by simpa using hα
    have he : α = fun _ => α 0 := by ext i; exact congrArg α (Subsingleton.elim i 0)
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with ha | ha
    · refine ⟨euclideanToDomainL2 1 f, ?_⟩
      rw [he]
      simp [ha, Specs.ExpandedFA.Distributions.DistributionCalculus.multiIndexDerivativeValue,
        Specs.ExpandedFA.Distributions.DistributionCalculus.derivativeValue,
        Distributions.multiIndexWord, Distributions.testPartialCLM]
    · refine ⟨euclideanToDomainL2 1 g, ?_⟩
      rw [he]
      simpa [ha, Distributions.distributionDerivative, Specs.ExpandedFA.Distributions.DistributionCalculus.multiIndexDerivativeValue,
        Distributions.multiIndexWord] using hg
  · intro h
    obtain ⟨g, hg⟩ := h (fun _ => 1) (by simp)
    refine ⟨domainToEuclideanL2 1 g, ?_⟩
    change lpDistribution (euclideanToDomainL2 1 (domainToEuclideanL2 1 g)) =
      Distributions.distributionDerivative ℂ 1 ⊤ [0]
        (lpDistribution (euclideanToDomainL2 1 f))
    rw [euclideanToDomainL2_rightInverse]
    simpa [Distributions.distributionDerivative, Specs.ExpandedFA.Distributions.DistributionCalculus.multiIndexDerivativeValue,
      Distributions.multiIndexWord] using hg

/-- The graph of momentum parametrized continuously by the actual H¹ norm. -/
def momentumGraphMap : Hs 1 (1 : ℕ) →L[ℂ] H × H :=
  (underlyingL2 1 (1 : ℕ) (by norm_num)).prod
    ((-Complex.I) • derivativeL2CLM (fun _ : Fin 1 => 1) (m := 1) (by simp))

theorem momentumGraphMap_mem (u : Hs 1 (1 : ℕ)) : momentumGraphMap u ∈ momentum.graph := by
  rw [weak_graph]
  change HasWeakDerivative (underlyingL2 1 (1 : ℕ) (by norm_num) u)
    (Complex.I • ((-Complex.I) • derivativeL2CLM (fun _ : Fin 1 => 1) (m := 1) (by simp) u))
  simp only [smul_smul, mul_neg, Complex.I_mul_I, neg_neg, one_smul]
  rw [weakDerivative_fourier]
  have hd := derivativeL2CLM_fourier_coe (fun _ : Fin 1 => 1) (m := 1) (by simp) u
  have hf : l2Fourier 1 (underlyingL2 1 (1 : ℕ) (by norm_num) u) = fourierDensityL2 (by norm_num : (0:ℝ) ≤ (1 : ℕ)) u :=
    (l2Fourier 1).apply_symm_apply _
  rw [hf]
  filter_upwards [hd, fourierDensityL2_coe (by norm_num : (0:ℝ) ≤ (1 : ℕ)) u] with ξ hξ hφ
  rw [hφ]
  simp only [derivativeSymbol, Fin.prod_univ_one, pow_one] at hξ
  exact hξ

theorem momentumGraphMap_surjective (f g : H) (hfg : (f, g) ∈ momentum.graph) :
    ∃ u : Hs 1 (1 : ℕ), momentumGraphMap u = (f, g) := by
  have hf : f ∈ momentum.domain := by
    obtain ⟨v, hv, _⟩ := momentum.mem_graph_iff.mp hfg
    simpa only [hv] using v.2
  obtain ⟨v, hv⟩ := (h1_iff_sobolev f).mp ((momentum_domain f).mp hf)
  obtain ⟨u, rfl⟩ := integerEmbedding_surjective 1 1 v
  refine ⟨u, ?_⟩
  have hu : underlyingL2 1 (1 : ℕ) (by norm_num) u = f := by
    apply (euclideanToDomainL2 1).injective
    rw [← hv, integerEmbedding_zero]
  have hmap := momentumGraphMap_mem u
  change (underlyingL2 1 (1 : ℕ) (by norm_num) u, _) ∈ momentum.graph at hmap
  rw [hu] at hmap
  have hg : (momentumGraphMap u).2 = g :=
    momentum.mem_graph_snd_inj hmap hfg rfl
  exact Prod.ext hu hg

theorem underlyingL2_of_schwartz (u : Hs 1 (1 : ℕ)) (φ : S)
    (h : realization u = schwartzRegularDistribution φ) :
    underlyingL2 1 (1 : ℕ) (by norm_num) u = φ.toLp 2 volume := by
  apply (LinearMap.ker_eq_bot.mp
    (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ)
      (μ := (volume : Measure (Euclidean 1))) (p := 2)))
  change Lp.toTemperedDistribution _ = Lp.toTemperedDistribution _
  rw [← realization_underlyingL2 (by norm_num), h]
  ext ψ
  rw [Inversion.regular_distribution_pairing, Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [φ.coeFn_toLp 2 volume] with x hx
  simp only [hx, smul_eq_mul, mul_comm]

theorem schwartz_le_momentum : schwartzSubmodule ≤ momentum.domain := by
  rintro f ⟨φ, rfl⟩
  obtain ⟨v, hv, _⟩ := momentum.mem_graph_iff.mp (invariance φ).2
  change φ.toLp 2 volume ∈ _
  simpa only [hv] using v.2

theorem schwartz_le_position : schwartzSubmodule ≤ position.domain := by
  rintro f ⟨φ, rfl⟩
  obtain ⟨v, hv, _⟩ := position.mem_graph_iff.mp (invariance φ).1
  change φ.toLp 2 volume ∈ _
  simpa only [hv] using v.2

theorem mem_restricted_graph {A : Operator ℂ H H} {f g : H}
    (hf : f ∈ schwartzSubmodule) (hfg : (f, g) ∈ A.graph) :
    (f, g) ∈ (A.domRestrict schwartzSubmodule).graph := by
  obtain ⟨v, hv, hvg⟩ := A.mem_graph_iff.mp hfg
  refine (A.domRestrict schwartzSubmodule).mem_graph_iff.mpr
    ⟨⟨v, ⟨hv.symm ▸ hf, v.2⟩⟩, hv, ?_⟩
  exact hvg

theorem momentum_core : OperatorDomainsSpec.coreValue momentum schwartzSubmodule := by
  refine ⟨schwartz_le_momentum, le_antisymm
    (Submodule.topologicalClosure_mono (LinearPMap.le_graph_of_le LinearPMap.domRestrict_le)) ?_⟩
  apply momentum.graph.topologicalClosure_minimal
    (t := (momentum.domRestrict schwartzSubmodule).graph.topologicalClosure)
    (ht := Submodule.isClosed_topologicalClosure _)
  intro z hz
  obtain ⟨u, hu⟩ := momentumGraphMap_surjective z.1 z.2 hz
  have hd := schwartz_dense 1 (1 : ℕ) u
  have ht := mem_closure_image momentumGraphMap.continuous.continuousAt hd
  rw [hu] at ht
  apply closure_mono (t := ((momentum.domRestrict schwartzSubmodule).graph : Set (H × H))) ?_ ht
  rintro _ ⟨v, ⟨φ, hφ⟩, rfl⟩
  apply mem_restricted_graph _ (momentumGraphMap_mem v)
  change underlyingL2 1 (1 : ℕ) (by norm_num) v ∈ schwartzSubmodule
  rw [underlyingL2_of_schwartz v φ hφ]
  exact ⟨φ, rfl⟩

theorem frequencyPosition_graph (f g : H) :
    (f, g) ∈ frequencyPosition.graph ↔
      (f, (2 * (Real.pi : ℂ))⁻¹ • g) ∈ position.graph := by
  have hc : 2 * (Real.pi : ℂ) ≠ 0 := mul_ne_zero (by norm_num)
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  rw [frequencyPosition, position, canonicalPosition, mem_maximalMultiplier_graph_iff,
    mem_maximalMultiplier_graph_iff]
  constructor
  · intro h
    filter_upwards [h, Lp.coeFn_smul ((2 * (Real.pi : ℂ))⁻¹) g] with x hx hg
    rw [hg]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hx]
    push_cast
    field_simp
  · intro h
    filter_upwards [h, Lp.coeFn_smul ((2 * (Real.pi : ℂ))⁻¹) g] with x hx hg
    rw [hg] at hx
    simp only [Pi.smul_apply, smul_eq_mul] at hx
    apply mul_left_cancel₀ (a := (2 * (Real.pi : ℂ))⁻¹) (inv_ne_zero hc)
    rw [hx]
    push_cast
    field_simp

/-- Fourier transformation of the momentum graph, with the exact 2π factor. -/
def positionGraphTransform : H × H →L[ℂ] H × H :=
  (l2Fourier 1).toContinuousLinearEquiv.toContinuousLinearMap.prodMap
    ((2 * (Real.pi : ℂ))⁻¹ • (l2Fourier 1).toContinuousLinearEquiv.toContinuousLinearMap)

theorem positionGraphTransform_mem {z : H × H} (hz : z ∈ momentum.graph) :
    positionGraphTransform z ∈ position.graph :=
  (frequencyPosition_graph _ _).mp ((unitaryPullback_graph _ _ _ _).mp hz)

theorem positionGraphTransform_surjective (f g : H) (hfg : (f, g) ∈ position.graph) :
    ∃ z ∈ momentum.graph, positionGraphTransform z = (f, g) := by
  let z : H × H := ((l2Fourier 1).symm f, (l2Fourier 1).symm ((2 * (Real.pi : ℂ)) • g))
  have hc : 2 * (Real.pi : ℂ) ≠ 0 := mul_ne_zero (by norm_num)
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hz : positionGraphTransform z = (f, g) := by
    change (l2Fourier 1 ((l2Fourier 1).symm f),
      (2 * (Real.pi : ℂ))⁻¹ • l2Fourier 1 ((l2Fourier 1).symm ((2 * (Real.pi : ℂ)) • g))) = _
    simp only [LinearIsometryEquiv.apply_symm_apply, smul_smul, inv_mul_cancel₀ hc, one_smul]
  refine ⟨z, ?_, hz⟩
  apply (unitaryPullback_graph (l2Fourier 1) frequencyPosition _ _).mpr
  apply (frequencyPosition_graph _ _).mpr
  change positionGraphTransform z ∈ position.graph
  rw [hz]
  exact hfg

theorem position_core : OperatorDomainsSpec.coreValue position schwartzSubmodule := by
  refine ⟨schwartz_le_position, le_antisymm
    (Submodule.topologicalClosure_mono (LinearPMap.le_graph_of_le LinearPMap.domRestrict_le)) ?_⟩
  apply position.graph.topologicalClosure_minimal
    (t := (position.domRestrict schwartzSubmodule).graph.topologicalClosure)
    (ht := Submodule.isClosed_topologicalClosure _)
  intro z hz
  obtain ⟨v, hv, hvz⟩ := positionGraphTransform_surjective z.1 z.2 hz
  have hvcl : v ∈ closure ((momentum.domRestrict schwartzSubmodule).graph : Set (H × H)) := by
    change v ∈ (momentum.domRestrict schwartzSubmodule).graph.topologicalClosure
    rw [momentum_core.2]
    exact momentum.graph.le_topologicalClosure hv
  have ht := mem_closure_image positionGraphTransform.continuous.continuousAt hvcl
  rw [hvz] at ht
  apply closure_mono (t := ((position.domRestrict schwartzSubmodule).graph : Set (H × H))) ?_ ht
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨f, hf, hfg⟩ := (momentum.domRestrict schwartzSubmodule).mem_graph_iff.mp hw
  apply mem_restricted_graph _
    (positionGraphTransform_mem (LinearPMap.le_graph_of_le LinearPMap.domRestrict_le hw))
  have hfirst : w.1 ∈ schwartzSubmodule := hf ▸ f.2.1
  obtain ⟨φ, hφ⟩ := hfirst
  change l2Fourier 1 w.1 ∈ schwartzSubmodule
  change φ.toLp 2 volume = w.1 at hφ
  rw [← hφ, Plancherel.extension]
  exact ⟨schwartzFourier φ, rfl⟩

theorem cores : Spec.Cores := ⟨position_core, momentum_core⟩

def schwartzMultiplier (χ : S) : H →L[ℂ] H :=
  multiplierL2CLM χ χ.hasTemperateGrowth (χ.norm_le_seminorm ℂ)

theorem schwartzMultiplier_coe (χ : S) (f : H) :
    schwartzMultiplier χ f =ᵐ[volume] fun x => χ x * f x :=
  multiplierL2_coe χ χ.hasTemperateGrowth (χ.norm_le_seminorm ℂ) f

theorem l2_norm_sq (f : H) : ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  have h : RCLike.re (inner ℂ f f) = ∫ x, ‖f x‖ ^ 2 := by
    rw [L2.inner_def, ← integral_re (𝕜 := ℂ) (L2.integrable_inner (𝕜 := ℂ) f f)]
    simp only [inner_self_eq_norm_sq]
  simpa only [inner_self_eq_norm_sq] using h

/-- Bounded pointwise convergence of symbols gives strong L² convergence. -/
theorem schwartzMultiplier_tendsto (χ : ℕ → S) (a : ℂ) (C : ℝ)
    (hC : 0 ≤ C) (hb : ∀ n x, ‖χ n x‖ ≤ C)
    (ha : ∀ x, Tendsto (fun n => χ n x) atTop (𝓝 a)) (f : H) :
    Tendsto (fun n => schwartzMultiplier (χ n) f) atTop (𝓝 (a • f)) := by
  have hcoe n : (schwartzMultiplier (χ n) f - a • f : H) =ᵐ[volume]
      fun x => (χ n x - a) * f x := by
    filter_upwards [Lp.coeFn_sub (schwartzMultiplier (χ n) f) (a • f),
      schwartzMultiplier_coe (χ n) f, Lp.coeFn_smul a f] with x hx hy hz
    simp only [hx, Pi.sub_apply, hy, hz, Pi.smul_apply, smul_eq_mul, sub_mul]
  have hi : Tendsto (fun n => ∫ x, ‖(χ n x - a) * f x‖ ^ 2) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence
      (F := fun n x => ‖(χ n x - a) * f x‖ ^ 2) (f := fun _ => (0 : ℝ))
      (fun x => (C + ‖a‖) ^ 2 * ‖f x‖ ^ 2)
      (fun n => (((χ n).continuous.aestronglyMeasurable.sub aestronglyMeasurable_const).mul
        (Lp.aestronglyMeasurable f)).norm.pow 2)
      (((Lp.memLp f).integrable_norm_pow (by norm_num)).const_mul ((C + ‖a‖) ^ 2))
      (fun n => Eventually.of_forall fun x => by
        change ‖‖(χ n x - a) * f x‖ ^ 2‖ ≤ _
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_mul, mul_pow]
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        exact pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le (χ n x) a).trans (add_le_add (hb n x) (le_refl ‖a‖))) 2)
      (Eventually.of_forall fun x => by
        have h := (((ha x).sub_const a).mul_const (f x)).norm.pow 2
        simpa using h)
    simpa using h
  have hn : Tendsto (fun n => ‖schwartzMultiplier (χ n) f - a • f‖ ^ 2) atTop (𝓝 0) := by
    convert hi using 1
    ext n
    rw [l2_norm_sq]
    exact integral_congr_ae ((hcoe n).fun_comp (fun z : ℂ => ‖z‖ ^ 2))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hn
  change Tendsto (fun n => Real.sqrt (‖schwartzMultiplier (χ n) f - a • f‖ ^ 2))
    atTop (𝓝 (Real.sqrt 0)) at hs
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hs

def dilation (n : ℕ) : Euclidean 1 ≃L[ℝ] Euclidean 1 where
  __ := LinearEquiv.smulOfNeZero ℝ (Euclidean 1) ((n : ℝ) + 1)⁻¹ (by positivity)
  continuous_toFun := by
    change Continuous (fun x : Euclidean 1 => ((n : ℝ) + 1)⁻¹ • x)
    fun_prop
  continuous_invFun := by
    change Continuous (fun x : Euclidean 1 => (((n : ℝ) + 1)⁻¹)⁻¹ • x)
    fun_prop

def scaledCutoff (χ : S) (n : ℕ) : S :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (dilation n) χ

@[simp] theorem scaledCutoff_apply (χ : S) (n : ℕ) (x : Euclidean 1) :
    scaledCutoff χ n x = χ (((n : ℝ) + 1)⁻¹ • x) := rfl

theorem scaledCutoff_bound (χ : S) (n : ℕ) (x : Euclidean 1) :
    ‖scaledCutoff χ n x‖ ≤ SchwartzMap.seminorm ℂ 0 0 χ := χ.norm_le_seminorm ℂ _

theorem scaledCutoff_pointwise (χ : S) (hχ : ∀ x, ‖x‖ ≤ 1 → χ x = 1) (x : Euclidean 1) :
    Tendsto (fun n => scaledCutoff χ n x) atTop (𝓝 1) := by
  have ht : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹ • x) atTop (𝓝 0) := by
    have hn : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp ((tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop))
    simpa using hn.smul_const x
  have h0 : χ 0 = 1 := hχ 0 (by simp)
  have h := χ.continuous.continuousAt.tendsto.comp ht
  change Tendsto (fun n : ℕ => χ (((n : ℝ) + 1)⁻¹ • x)) atTop (𝓝 (χ 0)) at h
  simpa only [scaledCutoff_apply, h0] using h

def schwartzProduct (χ φ : S) : S := SchwartzMap.smulLeftCLM ℂ χ φ

@[simp] theorem schwartzProduct_apply (χ φ : S) (x : Euclidean 1) :
    schwartzProduct χ φ x = χ x * φ x :=
  SchwartzMap.smulLeftCLM_apply_apply χ.hasTemperateGrowth φ x

theorem schwartzMomentum_apply (φ : S) (x : Euclidean 1) :
    schwartzMomentum φ x = -Complex.I * fderiv ℝ φ x (basisVector (d := 1) 0) := rfl

@[simp] theorem schwartzPosition_apply (φ : S) (x : Euclidean 1) :
    schwartzPosition φ x = (x 0 : ℂ) * φ x :=
  SchwartzMap.smulLeftCLM_apply_apply (coordinate_growth (𝕜 := ℂ) (d := 1) 0) φ x

theorem schwartzMomentum_product (χ φ : S) (x : Euclidean 1) :
    schwartzMomentum (schwartzProduct χ φ) x =
      χ x * schwartzMomentum φ x + schwartzMomentum χ x * φ x := by
  simp only [schwartzMomentum_apply]
  have heq : (schwartzProduct χ φ : Euclidean 1 → ℂ) = fun x => χ x * φ x :=
    funext (schwartzProduct_apply χ φ)
  have hf := fderiv_mul (𝕜 := ℝ) (c := (χ : Euclidean 1 → ℂ)) (d := (φ : Euclidean 1 → ℂ))
    (x := x) χ.differentiableAt φ.differentiableAt
  change fderiv ℝ (fun x => χ x * φ x) x = _ at hf
  rw [heq, hf]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem schwartzMomentum_scaledCutoff (χ : S) (n : ℕ) (x : Euclidean 1) :
    schwartzMomentum (scaledCutoff χ n) x =
      Complex.ofReal (((n : ℝ) + 1)⁻¹) * schwartzMomentum χ (((n : ℝ) + 1)⁻¹ • x) := by
  rw [schwartzMomentum_apply, schwartzMomentum_apply]
  change -Complex.I * fderiv ℝ (χ ∘ dilation n) x (basisVector (d := 1) 0) = _
  rw [fderiv_comp x χ.differentiableAt (dilation n).differentiableAt,
    ContinuousLinearEquiv.fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  change -Complex.I * fderiv ℝ χ (((n : ℝ) + 1)⁻¹ • x)
    (((n : ℝ) + 1)⁻¹ • basisVector (d := 1) 0) = _
  rw [map_smul]
  simp only [Complex.real_smul]
  ring

theorem scaledCutoff_momentum_bound (χ : S) (n : ℕ) (x : Euclidean 1) :
    ‖schwartzMomentum (scaledCutoff χ n) x‖ ≤
      SchwartzMap.seminorm ℂ 0 0 (schwartzMomentum χ) := by
  rw [schwartzMomentum_scaledCutoff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < ((n : ℝ) + 1)⁻¹)]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    ((inv_le_one₀ (by positivity : 0 < (n : ℝ) + 1)).mpr (by have := Nat.cast_nonneg (α := ℝ) n; linarith))).trans
      ((schwartzMomentum χ).norm_le_seminorm ℂ _)

theorem scaledCutoff_momentum_pointwise (χ : S) (x : Euclidean 1) :
    Tendsto (fun n => schwartzMomentum (scaledCutoff χ n) x) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have harg := hn.smul_const x
  have hval := (schwartzMomentum χ).continuous.continuousAt.tendsto.comp harg
  have hc := (Complex.continuous_ofReal.continuousAt.tendsto.comp hn).mul hval
  simpa only [Function.comp_apply, scaledCutoff_apply, schwartzMomentum_scaledCutoff, Complex.ofReal_zero,
    zero_smul, zero_mul] using hc

def jointSchwartzGraph (φ : S) : H × H × H :=
  (φ.toLp 2 volume, (schwartzPosition φ).toLp 2 volume, (schwartzMomentum φ).toLp 2 volume)

def cutoffGraphMap (χ : S) : H × H →L[ℂ] H × H × H :=
  ((schwartzMultiplier χ).comp (ContinuousLinearMap.fst ℂ H H)).prod
    (((schwartzMultiplier (schwartzPosition χ)).comp (ContinuousLinearMap.fst ℂ H H)).prod
      ((schwartzMultiplier χ).comp (ContinuousLinearMap.snd ℂ H H) +
        (schwartzMultiplier (schwartzMomentum χ)).comp (ContinuousLinearMap.fst ℂ H H)))

theorem cutoffGraphMap_schwartz (χ φ : S) :
    cutoffGraphMap χ (φ.toLp 2 volume, (schwartzMomentum φ).toLp 2 volume) =
      jointSchwartzGraph (schwartzProduct χ φ) := by
  apply Prod.ext
  · apply Lp.ext
    filter_upwards [schwartzMultiplier_coe χ (φ.toLp 2 volume), φ.coeFn_toLp 2 volume,
      (schwartzProduct χ φ).coeFn_toLp 2 volume] with x hx hφ hp
    change schwartzMultiplier χ (φ.toLp 2 volume) x = (schwartzProduct χ φ).toLp 2 volume x
    rw [hx, hφ, hp, schwartzProduct_apply]
  · apply Prod.ext
    · apply Lp.ext
      filter_upwards [schwartzMultiplier_coe (schwartzPosition χ) (φ.toLp 2 volume),
        φ.coeFn_toLp 2 volume, (schwartzPosition (schwartzProduct χ φ)).coeFn_toLp 2 volume]
        with x hx hφ hp
      change schwartzMultiplier (schwartzPosition χ) (φ.toLp 2 volume) x =
        (schwartzPosition (schwartzProduct χ φ)).toLp 2 volume x
      rw [hx, hφ, hp]
      simp only [schwartzPosition_apply, schwartzProduct_apply, mul_assoc]
    · apply Lp.ext
      filter_upwards [Lp.coeFn_add
          (schwartzMultiplier χ ((schwartzMomentum φ).toLp 2 volume))
          (schwartzMultiplier (schwartzMomentum χ) (φ.toLp 2 volume)),
        schwartzMultiplier_coe χ ((schwartzMomentum φ).toLp 2 volume),
        schwartzMultiplier_coe (schwartzMomentum χ) (φ.toLp 2 volume),
        φ.coeFn_toLp 2 volume, (schwartzMomentum φ).coeFn_toLp 2 volume,
        (schwartzMomentum (schwartzProduct χ φ)).coeFn_toLp 2 volume]
        with x hadd h₁ h₂ hφ hp hprod
      change (schwartzMultiplier χ ((schwartzMomentum φ).toLp 2 volume) +
        schwartzMultiplier (schwartzMomentum χ) (φ.toLp 2 volume) : H) x =
        (schwartzMomentum (schwartzProduct χ φ)).toLp 2 volume x
      rw [hadd]
      simp only [Pi.add_apply, h₁, h₂, hφ, hp, hprod, schwartzMomentum_product]

theorem cutoffGraphMap_mem_closure (χ : S) (f p : H) (hfp : (f, p) ∈ momentum.graph) :
    cutoffGraphMap χ (f, p) ∈ closure (Set.range jointSchwartzGraph) := by
  have hcl : (f, p) ∈ closure ((momentum.domRestrict schwartzSubmodule).graph : Set (H × H)) := by
    change (f, p) ∈ (momentum.domRestrict schwartzSubmodule).graph.topologicalClosure
    rw [momentum_core.2]
    exact momentum.graph.le_topologicalClosure hfp
  have ht := mem_closure_image (cutoffGraphMap χ).continuous.continuousAt hcl
  apply closure_mono ?_ ht
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨v, hv, hvp⟩ := (momentum.domRestrict schwartzSubmodule).mem_graph_iff.mp hw
  obtain ⟨φ, hφ⟩ := hv ▸ v.2.1
  change φ.toLp 2 volume = w.1 at hφ
  have hp : (schwartzMomentum φ).toLp 2 volume = w.2 :=
    momentum.mem_graph_snd_inj (invariance φ).2
      (LinearPMap.le_graph_of_le LinearPMap.domRestrict_le hw) hφ
  refine ⟨schwartzProduct χ φ, ?_⟩
  have hw : w = (φ.toLp 2 volume, (schwartzMomentum φ).toLp 2 volume) :=
    Prod.ext hφ.symm hp.symm
  rw [hw, cutoffGraphMap_schwartz]

theorem jointGraph_mem_closure (f : H) (hq : f ∈ position.domain) (hp : f ∈ momentum.domain) :
    (f, position ⟨f, hq⟩, momentum ⟨f, hp⟩) ∈ closure (Set.range jointSchwartzGraph) := by
  obtain ⟨χ, hχsupp, hχ⟩ := exists_schwartz_cutoff 1
  let χn := scaledCutoff χ
  have hstrong (g : H) : Tendsto (fun n => schwartzMultiplier (χn n) g) atTop (𝓝 g) := by
    have h := schwartzMultiplier_tendsto χn 1 (SchwartzMap.seminorm ℂ 0 0 χ)
      (apply_nonneg _ _) (scaledCutoff_bound χ) (scaledCutoff_pointwise χ hχ) g
    simpa only [one_smul] using h
  have hderiv : Tendsto (fun n => schwartzMultiplier (schwartzMomentum (χn n)) f)
      atTop (𝓝 0) := by
    have h := schwartzMultiplier_tendsto (fun n => schwartzMomentum (χn n)) 0
      (SchwartzMap.seminorm ℂ 0 0 (schwartzMomentum χ)) (apply_nonneg _ _)
      (scaledCutoff_momentum_bound χ) (scaledCutoff_momentum_pointwise χ) f
    simpa only [zero_smul] using h
  have hcomm (n : ℕ) : schwartzMultiplier (schwartzPosition (χn n)) f =
      schwartzMultiplier (χn n) (position ⟨f, hq⟩) := by
    apply Lp.ext
    filter_upwards [schwartzMultiplier_coe (schwartzPosition (χn n)) f,
      schwartzMultiplier_coe (χn n) (position ⟨f, hq⟩), position_apply ⟨f, hq⟩]
      with x hx hy hz
    rw [hx, hy, hz]
    simp only [schwartzPosition_apply]
    ring
  have hlim : Tendsto (fun n => cutoffGraphMap (χn n) (f, momentum ⟨f, hp⟩)) atTop
      (𝓝 (f, position ⟨f, hq⟩, momentum ⟨f, hp⟩)) := by
    have hqconv : Tendsto (fun n => schwartzMultiplier (schwartzPosition (χn n)) f)
        atTop (𝓝 (position ⟨f, hq⟩)) := by
      simpa only [hcomm] using hstrong (position ⟨f, hq⟩)
    have hpconv := (hstrong (momentum ⟨f, hp⟩)).add hderiv
    simpa [cutoffGraphMap] using (hstrong f).prodMk_nhds (hqconv.prodMk_nhds hpconv)
  exact isClosed_closure.mem_of_tendsto hlim (Eventually.of_forall fun n =>
    cutoffGraphMap_mem_closure (χn n) f (momentum ⟨f, hp⟩) (momentum.mem_graph ⟨f, hp⟩))

theorem joint_core : Spec.JointCore := by
  intro f hq hp ε hε
  have hcl := jointGraph_mem_closure f hq hp
  obtain ⟨z, ⟨φ, rfl⟩, hz⟩ := Metric.mem_closure_iff.mp hcl (ε / 3) (by positivity)
  refine ⟨φ, ?_⟩
  let t : H × H × H := (f, position ⟨f, hq⟩, momentum ⟨f, hp⟩)
  have h₀ : dist (jointSchwartzGraph φ).1 t.1 ≤ dist (jointSchwartzGraph φ) t := by
    rw [Prod.dist_eq]
    exact le_max_left _ _
  have hs : dist (jointSchwartzGraph φ).2 t.2 ≤ dist (jointSchwartzGraph φ) t := by
    rw [Prod.dist_eq]
    exact le_max_right _ _
  have h₁ : dist (jointSchwartzGraph φ).2.1 t.2.1 ≤ dist (jointSchwartzGraph φ) t := by
    apply le_trans ?_ hs
    rw [Prod.dist_eq]
    exact le_max_left _ _
  have h₂ : dist (jointSchwartzGraph φ).2.2 t.2.2 ≤ dist (jointSchwartzGraph φ) t := by
    apply le_trans ?_ hs
    rw [Prod.dist_eq]
    exact le_max_right _ _
  change ‖φ.toLp 2 volume - f‖ +
    ‖(schwartzPosition φ).toLp 2 volume - position ⟨f, hq⟩‖ +
    ‖(schwartzMomentum φ).toLp 2 volume - momentum ⟨f, hp⟩‖ < ε
  have ht : dist (jointSchwartzGraph φ) t < ε / 3 := by simpa [t, dist_comm] using hz
  simp only [jointSchwartzGraph, t, dist_eq_norm] at h₀ h₁ h₂ ht
  linarith

end ExpandedFA.Models.PositionMomentum
