import MathGenome.Internal.FourierSobolev.Specs.P102.U4.ZeroDimension
import MathGenome.Internal.FourierSobolev.P102.U4.SchwartzRestriction
import MathGenome.Internal.FourierSobolev.P102.U4.LocalOrder
import MathGenome.Internal.FourierSobolev.P102.U4.DistributionSupport
import MathGenome.Internal.FourierSobolev.P102.U4.LocalConvolution
import MathGenome.Internal.FourierSobolev.P102.U4.ZeroExtension
import MathGenome.Internal.FourierSobolev.P102.U4.NegativeSobolev
import MathGenome.Internal.FourierSobolev.P102.U4.DistributionConvolution

noncomputable section
open Set TopologicalSpace MeasureTheory Filter Classical
open scoped ContDiff Distributions ENNReal Topology
namespace P102.U4
namespace ZeroDimensionProof
open ZeroDimensionData

variable {𝕜 : Type} [RCLike 𝕜]

lemma point_eq (x : Space 0) : x = 0 := Subsingleton.elim _ _

lemma multiIndex_eq (α : MultiIndex 0) : α = 0 := by
  apply Multiset.eq_zero_iff_forall_notMem.mpr
  intro i
  exact Fin.elim0 i

lemma opens_cases (Ω : Opens (Space 0)) : Ω = ⊥ ∨ Ω = ⊤ := by
  by_cases h : (0 : Space 0) ∈ Ω
  · right
    ext x
    simp [point_eq x, h]
  · left
    ext x
    simp [point_eq x, h]

lemma opens_top (Ω : Opens (Space 0)) (h : (0 : Space 0) ∈ Ω) : Ω = ⊤ := by
  rcases opens_cases Ω with h' | h'
  · simp [h'] at h
  · exact h'

lemma volume_eq : (volume : Measure (Space 0)) = Measure.dirac 0 :=
  volume_euclideanSpace_eq_dirac (Fin 0)

lemma integral_eq (f : Space 0 → 𝕜) : (∫ x, f x) = f 0 := by
  rw [volume_eq, integral_dirac]

omit [RCLike 𝕜] in
lemma function_const (f : Space 0 → 𝕜) : f = fun _ => f 0 := by
  funext x
  rw [point_eq x]

lemma smooth_compact (f : Space 0 → 𝕜) :
    ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f := by
  constructor
  · rw [function_const f]
    exact contDiff_const
  · exact isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _)

lemma test_smul_one (Ω : Opens (Space 0)) (hΩ : (0 : Space 0) ∈ Ω)
    (φ : TestSpace 𝕜 Ω) : φ = φ 0 • constantTest 𝕜 Ω hΩ 1 := by
  ext x
  change φ x = φ 0 * 1
  rw [point_eq x, mul_one]

def stageEquiv (K : Compacts (Space 0)) (hK : (0 : Space 0) ∈ K) :
    FixedSupport 0 𝕜 K ≃L[𝕜] 𝕜 where
  toFun φ := φ 0
  invFun := constantStage 𝕜 K hK
  left_inv φ := by ext x; exact congrArg φ (point_eq x).symm
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := continuous_eval_const 0
  continuous_invFun := by
    have h : (constantStage 𝕜 K hK : 𝕜 → FixedSupport 0 𝕜 K) =
        fun c => c • constantStage 𝕜 K hK 1 := by
      funext c
      ext x
      change c = c * 1
      exact (mul_one c).symm
    rw [h]
    exact continuous_id.smul continuous_const

def testEquiv (Ω : Opens (Space 0)) (hΩ : (0 : Space 0) ∈ Ω) :
    TestSpace 𝕜 Ω ≃L[𝕜] 𝕜 where
  toFun φ := φ 0
  invFun := constantTest 𝕜 Ω hΩ
  left_inv φ := by ext x; exact congrArg φ (point_eq x).symm
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := continuous_eval_const 0
  continuous_invFun := by
    have hK : (fullCompact : Set (Space 0)) ⊆ Ω := by
      intro x _
      simpa [point_eq x] using hΩ
    have heq : (constantTest 𝕜 Ω hΩ : 𝕜 → TestSpace 𝕜 Ω) =
        (stageInclusion 𝕜 hK) ∘ (stageEquiv (𝕜 := 𝕜) fullCompact (by trivial)).symm := by
      funext c
      ext x
      rfl
    rw [heq]
    exact (stageInclusion 𝕜 hK).continuous.comp (stageEquiv fullCompact (by trivial)).symm.continuous

def schwartzEquiv : SchwartzTests 0 𝕜 ≃L[𝕜] 𝕜 where
  toFun φ := φ 0
  invFun c := testToSchwartz 0 𝕜 (constantTest 𝕜 ⊤ (by trivial) c)
  left_inv φ := by ext x; exact congrArg φ (point_eq x).symm
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := (continuous_eval_const 0 :
    Continuous (fun f : BoundedContinuousFunction (Space 0) 𝕜 => f 0)).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM 𝕜 (Space 0) 𝕜).continuous
  continuous_invFun := (testToSchwartzCLM 0 𝕜).continuous.comp
    (testEquiv (𝕜 := 𝕜) ⊤ (by trivial)).symm.continuous

lemma geometry : ZeroDimensionExpected.Geometry := by
  exact ⟨point_eq, volume_eq, by simp [volume_eq], opens_cases, multiIndex_eq, inferInstance⟩

lemma functions : ZeroDimensionExpected.Functions := by
  intro 𝕜 _
  exact ⟨smooth_compact, fun Ω hΩ => ⟨testEquiv Ω hΩ, fun _ => rfl⟩,
    fun K hK => ⟨stageEquiv K hK, fun _ => rfl⟩, ⟨schwartzEquiv, fun _ => rfl⟩⟩

lemma seminorm_eq (K : Compacts (Space 0)) (m : ℕ) (φ : FixedSupport 0 𝕜 K) :
    coordinateSupSeminorm 𝕜 K m φ = ‖φ 0‖ := by
  apply le_antisymm
  · apply (multiIndexSeminormFormula 0 𝕜 K m φ _ (norm_nonneg _)).mpr
    intro α _ x _
    rw [multiIndex_eq α, point_eq x]
    simp [multiPartial, partialWord]
  · by_cases hK : (0 : Space 0) ∈ K
    · have h := (multiIndexSeminormFormula 0 𝕜 K m φ _ (apply_nonneg _ _)).mp
        le_rfl 0 (by simp) 0 hK
      simpa [multiPartial, partialWord] using h
    · have hz : φ 0 = (0 : 𝕜) := φ.zero_on_compl hK
      rw [hz, norm_zero]
      exact apply_nonneg _ _

lemma linear_formula (Ω : Opens (Space 0)) (hΩ : (0 : Space 0) ∈ Ω)
    (T : TestSpace 𝕜 Ω →ₗ[𝕜] 𝕜) (φ : TestSpace 𝕜 Ω) :
    T φ = φ 0 * T (constantTest 𝕜 Ω hΩ 1) := by
  conv_lhs => rw [test_smul_one Ω hΩ φ]
  exact T.map_smul _ _

lemma order : ZeroDimensionExpected.Order := by
  intro 𝕜 _ Ω hΩ
  refine ⟨seminorm_eq, fun T => ⟨?_, fun φ => ⟨linear_formula Ω hΩ T φ, ?_⟩⟩⟩
  · have heq : (T : TestSpace 𝕜 Ω → 𝕜) =
        fun φ => φ 0 * T (constantTest 𝕜 Ω hΩ 1) := funext (linear_formula Ω hΩ T)
    rw [heq]
    exact (continuous_eval_const 0).mul continuous_const
  · rw [linear_formula Ω hΩ T φ, norm_mul, mul_comm]

lemma distribution_scalar (Ω : Opens (Space 0)) (a : Space 0) (ha : a ∈ Ω)
    (S : DistributionSpace 𝕜 Ω) : ∃! c : 𝕜, S = c • pointMass 𝕜 Ω a := by
  have hΩ : (0 : Space 0) ∈ Ω := by simpa only [point_eq a] using ha
  refine ⟨S (constantTest 𝕜 Ω hΩ 1), ?_, ?_⟩
  · ext φ
    change S.toLinearMap φ = _
    rw [linear_formula Ω hΩ S.toLinearMap φ]
    change φ 0 * S _ = S _ * φ a
    rw [point_eq a, mul_comm]
  · intro c hc
    have h := congrArg (fun T : DistributionSpace 𝕜 Ω => T (constantTest 𝕜 Ω hΩ 1)) hc
    change S (constantTest 𝕜 Ω hΩ 1) = c * 1 at h
    simpa only [mul_one] using h.symm

lemma regular_scalar (Ω : Opens (Space 0)) (a : Space 0) (ha : a ∈ Ω)
    (f : Space 0 → 𝕜) : regularDistribution Ω f = f a • pointMass 𝕜 Ω a := by
  have hΩ : (0 : Space 0) ∈ Ω := by simpa only [point_eq a] using ha
  have hf : LocallyIntegrableOn f Ω volume :=
    (smooth_compact f).1.continuous.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet
  ext φ
  rw [regular_pairing 0 𝕜 Ω f hf φ]
  have ht : (Ω : Set (Space 0)) = Set.univ := congrArg (fun U : Opens (Space 0) => (U : Set (Space 0))) (opens_top Ω hΩ)
  rw [ht, Measure.restrict_univ]
  rw [integral_eq]
  change f 0 * φ 0 = f a * φ a
  rw [point_eq a]

lemma support_scalar (Ω : Opens (Space 0)) (a : Space 0) (ha : a ∈ Ω)
    (S : DistributionSpace 𝕜 Ω) : relativeSupport S = if S = 0 then ∅ else {a} := by
  classical
  by_cases hS : S = 0
  · simp only [hS, ↓reduceIte]
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    apply hx.2
    apply subset_vanishingRegion (0 : DistributionSpace 𝕜 Ω) Ω.isOpen (subset_refl _) _ hx.1
    intro φ _
    rfl
  · simp only [hS, ↓reduceIte]
    ext x
    constructor
    · intro _
      exact Subsingleton.elim x a
    · intro hx
      have hxΩ : x ∈ Ω := by
        rw [Set.mem_singleton_iff.mp hx]
        exact ha
      refine ⟨hxΩ, ?_⟩
      intro hv
      obtain ⟨U, ⟨_, _, hU⟩, hxU⟩ := Set.mem_sUnion.mp hv
      apply hS
      ext φ
      apply hU φ
      intro y _
      simpa only [Subsingleton.elim y x] using hxU

lemma distribution_derivative (Ω : Opens (Space 0))
    (S : DistributionSpace 𝕜 Ω) (α : MultiIndex 0) : distributionPartial α S = S := by
  rw [multiIndex_eq α]
  exact derivative_zero 0 𝕜 Ω S

lemma bounded_index_eq (m : ℕ) (α : BoundedMultiIndex 0 m) :
    α = (⟨0, by simp⟩ : BoundedMultiIndex 0 m) := Subtype.ext (multiIndex_eq α.val)

lemma point_sum_scalar (Ω : Opens (Space 0)) (a : Space 0) (m : ℕ)
    (c : BoundedMultiIndex 0 m → 𝕜) :
    pointDerivativeSum Ω a m c = c ⟨0, by simp⟩ • pointMass 𝕜 Ω a := by
  classical
  unfold pointDerivativeSum
  rw [Finset.sum_eq_single (⟨0, by simp⟩ : BoundedMultiIndex 0 m)]
  · rw [derivative_zero]
  · intro b _ hb
    exact (hb (bounded_index_eq m b)).elim
  · simp

lemma point_unique (Ω : Opens (Space 0)) (a : Space 0) (ha : a ∈ Ω)
    (m : ℕ) (S : DistributionSpace 𝕜 Ω) :
    ∃! c : BoundedMultiIndex 0 m → 𝕜, S = pointDerivativeSum Ω a m c := by
  obtain ⟨c, hc, hcu⟩ := distribution_scalar Ω a ha S
  refine ⟨fun _ => c, ?_, ?_⟩
  · change S = pointDerivativeSum Ω a m (fun _ => c)
    rw [point_sum_scalar]
    exact hc
  · intro b hb
    have hbc := hcu (b ⟨0, by simp⟩) (hb.trans (point_sum_scalar Ω a m b))
    funext α
    rw [bounded_index_eq m α]
    exact hbc

lemma distributions : ZeroDimensionExpected.Distributions := by
  intro 𝕜 _ Ω a ha
  exact ⟨distribution_scalar Ω a ha, regular_scalar Ω a ha,
    support_scalar Ω a ha, distribution_derivative Ω,
    fun m S => point_unique Ω a ha m S⟩

lemma local_scalar (T : DistributionSpace 𝕜 (⊤ : Opens (Space 0)))
    (ρ : WholeTests 0 𝕜) (x : Space 0) :
    localConvolution T ρ x = ρ 0 * T (constantTest 𝕜 ⊤ (by trivial) 1) := by
  have hx : x ∈ convolutionDomain ⊤ ρ := by intro z hz; trivial
  rw [localConvolution_pairing 0 𝕜 ⊤ T ρ x hx]
  change T.toLinearMap _ = _
  rw [linear_formula ⊤ (by trivial) T.toLinearMap]
  change ρ (x - 0) * T _ = _
  rw [point_eq x, sub_self]

lemma convolution : ZeroDimensionExpected.Convolution := by
  intro 𝕜 _
  obtain ⟨C, hpair, _, _⟩ := distributionConvolution_construction 0 𝕜
  let hS (S : DistributionSpace 𝕜 (⊤ : Opens (Space 0))) :
      IsCompact (relativeSupport S) := (Set.toFinite _).isCompact
  refine ⟨⟨fun T S => C T S (Or.inr (hS S)), (fun T S φ => hpair T S (hS S) φ), ?_⟩, local_scalar, ?_, ?_⟩
  · intro c b
    ext φ
    obtain ⟨ψ, hψ, hCψ⟩ := hpair (c • pointMass 𝕜 ⊤ 0)
      (b • pointMass 𝕜 ⊤ 0) (hS _) φ
    rw [hCψ]
    change c * ψ 0 = (c * b) * φ 0
    rw [hψ 0]
    change c * (b * φ (0 + 0)) = (c * b) * φ 0
    simp only [add_zero]
    ring
  · intro f g x
    unfold functionConvolution
    rw [integral_eq, point_eq x, sub_self]
  · intro ρ hρ
    rw [integral_eq] at hρ
    exact (function_const ρ).trans (by rw [hρ])

lemma lp_empty (p : ℝ≥0∞) (u : DomainLp 𝕜 (⊥ : Opens (Space 0)) p) : u = 0 := by
  apply Lp.ext
  simp only [Opens.coe_bot, Measure.restrict_empty, ae_zero]
  exact Filter.eventually_bot

lemma testLp_surjective (Ω : Opens (Space 0)) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Function.Surjective (testToDomainLp (𝕜 := 𝕜) Ω p) := by
  intro u
  rcases opens_cases Ω with hΩ | hΩ
  · subst Ω
    refine ⟨0, ?_⟩
    rw [map_zero, lp_empty p u]
  · subst Ω
    refine ⟨constantTest 𝕜 ⊤ (by trivial) (u 0), ?_⟩
    apply Lp.ext
    filter_upwards [testToDomainLp_ae ⊤ p (constantTest 𝕜 ⊤ (by trivial) (u 0))] with x hx
    exact hx.trans (congrArg u (point_eq x)).symm

def scalarLpLI (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    𝕜 →ₗᵢ[𝕜] DomainLp 𝕜 (⊤ : Opens (Space 0)) p where
  toLinearMap := Lp.constₗ p (volume.restrict (↑(⊤ : Opens (Space 0)) : Set (Space 0))) 𝕜
  norm_map' c := by
    have hp : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))
    simp only [Lp.constₗ_apply, Opens.coe_top]
    rw [Lp.norm_const p _ c hp]
    simp [Measure.real, volume_eq]

lemma scalarLp_surjective (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Function.Surjective (scalarLpLI (𝕜 := 𝕜) p) := by
  intro u
  refine ⟨u 0, ?_⟩
  apply Lp.ext
  filter_upwards [Lp.coeFn_const p
    (volume.restrict (↑(⊤ : Opens (Space 0)) : Set (Space 0))) (u 0)] with x hx
  exact hx.trans (congrArg u (point_eq x)).symm

def scalarLpEquiv (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    DomainLp 𝕜 (⊤ : Opens (Space 0)) p ≃ₗᵢ[𝕜] 𝕜 :=
  (LinearIsometryEquiv.ofSurjective (scalarLpLI p) (scalarLp_surjective p)).symm

lemma scalarLpEquiv_apply (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : DomainLp 𝕜 (⊤ : Opens (Space 0)) p) : scalarLpEquiv p u = u 0 := by
  have h := (scalarLpEquiv (𝕜 := 𝕜) p).symm_apply_apply u
  have hc := Lp.coeFn_const p
    (volume.restrict (↑(⊤ : Opens (Space 0)) : Set (Space 0))) (scalarLpEquiv p u)
  have hcoe : (scalarLpLI p (scalarLpEquiv p u) : Space 0 → 𝕜) =ᵐ[
      volume.restrict (↑(⊤ : Opens (Space 0)) : Set (Space 0))] u := by
    rw [show scalarLpLI p (scalarLpEquiv p u) = u from h]
  have he : (fun _ : Space 0 => scalarLpEquiv p u) =ᵐ[
      volume.restrict (↑(⊤ : Opens (Space 0)) : Set (Space 0))] u := hc.symm.trans hcoe
  simp only [Opens.coe_top, Measure.restrict_univ, volume_eq] at he
  simpa only [ae_dirac_eq, Filter.EventuallyEq, Filter.eventually_pure] using he

lemma zeroSubmodule_top (Ω : Opens (Space 0)) (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    sobolevZeroSubmodule 𝕜 Ω m p = ⊤ := by
  have hs : smoothSobolevSubmodule 𝕜 Ω m p = ⊤ := by
    apply Submodule.eq_top_iff'.mpr
    intro u
    exact testLp_surjective Ω p (sobolevUnderlying u)
  apply top_unique
  rw [← hs]
  exact (smoothSobolevSubmodule 𝕜 Ω m p).le_topologicalClosure

lemma sobolevSpaces : ZeroDimensionExpected.SobolevSpaces := by
  intro 𝕜 _ m p _
  refine ⟨⟨scalarLpEquiv p, scalarLpEquiv_apply p⟩, fun Ω => ?_⟩
  obtain ⟨e, he⟩ := sobolev_zeroDimension_isometry (𝕜 := 𝕜) (m := m) (p := p) Ω
  have hz := zeroSubmodule_top (𝕜 := 𝕜) Ω m p
  refine ⟨⟨e, he⟩, hz, ?_, fun u => (e.norm_map u).symm.trans (congrArg norm (he u))⟩
  exact ⟨(LinearIsometryEquiv.ofTop (Sobolev 𝕜 Ω m p) (sobolevZeroSubmodule 𝕜 Ω m p) hz).trans e,
    fun u => he u.val⟩

lemma negative : ZeroDimensionExpected.Negative := by
  have hzero : NegativeSobolevExpected.ZeroDimension := negative_zeroDimension
  refine ⟨hzero, ?_⟩
  intro 𝕜 _ Ω p _ hp1 hp
  obtain ⟨R, hreal⟩ := negative_realization (𝕜 := 𝕜) Ω p hp1 hp
  refine ⟨R, hreal, ?_⟩
  intro f
  obtain ⟨a, haNorm, ha⟩ := hzero Ω p hp1 hp f
  refine ⟨a, haNorm, ?_, ha⟩
  ext φ
  obtain ⟨u, hu⟩ := zeroExtension_smoothInclusion Ω 1 p φ
  let v : SobolevZero 𝕜 Ω 1 p := ⟨u, by rw [zeroSubmodule_top]; trivial⟩
  rw [hreal.2 f φ v hu, ha v]
  rw [regular_pairing 0 𝕜 Ω a
    (domainLp_locallyIntegrable Ω (ENNReal.conjExponent p) a) φ]
  apply integral_congr_ae
  filter_upwards [testToDomainLp_ae Ω p φ] with x hx
  change a x * sobolevUnderlying u x = a x * φ x
  rw [hu, hx]

lemma empty : ZeroDimensionExpected.Empty := by
  intro 𝕜 _
  refine ⟨emptyTests 0 𝕜, fun φ => (emptyStage 0 𝕜 φ).1, ?_, lp_empty,
    fun m p _ => sobolev_empty m p, ?_, negative_empty⟩
  · intro S
    have hS : S = 0 := by
      ext φ
      rw [emptyTests 0 𝕜 φ, map_zero]
      rfl
    refine ⟨hS, ?_⟩
    exact Set.sdiff_eq_empty.mpr (Set.empty_subset _)
  · intro m p _ u
    apply Subtype.ext
    exact sobolev_empty m p u.val

end ZeroDimensionProof

theorem zeroDimension_geometry : ZeroDimensionExpected.Geometry :=
  ZeroDimensionProof.geometry

theorem zeroDimension_functions : ZeroDimensionExpected.Functions :=
  ZeroDimensionProof.functions

theorem zeroDimension_order : ZeroDimensionExpected.Order :=
  ZeroDimensionProof.order

theorem zeroDimension_distributions : ZeroDimensionExpected.Distributions :=
  ZeroDimensionProof.distributions

theorem zeroDimension_convolution : ZeroDimensionExpected.Convolution :=
  ZeroDimensionProof.convolution

theorem zeroDimension_sobolev : ZeroDimensionExpected.SobolevSpaces :=
  ZeroDimensionProof.sobolevSpaces

theorem zeroDimension_negative : ZeroDimensionExpected.Negative :=
  ZeroDimensionProof.negative

theorem zeroDimension_empty : ZeroDimensionExpected.Empty :=
  ZeroDimensionProof.empty

end P102.U4
