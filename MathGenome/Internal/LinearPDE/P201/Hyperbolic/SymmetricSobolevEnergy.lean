import MathGenome.Internal.LinearPDE.P201Specs.Hyperbolic.SymmetricSobolevEnergy
import MathGenome.Internal.LinearPDE.P201.Common.SpatialInterfaces
import MathGenome.Internal.LinearPDE.P201.Hyperbolic.SymmetricEnergy
import MathGenome.Internal.FourierSobolev.P102.U4.DistributionOperations
import MathGenome.Internal.FourierSobolev.P102.U4.WholeSpaceDensity
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.UniformSpace.UniformApproximation

noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 2000
set_option maxHeartbeats 2000000
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal InnerProductSpace ContDiff Topology
namespace P201.Hyperbolic.SymmetricSobolevEnergy
open P201Specs.Hyperbolic.SymmetricSobolevEnergy

/-- The vector norm uses the source derivative-square convention exactly. -/
theorem full_norm : FullNormStatement := by
  intro n m k 𝕜 _ v
  rw [PiLp.norm_sq_eq_of_L2]
  calc
    _ = ∑ i : Fin m, ∑ α : P102.U4.SobolevIndex n k,
        ‖P102.U4.sobolevDerivative (P201Specs.hToW 𝕜 ⊤ k (v i)) α‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      exact P201.fullHilbertNorm ⊤ k (v i)
    _ = _ := Finset.sum_comm

private theorem lpNorm_two_sq {Z E : Type*} [MeasurableSpace Z]
    [NormedAddCommGroup E] {μ : Measure Z} {f : Z → E}
    (hf : AEStronglyMeasurable f μ) :
    lpNorm f 2 μ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  have h : lpNorm f 2 μ = Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) := by
    rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hf]
    norm_num [Real.sqrt_eq_rpow]
  rw [h, Real.sq_sqrt (integral_nonneg (fun _ => sq_nonneg _))]

/-- Componentwise weak derivatives assemble into the genuine vector L² norm. -/
theorem section_norm : SectionNormStatement := by
  intro n m k 𝕜 _ v
  have hm : ∀ (α : P102.U4.SobolevIndex n k) (i : Fin m),
      MemLp (fun x => P102.U4.sobolevDerivative (P201Specs.hToW 𝕜 ⊤ k (v i)) α x) 2
        (volume : Measure (P201Specs.Space n)) := by
    intro α i
    exact (Lp.memLp _).mono_measure (by simp)
  have hv : ∀ α : P102.U4.SobolevIndex n k, MemLp (derivativeSection v α) 2 volume := by
    intro α
    apply MemLp.of_eval_piLp
    exact hm α
  refine ⟨hv, ?_⟩
  rw [full_norm]
  apply Finset.sum_congr rfl
  intro α _
  rw [lpNorm_two_sq (hv α).aestronglyMeasurable]
  simp_rw [PiLp.norm_sq_eq_of_L2]
  change (∑ i : Fin m, ‖P102.U4.sobolevDerivative (P201Specs.hToW 𝕜 ⊤ k (v i)) α‖ ^ 2) =
    ∫ x, ∑ i : Fin m, ‖P102.U4.sobolevDerivative (P201Specs.hToW 𝕜 ⊤ k (v i)) α x‖ ^ 2
  rw [integral_finsetSum _ (fun i _ => (hm α i).integrable_norm_pow (by norm_num))]
  apply Finset.sum_congr rfl
  intro i _
  rw [Lp.norm_def]
  change lpNorm _ 2 _ ^ 2 = _
  rw [lpNorm_two_sq (Lp.aestronglyMeasurable _)]
  simp only [P201Specs.domainMeasure, TopologicalSpace.Opens.coe_top, Measure.restrict_univ]

/-- Scalar Gronwall comparison for the actual H^s Hilbert norm. -/
theorem hilbert_comparison : HilbertComparisonStatement := by
  intro X _ _ T C u du f hT hC hu hdu hf hd hb
  let E : ℝ → ℝ := fun t => ‖u t‖ ^ 2 / 2
  let D : ℝ → ℝ := fun t => inner ℝ (u t) (du t)
  have hEc : ContinuousOn E (Icc 0 T) := (hu.norm.pow 2).div_const 2
  have hDc : ContinuousOn D (Icc 0 T) := hu.inner hdu
  have hEd : ∀ t ∈ Ioo 0 T, HasDerivAt E (D t) t := by
    intro t ht
    convert ((hd t ht).norm_sq.div_const 2) using 1
    dsimp [E, D]
    ring
  have hFi : IntegrableOn (fun t => ‖f t‖) (Icc 0 T) :=
    hf.norm.integrableOn_Icc
  have hEn : ∀ t ∈ Icc 0 T, 0 ≤ E t := fun t _ => by dsimp [E]; positivity
  have hroot (t : ℝ) : Real.sqrt (2 * E t) = ‖u t‖ := by
    dsimp [E]
    rw [show 2 * (‖u t‖ ^ 2 / 2) = ‖u t‖ ^ 2 by ring]
    exact Real.sqrt_sq (norm_nonneg _)
  have hb' : ∀ᵐ t ∂volume.restrict (Icc 0 T),
      D t ≤ 2 * C * E t + ‖f t‖ * Real.sqrt (2 * E t) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [hroot]
    dsimp [D, E]
    nlinarith [hb t ht]
  have h := P201.Hyperbolic.SymmetricEnergy.sqrt_energy_comparison
    T C E D (fun t => ‖f t‖) hT hC hEc hDc hEd hEn hFi
    (Filter.Eventually.of_forall (fun t => norm_nonneg _)) hb'
  simpa only [hroot] using h

/-- Equality of vector a.e. representatives determines the actual Sobolev element. -/
theorem underlying_injective {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {u v : WholeH n m 𝕜 k}
    (h : underlyingSection u =ᵐ[volume] underlyingSection v) : u = v := by
  apply PiLp.ext
  intro i
  apply P201.hilbertUnderlyingInjective ⊤ k
  apply Lp.ext
  have hi := h.mono (fun x hx => congrArg (fun z : P201Specs.Hyperbolic.SymmetricEnergy.Fiber 𝕜 m => z i) hx)
  change ∀ᵐ x ∂volume, P201Specs.hUnderlying ⊤ k (u i) x =
    P201Specs.hUnderlying ⊤ k (v i) x at hi
  exact ae_restrict_of_ae hi

/-- Order lowering commutes with subtraction, without choosing any representatives. -/
theorem isLowerOrder_sub {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {u v : WholeH n m 𝕜 (k + 1)} {w z : WholeH n m 𝕜 k}
    (hu : IsLowerOrder u w) (hv : IsLowerOrder v z) :
    IsLowerOrder (u - v) (w - z) := by
  intro i
  change P201Specs.hUnderlying ⊤ (k + 1) (u i - v i) =
    P201Specs.hUnderlying ⊤ k (w i - z i)
  rw [map_sub, map_sub, hu i, hv i]

/-- The comparison lemma also applies to complex Hilbert spaces, with the
real part of the energy pairing and the original Hilbert norm. -/
theorem rclike_hilbert_comparison {𝕜 X : Type} [RCLike 𝕜]
    [NormedAddCommGroup X] [InnerProductSpace 𝕜 X]
    [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X]
    (T C : ℝ) (u du f : ℝ → X) (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hu : ContinuousOn u (Icc 0 T)) (hdu : ContinuousOn du (Icc 0 T))
    (hf : ContinuousOn f (Icc 0 T))
    (hd : ∀ t ∈ Ioo 0 T, HasDerivAt u (du t) t)
    (hb : ∀ t ∈ Icc 0 T, RCLike.re (inner 𝕜 (u t) (du t)) ≤
      C * ‖u t‖ ^ 2 + ‖u t‖ * ‖f t‖) :
    ‖u T‖ ≤ Real.exp (C * T) * (‖u 0‖ + ∫ t in (0 : ℝ)..T, ‖f t‖) := by
  let E : ℝ → ℝ := fun t => ‖u t‖ ^ 2 / 2
  let D : ℝ → ℝ := fun t => RCLike.re (inner 𝕜 (u t) (du t))
  have hEc : ContinuousOn E (Icc 0 T) := (hu.norm.pow 2).div_const 2
  have hDc : ContinuousOn D (Icc 0 T) := RCLike.continuous_re.comp_continuousOn (hu.inner hdu)
  have hEd : ∀ t ∈ Ioo 0 T, HasDerivAt E (D t) t := by
    intro t ht
    have hi := (hd t ht).inner 𝕜 (hd t ht)
    have hr := ((RCLike.reCLM : 𝕜 →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t hi).div_const 2
    convert hr using 1
    · funext r
      simp [E]
    · simp only [RCLike.reCLM_apply, map_add, inner_re_symm]
      dsimp [D]
      ring
  have hFi : IntegrableOn (fun t => ‖f t‖) (Icc 0 T) := hf.norm.integrableOn_Icc
  have hEn : ∀ t ∈ Icc 0 T, 0 ≤ E t := fun t _ => by dsimp [E]; positivity
  have hroot (t : ℝ) : Real.sqrt (2 * E t) = ‖u t‖ := by
    dsimp [E]
    rw [show 2 * (‖u t‖ ^ 2 / 2) = ‖u t‖ ^ 2 by ring]
    exact Real.sqrt_sq (norm_nonneg _)
  have hb' : ∀ᵐ t ∂volume.restrict (Icc 0 T),
      D t ≤ 2 * C * E t + ‖f t‖ * Real.sqrt (2 * E t) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [hroot]
    dsimp [D, E]
    nlinarith [hb t ht]
  have h := P201.Hyperbolic.SymmetricEnergy.sqrt_energy_comparison
    T C E D (fun t => ‖f t‖) hT hC hEc hDc hEd hEn hFi
    (Filter.Eventually.of_forall (fun t => norm_nonneg _)) hb'
  simpa only [hroot] using h

/-- The spatial pairing inequality yields the time estimate on every initial
subinterval. The high-regularity lift need not be continuous in the higher norm. -/
theorem estimate_of_pairing {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {T C : ℝ} (Q : ℝ → WholeH n m 𝕜 (k + 1) →L[𝕜] WholeH n m 𝕜 k)
    (hC : 0 ≤ C) (u du f : ℝ → WholeH n m 𝕜 k)
    (V : ℝ → WholeH n m 𝕜 (k + 1))
    (hu : ContinuousOn u (Icc 0 T)) (hdu : ContinuousOn du (Icc 0 T))
    (hf : ContinuousOn f (Icc 0 T))
    (hd : ∀ r ∈ Ioo 0 T, HasDerivAt u (du r) r)
    (hl : ∀ r ∈ Icc 0 T, IsLowerOrder (V r) (u r))
    (he : ∀ r ∈ Icc 0 T, du r = Q r (V r) + f r)
    (hp : ∀ r ∈ Icc 0 T, ∀ (v : WholeH n m 𝕜 (k + 1)) (w : WholeH n m 𝕜 k),
      IsLowerOrder v w → |RCLike.re (inner 𝕜 w (Q r v))| ≤ C * ‖w‖ ^ 2) :
    ∀ t ∈ Icc 0 T,
      ‖u t‖ ≤ Real.exp (C * t) * (‖u 0‖ + ∫ r in (0 : ℝ)..t, ‖f r‖) := by
  intro t ht
  have hsub : Icc (0 : ℝ) t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
  apply rclike_hilbert_comparison (𝕜 := 𝕜) t C u du f ht.1 hC
    (hu.mono hsub) (hdu.mono hsub) (hf.mono hsub)
  · intro r hr
    exact hd r ⟨hr.1, hr.2.trans_le ht.2⟩
  · intro r hr
    have hrT := hsub hr
    rw [he r hrT, inner_add_right, map_add]
    have hp' := (le_abs_self _).trans (hp r hrT (V r) (u r) (hl r hrT))
    have hf' : RCLike.re (inner 𝕜 (u r) (f r)) ≤ ‖u r‖ * ‖f r‖ :=
      (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
    linarith

/-- Complete algebraic assembly of the high-order estimate and its difference
estimate, conditional on the separately proved spatial pairing theorem. -/
theorem evolution_of_pairing : EvolutionOfPairingStatement := by
  intro hp n s hn hs K hK
  obtain ⟨C, hC, hp⟩ := hp n s hn hs K hK
  refine ⟨C, hC, ?_⟩
  intro m 𝕜 _ T hT A B hAB k hk
  obtain ⟨Q, hQ, hp⟩ := hp T hT A B hAB k hk
  have solve (u du f : ℝ → WholeH n m 𝕜 k)
      (V : ℝ → WholeH n m 𝕜 (k + 1))
      (he : ∀ r ∈ Icc 0 T, underlyingSection (du r - f r) =ᵐ[volume]
        pSection (fun j => A j r) (B r) (V r)) :
      ∀ r ∈ Icc 0 T, du r = Q r (V r) + f r := by
    intro r hr
    have heq : du r - f r = Q r (V r) :=
      underlying_injective ((he r hr).trans ((hQ r hr (V r)).symm))
    exact sub_eq_iff_eq_add.mp heq
  constructor
  · intro u du f V hu
    rcases hu with ⟨huc, hduc, hfc, hd, hl, he⟩
    exact estimate_of_pairing Q hC u du f V huc hduc hfc hd hl (solve u du f V he) hp
  · intro u du f v dv g U V hu hv
    rcases hu with ⟨huc, hduc, hfc, hd, hl, he⟩
    rcases hv with ⟨hvc, hdvc, hgc, hdv, hlv, hev⟩
    apply estimate_of_pairing Q hC (fun r => u r - v r) (fun r => du r - dv r)
      (fun r => f r - g r) (fun r => U r - V r)
      (huc.sub hvc) (hduc.sub hdvc) (hfc.sub hgc)
    · intro r hr
      exact HasDerivAt.sub (𝕜 := ℝ) (F := WholeH n m 𝕜 k) (f := u) (g := v)
        (f' := du r) (g' := dv r) (hd r hr) (hdv r hr)
    · intro r hr
      exact isLowerOrder_sub (hl r hr) (hlv r hr)
    · intro r hr
      rw [solve u du f U he r hr, solve v dv g V hev r hr, map_sub]
      abel
    · exact hp


/-- Addition of a fixed multi-index embeds the lower derivative index set. -/
def shiftedIndex {n k l : ℕ} (β : P102.U4.SobolevIndex n l)
    (α : P102.U4.SobolevIndex n k) : P102.U4.SobolevIndex n (k + l) :=
  ⟨α.val + β.val, by simpa only [Multiset.card_add] using Nat.add_le_add α.property β.property⟩

theorem shiftedIndex_injective {n k l : ℕ} (β : P102.U4.SobolevIndex n l) :
    Function.Injective (shiftedIndex (k := k) β) := by
  intro α γ h
  apply Subtype.ext
  exact add_right_cancel (congrArg Subtype.val h)

/-- A weak derivative is obtained by shifting the actual closed-graph tuple.
This construction works on every open domain and does not require density. -/
def scalarDerivative {n k l : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : P201Specs.Domain n) (β : P102.U4.SobolevIndex n l)
    (u : P201Specs.H 𝕜 Ω (k + l)) : P201Specs.H 𝕜 Ω k :=
  ⟨WithLp.toLp 2 (fun α => u.val (shiftedIndex β α)), by
    change P201Specs.hilbertTupleToSum 𝕜 Ω k
      (WithLp.toLp 2 (fun α => u.val (shiftedIndex β α))) ∈
        P102.U4.sobolevSubmodule 𝕜 Ω k 2
    apply (P102.U4.mem_sobolevSubmodule_iff Ω k 2 _).mpr
    intro α φ
    apply (P102.U4.distributionPartial_eq_regularLp_iff Ω 2 α.val _ _).mp
    change P102.U4.distributionPartial α.val
      (P102.U4.regularDistribution Ω (u.val (shiftedIndex β (P102.U4.zeroSobolevIndex n k)))) =
      P102.U4.regularDistribution Ω (u.val (shiftedIndex β α))
    have hb := P201.hilbertDerivativeDistribution Ω (k + l) u
      (shiftedIndex β (P102.U4.zeroSobolevIndex n k))
    have ha := P201.hilbertDerivativeDistribution Ω (k + l) u (shiftedIndex β α)
    change P102.U4.distributionPartial (shiftedIndex β (P102.U4.zeroSobolevIndex n k)).val
      (P102.U4.regularDistribution Ω (P201Specs.hUnderlying Ω (k + l) u)) =
      P102.U4.regularDistribution Ω (u.val (shiftedIndex β (P102.U4.zeroSobolevIndex n k))) at hb
    change P102.U4.distributionPartial (shiftedIndex β α).val
      (P102.U4.regularDistribution Ω (P201Specs.hUnderlying Ω (k + l) u)) =
      P102.U4.regularDistribution Ω (u.val (shiftedIndex β α)) at ha
    rw [← hb, ← P102.U4.derivative_add n 𝕜 Ω]
    simpa only [shiftedIndex, P102.U4.zeroSobolevIndex, zero_add] using ha⟩

theorem scalarDerivative_norm_le {n k l : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : P201Specs.Domain n) (β : P102.U4.SobolevIndex n l)
    (u : P201Specs.H 𝕜 Ω (k + l)) : ‖scalarDerivative Ω β u‖ ≤ ‖u‖ := by
  classical
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change ‖(scalarDerivative Ω β u).val‖ ^ 2 ≤ ‖u.val‖ ^ 2
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  change (∑ α, ‖u.val (shiftedIndex β α)‖ ^ 2) ≤ ∑ γ, ‖u.val γ‖ ^ 2
  calc
    _ = ∑ γ ∈ Finset.univ.image (shiftedIndex (k := k) β), ‖u.val γ‖ ^ 2 := by
      rw [Finset.sum_image]
      exact fun _ _ _ _ h => shiftedIndex_injective β h
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => sq_nonneg _)

/-- All distributional coordinate derivatives, and order lowering (β=0),
are contractions for the exact derivative-square Sobolev norm. -/
def scalarDerivativeCLM {n k l : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : P201Specs.Domain n) (β : P102.U4.SobolevIndex n l) :
    P201Specs.H 𝕜 Ω (k + l) →L[𝕜] P201Specs.H 𝕜 Ω k :=
  LinearMap.mkContinuous
    { toFun := scalarDerivative Ω β
      map_add' := by intro u v; apply Subtype.ext; rfl
      map_smul' := by intro c u; apply Subtype.ext; rfl }
    1 (fun u => by
      change ‖scalarDerivative Ω β u‖ ≤ 1 * ‖u‖
      simpa only [one_mul] using scalarDerivative_norm_le Ω β u)

/-- Derivative coordinates of the constructed weak derivative are unchanged. -/
theorem scalarDerivative_coordinate {n k l : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : P201Specs.Domain n) (β : P102.U4.SobolevIndex n l)
    (u : P201Specs.H 𝕜 Ω (k + l)) (α : P102.U4.SobolevIndex n k) :
    P102.U4.sobolevDerivative (P201Specs.hToW 𝕜 Ω k (scalarDerivativeCLM Ω β u)) α =
      P102.U4.sobolevDerivative (P201Specs.hToW 𝕜 Ω (k + l) u) (shiftedIndex β α) := rfl


/-- The componentwise weak derivative acts on the original Euclidean fiber,
with a bound independent of the number of components. -/
def wholeDerivativeCLM {n m k l : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (β : P102.U4.SobolevIndex n l) :
    WholeH n m 𝕜 (k + l) →L[𝕜] WholeH n m 𝕜 k :=
  LinearMap.mkContinuous
    { toFun := fun u => WithLp.toLp 2 (fun i => scalarDerivativeCLM ⊤ β (u i))
      map_add' := by intro u v; apply PiLp.ext; intro i; exact map_add _ _ _
      map_smul' := by
        intro c u
        apply PiLp.ext
        intro i
        exact (scalarDerivativeCLM (𝕜 := 𝕜) ⊤ β).map_smul c (u i) }
    1 (fun u => by
      change ‖WithLp.toLp 2 (fun i : Fin m => scalarDerivativeCLM ⊤ β (u i))‖ ≤ 1 * ‖u‖
      rw [one_mul]
      apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
      apply Finset.sum_le_sum
      intro i _
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
        (scalarDerivative_norm_le ⊤ β (u i)))

theorem wholeDerivativeCLM_norm_le {n m k l : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (β : P102.U4.SobolevIndex n l) :
    ‖wholeDerivativeCLM (m := m) (k := k) (𝕜 := 𝕜) β‖ ≤ 1 := by
  exact LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- The weak derivative realizes the corresponding actual a.e. section. -/
theorem wholeDerivative_underlying {n m k l : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (β : P102.U4.SobolevIndex n l) (u : WholeH n m 𝕜 (k + l)) :
    underlyingSection (wholeDerivativeCLM (k := k) β u) =
      derivativeSection u ⟨β.val, β.property.trans (Nat.le_add_left l k)⟩ := by
  funext x
  apply PiLp.ext
  intro i
  change (u i).val (shiftedIndex β (P102.U4.zeroSobolevIndex n k)) x =
    (u i).val ⟨β.val, β.property.trans (Nat.le_add_left l k)⟩ x
  have hi : shiftedIndex β (P102.U4.zeroSobolevIndex n k) =
      (⟨β.val, β.property.trans (Nat.le_add_left l k)⟩ : P102.U4.SobolevIndex n (k + l)) :=
    Subtype.ext (zero_add β.val)
  rw [hi]

/-- Natural order lowering, as a contraction of the actual weak-derivative graph. -/
def lowerOrderCLM {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜] :
    WholeH n m 𝕜 (k + 1) →L[𝕜] WholeH n m 𝕜 k :=
  wholeDerivativeCLM (P102.U4.zeroSobolevIndex n 1)

def partialCLM {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜] (j : Fin n) :
    WholeH n m 𝕜 (k + 1) →L[𝕜] WholeH n m 𝕜 k :=
  wholeDerivativeCLM (⟨{j}, by simp⟩ : P102.U4.SobolevIndex n 1)

theorem lowerOrderCLM_realizes {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (u : WholeH n m 𝕜 (k + 1)) : IsLowerOrder u (lowerOrderCLM u) := by
  intro i
  change (u i).val (P102.U4.zeroSobolevIndex n (k + 1)) =
    (u i).val (shiftedIndex (P102.U4.zeroSobolevIndex n 1) (P102.U4.zeroSobolevIndex n k))
  rfl

theorem lowerOrderCLM_underlying {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (u : WholeH n m 𝕜 (k + 1)) : underlyingSection (lowerOrderCLM u) = underlyingSection u :=
  wholeDerivative_underlying (P102.U4.zeroSobolevIndex n 1) u

theorem partialCLM_underlying {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (j : Fin n) (u : WholeH n m 𝕜 (k + 1)) :
    underlyingSection (partialCLM j u) = derivativeSection u ⟨{j}, by simp⟩ :=
  wholeDerivative_underlying (⟨{j}, by simp⟩ : P102.U4.SobolevIndex n 1) u

/-- The lower-order representative always exists and is unique. -/
theorem lowerOrder_existsUnique {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (u : WholeH n m 𝕜 (k + 1)) : ∃! w, IsLowerOrder u w := by
  refine ⟨lowerOrderCLM u, lowerOrderCLM_realizes u, ?_⟩
  intro w hw
  apply PiLp.ext
  intro i
  apply P201.hilbertUnderlyingInjective ⊤ k
  exact (hw i).symm.trans (lowerOrderCLM_realizes u i)


/-- A.e. section algebra follows from the canonical linear map to L² classes. -/
theorem underlyingSection_zero {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜] :
    underlyingSection (0 : WholeH n m 𝕜 k) =ᵐ[volume] 0 := by
  have h (i : Fin m) : ∀ᵐ x ∂volume,
      P201Specs.hUnderlying ⊤ k (0 : P201Specs.H 𝕜 (⊤ : P201Specs.Domain n) k) x = 0 := by
    rw [map_zero]
    simpa only [Filter.EventuallyEq, P201Specs.domainMeasure, TopologicalSpace.Opens.coe_top,
      Measure.restrict_univ, Pi.zero_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
      using (Lp.coeFn_zero 𝕜 2 (P201Specs.domainMeasure (⊤ : P201Specs.Domain n)))
  filter_upwards [ae_all_iff.mpr h] with x hx
  exact PiLp.ext (fun i => hx i)

theorem underlyingSection_add {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (u v : WholeH n m 𝕜 k) :
    underlyingSection (u + v) =ᵐ[volume] underlyingSection u + underlyingSection v := by
  have h (i : Fin m) : ∀ᵐ x ∂volume,
      P201Specs.hUnderlying ⊤ k (u i + v i) x =
      P201Specs.hUnderlying ⊤ k (u i) x + P201Specs.hUnderlying ⊤ k (v i) x := by
    rw [map_add]
    simpa only [Filter.EventuallyEq, P201Specs.domainMeasure, TopologicalSpace.Opens.coe_top,
      Measure.restrict_univ, Pi.zero_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
      using Lp.coeFn_add (P201Specs.hUnderlying ⊤ k (u i)) (P201Specs.hUnderlying ⊤ k (v i))
  filter_upwards [ae_all_iff.mpr h] with x hx
  exact PiLp.ext (fun i => hx i)

theorem underlyingSection_sub {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (u v : WholeH n m 𝕜 k) :
    underlyingSection (u - v) =ᵐ[volume] underlyingSection u - underlyingSection v := by
  have h (i : Fin m) : ∀ᵐ x ∂volume,
      P201Specs.hUnderlying ⊤ k (u i - v i) x =
      P201Specs.hUnderlying ⊤ k (u i) x - P201Specs.hUnderlying ⊤ k (v i) x := by
    rw [map_sub]
    simpa only [Filter.EventuallyEq, P201Specs.domainMeasure, TopologicalSpace.Opens.coe_top,
      Measure.restrict_univ, Pi.zero_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
      using Lp.coeFn_sub (P201Specs.hUnderlying ⊤ k (u i)) (P201Specs.hUnderlying ⊤ k (v i))
  filter_upwards [ae_all_iff.mpr h] with x hx
  exact PiLp.ext (fun i => hx i)

theorem underlyingSection_neg {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (u : WholeH n m 𝕜 k) :
    underlyingSection (-u) =ᵐ[volume] -underlyingSection u := by
  have h (i : Fin m) : ∀ᵐ x ∂volume,
      P201Specs.hUnderlying ⊤ k (-u i) x = -P201Specs.hUnderlying ⊤ k (u i) x := by
    rw [map_neg]
    simpa only [Filter.EventuallyEq, P201Specs.domainMeasure, TopologicalSpace.Opens.coe_top,
      Measure.restrict_univ, Pi.zero_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
      using Lp.coeFn_neg (P201Specs.hUnderlying ⊤ k (u i))
  filter_upwards [ae_all_iff.mpr h] with x hx
  exact PiLp.ext (fun i => hx i)

theorem underlyingSection_sum {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {ι : Type*} (s : Finset ι) (u : ι → WholeH n m 𝕜 k) :
    underlyingSection (∑ i ∈ s, u i) =ᵐ[volume] fun x => ∑ i ∈ s, underlyingSection (u i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Filter.EventuallyEq, Finset.sum_empty, Pi.zero_apply] using (underlyingSection_zero (n := n) (m := m) (k := k) (𝕜 := 𝕜))
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (underlyingSection_add _ _).trans (Filter.EventuallyEq.rfl.add ih)

open P201Specs.Hyperbolic.SymmetricEnergy in
/-- The first-order operator constructed from actual bounded multiplier maps. -/
def operatorFromMultipliers {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (M : Fin n → WholeH n m 𝕜 k →L[𝕜] WholeH n m 𝕜 k)
    (N : WholeH n m 𝕜 k →L[𝕜] WholeH n m 𝕜 k) :
    WholeH n m 𝕜 (k + 1) →L[𝕜] WholeH n m 𝕜 k :=
  -(∑ j, (M j).comp (partialCLM j)) - N.comp lowerOrderCLM

open P201Specs.Hyperbolic.SymmetricEnergy in
theorem operatorFromMultipliers_realizes {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (A : Fin n → P201Specs.Space n → Operator m 𝕜) (B : P201Specs.Space n → Operator m 𝕜)
    (M : Fin n → WholeH n m 𝕜 k →L[𝕜] WholeH n m 𝕜 k)
    (N : WholeH n m 𝕜 k →L[𝕜] WholeH n m 𝕜 k)
    (hM : ∀ j, RealizesMultiplier (A j) (M j)) (hN : RealizesMultiplier B N) :
    RealizesP A B (operatorFromMultipliers M N) := by
  intro v
  have hsum := underlyingSection_sum Finset.univ (fun j => M j (partialCLM j v))
  have hneg := underlyingSection_neg (∑ j, M j (partialCLM j v))
  have hsub := underlyingSection_sub (-(∑ j, M j (partialCLM j v))) (N (lowerOrderCLM v))
  have hj : ∀ᵐ x ∂volume, ∀ j,
      underlyingSection (M j (partialCLM j v)) x = A j x (derivativeSection v ⟨{j}, by simp⟩ x) := by
    apply ae_all_iff.mpr
    intro j
    simpa only [Filter.EventuallyEq, partialCLM_underlying] using hM j (partialCLM j v)
  have hb := hN (lowerOrderCLM v)
  rw [lowerOrderCLM_underlying] at hb
  change ∀ᵐ x ∂volume, underlyingSection
    ((-(∑ j, (M j).comp (partialCLM j)) - N.comp lowerOrderCLM) v) x = _
  simp only [sub_apply, neg_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply]
  filter_upwards [hsub, hneg, hsum, hj, hb] with x hx hn hs hj hb
  rw [hx]
  simp only [Pi.sub_apply, Pi.neg_apply] at hn ⊢
  rw [hn, hs, hb]
  simp only [pSection]
  congr 2
  exact Finset.sum_congr rfl (fun j _ => hj j)

theorem operatorFromMultipliers_norm_le {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {C : ℝ} (hC : 0 ≤ C)
    (M : Fin n → WholeH n m 𝕜 k →L[𝕜] WholeH n m 𝕜 k)
    (N : WholeH n m 𝕜 k →L[𝕜] WholeH n m 𝕜 k)
    (hM : ∀ j, ‖M j‖ ≤ C) (hN : ‖N‖ ≤ C) :
    ‖operatorFromMultipliers M N‖ ≤ (n + 1 : ℝ) * C := by
  have hj (j : Fin n) : ‖(M j).comp (partialCLM j)‖ ≤ C := by
    calc
      _ ≤ ‖M j‖ * ‖partialCLM (k := k) (m := m) (𝕜 := 𝕜) j‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ C * 1 := mul_le_mul (hM j) (wholeDerivativeCLM_norm_le _) (norm_nonneg _) hC
      _ = C := mul_one _
  have hb : ‖N.comp (lowerOrderCLM (k := k))‖ ≤ C := by
    calc
      _ ≤ ‖N‖ * ‖lowerOrderCLM (n := n) (m := m) (𝕜 := 𝕜) (k := k)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ C * 1 := mul_le_mul hN (wholeDerivativeCLM_norm_le _) (norm_nonneg _) hC
      _ = C := mul_one _
  have hs : ‖∑ j, (M j).comp (partialCLM j)‖ ≤ n * C := by
    calc
      _ ≤ ∑ j, ‖(M j).comp (partialCLM j)‖ := norm_sum_le _ _
      _ ≤ ∑ _ : Fin n, C := Finset.sum_le_sum (fun j _ => hj j)
      _ = n * C := by simp
  calc
    _ ≤ ‖-(∑ j, (M j).comp (partialCLM j))‖ + ‖N.comp lowerOrderCLM‖ := norm_sub_le _ _
    _ = ‖∑ j, (M j).comp (partialCLM j)‖ + ‖N.comp lowerOrderCLM‖ := by exact congrArg (fun r : ℝ => r + ‖N.comp lowerOrderCLM‖) (norm_neg _)
    _ ≤ n * C + C := add_le_add hs hb
    _ = _ := by ring


/-- The source P-family assertion follows from the multiplier assertion;
weak derivatives, inclusions and their quantitative bounds are proved above. -/
theorem operator_of_multiplier : MultiplierStatement → OperatorStatement := by
  classical
  intro hm n s hn hs K hK
  obtain ⟨C, hC, hm⟩ := hm n s hn hs K hK
  refine ⟨(n + 1 : ℝ) * C, by positivity, ?_⟩
  intro m 𝕜 _ T hT A B hAB k hk
  have ha (j : Fin n) := hm T hT (A j) (hAB.1 j) k hk.le
  choose M hMa hMc using ha
  obtain ⟨N, hNa, hNc⟩ := hm T hT B hAB.2.1 k hk.le
  refine ⟨fun t => operatorFromMultipliers (fun j => M j t) (N t), ?_, ?_⟩
  · intro t ht
    exact ⟨operatorFromMultipliers_realizes (fun j => A j t) (B t) _ _
        (fun j => (hMa j t ht).1) (hNa t ht).1,
      operatorFromMultipliers_norm_le hC _ _ (fun j => (hMa j t ht).2) (hNa t ht).2⟩
  · intro v
    change ContinuousOn
      (fun t => (-(∑ j, (M j t).comp (partialCLM j)) - (N t).comp lowerOrderCLM) v) (Icc 0 T)
    simp only [sub_apply, neg_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply]
    exact (continuousOn_finsetSum _ (fun j _ => hMc j (partialCLM j v))).neg.sub
      (hNc (lowerOrderCLM v))


section CoefficientCalculus
open P201Specs.Hyperbolic.SymmetricSobolevEnergy
open P201Specs.Hyperbolic.SymmetricEnergy

/-- Smoothness of the spacetime coefficient gives smoothness of every spatial slice. -/
theorem coefficient_slice_contDiff {n : ℕ} {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {T : ℝ}
    {a : ℝ → P201Specs.Space n → E}
    (ha : ContDiffOn ℝ ∞ (Function.uncurry a) (slab n T))
    {t : ℝ} (ht : t ∈ Icc 0 T) : ContDiff ℝ ∞ (a t) := by
  rw [← contDiffOn_univ]
  exact ha.comp (contDiffOn_const.prodMk contDiffOn_id) (fun x _ => ⟨ht, mem_univ x⟩)

/-- Taking any finite sequence of spatial derivatives preserves smoothness. -/
theorem spatialWord_contDiff {n : ℕ} {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : P201Specs.Space n → E} (ha : ContDiff ℝ ∞ a) (l : List (Fin n)) :
    ContDiff ℝ ∞ (spatialWord a l) := by
  induction l with
  | nil => exact ha
  | cons j l ih => exact (ih.fderiv_right (by simp)).clm_apply contDiff_const

/-- For a nondegenerate slab, the spatial derivative fields remain jointly smooth
up to the time endpoints. -/
theorem spatialWord_contDiffOn_slab {n : ℕ} {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {T : ℝ} (hT : 0 < T)
    {a : ℝ → P201Specs.Space n → E}
    (ha : ContDiffOn ℝ ∞ (Function.uncurry a) (slab n T)) (l : List (Fin n)) :
    ContDiffOn ℝ ∞ (fun z : ℝ × P201Specs.Space n => spatialWord (a z.1) l z.2)
      (slab n T) := by
  induction l with
  | nil => exact ha
  | cons j l ih =>
    have hd := (ih.fderivWithin ((uniqueDiffOn_Icc hT).prod uniqueDiffOn_univ)
      (m := ∞) (by simp)).clm_apply
        (contDiffOn_const (c := ((0 : ℝ), P201Specs.coordinate n j)))
    apply hd.congr
    intro z hz
    have hi1 : ContDiffOn ℝ 1 (fun z : ℝ × P201Specs.Space n => spatialWord (a z.1) l z.2) (slab n T) :=
      ih.of_le (by simp)
    have hh := P201.Hyperbolic.SymmetricEnergy.slab_section_hasFDerivAt
      (e := fun t x => spatialWord (a t) l x) hi1 hz.1 z.2
    change fderiv ℝ (spatialWord (a z.1) l) z.2 (P201Specs.coordinate n j) = _
    rw [hh.fderiv]
    rfl

/-- The spatial jets are continuous on the actual closed time slab, without
any bound on time derivatives. The degenerate time interval is included. -/
theorem spatialWord_continuousOn_slab {n : ℕ} {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {T : ℝ} (hT : 0 ≤ T)
    {a : ℝ → P201Specs.Space n → E}
    (ha : ContDiffOn ℝ ∞ (Function.uncurry a) (slab n T)) (l : List (Fin n)) :
    ContinuousOn (fun z : ℝ × P201Specs.Space n => spatialWord (a z.1) l z.2)
      (slab n T) := by
  rcases hT.eq_or_lt with hT | hT
  · subst T
    have hc := ((spatialWord_contDiff (coefficient_slice_contDiff ha (t := 0) (by simp)) l).continuous.comp
      continuous_snd).continuousOn (s := slab n 0)
    apply hc.congr
    intro z hz
    have hz0 : z.1 = 0 := le_antisymm hz.1.2 hz.1.1
    simp only [hz0, Function.comp_apply]
  · exact (spatialWord_contDiffOn_slab hT ha l).continuousOn

theorem spatialWord_append {n : ℕ} {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : P201Specs.Space n → E) (l l' : List (Fin n)) :
    spatialWord a (l ++ l') = spatialWord (spatialWord a l') l := by
  induction l with
  | nil => rfl
  | cons j l ih => simp only [List.cons_append, spatialWord, ih]

/-- Spatial differentiation commutes with any fixed continuous real-linear map. -/
theorem spatialWord_comp_clm {n : ℕ} {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) {a : P201Specs.Space n → E}
    (ha : ContDiff ℝ ∞ a) (l : List (Fin n)) :
    spatialWord (fun x => L (a x)) l = fun x => L (spatialWord a l x) := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    funext x
    change fderiv ℝ (spatialWord (fun x => L (a x)) l) x (P201Specs.coordinate n j) = _
    rw [ih]
    change fderiv ℝ (L ∘ spatialWord a l) x (P201Specs.coordinate n j) = _
    rw [(L.hasFDerivAt.comp x
      ((spatialWord_contDiff ha l).differentiable (by simp) x).hasFDerivAt).fderiv]
    rfl

theorem spatialWord_swap {n : ℕ} {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : P201Specs.Space n → E} (ha : ContDiff ℝ ∞ a)
    (i j : Fin n) (l : List (Fin n)) :
    spatialWord a (i :: j :: l) = spatialWord a (j :: i :: l) := by
  funext x
  have hg := spatialWord_contDiff ha l
  have hd : DifferentiableAt ℝ (fderiv ℝ (spatialWord a l)) x :=
    (hg.fderiv_right (m := 1) (by simp)).differentiable one_ne_zero x
  simp only [spatialWord]
  rw [fderiv_clm_apply hd (differentiableAt_const (P201Specs.coordinate n j)),
    fderiv_clm_apply hd (differentiableAt_const (P201Specs.coordinate n i))]
  simpa only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply] using
    (hg.contDiffAt.isSymmSndFDerivAt (by simp) (P201Specs.coordinate n i) (P201Specs.coordinate n j))

/-- Mixed spatial derivatives commute for arbitrary Banach-valued smooth maps. -/
theorem spatialWord_perm {n : ℕ} {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : P201Specs.Space n → E} (ha : ContDiff ℝ ∞ a)
    {l l' : List (Fin n)} (h : l.Perm l') : spatialWord a l = spatialWord a l' := by
  induction h with
  | nil => rfl
  | cons j h ih => simp only [spatialWord, ih]
  | swap i j l => exact spatialWord_swap ha _ _ _
  | trans h h' ih ih' => exact ih.trans ih'

/-- Scalar words agree with the canonical upstream derivative convention. -/
theorem spatialWord_eq_partialWord {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (a : P201Specs.Space n → 𝕜) (l : List (Fin n)) :
    spatialWord a l = P102.U4.partialWord a l := by
  induction l with
  | nil => rfl
  | cons j l ih => simp only [spatialWord, P102.U4.partialWord, ih]

/-- Bounds stated for multi-indices control every derivative word, retaining
all repeated directions in a product-rule expansion. -/
theorem coefficient_word_bound {n m s : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {T K : ℝ} {a : LowerOrder n m 𝕜}
    (ha : BoundedSmoothCoefficient T s K a) {t : ℝ} (ht : t ∈ Icc 0 T)
    (l : List (Fin n)) (hl : l.length ≤ s) (x : P201Specs.Space n) :
    ‖spatialWord (a t) l x‖ ≤ K := by
  have hp : ((l : Multiset (Fin n)).sort (· ≤ ·)).Perm l :=
    Multiset.coe_eq_coe.mp (Multiset.sort_eq _ _)
  rw [← spatialWord_perm (coefficient_slice_contDiff ha.1 ht) hp]
  exact ha.2 (l : P201Specs.MultiIndex n) (by simpa using hl) t ht x

/-- Each coefficient spatial derivative is jointly continuous on the closed
slab under exactly the smoothness hypothesis in the source. -/
theorem coefficient_partial_continuousOn {n m s : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {T K : ℝ} (hT : 0 ≤ T) {a : LowerOrder n m 𝕜}
    (ha : BoundedSmoothCoefficient T s K a) (α : P201Specs.MultiIndex n) :
    ContinuousOn (fun z : ℝ × P201Specs.Space n => spatialPartial (a z.1) α z.2)
      (slab n T) :=
  spatialWord_continuousOn_slab hT ha.1 (α.sort (· ≤ ·))

/-- The fixed-spatial-point time continuity needed for dominated convergence. -/
theorem coefficient_word_time_continuousOn {n m s : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {T K : ℝ} (hT : 0 ≤ T) {a : LowerOrder n m 𝕜}
    (ha : BoundedSmoothCoefficient T s K a) (l : List (Fin n)) (x : P201Specs.Space n) :
    ContinuousOn (fun t => spatialWord (a t) l x) (Icc 0 T) := by
  exact (spatialWord_continuousOn_slab hT ha.1 l).comp
    (continuousOn_id.prodMk continuousOn_const) (fun t ht => ⟨ht, mem_univ x⟩)


end CoefficientCalculus

section ScalarProducts
open P102.U4 P201Specs.Hyperbolic.SymmetricEnergy
/-- Pointwise boundedness of each of the finitely many coefficient derivatives.
This predicate is a consequence of the source coefficient bounds. -/
def ScalarBoundedWords {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (a : SmoothCoefficient 𝕜 (⊤ : P201Specs.Domain n)) (k : ℕ) : Prop :=
  ∀ l : List (Fin n), l.length ≤ k → ∃ C : ℝ, ∀ x, ‖partialWord a.val l x‖ ≤ C

theorem scalarBoundedWords_partial {n k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {a : SmoothCoefficient 𝕜 (⊤ : P201Specs.Domain n)}
    (ha : ScalarBoundedWords a (k + 1)) (i : Fin n) :
    ScalarBoundedWords (coefficientPartial i a) k := by
  intro l hl
  obtain ⟨C, hC⟩ := ha (l ++ [i]) (by simp only [List.length_append, List.length_singleton]; omega)
  refine ⟨C, ?_⟩
  intro x
  change ‖partialWord (partialWord a.val [i]) l x‖ ≤ C
  rw [← partialWord_append]
  exact hC x

theorem scalarBoundedWords_mono {n k l : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {a : SmoothCoefficient 𝕜 (⊤ : P201Specs.Domain n)}
    (ha : ScalarBoundedWords a k) (hl : l ≤ k) : ScalarBoundedWords a l :=
  fun word hword => ha word (hword.trans hl)

/-- Bounded scalar smooth functions act on the actual Lp classes. -/
theorem exists_regular_smoothProduct {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (a : SmoothCoefficient 𝕜 (⊤ : P201Specs.Domain n))
    (ha : ∃ C : ℝ, ∀ x, ‖a.val x‖ ≤ C)
    (u : DomainLp 𝕜 (⊤ : P201Specs.Domain n) p) :
    ∃ w : DomainLp 𝕜 (⊤ : P201Specs.Domain n) p,
      P102.U4.regularDistribution ⊤ w = distributionMultiplier a (P102.U4.regularDistribution ⊤ u) ∧
      (w : P201Specs.Space n → 𝕜) =ᵐ[volume] fun x => a.val x * u x := by
  obtain ⟨C, hC⟩ := ha
  have hcont : Continuous a.val := (contDiffOn_univ.mp a.property).continuous
  have hm : MemLp (fun x => a.val x * u x) p
      (volume.restrict (⊤ : P201Specs.Domain n).carrier) :=
    (memLp_top_of_bound hcont.aestronglyMeasurable C
      (Filter.Eventually.of_forall hC)).mul (Lp.memLp u)
  refine ⟨hm.toLp _, ?_, ?_⟩
  · ext ψ
    rw [distributionMultiplier_apply, regular_pairing n 𝕜 ⊤ _
      (domainLp_locallyIntegrable ⊤ p _), regular_pairing n 𝕜 ⊤ _
      (domainLp_locallyIntegrable ⊤ p _)]
    apply integral_congr_ae
    filter_upwards [hm.coeFn_toLp] with x hx
    change hm.toLp _ x * ψ x = u x * (a.val x * ψ x)
    rw [hx]
    ring
  · simpa only [show (⊤ : P201Specs.Domain n).carrier = Set.univ from rfl, Measure.restrict_univ] using hm.coeFn_toLp

/-- Each branch of the finite iterated product rule is represented by Lp.
No certificate about derivatives of the product is assumed. -/
theorem scalarLeibnizExpansion_hasLp {n k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : Sobolev 𝕜 (⊤ : P201Specs.Domain n) k p) (l : List (Fin n)) :
    ∀ (a : SmoothCoefficient 𝕜 (⊤ : P201Specs.Domain n)) (β : MultiIndex n),
      ScalarBoundedWords a l.length → β.card + l.length ≤ k →
    ∃ w : DomainLp 𝕜 (⊤ : P201Specs.Domain n) p, P102.U4.regularDistribution ⊤ w =
      leibnizExpansion testMultiplier l a
        (distributionPartial β (P102.U4.regularDistribution ⊤ (sobolevUnderlying u))) := by
  induction l with
  | nil =>
    intro a β ha hβ
    have hβk : β.card ≤ k := by simpa using hβ
    obtain ⟨w, hw, _⟩ := exists_regular_smoothProduct a (by simpa [partialWord] using ha [] (by simp))
      (sobolevDerivative u ⟨β, hβk⟩)
    refine ⟨w, ?_⟩
    rw [sobolev_derivative_distribution ⊤ k p u ⟨β, hβk⟩]
    exact hw
  | cons i l ih =>
    intro a β ha hβ
    have hleft : β.card + l.length ≤ k := by simp only [List.length_cons] at hβ; omega
    have hright : ({i} + β).card + l.length ≤ k := by
      simp only [Multiset.card_add, Multiset.card_singleton]
      simp only [List.length_cons] at hβ
      omega
    obtain ⟨w₁, hw₁⟩ := ih (coefficientPartial i a) β (scalarBoundedWords_partial ha i) hleft
    obtain ⟨w₂, hw₂⟩ := ih a ({i} + β) (scalarBoundedWords_mono ha (by simp)) hright
    refine ⟨w₁ + w₂, ?_⟩
    have hadd : P102.U4.regularDistribution ⊤ (w₁ + w₂) = P102.U4.regularDistribution ⊤ w₁ + P102.U4.regularDistribution ⊤ w₂ := by
      ext ψ
      simp only [add_apply, regularLp_pairing ⊤ p]
      exact map_add (lpTestPairing ⊤ p ψ) w₁ w₂
    rw [hadd, hw₁, hw₂]
    change _ = leibnizExpansion testMultiplier l (coefficientPartial i a)
        (distributionPartial β (P102.U4.regularDistribution ⊤ (sobolevUnderlying u))) +
      leibnizExpansion testMultiplier l a (distributionPartial {i}
        (distributionPartial β (P102.U4.regularDistribution ⊤ (sobolevUnderlying u))))
    rw [← derivative_add n 𝕜 ⊤ {i} β]

/-- A scalar bounded smooth coefficient preserves the genuine distribution-defined H^k. -/
theorem exists_h_smoothProduct {n k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (a : SmoothCoefficient 𝕜 (⊤ : P201Specs.Domain n))
    (ha : ScalarBoundedWords a k) (u : P201Specs.H 𝕜 (⊤ : P201Specs.Domain n) k) :
    ∃ v : P201Specs.H 𝕜 (⊤ : P201Specs.Domain n) k,
      (P201Specs.hUnderlying ⊤ k v : P201Specs.Space n → 𝕜) =ᵐ[volume]
        fun x => a.val x * P201Specs.hUnderlying ⊤ k u x := by
  obtain ⟨w, hw, hwae⟩ := exists_regular_smoothProduct a
    (by simpa [partialWord] using ha [] (by simp)) (P201Specs.hUnderlying ⊤ k u)
  have hwrange : w ∈ Set.range (@sobolevUnderlying n 𝕜 _ ⊤ k 2 _) := by
    rw [sobolev_range ⊤ k 2]
    intro α hα
    obtain ⟨z, hz⟩ := scalarLeibnizExpansion_hasLp (P201Specs.hToW 𝕜 ⊤ k u)
      (α.sort (· ≤ ·)) a 0 (scalarBoundedWords_mono ha (by simpa using hα)) (by simpa using hα)
    refine ⟨z, ?_⟩
    rw [hw, distributionMultiplier_iteratedProductRule]
    rw [derivative_zero] at hz
    exact hz.symm
  obtain ⟨v, hv⟩ := hwrange
  refine ⟨(P201Specs.hToW 𝕜 ⊤ k).symm v, ?_⟩
  change (sobolevUnderlying v : P201Specs.Space n → 𝕜) =ᵐ[volume] _
  rw [hv]
  exact hwae

open P201Specs.Hyperbolic.SymmetricSobolevEnergy
open P201Specs.Hyperbolic.SymmetricEnergy

/-- Matrix entries use the actual Euclidean coordinate vectors. -/
def matrixEntry {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (M : Operator m 𝕜) (i j : Fin m) : 𝕜 := M (PiLp.single 2 j 1) i

theorem operator_apply_eq_entrySum {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (M : Operator m 𝕜) (z : Fiber 𝕜 m) (i : Fin m) :
    M z i = ∑ j : Fin m, matrixEntry M i j * z j := by
  classical
  have hz : z = ∑ j : Fin m, z j • (PiLp.single 2 j 1 : Fiber 𝕜 m) := by
    apply PiLp.ext
    intro j
    simp [Pi.single_apply]
  conv_lhs => rw [hz]
  simp [matrixEntry, mul_comm]

/-- The finite matrix assembly gives a genuine H^k multiplier value. The
hypotheses on scalar entries are later discharged by the coefficient jets. -/
theorem exists_whole_smoothProduct {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (a : P201Specs.Space n → Operator m 𝕜)
    (hentry : ∀ i j : Fin m, ContDiff ℝ ∞ (fun x => matrixEntry (a x) i j))
    (hbound : ∀ i j : Fin m,
      ScalarBoundedWords ⟨fun x => matrixEntry (a x) i j, (hentry i j).contDiffOn⟩ k)
    (u : WholeH n m 𝕜 k) :
    ∃ v : WholeH n m 𝕜 k,
      underlyingSection v =ᵐ[volume] fun x => a x (underlyingSection u x) := by
  classical
  have hex (i j : Fin m) := exists_h_smoothProduct
    ⟨fun x => matrixEntry (a x) i j, (hentry i j).contDiffOn⟩ (hbound i j) (u j)
  choose v hv using hex
  refine ⟨WithLp.toLp 2 (fun i => ∑ j : Fin m, v i j), ?_⟩
  have hsum (i : Fin m) : ∀ᵐ x ∂volume,
      P201Specs.hUnderlying ⊤ k (∑ j : Fin m, v i j) x =
        ∑ j : Fin m, matrixEntry (a x) i j * P201Specs.hUnderlying ⊤ k (u j) x := by
    have hrep := Lp.coeFn_fun_finsetSum Finset.univ
      (fun j : Fin m => P201Specs.hUnderlying ⊤ k (v i j))
    simp only [P201Specs.domainMeasure, Opens.coe_top, Measure.restrict_univ] at hrep
    have hall := MeasureTheory.ae_all_iff.mpr (hv i)
    filter_upwards [hrep, hall] with x hx hall
    simpa only [map_sum] using hx.trans (Finset.sum_congr rfl (fun j _ => hall j))
  have hall := MeasureTheory.ae_all_iff.mpr hsum
  filter_upwards [hall] with x hx
  apply PiLp.ext
  intro i
  change P201Specs.hUnderlying ⊤ k (∑ j : Fin m, v i j) x = _
  rw [hx i, operator_apply_eq_entrySum]
  rfl


end ScalarProducts

namespace LpMultiplier
variable {X 𝕜 E F : Type*} [MeasurableSpace X] {μ : Measure X}
 [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
 [NormedAddCommGroup F] [NormedSpace 𝕜 F]

private theorem action_memLp (a : X → E →L[𝕜] F)
 (ha : AEStronglyMeasurable a μ) (K : ℝ) (hK : ∀ᵐ x ∂μ, ‖a x‖ ≤ K)
 (f : MeasureTheory.Lp E 2 μ) : MemLp (fun x => a x (f x)) 2 μ := by
  apply (MeasureTheory.Lp.memLp f).of_le_mul ((isBoundedBilinearMap_apply (𝕜 := 𝕜) (E := E) (F := F)).continuous.comp_aestronglyMeasurable (ha.prodMk (MeasureTheory.Lp.aestronglyMeasurable f)))
  filter_upwards [hK] with x hx
  exact (a x).le_opNorm (f x) |>.trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))

noncomputable def action (a : X → E →L[𝕜] F)
 (ha : AEStronglyMeasurable a μ) (K : ℝ) (hK : ∀ᵐ x ∂μ, ‖a x‖ ≤ K)
 (f : MeasureTheory.Lp E 2 μ) : MeasureTheory.Lp F 2 μ :=
 (action_memLp a ha K hK f).toLp (fun x => a x (f x))

theorem action_ae (a : X → E →L[𝕜] F)
 (ha : AEStronglyMeasurable a μ) (K : ℝ) (hK : ∀ᵐ x ∂μ, ‖a x‖ ≤ K)
 (f : MeasureTheory.Lp E 2 μ) : action a ha K hK f =ᵐ[μ] fun x => a x (f x) :=
 MemLp.coeFn_toLp _

theorem action_norm_le (a : X → E →L[𝕜] F)
 (ha : AEStronglyMeasurable a μ) (K : ℝ) (hK : ∀ᵐ x ∂μ, ‖a x‖ ≤ K)
 (f : MeasureTheory.Lp E 2 μ) : ‖action a ha K hK f‖ ≤ K * ‖f‖ := by
 apply MeasureTheory.Lp.norm_le_mul_norm_of_ae_le_mul
 filter_upwards [action_ae a ha K hK f, hK] with x hx hk
 rw [hx]
 exact (a x).le_opNorm (f x) |>.trans (mul_le_mul_of_nonneg_right hk (norm_nonneg _))

noncomputable def multiplier (a : X → E →L[𝕜] F)
 (ha : AEStronglyMeasurable a μ) (K : ℝ) (hK : ∀ᵐ x ∂μ, ‖a x‖ ≤ K) :
 MeasureTheory.Lp E 2 μ →L[𝕜] MeasureTheory.Lp F 2 μ :=
 LinearMap.mkContinuous
 { toFun := action a ha K hK
   map_add' := by
     intro f g
     apply MeasureTheory.Lp.ext
     filter_upwards [action_ae a ha K hK (f + g), action_ae a ha K hK f,
       action_ae a ha K hK g, MeasureTheory.Lp.coeFn_add f g,
       MeasureTheory.Lp.coeFn_add (action a ha K hK f) (action a ha K hK g)] with x h1 h2 h3 h4 h5
     rw [h1, h5, h4]
     change a x (f x + g x) = action a ha K hK f x + action a ha K hK g x
     rw [map_add, h2, h3]
   map_smul' := by
     intro c f
     change action a ha K hK (c • f) = c • action a ha K hK f
     apply MeasureTheory.Lp.ext
     filter_upwards [action_ae a ha K hK (c • f), action_ae a ha K hK f,
       MeasureTheory.Lp.coeFn_smul c f, MeasureTheory.Lp.coeFn_smul c (action a ha K hK f)] with x h1 h2 h3 h4
     rw [h1, h4, h3]
     change a x (c • f x) = c • action a ha K hK f x
     rw [map_smul, h2] }
 K (action_norm_le a ha K hK)

theorem multiplier_norm_le (a : X → E →L[𝕜] F)
 (ha : AEStronglyMeasurable a μ) (K : ℝ) (hK0 : 0 ≤ K) (hK : ∀ᵐ x ∂μ, ‖a x‖ ≤ K) :
 ‖multiplier a ha K hK‖ ≤ K := by
 apply ContinuousLinearMap.opNorm_le_bound (multiplier a ha K hK) hK0
 exact action_norm_le a ha K hK

theorem continuous_action {Y : Type*} [TopologicalSpace Y] [FirstCountableTopology Y]
 (a : Y → X → E →L[𝕜] F)
 (ha : ∀ t, AEStronglyMeasurable (a t) μ)
 (K : ℝ) (hK0 : 0 ≤ K) (hK : ∀ t, ∀ᵐ x ∂μ, ‖a t x‖ ≤ K)
 (hc : ∀ᵐ x ∂μ, Continuous (fun t => a t x))
 (f : MeasureTheory.Lp E 2 μ) : Continuous (fun t => action (a t) (ha t) K (hK t) f) := by
 apply continuous_iff_continuousAt.2
 intro t₀
 let g : Y → X → ℝ := fun t x => ‖a t x (f x) - a t₀ x (f x)‖ ^ 2
 have hgm (t : Y) : AEStronglyMeasurable (g t) μ :=
   ((action_memLp (a t) (ha t) K (hK t) f).aestronglyMeasurable.sub
     (action_memLp (a t₀) (ha t₀) K (hK t₀) f).aestronglyMeasurable).norm.pow 2
 have hgb (t : Y) : ∀ᵐ x ∂μ, ‖g t x‖ ≤ (2 * K) ^ 2 * ‖f x‖ ^ 2 := by
   filter_upwards [hK t, hK t₀] with x ht ht₀
   have hb (r : Y) (hr : ‖a r x‖ ≤ K) : ‖a r x (f x)‖ ≤ K * ‖f x‖ :=
     (a r x).le_opNorm (f x) |>.trans (mul_le_mul_of_nonneg_right hr (norm_nonneg _))
   have hn : ‖a t x (f x) - a t₀ x (f x)‖ ≤ 2 * K * ‖f x‖ := by
     have := norm_sub_le (a t x (f x)) (a t₀ x (f x))
     linarith [hb t ht, hb t₀ ht₀]
   dsimp [g]
   rw [abs_of_nonneg (sq_nonneg _), ← mul_pow]
   exact pow_le_pow_left₀ (norm_nonneg _) hn 2
 have hgc : ∀ᵐ x ∂μ, Continuous (fun t => g t x) := by
   filter_upwards [hc] with x hx
   exact ((hx.clm_apply continuous_const).sub continuous_const).norm.pow 2
 have hi : Integrable (fun x => (2 * K) ^ 2 * ‖f x‖ ^ 2) μ :=
   ((MeasureTheory.Lp.memLp f).integrable_norm_pow (by norm_num)).const_mul _
 have hg : Continuous (fun t => ∫ x, g t x ∂μ) :=
   continuous_of_dominated hgm hgb hi hgc
 have heq (t : Y) : dist (action (a t) (ha t) K (hK t) f)
     (action (a t₀) (ha t₀) K (hK t₀) f) = Real.sqrt (∫ x, g t x ∂μ) := by
   rw [dist_eq_norm, MeasureTheory.Lp.norm_def]
   have hae : (⇑(action (a t) (ha t) K (hK t) f -
       action (a t₀) (ha t₀) K (hK t₀) f)) =ᵐ[μ]
       fun x => a t x (f x) - a t₀ x (f x) := by
     filter_upwards [MeasureTheory.Lp.coeFn_sub (action (a t) (ha t) K (hK t) f)
       (action (a t₀) (ha t₀) K (hK t₀) f),
       action_ae (a t) (ha t) K (hK t) f,
       action_ae (a t₀) (ha t₀) K (hK t₀) f] with x h1 h2 h3
     simpa [h2, h3] using h1
   rw [eLpNorm_congr_ae hae]
   change lpNorm _ 2 μ = _
   have hfm : AEStronglyMeasurable (fun x => a t x (f x) - a t₀ x (f x)) μ :=
     ((action_memLp (a t) (ha t) K (hK t) f).sub
       (action_memLp (a t₀) (ha t₀) K (hK t₀) f)).aestronglyMeasurable
   rw [lpNorm_eq_integral_norm_rpow_toReal (p := 2) (by norm_num) (by norm_num) hfm]
   norm_num [g, Real.sqrt_eq_rpow]
 apply (tendsto_iff_dist_tendsto_zero).2
 have hz : (∫ x, g t₀ x ∂μ) = 0 := by simp [g]
 have ht := (hg.continuousAt (x := t₀)).tendsto.sqrt
 simpa only [← heq, hz, Real.sqrt_zero] using ht
end LpMultiplier


open P201Specs P201Specs.Hyperbolic.SymmetricEnergy P201Specs.Hyperbolic.SymmetricSobolevEnergy
namespace CoefLp
variable {n m s : ℕ} {𝕜 : Type} [RCLike 𝕜] {T K : ℝ}
 (a : LowerOrder n m 𝕜) (ha : BoundedSmoothCoefficient T s K a)
include ha

theorem coefficient_bound (t : ℝ) (ht : t ∈ Icc 0 T) (x : Space n) : ‖a t x‖ ≤ K := by
 simpa [spatialPartial, spatialWord] using ha.2 0 (by simp) t ht x

theorem coefficient_slice_continuous (t : ℝ) (ht : t ∈ Icc 0 T) : Continuous (a t) := by
 have hc := ha.1.continuousOn
 exact hc.comp_continuous (continuous_const.prodMk continuous_id) (fun x => ⟨ht, mem_univ x⟩)

theorem coefficient_time_continuous (x : Space n) :
 Continuous (fun t : Icc (0:ℝ) T => a t x) := by
 exact ha.1.continuousOn.comp_continuous
   (continuous_subtype_val.prodMk continuous_const) (fun t => ⟨t.property, mem_univ x⟩)

theorem coefficient_l2_multiplier (hK : 0 ≤ K) :
 ∃ M : ℝ → MeasureTheory.Lp (Fiber 𝕜 m) 2 (volume : Measure (Space n)) →L[𝕜]
     MeasureTheory.Lp (Fiber 𝕜 m) 2 (volume : Measure (Space n)),
   (∀ t ∈ Icc 0 T, ‖M t‖ ≤ K ∧ ∀ v, M t v =ᵐ[volume] fun x => a t x (v x)) ∧
   ∀ v, ContinuousOn (fun t => M t v) (Icc 0 T) := by
 let am : ∀ t : Icc (0:ℝ) T, AEStronglyMeasurable (a t) volume := fun t =>
   (coefficient_slice_continuous a ha t t.property).aestronglyMeasurable
 let ab : ∀ t : Icc (0:ℝ) T, ∀ᵐ x ∂volume, ‖a t x‖ ≤ K := fun t =>
   Eventually.of_forall (coefficient_bound a ha t t.property)
 let N := fun t : Icc (0:ℝ) T => LpMultiplier.multiplier (a t) (am t) K (ab t)
 let M := fun t : ℝ => if ht : t ∈ Icc 0 T then N ⟨t, ht⟩ else 0
 refine ⟨M, ?_, ?_⟩
 · intro t ht
   dsimp [M]
   rw [dite_eq_left ht]
   refine ⟨LpMultiplier.multiplier_norm_le _ _ K hK _, ?_⟩
   intro v
   exact LpMultiplier.action_ae (a t) (am ⟨t, ht⟩) K (ab ⟨t, ht⟩) v
 · intro v
   rw [continuousOn_iff_continuous_domRestrict]
   have h := LpMultiplier.continuous_action (fun t : Icc (0:ℝ) T => a t) am K hK ab
     (Eventually.of_forall (coefficient_time_continuous a ha)) v
   convert h using 1
   funext t
   dsimp [M, N, LpMultiplier.multiplier]
   rw [dite_eq_left t.property]
   rfl
end CoefLp


section SpatialPairing
open Filter
open P201Specs.Hyperbolic.SymmetricEnergy

/-- The integral of an integrable line derivative of an integrable function
vanishes; both integrability assumptions are essential. -/
theorem integral_line_derivative_eq_zero {n : ℕ}
    {q dq : P201Specs.Space n → ℝ} (v : P201Specs.Space n)
    (hq : Integrable q) (hdq : Integrable dq)
    (hd : ∀ x, HasLineDerivAt ℝ q (dq x) x v) :
    ∫ x, dq x = 0 := by
  have h := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (f := fun _ : P201Specs.Space n => (1 : ℝ)) (f' := fun _ => (0 : ℝ))
    (g := q) (g' := dq) (v := v) (B := ContinuousLinearMap.mul ℝ ℝ)
    (by simpa using (integrable_zero : Integrable (fun _ : P201Specs.Space n => (0 : ℝ))))
    (by simpa using hdq) (by simpa using hq)
    (fun x _ => by simp only [HasLineDerivAt]; exact hasDerivAt_const 0 1)
    (fun x _ => hd x)
  simpa using h

/-- L² inputs paired through a measurable uniformly bounded coefficient have
an integrable scalar real pairing, with a dimension independent bound. -/
theorem integrable_real_operator_pairing {n m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {A : P201Specs.Space n → Operator m 𝕜}
    {u v : P201Specs.Space n → Fiber 𝕜 m} {K : ℝ}
    (hA : AEStronglyMeasurable A) (hb : ∀ x, ‖A x‖ ≤ K)
    (hu : MemLp u 2) (hv : MemLp v 2) :
    Integrable (fun x => RCLike.re (inner 𝕜 (u x) (A x (v x)))) := by
  have hp : Integrable (fun x => K * (‖u x‖ * ‖v x‖)) :=
    (hu.norm.integrable_mul hv.norm).const_mul K
  apply hp.mono'
  · exact (hu.aestronglyMeasurable.inner
      (P201.Hyperbolic.SymmetricEnergy.operator_apply_bilinear_real.continuous.comp_aestronglyMeasurable
        (hA.prodMk hv.aestronglyMeasurable))).re
  · filter_upwards [] with x
    calc
      ‖RCLike.re (inner 𝕜 (u x) (A x (v x)))‖ ≤ ‖inner 𝕜 (u x) (A x (v x))‖ :=
        RCLike.norm_re_le_norm _
      _ ≤ ‖u x‖ * ‖A x (v x)‖ := norm_inner_le_norm _ _
      _ ≤ ‖u x‖ * (K * ‖v x‖) := mul_le_mul_of_nonneg_left
        ((A x).le_opNorm (v x) |>.trans (mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _)))
        (norm_nonneg _)
      _ = K * (‖u x‖ * ‖v x‖) := by ring

/-- Exact symmetric spatial cancellation on the whole space.  The hypotheses
state the actual pointwise line derivatives and the integrability needed to
remove the flux; no time regularity or compact support is required. -/
theorem symmetric_principal_integral {n m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {A dA : P201Specs.Space n → Operator m 𝕜}
    {u du : P201Specs.Space n → Fiber 𝕜 m} (v : P201Specs.Space n)
    (hA : ∀ x, HasLineDerivAt ℝ A (dA x) x v)
    (hu : ∀ x, HasLineDerivAt ℝ u (du x) x v)
    (hsym : ∀ x, IsSelfAdjoint (A x))
    (hflux : Integrable (fun x => RCLike.re (inner 𝕜 (u x) (A x (u x))) / 2))
    (hcoeff : Integrable (fun x => RCLike.re (inner 𝕜 (u x) (dA x (u x))) / 2))
    (hprincipal : Integrable (fun x => RCLike.re (inner 𝕜 (u x) (A x (du x))))) :
    (∫ x, RCLike.re (inner 𝕜 (u x) (A x (du x)))) =
      -(∫ x, RCLike.re (inner 𝕜 (u x) (dA x (u x))) / 2) := by
  have hzero := integral_line_derivative_eq_zero v hflux (hcoeff.add hprincipal)
    (fun x => by
      convert P201.Hyperbolic.SymmetricEnergy.hasDerivAt_symmetric_flux
          (hA x) (hu x) (by simpa using hsym x) using 1 <;>
        simp only [HasLineDerivAt, zero_smul, add_zero, Pi.add_apply])
  simp only [Pi.add_apply] at hzero
  rw [integral_add hcoeff hprincipal] at hzero
  linarith

/-- The classical symmetric energy cancellation with its actual L² bound. -/
theorem symmetric_principal_integral_bound {n m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {A dA : P201Specs.Space n → Operator m 𝕜}
    {u du : P201Specs.Space n → Fiber 𝕜 m} {K M : ℝ}
    (v : P201Specs.Space n) (hK : 0 ≤ K)
    (hA : ∀ x, HasLineDerivAt ℝ A (dA x) x v)
    (hu : ∀ x, HasLineDerivAt ℝ u (du x) x v)
    (hsym : ∀ x, IsSelfAdjoint (A x))
    (hmA : AEStronglyMeasurable A) (hmdA : AEStronglyMeasurable dA)
    (hbA : ∀ x, ‖A x‖ ≤ M) (hbdA : ∀ x, ‖dA x‖ ≤ K)
    (huLp : MemLp u 2) (hduLp : MemLp du 2) :
    |∫ x, RCLike.re (inner 𝕜 (u x) (A x (du x)))| ≤
      (K / 2) * (lpNorm u 2 volume) ^ 2 := by
  have hflux := (integrable_real_operator_pairing hmA hbA huLp huLp).div_const 2
  have hcoeff := (integrable_real_operator_pairing hmdA hbdA huLp huLp).div_const 2
  have hprincipal := integrable_real_operator_pairing hmA hbA huLp hduLp
  rw [symmetric_principal_integral v hA hu hsym hflux hcoeff hprincipal, abs_neg]
  have hsq : Integrable (fun x => ‖u x‖ ^ 2) := huLp.integrable_norm_pow (by norm_num)
  have hpw (x : P201Specs.Space n) :
      ‖RCLike.re (inner 𝕜 (u x) (dA x (u x))) / 2‖ ≤ (K / 2) * ‖u x‖ ^ 2 := by
    have hb := (P201.Hyperbolic.SymmetricEnergy.realPart_quadratic_bound
      (dA x) (u x)).trans (mul_le_mul_of_nonneg_right (hbdA x) (sq_nonneg _))
    rw [norm_div, Real.norm_eq_abs, Real.norm_ofNat]
    nlinarith
  have hi := norm_integral_le_of_norm_le (hsq.const_mul (K / 2)) (ae_of_all _ hpw)
  rw [Real.norm_eq_abs, integral_const_mul] at hi
  have hnorm : (lpNorm u 2 volume) ^ 2 = ∫ x, ‖u x‖ ^ 2 := by
    rw [P201.Hyperbolic.SymmetricEnergy.lpNorm_two_eq_sqrt_integral huLp.aestronglyMeasurable,
      Real.sq_sqrt (integral_nonneg (fun x => sq_nonneg ‖u x‖))]
  simpa only [hnorm] using hi


end SpatialPairing

section SmoothDensity
open Filter
open P201Specs.Hyperbolic.SymmetricSobolevEnergy

/-- Whole-space compact smooth density transferred to the actual Hilbert
Sobolev space, component by component. The derivative representatives remain
specified, and convergence is in the full derivative-square norm. -/
theorem wholeH_smooth_density {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (u : WholeH n m 𝕜 k) :
    ∃ (φ : ℕ → Fin m → P102.U4.WholeTests n 𝕜) (v : ℕ → WholeH n m 𝕜 k),
      (∀ r i, P102.U4.RepresentsSobolev (φ r i) (P201Specs.hToW 𝕜 ⊤ k (v r i))) ∧
      Tendsto v atTop (𝓝 u) := by
  have hd (i : Fin m) := P102.U4.wholeSpace_density k 2 (by norm_num)
    (P201Specs.hToW 𝕜 ⊤ k (u i))
  choose φ w hwrep hwconv hwerr using hd
  let v : ℕ → WholeH n m 𝕜 k := fun r => WithLp.toLp 2
    (fun i => (P201Specs.hToW 𝕜 ⊤ k).symm (w i r))
  refine ⟨fun r i => φ i r, v, ?_, ?_⟩
  · intro r i
    simpa only [v, ContinuousLinearEquiv.apply_symm_apply] using hwrep i r
  · have hc (i : Fin m) : Tendsto (fun r => v r i) atTop (𝓝 (u i)) := by
      simpa only [v, ContinuousLinearEquiv.symm_apply_apply, Function.comp_def] using
        ((P201Specs.hToW 𝕜 ⊤ k).symm.continuous.tendsto
          (P201Specs.hToW 𝕜 ⊤ k (u i))).comp (hwconv i)
    have ht := (PiLp.continuous_toLp 2 (fun _ : Fin m => P201Specs.H 𝕜 ⊤ k)).tendsto
      (fun i => u i)
    simpa only [Function.comp_def, WithLp.toLp_ofLp] using
      ht.comp (tendsto_pi_nhds.mpr hc)

/-- A bound verified on the compact smooth dense subset extends through the
actual bounded operators and inclusion. This is the final density step after
the differential commutator and symmetric principal-term estimates. -/
theorem pairing_bound_of_smooth {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Q : WholeH n m 𝕜 (k + 1) →L[𝕜] WholeH n m 𝕜 k) (C : ℝ)
    (hb : ∀ (φ : Fin m → P102.U4.WholeTests n 𝕜)
      (v : WholeH n m 𝕜 (k + 1)),
      (∀ i, P102.U4.RepresentsSobolev (φ i)
        (P201Specs.hToW 𝕜 ⊤ (k + 1) (v i))) →
      |RCLike.re (inner 𝕜 (lowerOrderCLM v) (Q v))| ≤ C * ‖lowerOrderCLM v‖ ^ 2) :
    ∀ (v : WholeH n m 𝕜 (k + 1)) (w : WholeH n m 𝕜 k),
      IsLowerOrder v w → |RCLike.re (inner 𝕜 w (Q v))| ≤ C * ‖w‖ ^ 2 := by
  intro v w hw
  have heq : w = lowerOrderCLM v := by
    apply PiLp.ext
    intro i
    apply P201.hilbertUnderlyingInjective ⊤ k
    exact (hw i).symm.trans (lowerOrderCLM_realizes v i)
  rw [heq]
  obtain ⟨φ, u, hrep, hconv⟩ := wholeH_smooth_density v
  have hclosed : IsClosed {z : WholeH n m 𝕜 (k + 1) |
      |RCLike.re (inner 𝕜 (lowerOrderCLM z) (Q z))| ≤ C * ‖lowerOrderCLM z‖ ^ 2} := by
    apply isClosed_le
    · exact (RCLike.continuous_re.comp (lowerOrderCLM.continuous.inner Q.continuous)).abs
    · exact continuous_const.mul (lowerOrderCLM.continuous.norm.pow 2)
  exact hclosed.mem_of_tendsto hconv (Eventually.of_forall (fun r => hb (φ r) (u r) (hrep r)))


end SmoothDensity


section MatrixMembership
open P201Specs.Hyperbolic.SymmetricSobolevEnergy P201Specs.Hyperbolic.SymmetricEnergy
open P102.U4

/-- Each finite matrix entry is bounded by the operator norm, without a
factor depending on the fiber dimension. -/
theorem matrixEntry_norm_le {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (M : Operator m 𝕜) (i j : Fin m) : ‖matrixEntry M i j‖ ≤ ‖M‖ := by
  calc
    _ ≤ ‖M (PiLp.single 2 j 1)‖ := PiLp.norm_apply_le _ i
    _ ≤ ‖M‖ * ‖(PiLp.single 2 j 1 : Fiber 𝕜 m)‖ := M.le_opNorm _
    _ = _ := by rw [PiLp.norm_single]; simp

/-- Fixed entry evaluation, as a continuous real-linear map for differentiation. -/
def matrixEntryCLM {m : ℕ} {𝕜 : Type} [RCLike 𝕜] (i j : Fin m) :
    Operator m 𝕜 →L[ℝ] 𝕜 :=
  LinearMap.mkContinuous
    { toFun := fun M => matrixEntry M i j
      map_add' := by intro M N; rfl
      map_smul' := by intro r M; rfl }
    1 (fun M => by
      change ‖matrixEntry M i j‖ ≤ 1 * ‖M‖
      simpa only [one_mul] using matrixEntry_norm_le M i j)

theorem matrixEntry_contDiff {n m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {a : P201Specs.Space n → Operator m 𝕜} (ha : ContDiff ℝ ∞ a) (i j : Fin m) :
    ContDiff ℝ ∞ (fun x => matrixEntry (a x) i j) := by
  change ContDiff ℝ ∞ (matrixEntryCLM i j ∘ a)
  exact (matrixEntryCLM i j).contDiff.comp ha

/-- Operator-valued spatial word bounds imply the scalar entry bounds used in
the weak derivative construction. -/
theorem matrixEntry_boundedWords {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {a : P201Specs.Space n → Operator m 𝕜} (ha : ContDiff ℝ ∞ a)
    (hb : ∀ l : List (Fin n), l.length ≤ k → ∃ C : ℝ, ∀ x, ‖spatialWord a l x‖ ≤ C)
    (i j : Fin m) :
    ScalarBoundedWords ⟨fun x => matrixEntry (a x) i j,
      (matrixEntry_contDiff ha i j).contDiffOn⟩ k := by
  intro l hl
  obtain ⟨C, hC⟩ := hb l hl
  refine ⟨C, ?_⟩
  intro x
  change ‖partialWord (fun x => matrixEntry (a x) i j) l x‖ ≤ C
  rw [← spatialWord_eq_partialWord]
  change ‖spatialWord (fun x => matrixEntryCLM i j (a x)) l x‖ ≤ C
  rw [spatialWord_comp_clm (matrixEntryCLM i j) ha]
  exact (matrixEntry_norm_le _ i j).trans (hC x)

/-- Preservation of the actual vector Sobolev space by bounded smooth
coefficients, derived from the distributional Leibniz rule. -/
theorem exists_whole_smoothProduct_of_wordBounds {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (a : P201Specs.Space n → Operator m 𝕜) (ha : ContDiff ℝ ∞ a)
    (hb : ∀ l : List (Fin n), l.length ≤ k → ∃ C : ℝ, ∀ x, ‖spatialWord a l x‖ ≤ C)
    (u : WholeH n m 𝕜 k) :
    ∃ v : WholeH n m 𝕜 k,
      underlyingSection v =ᵐ[volume] fun x => a x (underlyingSection u x) := by
  exact exists_whole_smoothProduct a
    (matrixEntry_contDiff ha)
    (matrixEntry_boundedWords ha hb) u

/-- The source assumptions suffice for Sobolev product membership at every
order through s, including the zero derivative. -/
theorem coefficient_product_mem {n m s k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {T K : ℝ} {a : LowerOrder n m 𝕜}
    (ha : BoundedSmoothCoefficient T s K a) {t : ℝ} (ht : t ∈ Icc 0 T)
    (hk : k ≤ s) (u : WholeH n m 𝕜 k) :
    ∃ v : WholeH n m 𝕜 k,
      underlyingSection v =ᵐ[volume] fun x => a t x (underlyingSection u x) := by
  apply exists_whole_smoothProduct_of_wordBounds (a t) (coefficient_slice_contDiff ha.1 ht)
  intro l hl
  exact ⟨K, coefficient_word_bound ha ht l (hl.trans hk)⟩

/-- Scalar multiplication of a Sobolev element is pointwise scalar
multiplication of its underlying a.e. section. -/
theorem underlyingSection_smul {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (c : 𝕜) (u : WholeH n m 𝕜 k) :
    underlyingSection (c • u) =ᵐ[volume] c • underlyingSection u := by
  have h (i : Fin m) : ∀ᵐ x ∂volume,
      P201Specs.hUnderlying ⊤ k (c • u i) x = c • P201Specs.hUnderlying ⊤ k (u i) x := by
    rw [map_smul]
    simpa only [Filter.EventuallyEq, P201Specs.domainMeasure, Opens.coe_top, Measure.restrict_univ,
      Pi.smul_apply] using Lp.coeFn_smul c (P201Specs.hUnderlying ⊤ k (u i))
  filter_upwards [ae_all_iff.mpr h] with x hx
  exact PiLp.ext (fun i => hx i)

/-- The product is uniquely specified by its actual a.e. action. -/
def smoothMultiplierValue {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (a : P201Specs.Space n → Operator m 𝕜) (ha : ContDiff ℝ ∞ a)
    (hb : ∀ l : List (Fin n), l.length ≤ k → ∃ C : ℝ, ∀ x, ‖spatialWord a l x‖ ≤ C)
    (u : WholeH n m 𝕜 k) : WholeH n m 𝕜 k :=
  (exists_whole_smoothProduct_of_wordBounds a ha hb u).choose

theorem smoothMultiplierValue_realizes {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (a : P201Specs.Space n → Operator m 𝕜) (ha : ContDiff ℝ ∞ a)
    (hb : ∀ l : List (Fin n), l.length ≤ k → ∃ C : ℝ, ∀ x, ‖spatialWord a l x‖ ≤ C)
    (u : WholeH n m 𝕜 k) :
    underlyingSection (smoothMultiplierValue a ha hb u) =ᵐ[volume]
      fun x => a x (underlyingSection u x) :=
  (exists_whole_smoothProduct_of_wordBounds a ha hb u).choose_spec

/-- The constructed Sobolev multiplier is a genuine linear map. Boundedness
and time continuity are separate quantitative conclusions. -/
def smoothMultiplierLinear {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (a : P201Specs.Space n → Operator m 𝕜) (ha : ContDiff ℝ ∞ a)
    (hb : ∀ l : List (Fin n), l.length ≤ k → ∃ C : ℝ, ∀ x, ‖spatialWord a l x‖ ≤ C) :
    WholeH n m 𝕜 k →ₗ[𝕜] WholeH n m 𝕜 k where
  toFun := smoothMultiplierValue a ha hb
  map_add' u v := by
    apply underlying_injective
    filter_upwards [smoothMultiplierValue_realizes a ha hb (u + v),
      underlyingSection_add (smoothMultiplierValue a ha hb u) (smoothMultiplierValue a ha hb v),
      smoothMultiplierValue_realizes a ha hb u, smoothMultiplierValue_realizes a ha hb v,
      underlyingSection_add u v] with x h1 h2 h3 h4 h5
    rw [h1, h2, h5]
    change a x (underlyingSection u x + underlyingSection v x) = _
    rw [map_add]
    simp only [Pi.add_apply, h3, h4]
  map_smul' c u := by
    change smoothMultiplierValue a ha hb (c • u) = c • smoothMultiplierValue a ha hb u
    apply underlying_injective
    filter_upwards [smoothMultiplierValue_realizes a ha hb (c • u),
      underlyingSection_smul c (smoothMultiplierValue a ha hb u),
      smoothMultiplierValue_realizes a ha hb u, underlyingSection_smul c u] with x h1 h2 h3 h4
    rw [h1, h2, h4]
    change a x (c • underlyingSection u x) = _
    rw [map_smul]
    simp only [Pi.smul_apply, h3]

end MatrixMembership




section ZeroL2Bridge
open P201Specs P201Specs.Hyperbolic.SymmetricEnergy P201Specs.Hyperbolic.SymmetricSobolevEnergy
variable {n m : ℕ} {𝕜 : Type} [RCLike 𝕜]

def zeroVectorL2 (v : WholeH n m 𝕜 0) : MeasureTheory.Lp (Fiber 𝕜 m) 2 (volume : Measure (Space n)) :=
 ((section_norm v).1 _).toLp (underlyingSection v)

theorem zeroVectorL2_ae (v : WholeH n m 𝕜 0) :
 zeroVectorL2 v =ᵐ[volume] underlyingSection v := MemLp.coeFn_toLp _

theorem zeroVectorL2_norm (v : WholeH n m 𝕜 0) : ‖zeroVectorL2 v‖ = ‖v‖ := by
 have hidx (α : P102.U4.SobolevIndex n 0) : α = P102.U4.zeroSobolevIndex n 0 := by
   apply Subtype.ext
   exact Multiset.card_eq_zero.mp (Nat.eq_zero_of_le_zero α.property)
 have hn : ‖v‖ ^ 2 = lpNorm (underlyingSection v) 2 volume ^ 2 := by
   rw [(section_norm v).2]
   apply Finset.sum_eq_single (P102.U4.zeroSobolevIndex n 0)
   · intro α _ hα
     exact (hα (hidx α)).elim
   · simp
 have heq : ‖zeroVectorL2 v‖ = lpNorm (underlyingSection v) 2 volume := by
   rw [Lp.norm_def, eLpNorm_congr_ae (zeroVectorL2_ae v)]
   rfl
 rw [heq]
 nlinarith [lpNorm_nonneg (f := underlyingSection v) (p := 2) (μ := volume), norm_nonneg v]

def zeroVectorL2Linear : WholeH n m 𝕜 0 →ₗ[𝕜]
 MeasureTheory.Lp (Fiber 𝕜 m) 2 (volume : Measure (Space n)) where
 toFun := zeroVectorL2
 map_add' v w := by
   apply Lp.ext
   have hi : ∀ᵐ x ∂(volume : Measure (Space n)), ∀ i : Fin m,
       (hUnderlying ⊤ 0 (v i + w i)) x = hUnderlying ⊤ 0 (v i) x + hUnderlying ⊤ 0 (w i) x := by
     rw [ae_all_iff]
     intro i
     rw [map_add]
     exact (Lp.coeFn_add (hUnderlying ⊤ 0 (v i)) (hUnderlying ⊤ 0 (w i))).filter_mono
       (MeasureTheory.ae_mono (show (volume : Measure (Space n)) ≤ P201Specs.domainMeasure (⊤ : Domain n) by simp [P201Specs.domainMeasure]))
   filter_upwards [zeroVectorL2_ae (v+w), zeroVectorL2_ae v, zeroVectorL2_ae w,
     Lp.coeFn_add (zeroVectorL2 v) (zeroVectorL2 w), hi] with x h1 h2 h3 h4 h5
   rw [h1, h4]
   change underlyingSection (v+w) x = zeroVectorL2 v x + zeroVectorL2 w x
   rw [h2, h3]
   apply PiLp.ext
   intro i
   exact h5 i
 map_smul' c v := by
   change zeroVectorL2 (c • v) = c • zeroVectorL2 v
   apply Lp.ext
   have hi : ∀ᵐ x ∂(volume : Measure (Space n)), ∀ i : Fin m,
       (hUnderlying ⊤ 0 (c • v i)) x = c • hUnderlying ⊤ 0 (v i) x := by
     rw [ae_all_iff]
     intro i
     rw [map_smul]
     exact (Lp.coeFn_smul c (hUnderlying ⊤ 0 (v i))).filter_mono
       (MeasureTheory.ae_mono (show (volume : Measure (Space n)) ≤ P201Specs.domainMeasure (⊤ : Domain n) by simp [P201Specs.domainMeasure]))
   filter_upwards [zeroVectorL2_ae (c • v), zeroVectorL2_ae v,
     Lp.coeFn_smul c (zeroVectorL2 v), hi] with x h1 h2 h3 h4
   rw [h1, h3]
   change underlyingSection (c • v) x = c • zeroVectorL2 v x
   rw [h2]
   apply PiLp.ext
   intro i
   exact h4 i

def zeroVectorL2Isometry : WholeH n m 𝕜 0 →ₗᵢ[𝕜]
 MeasureTheory.Lp (Fiber 𝕜 m) 2 (volume : Measure (Space n)) where
 toLinearMap := zeroVectorL2Linear
 norm_map' := zeroVectorL2_norm


theorem zeroVectorL2_surjective : Function.Surjective (@zeroVectorL2 n m 𝕜 _) := by
 intro f
 obtain ⟨e, he⟩ := P102.U4.sobolev_zeroOrder_isometry (𝕜 := 𝕜) (p := 2) (⊤ : Domain n)
 have hf (i : Fin m) : MemLp (fun x => f x i) 2 (P201Specs.domainMeasure (⊤ : Domain n)) :=
   ((Lp.memLp f).eval_piLp i).mono_measure (by simp [P201Specs.domainMeasure])
 let fi (i : Fin m) : P201Specs.Lp 𝕜 (⊤ : Domain n) 2 := (hf i).toLp (fun x => f x i)
 let v : WholeH n m 𝕜 0 := WithLp.toLp 2 (fun i => (hToW 𝕜 ⊤ 0).symm (e.symm (fi i)))
 have hv (i : Fin m) : hUnderlying ⊤ 0 (v i) = fi i := by
   change P102.U4.sobolevUnderlying ((hToW 𝕜 ⊤ 0)
     ((hToW 𝕜 ⊤ 0).symm (e.symm (fi i)))) = fi i
   rw [ContinuousLinearEquiv.apply_symm_apply, ← he, e.apply_symm_apply]
 refine ⟨v, ?_⟩
 apply Lp.ext
 have hfi : ∀ᵐ x ∂(volume : Measure (Space n)), ∀ i : Fin m, fi i x = f x i := by
   rw [ae_all_iff]
   intro i
   exact (hf i).coeFn_toLp.filter_mono
     (MeasureTheory.ae_mono (show (volume : Measure (Space n)) ≤ P201Specs.domainMeasure (⊤ : Domain n) by simp [P201Specs.domainMeasure]))
 filter_upwards [zeroVectorL2_ae v, hfi] with x hx hfx
 rw [hx]
 apply PiLp.ext
 intro i
 change hUnderlying ⊤ 0 (v i) x = f x i
 rw [hv]
 exact hfx i

def zeroVectorL2Iso : WholeH n m 𝕜 0 ≃ₗᵢ[𝕜]
 MeasureTheory.Lp (Fiber 𝕜 m) 2 (volume : Measure (Space n)) :=
 LinearIsometryEquiv.ofSurjective zeroVectorL2Isometry zeroVectorL2_surjective

theorem coefficient_zero_multiplier {s : ℕ} {T K : ℝ} (hK : 0 ≤ K)
 (a : LowerOrder n m 𝕜) (ha : BoundedSmoothCoefficient T s K a) :
 ∃ M : ℝ → WholeH n m 𝕜 0 →L[𝕜] WholeH n m 𝕜 0,
   (∀ t ∈ Icc 0 T, RealizesMultiplier (a t) (M t) ∧ ‖M t‖ ≤ K) ∧
   ∀ v, ContinuousOn (fun t => M t v) (Icc 0 T) := by
 obtain ⟨N, hN, hNc⟩ := CoefLp.coefficient_l2_multiplier a ha hK
 let e : WholeH n m 𝕜 0 ≃ₗᵢ[𝕜] MeasureTheory.Lp (Fiber 𝕜 m) 2 (volume : Measure (Space n)) :=
   zeroVectorL2Iso
 let M : ℝ → WholeH n m 𝕜 0 →L[𝕜] WholeH n m 𝕜 0 := fun t =>
   e.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
     ((N t).comp e.toContinuousLinearEquiv.toContinuousLinearMap)
 have he (v : WholeH n m 𝕜 0) : e v = zeroVectorL2 v := rfl
 have hout (t : ℝ) (v : WholeH n m 𝕜 0) : zeroVectorL2 (M t v) = N t (e v) := by
   change e (e.symm (N t (e v))) = _
   exact e.apply_symm_apply _
 refine ⟨M, ?_, ?_⟩
 · intro t ht
   refine ⟨?_, ?_⟩
   · intro v
     have hnv := (hN t ht).2 (e v)
     have hh : zeroVectorL2 (M t v) =ᵐ[volume] fun x => a t x (zeroVectorL2 v x) := by
       rw [hout, ← he]
       exact hnv
     filter_upwards [zeroVectorL2_ae (M t v), hh, zeroVectorL2_ae v] with x h1 h2 h3
     rw [← h1, h2, h3]
   · apply ContinuousLinearMap.opNorm_le_bound (M t) hK
     intro v
     change ‖e.symm (N t (e v))‖ ≤ K * ‖v‖
     rw [e.symm.norm_map]
     calc
       ‖N t (e v)‖ ≤ ‖N t‖ * ‖e v‖ := (N t).le_opNorm _
       _ ≤ K * ‖e v‖ := mul_le_mul_of_nonneg_right (hN t ht).1 (norm_nonneg _)
       _ = K * ‖v‖ := by rw [e.norm_map]
 · intro v
   exact e.symm.continuous.comp_continuousOn (hNc (e v))


end ZeroL2Bridge

section InnerBridge
open P201Specs.Hyperbolic.SymmetricEnergy
/-- The full Sobolev inner product is the sum of the actual vector L²
pairings of its weak derivatives, with the source's exact coefficients. -/
theorem wholeH_inner_eq_sum_integral {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (u v : WholeH n m 𝕜 k) :
    inner 𝕜 u v = ∑ α : P102.U4.SobolevIndex n k,
      ∫ x, inner 𝕜 (derivativeSection u α x) (derivativeSection v α x) := by
  rw [PiLp.inner_apply]
  calc
    _ = ∑ i : Fin m, ∑ α : P102.U4.SobolevIndex n k,
        inner 𝕜 (P102.U4.sobolevDerivative (P201Specs.hToW 𝕜 ⊤ k (u i)) α)
          (P102.U4.sobolevDerivative (P201Specs.hToW 𝕜 ⊤ k (v i)) α) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Submodule.coe_inner, PiLp.inner_apply]
      rfl
    _ = ∑ α : P102.U4.SobolevIndex n k, ∑ i : Fin m,
        inner 𝕜 (P102.U4.sobolevDerivative (P201Specs.hToW 𝕜 ⊤ k (u i)) α)
          (P102.U4.sobolevDerivative (P201Specs.hToW 𝕜 ⊤ k (v i)) α) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro α _
      simp_rw [derivativeSection, PiLp.inner_apply]
      change (∑ i : Fin m, inner 𝕜
        (P102.U4.sobolevDerivative (P201Specs.hToW 𝕜 ⊤ k (u i)) α)
        (P102.U4.sobolevDerivative (P201Specs.hToW 𝕜 ⊤ k (v i)) α)) =
        ∫ x, ∑ i : Fin m, inner 𝕜
          (P102.U4.sobolevDerivative (P201Specs.hToW 𝕜 ⊤ k (u i)) α x)
          (P102.U4.sobolevDerivative (P201Specs.hToW 𝕜 ⊤ k (v i)) α x)
      have hi (i : Fin m) : Integrable (fun x => inner 𝕜
          (P102.U4.sobolevDerivative (P201Specs.hToW 𝕜 ⊤ k (u i)) α x)
          (P102.U4.sobolevDerivative (P201Specs.hToW 𝕜 ⊤ k (v i)) α x)) volume := by
        simpa only [P201Specs.domainMeasure, TopologicalSpace.Opens.coe_top,
          Measure.restrict_univ] using
          L2.integrable_inner (𝕜 := 𝕜)
            (P102.U4.sobolevDerivative (P201Specs.hToW 𝕜 ⊤ k (u i)) α)
            (P102.U4.sobolevDerivative (P201Specs.hToW 𝕜 ⊤ k (v i)) α)
      rw [integral_finsetSum _ (fun i _ => hi i)]
      apply Finset.sum_congr rfl
      intro i _
      rw [L2.inner_def]
      simp only [P201Specs.domainMeasure, TopologicalSpace.Opens.coe_top,
        Measure.restrict_univ]


end InnerBridge

section WordSplits
open P102.U4
/-- All two-way splittings of the occurrences in a coordinate word. Duplicated
directions retain their binomial multiplicities through duplicated entries. -/
def wordSplits {ι : Type*} : List ι → List (List ι × List ι)
  | [] => [([], [])]
  | i :: l => (wordSplits l).map (fun p => (i :: p.1, p.2)) ++
      (wordSplits l).map (fun p => (p.1, i :: p.2))

/-- Differentiate a smooth coefficient in the order selected by the splitting. -/
def coefficientWord {n : ℕ} {𝕜 : Type} [RCLike 𝕜] {Ω : P201Specs.Domain n} :
    List (Fin n) → SmoothCoefficient 𝕜 Ω → SmoothCoefficient 𝕜 Ω
  | [], a => a
  | i :: l, a => coefficientWord l (coefficientPartial i a)

theorem coefficientWord_val {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : P201Specs.Domain n} (l : List (Fin n)) (a : SmoothCoefficient 𝕜 Ω) :
    (coefficientWord l a).val = partialWord a.val l.reverse := by
  induction l generalizing a with
  | nil => rfl
  | cons i l ih =>
    rw [coefficientWord, ih, List.reverse_cons, partialWord_append]
    rfl

/-- Explicit finite Leibniz formula for the actual distribution multiplier. -/
theorem leibnizExpansion_eq_wordSplits {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : P201Specs.Domain n} (l : List (Fin n)) (a : SmoothCoefficient 𝕜 Ω)
    (T : DistributionSpace 𝕜 Ω) :
    leibnizExpansion testMultiplier l a T =
      ((wordSplits l).map (fun p => distributionMultiplier (coefficientWord p.1 a)
        (distributionPartial (p.2 : Multiset (Fin n)) T))).sum := by
  induction l generalizing a T with
  | nil =>
    simp only [leibnizExpansion, wordSplits, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, coefficientWord]
    change transposeMultiplier testMultiplier a T = distributionMultiplier a (distributionPartial 0 T)
    rw [derivative_zero]
    rfl
  | cons i l ih =>
    simp only [leibnizExpansion, wordSplits, List.map_append, List.sum_append, List.map_map]
    rw [ih, ih]
    congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro p hp
    change distributionMultiplier (coefficientWord p.1 a)
        (distributionPartial (p.2 : Multiset (Fin n)) (distributionPartial {i} T)) =
        distributionMultiplier (coefficientWord p.1 a)
          (distributionPartial ((i :: p.2 : List (Fin n)) : Multiset (Fin n)) T)
    rw [← derivative_add n 𝕜 Ω]
    congr 2
    change (p.2 : Multiset (Fin n)) + {i} = i ::ₘ (p.2 : Multiset (Fin n))
    rw [add_comm, Multiset.singleton_add]

theorem wordSplits_length {ι : Type*} (l : List ι) :
    (wordSplits l).length = 2 ^ l.length := by
  induction l with
  | nil => simp [wordSplits]
  | cons i l ih =>
    simp only [wordSplits, List.length_append, List.length_map, ih, List.length_cons]
    ring

/-- Every split preserves the total order, so each factor has permitted regularity. -/
theorem wordSplits_mem_lengths {ι : Type*} {l : List ι} {p : List ι × List ι}
    (hp : p ∈ wordSplits l) : p.1.length + p.2.length = l.length := by
  induction l generalizing p with
  | nil =>
    simp only [wordSplits, List.mem_singleton] at hp
    subst p
    rfl
  | cons i l ih =>
    simp only [wordSplits, List.mem_append, List.mem_map] at hp
    rcases hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · simp only [List.length_cons]
      have h := ih hq
      omega
    · simp only [List.length_cons]
      have h := ih hq
      omega

theorem wordSplits_filter_empty {ι : Type*} (l : List ι) :
    (wordSplits l).filter (fun p => p.1.isEmpty) = [([], l)] := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp [wordSplits, List.filter_map, Function.comp_def, ih]

/-- Proper splits place at least one derivative on the coefficient. -/
def properWordSplits {ι : Type*} (l : List ι) : List (List ι × List ι) :=
  (wordSplits l).filter (fun p => !p.1.isEmpty)

theorem wordSplits_sum_eq_principal_add {ι M : Type*} [AddCommMonoid M]
    (l : List ι) (f : List ι × List ι → M) :
    ((wordSplits l).map f).sum = f ([], l) + ((properWordSplits l).map f).sum := by
  have h := (List.Perm.map f (List.filter_append_perm (fun p : List ι × List ι => p.1.isEmpty)
    (wordSplits l))).sum_eq
  simpa only [List.map_append, List.sum_append, wordSplits_filter_empty, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, add_zero, properWordSplits] using h.symm

theorem properWordSplits_length {ι : Type*} (l : List ι) :
    (properWordSplits l).length = 2 ^ l.length - 1 := by
  have h := (List.filter_append_perm (fun p : List ι × List ι => p.1.isEmpty)
    (wordSplits l)).length_eq
  rw [List.length_append, wordSplits_filter_empty, List.length_singleton,
    wordSplits_length] at h
  change 1 + (properWordSplits l).length = 2 ^ l.length at h
  omega

theorem properWordSplits_mem {ι : Type*} {l : List ι} {p : List ι × List ι}
    (hp : p ∈ properWordSplits l) :
    p ∈ wordSplits l ∧ p.1 ≠ [] ∧ p.2.length + 1 ≤ l.length := by
  have hmem : p ∈ wordSplits l := (List.mem_filter.mp hp).1
  have hn : p.1 ≠ [] := by
    intro h
    simp [properWordSplits, List.mem_filter, h] at hp
  have hlen := wordSplits_mem_lengths hmem
  have hpos : 0 < p.1.length := List.length_pos_iff.mpr hn
  exact ⟨hmem, hn, by omega⟩

/-- The leading term is the unique split with no derivative on the coefficient.
All other terms have one fewer derivative available for the field. -/
theorem leibnizExpansion_eq_principal_add {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : P201Specs.Domain n} (l : List (Fin n)) (a : SmoothCoefficient 𝕜 Ω)
    (T : DistributionSpace 𝕜 Ω) :
    leibnizExpansion testMultiplier l a T =
      distributionMultiplier a (distributionPartial (l : Multiset (Fin n)) T) +
      ((properWordSplits l).map (fun p => distributionMultiplier (coefficientWord p.1 a)
        (distributionPartial (p.2 : Multiset (Fin n)) T))).sum := by
  rw [leibnizExpansion_eq_wordSplits, wordSplits_sum_eq_principal_add]
  rfl


end WordSplits

/-- Differentiation commutes with a finite list sum, preserving multiplicity. -/
theorem hasFDerivAt_list_sum {ι : Type*} {X G : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (ls : List ι) (f : ι → X → G) (df : ι → X →L[ℝ] G) (x : X)
    (hf : ∀ i ∈ ls, HasFDerivAt (f i) (df i) x) :
    HasFDerivAt (fun y => (ls.map (fun i => f i y)).sum) (ls.map df).sum x := by
  induction ls with
  | nil => simpa only [List.map_nil, List.sum_nil] using hasFDerivAt_const (0 : G) x
  | cons i ls ih =>
    simpa only [List.map_cons, List.sum_cons] using
      (hf i (by simp)).fun_add (ih (fun j hj => hf j (by simp [hj])))

/-- Closed finite coordinate-word Leibniz formula for arbitrary continuous
real-bilinear products; hence also for matrix action with Euclidean operator norm. -/
theorem spatialWord_bilinear {n : ℕ} {E F G : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {b : E × F → G} (hb : IsBoundedBilinearMap ℝ b)
    {a : P201Specs.Space n → E} {u : P201Specs.Space n → F}
    (ha : ContDiff ℝ ∞ a) (hu : ContDiff ℝ ∞ u) (l : List (Fin n)) :
    spatialWord (fun x => b (a x, u x)) l = fun x =>
      ((wordSplits l).map (fun p => b (spatialWord a p.1 x, spatialWord u p.2 x))).sum := by
  induction l with
  | nil => funext x; simp only [spatialWord, wordSplits, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero]
  | cons j l ih =>
    funext x
    change fderiv ℝ (spatialWord (fun x => b (a x, u x)) l) x (P201Specs.coordinate n j) = _
    rw [ih]
    let f (p : List (Fin n) × List (Fin n)) :=
      fun x => b (spatialWord a p.1 x, spatialWord u p.2 x)
    let df (p : List (Fin n) × List (Fin n)) :=
      (hb.deriv (spatialWord a p.1 x, spatialWord u p.2 x)).comp
        ((fderiv ℝ (spatialWord a p.1) x).prod (fderiv ℝ (spatialWord u p.2) x))
    have hd (p : List (Fin n) × List (Fin n)) : HasFDerivAt (f p) (df p) x :=
      (hb.hasFDerivAt _).comp x
        (((spatialWord_contDiff ha p.1).differentiable (by simp) x).hasFDerivAt.prodMk
          ((spatialWord_contDiff hu p.2).differentiable (by simp) x).hasFDerivAt)
    rw [(hasFDerivAt_list_sum (wordSplits l) f df x (fun p _ => hd p)).fderiv]
    change ((wordSplits l).map df).sum (P201Specs.coordinate n j) = _
    change (ContinuousLinearMap.apply ℝ G (P201Specs.coordinate n j))
      ((wordSplits l).map df).sum = _
    rw [map_list_sum]
    simp only [List.map_map, Function.comp_def, df, ContinuousLinearMap.apply_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.prod_apply, IsBoundedBilinearMap.deriv_apply]
    simp only [wordSplits, List.map_append, List.sum_append, List.map_map, Function.comp_def]
    rw [List.sum_map_add, add_comm]
    rfl



section SmoothSections
open P201Specs.Hyperbolic.SymmetricSobolevEnergy P201Specs.Hyperbolic.SymmetricEnergy
open P102.U4

/-- A smooth representative determines all weak derivatives of the genuine
Sobolev element. This follows from distributional uniqueness. -/
theorem scalar_derivative_eq_smooth {n k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (u : P201Specs.H 𝕜 (⊤ : P201Specs.Domain n) k)
    {f : P201Specs.Space n → 𝕜} (hf : ContDiff ℝ ∞ f)
    (hrep : (P201Specs.hUnderlying ⊤ k u : P201Specs.Space n → 𝕜) =ᵐ[volume] f)
    (α : SobolevIndex n k) :
    (sobolevDerivative (P201Specs.hToW 𝕜 ⊤ k u) α : P201Specs.Space n → 𝕜) =ᵐ[volume]
      multiPartial f α.val := by
  have hfloc : LocallyIntegrableOn f (⊤ : P201Specs.Domain n) volume :=
    hf.continuous.continuousOn.locallyIntegrableOn isOpen_univ.measurableSet
  have hreg : P102.U4.regularDistribution ⊤ (P201Specs.hUnderlying ⊤ k u) =
      P102.U4.regularDistribution ⊤ f := by
    apply (regular_injectivity n 𝕜 ⊤ _ _ (domainLp_locallyIntegrable ⊤ 2 _) hfloc).mpr
    exact ae_restrict_of_ae hrep
  have hd := P201.hilbertDerivativeDistribution ⊤ k u α
  change distributionPartial α.val (P102.U4.regularDistribution ⊤ (P201Specs.hUnderlying ⊤ k u)) =
    P102.U4.regularDistribution ⊤ (sobolevDerivative (P201Specs.hToW 𝕜 ⊤ k u) α) at hd
  rw [hreg, derivative_classicalCompatibility n 𝕜 ⊤ α.val f
    (hf.of_le (by simp)).contDiffOn] at hd
  have hdf : LocallyIntegrableOn (multiPartial f α.val) (⊤ : P201Specs.Domain n) volume :=
    (partialWord_contDiff hf _).continuous.continuousOn.locallyIntegrableOn isOpen_univ.measurableSet
  have hae := (regular_injectivity n 𝕜 ⊤ _ _
    (domainLp_locallyIntegrable ⊤ 2 _) hdf).mp hd.symm
  simpa only [Opens.coe_top, Measure.restrict_univ] using hae

/-- Pointwise coordinate evaluation commutes with all vector spatial words. -/
theorem spatialWord_apply_component {n m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {f : P201Specs.Space n → Fiber 𝕜 m} (hf : ContDiff ℝ ∞ f)
    (l : List (Fin n)) (i : Fin m) (x : P201Specs.Space n) :
    P102.U4.partialWord (fun y => f y i) l x = spatialWord f l x i := by
  let L : Fiber 𝕜 m →L[ℝ] 𝕜 := (PiLp.proj (𝕜 := 𝕜) 2 (fun _ : Fin m => 𝕜) i).restrictScalars ℝ
  have h := congrFun (spatialWord_comp_clm L hf l) x
  rw [spatialWord_eq_partialWord] at h
  exact h

/-- Every vector weak derivative agrees with the corresponding classical
spatial derivative whenever a smooth representative is available. -/
theorem derivativeSection_eq_smooth {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (u : WholeH n m 𝕜 k) {f : P201Specs.Space n → Fiber 𝕜 m}
    (hf : ContDiff ℝ ∞ f) (hrep : underlyingSection u =ᵐ[volume] f)
    (α : SobolevIndex n k) : derivativeSection u α =ᵐ[volume] spatialPartial f α.val := by
  have hs (i : Fin m) : ContDiff ℝ ∞ (fun x => f x i) := by
    exact (contDiff_piLp 2).mp hf i
  have hc (i : Fin m) : ∀ᵐ x ∂volume,
      sobolevDerivative (P201Specs.hToW 𝕜 ⊤ k (u i)) α x = multiPartial (fun y => f y i) α.val x :=
    scalar_derivative_eq_smooth (u i) (hs i)
      (hrep.mono (fun x hx => congrArg (fun z : Fiber 𝕜 m => z i) hx)) α
  filter_upwards [ae_all_iff.mpr hc] with x hx
  apply PiLp.ext
  intro i
  change sobolevDerivative (P201Specs.hToW 𝕜 ⊤ k (u i)) α x = _
  rw [hx i]
  exact spatialWord_apply_component hf (α.val.sort (· ≤ ·)) i x

/-- Compact smooth component tests give a smooth vector representative. -/
def testSection {n m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (φ : Fin m → WholeTests n 𝕜) : P201Specs.Space n → Fiber 𝕜 m :=
  fun x => WithLp.toLp 2 (fun i => φ i x)

theorem testSection_contDiff {n m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (φ : Fin m → WholeTests n 𝕜) : ContDiff ℝ ∞ (testSection φ) := by
  apply (contDiff_piLp 2).mpr
  intro i
  exact (φ i).contDiff

theorem testSection_represents {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (φ : Fin m → WholeTests n 𝕜) (u : WholeH n m 𝕜 k)
    (hrep : ∀ i, RepresentsSobolev (φ i) (P201Specs.hToW 𝕜 ⊤ k (u i))) :
    underlyingSection u =ᵐ[volume] testSection φ := by
  have hc (i : Fin m) := hrep i (zeroSobolevIndex n k)
  filter_upwards [ae_all_iff.mpr hc] with x hx
  apply PiLp.ext
  intro i
  change sobolevDerivative (P201Specs.hToW 𝕜 ⊤ k (u i)) (zeroSobolevIndex n k) x = φ i x
  simpa only [P102.U4.multiPartial, zeroSobolevIndex, Multiset.sort_zero, P102.U4.partialWord] using hx i

/-- Every classical derivative through the Sobolev order has L² norm at most
the exact full Sobolev norm. -/
theorem smooth_word_lpNorm_le {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (u : WholeH n m 𝕜 k) {f : P201Specs.Space n → Fiber 𝕜 m}
    (hf : ContDiff ℝ ∞ f) (hrep : underlyingSection u =ᵐ[volume] f)
    (l : List (Fin n)) (hl : l.length ≤ k) :
    MemLp (spatialWord f l) 2 volume ∧ lpNorm (spatialWord f l) 2 volume ≤ ‖u‖ := by
  classical
  let α : SobolevIndex n k := ⟨l, by simpa using hl⟩
  have hp : ((l : Multiset (Fin n)).sort (· ≤ ·)).Perm l :=
    Multiset.coe_eq_coe.mp (Multiset.sort_eq _ _)
  have hsec := derivativeSection_eq_smooth u hf hrep α
  change derivativeSection u α =ᵐ[volume] spatialWord f ((l : Multiset (Fin n)).sort (· ≤ ·)) at hsec
  rw [spatialWord_perm hf hp] at hsec
  have hm := (memLp_congr_ae hsec).mp ((section_norm u).1 α)
  refine ⟨hm, ?_⟩
  have hs : lpNorm (derivativeSection u α) 2 volume ^ 2 ≤ ‖u‖ ^ 2 := by
    rw [(section_norm u).2]
    exact Finset.single_le_sum (fun β _ => sq_nonneg (lpNorm (derivativeSection u β) 2 volume)) (Finset.mem_univ α)
  have he : lpNorm (derivativeSection u α) 2 volume = lpNorm (spatialWord f l) 2 volume :=
    congrArg ENNReal.toReal (eLpNorm_congr_ae hsec)
  rw [he] at hs
  exact (sq_le_sq₀ (lpNorm_nonneg (f := spatialWord f l)) (norm_nonneg _)).mp hs

end SmoothSections

section DerivativeL2Bridge
open P201Specs P201Specs.Hyperbolic.SymmetricEnergy P201Specs.Hyperbolic.SymmetricSobolevEnergy
variable {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]

def scalarSobolevCoordinate (α : P102.U4.SobolevIndex n k) : H 𝕜 (⊤ : Domain n) k →L[𝕜] P201Specs.Lp 𝕜 (⊤ : Domain n) 2 :=
 (PiLp.proj 2 _ α).comp (P201Specs.hilbertSubmodule 𝕜 ⊤ k).subtypeL

variable (α : P102.U4.SobolevIndex n k)

def derivativeVectorL2 (v : WholeH n m 𝕜 k) : MeasureTheory.Lp (Fiber 𝕜 m) 2 (volume : Measure (Space n)) :=
 ((section_norm v).1 α).toLp (derivativeSection v α)

theorem derivativeVectorL2_ae (v : WholeH n m 𝕜 k) :
 derivativeVectorL2 α v =ᵐ[volume] derivativeSection v α := MemLp.coeFn_toLp _

theorem derivativeVectorL2_norm_le (v : WholeH n m 𝕜 k) : ‖derivativeVectorL2 α v‖ ≤ ‖v‖ := by
 have heq : ‖derivativeVectorL2 α v‖ = lpNorm (derivativeSection v α) 2 volume := by
   rw [Lp.norm_def, eLpNorm_congr_ae (derivativeVectorL2_ae α v)]
   rfl
 have hn : lpNorm (derivativeSection v α) 2 volume ^ 2 ≤ ‖v‖ ^ 2 := by
   rw [(section_norm v).2]
   exact Finset.single_le_sum (fun β _ => sq_nonneg (lpNorm (derivativeSection v β) 2 volume)) (Finset.mem_univ α)
 rw [heq]
 nlinarith [lpNorm_nonneg (f := derivativeSection v α) (p := 2) (μ := volume), norm_nonneg v]

def derivativeVectorL2Linear : WholeH n m 𝕜 k →ₗ[𝕜]
 MeasureTheory.Lp (Fiber 𝕜 m) 2 (volume : Measure (Space n)) where
 toFun := derivativeVectorL2 α
 map_add' v w := by
   apply Lp.ext
   have hi : ∀ᵐ x ∂(volume : Measure (Space n)), ∀ i : Fin m,
       (scalarSobolevCoordinate α (v i + w i)) x = scalarSobolevCoordinate α (v i) x + scalarSobolevCoordinate α (w i) x := by
     rw [ae_all_iff]
     intro i
     rw [map_add]
     exact (Lp.coeFn_add (scalarSobolevCoordinate α (v i)) (scalarSobolevCoordinate α (w i))).filter_mono
       (MeasureTheory.ae_mono (show (volume : Measure (Space n)) ≤ P201Specs.domainMeasure (⊤ : Domain n) by simp [P201Specs.domainMeasure]))
   filter_upwards [derivativeVectorL2_ae α (v+w), derivativeVectorL2_ae α v, derivativeVectorL2_ae α w,
     Lp.coeFn_add (derivativeVectorL2 α v) (derivativeVectorL2 α w), hi] with x h1 h2 h3 h4 h5
   rw [h1, h4]
   change derivativeSection (v+w) α x = derivativeVectorL2 α v x + derivativeVectorL2 α w x
   rw [h2, h3]
   apply PiLp.ext
   intro i
   exact h5 i
 map_smul' c v := by
   change derivativeVectorL2 α (c • v) = c • derivativeVectorL2 α v
   apply Lp.ext
   have hi : ∀ᵐ x ∂(volume : Measure (Space n)), ∀ i : Fin m,
       (scalarSobolevCoordinate α (c • v i)) x = c • scalarSobolevCoordinate α (v i) x := by
     rw [ae_all_iff]
     intro i
     rw [map_smul]
     exact (Lp.coeFn_smul c (scalarSobolevCoordinate α (v i))).filter_mono
       (MeasureTheory.ae_mono (show (volume : Measure (Space n)) ≤ P201Specs.domainMeasure (⊤ : Domain n) by simp [P201Specs.domainMeasure]))
   filter_upwards [derivativeVectorL2_ae α (c • v), derivativeVectorL2_ae α v,
     Lp.coeFn_smul c (derivativeVectorL2 α v), hi] with x h1 h2 h3 h4
   rw [h1, h3]
   change derivativeSection (c • v) α x = c • derivativeVectorL2 α v x
   rw [h2]
   apply PiLp.ext
   intro i
   exact h4 i

def derivativeToL2 : WholeH n m 𝕜 k →L[𝕜]
 MeasureTheory.Lp (Fiber 𝕜 m) 2 (volume : Measure (Space n)) :=
 (derivativeVectorL2Linear α).mkContinuous 1 (by
   intro v
   change ‖derivativeVectorL2 α v‖ ≤ 1 * ‖v‖
   simpa using derivativeVectorL2_norm_le α v)

theorem derivativeToL2_norm_le : ‖derivativeToL2 (m := m) (𝕜 := 𝕜) α‖ ≤ 1 := by
 apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
 intro v
 change ‖derivativeVectorL2 α v‖ ≤ 1 * ‖v‖
 simpa using derivativeVectorL2_norm_le α v


variable {α}

def wholeToL2Tuple : WholeH n m 𝕜 k →ₗᵢ[𝕜]
 PiLp 2 (fun _ : P102.U4.SobolevIndex n k =>
   MeasureTheory.Lp (Fiber 𝕜 m) 2 (volume : Measure (Space n))) where
 toFun v := WithLp.toLp 2 (fun β => derivativeToL2 β v)
 map_add' v w := by
   apply PiLp.ext
   intro β
   exact (derivativeToL2 β).map_add v w
 map_smul' c v := by
   apply PiLp.ext
   intro β
   exact (derivativeToL2 β).map_smul c v
 norm_map' v := by
   change ‖WithLp.toLp 2 (fun β : P102.U4.SobolevIndex n k => derivativeToL2 β v)‖ = ‖v‖
   have hn : ‖WithLp.toLp 2 (fun β : P102.U4.SobolevIndex n k => derivativeToL2 β v)‖ ^ 2 = ‖v‖ ^ 2 := by
     rw [PiLp.norm_sq_eq_of_L2, (section_norm v).2]
     apply Finset.sum_congr rfl
     intro β _
     change ‖derivativeVectorL2 β v‖ ^ 2 = _
     rw [Lp.norm_def, eLpNorm_congr_ae (derivativeVectorL2_ae β v)]
     rfl
   nlinarith [norm_nonneg (WithLp.toLp 2 (fun β : P102.U4.SobolevIndex n k => derivativeToL2 β v)), norm_nonneg v]

theorem derivativeToL2_ae (α : P102.U4.SobolevIndex n k) (v : WholeH n m 𝕜 k) :
 derivativeToL2 α v =ᵐ[volume] derivativeSection v α := derivativeVectorL2_ae α v

theorem continuousOn_iff_derivativeToL2 {Y : Type*} [TopologicalSpace Y]
 (v : Y → WholeH n m 𝕜 k) (S : Set Y) :
 ContinuousOn v S ↔ ∀ β, ContinuousOn (fun t => derivativeToL2 β (v t)) S := by
 constructor
 · intro hv β
   exact (derivativeToL2 β).continuous.comp_continuousOn hv
 · intro hv
   apply wholeToL2Tuple.isometry.isEmbedding.continuousOn_iff.mpr
   apply (PiLp.homeomorph 2 _).isEmbedding.continuousOn_iff.mpr
   change ContinuousOn (fun t β => derivativeToL2 β (v t)) S
   exact continuousOn_pi.mpr hv


end DerivativeL2Bridge

section QuantitativeProducts
open P201Specs.Hyperbolic.SymmetricSobolevEnergy
open P201Specs.Hyperbolic.SymmetricEnergy

/-- Pointwise uniformly bounded operator action controls the actual vector
L² norm without a finite-fiber dimension loss. -/
theorem operator_product_memLp_norm {n m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {a : P201Specs.Space n → Operator m 𝕜}
    {u : P201Specs.Space n → Fiber 𝕜 m} {K : ℝ} (hK : 0 ≤ K)
    (ha : AEStronglyMeasurable a) (hb : ∀ x, ‖a x‖ ≤ K) (hu : MemLp u 2) :
    MemLp (fun x => a x (u x)) 2 ∧
      lpNorm (fun x => a x (u x)) 2 volume ≤ K * lpNorm u 2 volume := by
  have hpoint (x) : ‖a x (u x)‖ ≤ K * ‖u x‖ :=
    (a x).le_opNorm (u x) |>.trans (mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _))
  refine ⟨hu.of_le_mul
    (P201.Hyperbolic.SymmetricEnergy.operator_apply_bilinear_real.continuous.comp_aestronglyMeasurable
      (ha.prodMk hu.aestronglyMeasurable)) (ae_of_all _ hpoint), ?_⟩
  have h := lpNorm_mono_real (hu.norm.const_mul K) hpoint
  have he : lpNorm (fun x => K * ‖u x‖) 2 volume = K * lpNorm u 2 volume := by
    change lpNorm (K • (fun x => ‖u x‖)) 2 volume = _
    rw [lpNorm_const_smul, lpNorm_norm hu.aestronglyMeasurable]
    simp only [Real.nnnorm_of_nonneg hK, NNReal.coe_mk]
  exact h.trans_eq he

/-- The triangle inequality for a list of L² functions, including repetitions. -/
theorem list_sum_memLp_norm {ι : Type*} {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] {μ : Measure X}
    (ls : List ι) (f : ι → X → E) (C : ℝ)
    (hf : ∀ i ∈ ls, MemLp (f i) 2 μ)
    (hb : ∀ i ∈ ls, lpNorm (f i) 2 μ ≤ C) :
    MemLp (fun x => (ls.map (fun i => f i x)).sum) 2 μ ∧
      lpNorm (fun x => (ls.map (fun i => f i x)).sum) 2 μ ≤ (ls.length : ℝ) * C := by
  induction ls with
  | nil => constructor
           · exact MemLp.zero
           · simp
  | cons i ls ih =>
    obtain ⟨hi, hib⟩ := ih (fun j hj => hf j (by simp [hj])) (fun j hj => hb j (by simp [hj]))
    constructor
    · simp only [List.map_cons, List.sum_cons]
      convert (hf i (by simp)).add hi using 1
    · simp only [List.map_cons, List.sum_cons]
      calc
        _ ≤ lpNorm (f i) 2 μ + lpNorm (fun x => (ls.map (fun j => f j x)).sum) 2 μ :=
          lpNorm_add_le (hf i (by simp)) (by norm_num)
        _ ≤ C + (ls.length : ℝ) * C := add_le_add (hb i (by simp)) hib
        _ = ((i :: ls).length : ℝ) * C := by simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring

/-- Cauchy--Schwarz for actual vector L² sections, retaining the real
part used in the real and complex energy estimates. -/
theorem real_inner_integrable_bound {n m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {u v : P201Specs.Space n → Fiber 𝕜 m} (hu : MemLp u 2) (hv : MemLp v 2) :
    Integrable (fun x => RCLike.re (inner 𝕜 (u x) (v x))) ∧
      |∫ x, RCLike.re (inner 𝕜 (u x) (v x))| ≤ lpNorm u 2 volume * lpNorm v 2 volume := by
  have hi : Integrable (fun x => ‖u x‖ * ‖v x‖) := hu.norm.integrable_mul hv.norm
  have hp (x) : ‖RCLike.re (inner 𝕜 (u x) (v x))‖ ≤ ‖u x‖ * ‖v x‖ :=
    (RCLike.norm_re_le_norm _).trans (norm_inner_le_norm _ _)
  refine ⟨hi.mono' (hu.aestronglyMeasurable.inner hv.aestronglyMeasurable).re (ae_of_all _ hp), ?_⟩
  have h := norm_integral_le_of_norm_le hi (ae_of_all _ hp)
  rw [Real.norm_eq_abs] at h
  exact h.trans (P201.Hyperbolic.SymmetricEnergy.integral_norm_mul_le_lpNorm_two hu hv)

/-- Leibniz' rule gives the quantitative L² multiplier bound for one arbitrary
coordinate word, with every binomial multiplicity counted. -/
theorem smooth_product_word_bound {n m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {a : P201Specs.Space n → Operator m 𝕜}
    {u : P201Specs.Space n → Fiber 𝕜 m} {K U : ℝ} (hK : 0 ≤ K)
    (ha : ContDiff ℝ ∞ a) (hu : ContDiff ℝ ∞ u) (l : List (Fin n))
    (hbA : ∀ q : List (Fin n), q.length ≤ l.length → ∀ x, ‖spatialWord a q x‖ ≤ K)
    (hbu : ∀ q : List (Fin n), q.length ≤ l.length →
      MemLp (spatialWord u q) 2 ∧ lpNorm (spatialWord u q) 2 volume ≤ U) :
    MemLp (spatialWord (fun x => a x (u x)) l) 2 ∧
      lpNorm (spatialWord (fun x => a x (u x)) l) 2 volume ≤ K * (2 : ℝ) ^ l.length * U := by
  rw [spatialWord_bilinear P201.Hyperbolic.SymmetricEnergy.operator_apply_bilinear_real ha hu]
  have hp (p : List (Fin n) × List (Fin n)) (hp : p ∈ wordSplits l) :
      MemLp (fun x => spatialWord a p.1 x (spatialWord u p.2 x)) 2 ∧
        lpNorm (fun x => spatialWord a p.1 x (spatialWord u p.2 x)) 2 volume ≤ K * U := by
    have hlen := wordSplits_mem_lengths hp
    have hleft : p.1.length ≤ l.length := by omega
    have hright : p.2.length ≤ l.length := by omega
    have h := operator_product_memLp_norm hK
      (spatialWord_contDiff ha p.1).continuous.aestronglyMeasurable (hbA p.1 hleft) (hbu p.2 hright).1
    exact ⟨h.1, h.2.trans (mul_le_mul_of_nonneg_left (hbu p.2 hright).2 hK)⟩
  have h := list_sum_memLp_norm (wordSplits l)
    (fun p x => spatialWord a p.1 x (spatialWord u p.2 x)) (K * U)
    (fun p hmem => (hp p hmem).1) (fun p hmem => (hp p hmem).2)
  refine ⟨h.1, h.2.trans_eq ?_⟩
  rw [wordSplits_length, Nat.cast_pow, Nat.cast_ofNat]
  ring

/-- Every genuine commutator term differentiates the coefficient, so at most
|l| derivatives remain on u even when the undifferentiated expression uses ∂j u. -/
theorem smooth_commutator_word_bound {n m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {a : P201Specs.Space n → Operator m 𝕜}
    {u : P201Specs.Space n → Fiber 𝕜 m} {K U : ℝ} (hK : 0 ≤ K)
    (ha : ContDiff ℝ ∞ a) (hu : ContDiff ℝ ∞ u) (l : List (Fin n)) (j : Fin n)
    (hbA : ∀ q : List (Fin n), q.length ≤ l.length → ∀ x, ‖spatialWord a q x‖ ≤ K)
    (hbu : ∀ q : List (Fin n), q.length ≤ l.length →
      MemLp (spatialWord u q) 2 ∧ lpNorm (spatialWord u q) 2 volume ≤ U) :
    let R := fun x => spatialWord (fun y => a y (spatialWord u [j] y)) l x -
      a x (spatialWord (spatialWord u [j]) l x)
    MemLp R 2 ∧ lpNorm R 2 volume ≤ K * ((2 : ℝ) ^ l.length - 1) * U := by
  dsimp only
  have heq : (fun x => spatialWord (fun y => a y (spatialWord u [j] y)) l x -
      a x (spatialWord (spatialWord u [j]) l x)) =
      fun x => ((properWordSplits l).map (fun p =>
        spatialWord a p.1 x (spatialWord (spatialWord u [j]) p.2 x))).sum := by
    funext x
    rw [congrFun (spatialWord_bilinear P201.Hyperbolic.SymmetricEnergy.operator_apply_bilinear_real
      ha (spatialWord_contDiff hu [j]) l) x, wordSplits_sum_eq_principal_add]
    simp only [spatialWord]
    abel
  rw [heq]
  have hp (p : List (Fin n) × List (Fin n)) (hp : p ∈ properWordSplits l) :
      MemLp (fun x => spatialWord a p.1 x (spatialWord (spatialWord u [j]) p.2 x)) 2 ∧
      lpNorm (fun x => spatialWord a p.1 x (spatialWord (spatialWord u [j]) p.2 x)) 2 volume ≤ K * U := by
    have hp' := properWordSplits_mem hp
    have hlen := wordSplits_mem_lengths hp'.1
    have hleft : p.1.length ≤ l.length := by omega
    have hright : (p.2 ++ [j]).length ≤ l.length := by
      simpa only [List.length_append, List.length_singleton] using hp'.2.2
    have hfield := hbu (p.2 ++ [j]) hright
    rw [spatialWord_append] at hfield
    have h := operator_product_memLp_norm hK
      (spatialWord_contDiff ha p.1).continuous.aestronglyMeasurable (hbA p.1 hleft) hfield.1
    exact ⟨h.1, h.2.trans (mul_le_mul_of_nonneg_left hfield.2 hK)⟩
  have h := list_sum_memLp_norm (properWordSplits l)
    (fun p x => spatialWord a p.1 x (spatialWord (spatialWord u [j]) p.2 x)) (K * U)
    (fun p hmem => (hp p hmem).1) (fun p hmem => (hp p hmem).2)
  refine ⟨h.1, h.2.trans_eq ?_⟩
  rw [properWordSplits_length, Nat.cast_sub (by have := Nat.one_le_pow l.length 2 (by norm_num); omega),
    Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  ring


end QuantitativeProducts


section MultiplierNorm
open P201Specs.Hyperbolic.SymmetricSobolevEnergy P201Specs.Hyperbolic.SymmetricEnergy

/-- A dimension-independent common multiplier constant for all orders k≤s. -/
def multiplierConstant (n s : ℕ) (K : ℝ) : ℝ :=
  Real.sqrt (Fintype.card (P102.U4.SobolevIndex n s)) * K * 2 ^ s

theorem multiplierConstant_nonneg {n s : ℕ} {K : ℝ} (hK : 0 ≤ K) :
    0 ≤ multiplierConstant n s K := by unfold multiplierConstant; positivity

theorem sobolevIndex_card_mono {n k s : ℕ} (hk : k ≤ s) :
    Fintype.card (P102.U4.SobolevIndex n k) ≤ Fintype.card (P102.U4.SobolevIndex n s) := by
  classical
  apply Fintype.card_le_of_injective (α := P102.U4.SobolevIndex n k) (β := P102.U4.SobolevIndex n s) (fun α : P102.U4.SobolevIndex n k =>
    (⟨α.val, α.property.trans hk⟩ : P102.U4.SobolevIndex n s))
  intro α β h
  apply Subtype.ext
  exact congrArg (fun γ : P102.U4.SobolevIndex n s => γ.val) h

/-- The exact derivative-square norm gives a quantitative bound on the dense
smooth class by Leibniz' rule, without a fiber-dimension loss. -/
theorem multiplier_smooth_norm_le {n m k s : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {K : ℝ} (hK : 0 ≤ K) (hk : k ≤ s)
    {a : P201Specs.Space n → Operator m 𝕜} (ha : ContDiff ℝ ∞ a)
    (hb : ∀ l : List (Fin n), l.length ≤ s → ∀ x, ‖spatialWord a l x‖ ≤ K)
    (M : WholeH n m 𝕜 k →L[𝕜] WholeH n m 𝕜 k) (hM : RealizesMultiplier a M)
    (φ : Fin m → P102.U4.WholeTests n 𝕜) (u : WholeH n m 𝕜 k)
    (hrep : ∀ i, P102.U4.RepresentsSobolev (φ i) (P201Specs.hToW 𝕜 ⊤ k (u i))) :
    ‖M u‖ ≤ multiplierConstant n s K * ‖u‖ := by
  let f := testSection φ
  have hf : ContDiff ℝ ∞ f := testSection_contDiff φ
  have hur : underlyingSection u =ᵐ[volume] f := testSection_represents φ u hrep
  let g := fun x => a x (f x)
  have hg : ContDiff ℝ ∞ g := by
    change ContDiff ℝ ∞ ((fun p : Operator m 𝕜 × Fiber 𝕜 m => p.1 p.2) ∘ fun x => (a x, f x))
    exact P201.Hyperbolic.SymmetricEnergy.operator_apply_bilinear_real.contDiff.comp (ha.prodMk hf)
  have hgr : underlyingSection (M u) =ᵐ[volume] g := (hM u).trans
    (hur.mono (fun x hx => congrArg (a x) hx))
  have hder (α : P102.U4.SobolevIndex n k) :
      lpNorm (derivativeSection (M u) α) 2 volume ≤ K * (2 : ℝ) ^ s * ‖u‖ := by
    let l := α.val.sort (· ≤ ·)
    have hl : l.length ≤ k := by simpa [l] using α.property
    have hq := smooth_product_word_bound hK ha hf l
      (fun q hq => hb q (hq.trans (hl.trans hk)))
      (fun q hq => smooth_word_lpNorm_le u hf hur q (hq.trans hl))
    have he := derivativeSection_eq_smooth (M u) hg hgr α
    have hnorm : lpNorm (derivativeSection (M u) α) 2 volume = lpNorm (spatialWord g l) 2 volume :=
      congrArg ENNReal.toReal (eLpNorm_congr_ae he)
    rw [hnorm]
    apply hq.2.trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg u)
    apply mul_le_mul_of_nonneg_left _ hK
    exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (hl.trans hk)
  let N : ℝ := Fintype.card (P102.U4.SobolevIndex n s)
  let D : ℝ := K * (2 : ℝ) ^ s * ‖u‖
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hsquare : ‖M u‖ ^ 2 ≤ N * D ^ 2 := by
    rw [(section_norm (M u)).2]
    calc
      _ ≤ ∑ _ : P102.U4.SobolevIndex n k, D ^ 2 := by
        apply Finset.sum_le_sum
        intro α _
        exact pow_le_pow_left₀ lpNorm_nonneg (hder α) 2
      _ = (Fintype.card (P102.U4.SobolevIndex n k) : ℝ) * D ^ 2 := by simp
      _ ≤ N * D ^ 2 := mul_le_mul_of_nonneg_right (by dsimp [N]; exact_mod_cast sobolevIndex_card_mono (n := n) hk) (sq_nonneg _)
  have heq : (multiplierConstant n s K * ‖u‖) ^ 2 = N * D ^ 2 := by
    dsimp [multiplierConstant, N, D]
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    ring
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (multiplierConstant_nonneg hK) (norm_nonneg _))).mp
    (hsquare.trans_eq heq.symm)

/-- The dimension-independent multiplier bound extends from compact smooth
functions through the actual bounded multiplier and genuine Sobolev density. -/
theorem multiplier_norm_le_of_realizes {n m k s : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {K : ℝ} (hK : 0 ≤ K) (hk : k ≤ s)
    {a : P201Specs.Space n → Operator m 𝕜} (ha : ContDiff ℝ ∞ a)
    (hb : ∀ l : List (Fin n), l.length ≤ s → ∀ x, ‖spatialWord a l x‖ ≤ K)
    (M : WholeH n m 𝕜 k →L[𝕜] WholeH n m 𝕜 k) (hM : RealizesMultiplier a M) :
    ‖M‖ ≤ multiplierConstant n s K := by
  apply ContinuousLinearMap.opNorm_le_bound _ (multiplierConstant_nonneg hK)
  intro u
  obtain ⟨φ, v, hrep, hv⟩ := wholeH_smooth_density u
  have hc : IsClosed {z : WholeH n m 𝕜 k | ‖M z‖ ≤ multiplierConstant n s K * ‖z‖} :=
    isClosed_le M.continuous.norm (continuous_const.mul continuous_norm)
  exact hc.mem_of_tendsto hv (Eventually.of_forall (fun r =>
    multiplier_smooth_norm_le hK hk ha hb M hM (φ r) (v r) (hrep r)))

end MultiplierNorm

section CoefficientJetL2
open P201Specs P201Specs.Hyperbolic.SymmetricEnergy P201Specs.Hyperbolic.SymmetricSobolevEnergy
variable {n m s : ℕ} {𝕜 : Type} [RCLike 𝕜] {T K : ℝ}

theorem coefficient_word_l2_multiplier (hT : 0 ≤ T) (hK : 0 ≤ K)
 (a : LowerOrder n m 𝕜) (ha : BoundedSmoothCoefficient T s K a)
 (l : List (Fin n)) (hl : l.length ≤ s) :
 ∃ M : ℝ → MeasureTheory.Lp (Fiber 𝕜 m) 2 (volume : Measure (Space n)) →L[𝕜]
     MeasureTheory.Lp (Fiber 𝕜 m) 2 (volume : Measure (Space n)),
   (∀ t ∈ Icc 0 T, ‖M t‖ ≤ K ∧ ∀ v,
     M t v =ᵐ[volume] fun x => spatialWord (a t) l x (v x)) ∧
   ∀ v, ContinuousOn (fun t => M t v) (Icc 0 T) := by
 let am : ∀ t : Icc (0:ℝ) T, AEStronglyMeasurable (spatialWord (a t) l) volume := fun t =>
   (spatialWord_contDiff (coefficient_slice_contDiff ha.1 t.property) l).continuous.aestronglyMeasurable
 let ab : ∀ t : Icc (0:ℝ) T, ∀ᵐ x ∂volume, ‖spatialWord (a t) l x‖ ≤ K := fun t =>
   Eventually.of_forall (coefficient_word_bound ha t.property l hl)
 let N := fun t : Icc (0:ℝ) T => LpMultiplier.multiplier (spatialWord (a t) l) (am t) K (ab t)
 let M := fun t : ℝ => if ht : t ∈ Icc 0 T then N ⟨t, ht⟩ else 0
 refine ⟨M, ?_, ?_⟩
 · intro t ht
   dsimp [M]
   rw [dite_eq_left ht]
   refine ⟨LpMultiplier.multiplier_norm_le _ _ K hK _, ?_⟩
   intro v
   exact LpMultiplier.action_ae (spatialWord (a t) l) (am ⟨t, ht⟩) K (ab ⟨t, ht⟩) v
 · intro v
   rw [continuousOn_iff_continuous_domRestrict]
   have h := LpMultiplier.continuous_action (fun t : Icc (0:ℝ) T => spatialWord (a t) l)
     am K hK ab (Eventually.of_forall (fun x =>
       continuousOn_iff_continuous_domRestrict.mp (coefficient_word_time_continuousOn hT ha l x))) v
   convert h using 1
   funext t
   dsimp [M, N, LpMultiplier.multiplier]
   rw [dite_eq_left t.property]
   rfl


end CoefficientJetL2

section SmoothPrincipalEnergy
open P201Specs.Hyperbolic.SymmetricSobolevEnergy
open P201Specs.Hyperbolic.SymmetricEnergy

theorem spatialWord_sub {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : P201Specs.Space n → E} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (l : List (Fin n)) :
    spatialWord (fun x => f x - g x) l = fun x => spatialWord f l x - spatialWord g l x := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    funext x
    change fderiv ℝ (spatialWord (fun x => f x - g x) l) x (P201Specs.coordinate n j) = _
    rw [ih, fderiv_fun_sub ((spatialWord_contDiff hf l).differentiable (by simp) x)
      ((spatialWord_contDiff hg l).differentiable (by simp) x)]
    rfl

theorem spatialWord_neg {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : P201Specs.Space n → E} (hf : ContDiff ℝ ∞ f) (l : List (Fin n)) :
    spatialWord (fun x => -f x) l = fun x => -spatialWord f l x := by
  simpa only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply] using
    spatialWord_comp_clm (-(ContinuousLinearMap.id ℝ E)) hf l

theorem spatialWord_finset_sum {n : ℕ} {ι E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Finset ι) (f : ι → P201Specs.Space n → E)
    (hf : ∀ i ∈ S, ContDiff ℝ ∞ (f i)) (l : List (Fin n)) :
    spatialWord (fun x => ∑ i ∈ S, f i x) l = fun x => ∑ i ∈ S, spatialWord (f i) l x := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    funext x
    change fderiv ℝ (spatialWord (fun x => ∑ i ∈ S, f i x) l) x (P201Specs.coordinate n j) = _
    rw [ih, fderiv_fun_sum (fun i hi => (spatialWord_contDiff (hf i hi) l).differentiable (by simp) x)]
    simp only [ContinuousLinearMap.sum_apply, spatialWord]

/-- The differentiated classical principal term has the correct energy bound.
Only max(1,|l|) coefficient derivatives are used; the extra u derivative is
needed for integrability, while the bound uses only derivatives through |l|. -/
theorem smooth_principal_word_energy {n m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {a : P201Specs.Space n → Operator m 𝕜}
    {u : P201Specs.Space n → Fiber 𝕜 m} {K U : ℝ}
    (hK : 0 ≤ K) (hU : 0 ≤ U) (ha : ContDiff ℝ ∞ a) (hu : ContDiff ℝ ∞ u)
    (hsym : ∀ x, IsSelfAdjoint (a x)) (l : List (Fin n)) (j : Fin n)
    (hbA : ∀ q : List (Fin n), q.length ≤ max 1 l.length → ∀ x, ‖spatialWord a q x‖ ≤ K)
    (hbu : ∀ q : List (Fin n), q.length ≤ l.length →
      MemLp (spatialWord u q) 2 ∧ lpNorm (spatialWord u q) 2 volume ≤ U)
    (hmore : ∀ q : List (Fin n), q.length ≤ l.length + 1 → MemLp (spatialWord u q) 2) :
    Integrable (fun x => RCLike.re (inner 𝕜 (spatialWord u l x)
      (spatialWord (fun y => a y (spatialWord u [j] y)) l x))) ∧
    |∫ x, RCLike.re (inner 𝕜 (spatialWord u l x)
      (spatialWord (fun y => a y (spatialWord u [j] y)) l x))| ≤
      K * ((2 : ℝ) ^ l.length + 1) * U ^ 2 := by
  let w := spatialWord u l
  let dw := spatialWord u (j :: l)
  let da := spatialWord a [j]
  let R := fun x => spatialWord (fun y => a y (spatialWord u [j] y)) l x -
    a x (spatialWord (spatialWord u [j]) l x)
  have hw := hbu l le_rfl
  have hdw : MemLp dw 2 := hmore (j :: l) (by simp)
  have hcommute : spatialWord (spatialWord u [j]) l = dw := by
    rw [← spatialWord_append]
    have hp : (l ++ [j]).Perm ([j] ++ l) := List.perm_append_comm
    simpa only [List.singleton_append] using spatialWord_perm hu hp
  have hR := smooth_commutator_word_bound hK ha hu l j
    (fun q hq => hbA q (hq.trans (le_max_right 1 l.length))) hbu
  change MemLp R 2 ∧ lpNorm R 2 volume ≤ K * ((2 : ℝ) ^ l.length - 1) * U at hR
  have haLine (x) : HasLineDerivAt ℝ a (da x) x (P201Specs.coordinate n j) := by
    exact ((ha.differentiable (by simp) x).hasFDerivAt.hasLineDerivAt _)
  have hwLine (x) : HasLineDerivAt ℝ w (dw x) x (P201Specs.coordinate n j) := by
    exact (((spatialWord_contDiff hu l).differentiable (by simp) x).hasFDerivAt.hasLineDerivAt _)
  have hP := symmetric_principal_integral_bound (P201Specs.coordinate n j) hK haLine hwLine hsym
    ha.continuous.aestronglyMeasurable (spatialWord_contDiff ha [j]).continuous.aestronglyMeasurable
    (hbA [] (by simp)) (hbA [j] (by simp)) hw.1 hdw
  have hiP := integrable_real_operator_pairing ha.continuous.aestronglyMeasurable
    (hbA [] (by simp)) hw.1 hdw
  have hiR := real_inner_integrable_bound hw.1 hR.1
  have hsplit (x) :
      RCLike.re (inner 𝕜 (w x) (spatialWord (fun y => a y (spatialWord u [j] y)) l x)) =
      RCLike.re (inner 𝕜 (w x) (a x (dw x))) + RCLike.re (inner 𝕜 (w x) (R x)) := by
    have hh : spatialWord (fun y => a y (spatialWord u [j] y)) l x = a x (dw x) + R x := by
      dsimp [R]
      rw [hcommute]
      abel
    rw [hh, inner_add_right, map_add]
  have hi : Integrable (fun x => RCLike.re (inner 𝕜 (w x)
      (spatialWord (fun y => a y (spatialWord u [j] y)) l x))) := by
    simp_rw [hsplit]
    exact hiP.add hiR.1
  refine ⟨hi, ?_⟩
  change |∫ x, RCLike.re (inner 𝕜 (w x) _)| ≤ _
  simp_rw [hsplit]
  rw [integral_add hiP hiR.1]
  have hP' : |∫ x, RCLike.re (inner 𝕜 (w x) (a x (dw x)))| ≤ (K / 2) * U ^ 2 := by
    exact hP.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (lpNorm_nonneg (f := w)) hw.2 2) (by positivity))
  have hR' : |∫ x, RCLike.re (inner 𝕜 (w x) (R x))| ≤ K * ((2 : ℝ) ^ l.length - 1) * U ^ 2 := by
    calc
      _ ≤ lpNorm w 2 volume * lpNorm R 2 volume := hiR.2
      _ ≤ U * (K * ((2 : ℝ) ^ l.length - 1) * U) :=
        mul_le_mul hw.2 hR.2 (lpNorm_nonneg (f := R)) hU
      _ = _ := by ring
  calc
    _ ≤ |∫ x, RCLike.re (inner 𝕜 (w x) (a x (dw x)))| +
      |∫ x, RCLike.re (inner 𝕜 (w x) (R x))| := abs_add_le _ _
    _ ≤ (K / 2) * U ^ 2 + K * ((2 : ℝ) ^ l.length - 1) * U ^ 2 := add_le_add hP' hR'
    _ ≤ K * ((2 : ℝ) ^ l.length + 1) * U ^ 2 := by nlinarith [mul_nonneg hK (sq_nonneg U)]

/-- The complete classical differentiated P pairing, with a constant independent
of the vector fiber dimension and no coefficient derivative beyond max(1,|l|). -/
theorem smooth_p_word_energy {n m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (A : Fin n → P201Specs.Space n → Operator m 𝕜) (B : P201Specs.Space n → Operator m 𝕜)
    {u : P201Specs.Space n → Fiber 𝕜 m} {K U : ℝ}
    (hK : 0 ≤ K) (hU : 0 ≤ U) (hA : ∀ j, ContDiff ℝ ∞ (A j))
    (hB : ContDiff ℝ ∞ B) (hu : ContDiff ℝ ∞ u)
    (hsym : ∀ j x, IsSelfAdjoint (A j x)) (l : List (Fin n))
    (hbA : ∀ j (q : List (Fin n)), q.length ≤ max 1 l.length → ∀ x, ‖spatialWord (A j) q x‖ ≤ K)
    (hbB : ∀ q : List (Fin n), q.length ≤ l.length → ∀ x, ‖spatialWord B q x‖ ≤ K)
    (hbu : ∀ q : List (Fin n), q.length ≤ l.length →
      MemLp (spatialWord u q) 2 ∧ lpNorm (spatialWord u q) 2 volume ≤ U)
    (hmore : ∀ q : List (Fin n), q.length ≤ l.length + 1 → MemLp (spatialWord u q) 2) :
    let p := fun x => -(∑ j, A j x (spatialWord u [j] x)) - B x (u x)
    Integrable (fun x => RCLike.re (inner 𝕜 (spatialWord u l x) (spatialWord p l x))) ∧
    |∫ x, RCLike.re (inner 𝕜 (spatialWord u l x) (spatialWord p l x))| ≤
      ((n + 1 : ℕ) : ℝ) * K * ((2 : ℝ) ^ l.length + 1) * U ^ 2 := by
  classical
  dsimp only
  let Aj (j : Fin n) := fun x => A j x (spatialWord u [j] x)
  let Bu := fun x => B x (u x)
  have hAj (j : Fin n) : ContDiff ℝ ∞ (Aj j) :=
    (P201.Hyperbolic.SymmetricEnergy.operator_apply_bilinear_real (m := m) (𝕜 := 𝕜)).contDiff.comp ((hA j).prodMk (spatialWord_contDiff hu [j]))
  have hBu : ContDiff ℝ ∞ Bu :=
    (P201.Hyperbolic.SymmetricEnergy.operator_apply_bilinear_real (m := m) (𝕜 := 𝕜)).contDiff.comp (hB.prodMk hu)
  have hsumA : ContDiff ℝ ∞ (fun x => ∑ j, Aj j x) := ContDiff.sum (fun j _ => hAj j)
  have hpr (j : Fin n) := smooth_principal_word_energy hK hU (hA j) hu (hsym j) l j (hbA j) hbu hmore
  have hmul := smooth_product_word_bound hK hB hu l hbB hbu
  have hw := hbu l le_rfl
  have hbe := real_inner_integrable_bound hw.1 hmul.1
  have hbb : |∫ x, RCLike.re (inner 𝕜 (spatialWord u l x) (spatialWord Bu l x))| ≤
      K * (2 : ℝ) ^ l.length * U ^ 2 := by
    calc
      _ ≤ lpNorm (spatialWord u l) 2 volume * lpNorm (spatialWord Bu l) 2 volume := hbe.2
      _ ≤ U * (K * (2 : ℝ) ^ l.length * U) := mul_le_mul hw.2 hmul.2 (lpNorm_nonneg (f := spatialWord Bu l)) hU
      _ = _ := by ring
  have hs : ∀ x, RCLike.re (inner 𝕜 (spatialWord u l x)
      (spatialWord (fun x => -(∑ j, Aj j x) - Bu x) l x)) =
      -(∑ j, RCLike.re (inner 𝕜 (spatialWord u l x) (spatialWord (Aj j) l x))) -
      RCLike.re (inner 𝕜 (spatialWord u l x) (spatialWord Bu l x)) := by
    intro x
    rw [spatialWord_sub hsumA.neg hBu, spatialWord_neg hsumA,
      spatialWord_finset_sum Finset.univ Aj (fun j _ => hAj j)]
    simp only [inner_sub_right, inner_neg_right, inner_sum, map_sub, map_neg, map_sum]
  have hiSum : Integrable (fun x => ∑ j, RCLike.re
      (inner 𝕜 (spatialWord u l x) (spatialWord (Aj j) l x))) :=
    integrable_finsetSum Finset.univ (fun j _ => (hpr j).1)
  constructor
  · change Integrable (fun x => RCLike.re (inner 𝕜 (spatialWord u l x)
      (spatialWord (fun x => -(∑ j, Aj j x) - Bu x) l x)))
    simp_rw [hs]
    exact hiSum.neg.sub hbe.1
  · change |∫ x, RCLike.re (inner 𝕜 (spatialWord u l x)
      (spatialWord (fun x => -(∑ j, Aj j x) - Bu x) l x))| ≤ _
    simp_rw [hs]
    have hiNeg : Integrable (fun x => -(∑ j, RCLike.re
      (inner 𝕜 (spatialWord u l x) (spatialWord (Aj j) l x)))) := by
      convert hiSum.neg using 1
    have hiB : Integrable (fun x => RCLike.re
      (inner 𝕜 (spatialWord u l x) (spatialWord Bu l x))) := hbe.1
    rw [integral_sub hiNeg hiB, integral_neg, integral_finsetSum _ (fun j _ => (hpr j).1)]
    calc
      _ ≤ |-(∑ j, ∫ x, RCLike.re (inner 𝕜 (spatialWord u l x) (spatialWord (Aj j) l x)))| +
          |∫ x, RCLike.re (inner 𝕜 (spatialWord u l x) (spatialWord Bu l x))| := abs_sub _ _
      _ ≤ (∑ j, |∫ x, RCLike.re (inner 𝕜 (spatialWord u l x) (spatialWord (Aj j) l x))|) +
          K * (2 : ℝ) ^ l.length * U ^ 2 := by
        rw [abs_neg]
        exact add_le_add (Finset.abs_sum_le_sum_abs _ _) hbb
      _ ≤ (∑ _j : Fin n, K * ((2 : ℝ) ^ l.length + 1) * U ^ 2) +
          K * (2 : ℝ) ^ l.length * U ^ 2 :=
        add_le_add (Finset.sum_le_sum (fun j _ => (hpr j).2)) le_rfl
      _ ≤ ((n + 1 : ℕ) : ℝ) * K * ((2 : ℝ) ^ l.length + 1) * U ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
        nlinarith [mul_nonneg hK (sq_nonneg U)]


end SmoothPrincipalEnergy

namespace StrongContinuity
variable {Y 𝕜 E F : Type*} [TopologicalSpace Y] [NontriviallyNormedField 𝕜]
 [NormedAddCommGroup E] [NormedSpace 𝕜 E]
 [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem continuousOn_of_dense (M : Y → E →L[𝕜] F) (S : Set Y) (D : Set E)
 (hD : Dense D) (K : ℝ) (hK : ∀ t ∈ S, ‖M t‖ ≤ K)
 (hc : ∀ v ∈ D, ContinuousOn (fun t => M t v) S) :
 ∀ v, ContinuousOn (fun t => M t v) S := by
 intro v
 obtain ⟨u, huD, hu⟩ := mem_closure_iff_seq_limit.mp (hD v)
 have hz : Tendsto (fun n => K * ‖v - u n‖) atTop (𝓝 0) := by
   have ht : Tendsto (fun n => v - u n) atTop (𝓝 (v-v)) := tendsto_const_nhds.sub hu
   have htK : Tendsto (fun _ : ℕ => K) atTop (𝓝 K) := tendsto_const_nhds
   simpa using htK.mul ht.norm
 have hU : TendstoUniformlyOn (fun n t => M t (u n)) (fun t => M t v) atTop S := by
   apply Metric.tendstoUniformlyOn_iff.mpr
   intro ε hε
   have he := (tendsto_order.1 hz).2 ε hε
   filter_upwards [he] with n hn t ht
   calc
     dist (M t v) (M t (u n)) = ‖M t (v - u n)‖ := by rw [dist_eq_norm, map_sub]
     _ ≤ K * ‖v - u n‖ := ((M t).le_opNorm _).trans
       (mul_le_mul_of_nonneg_right (hK t ht) (norm_nonneg _))
     _ < ε := hn
 exact hU.continuousOn (Eventually.of_forall (fun n => hc (u n) (huD n))).frequently
end StrongContinuity


section ClosedMultiplier
open P201Specs.Hyperbolic.SymmetricEnergy
def wholeUnderlyingL2Value {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (u : WholeH n m 𝕜 k) : MeasureTheory.Lp (Fiber 𝕜 m) 2
      (volume : Measure (P201Specs.Space n)) :=
  ((section_norm u).1 _).toLp (underlyingSection u)

theorem wholeUnderlyingL2Value_ae {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (u : WholeH n m 𝕜 k) : wholeUnderlyingL2Value u =ᵐ[volume] underlyingSection u :=
  MemLp.coeFn_toLp _

theorem wholeUnderlyingL2Value_norm_le {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (u : WholeH n m 𝕜 k) : ‖wholeUnderlyingL2Value u‖ ≤ ‖u‖ := by
  classical
  have hn : lpNorm (underlyingSection u) 2 volume ^ 2 ≤ ‖u‖ ^ 2 := by
    rw [(section_norm u).2]
    exact Finset.single_le_sum (f := fun α : P102.U4.SobolevIndex n k =>
      lpNorm (derivativeSection u α) 2 volume ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ (P102.U4.zeroSobolevIndex n k))
  have heq : ‖wholeUnderlyingL2Value u‖ = lpNorm (underlyingSection u) 2 volume := by
    rw [MeasureTheory.Lp.norm_def, eLpNorm_congr_ae (wholeUnderlyingL2Value_ae u)]
    rfl
  rw [heq]
  nlinarith [lpNorm_nonneg (f := underlyingSection u) (p := 2) (μ := volume), norm_nonneg u]

def wholeUnderlyingL2 {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜] :
    WholeH n m 𝕜 k →L[𝕜] MeasureTheory.Lp (Fiber 𝕜 m) 2
      (volume : Measure (P201Specs.Space n)) :=
  LinearMap.mkContinuous
    { toFun := wholeUnderlyingL2Value
      map_add' := by
        intro u v
        apply MeasureTheory.Lp.ext
        filter_upwards [wholeUnderlyingL2Value_ae (u+v), wholeUnderlyingL2Value_ae u,
          wholeUnderlyingL2Value_ae v, underlyingSection_add u v,
          MeasureTheory.Lp.coeFn_add (wholeUnderlyingL2Value u) (wholeUnderlyingL2Value v)] with x h1 h2 h3 h4 h5
        rw [h1, h5]
        change underlyingSection (u+v) x = wholeUnderlyingL2Value u x + wholeUnderlyingL2Value v x
        rw [h2, h3]
        exact h4
      map_smul' := by
        intro c u
        change wholeUnderlyingL2Value (c • u) = c • wholeUnderlyingL2Value u
        apply MeasureTheory.Lp.ext
        filter_upwards [wholeUnderlyingL2Value_ae (c • u), wholeUnderlyingL2Value_ae u,
          underlyingSection_smul c u, MeasureTheory.Lp.coeFn_smul c (wholeUnderlyingL2Value u)] with x h1 h2 h3 h4
        rw [h1, h4]
        change underlyingSection (c • u) x = c • wholeUnderlyingL2Value u x
        rw [h2]
        exact h3 }
    1 (fun u => by
      change ‖wholeUnderlyingL2Value u‖ ≤ 1 * ‖u‖
      simpa only [one_mul] using wholeUnderlyingL2Value_norm_le u)

theorem wholeUnderlyingL2_ae {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (u : WholeH n m 𝕜 k) : wholeUnderlyingL2 u =ᵐ[volume] underlyingSection u :=
  wholeUnderlyingL2Value_ae u

theorem wholeUnderlyingL2_injective {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜] :
    Function.Injective (wholeUnderlyingL2 (n := n) (m := m) (k := k) (𝕜 := 𝕜)) := by
  intro u v h
  apply underlying_injective
  filter_upwards [wholeUnderlyingL2_ae u, wholeUnderlyingL2_ae v, MeasureTheory.Lp.ext_iff.mp h] with x h1 h2 h3
  rw [← h1, ← h2, h3]

theorem smoothMultiplierLinear_graph_isClosed {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (a : P201Specs.Space n → Operator m 𝕜) (ha : ContDiff ℝ ∞ a)
    (hb : ∀ l : List (Fin n), l.length ≤ k → ∃ C : ℝ, ∀ x, ‖spatialWord a l x‖ ≤ C) :
    IsClosed ((smoothMultiplierLinear a ha hb).graph : Set (WholeH n m 𝕜 k × WholeH n m 𝕜 k)) := by
  classical
  obtain ⟨C, hC⟩ := hb [] (by simp)
  have hC' : ∀ᵐ x ∂volume, ‖a x‖ ≤ C := Eventually.of_forall hC
  let N : MeasureTheory.Lp (Fiber 𝕜 m) 2 (volume : Measure (P201Specs.Space n)) →L[𝕜]
      MeasureTheory.Lp (Fiber 𝕜 m) 2 volume :=
    LpMultiplier.multiplier a ha.continuous.aestronglyMeasurable C hC'
  have hcomm (u : WholeH n m 𝕜 k) :
      wholeUnderlyingL2 (smoothMultiplierLinear a ha hb u) = N (wholeUnderlyingL2 u) := by
    apply MeasureTheory.Lp.ext
    have hr := smoothMultiplierValue_realizes a ha hb u
    have hN := LpMultiplier.action_ae a ha.continuous.aestronglyMeasurable C hC' (wholeUnderlyingL2 u)
    filter_upwards [wholeUnderlyingL2_ae (smoothMultiplierLinear a ha hb u), hr, hN,
      wholeUnderlyingL2_ae u] with x h1 h2 h3 h4
    rw [h1]
    change underlyingSection (smoothMultiplierValue a ha hb u) x = _
    rw [h2]
    change a x (underlyingSection u x) = LpMultiplier.action a ha.continuous.aestronglyMeasurable C hC' (wholeUnderlyingL2 u) x
    rw [h3, h4]
  have heq : ((smoothMultiplierLinear a ha hb).graph : Set (WholeH n m 𝕜 k × WholeH n m 𝕜 k)) =
      {z | wholeUnderlyingL2 z.2 = N (wholeUnderlyingL2 z.1)} := by
    ext z
    constructor
    · intro hz
      change z.2 = smoothMultiplierLinear a ha hb z.1 at hz
      change wholeUnderlyingL2 z.2 = N (wholeUnderlyingL2 z.1)
      rw [hz]
      exact hcomm z.1
    · intro hz
      change z.2 = smoothMultiplierLinear a ha hb z.1
      apply wholeUnderlyingL2_injective
      exact hz.trans (hcomm z.1).symm
  rw [heq]
  apply isClosed_eq
  · exact wholeUnderlyingL2.continuous.comp continuous_snd
  · exact N.continuous.comp (wholeUnderlyingL2.continuous.comp continuous_fst)

/-- Qualitative continuity follows from the actual closed graph. Quantitative
norm bounds are subsequently proved on the smooth dense subspace. -/
def smoothMultiplierCLM {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (a : P201Specs.Space n → Operator m 𝕜) (ha : ContDiff ℝ ∞ a)
    (hb : ∀ l : List (Fin n), l.length ≤ k → ∃ C : ℝ, ∀ x, ‖spatialWord a l x‖ ≤ C) :
    WholeH n m 𝕜 k →L[𝕜] WholeH n m 𝕜 k :=
  { toLinearMap := smoothMultiplierLinear a ha hb
    cont := LinearMap.continuous_of_isClosed_graph (𝕜 := 𝕜)
      (E := WholeH n m 𝕜 k) (F := WholeH n m 𝕜 k) (smoothMultiplierLinear a ha hb)
      (smoothMultiplierLinear_graph_isClosed a ha hb) }

theorem smoothMultiplierCLM_realizes {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (a : P201Specs.Space n → Operator m 𝕜) (ha : ContDiff ℝ ∞ a)
    (hb : ∀ l : List (Fin n), l.length ≤ k → ∃ C : ℝ, ∀ x, ‖spatialWord a l x‖ ≤ C) :
    RealizesMultiplier a (smoothMultiplierCLM a ha hb) := by
  intro u
  change underlyingSection (smoothMultiplierValue a ha hb u) =ᵐ[volume] _
  exact smoothMultiplierValue_realizes a ha hb u


end ClosedMultiplier

section SmoothTimeContinuity
open P201Specs P201Specs.Hyperbolic.SymmetricEnergy P201Specs.Hyperbolic.SymmetricSobolevEnergy

theorem lp_list_sum_ae {ι X E : Type*} [MeasurableSpace X] {μ : Measure X}
 [NormedAddCommGroup E] (ls : List ι) (f : ι → MeasureTheory.Lp E 2 μ)
 (g : ι → X → E) (h : ∀ i ∈ ls, f i =ᵐ[μ] g i) :
 (ls.map f).sum =ᵐ[μ] fun x => (ls.map (fun i => g i x)).sum := by
 induction ls with
 | nil =>
   filter_upwards [Lp.coeFn_zero E 2 μ] with x hx
   simpa only [List.map_nil, List.sum_nil, Pi.zero_apply] using hx
 | cons i ls ih =>
   have hh := (Lp.coeFn_add (f i) ((ls.map f).sum)).trans
     ((h i (by simp)).add (ih (fun j hj => h j (by simp [hj]))))
   filter_upwards [hh] with x hx
   simpa only [List.map_cons, List.sum_cons, Pi.add_apply] using hx

theorem continuous_list_sum {ι Y E : Type*} [TopologicalSpace Y]
 [TopologicalSpace E] [AddCommMonoid E] [ContinuousAdd E]
 (ls : List ι) (f : ι → Y → E) (hf : ∀ i ∈ ls, Continuous (f i)) :
 Continuous (fun t => (ls.map (fun i => f i t)).sum) := by
 induction ls with
 | nil => simpa only [List.map_nil, List.sum_nil] using continuous_const (y := (0:E))
 | cons i ls ih =>
   convert (hf i (by simp)).add (ih (fun j hj => hf j (by simp [hj]))) using 1
   funext t
   simp only [List.map_cons, List.sum_cons, Pi.add_apply]

theorem multiplier_continuousOn_smooth {n m s k : ℕ} {𝕜 : Type} [RCLike 𝕜]
 {T K : ℝ} (hT : 0 ≤ T) (hK : 0 ≤ K)
 (a : LowerOrder n m 𝕜) (ha : BoundedSmoothCoefficient T s K a) (hk : k ≤ s)
 (M : ℝ → WholeH n m 𝕜 k →L[𝕜] WholeH n m 𝕜 k)
 (hM : ∀ t ∈ Icc 0 T, RealizesMultiplier (a t) (M t))
 (u : WholeH n m 𝕜 k) (f : Space n → Fiber 𝕜 m)
 (hf : ContDiff ℝ ∞ f) (hrep : underlyingSection u =ᵐ[volume] f) :
 ContinuousOn (fun t => M t u) (Icc 0 T) := by
 apply (continuousOn_iff_derivativeToL2 _ _).mpr
 intro β
 rw [continuousOn_iff_continuous_domRestrict]
 let l : List (Fin n) := β.val.sort (· ≤ ·)
 have hl : l.length ≤ k := by simpa [l] using β.property
 let ls := wordSplits l
 let Idx := {p : List (Fin n) × List (Fin n) // p ∈ ls}
 have hlen (p : Idx) : p.val.1.length ≤ s ∧ p.val.2.length ≤ k := by
   have h := wordSplits_mem_lengths p.property
   constructor <;> omega
 let fp (p : Idx) : MeasureTheory.Lp (Fiber 𝕜 m) 2 (volume : Measure (Space n)) :=
   ((smooth_word_lpNorm_le u hf hrep p.val.2 (hlen p).2).1).toLp (spatialWord f p.val.2)
 let am (p : Idx) (t : Icc (0:ℝ) T) : AEStronglyMeasurable (spatialWord (a t) p.val.1) volume :=
   (spatialWord_contDiff (coefficient_slice_contDiff ha.1 t.property) p.val.1).continuous.aestronglyMeasurable
 let ab (p : Idx) (t : Icc (0:ℝ) T) : ∀ᵐ x ∂volume, ‖spatialWord (a t) p.val.1 x‖ ≤ K :=
   Eventually.of_forall (coefficient_word_bound ha t.property p.val.1 (hlen p).1)
 let term (p : Idx) (t : Icc (0:ℝ) T) :=
   LpMultiplier.action (spatialWord (a t) p.val.1) (am p t) K (ab p t) (fp p)
 have htcont (p : Idx) : Continuous (term p) := by
   exact LpMultiplier.continuous_action _ (am p) K hK (ab p)
     (Eventually.of_forall (fun x => continuousOn_iff_continuous_domRestrict.mp
       (coefficient_word_time_continuousOn hT ha p.val.1 x))) (fp p)
 have htae (p : Idx) (t : Icc (0:ℝ) T) : term p t =ᵐ[volume]
     fun x => spatialWord (a t) p.val.1 x (spatialWord f p.val.2 x) := by
   have h1 := LpMultiplier.action_ae (spatialWord (a t) p.val.1) (am p t) K (ab p t) (fp p)
   have h2 : fp p =ᵐ[volume] spatialWord f p.val.2 := MemLp.coeFn_toLp _
   filter_upwards [h1, h2] with x hx hy
   rw [hx, hy]
 have hsumcont : Continuous (fun t => (ls.attach.map (fun p => term p t)).sum) :=
   continuous_list_sum ls.attach term (fun p _ => htcont p)
 have heq (t : Icc (0:ℝ) T) : derivativeToL2 β (M t u) =
     (ls.attach.map (fun p => term p t)).sum := by
   have hmf : ContDiff ℝ ∞ (fun x => a t x (f x)) :=
     (P201.Hyperbolic.SymmetricEnergy.operator_apply_bilinear_real (m := m) (𝕜 := 𝕜)).contDiff.comp₂
       (coefficient_slice_contDiff ha.1 t.property) hf
   have hmr : underlyingSection (M t u) =ᵐ[volume] fun x => a t x (f x) := by
     filter_upwards [hM t t.property u, hrep] with x hx hy
     rw [hx, hy]
   have hd := (derivativeToL2_ae β (M t u)).trans (derivativeSection_eq_smooth (M t u) hmf hmr β)
   have hls := lp_list_sum_ae ls.attach (fun p => term p t)
     (fun p x => spatialWord (a t) p.val.1 x (spatialWord f p.val.2 x)) (fun p _ => htae p t)
   apply Lp.ext
   filter_upwards [hd, hls] with x hx hy
   rw [hx, hy]
   change spatialWord (fun y => a t y (f y)) l x = _
   rw [spatialWord_bilinear P201.Hyperbolic.SymmetricEnergy.operator_apply_bilinear_real
     (coefficient_slice_contDiff ha.1 t.property) hf]
   change (ls.map (fun p => spatialWord (a t) p.1 x (spatialWord f p.2 x))).sum = _
   exact congrArg List.sum (List.attach_map_val (l := ls)).symm
 rw [show (Icc (0:ℝ) T).domRestrict (fun t => derivativeToL2 β (M t u)) =
     (fun t => (ls.attach.map (fun p => term p t)).sum) by funext t; exact heq t]
 exact hsumcont

end SmoothTimeContinuity

section CoefficientFamily
open P201Specs.Hyperbolic.SymmetricEnergy
/-- The source data construct an actual uniformly bounded H^k multiplier
family; no time derivative bound is added to the hypotheses. -/
theorem coefficient_multiplier_family {n m s k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {T K : ℝ} (hK : 0 ≤ K) (hk : k ≤ s)
    (a : LowerOrder n m 𝕜) (ha : BoundedSmoothCoefficient T s K a) :
    ∃ M : ℝ → WholeH n m 𝕜 k →L[𝕜] WholeH n m 𝕜 k,
      ∀ t ∈ Icc 0 T, RealizesMultiplier (a t) (M t) ∧
        ‖M t‖ ≤ multiplierConstant n s K := by
  let hs : ∀ t : Icc (0 : ℝ) T, ContDiff ℝ ∞ (a t) :=
    fun t => coefficient_slice_contDiff ha.1 t.property
  let hb : ∀ t : Icc (0 : ℝ) T, ∀ l : List (Fin n), l.length ≤ k →
      ∃ C : ℝ, ∀ x, ‖spatialWord (a t) l x‖ ≤ C := fun t l hl =>
    ⟨K, coefficient_word_bound ha t.property l (hl.trans hk)⟩
  let N : Icc (0 : ℝ) T → WholeH n m 𝕜 k →L[𝕜] WholeH n m 𝕜 k :=
    fun t => smoothMultiplierCLM (a t) (hs t) (hb t)
  refine ⟨fun t => if ht : t ∈ Icc 0 T then N ⟨t, ht⟩ else 0, ?_⟩
  intro t ht
  dsimp only
  rw [dite_eq_left ht]
  have hM : RealizesMultiplier (a t) (N ⟨t, ht⟩) :=
    smoothMultiplierCLM_realizes (a t) (hs ⟨t, ht⟩) (hb ⟨t, ht⟩)
  refine ⟨hM, ?_⟩
  exact multiplier_norm_le_of_realizes hK hk (hs ⟨t, ht⟩)
    (fun l hl => coefficient_word_bound ha ht l hl) (N ⟨t, ht⟩) hM


end CoefficientFamily

section SobolevPairing
open P201Specs.Hyperbolic.SymmetricEnergy
theorem smooth_Q_pairing_bound {n m s k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (hs : 1 ≤ s) (hk : k ≤ s) {K : ℝ} (hK : 0 ≤ K)
    (A : Fin n → P201Specs.Space n → Operator m 𝕜) (B : P201Specs.Space n → Operator m 𝕜)
    (hA : ∀ j, ContDiff ℝ ∞ (A j)) (hB : ContDiff ℝ ∞ B)
    (hsym : ∀ j x, IsSelfAdjoint (A j x))
    (hbA : ∀ j (q : List (Fin n)), q.length ≤ s → ∀ x, ‖spatialWord (A j) q x‖ ≤ K)
    (hbB : ∀ q : List (Fin n), q.length ≤ s → ∀ x, ‖spatialWord B q x‖ ≤ K)
    (Q : WholeH n m 𝕜 (k + 1) →L[𝕜] WholeH n m 𝕜 k) (hQ : RealizesP A B Q)
    (v : WholeH n m 𝕜 (k + 1)) {f : P201Specs.Space n → Fiber 𝕜 m}
    (hf : ContDiff ℝ ∞ f) (hv : underlyingSection v =ᵐ[volume] f) :
    |RCLike.re (inner 𝕜 (lowerOrderCLM v) (Q v))| ≤
      (Fintype.card (P102.U4.SobolevIndex n s) : ℝ) * ((n + 1 : ℕ) : ℝ) * K *
        ((2 : ℝ) ^ s + 1) * ‖lowerOrderCLM v‖ ^ 2 := by
  classical
  let w := lowerOrderCLM v
  let p := fun x => -(∑ j, A j x (spatialWord f [j] x)) - B x (f x)
  have hw : underlyingSection w =ᵐ[volume] f := by
    simpa only [w, lowerOrderCLM_underlying] using hv
  have hder (j : Fin n) : derivativeSection v (⟨{j}, by simp⟩ : P102.U4.SobolevIndex n (k + 1)) =ᵐ[volume]
      spatialWord f [j] := by
    simpa only [spatialPartial, Multiset.sort_singleton] using
      derivativeSection_eq_smooth v hf hv (⟨{j}, by simp⟩ : P102.U4.SobolevIndex n (k + 1))
  have hprep : underlyingSection (Q v) =ᵐ[volume] p := by
    filter_upwards [hQ v, hv, ae_all_iff.mpr hder] with x hx hxv hxd
    dsimp [pSection] at hx
    rw [hx, hxv]
    simp_rw [hxd]
    rfl
  have hp : ContDiff ℝ ∞ p := by
    apply ContDiff.sub
    · apply ContDiff.neg
      apply ContDiff.sum
      intro j _
      exact (P201.Hyperbolic.SymmetricEnergy.operator_apply_bilinear_real (m := m) (𝕜 := 𝕜)).contDiff.comp
        ((hA j).prodMk (spatialWord_contDiff hf [j]))
    · exact (P201.Hyperbolic.SymmetricEnergy.operator_apply_bilinear_real (m := m) (𝕜 := 𝕜)).contDiff.comp
        (hB.prodMk hf)
  let D : ℝ := ((n + 1 : ℕ) : ℝ) * K * ((2 : ℝ) ^ s + 1)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hbound (α : P102.U4.SobolevIndex n k) :
      |∫ x, RCLike.re (inner 𝕜 (derivativeSection w α x) (derivativeSection (Q v) α x))| ≤ D * ‖w‖ ^ 2 := by
    let l := α.val.sort (· ≤ ·)
    have hl : l.length ≤ k := by simpa only [l, Multiset.length_sort] using α.property
    have henergy := smooth_p_word_energy A B hK (norm_nonneg w) hA hB hf hsym l
      (fun j q hq => hbA j q (hq.trans (max_le hs (hl.trans hk))))
      (fun q hq => hbB q (hq.trans (hl.trans hk)))
      (fun q hq => smooth_word_lpNorm_le w hf hw q (hq.trans hl))
      (fun q hq => (smooth_word_lpNorm_le v hf hv q (hq.trans (Nat.add_le_add_right hl 1))).1)
    have heq : (∫ x, RCLike.re (inner 𝕜 (derivativeSection w α x) (derivativeSection (Q v) α x))) =
        ∫ x, RCLike.re (inner 𝕜 (spatialWord f l x) (spatialWord p l x)) := by
      apply integral_congr_ae
      filter_upwards [derivativeSection_eq_smooth w hf hw α,
        derivativeSection_eq_smooth (Q v) hp hprep α] with x h1 h2
      rw [h1, h2]
      rfl
    rw [heq]
    have hpow : (2 : ℝ) ^ l.length ≤ (2 : ℝ) ^ s := pow_le_pow_right₀ (by norm_num) (hl.trans hk)
    exact henergy.2.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add hpow (le_refl 1))
        (mul_nonneg (by positivity) hK)) (sq_nonneg ‖w‖))
  have hi (α : P102.U4.SobolevIndex n k) : Integrable (fun x =>
      inner 𝕜 (derivativeSection w α x) (derivativeSection (Q v) α x)) := by
    have h := L2.integrable_inner (𝕜 := 𝕜) (derivativeToL2 α w) (derivativeToL2 α (Q v))
    apply h.congr
    filter_upwards [derivativeToL2_ae α w, derivativeToL2_ae α (Q v)] with x h1 h2
    rw [h1, h2]
  change |RCLike.re (inner 𝕜 w (Q v))| ≤ _
  rw [wholeH_inner_eq_sum_integral, map_sum]
  simp_rw [← integral_re (hi _)]
  have hcard : (Fintype.card (P102.U4.SobolevIndex n k) : ℝ) ≤
      Fintype.card (P102.U4.SobolevIndex n s) := by
    let inclusion : P102.U4.SobolevIndex n k → P102.U4.SobolevIndex n s :=
      fun α => ⟨α.val, α.property.trans hk⟩
    have hinj : Function.Injective inclusion := by
      intro α β h
      exact Subtype.ext (congrArg (fun z : P102.U4.SobolevIndex n s => z.val) h)
    exact_mod_cast Fintype.card_le_of_injective inclusion hinj
  calc
    _ ≤ ∑ α : P102.U4.SobolevIndex n k,
      |∫ x, RCLike.re (inner 𝕜 (derivativeSection w α x) (derivativeSection (Q v) α x))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _α : P102.U4.SobolevIndex n k, D * ‖w‖ ^ 2 := Finset.sum_le_sum (fun α _ => hbound α)
    _ = (Fintype.card (P102.U4.SobolevIndex n k) : ℝ) * D * ‖w‖ ^ 2 := by simp; ring
    _ ≤ (Fintype.card (P102.U4.SobolevIndex n s) : ℝ) * D * ‖w‖ ^ 2 := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcard hD) (sq_nonneg _)
    _ = _ := by dsimp [D]; ring

/-- The bounded realization of P satisfies the spatial Sobolev energy estimate;
compact smooth density removes all representative regularity assumptions. -/
theorem Q_pairing_bound {n m s k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (hs : 1 ≤ s) (hk : k ≤ s) {K : ℝ} (hK : 0 ≤ K)
    (A : Fin n → P201Specs.Space n → Operator m 𝕜) (B : P201Specs.Space n → Operator m 𝕜)
    (hA : ∀ j, ContDiff ℝ ∞ (A j)) (hB : ContDiff ℝ ∞ B)
    (hsym : ∀ j x, IsSelfAdjoint (A j x))
    (hbA : ∀ j (q : List (Fin n)), q.length ≤ s → ∀ x, ‖spatialWord (A j) q x‖ ≤ K)
    (hbB : ∀ q : List (Fin n), q.length ≤ s → ∀ x, ‖spatialWord B q x‖ ≤ K)
    (Q : WholeH n m 𝕜 (k + 1) →L[𝕜] WholeH n m 𝕜 k) (hQ : RealizesP A B Q) :
    ∀ (v : WholeH n m 𝕜 (k + 1)) (w : WholeH n m 𝕜 k), IsLowerOrder v w →
      |RCLike.re (inner 𝕜 w (Q v))| ≤
      (Fintype.card (P102.U4.SobolevIndex n s) : ℝ) * ((n + 1 : ℕ) : ℝ) * K *
        ((2 : ℝ) ^ s + 1) * ‖w‖ ^ 2 := by
  apply pairing_bound_of_smooth
  intro φ v hφ
  exact smooth_Q_pairing_bound hs hk hK A B hA hB hsym hbA hbB Q hQ v
    (testSection_contDiff φ) (testSection_represents φ v hφ)


end SobolevPairing

/-- The full spatial high-order energy bound under the original coefficient
hypotheses. No commutator or time-continuity certificate is assumed. -/
theorem pairing_bound : PairingStatement := by
  classical
  intro n s hn hs K hK
  let C : ℝ := (Fintype.card (P102.U4.SobolevIndex n s) : ℝ) * ((n + 1 : ℕ) : ℝ) * K *
    ((2 : ℝ) ^ s + 1)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro m 𝕜 _ T hT A B hAB k hk
  have hA (j : Fin n) := coefficient_multiplier_family hK hk (A j) (hAB.1 j)
  choose M hM using hA
  obtain ⟨N, hN⟩ := coefficient_multiplier_family hK hk B hAB.2.1
  let Q := fun t => operatorFromMultipliers (fun j => M j t) (N t)
  have hQ : ∀ t ∈ Icc 0 T, RealizesP (fun j => A j t) (B t) (Q t) := by
    intro t ht
    exact operatorFromMultipliers_realizes (fun j => A j t) (B t) _ _
      (fun j => (hM j t ht).1) (hN t ht).1
  refine ⟨Q, hQ, ?_⟩
  intro t ht
  exact Q_pairing_bound (by omega) hk hK (fun j => A j t) (B t)
    (fun j => coefficient_slice_contDiff (hAB.1 j).1 ht)
    (coefficient_slice_contDiff hAB.2.1.1 ht)
    (fun j x => hAB.2.2 j t ht x)
    (fun j q hq => coefficient_word_bound (hAB.1 j) ht q hq)
    (fun q hq => coefficient_word_bound hAB.2.1 ht q hq) (Q t) (hQ t ht)

/-- The source high-order a priori estimate and its full difference estimate,
now unconditional on the spatial pairing theorem. -/
theorem evolution_estimate : EvolutionStatement := evolution_of_pairing pairing_bound


section StrongMultiplierContinuity
open P201Specs P201Specs.Hyperbolic.SymmetricEnergy P201Specs.Hyperbolic.SymmetricSobolevEnergy

theorem multiplier_continuousOn {n m s k : ℕ} {𝕜 : Type} [RCLike 𝕜]
 {T K C : ℝ} (hT : 0 ≤ T) (hK : 0 ≤ K)
 (a : LowerOrder n m 𝕜) (ha : BoundedSmoothCoefficient T s K a) (hk : k ≤ s)
 (M : ℝ → WholeH n m 𝕜 k →L[𝕜] WholeH n m 𝕜 k)
 (hM : ∀ t ∈ Icc 0 T, RealizesMultiplier (a t) (M t))
 (hb : ∀ t ∈ Icc 0 T, ‖M t‖ ≤ C) :
 ∀ u, ContinuousOn (fun t => M t u) (Icc 0 T) := by
 intro u
 obtain ⟨φ, v, hv, ht⟩ := wholeH_smooth_density u
 have hvc (r : ℕ) : ContinuousOn (fun t => M t (v r)) (Icc 0 T) :=
   multiplier_continuousOn_smooth hT hK a ha hk M hM (v r) (testSection (φ r))
     (testSection_contDiff (φ r)) (testSection_represents (φ r) (v r) (hv r))
 have hz : Tendsto (fun r => C * ‖u - v r‖) atTop (𝓝 0) := by
   have ht' : Tendsto (fun r => u - v r) atTop (𝓝 (u-u)) := tendsto_const_nhds.sub ht
   have htC : Tendsto (fun _ : ℕ => C) atTop (𝓝 C) := tendsto_const_nhds
   simpa using htC.mul ht'.norm
 have hU : TendstoUniformlyOn (fun r t => M t (v r)) (fun t => M t u) atTop (Icc 0 T) := by
   apply Metric.tendstoUniformlyOn_iff.mpr
   intro ε hε
   have he := (tendsto_order.1 hz).2 ε hε
   filter_upwards [he] with r hr t ht
   calc
     dist (M t u) (M t (v r)) = ‖M t (u-v r)‖ := by rw [dist_eq_norm, map_sub]
     _ ≤ C * ‖u-v r‖ := ((M t).le_opNorm _).trans
       (mul_le_mul_of_nonneg_right (hb t ht) (norm_nonneg _))
     _ < ε := hr
 exact hU.continuousOn (Eventually.of_forall hvc).frequently


end StrongMultiplierContinuity

/-- All source coefficient multipliers are uniformly bounded and strongly
continuous on every fixed H^k vector, with one constant depending only n,s,K. -/
theorem multiplier_family : MultiplierStatement := by
  intro n s hn hs K hK
  refine ⟨multiplierConstant n s K, multiplierConstant_nonneg hK, ?_⟩
  intro m 𝕜 _ T hT a ha k hk
  obtain ⟨M, hM⟩ := coefficient_multiplier_family hK hk a ha
  refine ⟨M, hM, ?_⟩
  exact multiplier_continuousOn hT hK a ha hk M
    (fun t ht => (hM t ht).1) (fun t ht => (hM t ht).2)

/-- P(t)=-Σ Aʲ(t)∂ʲ-B(t) is uniformly bounded and strongly continuous from
H^k to H^(k-1) for each source order 1≤k≤s. -/
theorem operator_family : OperatorStatement := operator_of_multiplier multiplier_family

end P201.Hyperbolic.SymmetricSobolevEnergy
