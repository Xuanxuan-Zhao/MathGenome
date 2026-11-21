import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.MomentRegularization
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.MomentProjection
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

noncomputable section
open scoped InnerProductSpace Topology
open Filter Metric
namespace ExpandedFA.PartV.MomentRegularization
universe u v w
variable {𝕜 : Type u} {X : Type v} {Y : Type w} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedAddCommGroup Y]
  [InnerProductSpace 𝕜 X] [InnerProductSpace 𝕜 Y]
  [CompleteSpace X] [CompleteSpace Y]
open MomentProjection.Spec (trialSpace momentOperator)
open Spec (stageMap beta noiseConstant)

theorem stage_bijective (A : X →L[𝕜] Y) (V : Submodule 𝕜 Y)
    [FiniteDimensional 𝕜 V] (hV : V ≤ A.adjoint.ker.orthogonal) :
    Function.Bijective (stageMap A V) := by
  constructor
  · intro z t h
    apply Subtype.ext
    have heq : V.starProjection (A (z : X)) = V.starProjection (A (t : X)) :=
      congrArg (fun v : V => (v : Y)) h
    have hz := (MomentProjection.equation_iff_projection A V (t : X) (z : X)).mp
      ⟨z.prop, heq⟩
    exact hz.trans (Submodule.starProjection_eq_self_iff.mpr t.prop)
  · intro y
    obtain ⟨v, hv⟩ := (MomentProjection.moment_operator_bijective A V hV).2 y
    refine ⟨⟨A.adjoint v, ⟨v, v.prop, rfl⟩⟩, ?_⟩
    exact hv

/-- Compactness of the unit sphere gives the actual least stretching factor. -/
theorem beta_minimum (A : X →L[𝕜] Y) (V : Submodule 𝕜 Y)
    [FiniteDimensional 𝕜 V] (hV : V ≤ A.adjoint.ker.orthogonal) (hne : V ≠ ⊥) :
    0 < beta A V ∧
    IsLeast {r | ∃ z : trialSpace A V, ‖z‖ = 1 ∧ ‖stageMap A V z‖ = r} (beta A V) := by
  have hb := stage_bijective A V hV
  have : Nontrivial V := Submodule.nontrivial_iff_ne_bot.mpr hne
  have : Nontrivial (trialSpace A V) := Function.Surjective.nontrivial hb.2
  let := InnerProductSpace.rclikeToReal 𝕜 (trialSpace A V)
  obtain ⟨z, hz, hmin⟩ := (isCompact_sphere (0 : trialSpace A V) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr (by norm_num : (0 : ℝ) ≤ 1))
    ((stageMap A V).continuous.norm.continuousOn)
  have hzn : ‖z‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hz
  have hl : IsLeast {r | ∃ z : trialSpace A V, ‖z‖ = 1 ∧ ‖stageMap A V z‖ = r}
      ‖stageMap A V z‖ := by
    refine ⟨⟨z, hzn, rfl⟩, ?_⟩
    rintro r ⟨t, ht, rfl⟩
    exact hmin (by simpa only [mem_sphere, dist_zero_right] using ht)
  have heq : beta A V = ‖stageMap A V z‖ := hl.csInf_eq
  refine ⟨?_, heq.symm ▸ hl⟩
  rw [heq]
  apply norm_pos_iff.mpr
  intro hzero
  have : z = 0 := hb.1 (by simpa using hzero)
  simp [this] at hzn

/-- A minimum-stretch vector is an eigenvector of T* T. -/
theorem minimum_stretch_eigenvector (T : X →L[𝕜] Y) (b : ℝ)
    (hleast : IsLeast {r | ∃ z : X, ‖z‖ = 1 ∧ ‖T z‖ = r} b) :
    ∃ e : X, ‖e‖ = 1 ∧ ‖T e‖ = b ∧
      T.adjoint (T e) = ((b ^ 2 : ℝ) : 𝕜) • e := by
  obtain ⟨e, he, hTe⟩ := hleast.1
  let B := T.adjoint.comp T
  have hre (z : X) : B.reApplyInnerSelf z = ‖T z‖ ^ 2 := by
    rw [ContinuousLinearMap.reApplyInnerSelf_apply]
    change RCLike.re (inner 𝕜 (T.adjoint (T z)) z) = _
    rw [T.adjoint_inner_left, inner_self_eq_norm_sq]
  have hmin : IsMinOn B.reApplyInnerSelf (sphere (0 : X) ‖e‖) e := by
    intro z hz
    have hz' : ‖z‖ = 1 := by simpa [he] using hz
    have h := hleast.2 (show ‖T z‖ ∈ {r | ∃ z : X, ‖z‖ = 1 ∧ ‖T z‖ = r}
      from ⟨z, hz', rfl⟩)
    change B.reApplyInnerSelf e ≤ B.reApplyInnerSelf z
    rw [hre, hre, hTe]
    nlinarith [norm_nonneg (T e), norm_nonneg (T z)]
  have hsa : IsSelfAdjoint B := by
    apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    intro z t
    change inner 𝕜 (T.adjoint (T z)) t = inner 𝕜 z (T.adjoint (T t))
    rw [T.adjoint_inner_left, T.adjoint_inner_right]
  have h := hsa.eq_smul_self_of_isLocalExtrOn (Or.inl hmin.isLocalMinOn)
  have hray : B.rayleighQuotient e = b ^ 2 := by
    simp only [ContinuousLinearMap.rayleighQuotient, hre, he, hTe, one_pow, div_one]
  exact ⟨e, he, hTe, by simpa only [hray, B, ContinuousLinearMap.comp_apply] using h⟩

theorem singular_characterization : Spec.SingularCharacterization.{u, v, w} := by
  intro 𝕜 X Y _ _ _ _ _ _ _ A V _ hV hne
  obtain ⟨hb, hleast⟩ := beta_minimum A V hV hne
  obtain ⟨e, he, hTe, heig⟩ := minimum_stretch_eigenvector (stageMap A V) (beta A V) hleast
  have hbK : (beta A V : 𝕜) ≠ 0 := by exact_mod_cast hb.ne'
  let f : V := ((beta A V)⁻¹ : 𝕜) • stageMap A V e
  refine ⟨⟨e, f, he, ?_, ?_, ?_⟩, ?_⟩
  · simp only [f, norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_pos hb, hTe]
    exact inv_mul_cancel₀ hb.ne'
  · simp [f, smul_smul, hbK]
  · rw [show (stageMap A V).adjoint f =
        ((beta A V)⁻¹ : 𝕜) • (stageMap A V).adjoint (stageMap A V e) from map_smul ..,
      heig, smul_smul, RCLike.ofReal_pow]
    congr 1
    field_simp
  · intro σ e f hσ he hf hmap
    apply hleast.2
    refine ⟨e, he, ?_⟩
    rw [hmap, norm_smul, RCLike.norm_ofReal, abs_of_nonneg hσ, hf, mul_one]

theorem stage_bound (A : X →L[𝕜] Y) (V : Submodule 𝕜 Y)
    [FiniteDimensional 𝕜 V] (hV : V ≤ A.adjoint.ker.orthogonal)
    (z : trialSpace A V) : ‖z‖ ≤ noiseConstant A V * ‖stageMap A V z‖ := by
  classical
  by_cases hbot : V = ⊥
  · have hz : z = 0 := by
      apply Subtype.ext
      have := z.prop
      simpa [trialSpace, hbot] using this
    simp [hz]
  · have hb := beta_minimum A V hV hbot
    rw [noiseConstant, ite_eq_right hbot, ← div_eq_inv_mul]
    apply (le_div_iff₀ hb.1).mpr
    by_cases hz : z = 0
    · simp [hz]
    have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
    let t : trialSpace A V := ((‖z‖⁻¹ : ℝ) : 𝕜) • z
    have ht : ‖t‖ = 1 := by
      simpa only [t, RCLike.ofReal_inv] using (norm_smul_inv_norm (𝕜 := 𝕜) hz)
    have h := hb.2.2 (show ‖stageMap A V t‖ ∈
        {r | ∃ z : trialSpace A V, ‖z‖ = 1 ∧ ‖stageMap A V z‖ = r} from
      ⟨t, ht, rfl⟩)
    have hnorm : ‖stageMap A V t‖ = ‖stageMap A V z‖ / ‖z‖ := by
      simp [t, map_smul, norm_smul, div_eq_mul_inv, mul_comm]
    rw [hnorm] at h
    have := (le_div_iff₀ hn).mp h
    nlinarith

theorem noiseConstant_nonneg (A : X →L[𝕜] Y) (V : Submodule 𝕜 Y)
    [FiniteDimensional 𝕜 V] (hV : V ≤ A.adjoint.ker.orthogonal) :
    0 ≤ noiseConstant A V := by
  classical
  by_cases h : V = ⊥
  · simp [noiseConstant, h]
  · simp only [noiseConstant, ite_eq_right h]
    exact (inv_pos.mpr (beta_minimum A V hV h).1).le

theorem noisy_solvable (A : X →L[𝕜] Y) (V : Submodule 𝕜 Y)
    [FiniteDimensional 𝕜 V] (hV : V ≤ A.adjoint.ker.orthogonal) (g : Y) :
    ∃! z : X, z ∈ trialSpace A V ∧ V.starProjection (A z) = V.starProjection g := by
  obtain ⟨z, hz⟩ := (stage_bijective A V hV).2 (V.orthogonalProjectionOnto g)
  refine ⟨z, ⟨z.prop, congrArg (fun y : V => (y : Y)) hz⟩, ?_⟩
  rintro t ⟨ht, heq⟩
  have h : stageMap A V ⟨t, ht⟩ = stageMap A V z := by
    apply Subtype.ext
    exact heq.trans (congrArg (fun y : V => (y : Y)) hz).symm
  exact congrArg (fun x : trialSpace A V => (x : X)) ((stage_bijective A V hV).1 h)

theorem stage_stability : Spec.StageStability.{u, v, w} := by
  intro 𝕜 X Y _ _ _ _ _ _ _ A V _ hV
  exact ⟨stage_bijective A V hV, beta_minimum A V hV,
    noiseConstant_nonneg A V hV, stage_bound A V hV, noisy_solvable A V hV⟩

theorem noisy_error : Spec.NoisyError.{u, v, w} := by
  intro 𝕜 X Y _ _ _ _ _ _ _ A V _ hV x z g δ hnoise hz heq
  let p := (trialSpace A V).starProjection x
  have hp : p ∈ trialSpace A V := (trialSpace A V).starProjection_apply_mem x
  have hpeq : V.starProjection (A p) = V.starProjection (A x) :=
    ((MomentProjection.equation_iff_projection A V x p).mpr rfl).2
  let d : trialSpace A V := ⟨z - p, (trialSpace A V).sub_mem hz hp⟩
  have hd : ‖stageMap A V d‖ ≤ δ := by
    have hid : (stageMap A V d : Y) = V.starProjection (g - A x) := by
      change V.starProjection (A (z - p)) = _
      rw [map_sub, map_sub, heq, hpeq, map_sub]
    change ‖(stageMap A V d : Y)‖ ≤ δ
    rw [hid]
    exact (V.norm_starProjection_apply_le _).trans hnoise
  have hbd : ‖z - p‖ ≤ δ * noiseConstant A V := by
    exact (stage_bound A V hV d).trans
      ((mul_le_mul_of_nonneg_left hd (noiseConstant_nonneg A V hV)).trans_eq (mul_comm ..))
  have hdist : ‖p - x‖ = Metric.infDist x (trialSpace A V : Set X) := by
    rw [norm_sub_rev, ← dist_eq_norm]
    exact (trialSpace A V).dist_starProjection_eq_infDist x
  calc
    ‖z - x‖ ≤ ‖z - p‖ + ‖p - x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ δ * noiseConstant A V + Metric.infDist x (trialSpace A V : Set X) :=
      add_le_add hbd hdist.le
    _ = _ := add_comm ..

theorem zero_stage : Spec.ZeroStage.{u, v, w} := by
  intro 𝕜 X Y _ _ _ _ _ _ _ A g
  simp [noiseConstant, trialSpace]

private def thresholdBase (C : ℕ → ℝ) (n : ℕ) : ℝ :=
  min (1 / ((n : ℝ) + 1)) (1 / (((n : ℝ) + 1) * (C n + 1)))
private def threshold (C : ℕ → ℝ) : ℕ → ℝ
  | 0 => thresholdBase C 0
  | n + 1 => min (threshold C n) (thresholdBase C (n+1))

private theorem threshold_properties (C : ℕ → ℝ) (hC : ∀ n, 0 ≤ C n) :
    (∀ n, 0 < threshold C n) ∧ Antitone (threshold C) ∧
    (∀ n, threshold C n ≤ 1 / ((n : ℝ) + 1)) ∧
    (∀ n, threshold C n * C n ≤ 1 / ((n : ℝ) + 1)) := by
  have hbase (n : ℕ) : 0 < thresholdBase C n := by
    exact lt_min (one_div_pos.mpr (by positivity))
      (one_div_pos.mpr (mul_pos (by positivity) (by linarith [hC n])))
  have hpos (n : ℕ) : 0 < threshold C n := by
    induction n with
    | zero => exact hbase 0
    | succ n ih => exact lt_min ih (hbase _)
  have hle (n : ℕ) : threshold C n ≤ thresholdBase C n := by
    cases n with
    | zero => rfl
    | succ n => exact min_le_right ..
  refine ⟨hpos, antitone_nat_of_succ_le (fun n => min_le_left ..),
    fun n => (hle n).trans (min_le_left ..), ?_⟩
  intro n
  have ht := (hle n).trans (min_le_right ..)
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hc : 0 < C n + 1 := by linarith [hC n]
  have hm : threshold C n * ((n : ℝ) + 1) * (C n + 1) ≤ 1 := by
    have := (le_div_iff₀ (mul_pos hn hc)).mp ht
    nlinarith
  apply (le_div_iff₀ hn).mpr
  nlinarith [hpos n]

/-- Choose the stage immediately before the first threshold below the noise level. -/
theorem slow_choice : Spec.SlowChoice := by
  intro C hC
  classical
  obtain ⟨hp, ha, hb, hc⟩ := threshold_properties C hC
  have hlim : Tendsto (threshold C) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => (hp n).le) hb
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hex (δ : ℝ) (hδ : 0 < δ) : ∃ k, threshold C k < δ :=
    (hlim.eventually (gt_mem_nhds hδ)).exists
  let first (δ : ℝ) : ℕ := if h : 0 < δ then Nat.find (hex δ h) else 0
  let n (δ : ℝ) : ℕ := first δ - 1
  have hfirst (δ : ℝ) (hδ : 0 < δ) : threshold C (first δ) < δ := by
    simp only [first, dite_eq_left hδ]
    exact Nat.find_spec (hex δ hδ)
  have hnlim : Tendsto n (𝓝[>] (0 : ℝ)) atTop := by
    apply Filter.tendsto_atTop.2
    intro N
    filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds (hp (N+1))).filter_mono
      nhdsWithin_le_nhds] with δ hδ hsmall
    have hδ : 0 < δ := hδ
    have hlt : N+1 < first δ := by
      by_contra h
      have := ha (Nat.le_of_not_gt h)
      have hf := hfirst δ hδ
      linarith
    dsimp [n]
    omega
  have hgood : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      0 ≤ δ * C (n δ) ∧ δ * C (n δ) ≤ 1 / ((n δ : ℝ) + 1) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (hp 0)).filter_mono nhdsWithin_le_nhds] with δ hδ hsmall
    have hδ : 0 < δ := hδ
    have hfpos : 0 < first δ := by
      by_contra h
      have hf := hfirst δ hδ
      have hz : first δ = 0 := by omega
      rw [hz] at hf
      linarith
    have hprior : δ ≤ threshold C (n δ) := by
      have hi : n δ < Nat.find (hex δ hδ) := by
        have he : first δ = Nat.find (hex δ hδ) := by simp [first, hδ]
        dsimp [n]
        omega
      exact le_of_not_gt (Nat.find_min (hex δ hδ) hi)
    exact ⟨mul_nonneg hδ.le (hC _),
      (mul_le_mul_of_nonneg_right hprior (hC _)).trans (hc _)⟩
  refine ⟨n, hnlim, ?_⟩
  apply squeeze_zero' (hgood.mono fun _ h => h.1) (hgood.mono fun _ h => h.2)
  exact (show Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) by
    exact tendsto_one_div_add_atTop_nhds_zero_nat).comp hnlim

theorem moment_regularization : Spec.Regularization.{u, v, w} := by
  intro 𝕜 X Y _ _ _ _ _ _ _ A V _ hmono hdense x hx
  have hV (k : ℕ) : V k ≤ A.adjoint.ker.orthogonal :=
    (MomentProjection.stage_properties.{u, v, w, 0} A V hmono hdense k).1
  have hnonneg (k : ℕ) : 0 ≤ noiseConstant A (V k) :=
    noiseConstant_nonneg A (V k) (hV k)
  refine ⟨slow_choice (fun k => noiseConstant A (V k)) hnonneg, ?_⟩
  intro n hn hnoise g z hg hz
  have hproj : Tendsto (fun k => (trialSpace A (V k)).starProjection x) atTop (𝓝 x) :=
    (MomentProjection.moment_projection A V hmono hdense (A x) x rfl hx).2.2
  have hbias : Tendsto (fun δ => Metric.infDist x (trialSpace A (V (n δ)) : Set X))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := (((tendsto_const_nhds : Tendsto (fun _ : ℝ => x) (𝓝[>] (0 : ℝ)) (𝓝 x)).sub (hproj.comp hn)).norm)
    simpa only [sub_self, norm_zero, Function.comp_apply, ← dist_eq_norm,
      Submodule.dist_starProjection_eq_infDist] using h
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _))
    (show ∀ᶠ δ in 𝓝[>] (0 : ℝ), ‖z δ - x‖ ≤
      Metric.infDist x (trialSpace A (V (n δ)) : Set X) +
        δ * noiseConstant A (V (n δ)) from ?_)
  · simpa only [add_zero] using hbias.add hnoise
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact noisy_error A (V (n δ)) (hV _) x (z δ) (g δ) δ (hg δ hδ)
      (hz δ hδ).1 (hz δ hδ).2

end ExpandedFA.PartV.MomentRegularization
