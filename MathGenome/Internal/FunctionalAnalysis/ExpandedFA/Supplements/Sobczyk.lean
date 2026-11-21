import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Supplements.Sobczyk
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C05NormExtension
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Instances.Nat
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
Sobczyk's theorem, paper.tex:6424–6455. Hahn–Banach extends the coordinate
functionals into a fixed dual ball. Compactness and metrizability allow us
to subtract a sequence in its annihilator fiber, retaining the exact norm
bound and obtaining pointwise nullity on the whole ambient normed space.
No completeness or closedness is used in the extension construction.
-/

noncomputable section
open Filter Topology Metric

namespace ExpandedFA.Supplements.Sobczyk

/-- In a compact metric space, a sequence whose subsequential limits all lie
in a nonempty closed set can be approximated by points of that set. -/
lemma compact_fiber_approximation {X : Type*} [MetricSpace X] [CompactSpace X]
    (F : Set X) (hF : IsClosed F) (hne : F.Nonempty) (g : ℕ → X)
    (hlim : ∀ (φ : ℕ → ℕ), Tendsto φ atTop atTop → ∀ a,
      Tendsto (g ∘ φ) atTop (𝓝 a) → a ∈ F) :
    ∃ h : ℕ → X, (∀ n, h n ∈ F) ∧
      Tendsto (fun n => dist (g n) (h n)) atTop (𝓝 0) := by
  have hcompact : IsCompact F := hF.isCompact
  choose h hh hd using fun n => hcompact.exists_infDist_eq_dist hne (g n)
  refine ⟨h, hh, ?_⟩
  have hinf : Tendsto (fun n => infDist (g n) F) atTop (𝓝 0) := by
    apply tendsto_of_subseq_tendsto
    intro φ hφ
    obtain ⟨a, ψ, hψ, ha⟩ := CompactSpace.tendsto_subseq (g ∘ φ)
    have hamem : a ∈ F := hlim (φ ∘ ψ) (hφ.comp hψ.tendsto_atTop) a ha
    refine ⟨ψ, ?_⟩
    simpa only [Function.comp_def, infDist_zero_of_mem hamem] using
      (continuous_infDist_pt F).continuousAt.tendsto.comp ha
  simpa only [hd] using hinf

/-- Correct uniformly bounded extensions by equally bounded annihilating
functionals. The corrected sequence tends pointwise to zero on all of E. -/
lemma weakStar_null_correction {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace.SeparableSpace E]
    (Y : Submodule 𝕜 E) (R : ℝ) (hR : 0 ≤ R) (g : ℕ → E →L[𝕜] 𝕜)
    (hg : ∀ n, ‖g n‖ ≤ R)
    (hY : ∀ y : Y, Tendsto (fun n => g n (y : E)) atTop (𝓝 0)) :
    ∃ h : ℕ → E →L[𝕜] 𝕜,
      (∀ n, ‖h n‖ ≤ R) ∧ (∀ n (y : Y), h n (y : E) = 0) ∧
      ∀ x : E, Tendsto (fun n => (g n - h n) x) atTop (𝓝 0) := by
  let K : Set (WeakDual 𝕜 E) := {f | ‖f.toStrongDual‖ ≤ R}
  have hK : IsCompact K := by
    simpa only [K, Metric.closedBall, dist_zero_right, Set.preimage_ofPred_eq] using
      (WeakDual.isCompact_closedBall (𝕜 := 𝕜) (E := E) 0 R)
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : TopologicalSpace.MetrizableSpace K := WeakDual.metrizable_of_isCompact 𝕜 E K hK
  let : MetricSpace K := TopologicalSpace.metrizableSpaceMetric K
  let gK : ℕ → K := fun n => ⟨StrongDual.toWeakDual (g n), hg n⟩
  let F : Set K := {f | ∀ y : Y, f.val (y : E) = 0}
  have hF : IsClosed F := by
    simp only [F, Set.ofPred_forall]
    exact isClosed_iInter fun y => isClosed_eq
      ((WeakDual.eval_continuous (𝕜 := 𝕜) (y : E)).comp continuous_subtype_val)
      continuous_const
  have hne : F.Nonempty := ⟨⟨0, by simpa [K]⟩, fun _ => rfl⟩
  obtain ⟨hK, hhF, hdist⟩ := compact_fiber_approximation F hF hne gK (by
    intro φ hφ a ha y
    have heval := (((WeakDual.eval_continuous (𝕜 := 𝕜) (y : E)).comp
      continuous_subtype_val).tendsto a).comp ha
    exact tendsto_nhds_unique heval ((hY y).comp hφ))
  refine ⟨fun n => (hK n).val.toStrongDual, fun n => (hK n).property,
    fun n y => hhF n y, ?_⟩
  intro x
  have hu : UniformContinuous (fun f : K => f.val x) :=
    CompactSpace.uniformContinuous_of_continuous
      ((WeakDual.eval_continuous (𝕜 := 𝕜) x).comp continuous_subtype_val)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := Metric.uniformContinuous_iff.mp hu ε hε
  filter_upwards [hdist.eventually (gt_mem_nhds hδ)] with n hn
  have he := hδε hn
  change dist (g n x) ((hK n).val.toStrongDual x) < ε at he
  simpa only [sub_apply, dist_zero_right, ← dist_eq_norm] using he

/-- Sobczyk's extension, with its exact constant, for arbitrary subspaces
of separable normed spaces over either manuscript scalar field. -/
theorem sobczyk_extension : Spec.Extension := by
  intro 𝕜 E _ _ _ _ Y T
  let f : ℕ → Y →L[𝕜] 𝕜 := fun n =>
    (show Y →ₗ[𝕜] 𝕜 from
      { toFun := fun y => T y n
        map_add' := by intros; simp
        map_smul' := by intros; simp }).mkContinuous ‖T‖ (fun y =>
      ((T y).toBCF.norm_coe_le_norm n).trans (T.le_opNorm y))
  have hf : ∀ n, ‖f n‖ ≤ ‖T‖ := fun n =>
    LinearMap.mkContinuous_norm_le _ (norm_nonneg T) _
  have hext : ∀ n, ∃ g : E →L[𝕜] 𝕜,
      (∀ y : Y, g (y : E) = f n y) ∧ ‖g‖ = ‖f n‖ := fun n =>
    P1.C05NormExtension.norm_preserving_extension 𝕜 E Y (f n)
  choose g hgy hgnorm using hext
  have hY : ∀ y : Y, Tendsto (fun n => g n (y : E)) atTop (𝓝 0) := by
    intro y
    have hz := zero_at_infty (T y)
    rw [cocompact_eq_cofinite, Nat.cofinite_eq_atTop] at hz
    simp only [hgy]
    exact hz
  obtain ⟨h, hnorm, hzero, hnull⟩ := weakStar_null_correction Y ‖T‖ (norm_nonneg T)
    g (fun n => (hgnorm n).le.trans (hf n)) hY
  let Sₗ : E →ₗ[𝕜] C0 𝕜 :=
    { toFun := fun x =>
        { toFun := fun n => (g n - h n) x
          continuous_toFun := continuous_of_discreteTopology
          zero_at_infty' := by
            rw [cocompact_eq_cofinite, Nat.cofinite_eq_atTop]
            exact hnull x }
      map_add' := by intros; ext; simp [sub_add_sub_comm]
      map_smul' := by intros; ext; simp }
  have hbound : ∀ x, ‖Sₗ x‖ ≤ (2 * ‖T‖) * ‖x‖ := by
    intro x
    change ‖(Sₗ x).toBCF‖ ≤ _
    apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    intro n
    change ‖(g n - h n) x‖ ≤ _
    calc
      _ ≤ ‖g n - h n‖ * ‖x‖ := (g n - h n).le_opNorm x
      _ ≤ (‖g n‖ + ‖h n‖) * ‖x‖ :=
        mul_le_mul_of_nonneg_right (norm_sub_le _ _) (norm_nonneg x)
      _ ≤ (2 * ‖T‖) * ‖x‖ := by
        gcongr
        linarith [hnorm n, (hgnorm n).le.trans (hf n)]
  refine ⟨Sₗ.mkContinuous (2 * ‖T‖) hbound, ?_,
    LinearMap.mkContinuous_norm_le _ (by positivity) _⟩
  intro y
  ext n
  change (g n - h n) (y : E) = T y n
  simp only [sub_apply, hgy, hzero, sub_zero]
  rfl

/-- The discrete C₀ representation has exactly the manuscript's coordinates
and its supremum norm. -/
theorem c0_sequence_identification : Spec.SequenceIdentification := by
  intro 𝕜 _
  constructor
  · intro x
    constructor
    · rintro ⟨y, rfl⟩
      have h := zero_at_infty y
      rwa [cocompact_eq_cofinite, Nat.cofinite_eq_atTop] at h
    · intro hx
      exact ⟨{ toFun := x
               continuous_toFun := continuous_of_discreteTopology
               zero_at_infty' := by
                 rwa [cocompact_eq_cofinite, Nat.cofinite_eq_atTop] }, rfl⟩
  · intro y
    constructor
    · rintro _ ⟨n, rfl⟩
      exact y.toBCF.norm_coe_le_norm n
    · intro b hb
      exact BoundedContinuousFunction.norm_le_of_nonempty.mpr (fun n => hb ⟨n, rfl⟩)

/-- Inclusion composed with a bounded retraction is a projection onto Y. -/
lemma projection_of_retraction {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (Y : Submodule 𝕜 E)
    (r : E →L[𝕜] Y) (hr : ∀ y : Y, r (y : E) = y) :
    IsProjectionOnto Y (Y.subtypeL.comp r) := by
  refine ⟨?_, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact (r z).property
    · intro hx
      exact ⟨x, congrArg Subtype.val (hr ⟨x, hx⟩)⟩
  · intro y
    exact congrArg Subtype.val (hr y)
  · ext x
    exact congrArg Subtype.val (hr (r x))

/-- Every closed isomorphic copy of c₀ in a separable Banach space is
complemented, with an explicit bounded idempotent having exactly that range. -/
theorem sobczyk_complemented : Spec.ComplementedCopies := by
  intro 𝕜 E _ _ _ _ _ Y _hclosed i
  obtain ⟨S, hS, _hSnorm⟩ := sobczyk_extension 𝕜 E Y i.symm.toContinuousLinearMap
  let r : E →L[𝕜] Y := i.toContinuousLinearMap.comp S
  have hr : ∀ y : Y, r (y : E) = y := by
    intro y
    change i (S (y : E)) = y
    rw [hS y]
    exact i.apply_symm_apply y
  exact ⟨⟨r, hr⟩, Y.subtypeL.comp r, projection_of_retraction Y r hr⟩

/-- For an isometric copy the projection norm is at most two. -/
theorem sobczyk_isometric_projection : Spec.IsometricCopies := by
  intro 𝕜 E _ _ _ _ _ Y _hclosed i
  obtain ⟨S, hS, hSnorm⟩ := sobczyk_extension 𝕜 E Y
    i.symm.toContinuousLinearEquiv.toContinuousLinearMap
  let r : E →L[𝕜] Y := i.toContinuousLinearEquiv.toContinuousLinearMap.comp S
  have hr : ∀ y : Y, r (y : E) = y := by
    intro y
    change i (S (y : E)) = y
    rw [hS y]
    exact i.apply_symm_apply y
  refine ⟨Y.subtypeL.comp r, projection_of_retraction Y r hr, ?_⟩
  have hinv : ‖i.symm.toContinuousLinearEquiv.toContinuousLinearMap‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro y
    simp
  have hSbound : ‖S‖ ≤ 2 := hSnorm.trans (by linarith)
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  change ‖i (S x)‖ ≤ 2 * ‖x‖
  rw [i.norm_map]
  exact (S.le_opNorm x).trans (mul_le_mul_of_nonneg_right hSbound (norm_nonneg x))

end ExpandedFA.Supplements.Sobczyk
