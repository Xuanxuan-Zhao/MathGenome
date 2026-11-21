import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.JamesWitness
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C13Embedding
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C13Alaoglu
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C05NormExtension
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C06DoubleAnnihilator
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace ExpandedFA.P1.JamesWitness
open Filter Topology TopologicalSpace
open scoped Topology
noncomputable section
set_option maxHeartbeats 2000000

/-- A closed noncompact set has an image-closure point outside an embedded
copy whenever its image lies in a compact set. -/
theorem exists_closure_point_outside_range {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {j : X → Y} (hj : IsEmbedding j) {A : Set X} {B : Set Y}
    (hA : IsClosed A) (hnc : ¬ IsCompact A) (hB : IsCompact B)
    (hAB : j '' A ⊆ B) :
    ∃ y ∈ closure (j '' A), y ∉ Set.range j := by
  by_contra! h
  have hc : IsCompact (closure (j '' A)) :=
    hB.of_isClosed_subset isClosed_closure (closure_minimal hAB hB.isClosed)
  have hp := hj.isInducing.isCompact_preimage' hc h
  rw [← hj.closure_eq_preimage_closure_image, hA.closure_eq] at hp
  exact hnc hp

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- In the bidual, annihilating the annihilator of a finite-dimensional
subspace is exactly membership in its canonical image. -/
theorem finite_double_annihilator (M : Submodule 𝕜 E)
    [FiniteDimensional 𝕜 M] (Ψ : (E →L[𝕜] 𝕜) →L[𝕜] 𝕜)
    (hΨ : ∀ f : E →L[𝕜] 𝕜, (∀ x ∈ M, f x = 0) → Ψ f = 0) :
    ∃ x ∈ M, C04CanonicalMap.canonicalEvaluation 𝕜 E x = Ψ := by
  let J : E →L[𝕜] ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜) :=
    C04CanonicalMap.canonicalEvaluation 𝕜 E
  let N : Submodule 𝕜 ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜) := M.map J.toLinearMap
  have hmem : Ψ ∈ @closure ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜)
      (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 (E →L[𝕜] 𝕜))
      (N : Set ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜)) := by
    unfold C12WeakStar.Spec.WeakStarTopologyValue
    rw [← C06DoubleAnnihilator.double_annihilator_dual 𝕜 (E →L[𝕜] 𝕜) N]
    intro f hf
    apply hΨ f
    intro x hx
    exact hf (J x) (Submodule.mem_map_of_mem hx)
  have hclosed : @IsClosed ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜)
      (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 (E →L[𝕜] 𝕜))
      (N : Set ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜)) := by
    letI : AddCommGroup (WeakDual 𝕜 (E →L[𝕜] 𝕜)) :=
      inferInstanceAs (AddCommGroup ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜))
    let Jw : E →ₗ[𝕜] WeakDual 𝕜 (E →L[𝕜] 𝕜) :=
      StrongDual.toWeakDual.toLinearMap.comp J.toLinearMap
    let Nw : Submodule 𝕜 (WeakDual 𝕜 (E →L[𝕜] 𝕜)) := M.map Jw
    have : FiniteDimensional 𝕜 Nw := inferInstance
    change @IsClosed (WeakDual 𝕜 (E →L[𝕜] 𝕜))
      (TopologicalSpace.induced id inferInstance) (Nw : Set _)
    rw [induced_id]
    exact Nw.closed_of_finiteDimensional
  have heq := @IsClosed.closure_eq _
    (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 (E →L[𝕜] 𝕜)) _ hclosed
  rw [heq] at hmem
  exact hmem

/-- A bidual point uniformly separated from J(E) has a unit functional
annihilating any finite-dimensional M and taking a prescribed small value. -/
theorem exists_unit_annihilator_value
    (Φ : (E →L[𝕜] 𝕜) →L[𝕜] 𝕜) {δ θ : ℝ}
    (hθ : 0 < θ) (hθδ : θ < δ)
    (hgap : ∀ x : E, δ ≤ ‖Φ - C04CanonicalMap.canonicalEvaluation 𝕜 E x‖)
    (M : Submodule 𝕜 E) [FiniteDimensional 𝕜 M] :
    ∃ f : E →L[𝕜] 𝕜, ‖f‖ ≤ 1 ∧ (∀ x ∈ M, f x = 0) ∧ Φ f = (θ : 𝕜) := by
  let P : Submodule 𝕜 (E →L[𝕜] 𝕜) :=
    { carrier := {f | ∀ x ∈ M, f x = 0}
      zero_mem' := by simp
      add_mem' := by intro f g hf hg x hx; simp [hf x hx, hg x hx]
      smul_mem' := by intro c f hf x hx; simp [hf x hx] }
  letI : NormedAddCommGroup P := inferInstance
  letI : NormedSpace 𝕜 P := inferInstance
  let R : P →L[𝕜] 𝕜 := Φ.comp P.subtypeL
  obtain ⟨F, hF, hFnorm⟩ := C05NormExtension.norm_preserving_extension 𝕜
    (E →L[𝕜] 𝕜) P R
  have hvan : ∀ f : E →L[𝕜] 𝕜, (∀ x ∈ M, f x = 0) → (Φ - F) f = 0 := by
    intro f hf
    exact sub_eq_zero.mpr (hF ⟨f, hf⟩).symm
  obtain ⟨x, _, hx⟩ := finite_double_annihilator M (Φ - F) hvan
  have hδ : δ ≤ ‖R‖ := by
    have hh := hgap x
    rw [hx] at hh
    change δ ≤ ‖Φ - (Φ - F)‖ at hh
    have he : Φ - (Φ - F) = F := sub_sub_cancel Φ F
    exact hFnorm ▸ (he ▸ hh)
  have hex : ∃ f : P, ‖f‖ = 1 ∧ θ < ‖R f‖ := by
    by_contra! hn
    have hle : ‖R‖ ≤ θ := ContinuousLinearMap.opNorm_le_of_unit_norm hθ.le hn
    exact (hθδ.trans_le hδ).not_ge hle
  obtain ⟨f, hf, hval⟩ := hex
  have hnz : Φ (f : E →L[𝕜] 𝕜) ≠ 0 := by
    exact norm_pos_iff.mp (hθ.trans hval)
  let c : 𝕜 := (θ : 𝕜) / Φ (f : E →L[𝕜] 𝕜)
  refine ⟨c • (f : E →L[𝕜] 𝕜), ?_, ?_, ?_⟩
  · rw [norm_smul]
    change ‖c‖ * ‖f‖ ≤ 1
    rw [hf, mul_one]
    dsimp [c]
    rw [norm_div, RCLike.norm_ofReal, abs_of_pos hθ]
    exact (div_le_one (hθ.trans hval)).mpr hval.le
  · intro x hx
    simp only [smul_apply, f.property x hx, smul_zero]
  · rw [map_smul]
    exact div_mul_cancel₀ _ hnz

/-- Uniformly bounded functionals vanishing on longer finite prefixes of a
dense sequence converge pointwise to zero on the whole set. -/
theorem tendsto_zero_of_dense_prefix (A : Set E) (a : ℕ → A)
    (ha : DenseRange a) (f : ℕ → E →L[𝕜] 𝕜)
    (hf : ∀ n, ‖f n‖ ≤ 1)
    (hz : ∀ n j, j < n → f n (a j) = 0) :
    ∀ x ∈ A, Tendsto (fun n => f n x) atTop (𝓝 0) := by
  intro x hx
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨j, hj⟩ := ha.exists_dist_lt (⟨x, hx⟩ : A) hε
  refine ⟨j + 1, fun n hn => ?_⟩
  have hzero := hz n j (by omega)
  rw [dist_zero_right, ← sub_zero (f n x), ← hzero, ← map_sub]
  calc
    ‖f n (x - (a j : E))‖ ≤ ‖f n‖ * ‖x - (a j : E)‖ := (f n).le_opNorm _
    _ ≤ 1 * ‖x - (a j : E)‖ := mul_le_mul_of_nonneg_right (hf n) (norm_nonneg _)
    _ < ε := by simpa only [one_mul, ← dist_eq_norm, Subtype.dist_eq] using hj

/-- Noncompactness supplies a genuine bidual point outside the canonical
image, in the weak-star closure of J(A). -/
theorem exists_bidual_escape (A : Set E)
    (hunit : A ⊆ {x | ‖x‖ ≤ 1})
    (hclosed : @IsClosed E (C12DualPairSpec.DualPairTopologyValue 𝕜 E
      (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E)) A)
    (hnc : ¬ @IsCompact E (C12DualPairSpec.DualPairTopologyValue 𝕜 E
      (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E)) A) :
    ∃ Φ : (E →L[𝕜] 𝕜) →L[𝕜] 𝕜,
      Φ ∈ @closure _ (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 (E →L[𝕜] 𝕜))
        (C04CanonicalMap.canonicalEvaluation 𝕜 E '' A) ∧
      Φ ∉ Set.range (C04CanonicalMap.canonicalEvaluation 𝕜 E) := by
  have ht2 : @T2Space ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜)
      (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 (E →L[𝕜] 𝕜)) := by
    change @T2Space (WeakDual 𝕜 (E →L[𝕜] 𝕜))
      (TopologicalSpace.induced id inferInstance)
    rw [induced_id]
    infer_instance
  apply @exists_closure_point_outside_range E ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜)
    (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E))
    (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 (E →L[𝕜] 𝕜)) ht2
    (C04CanonicalMap.canonicalEvaluation 𝕜 E)
    (C13Embedding.canonicalEvaluation_weak_embedding 𝕜 E) A
    {Φ | ‖Φ‖ ≤ 1} hclosed hnc (C13Alaoglu.banach_alaoglu 𝕜 (E →L[𝕜] 𝕜))
  rintro _ ⟨x, hx, rfl⟩
  change ‖C04CanonicalMap.canonicalEvaluation 𝕜 E x‖ ≤ 1
  exact (C05BidualIsometry.canonicalEvaluation_norm 𝕜 E x).le.trans (hunit hx)

/-- Evaluation of a weak-star closure point is bounded by the A-seminorm. -/
theorem norm_eval_le_sup (A : Set E) (hunit : A ⊆ {x | ‖x‖ ≤ 1})
    (Φ : (E →L[𝕜] 𝕜) →L[𝕜] 𝕜)
    (hΦ : Φ ∈ @closure _ (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 (E →L[𝕜] 𝕜))
      (C04CanonicalMap.canonicalEvaluation 𝕜 E '' A)) (g : E →L[𝕜] 𝕜) :
    ‖Φ g‖ ≤ sSup ((fun x => ‖g x‖) '' A) := by
  have hb : BddAbove ((fun x => ‖g x‖) '' A) := by
    refine ⟨‖g‖, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact g.unit_le_opNorm x (hunit hx)
  have hc : @IsClosed ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜)
      (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 (E →L[𝕜] 𝕜))
      {Ψ | ‖Ψ g‖ ≤ sSup ((fun x => ‖g x‖) '' A)} := by
    change @IsClosed (WeakDual 𝕜 (E →L[𝕜] 𝕜))
      (TopologicalSpace.induced id inferInstance) _
    rw [induced_id]
    exact isClosed_le (WeakDual.eval_continuous g).norm continuous_const
  apply @closure_minimal _
    (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 (E →L[𝕜] 𝕜))
    (C04CanonicalMap.canonicalEvaluation 𝕜 E '' A)
    {Ψ | ‖Ψ g‖ ≤ sSup ((fun x => ‖g x‖) '' A)} ?_ hc Φ hΦ
  rintro _ ⟨x, hx, rfl⟩
  exact le_csSup hb ⟨x, hx, rfl⟩

/-- The separable witness lemma, over both scalar fields. -/
theorem separable_witness : Spec.SeparableWitness := by
  classical
  intro 𝕜 E _ _ _ _ A hne hunit hsep hclosed hnc
  letI : NormedAddCommGroup ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜) := inferInstance
  obtain ⟨Φ, hΦ, hΦout⟩ := exists_bidual_escape A hunit hclosed hnc
  let J : E →L[𝕜] ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜) :=
    C04CanonicalMap.canonicalEvaluation 𝕜 E
  have hJclosed : IsClosed (Set.range J) :=
    (C05BidualIsometry.canonicalEvaluation_linear_isometry 𝕜 E).2.2.isClosedEmbedding.isClosed_range
  let δ := Metric.infDist Φ (Set.range J)
  have hδ : 0 < δ :=
    (hJclosed.notMem_iff_infDist_pos (Set.range_nonempty J)).mp hΦout
  let θ : ℝ := min δ 1 / 2
  have hθ : 0 < θ := div_pos (lt_min hδ zero_lt_one) (by norm_num)
  have hθmin : θ < min δ 1 := by dsimp [θ]; linarith [lt_min hδ zero_lt_one]
  have hθδ : θ < δ := hθmin.trans_le (min_le_left _ _)
  have hθone : θ < 1 := hθmin.trans_le (min_le_right _ _)
  have hgap : ∀ x, δ ≤ ‖Φ - C04CanonicalMap.canonicalEvaluation 𝕜 E x‖ := by
    intro x
    have hh : δ ≤ dist Φ (J x) := Metric.infDist_le_dist_of_mem (Set.mem_range_self x)
    rw [dist_eq_norm] at hh
    exact hh
  letI : SeparableSpace A := hsep.separableSpace
  letI : Nonempty A := hne.to_subtype
  obtain ⟨a, ha⟩ := exists_dense_seq A
  let M (n : ℕ) : Submodule 𝕜 E :=
    Submodule.span 𝕜 (((Finset.range n).image (fun j => (a j : E))) : Set E)
  have hM (n : ℕ) : FiniteDimensional 𝕜 (M n) := by dsimp [M]; infer_instance
  have hex (n : ℕ) : ∃ f : E →L[𝕜] 𝕜,
      ‖f‖ ≤ 1 ∧ (∀ x ∈ M n, f x = 0) ∧ Φ f = (θ : 𝕜) := by
    haveI := hM n
    exact exists_unit_annihilator_value Φ hθ hθδ hgap (M n)
  choose f hf hz hΦf using hex
  refine ⟨θ, f, hθ, hθone, hf, ?_, ?_⟩
  · apply tendsto_zero_of_dense_prefix A a ha f hf
    intro n j hj
    apply hz n
    apply Submodule.subset_span
    exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩
  · intro g hg
    have hconv : Convex ℝ {g : E →L[𝕜] 𝕜 | Φ g = (θ : 𝕜)} :=
      (convex_singleton (θ : 𝕜)).linear_preimage (Φ.restrictScalars ℝ).toLinearMap
    have hgval : Φ g = (θ : 𝕜) :=
      convexHull_min (by rintro _ ⟨n, rfl⟩; exact hΦf n) hconv hg
    have hh := norm_eval_le_sup A hunit Φ hΦ g
    simpa only [hgval, RCLike.norm_ofReal, abs_of_pos hθ] using hh

end
end ExpandedFA.P1.JamesWitness
