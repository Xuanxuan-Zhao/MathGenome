import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.SpectralRegularization
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.Picard
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.Positivity

noncomputable section
universe u v w a b z
namespace ExpandedFA.PartV.SpectralRegularization
open Filter
open scoped Topology InnerProductSpace
open Spec

abbrev regularized := @Spec.regularizedValue
abbrev filterBound := @Spec.filterBoundValue
abbrev cutoff := @Spec.cutoffValue
abbrev tikhonov := @Spec.tikhonovValue

variable {𝕜 : Type u} {H : Type v} {G : Type w} {J : Type z} [RCLike 𝕜]
  [NormedAddCommGroup H] [NormedAddCommGroup G]
  [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 G]
  [CompleteSpace H] [CompleteSpace G]

lemma synthesis_norm_sq (e : J → H) (he : Orthonormal 𝕜 e) (c : J → 𝕜)
    (hc : Summable (fun j => ‖c j‖ ^ 2)) :
    ‖∑' j, c j • e j‖ ^ 2 = ∑' j, ‖c j‖ ^ 2 := by
  have hs := Picard.orthonormal_synthesis_summable e he c hc
  apply tendsto_nhds_unique (hs.hasSum.norm.pow 2)
  have ht : Tendsto (fun F : Finset J => ∑ j ∈ F, ‖c j‖ ^ 2) atTop
      (𝓝 (∑' j, ‖c j‖ ^ 2)) := hc.hasSum
  have hf (F : Finset J) : ‖∑ j ∈ F, c j • e j‖ ^ 2 = ∑ j ∈ F, ‖c j‖ ^ 2 := by
    simpa only [LinearIsometry.toSpanSingleton_apply] using he.orthogonalFamily.norm_sum c F
  change Tendsto (fun F : Finset J => ‖∑ j ∈ F, c j • e j‖ ^ 2) atTop _
  simpa only [hf] using ht

omit [CompleteSpace G] in
lemma weighted_summable (g : J → G) (hg : Orthonormal 𝕜 g)
    (c : J → 𝕜) (C : ℝ) (_hC : 0 ≤ C) (hc : ∀ j, ‖c j‖ ≤ C) (f : G) :
    Summable (fun j => ‖c j * inner 𝕜 (g j) f‖ ^ 2) := by
  refine ((hg.inner_products_summable f).mul_left (C ^ 2)).of_nonneg_of_le
    (fun _ => sq_nonneg _) ?_
  intro j
  rw [norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hc j) 2) (sq_nonneg _)

omit [CompleteSpace G] in
lemma weighted_norm_le (e : J → H) (g : J → G)
    (he : Orthonormal 𝕜 e) (hg : Orthonormal 𝕜 g)
    (c : J → 𝕜) (C : ℝ) (hC : 0 ≤ C) (hc : ∀ j, ‖c j‖ ≤ C) (f : G) :
    ‖∑' j, (c j * inner 𝕜 (g j) f) • e j‖ ≤ C * ‖f‖ := by
  have hs := weighted_summable g hg c C hC hc f
  have hsq : ‖∑' j, (c j * inner 𝕜 (g j) f) • e j‖ ^ 2 ≤ (C * ‖f‖) ^ 2 := by
    rw [synthesis_norm_sq e he _ hs, mul_pow]
    calc
      _ ≤ ∑' j, C ^ 2 * ‖inner 𝕜 (g j) f‖ ^ 2 := by
        apply hs.tsum_le_tsum _ ((hg.inner_products_summable f).mul_left _)
        intro j
        rw [norm_mul, mul_pow]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg _) (hc j) 2) (sq_nonneg _)
      _ = C ^ 2 * ∑' j, ‖inner 𝕜 (g j) f‖ ^ 2 := tsum_mul_left
      _ ≤ _ := mul_le_mul_of_nonneg_left (hg.tsum_inner_products_le f) (sq_nonneg _)
  nlinarith [norm_nonneg (∑' j, (c j * inner 𝕜 (g j) f) • e j),
    mul_nonneg hC (norm_nonneg f)]

/-- Bounded diagonal synthesis between two orthonormal families. -/
def diagonalMap (e : J → H) (g : J → G)
    (he : Orthonormal 𝕜 e) (hg : Orthonormal 𝕜 g)
    (c : J → 𝕜) (C : ℝ) (hC : 0 ≤ C) (hc : ∀ j, ‖c j‖ ≤ C) : G →L[𝕜] H :=
  LinearMap.mkContinuous
    { toFun := fun f => ∑' j, (c j * inner 𝕜 (g j) f) • e j
      map_add' := by
        intro f f'
        simp only [inner_add_right, mul_add, add_smul]
        exact (Picard.orthonormal_synthesis_summable e he _
          (weighted_summable g hg c C hC hc f)).tsum_add
          (Picard.orthonormal_synthesis_summable e he _
            (weighted_summable g hg c C hC hc f'))
      map_smul' := by
        intro k f
        simp only [inner_smul_right, RingHom.id_apply, mul_left_comm (c _) k, mul_smul]
        exact tsum_const_smul'' k }
    C (weighted_norm_le e g he hg c C hC hc)

theorem boundedness : Spec.Boundedness.{u,v,w} := by
  intro 𝕜 H G _ _ _ _ _ _ _ A S ψ C hC hc
  constructor
  · intro f
    exact (Picard.orthonormal_synthesis_summable S.rightVector S.right_orthonormal _
      (weighted_summable S.leftVector S.left_orthonormal _ C hC hc f)).hasSum
  · refine ⟨diagonalMap S.rightVector S.leftVector S.right_orthonormal
      S.left_orthonormal _ C hC hc, fun _ => rfl, ?_⟩
    exact LinearMap.mkContinuous_norm_le _ hC _

theorem canonical_bound : Spec.CanonicalBound.{u,v,w} := by
  intro 𝕜 H G _ _ _ _ _ _ _ A S ψ hb
  have hb' : BddAbove (insert 0 (Set.range (fun j => ‖ψ (S.sigma j)‖))) :=
    hb.insert 0
  refine ⟨le_csSup hb' (Set.mem_insert _ _), ?_, ?_⟩
  · intro j
    exact le_csSup hb' (Set.mem_insert_of_mem _ (Set.mem_range_self j))
  · intro C hC hc
    apply csSup_le (Set.insert_nonempty _ _)
    rintro r (rfl | ⟨j, rfl⟩)
    · exact hC
    · exact hc j

/-- The singular coefficients of exact data, with the conjugate-first convention. -/
lemma exact_coefficient (A : H →L[𝕜] G) (S : System A) (x : H) (j : S.Index) :
    inner 𝕜 (S.leftVector j) (A x) =
      (S.sigma j : 𝕜) * inner 𝕜 (S.rightVector j) x := by
  rw [← ContinuousLinearMap.adjoint_inner_left, S.adjoint_left,
    inner_smul_left, RCLike.conj_ofReal]

theorem exact_convergence : Spec.ExactConvergence.{u,v,w,a} := by
  intro 𝕜 H G _ _ _ _ _ _ _ A S I l ψ C h x hx
  obtain ⟨hC, hc, ⟨M, hM, hm⟩, hlim⟩ := h
  let m : I → S.Index → 𝕜 := fun η j => (S.sigma j : 𝕜) * ψ η (S.sigma j)
  let c : S.Index → 𝕜 := fun j => inner 𝕜 (S.rightVector j) x
  have hbound (η : I) (j : S.Index) : ‖m η j - 1‖ ≤ M + 1 := by
    exact (norm_sub_le _ _).trans (by simpa only [norm_one, m] using add_le_add (hm η j) (le_refl (1 : ℝ)))
  have hrepr : HasSum (fun j => c j • S.rightVector j) x := by
    apply (Hilbert.PreHilbertBesselParseval.closedSpan_iff_net_convergence
      𝕜 H S.Index S.rightVector S.right_orthonormal x).mp
    rwa [S.right_closedSpan]
  have herrsum (η : I) : Summable (fun j => ‖(m η j - 1) * c j‖ ^ 2) :=
    weighted_summable S.rightVector S.right_orthonormal _ (M + 1) (by positivity)
      (hbound η) x
  have herr (η : I) :
      (∑' j, ((m η j - 1) * c j) • S.rightVector j) =
        regularizedValue S (ψ η) (A x) - x := by
    have hsum := (boundedness 𝕜 H G A S (ψ η) (C η) (hC η) (hc η)).1 (A x)
    convert (hsum.sub hrepr).tsum_eq using 1
    congr 1
    ext j
    rw [exact_coefficient, ← sub_smul]
    congr 1
    dsimp [m, c]
    ring
  have hsq (η : I) :
      ‖regularizedValue S (ψ η) (A x) - x‖ ^ 2 =
        ∑' j, ‖(m η j - 1) * c j‖ ^ 2 := by
    rw [← herr η]
    exact synthesis_norm_sq S.rightVector S.right_orthonormal _ (herrsum η)
  have hdom := (S.right_orthonormal.inner_products_summable x).mul_left ((M + 1) ^ 2)
  have hconv : Tendsto (fun η => ∑' j, ‖(m η j - 1) * c j‖ ^ 2) l (𝓝 0) := by
    convert tendsto_tsum_of_dominated_convergence hdom (g := fun _ => (0 : ℝ)) ?_ ?_ using 1
    · simp
    · intro j
      simpa only [sub_self, zero_mul, norm_zero, zero_pow (by decide : 2 ≠ 0)] using
        (((hlim j).sub_const 1).mul_const (c j)).norm.pow 2
    · apply Eventually.of_forall
      intro η j
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_mul, mul_pow]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (hbound η j) 2) (sq_nonneg _)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hs : Tendsto (fun η => ‖regularizedValue S (ψ η) (A x) - x‖ ^ 2) l (𝓝 0) := by
    simpa only [hsq] using hconv
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hs.sqrt

theorem noise_estimate : Spec.NoiseEstimate.{u,v,w} := by
  intro 𝕜 H G _ _ _ _ _ _ _ A S ψ C δ hC hc f g hfg
  obtain ⟨R, hR, hn⟩ := (boundedness 𝕜 H G A S ψ C hC hc).2
  rw [← hR, ← hR, ← map_sub]
  calc
    ‖R (g - f)‖ ≤ ‖R‖ * ‖g - f‖ := R.le_opNorm _
    _ ≤ C * δ := mul_le_mul hn hfg (norm_nonneg _) hC
    _ = δ * C := mul_comm _ _

theorem noisy_convergence : Spec.NoisyConvergence.{u,v,w,a,b} := by
  intro 𝕜 H G _ _ _ _ _ _ _ A S I l ψ C h P p η δ g x hx hη hg hδ
  have hexact := (exact_convergence 𝕜 H G A S I l ψ C h x hx).comp hη
  have hnoise : Tendsto (fun t => regularizedValue S (ψ (η t)) (g t) -
      regularizedValue S (ψ (η t)) (A x)) p (𝓝 0) := by
    apply squeeze_zero_norm (fun t => ?_) hδ
    exact noise_estimate 𝕜 H G A S (ψ (η t)) (C (η t)) (δ t)
      (h.1 _) (h.2.1 _) _ _ (hg t)
  simpa only [Function.comp_def, sub_add_cancel, zero_add] using hnoise.add hexact

lemma cutoff_norm_le (ε : PositiveParameter) (σ : ℝ) (hσ : 0 < σ) :
    ‖cutoffValue (𝕜 := 𝕜) ε σ‖ ≤ (ε : ℝ)⁻¹ := by
  dsimp [cutoffValue]
  split_ifs with h
  · rw [norm_inv, RCLike.norm_ofReal, abs_of_pos hσ]
    exact inv_anti₀ ε.property h
  · simpa only [norm_zero] using inv_nonneg.mpr ε.property.le

lemma cutoff_multiplier_bound (ε : PositiveParameter) (σ : ℝ) (hσ : 0 < σ) :
    ‖(σ : 𝕜) * cutoffValue ε σ‖ ≤ 1 := by
  dsimp [cutoffValue]
  split_ifs
  · have hn : (σ : 𝕜) ≠ 0 := by exact_mod_cast hσ.ne'
    simp [hn]
  · simp

lemma cutoff_multiplier_tendsto (σ : ℝ) (hσ : 0 < σ) :
    Tendsto (fun ε => (σ : 𝕜) * cutoffValue ε σ) smallParameters (𝓝 1) := by
  have ht : Tendsto (fun ε : PositiveParameter => (ε : ℝ)) smallParameters (𝓝 0) :=
    tendsto_comap
  apply tendsto_const_nhds.congr'
  filter_upwards [ht.eventually (eventually_lt_nhds hσ)] with ε hε
  have hn : (σ : 𝕜) ≠ 0 := by exact_mod_cast hσ.ne'
  simp only [cutoffValue, ite_eq_left hε.le, mul_inv_cancel₀ hn]

theorem cutoff_instance : Spec.CutoffInstance.{u,v,w} := by
  intro 𝕜 H G _ _ _ _ _ _ _ A S
  have hc ε j := cutoff_norm_le (𝕜 := 𝕜) ε (S.sigma j) (S.positive j)
  constructor
  · exact ⟨fun ε => inv_nonneg.mpr ε.property.le, hc,
      ⟨1, zero_le_one, fun ε j => cutoff_multiplier_bound ε _ (S.positive j)⟩,
      fun j => cutoff_multiplier_tendsto _ (S.positive j)⟩
  · intro ε
    have hb : BddAbove (Set.range (fun j => ‖cutoffValue (𝕜 := 𝕜) ε (S.sigma j)‖)) :=
      ⟨(ε : ℝ)⁻¹, by rintro _ ⟨j, rfl⟩; exact hc ε j⟩
    exact (canonical_bound 𝕜 H G A S _ hb).2.2 _ (inv_nonneg.mpr ε.property.le) (hc ε)

lemma tikhonov_nonneg (α : PositiveParameter) (σ : ℝ) (hσ : 0 < σ) :
    0 ≤ σ / ((α : ℝ) + σ ^ 2) := by
  have ha := α.property
  positivity

lemma tikhonov_norm_le (α : PositiveParameter) (σ : ℝ) (hσ : 0 < σ) :
    ‖tikhonovValue (𝕜 := 𝕜) α σ‖ ≤ 1 / (2 * Real.sqrt (α : ℝ)) := by
  rw [tikhonovValue, RCLike.norm_ofReal, abs_of_nonneg (tikhonov_nonneg α σ hσ)]
  have ha := α.property
  have hd : 0 < (α : ℝ) + σ ^ 2 := by positivity
  have hs : 0 < Real.sqrt (α : ℝ) := Real.sqrt_pos.mpr α.property
  apply (div_le_div_iff₀ hd (by positivity : 0 < 2 * Real.sqrt (α : ℝ))).mpr
  have hsq := Real.sq_sqrt α.property.le
  nlinarith [sq_nonneg (σ - Real.sqrt (α : ℝ))]

lemma tikhonov_multiplier_bound (α : PositiveParameter) (σ : ℝ) (hσ : 0 < σ) :
    ‖(σ : 𝕜) * tikhonovValue α σ‖ ≤ 1 := by
  have ha := α.property
  rw [tikhonovValue, ← RCLike.ofReal_mul, RCLike.norm_ofReal,
    abs_of_nonneg (mul_nonneg hσ.le (tikhonov_nonneg α σ hσ))]
  rw [← mul_div_assoc]
  apply (div_le_one (by positivity : 0 < (α : ℝ) + σ ^ 2)).mpr
  nlinarith [α.property]

lemma tikhonov_multiplier_tendsto (σ : ℝ) (hσ : 0 < σ) :
    Tendsto (fun α => (σ : 𝕜) * tikhonovValue α σ) smallParameters (𝓝 1) := by
  have ht : Tendsto (fun α : PositiveParameter => (α : ℝ)) smallParameters (𝓝 0) :=
    tendsto_comap
  have hd : Tendsto (fun α : PositiveParameter => (α : ℝ) + σ ^ 2)
      smallParameters (𝓝 (σ ^ 2)) := by simpa using ht.add_const (σ ^ 2)
  have hr := (tendsto_const_nhds (x := σ)).mul
    ((tendsto_const_nhds (x := σ)).div hd (pow_ne_zero 2 hσ.ne'))
  have hreal : Tendsto (fun α : PositiveParameter => σ * (σ / ((α : ℝ) + σ ^ 2)))
      smallParameters (𝓝 1) := by
    convert hr using 1
    field_simp [hσ.ne']
  have hcast := ((RCLike.continuous_ofReal (K := 𝕜)).tendsto 1).comp hreal
  simpa only [Function.comp_def, RCLike.ofReal_mul, RCLike.ofReal_one, tikhonovValue]
    using hcast

theorem tikhonov_instance : Spec.TikhonovInstance.{u,v,w} := by
  intro 𝕜 H G _ _ _ _ _ _ _ A S
  have hc α j := tikhonov_norm_le (𝕜 := 𝕜) α (S.sigma j) (S.positive j)
  have hC (α : PositiveParameter) : 0 ≤ 1 / (2 * Real.sqrt (α : ℝ)) := by positivity
  constructor
  · exact ⟨hC, hc,
      ⟨1, zero_le_one, fun α j => tikhonov_multiplier_bound α _ (S.positive j)⟩,
      fun j => tikhonov_multiplier_tendsto _ (S.positive j)⟩
  · intro α
    have hb : BddAbove (Set.range (fun j => ‖tikhonovValue (𝕜 := 𝕜) α (S.sigma j)‖)) :=
      ⟨1 / (2 * Real.sqrt (α : ℝ)), by rintro _ ⟨j, rfl⟩; exact hc α j⟩
    exact (canonical_bound 𝕜 H G A S _ hb).2.2 _ (hC α) (hc α)

theorem parameter_limit : Spec.ParameterLimit.{b} := by
  constructor
  · change NeBot (comap (Subtype.val : Set.Ioi (0 : ℝ) → ℝ) (𝓝 (0 : ℝ)))
    apply (mem_closure_iff_comap_neBot (x := (0 : ℝ)) (s := Set.Ioi 0)).mp
    rw [closure_Ioi]
    exact le_refl (0 : ℝ)
  · intro P p η
    exact tendsto_comap_iff

/-- In particular, the C constants can be the source's actual suprema. -/
theorem canonical_conditions : Spec.CanonicalConditions.{u,v,w,a} := by
  intro 𝕜 H G _ _ _ _ _ _ _ A S I l ψ hb hm hl
  have h η := canonical_bound 𝕜 H G A S (ψ η) (hb η)
  exact ⟨fun η => (h η).1, fun η => (h η).2.1, hm, hl⟩

end ExpandedFA.PartV.SpectralRegularization
