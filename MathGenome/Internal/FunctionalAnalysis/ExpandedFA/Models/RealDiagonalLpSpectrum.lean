import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Models.RealDiagonalLpSpectrum
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Models.DiagonalLpSpectrum

noncomputable section
open scoped ENNReal
namespace ExpandedFA.Models
open RealDiagonalLpSpectrumSpec

-- The canonical maps are shared with the independent specification.
def realLpEmbed : EmbedType := embedValue
def realLpRe : ReType := reValue
def realLpIm : ReType := imValue
def realLpSynthesis : SynthType := synthValue
def realDiagonalLp : RealDiagonalType := realDiagonalValue
def complexifiedRealDiagonalLp : ComplexifiedType := complexifiedValue

@[simp] lemma realLpEmbed_apply (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (x : RSequence p) (n : ℕ) : embedValue p x n = (x n : ℂ) := rfl
@[simp] lemma realLpRe_apply (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (z : CSequence p) (n : ℕ) : reValue p z n = (z n).re := rfl
@[simp] lemma realLpIm_apply (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (z : CSequence p) (n : ℕ) : imValue p z n = (z n).im := rfl
@[simp] lemma realLpSynthesis_apply (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (x y : RSequence p) (n : ℕ) :
    synthValue p (x,y) n = (x n : ℂ) + Complex.I * (y n : ℂ) := rfl

lemma realLpEmbed_norm (p : ℝ≥0∞) [Fact (1 ≤ p)] (x : RSequence p) :
    ‖embedValue p x‖ = ‖x‖ := by
  have hp : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  apply le_antisymm
  · exact lp.norm_mono hp (fun n => by simp)
  · exact lp.norm_mono hp (fun n => by simp)

lemma realLpRe_norm_le (p : ℝ≥0∞) [Fact (1 ≤ p)] (z : CSequence p) :
    ‖reValue p z‖ ≤ ‖z‖ := by
  apply lp.norm_mono (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  intro n
  exact Complex.abs_re_le_norm (z n)

lemma realLpIm_norm_le (p : ℝ≥0∞) [Fact (1 ≤ p)] (z : CSequence p) :
    ‖imValue p z‖ ≤ ‖z‖ := by
  apply lp.norm_mono (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  intro n
  exact Complex.abs_im_le_norm (z n)

@[simp] lemma realLpRe_synth (p : ℝ≥0∞) [Fact (1 ≤ p)] (x y : RSequence p) :
    reValue p (synthValue p (x,y)) = x := by
  apply lp.ext
  funext n
  simp

@[simp] lemma realLpIm_synth (p : ℝ≥0∞) [Fact (1 ≤ p)] (x y : RSequence p) :
    imValue p (synthValue p (x,y)) = y := by
  apply lp.ext
  funext n
  simp

@[simp] lemma realLp_synth_parts (p : ℝ≥0∞) [Fact (1 ≤ p)] (z : CSequence p) :
    synthValue p (reValue p z, imValue p z) = z := by
  apply lp.ext
  funext n
  simp only [realLpSynthesis_apply, realLpRe_apply, realLpIm_apply]
  simpa only [mul_comm] using Complex.re_add_im (z n)

/-- This uses the existing complex norm on ℓᵖ; the product has its usual maximum norm. -/
def realLpPartsEquiv (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    CSequence p ≃L[ℝ] RSequence p × RSequence p where
  toFun z := (reValue p z, imValue p z)
  invFun w := synthValue p w
  left_inv z := realLp_synth_parts p z
  right_inv w := by rcases w with ⟨x,y⟩; simp
  map_add' z w := by simp only [map_add, Prod.mk_add_mk]
  map_smul' c z := by simp only [map_smul, Prod.smul_mk, RingHom.id_apply]
  continuous_toFun := (reValue p).continuous.prodMk (imValue p).continuous
  continuous_invFun := (synthValue p).continuous

theorem realLp_coordinates : Coordinates := by
  intro p hp
  exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩

theorem realLp_embedding_isometric : EmbeddingIsometric := by
  intro p hp
  exact AddMonoidHomClass.isometry_of_norm (embedValue p) (realLpEmbed_norm p)

theorem realLp_part_bounds : PartBounds := by
  intro p hp z
  exact ⟨realLpRe_norm_le p z, realLpIm_norm_le p z⟩

theorem realLp_synthesis_bounds : SynthesisBounds := by
  intro p hp x y
  constructor
  · apply max_le
    · simpa using realLpRe_norm_le p (synthValue p (x,y))
    · simpa using realLpIm_norm_le p (synthValue p (x,y))
  · change ‖embedValue p x + Complex.I • embedValue p y‖ ≤ ‖x‖ + ‖y‖
    calc
      _ ≤ ‖embedValue p x‖ + ‖Complex.I • embedValue p y‖ := norm_add_le _ _
      _ = ‖x‖ + ‖y‖ := by simp [norm_smul, realLpEmbed_norm]

theorem realLp_complexification : Complexification := by
  intro p hp
  refine ⟨realLpPartsEquiv p, fun _ => rfl, fun _ => rfl,
    realLp_synth_parts p, ?_, ?_⟩
  · intro x y
    simp
  · intro c z
    apply Prod.ext
    · apply lp.ext
      funext n
      change (c * z n).re = c.re * (z n).re - c.im * (z n).im
      exact Complex.mul_re c (z n)
    · apply lp.ext
      funext n
      change (c * z n).im = c.im * (z n).re + c.re * (z n).im
      rw [Complex.mul_im, add_comm]

theorem realLp_complex_complete : ComplexComplete := by
  intro p hp s hs
  exact cauchySeq_tendsto_of_complete hs

theorem realDiagonalLp_laws : RealDiagonalLaws := by
  intro p hp a
  have hb : ‖realDiagonalValue p a‖ ≤ ‖a‖ :=
    ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (realDiagonalLinear_bound p a)
  refine ⟨fun _ _ => rfl, hb, ?_⟩
  simpa only [lp.norm_eq_ciSup, Real.norm_eq_abs] using hb

lemma complexifiedRealDiagonalLp_embed (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : RSequence ∞)
    (x : RSequence p) : complexifiedValue p a (embedValue p x) =
    embedValue p (realDiagonalValue p a x) := by
  apply lp.ext
  funext n
  change (a n : ℂ) * (x n : ℂ) = ((a n * x n : ℝ) : ℂ)
  exact (Complex.ofReal_mul _ _).symm

lemma complexifiedRealDiagonalLp_synth (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : RSequence ∞)
    (x y : RSequence p) : complexifiedValue p a (synthValue p (x,y)) =
    synthValue p (realDiagonalValue p a x, realDiagonalValue p a y) := by
  change complexifiedValue p a (embedValue p x + Complex.I • embedValue p y) = _
  rw [map_add, map_smul, complexifiedRealDiagonalLp_embed, complexifiedRealDiagonalLp_embed]
  rfl

/-- Re/Im decomposition, rather than finite-support density, gives uniqueness even at infinity. -/
theorem realDiagonalLp_extension : ExtensionLaws := by
  intro p hp a
  refine ⟨complexifiedRealDiagonalLp_embed p a, complexifiedRealDiagonalLp_synth p a, ?_⟩
  intro T hT
  apply LinearMap.ext
  intro z
  rw [← realLp_synth_parts p z]
  change T (embedValue p (reValue p z) + Complex.I • embedValue p (imValue p z)) = _
  rw [map_add, map_smul, hT, hT]
  exact (complexifiedRealDiagonalLp_synth p a _ _).symm

theorem complexifiedRealDiagonalLp_spectrum : ComplexSpectrumLaw := by
  intro p hp a
  exact diagonalLp_spectrum p (embedValue ∞ a)

/-- The real reciprocal sequence is bounded whenever the parameter avoids
its real closure. This is the same uniform separation for every p. -/
lemma realDiagonal_reciprocal_mem (a : RSequence ∞) {r : ℝ}
    (hr : r ∉ closure (Set.range fun n => a n)) :
    Memℓp (fun n => (r - a n)⁻¹) ∞ := by
  rw [Metric.mem_closure_range_iff] at hr
  push Not at hr
  obtain ⟨ε, hε, hn⟩ := hr
  apply memℓp_infty
  refine ⟨ε⁻¹, ?_⟩
  rintro _ ⟨n, rfl⟩
  have hb : ‖r - a n‖⁻¹ ≤ ε⁻¹ :=
    inv_anti₀ hε (by simpa only [dist_eq_norm] using hn n)
  simpa only [norm_inv] using hb

/-- The inverse is an actual bounded real operator, verified on both sides. -/
lemma realDiagonal_isUnit_of_not_mem_closure (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (a : RSequence ∞) {r : ℝ} (hr : r ∉ closure (Set.range fun n => a n)) :
    IsUnit (algebraMap ℝ (RSequence p →L[ℝ] RSequence p) r - realDiagonalValue p a) := by
  let b : RSequence ∞ := ⟨fun n => (r - a n)⁻¹, realDiagonal_reciprocal_mem a hr⟩
  have hn : ∀ n, r - a n ≠ 0 := by
    intro n
    apply sub_ne_zero.mpr
    intro he
    exact hr (subset_closure ⟨n, he.symm⟩)
  refine ⟨{
    val := algebraMap ℝ (RSequence p →L[ℝ] RSequence p) r - realDiagonalValue p a
    inv := realDiagonalValue p b
    val_inv := ?_
    inv_val := ?_ }, rfl⟩
  · apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext n
    change r * ((r - a n)⁻¹ * x n) - a n * ((r - a n)⁻¹ * x n) = x n
    rw [← sub_mul, ← mul_assoc, mul_inv_cancel₀ (hn n), one_mul]
  · apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext n
    change (r - a n)⁻¹ * (r * x n - a n * x n) = x n
    rw [← sub_mul, ← mul_assoc, inv_mul_cancel₀ (hn n), one_mul]

/-- Unit coordinate vectors obstruct invertibility at every diagonal entry.
No density claim is involved, including when p is infinity. -/
lemma realDiagonal_entry_mem_spectrum (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (a : RSequence ∞) (n : ℕ) : a n ∈ spectrum ℝ (realDiagonalValue p a) := by
  apply spectrum.mem_iff.mpr
  rintro ⟨u, hu⟩
  let e : RSequence p := lp.single p n 1
  have he : (algebraMap ℝ (RSequence p →L[ℝ] RSequence p) (a n) -
      realDiagonalValue p a) e = 0 := by
    apply lp.ext
    funext k
    change a n * e k - a k * e k = 0
    by_cases hk : k = n
    · subst k; exact sub_self _
    · have hek : e k = 0 := lp.single_apply_ne p n 1 hk
      rw [hek]
      simp
  have he' : (u : RSequence p →L[ℝ] RSequence p) e =
      (u : RSequence p →L[ℝ] RSequence p) 0 := by
    rw [hu, map_zero]
    exact he
  have he0 : e = 0 := (ContinuousLinearEquiv.ofUnit u).injective he'
  have h := congrArg (fun x : RSequence p => x n) he0
  simp [e] at h

theorem realDiagonalLp_spectrum : RealSpectrumLaw := by
  intro p hp a
  apply Set.Subset.antisymm
  · intro r hr
    by_contra hc
    exact (spectrum.mem_iff.mp hr) (realDiagonal_isUnit_of_not_mem_closure p a hc)
  · apply closure_minimal
    · rintro r ⟨n, rfl⟩
      exact realDiagonal_entry_mem_spectrum p a n
    · exact spectrum.isClosed (realDiagonalValue p a)

theorem realDiagonalLp_resolvent : RealResolventLaw := by
  intro p hp a r
  rw [← realDiagonalLp_spectrum p a, spectrum.mem_iff, not_not]

theorem boundedRealSequence_diagonalLp_spectrum : BoundedRealSequenceLaw := by
  intro p hp a ha
  exact ⟨complexifiedRealDiagonalLp_spectrum p _, realDiagonalLp_spectrum p _⟩

end ExpandedFA.Models
