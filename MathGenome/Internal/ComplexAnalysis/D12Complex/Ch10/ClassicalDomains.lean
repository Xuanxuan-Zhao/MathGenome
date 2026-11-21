import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch10.ClassicalDomains
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch10.ElementaryMaps
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch10.Joukowski
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
open Set
namespace D12Complex.ClassicalDomains

/-- Composition retains both on-set inverse laws and weak holomorphy. -/
theorem biholomorphicPair_comp {U V W : Set ℂ} {f g h k : ℂ → ℂ}
    (hf : BiholomorphicPair U V f g) (hh : BiholomorphicPair V W h k) :
    BiholomorphicPair U W (h ∘ f) (g ∘ k) := by
  rcases hf with ⟨hf, hg, hfm, hgm, hgl, hgr⟩
  rcases hh with ⟨hh, hk, hhm, hkm, hkl, hkr⟩
  refine ⟨⟨hf.1, fun z hz => (hh.2 _ (hfm hz)).comp z (hf.2 z hz)⟩,
    ⟨hk.1, fun w hw => (hg.2 _ (hkm hw)).comp w (hk.2 w hw)⟩,
    hhm.comp hfm, hgm.comp hkm, ?_, ?_⟩
  · intro z hz
    simp only [Function.comp_apply, hkl (hfm hz), hgl hz]
  · intro w hw
    simp only [Function.comp_apply, hgr (hkm hw), hkr hw]

theorem biholomorphicPair_symm {U V : Set ℂ} {f g : ℂ → ℂ}
    (h : BiholomorphicPair U V f g) : BiholomorphicPair V U g f :=
  ⟨h.2.1, h.1, h.2.2.2.1, h.2.2.1, h.2.2.2.2.2, h.2.2.2.2.1⟩

/-- Every nonsingular complex affine change, on an arbitrary open set. -/
theorem affine_preimage_pair (V : Set ℂ) (hV : IsOpen V) (a d : ℂ) (hd : d ≠ 0) :
    BiholomorphicPair ((fun z => (z - a) / d) ⁻¹' V) V
      (fun z => (z - a) / d) (fun w => a + d * w) := by
  have hl (z : ℂ) : a + d * ((z - a) / d) = z := by field_simp; ring
  have hr (w : ℂ) : (a + d * w - a) / d = w := by field_simp; ring
  refine ⟨⟨hV.preimage (by fun_prop), fun _ _ => differentiableAt_id.sub_const a |>.div_const d⟩,
    ⟨hV, fun _ _ => differentiableAt_id.const_mul d |>.const_add a⟩,
    fun _ hz => hz, ?_, fun z _ => hl z, fun w _ => hr w⟩
  intro w hw
  change (a + d * w - a) / d ∈ V
  rwa [hr]

theorem disk_biholomorphicPair :
    Specs.D12Complex.Ch10.ClassicalDomains.disk_biholomorphicPair_type := by
  intro a r hr
  have h := affine_preimage_pair unitDisk (isOpen_lt continuous_norm continuous_const)
    a (r : ℂ) (Complex.ofReal_ne_zero.mpr hr.ne')
  have he : (fun z : ℂ => (z - a) / (r : ℂ)) ⁻¹' unitDisk = Metric.ball a r := by
    ext z
    simp only [mem_preimage, unitDisk, mem_ofPred_eq, Metric.mem_ball, dist_eq_norm,
      norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    exact div_lt_one hr
  rwa [he] at h

theorem halfPlane_biholomorphicPair :
    Specs.D12Complex.Ch10.ClassicalDomains.halfPlane_biholomorphicPair_type := by
  intro a d hd
  exact biholomorphicPair_comp
    (affine_preimage_pair upperHalfPlane (isOpen_lt continuous_const Complex.continuous_im) a d hd)
    ElementaryMaps.cayley_biholomorphicPair

/-- Affine normalization of any finite positive strip width. -/
theorem strip_normalization (a θ : ℝ) (hθ : 0 < θ) :
    BiholomorphicPair (horizontalStrip a θ) (horizontalStrip 0 Real.pi)
      (fun z => ((Real.pi / θ : ℝ) : ℂ) * (z - (a : ℂ) * Complex.I))
      (fun w => (a : ℂ) * Complex.I + ((θ / Real.pi : ℝ) : ℂ) * w) := by
  refine ⟨⟨ElementaryMaps.isOpen_horizontalStrip a θ, fun _ _ =>
    (differentiableAt_id.sub_const _).const_mul _⟩,
    ⟨ElementaryMaps.isOpen_horizontalStrip 0 Real.pi, fun _ _ =>
      differentiableAt_id.const_mul _ |>.const_add _⟩,
    fun _ hz => ElementaryMaps.scale_strip a θ hθ hz,
    fun _ hz => ElementaryMaps.unscale_strip a θ hθ hz,
    fun z _ => ElementaryMaps.unscale_scale a θ hθ.ne' z,
    fun w _ => ElementaryMaps.scale_unscale a θ hθ.ne' w⟩

theorem strip_biholomorphicPair :
    Specs.D12Complex.Ch10.ClassicalDomains.strip_biholomorphicPair_type := by
  intro a θ hθ
  have he := ElementaryMaps.exponential_biholomorphicPair 0 Real.pi Real.pi_pos
    (by linarith [Real.pi_pos])
  rw [ElementaryMaps.sector_zero_pi] at he
  exact biholomorphicPair_comp (biholomorphicPair_comp (strip_normalization a θ hθ) he)
    ElementaryMaps.cayley_biholomorphicPair

theorem sector_biholomorphicPair :
    Specs.D12Complex.Ch10.ClassicalDomains.sector_biholomorphicPair_type := by
  intro v a θ hpos hθ
  have ha := affine_preimage_pair (sector a θ) (ElementaryMaps.isOpen_sector a θ) v 1 one_ne_zero
  simp only [div_one, one_mul] at ha
  exact biholomorphicPair_comp
    (biholomorphicPair_comp ha (ElementaryMaps.sectorPower_biholomorphicPair a θ hpos hθ))
    ElementaryMaps.cayley_biholomorphicPair

/-- The normalization removes exactly the prescribed ray, including its endpoint. -/
theorem raySlit_eq_preimage (v d : ℂ) (hd : d ≠ 0) :
    ((fun t : ℝ => v + (t : ℂ) * d) '' Ici 0)ᶜ =
      (fun z => (z - v) / (-d)) ⁻¹' PrincipalSlitPlane := by
  ext z
  change (¬∃ t : ℝ, 0 ≤ t ∧ v + (t : ℂ) * d = z) ↔
    ¬∃ s : ℝ, s ≤ 0 ∧ (s : ℂ) = (z - v) / (-d)
  apply not_congr
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨-t, neg_nonpos.mpr ht, ?_⟩
    push_cast
    field_simp
    ring
  · rintro ⟨s, hs, he⟩
    refine ⟨-s, neg_nonneg.mpr hs, ?_⟩
    have he' := (eq_div_iff (neg_ne_zero.mpr hd)).mp he
    push_cast
    linear_combination he'

theorem raySlit_biholomorphicPair :
    Specs.D12Complex.Ch10.ClassicalDomains.raySlit_biholomorphicPair_type := by
  intro v d hd
  have ha := affine_preimage_pair PrincipalSlitPlane
    PrincipalLogarithm.isOpen_principalSlitPlane v (-d) (neg_ne_zero.mpr hd)
  rw [← raySlit_eq_preimage v d hd] at ha
  have he : PrincipalStrip = horizontalStrip (-Real.pi) (2 * Real.pi) := by
    ext z
    simp only [PrincipalStrip, horizontalStrip, mem_ofPred_eq, abs_lt]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have hl := PrincipalLogarithm.principalLog_biholomorphicPair
  change BiholomorphicPair PrincipalSlitPlane PrincipalStrip PrincipalLog E at hl
  rw [he] at hl
  exact biholomorphicPair_comp (biholomorphicPair_comp ha hl)
    (strip_biholomorphicPair (-Real.pi) (2 * Real.pi) (by linarith [Real.pi_pos]))

/-- Affine coordinates of a closed segment, with both endpoint inequalities weak. -/
theorem segment_mem_iff (p q z : ℂ) :
    z ∈ segment ℝ p q ↔ ∃ t : ℝ, -1 ≤ t ∧ t ≤ 1 ∧
      (p + q) / 2 + ((q - p) / 2) * (t : ℂ) = z := by
  rw [segment_eq_image ℝ p q]
  constructor
  · rintro ⟨s, ⟨hs0, hs1⟩, rfl⟩
    refine ⟨2 * s - 1, by linarith, by linarith, ?_⟩
    simp only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_mul,
      Complex.ofReal_ofNat, Complex.ofReal_one]
    ring
  · rintro ⟨t, ht0, ht1, rfl⟩
    refine ⟨(t + 1) / 2, ⟨by linarith, by linarith⟩, ?_⟩
    simp only [Complex.real_smul]
    push_cast
    ring

theorem segmentComplement_eq_preimage (p q : ℂ) (hpq : p ≠ q) :
    (segment ℝ p q)ᶜ =
      (fun w => (w - (p + q) / 2) / ((q - p) / 2)) ⁻¹' Joukowski.slitPlane := by
  have hd : (q - p) / 2 ≠ 0 := div_ne_zero (sub_ne_zero.mpr hpq.symm) (by norm_num)
  ext z
  change (z ∉ segment ℝ p q) ↔ ¬(_ = 0 ∧ -1 ≤ _ ∧ _ ≤ 1)
  apply not_congr
  rw [segment_mem_iff]
  let w := (z - (p + q) / 2) / ((q - p) / 2)
  change (∃ t : ℝ, -1 ≤ t ∧ t ≤ 1 ∧ (p + q) / 2 + ((q - p) / 2) * (t : ℂ) = z) ↔
    w.im = 0 ∧ -1 ≤ w.re ∧ w.re ≤ 1
  constructor
  · rintro ⟨t, ht0, ht1, he⟩
    have hw : w = (t : ℂ) := by
      dsimp [w]
      rw [← he]
      field_simp
      ring
    simpa [hw] using And.intro ht0 ht1
  · rintro ⟨hi, hr0, hr1⟩
    refine ⟨w.re, hr0, hr1, ?_⟩
    have hw : (w.re : ℂ) = w := by
      apply Complex.ext <;> simp [hi]
    rw [hw]
    dsimp [w]
    field_simp
    ring

theorem exterior_segment_biholomorphicPair :
    Specs.D12Complex.Ch10.ClassicalDomains.exterior_segment_biholomorphicPair_type := by
  intro a r p q hr hpq
  have he := affine_preimage_pair Joukowski.exterior Joukowski.isOpen_exterior
    a (r : ℂ) (Complex.ofReal_ne_zero.mpr hr.ne')
  have hsource : (fun z : ℂ => (z - a) / (r : ℂ)) ⁻¹' Joukowski.exterior =
      {z | r < ‖z - a‖} := by
    ext z
    simp only [mem_preimage, Joukowski.exterior, mem_ofPred_eq, norm_div,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    exact one_lt_div hr
  rw [hsource] at he
  have ht := biholomorphicPair_symm (affine_preimage_pair Joukowski.slitPlane
    Joukowski.isOpen_slitPlane ((p + q) / 2) ((q - p) / 2)
    (div_ne_zero (sub_ne_zero.mpr hpq.symm) (by norm_num)))
  rw [← segmentComplement_eq_preimage p q hpq] at ht
  have hc := biholomorphicPair_comp he Joukowski.biholomorphic_pair
  have hf := biholomorphicPair_comp hc ht
  exact hf

end D12Complex.ClassicalDomains
