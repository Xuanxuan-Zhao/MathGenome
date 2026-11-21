import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch06.DiskAutomorphisms
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch06.Schwarz
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

noncomputable section
open Metric Set
namespace D12Complex.DiskAutomorphisms

abbrev phi : Specs.D12Complex.Ch06.DiskAutomorphisms.phi_type := DiskPhi
abbrev phiInv : Specs.D12Complex.Ch06.DiskAutomorphisms.phiInv_type := DiskPhiInv

private lemma norm_mul_lt_one {a z : ℂ} (ha : a ∈ ball (0 : ℂ) 1)
    (hz : z ∈ ball (0 : ℂ) 1) : ‖star a * z‖ < 1 := by
  rw [norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg z)
    (le_of_lt (mem_ball_zero_iff.mp ha))).trans_lt (mem_ball_zero_iff.mp hz)

theorem denominator_ne_zero :
    Specs.D12Complex.Ch06.DiskAutomorphisms.denominator_ne_zero_type := by
  intro a ha z hz h
  have he : star a * z = 1 := (sub_eq_zero.mp h).symm
  have hn := norm_mul_lt_one ha hz
  rw [he, norm_one] at hn
  exact (lt_irrefl 1) hn

private lemma norm_difference_identity (a z : ℂ) :
    ‖1 - star a * z‖ ^ 2 - ‖z - a‖ ^ 2 =
      (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

private lemma phi_mapsTo {a : ℂ} (ha : a ∈ ball (0 : ℂ) 1) :
    MapsTo (DiskPhi a) (ball 0 1) (ball 0 1) := by
  intro z hz
  have ha' : ‖a‖ < 1 := mem_ball_zero_iff.mp ha
  have hz' : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hapos : 0 < 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  have hzpos : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hi := norm_difference_identity a z
  have hn : ‖z - a‖ < ‖1 - star a * z‖ := by
    nlinarith [mul_pos hapos hzpos, norm_nonneg (z-a), norm_nonneg (1-star a*z)]
  rw [mem_ball_zero_iff, DiskPhi, norm_div]
  exact (div_lt_one (lt_of_le_of_lt (norm_nonneg _) hn)).mpr hn

private lemma phiInv_eq (a : ℂ) : DiskPhiInv a = DiskPhi (-a) := by
  funext z
  simp [DiskPhiInv, DiskPhi]

theorem inverse_denominator_ne_zero :
    Specs.D12Complex.Ch06.DiskAutomorphisms.inverse_denominator_ne_zero_type := by
  intro a ha w hw
  simpa using denominator_ne_zero (-a) (by simpa using ha) w hw

private lemma phi_holomorphic {a : ℂ} (ha : a ∈ ball (0 : ℂ) 1) :
    HolomorphicOn (ball 0 1) (DiskPhi a) := by
  refine ⟨isOpen_ball, fun z hz => ?_⟩
  exact (differentiableAt_id.sub_const a).div
    (differentiableAt_const 1 |>.sub (differentiableAt_id.const_mul (star a)))
    (denominator_ne_zero a ha z hz)

private lemma phiInv_mapsTo {a : ℂ} (ha : a ∈ ball (0 : ℂ) 1) :
    MapsTo (DiskPhiInv a) (ball 0 1) (ball 0 1) := by
  rw [phiInv_eq]
  exact phi_mapsTo (by simpa using ha)

private lemma inverse_phi {a z : ℂ} (ha : a ∈ ball (0 : ℂ) 1)
    (hz : z ∈ ball (0 : ℂ) 1) : DiskPhiInv a (DiskPhi a z) = z := by
  have hd := denominator_ne_zero a ha z hz
  have he := inverse_denominator_ne_zero a ha (DiskPhi a z) (phi_mapsTo ha hz)
  change (DiskPhi a z + a) / (1 + star a * DiskPhi a z) = z
  rw [div_eq_iff he]
  dsimp [DiskPhi]
  simp only [div_eq_mul_inv]
  calc
    (z - a) * (1 - star a * z)⁻¹ + a =
        z * (1 + star a * ((z - a) * (1 - star a * z)⁻¹)) +
          (a - z) * (1 - (1 - star a * z) * (1 - star a * z)⁻¹) := by simp only [Complex.star_def]; ring
    _ = _ := by rw [mul_inv_cancel₀ hd]; simp only [Complex.star_def]; ring

theorem phi_biholomorphicPair :
    Specs.D12Complex.Ch06.DiskAutomorphisms.phi_biholomorphicPair_type := by
  intro a ha
  refine ⟨phi_holomorphic ha, ?_, phi_mapsTo ha, phiInv_mapsTo ha,
    fun z hz => inverse_phi ha hz, ?_⟩
  · rw [phiInv_eq]
    exact phi_holomorphic (by simpa using ha)
  · intro w hw
    have h := inverse_phi (a := -a) (by simpa using ha) hw
    simpa only [phiInv_eq, neg_neg] using h

/-- Composition preserves the shared biholomorphic-pair predicate. -/
lemma biholomorphicPair_comp {f g F G : ℂ → ℂ}
    (h : BiholomorphicPair (ball 0 1) (ball 0 1) f g)
    (H : BiholomorphicPair (ball 0 1) (ball 0 1) F G) :
    BiholomorphicPair (ball 0 1) (ball 0 1) (F ∘ f) (g ∘ G) := by
  rcases h with ⟨hf, hg, hfm, hgm, hl, hr⟩
  rcases H with ⟨hF, hG, hFm, hGm, hL, hR⟩
  refine ⟨⟨isOpen_ball, fun z hz => (hF.2 _ (hfm hz)).comp z (hf.2 z hz)⟩,
    ⟨isOpen_ball, fun z hz => (hg.2 _ (hGm hz)).comp z (hG.2 z hz)⟩,
    hFm.comp hfm, hgm.comp hGm, ?_, ?_⟩
  · intro z hz
    simp only [Function.comp_apply, hL (hfm hz), hl hz]
  · intro z hz
    simp only [Function.comp_apply, hr (hGm hz), hR hz]

private lemma rotation_pair (c : ℂ) (hc : ‖c‖ = 1) :
    BiholomorphicPair (ball 0 1) (ball 0 1)
      (fun z => c * z) (fun z => c⁻¹ * z) := by
  have hci : ‖c⁻¹‖ = 1 := by simp [hc]
  have hne : c ≠ 0 := by intro h; simp [h] at hc
  refine ⟨(Schwarz.rotation_converse c hc).1,
    (Schwarz.rotation_converse _ hci).1,
    (Schwarz.rotation_converse c hc).2.1,
    (Schwarz.rotation_converse _ hci).2.1, ?_, ?_⟩
  · intro z _
    simp [hne]
  · intro z _
    simp [hne]

theorem rotation_phi_automorphism :
    Specs.D12Complex.Ch06.DiskAutomorphisms.rotation_phi_automorphism_type := by
  intro a ha c hc
  exact ⟨_, biholomorphicPair_comp (phi_biholomorphicPair a ha) (rotation_pair c hc)⟩

/-- Apply Schwarz to a disk automorphism and its inverse. -/
lemma rotation_of_pair_fix_zero {f g : ℂ → ℂ}
    (h : BiholomorphicPair (ball 0 1) (ball 0 1) f g) (h0 : f 0 = 0) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ EqOn f (fun z => c * z) (ball 0 1) := by
  rcases h with ⟨hf, hg, hfm, hgm, hl, hr⟩
  have hz : (0 : ℂ) ∈ ball 0 1 := mem_ball_self zero_lt_one
  have hg0 : g 0 = 0 := by simpa [h0] using hl hz
  have hn (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : ‖f z‖ = ‖z‖ := by
    apply le_antisymm (Schwarz.norm_le_norm f hf hfm h0 z hz)
    have hi := Schwarz.norm_le_norm g hg hgm hg0 (f z) (hfm hz)
    simpa only [hl hz] using hi
  have hm : (1 / 2 : ℂ) ∈ ball 0 1 := by
    norm_num [mem_ball_zero_iff, norm_div]
  exact Schwarz.rotation_of_norm_eq f hf hfm h0 _ hm (by norm_num) (hn _ hm)

theorem zero_preimage :
    Specs.D12Complex.Ch06.DiskAutomorphisms.zero_preimage_type := by
  intro f a c ha hc he z hz
  have hne : c ≠ 0 := by intro h; simp [h] at hc
  rw [he hz, mul_eq_zero, or_iff_right hne, DiskPhi, div_eq_zero_iff,
    or_iff_left (denominator_ne_zero a ha z hz), sub_eq_zero]

private lemma exists_parameters {f : ℂ → ℂ}
    (h : IsBiholomorphism (ball 0 1) (ball 0 1) f) :
    ∃ a c : ℂ, a ∈ ball (0 : ℂ) 1 ∧ ‖c‖ = 1 ∧
      EqOn f (fun z => c * DiskPhi a z) (ball 0 1) := by
  rcases h with ⟨g, hf, hg, hfm, hgm, hl, hr⟩
  have hz : (0 : ℂ) ∈ ball 0 1 := mem_ball_self zero_lt_one
  let a := g 0
  have ha : a ∈ ball (0 : ℂ) 1 := hgm hz
  have hp := phi_biholomorphicPair a ha
  have hpi : BiholomorphicPair (ball 0 1) (ball 0 1) (DiskPhiInv a) (DiskPhi a) :=
    ⟨hp.2.1, hp.1, hp.2.2.2.1, hp.2.2.1, hp.2.2.2.2.2, hp.2.2.2.2.1⟩
  have hn := biholomorphicPair_comp hpi ⟨hf, hg, hfm, hgm, hl, hr⟩
  have hn0 : (f ∘ DiskPhiInv a) 0 = 0 := by
    simpa [Function.comp_apply, DiskPhiInv, a] using hr hz
  obtain ⟨c, hc, he⟩ := rotation_of_pair_fix_zero hn hn0
  refine ⟨a, c, ha, hc, fun z hz => ?_⟩
  have hi := he (hp.2.2.1 hz)
  simpa only [Function.comp_apply, hp.2.2.2.2.1 hz] using hi

theorem classification :
    Specs.D12Complex.Ch06.DiskAutomorphisms.classification_type := by
  intro f hf
  obtain ⟨a, c, ha, hc, he⟩ := exists_parameters hf
  refine ⟨(a,c), ⟨ha, hc, he⟩, ?_⟩
  rintro ⟨b,d⟩ ⟨hb, hd, hde⟩
  have hba : b = a := by
    apply (zero_preimage f a c ha hc he b hb).mp
    exact (zero_preimage f b d hb hd hde b hb).mpr rfl
  subst b
  have hw : (1 / 2 : ℂ) ∈ ball 0 1 := by
    norm_num [mem_ball_zero_iff, norm_div]
  have hp := phi_biholomorphicPair a ha
  have hz := hp.2.2.2.1 hw
  have hv : DiskPhi a (DiskPhiInv a (1 / 2)) = 1 / 2 := hp.2.2.2.2.2 hw
  have hcd := (hde hz).symm.trans (he hz)
  dsimp only at hcd
  rw [hv] at hcd
  have : d = c := (mul_right_cancel₀ (by norm_num : (1 / 2 : ℂ) ≠ 0)) hcd
  exact Prod.ext rfl this

end D12Complex.DiskAutomorphisms
