import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch06.SchwarzPick
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch06.DiskAutomorphisms
import Mathlib.Tactic.FieldSimp
import Batteries.Tactic.OpenPrivate

noncomputable section
open Metric Set
open scoped Topology
namespace D12Complex.SchwarzPick

private lemma gap_pos {a : ℂ} (ha : a ∈ ball (0 : ℂ) 1) :
    0 < 1 - ‖a‖ ^ 2 := by
  have := mem_ball_zero_iff.mp ha
  nlinarith [norm_nonneg a]

private lemma phi_at_center (a : ℂ) : DiskPhi a a = 0 := by
  simp [DiskPhi]

private lemma inv_at_zero (a : ℂ) : DiskPhiInv a 0 = a := by
  simp [DiskPhiInv]

private lemma phi_hasDerivAt_center {a : ℂ} (ha : a ∈ ball (0 : ℂ) 1) :
    HasDerivAt (DiskPhi a) (1 / (1 - star a * a)) a := by
  have hd := ((hasDerivAt_id a).sub_const a).div
    ((hasDerivAt_const a (1 : ℂ)).sub ((hasDerivAt_id a).const_mul (star a)))
    (DiskAutomorphisms.denominator_ne_zero a ha a ha)
  convert hd using 1
  · rfl
  · dsimp
    have hn := DiskAutomorphisms.denominator_ne_zero a ha a ha
    simp only [Complex.star_def] at hn ⊢
    field_simp [hn]
    ring

private lemma inv_hasDerivAt_zero (a : ℂ) :
    HasDerivAt (DiskPhiInv a) (1 - star a * a) 0 := by
  have hd := ((hasDerivAt_id (0 : ℂ)).add_const a).div
    ((hasDerivAt_const (0 : ℂ) (1 : ℂ)).add
      ((hasDerivAt_id (0 : ℂ)).const_mul (star a))) (by simp)
  convert hd using 1
  · rfl
  · simp [mul_comm]

private lemma norm_gap {a : ℂ} (ha : a ∈ ball (0 : ℂ) 1) :
    ‖1 - star a * a‖ = 1 - ‖a‖ ^ 2 := by
  rw [Complex.star_def, Complex.conj_mul']
  have h : (1 : ℂ) - (‖a‖ : ℂ) ^ 2 = ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) := by norm_cast
  rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (gap_pos ha)]

/-- Move the source point and its image to zero. -/
private def normalized (f : ℂ → ℂ) (a : ℂ) : ℂ → ℂ :=
  DiskPhi (f a) ∘ f ∘ DiskPhiInv a

private lemma normalized_data {f : ℂ → ℂ}
    (hf : HolomorphicOn (ball 0 1) f) (hm : MapsTo f (ball 0 1) (ball 0 1))
    {a : ℂ} (ha : a ∈ ball (0 : ℂ) 1) :
    HolomorphicOn (ball 0 1) (normalized f a) ∧
    MapsTo (normalized f a) (ball 0 1) (ball 0 1) ∧ normalized f a 0 = 0 := by
  have hp := DiskAutomorphisms.phi_biholomorphicPair a ha
  have hq := DiskAutomorphisms.phi_biholomorphicPair (f a) (hm ha)
  refine ⟨⟨isOpen_ball, fun w hw => ?_⟩, ?_, ?_⟩
  · exact (hq.1.2 _ (hm (hp.2.2.2.1 hw))).comp w
      ((hf.2 _ (hp.2.2.2.1 hw)).comp w (hp.2.1.2 w hw))
  · exact hq.2.2.1.comp (hm.comp hp.2.2.2.1)
  · simp [normalized, inv_at_zero, phi_at_center]

private lemma normalized_at_phi {f : ℂ → ℂ} {a z : ℂ}
    (ha : a ∈ ball (0 : ℂ) 1) (hz : z ∈ ball (0 : ℂ) 1) :
    normalized f a (DiskPhi a z) = DiskPhi (f a) (f z) := by
  simp only [normalized, Function.comp_apply,
    (DiskAutomorphisms.phi_biholomorphicPair a ha).2.2.2.2.1 hz]

private lemma normalized_deriv_norm {f : ℂ → ℂ}
    (hf : HolomorphicOn (ball 0 1) f) (hm : MapsTo f (ball 0 1) (ball 0 1))
    {a : ℂ} (ha : a ∈ ball (0 : ℂ) 1) :
    ‖deriv (normalized f a) 0‖ =
      ‖deriv f a‖ / (1 - ‖f a‖ ^ 2) * (1 - ‖a‖ ^ 2) := by
  have h₁ := inv_hasDerivAt_zero a
  have hfd : HasDerivAt f (deriv f a) (DiskPhiInv a 0) := by
    simpa only [inv_at_zero] using (hf.2 a ha).hasDerivAt
  have h₂ := hfd.comp 0 h₁
  have hpd : HasDerivAt (DiskPhi (f a)) (1 / (1 - star (f a) * f a))
      ((f ∘ DiskPhiInv a) 0) := by
    simpa only [Function.comp_apply, inv_at_zero] using phi_hasDerivAt_center (hm ha)
  have h₃ := hpd.comp 0 h₂
  change HasDerivAt (normalized f a) _ 0 at h₃
  rw [h₃.deriv, norm_mul, norm_mul, norm_div, norm_one, norm_gap ha, norm_gap (hm ha)]
  ring

theorem value_le : Specs.D12Complex.Ch06.SchwarzPick.value_le_type := by
  intro f hf hm a ha z hz
  have hn := normalized_data hf hm ha
  have hp := DiskAutomorphisms.phi_biholomorphicPair a ha
  have h := Schwarz.norm_le_norm (normalized f a) hn.1 hn.2.1 hn.2.2
    (DiskPhi a z) (hp.2.2.1 hz)
  rw [normalized_at_phi ha hz] at h
  exact h

theorem derivative_le : Specs.D12Complex.Ch06.SchwarzPick.derivative_le_type := by
  intro f hf hm a ha
  have hn := normalized_data hf hm ha
  have h := Schwarz.norm_deriv_zero_le_one (normalized f a) hn.1 hn.2.1 hn.2.2
  rw [normalized_deriv_norm hf hm ha] at h
  exact (le_div_iff₀ (gap_pos ha)).mpr (by simpa [mul_comm] using h)

private lemma pair_symm {f g : ℂ → ℂ}
    (h : BiholomorphicPair (ball 0 1) (ball 0 1) f g) :
    BiholomorphicPair (ball 0 1) (ball 0 1) g f :=
  ⟨h.2.1, h.1, h.2.2.2.1, h.2.2.1, h.2.2.2.2.2, h.2.2.2.2.1⟩

/-- Total representatives may differ away from the disk. -/
private lemma pair_congr_left {f F g : ℂ → ℂ}
    (h : BiholomorphicPair (ball 0 1) (ball 0 1) F g)
    (hf : HolomorphicOn (ball 0 1) f) (hm : MapsTo f (ball 0 1) (ball 0 1))
    (he : EqOn f F (ball 0 1)) :
    BiholomorphicPair (ball 0 1) (ball 0 1) f g := by
  refine ⟨hf, h.2.1, hm, h.2.2.2.1, ?_, ?_⟩
  · intro z hz
    rw [he hz]
    exact h.2.2.2.2.1 hz
  · intro z hz
    rw [he (h.2.2.2.1 hz)]
    exact h.2.2.2.2.2 hz

private lemma unnormalize_automorphism {f : ℂ → ℂ}
    (hf : HolomorphicOn (ball 0 1) f) (hm : MapsTo f (ball 0 1) (ball 0 1))
    {a : ℂ} (ha : a ∈ ball (0 : ℂ) 1)
    (hn : IsBiholomorphism (ball 0 1) (ball 0 1) (normalized f a)) :
    IsBiholomorphism (ball 0 1) (ball 0 1) f := by
  obtain ⟨g, hg⟩ := hn
  have hp := DiskAutomorphisms.phi_biholomorphicPair a ha
  have hq := DiskAutomorphisms.phi_biholomorphicPair (f a) (hm ha)
  have H := DiskAutomorphisms.biholomorphicPair_comp
    (DiskAutomorphisms.biholomorphicPair_comp hp hg) (pair_symm hq)
  refine ⟨_, pair_congr_left H hf hm (fun z hz => ?_)⟩
  simp only [Function.comp_apply, normalized_at_phi ha hz,
    hq.2.2.2.2.1 (hm hz)]

open private rotation_pair from MathGenome.Internal.ComplexAnalysis.D12Complex.Ch06.DiskAutomorphisms

private lemma automorphism_of_normalized_rotation {f : ℂ → ℂ}
    (hf : HolomorphicOn (ball 0 1) f) (hm : MapsTo f (ball 0 1) (ball 0 1))
    {a : ℂ} (ha : a ∈ ball (0 : ℂ) 1)
    (hr : ∃ c : ℂ, ‖c‖ = 1 ∧ EqOn (normalized f a) (fun w => c * w) (ball 0 1)) :
    IsBiholomorphism (ball 0 1) (ball 0 1) f := by
  obtain ⟨c, hc, he⟩ := hr
  have hn := normalized_data hf hm ha
  exact unnormalize_automorphism hf hm ha
    ⟨_, pair_congr_left (rotation_pair c hc) hn.1 hn.2.1 he⟩

private lemma normalized_rotation_of_automorphism {f : ℂ → ℂ}
    (H : IsBiholomorphism (ball 0 1) (ball 0 1) f)
    {a : ℂ} (ha : a ∈ ball (0 : ℂ) 1) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ EqOn (normalized f a) (fun w => c * w) (ball 0 1) := by
  obtain ⟨g, hg⟩ := H
  have hp := DiskAutomorphisms.phi_biholomorphicPair a ha
  have hq := DiskAutomorphisms.phi_biholomorphicPair (f a) (hg.2.2.1 ha)
  have hn := DiskAutomorphisms.biholomorphicPair_comp
    (DiskAutomorphisms.biholomorphicPair_comp (pair_symm hp) hg) hq
  exact DiskAutomorphisms.rotation_of_pair_fix_zero hn
    (normalized_data hg.1 hg.2.2.1 ha).2.2

theorem automorphism_equalities :
    Specs.D12Complex.Ch06.SchwarzPick.automorphism_equalities_type := by
  intro f H a ha
  obtain ⟨c, hc, he⟩ := normalized_rotation_of_automorphism H ha
  obtain ⟨g, hg⟩ := H
  have hf := hg.1
  have hm := hg.2.2.1
  have hp := DiskAutomorphisms.phi_biholomorphicPair a ha
  refine ⟨fun z hz => ?_, ?_⟩
  · have h := he (hp.2.2.1 hz)
    rw [normalized_at_phi ha hz] at h
    change ‖DiskPhi (f a) (f z)‖ = ‖DiskPhi a z‖
    rw [h, norm_mul, hc, one_mul]
  · have hs : ∀ᶠ w : ℂ in 𝓝 0, w ∈ ball (0 : ℂ) 1 :=
      isOpen_ball.mem_nhds (mem_ball_self zero_lt_one)
    have hev : normalized f a =ᶠ[𝓝 0] (fun w : ℂ => c * w) :=
      hs.mono (fun w hw => he hw)
    have hd : ‖deriv (normalized f a) 0‖ = 1 := by
      rw [hev.deriv_eq]
      exact (Schwarz.rotation_converse c hc).2.2.2.2
    rw [normalized_deriv_norm hf hm ha] at hd
    exact (eq_div_iff (ne_of_gt (gap_pos ha))).mpr hd

theorem value_eq_iff : Specs.D12Complex.Ch06.SchwarzPick.value_eq_iff_type := by
  intro f hf hm a ha z hz hne
  constructor
  · intro heq
    have hn := normalized_data hf hm ha
    have hp := DiskAutomorphisms.phi_biholomorphicPair a ha
    have hphine : DiskPhi a z ≠ 0 := by
      intro he
      have h := hp.2.2.2.2.1 hz
      rw [he, inv_at_zero] at h
      exact hne h.symm
    apply automorphism_of_normalized_rotation hf hm ha
    apply Schwarz.rotation_of_norm_eq (normalized f a) hn.1 hn.2.1 hn.2.2
      (DiskPhi a z) (hp.2.2.1 hz) hphine
    rw [normalized_at_phi ha hz]
    exact heq
  · intro H
    exact (automorphism_equalities f H a ha).1 z hz

theorem derivative_eq_iff :
    Specs.D12Complex.Ch06.SchwarzPick.derivative_eq_iff_type := by
  intro f hf hm a ha
  constructor
  · intro heq
    have hn := normalized_data hf hm ha
    have hd : ‖deriv (normalized f a) 0‖ = 1 := by
      rw [normalized_deriv_norm hf hm ha, heq]
      exact one_div_mul_cancel (ne_of_gt (gap_pos ha))
    exact automorphism_of_normalized_rotation hf hm ha
      (Schwarz.rotation_of_norm_deriv_eq_one (normalized f a) hn.1 hn.2.1 hn.2.2 hd)
  · intro H
    exact (automorphism_equalities f H a ha).2

theorem equality_cases : Specs.D12Complex.Ch06.SchwarzPick.equality_cases_type := by
  intro f hf hm
  have h0 : (0 : ℂ) ∈ ball 0 1 := mem_ball_self zero_lt_one
  have hh : (1 / 2 : ℂ) ∈ ball 0 1 := by
    norm_num [mem_ball_zero_iff, norm_div]
  constructor
  · constructor
    · rintro ⟨a, ha, z, hz, hza, heq⟩
      exact (value_eq_iff f hf hm a ha z hz hza).mp heq
    · intro H
      exact ⟨0, h0, 1 / 2, hh, by norm_num,
        (automorphism_equalities f H 0 h0).1 (1 / 2) hh⟩
  · constructor
    · rintro ⟨a, ha, heq⟩
      exact (derivative_eq_iff f hf hm a ha).mp heq
    · intro H
      exact ⟨0, h0, (automorphism_equalities f H 0 h0).2⟩

end D12Complex.SchwarzPick
