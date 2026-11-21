import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch05.LocalMappingNormalForm
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch05.LocalZeroFactorization
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch02.LocalLogarithmsRoots
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch05.LocalHolomorphicInverse
import Mathlib.RingTheory.RootsOfUnity.Complex

noncomputable section
open Filter Set
open scoped Topology

namespace D12Complex.LocalMappingNormalForm

/-- The logarithm constructs a root directly, without algebraic closure. -/
theorem complex_power_surjective :
    Specs.D12Complex.Ch05.LocalMappingNormalForm.complex_power_surjective_type := by
  intro m hm w
  by_cases hw : w = 0
  · exact ⟨0, by simp [hw, hm.ne']⟩
  · refine ⟨Complex.exp (Complex.log w / (m : ℂ)), ?_⟩
    rw [← Complex.exp_nat_mul, mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hm.ne'),
      Complex.exp_log hw]

/-- Primitive roots come from the exponential kernel; the polynomial root
bound and the m explicit roots give equality, rather than invoking FTA. -/
theorem complex_power_roots :
    Specs.D12Complex.Ch05.LocalMappingNormalForm.complex_power_roots_type := by
  intro m hm w hw
  classical
  obtain ⟨α, hα⟩ := complex_power_surjective m hm w
  have hζ := Complex.isPrimitiveRoot_exp m hm.ne'
  have hcard : (Polynomial.nthRoots m w).toFinset.card = m := by
    rw [Multiset.toFinset_card_of_nodup (hζ.nthRoots_nodup hw),
      hζ.card_nthRoots, ite_eq_left ⟨α, hα⟩]
  have hset : {z : ℂ | z ^ m = w} =
      (Polynomial.nthRoots m w).toFinset := by
    ext z
    simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_nthRoots hm,
      Set.mem_ofPred_eq]
  rw [hset]
  exact ⟨Finset.finite_toSet _, by simpa using hcard⟩

/-- Restrict both sides of a biholomorphism to an open subset of its target. -/
lemma restrict_biholomorphic_target {P V W : Set ℂ} {φ ψ : ℂ → ℂ}
    (h : BiholomorphicPair P V φ ψ) (hW : IsOpen W) (hWV : W ⊆ V) :
    BiholomorphicPair (P ∩ φ ⁻¹' W) W φ ψ := by
  rcases h with ⟨hφ, hψ, hφmap, hψmap, hl, hr⟩
  have hc : ContinuousOn φ P := fun z hz => (hφ.2 z hz).continuousAt.continuousWithinAt
  refine ⟨⟨hc.isOpen_inter_preimage hφ.1 hW, fun z hz => hφ.2 z hz.1⟩,
    ⟨hW, fun w hw => hψ.2 w (hWV hw)⟩, fun z hz => hz.2, ?_,
    fun z hz => hl hz.1, fun w hw => hr (hWV hw)⟩
  intro w hw
  exact ⟨hψmap (hWV hw), by simpa only [mem_preimage, hr (hWV hw)] using hw⟩

/-- Factorization, a local root of the unit, and the inverse theorem construct
an actual power coordinate on a neighborhood with a round target. -/
lemma exists_power_coordinate (Ω : Set ℂ) (f : ℂ → ℂ) (a : ℂ)
    (hf : HolomorphicOn Ω f) (ha : a ∈ Ω)
    (hnc : ¬ (∀ᶠ z in 𝓝 a, f z = f a)) :
    ∃ (m : ℕ), 0 < m ∧ ∃ (r : ℝ), 0 < r ∧
    ∃ (U : Set ℂ) (φ ψ : ℂ → ℂ), a ∈ U ∧ U ⊆ Ω ∧
      BiholomorphicPair U (Metric.ball 0 r) φ ψ ∧ φ a = 0 ∧
      (∀ z ∈ U, f z - f a = (φ z) ^ m) ∧
      analyticOrderAt (fun z => f z - f a) a = (m : ℕ∞) := by
  let F := fun z => f z - f a
  have hF : LocalZeroFactorization.HolomorphicNear F a :=
    ⟨Ω, ha, hf.1, fun z hz => (hf.2 z hz).sub_const (f a)⟩
  have hF0 : ¬ LocalZeroFactorization.ZeroGerm F a := by
    intro h
    apply hnc
    filter_upwards [h] with z hz
    exact sub_eq_zero.mp hz
  obtain h | ⟨_, m, hm, _⟩ := LocalZeroFactorization.local_zero_factorization F a hF
  · exact False.elim (hF0 h.1)
  have hmpos : 0 < m :=
    (LocalZeroFactorization.finiteOrder_zero_iff F a m hm).mp (sub_self _)
  have hmorder := (LocalZeroFactorization.order_eq_nat_iff F a hF m).mpr hm
  obtain ⟨g, ⟨G, haG, hg⟩, hg0, heq⟩ := hm
  obtain ⟨c, hc⟩ := complex_power_surjective m hmpos (g a)
  obtain ⟨R, h, haR, _, hh, _, hroot⟩ :=
    LocalLogarithmsRoots.local_root G g a m c hg haG hg0 hmpos hc
  have hha0 : h a ≠ 0 := by
    intro hzero
    apply hg0
    rw [← hroot a haR, hzero, zero_pow hmpos.ne']
  obtain ⟨W, hW, hoW, haW⟩ := eventually_nhds_iff.mp heq
  let N := Ω ∩ (R ∩ W)
  let φ := fun z => (z - a) * h z
  have haN : a ∈ N := ⟨ha, haR, haW⟩
  have hφ : HolomorphicOn N φ :=
    ⟨hf.1.inter (hh.1.inter hoW), fun z hz =>
      (differentiableAt_id.sub_const a).mul (hh.2 z hz.2.1)⟩
  have hφ0 : φ a = 0 := by simp [φ]
  have hdφ : HasDerivAt φ (h a) a := by
    convert ((hasDerivAt_id a).sub_const a).mul (hh.2 a haR).hasDerivAt using 1 <;> simp [φ]; rfl
  have hnormal : ∀ z ∈ N, f z - f a = (φ z) ^ m := by
    intro z hz
    rw [show f z - f a = (z - a) ^ m * g z from hW z hz.2.2]
    simp only [φ, mul_pow, hroot z hz.2.1]
  obtain ⟨P, V, ψ, haP, hφaV, hPN, hpair, _, _⟩ :=
    LocalHolomorphicInverse.local_holomorphic_inverse N φ a hφ haN
      (by rw [hdφ.deriv]; exact hha0)
  have h0V : (0 : ℂ) ∈ V := hφ0 ▸ hφaV
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hpair.2.1.1 0 h0V
  have hballV : Metric.ball (0 : ℂ) r ⊆ V := hball
  let U := P ∩ φ ⁻¹' Metric.ball 0 r
  have hU : BiholomorphicPair U (Metric.ball 0 r) φ ψ :=
    restrict_biholomorphic_target hpair Metric.isOpen_ball hballV
  refine ⟨m, hmpos, r, hr, U, φ, ψ, ?_, ?_, hU, hφ0, ?_, hmorder⟩
  · exact ⟨haP, by simpa only [mem_preimage, hφ0] using Metric.mem_ball_self hr⟩
  · exact fun z hz => (hPN hz.1).1
  · exact fun z hz => hnormal z (hPN hz.1)

/-- The norm of a power controls precisely which round disk contains its roots. -/
lemma root_mem_ball {m : ℕ} {r : ℝ} {w z : ℂ}
    (hr : 0 < r) (hw : ‖w‖ < r ^ m) (hz : z ^ m = w) :
    z ∈ Metric.ball (0 : ℂ) r := by
  rw [Metric.mem_ball, dist_zero_right]
  apply lt_of_pow_lt_pow_left₀ m hr.le
  rwa [← norm_pow, hz]

/-- All the geometric and counting conclusions use the same power coordinate. -/
theorem local_mapping_normal_form :
    Specs.D12Complex.Ch05.LocalMappingNormalForm.local_mapping_normal_form_type := by
  intro Ω f a hf ha hnc
  obtain ⟨m, hm, r, hr, U, φ, ψ, haU, hUΩ, hpair, hφ0, hform, horder⟩ :=
    exists_power_coordinate Ω f a hf ha hnc
  obtain ⟨hφbij, _⟩ := biholomorphicPair_bijOn U (Metric.ball 0 r) φ ψ hpair
  have hφmap := hpair.2.2.1
  have hψmap := hpair.2.2.2.1
  have hleft := hpair.2.2.2.2.1
  have hright := hpair.2.2.2.2.2
  have himage : f '' U = Metric.ball (f a) (r ^ m) := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [Metric.mem_ball, dist_eq_norm, hform z hz, norm_pow]
      exact pow_lt_pow_left₀ (by simpa using hφmap hz) (norm_nonneg _) hm.ne'
    · intro hw
      have hw' : ‖w - f a‖ < r ^ m := by simpa [dist_eq_norm] using hw
      obtain ⟨ζ, hζ⟩ := complex_power_surjective m hm (w - f a)
      have hζball := root_mem_ball hr hw' hζ
      refine ⟨ψ ζ, hψmap hζball, ?_⟩
      have heq := hform (ψ ζ) (hψmap hζball)
      rw [hright hζball, hζ] at heq
      exact sub_left_injective heq
  have hcount : ∀ w ∈ Metric.ball (f a) (r ^ m), w ≠ f a →
      Set.Finite {z : ℂ | z ∈ U ∧ f z = w} ∧
        Set.ncard {z : ℂ | z ∈ U ∧ f z = w} = m := by
    intro w hw hw0
    have hw' : ‖w - f a‖ < r ^ m := by simpa [dist_eq_norm] using hw
    have hrootball : ∀ ζ : ℂ, ζ ^ m = w - f a → ζ ∈ Metric.ball (0 : ℂ) r :=
      fun ζ hζ => root_mem_ball hr hw' hζ
    have hb : Set.BijOn φ {z : ℂ | z ∈ U ∧ f z = w}
        {ζ : ℂ | ζ ^ m = w - f a} := by
      refine ⟨?_, ?_, ?_⟩
      · intro z hz
        change (φ z) ^ m = w - f a
        rw [← hform z hz.1, hz.2]
      · intro z hz z' hz' heq
        exact hφbij.2.1 hz.1 hz'.1 heq
      · intro ζ hζ
        have hζball := hrootball ζ hζ
        refine ⟨ψ ζ, ⟨hψmap hζball, ?_⟩, hright hζball⟩
        have heq := hform (ψ ζ) (hψmap hζball)
        rw [hright hζball, hζ] at heq
        exact sub_left_injective heq
    obtain ⟨hfin, hcard⟩ := complex_power_roots m hm (w - f a) (sub_ne_zero.mpr hw0)
    exact ⟨hb.finite_iff_finite.mpr hfin, hb.ncard_eq.trans hcard⟩
  have hcenter : ∀ z ∈ U, f z = f a ↔ z = a := by
    intro z hz
    constructor
    · intro h
      have hpow : (φ z) ^ m = 0 := by rw [← hform z hz, h, sub_self]
      have heq : φ z = φ a := (pow_eq_zero_iff hm.ne').mp hpow |>.trans hφ0.symm
      exact hφbij.2.1 hz haU heq
    · rintro rfl
      rfl
  exact ⟨m, hm, r, hr, U, φ, ψ, haU, hUΩ, hpair, hφ0, hform,
    himage, hcount, hcenter, horder⟩

end D12Complex.LocalMappingNormalForm
