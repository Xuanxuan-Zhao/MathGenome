import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch23.OmittedValueNormality
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch23.SchottkyPropagation
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch11.Montel
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch09.Hurwitz
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch11.ChordalMetric
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.SphereHolomorphic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
Montel–Carathéodory (paper.tex:4247–4277). Schottky propagation bounds the
center-small subfamily on each compact set. Finite Montel then applies to
that subfamily, or to the reciprocals. Hurwitz separates the nonvanishing
reciprocal limit from the identically zero limit. Reciprocal chordal
isometry proves convergence to infinity in the latter case.
-/
noncomputable section
open Set Filter
open scoped Topology
namespace D12Complex.OmittedValueNormality


/-- The omitted-value sequences whose values at one fixed center are at most one
have ordinary holomorphic compact subsequences. -/
theorem bounded_center_subsequence (Ω : Set ℂ) (a : ℂ) (hΩ : IsDomain Ω) (ha : a ∈ Ω)
    (F : ℕ → ℂ → ℂ) (hF : ∀ n, HolomorphicOn Ω (F n))
    (hzero : ∀ n, ∀ z ∈ Ω, F n z ≠ 0)
    (hone : ∀ n, ∀ z ∈ Ω, F n z ≠ 1)
    (hcenter : ∀ n, ‖F n a‖ ≤ 1) :
    ∃ (φ : ℕ → ℕ) (f : ℂ → ℂ), StrictMono φ ∧ HolomorphicOn Ω f ∧
      TendstoLocallyUniformlyOn (fun n => F (φ n)) f atTop Ω := by
  let 𝓕 : Set (ℂ → ℂ) := Set.range F
  have hhol : ∀ f ∈ 𝓕, HolomorphicOn Ω f := by
    rintro f ⟨n, rfl⟩
    exact hF n
  have hb : HolomorphicCompactness.LocallyBounded Ω 𝓕 := by
    intro K hK hKΩ
    obtain ⟨M, hM, hbM⟩ := SchottkyPropagation.compact_bound Ω a hΩ ha K hK hKΩ
    refine ⟨M, hM.le, ?_⟩
    rintro f ⟨n, rfl⟩ z hz
    exact hbM (F n) (hF n) (hzero n) (hone n) (hcenter n) z hz
  exact (Ch11.Montel.locallyBounded_iff_finiteNormal Ω 𝓕 hΩ.2.1 hhol).mp hb
    F (fun n => Set.mem_range_self n)

/-- Infinite center-smallness is sufficient, with both index selections
combined into a single strictly increasing map. -/
theorem frequently_bounded_center_subsequence (Ω : Set ℂ) (a : ℂ)
    (hΩ : IsDomain Ω) (ha : a ∈ Ω) (F : ℕ → ℂ → ℂ)
    (hF : ∀ n, HolomorphicOn Ω (F n))
    (hzero : ∀ n, ∀ z ∈ Ω, F n z ≠ 0)
    (hone : ∀ n, ∀ z ∈ Ω, F n z ≠ 1)
    (hcenter : ∃ᶠ n in atTop, ‖F n a‖ ≤ 1) :
    ∃ (φ : ℕ → ℕ) (f : ℂ → ℂ), StrictMono φ ∧ HolomorphicOn Ω f ∧
      TendstoLocallyUniformlyOn (fun n => F (φ n)) f atTop Ω := by
  obtain ⟨ψ, hψ, hcψ⟩ := extraction_of_frequently_atTop hcenter
  obtain ⟨φ, f, hφ, hf, hlim⟩ := bounded_center_subsequence Ω a hΩ ha
    (fun n => F (ψ n)) (fun n => hF (ψ n))
    (fun n => hzero (ψ n)) (fun n => hone (ψ n)) hcψ
  exact ⟨ψ ∘ φ, f, hψ.comp hφ, hf, hlim⟩

/-- Either original center values are small infinitely often, or reciprocal
center values are small infinitely often. -/
theorem center_selection (a : ℂ) (F : ℕ → ℂ → ℂ) :
    (∃ᶠ n in atTop, ‖F n a‖ ≤ 1) ∨
      ∃ᶠ n in atTop, ‖(F n a)⁻¹‖ ≤ 1 := by
  by_cases h : ∃ᶠ n in atTop, ‖F n a‖ ≤ 1
  · exact Or.inl h
  · right
    apply (not_frequently.mp h).frequently.mono
    intro n hn
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ (le_of_lt (lt_of_not_ge hn))



lemma finite_chordal_le (z w : ℂ) :
    Chordal.chordal (sphereFinite z) (sphereFinite w) ≤ ‖z - w‖ := by
  rw [Chordal.chordal_finite]
  have hz : 1 ≤ Real.sqrt (1 + ‖z‖ ^ 2) := Real.one_le_sqrt.mpr (by nlinarith [sq_nonneg ‖z‖])
  have hw : 1 ≤ Real.sqrt (1 + ‖w‖ ^ 2) := Real.one_le_sqrt.mpr (by nlinarith [sq_nonneg ‖w‖])
  exact div_le_self (norm_nonneg _) (one_le_mul_of_one_le_of_one_le hz hw)

lemma ordinary_spherical {Ω : Set ℂ} {f : ℕ → ℂ → ℂ} {h : ℂ → ℂ}
    (hlim : TendstoLocallyUniformlyOn f h atTop Ω) :
    SphericalLimits.SphericalLocallyUniformOn
      (fun n z => sphereFinite (f n z)) (fun z => sphereFinite (h z)) Ω := by
  intro K hK hKΩ ε hε
  have hu := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
    (hlim.mono hKΩ)
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu ε hε] with n hn
  intro z hz
  exact (finite_chordal_le (h z) (f n z)).trans_lt (by simpa [dist_eq_norm] using hn z hz)

lemma reciprocal_finite (z : ℂ) (hz : z ≠ 0) :
    Chordal.reciprocal (sphereFinite z) = sphereFinite z⁻¹ := by
  simp [Chordal.reciprocal, Mobius.mobiusMap, sphereFinite, Mobius.spherePair, hz]

lemma reciprocal_zero : Chordal.reciprocal (sphereFinite 0) = sphereInfty := by
  simp [Chordal.reciprocal, Mobius.mobiusMap, sphereFinite, Mobius.spherePair]

lemma chordal_infty_reciprocal (z : ℂ) (hz : z ≠ 0) :
    Chordal.chordal sphereInfty (sphereFinite z) =
      ‖z⁻¹‖ / Real.sqrt (1 + ‖z⁻¹‖ ^ 2) := by
  have he := Chordal.reciprocal_chordal (sphereFinite 0) (sphereFinite z⁻¹)
  rw [reciprocal_zero, reciprocal_finite _ (inv_ne_zero hz), inv_inv,
    Chordal.chordal_finite] at he
  simpa only [norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero,
    Real.sqrt_one, one_mul, zero_sub, norm_neg] using he

lemma reciprocal_spherical {Ω : Set ℂ} {f : ℕ → ℂ → ℂ} {h : ℂ → ℂ}
    (hf : ∀ n z, z ∈ Ω → f n z ≠ 0)
    (hh : ∀ z ∈ Ω, h z ≠ 0)
    (hlim : TendstoLocallyUniformlyOn (fun n z => (f n z)⁻¹) h atTop Ω) :
    SphericalLimits.SphericalLocallyUniformOn
      (fun n z => sphereFinite (f n z)) (fun z => sphereFinite ((h z)⁻¹)) Ω := by
  have hs := ordinary_spherical hlim
  intro K hK hKΩ ε hε
  filter_upwards [hs K hK hKΩ ε hε] with n hn
  intro z hz
  have he := Chordal.reciprocal_chordal (sphereFinite (h z)) (sphereFinite ((f n z)⁻¹))
  rw [reciprocal_finite _ (hh z (hKΩ hz)),
    reciprocal_finite _ (inv_ne_zero (hf n z (hKΩ hz))), inv_inv] at he
  exact he.trans_lt (hn z hz)

lemma reciprocal_zero_spherical {Ω : Set ℂ} {f : ℕ → ℂ → ℂ}
    (hf : ∀ n z, z ∈ Ω → f n z ≠ 0)
    (hlim : TendstoLocallyUniformlyOn (fun n z => (f n z)⁻¹) (fun _ => 0) atTop Ω) :
    SphericalLimits.SphericalLocallyUniformOn
      (fun n z => sphereFinite (f n z)) (fun _ => sphereInfty) Ω := by
  have hs := ordinary_spherical hlim
  intro K hK hKΩ ε hε
  filter_upwards [hs K hK hKΩ ε hε] with n hn
  intro z hz
  have he := Chordal.reciprocal_chordal (sphereFinite 0) (sphereFinite ((f n z)⁻¹))
  rw [reciprocal_zero,
    reciprocal_finite _ (inv_ne_zero (hf n z (hKΩ hz))), inv_inv] at he
  exact he.trans_lt (hn z hz)


/-- Inversion preserves weak holomorphy where the original function is nonzero. -/
lemma holomorphic_inverse {Ω : Set ℂ} {f : ℂ → ℂ}
    (hf : HolomorphicOn Ω f) (hzero : ∀ z ∈ Ω, f z ≠ 0) :
    HolomorphicOn Ω (fun z => (f z)⁻¹) :=
  ⟨hf.1, fun z hz => (hf.2 z hz).inv (hzero z hz)⟩

/-- Hurwitz gives the precise finite or infinite alternative for a reciprocal limit. -/
theorem reciprocal_limit_alternative :
    Specs.D12Complex.Ch23.OmittedValueNormality.reciprocal_limit_alternative_type := by
  intro Ω F h hΩ hF hzero hh hlim
  have hi (n : ℕ) : HolomorphicOn Ω (fun z => (F n z)⁻¹) :=
    holomorphic_inverse (hF n) (hzero n)
  rcases Hurwitz.zero_free_or_identically_zero Ω (fun n z => (F n z)⁻¹) h
      hΩ hi hh hlim (fun n z hz => inv_ne_zero (hzero n z hz)) with hn | hz
  · left
    refine ⟨hn, holomorphic_inverse hh hn, ?_⟩
    have hc : ContinuousOn h Ω := fun z hz =>
      (hh.2 z hz).continuousAt.continuousWithinAt
    convert hlim.inv₀ hc hn using 1
    ext n z
    simp only [Pi.inv_apply, inv_inv]
  · exact Or.inr ⟨hz, reciprocal_zero_spherical hzero (hlim.congr_right hz)⟩

/-- Every omitted-two-values sequence has a finite holomorphic or infinite
spherical compact subsequential limit, on the whole original domain. -/
theorem subsequence : Specs.D12Complex.Ch23.OmittedValueNormality.subsequence_type := by
  intro Ω F hΩ hF hzero hone
  obtain ⟨a, ha⟩ := hΩ.1
  rcases center_selection a F with hc | hc
  · obtain ⟨φ, h, hφ, hh, hlim⟩ :=
      frequently_bounded_center_subsequence Ω a hΩ ha F hF hzero hone hc
    exact ⟨φ, hφ, Or.inl ⟨h, hh, hlim, ordinary_spherical hlim⟩⟩
  · have hi (n : ℕ) : HolomorphicOn Ω (fun z => (F n z)⁻¹) :=
      holomorphic_inverse (hF n) (hzero n)
    have hi0 (n : ℕ) (z : ℂ) (hz : z ∈ Ω) : (F n z)⁻¹ ≠ 0 :=
      inv_ne_zero (hzero n z hz)
    have hi1 (n : ℕ) (z : ℂ) (hz : z ∈ Ω) : (F n z)⁻¹ ≠ 1 := by
      intro he
      apply hone n z hz
      simpa only [inv_inv, inv_one] using congrArg (fun w : ℂ => w⁻¹) he
    obtain ⟨φ, h, hφ, hh, hlim⟩ :=
      frequently_bounded_center_subsequence Ω a hΩ ha
        (fun n z => (F n z)⁻¹) hi hi0 hi1 hc
    rcases reciprocal_limit_alternative Ω (fun n => F (φ n)) h hΩ
        (fun n => hF (φ n)) (fun n => hzero (φ n)) hh hlim with hn | hz
    · exact ⟨φ, hφ, Or.inl ⟨fun z => (h z)⁻¹, hn.2.1, hn.2.2,
        ordinary_spherical hn.2.2⟩⟩
    · exact ⟨φ, hφ, Or.inr hz.2⟩


lemma scalarMeromorphic_of_eqOn_finite {Ω : Set ℂ} {f : ℂ → ℂ}
    {F : ℂ → RiemannSphere} (hf : HolomorphicOn Ω f)
    (he : EqOn F (fun z => sphereFinite (f z)) Ω) :
    ScalarMeromorphicOn Ω F := by
  have hfin : ∀ z ∈ Ω, F z ≠ sphereInfty := by
    intro z hz
    rw [he hz]
    exact OnePoint.coe_ne_infty _
  have hset : {z | z ∈ Ω ∧ F z ≠ sphereInfty} = Ω := by
    ext z
    exact ⟨fun h => h.1, fun h => ⟨h, hfin z h⟩⟩
  have hg : HolomorphicOn Ω (scalarFinitePart F) := by
    refine ⟨hf.1, fun z hz => ?_⟩
    have hez : f =ᶠ[𝓝 z] scalarFinitePart F := by
      filter_upwards [hf.1.mem_nhds hz] with w hw
      simp only [scalarFinitePart, he hw, finiteCoordinate_sphereFinite]
    exact hez.differentiableAt_iff.mp (hf.2 z hz)
  refine ⟨hf.1, ?_, ?_, ?_, ?_, ?_⟩
  · have hemp : {z : Ω | F z = sphereInfty} = ∅ := by
      ext z
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact hfin z z.property
    rw [hemp]
    exact isClosed_empty
  · have hemp : scalarPoleSet Ω F = ∅ := by
      ext z
      simp only [scalarPoleSet, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      exact hfin z
    rw [hemp]
    simp only [isDiscrete_iff_forall_mem_exists_isOpen, mem_empty_iff_false, forall_false, implies_true]
  · simpa only [hset] using hg
  · intro z hz hinf
    exact (hfin z hz hinf).elim
  · intro z hz
    exact ⟨z, mem_connectedComponentIn hz, hfin z hz⟩

lemma scalarMeromorphic_finite {Ω : Set ℂ} {f : ℂ → ℂ}
    (hf : HolomorphicOn Ω f) :
    ScalarMeromorphicOn Ω (fun z => sphereFinite (f z)) :=
  scalarMeromorphic_of_eqOn_finite hf (fun _ _ => rfl)


/-- The full omitted-value family is normal for the canonical chordal metric. -/
theorem spherically_normal :
    Specs.D12Complex.Ch23.OmittedValueNormality.spherically_normal_type := by
  classical
  intro Ω hΩ
  constructor
  · rintro G ⟨f, hf, _hzero, _hone, he⟩
    exact Or.inl (scalarMeromorphic_of_eqOn_finite hf he)
  · intro G hG
    choose f hf hzero hone he using hG
    obtain ⟨φ, hφ, hlim⟩ := subsequence Ω f hΩ hf hzero hone
    rcases hlim with ⟨h, hh, _hord, hs⟩ | hs
    · refine ⟨φ, fun z => sphereFinite (h z), hφ,
        Or.inl (scalarMeromorphic_finite hh), ?_⟩
      intro K hK hKΩ ε hε
      filter_upwards [hs K hK hKΩ ε hε] with n hn
      intro z hz
      change Chordal.chordal (sphereFinite (h z)) (G (φ n) z) < ε
      rw [he (φ n) (hKΩ hz)]
      exact hn z hz
    · refine ⟨φ, fun _ => sphereInfty, hφ, Or.inr (fun _ _ => rfl), ?_⟩
      intro K hK hKΩ ε hε
      filter_upwards [hs K hK hKΩ ε hε] with n hn
      intro z hz
      change Chordal.chordal sphereInfty (G (φ n) z) < ε
      rw [he (φ n) (hKΩ hz)]
      exact hn z hz

end D12Complex.OmittedValueNormality
