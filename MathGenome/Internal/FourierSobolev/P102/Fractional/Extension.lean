import MathGenome.Internal.FourierSobolev.Specs.P102.Fractional.Extension
import MathGenome.Internal.FourierSobolev.P102.Fractional.Localization
import MathGenome.Internal.FourierSobolev.P102.Sobolev.LipschitzGeometry
import Mathlib.Analysis.Calculus.ContDiff.RCLike

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace P102.Fractional
namespace Extension

variable {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
variable {G H : Set (Domain d)} {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Finite energy of the underlying representative of a graph element. -/
theorem energy_lt_top (hpt : p ≠ ∞) (u : Space 𝕜 G s p) :
    energy G s p (firstProjection u) < ∞ :=
  (firstProjection_range hpt (firstProjection u)).mp ⟨u, rfl⟩

/-- The seminorm stays finite on the canonical graph space. -/
theorem seminorm_lt_top (hpt : p ≠ ∞) (u : Space 𝕜 G s p) :
    seminorm G s p (firstProjection u) < ∞ :=
  (firstProjection_range_seminorm hpt (firstProjection u)).mp ⟨u, rfl⟩

omit [Fact (1 ≤ p)] in
/-- Restriction decreases the exact Gagliardo seminorm. -/
theorem seminorm_mono_domain (hGH : G ⊆ H) (u : Domain d → 𝕜) :
    seminorm G s p u ≤ seminorm H s p u := by
  exact ENNReal.rpow_le_rpow (energy_mono_domain hGH u) (by positivity)

/-- Restriction between any nested sets is a contraction on the manuscript's
sum-norm spaces. The statement records the representative, not just existence
of an abstract map between Banach spaces. -/
theorem restriction (hpt : p ≠ ∞) (hGH : G ⊆ H) :
    ∃ R : Space 𝕜 H s p →L[𝕜] Space 𝕜 G s p,
      ∀ u, (firstProjection (R u) : Domain d → 𝕜) =ᵐ[domainMeasure G]
        firstProjection u ∧ ‖R u‖ ≤ ‖u‖ := by
  have hm : domainMeasure G ≤ domainMeasure H := Measure.restrict_mono hGH le_rfl
  obtain ⟨R, hR⟩ := exists_continuousLinearMap_of_representatives hpt
    (LinearMap.id : (Domain d → 𝕜) →ₗ[𝕜] (Domain d → 𝕜))
    (fun _ _ h => h.filter_mono (Measure.absolutelyContinuous_of_le hm).ae_le)
    (fun u => (Lp.memLp (firstProjection u)).mono_measure hm)
    (fun u => (energy_mono_domain hGH _).trans_lt (energy_lt_top hpt u))
    1 (by
      intro u
      change (eLpNorm (firstProjection u) p (domainMeasure G)).toReal +
        (seminorm G s p (firstProjection u)).toReal ≤ 1 * ‖u‖
      rw [one_mul, space_norm hpt]
      apply add_le_add
      · exact ENNReal.toReal_mono (Lp.memLp (firstProjection u)).ne
          (eLpNorm_mono_measure _ hm)
      · exact ENNReal.toReal_mono (seminorm_lt_top hpt u).ne
          (seminorm_mono_domain hGH _))
  exact ⟨R, fun u => by simpa only [one_mul, LinearMap.id_apply] using hR u⟩

/-- Lift an operation that is linear almost everywhere to an actual bounded
linear map. The input is already an element of the canonical graph space;
this form permits a zero extension after a localized continuous linear map. -/
theorem exists_map_of_ae_linear {e : ℕ} {J : Set (Domain e)}
    (F : Space 𝕜 G s p → Domain e → 𝕜)
    (hadd : ∀ u v, F (u + v) =ᵐ[domainMeasure J] F u + F v)
    (hsmul : ∀ (c : 𝕜) u, F (c • u) =ᵐ[domainMeasure J] c • F u)
    (C : ℝ)
    (hex : ∀ u, ∃ v : Space 𝕜 J s p,
      (firstProjection v : Domain e → 𝕜) =ᵐ[domainMeasure J] F u ∧
        ‖v‖ ≤ C * ‖u‖) :
    ∃ T : Space 𝕜 G s p →L[𝕜] Space 𝕜 J s p,
      ∀ u, (firstProjection (T u) : Domain e → 𝕜) =ᵐ[domainMeasure J] F u ∧
        ‖T u‖ ≤ C * ‖u‖ := by
  classical
  choose f hf hb using hex
  have hfadd : ∀ u v, f (u + v) = f u + f v := by
    intro u v
    apply firstProjection_injective
    apply Lp.ext
    filter_upwards [hf (u + v), hadd u v, hf u, hf v,
      Lp.coeFn_add (firstProjection (f u)) (firstProjection (f v))]
      with x hsum hadd hu hv hcoe
    change firstProjection (f (u + v)) x =
      (firstProjection (f u) + firstProjection (f v)) x
    simp only [hcoe, hsum, hadd, Pi.add_apply, hu, hv]
  have hfsmul : ∀ (c : 𝕜) u, f (c • u) = c • f u := by
    intro c u
    apply firstProjection_injective
    apply Lp.ext
    filter_upwards [hf (c • u), hsmul c u, hf u,
      Lp.coeFn_smul c (firstProjection (f u))] with x hsum hsmul hu hcoe
    change firstProjection (f (c • u)) x = (c • firstProjection (f u)) x
    simp only [hcoe, hsum, hsmul, Pi.smul_apply, hu]
  let B : Space 𝕜 G s p →ₗ[𝕜] Space 𝕜 J s p :=
    { toFun := f, map_add' := hfadd, map_smul' := hfsmul }
  exact ⟨B.mkContinuous C hb, fun u => ⟨hf u, hb u⟩⟩

/-- The upstream zero extension is a bounded *linear* operation after any
bounded linear map whose outputs uniformly avoid the artificial edge.
Its upstream pointwise existence witnesses suffice because graph elements
are uniquely determined by their underlying a.e. classes. -/
theorem zero_extension_after {e : ℕ} {J : Set (Domain e)}
    (hd : 1 ≤ d) (hs : 0 < s) (hs1 : s < 1) (hpt : p ≠ ∞)
    (hGo : IsOpen G) (hHo : IsOpen H) (hGH : G ⊆ H)
    (δ : ℝ) (hδ : 0 < δ)
    (A : Space 𝕜 J s p →L[𝕜] Space 𝕜 G s p)
    (haway : ∀ u, SupportedAway G H δ (firstProjection (A u))) :
    ∃ T : Space 𝕜 J s p →L[𝕜] Space 𝕜 H s p,
      ∀ u, (firstProjection (T u) : Domain d → 𝕜) =ᵐ[domainMeasure H]
        zeroExtend G (firstProjection (A u)) := by
  obtain ⟨C, hC⟩ := zero_extension_away d hd s hs hs1 p hpt
  have hv := (hC (𝕜 := 𝕜) G H hGo hHo hGH δ hδ).2
  let B : ℝ := 2 + (C : ℝ) * δ ^ (-s * p.toReal)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  obtain ⟨T, hT⟩ := exists_map_of_ae_linear
    (fun u => zeroExtend G (firstProjection (A u)))
    (fun u v => by
      have ha : (firstProjection (A (u + v)) : Domain d → 𝕜) =ᵐ[domainMeasure G]
          (firstProjection (A u) : Domain d → 𝕜) + firstProjection (A v) := by
        simpa only [map_add] using
          Lp.coeFn_add (firstProjection (A u)) (firstProjection (A v))
      have hz := zeroExtend_congr (H := H) hGo.measurableSet ha
      filter_upwards [hz] with x hx
      rw [hx]
      by_cases hxG : x ∈ G <;> simp [zeroExtend, hxG])
    (fun c u => by
      have ha : (firstProjection (A (c • u)) : Domain d → 𝕜) =ᵐ[domainMeasure G]
          c • (firstProjection (A u) : Domain d → 𝕜) := by
        simpa only [map_smul] using Lp.coeFn_smul c (firstProjection (A u))
      have hz := zeroExtend_congr (H := H) hGo.measurableSet ha
      filter_upwards [hz] with x hx
      rw [hx]
      by_cases hxG : x ∈ G <;> simp [zeroExtend, hxG])
    (B * ‖A‖) (fun u => by
      obtain ⟨v, hv, hb⟩ := hv (A u) (haway u)
      refine ⟨v, hv, hb.trans ?_⟩
      change B * ‖A u‖ ≤ (B * ‖A‖) * ‖u‖
      calc
        B * ‖A u‖ ≤ B * (‖A‖ * ‖u‖) :=
          mul_le_mul_of_nonneg_left (A.le_opNorm u) hB
        _ = _ := (mul_assoc _ _ _).symm)
  exact ⟨T, fun u => (hT u).1⟩

/-- Finite sums of graph elements have the expected sum of representatives. -/
theorem firstProjection_sum_ae {ι : Type*} (t : Finset ι)
    (u : ι → Space 𝕜 G s p) :
    (firstProjection (∑ i ∈ t, u i) : Domain d → 𝕜) =ᵐ[domainMeasure G]
      ∑ i ∈ t, (firstProjection (u i) : Domain d → 𝕜) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using Lp.coeFn_zero 𝕜 p (domainMeasure G)
  | @insert i t hi ih =>
    simp only [Finset.sum_insert hi, map_add]
    exact (Lp.coeFn_add _ _).trans (Filter.EventuallyEq.add ae_eq_rfl ih)

/-- Assemble finitely many localized bounded linear operators. The partition
identity is required only on G. The resulting support is one compact union,
fixed before choosing the input, and the estimate is for the full sum norm. -/
theorem finite_assembly {ι : Type*} [Fintype ι]
    (hpt : p ≠ ∞) (hGo : IsOpen G)
    (χ : ι → Domain d → 𝕜) (hχ : ∀ x ∈ G, ∑ i, χ i x = 1)
    (E : ι → Space 𝕜 G s p →L[𝕜] Space 𝕜 Set.univ s p)
    (hres : ∀ i u, (firstProjection (E i u) : Domain d → 𝕜)
      =ᵐ[domainMeasure G] fun x => χ i x * firstProjection u x)
    (K : ι → Set (Domain d)) (hK : ∀ i, IsCompact (K i))
    (hsupp : ∀ i u, ∀ᵐ x ∂volume, x ∉ K i → firstProjection (E i u) x = 0) :
    ∃ (K' : Set (Domain d)), IsCompact K' ∧
    ∃ (C : ℝ≥0) (T : Space 𝕜 G s p →L[𝕜] Space 𝕜 Set.univ s p),
      (∀ u, (firstProjection (T u) : Domain d → 𝕜) =ᵐ[domainMeasure G]
        firstProjection u) ∧
      (∀ u, ∀ᵐ x ∂volume, x ∉ K' → firstProjection (T u) x = 0) ∧
      (∀ u, ‖T u‖ ≤ (C : ℝ) *
        (‖firstProjection u‖ + (seminorm G s p (firstProjection u)).toReal)) := by
  classical
  let T := ∑ i, E i
  have hsum (u : Space 𝕜 G s p) :
      (firstProjection (T u) : Domain d → 𝕜) =ᵐ[volume]
        ∑ i, (firstProjection (E i u) : Domain d → 𝕜) := by
    simpa only [T, sum_apply, domainMeasure, Measure.restrict_univ]
      using firstProjection_sum_ae Finset.univ (fun i => E i u)
  refine ⟨⋃ i, K i, isCompact_iUnion hK, ‖T‖₊, T, ?_, ?_, ?_⟩
  · intro u
    have hr := ae_all_iff.mpr (fun i => hres i u)
    filter_upwards [ae_restrict_of_ae (hsum u), hr,
      ae_restrict_mem hGo.measurableSet] with x hx hr hxG
    rw [hx, Finset.sum_apply]
    change (∑ i, firstProjection (E i u) x) = firstProjection u x
    simp_rw [hr]
    rw [← Finset.sum_mul, hχ x hxG, one_mul]
  · intro u
    have hs := ae_all_iff.mpr (fun i => hsupp i u)
    filter_upwards [hsum u, hs] with x hx hs hxK
    rw [hx, Finset.sum_apply]
    change (∑ i, firstProjection (E i u) x) = 0
    exact Finset.sum_eq_zero (fun i _ => hs i (fun hi => hxK (Set.mem_iUnion.mpr ⟨i, hi⟩)))
  · intro u
    simpa only [coe_nnnorm, ← space_norm hpt] using T.le_opNorm u

/-- Compact support inside an open set supplies the uniform positive separation
needed for extension across its complement. Empty supports are allowed. -/
theorem compact_support_separated (hGo : IsOpen G)
    {φ : Domain d → 𝕜} (hφ : HasCompactSupport φ) (hφG : tsupport φ ⊆ G) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ tsupport φ, ∀ y ∉ G, δ ≤ dist x y := by
  obtain ⟨δ, hδ, hthick⟩ := hφ.exists_cthickening_subset_open hGo hφG
  refine ⟨δ, hδ, fun x hx y hy => ?_⟩
  by_contra! hdist
  apply hy
  apply hthick
  exact Metric.mem_cthickening_of_dist_le y x δ _ hx (by simpa [dist_comm] using hdist.le)

/-- A compactly supported smooth interior piece has a bounded linear zero
extension, retaining its compact support and its cutoff representative on G.
This proves the interior part of the source's finite localization construction. -/
theorem interior_piece (hd : 1 ≤ d) (hs : 0 < s) (hs1 : s < 1) (hpt : p ≠ ∞)
    (hGo : IsOpen G) (φ : Domain d → 𝕜)
    (hφsmooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) φ) (hφcompact : HasCompactSupport φ)
    (hφG : tsupport φ ⊆ G) :
    ∃ T : Space 𝕜 G s p →L[𝕜] Space 𝕜 Set.univ s p,
      (∀ u, (firstProjection (T u) : Domain d → 𝕜) =ᵐ[domainMeasure G]
        fun x => φ x * firstProjection u x) ∧
      (∀ u, ∀ᵐ x ∂volume, x ∉ tsupport φ → firstProjection (T u) x = 0) := by
  obtain ⟨L, hL⟩ := hφsmooth.lipschitzWith_of_hasCompactSupport hφcompact (by simp)
  obtain ⟨M, hM⟩ := hφcompact.exists_bound_of_continuous hφsmooth.continuous
  let M' : ℝ≥0 := ⟨max M 0, le_max_right _ _⟩
  obtain ⟨C, hC⟩ := bounded_lipschitz_multiplier d hd s hs hs1 p hpt M' L
  obtain ⟨A, hA⟩ := (hC G hGo φ hL.lipschitzOnWith
    (fun x _ => (hM x).trans (le_max_left _ _))).2
  obtain ⟨δ, hδ, hsep⟩ := compact_support_separated hGo hφcompact hφG
  have haway : ∀ u, SupportedAway G Set.univ δ (firstProjection (A u)) := by
    intro u
    filter_upwards [(hA u).1] with x hx hnonzero y hy
    have hφx : φ x ≠ 0 := by
      intro hz
      apply hnonzero
      simp [hx, hz]
    exact hsep x (subset_tsupport φ hφx) y hy.2
  obtain ⟨T, hT⟩ := zero_extension_after hd hs hs1 hpt hGo isOpen_univ
    (Set.subset_univ G) δ hδ A haway
  have hz (u : Space 𝕜 G s p) :
      (firstProjection (T u) : Domain d → 𝕜) =ᵐ[volume]
        zeroExtend G (fun x => φ x * firstProjection u x) := by
    have hzero := zeroExtend_congr (H := Set.univ) hGo.measurableSet (hA u).1
    simpa only [domainMeasure, Measure.restrict_univ] using (hT u).trans hzero
  refine ⟨T, ?_, ?_⟩
  · intro u
    filter_upwards [ae_restrict_of_ae (hz u), ae_restrict_mem hGo.measurableSet]
      with x hx hxG
    simpa only [zeroExtend, Set.indicator_of_mem hxG] using hx
  · intro u
    filter_upwards [hz u] with x hx hxφ
    rw [hx]
    by_cases hxG : x ∈ G <;>
      simp [zeroExtend, hxG, image_eq_zero_of_notMem_tsupport hxφ]

/-- The empty open set needs no chart or reflection. Its zero operator is an
extension and has empty support; the full norm bound has constant zero. -/
theorem empty_extension (d : ℕ) (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ∃ (K : Set (Domain d)), IsCompact K ∧
    ∃ (C : ℝ≥0) (T : Space 𝕜 (∅ : Set (Domain d)) s p →L[𝕜]
      Space 𝕜 Set.univ s p),
      (∀ u, (firstProjection (T u) : Domain d → 𝕜) =ᵐ[domainMeasure ∅]
        firstProjection u) ∧
      (∀ u, ∀ᵐ x ∂volume, x ∉ K → firstProjection (T u) x = 0) ∧
      (∀ u, ‖T u‖ ≤ (C : ℝ) *
        (‖firstProjection u‖ + (seminorm ∅ s p (firstProjection u)).toReal)) := by
  refine ⟨∅, isCompact_empty, 0, 0, ?_, ?_, ?_⟩
  · intro u
    simp only [domainMeasure, Measure.restrict_empty, ae_zero]
    exact Filter.eventually_bot
  · intro u
    have hzero := Lp.coeFn_zero 𝕜 p (domainMeasure (Set.univ : Set (Domain d)))
    have hz : ∀ᵐ x ∂volume,
        (0 : Lp 𝕜 p (domainMeasure (Set.univ : Set (Domain d)))) x = 0 := by
      simpa only [Filter.EventuallyEq, domainMeasure, Measure.restrict_univ, Pi.zero_apply] using hzero
    filter_upwards [hz] with x hx _
    exact hx
  · intro u
    simp

/-- Transfer the smooth cutoffs of the geometric partition into the canonical
coordinate and scalar models. Only support containment is needed after casting
from real to real or complex scalars. -/
theorem cutoff_in_coordinates (n : ℕ)
    (χ : P102.U4.GraphPieces.Ambient n → ℝ)
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) χ) (hc : HasCompactSupport χ) :
    ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => (χ ((geometryCoordinates n).symm x) : 𝕜)) ∧
    HasCompactSupport (fun x => (χ ((geometryCoordinates n).symm x) : 𝕜)) ∧
    tsupport (fun x => (χ ((geometryCoordinates n).symm x) : 𝕜)) ⊆
      geometryCoordinates n '' tsupport χ := by
  have hreal := hχ.comp (geometryCoordinates n).symm.contDiff
  refine ⟨(RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).contDiff.comp hreal, ?_, ?_⟩
  · exact (hc.comp_homeomorph (geometryCoordinates n).symm.toHomeomorph).comp_left
      (show (0 : ℝ) = (0 : 𝕜) from RCLike.ofReal_zero)
  · intro x hx
    have hx' : x ∈ tsupport (χ ∘ (geometryCoordinates n).symm) :=
      tsupport_comp_subset (g := fun t : ℝ => (t : 𝕜)) (by simp) _ hx
    change x ∈ tsupport (χ ∘ (geometryCoordinates n).symm.toHomeomorph) at hx'
    rw [tsupport_comp_eq_preimage χ (geometryCoordinates n).symm.toHomeomorph] at hx'
    exact ⟨(geometryCoordinates n).symm x, hx', (geometryCoordinates n).apply_symm_apply x⟩

/-- Even reflection sends an essential support S into the union of S and
its reflected image. The explicitly assigned value on the flat face is zero. -/
theorem evenExtend_support {n : ℕ} {u : Domain (n + 1) → 𝕜}
    (S : Set (Domain (n + 1)))
    (hu : ∀ᵐ x ∂domainMeasure (upperHalfSpace n), x ∉ S → u x = 0) :
    ∀ᵐ x ∂volume, x ∉ S ∪ flatReflection '' S → evenExtend u x = 0 := by
  classical
  have heq : u =ᵐ[domainMeasure (upperHalfSpace n)] S.indicator u := by
    filter_upwards [hu] with x hx
    by_cases hxS : x ∈ S
    · simp [hxS]
    · simp [hxS, hx hxS]
  have he := evenExtend_congr heq
  have he' : evenExtend u =ᵐ[volume] evenExtend (S.indicator u) := by
    simpa only [domainMeasure, Measure.restrict_univ] using he
  filter_upwards [he'] with x hx hxS
  rw [hx]
  have hnS : x ∉ S := fun h => hxS (Or.inl h)
  have hrS : flatReflection x ∉ S := by
    intro h
    apply hxS
    exact Or.inr ⟨flatReflection x, h, flatReflection_involutive x⟩
  by_cases hzero : x 0 = 0
  · simp [evenExtend, hzero]
  by_cases hpos : 0 < x 0 <;> simp [evenExtend, hzero, hpos, hnS, hrS]

/-- Local flat patch construction: zero extension across separated artificial
edges followed by even reflection. All maps are on the canonical graph spaces.
The support bound is uniform over the input, and no trace at height zero is used. -/
theorem flat_patch_extension {n e : ℕ} {J : Set (Domain e)}
    {G : Set (Domain (n + 1))}
    (hs : 0 < s) (hs1 : s < 1) (hpt : p ≠ ∞)
    (hGo : IsOpen G) (hGH : G ⊆ upperHalfSpace n)
    (δ : ℝ) (hδ : 0 < δ)
    (A : Space 𝕜 J s p →L[𝕜] Space 𝕜 G s p)
    (haway : ∀ u, SupportedAway G (upperHalfSpace n) δ (firstProjection (A u)))
    (S : Set (Domain (n + 1))) (_hS : IsCompact S)
    (hsupp : ∀ u, ∀ᵐ x ∂domainMeasure G, x ∉ S → firstProjection (A u) x = 0) :
    ∃ T : Space 𝕜 J s p →L[𝕜] Space 𝕜 Set.univ s p,
      (∀ u, (firstProjection (T u) : Domain (n + 1) → 𝕜) =ᵐ[domainMeasure G]
        firstProjection (A u)) ∧
      (∀ u, ∀ᵐ x ∂volume, x ∉ S ∪ flatReflection '' S → firstProjection (T u) x = 0) := by
  have hH : IsOpen (upperHalfSpace n) :=
    isOpen_lt continuous_const (PiLp.continuous_apply 2 (fun _ : Fin (n + 1) => ℝ) 0)
  obtain ⟨Z, hZ⟩ := zero_extension_after (by omega : 1 ≤ n + 1)
    hs hs1 hpt hGo hH hGH δ hδ A haway
  obtain ⟨R, hR⟩ := (even_reflection n s hs hs1 p hpt (𝕜 := 𝕜)).2.2
  let T := R.comp Z
  have hT (u : Space 𝕜 J s p) :
      (firstProjection (T u) : Domain (n + 1) → 𝕜) =ᵐ[volume]
        evenExtend (firstProjection (Z u)) := by
    simpa only [T, ContinuousLinearMap.comp_apply, domainMeasure, Measure.restrict_univ]
      using (hR (Z u)).1
  have hZsupport (u : Space 𝕜 J s p) :
      ∀ᵐ x ∂domainMeasure (upperHalfSpace n), x ∉ S → firstProjection (Z u) x = 0 := by
    have hsu := (ae_restrict_iff' hGo.measurableSet).mp (hsupp u)
    filter_upwards [hZ u, ae_restrict_of_ae hsu] with x hx hsu hxS
    rw [hx]
    by_cases hxG : x ∈ G
    · simp [zeroExtend, hxG, hsu hxG hxS]
    · simp [zeroExtend, hxG]
  refine ⟨T, ?_, ?_⟩
  · intro u
    have hzG := (hZ u).filter_mono (ae_mono (Measure.restrict_mono hGH le_rfl))
    filter_upwards [ae_restrict_of_ae (hT u), hzG,
      ae_restrict_mem hGo.measurableSet] with x hx hz hxG
    have hxH : 0 < x 0 := hGH hxG
    rw [hx]
    simp only [evenExtend, ne_of_gt hxH, ↓reduceIte, hxH, hz, zeroExtend,
      Set.indicator_of_mem hxG]
  · intro u
    filter_upwards [hT u, evenExtend_support S (hZsupport u)] with x hx hs hxK
    exact hx.trans (hs hxK)

/-- Pull a null exceptional set through a global bi-Lipschitz coordinate map.
The assertion is restricted to the inverse image of the original open set. -/
theorem coordinate_ae {K' : ℝ≥0} (F : Domain d ≃ₜ Domain d)
    (hF' : LipschitzWith K' F.symm) (hGo : IsOpen G)
    {P : Domain d → Prop} (hP : ∀ᵐ x ∂domainMeasure G, P x) :
    ∀ᵐ x ∂domainMeasure (F ⁻¹' G), P (F x) := by
  let f : (F ⁻¹' G) ≃ₜ G := F.subtype (fun _ => Iff.rfl)
  have hf' : LipschitzWith K' f.symm := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact hF'.dist_le_mul x y
  have hh := (Pullback.coordinate_quasiMeasurePreserving
    (hGo.preimage F.continuous) hGo f hf').ae hP
  filter_upwards [hh, ae_restrict_mem (hGo.preimage F.continuous).measurableSet]
    with x hx hxG
  simpa [Pullback.coordinate, hxG, f, Homeomorph.subtype] using hx

/-- The upstream chart operator for a global coordinate map has the ordinary
composition formula on the inverse-image domain. -/
theorem coordinate_operator {K K' : ℝ≥0}
    (hd : 1 ≤ d) (hs : 0 < s) (hs1 : s < 1) (hpt : p ≠ ∞)
    (F : Domain d ≃ₜ Domain d) (hF : LipschitzWith K F)
    (hF' : LipschitzWith K' F.symm) (hGo : IsOpen G) (hpre : H = F ⁻¹' G) :
    ∃ T : Space 𝕜 G s p →L[𝕜] Space 𝕜 H s p,
      ∀ u, (firstProjection (T u) : Domain d → 𝕜) =ᵐ[domainMeasure H]
        fun x => firstProjection u (F x) := by
  have hHo : IsOpen H := by rw [hpre]; exact hGo.preimage F.continuous
  let f : H ≃ₜ G := F.sets hpre
  have hf : LipschitzWith K f := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact hF.dist_le_mul x y
  have hf' : LipschitzWith K' f.symm := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact hF'.dist_le_mul x y
  obtain ⟨C, hC⟩ := bilipschitz_pullback d hd s hs hs1 p hpt K K'
  obtain ⟨T, hT⟩ := (hC (𝕜 := 𝕜) _ _ hHo hGo f hf hf').2.2
  refine ⟨T, fun u => ?_⟩
  filter_upwards [(hT u).1, ae_restrict_mem hHo.measurableSet]
    with x hx hxG
  simpa [chartPullback, hxG, f, Homeomorph.subtype] using hx

set_option maxHeartbeats 2000000 in
/-- A localized boundary piece in global bi-Lipschitz flattened coordinates.
Only local agreement with the upper half-space is required. -/
theorem flattened_piece {n : ℕ} {G : Set (Domain (n + 1))} {L L' : ℝ≥0}
    (hs : 0 < s) (hs1 : s < 1) (hpt : p ≠ ∞) (hGo : IsOpen G)
    (F : Domain (n + 1) ≃ₜ Domain (n + 1))
    (hF : LipschitzWith L F) (hF' : LipschitzWith L' F.symm)
    (Q : Set (Domain (n + 1))) (hQo : IsOpen Q)
    (hQR : ∀ x ∈ Q, flatReflection x ∈ Q)
    (hside : ∀ x ∈ Q, F x ∈ G ↔ x ∈ upperHalfSpace n)
    (φ : Domain (n + 1) → 𝕜)
    (hφ : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) φ) (hc : HasCompactSupport φ)
    (hφQ : tsupport φ ⊆ F '' Q) :
    ∃ (K : Set (Domain (n + 1))), IsCompact K ∧
    ∃ T : Space 𝕜 G s p →L[𝕜] Space 𝕜 Set.univ s p,
      (∀ u, (firstProjection (T u) : Domain (n + 1) → 𝕜) =ᵐ[domainMeasure G]
        fun x => φ x * firstProjection u x) ∧
      (∀ u, ∀ᵐ x ∂volume, x ∉ K → firstProjection (T u) x = 0) := by
  classical
  let D := F ⁻¹' G
  let W := D ∩ upperHalfSpace n
  let S := F ⁻¹' tsupport φ
  have hDo : IsOpen D := hGo.preimage F.continuous
  have hHo : IsOpen (upperHalfSpace n) :=
    isOpen_lt continuous_const (PiLp.continuous_apply 2 (fun _ : Fin (n + 1) => ℝ) 0)
  have hWo : IsOpen W := hDo.inter hHo
  have hSc : IsCompact S := F.isCompact_preimage.mpr hc
  have hSQ : S ⊆ Q := by
    intro x hx
    obtain ⟨y, hy, he⟩ := hφQ hx
    exact F.injective he ▸ hy
  let K := S ∪ flatReflection '' S
  have hKc : IsCompact K := hSc.union
    (hSc.image (flatReflectionLinearIsometryEquiv n).continuous)
  have hKQ : K ⊆ Q := by
    rintro x (hx | ⟨y, hy, rfl⟩)
    · exact hSQ hx
    · exact hQR y (hSQ hy)
  obtain ⟨δ, hδ, hδQ⟩ := hSc.exists_cthickening_subset_open hQo hSQ
  have hsep : ∀ x ∈ S, ∀ y ∉ Q, δ ≤ dist x y := by
    intro x hx y hy
    by_contra! hh
    exact hy (hδQ (Metric.mem_cthickening_of_dist_le y x δ _ hx
      (by simpa [dist_comm] using hh.le)))
  obtain ⟨Lφ, hLφ⟩ := hφ.lipschitzWith_of_hasCompactSupport hc (by simp)
  obtain ⟨M, hM⟩ := hc.exists_bound_of_continuous hφ.continuous
  obtain ⟨Cφ, hCφ⟩ := bounded_lipschitz_multiplier (n + 1) (by omega)
    s hs hs1 p hpt (⟨max M 0, le_max_right _ _⟩ : ℝ≥0) Lφ
  obtain ⟨Mφ, hMφ⟩ := (hCφ G hGo φ hLφ.lipschitzOnWith
    (fun x _ => (hM x).trans (le_max_left _ _))).2
  obtain ⟨P, hP⟩ := coordinate_operator (𝕜 := 𝕜) (by omega : 1 ≤ n + 1)
    hs hs1 hpt F hF hF' hGo (H := D) rfl
  let A := P.comp Mφ
  have hA (u : Space 𝕜 G s p) :
      (firstProjection (A u) : Domain (n + 1) → 𝕜) =ᵐ[domainMeasure D]
        fun x => φ (F x) * firstProjection u (F x) := by
    exact (hP (Mφ u)).trans (coordinate_ae F hF' hGo (hMφ u).1)
  obtain ⟨B0, hB0⟩ := restriction (𝕜 := 𝕜) (s := s) hpt
    (show W ⊆ D from Set.inter_subset_left)
  let B := B0.comp A
  have hB (u : Space 𝕜 G s p) :
      (firstProjection (B u) : Domain (n + 1) → 𝕜) =ᵐ[domainMeasure W]
        fun x => φ (F x) * firstProjection u (F x) := by
    exact (hB0 (A u)).1.trans ((hA u).filter_mono
      (ae_mono (Measure.restrict_mono Set.inter_subset_left le_rfl)))
  have haway : ∀ u, SupportedAway W (upperHalfSpace n) δ (firstProjection (B u)) := by
    intro u
    filter_upwards [hB u] with x hx hnonzero y hy
    have hxS : x ∈ S := by
      apply subset_tsupport φ
      intro hz
      exact hnonzero (by simp [hx, hz])
    apply hsep x hxS y
    intro hyQ
    apply hy.2
    exact ⟨(hside y hyQ).mpr hy.1, hy.1⟩
  have hBsupp : ∀ u, ∀ᵐ x ∂domainMeasure W, x ∉ S → firstProjection (B u) x = 0 := by
    intro u
    filter_upwards [hB u] with x hx hxS
    rw [hx, image_eq_zero_of_notMem_tsupport hxS, zero_mul]
  obtain ⟨V, hVres, hVsupp⟩ := flat_patch_extension hs hs1 hpt hWo
    Set.inter_subset_right δ hδ B haway S hSc hBsupp
  have hV (u : Space 𝕜 G s p) :
      (firstProjection (V u) : Domain (n + 1) → 𝕜) =ᵐ[domainMeasure D]
        fun x => φ (F x) * firstProjection u (F x) := by
    have hvw := (ae_restrict_iff' hWo.measurableSet).mp ((hVres u).trans (hB u))
    filter_upwards [ae_restrict_of_ae hvw, ae_restrict_of_ae (hVsupp u),
      ae_restrict_mem hDo.measurableSet] with x hx hsupp hxD
    by_cases hxQ : x ∈ Q
    · exact hx ⟨hxD, (hside x hxQ).mp hxD⟩
    · rw [hsupp (fun hxK => hxQ (hKQ hxK)),
        image_eq_zero_of_notMem_tsupport (fun hxS => hxQ (hSQ hxS)), zero_mul]
  obtain ⟨P', hP'⟩ := coordinate_operator (𝕜 := 𝕜) (G := Set.univ) (H := Set.univ)
    (by omega : 1 ≤ n + 1) hs hs1 hpt F.symm hF' hF isOpen_univ (by simp)
  let T := P'.comp V
  have hT (u : Space 𝕜 G s p) :
      (firstProjection (T u) : Domain (n + 1) → 𝕜) =ᵐ[volume]
        fun x => firstProjection (V u) (F.symm x) := by
    simpa only [T, ContinuousLinearMap.comp_apply, domainMeasure, Measure.restrict_univ]
      using hP' (V u)
  refine ⟨F '' K, hKc.image F.continuous, T, ?_, ?_⟩
  · intro u
    have hh := coordinate_ae F.symm hF hDo (hV u)
    have hpre : F.symm ⁻¹' D = G := by
      ext x
      simp [D]
    rw [hpre] at hh
    filter_upwards [ae_restrict_of_ae (hT u), hh] with x hx hh
    simpa only [F.apply_symm_apply] using hx.trans hh
  · intro u
    have hsupp : ∀ᵐ x ∂volume,
        F.symm x ∉ K → firstProjection (V u) (F.symm x) = 0 := by
      have hh := coordinate_ae F.symm hF isOpen_univ
        (show ∀ᵐ x ∂domainMeasure Set.univ, x ∉ K → firstProjection (V u) x = 0 by
          simpa only [domainMeasure, Measure.restrict_univ] using hVsupp u)
      simpa only [Set.preimage_univ, domainMeasure, Measure.restrict_univ] using hh
    filter_upwards [hT u, hsupp] with x hx hs hxK
    exact hx.trans (hs (fun hh => hxK ⟨F.symm x, hh, F.apply_symm_apply x⟩))

/-- Separate the first (normal) coordinate from the remaining tangential
coordinates. Finite dimensionality makes both linear directions continuous,
including when the tangential factor has dimension zero. -/
def normalCoordinates (n : ℕ) : Domain (n + 1) ≃L[ℝ] P102.U4.GraphPieces.Ambient n :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x => WithLp.toLp 2 (WithLp.toLp 2 (fun i : Fin n => x i.succ), x 0)
      invFun := fun z => WithLp.toLp 2 (Fin.cons z.ofLp.2 z.ofLp.1.ofLp)
      left_inv := by
        intro x
        ext i
        exact Fin.cases (by simp) (fun j => by simp) i
      right_inv := by
        intro z
        apply (WithLp.equiv 2 (P102.U4.Space n × ℝ)).injective
        ext i <;> simp
      map_add' := by
        intro x y
        apply (WithLp.equiv 2 (P102.U4.Space n × ℝ)).injective
        ext i <;> simp
      map_smul' := by
        intro c x
        apply (WithLp.equiv 2 (P102.U4.Space n × ℝ)).injective
        ext i <;> simp }

@[simp] theorem normalCoordinates_apply (n : ℕ) (x : Domain (n + 1)) :
    (normalCoordinates n x).ofLp = (WithLp.toLp 2 (fun i : Fin n => x i.succ), x 0) := rfl

@[simp] theorem normalCoordinates_reflection (n : ℕ) (x : Domain (n + 1)) :
    (normalCoordinates n (flatReflection x)).ofLp =
      ((normalCoordinates n x).ofLp.1, -(normalCoordinates n x).ofLp.2) := by
  simp only [normalCoordinates_apply, flatReflection]
  congr 1

set_option maxHeartbeats 2000000 in
/-- Local boundary-chart step: localize, flatten, extend across artificial edges,
reflect, and push forward through the global Lipschitz graph shear. -/
theorem boundary_piece {n : ℕ} {G : Set (Domain (n + 1))}
    (hs : 0 < s) (hs1 : s < 1) (hpt : p ≠ ∞) (hGo : IsOpen G)
    (C : P102.Sobolev.Geometry.BoundaryChart (geometryCoordinates n ⁻¹' G))
    (r a : ℝ) (_hr : 0 < r) (hrC : r < C.radius)
    (_ha : 0 < a) (haC : a < C.height)
    (φ : Domain (n + 1) → 𝕜)
    (hφ : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) φ) (hc : HasCompactSupport φ)
    (hφC : tsupport φ ⊆ geometryCoordinates n ''
      P102.Sobolev.Geometry.chartImage C.frame C.graphFunction C.center r a) :
    ∃ (K : Set (Domain (n + 1))), IsCompact K ∧
    ∃ T : Space 𝕜 G s p →L[𝕜] Space 𝕜 Set.univ s p,
      (∀ u, (firstProjection (T u) : Domain (n + 1) → 𝕜) =ᵐ[domainMeasure G]
        fun x => φ x * firstProjection u x) ∧
      (∀ u, ∀ᵐ x ∂volume, x ∉ K → firstProjection (T u) x = 0) := by
  classical
  let J := normalCoordinates n
  obtain ⟨g, hg, heq⟩ := C.graph_lipschitz.extend_real
  let S := P102.Sobolev.Geometry.shearHomeomorph g hg.continuous
  let F : Domain (n + 1) ≃ₜ Domain (n + 1) :=
    J.toHomeomorph.trans (S.trans (C.frame.toHomeomorph.trans
      (geometryCoordinates n).toHomeomorph))
  have hS := P102.Sobolev.Geometry.shear_lipschitzWith hg
  have hS' : LipschitzWith (P102.Sobolev.Geometry.shearConstant C.constant) S.symm := by
    change LipschitzWith _ (P102.Sobolev.Geometry.unshear g)
    rw [P102.Sobolev.Geometry.unshear_eq_shear_neg]
    exact P102.Sobolev.Geometry.shear_lipschitzWith hg.neg
  have hF := (geometryCoordinates n).lipschitzWith.comp
    (C.frame.isometry.lipschitzWith.comp (hS.comp J.toContinuousLinearMap.lipschitzWith))
  have hF' := J.symm.toContinuousLinearMap.lipschitzWith.comp
    (hS'.comp (C.frame.symm.isometry.lipschitzWith.comp (geometryCoordinates n).symm.lipschitzWith))
  let Q := J ⁻¹' P102.Sobolev.Geometry.cylinder C.center C.radius C.height
  have hQo : IsOpen Q :=
    (P102.Sobolev.Geometry.cylinder_open C.center C.radius C.height).preimage J.continuous
  have hQR : ∀ x ∈ Q, flatReflection x ∈ Q := by
    intro x hx
    change (J (flatReflection x)).ofLp.1 ∈ Metric.ball C.center C.radius ∧
      (J (flatReflection x)).ofLp.2 ∈ Set.Ioo (-C.height) C.height
    rw [show (J (flatReflection x)).ofLp = ((J x).ofLp.1, -(J x).ofLp.2) from
      normalCoordinates_reflection n x]
    exact ⟨hx.1, by constructor <;> linarith [hx.2.1, hx.2.2]⟩
  have hlocal (x : Domain (n + 1)) (hx : x ∈ Q) :
      F x = geometryCoordinates n
        (C.frame (P102.Sobolev.Geometry.shear C.graphFunction (J x))) := by
    change geometryCoordinates n (C.frame (P102.Sobolev.Geometry.shear g (J x))) = _
    congr 2
    simp only [P102.Sobolev.Geometry.shear, heq hx.1]
  have hside : ∀ x ∈ Q, F x ∈ G ↔ x ∈ upperHalfSpace n := by
    intro x hx
    have hxchart : C.frame (P102.Sobolev.Geometry.shear C.graphFunction (J x)) ∈
        P102.Sobolev.Geometry.chartImage C.frame C.graphFunction C.center C.radius C.height :=
      ⟨_, ⟨J x, hx, rfl⟩, rfl⟩
    constructor
    · intro hxG
      have hw : C.frame (P102.Sobolev.Geometry.shear C.graphFunction (J x)) ∈
          (geometryCoordinates n ⁻¹' G) ∩
          P102.Sobolev.Geometry.chartImage C.frame C.graphFunction C.center C.radius C.height :=
        ⟨by change geometryCoordinates n _ ∈ G; rw [← hlocal x hx]; exact hxG, hxchart⟩
      rw [C.side] at hw
      obtain ⟨u, ⟨v, hv, hvu⟩, hu⟩ := hw
      have hvx : v = J x := (P102.Sobolev.Geometry.shearEquiv C.graphFunction).injective
        (hvu.trans (C.frame.injective hu))
      change 0 < (J x).ofLp.2
      rw [← hvx]
      exact hv.2.1
    · intro hxH
      have hw : C.frame (P102.Sobolev.Geometry.shear C.graphFunction (J x)) ∈
          C.frame '' (P102.Sobolev.Geometry.shear C.graphFunction ''
            P102.Sobolev.Geometry.upperCylinder C.center C.radius C.height) :=
        ⟨_, ⟨J x, ⟨hx.1, hxH, hx.2.2⟩, rfl⟩, rfl⟩
      rw [← C.side] at hw
      rw [hlocal x hx]
      exact hw.1
  have himage : geometryCoordinates n ''
      P102.Sobolev.Geometry.chartImage C.frame g C.center C.radius C.height = F '' Q := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, ⟨w, hw, rfl⟩, rfl⟩, rfl⟩
      refine ⟨J.symm w, ?_, ?_⟩
      · change J (J.symm w) ∈ P102.Sobolev.Geometry.cylinder C.center C.radius C.height
        simpa only [J.apply_symm_apply] using hw
      · change geometryCoordinates n (C.frame (P102.Sobolev.Geometry.shear g (J (J.symm w)))) = _
        rw [J.apply_symm_apply]
    · rintro ⟨y, hy, rfl⟩
      exact ⟨_, ⟨_, ⟨J y, hy, rfl⟩, rfl⟩, rfl⟩
  have hsupp : tsupport φ ⊆ geometryCoordinates n ''
      P102.Sobolev.Geometry.chartImage C.frame C.graphFunction C.center C.radius C.height :=
    hφC.trans (Set.image_mono (P102.Sobolev.Geometry.chartImage_mono
      C.frame C.graphFunction C.center hrC.le haC.le))
  rw [P102.Sobolev.Geometry.chartImage_eq_of_eqOn C.frame heq, himage] at hsupp
  exact flattened_piece hs hs1 hpt hGo F hF hF' Q hQo hQR hside φ hφ hc hsupp

end Extension

/-- The full source conclusion, assembled from its interior and boundary pieces. -/
theorem bounded_linear_extension : Specs.P102.Fractional.Extension.extension := by
  intro n G hG s hs hs1 p _ hpt 𝕜 _
  classical
  by_cases hEmpty : G = ∅
  · subst G
    exact Extension.empty_extension (n + 1) s p
  have hGo : IsOpen G := (geometryCoordinates n).toHomeomorph.isOpen_preimage.mp hG.1
  obtain ⟨k, C, r, a, hsmall, _hcover, V, χ, _hVo, hGV, hχ, hsum, hχ0, _hsep, hχC⟩ :=
    P102.Sobolev.Geometry.finite_localization n (geometryCoordinates n ⁻¹' G) hG
  let φ : Fin (k + 1) → Domain (n + 1) → 𝕜 :=
    fun i x => (χ i ((geometryCoordinates n).symm x) : 𝕜)
  have hφ (i) := Extension.cutoff_in_coordinates (𝕜 := 𝕜) n (χ i)
    (hχ i).1 (hχ i).2.1
  have hφ0 : tsupport (φ 0) ⊆ G := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (hφ 0).2.2 hx
    exact hχ0 hy
  obtain ⟨E0, hE0res, hE0supp⟩ := Extension.interior_piece (by omega : 1 ≤ n + 1)
    hs hs1 hpt hGo (φ 0) (hφ 0).1 (hφ 0).2.1 hφ0
  have hb (i : Fin k) :
      ∃ (K : Set (Domain (n + 1))), IsCompact K ∧
      ∃ E : Space 𝕜 G s p →L[𝕜] Space 𝕜 Set.univ s p,
        (∀ u, (firstProjection (E u) : Domain (n + 1) → 𝕜) =ᵐ[domainMeasure G]
          fun x => φ i.succ x * firstProjection u x) ∧
        (∀ u, ∀ᵐ x ∂volume, x ∉ K → firstProjection (E u) x = 0) := by
    apply Extension.boundary_piece hs hs1 hpt hGo (C i) (r i) (a i)
      (hsmall i).1 (hsmall i).2.1 (hsmall i).2.2.1 (hsmall i).2.2.2
      (φ i.succ) (hφ i.succ).1 (hφ i.succ).2.1
    exact (hφ i.succ).2.2.trans (Set.image_mono (hχC i))
  choose K hK E hEres hEsupp using hb
  let Eall : Fin (k + 1) → Space 𝕜 G s p →L[𝕜] Space 𝕜 Set.univ s p :=
    Fin.cases E0 E
  let Kall : Fin (k + 1) → Set (Domain (n + 1)) := Fin.cases (tsupport (φ 0)) K
  apply Extension.finite_assembly hpt hGo φ ?_ Eall ?_ Kall ?_ ?_
  · intro x hx
    have hx' : (geometryCoordinates n).symm x ∈ geometryCoordinates n ⁻¹' G := by
      simpa only [Set.mem_preimage, (geometryCoordinates n).apply_symm_apply] using hx
    have hp := hsum ((geometryCoordinates n).symm x) (hGV (subset_closure hx'))
    change ∑ i, (χ i ((geometryCoordinates n).symm x) : 𝕜) = 1
    exact_mod_cast hp
  · intro i
    exact Fin.cases hE0res hEres i
  · intro i
    exact Fin.cases (hφ 0).2.1 hK i
  · intro i
    exact Fin.cases hE0supp hEsupp i

end P102.Fractional
