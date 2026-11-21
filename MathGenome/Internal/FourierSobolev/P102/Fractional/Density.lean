import MathGenome.Internal.FourierSobolev.Specs.P102.Fractional.Density
import MathGenome.Internal.FourierSobolev.P102.Fractional.Space
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.SharpTraceExtension
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.SecondTraceGeometry

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace P102.Fractional

variable {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
variable {G : Set (Domain d)} {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Construct the canonical graph class from a representative and its two
finite Lp norms. No pointwise identification of chosen Lp representatives is
assumed. -/
def ofMemLp (f : Domain d → 𝕜) (hf : MemLp f p (domainMeasure G))
    (hi : MemLp (increment f) p (pairMeasure G s p)) : Space 𝕜 G s p :=
  ⟨WithLp.toLp 1 (hf.toLp f, hi.toLp (increment f)),
    hi.coeFn_toLp.trans (increment_congr hf.coeFn_toLp).symm⟩

theorem firstProjection_ofMemLp (f : Domain d → 𝕜)
    (hf : MemLp f p (domainMeasure G))
    (hi : MemLp (increment f) p (pairMeasure G s p)) :
    firstProjection (ofMemLp f hf hi) = hf.toLp f := rfl

theorem ofMemLp_ae (f : Domain d → 𝕜) (hf : MemLp f p (domainMeasure G))
    (hi : MemLp (increment f) p (pairMeasure G s p)) :
    (firstProjection (ofMemLp f hf hi) : Domain d → 𝕜) =ᵐ[domainMeasure G] f :=
  hf.coeFn_toLp

/-- Exact full-norm formula for a representative, rather than only for a
chosen Lp coercion. -/
theorem norm_ofMemLp (hpt : p ≠ ∞) (f : Domain d → 𝕜)
    (hf : MemLp f p (domainMeasure G))
    (hi : MemLp (increment f) p (pairMeasure G s p)) :
    ‖ofMemLp f hf hi‖ = (eLpNorm f p (domainMeasure G)).toReal +
      (seminorm G s p f).toReal := by
  rw [space_norm hpt, seminorm_congr (ofMemLp_ae f hf hi)]
  change ‖hf.toLp f‖ + _ = _
  rw [Lp.norm_def, eLpNorm_congr_ae hf.coeFn_toLp]

/-- The two Lp limits are exactly convergence in the full Gagliardo norm.
This bridge is useful for both cutoffs and mollification. -/
theorem tendsto_iff_components {ι : Type*} {l : Filter ι}
    (v : ι → Space 𝕜 G s p) (u : Space 𝕜 G s p) :
    Tendsto v l (𝓝 u) ↔
      Tendsto (fun n => (v n).val.fst) l (𝓝 u.val.fst) ∧
      Tendsto (fun n => (v n).val.snd) l (𝓝 u.val.snd) := by
  rw [tendsto_subtype_rng]
  change Tendsto (fun n => (v n).val) l (𝓝 u.val) ↔ _
  constructor
  · intro h
    exact ⟨((WithLp.continuous_fst 1 _ _).tendsto _).comp h,
      ((WithLp.continuous_snd 1 _ _).tendsto _).comp h⟩
  · rintro ⟨hf, hi⟩
    exact (WithLp.prod_continuous_toLp 1 _ _).continuousAt.tendsto.comp
      (hf.prodMk_nhds hi)

/-- For arbitrary representatives, convergence of the function and of its
weighted increment suffices for full Gagliardo convergence, and is necessary. -/
theorem tendsto_ofMemLp_iff {ι : Type*} {l : Filter ι}
    (f : ι → Domain d → 𝕜) (g : Domain d → 𝕜)
    (hf : ∀ n, MemLp (f n) p (domainMeasure G))
    (hi : ∀ n, MemLp (increment (f n)) p (pairMeasure G s p))
    (hg : MemLp g p (domainMeasure G))
    (hgi : MemLp (increment g) p (pairMeasure G s p)) :
    Tendsto (fun n => ofMemLp (f n) (hf n) (hi n)) l (𝓝 (ofMemLp g hg hgi)) ↔
      Tendsto (fun n => eLpNorm (f n - g) p (domainMeasure G)) l (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (increment (f n) - increment g) p
        (pairMeasure G s p)) l (𝓝 0) := by
  rw [tendsto_iff_components]
  change Tendsto (fun n => (hf n).toLp (f n)) l (𝓝 (hg.toLp g)) ∧
    Tendsto (fun n => (hi n).toLp (increment (f n))) l (𝓝 (hgi.toLp (increment g))) ↔ _
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'', Lp.tendsto_Lp_iff_tendsto_eLpNorm'']

theorem smoothCompactElements_subset_compactElements :
    smoothCompactElements (d := d) 𝕜 s p ⊆ compactElements 𝕜 s p := by
  rintro u ⟨f, _, hfc, hfu⟩
  exact ⟨f, hfc, hfu⟩

/-- Assembly of the two analytic approximation stages. -/
theorem smoothCompact_dense_of_two_stages
    (hcut : Dense (compactElements (d := d) 𝕜 s p))
    (hsm : compactElements (d := d) 𝕜 s p ⊆ closure (smoothCompactElements 𝕜 s p)) :
    Dense (smoothCompactElements (d := d) 𝕜 s p) := by
  intro u
  have hu := hcut u
  simpa only [closure_closure] using closure_mono hsm hu

namespace CoordinateBridge

open ExpandedFA.PartIV.FractionalSobolev
variable {𝕜 : Type} [RCLike 𝕜]

def toCoordinates : Lp 𝕜 p (domainMeasure (Set.univ : Set (Domain d))) →ₗᵢ[𝕜]
    Lp 𝕜 p (volume : Measure (Fin d → ℝ)) :=
  Lp.compMeasurePreservingₗᵢ 𝕜 (WithLp.toLp 2)
    (by simpa only [domainMeasure, Measure.restrict_univ] using
      PiLp.volume_preserving_toLp (Fin d))

def fromCoordinates : Lp 𝕜 p (volume : Measure (Fin d → ℝ)) →ₗᵢ[𝕜]
    Lp 𝕜 p (domainMeasure (Set.univ : Set (Domain d))) :=
  Lp.compMeasurePreservingₗᵢ 𝕜 WithLp.ofLp
    (by simpa only [domainMeasure, Measure.restrict_univ] using
      PiLp.volume_preserving_ofLp (Fin d))

theorem toCoordinates_ae (u : Lp 𝕜 p (domainMeasure (Set.univ : Set (Domain d)))) :
    toCoordinates u =ᵐ[volume] fun x => u (WithLp.toLp 2 x) :=
  Lp.coeFn_compMeasurePreserving _ _

theorem fromCoordinates_ae (u : Lp 𝕜 p (volume : Measure (Fin d → ℝ))) :
    fromCoordinates u =ᵐ[domainMeasure (Set.univ : Set (Domain d))]
      fun x => u (WithLp.ofLp x) :=
  Lp.coeFn_compMeasurePreserving _ _

theorem from_to (u : Lp 𝕜 p (domainMeasure (Set.univ : Set (Domain d)))) :
    fromCoordinates (toCoordinates u) = u := by
  apply Lp.ext
  have ht := (PiLp.volume_preserving_ofLp (Fin d)).quasiMeasurePreserving.ae_eq_comp
    (toCoordinates_ae u)
  have hf := fromCoordinates_ae (toCoordinates u)
  simp only [domainMeasure, Measure.restrict_univ] at *
  exact hf.trans ht

theorem to_from (u : Lp 𝕜 p (volume : Measure (Fin d → ℝ))) :
    toCoordinates (fromCoordinates u) = u := by
  apply Lp.ext
  have hf := fromCoordinates_ae u
  simp only [domainMeasure, Measure.restrict_univ] at hf
  have ht := (PiLp.volume_preserving_toLp (Fin d)).quasiMeasurePreserving.ae_eq_comp hf
  exact (toCoordinates_ae (fromCoordinates u)).trans ht

omit [Fact (1 ≤ p)] in
/-- Change of Euclidean coordinates preserves the original singular double
integral, including its zero value on the diagonal. -/
theorem energy_coordinates (f : Domain d → 𝕜) :
    (∫⁻ x : Fin d → ℝ, ∫⁻ y : Fin d → ℝ,
      differenceKernel s p (y - x) *
        ‖f (WithLp.toLp 2 y) - f (WithLp.toLp 2 x)‖ₑ ^ p.toReal) =
      energy Set.univ s p f := by
  have he := (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurableEmbedding
  have hm := PiLp.volume_preserving_toLp (Fin d)
  unfold energy
  simp only [domainMeasure, Measure.restrict_univ]
  rw [← hm.lintegral_comp_emb he]
  apply lintegral_congr
  intro x
  rw [← hm.lintegral_comp_emb he]
  apply lintegral_congr
  intro y
  by_cases hxy : x = y
  · subst y
    simp [differenceKernel]
  · have hyx : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
    have hne : WithLp.toLp 2 x ≠ WithLp.toLp 2 y :=
      fun h => hxy ((WithLp.equiv 2 _).symm.injective h)
    rw [ite_eq_right hne, differenceKernel, ite_eq_right hyx, ENNReal.rpow_neg]
    rw [div_eq_mul_inv, mul_comm]
    congr 1
    · rw [enorm_sub_rev]
    · congr 2
      simp only [euclideanLength, WithLp.toLp_sub]
      rw [norm_sub_rev]

theorem differenceEnergy_toCoordinates
    (u : Lp 𝕜 p (domainMeasure (Set.univ : Set (Domain d)))) :
    differenceEnergy s p (toCoordinates u) = energy Set.univ s p u := by
  rw [difference_energy_double_integral]
  change (∫⁻ x, ∫⁻ y, differenceKernel s p (y - x) *
    ‖toCoordinates u y - toCoordinates u x‖ₑ ^ p.toReal) = _
  rw [← energy_coordinates]
  apply lintegral_congr_ae
  filter_upwards [toCoordinates_ae u] with x hx
  apply lintegral_congr_ae
  filter_upwards [toCoordinates_ae u] with y hy
  rw [hx, hy]

theorem energy_fromCoordinates (u : Lp 𝕜 p (volume : Measure (Fin d → ℝ))) :
    energy Set.univ s p (fromCoordinates u) = differenceEnergy s p u := by
  rw [← differenceEnergy_toCoordinates, to_from]

/-- A graph class transported to the library's finite-energy realization. -/
def toFractional (hpt : p ≠ ∞)
    (u : P102.Fractional.Space 𝕜 (Set.univ : Set (Domain d)) s p) :
    FractionalSpace 𝕜 d s p :=
  ⟨toCoordinates (firstProjection u), by
    rw [differenceEnergy_toCoordinates]
    exact (firstProjection_range hpt (firstProjection u)).mp ⟨u, rfl⟩⟩

/-- Lift a finite-energy coordinate class through the already proved range
characterization of the canonical graph. -/
def ofFractional (hpt : p ≠ ∞) (u : FractionalSpace 𝕜 d s p) :
    P102.Fractional.Space 𝕜 (Set.univ : Set (Domain d)) s p :=
  Classical.choose ((firstProjection_range hpt (fromCoordinates u.val)).mpr
    (by rw [energy_fromCoordinates]; exact u.property))

theorem firstProjection_ofFractional (hpt : p ≠ ∞) (u : FractionalSpace 𝕜 d s p) :
    firstProjection (ofFractional hpt u) = fromCoordinates u.val :=
  Classical.choose_spec ((firstProjection_range hpt (fromCoordinates u.val)).mpr
    (by rw [energy_fromCoordinates]; exact u.property))

/-- The error in the library statement is exactly the full canonical norm.
In particular no merely-Lp convergence is used in transporting density. -/
theorem norm_sub_eq_error (hpt : p ≠ ∞)
    (v u : P102.Fractional.Space 𝕜 (Set.univ : Set (Domain d)) s p) :
    ‖v - u‖ = ExpandedFA.PartIV.SharpTraceExtension.fractionalError s p
      (toCoordinates (firstProjection v)) (toCoordinates (firstProjection u)) := by
  rw [space_norm hpt, seminorm, ← ENNReal.toReal_rpow,
    ← differenceEnergy_toCoordinates]
  rw [← (toCoordinates (d := d) (𝕜 := 𝕜) (p := p)).norm_map (firstProjection (v - u))]
  simp only [map_sub]
  rfl

end CoordinateBridge

/-- Every compactly supported smooth function has finite weighted increment
norm, including at p = 1. -/
theorem smoothCompact_memLp : Specs.P102.Fractional.Density.SmoothCompactMembership := by
  intro d hd 𝕜 _ s hs0 hs1 p _ hpt f hfs hfc
  have hf : MemLp f p (domainMeasure (Set.univ : Set (Domain d))) := by
    simpa only [domainMeasure, Measure.restrict_univ] using
      (hfs.continuous.memLp_of_hasCompactSupport hfc : MemLp f p volume)
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)
  let φ : ExpandedFA.Distributions.Tests 𝕜
      (⊤ : TopologicalSpace.Opens (Fin d → ℝ)) :=
    ⟨f ∘ e.symm, hfs.comp e.symm.contDiff,
      hfc.comp_homeomorph e.symm.toHomeomorph, Set.subset_univ _⟩
  let z := ExpandedFA.Sobolev.testToSobolev (p := p) 1 φ
  obtain ⟨hfin, _⟩ :=
    ExpandedFA.PartIV.SecondTrace.Analytic.whole_first_fractional_norm_bound s p hs0 hs1 hpt z
  have hrep :
      ExpandedFA.PartIV.FractionalSobolev.wholeLp
        (z.val (ExpandedFA.Sobolev.zeroIndex d 1)) =ᵐ[volume]
        (fun x : Fin d → ℝ => f (WithLp.toLp 2 x)) := by
    apply (ExpandedFA.PartIV.FractionalSobolev.wholeLp_representative _).trans
    have hφ := ExpandedFA.Sobolev.testToDomainLp_coe (p := p) φ
    change ExpandedFA.Sobolev.testToDomainLp φ =ᵐ[volume.restrict Set.univ]
      (fun x => f (WithLp.toLp 2 x)) at hφ
    simpa only [z, ExpandedFA.Sobolev.testToSobolev_underlying,
      TopologicalSpace.Opens.coe_top, Measure.restrict_univ] using hφ
  have heq : CoordinateBridge.toCoordinates (hf.toLp f) =
      ExpandedFA.PartIV.FractionalSobolev.wholeLp
        (z.val (ExpandedFA.Sobolev.zeroIndex d 1)) := by
    apply Lp.ext
    have hfc' := hf.coeFn_toLp
    simp only [domainMeasure, Measure.restrict_univ] at hfc'
    have hm := (PiLp.volume_preserving_toLp (Fin d)).quasiMeasurePreserving.ae_eq_comp hfc'
    exact ((CoordinateBridge.toCoordinates_ae (hf.toLp f)).trans hm).trans hrep.symm
  refine ⟨hf, (memLp_increment_iff
    (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hpt hf.aestronglyMeasurable).mpr ?_⟩
  rw [← energy_congr hf.coeFn_toLp, ← CoordinateBridge.differenceEnergy_toCoordinates, heq]
  exact hfin

/-- C_c^∞ is dense for the original full Gagliardo norm on all of ℝ^d. -/
theorem smoothCompact_dense : Specs.P102.Fractional.Density.SmoothCompactDensity := by
  intro d hd 𝕜 _ s hs0 hs1 p _ hpt u
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  let u' := CoordinateBridge.toFractional hpt u
  obtain ⟨v, f, hfs, hfc, hvf, herr⟩ :=
    ExpandedFA.PartIV.SharpTraceExtension.smooth_density 𝕜 d s hs0 hs1 p hpt u' ε hε
  let w := CoordinateBridge.ofFractional hpt v
  have hw : firstProjection w = CoordinateBridge.fromCoordinates v.val :=
    CoordinateBridge.firstProjection_ofFractional hpt v
  refine ⟨w, ?_, ?_⟩
  · refine ⟨f ∘ WithLp.ofLp, ?_, ?_, ?_⟩
    · exact hfs.comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).contDiff
    · exact hfc.comp_homeomorph (PiLp.homeomorph 2 (fun _ : Fin d => ℝ))
    · rw [hw]
      have hm := (PiLp.volume_preserving_ofLp (Fin d)).quasiMeasurePreserving.ae_eq_comp hvf
      have hr := CoordinateBridge.fromCoordinates_ae v.val
      simp only [domainMeasure, Measure.restrict_univ] at *
      exact (hr.trans hm).symm
  · rw [dist_eq_norm', CoordinateBridge.norm_sub_eq_error hpt, hw,
      CoordinateBridge.to_from]
    exact herr

end P102.Fractional
