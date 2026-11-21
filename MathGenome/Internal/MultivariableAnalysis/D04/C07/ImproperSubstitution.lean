import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C07.ImproperSubstitution
import MathGenome.Internal.MultivariableAnalysis.D04.C07.RegionSubstitution
import MathGenome.Internal.MultivariableAnalysis.D04.C06.AbsoluteConvergence

/-! Improper substitution via actual compact Jordan truncations.
The equality of absolute masses is proved even when their common value is
infinite. Conditional limits retain the displayed exhaustion throughout.
-/
noncomputable section
open Set Filter Topology
open scoped Classical ENNReal
namespace D04.ImproperSubstitution
open Darboux JordanRegions ImproperExhaustions AbsoluteConvergence

abbrev weightedPullback := @Specs.D04.C07.ImproperSubstitution.Model.weightedPullback

variable {n : ℕ}

/-- Compact containment supplies both the compact image and its Jordan property. -/
theorem compactJordan_image : Specs.D04.C07.ImproperSubstitution.compactJordan_imageType := by
  intro n e he hei K hK
  have hc := hK.1.image_of_continuousOn (e.continuousOn.mono hK.2.2)
  have hj := RegionSubstitution.jordan_image e he hei K hK.2.1
    (by simpa only [hK.1.isClosed.closure_eq] using hK.1)
    (by simpa only [hK.1.isClosed.closure_eq] using hK.2.2)
  refine ⟨hc, hj.2, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact e.map_source (hK.2.2 hx)

lemma image_interior_subset (e : OpenPartialHomeomorph (E n) (E n))
    {S : Set (E n)} (hS : S ⊆ e.source) :
    e '' interior S ⊆ interior (e '' S) :=
  interior_maximal (image_mono interior_subset)
    (e.isOpen_image_of_subset_source isOpen_interior (interior_subset.trans hS))

theorem regularExhaustion_image : Specs.D04.C07.ImproperSubstitution.regularExhaustion_imageType := by
  intro n e he hei K hK
  refine ⟨fun j => compactJordan_image e he hei (hK.1 j), ?_, ?_⟩
  · intro j
    exact (image_mono (hK.2.1 j)).trans (image_interior_subset e (hK.1 (j+1)).2.2)
  · apply Subset.antisymm
    · exact iUnion_subset (fun j => interior_subset.trans
        (compactJordan_image e he hei (hK.1 j)).2.2)
    · intro y hy
      have hx : e.symm y ∈ ⋃ j, interior (K j) := by
        rw [hK.2.2]
        exact e.map_target hy
      obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨j, image_interior_subset e (hK.1 j).2.2
        ⟨e.symm y, hj, e.right_inv hy⟩⟩

theorem regularExhaustion_preimage : Specs.D04.C07.ImproperSubstitution.regularExhaustion_preimageType := by
  intro n e he hei L hL
  have h := regularExhaustion_image e.symm hei he hL
  have heq : (fun j => e.symm '' L j) = (fun j => e.source ∩ e ⁻¹' L j) := by
    funext j
    exact e.symm_image_eq_source_inter_preimage (hL.1 j).2.2
  rwa [heq] at h

/-- Region integrability on a closed box gives native box integrability.
For a nondegenerate box, insert its endpoints in an enclosing box and use
the central grid cell. Degenerate boxes use boundedness and zero content.
This also works for the empty product of coordinate partitions in dimension zero. -/
lemma integrable_box_of_region {Q : Box n} {f : E n → ℝ}
    (hf : RegionIntegrable (fun x : carrier Q => f x)) : Integrable f Q := by
  by_cases hd : Degenerate Q
  · obtain ⟨M, hM⟩ := hf.1
    exact integrable_degenerate f Q (bounded_of_abs_le (fun x hx => by
      simpa only [Real.norm_eq_abs] using hM ⟨x, hx⟩)) hd
  · obtain ⟨R, hR, hi⟩ := hf.2
    have hq := nondegenerate_of_not_degenerate hd
    have hl (i) : R.lower i < Q.lower i :=
      (encloses_open hR (subset_closure (lower_mem Q)) i).1
    have hu (i) : Q.upper i < R.upper i :=
      (encloses_open hR (subset_closure (upper_mem Q)) i).2
    let P : Grid R := fun i => threePartition (R.lower i) (Q.lower i) (Q.upper i)
      (R.upper i) (hl i) (hq i) (hu i)
    let c₀ : CellIndex P := fun _ => (1 : Fin 3)
    have hmid : cellBox P c₀ = Q := by
      apply Subdivision.box_ext <;> ext i <;> rfl
    have hiQ := (subdivision_integrable _ R hi.1 P).mp hi c₀
    rw [hmid] at hiQ
    apply (integrable_congr (f := zeroExtension (fun x : carrier Q => f x))
      (g := f) (fun x hx => zeroExtension_apply _ ⟨x, hx⟩)).mp hiQ

theorem proper_substitution : Specs.D04.C07.ImproperSubstitution.proper_substitutionType := by
  intro n e he hei f hf K hK
  have hT := compactJordan_image e he hei hK
  have hfi := locally_integrable_on_compact_jordan e.open_target hf hT
  have hsub := RegionSubstitution.region_substitution e he hei K hK.2.1
    (by simpa only [hK.1.isClosed.closure_eq] using hK.1)
    (by simpa only [hK.1.isClosed.closure_eq] using hK.2.2)
    (fun y : e '' K => f y) hfi.1
  exact ⟨hfi, hsub.2.1.mp hfi, hsub.2.2 (Or.inl hfi)⟩

theorem locally_integrable_pullback : Specs.D04.C07.ImproperSubstitution.locally_integrable_pullbackType := by
  intro n e he hei f hf Q hQ
  exact integrable_box_of_region
    (proper_substitution e he hei hf ⟨DiscontinuityCriterion.carrier_compact Q, jordan_box Q, hQ⟩).2.1

lemma weightedPullback_abs (e : OpenPartialHomeomorph (E n) (E n)) (f : E n → ℝ) :
    weightedPullback e (fun y => |f y|) = fun x => |weightedPullback e f x| := by
  funext x
  simp only [weightedPullback, Specs.D04.C07.ImproperSubstitution.Model.weightedPullback,
    abs_mul, abs_abs]

theorem proper_abs_substitution : Specs.D04.C07.ImproperSubstitution.proper_abs_substitutionType := by
  intro n e he hei f hf K hK
  have h := proper_substitution e he hei (locally_integrable_abs hf) hK
  simpa only [weightedPullback_abs] using h

theorem absolute_mass_substitution : Specs.D04.C07.ImproperSubstitution.absolute_mass_substitutionType := by
  intro n e he hei f hf
  obtain ⟨K, hK⟩ := regular_exhaustion_exists e.source e.open_source
  have hL := regularExhaustion_image e he hei hK
  have hg := locally_integrable_pullback e he hei hf
  have hleft := (nonnegative_exhaustion e.open_target (locally_integrable_abs hf)
    (fun x _ => abs_nonneg (f x)) hL).2.1
  have hright := (nonnegative_exhaustion e.open_source (locally_integrable_abs hg)
    (fun x _ => abs_nonneg (weightedPullback e f x)) hK).2.1
  rw [absolute_mass_abs] at hleft hright
  change absoluteMass e.target f = absoluteMass e.source (weightedPullback e f)
  rw [← hleft, ← hright]
  congr 1
  funext j
  exact congrArg ENNReal.ofReal (proper_abs_substitution e he hei hf (hK.1 j)).2.2

theorem absolutely_convergent_iff : Specs.D04.C07.ImproperSubstitution.absolutely_convergent_iffType := by
  intro n e he hei f hf
  have hg := locally_integrable_pullback e he hei hf
  have hm := absolute_mass_substitution e he hei hf
  constructor
  · intro h
    exact ⟨hg, hm ▸ h.2⟩
  · intro h
    exact ⟨hf, hm.symm ▸ h.2⟩

theorem integral_along_iff : Specs.D04.C07.ImproperSubstitution.integral_along_iffType := by
  intro n e he hei f hf K hK
  have heq (j) := (proper_substitution e he hei hf (hK.1 j)).2.2
  refine ⟨heq, fun I => ?_⟩
  change Tendsto _ atTop (𝓝 I) ↔ Tendsto _ atTop (𝓝 I)
  have heqfun : (fun j => regionIntegral (fun y : e '' K j => f y)) =
      (fun j => regionIntegral (fun x : K j => weightedPullback e f x)) := funext heq
  rw [heqfun]

theorem improper_substitution : Specs.D04.C07.ImproperSubstitution.improper_substitutionType := by
  intro n e he hei f hf ha
  have hab := absolutely_convergent_iff e he hei hf
  have haf : AbsolutelyConvergent e.target f := ha.elim id hab.mpr
  have hag := hab.mp haf
  obtain ⟨K, hK⟩ := regular_exhaustion_exists e.source e.open_source
  have hL := regularExhaustion_image e he hei hK
  have hlim := (integral_along_iff e he hei hf hK).2 (improperIntegral e.target f)
  have hsigned := absolute_limit_unique e.open_source hag hK
    (hlim.mp ((absolute_exhaustion e.open_target haf).1 _ hL))
  have hafabs : AbsolutelyConvergent e.target (fun y => |f y|) :=
    ⟨locally_integrable_abs hf, by simpa only [absolute_mass_abs] using haf.2⟩
  have hagabs : AbsolutelyConvergent e.source (fun x => |weightedPullback e f x|) :=
    ⟨locally_integrable_abs hag.1, by simpa only [absolute_mass_abs] using hag.2⟩
  have hflim := (absolute_exhaustion e.open_target hafabs).1 _ hL
  have habsfun :
      (fun j => regionIntegral (fun y : e '' K j => |f y|)) =
      (fun j => regionIntegral (fun x : K j => |weightedPullback e f x|)) :=
    funext (fun j => (proper_abs_substitution e he hei hf (hK.1 j)).2.2)
  change Tendsto _ atTop (𝓝 _) at hflim
  rw [habsfun] at hflim
  exact ⟨hsigned, absolute_limit_unique e.open_source hagabs hK hflim⟩

theorem conditional_substitution_iff : Specs.D04.C07.ImproperSubstitution.conditional_substitution_iffType := by
  intro n e he hei f hf K hK I
  have hg := locally_integrable_pullback e he hei hf
  have hL := regularExhaustion_image e he hei hK
  have hab := absolutely_convergent_iff e he hei hf
  have hlim := (integral_along_iff e he hei hf hK).2 I
  constructor
  · rintro ⟨_, _, hn, hI⟩
    exact ⟨hg, hK, fun ha => hn (hab.mpr ha), hlim.mp hI⟩
  · rintro ⟨_, _, hn, hI⟩
    exact ⟨hf, hL, fun ha => hn (hab.mp ha), hlim.mpr hI⟩

theorem zero_dimension : Specs.D04.C07.ImproperSubstitution.zero_dimensionType := by
  intro e f
  have hdet (x : E 0) : (fderiv ℝ e x).det = 1 :=
    LinearMap.det_eq_one_of_subsingleton _
  have hg : weightedPullback e f = f := by
    funext x
    simp only [weightedPullback, Specs.D04.C07.ImproperSubstitution.Model.weightedPullback,
      hdet, abs_one, mul_one, Subsingleton.elim (e x) x]
  have heval (Ω : Set (E 0)) (hΩ : IsOpen Ω) :
      improperIntegral Ω f = (if (0 : E 0) ∈ Ω then f 0 else 0) := by
    obtain ⟨K, hK⟩ := regular_exhaustion_exists Ω hΩ
    have hz := ImproperExhaustions.zero_dimension Ω f
    exact (absolute_limit_unique hΩ hz.2.2.2.1 hK (hz.2.2.2.2 K hK)).symm
  exact ⟨hdet, congrFun hg 0, heval e.target e.open_target, by
    change improperIntegral e.source (weightedPullback e f) = _
    rw [hg]; exact heval e.source e.open_source⟩

end D04.ImproperSubstitution
