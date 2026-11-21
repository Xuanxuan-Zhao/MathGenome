import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch23.GreatPicard
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch23.TwoOmissionsPunctureExtension

/-!
The final finite-preimage step of Great Picard. A finite set away from the
puncture is closed, so a sufficiently small disk misses it. Apply this to
each of two finite fibers and take a common radius. Holomorphy restricts
to that disk; the two-omissions extension theorem contradicts essentiality.
-/

open Set Metric

namespace D12Complex.GreatPicard

/-- Values with finitely many distinct preimages in some smaller punctured disk. -/
def finitePreimageValues (f : ℂ → ℂ) (a : ℂ) (R : ℝ) : Set ℂ :=
  {v | ∃ r : ℝ, 0 < r ∧ r < R ∧
    ({z : ℂ | z ∈ puncturedDisk a r ∧ f z = v} : Set ℂ).Finite}

lemma finite_preimage_omitted (a : ℂ) {R : ℝ} (f : ℂ → ℂ) (v : ℂ)
    (hR : 0 < R)
    (hfinite : ({z : ℂ | z ∈ puncturedDisk a R ∧ f z = v} : Set ℂ).Finite) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧ ∀ z ∈ puncturedDisk a r, f z ≠ v := by
  have ha : a ∈ ({z : ℂ | z ∈ puncturedDisk a R ∧ f z = v} : Set ℂ)ᶜ := by
    rintro ⟨haz, _⟩
    simpa [puncturedDisk] using haz.1
  obtain ⟨ε, hε, hεS⟩ := Metric.isOpen_iff.mp hfinite.isClosed.isOpen_compl a ha
  refine ⟨min ε (R / 2), lt_min hε (half_pos hR),
    (min_le_right _ _).trans_lt (half_lt_self hR), ?_⟩
  intro z hz heq
  have hzε : z ∈ ball a ε := by
    exact Metric.mem_ball.mpr (by
      simpa [dist_eq_norm] using hz.2.trans_le (min_le_left ε (R / 2)))
  apply hεS hzε
  exact ⟨⟨hz.1, hz.2.trans ((min_le_right _ _).trans_lt (half_lt_self hR))⟩, heq⟩

theorem two_finite_preimages_omitted (a : ℂ) (R : ℝ) (f : ℂ → ℂ) (u v : ℂ)
    (hu : u ∈ finitePreimageValues f a R) (hv : v ∈ finitePreimageValues f a R) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧
      (∀ z ∈ puncturedDisk a r, f z ≠ u) ∧
      (∀ z ∈ puncturedDisk a r, f z ≠ v) := by
  obtain ⟨ru, hru, hruR, hufin⟩ := hu
  obtain ⟨rv, hrv, hrvR, hvfin⟩ := hv
  obtain ⟨su, hsu, hsuru, huomit⟩ := finite_preimage_omitted a f u hru hufin
  obtain ⟨sv, hsv, hsvrv, hvomit⟩ := finite_preimage_omitted a f v hrv hvfin
  refine ⟨min su sv, lt_min hsu hsv,
    (min_le_left _ _).trans_lt (hsuru.trans hruR), ?_, ?_⟩
  · intro z hz
    exact huomit z ⟨hz.1, hz.2.trans_le (min_le_left _ _)⟩
  · intro z hz
    exact hvomit z ⟨hz.1, hz.2.trans_le (min_le_right _ _)⟩

theorem exceptional_values_subsingleton (a : ℂ) (R : ℝ) (f : ℂ → ℂ)
    (_hR : 0 < R) (hf : HolomorphicOn (puncturedDisk a R) f)
    (hessential : EssentialSingularityAt f a) :
    (finitePreimageValues f a R).Subsingleton := by
  intro u hu v hv
  by_contra huv
  obtain ⟨r, hr, hrR, huomit, hvomit⟩ :=
    two_finite_preimages_omitted a R f u v hu hv
  have hfr : HolomorphicOn (puncturedDisk a r) f :=
    ⟨TwoOmissionsPunctureExtension.puncturedDisk_open a r,
      fun z hz => hf.2 z ⟨hz.1, hz.2.trans hrR⟩⟩
  exact TwoOmissionsPunctureExtension.not_essential_of_two_omissions
    a r f u v hr hfr huv huomit hvomit hessential

theorem infinite_preimages (a : ℂ) (R : ℝ) (f : ℂ → ℂ) (hR : 0 < R)
    (v : ℂ) (hv : v ∉ finitePreimageValues f a R) (r : ℝ) (hr : 0 < r) :
    ({z : ℂ | z ∈ puncturedDisk a r ∧ f z = v} : Set ℂ).Infinite := by
  intro hfinite
  apply hv
  refine ⟨min r (R / 2), lt_min hr (half_pos hR),
    (min_le_right _ _).trans_lt (half_lt_self hR), hfinite.subset ?_⟩
  intro z hz
  exact ⟨⟨hz.1.1, hz.1.2.trans_le (min_le_left _ _)⟩, hz.2⟩

theorem exists_global_exception (a : ℂ) (R : ℝ) (f : ℂ → ℂ) (hR : 0 < R)
    (hf : HolomorphicOn (puncturedDisk a R) f)
    (hessential : EssentialSingularityAt f a) :
    ∃ e : ℂ, ∀ v : ℂ, v ≠ e → ∀ r : ℝ, 0 < r →
      ({z : ℂ | z ∈ puncturedDisk a r ∧ f z = v} : Set ℂ).Infinite := by
  have hsub := exceptional_values_subsingleton a R f hR hf hessential
  by_cases hne : (finitePreimageValues f a R).Nonempty
  · obtain ⟨e, he⟩ := hne
    refine ⟨e, fun v hve => infinite_preimages a R f hR v ?_⟩
    intro hv
    exact hve (hsub hv he)
  · refine ⟨0, fun v _ => infinite_preimages a R f hR v ?_⟩
    intro hv
    exact hne ⟨v, hv⟩

end D12Complex.GreatPicard
