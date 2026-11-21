import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch23.MeromorphicGreatPicard
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch23.ThreeOmissionsPunctureExtension

/-!
Great Picard, paper.tex:4320–4351. A finite fiber misses a sufficiently small
punctured disk, because a finite set is closed and does not contain the center.
Three exceptional sphere values would therefore be omitted simultaneously on
one smaller disk, where the three-omissions extension theorem contradicts
essentiality. The scalar assertion uses the corresponding two-omissions
extension theorem with the canonical scalar singularity predicates.
-/
noncomputable section
open Set

namespace D12Complex.MeromorphicGreatPicard

abbrev SpherePunctureExtensionAt :
    Specs.D12Complex.Ch23.MeromorphicGreatPicard.SpherePunctureExtensionAt_type :=
  _root_.D12Complex.SpherePunctureExtensionAt

abbrev finitePreimageValues :
    Specs.D12Complex.Ch23.MeromorphicGreatPicard.finitePreimageValues_type :=
  @_root_.D12Complex.finitePreimageValues

lemma puncturedDisk_mono {a : ℂ} {r R : ℝ} (h : r ≤ R) :
    puncturedDisk a r ⊆ puncturedDisk a R :=
  fun _ hz => ⟨hz.1, lt_of_lt_of_le hz.2 h⟩

/-- Finitely many preimages can be removed by shrinking the radius. -/
lemma finite_preimage_value_omitted {α : Type*} {f : ℂ → α} {a : ℂ} {v : α}
    (hv : v ∈ finitePreimageValues f a) :
    ∃ r : ℝ, 0 < r ∧ ∀ z ∈ puncturedDisk a r, f z ≠ v := by
  obtain ⟨R, hR, hfin⟩ := hv
  have ha : a ∈ ({z | z ∈ puncturedDisk a R ∧ f z = v} : Set ℂ)ᶜ := by
    simp [puncturedDisk]
  obtain ⟨ε, hε, hεsub⟩ :=
    Metric.mem_nhds_iff.mp (hfin.isClosed.isOpen_compl.mem_nhds ha)
  refine ⟨min R ε, lt_min hR hε, ?_⟩
  intro z hz heq
  apply hεsub ?_ ⟨?_, heq⟩
  · exact show dist z a < ε by
      simpa [dist_eq_norm] using lt_of_lt_of_le hz.2 (min_le_right R ε)
  · exact puncturedDisk_mono (min_le_left R ε) hz

/-- Empty fibers are finite, so every locally omitted value is exceptional. -/
lemma omitted_mem_finitePreimageValues {α : Type*} {f : ℂ → α} {a : ℂ} {v : α}
    {R : ℝ} (hR : 0 < R) (hv : ∀ z ∈ puncturedDisk a R, f z ≠ v) :
    v ∈ finitePreimageValues f a := by
  refine ⟨R, hR, ?_⟩
  have he : {z | z ∈ puncturedDisk a R ∧ f z = v} = (∅ : Set ℂ) := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    exact hv z hz.1 hz.2
  rw [he]
  exact Set.finite_empty

theorem not_mem_finitePreimageValues_iff :
    Specs.D12Complex.Ch23.MeromorphicGreatPicard.not_mem_finitePreimageValues_iff_type := by
  intro α f a v
  simp only [_root_.D12Complex.finitePreimageValues, Set.mem_ofPred_eq,
    not_exists, not_and, Set.Infinite]

/-- The analytic input to the sphere cardinal bound. -/
lemma sphere_no_three_exceptions {a : ℂ} {R : ℝ} {f : ℂ → RiemannSphere}
    (hR : 0 < R) (hf : PlaneSphereHolomorphicOn (puncturedDisk a R) f)
    (hess : ¬ SpherePunctureExtensionAt f a)
    (p q s : RiemannSphere) (hp : p ∈ finitePreimageValues f a)
    (hq : q ∈ finitePreimageValues f a) (hs : s ∈ finitePreimageValues f a)
    (hpq : p ≠ q) (hps : p ≠ s) (hqs : q ≠ s) : False := by
  obtain ⟨rp, hrp, hop⟩ := finite_preimage_value_omitted hp
  obtain ⟨rq, hrq, hoq⟩ := finite_preimage_value_omitted hq
  obtain ⟨rs, hrs, hos⟩ := finite_preimage_value_omitted hs
  let δ := min R (min rp (min rq rs))
  have hδ : 0 < δ := lt_min hR (lt_min hrp (lt_min hrq hrs))
  have hδR : δ ≤ R := min_le_left _ _
  have hδp : δ ≤ rp := (min_le_right _ _).trans (min_le_left _ _)
  have hδq : δ ≤ rq := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hδs : δ ≤ rs := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  have hfδ : PlaneSphereHolomorphicOn (puncturedDisk a δ) f :=
    ⟨TwoOmissionsPunctureExtension.puncturedDisk_open a δ,
      fun z hz => hf.2 z (puncturedDisk_mono hδR hz)⟩
  obtain ⟨F, hF, he⟩ :=
    ThreeOmissionsPunctureExtension.three_omissions_puncture_extension a δ f p q s
      hδ hfδ hpq hps hqs
      (fun z hz => hop z (puncturedDisk_mono hδp hz))
      (fun z hz => hoq z (puncturedDisk_mono hδq hz))
      (fun z hz => hos z (puncturedDisk_mono hδs hz))
  exact hess ⟨δ, hδ, F, hF, he⟩

lemma encard_le_two_of_no_three {α : Type*} (s : Set α)
    (h : ∀ p ∈ s, ∀ q ∈ s, ∀ r ∈ s, p ≠ q → p ≠ r → q ≠ r → False) :
    s.encard ≤ 2 := by
  classical
  rcases s.subsingleton_or_nontrivial with hs | ⟨p, hp, q, hq, hpq⟩
  · exact (Set.encard_le_one_iff_subsingleton.mpr hs).trans (by decide)
  · have hsub : s ⊆ {p, q} := by
      intro r hr
      by_cases hpr : p = r
      · exact Or.inl hpr.symm
      by_cases hqr : q = r
      · exact Or.inr hqr.symm
      exact False.elim (h p hp q hq r hr hpq hpr hqr)
    exact (Set.encard_le_encard hsub).trans (le_of_eq (Set.encard_pair hpq))

theorem sphere_great_picard :
    Specs.D12Complex.Ch23.MeromorphicGreatPicard.sphere_great_picard_type := by
  intro a R f hR hf hess
  refine ⟨encard_le_two_of_no_three (finitePreimageValues f a) ?_, ?_⟩
  · intro p hp q hq s hs hpq hps hqs
    exact sphere_no_three_exceptions hR hf hess p q s hp hq hs hpq hps hqs
  · intro v hv
    exact (not_mem_finitePreimageValues_iff f a v).mp hv

theorem meromorphic_great_picard :
    Specs.D12Complex.Ch23.MeromorphicGreatPicard.meromorphic_great_picard_type := by
  intro a R f hR hf hess
  exact sphere_great_picard a R f hR (scalarMeromorphic_planeSphereHolomorphic hf) hess

theorem sphere_great_picard_omitting_infty :
    Specs.D12Complex.Ch23.MeromorphicGreatPicard.sphere_great_picard_omitting_infty_type := by
  intro a R f hR hf hess hinfty
  have hi : sphereInfty ∈ finitePreimageValues f a :=
    omitted_mem_finitePreimageValues hR hinfty
  refine ⟨Set.encard_le_one_iff.mpr ?_, ?_⟩
  · intro u v hu hv
    by_contra huv
    exact sphere_no_three_exceptions hR hf hess (sphereFinite u) (sphereFinite v)
      sphereInfty hu hv hi
      (fun he => huv (sphereFinite_injective he))
      (OnePoint.coe_ne_infty u) (OnePoint.coe_ne_infty v)
  · intro v hv
    exact (not_mem_finitePreimageValues_iff f a (sphereFinite v)).mp hv

theorem holomorphic_great_picard :
    Specs.D12Complex.Ch23.MeromorphicGreatPicard.holomorphic_great_picard_type := by
  intro f a hess
  obtain ⟨R, hR, hf⟩ := hess.1
  refine ⟨Set.encard_le_one_iff.mpr ?_, ?_⟩
  · intro u v hu hv
    by_contra huv
    obtain ⟨ru, hru, hou⟩ := finite_preimage_value_omitted hu
    obtain ⟨rv, hrv, hov⟩ := finite_preimage_value_omitted hv
    let δ := min R (min ru rv)
    have hδ : 0 < δ := lt_min hR (lt_min hru hrv)
    have hδR : δ ≤ R := min_le_left _ _
    have hδu : δ ≤ ru := (min_le_right _ _).trans (min_le_left _ _)
    have hδv : δ ≤ rv := (min_le_right _ _).trans (min_le_right _ _)
    have hfδ : HolomorphicOn (puncturedDisk a δ) f :=
      ⟨TwoOmissionsPunctureExtension.puncturedDisk_open a δ,
        fun z hz => hf.2 z (puncturedDisk_mono hδR hz)⟩
    exact TwoOmissionsPunctureExtension.not_essential_of_two_omissions a δ f u v hδ hfδ huv
      (fun z hz => hou z (puncturedDisk_mono hδu hz))
      (fun z hz => hov z (puncturedDisk_mono hδv hz)) hess
  · intro v hv
    exact (not_mem_finitePreimageValues_iff f a v).mp hv

end D12Complex.MeromorphicGreatPicard
