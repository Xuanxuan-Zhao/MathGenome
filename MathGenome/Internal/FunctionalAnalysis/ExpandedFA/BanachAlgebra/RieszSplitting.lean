import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachAlgebra.HolomorphicSpectralMapping
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachAlgebra.RieszSplitting
import Mathlib.Topology.Separation.Regular

noncomputable section
namespace ExpandedFA.BanachAlgebra.RieszSplitting
open Set
open ContourCalculus HolomorphicHomomorphism HolomorphicSpectralMapping
open Specs.ExpandedFA.BanachAlgebra.Conventions
universe u

lemma cutoff_differentiable {U₁ U₂ : Set ℂ} {f : ℂ → ℂ}
    (h₁ : IsOpen U₁) (h₂ : IsOpen U₂)
    (hf₁ : EqOn f (fun _ => 1) U₁) (hf₂ : EqOn f (fun _ => 0) U₂) :
    DifferentiableOn ℂ f (U₁ ∪ U₂) := by
  intro z hz
  rcases hz with hz | hz
  · exact ((differentiableAt_const (c := (1 : ℂ))).congr_of_eventuallyEq
      (Filter.eventuallyEq_iff_exists_mem.mpr ⟨U₁, h₁.mem_nhds hz, hf₁⟩)).differentiableWithinAt
  · exact ((differentiableAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      (Filter.eventuallyEq_iff_exists_mem.mpr ⟨U₂, h₂.mem_nhds hz, hf₂⟩)).differentiableWithinAt


theorem separating_neighborhoods : Spec.SeparatingNeighborhoods := by
  intro K₁ K₂ h₁ h₂ hd
  obtain ⟨U₁, U₂, ho₁, ho₂, hs₁, hs₂, hdU⟩ :=
    SeparatedNhds.of_isCompact_isClosed h₁ h₂.isClosed hd
  refine ⟨U₁, U₂, ho₁, ho₂, hdU, hs₁, hs₂, ?_⟩
  classical
  apply cutoff_differentiable ho₁ ho₂
  · intro z hz
    exact indicator_of_mem hz _
  · intro z hz
    exact indicator_of_notMem (fun h => Set.disjoint_left.mp hdU h hz) _

section Projection
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X]

lemma projection_fixed {P : X →L[ℂ] X} (hP : P * P = P) {x : X}
    (hx : x ∈ P.range) : P x = x := by
  obtain ⟨y, rfl⟩ := hx
  exact congrArg (fun Q : X →L[ℂ] X => Q y) hP

lemma projection_range_closed {P : X →L[ℂ] X} (hP : P * P = P) :
    IsClosed (P.range : Set X) := by
  have he : (P.range : Set X) = {x | P x = x} := by
    ext x
    exact ⟨projection_fixed hP, fun hx => ⟨x, hx⟩⟩
  rw [he]
  exact isClosed_eq P.continuous continuous_id

lemma complement_idempotent {P : X →L[ℂ] X} (hP : P * P = P) :
    (1 - P) * (1 - P) = 1 - P := by
  noncomm_ring [hP]

/-- The sum of the two actual projection ranges is a topological direct sum. -/
def projectionEquiv (P : X →L[ℂ] X) (hP : P * P = P) :
    X ≃L[ℂ] (P.range × (1 - P).range) :=
  ContinuousLinearEquiv.equivOfInverse
    (P.rangeRestrict.prod (1 - P).rangeRestrict)
    (P.range.subtypeL.coprod (1 - P).range.subtypeL)
    (by intro x; change P x + (1 - P) x = x; simp)
    (by
      rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
      apply Prod.ext <;> apply Subtype.ext
      · change P (x + y) = x
        have hx' := projection_fixed hP hx
        obtain ⟨v, rfl⟩ := hy
        have hv := congrArg (fun Q : X →L[ℂ] X => Q v) hP
        change P (P v) = P v at hv
        simp_all [map_add, map_sub]
      · change (1 - P) (x + y) = y
        have hy' := projection_fixed (complement_idempotent hP) hy
        obtain ⟨v, rfl⟩ := hx
        have hv := congrArg (fun Q : X →L[ℂ] X => Q v) hP
        change P (P v) = P v at hv
        simp_all [map_add])

lemma invariant_range {T P : X →L[ℂ] X} (hc : Commute T P) :
    ∀ x ∈ P.range, T x ∈ P.range := by
  rintro _ ⟨y, rfl⟩
  exact ⟨T y, (congrArg (fun Q : X →L[ℂ] X => Q y) hc.eq).symm⟩

/-- Two block inverses assemble into a bounded inverse on the whole space.
This direction of the block spectrum formula is sufficient for exactness. -/
lemma spectrum_subset_union {T P : X →L[ℂ] X} (hc : Commute T P)
    (R₁ : P.range →L[ℂ] P.range) (R₂ : (1 - P).range →L[ℂ] (1 - P).range)
    (h₁ : ∀ x : P.range, (R₁ x : X) = T x)
    (h₂ : ∀ x : (1 - P).range, (R₂ x : X) = T x) :
    spectrum ℂ T ⊆ spectrum ℂ R₁ ∪ spectrum ℂ R₂ := by
  intro z hz
  by_contra h
  have hnot := not_or.mp h
  obtain ⟨S₁, hr₁, hl₁⟩ := isUnit_iff_exists.mp (not_not.mp hnot.1)
  obtain ⟨S₂, hr₂, hl₂⟩ := isUnit_iff_exists.mp (not_not.mp hnot.2)
  let S : X →L[ℂ] X :=
    (P.range.subtypeL.comp (S₁.comp P.rangeRestrict)) +
    ((1 - P).range.subtypeL.comp (S₂.comp (1 - P).rangeRestrict))
  have right (x : X) : z • S x - T (S x) = x := by
    have hh₁ := congrArg (fun Q : P.range →L[ℂ] P.range => (Q (P.rangeRestrict x) : X)) hr₁
    have hh₂ := congrArg (fun Q : (1 - P).range →L[ℂ] (1 - P).range =>
      (Q ((1 - P).rangeRestrict x) : X)) hr₂
    change z • (S₁ (P.rangeRestrict x) : X) -
      (R₁ (S₁ (P.rangeRestrict x)) : X) = P x at hh₁
    change z • (S₂ ((1 - P).rangeRestrict x) : X) -
      (R₂ (S₂ ((1 - P).rangeRestrict x)) : X) = (1 - P) x at hh₂
    rw [h₁] at hh₁
    rw [h₂] at hh₂
    change z • ((S₁ (P.rangeRestrict x) : X) + (S₂ ((1 - P).rangeRestrict x) : X)) -
      T ((S₁ (P.rangeRestrict x) : X) + (S₂ ((1 - P).rangeRestrict x) : X)) = x
    rw [smul_add, map_add, add_sub_add_comm, hh₁, hh₂]
    simp
  have left (x : X) : S (z • x - T x) = x := by
    have hp (x : X) : P (T x) = T (P x) := by
      exact (congrArg (fun Q : X →L[ℂ] X => Q x) hc.eq).symm
    have hq (x : X) : (1 - P) (T x) = T ((1 - P) x) := by
      simp [hp, map_sub]
    have ee₁ : P.rangeRestrict (z • x - T x) =
        (algebraMap ℂ (P.range →L[ℂ] P.range) z - R₁) (P.rangeRestrict x) := by
      apply Subtype.ext
      change P (z • x - T x) = z • P x - (R₁ (P.rangeRestrict x) : X)
      rw [h₁]
      simp [hp]
    have ee₂ : (1 - P).rangeRestrict (z • x - T x) =
        (algebraMap ℂ ((1 - P).range →L[ℂ] (1 - P).range) z - R₂)
          ((1 - P).rangeRestrict x) := by
      apply Subtype.ext
      change (1 - P) (z • x - T x) = z • (1 - P) x -
        (R₂ ((1 - P).rangeRestrict x) : X)
      rw [h₂]
      change (1 - P) (z • x - T x) = z • (1 - P) x - T ((1 - P) x)
      rw [map_sub, map_smul, hq]
    have hh₁ := congrArg (fun Q : P.range →L[ℂ] P.range => (Q (P.rangeRestrict x) : X)) hl₁
    have hh₂ := congrArg (fun Q : (1 - P).range →L[ℂ] (1 - P).range =>
      (Q ((1 - P).rangeRestrict x) : X)) hl₂
    change (S₁ ((algebraMap ℂ (P.range →L[ℂ] P.range) z - R₁)
      (P.rangeRestrict x)) : X) = P x at hh₁
    change (S₂ ((algebraMap ℂ ((1 - P).range →L[ℂ] (1 - P).range) z - R₂)
      ((1 - P).rangeRestrict x)) : X) = (1 - P) x at hh₂
    change (S₁ (P.rangeRestrict (z • x - T x)) : X) +
      (S₂ ((1 - P).rangeRestrict (z • x - T x)) : X) = x
    rw [ee₁, ee₂, hh₁, hh₂]
    simp
  apply hz
  apply isUnit_iff_exists.mpr
  refine ⟨S, ?_, ?_⟩ <;> ext x
  · exact right x
  · exact left x

end Projection


section Calculus
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [Nontrivial X]

lemma cutoff_idempotent (T : X →L[ℂ] X) {U₁ U₂ : Set ℂ} {f : ℂ → ℂ}
    (h₁ : IsOpen U₁) (h₂ : IsOpen U₂)
    (hK : spectrum ℂ T ⊆ U₁ ∪ U₂)
    (hf₁ : EqOn f (fun _ => 1) U₁) (hf₂ : EqOn f (fun _ => 0) U₂) :
    let P := holomorphicValue (X →L[ℂ] X) T (U₁ ∪ U₂) f
    P * P = P := by
  dsimp
  have hA : IsUnitalBanachAlgebra (X →L[ℂ] X) :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  have hf := cutoff_differentiable h₁ h₂ hf₁ hf₂
  rw [← multiplicativity _ hA T _ _ _ (h₁.union h₂) hK hf hf]
  apply holomorphicValue_congr hA T (h₁.union h₂) hK
  intro z hz
  rcases hz with hz | hz
  · simp [hf₁ hz]
  · simp [hf₂ hz]

/-- The cutoff resolvent supplies a bounded inverse on its projection range,
including a zero range. No holomorphic extension across the other piece is
needed: the function is zero on its entire neighborhood. -/
lemma restricted_spectrum_subset (T : X →L[ℂ] X) (K₁ K₂ : Set ℂ)
    (hK : spectrum ℂ T = K₁ ∪ K₂) {U₁ U₂ : Set ℂ} {f : ℂ → ℂ}
    (h₁ : IsOpen U₁) (h₂ : IsOpen U₂) (hd : Disjoint U₁ U₂)
    (hs₁ : K₁ ⊆ U₁) (hs₂ : K₂ ⊆ U₂)
    (hf₁ : EqOn f (fun _ => 1) U₁) (hf₂ : EqOn f (fun _ => 0) U₂)
    (P : X →L[ℂ] X) (heP : P = holomorphicValue (X →L[ℂ] X) T (U₁ ∪ U₂) f)
    (hP : P * P = P) (R : P.range →L[ℂ] P.range)
    (hR : ∀ x : P.range, (R x : X) = T x) : spectrum ℂ R ⊆ K₁ := by
  intro z hz
  by_contra hzK
  have hA : IsUnitalBanachAlgebra (X →L[ℂ] X) :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  let V₁ := U₁ ∩ {z}ᶜ
  let V := V₁ ∪ U₂
  let g : ℂ → ℂ := U₁.indicator (fun w => (z - w)⁻¹)
  have hv₁ : IsOpen V₁ := h₁.inter isOpen_compl_singleton
  have hv : IsOpen V := hv₁.union h₂
  have hKU : spectrum ℂ T ⊆ U₁ ∪ U₂ := by rw [hK]; exact union_subset_union hs₁ hs₂
  have hKV : spectrum ℂ T ⊆ V := by
    rw [hK]
    rintro w (hw | hw)
    · exact Or.inl ⟨hs₁ hw, fun he => hzK (he ▸ hw)⟩
    · exact Or.inr (hs₂ hw)
  have hVU : V ⊆ U₁ ∪ U₂ := union_subset_union inter_subset_left Subset.rfl
  have hf := cutoff_differentiable h₁ h₂ hf₁ hf₂
  have hg₁ : DifferentiableOn ℂ g V₁ := by
    apply (((differentiableOn_const z).sub differentiableOn_id).inv ?_).congr
    · intro w hw
      exact indicator_of_mem hw.1 _
    · intro w hw
      exact sub_ne_zero.mpr (fun he => hw.2 he.symm)
  have hg₂ : DifferentiableOn ℂ g U₂ := by
    apply (differentiableOn_const (0 : ℂ)).congr
    intro w hw
    exact indicator_of_notMem (fun hw₁ => Set.disjoint_left.mp hd hw₁ hw) _
  have hg : DifferentiableOn ℂ g V :=
    (differentiableOn_union_iff_of_isOpen hv₁ h₂).mpr ⟨hg₁, hg₂⟩
  have hePV : P = holomorphicValue (X →L[ℂ] X) T V f :=
    heP.trans (holomorphicValue_restrict hA T (h₁.union h₂) hv hKU hKV hVU hf)
  let G := holomorphicValue (X →L[ℂ] X) T V g
  have hPG : P * G = G := by
    rw [hePV, ← multiplicativity _ hA T V f g hv hKV (hf.mono hVU) hg]
    apply holomorphicValue_congr hA T hv hKV
    intro w hw
    rcases hw with hw | hw
    · simp [hf₁ hw.1]
    · simp [hf₂ hw, show g w = 0 from
        indicator_of_notMem (fun hw₁ => Set.disjoint_left.mp hd hw₁ hw) _]
  have hZG : (algebraMap ℂ (X →L[ℂ] X) z - T) * G = P := by
    have heZ : holomorphicValue (X →L[ℂ] X) T V (fun w => z - w) =
        algebraMap ℂ (X →L[ℂ] X) z - T := by
      have hh := holomorphicValue_const_sub hA T hv hKV differentiableOn_id z
      change holomorphicValue (X →L[ℂ] X) T V (fun w => z - w) =
        algebraMap ℂ (X →L[ℂ] X) z - holomorphicValue (X →L[ℂ] X) T V id at hh
      exact hh.trans (congrArg (fun Q : X →L[ℂ] X => algebraMap ℂ (X →L[ℂ] X) z - Q)
        (coordinate _ hA T V hv hKV))
    rw [← heZ]
    change holomorphicValue (X →L[ℂ] X) T V (fun w => z - w) *
      holomorphicValue (X →L[ℂ] X) T V g = P
    rw [← multiplicativity _ hA T V (fun w => z - w) g hv hKV
      ((differentiableOn_const z).sub differentiableOn_id) hg, hePV]
    apply holomorphicValue_congr hA T hv hKV
    intro w hw
    rcases hw with hw | hw
    · have hne : z - w ≠ 0 := sub_ne_zero.mpr (fun he => hw.2 he.symm)
      simp [g, indicator_of_mem hw.1, hne, hf₁ hw.1]
    · have hn : w ∉ U₁ := fun hw₁ => Set.disjoint_left.mp hd hw₁ hw
      simp [g, indicator_of_notMem hn, hf₂ hw]
  have hcG : Commute T G := commutation _ hA T T V g hv hKV hg (Commute.refl T)
  have hGZ : G * (algebraMap ℂ (X →L[ℂ] X) z - T) = P := by
    rw [(Commute.sub_left (Algebra.commutes z G) hcG).eq] at hZG
    exact hZG
  let S : P.range →L[ℂ] P.range := G.restrict (by
    intro x _
    exact ⟨G x, congrArg (fun Q : X →L[ℂ] X => Q x) hPG⟩)
  apply hz
  apply isUnit_iff_exists.mpr
  refine ⟨S, ?_, ?_⟩
  · ext x
    change z • G x - (R (S x) : X) = x
    rw [hR]
    change z • G x - T (G x) = x
    have he := congrArg (fun Q : X →L[ℂ] X => Q x) hZG
    change z • G x - T (G x) = P x at he
    exact he.trans (projection_fixed hP x.property)
  · ext x
    change G ((algebraMap ℂ (P.range →L[ℂ] P.range) z - R) x : X) = x
    change G (z • (x : X) - (R x : X)) = x
    rw [hR]
    have he := congrArg (fun Q : X →L[ℂ] X => Q x) hGZ
    change G (z • (x : X) - T x) = P x at he
    exact he.trans (projection_fixed hP x.property)
end Calculus


/-- Riesz spectral splitting for arbitrary complex Banach spaces, including
zero spaces and empty spectral pieces. -/
theorem riesz_splitting : Spec.SpectralSplitting.{u} := by
  intro X _ _ _ T K₁ K₂ _ _ hdK hK U₁ U₂ f ho₁ ho₂ hdU hs₁ hs₂ hf₁ hf₂
  let P := holomorphicValue (X →L[ℂ] X) T (U₁ ∪ U₂) f
  change Spec.SplittingData T P K₁ K₂
  have hKU : spectrum ℂ T ⊆ U₁ ∪ U₂ := by
    rw [show spectrum ℂ T = K₁ ∪ K₂ from hK]
    exact union_subset_union hs₁ hs₂
  have hf := cutoff_differentiable ho₁ ho₂ hf₁ hf₂
  have hc : Commute T P := operator_commutation X T T (U₁ ∪ U₂) f
    (ho₁.union ho₂) hKU hf rfl
  have hP : P * P = P := by
    rcases subsingleton_or_nontrivial X with hX | hX
    · exact Subsingleton.elim _ _
    · exact cutoff_idempotent T ho₁ ho₂ hKU hf₁ hf₂
  have hQ := complement_idempotent hP
  have hcQ : Commute T (1 - P) := (Commute.one_right T).sub_right hc
  let R₁ : P.range →L[ℂ] P.range := T.restrict (invariant_range hc)
  let R₂ : (1 - P).range →L[ℂ] (1 - P).range := T.restrict (invariant_range hcQ)
  have hr₁ (x : P.range) : (R₁ x : X) = T x := rfl
  have hr₂ (x : (1 - P).range) : (R₂ x : X) = T x := rfl
  have hsubs : spectrum ℂ R₁ ⊆ K₁ ∧ spectrum ℂ R₂ ⊆ K₂ := by
    rcases subsingleton_or_nontrivial X with hX | hX
    · simp only [spectrum.of_subsingleton, empty_subset, and_self]
    · have hA : IsUnitalBanachAlgebra (X →L[ℂ] X) :=
        ⟨inferInstance, inferInstance, inferInstance⟩
      have hf'₁ : EqOn (fun z => 1 - f z) (fun _ => 1) U₂ := by
        intro z hz; simp [hf₂ hz]
      have hf'₂ : EqOn (fun z => 1 - f z) (fun _ => 0) U₁ := by
        intro z hz; simp [hf₁ hz]
      have heQ : 1 - P = holomorphicValue (X →L[ℂ] X) T (U₂ ∪ U₁)
          (fun z => 1 - f z) := by
        rw [union_comm, holomorphicValue_const_sub hA T (ho₁.union ho₂) hKU hf 1]
        simp [P]
      refine ⟨restricted_spectrum_subset T K₁ K₂ hK ho₁ ho₂ hdU hs₁ hs₂
        hf₁ hf₂ P rfl hP R₁ hr₁, ?_⟩
      apply restricted_spectrum_subset T K₂ K₁ _ ho₂ ho₁ hdU.symm hs₂ hs₁
        hf'₁ hf'₂ (1 - P) heQ hQ R₂ hr₂
      exact (show spectrum ℂ T = K₁ ∪ K₂ from hK).trans (union_comm _ _)
  have hblock := spectrum_subset_union hc R₁ R₂ hr₁ hr₂
  have he₁ : spectrum ℂ R₁ = K₁ := by
    apply Set.Subset.antisymm hsubs.1
    intro z hz
    have hzT : z ∈ spectrum ℂ T := by rw [show spectrum ℂ T = K₁ ∪ K₂ from hK]; exact Or.inl hz
    rcases hblock hzT with hz₁ | hz₂
    · exact hz₁
    · exact False.elim (Set.disjoint_left.mp hdK hz (hsubs.2 hz₂))
  have he₂ : spectrum ℂ R₂ = K₂ := by
    apply Set.Subset.antisymm hsubs.2
    intro z hz
    have hzT : z ∈ spectrum ℂ T := by rw [show spectrum ℂ T = K₁ ∪ K₂ from hK]; exact Or.inr hz
    rcases hblock hzT with hz₁ | hz₂
    · exact False.elim (Set.disjoint_left.mp hdK (hsubs.1 hz₁) hz)
    · exact hz₂
  refine ⟨hP, hc, projection_range_closed hP, projection_range_closed hQ,
    R₁, R₂, hr₁, hr₂, he₁, he₂, projectionEquiv P hP, ?_, ?_⟩
  · intro x
    exact ⟨rfl, rfl⟩
  · intro y
    rfl

/-- The projection is independent of how far the original holomorphic
cutoff is defined beyond the two spectral pieces. -/
theorem splitting_on_neighborhood : Spec.SplittingOnNeighborhood.{u} := by
  intro X _ _ _ T K₁ K₂ h₁ h₂ hdK hK U f hU hKU hf hcut
  obtain ⟨U₁, U₂, ho₁, ho₂, hdU, hs₁, hs₂, hf₁, hf₂⟩ := hcut
  have hK' : spectrum ℂ T = K₁ ∪ K₂ := hK
  have hs₁' : K₁ ⊆ U₁ ∩ U := by
    intro z hz
    exact ⟨hs₁ hz, hKU (hK.symm ▸ Or.inl hz)⟩
  have hs₂' : K₂ ⊆ U₂ ∩ U := by
    intro z hz
    exact ⟨hs₂ hz, hKU (hK.symm ▸ Or.inr hz)⟩
  have hres := riesz_splitting X T K₁ K₂ h₁ h₂ hdK hK (U₁ ∩ U) (U₂ ∩ U) f
    (ho₁.inter hU) (ho₂.inter hU)
    (hdU.mono inter_subset_left inter_subset_left) hs₁' hs₂'
    (hf₁.mono inter_subset_left) (hf₂.mono inter_subset_left)
  have he : holomorphicValue (X →L[ℂ] X) T U f =
      holomorphicValue (X →L[ℂ] X) T ((U₁ ∩ U) ∪ (U₂ ∩ U)) f := by
    rcases subsingleton_or_nontrivial X with hX | hX
    · exact Subsingleton.elim _ _
    · apply holomorphicValue_restrict ⟨inferInstance, inferInstance, inferInstance⟩
        T hU ((ho₁.inter hU).union (ho₂.inter hU)) hKU
      · change spectrum ℂ T ⊆ (U₁ ∩ U) ∪ (U₂ ∩ U)
        rw [hK']
        exact union_subset_union hs₁' hs₂'
      · exact union_subset inter_subset_right inter_subset_right
      · exact hf
  change Spec.SplittingData T (holomorphicValue (X →L[ℂ] X) T U f) K₁ K₂
  rw [he]
  exact hres

end ExpandedFA.BanachAlgebra.RieszSplitting
