import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.LongestElementRho
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.WeylChambersLength

noncomputable section
namespace LieAlgebrasAndRepresentations
open Set Module
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma positiveRoots_finite {R : Set E} (hR : RootAxioms R) (v : E) :
    (positiveRoots R v).Finite := hR.finite.subset (fun _ h => h.1)

lemma rootRegular_neg {R : Set E} {v : E} (hv : RootRegular R v) :
    RootRegular R (-v) := by
  intro a ha
  simpa using neg_ne_zero.mpr (hv a ha)

lemma positiveRoots_neg (R : Set E) (v : E) (hR : RootAxioms R) :
    positiveRoots R (-v) = Neg.neg '' positiveRoots R v := by
  ext a
  constructor
  · intro ha
    exact ⟨-a, ⟨hR.neg_mem ha.1, by simpa using ha.2⟩, neg_neg a⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨hR.neg_mem ha.1, by simpa using ha.2⟩

/-- The chamber containing a regular point determines all root signs. -/
lemma weyl_image_positiveRoots {R : Set E} (hR : IsRootSystem R) {v z : E}
    (hv : RootRegular R v) (hz : RootRegular R z) (w : rootWeylGroup R) :
    w.val '' simpleChamber R v = simpleChamber R z ↔
      w.val '' positiveRoots R v = positiveRoots R z := by
  constructor
  · intro hw
    have hpre : w.val.symm z ∈ simpleChamber R v := by
      obtain ⟨x, hx, he⟩ := (show z ∈ w.val '' simpleChamber R v from
        hw.symm ▸ self_mem_simpleChamber R z)
      simpa [← he] using hx
    have hf : w.val '' positiveRoots R v ⊆ positiveRoots R z := by
      rintro _ ⟨a, ha, rfl⟩
      refine ⟨(rootWeylGroup_mem_iff hR.toRootAxioms w.property a).mp ha.1, ?_⟩
      have hi := rootWeylGroup_inner w.property (w.val.symm z) a
      rw [LinearEquiv.apply_symm_apply] at hi
      rw [hi]
      exact simpleChamber_pairing_positive hR.toRootAxioms hpre ha
    have hpre' : w.val v ∈ simpleChamber R z := by
      rw [← hw]
      exact mem_image_of_mem _ (self_mem_simpleChamber R v)
    apply Subset.antisymm hf
    intro a ha
    refine ⟨w.val.symm a, ⟨?_, ?_⟩, w.val.apply_symm_apply a⟩
    · exact (rootWeylGroup_mem_iff hR.toRootAxioms (w⁻¹).property a).mp ha.1
    · have hi := rootWeylGroup_inner w.property v (w.val.symm a)
      rw [LinearEquiv.apply_symm_apply] at hi
      rw [← hi]
      exact simpleChamber_pairing_positive hR.toRootAxioms hpre' ha
  · intro hw
    have hp : w.val v ∈ simpleChamber R z := by
      intro a ha
      obtain ⟨b, hb, he⟩ := hw.symm ▸ ha.1
      rw [← he, rootWeylGroup_inner w.property]
      exact hb.2
    rw [simpleChamber_connectedComponent R hR v hv,
      rootWeylGroup_image_component hR.toRootAxioms w hv]
    have hc := connectedComponentIn_eq
      (show w.val v ∈ connectedComponentIn (rootHyperplaneComplement R) z from
        (simpleChamber_connectedComponent R hR z hz) ▸ hp)
    exact hc.symm.trans (simpleChamber_connectedComponent R hR z hz).symm

theorem longest_weyl_exists_unique : LongestElementRhoSpecs.existenceType := by
  intro E _ _ R hR v hv
  have hc : IsWeylChamber R (simpleChamber R v) :=
    ⟨v, hv, simpleChamber_connectedComponent R hR v hv⟩
  have hn : IsWeylChamber R (simpleChamber R (-v)) :=
    ⟨-v, rootRegular_neg hv, simpleChamber_connectedComponent R hR (-v) (rootRegular_neg hv)⟩
  obtain ⟨w, hw, hu⟩ := weyl_chambers_simply_transitive R hR v hv _ _ hc hn
  refine ⟨w, ?_, ?_⟩
  · exact (weyl_image_positiveRoots hR hv (rootRegular_neg hv) w).mp hw |>.trans
      (positiveRoots_neg R v hR.toRootAxioms)
  · intro z hz
    apply hu z
    apply (weyl_image_positiveRoots hR hv (rootRegular_neg hv) z).mpr
    exact hz.trans (positiveRoots_neg R v hR.toRootAxioms).symm

/-- Public half-sum definitions use the canonical objects in the independent Specs. -/
abbrev rho : LongestElementRhoSpecs.rhoType := @rootRho
abbrev rhoCoroot : LongestElementRhoSpecs.rhoType := @corootRho

theorem longest_weyl_involution : LongestElementRhoSpecs.involutionType := by
  intro E _ _ R hR v hv w hw
  have hsq : (w * w).val '' positiveRoots R v = positiveRoots R v := by
    have hneg : w.val '' (Neg.neg '' positiveRoots R v) =
        Neg.neg '' (w.val '' positiveRoots R v) := by
      simp only [image_image, map_neg]
    rw [weyl_image_mul, hw, hneg, hw, image_image]
    simp only [neg_neg, image_id']
  exact weyl_simpleChamber_stabilizer hR hv (w * w)
    ((weyl_image_positiveRoots hR hv hv (w * w)).mpr hsq)

theorem longest_weyl_length : LongestElementRhoSpecs.lengthType := by
  intro E _ _ R hR v hv w hw
  rw [weyl_length_eq_inversions R hR v hv w]
  congr 1
  apply Subset.antisymm (fun _ ha => ha.1)
  intro a ha
  obtain ⟨b, hb, he⟩ := (show w.val a ∈ Neg.neg '' positiveRoots R v from
    hw ▸ mem_image_of_mem w.val ha)
  exact ⟨ha, by rw [← he, inner_neg_right]; exact neg_neg_of_pos hb.2⟩

/-- A simple reflection permutes the positive roots other than its own root.
Consequently a reflection-compatible odd function has this sum identity. -/
lemma simple_reflection_finsum {R : Set E} (hR : IsRootSystem R) {v a : E}
    (hv : RootRegular R v) (ha : a ∈ simpleRoots R v) (f : E → E)
    (hf : ∀ x, rootReflectionEquiv a (f x) = f (rootReflectionEquiv a x))
    (hfa : f (-a) = -f a) :
    rootReflectionEquiv a (∑ᶠ x ∈ positiveRoots R v, f x) =
      (∑ᶠ x ∈ positiveRoots R v, f x) - (2 : ℝ) • f a := by
  classical
  let S := (positiveRoots_finite hR.toRootAxioms v).toFinset
  have haS : a ∈ S := by simpa [S] using ha.1
  have hm {x : E} (hx : x ∈ S.erase a) : rootReflectionEquiv a x ∈ S.erase a := by
    obtain ⟨hne, hxS⟩ := Finset.mem_erase.mp hx
    have hxP : x ∈ positiveRoots R v := by simpa [S] using hxS
    have hp := simple_reflection_positive hR hv ha hxP hne
    refine Finset.mem_erase.mpr ⟨?_, by simpa [S] using hp⟩
    intro he
    have he' := congrArg (rootReflectionEquiv a) he
    simp only [rootReflectionEquiv_apply, reflection_involutive,
      reflection_self (hR.nonzero a ha.1.1)] at he'
    have hxpos := hxP.2
    rw [he', inner_neg_right] at hxpos
    linarith [ha.1.2]
  have hperm : ∑ x ∈ S.erase a, f (rootReflectionEquiv a x) =
      ∑ x ∈ S.erase a, f x := by
    apply Finset.sum_bij (fun x _ => rootReflectionEquiv a x)
    · exact fun _ hx => hm hx
    · intro x hx y hy he
      exact (rootReflectionEquiv a).injective he
    · intro x hx
      exact ⟨rootReflectionEquiv a x, hm hx, by simp⟩
    · intro x hx
      rfl
  rw [finsum_mem_eq_finite_toFinset_sum f (positiveRoots_finite hR.toRootAxioms v)]
  change rootReflectionEquiv a (∑ x ∈ S, f x) = (∑ x ∈ S, f x) - (2 : ℝ) • f a
  rw [← Finset.sum_erase_add S f haS, map_add, map_sum]
  simp_rw [hf]
  rw [hperm, rootReflectionEquiv_apply, reflection_self (hR.nonzero a ha.1.1), hfa]
  rw [two_smul]
  abel

lemma simple_reflection_rho {R : Set E} (hR : IsRootSystem R) {v a : E}
    (hv : RootRegular R v) (ha : a ∈ simpleRoots R v) :
    rootReflection a (rootRho R v) = rootRho R v - a := by
  simp only [rootRho, ← rootReflectionEquiv_apply, map_smul]
  rw [simple_reflection_finsum hR hv ha (fun x => x) (fun _ => rfl) rfl]
  simp [smul_sub, smul_smul]

lemma simple_reflection_corootRho {R : Set E} (hR : IsRootSystem R) {v a : E}
    (hv : RootRegular R v) (ha : a ∈ simpleRoots R v) :
    rootReflection a (corootRho R v) = corootRho R v - coroot a := by
  simp only [corootRho, ← rootReflectionEquiv_apply, map_smul]
  rw [simple_reflection_finsum hR hv ha coroot
    (fun x => by simp only [rootReflectionEquiv_apply, reflection_coroot])
    (by simp [coroot])]
  simp [smul_sub, smul_smul]

theorem rho_simple_coroot_pairing : LongestElementRhoSpecs.rhoPairingType := by
  intro E _ _ R hR v hv a ha
  have he := simple_reflection_rho hR hv ha
  have hc : (2 * inner ℝ (rootRho R v) a / inner ℝ a a) • a = (1 : ℝ) • a := by
    simpa only [rootReflection, sub_right_inj, one_smul] using he
  have hc' := (smul_left_injective ℝ (hR.nonzero a ha.1.1)) hc
  simp only [coroot, real_inner_smul_right]
  convert hc' using 1
  ring

theorem simple_root_corootRho_pairing : LongestElementRhoSpecs.corootRhoPairingType := by
  intro E _ _ R hR v hv a ha
  have he := simple_reflection_corootRho hR hv ha
  have hc : (2 * inner ℝ (corootRho R v) a / inner ℝ a a) • a =
      (2 / inner ℝ a a) • a := by
    simpa only [rootReflection, coroot, sub_right_inj] using he
  have hc' := (smul_left_injective ℝ (hR.nonzero a ha.1.1)) hc
  have hn : inner ℝ a a ≠ 0 := inner_self_ne_zero (hR.nonzero a ha.1.1)
  have hi : inner ℝ (corootRho R v) a = 1 := by
    field_simp at hc'
    nlinarith
  rwa [real_inner_comm]

theorem empty_longest_rho : LongestElementRhoSpecs.emptyType := by
  intro E _ _ v
  simp [IsLongestWeylElement, positiveRoots, rootRho, corootRho]

end LieAlgebrasAndRepresentations
