import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SimpleRoots
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RankTwoRootSystems
import Mathlib.Algebra.Group.Irreducible.Indecomposable
import Mathlib.LinearAlgebra.QuadraticForm.Dual
import Mathlib.LinearAlgebra.Basis.Basic

/-! Simple roots for a prescribed regular vector (LA-E02).

Source: notes/005/lie-algebras-and-representations.tex, res:E02,
expanded lines 2038–2083. Finite additive generation proves decomposition;
nonpositive pairwise inner products prove independence. For the orbit theorem,
a counterexample with minimal `(v, β)` contradicts simple reflection descent.
The statements and proofs also apply to the empty root system in the zero space.
-/

noncomputable section
namespace LieAlgebrasAndRepresentations
open Set Module
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma simpleRoots_subset_positive (R : Set E) (v : E) :
    simpleRoots R v ⊆ positiveRoots R v := fun _ h => h.1

lemma simpleRoots_subset (R : Set E) (v : E) : simpleRoots R v ⊆ R :=
  fun _ h => h.1.1

lemma simpleRoots_finite {R : Set E} (hR : RootAxioms R) (v : E) :
    (simpleRoots R v).Finite := hR.finite.subset (simpleRoots_subset R v)

lemma positive_or_neg_positive {R : Set E} (hR : RootAxioms R) {v : E}
    (hv : RootRegular R v) {a : E} (ha : a ∈ R) :
    a ∈ positiveRoots R v ∨ -a ∈ positiveRoots R v := by
  rcases lt_or_gt_of_ne (hv a ha) with h | h
  · exact Or.inr ⟨hR.neg_mem ha, by simpa using neg_pos.mpr h⟩
  · exact Or.inl ⟨ha, h⟩

lemma simpleRoots_pairwise_nonpos {R : Set E} (hR : RootAxioms R) {v : E}
    (hv : RootRegular R v) :
    (simpleRoots R v).Pairwise (fun a b => inner ℝ a b ≤ 0) := by
  intro a ha b hb hab
  by_contra! hip
  have hd := difference_root R hR a ha.1.1 b hb.1.1 hab hip
  rcases positive_or_neg_positive hR hv hd with hp | hp
  · exact ha.2 (a-b) hp b hb.1 (by abel)
  · exact hb.2 (-(a-b)) hp a ha.1 (by abel)

lemma simpleRoots_linearIndependent {R : Set E} (hR : RootAxioms R) {v : E}
    (hv : RootRegular R v) :
    LinearIndependent ℝ (fun a : simpleRoots R v => (a : E)) := by
  apply LinearMap.BilinForm.linearIndependent_of_pairwise_le_zero
    (innerₗ E) (f := innerₗ E v)
  · intro x hx
    exact real_inner_self_pos.mpr hx
  · intro a
    exact a.property.1.2
  · intro a b hab
    exact simpleRoots_pairwise_nonpos hR hv a.property b.property
      (fun h => hab (Subtype.ext h))

lemma image_baseOf_eq_simpleRoots (R : Set E) (v : E) :
    (fun a : R => (a : E)) ''
      IsAddIndecomposable.baseOf (fun a : R => (a : E)) (innerₗ E v).toAddMonoidHom =
      simpleRoots R v := by
  ext a
  constructor
  · rintro ⟨a, ⟨ha, hi⟩, rfl⟩
    refine ⟨⟨a.property, ha⟩, ?_⟩
    intro b hb c hc heq
    rcases hi ⟨b, hb.1⟩ hb.2 ⟨c, hc.1⟩ hc.2 heq with h | h
    · exact (ne_of_gt hb.2) (by rw [show b = 0 from h]; simp)
    · exact (ne_of_gt hc.2) (by rw [show c = 0 from h]; simp)
  · intro ha
    refine ⟨⟨a, ha.1.1⟩, ⟨ha.1.2, ?_⟩, rfl⟩
    intro b hb c hc heq
    exact False.elim (ha.2 b ⟨b.property, hb⟩ c ⟨c.property, hc⟩ heq)

lemma positive_mem_closure_simple {R : Set E} (hR : RootAxioms R) (v : E)
    {a : E} (ha : a ∈ positiveRoots R v) :
    a ∈ AddSubmonoid.closure (simpleRoots R v) := by
  let : Finite R := hR.finite.to_subtype
  rw [← image_baseOf_eq_simpleRoots R v,
    AddSubmonoid.closure_image_isAddIndecomposable_baseOf]
  exact AddSubmonoid.subset_closure ⟨⟨a, ha.1⟩, ha.2, rfl⟩

lemma positive_nat_expansion {R : Set E} (hR : RootAxioms R) (v : E)
    {a : E} (ha : a ∈ positiveRoots R v) :
    ∃ c : simpleRoots R v →₀ ℕ,
      Finsupp.linearCombination ℕ (fun b : simpleRoots R v => (b : E)) c = a := by
  apply Finsupp.mem_span_range_iff_exists_finsupp.mp
  have hr : Set.range (fun b : simpleRoots R v => (b : E)) = simpleRoots R v :=
    Subtype.range_coe
  rw [hr, ← Submodule.mem_toAddSubmonoid, Submodule.span_nat_eq_addSubmonoidClosure]
  exact positive_mem_closure_simple hR v ha

lemma simpleRoots_span {R : Set E} (hR : IsRootSystem R) {v : E}
    (hv : RootRegular R v) : Submodule.span ℝ (simpleRoots R v) = ⊤ := by
  apply top_unique
  rw [← hR.span_eq_top]
  apply Submodule.span_le.mpr
  intro a ha
  have hspan {b : E} (hb : b ∈ positiveRoots R v) :
      b ∈ Submodule.span ℝ (simpleRoots R v) := by
    exact AddSubmonoid.closure_le.mpr (fun _ h => Submodule.subset_span h)
      (positive_mem_closure_simple hR.toRootAxioms v hb)
  rcases positive_or_neg_positive hR.toRootAxioms hv ha with hp | hp
  · exact hspan hp
  · simpa using (Submodule.span ℝ (simpleRoots R v)).neg_mem (hspan hp)

theorem simpleRoots_basis : SimpleRootSpecs.basisType := by
  intro E _ _ R hR v hv
  refine ⟨Basis.mk (simpleRoots_linearIndependent hR.toRootAxioms hv) ?_, ?_⟩
  · rw [Subtype.range_coe, simpleRoots_span hR hv]
  · intro a
    exact Basis.mk_apply _ _ a

lemma positive_int_expansion {R : Set E} (hR : RootAxioms R) (v : E)
    {a : E} (ha : a ∈ positiveRoots R v) :
    ∃ c : simpleRoots R v →₀ ℤ,
      Finsupp.linearCombination ℤ (fun b : simpleRoots R v => (b : E)) c = a ∧
      ∀ b, 0 ≤ c b := by
  classical
  refine AddSubmonoid.closure_induction (fun x hx => ?_) ?_
    (fun x y hx hy ihx ihy => ?_) (positive_mem_closure_simple hR v ha)
  · refine ⟨Finsupp.single ⟨x, hx⟩ 1, by simp, ?_⟩
    intro b
    simp only [Finsupp.single_apply]
    split_ifs <;> norm_num
  · exact ⟨0, by simp, by simp⟩
  · obtain ⟨c, hc, hcpos⟩ := ihx
    obtain ⟨d, hd, hdpos⟩ := ihy
    exact ⟨c+d, by simp [hc, hd], fun b => add_nonneg (hcpos b) (hdpos b)⟩

theorem simpleRoots_coefficients : SimpleRootSpecs.coefficientsType := by
  intro E _ _ R hR v hv a ha
  rcases positive_or_neg_positive hR.toRootAxioms hv ha with hp | hp
  · obtain ⟨c, hc, hn⟩ := positive_int_expansion hR.toRootAxioms v hp
    exact ⟨c, hc, Or.inl hn⟩
  · obtain ⟨c, hc, hn⟩ := positive_int_expansion hR.toRootAxioms v hp
    exact ⟨-c, by simp [hc], Or.inr (fun b => by simpa using neg_nonpos.mpr (hn b))⟩

lemma positive_exists_simple_inner_pos {R : Set E} (hR : RootAxioms R) (v : E)
    {b : E} (hb : b ∈ positiveRoots R v) :
    ∃ a ∈ simpleRoots R v, 0 < inner ℝ b a := by
  classical
  obtain ⟨c, hc⟩ := positive_nat_expansion hR v hb
  by_contra! hn
  have hip : 0 < inner ℝ b b := real_inner_self_pos.mpr (hR.nonzero b hb.1)
  have heq := congrArg (fun x => inner ℝ b x) hc
  rw [Finsupp.linearCombination_apply, Finsupp.sum, inner_sum] at heq
  have hs : ∑ a ∈ c.support, inner ℝ b (c a • (a : E)) ≤ 0 := by
    apply Finset.sum_nonpos
    intro a ha
    rw [← Nat.cast_smul_eq_nsmul ℝ, real_inner_smul_right]
    exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (hn a a.property)
  linarith

theorem simpleRoots_lowering : SimpleRootSpecs.loweringType := by
  intro E _ _ R hR v hv b hb hns
  obtain ⟨a, ha, hip⟩ := positive_exists_simple_inner_pos hR.toRootAxioms v hb
  have hba : b ≠ a := fun h => hns (h.symm ▸ ha)
  have hd := difference_root R hR.toRootAxioms b hb.1 a ha.1.1 hba hip
  rcases positive_or_neg_positive hR.toRootAxioms hv hd with hp | hp
  · exact ⟨a, ha, hp⟩
  · exact False.elim (ha.2 b hb (-(b-a)) hp (by abel))

@[simp] lemma rootReflectionEquiv_apply (a b : E) :
    rootReflectionEquiv a b = rootReflection a b := by
  classical
  by_cases ha : a = 0
  · simp [rootReflectionEquiv, ha, rootReflection]
  · rw [rootReflectionEquiv, dite_eq_right ha, Module.reflection_apply]
    simp only [LinearMap.smul_apply, innerₗ_apply_apply, smul_eq_mul]
    rw [rootReflection, real_inner_comm a b]
    congr 2
    ring

@[simp] lemma rootReflectionEquiv_inv (a : E) :
    (rootReflectionEquiv a)⁻¹ = rootReflectionEquiv a := by
  ext b
  apply (rootReflectionEquiv a).injective
  change rootReflectionEquiv a ((rootReflectionEquiv a).symm b) =
    rootReflectionEquiv a (rootReflectionEquiv a b)
  rw [LinearEquiv.apply_symm_apply]
  simp only [rootReflectionEquiv_apply, reflection_involutive]

lemma positive_basis_coords_nonneg {R : Set E} (hR : RootAxioms R) {v : E}
    (b : Basis (simpleRoots R v) ℝ E) (hb : ∀ i, b i = (i : E))
    {a : E} (ha : a ∈ positiveRoots R v) : ∀ i, 0 ≤ b.repr a i := by
  classical
  refine AddSubmonoid.closure_induction (fun a ha => ?_) ?_
    (fun x y hx hy ihx ihy => ?_) (positive_mem_closure_simple hR v ha)
  · intro i
    have heq : a = b ⟨a, ha⟩ := (hb ⟨a, ha⟩).symm
    rw [heq, b.repr_self, Finsupp.single_apply]
    split_ifs <;> norm_num
  · simp
  · intro i
    simpa using add_nonneg (ihx i) (ihy i)

lemma simple_reflection_positive {R : Set E} (hR : IsRootSystem R) {v : E}
    (hv : RootRegular R v) {a x : E} (ha : a ∈ simpleRoots R v)
    (hx : x ∈ positiveRoots R v) (hne : x ≠ a) :
    rootReflection a x ∈ positiveRoots R v := by
  classical
  have hr := hR.reflection_mem a ha.1.1 x hx.1
  rcases positive_or_neg_positive hR.toRootAxioms hv hr with hp | hp
  · exact hp
  obtain ⟨b, hb⟩ := simpleRoots_basis R hR v hv
  let i : simpleRoots R v := ⟨a, ha⟩
  have hxpos := positive_basis_coords_nonneg hR.toRootAxioms b hb hx
  have hrpos := positive_basis_coords_nonneg hR.toRootAxioms b hb hp
  have hzero (j : simpleRoots R v) (hj : j ≠ i) : b.repr x j = 0 := by
    have hai : b.repr a j = 0 := by
      change b.repr (i : E) j = 0
      rw [← hb i, b.repr_self]
      exact Finsupp.single_eq_of_ne hj
    have heq : b.repr (-rootReflection a x) j = - b.repr x j := by
      simp [rootReflection, map_sub, map_smul, hai]
    have hn := hrpos j
    rw [heq] at hn
    exact le_antisymm (neg_nonneg.mp hn) (hxpos j)
  have hre : b.repr x = Finsupp.single i (b.repr x i) := by
    ext j
    by_cases hj : j = i
    · simp [hj]
    · simp [Finsupp.single_eq_of_ne hj, hzero j hj]
  have hline : x ∈ Submodule.span ℝ ({a} : Set E) := by
    have heq : x = (b.repr x i) • a := by
      calc
        x = b.repr.symm (b.repr x) := (b.repr.symm_apply_apply x).symm
        _ = (b.repr x i) • a := by rw [hre]; simp [hb, i]
    rw [heq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  rcases hR.reduced a ha.1.1 x hx.1 hline with heq | heq
  · exact False.elim (hne heq)
  · have hxa := hx.2
    rw [heq, inner_neg_right] at hxa
    linarith [ha.1.2]

lemma simpleWeylGroup_le (R : Set E) (v : E) :
    simpleWeylGroup R v ≤ rootWeylGroup R :=
  Subgroup.closure_mono (Set.image_mono (simpleRoots_subset R v))

lemma simple_reflection_mem {R : Set E} {v a : E} (ha : a ∈ simpleRoots R v) :
    rootReflectionEquiv a ∈ simpleWeylGroup R v :=
  Subgroup.subset_closure (mem_image_of_mem _ ha)

lemma positive_simple_orbit {R : Set E} (hR : IsRootSystem R) {v : E}
    (hv : RootRegular R v) {x : E} (hx : x ∈ positiveRoots R v) :
    ∃ w : simpleWeylGroup R v, ∃ a ∈ simpleRoots R v, w.val a = x := by
  classical
  by_contra hbad
  let S : Set E := {x | x ∈ positiveRoots R v ∧
    ¬ ∃ w : simpleWeylGroup R v, ∃ a ∈ simpleRoots R v, w.val a = x}
  have hf : S.Finite := hR.finite.subset (fun _ h => h.1.1)
  obtain ⟨y, hy⟩ := hf.exists_minimalFor (fun z => inner ℝ v z) S ⟨x, hx, hbad⟩
  have hypos := hy.prop.1
  have hynot := hy.prop.2
  have hys : y ∉ simpleRoots R v := by
    intro hys
    exact hynot ⟨1, y, hys, rfl⟩
  obtain ⟨a, ha, hip⟩ := positive_exists_simple_inner_pos hR.toRootAxioms v hypos
  have hne : y ≠ a := fun h => hys (h.symm ▸ ha)
  have hr := simple_reflection_positive hR hv ha hypos hne
  have hcart : 0 < rootCartan y a :=
    div_pos (mul_pos two_pos hip) (real_inner_self_pos.mpr (hR.nonzero a ha.1.1))
  have hlt : inner ℝ v (rootReflection a y) < inner ℝ v y := by
    change inner ℝ v (y - rootCartan y a • a) < _
    rw [inner_sub_right, real_inner_smul_right]
    linarith [mul_pos hcart ha.1.2]
  have hgood : ∃ w : simpleWeylGroup R v, ∃ b ∈ simpleRoots R v,
      w.val b = rootReflection a y := by
    by_contra hnot
    have hm := hy.le_of_le (show rootReflection a y ∈ S from ⟨hr, hnot⟩) hlt.le
    exact (not_le.mpr hlt) hm
  obtain ⟨w, b, hb, hw⟩ := hgood
  apply hynot
  refine ⟨⟨rootReflectionEquiv a, simple_reflection_mem ha⟩ * w, b, hb, ?_⟩
  change rootReflectionEquiv a (w.val b) = y
  rw [hw, rootReflectionEquiv_apply, reflection_involutive]

lemma root_simple_orbit {R : Set E} (hR : IsRootSystem R) {v : E}
    (hv : RootRegular R v) {x : E} (hx : x ∈ R) :
    ∃ w : simpleWeylGroup R v, ∃ a ∈ simpleRoots R v, w.val a = x := by
  rcases positive_or_neg_positive hR.toRootAxioms hv hx with hp | hp
  · exact positive_simple_orbit hR hv hp
  obtain ⟨w, a, ha, hw⟩ := positive_simple_orbit hR hv hp
  refine ⟨w * ⟨rootReflectionEquiv a, simple_reflection_mem ha⟩, a, ha, ?_⟩
  change w.val (rootReflectionEquiv a a) = x
  rw [rootReflectionEquiv_apply, reflection_self (hR.nonzero a ha.1.1), map_neg, hw, neg_neg]

lemma rootWeylGroup_inner {R : Set E} {w : E ≃ₗ[ℝ] E} (hw : w ∈ rootWeylGroup R) :
    ∀ x y, inner ℝ (w x) (w y) = inner ℝ x y := by
  induction hw using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, rfl⟩ := hw
    intro x y
    simp only [rootReflectionEquiv_apply, reflection_inner]
  | one => intro x y; rfl
  | mul w z hw hz ihw ihz =>
    intro x y
    exact (ihw (z x) (z y)).trans (ihz x y)
  | inv w hw ih =>
    intro x y
    have h := ih (w.symm x) (w.symm y)
    simpa using h.symm

lemma rootWeylGroup_mem_iff {R : Set E} (hR : RootAxioms R)
    {w : E ≃ₗ[ℝ] E} (hw : w ∈ rootWeylGroup R) :
    ∀ x, x ∈ R ↔ w x ∈ R := by
  induction hw using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, rfl⟩ := hw
    intro x
    simp only [rootReflectionEquiv_apply]
    exact ⟨fun hx => hR.reflection_mem a ha x hx,
      fun hx => by simpa using hR.reflection_mem a ha (rootReflection a x) hx⟩
  | one => intro x; rfl
  | mul w z hw hz ihw ihz =>
    intro x
    exact (ihz x).trans (ihw (z x))
  | inv w hw ih =>
    intro x
    simpa using (ih (w.symm x)).symm

lemma rootReflection_map (w : E ≃ₗ[ℝ] E)
    (hw : ∀ x y, inner ℝ (w x) (w y) = inner ℝ x y) (a x : E) :
    w (rootReflection a x) = rootReflection (w a) (w x) := by
  simp only [rootReflection, map_sub, map_smul, hw]

lemma rootReflectionEquiv_conjugate (w : E ≃ₗ[ℝ] E)
    (hw : ∀ x y, inner ℝ (w x) (w y) = inner ℝ x y) (a : E) :
    rootReflectionEquiv (w a) = w * rootReflectionEquiv a * w⁻¹ := by
  ext x
  change rootReflectionEquiv (w a) x = w (rootReflectionEquiv a (w.symm x))
  simp only [rootReflectionEquiv_apply, rootReflection_map w hw, LinearEquiv.apply_symm_apply]

theorem simpleRoots_generate : SimpleRootSpecs.generationType := by
  intro E _ _ R hR v hv
  apply le_antisymm (simpleWeylGroup_le R v)
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨w, a, ha, hw⟩ := root_simple_orbit hR hv hx
  rw [← hw, rootReflectionEquiv_conjugate w.val
    (rootWeylGroup_inner (simpleWeylGroup_le R v w.property))]
  exact (simpleWeylGroup R v).mul_mem
    ((simpleWeylGroup R v).mul_mem w.property (simple_reflection_mem ha))
    ((simpleWeylGroup R v).inv_mem w.property)

theorem simpleRoots_orbit : SimpleRootSpecs.orbitType := by
  intro E _ _ R hR v hv
  ext x
  constructor
  · intro hx
    obtain ⟨w, a, ha, hw⟩ := root_simple_orbit hR hv hx
    exact ⟨⟨w.val, simpleWeylGroup_le R v w.property⟩, a, ha, hw⟩
  · rintro ⟨w, a, ha, rfl⟩
    exact (rootWeylGroup_mem_iff hR.toRootAxioms w.property a).mp ha.1.1

end LieAlgebrasAndRepresentations
