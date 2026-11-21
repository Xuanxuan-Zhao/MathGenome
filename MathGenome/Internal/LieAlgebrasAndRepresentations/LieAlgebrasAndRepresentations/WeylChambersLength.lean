import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.WeylChambersLength
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SimpleRoots
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-! LA-E03-Length: chambers and the length formula.

Source: notes/005/lie-algebras-and-representations.tex, res:E03,
expanded lines 2085–2142. The deletion argument follows a positive root
through a word, using LA-E02's simple-reflection positivity. Inversion counting
then proves minimal word length. Connectedness fixes the signs on a chamber;
finiteness and maximization on an orbit prove transitivity without a gallery
construction. No nonempty-root or positive-rank assumption is imposed.

The closed-chamber fundamental-domain assertion is allocated to LA-E03.
-/

noncomputable section
namespace LieAlgebrasAndRepresentations
open Set Module
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

@[simp] lemma weylWordProduct_nil {R : Set E} {v : E} :
    weylWordProduct ([] : List (simpleRoots R v)) = 1 := rfl

@[simp] lemma weylWordProduct_cons {R : Set E} {v : E}
    (a : simpleRoots R v) (l : List (simpleRoots R v)) :
    weylWordProduct (a :: l) = rootReflectionEquiv (a : E) * weylWordProduct l := rfl

@[simp] lemma weylWordProduct_append {R : Set E} {v : E}
    (l k : List (simpleRoots R v)) :
    weylWordProduct (l ++ k) = weylWordProduct l * weylWordProduct k := by
  simp [weylWordProduct, List.map_append, List.prod_append]

lemma weylWordProduct_mem {R : Set E} {v : E} (l : List (simpleRoots R v)) :
    weylWordProduct l ∈ rootWeylGroup R := by
  induction l with
  | nil => exact (rootWeylGroup R).one_mem
  | cons a l ih =>
    exact (rootWeylGroup R).mul_mem
      (simpleWeylGroup_le R v (simple_reflection_mem a.property)) ih

lemma weylWordProduct_reverse {R : Set E} {v : E} (l : List (simpleRoots R v)) :
    weylWordProduct l.reverse = (weylWordProduct l)⁻¹ := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simpa only [List.reverse_cons, weylWordProduct_append, weylWordProduct_cons,
      weylWordProduct_nil, mul_one, mul_inv_rev, rootReflectionEquiv_inv] using
      (congrArg (· * rootReflectionEquiv (a : E)) ih)

lemma exists_weylWord {R : Set E} (hR : IsRootSystem R) {v : E}
    (hv : RootRegular R v) (w : rootWeylGroup R) :
    ∃ l : List (simpleRoots R v), weylWordProduct l = w.val := by
  have hw : w.val ∈ simpleWeylGroup R v := by
    rw [simpleRoots_generate R hR v hv]
    exact w.property
  generalize heq : w.val = g at hw ⊢
  clear heq
  induction hw using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, rfl⟩ := hw
    exact ⟨[⟨a, ha⟩], by simp [weylWordProduct]⟩
  | one => exact ⟨[], rfl⟩
  | mul w z hw hz ihw ihz =>
    obtain ⟨l, rfl⟩ := ihw
    obtain ⟨k, rfl⟩ := ihz
    exact ⟨l ++ k, weylWordProduct_append l k⟩
  | inv w hw ih =>
    obtain ⟨l, rfl⟩ := ih
    exact ⟨l.reverse, weylWordProduct_reverse l⟩

lemma weylWordLength_le {R : Set E} {v : E} {w : rootWeylGroup R}
    (l : List (simpleRoots R v)) (hl : weylWordProduct l = w.val) :
    weylWordLength R v w ≤ l.length :=
  csInf_le' ⟨l, rfl, hl⟩

theorem weyl_shortest_word : WeylChamberLengthSpecs.shortestWordType := by
  intro E _ _ R hR v hv w
  have hn : {n | ∃ l : List (simpleRoots R v), l.length = n ∧
      weylWordProduct l = w.val}.Nonempty := by
    obtain ⟨l, hl⟩ := exists_weylWord hR hv w
    exact ⟨l.length, l, rfl, hl⟩
  obtain ⟨l, hlen, hl⟩ := csInf_mem hn
  exact ⟨l, hl, hlen, fun k hk => hlen ▸ weylWordLength_le k hk⟩

/-- The sign-change deletion argument. A word sending a positive root negative
can be shortened by one after multiplying by that root's reflection. -/
lemma weyl_word_deletion {R : Set E} (hR : IsRootSystem R) {v : E}
    (hv : RootRegular R v) (l : List (simpleRoots R v)) {a : E}
    (ha : a ∈ positiveRoots R v)
    (hneg : inner ℝ v (weylWordProduct l a) < 0) :
    ∃ k : List (simpleRoots R v),
      weylWordProduct k = weylWordProduct l * rootReflectionEquiv a ∧
      k.length + 1 = l.length := by
  induction l with
  | nil => simpa using (not_lt_of_gt ha.2 hneg)
  | cons i l ih =>
    have hroot : weylWordProduct l a ∈ R :=
      (rootWeylGroup_mem_iff hR.toRootAxioms (weylWordProduct_mem l) a).mp ha.1
    by_cases hn : inner ℝ v (weylWordProduct l a) < 0
    · obtain ⟨k, hk, hlen⟩ := ih hn
      refine ⟨i :: k, ?_, by simpa only [List.length_cons, Nat.add_right_cancel_iff] using hlen⟩
      simp only [weylWordProduct_cons, hk, mul_assoc]
    · have hp : weylWordProduct l a ∈ positiveRoots R v :=
        ⟨hroot, lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm (hv _ hroot))⟩
      have heq : weylWordProduct l a = (i : E) := by
        by_contra hne
        have hpos := simple_reflection_positive hR hv i.property hp hne
        have hneg' : inner ℝ v (rootReflection (i : E) (weylWordProduct l a)) < 0 := by
          simpa only [weylWordProduct_cons, LinearEquiv.mul_apply, rootReflectionEquiv_apply] using hneg
        exact not_lt_of_gt hpos.2 hneg'
      refine ⟨l, ?_, by simp⟩
      have hc := rootReflectionEquiv_conjugate (weylWordProduct l)
        (rootWeylGroup_inner (weylWordProduct_mem l)) a
      rw [heq] at hc
      rw [weylWordProduct_cons, hc]
      have hi : rootReflectionEquiv a * rootReflectionEquiv a = (1 : E ≃ₗ[ℝ] E) := by
        nth_rw 1 [← rootReflectionEquiv_inv a]
        exact inv_mul_cancel _
      simp only [mul_assoc, inv_mul_cancel_left, hi, mul_one]

lemma inversionRoots_finite {R : Set E} (hR : RootAxioms R) (v : E)
    (w : E ≃ₗ[ℝ] E) : (inversionRoots R v w).Finite :=
  hR.finite.subset (fun _ h => h.1.1)

lemma inversionRoots_mul_simple {R : Set E} (hR : IsRootSystem R) {v : E}
    (hv : RootRegular R v) (u : E ≃ₗ[ℝ] E) (i : simpleRoots R v)
    (hpos : 0 < inner ℝ v (u (i : E))) :
    inversionRoots R v (u * rootReflectionEquiv (i : E)) =
      insert (i : E) (rootReflectionEquiv (i : E) '' inversionRoots R v u) := by
  ext x
  constructor
  · intro hx
    by_cases hxi : x = (i : E)
    · exact Or.inl hxi
    · right
      refine ⟨rootReflectionEquiv (i : E) x, ?_, ?_⟩
      · exact ⟨by simpa only [rootReflectionEquiv_apply] using
          simple_reflection_positive hR hv i.property hx.1 hxi, hx.2⟩
      · simp only [rootReflectionEquiv_apply, reflection_involutive]
  · rintro (rfl | ⟨y, hy, rfl⟩)
    · refine ⟨i.property.1, ?_⟩
      change inner ℝ v (u (rootReflectionEquiv (i : E) (i : E))) < 0
      rw [rootReflectionEquiv_apply, reflection_self (hR.nonzero _ i.property.1.1),
        map_neg, inner_neg_right]
      exact neg_neg_of_pos hpos
    · have hne : y ≠ (i : E) := by
        rintro rfl
        exact not_lt_of_gt hpos hy.2
      refine ⟨by simpa only [rootReflectionEquiv_apply] using
        simple_reflection_positive hR hv i.property hy.1 hne, ?_⟩
      change inner ℝ v (u (rootReflectionEquiv (i : E)
        (rootReflectionEquiv (i : E) y))) < 0
      simpa only [rootReflectionEquiv_apply, reflection_involutive] using hy.2

lemma inversionRoots_ncard_mul_simple {R : Set E} (hR : IsRootSystem R) {v : E}
    (hv : RootRegular R v) (u : E ≃ₗ[ℝ] E) (i : simpleRoots R v)
    (hpos : 0 < inner ℝ v (u (i : E))) :
    (inversionRoots R v (u * rootReflectionEquiv (i : E))).ncard =
      (inversionRoots R v u).ncard + 1 := by
  rw [inversionRoots_mul_simple hR hv u i hpos]
  have hnot : (i : E) ∉ rootReflectionEquiv (i : E) '' inversionRoots R v u := by
    rintro ⟨y, hy, heq⟩
    have heq' := congrArg (rootReflectionEquiv (i : E)) heq
    simp only [rootReflectionEquiv_apply, reflection_involutive,
      reflection_self (hR.nonzero _ i.property.1.1)] at heq'
    have hp := hy.1.2
    rw [heq', inner_neg_right] at hp
    linarith [i.property.1.2]
  rw [Set.ncard_insert_of_notMem hnot ((inversionRoots_finite hR.toRootAxioms v u).image _),
    Set.ncard_image_of_injective _ (rootReflectionEquiv (i : E)).injective]

/-- Every shortest word has as many letters as inversions. -/
lemma shortest_word_inversions {R : Set E} (hR : IsRootSystem R) {v : E}
    (hv : RootRegular R v) (l : List (simpleRoots R v))
    (hmin : ∀ k : List (simpleRoots R v), weylWordProduct k = weylWordProduct l →
      l.length ≤ k.length) :
    l.length = (inversionRoots R v (weylWordProduct l)).ncard := by
  induction l using List.reverseRecOn with
  | nil =>
    have he : inversionRoots R v (1 : E ≃ₗ[ℝ] E) = ∅ := by
      ext a
      simp only [inversionRoots, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro ha
      exact not_lt_of_gt ha.2
    simp [he]
  | append_singleton l i ih =>
    have hminl : ∀ k : List (simpleRoots R v), weylWordProduct k = weylWordProduct l →
        l.length ≤ k.length := by
      intro k hk
      have hm := hmin (k ++ [i]) (by simp [hk])
      simpa using hm
    have hroot : weylWordProduct l (i : E) ∈ R :=
      (rootWeylGroup_mem_iff hR.toRootAxioms (weylWordProduct_mem l) _).mp i.property.1.1
    have hp : 0 < inner ℝ v (weylWordProduct l (i : E)) := by
      rcases lt_or_gt_of_ne (hv _ hroot) with hn | hp
      · obtain ⟨k, hk, hlen⟩ := weyl_word_deletion hR hv l i.property.1 hn
        have hm := hmin k (by simpa [weylWordProduct] using hk)
        simp only [List.length_append, List.length_singleton] at hm
        omega
      · exact hp
    simpa only [List.length_append, List.length_singleton, weylWordProduct_append,
      weylWordProduct_cons, weylWordProduct_nil, mul_one,
      inversionRoots_ncard_mul_simple hR hv _ i hp] using congrArg (· + 1) (ih hminl)

theorem weyl_length_eq_inversions : WeylChamberLengthSpecs.lengthType := by
  intro E _ _ R hR v hv w
  obtain ⟨l, hl, hlen, hmin⟩ := weyl_shortest_word R hR v hv w
  rw [← hlen, ← hl]
  exact shortest_word_inversions hR hv l (fun k hk => hmin k (hk.trans hl))

/-- Positivity on simple roots is positivity on every positive root. -/
lemma simpleChamber_pairing_positive {R : Set E} (hR : RootAxioms R) {v x a : E}
    (hx : x ∈ simpleChamber R v) (ha : a ∈ positiveRoots R v) :
    0 < inner ℝ x a := by
  have hcone : a = 0 ∨ 0 < inner ℝ x a := by
    refine AddSubmonoid.closure_induction (fun y hy => ?_) ?_
      (fun y z hy hz ihy ihz => ?_) (positive_mem_closure_simple hR v ha)
    · exact Or.inr (hx y hy)
    · exact Or.inl rfl
    · rcases ihy with rfl | ihy
      · simpa using ihz
      rcases ihz with rfl | ihz
      · simpa using Or.inr ihy
      · exact Or.inr (by rw [inner_add_right]; exact add_pos ihy ihz)
  exact hcone.resolve_left (hR.nonzero a ha.1)

lemma simpleChamber_regular {R : Set E} (hR : RootAxioms R) {v : E}
    (hv : RootRegular R v) {x : E} (hx : x ∈ simpleChamber R v) :
    RootRegular R x := by
  intro a ha
  rcases positive_or_neg_positive hR hv ha with hp | hp
  · exact ne_of_gt (simpleChamber_pairing_positive hR hx hp)
  · have hn := simpleChamber_pairing_positive hR hx hp
    rw [inner_neg_right] at hn
    exact ne_of_lt (neg_pos.mp hn)

lemma self_mem_simpleChamber (R : Set E) (v : E) : v ∈ simpleChamber R v :=
  fun _ ha => ha.1.2

lemma simpleChamber_convex (R : Set E) (v : E) : Convex ℝ (simpleChamber R v) := by
  have he : simpleChamber R v = ⋂ a : simpleRoots R v, {x | 0 < inner ℝ (a : E) x} := by
    ext x
    simp only [simpleChamber, mem_ofPred_eq, mem_iInter, Subtype.forall, real_inner_comm]
  rw [he]
  exact convex_iInter (fun a => convex_halfSpace_gt (innerₗ E (a : E)).isLinear 0)

theorem simpleChamber_connectedComponent : WeylChamberLengthSpecs.chamberType := by
  intro E _ _ R hR v hv
  apply Subset.antisymm
  · exact (simpleChamber_convex R v).isPreconnected.subset_connectedComponentIn
      (self_mem_simpleChamber R v) (fun _ hx => simpleChamber_regular hR.toRootAxioms hv hx)
  · intro x hx a ha
    exact isPreconnected_connectedComponentIn.lt_of_ne
      ((continuous_id.inner continuous_const).continuousOn)
      (fun y hy => connectedComponentIn_subset (rootHyperplaneComplement R) v hy a ha.1.1)
      ⟨v, mem_connectedComponentIn hv, ha.1.2⟩ hx

lemma rootWeylGroup_regular {R : Set E} (hR : RootAxioms R)
    (w : rootWeylGroup R) {x : E} (hx : RootRegular R x) : RootRegular R (w.val x) := by
  intro a ha
  have har : w.val.symm a ∈ R :=
    (rootWeylGroup_mem_iff hR ((rootWeylGroup R).inv_mem w.property) a).mp ha
  have hi := rootWeylGroup_inner w.property x (w.val.symm a)
  rw [LinearEquiv.apply_symm_apply] at hi
  rw [hi]
  exact hx _ har

lemma rootWeylGroup_image_complement {R : Set E} (hR : RootAxioms R)
    (w : rootWeylGroup R) : w.val '' rootHyperplaneComplement R = rootHyperplaneComplement R := by
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact rootWeylGroup_regular hR w hx
  · intro x hx
    refine ⟨w.val.symm x, rootWeylGroup_regular hR w⁻¹ hx, ?_⟩
    exact w.val.apply_symm_apply x

lemma rootWeylGroup_image_component {R : Set E} (hR : RootAxioms R)
    (w : rootWeylGroup R) {x : E} (hx : RootRegular R x) :
    w.val '' connectedComponentIn (rootHyperplaneComplement R) x =
      connectedComponentIn (rootHyperplaneComplement R) (w.val x) := by
  let f := (w.val.isometryOfInner (rootWeylGroup_inner w.property)).toHomeomorph
  have he := f.image_connectedComponentIn (s := rootHyperplaneComplement R) hx
  change w.val '' connectedComponentIn (rootHyperplaneComplement R) x =
    connectedComponentIn (w.val '' rootHyperplaneComplement R) (w.val x) at he
  rwa [rootWeylGroup_image_complement hR w] at he

theorem weyl_chamber_action : WeylChamberLengthSpecs.actionType := by
  intro E _ _ R hR w C hC
  obtain ⟨x, hx, rfl⟩ := hC
  exact ⟨w.val x, rootWeylGroup_regular hR.toRootAxioms w hx,
    rootWeylGroup_image_component hR.toRootAxioms w hx⟩

/-- A Weyl element is determined by its action on the finite spanning root set. -/
lemma rootWeylGroup_finite {R : Set E} (hR : IsRootSystem R) : Finite (rootWeylGroup R) := by
  haveI : Finite R := hR.finite.to_subtype
  let f : rootWeylGroup R → (R → R) := fun w a =>
    ⟨w.val a, (rootWeylGroup_mem_iff hR.toRootAxioms w.property a).mp a.property⟩
  apply Finite.of_injective f
  intro w z he
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.ext_on hR.span_eq_top
  intro a ha
  exact congrArg Subtype.val (congrFun he ⟨a, ha⟩)

/-- Maximizing `(v,wx)` on the finite orbit puts every regular vector in the
specified positive chamber. This avoids any generic-path assumption. -/
lemma exists_weyl_into_simpleChamber {R : Set E} (hR : IsRootSystem R) {v : E}
    (_hv : RootRegular R v) {x : E} (hx : RootRegular R x) :
    ∃ w : rootWeylGroup R, w.val x ∈ simpleChamber R v := by
  haveI := rootWeylGroup_finite hR
  obtain ⟨w, hw⟩ := (Set.finite_univ : (Set.univ : Set (rootWeylGroup R)).Finite).exists_maximalFor
    (fun w : rootWeylGroup R => inner ℝ v (w.val x)) Set.univ ⟨1, trivial⟩
  refine ⟨w, ?_⟩
  intro a ha
  have hne := rootWeylGroup_regular hR.toRootAxioms w hx a ha.1.1
  rcases lt_or_gt_of_ne hne with hn | hp
  · let s : rootWeylGroup R :=
      ⟨rootReflectionEquiv a, simpleWeylGroup_le R v (simple_reflection_mem ha)⟩
    have hcart : 2 * inner ℝ (w.val x) a / inner ℝ a a < 0 :=
      div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg two_pos hn)
        (real_inner_self_pos.mpr (hR.nonzero a ha.1.1))
    have hlt : inner ℝ v (w.val x) < inner ℝ v ((s * w).val x) := by
      change inner ℝ v (w.val x) < inner ℝ v (rootReflectionEquiv a (w.val x))
      rw [rootReflectionEquiv_apply, rootReflection, inner_sub_right, real_inner_smul_right]
      linarith [mul_neg_of_neg_of_pos hcart ha.1.2]
    have hle := hw.2 (show s * w ∈ (Set.univ : Set (rootWeylGroup R)) from trivial) hlt.le
    exact False.elim (not_le_of_gt hlt hle)
  · exact hp

@[simp] lemma weyl_image_mul {R : Set E} (w z : rootWeylGroup R) (C : Set E) :
    (w * z).val '' C = w.val '' (z.val '' C) := by
  rw [image_image]
  rfl

@[simp] lemma weyl_image_one (R : Set E) (C : Set E) :
    (1 : rootWeylGroup R).val '' C = C := image_id _

lemma exists_weyl_chamber_to_simple {R : Set E} (hR : IsRootSystem R) {v : E}
    (hv : RootRegular R v) {C : Set E} (hC : IsWeylChamber R C) :
    ∃ w : rootWeylGroup R, w.val '' C = simpleChamber R v := by
  obtain ⟨x, hx, rfl⟩ := hC
  obtain ⟨w, hw⟩ := exists_weyl_into_simpleChamber hR hv hx
  have hc := connectedComponentIn_eq
    (show w.val x ∈ connectedComponentIn (rootHyperplaneComplement R) v from
      (simpleChamber_connectedComponent R hR v hv) ▸ hw)
  exact ⟨w, (rootWeylGroup_image_component hR.toRootAxioms w hx).trans
    (hc.symm.trans (simpleChamber_connectedComponent R hR v hv).symm)⟩

lemma weyl_simpleChamber_stabilizer {R : Set E} (hR : IsRootSystem R) {v : E}
    (hv : RootRegular R v) (w : rootWeylGroup R)
    (hw : w.val '' simpleChamber R v = simpleChamber R v) : w = 1 := by
  have hvimage : v ∈ w.val '' simpleChamber R v := by
    rw [hw]
    exact self_mem_simpleChamber R v
  obtain ⟨x, hx, hwx⟩ := hvimage
  have hinv : inversionRoots R v w.val = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro a ha
    have hp := simpleChamber_pairing_positive hR.toRootAxioms hx ha.1
    have hi := rootWeylGroup_inner w.property x a
    rw [hwx] at hi
    exact not_lt_of_gt hp (hi ▸ ha.2)
  have hlen : weylWordLength R v w = 0 := by
    rw [weyl_length_eq_inversions R hR v hv w, hinv, ncard_empty]
  obtain ⟨l, hl, hlength, _⟩ := weyl_shortest_word R hR v hv w
  have hnil : l = [] := List.length_eq_zero_iff.mp (hlength.trans hlen)
  apply Subtype.ext
  simpa [hnil] using hl.symm

lemma weyl_chamber_stabilizer {R : Set E} (hR : IsRootSystem R) {v : E}
    (hv : RootRegular R v) {C : Set E} (hC : IsWeylChamber R C)
    (w : rootWeylGroup R) (hw : w.val '' C = C) : w = 1 := by
  obtain ⟨z, hz⟩ := exists_weyl_chamber_to_simple hR hv hC
  have hzi : z⁻¹.val '' simpleChamber R v = C := by
    rw [← hz, ← weyl_image_mul, inv_mul_cancel, weyl_image_one]
  have hconj : (z * w * z⁻¹).val '' simpleChamber R v = simpleChamber R v := by
    rw [weyl_image_mul, hzi, weyl_image_mul, hw, hz]
  have he := weyl_simpleChamber_stabilizer hR hv (z * w * z⁻¹) hconj
  have he' := congrArg (fun u => z⁻¹ * u * z) he
  simpa [mul_assoc] using he'

theorem weyl_chambers_simply_transitive : WeylChamberLengthSpecs.simplyTransitiveType := by
  intro E _ _ R hR v hv C D hC hD
  obtain ⟨c, hc⟩ := exists_weyl_chamber_to_simple hR hv hC
  obtain ⟨d, hd⟩ := exists_weyl_chamber_to_simple hR hv hD
  have hdi : d⁻¹.val '' simpleChamber R v = D := by
    rw [← hd, ← weyl_image_mul, inv_mul_cancel, weyl_image_one]
  refine ⟨d⁻¹ * c, ?_, ?_⟩
  · change (d⁻¹ * c).val '' C = D
    rw [weyl_image_mul, hc, hdi]
  · intro w hw
    have he : ((d⁻¹ * c)⁻¹ * w).val '' C = C := by
      rw [weyl_image_mul, hw, ← hdi, ← weyl_image_mul]
      simp only [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel, mul_one]
      rw [← hc, ← weyl_image_mul, inv_mul_cancel, weyl_image_one]
    have hst := weyl_chamber_stabilizer hR hv hC _ he
    exact (inv_mul_eq_one.mp hst).symm

end LieAlgebrasAndRepresentations
