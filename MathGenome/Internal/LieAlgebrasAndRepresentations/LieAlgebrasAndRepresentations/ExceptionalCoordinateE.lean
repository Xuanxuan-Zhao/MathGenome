import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ExceptionalCoordinateE
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ExceptionalCoordinateGF
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ClassicalCoordinateRoots

/-! Exact coordinate calculations for the E-series in res:E06.
The lattice, bounded coordinate certificates, and real Euclidean bridges
are proved independently of the root-system axioms they establish. -/
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace LieAlgebrasAndRepresentations.ExceptionalE
open Set Module
open ExceptionalGF (QVec Space unit sign realize dot)

lemma integral_list_card : integralList.card = 112 := by decide +kernel
lemma half_list_card : halfList.card = 128 := by decide +kernel
lemma e8_list_card : e8List.card = 240 := by decide +kernel
lemma parts_disjoint : Disjoint integralList halfList := by decide +kernel

lemma e7_list_cards : e7List.card = 126 ∧
    (e7List ∩ integralList).card = 62 ∧
    ((e7List ∩ integralList).filter (fun x => x 6 = 0 ∧ x 7 = 0)).card = 60 ∧
    ((e7List ∩ integralList).filter (fun x => x 6 ≠ 0 ∨ x 7 ≠ 0)).card = 2 ∧
    (e7List ∩ halfList).card = 64 := by decide +kernel

lemma e6_list_cards : e6List.card = 72 ∧
    (e6List ∩ integralList).card = 40 ∧
    (e6List ∩ halfList).card = 32 := by decide +kernel

theorem e8_count : Specs.e8Count := by
  unfold Specs.e8Count e8Roots
  simp only [ExceptionalGF.realize_ncard]
  exact ⟨e8_list_card, integral_list_card, half_list_card, parts_disjoint⟩

lemma e7_ambient_eq : e7AmbientRoots = e8Roots ∩ (e7Space : Set (Space 8)) := by
  ext x
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨hq, he⟩ := Finset.mem_filter.mp hq
    refine ⟨⟨q, hq, rfl⟩, ?_⟩
    change (q 6 : ℝ) + (q 7 : ℝ) = 0
    exact_mod_cast he
  · rintro ⟨⟨q, hq, rfl⟩, hx⟩
    refine ⟨q, Finset.mem_filter.mpr ⟨hq, ?_⟩, rfl⟩
    change (q 6 : ℝ) + (q 7 : ℝ) = 0 at hx
    exact_mod_cast hx

lemma e6_ambient_eq : e6AmbientRoots = e8Roots ∩ (e6Space : Set (Space 8)) := by
  ext x
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨hq, he⟩ := Finset.mem_filter.mp hq
    obtain ⟨hq, he'⟩ := Finset.mem_filter.mp hq
    refine ⟨⟨q, hq, rfl⟩, ?_, ?_⟩
    · change (q 6 : ℝ) + (q 7 : ℝ) = 0
      exact_mod_cast he'
    · change (q 5 : ℝ) = (q 6 : ℝ)
      exact_mod_cast he
  · rintro ⟨⟨q, hq, rfl⟩, hx⟩
    refine ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hq, ?_⟩, ?_⟩, rfl⟩
    · have h : (q 6 : ℝ) + (q 7 : ℝ) = 0 := hx.1
      exact_mod_cast h
    · have h : (q 5 : ℝ) = (q 6 : ℝ) := hx.2
      exact_mod_cast h

lemma e7_roots_image : (Subtype.val : e7Space → Space 8) '' e7Roots = e7AmbientRoots := by
  rw [e7_ambient_eq]
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨ha, a.property⟩
  · rintro ⟨hx, hs⟩
    exact ⟨⟨x, hs⟩, hx, rfl⟩

lemma e6_roots_image : (Subtype.val : e6Space → Space 8) '' e6Roots = e6AmbientRoots := by
  rw [e6_ambient_eq]
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨ha, a.property⟩
  · rintro ⟨hx, hs⟩
    exact ⟨⟨x, hs⟩, hx, rfl⟩

theorem e7_count : Specs.e7Count := by
  refine ⟨?_, e7_list_cards.2⟩
  change e7Roots.ncard = 126
  rw [← Set.ncard_image_of_injective e7Roots Subtype.val_injective, e7_roots_image]
  exact (ExceptionalGF.realize_ncard e7List).trans e7_list_cards.1

theorem e6_count : Specs.e6Count := by
  refine ⟨?_, e6_list_cards.2⟩
  change e6Roots.ncard = 72
  rw [← Set.ncard_image_of_injective e6Roots Subtype.val_injective, e6_roots_image]
  exact (ExceptionalGF.realize_ncard e6List).trans e6_list_cards.1

lemma simple_gram_q : ∀ i j : Fin 8, dot (simpleQ i) (simpleQ j) =
    if i = j then 2 else if adjacent i j then -1 else 0 := by decide +kernel

lemma adjacent_irrefl : ∀ i : Fin 8, ¬ adjacent i i := by decide +kernel
lemma adjacent_symm : ∀ i j : Fin 8, adjacent i j ↔ adjacent j i := by decide +kernel

lemma simple_gram (i j : Fin 8) : inner ℝ (e8Simple i) (e8Simple j) =
    if i = j then 2 else if adjacent i j then -1 else 0 := by
  rw [e8Simple, e8Simple, ExceptionalGF.realize_inner, simple_gram_q]
  split_ifs <;> norm_num

@[simp] lemma simple_norm (i : Fin 8) : inner ℝ (e8Simple i) (e8Simple i) = 2 := by
  rw [simple_gram]; exact if_pos rfl

lemma simple_cartan (i j : Fin 8) : cartanMatrix e8Simple i j =
    if i = j then 2 else if adjacent i j then -1 else 0 := by
  unfold cartanMatrix rootCartan
  rw [simple_norm, simple_gram]
  by_cases he : i = j
  · subst j; norm_num
  · rw [if_neg (Ne.symm he), if_neg he]
    simp only [← adjacent_symm j i]
    split_ifs <;> norm_num

theorem e8_diagram : Specs.e8Diagram := by
  refine ⟨simple_cartan, ?_, ?_⟩
  · intro i j
    by_cases he : i = j
    · subst j; simp [dynkinDiagram, adjacent_irrefl]
    · simp only [dynkinDiagram, if_neg he, simple_cartan, if_neg (Ne.symm he)]
      simp only [← adjacent_symm j i]
      split_ifs <;> norm_num
  · intro i j
    simp only [dynkinDiagram, simple_norm, lt_self_iff_false, and_false, not_false_eq_true]

lemma e7_cartan (i j : Fin 7) : cartanMatrix e7Simple i j =
    cartanMatrix e8Simple i.castSucc j.castSucc := rfl

lemma e6_cartan (i j : Fin 6) : cartanMatrix e6Simple i j =
    cartanMatrix e8Simple (i.castLE (by decide)) (j.castLE (by decide)) := rfl

theorem e7_diagram : Specs.e7Diagram := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    rw [e7_cartan, simple_cartan]
    simp
  · intro i j
    have h := e8_diagram.2.1 i.castSucc j.castSucc
    by_cases he : i = j
    · subst j; simp [dynkinDiagram, adjacent_irrefl]
    · simpa only [dynkinDiagram, e7_cartan, if_neg he, if_neg (show i.castSucc ≠ j.castSucc from fun hh => he (Fin.castSucc_inj.mp hh))] using h
  · intro i j
    have h := e8_diagram.2.2 i.castSucc j.castSucc
    change ¬ (i ≠ j ∧ _ ∧ _)
    rintro ⟨hne, hi, hn⟩
    exact h ⟨(fun he => hne (Fin.castSucc_inj.mp he)), hi, hn⟩

theorem e6_diagram : Specs.e6Diagram := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    rw [e6_cartan, simple_cartan]
    simp
  · intro i j
    have h := e8_diagram.2.1 (i.castLE (by decide)) (j.castLE (by decide))
    by_cases he : i = j
    · subst j; simp [dynkinDiagram, adjacent_irrefl]
    · simpa only [dynkinDiagram, e6_cartan, if_neg he, if_neg (show i.castLE (by decide : 6 ≤ 8) ≠ j.castLE (by decide : 6 ≤ 8) from fun hh => he (Fin.castLE_inj.mp hh))] using h
  · intro i j
    have h := e8_diagram.2.2 (i.castLE (by decide)) (j.castLE (by decide))
    change ¬ (i ≠ j ∧ _ ∧ _)
    rintro ⟨hne, hi, hn⟩
    exact h ⟨(fun he => hne (Fin.castLE_inj.mp he)), hi, hn⟩

lemma e8_list_norm : ∀ q ∈ e8List, dot q q = 2 := by decide +kernel

lemma e8_root_norm {x : Space 8} (hx : x ∈ e8Roots) : inner ℝ x x = 2 := by
  obtain ⟨q, hq, rfl⟩ := hx
  rw [ExceptionalGF.realize_inner, e8_list_norm q hq]
  norm_num

lemma simple_mem_q : ∀ i : Fin 8, simpleQ i ∈ e8List := by decide +kernel

lemma simple_mem (i : Fin 8) : e8Simple i ∈ e8Roots :=
  ⟨simpleQ i, simple_mem_q i, rfl⟩

lemma e8_separated_q : ∀ q ∈ e8List,
    dot ![0,1,2,3,4,5,6,23] q ≤ -1 ∨ 1 ≤ dot ![0,1,2,3,4,5,6,23] q := by
  decide +kernel

lemma e8_separated : ∀ x ∈ e8Roots,
    inner ℝ e8Regular x ≤ -1 ∨ 1 ≤ inner ℝ e8Regular x := by
  rintro _ ⟨q, hq, rfl⟩
  rw [e8Regular, ExceptionalGF.realize_inner]
  rcases e8_separated_q q hq with h | h
  · left; exact_mod_cast h
  · right; exact_mod_cast h

lemma e8_regular : RootRegular e8Roots e8Regular :=
  ClassicalCoordinates.regular_of_separated e8_separated

lemma simple_height : ∀ i : Fin 8, inner ℝ e8Regular (e8Simple i) = 1 := by
  intro i
  fin_cases i <;> norm_num [e8Regular, e8Simple, ExceptionalGF.realize_inner,
    simpleQ, dot, Fin.sum_univ_succ]

lemma e8_simple_mem (i : Fin 8) : e8Simple i ∈ simpleRoots e8Roots e8Regular :=
  ClassicalCoordinates.simple_of_height_one e8_separated (simple_mem i) (simple_height i)

def coordinates (x : Space 8) : Fin 8 → ℝ :=
  ![2*x 7, (x 0+x 1+x 2+x 3+x 4+x 5+x 6+5*x 7)/2,
    (-x 0+x 1+x 2+x 3+x 4+x 5+x 6+7*x 7)/2,
    x 2+x 3+x 4+x 5+x 6+5*x 7,
    x 3+x 4+x 5+x 6+4*x 7,
    x 4+x 5+x 6+3*x 7, x 5+x 6+2*x 7, x 6+x 7]

lemma coordinate_expansion (x : Space 8) : x = ∑ i, coordinates x i • e8Simple i := by
  ext j
  fin_cases j <;>
    simp [coordinates, e8Simple, simpleQ, realize, Fin.sum_univ_succ] <;> ring

lemma simple_span : Submodule.span ℝ (Set.range e8Simple) = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro x
  rw [coordinate_expansion x]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _
    (Submodule.subset_span (Set.mem_range_self i)))

lemma e7_simple_span : Submodule.span ℝ (Set.range e7Simple) = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro x
  have hx : (x : Space 8) 6 + (x : Space 8) 7 = 0 := x.property
  have he : x = ∑ i : Fin 7, coordinates x.val i.castSucc • e7Simple i := by
    apply Subtype.ext
    ext j
    fin_cases j <;>
      simp [coordinates, e7Simple, e8Simple, simpleQ, realize, Fin.sum_univ_succ] <;>
      linarith
  rw [he]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _
    (Submodule.subset_span (Set.mem_range_self i)))

lemma e6_simple_span : Submodule.span ℝ (Set.range e6Simple) = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro x
  have hx : (x : Space 8) 6 + (x : Space 8) 7 = 0 ∧ (x : Space 8) 5 = (x : Space 8) 6 := x.property
  have he : x = ∑ i : Fin 6, coordinates x.val (i.castLE (by decide)) • e6Simple i := by
    apply Subtype.ext
    ext j
    fin_cases j <;>
      simp [coordinates, e6Simple, e8Simple, simpleQ, realize, Fin.sum_univ_succ] <;>
      linarith [hx.1, hx.2]
  rw [he]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _
    (Submodule.subset_span (Set.mem_range_self i)))

lemma lattice_zero : (0 : Space 8) ∈ lattice := by
  left
  exact ⟨0, by simp, by simp⟩
lemma lattice_add {x y : Space 8} (hx : x ∈ lattice) (hy : y ∈ lattice) : x+y ∈ lattice := by
  rcases hx with ⟨z, hz, hx⟩ | ⟨z, hz, hx⟩ <;>
    rcases hy with ⟨w, hw, hy⟩ | ⟨w, hw, hy⟩
  · left
    refine ⟨z+w, ?_, ?_⟩
    · simpa [Finset.sum_add_distrib] using hz.add hw
    · intro i; simp [hx i, hy i]
  · right
    refine ⟨z+w, ?_, ?_⟩
    · simpa [Finset.sum_add_distrib] using hz.add hw
    · intro i; simp [hx i, hy i]; ring
  · right
    refine ⟨z+w, ?_, ?_⟩
    · simpa [Finset.sum_add_distrib] using hz.add hw
    · intro i; simp [hx i, hy i]; ring
  · left
    refine ⟨fun i => z i+w i+1, ?_, ?_⟩
    · simpa [Finset.sum_add_distrib] using (hz.add hw).add (show Even (8 : ℤ) by decide)
    · intro i; simp [hx i, hy i]; ring
lemma lattice_neg {x : Space 8} (hx : x ∈ lattice) : -x ∈ lattice := by
  rcases hx with ⟨z, hz, hx⟩ | ⟨z, hz, hx⟩
  · left
    refine ⟨-z, ?_, ?_⟩
    · simpa using hz.neg
    · intro i; simp [hx i]
  · right
    refine ⟨fun i => -z i-1, ?_, ?_⟩
    · simpa [Finset.sum_sub_distrib] using hz.neg.sub (show Even (8 : ℤ) by decide)
    · intro i; simp [hx i]; ring

def latticeGroup : AddSubgroup (Space 8) where
  carrier := lattice
  zero_mem' := lattice_zero
  add_mem' := lattice_add
  neg_mem' := lattice_neg

lemma e8_span : Submodule.span ℝ e8Roots = ⊤ := by
  apply top_unique
  rw [← simple_span]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  exact simple_mem i

/-- Assembly from the lattice and norm-2 theorems proved below. -/
lemma e8_rootSystem_of_lattice (hL : Specs.latticeType) (hN : Specs.normTwoType) :
    IsRootSystem e8Roots := by
  have hl {x : Space 8} (hx : x ∈ e8Roots) : x ∈ lattice :=
    ((Set.ext_iff.mp hN x).mpr hx).1
  refine { finite := e8List.finite_toSet.image _
           nonzero := ?_
           reflection_mem := ?_
           integral := ?_
           reduced := ?_
           span_eq_top := e8_span }
  · intro a ha hz
    have hn := e8_root_norm ha
    rw [hz] at hn
    norm_num at hn
  · intro a ha b hb
    apply (Set.ext_iff.mp hN _).mp
    refine ⟨?_, ?_⟩
    · obtain ⟨z, hz⟩ := hL.2.2.2.2.2.1 b (hl hb) a (hl ha)
      have he : rootReflection a b = b - z • a := by
        rw [rootReflection, e8_root_norm ha, hz]
        norm_num [Int.cast_smul_eq_zsmul]
      rw [he]
      exact latticeGroup.sub_mem (hl hb) (latticeGroup.zsmul_mem (hl ha) z)
    · rw [reflection_inner, e8_root_norm hb]
  · intro a ha b hb
    obtain ⟨z, hz⟩ := hL.2.2.2.2.2.1 b (hl hb) a (hl ha)
    exact ⟨z, by rw [e8_root_norm ha, hz]; ring⟩
  · intro a ha b hb hba
    exact ClassicalCoordinates.equal_norm_reduced (by norm_num) (e8_root_norm ha)
      (e8_root_norm hb) hba

lemma e8_basis_of_rootSystem (hR : IsRootSystem e8Roots) : Specs.e8Basis :=
  ⟨e8_regular, ClassicalCoordinates.simple_basis_of_span e8Roots hR e8Regular e8_regular
    e8Simple e8_simple_mem simple_span⟩

lemma rootAxioms_subspace {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {R : Set E} (hR : RootAxioms R) (V : Submodule ℝ E) :
    RootAxioms {x : V | (x : E) ∈ R} where
  finite := hR.finite.preimage Subtype.val_injective.injOn
  nonzero := by
    intro a ha he
    apply hR.nonzero a ha
    exact congrArg Subtype.val he
  reflection_mem := by
    intro a ha b hb
    exact hR.reflection_mem a ha b hb
  integral := by
    intro a ha b hb
    exact hR.integral a ha b hb
  reduced := by
    intro a ha b hb hba
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hba
    have ht' : t • (a : E) = b := congrArg Subtype.val ht
    rcases hR.reduced a ha b hb (Submodule.mem_span_singleton.mpr ⟨t, ht'⟩) with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)

lemma e7_simple_mem_root (i : Fin 7) : e7Simple i ∈ e7Roots := simple_mem i.castSucc
lemma e6_simple_mem_root (i : Fin 6) : e6Simple i ∈ e6Roots := simple_mem (i.castLE (by decide))

lemma e7_rootSystem_of_e8 (hR : IsRootSystem e8Roots) : IsRootSystem e7Roots := by
  refine ⟨rootAxioms_subspace hR.toRootAxioms e7Space, ?_⟩
  apply top_unique
  rw [← e7_simple_span]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  exact e7_simple_mem_root i

lemma e6_rootSystem_of_e8 (hR : IsRootSystem e8Roots) : IsRootSystem e6Roots := by
  refine ⟨rootAxioms_subspace hR.toRootAxioms e6Space, ?_⟩
  apply top_unique
  rw [← e6_simple_span]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  exact e6_simple_mem_root i

lemma e7_height (x : e7Space) : inner ℝ e7Regular x = inner ℝ e8Regular (x : Space 8) := by
  have hx : (x : Space 8) 6 + (x : Space 8) 7 = 0 := x.property
  simp [e7Regular, e8Regular, PiLp.inner_apply, Fin.sum_univ_succ,
    RCLike.inner_apply, realize, Submodule.coe_inner]
  linarith

lemma e6_height (x : e6Space) : inner ℝ e6Regular x = inner ℝ e8Regular (x : Space 8) := by
  have hx : (x : Space 8) 6 + (x : Space 8) 7 = 0 ∧ (x : Space 8) 5 = (x : Space 8) 6 := x.property
  simp [e6Regular, e8Regular, PiLp.inner_apply, Fin.sum_univ_succ,
    RCLike.inner_apply, realize, Submodule.coe_inner]
  linarith [hx.1, hx.2]

lemma e7_separated : ∀ x ∈ e7Roots, inner ℝ e7Regular x ≤ -1 ∨ 1 ≤ inner ℝ e7Regular x := by
  intro x hx
  rw [e7_height]
  exact e8_separated x hx

lemma e6_separated : ∀ x ∈ e6Roots, inner ℝ e6Regular x ≤ -1 ∨ 1 ≤ inner ℝ e6Regular x := by
  intro x hx
  rw [e6_height]
  exact e8_separated x hx

lemma e7_regular : RootRegular e7Roots e7Regular :=
  ClassicalCoordinates.regular_of_separated e7_separated
lemma e6_regular : RootRegular e6Roots e6Regular :=
  ClassicalCoordinates.regular_of_separated e6_separated

lemma e7_simple_mem (i : Fin 7) : e7Simple i ∈ simpleRoots e7Roots e7Regular :=
  ClassicalCoordinates.simple_of_height_one e7_separated (e7_simple_mem_root i)
    ((e7_height (e7Simple i)).trans (simple_height i.castSucc))
lemma e6_simple_mem (i : Fin 6) : e6Simple i ∈ simpleRoots e6Roots e6Regular :=
  ClassicalCoordinates.simple_of_height_one e6_separated (e6_simple_mem_root i)
    ((e6_height (e6Simple i)).trans (simple_height (i.castLE (by decide))))

lemma e8_simple_injective : Function.Injective e8Simple := by
  intro i j he
  have hq := ExceptionalGF.realize_injective he
  have hi : Function.Injective simpleQ := by decide +kernel
  exact hi hq

lemma e7_simple_injective : Function.Injective e7Simple := by
  intro i j he
  have hi := e8_simple_injective (congrArg Subtype.val he)
  exact Fin.castSucc_inj.mp hi

lemma e6_simple_injective : Function.Injective e6Simple := by
  intro i j he
  have hi := e8_simple_injective (congrArg Subtype.val he)
  exact Fin.castLE_inj.mp hi

lemma simple_basis_spanning {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} {R : Set E} {v : E} (hR : IsRootSystem R) (hv : RootRegular R v)
    (s : Fin n → E) (hinj : Function.Injective s)
    (hs : ∀ i, s i ∈ simpleRoots R v)
    (hspan : Submodule.span ℝ (range s) = ⊤) :
    ∃ b : Basis (Fin n) ℝ E, (∀ i, b i = s i) ∧ IsSimpleBasis R v b := by
  obtain ⟨c, hc⟩ := simpleRoots_basis R hR v hv
  have hcrange : range c = simpleRoots R v := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩; rw [hc a]; exact a.property
    · intro hx; exact ⟨⟨x, hx⟩, hc ⟨x, hx⟩⟩
  have hli : LinearIndepOn ℝ id (simpleRoots R v) := by
    rw [← hcrange]
    exact c.linearIndependent.linearIndepOn_id
  have hsub : range s ⊆ simpleRoots R v := by rintro _ ⟨i, rfl⟩; exact hs i
  have heq : range s = simpleRoots R v := by
    apply Eq.symm
    apply eq_of_linearIndepOn_id_of_span_subtype hli hsub
    rw [hspan]
    exact Set.subset_univ _
  exact ExceptionalGF.simple_family_basis hR hv s hinj heq

lemma e7_basis_of_rootSystem (hR : IsRootSystem e7Roots) : Specs.e7Basis :=
  ⟨e7_regular, simple_basis_spanning hR e7_regular e7Simple e7_simple_injective
    e7_simple_mem e7_simple_span⟩
lemma e6_basis_of_rootSystem (hR : IsRootSystem e6Roots) : Specs.e6Basis :=
  ⟨e6_regular, simple_basis_spanning hR e6_regular e6Simple e6_simple_injective
    e6_simple_mem e6_simple_span⟩

/-- An integer norm-2 vector has coordinates in `{-1,0,1}`. This finite
certificate checks precisely the resulting bounded problem. -/
lemma integer_grid_certificate : ∀ c : Fin 8 → Fin 3,
    (∑ i, ((c i).val - (1 : ℤ)) ^ 2) = 2 →
    (fun i => ((c i).val : ℚ) - 1) ∈ e8List := by decide +kernel
/-- A shifted integer norm-2 vector has integer parts in `{-1,0}`; the
even-sum condition selects exactly the allowed half roots. -/
lemma half_grid_certificate : ∀ c : Fin 8 → Fin 2,
    Even (∑ i, ((c i).val - (1 : ℤ))) →
    (fun i => ((c i).val : ℚ) - 1 + 1/2) ∈ e8List := by decide +kernel
lemma list_lattice_certificate : ∀ q ∈ e8List,
    (Even (∑ i, (⌊q i⌋ : ℤ)) ∧ ∀ i, q i = (⌊q i⌋ : ℤ)) ∨
    (Even (∑ i, (⌊q i⌋ : ℤ)) ∧ ∀ i, q i = (⌊q i⌋ : ℤ) + 1/2) := by
  decide +kernel

lemma inner_coordinates (x y : Space 8) : inner ℝ x y = ∑ i, x i*y i := by
  simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]
lemma lattice_integral {x y : Space 8} (hx : x ∈ lattice) (hy : y ∈ lattice) :
    ∃ z : ℤ, inner ℝ x y = (z : ℝ) := by
  rcases hx with ⟨z, ⟨k, hk⟩, hx⟩ | ⟨z, ⟨k, hk⟩, hx⟩ <;>
    rcases hy with ⟨w, ⟨l, hl⟩, hy⟩ | ⟨w, ⟨l, hl⟩, hy⟩
  · exact ⟨∑ i, z i*w i, by simp [inner_coordinates, hx, hy]⟩
  · refine ⟨(∑ i, z i*w i)+k, ?_⟩
    have hk' : (∑ i, (z i : ℝ)) = (k : ℝ)+(k : ℝ) := by exact_mod_cast hk
    simp [inner_coordinates, hx, hy, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
    linarith
  · refine ⟨(∑ i, z i*w i)+l, ?_⟩
    have hl' : (∑ i, (w i : ℝ)) = (l : ℝ)+(l : ℝ) := by exact_mod_cast hl
    simp [inner_coordinates, hx, hy, add_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
    linarith
  · refine ⟨(∑ i, z i*w i)+k+l+2, ?_⟩
    have hk' : (∑ i, (z i : ℝ)) = (k : ℝ)+(k : ℝ) := by exact_mod_cast hk
    have hl' : (∑ i, (w i : ℝ)) = (l : ℝ)+(l : ℝ) := by exact_mod_cast hl
    simp [inner_coordinates, hx, hy, add_mul, mul_add, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.sum_mul]
    linarith
lemma lattice_even {x : Space 8} (hx : x ∈ lattice) :
    ∃ z : ℤ, inner ℝ x x = 2 * (z : ℝ) := by
  rcases hx with ⟨z, hz, hx⟩ | ⟨z, hz, hx⟩
  · have he : Even (∑ i, z i*(z i-1)) := Finset.even_sum _ (fun i _ => Int.even_mul_pred_self (z i))
    have he' : Even (∑ i, z i*z i) := by
      convert he.add hz using 1
      rw [← Finset.sum_add_distrib]
      congr 1
      funext i
      ring
    obtain ⟨k, hk⟩ := he'
    refine ⟨k, ?_⟩
    have hk' : (∑ i, (z i : ℝ)*(z i : ℝ)) = (k : ℝ)+(k : ℝ) := by exact_mod_cast hk
    rw [inner_coordinates]
    simp [hx]
    linarith
  · have he : Even (∑ i, z i*(z i+1)) := Finset.even_sum _ (fun i _ => Int.even_mul_succ_self (z i))
    obtain ⟨k, hk⟩ := he
    refine ⟨k+1, ?_⟩
    have hk' : (∑ i, (z i : ℝ)*((z i : ℝ)+1)) = (k : ℝ)+(k : ℝ) := by exact_mod_cast hk
    simp only [mul_add, mul_one, Finset.sum_add_distrib] at hk'
    rw [inner_coordinates]
    simp [hx, add_mul, mul_add, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.sum_mul]
    linarith
lemma lattice_discrete : DiscreteTopology lattice := by
  apply discreteTopology_iff_isOpen_singleton.mpr
  intro x
  have he : Metric.ball x 1 = {x} := by
    ext y
    constructor
    · intro hy
      apply Set.mem_singleton_iff.mpr
      by_contra hne
      have hne' : (y : Space 8) - (x : Space 8) ≠ 0 := by
        intro he
        exact hne (Subtype.ext (sub_eq_zero.mp he))
      have hl : (y : Space 8) - (x : Space 8) ∈ lattice :=
        latticeGroup.sub_mem y.property x.property
      obtain ⟨z, hz⟩ := lattice_even hl
      have hp : 0 < inner ℝ ((y : Space 8)-(x : Space 8)) ((y : Space 8)-(x : Space 8)) :=
        real_inner_self_pos.mpr hne'
      have hzpos : (0 : ℝ) < (z : ℝ) := by nlinarith
      have hzpos' : (0 : ℤ) < z := by exact_mod_cast hzpos
      have hone : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast (show (1 : ℤ) ≤ z by omega)
      change dist (y : Space 8) (x : Space 8) < 1 at hy
      rw [dist_eq_norm] at hy
      rw [real_inner_self_eq_norm_sq] at hz
      have hn := norm_nonneg ((y : Space 8)-(x : Space 8))
      nlinarith
    · rintro rfl
      simp
  rw [← he]
  exact Metric.isOpen_ball
lemma coord_sq_le_two {x : Space 8} (hx : inner ℝ x x = 2) (i : Fin 8) : x i ^ 2 ≤ 2 := by
  have hs : (∑ i, x i ^ 2) = 2 := by
    rw [← hx, PiLp.inner_apply]
    simp [RCLike.inner_apply, pow_two]
  rw [← hs]
  exact Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)

lemma integer_bounds {x : Space 8} (hn : inner ℝ x x = 2)
    {z : Fin 8 → ℤ} (hz : ∀ i, x i = (z i : ℝ)) (i : Fin 8) : -1 ≤ z i ∧ z i ≤ 1 := by
  have hi := coord_sq_le_two hn i
  rw [hz] at hi
  have hr : (-2 : ℝ) < (z i : ℝ) ∧ (z i : ℝ) < 2 := by constructor <;> nlinarith
  have hi' : (-2 : ℤ) < z i ∧ z i < 2 := by exact_mod_cast hr
  omega

lemma half_bounds {x : Space 8} (hn : inner ℝ x x = 2)
    {z : Fin 8 → ℤ} (hz : ∀ i, x i = (z i : ℝ)+1/2) (i : Fin 8) : -1 ≤ z i ∧ z i ≤ 0 := by
  have hi := coord_sq_le_two hn i
  rw [hz] at hi
  have hr : (-2 : ℝ) < (z i : ℝ) ∧ (z i : ℝ) < 1 := by constructor <;> nlinarith
  have hi' : (-2 : ℤ) < z i ∧ z i < 1 := by exact_mod_cast hr
  omega

lemma norm_two_grid_reduction
    (certI : ∀ c : Fin 8 → Fin 3, (∑ i, ((c i).val - (1 : ℤ)) ^ 2) = 2 →
      (fun i => ((c i).val : ℚ) - 1) ∈ e8List)
    (certH : ∀ c : Fin 8 → Fin 2, Even (∑ i, ((c i).val - (1 : ℤ))) →
      (fun i => ((c i).val : ℚ) - 1 + 1/2) ∈ e8List)
    {x : Space 8} (hx : x ∈ lattice) (hn : inner ℝ x x = 2) : x ∈ e8Roots := by
  rcases hx with ⟨z, hz, hx⟩ | ⟨z, hz, hx⟩
  · let c : Fin 8 → Fin 3 := fun i => ⟨(z i+1).toNat, by
      have := integer_bounds hn hx i
      omega⟩
    have hc (i : Fin 8) : ((c i).val : ℤ)-1 = z i := by
      dsimp [c]
      have := integer_bounds hn hx i
      omega
    have he : inner ℝ x x = ((∑ i, z i ^ 2 : ℤ) : ℝ) := by
      rw [PiLp.inner_apply]
      simp [RCLike.inner_apply, hx, pow_two]
    have hs : (∑ i, ((c i).val - (1 : ℤ)) ^ 2) = 2 := by
      simp_rw [hc]
      exact_mod_cast he.symm.trans hn
    refine ⟨_, certI c hs, ?_⟩
    ext i
    change ((((c i).val : ℚ) - 1 : ℚ) : ℝ) = x i
    rw [hx]
    push_cast
    exact_mod_cast hc i
  · let c : Fin 8 → Fin 2 := fun i => ⟨(z i+1).toNat, by
      have := half_bounds hn hx i
      omega⟩
    have hc (i : Fin 8) : ((c i).val : ℤ)-1 = z i := by
      dsimp [c]
      have := half_bounds hn hx i
      omega
    have hs : Even (∑ i, ((c i).val - (1 : ℤ))) := by simpa only [hc] using hz
    refine ⟨_, certH c hs, ?_⟩
    ext i
    change ((((c i).val : ℚ) - 1 + 1/2 : ℚ) : ℝ) = x i
    rw [hx]
    push_cast
    have hi : ((c i).val : ℝ)-1 = (z i : ℝ) := by exact_mod_cast hc i
    linarith
lemma e8_subset_lattice_of_certificate
    (certL : ∀ q ∈ e8List,
      (Even (∑ i, (⌊q i⌋ : ℤ)) ∧ ∀ i, q i = (⌊q i⌋ : ℤ)) ∨
      (Even (∑ i, (⌊q i⌋ : ℤ)) ∧ ∀ i, q i = (⌊q i⌋ : ℤ) + 1/2)) : e8Roots ⊆ lattice := by
  rintro _ ⟨q, hq, rfl⟩
  rcases certL q hq with ⟨hz, he⟩ | ⟨hz, he⟩
  · left
    refine ⟨fun i => ⌊q i⌋, hz, ?_⟩
    intro i
    change (q i : ℝ) = (⌊q i⌋ : ℤ)
    have h := congrArg (fun r : ℚ => (r : ℝ)) (he i)
    push_cast at h
    exact h
  · right
    refine ⟨fun i => ⌊q i⌋, hz, ?_⟩
    intro i
    change (q i : ℝ) = (⌊q i⌋ : ℤ) + 1/2
    have h := congrArg (fun r : ℚ => (r : ℝ)) (he i)
    push_cast at h
    exact h

lemma lattice_of_subset (hs : e8Roots ⊆ lattice) : Specs.latticeType := by
  have hspan : Submodule.span ℝ lattice = ⊤ := by
    apply top_unique
    rw [← e8_span]
    exact Submodule.span_mono hs
  exact ⟨lattice_zero, fun _ hx _ hy => lattice_add hx hy, fun _ hx => lattice_neg hx,
    lattice_discrete, hspan, fun _ hx _ hy => lattice_integral hx hy,
    fun _ hx => lattice_even hx⟩

theorem lattice_isIntegralEven : Specs.latticeType :=
  lattice_of_subset (e8_subset_lattice_of_certificate list_lattice_certificate)

theorem lattice_norm_two : Specs.normTwoType := by
  ext x
  constructor
  · rintro ⟨hx, hn⟩
    exact norm_two_grid_reduction integer_grid_certificate half_grid_certificate hx hn
  · intro hx
    exact ⟨e8_subset_lattice_of_certificate list_lattice_certificate hx, e8_root_norm hx⟩

theorem e8_isRootSystem : Specs.e8Axioms :=
  e8_rootSystem_of_lattice lattice_isIntegralEven lattice_norm_two

theorem e7_isRootSystem : Specs.e7Axioms := e7_rootSystem_of_e8 e8_isRootSystem
theorem e6_isRootSystem : Specs.e6Axioms := e6_rootSystem_of_e8 e8_isRootSystem

theorem e8_basis : Specs.e8Basis := e8_basis_of_rootSystem e8_isRootSystem
theorem e7_basis : Specs.e7Basis := e7_basis_of_rootSystem e7_isRootSystem
theorem e6_basis : Specs.e6Basis := e6_basis_of_rootSystem e6_isRootSystem

theorem coordinate_realizations : Specs.realizationsType := by
  exact ⟨⟨ClassicalCoordinates.rootSystemA, ClassicalCoordinates.countA,
      ClassicalCoordinates.simpleDiagramA⟩,
    ⟨ClassicalCoordinates.rootSystemB, ClassicalCoordinates.countB,
      ClassicalCoordinates.simpleDiagramB⟩,
    ⟨ClassicalCoordinates.rootSystemC, ClassicalCoordinates.countC,
      ClassicalCoordinates.simpleDiagramC⟩,
    ⟨ClassicalCoordinates.rootSystemD, ClassicalCoordinates.countD,
      ClassicalCoordinates.simpleDiagramD⟩,
    ⟨ExceptionalGF.g2_isRootSystem, ExceptionalGF.g2_count,
      ExceptionalGF.g2_basis, ExceptionalGF.g2_diagram⟩,
    ⟨ExceptionalGF.f4_isRootSystem, ExceptionalGF.f4_count,
      ExceptionalGF.f4_basis, ExceptionalGF.f4_diagram⟩,
    ⟨e8_isRootSystem, e8_count, e8_basis, e8_diagram⟩,
    ⟨e7_isRootSystem, e7_count, e7_basis, e7_diagram⟩,
    ⟨e6_isRootSystem, e6_count, e6_basis, e6_diagram⟩⟩

end LieAlgebrasAndRepresentations.ExceptionalE
