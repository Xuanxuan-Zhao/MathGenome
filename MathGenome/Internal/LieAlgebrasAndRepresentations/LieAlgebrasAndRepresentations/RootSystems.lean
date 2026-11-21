import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.RootSystems
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

noncomputable section
namespace LieAlgebrasAndRepresentations
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Public alias of the single canonical bundled Euclidean root-system interface. -/
abbrev EuclideanRootSystem : RootSystemSpecs.rootSystemType := @RootSystem

lemma inner_self_ne_zero {a : E} (ha : a ≠ 0) : inner ℝ a a ≠ 0 :=
  (_root_.inner_self_ne_zero).mpr ha

@[simp] lemma coroot_zero : coroot (0 : E) = 0 := by simp [coroot]

lemma coroot_inner (a : E) :
    inner ℝ (coroot a) (coroot a) = 4 / inner ℝ a a := by
  by_cases ha : a = 0
  · simp [ha, coroot]
  · have h := inner_self_ne_zero ha
    simp only [coroot, real_inner_smul_left, real_inner_smul_right]
    field_simp
    ring

@[simp] theorem coroot_coroot (a : E) : coroot (coroot a) = a := by
  by_cases ha : a = 0
  · simp [ha]
  · have h := inner_self_ne_zero ha
    rw [coroot, coroot_inner, coroot, smul_smul]
    have : 2 / (4 / inner ℝ a a) * (2 / inner ℝ a a) = 1 := by field_simp; ring
    rw [this, one_smul]

lemma coroot_ne_zero {a : E} (ha : a ≠ 0) : coroot a ≠ 0 := by
  intro h
  have := congrArg coroot h
  exact ha (by simpa using this)

lemma coroot_mem_span (a : E) : coroot a ∈ Submodule.span ℝ ({a} : Set E) :=
  Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

lemma span_coroot (a : E) :
    Submodule.span ℝ ({coroot a} : Set E) = Submodule.span ℝ ({a} : Set E) := by
  apply le_antisymm
  · exact Submodule.span_le.mpr (by simpa using coroot_mem_span a)
  · apply Submodule.span_le.mpr
    simpa using coroot_mem_span (coroot a)

lemma reflection_inner (a b c : E) :
    inner ℝ (rootReflection a b) (rootReflection a c) = inner ℝ b c := by
  by_cases ha : a = 0
  · simp [ha, rootReflection]
  · have h := inner_self_ne_zero ha
    simp only [rootReflection, inner_sub_left, inner_sub_right,
      real_inner_smul_left, real_inner_smul_right]
    rw [real_inner_comm a c]
    field_simp
    ring

@[simp] lemma reflection_involutive (a b : E) :
    rootReflection a (rootReflection a b) = b := by
  by_cases ha : a = 0
  · simp [ha, rootReflection]
  · have h := inner_self_ne_zero ha
    have hi : inner ℝ (rootReflection a b) a = - inner ℝ b a := by
      simp only [rootReflection, inner_sub_left, real_inner_smul_left]
      field_simp
      ring
    rw [rootReflection, hi, rootReflection]
    module

lemma reflection_smul (a b : E) (t : ℝ) :
    rootReflection a (t • b) = t • rootReflection a b := by
  simp only [rootReflection, real_inner_smul_left, smul_sub, smul_smul]
  congr 1
  congr 1
  ring

lemma reflection_coroot (a b : E) :
    rootReflection a (coroot b) = coroot (rootReflection a b) := by
  rw [coroot, reflection_smul, coroot, reflection_inner]

lemma coroot_reflection (a b : E) :
    rootReflection (coroot a) b = rootReflection a b := by
  by_cases ha : a = 0
  · simp [ha]
  · have h := inner_self_ne_zero ha
    simp only [rootReflection]
    rw [coroot_inner]
    simp only [coroot, real_inner_smul_right, smul_smul]
    congr 1
    congr 1
    field_simp
    ring

lemma coroot_pairing {a b : E} (ha : a ≠ 0) :
    2 * inner ℝ (coroot b) (coroot a) / inner ℝ (coroot a) (coroot a) =
      2 * inner ℝ a b / inner ℝ b b := by
  have h := inner_self_ne_zero ha
  by_cases hb : b = 0
  · simp [hb]
  · have h' := inner_self_ne_zero hb
    rw [coroot_inner]
    simp only [coroot, real_inner_smul_left, real_inner_smul_right]
    rw [real_inner_comm b a]
    field_simp
    ring

theorem dual_isRootSystem : RootSystemSpecs.dualType := by
  intro E _ _ R hR
  refine { finite := hR.finite.image _
           nonzero := ?_
           reflection_mem := ?_
           integral := ?_
           reduced := ?_
           span_eq_top := ?_ }
  · rintro _ ⟨a, ha, rfl⟩
    exact coroot_ne_zero (hR.nonzero a ha)
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [coroot_reflection, reflection_coroot]
    exact mem_image_of_mem _ (hR.reflection_mem a ha b hb)
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [coroot_pairing (hR.nonzero a ha)]
    exact hR.integral b hb a ha
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hba
    have hbspan : b ∈ Submodule.span ℝ ({a} : Set E) := by
      rw [span_coroot] at hba
      have := Submodule.smul_mem (Submodule.span ℝ ({a} : Set E))
        (2 / inner ℝ (coroot b) (coroot b)) hba
      change coroot (coroot b) ∈ Submodule.span ℝ ({a} : Set E) at this
      simpa only [SetLike.mem_coe, coroot_coroot] using this
    rcases hR.reduced a ha b hb hbspan with rfl | hb'
    · exact Or.inl rfl
    · right
      rw [hb']
      simp [coroot]
  · apply top_unique
    rw [← hR.span_eq_top]
    apply Submodule.span_le.mpr
    intro a ha
    have hc : coroot a ∈ Submodule.span ℝ (coroot '' R) :=
      Submodule.subset_span (mem_image_of_mem _ ha)
    have := Submodule.smul_mem (Submodule.span ℝ (coroot '' R))
      (2 / inner ℝ (coroot a) (coroot a)) hc
    change coroot (coroot a) ∈ Submodule.span ℝ (coroot '' R) at this
    simpa only [SetLike.mem_coe, coroot_coroot] using this

theorem double_dual : RootSystemSpecs.doubleDualType := by
  intro E _ _ R
  rw [Set.image_image]
  simp only [coroot_coroot, Set.image_id']

theorem reflection_image : RootSystemSpecs.reflectionImageType := by
  intro E _ _ R hR a ha
  apply le_antisymm
  · rintro _ ⟨b, hb, rfl⟩
    exact hR.reflection_mem a ha b hb
  · intro b hb
    exact ⟨rootReflection a b, hR.reflection_mem a ha b hb, reflection_involutive a b⟩

theorem empty_rootSystem : RootSystemSpecs.emptyType := by
  intro E _ _ inst
  refine { finite := Set.finite_empty
           nonzero := by simp
           reflection_mem := by simp
           integral := by simp
           reduced := by simp
           span_eq_top := ?_ }
  simp only [Submodule.span_empty, Submodule.eq_top_iff', Submodule.mem_bot]
  exact fun x => Subsingleton.elim x 0


namespace RootConnected
variable {R S : Set E} {a b c : E}
lemma refl (a : E) : RootConnected R a a := Relation.EqvGen.refl a
lemma symm (h : RootConnected R a b) : RootConnected R b a := Relation.EqvGen.symm _ _ h
lemma trans (h : RootConnected R a b) (h' : RootConnected R b c) :
    RootConnected R a c := Relation.EqvGen.trans _ _ _ h h'
lemma mono (hRS : R ⊆ S) (h : RootConnected R a b) : RootConnected S a b :=
  Relation.EqvGen.mono (fun _ _ h => ⟨hRS h.1, hRS h.2.1, h.2.2⟩) _ _ h
lemma mem_iff (h : RootConnected R a b) : a ∈ R ↔ b ∈ R := by
  induction h with
  | rel a b h => exact iff_of_true h.1 h.2.1
  | refl => rfl
  | symm a b h ih => exact ih.symm
  | trans a b c h h' ih ih' => exact ih.trans ih'
end RootConnected

/-- The canonical component containing a root. -/
def rootComponent (R : Set E) (a : E) : Set E := {b | RootConnected R a b}

lemma component_subset {R : Set E} {a : E} (ha : a ∈ R) : rootComponent R a ⊆ R :=
  fun _ h => h.mem_iff.mp ha

lemma component_eq {R : Set E} {a b : E} (hab : RootConnected R a b) :
    rootComponent R a = rootComponent R b := by
  ext c
  exact ⟨fun h => hab.symm.trans h, fun h => hab.trans h⟩

lemma connected_restrict {R : Set E} {a b c : E} (h : RootConnected R b c)
    (hab : RootConnected R a b) : RootConnected (rootComponent R a) b c := by
  induction h with
  | rel b c h =>
    exact Relation.EqvGen.rel _ _ ⟨hab, hab.trans (.rel _ _ h), h.2.2⟩
  | refl => exact .refl _
  | symm b c h ih => exact (ih (hab.trans (Relation.EqvGen.symm _ _ h))).symm
  | trans b c d h h' ih ih' => exact (ih hab).trans (ih' (hab.trans h))

lemma component_irreducible (R : Set E) (a : E) : IsIrreducible (rootComponent R a) := by
  refine ⟨⟨a, RootConnected.refl a⟩, ?_⟩
  intro b hb c hc
  exact connected_restrict (hb.symm.trans hc) hb

lemma components_orthogonal {R : Set E} {a b : E}
    (hne : rootComponent R a ≠ rootComponent R b) (ha : a ∈ R) (hb : b ∈ R) :
    ∀ x ∈ rootComponent R a, ∀ y ∈ rootComponent R b, inner ℝ x y = 0 := by
  intro x hx y hy
  by_contra hxy
  have hc : RootConnected R x y :=
    .rel _ _ ⟨component_subset ha hx, component_subset hb hy, hxy⟩
  exact hne (component_eq (hx.trans (hc.trans hy.symm)))

lemma reflection_inner_right {a b : E} (ha : a ≠ 0) :
    inner ℝ a (rootReflection a b) = -inner ℝ a b := by
  have h := inner_self_ne_zero ha
  simp only [rootReflection, inner_sub_right, real_inner_smul_right]
  rw [real_inner_comm b a]
  field_simp
  ring

lemma component_axioms {R : Set E} (hR : RootAxioms R) {a : E} (ha : a ∈ R) :
    RootAxioms (rootComponent R a) := by
  have hsub := component_subset ha
  refine { finite := hR.finite.subset hsub
           nonzero := fun x hx => hR.nonzero x (hsub hx)
           reflection_mem := ?_
           integral := fun x hx y hy => hR.integral x (hsub hx) y (hsub hy)
           reduced := fun x hx y hy => hR.reduced x (hsub hx) y (hsub hy) }
  intro x hx y hy
  by_cases hxy : inner ℝ x y = 0
  · have hyx : inner ℝ y x = 0 := by rw [real_inner_comm]; exact hxy
    simpa only [rootReflection, hyx, mul_zero, zero_div, zero_smul, sub_zero] using hy
  · have hr := hR.reflection_mem x (hsub hx) y (hsub hy)
    have hi : inner ℝ x (rootReflection x y) ≠ 0 := by
      rw [reflection_inner_right (hR.nonzero x (hsub hx))]
      exact neg_ne_zero.mpr hxy
    exact hx.trans (.rel _ _ ⟨hsub hx, hr, hi⟩)

/-- Chains cannot cross an orthogonal partition. -/
lemma connected_partition {R A B : Set E} (hc : A ∪ B = R)
    (ho : ∀ a ∈ A, ∀ b ∈ B, inner ℝ a b = 0) {x y : E}
    (h : RootConnected R x y) : (x ∈ A ↔ y ∈ A) := by
  induction h with
  | rel x y h =>
    have hx : x ∈ A ∪ B := hc.symm ▸ h.1
    have hy : y ∈ A ∪ B := hc.symm ▸ h.2.1
    constructor
    · intro hxA
      rcases hy with hyA | hyB
      · exact hyA
      · exact False.elim (h.2.2 (ho x hxA y hyB))
    · intro hyA
      rcases hx with hxA | hxB
      · exact hxA
      · exact False.elim (h.2.2 (by rw [real_inner_comm]; exact ho y hyA x hxB))
  | refl => rfl
  | symm x y h ih => exact ih.symm
  | trans x y z h h' ih ih' => exact ih.trans ih'

theorem irreducible_iff_no_orthogonal_partition : RootSystemSpecs.irreducibleType := by
  intro E _ _ R hn
  constructor
  · rintro ⟨hne, hconn⟩
    refine ⟨hne, ?_⟩
    intro A B hc ho
    by_cases hA : A = ∅
    · exact Or.inl hA
    · right
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro b hb
      obtain ⟨a, ha⟩ := Set.nonempty_iff_ne_empty.mpr hA
      have haR : a ∈ R := hc ▸ Or.inl ha
      have hbR : b ∈ R := hc ▸ Or.inr hb
      have hbA := (connected_partition hc ho (hconn a haR b hbR)).mp ha
      exact (inner_self_ne_zero (hn b hbR)) (ho b hbA b hb)
  · rintro ⟨hne, hpart⟩
    refine ⟨hne, ?_⟩
    intro a ha b hb
    let A := rootComponent R a
    let B := R \ A
    have hc : A ∪ B = R := by
      exact Set.union_sdiff_cancel (component_subset ha)
    have ho : ∀ x ∈ A, ∀ y ∈ B, inner ℝ x y = 0 := by
      intro x hx y hy
      by_contra hxy
      exact hy.2 (hx.trans (.rel _ _ ⟨component_subset ha hx, hy.1, hxy⟩))
    rcases hpart A B hc ho with hA | hB
    · have : a ∈ A := RootConnected.refl a
      simp [hA] at this
    · by_contra hab
      have : b ∈ B := ⟨hb, hab⟩
      simp [hB] at this

/-- The finite family of nonorthogonality components. -/
def rootComponents (R : Set E) : Set (Set E) := rootComponent R '' R

lemma canonical_decomposition {R : Set E} (hR : IsRootSystem R) :
    IsOrthogonalDecomposition R (rootComponents R) := by
  refine { finite := hR.finite.image _
           cover := ?_
           axioms := ?_
           irreducible := ?_
           orthogonal := ?_ }
  · ext a
    constructor
    · rintro ⟨A, ⟨b, hb, rfl⟩, ha⟩
      exact component_subset hb ha
    · intro ha
      exact ⟨rootComponent R a, ⟨a, ha, rfl⟩, RootConnected.refl a⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact component_axioms hR.toRootAxioms ha
  · rintro _ ⟨a, ha, rfl⟩
    exact component_irreducible R a
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hne
    exact components_orthogonal hne ha hb

lemma decomposition_block_subset {R : Set E} {C : Set (Set E)}
    (hC : IsOrthogonalDecomposition R C) {A : Set E} (hA : A ∈ C) : A ⊆ R := by
  intro a ha
  rw [← hC.cover]
  exact Set.mem_sUnion_of_mem ha hA

/-- Every block of any orthogonal decomposition is a full chain component. -/
lemma decomposition_component {R : Set E} {C : Set (Set E)}
    (hC : IsOrthogonalDecomposition R C) {A : Set E} (hA : A ∈ C)
    {a : E} (ha : a ∈ A) : A = rootComponent R a := by
  have hsub := decomposition_block_subset hC hA
  apply Set.Subset.antisymm
  · intro b hb
    exact ((hC.irreducible A hA).2 a ha b hb).mono hsub
  · intro b hb
    have hcover : A ∪ (R \ A) = R := Set.union_sdiff_cancel hsub
    have ho : ∀ x ∈ A, ∀ y ∈ R \ A, inner ℝ x y = 0 := by
      intro x hx y hy
      obtain ⟨B, hB, hyB⟩ := Set.mem_sUnion.mp (hC.cover.symm ▸ hy.1)
      have hne : A ≠ B := by
        intro heq
        exact hy.2 (heq ▸ hyB)
      exact hC.orthogonal A hA B hB hne x hx y hyB
    exact (connected_partition hcover ho hb).mp ha

theorem unique_orthogonal_decomposition : RootSystemSpecs.decompositionType := by
  intro E _ _ R hR
  refine ⟨rootComponents R, canonical_decomposition hR, ?_⟩
  intro C hC
  ext A
  constructor
  · intro hA
    obtain ⟨a, ha⟩ := (hC.irreducible A hA).1
    exact ⟨a, decomposition_block_subset hC hA ha, (decomposition_component hC hA ha).symm⟩
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨A, hA, haA⟩ := Set.mem_sUnion.mp (hC.cover.symm ▸ ha)
    exact decomposition_component hC hA haA ▸ hA


theorem component_rootSystem : RootSystemSpecs.componentSystemType := by
  intro E _ _ A hA
  let V := Submodule.span ℝ A
  let S : Set V := {a | (a : E) ∈ A}
  change IsRootSystem S
  have hval : (Subtype.val : V → E) '' S = A := by
    ext a
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro ha
      exact ⟨⟨a, Submodule.subset_span ha⟩, ha, rfl⟩
  have hreflection (a b : V) :
      (rootReflection a b : V).val = rootReflection (a : E) (b : E) := rfl
  refine { finite := Set.Finite.preimage Subtype.val_injective.injOn hA.finite
           nonzero := ?_
           reflection_mem := ?_
           integral := ?_
           reduced := ?_
           span_eq_top := ?_ }
  · intro a ha hzero
    exact hA.nonzero a ha (congrArg Subtype.val hzero)
  · intro a ha b hb
    exact hA.reflection_mem a ha b hb
  · intro a ha b hb
    exact hA.integral a ha b hb
  · intro a ha b hb hba
    have hba' : (b : E) ∈ Submodule.span ℝ ({(a : E)} : Set E) := by
      have hm := Submodule.apply_mem_span_image_of_mem_span V.subtype hba
      simpa only [Set.image_singleton, Submodule.subtype_apply] using hm
    rcases hA.reduced a ha b hb hba' with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  · apply Submodule.map_injective_of_injective V.injective_subtype
    rw [Submodule.map_span, Submodule.map_subtype_top]
    exact congrArg (Submodule.span ℝ) hval

/-- Irreducibility is preserved when a block is regarded in its own span. -/
theorem component_irreducible_in_span : RootSystemSpecs.componentIrreducibleType := by
  intro E _ _ A hA hI
  let V := Submodule.span ℝ A
  let S : Set V := {a | (a : E) ∈ A}
  have hval : (Subtype.val : V → E) '' S = A := by
    ext a
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro ha
      exact ⟨⟨a, Submodule.subset_span ha⟩, ha, rfl⟩
  apply (irreducible_iff_no_orthogonal_partition S (component_rootSystem A hA).nonzero).mpr
  refine ⟨?_, ?_⟩
  · obtain ⟨a, ha⟩ := hI.1
    exact ⟨⟨a, Submodule.subset_span ha⟩, ha⟩
  · intro B C hc ho
    have hc' : (Subtype.val '' B) ∪ (Subtype.val '' C) = A := by
      rw [← Set.image_union, hc, hval]
    have ho' : ∀ b ∈ (Subtype.val '' B), ∀ c ∈ (Subtype.val '' C), inner ℝ b c = 0 := by
      rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩
      exact ho b hb c hc
    have hi := (irreducible_iff_no_orthogonal_partition A hA.nonzero).mp hI
    rcases hi.2 _ _ hc' ho' with hB | hC
    · left
      exact Set.image_eq_empty.mp hB
    · right
      exact Set.image_eq_empty.mp hC

theorem component_spans : RootSystemSpecs.componentSpanType := by
  intro E _ _ R hR C hC
  constructor
  · rw [Submodule.iSup_span]
    have hc : (⋃ A : C, (A : Set E)) = R := by
      rw [← Set.sUnion_eq_iUnion]
      exact hC.cover
    rw [hc, hR.span_eq_top]
  · intro A hA B hB hne a ha b hb
    induction ha using Submodule.span_induction with
    | mem a ha =>
      induction hb using Submodule.span_induction with
      | mem b hb => exact hC.orthogonal A hA B hB hne a ha b hb
      | zero => simp
      | add x y hx hy hix hiy => simp only [inner_add_right, hix, hiy, add_zero]
      | smul t x hx hi => simp only [real_inner_smul_right, hi, mul_zero]
    | zero => simp
    | add x y hx hy hix hiy => simp only [inner_add_left, hix, hiy, add_zero]
    | smul t x hx hi => simp only [real_inner_smul_left, hi, mul_zero]


theorem component_internalSum : RootSystemSpecs.internalSumType := by
  intro E _ _ R hR C hC
  let V : C → Submodule ℝ E := fun A => Submodule.span ℝ (A : Set E)
  have ho : OrthogonalFamily ℝ (fun A => V A) (fun A => (V A).subtypeₗᵢ) := by
    intro A B hne a b
    exact (component_spans R hR C hC).2 A A.property B B.property
      (fun heq => hne (Subtype.ext heq)) a a.property b b.property
  exact DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    ho.independent (component_spans R hR C hC).1

lemma reflection_self {a : E} (ha : a ≠ 0) : rootReflection a a = -a := by
  have h := inner_self_ne_zero ha
  rw [rootReflection]
  have hc : 2 * inner ℝ a a / inner ℝ a a = 2 := by field_simp
  rw [hc, two_smul]
  abel

lemma RootAxioms.neg_mem {R : Set E} (hR : RootAxioms R) {a : E} (ha : a ∈ R) :
    -a ∈ R := by
  simpa only [reflection_self (hR.nonzero a ha)] using hR.reflection_mem a ha a ha

lemma RootAxioms.line_intersection {R : Set E} (hR : RootAxioms R) {a : E} (ha : a ∈ R) :
    R ∩ (Submodule.span ℝ ({a} : Set E) : Set E) = {a, -a} := by
  ext b
  constructor
  · intro hb
    rcases hR.reduced a ha b hb.1 hb.2 with h | h <;> simp [h]
  · intro hb
    rcases Set.mem_insert_iff.mp hb with rfl | hb
    · exact ⟨ha, Submodule.subset_span (by simp)⟩
    · have hb' : b = -a := Set.mem_singleton_iff.mp hb
      subst b
      exact ⟨hR.neg_mem ha, Submodule.neg_mem _ (Submodule.subset_span (by simp))⟩

theorem root_system_iff_source : RootSystemSpecs.sourceAxiomsType := by
  intro E _ _ R
  constructor
  · intro hR
    exact ⟨hR.finite, hR.span_eq_top, fun h => hR.nonzero 0 h rfl,
      reflection_image R hR.toRootAxioms, hR.integral,
      fun a ha => hR.toRootAxioms.line_intersection ha⟩
  · rintro ⟨hf, hs, hz, hrefl, hint, hred⟩
    refine { finite := hf
             span_eq_top := hs
             nonzero := ?_
             reflection_mem := ?_
             integral := hint
             reduced := ?_ }
    · intro a ha heq
      exact hz (heq ▸ ha)
    · intro a ha b hb
      rw [← hrefl a ha]
      exact mem_image_of_mem _ hb
    · intro a ha b hb hba
      have : b ∈ ({a, -a} : Set E) := hred a ha ▸ ⟨hb, hba⟩
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using this

end LieAlgebrasAndRepresentations
