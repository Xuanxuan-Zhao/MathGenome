import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ExceptionalCoordinateGF
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RootSystems
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SimpleRoots
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! Exact coordinate constructions of G₂ and F₄, res:E06.
Finite rational certificates are verified by the Lean kernel and transported
into the canonical real Euclidean root-system interface. -/
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 0

namespace LieAlgebrasAndRepresentations.ExceptionalGF
open Set Module

/-- Exact rational Euclidean pairing. -/
def dot {n : ℕ} (a b : QVec n) : ℚ := ∑ i, a i * b i

def reflect {n : ℕ} (a b : QVec n) : QVec n :=
  b - (2 * dot b a / dot a a) • a

@[simp] lemma realize_apply {n : ℕ} (a : QVec n) (i : Fin n) :
    realize a i = (a i : ℝ) := rfl

lemma realize_injective {n : ℕ} : Function.Injective (@realize n) := by
  intro a b h
  funext i
  have hi : (a i : ℝ) = (b i : ℝ) := congrArg (fun x : Space n => x i) h
  exact_mod_cast hi

@[simp] lemma realize_zero {n : ℕ} : realize (0 : QVec n) = 0 := by
  ext i
  simp [realize]

@[simp] lemma realize_neg {n : ℕ} (a : QVec n) : realize (-a) = -realize a := by
  ext i
  simp [realize]

@[simp] lemma realize_sub {n : ℕ} (a b : QVec n) :
    realize (b - a) = realize b - realize a := by
  ext i
  simp [realize]

@[simp] lemma realize_smul {n : ℕ} (t : ℚ) (a : QVec n) :
    realize (t • a) = (t : ℝ) • realize a := by
  ext i
  simp [realize]

lemma realize_inner {n : ℕ} (a b : QVec n) :
    inner ℝ (realize a) (realize b) = (dot a b : ℝ) := by
  simp [PiLp.inner_apply, dot, RCLike.inner_apply, mul_comm]

lemma realize_reflect {n : ℕ} (a b : QVec n) :
    realize (reflect a b) = rootReflection (realize a) (realize b) := by
  unfold reflect rootReflection
  rw [realize_sub, realize_smul, realize_inner, realize_inner]
  congr 2
  push_cast
  rfl

/-- A finite, entirely decidable certificate for the non-spanning root axioms.
The last test detects collinearity by the Gram determinant. -/
structure ListCertificate {n : ℕ} (S : Finset (QVec n)) : Prop where
  nonzero : ∀ a ∈ S, a ≠ 0
  reflection : ∀ a ∈ S, ∀ b ∈ S, reflect a b ∈ S
  integral : ∀ a ∈ S, ∀ b ∈ S, ∃ z ∈ (Finset.Icc (-3 : ℤ) 3),
    2 * dot b a / dot a a = (z : ℚ)
  reduced : ∀ a ∈ S, ∀ b ∈ S,
    dot a b ^ 2 = dot a a * dot b b → b = a ∨ b = -a

lemma list_rootAxioms {n : ℕ} (S : Finset (QVec n)) (hS : ListCertificate S) :
    RootAxioms (realize '' (S : Set (QVec n))) := by
  refine { finite := S.finite_toSet.image _
           nonzero := ?_
           reflection_mem := ?_
           integral := ?_
           reduced := ?_ }
  · rintro _ ⟨a, ha, rfl⟩ h
    exact hS.nonzero a ha (realize_injective (h.trans realize_zero.symm))
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← realize_reflect]
    exact mem_image_of_mem _ (hS.reflection a ha b hb)
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    obtain ⟨z, _, hz⟩ := hS.integral a ha b hb
    refine ⟨z, ?_⟩
    simp only [realize_inner]
    exact_mod_cast hz
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hba
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hba
    have hh : inner ℝ (realize a) (realize b) ^ 2 =
        inner ℝ (realize a) (realize a) * inner ℝ (realize b) (realize b) := by
      rw [← ht]
      simp only [real_inner_smul_right, real_inner_smul_left]
      ring
    simp only [realize_inner] at hh
    have hq : dot a b ^ 2 = dot a a * dot b b := by exact_mod_cast hh
    rcases hS.reduced a ha b hb hq with h | h
    · exact Or.inl (congrArg realize h)
    · exact Or.inr (by simpa using congrArg realize h)

lemma realize_ncard {n : ℕ} (S : Finset (QVec n)) :
    (realize '' (S : Set (QVec n))).ncard = S.card := by
  rw [Set.ncard_image_of_injective _ realize_injective, Set.ncard_coe_finset]

set_option maxRecDepth 4096 in
lemma g2_list_card : g2List.card = 12 := by decide +kernel

set_option maxRecDepth 4096 in
lemma f4_list_card : f4List.card = 48 := by decide +kernel

set_option maxRecDepth 4096 in
lemma f4_part_cards : f4Coordinate.card = 8 ∧ f4Long.card = 24 ∧ f4Half.card = 16 ∧
    Disjoint f4Coordinate f4Long ∧ Disjoint f4Coordinate f4Half ∧ Disjoint f4Long f4Half := by
  decide +kernel

lemma g2_certificate : ListCertificate g2List := by
  constructor <;> decide +kernel

lemma f4_certificate : ListCertificate f4List := by
  constructor <;> decide +kernel

lemma g2_ambient_axioms : RootAxioms g2AmbientRoots :=
  list_rootAxioms g2List g2_certificate

lemma f4_axioms : RootAxioms f4Roots :=
  list_rootAxioms f4List f4_certificate

/-- The source's separate F₄ counts, with disjointness as well as the total. -/
theorem f4_count : Specs.f4Count := by
  unfold Specs.f4Count f4Roots
  simp only [realize_ncard]
  exact ⟨f4_list_card, f4_part_cards⟩



lemma simple_family_basis {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} {R : Set E} {v : E} (hR : IsRootSystem R) (hv : RootRegular R v)
    (a : Fin n → E) (ha : Function.Injective a) (hs : range a = simpleRoots R v) :
    ∃ b : Basis (Fin n) ℝ E, (∀ i, b i = a i) ∧ IsSimpleBasis R v b := by
  obtain ⟨c, hc⟩ := simpleRoots_basis R hR v hv
  let e : Fin n ≃ simpleRoots R v := Equiv.ofBijective
    (fun i => ⟨a i, hs ▸ mem_range_self i⟩)
    ⟨fun i j h => ha (congrArg Subtype.val h), by
      rintro ⟨x, hx⟩
      obtain ⟨i, rfl⟩ := hs.symm ▸ hx
      exact ⟨i, rfl⟩⟩
  refine ⟨c.reindex e.symm, ?_, ?_⟩
  · intro i
    simpa only [Basis.reindex_apply, Equiv.symm_symm, e, Equiv.ofBijective, Equiv.coe_fn_mk] using hc (e i)
  · change range (c.reindex e.symm) = simpleRoots R v
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      rw [Basis.reindex_apply, Equiv.symm_symm, hc]
      exact (e i).property
    · intro hx
      obtain ⟨i, hi⟩ := e.surjective ⟨x, hx⟩
      refine ⟨i, ?_⟩
      rw [Basis.reindex_apply, Equiv.symm_symm, hc, hi]

lemma g2_simple_mem_q :
    (![1,-1,0] : QVec 3) ∈ g2List ∧ (![-2,1,1] : QVec 3) ∈ g2List := by
  decide +kernel

lemma g2_sum_q : ∀ a ∈ g2List, ∑ i, a i = 0 := by decide +kernel

lemma g2_span : Submodule.span ℝ g2AmbientRoots = g2Plane := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, rfl⟩
    change ∑ i, (a i : ℝ) = 0
    exact_mod_cast g2_sum_q a ha
  · intro x hx
    have hxs : x 0 + x 1 + x 2 = 0 := by
      simpa [g2Plane, Fin.sum_univ_succ, add_assoc] using hx
    have h1 : g2SimpleAmbient 0 ∈ Submodule.span ℝ g2AmbientRoots :=
      Submodule.subset_span ⟨_, g2_simple_mem_q.1, rfl⟩
    have h2 : g2SimpleAmbient 1 ∈ Submodule.span ℝ g2AmbientRoots :=
      Submodule.subset_span ⟨_, g2_simple_mem_q.2, rfl⟩
    have he : x = (x 0 + 2 * x 2) • g2SimpleAmbient 0 + x 2 • g2SimpleAmbient 1 := by
      ext i
      fin_cases i <;> simp [g2SimpleAmbient, realize] <;> linarith
    rw [he]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ h1) (Submodule.smul_mem _ _ h2)

lemma f4_unit_mem_q : ∀ i : Fin 4, unit i ∈ f4List := by decide +kernel

lemma f4_span : Submodule.span ℝ f4Roots = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro x
  have hu (i : Fin 4) : realize (unit i) ∈ Submodule.span ℝ f4Roots :=
    Submodule.subset_span ⟨unit i, f4_unit_mem_q i, rfl⟩
  have he : x = ∑ i, x i • realize (unit i) := by
    ext j
    fin_cases j <;> simp [Fin.sum_univ_succ, realize, unit, Pi.single_apply]
  rw [he]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (hu i))

theorem g2_isRootSystem : Specs.g2Axioms := by
  have h := component_rootSystem g2AmbientRoots g2_ambient_axioms
  rw [g2_span] at h
  exact h

theorem f4_isRootSystem : Specs.f4Axioms :=
  ⟨f4_axioms, f4_span⟩

theorem g2_count : Specs.g2Count := by
  have hi : (Subtype.val : g2Plane → Space 3) '' g2Roots = g2AmbientRoots := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩; exact ha
    · intro hx
      exact ⟨⟨x, g2_span ▸ Submodule.subset_span hx⟩, hx, rfl⟩
  change g2Roots.ncard = 12
  rw [← Set.ncard_image_of_injective g2Roots Subtype.val_injective, hi]
  exact (realize_ncard g2List).trans g2_list_card

@[simp] lemma realize_add {n : ℕ} (a b : QVec n) :
    realize (a + b) = realize a + realize b := by
  ext i
  simp [realize]

def qSimple {n : ℕ} (S : Finset (QVec n)) (v : QVec n) : Finset (QVec n) :=
  S.filter (fun a => 0 < dot v a ∧ ∀ b ∈ S, ∀ c ∈ S,
    0 < dot v b → 0 < dot v c → a ≠ b + c)

lemma simple_roots_realize {n : ℕ} (S : Finset (QVec n)) (v : QVec n) :
    simpleRoots (realize '' (S : Set (QVec n))) (realize v) =
      realize '' (qSimple S v : Set (QVec n)) := by
  ext x
  constructor
  · rintro ⟨⟨⟨a, ha, rfl⟩, hpos⟩, hind⟩
    rw [realize_inner] at hpos
    refine ⟨a, Finset.mem_filter.mpr ⟨ha, ?_, ?_⟩, rfl⟩
    · exact_mod_cast hpos
    · intro b hb c hc hpb hpc he
      have hpb' : 0 < inner ℝ (realize v) (realize b) := by
        rw [realize_inner]; exact_mod_cast hpb
      have hpc' : 0 < inner ℝ (realize v) (realize c) := by
        rw [realize_inner]; exact_mod_cast hpc
      exact hind _ ⟨⟨b, hb, rfl⟩, hpb'⟩ _ ⟨⟨c, hc, rfl⟩, hpc'⟩
        (by rw [he, realize_add])
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨ha, hp, hi⟩ := Finset.mem_filter.mp ha
    refine ⟨⟨⟨a, ha, rfl⟩, ?_⟩, ?_⟩
    · rw [realize_inner]; exact_mod_cast hp
    · rintro _ ⟨⟨b, hb, rfl⟩, hpb⟩ _ ⟨⟨c, hc, rfl⟩, hpc⟩ he
      rw [realize_inner] at hpb hpc
      have hpb' : 0 < dot v b := by exact_mod_cast hpb
      have hpc' : 0 < dot v c := by exact_mod_cast hpc
      apply hi b hb c hc hpb' hpc'
      exact realize_injective (by rw [realize_add]; exact he)

lemma regular_realize {n : ℕ} (S : Finset (QVec n)) (v : QVec n)
    (h : ∀ a ∈ S, dot v a ≠ 0) :
    RootRegular (realize '' (S : Set (QVec n))) (realize v) := by
  rintro _ ⟨a, ha, rfl⟩
  rw [realize_inner]
  exact_mod_cast h a ha

lemma g2_qsimple : qSimple g2List ![-1,-2,3] =
    {![1,-1,0], ![-2,1,1]} := by decide +kernel

lemma f4_qsimple : qSimple f4List ![8,3,2,1] =
    {![0,1,-1,0], ![0,0,1,-1], ![0,0,0,1], ![1/2,-1/2,-1/2,-1/2]} := by
  decide +kernel

lemma g2_qregular : ∀ a ∈ g2List, dot ![-1,-2,3] a ≠ 0 := by decide +kernel
lemma f4_qregular : ∀ a ∈ f4List, dot ![8,3,2,1] a ≠ 0 := by decide +kernel




lemma simpleRoots_submodule {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (V : Submodule ℝ E) (R : Set E) (hR : R ⊆ V) (v : V) :
    simpleRoots {x : V | (x : E) ∈ R} v =
      {x : V | (x : E) ∈ simpleRoots R (v : E)} := by
  ext a
  constructor
  · rintro ⟨ha, hind⟩
    refine ⟨ha, ?_⟩
    intro b hb c hc he
    exact hind ⟨b, hR hb.1⟩ hb ⟨c, hR hc.1⟩ hc (Subtype.ext he)
  · rintro ⟨ha, hind⟩
    refine ⟨ha, ?_⟩
    intro b hb c hc he
    exact hind b hb c hc (congrArg Subtype.val he)

lemma g2_ambient_simple : range g2SimpleAmbient =
    simpleRoots g2AmbientRoots g2RegularAmbient := by
  rw [g2AmbientRoots, g2RegularAmbient, simple_roots_realize, g2_qsimple]
  ext x
  simp [g2SimpleAmbient, or_comm]

lemma f4_simple : range f4Simple = simpleRoots f4Roots f4Regular := by
  rw [f4Roots, f4Regular, simple_roots_realize, f4_qsimple]
  ext x
  simp only [f4Simple, Matrix.range_cons, Matrix.range_empty, Set.image_insert_eq,
    Set.image_singleton, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff, Set.mem_union, Set.notMem_empty, or_false]

lemma g2_simple : range g2Simple = simpleRoots g2Roots g2Regular := by
  rw [g2Roots, simpleRoots_submodule g2Plane g2AmbientRoots
    (by rw [← g2_span]; exact Submodule.subset_span)]
  ext x
  change (∃ i, g2Simple i = x) ↔
    (x : Space 3) ∈ simpleRoots g2AmbientRoots g2RegularAmbient
  rw [← g2_ambient_simple]
  constructor
  · rintro ⟨i, rfl⟩; exact ⟨i, rfl⟩
  · rintro ⟨i, hi⟩; exact ⟨i, Subtype.ext hi⟩

lemma g2_simple_injective : Function.Injective g2Simple := by
  intro i j h
  have h0 := congrArg (fun x : g2Plane => (x : Space 3) 0) h
  fin_cases i <;> fin_cases j
  all_goals first | rfl | (norm_num [g2Simple, g2SimpleAmbient, realize] at h0)

lemma f4_simple_injective : Function.Injective f4Simple := by
  intro i j h
  have h0 := congrArg (fun x : Space 4 => x 0) h
  have h1 := congrArg (fun x : Space 4 => x 1) h
  have h2 := congrArg (fun x : Space 4 => x 2) h
  fin_cases i <;> fin_cases j
  all_goals try rfl
  all_goals norm_num [f4Simple, realize] at h0
  all_goals norm_num [f4Simple, realize] at h1
  all_goals norm_num [f4Simple, realize] at h2

theorem g2_basis : Specs.g2Basis := by
  have hr : RootRegular g2Roots g2Regular := by
    intro a ha
    exact regular_realize g2List ![-1,-2,3] g2_qregular (a : Space 3) ha
  exact ⟨hr, simple_family_basis g2_isRootSystem hr g2Simple g2_simple_injective g2_simple⟩

theorem f4_basis : Specs.f4Basis := by
  have hr := regular_realize f4List ![8,3,2,1] f4_qregular
  exact ⟨hr, simple_family_basis f4_isRootSystem hr f4Simple f4_simple_injective f4_simple⟩

lemma realize_norm_sq {n : ℕ} (a : QVec n) :
    ‖realize a‖ ^ 2 = (dot a a : ℝ) := by
  rw [← real_inner_self_eq_norm_sq]
  exact realize_inner a a

theorem g2_diagram : Specs.g2Diagram := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [cartanMatrix, rootCartan, g2Simple, g2SimpleAmbient, realize_norm_sq, realize_inner, dot,
        Submodule.coe_inner, PiLp.inner_apply, Fin.sum_univ_succ]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [dynkinDiagram, cartanMatrix, rootCartan, g2Simple, g2SimpleAmbient,
        realize_norm_sq, realize_inner, dot, Submodule.coe_inner, PiLp.inner_apply, Fin.sum_univ_succ]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [dynkinDiagram, g2Simple, g2SimpleAmbient, realize_norm_sq, realize_inner, dot,
        Submodule.coe_inner, PiLp.inner_apply, Fin.sum_univ_succ]

theorem f4_diagram : Specs.f4Diagram := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [cartanMatrix, rootCartan, f4Simple, realize_norm_sq, realize_inner, dot, PiLp.inner_apply, Fin.sum_univ_succ]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [dynkinDiagram, cartanMatrix, rootCartan, f4Simple,
        realize_norm_sq, realize_inner, dot, PiLp.inner_apply, Fin.sum_univ_succ]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [dynkinDiagram, f4Simple, realize_norm_sq, realize_inner, dot, PiLp.inner_apply, Fin.sum_univ_succ]


end LieAlgebrasAndRepresentations.ExceptionalGF
