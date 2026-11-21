import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SerreSimplicity
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SerreFiniteType
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Nat.Find

/-! LA-F03: simplicity and the canonical decomposition by connected components. -/
noncomputable section
open scoped DirectSum
namespace LieAlgebrasAndRepresentations.Serre
universe u v
variable {ι : Type u} [DecidableEq ι] (A : Matrix ι ι ℤ)
local instance componentDecidableEq : DecidableEq (Component A) := by
  classical
  infer_instance

/-- The Serre presentation on an empty index type gives the zero Lie algebra. -/
theorem emptySimplicity_spec :
    Specs.LieAlgebrasAndRepresentations.SerreSimplicity.emptyExpected.{u} :=
  empty_spec

/-- A surviving rank-one triple proves nonabelianness, including rank one. -/
theorem nonabelian_of_cartanConditions [Nonempty ι] (hA : CartanConditions A) :
    ¬ IsLieAbelian (Algebra A) := by
  intro hab
  haveI := hab
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hz : h A i = 0 := by
    have hi := ef A i i
    simpa only [ite_true, trivial_lie_zero] using hi.symm
  exact ((triangular_of_cartanConditions A hA).2.2.2.2 i).2.2 hz

/-- A nonzero Cartan coefficient lets an ideal recover a generator. -/
theorem e_mem_ideal_of_h_mem (I : LieIdeal ℂ (Algebra A)) {i j : ι}
    (hi : h A i ∈ I) (hij : A i j ≠ 0) : e A j ∈ I := by
  have hm := lie_mem_left ℂ (Algebra A) I (h A i) (e A j) hi
  have hec : ⁅h A i, e A j⁆ = (A i j : ℂ) • e A j := by
    simpa only [Int.cast_smul_eq_zsmul] using he A i j
  rw [hec] at hm
  have hcast : (A i j : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hij
  exact (I.toSubmodule.smul_mem_iff hcast).mp
    hm

/-- Once e_i is in an ideal, its whole rank-one triple is in that ideal. -/
theorem triple_mem_ideal_of_e_mem (hA : ∀ i, A i i = 2)
    (I : LieIdeal ℂ (Algebra A)) {i : ι} (hi : e A i ∈ I) :
    e A i ∈ I ∧ f A i ∈ I ∧ h A i ∈ I := by
  have hhI : h A i ∈ I := by
    simpa only [ef, ite_true] using lie_mem_left ℂ (Algebra A) I (e A i) (f A i) hi
  have hfI := lie_mem_left ℂ (Algebra A) I (h A i) (f A i) hhI
  rw [hf, hA] at hfI
  have hconv : (- (2 : ℂ)) • f A i = - ((2 : ℤ) • f A i) := by
    simp only [neg_smul, ← Int.cast_ofNat (R := ℂ) 2, Int.cast_smul_eq_zsmul]
  have hfI' : (- (2 : ℂ)) • f A i ∈ I := hconv.symm ▸ hfI
  exact ⟨hi, (I.toSubmodule.smul_mem_iff (by norm_num : (- (2 : ℂ)) ≠ 0)).mp hfI', hhI⟩

/-- Ideal membership propagates along the equivalence closure of graph edges. -/
theorem e_mem_ideal_of_connected (hA : CartanConditions A)
    (I : LieIdeal ℂ (Algebra A)) {i j : ι} (hij : MatrixConnected A i j) :
    e A i ∈ I ↔ e A j ∈ I := by
  induction hij with
  | rel i j hedge =>
    constructor
    · intro hi
      exact e_mem_ideal_of_h_mem A I
        (triple_mem_ideal_of_e_mem A hA.1 I hi).2.2 hedge.2
    · intro hj
      exact e_mem_ideal_of_h_mem A I
        (triple_mem_ideal_of_e_mem A hA.1 I hj).2.2
        (fun hji => hedge.2 ((hA.2.2 i j).mpr hji))
  | refl i => rfl
  | symm i j _ ih => exact ih.symm
  | trans i j k _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- One positive generator in an ideal of a connected Cartan presentation
forces the ideal to contain every generator. -/
theorem ideal_eq_top_of_e_mem (hA : CartanConditions A)
    (hconn : ∀ i j, MatrixConnected A i j) (I : LieIdeal ℂ (Algebra A))
    {i : ι} (hi : e A i ∈ I) : I = ⊤ := by
  have heI (j : ι) : e A j ∈ I :=
    (e_mem_ideal_of_connected A hA I (hconn i j)).mp hi
  have hgen := generators_generate A (LieIdeal.toLieSubalgebra ℂ (Algebra A) I)
    heI (fun j => (triple_mem_ideal_of_e_mem A hA.1 I (heI j)).2.1)
    (fun j => (triple_mem_ideal_of_e_mem A hA.1 I (heI j)).2.2)
  apply top_unique
  intro x _
  have hx : x ∈ (⊤ : LieSubalgebra ℂ (Algebra A)) := trivial
  rw [← hgen] at hx
  exact hx

@[simp] theorem componentOf_eq_iff {i j : ι} :
    componentOf A i = componentOf A j ↔ MatrixConnected A i j :=
  Quotient.eq

/-- Distinct components have zero Cartan coefficients in either direction. -/
theorem cartan_entry_eq_zero_of_component_ne {i j : ι}
    (hij : componentOf A i ≠ componentOf A j) : A i j = 0 := by
  by_contra hne
  apply hij
  apply (componentOf_eq_iff A).mpr
  exact Relation.EqvGen.rel i j ⟨fun heq => hij (congrArg (componentOf A) heq), hne⟩

theorem component_cartanConditions (hA : CartanConditions A) (c : Component A) :
    CartanConditions (componentMatrix A c) := by
  refine ⟨fun i => hA.1 i.val, ?_, fun i j => hA.2.2 i.val j.val⟩
  intro i j hij
  exact hA.2.1 i.val j.val (fun h => hij (Subtype.ext h))

/-- Every connected component has at least one vertex, even when the
original diagram has an arbitrary index type. -/
theorem component_nonempty (c : Component A) : Nonempty (componentVertices A c) := by
  induction c using Quotient.inductionOn with
  | _ i => exact ⟨⟨i, rfl⟩⟩

/-- The full algebra's generators satisfy each restricted presentation. -/
theorem component_relations
    (hA : ∀ i j, i ≠ j → A i j ≤ 0) (c : Component A) :
    RelationsHold (componentMatrix A c)
      (fun i => e A i.val) (fun i => f A i.val) (fun i => h A i.val) := by
  have hr := relations_spec A hA
  refine ⟨fun i j => hr.1 i.val j.val,
    fun i j => hr.2.1 i.val j.val, fun i j => hr.2.2.1 i.val j.val, ?_, ?_, ?_⟩
  · intro i j
    simpa only [Subtype.ext_iff] using hr.2.2.2.1 i.val j.val
  · intro i j hij
    exact hr.2.2.2.2.1 i.val j.val (fun h => hij (Subtype.ext h))
  · intro i j hij
    exact hr.2.2.2.2.2 i.val j.val (fun h => hij (Subtype.ext h))

/-- The canonical map from a component's Serre algebra into the full one. -/
def componentInclusion (hA : ∀ i j, i ≠ j → A i j ≤ 0) (c : Component A) :
    Algebra (componentMatrix A c) →ₗ⁅ℂ⁆ Algebra A :=
  lift (componentMatrix A c)
    (fun i j hij => hA i.val j.val (fun h => hij (Subtype.ext h)))
    (fun i => e A i.val) (fun i => f A i.val) (fun i => h A i.val)
    (component_relations A hA c)

@[simp] theorem componentInclusion_e (hA : ∀ i j, i ≠ j → A i j ≤ 0)
    (c : Component A) (i : componentVertices A c) :
    componentInclusion A hA c (e (componentMatrix A c) i) = e A i.val := lift_e ..
@[simp] theorem componentInclusion_f (hA : ∀ i j, i ≠ j → A i j ≤ 0)
    (c : Component A) (i : componentVertices A c) :
    componentInclusion A hA c (f (componentMatrix A c) i) = f A i.val := lift_f ..
@[simp] theorem componentInclusion_h (hA : ∀ i j, i ≠ j → A i j ≤ 0)
    (c : Component A) (i : componentVertices A c) :
    componentInclusion A hA c (h (componentMatrix A c) i) = h A i.val := lift_h ..

/-- A component generator extended by zero outside that component. -/
def componentPart (c : Component A)
    (g : componentVertices A c → Algebra (componentMatrix A c))
    (i : ι) : Algebra (componentMatrix A c) := by
  classical
  exact if hi : componentOf A i = c then g ⟨i, hi⟩ else 0

@[simp] theorem componentPart_inside (c : Component A)
    (g : componentVertices A c → Algebra (componentMatrix A c))
    (i : componentVertices A c) : componentPart A c g i.val = g i := by
  classical
  have hi : componentOf A i.val = c := i.property
  simp [componentPart, hi]

@[simp] theorem componentPart_outside (c : Component A)
    (g : componentVertices A c → Algebra (componentMatrix A c))
    (i : ι) (hi : componentOf A i ≠ c) : componentPart A c g i = 0 := by
  classical
  simp [componentPart, hi]

/-- Extending the restricted generators by zero respects all full relations. -/
theorem component_projection_relations
    (hA : ∀ i j, i ≠ j → A i j ≤ 0) (c : Component A) :
    RelationsHold A (componentPart A c (e (componentMatrix A c)))
      (componentPart A c (f (componentMatrix A c)))
      (componentPart A c (h (componentMatrix A c))) := by
  classical
  have hr := relations_spec (componentMatrix A c)
    (fun i j hij => hA i.val j.val (fun h => hij (Subtype.ext h)))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    by_cases hi : componentOf A i = c <;> by_cases hj : componentOf A j = c
    all_goals simp only [componentPart, hi, hj, ↓reduceDIte,
      hh, zero_lie, lie_zero]
  · intro i j
    by_cases hi : componentOf A i = c <;> by_cases hj : componentOf A j = c
    · simpa only [componentPart, dite_eq_left hi, dite_eq_left hj, componentMatrix] using
        hr.2.1 ⟨i,hi⟩ ⟨j,hj⟩
    · simp [componentPart, hi, hj]
    · have hz : A i j = 0 := cartan_entry_eq_zero_of_component_ne A
        (fun hij => hi (hij.trans hj))
      simp [componentPart, hi, hj, hz]
    · simp [componentPart, hi, hj]
  · intro i j
    by_cases hi : componentOf A i = c <;> by_cases hj : componentOf A j = c
    · simpa only [componentPart, dite_eq_left hi, dite_eq_left hj, componentMatrix] using
        hr.2.2.1 ⟨i,hi⟩ ⟨j,hj⟩
    · simp [componentPart, hi, hj]
    · have hz : A i j = 0 := cartan_entry_eq_zero_of_component_ne A
        (fun hij => hi (hij.trans hj))
      simp [componentPart, hi, hj, hz]
    · simp [componentPart, hi, hj]
  · intro i j
    by_cases hi : componentOf A i = c <;> by_cases hj : componentOf A j = c
    · simpa only [componentPart, dite_eq_left hi, dite_eq_left hj, Subtype.ext_iff] using
        hr.2.2.2.1 ⟨i,hi⟩ ⟨j,hj⟩
    · have hij : i ≠ j := fun h => hj (h ▸ hi)
      simp [componentPart, hi, hj, hij]
    · have hij : i ≠ j := fun h => hi (h.symm ▸ hj)
      simp [componentPart, hi, hj, hij]
    · simp [componentPart, hi, hj]
  · intro i j hij
    by_cases hi : componentOf A i = c <;> by_cases hj : componentOf A j = c
    · simpa only [componentPart, dite_eq_left hi, dite_eq_left hj, componentMatrix] using
        hr.2.2.2.2.1 ⟨i,hi⟩ ⟨j,hj⟩ (fun h => hij (congrArg Subtype.val h))
    · simp [componentPart, hi, hj]
    · have hz : A i j = 0 := cartan_entry_eq_zero_of_component_ne A
        (fun hij => hi (hij.trans hj))
      simp [componentPart, hi, hj, hz, iterBracket]
    · simp [componentPart, hi, hj]
  · intro i j hij
    by_cases hi : componentOf A i = c <;> by_cases hj : componentOf A j = c
    · simpa only [componentPart, dite_eq_left hi, dite_eq_left hj, componentMatrix] using
        hr.2.2.2.2.2 ⟨i,hi⟩ ⟨j,hj⟩ (fun h => hij (congrArg Subtype.val h))
    · simp [componentPart, hi, hj]
    · have hz : A i j = 0 := cartan_entry_eq_zero_of_component_ne A
        (fun hij => hi (hij.trans hj))
      simp [componentPart, hi, hj, hz, iterBracket]
    · simp [componentPart, hi, hj]

/-- The canonical retraction to a connected component. -/
def componentProjection (hA : ∀ i j, i ≠ j → A i j ≤ 0) (c : Component A) :
    Algebra A →ₗ⁅ℂ⁆ Algebra (componentMatrix A c) :=
  lift A hA (componentPart A c (e (componentMatrix A c)))
    (componentPart A c (f (componentMatrix A c)))
    (componentPart A c (h (componentMatrix A c)))
    (component_projection_relations A hA c)

@[simp] theorem componentProjection_e (hA : ∀ i j, i ≠ j → A i j ≤ 0)
    (c : Component A) (i : ι) : componentProjection A hA c (e A i) =
      componentPart A c (e (componentMatrix A c)) i := lift_e ..
@[simp] theorem componentProjection_f (hA : ∀ i j, i ≠ j → A i j ≤ 0)
    (c : Component A) (i : ι) : componentProjection A hA c (f A i) =
      componentPart A c (f (componentMatrix A c)) i := lift_f ..
@[simp] theorem componentProjection_h (hA : ∀ i j, i ≠ j → A i j ≤ 0)
    (c : Component A) (i : ι) : componentProjection A hA c (h A i) =
      componentPart A c (h (componentMatrix A c)) i := lift_h ..

/-- Each inclusion has a genuine left inverse, so no extra component
relations have been introduced by the full presentation. -/
theorem componentProjection_comp_inclusion
    (hA : ∀ i j, i ≠ j → A i j ≤ 0) (c : Component A) :
    (componentProjection A hA c).comp (componentInclusion A hA c) = LieHom.id := by
  apply hom_ext (componentMatrix A c)
  all_goals intro i; simp

theorem componentInclusion_injective
    (hA : ∀ i j, i ≠ j → A i j ≤ 0) (c : Component A) :
    Function.Injective (componentInclusion A hA c) := by
  apply Function.LeftInverse.injective (g := componentProjection A hA c)
  intro x
  exact LieHom.congr_fun (componentProjection_comp_inclusion A hA c) x

section Commutation
variable {L : Type*} [LieRing L] [LieAlgebra ℂ L]

/-- The elements commuting with one element form a Lie subalgebra. -/
def commutingSubalgebra (a : L) : LieSubalgebra ℂ L where
  carrier := {x | ⁅a,x⁆ = 0}
  zero_mem' := lie_zero a
  add_mem' := by
    intro x y hx hy
    change ⁅a,x⁆ = 0 at hx
    change ⁅a,y⁆ = 0 at hy
    change ⁅a,x+y⁆ = 0
    simp only [lie_add, hx, hy, add_zero]
  smul_mem' := by
    intro r x hx
    change ⁅a,x⁆ = 0 at hx
    change ⁅a,r • x⁆ = 0
    simp only [lie_smul, hx, smul_zero]
  lie_mem' := by
    intro x y hx hy
    change ⁅a,x⁆ = 0 at hx
    change ⁅a,y⁆ = 0 at hy
    change ⁅a,⁅x,y⁆⁆ = 0
    simp only [leibniz_lie, hx, hy, zero_lie, lie_zero, add_zero]

/-- Commuting with the generator images means commuting with every image. -/
theorem lie_hom_eq_zero_of_generators (φ : Algebra A →ₗ⁅ℂ⁆ L) (x : L)
    (hE : ∀ i, ⁅x, φ (e A i)⁆ = 0) (hF : ∀ i, ⁅x, φ (f A i)⁆ = 0)
    (hH : ∀ i, ⁅x, φ (h A i)⁆ = 0) (y : Algebra A) : ⁅x, φ y⁆ = 0 := by
  have hgen := generators_generate A ((commutingSubalgebra x).comap φ) hE hF hH
  have hy : y ∈ (⊤ : LieSubalgebra ℂ (Algebra A)) := trivial
  rw [← hgen] at hy
  exact hy

end Commutation

/-- Different components commute already on all three families of symbols. -/
theorem component_generators_commute {c d : Component A} (hcd : c ≠ d)
    (i : componentVertices A c) (j : componentVertices A d) :
    ⁅e A i.val, e A j.val⁆ = 0 ∧ ⁅e A i.val, f A j.val⁆ = 0 ∧
    ⁅e A i.val, h A j.val⁆ = 0 ∧ ⁅f A i.val, e A j.val⁆ = 0 ∧
    ⁅f A i.val, f A j.val⁆ = 0 ∧ ⁅f A i.val, h A j.val⁆ = 0 ∧
    ⁅h A i.val, e A j.val⁆ = 0 ∧ ⁅h A i.val, f A j.val⁆ = 0 ∧
    ⁅h A i.val, h A j.val⁆ = 0 := by
  have hcomp : componentOf A i.val ≠ componentOf A j.val := by
    intro heq
    apply hcd
    exact i.property.symm.trans (heq.trans j.property)
  have hij : i.val ≠ j.val := fun heq => hcomp (congrArg (componentOf A) heq)
  have hzero := cartan_entry_eq_zero_of_component_ne A hcomp
  have hzero' := cartan_entry_eq_zero_of_component_ne A hcomp.symm
  have hee : ⁅e A i.val, e A j.val⁆ = 0 := by
    simpa only [hzero, neg_zero, Int.toNat_zero, iterBracket] using native_serre_e A i.val j.val
  have hff : ⁅f A i.val, f A j.val⁆ = 0 := by
    simpa only [hzero, neg_zero, Int.toNat_zero, iterBracket] using native_serre_f A i.val j.val
  refine ⟨hee, ?_, ?_, ?_, hff, ?_, ?_, ?_, hh A i.val j.val⟩
  · simp only [ef, ite_eq_right hij]
  · rw [← lie_skew, he, hzero', zero_smul, neg_zero]
  · rw [← lie_skew, ef, ite_eq_right hij.symm, neg_zero]
  · rw [← lie_skew, hf, hzero', zero_smul, neg_zero, neg_zero]
  · rw [he, hzero, zero_smul]
  · rw [hf, hzero, zero_smul, neg_zero]

/-- The complete images of distinct component algebras commute. -/
theorem componentInclusions_commute
    (hA : ∀ i j, i ≠ j → A i j ≤ 0) {c d : Component A} (hcd : c ≠ d)
    (x : Algebra (componentMatrix A c)) (y : Algebra (componentMatrix A d)) :
    ⁅componentInclusion A hA c x, componentInclusion A hA d y⁆ = 0 := by
  apply lie_hom_eq_zero_of_generators (componentMatrix A d)
    (componentInclusion A hA d) (componentInclusion A hA c x) ?_ ?_ ?_ y
  all_goals
    intro j
    rw [← lie_skew]
    apply neg_eq_zero.mpr
    apply lie_hom_eq_zero_of_generators (componentMatrix A c)
      (componentInclusion A hA c) _ ?_ ?_ ?_ x
    all_goals
      intro i
      rw [← lie_skew]
      apply neg_eq_zero.mpr
      simp only [componentInclusion_e, componentInclusion_f, componentInclusion_h]
      have hr := component_generators_commute A hcd i j
      first | exact hr.1 | exact hr.2.1 | exact hr.2.2.1 | exact hr.2.2.2.1 |
        exact hr.2.2.2.2.1 | exact hr.2.2.2.2.2.1 | exact hr.2.2.2.2.2.2.1 |
        exact hr.2.2.2.2.2.2.2.1 | exact hr.2.2.2.2.2.2.2.2

/-- A retraction kills all other component inclusions. -/
theorem componentProjection_comp_inclusion_ne
    (hA : ∀ i j, i ≠ j → A i j ≤ 0) {c d : Component A} (hcd : c ≠ d) :
    (componentProjection A hA c).comp (componentInclusion A hA d) = 0 := by
  apply hom_ext (componentMatrix A d)
  all_goals
    intro i
    have hi : componentOf A i.val ≠ c := by
      intro heq
      exact hcd (heq.symm.trans i.property)
    simp [componentPart, hi]

/-- The actual sum of the mutually commuting component maps. -/
def componentSumHom (hA : ∀ i j, i ≠ j → A i j ≤ 0) :
    (⨁ c : Component A, Algebra (componentMatrix A c)) →ₗ⁅ℂ⁆ Algebra A := by
  classical
  exact DirectSum.toLieAlgebra (Algebra A) (componentInclusion A hA)
    (fun _ _ hcd => componentInclusions_commute A hA hcd)

@[simp] theorem componentSumHom_lof
    (hA : ∀ i j, i ≠ j → A i j ≤ 0) (c : Component A)
    (x : Algebra (componentMatrix A c)) :
    componentSumHom A hA (DirectSum.lof ℂ _ _ c x) = componentInclusion A hA c x := by
  classical
  exact DirectSum.toModule_lof (M := fun d : Component A => Algebra (componentMatrix A d))
    (φ := fun d => (componentInclusion A hA d).toLinearMap) ℂ c x

/-- Projecting a sum recovers its coordinate, giving directness without any
finite-dimensionality or root-space multiplicity assumption. -/
theorem componentProjection_sum
    (hA : ∀ i j, i ≠ j → A i j ≤ 0) (c : Component A)
    (x : ⨁ d : Component A, Algebra (componentMatrix A d)) :
    componentProjection A hA c (componentSumHom A hA x) = x c := by
  classical
  have hlin : (componentProjection A hA c).toLinearMap.comp
      (componentSumHom A hA).toLinearMap =
      DirectSum.component ℂ (Component A) (fun d => Algebra (componentMatrix A d)) c := by
    apply DirectSum.linearMap_ext
    intro d
    ext y
    change componentProjection A hA c
      (componentSumHom A hA (DirectSum.lof ℂ _ _ d y)) =
      DirectSum.component ℂ (Component A) (fun d => Algebra (componentMatrix A d)) c
        (DirectSum.lof ℂ (Component A) (fun d => Algebra (componentMatrix A d)) d y)
    rw [componentSumHom_lof]
    by_cases hdc : d = c
    · subst d
      rw [DirectSum.component.lof_self]
      exact LieHom.congr_fun (componentProjection_comp_inclusion A hA c) y
    · rw [DirectSum.component.of, dite_eq_right hdc]
      exact LieHom.congr_fun (componentProjection_comp_inclusion_ne A hA (fun h => hdc h.symm)) y
  exact LinearMap.congr_fun hlin x

theorem componentSumHom_injective (hA : ∀ i j, i ≠ j → A i j ≤ 0) :
    Function.Injective (componentSumHom A hA) := by
  intro x y hxy
  apply DFinsupp.ext
  intro c
  have hc := congrArg (componentProjection A hA c) hxy
  simpa only [componentProjection_sum] using hc

theorem componentSumHom_surjective (hA : ∀ i j, i ≠ j → A i j ≤ 0) :
    Function.Surjective (componentSumHom A hA) := by
  classical
  have hgen : (componentSumHom A hA).range = ⊤ := by
    apply generators_generate A
    · intro i
      exact ⟨DirectSum.lof ℂ _ _ (componentOf A i)
        (e (componentMatrix A (componentOf A i)) ⟨i,rfl⟩), by simp⟩
    · intro i
      exact ⟨DirectSum.lof ℂ _ _ (componentOf A i)
        (f (componentMatrix A (componentOf A i)) ⟨i,rfl⟩), by simp⟩
    · intro i
      exact ⟨DirectSum.lof ℂ _ _ (componentOf A i)
        (h (componentMatrix A (componentOf A i)) ⟨i,rfl⟩), by simp⟩
  intro x
  have hx : x ∈ (componentSumHom A hA).range := hgen.symm ▸ LieSubalgebra.mem_top x
  exact hx

/-- The component decomposition, proved directly from the Serre presentation.
It works for arbitrary index sets and nonpositive off-diagonal matrices. -/
def componentSumEquiv (hA : ∀ i j, i ≠ j → A i j ≤ 0) :
    (⨁ c : Component A, Algebra (componentMatrix A c)) ≃ₗ⁅ℂ⁆ Algebra A :=
  LieEquiv.ofBijective (componentSumHom A hA)
    ⟨componentSumHom_injective A hA, componentSumHom_surjective A hA⟩

@[simp] theorem componentSumEquiv_apply
    (hA : ∀ i j, i ≠ j → A i j ≤ 0)
    (x : ⨁ c : Component A, Algebra (componentMatrix A c)) :
    componentSumEquiv A hA x = componentSumHom A hA x := rfl

/-- The full finite-type component-sum statement, including all generator images. -/
theorem componentSum_spec :
    Specs.LieAlgebrasAndRepresentations.SerreSimplicity.componentSumExpected.{u,v} := by
  classical
  intro E _ _ ι _ _ R hR z hz b hb A hA
  have hcond := cartanConditions_spec R hR z hz b hb A hA
  refine ⟨componentSumEquiv A hcond.2.1, ?_⟩
  intro c i
  simp only [componentSumEquiv_apply]
  refine ⟨?_, ?_, ?_⟩
  · exact (componentSumHom_lof A hcond.2.1 c (e (componentMatrix A c) i)).trans
      (componentInclusion_e A hcond.2.1 c i)
  · exact (componentSumHom_lof A hcond.2.1 c (f (componentMatrix A c) i)).trans
      (componentInclusion_f A hcond.2.1 c i)
  · exact (componentSumHom_lof A hcond.2.1 c (h (componentMatrix A c) i)).trans
      (componentInclusion_h A hcond.2.1 c i)

/-- The restricted graph on a component is connected, rather than merely
having a component-shaped name. -/
theorem component_connected (c : Component A)
    (i j : componentVertices A c) : MatrixConnected (componentMatrix A c) i j := by
  have hpath : MatrixConnected A i.val j.val :=
    (componentOf_eq_iff A).mp (i.property.trans j.property.symm)
  have hlift : ∀ {x y : ι}, MatrixConnected A x y →
      ∀ (hx : componentOf A x = c) (hy : componentOf A y = c),
      MatrixConnected (componentMatrix A c) ⟨x,hx⟩ ⟨y,hy⟩ := by
    intro x y hp
    induction hp with
    | rel x y hxy =>
      intro hx hy
      exact Relation.EqvGen.rel _ _ ⟨fun h => hxy.1 (congrArg Subtype.val h), hxy.2⟩
    | refl x => intro hx hy; exact Relation.EqvGen.refl _
    | symm x y hp ih =>
      intro hx hy
      exact Relation.EqvGen.symm _ _ (ih hy hx)
    | trans x y z hxy hyz ihxy ihyz =>
      intro hx hz
      have hy : componentOf A y = c := ((componentOf_eq_iff A).mpr hxy).symm.trans hx
      exact Relation.EqvGen.trans _ _ _ (ihxy hx hy) (ihyz hy hz)
  exact hlift hpath i.property j.property

/-- All component factors are nonabelian. -/
theorem component_nonabelian (hA : CartanConditions A) (c : Component A) :
    ¬ IsLieAbelian (Algebra (componentMatrix A c)) := by
  haveI := component_nonempty A c
  exact nonabelian_of_cartanConditions (componentMatrix A c) (component_cartanConditions A hA c)

section DiagramBridge
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {R : Set E} {z : E} {b : Module.Basis ι ℝ E}

/-- The matrix graph used in the specification is exactly the source's
Dynkin graph, under the original root-system and matrix hypotheses. -/
theorem matrixConnected_iff_dynkinConnected (hR : IsRootSystem R)
    (hz : RootRegular R z) (hb : IsSimpleBasis R z b)
    (hA : ∀ i j, (A i j : ℝ) = cartanMatrix b i j) (i j : ι) :
    MatrixConnected A i j ↔ DynkinConnected b i j := by
  have hedge (i j : ι) : (i ≠ j ∧ A i j ≠ 0) ↔ (dynkinDiagram b).edges i j ≠ 0 := by
    rw [dynkin_edges_ne_zero hR hz hb i j]
    have hzentry : A i j = 0 ↔ inner ℝ (b i) (b j) = 0 := by
      rw [← cartan_zero_iff hR.toRootAxioms hb i j, ← hA i j]
      exact Int.cast_eq_zero.symm
    constructor
    · intro ⟨hne, hentry⟩
      exact ⟨hne, fun hz => hentry (hzentry.mpr hz)⟩
    · intro ⟨hne, hinner⟩
      exact ⟨hne, fun hz => hinner (hzentry.mp hz)⟩
  exact ⟨fun h => Relation.EqvGen.mono (fun i j hij => (hedge i j).mp hij) i j h,
    fun h => Relation.EqvGen.mono (fun i j hij => (hedge i j).mpr hij) i j h⟩

end DiagramBridge

/-- A spanning family of weight spaces gives a finite weight-vector sum for
each vector, without requiring finite-dimensionality of any weight space. -/
theorem exists_weight_vector_list
    (hspan : (⨆ χ : ι → ℂ, weightSpace A χ) = ⊤) (x : Algebra A) :
    ∃ l : List (Algebra A), (∀ y ∈ l, ∃ χ, y ∈ weightSpace A χ) ∧ l.sum = x := by
  have hx : x ∈ ⨆ χ : ι → ℂ, weightSpace A χ := hspan.symm ▸ Submodule.mem_top
  refine Submodule.iSup_induction (fun χ => weightSpace A χ)
    (motive := fun x => ∃ l : List (Algebra A),
      (∀ y ∈ l, ∃ χ, y ∈ weightSpace A χ) ∧ l.sum = x) hx ?_ ?_ ?_
  · intro χ y hy
    refine ⟨[y], ?_, by simp⟩
    intro z hz
    have hzy : z = y := by simpa only [List.mem_singleton] using hz
    subst z
    exact ⟨χ,hy⟩
  · exact ⟨[], by simp, by simp⟩
  · intro x y hx hy
    obtain ⟨l,hl,hls⟩ := hx
    obtain ⟨m,hm,hms⟩ := hy
    refine ⟨l ++ m, ?_, by simp only [List.sum_append, hls, hms]⟩
    intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact hl z hz
    · exact hm z hz

/-- Any nonzero ideal has a nonzero ordinary joint weight vector. The
minimal-length proof avoids a finite-dimensionality assumption and also
avoids assuming a weight decomposition of the ideal itself. -/
theorem ideal_contains_weight_vector
    (hspan : (⨆ χ : ι → ℂ, weightSpace A χ) = ⊤)
    (I : LieIdeal ℂ (Algebra A)) (hI : I ≠ ⊥) :
    ∃ (χ : ι → ℂ) (x : Algebra A), x ∈ I ∧ x ≠ 0 ∧ x ∈ weightSpace A χ := by
  classical
  have hx : ∃ x : Algebra A, x ∈ I ∧ x ≠ 0 := by
    by_contra hx
    apply hI
    apply (LieSubmodule.eq_bot_iff I).mpr
    intro x hxI
    by_contra hne
    exact hx ⟨x,hxI,hne⟩
  obtain ⟨x,hxI,hxne⟩ := hx
  obtain ⟨l,hl,hls⟩ := exists_weight_vector_list A hspan x
  have hex : ∃ n : ℕ, ∃ l : List (Algebra A), l.length = n ∧
      (∀ y ∈ l, ∃ χ, y ∈ weightSpace A χ) ∧ l.sum ∈ I ∧ l.sum ≠ 0 :=
    ⟨l.length, l, rfl, hl, hls.symm ▸ hxI, hls.symm ▸ hxne⟩
  obtain ⟨l,hlen,hl,hsI,hsne⟩ := Nat.find_spec hex
  cases l with
  | nil => exact False.elim (hsne (by simp))
  | cons a l =>
    obtain ⟨χ,hχ⟩ := hl a (by simp)
    refine ⟨χ, (a::l).sum, hsI, hsne, ?_⟩
    intro i
    let D : Module.End ℂ (Algebra A) :=
      LieAlgebra.ad ℂ (Algebra A) (h A i) - χ i • LinearMap.id
    have hD (y : Algebra A) : D y = ⁅h A i,y⁆ - χ i • y := rfl
    have hDa : D a = 0 := sub_eq_zero.mpr (hχ i)
    have hmap_sum : ∀ m : List (Algebra A), D m.sum = (m.map D).sum := by
      intro m
      induction m with
      | nil => simp
      | cons b m ih => simp only [List.sum_cons, List.map_cons, map_add, ih]
    have hsum : D (a::l).sum = (l.map D).sum := by
      rw [List.sum_cons, map_add, hDa, zero_add, hmap_sum]
    have hmem : (l.map D).sum ∈ I := by
      rw [← hsum, hD]
      exact I.sub_mem (I.lie_mem hsI) (I.smul_mem _ hsI)
    have hweights : ∀ y ∈ l.map D, ∃ ψ, y ∈ weightSpace A ψ := by
      intro y hy
      obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hy
      obtain ⟨ψ,hψ⟩ := hl z (List.mem_cons_of_mem a hz)
      refine ⟨ψ, ?_⟩
      have hDz : D z = (ψ i - χ i) • z := by rw [hD, hψ i, sub_smul]
      rw [hDz]
      exact (weightSpace A ψ).smul_mem _ hψ
    have hzero : (l.map D).sum = 0 := by
      by_contra hne
      have hmin := Nat.find_min' hex
        (show ∃ m : List (Algebra A), m.length = (l.map D).length ∧
          (∀ y ∈ m, ∃ ψ, y ∈ weightSpace A ψ) ∧ m.sum ∈ I ∧ m.sum ≠ 0 from
          ⟨l.map D, rfl, hweights, hmem, hne⟩)
      simp only [List.length_map] at hmin
      have hn : Nat.find hex = l.length + 1 := hlen.symm
      omega
    exact sub_eq_zero.mp (by rw [← hD, hsum, hzero])

/-- Generator extraction and connectedness imply nonabelian simplicity. -/
theorem isSimple_of_ideal_contains_e [Nonempty ι] (hA : CartanConditions A)
    (hconn : ∀ i j, MatrixConnected A i j)
    (hgen : ∀ I : LieIdeal ℂ (Algebra A), I ≠ ⊥ → ∃ i, e A i ∈ I) :
    LieAlgebra.IsSimple ℂ (Algebra A) where
  eq_bot_or_eq_top I := by
    by_cases hI : I = ⊥
    · exact Or.inl hI
    · obtain ⟨i,hi⟩ := hgen I hI
      exact Or.inr (ideal_eq_top_of_e_mem A hA hconn I hi)
  non_abelian := nonabelian_of_cartanConditions A hA

section IdealReflections
variable {L : Type*} [LieRing L] [LieAlgebra ℂ L]

/-- Terminating inner exponentials preserve every ideal. -/
theorem innerExp_mem_ideal (I : LieIdeal ℂ L) (z : L)
    (hz : ∀ x : L, ∃ n, iterBracket z n x = 0) {x : L} (hx : x ∈ I) :
    innerExp z hz x ∈ I := by
  obtain ⟨N, hN⟩ := hz x
  rw [innerExp_eq_expSum z hz hN]
  have hi (n : ℕ) : iterBracket z n x ∈ I := by
    induction n with
    | zero => exact hx
    | succ n ih => exact I.lie_mem ih
  exact I.sum_mem (fun n _ => I.smul_mem _ (hi n))

end IdealReflections

section RootExtraction
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {R : Set E} {z : E} (b : Module.Basis ι ℝ E)

/-- A root vector in an ideal yields a simple positive generator. The
reflection induction uses actual inner exponentials, so it preserves ideals. -/
theorem e_mem_of_root_vector (hR : IsRootSystem R) (hz : RootRegular R z)
    (hb : IsSimpleBasis R z b)
    (hA : ∀ i j, (A i j : ℝ) = cartanMatrix b i j)
    (I : LieIdeal ℂ (Algebra A)) :
    ∀ a ∈ R, ∀ x : Algebra A, x ∈ I → x ≠ 0 →
      x ∈ weightSpace A (rootWeight b a) → ∃ j, e A j ∈ I := by
  have hC := cartanConditions_spec R hR z hz b hb A hA
  apply root_property_of_simple_reflections hR hz
    (fun a => ∀ x : Algebra A, x ∈ I → x ≠ 0 →
      x ∈ weightSpace A (rootWeight b a) → ∃ j, e A j ∈ I)
  · intro a ha
    obtain ⟨i, rfl⟩ := hb.symm ▸ ha
    intro x hx hxne hxw
    rw [simple_weightSpace_eq_span A b hA i] at hxw
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hxw
    have hcne : c ≠ 0 := by
      rintro rfl
      exact hxne (by simpa using hc.symm)
    exact ⟨i, (I.toSubmodule.smul_mem_iff hcne).mp (hc.symm ▸ hx)⟩
  · intro a ha y hy
    obtain ⟨i, rfl⟩ := hb.symm ▸ ha
    intro x hx hxne hxw
    let n := ((positiveExp A i).trans (negativeExp A i)).trans (positiveExp A i)
    apply hy (n x)
    · have hp {y : Algebra A} (hy : y ∈ I) : positiveExp A i y ∈ I :=
        innerExp_mem_ideal I (e A i) (e_locally_nilpotent A i) hy
      have hm {y : Algebra A} (hy : y ∈ I) : negativeExp A i y ∈ I :=
        innerExp_mem_ideal I (-(f A i))
          (neg_iterBracket_locally_nilpotent (f A i) (f_locally_nilpotent A i)) hy
      exact hp (hm (hp hx))
    · exact n.toLinearEquiv.map_ne_zero_iff.mpr hxne
    · have hw := map_mem_weightSpace_of_cartan_reflection A i (hC.1 i) n
        (exponential_reflection_cartan A i (hC.1 i)) hxw
      rwa [rootWeight_reflection A b hA i y, reflectWeight_involutive A i (hC.1 i)] at hw

/-- The Cartan matrix is invertible after extension to the complex scalars. -/
theorem complex_cartan_isUnit [Fintype ι] (hR : IsRootSystem R) (hz : RootRegular R z)
    (hb : IsSimpleBasis R z b)
    (hA : ∀ i j, (A i j : ℝ) = cartanMatrix b i j) :
    IsUnit (A.map (Int.castRingHom ℂ)) := by
  have hu : IsUnit (cartanMatrix b) :=
    isUnit_of_mul_isUnit_right (cartan_symmetrization R hR z hz b hb).2.2.isUnit
  have hm := hu.map (Complex.ofRealHom.mapMatrix (m := ι))
  convert hm using 1
  ext i j
  change (A i j : ℂ) = ((cartanMatrix b i j : ℝ) : ℂ)
  rw [← hA]
  simp

/-- A Cartan element annihilating all simple positive generators is zero. -/
theorem cartan_eq_zero_of_lie_e_eq_zero [Fintype ι]
    (hR : IsRootSystem R) (hz : RootRegular R z) (hb : IsSimpleBasis R z b)
    (hA : ∀ i j, (A i j : ℝ) = cartanMatrix b i j)
    {x : Algebra A} (hx : x ∈ cartan A) (heq : ∀ j, ⁅x, e A j⁆ = 0) : x = 0 := by
  have hC := cartanConditions_spec R hR z hz b hb A hA
  obtain ⟨bh, hbh⟩ := (triangular_of_cartanConditions A hC).2.1
  let c : ι → ℂ := fun i => bh.repr ⟨x,hx⟩ i
  have hxsum : ∑ i, c i • h A i = x := by
    simpa only [Submodule.coe_sum, Submodule.coe_smul, hbh] using
      congrArg Subtype.val (bh.sum_repr ⟨x,hx⟩)
  have hcoeff (j : ι) : ∑ i, c i * (A i j : ℂ) = 0 := by
    have hce (i j : ι) : ⁅h A i, e A j⁆ = (A i j : ℂ) • e A j := by
      simpa only [Int.cast_smul_eq_zsmul] using he A i j
    have hbr : ⁅x, e A j⁆ = (∑ i, c i * (A i j : ℂ)) • e A j := by
      rw [← hxsum]
      simp only [sum_lie, smul_lie, hce, smul_smul, Finset.sum_smul]
    have hzero := hbr.symm.trans (heq j)
    exact (smul_eq_zero.mp hzero).resolve_right
      ((triangular_of_cartanConditions A hC).2.2.2.2 j).1
  have hc : c = 0 := by
    apply (Matrix.vecMul_injective_of_isUnit (complex_cartan_isUnit A b hR hz hb hA))
    ext j
    simpa only [Matrix.vecMul, dotProduct, Matrix.map_apply, Int.coe_castRingHom,
      Pi.zero_apply, zero_mul, Finset.sum_const_zero] using hcoeff j
  rw [← hxsum, hc]
  simp

/-- The finite-type weight theorem and ideal-preserving reflections extract
a simple positive generator from every nonzero ideal, even for disconnected A. -/
theorem ideal_contains_e [Fintype ι]
    (hR : IsRootSystem R) (hz : RootRegular R z) (hb : IsSimpleBasis R z b)
    (hA : ∀ i j, (A i j : ℝ) = cartanMatrix b i j)
    (I : LieIdeal ℂ (Algebra A)) (hI : I ≠ ⊥) : ∃ j, e A j ∈ I := by
  obtain ⟨χ, x, hxI, hxne, hxw⟩ :=
    ideal_contains_weight_vector A (weightSpace_iSup_eq_top A) I hI
  by_cases hχ : χ = 0
  · subst χ
    have hxc : x ∈ cartan A := (zero_weightSpace_eq_cartan A b hA) ▸ hxw
    have hex : ∃ j, ⁅x, e A j⁆ ≠ 0 := by
      by_contra! hn
      exact hxne (cartan_eq_zero_of_lie_e_eq_zero A b hR hz hb hA hxc hn)
    obtain ⟨j, hj⟩ := hex
    apply e_mem_of_root_vector A b hR hz hb hA I (b j) (hb.root_mem j)
      ⁅x, e A j⁆ (lie_mem_left ℂ (Algebra A) I _ _ hxI) hj
    have hew : e A j ∈ weightSpace A (rootWeight b (b j)) := by
      rw [simple_weightSpace_eq_span A b hA j]
      exact Submodule.subset_span (Set.mem_singleton _)
    have hmem := lie_mem_weightSpace A hxw hew
    simpa using hmem
  · have hws : weightSpace A χ ≠ ⊥ := by
      intro hbot
      exact hxne (by simpa [hbot] using hxw)
    obtain ⟨a, ha, hχa⟩ := nonzero_weight_is_root A hR hz b hb hA hχ hws
    exact e_mem_of_root_vector A b hR hz hb hA I a ha x hxI hxne (hχa ▸ hxw)

/-- Connected finite-type Serre algebras are nonabelian simple. -/
theorem isSimple_spec :
    Specs.LieAlgebrasAndRepresentations.SerreSimplicity.simpleExpected.{u,v} := by
  intro E _ _ ι _ _ _ R hR z hz b hb A hA hconn
  exact isSimple_of_ideal_contains_e A (cartanConditions_spec R hR z hz b hb A hA)
    hconn (ideal_contains_e A b hR hz hb hA)

/-- Simplicity of a component follows inside the full root system. Mapping
an ideal forward and projecting back avoids assuming a root-system structure
on a component subtype. Other projections force the extracted generator to
belong to this component. -/
theorem component_ideal_contains_e [Fintype ι]
    (hR : IsRootSystem R) (hz : RootRegular R z) (hb : IsSimpleBasis R z b)
    (hA : ∀ i j, (A i j : ℝ) = cartanMatrix b i j)
    (c : Component A) (I : LieIdeal ℂ (Algebra (componentMatrix A c)))
    (hI : I ≠ ⊥) : ∃ i, e (componentMatrix A c) i ∈ I := by
  classical
  have hC := cartanConditions_spec R hR z hz b hb A hA
  let J := I.map (componentInclusion A hC.2.1 c)
  have hJ : J ≠ ⊥ := fun hzero => hI
    (LieIdeal.bot_of_map_eq_bot (componentInclusion_injective A hC.2.1 c) hzero)
  obtain ⟨j, hj⟩ := ideal_contains_e A b hR hz hb hA J hJ
  have hjc : componentOf A j = c := by
    by_contra hne
    have hle : J ≤ (componentProjection A hC.2.1 (componentOf A j)).ker := by
      apply LieIdeal.map_le_iff_le_comap.mpr
      intro x hx
      change componentProjection A hC.2.1 (componentOf A j)
        (componentInclusion A hC.2.1 c x) = 0
      exact LieHom.congr_fun (componentProjection_comp_inclusion_ne A hC.2.1 hne) x
    have hz := hle hj
    change componentProjection A hC.2.1 (componentOf A j) (e A j) = 0 at hz
    have hz' : e (componentMatrix A (componentOf A j)) ⟨j,rfl⟩ = 0 := by
      simpa [componentProjection_e, componentPart] using hz
    exact ((triangular_of_cartanConditions _
      (component_cartanConditions A hC (componentOf A j))).2.2.2.2 ⟨j,rfl⟩).1 hz'
  have hle : J ≤ LieIdeal.comap (componentProjection A hC.2.1 c) I := by
    apply LieIdeal.map_le_iff_le_comap.mpr
    intro x hx
    change componentProjection A hC.2.1 c (componentInclusion A hC.2.1 c x) ∈ I
    have heq := LieHom.congr_fun (componentProjection_comp_inclusion A hC.2.1 c) x
    exact heq.symm ▸ hx
  have hm := hle hj
  change componentProjection A hC.2.1 c (e A j) ∈ I at hm
  refine ⟨⟨j,hjc⟩, ?_⟩
  simpa only [componentProjection_e, componentPart, dite_eq_left hjc] using hm

/-- Every actual connected component factor is nonabelian simple. -/
theorem componentSimple_spec :
    Specs.LieAlgebrasAndRepresentations.SerreSimplicity.componentSimpleExpected.{u,v} := by
  classical
  intro E _ _ ι _ _ R hR z hz b hb A hA c
  have hC := cartanConditions_spec R hR z hz b hb A hA
  haveI := component_nonempty A c
  exact isSimple_of_ideal_contains_e (componentMatrix A c)
    (component_cartanConditions A hC c) (component_connected A c)
    (component_ideal_contains_e A b hR hz hb hA c)

end RootExtraction

end LieAlgebrasAndRepresentations.Serre
