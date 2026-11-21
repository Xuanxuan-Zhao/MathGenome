import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Matroid.ForwardPresentations
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.ParallelClasses

/-! Parallel classes and a choice of their nonloop representatives (W68).
We identify parallelism with singleton closure equality, then choose one point
of each such class. The map is defined on the nonloop subtype, even when empty. -/
namespace FiniteCombinatorics.Matroid
open Set
universe u
variable {α : Type u}

def ParallelRelated (M : _root_.Matroid α) [M.Finite] (e f : α) : Prop :=
  e = f ∨ (e ≠ f ∧ rank M {e, f} = 1)

def nonloopClosureSetoid (M : _root_.Matroid α) : Setoid {e // M.IsNonloop e} :=
  Expected.nonloopClosureSetoid M

noncomputable def parallelRepresentative (M : _root_.Matroid α)
    (e : {e // M.IsNonloop e}) : {e // M.IsNonloop e} :=
  (Quotient.mk (nonloopClosureSetoid M) e).out

noncomputable def parallelRepresentatives (M : _root_.Matroid α) : Set α :=
  Set.range (fun e : {e // M.IsNonloop e} => (parallelRepresentative M e).val)

def IsParallelRepresentativeSet (M : _root_.Matroid α) [M.Finite] (S : Set α) : Prop :=
  (∀ s ∈ S, M.IsNonloop s) ∧
    ∀ e, M.IsNonloop e → ∃! s, s ∈ S ∧ ParallelRelated M e s

noncomputable def parallelImage (M : _root_.Matroid α) (A : Set α) : Set α :=
  (fun e : {e // M.IsNonloop e} => (parallelRepresentative M e).val) ''
    {e | e.val ∈ A}

theorem nonloopCharacterization (M : _root_.Matroid α) (e : α) :
    M.IsNonloop e ↔ e ∈ M.E ∧ ¬ M.IsCircuit {e} := by
  rw [_root_.Matroid.singleton_isCircuit, _root_.Matroid.isNonloop_iff, and_comm]

private theorem nonloop_rank_singleton (M : _root_.Matroid α) [M.Finite]
    {e : α} (he : M.IsNonloop e) : rank M {e} = 1 := by
  simp [rank, he.eRk_eq]

/-- A nonloop pair has rank one exactly when its singleton closures agree. -/
private theorem pair_rank_one_iff (M : _root_.Matroid α) [M.Finite]
    {e f : α} (he : M.IsNonloop e) (hf : M.IsNonloop f) :
    rank M {e, f} = 1 ↔ M.closure {e} = M.closure {f} := by
  have hr := nonloop_rank_singleton M hf
  have hc := closureRank M {f} (singleton_subset_iff.mpr hf.mem_ground) e he.mem_ground
  constructor
  · intro h
    apply he.closure_eq_of_mem_closure
    exact hc.mpr (h.trans hr.symm)
  · intro h
    have hemem : e ∈ M.closure {f} := h ▸ M.mem_closure_self e
    exact (hc.mp hemem).trans hr

theorem parallelClosure (M : _root_.Matroid α) [M.Finite]
    {e f : α} (he : M.IsNonloop e) (hf : M.IsNonloop f) :
    ParallelRelated M e f ↔ M.closure {e} = M.closure {f} := by
  constructor
  · rintro (rfl | ⟨_, h⟩)
    · rfl
    · exact (pair_rank_one_iff M he hf).mp h
  · intro h
    by_cases hef : e = f
    · exact Or.inl hef
    · exact Or.inr ⟨hef, (pair_rank_one_iff M he hf).mpr h⟩

theorem parallelRankCriterion (M : _root_.Matroid α) [M.Finite]
    {e f : α} (_he : M.IsNonloop e) (_hf : M.IsNonloop f) (hef : e ≠ f) :
    ParallelRelated M e f ↔ rank M {e, f} = 1 := by
  simp [ParallelRelated, hef]

theorem parallelEquivalence (M : _root_.Matroid α) [M.Finite] :
    Equivalence (fun e f : {e // M.IsNonloop e} => ParallelRelated M e.val f.val) := by
  refine ⟨fun e => Or.inl rfl, ?_, ?_⟩
  · intro e f h
    exact (parallelClosure M f.property e.property).mpr
      ((parallelClosure M e.property f.property).mp h).symm
  · intro e f g hef hfg
    exact (parallelClosure M e.property g.property).mpr
      (((parallelClosure M e.property f.property).mp hef).trans
        ((parallelClosure M f.property g.property).mp hfg))

private theorem representative_closure (M : _root_.Matroid α)
    (e : {e // M.IsNonloop e}) :
    M.closure {(parallelRepresentative M e).val} = M.closure {e.val} := by
  exact Quotient.mk_out (s := nonloopClosureSetoid M) e

theorem parallelRepresentative_related (M : _root_.Matroid α) [M.Finite]
    (e : {e // M.IsNonloop e}) :
    ParallelRelated M e.val (parallelRepresentative M e).val := by
  exact (parallelClosure M e.property (parallelRepresentative M e).property).mpr
    (representative_closure M e).symm

theorem parallelRepresentative_eq_iff (M : _root_.Matroid α) [M.Finite]
    (e f : {e // M.IsNonloop e}) :
    parallelRepresentative M e = parallelRepresentative M f ↔ ParallelRelated M e.val f.val := by
  rw [parallelClosure M e.property f.property]
  constructor
  · intro h
    exact (representative_closure M e).symm.trans
      ((congrArg (fun x : {e // M.IsNonloop e} => M.closure {x.val}) h).trans
        (representative_closure M f))
  · intro h
    exact congrArg Quotient.out (Quotient.sound (s := nonloopClosureSetoid M) h)

theorem parallelRepresentative_mem (M : _root_.Matroid α)
    (e : {e // M.IsNonloop e}) :
    (parallelRepresentative M e).val ∈ parallelRepresentatives M :=
  ⟨e, rfl⟩

theorem parallelRepresentatives_ground (M : _root_.Matroid α) :
    parallelRepresentatives M ⊆ M.E := by
  rintro s ⟨e, rfl⟩
  exact (parallelRepresentative M e).property.mem_ground

theorem parallelRepresentatives_spec (M : _root_.Matroid α) [M.Finite] :
    IsParallelRepresentativeSet M (parallelRepresentatives M) := by
  refine ⟨?_, ?_⟩
  · rintro s ⟨e, rfl⟩
    exact (parallelRepresentative M e).property
  · intro e he
    refine ⟨(parallelRepresentative M ⟨e, he⟩).val,
      ⟨parallelRepresentative_mem M ⟨e, he⟩, parallelRepresentative_related M ⟨e, he⟩⟩, ?_⟩
    rintro s ⟨⟨f, rfl⟩, h⟩
    have hcl := (parallelClosure M he (parallelRepresentative M f).property).mp h
    have hef : ParallelRelated M e f.val :=
      (parallelClosure M he f.property).mpr (hcl.trans (representative_closure M f))
    exact congrArg Subtype.val ((parallelRepresentative_eq_iff M ⟨e, he⟩ f).mpr hef).symm

theorem parallelRepresentative_fixed (M : _root_.Matroid α) [M.Finite]
    (s : {e // M.IsNonloop e}) (hs : s.val ∈ parallelRepresentatives M) :
    parallelRepresentative M s = s := by
  obtain ⟨f, hf⟩ := hs
  have h : ParallelRelated M s.val f.val :=
    (parallelClosure M s.property f.property).mpr
      (by rw [← hf]; exact representative_closure M f)
  exact ((parallelRepresentative_eq_iff M s f).mpr h).trans (Subtype.ext hf)

theorem parallelImage_mem (M : _root_.Matroid α) (A : Set α) (s : α) :
    s ∈ parallelImage M A ↔
      ∃ e : {e // M.IsNonloop e}, e.val ∈ A ∧ (parallelRepresentative M e).val = s :=
  Iff.rfl

theorem parallelImage_subset (M : _root_.Matroid α) (A : Set α) :
    parallelImage M A ⊆ parallelRepresentatives M := by
  rintro s ⟨e, _, rfl⟩
  exact parallelRepresentative_mem M e

theorem parallelRepresentatives_finite (M : _root_.Matroid α) [M.Finite] :
    (parallelRepresentatives M).Finite :=
  M.ground_finite.subset (parallelRepresentatives_ground M)

theorem parallelRepresentatives_empty (M : _root_.Matroid α)
    (hM : ∀ e ∈ M.E, M.IsLoop e) : parallelRepresentatives M = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro s ⟨e, rfl⟩
  exact e.property.not_isLoop (hM e.val e.property.mem_ground)

theorem parallelImage_empty (M : _root_.Matroid α) (A : Set α)
    (hA : ∀ e ∈ A, ¬ M.IsNonloop e) : parallelImage M A = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro s ⟨e, he, _⟩
  exact hA e.val he e.property

end FiniteCombinatorics.Matroid
