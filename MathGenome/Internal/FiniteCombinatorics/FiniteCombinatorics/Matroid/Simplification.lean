import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Matroid.ParallelClasses
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.Simplification

/-! Simplification (W68). The representative image and A span the same closure:
loops lie in every closure, and a nonloop and its representative have equal
singleton closures. Restriction then gives both displayed identities. -/
namespace FiniteCombinatorics.Matroid
open Set
open scoped _root_.Matroid
universe u
variable {α : Type u}

def representativeImage (M : _root_.Matroid α)
    (q : {e // M.IsNonloop e} → α) (A : Set α) : Set α :=
  q '' {e | e.val ∈ A}

def IsRepresentativeMap (M : _root_.Matroid α) [M.Finite] (S : Set α)
    (q : {e // M.IsNonloop e} → α) : Prop :=
  ∀ e, q e ∈ S ∧ ParallelRelated M e.val (q e)

def IsSimple (M : _root_.Matroid α) [M.Finite] : Prop :=
  (∀ e ∈ M.E, M.IsNonloop e) ∧
    ∀ e ∈ M.E, ∀ f ∈ M.E, ParallelRelated M e f → e = f

theorem representativeSet_ground (M : _root_.Matroid α) [M.Finite]
    {S : Set α} (hS : IsParallelRepresentativeSet M S) : S ⊆ M.E :=
  fun s hs => (hS.1 s hs).mem_ground

theorem representativeImage_subset (M : _root_.Matroid α) [M.Finite]
    {S : Set α} {q : {e // M.IsNonloop e} → α}
    (hq : IsRepresentativeMap M S q) (A : Set α) : representativeImage M q A ⊆ S := by
  rintro s ⟨e, _, rfl⟩
  exact (hq e).1

theorem representativeChoice (M : _root_.Matroid α) [M.Finite] :
    ∃ (S : Set α) (q : {e // M.IsNonloop e} → α),
      IsParallelRepresentativeSet M S ∧ IsRepresentativeMap M S q := by
  exact ⟨parallelRepresentatives M, fun e => (parallelRepresentative M e).val,
    parallelRepresentatives_spec M,
    fun e => ⟨parallelRepresentative_mem M e, parallelRepresentative_related M e⟩⟩

theorem representativeClosure (M : _root_.Matroid α) [M.Finite]
    (S : Set α) (q : {e // M.IsNonloop e} → α)
    (hS : IsParallelRepresentativeSet M S) (hq : IsRepresentativeMap M S q)
    (A : Set α) (hA : A ⊆ M.E) :
    M.closure (representativeImage M q A) = M.closure A := by
  apply Subset.antisymm
  · apply M.closure_subset_closure_of_subset_closure
    rintro s ⟨e, heA, rfl⟩
    have hc := (parallelClosure M e.property (hS.1 _ (hq e).1)).mp (hq e).2
    apply M.closure_subset_closure (singleton_subset_iff.mpr heA)
    rw [hc]
    exact M.mem_closure_self (q e) (hS.1 _ (hq e).1).mem_ground
  · apply M.closure_subset_closure_of_subset_closure
    intro e heA
    rcases M.isLoop_or_isNonloop e (hA heA) with he | he
    · exact he.mem_closure _
    · have hc := (parallelClosure M he (hS.1 _ (hq ⟨e, he⟩).1)).mp (hq ⟨e, he⟩).2
      have hmem : q ⟨e, he⟩ ∈ representativeImage M q A := ⟨⟨e, he⟩, heA, rfl⟩
      apply M.closure_subset_closure (singleton_subset_iff.mpr hmem)
      rw [← hc]
      exact M.mem_closure_self e

theorem simplificationSimple (M : _root_.Matroid α) [M.Finite]
    (S : Set α) (hS : IsParallelRepresentativeSet M S) :
    letI : (M ↾ S).Finite := M.restrict_finite
      (M.ground_finite.subset (fun s hs => (hS.1 s hs).mem_ground))
    IsSimple (M ↾ S) := by
  letI : (M ↾ S).Finite := M.restrict_finite
    (M.ground_finite.subset (representativeSet_ground M hS))
  refine ⟨fun e he => _root_.Matroid.restrict_isNonloop_iff.mpr ⟨hS.1 e he, he⟩, ?_⟩
  intro e he f hf hef
  have hr : rank (M ↾ S) {e, f} = rank M {e, f} := by
    unfold rank
    rw [M.restrict_eRk_eq (by simp only [pair_subset_iff]; exact ⟨he, hf⟩)]
  have hrel : ParallelRelated M e f := by
    rcases hef with h | ⟨hne, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨hne, hr ▸ h⟩
  obtain ⟨s, _, huniq⟩ := hS.2 e (hS.1 e he)
  exact (huniq e ⟨he, Or.inl rfl⟩).trans (huniq f ⟨hf, hrel⟩).symm

theorem simplificationRank (M : _root_.Matroid α) [M.Finite]
    (S : Set α) (hS : IsParallelRepresentativeSet M S)
    (q : {e // M.IsNonloop e} → α) (hq : IsRepresentativeMap M S q)
    (A : Set α) (hA : A ⊆ M.E) :
    letI : (M ↾ S).Finite := M.restrict_finite
      (M.ground_finite.subset (fun s hs => (hS.1 s hs).mem_ground))
    rank (M ↾ S) (representativeImage M q A) = rank M A := by
  letI : (M ↾ S).Finite := M.restrict_finite
    (M.ground_finite.subset (representativeSet_ground M hS))
  unfold rank
  rw [M.restrict_eRk_eq (representativeImage_subset M hq A),
    ← M.eRk_closure_eq (representativeImage M q A), representativeClosure M S q hS hq A hA,
    M.eRk_closure_eq]

theorem simplificationClosure (M : _root_.Matroid α) [M.Finite]
    (S : Set α) (q : {e // M.IsNonloop e} → α)
    (hS : IsParallelRepresentativeSet M S) (hq : IsRepresentativeMap M S q)
    (A : Set α) (hA : A ⊆ M.E) :
    (M ↾ S).closure (representativeImage M q A) = M.closure A ∩ S := by
  rw [M.restrict_closure_eq (representativeImage_subset M hq A) (representativeSet_ground M hS),
    representativeClosure M S q hS hq A hA]

theorem simplificationAllLoops (M : _root_.Matroid α) [M.Finite]
    (S : Set α) (q : {e // M.IsNonloop e} → α)
    (hS : IsParallelRepresentativeSet M S) (hM : ∀ e ∈ M.E, M.IsLoop e) :
    S = ∅ ∧ ∀ A, representativeImage M q A = ∅ := by
  constructor
  · apply Set.eq_empty_iff_forall_notMem.mpr
    intro s hs
    exact (hS.1 s hs).not_isLoop (hM s (hS.1 s hs).mem_ground)
  · intro A
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro s ⟨e, _, _⟩
    exact e.property.not_isLoop (hM e.val e.property.mem_ground)

theorem simplificationRankZero (M : _root_.Matroid α) [M.Finite]
    (S : Set α) (q : {e // M.IsNonloop e} → α)
    (hS : IsParallelRepresentativeSet M S) (hM : rank M M.E = 0) :
    S = ∅ ∧ ∀ A, representativeImage M q A = ∅ := by
  apply simplificationAllLoops M S q hS
  have hn : (M.eRk M.E).toNat = 0 := by
    unfold rank at hM
    exact_mod_cast hM
  have hz : M.eRk M.E = 0 := by rw [← finiteRankBridge M M.E, hn]; rfl
  exact fun e he => (M.eRk_eq_zero_iff Subset.rfl).mp hz he

theorem simplificationEmptyGround (M : _root_.Matroid α) [M.Finite]
    (S : Set α) (q : {e // M.IsNonloop e} → α)
    (hS : IsParallelRepresentativeSet M S) (hM : M.E = ∅) :
    S = ∅ ∧ ∀ A, representativeImage M q A = ∅ := by
  apply simplificationAllLoops M S q hS
  intro e he
  rw [hM] at he
  exact he.elim

theorem canonicalRepresentativeMap (M : _root_.Matroid α) [M.Finite] :
    IsRepresentativeMap M (parallelRepresentatives M)
      (fun e => (parallelRepresentative M e).val) ∧
    ∀ A, representativeImage M (fun e => (parallelRepresentative M e).val) A = parallelImage M A := by
  exact ⟨fun e => ⟨parallelRepresentative_mem M e, parallelRepresentative_related M e⟩,
    fun _ => rfl⟩

end FiniteCombinatorics.Matroid
