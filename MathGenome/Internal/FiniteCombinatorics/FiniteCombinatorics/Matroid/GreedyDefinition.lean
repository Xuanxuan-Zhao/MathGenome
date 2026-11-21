import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Matroid.Foundation
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.GreedyDefinition

/-! Weighted greedy selection, paper.tex W78. No augmentation assumption is used.
The algorithm scans every element, even with negative weight. Deleting negative
weights is a separate restriction for the independent-set objective. -/
namespace FiniteCombinatorics.Matroid
open Set
universe u
variable {α : Type u} {E : Set α}

/-- Each ground element occurs once, ordered by descending weight and then tie order. -/
noncomputable def greedyEnumeration (S : IndependenceSystem E) (w : E → ℝ)
    (tie : LinearOrder E) : List E := by
  classical
  letI := S.finite_ground.fintype
  exact Finset.univ.sort (WeightTieBefore w tie)

/-- The weight of a subset of E; values on arbitrary ambient sets ignore points off E. -/
noncomputable def subsetWeight (S : IndependenceSystem E) (w : E → ℝ)
    (A : Set α) : ℝ := by
  classical
  letI := S.finite_ground.fintype
  exact ∑ e : E, if (e : α) ∈ A then w e else 0

/-- One greedy step, including elements with negative weight. -/
noncomputable def greedyStep (S : IndependenceSystem E) (I : Set α) (e : E) : Set α := by
  classical
  exact if S.Indep (insert (e : α) I) then insert (e : α) I else I

/-- I_i: perform precisely the first i steps (saturating after the last element). -/
noncomputable def greedyState (S : IndependenceSystem E) (w : E → ℝ)
    (tie : LinearOrder E) (i : ℕ) : Set α :=
  ((greedyEnumeration S w tie).take i).foldl (greedyStep S) ∅

/-- Return I_n after scanning all n elements. -/
noncomputable def greedyOutput (S : IndependenceSystem E) (w : E → ℝ)
    (tie : LinearOrder E) : Set α :=
  greedyState S w tie (greedyEnumeration S w tie).length

/-- P_i is the set of elements in the first i positions, with P_0 empty. -/
noncomputable def greedyPrefix (S : IndependenceSystem E) (w : E → ℝ)
    (tie : LinearOrder E) (i : ℕ) : Set α :=
  {x | ∃ e ∈ (greedyEnumeration S w tie).take i, (e : α) = x}

/-- Feasibility includes maximality by inclusion, using the shared foundation predicate. -/
noncomputable def BasisOptimal (S : IndependenceSystem E) (w : E → ℝ)
    (I : Set α) : Prop :=
  MaximalIndependent S I ∧
    ∀ J, MaximalIndependent S J → subsetWeight S w J ≤ subsetWeight S w I

/-- Independent-set optimization allows all cardinalities. -/
noncomputable def IndependentOptimal (S : IndependenceSystem E) (w : E → ℝ)
    (I : Set α) : Prop :=
  S.Indep I ∧ ∀ J, S.Indep J → subsetWeight S w J ≤ subsetWeight S w I

/-- Zero-weight elements are retained. -/
def nonnegativeGround (w : E → ℝ) : Set α :=
  {x | ∃ hx : x ∈ E, 0 ≤ w ⟨x, hx⟩}

/-- Delete negative-weight elements; do not change the ambient type or independence test. -/
def nonnegativeRestriction (S : IndependenceSystem E) (w : E → ℝ) :
    IndependenceSystem (nonnegativeGround w) where
  finite_ground := S.finite_ground.subset (fun _ h => h.choose)
  Indep I := S.Indep I ∧ I ⊆ nonnegativeGround w
  empty_indep := ⟨S.empty_indep, empty_subset _⟩
  hereditary := fun {_ _} h hIJ => ⟨S.hereditary h.1 hIJ, hIJ.trans h.2⟩
  subset_ground := fun {_} h => h.2

/-- The unchanged weight function on the restricted ground. -/
def nonnegativeWeight (w : E → ℝ) (e : nonnegativeGround w) : ℝ :=
  w ⟨e.val, e.property.choose⟩

/-- Restrict the original tie order along the inclusion of the nonnegative ground. -/
@[instance_reducible] noncomputable def nonnegativeTie (w : E → ℝ) (tie : LinearOrder E) :
    LinearOrder (nonnegativeGround w) := by
  letI := tie
  exact LinearOrder.lift' (fun e : nonnegativeGround w =>
    (⟨e.val, e.property.choose⟩ : E)) (by
      intro a b h
      apply Subtype.ext
      exact congrArg (fun x : E => (x : α)) h)

/-- Greedy on the nonnegative restriction, with the inherited weights and tie order. -/
noncomputable def nonnegativeGreedyOutput (S : IndependenceSystem E) (w : E → ℝ)
    (tie : LinearOrder E) : Set α :=
  greedyOutput (nonnegativeRestriction S w) (nonnegativeWeight w) (nonnegativeTie w tie)

theorem greedyEnumeration_nodup :
  ∀ {α : Type u} {E : Set α}, ∀ (S : IndependenceSystem E) (w : E → ℝ) (tie : LinearOrder E), (greedyEnumeration S w tie).Nodup := by
  intro α E S w tie
  classical
  unfold greedyEnumeration
  exact Finset.sort_nodup _ _

theorem greedyEnumeration_mem :
  ∀ {α : Type u} {E : Set α}, ∀ (S : IndependenceSystem E) (w : E → ℝ) (tie : LinearOrder E), ∀ e : E, e ∈ greedyEnumeration S w tie := by
  intro α E S w tie e
  classical
  simp [greedyEnumeration]

theorem greedyEnumeration_pairwise :
  ∀ {α : Type u} {E : Set α}, ∀ (S : IndependenceSystem E) (w : E → ℝ) (tie : LinearOrder E), (greedyEnumeration S w tie).Pairwise (WeightTieBefore w tie) := by
  intro α E S w tie
  classical
  unfold greedyEnumeration
  exact Finset.pairwise_sort _ _

theorem greedyState_zero :
  ∀ {α : Type u} {E : Set α}, ∀ (S : IndependenceSystem E) (w : E → ℝ) (tie : LinearOrder E), greedyState S w tie 0 = ∅ := by
  intro α E S w tie
  simp [greedyState]

theorem greedyState_succ :
  ∀ {α : Type u} {E : Set α}, ∀ (S : IndependenceSystem E) (w : E → ℝ) (tie : LinearOrder E), ∀ (i : ℕ) (e : E), (greedyEnumeration S w tie)[i]? = some e →
    greedyState S w tie (i + 1) = greedyStep S (greedyState S w tie i) e := by
  intro α E S w tie i e h
  simp [greedyState, List.take_add_one, h, List.foldl_append]

theorem greedyStep_accept :
  ∀ {α : Type u} {E : Set α}, ∀ (S : IndependenceSystem E) (I : Set α) (e : E),
    S.Indep (insert (e : α) I) → greedyStep S I e = insert (e : α) I := by
  intro α E S I e h
  classical
  simp [greedyStep, h]

theorem greedyStep_reject :
  ∀ {α : Type u} {E : Set α}, ∀ (S : IndependenceSystem E) (I : Set α) (e : E),
    ¬ S.Indep (insert (e : α) I) → greedyStep S I e = I := by
  intro α E S I e h
  classical
  simp [greedyStep, h]

theorem greedyPrefix_zero :
  ∀ {α : Type u} {E : Set α}, ∀ (S : IndependenceSystem E) (w : E → ℝ) (tie : LinearOrder E), greedyPrefix S w tie 0 = ∅ := by
  intro α E S w tie
  ext x
  simp [greedyPrefix]

theorem greedyPrefix_full :
  ∀ {α : Type u} {E : Set α}, ∀ (S : IndependenceSystem E) (w : E → ℝ) (tie : LinearOrder E), greedyPrefix S w tie (greedyEnumeration S w tie).length = E := by
  intro α E S w tie
  ext x
  constructor
  · rintro ⟨e, _, rfl⟩
    exact e.property
  · intro hx
    exact ⟨⟨x, hx⟩, by simpa using greedyEnumeration_mem S w tie ⟨x, hx⟩, rfl⟩

theorem subsetWeight_empty :
  ∀ {α : Type u} {E : Set α}, ∀ (S : IndependenceSystem E) (w : E → ℝ), subsetWeight S w ∅ = 0 := by
  intro α E S w
  classical
  simp [subsetWeight]

theorem nonnegativeRestriction_indep :
  ∀ {α : Type u} {E : Set α}, ∀ (S : IndependenceSystem E) (w : E → ℝ) (I : Set α),
    (nonnegativeRestriction S w).Indep I ↔ S.Indep I ∧ I ⊆ nonnegativeGround w := by
  intro α E S w I
  rfl

theorem greedyOutput_empty :
  ∀ {α : Type u} (S : IndependenceSystem (∅ : Set α))
    (w : (∅ : Set α) → ℝ) (tie : LinearOrder (∅ : Set α)), greedyOutput S w tie = ∅ := by
  intro α S w tie
  classical
  have h : greedyEnumeration S w tie = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro e he
    exact e.property
  simp [greedyOutput, greedyState, h]


end FiniteCombinatorics.Matroid
