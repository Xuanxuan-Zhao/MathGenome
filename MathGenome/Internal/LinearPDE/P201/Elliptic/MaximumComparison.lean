import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.MaximumComparison
import MathGenome.Internal.LinearPDE.P201.Elliptic.StrongMaximum

noncomputable section
open Set TopologicalSpace
open scoped ContDiff
namespace P201.Elliptic
open P201Specs.Elliptic

/-- A nonempty bounded open set in positive-dimensional Euclidean space has
nonempty boundary. No boundary smoothness is needed. -/
theorem boundedOpen_frontier_nonempty {n : ℕ} (hn : 1 ≤ n)
    {Ω : P201Specs.Domain n} (hb : Bornology.IsBounded (Ω : Set (P201Specs.Space n)))
    (hne : (Ω : Set (P201Specs.Space n)).Nonempty) :
    (frontier (Ω : Set (P201Specs.Space n))).Nonempty := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  apply nonempty_frontier_iff.mpr
  refine ⟨hne, ?_⟩
  intro heq
  exact NormedSpace.unbounded_univ ℝ (P201Specs.Space n) (heq ▸ hb)

/-- Compactness upgrades an interior constancy principle to a boundary bound.
The input constancy principle is invoked only at a maximum above the proposed
boundary bound. Continuity propagates that constant to the boundary. -/
theorem boundaryBound_of_interior_constancy {n : ℕ} (hn : 1 ≤ n)
    {Ω : P201Specs.Domain n} (hb : Bornology.IsBounded (Ω : Set (P201Specs.Space n)))
    {u : P201Specs.Space n → ℝ} (hu : ContinuousOn u (closure (Ω : Set _)))
    {M : ℝ} (hboundary : ∀ x ∈ frontier (Ω : Set _), u x ≤ M)
    (hstrong : ∀ z ∈ (Ω : Set _), M < u z → IsMaxOn u (Ω : Set _) z →
      ∀ x ∈ (Ω : Set _), u x = u z) :
    ∀ x ∈ (Ω : Set _), u x ≤ M := by
  intro x hx
  by_contra hnot
  obtain ⟨z, hz, hmax⟩ := hb.isCompact_closure.exists_isMaxOn
    ⟨x, subset_closure hx⟩ hu
  have hzM : M < u z := (lt_of_not_ge hnot).trans_le (hmax (subset_closure hx))
  have hzΩ : z ∈ (Ω : Set _) := by
    by_contra hznot
    have hzfront : z ∈ frontier (Ω : Set _) := by
      rw [frontier, Ω.isOpen.interior_eq]
      exact ⟨hz, hznot⟩
    exact (hboundary z hzfront).not_gt hzM
  have hconst := hstrong z hzΩ hzM (fun y hy => hmax (subset_closure hy))
  obtain ⟨y, hy⟩ := boundedOpen_frontier_nonempty hn hb ⟨x, hx⟩
  have hzle : u z ≤ u y :=
    le_on_closure (fun t ht => (hconst t ht).ge) continuousOn_const hu
      (frontier_subset_closure hy)
  exact (hzle.trans (hboundary y hy)).not_gt hzM

/-- Pointwise weak principle, useful even when the domain is empty. -/
theorem weakMaximumBoundaryBound {n : ℕ} (hn : 1 ≤ n)
    {Ω : P201Specs.Domain n} (hb : Bornology.IsBounded (Ω : Set (P201Specs.Space n)))
    (hconn : IsPreconnected (Ω : Set (P201Specs.Space n)))
    {a : P201Specs.Space n → Matrix (Fin n) (Fin n) ℝ}
    {b : P201Specs.Space n → P201Specs.Space n} {c u : P201Specs.Space n → ℝ}
    (hcoeff : EllipticCoefficients Ω a b c) (hc : ∀ x ∈ (Ω : Set _), c x ≤ 0)
    (hu : ContDiffOn ℝ 2 u (Ω : Set _))
    (hclosure : ContinuousOn u (closure (Ω : Set _)))
    (hLu : ∀ x ∈ (Ω : Set _), 0 ≤ nondivergenceOperator a b c u x)
    {M : ℝ} (hM : 0 ≤ M) (hboundary : ∀ x ∈ frontier (Ω : Set _), u x ≤ M) :
    ∀ x ∈ (Ω : Set _), u x ≤ M := by
  apply boundaryBound_of_interior_constancy hn hb hclosure hboundary
  intro z hz hMz hmax
  exact strongMaximum n hn Ω hb ⟨⟨z, hz⟩, hconn⟩ a b c u hcoeff hc hu hclosure hLu
    z hz (hM.trans hMz.le) hmax

/-- The zero-order-free pointwise bound permits an arbitrary real boundary bound. -/
theorem weakMaximumZeroOrderFreeBoundaryBound {n : ℕ} (hn : 1 ≤ n)
    {Ω : P201Specs.Domain n} (hb : Bornology.IsBounded (Ω : Set (P201Specs.Space n)))
    (hconn : IsPreconnected (Ω : Set (P201Specs.Space n)))
    {a : P201Specs.Space n → Matrix (Fin n) (Fin n) ℝ}
    {b : P201Specs.Space n → P201Specs.Space n} {c u : P201Specs.Space n → ℝ}
    (hcoeff : EllipticCoefficients Ω a b c) (hc : ∀ x ∈ (Ω : Set _), c x = 0)
    (hu : ContDiffOn ℝ 2 u (Ω : Set _))
    (hclosure : ContinuousOn u (closure (Ω : Set _)))
    (hLu : ∀ x ∈ (Ω : Set _), 0 ≤ nondivergenceOperator a b c u x)
    {M : ℝ} (hboundary : ∀ x ∈ frontier (Ω : Set _), u x ≤ M) :
    ∀ x ∈ (Ω : Set _), u x ≤ M := by
  apply boundaryBound_of_interior_constancy hn hb hclosure hboundary
  intro z hz _hMz hmax
  exact strongMaximumZeroOrderFree n hn Ω hb ⟨⟨z, hz⟩, hconn⟩ a b c u
    hcoeff hc hu hclosure hLu z hz hmax

/-- Weak maximum principle with c ≤ 0 and no global coefficient upper bounds. -/
theorem weakMaximum : P201Specs.Elliptic.weakMaximumStatement := by
  intro n hn Ω hb hconn a b c u hcoeff hc hu hclosure hLu
  rcases (Ω : Set (P201Specs.Space n)).eq_empty_or_nonempty with he | hne
  · simp only [he, image_empty, frontier_empty]
    exact le_max_right _ _
  have hbd : BddAbove (u '' frontier (Ω : Set _)) :=
    hb.isCompact_closure.bddAbove_image hclosure |>.mono
      (image_mono frontier_subset_closure)
  apply csSup_le (hne.image u)
  rintro _ ⟨x, hx, rfl⟩
  apply weakMaximumBoundaryBound hn hb hconn hcoeff hc hu hclosure hLu (le_max_left _ _)
    (fun y hy => (le_csSup hbd (mem_image_of_mem u hy)).trans (le_max_right _ _)) x hx

/-- The sharper supremum bound for c = 0, including arbitrary signs. -/
theorem weakMaximumZeroOrderFree : P201Specs.Elliptic.weakMaximumZeroOrderFreeStatement := by
  intro n hn Ω hb hconn a b c u hcoeff hc hu hclosure hLu
  rcases (Ω : Set (P201Specs.Space n)).eq_empty_or_nonempty with he | hne
  · simp only [he, image_empty, frontier_empty, le_refl]
  have hbd : BddAbove (u '' frontier (Ω : Set _)) :=
    hb.isCompact_closure.bddAbove_image hclosure |>.mono
      (image_mono frontier_subset_closure)
  apply csSup_le (hne.image u)
  rintro _ ⟨x, hx, rfl⟩
  apply weakMaximumZeroOrderFreeBoundaryBound hn hb hconn hcoeff hc hu hclosure hLu
    (fun y hy => le_csSup hbd (mem_image_of_mem u hy)) x hx

/-- Comparison follows by applying the pointwise bound to the actual difference. -/
theorem comparison : P201Specs.Elliptic.comparisonStatement := by
  intro n hn Ω hb hconn a b c u v hcoeff hc hu hclosureu hv hclosurev hL hboundary x hx
  have hLdiff : ∀ y ∈ (Ω : Set _),
      0 ≤ nondivergenceOperator a b c (fun z => u z - v z) y := by
    intro y hy
    have he := nondivergenceOperator_mul_sub a b c hu hv 1 hy
    simp only [one_mul] at he
    rw [he]
    exact sub_nonneg.mpr (hL y hy)
  exact sub_nonpos.mp (weakMaximumBoundaryBound hn hb hconn hcoeff hc (hu.sub hv)
    (hclosureu.sub hclosurev) hLdiff (le_refl 0)
    (fun y hy => sub_nonpos.mpr (hboundary y hy)) x hx)

/-- The full source theorem, retaining both upstream strong maximum clauses. -/
theorem classicalComparison : P201Specs.Elliptic.classicalComparisonStatement :=
  ⟨weakMaximum, strongMaximum, weakMaximumZeroOrderFree, strongMaximumZeroOrderFree,
    comparison⟩

end P201.Elliptic
