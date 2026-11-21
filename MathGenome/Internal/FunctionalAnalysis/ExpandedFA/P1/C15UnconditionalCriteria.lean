import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C15UnconditionalCriteria
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C15Unconditional
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.AbsoluteUnconditionalBoundary
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Logic.Equiv.Fintype

/-!
Tail, subseries and permutation criteria for unconditional convergence.
For the two converse implications, Baire supplies uniform Cauchy estimates
on a finite cylinder of selections or permutations. An arbitrary finite
late block can be inserted into that cylinder, proving the tail condition.
No common sum is assumed: its existence and independence are conclusions.
-/

open Filter
open scoped Topology
noncomputable section
namespace ExpandedFA.P1.C15UnconditionalCriteria

open C15Unconditional

def FiniteTailCondition : Spec.FiniteTailConditionType := @Spec.FiniteTailConditionValue

def EverySubseriesConverges : Spec.EverySubseriesConvergesType :=
  @Spec.EverySubseriesConvergesValue

def EveryRearrangementConverges : Spec.EveryRearrangementConvergesType :=
  @Spec.EveryRearrangementConvergesValue

variable {E : Type*} [NormedAddCommGroup E]

/-- The tail condition describes a Cauchy net, without a completeness assumption. -/
theorem cauchySeq_finset_iff_finiteTailCondition (v : ℕ → E) :
    CauchySeq (finiteSubsum v) ↔ FiniteTailCondition v := by
  change (CauchySeq fun F : Finset ℕ => ∑ i ∈ F, v i) ↔ _
  rw [cauchySeq_finset_iff_vanishing_norm]
  constructor
  · intro h ε hε
    obtain ⟨s, hs⟩ := h ε hε
    refine ⟨s.sup id + 1, fun F hF => hs F ?_⟩
    apply Finset.disjoint_left.mpr
    intro i hi his
    exact (Nat.not_succ_le_self _) ((hF i hi).trans (Finset.le_sup (f := id) his))
  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    refine ⟨Finset.range N, fun F hF => hN F ?_⟩
    intro i hi
    exact Nat.le_of_not_lt fun hlt =>
      Finset.disjoint_left.mp hF hi (Finset.mem_range.mpr hlt)

/-- Convergence implies tail control even in an incomplete normed space. -/
theorem UnconditionallyConvergent.finiteTailCondition {v : ℕ → E}
    (h : UnconditionallyConvergent v) : FiniteTailCondition v := by
  obtain ⟨x, hx⟩ := h
  exact (cauchySeq_finset_iff_finiteTailCondition v).mp hx.cauchySeq

/-- Completeness supplies the limit of the Cauchy net in the converse. -/
theorem unconditionallyConvergent_iff_finiteTailCondition [CompleteSpace E] (v : ℕ → E) :
    UnconditionallyConvergent v ↔ FiniteTailCondition v := by
  change C15Unconditional.Spec.UnconditionallyConvergentValue v ↔ _
  rw [unconditionallyConvergent_iff_summable, summable_iff_cauchySeq_finset]
  exact cauchySeq_finset_iff_finiteTailCondition v

/-- The finite-subset net and the ordinary initial sums have the same limit. -/
theorem exists_unconditionalSum_and_orderedSum_of_finiteTailCondition [CompleteSpace E]
    {v : ℕ → E} (h : FiniteTailCondition v) :
    ∃ x : E, HasUnconditionalSum v x ∧ C01Banach.Spec.HasSequentialSumValue E v x := by
  obtain ⟨x, hx⟩ := (unconditionallyConvergent_iff_finiteTailCondition v).mpr h
  exact ⟨x, hx, C15Unconditional.hasUnconditionalSum_hasSequentialSum v x hx⟩

/-- Given tail control and an existing ordered limit, completeness is unnecessary
to identify that vector as the limit of all finite subsums. -/
theorem hasUnconditionalSum_iff_hasOrderedSum_of_finiteTailCondition
    {v : ℕ → E} (h : FiniteTailCondition v) (x : E) :
    HasUnconditionalSum v x ↔ C01Banach.Spec.HasSequentialSumValue E v x := by
  constructor
  · exact C15Unconditional.hasUnconditionalSum_hasSequentialSum v x
  · intro hx
    exact tendsto_nhds_of_cauchySeq_of_subseq
      ((cauchySeq_finset_iff_finiteTailCondition v).mpr h) tendsto_finset_range ((C01Banach.hasSequentialSum_iff E v x).mp hx)

theorem hasUnconditionalSum_hasSequentialSum_rearrangement {v : ℕ → E} {x : E}
    (h : HasUnconditionalSum v x) (σ : Equiv.Perm ℕ) : C01Banach.Spec.HasSequentialSumValue E (v ∘ σ) x := by
  exact (C01Banach.hasSequentialSum_iff E (v ∘ σ) x).mpr
    ((σ.hasSum_iff.mpr h).tendsto_sum_nat)

/-- A Baire argument supplies an open set on which sufficiently late differences
of a pointwise Cauchy sequence of continuous maps have a common bound. -/
private theorem cauchy_uniform_on_open {X : Type*} [TopologicalSpace X]
    [BaireSpace X] [Nonempty X] (f : ℕ → X → E) (hc : ∀ n, Continuous (f n))
    (h : ∀ x, CauchySeq (fun n => f n x)) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∃ U : Set X, IsOpen U ∧ U.Nonempty ∧
      ∀ x ∈ U, ∀ m ≥ N, ∀ n ≥ N, ‖f m x - f n x‖ ≤ ε := by
  let C : ℕ → Set X := fun N => {x | ∀ m ≥ N, ∀ n ≥ N, ‖f m x - f n x‖ ≤ ε}
  have hC : ∀ N, IsClosed (C N) := by
    intro N
    simp only [C, Set.ofPred_forall]
    exact isClosed_iInter fun m => isClosed_iInter fun _ =>
      isClosed_iInter fun n => isClosed_iInter fun _ =>
        isClosed_le ((hc m).sub (hc n)).norm continuous_const
  have hcover : ⋃ N, C N = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp (h x) ε hε
    exact Set.mem_iUnion.mpr ⟨N, fun m hm n hn => le_of_lt (by
      simpa only [dist_eq_norm] using hN m hm n hn)⟩
  obtain ⟨N, hN⟩ := nonempty_interior_of_iUnion_of_closed hC hcover
  exact ⟨N, interior (C N), isOpen_interior, hN, fun x hx => interior_subset hx⟩

/-- Open sets in a product contain a cylinder prescribing finitely many values. -/
private theorem finite_cylinder {ι α : Type*} [TopologicalSpace α]
    {U : Set (ι → α)} (hU : IsOpen U) {p : ι → α} (hp : p ∈ U) :
    ∃ s : Finset ι, ∀ q : ι → α, (∀ i ∈ s, q i = p i) → q ∈ U := by
  obtain ⟨s, u, hu, hs⟩ := isOpen_pi_iff.mp hU p hp
  exact ⟨s, fun q hq => hs (fun i hi => (hq i hi).symm ▸ (hu i hi).2)⟩

/-- The subseries hypothesis implies uniform smallness of finite tail sums.
Baire is applied to the compact space of choices of retained terms. -/
theorem finiteTailCondition_of_everySubseriesConverges {v : ℕ → E}
    (h : EverySubseriesConverges v) : FiniteTailCondition v := by
  classical
  intro ε hε
  let f : ℕ → (ℕ → Bool) → E := fun n p => ∑ i ∈ Finset.range n,
    if p i then v i else 0
  have hf : ∀ n, Continuous (f n) := by
    intro n
    apply continuous_finsetSum
    intro i _
    exact (continuous_of_discreteTopology : Continuous (fun b : Bool => if b then v i else 0)).comp
      (continuous_apply i)
  have hc : ∀ p, CauchySeq (fun n => f n p) := by
    intro p
    obtain ⟨x, hx⟩ := h {i | p i = true}
    have heq : (fun n => f n p) = (fun n => ∑ i ∈ Finset.range n,
        ({i | p i = true} : Set ℕ).indicator v i) := by
      funext n
      apply Finset.sum_congr rfl
      intro i _
      cases hp : p i <;> simp [hp]
    rw [heq]
    exact ((C01Banach.hasSequentialSum_iff E _ x).mp hx).cauchySeq
  obtain ⟨N, U, hU, ⟨p, hp⟩, hbound⟩ := cauchy_uniform_on_open f hf hc (half_pos hε)
  obtain ⟨s, hs⟩ := finite_cylinder hU hp
  let M := max N (s.sup id + 1)
  refine ⟨M, fun F hF => ?_⟩
  let q : ℕ → Bool := fun i => if i < M then p i else decide (i ∈ F)
  have hq : q ∈ U := hs q fun i hi => by
    have : i < M := (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)).trans_le (le_max_right _ _)
    simp [q, this]
  let L := max M (F.sup id + 1)
  have hML : M ≤ L := le_max_left _ _
  have hsum : f L q - f M q = finiteSubsum v F := by
    change (∑ i ∈ Finset.range L, _) - (∑ i ∈ Finset.range M, _) = _
    rw [← Finset.sum_Ico_eq_sub _ hML]
    change (∑ i ∈ Finset.Ico M L, _) = ∑ i ∈ F, v i
    calc
      _ = ∑ i ∈ Finset.Ico M L, if i ∈ F then v i else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [q, Nat.not_lt.mpr (Finset.mem_Ico.mp hi).1]
      _ = ∑ i ∈ F, v i := by
        rw [← Finset.sum_filter]
        congr 1
        ext i
        simp only [Finset.mem_filter, Finset.mem_Ico]
        exact ⟨fun hi => hi.2, fun hi => ⟨⟨hF i hi,
          (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)).trans_le (le_max_right _ _)⟩, hi⟩⟩
  change ‖finiteSubsum v F‖ < ε
  rw [← hsum]
  exact (hbound q hq L ((le_max_left _ _).trans hML) M (le_max_left _ _)).trans_lt
    (half_lt_self hε)

theorem unconditionallyConvergent_iff_everySubseriesConverges [CompleteSpace E] (v : ℕ → E) :
    UnconditionallyConvergent v ↔ EverySubseriesConverges v := by
  constructor
  · intro h A
    have hs : Summable v := (unconditionallyConvergent_iff_summable v).mp h
    exact ⟨_, (C01Banach.hasSequentialSum_iff E _ _).mpr
      (hs.indicator A).hasSum.tendsto_sum_nat⟩
  · intro h
    exact (unconditionallyConvergent_iff_finiteTailCondition v).mpr
      (finiteTailCondition_of_everySubseriesConverges h)

/-- Evaluation at a continuously varying index is continuous when the index
space is discrete. -/
private theorem continuous_variable_apply {X : Type*} [TopologicalSpace X]
    (a : X → ℕ → ℕ) (b : X → ℕ) (ha : Continuous a) (hb : Continuous b) :
    Continuous (fun x => a x (b x)) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hh : ∀ᶠ y in 𝓝 x, b y = b x := hb.continuousAt.eventually
    (show ∀ᶠ z in 𝓝 (b x), z = b x from by simp)
  apply (((continuous_apply (b x)).comp ha).continuousAt).congr_of_eventuallyEq
  filter_upwards [hh] with y hy
  simp only [Function.comp_apply, hy]

private def permutationCodes : Set ((Bool × ℕ) → ℕ) :=
  {p | ∀ n, p (false, p (true, n)) = n ∧ p (true, p (false, n)) = n}

private theorem permutationCodes_closed : IsClosed permutationCodes := by
  simp only [permutationCodes, Set.ofPred_forall]
  apply isClosed_iInter
  intro n
  apply IsClosed.inter
  · exact isClosed_eq (continuous_variable_apply (fun (p : (Bool × ℕ) → ℕ) n => p (false, n))
      (fun p => p (true, n)) (continuous_pi fun _ => continuous_apply _) (continuous_apply _))
      continuous_const
  · exact isClosed_eq (continuous_variable_apply (fun (p : (Bool × ℕ) → ℕ) n => p (true, n))
      (fun p => p (false, n)) (continuous_pi fun _ => continuous_apply _) (continuous_apply _))
      continuous_const

private abbrev PermutationSpace := permutationCodes

private def encodePermutation (σ : Equiv.Perm ℕ) : PermutationSpace :=
  ⟨fun i => if i.1 then σ.symm i.2 else σ i.2, by
    intro n
    exact ⟨σ.apply_symm_apply n, σ.symm_apply_apply n⟩⟩

private def decodePermutation (p : PermutationSpace) : Equiv.Perm ℕ where
  toFun n := p.val (false, n)
  invFun n := p.val (true, n)
  left_inv n := (p.property n).2
  right_inv n := (p.property n).1

private instance : Nonempty PermutationSpace := ⟨encodePermutation (Equiv.refl ℕ)⟩
private instance : PolishSpace PermutationSpace := permutationCodes_closed.polishSpace

/-- A neighborhood of a permutation contains all permutations agreeing on
finitely many forward and inverse values. -/
private theorem permutation_cylinder {U : Set PermutationSpace} (hU : IsOpen U)
    {p : PermutationSpace} (hp : p ∈ U) :
    ∃ K : ℕ, ∀ σ : Equiv.Perm ℕ,
      (∀ i < K, σ i = decodePermutation p i) →
      (∀ i < K, σ.symm i = (decodePermutation p).symm i) →
      encodePermutation σ ∈ U := by
  obtain ⟨V, hV, hUV⟩ := isOpen_induced_iff.mp hU
  have hpV : p.val ∈ V := by change p ∈ Subtype.val ⁻¹' V; rwa [hUV]
  obtain ⟨s, hs⟩ := finite_cylinder hV hpV
  refine ⟨s.sup Prod.snd + 1, fun σ hσ hσ' => ?_⟩
  rw [← hUV]
  apply hs
  intro i hi
  have hilt : i.2 < s.sup Prod.snd + 1 := Nat.lt_succ_of_le (Finset.le_sup hi)
  rcases i with ⟨b, i⟩
  cases b
  · exact hσ i hilt
  · exact hσ' i hilt

/-- Extend a finite initial matching, putting an arbitrary disjoint finite set
immediately after the prescribed prefix. -/
private theorem permutation_with_block (π : Equiv.Perm ℕ) (M : ℕ) (F : Finset ℕ)
    (hF : ∀ i ∈ F, ∀ j < M, i ≠ π j) :
    ∃ σ : Equiv.Perm ℕ, (∀ j < M, σ j = π j) ∧
      (Finset.Ico M (M + F.card)).image σ = F := by
  classical
  let e : Fin F.card ≃ F := (Fintype.equivFinOfCardEq (by simp)).symm
  let g : Fin (M + F.card) → ℕ := fun j =>
    if hj : j.val < M then π j.val else
      (e ⟨j.val - M, by omega⟩).val
  have hg : Function.Injective g := by
    intro a b hab
    by_cases ha : a.val < M <;> by_cases hb : b.val < M
    · simp only [g, dite_eq_left ha, dite_eq_left hb] at hab
      exact Fin.ext (π.injective hab)
    · simp only [g, dite_eq_left ha, dite_eq_right hb] at hab
      exact False.elim (hF _ (e _).property _ ha hab.symm)
    · simp only [g, dite_eq_right ha, dite_eq_left hb] at hab
      exact False.elim (hF _ (e _).property _ hb hab)
    · simp only [g, dite_eq_right ha, dite_eq_right hb] at hab
      have he : a.val - M = b.val - M := congrArg Fin.val (e.injective (Subtype.ext hab))
      apply Fin.ext
      omega
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (fun j : Fin (M + F.card) => j.val) g Fin.val_injective hg
  refine ⟨σ, ?_, ?_⟩
  · intro j hj
    have hj' : j < M + F.card := by omega
    simpa only [g, dite_eq_left hj] using hσ ⟨j, hj'⟩
  · ext i
    constructor
    · intro hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨hjM, hjL⟩ := Finset.mem_Ico.mp hj
      have hj : ¬ j < M := by omega
      have heq : σ j = (e ⟨j - M, by omega⟩).val := by
        simpa only [g, dite_eq_right hj] using hσ ⟨j, hjL⟩
      rw [heq]
      exact (e _).property
    · intro hi
      obtain ⟨j, hj⟩ := e.surjective ⟨i, hi⟩
      apply Finset.mem_image.mpr
      refine ⟨M + j.val, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩
      have hnot : ¬ M + j.val < M := by omega
      have hsum : M + j.val - M = j.val := by omega
      have heq := hσ ⟨M + j.val, by omega⟩
      simp only [g, dite_eq_right hnot] at heq
      simpa only [hsum, hj] using heq

/-- Each permutation is allowed its own limit. Baire uniformity on a cylinder,
followed by extension of a finite matching, forces the finite-tail condition. -/
theorem finiteTailCondition_of_everyRearrangementConverges {v : ℕ → E}
    (h : EveryRearrangementConverges v) : FiniteTailCondition v := by
  classical
  intro ε hε
  let f : ℕ → PermutationSpace → E := fun n p =>
    ∑ i ∈ Finset.range n, v (p.val (false, i))
  have hf : ∀ n, Continuous (f n) := by
    intro n
    apply continuous_finsetSum
    intro i _
    exact (continuous_of_discreteTopology : Continuous v).comp
      ((continuous_apply _).comp continuous_subtype_val)
  have hc : ∀ p, CauchySeq (fun n => f n p) := by
    intro p
    obtain ⟨x, hx⟩ := h (decodePermutation p)
    exact ((C01Banach.hasSequentialSum_iff E _ x).mp hx).cauchySeq
  obtain ⟨N, U, hU, ⟨p, hp⟩, hbound⟩ := cauchy_uniform_on_open f hf hc (half_pos hε)
  obtain ⟨K, hK⟩ := permutation_cylinder hU hp
  let π := decodePermutation p
  let M := max N (max K ((Finset.range K).sup π.symm + 1))
  have hNM : N ≤ M := le_max_left _ _
  have hKM : K ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  refine ⟨(Finset.range M).sup π + 1, fun F hF => ?_⟩
  obtain ⟨σ, hσ, hσF⟩ := permutation_with_block π M F (by
    intro i hi j hj heq
    have hji : π j ≤ (Finset.range M).sup π := Finset.le_sup (Finset.mem_range.mpr hj)
    have := hF i hi
    omega)
  have hσU : encodePermutation σ ∈ U := by
    apply hK σ
    · intro i hi
      exact hσ i (hi.trans_le hKM)
    · intro i hi
      have hiM : π.symm i < M :=
        (Nat.lt_succ_of_le (Finset.le_sup (f := π.symm) (Finset.mem_range.mpr hi))).trans_le
          ((le_max_right _ _).trans (le_max_right _ _))
      apply σ.injective
      rw [σ.apply_symm_apply, hσ _ hiM, π.apply_symm_apply]
  have hsum : f (M + F.card) (encodePermutation σ) - f M (encodePermutation σ) =
      finiteSubsum v F := by
    change (∑ i ∈ Finset.range (M + F.card), v (σ i)) -
      (∑ i ∈ Finset.range M, v (σ i)) = ∑ i ∈ F, v i
    rw [← Finset.sum_Ico_eq_sub _ (by omega : M ≤ M + F.card)]
    calc
      _ = ∑ i ∈ (Finset.Ico M (M + F.card)).image σ, v i := by
        symm
        apply Finset.sum_image
        intro i _ j _ hij
        exact σ.injective hij
      _ = ∑ i ∈ F, v i := by rw [hσF]
  change ‖finiteSubsum v F‖ < ε
  rw [← hsum]
  exact (hbound _ hσU _ (by omega) _ hNM).trans_lt (half_lt_self hε)

/-- Ordered convergence under every permutation suffices; a common sum is
proved below, rather than included in the hypothesis. -/
theorem unconditionallyConvergent_iff_everyRearrangementConverges [CompleteSpace E] (v : ℕ → E) :
    UnconditionallyConvergent v ↔ EveryRearrangementConverges v := by
  constructor
  · rintro ⟨x, hx⟩ σ
    exact ⟨x, hasUnconditionalSum_hasSequentialSum_rearrangement hx σ⟩
  · intro h
    exact (unconditionallyConvergent_iff_finiteTailCondition v).mpr
      (finiteTailCondition_of_everyRearrangementConverges h)

/-- All four source conditions are equivalent in a Banach space. -/
theorem unconditional_criteria [CompleteSpace E] (v : ℕ → E) :
    (UnconditionallyConvergent v ↔ FiniteTailCondition v) ∧
    (FiniteTailCondition v ↔ EverySubseriesConverges v) ∧
    (FiniteTailCondition v ↔ EveryRearrangementConverges v) := by
  have ht := unconditionallyConvergent_iff_finiteTailCondition v
  exact ⟨ht, ht.symm.trans (unconditionallyConvergent_iff_everySubseriesConverges v),
    ht.symm.trans (unconditionallyConvergent_iff_everyRearrangementConverges v)⟩

/-- There is a single vector which is both the finite-subset sum and the
ordered sum after every permutation (including the identity). -/
theorem rearrangements_have_same_sum [CompleteSpace E] {v : ℕ → E}
    (h : EveryRearrangementConverges v) :
    ∃ x : E, HasUnconditionalSum v x ∧ ∀ σ : Equiv.Perm ℕ, C01Banach.Spec.HasSequentialSumValue E (v ∘ σ) x := by
  obtain ⟨x, hx⟩ := (unconditionallyConvergent_iff_everyRearrangementConverges v).mpr h
  exact ⟨x, hx, hasUnconditionalSum_hasSequentialSum_rearrangement hx⟩


theorem absolute_implies_unconditional : Spec.AbsoluteImpliesUnconditional :=
  AbsoluteUnconditionalBoundary.absolute_implies_unconditional

theorem hilbert_converse_fails : Spec.HilbertConverseFails :=
  AbsoluteUnconditionalBoundary.harmonic_boundary

end ExpandedFA.P1.C15UnconditionalCriteria
