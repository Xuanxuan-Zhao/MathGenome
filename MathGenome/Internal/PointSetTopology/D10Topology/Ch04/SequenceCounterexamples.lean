import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch04.SequenceCounterexamples
import MathGenome.Internal.PointSetTopology.D10Topology.Ch01.ElementaryTopologies
import MathGenome.Internal.PointSetTopology.D10Topology.Ch04.NetTests
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-! The two counterexamples of paper.tex, d10:04:sequence-failure. -/
open Set
open scoped Topology
universe u v
namespace D10Topology.Ch04

abbrev alternatingPair : ℕ → ℝ × ℝ :=
  Specs.D10Topology.Ch04.SequenceCounterexamples.alternatingPair

/-- Eventual equality suffices in every topology. -/
theorem sequence_converges_of_eventually_equal {X : Type u}
    (t : TopologicalSpace X) (a : ℕ → X) (x : X)
    (h : ∃ N, ∀ n, N ≤ n → a n = x) : Converges t a x := by
  intro U hU
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun n hn => ?_⟩
  rw [hN n hn]
  exact Ch01.neighborhood_contains t x U hU

theorem cocountable_sequence_converges_iff (X : Type u) (a : ℕ → X) (x : X) :
    Converges (Ch01.cocountableTopology X) a x ↔ ∃ N, ∀ n, N ≤ n → a n = x := by
  classical
  constructor
  · intro h
    let C : Set X := range a \ {x}
    have hC : C.Countable := (countable_range a).mono sdiff_subset
    have hO : IsOpen[Ch01.cocountableTopology X] Cᶜ :=
      (Ch01.cocountable_countable_closed X C hC).isOpen_compl
    have hx : x ∈ Cᶜ := by simp [C]
    obtain ⟨N, hN⟩ := h Cᶜ ⟨Cᶜ, hO, hx, Subset.rfl⟩
    refine ⟨N, fun n hn => ?_⟩
    by_contra hne
    exact hN n hn ⟨mem_range_self n, hne⟩
  · exact sequence_converges_of_eventually_equal _ a x

theorem cocountable_id_preserves_sequences (X : Type u) (a : ℕ → X) (x : X)
    (ha : Converges (Ch01.cocountableTopology X) a x) :
    Converges (⊥ : TopologicalSpace X) (id ∘ a) (id x) := by
  exact sequence_converges_of_eventually_equal _ a x
    ((cocountable_sequence_converges_iff X a x).mp ha)

theorem cocountable_singleton_not_open (X : Type u) [Uncountable X] (x : X) :
    ¬ IsOpen[Ch01.cocountableTopology X] ({x} : Set X) := by
  intro h
  rcases (Ch01.cocountable_opens X {x}).mp h with h | h
  · exact (singleton_nonempty x).ne_empty h
  · apply Set.not_countable_univ (α := X)
    rw [← union_compl_self ({x} : Set X)]
    exact (countable_singleton x).union h

theorem cocountable_id_not_continuous (X : Type u) [Uncountable X] :
    ¬ @Continuous X X (Ch01.cocountableTopology X) ⊥ id := by
  intro h
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  have hs : IsOpen[⊥] ({x} : Set X) := trivial
  exact cocountable_singleton_not_open X x (@Continuous.isOpen_preimage X X (Ch01.cocountableTopology X) ⊥ id h {x} hs)

theorem cocountable_dense_not_sequential (X : Type u) (A : Set X)
    (hA : ¬ A.Countable) (hproper : A ≠ univ) :
    @Dense X (Ch01.cocountableTopology X) A ∧
    (∃ x : X, x ∉ A) ∧
    ∀ x : X, x ∉ A →
      (∀ a : ℕ → X, (∀ n, a n ∈ A) → ¬ Converges (Ch01.cocountableTopology X) a x) ∧
      (∃ (D : Type (max u v)) (p : Preorder D),
        Nonempty D ∧ @IsDirectedOrder D p.toLE ∧
        ∃ a : Net D X, (∀ d, a d ∈ A) ∧
          @Converges D X p (Ch01.cocountableTopology X) a x) := by
  classical
  let := Ch01.cocountableTopology X
  have hd : Dense A := Ch01.cocountable_uncountable_dense X A hA
  refine ⟨hd, ?_, fun x hx => ⟨?_, ?_⟩⟩
  · by_contra h
    exact hproper (eq_univ_of_forall fun x => by simpa using not_exists.mp h x)
  · intro a ha hc
    obtain ⟨N, hN⟩ := (cocountable_sequence_converges_iff X a x).mp hc
    exact hx (hN N le_rfl ▸ ha N)
  · exact (closure_iff_exists_net.{u, v} A x).mp (hd x)

theorem alternating_coordinate_clusters :
    Clusters (inferInstance : TopologicalSpace ℝ) (fun n => (alternatingPair n).1) 0 ∧
    Clusters (inferInstance : TopologicalSpace ℝ) (fun n => (alternatingPair n).2) 0 := by
  constructor
  · intro U hU N
    refine ⟨2 * N, by omega, ?_⟩
    have hx := Ch01.neighborhood_contains _ (0 : ℝ) U hU
    simpa [alternatingPair, Specs.D10Topology.Ch04.SequenceCounterexamples.alternatingPair] using hx
  · intro U hU N
    refine ⟨2 * N + 1, by omega, ?_⟩
    have hx := Ch01.neighborhood_contains _ (0 : ℝ) U hU
    simpa [alternatingPair, Specs.D10Topology.Ch04.SequenceCounterexamples.alternatingPair,
      Nat.add_mod, Nat.mul_mod] using hx

theorem alternating_square_witness :
    let U : Set (ℝ × ℝ) := (Ioo (-(1/2 : ℝ)) (1/2)) ×ˢ (Ioo (-(1/2 : ℝ)) (1/2))
    IsOpen U ∧ (0, 0) ∈ U ∧ ∀ n, alternatingPair n ∉ U := by
  refine ⟨isOpen_Ioo.prod isOpen_Ioo, by norm_num, fun n => ?_⟩
  unfold alternatingPair Specs.D10Topology.Ch04.SequenceCounterexamples.alternatingPair
  split <;> norm_num

theorem alternating_not_cluster :
    ¬ Clusters (inferInstance : TopologicalSpace (ℝ × ℝ)) alternatingPair (0, 0) := by
  intro h
  obtain ⟨hO, hx, hmiss⟩ := alternating_square_witness
  obtain ⟨n, _, hn⟩ := h _ ⟨_, hO, hx, Subset.rfl⟩ 0
  exact hmiss n hn

end D10Topology.Ch04
