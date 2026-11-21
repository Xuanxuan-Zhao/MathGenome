import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch10.UrysohnMetrization
import MathGenome.Internal.PointSetTopology.D10Topology.Ch08.RegularLindelofNormal
import MathGenome.Internal.PointSetTopology.D10Topology.Ch07.UrysohnSeparation
import MathGenome.Internal.PointSetTopology.D10Topology.Ch10.EvaluationEmbedding
import MathGenome.Internal.PointSetTopology.D10Topology.Ch10.CountableProductMetric
import Mathlib.Data.Nat.Pairing
import Mathlib.Topology.Homeomorph.Lemmas

/-! Urysohn metrization, including the required countable-cube embedding.
We use a sequence of basis sets (also available for the empty space), and
choose the Urysohn function for each nested pair of basis sets. All other
pairs receive the zero function. Pairing ℕ × ℕ with ℕ pads finite bases
without any infinitude hypothesis. -/

open Set Topology
universe u

namespace D10Topology.Ch10

/-- A countable family detects every neighborhood. No separation hypothesis
is needed for this step beyond regularity. -/
theorem exists_countable_neighborhood_functions {X : Type u} [t : TopologicalSpace X]
    (hR : Ch07.Regular X) (hS : Ch08.SecondCountable t) :
    ∃ f : ℕ → X → unitInterval, (∀ n, Continuous (f n)) ∧
      ∀ U : Set X, IsOpen U → ∀ x ∈ U,
        ∃ n, 0 < (f n x : ℝ) ∧ ∀ y, y ∉ U → f n y = 0 := by
  classical
  letI : RegularSpace X := hR
  letI : SecondCountableTopology X := hS
  have hN : Ch07.Normal X :=
    Ch08.regular_lindelof_normal hR Ch08.secondCountable_lindelof
  obtain ⟨B, hB⟩ := TopologicalSpace.exists_seq_basis X
  have hex : ∀ p : ℕ × ℕ, ∃ f : X → unitInterval, Continuous f ∧
      (closure (B p.1) ⊆ B p.2 →
        (∀ x ∈ closure (B p.1), f x = 1) ∧ (∀ x ∈ (B p.2)ᶜ, f x = 0)) := by
    intro p
    by_cases hp : closure (B p.1) ⊆ B p.2
    · obtain ⟨f, hf, h1, h0⟩ := Ch07.normal_closed_open_function X hN
        (closure (B p.1)) (B p.2) isClosed_closure
        (hB.isOpen (mem_range_self p.2)) hp
      exact ⟨f, hf, fun _ => ⟨h1, h0⟩⟩
    · exact ⟨fun _ => 0, continuous_const, fun h => (hp h).elim⟩
  choose g hg hval using hex
  refine ⟨fun n => g (Nat.unpair n), fun n => hg _, ?_⟩
  intro U hU x hx
  obtain ⟨V, ⟨j, rfl⟩, hxj, hjU⟩ := hB.exists_subset_of_mem_open hx hU
  obtain ⟨V, ⟨i, rfl⟩, hxi, hij⟩ :=
    hB.exists_closure_subset ((hB.isOpen (mem_range_self j)).mem_nhds hxj)
  refine ⟨Nat.pair i j, ?_, ?_⟩
  · simp only [Nat.unpair_pair]
    rw [(hval (i, j) hij).1 x (subset_closure hxi)]
    exact zero_lt_one
  · intro y hy
    simp only [Nat.unpair_pair]
    exact (hval (i, j) hij).2 y (fun hyj => hy (hjU hyj))

theorem urysohn_metrization_nat {X : Type u} [t : TopologicalSpace X]
    (hR : Ch07.Regular X) (hS : Ch08.SecondCountable t) (h1 : Ch07.T1 X) :
    (∃ e : X → (ℕ → unitInterval), IsEmbedding e) ∧ Ch09.Metrizable t := by
  letI : T1Space X := h1
  obtain ⟨f, hf, hlocal⟩ := exists_countable_neighborhood_functions hR hS
  have hs : ∀ x y, x ≠ y → ∃ n, f n x ≠ f n y := by
    intro x y hxy
    obtain ⟨n, hn, hzero⟩ := hlocal ({y}ᶜ) isClosed_singleton.isOpen_compl x
      (by simpa using hxy)
    refine ⟨n, ?_⟩
    intro heq
    have h0 : f n y = 0 := hzero y (by simp)
    rw [heq, h0] at hn
    exact (lt_irrefl (0 : ℝ)) hn
  have he : IsEmbedding (fun x n => f n x) :=
    evaluation_embedding_unitInterval f hf hs hlocal
  refine ⟨⟨_, he⟩, ?_⟩
  -- The upstream product metric has exactly the product topology, so its
  -- pullback along this embedding is compatible with the given topology.
  letI : MetricSpace (ℕ → unitInterval) := productMetric (fun _ => inferInstance)
  exact ⟨he.comapMetricSpace (fun x n => f n x), rfl⟩

/-- Reindex by n ↦ n+1 to obtain precisely the positive-index cube of the paper. -/
theorem urysohn_metrization {X : Type u} [t : TopologicalSpace X]
    (hR : Ch07.Regular X) (hS : Ch08.SecondCountable t) (h1 : Ch07.T1 X) :
    (∃ e : X → (ℕ+ → unitInterval), IsEmbedding e) ∧ Ch09.Metrizable t := by
  obtain ⟨⟨e, he⟩, hm⟩ := urysohn_metrization_nat hR hS h1
  let h : (ℕ → unitInterval) ≃ₜ (ℕ+ → unitInterval) :=
    Homeomorph.piCongrLeft (Y := fun _ : ℕ+ => unitInterval) Equiv.pnatEquivNat.symm
  exact ⟨⟨h ∘ e, h.isEmbedding.comp he⟩, hm⟩

theorem urysohn_metrization_t0 {X : Type u} [t : TopologicalSpace X]
    (hR : Ch07.Regular X) (hS : Ch08.SecondCountable t) (h0 : Ch07.T0 X) :
    (∃ e : X → (ℕ+ → unitInterval), IsEmbedding e) ∧ Ch09.Metrizable t :=
  urysohn_metrization hR hS (Ch07.regular_t0_implies_t1 X hR h0)

theorem regular_separation_equivalence {X : Type u} [TopologicalSpace X]
    (hR : Ch07.Regular X) : Ch07.T0 X ↔ Ch07.T1 X :=
  ⟨Ch07.regular_t0_implies_t1 X hR, Ch07.t1_implies_t0 X⟩

theorem indiscrete_two_point_counterexample :
    @RegularSpace Bool ⊤ ∧ @SecondCountableTopology Bool ⊤ ∧
      ¬ Ch09.Metrizable (⊤ : TopologicalSpace Bool) := by
  letI : TopologicalSpace Bool := ⊤
  have hR : Ch07.Regular Bool := by
    apply (Ch07.regular_iff_disjoint_open Bool).mpr
    intro F hF x hx
    have hFc : Fᶜ = univ :=
      (TopologicalSpace.isOpen_top_iff Fᶜ).mp hF.isOpen_compl |>.resolve_left
        (fun he => by
          have : x ∈ Fᶜ := hx
          simpa only [he, mem_empty_iff_false] using this)
    have hF0 : F = ∅ := by
      have h := congrArg compl hFc
      simpa only [compl_compl, compl_univ] using h
    subst F
    exact ⟨univ, ∅, isOpen_univ, isOpen_empty, mem_univ x, subset_rfl, by simp⟩
  refine ⟨hR, inferInstance, ?_⟩
  intro hm
  letI : TopologicalSpace.MetrizableSpace Bool := (Ch09.metrizable_iff_mathlib _).mp hm
  have hopen : IsOpen ({false}ᶜ : Set Bool) := isClosed_singleton.isOpen_compl
  obtain h | h := (TopologicalSpace.isOpen_top_iff _).mp hopen
  · have : true ∈ ({false}ᶜ : Set Bool) := by simp
    simpa [h] using this
  · have : false ∉ ({false}ᶜ : Set Bool) := by simp
    simp [h] at this

end D10Topology.Ch10
