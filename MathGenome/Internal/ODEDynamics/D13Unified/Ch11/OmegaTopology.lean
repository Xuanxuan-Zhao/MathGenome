import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch11.OmegaTopology
import MathGenome.Internal.ODEDynamics.D13Unified.Ch11.Invariant
import MathGenome.Internal.ODEDynamics.D13Unified.Ch11.Flow
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Connected.Clopen
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
open Set Filter Metric
open scoped Topology

namespace D13Unified.Ch11.OmegaTopology
open Specs.D13Unified.Ch11.OmegaTopology
open Specs.D13Unified.Ch01.AutonomousParameters
open Specs.D13Unified.Ch04.MaximalSolutionMap
open Ch06.StateDerivative
universe u

/-- Ambient omega-limit set on the actual maximal lifespan. -/
def omega : omegaType := omegaValue

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma orbitTail_antitone (F : AutonomousODE E) (x : E) : Antitone (orbitTail F x) := by
  intro s r hsr
  exact image_mono (fun t ht => ⟨ht.1, hsr.trans ht.2⟩)

lemma omega_eq_nat_inter (F : AutonomousODE E) (x : E) :
    omegaValue F x = ⋂ n : ℕ, closure (orbitTail F x n) := by
  ext y
  simp only [omegaValue, mem_iInter]
  constructor
  · intro h n
    exact h n (Nat.cast_nonneg n)
  · intro h s _
    obtain ⟨n, hn⟩ := exists_nat_ge s
    exact closure_mono (orbitTail_antitone F x hn) (h n)

lemma omega_subset (F : AutonomousODE E) (x : E) :
    omegaValue F x ⊆ closure (positiveOrbit F x) := by
  intro y hy
  exact mem_iInter.mp (mem_iInter.mp hy 0) le_rfl

/-- Compact confinement of this one orbit suffices; no invariance of its
closure is assumed in the continuation argument. -/
lemma forward_complete [FiniteDimensional ℝ E] (F : AutonomousODE E)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {x : E} (hx : x ∈ F.domain)
    (hK : IsCompact (closure (positiveOrbit F x)))
    (hKΩ : closure (positiveOrbit F x) ⊆ F.domain) :
    Ici 0 ⊆ (flowInterval F x).carrier := by
  have hL := F.locallyLipschitzInState_of_contDiffOn hF
  obtain ⟨hsol, hz, hi, hm, hend, hc, hu⟩ :=
    ODE.canonical_solution F.toODE hL 0 x hx
  change lowerEndpointValue F.toODE 0 x < (0 : ℝ) ∧
    (0 : ℝ) < upperEndpointValue F.toODE 0 x ∧
    (maximalIntervalValue F.toODE 0 x).carrier =
      {t : ℝ | lowerEndpointValue F.toODE 0 x < (t : EReal) ∧
        (t : EReal) < upperEndpointValue F.toODE 0 x} at hend
  have hb : upperEndpointValue F.toODE 0 x = ⊤ := by
    cases hb : upperEndpointValue F.toODE 0 x using EReal.rec with
    | bot => simpa [hb] using hend.2.1
    | top => rfl
    | coe b =>
      exfalso
      have h0b : (0 : ℝ) < b := by simpa [hb] using hend.2.1
      obtain ⟨τ, hτ, hesc⟩ := Ch04.CompactEscape.right_escape F.toODE hL 0 x
        hx b hb (Icc 0 b ×ˢ closure (positiveOrbit F x)) (isCompact_Icc.prod hK)
        (fun q hq => hKΩ hq.2)
      let t : ℝ := (max τ 0 + b) / 2
      have hmb : max τ 0 < b := max_lt hτ h0b
      have hmt : max τ 0 < t := by dsimp [t]; linarith
      have htb : t < b := by dsimp [t]; linarith
      have ht0 : 0 ≤ t := (le_max_right τ 0).trans hmt.le
      have htI : t ∈ (flowInterval F x).carrier := by
        change t ∈ (maximalIntervalValue F.toODE 0 x).carrier
        rw [hend.2.2]
        exact ⟨hend.1.trans_le (EReal.coe_le_coe ht0), by simpa [hb] using htb⟩
      have heval := (ODE.solutionValue_on_domain F.toODE hL t 0 x ⟨hx, htI⟩).1
      apply hesc t ⟨(le_max_left τ 0).trans_lt hmt, htb⟩
      refine ⟨⟨ht0, htb.le⟩, ?_⟩
      rw [heval]
      exact subset_closure ⟨t, ⟨htI, ht0⟩, rfl⟩
  intro t ht
  change t ∈ (maximalIntervalValue F.toODE 0 x).carrier
  rw [hend.2.2]
  exact ⟨hend.1.trans_le (EReal.coe_le_coe ht), by simp [hb]⟩

/-- A decreasing family of compact connected sets has connected intersection.
The proof separates a hypothetical partition and uses compactness to put a
whole tail in the resulting two disjoint open neighborhoods. -/
lemma connected_nat_inter {X : Type*} [TopologicalSpace X] [T2Space X]
    (T : ℕ → Set X) (hmono : Antitone T) (hne : ∀ n, (T n).Nonempty)
    (hcompact : IsCompact (T 0)) (hclosed : ∀ n, IsClosed (T n))
    (hconn : ∀ n, IsPreconnected (T n)) : IsConnected (⋂ n, T n) := by
  have hneC := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed T
    (fun n => hmono (Nat.le_succ n)) hne hcompact hclosed
  have hclC : IsClosed (⋂ n, T n) := isClosed_iInter hclosed
  have hcC : IsCompact (⋂ n, T n) :=
    hcompact.of_isClosed_subset hclC (iInter_subset T 0)
  refine ⟨hneC, (isPreconnected_iff_subset_of_fully_disjoint_closed hclC).2 ?_⟩
  intro u v hu hv hcover hdis
  by_contra h
  push Not at h
  obtain ⟨a, haC, hau⟩ := not_subset.mp h.1
  obtain ⟨b, hbC, hbv⟩ := not_subset.mp h.2
  have hav := (hcover haC).resolve_left hau
  have hbu := (hcover hbC).resolve_right hbv
  obtain ⟨U, V, hU, hV, hCU, hCV, hUV⟩ :=
    SeparatedNhds.of_isCompact_isCompact (hcC.inter_right hu) (hcC.inter_right hv)
      (hdis.mono inter_subset_right inter_subset_right)
  have hcover' : (⋂ n, T n) ⊆ U ∪ V := by
    intro z hz
    rcases hcover hz with hzU | hzV
    · exact Or.inl (hCU ⟨hz, hzU⟩)
    · exact Or.inr (hCV ⟨hz, hzV⟩)
  have hbad : Disjoint (T 0 \ (U ∪ V)) (⋂ n, T n) := by
    exact disjoint_left.2 (fun z hz hzC => hz.2 (hcover' hzC))
  obtain ⟨n, hn⟩ := (hcompact.diff (hU.union hV)).elim_directed_family_closed T hclosed
    hbad hmono.directed_ge
  have hTcover : T n ⊆ U ∪ V := by
    intro z hz
    by_contra hz'
    exact disjoint_left.mp hn ⟨hmono (Nat.zero_le n) hz, hz'⟩ hz
  obtain ⟨z, _, hzU, hzV⟩ := hconn n U V hU hV hTcover
    ⟨b, mem_iInter.mp hbC n, hCU ⟨hbC, hbu⟩⟩
    ⟨a, mem_iInter.mp haC n, hCV ⟨haC, hav⟩⟩
  exact disjoint_left.mp hUV hzU hzV

/-- The full topological assertion, including forward completeness, for one
relatively compact positive orbit contained in the original state domain. -/
theorem compact_omega_topology : CompactOmegaTopology.{u} := by
  intro E _ _ _ F hF x hx hK hKΩ
  have hcomplete := forward_complete F hF hx hK hKΩ
  have hc := (flow_ivp F hF hx).1.1.continuousOn
  have htail (n : ℕ) : orbitTail F x n = (fun t => flow F t x) '' Ici (n : ℝ) := by
    unfold orbitTail
    congr 1
    ext t
    exact and_iff_right_of_imp (fun ht => hcomplete (show 0 ≤ t from (Nat.cast_nonneg n).trans ht))
  have hn (n : ℕ) : (closure (orbitTail F x n)).Nonempty := by
    rw [htail]
    exact (nonempty_Ici.image _).closure
  have hcl (n : ℕ) : IsClosed (closure (orbitTail F x n)) := isClosed_closure
  have hmono : Antitone (fun n : ℕ => closure (orbitTail F x n)) := by
    intro m n hmn
    exact closure_mono (orbitTail_antitone F x (by exact_mod_cast hmn))
  have hconn (n : ℕ) : IsPreconnected (closure (orbitTail F x n)) := by
    rw [htail]
    exact (isPreconnected_Ici.image _ (hc.mono
      (fun t ht => hcomplete ((Nat.cast_nonneg n).trans ht)))).closure
  have hK0 : IsCompact (closure (orbitTail F x (0 : ℕ))) := by simpa [positiveOrbit] using hK
  have hconnected := connected_nat_inter _ hmono hn hK0 hcl hconn
  rw [← omega_eq_nat_inter F x] at hconnected
  refine ⟨hcomplete, hconnected.nonempty, ?_, hconnected, omega_subset F x⟩
  exact hK.of_isClosed_subset
    (isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_closure)
    (omega_subset F x)

/-- Approximating each closed tail at accuracy 1/(j+1) produces actual times
at least j. Conversely any such divergent sequence eventually lies in each tail. -/
theorem sequence_characterization : SequenceCharacterization.{u} := by
  intro E _ _ F x y
  constructor
  · intro hy
    have hnear (j : ℕ) : ∃ t : ℝ,
        (t ∈ (flowInterval F x).carrier ∧ (j : ℝ) ≤ t) ∧
        dist y (flow F t x) < 1 / ((j : ℝ) + 1) := by
      have hj : y ∈ closure (orbitTail F x j) :=
        mem_iInter.mp (mem_iInter.mp hy j) (Nat.cast_nonneg j)
      obtain ⟨z, ⟨t, ht, rfl⟩, hz⟩ := Metric.mem_closure_iff.mp hj
        (1 / ((j : ℝ) + 1)) (by positivity)
      exact ⟨t, ht, hz⟩
    choose t ht hd using hnear
    refine ⟨t, fun j => ⟨(ht j).1, (Nat.cast_nonneg j).trans (ht j).2⟩, ?_, ?_⟩
    · exact tendsto_atTop_mono (fun j => (ht j).2) tendsto_natCast_atTop_atTop
    · apply tendsto_iff_dist_tendsto_zero.mpr
      simpa only [dist_comm] using
        (squeeze_zero (fun j => dist_nonneg) (fun j => (hd j).le)
          tendsto_one_div_add_atTop_nhds_zero_nat)
  · rintro ⟨t, ht, htTop, hty⟩
    refine mem_iInter.mpr fun s => mem_iInter.mpr fun hs => ?_
    apply isClosed_closure.mem_of_tendsto hty
    filter_upwards [htTop (eventually_ge_atTop s)] with j hj
    exact subset_closure ⟨t j, ⟨(ht j).1, hj⟩, rfl⟩

end D13Unified.Ch11.OmegaTopology
