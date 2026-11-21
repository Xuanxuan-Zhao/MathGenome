import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch11.Omega
import MathGenome.Internal.ODEDynamics.D13Unified.Ch11.OmegaTopology

noncomputable section
open Set Filter Metric
open scoped Topology

namespace D13Unified.Ch11.Omega
open Specs.D13Unified.Ch01.AutonomousParameters
open Specs.D13Unified.Ch11.OmegaTopology
open Specs.D13Unified.Ch11.Invariant
open Specs.D13Unified.Ch11.Flow
open Ch06.StateDerivative
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A finite time of either sign can be passed through an omega-limit
sequence. Openness of the actual time-map domain supplies a common domain
for all sufficiently late terms; no global flow is used here. -/
lemma omega_invariant (F : AutonomousODE E)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {x : E} (hx : x ∈ F.domain)
    (hKΩ : closure (positiveOrbit F x) ⊆ F.domain) :
    invariantValue F (omegaValue F x) := by
  have hΩ : omegaValue F x ⊆ F.domain := (OmegaTopology.omega_subset F x).trans hKΩ
  refine ⟨hΩ, ?_⟩
  intro y hy s hs
  obtain ⟨t, ht, htTop, hty⟩ := (OmegaTopology.sequence_characterization F x y).mp hy
  have hyD : y ∈ timeDomainValue F s := ⟨hΩ hy, hs⟩
  have hnear : ∀ᶠ j in atTop, flow F (t j) x ∈ timeDomainValue F s :=
    hty ((Flow.isOpen_timeDomain F hF s).mem_nhds hyD)
  have hc : ContinuousAt (flow F s) y :=
    (Flow.contDiffOn_timeMap 1 le_rfl F hF s).continuousOn.continuousAt
      ((Flow.isOpen_timeDomain F hF s).mem_nhds hyD)
  have hlim := hc.tendsto.comp hty
  refine mem_iInter.mpr fun a => mem_iInter.mpr fun ha => ?_
  apply isClosed_closure.mem_of_tendsto hlim
  filter_upwards [hnear, htTop (eventually_ge_atTop (a-s))] with j hj hja
  change a - s ≤ t j at hja
  have htrans := Flow.flow_translation F hF x hx (t j) (ht j).1
  have hst : s + t j ∈ (flowInterval F x).carrier := by
    have hjs := hj.2
    rw [htrans.1] at hjs
    exact hjs
  have heq := htrans.2 s hst
  change flow F s (flow F (t j) x) ∈ closure (orbitTail F x a)
  rw [heq]
  exact subset_closure ⟨s + t j, ⟨hst, by linarith⟩, rfl⟩

omit [FiniteDimensional ℝ E] in
/-- Compact nested tails eventually lie in every distance neighborhood of
their intersection. This proves attraction for continuous real time. -/
lemma distance_tendsto (F : AutonomousODE E) {x : E}
    (hcomplete : Ici 0 ⊆ (flowInterval F x).carrier)
    (hK : IsCompact (closure (positiveOrbit F x))) :
    Tendsto (fun t : ℝ => infDist (flow F t x) (omegaValue F x)) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun _ => ha.trans_le infDist_nonneg
  · intro ε hε
    let U : Set E := {z | infDist z (omegaValue F x) < ε}
    have hU : IsOpen U := isOpen_lt (continuous_infDist_pt _) continuous_const
    have hcover : omegaValue F x ⊆ U := by
      intro y hy
      change infDist y (omegaValue F x) < ε
      simpa only [infDist_zero_of_mem hy] using hε
    let T : ℕ → Set E := fun n => closure (orbitTail F x n)
    have hmono : Antitone T := by
      intro m n hmn
      exact closure_mono (OmegaTopology.orbitTail_antitone F x (by exact_mod_cast hmn))
    have hbad : Disjoint (closure (positiveOrbit F x) \ U) (⋂ n, T n) := by
      rw [← OmegaTopology.omega_eq_nat_inter F x]
      exact disjoint_left.mpr fun _ hz hw => hz.2 (hcover hw)
    obtain ⟨n, hn⟩ := (hK.diff hU).elim_directed_family_closed T
      (fun _ => isClosed_closure) hbad hmono.directed_ge
    filter_upwards [eventually_ge_atTop (n : ℝ)] with t ht
    have ht0 : 0 ≤ t := (Nat.cast_nonneg n).trans ht
    have hpt : flow F t x ∈ T n :=
      subset_closure ⟨t, ⟨hcomplete ht0, ht⟩, rfl⟩
    by_contra h
    exact disjoint_left.mp hn
      ⟨subset_closure ⟨t, ⟨hcomplete ht0, ht0⟩, rfl⟩, h⟩ hpt

/-- All conclusions of the compact omega-limit theorem on the actual state
and time domains, including full invariance and complete two-sided orbits. -/
theorem compact_omega : Specs.D13Unified.Ch11.Omega.CompactOmega.{u} := by
  intro E _ _ _ F hF x hx hK hKΩ
  obtain ⟨hforward, hne, hcompact, hconnected, hsub⟩ :=
    OmegaTopology.compact_omega_topology F hF x hx hK hKΩ
  have hinv := omega_invariant F hF hx hKΩ
  have hcomplete := Invariant.compact_complete F hF (omegaValue F x) hcompact hinv
  refine ⟨hforward, hne, hcompact, hconnected, hsub, hinv, hcomplete, ?_,
    fun y => OmegaTopology.sequence_characterization F x y,
    distance_tendsto F hforward hK⟩
  intro t
  apply Subset.antisymm
  · rintro _ ⟨y, hy, rfl⟩
    exact (hcomplete y hy).2 t
  · intro y hy
    have hz := (hcomplete y hy).2 (-t)
    refine ⟨flow F (-t) y, hz, ?_⟩
    have hrev := Flow.reverse_flow F hF
      (show y ∈ timeDomainValue F (-t) from
        ⟨hinv.1 hy, (hcomplete y hy).1.symm ▸ mem_univ (-t)⟩)
    simpa only [neg_neg] using hrev.2

end D13Unified.Ch11.Omega
