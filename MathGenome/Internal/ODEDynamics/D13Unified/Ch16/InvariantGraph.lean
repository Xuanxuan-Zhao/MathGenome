import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch16.InvariantGraph
import MathGenome.Internal.ODEDynamics.D13Unified.Ch03.LocalExistenceUniqueness
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Prod

noncomputable section
open Set Metric Filter
open scoped Topology

namespace D13Unified.Ch16.InvariantGraph
universe u v
variable {E : Type u} {G : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

@[simp] lemma odeOn_eval {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (U : Set X) (hU : IsOpen U) (V : X → X) (hV : ContinuousOn V U)
    (t : ℝ) {x : X} (hx : x ∈ U) :
    (odeOn U hU V hV).eval t x = V x := by
  exact ODE.eval_of_mem _ hx

lemma c1_locallyLipschitz {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (U : Set X) (hU : IsOpen U) (V : X → X) (hV : ContDiffOn ℝ 1 V U) :
    Specs.D13Unified.Ch03.LocalLipschitz.locallyLipschitzInStateValue
      (odeOn U hU V hV.continuousOn) := by
  intro s ξ hξ
  obtain ⟨K, A, hA, hK⟩ := (hV.contDiffAt (hU.mem_nhds hξ)).exists_lipschitzOnWith
  obtain ⟨b, hb, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem hA (hU.mem_nhds hξ))
  refine ⟨1, b, K, zero_lt_one, hb, K.coe_nonneg, ?_, ?_⟩
  · intro p hp
    exact (hball hp.2).2
  · intro t ht x hx y hy
    simp only [odeOn_eval U hU V hV.continuousOn t (hball hx).2,
      odeOn_eval U hU V hV.continuousOn t (hball hy).2]
    exact hK.norm_sub_le (hball hx).1 (hball hy).1

namespace GraphSystem
variable (S : GraphSystem E G)

@[simp] lemma full_eval (t : ℝ) {z : E × G} (hz : z ∈ S.domain) :
    S.fullODE.eval t z = S.field z := odeOn_eval _ _ _ _ t hz

@[simp] lemma reduced_eval (t : ℝ) {x : E} (hx : x ∈ S.base) :
    S.reducedODE.eval t x = S.reducedField x := odeOn_eval _ _ _ _ t hx

lemma graph_hasFDerivAt {x : E} (hx : x ∈ S.base) :
    HasFDerivAt S.graph (fderiv ℝ S.graph x) x :=
  ((S.graph_c1.contDiffAt (S.isOpen_base.mem_nhds hx)).differentiableAt one_ne_zero).hasFDerivAt

lemma full_lipschitz : Specs.D13Unified.Ch03.LocalLipschitz.locallyLipschitzInStateValue
    S.fullODE := c1_locallyLipschitz _ _ _ S.field_c1

lemma reduced_lipschitz : Specs.D13Unified.Ch03.LocalLipschitz.locallyLipschitzInStateValue
    S.reducedODE := c1_locallyLipschitz _ _ _ S.reduced_c1

end GraphSystem

open Specs.D13Unified.Ch16.InvariantGraph

theorem lift_solutions : liftSolutionsExpected.{u, v} := by
  intro E G _ _ _ _ S hS I x hx
  have hr : ∀ t ∈ I.carrier, x t ∈ S.base := hx.2.1
  refine ⟨S.lift_c1.continuousOn.comp hx.1 hr, ?_, ?_⟩
  · intro t ht
    exact S.graph_mem _ (hr t ht)
  · intro t ht
    have hd : HasDerivWithinAt x (S.reducedField (x t)) I.carrier t := by
      simpa only [S.reduced_eval t (hr t ht)] using hx.2.2 t ht
    have hg := (S.graph_hasFDerivAt (hr t ht)).comp_hasDerivWithinAt t hd
    rw [hS _ (hr t ht)] at hg
    simpa only [S.full_eval t (S.graph_mem _ (hr t ht)), GraphSystem.lift,
      GraphSystem.reducedField, Prod.eta, Function.comp_def] using hd.prodMk hg

/-- On open intervals the endpoint-aware lift is the classical C¹ lift. -/
lemma lift_classical (S : GraphSystem E G) (hS : S.Tangent)
    (I : OpenTimeInterval) (x : ℝ → E)
    (hx : IsClassicalSolutionOn S.reducedODE I x) :
    IsClassicalSolutionOn S.fullODE I (fun t => S.lift (x t)) := by
  apply (classical_iff_solutionOn _ _ _).mpr
  exact lift_solutions S hS I.toTimeInterval x
    ((classical_iff_solutionOn _ _ _).mp hx)

theorem identify_solutions : identifySolutionsExpected.{u, v} := by
  intro E G _ _ _ _ _ _ S hS I J x z s ξ hx hz
  have hlift : IsClassicalIVPOn S.fullODE I (fun t => S.lift (x t)) s (S.lift ξ) :=
    ⟨lift_classical S hS I x hx.1, hx.2.1, congrArg S.lift hx.2.2⟩
  exact Ch03.LocalExistenceUniqueness.overlap_uniqueness S.fullODE S.full_lipschitz
    I J _ z s (S.lift ξ) hlift hz

/-- Existence is derived from the original C¹ hypothesis, so the local
invariance predicate cannot hold just because there are no trajectories. -/
lemma GraphSystem.exists_full [FiniteDimensional ℝ E] [FiniteDimensional ℝ G]
    (S : GraphSystem E G) (x : E) (hx : x ∈ S.base) :
    ∃ (I : OpenTimeInterval) (z : ℝ → E × G),
      IsClassicalIVPOn S.fullODE I z 0 (S.lift x) := by
  obtain ⟨I, z, hz, _⟩ := Ch03.LocalExistenceUniqueness.local_existence_uniqueness
    S.fullODE S.full_lipschitz 0 (S.lift x) (S.graph_mem x hx)
  exact ⟨I, z, hz⟩

theorem invariant_graph : invariantGraphExpected.{u, v} := by
  intro E G _ _ _ _ _ _ S
  constructor
  · intro hS x hx I z hz
    obtain ⟨K, u, hu, _⟩ := Ch03.LocalExistenceUniqueness.local_existence_uniqueness
      S.reducedODE S.reduced_lipschitz 0 x hx
    have heq := identify_solutions S hS K I u z 0 x hu hz
    let J : OpenTimeInterval :=
      { carrier := K.carrier ∩ I.carrier
        nonempty := ⟨0, hu.2.1, hz.2.1⟩
        ordConnected := K.ordConnected.inter I.ordConnected
        isOpen := K.isOpen.inter I.isOpen }
    refine ⟨J, ⟨hu.2.1, hz.2.1⟩, inter_subset_right, ?_⟩
    intro t ht
    have hzt : z t = S.lift (u t) := (heq ht).symm
    rw [hzt]
    exact ⟨hu.1.2.1 t ht.1, rfl⟩
  · intro hS x hx
    obtain ⟨I, z, hz⟩ := S.exists_full x hx
    obtain ⟨J, h0, hJI, hgraph⟩ := hS x hx I z hz
    have hd : HasDerivAt z (S.field (S.lift x)) 0 := by
      have h := hz.1.2.2 0 hz.2.1
      rw [hz.2.2] at h
      have he : S.fullODE.eval 0 (S.lift x) = S.field (S.lift x) :=
        S.full_eval 0 (S.graph_mem x hx)
      rw [he] at h
      exact h
    have hf : HasDerivAt (fun t => (z t).1) (S.reducedField x) 0 := by
      simpa only [Function.comp_def, ContinuousLinearMap.coe_fst',
        GraphSystem.reducedField] using
        (ContinuousLinearMap.fst ℝ E G).hasFDerivAt.comp_hasDerivAt 0 hd
    have hg : HasDerivAt (fun t => (z t).2) (S.field (S.lift x)).2 0 := by
      simpa only [Function.comp_def, ContinuousLinearMap.coe_snd'] using
        (ContinuousLinearMap.snd ℝ E G).hasFDerivAt.comp_hasDerivAt 0 hd
    have hh : HasFDerivAt S.graph (fderiv ℝ S.graph x) (z 0).1 := by
      simpa only [hz.2.2, GraphSystem.lift] using S.graph_hasFDerivAt hx
    have hc := hh.comp_hasDerivAt 0 hf
    have heq : (fun t => (z t).2) =ᶠ[𝓝 0] (fun t => S.graph (z t).1) := by
      filter_upwards [J.isOpen.mem_nhds h0] with t ht
      exact (hgraph t ht).2
    exact (hc.congr_of_eventuallyEq heq).unique hg

end D13Unified.Ch16.InvariantGraph
