import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch11.Orbits
import MathGenome.Internal.ODEDynamics.D13Unified.Ch11.Flow
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Algebra.Field.Periodic

/-! Orbit alternatives on the canonical maximal domain. -/
noncomputable section
open Set Filter
open scoped Topology

namespace D13Unified.Ch11.Orbits
open Ch06.StateDerivative
open Specs.D13Unified.Ch01.AutonomousParameters
open Specs.D13Unified.Ch01.SolutionConcepts
open Specs.D13Unified.Ch04.MaximalSolutionMap
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma constant_equilibrium (F : AutonomousODE E) (hF : ContDiffOn ℝ 1 F.eval F.domain)
    {p : E} (hp : p ∈ F.domain) (he : F.eval p = 0) :
    IsComplete F p ∧ IsConstant F p := by
  let J : OpenTimeInterval := ⟨⟨univ, univ_nonempty, ordConnected_univ⟩, isOpen_univ⟩
  have hc : classicalIVPOnValue F.toODE J (fun _ => p) 0 p := by
    refine ⟨⟨contDiffOn_const, fun _ _ => hp, ?_⟩, mem_univ _, rfl⟩
    intro t ht
    simpa only [AutonomousODE.toODE_eval, he] using hasDerivAt_const t p
  have h := (ODE.canonical_solution F.toODE
    (F.locallyLipschitzInState_of_contDiffOn hF) 0 p hp).2.2.2.2.2.1 J _ hc
  exact ⟨Subset.antisymm (subset_univ _) h.1, fun t _ => h.2 (mem_univ t)⟩

theorem equilibrium_characterization :
    Specs.D13Unified.Ch11.Orbits.EquilibriumCharacterization.{u} := by
  intro E _ _ _ F hF p hp
  constructor
  · exact fun he => (constant_equilibrium F hF hp he).2
  · intro hc
    have hX := flow_ivp F hF hp
    have hd := hX.1.2.2 0 hX.2.1
    have hn : (fun t => flow F t p) =ᶠ[𝓝 0] (fun _ => p) := by
      filter_upwards [(flowInterval F p).isOpen.mem_nhds hX.2.1] with t ht
      exact hc t ht
    have hd0 := hd.congr_of_eventuallyEq hn.symm
    simpa only [AutonomousODE.toODE_eval, hX.2.2, AutonomousODE.eval] using
      hd0.unique (hasDerivAt_const (0 : ℝ) p)

theorem equilibrium_complete : Specs.D13Unified.Ch11.Orbits.EquilibriumComplete.{u} := by
  intro E _ _ _ F hF p hp he
  exact (constant_equilibrium F hF hp he).1

/-- Rebasing an orbit changes its time coordinates by a translation and hence
preserves its image as a set. -/
lemma orbit_rebase (F : AutonomousODE E) (hF : ContDiffOn ℝ 1 F.eval F.domain)
    {x : E} (hx : x ∈ F.domain) {s : ℝ} (hs : s ∈ (flowInterval F x).carrier) :
    orbit F (flow F s x) = orbit F x := by
  have hT := Flow.flow_translation F hF x hx s hs
  apply Subset.antisymm
  · rintro _ ⟨t, ht, rfl⟩
    rw [hT.1] at ht
    exact ⟨t+s, ht, (hT.2 t ht).symm⟩
  · rintro _ ⟨t, ht, rfl⟩
    have hm : t-s ∈ (flowInterval F (flow F s x)).carrier := by
      rw [hT.1]; simpa using ht
    exact ⟨t-s, hm, by simpa using hT.2 (t-s) (by simpa using ht)⟩

theorem orbit_partition : Specs.D13Unified.Ch11.Orbits.OrbitPartition.{u} := by
  intro E _ _ _ F hF x hx y hy
  by_cases hd : Disjoint (orbit F x) (orbit F y)
  · exact Or.inl hd
  · right
    obtain ⟨z, hzx, hzy⟩ := Set.not_disjoint_iff.mp hd
    obtain ⟨s, hs, hsz⟩ := hzx
    obtain ⟨t, ht, htz⟩ := hzy
    exact (orbit_rebase F hF hx hs).symm.trans
      ((congrArg (orbit F) (hsz.trans htz.symm)).trans (orbit_rebase F hF hy ht))


/-- A return forces the entire maximal interval to repeat. Reducing any real
time modulo the return time then puts it in that interval. -/
lemma complete_of_positive_return (F : AutonomousODE E)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {y : E} (hy : y ∈ F.domain)
    {T : ℝ} (hT : 0 < T) (hTI : T ∈ (flowInterval F y).carrier)
    (hr : flow F T y = y) :
    IsComplete F y ∧ Function.Periodic (fun t => flow F t y) T := by
  have hX := flow_ivp F hF hy
  have hTr := Flow.flow_translation F hF y hy T hTI
  rw [hr] at hTr
  have hi (t : ℝ) : t ∈ (flowInterval F y).carrier ↔
      t+T ∈ (flowInterval F y).carrier := by
    change t ∈ (flowInterval F y).carrier ↔ t ∈ {r | r+T ∈ (flowInterval F y).carrier}
    rw [← hTr.1]
  have hm : Function.Periodic (fun t => t ∈ (flowInterval F y).carrier) T :=
    fun t => propext (hi t).symm
  have hall (t : ℝ) : t ∈ (flowInterval F y).carrier := by
    obtain ⟨r, hr, he⟩ := hm.exists_mem_Ico₀ hT t
    have hri : r ∈ (flowInterval F y).carrier :=
      (flowInterval F y).ordConnected.out hX.2.1 hTI ⟨hr.1, hr.2.le⟩
    exact he.mpr hri
  exact ⟨eq_univ_of_forall hall, fun t => (hTr.2 t (hall _)).symm⟩

lemma ordered_self_intersection (F : AutonomousODE E)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {x : E} (hx : x ∈ F.domain)
    {t₁ t₂ : ℝ} (h₁ : t₁ ∈ (flowInterval F x).carrier)
    (h₂ : t₂ ∈ (flowInterval F x).carrier) (hlt : t₁ < t₂)
    (he : flow F t₁ x = flow F t₂ x) :
    IsComplete F x ∧ Function.Periodic (fun t => flow F t x) (t₂-t₁) := by
  let y := flow F t₁ x
  have hy : y ∈ F.domain := (flow_ivp F hF hx).1.2.1 t₁ h₁
  have hTr := Flow.flow_translation F hF x hx t₁ h₁
  have hTI : t₂-t₁ ∈ (flowInterval F y).carrier := by
    rw [hTr.1]; simpa using h₂
  have hreturn : flow F (t₂-t₁) y = y := by
    calc flow F (t₂-t₁) y = flow F t₂ x := by
           simpa using hTr.2 (t₂-t₁) (by simpa using h₂)
         _ = y := he.symm
  obtain ⟨hcomplete, hperiod⟩ := complete_of_positive_return F hF hy
    (sub_pos.mpr hlt) hTI hreturn
  have hall (t : ℝ) : t ∈ (flowInterval F x).carrier := by
    have hi : t-t₁ ∈ (flowInterval F y).carrier := by rw [hcomplete]; trivial
    rw [hTr.1] at hi
    simpa using hi
  refine ⟨eq_univ_of_forall hall, ?_⟩
  intro t
  calc flow F (t+(t₂-t₁)) x = flow F ((t+(t₂-t₁))-t₁) y := by
         symm; simpa using hTr.2 ((t+(t₂-t₁))-t₁) (by simpa using hall (t+(t₂-t₁)))
       _ = flow F ((t-t₁)+(t₂-t₁)) y := by congr 1; ring
       _ = flow F (t-t₁) y := hperiod _
       _ = flow F t x := by simpa using hTr.2 (t-t₁) (by simpa using hall t)

theorem self_intersection : Specs.D13Unified.Ch11.Orbits.SelfIntersection.{u} := by
  intro E _ _ _ F hF x hx t₁ h₁ t₂ h₂ hne he
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact ordered_self_intersection F hF hx h₁ h₂ hlt he
  · obtain ⟨hc, hp⟩ := ordered_self_intersection F hF hx h₂ h₁ hgt he.symm
    exact ⟨hc, by convert hp.neg using 1; ring⟩

/-- The additive period group of an ambient curve. Its use for a trajectory
below follows only after its actual domain has been proved to be ℝ. -/
def periodGroup {A : Type*} (g : ℝ → A) : AddSubgroup ℝ where
  carrier := {T | Function.Periodic g T}
  zero_mem' := Function.periodic_with_period_zero g
  add_mem' := fun ha hb => ha.add_period hb
  neg_mem' := fun ha => ha.neg

/-- A nonconstant continuous real-time curve with a nonzero period has a least
positive period. A subgroup without a least positive element is dense; continuity
would then force the curve to be constant. -/
lemma exists_least_period {A : Type*} [TopologicalSpace A] [T2Space A]
    (g : ℝ → A) (hg : Continuous g) (hn : ¬ ∀ t, g t = g 0)
    {S : ℝ} (hS : S ≠ 0) (hp : Function.Periodic g S) :
    ∃ T : ℝ, 0 < T ∧ Function.Periodic g T ∧
      (∀ R : ℝ, 0 < R → Function.Periodic g R → T ≤ R) ∧
      ∀ R : ℝ, Function.Periodic g R ↔ ∃ k : ℤ, R = (k : ℝ)*T := by
  let G := periodGroup g
  have hbot : G ≠ ⊥ := by
    intro he
    have hm : S ∈ G := hp
    rw [he] at hm
    exact hS (by simpa using hm)
  have hleast : ∃ T : ℝ, IsLeast {R : ℝ | R ∈ G ∧ 0 < R} T := by
    by_contra h
    have hd := G.dense_of_no_min hbot h
    apply hn
    intro t
    apply closure_minimal (t := {r : ℝ | g r = g 0}) ?_ (isClosed_eq hg continuous_const) (hd t)
    intro r hr
    have h := hr (0 : ℝ)
    simpa using h
  obtain ⟨T, hT⟩ := hleast
  have hG : AddSubgroup.zmultiples T = G :=
    AddSubgroup.zmultiples_eq_of_isLeast_mem_and_pos hT
  refine ⟨T, hT.1.2, hT.1.1, fun R hR hpR => hT.2 ⟨hpR, hR⟩, ?_⟩
  intro R
  change R ∈ G ↔ _
  rw [← hG, AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by simpa only [zsmul_eq_mul] using hk.symm⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by simpa only [zsmul_eq_mul] using hk.symm⟩

theorem orbit_alternatives : Specs.D13Unified.Ch11.Orbits.OrbitAlternatives.{u} := by
  classical
  intro E _ _ _ F hF x hx hn
  by_cases hi : Set.InjOn (fun t => flow F t x) (flowInterval F x).carrier
  · exact Or.inl hi
  · right
    have hnot : ∃ t₁ ∈ (flowInterval F x).carrier, ∃ t₂ ∈ (flowInterval F x).carrier,
        flow F t₁ x = flow F t₂ x ∧ t₁ ≠ t₂ := by
      simpa only [Set.InjOn, not_forall, exists_prop, not_imp] using hi
    obtain ⟨t₁, h₁, t₂, h₂, he, hne⟩ := hnot
    obtain ⟨hc, hp⟩ := self_intersection F hF x hx t₁ h₁ t₂ h₂ hne he
    change (flowInterval F x).carrier = univ at hc
    have hX := flow_ivp F hF hx
    have hcont : Continuous (fun t => flow F t x) := by
      apply continuousOn_univ.mp
      simpa only [hc] using hX.1.1.continuousOn
    have hnon : ¬ ∀ t, flow F t x = flow F 0 x := by
      intro heq
      exact hn (fun t _ => (heq t).trans hX.2.2)
    exact ⟨hc, exists_least_period _ hcont hnon (sub_ne_zero.mpr hne.symm) hp⟩

/-- The nonconstant branch of the orbit alternative cannot be injective in
the presence of an actual self-intersection. -/
theorem self_intersection_least_period :
    Specs.D13Unified.Ch11.Orbits.SelfIntersectionLeastPeriod.{u} := by
  intro E _ _ _ F hF x hx hn t₁ h₁ t₂ h₂ hne he
  rcases orbit_alternatives F hF x hx hn with hi | hp
  · exact (hne (hi h₁ h₂ he)).elim
  · exact hp

end D13Unified.Ch11.Orbits
