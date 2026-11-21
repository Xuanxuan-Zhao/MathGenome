import MathGenome.Internal.LinearPDE.P201Specs.Potential.PerronReplacement
import MathGenome.Internal.LinearPDE.P201.Potential.SubharmonicComparison
import MathGenome.Internal.LinearPDE.P201.Potential.BallPoisson
import Mathlib.Topology.Piecewise

noncomputable section
open Set Metric Filter
open scoped Topology

namespace P201.PerronReplacement
open P201Specs
open P201Specs.SubharmonicMaximum
open P201Specs.PerronReplacement

abbrev perronClass : PerronClassType := @P201Specs.PerronReplacement.perronClass

/-- The continuous boundary trace computes the extended-real interior limsup. -/
lemma limsup_coe_eq {n : ℕ} {S C : Set (Space n)} {u : Space n → ℝ}
    (hc : ContinuousOn u C) (hSC : S ⊆ C) {z : Space n} (hz : z ∈ C)
    (hzS : z ∈ closure S) :
    limsup (fun x => (u x : EReal)) (𝓝[S] z) = (u z : EReal) := by
  have : NeBot (𝓝[S] z) := mem_closure_iff_nhdsWithin_neBot.mp hzS
  exact (continuous_coe_real_ereal.continuousAt.tendsto.comp
    ((hc z hz).mono hSC)).limsup_eq

lemma comparison {n : ℕ} (hn : 2 ≤ n) (Ω : Domain n) (u : Space n → ℝ)
    (hc : ContinuousOn u (Ω : Set _))
    (hu : IsSubharmonic Ω (fun x => (u x : EReal)))
    (a : Space n) (r : ℝ) (hr : 0 < r) (hD : closedBall a r ⊆ (Ω : Set _))
    (h : Space n → ℝ) (hh : MeanValues.IsHarmonic ⟨ball a r, isOpen_ball⟩ h)
    (hhc : ContinuousOn h (closedBall a r))
    (hb : ∀ z ∈ sphere a r, u z ≤ h z) :
    ∀ x ∈ ball a r, u x ≤ h x := by
  have hcomp := (SubharmonicComparison.equivalence hn Ω _ hu.1).2.mp hu.2
  have he := hcomp a r hr hD h hh hhc (by
    intro z hz
    rw [limsup_coe_eq hc (ball_subset_closedBall.trans hD)
      (hD (sphere_subset_closedBall hz)) (by
        rw [closure_ball a hr.ne']; exact sphere_subset_closedBall hz)]
    exact EReal.coe_le_coe_iff.mpr (hb z hz))
  exact fun x hx => EReal.coe_le_coe_iff.mp (he x hx)

lemma subharmonic_of_comparison {n : ℕ} (hn : 2 ≤ n) (Ω : Domain n)
    (u : Space n → ℝ) (hc : ContinuousOn u (Ω : Set _))
    (hcomp : ∀ a r, 0 < r → closedBall a r ⊆ (Ω : Set _) →
      ∀ h : Space n → ℝ,
      MeanValues.IsHarmonic ⟨ball a r, isOpen_ball⟩ h →
      ContinuousOn h (closedBall a r) →
      (∀ z ∈ sphere a r, u z ≤ h z) → ∀ x ∈ ball a r, u x ≤ h x) :
    IsSubharmonic Ω (fun x => (u x : EReal)) := by
  have had := SubharmonicMaximum.real_admissible Ω u hc
  refine ⟨had, (SubharmonicComparison.equivalence hn Ω _ had).2.mpr ?_⟩
  intro a r hr hD h hh hhc hb x hx
  apply EReal.coe_le_coe_iff.mpr
  apply hcomp a r hr hD h hh hhc ?_ x hx
  intro z hz
  have hbz := hb z hz
  rw [limsup_coe_eq hc (ball_subset_closedBall.trans hD)
    (hD (sphere_subset_closedBall hz)) (by
      rw [closure_ball a hr.ne']; exact sphere_subset_closedBall hz)] at hbz
  exact EReal.coe_le_coe_iff.mp hbz

theorem max_closure : MaxClosureStatement := by
  intro n hn Ω g u v hu hv
  refine ⟨hu.1.sup hv.1, ?_, fun z => max_le (hu.2.2 z) (hv.2.2 z)⟩
  apply subharmonic_of_comparison hn Ω _ ((hu.1.sup hv.1).mono subset_closure)
  intro a r hr hD h hh hhc hb x hx
  exact max_le
    (comparison hn Ω u (hu.1.mono subset_closure) hu.2.1 a r hr hD h hh hhc
      (fun z hz => (le_max_left _ _).trans (hb z hz)) x hx)
    (comparison hn Ω v (hv.1.mono subset_closure) hv.2.1 a r hr hD h hh hhc
      (fun z hz => (le_max_right _ _).trans (hb z hz)) x hx)

/-- A bounded open set requires no boundary regularity for harmonic comparison. -/
lemma harmonic_nonpos {n : ℕ} (hn : 2 ≤ n) (Ω : Domain n)
    (hΩ : Bornology.IsBounded (Ω : Set (Space n))) (u : Space n → ℝ)
    (hu : MeanValues.IsHarmonic Ω u) (hc : ContinuousOn u (closure (Ω : Set _)))
    (hb : ∀ z ∈ frontier (Ω : Set (Space n)), u z ≤ 0) :
    ∀ x ∈ Ω, u x ≤ 0 := by
  have hs : IsSubharmonic Ω (fun x => (u x : EReal)) :=
    (SubharmonicComparison.smooth_criterion hn Ω u hu.1).2.2.2.mpr
      (fun x hx => (hu.2 x hx).ge)
  have hboundary : ∀ z ∈ frontier (Ω : Set (Space n)),
      limsup (fun x => (u x : EReal)) (𝓝[Ω] z) ≤ (0 : EReal) := by
    intro z hz
    rw [limsup_coe_eq hc subset_closure hz.1 hz.1]
    exact EReal.coe_le_coe_iff.mpr (hb z hz)
  exact fun x hx => EReal.coe_le_coe_iff.mp
    (SubharmonicComparison.boundary_maximum hn Ω _ 0 hΩ hs hboundary x hx)

lemma harmonic_congr {n : ℕ} (Ω : Domain n) {u v : Space n → ℝ}
    (hu : MeanValues.IsHarmonic Ω u) (he : EqOn u v (Ω : Set _)) :
    MeanValues.IsHarmonic Ω v := by
  apply (P201.MeanValues.harmonic_bridge Ω v).mpr
  intro x hx
  apply (InnerProductSpace.harmonicAt_congr_nhds (f₁ := u) (f₂ := v) ?_).mp
    (((P201.MeanValues.harmonic_bridge Ω u).mp hu) x hx)
  filter_upwards [Ω.isOpen.mem_nhds hx] with y hy
  exact he hy

/-- Continuous harmonic raising remains subharmonic across its interface. -/
lemma harmonic_paste {n : ℕ} (hn : 2 ≤ n) (Ω D : Domain n)
    (u p : Space n → ℝ)
    (hu : IsSubharmonic Ω (fun x => (u x : EReal)))
    (huc : ContinuousOn u (Ω : Set _)) (hpc : ContinuousOn p (Ω : Set _))
    (hp : MeanValues.IsHarmonic D p) (hle : u ≤ p)
    (he : ∀ x ∉ (D : Set _), p x = u x) :
    IsSubharmonic Ω (fun x => (p x : EReal)) := by
  apply subharmonic_of_comparison hn Ω p hpc
  intro a r hr hB h hh hhc hb
  have huh : ∀ x ∈ closedBall a r, u x ≤ h x := by
    intro x hx
    by_cases hi : x ∈ ball a r
    · exact comparison hn Ω u huc hu a r hr hB h hh hhc
        (fun z hz => (hle z).trans (hb z hz)) x hi
    · exact (hle x).trans (hb x (by
        rw [mem_sphere]; exact le_antisymm hx (le_of_not_gt hi)))
  let V : Domain n := ⟨(D : Set _) ∩ ball a r, D.isOpen.inter isOpen_ball⟩
  have hVC : closure (V : Set (Space n)) ⊆ closedBall a r :=
    closure_minimal (inter_subset_right.trans ball_subset_closedBall) isClosed_closedBall
  have hf : MeanValues.IsHarmonic V (fun x => p x - h x) :=
    (P201.MeanValues.harmonic_bridge V _).mpr
      ((((P201.MeanValues.harmonic_bridge D p).mp hp).mono inter_subset_left).sub
        (((P201.MeanValues.harmonic_bridge _ h).mp hh).mono inter_subset_right))
  have hfc : ContinuousOn (fun x => p x - h x) (closure (V : Set _)) :=
    (hpc.mono (hVC.trans hB)).sub (hhc.mono hVC)
  have hfront : ∀ z ∈ frontier (V : Set (Space n)), p z - h z ≤ 0 := by
    intro z hz
    apply sub_nonpos.mpr
    have hzC := hVC hz.1
    by_cases hzD : z ∈ (D : Set _)
    · have hnB : z ∉ ball a r := by
        intro hzB
        have := hz.2
        rw [V.isOpen.interior_eq] at this
        exact this ⟨hzD, hzB⟩
      exact hb z (by rw [mem_sphere]; exact le_antisymm hzC (le_of_not_gt hnB))
    · rw [he z hzD]
      exact huh z hzC
  have hleV := harmonic_nonpos hn V
    (isBounded_ball.subset inter_subset_right) _ hf hfc hfront
  intro x hx
  by_cases hxD : x ∈ (D : Set _)
  · exact sub_nonpos.mp (hleV x ⟨hxD, hx⟩)
  · rw [he x hxD]
    exact huh x (ball_subset_closedBall hx)

theorem harmonic_raising : HarmonicRaisingStatement := by
  classical
  intro n hn Ω g a r hr hD u hu
  let q : C(sphere a r, ℝ) :=
    ⟨fun z => u z, (hu.1.mono ((sphere_subset_closedBall.trans hD).trans
      subset_closure)).domRestrict⟩
  let H := P201Specs.BallPoisson.poissonExtension a r q
  have hHc : ContinuousOn H (closedBall a r) :=
    (BallPoisson.continuous_extension hn a r hr q).1
  have hHb : ∀ z ∈ sphere a r, H z = u z := fun z hz =>
    (BallPoisson.continuous_extension hn a r hr q).2 ⟨z, hz⟩
  have hH : MeanValues.IsHarmonic ⟨ball a r, isOpen_ball⟩ H :=
    BallPoisson.poissonExtension_harmonic hn a hr q
  let p : Space n → ℝ := fun x => if x ∈ ball a r then H x else u x
  have hpc : ContinuousOn p (closure (Ω : Set _)) := by
    apply ContinuousOn.if
    · intro z hz
      exact hHb z (frontier_ball_subset_sphere hz.2)
    · exact hHc.mono (fun z hz => closure_ball_subset_closedBall hz.2)
    · exact hu.1.mono inter_subset_left
  have hp : MeanValues.IsHarmonic ⟨ball a r, isOpen_ball⟩ p :=
    harmonic_congr _ hH (fun x hx => by
      change x ∈ ball a r at hx
      simp only [p, ite_eq_left hx])
  have hle : u ≤ p := by
    have hc := comparison hn Ω u (hu.1.mono subset_closure) hu.2.1
      a r hr hD H hH hHc (fun z hz => (hHb z hz).ge)
    intro x
    by_cases hx : x ∈ ball a r
    · simpa only [p, ite_eq_left hx] using hc x hx
    · simp only [p, ite_eq_right hx, le_refl]
  refine ⟨p, ⟨hpc, ?_, ?_⟩, hle, hp⟩
  · exact harmonic_paste hn Ω ⟨ball a r, isOpen_ball⟩ u p hu.2.1
      (hu.1.mono subset_closure) (hpc.mono subset_closure) hp hle
      (fun x hx => by
        change x ∉ ball a r at hx
        simp only [p, ite_eq_right hx])
  · intro z
    have hz : (z : Space n) ∉ ball a r := by
      intro hi
      exact z.property.2 (by
        rw [Ω.isOpen.interior_eq]
        exact hD (ball_subset_closedBall hi))
    simpa only [p, ite_eq_right hz] using hu.2.2 z

end P201.PerronReplacement
