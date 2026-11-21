import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.PerronEnvelope
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch14.HarmonicReplacementPasting
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch13.HarnackConvergence
import Mathlib.Topology.Order.IsLUB

noncomputable section
open Set Metric Filter
open scoped Topology

namespace D12Complex.PerronEnvelope

abbrev perronClass := D12Complex.perronClass
abbrev perronEnvelope := D12Complex.perronEnvelope

lemma class_const {Ω : Set ℂ} {φ : ℂ → ℝ} (hΩ : IsOpen Ω) {m : ℝ}
    (hm : ∀ ξ ∈ frontier Ω, m ≤ φ ξ) : (fun _ => m) ∈ perronClass Ω φ := by
  refine ⟨SubharmonicOperations.subharmonicOn_const Ω m hΩ, ?_⟩
  intro ξ hξ ε hε
  exact ⟨1, zero_lt_one, fun _ _ _ => (hm ξ hξ).trans (le_add_of_nonneg_right hε.le)⟩

lemma class_upper_bound {Ω : Set ℂ} {φ u : ℂ → ℝ} {M : ℝ}
    (hΩ : Bornology.IsBounded Ω) (hu : u ∈ perronClass Ω φ)
    (hM : ∀ ξ ∈ frontier Ω, φ ξ ≤ M) : ∀ z ∈ Ω, u z ≤ M := by
  apply SubharmonicMaximum.subharmonic_boundary_maximum Ω u M hΩ hu.1
  intro ξ hξ ε hε
  obtain ⟨δ, hδ, hd⟩ := hu.2 ξ hξ ε hε
  exact ⟨δ, hδ, fun z hz hd' => (hd z hz hd').trans (by linarith [hM ξ hξ])⟩

lemma class_max {Ω : Set ℂ} {φ u v : ℂ → ℝ}
    (hu : u ∈ perronClass Ω φ) (hv : v ∈ perronClass Ω φ) :
    (fun z => max (u z) (v z)) ∈ perronClass Ω φ := by
  refine ⟨SubharmonicOperations.subharmonicOn_max Ω u v hu.1 hv.1, ?_⟩
  intro ξ hξ ε hε
  obtain ⟨δ, hδ, hd⟩ := hu.2 ξ hξ ε hε
  obtain ⟨η, hη, he⟩ := hv.2 ξ hξ ε hε
  exact ⟨min δ η, lt_min hδ hη, fun z hz ht =>
    max_le (hd z hz (ht.trans_le (min_le_left _ _)))
      (he z hz (ht.trans_le (min_le_right _ _)))⟩

lemma class_replacement {Ω : Set ℂ} {φ u : ℂ → ℝ} {a : ℂ} {R : ℝ}
    (hu : u ∈ perronClass Ω φ) (hR : 0 < R) (hsub : closedBall a R ⊆ Ω) :
    harmonicReplacement a R u ∈ perronClass Ω φ := by
  refine ⟨(HarmonicReplacementPasting.harmonicReplacement_properties Ω u a R
    hu.1 hR hsub).2.1, ?_⟩
  intro ξ hξ ε hε
  have hn : ξ ∉ closedBall a R := by
    intro hi
    exact (show ξ ∈ closure Ω ∧ ξ ∉ Ω by simpa [hu.1.1.frontier_eq] using hξ).2 (hsub hi)
  obtain ⟨η, hη, he⟩ := Metric.isOpen_iff.mp isClosed_closedBall.isOpen_compl ξ hn
  obtain ⟨δ, hδ, hd⟩ := hu.2 ξ hξ ε hε
  refine ⟨min δ η, lt_min hδ hη, fun z hz ht => ?_⟩
  have hnz : z ∉ ball a R := fun hi => he (ht.trans_le (min_le_right _ _))
    (ball_subset_closedBall hi)
  simpa [harmonicReplacement, hnz] using hd z hz (ht.trans_le (min_le_left _ _))

lemma values_bddAbove {Ω : Set ℂ} {φ : ℂ → ℝ} {M : ℝ}
    (hΩ : Bornology.IsBounded Ω) (hM : ∀ ξ ∈ frontier Ω, φ ξ ≤ M)
    {z : ℂ} (hz : z ∈ Ω) :
    BddAbove ((fun u : ℂ → ℝ => u z) '' perronClass Ω φ) := by
  refine ⟨M, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  exact class_upper_bound hΩ hu hM z hz

lemma le_envelope {Ω : Set ℂ} {φ u : ℂ → ℝ} {z : ℂ}
    (hb : BddAbove ((fun u : ℂ → ℝ => u z) '' perronClass Ω φ))
    (hu : u ∈ perronClass Ω φ) : u z ≤ perronEnvelope Ω φ z :=
  le_csSup hb ⟨u, hu, rfl⟩


/-- Successive finite maxima make the approximating functions increasing on
all of Ω, even though they were selected only by their values at one point. -/
def successiveMax (u : ℕ → ℂ → ℝ) : ℕ → ℂ → ℝ
  | 0 => u 0
  | n + 1 => fun z => max (successiveMax u n z) (u (n + 1) z)

lemma successiveMax_mem {Ω : Set ℂ} {φ : ℂ → ℝ} {u : ℕ → ℂ → ℝ}
    (hu : ∀ n, u n ∈ perronClass Ω φ) :
    ∀ n, successiveMax u n ∈ perronClass Ω φ := by
  intro n
  induction n with
  | zero => exact hu 0
  | succ n ih => exact class_max ih (hu (n + 1))

lemma successiveMax_mono (u : ℕ → ℂ → ℝ) (z : ℂ) :
    Monotone (fun n => successiveMax u n z) :=
  monotone_nat_of_le_succ (fun _ => le_max_left _ _)

lemma le_successiveMax (u : ℕ → ℂ → ℝ) (n : ℕ) (z : ℂ) :
    u n z ≤ successiveMax u n z := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact le_max_right _ _

/-- An increasing sequence of class members, harmonic on the chosen disk,
which approaches the actual envelope at its center. -/
lemma extremizing_sequence {Ω : Set ℂ} {φ : ℂ → ℝ} {a : ℂ} {R : ℝ}
    (hne : (perronClass Ω φ).Nonempty) (hR : 0 < R) (hsub : closedBall a R ⊆ Ω)
    (hb : ∀ z ∈ Ω, BddAbove ((fun u : ℂ → ℝ => u z) '' perronClass Ω φ)) :
    ∃ v : ℕ → ℂ → ℝ, (∀ n, v n ∈ perronClass Ω φ) ∧
      (∀ n, HarmonicOn (ball a R) (v n)) ∧
      (∀ z ∈ Ω, Monotone (fun n => v n z)) ∧
      Tendsto (fun n => v n a) atTop (𝓝 (perronEnvelope Ω φ a)) := by
  have ha : a ∈ Ω := hsub (mem_closedBall_self hR.le)
  obtain ⟨c, _hcmono, hct, hc⟩ := exists_seq_tendsto_sSup
    (hne.image (fun u : ℂ → ℝ => u a)) (hb a ha)
  choose u hu he using hc
  let w := successiveMax u
  have hw : ∀ n, w n ∈ perronClass Ω φ := successiveMax_mem hu
  let v : ℕ → ℂ → ℝ := fun n => harmonicReplacement a R (w n)
  have hv : ∀ n, v n ∈ perronClass Ω φ := fun n => class_replacement (hw n) hR hsub
  refine ⟨v, hv, ?_, ?_, ?_⟩
  · exact fun n => (HarmonicReplacementPasting.harmonicReplacement_properties Ω (w n) a R
      (hw n).1 hR hsub).2.2.1
  · intro z hz i j hij
    exact HarmonicReplacementPasting.harmonicReplacement_monotone Ω (w i) (w j) a R
      (hw i).1 (hw j).1 hR hsub
      (fun t _ => successiveMax_mono u t hij) z hz
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le hct tendsto_const_nhds
    · intro n
      rw [← he n]
      exact (le_successiveMax u n a).trans
        (HarmonicReplacementPasting.le_harmonicReplacement (hw n).1 hR hsub a ha)
    · exact fun n => le_envelope (hb a ha) (hv n)

/-- Every increasing, disk-harmonic sequence in the class has a finite
harmonic limit, bounded above by the envelope at every point of the disk. -/
lemma class_sequence_limit {Ω : Set ℂ} {φ : ℂ → ℝ} {a : ℂ} {R : ℝ}
    (hR : 0 < R) (hsub : closedBall a R ⊆ Ω)
    (hb : ∀ z ∈ Ω, BddAbove ((fun u : ℂ → ℝ => u z) '' perronClass Ω φ))
    {v : ℕ → ℂ → ℝ} (hv : ∀ n, v n ∈ perronClass Ω φ)
    (hh : ∀ n, HarmonicOn (ball a R) (v n))
    (hm : ∀ z ∈ Ω, Monotone (fun n => v n z)) :
    ∃ V : ℂ → ℝ, HarmonicOn (ball a R) V ∧
      HarnackConvergence.ConvergesOnCompacts (ball a R) v V ∧
      (∀ z ∈ ball a R, V z ≤ perronEnvelope Ω φ z) := by
  have hdom : IsDomain (ball a R) :=
    ⟨⟨a, mem_ball_self hR⟩, isOpen_ball, (convex_ball a R).isPreconnected⟩
  have ha : a ∈ Ω := hsub (mem_closedBall_self hR.le)
  have hbd : BddAbove (range (fun n => v n a)) := by
    refine (hb a ha).mono ?_
    rintro _ ⟨n, rfl⟩
    exact ⟨v n, hv n, rfl⟩
  obtain ⟨V, hV, hc⟩ := HarnackConvergence.finite_limit_of_bounded hdom hh
    (fun z hz => hm z (hsub (ball_subset_closedBall hz))) (mem_ball_self hR) hbd
  refine ⟨V, hV, hc, fun z hz => ?_⟩
  exact le_of_tendsto (hc.tendsto_at hz) (Eventually.of_forall fun n =>
    le_envelope (hb z (hsub (ball_subset_closedBall hz))) (hv n))

/-- The second replacement sequence tests an arbitrary class member. Equality
at the center and the strong minimum principle identify its harmonic limit
with the first one throughout the disk. This is what proves harmonicity of
the full supremum rather than just an extremizing basepoint limit. -/
lemma envelope_harmonic_on_disk {Ω : Set ℂ} {φ : ℂ → ℝ} {a : ℂ} {R : ℝ}
    (hne : (perronClass Ω φ).Nonempty) (hR : 0 < R) (hsub : closedBall a R ⊆ Ω)
    (hb : ∀ z ∈ Ω, BddAbove ((fun u : ℂ → ℝ => u z) '' perronClass Ω φ)) :
    HarmonicOn (ball a R) (perronEnvelope Ω φ) := by
  have ha : a ∈ ball a R := mem_ball_self hR
  have hdom : IsDomain (ball a R) :=
    ⟨⟨a, ha⟩, isOpen_ball, (convex_ball a R).isPreconnected⟩
  obtain ⟨v, hv, hvh, hvm, hvt⟩ := extremizing_sequence hne hR hsub hb
  obtain ⟨V, hV, hcV, hVH⟩ := class_sequence_limit hR hsub hb hv hvh hvm
  have hVa : V a = perronEnvelope Ω φ a := tendsto_nhds_unique (hcV.tendsto_at ha) hvt
  have hbound : ∀ w ∈ perronClass Ω φ, ∀ z ∈ ball a R, w z ≤ V z := by
    intro w hw
    let q : ℕ → ℂ → ℝ := fun n => harmonicReplacement a R (fun z => max (v n z) (w z))
    have hmax (n : ℕ) := class_max (hv n) hw
    have hq : ∀ n, q n ∈ perronClass Ω φ := fun n => class_replacement (hmax n) hR hsub
    have hqh : ∀ n, HarmonicOn (ball a R) (q n) := fun n =>
      (HarmonicReplacementPasting.harmonicReplacement_properties Ω _ a R
        (hmax n).1 hR hsub).2.2.1
    have hqm : ∀ z ∈ Ω, Monotone (fun n => q n z) := by
      intro z hz i j hij
      exact HarmonicReplacementPasting.harmonicReplacement_monotone Ω _ _ a R
        (hmax i).1 (hmax j).1 hR hsub
        (fun t ht => max_le_max (hvm t ht hij) le_rfl) z hz
    have hvq (n : ℕ) (z : ℂ) (hz : z ∈ Ω) : v n z ≤ q n z :=
      (le_max_left _ _).trans
        (HarmonicReplacementPasting.le_harmonicReplacement (hmax n).1 hR hsub z hz)
    have hwq (n : ℕ) (z : ℂ) (hz : z ∈ Ω) : w z ≤ q n z :=
      (le_max_right _ _).trans
        (HarmonicReplacementPasting.le_harmonicReplacement (hmax n).1 hR hsub z hz)
    obtain ⟨W, hW, hcW, hWH⟩ := class_sequence_limit hR hsub hb hq hqh hqm
    have hVW : ∀ z ∈ ball a R, V z ≤ W z := by
      intro z hz
      exact le_of_tendsto_of_tendsto (hcV.tendsto_at hz) (hcW.tendsto_at hz)
        (Eventually.of_forall fun n => hvq n z (hsub (ball_subset_closedBall hz)))
    have hWa : W a = V a := le_antisymm ((hWH a ha).trans_eq hVa.symm) (hVW a ha)
    have hdiff := HarnackConvergence.harmonic_sub hW hV
    have heq := MeanValueStrongPrinciple.harmonic_minimum (ball a R)
      (fun z => W z - V z) hdom hdiff a ha (by
        intro z hz
        have := hVW z hz
        linarith [hWa])
    intro z hz
    have hwW : w z ≤ W z := ge_of_tendsto (hcW.tendsto_at hz)
      (Eventually.of_forall fun n => hwq n z (hsub (ball_subset_closedBall hz)))
    have he := heq z hz
    linarith
  apply HarmonicReplacementPasting.harmonicOn_congr hV
  intro z hz
  apply le_antisymm (hVH z hz)
  apply csSup_le (hne.image (fun u : ℂ → ℝ => u z))
  rintro _ ⟨w, hw, rfl⟩
  exact hbound w hw z hz

lemma envelope_harmonic {Ω : Set ℂ} {φ : ℂ → ℝ} (hΩ : IsOpen Ω)
    (hne : (perronClass Ω φ).Nonempty)
    (hb : ∀ z ∈ Ω, BddAbove ((fun u : ℂ → ℝ => u z) '' perronClass Ω φ)) :
    HarmonicOn Ω (perronEnvelope Ω φ) := by
  apply (HarmonicFoundation.harmonicOn_iff_harmonicOnNhd Ω _ hΩ).mpr
  intro a ha
  obtain ⟨r, hr, hs⟩ := Metric.isOpen_iff.mp hΩ a ha
  have hclosed : closedBall a (r / 2) ⊆ Ω :=
    (closedBall_subset_ball (by linarith)).trans hs
  have hh := envelope_harmonic_on_disk hne (half_pos hr) hclosed hb
  exact ((HarmonicFoundation.harmonicOn_iff_harmonicOnNhd _ _ isOpen_ball).mp hh)
    a (mem_ball_self (half_pos hr))

theorem perron_envelope :
    Specs.D12Complex.Ch14.PerronEnvelope.perron_envelope_type := by
  intro Ω φ hΩ hΩb hφ
  have hnefront : (frontier Ω).Nonempty := nonempty_frontier_iff.mpr ⟨hΩ.1, by
    intro he
    exact NormedSpace.unbounded_univ ℝ ℂ (he ▸ hΩb)⟩
  have hcompact : IsCompact (frontier Ω) :=
    hΩb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hbφ := hcompact.bddBelow_image hφ
  have haφ := hcompact.bddAbove_image hφ
  have hm : ∀ ξ ∈ frontier Ω, sInf (φ '' frontier Ω) ≤ φ ξ :=
    fun ξ hξ => csInf_le hbφ ⟨ξ, hξ, rfl⟩
  have hM : ∀ ξ ∈ frontier Ω, φ ξ ≤ sSup (φ '' frontier Ω) :=
    fun ξ hξ => le_csSup haφ ⟨ξ, hξ, rfl⟩
  have hconst := class_const hΩ.2.1 hm
  have hne : (perronClass Ω φ).Nonempty := ⟨_, hconst⟩
  have hb := fun z (hz : z ∈ Ω) => values_bddAbove hΩb hM hz
  refine ⟨hne, fun z hz => ⟨hne.image _, hb z hz⟩, fun z hz => ⟨?_, ?_⟩,
    envelope_harmonic hΩ.2.1 hne hb⟩
  · exact le_envelope (hb z hz) hconst
  · apply csSup_le (hne.image _)
    rintro _ ⟨u, hu, rfl⟩
    exact class_upper_bound hΩb hu hM z hz

end D12Complex.PerronEnvelope
