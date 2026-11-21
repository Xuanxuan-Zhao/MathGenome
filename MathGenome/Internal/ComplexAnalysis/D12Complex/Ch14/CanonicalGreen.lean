import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.CanonicalGreen
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch14.RegularGreen
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch14.CircularExhaustion
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch13.HarnackConvergence
import Mathlib.Topology.Order.MonotoneConvergence

noncomputable section
open Set Metric Filter InnerProductSpace
open scoped Topology

namespace D12Complex

def canonicalGreen : Set ℂ → ℂ → ℂ → ℝ :=
  Specs.D12Complex.Ch14.CanonicalGreen.canonicalGreen_value

end D12Complex

namespace D12Complex.CanonicalGreen

abbrev IsPositiveGreen : Specs.D12Complex.Ch14.CanonicalGreen.IsPositiveGreen_type :=
  _root_.D12Complex.IsPositiveGreen
abbrev IsLeastPositiveGreen : Specs.D12Complex.Ch14.CanonicalGreen.IsLeastPositiveGreen_type :=
  _root_.D12Complex.IsLeastPositiveGreen

/-- A normalized local pole gives a harmonic correction on the whole domain. -/
lemma harmonic_correction {Ω : Set ℂ} {a : ℂ} {g : ℂ → ℝ}
    (hΩ : IsOpen Ω) (hh : HarmonicOn (Ω \ {a}) g)
    (hp : HasNormalizedLogPole Ω a g) :
    ∃ H : ℂ → ℝ, HarmonicOn Ω H ∧
      EqOn H (fun z => g z + Real.log ‖z - a‖) (Ω \ {a}) := by
  classical
  obtain ⟨r, hr, hsub, h, hhh, heq⟩ := hp
  let H : ℂ → ℝ := fun z => if z = a then h a else g z + Real.log ‖z - a‖
  have Heq {z : ℂ} (hz : z ≠ a) : H z = g z + Real.log ‖z - a‖ := by simp [H, hz]
  refine ⟨H, ?_, fun z hz => Heq hz.2⟩
  apply (HarmonicFoundation.harmonicOn_iff_harmonicOnNhd _ _ hΩ).mpr
  intro z hz
  by_cases hza : z = a
  · subst z
    apply (harmonicAt_congr_nhds (f₁ := h) (f₂ := H) ?_).mp
      (((HarmonicFoundation.harmonicOn_iff_harmonicOnNhd _ _ isOpen_ball).mp hhh)
        a (mem_ball_self hr))
    filter_upwards [ball_mem_nhds a hr] with w hw
    by_cases hwa : w = a
    · simp [H, hwa]
    · exact (heq ⟨hw, hwa⟩).trans (Heq hwa).symm
  · have hsum := (((HarmonicFoundation.harmonicOn_iff_harmonicOnNhd _ _ hh.1).mp hh)
      z ⟨hz, hza⟩).add (HarmonicRemovable.harmonicAt_log_norm a z hza)
    apply (harmonicAt_congr_nhds (f₁ := fun w => g w + Real.log ‖w - a‖)
      (f₂ := H) ?_).mp hsum
    filter_upwards [isOpen_ne.mem_nhds hza] with w hw
    exact (Heq hw).symm

/-- A positive normalized competitor on a larger open set dominates a regular
Green function compactly contained there. No boundary data on the larger set
enter this comparison. -/
lemma regular_le_positive {Ω D : Set ℂ} {a : ℂ} {v : ℂ → ℝ}
    (hΩ : IsOpen Ω) (hD : IsDomain D) (hDb : Bornology.IsBounded D)
    (hreg : ∀ ξ ∈ frontier D, RegularBoundaryPoint D ξ)
    (ha : a ∈ D) (hsub : closure D ⊆ Ω) (hv : IsPositiveGreen Ω a v) :
    ∀ z ∈ D \ {a}, regularGreen D a z ≤ v z := by
  obtain ⟨H, hH, heq⟩ := harmonic_correction hΩ hv.1 hv.2.1
  have hHD : IsDirichletSolution D H H :=
    ⟨HarmonicRemovable.harmonicOn_mono hH hD.2.1 (subset_closure.trans hsub),
      hH.2.1.continuousOn.mono hsub, fun _ _ => rfl⟩
  have hc := RegularGreen.correction_solution hD hDb hreg ha
  have hcomp := RegularDirichlet.solution_comparison hDb hc hHD (by
    intro ξ hξ
    have hξa : ξ ≠ a := by rintro rfl; exact (hD.2.1.frontier_eq ▸ hξ).2 ha
    rw [heq ⟨hsub (frontier_subset_closure hξ), hξa⟩]
    linarith [hv.2.2 ξ ⟨hsub (frontier_subset_closure hξ), hξa⟩])
  intro z hz
  have h := hcomp z (subset_closure hz.1)
  rw [heq ⟨hsub (subset_closure hz.1), hz.2⟩] at h
  dsimp [regularGreen]
  linarith

/-- A constant harmonic correction from a pole-centered surrounding disk
bounds all corrections, including their values at the pole. -/
lemma correction_upper {D : Set ℂ} {a : ℂ} {R : ℝ}
    (hD : IsDomain D) (hDb : Bornology.IsBounded D)
    (hreg : ∀ ξ ∈ frontier D, RegularBoundaryPoint D ξ) (ha : a ∈ D)
    (hsub : closure D ⊆ ball a R) :
    ∀ z ∈ closure D, perronSolution D (fun ξ => Real.log ‖ξ - a‖) z ≤ Real.log R := by
  have hc := RegularGreen.correction_solution hD hDb hreg ha
  have hk : HarmonicOn D (fun _ : ℂ => Real.log R) :=
    (HarmonicFoundation.harmonicOn_iff_harmonicOnNhd _ _ hD.2.1).mpr
      (fun _ _ => harmonicAt_const _)
  exact RegularDirichlet.solution_comparison hDb hc
    ⟨hk, continuous_const.continuousOn, fun _ _ => rfl⟩ (by
      intro ξ hξ
      have hξa : ξ ≠ a := by rintro rfl; exact (hD.2.1.frontier_eq ▸ hξ).2 ha
      exact Real.log_le_log (norm_pos_iff.mpr (sub_ne_zero.mpr hξa))
        (by have ht := mem_ball.mp (hsub (frontier_subset_closure hξ));
            simpa only [dist_eq_norm] using ht.le))

theorem least_green_unique : Specs.D12Complex.Ch14.CanonicalGreen.least_green_unique_type := by
  intro Ω a g h hg hh z hz
  exact le_antisymm (hg.2 h hh.1 z hz) (hh.2 g hg.1 z hz)


lemma correction_mono {D E : Set ℂ} {a : ℂ}
    (hD : IsDomain D) (hDb : Bornology.IsBounded D)
    (hDr : ∀ ξ ∈ frontier D, RegularBoundaryPoint D ξ) (haD : a ∈ D)
    (hE : IsDomain E) (hEb : Bornology.IsBounded E)
    (hEr : ∀ ξ ∈ frontier E, RegularBoundaryPoint E ξ) (haE : a ∈ E)
    (hsub : closure D ⊆ E) :
    ∀ z ∈ closure D,
      perronSolution D (fun ξ => Real.log ‖ξ - a‖) z ≤
      perronSolution E (fun ξ => Real.log ‖ξ - a‖) z := by
  have hC := RegularGreen.correction_solution hE hEb hEr haE
  have hG := RegularGreen.regular_green E a hE hEb hEr haE
  refine RegularDirichlet.solution_comparison hDb
    (RegularGreen.correction_solution hD hDb hDr haD)
    ⟨HarmonicRemovable.harmonicOn_mono hC.1 hD.2.1 (subset_closure.trans hsub),
      hC.1.2.1.continuousOn.mono hsub, fun _ _ => rfl⟩ ?_
  intro ξ hξ
  have hξa : ξ ≠ a := by rintro rfl; exact (hD.2.1.frontier_eq ▸ hξ).2 haD
  have hp := hG.2.1 ξ ⟨hsub (frontier_subset_closure hξ), hξa⟩
  change 0 < perronSolution E (fun ξ => Real.log ‖ξ - a‖) ξ - Real.log ‖ξ - a‖ at hp
  linarith

open CircularExhaustion

lemma circular_mono {Ω : Set ℂ} {s : ℕ → Finset ℂ} {r : ℕ → ℂ → ℝ}
    (he : IsCircularExhaustion Ω s r) :
    Monotone (fun j => diskUnion (s j) (r j)) := by
  apply monotone_nat_of_le_succ
  intro j
  exact subset_closure.trans (he.1 j).2.2.2.2.1

theorem circular_exhaustion_containing_pole :
    Specs.D12Complex.Ch14.CanonicalGreen.circular_exhaustion_containing_pole_type := by
  intro Ω a hΩ ha
  obtain ⟨s, r, he⟩ := CircularExhaustion.circular_exhaustion Ω hΩ
  obtain ⟨N, hN⟩ := he.2.2 {a} isCompact_singleton (singleton_subset_iff.mpr ha)
  let s' := fun j => s (N + j)
  let r' := fun j => r (N + j)
  have hcof : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∃ j, K ⊆ diskUnion (s' j) (r' j) := by
    intro K hK hKΩ
    obtain ⟨j, hj⟩ := he.2.2 K hK hKΩ
    exact ⟨j, hj.trans (circular_mono he (by omega : j ≤ N + j))⟩
  refine ⟨s', r', ⟨?_, ?_, hcof⟩, ?_⟩
  · intro j
    simpa only [s', r', Nat.add_assoc] using he.1 (N + j)
  · apply Subset.antisymm
    · exact iUnion_subset fun j => subset_closure.trans (he.1 (N + j)).2.2.2.1
    · intro z hz
      obtain ⟨j, hj⟩ := hcof {z} isCompact_singleton (singleton_subset_iff.mpr hz)
      exact mem_iUnion.mpr ⟨j, hj (mem_singleton z)⟩
  · intro j
    exact circular_mono he (Nat.le_add_right N j) (hN (mem_singleton a))

/-- Analytic assembly for a nested, compactly contained regular exhaustion.
The corrections, unlike the singular Green functions, are harmonic at a. -/
lemma limit_of_regular_exhaustion (Ω : Set ℂ) (a : ℂ) (D : ℕ → Set ℂ)
    (hΩ : IsDomain Ω) (hΩb : Bornology.IsBounded Ω) (ha : a ∈ Ω)
    (hD : ∀ j, IsDomain (D j))
    (hDc : ∀ j, IsCompact (closure (D j)))
    (hDr : ∀ j, ∀ ξ ∈ frontier (D j), RegularBoundaryPoint (D j) ξ)
    (hDa : ∀ j, a ∈ D j) (hsub : ∀ j, closure (D j) ⊆ Ω)
    (hnest : ∀ j, closure (D j) ⊆ D (j + 1))
    (hcof : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω → ∃ j, K ⊆ D j) :
    ∃ g : ℂ → ℝ, IsLeastPositiveGreen Ω a g ∧
      (∀ z : ℂ, Monotone (fun j => regularGreen (D j) a z)) ∧
      HarnackConvergence.ConvergesOnCompacts (Ω \ {a})
        (fun j => regularGreen (D j) a) g := by
  classical
  let C : ℕ → ℂ → ℝ := fun j => perronSolution (D j) (fun ξ => Real.log ‖ξ - a‖)
  have hDb (j : ℕ) : Bornology.IsBounded (D j) :=
    (hDc j).isBounded.subset subset_closure
  have hsol (j : ℕ) : IsDirichletSolution (D j) (fun ξ => Real.log ‖ξ - a‖) (C j) :=
    RegularGreen.correction_solution (hD j) (hDb j) (hDr j) (hDa j)
  have hgreen (j : ℕ) := RegularGreen.regular_green (D j) a (hD j) (hDb j) (hDr j) (hDa j)
  have hmonoD : Monotone D := monotone_nat_of_le_succ
    (fun j => subset_closure.trans (hnest j))
  have hmono : ∀ z, Monotone (fun j => C j z) := by
    intro z
    apply monotone_nat_of_le_succ
    intro j
    by_cases hz : z ∈ D j
    · exact correction_mono (hD j) (hDb j) (hDr j) (hDa j)
        (hD (j + 1)) (hDb (j + 1)) (hDr (j + 1)) (hDa (j + 1))
        (hnest j) z (subset_closure hz)
    · have hCj : C j z = Real.log ‖z - a‖ := by
        simp [C, perronSolution, hz]
      rw [hCj]
      by_cases hz' : z ∈ D (j + 1)
      · have hza : z ≠ a := by rintro rfl; exact hz (hDa j)
        have hp := (hgreen (j + 1)).2.1 z ⟨hz', hza⟩
        change 0 < C (j + 1) z - Real.log ‖z - a‖ at hp
        linarith
      · simp [C, perronSolution, hz']
  obtain ⟨R, hR, hΩR⟩ := hΩb.subset_ball_lt 0 a
  have hupper (j : ℕ) (z : ℂ) (hz : z ∈ Ω) : C j z ≤ Real.log R := by
    by_cases hzD : z ∈ D j
    · exact correction_upper (hD j) (hDb j) (hDr j) (hDa j)
        ((hsub j).trans hΩR) z (subset_closure hzD)
    · have hza : z ≠ a := by rintro rfl; exact hzD (hDa j)
      have hc : C j z = Real.log ‖z - a‖ := by simp [C, perronSolution, hzD]
      rw [hc]
      exact Real.log_le_log (norm_pos_iff.mpr (sub_ne_zero.mpr hza))
        (by have ht := mem_ball.mp (hΩR hz);
            simpa only [dist_eq_norm] using ht.le)
  let H : ℂ → ℝ := fun z => ⨆ j, C j z
  have hb (z : ℂ) (hz : z ∈ Ω) : BddAbove (range (fun j => C j z)) :=
    ⟨Real.log R, by rintro _ ⟨j, rfl⟩; exact hupper j z hz⟩
  have ht (z : ℂ) (hz : z ∈ Ω) : Tendsto (fun j => C j z) atTop (𝓝 (H z)) :=
    tendsto_atTop_ciSup (hmono z) (hb z hz)
  have htail (N : ℕ) : HarnackConvergence.ConvergesOnCompacts (D N)
      (fun j => C (j + N)) H := by
    apply HarnackConvergence.compact_convergence_of_pointwise (hD N)
      (fun j => HarmonicRemovable.harmonicOn_mono (hsol (j + N)).1 (hD N).2.1
        (hmonoD (Nat.le_add_left N j)))
      (fun z _ i j hij => hmono z (Nat.add_le_add_right hij N)) (hDa N)
    intro z hz
    exact (ht z (hsub N (subset_closure hz))).comp (tendsto_add_atTop_nat N)
  have hHstage (N : ℕ) : HarmonicOn (D N) H :=
    HarnackConvergence.harmonic_limit (hD N).2.1
      (fun j => HarmonicRemovable.harmonicOn_mono (hsol (j + N)).1 (hD N).2.1
        (hmonoD (Nat.le_add_left N j))) (htail N)
  have hH : HarmonicOn Ω H := by
    apply (HarmonicFoundation.harmonicOn_iff_harmonicOnNhd _ _ hΩ.2.1).mpr
    intro z hz
    obtain ⟨N, hN⟩ := hcof {z} isCompact_singleton (singleton_subset_iff.mpr hz)
    exact ((HarmonicFoundation.harmonicOn_iff_harmonicOnNhd _ _ (hD N).2.1).mp
      (hHstage N)) z (hN (mem_singleton z))
  have hconv : HarnackConvergence.ConvergesOnCompacts Ω C H := by
    intro K hK hKΩ
    obtain ⟨N, hN⟩ := hcof K hK hKΩ
    have htc := htail N K hK hN
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    obtain ⟨J, hJ⟩ := eventually_atTop.mp (Metric.tendstoUniformlyOn_iff.mp htc ε hε)
    filter_upwards [eventually_ge_atTop (J + N)] with j hj
    have he : (j - N) + N = j := Nat.sub_add_cancel (by omega)
    simpa only [he] using hJ (j - N) (by omega)
  let g : ℂ → ℝ := fun z => H z - Real.log ‖z - a‖
  have hgp : IsPositiveGreen Ω a g := by
    refine ⟨HarmonicRemovable.harmonicOn_sub
      (HarmonicRemovable.harmonicOn_mono hH (hΩ.2.1.sdiff isClosed_singleton)
        (fun _ hz => hz.1)) (RegularGreen.harmonic_log_distance Ω a hΩ.2.1), ?_, ?_⟩
    · obtain ⟨ρ, hρ, hρΩ⟩ := Metric.isOpen_iff.mp hΩ.2.1 a ha
      exact ⟨ρ, hρ, hρΩ, H, HarmonicRemovable.harmonicOn_mono hH isOpen_ball hρΩ,
        fun z _ => by dsimp [g]; ring⟩
    · intro z hz
      obtain ⟨N, hN⟩ := hcof {z} isCompact_singleton (singleton_subset_iff.mpr hz.1)
      have hp := (hgreen N).2.1 z ⟨hN (mem_singleton z), hz.2⟩
      have hle : C N z ≤ H z := le_ciSup (hb z hz.1) N
      change 0 < C N z - Real.log ‖z - a‖ at hp
      dsimp [g]
      linarith
  have hleast : IsLeastPositiveGreen Ω a g := by
    refine ⟨hgp, ?_⟩
    intro v hv z hz
    have hev : ∀ᶠ j in atTop, C j z - Real.log ‖z - a‖ ≤ v z := by
      obtain ⟨N, hN⟩ := hcof {z} isCompact_singleton (singleton_subset_iff.mpr hz.1)
      filter_upwards [eventually_ge_atTop N] with j hj
      exact regular_le_positive hΩ.2.1 (hD j) (hDb j) (hDr j) (hDa j) (hsub j) hv
        z ⟨hmonoD hj (hN (mem_singleton z)), hz.2⟩
    exact le_of_tendsto ((ht z hz.1).sub_const _) hev
  refine ⟨g, hleast, fun z i j hij => sub_le_sub_right (hmono z hij) _, ?_⟩
  intro K hK hKΩ
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp
    (hconv K hK (fun z hz => (hKΩ hz).1)) ε hε] with j hj
  intro z hz
  simpa only [g, regularGreen, C, Real.dist_eq, sub_sub_sub_cancel_right] using hj z hz


lemma circular_limit (Ω : Set ℂ) (a : ℂ)
    (hΩ : IsDomain Ω) (hΩb : Bornology.IsBounded Ω) (ha : a ∈ Ω)
    (s : ℕ → Finset ℂ) (r : ℕ → ℂ → ℝ) (he : IsCircularExhaustion Ω s r)
    (hea : ∀ j, a ∈ diskUnion (s j) (r j)) :
    ∃ g : ℂ → ℝ, IsLeastPositiveGreen Ω a g ∧
      (∀ z : ℂ, Monotone (fun j => regularGreen (diskUnion (s j) (r j)) a z)) ∧
      HarnackConvergence.ConvergesOnCompacts (Ω \ {a})
        (fun j => regularGreen (diskUnion (s j) (r j)) a) g := by
  apply limit_of_regular_exhaustion Ω a (fun j => diskUnion (s j) (r j)) hΩ hΩb ha
    (fun j => (he.1 j).2.1) (fun j => (he.1 j).2.2.1)
    (fun j => (he.1 j).2.2.2.2.2.2.2.2) hea
    (fun j => (he.1 j).2.2.2.1) (fun j => (he.1 j).2.2.2.2.1) he.2.2

theorem canonical_green_exists :
    Specs.D12Complex.Ch14.CanonicalGreen.canonical_green_exists_type := by
  intro Ω a hΩ hΩb ha
  obtain ⟨s, r, he, hea⟩ := circular_exhaustion_containing_pole Ω a hΩ ha
  obtain ⟨g, hg, _⟩ := circular_limit Ω a hΩ hΩb ha s r he hea
  exact ⟨g, hg⟩

theorem canonical_green : Specs.D12Complex.Ch14.CanonicalGreen.canonical_green_type := by
  intro Ω a hΩ hΩb ha
  have hex := canonical_green_exists Ω a hΩ hΩb ha
  simpa only [Specs.D12Complex.Ch14.CanonicalGreen.canonicalGreen_value, dite_eq_left hex] using
    Classical.choose_spec hex

theorem exhaustion_limit : Specs.D12Complex.Ch14.CanonicalGreen.exhaustion_limit_type := by
  intro Ω a hΩ hΩb ha s r he hea
  obtain ⟨g, hg, hm, hc⟩ := circular_limit Ω a hΩ hΩb ha s r he hea
  have heq := least_green_unique Ω a g (canonicalGreen Ω a) hg
    (canonical_green Ω a hΩ hΩb ha)
  exact ⟨hm, fun K hK hKΩ => (hc K hK hKΩ).congr_right (fun z hz => heq (hKΩ hz))⟩

end D12Complex.CanonicalGreen
