import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.RegularDirichlet
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch14.BarrierSqueeze
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch13.BoundaryMaximum

noncomputable section
open Set Metric Filter
open scoped Topology

namespace D12Complex

/-- A classical solution with the actual prescribed boundary values. -/
def IsDirichletSolution (Ω : Set ℂ) (φ u : ℂ → ℝ) : Prop :=
  HarmonicOn Ω u ∧ ContinuousOn u (closure Ω) ∧ EqOn u φ (frontier Ω)

/-- Perron's envelope on the domain, extended by its boundary datum. -/
def perronSolution (Ω : Set ℂ) (φ : ℂ → ℝ) (z : ℂ) : ℝ :=
  @ite ℝ (z ∈ Ω) (Classical.propDecidable _) (perronEnvelope Ω φ z) (φ z)

end D12Complex

namespace D12Complex.RegularDirichlet

/-- Joining all interior boundary limits to continuous boundary data gives
continuity also for approaches mixing interior and boundary points. -/
lemma continuousOn_extension {Ω : Set ℂ} {f φ : ℂ → ℝ}
    (hΩ : IsOpen Ω) (hf : ContinuousOn f Ω) (hφ : ContinuousOn φ (frontier Ω))
    (hlim : ∀ ξ ∈ frontier Ω, Tendsto f (𝓝[Ω] ξ) (𝓝 (φ ξ))) :
    ContinuousOn (fun z => @ite ℝ (z ∈ Ω) (Classical.propDecidable _) (f z) (φ z))
      (closure Ω) := by
  classical
  intro ξ hξ
  apply Metric.continuousWithinAt_iff.mpr
  intro ε hε
  by_cases hξΩ : ξ ∈ Ω
  · obtain ⟨δ, hδ, hd⟩ := Metric.continuousWithinAt_iff.mp (hf ξ hξΩ) ε hε
    obtain ⟨r, hr, hs⟩ := Metric.isOpen_iff.mp hΩ ξ hξΩ
    refine ⟨min δ r, lt_min hδ hr, fun z _ hz => ?_⟩
    have hzΩ : z ∈ Ω := hs (hz.trans_le (min_le_right _ _))
    simpa only [ite_eq_left hzΩ, ite_eq_left hξΩ] using hd hzΩ (hz.trans_le (min_le_left _ _))
  · have hξF : ξ ∈ frontier Ω := by rw [hΩ.frontier_eq]; exact ⟨hξ, hξΩ⟩
    obtain ⟨δ, hδ, hd⟩ := Metric.tendsto_nhdsWithin_nhds.mp (hlim ξ hξF) ε hε
    obtain ⟨r, hr, hs⟩ := Metric.continuousWithinAt_iff.mp (hφ ξ hξF) ε hε
    refine ⟨min δ r, lt_min hδ hr, fun z hz hdist => ?_⟩
    by_cases hzΩ : z ∈ Ω
    · simpa only [ite_eq_left hzΩ, ite_eq_right hξΩ] using hd hzΩ
        (hdist.trans_le (min_le_left _ _))
    · have hzF : z ∈ frontier Ω := by rw [hΩ.frontier_eq]; exact ⟨hz, hzΩ⟩
      simpa only [ite_eq_right hzΩ, ite_eq_right hξΩ] using hs hzF
        (hdist.trans_le (min_le_right _ _))

lemma perronSolution_eq_envelope {Ω : Set ℂ} {φ : ℂ → ℝ} {z : ℂ} (hz : z ∈ Ω) :
    perronSolution Ω φ z = perronEnvelope Ω φ z := by simp [perronSolution, hz]

lemma perronSolution_eq_boundary {Ω : Set ℂ} {φ : ℂ → ℝ} (hΩ : IsOpen Ω)
    {z : ℂ} (hz : z ∈ frontier Ω) : perronSolution Ω φ z = φ z := by
  have hn : z ∉ Ω := (hΩ.frontier_eq ▸ hz).2
  simp [perronSolution, hn]

/-- A continuous closure function bounded above on the boundary satisfies
the boundary-limsup hypothesis of the harmonic maximum theorem. -/
lemma boundaryLimsupLE_of_continuousOn {Ω : Set ℂ} {u : ℂ → ℝ} {M : ℝ}
    (hc : ContinuousOn u (closure Ω)) (hb : ∀ ξ ∈ frontier Ω, u ξ ≤ M) :
    BoundaryLimsupLE Ω u M := by
  intro ξ hξ ε hε
  obtain ⟨δ, hδ, hd⟩ := Metric.continuousWithinAt_iff.mp
    (hc ξ (frontier_subset_closure hξ)) ε hε
  refine ⟨δ, hδ, fun z hz hdist => ?_⟩
  have hh := hd (subset_closure hz) hdist
  have := (abs_lt.mp (show |u z - u ξ| < ε by simpa [Real.dist_eq] using hh)).2
  linarith [hb ξ hξ]

/-- Comparison is valid on the whole closure, with arbitrary boundary data. -/
lemma solution_comparison {Ω : Set ℂ} {φ ψ u v : ℂ → ℝ}
    (hΩb : Bornology.IsBounded Ω) (hu : IsDirichletSolution Ω φ u)
    (hv : IsDirichletSolution Ω ψ v) (hle : ∀ ξ ∈ frontier Ω, φ ξ ≤ ψ ξ) :
    ∀ z ∈ closure Ω, u z ≤ v z := by
  have hdiff := HarnackConvergence.harmonic_sub hu.1 hv.1
  have hb : BoundaryLimsupLE Ω (fun z => u z - v z) 0 :=
    boundaryLimsupLE_of_continuousOn (hu.2.1.sub hv.2.1) (by
      intro ξ hξ
      rw [hu.2.2 hξ, hv.2.2 hξ]
      exact sub_nonpos.mpr (hle ξ hξ))
  have hi := BoundaryMaximum.harmonic_boundary_maximum Ω _ 0 hΩb hdiff hb
  intro z hz
  by_cases hzΩ : z ∈ Ω
  · exact sub_nonpos.mp (hi z hzΩ)
  · have hzF : z ∈ frontier Ω := by rw [hu.1.1.frontier_eq]; exact ⟨hz, hzΩ⟩
    rw [hu.2.2 hzF, hv.2.2 hzF]
    exact hle z hzF

lemma solution_unique {Ω : Set ℂ} {φ u v : ℂ → ℝ}
    (hΩb : Bornology.IsBounded Ω) (hu : IsDirichletSolution Ω φ u)
    (hv : IsDirichletSolution Ω φ v) : EqOn u v (closure Ω) := by
  intro z hz
  exact le_antisymm (solution_comparison hΩb hu hv (fun _ _ => le_rfl) z hz)
    (solution_comparison hΩb hv hu (fun _ _ => le_rfl) z hz)

lemma perronSolution_isSolution {Ω : Set ℂ} {φ : ℂ → ℝ}
    (hΩ : IsDomain Ω) (hΩb : Bornology.IsBounded Ω)
    (hreg : ∀ ξ ∈ frontier Ω, RegularBoundaryPoint Ω ξ)
    (hφ : ContinuousOn φ (frontier Ω)) : IsDirichletSolution Ω φ (perronSolution Ω φ) := by
  have hH := (PerronEnvelope.perron_envelope Ω φ hΩ hΩb hφ).2.2.2
  refine ⟨HarmonicReplacementPasting.harmonicOn_congr hH (fun z hz =>
    (perronSolution_eq_envelope hz).symm), ?_, fun z hz => perronSolution_eq_boundary hΩ.2.1 hz⟩
  exact continuousOn_extension hΩ.2.1 hH.2.1.continuousOn hφ
    (fun ξ hξ => BarrierSqueeze.barrier_squeeze Ω φ ξ hΩ hΩb hφ (hreg ξ hξ))

theorem regular_dirichlet : Specs.D12Complex.Ch14.RegularDirichlet.regular_dirichlet_type := by
  intro Ω φ hΩ hΩb hreg hφ
  have hsol := perronSolution_isSolution hΩ hΩb hreg hφ
  refine ⟨hsol, ?_, fun u hu => solution_unique hΩb hu hsol⟩
  have hK : IsCompact (frontier Ω) :=
    hΩb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  intro z hz
  change sInf (φ '' frontier Ω) ≤ perronSolution Ω φ z ∧
    perronSolution Ω φ z ≤ sSup (φ '' frontier Ω)
  by_cases hzΩ : z ∈ Ω
  · rw [perronSolution_eq_envelope hzΩ]
    exact (PerronEnvelope.perron_envelope Ω φ hΩ hΩb hφ).2.2.1 z hzΩ
  · have hzF : z ∈ frontier Ω := by rw [hΩ.2.1.frontier_eq]; exact ⟨hz, hzΩ⟩
    rw [perronSolution_eq_boundary hΩ.2.1 hzF]
    exact ⟨csInf_le (hK.bddBelow_image hφ) ⟨z, hzF, rfl⟩,
      le_csSup (hK.bddAbove_image hφ) ⟨z, hzF, rfl⟩⟩

/-- Harmonicity is preserved by arbitrary real linear combinations. -/
lemma harmonic_linear {Ω : Set ℂ} {u v : ℂ → ℝ}
    (hu : HarmonicOn Ω u) (hv : HarmonicOn Ω v) (a b : ℝ) :
    HarmonicOn Ω (fun z => a * u z + b * v z) := by
  apply (HarmonicFoundation.harmonicOn_iff_harmonicOnNhd Ω _ hu.1).mpr
  have hu' := (HarmonicFoundation.harmonicOn_iff_harmonicOnNhd Ω _ hu.1).mp hu
  have hv' := (HarmonicFoundation.harmonicOn_iff_harmonicOnNhd Ω _ hv.1).mp hv
  change InnerProductSpace.HarmonicOnNhd (a • u + b • v) Ω
  exact (hu'.const_smul (c := a)).add (hv'.const_smul (c := b))

lemma solution_linear {Ω : Set ℂ} {φ ψ u v : ℂ → ℝ}
    (hu : IsDirichletSolution Ω φ u) (hv : IsDirichletSolution Ω ψ v) (a b : ℝ) :
    IsDirichletSolution Ω (fun z => a * φ z + b * ψ z)
      (fun z => a * u z + b * v z) := by
  refine ⟨harmonic_linear hu.1 hv.1 a b,
    (continuousOn_const.mul hu.2.1).add (continuousOn_const.mul hv.2.1), ?_⟩
  intro z hz
  change a * u z + b * v z = a * φ z + b * ψ z
  rw [hu.2.2 hz, hv.2.2 hz]

theorem perronSolution_linear :
    Specs.D12Complex.Ch14.RegularDirichlet.perronSolution_linear_type := by
  intro Ω φ ψ a b hΩ hΩb hreg hφ hψ
  have hu := perronSolution_isSolution hΩ hΩb hreg hφ
  have hv := perronSolution_isSolution hΩ hΩb hreg hψ
  have hw := perronSolution_isSolution (φ := fun z => a * φ z + b * ψ z) hΩ hΩb hreg
    ((continuousOn_const.mul hφ).add (continuousOn_const.mul hψ))
  exact solution_unique hΩb hw (solution_linear hu hv a b)

theorem perronEnvelope_linear :
    Specs.D12Complex.Ch14.RegularDirichlet.perronEnvelope_linear_type := by
  intro Ω φ ψ a b hΩ hΩb hreg hφ hψ z hz
  have hh := perronSolution_linear Ω φ ψ a b hΩ hΩb hreg hφ hψ (subset_closure hz)
  change perronSolution Ω (fun z => a * φ z + b * ψ z) z =
    a * perronSolution Ω φ z + b * perronSolution Ω ψ z at hh
  simpa only [perronSolution_eq_envelope hz] using hh

lemma solution_nonneg {Ω : Set ℂ} {φ u : ℂ → ℝ}
    (hΩb : Bornology.IsBounded Ω) (hu : IsDirichletSolution Ω φ u)
    (hφ : ∀ ξ ∈ frontier Ω, 0 ≤ φ ξ) : ∀ z ∈ closure Ω, 0 ≤ u z := by
  have hb : BoundaryLiminfGE Ω u 0 := by
    intro ξ hξ ε hε
    obtain ⟨δ, hδ, hd⟩ := Metric.continuousWithinAt_iff.mp
      (hu.2.1 ξ (frontier_subset_closure hξ)) ε hε
    refine ⟨δ, hδ, fun z hz hdist => ?_⟩
    have hh := hd (subset_closure hz) hdist
    have := (abs_lt.mp (show |u z - u ξ| < ε by simpa [Real.dist_eq] using hh)).1
    have hξpos : 0 ≤ u ξ := (hu.2.2 hξ).symm ▸ hφ ξ hξ
    linarith
  have hi := BoundaryMaximum.harmonic_boundary_minimum Ω u 0 hΩb hu.1 hb
  intro z hz
  by_cases hzΩ : z ∈ Ω
  · exact hi z hzΩ
  · have hzF : z ∈ frontier Ω := by rw [hu.1.1.frontier_eq]; exact ⟨hz, hzΩ⟩
    rw [hu.2.2 hzF]
    exact hφ z hzF

theorem perronSolution_nonneg :
    Specs.D12Complex.Ch14.RegularDirichlet.perronSolution_nonneg_type := by
  intro Ω φ hΩ hΩb hreg hφ hpos
  exact solution_nonneg hΩb (perronSolution_isSolution hΩ hΩb hreg hφ) hpos

theorem perronEnvelope_nonneg :
    Specs.D12Complex.Ch14.RegularDirichlet.perronEnvelope_nonneg_type := by
  intro Ω φ hΩ hΩb hreg hφ hpos z hz
  have hh : 0 ≤ perronSolution Ω φ z :=
    perronSolution_nonneg Ω φ hΩ hΩb hreg hφ hpos z (subset_closure hz)
  simpa only [perronSolution_eq_envelope hz] using hh

theorem perronSolution_mono :
    Specs.D12Complex.Ch14.RegularDirichlet.perronSolution_mono_type := by
  intro Ω φ ψ hΩ hΩb hreg hφ hψ hle
  exact solution_comparison hΩb (perronSolution_isSolution hΩ hΩb hreg hφ)
    (perronSolution_isSolution hΩ hΩb hreg hψ) hle

theorem perronEnvelope_mono :
    Specs.D12Complex.Ch14.RegularDirichlet.perronEnvelope_mono_type := by
  intro Ω φ ψ hΩ hΩb hreg hφ hψ hle z hz
  have hh : perronSolution Ω φ z ≤ perronSolution Ω ψ z :=
    perronSolution_mono Ω φ ψ hΩ hΩb hreg hφ hψ hle z (subset_closure hz)
  simpa only [perronSolution_eq_envelope hz] using hh

end D12Complex.RegularDirichlet
