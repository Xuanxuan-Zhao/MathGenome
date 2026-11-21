import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch11.HolomorphicCompactness
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch11.HolomorphicLimits
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.UniformSpace.CompleteSeparated
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.Compactness.SigmaCompact

noncomputable section
open Set Metric Filter
open scoped Topology

namespace D12Complex.HolomorphicCompactness

/-- A common finite norm bound on each compact subset of the open set. -/
def LocallyBounded (Ω : Set ℂ) (𝓕 : Set (ℂ → ℂ)) : Prop :=
  ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
    ∃ M : ℝ, 0 ≤ M ∧ ∀ f ∈ 𝓕, ∀ z ∈ K, ‖f z‖ ≤ M

/-- Cauchy's estimate on a fixed compact disk gives a common Lipschitz bound
on a smaller disk, independently of the member of the family. -/
lemma locally_lipschitz (Ω : Set ℂ) (𝓕 : Set (ℂ → ℂ)) (hΩ : IsOpen Ω)
    (hhol : ∀ f ∈ 𝓕, HolomorphicOn Ω f) (hb : LocallyBounded Ω 𝓕)
    (a : ℂ) (ha : a ∈ Ω) :
    ∃ r : ℝ, 0 < r ∧ ball a r ⊆ Ω ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ f ∈ 𝓕, ∀ x ∈ ball a r, ∀ y ∈ ball a r,
        ‖f y - f x‖ ≤ C * ‖y - x‖ := by
  obtain ⟨R, hR, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hΩ.mem_nhds ha)
  obtain ⟨M, hM, hbM⟩ := hb (closedBall a R) (isCompact_closedBall a R) hsub
  have hr : 0 < R / 2 := half_pos hR
  have hsmall : ball a (R / 2) ⊆ Ω :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))).trans hsub
  let C := 4 * M / R
  refine ⟨R / 2, hr, hsmall, C, by dsimp [C]; positivity, ?_⟩
  intro f hf x hx y hy
  apply Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z hz => (hhol f hf).2 z (hsmall hz)) ?_ (convex_ball a (R / 2)) hx hy
  intro z hz
  have he := HolomorphicLimits.norm_iteratedDeriv_le_of_boundary_bound Ω f
    (hhol f hf) a (R / 2) R M hr.le (by linarith) hsub hM
    (fun w hw => hbM f hf w (sphere_subset_closedBall hw)) 1 z (ball_subset_closedBall hz)
  convert he using 1 <;> simp [C, iteratedDeriv_one]
  field_simp
  ring

lemma equicontinuousOn (Ω : Set ℂ) (𝓕 : Set (ℂ → ℂ)) (hΩ : IsOpen Ω)
    (hhol : ∀ f ∈ 𝓕, HolomorphicOn Ω f) (hb : LocallyBounded Ω 𝓕) :
    EquicontinuousOn (fun f : 𝓕 => (f : ℂ → ℂ)) Ω := by
  intro a ha
  have he : EquicontinuousAt (fun f : 𝓕 => (f : ℂ → ℂ)) a := by
    obtain ⟨r, hr, _, C, hC, hLip⟩ := locally_lipschitz Ω 𝓕 hΩ hhol hb a ha
    apply Metric.equicontinuousAt_of_continuity_modulus
      (fun z => C * ‖z - a‖) (by
        have hc : Continuous (fun z : ℂ => C * ‖z - a‖) := by fun_prop
        simpa using hc.continuousAt.tendsto (x := a))
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with z hz f
    simpa only [dist_eq_norm, norm_sub_rev] using
      hLip f f.property a (mem_ball_self hr) z hz
  exact he.equicontinuousWithinAt Ω

theorem equicontinuousOn_compact :
    Specs.D12Complex.Ch11.HolomorphicCompactness.equicontinuousOn_compact_type := by
  intro Ω 𝓕 hΩ hhol hb K hK hKΩ
  rw [uniformEquicontinuousOn_iff_uniformContinuousOn]
  exact hK.uniformContinuousOn_of_continuous
    (equicontinuousOn_iff_continuousOn.mp (equicontinuousOn Ω 𝓕 hΩ hhol hb) |>.mono hKΩ)

/-- Arzelà–Ascoli is applied to the compact-open space of continuous maps on
Ω itself. Its countably generated uniformity supplies a single subsequence;
convergence there is convergence on every compact subset simultaneously. -/
theorem subsequence_holomorphic_limit :
    Specs.D12Complex.Ch11.HolomorphicCompactness.subsequence_holomorphic_limit_type := by
  classical
  intro Ω 𝓕 hΩ hhol hb F hF
  have : LocallyCompactSpace Ω := hΩ.locallyCompactSpace
  let G : ℕ → C(Ω, ℂ) := fun n =>
    ⟨fun z => F n z, continuousOn_iff_continuous_domRestrict.mp
      (fun z hz => ((hhol (F n) (hF n)).2 z hz).continuousAt.continuousWithinAt)⟩
  have hG (n : ℕ) (z : Ω) : G n z = F n z := rfl
  have hGe : Equicontinuous (fun n (z : Ω) => G n z) := by
    intro z
    apply (equicontinuousAt_restrict_iff (fun n => F n) z).mpr
    exact (equicontinuousOn Ω 𝓕 hΩ hhol hb z z.property).comp (fun n => ⟨F n, hF n⟩)
  have hSe : Equicontinuous (fun g : range G => fun z : Ω => (g : C(Ω, ℂ)) z) := by
    simpa only [Equicontinuous, EquicontinuousAt, forall_subtype_range_iff] using hGe
  have : T2Space (UniformOnFun Ω ℂ {K : Set Ω | IsCompact K}) :=
    UniformOnFun.t2Space_of_covering (by
      apply eq_univ_iff_forall.mpr
      intro z
      exact mem_sUnion.mpr ⟨{z}, isCompact_singleton, mem_singleton z⟩)
  have hc : IsCompact (closure (range G)) := by
    apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (𝔖 := {K : Set Ω | IsCompact K}) (F := fun g : C(Ω, ℂ) => fun z => g z)
      (fun _ hK => hK)
      ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding
      (fun K _ => hSe.equicontinuousOn K)
    intro K hK z hz
    obtain ⟨M, hM, hbM⟩ := hb {z.val} isCompact_singleton (singleton_subset_iff.mpr z.property)
    refine ⟨closedBall 0 M, isCompact_closedBall _ _, ?_⟩
    rintro g ⟨n, rfl⟩
    rw [hG, mem_closedBall, dist_zero_right]
    exact hbM (F n) (hF n) z.val (mem_singleton _)
  obtain ⟨g, _, φ, hφ, hlim⟩ := hc.tendsto_subseq (fun n => subset_closure (mem_range_self n))
  let f : ℂ → ℂ := fun z => if hz : z ∈ Ω then g ⟨z, hz⟩ else 0
  have hf : TendstoLocallyUniformlyOn (fun n => F (φ n)) f atTop Ω := by
    rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
    have ht := ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hlim
    change TendstoLocallyUniformly (fun n z => G (φ n) z) g atTop at ht
    simp_rw [hG] at ht
    simpa [Function.comp_def, f] using ht
  exact ⟨φ, f, hφ, HolomorphicLimits.holomorphic_limit Ω (fun n => F (φ n)) f hΩ
    (fun n => hhol _ (hF _)) hf, hf⟩

end D12Complex.HolomorphicCompactness
