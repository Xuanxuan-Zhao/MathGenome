import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch03.PC1MonotoneChainRule
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.PathsChains
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Tactic.NormNum

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace D12Complex.MonotoneChainRule

/-- A point between the extreme nodes, different from every node, lies
strictly inside one of the partition pieces. -/
theorem exists_open_piece {n : ℕ} (node : Fin (n + 1) → ℝ) {x : ℝ}
    (hx : x ∈ Icc (node 0) (node (Fin.last n)))
    (hne : x ∉ range node) :
    ∃ i : Fin n, x ∈ Ioo (node i.castSucc) (node i.succ) := by
  classical
  have hn : ∀ i, x ≠ node i := fun i h => hne ⟨i, h.symm⟩
  have hl : node 0 < x := lt_of_le_of_ne hx.1 (hn 0).symm
  have hr : x < node (Fin.last n) := lt_of_le_of_ne hx.2 (hn _)
  have hex : ∃ j, x < node j := ⟨Fin.last n, hr⟩
  have hz : Fin.find (fun j => x < node j) hex ≠ 0 := by
    intro h
    have hspec := Fin.find_spec hex
    rw [h] at hspec
    exact (not_lt_of_ge hl.le) hspec
  obtain ⟨i, hi⟩ := Fin.exists_succ_eq.mpr hz
  refine ⟨i, ?_, ?_⟩
  · have hmin := Fin.find_min hex (j := i.castSucc) (by rw [← hi]; simp)
    exact lt_of_le_of_ne (le_of_not_gt hmin) (hn _).symm
  · simpa only [← hi] using (Fin.find_spec hex)

/-- Finite C1 pieces give ordinary differentiability away from their nodes.
No derivative of the arbitrary total extension is asserted at an endpoint. -/
theorem differentiableAt_off_nodes {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → E} {n : ℕ} (node : Fin (n + 1) → ℝ)
    (hsmooth : ∀ i : Fin n, ContDiffOn ℝ 1 f (Icc (node i.castSucc) (node i.succ)))
    {x : ℝ} (hx : x ∈ Icc (node 0) (node (Fin.last n)))
    (hne : x ∉ range node) : DifferentiableAt ℝ f x := by
  obtain ⟨i, hi⟩ := exists_open_piece node hx hne
  exact ((hsmooth i).differentiableOn (by norm_num) x ⟨hi.1.le, hi.2.le⟩).differentiableAt
    (Icc_mem_nhds hi.1 hi.2)

/-- Except possibly at its infimum and supremum, a bounded monotone fiber
is locally constant. Its full inverse image need not be a null set. -/
theorem eventuallyEq_of_mem_fiber {φ : ℝ → ℝ} {c d v t : ℝ}
    (hmono : MonotoneOn φ (Icc c d))
    (ht : t ∈ Icc c d) (hv : φ t = v)
    (hl : t ≠ sInf {s | s ∈ Icc c d ∧ φ s = v})
    (hu : t ≠ sSup {s | s ∈ Icc c d ∧ φ s = v}) :
    φ =ᶠ[𝓝 t] (fun _ => v) := by
  let S : Set ℝ := {s | s ∈ Icc c d ∧ φ s = v}
  have htS : t ∈ S := ⟨ht, hv⟩
  have hbelow : BddBelow S := ⟨c, fun s hs => hs.1.1⟩
  have habove : BddAbove S := ⟨d, fun s hs => hs.1.2⟩
  have hinf : sInf S < t := lt_of_le_of_ne (csInf_le hbelow htS) hl.symm
  have hsup : t < sSup S := lt_of_le_of_ne (le_csSup habove htS) hu
  obtain ⟨l, hlS, hlt⟩ := (csInf_lt_iff hbelow ⟨t, htS⟩).mp hinf
  obtain ⟨u, huS, htu⟩ := (lt_csSup_iff habove ⟨t, htS⟩).mp hsup
  filter_upwards [Ioo_mem_nhds hlt htu] with s hs
  have hsI : s ∈ Icc c d := ⟨hlS.1.1.trans hs.1.le, hs.2.le.trans huS.1.2⟩
  apply le_antisymm
  · exact (hmono hsI huS.1 hs.2.le).trans_eq huS.2
  · exact hlS.2.symm.trans_le (hmono hlS.1 hsI hs.1.le)

end D12Complex.MonotoneChainRule

namespace D12Complex.PiecewiseC1Path

/-- The chain identity for nondecreasing piecewise C1 parameter maps.
Plateaus over corners are handled by local constancy, rather than by
discarding the whole inverse image of the corner. -/
theorem ae_deriv_monotone_comp (γ η : PiecewiseC1Path) (φ : ℝ → ℝ)
    (_hcont : ContinuousOn φ (Icc η.path.a η.path.b))
    (hmono : MonotoneOn φ (Icc η.path.a η.path.b))
    (hmaps : MapsTo φ (Icc η.path.a η.path.b) (Icc γ.path.a γ.path.b))
    (_hsurj : SurjOn φ (Icc η.path.a η.path.b) (Icc γ.path.a γ.path.b))
    (n : ℕ) (node : Fin (n + 1) → ℝ) (_hstrict : StrictMono node)
    (hfirst : node 0 = η.path.a) (hlast : node (Fin.last n) = η.path.b)
    (hsmooth : ∀ i : Fin n, ContDiffOn ℝ 1 φ (Icc (node i.castSucc) (node i.succ)))
    (hη : ∀ t ∈ Icc η.path.a η.path.b, η t = γ (φ t)) :
    ∀ᵐ t ∂(volume.restrict (Icc η.path.a η.path.b)),
      deriv η t = deriv φ t • deriv γ (φ t) := by
  classical
  let P := γ.partition
  let lower : Fin (P.count + 1) → ℝ :=
    fun i => sInf {s | s ∈ Icc η.path.a η.path.b ∧ φ s = P.node i}
  let upper : Fin (P.count + 1) → ℝ :=
    fun i => sSup {s | s ∈ Icc η.path.a η.path.b ∧ φ s = P.node i}
  -- This is a finite exceptional set, even when some corner fibers
  -- are intervals of positive length or the source interval is a singleton.
  have hsource := (finite_range node).countable.ae_notMem
    (volume.restrict (Icc η.path.a η.path.b))
  have hlower := (finite_range lower).countable.ae_notMem
    (volume.restrict (Icc η.path.a η.path.b))
  have hupper := (finite_range upper).countable.ae_notMem
    (volume.restrict (Icc η.path.a η.path.b))
  filter_upwards [ae_restrict_mem measurableSet_Icc, hsource, hlower, hupper]
    with t ht htn htl htu
  have hleft : η.path.a < t := by
    refine lt_of_le_of_ne ht.1 ?_
    intro heq
    exact htn ⟨0, hfirst.trans heq⟩
  have hright : t < η.path.b := by
    refine lt_of_le_of_ne ht.2 ?_
    intro heq
    exact htn ⟨Fin.last n, hlast.trans heq.symm⟩
  have hlocal : (η : ℝ → ℂ) =ᶠ[𝓝 t] (γ ∘ φ) := by
    filter_upwards [Icc_mem_nhds hleft hright] with s hs
    exact hη s hs
  by_cases hcorner : φ t ∈ range P.node
  · obtain ⟨i, hi⟩ := hcorner
    have hφconst : φ =ᶠ[𝓝 t] (fun _ => P.node i) :=
      MonotoneChainRule.eventuallyEq_of_mem_fiber hmono ht hi.symm
        (fun h => htl ⟨i, h.symm⟩) (fun h => htu ⟨i, h.symm⟩)
    have hφzero : deriv φ t = 0 := by
      rw [hφconst.deriv_eq]
      simp
    have hηconst : (η : ℝ → ℂ) =ᶠ[𝓝 t] (fun _ => γ (P.node i)) := by
      filter_upwards [hlocal, hφconst] with s hs hφs
      simpa only [Function.comp_apply, hφs] using hs
    rw [hηconst.deriv_eq, hφzero]
    simp
  · have hφdiff : DifferentiableAt ℝ φ t :=
      MonotoneChainRule.differentiableAt_off_nodes node hsmooth
        (by simpa only [hfirst, hlast] using ht) htn
    have hγdiff : DifferentiableAt ℝ (γ : ℝ → ℂ) (φ t) :=
      MonotoneChainRule.differentiableAt_off_nodes P.node P.smooth
        (by simpa only [P.first, P.last] using hmaps ht) hcorner
    exact hlocal.deriv_eq.trans (deriv.scomp t hγdiff hφdiff)

end D12Complex.PiecewiseC1Path
