import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch09.FtcSecond
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch05.Lagrange
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.FiniteChanges

/-!
Newton–Leibniz with an integrable derivative, K03.09.ftc_second.
Each real partition cell has an interior mean-value tag. At those tags the
sum telescopes exactly, while integrability controls every sufficiently fine
tagged sum. The complex proof applies the real theorem to the two components;
no common complex mean-value tag is asserted.
-/
namespace SingleVariableAnalysis.Riemann
open Set
open scoped BigOperators

/-- Interior mean-value tags give an exact telescoping sum on every partition. -/
theorem exists_meanValue_tagging (F g : ℝ → ℝ) {a b : ℝ}
    (hc : ContinuousOn F (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt F (g x) x) (P : Partition a b) :
    ∃ ξ : Tagging P, taggedSum P ξ g = F b - F a := by
  have hex (i : Fin P.n) : ∃ c ∈ Ioo (P.point i.castSucc) (P.point i.succ),
      F (P.point i.succ) - F (P.point i.castSucc) = g c * cellLength P i := by
    have hsub := cell_subset_interval P i
    have hint (x : ℝ) (hx : x ∈ Ioo (P.point i.castSucc) (P.point i.succ)) :
        x ∈ Ioo a b := by
      have hleft := hsub (left_mem_Icc.mpr (P.strictMono.monotone (Fin.castSucc_le_succ i)))
      have hright := hsub (right_mem_Icc.mpr (P.strictMono.monotone (Fin.castSucc_le_succ i)))
      exact ⟨hleft.1.trans_lt hx.1, hx.2.trans_le hright.2⟩
    obtain ⟨c, hci, he⟩ := SingleVariableAnalysis.lagrange_deriv F
      (P.point i.castSucc) (P.point i.succ)
      (P.strictMono (Fin.castSucc_lt_succ (i := i)))
      (hc.mono hsub) (fun x hx => (hd x (hint x hx)).differentiableAt)
    exact ⟨c, hci, by simpa only [(hd c (hint c hci)).deriv, cellLength, S.lengthValue] using he⟩
  choose c hc' he using hex
  let ξ : Tagging P := fun i => ⟨c i, (hc' i).1.le, (hc' i).2.le⟩
  refine ⟨ξ, ?_⟩
  calc
    taggedSum P ξ g = ∑ i : Fin P.n,
        (F (P.point i.succ) - F (P.point i.castSucc)) := by
      apply Finset.sum_congr rfl
      intro i _
      change cellLength P i * g (c i) = _
      rw [he i, mul_comm]
    _ = F b - F a := by
      simpa only [P.first, P.last] using sum_cell_differences (fun i => F (P.point i))

theorem real_ftc_second :
    Specs.SingleVariableAnalysis.Ch09.FtcSecond.realFtcSecond := by
  intro F g a b hab hc hd hg
  by_contra hne
  have hpos : 0 < ‖realIntegral g hg - (F b - F a)‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hlim := (real_tagged_equivalence g hab (RealIntegrable.bounded hg)
    (realIntegral g hg)).mp ⟨hg, rfl⟩
  obtain ⟨δ, hδ, hclose⟩ := hlim _ hpos
  obtain ⟨P, hP⟩ := exists_fine_partition hab δ hδ
  obtain ⟨ξ, he⟩ := exists_meanValue_tagging F g hc hd P
  have hlt := hclose P ξ hP
  change ‖taggedSum P ξ g - realIntegral g hg‖ < ‖realIntegral g hg - (F b - F a)‖ at hlt
  rw [he, norm_sub_rev] at hlt
  exact (lt_irrefl _ hlt)

theorem complex_ftc_second :
    Specs.SingleVariableAnalysis.Ch09.FtcSecond.complexFtcSecond := by
  intro F g a b hab hc hd hg
  have hdr (x : ℝ) (hx : x ∈ Ioo a b) :=
    (SingleVariableAnalysis.complex_hasDerivAt_iff_components F (g x) x).mp (hd x hx)
  have hr := real_ftc_second (fun x => (F x).re) (fun x => (g x).re) a b hab
    (Complex.continuous_re.comp_continuousOn hc) (fun x hx => (hdr x hx).1) hg.1
  have hi := real_ftc_second (fun x => (F x).im) (fun x => (g x).im) a b hab
    (Complex.continuous_im.comp_continuousOn hc) (fun x hx => (hdr x hx).2) hg.2
  apply Complex.ext
  · exact (complexIntegral_components g hg).1.trans (by simpa only [Complex.sub_re] using hr)
  · exact (complexIntegral_components g hg).2.trans (by simpa only [Complex.sub_im] using hi)

/-- Endpoint reassignment gives boundedness automatically; no endpoint limit
or derivative needs to exist. -/
theorem real_endpoint_extensions :
    Specs.SingleVariableAnalysis.Ch09.FtcSecond.realEndpointExtensions := by
  intro f g a b he hf
  obtain ⟨M, hM⟩ := BoundedOnInterval.abs_bound (RealIntegrable.bounded hf)
  have hb : BoundedOnInterval g a b := by
    apply boundedOnInterval_of_abs (M := max M (max |g a| |g b|))
    intro x hx
    by_cases ha : x = a
    · subst x
      exact (le_max_left _ _).trans (le_max_right _ _)
    by_cases hb : x = b
    · subst x
      exact (le_max_right _ _).trans (le_max_right _ _)
    have hi : x ∈ Ioo a b := ⟨lt_of_le_of_ne hx.1 (Ne.symm ha), lt_of_le_of_ne hx.2 hb⟩
    rw [← he x hi]
    exact (hM x hx).trans (le_max_left _ _)
  have hs : {x | x ∈ Icc a b ∧ f x ≠ g x}.Finite := by
    apply (Set.toFinite ({a, b} : Set ℝ)).subset
    intro x hx
    by_contra hn
    have ha : x ≠ a := by intro h; exact hn (by simp [h])
    have hb : x ≠ b := by intro h; exact hn (by simp [h])
    exact hx.2 (he x ⟨lt_of_le_of_ne hx.1.1 (Ne.symm ha), lt_of_le_of_ne hx.1.2 hb⟩)
  exact real_finite_changes f g (RealIntegrable.bounded hf) hb hs hf

theorem complex_endpoint_extensions :
    Specs.SingleVariableAnalysis.Ch09.FtcSecond.complexEndpointExtensions := by
  intro f g a b he hf
  obtain ⟨hr, hvr⟩ := real_endpoint_extensions
    (fun x => (f x).re) (fun x => (g x).re) a b
    (fun x hx => congrArg Complex.re (he x hx)) hf.1
  obtain ⟨hi, hvi⟩ := real_endpoint_extensions
    (fun x => (f x).im) (fun x => (g x).im) a b
    (fun x hx => congrArg Complex.im (he x hx)) hf.2
  refine ⟨⟨hr, hi⟩, ?_⟩
  apply Complex.ext
  · exact (complexIntegral_components g ⟨hr, hi⟩).1.trans
      (hvr.trans (complexIntegral_components f hf).1.symm)
  · exact (complexIntegral_components g ⟨hr, hi⟩).2.trans
      (hvi.trans (complexIntegral_components f hf).2.symm)

end SingleVariableAnalysis.Riemann
