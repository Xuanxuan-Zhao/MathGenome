import MathGenome.Internal.ODEDynamics.D13Unified.Ch01.SolutionConcepts
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch01.RestrictionPasting
import Mathlib.Analysis.Calculus.FDeriv.Extend

noncomputable section
open Set Filter
open scoped Topology

namespace D13Unified
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- If a point belongs to only one of two overlapping intervals, that interval
contains a relative neighborhood of the point in the union. -/
theorem interval_mem_nhdsWithin_union {A B : Set ℝ}
    (hA : OrdConnected A) (hB : OrdConnected B)
    (hab : (A ∩ B).Nonempty) {t : ℝ} (ht : t ∈ A) (htB : t ∉ B) :
    A ∈ 𝓝[A ∪ B] t := by
  obtain ⟨s, hsA, hsB⟩ := hab
  have hts : t ≠ s := by rintro rfl; exact htB hsB
  rcases lt_or_gt_of_ne hts with hts | hst
  · apply mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
    refine ⟨Iio s, Iio_mem_nhds hts, ?_⟩
    rintro r ⟨hrs, hr | hr⟩
    · exact hr
    · have htr : t ≤ r := by
        by_contra hn
        exact htB (hB.out hr hsB ⟨(lt_of_not_ge hn).le, hts.le⟩)
      exact hA.out ht hsA ⟨htr, hrs.le⟩
  · apply mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
    refine ⟨Ioi s, Ioi_mem_nhds hst, ?_⟩
    rintro r ⟨hsr, hr | hr⟩
    · exact hr
    · have hrt : r ≤ t := by
        by_contra hn
        exact htB (hB.out hsB hr ⟨hst.le, (lt_of_not_ge hn).le⟩)
      exact hA.out hsA ht ⟨hsr.le, hrt⟩

/-- A pointwise gluing rule for relative derivatives on overlapping intervals. -/
theorem hasDerivWithinAt_union_intervals {A B : Set ℝ}
    (hA : OrdConnected A) (hB : OrdConnected B)
    (hab : (A ∩ B).Nonempty) {z : ℝ → E} {v : E} {t : ℝ}
    (ht : t ∈ A ∪ B)
    (hdA : t ∈ A → HasDerivWithinAt z v A t)
    (hdB : t ∈ B → HasDerivWithinAt z v B t) :
    HasDerivWithinAt z v (A ∪ B) t := by
  by_cases htA : t ∈ A
  · by_cases htB : t ∈ B
    · exact (hdA htA).union (hdB htB)
    · exact (hdA htA).mono_of_mem_nhdsWithin
        (interval_mem_nhdsWithin_union hA hB hab htA htB)
  · have htB : t ∈ B := ht.resolve_left htA
    apply (hdB htB).mono_of_mem_nhdsWithin
    simpa only [union_comm] using
      interval_mem_nhdsWithin_union hB hA (by simpa only [inter_comm] using hab) htB htA

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The explicitly pasted representative agrees with both constituent curves. -/
theorem pasteCurves_eqOn {A B : Set ℝ} {x y : ℝ → E}
    (hxy : EqOn x y (A ∩ B)) :
    EqOn (pasteCurves A x y) x A ∧ EqOn (pasteCurves A x y) y B := by
  classical
  constructor
  · intro t ht
    simp [pasteCurves, ht]
  · intro t ht
    by_cases htA : t ∈ A
    · simpa [pasteCurves, htA] using hxy ⟨htA, ht⟩
    · simp [pasteCurves, htA]

/-- Restriction preserves the graph and all endpoint-aware differential data. -/
theorem solutionOn_restrict (F : ODE E) (I J : TimeInterval) (x : ℝ → E)
    (hJ : J.carrier ⊆ I.carrier) (hx : IsSolutionOn F I x) : IsSolutionOn F J x :=
  ⟨hx.1.mono hJ, fun t ht => hx.2.1 t (hJ ht),
    fun t ht => (hx.2.2 t (hJ ht)).mono hJ⟩

/-- Classical restriction retains C¹ regularity on every smaller open interval. -/
theorem classicalSolutionOn_restrict (F : ODE E) (I J : OpenTimeInterval) (x : ℝ → E)
    (hJ : J.carrier ⊆ I.carrier) (hx : IsClassicalSolutionOn F I x) :
    IsClassicalSolutionOn F J x :=
  ⟨hx.1.mono hJ, fun t ht => hx.2.1 t (hJ ht), fun t ht => hx.2.2 t (hJ ht)⟩

/-- Compatible solutions paste on their exact union, for every endpoint type. -/
theorem compatible_pasting (F : ODE E) (I J : TimeInterval) (x y : ℝ → E)
    (h : (I.carrier ∩ J.carrier).Nonempty)
    (hx : IsSolutionOn F I x) (hy : IsSolutionOn F J y)
    (hxy : EqOn x y (I.carrier ∩ J.carrier)) :
    let z := pasteCurves I.carrier x y
    IsSolutionOn F (I.union J h) z ∧ EqOn z x I.carrier ∧ EqOn z y J.carrier := by
  dsimp only
  obtain ⟨hzx, hzy⟩ := pasteCurves_eqOn hxy
  have hx' := (solutionOn_congr F I x _ hzx.symm).mp hx
  have hy' := (solutionOn_congr F J y _ hzy.symm).mp hy
  have hd : ∀ t ∈ (I.union J h).carrier,
      HasDerivWithinAt (pasteCurves I.carrier x y)
        (F.eval t (pasteCurves I.carrier x y t)) (I.union J h).carrier t := by
    intro t ht
    exact hasDerivWithinAt_union_intervals I.ordConnected J.ordConnected h ht
      (hx'.2.2 t) (hy'.2.2 t)
  refine ⟨⟨HasDerivWithinAt.continuousOn hd, ?_, hd⟩, hzx, hzy⟩
  intro t ht
  rcases ht with ht | ht
  · exact hx'.2.1 t ht
  · exact hy'.2.1 t ht

/-- The union of compatible classical solutions is C¹ on its open domain. -/
theorem classical_pasting (F : ODE E) (I J : OpenTimeInterval) (x y : ℝ → E)
    (h : (I.carrier ∩ J.carrier).Nonempty)
    (hx : IsClassicalSolutionOn F I x) (hy : IsClassicalSolutionOn F J y)
    (hxy : EqOn x y (I.carrier ∩ J.carrier)) :
    IsClassicalSolutionOn F
      ⟨I.toTimeInterval.union J.toTimeInterval h, I.isOpen.union J.isOpen⟩
      (pasteCurves I.carrier x y) := by
  apply (classical_iff_solutionOn _ _ _).mpr
  exact (compatible_pasting F I.toTimeInterval J.toTimeInterval x y h
    ((classical_iff_solutionOn F I x).mp hx)
    ((classical_iff_solutionOn F J y).mp hy) hxy).1

omit [NormedSpace ℝ E] in
/-- Continuity also glues on overlapping intervals even when their external
endpoints are not closed in the ambient line. -/
theorem continuousOn_union_intervals {A B : Set ℝ}
    (hA : OrdConnected A) (hB : OrdConnected B) (h : (A ∩ B).Nonempty)
    {z : ℝ → E} (hzA : ContinuousOn z A) (hzB : ContinuousOn z B) :
    ContinuousOn z (A ∪ B) := by
  intro t ht
  by_cases htA : t ∈ A
  · by_cases htB : t ∈ B
    · exact (hzA t htA).union (hzB t htB)
    · exact (hzA t htA).mono_of_mem_nhdsWithin
        (interval_mem_nhdsWithin_union hA hB h htA htB)
  · have htB := ht.resolve_left htA
    apply (hzB t htB).mono_of_mem_nhdsWithin
    simpa only [union_comm] using
      interval_mem_nhdsWithin_union hB hA (by simpa only [inter_comm] using h) htB htA

/-- A continuous derivative equation on a real interval extends across one
missing point, provided the curve is continuous there. Both sides may be
absent; finite outer endpoints and singleton intervals are allowed. -/
theorem hasDerivWithinAt_interval_of_ne {J : Set ℝ} (hJ : OrdConnected J)
    {x v : ℝ → E} {s : ℝ} (hs : s ∈ J) (hx : ContinuousOn x J)
    (hv : ContinuousOn v J)
    (hd : ∀ t ∈ J, t ≠ s → HasDerivWithinAt x (v t) J t) :
    HasDerivWithinAt x (v s) J s := by
  have hleft : HasDerivWithinAt x (v s) (J ∩ Iic s) s := by
    by_cases hside : ∃ a ∈ J, a < s
    · obtain ⟨a, ha, has⟩ := hside
      have hsub : Ioo a s ⊆ J := Ioo_subset_Icc_self.trans (hJ.out ha hs)
      have hlocal : ∀ t ∈ Ioo a s, J ∈ 𝓝 t := fun t ht =>
        mem_of_superset (Ioo_mem_nhds ht.1 ht.2) hsub
      have hd' : ∀ t ∈ Ioo a s, HasDerivAt x (v t) t := fun t ht =>
        (hd t (hsub ht) (ne_of_lt ht.2)).hasDerivAt (hlocal t ht)
      have hlim : Tendsto v (𝓝[<] s) (𝓝 (v s)) :=
        (hv s hs).mono_of_mem_nhdsWithin
          (mem_of_superset (Ioo_mem_nhdsLT has) hsub)
      have hderlim : Tendsto (deriv x) (𝓝[<] s) (𝓝 (v s)) := by
        apply hlim.congr'
        filter_upwards [Ioo_mem_nhdsLT has] with t ht
        exact (hd' t ht).deriv.symm
      exact (hasDerivWithinAt_Iic_of_tendsto_deriv
        (fun t ht => (hd' t ht).differentiableAt.differentiableWithinAt)
        ((hx s hs).mono hsub) (Ioo_mem_nhdsLT has) hderlim).mono inter_subset_right
    · change HasFDerivWithinAt x (ContinuousLinearMap.toSpanSingleton ℝ (v s)) _ s
      apply HasFDerivWithinAt.singleton.mono
      intro t ht
      apply mem_singleton_iff.mpr
      exact le_antisymm ht.2 (le_of_not_gt (fun hts => hside ⟨t, ht.1, hts⟩))
  have hright : HasDerivWithinAt x (v s) (J ∩ Ici s) s := by
    by_cases hside : ∃ b ∈ J, s < b
    · obtain ⟨b, hb, hsb⟩ := hside
      have hsub : Ioo s b ⊆ J := Ioo_subset_Icc_self.trans (hJ.out hs hb)
      have hlocal : ∀ t ∈ Ioo s b, J ∈ 𝓝 t := fun t ht =>
        mem_of_superset (Ioo_mem_nhds ht.1 ht.2) hsub
      have hd' : ∀ t ∈ Ioo s b, HasDerivAt x (v t) t := fun t ht =>
        (hd t (hsub ht) (ne_of_gt ht.1)).hasDerivAt (hlocal t ht)
      have hlim : Tendsto v (𝓝[>] s) (𝓝 (v s)) :=
        (hv s hs).mono_of_mem_nhdsWithin
          (mem_of_superset (Ioo_mem_nhdsGT hsb) hsub)
      have hderlim : Tendsto (deriv x) (𝓝[>] s) (𝓝 (v s)) := by
        apply hlim.congr'
        filter_upwards [Ioo_mem_nhdsGT hsb] with t ht
        exact (hd' t ht).deriv.symm
      exact (hasDerivWithinAt_Ici_of_tendsto_deriv
        (fun t ht => (hd' t ht).differentiableAt.differentiableWithinAt)
        ((hx s hs).mono hsub) (Ioo_mem_nhdsGT hsb) hderlim).mono inter_subset_right
    · change HasFDerivWithinAt x (ContinuousLinearMap.toSpanSingleton ℝ (v s)) _ s
      apply HasFDerivWithinAt.singleton.mono
      intro t ht
      apply mem_singleton_iff.mpr
      exact le_antisymm (le_of_not_gt (fun hst => hside ⟨t, ht.1, hst⟩)) ht.2
  have hcover : (J ∩ Iic s) ∪ (J ∩ Ici s) = J := by
    ext t
    simp only [mem_union, mem_inter_iff, mem_Iic, mem_Ici]
    exact ⟨fun h => h.elim And.left And.left,
      fun ht => (le_total t s).elim (fun h => Or.inl ⟨ht, h⟩) (fun h => Or.inr ⟨ht, h⟩)⟩
  simpa only [hcover] using hleft.union hright

/-- Pasting through a common endpoint proves the equation at the join from
continuity; no endpoint derivative is among the hypotheses. -/
theorem endpoint_pasting (F : ODE E) (L R : TimeInterval) (x y : ℝ → E)
    (s : ℝ) (ξ : E) (hsL : s ∈ L.carrier) (hsR : s ∈ R.carrier)
    (hL : L.carrier ⊆ Iic s) (hR : R.carrier ⊆ Ici s)
    (hx : ContinuousOn x L.carrier) (hy : ContinuousOn y R.carrier)
    (hxg : ∀ t ∈ L.carrier, (t, x t) ∈ F.domain)
    (hyg : ∀ t ∈ R.carrier, (t, y t) ∈ F.domain)
    (hxs : x s = ξ) (hys : y s = ξ)
    (hxd : ∀ t ∈ L.carrier, t < s →
      HasDerivWithinAt x (F.eval t (x t)) L.carrier t)
    (hyd : ∀ t ∈ R.carrier, s < t →
      HasDerivWithinAt y (F.eval t (y t)) R.carrier t) :
    let I := L.union R ⟨s, hsL, hsR⟩
    let z := pasteCurves L.carrier x y
    IsIVPOn F I z s ξ ∧
      EqOn z x L.carrier ∧ EqOn z y R.carrier ∧
      HasDerivWithinAt z (F.eval s ξ) I.carrier s ∧
      (s ∈ interior I.carrier → HasDerivAt z (F.eval s ξ) s) ∧
      (∀ hI : IsOpen I.carrier, IsClassicalSolutionOn F ⟨I, hI⟩ z) := by
  let I := L.union R ⟨s, hsL, hsR⟩
  let z := pasteCurves L.carrier x y
  change IsIVPOn F I z s ξ ∧ _
  have hxy : EqOn x y (L.carrier ∩ R.carrier) := by
    intro t ht
    have hts : t = s := le_antisymm (hL ht.1) (hR ht.2)
    simp only [hts, hxs, hys]
  obtain ⟨hzx, hzy⟩ := pasteCurves_eqOn hxy
  change EqOn z x L.carrier at hzx
  change EqOn z y R.carrier at hzy
  have hzs : z s = ξ := (hzx hsL).trans hxs
  have hs : s ∈ I.carrier := Or.inl hsL
  have hzc : ContinuousOn z I.carrier :=
    continuousOn_union_intervals L.ordConnected R.ordConnected ⟨s, hsL, hsR⟩
      (hx.congr hzx) (hy.congr hzy)
  have hzg : ∀ t ∈ I.carrier, (t, z t) ∈ F.domain := by
    intro t ht
    rcases ht with ht | ht
    · rw [hzx ht]; exact hxg t ht
    · rw [hzy ht]; exact hyg t ht
  have hzd : ∀ t ∈ I.carrier, t ≠ s →
      HasDerivWithinAt z (F.eval t (z t)) I.carrier t := by
    intro t ht hts
    apply hasDerivWithinAt_union_intervals L.ordConnected R.ordConnected
      ⟨s, hsL, hsR⟩ ht
    · intro htL
      have hd := (hxd t htL (lt_of_le_of_ne (hL htL) hts)).congr_of_mem hzx htL
      simpa only [hzx htL] using hd
    · intro htR
      have hd := (hyd t htR (lt_of_le_of_ne (hR htR) hts.symm)).congr_of_mem hzy htR
      simpa only [hzy htR] using hd
  have hv : ContinuousOn (fun t => F.eval t (z t)) I.carrier :=
    F.continuousOn_eval.comp (continuousOn_id.prodMk hzc) hzg
  have hds := hasDerivWithinAt_interval_of_ne I.ordConnected hs hzc hv hzd
  have hsol : IsSolutionOn F I z := by
    refine ⟨hzc, hzg, ?_⟩
    intro t ht
    by_cases hts : t = s
    · simpa only [hts] using hds
    · exact hzd t ht hts
  refine ⟨⟨hsol, hs, hzs⟩, hzx, hzy, ?_, ?_, ?_⟩
  · simpa only [hzs] using hds
  · intro hi
    simpa only [hzs] using hds.hasDerivAt (mem_interior_iff_mem_nhds.mp hi)
  · intro hI
    exact (classical_iff_solutionOn F ⟨I, hI⟩ z).mpr hsol

end D13Unified
