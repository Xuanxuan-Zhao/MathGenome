import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.CircularAngularCuts
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch14.CircularCornerRounding
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch14.FiniteCircularArcs
import Mathlib.Data.Finset.Sort
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real

/-! Angular subdivisions for literal circular surgery.
The final theorem `circular_angular_cuts` proves the complete independent type,
including actual regular ray changes and the uniform parameter-length bound. -/
noncomputable section
open Set Metric Filter Complex MeasureTheory
open scoped Topology ContDiff

namespace D12Complex.CircularAngularCuts
open CircularExhaustion CircularCornerRounding

/-- Restrict actual charts to avoid any prescribed finite set away from their
vertices. Forward and inverse functions are unchanged by this restriction. -/
theorem exists_uniform_charts_avoiding :
    Specs.D12Complex.Ch14.CircularAngularCuts.exists_uniform_charts_avoiding_type := by
  classical
  intro U J K hgeom
  obtain ⟨θ, e, R, L, hR, hL, hθ, hside, hc, hp, hdisj, hbound⟩ :=
    exists_uniform_corner_charts hgeom
  let A : ℂ → Set ℂ := fun p => (↑(K.erase p) : Set ℂ)ᶜ
  have hA : ∀ p, IsOpen (A p) := fun p => (K.erase p).finite_toSet.isClosed.isOpen_compl
  let E : ℂ → OpenPartialHomeomorph ℂ ℂ := fun p => (e p).restrOpen (A p) (hA p)
  have hpA : ∀ p, p ∈ A p := by simp [A]
  have hpE : ∀ p ∈ J, p ∈ (E p).source ∧ E p p = 0 := by
    intro p hpJ
    exact ⟨⟨(hp p hpJ).1, hpA p⟩, (hp p hpJ).2⟩
  have hscale : ∀ p : ℂ, ∃ r : ℝ, 0 < r ∧ (p ∈ J → closedBall (0 : ℂ) r ⊆ (E p).target) := by
    intro p
    by_cases hpJ : p ∈ J
    · have hz : (0 : ℂ) ∈ (E p).target := by
        rw [← (hpE p hpJ).2]
        exact (E p).map_source (hpE p hpJ).1
      obtain ⟨s, hs, hst⟩ := Metric.mem_nhds_iff.mp ((E p).open_target.mem_nhds hz)
      exact ⟨s / 2, by positivity, fun _ =>
        (closedBall_subset_ball (by linarith)).trans hst⟩
    · exact ⟨1, by norm_num, fun h => (hpJ h).elim⟩
  choose r hr hrt using hscale
  obtain ⟨s, hs, hsr⟩ := finite_positive_lower_bound J r (fun p _ => hr p)
  let R' := min R s
  have hR' : 0 < R' := lt_min hR hs
  let c : UniformCharts U J := {
    angle := θ
    chart := E
    R := R'
    L := L
    radius_pos := hR'
    lipschitz_pos := hL
    angle_bounds := hθ
    side := fun p hpJ z hz => hside p hpJ hz.1
    smooth := fun p hpJ => ⟨(hc p hpJ).1.mono inter_subset_left,
      (hc p hpJ).2.mono inter_subset_left⟩
    normalized := hpE
    disjoint := fun p hpJ q hqJ hpq =>
      (hdisj p hpJ q hqJ hpq).mono inter_subset_left inter_subset_left
    target_bound := fun p hpJ => ⟨
      (closedBall_subset_closedBall ((min_le_right R s).trans (hsr p hpJ))).trans (hrt p hpJ),
      (hbound p hpJ).2.mono (closedBall_subset_closedBall (min_le_left R s))⟩ }
  refine ⟨c, ?_⟩
  intro p hpJ q hqK hqp hqE
  exact hqE.2 (by simpa only [Finset.mem_coe, Finset.mem_erase] using And.intro hqp hqK)

/-- The domain used by the cut construction is already the literal surgery
from the accepted finite-chart theorem, with its actual defining functions. -/
theorem literal_surgery_regular :
    Specs.D12Complex.Ch14.CircularAngularCuts.literal_surgery_regular_type := by
  intro U J hgeom c ε hε hεR
  have htip : ∀ p ∈ J, sectorTip ε (c.angle p) ⊆ (c.chart p).target := by
    intro p hpJ
    exact (sectorTip_subset_closedBall hε).trans
      ((closedBall_subset_closedBall hεR.le).trans (c.target_bound p hpJ).1)
  exact (finite_chart_surgery hgeom c.chart c.angle hε c.angle_bounds c.side c.smooth
    c.normalized c.disjoint htip).2



/-- A finite set in a closed nondegenerate real interval, containing its endpoints,
can be enumerated in increasing order. -/
theorem finite_nodes_of_finset {a b : ℝ} (hab : a < b)
    (S : Finset ℝ) (ha : a ∈ S) (hb : b ∈ S)
    (hS : ∀ x ∈ S, x ∈ Icc a b) :
    ∃ (k : ℕ) (_ : 0 < k) (node : Fin (k + 1) → ℝ),
      StrictMono node ∧ node 0 = a ∧ node (Fin.last k) = b ∧
      range node = (S : Set ℝ) ∧
      ∀ j : Fin k, ∀ t ∈ Ioo (node j.castSucc) (node j.succ), t ∉ S := by
  classical
  have hcard : 2 ≤ S.card := by
    exact Finset.one_lt_card.mpr ⟨a, ha, b, hb, hab.ne⟩
  let k := S.card - 1
  have hk : 0 < k := by dsimp [k]; omega
  have hsk : S.card = k + 1 := by dsimp [k]; omega
  let e : Fin (k + 1) ↪o ℝ := S.orderEmbOfFin hsk
  have heS : ∀ j, e j ∈ S := fun j => S.orderEmbOfFin_mem hsk j
  have heR : range e = (S : Set ℝ) := S.range_orderEmbOfFin hsk
  have hzero : e 0 = a := by
    apply le_antisymm
    · obtain ⟨q, hq⟩ := heR.symm.subset ha
      rw [← hq]
      exact e.monotone (Fin.zero_le _)
    · exact (hS _ (heS _)).1
  have hlast : e (Fin.last k) = b := by
    apply le_antisymm
    · exact (hS _ (heS _)).2
    · obtain ⟨q, hq⟩ := heR.symm.subset hb
      rw [← hq]
      exact e.monotone (Fin.le_last _)
  refine ⟨k, hk, e, e.strictMono, hzero, hlast, heR, ?_⟩
  intro j t ht hmem
  obtain ⟨q, hq⟩ := heR.symm.subset hmem
  rw [← hq] at ht
  have h1 : j.castSucc < q := e.lt_iff_lt.mp ht.1
  have h2 : q < j.succ := e.lt_iff_lt.mp ht.2
  have h1' : j.val < q.val := h1
  have h2' : q.val < j.val + 1 := h2
  omega

/-- Consecutive closed intervals of a monotone finite node sequence cover exactly
its original closed interval. -/
theorem iUnion_node_intervals {k : ℕ} (hk : 0 < k)
    (node : Fin (k + 1) → ℝ) (hmono : Monotone node) :
    (⋃ j : Fin k, Icc (node j.castSucc) (node j.succ)) =
      Icc (node 0) (node (Fin.last k)) := by
  classical
  apply Subset.antisymm
  · intro t ht
    rcases mem_iUnion.mp ht with ⟨j, ht⟩
    exact ⟨(hmono (Fin.zero_le _)).trans ht.1,
      ht.2.trans (hmono (Fin.le_last _))⟩
  · intro t ht
    let S : Finset (Fin (k + 1)) := Finset.univ.filter (fun q => node q ≤ t)
    have hzero : (0 : Fin (k + 1)) ∈ S := by simp [S, ht.1]
    have hS : S.Nonempty := ⟨0, hzero⟩
    let q := S.max' hS
    have hqt : node q ≤ t := (Finset.mem_filter.mp (S.max'_mem hS)).2
    by_cases hqlast : q = Fin.last k
    · have hteq : t = node (Fin.last k) :=
        le_antisymm ht.2 (by simpa [hqlast] using hqt)
      let j : Fin k := ⟨k - 1, by omega⟩
      have hjsucc : j.succ = Fin.last k := by apply Fin.ext; dsimp [j]; omega
      refine mem_iUnion.mpr ⟨j, ?_⟩
      rw [hteq, hjsucc]
      exact ⟨hmono (Fin.le_last _), le_rfl⟩
    · have hqk : q.val < k := by
        have hqle := q.isLt
        have hqne : q.val ≠ k := by
          intro h; apply hqlast; apply Fin.ext; exact h
        omega
      let j : Fin k := ⟨q.val, hqk⟩
      have hjcast : j.castSucc = q := by apply Fin.ext; rfl
      have hnext : t ≤ node j.succ := by
        by_contra h
        have hmem : j.succ ∈ S := by
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
          exact (lt_of_not_ge h).le
        have hle := S.le_max' j.succ hmem
        have hv : j.val + 1 ≤ q.val := hle
        dsimp [j] at hv
        omega
      exact mem_iUnion.mpr ⟨j, by simpa [hjcast] using And.intro hqt hnext⟩

/-- Only injectivity in the open interval is needed; both endpoint images may coincide. -/
theorem exists_finite_marked_nodes {α : Type*} {f : ℝ → α} {a b : ℝ}
    (hab : a < b) (hinj : InjOn f (Ioo a b))
    (K : Set α) (hK : K.Finite) :
    ∃ (k : ℕ) (_ : 0 < k) (node : Fin (k + 1) → ℝ),
      StrictMono node ∧ node 0 = a ∧ node (Fin.last k) = b ∧
      (∀ t ∈ Icc a b, f t ∈ K → t ∈ range node) ∧
      ∀ j : Fin k, ∀ t ∈ Ioo (node j.castSucc) (node j.succ), f t ∉ K := by
  classical
  let M : Set ℝ := {t | t ∈ Ioo a b ∧ f t ∈ K}
  have hM : M.Finite := hK.of_injOn (f := f) (fun _ ht => ht.2)
    (hinj.mono fun _ ht => ht.1)
  let S := insert a (insert b hM.toFinset)
  have ha : a ∈ S := by simp [S]
  have hb : b ∈ S := by simp [S]
  have hS : ∀ x ∈ S, x ∈ Icc a b := by
    intro x hx
    simp only [S, Finset.mem_insert, Set.Finite.mem_toFinset] at hx
    rcases hx with rfl | rfl | hx
    · exact ⟨le_rfl, hab.le⟩
    · exact ⟨hab.le, le_rfl⟩
    · exact ⟨hx.1.1.le, hx.1.2.le⟩
  obtain ⟨k, hk, node, hmono, hfirst, hlast, hrange, havoid⟩ :=
    finite_nodes_of_finset hab S ha hb hS
  refine ⟨k, hk, node, hmono, hfirst, hlast, ?_, ?_⟩
  · intro t ht hmark
    rw [hrange]
    by_cases hta : t = a
    · simpa [hta] using ha
    by_cases htb : t = b
    · simpa [htb] using hb
    have htM : t ∈ M := ⟨⟨lt_of_le_of_ne ht.1 (Ne.symm hta),
      lt_of_le_of_ne ht.2 htb⟩, hmark⟩
    change t ∈ S
    simp only [S, Finset.mem_insert, Set.Finite.mem_toFinset]
    exact Or.inr (Or.inr htM)
  · intro j t ht hmark
    apply havoid j t ht
    have hleft := hS _ (show node j.castSucc ∈ S from
      hrange.subset (mem_range_self _))
    have hright := hS _ (show node j.succ ∈ S from
      hrange.subset (mem_range_self _))
    have htM : t ∈ M := ⟨⟨lt_of_le_of_lt hleft.1 ht.1,
      lt_of_lt_of_le ht.2 hright.2⟩, hmark⟩
    simp only [S, Finset.mem_insert, Set.Finite.mem_toFinset]
    exact Or.inr (Or.inr htM)



lemma nonzero_deriv_neighborhood {φ : ℝ → ℝ} {a b : ℝ} {S : Set ℝ}
    (hS : IsOpen S) (hsub : Icc a b ⊆ S) (hφ : ContDiffOn ℝ 1 φ S)
    (hne : ∀ t ∈ Icc a b, deriv φ t ≠ 0) :
    ∃ N : Set ℝ, IsOpen N ∧ Icc a b ⊆ N ∧ ContDiffOn ℝ 1 φ N ∧
      ∀ t ∈ N, deriv φ t ≠ 0 := by
  let N := S ∩ (deriv φ) ⁻¹' ({0}ᶜ : Set ℝ)
  have hN : IsOpen N := (hφ.continuousOn_deriv_of_isOpen hS (by norm_num)).isOpen_inter_preimage hS
    (isClosed_singleton.isOpen_compl)
  exact ⟨N, hN, fun t ht => ⟨hsub ht, hne t ht⟩, hφ.mono inter_subset_left,
    fun t ht => ht.2⟩

lemma strict_mono_or_anti_of_deriv_ne_zero {φ : ℝ → ℝ} {a b : ℝ} {S : Set ℝ}
    (hab : a ≤ b) (hS : IsOpen S) (hsub : Icc a b ⊆ S) (hφ : ContDiffOn ℝ 1 φ S)
    (hne : ∀ t ∈ Icc a b, deriv φ t ≠ 0) :
    StrictMonoOn φ (Icc a b) ∨ StrictAntiOn φ (Icc a b) := by
  have hC := (hφ.continuousOn_deriv_of_isOpen hS (by norm_num)).mono hsub
  have hc := hφ.continuousOn.mono hsub
  have ha : a ∈ Icc a b := left_mem_Icc.mpr hab
  rcases lt_or_gt_of_ne (hne a ha) with hneg | hpos
  · right
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _) hc
    intro x hx
    have hx' := interior_subset hx
    by_contra! hnonneg
    obtain ⟨y, hy, heq⟩ := isPreconnected_Icc.intermediate_value₂ ha hx' hC
      continuousOn_const hneg.le hnonneg
    exact hne y hy heq
  · left
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hc
    intro x hx
    have hx' := interior_subset hx
    by_contra! hnonpos
    obtain ⟨y, hy, heq⟩ := isPreconnected_Icc.intermediate_value₂ hx' ha hC
      continuousOn_const hnonpos hpos.le
    exact hne y hy heq

lemma derivative_nonzero_of_reparametrization {γ : ℝ → ℂ} {g : ℂ → ℂ}
    {φ : ℝ → ℝ} {a b ε : ℝ} {ξ : ℂ} (hab : a < b)
    (hφ : ∀ t ∈ Icc a b, DifferentiableAt ℝ φ t)
    (hg : ∀ t ∈ Icc a b, DifferentiableAt ℝ g ((ε * φ t) • ξ))
    (hγ : ∀ t ∈ Icc a b, DifferentiableAt ℝ γ t)
    (hγne : ∀ t ∈ Icc a b, deriv γ t ≠ 0)
    (heq : ∀ t ∈ Icc a b, γ t = g ((ε * φ t) • ξ)) :
    ∀ t ∈ Icc a b, deriv φ t ≠ 0 := by
  intro t ht hz
  have hdscalar : HasDerivAt (fun s => (ε * φ s) • ξ) (0 : ℂ) t := by
    simpa [hz] using ((hφ t ht).hasDerivAt.const_mul ε).smul_const ξ
  have hdcomp : HasDerivAt (fun s => g ((ε * φ s) • ξ)) (0 : ℂ) t := by
    simpa only [Function.comp_def, map_zero] using! (hg t ht).hasFDerivAt.comp_hasDerivAt t hdscalar
  have hdwithin : HasDerivWithinAt γ (0 : ℂ) (Icc a b) t :=
    hdcomp.hasDerivWithinAt.congr_of_mem heq ht
  have hzγ : deriv γ t = 0 := ContinuousLinearMap.toSpanSingleton_inj.mp <|
    (uniqueDiffOn_Icc hab).eq ht (hγ t ht).hasDerivAt.hasDerivWithinAt hdwithin
  exact hγne t ht hzγ


lemma scalar_coordinate_from_ray {e : ℂ → ℂ} {γ : ℝ → ℂ} {a b ε : ℝ} {ξ : ℂ}
    (hε : 0 < ε) (hξ : ξ ≠ 0)
    (hray : ∀ t ∈ Icc a b, ∃ r ∈ Icc (0 : ℝ) ε, e (γ t) = r • ξ) :
    let φ : ℝ → ℝ := fun t => (e (γ t) / ξ).re / ε
    (∀ t ∈ Icc a b, φ t ∈ Icc (0 : ℝ) 1) ∧
    ∀ t ∈ Icc a b, e (γ t) = (ε * φ t) • ξ := by
  dsimp only
  constructor
  · intro t ht
    obtain ⟨r, hr, heq⟩ := hray t ht
    rw [heq]
    simp only [Complex.real_smul, mul_div_cancel_right₀ _ hξ, Complex.ofReal_re]
    exact ⟨div_nonneg hr.1 hε.le, (div_le_one hε).mpr hr.2⟩
  · intro t ht
    obtain ⟨r, hr, heq⟩ := hray t ht
    rw [heq]
    simp only [Complex.real_smul, mul_div_cancel_right₀ _ hξ, Complex.ofReal_re]
    congr 1
    field_simp

lemma regular_radial_coordinate {γ : ℝ → ℂ} (e : OpenPartialHomeomorph ℂ ℂ)
    {a b ε : ℝ} {ξ : ℂ} (hab : a < b) (hε : 0 < ε) (hξ : ξ ≠ 0)
    (hγ : ContDiff ℝ 1 γ)
    (he : ContDiffOn ℝ 1 e e.source) (hg : ContDiffOn ℝ 1 e.symm e.target)
    (hsource : ∀ t ∈ Icc a b, γ t ∈ e.source)
    (hray : ∀ t ∈ Icc a b, ∃ r ∈ Icc (0 : ℝ) ε, e (γ t) = r • ξ)
    (hγne : ∀ t ∈ Icc a b, deriv γ t ≠ 0) :
    ∃ (φ : ℝ → ℝ) (N : Set ℝ), IsOpen N ∧ Icc a b ⊆ N ∧
      ContDiffOn ℝ 1 φ N ∧ (∀ t ∈ N, deriv φ t ≠ 0) ∧
      (∀ t ∈ Icc a b, φ t ∈ Icc (0 : ℝ) 1) ∧
      (StrictMonoOn φ (Icc a b) ∨ StrictAntiOn φ (Icc a b)) ∧
      ∀ t ∈ Icc a b, γ t = e.symm ((ε * φ t) • ξ) := by
  let φ : ℝ → ℝ := fun t => (e (γ t) / ξ).re / ε
  have hcoord := scalar_coordinate_from_ray hε hξ hray
  change (∀ t ∈ Icc a b, φ t ∈ Icc (0 : ℝ) 1) ∧
    (∀ t ∈ Icc a b, e (γ t) = (ε * φ t) • ξ) at hcoord
  let S : Set ℝ := γ ⁻¹' e.source
  have hS : IsOpen S := e.open_source.preimage hγ.continuous
  have hsub : Icc a b ⊆ S := hsource
  have hcomp : ContDiffOn ℝ 1 (fun t => e (γ t)) S :=
    he.comp hγ.contDiffOn (fun t ht => ht)
  have hφ : ContDiffOn ℝ 1 φ S := by
    exact (Complex.reCLM.contDiff.comp_contDiffOn (hcomp.div_const ξ)).div_const ε
  have hrep : ∀ t ∈ Icc a b, γ t = e.symm ((ε * φ t) • ξ) := by
    intro t ht
    rw [← hcoord.2 t ht, e.left_inv (hsource t ht)]
  have hne : ∀ t ∈ Icc a b, deriv φ t ≠ 0 :=
    derivative_nonzero_of_reparametrization hab
      (fun t ht => (hφ.contDiffAt (hS.mem_nhds (hsub ht))).differentiableAt (by norm_num))
      (fun t ht => by
        rw [← hcoord.2 t ht]
        exact (hg.contDiffAt (e.open_target.mem_nhds (e.map_source (hsource t ht)))).differentiableAt (by norm_num))
      (fun t ht => hγ.differentiable (by norm_num) t) hγne hrep
  obtain ⟨N, hN, hsubN, hφN, hneN⟩ := nonzero_deriv_neighborhood hS hsub hφ hne
  exact ⟨φ, N, hN, hsubN, hφN, hneN, hcoord.1,
    strict_mono_or_anti_of_deriv_ne_zero hab.le hS hsub hφ hne, hrep⟩





lemma regular_reparametrization {γ : ℝ → ℂ} {g : ℂ → ℂ}
    {φ : ℝ → ℝ} {S : Set ℝ} {a b ε : ℝ} {ξ : ℂ}
    (hab : a < b) (hS : IsOpen S) (hsub : Icc a b ⊆ S)
    (hφ : ContDiffOn ℝ 1 φ S)
    (hg : ∀ t ∈ Icc a b, DifferentiableAt ℝ g ((ε * φ t) • ξ))
    (hγ : ∀ t ∈ Icc a b, DifferentiableAt ℝ γ t)
    (hγne : ∀ t ∈ Icc a b, deriv γ t ≠ 0)
    (heq : ∀ t ∈ Icc a b, γ t = g ((ε * φ t) • ξ))
    (hbound : ∀ t ∈ Icc a b, φ t ∈ Icc (0 : ℝ) 1) :
    ∃ (N : Set ℝ) (lo hi : ℝ), IsOpen N ∧ Icc a b ⊆ N ∧
      ContDiffOn ℝ 1 φ N ∧ (∀ t ∈ N, deriv φ t ≠ 0) ∧
      0 ≤ lo ∧ lo < hi ∧ hi ≤ 1 ∧ φ '' Icc a b = Icc lo hi ∧
      ((StrictMonoOn φ (Icc a b) ∧ φ a = lo ∧ φ b = hi) ∨
        (StrictAntiOn φ (Icc a b) ∧ φ a = hi ∧ φ b = lo)) := by
  have hne : ∀ t ∈ Icc a b, deriv φ t ≠ 0 :=
    derivative_nonzero_of_reparametrization hab
      (fun t ht => (hφ.contDiffAt (hS.mem_nhds (hsub ht))).differentiableAt (by norm_num))
      hg hγ hγne heq
  obtain ⟨N, hN, hsubN, hφN, hneN⟩ := nonzero_deriv_neighborhood hS hsub hφ hne
  have hc : ContinuousOn φ (Icc a b) := hφ.continuousOn.mono hsub
  have ha : a ∈ Icc a b := left_mem_Icc.mpr hab.le
  have hb : b ∈ Icc a b := right_mem_Icc.mpr hab.le
  rcases strict_mono_or_anti_of_deriv_ne_zero hab.le hS hsub hφ hne with hm | hm
  · exact ⟨N, φ a, φ b, hN, hsubN, hφN, hneN,
      (hbound a ha).1, hm ha hb hab, (hbound b hb).2,
      hc.image_Icc_of_monotoneOn hab.le hm.monotoneOn, Or.inl ⟨hm, rfl, rfl⟩⟩
  · exact ⟨N, φ b, φ a, hN, hsubN, hφN, hneN,
      (hbound b hb).1, hm ha hb hab, (hbound a ha).2,
      hc.image_Icc_of_antitoneOn hab.le hm.antitoneOn, Or.inr ⟨hm, rfl, rfl⟩⟩



open CircularCornerRounding CircularExhaustion

lemma bottomRay_mem_frontier_sector {θ r : ℝ} (hθ : 0 < θ)
    (hθ' : θ < 2 * Real.pi) (hr : 0 ≤ r) :
    (r : ℂ) ∈ frontier (sector θ) := by
  have hpos : Ioi (0 : ℝ) ⊆ (fun s : ℝ => (s : ℂ)) ⁻¹' frontier (sector θ) := by
    intro s hs
    have hb := bottomTail_mem_frontier_roundedSector hs hθ hθ' (le_refl s)
    refine ⟨closure_mono sdiff_subset hb.1, ?_⟩
    intro hi
    have hm : (s : ℂ) ∈ sector θ := by
      simpa only [(isOpen_sector θ).interior_eq] using hi
    have hh := (polar_mem_sector_iff hs ⟨le_rfl, hθ.le⟩ hθ').mp
      (show (s : ℂ) * Complex.exp ((0 : ℂ) * I) ∈ sector θ by simpa using hm)
    exact (lt_irrefl (0 : ℝ)) hh.1
  have hc := closure_minimal hpos
    (isClosed_frontier.preimage (show Continuous (fun s : ℝ => (s : ℂ)) by fun_prop))
  rw [closure_Ioi] at hc
  exact hc hr

lemma topRay_mem_frontier_sector {θ r : ℝ} (hθ : 0 < θ)
    (hθ' : θ < 2 * Real.pi) (hr : 0 ≤ r) :
    (r : ℂ) * Complex.exp ((θ : ℂ) * I) ∈ frontier (sector θ) := by
  have hpos : Ioi (0 : ℝ) ⊆
      (fun s : ℝ => (s : ℂ) * Complex.exp ((θ : ℂ) * I)) ⁻¹' frontier (sector θ) := by
    intro s hs
    have hb := topTail_mem_frontier_roundedSector hs hθ hθ' (le_refl s)
    refine ⟨closure_mono sdiff_subset hb.1, ?_⟩
    intro hi
    have hm : (s : ℂ) * Complex.exp ((θ : ℂ) * I) ∈ sector θ := by
      simpa only [(isOpen_sector θ).interior_eq] using hi
    have hh := (polar_mem_sector_iff hs ⟨hθ.le, le_rfl⟩ hθ').mp hm
    exact (lt_irrefl θ) hh.2
  have hc := closure_minimal hpos
    (isClosed_frontier.preimage (show Continuous
      (fun s : ℝ => (s : ℂ) * Complex.exp ((θ : ℂ) * I)) by fun_prop))
  rw [closure_Ioi] at hc
  exact hc hr

lemma shortRay_not_mem_closure_roundedSector {ε θ r s : ℝ}
    (hε : 0 < ε) (hθ : 0 < θ) (hθ' : θ < 2 * Real.pi)
    (hr : 0 ≤ r) (hrε : r < ε) (hs : s = 0 ∨ s = 1) :
    (r : ℂ) * Complex.exp ((θ * smoothStep s : ℝ) * I) ∉
      closure (roundedSector ε θ) := by
  intro hz
  obtain ⟨u, t, ht, hu, he⟩ := mem_closure_roundedSector_polar hε hθ hθ' hz
  have hu0 : 0 < u := (mul_pos hε (radialProfile_pos ht)).trans_le hu
  have hru : r = u := by
    simpa only [norm_polar hr, norm_polar hu0.le] using congrArg norm he
  have hr0 : 0 < r := hru.symm ▸ hu0
  have hsI : s ∈ Icc (0 : ℝ) 1 := by rcases hs with rfl | rfl <;> simp
  have hsa : θ * smoothStep s ∈ Icc (0 : ℝ) θ := by
    constructor
    · exact mul_nonneg hθ.le (smoothStep_mem_Icc hsI).1
    · nlinarith [(smoothStep_mem_Icc hsI).2]
  have hta : θ * smoothStep t ∈ Icc (0 : ℝ) θ := by
    constructor
    · exact mul_nonneg hθ.le (smoothStep_mem_Icc ht).1
    · nlinarith [(smoothStep_mem_Icc ht).2]
  have ha := angle_eq_of_polar_eq hr0 hu0 hsa hta hθ' he
  have hst : s = t := smoothStep_strictMonoOn.injOn hsI ht (mul_left_cancel₀ hθ.ne' ha)
  have hp : radialProfile t = 1 := by
    rw [← hst]
    rcases hs with rfl | rfl <;> simp [radialProfile]
  rw [hp, mul_one, ← hru] at hu
  exact (not_le_of_gt hrε) hu

lemma removed_sector_frontier_eq_open_shortRays {ε θ : ℝ}
    (hε : 0 < ε) (hθ : 0 < θ) (hθ' : θ < 2 * Real.pi) :
    frontier (sector θ) \ frontier (roundedSector ε θ) =
      (fun r : ℝ => (r : ℂ)) '' Ico 0 ε ∪
      (fun r : ℝ => (r : ℂ) * Complex.exp ((θ : ℂ) * I)) '' Ico 0 ε := by
  apply Subset.antisymm
  · intro z hz
    rcases removed_sector_frontier_subset_shortRays hε hθ hz with h | h
    · obtain ⟨r, hr, rfl⟩ := h
      refine Or.inl ⟨r, ⟨hr.1, ?_⟩, rfl⟩
      exact lt_of_le_of_ne hr.2 (fun he => hz.2
        (bottomTail_mem_frontier_roundedSector hε hθ hθ' (by simp [he])))
    · obtain ⟨r, hr, rfl⟩ := h
      refine Or.inr ⟨r, ⟨hr.1, ?_⟩, rfl⟩
      exact lt_of_le_of_ne hr.2 (fun he => hz.2
        (topTail_mem_frontier_roundedSector hε hθ hθ' (by simp [he])))
  · rintro z (⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩)
    · refine ⟨bottomRay_mem_frontier_sector hθ hθ' hr.1, ?_⟩
      intro hz
      have hh := shortRay_not_mem_closure_roundedSector (s := 0) hε hθ hθ' hr.1 hr.2
        (by simp)
      apply hh
      simpa using hz.1
    · refine ⟨topRay_mem_frontier_sector hθ hθ' hr.1, ?_⟩
      intro hz
      have hh := shortRay_not_mem_closure_roundedSector (s := 1) hε hθ hθ' hr.1 hr.2
        (by simp)
      apply hh
      simpa using hz.1


/-- Exact removal, transported through the actual disjoint finite surgery.
The vertex belongs to the removed set; the two cutoff endpoints do not. -/
theorem surgery_removed_frontier_eq {U : Set ℂ} {J : Finset ℂ}
    (c : UniformCharts U J) {ε : ℝ} (hε : 0 < ε) (hεR : ε < c.R) :
    frontier U \ frontier (surgeryDomain c ε) = ⋃ p ∈ J, (c.chart p).symm ''
      ((fun r : ℝ => (r : ℂ)) '' Ico 0 ε ∪
       (fun r : ℝ => (r : ℂ) * Complex.exp ((c.angle p : ℂ) * Complex.I)) '' Ico 0 ε) := by
  have htip : ∀ p ∈ J, sectorTip ε (c.angle p) ⊆ (c.chart p).target := by
    intro p hpJ
    exact (sectorTip_subset_closedBall hε).trans
      ((closedBall_subset_closedBall hεR.le).trans (c.target_bound p hpJ).1)
  let K : Set ℂ := ⋃ p ∈ J, (c.chart p).symm '' sectorTip ε (c.angle p)
  have hK : IsClosed K := (J.isCompact_biUnion fun p hp =>
    (isCompact_sectorTip ε (c.angle p)).image_of_continuousOn
      ((c.chart p).symm.continuousOn.mono (htip p hp))).isClosed
  have hlocal := chart_surgery_isImage c.chart c.angle ε c.side c.disjoint htip
  apply Subset.antisymm
  · intro z hz
    have hzK : z ∈ K := (closed_removal_locality (U := U) hK).2.1 hz
    obtain ⟨p, hp, w, hw, heq⟩ := mem_iUnion₂.mp hzK
    have hzs : z ∈ (c.chart p).source := heq ▸ (c.chart p).map_target (htip p hp hw)
    have hmodel : c.chart p z ∈ frontier (sector (c.angle p)) \
        frontier (roundedSector ε (c.angle p)) :=
      ⟨((c.side p hp).frontier hzs).mpr hz.1,
        fun h => hz.2 (((hlocal p hp).frontier hzs).mp h)⟩
    rw [removed_sector_frontier_eq_open_shortRays hε (c.angle_bounds p hp).1
      (c.angle_bounds p hp).2] at hmodel
    exact mem_iUnion₂.mpr ⟨p, hp, c.chart p z, hmodel, (c.chart p).left_inv hzs⟩
  · intro z hz
    obtain ⟨p, hp, w, hw, rfl⟩ := mem_iUnion₂.mp hz
    have hwball : w ∈ closedBall (0 : ℂ) ε := by
      rcases hw with ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩
      · simpa only [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hr.1] using hr.2.le
      · simpa only [mem_closedBall_zero_iff, norm_polar hr.1] using hr.2.le
    have hwt : w ∈ (c.chart p).target :=
      (c.target_bound p hp).1 ((closedBall_subset_closedBall hεR.le) hwball)
    have hzs := (c.chart p).map_target hwt
    have hmodel : w ∈ frontier (sector (c.angle p)) \ frontier (roundedSector ε (c.angle p)) := by
      rw [removed_sector_frontier_eq_open_shortRays hε (c.angle_bounds p hp).1
        (c.angle_bounds p hp).2]
      exact hw
    have hright := (c.chart p).right_inv hwt
    refine ⟨((c.side p hp).frontier hzs).mp (by simpa only [hright] using hmodel.1), ?_⟩
    intro h
    exact hmodel.2 (by simpa only [hright] using ((hlocal p hp).frontier hzs).mpr h)

/-- Once a literal closed circle piece has been proved to lie on one chart ray,
its regular total scalar change is constructed from the actual chart. -/
theorem ray_change_of_closed_radial_piece {U : Set ℂ} {J : Finset ℂ}
    (c : UniformCharts U J) {ε : ℝ} (hε : 0 < ε)
    (p : ℂ) (hp : p ∈ J) (upper : Bool) (center : ℂ) {radius a b : ℝ}
    (hradius : 0 < radius) (hab : a < b)
    (hsource : ∀ t ∈ Icc a b, arcParam center radius t ∈ (c.chart p).source)
    (hray : ∀ t ∈ Icc a b, ∃ r ∈ Icc (0 : ℝ) ε,
      c.chart p (arcParam center radius t) = r • rayDirection (c.angle p) upper) :
    ∃ d : RayChange c ε center radius a b, d.corner = p ∧ d.upper = upper := by
  have hξ : rayDirection (c.angle p) upper ≠ 0 := by
    cases upper <;> simp [rayDirection, Complex.exp_ne_zero]
  have hγ : ContDiff ℝ 1 (arcParam center radius) := by
    change ContDiff ℝ 1 (circleMap center radius)
    exact contDiffOn_univ.mp ((FiniteCircularArcs.analytic_circle center radius).contDiffOn
      uniqueDiffOn_univ)
  have hγne : ∀ t ∈ Icc a b, deriv (arcParam center radius) t ≠ 0 := by
    intro t _
    change deriv (circleMap center radius) t ≠ 0
    rw [(FiniteCircularArcs.circle_hasDerivAt center radius t).deriv]
    exact mul_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hradius.ne')
      (Complex.exp_ne_zero _)) Complex.I_ne_zero
  obtain ⟨φ, N, hN, hsub, hφ, hreg, hbound, hmono, hcurve⟩ :=
    regular_radial_coordinate (c.chart p) hab hε hξ hγ (c.smooth p hp).1
      (c.smooth p hp).2 hsource hray hγne
  have hc := hφ.continuousOn.mono hsub
  have ha : a ∈ Icc a b := left_mem_Icc.mpr hab.le
  have hb : b ∈ Icc a b := right_mem_Icc.mpr hab.le
  rcases hmono with hm | hm
  · exact ⟨⟨p, hp, upper, φ a, φ b, (hbound a ha).1, hm ha hb hab, (hbound b hb).2,
      φ, N, hN, hsub, hφ, hreg, Or.inl ⟨hm, rfl, rfl⟩,
      hc.image_Icc_of_monotoneOn hab.le hm.monotoneOn, hcurve⟩, rfl, rfl⟩
  · exact ⟨⟨p, hp, upper, φ b, φ a, (hbound b hb).1, hm ha hb hab, (hbound a ha).2,
      φ, N, hN, hsub, hφ, hreg, Or.inr ⟨hm, rfl, rfl⟩,
      hc.image_Icc_of_antitoneOn hab.le hm.antitoneOn, hcurve⟩, rfl, rfl⟩


open CircularExhaustion CircularCornerRounding

theorem rayDirection_norm (θ : ℝ) (upper : Bool) : ‖rayDirection θ upper‖ = 1 := by
  cases upper <;> simp [rayDirection, Complex.norm_exp_ofReal_mul_I]

theorem arcParam_hasDerivAt (center : ℂ) (radius t : ℝ) :
    HasDerivAt (arcParam center radius)
      ((radius : ℂ) * Complex.exp ((t : ℂ) * Complex.I) * Complex.I) t := by
  change HasDerivAt (circleMap center radius)
    ((radius : ℂ) * Complex.exp ((t : ℂ) * Complex.I) * Complex.I) t
  exact FiniteCircularArcs.circle_hasDerivAt center radius t

theorem arcParam_norm_deriv (center : ℂ) {radius : ℝ} (hradius : 0 < radius) (t : ℝ) :
    ‖deriv (arcParam center radius) t‖ = radius := by
  rw [(arcParam_hasDerivAt center radius t).deriv]
  simp [Complex.norm_exp_ofReal_mul_I, abs_of_pos hradius]

theorem RayChange.integral_abs_deriv {U : Set ℂ} {J : Finset ℂ} {c : UniformCharts U J}
    {ε : ℝ} {center : ℂ} {radius a b : ℝ} (hab : a < b)
    (d : RayChange c ε center radius a b) :
    (∫ t in a..b, |deriv d.scalar t|) = d.hi - d.lo := by
  have hdiff : ∀ t ∈ Icc a b, DifferentiableAt ℝ d.scalar t := by
    intro t ht
    exact (d.smooth.differentiableOn (by norm_num) t
      (d.contains_interval ht)).differentiableAt
      (d.open_neighborhood.mem_nhds (d.contains_interval ht))
  have hcont : ContinuousOn (deriv d.scalar) (Icc a b) :=
    (d.smooth.continuousOn_deriv_of_isOpen d.open_neighborhood (by norm_num)).mono
      d.contains_interval
  have hint : IntervalIntegrable (deriv d.scalar) MeasureTheory.volume a b :=
    hcont.intervalIntegrable_of_Icc hab.le
  have hFTC : (∫ t in a..b, deriv d.scalar t) = d.scalar b - d.scalar a :=
    intervalIntegral.integral_deriv_eq_sub (fun t ht => hdiff t (by simpa [uIcc_of_le hab.le] using ht)) hint
  rcases d.monotonicity with ⟨hmono, ha, hb⟩ | ⟨hanti, ha, hb⟩
  · calc
      (∫ t in a..b, |deriv d.scalar t|) = ∫ t in a..b, deriv d.scalar t := by
        apply intervalIntegral.integral_congr_Ioo_of_le hab.le
        intro t ht
        have hnn : 0 ≤ deriv d.scalar t := by
          rw [← derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
          exact hmono.monotoneOn.derivWithin_nonneg
        exact abs_of_nonneg hnn
      _ = d.hi - d.lo := by rw [hFTC, ha, hb]
  · calc
      (∫ t in a..b, |deriv d.scalar t|) = ∫ t in a..b, -deriv d.scalar t := by
        apply intervalIntegral.integral_congr_Ioo_of_le hab.le
        intro t ht
        have hnp : deriv d.scalar t ≤ 0 := by
          rw [← derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
          exact hanti.antitoneOn.derivWithin_nonpos
        exact abs_of_nonpos hnp
      _ = -(d.scalar b - d.scalar a) := by rw [intervalIntegral.integral_neg, hFTC]
      _ = d.hi - d.lo := by rw [ha, hb]; ring

/-- Actual original angular speed is bounded by the actual scalar radial speed. -/
theorem RayChange.angular_speed_le {U : Set ℂ} {J : Finset ℂ} {c : UniformCharts U J}
    {ε : ℝ} {center : ℂ} {radius a b : ℝ} (hε : 0 < ε) (hεR : ε < c.R)
    (hradius : 0 < radius) (d : RayChange c ε center radius a b)
    {t : ℝ} (ht : t ∈ Ioo a b) :
    radius ≤ (c.L : ℝ) * ε * |deriv d.scalar t| := by
  let ξ := rayDirection (c.angle d.corner) d.upper
  let z : ℝ → ℂ := fun s => (ε * d.scalar s) • ξ
  let g : ℂ → ℂ := (c.chart d.corner).symm
  have hξ : ‖ξ‖ = 1 := rayDirection_norm _ _
  have hφ : d.scalar t ∈ Icc d.lo d.hi := by
    rw [← d.image_interval]
    exact mem_image_of_mem _ ⟨ht.1.le, ht.2.le⟩
  have hφ0 : 0 ≤ d.scalar t := d.lo_nonneg.trans hφ.1
  have hφ1 : d.scalar t ≤ 1 := hφ.2.trans d.hi_le_one
  have hzball : z t ∈ ball (0 : ℂ) c.R := by
    simp only [z, mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_mul, abs_of_pos hε, abs_of_nonneg hφ0, hξ, mul_one]
    exact (mul_le_mul_of_nonneg_left hφ1 hε.le).trans_lt (by simpa using hεR)
  have hzclosed : closedBall (0 : ℂ) c.R ∈ 𝓝 (z t) :=
    closedBall_mem_nhds_of_mem hzball
  have hztarget : z t ∈ (c.chart d.corner).target :=
    (c.target_bound d.corner d.corner_mem).1 (mem_of_mem_nhds hzclosed)
  have hgdiff : DifferentiableAt ℝ g (z t) :=
    ((c.smooth d.corner d.corner_mem).2.differentiableOn (by norm_num)
      (z t) hztarget).differentiableAt
      ((c.chart d.corner).open_target.mem_nhds hztarget)
  have hgLip : ‖fderiv ℝ g (z t)‖ ≤ (c.L : ℝ) :=
    norm_fderiv_le_of_lipschitzOn ℝ hzclosed (c.target_bound d.corner d.corner_mem).2
  have hφdiff : DifferentiableAt ℝ d.scalar t :=
    (d.smooth.differentiableOn (by norm_num) t
      (d.contains_interval ⟨ht.1.le, ht.2.le⟩)).differentiableAt
      (d.open_neighborhood.mem_nhds (d.contains_interval ⟨ht.1.le, ht.2.le⟩))
  have hzderiv : HasDerivAt z ((ε * deriv d.scalar t) • ξ) t :=
    (hφdiff.hasDerivAt.const_mul ε).smul_const ξ
  have heq : arcParam center radius =ᶠ[𝓝 t] g ∘ z := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact d.curve_eq s ⟨hs.1.le, hs.2.le⟩
  have hderiv : HasDerivAt (arcParam center radius)
      ((fderiv ℝ g (z t)) ((ε * deriv d.scalar t) • ξ)) t :=
    (hgdiff.hasFDerivAt.comp_hasDerivAt t hzderiv).congr_of_eventuallyEq heq
  calc
    radius = ‖deriv (arcParam center radius) t‖ :=
      (arcParam_norm_deriv center hradius t).symm
    _ = ‖(fderiv ℝ g (z t)) ((ε * deriv d.scalar t) • ξ)‖ := by rw [hderiv.deriv]
    _ ≤ ‖fderiv ℝ g (z t)‖ * ‖(ε * deriv d.scalar t) • ξ‖ :=
      (fderiv ℝ g (z t)).le_opNorm _
    _ ≤ (c.L : ℝ) * ‖(ε * deriv d.scalar t) • ξ‖ :=
      mul_le_mul_of_nonneg_right hgLip (norm_nonneg _)
    _ = (c.L : ℝ) * ε * |deriv d.scalar t| := by
      rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos hε, hξ, mul_one, mul_assoc]

/-- Conditional bound for the original angular parameter length, derived from
its genuine monotone or antitone radial change. -/
theorem RayChange.angular_length_le {U : Set ℂ} {J : Finset ℂ} {c : UniformCharts U J}
    {ε : ℝ} {center : ℂ} {radius a b : ℝ}
    (hε : 0 < ε) (hεR : ε < c.R) (hradius : 0 < radius) (hab : a < b)
    (d : RayChange c ε center radius a b) :
    radius * (b - a) ≤ (c.L : ℝ) * ε * (d.hi - d.lo) := by
  have hcont : ContinuousOn (deriv d.scalar) (Icc a b) :=
    (d.smooth.continuousOn_deriv_of_isOpen d.open_neighborhood (by norm_num)).mono
      d.contains_interval
  have hintAbs : IntervalIntegrable (fun t => |deriv d.scalar t|)
      MeasureTheory.volume a b := by
    simpa only [Real.norm_eq_abs] using (hcont.norm.intervalIntegrable_of_Icc hab.le)
  calc
    radius * (b - a) = ∫ t in a..b, radius := by
      rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
    _ ≤ ∫ t in a..b, (c.L : ℝ) * ε * |deriv d.scalar t| :=
      intervalIntegral.integral_mono_on_of_le_Ioo hab.le intervalIntegrable_const
        (hintAbs.const_mul _) (fun _ ht => d.angular_speed_le hε hεR hradius ht)
    _ = (c.L : ℝ) * ε * (d.hi - d.lo) := by
      rw [intervalIntegral.integral_const_mul, d.integral_abs_deriv hab]





/-- The total length of finitely many disjoint open subintervals of [0,1] is at most one. -/
theorem finite_disjoint_interval_lengths_le_one {α : Type*} [Fintype α]
    (lo hi : α → ℝ) (hlo : ∀ i, 0 ≤ lo i) (hle : ∀ i, lo i ≤ hi i)
    (hhi : ∀ i, hi i ≤ 1)
    (hdisj : Pairwise (fun i j => Disjoint (Ioo (lo i) (hi i)) (Ioo (lo j) (hi j)))) :
    (∑ i, (hi i - lo i)) ≤ 1 := by
  classical
  calc
    (∑ i, (hi i - lo i)) = ∑ i, volume.real (Ioo (lo i) (hi i)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (Real.volume_real_Ioo_of_le (hle i)).symm
    _ = volume.real (⋃ i, Ioo (lo i) (hi i)) :=
      (measureReal_iUnion_fintype hdisj (fun _ => measurableSet_Ioo)
        (fun _ => by simp)).symm
    _ ≤ volume.real (Ioo (0 : ℝ) 1) := by
      apply measureReal_mono _ (by simp)
      intro x hx
      rcases mem_iUnion.mp hx with ⟨i, hx⟩
      exact ⟨(hlo i).trans_lt hx.1, hx.2.trans_le (hhi i)⟩
    _ = 1 := by norm_num

/-- If intervals may overlap only between different tags, their total length
is bounded by the finite number of tags. -/
theorem finite_tagged_interval_lengths_le_card {α γ : Type*} [Fintype α] [Fintype γ]
    (tag : α → γ) (lo hi : α → ℝ)
    (hlo : ∀ i, 0 ≤ lo i) (hle : ∀ i, lo i ≤ hi i) (hhi : ∀ i, hi i ≤ 1)
    (hdisj : ∀ i j, i ≠ j → tag i = tag j →
      Disjoint (Ioo (lo i) (hi i)) (Ioo (lo j) (hi j))) :
    (∑ i, (hi i - lo i)) ≤ Fintype.card γ := by
  classical
  calc
    (∑ i, (hi i - lo i)) = ∑ g : γ, ∑ i : {i // tag i = g}, (hi i - lo i) :=
      (Fintype.sum_fiberwise tag (fun i => hi i - lo i)).symm
    _ ≤ ∑ _g : γ, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro g _
      apply finite_disjoint_interval_lengths_le_one
        (fun i : {i // tag i = g} => lo i) (fun i => hi i)
        (fun i => hlo i) (fun i => hle i) (fun i => hhi i)
      intro i j hij
      exact hdisj i j (fun h => hij (Subtype.ext h)) (i.property.trans j.property.symm)
    _ = Fintype.card γ := by simp

/-- Sum a uniform per-interval estimate after grouping disjoint radial intervals. -/
theorem finite_tagged_weight_sum_le {α γ : Type*} [Fintype α] [Fintype γ]
    (tag : α → γ) (lo hi weight : α → ℝ) {A : ℝ} (hA : 0 ≤ A)
    (hlo : ∀ i, 0 ≤ lo i) (hle : ∀ i, lo i ≤ hi i) (hhi : ∀ i, hi i ≤ 1)
    (hdisj : ∀ i j, i ≠ j → tag i = tag j →
      Disjoint (Ioo (lo i) (hi i)) (Ioo (lo j) (hi j)))
    (hweight : ∀ i, weight i ≤ A * (hi i - lo i)) :
    (∑ i, weight i) ≤ A * Fintype.card γ := by
  calc
    (∑ i, weight i) ≤ ∑ i, A * (hi i - lo i) := Finset.sum_le_sum (fun i _ => hweight i)
    _ = A * ∑ i, (hi i - lo i) := (Finset.mul_sum _ _ _).symm
    _ ≤ A * Fintype.card γ := mul_le_mul_of_nonneg_left
      (finite_tagged_interval_lengths_le_card tag lo hi hlo hle hhi hdisj) hA




lemma preconnected_closed_cover_dichotomy {α : Type*} [TopologicalSpace α]
    {S A B : Set α} (hS : IsPreconnected S) (hA : IsClosed A) (hB : IsClosed B)
    (hcover : S ⊆ A ∪ B) (hdisj : ∀ z ∈ S, z ∈ A → z ∈ B → False) :
    S ⊆ A ∨ S ⊆ B := by
  classical
  by_cases hSA : S ⊆ A
  · exact Or.inl hSA
  · right
    obtain ⟨x, hxS, hxA⟩ := not_subset.mp hSA
    have hxB : x ∈ B := (hcover hxS).resolve_left hxA
    intro y hyS
    by_contra hyB
    have hyA : y ∈ A := (hcover hyS).resolve_right hyB
    obtain ⟨z, hzS, hzA, hzB⟩ :=
      isPreconnected_closed_iff.mp hS A B hA hB hcover ⟨y, hyS, hyA⟩ ⟨x, hxS, hxB⟩
    exact hdisj z hzS hzA hzB

lemma preconnected_finite_closed_cover_choice {α ι : Type*} [TopologicalSpace α]
    [Finite ι] {F : ι → Set α} {S : Set α}
    (hF : ∀ i, IsClosed (F i)) (hS : IsPreconnected S) (hne : S.Nonempty)
    (hcover : S ⊆ ⋃ i, F i)
    (hdisj : ∀ i j, i ≠ j → ∀ z ∈ S, z ∈ F i → z ∈ F j → False) :
    ∃ i, S ⊆ F i := by
  classical
  obtain ⟨x, hxS⟩ := hne
  obtain ⟨i, hxi⟩ := mem_iUnion.mp (hcover hxS)
  let B : Set α := ⋃ j : {j : ι // j ≠ i}, F j.1
  have hB : IsClosed B := isClosed_iUnion_of_finite (fun j => hF j.1)
  have hcoverB : S ⊆ F i ∪ B := by
    intro z hzS
    obtain ⟨j, hzj⟩ := mem_iUnion.mp (hcover hzS)
    by_cases hji : j = i
    · exact Or.inl (hji ▸ hzj)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨j, hji⟩, hzj⟩)
  have hdisjB : ∀ z ∈ S, z ∈ F i → z ∈ B → False := by
    intro z hzS hzi hzB
    obtain ⟨j, hzj⟩ := mem_iUnion.mp hzB
    exact hdisj i j.1 j.2.symm z hzS hzi hzj
  rcases preconnected_closed_cover_dichotomy hS (hF i) hB hcoverB hdisjB with hsi | hsB
  · exact ⟨i, hsi⟩
  · exact False.elim (hdisjB x hxS hxi (hsB hxS))


lemma shortRays_subset_sectorTip {ε θ : ℝ} (hε : 0 < ε) :
    shortRays ε θ ⊆ sectorTip ε θ := by
  rintro z (⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩)
  · refine ⟨(0, r / ε), ⟨by simp, ⟨div_nonneg hr.1 hε.le, (div_le_one hε).mpr hr.2⟩⟩, ?_⟩
    change (r / ε) • roundingArc ε θ 0 = (r : ℂ)
    rw [(roundingArc_endpoints ε θ).1]
    simp only [Complex.real_smul, ← Complex.ofReal_mul, div_mul_cancel₀ _ hε.ne']
  · refine ⟨(1, r / ε), ⟨by simp, ⟨div_nonneg hr.1 hε.le, (div_le_one hε).mpr hr.2⟩⟩, ?_⟩
    change (r / ε) • roundingArc ε θ 1 =
      (r : ℂ) * Complex.exp ((θ : ℂ) * I)
    rw [(roundingArc_endpoints ε θ).2]
    simp only [Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, div_mul_cancel₀ _ hε.ne']

lemma frontier_sector_inter_tip_eq_shortRays {ε θ : ℝ}
    (hε : 0 < ε) (hθ : 0 < θ) (hθ' : θ < 2 * Real.pi) :
    frontier (sector θ) ∩ sectorTip ε θ = shortRays ε θ := by
  apply Subset.antisymm (frontier_sector_inter_tip_subset_shortRays hε hθ)
  intro z hz
  refine ⟨?_, shortRays_subset_sectorTip hε hz⟩
  rcases hz with ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩
  · exact bottomRay_mem_frontier_sector hθ hθ' hr.1
  · exact topRay_mem_frontier_sector hθ hθ' hr.1

lemma chart_tip_subset_target {U : Set ℂ} {J : Finset ℂ}
    (c : UniformCharts U J) {ε : ℝ} (hε : 0 < ε) (hεR : ε < c.R)
    {p : ℂ} (hp : p ∈ J) : sectorTip ε (c.angle p) ⊆ (c.chart p).target :=
  (sectorTip_subset_closedBall hε).trans
    ((closedBall_subset_closedBall hεR.le).trans (c.target_bound p hp).1)

lemma surgery_frontier_inter_tips_eq {U : Set ℂ} {J : Finset ℂ}
    (c : UniformCharts U J) {ε : ℝ} (hε : 0 < ε) (hεR : ε < c.R) :
    frontier U ∩ (⋃ p ∈ J, (c.chart p).symm '' sectorTip ε (c.angle p)) =
      ⋃ p ∈ J, (c.chart p).symm '' shortRays ε (c.angle p) := by
  apply Subset.antisymm
  · rintro z ⟨hz, hzK⟩
    obtain ⟨p, hp, w, hw, rfl⟩ := mem_iUnion₂.mp hzK
    have hwt := chart_tip_subset_target c hε hεR hp hw
    have hws := (c.chart p).map_target hwt
    have hmodel : w ∈ frontier (sector (c.angle p)) := by
      have hh := ((c.side p hp).frontier hws).mpr hz
      rwa [(c.chart p).right_inv hwt] at hh
    refine mem_iUnion₂.mpr ⟨p, hp, w, ?_, rfl⟩
    rw [← frontier_sector_inter_tip_eq_shortRays hε (c.angle_bounds p hp).1
      (c.angle_bounds p hp).2]
    exact ⟨hmodel, hw⟩
  · intro z hz
    obtain ⟨p, hp, w, hw, rfl⟩ := mem_iUnion₂.mp hz
    have hmodel : w ∈ frontier (sector (c.angle p)) ∩ sectorTip ε (c.angle p) := by
      rw [frontier_sector_inter_tip_eq_shortRays hε (c.angle_bounds p hp).1
        (c.angle_bounds p hp).2]
      exact hw
    have hwt := chart_tip_subset_target c hε hεR hp hmodel.2
    have hws := (c.chart p).map_target hwt
    refine ⟨?_, mem_iUnion₂.mpr ⟨p, hp, w, hmodel.2, rfl⟩⟩
    apply ((c.side p hp).frontier hws).mp
    rw [(c.chart p).right_inv hwt]
    exact hmodel.1

lemma common_model_frontier_inter_tip_eq_cutoffs {ε θ : ℝ}
    (hε : 0 < ε) (hθ : 0 < θ) (hθ' : θ < 2 * Real.pi) :
    (frontier (sector θ) ∩ frontier (roundedSector ε θ)) ∩ sectorTip ε θ =
      {(ε : ℂ), (ε : ℂ) * Complex.exp ((θ : ℂ) * I)} := by
  apply Subset.antisymm
  · rintro z ⟨⟨hzU, hzV⟩, hzK⟩
    have hzR : z ∈ shortRays ε θ :=
      (frontier_sector_inter_tip_eq_shortRays hε hθ hθ') ▸ ⟨hzU, hzK⟩
    rcases hzR with ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩
    · have hεr : ε ≤ r := by
        by_contra hh
        have hn := shortRay_not_mem_closure_roundedSector (s := 0) hε hθ hθ'
          hr.1 (not_le.mp hh) (by simp)
        apply hn
        simpa using hzV.1
      have he : r = ε := le_antisymm hr.2 hεr
      simp [he]
    · have hεr : ε ≤ r := by
        by_contra hh
        have hn := shortRay_not_mem_closure_roundedSector (s := 1) hε hθ hθ'
          hr.1 (not_le.mp hh) (by simp)
        apply hn
        simpa using hzV.1
      have he : r = ε := le_antisymm hr.2 hεr
      simp [he]
  · intro z hz
    rcases (show z = (ε : ℂ) ∨ z = (ε : ℂ) * Complex.exp ((θ : ℂ) * I) by simpa using hz) with rfl | rfl
    · refine ⟨⟨bottomRay_mem_frontier_sector hθ hθ' hε.le,
        bottomTail_mem_frontier_roundedSector hε hθ hθ' le_rfl⟩, ?_⟩
      exact shortRays_subset_sectorTip hε (Or.inl ⟨ε, ⟨hε.le, le_rfl⟩, rfl⟩)
    · refine ⟨⟨topRay_mem_frontier_sector hθ hθ' hε.le,
        topTail_mem_frontier_roundedSector hε hθ hθ' le_rfl⟩, ?_⟩
      exact shortRays_subset_sectorTip hε (Or.inr ⟨ε, ⟨hε.le, le_rfl⟩, rfl⟩)

lemma surgery_common_frontier_inter_tips_eq_cutoffs {U : Set ℂ} {J : Finset ℂ}
    (c : UniformCharts U J) {ε : ℝ} (hε : 0 < ε) (hεR : ε < c.R) :
    (frontier U ∩ frontier (surgeryDomain c ε)) ∩
        (⋃ p ∈ J, (c.chart p).symm '' sectorTip ε (c.angle p)) =
      ⋃ p ∈ J, {(c.chart p).symm (ε : ℂ),
        (c.chart p).symm ((ε : ℂ) * Complex.exp ((c.angle p : ℂ) * I))} := by
  have htip : ∀ p ∈ J, sectorTip ε (c.angle p) ⊆ (c.chart p).target :=
    fun p hp => chart_tip_subset_target c hε hεR hp
  have hlocal : ∀ p ∈ J, (c.chart p).IsImage (surgeryDomain c ε)
      (roundedSector ε (c.angle p)) :=
    chart_surgery_isImage c.chart c.angle ε c.side c.disjoint htip
  apply Subset.antisymm
  · rintro z ⟨⟨hzU, hzV⟩, hzK⟩
    obtain ⟨p, hp, w, hw, rfl⟩ := mem_iUnion₂.mp hzK
    have hwt := htip p hp hw
    have hws := (c.chart p).map_target hwt
    have hmodelU : w ∈ frontier (sector (c.angle p)) := by
      have hh := ((c.side p hp).frontier hws).mpr hzU
      rwa [(c.chart p).right_inv hwt] at hh
    have hmodelV : w ∈ frontier (roundedSector ε (c.angle p)) := by
      have hh := ((hlocal p hp).frontier hws).mpr hzV
      rwa [(c.chart p).right_inv hwt] at hh
    have hwcut := (Set.ext_iff.mp (common_model_frontier_inter_tip_eq_cutoffs hε
      (c.angle_bounds p hp).1 (c.angle_bounds p hp).2) w).mp ⟨⟨hmodelU, hmodelV⟩, hw⟩
    refine mem_iUnion₂.mpr ⟨p, hp, ?_⟩
    rcases (show w = (ε : ℂ) ∨ w = (ε : ℂ) * Complex.exp ((c.angle p : ℂ) * I) by
      simpa using hwcut) with rfl | rfl <;> simp
  · intro z hz
    obtain ⟨p, hp, hz⟩ := mem_iUnion₂.mp hz
    have hmodelCut : ∀ w ∈ ({(ε : ℂ), (ε : ℂ) * Complex.exp ((c.angle p : ℂ) * I)} : Set ℂ),
        (c.chart p).symm w ∈
          (frontier U ∩ frontier (surgeryDomain c ε)) ∩
            (⋃ q ∈ J, (c.chart q).symm '' sectorTip ε (c.angle q)) := by
      intro w hw
      have hmod := (Set.ext_iff.mp (common_model_frontier_inter_tip_eq_cutoffs hε
        (c.angle_bounds p hp).1 (c.angle_bounds p hp).2) w).mpr hw
      have hwt := htip p hp hmod.2
      have hws := (c.chart p).map_target hwt
      refine ⟨⟨?_, ?_⟩, mem_iUnion₂.mpr ⟨p, hp, w, hmod.2, rfl⟩⟩
      · apply ((c.side p hp).frontier hws).mp
        rw [(c.chart p).right_inv hwt]
        exact hmod.1.1
      · apply ((hlocal p hp).frontier hws).mp
        rw [(c.chart p).right_inv hwt]
        exact hmod.1.2
    rcases (show z = (c.chart p).symm (ε : ℂ) ∨
      z = (c.chart p).symm ((ε : ℂ) * Complex.exp ((c.angle p : ℂ) * I)) by
      simpa using hz) with rfl | rfl
    · exact hmodelCut _ (by simp)
    · exact hmodelCut _ (by simp)


/-- Parameter lengths of any genuine finite family of deleted pieces admit
one uniform bound once same-ray radial interiors have been proved disjoint.
The number of angular pieces does not occur in the bound. -/
theorem deleted_family_length_le {U : Set ℂ} {J : Finset ℂ}
    (c : UniformCharts U J) {ε : ℝ} (hε : 0 < ε) (hεR : ε < c.R)
    {α : Type*} [Fintype α] (center : α → ℂ) (radius a b : α → ℝ)
    (hradius : ∀ i, 0 < radius i) (hab : ∀ i, a i < b i)
    (d : ∀ i, RayChange c ε (center i) (radius i) (a i) (b i))
    (hdisj : ∀ i j, i ≠ j → (d i).corner = (d j).corner →
      (d i).upper = (d j).upper →
      Disjoint (Ioo (d i).lo (d i).hi) (Ioo (d j).lo (d j).hi)) :
    (∑ i, radius i * (b i - a i)) ≤ (2 * J.card * (c.L : ℝ)) * ε := by
  classical
  let tag : α → {p : ℂ // p ∈ J} × Bool := fun i =>
    (⟨(d i).corner, (d i).corner_mem⟩, (d i).upper)
  have hh := finite_tagged_weight_sum_le tag (fun i => (d i).lo) (fun i => (d i).hi)
    (fun i => radius i * (b i - a i)) (mul_nonneg c.L.coe_nonneg hε.le)
    (fun i => (d i).lo_nonneg) (fun i => (d i).lo_lt_hi.le) (fun i => (d i).hi_le_one)
    (fun i j hij htag => hdisj i j hij
      (congrArg (fun z : {p : ℂ // p ∈ J} × Bool => z.1.val) htag)
      (congrArg Prod.snd htag))
    (fun i => (d i).angular_length_le hε hεR (hradius i) (hab i))
  calc
    _ ≤ (c.L : ℝ) * ε * Fintype.card ({p : ℂ // p ∈ J} × Bool) := hh
    _ = (2 * J.card * (c.L : ℝ)) * ε := by simp; ring

lemma RayChange.scalar_mem_open_iff {U : Set ℂ} {J : Finset ℂ} {c : UniformCharts U J}
    {ε : ℝ} {center : ℂ} {radius a b t : ℝ} (d : RayChange c ε center radius a b)
    (ht : t ∈ Icc a b) : d.scalar t ∈ Ioo d.lo d.hi ↔ t ∈ Ioo a b := by
  rcases d.monotonicity with ⟨hm, ha, hb⟩ | ⟨hm, ha, hb⟩
  · constructor
    · intro h
      constructor
      · exact lt_of_le_of_ne ht.1 (fun he => by simpa only [← he, ha, lt_self_iff_false] using h.1)
      · exact lt_of_le_of_ne ht.2 (fun he => by simpa only [he, hb, lt_self_iff_false] using h.2)
    · intro h
      have haa : a ∈ Icc a b := ⟨le_rfl, ht.1.trans ht.2⟩
      have hbb : b ∈ Icc a b := ⟨ht.1.trans ht.2, le_rfl⟩
      exact ⟨ha ▸ hm haa ht h.1, hb ▸ hm ht hbb h.2⟩
  · constructor
    · intro h
      constructor
      · exact lt_of_le_of_ne ht.1 (fun he => by simpa only [← he, ha, lt_self_iff_false] using h.2)
      · exact lt_of_le_of_ne ht.2 (fun he => by simpa only [he, hb, lt_self_iff_false] using h.1)
    · intro h
      have haa : a ∈ Icc a b := ⟨le_rfl, ht.1.trans ht.2⟩
      have hbb : b ∈ Icc a b := ⟨ht.1.trans ht.2, le_rfl⟩
      exact ⟨hb ▸ hm ht hbb h.2, ha ▸ hm haa ht h.1⟩

lemma RayChange.exists_open_preimage {U : Set ℂ} {J : Finset ℂ} {c : UniformCharts U J}
    {ε : ℝ} {center : ℂ} {radius a b s : ℝ} (d : RayChange c ε center radius a b)
    (hs : s ∈ Ioo d.lo d.hi) : ∃ t ∈ Ioo a b, d.scalar t = s := by
  have hsimage : s ∈ d.scalar '' Icc a b := by
    rw [d.image_interval]
    exact ⟨hs.1.le, hs.2.le⟩
  obtain ⟨t, ht, he⟩ := hsimage
  exact ⟨t, (d.scalar_mem_open_iff ht).mp (he.symm ▸ hs), he⟩

/-- These are equalities of parametrized open images, derived from the actual
strict changes, rather than a containment or a Hausdorff estimate. -/
lemma RayChange.open_curve_image {U : Set ℂ} {J : Finset ℂ} {c : UniformCharts U J}
    {ε : ℝ} {center : ℂ} {radius a b : ℝ} (d : RayChange c ε center radius a b) :
    arcParam center radius '' Ioo a b =
      (fun s : ℝ => (c.chart d.corner).symm
        ((ε * s) • rayDirection (c.angle d.corner) d.upper)) '' Ioo d.lo d.hi := by
  apply Subset.antisymm
  · rintro z ⟨t, ht, rfl⟩
    exact ⟨d.scalar t, (d.scalar_mem_open_iff ⟨ht.1.le, ht.2.le⟩).mpr ht,
      (d.curve_eq t ⟨ht.1.le, ht.2.le⟩).symm⟩
  · rintro z ⟨s, hs, rfl⟩
    obtain ⟨t, ht, he⟩ := d.exists_open_preimage hs
    exact ⟨t, ht, by simpa only [he] using d.curve_eq t ⟨ht.1.le, ht.2.le⟩⟩




/-- A connected piece of the old frontier avoiding cutoff joins has one status. -/
theorem preconnected_retained_or_deleted {α : Type*} [TopologicalSpace α]
    {A B K S : Set α} (hS : IsPreconnected S) (hSA : S ⊆ A)
    (hB : IsClosed B) (hK : IsClosed K) (hremoved : A \ B ⊆ K)
    (hcommon : ∀ z ∈ S, z ∈ B → z ∉ K) : S ⊆ B ∨ S ⊆ Bᶜ := by
  classical
  by_cases hret : S ⊆ B
  · exact Or.inl hret
  · right
    obtain ⟨x, hxS, hxB⟩ := not_subset.mp hret
    intro y hyS hyB
    have hcover : S ⊆ Kᶜ ∪ Bᶜ := by
      intro z hzS
      by_cases hzB : z ∈ B
      · exact Or.inl (hcommon z hzS hzB)
      · exact Or.inr hzB
    obtain ⟨z, hzS, hzK, hzB⟩ := hS Kᶜ Bᶜ hK.isOpen_compl hB.isOpen_compl
      hcover ⟨y, hyS, hcommon y hyS hyB⟩ ⟨x, hxS, hxB⟩
    exact hzK (hremoved ⟨hSA hzS, hzB⟩)

/-- Continuity extends retained membership from the open interval to both endpoints. -/
theorem closed_image_subset_of_open_image_subset {α : Type*} [TopologicalSpace α]
    {f : ℝ → α} (hf : Continuous f) {a b : ℝ} (hab : a < b)
    {B : Set α} (hB : IsClosed B) (hinside : f '' Ioo a b ⊆ B) :
    f '' Icc a b ⊆ B := by
  rw [← closure_Ioo hab.ne]
  exact (image_closure_subset_closure_image hf).trans (closure_minimal hinside hB)

/-- Actual finite status subdivision from a finite physical marked set. The mark set
contains all common-frontier points inside the closed removal set. -/
theorem exists_status_subdivision {α : Type*} [TopologicalSpace α]
    {f : ℝ → α} (hf : Continuous f) {a b : ℝ} (hab : a < b)
    (hinj : InjOn f (Ioo a b)) {A B K M : Set α} (hM : M.Finite)
    (hA : f '' Icc a b ⊆ A) (hB : IsClosed B) (hK : IsClosed K)
    (hremoved : A \ B ⊆ K) (hcut : (A ∩ B) ∩ K ⊆ M) :
    ∃ s : Subdivision a b,
      (∀ t ∈ Icc a b, f t ∈ M → t ∈ range s.node) ∧
      (∀ j : Fin s.k, ∀ t ∈ Ioo (s.node j.castSucc) (s.node j.succ),
        f t ∈ B ↔ s.retained j = true) ∧
      (∀ j : Fin s.k, s.retained j = true →
        f '' Icc (s.node j.castSucc) (s.node j.succ) ⊆ B) ∧
      (∀ j : Fin s.k, s.retained j = true →
        ∀ t ∈ Ioo (s.node j.castSucc) (s.node j.succ), f t ∉ K) ∧
      (∀ j : Fin s.k, ∀ t ∈ Ioo (s.node j.castSucc) (s.node j.succ), f t ∉ M) := by
  classical
  obtain ⟨k, hk, node, hmono, hfirst, hlast, hmarks, havoid⟩ :=
    exists_finite_marked_nodes hab hinj M hM
  have hnodebounds : ∀ j, node j ∈ Icc a b := by
    intro j
    constructor
    · rw [← hfirst]
      exact hmono.monotone (Fin.zero_le _)
    · rw [← hlast]
      exact hmono.monotone (Fin.le_last _)
  have hinterval : ∀ j : Fin k, Icc (node j.castSucc) (node j.succ) ⊆ Icc a b := by
    intro j t ht
    exact ⟨(hnodebounds _).1.trans ht.1, ht.2.trans (hnodebounds _).2⟩
  have hstrict : ∀ j : Fin k, node j.castSucc < node j.succ := fun j =>
    hmono (show j.castSucc < j.succ from Fin.castSucc_lt_succ)
  have hcommon : ∀ (j : Fin k), ∀ z ∈ f '' Ioo (node j.castSucc) (node j.succ),
      z ∈ B → z ∉ K := by
    intro j z hz hzB hzK
    obtain ⟨t, ht, rfl⟩ := hz
    exact havoid j t ht (hcut ⟨⟨hA (mem_image_of_mem _ (hinterval j ⟨ht.1.le, ht.2.le⟩)), hzB⟩, hzK⟩)
  have hdichotomy : ∀ j : Fin k,
      (f '' Ioo (node j.castSucc) (node j.succ) ⊆ B) ∨
      (f '' Ioo (node j.castSucc) (node j.succ) ⊆ Bᶜ) := by
    intro j
    apply preconnected_retained_or_deleted (isPreconnected_Ioo.image f hf.continuousOn)
      (fun z hz => ?_) hB hK hremoved (hcommon j)
    obtain ⟨t, ht, rfl⟩ := hz
    exact hA (mem_image_of_mem _ (hinterval j ⟨ht.1.le, ht.2.le⟩))
  let retained : Fin k → Bool := fun j => decide (f '' Ioo (node j.castSucc) (node j.succ) ⊆ B)
  let s : Subdivision a b := ⟨k, node, hmono, hfirst, hlast, retained⟩
  have hret : ∀ j : Fin k, s.retained j = true ↔
      f '' Ioo (node j.castSucc) (node j.succ) ⊆ B := by
    intro j
    simp [s, retained]
  refine ⟨s, hmarks, ?_, ?_, ?_, havoid⟩
  · intro j t ht
    constructor
    · intro htB
      apply (hret j).mpr
      rcases hdichotomy j with h | h
      · exact h
      · exact False.elim (h (mem_image_of_mem _ ht) htB)
    · intro htrue
      exact (hret j).mp htrue (mem_image_of_mem _ ht)
  · intro j htrue
    exact closed_image_subset_of_open_image_subset hf (hstrict j) hB ((hret j).mp htrue)
  · intro j htrue t ht
    exact hcommon j _ (mem_image_of_mem _ ht) ((hret j).mp htrue (mem_image_of_mem _ ht))

/-- Retained points have an actual neighborhood on which the original set and
its literal removal agree, preserving any supplied local side formula. -/
theorem retained_local_side {α : Type*} [TopologicalSpace α] {U K W₀ : Set α}
    (hK : IsClosed K) {z : α} (hzK : z ∉ K) (hW₀ : IsOpen W₀) (hzW₀ : z ∈ W₀)
    {P : α → Prop} (hside : ∀ w ∈ W₀, w ∈ U ↔ P w) :
    ∃ W : Set α, IsOpen W ∧ z ∈ W ∧ U ∩ W = (U \ K) ∩ W ∧
      ∀ w ∈ W, w ∈ U \ K ↔ P w := by
  refine ⟨W₀ ∩ Kᶜ, hW₀.inter hK.isOpen_compl, ⟨hzW₀, hzK⟩, ?_, ?_⟩
  · ext w
    simp only [mem_inter_iff, Set.mem_sdiff, mem_compl_iff]
    constructor
    · rintro ⟨hu, hw, hk⟩
      exact ⟨⟨hu, hk⟩, hw, hk⟩
    · rintro ⟨⟨hu, _⟩, hw⟩
      exact ⟨hu, hw⟩
  · intro w hw
    exact ⟨fun h => (hside w hw.1).mp h.1,
      fun h => ⟨(hside w hw.1).mpr h, hw.2⟩⟩


lemma rayDirection_norm_for_fixed_ray (θ : ℝ) (upper : Bool) :
    ‖rayDirection θ upper‖ = 1 := by
  exact rayDirection_norm θ upper

lemma fixed_ray_direction_eq_of_positive_smul_eq {θ r s : ℝ}
    (hθ : 0 < θ) (hθ' : θ < 2 * Real.pi) (hr : 0 < r) (hs : 0 < s)
    {upper upper' : Bool}
    (heq : r • rayDirection θ upper = s • rayDirection θ upper') : upper = upper' := by
  cases upper <;> cases upper'
  · rfl
  · exfalso
    have he : (r : ℂ) * Complex.exp ((0 : ℂ) * I) =
        (s : ℂ) * Complex.exp ((θ : ℂ) * I) := by
      simpa [rayDirection, Complex.real_smul] using heq
    have hh := angle_eq_of_polar_eq hr hs ⟨le_rfl, hθ.le⟩ ⟨hθ.le, le_rfl⟩ hθ' he
    exact hθ.ne' hh.symm
  · exfalso
    have he : (s : ℂ) * Complex.exp ((0 : ℂ) * I) =
        (r : ℂ) * Complex.exp ((θ : ℂ) * I) := by
      simpa [rayDirection, Complex.real_smul] using heq.symm
    have hh := angle_eq_of_polar_eq hs hr ⟨le_rfl, hθ.le⟩ ⟨hθ.le, le_rfl⟩ hθ' he
    exact hθ.ne' hh.symm
  · rfl

lemma deleted_interval_fixed_closed_ray {U : Set ℂ} {J : Finset ℂ}
    (c : UniformCharts U J) {ε a b : ℝ} (hε : 0 < ε) (hεR : ε < c.R)
    {γ : ℝ → ℂ} (hγ : Continuous γ) (hab : a < b)
    (hdel : ∀ t ∈ Ioo a b, γ t ∈ frontier U \ frontier (surgeryDomain c ε))
    (havoid : ∀ t ∈ Ioo a b, γ t ∉ J) :
    ∃ p ∈ J, ∃ upper : Bool, ∀ t ∈ Icc a b,
      γ t ∈ (c.chart p).source ∧ ∃ r ∈ Icc (0 : ℝ) ε,
        c.chart p (γ t) = r • rayDirection (c.angle p) upper := by
  classical
  let ι := {p : ℂ // p ∈ J} × Bool
  let F : ι → Set ℂ := fun i =>
    (c.chart i.1.1).symm '' ((fun r : ℝ => r • rayDirection (c.angle i.1.1) i.2) '' Icc 0 ε)
  have htarget : ∀ p ∈ J, ∀ upper : Bool, ∀ r ∈ Icc (0 : ℝ) ε,
      r • rayDirection (c.angle p) upper ∈ (c.chart p).target := by
    intro p hp upper r hr
    apply (c.target_bound p hp).1
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hr.1, rayDirection_norm_for_fixed_ray, mul_one]
    exact hr.2.trans hεR.le
  have hF : ∀ i, IsClosed (F i) := by
    intro i
    apply IsCompact.isClosed
    apply (isCompact_Icc.image (show Continuous
      (fun r : ℝ => r • rayDirection (c.angle i.1.1) i.2) by fun_prop)).image_of_continuousOn
    apply (c.chart i.1.1).symm.continuousOn.mono
    rintro w ⟨r, hr, rfl⟩
    exact htarget i.1.1 i.1.2 i.2 r hr
  have hsource : ∀ i (z : ℂ), z ∈ F i → z ∈ (c.chart i.1.1).source := by
    rintro i z ⟨w, ⟨r, hr, rfl⟩, heq⟩
    exact heq ▸ (c.chart i.1.1).map_target (htarget i.1.1 i.1.2 i.2 r hr)
  let S := γ '' Ioo a b
  have hS : IsPreconnected S := isPreconnected_Ioo.image γ hγ.continuousOn
  have hSne : S.Nonempty := by
    obtain ⟨t, ht⟩ := nonempty_Ioo.mpr hab
    exact ⟨γ t, t, ht, rfl⟩
  have htip : ∀ p ∈ J, sectorTip ε (c.angle p) ⊆ (c.chart p).target := by
    intro p hp
    exact (sectorTip_subset_closedBall hε).trans
      ((closedBall_subset_closedBall hεR.le).trans (c.target_bound p hp).1)
  have hremoved := (chart_surgery_frontier_differences c.chart c.angle hε
    c.angle_bounds c.side c.disjoint htip).1
  have hcover : S ⊆ ⋃ i, F i := by
    rintro z ⟨t, ht, rfl⟩
    obtain ⟨p, hp, w, hw, heq⟩ := mem_iUnion₂.mp (hremoved (hdel t ht))
    rcases hw with ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩
    · refine mem_iUnion.mpr ⟨(⟨p, hp⟩, false), ?_⟩
      refine ⟨(r : ℂ), ⟨r, hr, ?_⟩, heq⟩
      simp [rayDirection]
    · refine mem_iUnion.mpr ⟨(⟨p, hp⟩, true), ?_⟩
      refine ⟨(r : ℂ) * Complex.exp ((c.angle p : ℂ) * I), ⟨r, hr, ?_⟩, heq⟩
      simp [rayDirection, Complex.real_smul]
  have hdisj : ∀ i j, i ≠ j → ∀ z ∈ S, z ∈ F i → z ∈ F j → False := by
    rintro ⟨⟨p, hp⟩, upper⟩ ⟨⟨q, hq⟩, upper'⟩ hij z hzS hzi hzj
    by_cases hpq : p = q
    · subst q
      obtain ⟨t, ht, rfl⟩ := hzS
      obtain ⟨w, ⟨r, hr, rfl⟩, heq⟩ := hzi
      obtain ⟨w', ⟨s, hs, rfl⟩, heq'⟩ := hzj
      have hinv : (c.chart p).symm (0 : ℂ) = p := by
        rw [← (c.normalized p hp).2]
        exact (c.chart p).left_inv (c.normalized p hp).1
      have hr0 : 0 < r := lt_of_le_of_ne hr.1 (by
        intro he
        have hzP : γ t = p := by simpa [← he, hinv] using heq.symm
        exact havoid t ht (hzP ▸ hp))
      have hs0 : 0 < s := lt_of_le_of_ne hs.1 (by
        intro he
        have hzP : γ t = p := by simpa [← he, hinv] using heq'.symm
        exact havoid t ht (hzP ▸ hp))
      have hcoord : r • rayDirection (c.angle p) upper =
          s • rayDirection (c.angle p) upper' := by
        calc
          _ = c.chart p (γ t) := by rw [← heq, (c.chart p).right_inv (htarget p hp upper r hr)]
          _ = _ := by rw [← heq', (c.chart p).right_inv (htarget p hp upper' s hs)]
      have hupper := fixed_ray_direction_eq_of_positive_smul_eq
        (c.angle_bounds p hp).1 (c.angle_bounds p hp).2 hr0 hs0 hcoord
      apply hij
      cases hupper
      rfl
    · exact Set.disjoint_left.mp (c.disjoint p hp q hq hpq)
        (hsource _ z hzi) (hsource _ z hzj)
  obtain ⟨i, hi⟩ := preconnected_finite_closed_cover_choice hF hS hSne hcover hdisj
  have hclosed : Icc a b ⊆ γ ⁻¹' F i := by
    have hsub : Ioo a b ⊆ γ ⁻¹' F i := fun t ht => hi ⟨t, ht, rfl⟩
    have hc := closure_minimal hsub ((hF i).preimage hγ)
    rwa [closure_Ioo hab.ne] at hc
  refine ⟨i.1.1, i.1.2, i.2, ?_⟩
  intro t ht
  have hmem := hclosed ht
  refine ⟨hsource i (γ t) hmem, ?_⟩
  obtain ⟨w, ⟨r, hr, rfl⟩, heq⟩ := hmem
  refine ⟨r, hr, ?_⟩
  rw [← heq, (c.chart i.1.1).right_inv (htarget i.1.1 i.1.2 i.2 r hr)]



open CircularExhaustion CircularCornerRounding

def emptyUniformCharts (U : Set ℂ) : UniformCharts U ∅ where
  angle := fun _ => Real.pi
  chart := fun _ => OpenPartialHomeomorph.refl ℂ
  R := 1
  L := 1
  radius_pos := by norm_num
  lipschitz_pos := by norm_num
  angle_bounds := by simp
  side := by simp
  smooth := by simp
  normalized := by simp
  disjoint := by simp
  target_bound := by simp

lemma surgeryDomain_empty {U : Set ℂ} (c : UniformCharts U ∅) (ε : ℝ) :
    surgeryDomain c ε = U := by
  simp [surgeryDomain]

abbrev uncutSubdivision {a b : ℝ} (hab : a < b) : Subdivision a b where
  k := 1
  node := fun j => if j.val = 0 then a else b
  strict := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    simpa using hab
  first := by simp
  last := by simp
  retained := fun _ => true

lemma uncutSubdivision_left {a b : ℝ} (hab : a < b) (j : Fin 1) :
    (uncutSubdivision hab).node j.castSucc = a := by
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  rfl

lemma uncutSubdivision_right {a b : ℝ} (hab : a < b) (j : Fin 1) :
    (uncutSubdivision hab).node j.succ = b := by
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  rfl

def emptyCutsAt {U : Set ℂ} {n : ℕ} {center : Fin n → ℂ}
    {radius start stop sign : Fin n → ℝ} (c : UniformCharts U ∅)
    (h : BoundaryHypotheses U n center radius start stop sign)
    (ε : ℝ) (hε : 0 < ε) : CutsAt c n center radius start stop sign ε 1 := by
  obtain ⟨hr, hsign, hcover, hdisjoint, hinj, hside⟩ := h
  have hfront (i : Fin n) : arcParam (center i) (radius i) '' Icc (start i) (stop i) ⊆ frontier U := by
    rw [hcover]
    exact subset_iUnion (fun i => arcParam (center i) (radius i) '' Icc (start i) (stop i)) i
  refine {
    cuts := fun i => uncutSubdivision (hr i).2.1
    retained_closed := ?_
    retained_cover := ?_
    open_classification := ?_
    retained_side := ?_
    deleted := ?_
    radial_cover := ?_
    radial_disjoint := ?_
    corner_cuts := ?_
    deleted_length := ?_ }
  · intro i j hj
    rw [surgeryDomain_empty, uncutSubdivision_left, uncutSubdivision_right]
    exact hfront i
  · intro z
    rw [surgeryDomain_empty, inter_self]
    constructor
    · intro hz
      have hz' : z ∈ ⋃ i, arcParam (center i) (radius i) '' Icc (start i) (stop i) := by
        rwa [← hcover]
      obtain ⟨i, hi⟩ := mem_iUnion.mp hz'
      exact ⟨i, (0 : Fin 1), rfl, by exact hi⟩
    · rintro ⟨i, j, hj, hz⟩
      have hj0 : j = 0 := Subsingleton.elim _ _
      subst j
      exact hfront i hz
  · intro i j t ht
    rw [uncutSubdivision_left, uncutSubdivision_right] at ht
    simp only [surgeryDomain_empty, iff_true]
    exact hfront i ⟨t, Ioo_subset_Icc_self ht, rfl⟩
  · intro i j hj t ht
    rw [uncutSubdivision_left, uncutSubdivision_right] at ht
    obtain ⟨W, hW, htW, hside⟩ := hside i t ht
    exact ⟨W, hW, htW, by rw [surgeryDomain_empty], by simpa only [surgeryDomain_empty] using hside⟩
  · intro i j hj
    simp at hj
  · intro p hp
    simp at hp
  · intro i j hj
    simp at hj
  · intro i t ht hmem
    simp at hmem
  · simp only [uncutSubdivision, ↓reduceIte, Finset.sum_const_zero]
    positivity

theorem circular_angular_cuts_empty (U : Set ℂ) (n : ℕ) (center : Fin n → ℂ)
    (radius start stop sign : Fin n → ℝ)
    (h : BoundaryHypotheses U n center radius start stop sign) :
    ∃ (c : UniformCharts U ∅) (ε₀ Cdel : ℝ),
      0 < ε₀ ∧ ε₀ ≤ c.R ∧ 0 < Cdel ∧
      (∀ p ∈ (∅ : Finset ℂ), ∀ i, ∀ q ∈ ({arcParam (center i) (radius i) (start i),
          arcParam (center i) (radius i) (stop i)} : Set ℂ), q ≠ p → q ∉ (c.chart p).source) ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ → Nonempty (CutsAt c n center radius start stop sign ε Cdel) := by
  refine ⟨emptyUniformCharts U, 1, 1, by norm_num, by rfl, by norm_num, ?_, ?_⟩
  · simp
  · intro ε hε hε₀
    exact ⟨emptyCutsAt (emptyUniformCharts U) h ε hε⟩


lemma Subdivision.k_pos {a b : ℝ} (s : Subdivision a b) (hab : a < b) : 0 < s.k := by
  by_contra h
  have hk : s.k = 0 := by omega
  have hindex : Fin.last s.k = (0 : Fin (s.k + 1)) := by apply Fin.ext; simp [hk]
  have he : a = b := s.first.symm.trans ((congrArg s.node hindex).symm.trans s.last)
  exact hab.ne he

lemma Subdivision.node_mem {a b : ℝ} (s : Subdivision a b) (j : Fin (s.k + 1)) :
    s.node j ∈ Icc a b := by
  constructor
  · simpa only [s.first] using s.strict.monotone (Fin.zero_le j)
  · simpa only [s.last] using s.strict.monotone (Fin.le_last j)

lemma Subdivision.closed_cover {a b : ℝ} (s : Subdivision a b) (hab : a < b) :
    (⋃ j : Fin s.k, Icc (s.node j.castSucc) (s.node j.succ)) = Icc a b := by
  simpa only [s.first, s.last] using iUnion_node_intervals (s.k_pos hab) s.node s.strict.monotone

lemma Subdivision.open_subset {a b : ℝ} (s : Subdivision a b) (j : Fin s.k) :
    Ioo (s.node j.castSucc) (s.node j.succ) ⊆ Ioo a b := by
  intro t ht
  exact ⟨(s.node_mem j.castSucc).1.trans_lt ht.1, ht.2.trans_le (s.node_mem j.succ).2⟩

lemma ray_point_target {U : Set ℂ} {J : Finset ℂ} (c : UniformCharts U J)
    {ε : ℝ} (hε : 0 < ε) (hεR : ε < c.R) {p : ℂ} (hp : p ∈ J)
    (upper : Bool) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (ε * s) • rayDirection (c.angle p) upper ∈ (c.chart p).target := by
  apply (c.target_bound p hp).1
  rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hε.le hs.1), rayDirection_norm, mul_one]
  have hmul : ε * s ≤ ε := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hs.2 hε.le
  exact hmul.trans hεR.le

/-- On each of the two rays, every strictly interior radial point is represented
by a deleted angular piece. No radial partition is assumed here. -/
theorem deleted_radial_interior_cover {U : Set ℂ} {J : Finset ℂ}
    (c : UniformCharts U J) {ε : ℝ} (hε : 0 < ε) (hεR : ε < c.R)
    {n : ℕ} {center : Fin n → ℂ} {radius start stop sign : Fin n → ℝ}
    (hboundary : BoundaryHypotheses U n center radius start stop sign)
    (s : ∀ i, Subdivision (start i) (stop i))
    (hret : ∀ i (j : Fin (s i).k), (s i).retained j = true →
      arcParam (center i) (radius i) '' Icc ((s i).node j.castSucc) ((s i).node j.succ) ⊆
        frontier (surgeryDomain c ε))
    (d : ∀ i (j : Fin (s i).k), (s i).retained j = false →
      RayChange c ε (center i) (radius i) ((s i).node j.castSucc) ((s i).node j.succ))
    (p : ℂ) (hp : p ∈ J) (upper : Bool) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    ∃ (i : Fin n) (j : Fin (s i).k) (h : (s i).retained j = false),
      (d i j h).corner = p ∧ (d i j h).upper = upper ∧
      r ∈ Icc (d i j h).lo (d i j h).hi := by
  classical
  let w : ℂ := (ε * r) • rayDirection (c.angle p) upper
  let z : ℂ := (c.chart p).symm w
  have hwt : w ∈ (c.chart p).target := ray_point_target c hε hεR hp upper ⟨hr.1.le, hr.2.le⟩
  have hzs : z ∈ (c.chart p).source := (c.chart p).map_target hwt
  have hmodel : w ∈ frontier (sector (c.angle p)) \ frontier (roundedSector ε (c.angle p)) := by
    rw [removed_sector_frontier_eq_open_shortRays hε (c.angle_bounds p hp).1 (c.angle_bounds p hp).2]
    have hrad : ε * r ∈ Ico (0 : ℝ) ε :=
      ⟨mul_nonneg hε.le hr.1.le, by nlinarith [hr.2]⟩
    cases upper
    · exact Or.inl ⟨ε * r, hrad, by simp [w, rayDirection]⟩
    · exact Or.inr ⟨ε * r, hrad, by simp [w, rayDirection, Complex.real_smul]⟩
  have hside := chart_surgery_isImage c.chart c.angle ε c.side c.disjoint
    (fun q hq => chart_tip_subset_target c hε hεR hq)
  have hzU : z ∈ frontier U := ((c.side p hp).frontier hzs).mp
    (by simpa only [z, (c.chart p).right_inv hwt] using hmodel.1)
  have hzV : z ∉ frontier (surgeryDomain c ε) := by
    intro h
    exact hmodel.2 (by simpa only [z, (c.chart p).right_inv hwt] using (hside p hp).frontier hzs |>.mpr h)
  obtain ⟨i, t, ht, htz⟩ : ∃ i t, t ∈ Icc (start i) (stop i) ∧
      arcParam (center i) (radius i) t = z := by
    rw [hboundary.2.2.1] at hzU
    obtain ⟨i, t, ht, he⟩ := mem_iUnion.mp hzU
    exact ⟨i, t, ht, he⟩
  have htcover : t ∈ ⋃ j : Fin (s i).k,
      Icc ((s i).node j.castSucc) ((s i).node j.succ) := by
    rw [(s i).closed_cover (hboundary.1 i).2.1]
    exact ht
  obtain ⟨j, htj⟩ := mem_iUnion.mp htcover
  have hj : (s i).retained j = false := by
    cases he : (s i).retained j
    · rfl
    · exact False.elim (hzV (hret i j he ⟨t, htj, htz⟩))
  let D := d i j hj
  have hφ : D.scalar t ∈ Icc D.lo D.hi := by
    rw [← D.image_interval]
    exact ⟨t, htj, rfl⟩
  have hφ01 : D.scalar t ∈ Icc (0 : ℝ) 1 :=
    ⟨D.lo_nonneg.trans hφ.1, hφ.2.trans D.hi_le_one⟩
  have hqtarget := ray_point_target c hε hεR D.corner_mem D.upper hφ01
  have hzq : z ∈ (c.chart D.corner).source := by
    rw [← htz, D.curve_eq t htj]
    exact (c.chart D.corner).map_target hqtarget
  have hqp : D.corner = p := by
    by_contra hne
    exact Set.disjoint_left.mp (c.disjoint D.corner D.corner_mem p hp hne) hzq hzs
  have hcoord : (ε * D.scalar t) • rayDirection (c.angle p) D.upper =
      (ε * r) • rayDirection (c.angle p) upper := by
    have he := congrArg (c.chart p) (D.curve_eq t htj)
    rw [htz] at he
    change c.chart p ((c.chart p).symm w) = _ at he
    rw [(c.chart p).right_inv hwt, hqp] at he
    rw [(c.chart p).right_inv (hqp ▸ hqtarget)] at he
    exact he.symm
  have hscalar : D.scalar t = r := by
    have hn := congrArg norm hcoord
    simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hε.le hφ01.1),
      abs_of_nonneg (mul_nonneg hε.le hr.1.le), rayDirection_norm, mul_one] at hn
    exact mul_left_cancel₀ hε.ne' hn
  have hupper : D.upper = upper := fixed_ray_direction_eq_of_positive_smul_eq
    (c.angle_bounds p hp).1 (c.angle_bounds p hp).2
    (by rw [hscalar]; exact mul_pos hε hr.1) (mul_pos hε hr.1) hcoord
  exact ⟨i, j, hj, hqp, hupper, hscalar ▸ hφ⟩

lemma Subdivision.open_interval_subset {a b : ℝ} (s : Subdivision a b) (j : Fin s.k) :
    Ioo (s.node j.castSucc) (s.node j.succ) ⊆ Ioo a b := by
  intro t ht
  have hleft := s.strict.monotone (Fin.zero_le j.castSucc)
  have hright := s.strict.monotone (Fin.le_last j.succ)
  rw [s.first] at hleft
  rw [s.last] at hright
  exact ⟨hleft.trans_lt ht.1, ht.2.trans_le hright⟩

lemma Subdivision.open_interval_index_unique {a b : ℝ} (s : Subdivision a b)
    {j j' : Fin s.k} {t : ℝ}
    (ht : t ∈ Ioo (s.node j.castSucc) (s.node j.succ))
    (ht' : t ∈ Ioo (s.node j'.castSucc) (s.node j'.succ)) : j = j' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hj | hj
  · have hle : j.succ ≤ j'.castSucc := by
      change j.val + 1 ≤ j'.val
      have hh : j.val < j'.val := hj
      omega
    have hn := s.strict.monotone hle
    exact (not_lt_of_ge (ht.2.le.trans hn)) ht'.1
  · have hle : j'.succ ≤ j.castSucc := by
      change j'.val + 1 ≤ j.val
      have hh : j'.val < j.val := hj
      omega
    have hn := s.strict.monotone hle
    exact (not_lt_of_ge (ht'.2.le.trans hn)) ht.1

lemma deleted_radial_intervals_disjoint {U : Set ℂ} {J : Finset ℂ}
    (c : UniformCharts U J) {ε : ℝ} {n : ℕ}
    {center : Fin n → ℂ} {radius start stop sign : Fin n → ℝ}
    (H : BoundaryHypotheses U n center radius start stop sign)
    (s : ∀ i, Subdivision (start i) (stop i))
    (d : ∀ i (j : Fin (s i).k), (s i).retained j = false →
      RayChange c ε (center i) (radius i) ((s i).node j.castSucc) ((s i).node j.succ))
    {i i' : Fin n} {j : Fin (s i).k} {j' : Fin (s i').k}
    (h : (s i).retained j = false) (h' : (s i').retained j' = false)
    (hne : (i, j.val) ≠ (i', j'.val))
    (hcorner : (d i j h).corner = (d i' j' h').corner)
    (hupper : (d i j h).upper = (d i' j' h').upper) :
    Disjoint (Ioo (d i j h).lo (d i j h).hi)
      (Ioo (d i' j' h').lo (d i' j' h').hi) := by
  apply Set.disjoint_left.mpr
  intro r hr hr'
  obtain ⟨t, ht, he⟩ := (d i j h).exists_open_preimage hr
  obtain ⟨t', ht', he'⟩ := (d i' j' h').exists_open_preimage hr'
  have hcurve : arcParam (center i) (radius i) t = arcParam (center i') (radius i') t' := by
    rw [(d i j h).curve_eq t ⟨ht.1.le, ht.2.le⟩,
      (d i' j' h').curve_eq t' ⟨ht'.1.le, ht'.2.le⟩, he, he', hcorner, hupper]
  have htI := (s i).open_interval_subset j ht
  have htI' := (s i').open_interval_subset j' ht'
  by_cases hii' : i = i'
  · subst i'
    have htt' := H.2.2.2.2.1 i htI htI' hcurve
    have hjj' := (s i).open_interval_index_unique ht (htt'.symm ▸ ht')
    apply hne
    simp only [hjj']
  · exact Set.disjoint_left.mp (H.2.2.2.1 i i' hii')
      ⟨t, htI, rfl⟩ ⟨t', htI', hcurve.symm⟩


/-- Closed radial intervals cover both endpoints as well: the finite union of
the actual closed target intervals is closed and already contains (0,1). -/
theorem deleted_radial_closed_cover {U : Set ℂ} {J : Finset ℂ}
    (c : UniformCharts U J) {ε : ℝ} (hε : 0 < ε) (hεR : ε < c.R)
    {n : ℕ} {center : Fin n → ℂ} {radius start stop sign : Fin n → ℝ}
    (hboundary : BoundaryHypotheses U n center radius start stop sign)
    (s : ∀ i, Subdivision (start i) (stop i))
    (hret : ∀ i (j : Fin (s i).k), (s i).retained j = true →
      arcParam (center i) (radius i) '' Icc ((s i).node j.castSucc) ((s i).node j.succ) ⊆
        frontier (surgeryDomain c ε))
    (d : ∀ i (j : Fin (s i).k), (s i).retained j = false →
      RayChange c ε (center i) (radius i) ((s i).node j.castSucc) ((s i).node j.succ))
    (p : ℂ) (hp : p ∈ J) (upper : Bool) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    ∃ (i : Fin n) (j : Fin (s i).k) (h : (s i).retained j = false),
      (d i j h).corner = p ∧ (d i j h).upper = upper ∧
      r ∈ Icc (d i j h).lo (d i j h).hi := by
  classical
  let DIndex := {x : (Σ i : Fin n, Fin (s i).k) // (s x.1).retained x.2 = false}
  let F : DIndex → Set ℝ := fun x =>
    if (d x.1.1 x.1.2 x.2).corner = p ∧ (d x.1.1 x.1.2 x.2).upper = upper then
      Icc (d x.1.1 x.1.2 x.2).lo (d x.1.1 x.1.2 x.2).hi else ∅
  have hF : ∀ x, IsClosed (F x) := by
    intro x
    dsimp [F]
    split_ifs
    · exact isClosed_Icc
    · exact isClosed_empty
  have hclosed : IsClosed (⋃ x, F x) := isClosed_iUnion_of_finite hF
  have hinside : Ioo (0 : ℝ) 1 ⊆ ⋃ x, F x := by
    intro u hu
    obtain ⟨i, j, h, hcorner, hupper, hmem⟩ :=
      deleted_radial_interior_cover c hε hεR hboundary s hret d p hp upper hu
    refine mem_iUnion.mpr ⟨⟨⟨i, j⟩, h⟩, ?_⟩
    simpa only [F, hcorner, hupper, and_self, ↓reduceIte] using hmem
  have hcover : Icc (0 : ℝ) 1 ⊆ ⋃ x, F x := by
    simpa only [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] using closure_minimal hinside hclosed
  obtain ⟨x, hx⟩ := mem_iUnion.mp (hcover hr)
  dsimp [F] at hx
  split_ifs at hx with htag
  · exact ⟨x.1.1, x.1.2, x.2, htag.1, htag.2, hx⟩
  · exact False.elim hx

-- BEGIN NEW GEOMETRIC CUT ASSEMBLY.

/-- The directly constructed geometric cut data, prior to global cover and radial
partition assembly. -/
structure GeometricCutsAt {U : Set ℂ} {J : Finset ℂ} (c : UniformCharts U J)
    (n : ℕ) (center : Fin n → ℂ) (radius start stop sign : Fin n → ℝ) (ε : ℝ) where
  cuts : ∀ i, Subdivision (start i) (stop i)
  retained_closed : ∀ i (j : Fin (cuts i).k), (cuts i).retained j = true →
    arcParam (center i) (radius i) ''
      Icc ((cuts i).node j.castSucc) ((cuts i).node j.succ) ⊆ frontier (surgeryDomain c ε)
  open_classification : ∀ i (j : Fin (cuts i).k),
    ∀ t ∈ Ioo ((cuts i).node j.castSucc) ((cuts i).node j.succ),
      arcParam (center i) (radius i) t ∈ frontier (surgeryDomain c ε) ↔
        (cuts i).retained j = true
  retained_side : ∀ i (j : Fin (cuts i).k), (cuts i).retained j = true →
    ∀ t ∈ Ioo ((cuts i).node j.castSucc) ((cuts i).node j.succ), ∃ W : Set ℂ,
      IsOpen W ∧ arcParam (center i) (radius i) t ∈ W ∧
      U ∩ W = surgeryDomain c ε ∩ W ∧
      ∀ z ∈ W, z ∈ surgeryDomain c ε ↔
        sign i * (‖z - center i‖ ^ 2 - radius i ^ 2) < 0
  deleted : ∀ i (j : Fin (cuts i).k), (cuts i).retained j = false →
    RayChange c ε (center i) (radius i) ((cuts i).node j.castSucc) ((cuts i).node j.succ)
  corner_cuts : ∀ i, ∀ t ∈ Icc (start i) (stop i),
    arcParam (center i) (radius i) t ∈ J → t ∈ Set.range (cuts i).node
  open_avoids_corners : ∀ i (j : Fin (cuts i).k),
    ∀ t ∈ Ioo ((cuts i).node j.castSucc) ((cuts i).node j.succ),
      arcParam (center i) (radius i) t ∉ J
  open_avoids_cutoffs : ∀ i (j : Fin (cuts i).k),
    ∀ t ∈ Ioo ((cuts i).node j.castSucc) ((cuts i).node j.succ),
      arcParam (center i) (radius i) t ∉ ⋃ p ∈ J,
        {(c.chart p).symm (ε : ℂ),
          (c.chart p).symm ((ε : ℂ) * Complex.exp ((c.angle p : ℂ) * Complex.I))}

/-- Classify every supplied circle and construct all genuine deleted ray changes. -/
theorem exists_geometric_cuts {U : Set ℂ} {J : Finset ℂ} (c : UniformCharts U J)
    {n : ℕ} {center : Fin n → ℂ} {radius start stop sign : Fin n → ℝ}
    (h : BoundaryHypotheses U n center radius start stop sign)
    {ε : ℝ} (hε : 0 < ε) (hεR : ε < c.R) :
    Nonempty (GeometricCutsAt c n center radius start stop sign ε) := by
  classical
  obtain ⟨hr, hsign, hcover, hdisjoint, hinj, hside⟩ := h
  let K : Set ℂ := ⋃ p ∈ J, (c.chart p).symm '' sectorTip ε (c.angle p)
  let E : Set ℂ := ⋃ p ∈ J, {(c.chart p).symm (ε : ℂ),
    (c.chart p).symm ((ε : ℂ) * Complex.exp ((c.angle p : ℂ) * Complex.I))}
  let M : Set ℂ := (↑J : Set ℂ) ∪ E
  have hE : E.Finite := J.finite_toSet.biUnion (fun p _ => Set.toFinite _)
  have hM : M.Finite := J.finite_toSet.union hE
  have htip : ∀ p ∈ J, sectorTip ε (c.angle p) ⊆ (c.chart p).target :=
    fun p hp => chart_tip_subset_target c hε hεR hp
  have hK : IsClosed K := (J.isCompact_biUnion fun p hp =>
    (isCompact_sectorTip ε (c.angle p)).image_of_continuousOn
      ((c.chart p).symm.continuousOn.mono (htip p hp))).isClosed
  have hremoved : frontier U \ frontier (surgeryDomain c ε) ⊆ K :=
    (closed_removal_locality (U := U) hK).2.1
  have hcut : (frontier U ∩ frontier (surgeryDomain c ε)) ∩ K ⊆ M := by
    rw [surgery_common_frontier_inter_tips_eq_cutoffs c hε hεR]
    exact subset_union_right
  have hfront : ∀ i, arcParam (center i) (radius i) '' Icc (start i) (stop i) ⊆ frontier U := by
    intro i
    rw [hcover]
    intro z hz
    exact mem_iUnion.mpr ⟨i, hz⟩
  have hγ : ∀ i, Continuous (arcParam (center i) (radius i)) := by
    intro i
    unfold arcParam
    fun_prop
  have hs : ∀ i, ∃ s : Subdivision (start i) (stop i),
      (∀ t ∈ Icc (start i) (stop i), arcParam (center i) (radius i) t ∈ M →
        t ∈ range s.node) ∧
      (∀ j : Fin s.k, ∀ t ∈ Ioo (s.node j.castSucc) (s.node j.succ),
        arcParam (center i) (radius i) t ∈ frontier (surgeryDomain c ε) ↔ s.retained j = true) ∧
      (∀ j : Fin s.k, s.retained j = true →
        arcParam (center i) (radius i) '' Icc (s.node j.castSucc) (s.node j.succ) ⊆
          frontier (surgeryDomain c ε)) ∧
      (∀ j : Fin s.k, s.retained j = true →
        ∀ t ∈ Ioo (s.node j.castSucc) (s.node j.succ), arcParam (center i) (radius i) t ∉ K) ∧
      (∀ j : Fin s.k, ∀ t ∈ Ioo (s.node j.castSucc) (s.node j.succ),
        arcParam (center i) (radius i) t ∉ M) := by
    intro i
    exact exists_status_subdivision (hγ i) (hr i).2.1 (hinj i) hM (hfront i)
      isClosed_frontier hK hremoved hcut
  choose s hsmarks hsclass hsclosed hsoutside hsavoid using hs
  have hbounds : ∀ i (j : Fin (s i).k),
      Icc ((s i).node j.castSucc) ((s i).node j.succ) ⊆ Icc (start i) (stop i) := by
    intro i j t ht
    constructor
    · exact ((s i).first.ge.trans ((s i).strict.monotone (Fin.zero_le _))).trans ht.1
    · exact ht.2.trans (((s i).strict.monotone (Fin.le_last _)).trans (s i).last.le)
  have hbounds_open : ∀ i (j : Fin (s i).k),
      Ioo ((s i).node j.castSucc) ((s i).node j.succ) ⊆ Ioo (start i) (stop i) := by
    intro i j t ht
    constructor
    · have ha : start i ≤ (s i).node j.castSucc := by
        exact (s i).first.ge.trans ((s i).strict.monotone (Fin.zero_le _))
      exact ha.trans_lt ht.1
    · have hb : (s i).node j.succ ≤ stop i := by
        exact ((s i).strict.monotone (Fin.le_last _)).trans (s i).last.le
      exact ht.2.trans_le hb
  have hdeleted : ∀ i (j : Fin (s i).k), (s i).retained j = false →
      Nonempty (RayChange c ε (center i) (radius i)
        ((s i).node j.castSucc) ((s i).node j.succ)) := by
    intro i j hj
    have hjlt : (s i).node j.castSucc < (s i).node j.succ :=
      (s i).strict (show j.castSucc < j.succ from Fin.castSucc_lt_succ)
    have hdel : ∀ t ∈ Ioo ((s i).node j.castSucc) ((s i).node j.succ),
        arcParam (center i) (radius i) t ∈ frontier U \ frontier (surgeryDomain c ε) := by
      intro t ht
      refine ⟨hfront i (mem_image_of_mem _ (hbounds i j ⟨ht.1.le, ht.2.le⟩)), ?_⟩
      intro hb
      have := (hsclass i j t ht).mp hb
      simp [hj] at this
    have havoidJ : ∀ t ∈ Ioo ((s i).node j.castSucc) ((s i).node j.succ),
        arcParam (center i) (radius i) t ∉ J :=
      fun t ht hmem => hsavoid i j t ht (Or.inl hmem)
    obtain ⟨p, hp, upper, hclosed⟩ := deleted_interval_fixed_closed_ray c hε hεR (hγ i) hjlt hdel havoidJ
    obtain ⟨d, _, _⟩ := ray_change_of_closed_radial_piece c hε p hp upper (center i)
      (hr i).1 hjlt (fun t ht => (hclosed t ht).1) (fun t ht => (hclosed t ht).2)
    exact ⟨d⟩
  refine ⟨{
    cuts := s
    retained_closed := hsclosed
    open_classification := hsclass
    retained_side := ?_
    deleted := fun i j hj => Classical.choice (hdeleted i j hj)
    corner_cuts := ?_
    open_avoids_corners := ?_
    open_avoids_cutoffs := ?_ }⟩
  · intro i j hj t ht
    obtain ⟨W₀, hW₀, htW₀, hsideW₀⟩ := hside i t (hbounds_open i j ht)
    exact retained_local_side hK (hsoutside i j hj t ht) hW₀ htW₀ hsideW₀
  · intro i t ht hmem
    exact hsmarks i t ht (Or.inl hmem)
  · intro i j t ht hmem
    exact hsavoid i j t ht (Or.inl hmem)
  · intro i j t ht hmem
    exact hsavoid i j t ht (Or.inr hmem)



lemma Subdivision.interval_subset {a b : ℝ} (s : Subdivision a b) (j : Fin s.k) :
    Icc (s.node j.castSucc) (s.node j.succ) ⊆ Icc a b := by
  intro t ht
  have hl := s.strict.monotone (Fin.zero_le j.castSucc)
  have hr := s.strict.monotone (Fin.le_last j.succ)
  rw [s.first] at hl
  rw [s.last] at hr
  exact ⟨hl.trans ht.1, ht.2.trans hr⟩

lemma Subdivision.exists_interval {a b t : ℝ} (hab : a < b)
    (s : Subdivision a b) (ht : t ∈ Icc a b) :
    ∃ j : Fin s.k, t ∈ Icc (s.node j.castSucc) (s.node j.succ) := by
  have hk : 0 < s.k := by
    by_contra hn
    have hk : s.k = 0 := Nat.eq_zero_of_not_pos hn
    have heq : (Fin.last s.k : Fin (s.k + 1)) = 0 := by apply Fin.ext; simp [hk]
    have hab' : a = b := s.first.symm.trans ((congrArg s.node heq.symm).trans s.last)
    exact hab.ne hab'
  have hc := iUnion_node_intervals hk s.node s.strict.monotone
  rw [s.first, s.last] at hc
  rw [← hc] at ht
  exact mem_iUnion.mp ht

lemma RayChange.closed_image_subset_tips {U : Set ℂ} {J : Finset ℂ} {c : UniformCharts U J}
    {ε : ℝ} (hε : 0 < ε) {center : ℂ} {radius a b : ℝ}
    (d : RayChange c ε center radius a b) :
    arcParam center radius '' Icc a b ⊆ ⋃ p ∈ J, (c.chart p).symm '' sectorTip ε (c.angle p) := by
  rintro z ⟨t, ht, rfl⟩
  have hscalar : d.scalar t ∈ Icc d.lo d.hi := by
    rw [← d.image_interval]
    exact mem_image_of_mem _ ht
  have h01 : d.scalar t ∈ Icc (0 : ℝ) 1 :=
    ⟨d.lo_nonneg.trans hscalar.1, hscalar.2.trans d.hi_le_one⟩
  rw [d.curve_eq t ht]
  apply mem_iUnion₂.mpr
  refine ⟨d.corner, d.corner_mem, (ε * d.scalar t) • rayDirection (c.angle d.corner) d.upper, ?_, rfl⟩
  apply shortRays_subset_sectorTip hε
  have hr : ε * d.scalar t ∈ Icc (0 : ℝ) ε :=
    ⟨mul_nonneg hε.le h01.1, (mul_le_mul_of_nonneg_left h01.2 hε.le).trans_eq (mul_one ε)⟩
  cases hu : d.upper
  · exact Or.inl ⟨ε * d.scalar t, hr, by simp [rayDirection, Complex.real_smul]⟩
  · exact Or.inr ⟨ε * d.scalar t, hr, by simp [rayDirection, Complex.real_smul]⟩

lemma retained_cover_outside_tips {U : Set ℂ} {J : Finset ℂ}
    (c : UniformCharts U J) {ε : ℝ} (hε : 0 < ε)
    {n : ℕ} {center : Fin n → ℂ} {radius start stop sign : Fin n → ℝ}
    (hb : BoundaryHypotheses U n center radius start stop sign)
    (s : ∀ i, Subdivision (start i) (stop i))
    (d : ∀ i (j : Fin (s i).k), (s i).retained j = false →
      RayChange c ε (center i) (radius i) ((s i).node j.castSucc) ((s i).node j.succ))
    {z : ℂ} (hz : z ∈ frontier U)
    (hzK : z ∉ ⋃ p ∈ J, (c.chart p).symm '' sectorTip ε (c.angle p)) :
    ∃ (i : Fin n) (j : Fin (s i).k), (s i).retained j = true ∧
      z ∈ arcParam (center i) (radius i) '' Icc ((s i).node j.castSucc) ((s i).node j.succ) := by
  obtain ⟨hr, hsign, hcover, hdisj, hinj, hside⟩ := hb
  rw [hcover] at hz
  obtain ⟨i, t, ht, rfl⟩ := mem_iUnion.mp hz
  obtain ⟨j, hj⟩ := (s i).exists_interval (hr i).2.1 ht
  by_cases hret : (s i).retained j = true
  · exact ⟨i, j, hret, t, hj, rfl⟩
  · have hdel : (s i).retained j = false := Bool.eq_false_of_not_eq_true hret
    exact (hzK ((d i j hdel).closed_image_subset_tips hε ⟨t, hj, rfl⟩)).elim

lemma frontier_cutoff_mem_closed_of_outside_tips {U : Set ℂ} {J : Finset ℂ}
    (c : UniformCharts U J) {ε : ℝ} (hε : 0 < ε) (hεR : ε < c.R)
    {A : Set ℂ} (hA : IsClosed A)
    (houtside : frontier U \ (⋃ p ∈ J, (c.chart p).symm '' sectorTip ε (c.angle p)) ⊆ A)
    {p : ℂ} (hp : p ∈ J) (upper : Bool) :
    (c.chart p).symm (ε • rayDirection (c.angle p) upper) ∈ A := by
  let ξ := rayDirection (c.angle p) upper
  have hξ : ‖ξ‖ = 1 := by
    cases upper <;> simp [ξ, rayDirection, Complex.norm_exp]
  have hnorm (r : ℝ) (hr : 0 ≤ r) : ‖r • ξ‖ = r := by
    rw [norm_smul, hξ, mul_one, Real.norm_eq_abs, abs_of_nonneg hr]
  have hmodel (r : ℝ) (hr : 0 ≤ r) : r • ξ ∈ frontier (sector (c.angle p)) := by
    cases upper
    · simpa [ξ, rayDirection, Complex.real_smul] using
        bottomRay_mem_frontier_sector (c.angle_bounds p hp).1 (c.angle_bounds p hp).2 hr
    · simpa [ξ, rayDirection, Complex.real_smul] using
        topRay_mem_frontier_sector (c.angle_bounds p hp).1 (c.angle_bounds p hp).2 hr
  have hεt : ε • ξ ∈ (c.chart p).target :=
    (c.target_bound p hp).1 (by simpa only [mem_closedBall_zero_iff, hnorm ε hε.le] using hεR.le)
  have hcont : ContinuousAt (fun r : ℝ => (c.chart p).symm (r • ξ)) ε :=
    by simpa only [Function.comp_def] using
      ((c.chart p).symm.continuousAt hεt).comp (f := fun r : ℝ => r • ξ) (x := ε)
        (by fun_prop : ContinuousAt (fun r : ℝ => r • ξ) ε)
  have hevent : ∀ᶠ r in 𝓝[>] ε, (c.chart p).symm (r • ξ) ∈ A := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hεR)] with r hr hrR
    have hr0 : 0 < r := hε.trans hr
    have hrt : r • ξ ∈ (c.chart p).target :=
      (c.target_bound p hp).1 (by simpa only [mem_closedBall_zero_iff, hnorm r hr0.le] using hrR.le)
    have hys := (c.chart p).map_target hrt
    apply houtside
    constructor
    · apply ((c.side p hp).frontier hys).mp
      rw [(c.chart p).right_inv hrt]
      exact hmodel r hr0.le
    · intro hyK
      obtain ⟨q, hq, w, hw, hyw⟩ := mem_iUnion₂.mp hyK
      have hwt := chart_tip_subset_target c hε hεR hq hw
      have hqs : (c.chart p).symm (r • ξ) ∈ (c.chart q).source :=
        hyw ▸ (c.chart q).map_target hwt
      have hqp : q = p := by
        by_contra hne
        exact Set.disjoint_left.mp (c.disjoint p hp q hq (Ne.symm hne)) hys hqs
      subst q
      have hwr : w = r • ξ := by
        have he := congrArg (c.chart p) hyw
        simpa only [(c.chart p).right_inv hwt, (c.chart p).right_inv hrt] using he
      have hwε := sectorTip_subset_closedBall hε hw
      rw [mem_closedBall_zero_iff, hwr, hnorm r hr0.le] at hwε
      exact (not_le_of_gt hr) hwε
  exact hA.mem_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds) hevent

/-- Retained closed pieces cover the entire common frontier, including the
cutoff endpoints. The hypotheses supply only retained inclusion and genuine
deleted ray changes; no classification or retained-cover certificate is used. -/
theorem retained_cover_of_closed_and_ray_changes {U : Set ℂ} {J : Finset ℂ}
    (c : UniformCharts U J) {ε : ℝ} (hε : 0 < ε) (hεR : ε < c.R)
    {n : ℕ} {center : Fin n → ℂ} {radius start stop sign : Fin n → ℝ}
    (hb : BoundaryHypotheses U n center radius start stop sign)
    (s : ∀ i, Subdivision (start i) (stop i))
    (hretclosed : ∀ i (j : Fin (s i).k), (s i).retained j = true →
      arcParam (center i) (radius i) '' Icc ((s i).node j.castSucc) ((s i).node j.succ) ⊆
        frontier (surgeryDomain c ε))
    (d : ∀ i (j : Fin (s i).k), (s i).retained j = false →
      RayChange c ε (center i) (radius i) ((s i).node j.castSucc) ((s i).node j.succ)) :
    ∀ z : ℂ, z ∈ frontier U ∩ frontier (surgeryDomain c ε) ↔
      ∃ (i : Fin n) (j : Fin (s i).k), (s i).retained j = true ∧
        z ∈ arcParam (center i) (radius i) ''
          Icc ((s i).node j.castSucc) ((s i).node j.succ) := by
  classical
  let A : Set ℂ := ⋃ i, ⋃ j : Fin (s i).k,
    if (s i).retained j then
      arcParam (center i) (radius i) '' Icc ((s i).node j.castSucc) ((s i).node j.succ)
    else ∅
  have hAmem (z : ℂ) : z ∈ A ↔
      ∃ (i : Fin n) (j : Fin (s i).k), (s i).retained j = true ∧
        z ∈ arcParam (center i) (radius i) ''
          Icc ((s i).node j.castSucc) ((s i).node j.succ) := by
    simp only [A, mem_iUnion]
    constructor
    · rintro ⟨i, j, hz⟩
      cases hret : (s i).retained j
      · simp [hret] at hz
      · exact ⟨i, j, hret, by simpa [hret] using hz⟩
    · rintro ⟨i, j, hret, hz⟩
      exact ⟨i, j, by simpa [hret] using hz⟩
  have hA : IsClosed A := by
    apply isClosed_iUnion_of_finite
    intro i
    apply isClosed_iUnion_of_finite
    intro j
    split_ifs
    · have hcont : Continuous (arcParam (center i) (radius i)) := by
        unfold arcParam
        fun_prop
      exact (isCompact_Icc.image hcont).isClosed
    · exact isClosed_empty
  have houtside : frontier U \ (⋃ p ∈ J, (c.chart p).symm '' sectorTip ε (c.angle p)) ⊆ A := by
    intro z hz
    rw [hAmem]
    exact retained_cover_outside_tips c hε hb s d hz.1 hz.2
  intro z
  rw [← hAmem z]
  constructor
  · intro hz
    by_cases hzK : z ∈ ⋃ p ∈ J, (c.chart p).symm '' sectorTip ε (c.angle p)
    · have hzcut : z ∈ ⋃ p ∈ J, {(c.chart p).symm (ε : ℂ),
          (c.chart p).symm ((ε : ℂ) * Complex.exp ((c.angle p : ℂ) * I))} := by
        rw [← surgery_common_frontier_inter_tips_eq_cutoffs c hε hεR]
        exact ⟨hz, hzK⟩
      obtain ⟨p, hp, hzcut⟩ := mem_iUnion₂.mp hzcut
      rcases (show z = (c.chart p).symm (ε : ℂ) ∨
        z = (c.chart p).symm ((ε : ℂ) * Complex.exp ((c.angle p : ℂ) * I)) by
          simpa using hzcut) with rfl | rfl
      · simpa only [rayDirection, Bool.false_eq_true, ↓reduceIte, Complex.real_smul, mul_one]
          using frontier_cutoff_mem_closed_of_outside_tips c hε hεR hA houtside hp false
      · simpa only [rayDirection, ↓reduceIte, Complex.real_smul]
          using frontier_cutoff_mem_closed_of_outside_tips c hε hεR hA houtside hp true
    · exact houtside ⟨hz.1, hzK⟩
  · intro hz
    obtain ⟨i, j, hret, hz⟩ := (hAmem z).mp hz
    refine ⟨?_, hretclosed i j hret hz⟩
    have hz' : z ∈ arcParam (center i) (radius i) '' Icc (start i) (stop i) :=
      image_mono ((s i).interval_subset j) hz
    rw [hb.2.2.1]
    exact mem_iUnion.mpr ⟨i, hz'⟩


theorem deleted_total_length_le {U : Set ℂ} {J : Finset ℂ}
    (c : UniformCharts U J) {ε : ℝ} (hε : 0 < ε) (hεR : ε < c.R) {n : ℕ}
    {center : Fin n → ℂ} {radius start stop sign : Fin n → ℝ}
    (H : BoundaryHypotheses U n center radius start stop sign)
    (s : ∀ i, Subdivision (start i) (stop i))
    (d : ∀ i (j : Fin (s i).k), (s i).retained j = false →
      RayChange c ε (center i) (radius i) ((s i).node j.castSucc) ((s i).node j.succ)) :
    (∑ i, ∑ j : Fin (s i).k, if (s i).retained j then 0 else
      radius i * ((s i).node j.succ - (s i).node j.castSucc)) ≤
      (2 * J.card * (c.L : ℝ)) * ε := by
  classical
  let A := Σ i : Fin n, Fin (s i).k
  let P : A → Prop := fun x => (s x.1).retained x.2 = false
  let DIndex := {x : A // P x}
  let weight : A → ℝ := fun x =>
    radius x.1 * ((s x.1).node x.2.succ - (s x.1).node x.2.castSucc)
  have htag : Function.Injective (fun x : A => (x.1, x.2.val)) := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ hh
    have hi := congrArg Prod.fst hh
    dsimp at hi
    subst i'
    have hj := congrArg Prod.snd hh
    dsimp at hj
    exact congrArg (Sigma.mk i) (Fin.ext hj)
  have hdisj : ∀ x y : DIndex, x ≠ y →
      (d x.1.1 x.1.2 x.2).corner = (d y.1.1 y.1.2 y.2).corner →
      (d x.1.1 x.1.2 x.2).upper = (d y.1.1 y.1.2 y.2).upper →
      Disjoint (Ioo (d x.1.1 x.1.2 x.2).lo (d x.1.1 x.1.2 x.2).hi)
        (Ioo (d y.1.1 y.1.2 y.2).lo (d y.1.1 y.1.2 y.2).hi) := by
    intro x y hxy hp hu
    apply deleted_radial_intervals_disjoint c H s d x.2 y.2 ?_ hp hu
    intro he
    exact hxy (Subtype.ext (htag he))
  have hbound := deleted_family_length_le c hε hεR
    (fun x : DIndex => center x.1.1) (fun x => radius x.1.1)
    (fun x => (s x.1.1).node x.1.2.castSucc)
    (fun x => (s x.1.1).node x.1.2.succ)
    (fun x => (H.1 x.1.1).1)
    (fun x => (s x.1.1).strict (show x.1.2.castSucc < x.1.2.succ from Fin.castSucc_lt_succ))
    (fun x => d x.1.1 x.1.2 x.2) hdisj
  have hsum : (∑ x : DIndex, weight x.1) = ∑ x : A, if P x then weight x else 0 := by
    rw [← Finset.sum_subtype (Finset.univ.filter P) (by simp) weight]
    exact Finset.sum_filter P weight
  calc
    _ = ∑ x : A, if P x then weight x else 0 := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hret : (s i).retained j = true
      · simp [P, weight, hret]
      · have hfalse := Bool.eq_false_of_not_eq_true hret
        simp [P, weight, hfalse]
    _ = ∑ x : DIndex, weight x.1 := hsum.symm
    _ ≤ (2 * J.card * (c.L : ℝ)) * ε := hbound

/-- The full angular-cut construction for the literal surgery, with constants
independent of the scale and of the number of subdivision intervals. -/
theorem circular_angular_cuts :
    Specs.D12Complex.Ch14.CircularAngularCuts.circular_angular_cuts_type := by
  classical
  intro U J hgeom n center radius start stop sign hb
  let K : Finset ℂ :=
    Finset.univ.image (fun i => arcParam (center i) (radius i) (start i)) ∪
    Finset.univ.image (fun i => arcParam (center i) (radius i) (stop i))
  obtain ⟨c, havoid⟩ := exists_uniform_charts_avoiding U J K hgeom
  refine ⟨c, c.R, 2 * J.card * (c.L : ℝ) + 1, c.radius_pos, le_rfl, ?_, ?_, ?_⟩
  · positivity
  · intro p hp i q hq hqp
    apply havoid p hp q _ hqp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
  · intro ε hε hεR
    obtain ⟨g⟩ := exists_geometric_cuts c hb hε hεR
    refine ⟨{
      cuts := g.cuts
      retained_closed := g.retained_closed
      retained_cover := retained_cover_of_closed_and_ray_changes c hε hεR hb g.cuts
        g.retained_closed g.deleted
      open_classification := g.open_classification
      retained_side := g.retained_side
      deleted := g.deleted
      radial_cover := fun p hp upper r hr => deleted_radial_closed_cover c hε hεR hb
        g.cuts g.retained_closed g.deleted p hp upper hr
      radial_disjoint := fun i j h i' j' h' hne hcorner hupper =>
        deleted_radial_intervals_disjoint c hb g.cuts g.deleted h h' hne hcorner hupper
      corner_cuts := g.corner_cuts
      deleted_length := ?_ }⟩
    exact (deleted_total_length_le c hε hεR hb g.cuts g.deleted).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)) hε.le)

end D12Complex.CircularAngularCuts
