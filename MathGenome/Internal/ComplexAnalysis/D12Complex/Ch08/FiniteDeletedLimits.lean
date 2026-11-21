import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch08.FiniteDeletedLimits
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Tactic.Choose
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open Set Filter MeasureTheory
open scoped Topology

namespace D12Complex.FiniteDeletedLimits

lemma deleted_integrable (s : Finset ℝ) (l u : ℝ) (f : ℝ → ℂ)
    (hf : ContinuousOn f (Icc l u \ (s : Set ℝ)))
    (ε : s → ℝ) (hε : ∀ a, 0 < ε a) :
    IntegrableOn f (Icc l u \ ⋃ a : s, Ioo (a.val - ε a) (a.val + ε a)) := by
  have hsub : (Icc l u \ ⋃ a : s, Ioo (a.val - ε a) (a.val + ε a)) ⊆
      Icc l u \ (s : Set ℝ) := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    intro hxs
    exact hx.2 (mem_iUnion.mpr ⟨⟨x, hxs⟩, by
      constructor <;> dsimp <;> linarith [hε ⟨x, hxs⟩]⟩)
  exact ContinuousOn.integrableOn_compact
    (isCompact_Icc.diff (isOpen_iUnion fun _ => isOpen_Ioo)) (hf.mono hsub)

/-- Cancellation uses actual integrals on the two retained real intervals. -/
lemma symmetric_principal_part_cancel (a r ε : ℝ) (A : ℂ) :
    (∫ x in (a-r)..(a-ε), A / ((x : ℂ) - (a : ℂ))) +
    (∫ x in (a+ε)..(a+r), A / ((x : ℂ) - (a : ℂ))) = 0 := by
  let k : ℝ → ℂ := fun x => A / (x : ℂ)
  have hleft : (∫ x in (a-r)..(a-ε), A / ((x : ℂ) - (a : ℂ))) =
      ∫ x in (-r)..(-ε), k x := by
    simpa [k, Complex.ofReal_add, add_sub_cancel_right, sub_eq_add_neg, add_comm,
      add_left_comm, add_assoc] using
      (intervalIntegral.integral_comp_add_right
        (fun x : ℝ => A / ((x : ℂ) - (a : ℂ))) a (a := -r) (b := -ε)).symm
  have hright : (∫ x in (a+ε)..(a+r), A / ((x : ℂ) - (a : ℂ))) =
      ∫ x in ε..r, k x := by
    simpa [k, Complex.ofReal_add, add_sub_cancel_right, add_comm] using
      (intervalIntegral.integral_comp_add_right
        (fun x : ℝ => A / ((x : ℂ) - (a : ℂ))) a (a := ε) (b := r)).symm
  rw [hleft, hright]
  have hn : (∫ x in (-r)..(-ε), k x) = -(∫ x in ε..r, k x) := by
    calc
      _ = ∫ x in ε..r, k (-x) := by
        simp only [intervalIntegral.integral_comp_neg]
      _ = ∫ x in ε..r, -(k x) := by
        apply intervalIntegral.integral_congr
        intro x _
        simp [k, div_neg]
      _ = _ := intervalIntegral.integral_neg
  rw [hn, neg_add_cancel]


lemma continuous_principal_part_on (a : ℝ) (A : ℂ) (t : Set ℝ)
    (ht : ∀ x ∈ t, x ≠ a) :
    ContinuousOn (fun x : ℝ => A / ((x : ℂ) - (a : ℂ))) t := by
  apply continuousOn_const.div (Complex.continuous_ofReal.continuousOn.sub continuousOn_const)
  intro x hx
  exact sub_ne_zero.mpr (by
    change (x : ℂ) ≠ (a : ℂ)
    exact_mod_cast ht x hx)

lemma local_shell_integral (a r ε : ℝ) (A : ℂ) (h f : ℝ → ℂ)
    (hε : 0 < ε) (hεr : ε ≤ r)
    (hh : ContinuousOn h (Icc (a-r) (a+r)))
    (heq : ∀ x ∈ Icc (a-r) (a+r), x ≠ a →
      f x = A / ((x : ℂ) - (a : ℂ)) + h x) :
    (∫ x in Icc (a-r) (a+r) \ Ioo (a-ε) (a+ε), f x) =
      (∫ x in (a-r)..(a-ε), h x) + (∫ x in (a+ε)..(a+r), h x) := by
  have hl : a-r ≤ a-ε := by linarith
  have hr : a+ε ≤ a+r := by linarith
  have hsubL : Icc (a-r) (a-ε) ⊆ Icc (a-r) (a+r) := by
    intro x hx; constructor <;> linarith [hx.1, hx.2]
  have hsubR : Icc (a+ε) (a+r) ⊆ Icc (a-r) (a+r) := by
    intro x hx; constructor <;> linarith [hx.1, hx.2]
  have hnL : ∀ x ∈ Icc (a-r) (a-ε), x ≠ a := by
    intro x hx; linarith [hx.2]
  have hnR : ∀ x ∈ Icc (a+ε) (a+r), x ≠ a := by
    intro x hx; linarith [hx.1]
  have hcL := (continuous_principal_part_on a A _ hnL).add (hh.mono hsubL)
  have hcR := (continuous_principal_part_on a A _ hnR).add (hh.mono hsubR)
  have hfL : ContinuousOn f (Icc (a-r) (a-ε)) :=
    hcL.congr (fun x hx => heq x (hsubL hx) (hnL x hx))
  have hfR : ContinuousOn f (Icc (a+ε) (a+r)) :=
    hcR.congr (fun x hx => heq x (hsubR hx) (hnR x hx))
  have hs : Icc (a-r) (a+r) \ Ioo (a-ε) (a+ε) =
      Icc (a-r) (a-ε) ∪ Icc (a+ε) (a+r) := by
    ext x
    simp only [Set.mem_sdiff, mem_Icc, mem_Ioo, mem_union]
    constructor
    · rintro ⟨hx, hn⟩
      by_cases hx' : x ≤ a-ε
      · exact Or.inl ⟨hx.1, hx'⟩
      · exact Or.inr ⟨by by_contra h; exact hn ⟨by linarith, by linarith⟩, hx.2⟩
    · rintro (hx | hx) <;> constructor
      · exact hsubL hx
      · intro hh; linarith [hx.2, hh.1]
      · exact hsubR hx
      · intro hh; linarith [hx.1, hh.2]
  have hd : Disjoint (Icc (a-r) (a-ε)) (Icc (a+ε) (a+r)) := by
    apply disjoint_left.mpr
    intro x hx hy
    linarith [hx.2, hy.1]
  rw [hs, setIntegral_union hd measurableSet_Icc hfL.integrableOn_Icc hfR.integrableOn_Icc,
    integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hl, ← intervalIntegral.integral_of_le hr]
  have hL : (∫ x in (a-r)..(a-ε), f x) =
      (∫ x in (a-r)..(a-ε), A / ((x : ℂ) - (a : ℂ))) +
      (∫ x in (a-r)..(a-ε), h x) := by
    rw [← intervalIntegral.integral_add
      ((continuous_principal_part_on a A _ hnL).intervalIntegrable_of_Icc hl)
      ((hh.mono hsubL).intervalIntegrable_of_Icc hl)]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hl] at hx
    exact heq x (hsubL hx) (hnL x hx)
  have hR : (∫ x in (a+ε)..(a+r), f x) =
      (∫ x in (a+ε)..(a+r), A / ((x : ℂ) - (a : ℂ))) +
      (∫ x in (a+ε)..(a+r), h x) := by
    rw [← intervalIntegral.integral_add
      ((continuous_principal_part_on a A _ hnR).intervalIntegrable_of_Icc hr)
      ((hh.mono hsubR).intervalIntegrable_of_Icc hr)]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hr] at hx
    exact heq x (hsubR hx) (hnR x hx)
  rw [hL, hR]
  have := symmetric_principal_part_cancel a r ε A
  linear_combination this

lemma local_shell_tendsto (a r : ℝ) (hr : 0 < r) (A : ℂ) (h f : ℝ → ℂ)
    (hh : ContinuousOn h (Icc (a-r) (a+r)))
    (heq : ∀ x ∈ Icc (a-r) (a+r), x ≠ a →
      f x = A / ((x : ℂ) - (a : ℂ)) + h x) :
    ∃ L : ℂ, Tendsto
      (fun ε : ℝ => ∫ x in Icc (a-r) (a+r) \ Ioo (a-ε) (a+ε), f x)
      (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  have hab : a-r ≤ a+r := by linarith
  let H : ℝ → ℂ := IccExtend hab (fun x => h x.val)
  have hH : Continuous H := continuous_IccExtend_iff.mpr
    hh.domRestrict
  have hEH : ∀ x ∈ Icc (a-r) (a+r), H x = h x := by
    intro x hx
    exact IccExtend_of_mem hab (fun x => h x.val) hx
  have hleft : Continuous (fun ε : ℝ => ∫ x in (a-r)..(a-ε), H x) :=
    (intervalIntegral.continuous_primitive (fun _ _ => hH.intervalIntegrable _ _) (a-r)).comp
      (continuous_const.sub continuous_id)
  have hright : Continuous (fun ε : ℝ => ∫ x in (a+ε)..(a+r), H x) := by
    have hc := (intervalIntegral.continuous_primitive (μ := volume) (fun _ _ => hH.intervalIntegrable _ _) (a+r)).neg
    convert hc.comp (continuous_const.add continuous_id) using 1
    funext ε
    exact intervalIntegral.integral_symm _ _
  refine ⟨_, ((hleft.add hright).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_⟩
  have hp : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have hb : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε < r :=
    hp.and ((eventually_lt_nhds hr).filter_mono nhdsWithin_le_nhds)
  filter_upwards [hb] with ε hε
  symm
  apply local_shell_integral a r ε A H f hε.1 hε.2.le hH.continuousOn
  intro x hx hxa
  rw [hEH x hx]
  exact heq x hx hxa


/-- A positive bound for any finite family; the empty family requires no special case. -/
lemma exists_positive_uniform_bound {ι : Type*} [Finite ι] (d : ι → ℝ)
    (hd : ∀ i, 0 < d i) : ∃ r : ℝ, 0 < r ∧ ∀ i, r < d i := by
  have h : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), ∀ i, r < d i :=
    eventually_all.mpr (fun i => (eventually_lt_nhds (hd i)).filter_mono nhdsWithin_le_nhds)
  have hp : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), 0 < r := self_mem_nhdsWithin
  exact (hp.and h).exists

lemma exists_disjoint_radius (s : Finset ℝ) (l u : ℝ)
    (hinside : ∀ a ∈ s, l < a ∧ a < u) (δ : s → ℝ) (hδ : ∀ a, 0 < δ a) :
    ∃ r : ℝ, 0 < r ∧ (∀ a : s, r < δ a) ∧
      (∀ a : s, Icc (a.val-r) (a.val+r) ⊆ Icc l u) ∧
      Pairwise (fun a b : s => Disjoint
        (Icc (a.val-r) (a.val+r)) (Icc (b.val-r) (b.val+r))) := by
  classical
  obtain ⟨r₁, hr₁, hb₁⟩ := exists_positive_uniform_bound
    (fun a : s => min (δ a) (min (a.val-l) (u-a.val))) (by
      intro a
      exact lt_min (hδ a) (lt_min (sub_pos.mpr (hinside a.val a.property).1)
        (sub_pos.mpr (hinside a.val a.property).2)))
  let d : s × s → ℝ := fun p => if p.1 = p.2 then 1 else |p.1.val-p.2.val| / 3
  have hd : ∀ p, 0 < d p := by
    intro ⟨a,b⟩
    dsimp [d]
    split_ifs with hab
    · norm_num
    · exact div_pos (abs_pos.mpr (sub_ne_zero.mpr (Subtype.coe_injective.ne hab))) (by norm_num)
  obtain ⟨r₂, hr₂, hb₂⟩ := exists_positive_uniform_bound d hd
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, ?_, ?_, ?_⟩
  · intro a
    exact (min_le_left _ _).trans_lt ((hb₁ a).trans_le (min_le_left _ _))
  · intro a x hx
    have hm := (hb₁ a).trans_le (min_le_right _ _)
    have hL := hm.trans_le (min_le_left _ _)
    have hU := hm.trans_le (min_le_right _ _)
    have hrr : min r₁ r₂ ≤ r₁ := min_le_left _ _
    constructor <;> linarith [hx.1, hx.2]
  · intro a b hab
    have hb : r₂ < |a.val-b.val| / 3 := by simpa [d, hab] using hb₂ (a,b)
    have hrr : min r₁ r₂ ≤ r₂ := min_le_right _ _
    apply disjoint_left.mpr
    intro x hx hy
    have : |a.val-b.val| ≤ 2 * min r₁ r₂ := by
      apply abs_le.mpr
      constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
    linarith

/-- Exact finite localization for nested deletions inside pairwise disjoint neighborhoods. -/
lemma deleted_set_partition {ι : Type*} (B : Set ℝ) (C N : ι → Set ℝ)
    (hCB : ∀ i, C i ⊆ B) (hNC : ∀ i, N i ⊆ C i)
    (hC : Pairwise (fun i j => Disjoint (C i) (C j))) :
    B \ ⋃ i, N i = (B \ ⋃ i, C i) ∪ ⋃ i, C i \ N i := by
  classical
  ext x
  constructor
  · intro hx
    by_cases hxc : x ∈ ⋃ i, C i
    · obtain ⟨i,hi⟩ := mem_iUnion.mp hxc
      exact Or.inr (mem_iUnion.mpr ⟨i, hi, fun hn => hx.2 (mem_iUnion.mpr ⟨i, hn⟩)⟩)
    · exact Or.inl ⟨hx.1, hxc⟩
  · rintro (hx | hx)
    · exact ⟨hx.1, fun hn => hx.2 (by
        obtain ⟨i,hi⟩ := mem_iUnion.mp hn
        exact mem_iUnion.mpr ⟨i, hNC i hi⟩)⟩
    · obtain ⟨i,hi,hni⟩ := mem_iUnion.mp hx
      refine ⟨hCB i hi, ?_⟩
      intro hn
      obtain ⟨j,hj⟩ := mem_iUnion.mp hn
      by_cases hij : i = j
      · subst j; exact hni hj
      · exact (disjoint_left.mp (hC hij) hi) (hNC j hj)

lemma integral_deleted_partition {ι : Type*} [Fintype ι] (B : Set ℝ) (C N : ι → Set ℝ)
    (f : ℝ → ℂ) (hCB : ∀ i, C i ⊆ B) (hNC : ∀ i, N i ⊆ C i)
    (hC : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hmC : ∀ i, MeasurableSet (C i)) (hmN : ∀ i, MeasurableSet (N i))
    (hf : IntegrableOn f (B \ ⋃ i, N i)) :
    (∫ x in B \ ⋃ i, N i, f x) =
      (∫ x in B \ ⋃ i, C i, f x) + ∑ i, ∫ x in C i \ N i, f x := by
  have hpart := deleted_set_partition B C N hCB hNC hC
  have hfi : ∀ i, IntegrableOn f (C i \ N i) := by
    intro i
    apply hf.mono_set
    rw [hpart]
    exact subset_union_of_subset_right (subset_iUnion (fun i => C i \ N i) i) _
  have hfr : IntegrableOn f (B \ ⋃ i, C i) := by
    apply hf.mono_set
    rw [hpart]
    exact subset_union_left
  have hd : Disjoint (B \ ⋃ i, C i) (⋃ i, C i \ N i) := by
    apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨i,hi⟩ := mem_iUnion.mp hy
    exact hx.2 (mem_iUnion.mpr ⟨i,hi.1⟩)
  have hdi : Pairwise (fun i j => Disjoint (C i \ N i) (C j \ N j)) := by
    intro i j hij
    exact (hC hij).mono sdiff_subset sdiff_subset
  have hm : ∀ i, MeasurableSet (C i \ N i) := fun i => (hmC i).diff (hmN i)
  rw [hpart, setIntegral_union hd (MeasurableSet.iUnion hm) hfr
    (integrableOn_finite_iUnion.mpr hfi), integral_iUnion_fintype hm hdi hfi]


/-- Finite localization of the local simple-principal-part decompositions. -/
theorem finite_deleted_limits : Spec.finite_deleted_limits := by
  classical
  intro s l u f _hlu hinside hf hlocal
  refine ⟨fun ε hε => deleted_integrable s l u f hf ε hε, ?_⟩
  choose δ A h hδ hh heq using (fun a : s => hlocal a.val a.property)
  obtain ⟨r,hr,hrδ,hCB,hC⟩ := exists_disjoint_radius s l u hinside δ hδ
  have hsub : ∀ a : s, Icc (a.val-r) (a.val+r) ⊆ Icc (a.val-δ a) (a.val+δ a) := by
    intro a x hx
    constructor <;> linarith [hx.1, hx.2, hrδ a]
  have hlocalLimits : ∀ a : s, ∃ L : ℂ, Tendsto
      (fun ε : ℝ => ∫ x in Icc (a.val-r) (a.val+r) \ Ioo (a.val-ε) (a.val+ε), f x)
      (𝓝[>] (0 : ℝ)) (𝓝 L) := by
    intro a
    exact local_shell_tendsto a.val r hr (A a) (h a) f ((hh a).mono (hsub a))
      (fun x hx hxa => heq a x (hsub a hx) hxa)
  choose L hL using hlocalLimits
  let C : s → Set ℝ := fun a => Icc (a.val-r) (a.val+r)
  let D : Set ℝ := Icc l u \ ⋃ a : s, C a
  have hsum : Tendsto
      (fun ε : s → ℝ => ∑ a : s, ∫ x in C a \ Ioo (a.val-ε a) (a.val+ε a), f x)
      (Filter.pi (fun _ : s => 𝓝[>] (0 : ℝ))) (𝓝 (∑ a : s, L a)) := by
    apply tendsto_finsetSum
    intro a _
    exact (hL a).comp (tendsto_eval_pi _ a)
  refine ⟨(∫ x in D, f x) + ∑ a : s, L a, (tendsto_const_nhds.add hsum).congr' ?_⟩
  have hp : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have hb : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε < r :=
    hp.and ((eventually_lt_nhds hr).filter_mono nhdsWithin_le_nhds)
  filter_upwards [eventually_pi (fun _ : s => hb)] with ε hε
  symm
  apply integral_deleted_partition (Icc l u) C
    (fun a : s => Ioo (a.val-ε a) (a.val+ε a)) f hCB ?_ hC
    (fun _ => measurableSet_Icc) (fun _ => measurableSet_Ioo)
    (deleted_integrable s l u f hf ε (fun a => (hε a).1))
  intro a x hx
  constructor <;> dsimp at * <;> linarith [hx.1, hx.2, (hε a).2]

end D12Complex.FiniteDeletedLimits
