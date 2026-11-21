import MathGenome.Internal.RealAnalysis.Specs.D11.Ch20.LocalNullEndpointRepresentative
import MathGenome.Internal.RealAnalysis.D11.Ch20.RadonDisjointCompactLocalization
import MathGenome.Internal.RealAnalysis.D11.Ch20.LpDualFiniteMeasure
import MathGenome.Internal.RealAnalysis.D11.Ch10.SigmafiniteSupport
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace D11.Ch20.LocalNullEndpointRepresentative
universe u
noncomputable section

section Extension
variable {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
variable (ν : Measure X) (A : Set X) (hA : MeasurableSet A)

private def extendZeroValue (f : Lp 𝕜 1 (ν.restrict A)) : Lp 𝕜 1 ν :=
  ((memLp_indicator_iff_restrict hA.nullMeasurableSet).mpr
    (Lp.memLp f)).toLp (A.indicator (f : X → 𝕜))

private lemma extendZeroValue_coe (f : Lp 𝕜 1 (ν.restrict A)) :
    extendZeroValue ν A hA f =ᵐ[ν] A.indicator (f : X → 𝕜) :=
  MemLp.coeFn_toLp ((memLp_indicator_iff_restrict hA.nullMeasurableSet).mpr (Lp.memLp f))

/-- Extending a restricted L¹ function by zero preserves its norm. -/
def extendZero : Lp 𝕜 1 (ν.restrict A) →ₗᵢ[𝕜] Lp 𝕜 1 ν where
  toFun := extendZeroValue ν A hA
  map_add' f g := by
    apply Lp.ext
    have he := (ae_eq_restrict_iff_indicator_ae_eq hA).mp (Lp.coeFn_add f g)
    filter_upwards [extendZeroValue_coe ν A hA (f + g),
      Lp.coeFn_add (extendZeroValue ν A hA f) (extendZeroValue ν A hA g),
      extendZeroValue_coe ν A hA f, extendZeroValue_coe ν A hA g, he] with x hx ha hf hg heq
    rw [hx, ha, Pi.add_apply, hf, hg, heq]
    by_cases hxA : x ∈ A <;> simp [hxA]
  map_smul' c f := by
    apply Lp.ext
    have he := (ae_eq_restrict_iff_indicator_ae_eq hA).mp (Lp.coeFn_smul c f)
    filter_upwards [extendZeroValue_coe ν A hA (c • f),
      Lp.coeFn_smul c (extendZeroValue ν A hA f), extendZeroValue_coe ν A hA f,
      he] with x hx hs hf heq
    simp only [RingHom.id_apply]
    rw [hx, hs, Pi.smul_apply, hf, heq]
    by_cases hxA : x ∈ A <;> simp [hxA]
  norm_map' f := by
    change ‖extendZeroValue ν A hA f‖ = ‖f‖
    rw [extendZeroValue, Lp.norm_toLp,
      eLpNorm_indicator_eq_eLpNorm_restrict hA.nullMeasurableSet, Lp.norm_def]

lemma extendZero_coe (f : Lp 𝕜 1 (ν.restrict A)) :
    extendZero ν A hA f =ᵐ[ν] A.indicator (f : X → 𝕜) :=
  extendZeroValue_coe ν A hA f

end Extension


section LocalDensity
variable {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜]

/-- Finite-measure duality applied to the zero-extension of a restriction.
The norm bound is the norm on the original space. -/
theorem local_density (ν : Measure X) (A : Set X) (hA : MeasurableSet A)
    (hfin : ν A < ∞) (ℓ : Lp 𝕜 1 ν →L[𝕜] 𝕜) :
    ∃ h : X → 𝕜, Measurable h ∧ (∀ x, ‖h x‖ ≤ ‖ℓ‖) ∧
      ∀ f : Lp 𝕜 1 (ν.restrict A),
        Integrable (fun x => f x * h x) (ν.restrict A) ∧
        ℓ (extendZero ν A hA f) = ∫ x in A, f x * h x ∂ν := by
  classical
  letI : IsFiniteMeasure (ν.restrict A) := ⟨by simpa using hfin⟩
  let L := ℓ.comp (extendZero (𝕜 := 𝕜) ν A hA).toContinuousLinearMap
  have hn : ‖L‖ ≤ ‖ℓ‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro f
    simpa [L] using ℓ.le_opNorm (extendZero ν A hA f)
  obtain ⟨k, hk, _⟩ := LpDualFiniteMeasure.finite_measure_duality
    (ν.restrict A) 1 ∞ (by simp) L
  have hb : ∀ᵐ x ∂ν.restrict A, ‖k x‖ ≤ ‖ℓ‖ := by
    have hh := ae_le_lpNorm_exponent_top (Lp.memLp k)
    have he : lpNorm (k : X → 𝕜) ∞ (ν.restrict A) = ‖k‖ := rfl
    rw [he, hk.2] at hh
    exact hh.mono fun _ hx => hx.trans hn
  let B := {x | ‖k x‖ ≤ ‖ℓ‖}
  have hB : MeasurableSet B := measurableSet_le (Lp.stronglyMeasurable k).measurable.norm measurable_const
  let h := B.indicator (k : X → 𝕜)
  have hh : h =ᵐ[ν.restrict A] k := by
    filter_upwards [hb] with x hx
    exact Set.indicator_of_mem (show x ∈ B from hx) _
  refine ⟨h, (Lp.stronglyMeasurable k).measurable.indicator hB, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ B
    · change ‖B.indicator (k : X → 𝕜) x‖ ≤ ‖ℓ‖
      rw [Set.indicator_of_mem hx]
      exact hx
    · simpa [h, hx] using norm_nonneg ℓ
  · intro f
    have he : (fun x => f x * h x) =ᵐ[ν.restrict A] fun x => f x * k x :=
      by
        filter_upwards [hh] with x hx
        rw [hx]
    refine ⟨(hk.1 f).1.congr he.symm, ?_⟩
    exact (hk.1 f).2.trans (integral_congr_ae he.symm)

end LocalDensity

section Support
open Specs.D11.Ch20.RadonDisjointCompactLocalization
variable {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  {𝕜 : Type} [RCLike 𝕜]

/-- A countable compact cover of the nonzero support is manufactured for each
L¹ function; the ambient space need not be sigma-finite. -/
theorem countable_compact_support (μ : @Measure X (borel X)) (hμ : Ch18.isRadon μ)
    (C : Set (Set X)) (hC : MaximalFamily μ C) :
    letI : MeasurableSpace X := M μ
    ∀ f : Lp 𝕜 1 (m μ), ∃ T : Set (Set X), T ⊆ C ∧ T.Countable ∧
      ∀ᵐ x ∂m μ, f x ≠ 0 → x ∈ ⋃₀ T := by
  letI : MeasurableSpace X := M μ
  intro f
  let A : ℕ → Set X := fun n => {x | 1 / (n + 1 : ℝ) < ‖f x‖}
  have hAm (n : ℕ) : MeasurableSet (A n) :=
    measurableSet_lt measurable_const (Lp.stronglyMeasurable f).norm.measurable
  have hAf (n : ℕ) : m μ (A n) < ∞ :=
    (L1.integrable_coeFn f).measure_norm_gt_lt_top (by positivity)
  have hd (n : ℕ) := RadonDisjointCompactLocalization.finite_decomposition
    μ hμ C hC (A n) (hAm n) (hAf n)
  let T := ⋃ n, meeting C (A n)
  have hT : T.Countable := Set.countable_iUnion (fun n => (hd n).1)
  have hTC : T ⊆ C := by
    intro K hK
    obtain ⟨n, hn⟩ := mem_iUnion.mp hK
    exact hn.1
  have hn : m μ (⋃ n, A n \ ⋃₀ meeting C (A n)) = 0 :=
    measure_iUnion_null fun n => (hd n).2.2
  refine ⟨T, hTC, hT, ?_⟩
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hn] with x hx hfx
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (norm_pos_iff.mpr hfx)
  have hm : x ∈ ⋃₀ meeting C (A n) := by
    by_contra hh
    exact hx (mem_iUnion.mpr ⟨n, hn, hh⟩)
  obtain ⟨K, hK, hxK⟩ := mem_sUnion.mp hm
  exact mem_sUnion.mpr ⟨K, mem_iUnion.mpr ⟨n, hK⟩, hxK⟩

end Support
section Approximation
variable {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
variable (ν : Measure X)

/-- Restriction inside the original ordinary L¹ space. -/
def cut (f : Lp 𝕜 1 ν) (A : Set X) (hA : MeasurableSet A) : Lp 𝕜 1 ν :=
  ((Lp.memLp f).indicator hA.nullMeasurableSet).toLp (A.indicator (f : X → 𝕜))

lemma cut_coe (f : Lp 𝕜 1 ν) (A : Set X) (hA : MeasurableSet A) :
    cut ν f A hA =ᵐ[ν] A.indicator (f : X → 𝕜) := MemLp.coeFn_toLp _

lemma cut_empty (f : Lp 𝕜 1 ν) : cut ν f ∅ MeasurableSet.empty = 0 := by
  apply Lp.ext
  filter_upwards [cut_coe ν f ∅ MeasurableSet.empty, Lp.coeFn_zero (E := 𝕜) (p := 1) (μ := ν)] with x hx hz
  simp only [Set.indicator_empty', Pi.zero_apply] at hx hz
  exact hx.trans hz.symm

lemma cut_union (f : Lp 𝕜 1 ν) (A B : Set X) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hd : Disjoint A B) :
    cut ν f (A ∪ B) (hA.union hB) = cut ν f A hA + cut ν f B hB := by
  apply Lp.ext
  filter_upwards [cut_coe ν f (A ∪ B) (hA.union hB), cut_coe ν f A hA,
    cut_coe ν f B hB, Lp.coeFn_add (cut ν f A hA) (cut ν f B hB)] with x hx hxA hxB hs
  rw [hx, hs, Pi.add_apply, hxA, hxB, Set.indicator_union_of_disjoint hd]

lemma cut_eq_extendZero (f : Lp 𝕜 1 ν) (A : Set X) (hA : MeasurableSet A) :
    cut ν f A hA = extendZero ν A hA ((Lp.memLp f).restrict A |>.toLp f) := by
  apply Lp.ext
  apply (cut_coe ν f A hA).trans
  apply EventuallyEq.trans _ (extendZero_coe ν A hA _).symm
  exact ((ae_eq_restrict_iff_indicator_ae_eq hA).mp (MemLp.coeFn_toLp _)).symm

/-- Dominated convergence on the countable compact cover gives convergence
in the original L¹ norm. -/
lemma tendsto_cut (f : Lp 𝕜 1 ν) (U : ℕ → Set X) (hU : ∀ n, MeasurableSet (U n))
    (hmono : Monotone U) (hcover : ∀ᵐ x ∂ν, f x ≠ 0 → x ∈ ⋃ n, U n) :
    Tendsto (fun n => cut ν f (U n) (hU n)) atTop (𝓝 f) := by
  have hlim : ∀ᵐ x ∂ν,
      Tendsto (fun n => ‖(U n).indicator (f : X → 𝕜) x - f x‖) atTop (𝓝 0) := by
    filter_upwards [hcover] with x hx
    by_cases hz : f x = 0
    · have he : (fun n => ‖(U n).indicator (f : X → 𝕜) x - f x‖) = fun _ : ℕ => (0 : ℝ) := by
        funext n
        by_cases hx : x ∈ U n <;> simp [hx, hz]
      rw [he]
      exact tendsto_const_nhds
    · obtain ⟨n, hn⟩ := mem_iUnion.mp (hx hz)
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop n] with j hj
      simp [Set.indicator_of_mem (hmono hj hn)]
  have hi := tendsto_integral_of_dominated_convergence (μ := ν)
    (fun x => ‖f x‖)
    (fun n => (((Lp.aestronglyMeasurable f).indicator (hU n)).sub (Lp.aestronglyMeasurable f)).norm)
    (L1.integrable_coeFn f).norm
    (fun n => ae_of_all ν fun x => by
      by_cases hx : x ∈ U n <;> simp [hx]) hlim
  simp only [integral_zero] at hi
  rw [tendsto_iff_norm_sub_tendsto_zero]
  convert hi using 1
  ext n
  rw [← dist_eq_norm, L1.dist_eq_integral_dist]
  apply integral_congr_ae
  filter_upwards [cut_coe ν f (U n) (hU n)] with x hc
  simp only [dist_eq_norm, hc, Pi.sub_apply]

lemma integral_extendZero_mul (A : Set X) (hA : MeasurableSet A)
    (f : Lp 𝕜 1 (ν.restrict A)) (g : X → 𝕜) :
    (∫ x, extendZero ν A hA f x * g x ∂ν) = ∫ x in A, f x * g x ∂ν := by
  rw [← integral_indicator hA]
  apply integral_congr_ae
  filter_upwards [extendZero_coe ν A hA f] with x hx
  by_cases hxA : x ∈ A <;> simp [hx, hxA]

end Approximation

section Assembly
open Specs.D11.Ch20.RadonDisjointCompactLocalization
variable {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  {𝕜 : Type} [RCLike 𝕜]

/-- Agreement on all compact pieces determines a continuous functional on
ordinary L¹. The countable family is chosen separately for each function. -/
theorem ext_of_compacts (μ : @Measure X (borel X)) (hμ : Ch18.isRadon μ)
    (C : Set (Set X)) (hC : MaximalFamily μ C) :
    letI : MeasurableSpace X := M μ
    ∀ L N : Lp 𝕜 1 (m μ) →L[𝕜] 𝕜,
      (∀ (K : Set X) (hK : K ∈ C) (hKm : MeasurableSet K)
        (f : Lp 𝕜 1 ((m μ).restrict K)),
        L (extendZero (m μ) K hKm f) = N (extendZero (m μ) K hKm f)) → L = N := by
  classical
  letI : MeasurableSpace X := M μ
  letI : OpensMeasurableSpace X := ⟨RadonCaratheodoryLocalization.borel_measurable μ⟩
  intro L N hLN
  ext f
  obtain ⟨T, hTC, hcT, hcover⟩ := countable_compact_support μ hμ C hC f
  have hmK (K : Set X) (hK : K ∈ insert ∅ C) : MeasurableSet K := by
    rcases hK with rfl | hK
    · exact MeasurableSet.empty
    · exact (hC.1.1 K hK).1.isClosed.measurableSet
  have hdK : (insert (∅ : Set X) C).Pairwise Disjoint := by
    exact Set.pairwise_insert.mpr
      ⟨hC.1.2, fun K _ _ => ⟨by simp, by simp⟩⟩
  have hfin (F : Finset (Set X)) (hF : ∀ K ∈ F, K ∈ insert ∅ C) :
      L (cut (m μ) f (⋃ K ∈ F, K) (Finset.measurableSet_biUnion F fun K hK => hmK K (hF K hK))) =
      N (cut (m μ) f (⋃ K ∈ F, K) (Finset.measurableSet_biUnion F fun K hK => hmK K (hF K hK))) := by
    induction F using Finset.induction_on with
    | empty => simp [cut_empty]
    | @insert K F hKF ih =>
      have hK := hF K (Finset.mem_insert_self K F)
      have hF' := fun J hJ => hF J (Finset.mem_insert_of_mem hJ)
      have hmF := Finset.measurableSet_biUnion F (fun J hJ => hmK J (hF' J hJ))
      have hdisj : Disjoint K (⋃ J ∈ F, J) := by
        apply disjoint_iUnion_right.mpr
        intro J
        apply disjoint_iUnion_right.mpr
        intro hJ
        exact hdK hK (hF' J hJ) (fun he => hKF (he ▸ hJ))
      simp only [Finset.mem_insert, iUnion_iUnion_eq_or_left]
      rw [cut_union (m μ) f K _ (hmK K hK) hmF hdisj, map_add, map_add, ih hF']
      congr 1
      rcases hK with rfl | hK
      · simp [cut_empty]
      · rw [cut_eq_extendZero]
        exact hLN K hK (hmK K (Or.inr hK)) _
  let E : ℕ → Set X := enumerateCountable hcT ∅
  let F (n : ℕ) := (Finset.range n).image E
  have hF (n : ℕ) (K : Set X) (hK : K ∈ F n) : K ∈ insert ∅ C := by
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hK
    rcases range_enumerateCountable_subset hcT ∅ (mem_range_self j) with he | he
    · exact Or.inl he
    · exact Or.inr (hTC he)
  let U (n : ℕ) := ⋃ K ∈ F n, K
  have hUm (n : ℕ) : MeasurableSet (U n) :=
    Finset.measurableSet_biUnion (F n) fun K hK => hmK K (hF n K hK)
  have hmono : Monotone U := by
    intro i j hij x hx
    obtain ⟨K, hK⟩ := mem_iUnion.mp hx
    obtain ⟨hKi, hxK⟩ := mem_iUnion.mp hK
    exact mem_iUnion.mpr ⟨K, mem_iUnion.mpr
      ⟨Finset.image_subset_image (Finset.range_mono hij) hKi, hxK⟩⟩
  have hcov : ∀ᵐ x ∂m μ, f x ≠ 0 → x ∈ ⋃ n, U n := by
    filter_upwards [hcover] with x hx hfx
    obtain ⟨K, hKT, hxK⟩ := hx hfx
    obtain ⟨j, hj⟩ := subset_range_enumerate hcT ∅ hKT
    exact mem_iUnion.mpr ⟨j + 1, mem_iUnion.mpr ⟨K,
      mem_iUnion.mpr ⟨Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (Nat.lt_succ_self j), hj⟩, hxK⟩⟩⟩
  have ht := tendsto_cut (m μ) f U hUm hmono hcov
  exact tendsto_nhds_unique (L.continuous.tendsto f |>.comp ht)
    ((N.continuous.tendsto f |>.comp ht).congr (fun n => (hfin (F n) (hF n)).symm))

end Assembly


/-- Representation by a pointwise bounded measurable density in the exact
Radon-derived Carathéodory space, without a sigma-finiteness hypothesis. -/
theorem endpoint_representative :
    Specs.D11.Ch20.LocalNullEndpointRepresentative.endpoint_representative := by
  classical
  intro X _ _ _ 𝕜 _ _ _ μ hμ
  letI : MeasurableSpace X := Specs.D11.Ch20.RadonDisjointCompactLocalization.M μ
  letI : OpensMeasurableSpace X := ⟨RadonCaratheodoryLocalization.borel_measurable μ⟩
  intro ℓ
  let ν := Specs.D11.Ch20.RadonDisjointCompactLocalization.m μ
  obtain ⟨C, hC⟩ := RadonDisjointCompactLocalization.exists_maximal_family μ hμ
  have hloc (K : Set X) (hK : K ∈ C) :
      ∃ h : X → 𝕜, Measurable h ∧ (∀ x, ‖h x‖ ≤ ‖ℓ‖) ∧
        ∀ f : Lp 𝕜 1 (ν.restrict K),
          Integrable (fun x => f x * h x) (ν.restrict K) ∧
          ℓ (extendZero ν K (hC.1.1 K hK).1.isClosed.measurableSet f) =
            ∫ x in K, f x * h x ∂ν := by
    apply local_density ν K (hC.1.1 K hK).1.isClosed.measurableSet _ ℓ
    change Specs.D11.Ch20.RadonDisjointCompactLocalization.m μ K < ∞
    rw [RadonCaratheodoryLocalization.measure_apply]
    exact hμ.1 K (hC.1.1 K hK).1
  choose h hm hb hr using hloc
  obtain ⟨g, hg, hglue, hzero⟩ :=
    RadonDisjointCompactLocalization.measurable_gluing μ hμ C hC 𝕜
      (fun K hK x => h K hK x)
      (fun K hK => (hm K hK).comp measurable_subtype_coe)
  have hbound (x : X) : ‖g x‖ ≤ ‖ℓ‖ := by
    by_cases hx : ∃ K ∈ C, x ∈ K
    · obtain ⟨K, hK, hxK⟩ := hx
      rw [hglue K hK ⟨x, hxK⟩]
      exact hb K hK x
    · rw [hzero x (by simpa only [not_exists, not_and] using hx), norm_zero]
      exact norm_nonneg _
  have hG : MemLp g ∞ ν :=
    memLp_top_of_bound hg.aestronglyMeasurable ‖ℓ‖ (ae_of_all ν hbound)
  let G : Lp 𝕜 ∞ ν := hG.toLp g
  let N : Lp 𝕜 1 ν →L[𝕜] 𝕜 := IntegralPairing.pairing ν 1 ∞ G
  have hN (f : Lp 𝕜 1 ν) : Integrable (fun x => f x * g x) ν ∧
      N f = ∫ x, f x * g x ∂ν := by
    obtain ⟨hi, he⟩ := IntegralPairing.pairing_eq_integral ν 1 ∞ G f
    have hae : (fun x => f x * G x) =ᵐ[ν] fun x => f x * g x := by
      filter_upwards [MemLp.coeFn_toLp hG] with x hx
      rw [hx]
    exact ⟨hi.congr hae, he.trans (integral_congr_ae hae)⟩
  have heq : ℓ = N := by
    apply ext_of_compacts μ hμ C hC ℓ N
    intro K hK hKm f
    rw [(hN _).2, integral_extendZero_mul ν K hKm f g]
    refine (hr K hK f).2.trans (integral_congr_ae ?_)
    apply (ae_restrict_iff' hKm).mpr
    exact ae_of_all ν fun x hx =>
      congrArg (fun z : 𝕜 => f x * z) (hglue K hK ⟨x, hx⟩).symm
  refine ⟨g, hg, hbound, fun f => ⟨(hN f).1, ?_⟩⟩
  rw [heq]
  exact (hN f).2

end
end D11.Ch20.LocalNullEndpointRepresentative
