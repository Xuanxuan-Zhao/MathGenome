import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.ChoquetMetrizable
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C24LcsSeparation
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.CompactHullMeasureBarycenters
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-!
Metrizable Choquet, `fa2:p1:choquet`.

A countable bounded family from the original real dual yields a continuous
strictly convex objective. Compactness gives a maximizing representing
probability. Nonextreme points are exhausted by compact chord images; a
Hahn–Banach lift and positive Riesz–Markov endpoint averaging show that each
such image has measure zero. The same exhaustion proves Borelness, without
assuming that the extreme set is closed.
-/

noncomputable section

namespace ExpandedFA.P1.ChoquetMetrizable

open Set MeasureTheory TopologicalSpace
open scoped CompactlySupported

universe u

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]

/-- The nonextreme points of a compact metrizable convex set form a countable
union of compact sets in its original subspace topology. -/
theorem nonextreme_eq_iUnion_compact (K : Set E) (hK : IsCompact K)
    (hconv : Convex ℝ K) [MetrizableSpace K] :
    ∃ A : ℕ → Set K, (∀ n, IsCompact (A n)) ∧
      {x : K | (x : E) ∉ C24FacesSpec.extremePoints K} = ⋃ n, A n := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : MetricSpace K := TopologicalSpace.metrizableSpaceMetric K
  let D := (K × K) × Icc (0 : ℝ) 1
  let chord : D → K := fun p =>
    ⟨(p.2 : ℝ) • (p.1.1 : E) + (1 - (p.2 : ℝ)) • (p.1.2 : E),
      hconv p.1.1.property p.1.2.property p.2.property.1
        (sub_nonneg.mpr p.2.property.2) (add_sub_cancel _ _)⟩
  have hchord : Continuous chord := by
    apply Continuous.subtype_mk
    exact ((continuous_subtype_val.comp continuous_snd).smul
      (continuous_subtype_val.comp (continuous_fst.comp continuous_fst))).add
      ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).smul
        (continuous_subtype_val.comp (continuous_snd.comp continuous_fst)))
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let F : ℕ → Set D := fun n =>
    {p | ε n ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ 1 - ε n ∧
      ε n ≤ dist p.1.1 p.1.2}
  have hF : ∀ n, IsCompact (F n) := by
    intro n
    apply IsClosed.isCompact
    exact (isClosed_le continuous_const (continuous_subtype_val.comp continuous_snd)).inter
      ((isClosed_le (continuous_subtype_val.comp continuous_snd) continuous_const).inter
        (isClosed_le continuous_const
          ((continuous_fst.comp continuous_fst).dist (continuous_snd.comp continuous_fst))))
  refine ⟨fun n => chord '' F n, fun n => (hF n).image hchord, ?_⟩
  ext x
  simp only [mem_ofPred_eq, mem_iUnion]
  constructor
  · intro hx
    by_contra hnone
    apply hx
    refine ⟨x.property, ?_⟩
    intro y hy z hz t ht0 ht1 heq
    by_cases hyz : y = z
    · subst z
      have hxy : (x : E) = y := by
        simpa only [← add_smul, add_sub_cancel, one_smul] using heq
      exact ⟨hxy.symm, hxy.symm⟩
    · let y' : K := ⟨y, hy⟩
      let z' : K := ⟨z, hz⟩
      have hd : 0 < dist y' z' := dist_pos.mpr (fun h => hyz (congrArg Subtype.val h))
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (lt_min ht0 (lt_min (sub_pos.mpr ht1) hd))
      have hn1 : ε n < t := lt_of_lt_of_le hn (min_le_left _ _)
      have hn2 : ε n < 1 - t :=
        lt_of_lt_of_le hn ((min_le_right _ _).trans (min_le_left _ _))
      have hn3 : ε n < dist y' z' :=
        lt_of_lt_of_le hn ((min_le_right _ _).trans (min_le_right _ _))
      exfalso
      apply hnone
      refine ⟨n, ⟨((y', z'), ⟨t, ht0.le, ht1.le⟩), ?_, ?_⟩⟩
      · exact ⟨hn1.le, by dsimp; linarith, hn3.le⟩
      · apply Subtype.ext
        exact heq.symm
  · rintro ⟨n, p, hp, hpx⟩ hx
    have hε : 0 < ε n := by dsimp [ε]; positivity
    have ht0 : 0 < (p.2 : ℝ) := hε.trans_le hp.1
    have ht1 : (p.2 : ℝ) < 1 := by linarith [hp.2.1]
    have heq : (x : E) = (p.2 : ℝ) • (p.1.1 : E) +
        (1 - (p.2 : ℝ)) • (p.1.2 : E) :=
      (congrArg Subtype.val hpx).symm
    obtain ⟨hy, hz⟩ := hx.2 _ p.1.1.property _ p.1.2.property _ ht0 ht1 heq
    have hyz : p.1.1 = p.1.2 := Subtype.ext (hy.trans hz.symm)
    have hd := hp.2.2
    rw [hyz, dist_self] at hd
    exact (not_le_of_gt hε) hd

/-- The extreme-point set is Borel without any closedness assumption. -/
theorem extreme_set_borel : Spec.ExtremeSetBorel.{u} := by
  intro E _ _ _ _ _ _ K hK hconv _
  let : MeasurableSpace K := borel K
  let : BorelSpace K := ⟨rfl⟩
  obtain ⟨A, hA, heq⟩ := nonextreme_eq_iUnion_compact K hK hconv
  have hnon : MeasurableSet {x : K | (x : E) ∉ C24FacesSpec.extremePoints K} := by
    rw [heq]
    exact MeasurableSet.iUnion fun n => (hA n).isClosed.measurableSet
  simpa only [compl_ofPred, not_not] using hnon.compl

/-- Compactness of probabilities and closed scalar moment conditions give a
regular maximizing measure for every continuous real objective. -/
theorem maximizing_representation : Spec.MaximizingRepresentation.{u} := by
  intro E _ _ _ _ _ _ K hK b hb q
  let : MeasurableSpace K := borel K
  let : BorelSpace K := ⟨rfl⟩
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let M : Set (ProbabilityMeasure K) :=
    {μ | ∀ ℓ : E →L[ℝ] ℝ, ℓ b = ∫ x : K, ℓ (x : E) ∂(μ : Measure K)}
  have hMclosed : IsClosed M := by
    have heq : M = ⋂ ℓ : E →L[ℝ] ℝ,
        {μ : ProbabilityMeasure K | ℓ b = ∫ x : K, ℓ (x : E) ∂(μ : Measure K)} := by
      ext μ
      simp [M]
    rw [heq]
    apply isClosed_iInter
    intro ℓ
    exact isClosed_eq continuous_const
      (ProbabilityMeasure.continuous_integral_continuousMap
        (⟨fun x : K => ℓ (x : E), ℓ.continuous.comp continuous_subtype_val⟩ : C(K, ℝ)))
  have hMne : M.Nonempty := by
    refine ⟨(Measure.dirac (⟨b, hb⟩ : K)).toProbabilityMeasure, ?_⟩
    intro ℓ
    change ℓ b = ∫ x : K, ℓ (x : E) ∂Measure.dirac (⟨b, hb⟩ : K)
    rw [integral_dirac]
  have hq : Continuous (fun μ : ProbabilityMeasure K => ∫ x : K, q x ∂(μ : Measure K)) :=
    ProbabilityMeasure.continuous_integral_continuousMap q
  obtain ⟨μ, hμ, hmax⟩ := hMclosed.isCompact.exists_isMaxOn hMne hq.continuousOn
  obtain ⟨ρ, hρprob, hρreg, hρ⟩ :=
    CompactHullMeasureBarycenters.exists_regular_probability μ ℝ
  let : IsProbabilityMeasure ρ := hρprob
  refine ⟨ρ, hρprob, hρreg, ?_, ?_⟩
  · intro ℓ
    refine ⟨(ℓ.continuous.comp continuous_subtype_val).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _), ?_⟩
    exact (hμ ℓ).trans (hρ
      ⟨fun x : K => ℓ (x : E), ℓ.continuous.comp continuous_subtype_val⟩)
  · intro ν hνprob hν
    let ν' : ProbabilityMeasure K := ⟨ν, hνprob⟩
    exact (hmax (a := ν') hν).trans_eq (hρ q)


set_option backward.isDefEq.respectTransparency false in
/-- Lift a finite measure through a continuous compact map whose range has full
measure. Only equality of continuous tests is needed, so no measurable selector
or regularity assumption on the given measure is required. -/
theorem exists_finite_lift {X Y : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (p : C(X, Y)) (ν : Measure Y) [IsFiniteMeasure ν]
    (hν : ν (Set.range p)ᶜ = 0) :
    ∃ ρ : Measure X, IsFiniteMeasure ρ ∧ ρ.Regular ∧
      ρ.real univ = ν.real univ ∧
      ∀ f : C(Y, ℝ), (∫ x, f (p x) ∂ρ) = ∫ y, f y ∂ν := by
  let T : C(Y, ℝ) →ₗ[ℝ] C(X, ℝ) :=
    { toFun := fun f => f.comp p
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let J : C(Y, ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun f => ∫ y, f y ∂ν
      map_add' := fun f g => integral_add
        (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      map_smul' := fun c f => integral_smul c f }
  have hb (f : C(Y, ℝ)) : ‖J f‖ ≤ ν.real univ * ‖T f‖ := by
    change ‖∫ y, f y ∂ν‖ ≤ ν.real univ * ‖T f‖
    rw [mul_comm]
    apply norm_integral_le_of_norm_le_const
    have hae : ∀ᵐ y ∂ν, y ∈ Set.range p := by
      rw [ae_iff]
      exact hν
    filter_upwards [hae] with y hy
    obtain ⟨x, rfl⟩ := hy
    exact (T f).norm_coe_le_norm x
  let H : (LinearMap.range T) →L[ℝ] ℝ := J.compLeftInverse T
  have hH (f : C(Y, ℝ)) : H ⟨T f, ⟨f, rfl⟩⟩ = J f :=
    LinearMap.compLeftInverse_apply_of_bdd J T ⟨ν.real univ, hb⟩ f (T f) rfl
  have hHnorm : ‖H‖ ≤ ν.real univ := by
    apply H.opNorm_le_bound ENNReal.toReal_nonneg
    rintro ⟨g, f, rfl⟩
    rw [hH]
    exact hb f
  obtain ⟨L, hL, hLnorm⟩ := exists_extension_norm_eq (LinearMap.range T) H
  have hpres (f : C(Y, ℝ)) : L (T f) = J f :=
    (hL ⟨T f, ⟨f, rfl⟩⟩).trans (hH f)
  have hnorm : ‖L‖ ≤ ν.real univ := hLnorm.le.trans hHnorm
  have hone : L (1 : C(X, ℝ)) = ν.real univ := by
    simpa [T, J] using hpres 1
  have hpos (f : C(X, ℝ)) (hf : ∀ x, 0 ≤ f x) : 0 ≤ L f := by
    have hnormf : ‖‖f‖ • (1 : C(X, ℝ)) - f‖ ≤ ‖f‖ := by
      apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
      intro x
      change |‖f‖ * 1 - f x| ≤ ‖f‖
      rw [abs_le]
      constructor <;> linarith [hf x, f.apply_le_norm x]
    have hle := (le_abs_self (L (‖f‖ • (1 : C(X, ℝ)) - f))).trans
      (L.le_opNorm _)
    have hle' : L (‖f‖ • (1 : C(X, ℝ)) - f) ≤ ν.real univ * ‖f‖ :=
      hle.trans ((mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left hnormf ENNReal.toReal_nonneg))
    rw [map_sub, map_smul, hone] at hle'
    change ‖f‖ * ν.real univ - L f ≤ ν.real univ * ‖f‖ at hle'
    nlinarith
  let Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ :=
    { toFun := fun f => L f.toContinuousMap
      map_add' := by intros; exact L.map_add _ _
      map_smul' := by intros; exact L.map_smul _ _
      monotone' := by
        intro f g hfg
        have := hpos (g.toContinuousMap - f.toContinuousMap) (fun x => sub_nonneg.mpr (hfg x))
        simpa only [map_sub, sub_nonneg] using this }
  let ρ := RealRMK.rieszMeasure Λ
  have hrep (f : C(X, ℝ)) : (∫ x, f x ∂ρ) = L f := by
    let f' : C_c(X, ℝ) :=
      { toContinuousMap := f
        hasCompactSupport' := HasCompactSupport.of_compactSpace _ }
    exact RealRMK.integral_rieszMeasure Λ f'
  refine ⟨ρ, inferInstance, inferInstance, ?_, ?_⟩
  · simpa using (hrep 1).trans hone
  · intro f
    exact (hrep (T f)).trans (hpres f)


/-- A compact metrizable subset has a countable family of uniformly bounded
restrictions of the original real dual which separates its points. -/
theorem bounded_separating_sequence [LocallyConvexSpace ℝ E]
    (K : Set E) (hK : IsCompact K) [MetrizableSpace K] :
    ∃ d : ℕ → E →L[ℝ] ℝ,
      (∀ n (x : K), |d n x| ≤ 1) ∧
      ∀ x y : K, x ≠ y → ∃ n, d n x ≠ d n y := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : MetricSpace K := TopologicalSpace.metrizableSpaceMetric K
  let U : (E →L[ℝ] ℝ) → Set (K × K) := fun ℓ => {p | ℓ p.1 ≠ ℓ p.2}
  have hU (ℓ : E →L[ℝ] ℝ) : IsOpen (U ℓ) :=
    isOpen_ne_fun (ℓ.continuous.comp (continuous_subtype_val.comp continuous_fst))
      (ℓ.continuous.comp (continuous_subtype_val.comp continuous_snd))
  have hcover : {p : K × K | p.1 ≠ p.2} ⊆ ⋃ ℓ, U ℓ := by
    intro p hp
    obtain ⟨ℓ, hℓ⟩ := C24.real_locally_convex_points_separated (p.1 : E) (p.2 : E)
      (fun heq => hp (Subtype.ext heq))
    exact mem_iUnion.mpr ⟨ℓ, hℓ⟩
  obtain ⟨ℓ, hℓ⟩ := (HereditarilyLindelofSpace.isLindelof
    {p : K × K | p.1 ≠ p.2}).indexed_countable_subcover U hU hcover
  let a : ℕ → C(K, ℝ) := fun n =>
    ⟨fun x => ℓ n x, (ℓ n).continuous.comp continuous_subtype_val⟩
  let c : ℕ → ℝ := fun n => (1 + ‖a n‖)⁻¹
  have hc (n : ℕ) : 0 < c n := inv_pos.mpr (by positivity)
  refine ⟨fun n => c n • ℓ n, ?_, ?_⟩
  · intro n x
    change |c n * a n x| ≤ 1
    rw [abs_mul, abs_of_pos (hc n)]
    calc
      c n * |a n x| ≤ c n * ‖a n‖ :=
        mul_le_mul_of_nonneg_left ((a n).norm_coe_le_norm x) (hc n).le
      _ ≤ 1 := by
        dsimp [c]
        rw [inv_mul_le_iff₀ (by positivity : 0 < 1 + ‖a n‖)]
        linarith
  · intro x y hxy
    obtain ⟨n, hn⟩ := mem_iUnion.mp (hℓ (show (x, y) ∈ {p : K × K | p.1 ≠ p.2} from hxy))
    refine ⟨n, ?_⟩
    change c n * ℓ n x ≠ c n * ℓ n y
    exact fun h => hn ((mul_left_cancel₀ (hc n).ne' h))

/-- A continuous objective strictly increases under every nontrivial proper
chord split. The ambient space itself need not be metrizable or normable. -/
theorem exists_strict_chord_objective [LocallyConvexSpace ℝ E]
    (K : Set E) (hK : IsCompact K) [MetrizableSpace K] :
    ∃ q : C(K, ℝ), ∀ (x y z : K), x ≠ y →
      ∀ t : ℝ, 0 < t → t < 1 →
      (z : E) = t • (x : E) + (1 - t) • (y : E) →
      q z < t * q x + (1 - t) * q y := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨d, hd, hsep⟩ := bounded_separating_sequence K hK
  let a : ℕ → C(K, ℝ) := fun n =>
    ⟨fun x => d n x, (d n).continuous.comp continuous_subtype_val⟩
  let w : ℕ → ℝ := fun n => (1 / 2 : ℝ) ^ n
  let f : ℕ → C(K, ℝ) := fun n => w n • (a n * a n)
  have hw (n : ℕ) : 0 < w n := by dsimp [w]; positivity
  have hf : Summable f := by
    apply summable_geometric_two.of_norm_bounded
    intro n
    apply (ContinuousMap.norm_le _ (hw n).le).mpr
    intro x
    change |w n * (a n x * a n x)| ≤ w n
    rw [abs_mul, abs_of_pos (hw n), abs_mul]
    have h := hd n x
    change |a n x| ≤ 1 at h
    simpa only [mul_one, one_mul] using
      mul_le_mul_of_nonneg_left (mul_self_le_mul_self (abs_nonneg (a n x)) h) (hw n).le
  refine ⟨∑' n, f n, ?_⟩
  intro x y z hxy t ht0 ht1 hz
  obtain ⟨j, hj⟩ := hsep x y hxy
  change a j x ≠ a j y at hj
  have heq (n : ℕ) : a n z = t * a n x + (1 - t) * a n y := by
    change d n (z : E) = _
    rw [hz, map_add, map_smul, map_smul]
    rfl
  have hterm (n : ℕ) : f n z ≤ t * f n x + (1 - t) * f n y := by
    change w n * (a n z * a n z) ≤
      t * (w n * (a n x * a n x)) + (1 - t) * (w n * (a n y * a n y))
    rw [heq]
    have hnon := mul_nonneg (mul_nonneg (hw n).le
      (mul_nonneg ht0.le (sub_pos.mpr ht1).le)) (sq_nonneg (a n x - a n y))
    nlinarith
  have hstrict : f j z < t * f j x + (1 - t) * f j y := by
    change w j * (a j z * a j z) <
      t * (w j * (a j x * a j x)) + (1 - t) * (w j * (a j y * a j y))
    rw [heq]
    have hpos := mul_pos (mul_pos (hw j) (mul_pos ht0 (sub_pos.mpr ht1)))
      (sq_pos_of_ne_zero (sub_ne_zero.mpr hj))
    nlinarith
  have hs (v : K) : Summable (fun n => f n v) :=
    (ContinuousMap.evalCLM ℝ v).summable hf
  have hval (v : K) : (∑' n, f n) v = ∑' n, f n v :=
    (ContinuousMap.evalCLM ℝ v).map_tsum hf
  have hsum := (hs z).tsum_lt_tsum hterm hstrict
    (((hs x).mul_left t).add ((hs y).mul_left (1 - t)))
  simpa only [hval, Summable.tsum_add
    ((hs x).mul_left t) ((hs y).mul_left (1 - t)), tsum_mul_left] using hsum


/-- Positive integration data on a compact space determine a finite regular
measure. No norm estimate is needed for this Riesz–Markov formulation. -/
theorem exists_measure_of_positive_linearMap {X : Type*} [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (L : C(X, ℝ) →ₗ[ℝ] ℝ) (hpos : ∀ f, (∀ x, 0 ≤ f x) → 0 ≤ L f) :
    ∃ ρ : Measure X, IsFiniteMeasure ρ ∧ ρ.Regular ∧
      ∀ f : C(X, ℝ), (∫ x, f x ∂ρ) = L f := by
  let Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ :=
    { toFun := fun f => L f.toContinuousMap
      map_add' := by intros; exact L.map_add _ _
      map_smul' := by intros; exact L.map_smul _ _
      monotone' := by
        intro f g hfg
        have := hpos (g.toContinuousMap - f.toContinuousMap)
          (fun x => sub_nonneg.mpr (hfg x))
        simpa only [map_sub, sub_nonneg] using this }
  refine ⟨RealRMK.rieszMeasure Λ, inferInstance, inferInstance, ?_⟩
  intro f
  let f' : C_c(X, ℝ) :=
    { toContinuousMap := f
      hasCompactSupport' := HasCompactSupport.of_compactSpace _ }
  exact RealRMK.integral_rieszMeasure Λ f'

/-- A measure on a compact family of chords can be replaced by its endpoint
averages, preserving all affine tests. This is built directly by positive
Riesz–Markov, so it needs neither selection nor weighted pushforwards. -/
theorem exists_endpoint_measure {X Y : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (l r : C(X, Y)) (t : C(X, ℝ)) (ht : ∀ x, 0 ≤ t x ∧ t x ≤ 1)
    (ρ : Measure X) [IsFiniteMeasure ρ] :
    ∃ σ : Measure Y, IsFiniteMeasure σ ∧ σ.Regular ∧
      ∀ f : C(Y, ℝ), (∫ y, f y ∂σ) =
        ∫ x, t x * f (l x) + (1 - t x) * f (r x) ∂ρ := by
  let B : C(Y, ℝ) →ₗ[ℝ] C(X, ℝ) :=
    { toFun := fun f => ⟨fun x => t x * f (l x) + (1 - t x) * f (r x),
        (t.continuous.mul (f.continuous.comp l.continuous)).add
          ((continuous_const.sub t.continuous).mul (f.continuous.comp r.continuous))⟩
      map_add' := by
        intro f g
        ext x
        change t x * (f (l x) + g (l x)) + (1 - t x) * (f (r x) + g (r x)) = _
        change _ = (t x * f (l x) + (1 - t x) * f (r x)) +
          (t x * g (l x) + (1 - t x) * g (r x))
        ring
      map_smul' := by
        intro c f
        ext x
        change t x * (c * f (l x)) + (1 - t x) * (c * f (r x)) =
          c * (t x * f (l x) + (1 - t x) * f (r x))
        ring }
  let J : C(X, ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun f => ∫ x, f x ∂ρ
      map_add' := fun f g => integral_add
        (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      map_smul' := fun c f => integral_smul c f }
  obtain ⟨σ, hfin, hreg, hσ⟩ := exists_measure_of_positive_linearMap (J.comp B) (by
    intro f hf
    apply integral_nonneg
    intro x
    exact add_nonneg (mul_nonneg (ht x).1 (hf _))
      (mul_nonneg (sub_nonneg.mpr (ht x).2) (hf _)))
  exact ⟨σ, hfin, hreg, hσ⟩


/-- A maximizing representing probability charges no compact family of chords
on which the objective has a strict Jensen gap. -/
theorem maximizing_measure_chord_null (K : Set E) (hK : IsCompact K)
    [MeasurableSpace K] [BorelSpace K] (b : E) (q : C(K, ℝ))
    (μ : Measure K) [IsProbabilityMeasure μ]
    (hmom : ∀ ℓ : E →L[ℝ] ℝ, ℓ b = ∫ x : K, ℓ (x : E) ∂μ)
    (hmax : ∀ η : Measure K, IsProbabilityMeasure η →
      (∀ ℓ : E →L[ℝ] ℝ, ℓ b = ∫ x : K, ℓ (x : E) ∂η) →
      (∫ x, q x ∂η) ≤ ∫ x, q x ∂μ)
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (p l r : C(X, K)) (t : C(X, ℝ)) (ht : ∀ x, 0 ≤ t x ∧ t x ≤ 1)
    (hchord : ∀ x, (p x : E) = t x • (l x : E) + (1 - t x) • (r x : E))
    (hgap : ∀ x, q (p x) < t x * q (l x) + (1 - t x) * q (r x)) :
    μ (range p) = 0 := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let A := range p
  have hA : MeasurableSet A := (isCompact_range p.continuous).isClosed.measurableSet
  let ν := μ.restrict A
  obtain ⟨ρ, hρfin, _hρreg, hρmass, hρ⟩ := exists_finite_lift p ν (by
    change (μ.restrict A) Aᶜ = 0
    rw [Measure.restrict_apply hA.compl]
    simp)
  let : IsFiniteMeasure ρ := hρfin
  obtain ⟨σ, hσfin, _hσreg, hσ⟩ := exists_endpoint_measure l r t ht ρ
  let : IsFiniteMeasure σ := hσfin
  let η := μ.restrict Aᶜ + σ
  have hint (f : C(K, ℝ)) : Integrable f μ :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hintσ (f : C(K, ℝ)) : Integrable f σ :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hintρ (f : C(X, ℝ)) : Integrable f ρ :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hη (f : C(K, ℝ)) : (∫ x, f x ∂η) =
      (∫ x in Aᶜ, f x ∂μ) + ∫ x, f x ∂σ :=
    integral_add_measure (hint f).restrict (hintσ f)
  have haff (f : C(K, ℝ))
      (hf : ∀ x, t x * f (l x) + (1 - t x) * f (r x) = f (p x)) :
      (∫ x, f x ∂η) = ∫ x, f x ∂μ := by
    rw [hη, hσ, integral_congr_ae (Filter.Eventually.of_forall hf), hρ]
    exact (add_comm _ _).trans (integral_add_compl hA (hint f))
  have hηprob : IsProbabilityMeasure η := by
    apply isProbabilityMeasure_iff_real.mpr
    have hone := haff (1 : C(K, ℝ)) (by
      intro x
      change t x * 1 + (1 - t x) * 1 = 1
      ring)
    simpa using hone
  have hηmom : ∀ ℓ : E →L[ℝ] ℝ, ℓ b = ∫ x : K, ℓ (x : E) ∂η := by
    intro ℓ
    let f : C(K, ℝ) := ⟨fun x => ℓ (x : E), ℓ.continuous.comp continuous_subtype_val⟩
    exact (hmom ℓ).trans (haff f (by
      intro x
      change _ = ℓ (p x : E)
      rw [hchord, map_add, map_smul, map_smul]
      rfl)).symm
  by_contra hnonzero
  have hρpos : 0 < ρ univ := by
    have hreal : 0 < ρ.real univ := by
      rw [hρmass]
      change 0 < ((μ.restrict A) univ).toReal
      rw [Measure.restrict_apply_univ]
      exact ENNReal.toReal_pos hnonzero (measure_ne_top _ _)
    exact (pos_iff_ne_zero).mpr (fun heq => hreal.ne' (by simp [Measure.real, heq]))
  let g : C(X, ℝ) :=
    ⟨fun x => t x * q (l x) + (1 - t x) * q (r x) - q (p x),
      ((t.continuous.mul (q.continuous.comp l.continuous)).add
        ((continuous_const.sub t.continuous).mul (q.continuous.comp r.continuous))).sub
          (q.continuous.comp p.continuous)⟩
  have hgpos (x : X) : 0 < g x := sub_pos.mpr (hgap x)
  have hsupport : Function.support g = univ := by
    ext x
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (hgpos x).ne'
  have hgint : 0 < ∫ x, g x ∂ρ :=
    (integral_pos_iff_support_of_nonneg (fun x => (hgpos x).le) (hintρ g)).mpr
      (hsupport ▸ hρpos)
  let v : C(X, ℝ) :=
    ⟨fun x => t x * q (l x) + (1 - t x) * q (r x),
      (t.continuous.mul (q.continuous.comp l.continuous)).add
        ((continuous_const.sub t.continuous).mul (q.continuous.comp r.continuous))⟩
  have hdiff : (∫ x, g x ∂ρ) = (∫ x, v x ∂ρ) - ∫ x, q (p x) ∂ρ :=
    integral_sub (hintρ v) (hintρ (q.comp p))
  have hstrict : (∫ x in A, q x ∂μ) < ∫ x, q x ∂σ := by
    rw [hσ q, ← hρ q]
    change (∫ x, q (p x) ∂ρ) < ∫ x, v x ∂ρ
    linarith
  have hbound := hmax η hηprob hηmom
  rw [hη q] at hbound
  have htotal := integral_add_compl hA (hint q)
  linarith


/-- Metrizable Choquet: a regular representing probability has mass one on the
Borel set of extreme points, without requiring that set to be closed. -/
theorem extreme_supported_representation : Spec.ExtremeSupportedRepresentation.{u} := by
  intro E _ _ _ _ _ _ _ K _hKne hK hconv _ b hb
  let : MeasurableSpace K := borel K
  let : BorelSpace K := ⟨rfl⟩
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : MetricSpace K := TopologicalSpace.metrizableSpaceMetric K
  obtain ⟨q, hq⟩ := exists_strict_chord_objective K hK
  obtain ⟨μ, hμprob, hμreg, hμmom, hμmax⟩ := maximizing_representation E K hK b hb q
  let : IsProbabilityMeasure μ := hμprob
  let D := (K × K) × Icc (0 : ℝ) 1
  let chord : D → K := fun p =>
    ⟨(p.2 : ℝ) • (p.1.1 : E) + (1 - (p.2 : ℝ)) • (p.1.2 : E),
      hconv p.1.1.property p.1.2.property p.2.property.1
        (sub_nonneg.mpr p.2.property.2) (add_sub_cancel _ _)⟩
  have hchord : Continuous chord := by
    apply Continuous.subtype_mk
    exact ((continuous_subtype_val.comp continuous_snd).smul
      (continuous_subtype_val.comp (continuous_fst.comp continuous_fst))).add
      ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).smul
        (continuous_subtype_val.comp (continuous_snd.comp continuous_fst)))
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let F : ℕ → Set D := fun n =>
    {p | ε n ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ 1 - ε n ∧
      ε n ≤ dist p.1.1 p.1.2}
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hF : ∀ n, IsCompact (F n) := by
    intro n
    apply IsClosed.isCompact
    exact (isClosed_le continuous_const (continuous_subtype_val.comp continuous_snd)).inter
      ((isClosed_le (continuous_subtype_val.comp continuous_snd) continuous_const).inter
        (isClosed_le continuous_const
          ((continuous_fst.comp continuous_fst).dist (continuous_snd.comp continuous_fst))))
  have hnull (n : ℕ) : μ (chord '' F n) = 0 := by
    let : CompactSpace (F n) := isCompact_iff_compactSpace.mp (hF n)
    let : MeasurableSpace (F n) := borel (F n)
    let : BorelSpace (F n) := ⟨rfl⟩
    let p : C(F n, K) := ⟨fun x => chord x.val, hchord.comp continuous_subtype_val⟩
    let l : C(F n, K) := ⟨fun x => x.val.1.1,
      (continuous_fst.comp continuous_fst).comp continuous_subtype_val⟩
    let r : C(F n, K) := ⟨fun x => x.val.1.2,
      (continuous_snd.comp continuous_fst).comp continuous_subtype_val⟩
    let t : C(F n, ℝ) := ⟨fun x => x.val.2,
      (continuous_subtype_val.comp continuous_snd).comp continuous_subtype_val⟩
    have ht0 (x : F n) : 0 < t x := (hε n).trans_le x.property.1
    have ht1 (x : F n) : t x < 1 := by
      have h := x.property.2.1
      change (x.val.2 : ℝ) ≤ 1 - ε n at h
      change (x.val.2 : ℝ) < 1
      linarith [hε n]
    have hneq (x : F n) : l x ≠ r x := by
      intro heq
      have hd := x.property.2.2
      change ε n ≤ dist (l x) (r x) at hd
      rw [heq, dist_self] at hd
      exact (not_le_of_gt (hε n)) hd
    have hrange : range p = chord '' F n := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨y.val, y.property, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨⟨y, hy⟩, rfl⟩
    rw [← hrange]
    exact maximizing_measure_chord_null K hK b q μ (fun ℓ => (hμmom ℓ).2) hμmax
      p l r t (fun x => ⟨(ht0 x).le, (ht1 x).le⟩) (fun _ => rfl)
      (fun x => hq (l x) (r x) (p x) (hneq x) (t x) (ht0 x) (ht1 x) rfl)
  have hcover : {x : K | (x : E) ∉ C24FacesSpec.extremePoints K} ⊆
      ⋃ n, chord '' F n := by
    intro x hx
    by_contra hnone
    apply hx
    refine ⟨x.property, ?_⟩
    intro y hy z hz t ht0 ht1 heq
    by_cases hyz : y = z
    · subst z
      have hxy : (x : E) = y := by
        simpa only [← add_smul, add_sub_cancel, one_smul] using heq
      exact ⟨hxy.symm, hxy.symm⟩
    · let y' : K := ⟨y, hy⟩
      let z' : K := ⟨z, hz⟩
      have hd : 0 < dist y' z' := dist_pos.mpr (fun h => hyz (congrArg Subtype.val h))
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (lt_min ht0 (lt_min (sub_pos.mpr ht1) hd))
      have hn1 : ε n < t := lt_of_lt_of_le hn (min_le_left _ _)
      have hn2 : ε n < 1 - t :=
        lt_of_lt_of_le hn ((min_le_right _ _).trans (min_le_left _ _))
      have hn3 : ε n < dist y' z' :=
        lt_of_lt_of_le hn ((min_le_right _ _).trans (min_le_right _ _))
      exfalso
      apply hnone
      apply mem_iUnion.mpr
      refine ⟨n, ⟨((y', z'), ⟨t, ht0.le, ht1.le⟩), ?_, ?_⟩⟩
      · exact ⟨hn1.le, by dsimp; linarith, hn3.le⟩
      · apply Subtype.ext
        exact heq.symm
  have hnonzero : μ {x : K | (x : E) ∉ C24FacesSpec.extremePoints K} = 0 :=
    measure_mono_null hcover (measure_iUnion_null hnull)
  refine ⟨μ, hμprob, hμreg, hμmom, ?_⟩
  have hext : MeasurableSet {x : K | (x : E) ∈ C24FacesSpec.extremePoints K} :=
    extreme_set_borel E K hK hconv
  have hcompl : μ {x : K | (x : E) ∈ C24FacesSpec.extremePoints K}ᶜ = 0 := hnonzero
  have htotal := measure_add_measure_compl hext (μ := μ)
  simpa only [hcompl, add_zero, measure_univ] using htotal

end ExpandedFA.P1.ChoquetMetrizable
