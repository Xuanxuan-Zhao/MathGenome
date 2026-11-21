import MathGenome.Internal.LinearPDE.P201Specs.Heat.DistributionRegularity
import MathGenome.Internal.LinearPDE.P201.Common.Cutoff
import MathGenome.Internal.LinearPDE.P201.Heat.CausalFundamental
import Mathlib.MeasureTheory.Measure.OpenPos
import MathGenome.Internal.FourierSobolev.P102.U4.DistributionConvolution
import MathGenome.Internal.FourierSobolev.Specs.P102.U4.PointSupport
import MathGenome.Internal.FourierSobolev.P102.U4.ConvolutionSymmetry
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ContDiff Pointwise
namespace P201.Heat
open P201Specs.Heat (spaceTimeCoordinates distributionHeat classicalHeat IsCaloric)
open P201Specs (SmoothCoefficient distributionMultiply)

lemma regularDistribution_restrict {d : ℕ} {V Ω : Domain d} (hV : V ≤ Ω)
    {f : Space d → ℝ} (hf : LocallyIntegrableOn f Ω volume) :
    P102.U4.restrictDistribution hV (regularDistribution Ω f) = regularDistribution V f := by
  ext φ
  change regularDistribution Ω f (P102.U4.zeroExtension ℝ hV φ) = _
  simp only [regularDistribution, P201Specs.regularDistribution, P102.U4.regularDistribution,
    TestFunction.integralAgainstBilinCLM_eq_integral hf,
    TestFunction.integralAgainstBilinCLM_eq_integral (hf.mono_set hV)]
  simp [P102.U4.zeroExtension, TestFunction.monoCLM_apply, hV]

lemma regularDistribution_congr {d : ℕ} {Ω : Domain d} {f g : Space d → ℝ}
    (hf : LocallyIntegrableOn f Ω volume) (hg : LocallyIntegrableOn g Ω volume)
    (heq : EqOn f g Ω) : regularDistribution Ω f = regularDistribution Ω g := by
  apply (P102.U4.regular_injectivity d ℝ Ω f g hf hg).mpr
  exact (ae_restrict_mem Ω.isOpen.measurableSet).mono fun x hx => heq hx

lemma multiPartial_singleton {d : ℕ} (f : Space d → ℝ) (i : Fin d) :
    multiPartial f {i} = fun z => fderiv ℝ f z (coordinate d i) := by
  change P102.U4.partialWord f (({i} : Multiset (Fin d)).sort (· ≤ ·)) = _
  rw [Multiset.sort_singleton]
  rfl

lemma multiPartial_pair {d : ℕ} (f : Space d → ℝ) (i : Fin d) :
    multiPartial f ({i, i} : MultiIndex d) =
      fun z => fderiv ℝ (fun w => fderiv ℝ f w (coordinate d i)) z (coordinate d i) := by
  change P102.U4.partialWord f (({i, i} : Multiset (Fin d)).sort (· ≤ ·)) = _
  rw [Multiset.insert_eq_cons, Multiset.sort_cons i {i} (· ≤ ·) (by simp),
    Multiset.sort_singleton]
  rfl

lemma smooth_multiPartial {d : ℕ} {Ω : Domain d} {f : Space d → ℝ}
    (hf : ContDiffOn ℝ ∞ f Ω) (α : MultiIndex d) :
    ContDiffOn ℝ ∞ (multiPartial f α) Ω := by
  apply contDiffOn_infty.mpr
  intro k
  exact P102.U4.partialWord_contDiffOn Ω
    (hf.of_le (show ((k + α.card : ℕ) : ℕ∞) ≤ ∞ by simp))
    (α.sort (· ≤ ·)) k (by simp)

lemma classicalHeat_smooth {n : ℕ} {Ω : Domain (n + 1)}
    {f : Space (n + 1) → ℝ} (hf : ContDiffOn ℝ ∞ f Ω) :
    ContDiffOn ℝ ∞ (classicalHeat f) Ω :=
  by
    unfold classicalHeat
    convert (smooth_multiPartial hf {(0 : Fin (n + 1))}).sub
        (ContDiffOn.sum (s := Finset.univ) fun (i : Fin n) _ =>
          smooth_multiPartial hf ({i.succ, i.succ} : MultiIndex (n + 1))) using 1
    ext z
    simp only [Pi.sub_apply, Finset.sum_apply]

/-- Smooth representatives of one distribution agree at every interior point. -/
theorem smoothRepresentative_unique {d : ℕ} {Ω : Domain d} {f g : Space d → ℝ}
    (hf : ContDiffOn ℝ ∞ f Ω) (hg : ContDiffOn ℝ ∞ g Ω)
    (heq : regularDistribution Ω f = regularDistribution Ω g) : EqOn f g Ω := by
  have ha := (P102.U4.regular_injectivity d ℝ Ω f g
    (hf.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet)
    (hg.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet)).mp heq
  exact Measure.eqOn_open_of_ae_eq ha Ω.isOpen hf.continuousOn hg.continuousOn

/-- Local smooth distribution representatives glue on arbitrary open sets.
No countability, connectedness, or geometric boundary condition is needed. -/
theorem smoothRepresentative_of_local {d : ℕ} {Ω : Domain d}
    (u : Distribution ℝ Ω)
    (hloc : ∀ x : Ω, ∃ (V : Domain d) (hV : V ≤ Ω), x.val ∈ V ∧
      ∃ f : Space d → ℝ, ContDiffOn ℝ ∞ f V ∧
        regularDistribution V f = P102.U4.restrictDistribution hV u) :
    ∃ f : Space d → ℝ, ContDiffOn ℝ ∞ f Ω ∧ regularDistribution Ω f = u := by
  classical
  choose V hV hx f hf hrep using hloc
  have overlap (a b : Ω) : EqOn (f a) (f b) ((V a : Set (Space d)) ∩ V b) := by
    have ha := congrArg (P102.U4.restrictDistribution (inf_le_left : V a ⊓ V b ≤ V a))
      (hrep a)
    have hb := congrArg (P102.U4.restrictDistribution (inf_le_right : V a ⊓ V b ≤ V b))
      (hrep b)
    rw [regularDistribution_restrict inf_le_left
      ((hf a).continuousOn.locallyIntegrableOn (V a).isOpen.measurableSet),
      P102.U4.restrictionTransitive] at ha
    rw [regularDistribution_restrict inf_le_right
      ((hf b).continuousOn.locallyIntegrableOn (V b).isOpen.measurableSet),
      P102.U4.restrictionTransitive] at hb
    exact smoothRepresentative_unique ((hf a).mono inter_subset_left)
      ((hf b).mono inter_subset_right) (ha.trans hb.symm)
  let F : Space d → ℝ := fun y => if hy : y ∈ Ω then f ⟨y, hy⟩ y else 0
  have hF_eq (a : Ω) : EqOn F (f a) (V a) := by
    intro y hy
    have hyΩ := hV a hy
    change (if h : y ∈ Ω then f ⟨y, h⟩ y else 0) = f a y
    rw [dite_eq_left hyΩ]
    exact overlap ⟨y, hyΩ⟩ a ⟨hx ⟨y, hyΩ⟩, hy⟩
  have hF : ContDiffOn ℝ ∞ F Ω := by
    apply Ω.isOpen.contDiffOn_iff.mpr
    intro y hy
    let a : Ω := ⟨y, hy⟩
    apply ((hf a).contDiffAt ((V a).isOpen.mem_nhds (hx a))).congr_of_eventuallyEq
    exact Filter.eventuallyEq_of_mem ((V a).isOpen.mem_nhds (hx a)) (hF_eq a)
  have hFi : LocallyIntegrableOn F Ω volume :=
    hF.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet
  let T : Distribution ℝ Ω := regularDistribution Ω F - u
  have hvan (a : Ω) : P102.U4.VanishesOn T (V a) := by
    have heq : P102.U4.restrictDistribution (hV a) (regularDistribution Ω F) =
        P102.U4.restrictDistribution (hV a) u := by
      rw [regularDistribution_restrict (hV a) hFi]
      exact (regularDistribution_congr (hFi.mono_set (hV a))
        ((hf a).continuousOn.locallyIntegrableOn (V a).isOpen.measurableSet)
        (hF_eq a)).trans (hrep a)
    apply P102.U4.vanishesOn_of_restriction (hV a) T (subset_refl _)
    intro φ _
    exact sub_eq_zero.mpr (congrArg (fun S : Distribution ℝ (V a) => S φ) heq)
  have hcover : (⋃ a : Ω, (V a : Set (Space d))) = Ω := by
    ext y
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, ha⟩
      exact hV a ha
    · intro hy
      exact mem_iUnion.mpr ⟨⟨y, hy⟩, hx ⟨y, hy⟩⟩
  have hall := P102.U4.vanishesOn_iUnion T (fun a => (V a : Set (Space d)))
    (fun a => (V a).isOpen) hvan
  rw [hcover] at hall
  refine ⟨F, hF, ?_⟩
  ext φ
  exact sub_eq_zero.mp (hall φ φ.tsupport_subset)

lemma regularDistribution_sub {d : ℕ} {Ω : Domain d} {f g : Space d → ℝ}
    (hf : LocallyIntegrableOn f Ω volume) (hg : LocallyIntegrableOn g Ω volume) :
    regularDistribution Ω (f - g) = regularDistribution Ω f - regularDistribution Ω g := by
  ext φ
  simp only [regularDistribution, P201Specs.regularDistribution, P102.U4.regularDistribution,
    TestFunction.integralAgainstBilinCLM_eq_integral (hf.sub hg),
    TestFunction.integralAgainstBilinCLM_eq_integral hf,
    TestFunction.integralAgainstBilinCLM_eq_integral hg,
    ContinuousLinearMap.mul_apply', sub_apply, Pi.sub_apply, mul_sub]
  exact integral_sub (φ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) hf)
    (φ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) hg)

lemma regularDistribution_sum {d : ℕ} {Ω : Domain d} {ι : Type*} (s : Finset ι)
    (f : ι → Space d → ℝ) (hf : ∀ i ∈ s, LocallyIntegrableOn (f i) Ω volume) :
    regularDistribution Ω (∑ i ∈ s, f i) = ∑ i ∈ s, regularDistribution Ω (f i) := by
  classical
  ext φ
  have hs : LocallyIntegrableOn (∑ i ∈ s, f i) Ω volume :=
    Finset.sum_induction f (fun g => LocallyIntegrableOn g Ω volume)
      (fun _ _ => LocallyIntegrableOn.add) locallyIntegrableOn_zero hf
  simp only [regularDistribution, P201Specs.regularDistribution, P102.U4.regularDistribution,
    TestFunction.integralAgainstBilinCLM_eq_integral hs, sum_apply]
  simp_rw [TestFunction.integralAgainstBilinCLM_apply]
  simp only [Finset.sum_apply, ContinuousLinearMap.mul_apply', Finset.mul_sum]
  have hint (i) (hi : i ∈ s) : Integrable (fun x => φ x * f i x) :=
    φ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) (hf i hi)
  rw [integral_finsetSum _ hint]
  apply Finset.sum_congr rfl
  intro i hi
  simp [hf i hi]

/-- Distributional and pointwise heat operators agree on every smooth local
representative, without any condition on its values outside the open set. -/
theorem distributionHeat_regular {n : ℕ} {Ω : Domain (n + 1)}
    {f : Space (n + 1) → ℝ} (hf : ContDiffOn ℝ ∞ f Ω) :
    distributionHeat (regularDistribution Ω f) = regularDistribution Ω (classicalHeat f) := by
  have hi (α : MultiIndex (n + 1)) : LocallyIntegrableOn (multiPartial f α) Ω volume :=
    (smooth_multiPartial hf α).continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet
  unfold distributionHeat classicalHeat
  have hsum : LocallyIntegrableOn
      (∑ i : Fin n, multiPartial f ({i.succ, i.succ} : MultiIndex (n + 1))) Ω volume :=
    by
      convert (ContDiffOn.sum (s := Finset.univ) fun (i : Fin n) _ =>
          smooth_multiPartial hf ({i.succ, i.succ} : MultiIndex (n + 1))).continuousOn.locallyIntegrableOn
          (μ := volume) Ω.isOpen.measurableSet using 1
      ext z
      simp only [Finset.sum_apply]
  rw [regularDistribution_sub (hi _) hsum,
    regularDistribution_sum Finset.univ _ (fun i _ => hi _)]
  congr 1
  · exact P102.U4.derivative_classicalCompatibility _ ℝ Ω _ f (hf.of_le (by simp))
  · apply Finset.sum_congr rfl
    intro i _
    exact P102.U4.derivative_classicalCompatibility _ ℝ Ω _ f (hf.of_le (by simp))

theorem classicalHeat_eq_zero_of_represents {n : ℕ} {Ω : Domain (n + 1)}
    {u : Distribution ℝ Ω} {f : Space (n + 1) → ℝ}
    (hf : ContDiffOn ℝ ∞ f Ω) (hu : distributionHeat u = 0)
    (hrep : regularDistribution Ω f = u) : EqOn (classicalHeat f) 0 Ω := by
  have hz : regularDistribution Ω (classicalHeat f) = regularDistribution Ω 0 := by
    rw [← distributionHeat_regular hf, hrep, hu]
    ext φ
    simp [regularDistribution, P201Specs.regularDistribution, P102.U4.regularDistribution]
  exact smoothRepresentative_unique (classicalHeat_smooth hf) contDiffOn_const hz

lemma spaceTimeCoordinates_symm_time (n : ℕ) :
    (spaceTimeCoordinates n).symm (0, 1) = coordinate (n + 1) 0 := by
  change WithLp.toLp 2 (Fin.cons (α := fun _ : Fin (n + 1) => ℝ) 1
    (WithLp.ofLp (0 : Space n))) = _
  ext j
  refine Fin.cases ?_ (fun i => ?_) j
  · simp [coordinate, P201Specs.coordinate,
      P102.U4.coordinateVector, EuclideanSpace.basisFun_apply]
  · simp [coordinate, P201Specs.coordinate,
      P102.U4.coordinateVector, EuclideanSpace.basisFun_apply]

lemma spaceTimeCoordinates_symm_spatial (n : ℕ) (i : Fin n) :
    (spaceTimeCoordinates n).symm (coordinate n i, 0) = coordinate (n + 1) i.succ := by
  change WithLp.toLp 2 (Fin.cons (α := fun _ : Fin (n + 1) => ℝ) 0
    (WithLp.ofLp (coordinate n i))) = _
  ext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [coordinate, P201Specs.coordinate,
      P102.U4.coordinateVector, EuclideanSpace.basisFun_apply]
  · simp [coordinate, P201Specs.coordinate,
      P102.U4.coordinateVector, EuclideanSpace.basisFun_apply, Pi.single_apply]

lemma timeSlice_deriv {n : ℕ} {f : Space (n + 1) → ℝ} {z : Space (n + 1)}
    (hf : DifferentiableAt ℝ f z) :
    deriv (fun t => f ((spaceTimeCoordinates n).symm ((spaceTimeCoordinates n z).1, t)))
        (spaceTimeCoordinates n z).2 = multiPartial f {0} z := by
  have hline := (spaceTimeCoordinates n).symm.hasFDerivAt.comp_hasDerivAt
    (spaceTimeCoordinates n z).2
    ((hasDerivAt_const _ ((spaceTimeCoordinates n z).1)).prodMk (hasDerivAt_id _))
  have hf' : HasFDerivAt f (fderiv ℝ f z)
      ((spaceTimeCoordinates n).symm ((spaceTimeCoordinates n z).1,
        (spaceTimeCoordinates n z).2)) := by
    simpa only [Prod.mk.eta, ContinuousLinearEquiv.symm_apply_apply] using hf.hasFDerivAt
  have h := hf'.comp_hasDerivAt _ hline
  simpa only [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.coe_coe,
    spaceTimeCoordinates_symm_time, multiPartial_singleton, Function.comp_def, id_eq] using h.deriv

lemma spatialSlice_fderiv {n : ℕ} {f : Space (n + 1) → ℝ}
    (x : Space n) (t : ℝ) (v : Space n)
    (hf : DifferentiableAt ℝ f ((spaceTimeCoordinates n).symm (x, t))) :
    fderiv ℝ (fun y => f ((spaceTimeCoordinates n).symm (y, t))) x v =
      fderiv ℝ f ((spaceTimeCoordinates n).symm (x, t))
        ((spaceTimeCoordinates n).symm (v, 0)) := by
  have hline := (spaceTimeCoordinates n).symm.hasFDerivAt.comp x
    ((hasFDerivAt_id x).prodMk (hasFDerivAt_const t x))
  have h := hf.hasFDerivAt.comp x hline
  change HasFDerivAt (fun y => f ((spaceTimeCoordinates n).symm (y, t))) _ x at h
  rw [h.fderiv]
  rfl

lemma spatialSlice_second {n : ℕ} {Ω : Domain (n + 1)}
    {f : Space (n + 1) → ℝ} (hf : ContDiffOn ℝ ∞ f Ω)
    {z : Space (n + 1)} (hz : z ∈ Ω) (i : Fin n) :
    multiPartial (fun x => f ((spaceTimeCoordinates n).symm
      (x, (spaceTimeCoordinates n z).2))) ({i, i} : MultiIndex n)
      (spaceTimeCoordinates n z).1 =
    multiPartial f ({i.succ, i.succ} : MultiIndex (n + 1)) z := by
  let c := spaceTimeCoordinates n
  let x := (c z).1
  let t := (c z).2
  let G : Space (n + 1) → ℝ := fun w => fderiv ℝ f w (coordinate (n + 1) i.succ)
  have hG : ContDiffOn ℝ ∞ G Ω :=
    (hf.fderiv_of_isOpen Ω.isOpen (by simp)).clm_apply contDiffOn_const
  have heq : (fun y => fderiv ℝ (fun a => f (c.symm (a, t))) y (coordinate n i))
      =ᶠ[nhds x] (fun y => G (c.symm (y, t))) := by
    have hn : ∀ᶠ y in nhds x, c.symm (y, t) ∈ Ω :=
      ((c.symm.continuous.comp (continuous_id.prodMk continuous_const)).continuousAt)
        (by simpa [x, t] using Ω.isOpen.mem_nhds hz)
    filter_upwards [hn] with y hy
    rw [spatialSlice_fderiv y t _
      ((hf.contDiffAt (Ω.isOpen.mem_nhds hy)).differentiableAt (by simp)),
      spaceTimeCoordinates_symm_spatial]
  rw [multiPartial_pair, multiPartial_pair]
  change fderiv ℝ (fun y => fderiv ℝ (fun a => f (c.symm (a, t))) y
    (coordinate n i)) x (coordinate n i) = fderiv ℝ G z (coordinate (n + 1) i.succ)
  rw [heq.fderiv_eq]
  have hd : DifferentiableAt ℝ G (c.symm (x, t)) := by
    simpa [x, t] using
      ((hG.contDiffAt (Ω.isOpen.mem_nhds hz)).differentiableAt (by simp))
  rw [spatialSlice_fderiv x t _ hd, spaceTimeCoordinates_symm_spatial]
  simp [x, t, c]

/-- The coordinate formula really is ∂ₜf = Δₓf, with the source sign. -/
theorem isCaloric_iff {n : ℕ} {Ω : Domain (n + 1)} {f : Space (n + 1) → ℝ}
    (hf : ContDiffOn ℝ ∞ f Ω) : IsCaloric Ω f ↔ EqOn (classicalHeat f) 0 Ω := by
  constructor
  · intro h z hz
    have heq := h z hz
    rw [timeSlice_deriv ((hf.contDiffAt (Ω.isOpen.mem_nhds hz)).differentiableAt (by simp))]
      at heq
    simp_rw [P201Specs.laplacian, spatialSlice_second hf hz] at heq
    simpa only [classicalHeat, Pi.sub_apply, Finset.sum_apply, Pi.zero_apply] using
      sub_eq_zero.mpr heq
  · intro h z hz
    rw [timeSlice_deriv ((hf.contDiffAt (Ω.isOpen.mem_nhds hz)).differentiableAt (by simp))]
    simp_rw [P201Specs.laplacian, spatialSlice_second hf hz]
    apply sub_eq_zero.mp
    simpa only [classicalHeat, Pi.sub_apply, Finset.sum_apply, Pi.zero_apply] using h hz

/-- The actual compact test obtained by transposing the heat operator. -/
def heatAdjointTest {n : ℕ} {Ω : Domain (n + 1)} (φ : Test ℝ Ω) : Test ℝ Ω :=
  -P102.U4.testPartialWord Ω [0] φ -
    ∑ i : Fin n, P102.U4.testPartialWord Ω [i.succ, i.succ] φ

lemma distributionHeat_pairing {n : ℕ} {Ω : Domain (n + 1)}
    (u : Distribution ℝ Ω) (φ : Test ℝ Ω) :
    distributionHeat u φ = u (heatAdjointTest φ) := by
  simp [distributionHeat, heatAdjointTest,
    P201Specs.distributionDerivative, P102.U4.distributionPartial,
    Multiset.insert_eq_cons, Multiset.sort_cons, Multiset.sort_singleton]

lemma heatAdjointTest_apply {n : ℕ} {Ω : Domain (n + 1)}
    (φ : Test ℝ Ω) (z : Space (n + 1)) :
    heatAdjointTest φ z = -multiPartial φ {0} z -
      ∑ i : Fin n, multiPartial φ ({i.succ, i.succ} : MultiIndex (n + 1)) z := by
  simp only [heatAdjointTest, sub_apply, neg_apply, sum_apply,
    P102.U4.testPartialWord_coe, multiPartial_singleton, multiPartial_pair,
    P102.U4.partialWord]

lemma heatAdjointTest_tsupport {n : ℕ} {Ω : Domain (n + 1)} (φ : Test ℝ Ω) :
    tsupport (heatAdjointTest φ) ⊆ tsupport φ := by
  apply (tsupport_sub _ _).trans
  apply union_subset
  · exact (tsupport_neg _).le.trans (P102.U4.testPartialWord_tsupport _ φ)
  · have hcoe : ⇑(∑ i : Fin n, P102.U4.testPartialWord Ω [i.succ, i.succ] φ) =
        ∑ i : Fin n, ⇑(P102.U4.testPartialWord Ω [i.succ, i.succ] φ) := by
      ext z
      simp
    rw [hcoe]
    apply Finset.sum_induction _ (fun f => tsupport f ⊆ tsupport φ)
    · intro f g hf hg
      exact (tsupport_add f g).trans (union_subset hf hg)
    · simp
    · intro i _
      exact P102.U4.testPartialWord_tsupport _ φ

/-- Lebesgue measure is unchanged by moving the time coordinate to the end. -/
lemma spaceTimeCoordinates_measurePreserving (n : ℕ) :
    MeasurePreserving (spaceTimeCoordinates n) := by
  exact (heatCoordinates_measurePreserving n).comp (PiLp.volume_preserving_ofLp (Fin (n + 1)))

/-- The causal kernel in the canonical Euclidean distribution coordinates. -/
def euclideanCausalKernel (n : ℕ) : Space (n + 1) → ℝ :=
  causalKernel n ∘ spaceTimeCoordinates n

lemma euclideanCausalKernel_locallyIntegrable (n : ℕ) (hn : 1 ≤ n) :
    LocallyIntegrable (euclideanCausalKernel n) := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  have h := (causalLocallyIntegrable n hn).integrableOn_isCompact
    (hK.image (spaceTimeCoordinates n).continuous)
  have h' := ((spaceTimeCoordinates_measurePreserving n).integrableOn_comp_preimage
    (spaceTimeCoordinates n).toHomeomorph.measurableEmbedding).mpr h
  simpa only [euclideanCausalKernel, Set.preimage_image_eq _
    (spaceTimeCoordinates n).injective] using h'

/-- The product-coordinate adjoint is exactly the transpose on common tests. -/
lemma adjointHeatTest_common {n : ℕ} (φ : Test ℝ (⊤ : Domain (n + 1)))
    (z : Space (n + 1)) :
    P201Specs.Heat.adjointHeatTest (φ ∘ (spaceTimeCoordinates n).symm)
      (spaceTimeCoordinates n z) = heatAdjointTest φ z := by
  rw [heatAdjointTest_apply]
  unfold P201Specs.Heat.adjointHeatTest
  simp only [Function.comp_apply]
  rw [timeSlice_deriv (φ.contDiff.differentiable (by simp) z)]
  simp_rw [P201Specs.laplacian,
    spatialSlice_second (Ω := ⊤) φ.contDiff.contDiffOn (Set.mem_univ z)]

/-- The causal fundamental equation transported to the common test dual. -/
theorem euclideanCausalFundamental (n : ℕ) (hn : 1 ≤ n) :
    distributionHeat (regularDistribution (⊤ : Domain (n + 1)) (euclideanCausalKernel n)) =
      P102.U4.pointMass ℝ ⊤ 0 := by
  ext φ
  rw [distributionHeat_pairing, P102.U4.regular_pairing _ ℝ ⊤ _
    (locallyIntegrableOn_univ.mpr (euclideanCausalKernel_locallyIntegrable n hn))]
  let c := spaceTimeCoordinates n
  have h := causalFundamental n hn (φ ∘ c.symm)
    (φ.contDiff.comp c.symm.contDiff)
    (φ.hasCompactSupport.comp_homeomorph c.symm.toHomeomorph)
  have hi := (spaceTimeCoordinates_measurePreserving n).integral_comp
    c.toHomeomorph.measurableEmbedding
    (fun z => causalKernel n z * P201Specs.Heat.adjointHeatTest (φ ∘ c.symm) z)
  change (∫ z, euclideanCausalKernel n z *
    P201Specs.Heat.adjointHeatTest (φ ∘ c.symm) (c z)) = _ at hi
  simp only [c, adjointHeatTest_common] at hi
  simp only [Opens.coe_top, setIntegral_univ]
  rw [hi, h.2.1]
  change φ (c.symm (0 : Space n × ℝ)) = φ 0
  rw [map_zero]

/-- Constant coefficient differentiation cannot enlarge heat-operator support. -/
lemma distributionHeat_support {n : ℕ} {Ω : Domain (n + 1)} (u : Distribution ℝ Ω) :
    P102.U4.relativeSupport (distributionHeat u) ⊆ P102.U4.relativeSupport u := by
  apply P102.U4.relativeSupport_mono _ u
  intro U _ _ hu φ hφ
  rw [distributionHeat_pairing]
  exact hu _ ((heatAdjointTest_tsupport φ).trans hφ)

lemma distributionHeat_compactSupport {n : ℕ} (v : Distribution ℝ (⊤ : Domain (n + 1)))
    (hv : IsCompact (P102.U4.relativeSupport v)) :
    IsCompact (P102.U4.relativeSupport (distributionHeat v)) :=
  hv.of_isClosed_subset (P102.U4.relativeSupport_top_isClosed _) (distributionHeat_support v)

/-- Inversion on compact distributions follows from the two differentiation
rules, without any function representative for the compact distribution. -/
theorem compactHeat_inverse {n : ℕ} (E v : Distribution ℝ (⊤ : Domain (n + 1)))
    (hv : IsCompact (P102.U4.relativeSupport v))
    (hE : distributionHeat E = P102.U4.pointMass ℝ ⊤ 0) :
    P102.U4.rightCompactConvolution E (distributionHeat v)
      (distributionHeat_compactSupport v hv) = v := by
  let hc (α : MultiIndex (n + 1)) := P102.U4.distributionPartial_compactSupport v hv α
  have hs (α : MultiIndex (n + 1)) :
      P102.U4.rightCompactConvolution E (distributionDerivative α v) (hc α) =
        P102.U4.rightCompactConvolution (distributionDerivative α E) v hv :=
    (P102.U4.rightCompactConvolution_partial_right E v hv α (hc α)).symm.trans
      (P102.U4.rightCompactConvolution_partial_left E v hv α)
  have hlin : P102.U4.rightCompactConvolution E (distributionHeat v)
      (distributionHeat_compactSupport v hv) =
      P102.U4.rightCompactConvolution (distributionHeat E) v hv := by
    have ht (φ : Test ℝ (⊤ : Domain (n + 1))) :
        P102.U4.convolutionInnerTest (distributionHeat v)
          (distributionHeat_compactSupport v hv) φ =
        P102.U4.convolutionInnerTest (distributionDerivative {0} v) (hc {0}) φ -
          ∑ i : Fin n, P102.U4.convolutionInnerTest
            (distributionDerivative ({i.succ, i.succ} : MultiIndex (n + 1)) v)
            (hc _) φ := by
      ext x
      change distributionHeat v (P102.U4.additionTest φ x) = _
      simp [distributionHeat]
    calc
      _ = P102.U4.rightCompactConvolution E (distributionDerivative {0} v) (hc {0}) -
          ∑ i : Fin n, P102.U4.rightCompactConvolution E
            (distributionDerivative ({i.succ, i.succ} : MultiIndex (n + 1)) v) (hc _) := by
        ext φ
        simp only [P102.U4.rightCompactConvolution_apply, ht, map_sub, map_sum,
          sub_apply, sum_apply]
      _ = _ := by
        simp_rw [hs]
        ext φ
        simp [P102.U4.rightCompactConvolution_apply, distributionHeat]
  rw [hlin, hE]
  ext φ
  change v (P102.U4.additionTest φ 0) = v φ
  congr 1
  ext x
  exact congrArg φ (zero_add x)

/-- Multiplication by a fixed compact test, with output in its fixed support
stage even when the input support crosses the domain boundary. -/
def localizationStage {d : ℕ} {Ω : Domain d} (χ : Test ℝ Ω)
    (K : Compacts (Space d)) :
    P102.U4.FixedSupport d ℝ K →L[ℝ]
      P102.U4.FixedSupport d ℝ ⟨tsupport χ, χ.hasCompactSupport⟩ where
  toFun φ := ⟨fun x => φ x * χ x, φ.contDiff.mul χ.contDiff, by
    intro x hx
    simp [image_eq_zero_of_notMem_tsupport hx]⟩
  map_add' φ ψ := by ext x; exact add_mul _ _ _
  map_smul' c φ := by ext x; exact mul_assoc _ _ _
  cont := by
    let B : P102.U4.FixedSupport d ℝ K →L[ℝ] P102.U4.FixedSupport d ℝ K :=
      ContDiffMapSupportedIn.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℝ) χ.contDiff
    apply (ContDiffMapSupportedIn.continuous_iff_comp _).mpr
    intro i
    convert (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i).continuous.comp B.continuous using 1
    rfl

/-- The localized test is a genuine test on Ω, even for whole-space input tests. -/
def localizationTestMap {d : ℕ} {Ω : Domain d} (χ : Test ℝ Ω) :
    Test ℝ (⊤ : Domain d) →L[ℝ] Test ℝ Ω :=
  TestFunction.limitCLM ℝ
    (fun φ => P102.U4.coefficientTestProduct ⟨φ, φ.contDiff.contDiffOn⟩ χ)
    (fun K _ => (P102.U4.stageInclusion ℝ χ.tsupport_subset).comp (localizationStage χ K))
    (by intro K hK φ; ext x; rfl)

@[simp] lemma localizationTestMap_apply {d : ℕ} {Ω : Domain d} (χ : Test ℝ Ω)
    (φ : Test ℝ (⊤ : Domain d)) (x : Space d) :
    localizationTestMap χ φ x = φ x * χ x := rfl

/-- The zero extension of χu is defined by transposing localized tests. -/
def localizedDistribution {d : ℕ} {Ω : Domain d} (χ : Test ℝ Ω)
    (u : Distribution ℝ Ω) : Distribution ℝ (⊤ : Domain d) :=
  u.comp (localizationTestMap χ)

lemma localizedDistribution_support {d : ℕ} {Ω : Domain d} (χ : Test ℝ Ω)
    (u : Distribution ℝ Ω) :
    P102.U4.relativeSupport (localizedDistribution χ u) ⊆ tsupport χ := by
  intro x hx
  by_contra hn
  apply P102.U4.notMem_relativeSupport_of_vanishes _
    (isClosed_tsupport χ).isOpen_compl (subset_univ _) ?_ hn hx
  intro φ hφ
  change u (localizationTestMap χ φ) = 0
  have hz : localizationTestMap χ φ = 0 := by
    ext y
    by_cases hy : y ∈ tsupport χ
    · have hny : y ∉ tsupport φ := fun h => hφ h hy
      simp [image_eq_zero_of_notMem_tsupport hny]
    · simp [image_eq_zero_of_notMem_tsupport hy]
  rw [hz, map_zero]

lemma localizedDistribution_compactSupport {d : ℕ} {Ω : Domain d} (χ : Test ℝ Ω)
    (u : Distribution ℝ Ω) :
    IsCompact (P102.U4.relativeSupport (localizedDistribution χ u)) :=
  χ.hasCompactSupport.of_isClosed_subset (P102.U4.relativeSupport_top_isClosed _)
    (localizedDistribution_support χ u)

/-- Restriction commutes with the heat operator in the common test model. -/
lemma distributionHeat_restrict {n : ℕ} {V Ω : Domain (n + 1)} (hV : V ≤ Ω)
    (u : Distribution ℝ Ω) :
    P102.U4.restrictDistribution hV (distributionHeat u) =
      distributionHeat (P102.U4.restrictDistribution hV u) := by
  ext φ
  change distributionHeat u (P102.U4.zeroExtension ℝ hV φ) =
    distributionHeat (P102.U4.restrictDistribution hV u) φ
  rw [distributionHeat_pairing, distributionHeat_pairing]
  change u (heatAdjointTest (P102.U4.zeroExtension ℝ hV φ)) =
    u (P102.U4.zeroExtension ℝ hV (heatAdjointTest φ))
  congr 1
  ext x
  simp [heatAdjointTest_apply, P102.U4.zeroExtension, TestFunction.monoCLM_apply, hV]

lemma localizedDistribution_restrict {d : ℕ} {V Ω : Domain d} (hV : V ≤ Ω)
    (χ : Test ℝ Ω) (u : Distribution ℝ Ω) (hχ : ∀ x ∈ V, χ x = 1) :
    P102.U4.restrictDistribution (le_top : V ≤ ⊤) (localizedDistribution χ u) =
      P102.U4.restrictDistribution hV u := by
  ext φ
  change u (localizationTestMap χ (P102.U4.zeroExtension ℝ le_top φ)) =
    u (P102.U4.zeroExtension ℝ hV φ)
  congr 1
  ext x
  simp only [localizationTestMap_apply, P102.U4.zeroExtension, TestFunction.monoCLM_apply,
    le_top, hV, and_self, ite_true]
  by_cases hx : x ∈ V
  · rw [hχ x hx, mul_one]
  · simp [φ.zero_on_compl hx]

/-- A compact localization agrees with u near the chosen point, while its heat
source has compact support separated from that whole neighborhood. -/
theorem exists_compactHeatLocalization {n : ℕ} (Ω : Domain (n + 1))
    (u : Distribution ℝ Ω) (hu : distributionHeat u = 0) (x : Ω) :
    ∃ (V : Domain (n + 1)) (hV : V ≤ Ω)
      (v : Distribution ℝ (⊤ : Domain (n + 1))),
      x.val ∈ V ∧ IsCompact (P102.U4.relativeSupport v) ∧
      P102.U4.restrictDistribution (le_top : V ≤ ⊤) v =
        P102.U4.restrictDistribution hV u ∧
      IsCompact (P102.U4.relativeSupport (distributionHeat v)) ∧
      Disjoint (V : Set (Space (n + 1))) (P102.U4.relativeSupport (distributionHeat v)) := by
  obtain ⟨χ, _, V, hxV, hV, hχ⟩ := P102.U4.cutoff (n + 1) Ω
    ⟨{x.val}, isCompact_singleton⟩ (singleton_subset_iff.mpr x.property)
  let v := localizedDistribution χ u
  have hv := localizedDistribution_compactSupport χ u
  have hrep := localizedDistribution_restrict hV χ u hχ
  refine ⟨V, hV, v, hxV (mem_singleton _), hv, hrep,
    distributionHeat_compactSupport v hv, ?_⟩
  have hz : P102.U4.restrictDistribution (le_top : V ≤ ⊤) (distributionHeat v) = 0 := by
    rw [distributionHeat_restrict, hrep, ← distributionHeat_restrict, hu]
    rfl
  have hvan : P102.U4.VanishesOn (distributionHeat v) V := by
    apply P102.U4.vanishesOn_of_restriction le_top _ (subset_refl _)
    intro φ _
    exact congrArg (fun T : Distribution ℝ V => T φ) hz
  apply disjoint_left.mpr
  intro y hy hs
  exact P102.U4.notMem_relativeSupport_of_vanishes _ V.isOpen (subset_univ _) hvan hy hs

/-- The canonical right-compact construction is symmetric when both supports
are compact. The interchange is applied to an actual compact two-variable test. -/
lemma rightCompactConvolution_comm {d : ℕ} (T S : Distribution ℝ (⊤ : Domain d))
    (hT : IsCompact (P102.U4.relativeSupport T))
    (hS : IsCompact (P102.U4.relativeSupport S)) :
    P102.U4.rightCompactConvolution T S hS = P102.U4.rightCompactConvolution S T hT := by
  obtain ⟨χ, hχ⟩ := P102.U4.exists_supportCutoff S hS
  obtain ⟨η, hη⟩ := P102.U4.exists_supportCutoff T hT
  ext φ
  obtain ⟨ψ, θ, hψ, hθ, he⟩ := P102.U4.distributionInterchange d ℝ T S
    (P102.U4.ConvolutionSymmetryProof.cutoffAddition φ χ η)
  have hTu : T ψ = T (P102.U4.convolutionInnerTest S hS φ) := by
    obtain ⟨U, hU, hηU⟩ := hη
    apply P102.U4.supportLocality d ℝ ⊤ T _ _ U U.isOpen hU
    intro x hx
    rw [hψ, P102.U4.ConvolutionSymmetryProof.cutoffAddition_right S φ χ η hχ,
      hηU x hx, one_mul]
    rfl
  have hSv : S θ = S (P102.U4.convolutionInnerTest T hT φ) := by
    obtain ⟨U, hU, hχU⟩ := hχ
    apply P102.U4.supportLocality d ℝ ⊤ S _ _ U U.isOpen hU
    intro x hx
    rw [hθ, P102.U4.ConvolutionSymmetryProof.cutoffAddition_left T φ χ η hη,
      hχU x hx, one_mul]
    rfl
  exact hTu.symm.trans (he.trans hSv)

/-- A compact smooth kernel is smoothing on either side of convolution. -/
lemma smoothKernel_left {d : ℕ} (S : Distribution ℝ (⊤ : Domain d))
    (hS : IsCompact (P102.U4.relativeSupport S)) (ρ : Test ℝ (⊤ : Domain d)) :
    P102.U4.rightCompactConvolution (regularDistribution ⊤ ρ) S hS =
      regularDistribution ⊤ (P102.U4.localConvolution S ρ) := by
  rw [rightCompactConvolution_comm _ S (P102.U4.regularDistribution_test_compactSupport ρ) hS]
  exact P102.U4.rightCompactConvolution_smoothKernel S ρ

/-- A kernel smooth away from zero gives a smooth convolution off the support
of its compact distribution factor. This does not presume that factor is a function. -/
theorem smoothRepresentative_off_support {d : ℕ} (k : Space d → ℝ)
    (hk : LocallyIntegrable k)
    (hks : ContDiffOn ℝ ∞ k ({0}ᶜ : Set (Space d)))
    (S : Distribution ℝ (⊤ : Domain d))
    (hS : IsCompact (P102.U4.relativeSupport S)) (x : Space d)
    (hx : x ∉ P102.U4.relativeSupport S) :
    ∃ V : Domain d, x ∈ V ∧ ∃ f : Space d → ℝ, ContDiffOn ℝ ∞ f V ∧
      regularDistribution V f = P102.U4.restrictDistribution (le_top : V ≤ ⊤)
        (P102.U4.rightCompactConvolution (regularDistribution ⊤ k) S hS) := by
  classical
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp
    (P102.U4.relativeSupport_top_isClosed S).isOpen_compl x hx
  let V : Domain d := ⟨Metric.ball x (r / 2), Metric.isOpen_ball⟩
  let K : Compacts (Space d) :=
    ⟨Metric.closedBall x (r / 2) - P102.U4.relativeSupport S,
      P102.U4.compact_sub_set (isCompact_closedBall x (r / 2)) hS⟩
  let A : Domain d := ⟨{0}ᶜ, isClosed_singleton.isOpen_compl⟩
  have hKA : (K : Set (Space d)) ⊆ A := by
    rintro z ⟨y, hy, w, hw, rfl⟩ hz
    have heq : y = w := sub_eq_zero.mp (mem_singleton_iff.mp hz)
    have hyb : y ∈ Metric.ball x r :=
      (Metric.closedBall_subset_ball (by linarith : r / 2 < r)) hy
    exact hball hyb (heq ▸ hw)
  obtain ⟨χ, _, U, hKU, _, hχ⟩ := P102.U4.cutoff d A K hKA
  let ρA : Test ℝ A := P102.U4.coefficientTestProduct ⟨k, hks⟩ χ
  let ρ : Test ℝ (⊤ : Domain d) := P102.U4.zeroExtension ℝ le_top ρA
  have hρ (z : Space d) : ρ z = k z * χ z := by
    simp [ρ, ρA, P102.U4.zeroExtension, TestFunction.monoCLM_apply]
  have hρK : EqOn ρ k K := by
    intro z hz
    rw [hρ, hχ z (hKU hz), mul_one]
  have hconv : P102.U4.restrictDistribution (le_top : V ≤ ⊤)
      (P102.U4.rightCompactConvolution (regularDistribution ⊤ k) S hS) =
      P102.U4.restrictDistribution (le_top : V ≤ ⊤)
      (P102.U4.rightCompactConvolution (regularDistribution ⊤ ρ) S hS) := by
    ext φ
    let ψ := P102.U4.zeroExtension ℝ (le_top : V ≤ ⊤) φ
    let θ := P102.U4.convolutionInnerTest S hS ψ
    have hθ : tsupport θ ⊆ K := by
      apply (P102.U4.convolutionInner_tsupport_subset S hS ψ).trans
      apply Set.sub_subset_sub_right
      intro y hy
      apply Metric.ball_subset_closedBall
      apply φ.tsupport_subset
      simpa [ψ, P102.U4.zeroExtension, TestFunction.monoCLM_apply] using hy
    change regularDistribution ⊤ k θ = regularDistribution ⊤ ρ θ
    rw [P102.U4.regular_pairing d ℝ ⊤ k (hk.locallyIntegrableOn _),
      P102.U4.regular_pairing d ℝ ⊤ ρ (ρ.continuous.locallyIntegrable.locallyIntegrableOn _)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => by
      change k z * θ z = ρ z * θ z
      by_cases hz : z ∈ tsupport θ
      · rw [hρK (hθ hz)]
      · rw [image_eq_zero_of_notMem_tsupport hz, mul_zero, mul_zero]
  have hsmooth : ContDiff ℝ ∞ (P102.U4.localConvolution S ρ) := by
    have h := P102.U4.localConvolution_smooth d ℝ ⊤ S ρ
    rw [P102.U4.convolutionDomain_top] at h
    exact contDiffOn_univ.mp h
  refine ⟨V, Metric.mem_ball_self (by linarith), P102.U4.localConvolution S ρ,
    hsmooth.contDiffOn, ?_⟩
  rw [hconv, smoothKernel_left S hS ρ,
    regularDistribution_restrict le_top (hsmooth.continuous.locallyIntegrable.locallyIntegrableOn _)]

/-- A real power multiplied by a flat exponential, extended by zero to the past. -/
def flatPower (a t : ℝ) : ℝ := t ^ a * expNegInvGlue t

lemma flatPower_of_nonpos (a : ℝ) {t : ℝ} (ht : t ≤ 0) : flatPower a t = 0 := by
  simp [flatPower, expNegInvGlue.zero_of_nonpos ht]

lemma flatPower_tendsto (a : ℝ) :
    Filter.Tendsto (flatPower a) (nhds 0) (nhds 0) := by
  unfold flatPower expNegInvGlue
  simp only [mul_ite, mul_zero]
  refine tendsto_const_nhds.if ?_
  simp only [not_le]
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (-a) 1 zero_lt_one).comp
    tendsto_inv_nhdsGT_zero
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp [← Real.rpow_neg_eq_inv_rpow]

lemma flatPower_div (a t : ℝ) : flatPower a t / t = flatPower (a - 1) t := by
  by_cases ht : 0 < t
  · simp only [flatPower, Real.rpow_sub ht, Real.rpow_one]
    ring
  · rw [flatPower_of_nonpos a (le_of_not_gt ht),
      flatPower_of_nonpos (a - 1) (le_of_not_gt ht), zero_div]

lemma flatPower_hasDerivAt (a t : ℝ) :
    HasDerivAt (flatPower a) (a * flatPower (a - 1) t + flatPower (a - 2) t) t := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · rw [flatPower_of_nonpos (a - 1) ht.le, flatPower_of_nonpos (a - 2) ht.le,
      mul_zero, zero_add]
    apply (hasDerivAt_const t 0).congr_of_eventuallyEq
    filter_upwards [gt_mem_nhds ht] with s hs
    exact flatPower_of_nonpos a hs.le
  · simp only [flatPower_of_nonpos _ le_rfl, mul_zero, zero_add]
    rw [hasDerivAt_iff_tendsto_slope]
    convert (flatPower_tendsto (a - 1)).mono_left
      (show nhdsWithin (0 : ℝ) {0}ᶜ ≤ nhds 0 from inf_le_left) using 1
    ext s
    simp [slope_def_field, flatPower_of_nonpos a le_rfl, flatPower_div]
  · have hg : HasDerivAt expNegInvGlue ((t⁻¹)^2 * expNegInvGlue t) t := by
      simpa using expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : Polynomial ℝ) t
    have hp : t ^ a * (t⁻¹)^2 = t ^ (a - 2) := by
      rw [Real.rpow_sub ht, Real.rpow_two]
      ring
    convert (Real.hasDerivAt_rpow_const (Or.inl ht.ne') (p := a)).mul hg using 1
    · rfl
    · simp only [flatPower]
      rw [show a * t ^ (a - 1) * expNegInvGlue t + t ^ a * ((t⁻¹)^2 * expNegInvGlue t) =
        a * (t ^ (a - 1) * expNegInvGlue t) + (t ^ a * (t⁻¹)^2) * expNegInvGlue t by ring, hp]

lemma flatPower_contDiff (a : ℝ) : ContDiff ℝ ∞ (flatPower a) := by
  apply contDiff_all_iff_nat.2 (fun m => ?_) ⊤
  induction m generalizing a with
  | zero =>
      have hd : Differentiable ℝ (flatPower a) := fun t =>
        (flatPower_hasDerivAt a t).differentiableAt
      exact contDiff_zero.mpr hd.continuous
  | succ m ih =>
      rw [show ((m + 1 : ℕ) : ℕ∞ω) = m + 1 from rfl]
      refine contDiff_succ_iff_deriv.mpr
        ⟨fun t => (flatPower_hasDerivAt a t).differentiableAt, by simp, ?_⟩
      convert (contDiff_const.mul (ih (a - 1))).add (ih (a - 2)) using 1
      ext t
      exact (flatPower_hasDerivAt a t).deriv

/-- Away from the spatial origin the causal Gaussian factors through a
globally smooth flat function of rescaled time. -/
lemma causalKernel_eq_flatPower (n : ℕ) (z : Space n × ℝ) (hx : z.1 ≠ 0) :
    causalKernel n z = (Real.pi * ‖z.1‖ ^ 2) ^ (-(n : ℝ) / 2) *
      flatPower (-(n : ℝ) / 2) (4 * z.2 / ‖z.1‖ ^ 2) := by
  have hq : 0 < ‖z.1‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
  by_cases ht : 0 < z.2
  · have hs : 0 < 4 * z.2 / ‖z.1‖ ^ 2 := by positivity
    simp only [causalKernel, P201Specs.Heat.causalKernel, ht, ↓reduceIte,
      P201Specs.Heat.gaussianKernel, flatPower, expNegInvGlue,
      not_le.mpr hs, ↓reduceIte]
    rw [← mul_assoc, ← Real.mul_rpow (by positivity : 0 ≤ Real.pi * ‖z.1‖ ^ 2)
      (le_of_lt hs)]
    have hp : Real.pi * ‖z.1‖ ^ 2 * (4 * z.2 / ‖z.1‖ ^ 2) =
        4 * Real.pi * z.2 := by field_simp
    have he : -(4 * z.2 / ‖z.1‖ ^ 2)⁻¹ = -‖z.1‖ ^ 2 / (4 * z.2) := by
      field_simp
    rw [hp, he]
  · rw [show causalKernel n z = 0 by simp [causalKernel, P201Specs.Heat.causalKernel, ht]]
    rw [flatPower_of_nonpos _ (div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (by norm_num) (le_of_not_gt ht)) hq.le), mul_zero]

lemma causalKernel_contDiffAt_spatial_nonzero (n : ℕ) (z : Space n × ℝ)
    (hx : z.1 ≠ 0) : ContDiffAt ℝ ∞ (causalKernel n) z := by
  have hq : ‖z.1‖ ^ 2 ≠ 0 := (sq_pos_of_pos (norm_pos_iff.mpr hx)).ne'
  have hs : ContDiffAt ℝ ∞ (fun w : Space n × ℝ => ‖w.1‖ ^ 2) z :=
    ((contDiff_norm_sq ℝ).comp contDiff_fst).contDiffAt
  have hpow : ContDiffAt ℝ ∞
      (fun w : Space n × ℝ => (Real.pi * ‖w.1‖ ^ 2) ^ (-(n : ℝ) / 2)) z :=
    (contDiffAt_const.mul hs).rpow_const_of_ne (mul_ne_zero Real.pi_ne_zero hq)
  have hflat : ContDiffAt ℝ ∞
      (fun w : Space n × ℝ => flatPower (-(n : ℝ) / 2) (4 * w.2 / ‖w.1‖ ^ 2)) z :=
    (flatPower_contDiff _).contDiffAt.comp z ((contDiffAt_const.mul contDiffAt_snd).div hs hq)
  apply (hpow.mul hflat).congr_of_eventuallyEq
  have hn : ∀ᶠ w : Space n × ℝ in nhds z, w.1 ≠ 0 :=
    continuous_fst.continuousAt.eventually_ne hx
  filter_upwards [hn] with w hw
  exact causalKernel_eq_flatPower n w hw

lemma causalKernel_contDiffOn (n : ℕ) (hn : 1 ≤ n) :
    ContDiffOn ℝ ∞ (causalKernel n) ({0}ᶜ : Set (Space n × ℝ)) := by
  intro z hz
  apply ContDiffAt.contDiffWithinAt
  by_cases hx : z.1 = 0
  · have ht : z.2 ≠ 0 := by
      intro ht
      apply hz
      simp [Prod.ext_iff, hx, ht]
    rcases lt_or_gt_of_ne ht with ht | ht
    · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      have hneg : ∀ᶠ w : Space n × ℝ in nhds z, w.2 < 0 :=
        continuous_snd.continuousAt.eventually_lt_const ht
      filter_upwards [hneg] with w hw
      simp [causalKernel, P201Specs.Heat.causalKernel, hw.not_gt]
    · have hg : ContDiffAt ℝ ∞ (fun w : Space n × ℝ => gaussianKernel n w.2 w.1) z :=
        (gaussianSmooth n hn).contDiffAt ((isOpen_lt continuous_const continuous_snd).mem_nhds ht)
      apply hg.congr_of_eventuallyEq
      have hpos : ∀ᶠ w : Space n × ℝ in nhds z, 0 < w.2 :=
        continuous_snd.continuousAt.eventually_const_lt ht
      filter_upwards [hpos] with w hw
      simp [causalKernel, P201Specs.Heat.causalKernel, hw]
  · exact causalKernel_contDiffAt_spatial_nonzero n z hx

lemma euclideanCausalKernel_contDiffOn (n : ℕ) (hn : 1 ≤ n) :
    ContDiffOn ℝ ∞ (euclideanCausalKernel n) ({0}ᶜ : Set (Space (n + 1))) := by
  apply (causalKernel_contDiffOn n hn).comp
    (spaceTimeCoordinates n).contDiff.contDiffOn
  intro z hz
  change (spaceTimeCoordinates n) z ≠ 0
  intro heq
  exact hz ((spaceTimeCoordinates n).injective (heq.trans (map_zero _).symm))

/-- A homogeneous distributional solution has a smooth representative near
each point, by compact localization and convolution with the causal kernel. -/
theorem localSmoothRepresentative {n : ℕ} (hn : 1 ≤ n) (Ω : Domain (n + 1))
    (u : Distribution ℝ Ω) (hu : distributionHeat u = 0) (x : Ω) :
    ∃ (V : Domain (n + 1)) (hV : V ≤ Ω), x.val ∈ V ∧
      ∃ f : Space (n + 1) → ℝ, ContDiffOn ℝ ∞ f V ∧
        regularDistribution V f = P102.U4.restrictDistribution hV u := by
  obtain ⟨V, hV, v, hxV, hv, hrep, hS, hdis⟩ :=
    exists_compactHeatLocalization Ω u hu x
  have hinv := compactHeat_inverse
    (regularDistribution (⊤ : Domain (n + 1)) (euclideanCausalKernel n))
    v hv (euclideanCausalFundamental n hn)
  have hxS : x.val ∉ P102.U4.relativeSupport (distributionHeat v) :=
    fun hx => (disjoint_left.mp hdis) hxV hx
  obtain ⟨W, hxW, f, hf, hfrep⟩ := smoothRepresentative_off_support
    (euclideanCausalKernel n) (euclideanCausalKernel_locallyIntegrable n hn)
    (euclideanCausalKernel_contDiffOn n hn) (distributionHeat v) hS x.val hxS
  refine ⟨V ⊓ W, inf_le_left.trans hV, ⟨hxV, hxW⟩, f,
    hf.mono (show (V ⊓ W : Domain (n + 1)) ≤ W from inf_le_right), ?_⟩
  have hloc : regularDistribution W f =
      P102.U4.restrictDistribution (le_top : W ≤ ⊤) v := by
    rw [hfrep, hinv]
  calc
    regularDistribution (V ⊓ W) f = P102.U4.restrictDistribution
        (inf_le_right : V ⊓ W ≤ W) (regularDistribution W f) := by
      symm
      exact regularDistribution_restrict inf_le_right
        (hf.continuousOn.locallyIntegrableOn W.isOpen.measurableSet)
    _ = P102.U4.restrictDistribution (le_top : V ⊓ W ≤ ⊤) v := by
      rw [hloc, P102.U4.restrictionTransitive]
    _ = P102.U4.restrictDistribution (inf_le_left : V ⊓ W ≤ V)
        (P102.U4.restrictDistribution (le_top : V ≤ ⊤) v) := by
      rw [P102.U4.restrictionTransitive]
    _ = P102.U4.restrictDistribution (inf_le_left.trans hV) u := by
      rw [hrep, P102.U4.restrictionTransitive]

/-- Every distributional homogeneous heat solution on an arbitrary open set
is represented by a smooth pointwise caloric function. -/
theorem distributionRegularity : P201Specs.Heat.distributionRegularityStatement := by
  intro n hn Ω u hu
  obtain ⟨f, hf, hrep⟩ := smoothRepresentative_of_local u
    (localSmoothRepresentative hn Ω u hu)
  exact ⟨f, hf, hrep, (isCaloric_iff hf).mpr
    (classicalHeat_eq_zero_of_represents hf hu hrep)⟩

end P201.Heat
