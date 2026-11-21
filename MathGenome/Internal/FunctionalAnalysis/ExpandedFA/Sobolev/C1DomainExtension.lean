import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.C1DomainExtension
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.HalfSpaceExtension
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Distributions.SmoothPartitionOfUnity
import Batteries.Tactic.OpenPrivate
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

/-! Simultaneous Sobolev extension on C¹ domains with compact boundary.
The construction includes nonlinear chart transport, smooth localization,
relative zero extension, finite assembly, one bounded output neighborhood
for bounded domains, and ambient smooth density for finite exponents. -/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal Manifold

namespace ExpandedFA.Sobolev.C1Extension
open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω Λ : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Compactness only concerns the boundary, so this selection also applies
to exterior domains and does not ask for a bounded interior patch. -/
theorem finite_boundary_charts :
    Specs.ExpandedFA.Sobolev.C1DomainExtension.FiniteBoundaryCharts := by
  classical
  intro d Ω hΩ hcompact
  choose i Φ hx hzero hΦ hInv hdomain using
    (fun x : frontier (Ω : Set (Domain d)) => hΩ x x.property)
  obtain ⟨s, hs⟩ := hcompact.elim_finite_subcover
    (fun x : frontier (Ω : Set (Domain d)) => (Φ x).source)
    (fun x => (Φ x).open_source)
    (fun x hx' => mem_iUnion.mpr ⟨⟨x, hx'⟩, hx ⟨x, hx'⟩⟩)
  refine ⟨s.card, fun j => i (s.equivFin.symm j).val,
    fun j => Φ (s.equivFin.symm j).val, ?_, ?_⟩
  · intro j
    exact ⟨hΦ _, hInv _, hdomain _⟩
  · intro x hx'
    obtain ⟨b, hb⟩ := mem_iUnion.mp (hs hx')
    obtain ⟨hbs, hxsource⟩ := mem_iUnion.mp hb
    refine mem_iUnion.mpr ⟨s.equivFin ⟨b, hbs⟩, ?_⟩
    simpa using hxsource

/-- Restriction of scalar Lp classes to a smaller open set. -/
def restrictLp (h : Ω ≤ Λ) (u : DomainLp 𝕜 Λ p) : DomainLp 𝕜 Ω p :=
  ((Lp.memLp u).mono_measure (Measure.restrict_mono h le_rfl)).toLp u

theorem restrictLp_coe (h : Ω ≤ Λ) (u : DomainLp 𝕜 Λ p) :
    restrictLp h u =ᵐ[volume.restrict (Ω : Set (Domain d))] u :=
  MemLp.coeFn_toLp _

theorem restrictLp_norm_le (h : Ω ≤ Λ) (u : DomainLp 𝕜 Λ p) :
    ‖restrictLp h u‖ ≤ ‖u‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (restrictLp_coe h u)]
  exact ENNReal.toReal_mono (Lp.memLp u).ne
    (eLpNorm_mono_measure u (Measure.restrict_mono h le_rfl))

/-- Complex scalar linearity is proved on a.e. classes as well. -/
def restrictLpLM (h : Ω ≤ Λ) : DomainLp 𝕜 Λ p →ₗ[𝕜] DomainLp 𝕜 Ω p where
  toFun := restrictLp h
  map_add' u v := by
    apply Lp.ext
    filter_upwards [restrictLp_coe h (u + v), restrictLp_coe h u,
      restrictLp_coe h v, Lp.coeFn_add (restrictLp h u) (restrictLp h v),
      (Lp.coeFn_add u v).filter_mono
        (ae_mono (Measure.restrict_mono h le_rfl))] with x huv hu hv hadd hsum
    rw [huv, hadd, hsum]
    simp only [Pi.add_apply, hu, hv]
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [restrictLp_coe h (c • u), restrictLp_coe h u,
      Lp.coeFn_smul c (restrictLp h u),
      (Lp.coeFn_smul c u).filter_mono
        (ae_mono (Measure.restrict_mono h le_rfl))] with x hcu hu hsmul hsource
    change restrictLp h (c • u) x = (c • restrictLp h u) x
    rw [hcu, hsmul, hsource]
    simp only [Pi.smul_apply, hu]

/-- The same test, viewed on a larger open domain. -/
def enlargeTest (h : Ω ≤ Λ) (φ : Tests 𝕜 Ω) : Tests 𝕜 Λ :=
  ⟨φ, φ.contDiff, φ.hasCompactSupport, φ.tsupport_subset.trans h⟩

theorem enlargeTest_partial (h : Ω ≤ Λ) (φ : Tests 𝕜 Ω) (w : List (Fin d)) :
    enlargeTest h (testPartialCLM w φ) = testPartialCLM w (enlargeTest h φ) := by
  apply TestFunction.ext
  intro x
  change testPartialCLM w φ x = testPartialCLM w (enlargeTest h φ) x
  rw [testPartial_formula, testPartial_formula]
  rfl

/-- Locality of the pairing, proved with the actual restricted measures. -/
theorem lpDistribution_restrict (h : Ω ≤ Λ) (u : DomainLp 𝕜 Λ p)
    (φ : Tests 𝕜 Ω) :
    lpDistribution (restrictLp h u) φ = lpDistribution u (enlargeTest h φ) := by
  rw [lpDistribution_apply, lpDistribution_apply]
  calc
    (∫ x in (Ω : Set (Domain d)), φ x * restrictLp h u x) =
        ∫ x in (Ω : Set (Domain d)), φ x * u x :=
      integral_congr_ae ((restrictLp_coe h u).mono (fun _ hx => congrArg (φ _ * ·) hx))
    _ = ∫ x, φ x * u x ∂(volume.restrict (Λ : Set (Domain d))) := by
      rw [← Measure.restrict_restrict_of_subset h]
      exact setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => by simp [φ.zero_on_compl hx])
    _ = _ := rfl

/-- Restriction preserves every weak derivative, including degree zero. -/
theorem restrictTuple_mem_graph {m : ℕ} (h : Ω ≤ Λ)
    (u : SpaceValue 𝕜 d Λ m p) :
    (WithLp.toLp 1 (fun α => restrictLp h (u.val α))) ∈ derivativeGraph 𝕜 Ω m p := by
  intro α
  ext φ
  change lpDistribution (restrictLp h (u.val α)) φ =
    (-1 : 𝕜) ^ (multiIndexWord (natIndex α)).length *
      lpDistribution (restrictLp h (u.val (zeroIndex d m)))
        (testPartialCLM (multiIndexWord (natIndex α)) φ)
  rw [lpDistribution_restrict, lpDistribution_restrict, enlargeTest_partial]
  exact congrArg (fun T : ScalarDistribution 𝕜 Λ => T (enlargeTest h φ)) (u.property α)

/-- The canonical all-orders restriction operator on derivative graphs. -/
def restrictSobolev {m : ℕ} (h : Ω ≤ Λ) :
    SpaceValue 𝕜 d Λ m p →L[𝕜] SpaceValue 𝕜 d Ω m p :=
  LinearMap.mkContinuous
    { toFun := fun u => ⟨WithLp.toLp 1 (fun α => restrictLp h (u.val α)),
          restrictTuple_mem_graph h u⟩
      map_add' := by
        intro u v
        apply Subtype.ext
        apply PiLp.ext
        intro α
        exact (restrictLpLM h).map_add _ _
      map_smul' := by
        intro c u
        apply Subtype.ext
        apply PiLp.ext
        intro α
        exact (restrictLpLM h).map_smul c _ }
    1 (fun u => by
      change ‖WithLp.toLp 1 (fun α => restrictLp h (u.val α))‖ ≤ 1 * ‖u.val‖
      rw [one_mul, PiLp.norm_eq_of_L1, PiLp.norm_eq_of_L1]
      exact Finset.sum_le_sum (fun α _ => restrictLp_norm_le h (u.val α)))

theorem restrictSobolev_coe {m : ℕ} (h : Ω ≤ Λ)
    (u : SpaceValue 𝕜 d Λ m p) (α : DerivativeIndex d m) :
    (restrictSobolev h u).val α =ᵐ[volume.restrict (Ω : Set (Domain d))] u.val α :=
  restrictLp_coe h _

theorem restrictSobolev_norm_le {m : ℕ} (h : Ω ≤ Λ)
    (u : SpaceValue 𝕜 d Λ m p) : ‖restrictSobolev h u‖ ≤ ‖u‖ := by
  change ‖WithLp.toLp 1 (fun α => restrictLp h (u.val α))‖ ≤ ‖u.val‖
  rw [PiLp.norm_eq_of_L1, PiLp.norm_eq_of_L1]
  exact Finset.sum_le_sum (fun α _ => restrictLp_norm_le h (u.val α))

/-- An extension is a right inverse on the full graph, since the
order-zero component determines every weak derivative. -/
theorem restrict_extension (E : SpaceValue 𝕜 d Ω 1 p →L[𝕜] SpaceValue 𝕜 d ⊤ 1 p)
    (hE : IsExtension Ω E) (u : SpaceValue 𝕜 d Ω 1 p) :
    restrictSobolev (le_top : Ω ≤ ⊤) (E u) = u := by
  apply sobolev_underlying_injective 𝕜 d Ω 1 p
  exact Lp.ext ((restrictSobolev_coe le_top (E u) _).trans (hE u))

/-- Smooth ambient approximation, restricted through a right inverse, proves
smooth-up-to-boundary density. This uses finite-p density only on the whole
space, so it makes no boundary density assumption. -/
theorem smooth_up_to_boundary_density_of_extension :
    Specs.ExpandedFA.Sobolev.C1DomainExtension.DensityOfExtension := by
  intro 𝕜 _ d Ω p _ hp E hE u
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨v, ⟨f, hf, hvf⟩, hv⟩ :=
    Metric.mem_closure_iff.mp
      (Smoothing.smooth_density 𝕜 d ⊤ 1 p hp (E u)) ε hε
  let R : SpaceValue 𝕜 d ⊤ 1 p →L[𝕜] SpaceValue 𝕜 d Ω 1 p :=
    restrictSobolev le_top
  refine ⟨R v, ⟨f, ?_, ?_⟩, ?_⟩
  · exact contDiffOn_univ.mp hf
  · exact (restrictSobolev_coe le_top v _).trans
      (hvf.filter_mono (ae_mono
        (by simpa using (Measure.restrict_le_self (μ := (volume : Measure (Domain d)))
          (s := (Ω : Set (Domain d)))))))
  · have hright : R (E u) = u := restrict_extension E hE u
    calc
      dist u (R v) = ‖R v - R (E u)‖ := by rw [hright, dist_comm u, dist_eq_norm]
      _ = ‖R (v - E u)‖ := by rw [map_sub]
      _ ≤ ‖v - E u‖ := restrictSobolev_norm_le le_top _
      _ = dist v (E u) := (dist_eq_norm _ _).symm
      _ < ε := by simpa only [dist_comm] using hv

/-- Once the single extension formula is constructed, its finite-p density
conclusion follows without additional boundary geometry. -/
theorem smooth_density_of_simultaneous_extension
    (h : HasSimultaneousExtension (𝕜 := 𝕜) Ω) (hp : p ≠ ∞) :
    Dense (SmoothUpToBoundary (𝕜 := 𝕜) Ω p) := by
  obtain ⟨_, E, hE, _, _⟩ := h
  exact smooth_up_to_boundary_density_of_extension 𝕜 d Ω p hp (E p) (hE p)

theorem smooth_density_of_extension_exists :
    Specs.ExpandedFA.Sobolev.C1DomainExtension.DensityConsequence := by
  intro hext 𝕜 _ d Ω hΩ hcompact p _ hp
  exact smooth_density_of_simultaneous_extension (hext 𝕜 d Ω hΩ hcompact) hp

/-- The whole-space boundary case in every dimension, including dimension zero. -/
theorem simultaneous_extension_top :
    Specs.ExpandedFA.Sobolev.C1DomainExtension.WholeSpaceExtension := by
  intro 𝕜 _ d
  refine ⟨LinearMap.id, fun p _ => ContinuousLinearMap.id 𝕜 _, ?_, ?_, ?_⟩
  · intro p _ u
    exact Filter.EventuallyEq.rfl
  · intro p _ u f hf
    simpa using hf.symm
  · intro hbounded
    refine ⟨⊤, hbounded, ?_, ?_⟩
    · simp
    · intro p _ u
      exact Filter.Eventually.of_forall (fun x hx => (hx (by simp)).elim)

/-- Empty domains impose no data; the zero map is compatible at every p. -/
theorem simultaneous_extension_bot :
    Specs.ExpandedFA.Sobolev.C1DomainExtension.EmptyExtension := by
  intro 𝕜 _ d
  refine ⟨0, fun p _ => 0, ?_, ?_, ?_⟩
  · intro p _ u
    simp only [zero_apply, Opens.coe_bot, Measure.restrict_empty,
      ae_zero]
    exact Filter.eventually_bot
  · intro p _ u f _
    simpa using (Lp.coeFn_zero 𝕜 p (volume.restrict
      ((⊤ : Opens (Domain d)) : Set (Domain d))))
  · intro _
    refine ⟨⊥, by simp, by simp, ?_⟩
    intro p _ u
    have hzero := Lp.coeFn_zero 𝕜 p (volume.restrict
      ((⊤ : Opens (Domain d)) : Set (Domain d)))
    simp


/-! Smooth ambient multipliers, with a bound independent of the exponent.
These apply to boundary patches because the coefficient need not vanish near
 the physical boundary of the domain. -/

open HalfSpace
open private firstJetCoordinate firstJetCoordinate_spec firstJetCoordinate_coordinate
  from MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.HalfSpaceExtension

/-- Multiplication by a bounded continuous ambient scalar function on Lp. -/
def boundedMulLp (a : Domain d → 𝕜) (ha : Continuous a) (C : ℝ)
    (hC : ∀ x, ‖a x‖ ≤ C) (u : DomainLp 𝕜 Ω p) : DomainLp 𝕜 Ω p :=
  ((Lp.memLp u).of_le_mul (f := fun x => a x * u x) (c := C)
    (ha.aestronglyMeasurable.mul (Lp.aestronglyMeasurable u))
    (Filter.Eventually.of_forall fun x => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _))).toLp _

theorem boundedMulLp_coe (a : Domain d → 𝕜) (ha : Continuous a) (C : ℝ)
    (hC : ∀ x, ‖a x‖ ≤ C) (u : DomainLp 𝕜 Ω p) :
    boundedMulLp a ha C hC u =ᵐ[volume.restrict (Ω : Set (Domain d))]
      fun x => a x * u x := MemLp.coeFn_toLp _

theorem boundedMulLp_norm_le (a : Domain d → 𝕜) (ha : Continuous a) (C : ℝ)
    (hC : ∀ x, ‖a x‖ ≤ C) (u : DomainLp 𝕜 Ω p) :
    ‖boundedMulLp a ha C hC u‖ ≤ C * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [boundedMulLp_coe a ha C hC u] with x hx
  rw [hx, norm_mul]
  exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)

def boundedMulLpLM (a : Domain d → 𝕜) (ha : Continuous a) (C : ℝ)
    (hC : ∀ x, ‖a x‖ ≤ C) : DomainLp 𝕜 Ω p →ₗ[𝕜] DomainLp 𝕜 Ω p where
  toFun := boundedMulLp a ha C hC
  map_add' u v := by
    apply Lp.ext
    filter_upwards [boundedMulLp_coe a ha C hC (u + v),
      boundedMulLp_coe a ha C hC u, boundedMulLp_coe a ha C hC v,
      Lp.coeFn_add u v,
      Lp.coeFn_add (boundedMulLp a ha C hC u) (boundedMulLp a ha C hC v)] with x h₁ h₂ h₃ h₄ h₅
    rw [h₁, h₅, h₄]
    simp only [Pi.add_apply, h₂, h₃]
    exact mul_add _ _ _
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [boundedMulLp_coe a ha C hC (c • u), boundedMulLp_coe a ha C hC u,
      Lp.coeFn_smul c u, Lp.coeFn_smul c (boundedMulLp a ha C hC u)] with x h₁ h₂ h₃ h₄
    change boundedMulLp a ha C hC (c • u) x = (c • boundedMulLp a ha C hC u) x
    rw [h₁, h₄, h₃]
    simp only [Pi.smul_apply, h₂, smul_eq_mul]
    ring

def ambientCoefficient (a : Domain d → 𝕜) (ha : ContDiff ℝ (⊤ : ℕ∞) a) :
    SmoothCoefficient 𝕜 Ω := ⟨a, ha.contDiffOn⟩

theorem boundedMulLp_distribution (a : Domain d → 𝕜)
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (C : ℝ) (hC : ∀ x, ‖a x‖ ≤ C)
    (u : DomainLp 𝕜 Ω p) :
    lpDistribution (boundedMulLp a ha.continuous C hC u) =
      multiplyDistribution (ambientCoefficient a ha) (lpDistribution u) := by
  ext φ
  simp only [lpDistribution_apply, multiplyDistribution_apply]
  apply integral_congr_ae
  filter_upwards [boundedMulLp_coe a ha.continuous C hC u] with x hx
  change φ x * boundedMulLp a ha.continuous C hC u x = (a x * φ x) * u x
  rw [hx]
  ring

/-- A scalar coefficient and all its first partials have one uniform bound. -/
def ambientMultiplyJet (a : Domain d → 𝕜) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (C : ℝ) (hC : ∀ x, ‖a x‖ ≤ C)
    (hD : ∀ j x, ‖partialFunction [j] a x‖ ≤ C)
    (u : DerivativeTuple 𝕜 Ω 1 p) : DerivativeTuple 𝕜 Ω 1 p :=
  WithLp.toLp 1 (fun α => if hα : α = zeroIndex d 1 then
    boundedMulLp a ha.continuous C hC (u (zeroIndex d 1)) else
    boundedMulLp a ha.continuous C hC (u α) +
      boundedMulLp (partialFunction [firstJetCoordinate α hα] a)
        (Smoothing.partialFunction_contDiff _ a ha).continuous C (hD _) (u (zeroIndex d 1)))

@[simp] theorem ambientMultiplyJet_zero (a : Domain d → 𝕜)
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (C : ℝ) (hC : ∀ x, ‖a x‖ ≤ C)
    (hD : ∀ j x, ‖partialFunction [j] a x‖ ≤ C) (u : DerivativeTuple 𝕜 Ω 1 p) :
    ambientMultiplyJet a ha C hC hD u (zeroIndex d 1) =
      boundedMulLp a ha.continuous C hC (u (zeroIndex d 1)) := by
  simp [ambientMultiplyJet]

@[simp] theorem ambientMultiplyJet_coordinate (a : Domain d → 𝕜)
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (C : ℝ) (hC : ∀ x, ‖a x‖ ≤ C)
    (hD : ∀ j x, ‖partialFunction [j] a x‖ ≤ C)
    (u : DerivativeTuple 𝕜 Ω 1 p) (j : Fin d) :
    ambientMultiplyJet a ha C hC hD u (coordinateIndex j) =
      boundedMulLp a ha.continuous C hC (u (coordinateIndex j)) +
        boundedMulLp (partialFunction [j] a)
          (Smoothing.partialFunction_contDiff _ a ha).continuous C (hD j) (u (zeroIndex d 1)) := by
  simp [ambientMultiplyJet]

theorem ambientMultiplyJet_mem (a : Domain d → 𝕜)
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (C : ℝ) (hC : ∀ x, ‖a x‖ ≤ C)
    (hD : ∀ j x, ‖partialFunction [j] a x‖ ≤ C) (u : SpaceValue 𝕜 d Ω 1 p) :
    ambientMultiplyJet a ha C hC hD u.val ∈ derivativeGraph 𝕜 Ω 1 p := by
  apply firstJet_mem_of_coordinateWeak
  intro j
  change lpDistribution (ambientMultiplyJet a ha C hC hD u.val (coordinateIndex j)) =
    -(lpDistribution (ambientMultiplyJet a ha C hC hD u.val (zeroIndex d 1))).comp (testPartialCLM [j])
  rw [ambientMultiplyJet_coordinate, ambientMultiplyJet_zero]
  change lpDistributionLM (_ + _) = _
  rw [map_add]
  change lpDistribution (boundedMulLp a ha.continuous C hC (u.val (coordinateIndex j))) +
    lpDistribution (boundedMulLp (partialFunction [j] a)
      (Smoothing.partialFunction_contDiff _ a ha).continuous C (hD j) (u.val (zeroIndex d 1))) = _
  rw [boundedMulLp_distribution a ha,
    boundedMulLp_distribution _ (Smoothing.partialFunction_contDiff _ a ha),
    boundedMulLp_distribution a ha]
  have hj := coordinate_weak_derivatives_on u j
  have hcoeff : ambientCoefficient (Ω := Ω) (partialFunction [j] a)
      (Smoothing.partialFunction_contDiff _ a ha) = coefficientPartial j (ambientCoefficient a ha) := rfl
  rw [hcoeff, hj, distribution_leibniz]
  exact add_comm _ _

theorem ambientMultiplyJet_norm_le (a : Domain d → 𝕜)
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ x, ‖a x‖ ≤ C)
    (hD : ∀ j x, ‖partialFunction [j] a x‖ ≤ C) (u : DerivativeTuple 𝕜 Ω 1 p) :
    ‖ambientMultiplyJet a ha C hC hD u‖ ≤
      (Fintype.card (DerivativeIndex d 1) * (2 * C)) * ‖u‖ := by
  classical
  have hcomponent (α : DerivativeIndex d 1) : ‖u α‖ ≤ ‖u‖ := by
    rw [PiLp.norm_eq_of_L1]
    exact Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ α)
  have hmul (α : DerivativeIndex d 1) :
      ‖boundedMulLp a ha.continuous C hC (u α)‖ ≤ C * ‖u‖ :=
    (boundedMulLp_norm_le _ _ _ _ _).trans (mul_le_mul_of_nonneg_left (hcomponent α) hC0)
  have hb (α : DerivativeIndex d 1) :
      ‖ambientMultiplyJet a ha C hC hD u α‖ ≤ (2 * C) * ‖u‖ := by
    simp only [ambientMultiplyJet, PiLp.toLp_apply]
    split_ifs with hα
    · exact (hmul _).trans (by nlinarith [mul_nonneg hC0 (norm_nonneg u)])
    · have hd := boundedMulLp_norm_le (partialFunction [firstJetCoordinate α hα] a)
        (Smoothing.partialFunction_contDiff _ a ha).continuous C (hD _) (u (zeroIndex d 1))
      have hd' := mul_le_mul_of_nonneg_left (hcomponent (zeroIndex d 1)) hC0
      exact (norm_add_le _ _).trans (by nlinarith [hmul α])
  rw [PiLp.norm_eq_of_L1]
  calc
    ∑ α, ‖ambientMultiplyJet a ha C hC hD u α‖ ≤
        ∑ _α : DerivativeIndex d 1, (2 * C) * ‖u‖ := Finset.sum_le_sum (fun α _ => hb α)
    _ = _ := by simp [mul_assoc]

/-- Bounded smooth ambient multiplication acts on the canonical graph at
all exponents, including infinity. The weak rule was proved directly on tests. -/
def ambientMultiply (a : Domain d → 𝕜) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ x, ‖a x‖ ≤ C)
    (hD : ∀ j x, ‖partialFunction [j] a x‖ ≤ C) :
    SpaceValue 𝕜 d Ω 1 p →L[𝕜] SpaceValue 𝕜 d Ω 1 p :=
  LinearMap.mkContinuous
    { toFun := fun u => ⟨ambientMultiplyJet a ha C hC hD u.val,
          ambientMultiplyJet_mem a ha C hC hD u⟩
      map_add' := by
        intro u v
        apply sobolev_underlying_injective 𝕜 d Ω 1 p
        change ambientMultiplyJet a ha C hC hD (u + v).val (zeroIndex d 1) =
          ambientMultiplyJet a ha C hC hD u.val (zeroIndex d 1) +
          ambientMultiplyJet a ha C hC hD v.val (zeroIndex d 1)
        simp only [ambientMultiplyJet_zero, Submodule.coe_add, PiLp.add_apply]
        exact (boundedMulLpLM a ha.continuous C hC).map_add _ _
      map_smul' := by
        intro c u
        apply sobolev_underlying_injective 𝕜 d Ω 1 p
        change ambientMultiplyJet a ha C hC hD (c • u).val (zeroIndex d 1) =
          c • ambientMultiplyJet a ha C hC hD u.val (zeroIndex d 1)
        simp only [ambientMultiplyJet_zero, Submodule.coe_smul, PiLp.smul_apply]
        exact (boundedMulLpLM a ha.continuous C hC).map_smul _ _ }
    (Fintype.card (DerivativeIndex d 1) * (2 * C))
    (fun u => ambientMultiplyJet_norm_le a ha C hC0 hC hD u.val)

theorem ambientMultiply_coe (a : Domain d → 𝕜) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ x, ‖a x‖ ≤ C)
    (hD : ∀ j x, ‖partialFunction [j] a x‖ ≤ C) (u : SpaceValue 𝕜 d Ω 1 p) :
    (ambientMultiply a ha C hC0 hC hD u).val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))]
      fun x => a x * u.val (zeroIndex d 1) x := by
  change ambientMultiplyJet a ha C hC hD u.val (zeroIndex d 1) =ᵐ[_] _
  rw [ambientMultiplyJet_zero]
  exact boundedMulLp_coe _ _ _ _ _


theorem ambient_smooth_multiplier :
    Specs.ExpandedFA.Sobolev.C1DomainExtension.AmbientSmoothMultiplier := by
  intro 𝕜 _ d Ω p _ a ha C hC0 hC hD
  refine ⟨ambientMultiply a ha C hC0 hC hD, fun u => ambientMultiply_coe a ha C hC0 hC hD u, ?_⟩
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  exact fun u => ambientMultiplyJet_norm_le a ha C hC0 hC hD u.val

/-- Compact smooth ambient cutoffs and their first partials admit a common
finite bound, chosen before the Sobolev exponent. -/
theorem ambient_test_bounds (η : Tests 𝕜 (⊤ : Opens (Domain d))) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ x, ‖η x‖ ≤ C) ∧
      ∀ j x, ‖partialFunction [j] η x‖ ≤ C := by
  classical
  obtain ⟨A, hA⟩ := η.hasCompactSupport.exists_bound_of_continuous η.continuous
  have hd (j : Fin d) : ∃ B : ℝ, ∀ x, ‖testPartialCLM [j] η x‖ ≤ B :=
    (testPartialCLM [j] η).hasCompactSupport.exists_bound_of_continuous
      (testPartialCLM [j] η).continuous
  choose B hB using hd
  let C := max 0 A + ∑ j, max 0 (B j)
  have hsum : 0 ≤ ∑ j, max 0 (B j) := Finset.sum_nonneg (fun _ _ => le_max_left _ _)
  refine ⟨C, add_nonneg (le_max_left _ _) hsum, ?_, ?_⟩
  · intro x
    exact (hA x).trans ((le_max_right _ _).trans (le_add_of_nonneg_right hsum))
  · intro j x
    have hj : max 0 (B j) ≤ ∑ k, max 0 (B k) :=
      Finset.single_le_sum (fun _ _ => le_max_left _ _) (Finset.mem_univ j)
    rw [← testPartial_formula]
    exact (hB j x).trans ((le_max_right _ _).trans
      (hj.trans (le_add_of_nonneg_left (le_max_left _ _))))

/-- A cutoff equal to one on the closure, supported in a single bounded open
neighborhood. This retains bounded empty domains and dimension zero. -/
theorem exists_bounded_ambient_cutoff (hΩ : Bornology.IsBounded (Ω : Set (Domain d))) :
    ∃ (U : Opens (Domain d)) (η : Tests 𝕜 (⊤ : Opens (Domain d))),
      Bornology.IsBounded (U : Set (Domain d)) ∧ closure (Ω : Set (Domain d)) ⊆ U ∧
      (∀ x ∈ closure (Ω : Set (Domain d)), η x = 1) ∧
      (∀ x, x ∉ U → η x = 0) := by
  obtain ⟨R, hR, hbound⟩ := hΩ.closure.exists_pos_norm_lt
  let V : Set (Domain d) := Metric.ball 0 R
  have hsub : closure (Ω : Set (Domain d)) ⊆ V := by
    intro x hx
    simpa [V, Metric.mem_ball, dist_zero_right] using hbound x hx
  obtain ⟨f, hf, _, hfs, hfone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞))
      Metric.isOpen_ball isClosed_closure hsub
  have hfcompact : HasCompactSupport f := by
    change IsCompact (closure (Function.support f))
    rw [hfs]
    exact Metric.isCompact_of_isClosed_isBounded isClosed_closure Metric.isBounded_ball.closure
  let η₀ : Tests ℝ (⊤ : Opens (Domain d)) := ⟨f, hf, hfcompact, by simp⟩
  let η : Tests 𝕜 (⊤ : Opens (Domain d)) := Smoothing.liftRealTest η₀
  refine ⟨⟨V, Metric.isOpen_ball⟩, η, Metric.isBounded_ball, hsub, ?_, ?_⟩
  · intro x hx
    change (RCLike.ofReal (f x) : 𝕜) = 1
    rw [(hfone x).mp hx, RCLike.ofReal_one]
  · intro x hx
    have hx' : x ∉ Function.support f := by rw [hfs]; exact hx
    have hfzero : f x = 0 := Function.notMem_support.mp hx'
    change (RCLike.ofReal (f x) : 𝕜) = 0
    simp [hfzero]

/-- Every compatible common extension can be normalized to satisfy the
bounded-domain support clause without changing its exponent range. -/
theorem bounded_support_reduction :
    Specs.ExpandedFA.Sobolev.C1DomainExtension.BoundedSupportReduction := by
  classical
  intro 𝕜 _ d Ω h
  obtain ⟨T, E, hE, hT⟩ := h
  by_cases hbounded : Bornology.IsBounded (Ω : Set (Domain d))
  · obtain ⟨U, η, hU, hΩU, hηone, hηzero⟩ :=
      exists_bounded_ambient_cutoff (𝕜 := 𝕜) hbounded
    obtain ⟨C, hC0, hC, hD⟩ := ambient_test_bounds η
    let M : ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)],
        SpaceValue 𝕜 d ⊤ 1 p →L[𝕜] SpaceValue 𝕜 d ⊤ 1 p :=
      fun p _ => ambientMultiply η η.contDiff C hC0 hC hD
    let S : (Domain d → 𝕜) →ₗ[𝕜] (Domain d → 𝕜) :=
      { toFun := fun f x => η x * T f x
        map_add' := fun f g => by funext x; simp [map_add, mul_add]
        map_smul' := fun c f => by funext x; simp [map_smul, smul_eq_mul, mul_left_comm] }
    refine ⟨S, fun p _ => (M p).comp (E p), ?_, ?_, ?_⟩
    · intro p _ u
      have hm := ambientMultiply_coe η η.contDiff C hC0 hC hD (E p u)
      have hm' := hm.filter_mono (ae_mono (Measure.restrict_mono (le_top : Ω ≤ ⊤) le_rfl))
      filter_upwards [hm', hE p u, ae_restrict_mem Ω.isOpen.measurableSet] with x hx hEx hxΩ
      change (M p (E p u)).val (zeroIndex d 1) x = _
      rw [hx, hEx, hηone x (subset_closure hxΩ), one_mul]
    · intro p _ u f hf
      have hm := ambientMultiply_coe η η.contDiff C hC0 hC hD (E p u)
      have hmfull : (M p (E p u)).val (zeroIndex d 1) =ᵐ[volume]
          fun x => η x * (E p u).val (zeroIndex d 1) x := by simpa [M] using hm
      have ht := hT p u f hf
      filter_upwards [hmfull, ht] with x hx ht'
      change (M p (E p u)).val (zeroIndex d 1) x = η x * T f x
      rw [hx, ht']
    · intro _
      refine ⟨U, hU, hΩU, ?_⟩
      intro p _ u
      have hm := ambientMultiply_coe η η.contDiff C hC0 hC hD (E p u)
      have hmfull : (M p (E p u)).val (zeroIndex d 1) =ᵐ[volume]
          fun x => η x * (E p u).val (zeroIndex d 1) x := by simpa [M] using hm
      filter_upwards [hmfull] with x hx hxU
      change (M p (E p u)).val (zeroIndex d 1) x = 0
      rw [hx, hηzero x hxU, zero_mul]
  · exact ⟨T, E, hE, hT, fun h' => (hbounded h').elim⟩


/-- A target test can be replaced by a source test agreeing near a relatively
closed support. The support need not be bounded or closed in the ambient space. -/
theorem exists_test_agree_near_support (h : Ω ≤ Λ) (K : Set (Domain d))
    (hK : IsClosed (K ∪ (Λ : Set (Domain d))ᶜ)) (hKΩ : K ⊆ Ω)
    (φ : Tests 𝕜 Λ) :
    ∃ ψ : Tests 𝕜 Ω, ∀ x ∈ K, (ψ : Domain d → 𝕜) =ᶠ[nhds x] φ := by
  let L := (K ∪ (Λ : Set (Domain d))ᶜ) ∩ tsupport φ
  have hLc : IsCompact L := φ.hasCompactSupport.inter_left hK
  have hLΩ : L ⊆ Ω := by
    intro x hx
    rcases hx.1 with hxK | hxΛ
    · exact hKΩ hxK
    · exact (hxΛ (φ.tsupport_subset hx.2)).elim
  obtain ⟨V, hV, hLV, hVΩ, _⟩ := exists_open_between_and_isCompact_closure hLc Ω.isOpen hLΩ
  obtain ⟨f, hf1, hf0, _⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (I := 𝓘(ℝ, Domain d)) (n := (⊤ : ℕ∞)) (t := V) hLc.isClosed
    (by simpa [hV.interior_eq] using hLV)
  let a : Domain d → 𝕜 := fun x => RCLike.ofReal (f x)
  have ha : ContDiff ℝ (⊤ : ℕ∞) a :=
    (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).contDiff.comp (contMDiff_iff_contDiff.mp f.contMDiff)
  have hs : tsupport a ⊆ closure V := by
    apply closure_mono
    intro x hx
    by_contra hxV
    exact hx (by simp [a, hf0 x hxV])
  let ψ : Tests 𝕜 Ω := ⟨a * φ, ha.mul φ.contDiff, φ.hasCompactSupport.mul_left,
    tsupport_mul_subset_left.trans (hs.trans hVΩ)⟩
  refine ⟨ψ, ?_⟩
  intro x hxK
  by_cases hxφ : x ∈ tsupport φ
  · have hxL : x ∈ L := ⟨Or.inl hxK, hxφ⟩
    have hf := hf1.filter_mono (nhds_le_nhdsSet hxL)
    filter_upwards [hf] with y hy
    change (RCLike.ofReal (f y) : 𝕜) * φ y = φ y
    simp [hy]
  · have hzero := notMem_tsupport_iff_eventuallyEq.mp hxφ
    filter_upwards [hzero] with y hy
    change a y * φ y = φ y
    simp [hy]

theorem partialFunction_eventuallyEq {f g : Domain d → 𝕜} {x : Domain d}
    (hfg : f =ᶠ[nhds x] g) (w : List (Fin d)) :
    partialFunction w f =ᶠ[nhds x] partialFunction w g := by
  induction w with
  | nil => exact hfg
  | cons j w ih =>
    exact (Filter.EventuallyEq.fderiv (𝕜 := ℝ) ih).mono (fun y hy => congrArg (fun T => T (coordinateVector j)) hy)

/-- Relative zero extension of Lp data; this does not assert Sobolev
regularity without the support condition proved below. -/
def zeroLp (Λ : Opens (Domain d)) (u : DomainLp 𝕜 Ω p) : DomainLp 𝕜 Λ p :=
  ((Smoothing.zeroExtend_memLp u).mono_measure Measure.restrict_le_self).toLp _

theorem zeroLp_coe (u : DomainLp 𝕜 Ω p) :
    zeroLp Λ u =ᵐ[volume.restrict (Λ : Set (Domain d))] (Ω : Set (Domain d)).indicator u :=
  MemLp.coeFn_toLp _

theorem zeroLp_norm (h : Ω ≤ Λ) (u : DomainLp 𝕜 Ω p) : ‖zeroLp Λ u‖ = ‖u‖ := by
  rw [Lp.norm_def, eLpNorm_congr_ae (zeroLp_coe u),
    eLpNorm_indicator_eq_eLpNorm_restrict Ω.isOpen.measurableSet.nullMeasurableSet,
    Measure.restrict_restrict_of_subset h, ← Lp.norm_def]

/-- Pairing relative zero extension with a target test is integration on the
source domain, without any support hypothesis. -/
theorem zeroLp_pairing (h : Ω ≤ Λ) (u : DomainLp 𝕜 Ω p) (φ : Tests 𝕜 Λ) :
    lpDistribution (zeroLp Λ u) φ = ∫ x in (Ω : Set (Domain d)), φ x * u x := by
  rw [lpDistribution_apply]
  calc
    _ = ∫ x, φ x * (Ω : Set (Domain d)).indicator u x ∂(volume.restrict (Λ : Set (Domain d))) :=
      integral_congr_ae ((zeroLp_coe u).mono (fun _ hx => congrArg (φ _ * ·) hx))
    _ = ∫ x, (Ω : Set (Domain d)).indicator (fun x => φ x * u x) x
        ∂(volume.restrict (Λ : Set (Domain d))) := by
      congr 1
      funext x
      by_cases hx : x ∈ Ω <;> simp [hx]
    _ = _ := by rw [integral_indicator Ω.isOpen.measurableSet, Measure.restrict_restrict_of_subset h]

theorem zeroLp_pairing_agree (h : Ω ≤ Λ) (K : Set (Domain d))
    (u : DomainLp 𝕜 Ω p) (hu : ∀ᵐ x ∂(volume.restrict (Ω : Set (Domain d))), x ∉ K → u x = 0)
    (φ : Tests 𝕜 Λ) (ψ : Tests 𝕜 Ω) (hψ : ∀ x ∈ K, ψ x = φ x) :
    lpDistribution (zeroLp Λ u) φ = lpDistribution u ψ := by
  rw [zeroLp_pairing h, lpDistribution_apply]
  apply integral_congr_ae
  filter_upwards [hu] with x hx
  by_cases hxK : x ∈ K
  · rw [hψ x hxK]
  · simp [hx hxK]

/-- No artificial boundary distribution is created when the full weak jet is
supported on a relatively closed set inside the source patch. This all-orders
statement also covers an unbounded interior piece. -/
theorem zeroJet_mem {m : ℕ} (h : Ω ≤ Λ) (K : Set (Domain d))
    (hK : IsClosed (K ∪ (Λ : Set (Domain d))ᶜ)) (hKΩ : K ⊆ Ω)
    (u : SpaceValue 𝕜 d Ω m p)
    (hu : ∀ α, ∀ᵐ x ∂(volume.restrict (Ω : Set (Domain d))), x ∉ K → u.val α x = 0) :
    WithLp.toLp 1 (fun α => zeroLp Λ (u.val α)) ∈ derivativeGraph 𝕜 Λ m p := by
  intro α
  ext φ
  obtain ⟨ψ, hψ⟩ := exists_test_agree_near_support h K hK hKΩ φ
  have hpair := zeroLp_pairing_agree h K (u.val α) (hu α) φ ψ
    (fun x hx => (hψ x hx).eq_of_nhds)
  change lpDistribution (zeroLp Λ (u.val α)) φ =
    (-1 : 𝕜) ^ (multiIndexWord (natIndex α)).length *
      lpDistribution (zeroLp Λ (u.val (zeroIndex d m))) (testPartialCLM (multiIndexWord (natIndex α)) φ)
  rw [hpair]
  have hweak := congrArg (fun T : ScalarDistribution 𝕜 Ω => T ψ) (u.property α)
  change lpDistribution (u.val α) ψ =
    (-1 : 𝕜) ^ (multiIndexWord (natIndex α)).length *
      lpDistribution (u.val (zeroIndex d m)) (testPartialCLM (multiIndexWord (natIndex α)) ψ) at hweak
  rw [hweak]
  congr 1
  symm
  apply zeroLp_pairing_agree h K _ (hu (zeroIndex d m))
  intro x hx
  rw [testPartial_formula, testPartial_formula]
  exact (partialFunction_eventuallyEq (hψ x hx) _).eq_of_nhds

/-- Isometric relative zero extension for supported Sobolev jets. -/
def relativeZeroExtend {m : ℕ} (h : Ω ≤ Λ) (K : Set (Domain d))
    (hK : IsClosed (K ∪ (Λ : Set (Domain d))ᶜ)) (hKΩ : K ⊆ Ω)
    (u : SpaceValue 𝕜 d Ω m p)
    (hu : ∀ α, ∀ᵐ x ∂(volume.restrict (Ω : Set (Domain d))), x ∉ K → u.val α x = 0) :
    SpaceValue 𝕜 d Λ m p :=
  ⟨WithLp.toLp 1 (fun α => zeroLp Λ (u.val α)), zeroJet_mem h K hK hKΩ u hu⟩

theorem relativeZeroExtend_norm {m : ℕ} (h : Ω ≤ Λ) (K : Set (Domain d))
    (hK : IsClosed (K ∪ (Λ : Set (Domain d))ᶜ)) (hKΩ : K ⊆ Ω)
    (u : SpaceValue 𝕜 d Ω m p)
    (hu : ∀ α, ∀ᵐ x ∂(volume.restrict (Ω : Set (Domain d))), x ∉ K → u.val α x = 0) :
    ‖relativeZeroExtend h K hK hKΩ u hu‖ = ‖u‖ := by
  change ‖WithLp.toLp 1 (fun α => zeroLp Λ (u.val α))‖ = ‖u.val‖
  rw [PiLp.norm_eq_of_L1, PiLp.norm_eq_of_L1]
  exact Finset.sum_congr rfl (fun α _ => zeroLp_norm h (u.val α))


/-- Relative zero extension is linear already on the Lp classes. -/
def zeroLpLM (Λ : Opens (Domain d)) : DomainLp 𝕜 Ω p →ₗ[𝕜] DomainLp 𝕜 Λ p where
  toFun := zeroLp Λ
  map_add' u v := by
    apply Lp.ext
    have hadd := ((ae_eq_restrict_iff_indicator_ae_eq Ω.isOpen.measurableSet).mp
      (Lp.coeFn_add u v)).filter_mono (ae_mono (Measure.restrict_le_self (s := (Λ : Set (Domain d)))))
    filter_upwards [zeroLp_coe (Λ := Λ) (u + v), zeroLp_coe (Λ := Λ) u,
      zeroLp_coe (Λ := Λ) v, Lp.coeFn_add (zeroLp Λ u) (zeroLp Λ v), hadd] with x h₁ h₂ h₃ h₄ h₅
    rw [h₁, h₄, h₅]
    simp only [Pi.add_apply, h₂, h₃]
    by_cases hx : x ∈ Ω <;> simp [hx]
  map_smul' c u := by
    apply Lp.ext
    have hsmul := ((ae_eq_restrict_iff_indicator_ae_eq Ω.isOpen.measurableSet).mp
      (Lp.coeFn_smul c u)).filter_mono (ae_mono (Measure.restrict_le_self (s := (Λ : Set (Domain d)))))
    filter_upwards [zeroLp_coe (Λ := Λ) (c • u), zeroLp_coe (Λ := Λ) u,
      Lp.coeFn_smul c (zeroLp Λ u), hsmul] with x h₁ h₂ h₃ h₄
    change zeroLp Λ (c • u) x = (c • zeroLp Λ u) x
    rw [h₁, h₃, h₄]
    simp only [Pi.smul_apply, h₂]
    by_cases hx : x ∈ Ω <;> simp [hx]

/-- The supported jets form a genuine scalar-linear subspace. -/
def supportedSobolev (𝕜 : Type) [RCLike 𝕜] {d : ℕ} (Ω : Opens (Domain d))
    (K : Set (Domain d)) (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Submodule 𝕜 (SpaceValue 𝕜 d Ω m p) where
  carrier := {u | ∀ α, ∀ᵐ x ∂(volume.restrict (Ω : Set (Domain d))), x ∉ K → u.val α x = 0}
  zero_mem' := by
    intro α
    exact (Lp.coeFn_zero 𝕜 p (volume.restrict (Ω : Set (Domain d)))).mono (fun _ hx _ => hx)
  add_mem' := by
    intro u v hu hv α
    filter_upwards [hu α, hv α, Lp.coeFn_add (u.val α) (v.val α)] with x h₁ h₂ h₃ hx
    change (u.val α + v.val α : DomainLp 𝕜 Ω p) x = 0
    rw [h₃]
    simp [h₁ hx, h₂ hx]
  smul_mem' := by
    intro c u hu α
    filter_upwards [hu α, Lp.coeFn_smul c (u.val α)] with x h₁ h₂ hx
    change (c • u.val α : DomainLp 𝕜 Ω p) x = 0
    rw [h₂]
    simp [h₁ hx]

/-- The relative zero-extension operator is an isometry on supported jets.
The closed support is relative to the target domain, so the construction is
usable next to a physical boundary as well as on an unbounded interior patch. -/
def relativeZeroExtensionCLM {m : ℕ} (h : Ω ≤ Λ) (K : Set (Domain d))
    (hK : IsClosed (K ∪ (Λ : Set (Domain d))ᶜ)) (hKΩ : K ⊆ Ω) :
    supportedSobolev 𝕜 Ω K m p →L[𝕜] SpaceValue 𝕜 d Λ m p :=
  LinearMap.mkContinuous
    { toFun := fun u => relativeZeroExtend h K hK hKΩ u.val u.property
      map_add' := by
        intro u v
        apply sobolev_underlying_injective 𝕜 d Λ m p
        change zeroLp Λ (u.val.val (zeroIndex d m) + v.val.val (zeroIndex d m)) =
          zeroLp Λ (u.val.val (zeroIndex d m)) + zeroLp Λ (v.val.val (zeroIndex d m))
        exact (zeroLpLM Λ).map_add _ _
      map_smul' := by
        intro c u
        apply sobolev_underlying_injective 𝕜 d Λ m p
        change zeroLp Λ (c • u.val.val (zeroIndex d m)) =
          c • zeroLp Λ (u.val.val (zeroIndex d m))
        exact (zeroLpLM Λ).map_smul _ _ }
    1 (fun u => by
      change ‖relativeZeroExtend h K hK hKΩ u.val u.property‖ ≤ 1 * ‖u‖
      rw [one_mul]
      change ‖relativeZeroExtend h K hK hKΩ u.val u.property‖ ≤ ‖u.val‖
      exact (relativeZeroExtend_norm h K hK hKΩ u.val u.property).le)

theorem relativeZeroExtensionCLM_norm {m : ℕ} (h : Ω ≤ Λ) (K : Set (Domain d))
    (hK : IsClosed (K ∪ (Λ : Set (Domain d))ᶜ)) (hKΩ : K ⊆ Ω)
    (u : supportedSobolev 𝕜 Ω K m p) :
    ‖relativeZeroExtensionCLM h K hK hKΩ u‖ = ‖u‖ :=
  relativeZeroExtend_norm h K hK hKΩ u.val u.property

end ExpandedFA.Sobolev.C1Extension


namespace ExpandedFA.Sobolev.C1Extension
open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
open HalfSpace
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω Λ : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem ambientMultiply_supported (a : Domain d → 𝕜) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ x, ‖a x‖ ≤ C)
    (hD : ∀ j x, ‖partialFunction [j] a x‖ ≤ C)
    (K : Set (Domain d)) (hK : (Ω : Set (Domain d)) ∩ tsupport a ⊆ K)
    (u : SpaceValue 𝕜 d Ω 1 p) :
    ambientMultiply a ha C hC0 hC hD u ∈ supportedSobolev 𝕜 Ω K 1 p := by
  intro α
  rcases Lines.multiIndex_order_one_cases (natIndex α) α.property with hz | ⟨j, hj⟩
  · have hα : α = zeroIndex d 1 := derivativeIndex_ext hz
    subst α
    filter_upwards [ambientMultiply_coe a ha C hC0 hC hD u,
      ae_restrict_mem Ω.isOpen.measurableSet] with x hx hxΩ hxK
    rw [hx, image_eq_zero_of_notMem_tsupport (fun hx' => hxK (hK ⟨hxΩ, hx'⟩)), zero_mul]
  · have hα : α = coordinateIndex j := derivativeIndex_ext (by simpa [coordinateIndex] using hj)
    subst α
    change ∀ᵐ x ∂(volume.restrict (Ω : Set (Domain d))),
      x ∉ K → ambientMultiplyJet a ha C hC hD u.val (coordinateIndex j) x = 0
    rw [ambientMultiplyJet_coordinate]
    filter_upwards [boundedMulLp_coe a ha.continuous C hC (u.val (coordinateIndex j)),
      boundedMulLp_coe (partialFunction [j] a)
        (Smoothing.partialFunction_contDiff _ a ha).continuous C (hD j) (u.val (zeroIndex d 1)),
      Lp.coeFn_add
        (boundedMulLp a ha.continuous C hC (u.val (coordinateIndex j)))
        (boundedMulLp (partialFunction [j] a)
          (Smoothing.partialFunction_contDiff _ a ha).continuous C (hD j) (u.val (zeroIndex d 1))),
      ae_restrict_mem Ω.isOpen.measurableSet] with x h₁ h₂ h₃ hxΩ hxK
    have hxa : x ∉ tsupport a := fun hx' => hxK (hK ⟨hxΩ, hx'⟩)
    have hzero : a x = 0 := image_eq_zero_of_notMem_tsupport hxa
    have hd : partialFunction [j] a x = 0 := by
      change fderiv ℝ a x (coordinateVector j) = 0
      rw [fderiv_of_notMem_tsupport ℝ hxa]
      rfl
    rw [h₃]
    simp only [Pi.add_apply, h₁, h₂, hzero, hd, zero_mul, add_zero]

/-- Multiplication followed by relative zero extension introduces no jump
at an artificial chart edge. The support condition is relative to the target. -/
def localizedZeroExtension (h : Ω ≤ Λ) (K : Set (Domain d))
    (hK : IsClosed (K ∪ (Λ : Set (Domain d))ᶜ)) (hKΩ : K ⊆ Ω)
    (a : Domain d → 𝕜) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ x, ‖a x‖ ≤ C)
    (hD : ∀ j x, ‖partialFunction [j] a x‖ ≤ C)
    (hcoeff : (Ω : Set (Domain d)) ∩ tsupport a ⊆ K) :
    SpaceValue 𝕜 d Ω 1 p →L[𝕜] SpaceValue 𝕜 d Λ 1 p :=
  (relativeZeroExtensionCLM h K hK hKΩ).comp
    ((ambientMultiply a ha C hC0 hC hD).codRestrict (supportedSobolev 𝕜 Ω K 1 p)
      (ambientMultiply_supported a ha C hC0 hC hD K hcoeff))

theorem localizedZeroExtension_coe (h : Ω ≤ Λ) (K : Set (Domain d))
    (hK : IsClosed (K ∪ (Λ : Set (Domain d))ᶜ)) (hKΩ : K ⊆ Ω)
    (a : Domain d → 𝕜) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ x, ‖a x‖ ≤ C)
    (hD : ∀ j x, ‖partialFunction [j] a x‖ ≤ C)
    (hcoeff : (Ω : Set (Domain d)) ∩ tsupport a ⊆ K)
    (u : SpaceValue 𝕜 d Ω 1 p) :
    (localizedZeroExtension h K hK hKΩ a ha C hC0 hC hD hcoeff u).val (zeroIndex d 1)
      =ᵐ[volume.restrict (Λ : Set (Domain d))]
        (Ω : Set (Domain d)).indicator (fun x => a x * u.val (zeroIndex d 1) x) := by
  have hm := ambientMultiply_coe a ha C hC0 hC hD u
  have hm' := ((ae_eq_restrict_iff_indicator_ae_eq Ω.isOpen.measurableSet).mp hm).filter_mono
    (ae_mono (Measure.restrict_le_self (s := (Λ : Set (Domain d)))))
  exact (zeroLp_coe ((ambientMultiply a ha C hC0 hC hD u).val (zeroIndex d 1))).trans hm'

theorem localizedZeroExtension_norm_le (h : Ω ≤ Λ) (K : Set (Domain d))
    (hK : IsClosed (K ∪ (Λ : Set (Domain d))ᶜ)) (hKΩ : K ⊆ Ω)
    (a : Domain d → 𝕜) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ x, ‖a x‖ ≤ C)
    (hD : ∀ j x, ‖partialFunction [j] a x‖ ≤ C)
    (hcoeff : (Ω : Set (Domain d)) ∩ tsupport a ⊆ K)
    (u : SpaceValue 𝕜 d Ω 1 p) :
    ‖localizedZeroExtension h K hK hKΩ a ha C hC0 hC hD hcoeff u‖ ≤
      (Fintype.card (DerivativeIndex d 1) * (2 * C)) * ‖u‖ := by
  change ‖relativeZeroExtend h K hK hKΩ
    (ambientMultiply a ha C hC0 hC hD u)
      (ambientMultiply_supported a ha C hC0 hC hD K hcoeff u)‖ ≤ _
  exact (relativeZeroExtend_norm h K hK hKΩ
    (ambientMultiply a ha C hC0 hC hD u)
    (ambientMultiply_supported a ha C hC0 hC hD K hcoeff u)).le.trans
      (ambientMultiplyJet_norm_le a ha C hC0 hC hD u.val)

end ExpandedFA.Sobolev.C1Extension


namespace ExpandedFA.Sobolev.C1Extension
open ExpandedFA.Distributions

/-- A finite smooth ambient localization near the compact boundary. The
interior coefficient is allowed to have unbounded support. -/
theorem finite_smooth_boundary_localization {d n : ℕ}
    (Ω : Opens (Domain d)) (U : Fin n → Set (Domain d))
    (hU : ∀ j, IsOpen (U j))
    (hcover : frontier (Ω : Set (Domain d)) ⊆ ⋃ j, U j)
    (hcompact : IsCompact (frontier (Ω : Set (Domain d)))) :
    ∃ (a : Option (Fin n) → Domain d → ℝ) (S : Set (Domain d)),
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (a j)) ∧
      (∀ j x, 0 ≤ a j x ∧ a j x ≤ 1) ∧
      (∀ x, a none x + ∑ j, a (some j) x = 1) ∧
      (∀ j, HasCompactSupport (a (some j)) ∧ tsupport (a (some j)) ⊆ U j) ∧
      IsClosed S ∧ S ⊆ Ω ∧
      closure (Ω : Set (Domain d)) ∩ tsupport (a none) ⊆ S := by
  classical
  obtain ⟨R, hR⟩ := hcompact.isBounded.subset_ball (0 : Domain d)
  let V : Option (Fin n) → Set (Domain d) :=
    fun j => match j with
      | none => (frontier (Ω : Set (Domain d)))ᶜ
      | some k => U k ∩ Metric.ball 0 R
  have hV : ∀ j, IsOpen (V j) := by
    intro j
    cases j with
    | none => exact isClosed_frontier.isOpen_compl
    | some j => exact (hU j).inter Metric.isOpen_ball
  have hVcover : (univ : Set (Domain d)) ⊆ ⋃ j, V j := by
    intro x _
    by_cases hx : x ∈ frontier (Ω : Set (Domain d))
    · obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover hx)
      exact mem_iUnion.mpr ⟨some j, hj, hR hx⟩
    · exact mem_iUnion.mpr ⟨none, hx⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (𝓘(ℝ, Domain d)) isClosed_univ V hV hVcover
  let a : Option (Fin n) → Domain d → ℝ := fun j => ρ j
  let S : Set (Domain d) := closure (Ω : Set (Domain d)) ∩ tsupport (a none)
  refine ⟨a, S, ?_, ?_, ?_, ?_, ?_, ?_, subset_rfl⟩
  · intro j
    exact contMDiff_iff_contDiff.mp (ρ j).contMDiff
  · intro j x
    exact ⟨ρ.nonneg j x, ρ.le_one j x⟩
  · intro x
    have hsum := ρ.sum_eq_one (mem_univ x)
    simpa only [finsum_eq_sum_of_fintype, Fintype.sum_option] using hsum
  · intro j
    refine ⟨?_, (hρ (some j)).trans inter_subset_left⟩
    exact Metric.isCompact_of_isClosed_isBounded (isClosed_tsupport _)
      (Metric.isBounded_ball.subset ((hρ (some j)).trans inter_subset_right))
  · exact isClosed_closure.inter (isClosed_tsupport _)
  · intro x hx
    have hxnot : x ∉ frontier (Ω : Set (Domain d)) := hρ none hx.2
    have : x ∈ interior (Ω : Set (Domain d)) := by
      rw [← closure_sdiff_frontier]
      exact ⟨hx.1, hxnot⟩
    exact interior_subset this

/-- Derivatives of every coefficient, including the unbounded interior
coefficient, have compact support and hence admit one finite common bound. -/
theorem finite_localization_bounds {𝕜 : Type} [RCLike 𝕜] {d n : ℕ}
    (a : Option (Fin n) → Domain d → 𝕜)
    (ha : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (a k))
    (hbound : ∀ k x, ‖a k x‖ ≤ 1)
    (hsum : ∀ x, a none x + ∑ k, a (some k) x = 1)
    (hcomp : ∀ k, HasCompactSupport (a (some k))) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ k x, ‖a k x‖ ≤ C) ∧
      ∀ k j x, ‖partialFunction [j] (a k) x‖ ≤ C := by
  classical
  let b : Domain d → 𝕜 := ∑ k, a (some k)
  have hb : HasCompactSupport b :=
    HasCompactSupport.finset_sum (fun k _ => hcomp k)
  have hn : a none = fun x => 1 - b x := by
    funext x
    have hx := hsum x
    simp only [b, Finset.sum_apply] at ⊢
    exact eq_sub_iff_add_eq.mpr hx
  have hD (k : Option (Fin n)) (j : Fin d) :
      HasCompactSupport (partialFunction [j] (a k)) := by
    cases k with
    | some k => exact (hcomp k).fderiv_apply (𝕜 := ℝ) (coordinateVector j)
    | none =>
      rw [hn]
      have heq : partialFunction [j] (fun x => 1 - b x) =
          -(partialFunction [j] b) := by
        funext x
        simp only [partialFunction, fderiv_const_sub, neg_apply, Pi.neg_apply]
      rw [heq]
      exact (hb.fderiv_apply (𝕜 := ℝ) (coordinateVector j)).neg
  have hBc (k : Option (Fin n)) (j : Fin d) :
      ∃ B : ℝ, ∀ x, ‖partialFunction [j] (a k) x‖ ≤ B := by
    apply (hD k j).exists_bound_of_continuous
    have hcont : ContDiff ℝ (⊤ : ℕ∞) (partialFunction [j] (a k)) :=
      ((ha k).fderiv_right (by simp)).clm_apply contDiff_const
    exact hcont.continuous
  choose B hB using hBc
  let C : ℝ := 1 + ∑ k, ∑ j, max 0 (B k j)
  have hnonneg (k : Option (Fin n)) : 0 ≤ ∑ j, max 0 (B k j) :=
    Finset.sum_nonneg (fun _ _ => le_max_left _ _)
  have hsum_nonneg : 0 ≤ ∑ k, ∑ j, max 0 (B k j) :=
    Finset.sum_nonneg (fun k _ => hnonneg k)
  refine ⟨C, add_nonneg zero_le_one hsum_nonneg, ?_, ?_⟩
  · intro k x
    exact (hbound k x).trans (le_add_of_nonneg_right hsum_nonneg)
  · intro k j x
    have hj : max 0 (B k j) ≤ ∑ l, max 0 (B k l) :=
      Finset.single_le_sum (fun _ _ => le_max_left _ _) (Finset.mem_univ j)
    have hk : (∑ l, max 0 (B k l)) ≤ ∑ l, ∑ j, max 0 (B l j) :=
      Finset.single_le_sum (fun l _ => hnonneg l) (Finset.mem_univ k)
    exact (hB k j x).trans ((le_max_right _ _).trans
      ((hj.trans hk).trans (le_add_of_nonneg_left zero_le_one)))

/-- The geometric localization with scalar coefficients and bounds ready
for the Sobolev multiplier construction. All data precede the exponent p. -/
theorem finite_scalar_boundary_localization {𝕜 : Type} [RCLike 𝕜] {d n : ℕ}
    (Ω : Opens (Domain d)) (U : Fin n → Set (Domain d))
    (hU : ∀ j, IsOpen (U j))
    (hcover : frontier (Ω : Set (Domain d)) ⊆ ⋃ j, U j)
    (hcompact : IsCompact (frontier (Ω : Set (Domain d)))) :
    ∃ (a : Option (Fin n) → Domain d → 𝕜) (S : Set (Domain d)) (C : ℝ),
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (a j)) ∧ 0 ≤ C ∧
      (∀ j x, ‖a j x‖ ≤ C) ∧
      (∀ j i x, ‖partialFunction [i] (a j) x‖ ≤ C) ∧
      (∀ x, a none x + ∑ j, a (some j) x = 1) ∧
      (∀ j, HasCompactSupport (a (some j)) ∧ tsupport (a (some j)) ⊆ U j) ∧
      IsClosed S ∧ S ⊆ Ω ∧
      closure (Ω : Set (Domain d)) ∩ tsupport (a none) ⊆ S := by
  classical
  obtain ⟨b, S, hb, hbrange, hbsum, hbcomp, hSc, hSΩ, hbS⟩ :=
    finite_smooth_boundary_localization Ω U hU hcover hcompact
  let a : Option (Fin n) → Domain d → 𝕜 := fun k x => RCLike.ofReal (b k x)
  have ha (k) : ContDiff ℝ (⊤ : ℕ∞) (a k) :=
    (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).contDiff.comp (hb k)
  have hnorm (k) (x) : ‖a k x‖ ≤ 1 := by
    rw [RCLike.norm_ofReal, abs_of_nonneg (hbrange k x).1]
    exact (hbrange k x).2
  have hsum (x) : a none x + ∑ k, a (some k) x = 1 := by
    have hx := congrArg (RCLike.ofReal : ℝ → 𝕜) (hbsum x)
    simpa only [RCLike.ofReal_add, RCLike.ofReal_sum, RCLike.ofReal_one] using hx
  have hsupp (k) : tsupport (a k) ⊆ tsupport (b k) :=
    tsupport_comp_subset RCLike.ofReal_zero (b k)
  have hcomp (k) : HasCompactSupport (a (some k)) :=
    (hbcomp k).1.comp_left RCLike.ofReal_zero
  obtain ⟨C, hC, hval, hder⟩ := finite_localization_bounds a ha hnorm hsum hcomp
  refine ⟨a, S, C, ha, hC, hval, hder, hsum, ?_, hSc, hSΩ, ?_⟩
  · intro k
    exact ⟨hcomp k, (hsupp (some k)).trans (hbcomp k).2⟩
  · exact (inter_subset_inter_right _ (hsupp none)).trans hbS

end ExpandedFA.Sobolev.C1Extension


namespace ExpandedFA.Sobolev.C1Extension.Transport
open Filter
variable {α β 𝕜 : Type*} [MeasurableSpace α] [MeasurableSpace β] [RCLike 𝕜]
  {μ : Measure α} {ν : Measure β} {p : ℝ≥0∞} [Fact (1 ≤ p)]

lemma comp_memLp_of_map_le {f : α → β} (hf : AEMeasurable f μ)
    {c : ℝ≥0∞} (hc : c ≠ ∞) (hμ : μ.map f ≤ c • ν) (u : Lp 𝕜 p ν) :
    MemLp (u ∘ f) p μ :=
  ((Lp.memLp u).of_measure_le_smul hc hμ).comp_of_map hf

lemma comp_eLpNorm_le_of_map_le {f : α → β} (hf : AEMeasurable f μ)
    {c : ℝ≥0∞} (hμ : μ.map f ≤ c • ν) (u : Lp 𝕜 p ν) :
    eLpNorm (u ∘ f) p μ ≤ c ^ (1 / p).toReal * eLpNorm u p ν := by
  have hq : μ.map f ≪ ν := Measure.absolutelyContinuous_of_le_smul hμ
  rw [← eLpNorm_map_measure
    ((Lp.memLp u).aestronglyMeasurable.mono_ac hq) hf]
  exact eLpNorm_le_of_measure_le_smul hμ

def pullLp {f : α → β} (hf : AEMeasurable f μ)
    {c : ℝ≥0∞} (hc : c ≠ ∞) (hμ : μ.map f ≤ c • ν) (u : Lp 𝕜 p ν) : Lp 𝕜 p μ :=
  (comp_memLp_of_map_le hf hc hμ u).toLp (u ∘ f)

lemma pullLp_coe {f : α → β} (hf : AEMeasurable f μ)
    {c : ℝ≥0∞} (hc : c ≠ ∞) (hμ : μ.map f ≤ c • ν) (u : Lp 𝕜 p ν) :
    pullLp hf hc hμ u =ᵐ[μ] u ∘ f := MemLp.coeFn_toLp _

lemma pullLp_norm_le {f : α → β} (hf : AEMeasurable f μ)
    {c : ℝ≥0∞} (hc : c ≠ ∞) (hμ : μ.map f ≤ c • ν) (u : Lp 𝕜 p ν) :
    ‖pullLp hf hc hμ u‖ ≤ c.toReal ^ (1 / p).toReal * ‖u‖ := by
  simp only [← toReal_enorm, Lp.enorm_def]
  rw [eLpNorm_congr_ae (pullLp_coe hf hc hμ u)]
  conv_rhs => rw [ENNReal.toReal_rpow, ← ENNReal.toReal_mul]
  apply ENNReal.toReal_mono
  · exact ENNReal.mul_ne_top (by simp [hc]) (Lp.memLp u).ne
  · exact comp_eLpNorm_le_of_map_le hf hμ u

def pullLpLM {f : α → β} (hf : AEMeasurable f μ)
    {c : ℝ≥0∞} (hc : c ≠ ∞) (hμ : μ.map f ≤ c • ν) :
    Lp 𝕜 p ν →ₗ[𝕜] Lp 𝕜 p μ where
  toFun := pullLp hf hc hμ
  map_add' u v := by
    apply Lp.ext
    have hq : μ.map f ≪ ν := Measure.absolutelyContinuous_of_le_smul hμ
    filter_upwards [pullLp_coe hf hc hμ (u + v),
      pullLp_coe hf hc hμ u, pullLp_coe hf hc hμ v,
      ae_of_ae_map hf (hq.ae_eq (Lp.coeFn_add u v)),
      Lp.coeFn_add (pullLp hf hc hμ u) (pullLp hf hc hμ v)] with x hsum hu hv huv hs
    simp only [Function.comp_apply] at hsum hu hv huv
    rw [hsum, huv, hs]
    simp only [Pi.add_apply, hu, hv]
  map_smul' a u := by
    apply Lp.ext
    have hq : μ.map f ≪ ν := Measure.absolutelyContinuous_of_le_smul hμ
    filter_upwards [pullLp_coe hf hc hμ (a • u),
      pullLp_coe hf hc hμ u,
      ae_of_ae_map hf (hq.ae_eq (Lp.coeFn_smul a u)),
      Lp.coeFn_smul a (pullLp hf hc hμ u)] with x has hu hau hs
    simp only [Function.comp_apply] at has hu hau
    simp only [RingHom.id_apply]
    rw [has, hau, hs]
    simp only [Pi.smul_apply, hu]

def pullLpCLM {f : α → β} (hf : AEMeasurable f μ)
    {c : ℝ≥0∞} (hc : c ≠ ∞) (hμ : μ.map f ≤ c • ν) :
    Lp 𝕜 p ν →L[𝕜] Lp 𝕜 p μ :=
  (pullLpLM hf hc hμ).mkContinuous (c.toReal ^ (1 / p).toReal)
    (pullLp_norm_le hf hc hμ)

lemma pullLp_coe_of_ae_eq {f : α → β} (hf : AEMeasurable f μ)
    {c : ℝ≥0∞} (hc : c ≠ ∞) (hμ : μ.map f ≤ c • ν) (u : Lp 𝕜 p ν)
    (g : β → 𝕜) (hgu : g =ᵐ[ν] u) :
    pullLp hf hc hμ u =ᵐ[μ] g ∘ f := by
  apply (pullLp_coe hf hc hμ u).trans
  exact ae_of_ae_map hf ((Measure.absolutelyContinuous_of_le_smul hμ).ae_eq hgu.symm)

lemma pullLpCLM_norm_le {f : α → β} (hf : AEMeasurable f μ)
    {c : ℝ≥0∞} (hc : c ≠ ∞) (hμ : μ.map f ≤ c • ν) :
    ‖(pullLpCLM hf hc hμ : Lp 𝕜 p ν →L[𝕜] Lp 𝕜 p μ)‖ ≤
      c.toReal ^ (1 / p).toReal :=
  LinearMap.mkContinuous_norm_le _ (Real.rpow_nonneg ENNReal.toReal_nonneg _) _

lemma pullLpCLM_norm_le_uniform {f : α → β} (hf : AEMeasurable f μ)
    {c : ℝ≥0∞} (hc : c ≠ ∞) (hμ : μ.map f ≤ c • ν) (hc1 : 1 ≤ c.toReal) :
    ‖(pullLpCLM hf hc hμ : Lp 𝕜 p ν →L[𝕜] Lp 𝕜 p μ)‖ ≤ c.toReal := by
  apply (pullLpCLM_norm_le hf hc hμ).trans
  apply Real.rpow_le_self_of_one_le hc1
  have hp : 1 / p ≤ (1 : ℝ≥0∞) := by
    simpa only [one_div, inv_one] using ENNReal.inv_le_inv.mpr (Fact.out : 1 ≤ p)
  exact (ENNReal.toReal_mono ENNReal.one_ne_top hp).trans_eq (by simp)

end ExpandedFA.Sobolev.C1Extension.Transport



namespace ExpandedFA.Sobolev.C1Extension.Transport
open Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [MeasureTheory.Measure.IsAddHaarMeasure μ]

lemma partialHomeomorph_map_measure_le (Φ : OpenPartialHomeomorph E E)
    (D : E → E →L[ℝ] E)
    (hD : ∀ y ∈ Φ.target, HasFDerivAt Φ.symm (D y) y)
    (C : ℝ) (hC : ∀ y ∈ Φ.target, |(D y).det| ≤ C) :
    (μ.restrict Φ.source).map Φ ≤ ENNReal.ofReal C • μ.restrict Φ.target := by
  have hΦ : AEMeasurable Φ (μ.restrict Φ.source) :=
    Φ.continuousOn.aemeasurable Φ.open_source.measurableSet
  apply Measure.le_iff.2
  intro t ht
  have hset : Φ.symm '' (t ∩ Φ.target) = Φ ⁻¹' t ∩ Φ.source := by
    ext x
    constructor
    · rintro ⟨y, ⟨hyt, hys⟩, rfl⟩
      exact ⟨by simpa only [mem_preimage, Φ.right_inv hys] using hyt, Φ.map_target hys⟩
    · rintro ⟨hxt, hxs⟩
      exact ⟨Φ x, ⟨hxt, Φ.map_source hxs⟩, Φ.left_inv hxs⟩
  rw [Measure.map_apply_of_aemeasurable hΦ ht, Measure.restrict_apply₀
    (hΦ.nullMeasurableSet_preimage ht), Measure.smul_apply,
    Measure.restrict_apply ht]
  rw [← hset, ← lintegral_abs_det_fderiv_eq_addHaar_image μ
    (ht.inter Φ.open_target.measurableSet)
    (fun y hy => (hD y hy.2).hasFDerivWithinAt)
    (Φ.symm.injOn.mono inter_subset_right)]
  calc
    (∫⁻ y in t ∩ Φ.target, ENNReal.ofReal |(D y).det| ∂μ) ≤
        ∫⁻ y in t ∩ Φ.target, ENNReal.ofReal C ∂μ :=
      setLIntegral_mono' (ht.inter Φ.open_target.measurableSet)
        (fun y hy => ENNReal.ofReal_le_ofReal (hC y hy.2))
    _ = _ := by simp

end ExpandedFA.Sobolev.C1Extension.Transport

namespace ExpandedFA.Sobolev.C1Extension.Transport
open Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [MeasureTheory.Measure.IsAddHaarMeasure μ]

lemma partialHomeomorph_map_measure_le_of_contDiff (Φ : OpenPartialHomeomorph E E)
    (hΦ : ContDiffOn ℝ 1 Φ.symm Φ.target)
    (C : ℝ) (hC : ∀ y ∈ Φ.target, |(fderiv ℝ Φ.symm y).det| ≤ C) :
    (μ.restrict Φ.source).map Φ ≤ ENNReal.ofReal C • μ.restrict Φ.target :=
  partialHomeomorph_map_measure_le μ Φ (fderiv ℝ Φ.symm)
    (fun y hy => ((hΦ.differentiableOn_one y hy).differentiableAt
      (Φ.open_target.mem_nhds hy)).hasFDerivAt) C hC

lemma partialHomeomorph_map_restrict_measure_le (Φ : OpenPartialHomeomorph E E)
    (D : E → E →L[ℝ] E)
    (hD : ∀ y ∈ Φ.target, HasFDerivAt Φ.symm (D y) y)
    (C : ℝ) (hC : ∀ y ∈ Φ.target, |(D y).det| ≤ C)
    (s : Set E) (hs : MeasurableSet s) :
    (μ.restrict (Φ ⁻¹' s ∩ Φ.source)).map Φ ≤
      ENNReal.ofReal C • μ.restrict (s ∩ Φ.target) := by
  have hΦ : AEMeasurable Φ (μ.restrict Φ.source) :=
    Φ.continuousOn.aemeasurable Φ.open_source.measurableSet
  have h := Measure.restrict_mono_measure
    (partialHomeomorph_map_measure_le μ Φ D hD C hC) s
  rw [Measure.restrict_map_of_aemeasurable hΦ hs,
    Measure.restrict_restrict₀ (hΦ.nullMeasurableSet_preimage hs),
    Measure.restrict_smul, Measure.restrict_restrict hs] at h
  exact h
end ExpandedFA.Sobolev.C1Extension.Transport

namespace ExpandedFA.Sobolev.C1Extension
open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

theorem relative_zero_extension :
    Specs.ExpandedFA.Sobolev.C1DomainExtension.RelativeZeroExtension := by
  intro 𝕜 _ d Ω Λ h K hK hKΩ m p _ u hu
  exact ⟨relativeZeroExtend h K hK hKΩ u hu, fun α => zeroLp_coe (u.val α),
    relativeZeroExtend_norm h K hK hKΩ u hu⟩

theorem localized_zero_extension :
    Specs.ExpandedFA.Sobolev.C1DomainExtension.LocalizedZeroExtension := by
  intro 𝕜 _ d Ω Λ h K hK hKΩ a ha C hC0 hC hD hcoeff p _
  refine ⟨localizedZeroExtension h K hK hKΩ a ha C hC0 hC hD hcoeff,
    localizedZeroExtension_coe h K hK hKΩ a ha C hC0 hC hD hcoeff, ?_⟩
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  exact localizedZeroExtension_norm_le h K hK hKΩ a ha C hC0 hC hD hcoeff

theorem finite_smooth_localization :
    Specs.ExpandedFA.Sobolev.C1DomainExtension.FiniteSmoothLocalization := by
  intro 𝕜 _ d n Ω U hU hcover hcompact
  exact finite_scalar_boundary_localization Ω U hU hcover hcompact

end ExpandedFA.Sobolev.C1Extension


namespace ExpandedFA.Sobolev.C1Extension
open ExpandedFA.Distributions

 theorem shrink_c1_chart {d : ℕ}
    (Φ : OpenPartialHomeomorph (Domain d) (Domain d))
    (x : Domain d) (hx : x ∈ Φ.source)
    (hΦ : ContDiffOn ℝ 1 Φ Φ.source)
    (hInv : ContDiffOn ℝ 1 Φ.symm Φ.target) :
    ∃ (Ψ : OpenPartialHomeomorph (Domain d) (Domain d)) (r : ℝ),
      0 < r ∧ x ∈ Ψ.source ∧
      Ψ.target = Metric.ball (Φ x) r ∧
      closure Ψ.source ⊆ Φ.source ∧ closure Ψ.target ⊆ Φ.target ∧
      IsCompact (closure Ψ.source) ∧ IsCompact (closure Ψ.target) ∧
      Bornology.IsBounded Ψ.source ∧ Bornology.IsBounded Ψ.target ∧
      (Ψ : (Domain d) → (Domain d)) = Φ ∧
      (Ψ.symm : (Domain d) → (Domain d)) = Φ.symm ∧
      ContDiffOn ℝ 1 Ψ Ψ.source ∧ ContDiffOn ℝ 1 Ψ.symm Ψ.target ∧
      ∃ C : ℝ, 0 ≤ C ∧
        (∀ y ∈ Ψ.source, ‖fderiv ℝ Ψ y‖ ≤ C) ∧
        (∀ y ∈ Ψ.target, ‖fderiv ℝ Ψ.symm y‖ ≤ C) := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (Φ.open_target.mem_nhds (Φ.map_source hx))
  let s : ℝ := r / 2
  have hs : 0 < s := half_pos hr
  have hclosed : Metric.closedBall (Φ x) s ⊆ Φ.target := by
    exact (Metric.closedBall_subset_ball (half_lt_self hr)).trans hball
  let B : Set (Domain d) := Metric.ball (Φ x) s
  let K : Set (Domain d) := Φ.symm '' Metric.closedBall (Φ x) s
  have hKcompact : IsCompact K :=
    (isCompact_closedBall (Φ x) s).image_of_continuousOn
      (hInv.continuousOn.mono hclosed)
  have hKsource : K ⊆ Φ.source := by
    rintro y ⟨z, hz, rfl⟩
    exact Φ.symm.map_source (hclosed hz)
  let Ψ := (Φ.symm.restrOpen B Metric.isOpen_ball).symm
  have htarget : Ψ.target = B := by
    change Φ.target ∩ B = B
    exact Set.inter_eq_right.mpr (Metric.ball_subset_closedBall.trans hclosed)
  have hsource : Ψ.source ⊆ Φ.source := by
    change Φ.source ∩ Φ ⁻¹' B ⊆ Φ.source
    exact inter_subset_left
  have hsourceK : Ψ.source ⊆ K := by
    intro y hy
    have hy' : y ∈ Φ.source ∧ Φ y ∈ B := hy
    exact ⟨Φ y, Metric.ball_subset_closedBall hy'.2, Φ.left_inv hy'.1⟩
  have hclosureK : closure Ψ.source ⊆ K :=
    hKcompact.isClosed.closure_subset_iff.mpr hsourceK
  have htargetold : Ψ.target ⊆ Φ.target := by
    rw [htarget]
    exact Metric.ball_subset_closedBall.trans hclosed
  have hΨ : ContDiffOn ℝ 1 Ψ Ψ.source := hΦ.mono hsource
  have hΨinv : ContDiffOn ℝ 1 Ψ.symm Ψ.target := hInv.mono htargetold
  obtain ⟨C₁, hC₁⟩ := hKcompact.exists_bound_of_continuousOn
    ((hΦ.continuousOn_fderiv_of_isOpen Φ.open_source (by simp)).mono hKsource)
  obtain ⟨C₂, hC₂⟩ := (isCompact_closedBall (Φ x) s).exists_bound_of_continuousOn
    ((hInv.continuousOn_fderiv_of_isOpen Φ.open_target (by simp)).mono hclosed)
  refine ⟨Ψ, s, hs, ?_, htarget, hclosureK.trans hKsource, ?_,
    hKcompact.of_isClosed_subset isClosed_closure hclosureK,
    ?_, hKcompact.isBounded.subset hsourceK, ?_, rfl, rfl, hΨ, hΨinv, max 0 (max C₁ C₂), le_max_left _ _, ?_, ?_⟩
  · change x ∈ Φ.source ∩ Φ ⁻¹' B
    exact ⟨hx, Metric.mem_ball_self hs⟩
  · rw [htarget]
    exact (closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall).trans hclosed
  · rw [htarget]
    exact (isCompact_closedBall (Φ x) s).of_isClosed_subset isClosed_closure
      (closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall)
  · rw [htarget]
    exact Metric.isBounded_ball
  · intro y hy
    exact (hC₁ y (hsourceK hy)).trans ((le_max_left C₁ C₂).trans (le_max_right _ _))
  · intro y hy
    have hyB : y ∈ B := htarget ▸ hy
    exact (hC₂ y (Metric.ball_subset_closedBall hyB)).trans
      ((le_max_right C₁ C₂).trans (le_max_right _ _))


open ExpandedFA.Distributions ExpandedFA.Sobolev.C1Extension

theorem local_bounded_c1_chart {d : ℕ} (Ω : TopologicalSpace.Opens (Domain d))
    (hΩ : IsC1Domain Ω) (x : Domain d) (hx : x ∈ frontier (Ω : Set (Domain d))) :
    ∃ (i : Fin d) (Ψ : OpenPartialHomeomorph (Domain d) (Domain d)) (C : ℝ),
      x ∈ Ψ.source ∧ Ψ x i = 0 ∧
      ContDiffOn ℝ 1 Ψ Ψ.source ∧ ContDiffOn ℝ 1 Ψ.symm Ψ.target ∧
      (∀ y ∈ Ψ.source, y ∈ Ω ↔ 0 < Ψ y i) ∧
      Bornology.IsBounded Ψ.source ∧ Bornology.IsBounded Ψ.target ∧
      IsCompact (closure Ψ.source) ∧ IsCompact (closure Ψ.target) ∧
      0 ≤ C ∧ (∀ y ∈ Ψ.source, ‖fderiv ℝ Ψ y‖ ≤ C) ∧
        (∀ y ∈ Ψ.target, ‖fderiv ℝ Ψ.symm y‖ ≤ C) := by
  obtain ⟨i, Φ, hxΦ, hzero, hΦ, hInv, hside⟩ := hΩ x hx
  obtain ⟨Ψ, r, hr, hxΨ, htarget, hs, ht, hsc, htc, hsb, htb,
      hfun, hinvfun, hΨ, hΨinv, C, hC, hCsrc, hCtgt⟩ :=
    shrink_c1_chart Φ x hxΦ hΦ hInv
  refine ⟨i, Ψ, C, hxΨ, ?_, hΨ, hΨinv, ?_, hsb, htb, hsc, htc, hC, hCsrc, hCtgt⟩
  · rw [hfun]
    exact hzero
  · intro y hy
    rw [hfun]
    exact hside y (hs (subset_closure hy))

end ExpandedFA.Sobolev.C1Extension


namespace ExpandedFA.Sobolev.C1Extension
open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

theorem finite_bounded_boundary_charts (d : ℕ) (Ω : Opens (Domain d))
    (hΩ : IsC1Domain Ω) (hcompact : IsCompact (frontier (Ω : Set (Domain d)))) :
    ∃ (n : ℕ) (i : Fin n → Fin d)
      (Φ : Fin n → OpenPartialHomeomorph (Domain d) (Domain d)) (C : ℝ),
      0 ≤ C ∧
      (∀ j, ContDiffOn ℝ 1 (Φ j) (Φ j).source ∧
        ContDiffOn ℝ 1 (Φ j).symm (Φ j).target ∧
        Bornology.IsBounded (Φ j).source ∧ Bornology.IsBounded (Φ j).target ∧
        (∀ y ∈ (Φ j).source, y ∈ Ω ↔ 0 < Φ j y (i j)) ∧
        (∀ y ∈ (Φ j).source, ‖fderiv ℝ (Φ j) y‖ ≤ C) ∧
        (∀ y ∈ (Φ j).target, ‖fderiv ℝ (Φ j).symm y‖ ≤ C)) ∧
      frontier (Ω : Set (Domain d)) ⊆ ⋃ j, (Φ j).source := by
  classical
  have hpoint (x : frontier (Ω : Set (Domain d))) :
      ∃ (i : Fin d) (Ψ : OpenPartialHomeomorph (Domain d) (Domain d)) (C : ℝ),
        x.val ∈ Ψ.source ∧ 0 ≤ C ∧
        ContDiffOn ℝ 1 Ψ Ψ.source ∧ ContDiffOn ℝ 1 Ψ.symm Ψ.target ∧
        Bornology.IsBounded Ψ.source ∧ Bornology.IsBounded Ψ.target ∧
        (∀ y ∈ Ψ.source, y ∈ Ω ↔ 0 < Ψ y i) ∧
        (∀ y ∈ Ψ.source, ‖fderiv ℝ Ψ y‖ ≤ C) ∧
        (∀ y ∈ Ψ.target, ‖fderiv ℝ Ψ.symm y‖ ≤ C) := by
    obtain ⟨i, Φ, hx, hzero, hΦ, hInv, hdomain⟩ := hΩ x.val x.property
    obtain ⟨Ψ, r, hr, hxΨ, htarget, hsource, _, _, _, hbsource, hbtarget,
      hfun, hsymmfun, hΨ, hΨinv, C, hC0, hC, hD⟩ := shrink_c1_chart Φ x.val hx hΦ hInv
    refine ⟨i, Ψ, C, hxΨ, hC0, hΨ, hΨinv, hbsource, hbtarget, ?_, hC, hD⟩
    intro y hy
    have hys : y ∈ Φ.source := hsource (subset_closure hy)
    simpa only [hfun] using hdomain y hys
  choose i Ψ C hx hC0 hΨ hΨinv hbsource hbtarget hdomain hC hD using hpoint
  obtain ⟨s, hs⟩ := hcompact.elim_finite_subcover
    (fun x : frontier (Ω : Set (Domain d)) => (Ψ x).source)
    (fun x => (Ψ x).open_source)
    (fun x hx' => mem_iUnion.mpr ⟨⟨x, hx'⟩, hx ⟨x, hx'⟩⟩)
  let B : ℝ := ∑ x ∈ s, C x
  have hBC (x : frontier (Ω : Set (Domain d))) (hx : x ∈ s) : C x ≤ B :=
    Finset.single_le_sum (fun y _ => hC0 y) hx
  refine ⟨s.card, fun j => i (s.equivFin.symm j).val,
    fun j => Ψ (s.equivFin.symm j).val, B, Finset.sum_nonneg (fun x _ => hC0 x), ?_, ?_⟩
  · intro j
    let x := s.equivFin.symm j
    refine ⟨hΨ x.val, hΨinv x.val, hbsource x.val, hbtarget x.val, hdomain x.val, ?_, ?_⟩
    · intro y hy
      exact (hC x.val y hy).trans (hBC x.val x.property)
    · intro y hy
      exact (hD x.val y hy).trans (hBC x.val x.property)
  · intro x hx'
    obtain ⟨b, hb⟩ := mem_iUnion.mp (hs hx')
    obtain ⟨hbs, hxsource⟩ := mem_iUnion.mp hb
    refine mem_iUnion.mpr ⟨s.equivFin ⟨b, hbs⟩, ?_⟩
    simpa using hxsource
end ExpandedFA.Sobolev.C1Extension


namespace ExpandedFA.Sobolev.C1Extension
open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

private theorem lp_finset_sum_coe {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {Ω : Opens (Domain d)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {ι : Type*} (s : Finset ι) (f : ι → DomainLp 𝕜 Ω p) :
    (∑ j ∈ s, f j) =ᵐ[volume.restrict (Ω : Set (Domain d))]
      fun x => ∑ j ∈ s, f j x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero 𝕜 p (volume.restrict (Ω : Set (Domain d)))] with x hx
    simpa only [Finset.sum_empty, Pi.zero_apply] using hx
  | @insert j s hj ih =>
    rw [Finset.sum_insert hj]
    filter_upwards [Lp.coeFn_add (f j) (∑ k ∈ s, f k), ih] with x hadd hsum
    simp only [hadd, Pi.add_apply, hsum, Finset.sum_insert hj]

private theorem sobolev_finset_sum_coe {𝕜 : Type} [RCLike 𝕜] {d m : ℕ}
    {Ω : Opens (Domain d)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {ι : Type*} (s : Finset ι) (u : ι → SpaceValue 𝕜 d Ω m p)
    (α : DerivativeIndex d m) :
    (∑ j ∈ s, u j).val α =ᵐ[volume.restrict (Ω : Set (Domain d))]
      fun x => ∑ j ∈ s, (u j).val α x := by
  let P : SpaceValue 𝕜 d Ω m p →ₗ[𝕜] DomainLp 𝕜 Ω p :=
    (PiLp.projₗ 1 _ α).comp (derivativeGraph 𝕜 Ω m p).subtype
  have heq : (∑ j ∈ s, u j).val α = ∑ j ∈ s, (u j).val α :=
    map_sum P u s
  rw [heq]
  exact lp_finset_sum_coe s (fun j => (u j).val α)

/-- Finitely many localized compatible extensions assemble into one common
raw formula and bounded Sobolev extension maps for every exponent. -/
theorem finite_compatible_extension_assembly {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {ι : Type*} [Fintype ι]
    (Ω : Opens (Domain d)) (a : ι → Domain d → 𝕜)
    (hsum : ∀ x ∈ Ω, ∑ j, a j x = 1)
    (T : ι → (Domain d → 𝕜) →ₗ[𝕜] (Domain d → 𝕜))
    (E : ι → ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)],
      SpaceValue 𝕜 d Ω 1 p →L[𝕜] SpaceValue 𝕜 d ⊤ 1 p)
    (hlocal : ∀ j (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : SpaceValue 𝕜 d Ω 1 p),
      (E j p u).val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))]
        fun x => a j x * u.val (zeroIndex d 1) x)
    (hcompatible : ∀ j (p : ℝ≥0∞) [Fact (1 ≤ p)]
      (u : SpaceValue 𝕜 d Ω 1 p) (f : Domain d → 𝕜),
      f =ᵐ[volume.restrict (Ω : Set (Domain d))] u.val (zeroIndex d 1) →
      (E j p u).val (zeroIndex d 1) =ᵐ[volume] T j f) :
    HasCompatibleExtension (𝕜 := 𝕜) Ω := by
  classical
  let Esum : ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)],
      SpaceValue 𝕜 d Ω 1 p →L[𝕜] SpaceValue 𝕜 d ⊤ 1 p := fun p _ => ∑ j, E j p
  refine ⟨∑ j, T j, Esum, ?_, ?_⟩
  · intro p _ u
    have heq : Esum p u = ∑ j, E j p u := by simp [Esum]
    rw [heq]
    have hco := sobolev_finset_sum_coe Finset.univ (fun j => E j p u) (zeroIndex d 1)
    have hcoΩ := hco.filter_mono (ae_mono
      (Measure.restrict_mono (le_top : Ω ≤ ⊤) le_rfl))
    filter_upwards [hcoΩ, ae_all_iff.mpr (fun j => hlocal j p u),
      ae_restrict_mem Ω.isOpen.measurableSet] with x hx hj hxΩ
    rw [hx]
    simp only [hj]
    rw [← Finset.sum_mul, hsum x hxΩ, one_mul]
  · intro p _ u f hf
    have heq : Esum p u = ∑ j, E j p u := by simp [Esum]
    rw [heq]
    have hco := sobolev_finset_sum_coe Finset.univ (fun j => E j p u) (zeroIndex d 1)
    have hcofull : (∑ j, E j p u).val (zeroIndex d 1) =ᵐ[volume]
        fun x => ∑ j, (E j p u).val (zeroIndex d 1) x := by simpa using hco
    filter_upwards [hcofull, ae_all_iff.mpr (fun j => hcompatible j p u f hf)] with x hx hj
    rw [hx]
    simp only [hj, LinearMap.sum_apply, Finset.sum_apply]

/-- The same finite assembly, followed by the fixed-neighborhood
normalization, gives the full simultaneous-extension conclusion. -/
theorem finite_simultaneous_extension_assembly {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {ι : Type*} [Fintype ι]
    (Ω : Opens (Domain d)) (a : ι → Domain d → 𝕜)
    (hsum : ∀ x ∈ Ω, ∑ j, a j x = 1)
    (T : ι → (Domain d → 𝕜) →ₗ[𝕜] (Domain d → 𝕜))
    (E : ι → ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)],
      SpaceValue 𝕜 d Ω 1 p →L[𝕜] SpaceValue 𝕜 d ⊤ 1 p)
    (hlocal : ∀ j (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : SpaceValue 𝕜 d Ω 1 p),
      (E j p u).val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))]
        fun x => a j x * u.val (zeroIndex d 1) x)
    (hcompatible : ∀ j (p : ℝ≥0∞) [Fact (1 ≤ p)]
      (u : SpaceValue 𝕜 d Ω 1 p) (f : Domain d → 𝕜),
      f =ᵐ[volume.restrict (Ω : Set (Domain d))] u.val (zeroIndex d 1) →
      (E j p u).val (zeroIndex d 1) =ᵐ[volume] T j f) :
    HasSimultaneousExtension (𝕜 := 𝕜) Ω := by
  apply bounded_support_reduction 𝕜 d Ω
  exact finite_compatible_extension_assembly Ω a hsum T E hlocal hcompatible

/-- Empty-frontier domains in Euclidean space are the empty set or the
whole space, including in dimension zero. -/
theorem simultaneous_extension_of_frontier_empty {𝕜 : Type} [RCLike 𝕜]
    {d : ℕ} (Ω : Opens (Domain d))
    (hfrontier : frontier (Ω : Set (Domain d)) = ∅) :
    HasSimultaneousExtension (𝕜 := 𝕜) Ω := by
  rcases frontier_eq_empty_iff.mp hfrontier with hempty | hfull
  · have hΩ : Ω = ⊥ := SetLike.coe_injective hempty
    subst Ω
    exact simultaneous_extension_bot 𝕜 d
  · have hΩ : Ω = ⊤ := SetLike.coe_injective hfull
    subst Ω
    exact simultaneous_extension_top 𝕜 d

end ExpandedFA.Sobolev.C1Extension

namespace ExpandedFA.Sobolev.C1Extension

theorem bounded_boundary_charts :
    Specs.ExpandedFA.Sobolev.C1DomainExtension.FiniteBoundedBoundaryCharts := by
  intro d Ω hΩ hcompact
  exact finite_bounded_boundary_charts d Ω hΩ hcompact

theorem finite_extension_assembly :
    Specs.ExpandedFA.Sobolev.C1DomainExtension.FiniteExtensionAssembly := by
  intro 𝕜 _ d ι _ Ω a hsum T E hlocal hcompatible
  exact finite_simultaneous_extension_assembly Ω a hsum T E hlocal hcompatible

theorem frontier_empty_extension :
    Specs.ExpandedFA.Sobolev.C1DomainExtension.FrontierEmptyExtension := by
  intro 𝕜 _ d Ω hfrontier
  exact simultaneous_extension_of_frontier_empty Ω hfrontier

end ExpandedFA.Sobolev.C1Extension


namespace ExpandedFA.Sobolev.C1Extension
open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω Λ : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The common raw formula for a smooth piece extended by zero. -/
def localizedRaw (Ω : Opens (Domain d)) (a : Domain d → 𝕜) :
    (Domain d → 𝕜) →ₗ[𝕜] (Domain d → 𝕜) where
  toFun := fun f => (Ω : Set (Domain d)).indicator (fun x => a x * f x)
  map_add' f g := by
    funext x
    by_cases hx : x ∈ Ω <;> simp [hx, mul_add]
  map_smul' c f := by
    funext x
    by_cases hx : x ∈ Ω <;> simp [hx, smul_eq_mul, mul_left_comm]

theorem localizedZeroExtension_representative (h : Ω ≤ Λ) (K : Set (Domain d))
    (hK : IsClosed (K ∪ (Λ : Set (Domain d))ᶜ)) (hKΩ : K ⊆ Ω)
    (a : Domain d → 𝕜) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ x, ‖a x‖ ≤ C)
    (hD : ∀ j x, ‖partialFunction [j] a x‖ ≤ C)
    (hcoeff : (Ω : Set (Domain d)) ∩ tsupport a ⊆ K)
    (u : SpaceValue 𝕜 d Ω 1 p) (f : Domain d → 𝕜)
    (hf : f =ᵐ[volume.restrict (Ω : Set (Domain d))] u.val (zeroIndex d 1)) :
    (localizedZeroExtension h K hK hKΩ a ha C hC0 hC hD hcoeff u).val (zeroIndex d 1)
      =ᵐ[volume.restrict (Λ : Set (Domain d))] localizedRaw Ω a f := by
  have hmul := hf.mono (fun x hx => congrArg (a x * ·) hx)
  have hmul' := ((ae_eq_restrict_iff_indicator_ae_eq Ω.isOpen.measurableSet).mp hmul).filter_mono
    (ae_mono (Measure.restrict_le_self (s := (Λ : Set (Domain d)))))
  exact (localizedZeroExtension_coe h K hK hKΩ a ha C hC0 hC hD hcoeff u).trans hmul'.symm

/-- The interior contribution is one common linear formula at all exponents.
The closed interior support may be unbounded. -/
theorem interior_compatible_piece (a : Domain d → 𝕜)
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ x, ‖a x‖ ≤ C) (hD : ∀ j x, ‖partialFunction [j] a x‖ ≤ C)
    (K : Set (Domain d)) (hK : IsClosed K) (hKΩ : K ⊆ Ω)
    (hcoeff : (Ω : Set (Domain d)) ∩ tsupport a ⊆ K) :
    ∃ (T : (Domain d → 𝕜) →ₗ[𝕜] (Domain d → 𝕜))
      (E : ∀ (q : ℝ≥0∞) [Fact (1 ≤ q)],
        SpaceValue 𝕜 d Ω 1 q →L[𝕜] SpaceValue 𝕜 d ⊤ 1 q),
      (∀ (q : ℝ≥0∞) [Fact (1 ≤ q)] (u : SpaceValue 𝕜 d Ω 1 q),
        (E q u).val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))]
          fun x => a x * u.val (zeroIndex d 1) x) ∧
      (∀ (q : ℝ≥0∞) [Fact (1 ≤ q)] (u : SpaceValue 𝕜 d Ω 1 q) (f : Domain d → 𝕜),
        f =ᵐ[volume.restrict (Ω : Set (Domain d))] u.val (zeroIndex d 1) →
        (E q u).val (zeroIndex d 1) =ᵐ[volume] T f) := by
  have hKt : IsClosed (K ∪ ((⊤ : Opens (Domain d)) : Set (Domain d))ᶜ) := by simpa using hK
  let E : ∀ (q : ℝ≥0∞) [Fact (1 ≤ q)],
      SpaceValue 𝕜 d Ω 1 q →L[𝕜] SpaceValue 𝕜 d ⊤ 1 q := fun q _ =>
    localizedZeroExtension le_top K hKt hKΩ a ha C hC0 hC hD hcoeff
  refine ⟨localizedRaw Ω a, E, ?_, ?_⟩
  · intro q _ u
    have heq := (localizedZeroExtension_coe le_top K hKt hKΩ a ha C hC0 hC hD hcoeff u).filter_mono
      (ae_mono (Measure.restrict_mono (le_top : Ω ≤ ⊤) le_rfl))
    filter_upwards [heq, ae_restrict_mem Ω.isOpen.measurableSet] with x hx hxΩ
    simpa only [Set.indicator_of_mem hxΩ] using hx
  · intro q _ u f hf
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      localizedZeroExtension_representative le_top K hKt hKΩ a ha C hC0 hC hD hcoeff u f hf
end ExpandedFA.Sobolev.C1Extension


namespace ExpandedFA.Sobolev.C1Extension.Classical
open ExpandedFA.Distributions ExpandedFA.Sobolev
open ExpandedFA.Sobolev.Lines
open ExpandedFA.Sobolev.HalfSpace
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem c1_classical_hasWeak
    (f : Domain d → 𝕜) (hf : ContDiffOn ℝ 1 f Ω)
    (u : DomainLp 𝕜 Ω p) (g : Fin d → DomainLp 𝕜 Ω p)
    (hu : u =ᵐ[volume.restrict (Ω : Set (Domain d))] f)
    (hg : ∀ j, g j =ᵐ[volume.restrict (Ω : Set (Domain d))]
      fun x => fderiv ℝ f x (coordinateVector j)) :
    HasWeakCoordinateDerivatives u g := by
  apply acl_to_weak u g f hu
  intro i
  filter_upwards [ae_on_fibers i (hg i)] with y hy
  refine ⟨?_, ?_⟩
  · intro a b hab
    have hcomp : ContDiffOn ℝ 1 (fun t => f (coordinateLine i y t)) (uIcc a b) :=
      hf.comp ((coordinateLine_contDiff i y).of_le (by simp)).contDiffOn (fun t ht => hab ht)
    exact hcomp.absolutelyContinuousOnInterval
  · filter_upwards [hy, ae_restrict_mem (fiber Ω i y).isOpen.measurableSet] with t hgt ht
    rw [hgt]
    exact ((hf.contDiffAt (Ω.isOpen.mem_nhds ht)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt
      t (coordinateLine_hasDerivAt i y t)

theorem c1_firstJet_mem
    (f : Domain d → 𝕜) (hf : ContDiffOn ℝ 1 f Ω)
    (v : DerivativeTuple 𝕜 Ω 1 p)
    (hz : v (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))] f)
    (hg : ∀ j, v (coordinateIndex j) =ᵐ[volume.restrict (Ω : Set (Domain d))]
      fun x => fderiv ℝ f x (coordinateVector j)) :
    v ∈ derivativeGraph 𝕜 Ω 1 p :=
  firstJet_mem_of_coordinateWeak v (c1_classical_hasWeak f hf _ _ hz hg)

theorem c1_mem_sobolev
    (f : Domain d → 𝕜) (hf : ContDiffOn ℝ 1 f Ω)
    (hLp : MemLp f p (volume.restrict (Ω : Set (Domain d))))
    (hDeriv : ∀ j, MemLp (fun x => fderiv ℝ f x (coordinateVector j)) p
      (volume.restrict (Ω : Set (Domain d)))) :
    ∃ u : SpaceValue 𝕜 d Ω 1 p,
      u.val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))] f ∧
      ∀ j, u.val (coordinateIndex j) =ᵐ[volume.restrict (Ω : Set (Domain d))]
        fun x => fderiv ℝ f x (coordinateVector j) := by
  let u₀ : DomainLp 𝕜 Ω p := hLp.toLp f
  let g : Fin d → DomainLp 𝕜 Ω p := fun j =>
    (hDeriv j).toLp (fun x => fderiv ℝ f x (coordinateVector j))
  have hu₀ : u₀ =ᵐ[volume.restrict (Ω : Set (Domain d))] f := MemLp.coeFn_toLp hLp
  have hg : ∀ j, g j =ᵐ[volume.restrict (Ω : Set (Domain d))]
      fun x => fderiv ℝ f x (coordinateVector j) := fun j => MemLp.coeFn_toLp (hDeriv j)
  have hw := c1_classical_hasWeak f hf u₀ g hu₀ hg
  obtain ⟨u, huz⟩ := (first_order_membership_iff u₀).mpr ⟨g, hw⟩
  refine ⟨u, huz ▸ hu₀, fun j => ?_⟩
  have hc := coordinate_weak_derivatives_on u j
  have hEq : u.val (coordinateIndex j) = g j := by
    apply ExpandedFA.Sobolev.lpDistribution_injective
    rw [hc, hw j]
    congr 2
    simpa [underlyingLp] using congrArg (fun z : DomainLp 𝕜 Ω p => lpDistribution z) huz
  rw [hEq]
  exact hg j

end ExpandedFA.Sobolev.C1Extension.Classical


namespace ExpandedFA.Sobolev.C1Extension.Transport
open Filter
open TopologicalSpace ExpandedFA.Distributions ExpandedFA.Sobolev

lemma exists_det_bound_of_norm_bound {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (C : ℝ) :
    ∃ J : ℝ, 1 ≤ J ∧ ∀ A : E →L[ℝ] E, ‖A‖ ≤ C → |A.det| ≤ J := by
  obtain ⟨J, hJ⟩ := (isCompact_closedBall (0 : E →L[ℝ] E) C).exists_bound_of_continuousOn
    ContinuousLinearMap.continuous_det.continuousOn
  refine ⟨max 1 J, le_max_left _ _, ?_⟩
  intro A hA
  have hAJ : |A.det| ≤ J := by
    simpa only [Real.norm_eq_abs] using
      (hJ A (by simpa only [Metric.mem_closedBall, dist_zero_right] using hA))
  exact hAJ.trans (le_max_right _ _)

variable {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

lemma chart_aemeasurable (Φ : OpenPartialHomeomorph (Domain d) (Domain d))
    (Ω : Opens (Domain d)) :
    AEMeasurable Φ (volume.restrict (chartPreimage Φ Ω : Set (Domain d))) :=
  (Φ.continuousOn.mono inter_subset_left).aemeasurable (chartPreimage Φ Ω).isOpen.measurableSet

lemma chart_map_measure_le (Φ : OpenPartialHomeomorph (Domain d) (Domain d))
    (hΦ : ContDiffOn ℝ 1 Φ.symm Φ.target)
    (C : ℝ) (hC : ∀ y ∈ Φ.target, |(fderiv ℝ Φ.symm y).det| ≤ C)
    (Ω : Opens (Domain d)) :
    (volume.restrict (chartPreimage Φ Ω : Set (Domain d))).map Φ ≤
      ENNReal.ofReal C • volume.restrict (chartTarget Φ Ω : Set (Domain d)) := by
  have hmap := partialHomeomorph_map_restrict_measure_le volume Φ (fderiv ℝ Φ.symm)
    (fun y hy => ((hΦ.differentiableOn_one y hy).differentiableAt
      (Φ.open_target.mem_nhds hy)).hasFDerivAt) C hC (Ω : Set (Domain d)) Ω.isOpen.measurableSet
  change (volume.restrict (Φ.source ∩ Φ ⁻¹' (Ω : Set (Domain d)))).map Φ ≤
    ENNReal.ofReal C • volume.restrict ((Ω : Set (Domain d)) ∩ Φ.target)
  rw [Set.inter_comm Φ.source (Φ ⁻¹' (Ω : Set (Domain d)))]
  exact hmap

def chartLpPull (Φ : OpenPartialHomeomorph (Domain d) (Domain d))
    (hΦ : ContDiffOn ℝ 1 Φ.symm Φ.target)
    (C : ℝ) (hC : ∀ y ∈ Φ.target, |(fderiv ℝ Φ.symm y).det| ≤ C)
    (Ω : Opens (Domain d)) :
    DomainLp 𝕜 (chartTarget Φ Ω) p →L[𝕜] DomainLp 𝕜 (chartPreimage Φ Ω) p :=
  pullLpCLM (chart_aemeasurable Φ Ω)
    (ENNReal.ofReal_ne_top : ENNReal.ofReal C ≠ ∞) (chart_map_measure_le Φ hΦ C hC Ω)

lemma chartLpPull_coe (Φ : OpenPartialHomeomorph (Domain d) (Domain d))
    (hΦ : ContDiffOn ℝ 1 Φ.symm Φ.target)
    (C : ℝ) (hC : ∀ y ∈ Φ.target, |(fderiv ℝ Φ.symm y).det| ≤ C)
    (Ω : Opens (Domain d)) (u : DomainLp 𝕜 (chartTarget Φ Ω) p) :
    chartLpPull Φ hΦ C hC Ω u =ᵐ[volume.restrict (chartPreimage Φ Ω : Set (Domain d))]
      u ∘ Φ :=
  pullLp_coe (chart_aemeasurable Φ Ω) (ENNReal.ofReal_ne_top : ENNReal.ofReal C ≠ ∞)
    (chart_map_measure_le Φ hΦ C hC Ω) u

lemma chartLpPull_norm_le (Φ : OpenPartialHomeomorph (Domain d) (Domain d))
    (hΦ : ContDiffOn ℝ 1 Φ.symm Φ.target)
    (C : ℝ) (hC1 : 1 ≤ C) (hC : ∀ y ∈ Φ.target, |(fderiv ℝ Φ.symm y).det| ≤ C)
    (Ω : Opens (Domain d)) :
    ‖(chartLpPull Φ hΦ C hC Ω :
      DomainLp 𝕜 (chartTarget Φ Ω) p →L[𝕜] DomainLp 𝕜 (chartPreimage Φ Ω) p)‖ ≤ C := by
  have hC0 : 0 ≤ C := zero_le_one.trans hC1
  simpa only [chartLpPull, ENNReal.toReal_ofReal hC0] using
    (pullLpCLM_norm_le_uniform (𝕜 := 𝕜) (p := p) (chart_aemeasurable Φ Ω)
      (ENNReal.ofReal_ne_top : ENNReal.ofReal C ≠ ∞) (chart_map_measure_le Φ hΦ C hC Ω)
      (by simpa only [ENNReal.toReal_ofReal hC0] using hC1))

end ExpandedFA.Sobolev.C1Extension.Transport

namespace ExpandedFA.Sobolev.C1Extension
open ExpandedFA.Distributions

theorem chart_lp_transport :
    Specs.ExpandedFA.Sobolev.C1DomainExtension.ChartLpTransport := by
  intro 𝕜 _ d Φ hΦ C hC
  obtain ⟨J, hJ, hdet⟩ := Transport.exists_det_bound_of_norm_bound (E := Domain d) C
  have hbound (y) (hy : y ∈ Φ.target) : |(fderiv ℝ Φ.symm y).det| ≤ J :=
    hdet _ (hC y hy)
  refine ⟨J, hJ, ?_⟩
  intro Ω p _
  refine ⟨Transport.chartLpPull Φ hΦ J hbound Ω, ?_,
    Transport.chartLpPull_norm_le Φ hΦ J hJ hbound Ω⟩
  intro u f hf
  exact Transport.pullLp_coe_of_ae_eq (Transport.chart_aemeasurable Φ Ω)
    ENNReal.ofReal_ne_top (Transport.chart_map_measure_le Φ hΦ J hbound Ω) u f hf.symm

end ExpandedFA.Sobolev.C1Extension


namespace ExpandedFA.Sobolev.C1Extension.Transport
open Filter
open ExpandedFA.Distributions ExpandedFA.Sobolev
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

variable {𝕜 : Type} [RCLike 𝕜] {d m : ℕ} {Ω : Opens (Domain d)}
  {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

lemma lpDistribution_eq_of_ae_exponent (u : DomainLp 𝕜 Ω p) (v : DomainLp 𝕜 Ω q)
    (huv : u =ᵐ[volume.restrict (Ω : Set (Domain d))] v) :
    lpDistribution u = lpDistribution v := by
  ext φ
  simp only [lpDistribution_apply]
  apply integral_congr_ae
  filter_upwards [huv] with x hx
  rw [hx]

def lowerExponent [IsFiniteMeasure (volume.restrict (Ω : Set (Domain d)))]
    (hqp : q ≤ p) (u : SpaceValue 𝕜 d Ω m p) : SpaceValue 𝕜 d Ω m q := by
  let v : DerivativeTuple 𝕜 Ω m q := WithLp.toLp 1 fun α =>
    ((Lp.memLp (u.val α)).mono_exponent hqp).toLp (u.val α)
  have hv (α : DerivativeIndex d m) : v α =ᵐ[volume.restrict (Ω : Set (Domain d))] u.val α :=
    MemLp.coeFn_toLp ((Lp.memLp (u.val α)).mono_exponent hqp)
  refine ⟨v, ?_⟩
  intro α
  change lpDistribution (v α) =
    Specs.ExpandedFA.Distributions.DistributionCalculus.multiIndexDerivativeValue
      𝕜 d Ω (natIndex α) (lpDistribution (v (zeroIndex d m)))
  rw [lpDistribution_eq_of_ae_exponent (v α) (u.val α) (hv α),
    lpDistribution_eq_of_ae_exponent (v (zeroIndex d m)) (u.val (zeroIndex d m)) (hv _)]
  exact u.property α

lemma lowerExponent_coe [IsFiniteMeasure (volume.restrict (Ω : Set (Domain d)))]
    (hqp : q ≤ p) (u : SpaceValue 𝕜 d Ω m p) (α : DerivativeIndex d m) :
    (lowerExponent hqp u).val α =ᵐ[volume.restrict (Ω : Set (Domain d))] u.val α :=
  MemLp.coeFn_toLp ((Lp.memLp (u.val α)).mono_exponent hqp)
end ExpandedFA.Sobolev.C1Extension.Transport

namespace ExpandedFA.Sobolev.C1Extension

theorem interior_localization :
    Specs.ExpandedFA.Sobolev.C1DomainExtension.InteriorCompatiblePiece := by
  intro 𝕜 _ d Ω a ha C hC0 hC hD K hK hKΩ hcoeff
  exact interior_compatible_piece a ha C hC0 hC hD K hK hKΩ hcoeff

end ExpandedFA.Sobolev.C1Extension


namespace ExpandedFA.Sobolev.C1Extension.Classical
open ExpandedFA.Distributions ExpandedFA.Sobolev
open ExpandedFA.Sobolev.Lines ExpandedFA.Sobolev.HalfSpace
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

lemma c1_partial_continuousOn (f : Domain d → 𝕜) (hf : ContDiffOn ℝ 1 f Ω) (j : Fin d) :
    ContinuousOn (fun x => fderiv ℝ f x (coordinateVector j)) Ω :=
  (hf.continuousOn_fderiv_of_isOpen Ω.isOpen (by simp)).clm_apply continuousOn_const

lemma c1_test_ibp (f : Domain d → 𝕜) (hf : ContDiffOn ℝ 1 f Ω)
    (j : Fin d) (φ : Tests 𝕜 Ω) :
    (∫ x in (Ω : Set (Domain d)), φ x * fderiv ℝ f x (coordinateVector j)) =
      -(∫ x in (Ω : Set (Domain d)), testPartialCLM [j] φ x * f x) := by
  have hfLoc : LocallyIntegrableOn f Ω volume :=
    hf.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet
  have hdLoc : LocallyIntegrableOn (fun x => fderiv ℝ f x (coordinateVector j)) Ω volume :=
    (c1_partial_continuousOn f hf j).locallyIntegrableOn Ω.isOpen.measurableSet
  have h₁ := φ.integrable_bilin (ContinuousLinearMap.mul 𝕜 𝕜) hdLoc
  have h₂ := (testPartialCLM [j] φ).integrable_bilin (ContinuousLinearMap.mul 𝕜 𝕜) hfLoc
  have h₃ := φ.integrable_bilin (ContinuousLinearMap.mul 𝕜 𝕜) hfLoc
  change Integrable (fun x => φ x * fderiv ℝ f x (coordinateVector j)) volume at h₁
  change Integrable (fun x => testPartialCLM [j] φ x * f x) volume at h₂
  change Integrable (fun x => φ x * f x) volume at h₃
  have hφd (x : Domain d) : fderiv ℝ (fun x => φ x) x (coordinateVector j) =
      testPartialCLM [j] φ x := by
    rw [testPartial_formula]
    rfl
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := f) (g := fun x => φ x) (v := coordinateVector j)
    (by simpa only [mul_comm] using h₁)
    (by simpa only [hφd, mul_comm] using h₂)
    (by simpa only [mul_comm] using h₃)
    (fun x hx => (hf.contDiffAt (Ω.isOpen.mem_nhds (φ.tsupport_subset hx))).differentiableAt (by simp))
    (fun x _ => φ.contDiff.differentiable (by simp) x)
  have h' : (∫ x, φ x * fderiv ℝ f x (coordinateVector j)) =
      -(∫ x, testPartialCLM [j] φ x * f x) := by
    simpa only [hφd, neg_neg, mul_comm] using congrArg Neg.neg h.symm
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => by simp [φ.zero_on_compl hx]),
    setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => by simp [(testPartialCLM [j] φ).zero_on_compl hx])]
  exact h'

 theorem c1_representative_derivative (u : SpaceValue 𝕜 d Ω 1 p)
    (f : Domain d → 𝕜) (hf : ContDiffOn ℝ 1 f Ω)
    (hu : u.val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))] f)
    (j : Fin d) :
    u.val (coordinateIndex j) =ᵐ[volume.restrict (Ω : Set (Domain d))]
      fun x => fderiv ℝ f x (coordinateVector j) := by
  let D : Domain d → 𝕜 := fun x => fderiv ℝ f x (coordinateVector j)
  have hdLoc : LocallyIntegrableOn D Ω (volume.restrict (Ω : Set (Domain d))) :=
    (c1_partial_continuousOn f hf j).locallyIntegrableOn Ω.isOpen.measurableSet
  have hloc := (domainLp_locallyIntegrable (u.val (coordinateIndex j))).sub hdLoc
  have hz := Ω.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc
    (fun g hg hgc hgs => by
      let φ : Tests 𝕜 Ω :=
        ⟨fun x => (g x : 𝕜), ((RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).contDiff.comp hg),
          hgc.comp_left (by simp), (tsupport_comp_subset (g := fun r : ℝ => (r : 𝕜)) (by simp) g).trans hgs⟩
      have hw := congrArg (fun T : ScalarDistribution 𝕜 Ω => T φ)
        (coordinate_weak_derivatives_on u j)
      simp only [lpDistribution_apply, _root_.neg_apply, ContinuousLinearMap.comp_apply, underlyingLp] at hw
      have hrew : (∫ x in (Ω : Set (Domain d)), testPartialCLM [j] φ x * u.val (zeroIndex d 1) x) =
          ∫ x in (Ω : Set (Domain d)), testPartialCLM [j] φ x * f x := by
        exact integral_congr_ae (hu.mono (fun x hx => congrArg (testPartialCLM [j] φ x * ·) hx))
      have hclass := c1_test_ibp f hf j φ
      have hintu := φ.integrable_bilin (ContinuousLinearMap.mul 𝕜 𝕜)
        (domainLp_locallyIntegrable (u.val (coordinateIndex j)))
      have hintd := φ.integrable_bilin (ContinuousLinearMap.mul 𝕜 𝕜) hdLoc
      change Integrable (fun x => φ x * u.val (coordinateIndex j) x) (volume.restrict (Ω : Set (Domain d))) at hintu
      change Integrable (fun x => φ x * D x) (volume.restrict (Ω : Set (Domain d))) at hintd
      simp only [RCLike.real_smul_eq_coe_mul]
      change (∫ x, φ x * (u.val (coordinateIndex j) x - D x) ∂(volume.restrict (Ω : Set (Domain d)))) = 0
      simp_rw [mul_sub]
      rw [integral_sub hintu hintd]
      change (∫ x in (Ω : Set (Domain d)), φ x * u.val (coordinateIndex j) x) -
        (∫ x in (Ω : Set (Domain d)), φ x * D x) = 0
      rw [hw, hrew, hclass, sub_self])
  have hz' := (ae_restrict_iff' Ω.isOpen.measurableSet).mpr hz
  rw [Measure.restrict_restrict Ω.isOpen.measurableSet, inter_self] at hz'
  filter_upwards [hz'] with x hx
  exact sub_eq_zero.mp hx

end ExpandedFA.Sobolev.C1Extension.Classical


namespace ExpandedFA.Sobolev.C1Extension
open ExpandedFA.Distributions

theorem exists_compact_ambient_cutoff {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (K : Set (Domain d)) (hK : IsCompact K) (U : Opens (Domain d)) (hKU : K ⊆ U) :
    ∃ η : Tests 𝕜 (⊤ : Opens (Domain d)),
      tsupport η ⊆ U ∧ ∀ x ∈ K, η x = 1 := by
  obtain ⟨V, hV, hKV, hVU, hVc⟩ := exists_open_between_and_isCompact_closure hK U.isOpen hKU
  obtain ⟨f, hf, _, hfs, hfone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hV hK.isClosed hKV
  have hfc : HasCompactSupport f := by
    change IsCompact (closure (Function.support f))
    rw [hfs]
    exact hVc
  let a : Domain d → 𝕜 := fun x => RCLike.ofReal (f x)
  have ha : ContDiff ℝ (⊤ : ℕ∞) a :=
    (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).contDiff.comp hf
  have hac : HasCompactSupport a := hfc.comp_left RCLike.ofReal_zero
  let η : Tests 𝕜 (⊤ : Opens (Domain d)) := ⟨a, ha, hac, by simp⟩
  refine ⟨η, ?_, ?_⟩
  · exact (tsupport_comp_subset RCLike.ofReal_zero f).trans (by simpa [tsupport, hfs] using hVU)
  · intro x hx
    change (RCLike.ofReal (f x) : 𝕜) = 1
    rw [(hfone x).mp hx, RCLike.ofReal_one]

/-- A second cutoff in flattened coordinates can equal one on the entire
image of an ambient boundary piece; no regularity of a composed cutoff is used. -/
theorem exists_chart_cutoff {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Φ : OpenPartialHomeomorph (Domain d) (Domain d))
    (θ : Tests 𝕜 (⊤ : Opens (Domain d))) (hθ : tsupport θ ⊆ Φ.source) :
    ∃ χ : Tests 𝕜 (⊤ : Opens (Domain d)),
      tsupport χ ⊆ Φ.target ∧ ∀ x ∈ tsupport θ, χ (Φ x) = 1 := by
  have hc : IsCompact (Φ '' tsupport θ) :=
    θ.hasCompactSupport.image_of_continuousOn (Φ.continuousOn.mono hθ)
  have ht : Φ '' tsupport θ ⊆ Φ.target := by
    rintro y ⟨x, hx, rfl⟩
    exact Φ.map_source (hθ hx)
  obtain ⟨χ, hχ, hχone⟩ := exists_compact_ambient_cutoff (𝕜 := 𝕜)
    (Φ '' tsupport θ) hc ⟨Φ.target, Φ.open_target⟩ ht
  exact ⟨χ, hχ, fun x hx => hχone (Φ x) ⟨x, hx, rfl⟩⟩

end ExpandedFA.Sobolev.C1Extension


namespace ExpandedFA.Sobolev.C1Extension.Transport
open Filter
open ExpandedFA.Distributions ExpandedFA.Sobolev ExpandedFA.Sobolev.HalfSpace
open private firstJetCoordinate firstJetCoordinate_spec firstJetCoordinate_coordinate
  from MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.HalfSpaceExtension

section GenericMul
variable {X 𝕜 : Type*} [MeasurableSpace X] [RCLike 𝕜]
  {μ : Measure X} {p : ℝ≥0∞} [Fact (1 ≤ p)]

def aeSmulLp (a : X → ℝ) (ha : AEStronglyMeasurable a μ) (B : ℝ)
    (hB : ∀ᵐ x ∂μ, ‖a x‖ ≤ B) (u : Lp 𝕜 p μ) : Lp 𝕜 p μ :=
  ((Lp.memLp u).of_le_mul (f := fun x => a x • u x) (c := B)
    (ha.smul (Lp.memLp u).aestronglyMeasurable)
    (by filter_upwards [hB] with x hx
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_right hx (norm_nonneg _))).toLp _

lemma aeSmulLp_coe (a : X → ℝ) (ha : AEStronglyMeasurable a μ) (B : ℝ)
    (hB : ∀ᵐ x ∂μ, ‖a x‖ ≤ B) (u : Lp 𝕜 p μ) :
    aeSmulLp a ha B hB u =ᵐ[μ] fun x => a x • u x := MemLp.coeFn_toLp _

lemma aeSmulLp_norm_le (a : X → ℝ) (ha : AEStronglyMeasurable a μ) (B : ℝ)
    (hB : ∀ᵐ x ∂μ, ‖a x‖ ≤ B) (u : Lp 𝕜 p μ) :
    ‖aeSmulLp a ha B hB u‖ ≤ B * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [aeSmulLp_coe a ha B hB u, hB] with x hx hbx
  rw [hx, norm_smul]
  exact mul_le_mul_of_nonneg_right hbx (norm_nonneg _)

def aeSmulLpLM (a : X → ℝ) (ha : AEStronglyMeasurable a μ) (B : ℝ)
    (hB : ∀ᵐ x ∂μ, ‖a x‖ ≤ B) : Lp 𝕜 p μ →ₗ[𝕜] Lp 𝕜 p μ where
  toFun := aeSmulLp a ha B hB
  map_add' u v := by
    apply Lp.ext
    filter_upwards [aeSmulLp_coe a ha B hB (u + v), aeSmulLp_coe a ha B hB u,
      aeSmulLp_coe a ha B hB v, Lp.coeFn_add u v,
      Lp.coeFn_add (aeSmulLp a ha B hB u) (aeSmulLp a ha B hB v)] with x hs hu hv ha hc
    rw [hs, hc, ha]
    simp only [Pi.add_apply, hu, hv, smul_add]
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [aeSmulLp_coe a ha B hB (c • u), aeSmulLp_coe a ha B hB u,
      Lp.coeFn_smul c u, Lp.coeFn_smul c (aeSmulLp a ha B hB u)] with x hs hu hau hc
    change aeSmulLp a ha B hB (c • u) x = (c • aeSmulLp a ha B hB u) x
    rw [hs, hc, hau]
    simp only [Pi.smul_apply, hu]
    exact smul_comm _ _ _

def aeSmulLpCLM (a : X → ℝ) (ha : AEStronglyMeasurable a μ) (B : ℝ)
    (hB : ∀ᵐ x ∂μ, ‖a x‖ ≤ B) : Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p μ :=
  (aeSmulLpLM (𝕜 := 𝕜) (p := p) a ha B hB).mkContinuous B
    (fun u => aeSmulLp_norm_le a ha B hB u)

lemma aeSmulLpCLM_norm_le (a : X → ℝ) (ha : AEStronglyMeasurable a μ) (B : ℝ)
    (hB0 : 0 ≤ B) (hB : ∀ᵐ x ∂μ, ‖a x‖ ≤ B) :
    ‖(aeSmulLpCLM a ha B hB : Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p μ)‖ ≤ B :=
  LinearMap.mkContinuous_norm_le _ hB0 _
end GenericMul

variable {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

def chartCoefficient (Φ : OpenPartialHomeomorph (Domain d) (Domain d))
    (j k : Fin d) (x : Domain d) : ℝ := fderiv ℝ Φ x (coordinateVector j) k

lemma chartCoefficient_aemeasurable (Φ : OpenPartialHomeomorph (Domain d) (Domain d))
    (hΦ : ContDiffOn ℝ 1 Φ Φ.source) (Ω : Opens (Domain d)) (j k : Fin d) :
    AEStronglyMeasurable (chartCoefficient Φ j k)
      (volume.restrict (chartPreimage Φ Ω : Set (Domain d))) := by
  have hd := hΦ.continuousOn_fderiv_of_isOpen Φ.open_source (by simp)
  exact ((continuous_apply k).comp_continuousOn
    (hd.clm_apply continuousOn_const)).mono inter_subset_left |>.aestronglyMeasurable
      (chartPreimage Φ Ω).isOpen.measurableSet

lemma chartCoefficient_ae_bound (Φ : OpenPartialHomeomorph (Domain d) (Domain d))
    (B : ℝ) (hB : ∀ x ∈ Φ.source, ‖fderiv ℝ Φ x‖ ≤ B)
    (Ω : Opens (Domain d)) (j k : Fin d) :
    ∀ᵐ x ∂volume.restrict (chartPreimage Φ Ω : Set (Domain d)), ‖chartCoefficient Φ j k x‖ ≤ B := by
  filter_upwards [ae_restrict_mem (chartPreimage Φ Ω).isOpen.measurableSet] with x hx
  apply (norm_le_pi_norm (fderiv ℝ Φ x (coordinateVector j)) k).trans
  apply ((fderiv ℝ Φ x).le_opNorm (coordinateVector j)).trans
  simpa only [coordinateVector, Pi.norm_single, norm_one, mul_one] using hB x hx.1


section ChainJet
variable (Φ : OpenPartialHomeomorph (Domain d) (Domain d))
  (hΦ : ContDiffOn ℝ 1 Φ Φ.source) (hInv : ContDiffOn ℝ 1 Φ.symm Φ.target)
  (B : ℝ) (hB : ∀ x ∈ Φ.source, ‖fderiv ℝ Φ x‖ ≤ B)
  (J : ℝ) (hJ : ∀ y ∈ Φ.target, |(fderiv ℝ Φ.symm y).det| ≤ J)
  (Ω : Opens (Domain d))

def chartGradientLp (j k : Fin d) :
    DomainLp 𝕜 (chartTarget Φ Ω) p →L[𝕜] DomainLp 𝕜 (chartPreimage Φ Ω) p :=
  (aeSmulLpCLM (chartCoefficient Φ j k) (chartCoefficient_aemeasurable Φ hΦ Ω j k)
    B (chartCoefficient_ae_bound Φ B hB Ω j k)).comp (chartLpPull Φ hInv J hJ Ω)

lemma chartGradientLp_coe (j k : Fin d) (u : DomainLp 𝕜 (chartTarget Φ Ω) p) :
    chartGradientLp Φ hΦ hInv B hB J hJ Ω j k u =ᵐ[
      volume.restrict (chartPreimage Φ Ω : Set (Domain d))]
      fun x => chartCoefficient Φ j k x • u (Φ x) := by
  apply (aeSmulLp_coe (chartCoefficient Φ j k) (chartCoefficient_aemeasurable Φ hΦ Ω j k)
    B (chartCoefficient_ae_bound Φ B hB Ω j k) (chartLpPull Φ hInv J hJ Ω u)).trans
  filter_upwards [chartLpPull_coe Φ hInv J hJ Ω u] with x hx
  rw [Function.comp_apply] at hx
  rw [hx]

lemma chartLpPull_apply_norm_le (hJ1 : 1 ≤ J)
    (u : DomainLp 𝕜 (chartTarget Φ Ω) p) :
    ‖chartLpPull Φ hInv J hJ Ω u‖ ≤ J * ‖u‖ := by
  have hP : ‖(chartLpPull Φ hInv J hJ Ω :
      DomainLp 𝕜 (chartTarget Φ Ω) p →L[𝕜] DomainLp 𝕜 (chartPreimage Φ Ω) p)‖ ≤ J :=
    chartLpPull_norm_le Φ hInv J hJ1 hJ Ω
  have hPu := (chartLpPull (𝕜 := 𝕜) (p := p) Φ hInv J hJ Ω).le_opNorm u
  nlinarith [norm_nonneg u]

lemma chartGradientLp_norm_le (hB0 : 0 ≤ B) (hJ1 : 1 ≤ J)
    (j k : Fin d) (u : DomainLp 𝕜 (chartTarget Φ Ω) p) :
    ‖chartGradientLp Φ hΦ hInv B hB J hJ Ω j k u‖ ≤ B * J * ‖u‖ := by
  have hpull := chartLpPull_apply_norm_le Φ hInv J hJ Ω hJ1 u
  have hmul : ‖chartGradientLp Φ hΦ hInv B hB J hJ Ω j k u‖ ≤
      B * ‖chartLpPull Φ hInv J hJ Ω u‖ :=
    aeSmulLp_norm_le (chartCoefficient Φ j k)
      (chartCoefficient_aemeasurable Φ hΦ Ω j k) B
      (chartCoefficient_ae_bound Φ B hB Ω j k) (chartLpPull Φ hInv J hJ Ω u)
  nlinarith

def chartChainJet (u : DerivativeTuple 𝕜 (chartTarget Φ Ω) 1 p) :
    DerivativeTuple 𝕜 (chartPreimage Φ Ω) 1 p :=
  WithLp.toLp 1 fun α => if hα : α = zeroIndex d 1 then
    chartLpPull Φ hInv J hJ Ω (u (zeroIndex d 1)) else
    ∑ k, chartGradientLp Φ hΦ hInv B hB J hJ Ω (firstJetCoordinate α hα) k (u (coordinateIndex k))

@[simp] lemma chartChainJet_zero (u : DerivativeTuple 𝕜 (chartTarget Φ Ω) 1 p) :
    chartChainJet Φ hΦ hInv B hB J hJ Ω u (zeroIndex d 1) =
      chartLpPull Φ hInv J hJ Ω (u (zeroIndex d 1)) := by
  simp [chartChainJet]

@[simp] lemma chartChainJet_coordinate (u : DerivativeTuple 𝕜 (chartTarget Φ Ω) 1 p) (j : Fin d) :
    chartChainJet Φ hΦ hInv B hB J hJ Ω u (coordinateIndex j) =
      ∑ k, chartGradientLp Φ hΦ hInv B hB J hJ Ω j k (u (coordinateIndex k)) := by
  simp [chartChainJet]

lemma chartChainJet_coordinate_coe (u : DerivativeTuple 𝕜 (chartTarget Φ Ω) 1 p) (j : Fin d) :
    chartChainJet Φ hΦ hInv B hB J hJ Ω u (coordinateIndex j) =ᵐ[
      volume.restrict (chartPreimage Φ Ω : Set (Domain d))]
      fun x => ∑ k, chartCoefficient Φ j k x • u (coordinateIndex k) (Φ x) := by
  classical
  rw [chartChainJet_coordinate]
  refine (Lp.coeFn_finsetSum _ _).trans ?_
  exact (eventuallyEq_sum (s := Finset.univ) (fun k _ =>
    chartGradientLp_coe Φ hΦ hInv B hB J hJ Ω j k (u (coordinateIndex k)))).trans
      (Eventually.of_forall fun x => by simp only [Finset.sum_apply])

lemma chartChainJet_add (u v : DerivativeTuple 𝕜 (chartTarget Φ Ω) 1 p) :
    chartChainJet Φ hΦ hInv B hB J hJ Ω (u + v) =
      chartChainJet Φ hΦ hInv B hB J hJ Ω u + chartChainJet Φ hΦ hInv B hB J hJ Ω v := by
  classical
  apply PiLp.ext
  intro α
  simp only [chartChainJet, PiLp.toLp_apply, PiLp.add_apply]
  split_ifs <;> simp only [PiLp.add_apply, map_add, Finset.sum_add_distrib]

lemma chartChainJet_smul (c : 𝕜) (u : DerivativeTuple 𝕜 (chartTarget Φ Ω) 1 p) :
    chartChainJet Φ hΦ hInv B hB J hJ Ω (c • u) =
      c • chartChainJet Φ hΦ hInv B hB J hJ Ω u := by
  classical
  apply PiLp.ext
  intro α
  simp only [chartChainJet, PiLp.toLp_apply, PiLp.smul_apply]
  split_ifs <;> simp only [PiLp.smul_apply, map_smul, Finset.smul_sum]

def chartChainJetLM : DerivativeTuple 𝕜 (chartTarget Φ Ω) 1 p →ₗ[𝕜]
    DerivativeTuple 𝕜 (chartPreimage Φ Ω) 1 p where
  toFun := chartChainJet Φ hΦ hInv B hB J hJ Ω
  map_add' := chartChainJet_add Φ hΦ hInv B hB J hJ Ω
  map_smul' := chartChainJet_smul Φ hΦ hInv B hB J hJ Ω

lemma chartChainJet_norm_le (hB0 : 0 ≤ B) (hJ1 : 1 ≤ J)
    (u : DerivativeTuple 𝕜 (chartTarget Φ Ω) 1 p) :
    ‖chartChainJet Φ hΦ hInv B hB J hJ Ω u‖ ≤
      (Fintype.card (DerivativeIndex d 1) * (J + d * B * J)) * ‖u‖ := by
  classical
  have hJ0 : 0 ≤ J := zero_le_one.trans hJ1
  have hcomp (α : DerivativeIndex d 1) :
      ‖chartChainJet Φ hΦ hInv B hB J hJ Ω u α‖ ≤ (J + d * B * J) * ‖u‖ := by
    simp only [chartChainJet, PiLp.toLp_apply]
    split_ifs with hα
    · calc
        ‖chartLpPull Φ hInv J hJ Ω (u (zeroIndex d 1))‖ ≤ J * ‖u (zeroIndex d 1)‖ :=
          chartLpPull_apply_norm_le Φ hInv J hJ Ω hJ1 _
        _ ≤ J * ‖u‖ := mul_le_mul_of_nonneg_left (PiLp.norm_apply_le u _) hJ0
        _ ≤ _ := by nlinarith [norm_nonneg u, show (0:ℝ) ≤ d * B * J by positivity]
    · calc
        ‖∑ k, chartGradientLp Φ hΦ hInv B hB J hJ Ω (firstJetCoordinate α hα) k (u (coordinateIndex k))‖ ≤
            ∑ k : Fin d, B * J * ‖u‖ := by
          apply (norm_sum_le _ _).trans
          apply Finset.sum_le_sum
          intro k hk
          exact (chartGradientLp_norm_le Φ hΦ hInv B hB J hJ Ω hB0 hJ1 _ k _).trans
            (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le u _) (mul_nonneg hB0 hJ0))
        _ = d * B * J * ‖u‖ := by simp; ring
        _ ≤ _ := by nlinarith [norm_nonneg u]
  rw [PiLp.norm_eq_of_L1]
  calc
    _ ≤ ∑ _α : DerivativeIndex d 1, (J + d * B * J) * ‖u‖ :=
      Finset.sum_le_sum fun α _ => hcomp α
    _ = _ := by simp [mul_assoc]

def chartChainJetCLM (hB0 : 0 ≤ B) (hJ1 : 1 ≤ J) :
    DerivativeTuple 𝕜 (chartTarget Φ Ω) 1 p →L[𝕜] DerivativeTuple 𝕜 (chartPreimage Φ Ω) 1 p :=
  (chartChainJetLM Φ hΦ hInv B hB J hJ Ω).mkContinuous
    (Fintype.card (DerivativeIndex d 1) * (J + d * B * J))
    (chartChainJet_norm_le Φ hΦ hInv B hB J hJ Ω hB0 hJ1)

end ChainJet
end ExpandedFA.Sobolev.C1Extension.Transport


namespace ExpandedFA.Sobolev.C1Extension.Transport
open Filter
open ExpandedFA.Distributions ExpandedFA.Sobolev ExpandedFA.Sobolev.HalfSpace
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
open _root_.ExpandedFA.Sobolev.C1Extension.Classical
variable {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

lemma chart_smooth_chain_coordinate
    (Φ : OpenPartialHomeomorph (Domain d) (Domain d))
    (hΦ : ContDiffOn ℝ 1 Φ Φ.source) (Ω : Opens (Domain d))
    (f : Domain d → 𝕜) (hf : ContDiffOn ℝ 1 f (chartTarget Φ Ω))
    (x : Domain d) (hx : x ∈ chartPreimage Φ Ω) (j : Fin d) :
    fderiv ℝ (f ∘ Φ) x (coordinateVector j) =
      ∑ k, chartCoefficient Φ j k x • fderiv ℝ f (Φ x) (coordinateVector k) := by
  have hxf : Φ x ∈ chartTarget Φ Ω := ⟨hx.2, Φ.map_source hx.1⟩
  have hdΦ := (hΦ.contDiffAt (Φ.open_source.mem_nhds hx.1)).differentiableAt (by simp)
  have hdf := (hf.contDiffAt ((chartTarget Φ Ω).isOpen.mem_nhds hxf)).differentiableAt (by simp)
  rw [fderiv_comp x hdf hdΦ]
  change fderiv ℝ f (Φ x) (fderiv ℝ Φ x (coordinateVector j)) = _
  calc
    _ = fderiv ℝ f (Φ x) (∑ k, chartCoefficient Φ j k x • coordinateVector k) :=
      congrArg _ (pi_eq_sum_univ' (fderiv ℝ Φ x (coordinateVector j)))
    _ = _ := by simp only [map_sum, map_smul]

lemma chartChainJet_mem_of_smooth
    (Φ : OpenPartialHomeomorph (Domain d) (Domain d))
    (hΦ : ContDiffOn ℝ 1 Φ Φ.source) (hInv : ContDiffOn ℝ 1 Φ.symm Φ.target)
    (B : ℝ) (hB : ∀ x ∈ Φ.source, ‖fderiv ℝ Φ x‖ ≤ B)
    (J : ℝ) (hJ : ∀ y ∈ Φ.target, |(fderiv ℝ Φ.symm y).det| ≤ J)
    (Ω : Opens (Domain d)) (u : SpaceValue 𝕜 d (chartTarget Φ Ω) 1 p)
    (f : Domain d → 𝕜) (hf : ContDiffOn ℝ 1 f (chartTarget Φ Ω))
    (hu : u.val (zeroIndex d 1) =ᵐ[volume.restrict (chartTarget Φ Ω : Set (Domain d))] f) :
    chartChainJet Φ hΦ hInv B hB J hJ Ω u.val ∈ derivativeGraph 𝕜 (chartPreimage Φ Ω) 1 p := by
  have hcomp : ContDiffOn ℝ 1 (f ∘ Φ) (chartPreimage Φ Ω) :=
    hf.comp (hΦ.mono inter_subset_left) (fun x hx => ⟨hx.2, Φ.map_source hx.1⟩)
  apply Classical.c1_firstJet_mem (f ∘ Φ) hcomp
  · rw [chartChainJet_zero]
    exact pullLp_coe_of_ae_eq (chart_aemeasurable Φ Ω) ENNReal.ofReal_ne_top
      (chart_map_measure_le Φ hInv J hJ Ω) (u.val (zeroIndex d 1)) f hu.symm
  · intro j
    apply (chartChainJet_coordinate_coe Φ hΦ hInv B hB J hJ Ω u.val j).trans
    have hg (k : Fin d) : (fun x => u.val (coordinateIndex k) (Φ x)) =ᵐ[
        volume.restrict (chartPreimage Φ Ω : Set (Domain d))]
        (fun x => fderiv ℝ f (Φ x) (coordinateVector k)) := by
      have hk := Classical.c1_representative_derivative u f hf hu k
      have h₁ := chartLpPull_coe Φ hInv J hJ Ω (u.val (coordinateIndex k))
      have h₂ := pullLp_coe_of_ae_eq (chart_aemeasurable Φ Ω) ENNReal.ofReal_ne_top
        (chart_map_measure_le Φ hInv J hJ Ω) (u.val (coordinateIndex k))
        (fun x => fderiv ℝ f x (coordinateVector k)) hk.symm
      exact h₁.symm.trans h₂
    filter_upwards [ae_all_iff.mpr hg, ae_restrict_mem (chartPreimage Φ Ω).isOpen.measurableSet]
      with x hx hxU
    rw [chart_smooth_chain_coordinate Φ hΦ Ω f hf x hxU j]
    exact Finset.sum_congr rfl (fun k _ => congrArg (chartCoefficient Φ j k x • ·) (hx k))

lemma chartChainJet_mem_finite_of_continuous
    (Φ : OpenPartialHomeomorph (Domain d) (Domain d))
    (hΦ : ContDiffOn ℝ 1 Φ Φ.source) (hInv : ContDiffOn ℝ 1 Φ.symm Φ.target)
    (B : ℝ) (hB : ∀ x ∈ Φ.source, ‖fderiv ℝ Φ x‖ ≤ B) (hB0 : 0 ≤ B)
    (J : ℝ) (hJ : ∀ y ∈ Φ.target, |(fderiv ℝ Φ.symm y).det| ≤ J) (hJ1 : 1 ≤ J)
    (Ω : Opens (Domain d)) (hp : p ≠ ∞)
    (hcont : Continuous (chartChainJet (𝕜 := 𝕜) (p := p) Φ hΦ hInv B hB J hJ Ω))
    (u : SpaceValue 𝕜 d (chartTarget Φ Ω) 1 p) :
    chartChainJet Φ hΦ hInv B hB J hJ Ω u.val ∈ derivativeGraph 𝕜 (chartPreimage Φ Ω) 1 p := by
  let F : SpaceValue 𝕜 d (chartTarget Φ Ω) 1 p →
      DerivativeTuple 𝕜 (chartPreimage Φ Ω) 1 p :=
    fun u => chartChainJet Φ hΦ hInv B hB J hJ Ω u.val
  have hc : IsClosed {v : SpaceValue 𝕜 d (chartTarget Φ Ω) 1 p |
      F v ∈ derivativeGraph 𝕜 (chartPreimage Φ Ω) 1 p} :=
    Smoothing.derivativeGraph_isClosed.preimage (hcont.comp continuous_subtype_val)
  have hsub : Specs.ExpandedFA.Sobolev.SobolevSmoothingAndDensity.SmoothMembers
      𝕜 d (chartTarget Φ Ω) 1 p ⊆
      {v : SpaceValue 𝕜 d (chartTarget Φ Ω) 1 p |
        F v ∈ derivativeGraph 𝕜 (chartPreimage Φ Ω) 1 p} := by
    rintro v ⟨f, hf, hvf⟩
    exact chartChainJet_mem_of_smooth Φ hΦ hInv B hB J hJ Ω v f (hf.of_le (by simp)) hvf
  exact (hc.closure_subset_iff.mpr hsub) (Smoothing.smooth_density 𝕜 d (chartTarget Φ Ω) 1 p hp u)

end ExpandedFA.Sobolev.C1Extension.Transport



namespace ExpandedFA.Sobolev.C1Extension.Transport
open Filter
open ExpandedFA.Distributions ExpandedFA.Sobolev ExpandedFA.Sobolev.HalfSpace
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
variable {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

lemma chartChainJet_congr_exponent
    (Φ : OpenPartialHomeomorph (Domain d) (Domain d))
    (hΦ : ContDiffOn ℝ 1 Φ Φ.source) (hInv : ContDiffOn ℝ 1 Φ.symm Φ.target)
    (B : ℝ) (hB : ∀ x ∈ Φ.source, ‖fderiv ℝ Φ x‖ ≤ B)
    (J : ℝ) (hJ : ∀ y ∈ Φ.target, |(fderiv ℝ Φ.symm y).det| ≤ J)
    (Ω : Opens (Domain d))
    (u : DerivativeTuple 𝕜 (chartTarget Φ Ω) 1 p)
    (v : DerivativeTuple 𝕜 (chartTarget Φ Ω) 1 q)
    (huv : ∀ α, u α =ᵐ[volume.restrict (chartTarget Φ Ω : Set (Domain d))] v α)
    (α : DerivativeIndex d 1) :
    chartChainJet Φ hΦ hInv B hB J hJ Ω u α =ᵐ[
      volume.restrict (chartPreimage Φ Ω : Set (Domain d))]
      chartChainJet Φ hΦ hInv B hB J hJ Ω v α := by
  have hcomp (β : DerivativeIndex d 1) : (fun x => u β (Φ x)) =ᵐ[
      volume.restrict (chartPreimage Φ Ω : Set (Domain d))] (fun x => v β (Φ x)) :=
    ae_of_ae_map (chart_aemeasurable Φ Ω)
      ((Measure.absolutelyContinuous_of_le_smul (chart_map_measure_le Φ hInv J hJ Ω)).ae_eq (huv β))
  rcases Lines.multiIndex_order_one_cases (natIndex α) α.property with hz | ⟨j, hj⟩
  · have hα : α = zeroIndex d 1 := derivativeIndex_ext hz
    subst α
    rw [chartChainJet_zero, chartChainJet_zero]
    exact (chartLpPull_coe Φ hInv J hJ Ω _).trans
      ((hcomp _).trans (chartLpPull_coe Φ hInv J hJ Ω _).symm)
  · have hα : α = coordinateIndex j := derivativeIndex_ext (by simpa [coordinateIndex] using hj)
    subst α
    apply (chartChainJet_coordinate_coe Φ hΦ hInv B hB J hJ Ω u j).trans
    apply EventuallyEq.trans ?_ (chartChainJet_coordinate_coe Φ hΦ hInv B hB J hJ Ω v j).symm
    filter_upwards [ae_all_iff.mpr (fun k : Fin d => hcomp (coordinateIndex k))] with x hx
    exact Finset.sum_congr rfl (fun k _ => congrArg (chartCoefficient Φ j k x • ·) (hx k))

lemma chartChainJet_mem_all_of_finite_target
    (Φ : OpenPartialHomeomorph (Domain d) (Domain d))
    (hΦ : ContDiffOn ℝ 1 Φ Φ.source) (hInv : ContDiffOn ℝ 1 Φ.symm Φ.target)
    (B : ℝ) (hB : ∀ x ∈ Φ.source, ‖fderiv ℝ Φ x‖ ≤ B) (hB0 : 0 ≤ B)
    (J : ℝ) (hJ : ∀ y ∈ Φ.target, |(fderiv ℝ Φ.symm y).det| ≤ J) (hJ1 : 1 ≤ J)
    (Ω : Opens (Domain d))
    [IsFiniteMeasure (volume.restrict (chartTarget Φ Ω : Set (Domain d)))]
    (hcont : Continuous (chartChainJet (𝕜 := 𝕜) (p := 1) Φ hΦ hInv B hB J hJ Ω))
    (u : SpaceValue 𝕜 d (chartTarget Φ Ω) 1 p) :
    chartChainJet Φ hΦ hInv B hB J hJ Ω u.val ∈ derivativeGraph 𝕜 (chartPreimage Φ Ω) 1 p := by
  let u₁ : SpaceValue 𝕜 d (chartTarget Φ Ω) 1 1 := lowerExponent (q := 1) Fact.out u
  let v₁ := chartChainJet (p := 1) Φ hΦ hInv B hB J hJ Ω u₁.val
  let v := chartChainJet Φ hΦ hInv B hB J hJ Ω u.val
  have hv₁ : v₁ ∈ derivativeGraph 𝕜 (chartPreimage Φ Ω) 1 1 :=
    chartChainJet_mem_finite_of_continuous Φ hΦ hInv B hB hB0 J hJ hJ1 Ω (by simp) hcont u₁
  have hcongr (α : DerivativeIndex d 1) : v α =ᵐ[
      volume.restrict (chartPreimage Φ Ω : Set (Domain d))] v₁ α :=
    chartChainJet_congr_exponent Φ hΦ hInv B hB J hJ Ω u.val u₁.val
      (fun β => (lowerExponent_coe (q := 1) Fact.out u β).symm) α
  intro α
  change lpDistribution (v α) =
    Specs.ExpandedFA.Distributions.DistributionCalculus.multiIndexDerivativeValue
      𝕜 d (chartPreimage Φ Ω) (natIndex α) (lpDistribution (v (zeroIndex d 1)))
  rw [lpDistribution_eq_of_ae_exponent (v α) (v₁ α) (hcongr α),
    lpDistribution_eq_of_ae_exponent (v (zeroIndex d 1)) (v₁ (zeroIndex d 1)) (hcongr _)]
  exact hv₁ α

end ExpandedFA.Sobolev.C1Extension.Transport


namespace ExpandedFA.Sobolev.C1Extension
open ExpandedFA.Distributions HalfSpace
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

def rawComposition {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (F : Domain d → Domain d) :
    (Domain d → 𝕜) →ₗ[𝕜] (Domain d → 𝕜) where
  toFun f := f ∘ F
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def rawReflection {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (i : Fin d) :
    (Domain d → 𝕜) →ₗ[𝕜] (Domain d → 𝕜) where
  toFun := reflection i false
  map_add' := reflection_add i false
  map_smul' := reflection_smul i false

set_option maxHeartbeats 800000 in
theorem boundary_piece_of_transports {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Ω : Opens (Domain d)) (i : Fin d)
    (Φ : OpenPartialHomeomorph (Domain d) (Domain d))
    (hside : ∀ x ∈ Φ.source, x ∈ Ω ↔ 0 < Φ x i)
    (θ : Tests 𝕜 (⊤ : Opens (Domain d))) (hθ : tsupport θ ⊆ Φ.source)
    (P : ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)],
      SpaceValue 𝕜 d (Ω ⊓ ⟨Φ.source, Φ.open_source⟩) 1 p →L[𝕜]
        SpaceValue 𝕜 d (⟨Φ.target, Φ.open_target⟩ ⊓ upper i) 1 p)
    (hP : ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)]
      (u : SpaceValue 𝕜 d (Ω ⊓ ⟨Φ.source, Φ.open_source⟩) 1 p) (f : Domain d → 𝕜),
      f =ᵐ[volume.restrict ((Ω ⊓ ⟨Φ.source, Φ.open_source⟩ : Opens (Domain d)) : Set (Domain d))]
        u.val (zeroIndex d 1) →
      (P p u).val (zeroIndex d 1) =ᵐ[volume.restrict
        ((⟨Φ.target, Φ.open_target⟩ ⊓ upper i : Opens (Domain d)) : Set (Domain d))] f ∘ Φ.symm)
    (Q : ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)],
      SpaceValue 𝕜 d ⟨Φ.target, Φ.open_target⟩ 1 p →L[𝕜]
        SpaceValue 𝕜 d ⟨Φ.source, Φ.open_source⟩ 1 p)
    (hQ : ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)]
      (u : SpaceValue 𝕜 d ⟨Φ.target, Φ.open_target⟩ 1 p) (f : Domain d → 𝕜),
      f =ᵐ[volume.restrict Φ.target] u.val (zeroIndex d 1) →
      (Q p u).val (zeroIndex d 1) =ᵐ[volume.restrict Φ.source] f ∘ Φ) :
    ∃ (T : (Domain d → 𝕜) →ₗ[𝕜] (Domain d → 𝕜))
      (E : ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)],
        SpaceValue 𝕜 d Ω 1 p →L[𝕜] SpaceValue 𝕜 d ⊤ 1 p),
      (∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : SpaceValue 𝕜 d Ω 1 p),
        (E p u).val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))]
          fun x => θ x * u.val (zeroIndex d 1) x) ∧
      (∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : SpaceValue 𝕜 d Ω 1 p) (f : Domain d → 𝕜),
        f =ᵐ[volume.restrict (Ω : Set (Domain d))] u.val (zeroIndex d 1) →
        (E p u).val (zeroIndex d 1) =ᵐ[volume] T f) := by
  classical
  let A : Opens (Domain d) := ⟨Φ.source, Φ.open_source⟩
  let B : Opens (Domain d) := ⟨Φ.target, Φ.open_target⟩
  let V : Opens (Domain d) := B ⊓ upper i
  obtain ⟨χ, hχ, hχone⟩ := exists_chart_cutoff Φ θ hθ
  obtain ⟨Cχ, hCχ0, hCχ, hDχ⟩ := ambient_test_bounds χ
  obtain ⟨Cθ, hCθ0, hCθ, hDθ⟩ := ambient_test_bounds θ
  let K : Set (Domain d) := tsupport χ ∩ (upper i : Set (Domain d))
  have hK : IsClosed (K ∪ (upper i : Set (Domain d))ᶜ) := by
    have heq : K ∪ (upper i : Set (Domain d))ᶜ = tsupport χ ∪ (upper i : Set (Domain d))ᶜ := by
      ext x
      simp only [K, mem_union, mem_inter_iff, mem_compl_iff]
      tauto
    rw [heq]
    exact (isClosed_tsupport χ).union (upper i).isOpen.isClosed_compl
  have hKV : K ⊆ V := fun x hx => ⟨hχ hx.1, hx.2⟩
  have hχK : (V : Set (Domain d)) ∩ tsupport χ ⊆ K := fun x hx => ⟨hx.2, hx.1.2⟩
  have hθK : IsClosed (tsupport θ ∪ ((⊤ : Opens (Domain d)) : Set (Domain d))ᶜ) := by simpa using isClosed_tsupport θ
  let Mχ : ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)],
      SpaceValue 𝕜 d V 1 p →L[𝕜] SpaceValue 𝕜 d (upper i) 1 p := fun p _ =>
    localizedZeroExtension inf_le_right K hK hKV χ χ.contDiff Cχ hCχ0 hCχ hDχ hχK
  let Mθ : ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)],
      SpaceValue 𝕜 d A 1 p →L[𝕜] SpaceValue 𝕜 d ⊤ 1 p := fun p _ =>
    localizedZeroExtension le_top (tsupport θ) hθK hθ θ θ.contDiff Cθ hCθ0 hCθ hDθ inter_subset_right
  let R : ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)],
      SpaceValue 𝕜 d (upper i) 1 p →L[𝕜] SpaceValue 𝕜 d ⊤ 1 p := fun p _ =>
    sobolevReflection weak_reflection i
  let E : ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)],
      SpaceValue 𝕜 d Ω 1 p →L[𝕜] SpaceValue 𝕜 d ⊤ 1 p := fun p _ =>
    (Mθ p).comp ((Q p).comp ((restrictSobolev (le_top : B ≤ ⊤)).comp
      ((R p).comp ((Mχ p).comp ((P p).comp (restrictSobolev (inf_le_left : Ω ⊓ A ≤ Ω)))))))
  let T : (Domain d → 𝕜) →ₗ[𝕜] (Domain d → 𝕜) :=
    (localizedRaw A θ).comp ((rawComposition Φ).comp ((rawReflection i).comp
      ((localizedRaw V χ).comp (rawComposition Φ.symm))))
  have hT : ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : SpaceValue 𝕜 d Ω 1 p) (f : Domain d → 𝕜),
      f =ᵐ[volume.restrict (Ω : Set (Domain d))] u.val (zeroIndex d 1) →
      (E p u).val (zeroIndex d 1) =ᵐ[volume] T f := by
    intro p _ u f hf
    let uS := restrictSobolev (inf_le_left : Ω ⊓ A ≤ Ω) u
    have hS : f =ᵐ[volume.restrict ((Ω ⊓ A : Opens (Domain d)) : Set (Domain d))] uS.val (zeroIndex d 1) :=
      (hf.filter_mono (ae_mono (Measure.restrict_mono (inf_le_left : Ω ⊓ A ≤ Ω) le_rfl))).trans
        (restrictSobolev_coe inf_le_left u _).symm
    have hpull := hP p uS f hS
    have hmul := localizedZeroExtension_representative inf_le_right K hK hKV χ χ.contDiff
      Cχ hCχ0 hCχ hDχ hχK (P p uS) (f ∘ Φ.symm) hpull.symm
    have href : (R p (Mχ p (P p uS))).val (zeroIndex d 1) =ᵐ[volume]
        reflection i false ((Mχ p (P p uS)).val (zeroIndex d 1)) := by
      change reflectLp i (normalParity i (zeroIndex d 1)) _ =ᵐ[volume] _
      rw [normalParity_zero]
      exact reflectLp_coe i false _
    have href' := href.trans (reflection_congr i false hmul)
    have hB := (restrictSobolev_coe (le_top : B ≤ ⊤) (R p (Mχ p (P p uS))) (zeroIndex d 1)).trans
      (href'.filter_mono (ae_mono (Measure.restrict_le_self (s := (B : Set (Domain d))))))
    have hback := hQ p (restrictSobolev (le_top : B ≤ ⊤) (R p (Mχ p (P p uS))))
      (reflection i false (localizedRaw V χ (f ∘ Φ.symm))) hB.symm
    change (Mθ p (Q p (restrictSobolev (le_top : B ≤ ⊤) (R p (Mχ p (P p uS)))))).val (zeroIndex d 1)
      =ᵐ[volume] localizedRaw A θ ((reflection i false (localizedRaw V χ (f ∘ Φ.symm))) ∘ Φ)
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      (localizedZeroExtension_representative le_top (tsupport θ) hθK hθ θ θ.contDiff
        Cθ hCθ0 hCθ hDθ inter_subset_right
        (Q p (restrictSobolev (le_top : B ≤ ⊤) (R p (Mχ p (P p uS)))))
        ((reflection i false (localizedRaw V χ (f ∘ Φ.symm))) ∘ Φ) hback.symm)
  have hpoint (f : Domain d → 𝕜) (x : Domain d) (hxΩ : x ∈ Ω) : T f x = θ x * f x := by
    change (A : Set (Domain d)).indicator
      (fun y => θ y * reflection i false (localizedRaw V χ (f ∘ Φ.symm)) (Φ y)) x = _
    by_cases hxA : x ∈ A
    · have hxH : Φ x ∈ upper i := (hside x hxA).mp hxΩ
      rw [indicator_of_mem hxA, reflection_of_pos i false _ hxH]
      have hxV : Φ x ∈ V := ⟨Φ.map_source hxA, hxH⟩
      change θ x * ((V : Set (Domain d)).indicator (fun y => χ y * f (Φ.symm y)) (Φ x)) = _
      rw [indicator_of_mem hxV, Φ.left_inv hxA]
      by_cases hxθ : x ∈ tsupport θ
      · rw [hχone x hxθ, one_mul]
      · rw [image_eq_zero_of_notMem_tsupport hxθ, zero_mul, zero_mul]
    · rw [indicator_of_notMem hxA, image_eq_zero_of_notMem_tsupport (fun h => hxA (hθ h)), zero_mul]
  refine ⟨T, E, ?_, hT⟩
  intro p _ u
  have heq := (hT p u (u.val (zeroIndex d 1)) Filter.EventuallyEq.rfl).filter_mono
    (ae_mono (Measure.restrict_le_self (s := (Ω : Set (Domain d)))))
  filter_upwards [heq, ae_restrict_mem Ω.isOpen.measurableSet] with x hx hxΩ
  exact hx.trans (hpoint _ x hxΩ)

end ExpandedFA.Sobolev.C1Extension


namespace ExpandedFA.Sobolev.C1Extension.Transport
open ExpandedFA.Distributions ExpandedFA.Sobolev ExpandedFA.Sobolev.HalfSpace
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
variable {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

section Wrapper
variable (Φ : OpenPartialHomeomorph (Domain d) (Domain d))
  (hΦ : ContDiffOn ℝ 1 Φ Φ.source) (hInv : ContDiffOn ℝ 1 Φ.symm Φ.target)
  (B : ℝ) (hB : ∀ x ∈ Φ.source, ‖fderiv ℝ Φ x‖ ≤ B) (hB0 : 0 ≤ B)
  (J : ℝ) (hJ : ∀ y ∈ Φ.target, |(fderiv ℝ Φ.symm y).det| ≤ J) (hJ1 : 1 ≤ J)
  (Ω : Opens (Domain d)) (hTarget : Bornology.IsBounded Φ.target)

def chartSobolevPull : SpaceValue 𝕜 d (chartTarget Φ Ω) 1 p →L[𝕜]
    SpaceValue 𝕜 d (chartPreimage Φ Ω) 1 p := by
  letI : IsFiniteMeasure (volume.restrict (chartTarget Φ Ω : Set (Domain d))) :=
    isFiniteMeasure_restrict.mpr ((hTarget.subset inter_subset_right).measure_lt_top.ne)
  exact (chartChainJetCLM Φ hΦ hInv B hB J hJ Ω hB0 hJ1).restrict
    (fun u hu => chartChainJet_mem_all_of_finite_target Φ hΦ hInv B hB hB0 J hJ hJ1 Ω
      (chartChainJetCLM (𝕜 := 𝕜) (p := 1) Φ hΦ hInv B hB J hJ Ω hB0 hJ1).continuous ⟨u, hu⟩)

lemma chartSobolevPull_val (u : SpaceValue 𝕜 d (chartTarget Φ Ω) 1 p) :
    (chartSobolevPull Φ hΦ hInv B hB hB0 J hJ hJ1 Ω hTarget u).val =
      chartChainJet Φ hΦ hInv B hB J hJ Ω u.val := rfl

lemma chartSobolevPull_coe (u : SpaceValue 𝕜 d (chartTarget Φ Ω) 1 p)
    (f : Domain d → 𝕜)
    (hf : f =ᵐ[volume.restrict (chartTarget Φ Ω : Set (Domain d))] u.val (zeroIndex d 1)) :
    (chartSobolevPull Φ hΦ hInv B hB hB0 J hJ hJ1 Ω hTarget u).val (zeroIndex d 1) =ᵐ[
      volume.restrict (chartPreimage Φ Ω : Set (Domain d))] f ∘ Φ := by
  rw [chartSobolevPull_val, chartChainJet_zero]
  exact pullLp_coe_of_ae_eq (chart_aemeasurable Φ Ω) ENNReal.ofReal_ne_top
    (chart_map_measure_le Φ hInv J hJ Ω) (u.val (zeroIndex d 1)) f hf

lemma chartSobolevPull_coordinate_coe (u : SpaceValue 𝕜 d (chartTarget Φ Ω) 1 p) (j : Fin d) :
    (chartSobolevPull Φ hΦ hInv B hB hB0 J hJ hJ1 Ω hTarget u).val (coordinateIndex j) =ᵐ[
      volume.restrict (chartPreimage Φ Ω : Set (Domain d))]
      fun x => ∑ k, chartCoefficient Φ j k x • u.val (coordinateIndex k) (Φ x) := by
  rw [chartSobolevPull_val]
  exact chartChainJet_coordinate_coe Φ hΦ hInv B hB J hJ Ω u.val j

lemma chartSobolevPull_norm_le :
    ‖(chartSobolevPull Φ hΦ hInv B hB hB0 J hJ hJ1 Ω hTarget :
      SpaceValue 𝕜 d (chartTarget Φ Ω) 1 p →L[𝕜] SpaceValue 𝕜 d (chartPreimage Φ Ω) 1 p)‖ ≤
      Fintype.card (DerivativeIndex d 1) * (J + d * B * J) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  change ‖chartChainJet Φ hΦ hInv B hB J hJ Ω u.val‖ ≤
    (Fintype.card (DerivativeIndex d 1) * (J + d * B * J)) * ‖u.val‖
  exact chartChainJet_norm_le Φ hΦ hInv B hB J hJ Ω hB0 hJ1 u.val

end Wrapper
end ExpandedFA.Sobolev.C1Extension.Transport


namespace ExpandedFA.Sobolev.C1Extension.Transport
open ExpandedFA.Distributions ExpandedFA.Sobolev.HalfSpace

@[simp] theorem chartPreimage_top {d : ℕ}
    (Φ : OpenPartialHomeomorph (Domain d) (Domain d)) :
    chartPreimage Φ ⊤ = ⟨Φ.source, Φ.open_source⟩ := by
  ext x
  simp [chartPreimage]

@[simp] theorem chartTarget_top {d : ℕ}
    (Φ : OpenPartialHomeomorph (Domain d) (Domain d)) :
    chartTarget Φ ⊤ = ⟨Φ.target, Φ.open_target⟩ := by
  ext x
  simp [chartTarget]

@[simp] theorem chartTarget_symm {d : ℕ}
    (Φ : OpenPartialHomeomorph (Domain d) (Domain d)) (Ω : Opens (Domain d)) :
    chartTarget Φ.symm Ω = Ω ⊓ ⟨Φ.source, Φ.open_source⟩ := rfl

theorem chartPreimage_symm_of_side {d : ℕ}
    (Φ : OpenPartialHomeomorph (Domain d) (Domain d)) (Ω : Opens (Domain d))
    (i : Fin d) (hside : ∀ x ∈ Φ.source, x ∈ Ω ↔ 0 < Φ x i) :
    chartPreimage Φ.symm Ω = ⟨Φ.target, Φ.open_target⟩ ⊓ upper i := by
  ext y
  change (y ∈ Φ.target ∧ Φ.symm y ∈ Ω) ↔ (y ∈ Φ.target ∧ 0 < y i)
  constructor
  · rintro ⟨hy, hΩ⟩
    refine ⟨hy, ?_⟩
    have hp := (hside (Φ.symm y) (Φ.map_target hy)).mp hΩ
    simpa only [Φ.right_inv hy] using hp
  · rintro ⟨hy, hpos⟩
    refine ⟨hy, (hside (Φ.symm y) (Φ.map_target hy)).mpr ?_⟩
    simpa only [Φ.right_inv hy] using hpos

end ExpandedFA.Sobolev.C1Extension.Transport


namespace ExpandedFA.Sobolev.C1Extension
open ExpandedFA.Distributions ExpandedFA.Sobolev ExpandedFA.Sobolev.HalfSpace
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces Transport

set_option maxHeartbeats 800000 in
theorem boundary_chart_piece {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Ω : Opens (Domain d)) (i : Fin d)
    (Φ : OpenPartialHomeomorph (Domain d) (Domain d))
    (hΦ : ContDiffOn ℝ 1 Φ Φ.source) (hInv : ContDiffOn ℝ 1 Φ.symm Φ.target)
    (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ x ∈ Φ.source, ‖fderiv ℝ Φ x‖ ≤ B)
    (hBinv : ∀ x ∈ Φ.target, ‖fderiv ℝ Φ.symm x‖ ≤ B)
    (hSource : Bornology.IsBounded Φ.source) (hTarget : Bornology.IsBounded Φ.target)
    (hside : ∀ x ∈ Φ.source, x ∈ Ω ↔ 0 < Φ x i)
    (θ : Tests 𝕜 (⊤ : Opens (Domain d))) (hθ : tsupport θ ⊆ Φ.source) :
    ∃ (T : (Domain d → 𝕜) →ₗ[𝕜] (Domain d → 𝕜))
      (E : ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)],
        SpaceValue 𝕜 d Ω 1 p →L[𝕜] SpaceValue 𝕜 d ⊤ 1 p),
      (∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : SpaceValue 𝕜 d Ω 1 p),
        (E p u).val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))]
          fun x => θ x * u.val (zeroIndex d 1) x) ∧
      (∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : SpaceValue 𝕜 d Ω 1 p) (f : Domain d → 𝕜),
        f =ᵐ[volume.restrict (Ω : Set (Domain d))] u.val (zeroIndex d 1) →
        (E p u).val (zeroIndex d 1) =ᵐ[volume] T f) := by
  obtain ⟨J, hJ1, hJ⟩ := exists_det_bound_of_norm_bound (E := Domain d) B
  have hJsrc : ∀ x ∈ Φ.source, |(fderiv ℝ Φ x).det| ≤ J :=
    fun x hx => hJ _ (hB x hx)
  have hJtgt : ∀ x ∈ Φ.target, |(fderiv ℝ Φ.symm x).det| ≤ J :=
    fun x hx => hJ _ (hBinv x hx)
  have hPall (p : ℝ≥0∞) [Fact (1 ≤ p)] :
      ∃ P : SpaceValue 𝕜 d (Ω ⊓ ⟨Φ.source, Φ.open_source⟩) 1 p →L[𝕜]
          SpaceValue 𝕜 d (⟨Φ.target, Φ.open_target⟩ ⊓ upper i) 1 p,
        ∀ (u : SpaceValue 𝕜 d (Ω ⊓ ⟨Φ.source, Φ.open_source⟩) 1 p) (f : Domain d → 𝕜),
          f =ᵐ[volume.restrict ((Ω ⊓ ⟨Φ.source, Φ.open_source⟩ : Opens (Domain d)) : Set (Domain d))]
            u.val (zeroIndex d 1) →
          (P u).val (zeroIndex d 1) =ᵐ[volume.restrict
            ((⟨Φ.target, Φ.open_target⟩ ⊓ upper i : Opens (Domain d)) : Set (Domain d))] f ∘ Φ.symm := by
    rw [← chartPreimage_symm_of_side Φ Ω i hside]
    refine ⟨chartSobolevPull Φ.symm hInv hΦ B hBinv hB0 J hJsrc hJ1 Ω hSource, ?_⟩
    intro u f hf
    exact chartSobolevPull_coe Φ.symm hInv hΦ B hBinv hB0 J hJsrc hJ1 Ω hSource u f hf
  have hQall (p : ℝ≥0∞) [Fact (1 ≤ p)] :
      ∃ Q : SpaceValue 𝕜 d ⟨Φ.target, Φ.open_target⟩ 1 p →L[𝕜]
          SpaceValue 𝕜 d ⟨Φ.source, Φ.open_source⟩ 1 p,
        ∀ (u : SpaceValue 𝕜 d ⟨Φ.target, Φ.open_target⟩ 1 p) (f : Domain d → 𝕜),
          f =ᵐ[volume.restrict Φ.target] u.val (zeroIndex d 1) →
          (Q u).val (zeroIndex d 1) =ᵐ[volume.restrict Φ.source] f ∘ Φ := by
    rw [← chartPreimage_top Φ, ← chartTarget_top Φ]
    refine ⟨chartSobolevPull Φ hΦ hInv B hB hB0 J hJtgt hJ1 ⊤ hTarget, ?_⟩
    intro u f hf
    simpa [chartPreimage] using
      (chartSobolevPull_coe Φ hΦ hInv B hB hB0 J hJtgt hJ1 ⊤ hTarget u f
        (by simpa [chartTarget] using hf))
  let P := fun (p : ℝ≥0∞) [Fact (1 ≤ p)] => Classical.choose (hPall p)
  let Q := fun (p : ℝ≥0∞) [Fact (1 ≤ p)] => Classical.choose (hQall p)
  exact boundary_piece_of_transports Ω i Φ hside θ hθ P
    (fun p _ => Classical.choose_spec (hPall p)) Q (fun p _ => Classical.choose_spec (hQall p))
end ExpandedFA.Sobolev.C1Extension


namespace ExpandedFA.Sobolev.C1Extension
open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

set_option maxHeartbeats 800000 in
theorem extension_exists : Specs.ExpandedFA.Sobolev.C1DomainExtension.ExtensionExists := by
  classical
  intro 𝕜 _ d Ω hΩ hcompact
  obtain ⟨n, i, Φ, B, hB0, hcharts, hcover⟩ := finite_bounded_boundary_charts d Ω hΩ hcompact
  obtain ⟨a, S, C, ha, hC0, hC, hD, hsum, hsupp, hSc, hSΩ, hS⟩ :=
    finite_scalar_boundary_localization (𝕜 := 𝕜) Ω (fun j => (Φ j).source)
      (fun j => (Φ j).open_source) hcover hcompact
  have hpiece (k : Option (Fin n)) :
      ∃ (T : (Domain d → 𝕜) →ₗ[𝕜] (Domain d → 𝕜))
        (E : ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)],
          SpaceValue 𝕜 d Ω 1 p →L[𝕜] SpaceValue 𝕜 d ⊤ 1 p),
        (∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : SpaceValue 𝕜 d Ω 1 p),
          (E p u).val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))]
            fun x => a k x * u.val (zeroIndex d 1) x) ∧
        (∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : SpaceValue 𝕜 d Ω 1 p) (f : Domain d → 𝕜),
          f =ᵐ[volume.restrict (Ω : Set (Domain d))] u.val (zeroIndex d 1) →
          (E p u).val (zeroIndex d 1) =ᵐ[volume] T f) := by
    cases k with
    | none =>
      exact interior_compatible_piece (a none) (ha none) C hC0 (hC none) (hD none)
        S hSc hSΩ ((inter_subset_inter_left _ subset_closure).trans hS)
    | some j =>
      let θ : Tests 𝕜 (⊤ : Opens (Domain d)) :=
        ⟨a (some j), ha (some j), (hsupp j).1, by simp⟩
      obtain ⟨hΦ, hInv, hbsource, hbtarget, hside, hder, hderInv⟩ := hcharts j
      exact boundary_chart_piece Ω (i j) (Φ j) hΦ hInv B hB0 hder hderInv
        hbsource hbtarget hside θ (hsupp j).2
  choose T E hlocal hcompatible using hpiece
  exact finite_simultaneous_extension_assembly Ω a
    (fun x _ => by simpa only [Fintype.sum_option] using hsum x)
    T E hlocal hcompatible

theorem smooth_density : Specs.ExpandedFA.Sobolev.C1DomainExtension.SmoothDensity :=
  smooth_density_of_extension_exists extension_exists

end ExpandedFA.Sobolev.C1Extension
