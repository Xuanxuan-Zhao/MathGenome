import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.VolterraSmoothness
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.VolterraResolventKernel
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Closed-interval Leibniz differentiation, finite-order solution regularity, and
joint smoothness of the actual scalar resolvent series. For the kernel result,
affine rescaling to a fixed unit interval identifies the reduced kernel with
a smooth family of inverse operators in the supremum norm. -/

set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace ExpandedFA.PartV


section
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
local instance volterraDifferentiationProofRealSpace : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
local instance volterraDifferentiationProofRealOperatorSpace : NormedSpace ℝ (E →L[𝕜] E) :=
  NormedSpace.restrictScalars ℝ 𝕜 (E →L[𝕜] E)

variable {a b : ℝ} (hab : a ≤ b)
  (k dk : C(volterraTriangle a b, E →L[𝕜] E))
  (u : C(VolterraInterval a b, E))

@[simp] theorem volterraIntervalExtension_coe (t : VolterraInterval a b) :
    volterraIntervalExtension hab u t = u t := by
  simp [volterraIntervalExtension, Set.projIcc_of_mem hab t.property]

theorem continuous_volterraIntervalExtension :
    Continuous (volterraIntervalExtension hab u) :=
  u.continuous.comp continuous_projIcc

theorem continuous_volterraKernelSection (s : VolterraInterval a b) :
    Continuous (volterraKernelSection k s) := by
  apply k.continuous.comp
  apply Continuous.subtype_mk
  exact (continuous_const.max (continuous_const.min continuous_id)).prodMk continuous_const

theorem volterraKernelSection_eq (s : VolterraInterval a b) {t : ℝ}
    (ht : t ∈ Icc (s : ℝ) b) :
    volterraKernelSection k s t = k ⟨(t, s), s.property.1, ht.1, ht.2⟩ := by
  unfold volterraKernelSection
  congr 1
  apply Subtype.ext
  simp [min_eq_right ht.2, max_eq_right ht.1]

/-- A continuous extension of the derivative integrand to the real plane.
Only its values on the original triangle enter any integral below. -/
def volterraPlaneIntegrand (r s : ℝ) : E :=
  volterraIntegrand hab dk u (Set.projIcc a b hab r) s

theorem continuous_volterraPlaneIntegrand :
    Continuous (Function.uncurry (volterraPlaneIntegrand hab dk u)) := by
  exact (continuous_volterraIntegrand hab dk u).comp
    (((continuous_projIcc : Continuous (Set.projIcc a b hab)).comp continuous_fst).prodMk continuous_snd)

theorem volterraPlaneIntegrand_eq (r : VolterraInterval a b) {s : ℝ}
    (hs : s ∈ Icc a (r : ℝ)) :
    volterraPlaneIntegrand hab dk u r s =
      dk ⟨((r : ℝ), s), hs.1, hs.2, r.property.2⟩
        (u ⟨s, hs.1, hs.2.trans r.property.2⟩) := by
  unfold volterraPlaneIntegrand
  rw [Set.projIcc_of_mem hab r.property]
  exact volterraIntegrand_eq hab dk u r s hs

variable [CompleteSpace E]

/-- The fundamental theorem on a single admissible kernel section, evaluated
on a fixed vector. No derivative in the second variable is used. -/
theorem volterra_section_integral
    (hk : VolterraKernelHasDerivative k dk)
    (s t : VolterraInterval a b) (hst : (s : ℝ) ≤ t) :
    (∫ r in (s : ℝ)..(t : ℝ), volterraPlaneIntegrand hab dk u r s) =
      k ⟨((t : ℝ), s), s.property.1, hst, t.property.2⟩ (u s) -
      k ⟨((s : ℝ), s), s.property.1, le_rfl, s.property.2⟩ (u s) := by
  let ev : (E →L[𝕜] E) →L[ℝ] E :=
    { toFun := fun A => A (u s)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      cont := (ContinuousLinearMap.apply 𝕜 E (u s)).continuous }
  have hc : Continuous (fun r => volterraKernelSection k s r (u s)) :=
    ev.continuous.comp (continuous_volterraKernelSection k s)
  have hd : ∀ r ∈ Ioo (s : ℝ) (t : ℝ),
      HasDerivAt (fun r => volterraKernelSection k s r (u s))
        (volterraKernelSection dk s r (u s)) r := by
    intro r hr
    have hri : r ∈ Icc (s : ℝ) b := ⟨hr.1.le, hr.2.le.trans t.property.2⟩
    have h := (hk s r hri).hasDerivAt
      (Icc_mem_nhds hr.1 (hr.2.trans_le t.property.2))
    have he := ev.hasFDerivAt.comp_hasDerivAt r h
    rw [volterraKernelSection_eq dk s hri]
    exact he
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst hc.continuousOn hd
    ((ev.continuous.comp (continuous_volterraKernelSection dk s)).intervalIntegrable _ _)
  have hi : (∫ r in (s : ℝ)..(t : ℝ), volterraPlaneIntegrand hab dk u r s) =
      ∫ r in (s : ℝ)..(t : ℝ), volterraKernelSection dk s r (u s) := by
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le hst] at hr
    have hri : r ∈ Icc (s : ℝ) b := ⟨hr.1, hr.2.trans t.property.2⟩
    dsimp only
    rw [volterraKernelSection_eq dk s hri]
    exact volterraPlaneIntegrand_eq hab dk u ⟨r, s.property.1.trans hr.1,
      hr.2.trans t.property.2⟩ ⟨s.property.1, hr.1⟩
  rw [hi, hFTC, volterraKernelSection_eq k s ⟨hst, t.property.2⟩,
    volterraKernelSection_eq k s ⟨le_rfl, s.property.2⟩]

omit [CompleteSpace E] in
/-- The Leibniz expression is continuous on the original interval. -/
theorem continuous_volterraDerivativeValue :
    Continuous (volterraDerivativeValue hab k dk u) := by
  have hdiag : Continuous (fun t : VolterraInterval a b =>
      (⟨((t : ℝ), t), t.property.1, le_rfl, t.property.2⟩ : volterraTriangle a b)) := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.prodMk continuous_subtype_val
  exact ((k.continuous.comp hdiag).clm_apply u.continuous).add
    (continuous_volterraIntegral hab dk u)

/-- The triangular integral is the primitive of the continuous Leibniz
expression. This identity uses only section FTC and Banach-valued Fubini. -/
theorem volterra_integral_primitive (hk : VolterraKernelHasDerivative k dk)
    (t : VolterraInterval a b) :
    volterraIntegralValue hab k u t =
      ∫ r in a..(t : ℝ), volterraDerivativeValue hab k dk u (Set.projIcc a b hab r) := by
  let F := volterraPlaneIntegrand hab dk u
  let d : ℝ → E := fun r =>
    k ⟨((Set.projIcc a b hab r : ℝ), Set.projIcc a b hab r),
      (Set.projIcc a b hab r).property.1, le_rfl,
      (Set.projIcc a b hab r).property.2⟩ (u (Set.projIcc a b hab r))
  have hd : Continuous d := by
    apply Continuous.clm_apply _ (u.continuous.comp continuous_projIcc)
    apply k.continuous.comp
    apply Continuous.subtype_mk
    exact ((continuous_subtype_val.comp continuous_projIcc).prodMk
      (continuous_subtype_val.comp continuous_projIcc))
  have hFi : Continuous (fun s => ∫ r in s..(t : ℝ), F r s) := by
    have hc : Continuous (fun p : ℝ × ℝ => F p.2 p.1) :=
      (continuous_volterraPlaneIntegrand hab dk u).comp continuous_swap
    have hi := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (a₀ := (t : ℝ)) (μ := volume) (f := fun s r => F r s) hc continuous_id
    convert hi.neg using 1
    funext s
    exact intervalIntegral.integral_symm _ _
  have hsplit : volterraIntegralValue hab k u t =
      ∫ s in a..(t : ℝ), d s + ∫ r in s..(t : ℝ), F r s := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le t.property.1] at hs
    let si : VolterraInterval a b := ⟨s, hs.1, hs.2.trans t.property.2⟩
    have hsection := volterra_section_integral hab k dk u hk si t hs.2
    dsimp only [F] at *
    rw [hsection, volterraIntegrand_eq hab k u t s hs]
    dsimp only [d]
    rw [Set.projIcc_of_mem hab si.property]
    abel
  rw [hsplit, intervalIntegral.integral_add (hd.intervalIntegrable _ _)
    (hFi.intervalIntegrable _ _), (integral_triangle_swap a (t : ℝ) t.property.1 F
      (continuous_volterraPlaneIntegrand hab dk u)).symm]
  have hinner (r : ℝ) (hr : r ∈ Icc a (t : ℝ)) :
      (∫ s in a..r, F r s) =
        volterraIntegralValue hab dk u (Set.projIcc a b hab r) := by
    have hri : r ∈ Icc a b := ⟨hr.1, hr.2.trans t.property.2⟩
    change (∫ s in a..r, volterraIntegrand hab dk u (Set.projIcc a b hab r) s) = _
    unfold volterraIntegralValue
    rw [Set.projIcc_of_mem hab hri]
  have heq : (∫ r in a..(t : ℝ), ∫ s in a..r, F r s) =
      ∫ r in a..(t : ℝ), volterraIntegralValue hab dk u (Set.projIcc a b hab r) := by
    apply intervalIntegral.integral_congr
    intro r hr
    exact hinner r (by simpa [uIcc_of_le t.property.1] using hr)
  rw [heq]
  exact (intervalIntegral.integral_add (hd.intervalIntegrable _ _)
    (((continuous_volterraIntegral hab dk u).comp
      (continuous_projIcc : Continuous (Set.projIcc a b hab))).intervalIntegrable a (t : ℝ))).symm

omit [CompleteSpace E] in
/-- A continuous displayed within derivative gives native `C¹` regularity. -/
theorem volterra_contDiffOn_of_interval_derivative_pos (hlt : a < b)
    (f f' : C(VolterraInterval a b, E))
    (hf : VolterraHasIntervalDerivative (𝕜 := 𝕜) hab f f') :
    ContDiffOn ℝ 1 (volterraIntervalExtension hab f) (Icc a b) := by
  have hs := uniqueDiffOn_Icc hlt
  apply (contDiffOn_one_iff_derivWithin hs).mpr
  refine ⟨fun t ht => (hf ⟨t, ht⟩).differentiableWithinAt, ?_⟩
  apply (continuous_volterraIntervalExtension hab f').continuousOn.congr
  intro t ht
  exact ((hf ⟨t, ht⟩).derivWithin (hs t ht)).trans
    (volterraIntervalExtension_coe hab f' ⟨t, ht⟩).symm

omit [CompleteSpace E] in
/-- Continuous within derivatives also imply C¹ on a singleton interval. -/
theorem volterra_contDiffOn_of_interval_derivative
    (f f' : C(VolterraInterval a b, E))
    (hf : VolterraHasIntervalDerivative (𝕜 := 𝕜) hab f f') :
    ContDiffOn ℝ 1 (volterraIntervalExtension hab f) (Icc a b) := by
  by_cases hlt : a < b
  · exact volterra_contDiffOn_of_interval_derivative_pos hab hlt f f' hf
  · have heq : a = b := le_antisymm hab (le_of_not_gt hlt)
    subst b
    apply (contDiffOn_const (c := f ⟨a, le_rfl, le_rfl⟩)).congr
    intro x hx
    have hx' : x = a := le_antisymm hx.2 hx.1
    subst x
    exact volterraIntervalExtension_coe hab f ⟨a, le_rfl, le_rfl⟩

omit [CompleteSpace E] in
/-- Conversely native `C¹` on the closed interval supplies a continuous
within derivative; thus the displayed-data hypothesis loses no `C¹` data. -/
theorem volterra_c1_iff_exists_derivative (hlt : a < b)
    (f : C(VolterraInterval a b, E)) :
    ContDiffOn ℝ 1 (volterraIntervalExtension hab f) (Icc a b) ↔
      ∃ f' : C(VolterraInterval a b, E),
        VolterraHasIntervalDerivative (𝕜 := 𝕜) hab f f' := by
  constructor
  · intro hf
    obtain ⟨hd, hc⟩ := (contDiffOn_one_iff_derivWithin (uniqueDiffOn_Icc hlt)).mp hf
    let f' : C(VolterraInterval a b, E) :=
      ⟨fun t => derivWithin (volterraIntervalExtension hab f) (Icc a b) t,
        continuousOn_iff_continuous_domRestrict.mp hc⟩
    exact ⟨f', fun t => (hd t t.property).hasDerivWithinAt⟩
  · rintro ⟨f', hf⟩
    exact volterra_contDiffOn_of_interval_derivative hab f f' hf

/-- The within Leibniz rule, including both endpoints. -/
theorem volterra_hasDerivWithinAt (hk : VolterraKernelHasDerivative k dk)
    (t : VolterraInterval a b) :
    HasDerivWithinAt
      (volterraIntervalExtension hab (VolterraOperatorSpec.OperatorValue 𝕜 E a b hab k u))
      (volterraDerivativeValue hab k dk u t) (Icc a b) t := by
  have hc : Continuous (fun r => volterraDerivativeValue hab k dk u (Set.projIcc a b hab r)) :=
    (continuous_volterraDerivativeValue hab k dk u).comp continuous_projIcc
  have hprim := intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable a (t : ℝ))
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  rw [Set.projIcc_of_mem hab t.property] at hprim
  apply hprim.hasDerivWithinAt.congr_of_mem _ t.property
  intro r hr
  change VolterraOperatorSpec.OperatorValue 𝕜 E a b hab k u (Set.projIcc a b hab r) = _
  rw [(volterra_operator_properties 𝕜 E a b hab k).1]
  rw [volterra_integral_primitive hab k dk u hk]
  rw [Set.projIcc_of_mem hab hr]

end

/-- Full Leibniz rule and `C¹` regularity for every continuous argument. -/
theorem volterra_leibniz_rule : VolterraSmoothnessSpec.LeibnizRule := by
  intro 𝕜 E _ _ _ _ a b hab k dk hk u
  let := NormedSpace.restrictScalars ℝ 𝕜 E
  let V := VolterraOperatorSpec.OperatorValue 𝕜 E a b hab k
  let D : C(VolterraInterval a b, E) :=
    ⟨volterraDerivativeValue hab k dk u, continuous_volterraDerivativeValue hab k dk u⟩
  have hd : VolterraHasIntervalDerivative (𝕜 := 𝕜) hab (V u) D :=
    volterra_hasDerivWithinAt hab k dk u hk
  refine ⟨D.continuous, volterra_contDiffOn_of_interval_derivative hab (V u) D hd, hd, ?_⟩
  intro t ht
  exact (hd ⟨t, ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

/-- The derivative-witness formulation covers precisely the original `C¹`
data on the closed interval. -/
theorem volterra_c1_identification : VolterraSmoothnessSpec.C1Identification := by
  intro 𝕜 E _ _ _ a b hab f
  exact volterra_c1_iff_exists_derivative hab.le hab f

/-- The unique solution inherits a continuous derivative from the datum and
the first-variable derivative of the kernel, for every scalar parameter. -/
theorem volterra_solution_regularity : VolterraSmoothnessSpec.SolutionRegularity := by
  intro 𝕜 E _ _ _ _ a b hab k dk hk lam f f' hf
  let := NormedSpace.restrictScalars ℝ 𝕜 E
  let : SMulCommClass ℝ 𝕜 E :=
    ⟨fun r c x => by
      change (algebraMap ℝ 𝕜 r) • (c • x) = c • ((algebraMap ℝ 𝕜 r) • x)
      simp only [smul_smul, mul_comm]⟩
  let V := VolterraOperatorSpec.OperatorValue 𝕜 E a b hab k
  obtain ⟨u, hu, huniq, _, _, _⟩ :=
    volterra_solvability_and_iteration 𝕜 E a b hab k lam f
  obtain ⟨hD, _, hwithin, _⟩ := volterra_leibniz_rule 𝕜 E a b hab k dk hk u
  let D : C(VolterraInterval a b, E) := ⟨volterraDerivativeValue hab k dk u, hD⟩
  let u' : C(VolterraInterval a b, E) := f' + lam • D
  have heq : ∀ r : ℝ, volterraIntervalExtension hab u r =
      volterraIntervalExtension hab f r +
        lam • volterraIntervalExtension hab (V u) r := by
    intro r
    have h := congrArg (fun v : C(VolterraInterval a b, E) => v (Set.projIcc a b hab r)) hu
    change u (Set.projIcc a b hab r) -
      lam • V u (Set.projIcc a b hab r) = f (Set.projIcc a b hab r) at h
    exact sub_eq_iff_eq_add.mp h
  have hd : VolterraHasIntervalDerivative (𝕜 := 𝕜) hab u u' := by
    intro t
    change HasDerivWithinAt (volterraIntervalExtension hab u)
      (f' t + lam • volterraDerivativeValue hab k dk u t) (Icc a b) t
    apply ((hf t).add ((hwithin t).const_smul lam)).congr
    · exact fun r _ => heq r
    · exact heq t
  refine ⟨u, hu, huniq,
    volterra_contDiffOn_of_interval_derivative hab u u' hd, u', hd, ?_, ?_⟩
  · intro t
    change f' t + lam • volterraDerivativeValue hab k dk u t = _
    simp only [volterraDerivativeValue, smul_add, add_assoc]
  · intro t ht
    exact (hd ⟨t, ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

section AmbientKernel
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
local instance volterraAmbientRealSpace : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
local instance volterraAmbientRealOperatorSpace : NormedSpace ℝ (E →L[𝕜] E) :=
  NormedSpace.restrictScalars ℝ 𝕜 (E →L[𝕜] E)
variable {a b : ℝ} {U : Set (ℝ × ℝ)}

/-- A genuine ambient smooth kernel supplies the section derivatives used in
Leibniz' rule. In particular these are derived, rather than assumed certificates. -/
theorem ambient_volterraKernel_hasDerivative (hU : IsOpen U)
    (hsub : volterraTriangle a b ⊆ U)
    (K : ℝ × ℝ → E →L[𝕜] E) (hK : ContDiffOn ℝ 1 K U)
    (hK₀ : ContinuousOn K (volterraTriangle a b))
    (hK₁ : ContinuousOn (volterraPartialFirst K) (volterraTriangle a b)) :
    VolterraKernelHasDerivative (ambientVolterraKernel K hK₀)
      (ambientVolterraKernel (volterraPartialFirst K) hK₁) := by
  intro s t ht
  have hp : (t, (s : ℝ)) ∈ volterraTriangle a b := ⟨s.property.1, ht⟩
  have hD := (hK.contDiffAt (hU.mem_nhds (hsub hp))).differentiableAt_one.hasFDerivAt
  have hline : HasDerivAt (fun r : ℝ => (r, (s : ℝ))) (1, 0) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t (s : ℝ))
  have h := hD.comp_hasDerivAt t hline
  apply h.hasDerivWithinAt.congr_of_mem _ ht
  intro r hr
  rw [volterraKernelSection_eq _ s hr]
  rfl

/-- Real first partial derivatives lower the smoothness order by one. -/
theorem contDiffOn_volterraPartialFirst (hU : IsOpen U) (n : ℕ)
    (K : ℝ × ℝ → E →L[𝕜] E) (hK : ContDiffOn ℝ (n + 1) K U) :
    ContDiffOn ℝ n (volterraPartialFirst K) U := by
  exact (hK.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const

/-- The closed-interval derivative criterion in all finite orders, including
singleton intervals. No uniqueness of derivatives is asserted on a singleton. -/
theorem volterra_contDiffOn_succ_of_interval_derivative (hab : a ≤ b) (n : ℕ)
    (f f' : C(VolterraInterval a b, E))
    (hf : VolterraHasIntervalDerivative (𝕜 := 𝕜) hab f f')
    (hf' : ContDiffOn ℝ n (volterraIntervalExtension hab f') (Icc a b)) :
    ContDiffOn ℝ (n + 1) (volterraIntervalExtension hab f) (Icc a b) := by
  by_cases hlt : a < b
  · have hs := uniqueDiffOn_Icc hlt
    apply (contDiffOn_succ_iff_derivWithin hs).mpr
    refine ⟨fun t ht => (hf ⟨t, ht⟩).differentiableWithinAt, by simp, ?_⟩
    apply hf'.congr
    intro t ht
    exact ((hf ⟨t, ht⟩).derivWithin (hs t ht)).trans
      (volterraIntervalExtension_coe hab f' ⟨t, ht⟩).symm
  · have heq : a = b := le_antisymm hab (le_of_not_gt hlt)
    subst b
    apply (contDiffOn_const (c := f ⟨a, le_rfl, le_rfl⟩)).congr
    intro x hx
    have hx' : x = a := le_antisymm hx.2 hx.1
    subst x
    exact volterraIntervalExtension_coe hab f ⟨a, le_rfl, le_rfl⟩

variable [CompleteSpace E]
local instance : SMulCommClass ℝ 𝕜 E where
  smul_comm r c x := by
    change (algebraMap ℝ 𝕜 r) • (c • x) = c • ((algebraMap ℝ 𝕜 r) • x)
    simp only [smul_smul, mul_comm]

local instance : IsScalarTower ℝ 𝕜 E where
  smul_assoc r c x := by
    change (r • c) • x = (algebraMap ℝ 𝕜 r) • (c • x)
    rw [Algebra.smul_def, mul_smul]

/-- A smooth kernel gains one derivative over the regularity of its argument.
The proof iterates the actual Leibniz rule, without differentiating an
unjustified formal series. -/
theorem volterra_integral_smoothing (n : ℕ) :
    ∀ (hab : a ≤ b) (_hU : IsOpen U) (_hsub : volterraTriangle a b ⊆ U)
    (K : ℝ × ℝ → E →L[𝕜] E) (_hK : ContDiffOn ℝ (n + 1) K U)
    (hK₀ : ContinuousOn K (volterraTriangle a b))
    (u : C(VolterraInterval a b, E)),
    ContDiffOn ℝ n (volterraIntervalExtension hab u) (Icc a b) →
    ContDiffOn ℝ (n + 1)
      (volterraIntervalExtension hab
        (VolterraOperatorSpec.OperatorValue 𝕜 E a b hab (ambientVolterraKernel K hK₀) u))
      (Icc a b) := by
  induction n with
  | zero =>
    intro hab hU hsub K hK hK₀ u _hu
    have hK₁ := (contDiffOn_volterraPartialFirst hU 0 K hK).continuousOn.mono hsub
    exact (volterra_leibniz_rule 𝕜 E a b hab _ _
      (ambient_volterraKernel_hasDerivative hU hsub K hK hK₀ hK₁) u).2.1
  | succ n ih =>
    intro hab hU hsub K hK hK₀ u hu
    let k := ambientVolterraKernel K hK₀
    have hdK : ContDiffOn ℝ (n + 1) (volterraPartialFirst K) U :=
      contDiffOn_volterraPartialFirst hU (n + 1) K hK
    have hdK₀ := hdK.continuousOn.mono hsub
    let dk := ambientVolterraKernel (volterraPartialFirst K) hdK₀
    have hk : VolterraKernelHasDerivative k dk :=
      ambient_volterraKernel_hasDerivative hU hsub K (hK.of_le (by simp)) hK₀ hdK₀
    let V := VolterraOperatorSpec.OperatorValue 𝕜 E a b hab k
    let D : C(VolterraInterval a b, E) :=
      ⟨volterraDerivativeValue hab k dk u, continuous_volterraDerivativeValue hab k dk u⟩
    have hD : VolterraHasIntervalDerivative (𝕜 := 𝕜) hab (V u) D :=
      volterra_hasDerivWithinAt hab k dk u hk
    have hdiag : ContDiffOn ℝ (n + 1) (fun t : ℝ => K (t, t)) (Icc a b) :=
      (hK.of_le (by simp)).comp (contDiffOn_id.prodMk contDiffOn_id)
        (fun t ht => hsub ⟨ht.1, le_rfl, ht.2⟩)
    have heval : ContDiffOn ℝ (n + 1)
        (fun t => K (t, t) (volterraIntervalExtension hab u t)) (Icc a b) :=
      ((ContinuousLinearMap.restrictScalarsL 𝕜 E E ℝ ℝ).contDiff.comp_contDiffOn hdiag).clm_apply hu
    have hi := ih hab hU hsub (volterraPartialFirst K) hdK hdK₀ u (hu.of_le (by simp))
    have hDC : ContDiffOn ℝ (n + 1) (volterraIntervalExtension hab D) (Icc a b) := by
      apply (heval.add hi).congr
      intro t ht
      rw [show volterraIntervalExtension hab D t = D ⟨t, ht⟩ from
        volterraIntervalExtension_coe hab D ⟨t, ht⟩]
      change K (t, t) (u ⟨t, ht⟩) + volterraIntegralValue hab dk u ⟨t, ht⟩ = _
      rw [volterraIntervalExtension_coe hab u ⟨t, ht⟩,
        volterraIntervalExtension_coe hab _ ⟨t, ht⟩,
        (volterra_operator_properties 𝕜 E a b hab dk).1]
    exact volterra_contDiffOn_succ_of_interval_derivative hab (n + 1) (V u) D hD hDC

/-- Every finite order of the datum and ambient kernel is inherited by any
solution of the original continuous Volterra equation. -/
theorem ambient_volterra_solution_contDiff (m : ℕ) :
    ∀ (hab : a ≤ b) (_hU : IsOpen U) (_hsub : volterraTriangle a b ⊆ U)
    (K : ℝ × ℝ → E →L[𝕜] E) (_hK : ContDiffOn ℝ m K U)
    (hK₀ : ContinuousOn K (volterraTriangle a b)) (lam : 𝕜)
    (f u : C(VolterraInterval a b, E)),
    ContDiffOn ℝ m (volterraIntervalExtension hab f) (Icc a b) →
    u - lam • VolterraOperatorSpec.OperatorValue 𝕜 E a b hab (ambientVolterraKernel K hK₀) u = f →
    ContDiffOn ℝ m (volterraIntervalExtension hab u) (Icc a b) := by
  induction m with
  | zero =>
    intro hab _hU _hsub _K _hK _hK₀ _lam _f u _hf _hu
    exact contDiffOn_zero.mpr (continuous_volterraIntervalExtension hab u).continuousOn
  | succ n ih =>
    intro hab hU hsub K hK hK₀ lam f u hf hu
    have hun := ih hab hU hsub K (hK.of_le (by simp)) hK₀ lam f u
      (hf.of_le (by simp)) hu
    have hV := volterra_integral_smoothing n hab hU hsub K hK hK₀ u hun
    apply (hf.add (hV.const_smul lam)).congr
    intro t ht
    have heq := congrArg (fun v : C(VolterraInterval a b, E) => v (Set.projIcc a b hab t)) hu
    exact sub_eq_iff_eq_add.mp heq

end AmbientKernel


/-- The finite-order source assertion for real and complex scalar kernels. -/
theorem volterra_scalar_solution_regularity : VolterraSmoothnessSpec.ScalarSolutionRegularity := by
  intro 𝕜 _ a b hab m U hU hsub k hk lam f hf
  let K : ℝ × ℝ → 𝕜 →L[𝕜] 𝕜 := fun p => ContinuousLinearMap.lsmul 𝕜 𝕜 (k p)
  have hK : ContDiffOn ℝ m K U :=
    ((ContinuousLinearMap.lsmul 𝕜 𝕜 : 𝕜 →L[𝕜] 𝕜 →L[𝕜] 𝕜).restrictScalars ℝ).contDiff.comp_contDiffOn hk
  have hK₀ := hK.continuousOn.mono hsub
  obtain ⟨u, hu, huniq, _, _, _⟩ := volterra_solvability_and_iteration 𝕜 𝕜 a b hab
    (VolterraSmoothnessSpec.scalarVolterraKernel k (hk.continuousOn.mono hsub)) lam f
  refine ⟨u, hu, huniq, ?_⟩
  have H := ambient_volterra_solution_contDiff (𝕜 := 𝕜) (E := 𝕜)
    (a := a) (b := b) (U := U) m
  simp only [volterraAmbientRealSpace, volterraAmbientRealOperatorSpace,
    NormedSpace.restrictScalars_eq] at H
  exact H hab hU hsub K hK hK₀ lam f u hf hu

/-- Multiplication realizes the source scalar partial derivative in the
operator-norm derivative used by the Banach-valued Leibniz rule. -/
theorem scalar_volterraPartialFirst {𝕜 : Type*} [RCLike 𝕜]
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) (k : ℝ × ℝ → 𝕜)
    (hk : ContDiffOn ℝ 1 k U) {p : ℝ × ℝ} (hp : p ∈ U) :
    volterraPartialFirst (fun q => (ContinuousLinearMap.lsmul 𝕜 𝕜 (k q) : 𝕜 →L[𝕜] 𝕜)) p =
      (ContinuousLinearMap.lsmul 𝕜 𝕜 (scalarVolterraPartialFirst k p) : 𝕜 →L[𝕜] 𝕜) := by
  unfold volterraPartialFirst
  rw [volterraDifferentiationSpecRealOperatorSpace, NormedSpace.restrictScalars_eq]
  let L : 𝕜 →L[ℝ] 𝕜 →L[𝕜] 𝕜 :=
    (ContinuousLinearMap.lsmul 𝕜 𝕜 : 𝕜 →L[𝕜] 𝕜 →L[𝕜] 𝕜).restrictScalars ℝ
  have h := L.hasFDerivAt.comp p
    (hk.contDiffAt (hU.mem_nhds hp)).differentiableAt_one.hasFDerivAt
  change fderiv ℝ (fun q => L (k q)) p (1, 0) = L (fderiv ℝ k p (1, 0))
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply] using
    congrArg (fun A : (ℝ × ℝ) →L[ℝ] 𝕜 →L[𝕜] 𝕜 => A (1, 0)) h.fderiv

/-- The displayed formula is for the actual native scalar partial derivative
and the original integral, including both interval endpoints. -/
theorem volterra_scalar_c1_formula : VolterraSmoothnessSpec.ScalarC1Formula := by
  intro 𝕜 _ a b hab U hU hsub k hk lam f u hf hu t
  let K : ℝ × ℝ → 𝕜 →L[𝕜] 𝕜 := fun p => ContinuousLinearMap.lsmul 𝕜 𝕜 (k p)
  have hK : ContDiffOn ℝ 1 K U :=
    ((ContinuousLinearMap.lsmul 𝕜 𝕜 : 𝕜 →L[𝕜] 𝕜 →L[𝕜] 𝕜).restrictScalars ℝ).contDiff.comp_contDiffOn hk
  have hK₀ := hK.continuousOn.mono hsub
  have HP := contDiffOn_volterraPartialFirst (𝕜 := 𝕜) (E := 𝕜) (U := U) hU 0 K
  simp only [volterraAmbientRealSpace, volterraAmbientRealOperatorSpace,
    NormedSpace.restrictScalars_eq] at HP
  have hdK₀ := (HP hK).continuousOn.mono hsub
  let kop := ambientVolterraKernel K hK₀
  let dk := ambientVolterraKernel (volterraPartialFirst K) hdK₀
  have hkop : VolterraKernelHasDerivative kop dk :=
    by
      have H := ambient_volterraKernel_hasDerivative (𝕜 := 𝕜) (E := 𝕜)
        (a := a) (b := b) (U := U) hU hsub K
      simp only [volterraAmbientRealSpace, volterraAmbientRealOperatorSpace,
        NormedSpace.restrictScalars_eq] at H
      exact H hK hK₀ hdK₀
  let V := VolterraOperatorSpec.OperatorValue 𝕜 𝕜 a b hab kop
  have hv := volterra_hasDerivWithinAt hab kop dk u hkop t
  rw [volterraDifferentiationProofRealSpace, NormedSpace.restrictScalars_eq] at hv
  have heq (r : ℝ) : volterraIntervalExtension hab u r =
      volterraIntervalExtension hab f r + lam • volterraIntervalExtension hab (V u) r := by
    exact sub_eq_iff_eq_add.mp
      (congrArg (fun v : C(VolterraInterval a b, 𝕜) => v (Set.projIcc a b hab r)) hu)
  have hd := ((hf.differentiableOn_one t t.property).hasDerivWithinAt.add
    (hv.const_smul lam)).congr (fun r _ => heq r) (heq t)
  have hi : volterraIntegralValue hab dk u t = ∫ s in a..(t : ℝ),
      scalarVolterraPartialFirst k ((t : ℝ), s) * volterraIntervalExtension hab u s := by
    rw [volterraIntegralValue, instNormedSpaceReal_specs, NormedSpace.restrictScalars_eq]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le t.property.1] at hs
    rw [volterraIntegrand_eq hab dk u t s hs]
    change volterraPartialFirst K ((t : ℝ), s)
      (u ⟨s, hs.1, hs.2.trans t.property.2⟩) = _
    rw [scalar_volterraPartialFirst hU k hk (hsub ⟨hs.1, hs.2, t.property.2⟩)]
    change scalarVolterraPartialFirst k ((t : ℝ), s) * u ⟨s, hs.1, hs.2.trans t.property.2⟩ =
      scalarVolterraPartialFirst k ((t : ℝ), s) * volterraIntervalExtension hab u s
    rw [volterraIntervalExtension_coe hab u ⟨s, hs.1, hs.2.trans t.property.2⟩]
  convert hd using 1
  dsimp [volterraDerivativeValue, kop, ambientVolterraKernel]
  rw [hi]
  simp only [K, ContinuousLinearMap.lsmul_apply, smul_eq_mul,
    mul_add, mul_assoc, add_assoc]

/-- The triangle representative really preserves every original kernel value. -/
@[simp] theorem volterraTriangleClamp_coe {a b : ℝ} (hab : a ≤ b)
    (p : volterraTriangle a b) : volterraTriangleClamp hab p = p := by
  apply Subtype.ext
  have hp : p.val.1 ∈ Icc a b := ⟨p.property.1.trans p.property.2.1, p.property.2.2⟩
  simp [volterraTriangleClamp, volterraRetraction, Set.projIcc_of_mem hab hp,
    min_eq_right p.property.2.1, max_eq_right p.property.1]

theorem continuous_volterraTriangleClamp {a b : ℝ} (hab : a ≤ b) :
    Continuous (volterraTriangleClamp hab) :=
  continuous_volterraRetraction.comp
    (((continuous_projIcc : Continuous (Set.projIcc a b hab)).comp continuous_fst).prodMk continuous_snd)

/-- The joint order-zero case uses the actual accepted kernel sums. -/
theorem volterra_scalar_resolvent_continuous {𝕜 : Type*} [RCLike 𝕜]
    {a b : ℝ} (hab : a ≤ b) (k : C(volterraTriangle a b, 𝕜 →L[𝕜] 𝕜)) (lam : 𝕜) :
    Continuous (scalarReducedResolventExtension hab k lam) ∧
      Continuous (scalarResolventExtension hab k lam) := by
  constructor
  · exact ((volterra_reduced_kernel_uniform_series 𝕜 𝕜 a b hab k lam).1.comp
      (continuous_volterraTriangleClamp hab)).clm_apply continuous_const
  · exact ((volterra_kernel_uniform_series 𝕜 𝕜 a b hab k lam).1.comp
      (continuous_volterraTriangleClamp hab)).clm_apply continuous_const

/-- The entire joint kernel smoothness conclusion holds in the degenerate
interval case. All within derivatives there are nonunique, as they should be. -/
theorem volterra_scalar_resolvent_singleton {𝕜 : Type*} [RCLike 𝕜]
    (a : ℝ) (m : ℕ) (k : C(volterraTriangle a a, 𝕜 →L[𝕜] 𝕜)) (lam : 𝕜) :
    ContDiffOn ℝ m (scalarReducedResolventExtension le_rfl k lam) (volterraTriangle a a) ∧
    ContDiffOn ℝ m (scalarResolventExtension le_rfl k lam) (volterraTriangle a a) := by
  have hsingle : volterraTriangle a a = {(a, a)} := by
    ext p
    constructor
    · intro hp
      have hs : p.2 = a := le_antisymm (hp.2.1.trans hp.2.2) hp.1
      have ht : p.1 = a := le_antisymm hp.2.2 (hp.1.trans hp.2.1)
      exact Prod.ext ht hs
    · intro hp
      have hp' : p = (a, a) := hp
      subst p
      exact ⟨le_rfl, le_rfl, le_rfl⟩
  rw [hsingle]
  constructor <;> intro p hp <;> have hp' : p = (a, a) := hp <;> subst p <;>
    exact contDiffWithinAt_singleton

end ExpandedFA.PartV

namespace ExpandedFA.PartV.CompactParameter
universe u v
variable {P K : Type u} {F : Type (max u v)} [NormedAddCommGroup P] [NormedSpace ℝ P]
 [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K] [CompactSpace K]

def pointwiseLinear (d : C(K,P →L[ℝ] F)) : P →L[ℝ] C(K,F) :=
  LinearMap.mkContinuous
  ({ toFun := fun p => ⟨fun k => d k p, d.continuous.clm_apply continuous_const⟩,
     map_add' := fun p q => by ext k; exact (d k).map_add p q
     map_smul' := fun c p => by ext k; exact (d k).map_smul c p } : P →ₗ[ℝ] C(K,F))
  ‖d‖ (fun p => by
    apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg d) (norm_nonneg p))).2
    intro k
    exact (d k).le_opNorm p |>.trans (mul_le_mul_of_nonneg_right (d.norm_coe_le_norm k) (norm_nonneg p)))

@[simp] theorem pointwiseLinear_apply (d : C(K,P →L[ℝ] F)) (p : P) (k : K) :
    pointwiseLinear d p k = d k p := rfl

 theorem pointwiseLinear_norm_le (d : C(K,P →L[ℝ] F)) : ‖pointwiseLinear d‖ ≤ ‖d‖ := by
  apply ContinuousLinearMap.opNorm_le_bound (pointwiseLinear d) (norm_nonneg d)
  intro p
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
  intro k
  exact (d k).le_opNorm p |>.trans (mul_le_mul_of_nonneg_right (d.norm_coe_le_norm k) (norm_nonneg p))

def pointwiseLinearL : C(K,P →L[ℝ] F) →L[ℝ] P →L[ℝ] C(K,F) := by
  let L : C(K,P →L[ℝ] F) →ₗ[ℝ] P →L[ℝ] C(K,F) :=
    { toFun := pointwiseLinear
      map_add' := fun d e => by
        apply ContinuousLinearMap.ext
        intro p
        apply ContinuousMap.ext
        intro k
        rfl
      map_smul' := fun c d => by
        apply ContinuousLinearMap.ext
        intro p
        apply ContinuousMap.ext
        intro k
        rfl }
  refine LinearMap.mkContinuous (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := C(K,P →L[ℝ] F)) (F := P →L[ℝ] C(K,F)) L 1 (fun d => ?_)
  change ‖pointwiseLinear d‖ ≤ 1 * ‖d‖
  simpa using pointwiseLinear_norm_le (P := P) (K := K) (F := F) d

/-- A continuously varying pointwise derivative is a derivative for the uniform norm. -/
theorem hasFDerivAt_of_pointwise
    {f : P → C(K,F)} {D : P → P →L[ℝ] C(K,F)} {U : Set P} {x : P}
    (hU : U ∈ 𝓝 x) (hD : ContinuousAt D x)
    (hd : ∀ y ∈ U, ∀ k : K,
      HasFDerivAt (fun z => f z k) ((ContinuousMap.evalCLM ℝ k).comp (D y)) y) :
    HasFDerivAt f (D x) x := by
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨δ, hδ, hδD⟩ := Metric.continuousAt_iff.mp hD ε hε
  let ρ := min r δ
  have hρ : 0 < ρ := lt_min hr hδ
  filter_upwards [Metric.ball_mem_nhds x hρ] with y hy
  apply (ContinuousMap.norm_le _ (mul_nonneg hε.le (norm_nonneg _))).2
  intro k
  have hder : ∀ z ∈ Metric.ball x ρ,
      HasFDerivWithinAt (fun z => f z k)
        ((ContinuousMap.evalCLM ℝ k).comp (D z)) (Metric.ball x ρ) z := by
    intro z hz
    exact (hd z (hrU (Metric.ball_subset_ball (min_le_left _ _) hz)) k).hasFDerivWithinAt
  have hb : ∀ z ∈ Metric.ball x ρ,
      ‖(ContinuousMap.evalCLM ℝ k).comp (D z) -
        (ContinuousMap.evalCLM ℝ k).comp (D x)‖ ≤ ε := by
    intro z hz
    apply ContinuousLinearMap.opNorm_le_bound _ hε.le
    intro v
    have hzd : ‖D z - D x‖ ≤ ε :=
      by simpa [dist_eq_norm] using (hδD (Metric.mem_ball.mp (Metric.ball_subset_ball (min_le_right _ _) hz))).le
    calc
      ‖((ContinuousMap.evalCLM ℝ k).comp (D z) -
          (ContinuousMap.evalCLM ℝ k).comp (D x)) v‖ = ‖((D z - D x) v) k‖ := rfl
      _ ≤ ‖(D z - D x) v‖ := ContinuousMap.norm_coe_le_norm _ _
      _ ≤ ‖D z - D x‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ε * ‖v‖ := mul_le_mul_of_nonneg_right hzd (norm_nonneg _)
  exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le' hder hb
    (convex_ball x ρ) (Metric.mem_ball_self hρ) hy

variable {Q : Type u} [NormedAddCommGroup Q] [NormedSpace ℝ Q]

/-- A smooth ambient family over a compact parameter space is smooth in the sup norm. -/
theorem contDiffOn_of_ambient (m : ℕ) {q : K → Q} (hq : Continuous q)
    {U : Set P} (hU : IsOpen U) {W : Set (P × Q)} (hW : IsOpen W)
    (hsub : ∀ p ∈ U, ∀ k, (p,q k) ∈ W)
    {g : P × Q → F} (hg : ContDiffOn ℝ m g W)
    {f : P → C(K,F)} (heq : ∀ p ∈ U, ∀ k, f p k = g (p,q k)) :
    ContDiffOn ℝ m f U := by
  induction m generalizing F with
  | zero =>
    apply contDiffOn_zero.mpr
    apply ContinuousMap.continuousOn_of_continuousOn_uncurry
    have hc : ContinuousOn (fun z : P × K => g (z.1,q z.2)) (U ×ˢ univ) :=
      hg.continuousOn.comp (continuous_fst.prodMk (hq.comp continuous_snd)).continuousOn
        (fun z hz => hsub z.1 hz.1 z.2)
    apply hc.congr
    intro z hz
    exact heq z.1 hz.1 z.2
  | succ m ih =>
    let g' : P × Q → P →L[ℝ] F := fun z => (fderiv ℝ g z).comp (ContinuousLinearMap.inl ℝ P Q)
    have hg' : ContDiffOn ℝ m g' W :=
      (hg.fderiv_of_isOpen hW (by simp)).clm_comp contDiffOn_const
    let d : P → C(K,P →L[ℝ] F) := fun p =>
      ContinuousMap.mkD (fun k => g' (p,q k)) 0
    have hdc : ∀ p ∈ U, Continuous (fun k => g' (p,q k)) := by
      intro p hp
      exact hg'.continuousOn.comp_continuous (continuous_const.prodMk hq)
        (fun k => hsub p hp k)
    have hdeq : ∀ p ∈ U, ∀ k, d p k = g' (p,q k) := by
      intro p hp k
      exact ContinuousMap.mkD_apply_of_continuous (hdc p hp)
    have hd : ContDiffOn ℝ m d U := ih hg' hdeq
    let D : P → P →L[ℝ] C(K,F) := fun p => pointwiseLinearL (P := P) (K := K) (F := F) (d p)
    have hD : ContDiffOn ℝ m D U := by
      exact (pointwiseLinearL (P := P) (K := K) (F := F)).contDiff.comp_contDiffOn hd
    rw [Nat.cast_add, Nat.cast_one]
    apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (𝕜 := ℝ) (n := (m : WithTop ℕ∞)) (hU.uniqueDiffOn (𝕜 := ℝ))).mpr
    refine ⟨by simp, D, hD, ?_⟩
    intro x hx
    apply HasFDerivAt.hasFDerivWithinAt
    apply hasFDerivAt_of_pointwise (hU.mem_nhds hx)
      (hD.continuousOn.continuousAt (hU.mem_nhds hx))
    intro y hy k
    have hgy := (hg.contDiffAt (hW.mem_nhds (hsub y hy k))).differentiableAt
      (by simp : (↑(m + 1) : WithTop ℕ∞) ≠ 0)
    have he := hgy.hasFDerivAt.comp y (hasFDerivAt_prodMk_left (𝕜 := ℝ) y (q k))
    have he' : HasFDerivAt (fun z => f z k) (g' (y,q k)) y := by
      apply he.congr_of_eventuallyEq
      filter_upwards [hU.mem_nhds hy] with z hz
      exact heq z hz k
    convert he' using 1
    apply ContinuousLinearMap.ext
    intro v
    change d y k v = g' (y,q k) v
    rw [hdeq y hy k]
end ExpandedFA.PartV.CompactParameter
namespace ExpandedFA.PartV

theorem scalarReducedResolventExtension_zero {𝕜 : Type*} [RCLike 𝕜]
    {a b : ℝ} (hab : a ≤ b) (k : C(volterraTriangle a b, 𝕜 →L[𝕜] 𝕜)) (p : ℝ × ℝ) :
    scalarReducedResolventExtension hab k 0 p = k (volterraTriangleClamp hab p) 1 := by
  dsimp only [scalarReducedResolventExtension]
  rw [(volterra_resolvent_kernel_identities hab k 0).1]
  simp

theorem scalarResolventExtension_eq_mul {𝕜 : Type*} [RCLike 𝕜]
    {a b : ℝ} (hab : a ≤ b) (k : C(volterraTriangle a b, 𝕜 →L[𝕜] 𝕜))
    (lam : 𝕜) (p : ℝ × ℝ) :
    scalarResolventExtension hab k lam p = lam * scalarReducedResolventExtension hab k lam p := by
  dsimp only [scalarResolventExtension, scalarReducedResolventExtension]
  rw [volterraResolventKernel_eq_smul hab k lam]
  simp

theorem scalarResolventExtension_zero {𝕜 : Type*} [RCLike 𝕜]
    {a b : ℝ} (hab : a ≤ b) (k : C(volterraTriangle a b, 𝕜 →L[𝕜] 𝕜)) :
    scalarResolventExtension hab k 0 = 0 := by
  funext p
  rw [scalarResolventExtension_eq_mul]
  simp

theorem volterra_scalar_resolvent_zero_parameter {𝕜 : Type*} [RCLike 𝕜]
    (a b : ℝ) (hab : a ≤ b) (m : ℕ) (U : Set (ℝ × ℝ))
    (hsub : volterraTriangle a b ⊆ U) (k : ℝ × ℝ → 𝕜) (hk : ContDiffOn ℝ m k U) :
    let kop := VolterraSmoothnessSpec.scalarVolterraKernel k (hk.continuousOn.mono hsub)
    ContDiffOn ℝ m (scalarReducedResolventExtension hab kop 0) (volterraTriangle a b) ∧
    ContDiffOn ℝ m (scalarResolventExtension hab kop 0) (volterraTriangle a b) := by
  dsimp only
  constructor
  · apply (hk.mono hsub).congr
    intro p hp
    rw [scalarReducedResolventExtension_zero]
    have he : volterraTriangleClamp hab p = ⟨p, hp⟩ := volterraTriangleClamp_coe hab ⟨p,hp⟩
    simp [he, VolterraSmoothnessSpec.scalarVolterraKernel]
  · rw [scalarResolventExtension_zero]
    exact contDiffOn_const

theorem scalarContinuousLinearMap_apply {𝕜 : Type*} [RCLike 𝕜]
    (A : 𝕜 →L[𝕜] 𝕜) (z : 𝕜) : A z = A 1 * z := by
  simpa [smul_eq_mul, mul_comm] using A.map_smul z (1 : 𝕜)

theorem scalar_kernelConvolution_apply_one {𝕜 : Type*} [RCLike 𝕜]
    {a b : ℝ} {h g : volterraTriangle a b → 𝕜 →L[𝕜] 𝕜}
    (hh : Continuous h) (hg : Continuous g) (p : volterraTriangle a b) :
    kernelConvolution h g p 1 =
      ∫ r in p.val.2..p.val.1,
        h (kernelLeftPoint p r) 1 * g (kernelRightPoint p r) 1 := by
  unfold kernelConvolution
  rw [instNormedSpaceReal_specs_2, NormedSpace.restrictScalars_eq]
  have hi := ((continuous_kernelConvolution_integrand hh hg).comp
    ( (continuous_const : Continuous (fun _ : ℝ => p)).prodMk continuous_id)).intervalIntegrable (μ := volume) p.val.2 p.val.1
  calc
    _ = ∫ r in p.val.2..p.val.1, (h (kernelLeftPoint p r)).comp (g (kernelRightPoint p r)) 1 := by
      simpa only [Function.comp_def, id_eq] using ContinuousLinearMap.intervalIntegral_apply hi (1 : 𝕜)
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro r hr
      simpa only [ContinuousLinearMap.comp_apply] using scalarContinuousLinearMap_apply (h (kernelLeftPoint p r)) (g (kernelRightPoint p r) 1)

theorem scalarResolventExtension_contDiffOn_of_reduced {𝕜 : Type*} [RCLike 𝕜]
    {a b : ℝ} (hab : a ≤ b) (k : C(volterraTriangle a b, 𝕜 →L[𝕜] 𝕜))
    (lam : 𝕜) (m : ℕ) (h : ContDiffOn ℝ m
      (scalarReducedResolventExtension hab k lam) (volterraTriangle a b)) :
    ContDiffOn ℝ m (scalarResolventExtension hab k lam) (volterraTriangle a b) := by
  have he : scalarResolventExtension hab k lam =
      fun p => lam * scalarReducedResolventExtension hab k lam p :=
    funext (scalarResolventExtension_eq_mul hab k lam)
  rw [he]
  exact contDiffOn_const.mul h

theorem scalarReducedResolventExtension_identities {𝕜 : Type*} [RCLike 𝕜]
    {a b : ℝ} (hab : a ≤ b) (k : ℝ × ℝ → 𝕜)
    (hk : ContinuousOn k (volterraTriangle a b)) (lam : 𝕜)
    (p : volterraTriangle a b) :
    let kop := VolterraSmoothnessSpec.scalarVolterraKernel k hk
    let R := scalarReducedResolventExtension hab kop lam
    (R p = k p + lam * ∫ r in p.val.2..p.val.1,
      k (kernelLeftPoint p r) * R (kernelRightPoint p r)) ∧
    (R p = k p + lam * ∫ r in p.val.2..p.val.1,
      R (kernelLeftPoint p r) * k (kernelRightPoint p r)) := by
  dsimp only
  let kop := VolterraSmoothnessSpec.scalarVolterraKernel k hk
  have hc : Continuous (volterraReducedResolventKernel kop lam) :=
    (volterra_kernel_series hab kop lam).1
  have hl := congrArg (fun A : 𝕜 →L[𝕜] 𝕜 => A 1)
    ((volterra_resolvent_kernel_identities hab kop lam).1 p)
  have hr := congrArg (fun A : 𝕜 →L[𝕜] 𝕜 => A 1)
    ((volterra_resolvent_kernel_identities hab kop lam).2 p)
  rw [add_apply, smul_apply,
    scalar_kernelConvolution_apply_one kop.continuous hc] at hl
  rw [add_apply, smul_apply,
    scalar_kernelConvolution_apply_one hc kop.continuous] at hr
  constructor
  · simpa only [scalarReducedResolventExtension, volterraTriangleClamp_coe,
      kop, VolterraSmoothnessSpec.scalarVolterraKernel, ContinuousMap.coe_mk,
      ContinuousLinearMap.lsmul_apply, smul_eq_mul, mul_one] using hl
  · simpa only [scalarReducedResolventExtension, volterraTriangleClamp_coe,
      kop, VolterraSmoothnessSpec.scalarVolterraKernel, ContinuousMap.coe_mk,
      ContinuousLinearMap.lsmul_apply, smul_eq_mul, mul_one] using hr

end ExpandedFA.PartV

namespace ExpandedFA.PartV
section KernelParameter
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [CompleteSpace E] {a b : ℝ}

/-- Dependence of the Volterra operator on its continuous operator kernel. -/
def volterraKernelToOperator (hab : a ≤ b) :
    C(volterraTriangle a b, E →L[𝕜] E) →L[𝕜]
      (C(VolterraInterval a b, E) →L[𝕜] C(VolterraInterval a b, E)) :=
  by
    let L : C(volterraTriangle a b, E →L[𝕜] E) →ₗ[𝕜]
        (C(VolterraInterval a b, E) →L[𝕜] C(VolterraInterval a b, E)) :=
      { toFun := fun k => VolterraOperatorSpec.OperatorValue 𝕜 E a b hab k
        map_add' := fun h g => volterra_operator_add_kernel hab h g
        map_smul' := fun c h => by
          change VolterraOperatorSpec.OperatorValue 𝕜 E a b hab (c • h) =
            c • VolterraOperatorSpec.OperatorValue 𝕜 E a b hab h
          exact volterra_operator_smul_kernel hab c h }
    exact LinearMap.mkContinuous
      (𝕜 := 𝕜) (𝕜₂ := 𝕜)
      (E := C(volterraTriangle a b, E →L[𝕜] E))
      (F := C(VolterraInterval a b, E) →L[𝕜] C(VolterraInterval a b, E))
      (σ := RingHom.id 𝕜) L (b - a) (fun k => by
      change ‖VolterraOperatorSpec.OperatorValue 𝕜 E a b hab k‖ ≤ (b-a) * ‖k‖
      simpa only [mul_comm] using (volterra_operator_properties 𝕜 E a b hab k).2.2)

@[simp] theorem volterraKernelToOperator_apply (hab : a ≤ b)
    (k : C(volterraTriangle a b, E →L[𝕜] E)) :
    volterraKernelToOperator hab k = VolterraOperatorSpec.OperatorValue 𝕜 E a b hab k := rfl

/-- Native inverse of the second-kind Volterra operator. -/
def volterraKernelInverse (hab : a ≤ b) (lam : 𝕜)
    (k : C(volterraTriangle a b, E →L[𝕜] E)) :=
  Ring.inverse (1 - lam • volterraKernelToOperator hab k)

/-- The inverse is smooth in the kernel in its supremum norm. -/
theorem volterraKernelInverse_contDiff (hab : a ≤ b) (lam : 𝕜)
    (n : WithTop ℕ∞) :
    ContDiff 𝕜 n (volterraKernelInverse (E := E) hab lam) := by
  apply contDiff_iff_contDiffAt.mpr
  intro k
  obtain ⟨hu, _, _⟩ := volterra_inverse_series 𝕜 E a b hab k lam
  obtain ⟨u, hu⟩ := hu
  have hInv : ContDiffAt 𝕜 n Ring.inverse
      (1 - lam • volterraKernelToOperator hab k) := by
    rw [volterraKernelToOperator_apply, ← hu]
    exact contDiffAt_ringInverse (R := C(VolterraInterval a b, E) →L[𝕜] C(VolterraInterval a b, E)) 𝕜 u
  have hOp : ContDiff 𝕜 n
      (volterraKernelToOperator (𝕜 := 𝕜) (E := E) hab) :=
    ContinuousLinearMap.contDiff (𝕜 := 𝕜)
      (E := C(volterraTriangle a b, E →L[𝕜] E))
      (F := C(VolterraInterval a b, E) →L[𝕜] C(VolterraInterval a b, E))
      (n := n) (volterraKernelToOperator (𝕜 := 𝕜) (E := E) hab)
  have hscaled : ContDiff 𝕜 n (fun h : C(volterraTriangle a b, E →L[𝕜] E) =>
      lam • volterraKernelToOperator (𝕜 := 𝕜) (E := E) hab h) :=
    hOp.const_smul lam
  have hconst : ContDiff 𝕜 n (fun _ : C(volterraTriangle a b, E →L[𝕜] E) =>
      (1 : C(VolterraInterval a b, E) →L[𝕜] C(VolterraInterval a b, E))) :=
    contDiff_const
  have hV := hconst.sub hscaled
  exact hInv.comp k hV.contDiffAt

/-- Joint smoothness in the continuous kernel and continuous datum. -/
theorem volterraKernelSolution_contDiff (hab : a ≤ b) (lam : 𝕜)
    (n : WithTop ℕ∞) :
    ContDiff 𝕜 n (fun q : C(volterraTriangle a b, E →L[𝕜] E) ×
        C(VolterraInterval a b, E) =>
      volterraKernelInverse hab lam q.1 q.2) := by
  exact ((volterraKernelInverse_contDiff (E := E) hab lam n).comp contDiff_fst).clm_apply
    contDiff_snd

/-- For scalar state space the same map is smooth in real parameters. -/
theorem volterraScalarKernelSolution_contDiff_real (hab : a ≤ b) (lam : 𝕜)
    (n : WithTop ℕ∞) :
    ContDiff ℝ n (fun q : C(volterraTriangle a b, 𝕜 →L[𝕜] 𝕜) ×
        C(VolterraInterval a b, 𝕜) =>
      volterraKernelInverse hab lam q.1 q.2) :=
  (volterraKernelSolution_contDiff (E := 𝕜) hab lam n).restrict_scalars ℝ

/-- The bottom edge of the fixed unit triangle. -/
def volterraUnitBottom : C(VolterraInterval 0 1, volterraTriangle 0 1) :=
  ⟨fun x => ⟨((x : ℝ), 0), le_rfl, x.property.1, x.property.2⟩,
    (continuous_subtype_val.prodMk continuous_const).subtype_mk _⟩

/-- Restriction to the bottom edge followed by evaluation of scalar operators at one. -/
def volterraUnitDatumMap : C(volterraTriangle 0 1, 𝕜 →L[𝕜] 𝕜) →L[𝕜]
    C(VolterraInterval 0 1, 𝕜) :=
  (ContinuousLinearMap.compLeftContinuous 𝕜 (VolterraInterval 0 1)
      (ContinuousLinearMap.apply 𝕜 𝕜 (1 : 𝕜))).comp
    (ContinuousMap.compCLM 𝕜 (𝕜 →L[𝕜] 𝕜) volterraUnitBottom)

@[simp] theorem volterraUnitDatumMap_apply
    (k : C(volterraTriangle 0 1, 𝕜 →L[𝕜] 𝕜)) (x : VolterraInterval 0 1) :
    volterraUnitDatumMap k x = k ⟨((x : ℝ), 0), le_rfl, x.property.1, x.property.2⟩ 1 := rfl

/-- The scalar resolvent formula on the unit interval is smooth in the unscaled
kernel family and in its scalar Jacobian. -/
theorem volterraUnitResolventFormula_contDiff_real (lam : 𝕜) (n : WithTop ℕ∞) :
    ContDiff ℝ n (fun q : 𝕜 × C(volterraTriangle 0 1, 𝕜 →L[𝕜] 𝕜) =>
      volterraKernelInverse (show (0 : ℝ) ≤ 1 by norm_num) lam (q.1 • q.2)
        (volterraUnitDatumMap q.2) ⟨1, by norm_num, le_rfl⟩) := by
  have hd : ContDiff ℝ n (fun k : C(volterraTriangle 0 1, 𝕜 →L[𝕜] 𝕜) =>
      volterraUnitDatumMap k) :=
    (ContinuousLinearMap.contDiff (𝕜 := 𝕜)
      (E := C(volterraTriangle 0 1, 𝕜 →L[𝕜] 𝕜))
      (F := C(VolterraInterval 0 1, 𝕜)) (n := n)
      (volterraUnitDatumMap (𝕜 := 𝕜))).restrict_scalars ℝ
  have hmul : ContDiff ℝ n (fun q : 𝕜 × C(volterraTriangle 0 1, 𝕜 →L[𝕜] 𝕜) =>
      q.1 • q.2) :=
    contDiff_smul (𝕜 := ℝ) (𝕜' := 𝕜)
      (F := C(volterraTriangle 0 1, 𝕜 →L[𝕜] 𝕜))
  have hdatum : ContDiff ℝ n (fun q : 𝕜 × C(volterraTriangle 0 1, 𝕜 →L[𝕜] 𝕜) =>
      volterraUnitDatumMap q.2) := hd.comp contDiff_snd
  have hpair := hmul.prodMk hdatum
  have hsol := (volterraScalarKernelSolution_contDiff_real
    (show (0 : ℝ) ≤ 1 by norm_num) lam n).comp hpair
  exact ((ContinuousMap.evalCLM 𝕜 ⟨(1 : ℝ), by norm_num, le_rfl⟩ :
    C(VolterraInterval 0 1, 𝕜) →L[𝕜] 𝕜).contDiff.restrict_scalars ℝ).comp hsol

end KernelParameter
end ExpandedFA.PartV

namespace ExpandedFA.PartV

/-- Affine parametrization of a section between the two coordinates. -/
def volterraAffine (p : ℝ × ℝ) (x : ℝ) : ℝ := p.2 + (p.1 - p.2) * x

theorem volterraAffine_bounds {a b : ℝ} (p : volterraTriangle a b)
    {x : ℝ} (hx : x ∈ Icc 0 1) :
    p.val.2 ≤ volterraAffine p x ∧ volterraAffine p x ≤ p.val.1 := by
  have hd : 0 ≤ p.val.1 - p.val.2 := sub_nonneg.mpr p.property.2.1
  dsimp [volterraAffine]
  constructor <;> nlinarith [mul_nonneg hd hx.1, mul_nonneg hd (sub_nonneg.mpr hx.2)]

/-- The affine image of the unit triangle is contained in the original triangle. -/
def volterraAffineTriangle {a b : ℝ} (p : volterraTriangle a b)
    (q : volterraTriangle 0 1) : volterraTriangle a b :=
  ⟨(volterraAffine p q.val.1, volterraAffine p q.val.2),
    p.property.1.trans (volterraAffine_bounds p ⟨q.property.1,
      q.property.2.1.trans q.property.2.2⟩).1,
    by
      dsimp [volterraAffine]
      exact add_le_add_right (mul_le_mul_of_nonneg_left q.property.2.1
        (sub_nonneg.mpr p.property.2.1)) _,
    (volterraAffine_bounds p ⟨q.property.1.trans q.property.2.1, q.property.2.2⟩).2.trans
      p.property.2.2⟩

theorem continuous_volterraAffineTriangle {a b : ℝ} (p : volterraTriangle a b) :
    Continuous (volterraAffineTriangle p) := by
  apply Continuous.subtype_mk
  exact (continuous_const.add (continuous_const.mul
    (continuous_fst.comp continuous_subtype_val))).prodMk
    (continuous_const.add (continuous_const.mul (continuous_snd.comp continuous_subtype_val)))

/-- The transformed operator kernel includes the Jacobian, with no division. -/
def volterraRescaledKernel {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {a b : ℝ}
    (k : C(volterraTriangle a b, E →L[𝕜] E)) (p : volterraTriangle a b) :
    C(volterraTriangle 0 1, E →L[𝕜] E) :=
  (algebraMap ℝ 𝕜 (p.val.1 - p.val.2)) •
    k.comp ⟨volterraAffineTriangle p, continuous_volterraAffineTriangle p⟩


/-- The left endpoint stays fixed as the first coordinate runs from zero to one. -/
def volterraAffineSection {a b : ℝ} (p : volterraTriangle a b)
    (x : VolterraInterval 0 1) : volterraTriangle a b :=
  ⟨(volterraAffine p x, p.val.2), p.property.1,
    (volterraAffine_bounds p x.property).1,
    (volterraAffine_bounds p x.property).2.trans p.property.2.2⟩

theorem continuous_volterraAffineSection {a b : ℝ} (p : volterraTriangle a b) :
    Continuous (volterraAffineSection p) := by
  apply Continuous.subtype_mk
  exact (continuous_const.add (continuous_const.mul continuous_subtype_val)).prodMk continuous_const

section RescaledScalar
variable {𝕜 : Type*} [RCLike 𝕜] {a b : ℝ}

/-- The reduced kernel on a fixed unit section. -/
def volterraRescaledReducedSection (hab : a ≤ b)
    (k : C(volterraTriangle a b, 𝕜 →L[𝕜] 𝕜)) (lam : 𝕜) (p : volterraTriangle a b) :
    C(VolterraInterval 0 1, 𝕜) :=
  ⟨fun x => volterraReducedResolventKernel k lam (volterraAffineSection p x) 1,
    (((volterra_reduced_kernel_uniform_series 𝕜 𝕜 a b hab k lam).1.comp
      (continuous_volterraAffineSection p)).clm_apply continuous_const)⟩

/-- The inhomogeneous term for the rescaled resolvent equation. -/
def volterraRescaledDatum
    (k : C(volterraTriangle a b, 𝕜 →L[𝕜] 𝕜)) (p : volterraTriangle a b) :
    C(VolterraInterval 0 1, 𝕜) :=
  ⟨fun x => k (volterraAffineSection p x) 1,
    (k.continuous.comp (continuous_volterraAffineSection p)).clm_apply continuous_const⟩

/-- Rescaling preserves the convolution integral, including diagonal sections. -/
theorem volterraRescaled_integral (hab : a ≤ b)
    (k : C(volterraTriangle a b, 𝕜 →L[𝕜] 𝕜)) (lam : 𝕜)
    (p : volterraTriangle a b) (x : VolterraInterval 0 1) :
    VolterraOperatorSpec.OperatorValue 𝕜 𝕜 0 1 (by norm_num)
      (volterraRescaledKernel k p) (volterraRescaledReducedSection hab k lam p) x =
    kernelConvolution k (volterraReducedResolventKernel k lam)
      (volterraAffineSection p x) 1 := by
  let R := volterraReducedResolventKernel k lam
  let q := volterraAffineSection p x
  let F : ℝ → 𝕜 := fun r => (k (kernelLeftPoint q r)) (R (kernelRightPoint q r) 1)
  have hR : Continuous R := (volterra_reduced_kernel_uniform_series 𝕜 𝕜 a b hab k lam).1
  have hc := (continuous_kernelConvolution_integrand k.continuous hR).comp
    (continuous_const.prodMk continuous_id : Continuous (fun r : ℝ => (q, r)))
  have hconv : kernelConvolution k R q 1 = ∫ r in q.val.2..q.val.1, F r := by
    unfold kernelConvolution
    rw [instNormedSpaceReal_specs_2, NormedSpace.restrictScalars_eq]
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply] using
      ContinuousLinearMap.intervalIntegral_apply (hc.intervalIntegrable (μ := volume) q.val.2 q.val.1) (1 : 𝕜)
  rw [hconv]
  have hsubst : (p.val.1 - p.val.2) • (∫ y in 0..(x : ℝ), F (volterraAffine p y)) =
      ∫ r in q.val.2..q.val.1, F r := by
    simpa only [volterraAffine, volterraAffineSection, q, mul_zero, add_zero] using
      intervalIntegral.smul_integral_comp_add_mul (f := F) (a := 0) (b := (x : ℝ))
        (p.val.1 - p.val.2) p.val.2
  rw [← hsubst, ← intervalIntegral.integral_smul,
    (volterra_operator_properties 𝕜 𝕜 0 1 (by norm_num) (volterraRescaledKernel k p)).1]
  unfold volterraIntegralValue
  rw [instNormedSpaceReal_specs, NormedSpace.restrictScalars_eq]
  apply intervalIntegral.integral_congr
  intro y hy
  rw [uIcc_of_le x.property.1] at hy
  rw [volterraIntegrand_eq _ _ _ x y hy]
  have hy1 : y ≤ 1 := hy.2.trans x.property.2
  have hf : volterraAffine p y ∈ Icc q.val.2 q.val.1 := by
    constructor
    · exact (volterraAffine_bounds p ⟨hy.1, hy1⟩).1
    · dsimp [q, volterraAffineSection, volterraAffine]
      exact add_le_add_right (mul_le_mul_of_nonneg_left hy.2
        (sub_nonneg.mpr p.property.2.1)) _
  dsimp only [F]
  rw [show kernelLeftPoint q (volterraAffine p y) =
      volterraAffineTriangle p ⟨((x : ℝ), y), hy.1, hy.2, x.property.2⟩ by
    apply Subtype.ext
    change (q.val.1, kernelIntegrationPoint q (volterraAffine p y)) = _
    rw [kernelIntegrationPoint_eq q _ hf]
    rfl,
    show kernelRightPoint q (volterraAffine p y) =
      volterraAffineSection p ⟨y, hy.1, hy1⟩ by
    apply Subtype.ext
    change (kernelIntegrationPoint q (volterraAffine p y), q.val.2) = _
    rw [kernelIntegrationPoint_eq q _ hf]
    rfl]
  dsimp [volterraRescaledKernel, volterraRescaledReducedSection, F]
  simp [Algebra.smul_def, R, sub_mul]

/-- The accepted reduced kernel solves a Volterra equation on the fixed unit interval. -/
theorem volterraRescaled_equation (hab : a ≤ b)
    (k : C(volterraTriangle a b, 𝕜 →L[𝕜] 𝕜)) (lam : 𝕜)
    (p : volterraTriangle a b) :
    volterraRescaledReducedSection hab k lam p - lam •
      VolterraOperatorSpec.OperatorValue 𝕜 𝕜 0 1 (by norm_num)
        (volterraRescaledKernel k p) (volterraRescaledReducedSection hab k lam p) =
      volterraRescaledDatum k p := by
  ext x
  change volterraReducedResolventKernel k lam (volterraAffineSection p x) 1 -
    lam • (VolterraOperatorSpec.OperatorValue 𝕜 𝕜 0 1 (by norm_num)
      (volterraRescaledKernel k p) (volterraRescaledReducedSection hab k lam p) x) = _
  rw [volterraRescaled_integral hab k lam p x]
  apply sub_eq_iff_eq_add.mpr
  exact congrArg (fun A : 𝕜 →L[𝕜] 𝕜 => A 1)
    ((volterra_resolvent_kernel_identities hab k lam).1 (volterraAffineSection p x))

/-- Fixed-domain inverse formula for the original two-variable reduced kernel. -/
theorem volterraRescaled_inverse (hab : a ≤ b)
    (k : C(volterraTriangle a b, 𝕜 →L[𝕜] 𝕜)) (lam : 𝕜)
    (p : volterraTriangle a b) :
    volterraReducedResolventKernel k lam p 1 =
      (Ring.inverse (1 - lam • VolterraOperatorSpec.OperatorValue 𝕜 𝕜 0 1 (by norm_num)
        (volterraRescaledKernel k p)) (volterraRescaledDatum k p)) ⟨1, by norm_num, le_rfl⟩ := by
  let V := VolterraOperatorSpec.OperatorValue 𝕜 𝕜 0 1 (by norm_num) (volterraRescaledKernel k p)
  let u := volterraRescaledReducedSection hab k lam p
  have hu : (1 - lam • V) u = volterraRescaledDatum k p :=
    volterraRescaled_equation hab k lam p
  have hV := (volterra_inverse_series 𝕜 𝕜 0 1 (by norm_num) (volterraRescaledKernel k p) lam).1
  have he : u = Ring.inverse (1 - lam • V) (volterraRescaledDatum k p) := by
    calc
      u = (Ring.inverse (1 - lam • V) * (1 - lam • V)) u := by
        rw [Ring.inverse_mul_cancel _ hV]; rfl
      _ = Ring.inverse (1 - lam • V) (volterraRescaledDatum k p) := by rw [mul_apply_eq_comp, hu]
  have hlast : volterraAffineSection p ⟨1, by norm_num, le_rfl⟩ = p := by
    apply Subtype.ext
    simp [volterraAffineSection, volterraAffine]
  have h := congrArg (fun w : C(VolterraInterval 0 1, 𝕜) => w ⟨1, by norm_num, le_rfl⟩) he
  simpa only [u, volterraRescaledReducedSection, ContinuousMap.coe_mk, hlast] using h

end RescaledScalar
/-- Polynomial affine map, before restricting the two triangles. -/
def volterraAffinePair (p q : ℝ × ℝ) : ℝ × ℝ :=
  (volterraAffine p q.1, volterraAffine p q.2)

theorem contDiff_volterraAffinePair (n : WithTop ℕ∞) :
    ContDiff ℝ n (fun z : (ℝ × ℝ) × (ℝ × ℝ) => volterraAffinePair z.1 z.2) := by
  exact ((contDiff_snd.comp contDiff_fst).add
      (((contDiff_fst.comp contDiff_fst).sub (contDiff_snd.comp contDiff_fst)).mul
        (contDiff_fst.comp contDiff_snd))).prodMk
    ((contDiff_snd.comp contDiff_fst).add
      (((contDiff_fst.comp contDiff_fst).sub (contDiff_snd.comp contDiff_fst)).mul
        (contDiff_snd.comp contDiff_snd)))

/-- All parameters whose rescaled unit triangle stays inside the ambient domain. -/
def volterraKernelParameterDomain (U : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  {p | ∀ q : volterraTriangle 0 1, volterraAffinePair p q ∈ U}

theorem isOpen_volterraKernelParameterDomain {U : Set (ℝ × ℝ)} (hU : IsOpen U) :
    IsOpen (volterraKernelParameterDomain U) := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  have hc : Continuous (fun z : (ℝ × ℝ) × volterraTriangle 0 1 =>
      volterraAffinePair z.1 z.2) :=
    (contDiff_volterraAffinePair 0).continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have h := (isCompact_univ : IsCompact (univ : Set (volterraTriangle 0 1))).eventually_forall_of_forall_eventually
    (x₀ := p) (P := fun r q => volterraAffinePair r q ∈ U)
    (fun q _ => hc.continuousAt.preimage_mem_nhds (hU.mem_nhds (hp q)))
  exact h.mono (fun r hr q => hr q (mem_univ q))

theorem volterraTriangle_subset_parameterDomain {a b : ℝ} {U : Set (ℝ × ℝ)}
    (hsub : volterraTriangle a b ⊆ U) :
    volterraTriangle a b ⊆ volterraKernelParameterDomain U := by
  intro p hp q
  exact hsub (volterraAffineTriangle ⟨p, hp⟩ q).property

/-- A continuous-map-valued family on the open admissible parameter set.
The value outside that set is irrelevant to all within derivatives. -/
def volterraKernelFamily {𝕜 : Type*} [RCLike 𝕜]
    {U : Set (ℝ × ℝ)} (k : ℝ × ℝ → 𝕜 →L[𝕜] 𝕜) (hk : ContinuousOn k U)
    (p : ℝ × ℝ) : C(volterraTriangle 0 1, 𝕜 →L[𝕜] 𝕜) := by
  classical
  exact if hp : p ∈ volterraKernelParameterDomain U then
    ⟨fun q => k (volterraAffinePair p q), hk.comp_continuous
      ((contDiff_volterraAffinePair 0).continuous.comp
        (continuous_const.prodMk continuous_subtype_val)) hp⟩
  else 0

@[simp] theorem volterraKernelFamily_apply {𝕜 : Type*} [RCLike 𝕜]
    {U : Set (ℝ × ℝ)} (k : ℝ × ℝ → 𝕜 →L[𝕜] 𝕜) (hk : ContinuousOn k U)
    {p : ℝ × ℝ} (hp : p ∈ volterraKernelParameterDomain U) (q : volterraTriangle 0 1) :
    volterraKernelFamily k hk p q = k (volterraAffinePair p q) := by
  simp only [volterraKernelFamily, dite_eq_left hp, ContinuousMap.coe_mk]

end ExpandedFA.PartV


namespace ExpandedFA.PartV
/-- Joint ambient regularity gives operator-norm regularity of all unit-triangle pullbacks. -/
theorem volterraKernelFamily_contDiffOn {𝕜 : Type*} [RCLike 𝕜]
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) (m : ℕ)
    (k : ℝ × ℝ → 𝕜 →L[𝕜] 𝕜) (hk : ContDiffOn ℝ m k U) :
    ContDiffOn ℝ m (volterraKernelFamily k hk.continuousOn) (volterraKernelParameterDomain U) := by
  let A := fun z : (ℝ × ℝ) × (ℝ × ℝ) => volterraAffinePair z.1 z.2
  let W := A ⁻¹' U
  have hA := contDiff_volterraAffinePair m
  have hg : ContDiffOn ℝ m (fun z => k (A z)) W :=
    hk.comp hA.contDiffOn (fun _ hz => hz)
  apply CompactParameter.contDiffOn_of_ambient m continuous_subtype_val
    (isOpen_volterraKernelParameterDomain hU) (hU.preimage hA.continuous)
    (fun p hp q => hp q) hg
  intro p hp q
  exact volterraKernelFamily_apply k hk.continuousOn hp q
end ExpandedFA.PartV

namespace ExpandedFA.PartV
/-- Both actual scalar resolvent kernels are jointly C^m on the full closed triangle. -/
theorem volterra_scalar_resolvent_regularity : VolterraSmoothnessSpec.ScalarResolventRegularity := by
  intro 𝕜 _ a b hab m U hU hsub k hk lam
  let K : ℝ × ℝ → 𝕜 →L[𝕜] 𝕜 := fun p => ContinuousLinearMap.lsmul 𝕜 𝕜 (k p)
  have hK : ContDiffOn ℝ m K U :=
    ((ContinuousLinearMap.lsmul 𝕜 𝕜 : 𝕜 →L[𝕜] 𝕜 →L[𝕜] 𝕜).restrictScalars ℝ).contDiff.comp_contDiffOn hk
  let kop := VolterraSmoothnessSpec.scalarVolterraKernel k (hk.continuousOn.mono hsub)
  let F := volterraKernelFamily K hK.continuousOn
  let S := volterraKernelParameterDomain U
  have hF : ContDiffOn ℝ m F S := volterraKernelFamily_contDiffOn hU m K hK
  have hc : ContDiffOn ℝ m (fun p : ℝ × ℝ => algebraMap ℝ 𝕜 (p.1 - p.2)) S := by
    exact (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).contDiff.comp_contDiffOn
      (contDiffOn_fst.sub contDiffOn_snd)
  have hformula := (volterraUnitResolventFormula_contDiff_real lam m).comp_contDiffOn
    (hc.prodMk hF)
  have hred : ContDiffOn ℝ m (scalarReducedResolventExtension hab kop lam)
      (volterraTriangle a b) := by
    apply (hformula.mono (volterraTriangle_subset_parameterDomain hsub)).congr
    intro p hp
    let pp : volterraTriangle a b := ⟨p,hp⟩
    have hpS : p ∈ S := volterraTriangle_subset_parameterDomain hsub hp
    have hscaled : (algebraMap ℝ 𝕜 (p.1 - p.2)) • F p = volterraRescaledKernel kop pp := by
      congr 1
      apply ContinuousMap.ext
      intro q
      rw [show F p q = K (volterraAffinePair p q) from
        volterraKernelFamily_apply K hK.continuousOn hpS q]
      rfl
    have hdatum : volterraUnitDatumMap (F p) = volterraRescaledDatum kop pp := by
      ext x
      rw [volterraUnitDatumMap_apply,
        show F p ⟨((x : ℝ), 0), le_rfl, x.property.1, x.property.2⟩ =
          K (volterraAffinePair p ((x : ℝ),0)) from
          volterraKernelFamily_apply K hK.continuousOn hpS _]
      simp [K, kop, VolterraSmoothnessSpec.scalarVolterraKernel, volterraRescaledDatum,
        volterraAffinePair, volterraAffineSection, volterraAffine, pp]
    dsimp only [Function.comp_def]
    change scalarReducedResolventExtension hab kop lam p = _
    rw [hscaled, hdatum]
    change volterraReducedResolventKernel kop lam (volterraTriangleClamp hab p) 1 = _
    rw [show volterraTriangleClamp hab p = pp from volterraTriangleClamp_coe hab pp]
    exact volterraRescaled_inverse hab kop lam pp
  exact ⟨hred, scalarResolventExtension_contDiffOn_of_reduced hab kop lam m hred⟩
end ExpandedFA.PartV
