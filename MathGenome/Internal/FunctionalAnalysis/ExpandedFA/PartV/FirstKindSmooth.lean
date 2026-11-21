import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.FirstKindSmooth
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.VolterraSmoothness
import Mathlib.Tactic.LinearCombination

set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

noncomputable section
open Set MeasureTheory
namespace ExpandedFA.PartV.FirstKindSmooth

variable {𝕜 : Type*} [RCLike 𝕜] {a b : ℝ}

/-- The scalar kernel as multiplication operators, for reuse of the Banach
Volterra results. -/
def multiplicationKernel (k : C(volterraTriangle a b, 𝕜)) :
    C(volterraTriangle a b, 𝕜 →L[𝕜] 𝕜) :=
  ⟨fun p => k p • ContinuousLinearMap.id 𝕜 𝕜,
    k.continuous.smul continuous_const⟩

def scalarVolterraSection (k : C(volterraTriangle a b, 𝕜))
    (s : VolterraInterval a b) (t : ℝ) : 𝕜 :=
  k ⟨(max (s : ℝ) (min b t), s), s.property.1,
    le_max_left _ _, max_le s.property.2 (min_le_left _ _)⟩

def ScalarVolterraHasDerivative (k dk : C(volterraTriangle a b, 𝕜)) : Prop :=
  ∀ (s : VolterraInterval a b) (t : ℝ) (ht : t ∈ Icc (s : ℝ) b),
    HasDerivWithinAt (scalarVolterraSection k s)
      (dk ⟨(t, s), s.property.1, ht.1, ht.2⟩) (Icc (s : ℝ) b) t

def volterraDiagonalPoint (t : VolterraInterval a b) : volterraTriangle a b :=
  ⟨((t : ℝ), t), t.property.1, le_rfl, t.property.2⟩

def volterraDiagonal (k : C(volterraTriangle a b, 𝕜)) :
    C(VolterraInterval a b, 𝕜) :=
  ⟨fun t => k (volterraDiagonalPoint t), k.continuous.comp
    ((continuous_subtype_val.prodMk continuous_subtype_val).subtype_mk _)⟩

def volterraTriangleTime (p : volterraTriangle a b) : VolterraInterval a b :=
  ⟨p.1.1, p.property.1.trans p.property.2.1, p.property.2.2⟩

/-- The continuous kernel `∂ₜk(t,s) / k(t,t)` on the same triangle. -/
def firstKindTransformedKernel (k dk : C(volterraTriangle a b, 𝕜))
    (hne : ∀ t, volterraDiagonal k t ≠ 0) : C(volterraTriangle a b, 𝕜) :=
  ⟨fun p => dk p / volterraDiagonal k (volterraTriangleTime p),
    dk.continuous.div ((volterraDiagonal k).continuous.comp
      ((continuous_fst.comp continuous_subtype_val).subtype_mk _)) (fun p => hne (volterraTriangleTime p))⟩

def firstKindTransformedDatum (k : C(volterraTriangle a b, 𝕜))
    (g' : C(VolterraInterval a b, 𝕜)) (hne : ∀ t, volterraDiagonal k t ≠ 0) :
    C(VolterraInterval a b, 𝕜) :=
  ⟨fun t => g' t / volterraDiagonal k t,
    g'.continuous.div (volterraDiagonal k).continuous hne⟩

def FirstKindVolterraEquation (hab : a ≤ b) (k : C(volterraTriangle a b, 𝕜))
    (g u : C(VolterraInterval a b, 𝕜)) : Prop :=
  ∀ t, volterraIntegralValue hab (multiplicationKernel k) u t = g t

def FirstKindTransformedEquation (hab : a ≤ b)
    (k dk : C(volterraTriangle a b, 𝕜)) (g' u : C(VolterraInterval a b, 𝕜))
    (_hne : ∀ t, volterraDiagonal k t ≠ 0) : Prop :=
  ∀ t, u t = g' t / volterraDiagonal k t -
    volterraIntegralValue hab (multiplicationKernel (firstKindTransformedKernel k dk _hne)) u t


/-- Changing from the restricted real module to an existing compatible real
module preserves within differentiation. -/
theorem hasDerivWithinAt_restrictScalars_iff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
    (f : ℝ → E) (f' : E) (s : Set ℝ) (x : ℝ) :
    (letI := NormedSpace.restrictScalars ℝ 𝕜 E; HasDerivWithinAt f f' s x) ↔
      HasDerivWithinAt f f' s x := by
  have h : NormedSpace.restrictScalars ℝ 𝕜 E = (inferInstance : NormedSpace ℝ E) :=
    NormedSpace.restrictScalars_eq ℝ 𝕜
  cases h
  rfl

theorem contDiffOn_restrictScalars_iff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
    (f : ℝ → E) (s : Set ℝ) :
    (letI := NormedSpace.restrictScalars ℝ 𝕜 E; ContDiffOn ℝ 1 f s) ↔
      ContDiffOn ℝ 1 f s := by
  have h : NormedSpace.restrictScalars ℝ 𝕜 E = (inferInstance : NormedSpace ℝ E) :=
    NormedSpace.restrictScalars_eq ℝ 𝕜
  cases h
  rfl

@[simp] theorem multiplicationKernel_apply (k : C(volterraTriangle a b, 𝕜))
    (p : volterraTriangle a b) (x : 𝕜) : multiplicationKernel k p x = k p * x := rfl

theorem scalarVolterra_hasDerivative {k dk : C(volterraTriangle a b, 𝕜)}
    (hk : ScalarVolterraHasDerivative k dk) :
    VolterraKernelHasDerivative (multiplicationKernel k) (multiplicationKernel dk) := by
  intro s t ht
  apply (hasDerivWithinAt_restrictScalars_iff (𝕜 := 𝕜) _ _ _ _).mpr
  exact (hk s t ht).smul_const (ContinuousLinearMap.id 𝕜 𝕜)

/-- The operator encoding has exactly the original scalar integral. -/
theorem scalarVolterra_integral_formula (hab : a ≤ b)
    (k : C(volterraTriangle a b, 𝕜)) (u : C(VolterraInterval a b, 𝕜))
    (t : VolterraInterval a b) :
    volterraIntegralValue hab (multiplicationKernel k) u t =
      ∫ s in a..(t : ℝ), k (volterraRetraction t s) * u (Set.projIcc a b hab s) := by
  unfold volterraIntegralValue volterraIntegrand instNormedSpaceReal_specs
  rw [NormedSpace.restrictScalars_eq]
  rfl

/-- Division by the diagonal is independent of the integration variable. -/
theorem firstKind_transformed_integral (hab : a ≤ b)
    (k dk : C(volterraTriangle a b, 𝕜)) (hne : ∀ t, volterraDiagonal k t ≠ 0)
    (u : C(VolterraInterval a b, 𝕜)) (t : VolterraInterval a b) :
    volterraIntegralValue hab
      (multiplicationKernel (firstKindTransformedKernel k dk hne)) u t =
      volterraIntegralValue hab (multiplicationKernel dk) u t / volterraDiagonal k t := by
  simp only [scalarVolterra_integral_formula]
  rw [← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro s _
  change (dk (volterraRetraction t s) /
    volterraDiagonal k (volterraTriangleTime (volterraRetraction t s))) * _ = _
  have ht : volterraTriangleTime (volterraRetraction t s) = t := Subtype.ext rfl
  rw [ht]
  ring

theorem firstKind_transformed_iff (hab : a ≤ b)
    (k dk : C(volterraTriangle a b, 𝕜)) (hne : ∀ t, volterraDiagonal k t ≠ 0)
    (g' u : C(VolterraInterval a b, 𝕜)) :
    FirstKindTransformedEquation hab k dk g' u hne ↔
      ∀ t, volterraDerivativeValue hab (multiplicationKernel k) (multiplicationKernel dk) u t = g' t := by
  unfold FirstKindTransformedEquation
  simp only [firstKind_transformed_integral, volterraDerivativeValue, multiplicationKernel_apply]
  apply forall_congr'
  intro t
  change u t = g' t / volterraDiagonal k t -
      volterraIntegralValue hab (multiplicationKernel dk) u t / volterraDiagonal k t ↔
    volterraDiagonal k t * u t + volterraIntegralValue hab (multiplicationKernel dk) u t = g' t
  rw [← sub_div, eq_div_iff (hne t)]
  constructor <;> intro h <;> linear_combination h

theorem firstKind_compatibility (hab : a ≤ b)
    (k : C(volterraTriangle a b, 𝕜)) (g u : C(VolterraInterval a b, 𝕜))
    (hu : FirstKindVolterraEquation hab k g u) : g ⟨a, le_rfl, hab⟩ = 0 := by
  have h := hu ⟨a, le_rfl, hab⟩
  simpa [volterraIntegralValue] using h.symm

/-- Differentiate equality with the prescribed datum; strict interval length
ensures uniqueness of the within derivatives, including the endpoints. -/
theorem firstKind_to_transformed (hab : a < b)
    (k dk : C(volterraTriangle a b, 𝕜)) (hk : ScalarVolterraHasDerivative k dk)
    (hne : ∀ t, volterraDiagonal k t ≠ 0)
    (g g' u : C(VolterraInterval a b, 𝕜))
    (hg : VolterraHasIntervalDerivative (𝕜 := 𝕜) hab.le g g')
    (hu : FirstKindVolterraEquation hab.le k g u) :
    FirstKindTransformedEquation hab.le k dk g' u hne := by
  apply (firstKind_transformed_iff hab.le k dk hne g' u).mpr
  intro t
  have hV : VolterraOperatorSpec.OperatorValue 𝕜 𝕜 a b hab.le (multiplicationKernel k) u = g := by
    ext x
    rw [(volterra_operator_properties 𝕜 𝕜 a b hab.le (multiplicationKernel k)).1]
    exact hu x
  have hd := volterra_hasDerivWithinAt hab.le (multiplicationKernel k)
    (multiplicationKernel dk) u (scalarVolterra_hasDerivative hk) t
  rw [hV] at hd
  have hd' := (hasDerivWithinAt_restrictScalars_iff (𝕜 := 𝕜) _ _ _ _).mp hd
  have hgt := (hasDerivWithinAt_restrictScalars_iff (𝕜 := 𝕜) _ _ _ _).mp (hg t)
  exact (hd'.derivWithin (uniqueDiffOn_Icc hab t t.property)).symm.trans
    (hgt.derivWithin (uniqueDiffOn_Icc hab t t.property))

/-- Recover the first-kind equation from its derivative and its value at `a`.
The two fundamental-theorem identities use only the original interval. -/
theorem firstKind_of_transformed (hab : a < b)
    (k dk : C(volterraTriangle a b, 𝕜)) (hk : ScalarVolterraHasDerivative k dk)
    (hne : ∀ t, volterraDiagonal k t ≠ 0)
    (g g' u : C(VolterraInterval a b, 𝕜))
    (hg : VolterraHasIntervalDerivative (𝕜 := 𝕜) hab.le g g')
    (hga : g ⟨a, le_rfl, hab.le⟩ = 0)
    (hu : FirstKindTransformedEquation hab.le k dk g' u hne) :
    FirstKindVolterraEquation hab.le k g u := by
  have hd := (firstKind_transformed_iff hab.le k dk hne g' u).mp hu
  intro t
  have hprim := volterra_integral_primitive hab.le (multiplicationKernel k)
    (multiplicationKernel dk) u (scalarVolterra_hasDerivative hk) t
  unfold volterraDifferentiationProofRealSpace at hprim
  rw [NormedSpace.restrictScalars_eq] at hprim
  rw [hprim]
  have hi : (∫ r in a..(t : ℝ),
      volterraDerivativeValue hab.le (multiplicationKernel k) (multiplicationKernel dk) u
        (Set.projIcc a b hab.le r)) =
      ∫ r in a..(t : ℝ), volterraIntervalExtension hab.le g' r := by
    apply intervalIntegral.integral_congr
    intro r _
    exact hd _
  rw [hi]
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le t.property.1
    (continuous_volterraIntervalExtension hab.le g).continuousOn
    (f' := volterraIntervalExtension hab.le g')
    (fun r hr => by
      let ri : VolterraInterval a b := ⟨r, hr.1.le, hr.2.le.trans t.property.2⟩
      change HasDerivAt (volterraIntervalExtension hab.le g)
        (volterraIntervalExtension hab.le g' ri) r
      rw [volterraIntervalExtension_coe]
      have hgr := (hasDerivWithinAt_restrictScalars_iff (𝕜 := 𝕜) _ _ _ _).mp (hg ri)
      exact hgr.hasDerivAt (Icc_mem_nhds hr.1 (hr.2.trans_le t.property.2)))
    ((continuous_volterraIntervalExtension hab.le g').intervalIntegrable _ _)
  rw [hFTC, volterraIntervalExtension_coe hab.le g t]
  have ha := volterraIntervalExtension_coe hab.le g ⟨a, le_rfl, hab.le⟩
  rw [ha, hga, sub_zero]

/-- Full-interval solvability applies to the divided continuous kernel with
parameter `-1`, without a smallness condition. -/
theorem firstKind_transformed_unique (hab : a ≤ b)
    (k dk : C(volterraTriangle a b, 𝕜)) (hne : ∀ t, volterraDiagonal k t ≠ 0)
    (g' : C(VolterraInterval a b, 𝕜)) :
    ∃! u, FirstKindTransformedEquation hab k dk g' u hne := by
  let l := multiplicationKernel (firstKindTransformedKernel k dk hne)
  let f := firstKindTransformedDatum k g' hne
  let V := VolterraOperatorSpec.OperatorValue 𝕜 𝕜 a b hab l
  have hformula := (volterra_operator_properties 𝕜 𝕜 a b hab l).1
  have heq (u : C(VolterraInterval a b, 𝕜)) :
      FirstKindTransformedEquation hab k dk g' u hne ↔ u - (-1 : 𝕜) • V u = f := by
    simp only [neg_one_smul, sub_neg_eq_add]
    constructor
    · intro hu
      ext t
      change u t + V u t = g' t / volterraDiagonal k t
      rw [hformula]
      exact eq_sub_iff_add_eq.mp (hu t)
    · intro hu t
      have h := congrArg (fun v : C(VolterraInterval a b, 𝕜) => v t) hu
      change u t + V u t = g' t / volterraDiagonal k t at h
      rw [hformula] at h
      exact eq_sub_iff_add_eq.mpr h
  obtain ⟨u, hu, huniq, _, _, _⟩ := volterra_solvability_and_iteration 𝕜 𝕜 a b hab l (-1) f
  exact ⟨u, (heq u).mpr hu, fun v hv => huniq v ((heq v).mp hv)⟩


/-- Restriction of the actual ambient derivative supplies all section derivatives.
The derivative here is derived from native `C¹`, not an added hypothesis. -/
theorem ambient_scalar_hasDerivative {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hsub : volterraTriangle a b ⊆ U) (k : ℝ × ℝ → 𝕜)
    (hk : ContDiffOn ℝ 1 k U) :
    let K : C(volterraTriangle a b, 𝕜) := ⟨fun p => k p,
      (hk.continuousOn.mono hsub).domRestrict⟩
    let D : C(volterraTriangle a b, 𝕜) := ⟨fun p => scalarVolterraPartialFirst k p,
      (((hk.fderiv_of_isOpen (m := 0) hU (by simp)).clm_apply contDiffOn_const).continuousOn.mono
        hsub).domRestrict⟩
    ScalarVolterraHasDerivative K D := by
  intro K D s t ht
  have hp : (t, (s : ℝ)) ∈ volterraTriangle a b := ⟨s.property.1, ht⟩
  have hder := (hk.contDiffAt (hU.mem_nhds (hsub hp))).differentiableAt_one.hasFDerivAt
  have hline : HasDerivAt (fun r : ℝ => (r, (s : ℝ))) (1, 0) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t (s : ℝ))
  have h := hder.comp_hasDerivAt t hline
  apply h.hasDerivWithinAt.congr_of_mem _ ht
  intro r hr
  change k (max (s : ℝ) (min b r), (s : ℝ)) = k (r, (s : ℝ))
  rw [min_eq_right hr.2, max_eq_right hr.1]

/-- The internal multiplication-operator encoding equals the source integral. -/
theorem ambient_equation_iff (hab : a ≤ b) (k : ℝ × ℝ → 𝕜)
    (hc : ContinuousOn k (volterraTriangle a b))
    (g u : C(VolterraInterval a b, 𝕜)) :
    FirstKindVolterraEquation hab ⟨fun p => k p, hc.domRestrict⟩ g u ↔
      firstKindVolterraEquation hab k g u := by
  have heq (t : VolterraInterval a b) :
      volterraIntegralValue hab (multiplicationKernel ⟨fun p => k p, hc.domRestrict⟩) u t =
        ∫ s in a..(t : ℝ), k ((t : ℝ), s) * volterraIntervalExtension hab u s := by
    rw [scalarVolterra_integral_formula]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le t.property.1] at hs
    dsimp [volterraRetraction, volterraIntervalExtension]
    rw [min_eq_right hs.2, max_eq_right hs.1]
  unfold FirstKindVolterraEquation firstKindVolterraEquation
  simp only [heq]

/-- Complete endpoint classification; singleton integral equations constrain
only the datum, and constants zero and one give distinct solutions. -/
theorem singleton_classification : FirstKindSmoothSpec.SingletonClassification := by
  intro 𝕜 _ a k g
  have heq (u : C(VolterraInterval a a, 𝕜)) :
      firstKindVolterraEquation (le_refl a) k g u ↔ g ⟨a, le_rfl, le_rfl⟩ = 0 := by
    constructor
    · intro hu
      have h := hu ⟨a, le_rfl, le_rfl⟩
      simpa using h.symm
    · intro hg t
      have ht : t = ⟨a, le_rfl, le_rfl⟩ :=
        Subtype.ext (le_antisymm t.property.2 t.property.1)
      subst t
      simpa [firstKindVolterraEquation] using hg.symm
  refine ⟨heq, ?_⟩
  intro hg hu
  obtain ⟨u, _, huniq⟩ := hu
  have h0 := huniq (ContinuousMap.const _ 0) ((heq _).mpr hg)
  have h1 := huniq (ContinuousMap.const _ 1) ((heq _).mpr hg)
  have h01 := congrArg (fun f : C(VolterraInterval a a, 𝕜) => f ⟨a, le_rfl, le_rfl⟩)
    (h0.trans h1.symm)
  exact zero_ne_one h01

/-- The source first-kind solvability theorem, with the positive-interval
uniqueness and zero-interval existence cases kept separate. -/
theorem c1_solvability : FirstKindSmoothSpec.C1Solvability := by
  intro 𝕜 _ a b hab U hU hsub k hk hne g hg
  by_cases hlt : a < b
  · let K : C(volterraTriangle a b, 𝕜) :=
      ⟨fun p => k p, (hk.continuousOn.mono hsub).domRestrict⟩
    let D : C(volterraTriangle a b, 𝕜) :=
      ⟨fun p => scalarVolterraPartialFirst k p,
        (((hk.fderiv_of_isOpen (m := 0) hU (by simp)).clm_apply contDiffOn_const).continuousOn.mono
          hsub).domRestrict⟩
    have hKD : ScalarVolterraHasDerivative K D := ambient_scalar_hasDerivative hU hsub k hk
    have hdiag : ∀ t, volterraDiagonal K t ≠ 0 := hne
    have hgr := (contDiffOn_restrictScalars_iff (𝕜 := 𝕜) _ _).mpr hg
    obtain ⟨g', hg'⟩ := (volterra_c1_identification 𝕜 𝕜 a b hlt g).mp hgr
    obtain ⟨u, hu, huniq⟩ := firstKind_transformed_unique hab K D hdiag g'
    have hiff (v : C(VolterraInterval a b, 𝕜)) :
        FirstKindVolterraEquation hab K g v ↔ firstKindVolterraEquation hab k g v :=
      ambient_equation_iff hab k (hk.continuousOn.mono hsub) g v
    have hto (v) (hv : firstKindVolterraEquation hab k g v) :
        FirstKindTransformedEquation hab K D g' v hdiag :=
      firstKind_to_transformed hlt K D hKD hdiag g g' v hg' ((hiff v).mpr hv)
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rintro ⟨v, hv⟩
      exact firstKind_compatibility hab K g v ((hiff v).mpr hv)
    · intro hga
      exact ⟨u, (hiff u).mp (firstKind_of_transformed hlt K D hKD hdiag g g' u hg' hga hu)⟩
    · intro _ v w hv hw
      exact (huniq v (hto v hv)).trans (huniq w (hto w hw)).symm
  · have hab' : a = b := le_antisymm hab (le_of_not_gt hlt)
    subst b
    have heq := (singleton_classification 𝕜 a k g).1
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rintro ⟨u, hu⟩
      exact (heq u).mp hu
    · intro hga
      exact ⟨ContinuousMap.const _ 0, (heq _).mpr hga⟩
    · intro h
      exact (lt_irrefl a h).elim

end ExpandedFA.PartV.FirstKindSmooth
