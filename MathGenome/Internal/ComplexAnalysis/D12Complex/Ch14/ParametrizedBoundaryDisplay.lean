import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.ParametrizedBoundaryDisplay
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch14.ComplexGreenBridge
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Topology.Instances.Matrix

noncomputable section
set_option maxHeartbeats 800000
open Set Filter Topology
open scoped RealInnerProductSpace ContDiff

open D12Complex.ComplexGreenBridge
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C12.ClassicalRegularDomains.Model
open Specs.D04.C06.JordanRegions.Model
open Specs.D04.C12.RegularDomainRiemannManifoldBridge.Model
open Specs.D04.C13.OrientedEuclideanDictionary.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.Model
open Specs.D04.C14.ChartIndependentTangentSpaces.Model
open Specs.D04.C14.OrientationsAndChartSigns.Model
open Specs.D04.C14.MetricTopFormsAndDensities.Model
open Specs.D04.C14.OutwardFirstBoundaryOrientation.Model
open Specs.D04.C15.FiniteGeometricPatchIntegrals.Model
open Specs.D04.C15.FiniteManifoldBoundaryAssembly.Model
open Specs.D04.C15.GeneralizedStokes.Model
open Specs.D04.C12.GaussDivergenceTheorem.Model

namespace D12Complex.ParametrizedBoundaryDisplay
open D12Complex.ComplexGreenBridge
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C12.ClassicalRegularDomains.Model
open Specs.D04.C06.JordanRegions.Model
open Specs.D04.C15.FiniteGeometricPatchIntegrals.Model

lemma interval_coordinate (t : ℝ) : intervalIsometry t 0 = t := by
  exact OrthonormalBasis.singleton_repr t 0

lemma interval_region_closed (a b : ℝ) :
    IsClosed (intervalIsometry '' Icc a b) :=
  intervalIsometry.toHomeomorph.isClosedMap _ isClosed_Icc

lemma interval_region_jordan (a b : ℝ) (hab : a ≤ b) :
    Jordan (intervalIsometry '' Icc a b) := by
  let Q : Specs.D04.C06.DarbouxIntegral.Model.Box 1 :=
    ⟨intervalIsometry a, intervalIsometry b, fun i => by
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      simpa only [interval_coordinate] using hab⟩
  have he : intervalIsometry '' Icc a b = Specs.D04.C06.DarbouxIntegral.Model.carrier Q := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩ i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      simpa [Q, interval_coordinate] using ht
    · intro hx
      refine ⟨intervalIsometry.symm x, ?_, intervalIsometry.apply_symm_apply x⟩
      have h := hx 0
      have he : x 0 = intervalIsometry.symm x := by
        have hh := interval_coordinate (intervalIsometry.symm x)
        simpa only [LinearIsometryEquiv.apply_symm_apply] using hh
      simpa only [Q, interval_coordinate, he] using h
  rw [he]
  exact D04.OneCoordinate.Boxes.jordan_carrier Q

/-- The canonical interval patch keeps the supplied global map literally.
Its open domain is chosen inside the supplied regularity set and over O. -/
lemma interval_patch_exists (O : Set ℂ) (hO : IsOpen O) (γ : ℝ → ℂ)
    (a b : ℝ) (hab : a ≤ b) (T : Set ℝ) (hT : IsOpen T)
    (hI : Icc a b ⊆ T) (hγ : ContDiffOn ℝ 1 γ T)
    (hγO : MapsTo γ (Icc a b) O) :
    ∃ P : Patch 1 (planeIsometry '' O),
      P.region = intervalIsometry '' Icc a b ∧
      (∀ x, P.map x = planeIsometry (γ (intervalIsometry.symm x))) ∧
      P.domain ⊆ intervalIsometry '' T := by
  let S := T ∩ γ ⁻¹' O
  have hS : IsOpen S := hγ.continuousOn.isOpen_inter_preimage hT hO
  have hIS : Icc a b ⊆ S := fun t ht => ⟨hI ht, hγO ht⟩
  let P : Patch 1 (planeIsometry '' O) := {
    region := intervalIsometry '' Icc a b
    jordan := interval_region_jordan a b hab
    map := fun x => planeIsometry (γ (intervalIsometry.symm x))
    domain := intervalIsometry '' S
    open_domain := intervalIsometry.toHomeomorph.isOpenMap _ hS
    contains := by
      rw [(interval_region_closed a b).closure_eq]
      exact image_mono hIS
    regular := by
      exact planeIsometry.contDiff.comp_contDiffOn
        ((hγ.mono (show S ⊆ T from inter_subset_left)).comp
          intervalIsometry.symm.contDiff.contDiffOn (by
            rintro _ ⟨t, ht, rfl⟩
            simpa only [LinearIsometryEquiv.symm_apply_apply] using ht))
    mapsTo := by
      rintro _ ⟨t, ht, rfl⟩
      simp only [LinearIsometryEquiv.symm_apply_apply]
      exact ⟨γ t, ht.2, rfl⟩ }
  exact ⟨P, rfl, fun _ => rfl, image_mono inter_subset_left⟩

/-- A finite family of actual dimension-zero D04 seams. -/
def pointSeams {ι : Type} [Fintype ι] (p : ι → E 2) : Seams 2 where
  count := Fintype.card ι
  dim := fun _ => 0
  lower := fun _ => by norm_num
  parameter := fun _ => {0}
  compact := fun _ => isCompact_singleton
  map := fun i _ => p ((Fintype.equivFin ι).symm i)
  localC1 := by
    intro i x hx
    refine ⟨univ, (fun _ => p ((Fintype.equivFin ι).symm i)), univ_mem,
      contDiffAt_const, ?_⟩
    intro y hy
    rfl

lemma pointSeams_carrier {ι : Type} [Fintype ι] (p : ι → E 2) :
    (pointSeams p).carrier = range p := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, y, hy, hxy⟩ := mem_iUnion.mp hx
    exact ⟨(Fintype.equivFin ι).symm i, hxy⟩
  · rintro ⟨i, rfl⟩
    apply mem_iUnion.mpr
    refine ⟨Fintype.equivFin ι i, (0 : E 0), Set.mem_singleton 0, ?_⟩
    simp [pointSeams]

lemma repeated_value_mem_endpoints (γ : ℝ → ℂ) (a b t s : ℝ)
    (hinj : InjOn γ (Ioo a b)) (ht : t ∈ Icc a b) (hs : s ∈ Icc a b)
    (hne : t ≠ s) (he : γ t = γ s) : γ t ∈ ({γ a, γ b} : Set ℂ) := by
  by_cases hta : t = a
  · simp [hta]
  by_cases htb : t = b
  · simp [htb]
  by_cases hsa : s = a
  · simp [he, hsa]
  by_cases hsb : s = b
  · simp [he, hsb]
  exact (hne (hinj ⟨lt_of_le_of_ne ht.1 (Ne.symm hta), lt_of_le_of_ne ht.2 htb⟩
    ⟨lt_of_le_of_ne hs.1 (Ne.symm hsa), lt_of_le_of_ne hs.2 hsb⟩ he)).elim

lemma common_value_mem_endpoints {m : ℕ} (γ : Fin m → ℝ → ℂ)
    (a b : Fin m → ℝ) (i j : Fin m) (_hij : i ≠ j)
    (hdis : Disjoint (γ i '' Ioo (a i) (b i)) (γ j '' Ioo (a j) (b j)))
    (t s : ℝ) (ht : t ∈ Icc (a i) (b i)) (hs : s ∈ Icc (a j) (b j))
    (he : γ i t = γ j s) :
    γ i t ∈ ({γ i (a i), γ i (b i), γ j (a j), γ j (b j)} : Set ℂ) := by
  by_cases hta : t = a i
  · simp [hta]
  by_cases htb : t = b i
  · simp [htb]
  by_cases hsa : s = a j
  · simp [he, hsa]
  by_cases hsb : s = b j
  · simp [he, hsb]
  exact (Set.disjoint_left.mp hdis
    (mem_image_of_mem _ ⟨lt_of_le_of_ne ht.1 (Ne.symm hta), lt_of_le_of_ne ht.2 htb⟩)
    ⟨s, ⟨lt_of_le_of_ne hs.1 (Ne.symm hsa), lt_of_le_of_ne hs.2 hsb⟩, he.symm⟩).elim

end D12Complex.ParametrizedBoundaryDisplay


noncomputable section
open Set Function
open scoped ContDiff
namespace D12Complex.ParametrizedBoundaryDisplay
open D12Complex.ComplexGreenBridge
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model

lemma real_curve_column (η : ℝ → ℂ) {t : ℝ} (hη : DifferentiableAt ℝ η t) :
    fderiv ℝ (fun x : E 1 => planeIsometry (η (intervalIsometry.symm x)))
      (intervalIsometry t) (standardBasis 1 0) = planeIsometry (deriv η t) := by
  have hdη := hη.hasDerivAt
  have hι := intervalIsometry.symm.toContinuousLinearEquiv.hasFDerivAt
    (x := intervalIsometry t)
  have hdη' : HasDerivAt η (deriv η t) (intervalIsometry.symm (intervalIsometry t)) := by
    simpa using hdη
  have hh := planeIsometry.toContinuousLinearEquiv.hasFDerivAt.comp
    (intervalIsometry t) (hdη'.hasFDerivAt.comp (intervalIsometry t) hι)
  have hdf : fderiv ℝ
      (fun x : E 1 => planeIsometry (η (intervalIsometry.symm x)))
      (intervalIsometry t) =
        planeIsometry.toContinuousLinearEquiv.toContinuousLinearMap.comp
          ((ContinuousLinearMap.toSpanSingleton ℝ (deriv η t)).comp
            intervalIsometry.symm.toContinuousLinearEquiv.toContinuousLinearMap) := hh.fderiv
  rw [hdf]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  rw [← D12Complex.ComplexGreenBridge.interval_basis]
  apply congrArg planeIsometry
  change (intervalIsometry.symm (intervalIsometry 1)) • deriv η t = deriv η t
  simp

lemma real_curve_full_rank (η : ℝ → ℂ) {t : ℝ}
    (hη : DifferentiableAt ℝ η t) (hne : deriv η t ≠ 0) :
    Function.Injective (fderiv ℝ
      (fun x : E 1 => planeIsometry (η (intervalIsometry.symm x)))
      (intervalIsometry t)) := by
  let A := fderiv ℝ
    (fun x : E 1 => planeIsometry (η (intervalIsometry.symm x))) (intervalIsometry t)
  have hcol : A (standardBasis 1 0) ≠ 0 := by
    rw [show A (standardBasis 1 0) = planeIsometry (deriv η t) from real_curve_column η hη]
    exact fun h => hne (planeIsometry.injective (by simpa using h))
  intro x y hxy
  apply intervalIsometry.symm.injective
  have hx : x = (intervalIsometry.symm x) • standardBasis 1 0 := by
    calc
      x = intervalIsometry (intervalIsometry.symm x) := by simp
      _ = _ := by simpa [D12Complex.ComplexGreenBridge.interval_basis] using
        (intervalIsometry.map_smul (intervalIsometry.symm x) (1 : ℝ))
  have hy : y = (intervalIsometry.symm y) • standardBasis 1 0 := by
    calc
      y = intervalIsometry (intervalIsometry.symm y) := by simp
      _ = _ := by simpa [D12Complex.ComplexGreenBridge.interval_basis] using
        (intervalIsometry.map_smul (intervalIsometry.symm y) (1 : ℝ))
  change A x = A y at hxy
  rw [hx, hy, map_smul, map_smul] at hxy
  exact (smul_left_injective ℝ hcol) hxy

/-- An ordinary regular parametrization with ordinary continuous inverse is an
actual D04 embedded chart. No ambient inverse extension is required. -/
def curveEmbeddedChart {V W : Set ℂ} {l r : ℝ}
    (hW : IsOpen W) (η : ℝ → ℂ) (κ : ℂ → ℝ)
    (hη : ContDiffOn ℝ 1 η (Ioo l r))
    (hne : ∀ t ∈ Ioo l r, deriv η t ≠ 0)
    (hmap : MapsTo η (Ioo l r) (frontier V ∩ W))
    (hinv : MapsTo κ (frontier V ∩ W) (Ioo l r))
    (hleft : ∀ t ∈ Ioo l r, κ (η t) = t)
    (hright : ∀ z ∈ frontier V ∩ W, η (κ z) = z)
    (hκ : ContinuousOn κ (frontier V ∩ W)) :
    EmbeddedChart 1 1 2 (planeIsometry '' frontier V) where
  half := false
  half_pos := by simp
  source := intervalIsometry '' Ioo l r
  source_open := ⟨intervalIsometry '' Ioo l r,
    intervalIsometry.toHomeomorph.isOpenMap _ isOpen_Ioo, by simp [parameterSpace]⟩
  ambient := planeIsometry '' W
  ambient_open := planeIsometry.toHomeomorph.isOpenMap _ hW
  toFun := fun x => planeIsometry (η (intervalIsometry.symm x))
  invFun := fun z => intervalIsometry (κ (planeIsometry.symm z))
  map_source := by
    rintro x ⟨t, ht, rfl⟩
    simpa only [intervalIsometry.symm_apply_apply] using
      ⟨mem_image_of_mem planeIsometry (hmap ht).1,
        mem_image_of_mem planeIsometry (hmap ht).2⟩
  map_target := by
    rintro z ⟨⟨p, hp, hpz⟩, ⟨q, hq, hqz⟩⟩
    have hpq : p = q := planeIsometry.injective (hpz.trans hqz.symm)
    subst q
    simp only [← hpz, planeIsometry.symm_apply_apply]
    exact mem_image_of_mem _ (hinv ⟨hp, hq⟩)
  left_inv := by
    rintro x ⟨t, ht, rfl⟩
    simp only [intervalIsometry.symm_apply_apply, planeIsometry.symm_apply_apply, hleft t ht]
  right_inv := by
    rintro z ⟨⟨p, hp, hpz⟩, ⟨q, hq, hqz⟩⟩
    have hpq : p = q := planeIsometry.injective (hpz.trans hqz.symm)
    subst q
    rw [← hpz]
    simp only [planeIsometry.symm_apply_apply, intervalIsometry.symm_apply_apply,
      hright p ⟨hp, hq⟩]
  continuous_toFun := by
    exact planeIsometry.continuous.comp_continuousOn
      (hη.continuousOn.comp intervalIsometry.symm.continuous.continuousOn (by
        rintro x ⟨t, ht, rfl⟩; simpa using ht))
  continuous_invFun := by
    exact intervalIsometry.continuous.comp_continuousOn
      (hκ.comp planeIsometry.symm.continuous.continuousOn (by
        rintro z ⟨⟨p, hp, hpz⟩, ⟨q, hq, hqz⟩⟩
        have hpq : p = q := planeIsometry.injective (hpz.trans hqz.symm)
        subst q
        rw [← hpz, planeIsometry.symm_apply_apply]
        exact ⟨hp, hq⟩))
  regular := by
    rintro x ⟨t, ht, rfl⟩
    refine ⟨intervalIsometry '' Ioo l r,
      fun x => planeIsometry (η (intervalIsometry.symm x)),
      intervalIsometry.toHomeomorph.isOpenMap _ isOpen_Ioo,
      mem_image_of_mem _ ht, ?_, ?_, ?_⟩
    · intro x hx; rfl
    · exact planeIsometry.contDiff.comp_contDiffOn
        (hη.comp intervalIsometry.symm.contDiff.contDiffOn (by
          rintro x ⟨s, hs, rfl⟩; simpa using hs))
    · rintro x ⟨s, hs, rfl⟩
      exact real_curve_full_rank η
        ((hη.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hs))
        (hne s hs)

open Specs.D04.C14.OrientationsAndChartSigns.Model

lemma preconnected_chart_sign {M : Set (E 2)}
    (o : PositiveManifoldOrientation 1 1 M) (c : EmbeddedChart 1 1 2 M)
    (hsource : IsPreconnected c.source) (u : c.source) :
    ∃ s : PointSign, ∀ v : c.source, chartSign o.atPoint c v v.property = s.val := by
  letI : PreconnectedSpace c.source := isPreconnected_iff_preconnectedSpace.mp hsource
  refine ⟨⟨chartSign o.atPoint c u u.property,
    D04.Orientations.chartSign_values o.atPoint c o.manifold.1 o.manifold.2.1 u u.property⟩, ?_⟩
  intro v
  exact (o.locally_constant c).apply_eq_of_preconnectedSpace v u

/-- Ordinary local regular extension data give an actual boundary chart even
at a supplied closed interval endpoint. Every local chart has a constant sign. -/
lemma local_regular_chart {V : Set ℂ} {γ : ℝ → ℂ} {a b : ℝ}
    (hlocal : LocalRegularExtension V γ a b)
    {M : Set (E 2)} (hM : M = planeIsometry '' frontier V)
    (o : PositiveManifoldOrientation 1 1 M) (t : ℝ) (ht : t ∈ Icc a b) :
    ∃ (U : Set (E 1)) (c : EmbeddedChart 1 1 2 M) (s : PointSign),
      IsOpen U ∧ intervalIsometry t ∈ U ∧
      closure (intervalIsometry '' Icc a b) ∩ U ⊆ c.source ∧
      EqOn (fun x => planeIsometry (γ (intervalIsometry.symm x))) c.toFun
        (closure (intervalIsometry '' Icc a b) ∩ U) ∧
      ∀ v : c.source, chartSign o.atPoint c v v.property = s.val := by
  subst M
  obtain ⟨δ, W, η, κ, hδ, hW, htW, hη, hne, heq, hmap, hinv, hleft, hright, hκ⟩ :=
    hlocal t ht
  let c := curveEmbeddedChart hW η κ hη hne hmap hinv hleft hright hκ
  have htI : t ∈ Ioo (t - δ) (t + δ) := by constructor <;> linarith
  have htc : intervalIsometry t ∈ c.source := mem_image_of_mem _ htI
  have hpc : IsPreconnected c.source :=
    isPreconnected_Ioo.image _ intervalIsometry.continuous.continuousOn
  obtain ⟨s, hs⟩ := preconnected_chart_sign o c hpc ⟨intervalIsometry t, htc⟩
  refine ⟨c.source, c, s, ?_, htc, inter_subset_right, ?_, hs⟩
  · exact intervalIsometry.toHomeomorph.isOpenMap _ isOpen_Ioo
  · have hclosed : IsClosed (intervalIsometry '' Icc a b) :=
      intervalIsometry.toHomeomorph.isClosedMap _ isClosed_Icc
    rw [hclosed.closure_eq]
    rintro x ⟨⟨q, hq, rfl⟩, hxc⟩
    change planeIsometry (γ (intervalIsometry.symm (intervalIsometry q))) =
      planeIsometry (η (intervalIsometry.symm (intervalIsometry q)))
    simp only [intervalIsometry.symm_apply_apply]
    apply congrArg planeIsometry
    apply Eq.symm
    apply heq
    refine ⟨hq, ?_⟩
    rcases hxc with ⟨q', hq', hh⟩
    exact intervalIsometry.injective hh ▸ hq'

/-- Equality on a closed nondegenerate interval near t determines the actual
derivative at its endpoints too. -/
lemma deriv_eq_of_local_Icc {γ η : ℝ → ℂ} {a b t δ : ℝ}
    (hab : a < b) (ht : t ∈ Icc a b) (hδ : 0 < δ)
    (hγ : DifferentiableAt ℝ γ t) (hη : DifferentiableAt ℝ η t)
    (heq : EqOn η γ (Icc a b ∩ Ioo (t - δ) (t + δ))) :
    deriv η t = deriv γ t := by
  have hI : Ioo (t - δ) (t + δ) ∈ nhds t :=
    isOpen_Ioo.mem_nhds (by constructor <;> linarith)
  have hevent : η =ᶠ[nhdsWithin t (Icc a b)] γ := by
    filter_upwards [nhdsWithin_le_nhds hI, self_mem_nhdsWithin] with s hsI hsC
    exact heq ⟨hsC, hsI⟩
  have htI : t ∈ Ioo (t - δ) (t + δ) := by constructor <;> linarith
  have hηwithin : HasDerivWithinAt η (deriv η t) (Icc a b) t := hη.hasDerivAt.hasDerivWithinAt
  have hγwithin : HasDerivWithinAt γ (deriv γ t) (Icc a b) t := hγ.hasDerivAt.hasDerivWithinAt
  have hcongr : HasDerivWithinAt η (deriv γ t) (Icc a b) t :=
    hγwithin.congr_of_eventuallyEq hevent (heq ⟨ht, htI⟩)
  exact (hηwithin.derivWithin (uniqueDiffOn_Icc hab t ht)).symm.trans
    (hcongr.derivWithin (uniqueDiffOn_Icc hab t ht))

end D12Complex.ParametrizedBoundaryDisplay

noncomputable section
open Set Function Filter Topology
open scoped ContDiff
namespace D12Complex.ParametrizedBoundaryDisplay
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.Model
open Specs.D04.C14.ChartIndependentTangentSpaces.Model
open D12Complex.ComplexGreenBridge

lemma deriv_eq_of_eqOn_Icc_neighborhood {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : ℝ → F} {a b t : ℝ} (hab : a < b) (ht : t ∈ Icc a b)
    {U : Set ℝ} (hU : U ∈ 𝓝 t)
    (heq : EqOn f g (Icc a b ∩ U))
    (hf : DifferentiableAt ℝ f t) (hg : DifferentiableAt ℝ g t) :
    deriv f t = deriv g t := by
  have hfg : f =ᶠ[𝓝[Icc a b] t] g := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hU] with x hx hxU
    exact heq ⟨hx,hxU⟩
  have he : HasDerivWithinAt f (deriv g t) (Icc a b) t :=
    hg.hasDerivAt.hasDerivWithinAt.congr_of_eventuallyEq hfg (heq ⟨ht,mem_of_mem_nhds hU⟩)
  have h1 := hf.hasDerivAt.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc hab t ht)
  have h2 := he.derivWithin (uniqueDiffOn_Icc hab t ht)
  exact h1.symm.trans h2

lemma chartDifferential_eq_fderiv_on_interval {n : ℕ} {M : Set (E n)}
    (c : EmbeddedChart 1 1 n M) {f : E 1 → E n} {a b : ℝ}
    (hab : a < b) {u : E 1} (hu : u ∈ intervalIsometry '' Icc a b)
    {U : Set (E 1)} (hU : IsOpen U) (huU : u ∈ U)
    (hsource : (intervalIsometry '' Icc a b) ∩ U ⊆ c.source)
    (heq : EqOn f c.toFun ((intervalIsometry '' Icc a b) ∩ U))
    (hf : DifferentiableAt ℝ f u) :
    chartDifferential c u = fderiv ℝ f u := by
  have h_unique : UniqueDiffWithinAt ℝ ((intervalIsometry '' Icc a b) ∩ U) u :=
    ((intervalIsometry.toContinuousLinearEquiv.uniqueDiffOn_image (uniqueDiffOn_Icc hab)) u hu).inter
      (hU.mem_nhds huU)
  have hc := (D04.EmbeddedChart.hasDifferential c (by constructor <;> norm_num)
    (hsource ⟨hu,huU⟩)).mono hsource
  exact h_unique.eq (hc.congr heq (heq ⟨hu,huU⟩)) hf.hasFDerivAt.hasFDerivWithinAt
end D12Complex.ParametrizedBoundaryDisplay

noncomputable section
open Set
open scoped RealInnerProductSpace ContDiff
namespace D12Complex.ParametrizedBoundaryDisplay
open D12Complex.ComplexGreenBridge
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C12.RegularDomainRiemannManifoldBridge.Model
open Specs.D04.C13.OrientedEuclideanDictionary.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.Model
open Specs.D04.C14.ChartIndependentTangentSpaces.Model
open Specs.D04.C14.OrientationsAndChartSigns.Model
open Specs.D04.C14.MetricTopFormsAndDensities.Model
open Specs.D04.C14.OutwardFirstBoundaryOrientation.Model
open Specs.D04.C15.GeneralizedStokes.Model
open Specs.D04.C12.GaussDivergenceTheorem.Model

lemma chart_normal_determinant {M : Set (E 2)}
    (o : PositiveManifoldOrientation 1 2 M) (ho : IsAmbientOrientation o)
    (bO : PositiveManifoldOrientation 1 1 (intrinsicBoundary 1 2 M))
    (hO : OutwardFirst 1 o bO)
    (ν : intrinsicBoundary 1 2 M → E 2)
    (hν : ∀ x : intrinsicBoundary 1 2 M, IsOutwardUnitConormal 1 1 M x (ν x))
    (c : EmbeddedChart 1 1 2 (intrinsicBoundary 1 2 M)) (u : E 1) (hu : u ∈ c.source) :
    omega 2 (Fin.cons (ν ⟨c.toFun u, (c.map_source hu).1⟩)
      (fun i => chartDifferential c u (standardBasis 1 i))) =
      chartSign bO.atPoint c u hu * chartDensity c u := by
  let x : intrinsicBoundary 1 2 M := ⟨c.toFun u, (c.map_source hu).1⟩
  let v := fun i => tangentChartMap c u hu (standardBasis 1 i)
  have hflux := congrArg (fun η => η x v)
    (D04.Gauss.boundary_flux_positive o ho bO hO ν hν (fun _ => ν x))
  change fluxForm (fun _ => ν x) x (fun i => chartDifferential c u (standardBasis 1 i)) =
    inner ℝ (ν x) (ν x) * metricVolume bO.atPoint x v at hflux
  rw [D04.Dictionary.fluxForm_volume, real_inner_self_eq_norm_sq, (hν x).2.1] at hflux
  simp only [one_pow, one_mul] at hflux
  have hmetric := congrArg (fun A => A (standardBasis 1))
    (D04MetricDensity.metricVolume_pullback bO.manifold (by norm_num) bO.atPoint c u hu)
  change metricVolume bO.atPoint x v = _ at hmetric
  simp only [smul_apply, smul_eq_mul, omega, Module.Basis.det_self, mul_one] at hmetric
  exact hflux.trans hmetric

lemma chart_outward_frame {M : Set (E 2)}
    (o : PositiveManifoldOrientation 1 2 M) (ho : IsAmbientOrientation o)
    (bO : PositiveManifoldOrientation 1 1 (intrinsicBoundary 1 2 M))
    (hO : OutwardFirst 1 o bO)
    (ν : intrinsicBoundary 1 2 M → E 2)
    (hν : ∀ x : intrinsicBoundary 1 2 M, IsOutwardUnitConormal 1 1 M x (ν x))
    (c : EmbeddedChart 1 1 2 (intrinsicBoundary 1 2 M)) (u : E 1) (hu : u ∈ c.source) :
    ‖ν ⟨c.toFun u, (c.map_source hu).1⟩‖ = 1 ∧
      (∀ i, inner ℝ (ν ⟨c.toFun u, (c.map_source hu).1⟩)
        (chartDifferential c u (standardBasis 1 i)) = 0) ∧
      0 < chartSign bO.atPoint c u hu *
        omega 2 (Fin.cons (ν ⟨c.toFun u, (c.map_source hu).1⟩)
          (fun i => chartDifferential c u (standardBasis 1 i))) := by
  let x : intrinsicBoundary 1 2 M := ⟨c.toFun u, (c.map_source hu).1⟩
  refine ⟨(hν x).2.1, ?_, ?_⟩
  · intro i
    exact (hν x).2.2.1 _ (tangentChartMap c u hu (standardBasis 1 i)).property
  · rw [chart_normal_determinant o ho bO hO ν hν c u hu]
    have hs := D04.Orientations.chartSign_values bO.atPoint c bO.manifold.1 bO.manifold.2.1 u hu
    have hp := D04MetricDensity.chartDensity_positive c bO.manifold.1 u hu
    rcases hs with hs | hs <;> simpa [hs] using hp

end D12Complex.ParametrizedBoundaryDisplay



namespace D12Complex.ParametrizedBoundaryDisplay
open D12Complex.ComplexGreenBridge
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C12.ClassicalRegularDomains.Model
open Specs.D04.C13.OrientedEuclideanDictionary.Model
open Specs.D04.C14.OrientationsAndChartSigns.Model
open Specs.D04.C15.FiniteGeometricPatchIntegrals.Model

lemma normalAt_eq_actual {V : Set ℂ}
    (hV : IsClassicalRegularDomain (planeIsometry '' V))
    (z : ℂ) (hz : planeIsometry z ∈ frontier (planeIsometry '' V)) :
    normalAt hV z = planeIsometry.symm (outwardNormal hV ⟨planeIsometry z, hz⟩) := by
  simp [normalAt, hz]

lemma literal_integrand_eq_arcIntegrand {V : Set ℂ} {U : Set (E 2)}
    (hV : IsClassicalRegularDomain (planeIsometry '' V))
    (P : Patch 1 U) (γ : ℝ → ℂ)
    (hmap : ∀ x, P.map x = planeIsometry (γ (intervalIsometry.symm x)))
    (u v : ℂ → ℝ) :
    literalIntegrand hV γ u v = arcIntegrand hV P u v := by
  funext t
  have hnormal : normalAt hV (γ t) =
      planeIsometry.symm (patchNormal hV P (intervalIsometry t)) := by
    unfold normalAt patchNormal
    have hm := hmap (intervalIsometry t)
    simp only [LinearIsometryEquiv.symm_apply_apply] at hm
    by_cases hz : planeIsometry (γ t) ∈ frontier (planeIsometry '' V)
    · have hx : P.map (intervalIsometry t) ∈ frontier (planeIsometry '' V) := hm.symm ▸ hz
      rw [dite_eq_left hz, dite_eq_left hx]
      exact congrArg (fun p : frontier (planeIsometry '' V) =>
        planeIsometry.symm (outwardNormal hV p)) (Subtype.ext hm.symm)
    · have hx : P.map (intervalIsometry t) ∉ frontier (planeIsometry '' V) :=
        fun hx => hz (hm ▸ hx)
      rw [dite_eq_right hz, dite_eq_right hx]
  simp only [literalIntegrand, arcIntegrand, hmap,
    LinearIsometryEquiv.symm_apply_apply, hnormal]

/-- Once the genuine geometric display and its frames have been constructed,
its Green theorem is the supplied literal scalar interval identity. -/
lemma literal_scalar_green (V O : Set ℂ)
    (hV : IsClassicalRegularDomain (planeIsometry '' V))
    (hO : IsOpen O) (hVO : closure V ⊆ O)
    (B : BoundaryDisplay hV (planeIsometry '' O))
    (γ : Fin B.count → ℝ → ℂ) (a b : Fin B.count → ℝ)
    (hab : ∀ i, a i ≤ b i)
    (hregion : ∀ i, (B.patch i).region = intervalIsometry '' Icc (a i) (b i))
    (hmap : ∀ i x, (B.patch i).map x = planeIsometry (γ i (intervalIsometry.symm x)))
    (hframe : ∀ i x, x ∈ (B.patch i).region →
      ‖patchNormal hV (B.patch i) x‖ = 1 ∧
      (∀ j, inner ℝ (patchNormal hV (B.patch i) x)
        (fderiv ℝ (B.patch i).map x (standardBasis 1 j)) = 0) ∧
      0 < (B.sign i).val * omega 2 (Fin.cons (patchNormal hV (B.patch i) x)
        (fun j => fderiv ℝ (B.patch i).map x (standardBasis 1 j))))
    (u v : ℂ → ℝ) (hu : ContDiffOn ℝ 2 u O) (hv : ContDiffOn ℝ 2 v O)
    (hLu : ∀ z ∈ V, coordinateLaplacian u z = 0)
    (hLv : ∀ z ∈ V, coordinateLaplacian v z = 0) :
    (∀ i, IntervalIntegrable (literalIntegrand hV (γ i) u v)
      MeasureTheory.volume (a i) (b i)) ∧
      (∑ i, ∫ t in a i..b i, literalIntegrand hV (γ i) u v t) = 0 := by
  have hi := complex_boundary_integrable V O hV hO hVO u v hu hv
    B a b hab hregion hframe
  have hs := (harmonic_boundary_display V O hV hO hVO u v hu hv hLu hLv
    B a b hab hregion hframe).1
  constructor
  · intro i
    rw [literal_integrand_eq_arcIntegrand hV (B.patch i) (γ i) (hmap i) u v]
    exact hi i
  · simpa only [literal_integrand_eq_arcIntegrand hV (B.patch _) (γ _) (hmap _) u v,
      arcFlux] using hs

end D12Complex.ParametrizedBoundaryDisplay

namespace D12Complex.ParametrizedBoundaryDisplay
lemma finite_curve_seams {V : Set ℂ} {m : ℕ}
    (γ : Fin m → ℝ → ℂ) (a b : Fin m → ℝ)
    {O : Set (E 2)} (P : Fin m → Patch 1 O)
    (hregion : ∀ i, (P i).region = intervalIsometry '' Icc (a i) (b i))
    (hmap : ∀ i x, (P i).map x = planeIsometry (γ i (intervalIsometry.symm x)))
    (hinj : ∀ i, InjOn (γ i) (Ioo (a i) (b i)))
    (hdis : ∀ i j, i ≠ j →
      Disjoint (γ i '' Ioo (a i) (b i)) (γ j '' Ioo (a j) (b j)))
    (hcover : frontier V = ⋃ i, γ i '' Icc (a i) (b i)) :
    ∃ S : Seams 2,
      (∀ j, S.dim j = 0) ∧
      (∀ j x, x ∈ (P j).region → ∀ y, y ∈ (P j).region →
        x ≠ y → (P j).map x = (P j).map y → (P j).map x ∈ S.carrier) ∧
      (∀ i j, i ≠ j → ((P i).map '' (P i).region) ∩
        ((P j).map '' (P j).region) ⊆ S.carrier) ∧
      planeIsometry '' frontier V ⊆ (⋃ j, (P j).map '' (P j).region) ∪ S.carrier := by
  let endpoints : Fin m × Bool → E 2 := fun p =>
    planeIsometry (γ p.1 (if p.2 then b p.1 else a p.1))
  let S := pointSeams endpoints
  have hA (i : Fin m) : planeIsometry (γ i (a i)) ∈ S.carrier := by
    rw [show S.carrier = range endpoints from pointSeams_carrier endpoints]
    exact ⟨(i, false), rfl⟩
  have hB (i : Fin m) : planeIsometry (γ i (b i)) ∈ S.carrier := by
    rw [show S.carrier = range endpoints from pointSeams_carrier endpoints]
    exact ⟨(i, true), rfl⟩
  refine ⟨S, fun _ => rfl, ?_, ?_, ?_⟩
  · intro i x hx y hy hne he
    rw [hregion i] at hx hy
    obtain ⟨t, ht, rfl⟩ := hx
    obtain ⟨s, hs, rfl⟩ := hy
    have hts : t ≠ s := fun h => hne (congrArg intervalIsometry h)
    have he' : γ i t = γ i s := by
      apply planeIsometry.injective
      simpa only [hmap, intervalIsometry.symm_apply_apply] using he
    have h := repeated_value_mem_endpoints (γ i) (a i) (b i) t s (hinj i) ht hs hts he'
    rw [hmap]
    simp only [intervalIsometry.symm_apply_apply]
    rcases (show γ i t = γ i (a i) ∨ γ i t = γ i (b i) by simpa using h) with h | h
    · simpa only [h] using hA i
    · simpa only [h] using hB i
  · intro i j hij z hz
    obtain ⟨⟨x, hx, hxz⟩, ⟨y, hy, hyz⟩⟩ := hz
    rw [hregion i] at hx
    rw [hregion j] at hy
    obtain ⟨t, ht, rfl⟩ := hx
    obtain ⟨s, hs, rfl⟩ := hy
    have he : γ i t = γ j s := by
      apply planeIsometry.injective
      simpa only [hmap, intervalIsometry.symm_apply_apply] using hxz.trans hyz.symm
    have h := common_value_mem_endpoints γ a b i j hij (hdis i j hij) t s ht hs he
    have hzij : z = planeIsometry (γ i t) := by
      simpa only [hmap, intervalIsometry.symm_apply_apply] using hxz.symm
    rw [hzij]
    rcases (show γ i t = γ i (a i) ∨ γ i t = γ i (b i) ∨
        γ i t = γ j (a j) ∨ γ i t = γ j (b j) by simpa using h) with h | h | h | h
    · simpa only [h] using hA i
    · simpa only [h] using hB i
    · simpa only [h] using hA j
    · simpa only [h] using hB j
  · rintro z ⟨w, hw, rfl⟩
    rw [hcover] at hw
    obtain ⟨i, t, ht, rfl⟩ := mem_iUnion.mp hw
    apply Or.inl
    apply mem_iUnion.mpr
    refine ⟨i, intervalIsometry t, ?_, ?_⟩
    · rw [hregion]
      exact mem_image_of_mem _ ht
    · simp only [hmap, intervalIsometry.symm_apply_apply]

end D12Complex.ParametrizedBoundaryDisplay

namespace D12Complex.ParametrizedBoundaryDisplay
open Specs.D04.C12.RegularDomainRiemannManifoldBridge.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.Model
open Specs.D04.C14.OutwardFirstBoundaryOrientation.Model

lemma continuousOn_normalAt_comp {V : Set ℂ}
    (hV : IsClassicalRegularDomain (planeIsometry '' V))
    {S : Set ℝ} (γ : ℝ → ℂ) (hγ : ContinuousOn γ S)
    (hfront : ∀ t ∈ S, planeIsometry (γ t) ∈ frontier (planeIsometry '' V)) :
    ContinuousOn (fun t => normalAt hV (γ t)) S := by
  obtain ⟨o, ho, hK, hM, hb, hJD, hJK, hn, hdef, hdata⟩ :=
    D04.RegularDomainBridge.regular_domain_interface hV
  let ν : intrinsicBoundary 1 2 (closure (planeIsometry '' V)) → E 2 :=
    fun x => outwardNormal hV ⟨x, hb ▸ x.property⟩
  have hν (x : intrinsicBoundary 1 2 (closure (planeIsometry '' V))) :
      IsOutwardUnitConormal 1 1 (closure (planeIsometry '' V)) x (ν x) :=
    hn ⟨x, hb ▸ x.property⟩
  have heν : ν = D04BoundaryOrientation.outwardConormal hM := by
    funext x
    exact (D04BoundaryOrientation.conormal_exists_unique hM x x.property).unique
      (hν x) (D04BoundaryOrientation.outwardConormal_spec hM x)
  have hcν : Continuous ν := heν ▸ D04BoundaryOrientation.outwardConormal_continuous hM
  let curve : S → intrinsicBoundary 1 2 (closure (planeIsometry '' V)) :=
    fun t => ⟨planeIsometry (γ t), hb.symm ▸ hfront t t.property⟩
  have hcurve : Continuous curve :=
    (planeIsometry.continuous.comp (continuousOn_iff_continuous_domRestrict.mp hγ)).subtype_mk _
  apply continuousOn_iff_continuous_domRestrict.mpr
  have he : (fun t : S => normalAt hV (γ t)) =
      fun t => planeIsometry.symm (ν (curve t)) := by
    funext t
    rw [normalAt_eq_actual hV (γ t) (hfront t t.property)]
  change Continuous (fun t : S => normalAt hV (γ t))
  rw [he]
  exact planeIsometry.symm.continuous.comp (hcν.comp hcurve)

lemma connected_interval_sign {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Icc a b)) (hn : ∀ t ∈ Icc a b, f t ≠ 0) :
    ∃ s : PointSign, ∀ t ∈ Icc a b, Real.sign (f t) = s.val := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hs : Real.sign (f a) = 1 ∨ Real.sign (f a) = -1 := by
    rcases lt_or_gt_of_ne (hn a ha) with h | h
    · exact Or.inr (Real.sign_of_neg h)
    · exact Or.inl (Real.sign_of_pos h)
  letI : PreconnectedSpace (Icc a b) := Subtype.preconnectedSpace isPreconnected_Icc
  have hlc := D04BoundaryOrientation.sign_locally_constant (fun t : Icc a b => f t)
    (continuousOn_iff_continuous_domRestrict.mp hf) (fun t => hn t t.property)
  refine ⟨⟨Real.sign (f a), hs⟩, ?_⟩
  intro t ht
  exact hlc.apply_eq_of_preconnectedSpace ⟨t, ht⟩ ⟨a, ha⟩

lemma continuousOn_omega_cons {S : Set ℝ} (N T : ℝ → E 2)
    (hN : ContinuousOn N S) (hT : ContinuousOn T S) :
    ContinuousOn (fun t => omega 2 (Fin.cons (N t) (fun _ : Fin 1 => T t))) S := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  change Continuous (fun t : S =>
    ((standardBasis 2).toMatrix (Fin.cons (N t) (fun _ : Fin 1 => T t))).det)
  apply Continuous.matrix_det
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun t : S => (standardBasis 2).coord i
    ((Fin.cons (N t) (fun _ : Fin 1 => T t) : Fin 2 → E 2) j))
  have hcoord := ((standardBasis 2).coord i).continuous_of_finiteDimensional
  cases j using Fin.cases with
  | zero =>
    simpa only [Fin.cons_zero, Function.comp_def, Set.domRestrict_apply] using
      hcoord.comp (continuousOn_iff_continuous_domRestrict.mp hN)
  | succ j =>
    simpa only [Fin.cons_succ, Function.comp_def, Set.domRestrict_apply] using
      hcoord.comp (continuousOn_iff_continuous_domRestrict.mp hT)

lemma continuousOn_normal_determinant {V : Set ℂ}
    (hV : IsClassicalRegularDomain (planeIsometry '' V))
    {S T : Set ℝ} (γ : ℝ → ℂ) (hT : IsOpen T) (hST : S ⊆ T)
    (hγ : ContDiffOn ℝ 1 γ T)
    (hfront : ∀ t ∈ S, planeIsometry (γ t) ∈ frontier (planeIsometry '' V)) :
    ContinuousOn (fun t => omega 2
      (Fin.cons (planeIsometry (normalAt hV (γ t)))
        (fun _ : Fin 1 => planeIsometry (deriv γ t)))) S := by
  apply continuousOn_omega_cons
  · exact planeIsometry.continuous.comp_continuousOn
      (continuousOn_normalAt_comp hV γ (hγ.continuousOn.mono hST) hfront)
  · exact planeIsometry.continuous.comp_continuousOn
      ((hγ.continuousOn_deriv_of_isOpen hT le_rfl).mono hST)

end D12Complex.ParametrizedBoundaryDisplay

namespace D12Complex.ParametrizedBoundaryDisplay
/- Paste in namespace D12Complex.ParametrizedBoundaryDisplay after the local
curve regular-piece theorem. `hpiece` is the already proved per-curve lemma;
the final target must instantiate this helper with that lemma. -/

open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.OrientationsAndChartSigns.Model
open Specs.D04.C14.OutwardFirstBoundaryOrientation.Model
open Specs.D04.C12.RegularDomainRiemannManifoldBridge.Model
open Specs.D04.C15.GeneralizedStokes.Model
open Specs.D04.C15.FiniteManifoldBoundaryAssembly.Model

lemma boundary_display_from_piece_construction
    (V O : Set ℂ) (hD : IsClassicalRegularDomain (planeIsometry '' V))
    (hO : IsOpen O) (hVO : closure V ⊆ O)
    (m : ℕ) (γ : Fin m → ℝ → ℂ) (a b : Fin m → ℝ) (T : Fin m → Set ℝ)
    (H : RegularBoundaryCurves V m γ a b T)
    (hpiece : ∀ (o : PositiveManifoldOrientation 1 2 (closure (planeIsometry '' V)))
      (ho : IsAmbientOrientation o)
      (hb : intrinsicBoundary 1 2 (closure (planeIsometry '' V)) =
        frontier (planeIsometry '' V))
      (bO : PositiveManifoldOrientation 1 1
        (intrinsicBoundary 1 2 (closure (planeIsometry '' V))))
      (hout : OutwardFirst 1 o bO) (i : Fin m)
      (P : Patch 1 (planeIsometry '' O)),
      P.region = intervalIsometry '' Icc (a i) (b i) →
      (∀ x, P.map x = planeIsometry (γ i (intervalIsometry.symm x))) →
      ∃ s : PointSign, RegularPiece bO P s ∧ PatchFrame hD P s) :
    ∃ (B : BoundaryDisplay hD (planeIsometry '' O)) (hc : B.count = m),
      (∀ i, (B.patch (Fin.cast hc.symm i)).region = intervalIsometry '' Icc (a i) (b i)) ∧
      (∀ i x, (B.patch (Fin.cast hc.symm i)).map x =
        planeIsometry (γ i (intervalIsometry.symm x))) ∧
      (∀ i, (B.patch (Fin.cast hc.symm i)).domain ⊆ intervalIsometry '' T i) ∧
      (∀ j, PatchFrame hD (B.patch j) (B.sign j)) ∧
      (∀ j, B.seams.dim j = 0) := by
  classical
  obtain ⟨o, ho, hK, hM, hb, hJD, hJK, hn, hdef, hrest⟩ :=
    D04.RegularDomainBridge.regular_domain_interface hD
  obtain ⟨bO, hout⟩ := D04Stokes.outwardFirst_exists (d := 1) o
  have hpatch (i : Fin m) : ∃ P : Patch 1 (planeIsometry '' O),
      P.region = intervalIsometry '' Icc (a i) (b i) ∧
      (∀ x, P.map x = planeIsometry (γ i (intervalIsometry.symm x))) ∧
      P.domain ⊆ intervalIsometry '' T i := by
    apply interval_patch_exists O hO (γ i) (a i) (b i) (H.ordered i).le
      (T i) (H.params_open i) (H.params_contain i) (H.regular i)
    intro t ht
    apply hVO
    apply frontier_subset_closure
    rw [H.cover]
    exact mem_iUnion.mpr ⟨i, t, ht, rfl⟩
  choose P hregion hmap hdomain using hpatch
  have hp (i : Fin m) : ∃ s : PointSign, RegularPiece bO (P i) s ∧ PatchFrame hD (P i) s :=
    hpiece o ho hb bO hout i (P i) (hregion i) (hmap i)
  choose s hregular hframe using hp
  obtain ⟨S, hdim, hself, hinter, hcover⟩ :=
    finite_curve_seams γ a b P hregion hmap H.injective H.disjoint H.cover
  let B : BoundaryDisplay hD (planeIsometry '' O) := {
    orientation := o
    ambient := ho
    boundary_eq := hb
    boundaryOrientation := bO
    outward := hout
    count := m
    patch := P
    sign := s
    regular := hregular
    seams := S
    seam_dimension := fun i => by rw [hdim i]; norm_num
    self_intersections := hself
    intersections := hinter
    cover := by
      rw [hb, D12Complex.ComplexGreenBridge.frontier_image]
      exact hcover }
  exact ⟨B, rfl, hregion, hmap, hdomain, hframe, hdim⟩

end D12Complex.ParametrizedBoundaryDisplay

noncomputable section
set_option maxHeartbeats 800000
open Set Function Filter Topology
open scoped RealInnerProductSpace ContDiff
namespace D12Complex.ParametrizedBoundaryDisplay
open D12Complex.ComplexGreenBridge
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C12.ClassicalRegularDomains.Model
open Specs.D04.C12.RegularDomainRiemannManifoldBridge.Model
open Specs.D04.C13.OrientedEuclideanDictionary.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.Model
open Specs.D04.C14.ChartIndependentTangentSpaces.Model
open Specs.D04.C14.OrientationsAndChartSigns.Model
open Specs.D04.C14.OutwardFirstBoundaryOrientation.Model
open Specs.D04.C15.GeneralizedStokes.Model
open Specs.D04.C15.FiniteGeometricPatchIntegrals.Model
open Specs.D04.C15.FiniteManifoldBoundaryAssembly.Model

lemma sign_eq_of_signed_pos {x : ℝ} (s : PointSign) (h : 0 < s.val * x) :
    Real.sign x = s.val := by
  rcases s.property with hs | hs
  · rw [hs] at h ⊢
    exact Real.sign_of_pos (by simpa using h)
  · rw [hs] at h ⊢
    exact Real.sign_of_neg (by linarith)

lemma interval_patch_normal {V : Set ℂ} {O : Set (E 2)}
    (hD : IsClassicalRegularDomain (planeIsometry '' V)) (P : Patch 1 O)
    (γ : ℝ → ℂ) (hmap : ∀ x, P.map x = planeIsometry (γ (intervalIsometry.symm x)))
    (t : ℝ) :
    patchNormal hD P (intervalIsometry t) = planeIsometry (normalAt hD (γ t)) := by
  classical
  unfold patchNormal normalAt
  simp only [LinearIsometryEquiv.apply_symm_apply, hmap,
    LinearIsometryEquiv.symm_apply_apply]

lemma interval_patch_column {O : Set (E 2)} (P : Patch 1 O)
    (γ : ℝ → ℂ) (hmap : ∀ x, P.map x = planeIsometry (γ (intervalIsometry.symm x)))
    {t : ℝ} (hγ : DifferentiableAt ℝ γ t) (i : Fin 1) :
    fderiv ℝ P.map (intervalIsometry t) (standardBasis 1 i) = planeIsometry (deriv γ t) := by
  have hm : P.map = fun x => planeIsometry (γ (intervalIsometry.symm x)) := funext hmap
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  rw [hm]
  exact real_curve_column γ hγ

lemma local_chart_patch_frame {V : Set ℂ} {O : Set (E 2)}
    (hD : IsClassicalRegularDomain (planeIsometry '' V))
    (o : PositiveManifoldOrientation 1 2 (closure (planeIsometry '' V)))
    (ho : IsAmbientOrientation o)
    (bO : PositiveManifoldOrientation 1 1 (intrinsicBoundary 1 2 (closure (planeIsometry '' V))))
    (hout : OutwardFirst 1 o bO)
    (hb : intrinsicBoundary 1 2 (closure (planeIsometry '' V)) = frontier (planeIsometry '' V))
    (P : Patch 1 O) (a b : ℝ) (hab : a < b)
    (hreg : P.region = intervalIsometry '' Icc a b)
    (u : E 1) (hu : u ∈ P.region)
    (c : EmbeddedChart 1 1 2 (intrinsicBoundary 1 2 (closure (planeIsometry '' V))))
    (U : Set (E 1)) (hU : IsOpen U) (huU : u ∈ U)
    (hc : closure P.region ∩ U ⊆ c.source)
    (heq : EqOn P.map c.toFun (closure P.region ∩ U))
    (s : PointSign) (hs : ∀ v : c.source, chartSign bO.atPoint c v v.property = s.val) :
    ‖patchNormal hD P u‖ = 1 ∧
      (∀ i, inner ℝ (patchNormal hD P u) (fderiv ℝ P.map u (standardBasis 1 i)) = 0) ∧
      0 < s.val * omega 2 (Fin.cons (patchNormal hD P u)
        (fun i => fderiv ℝ P.map u (standardBasis 1 i))) := by
  let ν : intrinsicBoundary 1 2 (closure (planeIsometry '' V)) → E 2 :=
    fun x => outwardNormal hD ⟨x, hb ▸ x.property⟩
  have hν (x : intrinsicBoundary 1 2 (closure (planeIsometry '' V))) :
      IsOutwardUnitConormal 1 1 (closure (planeIsometry '' V)) x (ν x) :=
    D04.RegularDomainGeometry.outward_normal_conormal hD ⟨x,hb ▸ x.property⟩
  have hxu : u ∈ closure P.region ∩ U := ⟨subset_closure hu,huU⟩
  have hcu := hc hxu
  have hder : chartDifferential c u = fderiv ℝ P.map u := by
    apply chartDifferential_eq_fderiv_on_interval c hab (hreg ▸ hu) hU huU
    · intro v hv
      exact hc ⟨subset_closure (hreg.symm ▸ hv.1),hv.2⟩
    · intro v hv
      exact heq ⟨subset_closure (hreg.symm ▸ hv.1),hv.2⟩
    · exact (P.regular.differentiableOn (by norm_num)).differentiableAt
        (P.open_domain.mem_nhds (P.contains (subset_closure hu)))
  have hnormal : patchNormal hD P u = ν ⟨c.toFun u,(c.map_source hcu).1⟩ := by
    have hf : P.map u ∈ frontier (planeIsometry '' V) :=
      hb ▸ ((heq hxu).symm ▸ (c.map_source hcu).1)
    unfold patchNormal
    rw [dite_eq_left hf]
    exact congrArg (outwardNormal hD) (Subtype.ext (heq hxu))
  have hfr := chart_outward_frame o ho bO hout ν hν c u hcu
  rw [hs ⟨u,hcu⟩,hder,← hnormal] at hfr
  exact hfr

lemma global_sign_regular_piece {V : Set ℂ} {O : Set (E 2)}
    (hD : IsClassicalRegularDomain (planeIsometry '' V))
    (o : PositiveManifoldOrientation 1 2 (closure (planeIsometry '' V)))
    (ho : IsAmbientOrientation o)
    (bO : PositiveManifoldOrientation 1 1 (intrinsicBoundary 1 2 (closure (planeIsometry '' V))))
    (hout : OutwardFirst 1 o bO)
    (hb : intrinsicBoundary 1 2 (closure (planeIsometry '' V)) = frontier (planeIsometry '' V))
    (P : Patch 1 O) (a b : ℝ) (hab : a < b)
    (hreg : P.region = intervalIsometry '' Icc a b)
    (γ : ℝ → ℂ) (hmap : ∀ x, P.map x = planeIsometry (γ (intervalIsometry.symm x)))
    (T : Set ℝ) (hT : IsOpen T) (hI : Icc a b ⊆ T) (hγ : ContDiffOn ℝ 1 γ T)
    (hfront : ∀ t ∈ Icc a b, planeIsometry (γ t) ∈ frontier (planeIsometry '' V))
    (hlocal : LocalRegularExtension V γ a b) :
    ∃ s : PointSign, RegularPiece bO P s ∧ PatchFrame hD P s := by
  let d : ℝ → ℝ := fun t => omega 2 (Fin.cons (planeIsometry (normalAt hD (γ t)))
    (fun _ : Fin 1 => planeIsometry (deriv γ t)))
  have hdiff (t : ℝ) (ht : t ∈ Icc a b) : DifferentiableAt ℝ γ t :=
    (hγ.differentiableOn (by norm_num)).differentiableAt (hT.mem_nhds (hI ht))
  have hlocal_data (t : ℝ) (ht : t ∈ Icc a b) :
      ∃ (U : Set (E 1)) (c : EmbeddedChart 1 1 2
          (intrinsicBoundary 1 2 (closure (planeIsometry '' V)))) (s : PointSign),
        IsOpen U ∧ intervalIsometry t ∈ U ∧
        closure P.region ∩ U ⊆ c.source ∧ EqOn P.map c.toFun (closure P.region ∩ U) ∧
        (∀ v : c.source, chartSign bO.atPoint c v v.property = s.val) ∧
        (‖patchNormal hD P (intervalIsometry t)‖ = 1 ∧
          (∀ i, inner ℝ (patchNormal hD P (intervalIsometry t))
            (fderiv ℝ P.map (intervalIsometry t) (standardBasis 1 i)) = 0) ∧
          0 < s.val * omega 2 (Fin.cons (patchNormal hD P (intervalIsometry t))
            (fun i => fderiv ℝ P.map (intervalIsometry t) (standardBasis 1 i)))) ∧
        0 < s.val * d t ∧ Real.sign (d t) = s.val := by
    obtain ⟨U,c,s,hU,htU,hcs,heq,hsg⟩ := local_regular_chart hlocal
      (hb.trans (frontier_image V)) bO t ht
    have hcs' : closure P.region ∩ U ⊆ c.source := by simpa only [hreg] using hcs
    have heq' : EqOn P.map c.toFun (closure P.region ∩ U) := by
      intro x hx
      exact (hmap x).trans (heq (by simpa only [hreg] using hx))
    have hut : intervalIsometry t ∈ P.region := hreg ▸ mem_image_of_mem _ ht
    have hfr := local_chart_patch_frame hD o ho bO hout hb P a b hab hreg
      (intervalIsometry t) hut c U hU htU hcs' heq' s hsg
    have hdet : omega 2 (Fin.cons (patchNormal hD P (intervalIsometry t))
        (fun i => fderiv ℝ P.map (intervalIsometry t) (standardBasis 1 i))) = d t := by
      simp only [d, interval_patch_normal hD P γ hmap t,
        interval_patch_column P γ hmap (hdiff t ht)]
    have hp : 0 < s.val * d t := by
      rw [← hdet]
      exact hfr.2.2
    exact ⟨U,c,s,hU,htU,hcs',heq',hsg,hfr,hp,sign_eq_of_signed_pos s hp⟩
  have hd : ContinuousOn d (Icc a b) :=
    continuousOn_normal_determinant hD γ hT hI hγ hfront
  have hn : ∀ t ∈ Icc a b, d t ≠ 0 := by
    intro t ht
    obtain ⟨U,c,s,hU,htU,hcs,heq,hsg,hfr,hp,hss⟩ := hlocal_data t ht
    intro hz
    simpa only [hz,mul_zero,lt_self_iff_false] using hp
  obtain ⟨s,hs⟩ := connected_interval_sign hab.le d hd hn
  refine ⟨s, ?_, ?_⟩
  · intro u hu
    have hclosed := (interval_region_closed a b).closure_eq
    rw [hreg,hclosed] at hu
    obtain ⟨t,ht,rfl⟩ := hu
    obtain ⟨U,c,s',hU,htU,hcs,heq,hsg,hfr,hp,hss⟩ := hlocal_data t ht
    have hse : s'.val = s.val := hss.symm.trans (hs t ht)
    exact ⟨U,c,hU,htU,hcs,heq,fun v => (hsg v).trans hse⟩
  · intro u hu
    rw [hreg] at hu
    obtain ⟨t,ht,rfl⟩ := hu
    obtain ⟨U,c,s',hU,htU,hcs,heq,hsg,hfr,hp,hss⟩ := hlocal_data t ht
    have hse : s'.val = s.val := hss.symm.trans (hs t ht)
    simpa only [hse] using hfr

end D12Complex.ParametrizedBoundaryDisplay

namespace D12Complex.ParametrizedBoundaryDisplay

/-- The supplied finite interval curves construct the complete actual D04
boundary display, including regular endpoint charts and derived constant signs. -/
theorem boundary_display :
    Specs.D12Complex.Ch14.ParametrizedBoundaryDisplay.boundary_display_type := by
  intro V O hD hO hVO m γ a b T H
  apply boundary_display_from_piece_construction V O hD hO hVO m γ a b T H
  intro o ho hb bO hout i P hregion hmap
  apply global_sign_regular_piece hD o ho bO hout hb P (a i) (b i) (H.ordered i)
    hregion (γ i) hmap (T i) (H.params_open i) (H.params_contain i) (H.regular i)
    ?_ (H.local_extension i)
  intro t ht
  rw [frontier_image V]
  apply mem_image_of_mem
  rw [H.cover]
  exact mem_iUnion.mpr ⟨i, t, ht, rfl⟩

/-- Scalar harmonic flux for the original supplied arrays, with the actual
outward normal and the actual speed of each global curve. -/
theorem parametrized_harmonic_green :
    Specs.D12Complex.Ch14.ParametrizedBoundaryDisplay.parametrized_harmonic_green_type := by
  intro V O hD hO hVO m γ a b T H u v hu hv hLu hLv
  obtain ⟨B, hc, hregion, hmap, hdomain, hframe, hseams⟩ :=
    boundary_display V O hD hO hVO m γ a b T H
  subst m
  exact literal_scalar_green V O hD hO hVO B γ a b (fun i => (H.ordered i).le)
    hregion hmap hframe u v hu hv hLu hLv

namespace Definitions
abbrev LocalRegularExtension :
    Specs.D12Complex.Ch14.ParametrizedBoundaryDisplay.LocalRegularExtension_type :=
  @_root_.D12Complex.ParametrizedBoundaryDisplay.LocalRegularExtension
abbrev RegularBoundaryCurves :
    Specs.D12Complex.Ch14.ParametrizedBoundaryDisplay.RegularBoundaryCurves_type :=
  @_root_.D12Complex.ParametrizedBoundaryDisplay.RegularBoundaryCurves
abbrev PatchFrame : Specs.D12Complex.Ch14.ParametrizedBoundaryDisplay.PatchFrame_type :=
  @_root_.D12Complex.ParametrizedBoundaryDisplay.PatchFrame
abbrev normalAt : Specs.D12Complex.Ch14.ParametrizedBoundaryDisplay.normalAt_type :=
  @_root_.D12Complex.ParametrizedBoundaryDisplay.normalAt
abbrev literalIntegrand : Specs.D12Complex.Ch14.ParametrizedBoundaryDisplay.literalIntegrand_type :=
  @_root_.D12Complex.ParametrizedBoundaryDisplay.literalIntegrand
end Definitions

end D12Complex.ParametrizedBoundaryDisplay
