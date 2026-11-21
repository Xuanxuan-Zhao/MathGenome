import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C12.IntegrationByPartsAndGreenIdentities
import MathGenome.Internal.MultivariableAnalysis.D04.C12.GaussDivergenceTheorem
import MathGenome.Internal.MultivariableAnalysis.D04.C11.VectorDifferentialIdentities

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable
open Set Filter Topology
open scoped ContDiff BigOperators
namespace D04.GreenIdentities
open Specs.D04.C12.IntegrationByPartsAndGreenIdentities
open Specs.D04.C12.IntegrationByPartsAndGreenIdentities.Model
open Specs.D04.C12.GaussDivergenceTheorem.Model
open Specs.D04.C12.ClassicalRegularDomains.Model
open Specs.D04.C06.JordanRegions.Model
open Specs.D04.C15.DirectedSubstitution.Model
open Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model

-- Reuse the canonical operators; the value declarations introduce no new operators.
def boundaryIntegral : boundaryIntegralType := @boundaryIntegralValue
def normalDerivative : normalDerivativeType := @normalDerivativeValue

local notation "scalarGradient" => Specs.D04.C02.DerivativeBridge.Model.scalarGradient
local notation "scalarPartialDerivative" => Specs.D04.C02.DerivativeBridge.Model.scalarPartialDerivative
local notation "divergence" => Specs.D04.C11.EuclideanVectorOperators.Model.divergence
local notation "laplacian" => Specs.D04.C11.EuclideanVectorOperators.Model.laplacian
local notation "normalDerivative" => Specs.D04.C12.IntegrationByPartsAndGreenIdentities.Model.normalDerivative
local notation "boundaryIntegral" => Specs.D04.C12.IntegrationByPartsAndGreenIdentities.Model.boundaryIntegral

lemma density_value_unique {d n : ℕ} {M : Set (E n)} {ρ : M → ℝ} {I J : ℝ}
    (hI : HasDensityIntegral (d := d) ρ I) (hJ : HasDensityIntegral (d := d) ρ J) : I = J := by
  obtain ⟨P⟩ := hI.2.2.1
  exact (hI.2.2.2 P).2.symm.trans (hJ.2.2.2 P).2

lemma boundaryIntegral_eq {d : ℕ} {D : Set (E (d+1))} {ρ : frontier D → ℝ} {I : ℝ}
    (hi : HasDensityIntegral (d := d) ρ I) : boundaryIntegral ρ = I := by
  change (if h : ∃ J, HasDensityIntegral (d := d) ρ J then h.choose else 0) = I
  erw [dite_eq_left ⟨I, hi⟩]
  exact density_value_unique (Exists.choose_spec _) hi

lemma hasBoundaryIntegral {d : ℕ} {D : Set (E (d+1))} {ρ : frontier D → ℝ} {I : ℝ}
    (hi : HasDensityIntegral (d := d) ρ I) :
    HasDensityIntegral (d := d) ρ (boundaryIntegral ρ) := by
  erw [boundaryIntegral_eq hi]
  exact hi



/-- Continuous functions on the compact closure have the original region
Riemann integral. This is used for each summand before invoking linearity. -/
lemma region_integrable {d : ℕ} {D U : Set (E (d+1))}
    (hD : IsClassicalRegularDomain D) (hDU : closure D ⊆ U)
    {f : E (d+1) → ℝ} (hf : ContinuousOn f U) :
    RegionIntegrable (fun x : D => f x) :=
  D04.JordanRegions.integrable_continuous_on_closure (Nat.succ_pos d)
    (D04.RegularDomainGeometry.jordan_domain_and_closure hD).1
    (fun x => f x) (hf.comp_continuous continuous_subtype_val (fun x => hDU x.property))

lemma region_add_value {n : ℕ} {D : Set (E n)} (hb : Bornology.IsBounded D)
    (f g : D → ℝ) (hf : RegionIntegrable f) (hg : RegionIntegrable g)
    (hs : RegionIntegrable (fun x => f x + g x)) :
    regionIntegral (fun x => f x + g x) = regionIntegral f + regionIntegral g := by
  have h := D04.RegularDomainBridge.region_integral_sum hb
    ![f, g] (by intro i; fin_cases i; exact hf; exact hg)
    (fun x => f x + g x) hs (by intro x; simp [Fin.sum_univ_two])
  simpa [Fin.sum_univ_two] using h

lemma gradient_regular {n : ℕ} {U : Set (E n)} {f : E n → ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) :
    ContDiffOn ℝ 1 (scalarGradient f) U :=
  (crOn_iff_contDiffOn 1 U _ hU).mp
    (gradient_crOn U f hU ((crOn_iff_contDiffOn 2 U f hU).mpr hf))

lemma gradient_continuous {n : ℕ} {U : Set (E n)} {f : E n → ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U) :
    ContinuousOn (scalarGradient f) U := by
  have hd := hf.continuousOn_fderiv_of_isOpen hU le_rfl
  exact (InnerProductSpace.toDual ℝ (E n)).symm.toContinuousLinearEquiv.continuous.comp_continuousOn hd

lemma partial_continuous {n : ℕ} {U : Set (E n)} {f : E n → ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U) (i : Fin n) :
    ContinuousOn (fun x => scalarPartialDerivative f x i) U := by
  have hc := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i).continuous.comp_continuousOn
    (gradient_continuous hU hf)
  exact hc.congr (fun x hx => (gradient_coordinates U f x hU
    ((crOn_iff_contDiffOn 1 U f hU).mpr hf) hx i).symm)

lemma laplacian_continuous {d : ℕ} {U : Set (E (d+1))} {f : E (d+1) → ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) : ContinuousOn (laplacian f) U :=
  D04.Gauss.divergence_continuousOn U (scalarGradient f) hU
    ((crOn_iff_contDiffOn 1 U _ hU).mpr (gradient_regular hU hf))

lemma divergence_product_basis {n : ℕ} {U : Set (E n)} {f g : E n → ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U) (hg : ContDiffOn ℝ 1 g U)
    {x : E n} (hx : x ∈ U) (i : Fin n) :
    divergence (fun y => (f y * g y) • standardBasis n i) x =
      f x * scalarPartialDerivative g x i + g x * scalarPartialDerivative f x i := by
  change D04.divergence (fun y => (f y * g y) • standardBasis n i) x = _
  have hf' := (crOn_iff_contDiffOn 1 U f hU).mpr hf
  have hg' := (crOn_iff_contDiffOn 1 U g hU).mpr hg
  erw [divergence_smul U (fun y => f y * g y) (fun _ => standardBasis n i) x hU
    ((crOn_iff_contDiffOn 1 U _ hU).mpr (hf.mul hg))
    ((crOn_iff_contDiffOn 1 U _ hU).mpr contDiffOn_const) hx]
  change inner ℝ (scalarGradient (fun y => f y * g y) x) (standardBasis n i) +
    f x * g x * divergence (fun _ : E n => standardBasis n i) x = _
  have hgrad : scalarGradient (fun y => f y * g y) x =
      f x • scalarGradient g x + g x • scalarGradient f x :=
    gradient_product U f g x hU hf' hg' hx
  have hz : divergence (fun _ : E n => standardBasis n i) x = 0 := by
    change LinearMap.trace ℝ (E n) (fderiv ℝ (fun _ : E n => standardBasis n i) x).toLinearMap = 0
    simp
  erw [hz, mul_zero, add_zero, hgrad,
    inner_add_left, real_inner_smul_left, real_inner_smul_left]
  erw [show inner ℝ (scalarGradient g x) (standardBasis n i) = scalarGradient g x i from
    EuclideanSpace.inner_basisFun_real _ _ _,
    show inner ℝ (scalarGradient f x) (standardBasis n i) = scalarGradient f x i from
    EuclideanSpace.inner_basisFun_real _ _ _,
    gradient_coordinates U g x hU hg' hx i, gradient_coordinates U f x hU hf' hx i]
  rfl

theorem integration_by_parts : integration_by_partsType := by
  intro d D hD U f g hU hDU hf hg i
  let F : E (d+1) → E (d+1) := fun x => (f x * g x) • standardBasis (d+1) i
  have hF : ContDiffOn ℝ 1 F U := (hf.mul hg).smul contDiffOn_const
  obtain ⟨hi, hb⟩ := D04.Gauss.gauss hD U F hU hDU
    ((crOn_iff_contDiffOn 1 U F hU).mpr hF)
  have hd : (fun x : D => divergence F x) = fun x : D =>
      f x * scalarPartialDerivative g x i + g x * scalarPartialDerivative f x i := by
    funext x
    exact divergence_product_basis hU hf hg (hDU (subset_closure x.property)) i
  have hn : normalFlux F (outwardNormal hD) = fun x : frontier D =>
      f x * g x * outwardNormal hD x i := by
    funext x
    change inner ℝ ((f x * g x) • standardBasis (d+1) i) (outwardNormal hD x) = _
    erw [real_inner_smul_left, real_inner_comm, EuclideanSpace.inner_basisFun_real]
  erw [hd, hn] at hb
  erw [hd] at hi
  have hi₁ := region_integrable hD hDU (hf.continuousOn.mul (partial_continuous hU hg i))
  have hi₂ := region_integrable hD hDU (hg.continuousOn.mul (partial_continuous hU hf i))
  refine ⟨hi₁, hi₂, hasBoundaryIntegral hb, ?_⟩
  have hv := boundaryIntegral_eq hb
  erw [region_add_value hD.bounded _ _ hi₁ hi₂ hi] at hv
  exact eq_sub_iff_add_eq.mpr hv.symm

lemma divergence_green {n : ℕ} {U : Set (E n)} {u v : E n → ℝ}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U) (hv : ContDiffOn ℝ 2 v U)
    {x : E n} (hx : x ∈ U) :
    divergence (fun y => u y • scalarGradient v y) x =
      u x * laplacian v x + inner ℝ (scalarGradient u x) (scalarGradient v x) := by
  change D04.divergence (fun y => u y • scalarGradient v y) x = _
  erw [divergence_smul U u (scalarGradient v) x hU
    ((crOn_iff_contDiffOn 1 U u hU).mpr (hu.of_le (by norm_num)))
    ((crOn_iff_contDiffOn 1 U _ hU).mpr (gradient_regular hU hv)) hx]
  change inner ℝ (scalarGradient u x) (scalarGradient v x) + u x * laplacian v x = _
  exact add_comm _ _

theorem first_green : first_greenType := by
  intro d D hD U u v hU hDU hu hv
  let F := fun x => u x • scalarGradient v x
  have hF : ContDiffOn ℝ 1 F U :=
    (hu.of_le (by norm_num)).smul (gradient_regular hU hv)
  obtain ⟨hi, hb⟩ := D04.Gauss.gauss hD U F hU hDU
    ((crOn_iff_contDiffOn 1 U F hU).mpr hF)
  have hd : (fun x : D => divergence F x) = fun x : D =>
      u x * laplacian v x + inner ℝ (scalarGradient u x) (scalarGradient v x) := by
    funext x
    exact divergence_green hU hu hv (hDU (subset_closure x.property))
  have hn : normalFlux F (outwardNormal hD) = fun x : frontier D =>
      u x * normalDerivative hD v x := by
    funext x
    exact real_inner_smul_left _ _ _
  erw [hd, hn] at hb
  erw [hd] at hi
  have hi₁ := region_integrable hD hDU (hu.continuousOn.mul (laplacian_continuous hU hv))
  have hi₂ := region_integrable hD hDU
    ((gradient_regular hU hu).continuousOn.inner (gradient_regular hU hv).continuousOn)
  exact ⟨hi₁, hi₂, hi, hb, (boundaryIntegral_eq hb).symm⟩

lemma divergence_sub {n : ℕ} {F G : E n → E n} {x : E n}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) :
    divergence (fun y => F y - G y) x = divergence F x - divergence G x := by
  change LinearMap.trace ℝ (E n) (fderiv ℝ (fun y => F y - G y) x).toLinearMap = _
  erw [fderiv_fun_sub hF hG]
  exact map_sub (LinearMap.trace ℝ (E n)) _ _

theorem second_green : second_greenType := by
  intro d D hD U u v hU hDU hu hv
  let F := fun x => u x • scalarGradient v x
  let G := fun x => v x • scalarGradient u x
  have hF : ContDiffOn ℝ 1 F U :=
    (hu.of_le (by norm_num)).smul (gradient_regular hU hv)
  have hG : ContDiffOn ℝ 1 G U :=
    (hv.of_le (by norm_num)).smul (gradient_regular hU hu)
  obtain ⟨hi, hb⟩ := D04.Gauss.gauss hD U (fun x => F x - G x) hU hDU
    ((crOn_iff_contDiffOn 1 U _ hU).mpr (hF.sub hG))
  have hd : (fun x : D => divergence (fun y => F y - G y) x) =
      fun x : D => u x * laplacian v x - v x * laplacian u x := by
    funext x
    have hx := hDU (subset_closure x.property)
    erw [divergence_sub ((hF.contDiffAt (hU.mem_nhds hx)).differentiableAt one_ne_zero)
      ((hG.contDiffAt (hU.mem_nhds hx)).differentiableAt one_ne_zero),
      divergence_green hU hu hv hx, divergence_green hU hv hu hx, real_inner_comm (scalarGradient v x)]
    ring
  have hn : normalFlux (fun x => F x - G x) (outwardNormal hD) =
      fun x : frontier D => u x * normalDerivative hD v x - v x * normalDerivative hD u x := by
    funext x
    change inner ℝ (u x • scalarGradient v x - v x • scalarGradient u x) _ = _
    erw [inner_sub_left, real_inner_smul_left, real_inner_smul_left]
    rfl
  erw [hd] at hi
  erw [hd, hn] at hb
  exact ⟨hi, hb, (boundaryIntegral_eq hb).symm⟩



lemma boundaryIntegral_zero {d : ℕ} {D : Set (E (d+1))}
    (ρ : frontier D → ℝ) (hρ : ∀ x, ρ x = 0) : boundaryIntegral ρ = 0 := by
  change (if h : ∃ I, HasDensityIntegral (d := d) ρ I then h.choose else 0) = 0
  split_ifs with h
  · have hi := h.choose_spec
    obtain ⟨P⟩ := hi.2.2.1
    erw [← (hi.2.2.2 P).2]
    apply Finset.sum_eq_zero
    intro i _
    apply D04.GeometricUnion.coefficient_integral_eq_zero
    intro x
    change P.weight i ((P.chart i).toFun x) *
      (ρ (chartPoint (P.chart i) x) * _) = 0
    erw [hρ, zero_mul, mul_zero]
  · rfl

lemma boundary_not_mem {n : ℕ} {D : Set (E n)} (hD : IsClassicalRegularDomain D)
    (x : frontier D) : (x : E n) ∉ D := by
  have hx := x.property.2
  simpa only [hD.isOpen.interior_eq] using hx

lemma value_zero_on_boundary {n : ℕ} {Y : Type} [Zero Y] {D : Set (E n)}
    (hD : IsClassicalRegularDomain D) {f : E n → Y} (hs : tsupport f ⊆ D)
    (x : frontier D) : f x = 0 :=
  image_eq_zero_of_notMem_tsupport (fun hx => boundary_not_mem hD x (hs hx))

lemma gradient_zero_on_boundary {n : ℕ} {D : Set (E n)}
    (hD : IsClassicalRegularDomain D) {f : E n → ℝ} (hs : tsupport f ⊆ D)
    (x : frontier D) : scalarGradient f x = 0 := by
  have he : f =ᶠ[𝓝 (x : E n)] (fun _ => 0) :=
    notMem_tsupport_iff_eventuallyEq.mp (fun hx => boundary_not_mem hD x (hs hx))
  change _root_.gradient f x = 0
  erw [he.gradient_eq]
  simp [gradient]

theorem parts_boundary_compact : parts_boundary_compactType := by
  intro d D hD f g hs i
  apply boundaryIntegral_zero
  intro x
  erw [value_zero_on_boundary hD hs x, zero_mul]

theorem flux_boundary_compact : flux_boundary_compactType := by
  intro d D hD F hs
  apply boundaryIntegral_zero
  intro x
  change inner ℝ (F x) (outwardNormal hD x) = 0
  erw [value_zero_on_boundary hD hs x, inner_zero_left]

theorem first_green_product_boundary_compact : first_green_product_boundary_compactType := by
  intro d D hD u v hs
  apply boundaryIntegral_zero
  intro x
  change u x * inner ℝ (scalarGradient v x) (outwardNormal hD x) = 0
  rw [← real_inner_smul_left, value_zero_on_boundary hD hs x, inner_zero_left]

theorem second_green_product_boundary_compact : second_green_product_boundary_compactType := by
  intro d D hD u v hs
  apply boundaryIntegral_zero
  intro x
  calc
    u x * normalDerivative hD v x - v x * normalDerivative hD u x =
        inner ℝ (u x • scalarGradient v x - v x • scalarGradient u x) (outwardNormal hD x) := by
      rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left]
      rfl
    _ = 0 := by rw [value_zero_on_boundary hD hs x, inner_zero_left]

theorem green_boundary_compact : green_boundary_compactType := by
  intro d D hD u v hs
  have hn {f : E (d+1) → ℝ} (h : tsupport f ⊆ D) (x : frontier D) :
      normalDerivative hD f x = 0 := by
    change inner ℝ (scalarGradient f x) _ = 0
    erw [gradient_zero_on_boundary hD h x, inner_zero_left]
  constructor
  · apply boundaryIntegral_zero
    intro x
    rcases hs with hs | hs
    · erw [value_zero_on_boundary hD hs x, zero_mul]
    · erw [hn hs x, mul_zero]
  · apply boundaryIntegral_zero
    intro x
    rcases hs with hs | hs
    · erw [value_zero_on_boundary hD hs x, hn hs x, zero_mul, mul_zero, sub_self]
    · erw [value_zero_on_boundary hD hs x, hn hs x, zero_mul, mul_zero, sub_self]

/-- Compact relative support has compact ambient image inside the open domain.
Taking the closure of the zero extension's support cannot add boundary points. -/
lemma zero_extension_support {n : ℕ} {D : Set (E n)} (u : E n → ℝ)
    (hk : HasCompactSupport (fun x : D => u x)) :
    HasCompactSupport (zeroExtension (fun x : D => u x)) ∧
      tsupport (zeroExtension (fun x : D => u x)) ⊆ D := by
  let K := Subtype.val '' tsupport (fun x : D => u x)
  have hK : IsCompact K := hk.image continuous_subtype_val
  have hs : tsupport (zeroExtension (fun x : D => u x)) ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_cases h : x ∈ D
    · refine ⟨⟨x, h⟩, subset_tsupport _ ?_, rfl⟩
      simpa only [Function.mem_support,
        D04.JordanRegions.zeroExtension_apply (fun x : D => u x) ⟨x, h⟩] using hx
    · exact False.elim (hx (D04.JordanRegions.zeroExtension_of_not_mem _ h))
  exact ⟨hK.of_isClosed_subset (isClosed_tsupport _) hs,
    hs.trans (by rintro x ⟨y, _, rfl⟩; exact y.property)⟩

theorem zero_extension_regular : zero_extension_regularType := by
  intro n D hD r u hu hk
  let z := zeroExtension (fun x : D => u x)
  have hs : tsupport z ⊆ D := (zero_extension_support u hk).2
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ D
  · apply (hu.contDiffAt (hD.mem_nhds hx)).congr_of_eventuallyEq
    filter_upwards [hD.mem_nhds hx] with y hy
    exact D04.JordanRegions.zeroExtension_apply (fun x : D => u x) ⟨y, hy⟩
  · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    exact notMem_tsupport_iff_eventuallyEq.mp (fun h => hx (hs h))

theorem compact_energy : compact_energyType := by
  intro d D hD u hu hk
  let z := zeroExtension (fun x : D => u x)
  have hz : ContDiff ℝ 2 z := zero_extension_regular hD.isOpen 2 u hu hk
  have hs : tsupport z ⊆ D := (zero_extension_support u hk).2
  obtain ⟨hi₁, hi₂, hi, _, hv⟩ := first_green hD univ z z isOpen_univ
    (subset_univ _) hz.contDiffOn hz.contDiffOn
  have hb := (green_boundary_compact hD z z (Or.inl hs)).1
  erw [hb, region_add_value hD.bounded _ _ hi₁ hi₂ hi] at hv
  have he : (fun x : D => inner ℝ (scalarGradient z x) (scalarGradient z x)) =
      fun x : D => ‖scalarGradient z x‖ ^ 2 := by
    funext x
    exact real_inner_self_eq_norm_sq _
  erw [he] at hi₂ hv
  exact ⟨hz, hi₁, hi₂, by linarith⟩

end D04.GreenIdentities
