import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch04.SignedCurveMultiplicity
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C12.GreenCirculationAndFlux

/-! Geometric boundary densities use the actual Jordan patches and actual
ordinary derivatives, with the canonical D04 real coordinates. There is no
comparison certificate or assumed integral identity in these objects. -/
noncomputable section
set_option autoImplicit false
set_option linter.unusedVariables false
open Set MeasureTheory
open scoped Topology BigOperators
namespace D12Complex.ManifoldBoundaryDensity
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.OrientationsAndChartSigns.Model
open Specs.D04.C14.OutwardFirstBoundaryOrientation.Model
open Specs.D04.C15.GeneralizedStokes.Model
open Specs.D04.C15.FiniteManifoldBoundaryAssembly.Model
open Specs.D04.C15.FiniteGeometricUnionIntegral.Model
open Specs.D04.C12.RegularDomainRiemannManifoldBridge.Model
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C15.FiniteGeometricPatchIntegrals.Model
open Specs.D04.C12.GreenCirculationAndFlux.Model

/-- The positive orthonormal scalar coordinate of the actual E1 parameter. -/
def scalarCoordinates : ℝ ≃ₗᵢ[ℝ] E 1 :=
  (OrthonormalBasis.singleton (Fin 1) ℝ).repr

/-- The original total representative expressed in complex coordinates. -/
def patchCurve {O : Set (E 2)} (P : Patch 1 O) : ℝ → ℂ :=
  fun t => complexCoordinates.symm (P.map (scalarCoordinates t))

/-- The original Jordan region, with no interval normalization. -/
def patchParameters {O : Set (E 2)} (P : Patch 1 O) : Set ℝ :=
  scalarCoordinates ⁻¹' P.region

/-- Actual signed unit-velocity occurrence sum over the original region. -/
def patchDensity {O : Set (E 2)} (P : Patch 1 O) : ℂ → ℂ :=
  _root_.D12Complex.SignedCurveMultiplicity.signedDensity (patchCurve P) (patchParameters P)

/-- The complex circulation integral of the original D04 patch. -/
def complexPatchIntegral {O : Set (E 2)} (P : Patch 1 O) (q : ℂ → ℂ) : ℂ :=
  (patchIntegral P (fun _ => 1)
    (circulationForm (fun x => (q (complexCoordinates.symm x)).re)
      (fun x => -(q (complexCoordinates.symm x)).im)) : ℂ) +
  Complex.I * (patchIntegral P (fun _ => 1)
    (circulationForm (fun x => (q (complexCoordinates.symm x)).im)
      (fun x => (q (complexCoordinates.symm x)).re)) : ℂ)

/-- Signed density of the supplied outer patches, retaining all coefficients. -/
def displayDensity {O : Set (E 2)} {l : ℕ}
    (P : Fin l → Patch 1 O)
    (s : Fin l → Specs.D04.C14.OrientationsAndChartSigns.Model.PointSign)
    (b : Fin l → ℤ) (z : ℂ) : ℂ :=
  ∑ t, (b t : ℂ) * ((s t).val : ℂ) * patchDensity (P t) z


/-- Exactly the regular Jordan display data of the actual D04 theorem. -/
structure RegularDisplay (O M : Set (E 2)) (o : PositiveManifoldOrientation 1 1 M) where
  count : ℕ
  patch : Fin count → Patch 1 O
  sign : Fin count → PointSign
  regular : ∀ t, RegularPiece o (patch t) (sign t)
  seams : Seams 2
  lower : ∀ i, seams.dim i < 1
  self_intersection : ∀ t u, u ∈ (patch t).region → ∀ v, v ∈ (patch t).region → u ≠ v →
    (patch t).map u = (patch t).map v → (patch t).map u ∈ seams.carrier
  intersection : ∀ t u, t ≠ u →
    ((patch t).map '' (patch t).region) ∩ ((patch u).map '' (patch u).region) ⊆ seams.carrier
  cover : M ⊆ (⋃ t, (patch t).map '' (patch t).region) ∪ seams.carrier

/-- The finite compact, ambient-positive planar manifold branch of D04 Green.
Every field concerns actual geometry or orientations. No integral equality,
cycle representation, or index value is a field. -/
structure PlanarAssembly (q l p : ℕ) (O : Set (E 2)) where
  piece : Fin q → CompactManifold 1 2 O
  ambient_positive : ∀ j, IsAmbientOrientation (piece j).orientation
  boundaryOrientation : (j : Fin q) → PositiveManifoldOrientation 1 1
    (intrinsicBoundary 1 2 (piece j).carrier)
  outward : ∀ j, OutwardFirst 1 (piece j).orientation (boundaryOrientation j)
  display : (j : Fin q) → RegularDisplay O
    (intrinsicBoundary 1 2 (piece j).carrier) (boundaryOrientation j)
  bulkSeams : AmbientSeams 2 2
  bulk_intersection : ∀ i j, i ≠ j →
    (piece i).carrier ∩ (piece j).carrier ⊆ bulkSeams.carrier
  enumerate : (Fin l ⊕ (Fin p × Bool)) ≃ ((j : Fin q) × Fin (display j).count)
  outerPatch : Fin l → Patch 1 O
  outerSign : Fin l → PointSign
  outerMultiplicity : Fin l → ℤ
  deltaOut : Fin l → ℝ
  deltaOut_sign : ∀ t, deltaOut t = 1 ∨ deltaOut t = -1
  outerReparam : (t : Fin l) → LocalReparametrization
    ((display (enumerate (Sum.inl t)).1).patch (enumerate (Sum.inl t)).2).region
    (outerPatch t).region (deltaOut t)
  outer_match : ∀ t,
    EqOn ((display (enumerate (Sum.inl t)).1).patch (enumerate (Sum.inl t)).2).map
      ((outerPatch t).map ∘ (outerReparam t).map)
      ((display (enumerate (Sum.inl t)).1).patch (enumerate (Sum.inl t)).2).region ∧
    ((display (enumerate (Sum.inl t)).1).sign (enumerate (Sum.inl t)).2).val * deltaOut t =
      (outerSign t).val ∧ outerMultiplicity t = 1
  deltaPair : Fin p → ℝ
  deltaPair_sign : ∀ i, deltaPair i = 1 ∨ deltaPair i = -1
  pairReparam : (i : Fin p) → LocalReparametrization
    ((display (enumerate (Sum.inr (i,false))).1).patch (enumerate (Sum.inr (i,false))).2).region
    ((display (enumerate (Sum.inr (i,true))).1).patch (enumerate (Sum.inr (i,true))).2).region
    (deltaPair i)
  pair_match : ∀ i,
    EqOn ((display (enumerate (Sum.inr (i,false))).1).patch (enumerate (Sum.inr (i,false))).2).map
      (((display (enumerate (Sum.inr (i,true))).1).patch (enumerate (Sum.inr (i,true))).2).map ∘
        (pairReparam i).map)
      ((display (enumerate (Sum.inr (i,false))).1).patch (enumerate (Sum.inr (i,false))).2).region ∧
    ((display (enumerate (Sum.inr (i,false))).1).sign (enumerate (Sum.inr (i,false))).2).val *
        deltaPair i = -((display (enumerate (Sum.inr (i,true))).1).sign
          (enumerate (Sum.inr (i,true))).2).val

def originalDensity {q l p : ℕ} {O : Set (E 2)} (A : PlanarAssembly q l p O) (z : ℂ) : ℂ :=
  ∑ j, ∑ t, (((A.display j).sign t).val : ℂ) * patchDensity ((A.display j).patch t) z

def outerDensity {q l p : ℕ} {O : Set (E 2)} (A : PlanarAssembly q l p O) : ℂ → ℂ :=
  displayDensity A.outerPatch A.outerSign A.outerMultiplicity

/-- Encode each actual ±1 orientation as an integer chain coefficient. -/
def pointSignInt (s : PointSign) : ℤ := if s.val = 1 then 1 else -1

def outerPatchChain {q l p : ℕ} {O : Set (E 2)} (A : PlanarAssembly q l p O) : PatchChain 1 O :=
  ∑ t, Finsupp.single (⟨A.outerPatch t, fun _ => 1, continuousOn_const⟩ : WeightedPatch 1 O)
    (A.outerMultiplicity t * pointSignInt (A.outerSign t))


/-- Geometric outer density from the ORIGINAL unpaired boundary occurrences,
with the actual signs induced by the outward-first orientations. -/
def geometricOuterDensity {q l p : ℕ} {O : Set (E 2)} (A : PlanarAssembly q l p O) (z : ℂ) : ℂ :=
  ∑ t : Fin l,
    (((A.display (A.enumerate (Sum.inl t)).1).sign (A.enumerate (Sum.inl t)).2).val : ℂ) *
      patchDensity ((A.display (A.enumerate (Sum.inl t)).1).patch (A.enumerate (Sum.inl t)).2) z

end D12Complex.ManifoldBoundaryDensity

namespace D12Complex.ManifoldBoundaryDensity
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C15.FiniteGeometricPatchIntegrals.Model
open Specs.D04.C12.GreenCirculationAndFlux.Model
/-- Full actual weighted density/integral dictionary. This is a conclusion
predicate, never a geometric input or assumed certificate. -/
def AssemblyDictionary {q l p : ℕ} {O : Set (E 2)} (A : PlanarAssembly q l p O)
    (f : ℂ → ℂ) : Prop :=
    Integrable (fun z => f z * outerDensity A z) μH[1] ∧
    (∫ z, f z * outerDensity A z ∂μH[1]) =
      ∑ j, ∑ t, (((A.display j).sign t).val : ℂ) *
        complexPatchIntegral ((A.display j).patch t) f ∧
    (∫ z, f z * outerDensity A z ∂μH[1]) =
      (∑ t, (A.outerMultiplicity t : ℂ) * ((A.outerSign t).val : ℂ) *
        complexPatchIntegral (A.outerPatch t) f) ∧
    (∫ z, f z * outerDensity A z ∂μH[1]) =
      (patchChainIntegral
        (circulationForm (fun x => (f (complexCoordinates.symm x)).re)
          (fun x => -(f (complexCoordinates.symm x)).im)) (outerPatchChain A) : ℂ) +
      Complex.I * (patchChainIntegral
        (circulationForm (fun x => (f (complexCoordinates.symm x)).im)
          (fun x => (f (complexCoordinates.symm x)).re)) (outerPatchChain A) : ℂ)

/-- The full dictionary for original geometric outer occurrences. -/
def GeometricAssemblyDictionary {q l p : ℕ} {O : Set (E 2)} (A : PlanarAssembly q l p O)
    (f : ℂ → ℂ) : Prop :=
    Integrable (fun z => f z * geometricOuterDensity A z) μH[1] ∧
    (∫ z, f z * geometricOuterDensity A z ∂μH[1]) =
      ∑ j, ∑ t, (((A.display j).sign t).val : ℂ) *
        complexPatchIntegral ((A.display j).patch t) f ∧
    (∫ z, f z * geometricOuterDensity A z ∂μH[1]) =
      (∑ t, (A.outerMultiplicity t : ℂ) * ((A.outerSign t).val : ℂ) *
        complexPatchIntegral (A.outerPatch t) f) ∧
    (∫ z, f z * geometricOuterDensity A z ∂μH[1]) =
      (patchChainIntegral
        (circulationForm (fun x => (f (complexCoordinates.symm x)).re)
          (fun x => -(f (complexCoordinates.symm x)).im)) (outerPatchChain A) : ℂ) +
      Complex.I * (patchChainIntegral
        (circulationForm (fun x => (f (complexCoordinates.symm x)).im)
          (fun x => (f (complexCoordinates.symm x)).re)) (outerPatchChain A) : ℂ)

end D12Complex.ManifoldBoundaryDensity

namespace Specs.D12Complex.Ch04.ManifoldBoundaryDensity
open _root_.D12Complex.ManifoldBoundaryDensity
open Specs.D04.C12.GreenCirculationAndFlux.Model
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C15.FiniteGeometricPatchIntegrals.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.ChartIndependentTangentSpaces.Model
open Specs.D04.C14.OrientationsAndChartSigns.Model
open Specs.D04.C15.FiniteManifoldBoundaryAssembly.Model

-- Ordinary independent propositions; none is an axiom.
def patch_frontier_null_type : Prop :=
  ∀ {O : Set (E 2)} (P : Patch 1 O),
    (μH[1] : Measure ℂ)
      (complexCoordinates.symm '' (P.map '' frontier P.region)) = 0

def patch_pushforward_type : Prop :=
  ∀ {O : Set (E 2)} (P : Patch 1 O) (q : ℂ → ℂ),
    ContinuousOn q (complexCoordinates.symm '' (P.map '' closure P.region)) →
    Integrable (fun z => q z * patchDensity P z) μH[1] ∧
    complexPatchIntegral P q = ∫ z, q z * patchDensity P z ∂μH[1]

def display_pushforward_type : Prop :=
  ∀ {O : Set (E 2)} {l : ℕ} (P : Fin l → Patch 1 O)
    (s : Fin l → PointSign) (b : Fin l → ℤ) (q : ℂ → ℂ),
    (∀ t, ContinuousOn q
      (complexCoordinates.symm '' ((P t).map '' closure (P t).region))) →
    Integrable (fun z => q z * displayDensity P s b z) μH[1] ∧
    (∑ t, (b t : ℂ) * ((s t).val : ℂ) * complexPatchIntegral (P t) q) =
      ∫ z, q z * displayDensity P s b z ∂μH[1]

def regular_piece_differential_type : Prop :=
  ∀ {O M : Set (E 2)} (o : PositiveManifoldOrientation 1 1 M)
    (P : Patch 1 O) (s : PointSign), RegularPiece o P s →
    ∀ u ∈ interior P.region,
      ∃ (c : EmbeddedChart 1 1 2 M) (hu : u ∈ c.source),
        P.map u = c.toFun u ∧
        fderiv ℝ P.map u = chartDifferential c u ∧
        Function.Injective (fderiv ℝ P.map u) ∧
        chartSign o.atPoint c u hu = s.val


def patch_density_reparam_type : Prop :=
  ∀ {O : Set (E 2)} (P Q : Patch 1 O) (δ : ℝ), (δ = 1 ∨ δ = -1) →
    ∀ h : LocalReparametrization P.region Q.region δ,
    EqOn P.map (Q.map ∘ h.map) P.region →
    patchDensity P =ᵐ[μH[1]] fun z => (δ : ℂ) * patchDensity Q z

def assembly_density_type : Prop :=
  ∀ {q l p : ℕ} {O : Set (E 2)} (A : PlanarAssembly q l p O),
    originalDensity A =ᵐ[μH[1]] outerDensity A

def assembly_pushforward_type : Prop :=
  ∀ {q l p : ℕ} {O : Set (E 2)} (A : PlanarAssembly q l p O) (f : ℂ → ℂ),
    ContinuousOn f (complexCoordinates.symm '' (⋃ j, (A.piece j).carrier)) →
    AssemblyDictionary A f

def assembly_c1_type : Prop :=
  ∀ {q l p : ℕ} {O : Set (E 2)} (A : PlanarAssembly q l p O)
    (U : Set ℂ) (f : ℂ → ℂ), IsOpen U →
    complexCoordinates.symm '' (⋃ j, (A.piece j).carrier) ⊆ U →
    ContDiffOn ℝ 1 f U → AssemblyDictionary A f


def regular_piece_oriented_unit_type : Prop :=
  ∀ {O M : Set (E 2)}
    (o : PositiveManifoldOrientation 1 1 M) (P : Patch 1 O) (s : PointSign)
    (hP : RegularPiece o P s) (t : ℝ) (ht : scalarCoordinates t ∈ interior P.region),
    ∃ (c : EmbeddedChart 1 1 2 M) (hu : scalarCoordinates t ∈ c.source),
      P.map (scalarCoordinates t) = c.toFun (scalarCoordinates t) ∧
      chartSign o.atPoint c (scalarCoordinates t) hu = s.val ∧
      (s.val : ℂ) * _root_.D12Complex.SignedCurveMultiplicity.unitVelocity (patchCurve P) t =
        complexCoordinates.symm
          ((s.val / ‖chartDifferential c (scalarCoordinates t) (standardBasis 1 0)‖) •
            chartDifferential c (scalarCoordinates t) (standardBasis 1 0)) ∧
      0 < (o.atPoint (c.toFun (scalarCoordinates t)) (c.map_source hu).1).someVector
        (fun i => (s.val / ‖chartDifferential c (scalarCoordinates t) (standardBasis 1 0)‖) •
          tangentChartMap c (scalarCoordinates t) hu (standardBasis 1 i))

def regular_piece_fiber_type : Prop :=
  ∀ {O M : Set (E 2)}
    (o : PositiveManifoldOrientation 1 1 M) (P : Patch 1 O) (s : PointSign)
    (hP : RegularPiece o P s) (Z : Set (E 2))
    (hself : ∀ u ∈ P.region, ∀ v ∈ P.region, u ≠ v →
      P.map u = P.map v → P.map u ∈ Z)
    (t : ℝ) (ht : scalarCoordinates t ∈ interior P.region)
    (hz : P.map (scalarCoordinates t) ∉ Z),
    _root_.D12Complex.SignedCurveMultiplicity.regularFiber (patchCurve P) (patchParameters P)
      (patchCurve P t) = {t}

def regular_piece_density_type : Prop :=
  ∀ {O M : Set (E 2)}
    (o : PositiveManifoldOrientation 1 1 M) (P : Patch 1 O) (s : PointSign)
    (hP : RegularPiece o P s) (Z : Set (E 2))
    (hself : ∀ u ∈ P.region, ∀ v ∈ P.region, u ≠ v →
      P.map u = P.map v → P.map u ∈ Z)
    (t : ℝ) (ht : scalarCoordinates t ∈ interior P.region)
    (hz : P.map (scalarCoordinates t) ∉ Z),
    patchDensity P (patchCurve P t) = _root_.D12Complex.SignedCurveMultiplicity.unitVelocity (patchCurve P) t ∧
      ‖patchDensity P (patchCurve P t)‖ = 1

def regular_piece_multiplicity_type : Prop :=
  ∀ {O M : Set (E 2)}
    (o : PositiveManifoldOrientation 1 1 M) (P : Patch 1 O) (s : PointSign)
    (hP : RegularPiece o P s) (Z : Set (E 2))
    (hself : ∀ u ∈ P.region, ∀ v ∈ P.region, u ≠ v → P.map u = P.map v → P.map u ∈ Z)
    (t : ℝ) (ht : scalarCoordinates t ∈ interior P.region)
    (hz : P.map (scalarCoordinates t) ∉ Z),
    _root_.D12Complex.SignedCurveMultiplicity.multiplicity (patchCurve P) (patchParameters P) (patchCurve P t) = 1

def regular_display_occurrence_type : Prop :=
  ∀ {O M : Set (E 2)}
    (o : PositiveManifoldOrientation 1 1 M) (D : RegularDisplay O M o)
    (x : E 2) (hx : x ∈ M) (hz : x ∉ D.seams.carrier),
    ∃! a : ((t : Fin D.count) × (D.patch t).region), (D.patch a.1).map a.2 = x

def boundary_seams_finite_type : Prop :=
  ∀ (Z : Seams 2) (hZ : ∀ i, Z.dim i < 1),
    Z.carrier.Finite

def boundary_seams_null_type : Prop :=
  ∀ (Z : Seams 2) (hZ : ∀ i, Z.dim i < 1),
    (μH[1] : Measure ℂ) (complexCoordinates.symm '' Z.carrier) = 0

def regular_display_has_integral_type : Prop :=
  ∀ {O M : Set (E 2)}
    (o : PositiveManifoldOrientation 1 1 M) (D : RegularDisplay O M o)
    (hM : IsCompact M) (hMO : M ⊆ O)
    (ω : Specs.D04.C13.NormalizedFormsAndWedge.Model.FormField 2 1)
    (hω : Specs.D04.C13.NormalizedFormsAndWedge.Model.IsCrForm (some 0) O ω),
    Specs.D04.C15.GeneralizedStokes.Model.HasPositiveIntegral o
      (Specs.D04.C15.GeneralizedStokes.Model.tangentRestriction 1 1 M ω)
      (∑ t, (D.sign t).val * patchIntegral (D.patch t) (fun _ => 1) ω)

def regular_display_independent_type : Prop :=
  ∀ {O M : Set (E 2)}
    (o : PositiveManifoldOrientation 1 1 M) (D F : RegularDisplay O M o)
    (hM : IsCompact M) (hMO : M ⊆ O)
    (ω : Specs.D04.C13.NormalizedFormsAndWedge.Model.FormField 2 1)
    (hω : Specs.D04.C13.NormalizedFormsAndWedge.Model.IsCrForm (some 0) O ω),
    (∑ t, (D.sign t).val * patchIntegral (D.patch t) (fun _ => 1) ω) =
      ∑ t, (F.sign t).val * patchIntegral (F.patch t) (fun _ => 1) ω

def regular_display_complex_independent_type : Prop :=
  ∀ {O M : Set (E 2)}
    (o : PositiveManifoldOrientation 1 1 M) (D F : RegularDisplay O M o)
    (hO : IsOpen O) (hM : IsCompact M) (hMO : M ⊆ O) (f : ℂ → ℂ)
    (hf : ContinuousOn f (complexCoordinates.symm '' M)),
    (∑ t, ((D.sign t).val : ℂ) * complexPatchIntegral (D.patch t) f) =
      ∑ t, ((F.sign t).val : ℂ) * complexPatchIntegral (F.patch t) f

def assembly_density_integrable_type : Prop :=
  ∀ {q l p : ℕ} {O : Set (E 2)} (A : PlanarAssembly q l p O),
    Integrable (outerDensity A) μH[1] ∧ AEStronglyMeasurable (outerDensity A) μH[1]

def patch_reparam_closed_images_type : Prop :=
  ∀ {O : Set (E 2)} (P Q : Patch 1 O) (δ : ℝ)
    (h : LocalReparametrization P.region Q.region δ)
    (hmap : EqOn P.map (Q.map ∘ h.map) P.region),
    P.map '' closure P.region = Q.map '' closure Q.region

def scalarCoordinates_apply_type : Prop :=
  ∀ (t : ℝ) (i : Fin 1),
    scalarCoordinates t i = t

def scalarCoordinates_one_type : Prop :=
  scalarCoordinates 1 = standardBasis 1 0

def complexCoordinates_symm_norm_type : Prop :=
  ∀ (v : E 2),
    ‖complexCoordinates.symm v‖ = ‖v‖

def scalarCoordinates_type :=
  ℝ ≃ₗᵢ[ℝ] E 1
def scalarCoordinates_value : scalarCoordinates_type := @D12Complex.ManifoldBoundaryDensity.scalarCoordinates

def patchCurve_type :=
  ∀ {O : Set (E 2)} (P : Patch 1 O),
    ℝ → ℂ
def patchCurve_value : patchCurve_type := @D12Complex.ManifoldBoundaryDensity.patchCurve

def patchParameters_type :=
  ∀ {O : Set (E 2)} (P : Patch 1 O),
    Set ℝ
def patchParameters_value : patchParameters_type := @D12Complex.ManifoldBoundaryDensity.patchParameters

def patchDensity_type :=
  ∀ {O : Set (E 2)} (P : Patch 1 O),
    ℂ → ℂ
def patchDensity_value : patchDensity_type := @D12Complex.ManifoldBoundaryDensity.patchDensity

def complexPatchIntegral_type :=
  ∀ {O : Set (E 2)} (P : Patch 1 O) (q : ℂ → ℂ),
    ℂ
def complexPatchIntegral_value : complexPatchIntegral_type := @D12Complex.ManifoldBoundaryDensity.complexPatchIntegral

def displayDensity_type :=
  ∀ {O : Set (E 2)} {l : ℕ}
    (P : Fin l → Patch 1 O)
    (s : Fin l → Specs.D04.C14.OrientationsAndChartSigns.Model.PointSign)
    (b : Fin l → ℤ) (z : ℂ),
    ℂ
def displayDensity_value : displayDensity_type := @D12Complex.ManifoldBoundaryDensity.displayDensity

def RegularDisplay_type :=
  ∀ (O M : Set (E 2)) (o : PositiveManifoldOrientation 1 1 M),
    Type
def RegularDisplay_value : RegularDisplay_type := @D12Complex.ManifoldBoundaryDensity.RegularDisplay

def PlanarAssembly_type :=
  ∀ (q l p : ℕ) (O : Set (E 2)),
    Type
def PlanarAssembly_value : PlanarAssembly_type := @D12Complex.ManifoldBoundaryDensity.PlanarAssembly

def originalDensity_type :=
  ∀ {q l p : ℕ} {O : Set (E 2)} (A : PlanarAssembly q l p O) (z : ℂ),
    ℂ
def originalDensity_value : originalDensity_type := @D12Complex.ManifoldBoundaryDensity.originalDensity

def outerDensity_type :=
  ∀ {q l p : ℕ} {O : Set (E 2)} (A : PlanarAssembly q l p O),
    ℂ → ℂ
def outerDensity_value : outerDensity_type := @D12Complex.ManifoldBoundaryDensity.outerDensity

def pointSignInt_type :=
  ∀ (s : PointSign),
    ℤ
def pointSignInt_value : pointSignInt_type := @D12Complex.ManifoldBoundaryDensity.pointSignInt

def outerPatchChain_type :=
  ∀ {q l p : ℕ} {O : Set (E 2)} (A : PlanarAssembly q l p O),
    PatchChain 1 O
def outerPatchChain_value : outerPatchChain_type := @D12Complex.ManifoldBoundaryDensity.outerPatchChain

def AssemblyDictionary_type :=
  ∀ {q l p : ℕ} {O : Set (E 2)} (A : PlanarAssembly q l p O)
    (f : ℂ → ℂ),
    Prop
def AssemblyDictionary_value : AssemblyDictionary_type := @D12Complex.ManifoldBoundaryDensity.AssemblyDictionary

def geometricOuterDensity_type :=
  ∀ {q l p : ℕ} {O : Set (E 2)} (A : PlanarAssembly q l p O) (z : ℂ),
    ℂ
def geometricOuterDensity_value : geometricOuterDensity_type := @D12Complex.ManifoldBoundaryDensity.geometricOuterDensity

def GeometricAssemblyDictionary_type :=
  ∀ {q l p : ℕ} {O : Set (E 2)} (A : PlanarAssembly q l p O)
    (f : ℂ → ℂ),
    Prop
def GeometricAssemblyDictionary_value : GeometricAssemblyDictionary_type := @D12Complex.ManifoldBoundaryDensity.GeometricAssemblyDictionary

def geometric_outer_density_type : Prop :=
  ∀ {q l p : ℕ} {O : Set (E 2)} (A : PlanarAssembly q l p O),
    geometricOuterDensity A =ᵐ[μH[1]] outerDensity A

def original_geometric_outer_density_type : Prop :=
  ∀ {q l p : ℕ} {O : Set (E 2)} (A : PlanarAssembly q l p O),
    originalDensity A =ᵐ[μH[1]] geometricOuterDensity A

def geometric_assembly_pushforward_type : Prop :=
  ∀ {q l p : ℕ} {O : Set (E 2)}
    (A : PlanarAssembly q l p O) (f : ℂ → ℂ)
    (hf : ContinuousOn f (complexCoordinates.symm '' (⋃ j, (A.piece j).carrier))),
    GeometricAssemblyDictionary A f

def geometric_assembly_c1_type : Prop :=
  ∀ {q l p : ℕ} {O : Set (E 2)}
    (A : PlanarAssembly q l p O) (U : Set ℂ) (f : ℂ → ℂ) (_hU : IsOpen U)
    (hKU : complexCoordinates.symm '' (⋃ j, (A.piece j).carrier) ⊆ U)
    (hf : ContDiffOn ℝ 1 f U),
    GeometricAssemblyDictionary A f

def geometric_outer_integrable_type : Prop :=
  ∀ {q l p : ℕ} {O : Set (E 2)} (A : PlanarAssembly q l p O),
    Integrable (geometricOuterDensity A) μH[1] ∧ AEStronglyMeasurable (geometricOuterDensity A) μH[1]

end Specs.D12Complex.Ch04.ManifoldBoundaryDensity