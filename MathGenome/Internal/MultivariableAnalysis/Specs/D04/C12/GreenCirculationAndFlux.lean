import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C12.RegularDomainRiemannManifoldBridge
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C15.GeneralizedStokes
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C15.FinitePiecewiseStokes

/-! Green's theorem, paper.tex d04:12:green. All integrals below use the
shared Darboux/manifold integrals. The boundary has its induced orientation;
no connectedness, simple-connectedness, or positive-chart assumption is made. -/
noncomputable section
open Set Function
open scoped ContDiff BigOperators
namespace Specs.D04.C12.GreenCirculationAndFlux
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C02.DerivativeBridge.Model
open Specs.D04.C12.ClassicalRegularDomains.Model
open Specs.D04.C12.RegularDomainRiemannManifoldBridge.Model
open Specs.D04.C13.NormalizedFormsAndWedge.Model
open Specs.D04.C13.ExteriorDerivative.Model
open Specs.D04.C13.OrientedEuclideanDictionary.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.ChartIndependentTangentSpaces.Model
open Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.Model
open Specs.D04.C14.OrientationsAndChartSigns.Model
open Specs.D04.C14.OutwardFirstBoundaryOrientation.Model
open Specs.D04.C14.MetricTopFormsAndDensities.Model
open Specs.D04.C15.GeneralizedStokes.Model
open Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model
open Specs.D04.C06.JordanRegions.Model
namespace Model

def circulationForm (P Q : E 2 → ℝ) : FormField 2 1 :=
  fun x => P x • coordinateOne 0 + Q x • coordinateOne 1

def planarFluxForm (P Q : E 2 → ℝ) : FormField 2 1 :=
  circulationForm (fun x => -Q x) P

def circulationDensity (P Q : E 2 → ℝ) (x : E 2) : ℝ :=
  scalarPartialDerivative Q x 0 - scalarPartialDerivative P x 1

def divergenceDensity (P Q : E 2 → ℝ) (x : E 2) : ℝ :=
  scalarPartialDerivative P x 0 + scalarPartialDerivative Q x 1

/-- The scalar flux times the intrinsic oriented arclength form. The normal
is the actual classical outward normal, transported along the proved boundary equality. -/
def normalFluxField {D : Set (E 2)} (hD : IsClassicalRegularDomain D)
    (hb : intrinsicBoundary 1 2 (closure D) = frontier D)
    (bO : PositiveManifoldOrientation 1 1 (intrinsicBoundary 1 2 (closure D)))
    (P Q : E 2 → ℝ) : TangentTopField 1 1 (intrinsicBoundary 1 2 (closure D)) :=
  fun x =>
    (P x * outwardNormal hD ⟨x, hb ▸ x.property⟩ 0 +
     Q x * outwardNormal hD ⟨x, hb ▸ x.property⟩ 1) • metricVolume bO.atPoint x
end Model
open Model

abbrev circulationFormType := (E 2 → ℝ) → (E 2 → ℝ) → FormField 2 1
def circulationFormValue : circulationFormType := Model.circulationForm
def planarFluxFormValue : circulationFormType := Model.planarFluxForm
abbrev planarDensityType := (E 2 → ℝ) → (E 2 → ℝ) → E 2 → ℝ
def circulationDensityValue : planarDensityType := Model.circulationDensity
def divergenceDensityValue : planarDensityType := Model.divergenceDensity

def exterior_derivativesType : Prop :=
  ∀ (U : Set (E 2)) (P Q : E 2 → ℝ), IsOpen U → CrOn 1 U P → CrOn 1 U Q →
    ∀ x ∈ U,
      exteriorDerivative (circulationForm P Q) x = circulationDensity P Q x • omega 2 ∧
      exteriorDerivative (planarFluxForm P Q) x = divergenceDensity P Q x • omega 2

/-- The unit tangent of any positive orthonormal boundary frame is the
counterclockwise quarter-turn of the classical outward normal. -/
def boundary_tangent_normalType : Prop :=
  ∀ {D : Set (E 2)} (hD : IsClassicalRegularDomain D)
    (hb : intrinsicBoundary 1 2 (closure D) = frontier D)
    (o : PositiveManifoldOrientation 1 2 (closure D)), IsAmbientOrientation o →
    ∀ (bO : PositiveManifoldOrientation 1 1 (intrinsicBoundary 1 2 (closure D))),
      OutwardFirst 1 o bO → ∀ (x : intrinsicBoundary 1 2 (closure D))
        (b : OrthonormalBasis (Fin 1) ℝ (tangentSpace 1 1 (intrinsicBoundary 1 2 (closure D)) x)),
      b.toBasis.orientation = bO.atPoint x x.property →
      let ν := outwardNormal hD ⟨x, hb ▸ x.property⟩
      let τ := (b 0).val
      τ 0 = -ν 1 ∧ τ 1 = ν 0 ∧ ν 0 = τ 1 ∧ ν 1 = -τ 0

def flux_field_identificationType : Prop :=
  ∀ {D : Set (E 2)} (hD : IsClassicalRegularDomain D)
    (hb : intrinsicBoundary 1 2 (closure D) = frontier D)
    (o : PositiveManifoldOrientation 1 2 (closure D)), IsAmbientOrientation o →
    ∀ (bO : PositiveManifoldOrientation 1 1 (intrinsicBoundary 1 2 (closure D))),
      OutwardFirst 1 o bO → ∀ P Q : E 2 → ℝ,
      tangentRestriction 1 1 (intrinsicBoundary 1 2 (closure D)) (planarFluxForm P Q) =
        normalFluxField hD hb bO P Q

/-- Every boundary-chart coefficient is literally the ordinary directed line
integrand. No unit-speed or global parametrization hypothesis is introduced. -/
def line_coefficientType : Prop :=
  ∀ {M : Set (E 2)} (P Q : E 2 → ℝ) (c : EmbeddedChart 1 1 2 M) (u : c.source),
    topCoefficient (tangentRestriction 1 1 M (circulationForm P Q)) c u =
      P (c.toFun u) * (chartDifferential c u (standardBasis 1 0)) 0 +
      Q (c.toFun u) * (chartDifferential c u (standardBasis 1 0)) 1

/-- Circulation and both equal flux integrals, with existence/integrability
of the actual Riemann values. The same orientation works for both formulas. -/
def greenType : Prop :=
  ∀ {D : Set (E 2)} (hD : IsClassicalRegularDomain D)
    (U : Set (E 2)) (P Q : E 2 → ℝ),
    IsOpen U → closure D ⊆ U → CrOn 1 U P → CrOn 1 U Q →
    ∃ (hb : intrinsicBoundary 1 2 (closure D) = frontier D)
      (o : PositiveManifoldOrientation 1 2 (closure D))
      (bO : PositiveManifoldOrientation 1 1 (intrinsicBoundary 1 2 (closure D))),
      IsAmbientOrientation o ∧ OutwardFirst 1 o bO ∧
      RegionIntegrable (fun x : D => circulationDensity P Q x) ∧
      RegionIntegrable (fun x : D => divergenceDensity P Q x) ∧
      HasPositiveIntegral bO
        (tangentRestriction 1 1 (intrinsicBoundary 1 2 (closure D)) (circulationForm P Q))
        (regionIntegral (fun x : D => circulationDensity P Q x)) ∧
      HasPositiveIntegral bO
        (tangentRestriction 1 1 (intrinsicBoundary 1 2 (closure D)) (planarFluxForm P Q))
        (regionIntegral (fun x : D => divergenceDensity P Q x)) ∧
      HasPositiveIntegral bO (normalFluxField hD hb bO P Q)
        (regionIntegral (fun x : D => divergenceDensity P Q x))


open Specs.D04.C15.CellsChainsAndIntegrals.Model
open Specs.D04.C15.FinitePiecewiseStokes.Model
open Specs.D04.C15.FiniteGeometricPatchIntegrals.Model
open Specs.D04.C15.FiniteGeometricUnionIntegral.Model
open Specs.D04.C15.FiniteManifoldBoundaryAssembly.Model
def geometric_cell_greenType : Prop :=
  ∀ {N L : ℕ} {O : Set (E 2)} (c : Fin N → Cell 1 2 O)
    (P : Fin N → Fin 2 → Bool → Patch 1 O),
    (∀ j i e, (P j i e).region = cube 1 ∧
      EqOn (P j i e).map (cellExtension (cellFace (c j) i e)) (cube 1)) →
    ∀ (outer : PatchChain 1 O) (left right : Fin L → WeightedPatch 1 O)
      (b s : Fin L → ℤ),
    (∀ i, s i = 1 ∨ s i = -1) →
    (∀ i, ∃ h : LocalReparametrization (left i).patch.region (right i).patch.region (s i : ℝ),
      EqOn (left i).patch.map ((right i).patch.map ∘ h.map) (left i).patch.region) →
    (∀ i, EqOn (left i).weight (right i).weight ((right i).patch.map '' (right i).patch.region)) →
    GeometricEquivalent (∑ j, (1 : ℤ) • patchBoundary (P j))
      (outer + ∑ i, b i • (Finsupp.single (left i) 1 - s i • Finsupp.single (right i) 1)) →
    (∀ j, InjOn (cellExtension (c j)) (cube 2)) →
    (∀ j x, x ∈ cube 2 → Function.Injective (fderiv ℝ (cellExtension (c j)) x)) →
    ∀ Z : AmbientSeams 2 2,
    (∀ i j, i ≠ j → (cellExtension (c i) '' cube 2) ∩
      (cellExtension (c j) '' cube 2) ⊆ Z.carrier) →
    ∀ f g : E 2 → ℝ, IsOpen O → CrOn 1 O f → CrOn 1 O g →
    (∃ D : GeometricDecomposition 2 2 O,
        D.carrier = ⋃ j, cellExtension (c j) '' cube 2 ∧
        geometricUnionIntegral D (fun x => circulationDensity f g x • omega 2) = patchChainIntegral (circulationForm f g) outer) ∧
    (∃ D : GeometricDecomposition 2 2 O,
        D.carrier = ⋃ j, cellExtension (c j) '' cube 2 ∧
        geometricUnionIntegral D (fun x => divergenceDensity f g x • omega 2) = patchChainIntegral (planarFluxForm f g) outer)

def geometric_manifold_greenType : Prop :=
  ∀ {q : ℕ} {O : Set (E 2)} (M : Fin q → CompactManifold 1 2 O)
    (bO : (j : Fin q) → PositiveManifoldOrientation 1 1
      (intrinsicBoundary 1 2 (M j).carrier)),
    (∀ j, OutwardFirst 1 (M j).orientation (bO j)) →
    ∀ (m : Fin q → ℕ) (P : (j : Fin q) → Fin (m j) → Patch 1 O)
      (s : (j : Fin q) → Fin (m j) → PointSign),
    (∀ j t, RegularPiece (bO j) (P j t) (s j t)) →
    ∀ Z : Fin q → Seams 2, (∀ j i, (Z j).dim i < 1) →
    (∀ j t u, u ∈ (P j t).region → ∀ v, v ∈ (P j t).region → u ≠ v →
      (P j t).map u = (P j t).map v → (P j t).map u ∈ (Z j).carrier) →
    (∀ j t u, t ≠ u → ((P j t).map '' (P j t).region) ∩
      ((P j u).map '' (P j u).region) ⊆ (Z j).carrier) →
    (∀ j, intrinsicBoundary 1 2 (M j).carrier ⊆
      (⋃ t, (P j t).map '' (P j t).region) ∪ (Z j).carrier) →
    ∀ Zbulk : AmbientSeams 2 2,
    (∀ i j, i ≠ j → (M i).carrier ∩ (M j).carrier ⊆ Zbulk.carrier) →
    ∀ {l p : ℕ}
      (e : (Fin l ⊕ (Fin p × Bool)) ≃ ((j : Fin q) × Fin (m j)))
      (Q : Fin l → Patch 1 O) (tSign : Fin l → PointSign) (b : Fin l → ℤ)
      (deltaOut : Fin l → ℝ),
    (∀ t, deltaOut t = 1 ∨ deltaOut t = -1) →
    ∀ hOut : (t : Fin l) → LocalReparametrization
      (P (e (Sum.inl t)).1 (e (Sum.inl t)).2).region (Q t).region (deltaOut t),
    (∀ t, EqOn (P (e (Sum.inl t)).1 (e (Sum.inl t)).2).map
      ((Q t).map ∘ (hOut t).map) (P (e (Sum.inl t)).1 (e (Sum.inl t)).2).region ∧
      (s (e (Sum.inl t)).1 (e (Sum.inl t)).2).val * deltaOut t = (tSign t).val ∧
      b t = 1) →
    ∀ deltaPair : Fin p → ℝ, (∀ i, deltaPair i = 1 ∨ deltaPair i = -1) →
    ∀ hPair : (i : Fin p) → LocalReparametrization
      (P (e (Sum.inr (i,false))).1 (e (Sum.inr (i,false))).2).region
      (P (e (Sum.inr (i,true))).1 (e (Sum.inr (i,true))).2).region (deltaPair i),
    (∀ i, EqOn (P (e (Sum.inr (i,false))).1 (e (Sum.inr (i,false))).2).map
      ((P (e (Sum.inr (i,true))).1 (e (Sum.inr (i,true))).2).map ∘ (hPair i).map)
      (P (e (Sum.inr (i,false))).1 (e (Sum.inr (i,false))).2).region ∧
      (s (e (Sum.inr (i,false))).1 (e (Sum.inr (i,false))).2).val * deltaPair i =
        -(s (e (Sum.inr (i,true))).1 (e (Sum.inr (i,true))).2).val) →
    ∀ f g : E 2 → ℝ, IsOpen O → CrOn 1 O f → CrOn 1 O g →
    (∃ D : GeometricDecomposition 2 2 O,
      D.carrier = ⋃ j, (M j).carrier ∧
      geometricUnionIntegral D (fun x => circulationDensity f g x • omega 2) =
        ∑ t, b t • ((tSign t).val * patchIntegral (Q t) (fun _ => 1) (circulationForm f g))) ∧
    (∃ D : GeometricDecomposition 2 2 O,
      D.carrier = ⋃ j, (M j).carrier ∧
      geometricUnionIntegral D (fun x => divergenceDensity f g x • omega 2) =
        ∑ t, b t • ((tSign t).val * patchIntegral (Q t) (fun _ => 1) (planarFluxForm f g)))


open Specs.D04.C09.PathsLength.Model
open Specs.D04.C09.LineIntegrals.Model

namespace Model
/-- The right normal to a directed velocity. At a zero velocity it is zero;
regular pieces have unit normals. -/
def rightUnitNormal (v : E 2) : E 2 :=
  ‖v‖⁻¹ • WithLp.toLp 2 ![v 1,-v 0]
end Model

abbrev rightUnitNormalType := E 2 → E 2
def rightUnitNormalValue : rightUnitNormalType := Model.rightUnitNormal
abbrev normalFluxFieldType := ∀ {D : Set (E 2)} (hD : IsClassicalRegularDomain D)
  (hb : intrinsicBoundary 1 2 (closure D) = frontier D),
  PositiveManifoldOrientation 1 1 (intrinsicBoundary 1 2 (closure D)) →
  (E 2 → ℝ) → (E 2 → ℝ) → TangentTopField 1 1 (intrinsicBoundary 1 2 (closure D))
def normalFluxFieldValue : normalFluxFieldType := @Model.normalFluxField

/-- Directed flux agrees with scalar outward flux times positive speed,
including stationary velocities (which contribute zero). -/
def flux_speedType : Prop := ∀ (P Q : E 2 → ℝ) (x v : E 2),
  planarFluxForm P Q x (fun _ => v) =
    (P x * Model.rightUnitNormal v 0 + Q x * Model.rightUnitNormal v 1) * ‖v‖

def circulation_work_integrableType : Prop := ∀ {a b : ℝ} {γ : IntervalPath 2 a b}
  (d : PiecewiseC1Data γ) (P Q : E 2 → ℝ),
  OneFormIntegrable d (circulationForm P Q) ↔
    WorkIntegrable d (fun x => WithLp.toLp 2 ![P x,Q x])

def circulation_workType : Prop := ∀ {a b : ℝ} {γ : IntervalPath 2 a b}
  (d : PiecewiseC1Data γ) (P Q : E 2 → ℝ)
  (ha : OneFormIntegrable d (circulationForm P Q))
  (hw : WorkIntegrable d (fun x => WithLp.toLp 2 ![P x,Q x])),
  oneFormIntegral d (circulationForm P Q) ha =
    workLineIntegral d (fun x => WithLp.toLp 2 ![P x,Q x]) hw

/-- Top-degree cell coefficients are exactly scalar densities times their
signed volume Jacobian. This identifies the piecewise bulk integrals with
ordinary proper Riemann integrals on their parameter regions. -/
def cell_volume_coefficientType : Prop :=
  ∀ {O : Set (E 2)} (c : Cell 1 2 O) (f : E 2 → ℝ) (u : E 2),
    cellCoefficient c (fun x => f x • omega 2) u =
      f (cellExtension c u) * (fderiv ℝ (cellExtension c) u).det

/-- Parameter patch coefficients identify the actual outer circulation and
normal flux integrals, with arbitrary weights and parameter speeds. -/
def patch_line_coefficientsType : Prop :=
  ∀ {O : Set (E 2)} (C : Patch 1 O) (P Q : E 2 → ℝ) (u : E 1),
    let v := fderiv ℝ C.map u (standardBasis 1 0)
    Specs.D04.C15.FiniteGeometricPatchIntegrals.Model.coefficient C (circulationForm P Q) u =
      P (C.map u) * v 0 + Q (C.map u) * v 1 ∧
    Specs.D04.C15.FiniteGeometricPatchIntegrals.Model.coefficient C (planarFluxForm P Q) u =
      (P (C.map u) * Model.rightUnitNormal v 0 +
       Q (C.map u) * Model.rightUnitNormal v 1) * ‖v‖

def cell_chain_greenType : Prop :=
  ∀ {N P : ℕ} {O V : Set (E 2)} (c : Fin N → Cell 1 2 O)
    (a : Fin N → ℤ) (outer refined : Chain 1 1 O)
    (left right : Fin P → Cell 1 1 O) (b s : Fin P → ℤ),
    CellAssembly V (∑ j, a j • cellBoundary (c j)) refined →
    (∀ i, Nonempty (CubeReparametrization (left i) (right i) (s i))) →
    refined = outer +
      ∑ i, b i • (Finsupp.single (left i) 1 - s i • Finsupp.single (right i) 1) →
    ∀ f g : E 2 → ℝ, IsOpen V → CrOn 1 V f → CrOn 1 V g →
    (∀ j (x : cube 2), ((c j).toFun x).val ∈ V) →
    (∀ i (x : cube 1), ((right i).toFun x).val ∈ V) →
      ((∑ j, (a j : ℝ) * cellIntegral (c j) (fun x => circulationDensity f g x • omega 2)) =
        chainIntegral (circulationForm f g) outer) ∧
      ((∑ j, (a j : ℝ) * cellIntegral (c j) (fun x => divergenceDensity f g x • omega 2)) =
        chainIntegral (planarFluxForm f g) outer)

/-- Ordinary scalar Riemann form on the actual union of positive regular
planar cells. Positive determinant is precisely their standard dx∧dy
orientation; every boundary assembly assumption is unchanged. -/
def riemann_cell_greenType : Prop :=
    ∀ {N L : ℕ} {O : Set (E 2)} (c : Fin N → Cell 1 2 O)
    (P : Fin N → Fin 2 → Bool → Patch 1 O),
    (∀ j i e, (P j i e).region = cube 1 ∧
      EqOn (P j i e).map (cellExtension (cellFace (c j) i e)) (cube 1)) →
    ∀ (outer : PatchChain 1 O) (left right : Fin L → WeightedPatch 1 O)
      (b s : Fin L → ℤ),
    (∀ i, s i = 1 ∨ s i = -1) →
    (∀ i, ∃ h : LocalReparametrization (left i).patch.region (right i).patch.region (s i : ℝ),
      EqOn (left i).patch.map ((right i).patch.map ∘ h.map) (left i).patch.region) →
    (∀ i, EqOn (left i).weight (right i).weight ((right i).patch.map '' (right i).patch.region)) →
    GeometricEquivalent (∑ j, (1 : ℤ) • patchBoundary (P j))
      (outer + ∑ i, b i • (Finsupp.single (left i) 1 - s i • Finsupp.single (right i) 1)) →
    (∀ j, InjOn (cellExtension (c j)) (cube 2)) →
    (∀ j x, x ∈ cube 2 → 0 < (fderiv ℝ (cellExtension (c j)) x).det) →
    ∀ Z : AmbientSeams 2 2,
    (∀ i j, i ≠ j → (cellExtension (c i) '' cube 2) ∩
      (cellExtension (c j) '' cube 2) ⊆ Z.carrier) →
    ∀ f g : E 2 → ℝ, IsOpen O → CrOn 1 O f → CrOn 1 O g →
      let K := ⋃ j, cellExtension (c j) '' cube 2
      Jordan K ∧
      RegionIntegrable (fun x : K => circulationDensity f g x) ∧
      RegionIntegrable (fun x : K => divergenceDensity f g x) ∧
      regionIntegral (fun x : K => circulationDensity f g x) =
        patchChainIntegral (circulationForm f g) outer ∧
      regionIntegral (fun x : K => divergenceDensity f g x) =
        patchChainIntegral (planarFluxForm f g) outer


/-- Actual scalar Riemann integral of a compact full-dimensional manifold
with its standard ambient orientation. Every signed chart partition has this
value; no volume comparison certificate is an assumption. -/
def compact_manifold_riemannType : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ {M : Set (E n)}
    (o : PositiveManifoldOrientation 1 n M), IsAmbientOrientation o →
    IsCompact M → ∀ (f : M → ℝ), Continuous f →
    Jordan M ∧ RegionIntegrable f ∧
    ∀ A : SignedChartPartition o (topSupport (volumeField f)),
      orientedIntegral (volumeField f) A = regionIntegral f

/-- Both classical Green formulas on the actual scalar Jordan union of
compact manifold pieces. Bulk orientations are the standard dx∧dy orientation;
all boundary occurrences, reparametrizations and cancellation data are retained. -/
def riemann_manifold_greenType : Prop :=
  ∀ {q : ℕ} {O : Set (E 2)} (M : Fin q → CompactManifold 1 2 O),
    (∀ j, IsAmbientOrientation (M j).orientation) →
    ∀ (bO : (j : Fin q) → PositiveManifoldOrientation 1 1
      (intrinsicBoundary 1 2 (M j).carrier)),
    (∀ j, OutwardFirst 1 (M j).orientation (bO j)) →
    ∀ (m : Fin q → ℕ) (P : (j : Fin q) → Fin (m j) → Patch 1 O)
      (s : (j : Fin q) → Fin (m j) → PointSign),
    (∀ j t, RegularPiece (bO j) (P j t) (s j t)) →
    ∀ Z : Fin q → Seams 2, (∀ j i, (Z j).dim i < 1) →
    (∀ j t u, u ∈ (P j t).region → ∀ v, v ∈ (P j t).region → u ≠ v →
      (P j t).map u = (P j t).map v → (P j t).map u ∈ (Z j).carrier) →
    (∀ j t u, t ≠ u → ((P j t).map '' (P j t).region) ∩
      ((P j u).map '' (P j u).region) ⊆ (Z j).carrier) →
    (∀ j, intrinsicBoundary 1 2 (M j).carrier ⊆
      (⋃ t, (P j t).map '' (P j t).region) ∪ (Z j).carrier) →
    ∀ Zbulk : AmbientSeams 2 2,
    (∀ i j, i ≠ j → (M i).carrier ∩ (M j).carrier ⊆ Zbulk.carrier) →
    ∀ {l p : ℕ}
      (e : (Fin l ⊕ (Fin p × Bool)) ≃ ((j : Fin q) × Fin (m j)))
      (Q : Fin l → Patch 1 O) (tSign : Fin l → PointSign) (b : Fin l → ℤ)
      (deltaOut : Fin l → ℝ),
    (∀ t, deltaOut t = 1 ∨ deltaOut t = -1) →
    ∀ hOut : (t : Fin l) → LocalReparametrization
      (P (e (Sum.inl t)).1 (e (Sum.inl t)).2).region (Q t).region (deltaOut t),
    (∀ t, EqOn (P (e (Sum.inl t)).1 (e (Sum.inl t)).2).map
      ((Q t).map ∘ (hOut t).map) (P (e (Sum.inl t)).1 (e (Sum.inl t)).2).region ∧
      (s (e (Sum.inl t)).1 (e (Sum.inl t)).2).val * deltaOut t = (tSign t).val ∧
      b t = 1) →
    ∀ deltaPair : Fin p → ℝ, (∀ i, deltaPair i = 1 ∨ deltaPair i = -1) →
    ∀ hPair : (i : Fin p) → LocalReparametrization
      (P (e (Sum.inr (i,false))).1 (e (Sum.inr (i,false))).2).region
      (P (e (Sum.inr (i,true))).1 (e (Sum.inr (i,true))).2).region (deltaPair i),
    (∀ i, EqOn (P (e (Sum.inr (i,false))).1 (e (Sum.inr (i,false))).2).map
      ((P (e (Sum.inr (i,true))).1 (e (Sum.inr (i,true))).2).map ∘ (hPair i).map)
      (P (e (Sum.inr (i,false))).1 (e (Sum.inr (i,false))).2).region ∧
      (s (e (Sum.inr (i,false))).1 (e (Sum.inr (i,false))).2).val * deltaPair i =
        -(s (e (Sum.inr (i,true))).1 (e (Sum.inr (i,true))).2).val) →
    ∀ f g : E 2 → ℝ, IsOpen O → CrOn 1 O f → CrOn 1 O g →
    let K := ⋃ j, (M j).carrier
    Jordan K ∧
    RegionIntegrable (fun x : K => circulationDensity f g x) ∧
    RegionIntegrable (fun x : K => divergenceDensity f g x) ∧
    regionIntegral (fun x : K => circulationDensity f g x) =
      ∑ t, b t • ((tSign t).val * patchIntegral (Q t) (fun _ => 1) (circulationForm f g)) ∧
    regionIntegral (fun x : K => divergenceDensity f g x) =
      ∑ t, b t • ((tSign t).val * patchIntegral (Q t) (fun _ => 1) (planarFluxForm f g))

end Specs.D04.C12.GreenCirculationAndFlux
