import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C12.RegularDomainRiemannManifoldBridge
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C15.FinitePiecewiseStokes

/-! Gauss's theorem uses the existing Darboux region integral and the existing
positive Gram-density integral. The dimension is d+1, so d=0 is included. -/
noncomputable section
open Set Function
open scoped ContDiff BigOperators
namespace Specs.D04.C12.GaussDivergenceTheorem
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C11.EuclideanVectorOperators.Model
open Specs.D04.C12.ClassicalRegularDomains.Model
open Specs.D04.C12.RegularDomainRiemannManifoldBridge.Model
open Specs.D04.C13.NormalizedFormsAndWedge.Model
open Specs.D04.C13.ExteriorDerivative.Model
open Specs.D04.C13.OrientedEuclideanDictionary.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.Model
open Specs.D04.C14.ChartIndependentTangentSpaces.Model
open Specs.D04.C14.OrientationsAndChartSigns.Model
open Specs.D04.C14.OutwardFirstBoundaryOrientation.Model
open Specs.D04.C14.MetricTopFormsAndDensities.Model
open Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model
open Specs.D04.C15.DirectedSubstitution.Model
open Specs.D04.C15.GeneralizedStokes.Model
open Specs.D04.C06.JordanRegions.Model
namespace Model

/-- Signed metric form, with the explicitly signed-point convention in degree zero. -/
def orientedMetric : (d : ℕ) → {n : ℕ} → {M : Set (E n)} →
    ManifoldOrientation 1 d M → TangentTopField 1 d M
  | 0, _, _, s => zeroMetricVolume s
  | _+1, _, _, o => metricVolume o.atPoint

/-- The scalar multiplying the unsigned Gram density. -/
def normalFlux {d : ℕ} (F : E (d+1) → E (d+1))
    {M : Set (E (d+1))} (ν : M → E (d+1)) : M → ℝ :=
  fun x => inner ℝ (F x) (ν x)

/-- An unsigned integral with the original finite chart-partition construction.
Existence and integrability are conclusions, not assumed certificates. -/
def HasDensityIntegral {d n : ℕ} {M : Set (E n)} (ρ : M → ℝ) (I : ℝ) : Prop :=
  Continuous ρ ∧ HasCompactSupport ρ ∧
    Nonempty (ChartPartition 1 d M (tsupport ρ)) ∧
    ∀ P : ChartPartition 1 d M (tsupport ρ),
      (∀ i, ProperIntegrable (localizedDensityCoefficient ρ (P.chart i) (P.weight i))) ∧
      densityIntegral ρ P = I
end Model
open Model

def exterior_fluxType : Prop := ∀ {d : ℕ} (U : Set (E (d+1)))
    (F : E (d+1) → E (d+1)), IsOpen U → CrOn 1 U F →
    ∀ x ∈ U, exteriorDerivative (fluxForm F) x = divergence F x • omega (d+1)

/-- The actual pointwise flux bridge for every outward-first orientation. -/
def boundary_fluxType : Prop := ∀ {d : ℕ} {M : Set (E (d+1))}
    (o : PositiveManifoldOrientation 1 (d+1) M), IsAmbientOrientation o →
    ∀ (bO : ManifoldOrientation 1 d (intrinsicBoundary 1 (d+1) M)),
      OutwardFirst d o bO →
      ∀ (ν : intrinsicBoundary 1 (d+1) M → E (d+1)),
        (∀ x : intrinsicBoundary 1 (d+1) M, IsOutwardUnitConormal 1 d M x (ν x)) →
        ∀ F : E (d+1) → E (d+1),
        tangentRestriction 1 d (intrinsicBoundary 1 (d+1) M) (fluxForm F) =
          fun x => normalFlux F ν x • orientedMetric d bO x

/-- The ordinary divergence theorem, with every positive-dimensional ambient
space, arbitrary bounded regular domains (including disconnected or empty
ones), and C¹ data on any neighborhood of their closure. -/
def gaussType : Prop := ∀ {d : ℕ} {D : Set (E (d+1))}
    (hD : IsClassicalRegularDomain D) (U : Set (E (d+1)))
    (F : E (d+1) → E (d+1)), IsOpen U → closure D ⊆ U → CrOn 1 U F →
    RegionIntegrable (fun x : D => divergence F x) ∧
    HasDensityIntegral (d := d) (normalFlux F (outwardNormal hD))
      (regionIntegral (fun x : D => divergence F x))

/-- In dimension one the positive zero-dimensional density is counting:
the finite boundary sum has the actual outward signs, rather than empty-basis
orientation signs. -/
def gauss_endpointsType : Prop := ∀ {D : Set (E 1)} (hD : IsClassicalRegularDomain D)
    (U : Set (E 1)) (F : E 1 → E 1), IsOpen U → closure D ⊆ U → CrOn 1 U F →
    ∃ hfin : (frontier D).Finite,
      regionIntegral (fun x : D => divergence F x) =
        letI := hfin.fintype
        ∑ x : frontier D, F x 0 * outwardNormal hD x 0


open Specs.D04.C15.CellsChainsAndIntegrals.Model
open Specs.D04.C15.FiniteGeometricPatchIntegrals.Model
open Specs.D04.C15.FiniteGeometricUnionIntegral.Model
open Specs.D04.C15.FiniteManifoldBoundaryAssembly.Model
open Specs.D04.C15.FinitePiecewiseStokes.Model

namespace Model
/-- The ordinary divergence integrand times the normalized ambient volume. -/
def divergenceVolume {d : ℕ} (F : E (d+1) → E (d+1)) : FormField (d+1) (d+1) :=
  fun x => divergence F x • omega (d+1)
end Model
open Model

/-- The metric bridge on any regular oriented patch, using its unit perpendicular
normal with the prescribed outward-first sign. All factors are explicit. -/
def patch_fluxType : Prop := ∀ {d : ℕ} {O : Set (E (d+1))} (P : Patch d O)
    (F : E (d+1) → E (d+1)), IsOpen O → CrOn 1 O F →
    ∀ (w : E (d+1) → ℝ), ContinuousOn w O →
    ∀ (s : ℝ), (s = 1 ∨ s = -1) →
    ∀ (ν : E d → E (d+1)),
      (∀ x ∈ P.region, ‖ν x‖ = 1 ∧
        (∀ i, inner ℝ (ν x) (fderiv ℝ P.map x (standardBasis d i)) = 0) ∧
        0 < s * omega (d+1) (Fin.cons (ν x)
          (fun i => fderiv ℝ P.map x (standardBasis d i)))) →
      s * patchIntegral P w (fluxForm F) =
        regionIntegral (fun x : P.region =>
          w (P.map x) * inner ℝ (F (P.map x)) (ν x) *
            gramDensity (fun i => fderiv ℝ P.map x (standardBasis d i)))

/-- Specialization of the full geometric piecewise theorem. The inherited
hypotheses retain the actual directed seam matchings and multiplicity-one
conditions. `patch_fluxType` identifies each outer patch with normal flux. -/
def geometric_cell_piecewise_gaussType : Prop :=
  ∀ {k N L : ℕ} {O : Set (E (k+1))} (c : Fin N → Cell 1 (k+1) O)
    (P : Fin N → Fin (k+1) → Bool → Patch k O),
    (∀ j i e, (P j i e).region = cube k ∧
      EqOn (P j i e).map (cellExtension (cellFace (c j) i e)) (cube k)) →
    ∀ (outer : PatchChain k O) (left right : Fin L → WeightedPatch k O)
      (b s : Fin L → ℤ),
    (∀ i, s i = 1 ∨ s i = -1) →
    (∀ i, ∃ h : LocalReparametrization (left i).patch.region (right i).patch.region (s i : ℝ),
      EqOn (left i).patch.map ((right i).patch.map ∘ h.map) (left i).patch.region) →
    (∀ i, EqOn (left i).weight (right i).weight ((right i).patch.map '' (right i).patch.region)) →
    GeometricEquivalent (∑ j, (1 : ℤ) • patchBoundary (P j))
      (outer + ∑ i, b i • (Finsupp.single (left i) 1 - s i • Finsupp.single (right i) 1)) →
    (∀ j, InjOn (cellExtension (c j)) (cube (k+1))) →
    (∀ j x, x ∈ cube (k+1) → Function.Injective (fderiv ℝ (cellExtension (c j)) x)) →
    ∀ Z : AmbientSeams (k+1) (k+1),
    (∀ i j, i ≠ j → (cellExtension (c i) '' cube (k+1)) ∩
      (cellExtension (c j) '' cube (k+1)) ⊆ Z.carrier) →
    ∀ F : E (k+1) → E (k+1), IsOpen O → CrOn 1 O F →
      ∃ D : GeometricDecomposition (k+1) (k+1) O,
        D.carrier = ⋃ j, cellExtension (c j) '' cube (k+1) ∧
        geometricUnionIntegral D (divergenceVolume F) = patchChainIntegral (fluxForm F) outer


/-- Specialization of the full geometric piecewise theorem. The inherited
hypotheses retain the actual directed seam matchings and multiplicity-one
conditions. `patch_fluxType` identifies each outer patch with normal flux. -/
def geometric_manifold_piecewise_gaussType : Prop :=
  ∀ {d q} {O : Set (E (d+2))} (M : Fin q → CompactManifold (d+1) (d+2) O)
    (bO : (j : Fin q) → PositiveManifoldOrientation 1 (d+1)
      (intrinsicBoundary 1 (d+2) (M j).carrier)),
    (∀ j, OutwardFirst (d+1) (M j).orientation (bO j)) →
    ∀ (m : Fin q → ℕ) (P : (j : Fin q) → Fin (m j) → Patch (d+1) O)
      (s : (j : Fin q) → Fin (m j) → PointSign),
    (∀ j t, RegularPiece (bO j) (P j t) (s j t)) →
    ∀ Z : Fin q → Seams (d+2), (∀ j i, (Z j).dim i < d+1) →
    (∀ j t u, u ∈ (P j t).region → ∀ v, v ∈ (P j t).region → u ≠ v →
      (P j t).map u = (P j t).map v → (P j t).map u ∈ (Z j).carrier) →
    (∀ j t u, t ≠ u → ((P j t).map '' (P j t).region) ∩
      ((P j u).map '' (P j u).region) ⊆ (Z j).carrier) →
    (∀ j, intrinsicBoundary 1 (d+2) (M j).carrier ⊆
      (⋃ t, (P j t).map '' (P j t).region) ∪ (Z j).carrier) →
    ∀ Zbulk : AmbientSeams (d+2) (d+2),
    (∀ i j, i ≠ j → (M i).carrier ∩ (M j).carrier ⊆ Zbulk.carrier) →
    ∀ {l p : ℕ}
      (e : (Fin l ⊕ (Fin p × Bool)) ≃ ((j : Fin q) × Fin (m j)))
      (Q : Fin l → Patch (d+1) O) (tSign : Fin l → PointSign) (b : Fin l → ℤ)
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
    ∀ F : E (d+2) → E (d+2), IsOpen O → CrOn 1 O F →
    ∃ D : GeometricDecomposition (d+2) (d+2) O,
      D.carrier = ⋃ j, (M j).carrier ∧
      geometricUnionIntegral D (divergenceVolume F) =
        ∑ t, b t • ((tSign t).val * patchIntegral (Q t) (fun _ => 1) (fluxForm F))


/-- Specialization of the full geometric piecewise theorem. The inherited
hypotheses retain the actual directed seam matchings and multiplicity-one
conditions. `patch_fluxType` identifies each outer patch with normal flux. -/
def geometric_manifold_piecewise_gauss_pointsType : Prop :=
  ∀ {q} {O : Set (E (1))} (M : Fin q → CompactManifold 0 (1) O)
    (bO : (j : Fin q) → ZeroManifoldOrientation (intrinsicBoundary 1 1 (M j).carrier)),
    (∀ j, OutwardFirst 0 (M j).orientation (bO j)) → ∀ {l p : ℕ}
    (e : (Fin l ⊕ (Fin p × Bool)) ≃ (j : Fin q) × intrinsicBoundary 1 1 (M j).carrier)
    (P : Fin l → Patch 0 O) (s : Fin l → PointSign) (c : Fin l → ℤ),
    (∀ t, (0 : E 0) ∈ (P t).region ∧
      (P t).map 0 = (e (Sum.inl t)).2.val ∧
      s t = bO (e (Sum.inl t)).1 (e (Sum.inl t)).2 ∧ c t = 1) →
    (∀ i, (e (Sum.inr (i,false))).2.val = (e (Sum.inr (i,true))).2.val ∧
      (bO (e (Sum.inr (i,false))).1 (e (Sum.inr (i,false))).2).val =
        -(bO (e (Sum.inr (i,true))).1 (e (Sum.inr (i,true))).2).val) →
    ∀ Z : AmbientSeams 1 (1),
    (∀ i j, i ≠ j → (M i).carrier ∩ (M j).carrier ⊆ Z.carrier) →
    ∀ F : E (1) → E (1), IsOpen O → CrOn 1 O F →
    ∃ D : GeometricDecomposition 1 (1) O,
      D.carrier = ⋃ j, (M j).carrier ∧
      geometricUnionIntegral D (divergenceVolume F) =
        ∑ t, c t • (s t).val * patchIntegral (P t) (fun _ => 1) (fluxForm F)


/-- Outward-first normal data exist for every regular hypersurface frame;
no extra geometric certificate is required to use the patch bridge. -/
def frame_normal_existsType : Prop := ∀ {d : ℕ} (v : Fin d → E (d+1)),
    LinearIndependent ℝ v → ∀ s : ℝ, (s = 1 ∨ s = -1) →
    ∃ ν : E (d+1), ‖ν‖ = 1 ∧ (∀ i, inner ℝ ν (v i) = 0) ∧
      0 < s * omega (d+1) (Fin.cons ν v)

/-- Every regular patch has a normal with the prescribed orientation, and
its actual normal-flux integrand is Riemann integrable. -/
def patch_flux_existsType : Prop := ∀ {d : ℕ} {O : Set (E (d+1))} (P : Patch d O),
    (∀ x ∈ P.region, Function.Injective (fderiv ℝ P.map x)) →
    ∀ (F : E (d+1) → E (d+1)), IsOpen O → CrOn 1 O F →
    ∀ (w : E (d+1) → ℝ), ContinuousOn w O →
    ∀ s : ℝ, (s = 1 ∨ s = -1) →
    ∃ ν : E d → E (d+1),
      (∀ x ∈ P.region, ‖ν x‖ = 1 ∧
        (∀ i, inner ℝ (ν x) (fderiv ℝ P.map x (standardBasis d i)) = 0) ∧
        0 < s * omega (d+1) (Fin.cons (ν x)
          (fun i => fderiv ℝ P.map x (standardBasis d i)))) ∧
      RegionIntegrable (fun x : P.region =>
        w (P.map x) * inner ℝ (F (P.map x)) (ν x) *
          gramDensity (fun i => fderiv ℝ P.map x (standardBasis d i))) ∧
      s * patchIntegral P w (fluxForm F) =
        regionIntegral (fun x : P.region =>
          w (P.map x) * inner ℝ (F (P.map x)) (ν x) *
            gramDensity (fun i => fderiv ℝ P.map x (standardBasis d i)))

/-- Explicit normal-flux interpretation of any finite regular outer boundary.
Together with either geometric piecewise Gauss theorem this is its scalar
flux formula, with the original directed coefficients and multiplicities. -/
def patch_chain_fluxType : Prop := ∀ {d : ℕ} {O : Set (E (d+1))}
    (C : PatchChain d O),
    (∀ P ∈ C.support, ∀ x ∈ P.patch.region, Function.Injective (fderiv ℝ P.patch.map x)) →
    ∀ F : E (d+1) → E (d+1), IsOpen O → CrOn 1 O F →
    ∃ ν : (P : C.support) → E d → E (d+1),
      (∀ (P : C.support) (x : E d), x ∈ P.val.patch.region →
        ‖ν P x‖ = 1 ∧
        (∀ i, inner ℝ (ν P x) (fderiv ℝ P.val.patch.map x (standardBasis d i)) = 0) ∧
        0 < omega (d+1) (Fin.cons (ν P x)
          (fun i => fderiv ℝ P.val.patch.map x (standardBasis d i)))) ∧
      (∀ P : C.support, RegionIntegrable (fun x : P.val.patch.region =>
        P.val.weight (P.val.patch.map x) * inner ℝ (F (P.val.patch.map x)) (ν P x) *
          gramDensity (fun i => fderiv ℝ P.val.patch.map x (standardBasis d i)))) ∧
      patchChainIntegral (fluxForm F) C =
        ∑ P : C.support, (C P.val : ℝ) * regionIntegral
          (fun x : P.val.patch.region => P.val.weight (P.val.patch.map x) *
            inner ℝ (F (P.val.patch.map x)) (ν P x) *
              gramDensity (fun i => fderiv ℝ P.val.patch.map x (standardBasis d i)))

namespace Model
/-- A scalar normal-flux integral on a finite displayed boundary, with all
unit-normal, orientation, positive Gram, and integer coefficient data explicit. -/
def HasPatchChainFlux {d : ℕ} {O : Set (E (d+1))} (C : PatchChain d O)
    (F : E (d+1) → E (d+1)) (I : ℝ) : Prop :=
    ∃ ν : (P : C.support) → E d → E (d+1),
      (∀ (P : C.support) (x : E d), x ∈ P.val.patch.region →
        ‖ν P x‖ = 1 ∧
        (∀ i, inner ℝ (ν P x) (fderiv ℝ P.val.patch.map x (standardBasis d i)) = 0) ∧
        0 < omega (d+1) (Fin.cons (ν P x)
          (fun i => fderiv ℝ P.val.patch.map x (standardBasis d i)))) ∧
      (∀ P : C.support, RegionIntegrable (fun x : P.val.patch.region =>
        P.val.weight (P.val.patch.map x) * inner ℝ (F (P.val.patch.map x)) (ν P x) *
          gramDensity (fun i => fderiv ℝ P.val.patch.map x (standardBasis d i)))) ∧
      I =
        ∑ P : C.support, (C P.val : ℝ) * regionIntegral
          (fun x : P.val.patch.region => P.val.weight (P.val.patch.map x) *
            inner ℝ (F (P.val.patch.map x)) (ν P x) *
              gramDensity (fun i => fderiv ℝ P.val.patch.map x (standardBasis d i)))
end Model
open Model

/-- The finite regular-cell divergence theorem written directly as a sum of
scalar normal-flux integrals on its prescribed regular outer boundary. -/
def geometric_cell_piecewise_gauss_fluxType : Prop :=
  ∀ {k N L : ℕ} {O : Set (E (k+1))} (c : Fin N → Cell 1 (k+1) O)
    (P : Fin N → Fin (k+1) → Bool → Patch k O),
    (∀ j i e, (P j i e).region = cube k ∧
      EqOn (P j i e).map (cellExtension (cellFace (c j) i e)) (cube k)) →
    ∀ (outer : PatchChain k O) (left right : Fin L → WeightedPatch k O)
      (b s : Fin L → ℤ),
    (∀ i, s i = 1 ∨ s i = -1) →
    (∀ i, ∃ h : LocalReparametrization (left i).patch.region (right i).patch.region (s i : ℝ),
      EqOn (left i).patch.map ((right i).patch.map ∘ h.map) (left i).patch.region) →
    (∀ i, EqOn (left i).weight (right i).weight ((right i).patch.map '' (right i).patch.region)) →
    GeometricEquivalent (∑ j, (1 : ℤ) • patchBoundary (P j))
      (outer + ∑ i, b i • (Finsupp.single (left i) 1 - s i • Finsupp.single (right i) 1)) →
    (∀ j, InjOn (cellExtension (c j)) (cube (k+1))) →
    (∀ j x, x ∈ cube (k+1) → Function.Injective (fderiv ℝ (cellExtension (c j)) x)) →
    ∀ Z : AmbientSeams (k+1) (k+1),
    (∀ i j, i ≠ j → (cellExtension (c i) '' cube (k+1)) ∩
      (cellExtension (c j) '' cube (k+1)) ⊆ Z.carrier) →
    ∀ F : E (k+1) → E (k+1), IsOpen O → CrOn 1 O F →
      (∀ P ∈ outer.support, ∀ x ∈ P.patch.region, Function.Injective (fderiv ℝ P.patch.map x)) →
    ∃ D : GeometricDecomposition (k+1) (k+1) O,
        D.carrier = ⋃ j, cellExtension (c j) '' cube (k+1) ∧
        HasPatchChainFlux outer F (geometricUnionIntegral D (divergenceVolume F))

namespace Model
/-- The unsigned normal-flux integrals over finitely many prescribed oriented
patches; s records their outward-first signs and a their formal coefficients. -/
def HasFinitePatchFlux {d N : ℕ} {O : Set (E (d+1))}
    (P : Fin N → Patch d O) (s : Fin N → PointSign) (a : Fin N → ℤ)
    (F : E (d+1) → E (d+1)) (I : ℝ) : Prop :=
  ∃ ν : Fin N → E d → E (d+1),
    (∀ j x, x ∈ (P j).region → ‖ν j x‖ = 1 ∧
      (∀ i, inner ℝ (ν j x) (fderiv ℝ (P j).map x (standardBasis d i)) = 0) ∧
      0 < (s j).val * omega (d+1) (Fin.cons (ν j x)
        (fun i => fderiv ℝ (P j).map x (standardBasis d i)))) ∧
    (∀ j, RegionIntegrable (fun x : (P j).region =>
      inner ℝ (F ((P j).map x)) (ν j x) *
        gramDensity (fun i => fderiv ℝ (P j).map x (standardBasis d i)))) ∧
    I = ∑ j, (a j : ℝ) * regionIntegral (fun x : (P j).region =>
      inner ℝ (F ((P j).map x)) (ν j x) *
        gramDensity (fun i => fderiv ℝ (P j).map x (standardBasis d i)))
end Model
open Model

/-- The manifold-piece divergence theorem with its actual scalar normal-flux
integrals. All directed matchings, seam conditions, and multiplicity-one data
are the same as in the geometric theorem. -/
def geometric_manifold_piecewise_gauss_fluxType : Prop :=
  ∀ {d q} {O : Set (E (d+2))} (M : Fin q → CompactManifold (d+1) (d+2) O)
    (bO : (j : Fin q) → PositiveManifoldOrientation 1 (d+1)
      (intrinsicBoundary 1 (d+2) (M j).carrier)),
    (∀ j, OutwardFirst (d+1) (M j).orientation (bO j)) →
    ∀ (m : Fin q → ℕ) (P : (j : Fin q) → Fin (m j) → Patch (d+1) O)
      (s : (j : Fin q) → Fin (m j) → PointSign),
    (∀ j t, RegularPiece (bO j) (P j t) (s j t)) →
    ∀ Z : Fin q → Seams (d+2), (∀ j i, (Z j).dim i < d+1) →
    (∀ j t u, u ∈ (P j t).region → ∀ v, v ∈ (P j t).region → u ≠ v →
      (P j t).map u = (P j t).map v → (P j t).map u ∈ (Z j).carrier) →
    (∀ j t u, t ≠ u → ((P j t).map '' (P j t).region) ∩
      ((P j u).map '' (P j u).region) ⊆ (Z j).carrier) →
    (∀ j, intrinsicBoundary 1 (d+2) (M j).carrier ⊆
      (⋃ t, (P j t).map '' (P j t).region) ∪ (Z j).carrier) →
    ∀ Zbulk : AmbientSeams (d+2) (d+2),
    (∀ i j, i ≠ j → (M i).carrier ∩ (M j).carrier ⊆ Zbulk.carrier) →
    ∀ {l p : ℕ}
      (e : (Fin l ⊕ (Fin p × Bool)) ≃ ((j : Fin q) × Fin (m j)))
      (Q : Fin l → Patch (d+1) O) (tSign : Fin l → PointSign) (b : Fin l → ℤ)
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
    ∀ F : E (d+2) → E (d+2), IsOpen O → CrOn 1 O F →
    (∀ t x, x ∈ (Q t).region → Function.Injective (fderiv ℝ (Q t).map x)) →
    ∃ D : GeometricDecomposition (d+2) (d+2) O,
      D.carrier = ⋃ j, (M j).carrier ∧
      HasFinitePatchFlux Q tSign b F (geometricUnionIntegral D (divergenceVolume F))

/-- The manifold-piece divergence theorem with its actual scalar normal-flux
integrals. All directed matchings, seam conditions, and multiplicity-one data
are the same as in the geometric theorem. -/
def geometric_manifold_piecewise_gauss_flux_pointsType : Prop :=
  ∀ {q} {O : Set (E (1))} (M : Fin q → CompactManifold 0 (1) O)
    (bO : (j : Fin q) → ZeroManifoldOrientation (intrinsicBoundary 1 1 (M j).carrier)),
    (∀ j, OutwardFirst 0 (M j).orientation (bO j)) → ∀ {l p : ℕ}
    (e : (Fin l ⊕ (Fin p × Bool)) ≃ (j : Fin q) × intrinsicBoundary 1 1 (M j).carrier)
    (P : Fin l → Patch 0 O) (s : Fin l → PointSign) (c : Fin l → ℤ),
    (∀ t, (0 : E 0) ∈ (P t).region ∧
      (P t).map 0 = (e (Sum.inl t)).2.val ∧
      s t = bO (e (Sum.inl t)).1 (e (Sum.inl t)).2 ∧ c t = 1) →
    (∀ i, (e (Sum.inr (i,false))).2.val = (e (Sum.inr (i,true))).2.val ∧
      (bO (e (Sum.inr (i,false))).1 (e (Sum.inr (i,false))).2).val =
        -(bO (e (Sum.inr (i,true))).1 (e (Sum.inr (i,true))).2).val) →
    ∀ Z : AmbientSeams 1 (1),
    (∀ i j, i ≠ j → (M i).carrier ∩ (M j).carrier ⊆ Z.carrier) →
    ∀ F : E (1) → E (1), IsOpen O → CrOn 1 O F →
    ∃ D : GeometricDecomposition 1 (1) O,
      D.carrier = ⋃ j, (M j).carrier ∧
      HasFinitePatchFlux P s c F (geometricUnionIntegral D (divergenceVolume F))


/-- The unsigned scalar Riemann integral over a full-dimensional geometric
union agrees with its oriented form integral when each regular bulk piece
has the standard ambient orientation. Jordan measurability and scalar
integrability are conclusions. This includes mixtures of cells and manifolds. -/
def geometric_volume_riemannType : Prop :=
  ∀ {d : ℕ} {O : Set (E (d+1))} (D : GeometricDecomposition (d+1) (d+1) O),
    (∀ i, IsAmbientOrientation (D.orientation i)) →
    ∀ f : E (d+1) → ℝ, IsOpen O → ContinuousOn f O →
      Jordan D.carrier ∧ RegionIntegrable (fun x : D.carrier => f x) ∧
      geometricUnionIntegral D (fun x => f x • omega (d+1)) =
        regionIntegral (fun x : D.carrier => f x)


/-- The standard ambient finite-cell divergence theorem with ordinary scalar
Riemann bulk integral and the prescribed positive-Gram normal flux. -/
def riemann_cell_piecewise_gaussType : Prop :=
  ∀ {k N L : ℕ} {O : Set (E (k+1))} (c : Fin N → Cell 1 (k+1) O)
    (P : Fin N → Fin (k+1) → Bool → Patch k O),
    (∀ j i e, (P j i e).region = cube k ∧
      EqOn (P j i e).map (cellExtension (cellFace (c j) i e)) (cube k)) →
    ∀ (outer : PatchChain k O) (left right : Fin L → WeightedPatch k O)
      (b s : Fin L → ℤ),
    (∀ i, s i = 1 ∨ s i = -1) →
    (∀ i, ∃ h : LocalReparametrization (left i).patch.region (right i).patch.region (s i : ℝ),
      EqOn (left i).patch.map ((right i).patch.map ∘ h.map) (left i).patch.region) →
    (∀ i, EqOn (left i).weight (right i).weight ((right i).patch.map '' (right i).patch.region)) →
    GeometricEquivalent (∑ j, (1 : ℤ) • patchBoundary (P j))
      (outer + ∑ i, b i • (Finsupp.single (left i) 1 - s i • Finsupp.single (right i) 1)) →
    (∀ j, InjOn (cellExtension (c j)) (cube (k+1))) →
    (∀ j x, x ∈ cube (k+1) → Function.Injective (fderiv ℝ (cellExtension (c j)) x)) →
    ∀ Z : AmbientSeams (k+1) (k+1),
    (∀ i j, i ≠ j → (cellExtension (c i) '' cube (k+1)) ∩
      (cellExtension (c j) '' cube (k+1)) ⊆ Z.carrier) →
    ∀ F : E (k+1) → E (k+1), IsOpen O → CrOn 1 O F →
      (∀ P ∈ outer.support, ∀ x ∈ P.patch.region, Function.Injective (fderiv ℝ P.patch.map x)) →
    (∀ j x, x ∈ cube (k+1) → 0 < (fderiv ℝ (cellExtension (c j)) x).det) →
      Jordan (⋃ j, cellExtension (c j) '' cube (k+1)) ∧
      RegionIntegrable (fun x : (⋃ j, cellExtension (c j) '' cube (k+1)) => divergence F x) ∧
      regionIntegral (fun x : (⋃ j, cellExtension (c j) '' cube (k+1)) => divergence F x) = patchChainIntegral (fluxForm F) outer ∧
      HasPatchChainFlux outer F (regionIntegral (fun x : (⋃ j, cellExtension (c j) '' cube (k+1)) => divergence F x))

/-- The standard ambient finite-manifold divergence theorem with its ordinary
scalar Riemann bulk integral and the prescribed finite normal flux. -/
def riemann_manifold_piecewise_gaussType : Prop :=
  ∀ {d q} {O : Set (E (d+2))} (M : Fin q → CompactManifold (d+1) (d+2) O)
    (bO : (j : Fin q) → PositiveManifoldOrientation 1 (d+1)
      (intrinsicBoundary 1 (d+2) (M j).carrier)),
    (∀ j, OutwardFirst (d+1) (M j).orientation (bO j)) →
    ∀ (m : Fin q → ℕ) (P : (j : Fin q) → Fin (m j) → Patch (d+1) O)
      (s : (j : Fin q) → Fin (m j) → PointSign),
    (∀ j t, RegularPiece (bO j) (P j t) (s j t)) →
    ∀ Z : Fin q → Seams (d+2), (∀ j i, (Z j).dim i < d+1) →
    (∀ j t u, u ∈ (P j t).region → ∀ v, v ∈ (P j t).region → u ≠ v →
      (P j t).map u = (P j t).map v → (P j t).map u ∈ (Z j).carrier) →
    (∀ j t u, t ≠ u → ((P j t).map '' (P j t).region) ∩
      ((P j u).map '' (P j u).region) ⊆ (Z j).carrier) →
    (∀ j, intrinsicBoundary 1 (d+2) (M j).carrier ⊆
      (⋃ t, (P j t).map '' (P j t).region) ∪ (Z j).carrier) →
    ∀ Zbulk : AmbientSeams (d+2) (d+2),
    (∀ i j, i ≠ j → (M i).carrier ∩ (M j).carrier ⊆ Zbulk.carrier) →
    ∀ {l p : ℕ}
      (e : (Fin l ⊕ (Fin p × Bool)) ≃ ((j : Fin q) × Fin (m j)))
      (Q : Fin l → Patch (d+1) O) (tSign : Fin l → PointSign) (b : Fin l → ℤ)
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
    ∀ F : E (d+2) → E (d+2), IsOpen O → CrOn 1 O F →
    (∀ t x, x ∈ (Q t).region → Function.Injective (fderiv ℝ (Q t).map x)) →
    (∀ j, IsAmbientOrientation (M j).orientation) →
      Jordan (⋃ j, (M j).carrier) ∧
      RegionIntegrable (fun x : (⋃ j, (M j).carrier) => divergence F x) ∧
      regionIntegral (fun x : (⋃ j, (M j).carrier) => divergence F x) =
        ∑ t, b t • ((tSign t).val * patchIntegral (Q t) (fun _ => 1) (fluxForm F)) ∧
      HasFinitePatchFlux Q tSign b F
        (regionIntegral (fun x : (⋃ j, (M j).carrier) => divergence F x))

/-- The standard ambient finite-manifold divergence theorem with its ordinary
scalar Riemann bulk integral and the prescribed finite normal flux. -/
def riemann_manifold_piecewise_gauss_pointsType : Prop :=
  ∀ {q} {O : Set (E (1))} (M : Fin q → CompactManifold 0 (1) O)
    (bO : (j : Fin q) → ZeroManifoldOrientation (intrinsicBoundary 1 1 (M j).carrier)),
    (∀ j, OutwardFirst 0 (M j).orientation (bO j)) → ∀ {l p : ℕ}
    (e : (Fin l ⊕ (Fin p × Bool)) ≃ (j : Fin q) × intrinsicBoundary 1 1 (M j).carrier)
    (P : Fin l → Patch 0 O) (s : Fin l → PointSign) (c : Fin l → ℤ),
    (∀ t, (0 : E 0) ∈ (P t).region ∧
      (P t).map 0 = (e (Sum.inl t)).2.val ∧
      s t = bO (e (Sum.inl t)).1 (e (Sum.inl t)).2 ∧ c t = 1) →
    (∀ i, (e (Sum.inr (i,false))).2.val = (e (Sum.inr (i,true))).2.val ∧
      (bO (e (Sum.inr (i,false))).1 (e (Sum.inr (i,false))).2).val =
        -(bO (e (Sum.inr (i,true))).1 (e (Sum.inr (i,true))).2).val) →
    ∀ Z : AmbientSeams 1 (1),
    (∀ i j, i ≠ j → (M i).carrier ∩ (M j).carrier ⊆ Z.carrier) →
    ∀ F : E (1) → E (1), IsOpen O → CrOn 1 O F →
    (∀ j, IsAmbientOrientation (M j).orientation) →
      Jordan (⋃ j, (M j).carrier) ∧
      RegionIntegrable (fun x : (⋃ j, (M j).carrier) => divergence F x) ∧
      regionIntegral (fun x : (⋃ j, (M j).carrier) => divergence F x) =
        ∑ t, c t • ((s t).val * patchIntegral (P t) (fun _ => 1) (fluxForm F)) ∧
      HasFinitePatchFlux P s c F
        (regionIntegral (fun x : (⋃ j, (M j).carrier) => divergence F x)) ∧
      regionIntegral (fun x : (⋃ j, (M j).carrier) => divergence F x) =
        ∑ t, (c t : ℝ) * F ((P t).map 0) 0 * (s t).val

end Specs.D04.C12.GaussDivergenceTheorem
