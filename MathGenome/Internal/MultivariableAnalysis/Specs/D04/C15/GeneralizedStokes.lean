import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C15.IntrinsicExteriorDerivative
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C15.LocalStokesWithArtificialFaces
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C15.ManifoldIntegralIndependence
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C14.OutwardFirstBoundaryOrientation

/-! Generalized Stokes (paper.tex, d04:15:stokes).
The predicates below assert existence of the actual upstream Riemann integrals.
No local Stokes, localization identity, or integrability certificate is a
hypothesis of either Stokes proposition. The zero-dimensional boundary integral
uses explicitly signed points. -/
noncomputable section
open Set Function Filter Topology
open scoped ContDiff BigOperators Classical
namespace Specs.D04.C15.GeneralizedStokes
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C13.NormalizedFormsAndWedge.Model
open Specs.D04.C13.ExteriorDerivative.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.ChartIndependentTangentSpaces.Model
open Specs.D04.C14.OrientationsAndChartSigns.Model
open Specs.D04.C14.OutwardFirstBoundaryOrientation.Model
open Specs.D04.C14.MetricTopFormsAndDensities.Model
open Specs.D04.C14.FiniteCompactPartition.Model
open Specs.D04.C15.IntrinsicExteriorDerivative.Model
open Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model
open Specs.D04.C15.DirectedSubstitution.Model
namespace Model

/-- Arbitrary-degree tangent covector fields, sharing exactly the C² tangent
spaces and intrinsic forms of the exterior-derivative interface. -/
abbrev TangentForm (r : ℕ∞ω) (k : ℕ) {n : ℕ} (M : Set (E n)) (p : ℕ) :=
  (x : M) → Covector (tangentSpace r k M x) p

def formSupport {r : ℕ∞ω} {k n p : ℕ} {M : Set (E n)}
    (omega : TangentForm r k M p) : Set M := closure {x | omega x ≠ 0}

/-- Tangential restriction of an ambient form; it requires no derivative of
any chart pullback. At r=2 this is the shared `ambientRestriction`. -/
def tangentRestriction (r : ℕ∞ω) (k : ℕ) {n p : ℕ} (M : Set (E n))
    (omega : FormField n p) : TangentForm r k M p :=
  fun x => (omega x).compLinearMap (tangentSpace r k M x).subtype

/-- A total version of the boundary tangent inclusion. The manifold theorem
proves the inclusion and removes the fallback on every boundary point. -/
def boundaryTangentInclusion (r : ℕ∞ω) (d : ℕ) {n : ℕ} (M : Set (E n))
    (x : intrinsicBoundary r (d+1) M) :
    tangentSpace r d (intrinsicBoundary r (d+1) M) x →ₗ[ℝ]
      tangentSpace r (d+1) M x :=
  if h : tangentSpace r d (intrinsicBoundary r (d+1) M) x ≤
      tangentSpace r (d+1) M x then Submodule.inclusion h else 0

def boundaryRestriction {r : ℕ∞ω} {d n : ℕ} {M : Set (E n)}
    (omega : TangentForm r (d+1) M d) : TangentTopField r d (intrinsicBoundary r (d+1) M) :=
  fun x => (omega ⟨x, x.property.1⟩).compLinearMap (boundaryTangentInclusion r d M x)

/-- A common outward unit conormal, and the precise outward-first
characterization of the orientation, including independent point signs. -/
def OutwardFirst : {r : ℕ∞ω} → (d : ℕ) → {n : ℕ} → {M : Set (E n)} →
    PositiveManifoldOrientation r (d+1) M →
    ManifoldOrientation r d (intrinsicBoundary r (d+1) M) → Prop
  | r, 0, _, M, o, s =>
      ∃ ν : intrinsicBoundary r 1 M → E _, Continuous ν ∧
        (∀ x : intrinsicBoundary r 1 M, IsOutwardUnitConormal r 0 M x (ν x)) ∧
        ∀ x, ((s x).val = 1 ↔ PositiveOutwardLine o x (ν x)) ∧
          ((s x).val = -1 ↔ ¬ PositiveOutwardLine o x (ν x))
  | r, d+1, _, M, o, bO =>
      ∃ ν : intrinsicBoundary r (d+2) M → E _, Continuous ν ∧
        (∀ x : intrinsicBoundary r (d+2) M, IsOutwardUnitConormal r (d+1) M x (ν x)) ∧
        ∀ (x : intrinsicBoundary r (d+2) M)
          (b : Module.Basis (Fin (d+1)) ℝ
            (tangentSpace r (d+1) (intrinsicBoundary r (d+2) M) x)),
          b.orientation = bO.atPoint x x.property ↔ PositiveWithOutward o x (ν x) b

/-- Existence of a signed partition, integrability of each localized
coefficient, and the same value for every allowed signed partition. -/
def HasPositiveIntegral {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation r k M) (η : TangentTopField r k M) (I : ℝ) : Prop :=
  ContinuousTopField η ∧ IsCompact (topSupport η) ∧
    Nonempty (SignedChartPartition o (topSupport η)) ∧
    ∀ P : SignedChartPartition o (topSupport η),
      (∀ i, ProperIntegrable (localizedTopCoefficient η (P.chart i) (P.weight i))) ∧
      orientedIntegral η P = I

/-- Integration in dimension zero is finite signed evaluation. In positive
dimension this is exactly `HasPositiveIntegral`. -/
def HasManifoldIntegral : (r : ℕ∞ω) → (k : ℕ) → {n : ℕ} → {M : Set (E n)} →
    ManifoldOrientation r k M → TangentTopField r k M → ℝ → Prop
  | r, 0, _, M, s, η, I =>
      IsEmbeddedManifold r 0 M ∧ IsCompact (topSupport η) ∧
        (support (fun x : M => η x (fun j => Fin.elim0 j))).Finite ∧
        zeroIntegral s (fun x => η x (fun j => Fin.elim0 j)) = I
  | _, _+1, _, _, o, η, I => HasPositiveIntegral o η I

/-- The complete conclusion of the intrinsic theorem, without support or
regularity certificates stored in the conclusion's input data. -/
def IntrinsicStokesConclusion {d n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation 2 (d+1) M)
    (omega : IntrinsicForm (k := d+1) M d) : Prop :=
  ∃ bO : ManifoldOrientation 2 d (intrinsicBoundary 2 (d+1) M),
    OutwardFirst d o bO ∧ ∃ I : ℝ,
      HasPositiveIntegral o (intrinsicExteriorDerivative omega) I ∧
      HasManifoldIntegral 2 d bO (boundaryRestriction omega) I

/-- The C¹ ambient conclusion uses the tangent restriction of ambient domega.
In particular it does not postulate an intrinsic derivative in C¹ charts. -/
def AmbientStokesConclusion {d n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation 1 (d+1) M) (omega : FormField n d) : Prop :=
  ∃ bO : ManifoldOrientation 1 d (intrinsicBoundary 1 (d+1) M),
    OutwardFirst d o bO ∧ ∃ I : ℝ,
      HasPositiveIntegral o (tangentRestriction 1 (d+1) M (exteriorDerivative omega)) I ∧
      HasManifoldIntegral 1 d bO
        (tangentRestriction 1 d (intrinsicBoundary 1 (d+1) M) omega) I
end Model
open Model

/-- All positive dimensions up to the ambient dimension are included by the
manifold component of o; M need not be compact or boundaryless. -/
def intrinsic_stokesType : Prop :=
  ∀ {d n : ℕ} {M : Set (E n)} (o : PositiveManifoldOrientation 2 (d+1) M)
    (omega : IntrinsicForm (k := d+1) M d),
    IntrinsicC1 omega → IsCompact (formSupport omega) → IntrinsicStokesConclusion o omega

def intrinsic_stokes_compactType : Prop :=
  ∀ {d n : ℕ} {M : Set (E n)} (o : PositiveManifoldOrientation 2 (d+1) M),
    IsCompact M → ∀ omega : IntrinsicForm (k := d+1) M d,
      IntrinsicC1 omega → IntrinsicStokesConclusion o omega

def ambient_stokesType : Prop :=
  ∀ {d n : ℕ} {M : Set (E n)} (o : PositiveManifoldOrientation 1 (d+1) M)
    (O : Set (E n)) (omega : FormField n d), M ⊆ O → IsCrForm (some 1) O omega →
    IsCompact (M ∩ tsupport omega) → AmbientStokesConclusion o omega

def ambient_stokes_compactType : Prop :=
  ∀ {d n : ℕ} {M : Set (E n)} (o : PositiveManifoldOrientation 1 (d+1) M),
    IsCompact M → ∀ (O : Set (E n)) (omega : FormField n d),
      M ⊆ O → IsCrForm (some 1) O omega → AmbientStokesConclusion o omega

def intrinsic_stokes_boundarylessType : Prop :=
  ∀ {d n : ℕ} {M : Set (E n)} (o : PositiveManifoldOrientation 2 (d+1) M)
    (omega : IntrinsicForm (k := d+1) M d),
    IntrinsicC1 omega → IsCompact (formSupport omega) → intrinsicBoundary 2 (d+1) M = ∅ →
      HasPositiveIntegral o (intrinsicExteriorDerivative omega) 0

def ambient_stokes_boundarylessType : Prop :=
  ∀ {d n : ℕ} {M : Set (E n)} (o : PositiveManifoldOrientation 1 (d+1) M)
    (O : Set (E n)) (omega : FormField n d), M ⊆ O → IsCrForm (some 1) O omega →
    IsCompact (M ∩ tsupport omega) → intrinsicBoundary 1 (d+1) M = ∅ →
      HasPositiveIntegral o (tangentRestriction 1 (d+1) M (exteriorDerivative omega)) 0

/-- Supporting obligations used by finite ambient smooth localization. -/
def intrinsic_derivative_supportType : Prop :=
  ∀ {k n p : ℕ} {M : Set (E n)}, IsEmbeddedManifold 2 k M →
    ∀ (omega : IntrinsicForm (k := k) M p), IntrinsicC1 omega →
      formSupport (intrinsicExteriorDerivative omega) ⊆ formSupport omega

def intrinsic_top_continuousType : Prop :=
  ∀ {k n : ℕ} {M : Set (E n)} (η : IntrinsicForm (k := k) M k),
    IntrinsicContinuous η → ContinuousTopField η

def intrinsic_bulk_integral_existsType : Prop :=
  ∀ {d n : ℕ} {M : Set (E n)} (o : PositiveManifoldOrientation 2 (d+1) M)
    (omega : IntrinsicForm (k := d+1) M d), IntrinsicC1 omega → IsCompact (formSupport omega) →
      ∃ I, HasPositiveIntegral o (intrinsicExteriorDerivative omega) I

def outwardFirst_existsType : Prop :=
  ∀ {r : ℕ∞ω} {d n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation r (d+1) M),
    ∃ bO : ManifoldOrientation r d (intrinsicBoundary r (d+1) M), OutwardFirst d o bO

def intrinsic_partition_derivativeType : Prop :=
  ∀ {k n p m : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold 2 k M) (omega : IntrinsicForm (k := k) M p)
    (homega : IntrinsicC1 omega) (U : Fin m → Set M) (w : Fin m → E n → ℝ)
    (hw : PartitionNear M (formSupport omega) U m id w),
    (fun x : M => ∑ i, intrinsicExteriorDerivative (fun y : M => w i y • omega y) x) =
      intrinsicExteriorDerivative omega

def ambient_partition_derivativeType : Prop :=
  ∀ {k n p m : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold 1 k M) (O : Set (E n)) (alpha : FormField n p)
    (hMO : M ⊆ O) (ha : IsCrForm (some 1) O alpha)
    (U : Fin m → Set M) (w : Fin m → E n → ℝ)
    (hw : PartitionNear M (Subtype.val ⁻¹' tsupport alpha) U m id w),
    (fun x : M => ∑ i, tangentRestriction 1 k M
      (exteriorDerivative (fun y => w i y • alpha y)) x) =
        tangentRestriction 1 k M (exteriorDerivative alpha)

def intrinsicBoundary_closed_relativeType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold r k M),
    IsClosed (Subtype.val ⁻¹' intrinsicBoundary r k M : Set M)

def boundaryRestriction_C1Type : Prop :=
  ∀ {d n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold 2 (d+1) M) (omega : IntrinsicForm (k := d+1) M d)
    (homega : IntrinsicC1 omega),
    IntrinsicC1 (boundaryRestriction omega)

def boundaryRestriction_support_compactType : Prop :=
  ∀ {r : ℕ∞ω} {d n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold r (d+1) M) (omega : TangentForm r (d+1) M d)
    (hc : IsCompact (formSupport omega)),
    IsCompact (topSupport (boundaryRestriction omega))

def intrinsic_integrals_existType : Prop :=
  ∀ {d n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation 2 (d+1) M)
    (omega : IntrinsicForm (k := d+1) M d) (homega : IntrinsicC1 omega)
    (hc : IsCompact (formSupport omega)),
    ∃ bO : ManifoldOrientation 2 d (intrinsicBoundary 2 (d+1) M),
      OutwardFirst d o bO ∧ ∃ I J : ℝ,
        HasPositiveIntegral o (intrinsicExteriorDerivative omega) I ∧
        HasManifoldIntegral 2 d bO (boundaryRestriction omega) J

def ambient_integrals_existType : Prop :=
  ∀ {d n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation 1 (d+1) M) (O : Set (E n)) (alpha : FormField n d)
    (hMO : M ⊆ O) (ha : IsCrForm (some 1) O alpha)
    (hc : IsCompact (M ∩ tsupport alpha)),
    ∃ bO : ManifoldOrientation 1 d (intrinsicBoundary 1 (d+1) M),
      OutwardFirst d o bO ∧ ∃ I J : ℝ,
        HasPositiveIntegral o (tangentRestriction 1 (d+1) M (exteriorDerivative alpha)) I ∧
        HasManifoldIntegral 1 d bO
          (tangentRestriction 1 d (intrinsicBoundary 1 (d+1) M) alpha) J


/-- Closed comparison rectangles may meet the genuine flat boundary. -/
def proper_on_closed_boxType : Prop :=
  ∀ {k : ℕ} {S : Set (E k)} {f : S → ℝ}, ProperIntegrable f →
    ∀ Q : Specs.D04.C06.DarbouxIntegral.Model.Box k,
    Specs.D04.C06.DarbouxIntegral.Model.Nondegenerate Q →
    support (Specs.D04.C06.JordanRegions.Model.zeroExtension f) ⊆
      Specs.D04.C06.DarbouxIntegral.Model.carrier Q →
    ∃ hi : Specs.D04.C06.DarbouxIntegral.Model.Integrable
        (Specs.D04.C06.JordanRegions.Model.zeroExtension f) Q,
      coefficientIntegral f = Specs.D04.C06.DarbouxIntegral.Model.integral
        (Specs.D04.C06.JordanRegions.Model.zeroExtension f) Q hi

def withinExteriorDerivative_of_extensionType : Prop :=
  ∀ {a p : ℕ} {S : Set (E a)} {u : E a}, u ∈ S → UniqueDiffWithinAt ℝ S u →
    ∀ alpha beta : FormField a p, IsCrForm (some 1) univ alpha →
    alpha =ᶠ[𝓝[S] u] beta → withinExteriorDerivative S beta u = exteriorDerivative alpha u

/-- The explicit flat inclusion is stated in coordinates, independent of the
implementation-only boundary-chart constructor. -/
def compact_relative_halfspace_stokesType : Prop :=
  ∀ {k : ℕ} (U : Set (E (k+1))) (eta : FormField (k+1) k), IsOpen U →
    Specs.D04.C15.LocalStokesWithArtificialFaces.Model.LocallyC1On
      (U ∩ halfSpace (k+1)) eta →
    IsCompact (tsupport (fun x : ↥(U ∩ halfSpace (k+1)) => eta x)) →
    let inc : E k → E (k+1) := fun x => WithLp.toLp 2 (Fin.snoc (fun i => x i) 0)
    let S := U ∩ halfSpace (k+1)
    let T := inc ⁻¹' S
    let f : S → ℝ := fun x => withinExteriorDerivative S eta x (standardBasis (k+1))
    let g : T → ℝ := fun x => eta (inc x) (fun j => standardBasis (k+1) j.castSucc)
    ProperIntegrable f ∧ ProperIntegrable g ∧ ∀ sigma : ℝ,
      sigma * coefficientIntegral f = (sigma * (-1 : ℝ)^(k+1)) * coefficientIntegral g

def chartPullback_support_compactType : Prop :=
  ∀ {k n p : ℕ} {M : Set (E n)} (c : EmbeddedChart 2 k n M)
    (omega : IntrinsicForm (k := k) M p), IsCompact (formSupport omega) →
    formSupport omega ⊆ Subtype.val ⁻¹' c.ambient →
    IsCompact (tsupport (fun u : c.source => chartPullback c omega u))

def intrinsic_chart_halfspace_stokesType : Prop :=
  ∀ {d n : ℕ} {M : Set (E n)}, IsEmbeddedManifold 2 (d+1) M →
    ∀ c : EmbeddedChart 2 (d+1) n M, c.half = true →
    ∀ omega : IntrinsicForm (k := d+1) M d, IntrinsicC1 omega →
    IsCompact (formSupport omega) → formSupport omega ⊆ Subtype.val ⁻¹' c.ambient →
    let inc : E d → E (d+1) := fun x => WithLp.toLp 2 (Fin.snoc (fun i => x i) 0)
    let T := inc ⁻¹' c.source
    let g : T → ℝ := fun u => chartPullback c omega (inc u)
      (fun j => standardBasis (d+1) j.castSucc)
    ProperIntegrable (topCoefficient (intrinsicExteriorDerivative omega) c) ∧
      ProperIntegrable g ∧ ∀ sigma : ℝ,
        sigma * coefficientIntegral (topCoefficient (intrinsicExteriorDerivative omega) c) =
          (sigma * (-1 : ℝ)^(d+1)) * coefficientIntegral g

def locallyC1On_openType : Prop :=
  ∀ {a p : ℕ} (U : Set (E a)) (eta : FormField a p), IsOpen U →
    Specs.D04.C15.LocalStokesWithArtificialFaces.Model.LocallyC1On U eta →
    IsCrForm (some 1) U eta

def withinExteriorDerivative_openType : Prop :=
  ∀ {a p : ℕ} (U : Set (E a)) (eta : FormField a p), IsCrForm (some 1) U eta →
    ∀ {u : E a}, u ∈ U → withinExteriorDerivative U eta u = exteriorDerivative eta u

def compact_relative_interior_stokesType : Prop :=
  ∀ {k : ℕ} (U : Set (E (k+1))) (eta : FormField (k+1) k), IsOpen U →
    Specs.D04.C15.LocalStokesWithArtificialFaces.Model.LocallyC1On U eta →
    IsCompact (tsupport (fun x : U => eta x)) →
    let f : U → ℝ := fun x => withinExteriorDerivative U eta x (standardBasis (k+1))
    ProperIntegrable f ∧ coefficientIntegral f = 0

def intrinsic_chart_interior_stokesType : Prop :=
  ∀ {d n : ℕ} {M : Set (E n)}, IsEmbeddedManifold 2 (d+1) M →
    ∀ c : EmbeddedChart 2 (d+1) n M, c.half = false →
    ∀ omega : IntrinsicForm (k := d+1) M d, IntrinsicC1 omega →
    IsCompact (formSupport omega) → formSupport omega ⊆ Subtype.val ⁻¹' c.ambient →
    ProperIntegrable (topCoefficient (intrinsicExteriorDerivative omega) c) ∧
      coefficientIntegral (topCoefficient (intrinsicExteriorDerivative omega) c) = 0


/-! Value and support bridges for ambient C¹ localization. These are
independent propositions about the same canonical upstream objects. -/
open Specs.D04.C15.LocalStokesWithArtificialFaces.Model
open Specs.D04.C15.CellsChainsAndIntegrals.Model
open Specs.D04.C13.PullbackCalculus.Model
open Specs.D04.C06.DarbouxIntegral.Model hiding E

def rectangle_integral_substitutionType : Prop :=
  ∀ {k : ℕ} (Q : Specs.D04.C06.DarbouxIntegral.Model.Box k)
    (hq : Specs.D04.C06.DarbouxIntegral.Model.Nondegenerate Q) (f : E k → ℝ)
    (hf : ContinuousOn f (Specs.D04.C06.DarbouxIntegral.Model.carrier Q)),
    Specs.D04.C06.DarbouxIntegral.Model.lowerIntegral
      (fun x => Specs.D04.C06.DarbouxIntegral.Model.content Q * f (rectangleMap Q x)) (cubeBox k) =
        Specs.D04.C06.DarbouxIntegral.Model.lowerIntegral f Q

def rectangle_cell_integralType : Prop :=
  ∀ {k n : ℕ} (Q : Specs.D04.C06.DarbouxIntegral.Model.Box k)
    (hq : Specs.D04.C06.DarbouxIntegral.Model.Nondegenerate Q) (phi : E k → E n)
    (W : Set (E k)) (hW : IsOpen W) (hQ : Specs.D04.C06.DarbouxIntegral.Model.carrier Q ⊆ W)
    (hphi : ContDiffOn ℝ 1 phi W) (V : Set (E n)) (eta : FormField n k)
    (heta : IsCrForm (some 0) V eta) (hmap : MapsTo phi (Specs.D04.C06.DarbouxIntegral.Model.carrier Q) V),
    cellIntegral (rectangleChartCell Q phi W hW hQ hphi) eta =
      Specs.D04.C06.DarbouxIntegral.Model.lowerIntegral (fun u => pullback phi eta u (standardBasis k)) Q

def rectangle_face_cell_integralType : Prop :=
  ∀ {k n : ℕ} (Q : Specs.D04.C06.DarbouxIntegral.Model.Box (k+1))
    (hq : Specs.D04.C06.DarbouxIntegral.Model.Nondegenerate Q) (phi : E (k+1) → E n)
    (W : Set (E (k+1))) (hW : IsOpen W) (hQ : Specs.D04.C06.DarbouxIntegral.Model.carrier Q ⊆ W)
    (hphi : ContDiffOn ℝ 1 phi W) (V : Set (E n)) (eta : FormField n k)
    (heta : IsCrForm (some 0) V eta) (hmap : MapsTo phi (Specs.D04.C06.DarbouxIntegral.Model.carrier Q) V)
    (i : Fin (k+1)) (eps : Bool),
    cellIntegral (cellFace (rectangleChartCell Q phi W hW hQ hphi) i eps) eta =
      Specs.D04.C06.DarbouxIntegral.Model.lowerIntegral
        (fun u => pullback phi eta (rectangleFacePoint Q i eps u)
          (fun j => standardBasis (k+1) (i.succAbove j))) (rectangleFaceBox Q i)

def ambient_rectangle_integralType : Prop :=
  ∀ {k n : ℕ} (Q : Specs.D04.C06.DarbouxIntegral.Model.Box (k+1))
    (hq : Specs.D04.C06.DarbouxIntegral.Model.Nondegenerate Q) (phi : E (k+1) → E n)
    (W : Set (E (k+1))) (hW : IsOpen W) (hQ : Specs.D04.C06.DarbouxIntegral.Model.carrier Q ⊆ W)
    (hphi : ContDiffOn ℝ 1 phi W) (V : Set (E n)) (eta : FormField n k)
    (heta : IsCrForm (some 1) V eta) (hmap : MapsTo phi (Specs.D04.C06.DarbouxIntegral.Model.carrier Q) V)
    (hs : support (pullback phi eta) ∩ Specs.D04.C06.DarbouxIntegral.Model.carrier Q ⊆ halfBoxInterior Q)
    (sigma : ℝ),
    sigma * Specs.D04.C06.DarbouxIntegral.Model.lowerIntegral
      (fun u => pullback phi (exteriorDerivative eta) u (standardBasis (k+1))) Q =
    (sigma * (-1 : ℝ)^(k+1)) * Specs.D04.C06.DarbouxIntegral.Model.lowerIntegral
      (fun u => pullback phi eta (rectangleFacePoint Q (Fin.last k) false u)
        (fun j => standardBasis (k+1) j.castSucc)) (rectangleFaceBox Q (Fin.last k))

def ambient_interior_rectangle_integralType : Prop :=
  ∀ {k n : ℕ} (Q : Specs.D04.C06.DarbouxIntegral.Model.Box (k+1))
    (hq : Specs.D04.C06.DarbouxIntegral.Model.Nondegenerate Q) (phi : E (k+1) → E n)
    (W : Set (E (k+1))) (hW : IsOpen W) (hQ : Specs.D04.C06.DarbouxIntegral.Model.carrier Q ⊆ W)
    (hphi : ContDiffOn ℝ 1 phi W) (V : Set (E n)) (eta : FormField n k)
    (heta : IsCrForm (some 1) V eta) (hmap : MapsTo phi (Specs.D04.C06.DarbouxIntegral.Model.carrier Q) V)
    (hs : support (pullback phi eta) ∩ Specs.D04.C06.DarbouxIntegral.Model.carrier Q ⊆ boxInterior Q),
    Specs.D04.C06.DarbouxIntegral.Model.lowerIntegral
      (fun u => pullback phi (exteriorDerivative eta) u (standardBasis (k+1))) Q = 0

def tangentRestriction_weighted_derivative_supportType : Prop :=
  ∀ {k n p : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold 1 k M) (O : Set (E n)) (alpha : FormField n p)
    (hMO : M ⊆ O) (ha : IsCrForm (some 1) O alpha)
    (w : E n → ℝ) (hw : ContDiff ℝ 1 w),
    formSupport (tangentRestriction 1 k M (exteriorDerivative (fun y => w y • alpha y))) ⊆
      tsupport (fun x : M => w x)

def ambient_weighted_integrals_existType : Prop :=
  ∀ {d n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation 1 (d+1) M) (O : Set (E n)) (alpha : FormField n d)
    (hMO : M ⊆ O) (ha : IsCrForm (some 1) O alpha)
    (w : E n → ℝ) (hw : ContDiff ℝ 1 w)
    (hc : IsCompact (tsupport (fun x : M => w x))),
    ∃ bO : ManifoldOrientation 1 d (intrinsicBoundary 1 (d+1) M),
      OutwardFirst d o bO ∧ ∃ I J : ℝ,
        HasPositiveIntegral o
          (tangentRestriction 1 (d+1) M (exteriorDerivative (fun y => w y • alpha y))) I ∧
        HasManifoldIntegral 1 d bO
          (tangentRestriction 1 d (intrinsicBoundary 1 (d+1) M) (fun y => w y • alpha y)) J

def ambient_chart_rectangle_coefficientType : Prop :=
  ∀ {k n : ℕ} {M : Set (E n)}
    (c : EmbeddedChart 1 k n M) (eta : FormField n k)
    (hcont : ContinuousTopField (tangentRestriction 1 k M eta))
    (hc : IsCompact (topSupport (tangentRestriction 1 k M eta)))
    (hs : topSupport (tangentRestriction 1 k M eta) ⊆ Subtype.val ⁻¹' c.ambient)
    (Q : Specs.D04.C06.DarbouxIntegral.Model.Box k) (hq : Specs.D04.C06.DarbouxIntegral.Model.Nondegenerate Q)
    (hqs : Specs.D04.C06.DarbouxIntegral.Model.carrier Q ⊆ c.source)
    (hks : ∀ x ∈ topSupport (tangentRestriction 1 k M eta), c.invFun x ∈ Specs.D04.C06.DarbouxIntegral.Model.carrier Q)
    (W : Set (E k)) (hW : IsOpen W) (hqw : Specs.D04.C06.DarbouxIntegral.Model.carrier Q ⊆ W)
    (g : E k → E n) (hg : ContDiffOn ℝ 1 g W)
    (he : EqOn g c.toFun (c.source ∩ W)),
    ProperIntegrable (topCoefficient (tangentRestriction 1 k M eta) c) ∧
      coefficientIntegral (topCoefficient (tangentRestriction 1 k M eta) c) =
        Specs.D04.C06.DarbouxIntegral.Model.lowerIntegral (fun u => pullback g eta u (standardBasis k)) Q

end Specs.D04.C15.GeneralizedStokes
