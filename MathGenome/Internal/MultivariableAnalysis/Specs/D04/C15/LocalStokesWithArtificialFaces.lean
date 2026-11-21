import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C15.CellStokesC1
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C06.JordanRegions
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C14.OutwardFirstBoundaryOrientation
import Mathlib.Topology.Algebra.Support
import Mathlib.Tactic.Linarith

/-! Local Stokes, paper.tex, proof of d04:15:stokes.
All dimensions are k+1, including k=0 (signed points). Face coordinates
always retain their original order. The ambient theorem requires only C¹
of the parametrization; it never differentiates a pulled-back form. -/
noncomputable section
open Set
open scoped BigOperators Classical
namespace Specs.D04.C15.LocalStokesWithArtificialFaces
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C13.NormalizedFormsAndWedge.Model
open Specs.D04.C13.ExteriorDerivative.Model
open Specs.D04.C13.PullbackCalculus.Model
open Specs.D04.C15.CellsChainsAndIntegrals.Model
open Specs.D04.C06.DarbouxIntegral.Model hiding E
namespace Model

/-- Vanishing of the actual tangential coefficient on a parametrized face.
Ambient vanishing off the manifold is not required. -/
def FaceZero {r k n} {O : Set (E n)} (c : Cell r (k+1) O)
    (ω : FormField n k) (i : Fin (k+1)) (ε : Bool) : Prop :=
  ∀ x ∈ cube k, pullback (cellExtension c) ω (faceInsertion i ε x)
    (fun j => standardBasis (k+1) (i.succAbove j)) = 0

/-- Positive affine parametrization of the coordinate rectangle, even when
some sides are degenerate. -/
def rectangleMap {k : ℕ} (Q : Box k) (x : E k) : E k :=
  WithLp.toLp 2 (fun i => Q.lower i + (Q.upper i - Q.lower i) * x i)

/-- The smaller relative open rectangle avoids all artificial faces. -/
def halfBoxInterior {k : ℕ} (Q : Box (k+1)) : Set (E (k+1)) :=
  {x | (∀ i : Fin k, Q.lower i.castSucc < x i.castSucc ∧
      x i.castSucc < Q.upper i.castSucc) ∧
    Q.lower (Fin.last k) ≤ x (Fin.last k) ∧
      x (Fin.last k) < Q.upper (Fin.last k)}

/-- Actual zero extension, retaining the original coefficient field on U. -/
def extendForm {n p : ℕ} (U : Set (E n)) (η : FormField n p) : FormField n p :=
  U.indicator η

/-- Affine maps have the regularity needed for every rectangle cell. -/
theorem rectangleMap_C1 {k : ℕ} (Q : Box k) :
    ContDiff ℝ 1 (rectangleMap Q) := by
  have h : ContDiff ℝ 1 (fun x : E k => fun i =>
      Q.lower i + (Q.upper i - Q.lower i) * x i) := by
    apply contDiff_pi.mpr
    intro i
    exact contDiff_const.add (contDiff_const.mul
      ((contDiff_apply ℝ (fun _ : Fin k => ℝ) i).comp
        (coordinates k).toContinuousLinearEquiv.contDiff))
  exact (coordinates k).symm.toContinuousLinearEquiv.contDiff.comp h

theorem rectangleMap_mem {k : ℕ} (Q : Box k) {x : E k}
    (hx : x ∈ cube k) : rectangleMap Q x ∈ carrier Q := by
  intro i
  have hw : 0 ≤ Q.upper i - Q.lower i := sub_nonneg.mpr (Q.ordered i)
  have hlo := mul_nonneg hw (hx i).1
  have hhi := mul_le_of_le_one_right hw (hx i).2
  exact ⟨by dsimp [rectangleMap]; linarith,
    by dsimp [rectangleMap]; linarith⟩

/-- A chart restricted to a rectangle, represented by the canonical cube
cell. Values are retained exactly; only its regularity is packaged. -/
def rectangleChartCell {k n : ℕ} (Q : Box k) (φ : E k → E n)
    (W : Set (E k)) (hW : IsOpen W) (hQ : carrier Q ⊆ W)
    (hφ : ContDiffOn ℝ 1 φ W) : Cell 1 k (univ : Set (E n)) where
  toFun x := ⟨φ (rectangleMap Q x), mem_univ _⟩
  open_target := isOpen_univ
  positive := le_rfl
  hasExtension := ⟨φ ∘ rectangleMap Q, rectangleMap Q ⁻¹' W,
    hW.preimage (rectangleMap_C1 Q).continuous,
    (fun _ hx => hQ (rectangleMap_mem Q hx)),
    hφ.comp (rectangleMap_C1 Q).contDiffOn (fun _ hx => hx), fun _ => rfl⟩

/-- Identity chart on a coordinate rectangle, with increasing coordinates. -/
def rectangleCell {k : ℕ} (Q : Box k) : Cell 1 k (univ : Set (E k)) :=
  rectangleChartCell Q id univ isOpen_univ (subset_univ _) contDiffOn_id

/-- Local C¹ extensions on a relative domain. No differentiability of an
arbitrary ambient representative outside that domain is postulated. -/
def LocallyC1On {n p : ℕ} (S : Set (E n)) (η : FormField n p) : Prop :=
  ∀ x ∈ S, ∃ (W : Set (E n)) (theta : FormField n p),
    x ∈ W ∧ IsCrForm (some 1) W theta ∧ EqOn theta η (W ∩ S)

def boxInterior {k : ℕ} (Q : Box k) : Set (E k) :=
  {x | ∀ i, Q.lower i < x i ∧ x i < Q.upper i}

def rectangleFaceBox {k : ℕ} (Q : Box (k+1)) (i : Fin (k+1)) : Box k :=
  ⟨WithLp.toLp 2 (fun j => Q.lower (i.succAbove j)),
    WithLp.toLp 2 (fun j => Q.upper (i.succAbove j)), fun j => Q.ordered (i.succAbove j)⟩

def rectangleFacePoint {k : ℕ} (Q : Box (k+1)) (i : Fin (k+1))
    (eps : Bool) (x : E k) : E (k+1) :=
  WithLp.toLp 2 (Fin.insertNth i (if eps then Q.upper i else Q.lower i) (fun j => x j))

/-- Unscaled proper Riemann integral of the top coefficient on Q. -/
def coordinateIntegral {k : ℕ} (Q : Box k) (eta : FormField k k) : ℝ :=
  lowerIntegral (fun x => eta x (fun j => standardBasis k j)) Q

/-- The remaining coordinates occur in their original increasing order.
In dimension zero this lower integral is evaluation, by the upstream convention. -/
def coordinateFaceIntegral {k : ℕ} (Q : Box (k+1)) (eta : FormField (k+1) k)
    (i : Fin (k+1)) (eps : Bool) : ℝ :=
  lowerIntegral (fun x => eta (rectangleFacePoint Q i eps x)
    (fun j => standardBasis (k+1) (i.succAbove j))) (rectangleFaceBox Q i)

def centeredBox {n : ℕ} (p : E n) (delta : ℝ) (hd : 0 ≤ delta) : Box n where
  lower := WithLp.toLp 2 (fun i => p i - delta)
  upper := WithLp.toLp 2 (fun i => p i + delta)
  ordered _ := by dsimp; linarith

def halfCenteredBox {k : ℕ} (p : E (k+1)) (delta : ℝ) (hd : 0 ≤ delta)
    (hp : p (Fin.last k) = 0) : Box (k+1) where
  lower := WithLp.toLp 2 (fun i => if i = Fin.last k then 0 else p i - delta)
  upper := WithLp.toLp 2 (fun i => p i + delta)
  ordered i := by
    dsimp
    split_ifs with hi
    · subst i; rw [hp]; simpa only [zero_add] using hd
    · linarith

end Model
open Model

def cell_interiorType : Prop :=
  ∀ {k n : ℕ} {O : Set (E n)} (c : Cell 1 (k+1) O)
    (V : Set (E n)) (ω : FormField n k),
    IsCrForm (some 1) V ω →
    (∀ x : cube (k+1), (c.toFun x).val ∈ V) →
    (∀ i ε, FaceZero c ω i ε) → cellIntegral c (exteriorDerivative ω) = 0

def cell_halfspaceType : Prop :=
  ∀ {k n : ℕ} {O : Set (E n)} (c : Cell 1 (k+1) O)
    (V : Set (E n)) (ω : FormField n k),
    IsCrForm (some 1) V ω →
    (∀ x : cube (k+1), (c.toFun x).val ∈ V) →
    (∀ i ε, (i ≠ Fin.last k ∨ ε = true) → FaceZero c ω i ε) →
    cellIntegral c (exteriorDerivative ω) =
      (-1 : ℝ)^(k+1) * cellIntegral (cellFace c (Fin.last k) false) ω

/-- The chart sign is arbitrary, so a negative endpoint chart is included. -/
def signed_cell_halfspaceType : Prop :=
  ∀ {k n : ℕ} {O : Set (E n)} (c : Cell 1 (k+1) O)
    (V : Set (E n)) (ω : FormField n k),
    IsCrForm (some 1) V ω →
    (∀ x : cube (k+1), (c.toFun x).val ∈ V) →
    (∀ i ε, (i ≠ Fin.last k ∨ ε = true) → FaceZero c ω i ε) →
    ∀ σ : ℝ, σ * cellIntegral c (exteriorDerivative ω) =
      (σ * (-1 : ℝ)^(k+1)) * cellIntegral (cellFace c (Fin.last k) false) ω

/-- Compact support relative to an arbitrary open domain suffices for the
zero extension to be C¹ on the whole coordinate space. -/
def extendForm_C1Type : Prop :=
  ∀ {n p : ℕ} (U : Set (E n)) (η : FormField n p),
    IsCrForm (some 1) U η →
    IsCompact (tsupport (fun x : U => η x)) →
    IsCrForm (some 1) univ (extendForm U η)

/-- Finitely many local extensions can be glued near a relative compact
support, including support meeting the genuine flat boundary. -/
def compact_relative_extensionType : Prop :=
  ∀ {n p : ℕ} (S U : Set (E n)) (η : FormField n p), IsOpen U →
    LocallyC1On (U ∩ S) η →
    IsCompact (tsupport (fun x : ↥(U ∩ S) => η x)) →
    ∃ theta : FormField n p, IsCrForm (some 1) univ theta ∧
      EqOn theta (extendForm U η) S

/-- Ordinary coefficient Stokes on any nondegenerate coordinate rectangle. -/
def rectangle_stokesType : Prop :=
  ∀ {k : ℕ} (Q : Box (k+1)) (U : Set (E (k+1))) (eta : FormField (k+1) k),
    IsCrForm (some 1) U eta → carrier Q ⊆ U →
    coordinateIntegral Q (exteriorDerivative eta) =
      ∑ i : Fin (k+1), (-1 : ℝ)^i.val *
        (coordinateFaceIntegral Q eta i true - coordinateFaceIntegral Q eta i false)

/-- C¹ ambient local Stokes for a chart restricted to an actual rectangle.
Support control is imposed on its pullback, not on an ambient support off M. -/
def ambient_rectangleType : Prop :=
  ∀ {k n : ℕ} (Q : Box (k+1)) (φ : E (k+1) → E n)
    (W : Set (E (k+1))) (hW : IsOpen W) (hQ : carrier Q ⊆ W)
    (hφ : ContDiffOn ℝ 1 φ W) (V : Set (E n)) (omega : FormField n k),
    IsCrForm (some 1) V omega → MapsTo φ (carrier Q) V →
    (Function.support (pullback φ omega) ∩ carrier Q ⊆ halfBoxInterior Q) →
    ∀ sigma : ℝ,
      sigma * cellIntegral (rectangleChartCell Q φ W hW hQ hφ) (exteriorDerivative omega) =
        (sigma * (-1 : ℝ)^(k+1)) *
          cellIntegral (cellFace (rectangleChartCell Q φ W hW hQ hφ) (Fin.last k) false) omega

/-- Interior refinement into two nested rectangles inside the chart domain. -/
def interior_rectanglesType : Prop :=
  ∀ {n : ℕ} (U : Set (E n)), IsOpen U → ∀ p ∈ U,
    ∃ (delta : ℝ) (hd : 0 < delta),
      carrier (centeredBox p delta hd.le) ⊆ U ∧
      p ∈ boxInterior (centeredBox p (delta/2) (half_pos hd).le) ∧
      carrier (centeredBox p (delta/2) (half_pos hd).le) ⊆
        boxInterior (centeredBox p delta hd.le)

/-- Boundary refinement has a genuine flat bottom and strictly separated
artificial faces. U is the ambient open set defining the relative chart domain. -/
def boundary_rectanglesType : Prop :=
  ∀ {k : ℕ} (U : Set (E (k+1))), IsOpen U → ∀ p ∈ U,
    ∀ hp : p (Fin.last k) = 0, ∃ (delta : ℝ) (hd : 0 < delta),
      carrier (halfCenteredBox p delta hd.le hp) ⊆
        U ∩ Specs.D04.C14.EmbeddedManifoldCharts.Model.halfSpace (k+1) ∧
      p ∈ halfBoxInterior (halfCenteredBox p (delta/2) (half_pos hd).le hp) ∧
      carrier (halfCenteredBox p (delta/2) (half_pos hd).le hp) ⊆
        halfBoxInterior (halfCenteredBox p delta hd.le hp)

/-- Compact-support interior Stokes on an arbitrary open parameter domain.
The proper integral is computed on any enclosing rectangle after zero extension. -/
def compact_interiorType : Prop :=
  ∀ {k : ℕ} (U : Set (E (k+1))) (eta : FormField (k+1) k),
    IsCrForm (some 1) U eta → IsCompact (tsupport (fun x : U => eta x)) →
    IsCrForm (some 1) univ (extendForm U eta) ∧
    (∃ Q : Box (k+1), Nondegenerate Q ∧ tsupport (extendForm U eta) ⊆ boxInterior Q) ∧
    ∀ Q : Box (k+1), tsupport (extendForm U eta) ⊆ boxInterior Q →
      Integrable (fun x => exteriorDerivative (extendForm U eta) x
        (fun j => standardBasis (k+1) j)) Q ∧
      coordinateIntegral Q (exteriorDerivative (extendForm U eta)) = 0

/-- Half-space Stokes with local C¹ boundary extensions and arbitrary compact
relative support. The extension exists, all rectangles containing the support
are allowed, and both displayed coefficient integrals are proper Riemann integrals. -/
def compact_halfspaceType : Prop :=
  ∀ {k : ℕ} (U : Set (E (k+1))) (eta : FormField (k+1) k), IsOpen U →
    let H := Specs.D04.C14.EmbeddedManifoldCharts.Model.halfSpace (k+1)
    LocallyC1On (U ∩ H) eta →
    IsCompact (tsupport (fun x : ↥(U ∩ H) => eta x)) →
    let K := Subtype.val '' tsupport (fun x : ↥(U ∩ H) => eta x)
    ∃ theta : FormField (k+1) k,
      IsCrForm (some 1) univ theta ∧ EqOn theta (extendForm U eta) H ∧
      Function.support (exteriorDerivative theta) ∩ H ⊆ K ∧
      (∃ Q : Box (k+1), Nondegenerate Q ∧ Q.lower (Fin.last k) = 0 ∧ K ⊆ halfBoxInterior Q) ∧
      ∀ Q : Box (k+1), Q.lower (Fin.last k) = 0 → K ⊆ halfBoxInterior Q →
        Integrable (fun x => exteriorDerivative theta x (fun j => standardBasis (k+1) j)) Q ∧
        Integrable (fun x => theta (rectangleFacePoint Q (Fin.last k) false x)
          (fun j => standardBasis (k+1) ((Fin.last k).succAbove j)))
          (rectangleFaceBox Q (Fin.last k)) ∧
        ∀ sigma : ℝ, sigma * coordinateIntegral Q (exteriorDerivative theta) =
          (sigma * (-1 : ℝ)^(k+1)) * coordinateFaceIntegral Q theta (Fin.last k) false

/-- Derivatives from different local extensions agree even on the flat
boundary, so the exterior derivative in the half-space assertion is intrinsic. -/
def halfspace_extension_independentType : Prop :=
  ∀ {k p : ℕ} (eta theta : FormField (k+1) p),
    IsCrForm (some 1) univ eta → IsCrForm (some 1) univ theta →
    let H := Specs.D04.C14.EmbeddedManifoldCharts.Model.halfSpace (k+1)
    EqOn eta theta H → EqOn (exteriorDerivative eta) (exteriorDerivative theta) H

/-- The rescaled cell integrand is the ordinary chart coefficient times
the positive rectangle Jacobian, using the actual alternating-map evaluation. -/
def rectangle_bulk_coefficientType : Prop :=
  ∀ {k n : ℕ} (Q : Box k) (phi : E k → E n) (W : Set (E k))
    (hW : IsOpen W) (hQ : carrier Q ⊆ W) (hphi : ContDiffOn ℝ 1 phi W)
    (eta : FormField n k) (x : E k), x ∈ cube k →
    cellCoefficient (rectangleChartCell Q phi W hW hQ hphi) eta x =
      content Q * pullback phi eta (rectangleMap Q x) (fun j => standardBasis k j)

def rectangle_face_coefficientType : Prop :=
  ∀ {k n : ℕ} (Q : Box (k+1)) (phi : E (k+1) → E n) (W : Set (E (k+1)))
    (hW : IsOpen W) (hQ : carrier Q ⊆ W) (hphi : ContDiffOn ℝ 1 phi W)
    (eta : FormField n k) (i : Fin (k+1)) (eps : Bool) (x : E k), x ∈ cube k →
    pullback (cellExtension (rectangleChartCell Q phi W hW hQ hphi)) eta
      (faceInsertion i eps x) (fun j => standardBasis (k+1) (i.succAbove j)) =
      (∏ j : Fin k, (Q.upper (i.succAbove j) - Q.lower (i.succAbove j))) *
        pullback phi eta (rectangleMap Q (faceInsertion i eps x))
          (fun j => standardBasis (k+1) (i.succAbove j))

/-- Both local ambient cases use the same first-derivative chart hypotheses. -/
def ambient_interior_rectangleType : Prop :=
  ∀ {k n : ℕ} (Q : Box (k+1)) (phi : E (k+1) → E n)
    (W : Set (E (k+1))) (hW : IsOpen W) (hQ : carrier Q ⊆ W)
    (hphi : ContDiffOn ℝ 1 phi W) (V : Set (E n)) (eta : FormField n k),
    IsCrForm (some 1) V eta → MapsTo phi (carrier Q) V →
    (Function.support (pullback phi eta) ∩ carrier Q ⊆ boxInterior Q) →
    cellIntegral (rectangleChartCell Q phi W hW hQ hphi) (exteriorDerivative eta) = 0

/-- The boundary factor agrees with the actual outward-first basis determinant. -/
def outward_chart_factorType : Prop :=
  ∀ (k : ℕ) (sigma : ℝ),
    sigma * (standardBasis (k+1)).det
      (Fin.cons (-standardBasis (k+1) (Fin.last k))
        (fun j : Fin k => standardBasis (k+1) j.castSucc)) = sigma * (-1 : ℝ)^(k+1)

/-- Signed-point specialization, including sigma=-1 at a terminal endpoint. -/
def signed_pointType : Prop :=
  ∀ (Q : Box 1) (eta : FormField 1 0), IsCrForm (some 1) univ eta →
    Q.lower (Fin.last 0) = 0 →
    (Function.support eta ∩ carrier Q ⊆ halfBoxInterior Q) →
    ∀ sigma : ℝ, sigma * coordinateIntegral Q (exteriorDerivative eta) =
      (-sigma) * eta (WithLp.toLp 2 (fun _ : Fin 1 => (0 : ℝ))) (fun j => Fin.elim0 j)

/-- Differentiating the zero extension is exactly zero extending d eta,
so the compact interior theorem concerns the original exterior derivative. -/
def extendForm_exteriorDerivativeType : Prop :=
  ∀ {n p : ℕ} (U : Set (E n)) (eta : FormField n p),
    IsCrForm (some 1) U eta → IsCompact (tsupport (fun x : U => eta x)) →
    exteriorDerivative (extendForm U eta) = extendForm U (exteriorDerivative eta)

/-- In the half-space, the derivative has no support outside the original
compact relative support, including along the flat boundary. -/
def relative_derivative_supportType : Prop :=
  ∀ {k p : ℕ} (theta : FormField (k+1) p), IsCrForm (some 1) univ theta →
    ∀ K : Set (E (k+1)), IsClosed K →
    let H := Specs.D04.C14.EmbeddedManifoldCharts.Model.halfSpace (k+1)
    (Function.support theta ∩ H ⊆ K) →
    Function.support (exteriorDerivative theta) ∩ H ⊆ K

/-- The interior identity also holds in the existing open-domain integral,
with precisely the original d eta and its canonical scalar zero extension. -/
def compact_interior_openIntegralType : Prop :=
  ∀ {k : ℕ} (U : Set (E (k+1))) (eta : FormField (k+1) k),
    IsCrForm (some 1) U eta → IsCompact (tsupport (fun x : U => eta x)) →
    Specs.D04.C06.JordanRegions.Model.OpenIntegrable
      (fun x : U => exteriorDerivative eta x (fun j => standardBasis (k+1) j)) ∧
    Specs.D04.C06.JordanRegions.Model.openIntegral
      (fun x : U => exteriorDerivative eta x (fun j => standardBasis (k+1) j)) = 0

end Specs.D04.C15.LocalStokesWithArtificialFaces
