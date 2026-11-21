import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C07.CoordinateSeamsVolumes
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C07.ImproperSubstitution

/-! Independent statements for `d04:07:multiplicity` and `d04:07:double-angle`.
The ambient integral uses the shared Riemann integral on an open domain with
bounded support. In particular, integrability of a zero extension does not
require that the entire image set be bounded or Jordan. No compact-containment
condition is imposed on a sheet's closure. -/
noncomputable section
open Set
open scoped BigOperators Classical
namespace Specs.D04.C07.FiniteSheetCounting
open Specs.D04.C06.DarbouxIntegral.Model
open Specs.D04.C06.NullCovers.Model
open Specs.D04.C06.JordanRegions.Model
open Specs.D04.C07.CoordinateCharts.Model
namespace Model

/-- Riemann integrability on all of Euclidean space, via the actual zero
extension on the open domain `univ`. -/
def AmbientIntegrable {n : ℕ} (f : E n → ℝ) : Prop :=
  OpenIntegrable (fun x : (univ : Set (E n)) => f x)
def ambientIntegral {n : ℕ} (f : E n → ℝ) : ℝ :=
  openIntegral (fun x : (univ : Set (E n)) => f x)

/-- The natural number of sheets covering a point; image overlaps are retained. -/
def imageMultiplicity {n m : ℕ} (S : Fin m → Set (E n)) (y : E n) : ℕ :=
  (Finset.univ.filter (fun i => y ∈ S i)).card

def doubleDomain : Set (E 2) :=
  {p | 1 < p 0 ∧ p 0 < 2 ∧ 0 < p 1 ∧ p 1 < 4 * Real.pi}
def annulus : Set (E 2) := {y | 1 < ‖y‖ ∧ ‖y‖ < 2}
def angularPiece (i : Fin 4) : Set (E 2) :=
  {p | 1 < p 0 ∧ p 0 < 2 ∧ (i : ℝ) * Real.pi < p 1 ∧
    p 1 < ((i : ℝ) + 1) * Real.pi}
def doubleBox : Box 2 where
  lower := WithLp.toLp 2 ![1, 0]
  upper := WithLp.toLp 2 ![2, 4 * Real.pi]
  ordered := by intro i; fin_cases i <;> dsimp <;> linarith [Real.pi_pos]
end Model
open Model

abbrev AmbientIntegrableType := {n : ℕ} → (E n → ℝ) → Prop
def AmbientIntegrableValue : AmbientIntegrableType := @Model.AmbientIntegrable
abbrev ambientIntegralType := {n : ℕ} → (E n → ℝ) → ℝ
def ambientIntegralValue : ambientIntegralType := @Model.ambientIntegral
abbrev imageMultiplicityType := {n m : ℕ} → (Fin m → Set (E n)) → E n → ℕ
def imageMultiplicityValue : imageMultiplicityType := @Model.imageMultiplicity

/-- Finite linearity on actual ambient Riemann zero extensions. -/
def ambient_sumType : Prop := ∀ {n m : ℕ} (F : Fin m → E n → ℝ),
  (∀ i, AmbientIntegrable (F i)) →
  AmbientIntegrable (fun y => ∑ i, F i y) ∧
  ambientIntegral (fun y => ∑ i, F i y) = ∑ i, ambientIntegral (F i)

def multiplicity_identityType : Prop := ∀ {n m : ℕ}
    (S : Fin m → Set (E n)) (f : E n → ℝ) (y : E n),
  f y * (imageMultiplicity S y : ℝ) = ∑ i, (S i).indicator f y

/-- The counting stage after the individual sheet integrals have been
identified. This statement does not assume disjoint images. -/
def counting_integralType : Prop := ∀ {n m : ℕ}
    (S : Fin m → Set (E n)) (f : E n → ℝ),
  (∀ i, AmbientIntegrable ((S i).indicator f)) →
  AmbientIntegrable (fun y => f y * (imageMultiplicity S y : ℝ)) ∧
  (∑ i, ambientIntegral ((S i).indicator f)) =
    ambientIntegral (fun y => f y * (imageMultiplicity S y : ℝ))

/-- The single-sheet extension needed when `closure S` reaches the edge of a
chart. Integrability is assumed on both sides, exactly as in finite counting. -/
def single_sheetType : Prop := ∀ {n : ℕ} (e : OpenPartialHomeomorph (E n) (E n)),
  ContDiffOn ℝ 1 e e.source → ContDiffOn ℝ 1 e.symm e.target →
  ∀ S : Set (E n), Jordan S → S ⊆ e.source → ∀ f : E n → ℝ,
  (∃ M : ℝ, ∀ y, ‖f y‖ ≤ M) → AmbientIntegrable ((e '' S).indicator f) →
  RegionIntegrable (fun x : S => f (e x) * |(fderiv ℝ e x).det|) →
  regionIntegral (fun x : S => f (e x) * |(fderiv ℝ e x).det|) =
    ambientIntegral ((e '' S).indicator f)

/-- A finite decomposition of the actual parameter domain, with a content-zero
remainder, and an actual parametrization agreeing with the sheet charts on
neighborhoods of the pieces. Images are not required to be disjoint. -/
def finite_sheet_countingType : Prop := ∀ {n m : ℕ}
    (Φ : E n → E n) (T Z : Set (E n)) (S : Fin m → Set (E n))
    (e : Fin m → OpenPartialHomeomorph (E n) (E n)),
  (∀ i, Jordan (S i)) → Pairwise (fun i j => Disjoint (S i) (S j)) →
  (∀ i, S i ⊆ (e i).source) →
  (∀ i, ContDiffOn ℝ 1 (e i) (e i).source) →
  (∀ i, ContDiffOn ℝ 1 (e i).symm (e i).target) →
  (∀ i, EqOn Φ (e i) (e i).source) → ContentZero Z →
  T = (⋃ i, S i) ∪ Z → ∀ f : E n → ℝ,
  (∃ M : ℝ, ∀ y, ‖f y‖ ≤ M) →
  (∀ i, AmbientIntegrable (((e i) '' S i).indicator f)) →
  (∀ i, RegionIntegrable (fun x : S i => f (e i x) * |(fderiv ℝ (e i) x).det|)) →
  AmbientIntegrable (fun y => f y * (imageMultiplicity (fun i => (e i) '' S i) y : ℝ)) ∧
  (∑ i, regionIntegral (fun x : S i => f (e i x) * |(fderiv ℝ (e i) x).det|)) =
    ambientIntegral (fun y => f y * (imageMultiplicity (fun i => (e i) '' S i) y : ℝ))

/-- A bounded integrand on the discarded parameter set has integral zero.
Positive dimension is the scope of the source's content-zero assertions. -/
def remainder_zeroType : Prop := ∀ {n : ℕ}, 0 < n → ∀ Z : Set (E n),
  ContentZero Z → ∀ h : Z → ℝ, RegionBounded h →
    RegionIntegrable h ∧ regionIntegral h = 0

def double_decompositionType : Prop :=
  (∀ i : Fin 4, Jordan (angularPiece i)) ∧
  Pairwise (fun i j : Fin 4 => Disjoint (angularPiece i) (angularPiece j)) ∧
  (∀ i, angularPiece i ⊆ doubleDomain) ∧
  ContentZero (carrier doubleBox \ ⋃ i : Fin 4, angularPiece i) ∧
  (∀ i : Fin 4, ∃ e : OpenPartialHomeomorph (E 2) (E 2),
    (e : E 2 → E 2) = polar ∧ angularPiece i ⊆ e.source ∧
    ContDiffOn ℝ 1 e e.source ∧ ContDiffOn ℝ 1 e.symm e.target)

def double_imageType : Prop := polar '' doubleDomain = annulus

def double_multiplicityType : Prop := ∀ y : E 2,
  y ∈ annulus → y 1 ≠ 0 → imageMultiplicity (fun i => polar '' angularPiece i) y = 2

def double_jacobianType : Prop := ∀ p ∈ doubleDomain,
  (fderiv ℝ polar p).det = p 0 ∧ |(fderiv ℝ polar p).det| = p 0 ∧ 0 < p 0

def double_parameter_integralType : Prop :=
  RegionIntegrable (fun p : doubleDomain => p.val 0) ∧
  regionIntegral (fun p : doubleDomain => p.val 0) = 6 * Real.pi

def annulus_areaType : Prop := Jordan annulus ∧ volume annulus = 3 * Real.pi

/-- Both witnesses already have radius strictly between 1 and 2. -/
def double_noninjectiveType : Prop :=
  ∃ p ∈ doubleDomain, ∃ q ∈ doubleDomain, p ≠ q ∧ polar p = polar q ∧
    p 0 ≠ 0 ∧ q 0 ≠ 0
end Specs.D04.C07.FiniteSheetCounting
