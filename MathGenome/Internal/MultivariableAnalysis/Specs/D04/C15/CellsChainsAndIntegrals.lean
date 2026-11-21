import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C13.PullbackCalculus
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C06.DarbouxIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-! Cells are maps on the closed cube, with an existential extension, rather than
maps with a chosen germ as extra data. The order is a positive natural number or
∞ (`ℕ∞`); no rank, injectivity, or nonempty-target hypothesis is imposed.
Integrals use the already constructed proper Darboux/Riemann integral. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Set
open scoped BigOperators Classical ContDiff
namespace Specs.D04.C15.CellsChainsAndIntegrals
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C13.NormalizedFormsAndWedge.Model
open Specs.D04.C13.PullbackCalculus.Model
open Specs.D04.C06.DarbouxIntegral.Model hiding E
namespace Model

def cubeBox (k : ℕ) : Box k :=
  ⟨0, WithLp.toLp 2 (fun _ => 1), fun _ => zero_le_one⟩
def cube (k : ℕ) : Set (E k) := carrier (cubeBox k)

structure Cell (r : ℕ∞) (k : ℕ) {n : ℕ} (O : Set (E n)) where
  toFun : cube k → O
  open_target : IsOpen O
  positive : 1 ≤ r
  hasExtension : ∃ (f : E k → E n) (U : Set (E k)), IsOpen U ∧ cube k ⊆ U ∧
    ContDiffOn ℝ (r : ℕ∞ω) f U ∧ ∀ x : cube k, f x = (toFun x).val

def cellExtension {r k n} {O : Set (E n)} (c : Cell r k O) : E k → E n :=
  c.hasExtension.choose

def extensionDomain {r k n} {O : Set (E n)} (c : Cell r k O) : Set (E k) :=
  c.hasExtension.choose_spec.choose

theorem extension_spec {r k n} {O : Set (E n)} (c : Cell r k O) :
    IsOpen (extensionDomain c) ∧ cube k ⊆ extensionDomain c ∧
    ContDiffOn ℝ (r : ℕ∞ω) (cellExtension c) (extensionDomain c) ∧
    ∀ x : cube k, cellExtension c x = (c.toFun x).val :=
  c.hasExtension.choose_spec.choose_spec

/-- ε is an endpoint (false = 0, true = 1). Remaining coordinates retain their order. -/
def faceInsertion {k : ℕ} (i : Fin (k+1)) (ε : Bool) (x : E k) : E (k+1) :=
  WithLp.toLp 2 (Fin.insertNth i (if ε then 1 else 0) (fun j => x j))

theorem faceInsertion_contDiff {k : ℕ} (i : Fin (k+1)) (ε : Bool) :
    ContDiff ℝ ∞ (faceInsertion i ε) := by
  have h : ContDiff ℝ ∞ (fun x : E k =>
      Fin.insertNth (α := fun _ => ℝ) i (if ε then (1 : ℝ) else 0) (fun j => x j)) := by
    apply contDiff_pi.mpr
    intro j
    refine Fin.succAboveCases i ?_ (fun l => ?_) j
    · simpa only [Fin.insertNth_apply_same] using
        (contDiff_const : ContDiff ℝ ∞ (fun _ : E k => (if ε then (1 : ℝ) else 0)))
    · simp only [Fin.insertNth_apply_succAbove]
      have hc := (contDiff_apply ℝ (fun _ : Fin k => ℝ) l).comp
        ((coordinates k).toContinuousLinearEquiv.contDiff (n := (∞ : ℕ∞ω)))
      convert hc using 1
      funext x
      first | rfl | exact Fin.insertNth_apply_succAbove _ _ _ _
  exact (coordinates (k+1)).symm.toContinuousLinearEquiv.contDiff.comp h

theorem faceInsertion_mem {k : ℕ} (i : Fin (k+1)) (ε : Bool)
    {x : E k} (hx : x ∈ cube k) : faceInsertion i ε x ∈ cube (k+1) := by
  intro j
  refine Fin.succAboveCases i ?_ (fun l => ?_) j
  · simp only [faceInsertion, Fin.insertNth_apply_same, cubeBox, PiLp.zero_apply]
    cases ε <;> norm_num
  · simpa only [faceInsertion, Fin.insertNth_apply_succAbove, cubeBox, PiLp.zero_apply] using hx l

def cellFace {r k n} {O : Set (E n)} (c : Cell r (k+1) O)
    (i : Fin (k+1)) (ε : Bool) : Cell r k O where
  toFun x := c.toFun ⟨faceInsertion i ε x, faceInsertion_mem i ε x.property⟩
  open_target := c.open_target
  positive := c.positive
  hasExtension := by
    refine ⟨cellExtension c ∘ faceInsertion i ε,
      faceInsertion i ε ⁻¹' extensionDomain c,
      (extension_spec c).1.preimage (faceInsertion_contDiff i ε).continuous,
      (fun x hx => (extension_spec c).2.1 (faceInsertion_mem i ε hx)), ?_, ?_⟩
    · exact (extension_spec c).2.2.1.comp
        ((faceInsertion_contDiff i ε).of_le (by exact_mod_cast le_top)).contDiffOn
        (fun _ hx => hx)
    · intro x
      exact (extension_spec c).2.2.2 ⟨faceInsertion i ε x, faceInsertion_mem i ε x.property⟩

def cellCoefficient {r k n} {O : Set (E n)} (c : Cell r k O)
    (omega : FormField n k) (x : E k) : ℝ :=
  pullback (cellExtension c) omega x (fun j => standardBasis k j)

/-- Totalized by the lower integral; for continuous forms the theorem below proves
integrability, identifying this with the proper Riemann integral. -/
def cellIntegral {r k n} {O : Set (E n)} (c : Cell r k O) (omega : FormField n k) : ℝ :=
  lowerIntegral (cellCoefficient c omega) (cubeBox k)

abbrev Chain (r : ℕ∞) (k : ℕ) {n : ℕ} (O : Set (E n)) := Cell r k O →₀ ℤ

def chainIntegral {r k n} {O : Set (E n)} (omega : FormField n k) : Chain r k O →+ ℝ :=
  Finsupp.liftAddHom (fun c => ({
      toFun := fun a : ℤ => a • cellIntegral c omega
      map_zero' := by simp
      map_add' := fun a b => by simp [add_mul] } : ℤ →+ ℝ))

def cellBoundary {r k n} {O : Set (E n)} (c : Cell r (k+1) O) : Chain r k O :=
  ∑ i : Fin (k+1), (-1 : ℤ) ^ i.val •
    (Finsupp.single (cellFace c i true) 1 - Finsupp.single (cellFace c i false) 1)

def chainBoundarySucc {r k n} {O : Set (E n)} : Chain r (k+1) O →+ Chain r k O :=
  Finsupp.liftAddHom (fun c => ({
      toFun := fun a : ℤ => a • cellBoundary c
      map_zero' := by simp
      map_add' := fun a b => by simp [add_zsmul] } : ℤ →+ Chain r k O))

def chainBoundary {r n} {O : Set (E n)} : (k : ℕ) → Chain r k O →+ Chain r (k-1) O
  | 0 => 0
  | k+1 => chainBoundarySucc

/-- The unique zero-dimensional parameter is sent to the given point. -/
def pointCell (r : ℕ∞) {n : ℕ} (O : Set (E n)) (hO : IsOpen O)
    (hr : 1 ≤ r) (p : O) : Cell r 0 O where
  toFun _ := p
  open_target := hO
  positive := hr
  hasExtension := ⟨fun _ => p.val, univ, isOpen_univ, subset_univ _, contDiffOn_const,
    fun _ => rfl⟩
end Model

/-! Full expected types and canonical values. These use only library objects
and upstream Specs; no candidate implementation is imported. -/
open Model

abbrev cubeBoxType := (k : ℕ) → Box k
def cubeBoxValue : cubeBoxType := @Model.cubeBox

abbrev cubeType := (k : ℕ) → Set (E k)
def cubeValue : cubeType := @Model.cube

abbrev CellType := (r : ℕ∞) → (k : ℕ) → {n : ℕ} → Set (E n) → Type
def CellValue : CellType := @Model.Cell

abbrev cellExtensionType := {r : ℕ∞} → {k n : ℕ} → {O : Set (E n)} → Cell r k O → E k → E n
def cellExtensionValue : cellExtensionType := @Model.cellExtension

abbrev extensionDomainType := {r : ℕ∞} → {k n : ℕ} → {O : Set (E n)} → Cell r k O → Set (E k)
def extensionDomainValue : extensionDomainType := @Model.extensionDomain

abbrev faceInsertionType := {k : ℕ} → Fin (k+1) → Bool → E k → E (k+1)
def faceInsertionValue : faceInsertionType := @Model.faceInsertion

abbrev cellFaceType := {r : ℕ∞} → {k n : ℕ} → {O : Set (E n)} → Cell r (k+1) O → Fin (k+1) → Bool → Cell r k O
def cellFaceValue : cellFaceType := @Model.cellFace

abbrev cellCoefficientType := {r : ℕ∞} → {k n : ℕ} → {O : Set (E n)} → Cell r k O → FormField n k → E k → ℝ
def cellCoefficientValue : cellCoefficientType := @Model.cellCoefficient

abbrev cellIntegralType := {r : ℕ∞} → {k n : ℕ} → {O : Set (E n)} → Cell r k O → FormField n k → ℝ
def cellIntegralValue : cellIntegralType := @Model.cellIntegral

abbrev ChainType := (r : ℕ∞) → (k : ℕ) → {n : ℕ} → Set (E n) → Type
def ChainValue : ChainType := @Model.Chain

abbrev chainIntegralType := {r : ℕ∞} → {k n : ℕ} → {O : Set (E n)} → FormField n k → (Chain r k O →+ ℝ)
def chainIntegralValue : chainIntegralType := @Model.chainIntegral

abbrev cellBoundaryType := {r : ℕ∞} → {k n : ℕ} → {O : Set (E n)} → Cell r (k+1) O → Chain r k O
def cellBoundaryValue : cellBoundaryType := @Model.cellBoundary

abbrev chainBoundarySuccType := {r : ℕ∞} → {k n : ℕ} → {O : Set (E n)} → (Chain r (k+1) O →+ Chain r k O)
def chainBoundarySuccValue : chainBoundarySuccType := @Model.chainBoundarySucc

abbrev chainBoundaryType := {r : ℕ∞} → {n : ℕ} → {O : Set (E n)} → (k : ℕ) → (Chain r k O →+ Chain r (k-1) O)
def chainBoundaryValue : chainBoundaryType := @Model.chainBoundary

abbrev pointCellType := (r : ℕ∞) → {n : ℕ} → (O : Set (E n)) → IsOpen O → 1 ≤ r → O → Cell r 0 O
def pointCellValue : pointCellType := @Model.pointCell

def cell_extType : Prop :=
  ∀ {r k n} {O : Set (E n)} {c d : Cell r k O}
    (h : ∀ x, c.toFun x = d.toFun x),
  c = d

def extension_on_cubeType : Prop :=
  ∀ {r k n} {O : Set (E n)} (c : Cell r k O) (x : cube k),
  cellExtension c x = (c.toFun x).val

def extension_C1Type : Prop :=
  ∀ {r k n} {O : Set (E n)} (c : Cell r k O),
  ContDiffOn ℝ 1 (cellExtension c) (extensionDomain c)

def cellCoefficient_continuousType : Prop :=
  ∀ {r k n} {O : Set (E n)} (c : Cell r k O)
    (omega : FormField n k) (h : IsCrForm (some 0) O omega),
  ContinuousOn (cellCoefficient c omega) (cube k)

def cellCoefficient_integrableType : Prop :=
  ∀ {r k n} {O : Set (E n)} (c : Cell r k O)
    (omega : FormField n k) (h : IsCrForm (some 0) O omega),
  Specs.D04.C06.DarbouxIntegral.Model.Integrable (cellCoefficient c omega) (cubeBox k)

def faceInsertion_sameType : Prop :=
  ∀ {k} (i : Fin (k+1)) (ε : Bool) (x : E k),
  faceInsertion i ε x i = if ε then 1 else 0

def faceInsertion_otherType : Prop :=
  ∀ {k} (i : Fin (k+1)) (ε : Bool) (x : E k) (j : Fin k),
  faceInsertion i ε x (i.succAbove j) = x j

def cellFace_applyType : Prop :=
  ∀ {r k n} {O : Set (E n)} (c : Cell r (k+1) O)
    (i : Fin (k+1)) (ε : Bool) (x : cube k),
  (cellFace c i ε).toFun x = c.toFun
      ⟨faceInsertion i ε x, Specs.D04.C15.CellsChainsAndIntegrals.Model.faceInsertion_mem i ε x.property⟩

def chainIntegral_singleType : Prop :=
  ∀ {r k n} {O : Set (E n)} (omega : FormField n k)
    (c : Cell r k O) (a : ℤ),
  chainIntegral omega (Finsupp.single c a) = a • cellIntegral c omega

def chainIntegral_sumType : Prop :=
  ∀ {r k n} {O : Set (E n)} (omega : FormField n k)
    (C : Chain r k O),
  chainIntegral omega C = C.sum (fun c a => a • cellIntegral c omega)

def boundary_singleType : Prop :=
  ∀ {r k n} {O : Set (E n)} (c : Cell r (k+1) O) (a : ℤ),
  chainBoundarySucc (Finsupp.single c a) = a • cellBoundary c

def boundary_zero_chainType : Prop :=
  ∀ {r n} {O : Set (E n)} (C : Chain r 0 O),
  chainBoundary 0 C = 0

def cellIntegral_zero_degreeType : Prop :=
  ∀ {r n} {O : Set (E n)} (c : Cell r 0 O) (f : E n → ℝ),
  cellIntegral c (fun y => scalarCovector (f y)) = f (c.toFun ⟨0, (by intro i; exact ⟨le_rfl, zero_le_one⟩)⟩)

def pointCell_inverseType : Prop :=
  ∀ {r n} {O : Set (E n)} (c : Cell r 0 O),
  pointCell r O c.open_target c.positive (c.toFun ⟨0, (by intro i; exact ⟨le_rfl, zero_le_one⟩)⟩) = c

def extension_derivative_uniqueType : Prop :=
  ∀ {r k n} {O : Set (E n)} (c : Cell r k O)
    (f : E k → E n) (U : Set (E k)) (hU : IsOpen U) (hsub : cube k ⊆ U)
    (hf : ContDiffOn ℝ 1 f U) (heq : ∀ x : cube k, f x = (c.toFun x).val)
    (x : cube k),
  totalDerivative (cellExtension c) x = totalDerivative f x

def cellCoefficient_extension_independentType : Prop :=
  ∀ {r k n} {O : Set (E n)} (c : Cell r k O)
    (f : E k → E n) (U : Set (E k)) (hU : IsOpen U) (hsub : cube k ⊆ U)
    (hf : ContDiffOn ℝ 1 f U) (heq : ∀ x : cube k, f x = (c.toFun x).val)
    (omega : FormField n k) (x : cube k),
  cellCoefficient c omega x = pullback f omega x (fun j => standardBasis k j)

def cell_pullback_topType : Prop :=
  ∀ {r k n} {O : Set (E n)} (c : Cell r k O)
    (omega : FormField n k) (x : E k),
  pullback (cellExtension c) omega x = cellCoefficient c omega x • volumeForm k

def cellIntegral_extension_independentType : Prop :=
  ∀ {r k n} {O : Set (E n)} (c : Cell r k O)
    (f : E k → E n) (U : Set (E k)) (hU : IsOpen U) (hsub : cube k ⊆ U)
    (hf : ContDiffOn ℝ 1 f U) (heq : ∀ x : cube k, f x = (c.toFun x).val)
    (omega : FormField n k),
  cellIntegral c omega = Specs.D04.C06.DarbouxIntegral.Model.lowerIntegral
      (fun x => pullback f omega x (fun j => standardBasis k j)) (cubeBox k)

def cellIntegral_existsType : Prop :=
  ∀ {r k n} {O : Set (E n)} (c : Cell r k O)
    (omega : FormField n k) (h : IsCrForm (some 0) O omega),
  ∃ hi : Specs.D04.C06.DarbouxIntegral.Model.Integrable (cellCoefficient c omega) (cubeBox k),
      cellIntegral c omega = Specs.D04.C06.DarbouxIntegral.Model.integral (cellCoefficient c omega) (cubeBox k) hi

def chainIntegral_addType : Prop :=
  ∀ {r k n} {O : Set (E n)} (omega : FormField n k)
    (C D : Chain r k O),
  chainIntegral omega (C + D) = chainIntegral omega C + chainIntegral omega D

def chainBoundary_addType : Prop :=
  ∀ {r k n} {O : Set (E n)} (C D : Chain r k O),
  chainBoundary k (C + D) = chainBoundary k C + chainBoundary k D

def extension_into_targetType : Prop :=
  ∀ {r k n} {O : Set (E n)} (c : Cell r k O),
    ∃ U : Set (E k), IsOpen U ∧ cube k ⊆ U ∧
      ContDiffOn ℝ (r : ℕ∞ω) (cellExtension c) U ∧ MapsTo (cellExtension c) U O

end Specs.D04.C15.CellsChainsAndIntegrals
