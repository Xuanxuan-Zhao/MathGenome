import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C13.NormalizedFormsAndWedge
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C02.DerivativeBridge

/-! Pullback of the shared coefficient-defined Euclidean forms. Ambient functions
represent maps on open sets; algebraic statements are pointwise, and calculus
statements specify the open domains explicitly. -/
noncomputable section
open scoped BigOperators
open Set
namespace Specs.D04.C13.PullbackCalculus
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C02.DerivativeBridge.Model
open Specs.D04.C13.NormalizedFormsAndWedge.Model
namespace Model

def pullback {m n k : ℕ} (f : E m → E n) (ω : FormField n k) : FormField m k :=
  fun x => (ω (f x)).compLinearMap (totalDerivative f x).toLinearMap

def coordinateOneForm (n : ℕ) (i : Fin n) : Covector (E n) 1 :=
  linearCovector ((standardBasis n).coord i)

def volumeForm (n : ℕ) : Covector (E n) n :=
  wedgeList n (fun i => (standardBasis n).coord i)
/-- The C¹ map with coordinate expression t ↦ t |t|. -/
def roughMap (x : E 1) : E 1 := (x 0 * |x 0|) • standardBasis 1 0
end Model
open Model

abbrev pullbackType := {m n k : ℕ} → (E m → E n) → FormField n k → FormField m k
def pullbackValue : pullbackType := @Model.pullback
abbrev coordinateOneFormType := (n : ℕ) → Fin n → Covector (E n) 1
def coordinateOneFormValue : coordinateOneFormType := Model.coordinateOneForm
abbrev volumeFormType := (n : ℕ) → Covector (E n) n
def volumeFormValue : volumeFormType := Model.volumeForm

def pullback_applyType : Prop :=
  ∀ {m n k : ℕ} (f : E m → E n) (ω : FormField n k) (x : E m) (v : Fin k → E m),
    pullback f ω x v = ω (f x) (fun i => totalDerivative f x (v i))

def pullback_zero_degreeType : Prop :=
  ∀ {m n : ℕ} (f : E m → E n) (a : E n → ℝ),
    pullback f (fun y => scalarCovector (a y)) = fun x => scalarCovector (a (f x))

def pullback_addType : Prop :=
  ∀ {m n k : ℕ} (f : E m → E n) (α β : FormField n k),
    pullback f (fun y => α y + β y) = fun x => pullback f α x + pullback f β x

def pullback_smulType : Prop :=
  ∀ {m n k : ℕ} (f : E m → E n) (a : E n → ℝ) (ω : FormField n k),
    pullback f (fun y => a y • ω y) = fun x => a (f x) • pullback f ω x

def pullback_wedgeType : Prop :=
  ∀ {m n p q : ℕ} (f : E m → E n) (α : FormField n p) (β : FormField n q),
    pullback f (fun y => wedge (α y) (β y)) =
      fun x => wedge (pullback f α x) (pullback f β x)

def pullback_compType : Prop :=
  ∀ {m n l k : ℕ} (U : Set (E m)) (V : Set (E n)) (W : Set (E l))
    (f : E m → E n) (g : E n → E l) (ω : FormField l k)
    (x : E m), MapsTo f U V → MapsTo g V W → x ∈ U →
    TotalDifferentiableOn U f → TotalDifferentiableOn V g →
    pullback (g ∘ f) ω x = pullback f (pullback g ω) x

def pullback_coordinateType : Prop :=
  ∀ {m n : ℕ} (U : Set (E m)) (f : E m → E n) (x : E m) (i : Fin n),
    TotalDifferentiableAt U f x →
    pullback f (fun _ => coordinateOneForm n i) x =
      ∑ j : Fin m, scalarPartialDerivative (fun y => f y i) x j • coordinateOneForm m j

def pullback_volumeType : Prop :=
  ∀ {n : ℕ} (f : E n → E n) (a : E n → ℝ) (x : E n),
    pullback f (fun y => a y • volumeForm n) x =
      (a (f x) * Matrix.det (jacobian f x)) • volumeForm n

def pullback_isCrFormType : Prop :=
  ∀ {m n k : ℕ} (r : ℕ) (U : Set (E m)) (V : Set (E n))
    (f : E m → E n) (ω : FormField n k), IsOpen U → MapsTo f U V →
    CrOn (r + 1) U f → IsCrForm (some r) V ω → IsCrForm (some r) U (pullback f ω)

def pullback_continuousType : Prop :=
  ∀ {m n k : ℕ} (U : Set (E m)) (V : Set (E n))
    (f : E m → E n) (ω : FormField n k), IsOpen U → MapsTo f U V →
    CrOn 1 U f → IsCrForm (some 0) V ω → IsCrForm (some 0) U (pullback f ω)

def pullback_smoothType : Prop :=
  ∀ {m n k : ℕ} (U : Set (E m)) (V : Set (E n))
    (f : E m → E n) (ω : FormField n k), IsOpen U → MapsTo f U V →
    SmoothOn U f → IsCrForm none V ω → IsCrForm none U (pullback f ω)

abbrev roughMapType := E 1 → E 1
def roughMapValue : roughMapType := Model.roughMap

def roughMap_crOnType : Prop := CrOn 1 Set.univ roughMap

def coordinateOneForm_smoothType : Prop :=
  ∀ (n : ℕ) (i : Fin n), IsCrForm none Set.univ (fun _ => coordinateOneForm n i)

def roughMap_pullbackType : Prop :=
  ∀ x : E 1, pullback roughMap (fun _ => coordinateOneForm 1 0) x =
    (2 * |x 0|) • coordinateOneForm 1 0

def roughMap_pullback_not_C1Type : Prop :=
  ∀ (U : Set (E 1)), IsOpen U → (0 : E 1) ∈ U →
    ¬ IsCrForm (some 1) U (pullback roughMap (fun _ => coordinateOneForm 1 0))

end Specs.D04.C13.PullbackCalculus
