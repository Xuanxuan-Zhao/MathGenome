import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C02.DerivativeInterfaces
import Mathlib.Topology.Order.LocalExtr
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-! Reference definitions for d04:05:extrema. Functions on a feasible set are
represented by ambient functions restricted to it. Every point predicate includes
membership. No regularity is required for extrema or saddles. Stationarity asserts
an existing open-domain total derivative, rather than merely testing a selector. -/
noncomputable section
open Set Filter Topology
namespace Specs.D04.C05.ExtremaInterfaces
open Specs.D04.C01.EuclideanInterfaces.Model
namespace Model
def LocalMinimumOn : {n : ℕ} → Set (E n) → (E n → ℝ) → E n → Prop :=
  fun S f a => a ∈ S ∧ ∃ r > 0, ∀ x ∈ S, ‖x - a‖ < r → f a ≤ f x

def LocalMaximumOn : {n : ℕ} → Set (E n) → (E n → ℝ) → E n → Prop :=
  fun S f a => a ∈ S ∧ ∃ r > 0, ∀ x ∈ S, ‖x - a‖ < r → f x ≤ f a

def StrictLocalMinimumOn : {n : ℕ} → Set (E n) → (E n → ℝ) → E n → Prop :=
  fun S f a => a ∈ S ∧ ∃ r > 0, ∀ x ∈ S, ‖x - a‖ < r → x ≠ a → f a < f x

def StrictLocalMaximumOn : {n : ℕ} → Set (E n) → (E n → ℝ) → E n → Prop :=
  fun S f a => a ∈ S ∧ ∃ r > 0, ∀ x ∈ S, ‖x - a‖ < r → x ≠ a → f x < f a

def GlobalMinimumOn : {n : ℕ} → Set (E n) → (E n → ℝ) → E n → Prop :=
  fun S f a => a ∈ S ∧ ∀ x ∈ S, f a ≤ f x

def GlobalMaximumOn : {n : ℕ} → Set (E n) → (E n → ℝ) → E n → Prop :=
  fun S f a => a ∈ S ∧ ∀ x ∈ S, f x ≤ f a

def StationaryPoint : {n : ℕ} → Set (E n) → (E n → ℝ) → E n → Prop :=
  fun U f a => Specs.D04.C02.DerivativeInterfaces.Model.HasTotalDerivative U f 0 a

def CriticalPoint : {n : ℕ} → Set (E n) → (E n → ℝ) → E n → Prop :=
  fun U f a => StationaryPoint U f a

def SaddlePoint : {n : ℕ} → Set (E n) → (E n → ℝ) → E n → Prop :=
  fun S f a => a ∈ S ∧ ∀ r > 0,
    (∃ x ∈ S, ‖x - a‖ < r ∧ f a < f x) ∧
    (∃ x ∈ S, ‖x - a‖ < r ∧ f x < f a)

end Model

abbrev LocalMinimumOnType := {n : ℕ} → Set (E n) → (E n → ℝ) → E n → Prop
def LocalMinimumOnValue : LocalMinimumOnType := @Model.LocalMinimumOn

abbrev LocalMaximumOnType := {n : ℕ} → Set (E n) → (E n → ℝ) → E n → Prop
def LocalMaximumOnValue : LocalMaximumOnType := @Model.LocalMaximumOn

abbrev StrictLocalMinimumOnType := {n : ℕ} → Set (E n) → (E n → ℝ) → E n → Prop
def StrictLocalMinimumOnValue : StrictLocalMinimumOnType := @Model.StrictLocalMinimumOn

abbrev StrictLocalMaximumOnType := {n : ℕ} → Set (E n) → (E n → ℝ) → E n → Prop
def StrictLocalMaximumOnValue : StrictLocalMaximumOnType := @Model.StrictLocalMaximumOn

abbrev GlobalMinimumOnType := {n : ℕ} → Set (E n) → (E n → ℝ) → E n → Prop
def GlobalMinimumOnValue : GlobalMinimumOnType := @Model.GlobalMinimumOn

abbrev GlobalMaximumOnType := {n : ℕ} → Set (E n) → (E n → ℝ) → E n → Prop
def GlobalMaximumOnValue : GlobalMaximumOnType := @Model.GlobalMaximumOn

abbrev StationaryPointType := {n : ℕ} → Set (E n) → (E n → ℝ) → E n → Prop
def StationaryPointValue : StationaryPointType := @Model.StationaryPoint

abbrev CriticalPointType := {n : ℕ} → Set (E n) → (E n → ℝ) → E n → Prop
def CriticalPointValue : CriticalPointType := @Model.CriticalPoint

abbrev SaddlePointType := {n : ℕ} → Set (E n) → (E n → ℝ) → E n → Prop
def SaddlePointValue : SaddlePointType := @Model.SaddlePoint

open Model

def localMinimumOn_iffType : Prop :=
  ∀ {n : ℕ} (S : Set (E n)) (f : E n → ℝ) (a : E n),
    LocalMinimumOn S f a ↔ a ∈ S ∧ IsLocalMinOn f S a

def localMaximumOn_iffType : Prop :=
  ∀ {n : ℕ} (S : Set (E n)) (f : E n → ℝ) (a : E n),
    LocalMaximumOn S f a ↔ a ∈ S ∧ IsLocalMaxOn f S a

def globalMinimumOn_iffType : Prop :=
  ∀ {n : ℕ} (S : Set (E n)) (f : E n → ℝ) (a : E n),
    GlobalMinimumOn S f a ↔ a ∈ S ∧ IsMinOn f S a

def globalMaximumOn_iffType : Prop :=
  ∀ {n : ℕ} (S : Set (E n)) (f : E n → ℝ) (a : E n),
    GlobalMaximumOn S f a ↔ a ∈ S ∧ IsMaxOn f S a

def strictLocalMinimumOn_iffType : Prop :=
  ∀ {n : ℕ} (S : Set (E n)) (f : E n → ℝ) (a : E n),
    StrictLocalMinimumOn S f a ↔ a ∈ S ∧ ∀ᶠ x in 𝓝[S \ {a}] a, f a < f x

def strictLocalMaximumOn_iffType : Prop :=
  ∀ {n : ℕ} (S : Set (E n)) (f : E n → ℝ) (a : E n),
    StrictLocalMaximumOn S f a ↔ a ∈ S ∧ ∀ᶠ x in 𝓝[S \ {a}] a, f x < f a

def localMinimumOn_univ_iffType : Prop :=
  ∀ {n : ℕ} (f : E n → ℝ) (a : E n),
    LocalMinimumOn univ f a ↔ IsLocalMin f a

def localMaximumOn_univ_iffType : Prop :=
  ∀ {n : ℕ} (f : E n → ℝ) (a : E n),
    LocalMaximumOn univ f a ↔ IsLocalMax f a

def stationaryPoint_iffType : Prop :=
  ∀ {n : ℕ} (U : Set (E n)) (f : E n → ℝ) (a : E n),
    StationaryPoint U f a ↔ IsOpen U ∧ a ∈ U ∧ DifferentiableAt ℝ f a ∧
      Specs.D04.C02.DerivativeInterfaces.Model.totalDerivative f a = 0

def criticalPoint_iffType : Prop :=
  ∀ {n : ℕ} (U : Set (E n)) (f : E n → ℝ) (a : E n),
    CriticalPoint U f a ↔ StationaryPoint U f a

def saddlePoint_iff_neighborhoodsType : Prop :=
  ∀ {n : ℕ} (S : Set (E n)) (f : E n → ℝ) (a : E n),
    SaddlePoint S f a ↔ a ∈ S ∧ ∀ N ∈ 𝓝 a,
      (∃ x ∈ S, x ∈ N ∧ f a < f x) ∧ (∃ x ∈ S, x ∈ N ∧ f x < f a)

def saddlePoint_iff_not_extremaType : Prop :=
  ∀ {n : ℕ} (S : Set (E n)) (f : E n → ℝ) (a : E n),
    SaddlePoint S f a ↔ a ∈ S ∧ ¬ IsLocalMinOn f S a ∧ ¬ IsLocalMaxOn f S a

def isolated_strict_extremaType : Prop :=
  ∀ {n : ℕ} (S : Set (E n)) (f : E n → ℝ) (a : S),
    IsolatedPoint S a → StrictLocalMinimumOn S f a ∧ StrictLocalMaximumOn S f a

def strict_extrema_are_extremaType : Prop :=
  ∀ {n : ℕ} (S : Set (E n)) (f : E n → ℝ) (a : E n),
    (StrictLocalMinimumOn S f a → LocalMinimumOn S f a) ∧
      (StrictLocalMaximumOn S f a → LocalMaximumOn S f a)

def global_extrema_are_localType : Prop :=
  ∀ {n : ℕ} (S : Set (E n)) (f : E n → ℝ) (a : E n),
    (GlobalMinimumOn S f a → LocalMinimumOn S f a) ∧
      (GlobalMaximumOn S f a → LocalMaximumOn S f a)

def extrema_dimension_zeroType : Prop :=
  ∀ (S : Set (E 0)) (f : E 0 → ℝ) (a : E 0), a ∈ S →
    StrictLocalMinimumOn S f a ∧ StrictLocalMaximumOn S f a

def extrema_congrType : Prop :=
  ∀ {n : ℕ} (S : Set (E n)) (f g : E n → ℝ) (a : E n), EqOn f g S →
    (LocalMinimumOn S f a ↔ LocalMinimumOn S g a) ∧
    (LocalMaximumOn S f a ↔ LocalMaximumOn S g a) ∧
    (StrictLocalMinimumOn S f a ↔ StrictLocalMinimumOn S g a) ∧
    (StrictLocalMaximumOn S f a ↔ StrictLocalMaximumOn S g a) ∧
    (GlobalMinimumOn S f a ↔ GlobalMinimumOn S g a) ∧
    (GlobalMaximumOn S f a ↔ GlobalMaximumOn S g a) ∧
    (SaddlePoint S f a ↔ SaddlePoint S g a)

def feasible_function_extensionType : Prop :=
  ∀ {n : ℕ} (S : Set (E n)) (f : S → ℝ),
    ∃ g : E n → ℝ, ∀ x : S, g x = f x

def local_extrema_subtype_iffType : Prop :=
  ∀ {n : ℕ} (S : Set (E n)) (f : E n → ℝ) (a : S),
    (LocalMinimumOn S f a ↔ IsLocalMin (fun x : S => f x) a) ∧
    (LocalMaximumOn S f a ↔ IsLocalMax (fun x : S => f x) a)

def global_extrema_subtype_iffType : Prop :=
  ∀ {n : ℕ} (S : Set (E n)) (f : E n → ℝ) (a : S),
    (GlobalMinimumOn S f a ↔ IsMinOn (fun x : S => f x) univ a) ∧
    (GlobalMaximumOn S f a ↔ IsMaxOn (fun x : S => f x) univ a)

end Specs.D04.C05.ExtremaInterfaces
