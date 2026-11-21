import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Localization.Partitions
import Mathlib.Topology.Germ
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! Canonical objects for the germ/derivation model of tangent spaces.

The generated subalgebras below have an exact smooth-representative
characterization among the implementation targets. Thus the use of `adjoin`
does not impose an additional analytic hypothesis on a germ.
-/
namespace SmoothManifolds.TangentData
open ModelData AtlasData PartitionData Set Filter
open scoped Topology
universe u v

instance germRealAlgebra {M : Type u} [TopologicalSpace M] (p : M) :
    Algebra ℝ (Germ (𝓝 p) ℝ) :=
  ((Germ.coeRingHom (𝓝 p)).comp (Pi.constRingHom M ℝ)).toAlgebra

def smoothGermAlgebra {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (p : M) : Subalgebra ℝ (Germ (𝓝 p) ℝ) :=
  Algebra.adjoin ℝ {g | ∃ f : M → ℝ,
    ScalarContDiffAt (⊤ : ℕ∞) S.smoothStructure.val f p ∧ g = Germ.ofFun f}

abbrev SmoothGerm {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (p : M) := ↥(smoothGermAlgebra S p)

def globalSmoothAlgebra {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) : Subalgebra ℝ (M → ℝ) :=
  Algebra.adjoin ℝ {f | ScalarSmooth S.smoothStructure.val f}

abbrev GlobalSmooth {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) := ↥(globalSmoothAlgebra S)

def germEvaluation {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (p : M) : SmoothGerm S p →ₐ[ℝ] ℝ where
  toFun f := f.val.value
  map_one' := rfl
  map_zero' := rfl
  map_add' f g := Germ.valueAddHom.map_add f.val g.val
  map_mul' f g := Germ.valueMulHom.map_mul f.val g.val
  commutes' _ := rfl

def globalEvaluation {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (p : M) : GlobalSmooth S →ₐ[ℝ] ℝ where
  toFun f := f.val p
  map_one' := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

/-- Point derivations on an augmented real algebra. There is no locality or
continuity axiom. Constants are proved to vanish from the displayed rule. -/
def pointDerivations {B : Type v} [CommRing B] [Algebra ℝ B]
    (ε : B →ₐ[ℝ] ℝ) : Submodule ℝ (B →ₗ[ℝ] ℝ) where
  carrier := {D | ∀ f g, D (f * g) = ε f * D g + ε g * D f}
  zero_mem' := by simp
  add_mem' := by
    intro D E hD hE f g
    simp only [LinearMap.add_apply, hD f g, hE f g, mul_add]
    abel
  smul_mem' := by
    intro c D hD f g
    simp only [LinearMap.smul_apply, smul_eq_mul, hD f g, mul_add]
    ring

abbrev PointDerivation {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (p : M) := ↥(pointDerivations (germEvaluation S p))

/-- The shared intrinsic tangent fiber. Its coordinate realization is the
linear equivalence in `coordinate_tangent_modelType`, not a second fiber type. -/
abbrev TangentSpace := @PointDerivation

abbrev GlobalPointDerivation {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (p : M) :=
  ↥(pointDerivations (globalEvaluation S p))

def vanishingIdeal {B : Type v} [CommRing B] [Algebra ℝ B]
    (ε : B →ₐ[ℝ] ℝ) : Ideal B := RingHom.ker ε.toRingHom

/-- The submodule m² inside m, using precisely the ideal square. -/
def squareInIdeal {B : Type v} [CommRing B] [Algebra ℝ B]
    (ε : B →ₐ[ℝ] ℝ) : Submodule ℝ (vanishingIdeal ε) :=
  ((vanishingIdeal ε ^ 2).restrictScalars ℝ).comap
    ((vanishingIdeal ε).subtype.restrictScalars ℝ)

abbrev CotangentQuotient {B : Type v} [CommRing B] [Algebra ℝ B]
    (ε : B →ₐ[ℝ] ℝ) := (vanishingIdeal ε) ⧸ squareInIdeal ε

def cotangentClass {B : Type v} [CommRing B] [Algebra ℝ B]
    (ε : B →ₐ[ℝ] ℝ) : vanishingIdeal ε →ₗ[ℝ] CotangentQuotient ε :=
  (squareInIdeal ε).mkQ

/-- An actual ambient smooth chart representative of a germ. -/
def GermChartExtension {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (p : M) (e : ModelChart n a M)
    (g : SmoothGerm S p) (F : Euclidean n → ℝ) : Prop :=
  (∃ U : Set (Euclidean n), IsOpen U ∧ (e p).val ∈ U ∧ ContDiffOn ℝ (⊤ : ℕ∞) F U) ∧
    Germ.ofFun (fun y => F (e y).val) = g.val

/-- Both endpoint conventions are needed to realize all boundary tangent vectors. -/
inductive CurveSide where
  | twoSided
  | forward
  | backward
  deriving DecidableEq

def curveParameterSet : CurveSide → Set ℝ
  | .twoSided => univ
  | .forward => Ici 0
  | .backward => Iic 0

/-- Smooth curve at zero with the manuscript's local-extension convention.
Values away from the chosen side and neighborhood are irrelevant. -/
def CurveSmoothAt {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (p : M) (side : CurveSide) (c : ℝ → M) : Prop :=
  c 0 = p ∧ ContinuousWithinAt c (curveParameterSet side) 0 ∧
    ∀ e ∈ S.smoothStructure.val, p ∈ e.source →
      ∃ U : Set ℝ, IsOpen U ∧ 0 ∈ U ∧
        ∃ F : ℝ → Euclidean n, ContDiffOn ℝ (⊤ : ℕ∞) F U ∧
          (fun t => (e (c t)).val) =ᶠ[𝓝[curveParameterSet side] 0] F

def CurveRepresentsDerivation {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (p : M) (side : CurveSide) (c : ℝ → M)
    (D : PointDerivation S p) : Prop :=
  CurveSmoothAt S p side c ∧ ∀ (g : SmoothGerm S p) (f : M → ℝ),
    Germ.ofFun f = g.val → HasDerivWithinAt (f ∘ c) (D.val g) (curveParameterSet side) 0

end SmoothManifolds.TangentData

namespace Specs.SmoothManifolds.Tangent.Models
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.PartitionData
  _root_.SmoothManifolds.TangentData
open Set Filter
open scoped Topology
universe u v

def smoothGermAlgebraType :=
  {n : ℕ} → {a : ModelKind} → {M : Type u} → [TopologicalSpace M] → (S : SmoothManifold n a M) → (p : M) → Subalgebra ℝ (Germ (𝓝 p) ℝ)
noncomputable def smoothGermAlgebraValue : smoothGermAlgebraType := @TangentData.smoothGermAlgebra

def SmoothGermType :=
  {n : ℕ} → {a : ModelKind} → {M : Type u} → [TopologicalSpace M] → SmoothManifold n a M → M → Type u
noncomputable def SmoothGermValue : SmoothGermType := @TangentData.SmoothGerm

def globalSmoothAlgebraType :=
  {n : ℕ} → {a : ModelKind} → {M : Type u} → [TopologicalSpace M] → SmoothManifold n a M → Subalgebra ℝ (M → ℝ)
noncomputable def globalSmoothAlgebraValue : globalSmoothAlgebraType := @TangentData.globalSmoothAlgebra

def GlobalSmoothType :=
  {n : ℕ} → {a : ModelKind} → {M : Type u} → [TopologicalSpace M] → SmoothManifold n a M → Type u
noncomputable def GlobalSmoothValue : GlobalSmoothType := @TangentData.GlobalSmooth

def germEvaluationType :=
  {n : ℕ} → {a : ModelKind} → {M : Type u} → [TopologicalSpace M] → (S : SmoothManifold n a M) → (p : M) → SmoothGerm S p →ₐ[ℝ] ℝ
noncomputable def germEvaluationValue : germEvaluationType := @TangentData.germEvaluation

def globalEvaluationType :=
  {n : ℕ} → {a : ModelKind} → {M : Type u} → [TopologicalSpace M] → (S : SmoothManifold n a M) → M → GlobalSmooth S →ₐ[ℝ] ℝ
noncomputable def globalEvaluationValue : globalEvaluationType := @TangentData.globalEvaluation

def pointDerivationsType :=
  {B : Type v} → [CommRing B] → [Algebra ℝ B] → (B →ₐ[ℝ] ℝ) → Submodule ℝ (B →ₗ[ℝ] ℝ)
noncomputable def pointDerivationsValue : pointDerivationsType := @TangentData.pointDerivations

def PointDerivationType :=
  {n : ℕ} → {a : ModelKind} → {M : Type u} → [TopologicalSpace M] → SmoothManifold n a M → M → Type u
noncomputable def PointDerivationValue : PointDerivationType := @TangentData.PointDerivation

def TangentSpaceType := PointDerivationType
noncomputable def TangentSpaceValue : TangentSpaceType := @TangentData.TangentSpace

def GlobalPointDerivationType :=
  {n : ℕ} → {a : ModelKind} → {M : Type u} → [TopologicalSpace M] → SmoothManifold n a M → M → Type u
noncomputable def GlobalPointDerivationValue : GlobalPointDerivationType := @TangentData.GlobalPointDerivation

def vanishingIdealType :=
  {B : Type v} → [CommRing B] → [Algebra ℝ B] → (B →ₐ[ℝ] ℝ) → Ideal B
noncomputable def vanishingIdealValue : vanishingIdealType := @TangentData.vanishingIdeal

def squareInIdealType :=
  {B : Type v} → [CommRing B] → [Algebra ℝ B] → (ε : B →ₐ[ℝ] ℝ) → Submodule ℝ (vanishingIdeal ε)
noncomputable def squareInIdealValue : squareInIdealType := @TangentData.squareInIdeal

def CotangentQuotientType :=
  {B : Type v} → [CommRing B] → [Algebra ℝ B] → (B →ₐ[ℝ] ℝ) → Type v
noncomputable def CotangentQuotientValue : CotangentQuotientType := @TangentData.CotangentQuotient

def cotangentClassType :=
  {B : Type v} → [CommRing B] → [Algebra ℝ B] → (ε : B →ₐ[ℝ] ℝ) → vanishingIdeal ε →ₗ[ℝ] CotangentQuotient ε
noncomputable def cotangentClassValue : cotangentClassType := @TangentData.cotangentClass

def GermChartExtensionType :=
  {n : ℕ} → {a : ModelKind} → {M : Type u} → [TopologicalSpace M] → (S : SmoothManifold n a M) → (p : M) → ModelChart n a M → SmoothGerm S p → (Euclidean n → ℝ) → Prop
noncomputable def GermChartExtensionValue : GermChartExtensionType := @TangentData.GermChartExtension

def CurveSideType :=
  Type
noncomputable def CurveSideValue : CurveSideType := @TangentData.CurveSide

def curveParameterSetType :=
  CurveSide → Set ℝ
noncomputable def curveParameterSetValue : curveParameterSetType := @TangentData.curveParameterSet

def CurveSmoothAtType :=
  {n : ℕ} → {a : ModelKind} → {M : Type u} → [TopologicalSpace M] → SmoothManifold n a M → M → CurveSide → (ℝ → M) → Prop
noncomputable def CurveSmoothAtValue : CurveSmoothAtType := @TangentData.CurveSmoothAt

def CurveRepresentsDerivationType :=
  {n : ℕ} → {a : ModelKind} → {M : Type u} → [TopologicalSpace M] → (S : SmoothManifold n a M) → (p : M) → CurveSide → (ℝ → M) → PointDerivation S p → Prop
noncomputable def CurveRepresentsDerivationValue : CurveRepresentsDerivationType := @TangentData.CurveRepresentsDerivation

def mem_smoothGermAlgebra_iffType :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (p : M) (g : Germ (𝓝 p) ℝ),
    g ∈ smoothGermAlgebra S p ↔ ∃ f : M → ℝ,
      ScalarContDiffAt (⊤ : ℕ∞) S.smoothStructure.val f p ∧ g = Germ.ofFun f

def mem_globalSmoothAlgebra_iffType :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (f : M → ℝ),
    f ∈ globalSmoothAlgebra S ↔ ScalarSmooth S.smoothStructure.val f

def derivation_kills_constantsType :=
  ∀ {B : Type v} [CommRing B] [Algebra ℝ B] (ε : B →ₐ[ℝ] ℝ)
    (D : pointDerivations ε) (c : ℝ), D.val (algebraMap ℝ B c) = 0

def derivation_kills_squareType :=
  ∀ {B : Type v} [CommRing B] [Algebra ℝ B] (ε : B →ₐ[ℝ] ℝ)
    (D : pointDerivations ε) (f : B), f ∈ vanishingIdeal ε ^ 2 → D.val f = 0

def exists_derivationCotangentEquivType :=
  ∀ {B : Type v} [CommRing B] [Algebra ℝ B] (ε : B →ₐ[ℝ] ℝ)
    , ∃ e : pointDerivations ε ≃ₗ[ℝ] Module.Dual ℝ (CotangentQuotient ε),
      ∀ (D : pointDerivations ε) (f : vanishingIdeal ε),
        e D (cotangentClass ε f) = D.val f

def exists_global_representativeType :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (p : M) (f : M → ℝ),
    ScalarContDiffAt (⊤ : ℕ∞) S.smoothStructure.val f p →
    ∃ g : M → ℝ, ScalarSmooth S.smoothStructure.val g ∧ g =ᶠ[𝓝 p] f

def global_derivation_localityType :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (p : M) (D : GlobalPointDerivation S p)
    (f : GlobalSmooth S), f.val =ᶠ[𝓝 p] (fun _ => 0) → D.val f = 0

/-- Global/germ comparison, specified by its effect on every global function. -/
def exists_germGlobalDerivationEquivType :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (p : M),
    ∃ e : PointDerivation S p ≃ₗ[ℝ] GlobalPointDerivation S p,
      ∀ (D : PointDerivation S p) (f : GlobalSmooth S) (g : SmoothGerm S p),
        Germ.ofFun f.val = g.val → (e D).val f = D.val g

/-- Full chart model: coordinates, basis, coordinate tangent space, and
the action on every germ through every ambient smooth representative. -/
def coordinate_tangent_modelType :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (p : M) (e : ModelChart n a M),
    e ∈ S.smoothStructure.val → p ∈ e.source →
    ∃ (coords : Fin n → SmoothGerm S p)
      (b : Module.Basis (Fin n) ℝ (PointDerivation S p))
      (E : PointDerivation S p ≃ₗ[ℝ] Euclidean n),
      (∀ i, (coords i).val = Germ.ofFun (fun y => (e y).val i)) ∧
      (∀ D i, E D i = D.val (coords i)) ∧
      (∀ i, E (b i) = Pi.single i 1) ∧
      ∀ (D : PointDerivation S p) (g : SmoothGerm S p) (F : Euclidean n → ℝ),
        GermChartExtension S p e g F →
        D.val g = ∑ i, D.val (coords i) * fderiv ℝ F (e p).val (Pi.single i 1)

def tangent_dimensionType :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (p : M),
    FiniteDimensional ℝ (PointDerivation S p) ∧
      Module.finrank ℝ (PointDerivation S p) = n

def tangent_zeroType :=
  ∀ {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold 0 a M) (p : M), Subsingleton (PointDerivation S p)

def smooth_curve_defines_derivationType :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (p : M) (side : CurveSide) (c : ℝ → M),
    CurveSmoothAt S p side c →
      ∃! D : PointDerivation S p, CurveRepresentsDerivation S p side c D

def every_derivation_is_curve_velocityType :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (p : M) (D : PointDerivation S p),
    ∃ (side : CurveSide) (c : ℝ → M), CurveRepresentsDerivation S p side c D

def curve_velocity_chart_independentType :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (p : M) (s t : CurveSide) (c d : ℝ → M)
    (D E : PointDerivation S p),
    CurveRepresentsDerivation S p s c D → CurveRepresentsDerivation S p t d E →
    ∀ e ∈ S.smoothStructure.val, p ∈ e.source → ∀ v w : Euclidean n,
      HasDerivWithinAt (fun z => (e (c z)).val) v (curveParameterSet s) 0 →
      HasDerivWithinAt (fun z => (e (d z)).val) w (curveParameterSet t) 0 →
      (v = w ↔ D = E)

end Specs.SmoothManifolds.Tangent.Models
