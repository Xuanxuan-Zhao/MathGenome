import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.MeasureTheory.Function.L2Space

/-!
Coordinate direct integrals for paper.tex, fa2:p2:spectral-multiplicity.
Coordinates are numbered from zero: coordinate k is active exactly when k < m(z).
Multiplicity representatives are measurable and positive almost everywhere;
null-set changes are identified by `Multiplicity.AEEq`. No positive-mass
condition is imposed on the finite Borel measure.

A fiber operator is represented by its canonical zero extension to ℓ². The
conditions on the range and orthogonal complement express exactly this, rather
than imposing operator-norm measurability (which would be too restrictive).
Measurability is strong-operator measurability: each constant-vector orbit is
a.e. strongly measurable. Fields and their norm are considered modulo a.e. equality.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology ComplexConjugate

namespace ExpandedFA.VonNeumann.MultiplicityModel.Spec

abbrev SequenceSpace : Type := lp (fun _ : ℕ => ℂ) 2

/-- A measurable representative of a positive finite or infinite multiplicity. -/
structure Multiplicity (μ : Measure ℂ) where
  toFun : ℂ → ℕ∞
  measurable_toFun : Measurable toFun
  positive : ∀ᵐ z ∂μ, 0 < toFun z

instance (μ : Measure ℂ) : CoeFun (Multiplicity μ) (fun _ => ℂ → ℕ∞) :=
  ⟨Multiplicity.toFun⟩

/-- Equality of the multiplicity data, modulo the control measure. -/
def Multiplicity.AEEq {μ : Measure ℂ} (m n : Multiplicity μ) : Prop := m =ᵐ[μ] n

/-- The first d coordinates of ℓ², or all of ℓ² for d = ∞. -/
def fiber (d : ℕ∞) : Submodule ℂ SequenceSpace where
  carrier := {x | ∀ k : ℕ, ¬ (k : ℕ∞) < d → x k = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy k hk
    change x k + y k = 0
    rw [hx k hk, hy k hk, add_zero]
  smul_mem' := by
    intro c x hx k hk
    change c • x k = 0
    rw [hx k hk, smul_zero]

/-- L² sections whose inactive coordinates vanish, on one common conull set. -/
def directIntegralSubmodule (μ : Measure ℂ) (m : Multiplicity μ) :
    Submodule ℂ (Lp SequenceSpace 2 μ) where
  carrier := {f | ∀ᵐ z ∂μ, f z ∈ fiber (m z)}
  zero_mem' := by
    filter_upwards [Lp.coeFn_zero SequenceSpace 2 μ] with z hz
    rw [hz]
    exact (fiber (m z)).zero_mem
  add_mem' := by
    intro f g hf hg
    filter_upwards [hf, hg, Lp.coeFn_add f g] with z hf hg hfg
    rw [hfg]
    exact (fiber (m z)).add_mem hf hg
  smul_mem' := by
    intro c f hf
    filter_upwards [hf, Lp.coeFn_smul c f] with z hf hcf
    rw [hcf]
    exact (fiber (m z)).smul_mem c hf

/-- The inherited L² norm and inner product; completeness is a theorem. -/
abbrev DirectIntegral (μ : Measure ℂ) (m : Multiplicity μ) : Type := directIntegralSubmodule μ m

/-- Canonical zero extensions of bounded operators on the coordinate fibers. -/
def IsFiberOperator (d : ℕ∞) (B : SequenceSpace →L[ℂ] SequenceSpace) : Prop :=
  (∀ x, B x ∈ fiber d) ∧ (∀ x ∈ (fiber d)ᗮ, B x = 0)

/-- Measurable, essentially bounded fields. The second condition uses one
common null set for operator bounds, not separate null sets for each vector. -/
structure OperatorField (μ : Measure ℂ) (m : Multiplicity μ) where
  toFun : ℂ → SequenceSpace →L[ℂ] SequenceSpace
  fiberwise : ∀ᵐ z ∂μ, IsFiberOperator (m z) (toFun z)
  measurable_orbit : ∀ x, AEStronglyMeasurable (fun z => toFun z x) μ
  bounded : ∃ C : ℝ≥0, ∀ᵐ z ∂μ, ‖toFun z‖ ≤ C

instance {μ : Measure ℂ} {m : Multiplicity μ} :
    CoeFun (OperatorField μ m) (fun _ => ℂ → SequenceSpace →L[ℂ] SequenceSpace) :=
  ⟨OperatorField.toFun⟩

def OperatorField.AEEq {μ : Measure ℂ} {m : Multiplicity μ}
    (B C : OperatorField μ m) : Prop := B =ᵐ[μ] C

/-- Extended essential supremum of the actual fiber operator norms. -/
def fieldENorm {μ : Measure ℂ} {m : Multiplicity μ} (B : OperatorField μ m) : ℝ≥0∞ :=
  essSup (fun z => (‖B z‖₊ : ℝ≥0∞)) μ

/-- Finite real essential-sup norm (also zero for the zero measure). -/
def fieldNorm {μ : Measure ℂ} {m : Multiplicity μ} (B : OperatorField μ m) : ℝ :=
  (fieldENorm B).toReal

/-- The field itself modulo equality off a μ-null set. -/
def fieldSetoid (μ : Measure ℂ) (m : Multiplicity μ) : Setoid (OperatorField μ m) where
  r := OperatorField.AEEq
  iseqv := ⟨fun _ => Filter.EventuallyEq.rfl,
    fun h => h.symm, fun h h' => h.trans h'⟩

abbrev EssentialOperatorField (μ : Measure ℂ) (m : Multiplicity μ) :=
  Quotient (fieldSetoid μ m)

/-- Strong-operator measurability suffices for arbitrary measurable sections;
no measurability in the operator norm topology is needed. -/
theorem measurable_field_apply {μ : Measure ℂ} {m : Multiplicity μ}
    (B : OperatorField μ m) {f : ℂ → SequenceSpace} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun z => B z (f z)) μ := by
  classical
  have hs (s : SimpleFunc ℂ SequenceSpace) :
      AEStronglyMeasurable (fun z => B z (s z)) μ := by
    induction s using SimpleFunc.induction' with
    | const c => exact B.measurable_orbit c
    | @pcw s t A hA hs ht =>
      convert hs.restrict.piecewise hA.nullMeasurableSet ht.restrict using 1
      funext z
      by_cases hz : z ∈ A <;> simp [SimpleFunc.piecewise_apply, Set.piecewise, hz]
  have hlim : ∀ᵐ z ∂μ, Tendsto
      (fun n => B z (hf.stronglyMeasurable_mk.approx n z)) atTop (𝓝 (B z (f z))) := by
    filter_upwards [hf.ae_eq_mk] with z hz
    rw [hz]
    exact (B z).continuous.continuousAt.tendsto.comp
      (hf.stronglyMeasurable_mk.tendsto_approx z)
  exact aestronglyMeasurable_of_tendsto_ae atTop (fun n => hs _) hlim

theorem fieldENorm_lt_top {μ : Measure ℂ} {m : Multiplicity μ} (B : OperatorField μ m) :
    fieldENorm B < ∞ := by
  obtain ⟨C, hC⟩ := B.bounded
  apply lt_of_le_of_lt (essSup_le_of_ae_le (C : ℝ≥0∞) ?_) (ENNReal.coe_lt_top)
  filter_upwards [hC] with z hz
  exact_mod_cast hz

theorem ae_norm_le_fieldNorm {μ : Measure ℂ} {m : Multiplicity μ} (B : OperatorField μ m) :
    ∀ᵐ z ∂μ, ‖B z‖ ≤ fieldNorm B := by
  filter_upwards [ENNReal.ae_le_essSup (fun z => (‖B z‖₊ : ℝ≥0∞)) (μ := μ)] with z hz
  exact_mod_cast ENNReal.toReal_mono (fieldENorm_lt_top B).ne hz

theorem field_apply_memLp {μ : Measure ℂ} {m : Multiplicity μ}
    (B : OperatorField μ m) (f : Lp SequenceSpace 2 μ) :
    MemLp (fun z => B z (f z)) 2 μ := by
  apply (Lp.memLp f).of_le_mul (measurable_field_apply B (Lp.aestronglyMeasurable f))
    (c := fieldNorm B)
  filter_upwards [ae_norm_le_fieldNorm B] with z hz
  exact (B z).le_opNorm (f z) |>.trans (mul_le_mul_of_nonneg_right hz (norm_nonneg _))


/-- Essentially bounded coordinate on the measure support. -/
def BoundedCoordinate (μ : Measure ℂ) : Prop :=
  ∃ R : ℝ≥0, ∀ᵐ z ∂μ, ‖z‖ ≤ R

/-- Identification of the section space with the stated coordinate condition. -/
def SectionMembership : Prop :=
  ∀ (μ : Measure ℂ) (m : Multiplicity μ) (f : Lp SequenceSpace 2 μ),
    f ∈ directIntegralSubmodule μ m ↔
      ∀ᵐ z ∂μ, ∀ k : ℕ, ¬ (k : ℕ∞) < m z → f z k = 0

def ClosedSectionSpace : Prop :=
  ∀ (μ : Measure ℂ) (m : Multiplicity μ), IsClosed (directIntegralSubmodule μ m : Set (Lp SequenceSpace 2 μ))

def MultiplicityInvariance : Prop :=
  ∀ (μ : Measure ℂ) (m n : Multiplicity μ), m.AEEq n →
    directIntegralSubmodule μ m = directIntegralSubmodule μ n

/-- Every fiber operator has a canonical zero extension, with its norm preserved. -/
def FiberExtension : Prop :=
  ∀ (d : ℕ∞) (B : fiber d →L[ℂ] fiber d),
    ∃ T : SequenceSpace →L[ℂ] SequenceSpace,
      IsFiberOperator d T ∧ (∀ x : fiber d, T x = B x) ∧ ‖T‖ = ‖B‖

/-- Action must be an actual bounded operator with pointwise fiber action. -/
def FieldActionType : Type :=
  ∀ {μ : Measure ℂ} {m : Multiplicity μ},
    OperatorField μ m → DirectIntegral μ m →L[ℂ] DirectIntegral μ m

/-- The defining property fully determines the field action on L² classes. -/
def FieldActionProperty (action : FieldActionType) : Prop :=
  ∀ {μ : Measure ℂ} {m : Multiplicity μ} (B : OperatorField μ m)
    (f : DirectIntegral μ m),
    ((action B f : DirectIntegral μ m) : Lp SequenceSpace 2 μ) =ᵐ[μ]
      fun z => B z ((f : Lp SequenceSpace 2 μ) z)

/-- The pointwise action on ambient L² classes. -/
def applyLpValue {μ : Measure ℂ} {m : Multiplicity μ}
    (B : OperatorField μ m) (f : Lp SequenceSpace 2 μ) : Lp SequenceSpace 2 μ :=
  (field_apply_memLp B f).toLp (fun z => B z (f z))

lemma applyLpValue_ae {μ : Measure ℂ} {m : Multiplicity μ}
    (B : OperatorField μ m) (f : Lp SequenceSpace 2 μ) :
    applyLpValue B f =ᵐ[μ] fun z => B z (f z) := MemLp.coeFn_toLp _

def applyLpLinear {μ : Measure ℂ} {m : Multiplicity μ}
    (B : OperatorField μ m) : Lp SequenceSpace 2 μ →ₗ[ℂ] Lp SequenceSpace 2 μ where
  toFun := applyLpValue B
  map_add' f g := by
    apply Lp.ext
    filter_upwards [applyLpValue_ae B (f + g), applyLpValue_ae B f,
      applyLpValue_ae B g, Lp.coeFn_add f g,
      Lp.coeFn_add (applyLpValue B f) (applyLpValue B g)] with z h1 h2 h3 h4 h5
    simp only [h1, h2, h3, h4, h5, Pi.add_apply, map_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [applyLpValue_ae B (c • f), applyLpValue_ae B f,
      Lp.coeFn_smul c f, Lp.coeFn_smul c (applyLpValue B f)] with z h1 h2 h3 h4
    simp only [h1, h2, h3, h4, Pi.smul_apply, map_smul, RingHom.id_apply]

lemma applyLpValue_supported {μ : Measure ℂ} {m : Multiplicity μ}
    (B : OperatorField μ m) (f : Lp SequenceSpace 2 μ) :
    applyLpValue B f ∈ directIntegralSubmodule μ m := by
  filter_upwards [applyLpValue_ae B f, B.fiberwise] with z hz hB
  rw [hz]
  exact hB.1 _

lemma applyLpValue_bound {μ : Measure ℂ} {m : Multiplicity μ}
    (B : OperatorField μ m) (f : Lp SequenceSpace 2 μ) :
    ‖applyLpValue B f‖ ≤ fieldNorm B * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [applyLpValue_ae B f, ae_norm_le_fieldNorm B] with z hz hB
  rw [hz]
  exact (B z).le_opNorm _ |>.trans (mul_le_mul_of_nonneg_right hB (norm_nonneg _))

/-- Canonical bounded fiberwise action, built from the actual L² classes. -/
def fieldActionValue : FieldActionType := fun {μ m} B =>
  (((applyLpLinear B).comp (directIntegralSubmodule μ m).subtype).codRestrict
    (directIntegralSubmodule μ m) (fun f => applyLpValue_supported B f)).mkContinuous
      (fieldNorm B) (fun f => applyLpValue_bound B f)

/-- Coordinate multiplication is defined under exactly essential boundedness. -/
def CoordinateOperatorType : Type :=
  ∀ (μ : Measure ℂ) (m : Multiplicity μ), BoundedCoordinate μ →
    (DirectIntegral μ m →L[ℂ] DirectIntegral μ m)

def CoordinateOperatorProperty (coordinate : CoordinateOperatorType) : Prop :=
  ∀ (μ : Measure ℂ) (m : Multiplicity μ) (h : BoundedCoordinate μ)
    (f : DirectIntegral μ m),
    ((coordinate μ m h f : DirectIntegral μ m) : Lp SequenceSpace 2 μ) =ᵐ[μ]
      fun z => z • ((f : Lp SequenceSpace 2 μ) z)

/-- The bound is chosen only to establish L² integrability; the resulting
operator is independent of the chosen bound by a.e. extensionality. -/
lemma coordinate_memLp {μ : Measure ℂ} (h : BoundedCoordinate μ)
    (f : Lp SequenceSpace 2 μ) : MemLp (fun z => z • f z) 2 μ := by
  obtain ⟨R, hR⟩ := h
  apply (Lp.memLp f).of_le_mul
    (measurable_id.aestronglyMeasurable.smul (Lp.aestronglyMeasurable f)) (c := (R : ℝ))
  filter_upwards [hR] with z hz
  change ‖z • f z‖ ≤ _
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right hz (norm_nonneg _)

def coordinateLpValue {μ : Measure ℂ} (h : BoundedCoordinate μ)
    (f : Lp SequenceSpace 2 μ) : Lp SequenceSpace 2 μ :=
  (coordinate_memLp h f).toLp (fun z => z • f z)

lemma coordinateLpValue_ae {μ : Measure ℂ} (h : BoundedCoordinate μ)
    (f : Lp SequenceSpace 2 μ) :
    coordinateLpValue h f =ᵐ[μ] fun z => z • f z := MemLp.coeFn_toLp _

def coordinateLpLinear {μ : Measure ℂ} (h : BoundedCoordinate μ) :
    Lp SequenceSpace 2 μ →ₗ[ℂ] Lp SequenceSpace 2 μ where
  toFun := coordinateLpValue h
  map_add' f g := by
    apply Lp.ext
    filter_upwards [coordinateLpValue_ae h (f + g), coordinateLpValue_ae h f,
      coordinateLpValue_ae h g, Lp.coeFn_add f g,
      Lp.coeFn_add (coordinateLpValue h f) (coordinateLpValue h g)] with z h1 h2 h3 h4 h5
    simp only [h1, h2, h3, h4, h5, Pi.add_apply, smul_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [coordinateLpValue_ae h (c • f), coordinateLpValue_ae h f,
      Lp.coeFn_smul c f, Lp.coeFn_smul c (coordinateLpValue h f)] with z h1 h2 h3 h4
    simp only [RingHom.id_apply, h1, h2, h3, h4, Pi.smul_apply]
    exact smul_comm z c (f z)

lemma coordinateLpValue_supported {μ : Measure ℂ} (m : Multiplicity μ)
    (h : BoundedCoordinate μ) (f : Lp SequenceSpace 2 μ)
    (hf : f ∈ directIntegralSubmodule μ m) :
    coordinateLpValue h f ∈ directIntegralSubmodule μ m := by
  change ∀ᵐ z ∂μ, f z ∈ fiber (m z) at hf
  change ∀ᵐ z ∂μ, coordinateLpValue h f z ∈ fiber (m z)
  filter_upwards [coordinateLpValue_ae h f, hf] with z hz hfz
  rw [hz]
  exact (fiber (m z)).smul_mem z hfz

def coordinateLinear {μ : Measure ℂ} (m : Multiplicity μ) (h : BoundedCoordinate μ) :
    DirectIntegral μ m →ₗ[ℂ] DirectIntegral μ m :=
  (((coordinateLpLinear h).comp (directIntegralSubmodule μ m).subtype).codRestrict
    (directIntegralSubmodule μ m) (fun f => coordinateLpValue_supported m h f f.property))

lemma coordinateLinear_bound {μ : Measure ℂ} (m : Multiplicity μ) (h : BoundedCoordinate μ)
    (f : DirectIntegral μ m) :
    ‖coordinateLinear m h f‖ ≤ (h.choose : ℝ) * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [coordinateLpValue_ae h f, h.choose_spec] with z hz hR
  change ‖coordinateLpValue h (f : Lp SequenceSpace 2 μ) z‖ ≤ _
  rw [hz, norm_smul]
  exact mul_le_mul_of_nonneg_right hR (norm_nonneg _)

/-- Multiplication by the coordinate, with precisely essential boundedness as hypothesis. -/
def coordinateOperatorValue : CoordinateOperatorType := fun _ m h =>
  (coordinateLinear m h).mkContinuous (h.choose : ℝ) (coordinateLinear_bound m h)

lemma fieldActionValue_congr {μ : Measure ℂ} {m : Multiplicity μ}
    {B C : OperatorField μ m} (h : B.AEEq C) : fieldActionValue B = fieldActionValue C := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [applyLpValue_ae B f, applyLpValue_ae C f, h] with z hB hC hz
  change applyLpValue B (f : Lp SequenceSpace 2 μ) z = applyLpValue C (f : Lp SequenceSpace 2 μ) z
  rw [hB, hC, hz]

lemma fieldNorm_congr {μ : Measure ℂ} {m : Multiplicity μ}
    {B C : OperatorField μ m} (h : B.AEEq C) : fieldNorm B = fieldNorm C := by
  apply congrArg ENNReal.toReal
  apply essSup_congr_ae
  filter_upwards [h] with z hz
  rw [hz]

/-- The norm and action descend to actual equivalence classes of fields. -/
def essentialFieldNormValue {μ : Measure ℂ} {m : Multiplicity μ}
    (B : EssentialOperatorField μ m) : ℝ :=
  Quotient.lift fieldNorm (fun _ _ h => fieldNorm_congr h) B

def essentialFieldActionValue {μ : Measure ℂ} {m : Multiplicity μ}
    (B : EssentialOperatorField μ m) : DirectIntegral μ m →L[ℂ] DirectIntegral μ m :=
  Quotient.lift fieldActionValue (fun _ _ h => fieldActionValue_congr h) B

/-- Restriction of a canonical ambient operator to its actual fiber. -/
def restrictFiberValue {d : ℕ∞} (B : SequenceSpace →L[ℂ] SequenceSpace)
    (hB : IsFiberOperator d B) : fiber d →L[ℂ] fiber d :=
  (B.codRestrict (fiber d) hB.1).domRestrict (fiber d)

def FiberOperatorNorm : Prop :=
  ∀ (d : ℕ∞) (B : SequenceSpace →L[ℂ] SequenceSpace) (hB : IsFiberOperator d B),
    ‖B‖ = ‖restrictFiberValue B hB‖

def FieldActionBound : Prop :=
  ∀ {μ : Measure ℂ} {m : Multiplicity μ} (B : OperatorField μ m),
    ‖fieldActionValue B‖ ≤ fieldNorm B

def CoordinateBound : Prop :=
  ∀ (μ : Measure ℂ) (m : Multiplicity μ) (h : BoundedCoordinate μ)
    (R : ℝ≥0), (∀ᵐ z ∂μ, ‖z‖ ≤ R) → ‖coordinateOperatorValue μ m h‖ ≤ R

def FieldNormFinite : Prop :=
  ∀ {μ : Measure ℂ} {m : Multiplicity μ} (B : OperatorField μ m), fieldENorm B < ∞

def FieldNormZero : Prop :=
  ∀ {μ : Measure ℂ} {m : Multiplicity μ} (B : OperatorField μ m),
    fieldNorm B = 0 ↔ ∀ᵐ z ∂μ, B z = 0

/- Independent types and canonical values of the exported definitions. -/
def SequenceSpaceType : Type 1 := Type
def MultiplicityType : Type 1 := Measure ℂ → Type
def FiberType := ℕ∞ → Submodule ℂ SequenceSpace
def DirectIntegralSubmoduleType :=
  ∀ (μ : Measure ℂ), Multiplicity μ → Submodule ℂ (Lp SequenceSpace 2 μ)
def DirectIntegralType : Type 1 := ∀ (μ : Measure ℂ), Multiplicity μ → Type
def OperatorFieldType : Type 1 := ∀ (μ : Measure ℂ), Multiplicity μ → Type
def EssentialOperatorFieldType : Type 1 := ∀ (μ : Measure ℂ), Multiplicity μ → Type
def FieldENormType := ∀ {μ : Measure ℂ} {m : Multiplicity μ}, OperatorField μ m → ℝ≥0∞
def FieldNormType := ∀ {μ : Measure ℂ} {m : Multiplicity μ}, OperatorField μ m → ℝ
def BoundedCoordinateType := Measure ℂ → Prop
def EssentialFieldNormType :=
  ∀ {μ : Measure ℂ} {m : Multiplicity μ}, EssentialOperatorField μ m → ℝ
def EssentialFieldActionType := ∀ {μ : Measure ℂ} {m : Multiplicity μ},
  EssentialOperatorField μ m → (DirectIntegral μ m →L[ℂ] DirectIntegral μ m)

def CanonicalFieldActionProperty : Prop := FieldActionProperty (@fieldActionValue)
def CanonicalCoordinateOperatorProperty : Prop := CoordinateOperatorProperty coordinateOperatorValue

def MultiplicityValue : MultiplicityType := Multiplicity
def OperatorFieldValue : OperatorFieldType := OperatorField

end ExpandedFA.VonNeumann.MultiplicityModel.Spec
