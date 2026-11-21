import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.LeviCivita
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.TorsionAndMetric
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch05.MetricSplittings
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-! Theorem 6.3: the smooth Levi–Civita connection, Koszul and coordinate
formulas, and naturality under arbitrary local isometries. -/
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace P202.Geometry.LeviCivita
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.BundleData
  P202.ConnectionData P202.MetricData P202.TorsionMetricData P202.LeviCivitaData
open Filter
open scoped Topology Matrix
universe u

section Koszul
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M}

theorem tangent_sub_as_add (p : M) (v w : TangentSpace S p) :
    v - w = v + (-1 : ℝ) • w := by
  apply Subtype.ext
  apply LinearMap.ext
  intro f
  change v.val f - w.val f = v.val f + (-1 : ℝ) * w.val f
  ring

theorem bracket_eq_cov_sub
    (hf : P202Specs.Geometry.TorsionAndMetric.torsion_formulaType.{u})
    (C : Connection (tangentBundle S)) (hC : IsTorsionFree C)
    (X Y : Field S) (p : M) :
    (bracket X Y).val p = (C.cov X Y).val p - (C.cov Y X).val p := by
  have h := hf C X Y p
  rw [hC X Y] at h
  change 0 = _ at h
  exact (sub_eq_zero.mp h.symm).symm

theorem koszul_of_leviCivita
    (hf : P202Specs.Geometry.TorsionAndMetric.torsion_formulaType.{u})
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) (X Y Z : Field S) (p : M) :
    2 * pairing g p ((C.cov X Y).val p) (Z.val p) = koszulRHS g X Y Z p := by
  unfold koszulRHS
  rw [hC.2 X Y Z p, hC.2 Y Z X p, hC.2 Z X Y p,
    bracket_eq_cov_sub hf C hC.1 Y Z p,
    bracket_eq_cov_sub hf C hC.1 Z X p,
    bracket_eq_cov_sub hf C hC.1 X Y p]
  simp only [tangent_sub_as_add, pairing, LinearMap.BilinForm.add_right,
    LinearMap.BilinForm.smul_right]
  rw [g.symmetric p (Y.val p) ((C.cov X Z).val p),
    g.symmetric p ((C.cov Y Z).val p) (X.val p),
    g.symmetric p (Z.val p) ((C.cov Y X).val p),
    g.symmetric p ((C.cov Z X).val p) (Y.val p),
    g.symmetric p (Z.val p) ((C.cov X Y).val p)]
  ring

/-- Positive definiteness and the extension theorem allow all global smooth
fields to test equality of vectors in a single actual tangent fiber. -/
theorem pairing_ext (g : RiemannianMetric S) (p : M)
    {v w : TangentSpace S p}
    (h : ∀ Z : Field S, pairing g p v (Z.val p) = pairing g p w (Z.val p)) :
    v = w := by
  obtain ⟨Z, hZ⟩ := ConnectionForms.section_evaluation_surjective
    (tangentBundle S) p (v - w)
  have he := h Z
  rw [hZ] at he
  by_contra hne
  have hp := g.positive p (v - w) (sub_ne_zero.mpr hne)
  have hz : pairing g p (v - w) (v - w) = 0 := by
    rw [tangent_sub_as_add p v w]
    change (g.form p) (v + (-1 : ℝ) • w) (v + (-1 : ℝ) • w) = 0
    rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left]
    rw [tangent_sub_as_add p v w] at he
    change (g.form p) v (v + (-1 : ℝ) • w) = (g.form p) w (v + (-1 : ℝ) • w) at he
    linarith
  exact (ne_of_gt hp) hz

theorem connection_ext (C D : Connection (tangentBundle S))
    (h : ∀ (X Y : Field S) (p : M), (C.cov X Y).val p = (D.cov X Y).val p) :
    C = D := by
  have he : C.cov = D.cov := by
    apply LinearMap.ext
    intro X
    apply LinearMap.ext
    intro Y
    exact Subtype.ext (funext (h X Y))
  cases C
  cases D
  cases he
  rfl

theorem uniqueness_of_koszul (g : RiemannianMetric S)
    (C D : Connection (tangentBundle S))
    (hC : ∀ (X Y Z : Field S) (p : M),
      2 * pairing g p ((C.cov X Y).val p) (Z.val p) = koszulRHS g X Y Z p)
    (hD : ∀ (X Y Z : Field S) (p : M),
      2 * pairing g p ((D.cov X Y).val p) (Z.val p) = koszulRHS g X Y Z p) :
    C = D := by
  apply connection_ext
  intro X Y p
  apply pairing_ext g p
  intro Z
  linarith [hC X Y Z p, hD X Y Z p]

end Koszul

section Construction
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M}

noncomputable local instance fieldAddCommGroup : AddCommGroup (Field S) :=
  Module.addCommMonoidToAddCommGroup ℝ

theorem originalBracket_operation : SmoothManifolds.LieBracketData.BracketOperation
    (originalBracket (S := S)) :=
  (Classical.choose_spec (SmoothManifolds.LieBrackets.bracket_exists S
    (tangentStructure S))).1

theorem bracket_swap (X Y : Field S) : bracket Y X = -bracket X Y := by
  apply Subtype.ext
  funext p
  exact ((SmoothManifolds.LieBrackets.bracket_algebra S (tangentStructure S)).2.2
    _ originalBracket_operation).1 (originalField S Y) (originalField S X) p |>.trans (by
      apply Subtype.ext; apply LinearMap.ext; intro f
      change -((bracket X Y).val p).val f = (-1 : ℝ) * ((bracket X Y).val p).val f
      ring)

@[simp] theorem bracket_add_left (X Y Z : Field S) :
    bracket (X + Y) Z = bracket X Z + bracket Y Z := by
  apply Subtype.ext
  funext p
  exact ((SmoothManifolds.LieBrackets.bracket_algebra S (tangentStructure S)).2.2
    _ originalBracket_operation).2.2.1 (originalField S X) (originalField S Y)
      (originalField S Z) (originalField S (X + Y)) (fun _ => rfl) p

theorem bracket_add_right (X Y Z : Field S) :
    bracket X (Y + Z) = bracket X Y + bracket X Z := by
  apply Subtype.ext
  funext p
  exact ((SmoothManifolds.LieBrackets.bracket_algebra S (tangentStructure S)).2.2
    _ originalBracket_operation).2.2.2.1 (originalField S X) (originalField S Y)
      (originalField S Z) (originalField S (Y + Z)) (fun _ => rfl) p

theorem bracket_smul_left (c : ℝ) (X Y : Field S) :
    bracket (c • X) Y = c • bracket X Y := by
  apply Subtype.ext
  funext p
  exact ((SmoothManifolds.LieBrackets.bracket_algebra S (tangentStructure S)).2.2
    _ originalBracket_operation).2.2.2.2.1 c (originalField S X) (originalField S Y)
      (originalField S (c • X)) (fun _ => rfl) p

theorem bracket_smul_right (c : ℝ) (X Y : Field S) :
    bracket X (c • Y) = c • bracket X Y := by
  apply Subtype.ext
  funext p
  exact ((SmoothManifolds.LieBrackets.bracket_algebra S (tangentStructure S)).2.2
    _ originalBracket_operation).2.2.2.2.2.1 c (originalField S X) (originalField S Y)
      (originalField S (c • Y)) (fun _ => rfl) p

theorem bracket_mul_right (f : GlobalSmooth S) (X Y : Field S) :
    bracket X (mulSection f Y) = mulSection f (bracket X Y) +
      mulSection (act S X f) Y := by
  apply Subtype.ext
  funext p
  exact ((SmoothManifolds.LieBrackets.bracket_algebra S (tangentStructure S)).2.2
    _ originalBracket_operation).2.2.2.2.2.2 f (originalField S X) (originalField S Y)
      (originalField S (mulSection f Y)) (act S X)
      (SmoothManifolds.VectorFields.derivationOfField_represents S (tangentStructure S)
        (originalField S X)) (fun _ => rfl) p

theorem bracket_mul_left (f : GlobalSmooth S) (X Y : Field S) :
    bracket (mulSection f X) Y = mulSection f (bracket X Y) -
      mulSection (act S Y f) X := by
  rw [bracket_swap Y (mulSection f X), bracket_mul_right, bracket_swap X Y]
  apply Subtype.ext
  funext p
  apply Subtype.ext; apply LinearMap.ext; intro h
  change (-1 : ℝ) * (f.val p * ((-1 : ℝ) * ((bracket X Y).val p).val h) +
    ((act S Y f).val p) * (X.val p).val h) =
    f.val p * ((bracket X Y).val p).val h +
      (-1 : ℝ) * ((act S Y f).val p * (X.val p).val h)
  ring

/-- A genuine globally smooth function obtained by evaluating the metric. -/
noncomputable def fieldPairing (g : RiemannianMetric S) (X Y : Field S) : GlobalSmooth S :=
  ⟨fun p => pairing g p (X.val p) (Y.val p),
    (SmoothManifolds.mem_globalSmoothAlgebra_iff S _).mpr (fun p =>
      (SmoothManifolds.scalarContDiffAt_iff _ _ _ _).mpr
        (SmoothMetrics.metric_pairing_smoothAt S (tangentBundle S) g id X.val Y.val p
          (SmoothManifolds.manifoldContDiff_id (⊤ : ℕ∞) _ S.smoothStructure.property.1 p)
          (X.property p) (Y.property p)))⟩

@[simp] theorem fieldPairing_apply (g : RiemannianMetric S) (X Y : Field S) (p : M) :
    (fieldPairing g X Y).val p = pairing g p (X.val p) (Y.val p) := rfl

theorem fieldPairing_symm (g : RiemannianMetric S) (X Y : Field S) :
    fieldPairing g X Y = fieldPairing g Y X :=
  Subtype.ext (funext (fun p => g.symmetric p _ _))

@[simp] theorem fieldPairing_add_left (g : RiemannianMetric S) (X Y Z : Field S) :
    fieldPairing g (X + Y) Z = fieldPairing g X Z + fieldPairing g Y Z := by
  apply Subtype.ext; funext p
  exact LinearMap.BilinForm.add_left _ _ _

@[simp] theorem fieldPairing_add_right (g : RiemannianMetric S) (X Y Z : Field S) :
    fieldPairing g X (Y + Z) = fieldPairing g X Y + fieldPairing g X Z := by
  apply Subtype.ext; funext p
  exact (pairing g p (X.val p)).map_add _ _

@[simp] theorem fieldPairing_smul_left (g : RiemannianMetric S) (c : ℝ) (X Y : Field S) :
    fieldPairing g (c • X) Y = c • fieldPairing g X Y := by
  apply Subtype.ext; funext p
  exact LinearMap.BilinForm.smul_left _ _ _

@[simp] theorem fieldPairing_smul_right (g : RiemannianMetric S) (c : ℝ) (X Y : Field S) :
    fieldPairing g X (c • Y) = c • fieldPairing g X Y := by
  apply Subtype.ext; funext p
  exact (pairing g p (X.val p)).map_smul c _

@[simp] theorem fieldPairing_mul_left (g : RiemannianMetric S)
    (f : GlobalSmooth S) (X Y : Field S) :
    fieldPairing g (mulSection f X) Y = f * fieldPairing g X Y := by
  apply Subtype.ext; funext p
  exact LinearMap.BilinForm.smul_left _ _ _

@[simp] theorem fieldPairing_mul_right (g : RiemannianMetric S)
    (f : GlobalSmooth S) (X Y : Field S) :
    fieldPairing g X (mulSection f Y) = f * fieldPairing g X Y := by
  apply Subtype.ext; funext p
  exact (pairing g p (X.val p)).map_smul (f.val p) _

noncomputable def koszulFunction (g : RiemannianMetric S) (X Y Z : Field S) : GlobalSmooth S :=
  act S X (fieldPairing g Y Z) + act S Y (fieldPairing g Z X) -
    act S Z (fieldPairing g X Y) - fieldPairing g X (bracket Y Z) +
    fieldPairing g Y (bracket Z X) + fieldPairing g Z (bracket X Y)

theorem koszulFunction_apply (g : RiemannianMetric S) (X Y Z : Field S) (p : M) :
    (koszulFunction g X Y Z).val p = koszulRHS g X Y Z p := by
  change (koszulFunction g X Y Z).val p =
    scalarDerivative S (fieldPairing g Y Z).val p (X.val p) +
    scalarDerivative S (fieldPairing g Z X).val p (Y.val p) -
    scalarDerivative S (fieldPairing g X Y).val p (Z.val p) -
    pairing g p (X.val p) ((bracket Y Z).val p) +
    pairing g p (Y.val p) ((bracket Z X).val p) +
    pairing g p (Z.val p) ((bracket X Y).val p)
  rw [ConnectionForms.scalarDerivative_global (fieldPairing g Y Z),
    ConnectionForms.scalarDerivative_global (fieldPairing g Z X),
    ConnectionForms.scalarDerivative_global (fieldPairing g X Y)]
  rfl

@[simp] theorem fieldPairing_neg_left (g : RiemannianMetric S) (X Y : Field S) :
    fieldPairing g (-X) Y = -fieldPairing g X Y := by
  apply Subtype.ext; funext p
  change (g.form p) ((-1 : ℝ) • X.val p) (Y.val p) = -_
  rw [LinearMap.BilinForm.smul_left]
  change (-1 : ℝ) * (g.form p) (X.val p) (Y.val p) = -(g.form p) (X.val p) (Y.val p)
  ring

@[simp] theorem fieldPairing_neg_right (g : RiemannianMetric S) (X Y : Field S) :
    fieldPairing g X (-Y) = -fieldPairing g X Y := by
  apply Subtype.ext; funext p
  change (g.form p) (X.val p) ((-1 : ℝ) • Y.val p) = -_
  rw [LinearMap.BilinForm.smul_right]
  change (-1 : ℝ) * (g.form p) (X.val p) (Y.val p) = -(g.form p) (X.val p) (Y.val p)
  ring

@[simp] theorem fieldPairing_sub_left (g : RiemannianMetric S) (X Y Z : Field S) :
    fieldPairing g (X - Y) Z = fieldPairing g X Z - fieldPairing g Y Z := by
  apply Subtype.ext; funext p
  change (g.form p) (X.val p + (-1 : ℝ) • Y.val p) (Z.val p) = _
  rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left]
  change _ = (g.form p) (X.val p) (Z.val p) - (g.form p) (Y.val p) (Z.val p)
  ring

@[simp] theorem fieldPairing_sub_right (g : RiemannianMetric S) (X Y Z : Field S) :
    fieldPairing g X (Y - Z) = fieldPairing g X Y - fieldPairing g X Z := by
  apply Subtype.ext; funext p
  change (g.form p) (X.val p) (Y.val p + (-1 : ℝ) • Z.val p) = _
  rw [LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right]
  change _ = (g.form p) (X.val p) (Y.val p) - (g.form p) (X.val p) (Z.val p)
  ring

theorem koszulFunction_add_third (g : RiemannianMetric S) (X Y Z W : Field S) :
    koszulFunction g X Y (Z + W) = koszulFunction g X Y Z + koszulFunction g X Y W := by
  simp only [koszulFunction, fieldPairing_add_left, fieldPairing_add_right,
    bracket_add_left, bracket_add_right, InducedConnections.act_add_field, map_add]
  abel

theorem koszulFunction_smul_third (g : RiemannianMetric S) (c : ℝ) (X Y Z : Field S) :
    koszulFunction g X Y (c • Z) = c • koszulFunction g X Y Z := by
  simp only [koszulFunction, fieldPairing_smul_left, fieldPairing_smul_right,
    bracket_smul_left, bracket_smul_right, InducedConnections.act_smul_field,
    Derivation.map_smul, smul_add, smul_sub]

theorem koszulFunction_mul_third (g : RiemannianMetric S)
    (f : GlobalSmooth S) (X Y Z : Field S) :
    koszulFunction g X Y (mulSection f Z) = f * koszulFunction g X Y Z := by
  simp only [koszulFunction, fieldPairing_mul_left, fieldPairing_mul_right,
    bracket_mul_left, bracket_mul_right, fieldPairing_sub_right, fieldPairing_add_right,
    InducedConnections.act_mul_field, Derivation.leibniz, smul_eq_mul]
  rw [fieldPairing_symm g Z X]
  ring

theorem koszulFunction_add_first (g : RiemannianMetric S) (X W Y Z : Field S) :
    koszulFunction g (X + W) Y Z = koszulFunction g X Y Z + koszulFunction g W Y Z := by
  simp only [koszulFunction, fieldPairing_add_left, fieldPairing_add_right,
    bracket_add_left, bracket_add_right, InducedConnections.act_add_field, map_add]
  abel

theorem koszulFunction_smul_first (g : RiemannianMetric S) (c : ℝ) (X Y Z : Field S) :
    koszulFunction g (c • X) Y Z = c • koszulFunction g X Y Z := by
  simp only [koszulFunction, fieldPairing_smul_left, fieldPairing_smul_right,
    bracket_smul_left, bracket_smul_right, InducedConnections.act_smul_field,
    Derivation.map_smul, smul_add, smul_sub]

theorem koszulFunction_mul_first (g : RiemannianMetric S)
    (f : GlobalSmooth S) (X Y Z : Field S) :
    koszulFunction g (mulSection f X) Y Z = f * koszulFunction g X Y Z := by
  simp only [koszulFunction, fieldPairing_mul_left, fieldPairing_mul_right,
    bracket_mul_left, bracket_mul_right, fieldPairing_sub_right, fieldPairing_add_right,
    InducedConnections.act_mul_field, Derivation.leibniz, smul_eq_mul]
  rw [fieldPairing_symm g Z X, fieldPairing_symm g Y X]
  ring

theorem koszulFunction_add_second (g : RiemannianMetric S) (X Y W Z : Field S) :
    koszulFunction g X (Y + W) Z = koszulFunction g X Y Z + koszulFunction g X W Z := by
  simp only [koszulFunction, fieldPairing_add_left, fieldPairing_add_right,
    bracket_add_left, bracket_add_right, InducedConnections.act_add_field, map_add]
  abel

theorem koszulFunction_smul_second (g : RiemannianMetric S) (c : ℝ) (X Y Z : Field S) :
    koszulFunction g X (c • Y) Z = c • koszulFunction g X Y Z := by
  simp only [koszulFunction, fieldPairing_smul_left, fieldPairing_smul_right,
    bracket_smul_left, bracket_smul_right, InducedConnections.act_smul_field,
    Derivation.map_smul, smul_add, smul_sub]

theorem koszulFunction_leibniz (g : RiemannianMetric S)
    (f : GlobalSmooth S) (X Y Z : Field S) :
    koszulFunction g X (mulSection f Y) Z = f * koszulFunction g X Y Z +
      2 * act S X f * fieldPairing g Y Z := by
  simp only [koszulFunction, fieldPairing_mul_left, fieldPairing_mul_right,
    bracket_mul_left, bracket_mul_right, fieldPairing_sub_right, fieldPairing_add_right,
    InducedConnections.act_mul_field, Derivation.leibniz, smul_eq_mul]
  rw [fieldPairing_symm g Z Y]
  ring

noncomputable def koszulForm (g : RiemannianMetric S) (X Y : Field S) :
    Field S →ₗ[ℝ] GlobalSmooth S where
  toFun := koszulFunction g X Y
  map_add' := koszulFunction_add_third g X Y
  map_smul' := fun c Z => koszulFunction_smul_third g c X Y Z

noncomputable def koszulFormAt (g : RiemannianMetric S) (X Y : Field S) (p : M) :
    Field S →ₗ[ℝ] ℝ :=
  (SmoothManifolds.TangentData.globalEvaluation S p).toLinearMap.comp (koszulForm g X Y)

theorem koszulFormAt_mul (g : RiemannianMetric S) (X Y : Field S) (p : M)
    (f : GlobalSmooth S) (Z : Field S) :
    koszulFormAt g X Y p (mulSection f Z) = f.val p * koszulFormAt g X Y p Z :=
  congrArg (fun h : GlobalSmooth S => h.val p) (koszulFunction_mul_third g f X Y Z)

noncomputable def koszulCovector (g : RiemannianMetric S) (X Y : Field S) (p : M) :
    Module.Dual ℝ (TangentSpace S p) :=
  (1 / 2 : ℝ) • InducedConnections.fiberFunctional (tangentBundle S) p
    (koszulFormAt g X Y p) (koszulFormAt_mul g X Y p)

theorem koszulCovector_apply (g : RiemannianMetric S) (X Y Z : Field S) (p : M) :
    koszulCovector g X Y p (Z.val p) = (1 / 2 : ℝ) * (koszulFunction g X Y Z).val p := by
  simp only [koszulCovector, LinearMap.smul_apply, smul_eq_mul,
    InducedConnections.fiberFunctional_apply]
  rfl

theorem koszulCovector_smooth (g : RiemannianMetric S) (X Y : Field S) :
    SmoothManifolds.SectionExtensionData.SmoothSection (cotangentBundle S)
      (koszulCovector g X Y) := by
  intro p
  apply ConnectionForms.covector_smoothOn_of_evaluations Set.univ _ _ p (Set.mem_univ p)
  intro Z q _
  have h := (SmoothManifolds.scalarContDiffAt_iff _ _ _ _).mp
    ((SmoothManifolds.mem_globalSmoothAlgebra_iff S _).mp
      (koszulFunction g X Y Z).property q)
  apply ((SmoothManifolds.FrameData.VectorSmoothAt.const S.smoothStructure.val
    (1 / 2 : ℝ) q).prod h).postcomp (contDiff_fst.mul contDiff_snd) |>.congr
  exact Eventually.of_forall (fun r => (koszulCovector_apply g X Y Z r).symm)

noncomputable def koszulSection (g : RiemannianMetric S) (X Y : Field S) : Field S := by
  let I := SmoothManifolds.MetricSplittings.metricIso (tangentBundle S) g (cotangentDual S)
  exact ⟨fun p => (I.equiv p).symm (koszulCovector g X Y p), fun p =>
    SmoothManifolds.manifoldContDiffAt_comp
      (cotangentBundle S).totalManifold.smoothStructure.property.1.1
      (koszulCovector_smooth g X Y p)
      (I.inverse_smooth ⟨p, koszulCovector g X Y p⟩)⟩

theorem pairing_koszulSection (g : RiemannianMetric S) (X Y Z : Field S) (p : M) :
    pairing g p ((koszulSection g X Y).val p) (Z.val p) =
      (1 / 2 : ℝ) * (koszulFunction g X Y Z).val p := by
  change SmoothManifolds.MetricSplittings.metricEquiv (tangentBundle S) g p
    ((SmoothManifolds.MetricSplittings.metricEquiv (tangentBundle S) g p).symm
      (koszulCovector g X Y p)) (Z.val p) = _
  rw [LinearEquiv.apply_symm_apply, koszulCovector_apply]

theorem pairing_add_value (g : RiemannianMetric S) (p : M)
    (v w z : TangentSpace S p) :
    pairing g p (v + w) z = pairing g p v z + pairing g p w z :=
  LinearMap.BilinForm.add_left _ _ _

theorem pairing_smul_value (g : RiemannianMetric S) (p : M)
    (c : ℝ) (v z : TangentSpace S p) :
    pairing g p (c • v) z = c * pairing g p v z :=
  LinearMap.BilinForm.smul_left _ _ _

theorem koszulSection_add_first (g : RiemannianMetric S) (X W Y : Field S) :
    koszulSection g (X + W) Y = koszulSection g X Y + koszulSection g W Y := by
  apply ConnectionForms.section_ext; intro p
  apply pairing_ext g p; intro Z
  change pairing g p ((koszulSection g (X + W) Y).val p) (Z.val p) =
    pairing g p ((koszulSection g X Y).val p + (koszulSection g W Y).val p) (Z.val p)
  rw [pairing_add_value, pairing_koszulSection, pairing_koszulSection, pairing_koszulSection]
  have h := congrArg (fun f : GlobalSmooth S => f.val p) (koszulFunction_add_first g X W Y Z)
  change (koszulFunction g (X + W) Y Z).val p =
    (koszulFunction g X Y Z).val p + (koszulFunction g W Y Z).val p at h
  rw [h]; ring

theorem koszulSection_smul_first (g : RiemannianMetric S) (c : ℝ) (X Y : Field S) :
    koszulSection g (c • X) Y = c • koszulSection g X Y := by
  apply ConnectionForms.section_ext; intro p
  apply pairing_ext g p; intro Z
  change pairing g p ((koszulSection g (c • X) Y).val p) (Z.val p) =
    pairing g p (c • (koszulSection g X Y).val p) (Z.val p)
  rw [pairing_smul_value, pairing_koszulSection, pairing_koszulSection]
  have h := congrArg (fun f : GlobalSmooth S => f.val p) (koszulFunction_smul_first g c X Y Z)
  change (koszulFunction g (c • X) Y Z).val p = c * (koszulFunction g X Y Z).val p at h
  rw [h]; ring

theorem koszulSection_add_second (g : RiemannianMetric S) (X Y W : Field S) :
    koszulSection g X (Y + W) = koszulSection g X Y + koszulSection g X W := by
  apply ConnectionForms.section_ext; intro p
  apply pairing_ext g p; intro Z
  change pairing g p ((koszulSection g X (Y + W)).val p) (Z.val p) =
    pairing g p ((koszulSection g X Y).val p + (koszulSection g X W).val p) (Z.val p)
  rw [pairing_add_value, pairing_koszulSection, pairing_koszulSection, pairing_koszulSection]
  have h := congrArg (fun f : GlobalSmooth S => f.val p) (koszulFunction_add_second g X Y W Z)
  change (koszulFunction g X (Y + W) Z).val p =
    (koszulFunction g X Y Z).val p + (koszulFunction g X W Z).val p at h
  rw [h]; ring

theorem koszulSection_smul_second (g : RiemannianMetric S) (c : ℝ) (X Y : Field S) :
    koszulSection g X (c • Y) = c • koszulSection g X Y := by
  apply ConnectionForms.section_ext; intro p
  apply pairing_ext g p; intro Z
  change pairing g p ((koszulSection g X (c • Y)).val p) (Z.val p) =
    pairing g p (c • (koszulSection g X Y).val p) (Z.val p)
  rw [pairing_smul_value, pairing_koszulSection, pairing_koszulSection]
  have h := congrArg (fun f : GlobalSmooth S => f.val p) (koszulFunction_smul_second g c X Y Z)
  change (koszulFunction g X (c • Y) Z).val p = c * (koszulFunction g X Y Z).val p at h
  rw [h]; ring

theorem koszulSection_mul_first (g : RiemannianMetric S) (f : GlobalSmooth S) (X Y : Field S) :
    koszulSection g (mulSection f X) Y = mulSection f (koszulSection g X Y) := by
  apply ConnectionForms.section_ext; intro p
  apply pairing_ext g p; intro Z
  change pairing g p ((koszulSection g (mulSection f X) Y).val p) (Z.val p) =
    pairing g p (f.val p • (koszulSection g X Y).val p) (Z.val p)
  rw [pairing_smul_value, pairing_koszulSection, pairing_koszulSection]
  have h := congrArg (fun h : GlobalSmooth S => h.val p) (koszulFunction_mul_first g f X Y Z)
  change (koszulFunction g (mulSection f X) Y Z).val p = f.val p * (koszulFunction g X Y Z).val p at h
  rw [h]; ring

theorem koszulSection_leibniz (g : RiemannianMetric S) (f : GlobalSmooth S) (X Y : Field S) :
    koszulSection g X (mulSection f Y) =
      mulSection (act S X f) Y + mulSection f (koszulSection g X Y) := by
  apply ConnectionForms.section_ext; intro p
  apply pairing_ext g p; intro Z
  change pairing g p ((koszulSection g X (mulSection f Y)).val p) (Z.val p) =
    pairing g p ((act S X f).val p • Y.val p + f.val p • (koszulSection g X Y).val p) (Z.val p)
  rw [pairing_add_value, pairing_smul_value, pairing_smul_value,
    pairing_koszulSection, pairing_koszulSection]
  have h := congrArg (fun h : GlobalSmooth S => h.val p) (koszulFunction_leibniz g f X Y Z)
  change (koszulFunction g X (mulSection f Y) Z).val p =
    f.val p * (koszulFunction g X Y Z).val p +
      2 * (act S X f).val p * pairing g p (Y.val p) (Z.val p) at h
  rw [h]; ring

/-- The smooth connection constructed by metric duality of the Koszul form. -/
noncomputable def koszulConnection (g : RiemannianMetric S) : Connection (tangentBundle S) where
  cov :=
    { toFun := fun X =>
        { toFun := koszulSection g X
          map_add' := koszulSection_add_second g X
          map_smul' := fun c Y => koszulSection_smul_second g c X Y }
      map_add' := fun X W => LinearMap.ext (koszulSection_add_first g X W)
      map_smul' := fun c X => LinearMap.ext (koszulSection_smul_first g c X) }
  linear_field := koszulSection_mul_first g
  leibniz := fun X f Y => koszulSection_leibniz g f X Y

theorem koszulConnection_formula (g : RiemannianMetric S) (X Y Z : Field S) (p : M) :
    2 * pairing g p (((koszulConnection g).cov X Y).val p) (Z.val p) = koszulRHS g X Y Z p := by
  change 2 * pairing g p ((koszulSection g X Y).val p) (Z.val p) = _
  rw [pairing_koszulSection, koszulFunction_apply]
  ring

theorem koszulFunction_swap_second_third (g : RiemannianMetric S) (X Y Z : Field S) :
    koszulFunction g X Y Z + koszulFunction g X Z Y = 2 * act S X (fieldPairing g Y Z) := by
  unfold koszulFunction
  rw [bracket_swap Z Y, bracket_swap X Y, bracket_swap X Z]
  simp only [fieldPairing_neg_right]
  rw [fieldPairing_symm g Z Y, fieldPairing_symm g Z X, fieldPairing_symm g Y X]
  ring

theorem koszulFunction_swap_first_second (g : RiemannianMetric S) (X Y Z : Field S) :
    koszulFunction g X Y Z - koszulFunction g Y X Z = 2 * fieldPairing g (bracket X Y) Z := by
  unfold koszulFunction
  rw [bracket_swap X Y, bracket_swap Z Y, bracket_swap Z X]
  simp only [fieldPairing_neg_right]
  rw [fieldPairing_symm g Z Y, fieldPairing_symm g Z X, fieldPairing_symm g Y X,
    fieldPairing_symm g (bracket X Y) Z]
  ring

theorem koszulConnection_metricCompatible (g : RiemannianMetric S) :
    IsMetricCompatible g (koszulConnection g) := by
  intro X Y Z p
  change scalarDerivative S (fieldPairing g Y Z).val p (X.val p) = _
  rw [ConnectionForms.scalarDerivative_global]
  change _ = pairing g p ((koszulSection g X Y).val p) (Z.val p) +
    pairing g p (Y.val p) ((koszulSection g X Z).val p)
  rw [show pairing g p (Y.val p) ((koszulSection g X Z).val p) =
      pairing g p ((koszulSection g X Z).val p) (Y.val p) from g.symmetric p _ _]
  rw [pairing_koszulSection, pairing_koszulSection]
  have h := congrArg (fun f : GlobalSmooth S => f.val p) (koszulFunction_swap_second_third g X Y Z)
  change (koszulFunction g X Y Z).val p + (koszulFunction g X Z Y).val p =
    2 * (act S X (fieldPairing g Y Z)).val p at h
  linarith

theorem koszulConnection_torsionFree (g : RiemannianMetric S) :
    IsTorsionFree (koszulConnection g) := by
  intro X Y
  apply ConnectionForms.section_ext; intro p
  apply pairing_ext g p; intro Z
  change pairing g p
    (((koszulSection g X Y).val p + (-1 : ℝ) • (koszulSection g Y X).val p) +
      (-1 : ℝ) • (bracket X Y).val p) (Z.val p) = pairing g p 0 (Z.val p)
  rw [pairing_add_value, pairing_add_value, pairing_smul_value, pairing_smul_value,
    pairing_koszulSection, pairing_koszulSection]
  have hz : pairing g p 0 (Z.val p) = 0 := (g.form p).map_zero₂ _
  rw [hz]
  have h := congrArg (fun f : GlobalSmooth S => f.val p) (koszulFunction_swap_first_second g X Y Z)
  change (koszulFunction g X Y Z).val p - (koszulFunction g Y X Z).val p =
    2 * pairing g p ((bracket X Y).val p) (Z.val p) at h
  linarith

end Construction

section Coordinates
open SmoothManifolds.BundleOperationsData
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M}

theorem metricMatrix_det_ne_zero (g : RiemannianMetric S) (c : TangentIndex S)
    (p : M) (hp : p ∈ (tangentBundle S).baseSet c) :
    (metricMatrix g c p).det ≠ 0 := by
  classical
  let e := (tangentBundle S).fiberCoordinates c p hp
  let B : LinearMap.BilinForm ℝ (Euclidean n) :=
    (g.form p).compl₁₂ e.symm.toLinearMap e.symm.toLinearMap
  have hB : B.Nondegenerate := by
    constructor
    · intro v hv
      by_contra h
      have he : e.symm v ≠ 0 := fun hz =>
        h (e.symm.injective (hz.trans (map_zero _).symm))
      exact (ne_of_gt (g.positive p (e.symm v) he)) (hv v)
    · intro v hv
      by_contra h
      have he : e.symm v ≠ 0 := fun hz =>
        h (e.symm.injective (hz.trans (map_zero _).symm))
      exact (ne_of_gt (g.positive p (e.symm v) he)) (hv v)
  exact (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero
    (Pi.basisFun ℝ (Fin n))).mp hB

theorem coordinate_expansion (c : TangentIndex S) (p : M)
    (hp : p ∈ (tangentBundle S).baseSet c) (v : TangentSpace S p) :
    (∑ j : Fin n, ((tangentBundle S).fiberCoordinates c p hp v) j •
      coordinateVector c j p) = v := by
  classical
  let e := (tangentBundle S).fiberCoordinates c p hp
  simpa only [map_sum, map_smul, LinearEquiv.symm_apply_apply, Pi.basisFun_apply,
    SmoothVectorBundle.fiberCoordinates_symm_apply, Pi.basisFun_equivFun, LinearEquiv.refl_apply, e, coordinateVector] using
    congrArg e.symm ((Pi.basisFun ℝ (Fin n)).sum_equivFun (e v))

theorem coordinates_from_metric (g : RiemannianMetric S) (c : TangentIndex S) (p : M)
    (hp : p ∈ (tangentBundle S).baseSet c) (v : TangentSpace S p) (k : Fin n) :
    ((tangentBundle S).fiberCoordinates c p hp v) k =
      ∑ l : Fin n, (metricMatrix g c p)⁻¹ k l *
        pairing g p v (coordinateVector c l p) := by
  classical
  let x := (tangentBundle S).fiberCoordinates c p hp v
  have hmul : (metricMatrix g c p) *ᵥ x =
      fun l => pairing g p v (coordinateVector c l p) := by
    funext l
    have h := congrArg (fun w => pairing g p (coordinateVector c l p) w)
      (coordinate_expansion c p hp v)
    simp only [pairing, map_sum, map_smul, smul_eq_mul] at h
    change (∑ j, metricMatrix g c p l j * x j) = _
    calc
      _ = ∑ j, x j * pairing g p (coordinateVector c l p) (coordinateVector c j p) := by
        apply Finset.sum_congr rfl; intro j _; exact mul_comm _ _
      _ = pairing g p (coordinateVector c l p) v := h
      _ = pairing g p v (coordinateVector c l p) := g.symmetric p _ _
  have h := congrArg (fun y => (metricMatrix g c p)⁻¹ *ᵥ y) hmul
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _
    (isUnit_iff_ne_zero.mpr (metricMatrix_det_ne_zero g c p hp)), Matrix.one_mulVec] at h
  exact congrFun h k

theorem trivializationFrame_section (c : TangentIndex S) (j : Fin n)
    (p : (tangentBundle S).baseSet c) :
    (SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) c).section_ j p =
      coordinateVector c j p.val := by
  change ((Pi.basisFun ℝ (Fin n)).map
    ((tangentBundle S).fiberCoordinates c p.val p.property).symm) j = _
  simp only [Module.Basis.map_apply, Pi.basisFun_apply,
    SmoothVectorBundle.fiberCoordinates_symm_apply]
  rfl

theorem original_coordinates_eq (c : TangentIndex S) (X : Field S)
    (p : M) (hp : p ∈ (tangentBundle S).baseSet c) :
    SmoothManifolds.LieBracketData.coefficients (tangentStructure S)
      (originalField S X).val c.val c.property p =
      (tangentBundle S).fiberCoordinates c p hp (X.val p) := by
  have hpc : p ∈ c.val.source := (tangentRealization S).baseSet c ▸ hp
  rw [SmoothManifolds.LieBrackets.coefficients_eq _ _ _ _ hpc]
  exact ((tangentRealization S).coordinates c p hpc (X.val p)).symm

theorem coordinate_bracket_zero (c : TangentIndex S) (p : M)
    (hp : p ∈ (tangentBundle S).baseSet c) (i j : Fin n) (X Y : Field S)
    (hX : ∀ᶠ q in 𝓝 p, X.val q = coordinateVector c i q)
    (hY : ∀ᶠ q in 𝓝 p, Y.val q = coordinateVector c j q) : (bracket X Y).val p = 0 := by
  classical
  let B := tangentStructure S
  have hO : IsOpen ((tangentBundle S).baseSet c) :=
    (tangentBundle S).trivialization_baseSet c ▸
      ((tangentBundle S).trivialization c).open_baseSet
  have hcoord (k : Fin n) (Z : Field S) (hZ : ∀ᶠ q in 𝓝 p, Z.val q = coordinateVector c k q) :
      (fun _ : M => Pi.single k (1 : ℝ)) =ᶠ[𝓝 p]
        SmoothManifolds.LieBracketData.coefficients B (originalField S Z).val c.val c.property := by
    filter_upwards [hO.mem_nhds hp, hZ] with q hq hZq
    rw [original_coordinates_eq c Z q hq, hZq]
    exact ((tangentBundle S).fiberCoordinates c q hq).apply_symm_apply _ |>.symm
  have hdX : SmoothManifolds.FiniteRegularityData.HasCoordinateDerivative c.val
      (SmoothManifolds.LieBracketData.coefficients B (originalField S X).val c.val c.property) p 0 :=
    ⟨fun _ => Pi.single i 1, hasFDerivAt_const _ _, hcoord i X hX⟩
  have hdY : SmoothManifolds.FiniteRegularityData.HasCoordinateDerivative c.val
      (SmoothManifolds.LieBracketData.coefficients B (originalField S Y).val c.val c.property) p 0 :=
    ⟨fun _ => Pi.single j 1, hasFDerivAt_const _ _, hcoord j Y hY⟩
  have hpc : p ∈ c.val.source := (tangentRealization S).baseSet c ▸ hp
  have hb := (SmoothManifolds.LieBrackets.bracket_coordinates S B _
    originalBracket_operation (originalField S X) (originalField S Y)).2
      c.val c.property p hpc 0 0 hdX hdY
  apply (B.fiberCoordinates.equiv c.val c.property p hpc).injective
  rw [map_zero]
  funext k
  have h := hb k
  rw [SmoothManifolds.LieBrackets.coefficients_eq _ _ _ _ hpc] at h
  simpa only [ContinuousLinearMap.zero_apply, Pi.zero_apply, mul_zero, sub_self,
    Finset.sum_const_zero, bracket, realizedField] using h

theorem scalarDerivative_of_germ (f : M → ℝ) (F : GlobalSmooth S) (p : M)
    (hF : F.val =ᶠ[𝓝 p] f) (v : TangentSpace S p) :
    scalarDerivative S F.val p v = scalarDerivative S f p v := by
  rw [ConnectionForms.scalarDerivative_representative F.val F p EventuallyEq.rfl,
    ConnectionForms.scalarDerivative_representative f F p hF]

theorem trivializationFrame_coordinates (c : TangentIndex S)
    (p : (tangentBundle S).baseSet c) (v : TangentSpace S p.val) :
    ((SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) c).basis p).equivFun v =
      (tangentBundle S).fiberCoordinates c p.val p.property v := by
  change ((Pi.basisFun ℝ (Fin n)).map
    ((tangentBundle S).fiberCoordinates c p.val p.property).symm).equivFun v = _
  simp only [Module.Basis.map_equivFun, Pi.basisFun_equivFun, LinearEquiv.symm_symm,
    LinearEquiv.trans_refl]

set_option maxHeartbeats 4000000 in
theorem christoffel_formula_of_leviCivita
    (hf : P202Specs.Geometry.TorsionAndMetric.torsion_formulaType.{u})
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) (c : TangentIndex S)
    (p : (tangentBundle S).baseSet c) (k i j : Fin n) :
    christoffel C c p k i j = (1 / 2 : ℝ) * ∑ l : Fin n,
      (metricMatrix g c p.val)⁻¹ k l *
        (scalarDerivative S (fun q => metricMatrix g c q j l) p.val
            (coordinateVector c i p.val) +
         scalarDerivative S (fun q => metricMatrix g c q i l) p.val
            (coordinateVector c j p.val) -
         scalarDerivative S (fun q => metricMatrix g c q i j) p.val
            (coordinateVector c l p.val)) := by
  classical
  let B := tangentBundle S
  let b := SmoothManifolds.ConstantRankBundles.trivializationFrame B c
  have hO : IsOpen (B.baseSet c) :=
    B.trivialization_baseSet c ▸ (B.trivialization c).open_baseSet
  obtain ⟨e, he⟩ := ConnectionForms.local_frame_representative B b p
  have hec (r : Fin n) : ∀ᶠ q in 𝓝 p.val, (e r).val q = coordinateVector c r q := by
    filter_upwards [he r, hO.mem_nhds p.property] with q hq hq'
    rw [hq, SmoothManifolds.SectionExtension.totalSection_of_mem _ q hq']
    exact trivializationFrame_section c r ⟨q, hq'⟩
  have heval (r : Fin n) : (e r).val p.val = coordinateVector c r p.val :=
    (hec r).self_of_nhds
  have hscalar (r s : Fin n) : (fieldPairing g (e r) (e s)).val =ᶠ[𝓝 p.val]
      (fun q => metricMatrix g c q r s) := by
    filter_upwards [hec r, hec s] with q hr hs
    change pairing g q ((e r).val q) ((e s).val q) = _
    rw [hr, hs]; rfl
  have hbr (r s : Fin n) : (bracket (e r) (e s)).val p.val = 0 :=
    coordinate_bracket_zero c p.val p.property r s (e r) (e s) (hec r) (hec s)
  have hkoszul (l : Fin n) :
      2 * pairing g p.val ((C.cov (e i) (e j)).val p.val) (coordinateVector c l p.val) =
        scalarDerivative S (fun q => metricMatrix g c q j l) p.val (coordinateVector c i p.val) +
        scalarDerivative S (fun q => metricMatrix g c q i l) p.val (coordinateVector c j p.val) -
        scalarDerivative S (fun q => metricMatrix g c q i j) p.val (coordinateVector c l p.val) := by
    have h := koszul_of_leviCivita hf g C hC (e i) (e j) (e l) p.val
    unfold koszulRHS at h
    change 2 * pairing g p.val ((C.cov (e i) (e j)).val p.val) ((e l).val p.val) =
      scalarDerivative S (fieldPairing g (e j) (e l)).val p.val ((e i).val p.val) +
      scalarDerivative S (fieldPairing g (e l) (e i)).val p.val ((e j).val p.val) -
      scalarDerivative S (fieldPairing g (e i) (e j)).val p.val ((e l).val p.val) -
      pairing g p.val ((e i).val p.val) ((bracket (e j) (e l)).val p.val) +
      pairing g p.val ((e j).val p.val) ((bracket (e l) (e i)).val p.val) +
      pairing g p.val ((e l).val p.val) ((bracket (e i) (e j)).val p.val) at h
    rw [scalarDerivative_of_germ _ _ p.val (hscalar j l),
      fieldPairing_symm g (e l) (e i), scalarDerivative_of_germ _ _ p.val (hscalar i l),
      scalarDerivative_of_germ _ _ p.val (hscalar i j),
      heval i, heval j, heval l, hbr j l, hbr l i, hbr i j] at h
    simpa only [pairing, map_zero, sub_zero, add_zero] using h
  have hgamma : christoffel C c p k i j =
      (B.fiberCoordinates c p.val p.property ((C.cov (e i) (e j)).val p.val)) k := by
    change ((b.basis p).equivFun
      (pointDerivative C (SmoothManifolds.SectionExtension.totalSection (b.section_ j)) p.val
        (coordinateVector c i p.val))) k = _
    have hder : pointDerivative C (SmoothManifolds.SectionExtension.totalSection (b.section_ j)) p.val =
        pointDerivative C (e j).val p.val :=
      (ConnectionForms.pointDerivative_congr B C (e j).val _ p.val
        ⟨e j, Eventually.of_forall (fun _ => rfl)⟩ (he j)).symm
    have hglob : pointDerivative C (e j).val p.val ((e i).val p.val) =
        (C.cov (e i) (e j)).val p.val := ConnectionForms.pointDerivative_global B C (e j) p.val (e i)
    have hvalue : pointDerivative C (SmoothManifolds.SectionExtension.totalSection (b.section_ j)) p.val
        (coordinateVector c i p.val) = (C.cov (e i) (e j)).val p.val :=
      (congrArg (fun d : TangentSpace S p.val →ₗ[ℝ] TangentSpace S p.val =>
        d (coordinateVector c i p.val)) hder).trans
        ((congrArg (pointDerivative C (e j).val p.val) (heval i).symm).trans hglob)
    exact (congrArg (fun v : TangentSpace S p.val => (b.basis p).equivFun v k) hvalue).trans
      (congrFun (trivializationFrame_coordinates c p _) k)
  rw [hgamma, coordinates_from_metric g c p.val p.property]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [← hkoszul l]
  ring

end Coordinates

section Naturality
open SmoothManifolds.DifferentialData SmoothManifolds.BundleOperationsData
variable {n m : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {T : SmoothManifold m b N}

theorem action_related_at (f : M → N) (hf : IsSmoothMap S T f)
    (L : (q : M) → TangentSpace S q →ₗ[ℝ] TangentSpace T (f q))
    (hL : ∀ q, IsDifferential S T f q (L q)) (X : Field S) (X' : Field T)
    (p : M) (hX : L p (X.val p) = X'.val (f p)) (F : GlobalSmooth T) :
    (act S X (SmoothManifolds.VectorFields.composeGlobal S T f hf F)).val p =
      (act T X' F).val (f p) := by
  rw [ConnectionForms.act_apply, ConnectionForms.act_apply, ← hX]
  exact ((hL p) (X.val p) (SmoothManifolds.globalToGerm T (f p) F)
    (SmoothManifolds.globalToGerm S p (SmoothManifolds.VectorFields.composeGlobal S T f hf F))
    F.val rfl rfl).symm

theorem bracket_action (X Y : Field S) (F : GlobalSmooth S) (p : M) :
    (act S (bracket X Y) F).val p =
      (act S X (act S Y F)).val p - (act S Y (act S X F)).val p := by
  have h := originalBracket_operation (originalField S X) (originalField S Y)
    (act S X) (act S Y)
    (SmoothManifolds.VectorFields.derivationOfField_represents S (tangentStructure S) _)
    (SmoothManifolds.VectorFields.derivationOfField_represents S (tangentStructure S) _)
  have he := SmoothManifolds.LieBrackets.represents_eval h p F
  simpa only [Derivation.commutator_apply, Subalgebra.coe_sub, Pi.sub_apply,
    ConnectionForms.act_apply, bracket, realizedField] using he

theorem bracket_related_at (f : M → N) (hf : IsSmoothMap S T f)
    (L : (q : M) → TangentSpace S q →ₗ[ℝ] TangentSpace T (f q))
    (hL : ∀ q, IsDifferential S T f q (L q))
    (X Y : Field S) (X' Y' : Field T) (p : M)
    (hX : ∀ᶠ q in 𝓝 p, L q (X.val q) = X'.val (f q))
    (hY : ∀ᶠ q in 𝓝 p, L q (Y.val q) = Y'.val (f q)) :
    L p ((bracket X Y).val p) = (bracket X' Y').val (f p) := by
  apply SmoothManifolds.LieBrackets.tangent_ext_global (f p)
  intro F
  have hchain := (hL p) ((bracket X Y).val p) (SmoothManifolds.globalToGerm T (f p) F)
    (SmoothManifolds.globalToGerm S p (SmoothManifolds.VectorFields.composeGlobal S T f hf F))
    F.val rfl rfl
  change _ = (act T (bracket X' Y') F).val (f p)
  rw [hchain]
  change (act S (bracket X Y) (SmoothManifolds.VectorFields.composeGlobal S T f hf F)).val p = _
  rw [bracket_action, bracket_action]
  have hnear (Z : Field S) (Z' : Field T)
      (hZ : ∀ᶠ q in 𝓝 p, L q (Z.val q) = Z'.val (f q)) :
      (act S Z (SmoothManifolds.VectorFields.composeGlobal S T f hf F)).val =ᶠ[𝓝 p]
        (SmoothManifolds.VectorFields.composeGlobal S T f hf (act T Z' F)).val := by
    filter_upwards [hZ] with q hq
    exact action_related_at f hf L hL Z Z' q hq F
  rw [ConnectionForms.act_congr X _ _ p (hnear Y Y' hY),
    ConnectionForms.act_congr Y _ _ p (hnear X X' hX),
    action_related_at f hf L hL X X' p hX.self_of_nhds,
    action_related_at f hf L hL Y Y' p hY.self_of_nhds]

/-- A local diffeomorphism pushes any smooth source field to a smooth target
germ. Cutoffs give a global representative of that germ; no global
projectability of the field or injectivity of the map is asserted. -/
theorem exists_related_germ (f : M → N)
    (hf : SmoothManifolds.TensorData.IsLocalDiffeomorphism S T f)
    (L : (q : M) → TangentSpace S q →ₗ[ℝ] TangentSpace T (f q))
    (hL : ∀ q, IsDifferential S T f q (L q)) (X : Field S) (p : M) :
    ∃ X' : Field T, ∀ᶠ q in 𝓝 p, L q (X.val q) = X'.val (f q) := by
  classical
  obtain ⟨g, hg, hgp, hgf, _hfg⟩ := hf.2 p
  let TC := tangentBundle T
  obtain ⟨i, hi⟩ := TC.covers (f p)
  let b := SmoothManifolds.ConstantRankBundles.trivializationFrame TC i
  obtain ⟨e, he⟩ := ConnectionForms.local_frame_representative TC b ⟨f p, hi⟩
  let z : N → Bundle.TotalSpace (Euclidean m) (TangentSpace T) :=
    fun q => ⟨f (g q), L (g q) (X.val (g q))⟩
  have hXg := SmoothManifolds.manifoldContDiffAt_comp S.smoothStructure.property.1.1
    hg (X.property (g (f p)))
  have hdf := SmoothMetrics.differential_totalMap_smooth f hf.1 L hL
  have hz : ManifoldSmoothAt T.smoothStructure.val TC.totalManifold.smoothStructure.val z (f p) :=
    SmoothManifolds.manifoldContDiffAt_comp
      (tangentBundle S).totalManifold.smoothStructure.property.1.1 hXg
      (hdf ⟨g (f p), X.val (g (f p))⟩)
  let v : N → Euclidean m := fun q => ((TC.trivialization i) (z q)).2
  have hv : SmoothManifolds.FrameData.VectorSmoothAt T.smoothStructure.val v (f p) :=
    (SmoothManifolds.Frames.trivializationCoordinates_smoothAt TC i (z (f p))
      (by change f (g (f p)) ∈ TC.baseSet i; rw [hgp]; exact hi)).comp
      (g := z) TC.totalManifold.smoothStructure.property.1.1 hz
  have hcoeff (j : Fin m) : ∃ F : GlobalSmooth T, F.val =ᶠ[𝓝 (f p)] (fun q => v q j) := by
    have hj := hv.postcomp (ContinuousLinearMap.proj (R := ℝ) j).contDiff
    obtain ⟨F, hF, hFe⟩ := SmoothManifolds.exists_global_representative T (f p) _
      ((SmoothManifolds.scalarContDiffAt_iff _ _ _ _).mpr hj)
    exact ⟨⟨F, (SmoothManifolds.mem_globalSmoothAlgebra_iff T _).mpr hF⟩, hFe⟩
  choose F hF using hcoeff
  refine ⟨∑ j : Fin m, mulSection (F j) (e j), ?_⟩
  have hO : IsOpen (TC.baseSet i) := TC.trivialization_baseSet i ▸ (TC.trivialization i).open_baseSet
  filter_upwards [hgf, (hf.1 p).1.eventually (Filter.eventually_all.mpr hF),
    (hf.1 p).1.eventually (Filter.eventually_all.mpr he),
    (hf.1 p).1.preimage_mem_nhds (hO.mem_nhds hi)] with q hgfq hFq heq hiq
  have hrep (j : Fin m) : (F j).val (f q) = (TC.fiberCoordinates i (f q) hiq (L q (X.val q))) j := by
    rw [hFq j]
    change ((TC.trivialization i) ⟨f (g (f q)), L (g (f q)) (X.val (g (f q)))⟩).2 j = _
    change g (f q) = q at hgfq
    rw [hgfq]
    rfl
  have heval (j : Fin m) : (e j).val (f q) = coordinateVector i j (f q) := by
    rw [heq j, SmoothManifolds.SectionExtension.totalSection_of_mem (b.section_ j) (f q) hiq]
    exact trivializationFrame_section i j ⟨f q, hiq⟩
  symm
  change (∑ j : Fin m, mulSection (F j) (e j)).val (f q) = L q (X.val q)
  simp only [Submodule.coe_sum, Finset.sum_apply, ConnectionForms.mulSection_apply, heval, hrep]
  exact coordinate_expansion i (f q) hiq (L q (X.val q))

theorem koszulFunction_related_at (f : M → N) (hf : IsSmoothMap S T f)
    (L : (q : M) → TangentSpace S q →ₗ[ℝ] TangentSpace T (f q))
    (hL : ∀ q, IsDifferential S T f q (L q))
    (g : RiemannianMetric S) (h : RiemannianMetric T)
    (hm : IsMetricPreserving g h f L)
    (X Y Z : Field S) (X' Y' Z' : Field T) (p : M)
    (hX : ∀ᶠ q in 𝓝 p, L q (X.val q) = X'.val (f q))
    (hY : ∀ᶠ q in 𝓝 p, L q (Y.val q) = Y'.val (f q))
    (hZ : ∀ᶠ q in 𝓝 p, L q (Z.val q) = Z'.val (f q)) :
    (koszulFunction g X Y Z).val p = (koszulFunction h X' Y' Z').val (f p) := by
  have hpair (U V : Field S) (U' V' : Field T)
      (hU : ∀ᶠ q in 𝓝 p, L q (U.val q) = U'.val (f q))
      (hV : ∀ᶠ q in 𝓝 p, L q (V.val q) = V'.val (f q)) :
      (fieldPairing g U V).val =ᶠ[𝓝 p]
        (SmoothManifolds.VectorFields.composeGlobal S T f hf (fieldPairing h U' V')).val := by
    filter_upwards [hU, hV] with q hUq hVq
    change pairing g q (U.val q) (V.val q) = pairing h (f q) (U'.val (f q)) (V'.val (f q))
    rw [← hm q (U.val q) (V.val q), hUq, hVq]
  have ha (U V W : Field S) (U' V' W' : Field T)
      (hU : ∀ᶠ q in 𝓝 p, L q (U.val q) = U'.val (f q))
      (hV : ∀ᶠ q in 𝓝 p, L q (V.val q) = V'.val (f q))
      (hW : ∀ᶠ q in 𝓝 p, L q (W.val q) = W'.val (f q)) :
      (act S U (fieldPairing g V W)).val p = (act T U' (fieldPairing h V' W')).val (f p) := by
    rw [ConnectionForms.act_congr U _ _ p (hpair V W V' W' hV hW)]
    exact action_related_at f hf L hL U U' p hU.self_of_nhds _
  have hb (U V W : Field S) (U' V' W' : Field T)
      (hU : ∀ᶠ q in 𝓝 p, L q (U.val q) = U'.val (f q))
      (hV : ∀ᶠ q in 𝓝 p, L q (V.val q) = V'.val (f q))
      (hW : ∀ᶠ q in 𝓝 p, L q (W.val q) = W'.val (f q)) :
      pairing g p (U.val p) ((bracket V W).val p) =
        pairing h (f p) (U'.val (f p)) ((bracket V' W').val (f p)) := by
    rw [← hm p (U.val p) ((bracket V W).val p), hU.self_of_nhds,
      bracket_related_at f hf L hL V W V' W' p hV hW]
  change (act S X (fieldPairing g Y Z)).val p + (act S Y (fieldPairing g Z X)).val p -
      (act S Z (fieldPairing g X Y)).val p - pairing g p (X.val p) ((bracket Y Z).val p) +
      pairing g p (Y.val p) ((bracket Z X).val p) + pairing g p (Z.val p) ((bracket X Y).val p) =
    (act T X' (fieldPairing h Y' Z')).val (f p) + (act T Y' (fieldPairing h Z' X')).val (f p) -
      (act T Z' (fieldPairing h X' Y')).val (f p) -
      pairing h (f p) (X'.val (f p)) ((bracket Y' Z').val (f p)) +
      pairing h (f p) (Y'.val (f p)) ((bracket Z' X').val (f p)) +
      pairing h (f p) (Z'.val (f p)) ((bracket X' Y').val (f p))
  rw [ha X Y Z X' Y' Z' hX hY hZ, ha Y Z X Y' Z' X' hY hZ hX,
    ha Z X Y Z' X' Y' hZ hX hY, hb X Y Z X' Y' Z' hX hY hZ,
    hb Y Z X Y' Z' X' hY hZ hX, hb Z X Y Z' X' Y' hZ hX hY]

theorem connection_related_at
    (htor : P202Specs.Geometry.TorsionAndMetric.torsion_formulaType.{u})
    (f : M → N) (hf : SmoothManifolds.TensorData.IsLocalDiffeomorphism S T f)
    (L : (q : M) → TangentSpace S q →ₗ[ℝ] TangentSpace T (f q))
    (hL : ∀ q, IsDifferential S T f q (L q))
    (g : RiemannianMetric S) (h : RiemannianMetric T) (hm : IsMetricPreserving g h f L)
    (C : Connection (tangentBundle S)) (K : Connection (tangentBundle T))
    (hC : IsLeviCivita g C) (hK : IsLeviCivita h K)
    (X Y : Field S) (X' Y' : Field T) (p : M)
    (hX : ∀ᶠ q in 𝓝 p, L q (X.val q) = X'.val (f q))
    (hY : ∀ᶠ q in 𝓝 p, L q (Y.val q) = Y'.val (f q)) :
    L p ((C.cov X Y).val p) = (K.cov X' Y').val (f p) := by
  obtain ⟨E, hE⟩ := SmoothManifolds.Tensors.local_diffeomorphism_differential S T f hf
  have hEq : L p = (E p).toLinearMap :=
    (SmoothManifolds.differential_exists S T f hf.1 p).unique (hL p) (hE p)
  have hsurj : Function.Surjective (L p) := hEq ▸ (E p).surjective
  apply pairing_ext h (f p)
  intro W
  obtain ⟨v, hv⟩ := hsurj (W.val (f p))
  obtain ⟨Z, hZp⟩ := ConnectionForms.section_evaluation_surjective (tangentBundle S) p v
  obtain ⟨Z', hZ⟩ := exists_related_germ f hf L hL Z p
  have heval : Z'.val (f p) = W.val (f p) := by
    rw [← hZ.self_of_nhds, hZp, hv]
  have hc := koszul_of_leviCivita htor g C hC X Y Z p
  have hk := koszul_of_leviCivita htor h K hK X' Y' Z' (f p)
  have hn := koszulFunction_related_at f hf.1 L hL g h hm X Y Z X' Y' Z' p hX hY hZ
  rw [koszulFunction_apply, koszulFunction_apply] at hn
  have hp : pairing h (f p) (L p ((C.cov X Y).val p)) (Z'.val (f p)) =
      pairing g p ((C.cov X Y).val p) (Z.val p) := by
    rw [← hZ.self_of_nhds]
    exact hm p _ _
  rw [← heval, hp]
  linarith

/-- Smoothness of df(Y) as a section of the actual pullback tangent bundle. -/
noncomputable def differentialSection (f : M → N) (hf : IsSmoothMap S T f)
    (P : PullbackBundle (tangentBundle T) S f) (Y : Field S) :
    letI := P.space.topology; Section P.space.bundle := by
  letI := P.space.topology
  let L := SmoothManifolds.differential S T f hf
  have hL := SmoothManifolds.differential_spec S T f hf
  have hdf := SmoothMetrics.differential_totalMap_smooth f hf L hL
  refine ⟨fun q => L q (Y.val q), fun p => ?_⟩
  obtain ⟨i, hi⟩ := (tangentBundle T).covers (f p)
  apply SmoothManifolds.SectionExtension.smoothAt_of_coordinates P.space.bundle i
    (by rw [P.baseSet]; exact hi)
  have htotal := SmoothManifolds.manifoldContDiffAt_comp
    (tangentBundle S).totalManifold.smoothStructure.property.1.1
    (Y.property p) (hdf ⟨p, Y.val p⟩)
  have hc := (SmoothManifolds.Frames.trivializationCoordinates_smoothAt
    (tangentBundle T) i ⟨f p, L p (Y.val p)⟩ hi).comp
      (g := fun q : M => (⟨f q, L q (Y.val q)⟩ : Bundle.TotalSpace (Euclidean m) (TangentSpace T)))
      (tangentBundle T).totalManifold.smoothStructure.property.1.1 htotal
  apply hc.congr
  have hO : IsOpen ((tangentBundle T).baseSet i) :=
    (tangentBundle T).trivialization_baseSet i ▸
      ((tangentBundle T).trivialization i).open_baseSet
  filter_upwards [(hf p).1.preimage_mem_nhds (hO.mem_nhds hi)] with q hq
  exact (P.coordinates i q hq (L q (Y.val q))).symm

theorem localIsometry_intertwines_of_torsion_formula
    (htor : P202Specs.Geometry.TorsionAndMetric.torsion_formulaType.{u})
    (g : RiemannianMetric S) (h : RiemannianMetric T)
    (C : Connection (tangentBundle S)) (K : Connection (tangentBundle T))
    (hC : IsLeviCivita g C) (hK : IsLeviCivita h K)
    (f : M → N) (hi : IsLocalIsometry g h f) (hf : IsSmoothMap S T f)
    (P : PullbackBundle (tangentBundle T) S f) :
    letI := P.space.topology
    ∀ (D : Connection P.space.bundle),
      P202.PullbackData.IsPullback (tangentBundle T) K f hf P D →
    ∀ Y : Field S, ∃ t : Section P.space.bundle,
      (∀ q, t.val q = SmoothManifolds.differential S T f hf q (Y.val q)) ∧
      ∀ (X : Field S) (p : M),
        (D.cov X t).val p = SmoothManifolds.differential S T f hf p ((C.cov X Y).val p) := by
  letI := P.space.topology
  intro D hD Y
  let L := SmoothManifolds.differential S T f hf
  have hL := SmoothManifolds.differential_spec S T f hf
  obtain ⟨hlocal, A, hA, hmA⟩ := hi
  have hAL : A = L := by
    funext p
    exact (SmoothManifolds.differential_exists S T f hf p).unique (hA p) (hL p)
  have hm : IsMetricPreserving g h f L := hAL ▸ hmA
  refine ⟨differentialSection f hf P Y, fun _ => rfl, ?_⟩
  intro X p
  obtain ⟨X', hX⟩ := exists_related_germ f hlocal L hL X p
  obtain ⟨Y', hY⟩ := exists_related_germ f hlocal L hL Y p
  let s := PullbackConnections.pullSection (tangentBundle T) f hf P Y'
  have heq : ∀ᶠ q in 𝓝 p, (differentialSection f hf P Y).val q = s.val q := hY
  rw [ConnectionForms.locality_section P.space.bundle D X _ s p heq]
  rw [hD X Y' s (fun _ => rfl) p, hX.self_of_nhds,
    ConnectionForms.pointDerivative_global (tangentBundle T) K Y' (f p) X']
  exact (connection_related_at htor f hlocal L hL g h hm C K hC hK X Y X' Y' p hX hY).symm

end Naturality

theorem koszul_formula : P202Specs.Geometry.LeviCivita.koszul_formulaType.{u} := by
  intro n a M _ S g C hC X Y Z p
  exact koszul_of_leviCivita TorsionAndMetric.torsion_apply g C hC X Y Z p

theorem uniqueness : P202Specs.Geometry.LeviCivita.uniquenessType.{u} := by
  intro n a M _ S g C D hC hD
  exact uniqueness_of_koszul g C D
    (koszul_of_leviCivita TorsionAndMetric.torsion_apply g C hC)
    (koszul_of_leviCivita TorsionAndMetric.torsion_apply g D hD)

theorem exists_unique : P202Specs.Geometry.LeviCivita.exists_uniqueType.{u} := by
  intro n a M _ S g
  refine ⟨koszulConnection g,
    ⟨koszulConnection_torsionFree g, koszulConnection_metricCompatible g⟩, ?_⟩
  intro D hD
  exact uniqueness_of_koszul g D (koszulConnection g)
    (koszul_of_leviCivita TorsionAndMetric.torsion_apply g D hD)
    (koszulConnection_formula g)

theorem christoffel_formula : P202Specs.Geometry.LeviCivita.christoffel_formulaType.{u} := by
  intro n a M _ S g C hC c p k i j
  exact christoffel_formula_of_leviCivita TorsionAndMetric.torsion_apply g C hC c p k i j

theorem localIsometry_intertwines :
    P202Specs.Geometry.LeviCivita.localIsometry_intertwinesType.{u} := by
  intro n m a b M N _ _ S T g h C K hC hK f hi hsm P
  exact localIsometry_intertwines_of_torsion_formula
    TorsionAndMetric.torsion_apply g h C K hC hK f hi hsm P

end P202.Geometry.LeviCivita
