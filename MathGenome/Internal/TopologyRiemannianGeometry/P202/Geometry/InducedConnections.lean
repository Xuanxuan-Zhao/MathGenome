import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.InducedConnections
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.ConnectionCalculus
import Mathlib.LinearAlgebra.Isomorphisms

/-! Induced connections for paper.tex 3039--3040 and 3056--3062. -/
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace P202.Geometry.InducedConnections
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.BundleData SmoothManifolds.FrameData
  SmoothManifolds.BundleOperationsData SmoothManifolds.SectionExtensionData P202.ConnectionData P202.InducedConnectionData
open Set Filter
open scoped Topology
universe u v w z t

section DualSmoothness
variable {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E) (D : DualBundle B)

/-- Evaluation on a smooth section tests genuine dual-bundle smoothness. -/
theorem dual_smooth_of_evaluations (lam : (p : M) → Module.Dual ℝ (E p))
    (h : ∀ s : Section B, ∀ p,
      VectorSmoothAt S.smoothStructure.val (fun q => lam q (s.val q)) p) :
    letI := D.space.topology; SmoothSection D.space.bundle lam := by
  letI := D.space.topology
  intro p
  obtain ⟨i, hi⟩ := B.covers p
  have hV : IsOpen (B.baseSet i) :=
    B.trivialization_baseSet i ▸ (B.trivialization i).open_baseSet
  let b := SmoothManifolds.ConstantRankBundles.trivializationFrame B i
  obtain ⟨e, he⟩ := ConnectionForms.local_frame_representative B b ⟨p, hi⟩
  apply SmoothManifolds.SectionExtension.smoothAt_of_coordinates D.space.bundle i
    (by rw [D.baseSet]; exact hi)
  apply VectorSmoothAt.pi
  intro j
  apply (h (e j) p).congr
  filter_upwards [hV.mem_nhds hi, he j] with q hq heq
  rw [D.coordinates i q hq (lam q) j]
  rw [heq, SmoothManifolds.SectionExtension.totalSection_of_mem _ q hq]
  congr 1
  change ((Pi.basisFun ℝ (Fin r)).map (B.fiberCoordinates i q hq).symm) j = _
  simp only [Module.Basis.map_apply, Pi.basisFun_apply,
    SmoothManifolds.BundleData.SmoothVectorBundle.fiberCoordinates_symm_apply]

/-- Evaluation of actual smooth dual and primal sections is a smooth function. -/
theorem pairing_smooth :
    letI := D.space.topology
    ∀ (lam : Section D.space.bundle) (s : Section B) (p : M),
      VectorSmoothAt S.smoothStructure.val (fun q => lam.val q (s.val q)) p := by
  letI := D.space.topology
  intro lam s p
  classical
  obtain ⟨i, hi⟩ := B.covers p
  have ho : IsOpen (B.baseSet i) :=
    B.trivialization_baseSet i ▸ (B.trivialization i).open_baseSet
  have hd := SmoothManifolds.SectionExtension.coordinates_smoothAt D.space.bundle i
    (by rw [D.baseSet]; exact hi) (lam.property p)
  have hs := SmoothManifolds.SectionExtension.coordinates_smoothAt B i hi (s.property p)
  have hsum : VectorSmoothAt S.smoothStructure.val
      (fun q => ∑ j : Fin r,
        ((D.space.bundle.trivialization i) ⟨q, lam.val q⟩).2 j *
          ((B.trivialization i) ⟨q, s.val q⟩).2 j) p := by
    apply VectorSmoothAt.sum
    intro j
    exact ((hd.postcomp (ContinuousLinearMap.proj j).contDiff).prod
      (hs.postcomp (ContinuousLinearMap.proj j).contDiff)).postcomp
        (contDiff_fst.mul contDiff_snd)
  apply hsum.congr
  filter_upwards [ho.mem_nhds hi] with q hq
  have he := (Pi.basisFun ℝ (Fin r)).sum_equivFun (B.fiberCoordinates i q hq (s.val q))
  have hex : s.val q = ∑ j : Fin r,
      ((B.trivialization i) ⟨q, s.val q⟩).2 j •
        (B.trivialization i).symm q (Pi.single j 1) := by
    have hh := congrArg (B.fiberCoordinates i q hq).symm he
    rw [LinearEquiv.symm_apply_apply] at hh
    simpa only [LinearEquiv.symm_apply_apply, map_sum, map_smul,
      Pi.basisFun_apply, Pi.basisFun_equivFun, LinearEquiv.refl_apply, SmoothVectorBundle.fiberCoordinates_apply,
      SmoothVectorBundle.fiberCoordinates_symm_apply] using hh.symm
  conv_rhs => rw [hex, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [D.coordinates i q hq]
  simp only [map_smul, smul_eq_mul]
  exact mul_comm _ _

/-- The scalar pairing takes values in C∞(M). -/
noncomputable def pairing :
    letI := D.space.topology
    Section D.space.bundle → Section B → GlobalSmooth S := by
  letI := D.space.topology
  intro lam s
  exact ⟨fun q => lam.val q (s.val q),
    (SmoothManifolds.mem_globalSmoothAlgebra_iff S _).mpr
      (fun p => (SmoothManifolds.scalarContDiffAt_iff _ _ _ _).mpr
        (pairing_smooth B D lam s p))⟩

end DualSmoothness
section FiberDescent
variable {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E)

/-- A C∞-linear functional at p is local, by multiplication by a cutoff. -/
theorem functional_local (p : M) (H : Section B →ₗ[ℝ] ℝ)
    (hH : ∀ (f : GlobalSmooth S) (s : Section B), H (mulSection f s) = f.val p * H s)
    (s t : Section B) (hst : ∀ᶠ q in 𝓝 p, s.val q = t.val q) : H s = H t := by
  obtain ⟨U, hU, hUo, hpU⟩ := eventually_nhds_iff.mp hst
  obtain ⟨f, hf, hsupp⟩ := ConnectionForms.exists_cutoff_near (S := S) p U hUo hpU
  have heq : mulSection f s = mulSection f t := by
    apply Subtype.ext
    funext q
    by_cases hq : q ∈ U
    · change f.val q • s.val q = f.val q • t.val q
      rw [hU q hq]
    · have hz : f.val q = 0 := Function.notMem_support.mp
        (fun hz => hq (hsupp (subset_closure hz)))
      change f.val q • s.val q = f.val q • t.val q
      rw [hz, zero_smul, zero_smul]
  have h := congrArg H heq
  rw [hH, hH, hf.eq_of_nhds, one_mul, one_mul] at h
  exact h

/-- A C∞-linear functional at p vanishes on sections vanishing at p. -/
theorem functional_zero (p : M) (H : Section B →ₗ[ℝ] ℝ)
    (hH : ∀ (f : GlobalSmooth S) (s : Section B), H (mulSection f s) = f.val p * H s)
    (s : Section B) (hs : s.val p = 0) : H s = 0 := by
  obtain ⟨f, e, heq, hf⟩ := ConnectionForms.section_zero_decomposition B s p hs
  rw [functional_local B p H hH s _ heq, map_sum]
  apply Finset.sum_eq_zero
  intro j _
  rw [hH, hf, zero_mul]

/-- Evaluation at a point is a surjective real linear map. -/
def sectionEvaluation (p : M) : Section B →ₗ[ℝ] E p where
  toFun := fun s => s.val p
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

/-- Descent of a scalar-module-linear functional to the actual fiber. -/
noncomputable def fiberFunctional (p : M) (H : Section B →ₗ[ℝ] ℝ)
    (hH : ∀ (f : GlobalSmooth S) (s : Section B), H (mulSection f s) = f.val p * H s) :
    Module.Dual ℝ (E p) :=
  (sectionEvaluation B p).liftOfSurjective
    (ConnectionForms.section_evaluation_surjective B p)
    ⟨H, fun s hs => functional_zero B p H hH s hs⟩

@[simp] theorem fiberFunctional_apply (p : M) (H : Section B →ₗ[ℝ] ℝ)
    (hH : ∀ (f : GlobalSmooth S) (s : Section B), H (mulSection f s) = f.val p * H s)
    (s : Section B) : fiberFunctional B p H hH (s.val p) = H s :=
  LinearMap.equivOfSurjective_apply _ _

end FiberDescent
section ScalarAction
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M}

@[simp] theorem act_add_field (X Y : Field S) (f : GlobalSmooth S) :
    act S (X + Y) f = act S X f + act S Y f := by
  apply Subtype.ext
  funext p
  rfl

@[simp] theorem act_smul_field (c : ℝ) (X : Field S) (f : GlobalSmooth S) :
    act S (c • X) f = c • act S X f := by
  apply Subtype.ext
  funext p
  rfl

@[simp] theorem act_mul_field (f g : GlobalSmooth S) (X : Field S) :
    act S (mulSection f X) g = f * act S X g := by
  apply Subtype.ext
  funext p
  rfl

end ScalarAction

section DualConstruction
variable {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E) (D : DualBundle B)

set_option quotPrecheck false in
local notation "DualSection" => (letI := D.space.topology; Section D.space.bundle)

@[simp] theorem pairing_apply (lam : DualSection) (s : Section B) (p : M) :
    (pairing B D lam s).val p = lam.val p (s.val p) := rfl

@[simp] theorem pairing_add_right (lam : DualSection) (s t : Section B) :
    pairing B D lam (s + t) = pairing B D lam s + pairing B D lam t := by
  apply Subtype.ext
  funext p
  exact (lam.val p).map_add _ _

@[simp] theorem pairing_smul_right (lam : DualSection) (c : ℝ) (s : Section B) :
    pairing B D lam (c • s) = c • pairing B D lam s := by
  apply Subtype.ext
  funext p
  exact (lam.val p).map_smul c _

@[simp] theorem pairing_mul_right (lam : DualSection) (f : GlobalSmooth S) (s : Section B) :
    pairing B D lam (mulSection f s) = f * pairing B D lam s := by
  apply Subtype.ext
  funext p
  exact (lam.val p).map_smul (f.val p) _

@[simp] theorem pairing_add_left (lam mu : DualSection) (s : Section B) :
    pairing B D (lam + mu) s = pairing B D lam s + pairing B D mu s := rfl

@[simp] theorem pairing_smul_left (c : ℝ) (lam : DualSection) (s : Section B) :
    pairing B D (c • lam) s = c • pairing B D lam s := rfl

@[simp] theorem pairing_mul_left (f : GlobalSmooth S) (lam : DualSection) (s : Section B) :
    letI := D.space.topology
    pairing B D (mulSection f lam) s = f * pairing B D lam s := by
  letI := D.space.topology
  rfl

/-- The dual formula is initially an operator on sections. -/
noncomputable def dualDefect (C : Connection B) (X : Field S) (lam : DualSection) :
    Section B →ₗ[ℝ] GlobalSmooth S where
  toFun s := act S X (pairing B D lam s) - pairing B D lam (C.cov X s)
  map_add' s t := by simp only [map_add, pairing_add_right]; abel
  map_smul' c s := by simp only [map_smul, pairing_smul_right, Derivation.map_smul, RingHom.id_apply, smul_sub]

/-- Cancellation of the two derivatives of a scalar is the descent condition. -/
theorem dualDefect_mul (C : Connection B) (X : Field S) (lam : DualSection)
    (f : GlobalSmooth S) (s : Section B) :
    dualDefect B D C X lam (mulSection f s) = f * dualDefect B D C X lam s := by
  change act S X (pairing B D lam (mulSection f s)) -
      pairing B D lam (C.cov X (mulSection f s)) = _
  rw [pairing_mul_right, C.leibniz, pairing_add_right, pairing_mul_right, pairing_mul_right,
    Derivation.leibniz]
  change f * act S X (pairing B D lam s) + pairing B D lam s * act S X f -
      (act S X f * pairing B D lam s + f * pairing B D lam (C.cov X s)) =
        f * (act S X (pairing B D lam s) - pairing B D lam (C.cov X s))
  ring

/-- The pointwise evaluation of the defect. -/
noncomputable def dualDefectAt (C : Connection B) (X : Field S)
    (lam : DualSection) (p : M) : Section B →ₗ[ℝ] ℝ where
  toFun s := (dualDefect B D C X lam s).val p
  map_add' s t := congrArg (fun f : GlobalSmooth S => f.val p) (map_add _ s t)
  map_smul' c s := congrArg (fun f : GlobalSmooth S => f.val p) (map_smul _ c s)

theorem dualDefectAt_mul (C : Connection B) (X : Field S)
    (lam : DualSection) (p : M) (f : GlobalSmooth S) (s : Section B) :
    dualDefectAt B D C X lam p (mulSection f s) = f.val p * dualDefectAt B D C X lam p s :=
  congrArg (fun g : GlobalSmooth S => g.val p) (dualDefect_mul B D C X lam f s)

/-- The formula descends to a linear functional on each original fiber. -/
noncomputable def dualValue (C : Connection B) (X : Field S)
    (lam : DualSection) (p : M) : Module.Dual ℝ (E p) :=
  fiberFunctional B p (dualDefectAt B D C X lam p) (dualDefectAt_mul B D C X lam p)

@[simp] theorem dualValue_apply (C : Connection B) (X : Field S)
    (lam : DualSection) (s : Section B) (p : M) :
    dualValue B D C X lam p (s.val p) =
      (act S X (pairing B D lam s)).val p - lam.val p ((C.cov X s).val p) :=
  fiberFunctional_apply B p _ _ s

/-- The descended functional is a smooth section, tested on global sections. -/
noncomputable def dualSection (C : Connection B) (X : Field S)
    (lam : DualSection) : DualSection := by
  refine ⟨dualValue B D C X lam, dual_smooth_of_evaluations B D _ ?_⟩
  intro s p
  have h : VectorSmoothAt S.smoothStructure.val
      (fun q => (dualDefect B D C X lam s).val q) p :=
    (SmoothManifolds.scalarContDiffAt_iff _ _ _ _).mp
      ((SmoothManifolds.mem_globalSmoothAlgebra_iff S _).mp
        (dualDefect B D C X lam s).property p)
  exact h.congr (Filter.Eventually.of_forall (fun q => (dualValue_apply B D C X lam s q).symm))

@[simp] theorem dualSection_apply (C : Connection B) (X : Field S)
    (lam : DualSection) (s : Section B) (p : M) :
    (dualSection B D C X lam).val p (s.val p) =
      (act S X (pairing B D lam s)).val p - lam.val p ((C.cov X s).val p) :=
  dualValue_apply B D C X lam s p

/-- Global sections test equality on every fiber, including rank zero. -/
theorem dual_ext (lam mu : DualSection)
    (h : ∀ (s : Section B) (p : M), lam.val p (s.val p) = mu.val p (s.val p)) : lam = mu := by
  apply Subtype.ext
  funext p
  apply LinearMap.ext
  intro v
  obtain ⟨s, hs⟩ := ConnectionForms.section_evaluation_surjective B p v
  rw [← hs]
  exact h s p

/-- Additivity of the constructed dual derivative in its section argument. -/
theorem dualSection_add (C : Connection B) (X : Field S) (lam mu : DualSection) :
    dualSection B D C X (lam + mu) = dualSection B D C X lam + dualSection B D C X mu := by
  apply dual_ext B D
  intro s p
  simp only [dualSection_apply, pairing_add_left, map_add,
    Subalgebra.coe_add, Pi.add_apply, Submodule.coe_add, LinearMap.add_apply]
  abel

theorem dualSection_smul (C : Connection B) (X : Field S) (c : ℝ) (lam : DualSection) :
    dualSection B D C X (c • lam) = c • dualSection B D C X lam := by
  apply dual_ext B D
  intro s p
  simp only [dualSection_apply, pairing_smul_left, Derivation.map_smul,
    Subalgebra.coe_smul, Pi.smul_apply, Submodule.coe_smul_of_tower,
    LinearMap.smul_apply, smul_eq_mul]
  ring

theorem dualSection_add_field (C : Connection B) (X Y : Field S) (lam : DualSection) :
    dualSection B D C (X + Y) lam = dualSection B D C X lam + dualSection B D C Y lam := by
  apply dual_ext B D
  intro s p
  simp only [dualSection_apply, act_add_field, map_add,
    pairing_add_right, Subalgebra.coe_add, Pi.add_apply, Submodule.coe_add, LinearMap.add_apply]
  abel

theorem dualSection_smul_field (C : Connection B) (c : ℝ) (X : Field S) (lam : DualSection) :
    dualSection B D C (c • X) lam = c • dualSection B D C X lam := by
  apply dual_ext B D
  intro s p
  simp only [dualSection_apply, act_smul_field, map_smul,
    Subalgebra.coe_smul, Pi.smul_apply, Submodule.coe_smul_of_tower,
    LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
  ring

theorem dualSection_mul_field (C : Connection B) (f : GlobalSmooth S) (X : Field S)
    (lam : DualSection) :
    letI := D.space.topology
    dualSection B D C (mulSection f X) lam = mulSection f (dualSection B D C X lam) := by
  letI := D.space.topology
  apply dual_ext B D
  intro s p
  simp only [dualSection_apply, act_mul_field, C.linear_field,
    pairing_mul_right, Subalgebra.coe_mul, Pi.mul_apply,
    ConnectionForms.mulSection_apply, map_smul, smul_eq_mul, LinearMap.smul_apply]
  ring

theorem dualSection_leibniz (C : Connection B) (X : Field S) (f : GlobalSmooth S)
    (lam : DualSection) :
    letI := D.space.topology
    dualSection B D C X (mulSection f lam) =
      mulSection (act S X f) lam + mulSection f (dualSection B D C X lam) := by
  letI := D.space.topology
  apply dual_ext B D
  intro s p
  simp only [dualSection_apply, pairing_mul_left, Derivation.leibniz,
    Subalgebra.coe_add, Subalgebra.coe_mul, Pi.add_apply, Pi.mul_apply,
    ConnectionForms.mulSection_apply, Submodule.coe_add, LinearMap.add_apply,
    smul_eq_mul, LinearMap.smul_apply, pairing_apply]
  ring

/-- The induced dual connection; all its defining axioms have been proved. -/
noncomputable def dualConnection (C : Connection B) :
    letI := D.space.topology; Connection D.space.bundle := by
  letI := D.space.topology
  exact {
    cov := {
      toFun := fun X => {
        toFun := dualSection B D C X
        map_add' := dualSection_add B D C X
        map_smul' := dualSection_smul B D C X }
      map_add' := fun X Y => by
        apply LinearMap.ext
        intro lam
        exact dualSection_add_field B D C X Y lam
      map_smul' := fun c X => by
        apply LinearMap.ext
        intro lam
        exact dualSection_smul_field B D C c X lam }
    linear_field := dualSection_mul_field B D C
    leibniz := dualSection_leibniz B D C }

/-- The defining formula on every actual dual pair. -/
theorem dualConnection_rule (C : Connection B) : DualRule C D (dualConnection B D C) := by
  letI := D.space.topology
  intro X lam s p
  change (dualSection B D C X lam).val p (s.val p) = _
  rw [dualSection_apply, ← ConnectionForms.scalarDerivative_global (pairing B D lam s) X p]
  rfl

/-- Uniqueness does not require any global trivialization. -/
theorem dualConnection_unique (C : Connection B) :
    letI := D.space.topology
    ∀ K : Connection D.space.bundle, DualRule C D K → K = dualConnection B D C := by
  letI := D.space.topology
  intro K hK
  have heq : K.cov = (dualConnection B D C).cov := by
    apply LinearMap.ext
    intro X
    apply LinearMap.ext
    intro lam
    apply dual_ext B D
    intro s p
    rw [hK X lam s p, dualConnection_rule B D C X lam s p]
  cases K
  cases h : dualConnection B D C
  simp only [h] at heq
  congr 1

theorem dual_exists_unique : P202Specs.Geometry.InducedConnections.dual_exists_uniqueType.{u,v,w} := by
  intro n r a M _ S ι E _ _ _ B C D
  letI := D.space.topology
  exact ⟨dualConnection B D C, dualConnection_rule B D C,
    fun K hK => dualConnection_unique B D C K hK⟩

/-- The elementary contraction (evaluation) commutes with differentiation. -/
theorem dual_contraction (C : Connection B) (X : Field S) (lam : DualSection) (s : Section B) :
    letI := D.space.topology
    act S X (pairing B D lam s) =
      pairing B D ((dualConnection B D C).cov X lam) s + pairing B D lam (C.cov X s) := by
  letI := D.space.topology
  apply Subtype.ext
  funext p
  change _ = (dualSection B D C X lam).val p (s.val p) + lam.val p ((C.cov X s).val p)
  rw [dualSection_apply]
  ring

end DualConstruction

section TensorSections
variable {n r k : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {κ : Type t}
  {E : M → Type w} {F : M → Type z}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [∀ p, AddCommGroup (F p)] [∀ p, Module ℝ (F p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean k) F)]
  (B : SmoothVectorBundle S r ι E) (A : SmoothVectorBundle S k κ F)
  (T : TensorBundle B A)

/-- Pure products are smooth sections of the actual tensor-product bundle. -/
theorem tensorSection_smooth (s : Section B) (u : Section A) :
    letI := T.space.topology
    SmoothSection T.space.bundle (fun p => TensorProduct.tmul ℝ (s.val p) (u.val p)) := by
  letI := T.space.topology
  intro p
  obtain ⟨i, hi⟩ := B.covers p
  obtain ⟨j, hj⟩ := A.covers p
  have hBi : IsOpen (B.baseSet i) := B.trivialization_baseSet i ▸ (B.trivialization i).open_baseSet
  have hAj : IsOpen (A.baseSet j) := A.trivialization_baseSet j ▸ (A.trivialization j).open_baseSet
  apply SmoothManifolds.SectionExtension.smoothAt_of_coordinates T.space.bundle (i, j)
    (by rw [T.baseSet]; exact ⟨hi, hj⟩)
  apply VectorSmoothAt.pi
  intro l
  have hs := SmoothManifolds.SectionExtension.coordinates_smoothAt B i hi (s.property p)
  have hu := SmoothManifolds.SectionExtension.coordinates_smoothAt A j hj (u.property p)
  have hprod := ((hs.postcomp (ContinuousLinearMap.proj (finProdFinEquiv.symm l).1).contDiff).prod
    (hu.postcomp (ContinuousLinearMap.proj (finProdFinEquiv.symm l).2).contDiff)).postcomp
      (contDiff_fst.mul contDiff_snd)
  apply hprod.congr
  filter_upwards [hBi.mem_nhds hi, hAj.mem_nhds hj] with q hqB hqA
  rw [← finProdFinEquiv.apply_symm_apply l]
  simpa only [Equiv.symm_apply_apply, ContinuousLinearMap.proj_apply] using
    (T.coordinates (i, j) q (by rw [T.baseSet]; exact ⟨hqB, hqA⟩)
      (s.val q) (u.val q) (finProdFinEquiv.symm l).1 (finProdFinEquiv.symm l).2).symm

noncomputable def tensorSection (s : Section B) (u : Section A) :
    letI := T.space.topology; Section T.space.bundle := by
  letI := T.space.topology
  exact ⟨fun p => TensorProduct.tmul ℝ (s.val p) (u.val p), tensorSection_smooth B A T s u⟩

@[simp] theorem tensorSection_apply (s : Section B) (u : Section A) (p : M) :
    (tensorSection B A T s u).val p = TensorProduct.tmul ℝ (s.val p) (u.val p) := rfl

@[simp] theorem tensorSection_add_left (s t : Section B) (u : Section A) :
    tensorSection B A T (s + t) u = tensorSection B A T s u + tensorSection B A T t u := by
  apply Subtype.ext
  funext p
  exact TensorProduct.add_tmul _ _ _

@[simp] theorem tensorSection_add_right (s : Section B) (u v : Section A) :
    tensorSection B A T s (u + v) = tensorSection B A T s u + tensorSection B A T s v := by
  apply Subtype.ext
  funext p
  exact TensorProduct.tmul_add _ _ _

@[simp] theorem tensorSection_smul_left (c : ℝ) (s : Section B) (u : Section A) :
    tensorSection B A T (c • s) u = c • tensorSection B A T s u := by
  apply Subtype.ext
  funext p
  exact TensorProduct.smul_tmul' _ _ _

@[simp] theorem tensorSection_smul_right (c : ℝ) (s : Section B) (u : Section A) :
    tensorSection B A T s (c • u) = c • tensorSection B A T s u := by
  apply Subtype.ext
  funext p
  exact TensorProduct.tmul_smul _ _ _

@[simp] theorem tensorSection_mul_left (f : GlobalSmooth S) (s : Section B) (u : Section A) :
    letI := T.space.topology
    tensorSection B A T (mulSection f s) u = mulSection f (tensorSection B A T s u) := by
  letI := T.space.topology
  apply Subtype.ext
  funext p
  exact TensorProduct.smul_tmul' _ _ _

@[simp] theorem tensorSection_mul_right (f : GlobalSmooth S) (s : Section B) (u : Section A) :
    letI := T.space.topology
    tensorSection B A T s (mulSection f u) = mulSection f (tensorSection B A T s u) := by
  letI := T.space.topology
  apply Subtype.ext
  funext p
  exact TensorProduct.tmul_smul _ _ _

/-- The C∞(M)-balanced relation in the genuine tensor bundle. -/
theorem tensorSection_balance (f : GlobalSmooth S) (s : Section B) (u : Section A) :
    tensorSection B A T (mulSection f s) u = tensorSection B A T s (mulSection f u) := by
  rw [tensorSection_mul_left, tensorSection_mul_right]

/-- The required derivative on a pure product, before descent to all sections. -/
noncomputable def pureTensorDerivative (C : Connection B) (K : Connection A)
    (X : Field S) (s : Section B) (u : Section A) :
    letI := T.space.topology; Section T.space.bundle := by
  letI := T.space.topology
  exact tensorSection B A T (C.cov X s) u + tensorSection B A T s (K.cov X u)

/-- The product derivative respects moving a smooth scalar across the product.
The two scalar derivatives are equal; neither is discarded. -/
theorem pureTensorDerivative_balance (C : Connection B) (K : Connection A)
    (X : Field S) (f : GlobalSmooth S) (s : Section B) (u : Section A) :
    pureTensorDerivative B A T C K X (mulSection f s) u =
      pureTensorDerivative B A T C K X s (mulSection f u) := by
  letI := T.space.topology
  unfold pureTensorDerivative
  rw [C.leibniz, K.leibniz]
  simp only [tensorSection_add_left, tensorSection_add_right,
    tensorSection_mul_left, tensorSection_mul_right]
  abel

/-- The product derivative obeys the scalar Leibniz rule. -/
theorem pureTensorDerivative_leibniz (C : Connection B) (K : Connection A)
    (X : Field S) (f : GlobalSmooth S) (s : Section B) (u : Section A) :
    letI := T.space.topology
    pureTensorDerivative B A T C K X (mulSection f s) u =
      mulSection (act S X f) (tensorSection B A T s u) +
        mulSection f (pureTensorDerivative B A T C K X s u) := by
  letI := T.space.topology
  apply Subtype.ext
  funext p
  simp only [pureTensorDerivative, tensorSection_apply, C.leibniz,
    ConnectionForms.section_add_apply, ConnectionForms.mulSection_apply,
    TensorProduct.add_tmul, TensorProduct.smul_tmul', smul_add]
  abel

end TensorSections

section TensorDescent
variable {n r k : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {κ : Type t}
  {E : M → Type w} {F : M → Type z}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [∀ p, AddCommGroup (F p)] [∀ p, Module ℝ (F p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean k) F)]
  (B : SmoothVectorBundle S r ι E) (A : SmoothVectorBundle S k κ F)
  (T : TensorBundle B A)

/-- Formal real tensor products of global sections, used only as local
presentations. No assertion of global finite generation is made. -/
abbrev TensorPresentation := TensorProduct ℝ (Section B) (Section A)

/-- Evaluation of a formal presentation as a smooth tensor section. -/
noncomputable def tensorPresentationValue :
    letI := T.space.topology
    TensorPresentation B A →ₗ[ℝ] Section T.space.bundle := by
  letI := T.space.topology
  exact TensorProduct.lift {
    toFun := fun s => {
      toFun := tensorSection B A T s
      map_add' := tensorSection_add_right B A T s
      map_smul' := fun c u => tensorSection_smul_right B A T c s u }
    map_add' := fun s t => by
      apply LinearMap.ext
      intro u
      exact tensorSection_add_left B A T s t u
    map_smul' := fun c s => by
      apply LinearMap.ext
      intro u
      exact tensorSection_smul_left B A T c s u }

@[simp] theorem tensorPresentationValue_tmul (s : Section B) (u : Section A) :
    tensorPresentationValue B A T (TensorProduct.tmul ℝ s u) = tensorSection B A T s u := rfl

/-- The product-rule derivative on formal presentations. -/
noncomputable def tensorPresentationDerivative (C : Connection B) (K : Connection A) (X : Field S) :
    letI := T.space.topology
    TensorPresentation B A →ₗ[ℝ] Section T.space.bundle := by
  letI := T.space.topology
  exact (tensorPresentationValue B A T).comp
    (TensorProduct.map (C.cov X) (LinearMap.id : Section A →ₗ[ℝ] Section A) +
      TensorProduct.map (LinearMap.id : Section B →ₗ[ℝ] Section B) (K.cov X))

@[simp] theorem tensorPresentationDerivative_tmul (C : Connection B) (K : Connection A)
    (X : Field S) (s : Section B) (u : Section A) :
    tensorPresentationDerivative B A T C K X (TensorProduct.tmul ℝ s u) =
      pureTensorDerivative B A T C K X s u := by
  letI := T.space.topology
  simp only [tensorPresentationDerivative, LinearMap.comp_apply, LinearMap.add_apply,
    TensorProduct.map_tmul, LinearMap.id_apply, map_add, tensorPresentationValue_tmul,
    pureTensorDerivative]

/-- Evaluation of a tensor by a pair of dual vectors. -/
noncomputable def tensorEvaluation {V : Type*} {W : Type*}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (lam : Module.Dual ℝ V) (mu : Module.Dual ℝ W) :
    TensorProduct ℝ V W →ₗ[ℝ] ℝ :=
  TensorProduct.dualDistrib ℝ V W (TensorProduct.tmul ℝ lam mu)

@[simp] theorem tensorEvaluation_tmul {V : Type*} {W : Type*}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (lam : Module.Dual ℝ V) (mu : Module.Dual ℝ W) (v : V) (w : W) :
    tensorEvaluation lam mu (TensorProduct.tmul ℝ v w) = lam v * mu w := rfl

include B A in
/-- Dual pairs separate tensors in each actual fiber. -/
theorem tensorEvaluation_separates (p : M) (v : TensorProduct ℝ (E p) (F p))
    (h : ∀ (lam : Module.Dual ℝ (E p)) (mu : Module.Dual ℝ (F p)), tensorEvaluation lam mu v = 0) :
    v = 0 := by
  obtain ⟨i, hi⟩ := B.covers p
  obtain ⟨j, hj⟩ := A.covers p
  let e := B.fiberCoordinates i p hi
  let f := A.fiberCoordinates j p hj
  apply (SmoothManifolds.BundleOperations.tensorCoordinates e f).injective
  rw [map_zero]
  funext l
  obtain ⟨⟨il, jl⟩, rfl⟩ := finProdFinEquiv.surjective l
  have heq (w : TensorProduct ℝ (E p) (F p)) :
      SmoothManifolds.BundleOperations.tensorCoordinates e f w (finProdFinEquiv (il, jl)) =
        tensorEvaluation ((LinearMap.proj il).comp e.toLinearMap)
          ((LinearMap.proj jl).comp f.toLinearMap) w := by
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul v w => simp [tensorEvaluation_tmul]
    | add v w hv hw => simp only [map_add, Pi.add_apply, hv, hw]
  exact (heq v).trans (h _ _)

variable (D : DualBundle B) (H : DualBundle A)
set_option quotPrecheck false in
local notation "BDualSection" => (letI := D.space.topology; Section D.space.bundle)
set_option quotPrecheck false in
local notation "ADualSection" => (letI := H.space.topology; Section H.space.bundle)

noncomputable def pairingLinear (lam : BDualSection) : Section B →ₗ[ℝ] GlobalSmooth S where
  toFun := pairing B D lam
  map_add' := pairing_add_right B D lam
  map_smul' := pairing_smul_right B D lam

/-- Evaluation on formal presentations is genuinely a smooth scalar. -/
noncomputable def tensorPresentationPairing (lam : BDualSection) (mu : ADualSection) :
    TensorPresentation B A →ₗ[ℝ] GlobalSmooth S :=
  TensorProduct.lift (((LinearMap.mul ℝ (GlobalSmooth S)).comp
    (pairingLinear B D lam)).compl₂ (pairingLinear A H mu))

@[simp] theorem tensorPresentationPairing_tmul (lam : BDualSection) (mu : ADualSection)
    (s : Section B) (u : Section A) :
    tensorPresentationPairing B A D H lam mu (TensorProduct.tmul ℝ s u) =
      pairing B D lam s * pairing A H mu u := rfl

theorem tensorPresentationPairing_apply (lam : BDualSection) (mu : ADualSection)
    (x : TensorPresentation B A) (p : M) :
    (tensorPresentationPairing B A D H lam mu x).val p =
      tensorEvaluation (lam.val p) (mu.val p) ((tensorPresentationValue B A T x).val p) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s u => rfl
  | add x y hx hy =>
    simp only [map_add, Subalgebra.coe_add, Pi.add_apply, Submodule.coe_add, hx, hy]

/-- Differentiation of a tensor presentation paired with two dual sections.
The dual connection terms account exactly for differentiation of the tests. -/
theorem tensorPresentationDerivative_pairing (C : Connection B) (K : Connection A)
    (X : Field S) (lam : BDualSection) (mu : ADualSection)
    (x : TensorPresentation B A) (p : M) :
    tensorEvaluation (lam.val p) (mu.val p)
        ((tensorPresentationDerivative B A T C K X x).val p) =
      (act S X (tensorPresentationPairing B A D H lam mu x)).val p -
        tensorEvaluation ((dualSection B D C X lam).val p) (mu.val p)
          ((tensorPresentationValue B A T x).val p) -
        tensorEvaluation (lam.val p) ((dualSection A H K X mu).val p)
          ((tensorPresentationValue B A T x).val p) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s u =>
    simp only [tensorPresentationDerivative_tmul, pureTensorDerivative,
      tensorPresentationValue_tmul, tensorPresentationPairing_tmul,
      ConnectionForms.section_add_apply, tensorSection_apply, map_add,
      tensorEvaluation_tmul, dualSection_apply, Derivation.leibniz,
      Subalgebra.coe_add, Subalgebra.coe_mul, Pi.add_apply, Pi.mul_apply,
      smul_eq_mul, pairing_apply]
    ring
  | add x y hx hy =>
    simp only [map_add, Submodule.coe_add, Subalgebra.coe_add, Pi.add_apply, hx, hy]
    ring

include D H in
/-- The formal derivative vanishes on every locally zero presentation.
This is the well-definedness argument on the actual tensor fibers. -/
theorem tensorPresentationDerivative_zero (C : Connection B) (K : Connection A)
    (X : Field S) (x : TensorPresentation B A) (p : M)
    (hx : ∀ᶠ q in 𝓝 p, (tensorPresentationValue B A T x).val q = 0) :
    (tensorPresentationDerivative B A T C K X x).val p = 0 := by
  letI := D.space.topology
  letI := H.space.topology
  apply tensorEvaluation_separates B A p
  intro lam mu
  obtain ⟨s, hs⟩ := ConnectionForms.section_evaluation_surjective D.space.bundle p lam
  obtain ⟨u, hu⟩ := ConnectionForms.section_evaluation_surjective H.space.bundle p mu
  rw [← hs, ← hu, tensorPresentationDerivative_pairing B A T D H C K X s u x p]
  have hz : (tensorPresentationPairing B A D H s u x).val =ᶠ[𝓝 p] (0 : GlobalSmooth S).val := by
    filter_upwards [hx] with q hq
    rw [tensorPresentationPairing_apply B A T D H, hq, map_zero]
    rfl
  have hd := ConnectionForms.act_congr X (tensorPresentationPairing B A D H s u x) 0 p hz
  simpa only [hx.self_of_nhds, map_zero, ZeroMemClass.coe_zero, Pi.zero_apply, sub_zero] using hd

/-- The prescribed tensor charts agree with the tensor products of the
prescribed original fiber charts. -/
theorem tensorFiberCoordinates (i : ι) (j : κ) (p : M)
    (hi : p ∈ B.baseSet i) (hj : p ∈ A.baseSet j) :
    letI := T.space.topology
    T.space.bundle.fiberCoordinates (i, j) p (by rw [T.baseSet]; exact ⟨hi, hj⟩) =
      SmoothManifolds.BundleOperations.tensorCoordinates (B.fiberCoordinates i p hi)
        (A.fiberCoordinates j p hj) := by
  letI := T.space.topology
  apply LinearEquiv.toLinearMap_injective
  apply TensorProduct.ext'
  intro v w
  funext l
  obtain ⟨⟨il, jl⟩, rfl⟩ := finProdFinEquiv.surjective l
  change (T.space.bundle.fiberCoordinates (i, j) p _ (TensorProduct.tmul ℝ v w)) _ =
    (SmoothManifolds.BundleOperations.tensorCoordinates (B.fiberCoordinates i p hi)
      (A.fiberCoordinates j p hj)) (TensorProduct.tmul ℝ v w) _
  rw [SmoothManifolds.BundleOperations.tensorCoordinates_tmul]
  exact T.coordinates (i, j) p (by rw [T.baseSet]; exact ⟨hi, hj⟩) v w il jl

/-- A tensor trivialization frame consists of the actual pure products of
the original trivialization frames. -/
theorem tensorTrivializationFrame (i : ι) (j : κ)
    (p : M) (hi : p ∈ B.baseSet i) (hj : p ∈ A.baseSet j) (l : Fin (r*k)) :
    letI := T.space.topology
    (SmoothManifolds.ConstantRankBundles.trivializationFrame T.space.bundle (i, j)).section_ l
      ⟨p, by rw [T.baseSet]; exact ⟨hi, hj⟩⟩ =
      TensorProduct.tmul ℝ
        ((SmoothManifolds.ConstantRankBundles.trivializationFrame B i).section_
          (finProdFinEquiv.symm l).1 ⟨p, hi⟩)
        ((SmoothManifolds.ConstantRankBundles.trivializationFrame A j).section_
          (finProdFinEquiv.symm l).2 ⟨p, hj⟩) := by
  letI := T.space.topology
  have hpT : p ∈ T.space.bundle.baseSet (i,j) := by rw [T.baseSet]; exact ⟨hi, hj⟩
  change (T.space.bundle.fiberCoordinates (i, j) p hpT).symm ((Pi.basisFun ℝ (Fin (r*k))) l) =
    TensorProduct.tmul ℝ
      ((B.fiberCoordinates i p hi).symm ((Pi.basisFun ℝ (Fin r)) (finProdFinEquiv.symm l).1))
      ((A.fiberCoordinates j p hj).symm ((Pi.basisFun ℝ (Fin k)) (finProdFinEquiv.symm l).2))
  rw [tensorFiberCoordinates B A T i j p hi hj]
  simp only [Pi.basisFun_apply, SmoothManifolds.BundleOperations.tensorCoordinates_symm_single]

/-- Every smooth tensor section admits a finite pure-section presentation
near each point. This is local generation, not global triviality. -/
theorem exists_tensorPresentation :
    letI := T.space.topology
    ∀ (s : Section T.space.bundle) (p : M),
      ∃ x : TensorPresentation B A,
        ∀ᶠ q in 𝓝 p, (tensorPresentationValue B A T x).val q = s.val q := by
  letI := T.space.topology
  intro s p
  classical
  obtain ⟨i, hi⟩ := B.covers p
  obtain ⟨j, hj⟩ := A.covers p
  have hpT : p ∈ T.space.bundle.baseSet (i, j) := by rw [T.baseSet]; exact ⟨hi, hj⟩
  let b := SmoothManifolds.ConstantRankBundles.trivializationFrame B i
  let a := SmoothManifolds.ConstantRankBundles.trivializationFrame A j
  let t := SmoothManifolds.ConstantRankBundles.trivializationFrame T.space.bundle (i, j)
  have hBT : IsOpen (B.baseSet i) := B.trivialization_baseSet i ▸ (B.trivialization i).open_baseSet
  have hAT : IsOpen (A.baseSet j) := A.trivialization_baseSet j ▸ (A.trivialization j).open_baseSet
  have hTT : IsOpen (T.space.bundle.baseSet (i,j)) :=
    T.space.bundle.trivialization_baseSet (i,j) ▸ (T.space.bundle.trivialization (i,j)).open_baseSet
  obtain ⟨e, he⟩ := ConnectionForms.local_frame_representative B b ⟨p, hi⟩
  obtain ⟨u, hu⟩ := ConnectionForms.local_frame_representative A a ⟨p, hj⟩
  have hs := (restrictGlobalSection s _ hTT).property
  obtain ⟨f, hf⟩ := ConnectionForms.local_coefficients_representative T.space.bundle t
    (fun q => s.val q.val) hs ⟨p, hpT⟩
  refine ⟨∑ l : Fin (r*k), TensorProduct.tmul ℝ
    (mulSection (f l) (e (finProdFinEquiv.symm l).1)) (u (finProdFinEquiv.symm l).2), ?_⟩
  filter_upwards [hBT.mem_nhds hi, hAT.mem_nhds hj, hTT.mem_nhds hpT,
    Filter.eventually_all.mpr he, Filter.eventually_all.mpr hu, Filter.eventually_all.mpr hf]
    with q hqB hqA hqT heq huq hfq
  simp only [map_sum, Submodule.coe_sum, Finset.sum_apply,
    tensorPresentationValue_tmul, tensorSection_apply, ConnectionForms.mulSection_apply]
  rw [SmoothManifolds.Frames.section_expansion T.space.bundle _ hTT t
    (fun z => s.val z.val) ⟨q, hqT⟩]
  apply Finset.sum_congr rfl
  intro l _
  rw [hfq l, totalize_of_mem _ q hqT, heq, huq,
    SmoothManifolds.SectionExtension.totalSection_of_mem _ q hqB,
    SmoothManifolds.SectionExtension.totalSection_of_mem _ q hqA,
    ← TensorProduct.smul_tmul', ← tensorTrivializationFrame B A T i j q hqB hqA l]

/-- Equivalent local presentations have the same derivative in the fiber. -/
theorem tensorPresentationDerivative_congr (C : Connection B) (K : Connection A)
    (X : Field S) (x y : TensorPresentation B A) (p : M)
    (hxy : ∀ᶠ q in 𝓝 p, (tensorPresentationValue B A T x).val q =
      (tensorPresentationValue B A T y).val q) :
    (tensorPresentationDerivative B A T C K X x).val p =
      (tensorPresentationDerivative B A T C K X y).val p := by
  let d := Classical.choice (SmoothManifolds.BundleOperations.exists_dual B)
  let h := Classical.choice (SmoothManifolds.BundleOperations.exists_dual A)
  have hz : ∀ᶠ q in 𝓝 p, (tensorPresentationValue B A T (x-y)).val q = 0 := by
    filter_upwards [hxy] with q hq
    simpa only [map_sub, Submodule.coe_sub, Pi.sub_apply, sub_eq_zero] using hq
  have hd := tensorPresentationDerivative_zero B A T d h C K X (x-y) p hz
  exact sub_eq_zero.mp (by simpa only [map_sub, Submodule.coe_sub, Pi.sub_apply] using hd)

noncomputable def chosenTensorPresentation :
    letI := T.space.topology
    Section T.space.bundle → M → TensorPresentation B A := by
  letI := T.space.topology
  exact fun s p => Classical.choose (exists_tensorPresentation B A T s p)

theorem chosenTensorPresentation_spec :
    letI := T.space.topology
    ∀ (s : Section T.space.bundle) (p : M),
      ∀ᶠ q in 𝓝 p, (tensorPresentationValue B A T (chosenTensorPresentation B A T s p)).val q = s.val q := by
  letI := T.space.topology
  intro s p
  exact Classical.choose_spec (exists_tensorPresentation B A T s p)

noncomputable def tensorDerivativeValue (C : Connection B) (K : Connection A) (X : Field S) :
    letI := T.space.topology
    Section T.space.bundle → (p : M) → TensorProduct ℝ (E p) (F p) := by
  letI := T.space.topology
  exact fun s p => (tensorPresentationDerivative B A T C K X (chosenTensorPresentation B A T s p)).val p

theorem tensorDerivativeValue_eq (C : Connection B) (K : Connection A) (X : Field S) :
    letI := T.space.topology
    ∀ (s : Section T.space.bundle) (p : M) (x : TensorPresentation B A),
      (∀ᶠ q in 𝓝 p, (tensorPresentationValue B A T x).val q = s.val q) →
      tensorDerivativeValue B A T C K X s p = (tensorPresentationDerivative B A T C K X x).val p := by
  letI := T.space.topology
  intro s p x hx
  apply tensorPresentationDerivative_congr B A T C K X _ x p
  filter_upwards [chosenTensorPresentation_spec B A T s p, hx] with q hq hqx
  exact hq.trans hqx.symm

/-- Smoothness follows from any one finite presentation on a neighborhood. -/
theorem tensorDerivativeValue_smooth (C : Connection B) (K : Connection A) (X : Field S) :
    letI := T.space.topology
    ∀ s : Section T.space.bundle, SmoothSection T.space.bundle (tensorDerivativeValue B A T C K X s) := by
  letI := T.space.topology
  intro s p
  obtain ⟨x, hx⟩ := exists_tensorPresentation B A T s p
  apply SmoothManifolds.SectionExtension.section_smoothAt_congr T.space.bundle
    ((tensorPresentationDerivative B A T C K X x).property p)
  filter_upwards [hx.eventually_nhds] with q hq
  exact (tensorDerivativeValue_eq B A T C K X s q x hq).symm

noncomputable def sectionMultiplication (f : GlobalSmooth S) : Section B →ₗ[ℝ] Section B where
  toFun := mulSection f
  map_add' s t := by
    apply Subtype.ext
    funext p
    exact smul_add _ _ _
  map_smul' c s := by
    apply Subtype.ext
    funext p
    exact smul_comm _ _ _

noncomputable def multiplyPresentation (f : GlobalSmooth S) : TensorPresentation B A →ₗ[ℝ] TensorPresentation B A :=
  TensorProduct.map (sectionMultiplication B f) LinearMap.id

theorem tensorPresentationValue_mul (f : GlobalSmooth S) (x : TensorPresentation B A) :
    letI := T.space.topology
    tensorPresentationValue B A T (multiplyPresentation B A f x) =
      mulSection f (tensorPresentationValue B A T x) := by
  letI := T.space.topology
  induction x using TensorProduct.induction_on with
  | zero =>
    apply Subtype.ext
    funext p
    simp [ConnectionForms.mulSection_apply]
  | tmul s u => exact tensorSection_mul_left B A T f s u
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    exact (sectionMultiplication T.space.bundle f).map_add _ _ |>.symm

theorem tensorPresentationDerivative_mul (C : Connection B) (K : Connection A)
    (X : Field S) (f : GlobalSmooth S) (x : TensorPresentation B A) :
    letI := T.space.topology
    tensorPresentationDerivative B A T C K X (multiplyPresentation B A f x) =
      mulSection (act S X f) (tensorPresentationValue B A T x) +
        mulSection f (tensorPresentationDerivative B A T C K X x) := by
  letI := T.space.topology
  induction x using TensorProduct.induction_on with
  | zero =>
    apply Subtype.ext
    funext p
    simp [ConnectionForms.mulSection_apply]
  | tmul s u =>
    exact pureTensorDerivative_leibniz B A T C K X f s u
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    change _ = (sectionMultiplication T.space.bundle (act S X f)) (_ + _) +
      (sectionMultiplication T.space.bundle f) (_ + _)
    rw [map_add, map_add]
    simp only [sectionMultiplication, LinearMap.coe_mk, AddHom.coe_mk]
    abel

theorem tensorPresentationDerivative_add_field (C : Connection B) (K : Connection A)
    (X Y : Field S) (x : TensorPresentation B A) :
    tensorPresentationDerivative B A T C K (X+Y) x =
      tensorPresentationDerivative B A T C K X x + tensorPresentationDerivative B A T C K Y x := by
  letI := T.space.topology
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s u =>
    simp only [tensorPresentationDerivative_tmul, pureTensorDerivative, map_add, LinearMap.add_apply,
      tensorSection_add_left, tensorSection_add_right]
    abel
  | add x y hx hy => simp only [map_add, hx, hy]; abel

theorem tensorPresentationDerivative_smul_field (C : Connection B) (K : Connection A)
    (c : ℝ) (X : Field S) (x : TensorPresentation B A) :
    tensorPresentationDerivative B A T C K (c • X) x = c • tensorPresentationDerivative B A T C K X x := by
  letI := T.space.topology
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s u =>
    simp only [tensorPresentationDerivative_tmul, pureTensorDerivative, map_smul, LinearMap.smul_apply,
      tensorSection_smul_left, tensorSection_smul_right, smul_add, RingHom.id_apply]
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]

theorem tensorPresentationDerivative_mul_field (C : Connection B) (K : Connection A)
    (f : GlobalSmooth S) (X : Field S) (x : TensorPresentation B A) :
    letI := T.space.topology
    tensorPresentationDerivative B A T C K (mulSection f X) x =
      mulSection f (tensorPresentationDerivative B A T C K X x) := by
  letI := T.space.topology
  induction x using TensorProduct.induction_on with
  | zero =>
    apply Subtype.ext
    funext p
    simp [ConnectionForms.mulSection_apply]
  | tmul s u =>
    simp only [tensorPresentationDerivative_tmul, pureTensorDerivative, C.linear_field, K.linear_field,
      tensorSection_mul_left, tensorSection_mul_right]
    exact (sectionMultiplication T.space.bundle f).map_add _ _ |>.symm
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    exact (sectionMultiplication T.space.bundle f).map_add _ _ |>.symm

end TensorDescent


section TensorConnection
variable {n r k : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {κ : Type t}
  {E : M → Type w} {F : M → Type z}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [∀ p, AddCommGroup (F p)] [∀ p, Module ℝ (F p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean k) F)]
  (B : SmoothVectorBundle S r ι E) (A : SmoothVectorBundle S k κ F)
  (T : TensorBundle B A) (C : Connection B) (K : Connection A)
set_option quotPrecheck false in
local notation "TensorSection" => (letI := T.space.topology; Section T.space.bundle)

theorem tensorDerivativeValue_add (X : Field S) (s t : TensorSection) (p : M) :
    tensorDerivativeValue B A T C K X (s+t) p =
      tensorDerivativeValue B A T C K X s p + tensorDerivativeValue B A T C K X t p := by
  letI := T.space.topology
  obtain ⟨x, hx⟩ := exists_tensorPresentation B A T s p
  obtain ⟨y, hy⟩ := exists_tensorPresentation B A T t p
  have hxy : ∀ᶠ q in 𝓝 p, (tensorPresentationValue B A T (x+y)).val q = (s+t).val q := by
    filter_upwards [hx, hy] with q hq hq'
    simp only [map_add, ConnectionForms.section_add_apply, hq, hq']
  rw [tensorDerivativeValue_eq B A T C K X (s+t) p (x+y) hxy,
    tensorDerivativeValue_eq B A T C K X s p x hx,
    tensorDerivativeValue_eq B A T C K X t p y hy, map_add]
  rfl

theorem tensorDerivativeValue_smul (X : Field S) (c : ℝ) (s : TensorSection) (p : M) :
    tensorDerivativeValue B A T C K X (c • s) p = c • tensorDerivativeValue B A T C K X s p := by
  letI := T.space.topology
  obtain ⟨x, hx⟩ := exists_tensorPresentation B A T s p
  have hcx : ∀ᶠ q in 𝓝 p, (tensorPresentationValue B A T (c • x)).val q = (c • s).val q := by
    filter_upwards [hx] with q hq
    simp only [map_smul, ConnectionForms.section_smul_apply, hq]
  rw [tensorDerivativeValue_eq B A T C K X (c • s) p (c • x) hcx,
    tensorDerivativeValue_eq B A T C K X s p x hx, map_smul]
  rfl

theorem tensorDerivativeValue_add_field (X Y : Field S) (s : TensorSection) (p : M) :
    tensorDerivativeValue B A T C K (X+Y) s p =
      tensorDerivativeValue B A T C K X s p + tensorDerivativeValue B A T C K Y s p := by
  obtain ⟨x, hx⟩ := exists_tensorPresentation B A T s p
  rw [tensorDerivativeValue_eq B A T C K (X+Y) s p x hx,
    tensorDerivativeValue_eq B A T C K X s p x hx,
    tensorDerivativeValue_eq B A T C K Y s p x hx,
    tensorPresentationDerivative_add_field]
  rfl

theorem tensorDerivativeValue_smul_field (c : ℝ) (X : Field S) (s : TensorSection) (p : M) :
    tensorDerivativeValue B A T C K (c • X) s p = c • tensorDerivativeValue B A T C K X s p := by
  obtain ⟨x, hx⟩ := exists_tensorPresentation B A T s p
  rw [tensorDerivativeValue_eq B A T C K (c • X) s p x hx,
    tensorDerivativeValue_eq B A T C K X s p x hx,
    tensorPresentationDerivative_smul_field]
  rfl

theorem tensorDerivativeValue_mul_field (f : GlobalSmooth S) (X : Field S)
    (s : TensorSection) (p : M) :
    tensorDerivativeValue B A T C K (mulSection f X) s p =
      f.val p • tensorDerivativeValue B A T C K X s p := by
  obtain ⟨x, hx⟩ := exists_tensorPresentation B A T s p
  rw [tensorDerivativeValue_eq B A T C K (mulSection f X) s p x hx,
    tensorDerivativeValue_eq B A T C K X s p x hx,
    tensorPresentationDerivative_mul_field]
  rfl

theorem tensorDerivativeValue_leibniz (X : Field S) (f : GlobalSmooth S)
    (s : TensorSection) (p : M) :
    letI := T.space.topology
    tensorDerivativeValue B A T C K X (mulSection f s) p =
      (act S X f).val p • s.val p + f.val p • tensorDerivativeValue B A T C K X s p := by
  letI := T.space.topology
  obtain ⟨x, hx⟩ := exists_tensorPresentation B A T s p
  have hfx : ∀ᶠ q in 𝓝 p, (tensorPresentationValue B A T (multiplyPresentation B A f x)).val q =
      (mulSection f s).val q := by
    filter_upwards [hx] with q hq
    rw [tensorPresentationValue_mul, ConnectionForms.mulSection_apply,
      ConnectionForms.mulSection_apply, hq]
  rw [tensorDerivativeValue_eq B A T C K X (mulSection f s) p _ hfx,
    tensorDerivativeValue_eq B A T C K X s p x hx, tensorPresentationDerivative_mul]
  change _ • (tensorPresentationValue B A T x).val p + _ = _
  rw [hx.self_of_nhds]
  rfl

/-- The connection on the actual tensor-product bundle, for any pair of
connections; its smoothness and all its defining axioms are derived. -/
noncomputable def tensorConnection :
    letI := T.space.topology; Connection T.space.bundle := by
  letI := T.space.topology
  refine {
    cov := {
      toFun := fun X => {
        toFun := fun s => ⟨tensorDerivativeValue B A T C K X s,
          tensorDerivativeValue_smooth B A T C K X s⟩
        map_add' := ?_
        map_smul' := ?_ }
      map_add' := ?_
      map_smul' := ?_ }
    linear_field := ?_
    leibniz := ?_ }
  · rename_i X
    intro s t
    apply Subtype.ext
    funext p
    exact tensorDerivativeValue_add B A T C K X s t p
  · rename_i X
    intro c s
    apply Subtype.ext
    funext p
    exact tensorDerivativeValue_smul B A T C K X c s p
  · intro X Y
    apply LinearMap.ext
    intro s
    apply Subtype.ext
    funext p
    exact tensorDerivativeValue_add_field B A T C K X Y s p
  · intro c X
    apply LinearMap.ext
    intro s
    apply Subtype.ext
    funext p
    exact tensorDerivativeValue_smul_field B A T C K c X s p
  · intro f X s
    apply Subtype.ext
    funext p
    exact tensorDerivativeValue_mul_field B A T C K f X s p
  · intro X f s
    apply Subtype.ext
    funext p
    exact tensorDerivativeValue_leibniz B A T C K X f s p

/-- The constructed connection satisfies the product rule on all pure sections. -/
theorem tensorConnection_rule : TensorRule C K T (tensorConnection B A T C K) := by
  letI := T.space.topology
  intro X s u v hv p
  have heq : v = tensorSection B A T s u := Subtype.ext (funext hv)
  subst v
  change tensorDerivativeValue B A T C K X _ p = _
  have hh := tensorDerivativeValue_eq B A T C K X (tensorSection B A T s u) p
    (TensorProduct.tmul ℝ s u) (Filter.Eventually.of_forall (fun _ => rfl))
  simpa only [tensorPresentationDerivative_tmul, pureTensorDerivative,
    ConnectionForms.section_add_apply, tensorSection_apply] using hh

/-- Any connection with the pure-product rule has the formal derivative
on all finite presentations. -/
theorem connection_tensorPresentation :
    letI := T.space.topology
    ∀ (N : Connection T.space.bundle), TensorRule C K T N →
    ∀ (X : Field S) (x : TensorPresentation B A),
      N.cov X (tensorPresentationValue B A T x) = tensorPresentationDerivative B A T C K X x := by
  letI := T.space.topology
  intro N hN X x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s u =>
    apply Subtype.ext
    funext p
    exact hN X s u (tensorSection B A T s u) (fun _ => rfl) p
  | add x y hx hy => simp only [map_add, hx, hy]

theorem tensorConnection_unique :
    letI := T.space.topology
    ∀ (N : Connection T.space.bundle), TensorRule C K T N → N = tensorConnection B A T C K := by
  letI := T.space.topology
  intro N hN
  have heq : N.cov = (tensorConnection B A T C K).cov := by
    apply LinearMap.ext
    intro X
    apply LinearMap.ext
    intro s
    apply Subtype.ext
    funext p
    obtain ⟨x, hx⟩ := exists_tensorPresentation B A T s p
    rw [ConnectionForms.locality_section T.space.bundle N X s
      (tensorPresentationValue B A T x) p (hx.mono (fun _ h => h.symm)),
      connection_tensorPresentation B A T C K N hN]
    exact (tensorDerivativeValue_eq B A T C K X s p x hx).symm
  cases N
  cases h : tensorConnection B A T C K
  simp only [h] at heq
  congr 1

theorem tensor_exists_unique :
    P202Specs.Geometry.InducedConnections.tensor_exists_uniqueType.{u,v,t,w,z} := by
  intro n r k a M _ S ι κ E F _ _ _ _ _ _ B A C K T
  letI := T.space.topology
  exact ⟨tensorConnection B A T C K, tensorConnection_rule B A T C K,
    fun N hN => tensorConnection_unique B A T C K N hN⟩

end TensorConnection

/-- Contraction on a dual pair for any connection satisfying the induced rule. -/
theorem dual_rule_contraction : P202Specs.Geometry.InducedConnections.dual_contractionType.{u,v,w} := by
  intro n r a M _ S ι E _ _ _ B C D
  letI := D.space.topology
  intro K hK X lam s p
  have h := hK X lam s p
  linarith

section TensorPairing
variable {n r k : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {κ : Type t}
  {E : M → Type w} {F : M → Type z}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [∀ p, AddCommGroup (F p)] [∀ p, Module ℝ (F p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean k) F)]
  (B : SmoothVectorBundle S r ι E) (A : SmoothVectorBundle S k κ F)
  (T : TensorBundle B A) (D : DualBundle B) (H : DualBundle A)
set_option quotPrecheck false in
local notation "TensorSection" => (letI := T.space.topology; Section T.space.bundle)
set_option quotPrecheck false in
local notation "BDualSection" => (letI := D.space.topology; Section D.space.bundle)
set_option quotPrecheck false in
local notation "ADualSection" => (letI := H.space.topology; Section H.space.bundle)

/-- Evaluation of any smooth tensor section on smooth dual test sections is
smooth, using a finite presentation only locally. -/
theorem tensorPairing_smooth (s : TensorSection) (lam : BDualSection) (mu : ADualSection) (p : M) :
    VectorSmoothAt S.smoothStructure.val
      (fun q => tensorEvaluation (lam.val q) (mu.val q) (s.val q)) p := by
  obtain ⟨x, hx⟩ := exists_tensorPresentation B A T s p
  have h := (SmoothManifolds.scalarContDiffAt_iff _ _ _ _).mp
    ((SmoothManifolds.mem_globalSmoothAlgebra_iff S _).mp
      (tensorPresentationPairing B A D H lam mu x).property p)
  apply VectorSmoothAt.congr h
  filter_upwards [hx] with q hq
  rw [tensorPresentationPairing_apply B A T D H, hq]

noncomputable def tensorPairing (s : TensorSection) (lam : BDualSection) (mu : ADualSection) :
    GlobalSmooth S :=
  ⟨fun q => tensorEvaluation (lam.val q) (mu.val q) (s.val q),
    (SmoothManifolds.mem_globalSmoothAlgebra_iff S _).mpr
      (fun p => (SmoothManifolds.scalarContDiffAt_iff _ _ _ _).mpr
        (tensorPairing_smooth B A T D H s lam mu p))⟩

/-- The full evaluation product rule on arbitrary tensor sections. This
extends the pure-product calculation through all local balanced relations. -/
theorem tensorPairing_derivative (C : Connection B) (K : Connection A) (X : Field S)
    (s : TensorSection) (lam : BDualSection) (mu : ADualSection) (p : M) :
    (act S X (tensorPairing B A T D H s lam mu)).val p =
      tensorEvaluation ((dualSection B D C X lam).val p) (mu.val p) (s.val p) +
      tensorEvaluation (lam.val p) ((dualSection A H K X mu).val p) (s.val p) +
      tensorEvaluation (lam.val p) (mu.val p) (tensorDerivativeValue B A T C K X s p) := by
  obtain ⟨x, hx⟩ := exists_tensorPresentation B A T s p
  have he : (tensorPairing B A T D H s lam mu).val =ᶠ[𝓝 p]
      (tensorPresentationPairing B A D H lam mu x).val := by
    filter_upwards [hx] with q hq
    change tensorEvaluation (lam.val q) (mu.val q) (s.val q) = _
    rw [tensorPresentationPairing_apply B A T D H, hq]
  rw [ConnectionForms.act_congr X _ _ p he,
    tensorDerivativeValue_eq B A T C K X s p x hx,
    tensorPresentationDerivative_pairing B A T D H C K X lam mu x p,
    hx.self_of_nhds]
  ring

end TensorPairing

section EvaluationContraction
variable {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E) (D : DualBundle B)

@[simp] theorem evaluationContraction_tmul {V : Type*} [AddCommGroup V] [Module ℝ V]
    (lam : Module.Dual ℝ V) (v : V) :
    evaluationContraction (TensorProduct.tmul ℝ lam v) = lam v := rfl

/-- Finite presentations contract to genuinely smooth scalar functions. -/
noncomputable def contractionPresentation :
    letI := D.space.topology
    TensorPresentation D.space.bundle B →ₗ[ℝ] GlobalSmooth S := by
  letI := D.space.topology
  exact TensorProduct.lift {
    toFun := pairingLinear B D
    map_add' := fun lam mu => by
      apply LinearMap.ext
      intro s
      exact pairing_add_left B D lam mu s
    map_smul' := fun c lam => by
      apply LinearMap.ext
      intro s
      exact pairing_smul_left B D c lam s }

@[simp] theorem contractionPresentation_tmul :
    letI := D.space.topology
    ∀ (lam : Section D.space.bundle) (s : Section B),
    contractionPresentation B D (TensorProduct.tmul ℝ lam s) = pairing B D lam s := by
  letI := D.space.topology
  intro lam s
  rfl

theorem contractionPresentation_apply :
    letI := D.space.topology
    ∀ (T : TensorBundle D.space.bundle B),
    letI := T.space.topology
    ∀ (x : TensorPresentation D.space.bundle B) (p : M),
    (contractionPresentation B D x).val p =
      evaluationContraction ((tensorPresentationValue D.space.bundle B T x).val p) := by
  letI := D.space.topology
  intro T
  letI := T.space.topology
  intro x p
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul lam s => rfl
  | add x y hx hy =>
    simp only [map_add, Subalgebra.coe_add, Pi.add_apply, Submodule.coe_add, hx, hy]

/-- Natural evaluation is smooth for arbitrary tensor sections, by local
finite presentations rather than a global finite generation assumption. -/
theorem evaluation_contraction_smooth :
    letI := D.space.topology
    ∀ (T : TensorBundle D.space.bundle B),
    letI := T.space.topology
    ∀ (s : Section T.space.bundle) (p : M),
    VectorSmoothAt S.smoothStructure.val (fun q => evaluationContraction (s.val q)) p := by
  letI := D.space.topology
  intro T
  letI := T.space.topology
  intro s p
  obtain ⟨x, hx⟩ := exists_tensorPresentation D.space.bundle B T s p
  have h := (SmoothManifolds.scalarContDiffAt_iff _ _ _ _).mp
    ((SmoothManifolds.mem_globalSmoothAlgebra_iff S _).mp
      (contractionPresentation B D x).property p)
  apply VectorSmoothAt.congr h
  filter_upwards [hx] with q hq
  rw [contractionPresentation_apply B D T, hq]

/-- Contraction as a smooth scalar-valued linear map on all tensor sections. -/
noncomputable def contractionSection :
    letI := D.space.topology
    ∀ (T : TensorBundle D.space.bundle B),
    letI := T.space.topology
    Section T.space.bundle →ₗ[ℝ] GlobalSmooth S := by
  letI := D.space.topology
  intro T
  letI := T.space.topology
  exact {
    toFun := fun s => ⟨fun p => evaluationContraction (s.val p),
      (SmoothManifolds.mem_globalSmoothAlgebra_iff S _).mpr
        (fun p => (SmoothManifolds.scalarContDiffAt_iff _ _ _ _).mpr
          (evaluation_contraction_smooth B D T s p))⟩
    map_add' := fun s t => by
      apply Subtype.ext
      funext p
      exact map_add evaluationContraction _ _
    map_smul' := fun c s => by
      apply Subtype.ext
      funext p
      exact map_smul evaluationContraction c _ }

/-- The dual-pair derivative extends by linearity to every presentation. -/
theorem contractionPresentation_derivative (C : Connection B) :
    letI := D.space.topology
    ∀ (K : Connection D.space.bundle), DualRule C D K →
    ∀ (T : TensorBundle D.space.bundle B),
    letI := T.space.topology
    ∀ (X : Field S) (x : TensorPresentation D.space.bundle B) (p : M),
    (act S X (contractionPresentation B D x)).val p =
      evaluationContraction ((tensorPresentationDerivative D.space.bundle B T K C X x).val p) := by
  letI := D.space.topology
  intro K hK T
  letI := T.space.topology
  intro X x p
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul lam s =>
    have hh := hK X lam s p
    change (K.cov X lam).val p (s.val p) =
      scalarDerivative S (pairing B D lam s).val p (X.val p) - _ at hh
    rw [ConnectionForms.scalarDerivative_global] at hh
    change _ = evaluationContraction
      (TensorProduct.tmul ℝ ((K.cov X lam).val p) (s.val p) +
        TensorProduct.tmul ℝ (lam.val p) ((C.cov X s).val p))
    rw [map_add, evaluationContraction_tmul, evaluationContraction_tmul]
    change (act S X (pairing B D lam s)).val p = _
    linarith
  | add x y hx hy =>
    simp only [map_add, Subalgebra.coe_add, Pi.add_apply, Submodule.coe_add, hx, hy]

/-- Contraction commutes with the induced connection on every smooth section
of the actual tensor bundle E* ⊗ E. -/
theorem evaluation_contraction_derivative (C : Connection B) :
    letI := D.space.topology
    ∀ (K : Connection D.space.bundle), DualRule C D K →
    ∀ (T : TensorBundle D.space.bundle B),
    letI := T.space.topology
    ∀ (N : Connection T.space.bundle), TensorRule K C T N →
    ∀ (X : Field S) (s : Section T.space.bundle) (p : M),
    scalarDerivative S (fun q => evaluationContraction (s.val q)) p (X.val p) =
      evaluationContraction ((N.cov X s).val p) := by
  letI := D.space.topology
  intro K hK T
  letI := T.space.topology
  intro N hN X s p
  obtain ⟨x, hx⟩ := exists_tensorPresentation D.space.bundle B T s p
  have he : (contractionSection B D T s).val =ᶠ[𝓝 p]
      (contractionPresentation B D x).val := by
    filter_upwards [hx] with q hq
    change evaluationContraction (s.val q) = _
    rw [contractionPresentation_apply B D T, hq]
  change scalarDerivative S (contractionSection B D T s).val p (X.val p) = _
  rw [ConnectionForms.scalarDerivative_global,
    ConnectionForms.act_congr X _ _ p he,
    contractionPresentation_derivative B D C K hK T X x p]
  rw [ConnectionForms.locality_section T.space.bundle N X s
    (tensorPresentationValue D.space.bundle B T x) p (hx.mono (fun _ h => h.symm)),
    connection_tensorPresentation D.space.bundle B T K C N hN]

end EvaluationContraction

section DualNaturality
variable {n m r : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {T : SmoothManifold m b N}
  {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E) (F : N → M) (hF : IsSmoothMap T S F)
  (P : PullbackBundle B T F)

/-- In the actual common fiber, a pulled-back local frame has the original values. -/
theorem pullback_trivialization_symm (i : ι) (q : N) (hq : F q ∈ B.baseSet i)
    (v : Euclidean r) :
    letI := P.space.topology
    (P.space.bundle.trivialization i).symm q v = (B.trivialization i).symm (F q) v := by
  letI := P.space.topology
  have hp : q ∈ P.space.bundle.baseSet i := by rw [P.baseSet]; exact hq
  change (P.space.bundle.fiberCoordinates i q hp).symm v =
    (B.fiberCoordinates i (F q) hq).symm v
  have he : P.space.bundle.fiberCoordinates i q hp = B.fiberCoordinates i (F q) hq := by
    apply LinearEquiv.ext
    intro x
    exact P.coordinates i q hq x
  rw [he]


variable (D : DualBundle B)

/-- The identity on actual dual fibers identifies the pullback of the dual
with the dual of the pullback, including the prescribed smooth coordinates. -/
noncomputable def pullbackDualBundle
    (Q : letI := D.space.topology; PullbackBundle D.space.bundle T F) :
    letI := P.space.topology; DualBundle P.space.bundle := by
  letI := P.space.topology
  letI := D.space.topology
  refine { space := Q.space, baseSet := ?_, coordinates := ?_ }
  · intro i
    rw [Q.baseSet, D.baseSet, P.baseSet]
  · intro i q hq lam j
    have hi : F q ∈ B.baseSet i := by simpa only [P.baseSet, Set.mem_preimage] using hq
    rw [Q.coordinates i q (by rw [D.baseSet]; exact hi), D.coordinates i (F q) hi]
    rw [pullback_trivialization_symm B F P i q hi]

/-- The dual connection rule holds at every actual tangent vector. -/
theorem pointDerivative_dual (C : Connection B)
    (lam : letI := D.space.topology; Section D.space.bundle)
    (s : Section B) (p : M) (v : TangentSpace S p) :
    letI := D.space.topology
    (pointDerivative (dualConnection B D C) lam.val p v) (s.val p) =
      scalarDerivative S (fun q => lam.val q (s.val q)) p v -
        lam.val p (pointDerivative C s.val p v) := by
  letI := D.space.topology
  obtain ⟨X, hX⟩ := ConnectionForms.section_evaluation_surjective (tangentBundle S) p v
  rw [← hX, ConnectionForms.pointDerivative_global D.space.bundle,
    ConnectionForms.pointDerivative_global B]
  exact dualConnection_rule B D C X lam s p

/-- Pullback and dualization commute for the actual pullback-dual realization. -/
theorem dualConnection_pullback_isPullback (C : Connection B)
    (Q : letI := D.space.topology; PullbackBundle D.space.bundle T F) :
    letI := D.space.topology
    letI := P.space.topology
    letI := Q.space.topology
    P202.PullbackData.IsPullback D.space.bundle (dualConnection B D C) F hF Q
      (dualConnection P.space.bundle (pullbackDualBundle B F P D Q)
        (PullbackConnections.pullback B F hF P C)) := by
  letI := D.space.topology
  letI := P.space.topology
  letI := Q.space.topology
  intro X lam t ht q
  have he : t = PullbackConnections.pullSection D.space.bundle F hF Q lam :=
    Subtype.ext (funext ht)
  subst t
  apply LinearMap.ext
  intro x
  obtain ⟨s, hs⟩ := ConnectionForms.section_evaluation_surjective B (F q) x
  rw [← hs, pointDerivative_dual B D C lam s]
  have hd := dualConnection_rule P.space.bundle (pullbackDualBundle B F P D Q)
    (PullbackConnections.pullback B F hF P C) X
    (PullbackConnections.pullSection D.space.bundle F hF Q lam)
    (PullbackConnections.pullSection B F hF P s) q
  change ((dualConnection P.space.bundle (pullbackDualBundle B F P D Q)
      (PullbackConnections.pullback B F hF P C)).cov X
      (PullbackConnections.pullSection D.space.bundle F hF Q lam)).val q
      ((PullbackConnections.pullSection B F hF P s).val q) = _
  rw [hd]
  have hc := PullbackConnections.pullback_isPullback B F hF P C X s
    (PullbackConnections.pullSection B F hF P s) (fun _ => rfl) q
  rw [hc]
  have hh := PullbackConnections.scalar_chain_local F hF
    (fun p => lam.val p (s.val p)) q
    ((SmoothManifolds.scalarContDiffAt_iff _ _ _ _).mpr (pairing_smooth B D lam s (F q)))
    (X.val q)
  exact congrArg (fun y => y - lam.val (F q)
    (pointDerivative C s.val (F q) (SmoothManifolds.differential T S F hF q (X.val q)))) hh

/-- Equality of the two constructed connections, rather than only equality on
pulled-back fields, follows from the unrestricted pullback universal property. -/
theorem dualConnection_pullback (C : Connection B)
    (Q : letI := D.space.topology; PullbackBundle D.space.bundle T F) :
    letI := D.space.topology
    letI := P.space.topology
    letI := Q.space.topology
    dualConnection P.space.bundle (pullbackDualBundle B F P D Q)
        (PullbackConnections.pullback B F hF P C) =
      PullbackConnections.pullback D.space.bundle F hF Q (dualConnection B D C) := by
  letI := D.space.topology
  letI := P.space.topology
  letI := Q.space.topology
  exact PullbackConnections.uniqueness D.space.bundle F hF Q (dualConnection B D C)
    _ _ (dualConnection_pullback_isPullback B F hF P D C Q)
    (PullbackConnections.pullback_isPullback D.space.bundle F hF Q (dualConnection B D C))

end DualNaturality

section TensorNaturality
variable {n m r k : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {T : SmoothManifold m b N}
  {ι : Type v} {κ : Type t} {E : M → Type w} {G : M → Type z}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [∀ p, AddCommGroup (G p)] [∀ p, Module ℝ (G p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean k) G)]
  (B : SmoothVectorBundle S r ι E) (A : SmoothVectorBundle S k κ G)
  (F : N → M) (P : PullbackBundle B T F) (H : PullbackBundle A T F)
  (U : TensorBundle B A)

/-- On the actual tensor-product fibers, the pullback of a tensor bundle is
the tensor bundle of the two pullbacks, with exactly the pulled-back topology
and prescribed smooth trivializations. -/
noncomputable def pullbackTensorBundle
    (Q : letI := U.space.topology; PullbackBundle U.space.bundle T F) :
    letI := P.space.topology
    letI := H.space.topology
    TensorBundle P.space.bundle H.space.bundle := by
  letI := P.space.topology
  letI := H.space.topology
  letI := U.space.topology
  refine { space := Q.space, baseSet := ?_, coordinates := ?_ }
  · intro i
    rw [Q.baseSet, U.baseSet, P.baseSet, H.baseSet]
    rfl
  · intro i q hq x y j l
    have hi : F q ∈ U.space.bundle.baseSet i := by simpa only [Q.baseSet, Set.mem_preimage] using hq
    have hiB : F q ∈ B.baseSet i.1 := by rw [U.baseSet] at hi; exact hi.1
    have hiA : F q ∈ A.baseSet i.2 := by rw [U.baseSet] at hi; exact hi.2
    rw [Q.coordinates i q hi, U.coordinates i (F q) hi,
      P.coordinates i.1 q hiB, H.coordinates i.2 q hiA]
end TensorNaturality

section TensorNaturality
variable {n m r k : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {T : SmoothManifold m b N}
  {ι : Type v} {κ : Type t} {E : M → Type w} {G : M → Type z}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [∀ p, AddCommGroup (G p)] [∀ p, Module ℝ (G p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean k) G)]
  (B : SmoothVectorBundle S r ι E) (A : SmoothVectorBundle S k κ G)
  (F : N → M) (P : PullbackBundle B T F) (H : PullbackBundle A T F)
  (U : TensorBundle B A)

variable (hF : IsSmoothMap T S F)

/-- Pullback of smooth sections as a real linear map. -/
noncomputable def pullSectionLinear :
    letI := P.space.topology; Section B →ₗ[ℝ] Section P.space.bundle := by
  letI := P.space.topology
  refine { toFun := PullbackConnections.pullSection B F hF P, map_add' := ?_, map_smul' := ?_ }
  · intro s u
    apply Subtype.ext
    funext q
    rfl
  · intro c s
    apply Subtype.ext
    funext q
    rfl

/-- Pullback on the formal local tensor presentations. -/
noncomputable def pullTensorPresentation :
    letI := P.space.topology
    letI := H.space.topology
    TensorPresentation B A →ₗ[ℝ] TensorPresentation P.space.bundle H.space.bundle := by
  letI := P.space.topology
  letI := H.space.topology
  exact TensorProduct.map (pullSectionLinear B F P hF) (pullSectionLinear A F H hF)

variable (Q : letI := U.space.topology; PullbackBundle U.space.bundle T F)

/-- Pulling back a finite presentation preserves its actual tensor values. -/
theorem pullTensorPresentation_value (x : TensorPresentation B A) (q : N) :
    letI := P.space.topology
    letI := H.space.topology
    letI := U.space.topology
    letI := Q.space.topology
    (tensorPresentationValue P.space.bundle H.space.bundle (pullbackTensorBundle B A F P H U Q)
      (pullTensorPresentation B A F P H hF x)).val q =
      (tensorPresentationValue B A U x).val (F q) := by
  letI := P.space.topology
  letI := H.space.topology
  letI := U.space.topology
  letI := Q.space.topology
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s u => rfl
  | add x y hx hy => simp only [map_add, ConnectionForms.section_add_apply, hx, hy]

/-- The presentation derivative commutes with pullback in the actual tangent
direction dF(X), even when that direction has no global related field. -/
theorem pullTensorPresentation_derivative (C : Connection B) (K : Connection A)
    (X : Field T) (Y : Field S) (q : N)
    (hY : Y.val (F q) = SmoothManifolds.differential T S F hF q (X.val q))
    (x : TensorPresentation B A) :
    letI := P.space.topology
    letI := H.space.topology
    letI := U.space.topology
    letI := Q.space.topology
    (tensorPresentationDerivative P.space.bundle H.space.bundle (pullbackTensorBundle B A F P H U Q)
      (PullbackConnections.pullback B F hF P C) (PullbackConnections.pullback A F hF H K) X
      (pullTensorPresentation B A F P H hF x)).val q =
      (tensorPresentationDerivative B A U C K Y x).val (F q) := by
  letI := P.space.topology
  letI := H.space.topology
  letI := U.space.topology
  letI := Q.space.topology
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s u =>
    have hc := PullbackConnections.pullback_isPullback B F hF P C X s
      (PullbackConnections.pullSection B F hF P s) (fun _ => rfl) q
    have hk := PullbackConnections.pullback_isPullback A F hF H K X u
      (PullbackConnections.pullSection A F hF H u) (fun _ => rfl) q
    rw [← hY, ConnectionForms.pointDerivative_global B C] at hc
    rw [← hY, ConnectionForms.pointDerivative_global A K] at hk
    change (pureTensorDerivative P.space.bundle H.space.bundle (pullbackTensorBundle B A F P H U Q)
      (PullbackConnections.pullback B F hF P C) (PullbackConnections.pullback A F hF H K) X
      (PullbackConnections.pullSection B F hF P s) (PullbackConnections.pullSection A F hF H u)).val q =
      (pureTensorDerivative B A U C K Y s u).val (F q)
    simp only [pureTensorDerivative, ConnectionForms.section_add_apply, tensorSection_apply,
      PullbackConnections.pullSection_apply, hc, hk]
  | add x y hx hy => simp only [map_add, ConnectionForms.section_add_apply, hx, hy]

/-- Tensor products of pulled-back connections satisfy the original pullback
universal property on every tensor section, using local presentations. -/
theorem tensorConnection_pullback_isPullback (C : Connection B) (K : Connection A) :
    letI := P.space.topology
    letI := H.space.topology
    letI := U.space.topology
    letI := Q.space.topology
    P202.PullbackData.IsPullback U.space.bundle (tensorConnection B A U C K) F hF Q
      (tensorConnection P.space.bundle H.space.bundle (pullbackTensorBundle B A F P H U Q)
        (PullbackConnections.pullback B F hF P C) (PullbackConnections.pullback A F hF H K)) := by
  letI := P.space.topology
  letI := H.space.topology
  letI := U.space.topology
  letI := Q.space.topology
  let UP := pullbackTensorBundle B A F P H U Q
  let CP := PullbackConnections.pullback B F hF P C
  let KP := PullbackConnections.pullback A F hF H K
  let NC := tensorConnection B A U C K
  let NP := tensorConnection P.space.bundle H.space.bundle UP CP KP
  intro X s t ht q
  have he : t = PullbackConnections.pullSection U.space.bundle F hF Q s :=
    Subtype.ext (funext ht)
  subst t
  obtain ⟨x, hx⟩ := exists_tensorPresentation B A U s (F q)
  obtain ⟨Y, hY⟩ := ConnectionForms.section_evaluation_surjective (tangentBundle S)
    (F q) (SmoothManifolds.differential T S F hF q (X.val q))
  have hxp : ∀ᶠ z in 𝓝 q,
      (PullbackConnections.pullSection U.space.bundle F hF Q s).val z =
        (tensorPresentationValue P.space.bundle H.space.bundle UP
          (pullTensorPresentation B A F P H hF x)).val z := by
    filter_upwards [(hF q).1.tendsto.eventually hx] with z hz
    rw [pullTensorPresentation_value B A F P H U hF Q]
    exact hz.symm
  change (NP.cov X (PullbackConnections.pullSection U.space.bundle F hF Q s)).val q =
    pointDerivative NC s.val (F q) (SmoothManifolds.differential T S F hF q (X.val q))
  erw [ConnectionForms.locality_section Q.space.bundle NP X _ _ q hxp,
    connection_tensorPresentation P.space.bundle H.space.bundle UP CP KP NP
      (tensorConnection_rule P.space.bundle H.space.bundle UP CP KP),
    pullTensorPresentation_derivative B A F P H U hF Q C K X Y q hY,
    ← hY, ConnectionForms.pointDerivative_global U.space.bundle NC,
    ConnectionForms.locality_section U.space.bundle NC Y s _ (F q) (hx.mono (fun _ h => h.symm)),
    connection_tensorPresentation B A U C K NC (tensorConnection_rule B A U C K)]

/-- Pullback commutes with the induced tensor connection, as equality of the
constructed connections on their actual common bundle. -/
theorem tensorConnection_pullback (C : Connection B) (K : Connection A) :
    letI := P.space.topology
    letI := H.space.topology
    letI := U.space.topology
    letI := Q.space.topology
    tensorConnection P.space.bundle H.space.bundle (pullbackTensorBundle B A F P H U Q)
        (PullbackConnections.pullback B F hF P C) (PullbackConnections.pullback A F hF H K) =
      PullbackConnections.pullback U.space.bundle F hF Q (tensorConnection B A U C K) := by
  letI := P.space.topology
  letI := H.space.topology
  letI := U.space.topology
  letI := Q.space.topology
  exact PullbackConnections.uniqueness U.space.bundle F hF Q (tensorConnection B A U C K)
    _ _ (tensorConnection_pullback_isPullback B A F P H U hF Q C K)
    (PullbackConnections.pullback_isPullback U.space.bundle F hF Q (tensorConnection B A U C K))

end TensorNaturality

section TensorLinearMap
universe l h
variable {n r k d : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {κ : Type t} {δ : Type l}
  {E : M → Type w} {F : M → Type z} {G : M → Type h}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [∀ p, AddCommGroup (F p)] [∀ p, Module ℝ (F p)]
  [∀ p, AddCommGroup (G p)] [∀ p, Module ℝ (G p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean k) F)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean d) G)]
  (B : SmoothVectorBundle S r ι E) (A : SmoothVectorBundle S k κ F)
  (J : SmoothVectorBundle S d δ G)
  (L : (p : M) → TensorProduct ℝ (E p) (F p) →ₗ[ℝ] G p)
  (hL : ∀ (s : Section B) (u : Section A),
    SmoothSection J (fun p => L p (TensorProduct.tmul ℝ (s.val p) (u.val p))))

/-- A fiberwise linear operation, first evaluated on pure smooth sections. -/
def pureImageSection (s : Section B) (u : Section A) : Section J :=
  ⟨fun p => L p (TensorProduct.tmul ℝ (s.val p) (u.val p)), hL s u⟩

noncomputable def tensorImagePresentation : TensorPresentation B A →ₗ[ℝ] Section J :=
  TensorProduct.lift {
    toFun := fun s => {
      toFun := pureImageSection B A J L hL s
      map_add' := fun u v => by
        apply Subtype.ext
        funext p
        exact (congrArg (L p) (TensorProduct.tmul_add _ _ _)).trans (map_add _ _ _)
      map_smul' := fun c u => by
        apply Subtype.ext
        funext p
        exact (congrArg (L p) (TensorProduct.tmul_smul _ _ _)).trans (map_smul _ _ _) }
    map_add' := fun s t => by
      apply LinearMap.ext
      intro u
      apply Subtype.ext
      funext p
      exact (congrArg (L p) (TensorProduct.add_tmul _ _ _)).trans (map_add _ _ _)
    map_smul' := fun c s => by
      apply LinearMap.ext
      intro u
      apply Subtype.ext
      funext p
      change L p (TensorProduct.tmul ℝ (c • s.val p) (u.val p)) =
        c • L p (TensorProduct.tmul ℝ (s.val p) (u.val p))
      change L p (c • TensorProduct.tmul ℝ (s.val p) (u.val p)) = _
      exact map_smul (L p) c _ }

@[simp] theorem tensorImagePresentation_tmul (s : Section B) (u : Section A) :
    tensorImagePresentation B A J L hL (TensorProduct.tmul ℝ s u) =
      pureImageSection B A J L hL s u := rfl

theorem tensorImagePresentation_apply (T : TensorBundle B A)
    (x : TensorPresentation B A) (p : M) :
    (tensorImagePresentation B A J L hL x).val p =
      L p ((tensorPresentationValue B A T x).val p) := by
  letI := T.space.topology
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s u => rfl
  | add x y hx hy => simp only [map_add, Submodule.coe_add, Pi.add_apply, hx, hy]

include hL in
/-- Smoothness of a linear tensor operation can be checked on pure sections. -/
theorem tensorLinearMap_smooth (T : TensorBundle B A) :
    letI := T.space.topology
    ∀ s : Section T.space.bundle, SmoothSection J (fun p => L p (s.val p)) := by
  letI := T.space.topology
  intro s p
  obtain ⟨x, hx⟩ := exists_tensorPresentation B A T s p
  apply SmoothManifolds.SectionExtension.section_smoothAt_congr J
    ((tensorImagePresentation B A J L hL x).property p)
  filter_upwards [hx] with q hq
  rw [tensorImagePresentation_apply B A J L hL T, hq]

noncomputable def tensorLinearMapSection (T : TensorBundle B A) :
    letI := T.space.topology
    Section T.space.bundle →ₗ[ℝ] Section J := by
  letI := T.space.topology
  exact {
    toFun := fun s => ⟨fun p => L p (s.val p), tensorLinearMap_smooth B A J L hL T s⟩
    map_add' := fun s t => by
      apply Subtype.ext
      funext p
      exact map_add _ _ _
    map_smul' := fun c s => by
      apply Subtype.ext
      funext p
      exact map_smul (L p) c _ }

/-- A pure-section test suffices for a fiberwise linear operation to commute
with induced differentiation on every smooth tensor section. -/
theorem tensorLinearMap_parallel (C : Connection B) (K : Connection A) (H : Connection J)
    (hH : ∀ (X : Field S) (s : Section B) (u : Section A),
      H.cov X (pureImageSection B A J L hL s u) =
        pureImageSection B A J L hL (C.cov X s) u +
          pureImageSection B A J L hL s (K.cov X u))
    (T : TensorBundle B A) :
    letI := T.space.topology
    ∀ (N : Connection T.space.bundle), TensorRule C K T N →
    ∀ (X : Field S) (s : Section T.space.bundle),
    H.cov X (tensorLinearMapSection B A J L hL T s) =
      tensorLinearMapSection B A J L hL T (N.cov X s) := by
  letI := T.space.topology
  intro N hN X s
  have hp : ∀ x : TensorPresentation B A,
      H.cov X (tensorImagePresentation B A J L hL x) =
        tensorLinearMapSection B A J L hL T (tensorPresentationDerivative B A T C K X x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v w =>
      rw [tensorImagePresentation_tmul, hH]
      apply Subtype.ext
      funext p
      exact (map_add (L p) _ _).symm
    | add x y hx hy => simp only [map_add, hx, hy]
  apply Subtype.ext
  funext p
  obtain ⟨x, hx⟩ := exists_tensorPresentation B A T s p
  have he : ∀ᶠ q in 𝓝 p,
      (tensorLinearMapSection B A J L hL T s).val q =
        (tensorImagePresentation B A J L hL x).val q := by
    filter_upwards [hx] with q hq
    change L q (s.val q) = _
    rw [tensorImagePresentation_apply B A J L hL T, hq]
  rw [ConnectionForms.locality_section J H X _ _ p he, hp]
  change L p _ = L p _
  rw [ConnectionForms.locality_section T.space.bundle N X s
    (tensorPresentationValue B A T x) p (hx.mono (fun _ h => h.symm)),
    connection_tensorPresentation B A T C K N hN]

end TensorLinearMap


theorem dual_pullback_compatibility :
    P202Specs.Geometry.InducedConnections.dual_pullback_compatibilityType.{u,v,w} := by
  intro n m r a b M N _ _ S T ι E _ _ _ B C D F hF P
  letI := D.space.topology
  intro Q
  letI := P.space.topology
  letI := Q.space.topology
  intro CP CD CQ hCP hCD hCQ
  have heCP := PullbackConnections.uniqueness B F hF P C CP
    (PullbackConnections.pullback B F hF P C) hCP (PullbackConnections.pullback_isPullback B F hF P C)
  have heCD := dualConnection_unique B D C CD hCD
  have heCQ := PullbackConnections.uniqueness D.space.bundle F hF Q (dualConnection B D C) CQ
    (PullbackConnections.pullback D.space.bundle F hF Q (dualConnection B D C))
    (by simpa only [heCD] using hCQ)
    (PullbackConnections.pullback_isPullback D.space.bundle F hF Q (dualConnection B D C))
  refine ⟨⟨pullbackDualBundle B F P D Q, rfl⟩, ?_⟩
  intro X lam s q
  rw [heCP, heCQ, ← dualConnection_pullback B F hF P D C Q]
  exact dualConnection_rule P.space.bundle (pullbackDualBundle B F P D Q)
    (PullbackConnections.pullback B F hF P C) X lam s q

theorem tensor_pullback_compatibility :
    P202Specs.Geometry.InducedConnections.tensor_pullback_compatibilityType.{u,v,t,w,z} := by
  intro n m r k a b M N _ _ S T ι κ E G _ _ _ _ _ _ B A C K U F hF P H
  letI := U.space.topology
  intro Q
  letI := P.space.topology
  letI := H.space.topology
  letI := Q.space.topology
  intro CP KP CU CQ hCP hKP hCU hCQ
  have heCP := PullbackConnections.uniqueness B F hF P C CP
    (PullbackConnections.pullback B F hF P C) hCP (PullbackConnections.pullback_isPullback B F hF P C)
  have heKP := PullbackConnections.uniqueness A F hF H K KP
    (PullbackConnections.pullback A F hF H K) hKP (PullbackConnections.pullback_isPullback A F hF H K)
  have heCU := tensorConnection_unique B A U C K CU hCU
  have heCQ := PullbackConnections.uniqueness U.space.bundle F hF Q (tensorConnection B A U C K) CQ
    (PullbackConnections.pullback U.space.bundle F hF Q (tensorConnection B A U C K))
    (by simpa only [heCU] using hCQ)
    (PullbackConnections.pullback_isPullback U.space.bundle F hF Q (tensorConnection B A U C K))
  refine ⟨⟨pullbackTensorBundle B A F P H U Q, rfl⟩, ?_⟩
  intro X s u v hv q
  rw [heCP, heKP, heCQ, ← tensorConnection_pullback B A F P H U hF Q C K]
  exact tensorConnection_rule P.space.bundle H.space.bundle (pullbackTensorBundle B A F P H U Q)
    (PullbackConnections.pullback B F hF P C) (PullbackConnections.pullback A F hF H K)
    X s u v hv q

section TensorFlip
variable {n r k : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {κ : Type t}
  {E : M → Type w} {F : M → Type z}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [∀ p, AddCommGroup (F p)] [∀ p, Module ℝ (F p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean k) F)]
  (B : SmoothVectorBundle S r ι E) (A : SmoothVectorBundle S k κ F)
  (T : TensorBundle B A) (U : TensorBundle A B)

theorem tensorFlip_pure_smooth (s : Section B) (u : Section A) :
    letI := U.space.topology
    SmoothSection U.space.bundle (fun p =>
      (TensorProduct.comm ℝ (E p) (F p)) (TensorProduct.tmul ℝ (s.val p) (u.val p))) := by
  letI := U.space.topology
  exact tensorSection_smooth A B U u s

/-- Permutation of two factors is smooth on every actual tensor section. -/
theorem tensorFlip_smooth :
    letI := T.space.topology
    letI := U.space.topology
    ∀ s : Section T.space.bundle,
    SmoothSection U.space.bundle (fun p => (TensorProduct.comm ℝ (E p) (F p)) (s.val p)) := by
  letI := T.space.topology
  letI := U.space.topology
  exact tensorLinearMap_smooth B A U.space.bundle
    (fun p => (TensorProduct.comm ℝ (E p) (F p)).toLinearMap) (tensorFlip_pure_smooth B A U) T

/-- The canonical factor permutation commutes with induced differentiation. -/
theorem tensorFlip_derivative (C : Connection B) (K : Connection A) :
    letI := T.space.topology
    letI := U.space.topology
    ∀ (N : Connection T.space.bundle) (H : Connection U.space.bundle),
    TensorRule C K T N → TensorRule K C U H →
    ∀ (X : Field S) (s : Section T.space.bundle) (u : Section U.space.bundle),
    (∀ p, u.val p = (TensorProduct.comm ℝ (E p) (F p)) (s.val p)) →
    ∀ p, (H.cov X u).val p =
      (TensorProduct.comm ℝ (E p) (F p)) ((N.cov X s).val p) := by
  letI := T.space.topology
  letI := U.space.topology
  intro N H hN hH X s u hu p
  let L := fun p => (TensorProduct.comm ℝ (E p) (F p)).toLinearMap
  let hL := tensorFlip_pure_smooth B A U
  have hpar : ∀ (Y : Field S) (v : Section B) (w : Section A),
      H.cov Y (pureImageSection B A U.space.bundle L hL v w) =
        pureImageSection B A U.space.bundle L hL (C.cov Y v) w +
          pureImageSection B A U.space.bundle L hL v (K.cov Y w) := by
    intro Y v w
    apply Subtype.ext
    funext q
    change (H.cov Y (tensorSection A B U w v)).val q = _
    rw [hH Y w v (tensorSection A B U w v) (fun _ => rfl) q]
    exact add_comm _ _
  have hh := tensorLinearMap_parallel B A U.space.bundle L hL C K H hpar T N hN X s
  have he : u = tensorLinearMapSection B A U.space.bundle L hL T s :=
    Subtype.ext (funext hu)
  rw [he]
  exact congrArg (fun z : Section U.space.bundle => z.val p) hh

end TensorFlip

end P202.Geometry.InducedConnections

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace P202.Geometry.InducedConnections
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
 SmoothManifolds.TangentData SmoothManifolds.BundleData SmoothManifolds.FrameData
 SmoothManifolds.BundleOperationsData SmoothManifolds.SectionExtensionData P202.ConnectionData
 P202.InducedConnectionData
open Set Filter
open scoped Topology
universe u v w
section Flat
variable {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
 {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
 [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
 [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
 (B : SmoothVectorBundle S r ι E) (b : LocalFrame B Set.univ isOpen_univ)
@[simp] theorem frameCoefficient_add (s t : Section B) (j : Fin r) :
 frameCoefficient b (s + t) j = frameCoefficient b s j + frameCoefficient b t j := by
 apply Subtype.ext
 funext p
 exact congrFun ((b.basis ⟨p, mem_univ p⟩).equivFun.map_add (s.val p) (t.val p)) j
@[simp] theorem frameCoefficient_smul (c : ℝ) (s : Section B) (j : Fin r) :
 frameCoefficient b (c • s) j = c • frameCoefficient b s j := by
 apply Subtype.ext
 funext p
 exact congrFun ((b.basis ⟨p, mem_univ p⟩).equivFun.map_smul c (s.val p)) j
@[simp] theorem frameCoefficient_mul (f : GlobalSmooth S) (s : Section B) (j : Fin r) :
 frameCoefficient b (mulSection f s) j = f * frameCoefficient b s j := by
 apply Subtype.ext
 funext p
 exact congrFun ((b.basis ⟨p, mem_univ p⟩).equivFun.map_smul (f.val p) (s.val p)) j
noncomputable def flatDerivative (X : Field S) (s : Section B) : Section B :=
 ∑ j, mulSection (act S X (frameCoefficient b s j)) (frameMember b j)
@[simp] theorem flatDerivative_apply (X : Field S) (s : Section B) (p : M) :
 (flatDerivative B b X s).val p =
 ∑ j, (act S X (frameCoefficient b s j)).val p • (frameMember b j).val p := by
 simp [flatDerivative, ConnectionForms.mulSection_apply]
noncomputable def flatConnection : Connection B where
 cov := {
  toFun := fun X => {
   toFun := flatDerivative B b X
   map_add' := by
    intro s t
    apply Subtype.ext
    funext p
    simp [flatDerivative_apply, frameCoefficient_add, map_add, add_smul, Finset.sum_add_distrib]
   map_smul' := by
    intro c s
    apply Subtype.ext
    funext p
    simp [flatDerivative_apply, frameCoefficient_smul, map_smul, Finset.smul_sum, smul_smul] }
  map_add' := by
   intro X Y
   apply LinearMap.ext
   intro s
   apply Subtype.ext
   funext p
   simp [flatDerivative_apply, act_add_field, add_smul, Finset.sum_add_distrib]
  map_smul' := by
   intro c X
   apply LinearMap.ext
   intro s
   apply Subtype.ext
   funext p
   simp [flatDerivative_apply, act_smul_field, Finset.smul_sum, smul_smul] }
 linear_field := by
  intro f X s
  apply Subtype.ext
  funext p
  simp [flatDerivative_apply, act_mul_field, ConnectionForms.mulSection_apply,
   Finset.smul_sum, smul_smul]
 leibniz := by
  intro X f s
  apply Subtype.ext
  funext p
  change (flatDerivative B b X (mulSection f s)).val p =
   (act S X f).val p • s.val p + f.val p • (flatDerivative B b X s).val p
  have hex := congrArg (fun z : Section B => z.val p)
    (ConnectionCalculus.frame_expansion B b s)
  simp only [Submodule.coe_sum, Finset.sum_apply, ConnectionForms.mulSection_apply] at hex
  simp only [flatDerivative_apply, frameCoefficient_mul, Derivation.leibniz,
    Subalgebra.coe_add, Pi.add_apply, Subalgebra.coe_smul, Pi.smul_apply, smul_eq_mul,
    add_smul, mul_smul, Finset.sum_add_distrib]
  simp only [ConnectionForms.section_add_apply, ConnectionForms.mulSection_apply,
    flatDerivative_apply, Finset.smul_sum]
  rw [hex]
  simp only [Finset.smul_sum, smul_smul]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm]
  rfl
theorem flatConnection_coefficient (X : Field S) (s : Section B) (p : M) (i : Fin r) :
 (frameCoefficient b ((flatConnection B b).cov X s) i).val p =
   (act S X (frameCoefficient b s i)).val p := by
 change (b.basis ⟨p, mem_univ p⟩).equivFun ((flatDerivative B b X s).val p) i = _
 rw [flatDerivative_apply]
 simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
   ConnectionForms.frameMember_apply, ← b.basis_eq, Module.Basis.equivFun_self]
 simp
end Flat
section Mixed
variable {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
 {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
 [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
 [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
 (B : SmoothVectorBundle S r ι E)
theorem mixedUnitTrivialization_coordinates :
 letI := (mixedUnitBundle B).space.topology
 ∀ p v j, (mixedUnitTrivialization B).coordinates p v j =
   exteriorPower.zeroEquiv ℝ (E p) v := by
 letI := (mixedUnitBundle B).space.topology
 exact Classical.choose_spec
   (SmoothManifolds.BundleOperations.exterior_zero B (mixedUnitBundle B))
theorem mixedUnitFrame_section :
 letI := (mixedUnitBundle B).space.topology
 ∀ p j, (mixedUnitFrame B).section_ j ⟨p, mem_univ p⟩ =
   ((mixedUnitTrivialization B).coordinates p).symm (Pi.single j 1) := by
 letI := (mixedUnitBundle B).space.topology
 exact Classical.choose_spec (SmoothManifolds.Frames.trivialization_globalFrame
   (mixedUnitBundle B).space.bundle (mixedUnitTrivialization B))
theorem mixedUnitFrame_basis :
 letI := (mixedUnitBundle B).space.topology
 ∀ p, (mixedUnitFrame B).basis ⟨p, mem_univ p⟩ =
   (Pi.basisFun ℝ (Fin (r.choose 0))).map ((mixedUnitTrivialization B).coordinates p).symm := by
 letI := (mixedUnitBundle B).space.topology
 intro p
 apply DFunLike.ext
 intro j
 rw [(mixedUnitFrame B).basis_eq, mixedUnitFrame_section]
 simp only [Module.Basis.map_apply, Pi.basisFun_apply]
theorem mixedUnit_coefficient :
 letI := (mixedUnitBundle B).space.topology
 ∀ (s : Section (mixedUnitBundle B).space.bundle) j p,
   (frameCoefficient (mixedUnitFrame B) s j).val p =
     exteriorPower.zeroEquiv ℝ (E p) (s.val p) := by
 letI := (mixedUnitBundle B).space.topology
 intro s j p
 change ((mixedUnitFrame B).basis ⟨p, mem_univ p⟩).equivFun (s.val p) j = _
 rw [mixedUnitFrame_basis, Module.Basis.map_equivFun]
 simp only [LinearEquiv.symm_symm, LinearEquiv.trans_apply, Pi.basisFun_equivFun,
   LinearEquiv.refl_apply]
 exact mixedUnitTrivialization_coordinates B p (s.val p) j
noncomputable def mixedUnitConnection :
 letI := (mixedBundle B []).topology
 Connection (mixedBundle B []).bundle := by
 letI := (mixedUnitBundle B).space.topology
 exact flatConnection (mixedUnitBundle B).space.bundle (mixedUnitFrame B)
theorem mixedUnitConnection_rule : MixedUnitRule B (mixedUnitConnection B) := by
 letI := (mixedUnitBundle B).space.topology
 intro X s p
 let j : Fin (r.choose 0) := ⟨0, by simp⟩
 have hc := flatConnection_coefficient (mixedUnitBundle B).space.bundle
   (mixedUnitFrame B) X s p j
 rw [mixedUnit_coefficient] at hc
 change _ = (act S X (frameCoefficient (mixedUnitFrame B) s j)).val p at hc
 change exteriorPower.zeroEquiv ℝ (E p)
   (((flatConnection (mixedUnitBundle B).space.bundle (mixedUnitFrame B)).cov X s).val p) = _
 rw [hc]
 exact (ConnectionForms.scalarDerivative_representative
   (fun q => exteriorPower.zeroEquiv ℝ (E q) (s.val q))
   (frameCoefficient (mixedUnitFrame B) s j) p
   (Filter.Eventually.of_forall (fun q => mixedUnit_coefficient B s j q)) (X.val p)).symm
/-- The canonical constant unit of the degree-zero tensor bundle. -/
noncomputable def mixedUnitGenerator :
 letI := (mixedUnitBundle B).space.topology
 Section (mixedUnitBundle B).space.bundle := by
 letI := (mixedUnitBundle B).space.topology
 exact frameMember (mixedUnitFrame B) ⟨0, by simp⟩
theorem mixedUnitGenerator_apply :
 letI := (mixedUnitBundle B).space.topology
 ∀ p, (mixedUnitGenerator B).val p = (exteriorPower.zeroEquiv ℝ (E p)).symm 1 := by
 letI := (mixedUnitBundle B).space.topology
 intro p
 apply (exteriorPower.zeroEquiv ℝ (E p)).injective
 rw [LinearEquiv.apply_symm_apply]
 let j : Fin (r.choose 0) := ⟨0, by simp⟩
 rw [← mixedUnit_coefficient B (mixedUnitGenerator B) j p]
 change ((mixedUnitFrame B).basis ⟨p, mem_univ p⟩).equivFun
   ((mixedUnitFrame B).section_ j ⟨p, mem_univ p⟩) j = 1
 rw [← (mixedUnitFrame B).basis_eq]
 simp
/-- A scalar is a smooth section of the actual zero-degree bundle. -/
noncomputable def mixedScalarSection (f : GlobalSmooth S) :
 letI := (mixedUnitBundle B).space.topology
 Section (mixedUnitBundle B).space.bundle := by
 letI := (mixedUnitBundle B).space.topology
 exact mulSection f (mixedUnitGenerator B)
theorem mixedScalarSection_apply (f : GlobalSmooth S) :
 letI := (mixedUnitBundle B).space.topology
 ∀ p, (mixedScalarSection B f).val p =
   (exteriorPower.zeroEquiv ℝ (E p)).symm (f.val p) := by
 letI := (mixedUnitBundle B).space.topology
 intro p
 change f.val p • (mixedUnitGenerator B).val p = _
 rw [mixedUnitGenerator_apply, ← map_smul]
 simp
theorem mixedScalarSection_derivative (X : Field S) (f : GlobalSmooth S) :
 letI := (mixedUnitBundle B).space.topology
 letI := (mixedBundle B []).topology
 (mixedUnitConnection B).cov X (mixedScalarSection B f) =
   mixedScalarSection B (act S X f) := by
 letI := (mixedUnitBundle B).space.topology
 letI := (mixedBundle B []).topology
 apply Subtype.ext
 funext p
 apply (exteriorPower.zeroEquiv ℝ (E p)).injective
 have h := mixedUnitConnection_rule B X (mixedScalarSection B f) p
 change exteriorPower.zeroEquiv ℝ (E p)
   (((mixedUnitConnection B).cov X (mixedScalarSection B f)).val p) = _ at h
 rw [h, mixedScalarSection_apply, LinearEquiv.apply_symm_apply]
 apply ConnectionForms.scalarDerivative_representative
 filter_upwards [] with q
 rw [mixedScalarSection_apply, LinearEquiv.apply_symm_apply]

noncomputable def mixedConnection (C : Connection B) :
 (l : List Bool) → letI := (mixedBundle B l).topology; Connection (mixedBundle B l).bundle
 | [] => mixedUnitConnection B
 | false :: l => by
   letI := (mixedBundle B l).topology
   exact tensorConnection B (mixedBundle B l).bundle (mixedPrimalStep B l) C
     (mixedConnection C l)
 | true :: l => by
   letI := (mixedDualBundle B).space.topology
   letI := (mixedBundle B l).topology
   exact tensorConnection (mixedDualBundle B).space.bundle (mixedBundle B l).bundle
     (mixedDualStep B l) (dualConnection B (mixedDualBundle B) C) (mixedConnection C l)
theorem mixedConnection_rule (C : Connection B) :
 letI := (mixedDualBundle B).space.topology
 MixedFamilyRule B C (dualConnection B (mixedDualBundle B) C) (mixedConnection B C) := by
 letI := (mixedDualBundle B).space.topology
 refine ⟨dualConnection_rule B (mixedDualBundle B) C, mixedUnitConnection_rule B, ?_, ?_⟩
 · intro l
   letI := (mixedBundle B l).topology
   exact tensorConnection_rule B (mixedBundle B l).bundle (mixedPrimalStep B l) C
     (mixedConnection B C l)
 · intro l
   letI := (mixedBundle B l).topology
   exact tensorConnection_rule (mixedDualBundle B).space.bundle (mixedBundle B l).bundle
     (mixedDualStep B l) (dualConnection B (mixedDualBundle B) C) (mixedConnection B C l)
theorem mixedRank_eq (l : List Bool) : mixedRank r l = r ^ l.length := by
 induction l with
 | nil => simp [mixedRank]
 | cons b l ih => simp [mixedRank, ih, pow_succ, mul_comm]
/-- All positive-degree mixed fibers of a rank-zero bundle vanish. -/
theorem mixedFiber_zero {S : SmoothManifold n a M}
 {E : M → Type w} [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
 [TopologicalSpace (Bundle.TotalSpace (Euclidean 0) E)]
 (B : SmoothVectorBundle S 0 ι E) (b : Bool) (l : List Bool) (p : M)
 (x : MixedFiber E (b :: l) p) : x = 0 := by
 letI := (mixedBundle B (b :: l)).topology
 exact (SmoothManifolds.BundleOperations.zero_of_rank_eq_zero
   (mixedBundle B (b :: l)).bundle (by simp [mixedRank])).1 p x
end Mixed
/-- Simultaneous construction on all finite ordered primal/dual tensor words. -/
theorem mixed_exists : P202Specs.Geometry.InducedConnections.mixed_existsType.{u,v,w} := by
 intro n r a M _ S ι E _ _ _ B C
 letI := (mixedDualBundle B).space.topology
 exact ⟨dualConnection B (mixedDualBundle B) C, mixedConnection B C, mixedConnection_rule B C⟩
end P202.Geometry.InducedConnections

namespace P202.Geometry.InducedConnections
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
 SmoothManifolds.TangentData SmoothManifolds.BundleData SmoothManifolds.FrameData
 SmoothManifolds.BundleOperationsData SmoothManifolds.SectionExtensionData P202.ConnectionData
 P202.InducedConnectionData
open Set Filter
open scoped Topology
universe u v w z t
section SpectatorContraction
variable {n r k : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {κ : Type t}
  {E : M → Type w} {F : M → Type z}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [∀ p, AddCommGroup (F p)] [∀ p, Module ℝ (F p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean k) F)]
  (B : SmoothVectorBundle S r ι E) (D : DualBundle B)
  (A : SmoothVectorBundle S k κ F)

@[simp] theorem spectatorContraction_tmul {V W : Type*}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (v : TensorProduct ℝ (Module.Dual ℝ V) V) (w : W) :
    spectatorContraction (TensorProduct.tmul ℝ v w) = evaluationContraction v • w := rfl

theorem spectatorContraction_pure_smooth :
    letI := D.space.topology
    ∀ (V : TensorBundle D.space.bundle B),
    letI := V.space.topology
    ∀ (s : Section V.space.bundle) (u : Section A),
    SmoothSection A (fun p => spectatorContraction (TensorProduct.tmul ℝ (s.val p) (u.val p))) := by
  letI := D.space.topology
  intro V
  letI := V.space.topology
  intro s u
  exact (mulSection (contractionSection B D V s) u).property

/-- Contraction of a dual pair retains an arbitrary tensor spectator smoothly. -/
theorem spectatorContraction_smooth :
    letI := D.space.topology
    ∀ (V : TensorBundle D.space.bundle B),
    letI := V.space.topology
    ∀ (T : TensorBundle V.space.bundle A),
    letI := T.space.topology
    ∀ s : Section T.space.bundle, SmoothSection A (fun p => spectatorContraction (s.val p)) := by
  letI := D.space.topology
  intro V
  letI := V.space.topology
  intro T
  letI := T.space.topology
  exact tensorLinearMap_smooth V.space.bundle A A (fun _ => spectatorContraction)
    (spectatorContraction_pure_smooth B D A V) T

/-- An adjacent dual-pair contraction with an arbitrary spectator commutes
with the induced connection on every section, beyond pure tensors. -/
theorem spectatorContraction_derivative (C : Connection B) (K : Connection A) :
    letI := D.space.topology
    ∀ (CD : Connection D.space.bundle), DualRule C D CD →
    ∀ (V : TensorBundle D.space.bundle B),
    letI := V.space.topology
    ∀ (CV : Connection V.space.bundle), TensorRule CD C V CV →
    ∀ (T : TensorBundle V.space.bundle A),
    letI := T.space.topology
    ∀ (CT : Connection T.space.bundle), TensorRule CV K T CT →
    ∀ (X : Field S) (s : Section T.space.bundle) (u : Section A),
    (∀ p, u.val p = spectatorContraction (s.val p)) →
    ∀ p, (K.cov X u).val p = spectatorContraction ((CT.cov X s).val p) := by
  letI := D.space.topology
  intro CD hCD V
  letI := V.space.topology
  intro CV hCV T
  letI := T.space.topology
  intro CT hCT X s u hu p
  let hL := spectatorContraction_pure_smooth B D A V
  have hp : ∀ (Y : Field S) (v : Section V.space.bundle) (w : Section A),
      K.cov Y (pureImageSection V.space.bundle A A (fun _ => spectatorContraction) hL v w) =
        pureImageSection V.space.bundle A A (fun _ => spectatorContraction) hL (CV.cov Y v) w +
          pureImageSection V.space.bundle A A (fun _ => spectatorContraction) hL v (K.cov Y w) := by
    intro Y v w
    change K.cov Y (mulSection (contractionSection B D V v) w) = _
    rw [K.leibniz]
    apply Subtype.ext
    funext q
    have he := evaluation_contraction_derivative B D C CD hCD V CV hCV Y v q
    change (act S Y (contractionSection B D V v)).val q • w.val q +
        evaluationContraction (v.val q) • (K.cov Y w).val q = _
    rw [← ConnectionForms.scalarDerivative_global (contractionSection B D V v) Y q]
    change scalarDerivative S (fun z => evaluationContraction (v.val z)) q (Y.val q) • w.val q +
        evaluationContraction (v.val q) • (K.cov Y w).val q = _
    rw [he]
    rfl
  have hh := tensorLinearMap_parallel V.space.bundle A A (fun _ => spectatorContraction) hL
    CV K K hp T CT hCT X s
  have he : u = tensorLinearMapSection V.space.bundle A A (fun _ => spectatorContraction) hL T s :=
    Subtype.ext (funext hu)
  rw [he]
  exact congrArg (fun z : Section A => z.val p) hh
end SpectatorContraction

end P202.Geometry.InducedConnections

namespace P202.Geometry.InducedConnections
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
 SmoothManifolds.TangentData SmoothManifolds.BundleData SmoothManifolds.FrameData
 SmoothManifolds.BundleOperationsData SmoothManifolds.SectionExtensionData P202.ConnectionData
 P202.InducedConnectionData
open Set Filter
open scoped Topology
universe u v w z t
open P202.CurveConnectionData

section CurveHelpers
variable {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  {B : SmoothVectorBundle S r ι E}

/-- Covariant differentiation only uses the within germ of a field. -/
theorem curve_derivative_congr (C : Connection B)
    {c : ℝ → M} {f g : (s : ℝ) → E (c s)} {J : Set ℝ} {t : ℝ}
    (ht : t ∈ J) {D : E (c t)}
    (hD : HasCovariantDerivativeWithinAt C c f J t D)
    (hfg : ∀ᶠ s in 𝓝[J] t, f s = g s) :
    HasCovariantDerivativeWithinAt C c g J t D := by
  obtain ⟨V, hV, U, hU, b, hp, v', hv, hEq⟩ := hD
  have hcoef : coefficientsAlong b c g =ᶠ[𝓝[J] t] coefficientsAlong b c f := by
    filter_upwards [hfg] with s hs
    simp only [coefficientsAlong, hs]
  refine ⟨V, hV, U, hU, b, hp, v', hv.congr_of_eventuallyEq_of_mem hcoef ht, ?_⟩
  rw [hEq]
  unfold frameDerivative
  rw [hcoef.eq_of_nhdsWithin ht]

theorem curve_derivative_sum (C : Connection B) (X : Field S)
    {c : ℝ → M} {J : Set ℝ} {t : ℝ}
    (ht : t ∈ J) (hJ : UniqueDiffWithinAt ℝ J t)
    (hV : HasVelocityWithinAt S c J t (X.val (c t)))
    {α : Type*} (I : Finset α) (f : α → (s : ℝ) → E (c s))
    (D : α → E (c t))
    (hD : ∀ i ∈ I, HasCovariantDerivativeWithinAt C c (f i) J t (D i)) :
    HasCovariantDerivativeWithinAt C c (fun s => ∑ i ∈ I, f i s) J t (∑ i ∈ I, D i) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty, map_zero, ConnectionForms.section_zero_apply] using
      CurveCovariantDerivative.derivative_section_field C (0 : Section B) X ht hV
  | @insert i I hi ih =>
    simp only [Finset.mem_insert, forall_eq_or_imp] at hD
    simpa only [Finset.sum_insert hi] using
      CurveCovariantDerivative.derivative_add C ht hJ hD.1 (ih hD.2)

/-- Any differentiable field has a finite local expansion in global smooth
sections with parameter-differentiable scalar coefficients. No extension of
that field or of the curve into the manifold is assumed. -/
theorem curve_derivative_representation (C : Connection B) (X : Field S)
    {c : ℝ → M} {f : (s : ℝ) → E (c s)} {J : Set ℝ} {t : ℝ}
    (ht : t ∈ J) (hJ : UniqueDiffWithinAt ℝ J t)
    (hV : HasVelocityWithinAt S c J t (X.val (c t)))
    {D : E (c t)} (hD : HasCovariantDerivativeWithinAt C c f J t D) :
    ∃ (a : Fin r → ℝ → ℝ) (a' : Fin r → ℝ) (e : Fin r → Section B),
      (∀ i, HasDerivWithinAt (a i) (a' i) J t) ∧
      (∀ᶠ s in 𝓝[J] t, f s = ∑ i, a i s • (e i).val (c s)) ∧
      D = ∑ i, (a' i • (e i).val (c t) + a i t • (C.cov X (e i)).val (c t)) := by
  classical
  obtain ⟨V, hV', U, hU, b, hp, v', hv, hEq⟩ := hD
  obtain ⟨e, he⟩ := ConnectionForms.local_frame_representative B b ⟨c t, hp⟩
  let a (i : Fin r) (s : ℝ) := coefficientsAlong b c f s i
  have ha : ∀ i, HasDerivWithinAt (a i) (v' i) J t := hasDerivWithinAt_pi.mp hv
  have hf : ∀ᶠ s in 𝓝[J] t, f s = ∑ i, a i s • (e i).val (c s) := by
    filter_upwards [hV.1.eventually (hU.mem_nhds hp),
      hV.1 (Filter.eventually_all.mpr he)] with s hs heq
    conv_lhs => rw [← (b.basis ⟨c s, hs⟩).sum_equivFun (f s)]
    apply Finset.sum_congr rfl
    intro i _
    rw [heq i, SmoothManifolds.SectionExtension.totalSection_of_mem _ (c s) hs]
    change _ = coefficientsAlong b c f s i • b.section_ i ⟨c s, hs⟩
    rw [CurveCovariantDerivative.coefficientsAlong_of_mem b c f s hs]
    exact congrArg (_ • ·) (b.basis_eq ⟨c s, hs⟩ i)
  refine ⟨a, v', e, ha, hf, ?_⟩
  have hsum := curve_derivative_sum C X ht hJ hV Finset.univ
    (fun i s => a i s • (e i).val (c s))
    (fun i => v' i • (e i).val (c t) + a i t • (C.cov X (e i)).val (c t))
    (fun i _ => CurveCovariantDerivative.derivative_smul C
      (CurveCovariantDerivative.derivative_section_field C (e i) X ht hV) (ha i))
  exact CurveCovariantDerivative.covariantDerivative_unique C ht hJ
    ⟨V, hV', U, hU, b, hp, v', hv, hEq⟩
    (curve_derivative_congr C ht hsum (hf.mono (fun _ h => h.symm)))

end CurveHelpers

section CurveDual
variable {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E)

/-- The dual contraction rule for arbitrary differentiable fields along a
curve, with within derivatives including one-sided parameter germs. -/
theorem curve_dual_contraction (C : Connection B) (D : DualBundle B) :
    letI := D.space.topology
    ∀ (K : Connection D.space.bundle), DualRule C D K →
    ∀ {c : ℝ → M} {lam : (s : ℝ) → Module.Dual ℝ (E (c s))}
      {f : (s : ℝ) → E (c s)} {J : Set ℝ} {t : ℝ}
      (ht : t ∈ J) (hJ : UniqueDiffWithinAt ℝ J t)
      {DL : Module.Dual ℝ (E (c t))} {DF : E (c t)},
      HasCovariantDerivativeWithinAt K c lam J t DL →
      HasCovariantDerivativeWithinAt C c f J t DF →
      HasDerivWithinAt (fun s => lam s (f s)) (DL (f t) + lam t DF) J t := by
  letI := D.space.topology
  intro K hK c lam f J t ht hJ DL DF hL hF
  classical
  have hFcopy := hF
  obtain ⟨V, hV, _⟩ := hFcopy
  obtain ⟨X, hX⟩ := ConnectionForms.section_evaluation_surjective (tangentBundle S) (c t) V
  have hVX : HasVelocityWithinAt S c J t (X.val (c t)) := by rwa [hX]
  obtain ⟨a, a', e, ha, hf, hDF⟩ := curve_derivative_representation C X ht hJ hVX hF
  obtain ⟨b, b', l, hb, hl, hDL⟩ := curve_derivative_representation K X ht hJ hVX hL
  have hpair : (fun s => lam s (f s)) =ᶠ[𝓝[J] t]
      (fun s => ∑ i, ∑ j,
        b i s * a j s * (l i).val (c s) ((e j).val (c s))) := by
    filter_upwards [hf, hl] with s hfs hls
    rw [hfs, hls]
    simp only [LinearMap.sum_apply, map_sum, LinearMap.smul_apply, map_smul,
      smul_eq_mul, Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hscalar (i j : Fin r) :
      HasDerivWithinAt (fun s => (l i).val (c s) ((e j).val (c s)))
        ((K.cov X (l i)).val (c t) ((e j).val (c t)) +
          (l i).val (c t) ((C.cov X (e j)).val (c t))) J t := by
    have hs := CurveCovariantDerivative.scalar_chain hVX
      (fun p => (l i).val p ((e j).val p)) (pairing_smooth B D (l i) (e j) (c t))
    have hh := hK X (l i) (e j) (c t)
    have heq : scalarDerivative S (fun p => (l i).val p ((e j).val p)) (c t) (X.val (c t)) =
        (K.cov X (l i)).val (c t) ((e j).val (c t)) +
          (l i).val (c t) ((C.cov X (e j)).val (c t)) := by linarith only [hh]
    rw [heq] at hs
    exact hs
  have hd := HasDerivWithinAt.fun_sum (u := Finset.univ) (fun i _ =>
    HasDerivWithinAt.fun_sum (u := Finset.univ) (fun j _ =>
      ((hb i).mul (ha j)).mul (hscalar i j)))
  convert hd.congr_of_eventuallyEq_of_mem hpair ht using 1
  rw [hDL, hDF, hf.self_of_nhdsWithin ht, hl.self_of_nhdsWithin ht]
  simp only [LinearMap.sum_apply, map_sum, LinearMap.smul_apply, map_smul,
    LinearMap.add_apply, map_add, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  simp_rw [← Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Pi.mul_apply]
  ring

/-- Existence from C¹ data yields the contraction rule for the actual chosen
covariant derivative fields, on arbitrary uniquely differentiable germs. -/
theorem curve_dual_contraction_c1 (C : Connection B) (D : DualBundle B) :
    letI := D.space.topology
    ∀ (K : Connection D.space.bundle), DualRule C D K →
    ∀ {c : ℝ → M} {lam : (s : ℝ) → Module.Dual ℝ (E (c s))}
      {f : (s : ℝ) → E (c s)} {J : Set ℝ} {t : ℝ}
      (ht : t ∈ J) (hJ : UniqueDiffWithinAt ℝ J t),
      P202.CurveData.CoordinateC1On S c J → ContinuousOn c J →
      C1FieldOn (B := D.space.bundle) c lam J → C1FieldOn (B := B) c f J →
      HasDerivWithinAt (fun s => lam s (f s))
        ((covariantDerivativeWithin K c lam J t) (f t) +
          lam t (covariantDerivativeWithin C c f J t)) J t := by
  letI := D.space.topology
  intro K hK c lam f J t ht hJ hc hc' hl hf
  exact curve_dual_contraction B C D K hK ht hJ
    (CurveCovariantDerivative.covariantDerivativeWithin_spec K
      (CurveCovariantDerivative.exists_covariantDerivative K ht hc hc' hl))
    (CurveCovariantDerivative.covariantDerivativeWithin_spec C
      (CurveCovariantDerivative.exists_covariantDerivative C ht hc hc' hf))

/-- Ordinary covariant derivatives obey the same contraction rule. -/
theorem curve_dual_contraction_at (C : Connection B) (D : DualBundle B) :
    letI := D.space.topology
    ∀ (K : Connection D.space.bundle), DualRule C D K →
    ∀ {c : ℝ → M} {lam : (s : ℝ) → Module.Dual ℝ (E (c s))}
      {f : (s : ℝ) → E (c s)} {t : ℝ}
      {DL : Module.Dual ℝ (E (c t))} {DF : E (c t)},
      HasCovariantDerivativeAt K c lam t DL →
      HasCovariantDerivativeAt C c f t DF →
      HasDerivAt (fun s => lam s (f s)) (DL (f t) + lam t DF) t := by
  letI := D.space.topology
  intro K hK c lam f t DL DF hL hF
  exact hasDerivWithinAt_univ.mp (curve_dual_contraction B C D K hK
    (Set.mem_univ t) uniqueDiffWithinAt_univ hL hF)

end CurveDual

end P202.Geometry.InducedConnections

namespace P202.Geometry.InducedConnections
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.BundleData SmoothManifolds.FrameData
  SmoothManifolds.BundleOperationsData SmoothManifolds.SectionExtensionData P202.ConnectionData P202.InducedConnectionData
open Set Filter
open scoped Topology
universe u v w z t l h j i
section FiberLinearMap
variable {n r d : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {δ : Type l}
  {E : M → Type w} {G : M → Type h}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [∀ p, AddCommGroup (G p)] [∀ p, Module ℝ (G p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean d) G)]
  (B : SmoothVectorBundle S r ι E) (J : SmoothVectorBundle S d δ G)
  (L : (p : M) → E p →ₗ[ℝ] G p)
  (hL : ∀ s : Section B, SmoothSection J (fun p => L p (s.val p)))

/-- The section map of a fiberwise linear bundle operation preserving smooth sections. -/
def fiberLinearMapSection : Section B →ₗ[ℝ] Section J where
  toFun s := ⟨fun p => L p (s.val p), hL s⟩
  map_add' s t := Subtype.ext (funext (fun p => map_add (L p) _ _))
  map_smul' c s := Subtype.ext (funext (fun p => map_smul (L p) c _))
end FiberLinearMap

section TensorProductMap
variable {n r k d e : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {κ : Type t} {δ : Type l} {η : Type i}
  {E : M → Type w} {F : M → Type z} {G : M → Type h} {V : M → Type j}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [∀ p, AddCommGroup (F p)] [∀ p, Module ℝ (F p)]
  [∀ p, AddCommGroup (G p)] [∀ p, Module ℝ (G p)]
  [∀ p, AddCommGroup (V p)] [∀ p, Module ℝ (V p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean k) F)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean d) G)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean e) V)]
  (B : SmoothVectorBundle S r ι E) (A : SmoothVectorBundle S k κ F)
  (J : SmoothVectorBundle S d δ G) (W : SmoothVectorBundle S e η V)
  (T : TensorBundle B A) (U : TensorBundle J W)
  (L : (p : M) → E p →ₗ[ℝ] G p) (R : (p : M) → F p →ₗ[ℝ] V p)
  (hL : ∀ s : Section B, SmoothSection J (fun p => L p (s.val p)))
  (hR : ∀ s : Section A, SmoothSection W (fun p => R p (s.val p)))

include hL hR in
/-- Tensoring two smooth fiberwise linear operations preserves smooth sections. -/
theorem tensorProductMap_smooth :
    letI := T.space.topology
    letI := U.space.topology
    ∀ s : Section T.space.bundle,
    SmoothSection U.space.bundle (fun p => TensorProduct.map (L p) (R p) (s.val p)) := by
  letI := T.space.topology
  letI := U.space.topology
  apply tensorLinearMap_smooth B A U.space.bundle (fun p => TensorProduct.map (L p) (R p)) _ T
  intro s u
  exact tensorSection_smooth J W U (fiberLinearMapSection B J L hL s)
    (fiberLinearMapSection A W R hR u)

/-- Tensor products preserve parallel fiberwise linear operations. The two
input identities are the ordinary parallel-map property; the target tensor
identity follows from the proved product rule and local presentation descent. -/
theorem tensorProductMap_derivative (C : Connection B) (K : Connection A)
    (H : Connection J) (Q : Connection W)
    (hPL : ∀ (X : Field S) (s : Section B),
      H.cov X (fiberLinearMapSection B J L hL s) = fiberLinearMapSection B J L hL (C.cov X s))
    (hPR : ∀ (X : Field S) (s : Section A),
      Q.cov X (fiberLinearMapSection A W R hR s) = fiberLinearMapSection A W R hR (K.cov X s)) :
    letI := T.space.topology
    letI := U.space.topology
    ∀ (NT : Connection T.space.bundle) (NU : Connection U.space.bundle),
      TensorRule C K T NT → TensorRule H Q U NU →
    ∀ (X : Field S) (s : Section T.space.bundle) (u : Section U.space.bundle),
      (∀ p, u.val p = TensorProduct.map (L p) (R p) (s.val p)) →
      ∀ p, (NU.cov X u).val p = TensorProduct.map (L p) (R p) ((NT.cov X s).val p) := by
  letI := T.space.topology
  letI := U.space.topology
  intro NT NU hNT hNU X s u hu p
  let Z := fun p => TensorProduct.map (L p) (R p)
  have hZ : ∀ (s : Section B) (u : Section A),
      SmoothSection U.space.bundle (fun p => Z p (TensorProduct.tmul ℝ (s.val p) (u.val p))) := by
    intro s u
    exact tensorSection_smooth J W U (fiberLinearMapSection B J L hL s)
      (fiberLinearMapSection A W R hR u)
  have hpar : ∀ (Y : Field S) (v : Section B) (w : Section A),
      NU.cov Y (pureImageSection B A U.space.bundle Z hZ v w) =
        pureImageSection B A U.space.bundle Z hZ (C.cov Y v) w +
          pureImageSection B A U.space.bundle Z hZ v (K.cov Y w) := by
    intro Y v w
    have he : pureImageSection B A U.space.bundle Z hZ v w =
        tensorSection J W U (fiberLinearMapSection B J L hL v) (fiberLinearMapSection A W R hR w) := rfl
    apply Subtype.ext
    funext q
    rw [he, hNU Y (fiberLinearMapSection B J L hL v) (fiberLinearMapSection A W R hR w)
      (tensorSection J W U (fiberLinearMapSection B J L hL v) (fiberLinearMapSection A W R hR w))
      (fun _ => rfl) q, hPL Y v, hPR Y w]
    rfl
  have hh := tensorLinearMap_parallel B A U.space.bundle Z hZ C K NU hpar T NT hNT X s
  have he : u = tensorLinearMapSection B A U.space.bundle Z hZ T s := Subtype.ext (funext hu)
  rw [he]
  exact congrArg (fun z : Section U.space.bundle => z.val p) hh
end TensorProductMap
end P202.Geometry.InducedConnections

namespace P202.Geometry.InducedConnections
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.BundleData SmoothManifolds.FrameData
  SmoothManifolds.BundleOperationsData SmoothManifolds.SectionExtensionData P202.ConnectionData P202.InducedConnectionData
open Set Filter
open scoped Topology
universe u v w z t
section TensorLinearMap
universe l h
variable {n r k d : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {κ : Type t} {δ : Type l}
  {E : M → Type w} {F : M → Type z} {G : M → Type h}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [∀ p, AddCommGroup (F p)] [∀ p, Module ℝ (F p)]
  [∀ p, AddCommGroup (G p)] [∀ p, Module ℝ (G p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean k) F)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean d) G)]
  (B : SmoothVectorBundle S r ι E) (A : SmoothVectorBundle S k κ F)
  (J : SmoothVectorBundle S d δ G)
  (L : (p : M) → TensorProduct ℝ (E p) (F p) →ₗ[ℝ] G p)
  (hL : ∀ (s : Section B) (u : Section A),
    SmoothSection J (fun p => L p (TensorProduct.tmul ℝ (s.val p) (u.val p))))

/-- A local pure-section calculation determines differentiation of a moving
fiberwise linear tensor operation. The correction map may depend on X. -/
theorem tensorLinearMap_derivative (C : Connection B) (K : Connection A) (H : Connection J)
    (T : TensorBundle B A) :
    letI := T.space.topology
    ∀ (N : Connection T.space.bundle), TensorRule C K T N →
    ∀ (X : Field S) (R : (p : M) → TensorProduct ℝ (E p) (F p) →ₗ[ℝ] G p),
    (∀ (s : Section B) (u : Section A) (p : M),
      (H.cov X (pureImageSection B A J L hL s u)).val p =
        L p ((pureTensorDerivative B A T C K X s u).val p) +
          R p (TensorProduct.tmul ℝ (s.val p) (u.val p))) →
    ∀ (s : Section T.space.bundle) (p : M),
    (H.cov X (tensorLinearMapSection B A J L hL T s)).val p =
      L p ((N.cov X s).val p) + R p (s.val p) := by
  letI := T.space.topology
  intro N hN X R hR s p
  have hp : ∀ x : TensorPresentation B A,
      (H.cov X (tensorImagePresentation B A J L hL x)).val p =
        L p ((tensorPresentationDerivative B A T C K X x).val p) +
          R p ((tensorPresentationValue B A T x).val p) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v w => exact hR v w p
    | add x y hx hy =>
      simp only [map_add, ConnectionForms.section_add_apply, hx, hy]
      abel
  obtain ⟨x, hx⟩ := exists_tensorPresentation B A T s p
  have he : ∀ᶠ q in 𝓝 p,
      (tensorLinearMapSection B A J L hL T s).val q =
        (tensorImagePresentation B A J L hL x).val q := by
    filter_upwards [hx] with q hq
    change L q (s.val q) = _
    rw [tensorImagePresentation_apply B A J L hL T, hq]
  rw [ConnectionForms.locality_section J H X _ _ p he, hp,
    ConnectionForms.locality_section T.space.bundle N X s
      (tensorPresentationValue B A T x) p (hx.mono (fun _ h => h.symm)),
    connection_tensorPresentation B A T C K N hN, hx.self_of_nhds]
end TensorLinearMap
end P202.Geometry.InducedConnections

namespace P202.Geometry.InducedConnections
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.BundleData SmoothManifolds.FrameData
  SmoothManifolds.BundleOperationsData SmoothManifolds.SectionExtensionData P202.ConnectionData P202.InducedConnectionData
open Set Filter
open scoped Topology
universe u v w z t l h

noncomputable def tensorAssocRightLinear {V W Z : Type*}
    [AddCommGroup V] [AddCommGroup W] [AddCommGroup Z]
    [Module ℝ V] [Module ℝ W] [Module ℝ Z] (g : Z) :
    TensorProduct ℝ V W →ₗ[ℝ] TensorProduct ℝ V (TensorProduct ℝ W Z) :=
  (TensorProduct.assoc ℝ V W Z).toLinearMap.comp
    ((TensorProduct.mk ℝ (TensorProduct ℝ V W) Z).flip g)

@[simp] theorem tensorAssocRightLinear_tmul {V W Z : Type*}
    [AddCommGroup V] [AddCommGroup W] [AddCommGroup Z]
    [Module ℝ V] [Module ℝ W] [Module ℝ Z] (g : Z) (e : V) (f : W) :
    tensorAssocRightLinear g (TensorProduct.tmul ℝ e f) =
      TensorProduct.tmul ℝ e (TensorProduct.tmul ℝ f g) := rfl

section TensorAssoc
variable {n r k d : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {κ : Type t} {δ : Type l}
  {E : M → Type w} {F : M → Type z} {G : M → Type h}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [∀ p, AddCommGroup (F p)] [∀ p, Module ℝ (F p)]
  [∀ p, AddCommGroup (G p)] [∀ p, Module ℝ (G p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean k) F)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean d) G)]
  (B : SmoothVectorBundle S r ι E) (A : SmoothVectorBundle S k κ F)
  (J : SmoothVectorBundle S d δ G) (AB : TensorBundle B A) (BC : TensorBundle A J)
  (LT : letI := AB.space.topology; TensorBundle AB.space.bundle J)
  (RT : letI := BC.space.topology; TensorBundle B BC.space.bundle)

/-- Inserting a smooth third factor after reassociation is smooth on pure sections. -/
theorem tensorAssoc_insert_pure_smooth (g : Section J) (s : Section B) (u : Section A) :
    letI := BC.space.topology
    letI := RT.space.topology
    SmoothSection RT.space.bundle (fun p => tensorAssocRightLinear (g.val p)
      (TensorProduct.tmul ℝ (s.val p) (u.val p))) := by
  letI := BC.space.topology
  letI := RT.space.topology
  exact tensorSection_smooth B BC.space.bundle RT s (tensorSection A J BC u g)

/-- Partial reassociation is smooth on an arbitrary inner tensor section. -/
theorem tensorAssoc_insert_smooth (g : Section J) :
    letI := AB.space.topology
    letI := BC.space.topology
    letI := RT.space.topology
    ∀ s : Section AB.space.bundle,
    SmoothSection RT.space.bundle (fun p => tensorAssocRightLinear (g.val p) (s.val p)) := by
  letI := AB.space.topology
  letI := BC.space.topology
  letI := RT.space.topology
  exact tensorLinearMap_smooth B A RT.space.bundle
    (fun p => tensorAssocRightLinear (g.val p))
    (tensorAssoc_insert_pure_smooth B A J BC RT g) AB

/-- The canonical associator is smooth on every actual triple-tensor section. -/
theorem tensorAssoc_smooth :
    letI := AB.space.topology
    letI := BC.space.topology
    letI := LT.space.topology
    letI := RT.space.topology
    ∀ s : Section LT.space.bundle,
    SmoothSection RT.space.bundle (fun p => (TensorProduct.assoc ℝ (E p) (F p) (G p)) (s.val p)) := by
  letI := AB.space.topology
  letI := BC.space.topology
  letI := LT.space.topology
  letI := RT.space.topology
  exact tensorLinearMap_smooth AB.space.bundle J RT.space.bundle
    (fun p => (TensorProduct.assoc ℝ (E p) (F p) (G p)).toLinearMap)
    (fun s g => tensorAssoc_insert_smooth B A J AB BC RT g s) LT
/-- Reassociation after inserting a fixed smooth last factor. -/
noncomputable def tensorAssocInsertSection (g : Section J) :
    letI := AB.space.topology
    letI := BC.space.topology
    letI := RT.space.topology
    Section AB.space.bundle →ₗ[ℝ] Section RT.space.bundle := by
  letI := AB.space.topology
  letI := BC.space.topology
  letI := RT.space.topology
  exact tensorLinearMapSection B A RT.space.bundle
    (fun p => tensorAssocRightLinear (g.val p))
    (tensorAssoc_insert_pure_smooth B A J BC RT g) AB

/-- The three-factor product rule descends to an arbitrary section of the
first two factors, by locality of the induced tensor connection. -/
theorem tensorAssoc_insert_derivative (C : Connection B) (K : Connection A) (H : Connection J) :
    letI := AB.space.topology
    letI := BC.space.topology
    letI := RT.space.topology
    ∀ (NAB : Connection AB.space.bundle) (NBC : Connection BC.space.bundle)
      (NR : Connection RT.space.bundle),
      TensorRule C K AB NAB → TensorRule K H BC NBC → TensorRule C NBC RT NR →
    ∀ (X : Field S) (s : Section AB.space.bundle) (g : Section J) (p : M),
      (NR.cov X (tensorAssocInsertSection B A J AB BC RT g s)).val p =
        tensorAssocRightLinear (g.val p) ((NAB.cov X s).val p) +
          tensorAssocRightLinear ((H.cov X g).val p) (s.val p) := by
  letI := AB.space.topology
  letI := BC.space.topology
  letI := RT.space.topology
  intro NAB NBC NR hAB hBC hRT X s g p
  apply tensorLinearMap_derivative B A RT.space.bundle
    (fun q => tensorAssocRightLinear (g.val q))
    (tensorAssoc_insert_pure_smooth B A J BC RT g) C K NR AB NAB hAB X
    (fun q => tensorAssocRightLinear ((H.cov X g).val q)) ?_ s p
  intro e f q
  have he : pureImageSection B A RT.space.bundle
      (fun q => tensorAssocRightLinear (g.val q))
      (tensorAssoc_insert_pure_smooth B A J BC RT g) e f =
      tensorSection B BC.space.bundle RT e (tensorSection A J BC f g) := rfl
  rw [he, hRT X e (tensorSection A J BC f g)
    (tensorSection B BC.space.bundle RT e (tensorSection A J BC f g)) (fun _ => rfl) q,
    hBC X f g (tensorSection A J BC f g) (fun _ => rfl) q]
  simp only [pureTensorDerivative, ConnectionForms.section_add_apply, tensorSection_apply,
    map_add, tensorAssocRightLinear_tmul, TensorProduct.tmul_add]
  abel

/-- The canonical associator commutes with the induced connections for both
parenthesizations, on every smooth triple-tensor section. -/
theorem tensorAssoc_derivative (C : Connection B) (K : Connection A) (H : Connection J) :
    letI := AB.space.topology
    letI := BC.space.topology
    letI := LT.space.topology
    letI := RT.space.topology
    ∀ (NAB : Connection AB.space.bundle) (NBC : Connection BC.space.bundle)
      (NL : Connection LT.space.bundle) (NR : Connection RT.space.bundle),
      TensorRule C K AB NAB → TensorRule K H BC NBC →
      TensorRule NAB H LT NL → TensorRule C NBC RT NR →
    ∀ (X : Field S) (s : Section LT.space.bundle) (u : Section RT.space.bundle),
      (∀ p, u.val p = (TensorProduct.assoc ℝ (E p) (F p) (G p)) (s.val p)) →
      ∀ p, (NR.cov X u).val p =
        (TensorProduct.assoc ℝ (E p) (F p) (G p)) ((NL.cov X s).val p) := by
  letI := AB.space.topology
  letI := BC.space.topology
  letI := LT.space.topology
  letI := RT.space.topology
  intro NAB NBC NL NR hAB hBC hLT hRT X s u hu p
  let L := fun p => (TensorProduct.assoc ℝ (E p) (F p) (G p)).toLinearMap
  let hL := fun (v : Section AB.space.bundle) (g : Section J) =>
    tensorAssoc_insert_smooth B A J AB BC RT g v
  have hpar : ∀ (Y : Field S) (v : Section AB.space.bundle) (g : Section J),
      NR.cov Y (pureImageSection AB.space.bundle J RT.space.bundle L hL v g) =
        pureImageSection AB.space.bundle J RT.space.bundle L hL (NAB.cov Y v) g +
          pureImageSection AB.space.bundle J RT.space.bundle L hL v (H.cov Y g) := by
    intro Y v g
    apply Subtype.ext
    funext q
    exact tensorAssoc_insert_derivative B A J AB BC RT C K H NAB NBC NR hAB hBC hRT Y v g q
  have hh := tensorLinearMap_parallel AB.space.bundle J RT.space.bundle L hL
    NAB H NR hpar LT NL hLT X s
  have he : u = tensorLinearMapSection AB.space.bundle J RT.space.bundle L hL LT s :=
    Subtype.ext (funext hu)
  rw [he]
  exact congrArg (fun z : Section RT.space.bundle => z.val p) hh

/-- The inverse canonical associator is smooth, including arbitrary inner
sections rather than only decomposable three-factor sections. -/
theorem tensorAssoc_symm_smooth :
    letI := AB.space.topology
    letI := BC.space.topology
    letI := LT.space.topology
    letI := RT.space.topology
    ∀ s : Section RT.space.bundle,
    SmoothSection LT.space.bundle (fun p => (TensorProduct.assoc ℝ (E p) (F p) (G p)).symm (s.val p)) := by
  letI := AB.space.topology
  letI := BC.space.topology
  letI := LT.space.topology
  letI := RT.space.topology
  let L := fun (e : Section B) (p : M) =>
    (TensorProduct.assoc ℝ (E p) (F p) (G p)).symm.toLinearMap.comp
      (TensorProduct.mk ℝ (E p) (TensorProduct ℝ (F p) (G p)) (e.val p))
  have hL : ∀ (e : Section B) (f : Section A) (g : Section J),
      SmoothSection LT.space.bundle (fun p => L e p (TensorProduct.tmul ℝ (f.val p) (g.val p))) := by
    intro e f g
    exact tensorSection_smooth AB.space.bundle J LT (tensorSection B A AB e f) g
  have hp : ∀ (e : Section B) (s : Section BC.space.bundle),
      SmoothSection LT.space.bundle (fun p =>
        (TensorProduct.assoc ℝ (E p) (F p) (G p)).symm
          (TensorProduct.tmul ℝ (e.val p) (s.val p))) := by
    intro e s
    exact tensorLinearMap_smooth A J LT.space.bundle (L e) (hL e) BC s
  exact tensorLinearMap_smooth B BC.space.bundle LT.space.bundle
    (fun p => (TensorProduct.assoc ℝ (E p) (F p) (G p)).symm.toLinearMap) hp RT

/-- The inverse associator also intertwines induced differentiation. -/
theorem tensorAssoc_symm_derivative (C : Connection B) (K : Connection A) (H : Connection J) :
    letI := AB.space.topology
    letI := BC.space.topology
    letI := LT.space.topology
    letI := RT.space.topology
    ∀ (NAB : Connection AB.space.bundle) (NBC : Connection BC.space.bundle)
      (NL : Connection LT.space.bundle) (NR : Connection RT.space.bundle),
      TensorRule C K AB NAB → TensorRule K H BC NBC →
      TensorRule NAB H LT NL → TensorRule C NBC RT NR →
    ∀ (X : Field S) (s : Section RT.space.bundle) (u : Section LT.space.bundle),
      (∀ p, u.val p = (TensorProduct.assoc ℝ (E p) (F p) (G p)).symm (s.val p)) →
      ∀ p, (NL.cov X u).val p =
        (TensorProduct.assoc ℝ (E p) (F p) (G p)).symm ((NR.cov X s).val p) := by
  letI := AB.space.topology
  letI := BC.space.topology
  letI := LT.space.topology
  letI := RT.space.topology
  intro NAB NBC NL NR hAB hBC hLT hRT X s u hu p
  have hh := tensorAssoc_derivative B A J AB BC LT RT C K H NAB NBC NL NR hAB hBC hLT hRT
    X u s (fun q => by rw [hu q]; exact ((TensorProduct.assoc ℝ (E q) (F q) (G q)).apply_symm_apply _).symm) p
  apply (TensorProduct.assoc ℝ (E p) (F p) (G p)).injective
  simpa only [LinearEquiv.apply_symm_apply] using hh.symm

end TensorAssoc
end P202.Geometry.InducedConnections

namespace P202.Geometry.InducedConnections
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.BundleData SmoothManifolds.FrameData
  SmoothManifolds.BundleOperationsData SmoothManifolds.SectionExtensionData P202.ConnectionData P202.InducedConnectionData
open Set Filter
open scoped Topology
universe u v w z t

open P202.CurveConnectionData
section ParallelMapCurve
variable {n r k : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {κ : Type t}
  {E : M → Type w} {F : M → Type z}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [∀ p, AddCommGroup (F p)] [∀ p, Module ℝ (F p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean k) F)]
  (B : SmoothVectorBundle S r ι E) (A : SmoothVectorBundle S k κ F)
  (L : (p : M) → E p →ₗ[ℝ] F p)
  (hL : ∀ s : Section B, SmoothSection A (fun p => L p (s.val p)))

/-- A parallel smooth fiber map commutes with genuine C¹ within covariant
derivatives. It requires no smooth extension of the curve or its fields. -/
theorem parallelMap_curve_derivative (C : Connection B) (K : Connection A)
    (hpar : ∀ (X : Field S) (s : Section B),
      K.cov X (fiberLinearMapSection B A L hL s) =
        fiberLinearMapSection B A L hL (C.cov X s))
    {c : ℝ → M} {f : (s : ℝ) → E (c s)} {J : Set ℝ} {t : ℝ}
    (ht : t ∈ J) (hJ : UniqueDiffWithinAt ℝ J t)
    {D : E (c t)} (hD : HasCovariantDerivativeWithinAt C c f J t D) :
    HasCovariantDerivativeWithinAt K c (fun s => L (c s) (f s)) J t (L (c t) D) := by
  classical
  have hDc := hD
  obtain ⟨V, hV, _⟩ := hDc
  obtain ⟨X, hX⟩ := ConnectionForms.section_evaluation_surjective (tangentBundle S) (c t) V
  have hVX : HasVelocityWithinAt S c J t (X.val (c t)) := by rwa [hX]
  obtain ⟨a, a', e, ha, hf, hDF⟩ := curve_derivative_representation C X ht hJ hVX hD
  let g (i : Fin r) := fiberLinearMapSection B A L hL (e i)
  have hg := curve_derivative_sum K X ht hJ hVX Finset.univ
    (fun i s => a i s • (g i).val (c s))
    (fun i => a' i • (g i).val (c t) + a i t • (K.cov X (g i)).val (c t))
    (fun i _ => CurveCovariantDerivative.derivative_smul K
      (CurveCovariantDerivative.derivative_section_field K (g i) X ht hVX) (ha i))
  have hv : L (c t) D = ∑ i, (a' i • (g i).val (c t) +
      a i t • (K.cov X (g i)).val (c t)) := by
    rw [hDF, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_add, map_smul, map_smul]
    change _ = _ + a i t • (K.cov X (fiberLinearMapSection B A L hL (e i))).val (c t)
    rw [hpar]
    rfl
  rw [hv]
  apply curve_derivative_congr K ht hg
  filter_upwards [hf] with s hs
  rw [hs, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (map_smul (L (c s)) (a i s) ((e i).val (c s))).symm

end ParallelMapCurve

end P202.Geometry.InducedConnections

namespace P202.Geometry.InducedConnections
open P202.InducedConnectionData
universe u v w
variable {M : Type u} (E : M → Type w)
 [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
theorem tensorSlotEquiv_pure {b : Bool} {l k : List Bool}
 (h : TensorSlot b l k) (p : M) (v : TensorArguments E l p) :
 tensorSlotEquiv E h p (pureMixedTensor E l p v) =
   TensorProduct.tmul ℝ (tensorSlotArguments E h p v).1
     (pureMixedTensor E k p (tensorSlotArguments E h p v).2) := by
 induction h with
 | here l => cases b <;> rfl
 | @there a l k h ih =>
   cases a <;> cases b
   all_goals
    rcases v with ⟨v, vs⟩
    change (TensorProduct.leftComm ℝ _ _ _)
      (TensorProduct.tmul ℝ v ((tensorSlotEquiv E h p) (pureMixedTensor E l p vs))) = _
    rw [ih, TensorProduct.leftComm_tmul]
    rfl
/-- On pure tensors the selected dual acts on the selected primal vector. -/
theorem tensorContractSlots_pure {l k j : List Bool}
 (hd : TensorSlot true l k) (hp : TensorSlot false k j) (p : M)
 (v : TensorArguments E l p) :
 tensorContractSlots E hd hp p (pureMixedTensor E l p v) =
   DFunLike.coe (F := Module.Dual ℝ (E p)) (tensorSlotArguments E hd p v).1
     (tensorSlotArguments E hp p (tensorSlotArguments E hd p v).2).1 •
   pureMixedTensor E j p
     (tensorSlotArguments E hp p (tensorSlotArguments E hd p v).2).2 := by
 change (TensorProduct.lid ℝ (MixedFiber E j p))
   ((TensorProduct.map evaluationContraction (LinearMap.id : MixedFiber E j p →ₗ[ℝ] MixedFiber E j p))
     ((TensorProduct.assoc ℝ (Module.Dual ℝ (E p)) (E p) (MixedFiber E j p)).symm
       ((TensorProduct.congr (LinearEquiv.refl ℝ (Module.Dual ℝ (E p))) (tensorSlotEquiv E hp p))
         ((tensorSlotEquiv E hd p) (pureMixedTensor E l p v))))) = _
 rw [tensorSlotEquiv_pure, TensorProduct.congr_tmul, LinearEquiv.refl_apply,
   tensorSlotEquiv_pure, TensorProduct.assoc_symm_tmul, TensorProduct.map_tmul,
   evaluationContraction_tmul, LinearMap.id_apply, TensorProduct.lid_tmul]
end P202.Geometry.InducedConnections

namespace P202.Geometry.InducedConnections
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
 SmoothManifolds.TangentData SmoothManifolds.BundleData SmoothManifolds.FrameData
 SmoothManifolds.BundleOperationsData SmoothManifolds.SectionExtensionData P202.ConnectionData
 P202.InducedConnectionData
open Set Filter
open scoped Topology
universe u v w z t l h
noncomputable def tensorLeftCommInsertLinear {V W Z : Type*}
 [AddCommGroup V] [AddCommGroup W] [AddCommGroup Z]
 [Module ℝ V] [Module ℝ W] [Module ℝ Z] (e : V) :
 TensorProduct ℝ W Z →ₗ[ℝ] TensorProduct ℝ W (TensorProduct ℝ V Z) :=
 (TensorProduct.leftComm ℝ V W Z).toLinearMap.comp (TensorProduct.mk ℝ V (TensorProduct ℝ W Z) e)
@[simp] theorem tensorLeftCommInsertLinear_tmul {V W Z : Type*}
 [AddCommGroup V] [AddCommGroup W] [AddCommGroup Z]
 [Module ℝ V] [Module ℝ W] [Module ℝ Z] (e : V) (f : W) (g : Z) :
 tensorLeftCommInsertLinear e (TensorProduct.tmul ℝ f g) =
   TensorProduct.tmul ℝ f (TensorProduct.tmul ℝ e g) := by
 simp [tensorLeftCommInsertLinear]
section LeftComm
variable {n r k d : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
 {S : SmoothManifold n a M} {ι : Type v} {κ : Type t} {δ : Type l}
 {E : M → Type w} {F : M → Type z} {G : M → Type h}
 [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
 [∀ p, AddCommGroup (F p)] [∀ p, Module ℝ (F p)]
 [∀ p, AddCommGroup (G p)] [∀ p, Module ℝ (G p)]
 [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
 [TopologicalSpace (Bundle.TotalSpace (Euclidean k) F)]
 [TopologicalSpace (Bundle.TotalSpace (Euclidean d) G)]
 (B : SmoothVectorBundle S r ι E) (A : SmoothVectorBundle S k κ F)
 (J : SmoothVectorBundle S d δ G) (BC : TensorBundle A J) (AC : TensorBundle B J)
 (LT : letI := BC.space.topology; TensorBundle B BC.space.bundle)
 (RT : letI := AC.space.topology; TensorBundle A AC.space.bundle)
theorem tensorLeftComm_insert_pure_smooth (e : Section B) (f : Section A) (g : Section J) :
 letI := AC.space.topology
 letI := RT.space.topology
 SmoothSection RT.space.bundle (fun p => tensorLeftCommInsertLinear (e.val p)
   (TensorProduct.tmul ℝ (f.val p) (g.val p))) := by
 letI := AC.space.topology
 letI := RT.space.topology
 exact tensorSection_smooth A AC.space.bundle RT f (tensorSection B J AC e g)
theorem tensorLeftComm_insert_smooth (e : Section B) :
 letI := BC.space.topology
 letI := AC.space.topology
 letI := RT.space.topology
 ∀ s : Section BC.space.bundle,
 SmoothSection RT.space.bundle (fun p => tensorLeftCommInsertLinear (e.val p) (s.val p)) := by
 letI := BC.space.topology
 letI := AC.space.topology
 letI := RT.space.topology
 exact tensorLinearMap_smooth A J RT.space.bundle
   (fun p => tensorLeftCommInsertLinear (e.val p))
   (tensorLeftComm_insert_pure_smooth B A J AC RT e) BC
noncomputable def tensorLeftCommInsertSection (e : Section B) :
 letI := BC.space.topology
 letI := AC.space.topology
 letI := RT.space.topology
 Section BC.space.bundle →ₗ[ℝ] Section RT.space.bundle := by
 letI := BC.space.topology
 letI := AC.space.topology
 letI := RT.space.topology
 exact tensorLinearMapSection A J RT.space.bundle
   (fun p => tensorLeftCommInsertLinear (e.val p))
   (tensorLeftComm_insert_pure_smooth B A J AC RT e) BC
theorem tensorLeftComm_smooth :
 letI := BC.space.topology
 letI := AC.space.topology
 letI := LT.space.topology
 letI := RT.space.topology
 ∀ s : Section LT.space.bundle, SmoothSection RT.space.bundle
   (fun p => (TensorProduct.leftComm ℝ (E p) (F p) (G p)) (s.val p)) := by
 letI := BC.space.topology
 letI := AC.space.topology
 letI := LT.space.topology
 letI := RT.space.topology
 exact tensorLinearMap_smooth B BC.space.bundle RT.space.bundle
   (fun p => (TensorProduct.leftComm ℝ (E p) (F p) (G p)).toLinearMap)
   (fun e s => tensorLeftComm_insert_smooth B A J BC AC RT e s) LT
theorem tensorLeftComm_insert_derivative (C : Connection B) (K : Connection A) (H : Connection J) :
 letI := BC.space.topology
 letI := AC.space.topology
 letI := RT.space.topology
 ∀ (NBC : Connection BC.space.bundle) (NAC : Connection AC.space.bundle)
   (NR : Connection RT.space.bundle),
 TensorRule K H BC NBC → TensorRule C H AC NAC → TensorRule K NAC RT NR →
 ∀ (X : Field S) (e : Section B) (s : Section BC.space.bundle) (p : M),
 (NR.cov X (tensorLeftCommInsertSection B A J BC AC RT e s)).val p =
   tensorLeftCommInsertLinear (e.val p) ((NBC.cov X s).val p) +
   tensorLeftCommInsertLinear ((C.cov X e).val p) (s.val p) := by
 letI := BC.space.topology
 letI := AC.space.topology
 letI := RT.space.topology
 intro NBC NAC NR hBC hAC hRT X e s p
 apply tensorLinearMap_derivative A J RT.space.bundle
   (fun q => tensorLeftCommInsertLinear (e.val q))
   (tensorLeftComm_insert_pure_smooth B A J AC RT e) K H NR BC NBC hBC X
   (fun q => tensorLeftCommInsertLinear ((C.cov X e).val q)) ?_ s p
 intro f g q
 have he : pureImageSection A J RT.space.bundle
   (fun q => tensorLeftCommInsertLinear (e.val q))
   (tensorLeftComm_insert_pure_smooth B A J AC RT e) f g =
   tensorSection A AC.space.bundle RT f (tensorSection B J AC e g) := by
   apply Subtype.ext
   funext q
   exact tensorLeftCommInsertLinear_tmul _ _ _
 rw [he, hRT X f (tensorSection B J AC e g)
   (tensorSection A AC.space.bundle RT f (tensorSection B J AC e g)) (fun _ => rfl) q,
   hAC X e g (tensorSection B J AC e g) (fun _ => rfl) q]
 simp only [pureTensorDerivative, ConnectionForms.section_add_apply, tensorSection_apply,
   map_add, tensorLeftCommInsertLinear_tmul, TensorProduct.tmul_add]
 abel
theorem tensorLeftComm_derivative (C : Connection B) (K : Connection A) (H : Connection J) :
 letI := BC.space.topology
 letI := AC.space.topology
 letI := LT.space.topology
 letI := RT.space.topology
 ∀ (NBC : Connection BC.space.bundle) (NAC : Connection AC.space.bundle)
   (NL : Connection LT.space.bundle) (NR : Connection RT.space.bundle),
 TensorRule K H BC NBC → TensorRule C H AC NAC →
 TensorRule C NBC LT NL → TensorRule K NAC RT NR →
 ∀ (X : Field S) (s : Section LT.space.bundle) (u : Section RT.space.bundle),
 (∀ p, u.val p = (TensorProduct.leftComm ℝ (E p) (F p) (G p)) (s.val p)) →
 ∀ p, (NR.cov X u).val p =
   (TensorProduct.leftComm ℝ (E p) (F p) (G p)) ((NL.cov X s).val p) := by
 letI := BC.space.topology
 letI := AC.space.topology
 letI := LT.space.topology
 letI := RT.space.topology
 intro NBC NAC NL NR hBC hAC hLT hRT X s u hu p
 let L := fun p => (TensorProduct.leftComm ℝ (E p) (F p) (G p)).toLinearMap
 let hL := fun (e : Section B) (v : Section BC.space.bundle) =>
   tensorLeftComm_insert_smooth B A J BC AC RT e v
 have hpar : ∀ (Y : Field S) (e : Section B) (v : Section BC.space.bundle),
   NR.cov Y (pureImageSection B BC.space.bundle RT.space.bundle L hL e v) =
     pureImageSection B BC.space.bundle RT.space.bundle L hL (C.cov Y e) v +
       pureImageSection B BC.space.bundle RT.space.bundle L hL e (NBC.cov Y v) := by
   intro Y e v
   apply Subtype.ext
   funext q
   have hd := tensorLeftComm_insert_derivative B A J BC AC RT C K H NBC NAC NR
     hBC hAC hRT Y e v q
   exact hd.trans (add_comm _ _)
 have hh := tensorLinearMap_parallel B BC.space.bundle RT.space.bundle L hL C NBC NR hpar LT NL hLT X s
 have he : u = tensorLinearMapSection B BC.space.bundle RT.space.bundle L hL LT s :=
   Subtype.ext (funext hu)
 rw [he]
 exact congrArg (fun z : Section RT.space.bundle => z.val p) hh
end LeftComm
end P202.Geometry.InducedConnections

namespace P202.Geometry.InducedConnections
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.BundleData SmoothManifolds.FrameData
  SmoothManifolds.BundleOperationsData SmoothManifolds.SectionExtensionData P202.ConnectionData P202.InducedConnectionData
open Set Filter
open scoped Topology
universe u v w z t

open P202.CurveConnectionData
open P202.CurveConnectionData

section CurveTensor
variable {n r k : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {κ : Type t}
  {E : M → Type w} {F : M → Type z}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [∀ p, AddCommGroup (F p)] [∀ p, Module ℝ (F p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean k) F)]
  (B : SmoothVectorBundle S r ι E) (A : SmoothVectorBundle S k κ F)

/-- The tensor product rule holds for arbitrary differentiable fields along a
curve, including within and one-sided differentiation. -/
theorem curve_tensor_product (C : Connection B) (K : Connection A) (T : TensorBundle B A) :
    letI := T.space.topology
    ∀ (N : Connection T.space.bundle), TensorRule C K T N →
    ∀ {c : ℝ → M} {f : (s : ℝ) → E (c s)} {g : (s : ℝ) → F (c s)}
      {J : Set ℝ} {t : ℝ} (ht : t ∈ J) (hJ : UniqueDiffWithinAt ℝ J t)
      {DF : E (c t)} {DG : F (c t)},
      HasCovariantDerivativeWithinAt C c f J t DF →
      HasCovariantDerivativeWithinAt K c g J t DG →
      HasCovariantDerivativeWithinAt N c
        (fun s => TensorProduct.tmul ℝ (f s) (g s)) J t
        (TensorProduct.tmul ℝ DF (g t) + TensorProduct.tmul ℝ (f t) DG) := by
  letI := T.space.topology
  intro N hN c f g J t ht hJ DF DG hF hG
  classical
  have hFcopy := hF
  obtain ⟨V, hV, _⟩ := hFcopy
  obtain ⟨X, hX⟩ := ConnectionForms.section_evaluation_surjective (tangentBundle S) (c t) V
  have hVX : HasVelocityWithinAt S c J t (X.val (c t)) := by rwa [hX]
  obtain ⟨a, a', e, ha, hf, hDF⟩ := curve_derivative_representation C X ht hJ hVX hF
  obtain ⟨b, b', u, hb, hg, hDG⟩ := curve_derivative_representation K X ht hJ hVX hG
  have hsection (i : Fin r) (j : Fin k) :
      HasCovariantDerivativeWithinAt N c
        (fun s => TensorProduct.tmul ℝ ((e i).val (c s)) ((u j).val (c s))) J t
        (TensorProduct.tmul ℝ ((C.cov X (e i)).val (c t)) ((u j).val (c t)) +
          TensorProduct.tmul ℝ ((e i).val (c t)) ((K.cov X (u j)).val (c t))) := by
    have hs := CurveCovariantDerivative.derivative_section_field N
      (tensorSection B A T (e i) (u j)) X ht hVX
    rw [hN X (e i) (u j) (tensorSection B A T (e i) (u j)) (fun _ => rfl) (c t)] at hs
    exact hs
  let derivativeTerm (i : Fin r) (j : Fin k) :=
    (a' i * b j t + a i t * b' j) •
        TensorProduct.tmul ℝ ((e i).val (c t)) ((u j).val (c t)) +
      (a i t * b j t) •
        (TensorProduct.tmul ℝ ((C.cov X (e i)).val (c t)) ((u j).val (c t)) +
          TensorProduct.tmul ℝ ((e i).val (c t)) ((K.cov X (u j)).val (c t)))
  have hterm (i : Fin r) (j : Fin k) :
      HasCovariantDerivativeWithinAt N c
        (fun s => (a i s * b j s) •
          TensorProduct.tmul ℝ ((e i).val (c s)) ((u j).val (c s))) J t
        (derivativeTerm i j) :=
    CurveCovariantDerivative.derivative_smul N (hsection i j) ((ha i).mul (hb j))
  have hsum := curve_derivative_sum N X ht hJ hVX Finset.univ
    (fun i s => ∑ j, (a i s * b j s) •
      TensorProduct.tmul ℝ ((e i).val (c s)) ((u j).val (c s)))
    (fun i => ∑ j, derivativeTerm i j)
    (fun i _ => curve_derivative_sum N X ht hJ hVX Finset.univ
      (fun j s => (a i s * b j s) •
        TensorProduct.tmul ℝ ((e i).val (c s)) ((u j).val (c s)))
      (derivativeTerm i) (fun j _ => hterm i j))
  have hfg : ∀ᶠ s in 𝓝[J] t,
      TensorProduct.tmul ℝ (f s) (g s) = ∑ i, ∑ j, (a i s * b j s) •
        TensorProduct.tmul ℝ ((e i).val (c s)) ((u j).val (c s)) := by
    filter_upwards [hf, hg] with s hfs hgs
    rw [hfs, hgs]
    simp only [TensorProduct.sum_tmul, TensorProduct.tmul_sum, ← TensorProduct.smul_tmul',
      TensorProduct.tmul_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_comm]
  have hresult := curve_derivative_congr N ht hsum (hfg.mono (fun _ h => h.symm))
  convert hresult using 1
  rw [hDF, hDG, hf.self_of_nhdsWithin ht, hg.self_of_nhdsWithin ht]
  simp only [TensorProduct.sum_tmul, TensorProduct.tmul_sum, ← TensorProduct.smul_tmul',
    TensorProduct.tmul_smul, TensorProduct.add_tmul, TensorProduct.tmul_add, Finset.smul_sum, smul_smul,
    derivativeTerm]
  simp_rw [← Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [smul_add, smul_smul, add_smul]
  module

/-- On C¹ input fields the actual chosen covariant derivative has the tensor
product value, including at uniquely differentiable one-sided germs. -/
theorem curve_tensor_product_c1 (C : Connection B) (K : Connection A) (T : TensorBundle B A) :
    letI := T.space.topology
    ∀ (N : Connection T.space.bundle), TensorRule C K T N →
    ∀ {c : ℝ → M} {f : (s : ℝ) → E (c s)} {g : (s : ℝ) → F (c s)}
      {J : Set ℝ} {t : ℝ} (ht : t ∈ J) (hJ : UniqueDiffWithinAt ℝ J t),
      P202.CurveData.CoordinateC1On S c J → ContinuousOn c J →
      C1FieldOn (B := B) c f J → C1FieldOn (B := A) c g J →
      covariantDerivativeWithin N c (fun s => TensorProduct.tmul ℝ (f s) (g s)) J t =
        TensorProduct.tmul ℝ (covariantDerivativeWithin C c f J t) (g t) +
          TensorProduct.tmul ℝ (f t) (covariantDerivativeWithin K c g J t) := by
  letI := T.space.topology
  intro N hN c f g J t ht hJ hc hc' hf hg
  exact CurveCovariantDerivative.covariantDerivativeWithin_eq N ht hJ
    (curve_tensor_product B A C K T N hN ht hJ
      (CurveCovariantDerivative.covariantDerivativeWithin_spec C
        (CurveCovariantDerivative.exists_covariantDerivative C ht hc hc' hf))
      (CurveCovariantDerivative.covariantDerivativeWithin_spec K
        (CurveCovariantDerivative.exists_covariantDerivative K ht hc hc' hg)))

/-- Ordinary covariant differentiation of arbitrary differentiable fields
obeys the same tensor product rule. -/
theorem curve_tensor_product_at (C : Connection B) (K : Connection A) (T : TensorBundle B A) :
    letI := T.space.topology
    ∀ (N : Connection T.space.bundle), TensorRule C K T N →
    ∀ {c : ℝ → M} {f : (s : ℝ) → E (c s)} {g : (s : ℝ) → F (c s)} {t : ℝ}
      {DF : E (c t)} {DG : F (c t)},
      HasCovariantDerivativeAt C c f t DF → HasCovariantDerivativeAt K c g t DG →
      HasCovariantDerivativeAt N c (fun s => TensorProduct.tmul ℝ (f s) (g s)) t
        (TensorProduct.tmul ℝ DF (g t) + TensorProduct.tmul ℝ (f t) DG) := by
  letI := T.space.topology
  intro N hN c f g t DF DG hF hG
  exact curve_tensor_product B A C K T N hN
    (Set.mem_univ t) uniqueDiffWithinAt_univ hF hG

end CurveTensor

end P202.Geometry.InducedConnections

namespace P202.Geometry.InducedConnections
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
 SmoothManifolds.TangentData SmoothManifolds.BundleData SmoothManifolds.FrameData
 SmoothManifolds.BundleOperationsData SmoothManifolds.SectionExtensionData P202.ConnectionData
 P202.InducedConnectionData
universe u v w
variable {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
 {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
 [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
 [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
 (B : SmoothVectorBundle S r ι E)
noncomputable def tensorAtomConnection (C : Connection B) :
 (b : Bool) → letI := (tensorAtomBundle B b).topology; Connection (tensorAtomBundle B b).bundle
 | false => C
 | true => dualConnection B (mixedDualBundle B) C
noncomputable def mixedAtomStepConnection (C : Connection B) (b : Bool) (l : List Bool) :
 letI := (tensorAtomBundle B b).topology
 letI := (mixedBundle B l).topology
 letI := (mixedAtomStep B b l).space.topology
 Connection (mixedAtomStep B b l).space.bundle := by
 cases b
 · exact mixedConnection B C (false :: l)
 · exact mixedConnection B C (true :: l)
theorem mixedAtomStep_rule (C : Connection B) (b : Bool) (l : List Bool) :
 letI := (tensorAtomBundle B b).topology
 letI := (mixedBundle B l).topology
 letI := (mixedAtomStep B b l).space.topology
 TensorRule (tensorAtomConnection B C b) (mixedConnection B C l)
   (mixedAtomStep B b l) (mixedAtomStepConnection B C b l) := by
 cases b
 · letI := (mixedBundle B l).topology
   exact tensorConnection_rule B (mixedBundle B l).bundle (mixedPrimalStep B l) C
     (mixedConnection B C l)
 · letI := (mixedDualBundle B).space.topology
   letI := (mixedBundle B l).topology
   exact tensorConnection_rule (mixedDualBundle B).space.bundle (mixedBundle B l).bundle
     (mixedDualStep B l) (dualConnection B (mixedDualBundle B) C) (mixedConnection B C l)
end P202.Geometry.InducedConnections

namespace P202.Geometry.InducedConnections
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
 SmoothManifolds.TangentData SmoothManifolds.BundleData SmoothManifolds.FrameData
 SmoothManifolds.BundleOperationsData SmoothManifolds.SectionExtensionData P202.ConnectionData
 P202.InducedConnectionData
universe u v w
variable {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
 {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
 [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
 [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
 (B : SmoothVectorBundle S r ι E)
theorem tensorSlot_smooth {b : Bool} {l k : List Bool} (h : TensorSlot b l k) :
 letI := (tensorAtomBundle B b).topology
 letI := (mixedBundle B l).topology
 letI := (mixedBundle B k).topology
 letI := (mixedAtomStep B b k).space.topology
 ∀ s : Section (mixedBundle B l).bundle,
 SmoothSection (mixedAtomStep B b k).space.bundle
   (fun p => tensorSlotEquiv E h p (s.val p)) := by
 induction h with
 | here k =>
   let bb := b
   cases b
   all_goals
    letI := (mixedBundle B k).topology
    letI := (mixedBundle B (bb :: k)).topology
    intro s
    exact s.property
 | @there c l k h ih =>
   let cc := c
   let bb := b
   cases c <;> cases b
   all_goals
    let A := tensorAtomBundle B cc
    let F := tensorAtomBundle B bb
    let K := mixedBundle B k
    let L := mixedBundle B l
    let R := mixedAtomStep B bb k
    let P := mixedAtomStep B cc k
    let T := mixedAtomStep B cc l
    let V := mixedAtomStep B bb (cc :: k)
    letI := A.topology
    letI := F.topology
    letI := K.topology
    letI := L.topology
    letI := R.space.topology
    letI := P.space.topology
    letI := T.space.topology
    letI := (mixedBundle B (cc :: k)).topology
    letI := (mixedBundle B (cc :: l)).topology
    letI := V.space.topology
    let U := Classical.choice (SmoothManifolds.BundleOperations.exists_tensor A.bundle R.space.bundle)
    letI := U.space.topology
    intro s
    have hs := tensorProductMap_smooth A.bundle L.bundle A.bundle R.space.bundle T U
      (fun _ => LinearMap.id) (fun p => (tensorSlotEquiv E h p).toLinearMap)
      (fun v => v.property) ih s
    let u : Section U.space.bundle :=
      ⟨fun p => TensorProduct.map LinearMap.id (tensorSlotEquiv E h p).toLinearMap (s.val p), hs⟩
    have hu := tensorLeftComm_smooth A.bundle F.bundle K.bundle R P U V u
    exact hu
theorem tensorSlot_derivative (C : Connection B) {b : Bool} {l k : List Bool}
 (h : TensorSlot b l k) :
 letI := (tensorAtomBundle B b).topology
 letI := (mixedBundle B l).topology
 letI := (mixedBundle B k).topology
 letI := (mixedAtomStep B b k).space.topology
 ∀ (X : Field S) (s : Section (mixedBundle B l).bundle)
 (u : Section (mixedAtomStep B b k).space.bundle),
 (∀ p, u.val p = tensorSlotEquiv E h p (s.val p)) →
 ∀ p, ((mixedAtomStepConnection B C b k).cov X u).val p =
   tensorSlotEquiv E h p (((mixedConnection B C l).cov X s).val p) := by
 induction h with
 | here k =>
   let bb := b
   cases b
   all_goals
    letI := (mixedBundle B k).topology
    letI := (mixedBundle B (bb :: k)).topology
    intro X s u hu p
    change ∀ p, u.val p = s.val p at hu
    have he : u = s := Subtype.ext (funext hu)
    subst u
    rfl
 | @there c l k h ih =>
   let cc := c
   let bb := b
   cases c <;> cases b
   all_goals
    let A := tensorAtomBundle B cc
    let F := tensorAtomBundle B bb
    let K := mixedBundle B k
    let L := mixedBundle B l
    let R := mixedAtomStep B bb k
    let P := mixedAtomStep B cc k
    let T := mixedAtomStep B cc l
    let V := mixedAtomStep B bb (cc :: k)
    letI := A.topology
    letI := F.topology
    letI := K.topology
    letI := L.topology
    letI := R.space.topology
    letI := P.space.topology
    letI := T.space.topology
    letI := (mixedBundle B (cc :: k)).topology
    letI := (mixedBundle B (cc :: l)).topology
    letI := V.space.topology
    let U := Classical.choice (SmoothManifolds.BundleOperations.exists_tensor A.bundle R.space.bundle)
    letI := U.space.topology
    let CA := tensorAtomConnection B C cc
    let CF := tensorAtomConnection B C bb
    let CK := mixedConnection B C k
    let CL := mixedConnection B C l
    let CR := mixedAtomStepConnection B C bb k
    let CP := mixedAtomStepConnection B C cc k
    let CT := mixedAtomStepConnection B C cc l
    let CV := mixedAtomStepConnection B C bb (cc :: k)
    let CU := tensorConnection A.bundle R.space.bundle U CA CR
    let Rmap := fun p => (tensorSlotEquiv E h p).toLinearMap
    let hR := tensorSlot_smooth B h
    let hL := fun v : Section A.bundle => v.property
    have hPR : ∀ (Y : Field S) (v : Section L.bundle),
      CR.cov Y (fiberLinearMapSection L.bundle R.space.bundle Rmap hR v) =
        fiberLinearMapSection L.bundle R.space.bundle Rmap hR (CL.cov Y v) := by
      intro Y v
      apply Subtype.ext
      funext p
      exact ih Y v (fiberLinearMapSection L.bundle R.space.bundle Rmap hR v) (fun _ => rfl) p
    intro X s out hout p
    have hs := tensorProductMap_smooth A.bundle L.bundle A.bundle R.space.bundle T U
      (fun _ => LinearMap.id) Rmap hL hR s
    let u : Section U.space.bundle :=
      ⟨fun p => TensorProduct.map LinearMap.id (Rmap p) (s.val p), hs⟩
    have hp := tensorProductMap_derivative A.bundle L.bundle A.bundle R.space.bundle T U
      (fun _ => LinearMap.id) Rmap hL hR CA CL CA CR (fun _ _ => rfl) hPR
      CT CU (mixedAtomStep_rule B C cc l)
      (tensorConnection_rule A.bundle R.space.bundle U CA CR) X s u (fun _ => rfl) p
    have hleft : ∀ p, out.val p =
      (TensorProduct.leftComm ℝ (TensorAtom E cc p) (TensorAtom E bb p) (MixedFiber E k p)) (u.val p) :=
      hout
    have hx := tensorLeftComm_derivative A.bundle F.bundle K.bundle R P U V CA CF CK CR CP CU CV
      (mixedAtomStep_rule B C bb k) (mixedAtomStep_rule B C cc k)
      (tensorConnection_rule A.bundle R.space.bundle U CA CR)
      (mixedAtomStep_rule B C bb (cc :: k)) X u out hleft p
    rw [hp] at hx
    exact hx
end P202.Geometry.InducedConnections

namespace P202.Geometry.InducedConnections
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.BundleData SmoothManifolds.FrameData
  SmoothManifolds.BundleOperationsData SmoothManifolds.SectionExtensionData P202.ConnectionData P202.InducedConnectionData
open Set Filter
open scoped Topology
universe u v w z t
section MixedHeadContraction
variable {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E)

theorem tensorContractSlots_head (j : List Bool) (p : M) :
    tensorContractSlots E (.here (false :: j)) (.here j) p =
      spectatorContraction.comp
        (TensorProduct.assoc ℝ (Module.Dual ℝ (E p)) (E p) (MixedFiber E j p)).symm.toLinearMap := by
  apply TensorProduct.ext'
  intro lam x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v w => rfl
  | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, hx, hy]

/-- Contraction at the first dual/primal pair is smooth with any remaining
mixed tensor word, including the scalar unit as that remaining word. -/
theorem mixedHeadContraction_smooth (j : List Bool) :
    letI := (mixedBundle B (true :: false :: j)).topology
    letI := (mixedBundle B j).topology
    ∀ s : Section (mixedBundle B (true :: false :: j)).bundle,
    SmoothSection (mixedBundle B j).bundle
      (fun p => tensorContractSlots E (.here (false :: j)) (.here j) p (s.val p)) := by
  let D := mixedDualBundle B
  letI := D.space.topology
  let J := mixedBundle B j
  letI := J.topology
  let V := Classical.choice (SmoothManifolds.BundleOperations.exists_tensor D.space.bundle B)
  letI := V.space.topology
  let LT := Classical.choice (SmoothManifolds.BundleOperations.exists_tensor V.space.bundle J.bundle)
  letI := LT.space.topology
  let RT := mixedDualStep B (false :: j)
  let BC := mixedPrimalStep B j
  letI := (mixedBundle B (true :: false :: j)).topology
  intro s
  let st : Section LT.space.bundle := ⟨fun p =>
    (TensorProduct.assoc ℝ (Module.Dual ℝ (E p)) (E p) (MixedFiber E j p)).symm (s.val p),
    tensorAssoc_symm_smooth D.space.bundle B J.bundle V BC LT RT s⟩
  have hs := spectatorContraction_smooth B D J.bundle V LT st
  rw [show (fun p => tensorContractSlots E (.here (false :: j)) (.here j) p (s.val p)) =
    (fun p => spectatorContraction
      ((TensorProduct.assoc ℝ (Module.Dual ℝ (E p)) (E p) (MixedFiber E j p)).symm (s.val p))) by
      funext p; rw [tensorContractSlots_head]; rfl]
  exact hs

/-- The first-pair contraction commutes with the constructed mixed connection. -/
theorem mixedHeadContraction_derivative (C : Connection B) (j : List Bool) :
    letI := (mixedBundle B (true :: false :: j)).topology
    letI := (mixedBundle B j).topology
    ∀ (X : Field S) (s : Section (mixedBundle B (true :: false :: j)).bundle)
      (u : Section (mixedBundle B j).bundle),
    (∀ p, u.val p = tensorContractSlots E (.here (false :: j)) (.here j) p (s.val p)) →
    ∀ p, ((mixedConnection B C j).cov X u).val p =
      tensorContractSlots E (.here (false :: j)) (.here j) p
        (((mixedConnection B C (true :: false :: j)).cov X s).val p) := by
  let D := mixedDualBundle B
  letI := D.space.topology
  let J := mixedBundle B j
  letI := J.topology
  let V := Classical.choice (SmoothManifolds.BundleOperations.exists_tensor D.space.bundle B)
  letI := V.space.topology
  let LT := Classical.choice (SmoothManifolds.BundleOperations.exists_tensor V.space.bundle J.bundle)
  letI := LT.space.topology
  let RT := mixedDualStep B (false :: j)
  let BC := mixedPrimalStep B j
  letI := (mixedBundle B (true :: false :: j)).topology
  intro X s u hu p
  let st : Section LT.space.bundle := ⟨fun p =>
    (TensorProduct.assoc ℝ (Module.Dual ℝ (E p)) (E p) (MixedFiber E j p)).symm (s.val p),
    tensorAssoc_symm_smooth D.space.bundle B J.bundle V BC LT RT s⟩
  let CD := dualConnection B D C
  let CJ := mixedConnection B C j
  let CV := tensorConnection D.space.bundle B V CD C
  let CLT := tensorConnection V.space.bundle J.bundle LT CV CJ
  have hsc := spectatorContraction_derivative B D J.bundle C CJ CD
    (dualConnection_rule B D C) V CV (tensorConnection_rule D.space.bundle B V CD C)
    LT CLT (tensorConnection_rule V.space.bundle J.bundle LT CV CJ) X st u
    (by
      intro q
      have hh := congrArg (fun L : MixedFiber E (true :: false :: j) q →ₗ[ℝ] MixedFiber E j q =>
        L (s.val q)) (tensorContractSlots_head (E := E) j q)
      exact (hu q).trans hh) p
  letI := BC.space.topology
  have has := tensorAssoc_symm_derivative D.space.bundle B J.bundle V BC LT RT CD C CJ
    CV (mixedConnection B C (false :: j)) CLT (mixedConnection B C (true :: false :: j))
    (tensorConnection_rule D.space.bundle B V CD C)
    (tensorConnection_rule B J.bundle BC C CJ)
    (tensorConnection_rule V.space.bundle J.bundle LT CV CJ)
    (tensorConnection_rule D.space.bundle BC.space.bundle RT CD (mixedConnection B C (false :: j)))
    X s st (fun _ => rfl) p
  rw [has] at hsc
  have hh := congrArg (fun L : MixedFiber E (true :: false :: j) p →ₗ[ℝ] MixedFiber E j p =>
    L (((mixedConnection B C (true :: false :: j)).cov X s).val p))
      (tensorContractSlots_head (E := E) j p)
  exact hsc.trans hh.symm

end MixedHeadContraction
end P202.Geometry.InducedConnections

namespace P202.Geometry.InducedConnections
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.BundleData SmoothManifolds.FrameData
  SmoothManifolds.BundleOperationsData SmoothManifolds.SectionExtensionData P202.ConnectionData P202.InducedConnectionData
open Set Filter
open scoped Topology
universe u v w z t
section ParallelMapPullback
variable {n m r k : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {T : SmoothManifold m b N}
  {ι : Type v} {κ : Type t} {E : M → Type w} {G : M → Type z}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [∀ p, AddCommGroup (G p)] [∀ p, Module ℝ (G p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean k) G)]
  (B : SmoothVectorBundle S r ι E) (A : SmoothVectorBundle S k κ G)
  (L : (p : M) → E p →ₗ[ℝ] G p)
  (hL : ∀ s : Section B, SmoothSection A (fun p => L p (s.val p)))
  (F : N → M) (hF : IsSmoothMap T S F)
  (P : PullbackBundle B T F) (Q : PullbackBundle A T F)

include hL hF in
/-- A smooth fiberwise linear operation pulls back on arbitrary smooth fields
along a map; those fields need not themselves be pulled-back sections. -/
theorem parallelMap_pullback_smooth :
    letI := P.space.topology
    letI := Q.space.topology
    ∀ s : Section P.space.bundle,
      SmoothSection Q.space.bundle (fun q => L (F q) (s.val q)) := by
  letI := P.space.topology
  letI := Q.space.topology
  intro s q
  obtain ⟨f, e, he⟩ := PullbackConnections.section_germ_expansion B F hF P s q
  let v := ∑ j, mulSection (f j)
    (PullbackConnections.pullSection A F hF Q (fiberLinearMapSection B A L hL (e j)))
  have hv : ∀ z, v.val z = L (F z)
      ((∑ j, mulSection (f j) (PullbackConnections.pullSection B F hF P (e j))).val z) := by
    intro z
    simp only [v, Submodule.coe_sum, Finset.sum_apply, ConnectionForms.mulSection_apply,
      PullbackConnections.pullSection_apply, map_sum, map_smul]
    rfl
  apply SmoothManifolds.SectionExtension.section_smoothAt_congr Q.space.bundle (v.property q)
  filter_upwards [he] with z hz
  exact (hv z).trans (congrArg (L (F z)) hz.symm)

/-- The pulled-back fiberwise linear operation on spaces of smooth sections. -/
noncomputable def parallelMapPullbackSection :
    letI := P.space.topology
    letI := Q.space.topology
    Section P.space.bundle →ₗ[ℝ] Section Q.space.bundle := by
  letI := P.space.topology
  letI := Q.space.topology
  exact fiberLinearMapSection P.space.bundle Q.space.bundle (fun q => L (F q))
    (parallelMap_pullback_smooth B A L hL F hF P Q)

/-- Parallelism of a smooth fiber map holds intrinsically at each actual
tangent vector, with no related-field hypothesis. -/
theorem parallelMap_pointDerivative (C : Connection B) (K : Connection A)
    (hpar : ∀ (X : Field S) (s : Section B),
      K.cov X (fiberLinearMapSection B A L hL s) =
        fiberLinearMapSection B A L hL (C.cov X s))
    (s : Section B) (p : M) (v : TangentSpace S p) :
    pointDerivative K (fiberLinearMapSection B A L hL s).val p v =
      L p (pointDerivative C s.val p v) := by
  obtain ⟨X, hX⟩ := ConnectionForms.section_evaluation_surjective (tangentBundle S) p v
  rw [← hX, ConnectionForms.pointDerivative_global A K,
    ConnectionForms.pointDerivative_global B C, hpar]
  rfl

/-- Every parallel smooth fiberwise linear operation commutes with pullback
covariant differentiation on arbitrary smooth fields along any smooth map. -/
theorem parallelMap_pullback_derivative (C : Connection B) (K : Connection A)
    (hpar : ∀ (X : Field S) (s : Section B),
      K.cov X (fiberLinearMapSection B A L hL s) =
        fiberLinearMapSection B A L hL (C.cov X s)) :
    letI := P.space.topology
    letI := Q.space.topology
    ∀ (CP : Connection P.space.bundle) (CQ : Connection Q.space.bundle),
      P202.PullbackData.IsPullback B C F hF P CP →
      P202.PullbackData.IsPullback A K F hF Q CQ →
    ∀ (X : Field T) (s : Section P.space.bundle) (u : Section Q.space.bundle),
      (∀ q, u.val q = L (F q) (s.val q)) →
      ∀ q, (CQ.cov X u).val q = L (F q) ((CP.cov X s).val q) := by
  letI := P.space.topology
  letI := Q.space.topology
  intro CP CQ hCP hCQ X s u hu q
  obtain ⟨f, e, he⟩ := PullbackConnections.section_germ_expansion B F hF P s q
  let eP := fun j => PullbackConnections.pullSection B F hF P (e j)
  let eQ := fun j => PullbackConnections.pullSection A F hF Q
    (fiberLinearMapSection B A L hL (e j))
  have hv : ∀ z, (∑ j, mulSection (f j) (eQ j)).val z =
      L (F z) ((∑ j, mulSection (f j) (eP j)).val z) := by
    intro z
    simp only [eP, eQ, Submodule.coe_sum, Finset.sum_apply, ConnectionForms.mulSection_apply,
      PullbackConnections.pullSection_apply, map_sum, map_smul]
    rfl
  have heQ : ∀ᶠ z in 𝓝 q, u.val z = (∑ j, mulSection (f j) (eQ j)).val z := by
    filter_upwards [he] with z hz
    rw [hu z, hv z]
    exact congrArg (L (F z)) hz
  rw [ConnectionForms.locality_section Q.space.bundle CQ X u _ q heQ,
    ConnectionForms.locality_section P.space.bundle CP X s _ q he,
    ConnectionForms.finite_expansion Q.space.bundle CQ X r f eQ,
    ConnectionForms.finite_expansion P.space.bundle CP X r f eP]
  simp only [Submodule.coe_sum, Finset.sum_apply, ConnectionForms.section_add_apply,
    ConnectionForms.mulSection_apply, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hp := hCP X (e j) (eP j) (fun _ => rfl) q
  have hq := hCQ X (fiberLinearMapSection B A L hL (e j)) (eQ j) (fun _ => rfl) q
  rw [hq, hp, parallelMap_pointDerivative B A L hL C K hpar]
  rw [map_add, map_smul, map_smul]
  rfl
/-- The pulled-back section map is a parallel map for any realizations of the
pullback connections. -/
theorem parallelMap_pullback_parallel (C : Connection B) (K : Connection A)
    (hpar : ∀ (X : Field S) (s : Section B),
      K.cov X (fiberLinearMapSection B A L hL s) =
        fiberLinearMapSection B A L hL (C.cov X s)) :
    letI := P.space.topology
    letI := Q.space.topology
    ∀ (CP : Connection P.space.bundle) (CQ : Connection Q.space.bundle),
      P202.PullbackData.IsPullback B C F hF P CP →
      P202.PullbackData.IsPullback A K F hF Q CQ →
    ∀ (X : Field T) (s : Section P.space.bundle),
      CQ.cov X (parallelMapPullbackSection B A L hL F hF P Q s) =
        parallelMapPullbackSection B A L hL F hF P Q (CP.cov X s) := by
  letI := P.space.topology
  letI := Q.space.topology
  intro CP CQ hCP hCQ X s
  apply Subtype.ext
  funext q
  exact parallelMap_pullback_derivative B A L hL F hF P Q C K hpar CP CQ hCP hCQ X s
    (parallelMapPullbackSection B A L hL F hF P Q s) (fun _ => rfl) q

end ParallelMapPullback
end P202.Geometry.InducedConnections

namespace P202.Geometry.InducedConnections
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
 SmoothManifolds.TangentData SmoothManifolds.BundleData SmoothManifolds.FrameData
 SmoothManifolds.BundleOperationsData SmoothManifolds.SectionExtensionData P202.ConnectionData
 P202.InducedConnectionData
universe u v w
/-- Evaluation followed by scalar multiplication is the canonical contraction. -/
theorem spectatorContraction_eq_lid_map {V W : Type*}
 [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W] :
 (spectatorContraction : TensorProduct ℝ (TensorProduct ℝ (Module.Dual ℝ V) V) W →ₗ[ℝ] W) =
 (TensorProduct.lid ℝ W).toLinearMap.comp
   (TensorProduct.map evaluationContraction (LinearMap.id : W →ₗ[ℝ] W)) := by
 apply TensorProduct.ext'
 intro v w
 rw [spectatorContraction_tmul]
 rfl
/-- Any two-slot contraction is a first-pair contraction after its two canonical plucks. -/
theorem tensorContractSlots_via_head {M : Type u} [TopologicalSpace M] (E : M → Type w)
 [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
 {l k j : List Bool} (hd : TensorSlot true l k) (hp : TensorSlot false k j)
 (p : M) (v : MixedFiber E l p) :
 tensorContractSlots E hd hp p v =
   tensorContractSlots E (.here (false :: j)) (.here j) p
     (TensorProduct.map LinearMap.id (tensorSlotEquiv E hp p).toLinearMap
       (tensorSlotEquiv E hd p v)) := by
 rw [tensorContractSlots_head, spectatorContraction_eq_lid_map]
 rfl
variable {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
 {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
 [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
 [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
 (B : SmoothVectorBundle S r ι E)
theorem tensorContractSlots_smooth {l k j : List Bool}
 (hd : TensorSlot true l k) (hp : TensorSlot false k j) :
 letI := (mixedBundle B l).topology
 letI := (mixedBundle B j).topology
 ∀ s : Section (mixedBundle B l).bundle,
 SmoothSection (mixedBundle B j).bundle (fun p => tensorContractSlots E hd hp p (s.val p)) := by
 let D := mixedDualBundle B
 let K := mixedBundle B k
 let J := mixedBundle B j
 let F := mixedAtomStep B true k
 let P := mixedAtomStep B false j
 let U := mixedAtomStep B true (false :: j)
 letI := D.space.topology
 letI := (tensorAtomBundle B true).topology
 letI := (tensorAtomBundle B false).topology
 letI := K.topology
 letI := J.topology
 letI := F.space.topology
 letI := P.space.topology
 letI := (mixedBundle B (false :: j)).topology
 letI := U.space.topology
 letI := (mixedBundle B (true :: false :: j)).topology
 letI := (mixedBundle B l).topology
 intro s
 let s1 : Section F.space.bundle :=
   ⟨fun p => tensorSlotEquiv E hd p (s.val p), tensorSlot_smooth B hd s⟩
 have hs2 := tensorProductMap_smooth D.space.bundle K.bundle D.space.bundle P.space.bundle F U
   (fun _ => LinearMap.id) (fun p => (tensorSlotEquiv E hp p).toLinearMap)
   (fun v => v.property) (tensorSlot_smooth B hp) s1
 let s2 : Section U.space.bundle :=
   ⟨fun p => TensorProduct.map LinearMap.id (tensorSlotEquiv E hp p).toLinearMap (s1.val p), hs2⟩
 have hs3 := mixedHeadContraction_smooth B j s2
 have he : (fun p => tensorContractSlots E hd hp p (s.val p)) =
   (fun p => tensorContractSlots E (.here (false :: j)) (.here j) p (s2.val p)) := by
   funext p
   exact tensorContractSlots_via_head E hd hp p (s.val p)
 rw [he]
 exact hs3
/-- Every natural contraction at an arbitrary dual/primal slot pair commutes
with the induced connection on all smooth sections of every mixed tensor power. -/
theorem tensorContractSlots_derivative (C : Connection B) {l k j : List Bool}
 (hd : TensorSlot true l k) (hp : TensorSlot false k j) :
 letI := (mixedBundle B l).topology
 letI := (mixedBundle B j).topology
 ∀ (X : Field S) (s : Section (mixedBundle B l).bundle)
 (out : Section (mixedBundle B j).bundle),
 (∀ p, out.val p = tensorContractSlots E hd hp p (s.val p)) →
 ∀ p, ((mixedConnection B C j).cov X out).val p =
   tensorContractSlots E hd hp p (((mixedConnection B C l).cov X s).val p) := by
 let D := mixedDualBundle B
 let K := mixedBundle B k
 let J := mixedBundle B j
 let F := mixedAtomStep B true k
 let P := mixedAtomStep B false j
 let U := mixedAtomStep B true (false :: j)
 letI := D.space.topology
 letI := (tensorAtomBundle B true).topology
 letI := (tensorAtomBundle B false).topology
 letI := K.topology
 letI := J.topology
 letI := F.space.topology
 letI := P.space.topology
 letI := (mixedBundle B (false :: j)).topology
 letI := (mixedBundle B (true :: k)).topology
 letI := U.space.topology
 letI := (mixedBundle B (true :: false :: j)).topology
 letI := (mixedBundle B l).topology
 let CD := dualConnection B D C
 let CK := mixedConnection B C k
 let CP := mixedConnection B C (false :: j)
 let CF := mixedConnection B C (true :: k)
 let CU := mixedConnection B C (true :: false :: j)
 let Rmap := fun p => (tensorSlotEquiv E hp p).toLinearMap
 let hR := tensorSlot_smooth B hp
 let hL := fun v : Section D.space.bundle => v.property
 have hPR : ∀ (Y : Field S) (v : Section K.bundle),
   CP.cov Y (fiberLinearMapSection K.bundle P.space.bundle Rmap hR v) =
     fiberLinearMapSection K.bundle P.space.bundle Rmap hR (CK.cov Y v) := by
   intro Y v
   apply Subtype.ext
   funext p
   exact tensorSlot_derivative B C hp Y v
     (fiberLinearMapSection K.bundle P.space.bundle Rmap hR v) (fun _ => rfl) p
 intro X s out hout p
 let s1 : Section F.space.bundle :=
   ⟨fun p => tensorSlotEquiv E hd p (s.val p), tensorSlot_smooth B hd s⟩
 have hs2 := tensorProductMap_smooth D.space.bundle K.bundle D.space.bundle P.space.bundle F U
   (fun _ => LinearMap.id) Rmap hL hR s1
 let s2 : Section U.space.bundle :=
   ⟨fun p => TensorProduct.map LinearMap.id (Rmap p) (s1.val p), hs2⟩
 have h1 := tensorSlot_derivative B C hd X s s1 (fun _ => rfl) p
 have h2 := tensorProductMap_derivative D.space.bundle K.bundle D.space.bundle P.space.bundle F U
   (fun _ => LinearMap.id) Rmap hL hR CD CK CD CP (fun _ _ => rfl) hPR
   CF CU (mixedAtomStep_rule B C true k) (mixedAtomStep_rule B C true (false :: j))
   X s1 s2 (fun _ => rfl) p
 have houthead : ∀ q, out.val q =
   tensorContractSlots E (.here (false :: j)) (.here j) q (s2.val q) := by
   intro q
   exact (hout q).trans (tensorContractSlots_via_head E hd hp q (s.val q))
 have h3 := mixedHeadContraction_derivative B C j X s2 out houthead p
 change (((mixedConnection B C (true :: false :: j)).cov X s2).val p) =
   TensorProduct.map LinearMap.id (Rmap p)
     (((mixedAtomStepConnection B C true k).cov X s1).val p) at h2
 rw [h2, h1] at h3
 exact h3.trans (tensorContractSlots_via_head E hd hp p
   (((mixedConnection B C l).cov X s).val p)).symm
theorem mixedContraction_rule (C : Connection B) :
 MixedContractionRule B (mixedConnection B C) := by
 intro l k j hd hp
 exact ⟨tensorContractSlots_smooth B hd hp, tensorContractSlots_derivative B C hd hp⟩
end P202.Geometry.InducedConnections

namespace P202.Geometry.InducedConnections
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.BundleData SmoothManifolds.FrameData
  SmoothManifolds.BundleOperationsData SmoothManifolds.SectionExtensionData P202.ConnectionData P202.InducedConnectionData
open Set Filter
open scoped Topology
universe u v w z t

open P202.CurveConnectionData
section MixedContractionCarry
variable {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E) (C : Connection B)

/-- The proved smooth all-slot contraction rule carries through the actual
pullback connections to arbitrary fields along every smooth map. -/
theorem mixedMapContraction_rule
    (hcontr : MixedContractionRule B (mixedConnection B C)) :
    MixedMapContractionRule B (mixedConnection B C) := by
  intro l k j hd hp
  letI := (mixedBundle B l).topology
  letI := (mixedBundle B j).topology
  intro m b N _ T F hF P Q
  letI := P.space.topology
  letI := Q.space.topology
  let L := tensorContractSlots E hd hp
  let hL := (hcontr hd hp).1
  have hpar : ∀ (X : Field S) (s : Section (mixedBundle B l).bundle),
      (mixedConnection B C j).cov X
        (fiberLinearMapSection (mixedBundle B l).bundle (mixedBundle B j).bundle L hL s) =
      fiberLinearMapSection (mixedBundle B l).bundle (mixedBundle B j).bundle L hL
        ((mixedConnection B C l).cov X s) := by
    intro X s
    apply Subtype.ext
    funext p
    exact (hcontr hd hp).2 X s
      (fiberLinearMapSection (mixedBundle B l).bundle (mixedBundle B j).bundle L hL s)
      (fun _ => rfl) p
  refine ⟨parallelMap_pullback_smooth (mixedBundle B l).bundle (mixedBundle B j).bundle
    L hL F hF P Q, ?_⟩
  exact parallelMap_pullback_derivative (mixedBundle B l).bundle (mixedBundle B j).bundle
    L hL F hF P Q (mixedConnection B C l) (mixedConnection B C j) hpar

/-- All-slot contractions also carry through genuine within covariant
derivatives along C¹ curves, including ordinary and one-sided derivatives. -/
theorem mixedCurveContraction_rule
    (hcontr : MixedContractionRule B (mixedConnection B C)) :
    MixedCurveContractionRule B (mixedConnection B C) := by
  intro l k j hd hp
  letI := (mixedBundle B l).topology
  letI := (mixedBundle B j).topology
  intro c f J t ht hJ D hD
  let L := tensorContractSlots E hd hp
  let hL := (hcontr hd hp).1
  have hpar : ∀ (X : Field S) (s : Section (mixedBundle B l).bundle),
      (mixedConnection B C j).cov X
        (fiberLinearMapSection (mixedBundle B l).bundle (mixedBundle B j).bundle L hL s) =
      fiberLinearMapSection (mixedBundle B l).bundle (mixedBundle B j).bundle L hL
        ((mixedConnection B C l).cov X s) := by
    intro X s
    apply Subtype.ext
    funext p
    exact (hcontr hd hp).2 X s
      (fiberLinearMapSection (mixedBundle B l).bundle (mixedBundle B j).bundle L hL s)
      (fun _ => rfl) p
  have hg := parallelMap_curve_derivative (mixedBundle B l).bundle (mixedBundle B j).bundle
    L hL (mixedConnection B C l) (mixedConnection B C j) hpar ht hJ hD
  refine ⟨hg, ?_⟩
  rw [CurveCovariantDerivative.covariantDerivativeWithin_eq (mixedConnection B C j) ht hJ hg,
    CurveCovariantDerivative.covariantDerivativeWithin_eq (mixedConnection B C l) ht hJ hD]

end MixedContractionCarry

end P202.Geometry.InducedConnections

namespace P202.Geometry.InducedConnections
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.BundleData
 SmoothManifolds.BundleOperationsData P202.ConnectionData P202.InducedConnectionData
universe u v w z t

theorem balanced_product_derivative :
    P202Specs.Geometry.InducedConnections.balanced_product_derivativeType.{u,v,t,w,z} := by
  intro n r k a M _ S ι κ E F _ _ _ _ _ _ B A C K X f s u p
  let T := Classical.choice (SmoothManifolds.BundleOperations.exists_tensor B A)
  letI := T.space.topology
  exact congrArg (fun s : Section T.space.bundle => s.val p)
    (pureTensorDerivative_balance B A T C K X f s u)

/-- All finite mixed powers and all their natural contractions, with smooth-map
pullback and genuine C¹-curve differentiation, for every original connection. -/
theorem mixed_calculus_exists :
    P202Specs.Geometry.InducedConnections.mixed_calculus_existsType.{u,v,w} := by
  intro n r a M _ S ι E _ _ _ B C
  letI := (mixedDualBundle B).space.topology
  exact ⟨dualConnection B (mixedDualBundle B) C, mixedConnection B C,
    mixedConnection_rule B C, mixedContraction_rule B C,
    mixedMapContraction_rule B C (mixedContraction_rule B C),
    mixedCurveContraction_rule B C (mixedContraction_rule B C)⟩
end P202.Geometry.InducedConnections

namespace P202.Geometry.InducedConnections
universe u v w
/-- The actual finite mixed tensor bundle used by the constructed connections. -/
noncomputable def mixedTensorBundle :
    P202Specs.Geometry.InducedConnections.mixedTensorBundleType.{u,v,w} :=
  @P202.InducedConnectionData.mixedBundle

/-- Canonical contraction at any specified dual/primal pair of slots. -/
noncomputable def contraction :
    P202Specs.Geometry.InducedConnections.contractionType.{u,w} :=
  @P202.InducedConnectionData.tensorContractSlots
end P202.Geometry.InducedConnections
