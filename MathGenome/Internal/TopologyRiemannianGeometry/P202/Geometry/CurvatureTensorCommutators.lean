import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.CurvatureTensorCommutators
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.InducedConnections
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.SecondBianchi
import Mathlib.Tactic.Module

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000
namespace P202.Geometry.CurvatureTensorCommutators
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.BundleData SmoothManifolds.BundleOperationsData
  P202.ConnectionData P202.InducedConnectionData P202.CurvatureData
  P202.TensorCommutatorData P202.TorsionMetricData
open ConnectionForms (section_ext section_add_apply section_smul_apply section_zero_apply
  mulSection_apply scalarDerivative_global section_evaluation_surjective)
open Set Filter
open scoped Topology
universe u v w z t

section General
variable {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E) (C : Connection B)

@[simp] theorem commutator_apply (X Y : Field S) (s : Section B) (p : M) :
    (commutator C X Y s).val p = (C.cov X (C.cov Y s)).val p -
      (C.cov Y (C.cov X s)).val p - (C.cov (bracket X Y) s).val p := rfl

/-- Locality applies twice, so local tensor presentations suffice even for
second derivatives. -/
theorem commutator_local (X Y : Field S) (s u : Section B) (p : M)
    (h : ∀ᶠ q in 𝓝 p, s.val q = u.val q) :
    (commutator C X Y s).val p = (commutator C X Y u).val p := by
  have hd (Z : Field S) : ∀ᶠ q in 𝓝 p, (C.cov Z s).val q = (C.cov Z u).val q :=
    h.eventually_nhds.mono (fun q hq => ConnectionForms.locality_section B C Z s u q hq)
  simp only [commutator_apply]
  rw [ConnectionForms.locality_section B C X _ _ p (hd Y),
    ConnectionForms.locality_section B C Y _ _ p (hd X),
    ConnectionForms.locality_section B C (bracket X Y) s u p h]
end General

section Dual
variable {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E) (C : Connection B) (D : DualBundle B)

/-- Differentiation of evaluation is proved first; its commutator then has
zero scalar part. No curvature rule on duals is assumed. -/
theorem dual_pairing_derivative :
    letI := D.space.topology
    ∀ (K : Connection D.space.bundle), DualRule C D K →
    ∀ (X : Field S) (lam : Section D.space.bundle) (s : Section B),
      InducedConnections.pairing B D (K.cov X lam) s =
        act S X (InducedConnections.pairing B D lam s) -
          InducedConnections.pairing B D lam (C.cov X s) := by
  letI := D.space.topology
  intro K hK X lam s
  apply Subtype.ext; funext p
  apply (hK X lam s p).trans
  change scalarDerivative S (InducedConnections.pairing B D lam s).val p (X.val p) -
    lam.val p ((C.cov X s).val p) = _
  rw [scalarDerivative_global]
  rfl

theorem dual_commutator_evaluation :
    letI := D.space.topology
    ∀ (K : Connection D.space.bundle), DualRule C D K →
    ∀ (X Y : Field S) (lam : Section D.space.bundle) (s : Section B) (p : M),
      ((commutator K X Y lam).val p) (s.val p) =
        -lam.val p ((commutator C X Y s).val p) := by
  letI := D.space.topology
  intro K hK X Y lam s p
  have hbr := TorsionAndMetric.bracket_act X Y (InducedConnections.pairing B D lam s) p
  rw [scalarDerivative_global] at hbr
  have hXY := congrArg (fun f : GlobalSmooth S => f.val p)
    (dual_pairing_derivative B C D K hK X (K.cov Y lam) s)
  have hYX := congrArg (fun f : GlobalSmooth S => f.val p)
    (dual_pairing_derivative B C D K hK Y (K.cov X lam) s)
  rw [dual_pairing_derivative B C D K hK Y lam s, map_sub] at hXY
  rw [dual_pairing_derivative B C D K hK X lam s, map_sub] at hYX
  have h1 := congrArg (fun f : GlobalSmooth S => f.val p)
    (dual_pairing_derivative B C D K hK Y lam (C.cov X s))
  have h2 := congrArg (fun f : GlobalSmooth S => f.val p)
    (dual_pairing_derivative B C D K hK X lam (C.cov Y s))
  have h3 := congrArg (fun f : GlobalSmooth S => f.val p)
    (dual_pairing_derivative B C D K hK (bracket X Y) lam s)
  simp only [InducedConnections.pairing_apply, Subalgebra.coe_sub, Pi.sub_apply] at *
  simp only [commutator_apply, LinearMap.sub_apply, map_sub]
  linarith
end Dual

section Tensor
variable {n r k : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {κ : Type t}
  {E : M → Type w} {F : M → Type z}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [∀ p, AddCommGroup (F p)] [∀ p, Module ℝ (F p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean k) F)]
  (B : SmoothVectorBundle S r ι E) (A : SmoothVectorBundle S k κ F)
  (C : Connection B) (K : Connection A) (U : TensorBundle B A)

 theorem tensor_derivative_section :
    letI := U.space.topology
    ∀ (N : Connection U.space.bundle), TensorRule C K U N →
    ∀ (X : Field S) (s : Section B) (u : Section A),
      N.cov X (InducedConnections.tensorSection B A U s u) =
        InducedConnections.tensorSection B A U (C.cov X s) u +
          InducedConnections.tensorSection B A U s (K.cov X u) := by
  letI := U.space.topology
  intro N hN X s u
  apply section_ext; intro p
  exact hN X s u _ (fun _ => rfl) p

/-- The two mixed second derivatives cancel in the product commutator. -/
theorem tensor_commutator_pure :
    letI := U.space.topology
    ∀ (N : Connection U.space.bundle), TensorRule C K U N →
    ∀ (X Y : Field S) (s : Section B) (u : Section A) (p : M),
      (commutator N X Y (InducedConnections.tensorSection B A U s u)).val p =
        TensorProduct.tmul ℝ ((commutator C X Y s).val p) (u.val p) +
          TensorProduct.tmul ℝ (s.val p) ((commutator K X Y u).val p) := by
  letI := U.space.topology
  intro N hN X Y s u p
  simp only [commutator_apply, tensor_derivative_section B A C K U N hN,
    map_add, section_add_apply, InducedConnections.tensorSection_apply,
    TensorProduct.sub_tmul, TensorProduct.tmul_sub]
  abel

/-- Local finite presentations extend the formula from pure tensors to every
smooth tensor section. No global frame or global generation is required. -/
theorem tensor_commutator :
    letI := U.space.topology
    ∀ (N : Connection U.space.bundle), TensorRule C K U N →
    ∀ (X Y : Field S) (p : M) (R : E p →ₗ[ℝ] E p) (Q : F p →ₗ[ℝ] F p),
      (∀ s : Section B, (commutator C X Y s).val p = R (s.val p)) →
      (∀ u : Section A, (commutator K X Y u).val p = Q (u.val p)) →
    ∀ s : Section U.space.bundle,
      (commutator N X Y s).val p =
        ((TensorProduct.map R (LinearMap.id : F p →ₗ[ℝ] F p) +
          TensorProduct.map (LinearMap.id : E p →ₗ[ℝ] E p) Q) :
          TensorProduct ℝ (E p) (F p) →ₗ[ℝ] TensorProduct ℝ (E p) (F p)) (s.val p) := by
  letI := U.space.topology
  intro N hN X Y p R Q hR hQ s
  have hp (x : InducedConnections.TensorPresentation B A) :
      (commutator N X Y (InducedConnections.tensorPresentationValue B A U x)).val p =
        ((TensorProduct.map R (LinearMap.id : F p →ₗ[ℝ] F p) +
          TensorProduct.map (LinearMap.id : E p →ₗ[ℝ] E p) Q) :
          TensorProduct ℝ (E p) (F p) →ₗ[ℝ] TensorProduct ℝ (E p) (F p))
          ((InducedConnections.tensorPresentationValue B A U x).val p) := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v w =>
      rw [InducedConnections.tensorPresentationValue_tmul,
        tensor_commutator_pure B A C K U N hN, hR, hQ]
      rfl
    | add x y hx hy =>
      simp only [map_add, section_add_apply, hx, hy]
  obtain ⟨x, hx⟩ := InducedConnections.exists_tensorPresentation B A U s p
  rw [commutator_local U.space.bundle N X Y s _ p (hx.mono (fun _ h => h.symm)),
    hp, hx.self_of_nhds]
end Tensor

section Unit
variable {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E)

noncomputable def unitScalar :
    letI := (mixedBundle B []).topology
    Section (mixedBundle B []).bundle → GlobalSmooth S := by
  letI := (mixedBundle B []).topology
  letI := (mixedUnitBundle B).space.topology
  exact fun s => frameCoefficient (mixedUnitFrame B) s ⟨0, by simp⟩

@[simp] theorem unitScalar_apply :
    letI := (mixedBundle B []).topology
    ∀ (s : Section (mixedBundle B []).bundle) (p : M),
      (unitScalar B s).val p = exteriorPower.zeroEquiv ℝ (E p) (s.val p) := by
  letI := (mixedBundle B []).topology
  exact fun s p => InducedConnections.mixedUnit_coefficient B s ⟨0, by simp⟩ p

 theorem unitScalar_derivative :
    letI := (mixedBundle B []).topology
    ∀ (K : Connection (mixedBundle B []).bundle), MixedUnitRule B K →
    ∀ (X : Field S) (s : Section (mixedBundle B []).bundle),
      unitScalar B (K.cov X s) = act S X (unitScalar B s) := by
  letI := (mixedBundle B []).topology
  intro K hK X s
  apply Subtype.ext; funext p
  rw [unitScalar_apply, hK]
  have hf : (fun q => exteriorPower.zeroEquiv ℝ (E q) (s.val q)) = (unitScalar B s).val :=
    funext (fun q => (unitScalar_apply B s q).symm)
  rw [hf, scalarDerivative_global]

 theorem unit_commutator :
    letI := (mixedBundle B []).topology
    ∀ (K : Connection (mixedBundle B []).bundle), MixedUnitRule B K →
    ∀ (X Y : Field S) (s : Section (mixedBundle B []).bundle) (p : M),
      (commutator K X Y s).val p = 0 := by
  letI := (mixedBundle B []).topology
  intro K hK X Y s p
  apply (exteriorPower.zeroEquiv ℝ (E p)).injective
  rw [map_zero, ← unitScalar_apply]
  have hlin : unitScalar B (commutator K X Y s) =
      act S X (act S Y (unitScalar B s)) -
        act S Y (act S X (unitScalar B s)) - act S (bracket X Y) (unitScalar B s) := by
    apply Subtype.ext; funext q
    rw [unitScalar_apply]
    simp only [commutator_apply, map_sub, ← unitScalar_apply,
      unitScalar_derivative B K hK]
    rfl
  rw [hlin]
  have h := TorsionAndMetric.bracket_act X Y (unitScalar B s) p
  rw [scalarDerivative_global] at h
  change (act S X (act S Y (unitScalar B s))).val p -
    (act S Y (act S X (unitScalar B s))).val p -
      (act S (bracket X Y) (unitScalar B s)).val p = 0
  linarith
end Unit


section Mixed
variable {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E) (C : Connection B)

/-- The tensor-word argument is independent of any realization of the base
bundle. Specialization to the intrinsic tangent bundle is made below. -/
theorem mixed_commutator_at :
    letI := (mixedDualBundle B).space.topology
    ∀ (D : Connection (mixedDualBundle B).space.bundle) (K : MixedConnections B),
    MixedFamilyRule B C D K →
    ∀ (X Y : Field S) (p : M) (R : E p →ₗ[ℝ] E p),
    (∀ s : Section B, (commutator C X Y s).val p = R (s.val p)) →
    ∀ (l : List Bool), letI := (mixedBundle B l).topology
    ∀ s : Section (mixedBundle B l).bundle,
      (commutator (K l) X Y s).val p = mixedAction E p R l (s.val p) := by
  letI := (mixedDualBundle B).space.topology
  intro D K hK X Y p R hR l
  induction l with
  | nil =>
    letI := (mixedBundle B []).topology
    intro s
    exact unit_commutator B (K []) hK.2.1 X Y s p
  | cons b l ih =>
    letI := (mixedBundle B l).topology
    cases b with
    | false =>
      letI := (mixedBundle B (false :: l)).topology
      intro s
      exact tensor_commutator (E := E) (F := MixedFiber E l)
        B (mixedBundle B l).bundle C (K l) (mixedPrimalStep B l)
        (K (false :: l)) (hK.2.2.1 l) X Y p R (mixedAction E p R l) hR ih s
    | true =>
      letI := (mixedBundle B (true :: l)).topology
      intro s
      apply tensor_commutator (E := fun p => Module.Dual ℝ (E p)) (F := MixedFiber E l)
        (mixedDualBundle B).space.bundle (mixedBundle B l).bundle D (K l)
        (mixedDualStep B l) (K (true :: l)) (hK.2.2.2 l) X Y p
        (dualAction R) (mixedAction E p R l) ?_ ih s
      intro lam
      apply LinearMap.ext; intro v
      obtain ⟨s, rfl⟩ := section_evaluation_surjective B p v
      change ((commutator D X Y lam).val p) (s.val p) = -lam.val p (R (s.val p))
      rw [dual_commutator_evaluation B C (mixedDualBundle B) D hK.1, hR]
end Mixed

section Tangent
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M}

 theorem tangent_commutator (C : Connection (tangentBundle S)) (X Y Z : Field S) :
    commutator C X Y Z = curvature C X Y Z := by
  apply section_ext; intro p
  rw [commutator_apply, CurvatureAlgebra.curvature_apply]

 theorem dual_commutator : P202Specs.Geometry.CurvatureTensorCommutators.dual_commutatorType.{u} := by
  intro n a M _ S C T hT D
  letI := D.space.topology
  intro K hK X Y lam p z
  obtain ⟨Z, rfl⟩ := section_evaluation_surjective (tangentBundle S) p z
  rw [dual_commutator_evaluation (tangentBundle S) C D K hK X Y lam Z p,
    tangent_commutator, ← hT X Y Z p]

 theorem mixed_commutator : P202Specs.Geometry.CurvatureTensorCommutators.mixed_commutatorType.{u} := by
  intro n a M _ S C T hT
  dsimp only
  let B := tangentBundle S
  letI := (mixedDualBundle B).space.topology
  intro D K hK l
  letI := (mixedBundle B l).topology
  intro X Y s p
  apply mixed_commutator_at B C D K hK X Y p (T.val p (X.val p) (Y.val p)) ?_ l s
  intro Z
  rw [tangent_commutator, hT]
end Tangent

 theorem mixed_contraction : P202Specs.Geometry.CurvatureTensorCommutators.mixed_contractionType.{u} := by
  intro n a M _ S K hK l k j hd hp
  let B := tangentBundle S
  letI := (mixedBundle B l).topology
  letI := (mixedBundle B j).topology
  intro X Y s u hu p
  let L := tensorContractSlots (TangentSpace S) hd hp
  let contract (s : Section (mixedBundle B l).bundle) : Section (mixedBundle B j).bundle :=
    ⟨fun p => L p (s.val p), (hK hd hp).1 s⟩
  have hc (Z : Field S) (s : Section (mixedBundle B l).bundle) :
      (K j).cov Z (contract s) = contract ((K l).cov Z s) := by
    apply section_ext; intro q
    exact (hK hd hp).2 Z s (contract s) (fun _ => rfl) q
  have he : u = contract s := Subtype.ext (funext hu)
  rw [he]
  simp only [commutator_apply, hc]
  change L p (((K l).cov X ((K l).cov Y s)).val p) -
    L p (((K l).cov Y ((K l).cov X s)).val p) -
    L p (((K l).cov (bracket X Y) s).val p) = _
  rw [map_sub, map_sub]

 theorem induced_calculus : P202Specs.Geometry.CurvatureTensorCommutators.induced_calculusType.{u} := by
  intro n a M _ S C T hT
  obtain ⟨D, K, hK, hcon, _, _⟩ := InducedConnections.mixed_calculus_exists (tangentBundle S) C
  exact ⟨D, K, hK, hcon, mixed_commutator C T hT D K hK⟩


 theorem curvature_contraction : P202Specs.Geometry.CurvatureTensorCommutators.curvature_contractionType.{u} := by
  intro n a M _ S C T hT l k j hd hp p x y t
  obtain ⟨D, K, hK, hcon, _⟩ := induced_calculus C T hT
  let B := tangentBundle S
  letI := (mixedBundle B l).topology
  letI := (mixedBundle B j).topology
  obtain ⟨X, rfl⟩ := section_evaluation_surjective B p x
  obtain ⟨Y, rfl⟩ := section_evaluation_surjective B p y
  obtain ⟨s, rfl⟩ := section_evaluation_surjective (mixedBundle B l).bundle p t
  let u : Section (mixedBundle B j).bundle :=
    ⟨fun q => tensorContractSlots (TangentSpace S) hd hp q (s.val q), (hcon hd hp).1 s⟩
  have h := mixed_contraction K hcon hd hp X Y s u (fun _ => rfl) p
  rw [mixed_commutator C T hT D K hK j X Y u p,
    mixed_commutator C T hT D K hK l X Y s p] at h
  exact h.symm

 theorem complete_curvature : P202Specs.Geometry.CurvatureTensorCommutators.complete_curvatureType.{u} :=
  ⟨CurvatureAlgebra.tensorial, CurvatureAlgebra.tensor_exists_unique,
    CurvatureAlgebra.symmetries, CurvatureAlgebra.first_bianchi,
    SecondBianchi.second_bianchi, dual_commutator, mixed_commutator,
    mixed_contraction, induced_calculus, curvature_contraction⟩

end P202.Geometry.CurvatureTensorCommutators
