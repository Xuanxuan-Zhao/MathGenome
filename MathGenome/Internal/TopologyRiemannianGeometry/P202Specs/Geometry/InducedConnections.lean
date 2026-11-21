import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.ConnectionCalculus

/-! Independent specification for the induced connections in paper.tex 3039--3040,
3056--3062. The fiber duals and tensor products below are the actual P104 bundle
operations, with no metric, global frame or positive rank assumption. -/
set_option autoImplicit false
namespace P202.InducedConnectionData
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.FrameData
  SmoothManifolds.TangentData SmoothManifolds.BundleData
  SmoothManifolds.BundleOperationsData P202.ConnectionData
universe u v w

section Dual
variable {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  {B : SmoothVectorBundle S r ι E}

/-- Characterization of the induced dual connection on the actual dual bundle.
The scalar derivative is the intrinsic differential of the evaluation function. -/
def DualRule (C : Connection B) (D : DualBundle B) :
    letI := D.space.topology; Connection D.space.bundle → Prop := by
  letI := D.space.topology
  exact fun K => ∀ (X : Field S) (lam : Section D.space.bundle)
    (s : Section B) (p : M),
    ((K.cov X lam).val p) (s.val p) =
      scalarDerivative S (fun q => lam.val q (s.val q)) p (X.val p) -
        lam.val p ((C.cov X s).val p)
end Dual
section Tensor
universe z t
variable {n r k : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {κ : Type t}
  {E : M → Type w} {F : M → Type z}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [∀ p, AddCommGroup (F p)] [∀ p, Module ℝ (F p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean k) F)]
  {B : SmoothVectorBundle S r ι E} {A : SmoothVectorBundle S k κ F}

/-- Product-rule characterization for the actual tensor bundle. The smoothness
of pure products is separately specified, so this is not a vacuous condition. -/
def TensorRule (C : Connection B) (K : Connection A) (T : TensorBundle B A) :
    letI := T.space.topology; Connection T.space.bundle → Prop := by
  letI := T.space.topology
  exact fun N => ∀ (X : Field S) (s : Section B) (u : Section A)
    (v : Section T.space.bundle),
    (∀ p, v.val p = TensorProduct.tmul ℝ (s.val p) (u.val p)) →
    ∀ p, (N.cov X v).val p =
      TensorProduct.tmul ℝ ((C.cov X s).val p) (u.val p) +
        TensorProduct.tmul ℝ (s.val p) ((K.cov X u).val p)
end Tensor
/-- The natural evaluation contraction on the actual fiber tensor product. -/
noncomputable def evaluationContraction {V : Type*} [AddCommGroup V] [Module ℝ V] :
    TensorProduct ℝ (Module.Dual ℝ V) V →ₗ[ℝ] ℝ :=
  TensorProduct.lift (LinearMap.id : Module.Dual ℝ V →ₗ[ℝ] Module.Dual ℝ V)

end P202.InducedConnectionData

namespace P202Specs.Geometry.InducedConnections
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.FrameData
  SmoothManifolds.TangentData SmoothManifolds.BundleData
  SmoothManifolds.BundleOperationsData P202.ConnectionData P202.InducedConnectionData
universe u v w

def dual_exists_uniqueType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    (B : SmoothVectorBundle S r ι E) (C : Connection B) (D : DualBundle B),
    letI := D.space.topology
    ∃! K : Connection D.space.bundle, DualRule C D K

/-- Elementary contraction, with the derivative on smooth scalars interpreted
intrinsically. It holds for the uniquely induced dual connection. -/
def dual_contractionType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    (B : SmoothVectorBundle S r ι E) (C : Connection B) (D : DualBundle B),
    letI := D.space.topology
    ∀ (K : Connection D.space.bundle), DualRule C D K →
    ∀ (X : Field S) (lam : Section D.space.bundle) (s : Section B) (p : M),
      scalarDerivative S (fun q => lam.val q (s.val q)) p (X.val p) =
        (K.cov X lam).val p (s.val p) + lam.val p ((C.cov X s).val p)

universe z t

def tensor_exists_uniqueType.{u₁,v₁,t₁,w₁,z₁} : Prop :=
  ∀ {n r k : ℕ} {a : ModelKind} {M : Type u₁} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v₁} {κ : Type t₁}
    {E : M → Type w₁} {F : M → Type z₁}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [∀ p, AddCommGroup (F p)] [∀ p, Module ℝ (F p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean k) F)]
    (B : SmoothVectorBundle S r ι E) (A : SmoothVectorBundle S k κ F)
    (C : Connection B) (K : Connection A) (T : TensorBundle B A),
    letI := T.space.topology
    ∃! N : Connection T.space.bundle, TensorRule C K T N

def tensorSection_smoothType : Prop :=
  ∀ {n r k : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {κ : Type t}
    {E : M → Type w} {F : M → Type z}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [∀ p, AddCommGroup (F p)] [∀ p, Module ℝ (F p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean k) F)]
    (B : SmoothVectorBundle S r ι E) (A : SmoothVectorBundle S k κ F)
    (T : TensorBundle B A) (s : Section B) (u : Section A),
    letI := T.space.topology
    SmoothManifolds.SectionExtensionData.SmoothSection T.space.bundle
      (fun p => TensorProduct.tmul ℝ (s.val p) (u.val p))

/-- Evaluation contraction is smooth on every smooth tensor section, including
sections which are not globally a pure tensor or a finite sum of pure sections. -/
def evaluation_contraction_smoothType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    (B : SmoothVectorBundle S r ι E) (D : DualBundle B),
    letI := D.space.topology
    ∀ (T : TensorBundle D.space.bundle B),
    letI := T.space.topology
    ∀ s : Section T.space.bundle,
    ∀ p, VectorSmoothAt S.smoothStructure.val
      (fun q => evaluationContraction (s.val q)) p

/-- Natural evaluation contraction commutes with differentiation on arbitrary
sections of E* ⊗ E for the induced dual and tensor connections. -/
def evaluation_contraction_derivativeType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    (B : SmoothVectorBundle S r ι E) (D : DualBundle B) (C : Connection B),
    letI := D.space.topology
    ∀ (K : Connection D.space.bundle), DualRule C D K →
    ∀ (T : TensorBundle D.space.bundle B),
    letI := T.space.topology
    ∀ (N : Connection T.space.bundle), TensorRule K C T N →
    ∀ (X : Field S) (s : Section T.space.bundle) (p : M),
      scalarDerivative S (fun q => evaluationContraction (s.val q)) p (X.val p) =
        evaluationContraction ((N.cov X s).val p)

end P202Specs.Geometry.InducedConnections

namespace P202Specs.Geometry.InducedConnections
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.BundleData SmoothManifolds.FrameData
  SmoothManifolds.BundleOperationsData P202.ConnectionData P202.InducedConnectionData
universe u v w z t

/-- The pullback of the dual is canonically a dual-bundle realization of the
pullback; its pulled-back connection satisfies the dual rule on arbitrary fields
along the map. Every input connection is characterized by the original rules. -/
def dual_pullback_compatibilityType : Prop :=
  ∀ {n m r : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    (B : SmoothVectorBundle S r ι E) (C : Connection B) (D : DualBundle B)
    (F : N → M) (hF : IsSmoothMap T S F) (P : PullbackBundle B T F),
    letI := D.space.topology
    ∀ (Q : PullbackBundle D.space.bundle T F),
    letI := P.space.topology
    letI := Q.space.topology
    ∀ (CP : Connection P.space.bundle) (CD : Connection D.space.bundle)
      (CQ : Connection Q.space.bundle),
      P202.PullbackData.IsPullback B C F hF P CP → DualRule C D CD →
      P202.PullbackData.IsPullback D.space.bundle CD F hF Q CQ →
      (∃ R : DualBundle P.space.bundle, R.space = Q.space) ∧
      ∀ (X : Field T) (lam : Section Q.space.bundle) (s : Section P.space.bundle) (q : N),
        ((CQ.cov X lam).val q) (s.val q) =
          scalarDerivative T (fun z => lam.val z (s.val z)) q (X.val q) -
            lam.val q ((CP.cov X s).val q)

/-- Pullback preserves the actual tensor-bundle construction and its induced
connection product rule for arbitrary smooth fields along the map. -/
def tensor_pullback_compatibilityType.{u₁,v₁,t₁,w₁,z₁} : Prop :=
  ∀ {n m r k : ℕ} {a b : ModelKind} {M N : Type u₁}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    {ι : Type v₁} {κ : Type t₁} {E : M → Type w₁} {G : M → Type z₁}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [∀ p, AddCommGroup (G p)] [∀ p, Module ℝ (G p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean k) G)]
    (B : SmoothVectorBundle S r ι E) (A : SmoothVectorBundle S k κ G)
    (C : Connection B) (K : Connection A) (U : TensorBundle B A)
    (F : N → M) (hF : IsSmoothMap T S F) (P : PullbackBundle B T F) (H : PullbackBundle A T F),
    letI := U.space.topology
    ∀ (Q : PullbackBundle U.space.bundle T F),
    letI := P.space.topology
    letI := H.space.topology
    letI := Q.space.topology
    ∀ (CP : Connection P.space.bundle) (KP : Connection H.space.bundle)
      (CU : Connection U.space.bundle) (CQ : Connection Q.space.bundle),
      P202.PullbackData.IsPullback B C F hF P CP →
      P202.PullbackData.IsPullback A K F hF H KP → TensorRule C K U CU →
      P202.PullbackData.IsPullback U.space.bundle CU F hF Q CQ →
      (∃ R : TensorBundle P.space.bundle H.space.bundle, R.space = Q.space) ∧
      ∀ (X : Field T) (s : Section P.space.bundle) (u : Section H.space.bundle)
        (v : Section Q.space.bundle),
        (∀ q, v.val q = TensorProduct.tmul ℝ (s.val q) (u.val q)) →
        ∀ q, (CQ.cov X v).val q =
          TensorProduct.tmul ℝ ((CP.cov X s).val q) (u.val q) +
            TensorProduct.tmul ℝ (s.val q) ((KP.cov X u).val q)
end P202Specs.Geometry.InducedConnections

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace P202.InducedConnectionData
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
 SmoothManifolds.TangentData SmoothManifolds.BundleData SmoothManifolds.FrameData
 SmoothManifolds.BundleOperationsData SmoothManifolds.SectionExtensionData P202.ConnectionData
open Set Filter
open scoped Topology
universe u v w
structure RealVectorSpace where
 Carrier : Type w
 addCommGroup : AddCommGroup Carrier
 module : @Module ℝ Carrier _ addCommGroup.toAddCommMonoid
attribute [instance] RealVectorSpace.addCommGroup RealVectorSpace.module
variable {M : Type u} (E : M → Type w)
 [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
noncomputable def mixedSpace : List Bool → M → RealVectorSpace.{w}
 | [], p => ⟨⋀[ℝ]^0 (E p), inferInstance, inferInstance⟩
 | false :: l, p => ⟨TensorProduct ℝ (E p) (mixedSpace l p).Carrier,
     inferInstance, inferInstance⟩
 | true :: l, p => ⟨TensorProduct ℝ (Module.Dual ℝ (E p)) (mixedSpace l p).Carrier,
     inferInstance, inferInstance⟩
abbrev MixedFiber (l : List Bool) (p : M) := (mixedSpace E l p).Carrier
noncomputable instance mixedFiberAdd (l : List Bool) (p : M) : AddCommGroup (MixedFiber E l p) :=
 (mixedSpace E l p).addCommGroup
noncomputable instance mixedFiberModule (l : List Bool) (p : M) : Module ℝ (MixedFiber E l p) :=
 (mixedSpace E l p).module
def mixedRank (r : ℕ) : List Bool → ℕ
 | [] => r.choose 0
 | _ :: l => r * mixedRank r l
def MixedIndex (ι : Type v) : List Bool → Type v
 | [] => ι
 | _ :: l => ι × MixedIndex ι l
variable {n r : ℕ} {a : ModelKind} [TopologicalSpace M]
 {S : SmoothManifold n a M} {ι : Type v}
noncomputable abbrev MixedBundleSpace (l : List Bool) :=
 BundleSpace S (mixedRank r l) (MixedIndex ι l) (MixedFiber E l)
end P202.InducedConnectionData
namespace P202.InducedConnectionData
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
 SmoothManifolds.TangentData SmoothManifolds.BundleData SmoothManifolds.FrameData
 SmoothManifolds.BundleOperationsData SmoothManifolds.SectionExtensionData P202.ConnectionData
universe u v w
variable {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
 {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
 [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
 [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
 (B : SmoothVectorBundle S r ι E)
noncomputable def mixedUnitBundle : ExteriorBundle B 0 :=
 Classical.choice (SmoothManifolds.BundleOperations.exists_exterior B 0)
noncomputable def mixedDualBundle : DualBundle B :=
 Classical.choice (SmoothManifolds.BundleOperations.exists_dual B)
noncomputable def mixedBundle : (l : List Bool) →
 BundleSpace S (mixedRank r l) (MixedIndex ι l) (MixedFiber E l)
 | [] => (mixedUnitBundle B).space
 | false :: l => by
   let U := mixedBundle l
   letI := U.topology
   exact (Classical.choice (SmoothManifolds.BundleOperations.exists_tensor B U.bundle)).space
 | true :: l => by
   let D := mixedDualBundle B
   letI := D.space.topology
   let U := mixedBundle l
   letI := U.topology
   exact (Classical.choice (SmoothManifolds.BundleOperations.exists_tensor D.space.bundle U.bundle)).space
noncomputable def mixedPrimalStep (l : List Bool) :
 letI := (mixedBundle B l).topology
 TensorBundle B (mixedBundle B l).bundle := by
 letI := (mixedBundle B l).topology
 exact Classical.choice (SmoothManifolds.BundleOperations.exists_tensor B (mixedBundle B l).bundle)
noncomputable def mixedDualStep (l : List Bool) :
 letI := (mixedDualBundle B).space.topology
 letI := (mixedBundle B l).topology
 TensorBundle (mixedDualBundle B).space.bundle (mixedBundle B l).bundle := by
 letI := (mixedDualBundle B).space.topology
 letI := (mixedBundle B l).topology
 exact Classical.choice (SmoothManifolds.BundleOperations.exists_tensor
   (mixedDualBundle B).space.bundle (mixedBundle B l).bundle)
end P202.InducedConnectionData

namespace P202.InducedConnectionData
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
 SmoothManifolds.TangentData SmoothManifolds.BundleData SmoothManifolds.FrameData
 SmoothManifolds.BundleOperationsData SmoothManifolds.SectionExtensionData P202.ConnectionData
open Set
universe u v w
variable {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
 {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
 [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
 [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
 (B : SmoothVectorBundle S r ι E)
noncomputable def mixedUnitTrivialization :
 letI := (mixedUnitBundle B).space.topology
 SmoothTrivialization (mixedUnitBundle B).space.bundle := by
 letI := (mixedUnitBundle B).space.topology
 exact Classical.choose (SmoothManifolds.BundleOperations.exterior_zero B (mixedUnitBundle B))
noncomputable def mixedUnitFrame :
 letI := (mixedUnitBundle B).space.topology
 LocalFrame (mixedUnitBundle B).space.bundle univ isOpen_univ := by
 letI := (mixedUnitBundle B).space.topology
 exact Classical.choose (SmoothManifolds.Frames.trivialization_globalFrame
   (mixedUnitBundle B).space.bundle (mixedUnitTrivialization B))
/-- Degree zero is the scalar bundle through its canonical algebraic
identification, and its covariant derivative is the intrinsic scalar derivative. -/
def MixedUnitRule :
 letI := (mixedBundle B []).topology
 Connection (mixedBundle B []).bundle → Prop := by
 letI := (mixedBundle B []).topology
 exact fun C => ∀ (X : Field S) (s : Section (mixedBundle B []).bundle) (p : M),
   exteriorPower.zeroEquiv ℝ (E p) ((C.cov X s).val p) =
     scalarDerivative S (fun q => exteriorPower.zeroEquiv ℝ (E q) (s.val q)) p (X.val p)
/-- Induced connection on every ordered finite word of primal and dual factors.
`false` denotes a primal slot and `true` a dual slot. The displayed rules give
all recursive product laws, including the scalar unit. -/
def MixedFamilyRule (C : Connection B) :
 letI := (mixedDualBundle B).space.topology
 Connection (mixedDualBundle B).space.bundle →
 ((l : List Bool) → letI := (mixedBundle B l).topology;
   Connection (mixedBundle B l).bundle) → Prop := by
 letI := (mixedDualBundle B).space.topology
 exact fun D K => DualRule C (mixedDualBundle B) D ∧ MixedUnitRule B (K []) ∧
   (∀ l, letI := (mixedBundle B l).topology;
     letI := (mixedBundle B (false :: l)).topology;
     TensorRule C (K l) (mixedPrimalStep B l) (K (false :: l))) ∧
   (∀ l, letI := (mixedBundle B l).topology;
     letI := (mixedBundle B (true :: l)).topology;
     TensorRule D (K l) (mixedDualStep B l) (K (true :: l)))
/-- Canonical collapse of the trailing scalar unit on a single primal slot. -/
noncomputable def mixedPrimalEquiv (p : M) : MixedFiber E [false] p ≃ₗ[ℝ] E p :=
 (TensorProduct.congr (LinearEquiv.refl ℝ (E p)) (exteriorPower.zeroEquiv ℝ (E p))).trans
   (TensorProduct.rid ℝ (E p))
/-- Canonical collapse of the trailing scalar unit on a single dual slot. -/
noncomputable def mixedDualEquiv (p : M) :
 MixedFiber E [true] p ≃ₗ[ℝ] Module.Dual ℝ (E p) :=
 (TensorProduct.congr (LinearEquiv.refl ℝ (Module.Dual ℝ (E p)))
   (exteriorPower.zeroEquiv ℝ (E p))).trans (TensorProduct.rid ℝ (Module.Dual ℝ (E p)))
end P202.InducedConnectionData
namespace P202Specs.Geometry.InducedConnections
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
 SmoothManifolds.BundleData SmoothManifolds.BundleOperationsData
 P202.ConnectionData P202.InducedConnectionData
universe u v w
def mixed_existsType : Prop :=
 ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
 {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
 [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
 [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
 (B : SmoothVectorBundle S r ι E) (C : Connection B),
 letI := (mixedDualBundle B).space.topology
 ∃ D : Connection (mixedDualBundle B).space.bundle,
 ∃ K : (l : List Bool) → letI := (mixedBundle B l).topology;
   Connection (mixedBundle B l).bundle,
 MixedFamilyRule B C D K
end P202Specs.Geometry.InducedConnections

namespace P202.InducedConnectionData
/-- Evaluation on one dual/primal pair, retaining every other tensor factor. -/
noncomputable def spectatorContraction {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] :
    TensorProduct ℝ (TensorProduct ℝ (Module.Dual ℝ V) V) W →ₗ[ℝ] W :=
  TensorProduct.lift ((LinearMap.lsmul ℝ W).comp evaluationContraction)
end P202.InducedConnectionData

namespace P202Specs.Geometry.InducedConnections
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
 SmoothManifolds.TangentData SmoothManifolds.BundleData SmoothManifolds.BundleOperationsData
 P202.ConnectionData P202.InducedConnectionData
open Set Filter
open scoped Topology
universe u v w
open P202.CurveConnectionData

def curve_dual_contractionType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    (B : SmoothVectorBundle S r ι E)
    (C : Connection B) (D : DualBundle B),
    letI := D.space.topology
    ∀ (K : Connection D.space.bundle), DualRule C D K →
    ∀ {c : ℝ → M} {lam : (s : ℝ) → Module.Dual ℝ (E (c s))}
      {f : (s : ℝ) → E (c s)} {J : Set ℝ} {t : ℝ}
      (ht : t ∈ J) (hJ : UniqueDiffWithinAt ℝ J t)
      {DL : Module.Dual ℝ (E (c t))} {DF : E (c t)},
      HasCovariantDerivativeWithinAt K c lam J t DL →
      HasCovariantDerivativeWithinAt C c f J t DF →
      HasDerivWithinAt (fun s => lam s (f s)) (DL (f t) + lam t DF) J t

def curve_dual_contraction_c1Type : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    (B : SmoothVectorBundle S r ι E)
    (C : Connection B) (D : DualBundle B),
    letI := D.space.topology
    ∀ (K : Connection D.space.bundle), DualRule C D K →
    ∀ {c : ℝ → M} {lam : (s : ℝ) → Module.Dual ℝ (E (c s))}
      {f : (s : ℝ) → E (c s)} {J : Set ℝ} {t : ℝ}
      (ht : t ∈ J) (hJ : UniqueDiffWithinAt ℝ J t),
      P202.CurveData.CoordinateC1On S c J → ContinuousOn c J →
      C1FieldOn (B := D.space.bundle) c lam J → C1FieldOn (B := B) c f J →
      HasDerivWithinAt (fun s => lam s (f s))
        ((covariantDerivativeWithin K c lam J t) (f t) +
          lam t (covariantDerivativeWithin C c f J t)) J t

def curve_dual_contraction_atType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    (B : SmoothVectorBundle S r ι E)
    (C : Connection B) (D : DualBundle B),
    letI := D.space.topology
    ∀ (K : Connection D.space.bundle), DualRule C D K →
    ∀ {c : ℝ → M} {lam : (s : ℝ) → Module.Dual ℝ (E (c s))}
      {f : (s : ℝ) → E (c s)} {t : ℝ}
      {DL : Module.Dual ℝ (E (c t))} {DF : E (c t)},
      HasCovariantDerivativeAt K c lam t DL →
      HasCovariantDerivativeAt C c f t DF →
      HasDerivAt (fun s => lam s (f s)) (DL (f t) + lam t DF) t

end P202Specs.Geometry.InducedConnections

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace P202.InducedConnectionData
universe u v w
/-- Deleting one specified occurrence of a slot, preserving all other slots. -/
inductive TensorSlot (b : Bool) : List Bool → List Bool → Type
 | here (l : List Bool) : TensorSlot b (b :: l) l
 | there (a : Bool) {l k : List Bool} : TensorSlot b l k → TensorSlot b (a :: l) (a :: k)
variable {M : Type u} (E : M → Type w)
 [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
noncomputable def tensorAtom (b : Bool) (p : M) : RealVectorSpace.{w} :=
 match b with
 | false => ⟨E p, inferInstance, inferInstance⟩
 | true => ⟨Module.Dual ℝ (E p), inferInstance, inferInstance⟩
abbrev TensorAtom (b : Bool) (p : M) := (tensorAtom E b p).Carrier
noncomputable instance tensorAtomAdd (b : Bool) (p : M) : AddCommGroup (TensorAtom E b p) :=
 (tensorAtom E b p).addCommGroup
noncomputable instance tensorAtomModule (b : Bool) (p : M) : Module ℝ (TensorAtom E b p) :=
 (tensorAtom E b p).module
/-- Move a specified factor to the front by canonical associators and flips. -/
noncomputable def tensorSlotEquiv {b : Bool} {l k : List Bool}
 (h : TensorSlot b l k) (p : M) :
 MixedFiber E l p ≃ₗ[ℝ] TensorProduct ℝ (TensorAtom E b p) (MixedFiber E k p) := by
 induction h with
 | here l => cases b <;> exact LinearEquiv.refl ℝ _
 | @there a l k h ih =>
   have e := TensorProduct.congr (LinearEquiv.refl ℝ (TensorAtom E a p)) ih
   have f := TensorProduct.leftComm ℝ (TensorAtom E a p) (TensorAtom E b p) (MixedFiber E k p)
   cases a <;> cases b
   all_goals exact e.trans f
/-- Every occurrence specified by a pre and suff is selectable. -/
def tensorSlotAt (b : Bool) (pre suff : List Bool) :
 TensorSlot b (pre ++ b :: suff) (pre ++ suff) :=
 match pre with
 | [] => .here suff
 | a :: rest => .there a (tensorSlotAt b rest suff)
/-- A pure tensor's input values, with an actual degree-zero value at the end. -/
noncomputable def TensorArguments : List Bool → M → Type w
 | [], p => ⋀[ℝ]^0 (E p)
 | b :: l, p => TensorAtom E b p × TensorArguments l p
noncomputable def pureMixedTensor : (l : List Bool) → (p : M) →
 TensorArguments E l p → MixedFiber E l p
 | [], _, v => v
 | false :: l, p, v => TensorProduct.tmul ℝ v.1 (pureMixedTensor l p v.2)
 | true :: l, p, v => TensorProduct.tmul ℝ v.1 (pureMixedTensor l p v.2)
noncomputable def tensorSlotArguments {b : Bool} {l k : List Bool}
 (h : TensorSlot b l k) (p : M) :
 TensorArguments E l p → TensorAtom E b p × TensorArguments E k p := by
 induction h with
 | here l => exact id
 | @there a l k h ih => exact fun v =>
   let q := ih v.2
   (q.1, (v.1, q.2))
/-- Natural contraction at any selected dual slot and any selected primal slot.
The output keeps every uncontracted slot in its original order. -/
noncomputable def tensorContractSlots {l k j : List Bool}
 (hd : TensorSlot true l k) (hp : TensorSlot false k j) (p : M) :
 MixedFiber E l p →ₗ[ℝ] MixedFiber E j p :=
 let e := (tensorSlotEquiv E hd p).trans
   (TensorProduct.congr (LinearEquiv.refl ℝ (Module.Dual ℝ (E p)))
     (tensorSlotEquiv E hp p))
 (TensorProduct.lid ℝ (MixedFiber E j p)).toLinearMap.comp
   ((TensorProduct.map evaluationContraction (LinearMap.id : MixedFiber E j p →ₗ[ℝ] MixedFiber E j p)).comp
     ((TensorProduct.assoc ℝ (Module.Dual ℝ (E p)) (E p) (MixedFiber E j p)).symm.toLinearMap.comp
       e.toLinearMap))
end P202.InducedConnectionData


namespace P202Specs.Geometry.InducedConnections
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
 SmoothManifolds.TangentData SmoothManifolds.BundleData SmoothManifolds.BundleOperationsData
 P202.ConnectionData P202.InducedConnectionData
open Set Filter
open scoped Topology
universe u v w z t
open P202.CurveConnectionData
open P202.CurveConnectionData

def curve_tensor_productType : Prop :=
  ∀ {n r k : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {κ : Type t}
    {E : M → Type w} {F : M → Type z}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [∀ p, AddCommGroup (F p)] [∀ p, Module ℝ (F p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean k) F)]
    (B : SmoothVectorBundle S r ι E) (A : SmoothVectorBundle S k κ F)
    (C : Connection B) (K : Connection A) (T : TensorBundle B A),
    letI := T.space.topology
    ∀ (N : Connection T.space.bundle), TensorRule C K T N →
    ∀ {c : ℝ → M} {f : (s : ℝ) → E (c s)} {g : (s : ℝ) → F (c s)}
      {J : Set ℝ} {t : ℝ} (ht : t ∈ J) (hJ : UniqueDiffWithinAt ℝ J t)
      {DF : E (c t)} {DG : F (c t)},
      HasCovariantDerivativeWithinAt C c f J t DF →
      HasCovariantDerivativeWithinAt K c g J t DG →
      HasCovariantDerivativeWithinAt N c
        (fun s => TensorProduct.tmul ℝ (f s) (g s)) J t
        (TensorProduct.tmul ℝ DF (g t) + TensorProduct.tmul ℝ (f t) DG)

def curve_tensor_product_c1Type : Prop :=
  ∀ {n r k : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {κ : Type t}
    {E : M → Type w} {F : M → Type z}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [∀ p, AddCommGroup (F p)] [∀ p, Module ℝ (F p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean k) F)]
    (B : SmoothVectorBundle S r ι E) (A : SmoothVectorBundle S k κ F)
    (C : Connection B) (K : Connection A) (T : TensorBundle B A),
    letI := T.space.topology
    ∀ (N : Connection T.space.bundle), TensorRule C K T N →
    ∀ {c : ℝ → M} {f : (s : ℝ) → E (c s)} {g : (s : ℝ) → F (c s)}
      {J : Set ℝ} {t : ℝ} (ht : t ∈ J) (hJ : UniqueDiffWithinAt ℝ J t),
      P202.CurveData.CoordinateC1On S c J → ContinuousOn c J →
      C1FieldOn (B := B) c f J → C1FieldOn (B := A) c g J →
      covariantDerivativeWithin N c (fun s => TensorProduct.tmul ℝ (f s) (g s)) J t =
        TensorProduct.tmul ℝ (covariantDerivativeWithin C c f J t) (g t) +
          TensorProduct.tmul ℝ (f t) (covariantDerivativeWithin K c g J t)

def curve_tensor_product_atType : Prop :=
  ∀ {n r k : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {κ : Type t}
    {E : M → Type w} {F : M → Type z}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [∀ p, AddCommGroup (F p)] [∀ p, Module ℝ (F p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean k) F)]
    (B : SmoothVectorBundle S r ι E) (A : SmoothVectorBundle S k κ F)
    (C : Connection B) (K : Connection A) (T : TensorBundle B A),
    letI := T.space.topology
    ∀ (N : Connection T.space.bundle), TensorRule C K T N →
    ∀ {c : ℝ → M} {f : (s : ℝ) → E (c s)} {g : (s : ℝ) → F (c s)} {t : ℝ}
      {DF : E (c t)} {DG : F (c t)},
      HasCovariantDerivativeAt C c f t DF → HasCovariantDerivativeAt K c g t DG →
      HasCovariantDerivativeAt N c (fun s => TensorProduct.tmul ℝ (f s) (g s)) t
        (TensorProduct.tmul ℝ DF (g t) + TensorProduct.tmul ℝ (f t) DG)

end P202Specs.Geometry.InducedConnections

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
namespace P202.InducedConnectionData
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
 SmoothManifolds.TangentData SmoothManifolds.BundleData SmoothManifolds.FrameData
 SmoothManifolds.BundleOperationsData SmoothManifolds.SectionExtensionData P202.ConnectionData
universe u v w
variable {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
 {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
 [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
 [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
 (B : SmoothVectorBundle S r ι E)
noncomputable def tensorAtomBundle : (b : Bool) → BundleSpace S r ι (TensorAtom E b)
 | false => by
   change BundleSpace S r ι E
   exact ⟨inferInstance, B⟩
 | true => (mixedDualBundle B).space
noncomputable def mixedAtomStep (b : Bool) (l : List Bool) :
 letI := (tensorAtomBundle B b).topology
 letI := (mixedBundle B l).topology
 TensorBundle (tensorAtomBundle B b).bundle (mixedBundle B l).bundle := by
 cases b
 · exact mixedPrimalStep B l
 · exact mixedDualStep B l
end P202.InducedConnectionData

namespace P202.InducedConnectionData
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
 SmoothManifolds.TangentData SmoothManifolds.BundleData SmoothManifolds.BundleOperationsData
 SmoothManifolds.SectionExtensionData P202.ConnectionData P202.CurveConnectionData
open Set
universe u v w
variable {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
 {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
 [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
 [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
 (B : SmoothVectorBundle S r ι E)

abbrev MixedConnections := (l : List Bool) →
 letI := (mixedBundle B l).topology; Connection (mixedBundle B l).bundle

/-- Every dual/primal slot pair contracts smoothly and commutes with the
connection on all sections. Slot selection retains the order of other slots. -/
def MixedContractionRule (K : MixedConnections B) : Prop :=
 ∀ {l k j : List Bool} (hd : TensorSlot true l k) (hp : TensorSlot false k j),
 letI := (mixedBundle B l).topology
 letI := (mixedBundle B j).topology
 (∀ s : Section (mixedBundle B l).bundle,
   SmoothSection (mixedBundle B j).bundle
     (fun p => tensorContractSlots E hd hp p (s.val p))) ∧
 (∀ (X : Field S) (s : Section (mixedBundle B l).bundle)
    (u : Section (mixedBundle B j).bundle),
   (∀ p, u.val p = tensorContractSlots E hd hp p (s.val p)) →
   ∀ p, ((K j).cov X u).val p =
     tensorContractSlots E hd hp p (((K l).cov X s).val p))

/-- All natural contractions carry to arbitrary smooth fields along any smooth
map, on the actual pullback bundles with their pullback connections. -/
def MixedMapContractionRule (K : MixedConnections B) : Prop :=
 ∀ {l k j : List Bool} (hd : TensorSlot true l k) (hp : TensorSlot false k j),
 letI := (mixedBundle B l).topology
 letI := (mixedBundle B j).topology
 ∀ {m : ℕ} {b : ModelKind} {N : Type u} [TopologicalSpace N]
   (T : SmoothManifold m b N) (F : N → M) (hF : IsSmoothMap T S F)
   (P : PullbackBundle (mixedBundle B l).bundle T F)
   (Q : PullbackBundle (mixedBundle B j).bundle T F),
 letI := P.space.topology
 letI := Q.space.topology
 (∀ s : Section P.space.bundle, SmoothSection Q.space.bundle
   (fun q => tensorContractSlots E hd hp (F q) (s.val q))) ∧
 (∀ (CP : Connection P.space.bundle) (CQ : Connection Q.space.bundle),
   P202.PullbackData.IsPullback (mixedBundle B l).bundle (K l) F hF P CP →
   P202.PullbackData.IsPullback (mixedBundle B j).bundle (K j) F hF Q CQ →
   ∀ (X : Field T) (s : Section P.space.bundle) (u : Section Q.space.bundle),
   (∀ q, u.val q = tensorContractSlots E hd hp (F q) (s.val q)) →
   ∀ q, (CQ.cov X u).val q = tensorContractSlots E hd hp (F q) ((CP.cov X s).val q))

/-- All-slot contractions commute with genuine within covariant derivatives
of fields along C¹ curves. The arbitrary within germ includes ordinary and
one-sided differentiation, without a nonzero-velocity requirement. -/
def MixedCurveContractionRule (K : MixedConnections B) : Prop :=
 ∀ {l k j : List Bool} (hd : TensorSlot true l k) (hp : TensorSlot false k j),
 letI := (mixedBundle B l).topology
 letI := (mixedBundle B j).topology
 ∀ {c : ℝ → M} {f : (s : ℝ) → MixedFiber E l (c s)} {J : Set ℝ} {t : ℝ}
   (ht : t ∈ J) (hJ : UniqueDiffWithinAt ℝ J t) {D : MixedFiber E l (c t)},
 HasCovariantDerivativeWithinAt (K l) c f J t D →
 HasCovariantDerivativeWithinAt (K j) c
   (fun s => tensorContractSlots E hd hp (c s) (f s)) J t
     (tensorContractSlots E hd hp (c t) D) ∧
 covariantDerivativeWithin (K j) c
   (fun s => tensorContractSlots E hd hp (c s) (f s)) J t =
     tensorContractSlots E hd hp (c t) (covariantDerivativeWithin (K l) c f J t)
end P202.InducedConnectionData

namespace P202Specs.Geometry.InducedConnections
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.BundleData
 P202.ConnectionData P202.InducedConnectionData
universe u v w
/-- Full finite mixed tensor calculus, including all contractions and their
pullback and C¹-curve versions, for every original bundle connection. -/
def mixed_calculus_existsType : Prop :=
 ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
 {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
 [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
 [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
 (B : SmoothVectorBundle S r ι E) (C : Connection B),
 letI := (mixedDualBundle B).space.topology
 ∃ D : Connection (mixedDualBundle B).space.bundle,
 ∃ K : MixedConnections B,
 MixedFamilyRule B C D K ∧ MixedContractionRule B K ∧
   MixedMapContractionRule B K ∧ MixedCurveContractionRule B K
end P202Specs.Geometry.InducedConnections

namespace P202Specs.Geometry.InducedConnections
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
 SmoothManifolds.BundleData P202.ConnectionData
universe u v w z t
/-- The tensor product derivative respects the C∞-balanced relation. Both
scalar Leibniz terms are retained and coincide across the relation. -/
def balanced_product_derivativeType.{u₁,v₁,t₁,w₁,z₁} : Prop :=
 ∀ {n r k : ℕ} {a : ModelKind} {M : Type u₁} [TopologicalSpace M]
 {S : SmoothManifold n a M} {ι : Type v₁} {κ : Type t₁}
 {E : M → Type w₁} {F : M → Type z₁}
 [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
 [∀ p, AddCommGroup (F p)] [∀ p, Module ℝ (F p)]
 [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
 [TopologicalSpace (Bundle.TotalSpace (Euclidean k) F)]
 (B : SmoothVectorBundle S r ι E) (A : SmoothVectorBundle S k κ F)
 (C : Connection B) (K : Connection A) (X : Field S)
 (f : GlobalSmooth S) (s : Section B) (u : Section A) (p : M),
 TensorProduct.tmul ℝ ((C.cov X (mulSection f s)).val p) (u.val p) +
   TensorProduct.tmul ℝ ((mulSection f s).val p) ((K.cov X u).val p) =
 TensorProduct.tmul ℝ ((C.cov X s).val p) ((mulSection f u).val p) +
   TensorProduct.tmul ℝ (s.val p) ((K.cov X (mulSection f u)).val p)
end P202Specs.Geometry.InducedConnections

set_option autoImplicit false
namespace P202.InducedConnectionData
universe u w
variable {M : Type u} (E : M → Type w)
 [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
/-- The ordinary right-associated mixed tensor word, with a universe-lifted
real scalar as its degree-zero unit. `ULift.moduleEquiv` canonically identifies
this unit with the actual real scalars; no algebraic choice is involved. -/
noncomputable def scalarMixedSpace : List Bool → M → RealVectorSpace.{w}
 | [], _ => ⟨ULift.{w} ℝ, inferInstance, inferInstance⟩
 | false :: l, p => ⟨TensorProduct ℝ (E p) (scalarMixedSpace l p).Carrier,
     inferInstance, inferInstance⟩
 | true :: l, p => ⟨TensorProduct ℝ (Module.Dual ℝ (E p)) (scalarMixedSpace l p).Carrier,
     inferInstance, inferInstance⟩
abbrev ScalarMixedFiber (l : List Bool) (p : M) := (scalarMixedSpace E l p).Carrier
noncomputable instance scalarMixedAdd (l : List Bool) (p : M) :
 AddCommGroup (ScalarMixedFiber E l p) := (scalarMixedSpace E l p).addCommGroup
noncomputable instance scalarMixedModule (l : List Bool) (p : M) :
 Module ℝ (ScalarMixedFiber E l p) := (scalarMixedSpace E l p).module
/-- The canonical scalar interpretation of the degree-zero word. -/
noncomputable def scalarMixedUnitEquiv (p : M) : ScalarMixedFiber E [] p ≃ₗ[ℝ] ℝ :=
 ULift.moduleEquiv
/-- Canonical identification of the actual mixed fibers with the scalar-unit
recursive convention. Every primal and dual factor is kept unchanged; only
the terminal degree-zero exterior fiber is identified with the scalars. -/
noncomputable def mixedScalarTailEquiv : (l : List Bool) → (p : M) →
 MixedFiber E l p ≃ₗ[ℝ] ScalarMixedFiber E l p
 | [], p => (exteriorPower.zeroEquiv ℝ (E p)).trans ULift.moduleEquiv.symm
 | false :: l, p => TensorProduct.congr (LinearEquiv.refl ℝ (E p)) (mixedScalarTailEquiv l p)
 | true :: l, p => TensorProduct.congr (LinearEquiv.refl ℝ (Module.Dual ℝ (E p)))
     (mixedScalarTailEquiv l p)
@[simp] theorem mixedScalarTailEquiv_nil (p : M) :
 (mixedScalarTailEquiv E [] p).trans (scalarMixedUnitEquiv E p) =
   exteriorPower.zeroEquiv ℝ (E p) := by
 ext x
 rfl
@[simp] theorem mixedScalarTailEquiv_primal (l : List Bool) (p : M)
 (x : E p) (y : MixedFiber E l p) :
 mixedScalarTailEquiv E (false :: l) p (TensorProduct.tmul ℝ x y) =
   TensorProduct.tmul ℝ x (mixedScalarTailEquiv E l p y) := by
 exact TensorProduct.congr_tmul _ _ _ _
@[simp] theorem mixedScalarTailEquiv_dual (l : List Bool) (p : M)
 (x : Module.Dual ℝ (E p)) (y : MixedFiber E l p) :
 mixedScalarTailEquiv E (true :: l) p (TensorProduct.tmul ℝ x y) =
   TensorProduct.tmul ℝ x (mixedScalarTailEquiv E l p y) := by
 exact TensorProduct.congr_tmul _ _ _ _
end P202.InducedConnectionData

namespace P202Specs.Geometry.InducedConnections
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.BundleData
 SmoothManifolds.BundleOperationsData P202.InducedConnectionData
universe u v w
/-- The canonical actual mixed tensor-bundle construction, independently of
any connection or its proof of existence. -/
def mixedTensorBundleType :=
 ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
 {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
 [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
 [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
 (B : SmoothVectorBundle S r ι E) (l : List Bool),
 BundleSpace S (mixedRank r l) (MixedIndex ι l) (MixedFiber E l)

noncomputable def mixedTensorBundleValue : mixedTensorBundleType.{u,v,w} := @mixedBundle

/-- The actual all-slot contraction, with its independently fixed value. -/
def contractionType :=
 ∀ {M : Type u} (E : M → Type w)
 [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
 {l k j : List Bool} (hd : TensorSlot true l k) (hp : TensorSlot false k j) (p : M),
 MixedFiber E l p →ₗ[ℝ] MixedFiber E j p

noncomputable def contractionValue : contractionType.{u,w} := @tensorContractSlots
end P202Specs.Geometry.InducedConnections
