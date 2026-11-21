import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch07.ExteriorAlgebra
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch05.BundleOperations
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch05.Covectors

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
noncomputable section

namespace SmoothManifolds.ExteriorAlgebraResults
open ModelData AtlasData MapData TangentData BundleData BundleOperationsData
  CovectorData FrameData ExteriorData Module Set Filter
open scoped Topology
universe u v w

private theorem alternating_interpretation_proof :
    Specs.SmoothManifolds.Ch07.ExteriorAlgebra.alternating_interpretationType.{u} := by
  intro V _ _ _ k
  exact exteriorPower.alternatingMapLinearEquiv.symm.bijective.comp
    (exteriorPower.bijective_pairingDual ℝ V k)

private theorem determinant_normalization_proof :
    Specs.SmoothManifolds.Ch07.ExteriorAlgebra.determinant_normalizationType.{u} := by
  intro V _ _ k α v
  change exteriorPower.pairingDual ℝ V k (exteriorPower.ιMulti ℝ k α)
    (exteriorPower.ιMulti ℝ k v) = _
  rw [exteriorPower.pairingDual_ιMulti_ιMulti, ← Matrix.det_transpose]
  rfl

private theorem increasing_basis_proof :
    Specs.SmoothManifolds.Ch07.ExteriorAlgebra.increasing_basisType.{u} := by
  intro V _ _ n k b
  exact ⟨b.exteriorPower k, fun I => exteriorPower.basis_apply ℝ k b I⟩

private theorem wedge_decomposable_proof :
    Specs.SmoothManifolds.Ch07.ExteriorAlgebra.wedge_decomposableType.{u} := by
  intro V _ _ k l α β
  apply Subtype.ext
  exact ExteriorAlgebra.ιMulti_mul_ιMulti α β

private theorem wedge_assoc_proof :
    Specs.SmoothManifolds.Ch07.ExteriorAlgebra.wedge_assocType.{u} := by
  intro V _ _ k l m α β γ
  exact mul_assoc α.val β.val γ.val

/-- Graded commutativity, obtained by bilinear extension from decomposables. -/
theorem homogeneous_anticomm (V : Type u) [AddCommGroup V] [Module ℝ V]
    (k l : ℕ) (x : ⋀[ℝ]^k V) (y : ⋀[ℝ]^l V) :
    (x.val * y.val) = (-1 : ℝ)^(k*l) • (y.val * x.val) := by
  have hx : x.val ∈ Submodule.span ℝ (Set.range (ExteriorAlgebra.ιMulti ℝ k (M := V))) := by
    rw [ExteriorAlgebra.ιMulti_span_fixedDegree]; exact x.property
  have hy : y.val ∈ Submodule.span ℝ (Set.range (ExteriorAlgebra.ιMulti ℝ l (M := V))) := by
    rw [ExteriorAlgebra.ιMulti_span_fixedDegree]; exact y.property
  refine Submodule.span_induction₂
    (p := fun a b _ _ => a * b = (-1 : ℝ)^(k*l) • (b*a)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro a b ⟨v, rfl⟩ ⟨w, rfl⟩
    have hh := ExteriorAlgebra.ιMulti_mul_ιMulti_anticomm (R := ℝ) v w
    simpa only [Nat.mul_comm, Units.smul_def, Units.val_pow_eq_pow_val, Units.val_neg,
      Units.val_one, ← Int.cast_smul_eq_zsmul ℝ, Int.cast_pow, Int.cast_neg, Int.cast_one] using hh
  all_goals
    intros
    simp_all only [zero_mul, mul_zero, smul_zero, add_mul, mul_add, smul_add,
      mul_smul_comm, smul_mul_assoc]
  all_goals exact smul_comm _ _ _

private theorem wedge_comm_proof :
    Specs.SmoothManifolds.Ch07.ExteriorAlgebra.wedge_commType.{u} := by
  intro V _ _ k l α β
  exact homogeneous_anticomm (Module.Dual ℝ V) k l α β

private theorem degree_zero_proof :
    Specs.SmoothManifolds.Ch07.ExteriorAlgebra.degree_zeroType.{u} := by
  intro V _ _
  exact ⟨exteriorPower.zeroEquiv ℝ (Module.Dual ℝ V)⟩

private theorem above_dimension_proof :
    Specs.SmoothManifolds.Ch07.ExteriorAlgebra.above_dimensionType.{u} := by
  intro V _ _ _ k hk α
  have hdim : Module.finrank ℝ (Fiber V k) = 0 := by
    simp [Fiber, exteriorPower.finrank_eq, Subspace.dual_finrank_eq, Nat.choose_eq_zero_of_lt hk]
  exact (finrank_zero_iff_forall_zero.mp hdim) α

private theorem exists_formBundle_proof :
    Specs.SmoothManifolds.Ch07.ExteriorAlgebra.exists_formBundleType.{u} := by
  intro n a M _ S C k
  letI := (cotangentSpace C).topology
  exact BundleOperations.exists_exterior (cotangentSpace C).bundle k

/-- The algebraic dual basis of the coordinate tangent basis is exactly dx^i. -/
theorem coordinate_dualBasis {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (K : TangentBundleData.FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ c.source) (j : Fin n) :
    ((Pi.basisFun ℝ (Fin n)).map (K.equiv c hc p hp).symm).dualBasis j =
      coordinateCovector K c hc p hp j := by
  apply LinearMap.ext
  intro v
  simp [Module.Basis.coord_apply, coordinateCovector,
    Module.Basis.map_repr]

private theorem coefficient_expansion_proof :
    Specs.SmoothManifolds.Ch07.ExteriorAlgebra.coefficient_expansionType.{u} := by
  intro n a M _ S C k c hc ω p
  classical
  let b := ((Pi.basisFun ℝ (Fin n)).map
    (C.tangent.fiberCoordinates.equiv c hc p.val p.property).symm).dualBasis
  have hb (I : Index n k) :
      b.exteriorPower k I = exteriorPower.ιMulti ℝ k (fun j =>
        coordinateCovector C.tangent.fiberCoordinates c hc p.val p.property
          (Set.powersetCard.ofFinEmbEquiv.symm I j)) := by
    rw [exteriorPower.basis_apply]
    unfold exteriorPower.ιMulti_family
    congr 1
    funext j
    exact coordinate_dualBasis _ c hc p.val p.property _
  simpa only [ExteriorData.coefficients, ← hb] using ((b.exteriorPower k).sum_repr (ω p.val)).symm

private theorem coefficients_unique_proof :
    Specs.SmoothManifolds.Ch07.ExteriorAlgebra.coefficients_uniqueType.{u} := by
  intro n a M _ S C k c hc α β h p
  rw [coefficient_expansion_proof C k c hc α p, coefficient_expansion_proof C k c hc β p]
  simp only [h]


/-- Exterior bases are natural under linear equivalences. -/
theorem exteriorBasis_map {V : Type u} {W : Type v}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    {ι : Type w} [LinearOrder ι] (b : Basis ι ℝ V) (e : V ≃ₗ[ℝ] W) (k : ℕ) :
    (b.map e).exteriorPower k = (b.exteriorPower k).map (BundleOperations.exteriorEquiv k e) := by
  apply DFunLike.ext
  intro I
  simp [exteriorPower.basis_apply, exteriorPower.ιMulti_family, BundleOperations.exteriorEquiv,
    exteriorPower.map_apply_ιMulti]
  congr 1

section BundleCoordinates
variable {d r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold d a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E) {k : ℕ} (D : ExteriorBundle B k)

/-- The decomposable coordinate formula extends to every exterior vector. -/
theorem exterior_coordinates (i : ι) (p : M) (hp : p ∈ B.baseSet i)
    (x : ⋀[ℝ]^k (E p)) :
    letI := D.space.topology
    D.space.bundle.fiberCoordinates i p ((D.baseSet i).symm ▸ hp) x =
      D.modelEquiv (exteriorPower.map k (B.fiberCoordinates i p hp).toLinearMap x) := by
  letI := D.space.topology
  have h : (D.space.bundle.fiberCoordinates i p ((D.baseSet i).symm ▸ hp)).toLinearMap =
      D.modelEquiv.toLinearMap.comp (exteriorPower.map k (B.fiberCoordinates i p hp).toLinearMap) := by
    apply exteriorPower.linearMap_ext
    apply DFunLike.ext
    intro v
    simpa only [LinearMap.compAlternatingMap_apply, LinearEquiv.coe_coe,
      SmoothVectorBundle.fiberCoordinates_apply,
      LinearMap.comp_apply, exteriorPower.map_apply_ιMulti, Function.comp_def] using D.coordinates i p hp v
  exact LinearMap.congr_fun h x

end BundleCoordinates

/-- In cotangent coordinates, the ordered coframe is the dual of the intrinsic
coordinate tangent frame. This is the bridge from bundle coefficients to dx^I. -/
theorem cotangent_basis {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ c.source) :
    letI := (cotangentSpace C).topology
    ((Pi.basisFun ℝ (Fin n)).map
      (C.tangent.fiberCoordinates.equiv c hc p hp).symm).dualBasis =
    (Pi.basisFun ℝ (Fin n)).map
      ((cotangentSpace C).bundle.fiberCoordinates ⟨c, hc⟩ p
        ((Covectors.cotangent_baseSet C c hc).symm ▸ hp)).symm := by
  letI := (cotangentSpace C).topology
  apply DFunLike.ext
  intro j
  apply ((cotangentSpace C).bundle.fiberCoordinates ⟨c, hc⟩ p
    ((Covectors.cotangent_baseSet C c hc).symm ▸ hp)).injective
  rw [Module.Basis.map_apply, Pi.basisFun_apply, LinearEquiv.apply_symm_apply, coordinate_dualBasis]
  ext l
  rw [SmoothVectorBundle.fiberCoordinates_apply,
    Covectors.cotangent_coordinates C c hc p hp]
  simp [Module.Basis.map_apply, Covectors.coordinateCovector_apply, Pi.single_apply]

/-- A constant change of finite-dimensional linear coordinates preserves the
ambient-extension smoothness convention. -/
theorem vectorSmoothAt_equiv_iff {d : ℕ} {a : ModelKind} {X : Type u}
    [TopologicalSpace X] (A : Set (ModelChart d a X))
    {V : Type v} {W : Type w} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    (e : V ≃ₗ[ℝ] W) (f : X → V) (p : X) :
    VectorSmoothAt A (fun x => e (f x)) p ↔ VectorSmoothAt A f p := by
  constructor
  · intro h
    have hh := h.postcomp (LinearMap.toContinuousLinearMap e.symm.toLinearMap).contDiff
    simpa only [LinearMap.coe_toContinuousLinearMap', LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply] using hh
  · intro h
    exact h.postcomp (LinearMap.toContinuousLinearMap e.toLinearMap).contDiff

section Forms
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} (C : CotangentBundle S) {k : ℕ} (D : FormBundle C k)
  (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)

/-- The vector of increasing coefficients is a fixed linear transform of the
chosen exterior bundle's coordinates. -/
theorem coefficients_coordinates (ω : Field S k) (p : c.source) :
    letI := (cotangentSpace C).topology
    letI := D.space.topology
    (fun I => ExteriorData.coefficients C k c hc ω p I) =
      ((Pi.basisFun ℝ (Fin n)).exteriorPower k).equivFun
        (D.modelEquiv.symm (Frames.sectionCoordinates D.space.bundle c.source ⟨c, hc⟩
          (fun q => ω q.val) p)) := by
  letI := (cotangentSpace C).topology
  letI := D.space.topology
  have hp : p.val ∈ (cotangentSpace C).bundle.baseSet ⟨c, hc⟩ := by
    rw [Covectors.cotangent_baseSet]; exact p.property
  rw [show Frames.sectionCoordinates D.space.bundle c.source ⟨c, hc⟩
        (fun q => ω q.val) p = D.modelEquiv (exteriorPower.map k
          ((cotangentSpace C).bundle.fiberCoordinates ⟨c, hc⟩ p.val hp).toLinearMap (ω p.val))
      from exterior_coordinates (cotangentSpace C).bundle D ⟨c, hc⟩ p.val hp (ω p.val)]
  rw [LinearEquiv.symm_apply_apply]
  unfold ExteriorData.coefficients
  rw [cotangent_basis C c hc p.val p.property, exteriorBasis_map]
  ext I
  simp only [Module.Basis.map_repr, LinearEquiv.refl_apply,
    Module.Basis.equivFun_apply]
  rfl

/-- A local section is smooth exactly when its increasing coefficients are
smooth. The exterior model equivalence need not use increasing coordinates. -/
theorem local_smooth_iff_coefficients (ω : Field S k) :
    letI := (cotangentSpace C).topology
    letI := D.space.topology
    ManifoldSmooth (openSubsetAtlas S.smoothStructure.val c.source c.open_source)
      D.space.bundle.totalManifold.smoothStructure.val
      (fun p : c.source => (⟨p.val, ω p.val⟩ :
        Bundle.TotalSpace (Euclidean (n.choose k)) (fun q => Fiber (TangentSpace S q) k))) ↔
    ∀ I : Index n k, VectorSmooth
      (openSubsetAtlas S.smoothStructure.val c.source c.open_source)
      (fun p => ExteriorData.coefficients C k c hc ω p I) := by
  letI := (cotangentSpace C).topology
  letI := D.space.topology
  let A := openSubsetAtlas S.smoothStructure.val c.source c.open_source
  let e : Euclidean (n.choose k) ≃ₗ[ℝ] (Index n k → ℝ) :=
    D.modelEquiv.symm.trans ((Pi.basisFun ℝ (Fin n)).exteriorPower k).equivFun
  have hb (p : c.source) : p.val ∈ D.space.bundle.baseSet ⟨c, hc⟩ := by
    rw [D.baseSet, Covectors.cotangent_baseSet]; exact p.property
  have he (p : c.source) : e (Frames.sectionCoordinates D.space.bundle c.source ⟨c, hc⟩
        (fun q => ω q.val) p) = fun I => ExteriorData.coefficients C k c hc ω p I :=
    (coefficients_coordinates C D c hc ω p).symm
  constructor
  · intro h I p
    have hs := Frames.sectionCoordinates_smoothAt D.space.bundle c.source c.open_source
      ⟨c, hc⟩ (fun q => ω q.val) p (hb p) (h p)
    have hh := (vectorSmoothAt_equiv_iff A e _ p).mpr hs
    have hhh : VectorSmoothAt A (fun p => (fun I => ExteriorData.coefficients C k c hc ω p I)) p := by
      simpa only [he] using hh
    exact hhh.postcomp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Index n k => ℝ) I).contDiff
  · intro h p
    apply Frames.smoothAt_of_sectionCoordinates D.space.bundle c.source c.open_source
      ⟨c, hc⟩ (fun q => ω q.val) p (hb p)
    apply (vectorSmoothAt_equiv_iff A e _ p).mp
    simp_rw [he]
    exact VectorSmoothAt.pi (fun I => h I p)

end Forms

private theorem smooth_iff_coefficients_proof :
    Specs.SmoothManifolds.Ch07.ExteriorAlgebra.smooth_iff_coefficientsType.{u} := by
  intro n a M _ S C k D ω
  letI := (cotangentSpace C).topology
  letI := D.space.topology
  constructor
  · intro h c hc
    apply (local_smooth_iff_coefficients C D c hc ω).mp
    exact (manifoldContDiff_restrict_open (⊤ : ℕ∞) S.smoothStructure.val
      D.space.bundle.totalManifold.smoothStructure.val
      (fun p : M => (⟨p, ω p⟩ : Bundle.TotalSpace (Euclidean (n.choose k))
        (fun q => Fiber (TangentSpace S q) k))) c.source c.open_source).mp
      (fun p hp => h p)
  · intro h p
    obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
    have hh := (local_smooth_iff_coefficients C D c hc ω).mpr (h c hc)
    exact (manifoldContDiff_restrict_open (⊤ : ℕ∞) S.smoothStructure.val
      D.space.bundle.totalManifold.smoothStructure.val
      (fun p : M => (⟨p, ω p⟩ : Bundle.TotalSpace (Euclidean (n.choose k))
        (fun q => Fiber (TangentSpace S q) k))) c.source c.open_source).mpr hh p hp


/-- Exterior functoriality preserves homogeneous multiplication. -/
theorem map_wedge {V : Type u} {W : Type v}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    {k l : ℕ} (L : V →ₗ[ℝ] W) (x : ⋀[ℝ]^k V) (y : ⋀[ℝ]^l V) :
    exteriorPower.map (k+l) L (exteriorPower.wedge ℝ V k l x y) =
      exteriorPower.wedge ℝ W k l (exteriorPower.map k L x) (exteriorPower.map l L y) := by
  apply Subtype.ext
  simp only [exteriorPower.coe_map, exteriorPower.wedge, DirectSum.gMulLHom_apply_apply,
    SetLike.coe_gMul, map_mul]

/-- Wedge in any chosen finite-dimensional exterior coordinates is bilinear. -/
def modelWedge {n k l : ℕ}
    (D : (⋀[ℝ]^k (Euclidean n)) ≃ₗ[ℝ] Euclidean (n.choose k))
    (E : (⋀[ℝ]^l (Euclidean n)) ≃ₗ[ℝ] Euclidean (n.choose l))
    (F : (⋀[ℝ]^(k+l) (Euclidean n)) ≃ₗ[ℝ] Euclidean (n.choose (k+l))) :
    Euclidean (n.choose k) →ₗ[ℝ] Euclidean (n.choose l) →ₗ[ℝ] Euclidean (n.choose (k+l)) :=
  ((exteriorPower.wedge ℝ (Euclidean n) k l).compl₁₂ D.symm.toLinearMap E.symm.toLinearMap).compr₂
    F.toLinearMap

theorem bilinear_vectorSmoothAt {d r s t : ℕ} {a : ModelKind} {X : Type u}
    [TopologicalSpace X] {A : Set (ModelChart d a X)}
    (L : Euclidean r →ₗ[ℝ] Euclidean s →ₗ[ℝ] Euclidean t)
    {f : X → Euclidean r} {g : X → Euclidean s} {p : X}
    (hf : VectorSmoothAt A f p) (hg : VectorSmoothAt A g p) :
    VectorSmoothAt A (fun x => L (f x) (g x)) p := by
  let T : Euclidean r →L[ℝ] Euclidean s →L[ℝ] Euclidean t :=
    LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.toLinearMap.comp L)
  exact (hf.prod hg).postcomp ((T.contDiff.comp contDiff_fst).clm_apply contDiff_snd)

/-- The wedge has the same fixed bilinear formula in every induced chart. -/
theorem exterior_coordinates_wedge
    {d r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold d a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    (B : SmoothVectorBundle S r ι E) {k l : ℕ}
    (D : ExteriorBundle B k) (G : ExteriorBundle B l) (F : ExteriorBundle B (k+l))
    (i : ι) (p : M) (hp : p ∈ B.baseSet i) (x : ⋀[ℝ]^k (E p)) (y : ⋀[ℝ]^l (E p)) :
    letI := D.space.topology
    letI := G.space.topology
    letI := F.space.topology
    F.space.bundle.fiberCoordinates i p ((F.baseSet i).symm ▸ hp)
      (exteriorPower.wedge ℝ (E p) k l x y) =
    modelWedge D.modelEquiv G.modelEquiv F.modelEquiv
      (D.space.bundle.fiberCoordinates i p ((D.baseSet i).symm ▸ hp) x)
      (G.space.bundle.fiberCoordinates i p ((G.baseSet i).symm ▸ hp) y) := by
  letI := D.space.topology
  letI := G.space.topology
  letI := F.space.topology
  have hd := congrArg D.modelEquiv.symm (exterior_coordinates B D i p hp x)
  have hg := congrArg G.modelEquiv.symm (exterior_coordinates B G i p hp y)
  simp only [LinearEquiv.symm_apply_apply] at hd hg
  calc
    _ = F.modelEquiv (exteriorPower.map (k+l) (B.fiberCoordinates i p hp).toLinearMap
        (exteriorPower.wedge ℝ (E p) k l x y)) := exterior_coordinates B F i p hp _
    _ = F.modelEquiv (exteriorPower.wedge ℝ (Euclidean r) k l
        (exteriorPower.map k (B.fiberCoordinates i p hp).toLinearMap x)
        (exteriorPower.map l (B.fiberCoordinates i p hp).toLinearMap y)) :=
      congrArg F.modelEquiv (map_wedge (B.fiberCoordinates i p hp).toLinearMap x y)
    _ = _ := congrArg F.modelEquiv
      (congrArg₂ (fun z t => exteriorPower.wedge ℝ (Euclidean r) k l z t) hd.symm hg.symm)

private theorem wedge_smooth_proof :
    Specs.SmoothManifolds.Ch07.ExteriorAlgebra.wedge_smoothType.{u} := by
  intro n a M _ S C k l D E F α β hα hβ
  letI := (cotangentSpace C).topology
  letI := D.space.topology
  letI := E.space.topology
  letI := F.space.topology
  have hlocal (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) :
      ManifoldSmooth (openSubsetAtlas S.smoothStructure.val c.source c.open_source)
        F.space.bundle.totalManifold.smoothStructure.val
        (fun p : c.source => (⟨p.val, fieldWedge α β p.val⟩ :
          Bundle.TotalSpace (Euclidean (n.choose (k+l))) (fun q => Fiber (TangentSpace S q) (k+l)))) := by
    have hD := (manifoldContDiff_restrict_open (⊤ : ℕ∞) S.smoothStructure.val
      D.space.bundle.totalManifold.smoothStructure.val
      (fun p : M => (⟨p, α p⟩ : Bundle.TotalSpace (Euclidean (n.choose k))
        (fun q => Fiber (TangentSpace S q) k))) c.source c.open_source).mp (fun p hp => hα p)
    have hE := (manifoldContDiff_restrict_open (⊤ : ℕ∞) S.smoothStructure.val
      E.space.bundle.totalManifold.smoothStructure.val
      (fun p : M => (⟨p, β p⟩ : Bundle.TotalSpace (Euclidean (n.choose l))
        (fun q => Fiber (TangentSpace S q) l))) c.source c.open_source).mp (fun p hp => hβ p)
    have hb (p : c.source) : p.val ∈ (cotangentSpace C).bundle.baseSet ⟨c, hc⟩ := by
      rw [Covectors.cotangent_baseSet]; exact p.property
    intro p
    apply Frames.smoothAt_of_sectionCoordinates F.space.bundle c.source c.open_source ⟨c, hc⟩
      (fun q => fieldWedge α β q.val) p (by rw [F.baseSet]; exact hb p)
    have hd := Frames.sectionCoordinates_smoothAt D.space.bundle c.source c.open_source
      ⟨c, hc⟩ (fun q => α q.val) p (by rw [D.baseSet]; exact hb p) (hD p)
    have he := Frames.sectionCoordinates_smoothAt E.space.bundle c.source c.open_source
      ⟨c, hc⟩ (fun q => β q.val) p (by rw [E.baseSet]; exact hb p) (hE p)
    have hh := bilinear_vectorSmoothAt (modelWedge D.modelEquiv E.modelEquiv F.modelEquiv) hd he
    apply hh.congr
    apply Filter.Eventually.of_forall
    intro q
    change modelWedge D.modelEquiv E.modelEquiv F.modelEquiv
      (D.space.bundle.fiberCoordinates ⟨c, hc⟩ q.val ((D.baseSet _).symm ▸ hb q) (α q.val))
      (E.space.bundle.fiberCoordinates ⟨c, hc⟩ q.val ((E.baseSet _).symm ▸ hb q) (β q.val)) =
      F.space.bundle.fiberCoordinates ⟨c, hc⟩ q.val ((F.baseSet _).symm ▸ hb q)
        (wedge (V := TangentSpace S q.val) (k := k) (l := l) (α q.val) (β q.val))
    exact (exterior_coordinates_wedge (cotangentSpace C).bundle D E F ⟨c, hc⟩ q.val
      (hb q) (α q.val) (β q.val)).symm
  intro p
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
  exact (manifoldContDiff_restrict_open (⊤ : ℕ∞) S.smoothStructure.val
    F.space.bundle.totalManifold.smoothStructure.val
    (fun p : M => (⟨p, fieldWedge α β p⟩ : Bundle.TotalSpace (Euclidean (n.choose (k+l)))
      (fun q => Fiber (TangentSpace S q) (k+l)))) c.source c.open_source).mpr (hlocal c hc) p hp


private theorem tensor_interpretation_proof :
    Specs.SmoothManifolds.Ch07.ExteriorAlgebra.tensor_interpretationType.{u} := by
  intro V _ _ _ k
  have ht : Function.Bijective (TensorData.covariantEvaluate V k) :=
    PiTensorProduct.lift.symm.bijective.comp
      (PiTensorProduct.dualDistribEquiv (R := ℝ) (M := fun _ : Fin k => V)).bijective
  refine ⟨ht, fun t => ?_⟩
  have he := alternating_interpretation_proof V k
  constructor
  · rintro ⟨A, hA⟩
    obtain ⟨x, hx⟩ := he.2 A
    refine ⟨x, ?_, ?_⟩
    · exact (congrArg (fun A : AlternatingMap ℝ V ℝ (Fin k) => A.toMultilinearMap) hx).trans hA
    intro y hy
    apply he.1
    apply AlternatingMap.coe_multilinearMap_injective
    exact hy.trans ((congrArg (fun A : AlternatingMap ℝ V ℝ (Fin k) => A.toMultilinearMap) hx).trans hA).symm
  · rintro ⟨x, hx, _⟩
    exact ⟨evaluate V k x, hx⟩

private theorem fields_above_dimension_proof :
    Specs.SmoothManifolds.Ch07.ExteriorAlgebra.fields_above_dimensionType.{u} := by
  intro n a M _ S C k hk ω p
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
  let e := C.tangent.fiberCoordinates.equiv c hc p hp
  letI : FiniteDimensional ℝ (TangentSpace S p) :=
    FiniteDimensional.of_injective e.toLinearMap e.injective
  have hd : Module.finrank ℝ (TangentSpace S p) = n := by
    simpa [ModelData.Euclidean, Module.finrank_pi] using e.finrank_eq
  exact above_dimension_proof (TangentSpace S p) k (by rw [hd]; exact hk) (ω p)


theorem alternating_interpretation :
    Specs.SmoothManifolds.Ch07.ExteriorAlgebra.alternating_interpretationType.{u} :=
  alternating_interpretation_proof

theorem tensor_interpretation :
    Specs.SmoothManifolds.Ch07.ExteriorAlgebra.tensor_interpretationType.{u} :=
  tensor_interpretation_proof

theorem determinant_normalization :
    Specs.SmoothManifolds.Ch07.ExteriorAlgebra.determinant_normalizationType.{u} :=
  determinant_normalization_proof

theorem increasing_basis :
    Specs.SmoothManifolds.Ch07.ExteriorAlgebra.increasing_basisType.{u} :=
  increasing_basis_proof

theorem wedge_decomposable :
    Specs.SmoothManifolds.Ch07.ExteriorAlgebra.wedge_decomposableType.{u} :=
  wedge_decomposable_proof

theorem wedge_assoc :
    Specs.SmoothManifolds.Ch07.ExteriorAlgebra.wedge_assocType.{u} :=
  wedge_assoc_proof

theorem wedge_comm :
    Specs.SmoothManifolds.Ch07.ExteriorAlgebra.wedge_commType.{u} :=
  wedge_comm_proof

theorem degree_zero :
    Specs.SmoothManifolds.Ch07.ExteriorAlgebra.degree_zeroType.{u} :=
  degree_zero_proof

theorem above_dimension :
    Specs.SmoothManifolds.Ch07.ExteriorAlgebra.above_dimensionType.{u} :=
  above_dimension_proof

theorem fields_above_dimension :
    Specs.SmoothManifolds.Ch07.ExteriorAlgebra.fields_above_dimensionType.{u} :=
  fields_above_dimension_proof

theorem exists_formBundle :
    Specs.SmoothManifolds.Ch07.ExteriorAlgebra.exists_formBundleType.{u} :=
  exists_formBundle_proof

theorem coefficient_expansion :
    Specs.SmoothManifolds.Ch07.ExteriorAlgebra.coefficient_expansionType.{u} :=
  coefficient_expansion_proof

theorem coefficients_unique :
    Specs.SmoothManifolds.Ch07.ExteriorAlgebra.coefficients_uniqueType.{u} :=
  coefficients_unique_proof

theorem smooth_iff_coefficients :
    Specs.SmoothManifolds.Ch07.ExteriorAlgebra.smooth_iff_coefficientsType.{u} :=
  smooth_iff_coefficients_proof

theorem wedge_smooth :
    Specs.SmoothManifolds.Ch07.ExteriorAlgebra.wedge_smoothType.{u} :=
  wedge_smooth_proof

end SmoothManifolds.ExteriorAlgebraResults
