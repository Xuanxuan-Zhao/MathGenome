import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Orientations.Boundary
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Tangent.BoundaryCones
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Orientations.Equivalences
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Orientations.ProductsAndSigns
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin

/-! Intrinsic outward-first boundary orientations and their sign conventions. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
noncomputable section
open scoped Classical Topology SmoothManifolds.BoundaryConeData

namespace SmoothManifolds.BoundaryOrientations
open ModelData AtlasData MapData BoundaryData TangentData DifferentialData
  TangentBundleData OrientationData OrientationProductData BoundaryOrientationData
  OrientationResults Set Module
universe u v w

theorem inward_iff_coordinate {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n+1) .halfSpace M) (p : intrinsicBoundary S)
    (c : ModelChart (n+1) .halfSpace M) (hc : c ∈ S.smoothStructure.val)
    (hp : p.val ∈ c.source) (E : TangentSpace S p.val ≃ₗ[ℝ] Euclidean (n+1))
    (hE : IsChartCoordinates S p.val c E) (v : TangentSpace S p.val) :
    IsInward S p v ↔ 0 < E v (Fin.last n) := by
  constructor
  · rintro ⟨d, hd, hpd, F, hF, hv⟩
    obtain ⟨r, hr, hFE⟩ :=
      boundary_transition_positive S p d c hd hc hpd hp F E hF hE
    rw [hFE v]
    exact mul_pos hr hv
  · intro hv
    exact ⟨c, hc, hp, E, hE, hv⟩

theorem outward_iff_coordinate {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n+1) .halfSpace M) (p : intrinsicBoundary S)
    (c : ModelChart (n+1) .halfSpace M) (hc : c ∈ S.smoothStructure.val)
    (hp : p.val ∈ c.source) (E : TangentSpace S p.val ≃ₗ[ℝ] Euclidean (n+1))
    (hE : IsChartCoordinates S p.val c E) (v : TangentSpace S p.val) :
    IsOutward S p v ↔ E v (Fin.last n) < 0 := by
  simp only [IsOutward, inward_iff_coordinate S p c hc hp E hE,
    map_neg, Pi.neg_apply, neg_pos]

theorem normal_rays :
    Specs.SmoothManifolds.Orientations.Boundary.normal_raysType.{u} := by
  intro n a M _ S B hB p L hL c hc hp E hE
  cases a with
  | euclidean =>
    have h := p.property
    change p.val ∈ SmoothManifolds.intrinsicBoundary S at h
    rw [intrinsicBoundary_euclidean S] at h
    exact False.elim h
  | halfSpace =>
    have hi := inward_iff_coordinate S p c hc hp E hE
    have ho := outward_iff_coordinate S p c hc hp E hE
    refine ⟨hi, ho, ?_⟩
    obtain ⟨Q, hQ, hdim, hin, hout, _⟩ :=
      boundary_normal_quotient S B hB p L hL c hc hp E hE
    refine ⟨Q, hQ, hdim, ?_, ?_⟩
    · rw [inwardRay, show {v | IsInward S p v} = {v | 0 < E v (Fin.last n)} from
        Set.ext hi]
      exact hin
    · rw [outwardRay, show {v | IsOutward S p v} = {v | E v (Fin.last n) < 0} from
        Set.ext ho]
      exact hout

/-- Changing the degree index does not change the ambient exterior element. -/
@[simp] theorem coe_castExterior {V : Type u} [AddCommGroup V] [Module ℝ V]
    {i j : ℕ} (h : i = j) (x : ⋀[ℝ]^i V) :
    (castExterior h x : ExteriorAlgebra ℝ V) = x.val := by
  subst h
  rfl

/-- An explicit ambient-algebra formula makes the order of insertion unambiguous. -/
@[simp] theorem coe_normalWedge {V : Type u} {W : Type v}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    {n : ℕ} (L : W →ₗ[ℝ] V) (v : V) (η : ⋀[ℝ]^n W) :
    (normalWedge L v η : ExteriorAlgebra ℝ V) =
      ExteriorAlgebra.ι ℝ v * ExteriorAlgebra.map L η.val := by
  simp [normalWedge, exteriorPower.wedge, DirectSum.gMulLHom_apply_apply,
    SetLike.coe_gMul, exteriorPower.coe_map]

theorem normalWedge_add {V : Type u} {W : Type v}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    {n : ℕ} (L : W →ₗ[ℝ] V) (v w : V) (η : ⋀[ℝ]^n W) :
    normalWedge L (v+w) η = normalWedge L v η + normalWedge L w η := by
  apply Subtype.ext
  simp [map_add, add_mul]

theorem normalWedge_smul {V : Type u} {W : Type v}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    {n : ℕ} (L : W →ₗ[ℝ] V) (t : ℝ) (v : V) (η : ⋀[ℝ]^n W) :
    normalWedge L (t • v) η = t • normalWedge L v η := by
  apply Subtype.ext
  simp [map_smul]

/-- Inserting a tangential vector into a top tangential exterior vector gives
zero. This works for n=0 as well. -/
theorem normalWedge_tangent {V : Type u} {W : Type v}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    [FiniteDimensional ℝ W] {n : ℕ} (hdim : Module.finrank ℝ W = n)
    (L : W →ₗ[ℝ] V) (w : W) (η : ⋀[ℝ]^n W) :
    normalWedge L (L w) η = 0 := by
  have hzero : normalWedge (LinearMap.id : W →ₗ[ℝ] W) w η = 0 := by
    have hz : Module.finrank ℝ (⋀[ℝ]^(n+1) W) = 0 := by
      rw [exteriorPower.finrank_eq, hdim, Nat.choose_eq_zero_of_lt (Nat.lt_succ_self n)]
    exact (finrank_zero_iff_forall_zero.mp hz) _
  have hamb : ExteriorAlgebra.ι ℝ w * η.val = 0 := by
    have h := congrArg (fun x : ⋀[ℝ]^(n+1) W => x.val) hzero
    simpa using h
  apply Subtype.ext
  simpa using congrArg (ExteriorAlgebra.map L) hamb

theorem outward_independent :
    Specs.SmoothManifolds.Orientations.Boundary.outward_independentType.{u} := by
  intro n a M _ S B hB p L hL v w hv hw
  cases a with
  | euclidean =>
    have h := p.property
    change p.val ∈ SmoothManifolds.intrinsicBoundary S at h
    rw [intrinsicBoundary_euclidean S] at h
    exact False.elim h
  | halfSpace =>
    obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p.val
    let E := coordinateDerivationEquiv S p.val c hc hp
    have hE := coordinateDerivationEquiv_isChartCoordinates S p.val c hc hp
    have hv' := (outward_iff_coordinate S p c hc hp E hE v).mp hv
    have hw' := (outward_iff_coordinate S p c hc hp E hE w).mp hw
    let t : ℝ := E w (Fin.last n) / E v (Fin.last n)
    have ht : 0 < t := div_pos_of_neg_of_neg hw' hv'
    have hnorm : E (w - t • v) (Fin.last n) = 0 := by
      simp only [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [show t * E v (Fin.last n) = E w (Fin.last n) from
        div_mul_cancel₀ _ (ne_of_lt hv')]
      exact sub_self _
    have hmem := (boundary_inclusion_image S B hB p c hc hp L hL E hE).2
      (w - t • v) |>.mpr hnorm
    refine ⟨t, ht, hmem, ?_⟩
    obtain ⟨z, hz⟩ := hmem
    have hwz : w = L z + t • v := by rw [hz]; exact (sub_add_cancel w (t • v)).symm
    intro η
    letI := (tangent_dimension B p).1
    rw [hwz, normalWedge_add, normalWedge_tangent (tangent_dimension B p).2,
      zero_add, normalWedge_smul]

theorem outward_coordinate_wedge {V : Type u} [AddCommGroup V] [Module ℝ V]
    {n : ℕ} (b : Fin (n+1) → V) :
    ExteriorAlgebra.ι ℝ (-b (Fin.last n)) *
      ExteriorAlgebra.ιMulti ℝ n (fun i => b i.castSucc) =
    (-1 : ℝ)^(n+1) • ExteriorAlgebra.ιMulti ℝ (n+1) b := by
  have h := (ExteriorAlgebra.ιMulti ℝ (n+1) (M := V)).neg_one_pow_smul_map_insertNth
    (Fin.last n) (b (Fin.last n)) (fun i : Fin n => b i.castSucc)
  have hi : (Fin.last n).insertNth (b (Fin.last n)) (fun i : Fin n => b i.castSucc) = b := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  rw [hi] at h
  have h' : (-1 : ℝ)^n • ExteriorAlgebra.ιMulti ℝ (n+1) b =
      ExteriorAlgebra.ιMulti ℝ (n+1) (Matrix.vecCons (b (Fin.last n))
        (fun i : Fin n => b i.castSucc)) := by
    simpa only [Fin.val_last, ← Int.cast_smul_eq_zsmul ℝ, Int.cast_pow,
      Int.cast_neg, Int.cast_one] using h
  rw [map_neg, neg_mul]
  rw [show ExteriorAlgebra.ι ℝ (b (Fin.last n)) *
      ExteriorAlgebra.ιMulti ℝ n (fun i => b i.castSucc) =
      ExteriorAlgebra.ιMulti ℝ (n+1) (Matrix.vecCons (b (Fin.last n))
        (fun i : Fin n => b i.castSucc)) by simp]
  rw [← h']
  simp only [pow_succ, mul_neg_one, neg_smul]

theorem normalWedge_smul_right {V : Type u} {W : Type v}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    {n : ℕ} (L : W →ₗ[ℝ] V) (t : ℝ) (v : V) (η : ⋀[ℝ]^n W) :
    normalWedge L v (t • η) = t • normalWedge L v η := by
  apply Subtype.ext
  simp [map_smul]

theorem normalWedge_coordinateVector {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n+1) .halfSpace M)
    (B : SmoothManifold n .euclidean (intrinsicBoundary S))
    (K : FiberCoordinates S) (H : FiberCoordinates B)
    (c : ModelChart (n+1) .halfSpace M) (hc : c ∈ S.smoothStructure.val)
    (b : ModelChart n .euclidean (intrinsicBoundary S)) (hb : b ∈ B.smoothStructure.val)
    (hface : IsFaceRestriction S c b) (p : intrinsicBoundary S)
    (hp : p ∈ b.source) (hpc : p.val ∈ c.source)
    (L : TangentSpace B p →ₗ[ℝ] TangentSpace S p.val)
    (hL : IsDifferential B S Subtype.val p L) :
    normalWedge L (-(K.equiv c hc p.val hpc).symm ((Pi.basisFun ℝ (Fin (n+1))) (Fin.last n)))
      (coordinateVector H b hb ⟨p, hp⟩) =
    (-1 : ℝ)^(n+1) • coordinateVector K c hc ⟨p.val, hpc⟩ := by
  let E := K.equiv c hc p.val hpc
  let F := H.equiv b hb p hp
  have hinc (i : Fin n) : L (F.symm ((Pi.basisFun ℝ (Fin n)) i)) =
      E.symm ((Pi.basisFun ℝ (Fin (n+1))) i.castSucc) := by
    apply E.injective
    rw [boundary_inclusion_coordinates S B p c hc hpc b hb hface L hL E
      (K.isCoordinates c hc p.val hpc)]
    rw [← chartCoordinates_eq B p b hb hp F (H.isCoordinates b hb p hp), F.apply_symm_apply]
    simp only [E.apply_symm_apply]
    ext j
    refine Fin.lastCases ?_ (fun k => ?_) j <;> simp [Pi.basisFun_apply, Pi.single_apply]
  apply Subtype.ext
  simp only [coe_normalWedge, coordinateVector, exteriorPower.ιMulti_apply_coe,
    ExteriorAlgebra.map_apply_ιMulti, Submodule.coe_smul_of_tower]
  change ExteriorAlgebra.ι ℝ (-(E.symm ((Pi.basisFun ℝ (Fin (n+1))) (Fin.last n)))) *
      ExteriorAlgebra.ιMulti ℝ n (fun i => L (F.symm ((Pi.basisFun ℝ (Fin n)) i))) = _
  simp_rw [hinc]
  exact outward_coordinate_wedge (fun i => E.symm ((Pi.basisFun ℝ (Fin (n+1))) i))

theorem boundary_chart_sign :
    Specs.SmoothManifolds.Orientations.Boundary.boundary_chart_signType.{u} := by
  intro n a M _ S B hB o q hind s t hs ht c hc b hb hface p hp hpc
  cases a with
  | euclidean =>
    have h := p.property
    change p.val ∈ SmoothManifolds.intrinsicBoundary S at h
    rw [intrinsicBoundary_euclidean S] at h
    exact False.elim h
  | halfSpace =>
    obtain ⟨K⟩ := TangentBundle.fiberCoordinates_exists S
    obtain ⟨H⟩ := TangentBundle.fiberCoordinates_exists B
    obtain ⟨L, hL, _⟩ := differential_exists B S Subtype.val hB.1 p
    let E := K.equiv c hc p.val hpc
    let v := -E.symm ((Pi.basisFun ℝ (Fin (n+1))) (Fin.last n))
    have hv : IsOutward S p v := by
      apply (outward_iff_coordinate S p c hc hpc E (K.isCoordinates c hc p.val hpc) v).mpr
      simp [v, Pi.basisFun_apply]
    have hpos := (hind p L hL v hv _).mp (ht H b hb ⟨p, hp⟩)
    change IsPositive (o.val p.val)
      (normalWedge L v (signValue (t.sign b hb ⟨p, hp⟩) • coordinateVector H b hb ⟨p, hp⟩)) at hpos
    rw [normalWedge_smul_right, normalWedge_coordinateVector S B K H c hc b hb hface p hp hpc L hL] at hpos
    have hbulk := hs K c hc ⟨p.val, hpc⟩
    have hsame := (ray_eq_iff hpos.choose hbulk.choose).mp
      (hpos.choose_spec.trans hbulk.choose_spec.symm)
    have hrel := (signed_scalar_sameRay_iff (coordinateVector K c hc ⟨p.val, hpc⟩)
      (coordinateVector_ne_zero K c hc ⟨p.val, hpc⟩)
      ((-1 : ℝ)^(n+1)) (pow_ne_zero _ (by norm_num))
      (t.sign b hb ⟨p, hp⟩) (s.sign c hc ⟨p.val, hpc⟩)).mp hsame
    rcases (n+1).even_or_odd with he | he
    · rw [he.neg_one_pow] at hrel ⊢
      simpa using hrel.symm
    · rw [he.neg_one_pow] at hrel ⊢
      norm_num at hrel ⊢
      linarith


theorem positive_smul_iff {V : Type u} [AddCommGroup V] [Module ℝ V]
    (r : Module.Ray ℝ V) (x : V) {t : ℝ} (ht : 0 < t) :
    IsPositive r (t • x) ↔ IsPositive r x := by
  constructor
  · rintro ⟨htx, h⟩
    have hx : x ≠ 0 := fun hx => htx (by rw [hx, smul_zero])
    exact ⟨hx, (ray_pos_smul hx ht htx).symm.trans h⟩
  · rintro ⟨hx, h⟩
    exact ⟨smul_ne_zero ht.ne' hx, (ray_pos_smul hx ht _).trans h⟩

theorem positive_map_iff {V : Type u} {W : Type v}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (E : V ≃ₗ[ℝ] W) (r : Module.Ray ℝ V) (x : V) :
    IsPositive (Module.Ray.map E r) (E x) ↔ IsPositive r x := by
  constructor
  · rintro ⟨hEx, h⟩
    have hx : x ≠ 0 := E.map_ne_zero_iff.mp hEx
    refine ⟨hx, (Module.Ray.map E).injective ?_⟩
    simpa only [Module.Ray.map_apply] using h
  · rintro ⟨hx, h⟩
    exact ⟨E.map_ne_zero_iff.mpr hx, by rw [← Module.Ray.map_apply E x hx, h]⟩

theorem ray_ext_positive {V : Type u} [AddCommGroup V] [Module ℝ V]
    (r s : Module.Ray ℝ V) (h : ∀ x, IsPositive r x ↔ IsPositive s x) : r = s := by
  induction r using Module.Ray.ind with | h x hx =>
  exact ((h x).mp ⟨hx, rfl⟩).choose_spec

private def normalWedgeMap {V : Type u} {W : Type v}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    {n : ℕ} (L : W →ₗ[ℝ] V) (v : V) : (⋀[ℝ]^n W) →ₗ[ℝ] (⋀[ℝ]^(n+1) V) where
  toFun := normalWedge L v
  map_add' x y := by apply Subtype.ext; simp [map_add, mul_add]
  map_smul' t x := by apply Subtype.ext; simp

private theorem coordinate_normal_bijective {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n+1) .halfSpace M)
    (B : SmoothManifold n .euclidean (intrinsicBoundary S))
    (K : FiberCoordinates S) (H : FiberCoordinates B)
    (c : ModelChart (n+1) .halfSpace M) (hc : c ∈ S.smoothStructure.val)
    (b : ModelChart n .euclidean (intrinsicBoundary S)) (hb : b ∈ B.smoothStructure.val)
    (hface : IsFaceRestriction S c b) (p : intrinsicBoundary S)
    (hp : p ∈ b.source) (hpc : p.val ∈ c.source)
    (L : TangentSpace B p →ₗ[ℝ] TangentSpace S p.val)
    (hL : IsDifferential B S Subtype.val p L) :
    Function.Bijective (normalWedgeMap (n := n) L
      (-(K.equiv c hc p.val hpc).symm ((Pi.basisFun ℝ (Fin (n+1))) (Fin.last n)))) := by
  letI := (tangent_dimension S p.val).1
  letI := (tangent_dimension B p).1
  let A := normalWedgeMap (n := n) L
    (-(K.equiv c hc p.val hpc).symm ((Pi.basisFun ℝ (Fin (n+1))) (Fin.last n)))
  have hn : A (coordinateVector H b hb ⟨p, hp⟩) ≠ 0 := by
    change normalWedge _ _ _ ≠ 0
    rw [normalWedge_coordinateVector S B K H c hc b hb hface p hp hpc L hL]
    exact smul_ne_zero (pow_ne_zero _ (by norm_num)) (coordinateVector_ne_zero K c hc _)
  have hinj : Function.Injective A := by
    apply (LinearMap.ker_eq_bot).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    rw [determinant_eq_coefficient_smul H b hb ⟨p, hp⟩ x]
    have h := congrArg A (determinant_eq_coefficient_smul H b hb ⟨p, hp⟩ x)
    rw [hx, map_smul] at h
    have hz := (smul_eq_zero.mp h.symm).resolve_right hn
    rw [hz, zero_smul]
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    ((determinant_finrank B p).trans (determinant_finrank S p.val).symm)).mp hinj⟩

private def InducedRayPredicate {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold (n+1) a M}
    (B : SmoothManifold n .euclidean (intrinsicBoundary S)) (o : Orientation S)
    (p : intrinsicBoundary S) (r : DeterminantRay B p) : Prop :=
  ∀ (L : TangentSpace B p →ₗ[ℝ] TangentSpace S p.val),
    IsDifferential B S Subtype.val p L → ∀ v, IsOutward S p v → ∀ η,
    IsPositive r η ↔ IsPositive (o.val p.val) (normalWedge L v η)

private theorem pointwise_induced_ray
    (hout : Specs.SmoothManifolds.Orientations.Boundary.outward_independentType.{u})
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n+1) a M)
    (B : SmoothManifold n .euclidean (intrinsicBoundary S)) (hB : IsNaturalBoundary S B)
    (o : Orientation S) (p : intrinsicBoundary S) :
    ∃! r : DeterminantRay B p, InducedRayPredicate B o p r := by
  cases a with
  | euclidean =>
    exact False.elim (by simpa only [intrinsicBoundary_euclidean S, Set.mem_empty_iff_false] using p.property)
  | halfSpace =>
    obtain ⟨K⟩ := TangentBundle.fiberCoordinates_exists S
    obtain ⟨H⟩ := TangentBundle.fiberCoordinates_exists B
    obtain ⟨c, hc, hpc⟩ := S.smoothStructure.property.1.1 p.val
    obtain ⟨b, hb, hface⟩ := hB.2 c hc ⟨⟨p, hpc⟩⟩
    have hpb : p ∈ b.source := by rw [hface.1]; exact hpc
    obtain ⟨L, hL, huniq⟩ := differential_exists B S Subtype.val hB.1 p
    let E := K.equiv c hc p.val hpc
    let v := -E.symm ((Pi.basisFun ℝ (Fin (n+1))) (Fin.last n))
    have hv : IsOutward S p v := by
      apply (outward_iff_coordinate S p c hc hpc E (K.isCoordinates c hc p.val hpc) v).mpr
      simp [v, Pi.basisFun_apply]
    let Q := LinearEquiv.ofBijective (normalWedgeMap L v)
      (coordinate_normal_bijective S B K H c hc b hb hface p hpb hpc L hL)
    let r := Module.Ray.map Q.symm (o.val p.val)
    have hr (η) : IsPositive r η ↔ IsPositive (o.val p.val) (normalWedge L v η) := by
      change IsPositive r η ↔ IsPositive (o.val p.val) (Q η)
      have h := positive_map_iff Q r η
      simpa only [r, ← Module.Ray.map_symm Q, Equiv.apply_symm_apply] using h.symm
    have hpred : InducedRayPredicate B o p r := by
      intro L' hL' w hw η
      have heq : L' = L := huniq L' hL'
      subst L'
      obtain ⟨t, ht, _, htw⟩ := hout S B hB p L hL v w hv hw
      rw [htw, positive_smul_iff _ _ ht]
      exact hr η
    refine ⟨r, hpred, ?_⟩
    intro r' hr'
    apply ray_ext_positive r' r
    intro η
    exact (hr' L hL v hv η).trans (hr η).symm

private theorem coordinate_section_smooth_scalar {n : ℕ} {a : ModelKind}
    {M : Type u} [TopologicalSpace M] (S : SmoothManifold n a M)
    (K : FiberCoordinates S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (δ : c.source → ℝ) (hδ : IsLocallyConstant δ) :
    IsSmoothDeterminantSection c.source c.open_source
      (fun p => δ p • coordinateVector K c hc p) := by
  intro L d hd
  let incl : ↥(c.source ∩ d.source) → c.source := fun p => ⟨p.val, p.property.1⟩
  have hinc : Continuous incl := continuous_subtype_val.subtype_mk _
  have hs := vectorSmooth_of_isLocallyConstant
    (openSubsetAtlas S.smoothStructure.val (c.source ∩ d.source)
      (c.open_source.inter d.open_source)) (hδ.comp_continuous hinc)
  have ht := transitionDeterminant_smooth S L c d hc hd
  have he : (fun p : ↥(c.source ∩ d.source) =>
      determinantCoefficient L d hd ⟨p.val, p.property.2⟩
        (δ ⟨p.val, p.property.1⟩ • coordinateVector K c hc ⟨p.val, p.property.1⟩)) =
      (fun p : ↥(c.source ∩ d.source) => δ ⟨p.val, p.property.1⟩ *
        transitionDeterminant L c d hc hd p) := by
    funext p
    rw [map_smul, smul_eq_mul, coordinateVector_independent K L,
      coefficient_coordinateVector_transition]
  rw [he]
  intro p
  exact ((hs p).prod (ht p)).postcomp (contDiff_fst.mul contDiff_snd)

private theorem continuous_of_local_positive_sections {n : ℕ} {a : ModelKind}
    {M : Type u} [TopologicalSpace M] (S : SmoothManifold n a M) (r : RayField S)
    (hlocal : ∀ p : M, ∃ U : Set M, ∃ hU : IsOpen U, p ∈ U ∧
      ∃ g : ∀ q : U, DeterminantLine S q.val,
        IsSmoothDeterminantSection U hU g ∧ ∀ q, IsPositive (r q.val) (g q)) :
    IsContinuousRayField r := by
  intro K c hc
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro p
  obtain ⟨U, hU, hp, g, hs, hpos⟩ := hlocal p.val
  have hn (q : U) : g q ≠ 0 := (hpos q).choose
  let U' : Set c.source := {q | q.val ∈ U}
  have hU' : IsOpen U' := hU.preimage continuous_subtype_val
  let incl : U' → ↥(U ∩ c.source) := fun q => ⟨q.val.val, q.property, q.val.property⟩
  have hi : Continuous incl := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have h := (smooth_section_ray_locallyConstant U hU g hn hs K c hc).comp_continuous hi
  have he : (fun q : U' => Module.Ray.map (determinantCoordinates K c hc q.val) (r q.val.val)) =
      (fun q : U' => Module.Ray.map (determinantCoordinates K c hc q.val)
        (rayOfNeZero ℝ (g ⟨q.val.val, q.property⟩) (hn _))) := by
    funext q
    exact congrArg (Module.Ray.map (determinantCoordinates K c hc q.val))
      (hpos ⟨q.val.val, q.property⟩).choose_spec.symm
  have hf : IsLocallyConstant
      (fun q : U' => Module.Ray.map (determinantCoordinates K c hc q.val) (r q.val.val)) := by
    rw [he]
    exact h
  obtain ⟨V, hV, hpV, hconst⟩ := hf.exists_open ⟨p, hp⟩
  refine ⟨Subtype.val '' V, hU'.isOpenMap_subtype_val V hV, ⟨⟨p, hp⟩, hpV, rfl⟩, ?_⟩
  rintro y ⟨z, hz, rfl⟩
  exact hconst z hz

private theorem induced_rayfield_continuous
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n+1) a M)
    (B : SmoothManifold n .euclidean (intrinsicBoundary S)) (hB : IsNaturalBoundary S B)
    (o : Orientation S) (r : RayField B)
    (hr : ∀ p, InducedRayPredicate B o p (r p)) : IsContinuousRayField r := by
  apply continuous_of_local_positive_sections B r
  intro p
  cases a with
  | euclidean =>
    exact False.elim (by simpa only [intrinsicBoundary_euclidean S, Set.mem_empty_iff_false] using p.property)
  | halfSpace =>
    obtain ⟨K⟩ := TangentBundle.fiberCoordinates_exists S
    obtain ⟨H⟩ := TangentBundle.fiberCoordinates_exists B
    obtain ⟨s, hs, _⟩ := (signed_charts S o.val).mp o.property
    obtain ⟨c, hc, hpc⟩ := S.smoothStructure.property.1.1 p.val
    obtain ⟨b, hb, hface⟩ := hB.2 c hc ⟨⟨p, hpc⟩⟩
    have hpb : p ∈ b.source := by rw [hface.1]; exact hpc
    have hbc (q : b.source) : q.val.val ∈ c.source := by
      change q.val ∈ Subtype.val ⁻¹' c.source
      rw [← hface.1]; exact q.property
    let incl : b.source → c.source := fun q => ⟨q.val.val, hbc q⟩
    have hinc : Continuous incl :=
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    let δ : b.source → ℝ := fun q => signValue (s.sign c hc (incl q)) * (-1 : ℝ)^(n+1)
    have hδ : IsLocallyConstant δ :=
      ((s.locallyConstant c hc).comp_continuous hinc).comp
        (fun x => signValue x * (-1 : ℝ)^(n+1))
    let g : ∀ q : b.source, DeterminantLine B q.val :=
      fun q => δ q • coordinateVector H b hb q
    refine ⟨b.source, b.open_source, hpb, g,
      coordinate_section_smooth_scalar B H b hb δ hδ, ?_⟩
    intro q
    obtain ⟨L, hL, _⟩ := differential_exists B S Subtype.val hB.1 q.val
    let E := K.equiv c hc q.val.val (hbc q)
    let v := -E.symm ((Pi.basisFun ℝ (Fin (n+1))) (Fin.last n))
    have hv : IsOutward S q.val v := by
      apply (outward_iff_coordinate S q.val c hc (hbc q) E
        (K.isCoordinates c hc q.val.val (hbc q)) v).mpr
      simp [v, Pi.basisFun_apply]
    apply (hr q.val L hL v hv (g q)).mpr
    change IsPositive (o.val q.val.val)
      (normalWedge L v (δ q • coordinateVector H b hb q))
    rw [normalWedge_smul_right,
      normalWedge_coordinateVector S B K H c hc b hb hface q.val q.property (hbc q) L hL,
      smul_smul]
    have hscalar : δ q * (-1 : ℝ)^(n+1) = signValue (s.sign c hc (incl q)) := by
      dsimp only [δ]
      rw [mul_assoc, ← mul_pow]
      norm_num
    rw [hscalar]
    exact hs K c hc (incl q)

theorem boundary_orientation :
    Specs.SmoothManifolds.Orientations.Boundary.boundary_orientationType.{u} := by
  have hout : Specs.SmoothManifolds.Orientations.Boundary.outward_independentType.{u} :=
    outward_independent
  intro n a M _ S o
  constructor
  · obtain ⟨B, hinc, hcharts⟩ := exists_boundary_smoothManifold S
    exact ⟨B, hinc, hcharts⟩
  intro B hB
  let r : RayField B := fun p => (pointwise_induced_ray hout S B hB o p).choose
  have hr (p : intrinsicBoundary S) : InducedRayPredicate B o p (r p) :=
    (pointwise_induced_ray hout S B hB o p).choose_spec.1
  have hcont := induced_rayfield_continuous S B hB o r hr
  obtain ⟨G, hG⟩ := (smooth_generators B r).mp hcont
  refine ⟨⟨r, hcont⟩, ⟨hr, G, hG⟩, ?_⟩
  intro q hq
  apply Subtype.ext
  funext p
  exact (pointwise_induced_ray hout S B hB o p).choose_spec.2 (q.val p) (hq.1 p)



/-- Restrict a smooth atlas to an open subspace, including the empty subspace. -/
theorem openSubsetAtlas_isContDiffAtlas {n : ℕ} {a : ModelKind}
    {M : Type u} [TopologicalSpace M] (S : SmoothManifold n a M)
    (U : Set M) (hU : IsOpen U) :
    IsContDiffAtlas (⊤ : ℕ∞) (openSubsetAtlas S.smoothStructure.val U hU) := by
  exact SmoothManifolds.openSubsetAtlas_isContDiffAtlas (⊤ : ℕ∞) _
    S.smoothStructure.property.1 U hU

/-- The inclusion of the natural interior has an invertible actual differential. -/
theorem interior_differential {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M)
    (R : SmoothManifold n a (manifoldInterior S)) (hR : IsInteriorStructure S R)
    (p : manifoldInterior S) :
    ∃ E : TangentSpace R p ≃ₗ[ℝ] TangentSpace S p.val,
      IsDifferential R S Subtype.val p E.toLinearMap := by
  obtain ⟨hU, hReq, hinc⟩ := hR
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p.val
  let d := c.subtypeRestr (s := ⟨manifoldInterior S, hU⟩) ⟨p⟩
  have hd : d ∈ R.smoothStructure.val := by
    rw [hReq]
    exact subset_maximalExtension (openSubsetAtlas_isContDiffAtlas S _ hU) ⟨⟨p⟩, c, hc, rfl⟩
  obtain ⟨K⟩ := TangentBundle.fiberCoordinates_exists R
  obtain ⟨H⟩ := TangentBundle.fiberCoordinates_exists S
  obtain ⟨L, hL, _⟩ := differential_exists R S Subtype.val hinc p
  have hpd : p ∈ d.source := by simpa only [d, OpenPartialHomeomorph.subtypeRestr_source, Set.mem_preimage] using hp
  let E := K.equiv d hd p hpd
  let F := H.equiv c hc p.val hp
  have heq (v : TangentSpace R p) : F (L v) = E v := by
    have h := differential_jacobian R S Subtype.val hinc p L hL d c hd hc hpd hp
      E F (K.isCoordinates d hd p hpd) (H.isCoordinates c hc p.val hp)
      univ id isOpen_univ (mem_univ _) contDiff_id.contDiffOn (Filter.Eventually.of_forall (fun _ => rfl)) v
    simpa only [fderiv_id, ContinuousLinearMap.id_apply] using h
  refine ⟨E.trans F.symm, ?_⟩
  have hmap : (E.trans F.symm).toLinearMap = L := by
    apply LinearMap.ext
    intro v
    apply F.injective
    simpa using (heq v).symm
  rw [hmap]
  exact hL

/-- Every natural interior restriction has empty intrinsic boundary. -/
theorem interior_boundary_empty {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M)
    (R : SmoothManifold n a (manifoldInterior S)) (hR : IsInteriorStructure S R) :
    intrinsicBoundary R = ∅ := by
  obtain ⟨hU, hReq, _⟩ := hR
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨c, hc, hpc⟩ := S.smoothStructure.property.1.1 p.val
  let d := c.subtypeRestr (s := ⟨manifoldInterior S, hU⟩) ⟨p⟩
  have hd : d ∈ R.smoothStructure.val := by
    rw [hReq]
    exact subset_maximalExtension (openSubsetAtlas_isContDiffAtlas S _ hU) ⟨⟨p⟩, c, hc, rfl⟩
  have hpd : p ∈ d.source := by simpa only [d, OpenPartialHomeomorph.subtypeRestr_source, Set.mem_preimage] using hpc
  have hface := (intrinsicBoundary_iff_chart R d hd p hpd).mp hp
  have hb : p.val ∈ intrinsicBoundary S :=
    (intrinsicBoundary_iff_chart S c hc p.val hpc).mpr hface
  have hnot : p.val ∉ intrinsicBoundary S := by
    have hi := p.property
    change p.val ∈ SmoothManifolds.manifoldInterior S at hi
    exact (Set.ext_iff.mp (compl_intrinsicBoundary S) p.val).mpr hi
  exact hnot hb

theorem interior_orientation :
    Specs.SmoothManifolds.Orientations.Boundary.interior_orientationType.{u} := by
  intro n a M _ S o
  have hU := isOpen_manifoldInterior S
  obtain ⟨R, _, hReq, hinc⟩ := exists_openSubset_smoothManifold S (manifoldInterior S) hU
  have hR : IsInteriorStructure S R := ⟨hU, hReq, hinc⟩
  choose E hE using interior_differential S R hR
  let r : Orientation R := ⟨(fun p => Module.Ray.map (determinantMap n (E p).symm) (o.val p.val)),
    OrientationProducts.pullbackRayField_continuous R S Subtype.val hinc o E hE⟩
  have hr : IsRestrictedOrientation o r := by
    intro p F hF
    have he : F = E p := LinearEquiv.toLinearMap_injective
      ((differential_exists R S Subtype.val hinc p).unique hF (hE p))
    subst F
    simpa only [r, LinearEquiv.symm_symm] using
      OrientationProducts.rayMap_determinant_symm_apply_apply n (E p).symm (o.val p.val)
  refine ⟨R, hR, interior_boundary_empty S R hR, (fun p => ⟨E p, hE p⟩), r, hr, ?_⟩
  intro t ht
  apply Subtype.ext
  funext p
  apply (Module.Ray.map (determinantMap n (E p))).injective
  exact (ht p (E p) (hE p)).trans (hr p (E p) (hE p)).symm

/-- Ordinary oriented products, with their smooth universal property. -/
theorem exists_oriented_product {m n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N)
    (o : Orientation S) (q : Orientation T)
    (h : intrinsicBoundary S = ∅ ∨ intrinsicBoundary T = ∅) :
    ∃ k, ∃ P : SmoothManifold (m+n) k (M × N),
      IsSmoothProduct S T P ∧ ∃ r : Orientation P, IsProductOrientation o q r := by
  obtain ⟨k, P, hf, hg, hp, hE, r, hr, _⟩ :=
    OrientationProducts.ordinary_product S T o q h
  exact ⟨k, P, ⟨hf, hg, hp, hE⟩, r, hr⟩

/-- The product universal property makes a map on the first factor smooth. -/
theorem smooth_product_map_left {l m n : ℕ} {a b c j k : ModelKind}
    {X M N : Type u} [TopologicalSpace X] [TopologicalSpace M] [TopologicalSpace N]
    (B : SmoothManifold l a X) (S : SmoothManifold m b M)
    (R : SmoothManifold n c N)
    (F : SmoothManifold (l+n) j (X × N)) (P : SmoothManifold (m+n) k (M × N))
    (hF : IsSmoothProduct B R F) (hP : IsSmoothProduct S R P)
    (f : X → M) (hf : IsSmoothMap B S f) :
    IsSmoothMap F P (fun p => (f p.1, p.2)) := by
  apply hP.2.2.1 F (fun p => f p.1) Prod.snd
  · exact manifoldContDiff_comp (⊤ : ℕ∞) _ _ _ B.smoothStructure.property.1.1
      Prod.fst f hF.1 hf
  · exact hF.2.1

/-- The product universal property makes a map on the second factor smooth. -/
theorem smooth_product_map_right {l m n : ℕ} {a b c j k : ModelKind}
    {X M N : Type u} [TopologicalSpace X] [TopologicalSpace M] [TopologicalSpace N]
    (R : SmoothManifold l a X) (B : SmoothManifold m b M)
    (S : SmoothManifold n c N)
    (F : SmoothManifold (l+m) j (X × M)) (P : SmoothManifold (l+n) k (X × N))
    (hF : IsSmoothProduct R B F) (hP : IsSmoothProduct R S P)
    (f : M → N) (hf : IsSmoothMap B S f) :
    IsSmoothMap F P (fun p => (p.1, f p.2)) := by
  apply hP.2.2.1 F Prod.fst (fun p => f p.2)
  · exact hF.1
  · exact manifoldContDiff_comp (⊤ : ℕ∞) _ _ _ B.smoothStructure.property.1.1
      Prod.snd f hF.2.1 hf

/-- Naturality of the two projection differentials for a first-factor map. -/
theorem product_differential_left {l m n : ℕ} {a b c j k : ModelKind}
    {X M N : Type u} [TopologicalSpace X] [TopologicalSpace M] [TopologicalSpace N]
    (B : SmoothManifold l a X) (S : SmoothManifold m b M)
    (R : SmoothManifold n c N)
    (F : SmoothManifold (l+n) j (X × N)) (P : SmoothManifold (m+n) k (M × N))
    (hF : IsSmoothProduct B R F) (hP : IsSmoothProduct S R P)
    (f : X → M) (hf : IsSmoothMap B S f) (p : X × N)
    (A : TangentSpace B p.1 →ₗ[ℝ] TangentSpace S (f p.1))
    (hA : IsDifferential B S f p.1 A)
    (E : TangentSpace F p ≃ₗ[ℝ] (TangentSpace B p.1 × TangentSpace R p.2))
    (hE : IsProductDifferential B R F p E)
    (D : TangentSpace P (f p.1, p.2) ≃ₗ[ℝ]
      (TangentSpace S (f p.1) × TangentSpace R p.2))
    (hD : IsProductDifferential S R P (f p.1, p.2) D)
    (L : TangentSpace F p →ₗ[ℝ] TangentSpace P (f p.1, p.2))
    (hL : IsDifferential F P (fun q => (f q.1, q.2)) p L) :
    ∀ z, D (L z) = (A (E z).1, (E z).2) := by
  have hj := smooth_product_map_left B S R F P hF hP f hf
  have hfs : IsSmoothMap F S (fun q => f q.1) :=
    manifoldContDiff_comp (⊤ : ℕ∞) _ _ _ B.smoothStructure.property.1.1
      Prod.fst f hF.1 hf
  have h1 := differential_comp F P S (fun q => (f q.1, q.2)) Prod.fst
    hj hP.1 p L ((LinearMap.fst ℝ _ _).comp D.toLinearMap) hL hD.1
  have h2 := differential_comp F B S Prod.fst f hF.1 hf p
    ((LinearMap.fst ℝ _ _).comp E.toLinearMap) A hE.1 hA
  have he1 := (differential_exists F S (fun q => f q.1) hfs p).unique h1 h2
  have h3 := differential_comp F P R (fun q => (f q.1, q.2)) Prod.snd
    hj hP.2.1 p L ((LinearMap.snd ℝ _ _).comp D.toLinearMap) hL hD.2
  have he2 := (differential_exists F R Prod.snd hF.2.1 p).unique h3 hE.2
  intro z
  exact Prod.ext (congrArg (fun K => K z) he1) (congrArg (fun K => K z) he2)

/-- Naturality of the two projection differentials for a second-factor map. -/
theorem product_differential_right {l m n : ℕ} {a b c j k : ModelKind}
    {X M N : Type u} [TopologicalSpace X] [TopologicalSpace M] [TopologicalSpace N]
    (R : SmoothManifold l a X) (B : SmoothManifold m b M)
    (S : SmoothManifold n c N)
    (F : SmoothManifold (l+m) j (X × M)) (P : SmoothManifold (l+n) k (X × N))
    (hF : IsSmoothProduct R B F) (hP : IsSmoothProduct R S P)
    (f : M → N) (hf : IsSmoothMap B S f) (p : X × M)
    (A : TangentSpace B p.2 →ₗ[ℝ] TangentSpace S (f p.2))
    (hA : IsDifferential B S f p.2 A)
    (E : TangentSpace F p ≃ₗ[ℝ] (TangentSpace R p.1 × TangentSpace B p.2))
    (hE : IsProductDifferential R B F p E)
    (D : TangentSpace P (p.1, f p.2) ≃ₗ[ℝ]
      (TangentSpace R p.1 × TangentSpace S (f p.2)))
    (hD : IsProductDifferential R S P (p.1, f p.2) D)
    (L : TangentSpace F p →ₗ[ℝ] TangentSpace P (p.1, f p.2))
    (hL : IsDifferential F P (fun q => (q.1, f q.2)) p L) :
    ∀ z, D (L z) = ((E z).1, A (E z).2) := by
  have hj := smooth_product_map_right R B S F P hF hP f hf
  have hfs : IsSmoothMap F S (fun q => f q.2) :=
    manifoldContDiff_comp (⊤ : ℕ∞) _ _ _ B.smoothStructure.property.1.1
      Prod.snd f hF.2.1 hf
  have h1 := differential_comp F P R (fun q => (q.1, f q.2)) Prod.fst
    hj hP.1 p L ((LinearMap.fst ℝ _ _).comp D.toLinearMap) hL hD.1
  have he1 := (differential_exists F R Prod.fst hF.1 p).unique h1 hE.1
  have h2 := differential_comp F P S (fun q => (q.1, f q.2)) Prod.snd
    hj hP.2.1 p L ((LinearMap.snd ℝ _ _).comp D.toLinearMap) hL hD.2
  have h3 := differential_comp F B S Prod.snd f hF.2.1 hf p
    ((LinearMap.snd ℝ _ _).comp E.toLinearMap) A hE.2 hA
  have he2 := (differential_exists F S (fun q => f q.2) hfs p).unique h2 h3
  intro z
  exact Prod.ext (congrArg (fun K => K z) he1) (congrArg (fun K => K z) he2)


@[simp] theorem coe_orderedWedge {V W : Type u}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (m n : ℕ) (η : ⋀[ℝ]^m V) (θ : ⋀[ℝ]^n W) :
    (orderedWedge m n V W η θ : ExteriorAlgebra ℝ (V × W)) =
      ExteriorAlgebra.map (LinearMap.inl ℝ V W) η.val *
      ExteriorAlgebra.map (LinearMap.inr ℝ V W) θ.val := by
  simp only [orderedWedge, LinearMap.compl₁₂_apply, exteriorPower.wedge,
    DirectSum.gMulLHom_apply_apply, SetLike.coe_gMul, exteriorPower.coe_map]

@[simp] theorem exteriorMap_comp_apply {V : Type u} {W : Type v} {X : Type w}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    [AddCommGroup X] [Module ℝ X]
    (A : V →ₗ[ℝ] W) (B : W →ₗ[ℝ] X) (x : ExteriorAlgebra ℝ V) :
    ExteriorAlgebra.map B (ExteriorAlgebra.map A x) =
      ExteriorAlgebra.map (B.comp A) x := by
  exact congrArg (fun F : ExteriorAlgebra ℝ V →ₐ[ℝ] ExteriorAlgebra ℝ X => F x)
    (ExteriorAlgebra.map_comp_map A B)

@[simp] theorem coe_determinantMap {V : Type u} {W : Type v}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (n : ℕ) (E : V ≃ₗ[ℝ] W) (η : ⋀[ℝ]^n V) :
    (determinantMap n E η : ExteriorAlgebra ℝ W) =
      ExteriorAlgebra.map E.toLinearMap η.val := exteriorPower.coe_map _ _

/-- Exterior insertion and transport commute with a change of ambient coordinates. -/
theorem normalWedge_map {V : Type u} {W : Type v} {X : Type w}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    [AddCommGroup X] [Module ℝ X]
    {d : ℕ} (D : W →ₗ[ℝ] V) (E : V ≃ₗ[ℝ] X) (v : V) (η : ⋀[ℝ]^d W) :
    determinantMap (d+1) E (normalWedge D v η) =
      normalWedge (E.toLinearMap.comp D) (E v) η := by
  apply Subtype.ext
  simp only [coe_determinantMap, coe_normalWedge, map_mul,
    ExteriorAlgebra.map_apply_ι, exteriorMap_comp_apply]
  rfl

/-- Insertion on an ordered direct sum, with the normal in the first summand. -/
theorem normalWedge_ordered_left {A V W : Type u}
    [AddCommGroup A] [Module ℝ A] [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W]
    (m n : ℕ) (I : A →ₗ[ℝ] V) (v : V)
    (η : ⋀[ℝ]^m A) (θ : ⋀[ℝ]^n W) :
    castExterior (Nat.add_right_comm m n 1)
      (normalWedge (I.prodMap LinearMap.id) (v, 0)
        (orderedWedge m n A W η θ)) =
      orderedWedge (m+1) n V W (normalWedge I v η) θ := by
  apply Subtype.ext
  simp only [coe_castExterior, coe_normalWedge, coe_orderedWedge, map_mul,
    exteriorMap_comp_apply, ExteriorAlgebra.map_apply_ι]
  have h1 : (I.prodMap (LinearMap.id : W →ₗ[ℝ] W)).comp (LinearMap.inl ℝ A W) =
      (LinearMap.inl ℝ V W).comp I := by ext a <;> simp
  have h2 : (I.prodMap (LinearMap.id : W →ₗ[ℝ] W)).comp (LinearMap.inr ℝ A W) =
      LinearMap.inr ℝ V W := by ext a <;> simp
  rw [h1, h2]
  exact (mul_assoc _ _ _).symm

/-- Insertion from the second summand crosses the m first-factor directions. -/
theorem normalWedge_ordered_right {A V W : Type u}
    [AddCommGroup A] [Module ℝ A] [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W]
    (m n : ℕ) (I : A →ₗ[ℝ] W) (v : W)
    (η : ⋀[ℝ]^m V) (θ : ⋀[ℝ]^n A) :
    castExterior (Nat.add_assoc m n 1)
      (normalWedge (LinearMap.id.prodMap I) (0, v)
        (orderedWedge m n V A η θ)) =
      (-1 : ℝ)^m • orderedWedge m (n+1) V W η (normalWedge I v θ) := by
  apply Subtype.ext
  simp only [coe_castExterior, coe_normalWedge, coe_orderedWedge, map_mul,
    exteriorMap_comp_apply, ExteriorAlgebra.map_apply_ι,
    Submodule.coe_smul_of_tower]
  have h1 : ((LinearMap.id : V →ₗ[ℝ] V).prodMap I).comp (LinearMap.inl ℝ V A) =
      LinearMap.inl ℝ V W := by ext a <;> simp
  have h2 : ((LinearMap.id : V →ₗ[ℝ] V).prodMap I).comp (LinearMap.inr ℝ V A) =
      (LinearMap.inr ℝ V W).comp I := by ext a <;> simp
  rw [h1, h2]
  have hc := ExteriorAlgebraResults.homogeneous_anticomm (V × W) 1 m
    (exteriorPower.ιMulti ℝ 1 (fun _ => (0,v)))
    (exteriorPower.map m (LinearMap.inl ℝ V W) η)
  simp only [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, mul_one,
    exteriorPower.coe_map, Nat.one_mul] at hc
  rw [← mul_assoc, hc, smul_mul_assoc, mul_assoc]
  rfl


@[simp] theorem determinantMap_cast {V : Type u} {W : Type v}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    {i j : ℕ} (h : i = j) (E : V ≃ₗ[ℝ] W) (x : ⋀[ℝ]^i V) :
    determinantMap j E (castExterior h x) = castExterior h (determinantMap i E x) := by
  subst h
  rfl

theorem normalWedge_source_equiv {V : Type u} {W : Type v} {Y : Type w}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    [AddCommGroup Y] [Module ℝ Y]
    {d : ℕ} (D : Y →ₗ[ℝ] V) (F : Y ≃ₗ[ℝ] W) (v : V) (η : ⋀[ℝ]^d W) :
    normalWedge D v (determinantMap d F.symm η) =
      normalWedge (D.comp F.symm.toLinearMap) v η := by
  apply Subtype.ext
  simp only [coe_normalWedge, coe_determinantMap, exteriorMap_comp_apply]

theorem normalWedge_product_left {A V W X Y : Type u}
    [AddCommGroup A] [Module ℝ A] [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] [AddCommGroup X] [Module ℝ X]
    [AddCommGroup Y] [Module ℝ Y] [FiniteDimensional ℝ Y]
    (m n : ℕ) (hd : finrank ℝ Y = m+n) (I : A →ₗ[ℝ] V)
    (D : Y →ₗ[ℝ] X) (E : X ≃ₗ[ℝ] V × W) (F : Y ≃ₗ[ℝ] A × W)
    (hD : ∀ z, E (D z) = (I (F z).1, (F z).2))
    (v : X) (η : ⋀[ℝ]^m A) (θ : ⋀[ℝ]^n W) :
    castExterior (Nat.add_right_comm m n 1)
      (normalWedge D v (determinantMap (m+n) F.symm (orderedWedge m n A W η θ))) =
    determinantMap ((m+1)+n) E.symm
      (orderedWedge (m+1) n V W (normalWedge I (E v).1 η) θ) := by
  let z : Y := F.symm (0, (E v).2)
  have hv : v = E.symm ((E v).1, 0) + D z := by
    apply E.injective
    simp only [map_add, E.apply_symm_apply, hD, z, F.apply_symm_apply, map_zero]
    ext <;> simp
  have hnormal : normalWedge D v
      (determinantMap (m+n) F.symm (orderedWedge m n A W η θ)) =
      normalWedge D (E.symm ((E v).1, 0))
        (determinantMap (m+n) F.symm (orderedWedge m n A W η θ)) := by
    conv_lhs => rw [hv]
    rw [normalWedge_add, normalWedge_tangent hd, add_zero]
  rw [hnormal]
  apply (determinantMap ((m+1)+n) E).injective
  rw [OrientationProducts.determinantMap_apply_symm_apply, determinantMap_cast,
    normalWedge_source_equiv, normalWedge_map]
  have hcomp : E.toLinearMap.comp (D.comp F.symm.toLinearMap) =
      I.prodMap (LinearMap.id : W →ₗ[ℝ] W) := by
    apply LinearMap.ext
    intro a
    change E (D (F.symm a)) = _
    rw [hD, F.apply_symm_apply]
    rfl
  rw [hcomp, E.apply_symm_apply]
  exact normalWedge_ordered_left m n I (E v).1 η θ

theorem normalWedge_product_right {A V W X Y : Type u}
    [AddCommGroup A] [Module ℝ A] [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] [AddCommGroup X] [Module ℝ X]
    [AddCommGroup Y] [Module ℝ Y] [FiniteDimensional ℝ Y]
    (m n : ℕ) (hd : finrank ℝ Y = m+n) (I : A →ₗ[ℝ] W)
    (D : Y →ₗ[ℝ] X) (E : X ≃ₗ[ℝ] V × W) (F : Y ≃ₗ[ℝ] V × A)
    (hD : ∀ z, E (D z) = ((F z).1, I (F z).2))
    (v : X) (η : ⋀[ℝ]^m V) (θ : ⋀[ℝ]^n A) :
    castExterior (Nat.add_assoc m n 1)
      (normalWedge D v (determinantMap (m+n) F.symm (orderedWedge m n V A η θ))) =
    (-1 : ℝ)^m • determinantMap (m+(n+1)) E.symm
      (orderedWedge m (n+1) V W η (normalWedge I (E v).2 θ)) := by
  let z : Y := F.symm ((E v).1, 0)
  have hv : v = E.symm (0, (E v).2) + D z := by
    apply E.injective
    simp only [map_add, E.apply_symm_apply, hD, z, F.apply_symm_apply, map_zero]
    ext <;> simp
  have hnormal : normalWedge D v
      (determinantMap (m+n) F.symm (orderedWedge m n V A η θ)) =
      normalWedge D (E.symm (0, (E v).2))
        (determinantMap (m+n) F.symm (orderedWedge m n V A η θ)) := by
    conv_lhs => rw [hv]
    rw [normalWedge_add, normalWedge_tangent hd, add_zero]
  rw [hnormal]
  apply (determinantMap (m+(n+1)) E).injective
  rw [map_smul, OrientationProducts.determinantMap_apply_symm_apply,
    determinantMap_cast, normalWedge_source_equiv, normalWedge_map]
  have hcomp : E.toLinearMap.comp (D.comp F.symm.toLinearMap) =
      (LinearMap.id : V →ₗ[ℝ] V).prodMap I := by
    apply LinearMap.ext
    intro a
    change E (D (F.symm a)) = _
    rw [hD, F.apply_symm_apply]
    rfl
  rw [hcomp, E.apply_symm_apply]
  exact normalWedge_ordered_right m n I (E v).2 η θ


@[simp] theorem castExterior_add {V : Type u} [AddCommGroup V] [Module ℝ V]
    {i j : ℕ} (h : i = j) (x y : ⋀[ℝ]^i V) :
    castExterior h (x+y) = castExterior h x + castExterior h y := by subst h; rfl

@[simp] theorem castExterior_smul {V : Type u} [AddCommGroup V] [Module ℝ V]
    {i j : ℕ} (h : i = j) (t : ℝ) (x : ⋀[ℝ]^i V) :
    castExterior h (t • x) = t • castExterior h x := by subst h; rfl

def faceWedgeMap {V W : Type u} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] {d e : ℕ} (h : e+1=d)
    (D : W →ₗ[ℝ] V) (v : V) : (⋀[ℝ]^e W) →ₗ[ℝ] (⋀[ℝ]^d V) where
  toFun := fun η => castExterior h (normalWedge D v η)
  map_add' x y := by apply Subtype.ext; simp [map_add, mul_add]
  map_smul' t x := by apply Subtype.ext; simp

/-- A map from a line preserves positivity on every vector once it does so on
one positive generator. The target need not itself be one dimensional. -/
theorem positive_linearMap_iff_of_generator {V : Type u} {W : Type v}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    [FiniteDimensional ℝ V] (hd : Module.finrank ℝ V = 1)
    (A : V →ₗ[ℝ] W) (r : Module.Ray ℝ V) (s : Module.Ray ℝ W)
    (x : V) (hx : IsPositive r x) (hAx : IsPositive s (A x)) :
    ∀ y, IsPositive r y ↔ IsPositive s (A y) := by
  obtain ⟨hx0, hxr⟩ := hx
  obtain ⟨hAx0, hAs⟩ := hAx
  intro y
  rw [← hxr, ← hAs, positive_iff_pos_smul x hx0 y,
    positive_iff_pos_smul (A x) hAx0 (A y)]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, A.map_smul t x⟩
  · rintro ⟨t, ht, hAy⟩
    obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hd hx0 y
    have hcy : c • A x = A y := by rw [← A.map_smul, hc]
    have hct : c = t := smul_left_injective ℝ hAx0 (hcy.trans hAy)
    exact ⟨t, ht, by rw [← hct]; exact hc.symm⟩


/-- The algebraic positivity comparison for a first-factor boundary face. -/
theorem face_positive_left {A V W X Y : Type u}
    [AddCommGroup A] [Module ℝ A] [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] [AddCommGroup X] [Module ℝ X]
    [AddCommGroup Y] [Module ℝ Y] [FiniteDimensional ℝ Y]
    (m n : ℕ) (hd : finrank ℝ Y = m+n) (I : A →ₗ[ℝ] V)
    (D : Y →ₗ[ℝ] X) (E : X ≃ₗ[ℝ] V × W) (F : Y ≃ₗ[ℝ] A × W)
    (hD : ∀ z, E (D z) = (I (F z).1, (F z).2))
    (v : X) (rA : Module.Ray ℝ (⋀[ℝ]^m A))
    (rV : Module.Ray ℝ (⋀[ℝ]^(m+1) V)) (rW : Module.Ray ℝ (⋀[ℝ]^n W))
    (rY : Module.Ray ℝ (⋀[ℝ]^(m+n) Y))
    (rX : Module.Ray ℝ (⋀[ℝ]^((m+1)+n) X))
    (hI : ∀ η, IsPositive rA η ↔ IsPositive rV (normalWedge I (E v).1 η))
    (hF : ∀ η θ, IsPositive rA η → IsPositive rW θ →
      IsPositive rY (determinantMap (m+n) F.symm (orderedWedge m n A W η θ)))
    (hE : ∀ α θ, IsPositive rV α → IsPositive rW θ →
      IsPositive rX (determinantMap ((m+1)+n) E.symm (orderedWedge (m+1) n V W α θ))) :
    ∀ ζ, IsPositive rY ζ ↔ IsPositive rX
      (castExterior (Nat.add_right_comm m n 1) (normalWedge D v ζ)) := by
  let η := rA.someVector
  let θ := rW.someVector
  have hη : IsPositive rA η := ⟨rA.someVector_ne_zero, rA.someVector_ray⟩
  have hθ : IsPositive rW θ := ⟨rW.someVector_ne_zero, rW.someVector_ray⟩
  have hgen := hF η θ hη hθ
  have himage : IsPositive rX
      (faceWedgeMap (Nat.add_right_comm m n 1) D v
        (determinantMap (m+n) F.symm (orderedWedge m n A W η θ))) := by
    change IsPositive rX (castExterior _ (normalWedge _ _ _))
    rw [normalWedge_product_left m n hd I D E F hD]
    exact hE _ θ ((hI η).mp hη) hθ
  have hdim : finrank ℝ (⋀[ℝ]^(m+n) Y) = 1 := by simp [exteriorPower.finrank_eq, hd]
  exact positive_linearMap_iff_of_generator hdim
    (faceWedgeMap (Nat.add_right_comm m n 1) D v) rY rX _ hgen himage

/-- The algebraic positivity comparison for a second-factor boundary face. -/
theorem face_positive_right {A V W X Y : Type u}
    [AddCommGroup A] [Module ℝ A] [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] [AddCommGroup X] [Module ℝ X]
    [AddCommGroup Y] [Module ℝ Y] [FiniteDimensional ℝ Y]
    (m n : ℕ) (hd : finrank ℝ Y = m+n) (I : A →ₗ[ℝ] W)
    (D : Y →ₗ[ℝ] X) (E : X ≃ₗ[ℝ] V × W) (F : Y ≃ₗ[ℝ] V × A)
    (hD : ∀ z, E (D z) = ((F z).1, I (F z).2))
    (v : X) (rA : Module.Ray ℝ (⋀[ℝ]^n A))
    (rV : Module.Ray ℝ (⋀[ℝ]^m V)) (rW : Module.Ray ℝ (⋀[ℝ]^(n+1) W))
    (rY : Module.Ray ℝ (⋀[ℝ]^(m+n) Y))
    (rX : Module.Ray ℝ (⋀[ℝ]^(m+(n+1)) X))
    (hI : ∀ θ, IsPositive rA θ ↔ IsPositive rW (normalWedge I (E v).2 θ))
    (hF : ∀ η θ, IsPositive rV η → IsPositive rA θ →
      IsPositive rY (determinantMap (m+n) F.symm (orderedWedge m n V A η θ)))
    (hE : ∀ η β, IsPositive rV η → IsPositive rW β →
      IsPositive rX (determinantMap (m+(n+1)) E.symm (orderedWedge m (n+1) V W η β))) :
    ∀ ζ, IsPositive (if Even m then rY else -rY) ζ ↔ IsPositive rX
      (castExterior (Nat.add_assoc m n 1) (normalWedge D v ζ)) := by
  let η := rV.someVector
  let θ := rA.someVector
  have hη : IsPositive rV η := ⟨rV.someVector_ne_zero, rV.someVector_ray⟩
  have hθ : IsPositive rA θ := ⟨rA.someVector_ne_zero, rA.someVector_ray⟩
  let g := determinantMap (m+n) F.symm (orderedWedge m n V A η θ)
  have hg : IsPositive rY g := hF η θ hη hθ
  have hgen : IsPositive (if Even m then rY else -rY) ((-1 : ℝ)^m • g) := by
    rcases m.even_or_odd with hm | hm
    · simpa only [if_pos hm, hm.neg_one_pow, one_smul] using hg
    · rw [if_neg (Nat.not_even_iff_odd.mpr hm), hm.neg_one_pow]
      change IsPositive (-rY) ((-1 : ℝ) • g)
      rw [neg_one_smul ℝ g]
      exact ⟨neg_ne_zero.mpr hg.choose, by
        simpa only [neg_rayOfNeZero] using congrArg (fun r => -r) hg.choose_spec⟩
  let H := faceWedgeMap (Nat.add_assoc m n 1) D v
  have himage : IsPositive rX (H ((-1 : ℝ)^m • g)) := by
    rw [map_smul]
    change IsPositive rX ((-1 : ℝ)^m • castExterior (Nat.add_assoc m n 1) (normalWedge D v g))
    dsimp only [g]
    rw [normalWedge_product_right m n hd I D E F hD, smul_smul]
    have hs : (-1 : ℝ)^m * (-1 : ℝ)^m = 1 := by rw [← mul_pow]; norm_num
    rw [hs, one_smul]
    exact hE η _ hη ((hI θ).mp hθ)
  have hdim : finrank ℝ (⋀[ℝ]^(m+n) Y) = 1 := by simp [exteriorPower.finrank_eq, hd]
  exact positive_linearMap_iff_of_generator hdim H _ rX _ hgen himage


theorem product_left_face_orientation {m n : ℕ} {a b j k : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold (m+1) a M) (R : SmoothManifold n b N)
    (B : SmoothManifold m .euclidean (intrinsicBoundary S))
    (P : SmoothManifold ((m+1)+n) k (M × N))
    (F : SmoothManifold (m+n) j (intrinsicBoundary S × N))
    (hB : IsNaturalBoundary S B) (hP : IsSmoothProduct S R P)
    (hF : IsSmoothProduct B R F)
    (o : Orientation S) (r : Orientation R) (s : Orientation B)
    (oP : Orientation P) (oF : Orientation F)
    (hi : IsInducedOrientation o s)
    (hoP : IsProductOrientation o r oP) (hoF : IsProductOrientation s r oF) :
    IsFaceOrientation (Nat.add_right_comm m n 1) P F (fun p => (p.1.val, p.2))
      (fun p v => ∃ E, IsProductDifferential S R P (p.1.val, p.2) E ∧
        IsOutward S p.1 (E v).1) oP oF.val := by
  intro p L hL v hv ζ
  obtain ⟨D, hD, hv⟩ := hv
  obtain ⟨E, hE⟩ := hF.2.2.2 p
  obtain ⟨I, hI, _⟩ := differential_exists B S Subtype.val hB.1 p.1
  letI := (tangent_dimension F p).1
  have hblock := product_differential_left B S R F P hF hP Subtype.val hB.1
    p I hI E hE D hD L hL
  exact face_positive_left m n (tangent_dimension F p).2 I L D E hblock v
    (s.val p.1) (o.val p.1.val) (r.val p.2) (oF.val p) (oP.val (p.1.val, p.2))
    (fun η => hi p.1 I hI (D v).1 hv η)
    (hoF p E hE) (hoP (p.1.val, p.2) D hD) ζ

theorem product_right_face_orientation {m n : ℕ} {a b j k : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (R : SmoothManifold m a M) (T : SmoothManifold (n+1) b N)
    (B : SmoothManifold n .euclidean (intrinsicBoundary T))
    (P : SmoothManifold (m+(n+1)) k (M × N))
    (F : SmoothManifold (m+n) j (M × intrinsicBoundary T))
    (hB : IsNaturalBoundary T B) (hP : IsSmoothProduct R T P)
    (hF : IsSmoothProduct R B F)
    (r : Orientation R) (q : Orientation T) (s : Orientation B)
    (oP : Orientation P) (oF : Orientation F)
    (hi : IsInducedOrientation q s)
    (hoP : IsProductOrientation r q oP) (hoF : IsProductOrientation r s oF) :
    IsFaceOrientation (Nat.add_assoc m n 1) P F (fun p => (p.1, p.2.val))
      (fun p v => ∃ E, IsProductDifferential R T P (p.1, p.2.val) E ∧
        IsOutward T p.2 (E v).2) oP
      (fun p => if Even m then oF.val p else -oF.val p) := by
  intro p L hL v hv ζ
  obtain ⟨D, hD, hv⟩ := hv
  obtain ⟨E, hE⟩ := hF.2.2.2 p
  obtain ⟨I, hI, _⟩ := differential_exists B T Subtype.val hB.1 p.2
  letI := (tangent_dimension F p).1
  have hblock := product_differential_right R B T F P hF hP Subtype.val hB.1
    p I hI E hE D hD L hL
  exact face_positive_right m n (tangent_dimension F p).2 I L D E hblock v
    (s.val p.2) (r.val p.1) (q.val p.2.val) (oF.val p) (oP.val (p.1, p.2.val))
    (fun θ => hi p.2 I hI (D v).2 hv θ)
    (hoF p E hE) (hoP (p.1, p.2.val) D hD) ζ

theorem product_left_face :
    Specs.SmoothManifolds.Orientations.Boundary.product_left_faceType.{u} := by
  intro m n a b M N _ _ S T B hB o q s hi R r hR hr
  have hrempty := interior_boundary_empty T R hR
  obtain ⟨k, P, hP, oP, hoP⟩ := exists_oriented_product S R o r (Or.inr hrempty)
  obtain ⟨j, F, hF, oF, hoF⟩ := exists_oriented_product B R s r (Or.inr hrempty)
  refine ⟨k, P, j, F, hP, hF,
    smooth_product_map_left B S R F P hF hP Subtype.val hB.1, oP, oF, hoP, hoF, ?_⟩
  exact product_left_face_orientation S R B P F hB hP hF o r s oP oF hi hoP hoF

theorem product_right_face :
    Specs.SmoothManifolds.Orientations.Boundary.product_right_faceType.{u} := by
  intro m n a b M N _ _ S T B hB o q s hi R r hR hr
  have hrempty := interior_boundary_empty S R hR
  obtain ⟨k, P, hP, oP, hoP⟩ := exists_oriented_product R T r q (Or.inl hrempty)
  obtain ⟨j, F, hF, oF, hoF⟩ := exists_oriented_product R B r s (Or.inl hrempty)
  let tF : Orientation F := if Even m then oF else opposite oF
  have htF (p) : tF.val p = if Even m then oF.val p else -oF.val p := by
    by_cases hm : Even m <;> simp [tF, hm]
  refine ⟨k, P, j, F, hP, hF,
    smooth_product_map_right R B T F P hF hP Subtype.val hB.1,
    oP, oF, tF, hoP, hoF, htF, ?_⟩
  have he : tF.val = (fun p => if Even m then oF.val p else -oF.val p) := funext htF
  rw [he]
  exact product_right_face_orientation R T B P F hB hP hF r q s oP oF hi hoP hoF


private def intervalLeftChart (a b : ℝ) (hab : a < b) :
    ModelChart 1 .halfSpace (Icc a b) where
  toFun x := ⟨fun _ => x.val-a, by
    change 0 ≤ x.val-a
    exact sub_nonneg.mpr x.property.1⟩
  invFun y := ⟨a + min (y.val 0) (b-a), by
    constructor
    · have hy : 0 ≤ y.val 0 := y.property
      have : 0 ≤ min (y.val 0) (b-a) := le_min hy (sub_nonneg.mpr hab.le)
      linarith
    · have := min_le_right (y.val 0) (b-a)
      linarith⟩
  source := {x | x.val < b}
  target := {y | y.val 0 < b-a}
  map_source' x hx := by
    change x.val < b at hx
    change x.val-a < b-a
    linarith
  map_target' y hy := by
    change a + min (y.val 0) (b-a) < b
    have := min_le_left (y.val 0) (b-a)
    change y.val 0 < b-a at hy
    linarith
  left_inv' x hx := by
    apply Subtype.ext
    change a + min (x.val-a) (b-a) = x.val
    rw [min_eq_left (sub_le_sub_right x.property.2 a)]
    ring
  right_inv' y hy := by
    apply Subtype.ext
    funext j
    change a + min (y.val 0) (b-a) - a = y.val j
    have : y.val 0 ≤ b-a := le_of_lt hy
    rw [min_eq_left this]
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    ring
  open_source := isOpen_lt continuous_subtype_val continuous_const
  open_target := isOpen_lt (continuous_apply 0 |>.comp continuous_subtype_val) continuous_const
  continuousOn_toFun := by
    apply Continuous.continuousOn
    apply Continuous.subtype_mk
    apply continuous_pi
    intro j
    exact continuous_subtype_val.sub continuous_const
  continuousOn_invFun := by
    apply Continuous.continuousOn
    apply Continuous.subtype_mk
    exact continuous_const.add ((continuous_apply 0 |>.comp continuous_subtype_val).min continuous_const)

private def intervalRightChart (a b : ℝ) (hab : a < b) :
    ModelChart 1 .halfSpace (Icc a b) where
  toFun x := ⟨fun _ => b-x.val, by
    change 0 ≤ b-x.val
    exact sub_nonneg.mpr x.property.2⟩
  invFun y := ⟨b - min (y.val 0) (b-a), by
    constructor
    · have := min_le_right (y.val 0) (b-a)
      linarith
    · have hy : 0 ≤ y.val 0 := y.property
      have : 0 ≤ min (y.val 0) (b-a) := le_min hy (sub_nonneg.mpr hab.le)
      linarith⟩
  source := {x | a < x.val}
  target := {y | y.val 0 < b-a}
  map_source' x hx := by
    change a < x.val at hx
    change b-x.val < b-a
    linarith
  map_target' y hy := by
    change a < b - min (y.val 0) (b-a)
    have := min_le_left (y.val 0) (b-a)
    change y.val 0 < b-a at hy
    linarith
  left_inv' x hx := by
    apply Subtype.ext
    change b - min (b-x.val) (b-a) = x.val
    rw [min_eq_left (sub_le_sub_left x.property.1 b)]
    ring
  right_inv' y hy := by
    apply Subtype.ext
    funext j
    change b - (b - min (y.val 0) (b-a)) = y.val j
    have : y.val 0 ≤ b-a := le_of_lt hy
    rw [min_eq_left this]
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    ring
  open_source := isOpen_lt continuous_const continuous_subtype_val
  open_target := isOpen_lt (continuous_apply 0 |>.comp continuous_subtype_val) continuous_const
  continuousOn_toFun := by
    apply Continuous.continuousOn
    apply Continuous.subtype_mk
    apply continuous_pi
    intro j
    exact continuous_const.sub continuous_subtype_val
  continuousOn_invFun := by
    apply Continuous.continuousOn
    apply Continuous.subtype_mk
    exact continuous_const.sub ((continuous_apply 0 |>.comp continuous_subtype_val).min continuous_const)


private theorem chart_compatible_self {n : ℕ} {k : ModelKind} {X : Type*}
    [TopologicalSpace X] (c : ModelChart n k X) : ContDiffCompatible (⊤ : ℕ∞) c c := by
  apply contDiffCompatible_of_germs
  · intro x hx hx'
    exact LocalCoordinateExtension.self _ _ _
  · intro x hx hx'
    exact LocalCoordinateExtension.self _ _ _

private theorem intervalChartCompatible (a b : ℝ) (hab : a < b) :
    ContDiffCompatible (⊤ : ℕ∞) (intervalLeftChart a b hab) (intervalRightChart a b hab) := by
  apply contDiffCompatible_of_germs
  · intro x hx hx'
    refine ⟨univ, isOpen_univ, mem_univ _, fun z => (fun j => b-a-z j), ?_, ?_⟩
    · exact (contDiff_const.sub contDiff_id).contDiffOn
    · exact Filter.Eventually.of_forall (fun y => by funext j; dsimp [intervalLeftChart, intervalRightChart]; ring)
  · intro x hx hx'
    refine ⟨univ, isOpen_univ, mem_univ _, fun z => (fun j => b-a-z j), ?_, ?_⟩
    · exact (contDiff_const.sub contDiff_id).contDiffOn
    · exact Filter.Eventually.of_forall (fun y => by funext j; dsimp [intervalLeftChart, intervalRightChart]; ring)

private theorem intervalAtlas (a b : ℝ) (hab : a < b) :
    IsContDiffAtlas (⊤ : ℕ∞) {intervalLeftChart a b hab, intervalRightChart a b hab} := by
  constructor
  · intro x
    by_cases hx : x.val < b
    · exact ⟨intervalLeftChart a b hab, by simp, hx⟩
    · refine ⟨intervalRightChart a b hab, by simp, ?_⟩
      change a < x.val
      linarith [x.property.2]
  · intro c hc d hd
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc hd
    rcases hc with rfl | rfl <;> rcases hd with rfl | rfl
    · exact chart_compatible_self _
    · exact intervalChartCompatible a b hab
    · exact contDiffCompatible_symm (intervalChartCompatible a b hab)
    · exact chart_compatible_self _

private def standardInterval (a b : ℝ) (hab : a < b) :
    SmoothManifold 1 .halfSpace (Icc a b) where
  topologicalManifold := ⟨inferInstance, inferInstance,
    {intervalLeftChart a b hab, intervalRightChart a b hab}, (intervalAtlas a b hab).1⟩
  smoothStructure := ⟨maximalExtension (⊤ : ℕ∞)
    {intervalLeftChart a b hab, intervalRightChart a b hab},
    maximalExtension_isMaximal (intervalAtlas a b hab)⟩



private theorem standardInterval_spec (a b : ℝ) (hab : a < b) :
    IsStandardInterval a b (standardInterval a b hab)
      (intervalLeftChart a b hab) (intervalRightChart a b hab) := by
  exact ⟨subset_maximalExtension (intervalAtlas a b hab) (by simp),
    subset_maximalExtension (intervalAtlas a b hab) (by simp), rfl, rfl,
    (fun _ _ => rfl), (fun _ _ => rfl), rfl⟩

private theorem standardInterval_boundary (a b : ℝ) (hab : a < b) :
    intrinsicBoundary (standardInterval a b hab) = {x | x.val = a ∨ x.val = b} := by
  let S := standardInterval a b hab
  let l := intervalLeftChart a b hab
  let r := intervalRightChart a b hab
  have hl : l ∈ S.smoothStructure.val := (standardInterval_spec a b hab).1
  have hr : r ∈ S.smoothStructure.val := (standardInterval_spec a b hab).2.1
  ext x
  by_cases hx : x.val < b
  · have hxl : x ∈ l.source := hx
    rw [intrinsicBoundary_iff_chart S l hl x hxl]
    change x.val-a = 0 ↔ x.val = a ∨ x.val = b
    constructor
    · intro he; exact Or.inl (sub_eq_zero.mp he)
    · rintro (he | he)
      · exact sub_eq_zero.mpr he
      · exact False.elim (hx.ne he)
  · have hxr : x ∈ r.source := by change a < x.val; linarith [x.property.2]
    rw [intrinsicBoundary_iff_chart S r hr x hxr]
    change b-x.val = 0 ↔ x.val = a ∨ x.val = b
    constructor
    · intro he; exact Or.inr (sub_eq_zero.mp he).symm
    · rintro (he | he)
      · change a < x.val at hxr; linarith
      · exact sub_eq_zero.mpr he.symm



private theorem interval_transition_det (a b : ℝ) (hab : a < b)
    (K : FiberCoordinates (standardInterval a b hab))
    (hl : intervalLeftChart a b hab ∈ (standardInterval a b hab).smoothStructure.val)
    (hr : intervalRightChart a b hab ∈ (standardInterval a b hab).smoothStructure.val)
    (p : ↥((intervalLeftChart a b hab).source ∩ (intervalRightChart a b hab).source)) :
    transitionDeterminant K (intervalLeftChart a b hab) (intervalRightChart a b hab) hl hr p = -1 := by
  let S := standardInterval a b hab
  let F : Euclidean 1 → Euclidean 1 := fun z => (fun _ => b-a) - z
  have hF : ContDiffOn ℝ (⊤ : ℕ∞) F univ := (contDiff_const.sub contDiff_id).contDiffOn
  have hrep : (fun q => F ((intervalLeftChart a b hab) q).val) =ᶠ[nhds p.val]
      (fun q => ((intervalRightChart a b hab) q).val) :=
    Filter.Eventually.of_forall (fun q => by funext j; dsimp [F, intervalLeftChart, intervalRightChart]; ring)
  rw [transition_jacobian S K (intervalLeftChart a b hab) (intervalRightChart a b hab) hl hr p
    univ F isOpen_univ (mem_univ _) hF hrep]
  have hder : fderiv ℝ F ((intervalLeftChart a b hab) p.val).val =
      -(ContinuousLinearMap.id ℝ (Euclidean 1)) := by
    exact fderiv_const_sub (fun _ : Fin 1 => b-a) |>.trans (congrArg Neg.neg fderiv_id)
  rw [hder]
  change LinearMap.det (-LinearMap.id : Euclidean 1 →ₗ[ℝ] Euclidean 1) = -1
  rw [← neg_one_smul ℝ (LinearMap.id : Euclidean 1 →ₗ[ℝ] Euclidean 1), LinearMap.det_smul]
  simp

private theorem coordinateVector_eq_neg_of_transition {n : ℕ} {k : ModelKind} {X : Type*}
    [TopologicalSpace X] {S : SmoothManifold n k X} (K : FiberCoordinates S)
    (c d : ModelChart n k X) (hc : c ∈ S.smoothStructure.val) (hd : d ∈ S.smoothStructure.val)
    (p : ↥(c.source ∩ d.source)) (ht : transitionDeterminant K c d hc hd p = -1) :
    coordinateVector K c hc ⟨p.val,p.property.1⟩ = -coordinateVector K d hd ⟨p.val,p.property.2⟩ := by
  calc
    _ = determinantCoefficient K d hd ⟨p.val,p.property.2⟩
        (coordinateVector K c hc ⟨p.val,p.property.1⟩) • coordinateVector K d hd ⟨p.val,p.property.2⟩ :=
      determinant_eq_coefficient_smul K d hd ⟨p.val,p.property.2⟩ _
    _ = transitionDeterminant K c d hc hd p • coordinateVector K d hd ⟨p.val,p.property.2⟩ :=
      congrArg (fun δ => δ • coordinateVector K d hd ⟨p.val,p.property.2⟩)
        (coefficient_coordinateVector_transition K c d hc hd p)
    _ = -coordinateVector K d hd ⟨p.val,p.property.2⟩ := by
      simpa only [ht] using neg_one_smul ℝ (coordinateVector K d hd ⟨p.val,p.property.2⟩)

private theorem interval_coordinate_relation (a b : ℝ) (hab : a < b)
    (K : FiberCoordinates (standardInterval a b hab))
    (hl : intervalLeftChart a b hab ∈ (standardInterval a b hab).smoothStructure.val)
    (hr : intervalRightChart a b hab ∈ (standardInterval a b hab).smoothStructure.val)
    (p : ↥((intervalLeftChart a b hab).source ∩ (intervalRightChart a b hab).source)) :
    coordinateVector K (intervalLeftChart a b hab) hl ⟨p.val,p.property.1⟩ =
      -coordinateVector K (intervalRightChart a b hab) hr ⟨p.val,p.property.2⟩ :=
  coordinateVector_eq_neg_of_transition K (intervalLeftChart a b hab)
    (intervalRightChart a b hab) hl hr p (interval_transition_det a b hab K hl hr p)

set_option maxHeartbeats 3000000 in
private theorem interval_positive_orientation (a b : ℝ) (hab : a < b) :
    ∃ (o : Orientation (standardInterval a b hab)) (s : SignedCharts (standardInterval a b hab)),
      RepresentsSignedCharts o.val s ∧
      (∀ (hl : intervalLeftChart a b hab ∈ (standardInterval a b hab).smoothStructure.val) p,
        s.sign (intervalLeftChart a b hab) hl p = true) ∧
      (∀ (hr : intervalRightChart a b hab ∈ (standardInterval a b hab).smoothStructure.val) p,
        s.sign (intervalRightChart a b hab) hr p = false) := by
  let S := standardInterval a b hab
  let l := intervalLeftChart a b hab
  let r := intervalRightChart a b hab
  have hl : l ∈ S.smoothStructure.val := (standardInterval_spec a b hab).1
  have hr : r ∈ S.smoothStructure.val := (standardInterval_spec a b hab).2.1
  obtain ⟨K⟩ := TangentBundle.fiberCoordinates_exists S
  let C : Bool → ModelChart 1 .halfSpace (Icc a b) := fun i => if i then l else r
  have hC : ∀ i, C i ∈ S.smoothStructure.val := by intro i; cases i <;> assumption
  let G : LocalGenerators S := {
    index := Bool
    domain i := (C i).source
    isOpen_domain i := (C i).open_source
    cover x := by
      by_cases hx : x.val < b
      · exact ⟨true, hx⟩
      · refine ⟨false, ?_⟩
        change a < x.val
        linarith [x.property.2]
    generator i p := signValue i • coordinateVector K (C i) (hC i) p
    nonzero i p := smul_ne_zero (signValue_ne_zero i) (coordinateVector_ne_zero K (C i) (hC i) p)
    smooth i := coordinate_section_smooth_scalar S K (C i) (hC i)
      (fun _ => signValue i) (IsLocallyConstant.const _)
    overlap i j := by
      refine ⟨fun _ => 1, vectorSmooth_of_isLocallyConstant _ (IsLocallyConstant.const _), ?_⟩
      intro p
      refine ⟨zero_lt_one, ?_⟩
      simp only [one_smul]
      cases i <;> cases j
      · rfl
      · have hp1 : p.val ∈ r.source := p.property.1
        have hp2 : p.val ∈ l.source := p.property.2
        change (1 : ℝ) • coordinateVector K l hl ⟨p.val,hp2⟩ =
          (-1 : ℝ) • coordinateVector K r hr ⟨p.val,hp1⟩
        exact (one_smul ℝ _).trans ((interval_coordinate_relation a b hab K hl hr
          ⟨p.val,hp2,hp1⟩).trans (neg_one_smul ℝ _).symm)
      · have hp1 : p.val ∈ l.source := p.property.1
        have hp2 : p.val ∈ r.source := p.property.2
        change (-1 : ℝ) • coordinateVector K r hr ⟨p.val,hp2⟩ =
          (1 : ℝ) • coordinateVector K l hl ⟨p.val,hp1⟩
        exact (neg_one_smul ℝ _).trans ((interval_coordinate_relation a b hab K hl hr
          ⟨p.val,hp1,hp2⟩).symm.trans (one_smul ℝ _).symm)
      · rfl }
  obtain ⟨o, ho, _⟩ := generators_orientation S G
  obtain ⟨s, hs, _⟩ := (signed_charts S o.val).mp o.property
  refine ⟨o, s, hs, ?_, ?_⟩
  · intro hl' p
    have hp := ho true p
    have hsp := hs K l hl' p
    have he : s.sign l hl' p = true := by
      apply (coordinateRayEquiv K l hl' p).injective
      simp only [coordinateRayEquiv_apply]
      exact hsp.2.trans (by simpa [coordinateRayEquiv, G, C, signValue] using hp.2.symm)
    exact he
  · intro hr' p
    have hp := ho false p
    have hsp := hs K r hr' p
    have he : s.sign r hr' p = false := by
      apply (coordinateRayEquiv K r hr' p).injective
      simp only [coordinateRayEquiv_apply]
      exact hsp.2.trans (by simpa [coordinateRayEquiv, G, C, signValue] using hp.2.symm)
    exact he

private theorem not_positive_neg_of_positive {V : Type u}
    [AddCommGroup V] [Module ℝ V] (r : Module.Ray ℝ V) (x : V)
    (hx : IsPositive r x) : ¬ IsPositive r (-x) := by
  intro hn
  apply hx.1
  exact eq_zero_of_sameRay_self_neg
    ((ray_eq_iff hx.1 hn.1).mp (hx.2.trans hn.2.symm))

theorem positive_signed_generator_iff {V : Type u}
    [AddCommGroup V] [Module ℝ V] (r : Module.Ray ℝ V) (x : V)
    (ε : Bool) (hε : IsPositive r (signValue ε • x)) :
    (IsPositive r x ↔ ε = true) ∧ (IsPositive r (-x) ↔ ε = false) := by
  cases ε with
  | false =>
    have hn : IsPositive r (-x) := by simpa [signValue] using hε
    have hx : ¬ IsPositive r x := by
      simpa only [neg_neg] using not_positive_neg_of_positive r (-x) hn
    simp [hx, hn]
  | true =>
    have hx : IsPositive r x := by simpa [signValue] using hε
    have hn := not_positive_neg_of_positive r x hx
    simp [hx, hn]

theorem coordinateVector_zero {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (B : SmoothManifold 0 a M) (H : FiberCoordinates B)
    (c : ModelChart 0 a M) (hc : c ∈ B.smoothStructure.val) (p : c.source) :
    coordinateVector H c hc p =
      (exteriorPower.zeroEquiv ℝ (TangentSpace B p.val)).symm 1 := by
  apply (exteriorPower.zeroEquiv ℝ (TangentSpace B p.val)).injective
  simp [coordinateVector]

theorem zero_boundary_positivity_from_sign
    (hcharts : Specs.SmoothManifolds.Orientations.Boundary.boundary_chart_signType.{u})
    {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold 1 a M)
    (B : SmoothManifold 0 .euclidean (intrinsicBoundary S))
    (hB : IsNaturalBoundary S B) (o : Orientation S) (q : Orientation B)
    (hi : IsInducedOrientation o q) (s : SignedCharts S) (t : SignedCharts B)
    (hs : RepresentsSignedCharts o.val s) (ht : RepresentsSignedCharts q.val t)
    (H : FiberCoordinates B)
    (c : ModelChart 1 a M) (hc : c ∈ S.smoothStructure.val)
    (b : ModelChart 0 .euclidean (intrinsicBoundary S)) (hb : b ∈ B.smoothStructure.val)
    (hf : IsFaceRestriction S c b) (p : intrinsicBoundary S)
    (hp : p ∈ b.source) (hpc : p.val ∈ c.source) :
    (IsPositive (q.val p) ((exteriorPower.zeroEquiv ℝ (TangentSpace B p)).symm 1) ↔
      s.sign c hc ⟨p.val, hpc⟩ = false) ∧
    (IsPositive (q.val p) (-((exteriorPower.zeroEquiv ℝ (TangentSpace B p)).symm 1)) ↔
      s.sign c hc ⟨p.val, hpc⟩ = true) := by
  have hsign := hcharts S B hB o q hi s t hs ht c hc b hb hf p hp hpc
  have hpos := ht H b hb ⟨p, hp⟩
  rw [coordinateVector_zero] at hpos
  have hiff := positive_signed_generator_iff _ _ _ hpos
  cases hsval : s.sign c hc ⟨p.val, hpc⟩ <;>
    cases htval : t.sign b hb ⟨p, hp⟩ <;>
    norm_num [hsval, htval, signValue] at hsign <;>
    simp [hsval, htval] at hiff ⊢ <;> tauto

theorem interval_boundary_endpoint_signs
    (a b : ℝ) (hab : a < b)
    (S : SmoothManifold 1 .halfSpace (Icc a b))
    (l r : ModelChart 1 .halfSpace (Icc a b))
    (hstd : IsStandardInterval a b S l r)
    (hboundary : intrinsicBoundary S = {x | x.val = a ∨ x.val = b})
    (o : Orientation S) (s : SignedCharts S)
    (hs : RepresentsSignedCharts o.val s)
    (hl : ∀ (hl : l ∈ S.smoothStructure.val) p, s.sign l hl p = true)
    (hr : ∀ (hr : r ∈ S.smoothStructure.val) p, s.sign r hr p = false) :
    ∃ (B : SmoothManifold 0 .euclidean (intrinsicBoundary S)) (q : Orientation B),
      IsNaturalBoundary S B ∧ IsInducedOrientation o q ∧
      ∀ p : intrinsicBoundary S,
        (IsPositive (q.val p) ((exteriorPower.zeroEquiv ℝ (TangentSpace B p)).symm 1) ↔
          p.val.val = b) ∧
        (IsPositive (q.val p) (-((exteriorPower.zeroEquiv ℝ (TangentSpace B p)).symm 1)) ↔
          p.val.val = a) := by
  obtain ⟨⟨B, hB⟩, hex⟩ := boundary_orientation S o
  obtain ⟨q, ⟨hi, _⟩, _⟩ := hex B hB
  obtain ⟨t, ht, _⟩ := (signed_charts B q.val).mp q.property
  obtain ⟨H⟩ := TangentBundle.fiberCoordinates_exists B
  refine ⟨B, q, hB, hi, ?_⟩
  intro p
  have hend : p.val.val = a ∨ p.val.val = b := by
    exact (Set.ext_iff.mp hboundary p.val).mp p.property
  rcases hend with hpa | hpb
  · have hpl : p.val ∈ l.source := by
      rw [hstd.2.2.1]
      change p.val.val < b
      rw [hpa]
      exact hab
    obtain ⟨c, hc, hf⟩ := hB.2 l hstd.1 ⟨⟨p, hpl⟩⟩
    have hpc : p ∈ c.source := by rw [hf.1]; exact hpl
    have hsign := zero_boundary_positivity_from_sign boundary_chart_sign S B hB o q hi
      s t hs ht H l hstd.1 c hc hf p hpc hpl
    have hneq : p.val.val ≠ b := by rw [hpa]; exact hab.ne
    simpa [hl, hpa, hab.ne] using hsign
  · have hpr : p.val ∈ r.source := by
      rw [hstd.2.2.2.1]
      change a < p.val.val
      rw [hpb]
      exact hab
    obtain ⟨c, hc, hf⟩ := hB.2 r hstd.2.1 ⟨⟨p, hpr⟩⟩
    have hpc : p ∈ c.source := by rw [hf.1]; exact hpr
    have hsign := zero_boundary_positivity_from_sign boundary_chart_sign S B hB o q hi
      s t hs ht H r hstd.2.1 c hc hf p hpc hpr
    have hneq : p.val.val ≠ a := by rw [hpb]; exact hab.ne'
    simpa [hr, hpb, hab.ne'] using hsign


theorem interval_sign : Specs.SmoothManifolds.Orientations.Boundary.interval_signType := by
  intro a b hab
  obtain ⟨o, s, hs, hl, hr⟩ := interval_positive_orientation a b hab
  refine ⟨standardInterval a b hab, intervalLeftChart a b hab, intervalRightChart a b hab,
    standardInterval_spec a b hab, standardInterval_boundary a b hab, o, s, hs, hl, hr, ?_⟩
  exact interval_boundary_endpoint_signs a b hab (standardInterval a b hab)
    (intervalLeftChart a b hab) (intervalRightChart a b hab) (standardInterval_spec a b hab)
    (standardInterval_boundary a b hab) o s hs hl hr


end SmoothManifolds.BoundaryOrientations
