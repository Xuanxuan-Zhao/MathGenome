import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.SchlessingerConditions
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.SchlessingerTangentVectorSpace

/-! The tangent vector space of a functor satisfying Schlessinger's condition H2. -/

universe u w

namespace CommutativeAlgebraNotes

open CategoryTheory SchlessingerTangentVectorSpaceSpec

namespace LocalArtinAlgebra

variable {k : Type u} [Field k]

/-- Apply a linear map to the square-zero summand and the identity to the field. -/
abbrev splitMap {I J : Type u} [AddCommGroup I] [Module k I] [Module.Finite k I]
    [AddCommGroup J] [Module k J] [Module.Finite k J] (f : I →ₗ[k] J) :
    Hom (split k I) (split k J) := splitMapModel f

@[simp] theorem splitMap_fst {I J : Type u} [AddCommGroup I] [Module k I] [Module.Finite k I]
    [AddCommGroup J] [Module k J] [Module.Finite k J] (f : I →ₗ[k] J) (x : split k I) :
    (splitMap f x : TrivSqZeroExt k J).fst = (x : TrivSqZeroExt k I).fst := by
  let : Module kᵐᵒᵖ I := splitOppositeModule k I
  let : Module kᵐᵒᵖ J := splitOppositeModule k J
  let : IsCentralScalar k I := ⟨fun _ _ => rfl⟩
  let : IsCentralScalar k J := ⟨fun _ _ => rfl⟩
  exact TrivSqZeroExt.fst_map f x

@[simp] theorem splitMap_snd {I J : Type u} [AddCommGroup I] [Module k I] [Module.Finite k I]
    [AddCommGroup J] [Module k J] [Module.Finite k J] (f : I →ₗ[k] J) (x : split k I) :
    (splitMap f x : TrivSqZeroExt k J).snd = f (x : TrivSqZeroExt k I).snd := by
  let : Module kᵐᵒᵖ I := splitOppositeModule k I
  let : Module kᵐᵒᵖ J := splitOppositeModule k J
  let : IsCentralScalar k I := ⟨fun _ _ => rfl⟩
  let : IsCentralScalar k J := ⟨fun _ _ => rfl⟩
  exact TrivSqZeroExt.snd_map f x

end LocalArtinAlgebra

namespace ArtinFunctor

open LocalArtinAlgebra

variable {k : Type u} [Field k]
variable (F : ArtinFunctor.{u,w} k)

private theorem onHom_comp {A B C : LocalArtinAlgebra.{u,u} k}
    (f : Hom A B) (g : Hom B C) (x : F.toFunctor.obj A) :
    onHom F g (onHom F f x) = onHom F (g.comp f) x :=
  (ConcreteCategory.congr_hom (F.toFunctor.map_comp f g) x).symm

private theorem onHom_id {A : LocalArtinAlgebra.{u,u} k} (x : F.toFunctor.obj A) :
    onHom F (Hom.id A) x = x :=
  ConcreteCategory.congr_hom (F.toFunctor.map_id A) x

section LinearMaps

variable {I J K : Type u} [AddCommGroup I] [Module k I] [Module.Finite k I]
  [AddCommGroup J] [Module k J] [Module.Finite k J]
  [AddCommGroup K] [Module k K] [Module.Finite k K]

@[simp] theorem onLinear_comp (f : I →ₗ[k] J) (g : J →ₗ[k] K) (x : SplitValue F I) :
    onLinear F g (onLinear F f x) = onLinear F (g.comp f) x := by
  rw [onLinear, onLinear, onLinear, onHom_comp]
  congr 1
  apply Hom.ext
  intro y
  apply TrivSqZeroExt.ext
  · change (splitMap g (splitMap f y)).fst = (splitMap (g.comp f) y).fst
    simp
  · change (splitMap g (splitMap f y)).snd = (splitMap (g.comp f) y).snd
    simp

@[simp] theorem onLinear_id (x : SplitValue F I) : onLinear F LinearMap.id x = x := by
  have h : splitMap (LinearMap.id : I →ₗ[k] I) = Hom.id (split k I) :=
    Hom.ext fun y => TrivSqZeroExt.ext (by change (splitMap _ y).fst = y.fst; simp)
      (by change (splitMap _ y).snd = y.snd; simp)
  exact (congrArg (fun f => onHom F f x) h).trans (F.onHom_id x)

private theorem onLinear_zero (x : SplitValue F I) :
    onLinear F (0 : I →ₗ[k] k) x = tangentZero F := by
  have h : splitMap (0 : I →ₗ[k] k) =
      (fromFieldModel (split k k)).comp (residueHom (split k I)) :=
    Hom.ext fun y => TrivSqZeroExt.ext (by simp; rfl) (by simp; rfl)
  change onHom F (splitMap (0 : I →ₗ[k] k)) x = _
  rw [h, ← F.onHom_comp]
  congr 1
  exact Subsingleton.elim _ _

private theorem onLinear_bijective (e : I ≃ₗ[k] J) :
    Function.Bijective (onLinear F e.toLinearMap) := by
  have left (x : SplitValue F I) :
      onLinear F e.symm.toLinearMap (onLinear F e.toLinearMap x) = x := by simp
  have right (x : SplitValue F J) :
      onLinear F e.toLinearMap (onLinear F e.symm.toLinearMap x) = x := by simp
  exact ⟨Function.LeftInverse.injective left, Function.RightInverse.surjective right⟩

end LinearMaps

/-- The H2 comparison with the compatibility condition over the singleton erased. -/
private theorem residueComparison_bijective (h₂ : F.H2) (A B : LocalArtinAlgebra.{u,u} k)
    (h : B = dualNumbers k) :
    Function.Bijective (fun x : F.toFunctor.obj
        (pullback (residueHom A) (residueHom B)) =>
      (onHom F (pullbackFst (residueHom A) (residueHom B)) x,
        onHom F (pullbackSnd (residueHom A) (residueHom B)) x)) := by
  subst B
  let cmp := F.comparison (residueHom A) (residueHom (dualNumbers k))
  have forget : Function.Bijective (fun p : CompatiblePairs
      (onHom F (residueHom A)) (onHom F (residueHom (dualNumbers k))) => p.val) :=
    ⟨Subtype.val_injective, fun p => ⟨⟨p, Subsingleton.elim _ _⟩, rfl⟩⟩
  exact forget.comp (show Function.Bijective cmp from h₂ A)

section Pair

variable (I : Type u) [AddCommGroup I] [Module k I] [Module.Finite k I]

/-- The split algebra on a product of ideals maps to the fibre product over the field. -/
private def splitPairToPullback :
    Hom (split k (I × k)) (pullback (residueHom (split k I)) (residueHom (split k k))) :=
  pullbackLift _ _ (splitMap (LinearMap.fst k I k)) (splitMap (LinearMap.snd k I k))
    (Hom.ext fun x => by
      change (splitMap (LinearMap.fst k I k) x).fst = (splitMap (LinearMap.snd k I k) x).fst
      simp)

private theorem splitPairToPullback_bijective :
    Function.Bijective (fun x : split k (I × k) => (splitPairToPullback (k := k) I).val x) := by
  constructor
  · intro x y h
    have h₁ := congrArg (fun z => z.val.1) h
    have h₂ := congrArg (fun z => z.val.2) h
    change splitMap (LinearMap.fst k I k) x = splitMap (LinearMap.fst k I k) y at h₁
    change splitMap (LinearMap.snd k I k) x = splitMap (LinearMap.snd k I k) y at h₂
    exact TrivSqZeroExt.ext
      (by simpa only [splitMap_fst] using congrArg TrivSqZeroExt.fst h₁)
      (Prod.ext
        (by simpa only [splitMap_snd, LinearMap.fst_apply] using congrArg TrivSqZeroExt.snd h₁)
        (by simpa only [splitMap_snd, LinearMap.snd_apply] using congrArg TrivSqZeroExt.snd h₂))
  · rintro ⟨⟨a, b⟩, h⟩
    change TrivSqZeroExt k I at a
    change TrivSqZeroExt k k at b
    change a.fst = b.fst at h
    let z : split k (I × k) := ⟨a.fst, (a.snd, b.snd)⟩
    refine ⟨z, Subtype.ext (Prod.ext ?_ ?_)⟩
    · change splitMap (LinearMap.fst k I k) z = a
      exact TrivSqZeroExt.ext (splitMap_fst _ z) (splitMap_snd _ z)
    · change splitMap (LinearMap.snd k I k) z = b
      exact TrivSqZeroExt.ext ((splitMap_fst _ z).trans h) (splitMap_snd _ z)

private theorem onHom_bijective {A B : LocalArtinAlgebra.{u,u} k}
    (f : Hom A B) (hf : Function.Bijective f) : Function.Bijective (onHom F f) := by
  let e := AlgEquiv.ofBijective f.val hf
  let g : Hom B A := ⟨e.symm.toAlgHom, ⟨fun x hx => by
    have hh := hx.map e.toAlgHom
    exact e.apply_symm_apply x ▸ hh⟩⟩
  have left (x : F.toFunctor.obj A) : onHom F g (onHom F f x) = x := by
    rw [F.onHom_comp, show g.comp f = Hom.id A from Hom.ext e.symm_apply_apply, F.onHom_id]
  have right (x : F.toFunctor.obj B) : onHom F f (onHom F g x) = x := by
    rw [F.onHom_comp, show f.comp g = Hom.id B from Hom.ext e.apply_symm_apply, F.onHom_id]
  exact ⟨Function.LeftInverse.injective left, Function.RightInverse.surjective right⟩

private theorem splitPair_bijective (h₂ : F.H2) :
    Function.Bijective (fun x : SplitValue F (I × k) =>
      (onLinear F (LinearMap.fst k I k) x, onLinear F (LinearMap.snd k I k) x)) := by
  have h := (F.residueComparison_bijective h₂ (split k I) (split k k) (split_eq_dual k)).comp
    (F.onHom_bijective _ (splitPairToPullback_bijective I))
  convert h using 1
  funext x
  apply Prod.ext
  · exact (F.onHom_comp (splitPairToPullback I) (pullbackFst
      (residueHom (split k I)) (residueHom (split k k))) x).symm
  · exact (F.onHom_comp (splitPairToPullback I) (pullbackSnd
      (residueHom (split k I)) (residueHom (split k k))) x).symm

end Pair

private theorem tangentPair_bijective (h₂ : F.H2) : Function.Bijective (tangentPair F) :=
  F.splitPair_bijective k h₂

section LinearEvaluation

variable {I : Type u} [AddCommGroup I] [Module k I] [Module.Finite k I]

private theorem onLinear_add (h₂ : F.H2) (l m : I →ₗ[k] k) (x : SplitValue F I) :
    onLinear F (l + m) x = tangentAdd F (onLinear F l x) (onLinear F m x) := by
  have h : tangentPair F (onLinear F (l.prod m) x) = (onLinear F l x, onLinear F m x) := by
    simp [tangentPair]
  let : Nonempty (SplitValue F (k × k)) := ⟨pointedValue F (split k (k × k))⟩
  rw [tangentAdd, ← h, Function.leftInverse_invFun (F.tangentPair_bijective h₂).1]
  simp [addMap, LinearMap.add_comp]

private theorem onLinear_scale (a : k) (l : I →ₗ[k] k) (x : SplitValue F I) :
    tangentScale F a (onLinear F l x) = onLinear F (a • l) x := by
  simp [tangentScale, scaleMap, LinearMap.smul_comp]

end LinearEvaluation

/-- H2 gives all the vector space axioms for the operations on the split line. -/
theorem tangentVectorLaws (h₂ : F.H2) : VectorLaws F where
  add_assoc x y z := by
    obtain ⟨p, hp⟩ := (F.tangentPair_bijective h₂).2 (x, y)
    obtain ⟨q, hq⟩ := (F.splitPair_bijective (k × k) h₂).2 (p, z)
    let f := LinearMap.fst k (k × k) k
    let a := (LinearMap.fst k k k).comp f
    let b := (LinearMap.snd k k k).comp f
    let c := LinearMap.snd k (k × k) k
    have h₁ : onLinear F a q = x := by
      rw [← F.onLinear_comp, show onLinear F f q = p from congrArg Prod.fst hq]
      exact congrArg Prod.fst hp
    have h₂' : onLinear F b q = y := by
      rw [← F.onLinear_comp, show onLinear F f q = p from congrArg Prod.fst hq]
      exact congrArg Prod.snd hp
    have h₃ : onLinear F c q = z := congrArg Prod.snd hq
    rw [← h₁, ← h₂', ← h₃]
    simp only [← F.onLinear_add h₂, add_assoc]
  add_comm x y := by
    obtain ⟨p, hp⟩ := (F.tangentPair_bijective h₂).2 (x, y)
    have hx : onLinear F (LinearMap.fst k k k) p = x := congrArg Prod.fst hp
    have hy : onLinear F (LinearMap.snd k k k) p = y := congrArg Prod.snd hp
    rw [← hx, ← hy]
    simp only [← F.onLinear_add h₂, add_comm]
  add_zero x := by
    calc
      _ = tangentAdd F (onLinear F (LinearMap.id : k →ₗ[k] k) x)
          (onLinear F (0 : k →ₗ[k] k) x) := by rw [F.onLinear_id, F.onLinear_zero]
      _ = x := by rw [← F.onLinear_add h₂, add_zero, F.onLinear_id]
  neg_add_cancel x := by
    have h : (scaleMap (-1) + LinearMap.id : k →ₗ[k] k) = 0 := by
      apply LinearMap.ext
      intro r
      simp [scaleMap, smul_eq_mul]
    calc
      _ = tangentAdd F (onLinear F (scaleMap (-1)) x)
          (onLinear F (LinearMap.id : k →ₗ[k] k) x) := by rw [F.onLinear_id]; rfl
      _ = _ := by rw [← F.onLinear_add h₂, h, F.onLinear_zero]
  one_smul x := by simp [tangentScale, scaleMap]
  mul_smul a b x := by
    simp only [tangentScale, F.onLinear_comp]
    congr 1
    apply LinearMap.ext
    intro r
    simp [scaleMap, smul_eq_mul, mul_assoc]
  smul_zero a := by
    rw [← F.onLinear_zero (I := k) (tangentZero F), F.onLinear_scale, smul_zero, F.onLinear_zero]
  smul_add a x y := by
    obtain ⟨p, hp⟩ := (F.tangentPair_bijective h₂).2 (x, y)
    have hx : onLinear F (LinearMap.fst k k k) p = x := congrArg Prod.fst hp
    have hy : onLinear F (LinearMap.snd k k k) p = y := congrArg Prod.snd hp
    rw [← hx, ← hy]
    simp only [← F.onLinear_add h₂, F.onLinear_scale, smul_add]
  zero_smul x := by simp [tangentScale, scaleMap, F.onLinear_zero]
  add_smul a b x := by
    simp only [tangentScale, scaleMap, add_smul, F.onLinear_add h₂]

/-- The additive group on the existing tangent set. -/
noncomputable abbrev tangentAddCommGroup (h₂ : F.H2) : AddCommGroup F.Tangent :=
  tangentAddCommGroupModel F (F.tangentVectorLaws h₂)

/-- The scalar action on the existing tangent set. -/
noncomputable abbrev tangentModule (h₂ : F.H2) :
    letI := F.tangentAddCommGroup h₂
    Module k F.Tangent :=
  tangentModuleModel F (F.tangentVectorLaws h₂)

/-- Schlessinger's third condition, finite dimensionality of the tangent space. -/
abbrev H3 : Prop := H3Model F

theorem h3_iff_finite (laws : VectorLaws F) :
    letI := tangentAddCommGroupModel F laws
    letI := tangentModuleModel F laws
    F.H3 ↔ Module.Finite k F.Tangent := by
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨laws, h⟩⟩


/-- Split algebras on a zero space give the unique point of F(k). -/
private theorem eq_pointed_of_subsingleton (I : Type u) [AddCommGroup I] [Module k I]
    [Module.Finite k I] [Subsingleton I] (x : SplitValue F I) :
    x = pointedValue F (split k I) := by
  let A := split k I
  have h : (fromFieldModel A).comp (residueHom A) = Hom.id A :=
    Hom.ext fun y => TrivSqZeroExt.ext rfl (Subsingleton.elim _ _)
  calc
    x = onHom F (Hom.id A) x := (F.onHom_id x).symm
    _ = onHom F (fromFieldModel A) (onHom F (residueHom A) x) := by rw [F.onHom_comp, h]
    _ = pointedValue F A := congrArg (onHom F (fromFieldModel A)) (Subsingleton.elim _ _)

private def splitFirstCoordinate (n : ℕ) : (Fin (n + 1) → k) ≃ₗ[k] (Fin n → k) × k where
  toFun x := (fun i => x i.succ, x 0)
  invFun p := Fin.cons p.2 p.1
  left_inv x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Fin.cons_zero _ _
    · exact Fin.cons_succ _ _ _
  right_inv p := by
    apply Prod.ext
    · funext i
      exact @Fin.cons_succ n (fun _ => k) p.2 p.1 i
    · exact @Fin.cons_zero n (fun _ => k) p.2 p.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem standardCoordinates_bijective (h₂ : F.H2) (n : ℕ) :
    Function.Bijective (fun (x : SplitValue F (Fin n → k)) (i : Fin n) =>
      onLinear F (LinearMap.proj i : (Fin n → k) →ₗ[k] k) x) := by
  induction n with
  | zero =>
    refine ⟨fun x y _ => (F.eq_pointed_of_subsingleton _ x).trans
      (F.eq_pointed_of_subsingleton _ y).symm, fun p => ?_⟩
    exact ⟨pointedValue F (split k (Fin 0 → k)), funext fun i => i.elim0⟩
  | succ n ih =>
    let e : (Fin (n + 1) → k) ≃ₗ[k] (Fin n → k) × k := splitFirstCoordinate n
    have hPair := (F.splitPair_bijective (Fin n → k) h₂).comp (F.onLinear_bijective e)
    let append : ((Fin n → SplitValue F k) × SplitValue F k) ≃ (Fin (n + 1) → SplitValue F k) :=
      (Equiv.prodComm _ _).trans (Fin.consEquiv (fun _ : Fin (n + 1) => SplitValue F k))
    have h := append.bijective.comp ((ih.prodMap Function.bijective_id).comp hPair)
    convert h using 1
    funext x i
    let head := onLinear F (LinearMap.snd k (Fin n → k) k) (onLinear F e.toLinearMap x)
    let tail : Fin n → SplitValue F k := fun l =>
      onLinear F (LinearMap.proj l : (Fin n → k) →ₗ[k] k)
        (onLinear F (LinearMap.fst k (Fin n → k) k) (onLinear F e.toLinearMap x))
    refine Fin.cases ?_ (fun j => ?_) i
    · change onLinear F (LinearMap.proj 0 : (Fin (n + 1) → k) →ₗ[k] k) x =
        @Fin.cons n (fun _ => SplitValue F k) head tail 0
      rw [Fin.cons_zero]
      dsimp only [head]
      rw [F.onLinear_comp]
      rfl
    · change onLinear F (LinearMap.proj j.succ : (Fin (n + 1) → k) →ₗ[k] k) x =
        @Fin.cons n (fun _ => SplitValue F k) head tail j.succ
      rw [Fin.cons_succ]
      dsimp only [tail]
      rw [F.onLinear_comp, F.onLinear_comp]
      rfl

/-- The coordinate maps of any finite basis identify F(k ⊕ I) with a power of F(k ⊕ k). -/
private theorem basisCoordinates_bijective (h₂ : F.H2)
    {I : Type u} [AddCommGroup I] [Module k I] [Module.Finite k I] {n : ℕ}
    (b : Module.Basis (Fin n) k I) :
    Function.Bijective (fun (x : SplitValue F I) i => onLinear F (b.coord i) x) := by
  have h := (F.standardCoordinates_bijective h₂ n).comp (F.onLinear_bijective b.equivFun)
  convert h using 1
  funext x i
  change onLinear F (b.coord i) x =
    onLinear F (LinearMap.proj i : (Fin n → k) →ₗ[k] k) (onLinear F b.equivFun.toLinearMap x)
  rw [F.onLinear_comp]
  rfl


section TensorComparison

open scoped TensorProduct

variable {I : Type u} [AddCommGroup I] [Module k I] [Module.Finite k I]

/-- Testing along covectors gives a linear map from the dual of the ideal. -/
private noncomputable def covectorEvaluation (h₂ : F.H2) (x : SplitValue F I) :
    letI := F.tangentAddCommGroup h₂
    letI := F.tangentModule h₂
    Module.Dual k I →ₗ[k] F.Tangent :=
  letI := F.tangentAddCommGroup h₂
  letI := F.tangentModule h₂
  let e := tangentIdentification F
  { toFun := fun l => e (onLinear F l x)
    map_add' := fun l m => by
      change e (onLinear F (l + m) x) =
        e (tangentAdd F (e.symm (e (onLinear F l x))) (e.symm (e (onLinear F m x))))
      rw [e.symm_apply_apply, e.symm_apply_apply, F.onLinear_add h₂]
    map_smul' := fun a l => by
      change e (onLinear F (a • l) x) =
        e (tangentScale F a (e.symm (e (onLinear F l x))))
      rw [e.symm_apply_apply, F.onLinear_scale] }

private theorem covectorEvaluation_bijective (h₂ : F.H2) :
    Function.Bijective (F.covectorEvaluation (I := I) h₂) := by
  let : AddCommGroup F.Tangent := F.tangentAddCommGroup h₂
  let : Module k F.Tangent := F.tangentModule h₂
  let e := tangentIdentification F
  let b := Module.finBasis k I
  have hb := F.basisCoordinates_bijective h₂ b
  constructor
  · intro x y h
    apply hb.injective
    funext i
    apply e.injective
    have hh := congrArg (fun p => p (b.dualBasis i)) h
    simpa only [covectorEvaluation, LinearMap.coe_mk, AddHom.coe_mk,
      Module.Basis.coe_dualBasis] using hh
  · intro g
    obtain ⟨x, hx⟩ := hb.surjective (fun i => e.symm (g (b.dualBasis i)))
    refine ⟨x, b.dualBasis.ext fun i => ?_⟩
    change e (onLinear F (b.dualBasis i) x) = g (b.dualBasis i)
    simpa only [Module.Basis.coe_dualBasis] using
      (congrArg e (congrFun hx i)).trans (e.apply_symm_apply _)

/-- Basis-independent comparison of the split value with tangent tensors. -/
noncomputable def splitTensorComparison (h₂ : F.H2) (I : Type u)
    [AddCommGroup I] [Module k I] [Module.Finite k I] :
    SplitTensorComparison F (F.tangentVectorLaws h₂) I :=
  letI := F.tangentAddCommGroup h₂
  letI := F.tangentModule h₂
  { equiv := (Equiv.ofBijective (F.covectorEvaluation h₂) (F.covectorEvaluation_bijective h₂)).trans
      (tensorContraction (k := k) (I := I) (T := F.Tangent)).symm.toEquiv
    contract := fun x l =>
      DFunLike.congr_fun ((tensorContraction (k := k) (I := I) (T := F.Tangent)).apply_symm_apply
        (F.covectorEvaluation h₂ x)) l }

/-- Identify the split value with the tensor product of the tangent space and the ideal. -/
noncomputable abbrev splitTensorEquiv (h₂ : F.H2) (I : Type u)
    [AddCommGroup I] [Module k I] [Module.Finite k I] :=
  (F.splitTensorComparison h₂ I).equiv

theorem splitTensorExists (h₂ : F.H2) (laws : VectorLaws F) (I : Type u)
    [AddCommGroup I] [Module k I] [Module.Finite k I] :
    Nonempty (SplitTensorComparison F laws I) :=
  ⟨F.splitTensorComparison h₂ I⟩

end TensorComparison

open scoped TensorProduct in
/-- A pure tensor is the image of a tangent element along the map sending 1 to the ideal element. -/
theorem splitTensor_symm_tmul (laws : VectorLaws F)
    {I : Type u} [AddCommGroup I] [Module k I] [Module.Finite k I]
    (e : SplitTensorComparison F laws I) (t : F.Tangent) (i : I) :
    letI := tangentAddCommGroupModel F laws
    letI := tangentModuleModel F laws
    e.equiv.symm (t ⊗ₜ[k] i) =
      onLinear F (LinearMap.toSpanSingleton k I i) ((tangentIdentification F).symm t) := by
  let := tangentAddCommGroupModel F laws
  let := tangentModuleModel F laws
  apply e.equiv.injective
  rw [Equiv.apply_symm_apply]
  apply (tensorContraction (k := k) (I := I) (T := F.Tangent)).injective
  ext l
  rw [tensorContraction_tmul, e.contract, F.onLinear_comp, LinearMap.comp_toSpanSingleton]
  have h : LinearMap.toSpanSingleton k k (l i) = scaleMap (l i) := by
    apply LinearMap.ext
    intro a
    exact mul_comm a (l i)
  rw [h]
  rfl

open scoped TensorProduct in
theorem splitTensor_natural_ideal (laws : VectorLaws F)
    {I J : Type u} [AddCommGroup I] [Module k I] [Module.Finite k I]
    [AddCommGroup J] [Module k J] [Module.Finite k J]
    (eI : SplitTensorComparison F laws I) (eJ : SplitTensorComparison F laws J)
    (f : I →ₗ[k] J) (x : SplitValue F I) :
    letI := tangentAddCommGroupModel F laws
    letI := tangentModuleModel F laws
    eJ.equiv (onLinear F f x) = TensorProduct.map LinearMap.id f (eI.equiv x) := by
  let := tangentAddCommGroupModel F laws
  let := tangentModuleModel F laws
  apply (tensorContraction (k := k) (I := J) (T := F.Tangent)).injective
  ext l
  have h (z : F.Tangent ⊗[k] I) :
      tensorContraction (TensorProduct.map LinearMap.id f z) l =
        tensorContraction z (l.comp f) := by
    induction z using TensorProduct.inductionOn with
    | tmul t i => simp
    | add p q hp hq => simp [hp, hq]
  rw [h, eJ.contract, eI.contract, F.onLinear_comp]

section NaturalTransformation

open scoped TensorProduct

variable (G : ArtinFunctor.{u,w} k) (τ : F.toFunctor ⟶ G.toFunctor)

private theorem onNatural_hom {A B : LocalArtinAlgebra.{u,u} k} (f : Hom A B)
    (x : F.toFunctor.obj A) :
    onNatural F G τ B (onHom F f x) = onHom G f (onNatural F G τ A x) :=
  ConcreteCategory.congr_hom (τ.naturality f) x

private theorem onNatural_linear {I J : Type u} [AddCommGroup I] [Module k I] [Module.Finite k I]
    [AddCommGroup J] [Module k J] [Module.Finite k J] (f : I →ₗ[k] J) (x : SplitValue F I) :
    onNatural F G τ (split k J) (onLinear F f x) =
      onLinear G f (onNatural F G τ (split k I) x) :=
  F.onNatural_hom G τ (splitMap f) x

private theorem tangentIdentification_natural (x : SplitValue F k) :
    onNatural F G τ (dualNumbers k) (tangentIdentification F x) =
      tangentIdentification G (onNatural F G τ (split k k) x) :=
  F.onNatural_hom G τ (eqToHom (split_eq_dual k)) x

private noncomputable def splitTangentMap (hF : F.H2) (hG : G.H2) :
    letI := splitAddCommGroupModel F (F.tangentVectorLaws hF)
    letI := splitModuleModel F (F.tangentVectorLaws hF)
    letI := splitAddCommGroupModel G (G.tangentVectorLaws hG)
    letI := splitModuleModel G (G.tangentVectorLaws hG)
    SplitValue F k →ₗ[k] SplitValue G k :=
  letI := splitAddCommGroupModel F (F.tangentVectorLaws hF)
  letI := splitModuleModel F (F.tangentVectorLaws hF)
  letI := splitAddCommGroupModel G (G.tangentVectorLaws hG)
  letI := splitModuleModel G (G.tangentVectorLaws hG)
  { toFun := onNatural F G τ (split k k)
    map_add' := fun x y => by
      obtain ⟨p, hp⟩ := (F.tangentPair_bijective hF).2 (x, y)
      have hx : onLinear F (LinearMap.fst k k k) p = x := congrArg Prod.fst hp
      have hy : onLinear F (LinearMap.snd k k k) p = y := congrArg Prod.snd hp
      change onNatural F G τ (split k k) (tangentAdd F x y) =
        tangentAdd G (onNatural F G τ (split k k) x) (onNatural F G τ (split k k) y)
      rw [← hx, ← hy, ← F.onLinear_add hF, F.onNatural_linear, F.onNatural_linear,
        F.onNatural_linear, G.onLinear_add hG]
    map_smul' := fun a x => F.onNatural_linear G τ (scaleMap a) x }

/-- The linear tangent map induced by a natural transformation of H2 functors. -/
noncomputable def tangentMap (hF : F.H2) (hG : G.H2) :
    letI := F.tangentAddCommGroup hF
    letI := F.tangentModule hF
    letI := G.tangentAddCommGroup hG
    letI := G.tangentModule hG
    F.Tangent →ₗ[k] G.Tangent :=
  letI := F.tangentAddCommGroup hF
  letI := F.tangentModule hF
  letI := G.tangentAddCommGroup hG
  letI := G.tangentModule hG
  letI := splitAddCommGroupModel F (F.tangentVectorLaws hF)
  letI := splitModuleModel F (F.tangentVectorLaws hF)
  letI := splitAddCommGroupModel G (G.tangentVectorLaws hG)
  letI := splitModuleModel G (G.tangentVectorLaws hG)
  let eF := (tangentToSplitAddEquiv F (F.tangentVectorLaws hF)).linearEquiv k
  let eG := (tangentToSplitAddEquiv G (G.tangentVectorLaws hG)).linearEquiv k
  eG.symm.toLinearMap.comp ((F.splitTangentMap G τ hF hG).comp eF.toLinearMap)

@[simp] theorem tangentMap_apply (hF : F.H2) (hG : G.H2) (t : F.Tangent) :
    F.tangentMap G τ hF hG t = onNatural F G τ (dualNumbers k) t := by
  change tangentIdentification G (onNatural F G τ (split k k) ((tangentIdentification F).symm t)) = _
  rw [← F.tangentIdentification_natural, Equiv.apply_symm_apply]

theorem tangentMapExists (hF : F.H2) (hG : G.H2) (lawsF : VectorLaws F) (lawsG : VectorLaws G) :
    letI := tangentAddCommGroupModel F lawsF
    letI := tangentModuleModel F lawsF
    letI := tangentAddCommGroupModel G lawsG
    letI := tangentModuleModel G lawsG
    ∃ g : F.Tangent →ₗ[k] G.Tangent, ∀ t, g t = onNatural F G τ (dualNumbers k) t :=
  ⟨F.tangentMap G τ hF hG, F.tangentMap_apply G τ hF hG⟩

theorem splitTensor_natural_functor (lawsF : VectorLaws F) (lawsG : VectorLaws G)
    {I : Type u} [AddCommGroup I] [Module k I] [Module.Finite k I]
    (eF : SplitTensorComparison F lawsF I) (eG : SplitTensorComparison G lawsG I) :
    letI := tangentAddCommGroupModel F lawsF
    letI := tangentModuleModel F lawsF
    letI := tangentAddCommGroupModel G lawsG
    letI := tangentModuleModel G lawsG
    ∀ (g : F.Tangent →ₗ[k] G.Tangent),
    (∀ t, g t = onNatural F G τ (dualNumbers k) t) →
    ∀ x : SplitValue F I,
      eG.equiv (onNatural F G τ (split k I) x) =
        TensorProduct.map g LinearMap.id (eF.equiv x) := by
  let := tangentAddCommGroupModel F lawsF
  let := tangentModuleModel F lawsF
  let := tangentAddCommGroupModel G lawsG
  let := tangentModuleModel G lawsG
  intro g hg x
  apply (tensorContraction (k := k) (I := I) (T := G.Tangent)).injective
  ext l
  have h (z : F.Tangent ⊗[k] I) :
      tensorContraction (TensorProduct.map g LinearMap.id z) l = g (tensorContraction z l) := by
    induction z using TensorProduct.inductionOn with
    | tmul t i => simp
    | add p q hp hq => simp [hp, hq]
  rw [h, eG.contract, eF.contract, hg, F.tangentIdentification_natural, F.onNatural_linear]

end NaturalTransformation


end ArtinFunctor
end CommutativeAlgebraNotes
