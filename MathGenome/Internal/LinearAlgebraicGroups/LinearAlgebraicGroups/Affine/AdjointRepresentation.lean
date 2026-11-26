import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.AdjointRepresentation
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.LieBracket
import Batteries.Tactic.OpenPrivate
import Mathlib.LinearAlgebra.Matrix.ToLin

open scoped Matrix

open AlgebraicGeometry CategoryTheory Opposite WithConv Coalgebra Bialgebra TensorProduct
open LinearAlgebraicGroups.Specs.AdjointRepresentation

universe u

namespace LinearAlgebraicGroups

noncomputable section

variable {k : Type u} [Field k]

namespace AdjointRepresentation

private abbrev F (G : Specs.GroupScheme k) := (groupPointsFunctor k).obj G

private theorem map_comp_apply (G : Specs.GroupScheme k) {R S T : TestAlgebra k}
    (a : R ⟶ S) (b : S ⟶ T) (g : GroupPoints G R) :
    mapPoints (a ≫ b) g = mapPoints b (mapPoints a g) :=
  congrArg (fun f => GrpCat.Hom.hom f g) ((F G).map_comp a b)

private abbrev coordKernel (A : HopfAlgebraCategory k) (R : TestAlgebra k) :=
  Additive (((convolutionPoints A).map (reduction R)).hom.ker)

private abbrev aug (A : HopfAlgebraCategory k) := counitAlgHom k A

private abbrev cot (A : HopfAlgebraCategory k) := PointCotangent (aug A)

private abbrev ideal (A : HopfAlgebraCategory k) := IdentityTangent.augmentationIdeal A

variable (A : HopfAlgebraCategory k) (R : TestAlgebra k)

private theorem coord_fst (p : coordKernel A R) (a : A) :
    (p.toMul.val.ofConv a).fst = algebraMap k R (aug A a) :=
  congrArg (fun f : WithConv (A →ₐ[k] R) => f.ofConv a) p.toMul.property

/-- The augmentation split yields the universal tangent derivation. -/
private def projectAug (a : A) : ideal A :=
  ⟨a - algebraMap k A (aug A a), by simp [RingHom.mem_ker]⟩

private theorem projectAug_add (a b : A) :
    projectAug A (a + b) = projectAug A a + projectAug A b := by
  apply Subtype.ext
  change a + b - algebraMap k A (aug A (a + b)) =
    (a - algebraMap k A (aug A a)) + (b - algebraMap k A (aug A b))
  rw [map_add, map_add, add_sub_add_comm]

private theorem projectAug_mul (a b : A) :
    projectAug A (a * b) = aug A a • projectAug A b + aug A b • projectAug A a +
      (⟨(projectAug A a : A) * (projectAug A b : A),
        (ideal A).mul_mem_left _ (projectAug A b).property⟩ : ideal A) := by
  apply Subtype.ext
  simp only [Submodule.coe_add, Submodule.coe_smul_of_tower, Algebra.smul_def]
  change a * b - algebraMap k A (aug A (a * b)) =
    algebraMap k A (aug A a) * (b - algebraMap k A (aug A b)) +
    algebraMap k A (aug A b) * (a - algebraMap k A (aug A a)) +
    (a - algebraMap k A (aug A a)) * (b - algebraMap k A (aug A b))
  rw [map_mul, map_mul]
  ring

private theorem projectAug_const (a : k) : projectAug A (algebraMap k A a) = 0 := by
  apply Subtype.ext
  change algebraMap k A a - algebraMap k A (aug A (algebraMap k A a)) = 0
  rw [AlgHom.commutes, Algebra.algebraMap_self_apply, sub_self]

private theorem projectAug_mem (a : ideal A) : projectAug A a.val = a := by
  apply Subtype.ext
  change a.val - algebraMap k A (aug A a.val) = a.val
  rw [show aug A a.val = 0 from a.property, map_zero, sub_zero]

private def liftForm (D : cot A →ₗ[k] R) : coordKernel A R := by
  let I := ideal A
  let f : A →ₐ[k] DualNumber R := {
    toFun := fun a => (algebraMap k R (aug A a), D (I.toCotangent (projectAug A a)))
    map_zero' := by
      have h : projectAug A 0 = 0 := by simpa only [map_zero] using projectAug_const A 0
      apply TrivSqZeroExt.ext <;> simp [h]
    map_one' := by
      have h : projectAug A 1 = 0 := by simpa only [map_one] using projectAug_const A 1
      apply TrivSqZeroExt.ext <;> simp [h]
    map_add' := by
      intro a b
      apply TrivSqZeroExt.ext
      · change algebraMap k R (aug A (a + b)) =
          algebraMap k R (aug A a) + algebraMap k R (aug A b)
        simp
      · change D (I.toCotangent (projectAug A (a + b))) =
          D (I.toCotangent (projectAug A a)) + D (I.toCotangent (projectAug A b))
        simp [projectAug_add]
    map_mul' := by
      intro a b
      apply TrivSqZeroExt.ext
      · change algebraMap k R (aug A (a * b)) =
          algebraMap k R (aug A a) * algebraMap k R (aug A b)
        simp
      · change D (I.toCotangent (projectAug A (a * b))) =
          algebraMap k R (aug A a) * D (I.toCotangent (projectAug A b)) +
          D (I.toCotangent (projectAug A a)) * algebraMap k R (aug A b)
        rw [projectAug_mul, map_add, map_add, map_add, map_add]
        rw [show I.toCotangent ⟨(projectAug A a : A) * (projectAug A b : A), _⟩ = 0 from
          (I.toCotangent_eq_zero _).mpr (by
            rw [pow_two]
            exact Ideal.mul_mem_mul (projectAug A a).property (projectAug A b).property)]
        rw [map_zero, add_zero]
        change D ((I.toCotangent.restrictScalars k) (aug A a • projectAug A b)) +
          D ((I.toCotangent.restrictScalars k) (aug A b • projectAug A a)) = _
        simp only [map_smul, Algebra.smul_def]
        rw [mul_comm (algebraMap k R (aug A b))]
        rfl
    commutes' := fun a => by
      apply TrivSqZeroExt.ext
      · exact congrArg (algebraMap k R) (AlgHom.commutes (aug A) a)
      · change D (I.toCotangent (projectAug A (algebraMap k A a))) = 0
        simp [projectAug_const] }
  refine ⟨toConv f, ?_⟩
  apply WithConv.ext
  ext a
  rfl

private theorem liftForm_eval (D : cot A →ₗ[k] R) (a : ideal A) :
    ((liftForm A R D).toMul.val.ofConv a).snd = D ((ideal A).toCotangent a) := by
  change D ((ideal A).toCotangent (projectAug A a)) = _
  rw [projectAug_mem]

private theorem coord_ext {p q : coordKernel A R}
    (h : ∀ a : ideal A, (p.toMul.val.ofConv a).snd = (q.toMul.val.ofConv a).snd) : p = q := by
  apply Subtype.ext
  apply WithConv.ext
  apply AlgHom.ext
  intro a
  apply TrivSqZeroExt.ext
  · exact (coord_fst A R p a).trans (coord_fst A R q a).symm
  · change (p.toMul.val.ofConv a).snd = (q.toMul.val.ofConv a).snd
    have ha : a = (projectAug A a : A) + algebraMap k A (aug A a) := (sub_add_cancel ..).symm
    rw [ha, map_add, map_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_add, h]
    rw [AlgHom.commutes, AlgHom.commutes]

private def readForm (p : coordKernel A R) : cot A →ₗ[k] R := by
  let f := p.toMul.val.ofConv
  let I := ideal A
  let d : I →ₗ[k] R :=
    ((TrivSqZeroExt.sndHom (R := R) (M := R)).restrictScalars k).comp
      (f.toLinearMap.comp (I.subtype.restrictScalars k))
  refine ((I • ⊤ : Submodule A I).restrictScalars k).liftQ d ?_
  intro x hx
  change (f (x : A)).snd = 0
  have hsq : I ^ 2 ≤ RingHom.ker f.toRingHom := by
    rw [pow_two]
    refine Ideal.mul_le.mpr fun a ha b hb => ?_
    change f (a * b) = 0
    rw [map_mul]
    have h₁ := coord_fst A R p a
    have h₂ := coord_fst A R p b
    change (f a).fst = _ at h₁
    change (f b).fst = _ at h₂
    rw [show aug A a = 0 from ha, map_zero] at h₁
    rw [show aug A b = 0 from hb, map_zero] at h₂
    apply TrivSqZeroExt.ext <;> simp [h₁, h₂]
  have hx' : x ∈ LinearMap.ker I.toCotangent := by
    rwa [Ideal.toCotangent, Submodule.ker_mkQ]
  have h := hsq ((I.mem_toCotangent_ker (x := x)).mp hx')
  exact congrArg TrivSqZeroExt.snd (show f (x : A) = 0 from h)

private theorem readForm_eval (p : coordKernel A R) (a : ideal A) :
    readForm A R p ((ideal A).toCotangent a) = (p.toMul.val.ofConv a).snd := rfl

private theorem coord_snd_mul (p q : coordKernel A R) (a : A) :
    ((p + q).toMul.val.ofConv a).snd =
      (p.toMul.val.ofConv a).snd + (q.toMul.val.ofConv a).snd := by
  let f := p.toMul.val.ofConv
  let g := q.toMul.val.ofConv
  let d := (TrivSqZeroExt.sndHom (R := R) (M := R)).restrictScalars k
  let df := d.comp f.toLinearMap
  let dg := d.comp g.toLinearMap
  let m := (Algebra.TensorProduct.map f g).toLinearMap
  have h :
      d ∘ₗ (Algebra.TensorProduct.lmul' k (S := DualNumber R)).toLinearMap ∘ₗ m =
        (dg ∘ₗ (TensorProduct.lid k A).toLinearMap ∘ₗ (counit (R := k)).rTensor A) +
        (df ∘ₗ (TensorProduct.rid k A).toLinearMap ∘ₗ (counit (R := k)).lTensor A) := by
    apply TensorProduct.ext'
    intro b c
    change (f b * g c).snd = dg (counit (R := k) b • c) + df (counit (R := k) c • b)
    rw [DualNumber.snd_mul, show (f b).fst = _ from coord_fst A R p b,
      show (g c).fst = _ from coord_fst A R q c, map_smul, map_smul]
    simp only [Algebra.smul_def]
    change _ = algebraMap k R (aug A b) * (g c).snd + algebraMap k R (aug A c) * (f b).snd
    rw [mul_comm (algebraMap k R (aug A c))]
  have ha := LinearMap.congr_fun h (comul (R := k) a)
  change ((toConv f * toConv g : WithConv (A →ₐ[k] DualNumber R)).ofConv a).snd = df a + dg a
  rw [add_comm, AlgHom.convMul_def]
  change d ((Algebra.TensorProduct.lmul' k (S := DualNumber R)).toLinearMap
    (m (comul (R := k) a))) = dg a + df a
  simpa only [LinearMap.comp_apply, LinearMap.add_apply, rTensor_counit_comul,
    lTensor_counit_comul, LinearEquiv.coe_coe, TensorProduct.lid_tmul, TensorProduct.rid_tmul, one_smul] using ha

private def formEquiv : (cot A →ₗ[k] R) ≃+ coordKernel A R where
  toFun := liftForm A R
  invFun := readForm A R
  left_inv D := by
    ext x
    obtain ⟨a, rfl⟩ := (ideal A).toCotangent_surjective x
    rw [readForm_eval, liftForm_eval]
  right_inv p := coord_ext A R fun a => liftForm_eval A R _ a
  map_add' D E := coord_ext A R fun a => by
    rw [coord_snd_mul, liftForm_eval, liftForm_eval, liftForm_eval]
    rfl


private theorem natural_apply {P Q : TestAlgebra k ⥤ GrpCat.{u}} (e : P ⟶ Q)
    {R S : TestAlgebra k} (a : R ⟶ S) (p : P.obj R) :
    (e.app S).hom ((P.map a).hom p) = (Q.map a).hom ((e.app R).hom p) :=
  congrArg (fun f => GrpCat.Hom.hom f p) (e.naturality a)

private def mapRelativeKernel {P Q : TestAlgebra k ⥤ GrpCat.{u}} (e : P ⟶ Q)
    (R : TestAlgebra k) :
    Additive ((P.map (reduction R)).hom.ker) →+ Additive ((Q.map (reduction R)).hom.ker) where
  toFun p := ⟨(e.app _).hom p.toMul.val, by
    change (Q.map (reduction R)).hom ((e.app _).hom p.toMul.val) = 1
    rw [← natural_apply, p.toMul.property, map_one]⟩
  map_zero' := Subtype.ext (map_one (e.app _).hom)
  map_add' p q := Subtype.ext (map_mul (e.app _).hom p.toMul.val q.toMul.val)

private def relativeKernelIso {P Q : TestAlgebra k ⥤ GrpCat.{u}} (e : P ≅ Q)
    (R : TestAlgebra k) :
    Additive ((P.map (reduction R)).hom.ker) ≃+ Additive ((Q.map (reduction R)).hom.ker) where
  toFun := mapRelativeKernel e.hom R
  invFun := mapRelativeKernel e.inv R
  left_inv p := Subtype.ext (congrArg (fun f => GrpCat.Hom.hom f p.toMul.val)
    (e.hom_inv_id_app _))
  right_inv p := Subtype.ext (congrArg (fun f => GrpCat.Hom.hom f p.toMul.val)
    (e.inv_hom_id_app _))
  map_add' := (mapRelativeKernel e.hom R).map_add

private theorem liftForm_scale (r : R) (D : cot A →ₗ[k] R) :
    (liftForm A R (r • D)).toMul.val =
      ((convolutionPoints A).map (scale R r)).hom (liftForm A R D).toMul.val := by
  apply WithConv.ext
  apply AlgHom.ext
  intro a
  apply TrivSqZeroExt.ext
  · rfl
  · change (r • D) ((ideal A).toCotangent (projectAug A a)) =
      r * D ((ideal A).toCotangent (projectAug A a))
    rw [LinearMap.smul_apply]
    rfl

private theorem liftForm_naturality {S : TestAlgebra k} (a : R ⟶ S) (D : cot A →ₗ[k] R) :
    (liftForm A S (a.hom.toLinearMap.comp D)).toMul.val =
      ((convolutionPoints A).map (dualMap a)).hom (liftForm A R D).toMul.val := by
  apply WithConv.ext
  apply AlgHom.ext
  intro x
  apply TrivSqZeroExt.ext
  · exact (a.hom.commutes (aug A x)).symm
  · rfl

private def schemeFormEquiv {G : Specs.GroupScheme k} (e : convolutionPoints A ≅ F G) :
    (cot A →ₗ[k] R) ≃+ RelativeTangent G R :=
  (formEquiv A R).trans (relativeKernelIso e R)

private theorem schemeFormEquiv_scale {G : Specs.GroupScheme k} (e : convolutionPoints A ≅ F G)
    (r : R) (D : cot A →ₗ[k] R) :
    (schemeFormEquiv A R e (r • D)).toMul.val =
      mapPoints (scale R r) (schemeFormEquiv A R e D).toMul.val := by
  change (e.hom.app _).hom (liftForm A R (r • D)).toMul.val = _
  rw [liftForm_scale]
  exact natural_apply e.hom (scale R r) _

private theorem schemeFormEquiv_naturality {G : Specs.GroupScheme k} (e : convolutionPoints A ≅ F G)
    {S : TestAlgebra k} (a : R ⟶ S) (D : cot A →ₗ[k] R) :
    (schemeFormEquiv A S e (a.hom.toLinearMap.comp D)).toMul.val =
      mapPoints (dualMap a) (schemeFormEquiv A R e D).toMul.val := by
  change (e.hom.app _).hom (liftForm A S (a.hom.toLinearMap.comp D)).toMul.val = _
  rw [liftForm_naturality]
  exact natural_apply e.hom (dualMap a) _

private theorem scale_at_base (r : k) :
    scale (CommAlgCat.of k k) r = CommAlgCat.ofHom (dualNumberScale r) := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  apply TrivSqZeroExt.ext
  · exact (TrivSqZeroExt.fst_map (r • (LinearMap.id : k →ₗ[k] k)) x).symm
  · exact (TrivSqZeroExt.snd_map (r • (LinearMap.id : k →ₗ[k] k)) x).symm

open private augmentationCotangent_finite from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.IdentityTangent

private theorem tangent_coordinates (G : Specs.AffineAlgebraicGroup k)
    (s : Specs.IdentityLieStructure G.val) :
    letI := s.lieRing
    letI := s.lieAlgebra
    ∃ (n : ℕ) (b : Module.Basis (ULift.{u} (Fin n)) k (Lie k G.val)),
      Nonempty (TangentCoordinates G.val (ULift.{u} (Fin n)) b) := by
  let := s.lieRing
  let := s.lieAlgebra
  let E := finiteTypeHopfEquivalence k
  let A₀ := (E.inverse.obj G).unop
  let A := A₀.val
  let : Algebra.FiniteType k A := A₀.property
  let i : hopfSpectrum A ≅ G.val := (inducedFunctor Subtype.val).mapIso (E.counitIso.app G)
  let e := hopfSpecPointIso A ≪≫ (groupPointsFunctor k).mapIso i
  let := augmentationCotangent_finite A
  let C := cot A
  let n := Module.finrank k C
  let c : Module.Basis (ULift.{u} (Fin n)) k C :=
    (Module.finBasis k C).reindex Equiv.ulift.symm
  let f := schemeFormEquiv A (CommAlgCat.of k k) e
  let d : Module.Dual k C ≃ₗ[k] Lie k G.val :=
    { f.toEquiv with
      map_add' := fun x y => by
        have h := f.map_add x y
        have ha := congrArg (fun g : AddGroup (PointKernel G.val) => g.toAdd.add) s.group_law
        exact h.trans (congrFun (congrFun ha (f x)) (f y)).symm
      map_smul' := fun r D => by
        have hf := schemeFormEquiv_scale A (CommAlgCat.of k k) e r D
        have hs := congrArg (fun p : Lie k G.val => p.toMul.val)
          (congrFun (congrFun s.scalar_law r) (f D))
        rw [scale_at_base] at hf
        exact Subtype.ext (hf.trans hs.symm) }
  let b := c.dualBasis.map d
  refine ⟨n, b, ⟨{
    equiv := fun R => (c.constr R).toAddEquiv.trans (schemeFormEquiv A R e)
    smul := ?_
    naturality := ?_
    at_base := ?_ }⟩⟩
  · intro R r v
    change (schemeFormEquiv A R e (c.constr R (r • v))).toMul.val = _
    rw [map_smul]
    exact schemeFormEquiv_scale A R e r _
  · intro R S a v
    have h : c.constr S (fun j => a.hom (v j)) =
        a.hom.toLinearMap.comp (c.constr R v) := by
      apply c.ext
      intro j
      change c.constr S (fun j => a.hom (v j)) (c j) = a.hom (c.constr R v (c j))
      rw [c.constr_basis, c.constr_basis]
    change (schemeFormEquiv A S e (c.constr S (fun j => a.hom (v j)))).toMul.val = _
    rw [h]
    exact schemeFormEquiv_naturality A R e a _
  · intro p
    have h : c.constr k (b.equivFun p) = d.symm p := by
      apply c.ext
      intro j
      rw [c.constr_basis]
      change (c.dualBasis.map d).equivFun p j = d.symm p (c j)
      rw [Module.Basis.map_equivFun, LinearEquiv.trans_apply, Module.Basis.dualBasis_equivFun]
    change (d (c.constr k (b.equivFun p))).toMul.val = _
    rw [h, d.apply_symm_apply]

section Conjugation

variable {G : Specs.GroupScheme k} {ι : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup (Lie k G)] [Module k (Lie k G)]
  {b : Module.Basis ι k (Lie k G)} (T : TangentCoordinates G ι b)
  {R : TestAlgebra k}

private def conjugateTangent (g : GroupPoints G R) (v : RelativeTangent G R) :
    RelativeTangent G R :=
  ⟨conjugate g v, by
    change ((F G).map (reduction R)).hom
      (((F G).map (constants R)).hom g * v.toMul.val *
        (((F G).map (constants R)).hom g)⁻¹) = 1
    rw [map_mul, map_mul, map_inv, v.toMul.property, mul_one, mul_inv_cancel]⟩

private theorem constants_scale (r : R) : constants R ≫ scale R r = constants R := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  apply TrivSqZeroExt.ext
  · rfl
  · change r * 0 = 0
    exact mul_zero r

private theorem constants_dualMap {S : TestAlgebra k} (a : R ⟶ S) :
    constants R ≫ dualMap a = a ≫ constants S := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  exact TrivSqZeroExt.ext rfl (map_zero a.hom)

private def conjugationLinear (g : GroupPoints G R) : (ι → R) →ₗ[R] (ι → R) where
  toFun v := (T.equiv R).symm (conjugateTangent g (T.equiv R v))
  map_add' v w := by
    apply (T.equiv R).injective
    rw [AddEquiv.apply_symm_apply, map_add, map_add, AddEquiv.apply_symm_apply,
      AddEquiv.apply_symm_apply]
    apply Subtype.ext
    change _ * ((T.equiv R v).toMul.val * (T.equiv R w).toMul.val) * _ =
      (_ * (T.equiv R v).toMul.val * _) * (_ * (T.equiv R w).toMul.val * _)
    group
  map_smul' r v := by
    apply (T.equiv R).injective
    rw [AddEquiv.apply_symm_apply, RingHom.id_apply]
    apply Subtype.ext
    change conjugate g (T.equiv R (r • v)) = (T.equiv R (r • _)).toMul.val
    rw [T.smul]
    rw [AddEquiv.apply_symm_apply]
    change _ = ((F G).map (scale R r)).hom (conjugate g (T.equiv R v))
    unfold conjugate
    rw [T.smul]
    rw [map_mul, map_mul, map_inv]
    have h := (map_comp_apply G (constants R) (scale R r) g).symm
    rw [constants_scale] at h
    rw [show ((F G).map (scale R r)).hom (((F G).map (constants R)).hom g) =
      ((F G).map (constants R)).hom g from h]
    rfl

private theorem conjugationLinear_spec (g : GroupPoints G R) (v : ι → R) :
    (T.equiv R (conjugationLinear T g v)).toMul.val = conjugate g (T.equiv R v) :=
  congrArg (fun p => p.toMul.val) ((T.equiv R).apply_symm_apply _)

private def conjugationEnd : GroupPoints G R →* Module.End R (ι → R) where
  toFun := conjugationLinear T
  map_one' := by
    apply LinearMap.ext
    intro v
    change conjugationLinear T (1 : GroupPoints G R) v = v
    apply (T.equiv R).injective
    apply Subtype.ext
    change (T.equiv R (conjugationLinear T 1 v)).toMul.val = (T.equiv R v).toMul.val
    rw [conjugationLinear_spec]
    simp [conjugate]
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    change conjugationLinear T (g * h) v =
      conjugationLinear T g (conjugationLinear T h v)
    apply (T.equiv R).injective
    apply Subtype.ext
    change (T.equiv R (conjugationLinear T (g * h) v)).toMul.val =
      (T.equiv R (conjugationLinear T g (conjugationLinear T h v))).toMul.val
    rw [conjugationLinear_spec, conjugationLinear_spec]
    unfold conjugate
    rw [conjugationLinear_spec, conjugate, map_mul]
    dsimp only
    group

private def conjugationMatrix : GroupPoints G R →* Matrix.GeneralLinearGroup ι R :=
  ((LinearMap.toMatrixAlgEquiv' (R := R) (n := ι)).toMonoidHom.comp
    (conjugationEnd T)).toHomUnits

private theorem conjugationMatrix_spec (g : GroupPoints G R) (v : ι → R) :
    (T.equiv R ((conjugationMatrix T g).val *ᵥ v)).toMul.val = conjugate g (T.equiv R v) := by
  change (T.equiv R ((LinearMap.toMatrix' (conjugationLinear T g)) *ᵥ v)).toMul.val = _
  rw [LinearMap.toMatrix'_mulVec, conjugationLinear_spec]

set_option backward.isDefEq.respectTransparency false in
private theorem conjugationLinear_naturality {S : TestAlgebra k} (a : R ⟶ S)
    (g : GroupPoints G R) (v : ι → R) :
    conjugationLinear T (mapPoints a g) (fun i => a.hom (v i)) =
      fun i => a.hom (conjugationLinear T g v i) := by
  apply (T.equiv S).injective
  apply Subtype.ext
  change (T.equiv S (conjugationLinear T (mapPoints a g) (fun i => a.hom (v i)))).toMul.val =
    (T.equiv S (fun i => a.hom (conjugationLinear T g v i))).toMul.val
  rw [conjugationLinear_spec, T.naturality, conjugationLinear_spec]
  unfold conjugate
  rw [T.naturality]
  have h : mapPoints (constants S) (mapPoints a g) =
      mapPoints (dualMap a) (mapPoints (constants R) g) := by
    rw [← map_comp_apply, ← map_comp_apply, constants_dualMap]
  change (((F G).map (constants S)).hom (mapPoints a g)) *
      ((F G).map (dualMap a)).hom (T.equiv R v).toMul.val *
      (((F G).map (constants S)).hom (mapPoints a g))⁻¹ =
    ((F G).map (dualMap a)).hom _
  change ((F G).map (constants S)).hom (mapPoints a g) =
    ((F G).map (dualMap a)).hom (((F G).map (constants R)).hom g) at h
  rw [h, map_mul, map_mul, map_inv]

private def conjugationTransformation : F G ⟶ Specs.StandardGroups.generalLinearPoints k ι where
  app R := GrpCat.ofHom (X := (F G).obj R) (conjugationMatrix (R := R) T)
  naturality R S a := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro g
    apply Units.ext
    apply Matrix.ext
    intro i j
    have h : (fun l => a.hom ((Pi.single (M := fun _ : ι => R) j 1) l)) = Pi.single j (1 : S) := by
      funext l
      by_cases e : l = j <;> simp [e]
    change conjugationLinear T (mapPoints a g) (Pi.single j (1 : S)) i =
      a.hom (conjugationLinear T g (Pi.single (M := fun _ : ι => R) j 1) i)
    rw [← h, conjugationLinear_naturality]

end Conjugation

section Differential

open InfinitesimalCommutator

private abbrev baseTest (k : Type u) [Field k] := CommAlgCat.of k k
private abbrev dualTest (k : Type u) [Field k] := CommAlgCat.of k (DualNumber k)

private theorem constant_dualMap :
    dualMap (constants (baseTest k)) = CommAlgCat.ofHom (liftT k) := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  rfl

private theorem constant_mixed :
    CommAlgCat.ofHom (liftT k) ≫ scale (dualTest k) DualNumber.eps =
      CommAlgCat.ofHom (liftST k) := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  apply TrivSqZeroExt.ext
  · rfl
  · change (DualNumber.eps : DualNumber k) * (TrivSqZeroExt.inl x.snd) =
      TrivSqZeroExt.inr x.snd
    apply TrivSqZeroExt.ext
    · change (0 : k) * x.snd = 0
      exact zero_mul _
    · change (0 : k) * 0 + 1 * x.snd = x.snd
      simp

variable {G L : Specs.GroupScheme k} {ι : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup (Lie k G)] [Module k (Lie k G)]
  {b : Module.Basis ι k (Lie k G)} (T : TangentCoordinates G ι b)
  (l : F L ≅ Specs.StandardGroups.generalLinearPoints k ι)
  (Ad : G ⟶ L)

private def extendVector (v : ι → k) : ι → DualNumber k :=
  fun i => TrivSqZeroExt.inl (v i)

private theorem constant_tangent (p : Lie k G) :
    (T.equiv (dualTest k) (extendVector (b.equivFun p))).toMul.val =
      mapPoints (CommAlgCat.ofHom (liftT k)) p.toMul.val := by
  have h := T.naturality (constants (baseTest k)) (b.equivFun p)
  rw [T.at_base, constant_dualMap] at h
  exact h

private theorem mixed_tangent (p : Lie k G) :
    (T.equiv (dualTest k) ((DualNumber.eps : DualNumber k) •
      extendVector (b.equivFun p))).toMul.val =
      mapPoints (CommAlgCat.ofHom (liftST k)) p.toMul.val := by
  rw [T.smul, constant_tangent, ← map_comp_apply, constant_mixed]

private theorem differential_formula
    (hAd : ∀ (R : TestAlgebra k) (g : GroupPoints G R) (v : ι → R),
      let M := (l.hom.app R).hom (((groupPointsFunctor k).map Ad).app R g)
      (T.equiv R (M.val *ᵥ v)).toMul.val = conjugate g (T.equiv R v))
    {br : Lie k G → Lie k G → Lie k G} (hbr : IsBracket (F G) br) (x y : Lie k G) :
    matrixDifferential Ad l x *ᵥ b.equivFun y = b.equivFun (br x y) := by
  let D := dualTest k
  let M := (l.hom.app D).hom (((groupPointsFunctor k).map Ad).app D x.toMul.val)
  let v := extendVector (b.equivFun y)
  let w := extendVector (b.equivFun (br x y))
  have hv := hAd D x.toMul.val v
  change (T.equiv D (M.val *ᵥ v)).toMul.val = _ at hv
  have hprod : M.val *ᵥ v = (DualNumber.eps : DualNumber k) • w + v := by
    apply (T.equiv D).injective
    apply Subtype.ext
    change (T.equiv D (M.val *ᵥ v)).toMul.val =
      (T.equiv D ((DualNumber.eps : DualNumber k) • w + v)).toMul.val
    rw [hv, map_add]
    change conjugate x.toMul.val (T.equiv D (extendVector (b.equivFun y))) =
      (T.equiv D ((DualNumber.eps : DualNumber k) • extendVector (b.equivFun (br x y)))).toMul.val *
        (T.equiv D (extendVector (b.equivFun y))).toMul.val
    unfold conjugate
    rw [mixed_tangent T, constant_tangent T]
    have h := hbr x y
    change mapPoints (CommAlgCat.ofHom (liftST k)) (br x y).toMul.val =
      InfinitesimalCommutator.commutator (F G) x y at h
    rw [h]
    unfold InfinitesimalCommutator.commutator
    let aS : dualTest k ⟶ CommAlgCat.of k (TwoVariables k) := CommAlgCat.ofHom (liftS k)
    let aT : dualTest k ⟶ CommAlgCat.of k (TwoVariables k) := CommAlgCat.ofHom (liftT k)
    let sx := ((F G).map aS).hom x.toMul.val
    let ty := ((F G).map aT).hom y.toMul.val
    change sx * ty * sx⁻¹ = sx * ty * sx⁻¹ * ty⁻¹ * ty
    group
  funext i
  have h := congrArg (fun z : ι → DualNumber k => (z i).snd) hprod
  change (∑ j, M.val i j * v j).snd = ((DualNumber.eps : DualNumber k) * w i + v i).snd at h
  rw [TrivSqZeroExt.snd_sum, TrivSqZeroExt.snd_add, DualNumber.snd_mul] at h
  have hL (j : ι) : (M.val i j * v j).snd = (M.val i j).snd * b.equivFun y j := by
    rw [DualNumber.snd_mul]
    change (M.val i j).fst * 0 + (M.val i j).snd * b.equivFun y j = _
    simp only [mul_zero, zero_add]
  change (∑ j : ι, (M.val i j * v j).snd) =
    (0 : k) * 0 + 1 * b.equivFun (br x y) i + 0 at h
  simp only [mul_zero, one_mul, zero_add, add_zero] at h
  change (∑ j : ι, (M.val i j).snd * b.equivFun y j) = b.equivFun (br x y) i
  exact (Finset.sum_congr rfl (fun j _ => (hL j).symm)).trans h

end Differential


section ScalarExtension

variable (K : Type u) [Field K] [Algebra k K]

private abbrev restrict := restrictTestAlgebra k K
private abbrev extGroup := groupBaseChange k K

private theorem algebra_hom_ext {P Q : TestAlgebra k} {f g : P ⟶ Q}
    (h : ∀ x : P, f.hom x = g.hom x) : f = g :=
  CommAlgCat.hom_ext (@AlgHom.ext k P Q _ _ _ P.algebra Q.algebra _ _ h)

private theorem restriction_dualMap {R S : TestAlgebra K} (a : R ⟶ S) :
    (restrict (k := k) K).map (dualMap a) ≫ (dualRestriction K S).hom =
      (dualRestriction K R).hom ≫ dualMap ((restrict (k := k) K).map a) := by
  exact algebra_hom_ext fun _ => rfl

private theorem restriction_scale (R : TestAlgebra K) (r : R) :
    (restrict (k := k) K).map (scale R r) ≫ (dualRestriction K R).hom =
      (dualRestriction K R).hom ≫ scale ((restrict (k := k) K).obj R) r := by
  exact algebra_hom_ext fun _ => rfl

private theorem restriction_reduction (R : TestAlgebra K) :
    (restrict (k := k) K).map (reduction R) =
      (dualRestriction K R).hom ≫ reduction ((restrict (k := k) K).obj R) := by
  exact algebra_hom_ext fun _ => rfl

private theorem restriction_constants (R : TestAlgebra K) :
    (restrict (k := k) K).map (constants R) ≫ (dualRestriction K R).hom =
      constants ((restrict (k := k) K).obj R) := by
  exact algebra_hom_ext fun _ => rfl

private abbrev baseInclusion : baseTest k ⟶ (restrict (k := k) K).obj (baseTest K) :=
  let R := (restrict (k := k) K).obj (baseTest K)
  ConcreteCategory.ofHom (C := CommAlgCat k) (Y := R) (@Algebra.ofId k R _ _ R.algebra)

private theorem extension_dualMap :
    extendDualNumber (k := k) K ≫ (dualRestriction K (baseTest K)).hom =
      dualMap (baseInclusion (k := k) K) := by
  exact algebra_hom_ext fun _ => rfl

variable (G : Specs.GroupScheme k)

private abbrev pointRestrict (R : TestAlgebra K) :
    GroupPoints ((extGroup K).obj G) R ≃* GroupPoints G ((restrict (k := k) K).obj R) :=
  baseChangePointGroupEquiv K G R

private theorem pointRestrict_naturality {R S : TestAlgebra K} (a : R ⟶ S)
    (p : GroupPoints ((extGroup K).obj G) R) :
    pointRestrict K G S (mapPoints a p) =
      mapPoints ((restrict (k := k) K).map a) (pointRestrict K G R p) :=
  baseChangePointsNaturality k K G.X a p

private def relativePointRestrict (R : TestAlgebra K) :
    GroupPoints ((extGroup K).obj G) (CommAlgCat.of K (DualNumber R)) ≃*
      GroupPoints G (CommAlgCat.of k (DualNumber ((restrict (k := k) K).obj R))) :=
  (pointRestrict K G (CommAlgCat.of K (DualNumber R))).trans
    (((F G).mapIso (dualRestriction (k := k) K R)).groupIsoToMulEquiv)

private theorem relativePointRestrict_naturality {R S : TestAlgebra K} (a : R ⟶ S)
    (p : GroupPoints ((extGroup K).obj G) (CommAlgCat.of K (DualNumber R))) :
    relativePointRestrict K G S (mapPoints (dualMap a) p) =
      mapPoints (dualMap ((restrict (k := k) K).map a)) (relativePointRestrict K G R p) := by
  change mapPoints (dualRestriction K S).hom
      (pointRestrict K G _ (mapPoints (dualMap a) p)) = _
  rw [pointRestrict_naturality, ← map_comp_apply, restriction_dualMap, map_comp_apply]
  rfl

private theorem relativePointRestrict_scale (R : TestAlgebra K) (r : R)
    (p : GroupPoints ((extGroup K).obj G) (CommAlgCat.of K (DualNumber R))) :
    relativePointRestrict K G R (mapPoints (scale R r) p) =
      mapPoints (scale ((restrict (k := k) K).obj R) r) (relativePointRestrict K G R p) := by
  change mapPoints (dualRestriction K R).hom
      (pointRestrict K G _ (mapPoints (scale R r) p)) = _
  rw [pointRestrict_naturality, ← map_comp_apply, restriction_scale, map_comp_apply]
  rfl

private def tangentRestrict (R : TestAlgebra K) :
    RelativeTangent ((extGroup K).obj G) R ≃+ RelativeTangent G ((restrict (k := k) K).obj R) := by
  let H := (extGroup K).obj G
  let S := (restrict (k := k) K).obj R
  let e := relativePointRestrict K G R
  let d := pointRestrict K G R
  have h (p : GroupPoints H (CommAlgCat.of K (DualNumber R))) :
      d (((F H).map (reduction R)).hom p) = ((F G).map (reduction S)).hom (e p) :=
    calc
      _ = mapPoints ((restrict (k := k) K).map (reduction R)) (pointRestrict K G _ p) :=
        pointRestrict_naturality K G (reduction R) p
      _ = _ := by rw [restriction_reduction, map_comp_apply]; rfl
  have hker (p : GroupPoints H (CommAlgCat.of K (DualNumber R))) :
      p ∈ ((F H).map (reduction R)).hom.ker ↔
        e p ∈ ((F G).map (reduction S)).hom.ker := by
    change ((F H).map (reduction R)).hom p = 1 ↔ ((F G).map (reduction S)).hom (e p) = 1
    rw [← h, ← d.map_one, d.injective.eq_iff]
  let f : (((F H).map (reduction R)).hom.ker) ≃*
      (((F G).map (reduction S)).hom.ker) :=
    { toFun := fun p => ⟨e p.val, (hker _).mp p.property⟩
      invFun := fun q => ⟨e.symm q.val, (hker _).mpr (by
        rw [e.apply_symm_apply]
        exact q.property)⟩
      left_inv := fun p => Subtype.ext (e.symm_apply_apply p.val)
      right_inv := fun q => Subtype.ext (e.apply_symm_apply q.val)
      map_mul' := fun p q => Subtype.ext (e.map_mul p.val q.val) }
  exact f.toAdditive

private theorem tangentRestrict_apply (R : TestAlgebra K)
    (p : RelativeTangent ((extGroup K).obj G) R) :
    (tangentRestrict K G R p).toMul.val =
      relativePointRestrict K G R p.toMul.val := rfl

private theorem pointRestrict_conjugate (R : TestAlgebra K)
    (g : GroupPoints ((extGroup K).obj G) R) (p : RelativeTangent ((extGroup K).obj G) R) :
    relativePointRestrict K G R (conjugate g p) =
      conjugate (pointRestrict K G R g) (tangentRestrict K G R p) := by
  unfold conjugate
  dsimp only
  rw [map_mul, map_mul, map_inv]
  have h : relativePointRestrict K G R (((F ((extGroup K).obj G)).map (constants R)).hom g) =
      ((F G).map (constants ((restrict (k := k) K).obj R))).hom (pointRestrict K G R g) := by
    change mapPoints (dualRestriction K R).hom (pointRestrict K G _ (mapPoints (constants R) g)) =
      mapPoints (constants ((restrict (k := k) K).obj R)) (pointRestrict K G R g)
    rw [pointRestrict_naturality, ← map_comp_apply, restriction_constants]
  rw [h, tangentRestrict_apply]

private theorem relativePointRestrict_scheme {L : Specs.GroupScheme k} (Ad : G ⟶ L)
    (R : TestAlgebra K) (p : GroupPoints ((extGroup K).obj G) R) :
    baseChangePoint k K L.X R (((groupPointsFunctor K).map ((extGroup K).map Ad)).app R p) =
      ((groupPointsFunctor k).map Ad).app ((restrict (k := k) K).obj R)
        (pointRestrict K G R p) :=
  baseChangePointsSchemeNaturality k K Ad.hom.hom R p

set_option maxHeartbeats 800000 in
private theorem scalar_extension (G₀ : Specs.AffineAlgebraicGroup k)
    (s : Specs.IdentityLieStructure G₀.val)
    {L : Specs.GroupScheme k} {ι : Type u} [Fintype ι] [DecidableEq ι]
    (b : letI := s.lieRing; letI := s.lieAlgebra; Module.Basis ι k (Lie k G₀.val))
    (T : letI := s.lieRing; letI := s.lieAlgebra; TangentCoordinates G₀.val ι b)
    (l : F L ≅ Specs.StandardGroups.generalLinearPoints k ι)
    (Ad : G₀.val ⟶ L)
    (hAd : letI := s.lieRing; letI := s.lieAlgebra; ∀ (R : TestAlgebra k) (g : GroupPoints G₀.val R) (v : ι → R),
      let M := (l.hom.app R).hom (((groupPointsFunctor k).map Ad).app R g)
      (T.equiv R (M.val *ᵥ v)).toMul.val = conjugate g (T.equiv R v)) :
    ScalarExtension s b T l Ad := by
  intro K _ _ H sK
  let := s.lieRing
  let := s.lieAlgebra
  let := sK.lieRing
  let := sK.lieAlgebra
  let G := G₀.val
  obtain ⟨e, he⟩ := (identityLieBracketBaseChange k K G₀).2 s sK
  let bK := (b.baseChange K).map e.toLinearEquiv
  let E (R : TestAlgebra K) : (ι → R) ≃+ RelativeTangent H R :=
    (T.equiv ((restrict (k := k) K).obj R)).trans (tangentRestrict K G R).symm
  have hE (R : TestAlgebra K) (v : ι → R) :
      relativePointRestrict K G R (E R v).toMul.val =
        (T.equiv ((restrict (k := k) K).obj R) v).toMul.val := by
    change (tangentRestrict K G R (E R v)).toMul.val = _
    exact congrArg (fun p => p.toMul.val) ((tangentRestrict K G R).apply_symm_apply _)
  have hunit (p : Lie k G) :
      (T.equiv ((restrict (k := k) K).obj (baseTest K))
        (bK.equivFun (e (1 ⊗ₜ[k] p)))).toMul.val =
      relativePointRestrict K G (baseTest K) (e (1 ⊗ₜ[k] p)).toMul.val := by
    have hc : bK.equivFun (e (1 ⊗ₜ[k] p)) = fun i =>
        (baseInclusion (k := k) K).hom (b.equivFun p i) := by
      funext i
      change ((b.baseChange K).map e.toLinearEquiv).equivFun (e (1 ⊗ₜ[k] p)) i = _
      rw [Module.Basis.map_equivFun, LinearEquiv.trans_apply]
      change (b.baseChange K).equivFun (e.toLinearEquiv.symm (e.toLinearEquiv (1 ⊗ₜ[k] p))) i = _
      rw [LinearEquiv.symm_apply_apply, Module.Basis.equivFun_apply,
        Module.Basis.baseChange_repr_tmul]
      change b.repr p i • (1 : K) = algebraMap k K (b.equivFun p i)
      rw [Algebra.smul_def, mul_one, Module.Basis.equivFun_apply]
    rw [hc, T.naturality, T.at_base]
    change _ = mapPoints (dualRestriction K (baseTest K)).hom
      (baseChangePoint k K G.X (dualTest K) (e (1 ⊗ₜ[k] p)).toMul.val)
    rw [he, ← map_comp_apply, extension_dualMap]
  let D : Lie K H →ₗ[K] (ι → K) :=
    { toFun := fun y => (E (baseTest K)).symm y
      map_add' := fun x y => by
        have ha := congrArg (fun g : AddGroup (PointKernel H) => g.toAdd.add) sK.group_law
        exact (congrArg (E (baseTest K)).symm (congrFun (congrFun ha x) y)).trans
          ((E (baseTest K)).symm.map_add x y)
      map_smul' := fun t y => by
        let R := baseTest K
        let w := (E R).symm y
        have hw : E R w = y := (E R).apply_symm_apply y
        have hs := congrFun (congrFun sK.scalar_law t) y
        have hp := relativePointRestrict_scale K G R t y.toMul.val
        rw [scale_at_base] at hp
        apply (E R).injective
        apply Subtype.ext
        apply (relativePointRestrict K G R).injective
        change relativePointRestrict K G R
            (E R ((E R).symm (@SMul.smul K (Lie K H)
              sK.lieAlgebra.toModule.toDistribMulAction.toMulAction.toSMul t y))).toMul.val =
          relativePointRestrict K G R (E R (t • w)).toMul.val
        rw [AddEquiv.apply_symm_apply, hs, hE, T.smul, ← hE R w, hw]
        exact hp }
  have hD : D = bK.equivFun.toLinearMap := by
    apply bK.ext
    intro j
    have hb : bK j = e (1 ⊗ₜ[k] b j) := by
      change ((b.baseChange K).map e.toLinearEquiv) j = _
      rw [Module.Basis.map_apply, Module.Basis.baseChange_apply]
      rfl
    rw [hb]
    apply (E (baseTest K)).injective
    apply Subtype.ext
    apply (relativePointRestrict K G (baseTest K)).injective
    change relativePointRestrict K G (baseTest K)
        (E (baseTest K) ((E (baseTest K)).symm (e (1 ⊗ₜ[k] b j)))).toMul.val =
      relativePointRestrict K G (baseTest K)
        (E (baseTest K) (bK.equivFun (e (1 ⊗ₜ[k] b j)))).toMul.val
    rw [AddEquiv.apply_symm_apply, hE]
    exact (hunit (b j)).symm
  let TK : TangentCoordinates H ι bK := {
    equiv := E
    smul := fun R r v => by
      apply (relativePointRestrict K G R).injective
      rw [hE, relativePointRestrict_scale, hE, T.smul]
    naturality := fun {R S} a v => by
      apply (relativePointRestrict K G S).injective
      rw [hE, relativePointRestrict_naturality, hE]
      exact T.naturality ((restrict (k := k) K).map a) v
    at_base := fun p => by
      change (E (baseTest K) (bK.equivFun p)).toMul.val = p.toMul.val
      have h := LinearMap.congr_fun hD p
      change (E (baseTest K)).symm p = bK.equivFun p at h
      rw [← h, AddEquiv.apply_symm_apply] }
  refine ⟨e, TK, he, hE, ?_⟩
  intro R g v
  apply (relativePointRestrict K G R).injective
  change relativePointRestrict K G R (E R (_ *ᵥ v)).toMul.val =
    relativePointRestrict K G R (conjugate g (E R v))
  rw [hE, pointRestrict_conjugate]
  rw [relativePointRestrict_scheme K G Ad R g]
  have h := hAd ((restrict (k := k) K).obj R) (pointRestrict K G R g) v
  have ht : tangentRestrict K G R (E R v) =
      T.equiv ((restrict (k := k) K).obj R) v := (tangentRestrict K G R).apply_symm_apply _
  rw [ht]
  exact h

end ScalarExtension

end AdjointRepresentation

/-- For an affine algebraic group, the relative tangent action of conjugation
is rational, commutes with scalar extension, and differentiates to the bracket. -/
theorem adjointRepresentation : Specs.AdjointRepresentation.ConjugationRepresentation.{u} := by
  intro k _ G s
  let := s.lieRing
  let := s.lieAlgebra
  obtain ⟨n, b, ⟨T⟩⟩ := AdjointRepresentation.tangent_coordinates G s
  let ι := ULift.{u} (Fin n)
  let L := StandardGroups.generalLinearGroup k ι
  let l := StandardGroups.generalLinearGroupPointsIso k ι
  let a := AdjointRepresentation.conjugationTransformation T
  let E := groupHomEquiv G.val L.val G.property.1
  let Ad := E.symm (a ≫ l.inv)
  have he : (groupPointsFunctor k).map Ad = a ≫ l.inv := E.apply_symm_apply _
  have hAl : (groupPointsFunctor k).map Ad ≫ l.hom = a := by
    rw [he, Category.assoc, l.inv_hom_id, Category.comp_id]
  have hAd (R : TestAlgebra k) (g : GroupPoints G.val R) (v : ι → R) :
      let M := (l.hom.app R).hom (((groupPointsFunctor k).map Ad).app R g)
      (T.equiv R (M.val *ᵥ v)).toMul.val = conjugate g (T.equiv R v) := by
    have hm := congrArg (fun α : AdjointRepresentation.F G.val ⟶
        Specs.StandardGroups.generalLinearPoints k ι => (α.app R).hom g) hAl
    change (l.hom.app R).hom (((groupPointsFunctor k).map Ad).app R g) =
      AdjointRepresentation.conjugationMatrix T g at hm
    dsimp only
    rw [hm]
    exact AdjointRepresentation.conjugationMatrix_spec T g v
  exact ⟨n, b, T, L, l, Ad, hAd,
    AdjointRepresentation.differential_formula T l Ad hAd s.commutator_law,
    AdjointRepresentation.scalar_extension G s b T l Ad hAd⟩

/-- The combined identity tangent, Lie algebra, and adjoint representation result. -/
theorem lieAlgebraAndAdjoint : Specs.AdjointRepresentation.LieAlgebraAndAdjoint.{u} :=
  ⟨lieAffineComparison, lieFunctoriality, identityLieBracket, identityDifferentialLieHom,
    identityLieBracketBaseChange, adjointRepresentation⟩

end
end LinearAlgebraicGroups
