import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.Forms
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AffineGroups
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.NonabelianCohomology
import Batteries.Tactic.OpenPrivate
import Mathlib.CategoryTheory.Conj
import Mathlib.CategoryTheory.HomCongr

open CategoryTheory AlgebraicGeometry Coalgebra HopfAlgebra Module
open scoped TensorProduct

namespace LinearAlgebraicGroups.Descent.Forms

open NonabelianCohomology

universe u
noncomputable section

set_option maxRecDepth 2000

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

local instance formCoefficientTopology (A : HopfAlgebraCategory k) :
    TopologicalSpace (Coefficients K A) := ⊥

local instance formCoefficientDiscrete (A : HopfAlgebraCategory k) :
    DiscreteTopology (Coefficients K A) := ⟨rfl⟩

variable {A B C : HopfAlgebraCategory K}

section Semilinear

private theorem tensor_intertwine {R S : SemilinearAction k K A}
    {T U : SemilinearAction k K B} (f : A ⟶ B) (σ : Gal(K/k))
    (h : ∀ x, f.hom (R.act σ x) = T.act σ (f.hom x))
    (h' : ∀ x, f.hom (S.act σ x) = U.act σ (f.hom x))
    (x : A ⊗[K] A) :
    Algebra.TensorProduct.map f.hom.toAlgHom f.hom.toAlgHom ((R.tensor S).act σ x) =
      (T.tensor U).act σ (Algebra.TensorProduct.map f.hom.toAlgHom f.hom.toAlgHom x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    simp only [SemilinearAction.tensor_act_tmul, Algebra.TensorProduct.map_tmul]
    exact congrArg₂ (fun a b => a ⊗ₜ[K] b) (h a) (h' b)
  | add a b ha hb => simp only [map_add, ha, hb]

private theorem tensor_apply_hom {R : SemilinearAction k K A} (f : A ⟶ A)
    (T : SemilinearAction k K A) (σ : Gal(K/k))
    (h : ∀ x, T.act σ x = f.hom (R.act σ x)) (x : A ⊗[K] A) :
    (T.tensor T).act σ x =
      Algebra.TensorProduct.map f.hom.toAlgHom f.hom.toAlgHom ((R.tensor R).act σ x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    simp only [SemilinearAction.tensor_act_tmul, Algebra.TensorProduct.map_tmul, h]
    rfl
  | add a b ha hb => simp only [map_add, ha, hb]

private theorem hom_apply {A B : HopfAlgebraCategory K} (i : A ≅ B) (x : A) :
    i.inv.hom (i.hom.hom x) = x :=
  ConcreteCategory.congr_hom i.hom_inv_id x

private theorem inv_apply {A B : HopfAlgebraCategory K} (i : A ≅ B) (x : B) :
    i.hom.hom (i.inv.hom x) = x :=
  ConcreteCategory.congr_hom i.inv_hom_id x

private theorem act_inv_apply (D : SemilinearAction k K A) (σ : Gal(K/k)) (x : A) :
    D.act σ⁻¹ (D.act σ x) = x := by
  rw [← D.mul_act, inv_mul_cancel, D.one_act]

private theorem act_apply_inv (D : SemilinearAction k K A) (σ : Gal(K/k)) (x : A) :
    D.act σ (D.act σ⁻¹ x) = x := by
  rw [← D.mul_act, mul_inv_cancel, D.one_act]

private theorem comul_hom (f : A ⟶ B) (x : A) :
    Algebra.TensorProduct.map f.hom.toAlgHom f.hom.toAlgHom (comul (R := K) x) =
      comul (R := K) (f.hom x) :=
  CoalgHomClass.map_comp_comul_apply f.hom x

private theorem antipode_hom (f : A ⟶ B) (x : A) :
    f.hom (antipode K x) = antipode K (f.hom x) :=
  DFunLike.congr_fun (hopfSpecMorphism K f).2 x

private def transport (D : HopfDescentDatum k B) (i : A ≅ B) : HopfDescentDatum k A := by
  let T : SemilinearAction k K A :=
    { act := fun σ => ((CommHopfAlgCat.isoEquivBialgEquiv i).toAddEquiv.trans (D.action.act σ)).trans
        (CommHopfAlgCat.isoEquivBialgEquiv i).symm.toAddEquiv
      one_act := fun x => show i.inv.hom (D.action.act 1 (i.hom.hom x)) = x by
        rw [D.action.one_act, hom_apply]
      mul_act := fun σ τ x => show i.inv.hom (D.action.act (σ * τ) (i.hom.hom x)) =
        i.inv.hom (D.action.act σ (i.hom.hom (i.inv.hom (D.action.act τ (i.hom.hom x))))) by
        rw [inv_apply, D.action.mul_act]
      map_smul := fun σ r x => show i.inv.hom (D.action.act σ (i.hom.hom (r • x))) =
        σ r • i.inv.hom (D.action.act σ (i.hom.hom x)) by
        rw [map_smul, D.action.map_smul, map_smul] }
  have hi (σ : Gal(K/k)) (x : A) : i.hom.hom (T.act σ x) = D.action.act σ (i.hom.hom x) :=
    inv_apply i _
  have inj : Function.Injective i.hom.hom := fun x y h => by
    simpa only [hom_apply] using congrArg i.inv.hom h
  refine ⟨T, ?_, ?_, ?_, ?_, ?_⟩
  · intro σ
    apply inj
    rw [hi, map_one, D.map_one]
  · intro σ x y
    apply inj
    rw [hi, map_mul, D.map_mul, map_mul, hi, hi]
  · intro σ x
    have hinj := TensorProduct.map_injective_of_flat_flat
      i.hom.hom.toLinearMap i.hom.hom.toLinearMap inj inj
    apply hinj
    change Algebra.TensorProduct.map i.hom.hom.toAlgHom i.hom.hom.toAlgHom
      (comul (R := K) (T.act σ x)) = Algebra.TensorProduct.map i.hom.hom.toAlgHom
      i.hom.hom.toAlgHom ((T.tensor T).act σ (comul (R := K) x))
    rw [comul_hom, hi, tensor_intertwine i.hom σ (hi σ) (hi σ), comul_hom]
    exact D.comul_equivariant σ _
  · intro σ x
    change counit (R := K) (T.act σ x) = σ (counit (R := K) x)
    rw [← CoalgHomClass.counit_comp_apply i.hom.hom (T.act σ x), hi,
      ← CoalgHomClass.counit_comp_apply i.hom.hom x]
    exact D.counit_equivariant σ _
  · intro σ x
    apply inj
    change i.hom.hom (antipode K (T.act σ x)) = i.hom.hom (T.act σ (antipode K x))
    rw [antipode_hom, hi, hi, antipode_hom]
    exact D.antipode_equivariant σ _

end Semilinear

section Standard

variable (K) (P : HopfAlgebraCategory k)

private abbrev standardAct : SemilinearAction k K (extendedHopf K P) :=
  SemilinearAction.scalarExtension P

private def standard : HopfDescentDatum k (extendedHopf K P) := by
  let R := standardAct K P
  have hring (σ : Gal(K/k)) (x : extendedHopf K P) :
      R.act σ x = (Algebra.TensorProduct.congr σ (AlgEquiv.refl : P ≃ₐ[k] P)) x := by
    induction x using TensorProduct.inductionOn with
    | tmul r x => rfl
    | add a b ha hb => simp only [map_add, ha, hb]
  refine ⟨R, fun σ => (hring σ 1).trans (map_one _), ?_, ?_, ?_, ?_⟩
  · intro σ x y
    rw [hring, hring σ x, hring σ y, map_mul]
  · intro σ x
    change comul (R := K) (R.act σ x) = (R.tensor R).act σ (comul (R := K) x)
    induction x using TensorProduct.inductionOn with
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul r x =>
      change comul (R := K) (σ r ⊗ₜ[k] x) =
        (R.tensor R).act σ (comul (R := K) (r ⊗ₜ[k] x))
      have hscalar (z : K) : comul (R := K) z = z ⊗ₜ[K] (1 : K) := by
        rw [← Algebra.algebraMap_self_apply (R := K) z, Bialgebra.comul_algebraMap]
        rw [Algebra.TensorProduct.algebraMap_apply]
      rw [TensorProduct.comul_tmul, TensorProduct.comul_tmul, hscalar, hscalar]
      generalize comul (R := k) x = t
      induction t using TensorProduct.inductionOn with
      | tmul a b =>
        simp only [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul,
          SemilinearAction.tensor_act_tmul]
        change (σ r ⊗ₜ[k] a) ⊗ₜ[K] (1 ⊗ₜ[k] b) =
          (σ r ⊗ₜ[k] a) ⊗ₜ[K] (σ 1 ⊗ₜ[k] b)
        rw [map_one]
      | add a b ha hb => simp only [TensorProduct.tmul_add, map_add, ha, hb]
  · intro σ x
    change counit (R := K) (R.act σ x) = σ (counit (R := K) x)
    induction x using TensorProduct.inductionOn with
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul r x =>
      change counit (R := K) (σ r ⊗ₜ[k] x) = σ (counit (R := K) (r ⊗ₜ[k] x))
      simp [TensorProduct.counit_tmul, Algebra.smul_def]
  · intro σ x
    change antipode K (R.act σ x) = R.act σ (antipode K x)
    induction x using TensorProduct.inductionOn with
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul r x =>
      change antipode K (σ r ⊗ₜ[k] x) = R.act σ (antipode K (r ⊗ₜ[k] x))
      rw [TensorProduct.antipode_def, TensorProduct.AlgebraTensorModule.map_tmul,
        TensorProduct.AlgebraTensorModule.map_tmul]
      rfl

end Standard

section Cocycles

private abbrev applyIso (i : A ≅ B) (x : A) : B := i.hom.hom x
private abbrev evalAut (b : Aut A) (x : A) : A := applyIso b.asIso x

private theorem applyIso_left (i : A ≅ B) (x : A) :
    applyIso i.symm (applyIso i x) = x := hom_apply i x

private theorem applyIso_right (i : A ≅ B) (x : B) :
    applyIso i (applyIso i.symm x) = x := inv_apply i x

private theorem iso_ext (i j : A ≅ B) (h : ∀ x, applyIso i x = applyIso j x) : i = j :=
  Iso.ext (CommHopfAlgCat.hom_ext (BialgHom.ext h))

private theorem aut_ext (b c : Aut A) (h : ∀ x, evalAut b x = evalAut c x) : b = c :=
  Aut.ext (iso_ext _ _ h)

private theorem eval_mul (b c : Aut A) (x : A) :
    evalAut (b * c) x = evalAut b (evalAut c x) := rfl

private theorem eval_inv (b : Aut A) (x : A) :
    evalAut b⁻¹ (evalAut b x) = x := hom_apply b.asIso x

private theorem eval_inv' (b : Aut A) (x : A) :
    evalAut b (evalAut b⁻¹ x) = x := inv_apply b.asIso x

private def actionRingEquiv (D : HopfDescentDatum k A) (σ : Gal(K/k)) : A ≃+* A :=
  { D.action.act σ with map_mul' := D.map_mul σ }

/-- The quotient of two semilinear operators over the same field automorphism. -/
private def difference (T R : HopfDescentDatum k A) (σ : Gal(K/k)) : Aut A := by
  let f : A ≃ₐ[K] A :=
    { (actionRingEquiv R σ⁻¹).trans (actionRingEquiv T σ) with
      commutes' := fun r => show T.action.act σ (R.action.act σ⁻¹ (algebraMap K A r)) = _ by
        rw [Algebra.algebraMap_eq_smul_one, R.action.map_smul, R.map_one,
          T.action.map_smul, T.map_one]
        exact congrArg (fun r : K => r • (1 : A)) (AlgEquiv.apply_symm_apply σ r) }
  have hf (x : A) : f x = T.action.act σ (R.action.act σ⁻¹ x) := rfl
  refine Aut.of (CommHopfAlgCat.isoMk (BialgEquiv.ofAlgEquiv f ?_ ?_))
  · apply AlgHom.ext
    intro x
    change counit (R := K) (f x) = counit (R := K) x
    rw [hf, T.counit_equivariant σ, R.counit_equivariant σ⁻¹]
    exact AlgEquiv.apply_symm_apply σ _
  · have h (t : A ⊗[K] A) :
        Algebra.TensorProduct.map f.toAlgHom f.toAlgHom t =
          (T.action.tensor T.action).act σ ((R.action.tensor R.action).act σ⁻¹ t) := by
      induction t using TensorProduct.inductionOn with
      | tmul x y =>
        simp only [Algebra.TensorProduct.map_tmul, SemilinearAction.tensor_act_tmul]
        exact congrArg₂ (fun x y => x ⊗ₜ[K] y) (hf x) (hf y)
      | add x y hx hy => simp only [map_add, hx, hy]
    apply AlgHom.ext
    intro x
    change Algebra.TensorProduct.map f.toAlgHom f.toAlgHom (comul (R := K) x) = comul (R := K) (f x)
    rw [hf, T.comul_equivariant σ, R.comul_equivariant σ⁻¹, h]

private theorem difference_apply (T R : HopfDescentDatum k A) (σ : Gal(K/k)) (x : A) :
    evalAut (difference T R σ) (R.action.act σ x) = T.action.act σ x := by
  change T.action.act σ (R.action.act σ⁻¹ (R.action.act σ x)) = _
  rw [act_inv_apply]

private def conjugate (R : HopfDescentDatum k A) (σ : Gal(K/k)) (b : Aut A) : Aut A :=
  b * difference (transport R b.asIso) R σ

private theorem conjugate_apply (R : HopfDescentDatum k A) (σ : Gal(K/k)) (b : Aut A)
    (x : A) : evalAut (conjugate R σ b) (R.action.act σ x) = R.action.act σ (evalAut b x) := by
  rw [conjugate, eval_mul, difference_apply]
  exact inv_apply b.asIso _

private theorem conjugate_eq (R : HopfDescentDatum k A) (σ : Gal(K/k)) (b : Aut A)
    (x : A) : evalAut (conjugate R σ b) x = R.action.act σ (evalAut b (R.action.act σ⁻¹ x)) := by
  conv_lhs => rw [← act_apply_inv R.action σ x]
  exact conjugate_apply R σ b _

/-- Conjugation by the semilinear datum acts on the coordinate automorphisms. -/
private def coefficientAction (R : HopfDescentDatum k A) : Gal(K/k) →* MulAut (Aut A) where
  toFun σ :=
    { toFun := conjugate R σ
      invFun := conjugate R σ⁻¹
      left_inv := fun b => aut_ext _ _ (fun x => by
        rw [conjugate_eq, inv_inv, conjugate_apply, act_inv_apply])
      right_inv := fun b => aut_ext _ _ (fun x => by
        rw [conjugate_eq, ← act_inv_apply R.action σ x, conjugate_apply, act_apply_inv])
      map_mul' := fun b c => aut_ext _ _ (fun x => by
        obtain ⟨y, rfl⟩ := (R.action.act σ).surjective x
        rw [conjugate_apply, eval_mul, eval_mul, conjugate_apply, conjugate_apply]) }
  map_one' := by
    apply MulEquiv.ext
    intro b
    apply aut_ext
    intro x
    change evalAut (conjugate R 1 b) x = evalAut b x
    rw [conjugate_eq, inv_one, R.action.one_act, R.action.one_act]
  map_mul' σ τ := by
    apply MulEquiv.ext
    intro b
    apply aut_ext
    intro x
    obtain ⟨y, rfl⟩ := (R.action.act (σ * τ)).surjective x
    change evalAut (conjugate R (σ * τ) b) (R.action.act (σ * τ) y) =
      evalAut (conjugate R σ (conjugate R τ b)) (R.action.act (σ * τ) y)
    rw [conjugate_apply, R.action.mul_act, R.action.mul_act σ τ y, conjugate_apply,
      conjugate_apply]

private theorem coefficientAction_apply (R : HopfDescentDatum k A) (σ : Gal(K/k))
    (b : Aut A) (x : A) :
    evalAut (coefficientAction R σ b) (R.action.act σ x) =
      R.action.act σ (evalAut b x) := conjugate_apply R σ b x

private theorem difference_mul (T R : HopfDescentDatum k A) (σ τ : Gal(K/k)) :
    difference T R (σ * τ) =
      difference T R σ * coefficientAction R σ (difference T R τ) := by
  apply aut_ext
  intro x
  obtain ⟨y, rfl⟩ := (R.action.act (σ * τ)).surjective x
  rw [difference_apply, eval_mul, R.action.mul_act, coefficientAction_apply, difference_apply,
    difference_apply, T.action.mul_act]

variable [TopologicalSpace (Aut A)]

private def twist (R : HopfDescentDatum k A) (a : Cocycle (coefficientAction R)) :
    HopfDescentDatum k A := by
  let F (σ : Gal(K/k)) (x : A) := evalAut (a σ) (R.action.act σ x)
  have hmul (σ τ : Gal(K/k)) (x : A) : F (σ * τ) x = F σ (F τ x) := by
    dsimp only [F]
    rw [a.property.2, eval_mul, R.action.mul_act, coefficientAction_apply]
  have hone (x : A) : F 1 x = x := by
    dsimp only [F]
    rw [a.map_one, R.action.one_act]
    rfl
  let T : SemilinearAction k K A :=
    { act := fun σ => (R.action.act σ).trans (CommHopfAlgCat.ofIso (a σ).asIso).toAddEquiv
      one_act := hone
      mul_act := hmul
      map_smul := fun σ r x => show F σ (r • x) = σ r • F σ x by
        dsimp only [F, evalAut, applyIso]
        rw [R.action.map_smul, map_smul] }
  have hT (σ : Gal(K/k)) (x : A) : T.act σ x = F σ x := rfl
  refine ⟨T, ?_, ?_, ?_, ?_, ?_⟩
  · intro σ
    change (a σ).asIso.hom.hom (R.action.act σ 1) = 1
    rw [R.map_one, map_one]
  · intro σ x y
    change (a σ).asIso.hom.hom (R.action.act σ (x * y)) = _
    rw [R.map_mul, map_mul]
    rfl
  · intro σ x
    change comul (R := K) (F σ x) = (T.tensor T).act σ (comul (R := K) x)
    rw [tensor_apply_hom (a σ).asIso.hom T σ (hT σ), ← R.comul_equivariant σ x]
    exact (comul_hom (a σ).asIso.hom (R.action.act σ x)).symm
  · intro σ x
    change counit (R := K) ((a σ).asIso.hom.hom (R.action.act σ x)) = _
    rw [CoalgHomClass.counit_comp_apply]
    exact R.counit_equivariant σ x
  · intro σ x
    change antipode K ((a σ).asIso.hom.hom (R.action.act σ x)) =
      (a σ).asIso.hom.hom (R.action.act σ (antipode K x))
    rw [← antipode_hom, R.antipode_equivariant σ x]

end Cocycles

section Base

open private tensorAlong tensorAlong_tmul tensorAlong_injective
  comparison_counit_base from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AffineGroups

variable (K) (P : HopfAlgebraCategory k)

private abbrev includeBase : P →ₐ[k] K ⊗[k] P :=
  Algebra.TensorProduct.includeRight

private theorem includeBase_injective : Function.Injective (includeBase K P) :=
  Algebra.TensorProduct.includeRight_injective (algebraMap k K).injective

private theorem scalarExtension_repr (σ : Gal(K/k)) (b : Basis ι k P)
    (x : extendedHopf K P) (i : ι) :
    (b.baseChange K).repr ((standardAct K P).act σ x) i =
      σ ((b.baseChange K).repr x i) := by
  induction x using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, Finsupp.add_apply, ha, hb]
  | tmul r x =>
    simp [Basis.baseChange_repr_tmul]

/-- The scalar action fixes exactly the copy of the original coordinate algebra.
The basis argument applies to algebraic Galois extensions of any degree. -/
private theorem standard_fixed [IsGalois k K] (x : extendedHopf K P) :
    (∀ σ, (standardAct K P).act σ x = x) ↔ x ∈ Set.range (includeBase K P) := by
  constructor
  · intro h
    let b := Module.Free.chooseBasis k P
    let f := (b.baseChange K).repr x
    have hi (i : _) : ∃ r : k, algebraMap k K r = f i :=
      (InfiniteGalois.mem_range_algebraMap_iff_fixed (f i)).mpr fun σ => by
        change σ ((b.baseChange K).repr x i) = _
        rw [← scalarExtension_repr K P σ b x i, h σ]
    choose r hr using hi
    refine ⟨∑ i ∈ f.support, r i • b i, ?_⟩
    change (1 : K) ⊗ₜ[k] (∑ i ∈ f.support, r i • b i) = x
    have hx : (∑ i ∈ f.support, f i • b.baseChange K i) = x :=
      (b.baseChange K).linearCombination_repr x
    rw [TensorProduct.tmul_sum, ← hx]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← hr i, TensorProduct.tmul_smul]
    simp [Algebra.smul_def]
  · rintro ⟨y, rfl⟩ σ
    change σ (1 : K) ⊗ₜ[k] y = 1 ⊗ₜ[k] y
    rw [map_one]

private theorem includeBase_tensor_injective :
    Function.Injective (tensorAlong (K := K) (includeBase K P) (includeBase K P)) := by
  apply tensorAlong_injective
  all_goals
    have h : (includeBase K P).toLinearMap.liftBaseChange K = LinearMap.id := by
      apply TensorProduct.AlgebraTensorModule.ext
      intro r x
      change r • ((1 : K) ⊗ₜ[k] x) = r ⊗ₜ[k] x
      simp [TensorProduct.smul_tmul']
    rw [h]
    exact fun _ _ h => h

private theorem comul_base (Q : HopfAlgebraCategory k)
    (f : K ⊗[k] P →ₐ[K] K ⊗[k] Q)
    (g : P →ₐ[k] K ⊗[k] Q) (h : ∀ x, f (1 ⊗ₜ[k] x) = g x) (x : P) :
    Algebra.TensorProduct.map f f (comul (R := K) (1 ⊗ₜ[k] x)) =
      tensorAlong (K := K) g g (comul (R := k) x) := by
  rw [TensorProduct.comul_tmul, Bialgebra.comul_one, Algebra.TensorProduct.one_def]
  generalize comul (R := k) x = t
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    simp only [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul,
      Algebra.TensorProduct.map_tmul, h, tensorAlong_tmul]
  | add a b ha hb => simp only [TensorProduct.tmul_add, map_add, ha, hb]

variable {K} {P Q : HopfAlgebraCategory k}

private theorem extendedHom_ext (f g : extendedHopf K P ⟶ extendedHopf K Q)
    (h : ∀ x : P, f.hom (1 ⊗ₜ[k] x) = g.hom (1 ⊗ₜ[k] x)) : f = g := by
  apply CommHopfAlgCat.hom_ext
  apply BialgHom.ext
  intro t
  have hh : f.hom.toAlgHom = g.hom.toAlgHom :=
    Algebra.TensorProduct.ext_ring (AlgHom.ext h)
  exact DFunLike.congr_fun hh t

private theorem extendedHom_injective :
    Function.Injective (extendedHopfMap K (A := P) (B := Q)) := by
  intro f g h
  apply CommHopfAlgCat.hom_ext
  apply BialgHom.ext
  intro x
  apply includeBase_injective K Q
  exact ConcreteCategory.congr_hom h (1 ⊗ₜ[k] x : K ⊗[k] P)

private theorem extendedHom_comp {U : HopfAlgebraCategory k} (f : P ⟶ Q) (g : Q ⟶ U) :
    extendedHopfMap K (f ≫ g) = extendedHopfMap K f ≫ extendedHopfMap K g := by
  apply extendedHom_ext
  intro x
  rfl

private theorem extendedHom_id :
    extendedHopfMap K (𝟙 P) = 𝟙 (extendedHopf K P) := by
  apply extendedHom_ext
  intro x
  rfl

private theorem baseHom_equivariant (g : P ⟶ Q) :
    (standard K P).Equivariant (standard K Q) (extendedHopfMap K g) :=
  SemilinearAction.scalarExtension_equivariant (K := K) g.hom.toLinearMap

private theorem descend_standard_hom [IsGalois k K]
    (f : extendedHopf K P ⟶ extendedHopf K Q)
    (hf : (standard K P).Equivariant (standard K Q) f) :
    ∃ g : P ⟶ Q, extendedHopfMap K g = f := by
  let F := (includeBase K Q).range
  let e : Q ≃ₐ[k] F := AlgEquiv.ofInjective (includeBase K Q) (includeBase_injective K Q)
  let g₀ : P →ₐ[k] F :=
    ((f.hom.toAlgHom.restrictScalars k).comp (includeBase K P)).codRestrict F (fun x => by
      apply (standard_fixed K Q _).mp
      intro σ
      have h := hf σ (1 ⊗ₜ[k] x)
      change f.hom (σ (1 : K) ⊗ₜ[k] x) =
        (standardAct K Q).act σ (f.hom (1 ⊗ₜ[k] x)) at h
      rw [map_one] at h
      exact h.symm)
  let g : P →ₐ[k] Q := e.symm.toAlgHom.comp g₀
  have hg (x : P) : (1 : K) ⊗ₜ[k] g x = f.hom (1 ⊗ₜ[k] x) :=
    congrArg Subtype.val (e.apply_symm_apply (g₀ x))
  have hε : (Bialgebra.counitAlgHom k Q).comp g = Bialgebra.counitAlgHom k P := by
    apply AlgHom.ext
    intro x
    apply (algebraMap k K).injective
    change algebraMap k K (counit (R := k) (g x)) = algebraMap k K (counit (R := k) x)
    rw [← comparison_counit_base (K := K) (g x), ← comparison_counit_base (K := K) x, hg]
    exact CoalgHomClass.counit_comp_apply f.hom _
  have hΔ : (Algebra.TensorProduct.map g g).comp (Bialgebra.comulAlgHom k P) =
      (Bialgebra.comulAlgHom k Q).comp g := by
    apply AlgHom.ext
    intro x
    apply includeBase_tensor_injective K Q
    change tensorAlong (K := K) (includeBase K Q) (includeBase K Q)
      (Algebra.TensorProduct.map g g (comul (R := k) x)) =
      tensorAlong (K := K) (includeBase K Q) (includeBase K Q) (comul (R := k) (g x))
    have h (t : P ⊗[k] P) :
        tensorAlong (K := K) (includeBase K Q) (includeBase K Q)
          (Algebra.TensorProduct.map g g t) =
        tensorAlong (K := K) ((includeBase K Q).comp g) ((includeBase K Q).comp g) t := by
      induction t using TensorProduct.inductionOn with
      | tmul a b => rw [Algebra.TensorProduct.map_tmul, tensorAlong_tmul, tensorAlong_tmul]; rfl
      | add a b ha hb => simp only [map_add, ha, hb]
    rw [h, ← comul_base K P Q f.hom.toAlgHom ((includeBase K Q).comp g)
      (fun x => (hg x).symm), comul_hom, ← hg,
      ← comul_base K Q Q (AlgHom.id K _) (includeBase K Q) (fun _ => rfl)]
    simp
  let b := CommHopfAlgCat.ofHom (BialgHom.ofAlgHom g hε hΔ)
  refine ⟨b, extendedHom_ext _ _ ?_⟩
  exact hg

private theorem descend_standard_iso [IsGalois k K]
    (f : extendedHopf K P ≅ extendedHopf K Q)
    (hf : (standard K P).Equivariant (standard K Q) f.hom) :
    ∃ i : P ≅ Q, extendedHopfMap K i.hom = f.hom := by
  have hf' : (standard K Q).Equivariant (standard K P) f.inv := by
    intro σ x
    change f.inv.hom ((standardAct K Q).act σ x) = (standardAct K P).act σ (f.inv.hom x)
    have h := hf σ (f.inv.hom x)
    change f.hom.hom ((standardAct K P).act σ (f.inv.hom x)) =
      (standardAct K Q).act σ (f.hom.hom (f.inv.hom x)) at h
    rw [inv_apply] at h
    rw [← h, hom_apply]
  obtain ⟨i, hi⟩ := descend_standard_hom f.hom hf
  obtain ⟨j, hj⟩ := descend_standard_hom f.inv hf'
  refine ⟨⟨i, j, ?_, ?_⟩, hi⟩
  · apply extendedHom_injective (K := K)
    rw [extendedHom_comp, extendedHom_id, hi, hj, f.hom_inv_id]
  · apply extendedHom_injective (K := K)
    rw [extendedHom_comp, extendedHom_id, hi, hj, f.inv_hom_id]

end Base

section Classification

variable {P Q U : HopfAlgebraCategory k}

private abbrev formAction (K : Type u) [Field K] [Algebra k K] (P : HopfAlgebraCategory k) :=
  coefficientAction (standard K P)

private abbrev transported (i : extendedHopf K P ≅ extendedHopf K Q) :=
  transport (standard K Q) i

private theorem transported_apply (i : extendedHopf K P ≅ extendedHopf K Q)
    (σ : Gal(K/k)) (x : extendedHopf K P) :
    (transported i).action.act σ x =
      applyIso i.symm ((standardAct K Q).act σ (applyIso i x)) := rfl

private abbrev transportedDifference (i : extendedHopf K P ≅ extendedHopf K Q)
    (σ : Gal(K/k)) : Coefficients K P :=
  difference (transported i) (standard K P) σ

private def transportedCocycle (i : extendedHopf K P ≅ extendedHopf K Q)
    (h : Continuous (transportedDifference i)) : Cocycle (formAction K P) :=
  ⟨transportedDifference i, h, difference_mul _ _⟩

private theorem transportedCocycle_spec (i : extendedHopf K P ≅ extendedHopf K Q)
    (h : Continuous (transportedDifference i)) :
    IsTransportedCocycle i (transportedCocycle i h) :=
  difference_apply _ _

private theorem changesBy_iff_intertwine
    {i : extendedHopf K P ≅ extendedHopf K Q} {j : extendedHopf K P ≅ extendedHopf K U}
    {a a' : Cocycle (formAction K P)} (ha : IsTransportedCocycle i a)
    (ha' : IsTransportedCocycle j a') (b : Coefficients K P) :
    ChangesBy a a' b ↔ ∀ σ x, (transported i).action.act σ (evalAut b x) =
      evalAut b ((transported j).action.act σ x) := by
  have ht (σ : Gal(K/k)) (x : extendedHopf K P) :
      (transported i).action.act σ x = evalAut (a σ) ((standardAct K P).act σ x) :=
    (ha σ x).symm
  have ht' (σ : Gal(K/k)) (x : extendedHopf K P) :
      (transported j).action.act σ x = evalAut (a' σ) ((standardAct K P).act σ x) :=
    (ha' σ x).symm
  have hc (σ : Gal(K/k)) (x : extendedHopf K P) :
      evalAut (formAction K P σ b) ((standardAct K P).act σ x) =
        (standardAct K P).act σ (evalAut b x) := coefficientAction_apply (standard K P) σ b x
  constructor
  · intro h σ x
    rw [ht, ht', h σ, eval_mul, eval_mul, eval_inv', hc]
  · intro h σ
    apply aut_ext
    intro x
    obtain ⟨y, rfl⟩ := ((standardAct K P).act σ).surjective x
    rw [eval_mul, eval_mul, hc, ← ht, h σ, eval_inv, ht']

private def extendedIso (K : Type u) [Field K] [Algebra k K] (i : Q ≅ U) :
    extendedHopf K Q ≅ extendedHopf K U where
  hom := extendedHopfMap K i.hom
  inv := extendedHopfMap K i.inv
  hom_inv_id := by rw [← extendedHom_comp, i.hom_inv_id, extendedHom_id]
  inv_hom_id := by rw [← extendedHom_comp, i.inv_hom_id, extendedHom_id]

/-- Cohomology identifies exactly the forms isomorphic over the base field. -/
private theorem class_eq_iff_iso [IsGalois k K]
    {i : extendedHopf K P ≅ extendedHopf K Q} {j : extendedHopf K P ≅ extendedHopf K U}
    {a a' : Cocycle (formAction K P)} (ha : IsTransportedCocycle i a)
    (ha' : IsTransportedCocycle j a') : classOf a = classOf a' ↔ Nonempty (Q ≅ U) := by
  rw [classOf_eq_iff]
  constructor
  · rintro ⟨b, hb⟩
    let f := i.symm.trans (b.asIso.symm.trans j)
    have h := (changesBy_iff_intertwine ha ha' b).mp hb
    have hf : (standard K Q).Equivariant (standard K U) f.hom := by
      intro σ x
      obtain ⟨y, rfl⟩ := (CommHopfAlgCat.ofIso (b.asIso.trans i)).surjective x
      change applyIso j (evalAut b⁻¹ (applyIso i.symm
        ((standardAct K Q).act σ (applyIso i (evalAut b y))))) =
        (standardAct K U).act σ
          (applyIso j (evalAut b⁻¹ (applyIso i.symm (applyIso i (evalAut b y)))))
      change applyIso j (evalAut b⁻¹ ((transported i).action.act σ (evalAut b y))) = _
      rw [h σ y, eval_inv, applyIso_left, eval_inv, transported_apply, applyIso_right]
    obtain ⟨g, _⟩ := descend_standard_iso f hf
    exact ⟨g⟩
  · rintro ⟨g⟩
    let f := extendedIso K g
    let b : Coefficients K P := Aut.of (j.trans (f.symm.trans i.symm))
    refine ⟨b, (changesBy_iff_intertwine ha ha' b).mpr ?_⟩
    intro σ x
    have hf := baseHom_equivariant (K := K) g.inv σ (applyIso j x)
    change applyIso f.symm ((standardAct K U).act σ (applyIso j x)) =
      (standardAct K Q).act σ (applyIso f.symm (applyIso j x)) at hf
    change applyIso i.symm ((standardAct K Q).act σ
      (applyIso i (applyIso i.symm (applyIso f.symm (applyIso j x))))) =
      applyIso i.symm (applyIso f.symm (applyIso j (applyIso j.symm
        ((standardAct K U).act σ (applyIso j x)))))
    rw [applyIso_right, applyIso_right, hf]

private theorem classify [IsGalois k K] (P : HopfAlgebraCategory k)
    (hP : Algebra.FiniteType k P)
    (hact : Continuous (fun p : Gal(K/k) × Coefficients K P => formAction K P p.1 p.2))
    (hcontinuous : ∀ (Q : Models K P) (i : extendedHopf K P ≅ extendedHopf K Q.val),
      Continuous (transportedDifference i))
    (hrealize : ∀ a : Cocycle (formAction K P),
      ∃ (Q : Models K P) (i : extendedHopf K P ≅ extendedHopf K Q.val),
        IsTransportedCocycle i a) :
    Classifies K P hP := by
  let chooseIso (Q : Models K P) : extendedHopf K P ≅ extendedHopf K Q.val :=
    Classical.choice Q.property.2
  let cocycle (Q : Models K P) :=
    transportedCocycle (chooseIso Q) (hcontinuous Q (chooseIso Q))
  have hcocycle (Q : Models K P) := transportedCocycle_spec (chooseIso Q) (hcontinuous Q (chooseIso Q))
  let f : FormClasses K P → H1 (formAction K P) :=
    Quotient.lift (fun Q => classOf (cocycle Q)) (fun Q U h =>
      (class_eq_iff_iso (hcocycle Q) (hcocycle U)).mpr h)
  have hf (Q : Models K P) (i : extendedHopf K P ≅ extendedHopf K Q.val)
      {a : Cocycle (formAction K P)} (ha : IsTransportedCocycle i a) :
      f (Quotient.mk _ Q) = classOf a :=
    (class_eq_iff_iso (hcocycle Q) ha).mpr ⟨Iso.refl _⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro x y
      refine Quotient.inductionOn₂ x y (fun Q U h => Quotient.sound ?_)
      exact (class_eq_iff_iso (hcocycle Q) (hcocycle U)).mp h
    · intro a
      refine Quotient.inductionOn a (fun a => ?_)
      obtain ⟨Q, i, hi⟩ := hrealize a
      exact ⟨Quotient.mk _ Q, hf Q i hi⟩
  refine ⟨formAction K P, Equiv.ofBijective f hbij, coefficientAction_apply _, hact,
    hf (standardModel P hP) (Iso.refl _) (a := trivial _) (fun _ _ => rfl), ?_, hrealize⟩
  intro Q i
  let a := transportedCocycle i (hcontinuous Q i)
  have ha : IsTransportedCocycle i a := transportedCocycle_spec i (hcontinuous Q i)
  exact ⟨a, ha, hf Q i ha⟩

open private comparison_equivariant from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AffineGroups

private theorem finite_realization [FiniteDimensional k K] [IsGalois k K]
    (P : HopfAlgebraCategory k) (hP : Algebra.FiniteType k P)
    (a : Cocycle (formAction K P)) :
    ∃ (Q : Models K P) (i : extendedHopf K P ≅ extendedHopf K Q.val),
      IsTransportedCocycle i a := by
  let D := twist (standard K P) a
  let H := descendHopf D
  let Q : Models K P := ⟨H.algebra, (affineDescentProperties H).1 (by
    let := hP
    change Algebra.FiniteType K (K ⊗[k] P)
    infer_instance), ⟨H.iso.symm⟩⟩
  refine ⟨Q, H.iso.symm, fun σ x => ?_⟩
  have h := comparison_equivariant H σ (H.iso.inv.hom x)
  change H.iso.hom.hom ((standardAct K H.algebra).act σ (H.iso.inv.hom x)) =
    D.action.act σ (H.iso.hom.hom (H.iso.inv.hom x)) at h
  rw [inv_apply] at h
  exact h.symm

/-- Classification of finite Galois forms by pointed nonabelian cohomology. -/
theorem finiteForms : Specification.Finite.{u} := by
  intro k K _ _ _ _ _ P hP
  exact classify P hP continuous_of_discreteTopology
    (fun _ _ => continuous_of_discreteTopology) (finite_realization P hP)

end Classification

section FiniteLevels

variable {S : Type u} [Field S] [Algebra k S] [IsGalois k S]
variable {P Q U : HopfAlgebraCategory k}
variable (L : FiniteGaloisIntermediateField k S)

private abbrev inLevel (P : HopfAlgebraCategory k) (x : extendedHopf L P) :
    extendedHopf S P :=
  applyIso (scalarTowerIso P) ((1 : S) ⊗ₜ[L] x)

omit [IsGalois k S] in
private theorem inLevel_tmul (l : L) (x : P) :
    inLevel L P (l ⊗ₜ[k] x) = (algebraMap L S l) ⊗ₜ[k] x := by
  change (l • (1 : S)) ⊗ₜ[k] x = _
  rw [Algebra.smul_def, mul_one]

omit [IsGalois k S] in
private theorem inLevel_injective : Function.Injective (inLevel L P) :=
  (CommHopfAlgCat.ofIso (scalarTowerIso P)).injective.comp (includeBase_injective S _)

omit [IsGalois k S] in
private theorem raiseIso_inLevel (i : extendedHopf L P ≅ extendedHopf L Q)
    (x : extendedHopf L P) : applyIso (raiseIso i) (inLevel L P x) =
      inLevel L Q (applyIso i x) := by
  change applyIso (scalarTowerIso Q) ((extendedHopfMap S i.hom).hom
    (applyIso (scalarTowerIso P).symm (applyIso (scalarTowerIso P) ((1 : S) ⊗ₜ[L] x)))) = _
  rw [applyIso_left]
  rfl

omit [IsGalois k S] in
private theorem raiseIso_injective :
    Function.Injective (raiseIso (S := S) (P := P) (Q := Q) (L := L)) := by
  intro i j h
  apply iso_ext
  intro x
  apply inLevel_injective L
  rw [← raiseIso_inLevel, ← raiseIso_inLevel, h]

omit [IsGalois k S] in
private theorem raiseIso_ext (f g : extendedHopf S P ≅ extendedHopf S Q)
    (h : ∀ x : P, applyIso f (inLevel L P (1 ⊗ₜ[k] x)) =
      applyIso g (inLevel L P (1 ⊗ₜ[k] x))) : f = g := by
  apply Iso.ext
  apply extendedHom_ext
  intro x
  simpa only [inLevel_tmul, map_one] using h x

omit [IsGalois k S] in
private theorem raiseIso_symm (i : extendedHopf L P ≅ extendedHopf L Q) :
    raiseIso (S := S) i.symm = (raiseIso i).symm := by
  apply raiseIso_ext L
  intro x
  have h := raiseIso_inLevel L i (applyIso i.symm (1 ⊗ₜ[k] x))
  rw [applyIso_right] at h
  rw [raiseIso_inLevel, ← h, applyIso_left]

omit [IsGalois k S] in
private theorem raiseIso_action (σ : Gal(S/k)) (x : extendedHopf L P) :
    (standardAct S P).act σ (inLevel L P x) =
      inLevel L P ((standardAct L P).act (restriction L σ) x) := by
  induction x using TensorProduct.inductionOn with
  | add a b ha hb =>
    simp only [inLevel, applyIso, TensorProduct.tmul_add, map_add] at ha hb ⊢
    rw [ha, hb]
  | tmul l x =>
    rw [inLevel_tmul]
    change σ (algebraMap L S l) ⊗ₜ[k] x =
      inLevel L P (((restriction L σ) l) ⊗ₜ[k] x)
    rw [inLevel_tmul]
    exact congrArg (fun r : S => r ⊗ₜ[k] x) (AlgEquiv.restrictNormal_commutes σ L l).symm

omit [IsGalois k S] in
private theorem scalarTower_restrict_action (σ : Gal(S/L))
    (x : extendedHopf S (extendedHopf L P)) :
    applyIso (scalarTowerIso P) ((standardAct S (extendedHopf L P)).act σ x) =
      (standardAct S P).act (σ.restrictScalars k) (applyIso (scalarTowerIso P) x) := by
  induction x using TensorProduct.inductionOn with
  | add a b ha hb => simp only [applyIso, map_add] at ha hb ⊢; rw [ha, hb]
  | tmul s x =>
    induction x using TensorProduct.inductionOn with
    | add a b ha hb => simp only [TensorProduct.tmul_add, applyIso, map_add] at ha hb ⊢; rw [ha, hb]
    | tmul l x =>
      change (l • σ s) ⊗ₜ[k] x = σ (l • s) ⊗ₜ[k] x
      rw [map_smul]

private theorem equivariant_at_level_imp_descends
    (i : extendedHopf S P ≅ extendedHopf S Q)
    (hi : ∀ σ ∈ (restriction L).ker, ∀ x : extendedHopf S P,
      applyIso i ((standardAct S P).act σ x) = (standardAct S Q).act σ (applyIso i x)) :
    ∃ j : extendedHopf L P ≅ extendedHopf L Q, raiseIso j = i := by
  let tP : extendedHopf S (extendedHopf L P) ≅ extendedHopf S P := scalarTowerIso P
  let tQ : extendedHopf S (extendedHopf L Q) ≅ extendedHopf S Q := scalarTowerIso Q
  let f := tP.trans (i.trans tQ.symm)
  have hf : (standard S (extendedHopf L P)).Equivariant (standard S (extendedHopf L Q)) f.hom := by
    intro σ x
    have hn : σ.restrictScalars k ∈ (restriction L).ker := by
      rw [L.toIntermediateField.restrictNormalHom_ker]
      exact (L.toIntermediateField.fixingSubgroupEquiv.symm σ).property
    apply (CommHopfAlgCat.ofIso tQ).injective
    change applyIso tQ (applyIso tQ.symm (applyIso i (applyIso tP
      ((standardAct S (extendedHopf L P)).act σ x)))) =
        applyIso tQ ((standardAct S (extendedHopf L Q)).act σ
          (applyIso tQ.symm (applyIso i (applyIso tP x))))
    rw [applyIso_right, scalarTower_restrict_action, scalarTower_restrict_action, applyIso_right]
    exact hi _ hn _
  have : IsGalois L S := IsGalois.tower_top_intermediateField L.toIntermediateField
  obtain ⟨j, hj⟩ := descend_standard_iso f hf
  refine ⟨j, ?_⟩
  apply Iso.ext
  change tP.inv ≫ (extendedHopfMap S j.hom ≫ tQ.hom) = i.hom
  rw [hj]
  simp [f]

end FiniteLevels

section LevelExistence

variable {S : Type u} [Field S] [Algebra k S] [IsGalois k S]
variable {P Q : HopfAlgebraCategory k}

omit [IsGalois k S] in
private theorem restrictionKernel_mono {L M : FiniteGaloisIntermediateField k S} (h : L ≤ M) :
    (restriction M).ker ≤ (restriction L).ker := by
  rw [M.toIntermediateField.restrictNormalHom_ker, L.toIntermediateField.restrictNormalHom_ker]
  exact IntermediateField.fixingSubgroup_le ((FiniteGaloisIntermediateField.le_iff _ _).mp h)

private theorem element_defined_at_level (x : extendedHopf S P) :
    ∃ L : FiniteGaloisIntermediateField k S,
      ∀ σ ∈ (restriction L).ker, (standardAct S P).act σ x = x := by
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
    let L := FiniteGaloisIntermediateField.adjoin k ({r} : Set S)
    refine ⟨L, fun σ hσ => ?_⟩
    have hr : r ∈ L.toIntermediateField :=
      FiniteGaloisIntermediateField.subset_adjoin _ _ (Set.mem_singleton _)
    have hσ' := (L.toIntermediateField.restrictNormalHom_ker ▸ hσ)
    change σ r ⊗ₜ[k] x = r ⊗ₜ[k] x
    rw [(IntermediateField.mem_fixingSubgroup_iff L.toIntermediateField σ).mp hσ' r hr]
  | add a b ha hb =>
    obtain ⟨L, hL⟩ := ha
    obtain ⟨M, hM⟩ := hb
    refine ⟨L ⊔ M, fun σ hσ => ?_⟩
    rw [map_add, hL σ (restrictionKernel_mono le_sup_left hσ),
      hM σ (restrictionKernel_mono le_sup_right hσ)]

private theorem elements_defined_at_level {ι : Type*} (s : Finset ι)
    (f : ι → extendedHopf S P) :
    ∃ L : FiniteGaloisIntermediateField k S,
      ∀ σ ∈ (restriction L).ker, ∀ x ∈ s, (standardAct S P).act σ (f x) = f x := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨⊥, by simp⟩
  | @insert x s hx ih =>
    obtain ⟨L, hL⟩ := element_defined_at_level (f x)
    obtain ⟨M, hM⟩ := ih
    refine ⟨L ⊔ M, fun σ hσ y hy => ?_⟩
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact hL σ (restrictionKernel_mono le_sup_left hσ)
    · exact hM σ (restrictionKernel_mono le_sup_right hσ) y hy

omit [IsGalois k S] in
private theorem standard_acts_on_one_tmul (P : HopfAlgebraCategory k) (σ : Gal(S/k)) (x : P) :
    (standardAct S P).act σ (1 ⊗ₜ[k] x) = 1 ⊗ₜ[k] x := by
  change σ 1 ⊗ₜ[k] x = 1 ⊗ₜ[k] x
  rw [map_one]

private theorem iso_equivariant_at_some_level (hP : Algebra.FiniteType k P)
    (i : extendedHopf S P ≅ extendedHopf S Q) (L₀ : FiniteGaloisIntermediateField k S) :
    ∃ L : FiniteGaloisIntermediateField k S, L₀ ≤ L ∧
      ∀ σ ∈ (restriction L).ker, ∀ x : extendedHopf S P,
        applyIso i ((standardAct S P).act σ x) = (standardAct S Q).act σ (applyIso i x) := by
  let := hP
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := k) (A := P)
  obtain ⟨L, hL⟩ := elements_defined_at_level s (fun x => applyIso i (1 ⊗ₜ[k] x))
  refine ⟨L₀ ⊔ L, le_sup_left, fun σ hσ x => ?_⟩
  let b := transportedDifference i σ
  have hb₀ (y : P) (hy : y ∈ s) : evalAut b (1 ⊗ₜ[k] y) = 1 ⊗ₜ[k] y := by
    have h := difference_apply (transported i) (standard S P) σ (1 ⊗ₜ[k] y)
    change evalAut b ((standardAct S P).act σ (1 ⊗ₜ[k] y)) = (transported i).action.act σ (1 ⊗ₜ[k] y) at h
    rw [standard_acts_on_one_tmul, transported_apply, hL σ (restrictionKernel_mono le_sup_right hσ) y hy,
      applyIso_left] at h
    exact h
  have hb₁ : (b.asIso.hom.hom.toAlgHom.restrictScalars k).comp (includeBase S P) =
      includeBase S P := by
    apply AlgHom.ext_of_adjoin_eq_top hs
    intro y hy
    exact hb₀ y hy
  have hb : b = 1 := by
    apply Aut.ext
    apply Iso.ext
    apply extendedHom_ext
    intro y
    exact DFunLike.congr_fun hb₁ y
  have h := difference_apply (transported i) (standard S P) σ x
  change evalAut b ((standardAct S P).act σ x) = (transported i).action.act σ x at h
  rw [hb, transported_apply] at h
  change (standardAct S P).act σ x = _ at h
  rw [h, applyIso_right]

/-- A trivialization and its inverse descend together over a finite Galois field. -/
theorem finiteLevelIsomorphisms : Specification.FiniteLevelIsomorphisms.{u} := by
  intro k S _ _ _ _ P Q hP _ L₀ i
  obtain ⟨L, hle, h⟩ := iso_equivariant_at_some_level hP i L₀
  obtain ⟨j, hj⟩ := equivariant_at_level_imp_descends L i h
  exact ⟨L, j, hle, hj⟩

end LevelExistence

section InfiniteClassification

variable {S : Type u} [Field S] [Algebra k S] [IsGalois k S]
variable {P Q : HopfAlgebraCategory k}
variable (L : FiniteGaloisIntermediateField k S)

private def raiseAut : Coefficients L P →* Coefficients S P where
  toFun b := Aut.of (raiseIso b.asIso)
  map_one' := by
    apply Aut.ext
    apply raiseIso_ext L
    intro x
    exact raiseIso_inLevel L (Iso.refl _) _
  map_mul' b c := by
    apply Aut.ext
    apply raiseIso_ext L
    intro x
    change applyIso (raiseIso (c.asIso.trans b.asIso)) (inLevel L P (1 ⊗ₜ[k] x)) =
      applyIso (raiseIso b.asIso) (applyIso (raiseIso c.asIso) (inLevel L P (1 ⊗ₜ[k] x)))
    rw [raiseIso_inLevel, raiseIso_inLevel, raiseIso_inLevel]
    rfl

private theorem raiseAut_inLevel (b : Coefficients L P) (x : extendedHopf L P) :
    evalAut (raiseAut L b) (inLevel L P x) = inLevel L P (evalAut b x) :=
  raiseIso_inLevel L b.asIso x

omit [IsGalois k S] in
private theorem raiseAut_injective :
    Function.Injective (raiseAut (P := P) L) := by
  intro b c h
  apply Aut.ext
  exact raiseIso_injective L (congrArg Aut.asIso h)

omit [IsGalois k S] in
private theorem formAction_apply (T : Type u) [Field T] [Algebra k T] (P : HopfAlgebraCategory k)
    (σ : Gal(T/k)) (b : Coefficients T P) (x : extendedHopf T P) :
    evalAut (formAction T P σ b) ((standardAct T P).act σ x) =
      (standardAct T P).act σ (evalAut b x) :=
  coefficientAction_apply (standard T P) σ b x

private theorem raiseAut_action (σ : Gal(S/k)) (b : Coefficients L P) :
    raiseAut L (formAction L P (restriction L σ) b) = formAction S P σ (raiseAut L b) := by
  apply Aut.ext
  apply raiseIso_ext L
  intro x
  change evalAut (raiseAut L (formAction L P (restriction L σ) b)) (inLevel L P (1 ⊗ₜ[k] x)) =
    evalAut (formAction S P σ (raiseAut L b)) (inLevel L P (1 ⊗ₜ[k] x))
  have hS : (standardAct S P).act σ (inLevel L P (1 ⊗ₜ[k] x)) =
      inLevel L P (1 ⊗ₜ[k] x) := by rw [raiseIso_action, standard_acts_on_one_tmul]
  conv_rhs => rw [← hS, formAction_apply, raiseAut_inLevel, raiseIso_action]
  rw [raiseAut_inLevel]
  congr 1
  conv_lhs => rw [← standard_acts_on_one_tmul P (restriction L σ) x, formAction_apply]

/-- The coefficients fixed by a restriction kernel are the automorphisms
defined over its finite Galois field. -/
private theorem inLevelCoefficients_iff (b : Coefficients S P) :
    b ∈ LevelCoefficients (formAction S P) L ↔ b ∈ Set.range (raiseAut L) := by
  constructor
  · intro h
    have hb : ∀ σ ∈ (restriction L).ker, ∀ x : extendedHopf S P,
        applyIso b.asIso ((standardAct S P).act σ x) = (standardAct S P).act σ (applyIso b.asIso x) := by
      intro σ hσ x
      have he : formAction S P σ b = b := h σ hσ
      have hc := formAction_apply S P σ b x
      rwa [he] at hc
    obtain ⟨j, hj⟩ := equivariant_at_level_imp_descends L b.asIso hb
    exact ⟨Aut.of j, Aut.ext hj⟩
  · rintro ⟨c, rfl⟩ σ hσ
    change formAction S P σ (raiseAut L c) = raiseAut L c
    rw [← raiseAut_action, MonoidHom.mem_ker.mp hσ, map_one]
    rfl

private def levelAutEquiv :
    Coefficients L P ≃* LevelCoefficients (formAction S P) L :=
  MulEquiv.ofBijective ((raiseAut L).codRestrict _ (fun b =>
    (inLevelCoefficients_iff L (raiseAut L b)).mpr ⟨b, rfl⟩)) ⟨
      fun _ _ h => raiseAut_injective L (congrArg Subtype.val h),
      fun b => by
        obtain ⟨a, ha⟩ := (inLevelCoefficients_iff L b.val).mp b.property
        exact ⟨a, Subtype.ext ha⟩⟩

private theorem levelAutEquiv_action (δ : Gal(L/k)) (b : Coefficients L P) :
    levelAutEquiv L (formAction L P δ b) =
      levelAction (formAction S P) L δ (levelAutEquiv L b) := by
  obtain ⟨σ, rfl⟩ := (AlgEquiv.restrictNormalHom_surjective S
    (F := k) (K₁ := L)) δ
  apply Subtype.ext
  rw [quotientAction_apply]
  exact raiseAut_action L σ b

private theorem transportedDifference_raise (i : extendedHopf L P ≅ extendedHopf L Q)
    (σ : Gal(S/k)) :
    transportedDifference (raiseIso i) σ =
      raiseAut L (transportedDifference i (restriction L σ)) := by
  apply Aut.ext
  apply raiseIso_ext L
  intro x
  let y := (1 : L) ⊗ₜ[k] x
  have hS : (standardAct S P).act σ (inLevel L P y) = inLevel L P y := by
    rw [raiseIso_action, standard_acts_on_one_tmul]
  have hL : (standardAct L P).act (restriction L σ) y = y :=
    standard_acts_on_one_tmul P _ _
  have big := difference_apply (transported (raiseIso (S := S) i)) (standard S P) σ (inLevel L P y)
  have small := difference_apply (transported i) (standard L P) (restriction L σ) y
  change evalAut (transportedDifference (raiseIso i) σ) (inLevel L P y) =
    evalAut (raiseAut L (transportedDifference i (restriction L σ))) (inLevel L P y)
  change evalAut (transportedDifference (raiseIso i) σ)
    ((standardAct S P).act σ (inLevel L P y)) = (transported (raiseIso i)).action.act σ
      (inLevel L P y) at big
  rw [hS, transported_apply, raiseIso_inLevel, raiseIso_action,
    ← raiseIso_symm L, raiseIso_inLevel] at big
  change evalAut (transportedDifference i (restriction L σ))
    ((standardAct L P).act (restriction L σ) y) = (transported i).action.act (restriction L σ) y
    at small
  rw [hL, transported_apply] at small
  rw [big, raiseAut_inLevel, small]

private theorem transportedDifference_continuous (hP : Algebra.FiniteType k P)
    (hQ : Algebra.FiniteType k Q) (i : extendedHopf S P ≅ extendedHopf S Q) :
    Continuous (transportedDifference i) := by
  obtain ⟨L, j, _, rfl⟩ := finiteLevelIsomorphisms P Q hP hQ ⊥ i
  have h : transportedDifference (raiseIso (S := S) j) =
      (fun δ => raiseAut L (transportedDifference j δ)) ∘ restriction L := by
    funext σ
    exact transportedDifference_raise L j σ
  rw [h]
  exact continuous_of_discreteTopology.comp
    (InfiniteGalois.restrictNormalHom_continuous L.toIntermediateField)

private theorem infinite_realization (hP : Algebra.FiniteType k P)
    (a : Cocycle (formAction S P)) :
    ∃ (B : Models S P) (i : extendedHopf S P ≅ extendedHopf S B.val),
      IsTransportedCocycle i a := by
  obtain ⟨L, c, _, hc⟩ := finiteLevel (ρ := formAction S P) ⊥ a
  let e := levelAutEquiv (P := P) L
  let d : Cocycle (formAction L P) := ⟨fun δ => e.symm (c δ),
    continuous_of_discreteTopology, fun δ ε => by
      apply e.injective
      change e (e.symm (c (δ * ε))) = e (e.symm (c δ) * formAction L P δ (e.symm (c ε)))
      rw [map_mul, e.apply_symm_apply, e.apply_symm_apply, levelAutEquiv_action,
        e.apply_symm_apply]
      exact c.property.2 δ ε⟩
  obtain ⟨B, i, hi⟩ := finite_realization P hP d
  let BS : Models S P := ⟨B.val, B.property.1, ⟨raiseIso i⟩⟩
  refine ⟨BS, raiseIso i, fun σ x => ?_⟩
  have h₁ : transportedDifference i (restriction L σ) = d (restriction L σ) := by
    apply aut_ext
    intro y
    obtain ⟨z, rfl⟩ := ((standardAct L P).act (restriction L σ)).surjective y
    exact (difference_apply _ _ _ _).trans (hi _ _).symm
  have h₂ : raiseAut L (d (restriction L σ)) = a σ :=
    (congrArg Subtype.val (e.apply_symm_apply (c (restriction L σ)))).trans (hc σ)
  have h := difference_apply (transported (raiseIso (S := S) i)) (standard S P) σ x
  change evalAut (transportedDifference (raiseIso i) σ) ((standardAct S P).act σ x) = _ at h
  rwa [transportedDifference_raise L, h₁, h₂] at h

/-- Classification over the separable closure, with Krull and discrete topologies. -/
theorem separableClosureForms : Specification.SeparableClosure.{u} := by
  intro k S _ _ _ _ P hP
  refine classify P hP ((continuousAction_iff_finiteLevel (ρ := formAction S P)).mpr ?_)
    (fun B i => transportedDifference_continuous hP B.property.1 i) (infinite_realization hP)
  intro b
  obtain ⟨L, j, _, hj⟩ := finiteLevelIsomorphisms P P hP hP ⊥ b.asIso
  exact ⟨L, (inLevelCoefficients_iff L b).mpr ⟨Aut.of j, Aut.ext hj⟩⟩

end InfiniteClassification

section GroupSchemes

open private extendedGroupIso extendedSpecIso_hom_fst from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups

private def spectrumIsoEquiv (P Q : HopfAlgebraCategory k) :
    (P ≅ Q) ≃ (specGroup P ≅ specGroup Q) :=
  (show (P ≅ Q) ≃ (Opposite.op P ≅ Opposite.op Q) from
    ⟨fun i => i.symm.op, fun i => i.unop.symm,
      fun _ => by simp, fun _ => by apply Iso.ext; rfl⟩).trans
    ((hopfSpec.fullyFaithful (R := CommRingCat.of k)).isoEquiv)

private theorem spectrumIso_trans {P Q U : HopfAlgebraCategory k}
    (i : P ≅ Q) (j : Q ≅ U) :
    spectrumIso (i.trans j) = (spectrumIso i).trans (spectrumIso j) := by
  simp only [spectrumIso, Iso.trans_symm, Iso.op_trans, Functor.mapIso_trans]

private def spectrumAutEquiv (P : HopfAlgebraCategory k) : Aut P ≃* Aut (specGroup P) where
  toEquiv := (Aut.isoEquiv : Aut P ≃ (P ≅ P)).trans
    ((spectrumIsoEquiv P P).trans
      (Aut.isoEquiv : Aut (specGroup P) ≃ (specGroup P ≅ specGroup P)).symm)
  map_mul' b c := by
    apply Aut.ext
    exact spectrumIso_trans c.asIso b.asIso

private theorem exists_coordinate_model (G : Specs.AffineAlgebraicGroup k) :
    ∃ (P : HopfAlgebraCategory k) (_hP : Algebra.FiniteType k P), Nonempty (specGroup P ≅ G.val) := by
  let := finiteTypeHopfSpecEquivalence k
  let F := finiteTypeHopfSpec k
  let P := F.objPreimage G
  let i := (inducedFunctor (Subtype.val : Specs.AffineAlgebraicGroup k → Specs.GroupScheme k)).mapIso
    (F.objObjPreimageIso G)
  exact ⟨P.unop.val, P.unop.property, ⟨i⟩⟩

/-- The coordinate classification identifies group-scheme classes and the actual
automorphism group of the scalar extension by inverse pullback. -/
theorem schemeComparison : Specification.SchemeComparison.{u} := by
  intro k K _ _ _ G
  obtain ⟨P, hP, ⟨j⟩⟩ := exists_coordinate_model G
  let t := extendedGroupIso (k := k) K
  let b := (t P).trans ((groupBaseChange k K).mapIso j)
  let m := realizeSchemeModel K j t
  let f : FormClasses K P → SchemeFormClasses K G :=
    Quotient.lift (fun B => Quotient.mk _ (m B)) (fun _ _ ⟨i⟩ =>
      Quotient.sound ⟨spectrumIso i⟩)
  have hf : Function.Bijective f := by
    constructor
    · intro x y
      refine Quotient.inductionOn₂ x y (fun B C h => ?_)
      obtain ⟨i⟩ : Nonempty (specGroup B.val ≅ specGroup C.val) := Quotient.exact h
      exact Quotient.sound ⟨(spectrumIsoEquiv B.val C.val).symm i⟩
    · intro H
      refine Quotient.inductionOn H (fun H => ?_)
      obtain ⟨Q, hQ, ⟨u⟩⟩ := exists_coordinate_model H.val
      obtain ⟨v⟩ := H.property
      let w := b.trans (v.trans (((t Q).trans ((groupBaseChange k K).mapIso u)).symm))
      let B : Models K P := ⟨Q, hQ, ⟨(spectrumIsoEquiv (extendedHopf K P)
        (extendedHopf K Q)).symm w⟩⟩
      exact ⟨Quotient.mk _ B, Quotient.sound ⟨u⟩⟩
  let c := (spectrumAutEquiv (extendedHopf K P)).trans b.conjAut
  refine ⟨P, hP, j, t, Equiv.ofBijective f hf, c, extendedSpecIso_hom_fst K,
    Quotient.sound ⟨j⟩, fun _ => rfl, ?_, ?_⟩
  · intro a
    exact b.conjAut_apply (spectrumAutEquiv _ a)
  · intro B
    exact (((spectrumIsoEquiv _ _).trans (Iso.isoCongr b (t B.val))).bijective)

end GroupSchemes

section Relabel

variable {Γ M N : Type*} [Group Γ] [Group M] [Group N] [TopologicalSpace Γ]
  [TopologicalSpace M] [TopologicalSpace N] [DiscreteTopology M] [DiscreteTopology N]
  {ρ : Γ →* MulAut M} (c : M ≃* N)

private def unlabelCocycle (a : Cocycle (relabelAction c ρ)) : Cocycle ρ :=
  ⟨fun σ => c.symm (a σ), continuous_of_discreteTopology.comp a.property.1, fun σ τ => by
    apply c.injective
    change c (c.symm (a (σ * τ))) = c (c.symm (a σ) * ρ σ (c.symm (a τ)))
    rw [map_mul, c.apply_symm_apply, c.apply_symm_apply]
    exact a.property.2 σ τ⟩

private theorem relabelCocycle_surjective :
    Function.Surjective (relabelCocycle c (ρ := ρ)) :=
  fun a => ⟨unlabelCocycle c a, Subtype.ext (funext fun σ => c.apply_symm_apply (a σ))⟩

omit [DiscreteTopology N] in
private theorem relabelCocycle_changes {a b : Cocycle ρ} (x : M) :
    ChangesBy (relabelCocycle c a) (relabelCocycle c b) (c x) ↔ ChangesBy a b x := by
  have h (σ : Γ) :
      c (b σ) = (c x)⁻¹ * c (a σ) * c (ρ σ (c.symm (c x))) ↔
      b σ = x⁻¹ * a σ * ρ σ x := by
    rw [c.symm_apply_apply, ← map_inv c, ← map_mul c, ← map_mul c]
    exact c.injective.eq_iff
  exact ⟨fun he σ => (h σ).mp (he σ), fun he σ => (h σ).mpr (he σ)⟩

private def cohomologyRelabel : H1 ρ ≃ H1 (relabelAction c ρ) := by
  let f : H1 ρ → H1 (relabelAction c ρ) :=
    Quotient.lift (fun a => classOf (relabelCocycle c a)) (fun _ _ ⟨x, hx⟩ =>
      classOf_eq_iff.mpr ⟨c x, (relabelCocycle_changes c x).mpr hx⟩)
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro a b
    refine Quotient.inductionOn₂ a b (fun a b h => ?_)
    have hh : classOf (relabelCocycle c a) = classOf (relabelCocycle c b) := h
    obtain ⟨x, hx⟩ := classOf_eq_iff.mp hh
    obtain ⟨y, rfl⟩ := c.surjective x
    exact classOf_eq_iff.mpr ⟨y, (relabelCocycle_changes c y).mp hx⟩
  · intro a
    refine Quotient.inductionOn a (fun a => ?_)
    obtain ⟨b, hb⟩ := relabelCocycle_surjective c a
    exact ⟨classOf b, congrArg classOf hb⟩

private theorem cohomologyRelabel_basepoint :
    cohomologyRelabel c (basepoint ρ) = basepoint (relabelAction c ρ) := by
  apply congrArg classOf
  apply Subtype.ext
  funext σ
  exact map_one c

private theorem relabelAction_continuous
    (h : Continuous (fun p : Γ × M => ρ p.1 p.2)) :
    Continuous (fun p : Γ × N => relabelAction c ρ p.1 p.2) :=
  continuous_of_discreteTopology.comp (h.comp (continuous_fst.prodMk
    (continuous_of_discreteTopology.comp continuous_snd)))

end Relabel

section SchemeClassification

private theorem classifySchemes (G : Specs.AffineAlgebraicGroup k)
    (classifyHopf : ∀ (P : HopfAlgebraCategory k) (hP : Algebra.FiniteType k P), Classifies K P hP) :
    SchemeClassifies K G := by
  let : TopologicalSpace (Aut ((groupBaseChange k K).obj G.val)) := ⊥
  have : DiscreteTopology (Aut ((groupBaseChange k K).obj G.val)) := ⟨rfl⟩
  obtain ⟨P, hP, j, t, e, c, ht, hbase, he, hc, _⟩ := schemeComparison (K := K) G
  obtain ⟨ρ, d, hρ, hcont, hd, hclass, hrealize⟩ := classifyHopf P hP
  let q := e.symm.trans (d.trans (cohomologyRelabel c))
  refine ⟨P, hP, j, t, c, ρ, q, ht, hρ, hc, relabelAction_continuous c hcont, ?_, ?_, ?_⟩
  · change cohomologyRelabel c (d (e.symm (Quotient.mk _ ⟨G, ⟨Iso.refl _⟩⟩))) = _
    rw [← hbase, e.symm_apply_apply, hd, cohomologyRelabel_basepoint]
  · intro B i
    obtain ⟨a, ha, hqa⟩ := hclass B i
    refine ⟨a, ha, ?_⟩
    change cohomologyRelabel c (d (e.symm (Quotient.mk _ (realizeSchemeModel K j t B)))) = _
    rw [← he B, e.symm_apply_apply, hqa]
    rfl
  · intro a
    obtain ⟨b, hb⟩ := relabelCocycle_surjective c a
    obtain ⟨B, i, hi⟩ := hrealize b
    exact ⟨B, i, b, hi, hb⟩

/-- Finite Galois forms of an affine algebraic group up to group-scheme isomorphism. -/
theorem finiteSchemeForms : Specification.FiniteSchemes.{u} := by
  intro k K _ _ _ _ _ G
  exact classifySchemes G finiteForms

/-- Separable-closure forms classified by the continuous cohomology of the
actual group of automorphisms of the extended group scheme. -/
theorem separableClosureSchemeForms : Specification.SeparableClosureSchemes.{u} := by
  intro k S _ _ _ _ G
  exact classifySchemes G separableClosureForms

end SchemeClassification

end
end LinearAlgebraicGroups.Descent.Forms
