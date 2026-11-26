import Specs.LinearAlgebraicGroups.Affine.RationalJordanFactors
import LinearAlgebraicGroups.Affine.RationalRepresentations
import LinearAlgebraicGroups.Affine.LinearJordanFactors
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Rational Jordan decomposition via finite-dimensional subcomodules of the coordinate algebra. -/

open CategoryTheory WithConv Coalgebra Module
open scoped TensorProduct

universe u

namespace LinearAlgebraicGroups.Affine

noncomputable section

variable {k : Type u} [Field k] (A : HopfAlgebraCategory k)

private abbrev CoordinatePoint := (convolutionPoints A).obj (CommAlgCat.of k k)

variable {A} {V W : Type u} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

private def contract (g : A →ₐ[k] k) : V ⊗[k] A →ₗ[k] V :=
  (TensorProduct.rid k V).toLinearMap.comp (g.toLinearMap.lTensor V)

@[simp] private theorem contract_tmul (g : A →ₐ[k] k) (v : V) (a : A) :
    contract g (v ⊗ₜ[k] a) = g a • v := by simp [contract]

private def pointAction (ρ : RightComodule k A V) (g : CoordinatePoint A) : End k V :=
  (contract g.ofConv).comp ρ.coaction

private theorem action_natural (ρ : RightComodule k A V) (σ : RightComodule k A W)
    (f : V →ₗ[k] W) (hf : (f.rTensor A).comp ρ.coaction = σ.coaction.comp f)
    (g : CoordinatePoint A) :
    f.comp (pointAction ρ g) = (pointAction σ g).comp f := by
  ext x
  change f (contract g.ofConv (ρ.coaction x)) = contract g.ofConv (σ.coaction (f x))
  rw [← show f.rTensor A (ρ.coaction x) = σ.coaction (f x) from DFunLike.congr_fun hf x]
  induction ρ.coaction x using TensorProduct.inductionOn with
  | tmul v a => simp
  | add x y hx hy => simp [hx, hy]

private theorem action_mul (ρ : RightComodule k A V) (f g : CoordinatePoint A) :
    pointAction ρ (f * g) = pointAction ρ f * pointAction ρ g := by
  ext x
  let C : V ⊗[k] (A ⊗[k] A) →ₗ[k] V :=
    (contract f.ofConv).comp ((contract g.ofConv).lTensor V)
  have left (t : V ⊗[k] A) :
      C ((Coalgebra.comul (R := k) (A := A)).lTensor V t) = contract (f * g).ofConv t := by
    induction t using TensorProduct.inductionOn with
    | tmul v a =>
      simp only [LinearMap.lTensor_tmul, LinearMap.comp_apply, C, contract_tmul]
      congr 1
      rw [AlgHom.convMul_apply]
      generalize Coalgebra.comul (R := k) a = t
      induction t using TensorProduct.inductionOn with
      | tmul a b => simp [Algebra.smul_def, mul_comm]
      | add a b ha hb => simp [ha, hb]
    | add a b ha hb => simp [ha, hb]
  have right (t : V ⊗[k] A) :
      C (TensorProduct.assoc k V A A ((ρ.coaction.rTensor A) t)) =
        pointAction ρ f (contract g.ofConv t) := by
    induction t using TensorProduct.inductionOn with
    | tmul v a =>
      simp only [LinearMap.rTensor_tmul, contract_tmul, map_smul]
      change C (TensorProduct.assoc k V A A (ρ.coaction v ⊗ₜ[k] a)) =
        g.ofConv a • contract f.ofConv (ρ.coaction v)
      induction ρ.coaction v using TensorProduct.inductionOn with
      | tmul w b => simp [C, smul_smul, Algebra.smul_def, mul_comm]
      | add t s ht hs => simp [TensorProduct.add_tmul, ht, hs, smul_add]
    | add a b ha hb => simp [ha, hb]
  exact (left _).symm.trans ((congrArg C (ρ.coassoc x)).symm.trans (right _))

private theorem action_one (ρ : RightComodule k A V) :
    pointAction ρ (1 : CoordinatePoint A) = 1 := by
  ext x
  exact ρ.counit x

private theorem action_isUnit (ρ : RightComodule k A V) (g : CoordinatePoint A) :
    IsUnit (pointAction ρ g) := by
  let F : CoordinatePoint A →* End k V :=
    { toFun := pointAction ρ, map_one' := action_one ρ, map_mul' := action_mul ρ }
  exact (Group.isUnit g).map F

private def translation (g : CoordinatePoint A) : A →ₐ[k] A :=
  (Algebra.TensorProduct.rid k k A).toAlgHom.comp
    ((Algebra.TensorProduct.map (AlgHom.id k A) g.ofConv).comp (Bialgebra.comulAlgHom k A))

private theorem translation_eq (g : CoordinatePoint A) :
    (translation g).toLinearMap = pointAction (RightComodule.regular (k := k) (C := A)) g := by
  apply LinearMap.ext
  intro a
  change Algebra.TensorProduct.rid k k A
    (Algebra.TensorProduct.map (AlgHom.id k A) g.ofConv (Coalgebra.comul a)) =
    contract g.ofConv (Coalgebra.comul a)
  induction Coalgebra.comul (R := k) a using TensorProduct.inductionOn with
  | tmul a b => simp
  | add a b ha hb => simp [ha, hb]

private theorem counit_translation (g : CoordinatePoint A) (a : A) :
    counit (R := k) (translation g a) = g.ofConv a := by
  let F : k ⊗[k] A →ₗ[k] k :=
    g.ofConv.toLinearMap.comp (TensorProduct.lid k A).toLinearMap
  have h (z : A ⊗[k] A) :
      counit (R := k) (contract g.ofConv z) = F ((counit (R := k)).rTensor A z) := by
    induction z using TensorProduct.inductionOn with
    | tmul a b => simp [F, smul_eq_mul, mul_comm]
    | add a b ha hb => simp [ha, hb]
  rw [show translation g a = pointAction (RightComodule.regular (k := k) (C := A)) g a
    from DFunLike.congr_fun (translation_eq g) a]
  change counit (R := k) (contract g.ofConv (Coalgebra.comul a)) = g.ofConv a
  rw [h, Coalgebra.rTensor_counit_comul]
  simp [F]

private abbrev RegularSubcomodule (A : HopfAlgebraCategory k) :=
  (RightComodule.regular (k := k) (C := A)).FiniteSubcomodule

private instance (D : RegularSubcomodule A) : FiniteDimensional k D.val := D.property.2

private def slice (D : RegularSubcomodule A) : RightComodule k A D.val :=
  ((RightComodule.regular.isSubcomodule_iff_exists_coaction D.val).mp
    D.property.1).choose

private theorem slice_intertwines (g : CoordinatePoint A) (D : RegularSubcomodule A) :
    D.val.subtype.comp (pointAction (slice D) g) =
      (translation g).toLinearMap.comp D.val.subtype := by
  rw [translation_eq]
  exact action_natural _ _ _
    (((RightComodule.regular.isSubcomodule_iff_exists_coaction D.val).mp
      D.property.1).choose_spec) g

section Perfect

variable [PerfectField k]

private def jordanPair [FiniteDimensional k V] (f : End k V) (hf : IsUnit f) :
    End k V × End k V :=
  (multiplicativeJordanDecomposition f hf).exists.choose

private theorem jordanPair_spec [FiniteDimensional k V] (f : End k V) (hf : IsUnit f) :
    IsMultiplicativeJordanDecomposition f (jordanPair f hf).1 (jordanPair f hf).2 :=
  (multiplicativeJordanDecomposition f hf).exists.choose_spec

private def component (s : Bool) (e : End k V × End k V) : End k V :=
  if s then e.1 else e.2

private theorem component_intertwines [FiniteDimensional k V] [FiniteDimensional k W]
    {f s t : End k V} {g s' t' : End k W} (h : V →ₗ[k] W)
    (hf : IsMultiplicativeJordanDecomposition f s t)
    (hg : IsMultiplicativeJordanDecomposition g s' t')
    (hh : h.comp f = g.comp h) (b : Bool) :
    h.comp (component b (s, t)) = (component b (s', t')).comp h := by
  have H := multiplicativeJordanIntertwining h hf hg hh
  cases b
  · exact H.2
  · exact H.1

private def factors [FiniteDimensional k V]
    (ρ : RightComodule k A V) (g : CoordinatePoint A) : End k V × End k V :=
  jordanPair (pointAction ρ g) (action_isUnit ρ g)

private theorem factors_spec [FiniteDimensional k V]
    (ρ : RightComodule k A V) (g : CoordinatePoint A) :
    IsMultiplicativeJordanDecomposition (pointAction ρ g) (factors ρ g).1 (factors ρ g).2 :=
  jordanPair_spec _ _

private theorem factors_comp [FiniteDimensional k V] [FiniteDimensional k W]
    (ρ : RightComodule k A V) (σ : RightComodule k A W) (g : CoordinatePoint A)
    (f : V →ₗ[k] W) (hf : f.comp (pointAction ρ g) = (pointAction σ g).comp f)
    (b : Bool) :
    f.comp (component b (factors ρ g)) = (component b (factors σ g)).comp f :=
  component_intertwines f (factors_spec ρ g) (factors_spec σ g) hf b

private def sliceOf (x : A) : RegularSubcomodule A :=
  ((RightComodule.regular (k := k) (C := A)).exists_finiteSubcomodule x).choose

omit [PerfectField k] in
private theorem mem_sliceOf (x : A) : x ∈ (sliceOf x).val :=
  ((RightComodule.regular (k := k) (C := A)).exists_finiteSubcomodule x).choose_spec

private def translationFactor (g : CoordinatePoint A) (b : Bool) (x : A) : A :=
  component b (factors (slice (sliceOf x)) g) ⟨x, mem_sliceOf x⟩

private theorem slice_inclusion_factor (g : CoordinatePoint A) (b : Bool)
    (D E : RegularSubcomodule A) (hle : D.val ≤ E.val) (x : D.val) :
    (component b (factors (slice D) g) x : A) =
      (component b (factors (slice E) g) (Submodule.inclusion hle x) : A) := by
  have hi : (Submodule.inclusion hle).comp (pointAction (slice D) g) =
      (pointAction (slice E) g).comp (Submodule.inclusion hle) := by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    exact (DFunLike.congr_fun (slice_intertwines g D) y).trans
      (DFunLike.congr_fun (slice_intertwines g E) (Submodule.inclusion hle y)).symm
  exact congrArg Subtype.val (DFunLike.congr_fun (factors_comp _ _ g _ hi b) x)

private theorem translationFactor_apply (g : CoordinatePoint A) (b : Bool)
    (D : RegularSubcomodule A) (x : D.val) :
    translationFactor g b (x : A) = (component b (factors (slice D) g) x : A) := by
  obtain ⟨E, h₁, h₂⟩ := (RightComodule.regular (k := k) (C := A)).directed_finiteSubcomodules
    (sliceOf (x : A)) D
  exact (slice_inclusion_factor g b _ E h₁ ⟨x, mem_sliceOf (x : A)⟩).trans
    (slice_inclusion_factor g b D E h₂ x).symm

/-- Restrict the codomain of any map with finite-dimensional source to a finite
subcomodule containing its range. Only the intertwining at the given point is needed. -/
private theorem translationFactor_intertwines [FiniteDimensional k V]
    (g : CoordinatePoint A) (b : Bool) (f s t : End k V)
    (h : IsMultiplicativeJordanDecomposition f s t)
    (j : V →ₗ[k] A) (hj : j.comp f = (translation g).toLinearMap.comp j) (x : V) :
    translationFactor g b (j x) = j (component b (s, t) x) := by
  let basis := Module.finBasis k V
  obtain ⟨D, hD⟩ := (RightComodule.regular (k := k) (C := A))
    |>.exists_finiteSubcomodule_containing_range (fun i ↦ j (basis i))
  let j' : V →ₗ[k] D.val := basis.constr k fun i ↦ ⟨j (basis i), hD i⟩
  have hj' : D.val.subtype.comp j' = j := by
    apply basis.ext
    intro i
    simp [j']
  have hi : j'.comp f = (pointAction (slice D) g).comp j' := by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    exact (DFunLike.congr_fun hj' (f y)).trans ((DFunLike.congr_fun hj y).trans
      (congrArg (translation g) (DFunLike.congr_fun hj' y).symm |>.trans
        (DFunLike.congr_fun (slice_intertwines g D) (j' y)).symm))
  rw [← DFunLike.congr_fun hj' x]
  change translationFactor g b (j' x : A) = j (component b (s, t) x)
  rw [translationFactor_apply]
  exact (congrArg Subtype.val (DFunLike.congr_fun
    (component_intertwines j' h (factors_spec (slice D) g) hi b) x)).symm.trans
    (DFunLike.congr_fun hj' _)

private theorem translationFactor_add (g : CoordinatePoint A) (b : Bool) (x y : A) :
    translationFactor g b (x + y) = translationFactor g b x + translationFactor g b y := by
  obtain ⟨D, hx, hy⟩ := (RightComodule.regular (k := k) (C := A)).directed_finiteSubcomodules
    (sliceOf x) (sliceOf y)
  let x' : D.val := ⟨x, hx (mem_sliceOf x)⟩
  let y' : D.val := ⟨y, hy (mem_sliceOf y)⟩
  change translationFactor g b (↑(x' + y')) =
    translationFactor g b (x' : A) + translationFactor g b (y' : A)
  rw [translationFactor_apply g b D (x' + y'), translationFactor_apply g b D x',
    translationFactor_apply g b D y', map_add, Submodule.coe_add]

private theorem translationFactor_mul (g : CoordinatePoint A) (b : Bool) (x y : A) :
    translationFactor g b (x * y) = translationFactor g b x * translationFactor g b y := by
  let D := sliceOf x
  let E := sliceOf y
  let x' : D.val := ⟨x, mem_sliceOf x⟩
  let y' : E.val := ⟨y, mem_sliceOf y⟩
  let m : D.val ⊗[k] E.val →ₗ[k] A :=
    (TensorProduct.lift (LinearMap.mul k A)).comp (TensorProduct.map D.val.subtype E.val.subtype)
  have hm (v : D.val) (w : E.val) : m (v ⊗ₜ[k] w) = (v : A) * (w : A) := by
    simp [m]
  have hi : m.comp (TensorProduct.map (pointAction (slice D) g) (pointAction (slice E) g)) =
      (translation g).toLinearMap.comp m := by
    apply TensorProduct.ext'
    intro v w
    simp only [LinearMap.comp_apply, TensorProduct.map_tmul, hm, AlgHom.toLinearMap_apply,
      map_mul]
    exact congrArg₂ (· * ·) (DFunLike.congr_fun (slice_intertwines g D) v)
      (DFunLike.congr_fun (slice_intertwines g E) w)
  have h := translationFactor_intertwines g b _ _ _
    (multiplicativeJordanTensor (factors_spec (slice D) g) (factors_spec (slice E) g))
    m hi (x' ⊗ₜ[k] y')
  rw [hm] at h
  change translationFactor g b ((x' : A) * (y' : A)) = _
  rw [h, translationFactor_apply g b D x', translationFactor_apply g b E y']
  cases b <;> simp only [component, Bool.false_eq_true, ↓reduceIte, TensorProduct.map_tmul, hm]

private theorem translationFactor_constants (g : CoordinatePoint A) (b : Bool) (r : k) :
    translationFactor g b (algebraMap k A r) = algebraMap k A r := by
  have h : IsMultiplicativeJordanDecomposition (1 : End k k) 1 1 :=
    ⟨by simp, Commute.refl _, Module.End.isSemisimple_id, by simp, isUnit_one, isUnit_one⟩
  have hi : (Algebra.linearMap k A).comp (1 : End k k) =
      (translation g).toLinearMap.comp (Algebra.linearMap k A) := by
    apply LinearMap.ext
    intro z
    exact ((translation g).commutes z).symm
  simpa [component] using translationFactor_intertwines g b 1 1 1 h (Algebra.linearMap k A) hi r

private def translationFactorHom (g : CoordinatePoint A) (b : Bool) : A →ₐ[k] A where
  toFun := translationFactor g b
  map_one' := by simpa using translationFactor_constants g b (1 : k)
  map_zero' := by simpa using translationFactor_constants g b (0 : k)
  map_add' := translationFactor_add g b
  map_mul' := translationFactor_mul g b
  commutes' := translationFactor_constants g b

private def coordinateFactor (g : CoordinatePoint A) (b : Bool) : CoordinatePoint A :=
  toConv ((Bialgebra.counitAlgHom k A).comp (translationFactorHom g b))

private def matrixCoefficient (ρ : RightComodule k A V) (ℓ : V →ₗ[k] k) : V →ₗ[k] A :=
  (TensorProduct.lid k A).toLinearMap.comp ((ℓ.rTensor A).comp ρ.coaction)

omit [PerfectField k] in
private theorem matrixCoefficient_intertwines (ρ : RightComodule k A V)
    (ℓ : V →ₗ[k] k) (g : CoordinatePoint A) :
    (matrixCoefficient ρ ℓ).comp (pointAction ρ g) =
      (translation g).toLinearMap.comp (matrixCoefficient ρ ℓ) := by
  rw [translation_eq]
  apply action_natural
  apply LinearMap.ext
  intro x
  let L : V ⊗[k] A →ₗ[k] A :=
    (TensorProduct.lid k A).toLinearMap.comp (ℓ.rTensor A)
  let F : V ⊗[k] (A ⊗[k] A) →ₗ[k] A ⊗[k] A :=
    (TensorProduct.lid k (A ⊗[k] A)).toLinearMap.comp (ℓ.rTensor (A ⊗[k] A))
  have h₁ (z : (V ⊗[k] A) ⊗[k] A) :
      F (TensorProduct.assoc k V A A z) = L.rTensor A z := by
    induction z using TensorProduct.inductionOn with
    | tmul z a =>
      induction z using TensorProduct.inductionOn with
      | tmul v b => simp [F, L, TensorProduct.smul_tmul']
      | add x y hx hy => simp [TensorProduct.add_tmul, hx, hy]
    | add x y hx hy => simp [hx, hy]
  have h₂ (z : V ⊗[k] A) :
      F ((Coalgebra.comul (R := k) (A := A)).lTensor V z) =
        Coalgebra.comul (R := k) (L z) := by
    induction z using TensorProduct.inductionOn with
    | tmul v a => simp [F, L]
    | add x y hx hy => simp [hx, hy]
  have h₃ (z : V ⊗[k] A) :
      L.rTensor A (ρ.coaction.rTensor A z) = (matrixCoefficient ρ ℓ).rTensor A z := by
    induction z using TensorProduct.inductionOn with
    | tmul v a => rfl
    | add x y hx hy => simp [hx, hy]
  have h := congrArg F (ρ.coassoc x)
  rw [h₁, h₂, h₃] at h
  exact h

omit [PerfectField k] in
private theorem matrixCoefficient_action (ρ : RightComodule k A V)
    (ℓ : V →ₗ[k] k) (g : CoordinatePoint A) (v : V) :
    ℓ (pointAction ρ g v) = g.ofConv (matrixCoefficient ρ ℓ v) := by
  change ℓ (contract g.ofConv (ρ.coaction v)) =
    g.ofConv (TensorProduct.lid k A ((ℓ.rTensor A) (ρ.coaction v)))
  induction ρ.coaction v using TensorProduct.inductionOn with
  | tmul x a => simp [smul_eq_mul, mul_comm]
  | add x y hx hy => simp [hx, hy]

private theorem coordinateFactor_action [FiniteDimensional k V]
    (ρ : RightComodule k A V) (g : CoordinatePoint A) (b : Bool) :
    pointAction ρ (coordinateFactor g b) = component b (factors ρ g) := by
  apply (Module.finBasis k V).ext
  intro i
  apply (Module.finBasis k V).repr.injective
  ext j
  let ℓ := (Module.finBasis k V).coord j
  change ℓ (pointAction ρ (coordinateFactor g b) ((Module.finBasis k V) i)) = _
  rw [matrixCoefficient_action]
  change counit (R := k) (translationFactor g b
    (matrixCoefficient ρ ℓ ((Module.finBasis k V) i))) = _
  rw [translationFactor_intertwines g b _ _ _ (factors_spec ρ g) _
    (matrixCoefficient_intertwines ρ ℓ g)]
  exact (matrixCoefficient_action ρ ℓ (1 : CoordinatePoint A) _).symm.trans
    (by rw [action_one]; rfl)

omit [PerfectField k] in
private theorem coordinatePoint_ext {g h : CoordinatePoint A}
    (H : ∀ D : RegularSubcomodule A, pointAction (slice D) g = pointAction (slice D) h) : g = h := by
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro x
  obtain ⟨D, hx⟩ := (RightComodule.regular (k := k) (C := A)).exists_finiteSubcomodule x
  let x' : D.val := ⟨x, hx⟩
  rw [← counit_translation g x, ← counit_translation h x]
  congr 1
  exact (DFunLike.congr_fun (slice_intertwines g D) x').symm.trans
    ((congrArg Subtype.val (DFunLike.congr_fun (H D) x')).trans
      (DFunLike.congr_fun (slice_intertwines h D) x'))

private theorem coordinateFactors_spec [FiniteDimensional k V]
    (ρ : RightComodule k A V) (g : CoordinatePoint A) :
    IsMultiplicativeJordanDecomposition (pointAction ρ g)
      (pointAction ρ (coordinateFactor g true)) (pointAction ρ (coordinateFactor g false)) := by
  rw [coordinateFactor_action, coordinateFactor_action]
  exact factors_spec ρ g

private theorem coordinateFactors_mul (g : CoordinatePoint A) :
    g = coordinateFactor g true * coordinateFactor g false := by
  apply coordinatePoint_ext
  intro D
  rw [action_mul]
  exact (coordinateFactors_spec (slice D) g).eq_mul

private theorem coordinateFactors_commute (g : CoordinatePoint A) :
    Commute (coordinateFactor g true) (coordinateFactor g false) := by
  apply coordinatePoint_ext
  intro D
  rw [action_mul, action_mul]
  exact (coordinateFactors_spec (slice D) g).commute.eq

omit [PerfectField k] in
open RationalRepresentations in
private theorem representation_action_eq {ι : Type u} [Fintype ι] [DecidableEq ι]
    (b : Basis ι k V) (G : AffineGroupCategory k) (L : Specs.GroupScheme k)
    (e : convolutionPoints A ≅ (groupPointsFunctor k).obj G.val)
    (l : (groupPointsFunctor k).obj L ≅ Specs.StandardGroups.generalLinearPoints k ι)
    (f : Representation G L l) (ρ : RightComodule k A V)
    (hρ : coefficients A b ρ = universalMatrix A G L e l f) (g : CoordinatePoint A) :
    pointAction ρ g = rationalRepresentationAction b l f (e.hom.app _ g) := by
  apply b.ext
  intro j
  have h := evaluationComparison A b G L e l f ρ hρ (CommAlgCat.of k k) g.ofConv j
  apply congrArg (TensorProduct.rid k V) at h
  simpa [pointAction, contract, evaluate, rationalRepresentationAction, Matrix.toLin_self]
    using h

set_option maxHeartbeats 1000000 in
private theorem rationalJordanDecomposition_of_coordinates
    (G' : AffineGroupCategory k) (e : convolutionPoints A ≅ (groupPointsFunctor k).obj G'.val)
    (g : RationalPoints G'.val) :
    ∃! p : RationalPoints G'.val × RationalPoints G'.val,
      IsRationalJordanDecomposition G' g p.1 p.2 := by
  let r := CommAlgCat.of k k
  let eₖ := (e.app r).groupIsoToMulEquiv
  let g' : CoordinatePoint A := eₖ.symm g
  have hg : eₖ g' = g := eₖ.apply_symm_apply g
  let s := coordinateFactor g' true
  let t := coordinateFactor g' false
  refine ⟨(eₖ s, eₖ t), ⟨?_, ?_, ?_⟩, ?_⟩
  · exact hg.symm.trans ((congrArg eₖ (coordinateFactors_mul g')).trans (map_mul eₖ s t))
  · exact (coordinateFactors_commute g').map eₖ
  · intro V ι _ _ _ _ b L l f
    let : FiniteDimensional k V := b.finiteDimensional_of_finite
    obtain ⟨E, hE⟩ := RationalRepresentations.representationCoactionComparison A b G' L e l
    have hAction (a : CoordinatePoint A) :
        pointAction (E f) a = rationalRepresentationAction b l f (eₖ a) :=
      representation_action_eq b G' L e l f (E f) (hE f) a
    simpa only [hAction, hg] using coordinateFactors_spec (E f) g'
  · rintro ⟨s₀, t₀⟩ ⟨_, _, hst⟩
    let s' : CoordinatePoint A := eₖ.symm s₀
    let t' : CoordinatePoint A := eₖ.symm t₀
    have hs₀ : eₖ s' = s₀ := eₖ.apply_symm_apply s₀
    have ht₀ : eₖ t' = t₀ := eₖ.apply_symm_apply t₀
    have h (D : RegularSubcomodule A) :
        (pointAction (slice D) s', pointAction (slice D) t') =
          (pointAction (slice D) s, pointAction (slice D) t) := by
      let ι := ULift.{u} (Fin (finrank k D.val))
      let b : Basis ι k D.val := (Module.finBasis k D.val).reindex Equiv.ulift.symm
      let L := StandardGroups.generalLinearGroup k ι
      let l := StandardGroups.generalLinearGroupPointsIso (k := k) (ι := ι)
      obtain ⟨E, hE⟩ := RationalRepresentations.representationCoactionComparison A b G' L.val e l
      let f := E.symm (slice D)
      have hρ : RationalRepresentations.coefficients A b (slice D) =
          RationalRepresentations.universalMatrix A G' L.val e l f := by
        simpa only [f, Equiv.apply_symm_apply] using hE f
      have hAction (a : CoordinatePoint A) :
          pointAction (slice D) a = rationalRepresentationAction b l f (eₖ a) :=
        representation_action_eq b G' L.val e l f (slice D) hρ a
      have hdecomp : IsMultiplicativeJordanDecomposition (pointAction (slice D) g')
          (pointAction (slice D) s') (pointAction (slice D) t') := by
        simpa only [hAction, hg, hs₀, ht₀] using hst b L.val l f
      exact (multiplicativeJordanDecomposition _ (action_isUnit (slice D) g')).unique
        hdecomp (coordinateFactors_spec (slice D) g')
    have hs : s' = s := coordinatePoint_ext fun D ↦ congrArg Prod.fst (h D)
    have ht : t' = t := coordinatePoint_ext fun D ↦ congrArg Prod.snd (h D)
    exact Prod.ext (hs₀.symm.trans (congrArg eₖ hs))
      (ht₀.symm.trans (congrArg eₖ ht))

/-- Rational Jordan–Chevalley decomposition, with simultaneous compatibility
with every finite-dimensional rational representation. -/
theorem rationalJordanDecomposition : RationalJordanFactorsSpec.existenceAndUniqueness.{u} := by
  intro k _ _ G g
  let := affineHopfSpecEquivalence k
  let G' : AffineGroupCategory k := ⟨G.val, G.property.1⟩
  obtain ⟨e, _⟩ := coordinateHopfPoints k G'
  exact rationalJordanDecomposition_of_coordinates G' e g

set_option maxHeartbeats 600000 in
/-- Composition with a group scheme homomorphism preserves rational Jordan factors. -/
theorem rationalJordanDecompositionFunctorial : RationalJordanFactorsSpec.functoriality.{u} := by
  intro k _ _ G H f g s t h
  let r := CommAlgCat.of k k
  let F := groupPointsFunctor k
  let φ : RationalPoints G.val →* RationalPoints H.val := ((F.map f).app r).hom
  obtain ⟨hprod, hcomm, hrep⟩ := h
  refine ⟨(congrArg φ hprod).trans (map_mul φ s t), hcomm.map φ, ?_⟩
  intro V ι _ _ _ _ b L l ρ
  have hact (a : RationalPoints G.val) :
      rationalRepresentationAction (G := ⟨G.val, G.property.1⟩) b l (f ≫ ρ) a =
        rationalRepresentationAction (G := ⟨H.val, H.property.1⟩) b l ρ (φ a) := by
    simp only [rationalRepresentationAction, F, φ, r, Functor.map_comp, NatTrans.comp_app,
      GrpCat.comp_apply]
  simpa only [hact] using hrep b L l (f ≫ ρ)

end Perfect

open Polynomial in
/-- The semisimple factor of multiplication by a purely inseparable root need not descend. -/
theorem imperfectFieldJordanExample : RationalJordanFactorsSpec.imperfectFieldExample.{u} := by
  intro k _ p _ hp a ha
  let P : k[X] := X ^ p - C a
  let E := AdjoinRoot P
  let K := AlgebraicClosure k
  let r := AdjoinRoot.root P
  let F : End k E := Algebra.lmul k E r
  let : NeZero p := ⟨hp.ne'⟩
  let : Fact p.Prime := CharP.char_is_prime_of_pos k p
  have hP : Irreducible P := X_pow_sub_C_irreducible_of_prime Fact.out ha
  let : Fact (Irreducible P) := ⟨hP⟩
  have hm : P.Monic := monic_X_pow_sub_C a hp.ne'
  let : FiniteDimensional k E := hm.finite_adjoinRoot
  have hr : r ^ p = algebraMap k E a := by
    have h := AdjoinRoot.mk_self (f := P)
    change AdjoinRoot.mk P (X ^ p - C a) = 0 at h
    rw [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, sub_eq_zero] at h
    exact h
  have ha₀ : a ≠ 0 := by simpa [zero_pow hp.ne'] using (ha 0).symm
  have hr₀ : r ≠ 0 := by
    intro hz
    exact ha₀ ((algebraMap k E).injective (by simpa [hz, zero_pow hp.ne'] using hr.symm))
  have hF : IsUnit F := (isUnit_iff_ne_zero.mpr hr₀).map (Algebra.lmul k E).toMonoidHom
  have hchar : F.charpoly = P := by
    let B := AdjoinRoot.powerBasis hm.ne_zero
    have hB : B.gen = r := AdjoinRoot.powerBasis_gen hm.ne_zero
    rw [← F.charpoly_toMatrix B.basis]
    change (Algebra.leftMulMatrix B.basis r).charpoly = P
    rw [← hB, charpoly_leftMulMatrix B]
    exact AdjoinRoot.minpoly_powerBasis_gen_of_monic hm
  refine ⟨hP, AdjoinRoot.isField_iff_irreducible.mpr hP, hr, hF, hchar, ?_⟩
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap k K a) hp
  have hc₀ : c ≠ 0 := by
    intro hz
    exact ha₀ ((algebraMap k K).injective (by simpa [hz, zero_pow hp.ne'] using hc.symm))
  refine ⟨c, hc, ?_, ?_⟩
  · let H := F.baseChange K
    let S : End K (K ⊗[k] E) := c • 1
    let U := c⁻¹ • H
    have hU : U ^ p = 1 := by
      have hFp : F ^ p = a • 1 := by
        dsimp only [F]
        rw [← map_pow, hr, AlgHom.commutes]
        rfl
      have hHp : H ^ p = (algebraMap k K a) • 1 := by
        rw [← LinearMap.baseChange_pow, hFp, LinearMap.baseChange_smul, LinearMap.baseChange_one]
        exact (IsScalarTower.algebraMap_smul K a (1 : End K (K ⊗[k] E))).symm
      rw [show U = c⁻¹ • H from rfl, smul_pow, hHp, ← hc, smul_smul, ← mul_pow,
        inv_mul_cancel₀ hc₀, one_pow, one_smul]
    have hcomm : Commute S U := Algebra.commute_algebraMap_left c U
    have hSunit : IsUnit S :=
      (isUnit_iff_ne_zero.mpr hc₀).map (algebraMap K (End K (K ⊗[k] E)))
    have hsp : S.IsSemisimple := Module.End.IsSemisimple_smul _ Module.End.isSemisimple_id
    have : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
    have : CharP (End K (K ⊗[k] E)) p :=
      charP_of_injective_algebraMap (algebraMap K (End K (K ⊗[k] E))).injective p
    have hn : IsNilpotent (U - 1) := ⟨p, by
      rw [sub_pow_char_of_commute p (Commute.one_right U), hU, one_pow, sub_self]⟩
    refine ⟨U, ⟨?_, hcomm, hsp, hn, hSunit, (isUnit_pow_iff hp.ne').mp (hU ▸ isUnit_one)⟩⟩
    change H = (c • (1 : End K (K ⊗[k] E))) * (c⁻¹ • H)
    rw [smul_mul_assoc, one_mul, smul_smul, mul_inv_cancel₀ hc₀, one_smul]
  · rintro ⟨S, hS⟩
    obtain ⟨ℓ, hℓ⟩ := Module.Projective.exists_dual_eq_one k (one_ne_zero : (1 : E) ≠ 0)
    let d : K ⊗[k] E →ₗ[K] K := ((Algebra.linearMap k K).comp ℓ).liftBaseChange K
    have h := congrArg (fun T : End K (K ⊗[k] E) ↦ d (T ((1 : K) ⊗ₜ[k] (1 : E)))) hS
    have hc' : algebraMap k K (ℓ (S 1)) = c := by
      simpa [d, LinearMap.baseChange_tmul, LinearMap.liftBaseChange_tmul, hℓ] using h
    apply ha (ℓ (S 1))
    apply (algebraMap k K).injective
    rw [map_pow, hc', hc]

end
end LinearAlgebraicGroups.Affine
