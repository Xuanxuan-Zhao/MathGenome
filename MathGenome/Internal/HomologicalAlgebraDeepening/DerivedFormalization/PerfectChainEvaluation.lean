import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CochainModels
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.PerfectChainEvaluation
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.LinearAlgebra.Contraction
import Mathlib.Data.Int.Interval
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

namespace DerivedFormalization

open CategoryTheory Limits MonoidalCategory HomologicalComplex
open CochainComplex.HomComplex
open Specs.DerivedFormalization.PerfectChainEvaluation (boundedFiniteProjectiveValue)
open scoped TensorProduct

universe u
variable {R : Type u} [CommRing R]

noncomputable section

private theorem curry_apply_at (X Y Z : Comp.{u} R) (a : tensorComplex X Y ⟶ Z)
    {i j t : ℤ} (ht : i+j=t) (x : X.X i) (y : Y.X j) :
    ((tensorHomEquiv X Y Z a).f i x).v j t (by omega) y =
      a.f t (ιTensorObj X Y i j t ht (x ⊗ₜ[R] y)) := by
  subst t
  exact tensorHomEquiv_apply X Y Z a i j x y

/-- The tensor unit, namely the ring in degree zero. -/
abbrev ringStalk (R : Type u) [CommRing R] : Comp.{u} R :=
  HomologicalComplex.tensorUnit (ModuleCat R) (.up ℤ)

/-- The signed cochain dual with values in the ring in degree zero. -/
abbrev chainDual (P : Comp.{u} R) : Comp.{u} R := internalHom P (ringStalk R)

private abbrev stalkZero : (ringStalk R).X 0 ≅ ModuleCat.of R R :=
  singleObjXSelf (.up ℤ) 0 (ModuleCat.of R R)

private theorem stalkIsZero {n : ℤ} (h : n ≠ 0) : IsZero ((ringStalk R).X n) :=
  isZero_single_obj_X (.up ℤ) 0 (ModuleCat.of R R) n h

private theorem cochainDual_ext {P : Comp.{u} R} {n i : ℤ} (hi : i + n = 0)
    {f g : Cochain P (ringStalk R) n} (h : f.v i 0 hi = g.v i 0 hi) : f = g := by
  apply Cochain.ext
  intro j k hj
  by_cases hk : k = 0
  · obtain rfl : j = i := by omega
    cases hk
    exact h
  · exact (stalkIsZero hk).eq_of_tgt _ _

/-- A degree of the cochain dual is the module dual in the opposite degree. -/
def chainDualTerm (P : Comp.{u} R) {i n : ℤ} (hi : i + n = 0) :
    (chainDual P).X n ≃ₗ[R] Module.Dual R (P.X i) where
  toFun f := (f.v i 0 hi ≫ (stalkZero (R := R)).hom).hom
  invFun g := Cochain.mk fun j k hj =>
    if hk : k = 0 then
      eqToHom (congrArg P.X (show j = i by omega)) ≫ ModuleCat.ofHom g ≫
        (stalkZero (R := R)).inv ≫ eqToHom (congrArg (ringStalk R).X hk.symm)
    else 0
  left_inv f := by
    apply cochainDual_ext hi
    simp
  right_inv g := by
    change ((Cochain.mk _).v i 0 hi ≫ (stalkZero (R := R)).hom).hom = g
    simp
  map_add' f g := by
    ext x
    change ((f.v i 0 hi + g.v i 0 hi) ≫ (stalkZero (R := R)).hom) x = _
    rw [Preadditive.add_comp]
    rfl
  map_smul' r f := by
    ext x
    change ((r • f.v i 0 hi) ≫ (stalkZero (R := R)).hom) x = _
    rw [Linear.smul_comp]
    rfl

theorem chainDualTerm_apply (P : Comp.{u} R) {i n : ℤ} (hi : i + n = 0)
    (f : (chainDual P).X n) (x : P.X i) :
    chainDualTerm P hi f x = (stalkZero (R := R)).hom (f.v i 0 hi x) := rfl

theorem chainDual_boundedFiniteProjective {P : Comp.{u} R} (hP : boundedFiniteProjectiveValue P) :
    boundedFiniteProjectiveValue (chainDual P) := by
  obtain ⟨⟨a, b, hb⟩, hf, hp⟩ := hP
  let (i : ℤ) := hf i
  let (i : ℤ) := hp i
  refine ⟨⟨-b, -a, ?_⟩, ?_, ?_⟩
  · intro n hn
    let : Subsingleton (P.X (-n)) := ModuleCat.subsingleton_of_isZero (hb (-n) (by omega))
    exact ModuleCat.isZero_iff_subsingleton.mpr
      (chainDualTerm P (show -n + n = 0 by omega)).injective.subsingleton
  · intro n
    exact Module.Finite.of_surjective _ (chainDualTerm P (show -n + n = 0 by omega)).symm.surjective
  · intro n
    exact Module.Projective.of_equiv' (chainDualTerm P (show -n + n = 0 by omega)).symm

/-- Evaluation on the signed internal Hom, obtained by uncurrying the identity. -/
def chainEvaluation (P : Comp.{u} R) : tensorComplex (chainDual P) P ⟶ ringStalk R :=
  (tensorHomEquiv (chainDual P) P (ringStalk R)).symm (𝟙 (chainDual P))

theorem chainEvaluation_apply (P : Comp.{u} R) (j i t : ℤ) (ht : j + i = t)
    (f : (chainDual P).X j) (x : P.X i) :
    (chainEvaluation P).f t (ιTensorObj (chainDual P) P j i t ht (f ⊗ₜ[R] x)) =
      f.v i t (by omega) x := by
  subst t
  rw [← tensorHomEquiv_apply, chainEvaluation, LinearEquiv.apply_symm_apply]
  rfl

private theorem leftUnitor_inv_apply (Y : Comp.{u} R) (i : ℤ) (y : Y.X i) :
    (λ_ Y).inv.f i y =
      ιTensorObj (ringStalk R) Y 0 i i (zero_add i)
        ((stalkZero (R := R)).inv 1 ⊗ₜ[R] y) := by
  change (leftUnitor' Y).inv i y = _
  have h := ConcreteCategory.congr_hom (HomologicalComplex.leftUnitor'_inv Y i) y
  simp only [ModuleCat.comp_apply, ModuleCat.MonoidalCategory.leftUnitor_inv_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply] at h
  exact h

private theorem rightUnitor_inv_apply (Y : Comp.{u} R) (i : ℤ) (y : Y.X i) :
    (ρ_ Y).inv.f i y =
      ιTensorObj Y (ringStalk R) i 0 i (add_zero i)
        (y ⊗ₜ[R] (stalkZero (R := R)).inv 1) := by
  change (rightUnitor' Y).inv i y = _
  have h := ConcreteCategory.congr_hom (HomologicalComplex.rightUnitor'_inv Y i) y
  simp only [ModuleCat.comp_apply, ModuleCat.MonoidalCategory.rightUnitor_inv_apply,
    ModuleCat.MonoidalCategory.whiskerLeft_apply] at h
  exact h

private theorem rightUnitor_hom_apply (Y : Comp.{u} R) (i : ℤ) (y : Y.X i)
    (r : (ringStalk R).X 0) :
    (ρ_ Y).hom.f i (ιTensorObj Y (ringStalk R) i 0 i (add_zero i) (y ⊗ₜ[R] r)) =
      (stalkZero (R := R)).hom r • y := by
  apply (ConcreteCategory.bijective_of_isIso ((ρ_ Y).inv.f i)).injective
  have h := ConcreteCategory.congr_hom (congrArg (fun f : tensorComplex Y (ringStalk R) ⟶
    tensorComplex Y (ringStalk R) => f.f i) (ρ_ Y).hom_inv_id)
    (ιTensorObj Y (ringStalk R) i 0 i (add_zero i) (y ⊗ₜ[R] r))
  simp only [comp_f, ModuleCat.comp_apply, id_f] at h
  rw [h, rightUnitor_inv_apply, TensorProduct.smul_tmul]
  apply congrArg (ιTensorObj Y (ringStalk R) i 0 i (add_zero i))
  apply congrArg (fun a => y ⊗ₜ[R] a)
  symm
  rw [← map_smul (stalkZero (R := R)).inv.hom]
  change (stalkZero (R := R)).inv.hom (_ • (1 : R)) = _
  rw [smul_eq_mul, mul_one]
  exact ConcreteCategory.congr_hom (stalkZero (R := R)).hom_inv_id r

private theorem assoc_apply (X Y Z : Comp.{u} R) (i j k l : ℤ) (hl : i + j + k = l)
    (x : X.X i) (y : Y.X j) (z : Z.X k) :
    (α_ X Y Z).hom.f l
      (ιTensorObj (tensorComplex X Y) Z (i + j) k l hl
        (ιTensorObj X Y i j (i + j) rfl (x ⊗ₜ[R] y) ⊗ₜ[R] z)) =
      ιTensorObj X (tensorComplex Y Z) i (j + k) l (by omega)
        (x ⊗ₜ[R] ιTensorObj Y Z j k (j + k) rfl (y ⊗ₜ[R] z)) := by
  let F := curriedTensor (ModuleCat R)
  let c := ComplexShape.up ℤ
  have h := ι_mapBifunctorAssociatorX_hom (curriedAssociatorNatIso (ModuleCat R))
    X Y Z c c c i j k l hl
  rw [mapBifunctor₁₂.ι_eq (c₁ := c) (c₂ := c) (c₃ := c) F F X Y Z c c i j k
      (i + j) l rfl hl,
    mapBifunctor₂₃.ι_eq (c₁ := c) (c₂ := c) (c₃ := c) F F X Y Z c c c i j k
      (j + k) l rfl (show i + (j + k) = l by omega)] at h
  change (ιTensorObj X Y i j (i+j) rfl ▷ Z.X k) ≫
      ιTensorObj (tensorComplex X Y) Z (i+j) k l hl ≫ (α_ X Y Z).hom.f l =
    (α_ (X.X i) (Y.X j) (Z.X k)).hom ≫ (X.X i ◁ ιTensorObj Y Z j k (j+k) rfl) ≫
      ιTensorObj X (tensorComplex Y Z) i (j+k) l (by omega) at h
  have hh := ConcreteCategory.congr_hom h ((x ⊗ₜ[R] y) ⊗ₜ[R] z)
  simp only [ModuleCat.comp_apply] at hh
  exact hh

/-- The evaluation comparison, before imposing finiteness on the source of internal Hom. -/
def chainEvaluationComparison (P Y : Comp.{u} R) :
    tensorComplex Y (chainDual P) ⟶ internalHom P Y :=
  tensorHomEquiv (tensorComplex Y (chainDual P)) P Y
    ((α_ Y (chainDual P) P).hom ≫ Y ◁ chainEvaluation P ≫ (ρ_ Y).hom)

private theorem tensorMap_apply_at {X X' Y Y' : Comp.{u} R} (a : X ⟶ X') (b : Y ⟶ Y')
    {i j t : ℤ} (ht : i + j = t) (x : X.X i) (y : Y.X j) :
    (tensorMap a b).f t (ιTensorObj X Y i j t ht (x ⊗ₜ[R] y)) =
      ιTensorObj X' Y' i j t ht (a.f i x ⊗ₜ[R] b.f j y) := by
  subst t
  exact tensorMap_apply a b i j x y

private theorem comparison_apply_raw (P Y : Comp.{u} R) {i j k t l s : ℤ}
    (ht : j + k = t) (hl : i + t = l) (hs : k + i = s) (y : Y.X j) (f : (chainDual P).X k) (x : P.X i) :
    ((chainEvaluationComparison P Y).f t
      (ιTensorObj Y (chainDual P) j k t ht (y ⊗ₜ[R] f))).v i l hl x =
      (ρ_ Y).hom.f l (ιTensorObj Y (ringStalk R) j s l (by omega)
        (y ⊗ₜ[R] f.v i s (by omega) x)) := by
  subst s
  obtain rfl : l = t + i := by omega
  subst t
  rw [chainEvaluationComparison, tensorHomEquiv_apply]
  simp only [comp_f, ModuleCat.comp_apply]
  rw [assoc_apply]
  change (ρ_ Y).hom.f (j + k + i) ((tensorMap (𝟙 Y) (chainEvaluation P)).f _
    (ιTensorObj Y (tensorComplex (chainDual P) P) j (k + i) _ (by omega)
      (y ⊗ₜ[R] ιTensorObj (chainDual P) P k i (k+i) rfl (f ⊗ₜ[R] x)))) = _
  rw [tensorMap_apply_at, chainEvaluation_apply]
  rfl

/-- The matching summand acts by the ordinary evaluation of the homogeneous dual. -/
theorem chainEvaluationComparison_apply (P Y : Comp.{u} R) {i j k t : ℤ}
    (ht : j + k = t) (hk : i + k = 0) (y : Y.X j) (f : (chainDual P).X k) (x : P.X i) :
    ((chainEvaluationComparison P Y).f t
      (ιTensorObj Y (chainDual P) j k t ht (y ⊗ₜ[R] f))).v i j (by omega) x =
      chainDualTerm P hk f x • y := by
  rw [comparison_apply_raw P Y ht (show i + t = j by omega) (show k + i = 0 by omega),
    rightUnitor_hom_apply]
  rfl

/-- The other summands act by zero because the coefficient complex is a stalk. -/
theorem chainEvaluationComparison_apply_off (P Y : Comp.{u} R) {i j k t l : ℤ}
    (ht : j + k = t) (hl : i + t = l) (hk : i + k ≠ 0)
    (y : Y.X j) (f : (chainDual P).X k) (x : P.X i) :
    ((chainEvaluationComparison P Y).f t
      (ιTensorObj Y (chainDual P) j k t ht (y ⊗ₜ[R] f))).v i l hl x = 0 := by
  rw [comparison_apply_raw P Y ht hl rfl]
  have := ModuleCat.subsingleton_of_isZero (stalkIsZero (R := R) (n := k+i) (by omega))
  rw [Subsingleton.elim (f.v i (k + i) (add_comm i k) x) 0, TensorProduct.tmul_zero,
    map_zero, map_zero]

private theorem tensorTerm_ext {X Y : Comp.{u} R} {t : ℤ} {M : ModuleCat.{u} R}
    {f g : (tensorComplex X Y).X t ⟶ M}
    (h : ∀ (i j : ℤ) (ht : i + j = t) (x : X.X i) (y : Y.X j),
      f (ιTensorObj X Y i j t ht (x ⊗ₜ[R] y)) =
        g (ιTensorObj X Y i j t ht (x ⊗ₜ[R] y))) : f = g := by
  apply HomologicalComplex.mapBifunctor.hom_ext
    (K₁ := X) (K₂ := Y) (F := curriedTensor (ModuleCat R)) (c := .up ℤ)
  intro i j ht
  apply ModuleCat.hom_ext
  exact TensorProduct.ext' (h i j ht)

/-- Naturality of the comparison in the perfect factor and in the arbitrary target. -/
theorem chainEvaluationComparison_natural {P P' Y Y' : Comp.{u} R}
    (a : P' ⟶ P) (b : Y ⟶ Y') :
    tensorMap b (internalHomMap a (𝟙 (ringStalk R))) ≫ chainEvaluationComparison P' Y' =
      chainEvaluationComparison P Y ≫ internalHomMap a b := by
  apply HomologicalComplex.hom_ext
  intro t
  apply tensorTerm_ext
  intro j k ht y f
  apply Cochain.ext
  intro i l hl
  apply ModuleCat.hom_ext
  ext x : 1
  simp only [comp_f, ModuleCat.comp_apply, tensorMap_apply_at, internalHomMap_apply]
  by_cases hz : i + k = 0
  · have hj : j = l := by omega
    subst hj
    rw [chainEvaluationComparison_apply P' Y' ht hz, chainEvaluationComparison_apply P Y ht hz]
    simp only [chainDualTerm_apply, internalHomMap_apply, id_f, ModuleCat.id_apply]
    symm
    exact map_smul (b.f j).hom _ y
  · rw [chainEvaluationComparison_apply_off P' Y' ht hl hz,
      chainEvaluationComparison_apply_off P Y ht hl hz, map_zero]

private abbrev blockSource (P Y : Comp.{u} R) (t i : ℤ) :=
  Y.X (i+t) ⊗ (chainDual P).X (-i)

private def blockInclusion (P Y : Comp.{u} R) (t i : ℤ) :
    blockSource P Y t i →ₗ[R] (tensorComplex Y (chainDual P)).X t :=
  (ιTensorObj Y (chainDual P) (i+t) (-i) t (by omega)).hom

private def homProjection (P Y : Comp.{u} R) (t i : ℤ) :
    (internalHom P Y).X t →ₗ[R] (P.X i →ₗ[R] Y.X (i+t)) :=
  (LinearMap.proj i).comp (internalHomProduct P Y t).toLinearMap

private def blockEquiv (P Y : Comp.{u} R) (t i : ℤ)
    [Module.Finite R (P.X i)] [Module.Projective R (P.X i)] :
    blockSource P Y t i ≃ₗ[R] (P.X i →ₗ[R] Y.X (i+t)) :=
  (TensorProduct.congr (LinearEquiv.refl R (Y.X (i+t)))
      (chainDualTerm P (show i + -i = 0 by omega))).trans
    ((TensorProduct.comm R _ _).trans (dualTensorHomEquiv R (P.X i) (Y.X (i+t))))

private abbrev comparisonTerm (P Y : Comp.{u} R) (t : ℤ) :=
  (chainEvaluationComparison P Y).f t |>.hom

private theorem comparison_block (P Y : Comp.{u} R) (t i : ℤ)
    [Module.Finite R (P.X i)] [Module.Projective R (P.X i)]
    (z : blockSource P Y t i) :
    homProjection P Y t i (comparisonTerm P Y t (blockInclusion P Y t i z)) =
      blockEquiv P Y t i z := by
  change ((homProjection P Y t i).comp ((comparisonTerm P Y t).comp
      (blockInclusion P Y t i))) z = _
  suffices h : (homProjection P Y t i).comp ((comparisonTerm P Y t).comp
      (blockInclusion P Y t i)) = (blockEquiv P Y t i).toLinearMap by rw [h]; rfl
  apply TensorProduct.ext'
  intro y f
  ext x
  change ((chainEvaluationComparison P Y).f t
      (ιTensorObj Y (chainDual P) (i+t) (-i) t (by omega) (y ⊗ₜ[R] f))).v i (i+t) rfl x =
    chainDualTerm P (show i + -i = 0 by omega) f x • y
  exact chainEvaluationComparison_apply P Y (by omega) (by omega) y f x

private theorem comparison_block_off (P Y : Comp.{u} R) (t i j : ℤ) (hij : i ≠ j)
    (z : blockSource P Y t j) :
    homProjection P Y t i (comparisonTerm P Y t (blockInclusion P Y t j z)) = 0 := by
  change ((homProjection P Y t i).comp ((comparisonTerm P Y t).comp
      (blockInclusion P Y t j))) z = _
  suffices h : (homProjection P Y t i).comp ((comparisonTerm P Y t).comp
      (blockInclusion P Y t j)) = 0 by rw [h]; rfl
  apply TensorProduct.ext'
  intro y f
  ext x
  change ((chainEvaluationComparison P Y).f t
      (ιTensorObj Y (chainDual P) (j+t) (-j) t (by omega) (y ⊗ₜ[R] f))).v i (i+t) rfl x = 0
  exact chainEvaluationComparison_apply_off P Y (by omega) rfl (by omega) y f x

private def comparisonInverseTerm (P Y : Comp.{u} R) (t : ℤ) (s : Finset ℤ)
    [∀ i : ℤ, Module.Finite R (P.X i)] [∀ i : ℤ, Module.Projective R (P.X i)] :
    (internalHom P Y).X t →ₗ[R] (tensorComplex Y (chainDual P)).X t :=
  ∑ i ∈ s, (blockInclusion P Y t i).comp
    ((blockEquiv P Y t i).symm.toLinearMap.comp (homProjection P Y t i))

private theorem comparisonInverseTerm_apply (P Y : Comp.{u} R) (t : ℤ) (s : Finset ℤ)
    [∀ i : ℤ, Module.Finite R (P.X i)] [∀ i : ℤ, Module.Projective R (P.X i)]
    (f : (internalHom P Y).X t) :
    comparisonInverseTerm P Y t s f =
      ∑ i ∈ s, blockInclusion P Y t i ((blockEquiv P Y t i).symm (homProjection P Y t i f)) := by
  simp only [comparisonInverseTerm, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe]

private theorem comparisonTerm_bijective (P Y : Comp.{u} R) (t : ℤ)
    (s : Finset ℤ) (hs : ∀ i ∉ s, IsZero (P.X i))
    [∀ i : ℤ, Module.Finite R (P.X i)] [∀ i : ℤ, Module.Projective R (P.X i)] :
    Function.Bijective (comparisonTerm P Y t) := by
  classical
  let inv := comparisonInverseTerm P Y t s
  have hleft : inv.comp (comparisonTerm P Y t) = LinearMap.id := by
    have hblock (i : ℤ) (z : blockSource P Y t i) :
        inv (comparisonTerm P Y t (blockInclusion P Y t i z)) = blockInclusion P Y t i z := by
      by_cases hi : i ∈ s
      · rw [show inv = comparisonInverseTerm P Y t s from rfl, comparisonInverseTerm_apply,
          Finset.sum_eq_single_of_mem i hi]
        · rw [comparison_block, LinearEquiv.symm_apply_apply]
        · intro j _ hj
          rw [comparison_block_off P Y t j i hj, map_zero, map_zero]
      · have hz := ModuleCat.subsingleton_of_isZero (hs i hi)
        have hd : Subsingleton ((chainDual P).X (-i)) :=
          (chainDualTerm P (show i + -i = 0 by omega)).injective.subsingleton
        have hzero : Subsingleton (blockSource P Y t i) := by
          change Subsingleton (Y.X (i+t) ⊗[R] (chainDual P).X (-i))
          infer_instance
        rw [Subsingleton.elim z 0, map_zero, map_zero, map_zero]
    apply ModuleCat.hom_ext_iff.mp
    apply tensorTerm_ext
    intro j k ht y f
    generalize hh : -k = i at *
    have hj : j = i+t := by omega
    have hk : k = -i := by omega
    subst j
    subst k
    exact hblock i (y ⊗ₜ[R] f)
  have hright : Function.RightInverse inv (comparisonTerm P Y t) := by
    intro f
    apply (internalHomProduct P Y t).injective
    funext i
    change homProjection P Y t i (comparisonTerm P Y t (inv f)) = homProjection P Y t i f
    by_cases hi : i ∈ s
    · rw [show inv = comparisonInverseTerm P Y t s from rfl, comparisonInverseTerm_apply,
        map_sum, map_sum, Finset.sum_eq_single_of_mem i hi]
      · rw [comparison_block, LinearEquiv.apply_symm_apply]
      · intro j _ hj
        exact comparison_block_off P Y t i j hj.symm _
    · have := ModuleCat.subsingleton_of_isZero (hs i hi)
      exact Subsingleton.elim _ _
  exact ⟨(fun x y h => by
    have e := congrArg inv h
    exact (LinearMap.congr_fun hleft x).symm.trans (e.trans (LinearMap.congr_fun hleft y))),
    hright.surjective⟩

/-- The evaluation comparison is a chain isomorphism for a bounded finite projective model. -/
def chainEvaluationIso (P : Comp.{u} R) (hP : boundedFiniteProjectiveValue P) (Y : Comp.{u} R) :
    tensorComplex Y (chainDual P) ≅ internalHom P Y := by
  have hIso (n : ℤ) : IsIso ((chainEvaluationComparison P Y).f n) := by
    obtain ⟨⟨a,b,hb⟩, hf, hp⟩ := hP
    have := hf
    have := hp
    rw [ConcreteCategory.isIso_iff_bijective]
    exact comparisonTerm_bijective P Y n (Finset.Icc a b)
      (fun i hi => hb i (by
        simp only [Finset.mem_Icc, not_and_or, not_le] at hi
        exact hi))
  letI := HomologicalComplex.Hom.isIso_of_components (chainEvaluationComparison P Y)
  exact asIso (chainEvaluationComparison P Y)

theorem chainEvaluationIso_hom (P : Comp.{u} R) (hP : boundedFiniteProjectiveValue P)
    (Y : Comp.{u} R) : (chainEvaluationIso P hP Y).hom = chainEvaluationComparison P Y := rfl


/-- The coevaluation is the preimage of the identity under the evaluation comparison
and the tensor–Hom correspondence for the tensor unit. -/
def chainCoevaluation (P : Comp.{u} R) (hP : boundedFiniteProjectiveValue P) :
    ringStalk R ⟶ tensorComplex P (chainDual P) :=
  tensorHomEquiv (ringStalk R) P P (λ_ P).hom ≫ (chainEvaluationIso P hP P).inv

private theorem chainCoevaluation_comparison (P : Comp.{u} R) (hP : boundedFiniteProjectiveValue P) :
    chainCoevaluation P hP ≫ chainEvaluationComparison P P =
      tensorHomEquiv (ringStalk R) P P (λ_ P).hom := by
  rw [← chainEvaluationIso_hom P hP P, chainCoevaluation, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- The coevaluation evaluated at one is the cycle corresponding to the identity of (P). -/
theorem chainCoevaluation_cycle (P : Comp.{u} R) (hP : boundedFiniteProjectiveValue P) :
    (chainEvaluationComparison P P).f 0 ((chainCoevaluation P hP).f 0
      ((stalkZero (R := R)).inv 1)) = Cochain.ofHom (𝟙 P) := by
  have h := ConcreteCategory.congr_hom
    (congrArg (fun f : ringStalk R ⟶ internalHom P P => f.f 0)
      (chainCoevaluation_comparison P hP)) ((stalkZero (R := R)).inv 1)
  simp only [comp_f, ModuleCat.comp_apply] at h
  rw [h]
  apply Cochain.ext
  intro i j hij
  have hj : i = j := by omega
  subst hj
  apply ModuleCat.hom_ext
  ext x : 1
  change ((tensorHomEquiv (ringStalk R) P P (λ_ P).hom).f 0
    ((stalkZero (R := R)).inv 1)).v i i (add_zero i) x = x
  rw [curry_apply_at _ _ _ _ (zero_add i)]
  have hInv := ConcreteCategory.congr_hom
    (congrArg (fun f : P ⟶ P => f.f i) (λ_ P).inv_hom_id) x
  simp only [comp_f, ModuleCat.comp_apply, id_f] at hInv
  rw [leftUnitor_inv_apply] at hInv
  exact hInv

/-- The triangle identity on the original complex. -/
theorem chainEvaluation_triangle (P : Comp.{u} R) (hP : boundedFiniteProjectiveValue P) :
    chainCoevaluation P hP ▷ P ≫ (α_ P (chainDual P) P).hom ≫
        P ◁ chainEvaluation P ≫ (ρ_ P).hom = (λ_ P).hom := by
  apply (tensorHomEquiv (ringStalk R) P P).injective
  have h := tensorHomEquiv_natural (chainCoevaluation P hP) (𝟙 P) (𝟙 P)
    ((α_ P (chainDual P) P).hom ≫ P ◁ chainEvaluation P ≫ (ρ_ P).hom)
  rw [Category.comp_id, internalHomMap_id, Category.comp_id] at h
  exact h.trans (chainCoevaluation_comparison P hP)

-- To prove the second triangle, evaluate it against one further copy of the original
-- object. Interchange allows the two evaluation contractions to be performed in either order.
private theorem evaluation_rotate {C : Type*} [Category* C] [MonoidalCategory C]
    {P D : C} (ev : D ⊗ P ⟶ 𝟙_ C) (coev : 𝟙_ C ⟶ P ⊗ D) :
    ((ρ_ D).inv ≫ D ◁ coev ≫ (α_ D P D).inv ≫ ev ▷ D ≫ (λ_ D).hom) ▷ P ≫ ev =
      D ◁ ((λ_ P).inv ≫ coev ▷ P ≫ (α_ P D P).hom ≫ P ◁ ev ≫ (ρ_ P).hom) ≫ ev := by
  simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  calc
    _ = (ρ_ D).inv ▷ P ≫ (D ◁ coev) ▷ P ≫ (α_ D P D).inv ▷ P ≫
        (α_ (D ⊗ P) D P).hom ≫ (ev ▷ (D ⊗ P)) ≫ (𝟙_ C ◁ ev) ≫ (λ_ (𝟙_ C)).hom := by
      rw [leftUnitor_naturality]
      monoidal
    _ = (ρ_ D).inv ▷ P ≫ (D ◁ coev) ▷ P ≫ (α_ D P D).inv ▷ P ≫
        (α_ (D ⊗ P) D P).hom ≫ ((D ⊗ P) ◁ ev) ≫ (ev ▷ 𝟙_ C) ≫ (λ_ (𝟙_ C)).hom := by
      rw [whisker_exchange_assoc]
    _ = _ := by
      rw [unitors_equal, rightUnitor_naturality]
      monoidal

/-- The triangle identity on the dual complex. -/
theorem chainCoevaluation_triangle (P : Comp.{u} R) (hP : boundedFiniteProjectiveValue P) :
    (chainDual P) ◁ chainCoevaluation P hP ≫ (α_ (chainDual P) P (chainDual P)).inv ≫
      chainEvaluation P ▷ (chainDual P) = (ρ_ (chainDual P)).hom ≫ (λ_ (chainDual P)).inv := by
  let D := chainDual P
  let ev := chainEvaluation P
  let coev := chainCoevaluation P hP
  let h := (ρ_ D).inv ≫ D ◁ coev ≫ (α_ D P D).inv ≫ ev ▷ D ≫ (λ_ D).hom
  have he : h ▷ P ≫ ev = ev := by
    change ((ρ_ D).inv ≫ D ◁ coev ≫ (α_ D P D).inv ≫ ev ▷ D ≫ (λ_ D).hom) ▷ P ≫ ev = ev
    rw [evaluation_rotate]
    change D ◁ ((λ_ P).inv ≫ coev ▷ P ≫ (α_ P D P).hom ≫ P ◁ ev ≫ (ρ_ P).hom) ≫ ev = ev
    rw [show coev ▷ P ≫ (α_ P D P).hom ≫ P ◁ ev ≫ (ρ_ P).hom = (λ_ P).hom from
      chainEvaluation_triangle P hP, Iso.inv_hom_id, whiskerLeft_id, Category.id_comp]
  have hId : h = 𝟙 D := by
    have hc := tensorHomEquiv_natural h (𝟙 P) (𝟙 (ringStalk R)) ev
    change tensorHomEquiv D P (ringStalk R) (h ▷ P ≫ ev ≫ 𝟙 _) =
      h ≫ tensorHomEquiv D P (ringStalk R) ev ≫ internalHomMap (𝟙 P) (𝟙 _) at hc
    rw [Category.comp_id, he, internalHomMap_id, Category.comp_id] at hc
    have hid : tensorHomEquiv D P (ringStalk R) ev = 𝟙 D :=
      (tensorHomEquiv D P (ringStalk R)).apply_symm_apply _
    rw [hid, Category.comp_id] at hc
    exact hc.symm
  apply (cancel_epi (ρ_ D).inv).mp
  apply (cancel_mono (λ_ D).hom).mp
  dsimp only [h, D, coev, ev] at hId
  simpa only [D, Category.assoc, Iso.inv_hom_id, Iso.inv_hom_id_assoc, Category.comp_id] using hId

/-- Evaluation and coevaluation give the exact pairing in the category of cochain complexes. -/
@[instance_reducible] def chainExactPairing (P : Comp.{u} R) (hP : boundedFiniteProjectiveValue P) :
    ExactPairing P (chainDual P) where
  coevaluation' := chainCoevaluation P hP
  evaluation' := chainEvaluation P
  coevaluation_evaluation' := chainCoevaluation_triangle P hP
  evaluation_coevaluation' := by
    apply (cancel_mono (ρ_ P).hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      using chainEvaluation_triangle P hP


private theorem map_sign {M N : ModuleCat.{u} R} (f : M ⟶ N) (s : ℤˣ) (x : M) :
    f (s • x) = s • f x := by
  change f.hom (s • x) = s • f.hom x
  simp only [Units.smul_def, map_zsmul]

private def signedSwapTerm (X Y : Comp.{u} R) (t : ℤ) :
    (tensorComplex X Y).X t ⟶ (tensorComplex Y X).X t :=
  mapBifunctorDesc (K₁ := X) (K₂ := Y) (F := curriedTensor (ModuleCat R)) (c := .up ℤ)
    (j := t) fun i j (h : i+j=t) =>
      (i*j).negOnePow • ((TensorProduct.comm R (X.X i) (Y.X j)).toModuleIso.hom ≫
        ιTensorObj Y X j i t (by omega))

private theorem signedSwapTerm_apply (X Y : Comp.{u} R) {i j t : ℤ} (ht : i+j=t)
    (x : X.X i) (y : Y.X j) :
    signedSwapTerm X Y t (ιTensorObj X Y i j t ht (x ⊗ₜ[R] y)) =
      (i*j).negOnePow • ιTensorObj Y X j i t (by omega) (y ⊗ₜ[R] x) := by
  have h := ι_mapBifunctorDesc (K₁ := X) (K₂ := Y) (F := curriedTensor (ModuleCat R))
    (c := .up ℤ) (j := t)
    (fun a b (h : a+b=t) => (a*b).negOnePow •
      ((TensorProduct.comm R (X.X a) (Y.X b)).toModuleIso.hom ≫
        ιTensorObj Y X b a t (by omega))) i j ht
  exact ConcreteCategory.congr_hom h (x ⊗ₜ[R] y)

private def signedSwap (X Y : Comp.{u} R) : tensorComplex X Y ⟶ tensorComplex Y X where
  f := signedSwapTerm X Y
  comm' t l hl := by
    change t+1=l at hl
    apply tensorTerm_ext
    intro i j ht x y
    simp only [ModuleCat.comp_apply]
    rw [signedSwapTerm_apply, map_sign, tensor_d_apply j i t l (by omega) hl,
      tensor_d_apply i j t l ht hl, map_add, map_sign, signedSwapTerm_apply, signedSwapTerm_apply,
      smul_add, smul_smul, smul_smul]
    have h₁ : ((i+1)*j).negOnePow = (i*j).negOnePow * j.negOnePow := by
      rw [add_mul, one_mul, Int.negOnePow_add]
    have h₂ : i.negOnePow * (i*(j+1)).negOnePow = (i*j).negOnePow := by
      rw [← Int.negOnePow_add, show i + i*(j+1) = i*j + 2*i by ring, Int.negOnePow_add,
        Int.negOnePow_two_mul, mul_one]
    rw [h₁, h₂, add_comm]

/-- The signed biduality map is adjoint to evaluation after the Koszul interchange. -/
def chainBidual (P : Comp.{u} R) : P ⟶ chainDual (chainDual P) :=
  tensorHomEquiv P (chainDual P) (ringStalk R)
    (signedSwap P (chainDual P) ≫ chainEvaluation P)

/-- On homogeneous elements biduality is signed evaluation. -/
theorem chainBidual_apply (P : Comp.{u} R) {i j t : ℤ} (ht : j+i=t)
    (x : P.X i) (f : (chainDual P).X j) :
    ((chainBidual P).f i x).v j t ht f = (i*j).negOnePow • f.v i t (by omega) x := by
  have h : t = i+j := by omega
  subst h
  rw [chainBidual, tensorHomEquiv_apply, comp_f, ModuleCat.comp_apply]
  change (chainEvaluation P).f _ (signedSwapTerm P (chainDual P) _
    (ιTensorObj P (chainDual P) i j _ _ (x ⊗ₜ[R] f))) = _
  rw [signedSwapTerm_apply, map_sign, chainEvaluation_apply]

/-- The signed double dual is a chain isomorphism for finite projective terms. -/
def chainBidualIso (P : Comp.{u} R) (hP : boundedFiniteProjectiveValue P) :
    P ≅ chainDual (chainDual P) := by
  have hIso (i : ℤ) : IsIso ((chainBidual P).f i) := by
    have := hP.2.1 i
    have := hP.2.2 i
    let e := chainDualTerm P (show i + -i = 0 by omega)
    let e' := chainDualTerm (chainDual P) (show -i+i=0 by omega)
    let b := (Module.evalEquiv R (P.X i)).trans (e.dualMap.trans e'.symm)
    have hb (x : P.X i) : (chainBidual P).f i x = (i*(-i)).negOnePow • b x := by
      apply e'.injective
      ext f
      change chainDualTerm (chainDual P) (show -i+i=0 by omega) ((chainBidual P).f i x) f =
        (e' ((i*(-i)).negOnePow • b x)) f
      rw [chainDualTerm_apply, chainBidual_apply, map_sign]
      change (i*(-i)).negOnePow • e f x = _
      rw [show e' ((i*(-i)).negOnePow • b x) = (i*(-i)).negOnePow • e' (b x) from
        by simp only [Units.smul_def, map_zsmul]]
      have he : e' (b x) = e.dualMap (Module.evalEquiv R (P.X i) x) :=
        e'.apply_symm_apply _
      rw [he]
      rfl
    rw [ConcreteCategory.isIso_iff_bijective]
    have hsign : Function.Bijective (fun x : (chainDual (chainDual P)).X i =>
        (i*(-i)).negOnePow • x) :=
      ⟨fun x y h => by
        have h' := congrArg (fun z : (chainDual (chainDual P)).X i =>
          (i*(-i)).negOnePow⁻¹ • z) h
        simpa only [inv_smul_smul] using h',
       fun y => ⟨(i*(-i)).negOnePow⁻¹ • y, smul_inv_smul _ _⟩⟩
    have h := hsign.comp b.bijective
    convert h using 1
    funext x
    exact hb x
  letI := HomologicalComplex.Hom.isIso_of_components (chainBidual P)
  exact asIso (chainBidual P)

theorem chainBidualIso_hom (P : Comp.{u} R) (hP : boundedFiniteProjectiveValue P) :
    (chainBidualIso P hP).hom = chainBidual P := rfl

/-- The canonical comparison and signed duality data on the ordinary cochain models. -/
theorem perfectChainDuality : Specs.DerivedFormalization.PerfectChainEvaluation.chainDualityType := by
  intro R inst
  refine ⟨chainEvaluation, chainEvaluationComparison, chainCoevaluation, chainBidual,
    chainEvaluation_apply, chainEvaluationComparison_apply, chainEvaluationComparison_apply_off,
    chainEvaluationComparison_natural, ?_, chainCoevaluation_cycle, chainEvaluation_triangle,
    chainCoevaluation_triangle, chainBidual_apply, ?_⟩
  · intro P hP Y
    exact (chainEvaluationIso P hP Y).isIso_hom
  · intro P hP
    exact (chainBidualIso P hP).isIso_hom

end
end DerivedFormalization
