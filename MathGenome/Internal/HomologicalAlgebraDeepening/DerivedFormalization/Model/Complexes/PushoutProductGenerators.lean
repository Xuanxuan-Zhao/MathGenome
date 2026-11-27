import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Model.Complexes.PushoutProductGenerators
import Mathlib.Algebra.Homology.ShortComplex.Pushout
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Model.Complexes.Cofibrations
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CochainModels
import Mathlib.Algebra.Homology.BifunctorFlip
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Batteries.Tactic.OpenPrivate

open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
open scoped TensorProduct ZeroObject

universe u

namespace DerivedFormalization.Model.Complexes

open Specs.ComplexPushoutProductGenerators
open Specs.ComplexCellFactorization (diskGenerator sphereGenerator)

noncomputable section

variable {A : Type u} [CommRing A]

set_option backward.isDefEq.respectTransparency false

/-- The pushout product for the ordinary signed tensor on cochain complexes. -/
def pushoutProduct {X Y U V : Cochains A} (a : X ⟶ Y) (b : U ⟶ V) :
    source a b ⟶ tensorComplex Y V := pushoutProductValue a b

private abbrev T (X Y : Cochains A) := tensorComplex X Y

private abbrev G (X Y : Cochains A) := ∀ k, X.X k ⟶ Y.X k

private abbrev gid (X : Cochains A) : G X X := fun k ↦ 𝟙 (X.X k)

private lemma tensor_ext {X Y : Cochains A} {k : ℤ} {M : ModuleCat A}
    {f g : (T X Y).X k ⟶ M}
    (h : ∀ i j (e : i + j = k) (x : X.X i) (y : Y.X j),
      f (homogeneousTensor e x y) = g (homogeneousTensor e x y)) : f = g := by
  apply mapBifunctor.hom_ext (K₁ := X) (K₂ := Y) (F := curriedTensor (ModuleCat A))
    (c := ComplexShape.up ℤ)
  intro i j e
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  exact h i j e x y

/-- The tensor of maps of underlying graded modules. -/
private def gt {X Y U V : Cochains A} (a : G X Y) (b : G U V) : G (T X U) (T Y V) :=
  fun k ↦ mapBifunctorDesc (K₁ := X) (K₂ := U) (F := curriedTensor (ModuleCat A))
    (c := ComplexShape.up ℤ) fun i j e ↦ (a i ⊗ₘ b j) ≫ ιTensorObj Y V i j k e

@[simp] private lemma gt_apply {X Y U V : Cochains A} (a : G X Y) (b : G U V)
    {i j k : ℤ} (e : i + j = k) (x : X.X i) (y : U.X j) :
    gt a b k (homogeneousTensor e x y) = homogeneousTensor e (a i x) (b j y) := by
  have h := ι_mapBifunctorDesc (K₁ := X) (K₂ := U) (F := curriedTensor (ModuleCat A))
    (c := ComplexShape.up ℤ)
    (f := fun i j e ↦ (a i ⊗ₘ b j) ≫ ιTensorObj Y V i j k e) i j e
  have hh := ConcreteCategory.congr_hom h (x ⊗ₜ[A] y)
  change gt a b k (homogeneousTensor e x y) =
    ιTensorObj Y V i j k e ((a i ⊗ₘ b j) (x ⊗ₜ[A] y)) at hh
  rw [ModuleCat.MonoidalCategory.tensorHom_tmul] at hh
  exact hh

private lemma tensorMap_f {X Y U V : Cochains A} (a : X ⟶ Y) (b : U ⟶ V) (k : ℤ) :
    (tensorMap a b).f k = gt a.f b.f k := by
  apply tensor_ext
  intro i j e x y
  subst k
  rw [gt_apply, tensorMap_apply]

private lemma gt_comp {X Y Z U V W : Cochains A} (a : G X Y) (b : G U V)
    (c : G Y Z) (d : G V W) (k : ℤ) :
    gt a b k ≫ gt c d k = gt (fun i ↦ a i ≫ c i) (fun j ↦ b j ≫ d j) k := by
  apply tensor_ext
  intro i j e x y
  simp only [ModuleCat.comp_apply, gt_apply]

private lemma gt_id (X U : Cochains A) (k : ℤ) :
    gt (gid X) (gid U) k = 𝟙 _ := by
  change gt (Hom.f (𝟙 X)) (Hom.f (𝟙 U)) k = _
  rw [← tensorMap_f, tensorMap_id]
  rfl

private lemma gt_zero_left {X Y U V : Cochains A} (b : G U V) (k : ℤ) :
    gt (fun i ↦ (0 : X.X i ⟶ Y.X i)) b k = 0 := by
  apply tensor_ext
  intro i j e x y
  simp [homogeneousTensor]

private lemma gt_zero_right {X Y U V : Cochains A} (a : G X Y) (k : ℤ) :
    gt a (fun j ↦ (0 : U.X j ⟶ V.X j)) k = 0 := by
  apply tensor_ext
  intro i j e x y
  simp [homogeneousTensor]

private lemma gt_add_left {X Y U V : Cochains A} (a c : G X Y) (b : G U V) (k : ℤ) :
    gt (fun i ↦ a i + c i) b k = gt a b k + gt c b k := by
  apply tensor_ext
  intro i j e x y
  simp [homogeneousTensor, TensorProduct.add_tmul]

private lemma gt_add_right {X Y U V : Cochains A} (a : G X Y) (b d : G U V) (k : ℤ) :
    gt a (fun i ↦ b i + d i) k = gt a b k + gt a d k := by
  apply tensor_ext
  intro i j e x y
  simp [homogeneousTensor, TensorProduct.tmul_add]

private lemma product_inl {X Y U V : Cochains A} (a : X ⟶ Y) (b : U ⟶ V) :
    pushout.inl (leftLeg a b) (rightLeg a b) ≫ pushoutProduct a b = tensorMap (𝟙 Y) b :=
  pushout.inl_desc _ _ _

private lemma product_inr {X Y U V : Cochains A} (a : X ⟶ Y) (b : U ⟶ V) :
    pushout.inr (leftLeg a b) (rightLeg a b) ≫ pushoutProduct a b = tensorMap a (𝟙 V) :=
  pushout.inr_desc _ _ _

private theorem degreePushout {X Y U V : Cochains A} (a : X ⟶ Y) (b : U ⟶ V) (k : ℤ) :
    IsPushout ((leftLeg a b).f k) ((rightLeg a b).f k)
      ((pushout.inl (leftLeg a b) (rightLeg a b)).f k)
      ((pushout.inr (leftLeg a b) (rightLeg a b)).f k) :=
  (eval (ModuleCat.{u} A) (ComplexShape.up ℤ) k).map_isPushout
    (IsPushout.of_hasPushout (leftLeg a b) (rightLeg a b))

/-- A degreewise direct-sum decomposition with maps from a short complex. -/
private structure GradedSplit {X Y Z : Cochains A} (f : X ⟶ Y) (q : Y ⟶ Z) where
  r : G Y X
  s : G Z Y
  fr (k : ℤ) : f.f k ≫ r k = 𝟙 _
  fq (k : ℤ) : f.f k ≫ q.f k = 0
  sr (k : ℤ) : s k ≫ r k = 0
  sq (k : ℤ) : s k ≫ q.f k = 𝟙 _
  total (k : ℤ) : r k ≫ f.f k + q.f k ≫ s k = 𝟙 _

private def GradedSplit.isColimit {X Y Z : Cochains A} {f : X ⟶ Y} {q : Y ⟶ Z}
    (S : GradedSplit f q) :
    IsColimit (CokernelCofork.ofπ q (by ext k : 1; exact S.fq k : f ≫ q = 0)) := by
  refine isColimitAux _ (fun c ↦ ?_) (fun c ↦ ?_) (fun c m hm ↦ ?_)
  · refine
      { f := fun k ↦ S.s k ≫ c.π.f k
        comm' := fun i j _ ↦ ?_ }
    have : Epi (q.f i) := SplitEpi.epi ⟨S.s i, S.sq i⟩
    apply (cancel_epi (q.f i)).1
    have h (k : ℤ) : q.f k ≫ S.s k ≫ c.π.f k = c.π.f k := by
      have hz : f.f k ≫ c.π.f k = 0 := congrArg (fun t : X ⟶ c.pt ↦ t.f k) c.condition
      calc
        _ = (S.r k ≫ f.f k + q.f k ≫ S.s k) ≫ c.π.f k := by
          rw [Preadditive.add_comp, Category.assoc, hz, comp_zero, zero_add, Category.assoc]
        _ = _ := by rw [S.total, Category.id_comp]
    change q.f i ≫ (S.s i ≫ c.π.f i) ≫ c.pt.d i j =
      q.f i ≫ Z.d i j ≫ S.s j ≫ c.π.f j
    rw [← Category.assoc, h i, q.comm_assoc, h j, c.π.comm]
  · apply HomologicalComplex.hom_ext
    intro k
    change q.f k ≫ S.s k ≫ c.π.f k = c.π.f k
    have hz : f.f k ≫ c.π.f k = 0 := congrArg (fun t : X ⟶ c.pt ↦ t.f k) c.condition
    calc
      _ = (S.r k ≫ f.f k + q.f k ≫ S.s k) ≫ c.π.f k := by
        rw [Preadditive.add_comp, Category.assoc, hz, comp_zero, zero_add, Category.assoc]
      _ = _ := by rw [S.total, Category.id_comp]
  · apply HomologicalComplex.hom_ext
    intro k
    have hh := congrArg (fun t : Y ⟶ c.pt ↦ t.f k) hm
    change q.f k ≫ m.f k = c.π.f k at hh
    change m.f k = S.s k ≫ c.π.f k
    rw [← hh, ← Category.assoc, S.sq, Category.id_comp]

private lemma gt_normalize {X Y Z U V W : Cochains A} (a : G X Y) (b : G U V)
    (c : G Y Z) (d : G V W) (k : ℤ) (ac : G X Z) (bd : G U W)
    (h₁ : ∀ i, a i ≫ c i = ac i) (h₂ : ∀ j, b j ≫ d j = bd j) :
    gt a b k ≫ gt c d k = gt ac bd k := by
  rw [gt_comp, show (fun i ↦ a i ≫ c i) = ac from funext h₁,
    show (fun j ↦ b j ≫ d j) = bd from funext h₂]

private def GradedSplit.tensorPushout {X Y Z U V W : Cochains A}
    {a : X ⟶ Y} {q : Y ⟶ Z} {b : U ⟶ V} {p : V ⟶ W}
    (S : GradedSplit a q) (D : GradedSplit b p) :
    GradedSplit (pushoutProduct a b) (tensorMap q p) := by
  let I₁ := pushout.inl (leftLeg a b) (rightLeg a b)
  let I₂ := pushout.inr (leftLeg a b) (rightLeg a b)
  let c : G V V := fun j ↦ p.f j ≫ D.s j
  let r : G (T Y V) (source a b) := fun k ↦
    gt (gid Y) D.r k ≫ I₁.f k + gt S.r c k ≫ I₂.f k
  have h₁ (k : ℤ) : I₁.f k ≫ (pushoutProduct a b).f k = gt (gid Y) b.f k := by
    exact (congrArg (fun t : T Y U ⟶ T Y V ↦ t.f k) (product_inl a b)).trans
      (tensorMap_f (𝟙 Y) b k)
  have h₂ (k : ℤ) : I₂.f k ≫ (pushoutProduct a b).f k = gt a.f (gid V) k := by
    exact (congrArg (fun t : T X V ⟶ T Y V ↦ t.f k) (product_inr a b)).trans
      (tensorMap_f a (𝟙 V) k)
  have hbc (j : ℤ) : b.f j ≫ c j = 0 := by
    simp [c, ← Category.assoc, D.fq]
  have hsc (j : ℤ) : D.s j ≫ c j = D.s j := by
    simp [c, ← Category.assoc, D.sq]
  refine ⟨r, gt S.s D.s, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    apply (degreePushout a b k).hom_ext
    · change I₁.f k ≫ ((pushoutProduct a b).f k ≫ r k) = _
      simp only [r]
      rw [← Category.assoc, h₁, Preadditive.comp_add, ← Category.assoc, ← Category.assoc]
      rw [gt_normalize _ _ _ _ k (gid Y) (gid U) (fun i ↦ Category.id_comp _) D.fr,
        gt_id, Category.id_comp,
        gt_normalize _ _ _ _ k S.r (fun _ ↦ 0) (fun i ↦ Category.id_comp _) hbc,
        gt_zero_right, zero_comp, add_zero, Category.comp_id]
    · change I₂.f k ≫ ((pushoutProduct a b).f k ≫ r k) = _
      simp only [r]
      rw [← Category.assoc, h₂, Preadditive.comp_add, ← Category.assoc, ← Category.assoc]
      rw [gt_normalize _ _ _ _ k a.f D.r (fun i ↦ Category.comp_id _) (fun j ↦ Category.id_comp _),
        gt_normalize _ _ _ _ k (gid X) c S.fr (fun j ↦ Category.id_comp _),
        Category.comp_id]
      have hc := congrArg (fun t : T X U ⟶ source a b ↦ t.f k)
        (pushout.condition (f := leftLeg a b) (g := rightLeg a b))
      change (tensorMap a (𝟙 U)).f k ≫ I₁.f k =
        (tensorMap (𝟙 X) b).f k ≫ I₂.f k at hc
      rw [tensorMap_f, tensorMap_f] at hc
      change gt a.f (gid U) k ≫ I₁.f k = gt (gid X) b.f k ≫ I₂.f k at hc
      have hh : gt a.f D.r k ≫ I₁.f k = gt (gid X) (fun j ↦ D.r j ≫ b.f j) k ≫ I₂.f k := by
        have H₁ : gt (gid X) D.r k ≫ gt a.f (gid U) k = gt a.f D.r k :=
          gt_normalize _ _ _ _ k _ _ (fun _ ↦ Category.id_comp _) (fun _ ↦ Category.comp_id _)
        have H₂ : gt (gid X) D.r k ≫ gt (gid X) b.f k =
            gt (gid X) (fun j ↦ D.r j ≫ b.f j) k :=
          gt_normalize _ _ _ _ k _ _ (fun _ ↦ Category.id_comp _) (fun _ ↦ rfl)
        rw [← H₁, ← H₂, Category.assoc, Category.assoc, hc]
      rw [hh, ← Preadditive.add_comp, ← gt_add_right]
      rw [show (fun j ↦ D.r j ≫ b.f j + c j) = (gid V) from funext D.total,
        gt_id, Category.id_comp]
  · intro k
    rw [tensorMap_f]
    apply (degreePushout a b k).hom_ext
    · change I₁.f k ≫ ((pushoutProduct a b).f k ≫ _) = I₁.f k ≫ 0
      rw [← Category.assoc, h₁, gt_normalize _ _ _ _ k q.f (fun _ ↦ 0)
        (fun _ ↦ Category.id_comp _) D.fq, gt_zero_right, comp_zero]
    · change I₂.f k ≫ ((pushoutProduct a b).f k ≫ _) = I₂.f k ≫ 0
      rw [← Category.assoc, h₂, gt_normalize _ _ _ _ k (fun _ ↦ 0) p.f
        S.fq (fun _ ↦ Category.id_comp _), gt_zero_left, comp_zero]
  · intro k
    dsimp only [r]
    rw [Preadditive.comp_add, ← Category.assoc, ← Category.assoc]
    rw [gt_normalize _ _ _ _ k S.s (fun _ ↦ 0) (fun _ ↦ Category.comp_id _) D.sr,
      gt_zero_right, gt_normalize _ _ _ _ k (fun _ ↦ 0) D.s S.sr hsc,
      gt_zero_left, zero_comp, zero_comp, add_zero]
  · intro k
    rw [tensorMap_f, gt_normalize _ _ _ _ k (gid Z) (gid W) S.sq D.sq, gt_id]
  · intro k
    dsimp only [r]
    rw [Preadditive.add_comp, Category.assoc, Category.assoc, h₁, h₂, tensorMap_f]
    rw [gt_normalize _ _ _ _ k (gid Y) (fun j ↦ D.r j ≫ b.f j) (fun _ ↦ Category.id_comp _) (fun _ ↦ rfl),
      gt_normalize _ _ _ _ k (fun i ↦ S.r i ≫ a.f i) c (fun _ ↦ rfl) (fun _ ↦ Category.comp_id _),
      gt_comp]
    rw [add_assoc, ← gt_add_left,
      show (fun i ↦ S.r i ≫ a.f i + q.f i ≫ S.s i) = (gid Y) from funext S.total,
      ← gt_add_right,
      show (fun j ↦ D.r j ≫ b.f j + c j) = (gid V) from funext D.total, gt_id]

open private iGeneratorUpperIsIso sphereDegreeIsZero diskDegreeIsZero diskContraction
  from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Model.Complexes.CellFactorization

private abbrev Rmod (A : Type u) [CommRing A] := ModuleCat.of A A

private def sphereBasis (n : ℤ) : (sphere A n).X n ≅ Rmod A :=
  singleObjXSelf (ComplexShape.up ℤ) n (Rmod A)

private def diskLower (n : ℤ) : (disk A n).X n ≅ Rmod A :=
  doubleXIso₀ (𝟙 (Rmod A)) (ComplexShape.up_mk n (n + 1) rfl)

private def diskUpper (n : ℤ) : (disk A n).X (n + 1) ≅ Rmod A :=
  doubleXIso₁ (𝟙 (Rmod A)) (ComplexShape.up_mk n (n + 1) rfl) (by omega)

private lemma disk_d (n : ℤ) :
    (disk A n).d n (n + 1) = (diskLower n).hom ≫ (diskUpper n).inv := by
  change (double (𝟙 (Rmod A)) (ComplexShape.up_mk n (n + 1) rfl)).d n (n + 1) = _
  rw [double_d _ _ (by omega : n ≠ n + 1), Category.id_comp]
  rfl

private lemma disk_d_generator (n : ℤ) :
    (disk A n).d n (n + 1) (diskGenerator A n) = (diskUpper n).inv (1 : A) := by
  rw [disk_d]
  change (diskUpper n).inv ((diskLower n).hom ((diskLower n).inv (1 : A))) = _
  simp

private lemma diskHomEquiv_apply_generator {X : Cochains A} (n : ℤ)
    (f : disk A n ⟶ X) : diskHomEquiv n f = f.f n (diskGenerator A n) := rfl

private lemma sphereHomEquiv_apply_generator {X : Cochains A} (n : ℤ)
    (f : sphere A n ⟶ X) :
    (sphereHomEquiv n f).val = f.f n (sphereGenerator A n) := rfl

private lemma commute_apply {X Y : Cochains A} (f : X ⟶ Y) (i j : ℤ) (x : X.X i) :
    Y.d i j (f.f i x) = f.f j (X.d i j x) :=
  ConcreteCategory.congr_hom (f.comm i j) x

private lemma disk_d_generator_eq (n : ℤ) :
    (disk A n).d n (n + 1) (diskGenerator A n) =
      (iGenerator A n).f (n + 1) (sphereGenerator A (n + 1)) := by
  have h := sphereHomEquiv_iGenerator_comp n (𝟙 (disk A n))
  rw [sphereHomEquiv_comp, sphereHomEquiv_apply_generator, diskHomEquiv_apply_generator] at h
  change _ = (disk A n).d n (n + 1) ((𝟙 ((disk A n).X n)) (diskGenerator A n)) at h
  rw [ModuleCat.id_apply] at h
  exact h.symm

private def diskQuotient (n : ℤ) : disk A n ⟶ sphere A n :=
  mkHomToSingle (diskLower n).hom fun k h ↦ by
    have hkn : k + 1 = n := h
    change (double (𝟙 (Rmod A)) (ComplexShape.up_mk n (n + 1) rfl)).d k n ≫ _ = 0
    rw [double_d_eq_zero₀ _ _ _ _ (by omega : k ≠ n)]
    exact zero_comp

private lemma diskQuotient_f (n : ℤ) :
    (diskQuotient (A := A) n).f n = (diskLower n).hom ≫ (sphereBasis n).inv :=
  mkHomToSingle_f _ _

private lemma diskQuotient_apply (n : ℤ) :
    (diskQuotient (A := A) n).f n (diskGenerator A n) = sphereGenerator A n := by
  rw [diskQuotient_f]
  change (sphereBasis n).inv ((diskLower n).hom ((diskLower n).inv (1 : A))) =
    (sphereBasis n).inv 1
  simp

private def iSplit (n : ℤ) : GradedSplit (iGenerator A n) (diskQuotient n) := by
  letI : IsIso ((iGenerator A n).f (n + 1)) := iGeneratorUpperIsIso n
  letI : IsIso ((diskQuotient (A := A) n).f n) := by rw [diskQuotient_f]; infer_instance
  let r : G (disk A n) (sphere A (n + 1)) := fun k ↦
    if h : k = n + 1 then h.symm ▸ inv ((iGenerator A n).f (n + 1)) else 0
  let s : G (sphere A n) (disk A n) := fun k ↦
    if h : k = n then h.symm ▸ inv ((diskQuotient (A := A) n).f n) else 0
  refine ⟨r, s, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    by_cases h : k = n + 1
    · subst k
      simp [r]
    · exact (sphereDegreeIsZero (n + 1) k h).eq_of_src _ _
  · intro k
    by_cases h : k = n
    · subst k
      exact (sphereDegreeIsZero (n + 1) n (by omega)).eq_of_src _ _
    · exact (sphereDegreeIsZero n k h).eq_of_tgt _ _
  · intro k
    by_cases h : k = n
    · subst k
      exact (sphereDegreeIsZero (n + 1) n (by omega)).eq_of_tgt _ _
    · exact (sphereDegreeIsZero n k h).eq_of_src _ _
  · intro k
    by_cases h : k = n
    · subst k
      simp [s]
    · exact (sphereDegreeIsZero n k h).eq_of_src _ _
  · intro k
    by_cases h : k = n
    · subst k
      simp [r, s, show n ≠ n + 1 by omega]
    · by_cases h' : k = n + 1
      · subst k
        simp [r, s, show n + 1 ≠ n by omega]
      · exact (diskDegreeIsZero n k h h').eq_of_src _ _

private def jSplit (m : ℤ) : GradedSplit (jGenerator A m) (𝟙 (disk A m)) := by
  have h (k : ℤ) : IsZero ((0 : Cochains A).X k) :=
    (eval (ModuleCat.{u} A) (ComplexShape.up ℤ) k).map_isZero (isZero_zero _)
  refine ⟨fun _ ↦ 0, gid _, fun k ↦ (h k).eq_of_src _ _, fun k ↦ (h k).eq_of_src _ _,
    fun k ↦ (h k).eq_of_tgt _ _, ?_, ?_⟩
  · intro k
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
    simp
  · intro k
    change 0 ≫ _ + 𝟙 _ ≫ 𝟙 _ = 𝟙 _
    simp

private lemma GradedSplit.zero {X Y Z : Cochains A} {f : X ⟶ Y} {q : Y ⟶ Z}
    (S : GradedSplit f q) : f ≫ q = 0 :=
  HomologicalComplex.hom_ext _ _ S.fq

private lemma GradedSplit.splitMono {X Y Z : Cochains A} {f : X ⟶ Y} {q : Y ⟶ Z}
    (S : GradedSplit f q) (k : ℤ) : IsSplitMono (f.f k) :=
  IsSplitMono.mk' ⟨S.r k, S.fr k⟩

private def GradedSplit.cokernelIso {X Y Z : Cochains A} {f : X ⟶ Y} {q : Y ⟶ Z}
    (S : GradedSplit f q) : cokernel f ≅ Z :=
  (cokernelIsCokernel f).coconePointUniqueUpToIso S.isColimit

private lemma GradedSplit.cokernelIso_apply {X Y Z : Cochains A} {f : X ⟶ Y} {q : Y ⟶ Z}
    (S : GradedSplit f q) : cokernel.π f ≫ S.cokernelIso.hom = q := by
  exact (cokernelIsCokernel f).comp_coconePointUniqueUpToIso_hom S.isColimit WalkingParallelPair.one

private lemma GradedSplit.shortExact {X Y Z : Cochains A} {f : X ⟶ Y} {q : Y ⟶ Z}
    (S : GradedSplit f q) : (ShortComplex.mk f q S.zero).ShortExact := by
  have hm (k : ℤ) : Mono (f.f k) := SplitMono.mono ⟨S.r k, S.fr k⟩
  exact ShortComplex.ShortExact.mk'
    ((ShortComplex.mk f q S.zero).exact_of_g_is_cokernel S.isColimit)
    (mono_of_mono_f f hm) (epi_of_isColimit_cofork S.isColimit)

private lemma tensorZeroLeft {M N : ModuleCat.{u} A} (h : IsZero M) :
    IsZero (M ⊗ N) :=
  (tensorRight N).map_isZero h

private lemma tensorZeroRight {M N : ModuleCat.{u} A} (h : IsZero N) :
    IsZero (M ⊗ N) :=
  (tensorLeft M).map_isZero h

private lemma tensorDegreeZero (X Y : Cochains A) (k : ℤ)
    (h : ∀ i j, i + j = k → IsZero (X.X i ⊗ Y.X j)) :
    IsZero ((T X Y).X k) := by
  rw [IsZero.iff_id_eq_zero]
  apply mapBifunctor.hom_ext (K₁ := X) (K₂ := Y) (F := curriedTensor (ModuleCat A))
    (c := ComplexShape.up ℤ)
  intro i j e
  exact (h i j e).eq_of_src _ _

private def tensorDegreeIso (X Y : Cochains A) (i j k : ℤ) (e : i + j = k)
    (h : ∀ a b, a + b = k → (a ≠ i ∨ b ≠ j) → IsZero (X.X a ⊗ Y.X b)) :
    X.X i ⊗ Y.X j ≅ (T X Y).X k := by
  let p (a b : ℤ) : X.X a ⊗ Y.X b ⟶ X.X i ⊗ Y.X j :=
    if ha : a = i then
      if hb : b = j then eqToHom (by rw [ha, hb]) else 0
    else 0
  let r : (T X Y).X k ⟶ X.X i ⊗ Y.X j :=
    mapBifunctorDesc (K₁ := X) (K₂ := Y) (F := curriedTensor (ModuleCat A))
      (c := ComplexShape.up ℤ) (fun a b _ ↦ p a b)
  have hr (a b : ℤ) (hab : a + b = k) :
      ιTensorObj X Y a b k hab ≫ r = p a b :=
    ι_mapBifunctorDesc (K₁ := X) (K₂ := Y) (F := curriedTensor (ModuleCat A))
      (c := ComplexShape.up ℤ) (f := fun a b _ ↦ p a b) a b hab
  have hi : ιTensorObj X Y i j k e ≫ r = 𝟙 _ := by rw [hr]; simp [p]
  refine ⟨ιTensorObj X Y i j k e, r, hi, ?_⟩
  apply mapBifunctor.hom_ext (K₁ := X) (K₂ := Y) (F := curriedTensor (ModuleCat A))
    (c := ComplexShape.up ℤ)
  intro a b hab
  change a + b = k at hab
  change ιTensorObj X Y a b k hab ≫ r ≫ ιTensorObj X Y i j k e =
    ιTensorObj X Y a b k hab ≫ 𝟙 _
  by_cases ha : a = i
  · subst a
    have hb : b = j := by omega
    subst b
    rw [← Category.assoc, hi, Category.id_comp, Category.comp_id]
  · exact (h a b hab (.inl ha)).eq_of_src _ _

private lemma hom_eq_of_regular {M N : ModuleCat.{u} A} (e : Rmod A ≅ M)
    {f g : M ⟶ N} (h : f (e.hom (1 : A)) = g (e.hom (1 : A))) : f = g := by
  apply (cancel_epi e.hom).1
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  exact h

private def rankOneTensorIso {X Y : Cochains A} {i j k : ℤ} (e : i + j = k)
    (a : Rmod A ≅ X.X i) (b : Rmod A ≅ Y.X j)
    (h : ∀ i' j', i' + j' = k → (i' ≠ i ∨ j' ≠ j) → IsZero (X.X i' ⊗ Y.X j')) :
    Rmod A ≅ (T X Y).X k :=
  (λ_ (Rmod A)).symm ≪≫ (a ⊗ᵢ b) ≪≫ tensorDegreeIso X Y i j k e h

private lemma rankOneTensorIso_apply {X Y : Cochains A} {i j k : ℤ} (e : i + j = k)
    (a : Rmod A ≅ X.X i) (b : Rmod A ≅ Y.X j)
    (h : ∀ i' j', i' + j' = k → (i' ≠ i ∨ j' ≠ j) → IsZero (X.X i' ⊗ Y.X j')) :
    (rankOneTensorIso e a b h).hom (1 : A) = homogeneousTensor e (a.hom 1) (b.hom 1) := by
  change (ιTensorObj X Y i j k e)
    ((a.hom ⊗ₘ b.hom) ((1 : A) ⊗ₜ[A] (1 : A))) = _
  rw [ModuleCat.MonoidalCategory.tensorHom_tmul]

private lemma sphereTensorDiskZero (n m k : ℤ) (h₀ : k ≠ n + m) (h₁ : k ≠ n + m + 1) :
    IsZero ((T (sphere A n) (disk A m)).X k) := by
  apply tensorDegreeZero
  intro i j e
  by_cases hi : i = n
  · exact tensorZeroRight (diskDegreeIsZero m j (by omega) (by omega))
  · exact tensorZeroLeft (sphereDegreeIsZero n i hi)

private lemma sphereTensorSphereZero (n m k : ℤ) (h₀ : k ≠ n + m) :
    IsZero ((T (sphere A n) (sphere A m)).X k) := by
  apply tensorDegreeZero
  intro i j e
  by_cases hi : i = n
  · exact tensorZeroRight (sphereDegreeIsZero m j (by omega))
  · exact tensorZeroLeft (sphereDegreeIsZero n i hi)

private lemma sphereTensorSupported {Y : Cochains A} (n j k : ℤ) (e : n + j = k) :
    ∀ i' j', i' + j' = k → (i' ≠ n ∨ j' ≠ j) → IsZero ((sphere A n).X i' ⊗ Y.X j') := by
  intro i' j' e' h
  apply tensorZeroLeft
  apply sphereDegreeIsZero
  omega

private def signIso (s : ℤˣ) (M : ModuleCat.{u} A) : M ≅ M where
  hom := s • 𝟙 M
  inv := s • 𝟙 M
  hom_inv_id := by rcases Int.units_eq_one_or s with rfl | rfl <;> simp [Units.smul_def]
  inv_hom_id := by rcases Int.units_eq_one_or s with rfl | rfl <;> simp [Units.smul_def]

private lemma map_sign {M N : ModuleCat.{u} A} (f : M ⟶ N) (s : ℤˣ) (x : M) :
    f (s • x) = s • f x := by
  change f.hom (s • x) = s • f.hom x
  simp only [Units.smul_def, map_zsmul]

private lemma sign_twice (s : ℤˣ) {M : ModuleCat.{u} A} (x : M) : s • (s • x) = x := by
  rcases Int.units_eq_one_or s with rfl | rfl <;> simp [Units.smul_def]

private def diskToSphereTensorDisk (n m : ℤ) :
    disk A (n + m) ⟶ T (sphere A n) (disk A m) :=
  (diskHomEquiv (n + m)).symm (homogeneousTensor rfl (sphereGenerator A n) (diskGenerator A m))

private lemma diskToSphereTensorDisk_lower (n m : ℤ) :
    (diskToSphereTensorDisk (A := A) n m).f (n + m) (diskGenerator A (n + m)) =
      homogeneousTensor rfl (sphereGenerator A n) (diskGenerator A m) :=
  (diskHomEquiv (n + m)).apply_symm_apply _

private lemma diskToSphereTensorDisk_upper (n m : ℤ) :
    (diskToSphereTensorDisk (A := A) n m).f (n + m + 1)
      ((disk A (n + m)).d (n + m) (n + m + 1) (diskGenerator A (n + m))) =
      n.negOnePow • homogeneousTensor (by omega : n + (m + 1) = n + m + 1)
        (sphereGenerator A n) ((disk A m).d m (m + 1) (diskGenerator A m)) := by
  rw [← commute_apply (diskToSphereTensorDisk (A := A) n m) (n + m) (n + m + 1),
    diskToSphereTensorDisk_lower]
  have h := tensor_d_apply (P := sphere A n) (Q := disk A m) n m (n + m) (n + m + 1)
    rfl rfl (sphereGenerator A n) (diskGenerator A m)
  have hz : (sphere A n).d n (n + 1) (sphereGenerator A n) = 0 := by
    have hd : (sphere A n).d n (n + 1) = 0 := single_obj_d _ _ _ _ _
    exact ConcreteCategory.congr_hom hd _
  rw [hz, TensorProduct.zero_tmul, map_zero, zero_add] at h
  exact h

set_option maxHeartbeats 800000 in
private lemma diskToSphereTensorDisk_isIso (n m : ℤ) :
    IsIso (diskToSphereTensorDisk (A := A) n m) := by
  have hc (k : ℤ) : IsIso ((diskToSphereTensorDisk (A := A) n m).f k) := by
    by_cases h₀ : k = n + m
    · subst k
      let e := rankOneTensorIso (X := sphere A n) (Y := disk A m) rfl
        (sphereBasis n).symm (diskLower m).symm (sphereTensorSupported n m (n + m) rfl)
      have hh : (diskToSphereTensorDisk (A := A) n m).f (n + m) =
          (diskLower (n + m)).hom ≫ e.hom := by
        apply hom_eq_of_regular (diskLower (n + m)).symm
        change (diskToSphereTensorDisk (A := A) n m).f (n + m) (diskGenerator A (n + m)) =
          e.hom ((diskLower (n + m)).hom ((diskLower (n + m)).inv 1))
        rw [diskToSphereTensorDisk_lower]
        simp only [Iso.inv_hom_id_apply]
        exact (rankOneTensorIso_apply (X := sphere A n) (Y := disk A m) rfl
          (sphereBasis n).symm (diskLower m).symm _).symm
      rw [hh]
      infer_instance
    · by_cases h₁ : k = n + m + 1
      · subst k
        let e := rankOneTensorIso (X := sphere A n) (Y := disk A m)
          (by omega : n + (m + 1) = n + m + 1)
          (sphereBasis n).symm (diskUpper m).symm
          (sphereTensorSupported n (m + 1) (n + m + 1) (by omega))
        let s := signIso n.negOnePow ((T (sphere A n) (disk A m)).X (n + m + 1))
        have hh : (diskToSphereTensorDisk (A := A) n m).f (n + m + 1) =
            (diskUpper (n + m)).hom ≫ e.hom ≫ s.hom := by
          apply hom_eq_of_regular (diskUpper (n + m)).symm
          change (diskToSphereTensorDisk (A := A) n m).f (n + m + 1)
              ((diskUpper (n + m)).inv 1) =
            s.hom (e.hom ((diskUpper (n + m)).hom ((diskUpper (n + m)).inv 1)))
          have hup := diskToSphereTensorDisk_upper (A := A) n m
          rw [disk_d_generator (A := A) (n + m)] at hup
          rw [hup]
          have hid : (diskUpper (A := A) (n + m)).hom ((diskUpper (n + m)).inv 1) = 1 := by simp
          rw [hid, disk_d_generator m]
          change _ = n.negOnePow • e.hom 1
          exact congrArg (fun z : (T (sphere A n) (disk A m)).X (n + m + 1) ↦ n.negOnePow • z)
            (rankOneTensorIso_apply (X := sphere A n) (Y := disk A m)
              (by omega : n + (m + 1) = n + m + 1) (sphereBasis n).symm (diskUpper m).symm
              (sphereTensorSupported n (m + 1) (n + m + 1) (by omega))).symm
        rw [hh]
        infer_instance
      · let e := (diskDegreeIsZero (A := A) (n + m) k h₀ h₁).iso
          (sphereTensorDiskZero (A := A) n m k h₀ h₁)
        have hh : (diskToSphereTensorDisk (A := A) n m).f k = e.hom :=
          (diskDegreeIsZero (n + m) k h₀ h₁).eq_of_src _ _
        rw [hh]
        infer_instance
  exact Hom.isIso_of_components _

private lemma disk_projective (n k : ℤ) : Projective ((disk A n).X k) := by
  by_cases h : k = n
  · subst k
    exact Projective.of_iso (diskLower n).symm (inferInstance : Projective (Rmod A))
  · by_cases h' : k = n + 1
    · subst k
      exact Projective.of_iso (diskUpper n).symm (inferInstance : Projective (Rmod A))
    · exact (diskDegreeIsZero n k h h').projective

private lemma diskCokernel_cofibration {X Y : Cochains A} {f : X ⟶ Y}
    (h : ∀ k, IsSplitMono (f.f k)) {n : ℤ} (e : cokernel f ≅ disk A n) :
    projectiveCofibrations A f := by
  have : (disk A n).IsKProjective :=
    ⟨fun g _ ↦ ⟨by simpa using (diskContraction n).compRight g⟩⟩
  refine (projectiveCofibrations_iff A f).2 ⟨h, fun k ↦ ?_, ?_⟩
  · let E := (eval (ModuleCat.{u} A) (ComplexShape.up ℤ) k).mapIso e
    exact Projective.of_iso E.symm (disk_projective n k)
  · exact (isKProjective_iff_homComplex_acyclic A _).1
      (CochainComplex.isKProjective_of_iso e.symm)

private lemma diskCokernel_quasiIso {X Y Z : Cochains A} {f : X ⟶ Y} {q : Y ⟶ Z}
    (S : GradedSplit f q) {n : ℤ} (e : Z ≅ disk A n) : QuasiIso f := by
  have hd (k : ℤ) : IsZero (homology (disk A n) k) := by
    rw [IsZero.iff_id_eq_zero]
    have h := (diskContraction (A := A) n).homologyMap_eq k
    rwa [homologyMap_id, homologyMap_zero] at h
  have hz (k : ℤ) : IsZero (homology Z k) :=
    (hd k).of_iso ((homologyFunctor (ModuleCat A) (ComplexShape.up ℤ) k).mapIso e)
  have hs := S.shortExact
  rw [quasiIso_iff]
  intro k
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hm : Mono (homologyMap f k) :=
    ((ShortComplex.mk _ _ _).exact_iff_mono ((hz (k - 1)).eq_of_src _ _)).1
      (hs.homology_exact₁ (k - 1) k (show k - 1 + 1 = k by omega))
  have he : Epi (homologyMap f k) :=
    ((ShortComplex.mk _ _ _).exact_iff_epi ((hz k).eq_of_tgt _ _)).1 (hs.homology_exact₂ k)
  exact isIso_of_mono_of_epi _

private lemma tensorMap_onTensor {X Y U V : Cochains A} (a : X ⟶ Y) (b : U ⟶ V)
    {i j k : ℤ} (h : i + j = k) (x : X.X i) (y : U.X j) :
    (tensorMap a b).f k (homogeneousTensor h x y) =
      homogeneousTensor h (a.f i x) (b.f j y) := by
  rw [tensorMap_f, gt_apply]

/-- The pushout product of a sphere inclusion with a zero-to-disk generator. -/
theorem pushoutProductIJ : pushoutProductIJType.{u} := by
  intro A _ n m
  let f := pushoutProduct (iGenerator A n) (jGenerator A m)
  let q := tensorMap (diskQuotient n) (𝟙 (disk A m))
  let S : GradedSplit f q := (iSplit n).tensorPushout (jSplit m)
  let l := diskToSphereTensorDisk (A := A) n m
  have : IsIso l := diskToSphereTensorDisk_isIso n m
  let d : T (sphere A n) (disk A m) ≅ disk A (n + m) := (asIso l).symm
  let e := S.cokernelIso ≪≫ d
  have he : cokernel.π f ≫ e.hom = q ≫ d.hom := by
    change cokernel.π f ≫ S.cokernelIso.hom ≫ d.hom = _
    rw [← Category.assoc, S.cokernelIso_apply]
  change (∀ k, IsSplitMono (f.f k)) ∧ _ ∧ projectiveCofibrations A f ∧ QuasiIso f
  refine ⟨S.splitMono, ⟨e, ?_, ?_⟩, diskCokernel_cofibration S.splitMono e,
    diskCokernel_quasiIso S d⟩
  · change (cokernel.π f ≫ e.hom).f (n + m) _ = _
    rw [he]
    change d.hom.f (n + m) (q.f (n + m) (homogeneousTensor rfl
      (diskGenerator A n) (diskGenerator A m))) = diskGenerator A (n + m)
    have hq := tensorMap_onTensor (diskQuotient (A := A) n) (𝟙 (disk A m)) rfl
      (diskGenerator A n) (diskGenerator A m)
    change q.f (n + m) _ = homogeneousTensor rfl ((diskQuotient n).f n (diskGenerator A n))
      ((𝟙 ((disk A m).X m)) (diskGenerator A m)) at hq
    rw [diskQuotient_apply, ModuleCat.id_apply] at hq
    exact (congrArg (d.hom.f (n + m)) (hq.trans (diskToSphereTensorDisk_lower n m).symm)).trans
      (ConcreteCategory.congr_hom (congrArg (fun g ↦ g.f (n + m)) d.inv_hom_id) _)
  · change (cokernel.π f ≫ e.hom).f (n + m + 1) _ = _
    rw [he]
    let x := (disk A (n + m)).d (n + m) (n + m + 1) (diskGenerator A (n + m))
    let y := (disk A m).d m (m + 1) (diskGenerator A m)
    let t := homogeneousTensor (by omega : n + (m + 1) = n + m + 1) (sphereGenerator A n) y
    change d.hom.f (n + m + 1) (q.f (n + m + 1) (homogeneousTensor
      (by omega : n + (m + 1) = n + m + 1) (diskGenerator A n) y)) = n.negOnePow • x
    have hq := tensorMap_onTensor (diskQuotient (A := A) n) (𝟙 (disk A m))
      (by omega : n + (m + 1) = n + m + 1) (diskGenerator A n) y
    change q.f (n + m + 1) _ = homogeneousTensor (by omega : n + (m + 1) = n + m + 1)
      ((diskQuotient n).f n (diskGenerator A n)) ((𝟙 ((disk A m).X (m + 1))) y) at hq
    rw [diskQuotient_apply, ModuleCat.id_apply] at hq
    change q.f (n + m + 1) _ = t at hq
    have hl : d.inv.f (n + m + 1) x = n.negOnePow • t := diskToSphereTensorDisk_upper n m
    have hi : d.hom.f (n + m + 1) (d.inv.f (n + m + 1) x) = x :=
      ConcreteCategory.congr_hom (congrArg (fun g ↦ g.f (n + m + 1)) d.inv_hom_id) x
    rw [hq, ← sign_twice n.negOnePow t, ← hl, map_sign]
    exact congrArg (n.negOnePow • ·) hi

private lemma tensorSphere_cycle (n m : ℤ) :
    (T (sphere A n) (sphere A m)).d (n + m) (n + m + 1)
      (homogeneousTensor rfl (sphereGenerator A n) (sphereGenerator A m)) = 0 := by
  have hz := sphereTensorSphereZero (A := A) n m (n + m + 1) (by omega)
  have h := hz.eq_of_tgt ((T (sphere A n) (sphere A m)).d (n + m) (n + m + 1)) 0
  rw [h]
  rfl

private def sphereToSphereTensorSphere (n m : ℤ) :
    sphere A (n + m) ⟶ T (sphere A n) (sphere A m) :=
  (sphereHomEquiv (n + m)).symm ⟨_, tensorSphere_cycle n m⟩

private lemma sphereToSphereTensorSphere_apply (n m : ℤ) :
    (sphereToSphereTensorSphere (A := A) n m).f (n + m) (sphereGenerator A (n + m)) =
      homogeneousTensor rfl (sphereGenerator A n) (sphereGenerator A m) := by
  let z : { z : (T (sphere A n) (sphere A m)).X (n + m) //
    (T (sphere A n) (sphere A m)).d (n + m) (n + m + 1) z = 0 } :=
    ⟨homogeneousTensor rfl (sphereGenerator A n) (sphereGenerator A m), tensorSphere_cycle n m⟩
  change (sphereHomEquiv (n + m) ((sphereHomEquiv (n + m)).symm z)).val = z.val
  rw [Equiv.apply_symm_apply]

private lemma sphereToSphereTensorSphere_isIso (n m : ℤ) :
    IsIso (sphereToSphereTensorSphere (A := A) n m) := by
  have hc (k : ℤ) : IsIso ((sphereToSphereTensorSphere (A := A) n m).f k) := by
    by_cases h : k = n + m
    · subst k
      let e := rankOneTensorIso (X := sphere A n) (Y := sphere A m) rfl
        (sphereBasis n).symm (sphereBasis m).symm (sphereTensorSupported n m (n + m) rfl)
      have hh : (sphereToSphereTensorSphere (A := A) n m).f (n + m) =
          (sphereBasis (n + m)).hom ≫ e.hom := by
        apply hom_eq_of_regular (sphereBasis (n + m)).symm
        change (sphereToSphereTensorSphere (A := A) n m).f (n + m)
            (sphereGenerator A (n + m)) =
          e.hom ((sphereBasis (n + m)).hom ((sphereBasis (n + m)).inv 1))
        rw [sphereToSphereTensorSphere_apply]
        simp only [Iso.inv_hom_id_apply]
        exact (rankOneTensorIso_apply (X := sphere A n) (Y := sphere A m) rfl
          (sphereBasis n).symm (sphereBasis m).symm _).symm
      rw [hh]
      infer_instance
    · let e := (sphereDegreeIsZero (n + m) k h).iso (sphereTensorSphereZero (A := A) n m k h)
      have hh : (sphereToSphereTensorSphere (A := A) n m).f k = e.hom :=
        (sphereDegreeIsZero (n + m) k h).eq_of_src _ _
      rw [hh]
      infer_instance
  exact Hom.isIso_of_components _

/-- A square between graded-split inclusions is a pushout when its map on
quotients is invertible. -/
private lemma GradedSplit.isPushout {X Y Z U V W : Cochains A}
    {a : X ⟶ Y} {p : Y ⟶ Z} {b : U ⟶ V} {q : V ⟶ W}
    (S : GradedSplit a p) (D : GradedSplit b q)
    {s : X ⟶ U} {e : Y ⟶ V} {t : Z ⟶ W} [IsIso t]
    (h : a ≫ e = s ≫ b) (ht : e ≫ q = p ≫ t) : IsPushout a s e b := by
  let L := ShortComplex.mk a p S.zero
  let R := ShortComplex.mk b q D.zero
  let P := L.push s
  let k : P.X₂ ⟶ V := pushout.desc e b h
  have hk₁ : pushout.inl a s ≫ k = e := pushout.inl_desc _ _ _
  have hk₂ : pushout.inr a s ≫ k = b := pushout.inr_desc _ _ _
  let φ : P ⟶ R :=
    { τ₁ := 𝟙 U
      τ₂ := k
      τ₃ := t
      comm₁₂ := by
        change 𝟙 U ≫ b = pushout.inr a s ≫ k
        rw [hk₂, Category.id_comp]
      comm₂₃ := by
        change k ≫ q = P.g ≫ t
        apply pushout.hom_ext
        · rw [← Category.assoc, hk₁, ht]
          change p ≫ t = pushout.inl a s ≫ pushout.desc p 0 _ ≫ t
          rw [pushout.inl_desc_assoc]
        · change pushout.inr a s ≫ k ≫ q = pushout.inr a s ≫ P.g ≫ t
          rw [← Category.assoc, hk₂, D.zero]
          change 0 = pushout.inr a s ≫ pushout.desc p 0 _ ≫ t
          rw [pushout.inr_desc_assoc, zero_comp] }
  have hk : IsIso k :=
    ShortComplex.isIso₂_of_shortExact_of_isIso₁₃' φ (S.shortExact.push s) D.shortExact
      (by change IsIso (𝟙 U); infer_instance) (show IsIso t by infer_instance)
  exact (IsPushout.of_hasPushout a s).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (asIso k)
    (by simp) (by simp) (by simpa using hk₁) (by simpa using hk₂)

private lemma attachmentBoundary_image (n m : ℤ) :
    (pushoutProduct (iGenerator A n) (iGenerator A m)).f (n + m + 1)
      (attachmentBoundary A n m) =
      (T (disk A n) (disk A m)).d (n + m) (n + m + 1)
        (homogeneousTensor rfl (diskGenerator A n) (diskGenerator A m)) := by
  let a := iGenerator A n
  let b := iGenerator A m
  let f := pushoutProduct a b
  let k := n + m + 1
  let x := homogeneousTensor (by omega : n + 1 + m = k)
    (sphereGenerator A (n + 1)) (diskGenerator A m)
  let y := homogeneousTensor (by omega : n + (m + 1) = k)
    (diskGenerator A n) (sphereGenerator A (m + 1))
  change f.f k ((pushout.inr (leftLeg a b) (rightLeg a b)).f k x +
    n.negOnePow • (pushout.inl (leftLeg a b) (rightLeg a b)).f k y) = _
  have hr := ConcreteCategory.congr_hom
    (congrArg (fun g : T (sphere A (n + 1)) (disk A m) ⟶ T (disk A n) (disk A m) ↦
      g.f k) (product_inr a b)) x
  have hl := ConcreteCategory.congr_hom
    (congrArg (fun g : T (disk A n) (sphere A (m + 1)) ⟶ T (disk A n) (disk A m) ↦
      g.f k) (product_inl a b)) y
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply] at hr hl
  rw [map_add, map_sign, hr, hl]
  have tx := tensorMap_onTensor a (𝟙 (disk A m)) (by omega : n + 1 + m = k)
    (sphereGenerator A (n + 1)) (diskGenerator A m)
  have ty := tensorMap_onTensor (𝟙 (disk A n)) b (by omega : n + (m + 1) = k)
    (diskGenerator A n) (sphereGenerator A (m + 1))
  change (tensorMap a (𝟙 (disk A m))).f k x =
    homogeneousTensor (by omega : n + 1 + m = k)
      (a.f (n + 1) (sphereGenerator A (n + 1))) ((𝟙 ((disk A m).X m)) (diskGenerator A m)) at tx
  change (tensorMap (𝟙 (disk A n)) b).f k y =
    homogeneousTensor (by omega : n + (m + 1) = k)
      ((𝟙 ((disk A n).X n)) (diskGenerator A n)) (b.f (m + 1) (sphereGenerator A (m + 1))) at ty
  rw [ModuleCat.id_apply] at tx ty
  rw [tx, ty]
  have h := tensor_d_apply (P := disk A n) (Q := disk A m) n m (n + m) k rfl rfl
    (diskGenerator A n) (diskGenerator A m)
  rw [disk_d_generator_eq (A := A) n, disk_d_generator_eq (A := A) m] at h
  exact h.symm

private lemma attachmentBoundary_cycle (n m : ℤ) :
    (source (iGenerator A n) (iGenerator A m)).d (n + m + 1) (n + m + 1 + 1)
        (attachmentBoundary A n m) = 0 := by
  let f := pushoutProduct (iGenerator A n) (iGenerator A m)
  let k := n + m + 1
  let Q := (iSplit (A := A) n).tensorPushout (iSplit m)
  have hmono : Mono (f.f (k + 1)) := SplitMono.mono ⟨Q.r _, Q.fr _⟩
  apply (ModuleCat.mono_iff_injective (f.f (k + 1))).1 hmono
  change f.f (k + 1) ((source (iGenerator A n) (iGenerator A m)).d k (k + 1)
    (attachmentBoundary A n m)) = f.f (k + 1) 0
  rw [← commute_apply f k (k + 1), attachmentBoundary_image, map_zero]
  exact ConcreteCategory.congr_hom ((T (disk A n) (disk A m)).d_comp_d (n + m) k (k + 1)) _

/-- The two lower disk generators give the single new cell of the pushout product. -/
theorem pushoutProductII : pushoutProductIIType.{u} := by
  intro A _ n m
  let f := pushoutProduct (iGenerator A n) (iGenerator A m)
  let k := n + m
  let e : disk A k ⟶ T (disk A n) (disk A m) :=
    (diskHomEquiv k).symm (homogeneousTensor rfl (diskGenerator A n) (diskGenerator A m))
  let s : sphere A (k + 1) ⟶ source (iGenerator A n) (iGenerator A m) :=
    (sphereHomEquiv (k + 1)).symm ⟨attachmentBoundary A n m, attachmentBoundary_cycle n m⟩
  have he : e.f k (diskGenerator A k) =
      homogeneousTensor rfl (diskGenerator A n) (diskGenerator A m) :=
    (diskHomEquiv k).apply_symm_apply _
  have hs : s.f (k + 1) (sphereGenerator A (k + 1)) = attachmentBoundary A n m :=
    congrArg Subtype.val ((sphereHomEquiv (k + 1)).apply_symm_apply
      ⟨attachmentBoundary A n m, attachmentBoundary_cycle n m⟩)
  refine ⟨s, e, ?_, he, hs⟩
  change IsPushout (iGenerator A k) s e f
  have h : iGenerator A k ≫ e = s ≫ f := by
    apply (sphereHomEquiv (k + 1)).injective
    apply Subtype.ext
    rw [sphereHomEquiv_iGenerator_comp, sphereHomEquiv_comp]
    change (T (disk A n) (disk A m)).d k (k + 1) (e.f k (diskGenerator A k)) =
      f.f (k + 1) (s.f (k + 1) (sphereGenerator A (k + 1)))
    rw [hs, attachmentBoundary_image, he]
    rfl
  let q := tensorMap (diskQuotient (A := A) n) (diskQuotient m)
  let t := sphereToSphereTensorSphere (A := A) n m
  have : IsIso t := sphereToSphereTensorSphere_isIso n m
  have ht : e ≫ q = diskQuotient k ≫ t := by
    apply (diskHomEquiv k).injective
    rw [diskHomEquiv_comp, diskHomEquiv_comp]
    change q.f k (e.f k (diskGenerator A k)) =
      t.f k ((diskQuotient k).f k (diskGenerator A k))
    rw [he, diskQuotient_apply]
    have hq := tensorMap_onTensor (diskQuotient (A := A) n) (diskQuotient m) (rfl : n + m = k)
      (diskGenerator A n) (diskGenerator A m)
    rw [diskQuotient_apply, diskQuotient_apply] at hq
    exact hq.trans (sphereToSphereTensorSphere_apply n m).symm
  exact (iSplit k).isPushout ((iSplit n).tensorPushout (iSplit m)) h ht

/-- First braid the module terms and then use the signed flip of the total complex. -/
private def koszulSwap (X Y : Cochains A) : T X Y ≅ T Y X := by
  let c := ComplexShape.up ℤ
  let F := curriedTensor (ModuleCat A)
  let B := F.mapBifunctorHomologicalComplex c c
  let B' := F.flip.mapBifunctorHomologicalComplex c c
  have e : (B.obj X).obj Y ≅ (B'.obj X).obj Y := by
    refine Hom.isoOfComponents (fun i ↦ Hom.isoOfComponents (fun j ↦ β_ (X.X i) (Y.X j)) ?_) ?_
    · intro j j' _
      exact (BraidedCategory.braiding_naturality_right (X.X _) (Y.d j j')).symm
    · intro i i' _
      apply HomologicalComplex.hom_ext
      intro j
      exact (BraidedCategory.braiding_naturality_left (X.d i i') (Y.X j)).symm
  exact HomologicalComplex₂.total.mapIso e c ≪≫ mapBifunctorFlipIso Y X F c

/-- In the other order the cokernel is identified with the same disk
by the Koszul symmetry. -/
theorem pushoutProductJI : pushoutProductJIType.{u} := by
  intro A _ n m
  let f := pushoutProduct (jGenerator A m) (iGenerator A n)
  let q := tensorMap (𝟙 (disk A m)) (diskQuotient n)
  let S : GradedSplit f q := (jSplit m).tensorPushout (iSplit n)
  have : IsIso (diskToSphereTensorDisk (A := A) n m) := diskToSphereTensorDisk_isIso n m
  let d : T (disk A m) (sphere A n) ≅ disk A (n + m) :=
    koszulSwap _ _ ≪≫ (asIso (diskToSphereTensorDisk n m)).symm
  let e := S.cokernelIso ≪≫ d
  change (∀ k, IsSplitMono (f.f k)) ∧ Nonempty (cokernel f ≅ disk A (n + m)) ∧
    projectiveCofibrations A f ∧ QuasiIso f
  exact ⟨S.splitMono, ⟨e⟩, diskCokernel_cofibration S.splitMono e, diskCokernel_quasiIso S d⟩

end

end DerivedFormalization.Model.Complexes
