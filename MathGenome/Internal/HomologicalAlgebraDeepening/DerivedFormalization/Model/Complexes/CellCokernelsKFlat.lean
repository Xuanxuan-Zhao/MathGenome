import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Model.Complexes.CellCokernels
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Model.Complexes.CellCokernelsKFlat
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.Grp.Ulift
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open P103.BalancedTensor P103.Specs.Ch11.TorBalance

universe u v z j₀ j₁

namespace DerivedFormalization.Model.Complexes

open Specs.ComplexCellCokernelsKFlat

noncomputable section

variable {A : Type u} [Ring A]

/-- The signed direct-sum total of the balanced tensor product. -/
def balancedTensorTotal (A : Type u) [Ring A] (E : RightCochains.{u,v} A) (P : Cochains A) :
    TensorCochains.{max u v} := tensorTotalValue A E P

private theorem negation_component_d {R : Type u} [Ring R] (X : CochainComplex (ModuleCat.{v} R) ℤ)
    (p q : ℤ) (x : X.X p) :
    ((X.restriction downToUp).d (-p) (-q)).hom
        ((X.restrictionXIso downToUp (Int.neg_neg p)).inv.hom x) =
      (X.restrictionXIso downToUp (Int.neg_neg q)).inv.hom ((X.d p q).hom x) := by
  have h : (X.restrictionXIso downToUp (Int.neg_neg p)).inv ≫
      (X.restriction downToUp).d (-p) (-q) =
        X.d p q ≫ (X.restrictionXIso downToUp (Int.neg_neg q)).inv := by
    rw [restriction_d_eq X downToUp (Int.neg_neg p) (Int.neg_neg q), Iso.inv_hom_id_assoc]
  exact congrArg (fun f ↦ f.hom x) h

theorem balancedTensorTotal_d : tensorTotalDifferentialType.{u,v} := by
  intro A _ E P p q k h x y
  let C := E.restriction downToUp
  let D := P.restriction downToUp
  let K := tensorBicomplex C D
  let c := ComplexShape.down ℤ
  have h₁ : c.Rel (-p) (-(p + 1)) := by change -(p + 1) + 1 = -p; omega
  have h₂ : c.Rel (-q) (-(q + 1)) := by change -(q + 1) + 1 = -q; omega
  have hk : -p + -q = -k := by omega
  have hp : -(p + 1) + -q = -(k + 1) := by omega
  have hq : -p + -(q + 1) = -(k + 1) := by omega
  have hd : K.ιTotal c (-p) (-q) (-k) hk ≫ (K.total c).d (-k) (-(k + 1)) =
      (K.d (-p) (-(p + 1))).f (-q) ≫ K.ιTotal c (-(p + 1)) (-q) (-(k + 1)) hp +
      p.negOnePow • ((K.X (-p)).d (-q) (-(q + 1)) ≫
        K.ιTotal c (-p) (-(q + 1)) (-(k + 1)) hq) := by
    change _ ≫ (K.D₁ c (-k) (-(k + 1)) + K.D₂ c (-k) (-(k + 1))) = _
    rw [Preadditive.comp_add, K.ι_D₁, K.ι_D₂,
      K.d₁_eq c h₁ (-q) (-(k + 1)) hp, K.d₂_eq c (-p) h₂ (-(k + 1)) hq]
    change (1 : ℤˣ) • _ + (-p).negOnePow • _ = _
    rw [one_smul, Int.negOnePow_neg]
  let x' := (E.restrictionXIso downToUp (Int.neg_neg p)).inv.hom x
  let y' := (P.restrictionXIso downToUp (Int.neg_neg q)).inv.hom y
  have he := congrArg (fun f ↦ f.hom (tmul A x' y')) hd
  change ((tensorTotalValue A E P).d k (k + 1)).hom (tensorInclusionValue A E P p q k h x y) =
    tensorInclusion C D (-(p + 1)) (-q) (-(k + 1)) hp
      (tmul A ((C.d (-p) (-(p + 1))).hom x') y') +
    p.negOnePow • tensorInclusion C D (-p) (-(q + 1)) (-(k + 1)) hq
      (tmul A x' ((D.d (-q) (-(q + 1))).hom y')) at he
  rw [show ((C.d (-p) (-(p + 1))).hom x') = _ from negation_component_d E p (p + 1) x,
    show ((D.d (-q) (-(q + 1))).hom y') = _ from negation_component_d P q (q + 1) y] at he
  exact he

/-- Tensoring with this complex sends all acyclic right module complexes to acyclic complexes. -/
def IsKFlat (A : Type u) [Ring A] (P : Cochains A) : Prop :=
  ∀ (E : RightCochains.{u,v} A), E.Acyclic → (balancedTensorTotal A E P).Acyclic

private abbrev TensorChains := ChainComplex (ModuleCat.{z} ℤ) ℤ

private def tensorChainFunctor (C : ChainComplex (ModuleCat.{v} Aᵐᵒᵖ) ℤ) :
    ChainComplex (ModuleCat.{u} A) ℤ ⥤ TensorChains.{max u v} where
  obj := tensorTotal C
  map g := tensorTotalMap (𝟙 C) g
  map_id D := by
    change HomologicalComplex₂.total.map (tensorBicomplexMap (𝟙 C) (𝟙 D)) _ = _
    rw [P103.Ch11.TorBalance.tensorBicomplexMap_id, HomologicalComplex₂.total.map_id]
    rfl
  map_comp g h := by
    change HomologicalComplex₂.total.map (tensorBicomplexMap (𝟙 C) (g ≫ h)) _ =
      HomologicalComplex₂.total.map (tensorBicomplexMap (𝟙 C) g) _ ≫
        HomologicalComplex₂.total.map (tensorBicomplexMap (𝟙 C) h) _
    rw [← HomologicalComplex₂.total.map_comp,
      ← P103.Ch11.TorBalance.tensorBicomplexMap_comp, Category.id_comp]

private def tensorCochainFunctor (E : RightCochains.{u,v} A) : Cochains A ⥤ TensorCochains.{max u v} :=
  downToUp.restrictionFunctor _ ⋙ tensorChainFunctor (E.restriction downToUp) ⋙
    upToDown.restrictionFunctor _

theorem isKFlat_of_retract (A : Type u) [Ring A] {P Q : Cochains A} (r : Retract P Q)
    (hQ : IsKFlat.{u,v} A Q) : IsKFlat.{u,v} A P := by
  intro E hE n
  let F := tensorCochainFunctor E ⋙ homologyFunctor (ModuleCat.{max u v} ℤ) (ComplexShape.up ℤ) n
  apply (exactAt_iff_isZero_homology _ _).2
  have hz : IsZero (F.obj Q) := (hQ E hE n).isZero_homology
  apply (IsZero.iff_id_eq_zero _).2
  change 𝟙 (F.obj P) = 0
  rw [← F.map_id, ← r.retract, F.map_comp, hz.eq_of_tgt (F.map r.i) 0, zero_comp]

/-- The left action on maps out of a right module is precomposition with right multiplication. -/
private local instance tensorHomModule (M : ModuleCat.{v} Aᵐᵒᵖ) (V : ModuleCat.{max u v} ℤ) :
    Module A (M →+ V) where
  smul a f := AddMonoidHom.mk' (fun m ↦ f (MulOpposite.op a • m)) (by simp [smul_add])
  one_smul f := by
    ext m
    change f (MulOpposite.op (1 : A) • m) = f m
    simp
  mul_smul a b f := by
    ext m
    change f ((MulOpposite.op b * MulOpposite.op a) • m) =
      f (MulOpposite.op b • (MulOpposite.op a • m))
    rw [mul_smul]
  smul_zero a := by ext m; rfl
  smul_add a f g := by ext m; rfl
  add_smul a b f := by
    ext m
    change f (MulOpposite.op (a + b) • m) =
      f (MulOpposite.op a • m) + f (MulOpposite.op b • m)
    simp [add_smul]
  zero_smul f := by
    ext m
    change f (MulOpposite.op (0 : A) • m) = 0
    simp

private def tensorHomFunctor (M : ModuleCat.{v} Aᵐᵒᵖ) :
    ModuleCat.{max u v} ℤ ⥤ ModuleCat.{max u v} A where
  obj V := ModuleCat.of A (M →+ V)
  map f := ModuleCat.ofHom
    { toFun := fun g ↦ f.hom.toAddMonoidHom.comp g
      map_add' := by intros; ext m; simp
      map_smul' := by intros; rfl }
  map_id V := by ext f m; rfl
  map_comp f g := by ext h m; rfl

private def intLinear {B D : Type*} [AddCommGroup B] [AddCommGroup D]
    [Module ℤ B] [Module ℤ D] (f : B →+ D) : B →ₗ[ℤ] D :=
  { f with
    map_smul' := by
      intro r x
      change f ((inferInstance : Module ℤ B).smul r x) = (inferInstance : Module ℤ D).smul r (f x)
      rw [int_smul_eq_zsmul, int_smul_eq_zsmul, _root_.map_zsmul] }

private theorem tensorHom_ext {M : ModuleCat.{v} Aᵐᵒᵖ}
    {B : ModuleCat.{max u v} A} {V : ModuleCat.{max u v} ℤ}
    {f g : (leftTensorFunctor (R := A) M).obj B ⟶ V}
    (h : ∀ m b, f.hom (tmul A m b) = g.hom (tmul A m b)) : f = g := by
  apply ModuleCat.hom_ext
  apply LinearMap.toAddMonoidHom_injective
  exact P103.BalancedTensor.hom_ext h

private def tensorHomEquiv (M : ModuleCat.{v} Aᵐᵒᵖ)
    (B : ModuleCat.{max u v} A) (V : ModuleCat.{max u v} ℤ) :
    ((leftTensorFunctor (R := A) M).obj B ⟶ V) ≃ (B ⟶ (tensorHomFunctor M).obj V) where
  toFun f := ModuleCat.ofHom
    { toFun b := AddMonoidHom.mk' (fun m ↦ f.hom (tmul A m b)) (fun m m' ↦
      (congrArg f.hom (add_tmul m m' b)).trans (map_add f.hom _ _))
      map_add' b b' := by ext m; exact (congrArg f.hom (tmul_add m b b')).trans (map_add f.hom _ _)
      map_smul' a b := by
        ext m
        exact congrArg f.hom (balance a m b).symm }
  invFun g := by
    let p : Pairing A (A := M) (B := B) V := Pairing.ofFun
      (fun m b ↦ (show M →+ V from g b) m)
      (fun m m' b ↦ map_add (show M →+ V from g b) m m')
      (fun m b b' ↦ congrArg (fun f : M →+ V ↦ f m) (map_add g.hom b b'))
      (fun a m b ↦ (congrArg (fun f : M →+ V ↦ f m) (map_smul g.hom a b)).symm)
    exact ModuleCat.ofHom (intLinear (P103.BalancedTensor.lift p))
  left_inv f := by
    apply tensorHom_ext (M := M) (B := B)
    intro m b
    rfl
  right_inv g := by ext b m; rfl

private instance (M : ModuleCat.{v} Aᵐᵒᵖ) :
    (leftTensorFunctor (R := A) M : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} ℤ).IsLeftAdjoint :=
  ⟨_, ⟨Adjunction.mkOfHomEquiv
    { homEquiv := tensorHomEquiv M
      homEquiv_naturality_left_symm := by
        intros
        apply tensorHom_ext (M := M)
        intros
        rfl
      homEquiv_naturality_right := by intros; ext b; rfl }⟩⟩

/-- Lifting the underlying type of a module preserves colimits of the given shape. -/
private instance moduleUlift_preservesColimits (J : Type j₀) [Category.{j₁} J]
    [HasColimitsOfShape J AddCommGrpCat.{u}] [HasColimitsOfShape J AddCommGrpCat.{max u v}] :
    PreservesColimitsOfShape J (ModuleCat.uliftFunctor.{v,u} A) := by
  let F := ModuleCat.uliftFunctor.{v,u} A
  let G := forget₂ (ModuleCat.{max u v} A) AddCommGrpCat.{max u v}
  have : PreservesColimitsOfShape J (F ⋙ G) := by
    change PreservesColimitsOfShape J
      (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u} ⋙ AddCommGrpCat.uliftFunctor.{v,u})
    infer_instance
  exact preservesColimitsOfShape_of_reflects_of_preserves F G

/-- The actual mixed tensor agrees naturally with tensoring after lifting only the left
module into the common universe. -/
private def tensorUliftIso (M : ModuleCat.{v} Aᵐᵒᵖ) :
    (leftTensorFunctor (R := A) M : ModuleCat.{u} A ⥤ ModuleCat.{max u v} ℤ) ≅
      ModuleCat.uliftFunctor.{v,u} A ⋙
        (leftTensorFunctor (R := A) M : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} ℤ) := by
  refine NatIso.ofComponents (fun B ↦ ?_) ?_
  · refine
      { hom := ModuleCat.ofHom
          (P103.Specs.Ch11.ExtTorDefinitions.tensorMap LinearMap.id
            (ULift.moduleEquiv : ULift.{v} B ≃ₗ[A] B).symm.toLinearMap)
        inv := ModuleCat.ofHom
          (P103.Specs.Ch11.ExtTorDefinitions.tensorMap LinearMap.id
            (ULift.moduleEquiv : ULift.{v} B ≃ₗ[A] B).toLinearMap)
        hom_inv_id := ?_
        inv_hom_id := ?_ }
    all_goals
      apply ModuleCat.hom_ext
      apply P103.Specs.Ch11.ExtTorDefinitions.tensor_hom_ext
      intros
      rfl
  · intro B B' f
    apply ModuleCat.hom_ext
    apply P103.Specs.Ch11.ExtTorDefinitions.tensor_hom_ext
    intros
    rfl

private theorem mixedTensor_preservesColimits (M : ModuleCat.{v} Aᵐᵒᵖ)
    (J : Type j₀) [Category.{j₁} J]
    [HasColimitsOfShape J AddCommGrpCat.{u}] [HasColimitsOfShape J AddCommGrpCat.{max u v}] :
    PreservesColimitsOfShape J
      (leftTensorFunctor (R := A) M : ModuleCat.{u} A ⥤ ModuleCat.{max u v} ℤ) :=
  preservesColimitsOfShape_of_natIso (tensorUliftIso M).symm

private abbrev CoefficientChains (A : Type u) [Ring A] := ChainComplex (ModuleCat.{u} A) ℤ
private abbrev Diagonal (k : ℤ) := {ij : ℤ × ℤ // ij.1 + ij.2 = k}

private def tensorDiagonal (C : ChainComplex (ModuleCat.{v} Aᵐᵒᵖ) ℤ) (k : ℤ) :
    CoefficientChains A ⥤ (Discrete (Diagonal k) ⥤ ModuleCat.{max u v} ℤ) where
  obj D := Discrete.functor (fun ij ↦ (leftTensorFunctor (R := A) (C.X ij.1.1)).obj
    (D.X ij.1.2))
  map g := Discrete.natTrans (fun ij ↦
    (leftTensorFunctor (R := A) (C.X ij.as.1.1)).map (g.f ij.as.1.2))
  map_id D := by ext ij; simp
  map_comp g h := by ext ij; simp

private theorem tensorDiagonal_preservesColimitsOfShape (C : ChainComplex (ModuleCat.{v} Aᵐᵒᵖ) ℤ) (k : ℤ)
    (J : Type j₀) [Category.{j₁} J]
    [HasColimitsOfShape J AddCommGrpCat.{u}] [HasColimitsOfShape J AddCommGrpCat.{max u v}] :
    PreservesColimitsOfShape J (tensorDiagonal C k) where
  preservesColimit {F} := ⟨fun hc ↦ ⟨evaluationJointlyReflectsColimits _ (fun ij ↦ by
    let G := eval (ModuleCat.{u} A) (ComplexShape.down ℤ) ij.as.1.2 ⋙
      (leftTensorFunctor (R := A) (C.X ij.as.1.1))
    letI := mixedTensor_preservesColimits (C.X ij.as.1.1) J
    exact isColimitOfPreserves G hc)⟩⟩

/-- Evaluation of the total takes the coproduct over a degree diagonal. -/
private def tensorChainEvalIso (C : ChainComplex (ModuleCat.{v} Aᵐᵒᵖ) ℤ) (k : ℤ) :
    tensorChainFunctor C ⋙ eval (ModuleCat.{max u v} ℤ) (ComplexShape.down ℤ) k ≅
      tensorDiagonal C k ⋙ colim :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro D D' g
    change (tensorTotalMap (𝟙 C) g).f k ≫ 𝟙 _ =
      𝟙 _ ≫ colimMap ((tensorDiagonal C k).map g)
    rw [Category.comp_id, Category.id_comp]
    apply HomologicalComplex₂.total.hom_ext
    intro i j h
    change (tensorBicomplex C D).ιTotal _ i j k h ≫
      (HomologicalComplex₂.total.map (tensorBicomplexMap (𝟙 C) g) _).f k = _
    rw [HomologicalComplex₂.ιTotal_map]
    change _ = colimit.ι _ ⟨⟨(i, j), h⟩⟩ ≫ colimMap ((tensorDiagonal C k).map g)
    rw [ι_colimMap]
    rfl)

private instance (C : ChainComplex (ModuleCat.{v} Aᵐᵒᵖ) ℤ) (J : Type j₀) [Category.{j₁} J]
    [HasColimitsOfShape J AddCommGrpCat.{u}] [HasColimitsOfShape J AddCommGrpCat.{max u v}] :
    PreservesColimitsOfShape J (tensorChainFunctor C) := by
  apply preservesColimitsOfShape_of_eval
  intro k
  have := tensorDiagonal_preservesColimitsOfShape C k J
  exact preservesColimitsOfShape_of_natIso (tensorChainEvalIso C k).symm

private instance restriction_preservesColimitsOfShape
    {c c' : ComplexShape ℤ} (e : c.Embedding c') [e.IsRelIff]
    (M : Type*) [Category* M] [HasZeroMorphisms M]
    (J : Type j₀) [Category.{j₁} J] [HasColimitsOfShape J M] :
    PreservesColimitsOfShape J (e.restrictionFunctor M) :=
  preservesColimitsOfShape_of_eval _ (fun i ↦
    inferInstanceAs (PreservesColimitsOfShape J (eval M c' (e.f i))))

private instance (E : RightCochains.{u,v} A) (J : Type j₀) [Category.{j₁} J]
    [HasColimitsOfShape J AddCommGrpCat.{u}] [HasColimitsOfShape J AddCommGrpCat.{max u v}] :
    PreservesColimitsOfShape J (tensorCochainFunctor E) := by
  unfold tensorCochainFunctor
  infer_instance

private theorem tensorChain_degreewiseMono (C : ChainComplex (ModuleCat.{v} Aᵐᵒᵖ) ℤ)
    {P Q : CoefficientChains A} (g : P ⟶ Q) (hg : ∀ j, IsSplitMono (g.f j)) :
    Mono ((tensorChainFunctor C).map g) := by
  apply mono_of_mono_f
  intro k
  let K := tensorBicomplex C P
  let L := tensorBicomplex C Q
  let c := ComplexShape.down ℤ
  let s : (L.total c).X k ⟶ (K.total c).X k := L.totalDesc (c₁₂ := c)
    (fun i j h ↦ (leftTensorFunctor (R := A) (C.X i)).map
      (letI := hg j; retraction (g.f j)) ≫ K.ιTotal c i j k h)
  have hsplit : ((tensorChainFunctor C).map g).f k ≫ s = 𝟙 _ := by
    apply HomologicalComplex₂.total.hom_ext
    intro i j h
    have := hg j
    change K.ιTotal c i j k h ≫
      (HomologicalComplex₂.total.map (tensorBicomplexMap (𝟙 C) g) c).f k ≫ s =
        K.ιTotal c i j k h ≫ 𝟙 _
    rw [HomologicalComplex₂.ιTotal_map_assoc, HomologicalComplex₂.ι_totalDesc, Category.comp_id]
    change (leftTensorFunctor (R := A) (C.X i)).map (g.f j) ≫
        (leftTensorFunctor (R := A) (C.X i)).map (retraction (g.f j)) ≫ _ = _
    have hm : (leftTensorFunctor (R := A) (C.X i)).map (g.f j) ≫
        (leftTensorFunctor (R := A) (C.X i)).map (retraction (g.f j)) = 𝟙 _ := by
      rw [← Functor.map_comp, IsSplitMono.id]
      exact CategoryTheory.Functor.map_id _ _
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t : (K.X i).X j ⟶ (K.X i).X j ↦ t ≫ K.ιTotal c i j k h) hm).trans
        (Category.id_comp _))
  have : IsSplitMono (((tensorChainFunctor C).map g).f k) := ⟨⟨⟨s, hsplit⟩⟩⟩
  infer_instance

private theorem tensorCochain_degreewiseMono (E : RightCochains.{u,v} A)
    {P Q : Cochains A} (g : P ⟶ Q) (hg : ∀ j, IsSplitMono (g.f j)) :
    Mono ((tensorCochainFunctor E).map g) := by
  have := tensorChain_degreewiseMono (E.restriction downToUp)
    (restrictionMap g downToUp) (fun j ↦ hg (-j))
  apply mono_of_mono_f
  intro k
  exact (inferInstance : Mono (((tensorChainFunctor (E.restriction downToUp)).map
    (restrictionMap g downToUp)).f (-k)))

/-- Graded splittings keep the tensor map injective, even for nonflat right terms. -/
private theorem tensorCochain_cokernel_shortExact (E : RightCochains.{u,v} A) {P Q : Cochains A}
    (g : P ⟶ Q) (hg : ∀ j, IsSplitMono (g.f j)) :
    ((ShortComplex.cokernelSequence g).map (tensorCochainFunctor E)).ShortExact := by
  let T := tensorCochainFunctor E
  have hc : IsColimit (CokernelCofork.ofπ _ ((ShortComplex.cokernelSequence g).map T).zero) :=
    CokernelCofork.mapIsColimit _ (cokernelIsCokernel g) T
  obtain ⟨he, hep⟩ := (((ShortComplex.cokernelSequence g).map T).exact_and_epi_g_iff_g_is_cokernel).2 ⟨hc⟩
  exact ShortComplex.ShortExact.mk' he (tensorCochain_degreewiseMono E g hg) hep

/-- Exactness of colimits in the coefficient category passes to acyclic complexes. -/
private theorem acyclic_of_colimit
    (J : Type j₀) [Category.{j₁} J] [HasColimitsOfShape J (ModuleCat.{z} ℤ)]
    [HasExactColimitsOfShape J (ModuleCat.{z} ℤ)]
    {F : J ⥤ TensorCochains.{z}} {s : Cocone F} (hs : IsColimit s)
    (h : ∀ j, (F.obj j).Acyclic) : s.pt.Acyclic := by
  intro k
  let ev := eval (ModuleCat.{z} ℤ) (ComplexShape.up ℤ)
  let i := (ComplexShape.up ℤ).prev k
  let l := (ComplexShape.up ℤ).next k
  let S : ShortComplex (J ⥤ ModuleCat.{z} ℤ) :=
    ShortComplex.mk (Functor.whiskerLeft F (dNatTrans (ModuleCat.{z} ℤ) (ComplexShape.up ℤ) i k))
      (Functor.whiskerLeft F (dNatTrans (ModuleCat.{z} ℤ) (ComplexShape.up ℤ) k l)) (by
        ext1
        funext j
        exact (F.obj j).d_comp_d i k l)
  have hS : S.Exact := by
    rw [ShortComplex.exact_iff_isZero_homology, IsZero.iff_id_eq_zero]
    ext1
    funext j
    let G := (evaluation J (ModuleCat.{z} ℤ)).obj j
    have hzero : IsZero ((S.map G).homology) := (h j k).isZero_homology
    exact (hzero.of_iso (S.mapHomologyIso G).symm).eq_of_src _ _
  exact colim.exact_mapShortComplex hS
    (isColimitOfPreserves (ev i) hs) (isColimitOfPreserves (ev k) hs)
    (isColimitOfPreserves (ev l) hs) (s.pt.d i k) (s.pt.d k l)
    (fun j ↦ (s.ι.app j).comm i k)
    (fun j ↦ (s.ι.app j).comm k l)

private theorem restriction_acyclic {M : Type*} [Category* M] [Abelian M]
    {c c' : ComplexShape ℤ} (e : c.Embedding c') [e.IsRelIff]
    {K : HomologicalComplex M c'} (hK : K.Acyclic)
    (hp : ∀ k, e.f (c.prev k) = c'.prev (e.f k))
    (hn : ∀ k, e.f (c.next k) = c'.next (e.f k)) :
    (K.restriction e).Acyclic := by
  intro k
  have ex : (K.sc (e.f k)).Exact := hK (e.f k)
  apply (ShortComplex.exact_iff_of_iso
    (restriction.sc'Iso K e (c.prev k) k (c.next k) (hp k) rfl (hn k) rfl rfl)).2
  exact ex

private theorem chain_acyclic_of_cochain {M : Type*} [Category* M] [Abelian M]
    {E : CochainComplex M ℤ} (hE : E.Acyclic) :
    (E.restriction downToUp).Acyclic :=
  restriction_acyclic downToUp hE
    (fun k ↦ by rw [ChainComplex.prev, CochainComplex.prev]; change -(k + 1) = -k - 1; omega)
    (fun k ↦ by rw [ChainComplex.next, CochainComplex.next]; change -(k - 1) = -k + 1; omega)

private theorem cochain_acyclic_of_chain {M : Type*} [Category* M] [Abelian M]
    {E : ChainComplex M ℤ} (hE : E.Acyclic) :
    (E.restriction upToDown).Acyclic :=
  restriction_acyclic upToDown hE
    (fun k ↦ by rw [CochainComplex.prev, ChainComplex.prev]; change -(k - 1) = -k + 1; omega)
    (fun k ↦ by rw [CochainComplex.next, ChainComplex.next]; change -(k + 1) = -k - 1; omega)

private def underlyingInt : ModuleCat.{v} Aᵐᵒᵖ ⥤ ModuleCat.{max u v} ℤ where
  obj M := ModuleCat.of ℤ (ULift.{u} M)
  map f := ModuleCat.ofHom
    (ULift.moduleEquiv.symm.toLinearMap.comp
      (f.hom.toAddMonoidHom.toIntLinearMap.comp ULift.moduleEquiv.toLinearMap))
  map_id _ := by ext x; rfl
  map_comp _ _ := by ext x; rfl

private instance : (underlyingInt (A := A)).PreservesZeroMorphisms where
  map_zero _ _ := by ext x; rfl

private theorem underlyingInt_acyclic {C : ChainComplex (ModuleCat.{v} Aᵐᵒᵖ) ℤ} (hC : C.Acyclic) :
    ((underlyingInt.mapHomologicalComplex (ComplexShape.down ℤ)).obj C).Acyclic := by
  intro k
  apply (ShortComplex.moduleCat_exact_iff _).2
  intro x hx
  obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff (C.sc k)).1 (hC k) x.down
    (congrArg ULift.down hx)
  exact ⟨⟨y⟩, congrArg ULift.up hy⟩

private def chainTranslation (n : ℤ) :
    (ComplexShape.down ℤ).Embedding (ComplexShape.down ℤ) :=
  ComplexShape.embeddingDown'Add (1 : ℤ) n

private instance (n : ℤ) : (chainTranslation n).IsRelIff :=
  inferInstanceAs ((ComplexShape.embeddingDown'Add (1 : ℤ) n).IsRelIff)

private theorem translated_acyclic {C : TensorChains.{z}} (hC : C.Acyclic) (n : ℤ) :
    (C.restriction (chainTranslation n)).Acyclic :=
  restriction_acyclic _ hC
    (fun k ↦ by rw [ChainComplex.prev, ChainComplex.prev]; change k + 1 + n = k + n + 1; omega)
    (fun k ↦ by rw [ChainComplex.next, ChainComplex.next]; change k - 1 + n = k + n - 1; omega)

private abbrev sphereChain (n : ℤ) : CoefficientChains A :=
  (sphere A n).restriction downToUp

private theorem sphereChain_isZero (n j : ℤ) (h : j ≠ -n) :
    IsZero ((sphereChain (A := A) n).X j) :=
  isZero_single_obj_X (ComplexShape.up ℤ) n (ModuleCat.of A A) (-j) (by omega)

private def sphereChain_regular (n : ℤ) :
    (sphereChain (A := A) n).X (-n) ≅ ModuleCat.of A A :=
  (sphere A n).restrictionXIso downToUp (Int.neg_neg n) ≪≫ singleObjXSelf _ _ _

private theorem tensorSphere_inclusion_isIso (C : ChainComplex (ModuleCat.{v} Aᵐᵒᵖ) ℤ) (n k : ℤ) :
    IsIso ((tensorBicomplex C (sphereChain n)).ιTotal (ComplexShape.down ℤ)
      (k + n) (-n) k (show k + n + -n = k by omega)) := by
  let K := tensorBicomplex C (sphereChain n)
  let c := ComplexShape.down ℤ
  have hk : k + n + -n = k := by omega
  let i := K.ιTotal c (k + n) (-n) k hk
  classical
  let s := K.totalDesc (c₁₂ := c) (i₁₂ := k)
    (fun p q h ↦ if hq : q = -n then
      eqToHom (congrArg₂ (fun a b ↦ (K.X a).X b) (show p = k + n by
        change p + q = k at h
        omega) hq)
      else 0)
  have hs : i ≫ s = 𝟙 _ := by
    dsimp only [i, s]
    rw [HomologicalComplex₂.ι_totalDesc]
    simp
  refine ⟨⟨s, hs, ?_⟩⟩
  apply HomologicalComplex₂.total.hom_ext
  intro p q h
  change p + q = k at h
  by_cases hq : q = -n
  · subst q
    have hp : p = k + n := by omega
    subst p
    change i ≫ s ≫ i = i ≫ 𝟙 _
    rw [← Category.assoc, hs, Category.id_comp, Category.comp_id]
  · have hz : IsZero ((K.X p).X q) :=
      (leftTensorFunctor (R := A) (C.X p)).map_isZero (sphereChain_isZero n q hq)
    exact hz.eq_of_src _ _

private def tensorSphereComponent (C : ChainComplex (ModuleCat.{v} Aᵐᵒᵖ) ℤ) (n k : ℤ) :
    (underlyingInt (A := A)).obj (C.X (k + n)) ≅ (tensorTotal C (sphereChain n)).X k :=
  (AddEquiv.ulift.trans (rightUnit (R := A) (A := C.X (k + n))).symm).toIntLinearEquiv.toModuleIso ≪≫
    (leftTensorFunctor (R := A) (C.X (k + n))).mapIso (sphereChain_regular n).symm ≪≫
    (@asIso _ _ _ _
      ((tensorBicomplex C (sphereChain n)).ιTotal (ComplexShape.down ℤ)
        (k + n) (-n) k (show k + n + -n = k by omega))
      (tensorSphere_inclusion_isIso C n k))

/-- Tensoring with a sphere of the regular module translates the underlying complex. -/
private theorem tensorSphere_acyclic (E : RightCochains.{u,v} A) (hE : E.Acyclic) (n : ℤ) :
    ((tensorCochainFunctor E).obj (sphere A n)).Acyclic := by
  let C := E.restriction downToUp
  let D := sphereChain (A := A) n
  apply cochain_acyclic_of_chain (E := tensorTotal C D)
  have hC : C.Acyclic := chain_acyclic_of_cochain hE
  let U : ModuleCat.{v} Aᵐᵒᵖ ⥤ ModuleCat.{max u v} ℤ := underlyingInt
  suffices e : ((U.mapHomologicalComplex (ComplexShape.down ℤ)).obj C).restriction
      (chainTranslation n) ≅ tensorTotal C D from
    fun k ↦ (translated_acyclic (underlyingInt_acyclic hC) n k).of_iso e
  refine HomologicalComplex.Hom.isoOfComponents (tensorSphereComponent C n) ?_
  intro i j hij
  change j + 1 = i at hij
  let c := ComplexShape.down ℤ
  let e := (sphereChain_regular (A := A) n).inv
  let K := tensorBicomplex C D
  apply ModuleCat.hom_ext
  ext x
  change (tensorTotal C D).d i j
      (tensorInclusion C D (i + n) (-n) i (by omega) (tmul A x.down (e 1))) =
    tensorInclusion C D (j + n) (-n) j (by omega)
      (tmul A ((C.d (i + n) (j + n)).hom x.down) (e 1))
  have dz : D.d (-n) (-n - 1) = 0 :=
    single_obj_d (ComplexShape.up ℤ) n (ModuleCat.of A A) _ _
  have hv : (K.X (i + n)).d (-n) (-n - 1) = 0 :=
    ((leftTensorFunctor (R := A) (C.X (i + n))).map_zero _ _).symm ▸
      congrArg ((leftTensorFunctor (R := A) (C.X (i + n))).map) dz
  have hd : K.ιTotal c (i + n) (-n) i (by change i + n + -n = i; omega) ≫
      (K.total c).d i j =
    (K.d (i + n) (j + n)).f (-n) ≫
      K.ιTotal c (j + n) (-n) j (by change j + n + -n = j; omega) := by
    change _ ≫ (K.D₁ c i j + K.D₂ c i j) = _
    rw [Preadditive.comp_add, K.ι_D₁, K.ι_D₂,
      K.d₁_eq c (show c.Rel (i + n) (j + n) by change j + n + 1 = i + n; omega)
        (-n) j (by change j + n + -n = j; omega),
      K.d₂_eq' c (i + n) (show c.Rel (-n) (-n - 1) by change -n - 1 + 1 = -n; omega),
      hv, zero_comp, smul_zero, add_zero]
    exact one_smul (ℤˣ) _
  exact congrArg (fun f ↦ f.hom (tmul A x.down (e 1))) hd

private instance exactColimits_intModule (J : Type j₀) [Category.{j₁} J]
    [HasColimitsOfShape J (ModuleCat.{z} ℤ)] [HasColimitsOfShape J AddCommGrpCat.{z}]
    [HasExactColimitsOfShape J AddCommGrpCat.{z}] :
    HasExactColimitsOfShape J (ModuleCat.{z} ℤ) :=
  HasExactColimitsOfShape.domain_of_functor J (forget₂ (ModuleCat.{z} ℤ) AddCommGrpCat.{z})

private theorem tensorSphereCoproduct_acyclic (E : RightCochains.{u,v} A) (hE : E.Acyclic)
    {K : Type u} (degree : K → ℤ) :
    ((tensorCochainFunctor E).obj (∐ (fun i ↦ sphere A (degree i)))).Acyclic := by
  let F := Discrete.functor (fun i ↦ sphere A (degree i))
  let : AB4OfSize.{u} AddCommGrpCat.{max u v} := AB4OfSize_shrink _
  exact acyclic_of_colimit (Discrete K) (F := F ⋙ tensorCochainFunctor E)
    (isColimitOfPreserves (tensorCochainFunctor E) (colimit.isColimit F))
    (fun i ↦ tensorSphere_acyclic E hE (degree i.as))

theorem iCellCokernel_isKFlat (A : Type u) [Ring A] {X Y : Cochains A} (f : X ⟶ Y)
    (hf : iCell A f) : IsKFlat.{u,v} A (cokernel f) := by
  intro E hE
  obtain ⟨F, ι, hz, ⟨hc⟩, _, hstep⟩ := iCellCokernel_filtration A f hf
  let T := tensorCochainFunctor E
  have hstage : ∀ n, (T.obj (F.obj n)).Acyclic := by
    intro n
    induction n with
    | zero =>
      exact acyclic_of_isZero _ (T.map_isZero hz)
    | succ n ih =>
      obtain ⟨hg, K, degree, ⟨e⟩⟩ := hstep n
      let g := F.map (homOfLE (Nat.le_succ n))
      have hq := tensorSphereCoproduct_acyclic E hE degree
      exact (tensorCochain_cokernel_shortExact E g hg).acyclic_X₂ ih
        (fun k ↦ (hq k).of_iso (T.mapIso e.symm))
  exact acyclic_of_colimit ℕ (F := F ⋙ T) (isColimitOfPreserves T hc) hstage

end

end DerivedFormalization.Model.Complexes
