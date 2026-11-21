import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.KunnethOppositeInterchange
import MathGenome.Internal.AlgebraCore.P103.Ch11.TorBalance

namespace P103.Ch11.KunnethOppositeInterchange
open CategoryTheory
open P103.BalancedTensor
open P103.Specs.Ch02.FlatnessTests
open P103.Specs.Ch10.Complexes
open P103.Specs.Ch10.Comparison
open P103.Specs.Ch10.TotalComplexAssembly
open P103.Specs.Ch11.ExtTorDefinitions
open P103.Specs.Ch11.TorBalance
open P103.Specs.Ch11.KunnethOppositeInterchange
noncomputable section
universe u v w t
variable {R : Type u} [Ring R]

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[simp] theorem tensorFlip_tmul (A : Type v) (B : Type w)
    [AddCommGroup A] [Module Rᵐᵒᵖ A] [AddCommGroup B] [Module R B] (a : A) (b : B) :
    letI := doubleOppositeModule R B
    tensorFlip A B (tmul R a b) = tmul Rᵐᵒᵖ b a := rfl

@[simp] theorem tensorFlip_symm_tmul (A : Type v) (B : Type w)
    [AddCommGroup A] [Module Rᵐᵒᵖ A] [AddCommGroup B] [Module R B] (a : A) (b : B) :
    letI := doubleOppositeModule R B
    (tensorFlip A B).symm (tmul Rᵐᵒᵖ b a) = tmul R a b := rfl

/-- Scalar transport preserves the finite-relations characterization of flatness. -/
theorem flat_doubleOpposite (M : Type v) [AddCommGroup M] [Module R M] :
    letI := doubleOppositeModule R M
    Flat.{u,v,w} R M ↔ Flat.{u,v,w} Rᵐᵒᵖᵐᵒᵖ M := by
  letI := doubleOppositeModule R M
  rw [P103.Ch02.FlatnessTests.flat_iff_finiteRelations,
    P103.Ch02.FlatnessTests.flat_iff_finiteRelations]
  constructor
  · intro h n k x r hr
    obtain ⟨l, y, s, hx, hs⟩ := h n k x (fun j i => (r j i).unop.unop) hr
    refine ⟨l, y, fun i a => MulOpposite.op (MulOpposite.op (s i a)), hx, ?_⟩
    intro j a
    apply (RingEquiv.opOp R).symm.injective
    simpa using hs j a
  · intro h n k x r hr
    obtain ⟨l, y, s, hx, hs⟩ := h n k x
      (fun j i => MulOpposite.op (MulOpposite.op (r j i))) hr
    refine ⟨l, y, fun i a => (s i a).unop.unop, hx, ?_⟩
    intro j a
    have he := congrArg (RingEquiv.opOp R).symm (hs j a)
    simpa using he

theorem flat_transport : flat_transportType.{u,v,w} := by
  intro R _ M _ _
  letI := doubleOppositeModule R M
  exact (flat_doubleOpposite (R := R) M).trans
    (P103.Ch02.FlatnessTests.rightFlat_iff_opposite Rᵐᵒᵖ M).symm

/-- In particular boundary flatness, not just flatness of the chain terms,
survives the change of side required by the source theorem. -/
theorem complex_transport : complex_transportType.{u,v,w} := by
  intro R _ D n
  refine ⟨fun _ => Iff.rfl, fun _ => Iff.rfl, flat_transport R (D.X n), ?_, ?_⟩
  · exact flat_transport R (cycles D n)
  · exact flat_transport R (boundaries D n)

/-- The unsigned opposite flip exchanges the two differential directions. -/
def bicomplexFlip
    (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (D : ChainComplex (ModuleCat.{w} R) ℤ) :
    tensorBicomplex C D ≅ (tensorBicomplex (doubleOppositeComplex D) C).flip where
  hom :=
    { f p :=
        { f q := ModuleCat.ofHom (tensorFlip (C.X p) (D.X q)).toLinearMap
          comm' q q' _ := by
            apply ModuleCat.hom_ext
            apply tensor_hom_ext
            intro a b
            rfl }
      comm' p p' _ := by
        apply HomologicalComplex.Hom.ext
        funext q
        apply ModuleCat.hom_ext
        apply tensor_hom_ext
        intro a b
        rfl }
  inv :=
    { f p :=
        { f q := ModuleCat.ofHom (tensorFlip (C.X p) (D.X q)).symm.toLinearMap
          comm' q q' _ := by
            apply ModuleCat.hom_ext
            apply tensor_hom_ext
            intro b a
            rfl }
      comm' p p' _ := by
        apply HomologicalComplex.Hom.ext
        funext q
        apply ModuleCat.hom_ext
        apply tensor_hom_ext
        intro b a
        rfl }
  hom_inv_id := by
    apply HomologicalComplex.Hom.ext
    funext p
    apply HomologicalComplex.Hom.ext
    funext q
    apply ModuleCat.hom_ext
    apply tensor_hom_ext
    intro a b
    rfl
  inv_hom_id := by
    apply HomologicalComplex.Hom.ext
    funext p
    apply HomologicalComplex.Hom.ext
    funext q
    apply ModuleCat.hom_ext
    apply tensor_hom_ext
    intro b a
    rfl

/-- Koszul interchange on arbitrary integer complexes over opposite rings. -/
def signedFlip (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (D : ChainComplex (ModuleCat.{w} R) ℤ) :
    tensorTotal C D ≅ tensorTotal (doubleOppositeComplex D) C :=
  HomologicalComplex₂.total.mapIso (bicomplexFlip C D) (ComplexShape.down ℤ) ≪≫
    signedInterchange (tensorBicomplex (doubleOppositeComplex D) C)

theorem signedFlip_formula
    (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (D : ChainComplex (ModuleCat.{w} R) ℤ)
    (p q n : ℤ) (h : p + q = n) (a : C.X p) (b : D.X q) :
    (signedFlip C D).hom.f n (tensorInclusion C D p q n h (tmul R a b)) =
      (p * q).negOnePow •
        tensorInclusion (doubleOppositeComplex D) C q p n (by omega) (tmul Rᵐᵒᵖ b a) := by
  have hmap := HomologicalComplex₂.ιTotal_map _ _ (bicomplexFlip C D).hom
    (ComplexShape.down ℤ) p q n h
  have hflip := P103.Ch10.TotalComplexAssembly.signedInterchange_chain
    (tensorBicomplex (doubleOppositeComplex D) C) q p n h
  have hm := congrArg (fun f => f.hom (tmul R a b)) hmap
  have hs := congrArg (fun f => f.hom (tmul Rᵐᵒᵖ b a)) hflip
  change ((signedInterchange (tensorBicomplex (doubleOppositeComplex D) C)).hom.f n).hom
    (((HomologicalComplex₂.total.map (bicomplexFlip C D).hom
      (ComplexShape.down ℤ)).f n).hom (tensorInclusion C D p q n h (tmul R a b))) = _
  change (((HomologicalComplex₂.total.map (bicomplexFlip C D).hom
      (ComplexShape.down ℤ)).f n).hom (tensorInclusion C D p q n h (tmul R a b))) =
    ((tensorBicomplex (doubleOppositeComplex D) C).flip.ιTotal
      (ComplexShape.down ℤ) p q n h).hom (tmul Rᵐᵒᵖ b a) at hm
  rw [hm]
  rw [mul_comm q p] at hs
  dsimp only [P103.Ch11.TorBalance.tensorBicomplex,
    P103.Ch10.TotalComplexAssembly.signedInterchange] at hs ⊢
  rcases Int.units_eq_one_or (p * q).negOnePow with hsign | hsign <;>
    simp [hsign, Units.smul_def, tensorInclusion, totalInclusion] at hs ⊢ <;>
    convert hs using 1

section Ordinary
open CategoryTheory.Limits

/-- Restricting scalars commutes with the shared extension by zero. -/
def doubleOppositeExtendXIso (D : ChainComplex (ModuleCat.{w} R) ℕ) :
    ∀ a, HomologicalComplex.extend.X (doubleOppositeComplex D) a ≅
      (doubleOppositeFunctor R).obj (HomologicalComplex.extend.X D a)
  | none => IsZero.iso (isZero_zero _)
      ((doubleOppositeFunctor R).map_isZero (isZero_zero _))
  | some _ => Iso.refl _

def doubleOppositeExtendIso (D : ChainComplex (ModuleCat.{w} R) ℕ) :
    extendNonnegativeChain (doubleOppositeComplex D) ≅
      doubleOppositeComplex (extendNonnegativeChain D) := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun p => doubleOppositeExtendXIso D (nonnegativeChainEmbedding.r p)) ?_
  intro i j _
  change (doubleOppositeExtendXIso D (nonnegativeChainEmbedding.r i)).hom ≫
      (doubleOppositeFunctor R).map (HomologicalComplex.extend.d D
        (nonnegativeChainEmbedding.r i) (nonnegativeChainEmbedding.r j)) =
    HomologicalComplex.extend.d (doubleOppositeComplex D)
      (nonnegativeChainEmbedding.r i) (nonnegativeChainEmbedding.r j) ≫
        (doubleOppositeExtendXIso D (nonnegativeChainEmbedding.r j)).hom
  cases nonnegativeChainEmbedding.r i <;> cases nonnegativeChainEmbedding.r j <;>
    simp [doubleOppositeExtendXIso, HomologicalComplex.extend.d]

theorem doubleOppositeExtendIso_retained (D : ChainComplex (ModuleCat.{w} R) ℕ) (n : ℕ) :
    ((doubleOppositeExtendIso D).hom.f (n : ℤ)) ≫
        (doubleOppositeFunctor R).map (D.extendXIso nonnegativeChainEmbedding (i := n) rfl).hom =
      ((doubleOppositeComplex D).extendXIso nonnegativeChainEmbedding (i := n) rfl).hom := by
  have aux (a : Option ℕ) (ha : a = some n) :
      (doubleOppositeExtendXIso D a).hom ≫
        (doubleOppositeFunctor R).map (HomologicalComplex.extend.XIso D ha).hom =
      (HomologicalComplex.extend.XIso (doubleOppositeComplex D) ha).hom := by
    subst a
    simp [doubleOppositeExtendXIso, HomologicalComplex.extend.XIso]
  exact aux _ (nonnegativeChainEmbedding.r_eq_some (i := n) rfl)

theorem doubleOppositeExtendIso_on_retained
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (n : ℕ) (b : D.X n) :
    ((doubleOppositeExtendIso D).hom.f (n : ℤ)).hom
      (((doubleOppositeComplex D).extendXIso nonnegativeChainEmbedding (i := n) rfl).inv.hom b) =
        (D.extendXIso nonnegativeChainEmbedding (i := n) rfl).inv.hom b := by
  apply (D.extendXIso nonnegativeChainEmbedding (i := n) rfl).toLinearEquiv.injective
  have h := congrArg (fun k => k.hom
      (((doubleOppositeComplex D).extendXIso nonnegativeChainEmbedding (i := n) rfl).inv.hom b))
    (doubleOppositeExtendIso_retained D n)
  change (D.extendXIso nonnegativeChainEmbedding (i := n) rfl).hom.hom
    (((doubleOppositeExtendIso D).hom.f (n : ℤ)).hom
      (((doubleOppositeComplex D).extendXIso nonnegativeChainEmbedding (i := n) rfl).inv.hom b)) =
    ((doubleOppositeComplex D).extendXIso nonnegativeChainEmbedding (i := n) rfl).hom.hom
      (((doubleOppositeComplex D).extendXIso nonnegativeChainEmbedding (i := n) rfl).inv.hom b) at h
  have hn := congrArg (fun k => k.hom b)
    ((doubleOppositeComplex D).extendXIso nonnegativeChainEmbedding (i := n) rfl).inv_hom_id
  have ho := congrArg (fun k => k.hom b)
    (D.extendXIso nonnegativeChainEmbedding (i := n) rfl).inv_hom_id
  exact h.trans (hn.trans ho.symm)

theorem doubleOppositeExtendIso_inv_on_retained
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (n : ℕ) (b : D.X n) :
    ((doubleOppositeExtendIso D).inv.f (n : ℤ)).hom
      ((D.extendXIso nonnegativeChainEmbedding (i := n) rfl).inv.hom b) =
        ((doubleOppositeComplex D).extendXIso nonnegativeChainEmbedding (i := n) rfl).inv.hom b := by
  have hh := congrArg ((doubleOppositeExtendIso D).inv.f (n : ℤ)).hom
    (doubleOppositeExtendIso_on_retained D n b)
  have hc := congrArg (fun f => f.f (n : ℤ)) (doubleOppositeExtendIso D).hom_inv_id
  have ha := congrArg (fun f => f.hom
      (((doubleOppositeComplex D).extendXIso nonnegativeChainEmbedding (i := n) rfl).inv.hom b)) hc
  exact hh.symm.trans ha

/-- Both tensor factors may be replaced by isomorphic complexes. -/
def tensorTotalIso {C C' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
    {D D' : ChainComplex (ModuleCat.{w} R) ℤ} (e : C ≅ C') (f : D ≅ D') :
    tensorTotal C D ≅ tensorTotal C' D' :=
  HomologicalComplex₂.total.mapIso
    { hom := tensorBicomplexMap e.hom f.hom
      inv := tensorBicomplexMap e.inv f.inv
      hom_inv_id := by
        rw [← P103.Ch11.TorBalance.tensorBicomplexMap_comp,
          e.hom_inv_id, f.hom_inv_id, P103.Ch11.TorBalance.tensorBicomplexMap_id]
      inv_hom_id := by
        rw [← P103.Ch11.TorBalance.tensorBicomplexMap_comp,
          e.inv_hom_id, f.inv_hom_id, P103.Ch11.TorBalance.tensorBicomplexMap_id] }
    (ComplexShape.down ℤ)

def ordinarySignedFlip (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) :
    ordinaryTotal C D ≅ ordinaryTotal (doubleOppositeComplex D) C :=
  (nonnegativeChainEmbedding.restrictionFunctor (ModuleCat ℤ)).mapIso
    (signedFlip (extendNonnegativeChain C) (extendNonnegativeChain D) ≪≫
      (tensorTotalIso (doubleOppositeExtendIso D) (Iso.refl (extendNonnegativeChain C))).symm)

theorem tensorTotalIso_inv_inclusion {C C' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
    {D D' : ChainComplex (ModuleCat.{w} R) ℤ} (e : C ≅ C') (f : D ≅ D')
    (p q n : ℤ) (h : p + q = n) (a : C'.X p) (b : D'.X q) :
    ((tensorTotalIso e f).inv.f n).hom (tensorInclusion C' D' p q n h (tmul R a b)) =
      tensorInclusion C D p q n h (tmul R ((e.inv.f p).hom a) ((f.inv.f q).hom b)) :=
  P103.Ch11.TorBalance.tensorTotalMap_inclusion e.inv f.inv p q n h a b

theorem ordinarySignedFlip_formula
    (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ) (D : ChainComplex (ModuleCat.{w} R) ℕ)
    (p q n : ℕ) (h : p + q = n) (a : C.X p) (b : D.X q) :
    ((ordinarySignedFlip C D).hom.f n).hom
      (ordinaryInclusion C D p q n h (tmul R a b)) =
      ((p : ℤ) * (q : ℤ)).negOnePow •
        ordinaryInclusion (doubleOppositeComplex D) C q p n (by omega) (tmul Rᵐᵒᵖ b a) := by
  change ((tensorTotalIso (doubleOppositeExtendIso D) (Iso.refl (extendNonnegativeChain C))).inv.f (n : ℤ)).hom
    (((signedFlip (extendNonnegativeChain C) (extendNonnegativeChain D)).hom.f (n : ℤ)).hom
      (tensorInclusion (extendNonnegativeChain C) (extendNonnegativeChain D) p q n
        (by exact_mod_cast h) (tmul R
          ((C.extendXIso nonnegativeChainEmbedding (i := p) rfl).inv.hom a)
          ((D.extendXIso nonnegativeChainEmbedding (i := q) rfl).inv.hom b)))) = _
  rw [signedFlip_formula, map_zsmul_unit,
    tensorTotalIso_inv_inclusion, doubleOppositeExtendIso_inv_on_retained]
  rfl

theorem ordinarySignedFlip_natural
    {C C' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ}
    {D D' : ChainComplex (ModuleCat.{w} R) ℕ} (f : C ⟶ C') (g : D ⟶ D') :
    ordinaryTotalMap f g ≫ (ordinarySignedFlip C' D').hom =
      (ordinarySignedFlip C D).hom ≫ ordinaryTotalMap (doubleOppositeMap g) f := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply P103.Ch11.TorBalance.ordinaryTotal_hom_ext C D n
  intro p q h a b
  change ((ordinarySignedFlip C' D').hom.f n).hom
      (((ordinaryTotalMap f g).f n).hom
        (ordinaryInclusion C D p q n h (tmul R a b))) =
    ((ordinaryTotalMap (doubleOppositeMap g) f).f n).hom
      (((ordinarySignedFlip C D).hom.f n).hom
        (ordinaryInclusion C D p q n h (tmul R a b)))
  rw [P103.Ch11.TorBalance.ordinaryTotalMap_inclusion, ordinarySignedFlip_formula,
    ordinarySignedFlip_formula, map_zsmul_unit,
    P103.Ch11.TorBalance.ordinaryTotalMap_inclusion]
  rfl

/-- Signed interchange is simultaneous natural on the actual total complexes
and on their quotient homology, including degree zero. -/
theorem signed_interchange : signed_interchangeType.{u,v,w} := by
  intro R _
  exact ⟨{
    iso := ordinarySignedFlip
    formula := ordinarySignedFlip_formula
    naturality := ordinarySignedFlip_natural
    homology_naturality := fun f g n =>
      P103.Ch11.TorBalance.homologyMap_square _ _ _ _ (ordinarySignedFlip_natural f g) n }⟩
end Ordinary

section Tor
variable {A : Type v} {B : Type w}
variable [AddCommGroup A] [Module Rᵐᵒᵖ A] [AddCommGroup B] [Module R B]

/-- The augmentation maps are determined by their component formulas. -/
theorem augmentations_unique {P : LeftResolution Rᵐᵒᵖ A} {Q : LeftResolution R B}
    (α β : Augmentations P Q) : α.left = β.left ∧ α.right = β.right := by
  constructor
  · apply HomologicalComplex.Hom.ext
    funext n
    apply P103.Ch11.TorBalance.ordinaryTotal_hom_ext P.complex Q.complex n
    intro p q h a b
    by_cases hq : q = 0
    · subst q
      simp only [Nat.add_zero] at h
      subst n
      rw [α.left_zero, β.left_zero]
    · exact (LinearMap.congr_fun (α.left_positive p q n h hq) (tmul R a b)).trans
        (LinearMap.congr_fun (β.left_positive p q n h hq) (tmul R a b)).symm
  · apply HomologicalComplex.Hom.ext
    funext n
    apply P103.Ch11.TorBalance.ordinaryTotal_hom_ext P.complex Q.complex n
    intro p q h a b
    by_cases hp : p = 0
    · subst p
      simp only [Nat.zero_add] at h
      cases h
      rw [α.right_zero, β.right_zero]
    · exact (LinearMap.congr_fun (α.right_positive p q n h hp) (tmul R a b)).trans
        (LinearMap.congr_fun (β.right_positive p q n h hp) (tmul R a b)).symm

/-- Hence balance has no dependence on a selection of augmentation maps. -/
theorem balanceEquiv_independent {P : LeftResolution Rᵐᵒᵖ A} {Q : LeftResolution R B}
    (α β : Augmentations P Q) (hαL : QuasiIsomorphism α.left)
    (hαR : QuasiIsomorphism α.right) (hβL : QuasiIsomorphism β.left)
    (hβR : QuasiIsomorphism β.right) (n : ℕ) :
    balanceEquiv α hαL hαR n = balanceEquiv β hβL hβR n := by
  obtain ⟨hL, hR⟩ := augmentations_unique α β
  apply LinearEquiv.ext
  intro x
  obtain ⟨z, rfl⟩ := (hαL n).surjective x
  rw [P103.Ch11.TorBalance.balanceEquiv_apply_left, hL,
    P103.Ch11.TorBalance.balanceEquiv_apply_left, hR]

/-- Unsigned interchange commutes with simultaneous coefficient and complex maps. -/
theorem tensorComplexFlip_natural
    {A A' : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    [AddCommGroup A'] [Module Rᵐᵒᵖ A'] (f : A →ₗ[Rᵐᵒᵖ] A')
    {D D' : ChainComplex (ModuleCat.{w} R) ℕ} (m : D ⟶ D') :
    leftTensorMap f m ≫ (tensorComplexFlip A' D').hom =
      (tensorComplexFlip A D).hom ≫
        tensorFirstMap (doubleOppositeMap m) A ≫
          tensorSecondMap (doubleOppositeComplex D') f := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply tensor_hom_ext
  intro a b
  rfl

def transportAugmentation (P : LeftResolution Rᵐᵒᵖ A) (Q : LeftResolution R B)
    (hP : P.IsProjective) (hQ : Q.IsProjective) : Augmentations P Q :=
  (P103.Ch11.TorBalance.balance R A B P Q hP hQ).choose

theorem transportAugmentation_quasi (P : LeftResolution Rᵐᵒᵖ A) (Q : LeftResolution R B)
    (hP : P.IsProjective) (hQ : Q.IsProjective) :
    QuasiIsomorphism (transportAugmentation P Q hP hQ).left ∧
      QuasiIsomorphism (transportAugmentation P Q hP hQ).right :=
  (P103.Ch11.TorBalance.balance R A B P Q hP hQ).choose_spec

/-- Balance followed by the unsigned opposite flip, in the forward direction. -/
def torForward (P : LeftResolution Rᵐᵒᵖ A) (Q : LeftResolution R B)
    (hP : P.IsProjective) (hQ : Q.IsProjective) (n : ℕ) :
    letI := doubleOppositeModule R B
    TorWith P B n ≃ₗ[ℤ] TorWith (doubleOppositeResolution Q) A n := by
  letI := doubleOppositeModule R B
  exact (balanceEquiv (transportAugmentation P Q hP hQ)
      (transportAugmentation_quasi P Q hP hQ).1
      (transportAugmentation_quasi P Q hP hQ).2 n).trans
    (((quotientHomology (ComplexShape.down ℕ) n).mapIso
      (tensorComplexFlip A Q.complex)).toLinearEquiv)

theorem torForward_normalization (P : LeftResolution Rᵐᵒᵖ A) (Q : LeftResolution R B)
    (hP : P.IsProjective) (hQ : Q.IsProjective) (n : ℕ)
    (α : Augmentations P Q) (hL : QuasiIsomorphism α.left) (hR : QuasiIsomorphism α.right) :
    torForward P Q hP hQ n = (balanceEquiv α hL hR n).trans
      (((quotientHomology (ComplexShape.down ℕ) n).mapIso
        (tensorComplexFlip A Q.complex)).toLinearEquiv) := by
  unfold torForward
  rw [balanceEquiv_independent _ α _ _ hL hR n]

theorem torForward_natural
    (A A' : ModuleCat.{v} Rᵐᵒᵖ) (B B' : ModuleCat.{w} R)
    (P : LeftResolution Rᵐᵒᵖ A) (P' : LeftResolution Rᵐᵒᵖ A')
    (Q : LeftResolution R B) (Q' : LeftResolution R B')
    (hP : P.IsProjective) (hP' : P'.IsProjective)
    (hQ : Q.IsProjective) (hQ' : Q'.IsProjective)
    (f : A ⟶ A') (g : B ⟶ B') (l : P.complex ⟶ P'.complex)
    (m : Q.complex ⟶ Q'.complex)
    (hl : ChainLift P P' f.hom l) (hm : ChainLift Q Q' g.hom m) (n : ℕ) :
    (torForward P' Q' hP' hQ' n).toLinearMap.comp
      (homologyMap (tensorFirstMap l B ≫ tensorSecondMap P'.complex g.hom) n) =
    (homologyMap (tensorFirstMap (doubleOppositeMap m) A ≫
      tensorSecondMap (doubleOppositeComplex Q'.complex) f.hom) n).comp
        (torForward P Q hP hQ n).toLinearMap := by
  have he := P103.Ch11.TorBalance.balanceEquiv_natural R A A' B B' P P' Q Q'
    f.hom g.hom l m hl hm
    (transportAugmentation P Q hP hQ) (transportAugmentation P' Q' hP' hQ')
    (transportAugmentation_quasi P Q hP hQ).1
    (transportAugmentation_quasi P Q hP hQ).2
    (transportAugmentation_quasi P' Q' hP' hQ').1
    (transportAugmentation_quasi P' Q' hP' hQ').2 n
  have hf := P103.Ch11.TorBalance.homologyMap_square _ _ _ _
    (tensorComplexFlip_natural f.hom m) n
  change (homologyMap (tensorComplexFlip A' Q'.complex).hom n).comp
    ((balanceEquiv (transportAugmentation P' Q' hP' hQ')
      (transportAugmentation_quasi P' Q' hP' hQ').1
      (transportAugmentation_quasi P' Q' hP' hQ').2 n).toLinearMap.comp _) = _
  rw [he, ← LinearMap.comp_assoc, hf]
  rfl

/-- Canonical Tor transport, normalized for every augmentation and natural for
all comparison lifts and changes of either projective model. -/
def torTransport (R : Type u) [Ring R] : TorTransport.{u,v,w} R where
  equiv A B P Q hP hQ n := (torForward P Q hP hQ n).symm
  normalization A B P Q hP hQ n α hL hR :=
    torForward_normalization P Q hP hQ n α hL hR
  naturality A A' B B' P P' Q Q' hP hP' hQ hQ' f g l m hl hm n := by
    apply LinearMap.ext
    intro x
    change (torForward P' Q' hP' hQ' n).symm
      (homologyMap (tensorFirstMap (doubleOppositeMap m) A ≫
        tensorSecondMap (doubleOppositeComplex Q'.complex) f.hom) n x) =
      homologyMap (tensorFirstMap l B ≫ tensorSecondMap P'.complex g.hom) n
        ((torForward P Q hP hQ n).symm x)
    apply (torForward P' Q' hP' hQ' n).injective
    have he := LinearMap.congr_fun
      (torForward_natural A A' B B' P P' Q Q' hP hP' hQ hQ' f g l m hl hm n)
      ((torForward P Q hP hQ n).symm x)
    change torForward P' Q' hP' hQ' n
      (homologyMap (tensorFirstMap l B ≫ tensorSecondMap P'.complex g.hom) n
        ((torForward P Q hP hQ n).symm x)) =
      homologyMap (tensorFirstMap (doubleOppositeMap m) A ≫
        tensorSecondMap (doubleOppositeComplex Q'.complex) f.hom) n
          (torForward P Q hP hQ n ((torForward P Q hP hQ n).symm x)) at he
    rw [LinearEquiv.apply_symm_apply] at he ⊢
    exact he.symm

theorem tor_transport : tor_transportType.{u,v,w} := by
  intro R _
  exact ⟨torTransport R⟩
end Tor

/-- The signed interchange has the augmentation square that fixes its induced
Tor comparison as the balanced, unsigned opposite-ring identification. -/
theorem signed_augmentation : signed_augmentationType.{u,v,w} := by
  intro R _ S A B P Q
  letI := doubleOppositeModule R B
  intro α β
  apply HomologicalComplex.Hom.ext
  funext n
  apply P103.Ch11.TorBalance.ordinaryTotal_hom_ext P.complex Q.complex n
  intro p q h a b
  change (β.left.f n).hom
    (((S.iso P.complex Q.complex).hom.f n).hom
      (ordinaryInclusion P.complex Q.complex p q n h (tmul R a b))) =
    (((tensorComplexFlip A Q.complex).hom.f n).hom
      ((α.right.f n).hom
        (ordinaryInclusion P.complex Q.complex p q n h (tmul R a b))))
  rw [S.formula, map_zsmul_unit]
  by_cases hp : p = 0
  · subst p
    have hn : q = n := by omega
    cases hn
    simp only [Nat.cast_zero, zero_mul, Int.negOnePow_zero, one_smul]
    change (β.left.f n).hom
      (ordinaryInclusion (doubleOppositeResolution Q).complex P.complex n 0 n
        (by omega) (tmul Rᵐᵒᵖ b a)) =
      ((tensorComplexFlip A Q.complex).hom.f n).hom
        ((α.right.f n).hom
          (ordinaryInclusion P.complex Q.complex 0 n n (by omega) (tmul R a b)))
    rw [β.left_zero, α.right_zero]
    rfl
  · have ha := LinearMap.congr_fun (α.right_positive p q n h hp) (tmul R a b)
    have hb := LinearMap.congr_fun (β.left_positive q p n (by omega) hp) (tmul Rᵐᵒᵖ b a)
    change (α.right.f n).hom
      (ordinaryInclusion P.complex Q.complex p q n h (tmul R a b)) = 0 at ha
    change (β.left.f n).hom
      (ordinaryInclusion (doubleOppositeComplex Q.complex) P.complex q p n (by omega)
        (tmul Rᵐᵒᵖ b a)) = 0 at hb
    rw [ha, hb, map_zero, smul_zero]

/-- Projectivity is preserved by the explicit double-opposite action. -/
theorem projective_doubleOpposite (M : Type w) [AddCommGroup M] [Module R M]
    (hM : Module.Projective R M) :
    letI := doubleOppositeModule R M
    Module.Projective Rᵐᵒᵖᵐᵒᵖ M := by
  letI := doubleOppositeModule R M
  letI := hM
  let σ := (RingEquiv.opOp R).toRingHom
  let σ' := (RingEquiv.opOp R).symm.toRingHom
  letI : RingHomInvPair σ σ' := ⟨rfl, rfl⟩
  letI : RingHomInvPair σ' σ := ⟨rfl, rfl⟩
  let e : M ≃ₛₗ[σ] M :=
    { toFun := id
      invFun := id
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  exact Module.Projective.of_equiv e

/-- The inverse scalar restriction also preserves projectivity. -/
theorem projective_recover (M : Type w) [AddCommGroup M] [Module Rᵐᵒᵖᵐᵒᵖ M]
    (hM : Module.Projective Rᵐᵒᵖᵐᵒᵖ M) :
    letI : Module R M := Module.compHom M (RingEquiv.opOp R).toRingHom
    Module.Projective R M := by
  letI : Module R M := Module.compHom M (RingEquiv.opOp R).toRingHom
  letI := hM
  let σ := (RingEquiv.opOp R).symm.toRingHom
  let σ' := (RingEquiv.opOp R).toRingHom
  letI : RingHomInvPair σ σ' := ⟨rfl, rfl⟩
  letI : RingHomInvPair σ' σ := ⟨rfl, rfl⟩
  let e : M ≃ₛₗ[σ] M :=
    { toFun := id
      invFun := id
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  exact Module.Projective.of_equiv e

/-- Scalar transport and its inverse recover the actual augmented resolution;
thus the construction covers every independently chosen opposite model. -/
theorem opposite_projective_models : opposite_projective_modelsType.{u,w} := by
  intro R _ B _ _
  letI := doubleOppositeModule R B
  intro S
  refine ⟨rfl, ?_⟩
  constructor
  · intro h n
    exact projective_recover (R := R) (S.complex.X n) (h n)
  · intro h n
    exact projective_doubleOpposite (R := R) ((recoverResolution S).complex.X n) (h n)

set_option maxHeartbeats 1600000 in
/-- Transport with arbitrary projective choices on both sides. -/
def allModelTorTransport (R : Type u) [Ring R] : AllModelTorTransport.{u,v,w} R where
  equiv A B P hP S hS n :=
    (torTransport R).equiv A B P (recoverResolution S) hP
      ((opposite_projective_models R B S).2.mp hS) n
  normalization A B P Q hP hQ n α hL hR :=
    (torTransport R).normalization A B P Q hP
      ((opposite_projective_models R B (doubleOppositeResolution Q)).2.mp hQ) n α hL hR
  naturality A A' B B' P P' hP hP' S S' hS hS' f g l m hl hm n := by
    letI := doubleOppositeModule R B
    letI := doubleOppositeModule R B'
    have hm' : ChainLift (recoverResolution S) (recoverResolution S') g.hom (recoverMap m) := by
      apply LinearMap.ext
      intro b
      exact LinearMap.congr_fun hm b
    exact (torTransport R).naturality A A' B B' P P' (recoverResolution S)
      (recoverResolution S') hP hP'
      ((opposite_projective_models R B S).2.mp hS)
      ((opposite_projective_models R B' S').2.mp hS') f g l (recoverMap m) hl hm' n

theorem tor_transport_all_models : tor_transport_all_modelsType.{u,v,w} := by
  intro R _
  exact ⟨allModelTorTransport R⟩

/-- On both sides arbitrary lifts of the same coefficient maps induce the
same Tor maps. Together with simultaneous naturality, this includes changes
of projective models and the canonical comparison identifications. -/
theorem tor_lifts_independent : tor_lifts_independentType.{u,v,w} := by
  intro R _ A A' B B' P P' hP
  letI := doubleOppositeModule R B
  letI := doubleOppositeModule R B'
  intro S S' hS f g l l' m m' hl hl' hm hm' n
  have hleft := P103.Ch10.Comparison.chain_homology_independent Rᵐᵒᵖ ℤ
    (tensorFunctor B) A A' P P' hP f.hom l l' n hl hl'
  have hleft' : homologyMap (tensorFirstMap l B) n =
      homologyMap (tensorFirstMap l' B) n := congrArg ModuleCat.Hom.hom hleft
  have hright := P103.Ch10.Comparison.chain_homology_independent Rᵐᵒᵖᵐᵒᵖ ℤ
    (tensorFunctor (R := Rᵐᵒᵖ) A) B B' S S' hS (doubleOppositeLinear g.hom) m m' n hm hm'
  have hright' : homologyMap (tensorFirstMap m A) n =
      homologyMap (tensorFirstMap m' A) n := congrArg ModuleCat.Hom.hom hright
  constructor
  · simp only [P103.Ch10.Complexes.homologyMap_comp, hleft']
  · simp only [P103.Ch10.Complexes.homologyMap_comp, hright']

set_option maxHeartbeats 1600000 in
/-- Scalar transport commutes with the actual maps on quotient homology. -/
theorem homology_scalar_natural : homology_scalar_naturalType.{u,v} := by
  intro R _ D D' g n z
  rfl

/-- The inverse opposite-ring flip is unsigned and simultaneous natural. -/
theorem unsigned_tensor : unsigned_tensorType.{u,v,w} := by
  intro R _ A A' B B' _ _ _ _ _ _ _ _ f g
  letI := doubleOppositeModule R B
  letI := doubleOppositeModule R B'
  refine ⟨fun _ _ => rfl, fun _ _ => rfl, ?_⟩
  apply tensor_hom_ext
  intro b a
  rfl

end
end P103.Ch11.KunnethOppositeInterchange
