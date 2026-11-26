import Specs.LinearAlgebraicGroups.Descent.AffineTorsorDescent
import LinearAlgebraicGroups.Flag.FppfTorsors
import Mathlib.CategoryTheory.Sites.LocalProperties
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Jacobson.Ring

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Fppf

open Specs.Fppf
open Algebra.TensorProduct (includeLeft includeRight)

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem nonemptySchemeTorsorCriterion : NonemptySchemeTorsorCriterion.{u} := by
  intro k _ H X a hX hft _hqc hi
  let f : X.left.left ⟶ Spec (CommRingCat.of k) := X.hom.left
  have : LocallyOfFiniteType f := hft
  have hf : IsFppf f :=
    ⟨inferInstance, ⟨fun y ↦ ⟨Classical.choice hX, Subsingleton.elim _ _⟩⟩, inferInstance⟩
  exact (representedTorsorCriterion H.property.2 a).2 ⟨hf, hi⟩

section AlgebraDescent

variable {k K B : Type u} [Field k] [Field K] [CommRing B]
  [Algebra k K] [Algebra k B] (i : K →ₐ[k] B) (ρ : B →ₐ[k] K ⊗[k] B)

private def invariantAlgebra : Subalgebra k B :=
  ρ.equalizer includeRight

private abbrev recoveredAlgebraMap : K ⊗[k] invariantAlgebra ρ →ₐ[k] B :=
  Algebra.TensorProduct.productMap i (invariantAlgebra ρ).val

private theorem coefficient_invariant
    (h : ∀ b, Algebra.TensorProduct.map (AlgHom.id k K) ρ (ρ b) =
      Algebra.TensorProduct.map (AlgHom.id k K) includeRight (ρ b)) (b : B)
    {I : Type u} [DecidableEq I] (basis : Module.Basis I k K) (j : I) :
    TensorProduct.equivFinsuppOfBasisLeft basis (ρ b) j ∈ invariantAlgebra ρ := by
  change ρ _ = includeRight _
  have coeff (f : B →ₐ[k] K ⊗[k] B) (x : K ⊗[k] B) :
      TensorProduct.equivFinsuppOfBasisLeft basis
        (Algebra.TensorProduct.map (AlgHom.id k K) f x) j =
      f (TensorProduct.equivFinsuppOfBasisLeft basis x j) := by
    induction x using TensorProduct.inductionOn with
    | tmul a b => simp
    | add x y hx hy => simp [hx, hy]
  rw [← coeff ρ, h, coeff]

/-- The canonical map from the scalar extension of the equalizer to the original
algebra is bijective. The cocycle fixes the coefficients of each coaction value. -/
private theorem recoveredAlgebra_bijective
    (hi : ∀ a : K, ρ (i a) = (a ⊗ₜ[k] (1 : B)))
    (hc : ∀ b, Algebra.TensorProduct.productMap i (AlgHom.id k B) (ρ b) = b)
    (ha : ∀ b, Algebra.TensorProduct.map (AlgHom.id k K) ρ (ρ b) =
      Algebra.TensorProduct.map (AlgHom.id k K) includeRight (ρ b)) :
    Function.Bijective (recoveredAlgebraMap i ρ) := by
  classical
  let basis := Module.Free.chooseBasis k K
  let C := invariantAlgebra ρ
  let mapIn : K ⊗[k] C →ₐ[k] K ⊗[k] B :=
    Algebra.TensorProduct.map (AlgHom.id k K) C.val
  have hcoeff (x : K ⊗[k] C) (j : Module.Free.ChooseBasisIndex k K) :
      TensorProduct.equivFinsuppOfBasisLeft basis (mapIn x) j =
      (TensorProduct.equivFinsuppOfBasisLeft basis x j : B) := by
    induction x using TensorProduct.inductionOn with
    | tmul a b => simp [mapIn]
    | add x y hx hy => simp [hx, hy]
  have hcomp (x : K ⊗[k] C) : ρ (recoveredAlgebraMap i ρ x) = mapIn x := by
    induction x using TensorProduct.inductionOn with
    | tmul a b =>
      have hb : ρ (b : B) = includeRight (b : B) := b.property
      simp [recoveredAlgebraMap, hi, hb, mapIn, Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy => simp [hx, hy]
  constructor
  · intro x y h
    apply (TensorProduct.equivFinsuppOfBasisLeft basis).injective
    ext j
    exact (hcoeff x j).symm.trans (congrArg (fun z ↦
      TensorProduct.equivFinsuppOfBasisLeft basis z j) (by rw [← hcomp, ← hcomp, h]) |>.trans (hcoeff y j))
  · intro b
    let f : Module.Free.ChooseBasisIndex k K →₀ B :=
      TensorProduct.equivFinsuppOfBasisLeft basis (ρ b)
    let g : Module.Free.ChooseBasisIndex k K →₀ C :=
      ⟨f.support, fun j ↦ ⟨f j, coefficient_invariant ρ ha b basis j⟩,
        fun j ↦ by
          rw [Finsupp.mem_support_iff]
          exact not_congr ⟨fun h ↦ Subtype.ext h, fun h ↦ congrArg Subtype.val h⟩⟩
    let x := (TensorProduct.equivFinsuppOfBasisLeft basis).symm g
    have hx : mapIn x = ρ b := by
      apply (TensorProduct.equivFinsuppOfBasisLeft basis).injective
      ext j
      rw [hcoeff, LinearEquiv.apply_symm_apply]
      rfl
    have hm (y : K ⊗[k] C) :
        Algebra.TensorProduct.productMap i (AlgHom.id k B) (mapIn y) =
          recoveredAlgebraMap i ρ y := by
      induction y using TensorProduct.inductionOn with
      | tmul a b => simp [mapIn]
      | add y z hy hz => simp [hy, hz]
    exact ⟨x, by rw [← hm, hx, hc]⟩

end AlgebraDescent

section Schemes

variable (k : Type u) [Field k]

private abbrev fieldSite := Over (fieldBase k)

private abbrev fieldSiteEquiv : fieldSite k ≌ SchemeOver k :=
  Over.equivalenceOfIsTerminal Over.mkIdTerminal

private abbrev affineSpecFunctor : (CommAlgCat.{u} k)ᵒᵖ ⥤ fieldSite k :=
  algSpec (CommRingCat.of k) ⋙ (fieldSiteEquiv k).inverse

private abbrev affineTest (A : Type u) [CommRing A] [Algebra k A] : fieldSite k :=
  (affineSpecFunctor k).obj (op (CommAlgCat.of k A))

private def affineFullyFaithful : (affineSpecFunctor k).FullyFaithful :=
  (algSpec.fullyFaithful (R := CommRingCat.of k)).comp (fieldSiteEquiv k).fullyFaithfulInverse

private theorem fieldHom_left (T : fieldSite k) : T.hom.left = T.left.hom := by
  rw [Over.mkIdTerminal.hom_ext T.hom (Over.mkIdTerminal.from T.left)]
  exact Over.mkIdTerminal_from_left T.left

variable {k}

private abbrev affineMap {A B : Type u} [CommRing A] [Algebra k A] [CommRing B]
    [Algebra k B] (f : A →ₐ[k] B) : affineTest k B ⟶ affineTest k A :=
  (affineSpecFunctor k).map (CommAlgCat.ofHom f).op

private theorem affineMap_comp {A B C : Type u} [CommRing A] [Algebra k A] [CommRing B]
    [Algebra k B] [CommRing C] [Algebra k C] (f : A →ₐ[k] B) (g : B →ₐ[k] C) :
    affineMap (g.comp f) = affineMap g ≫ affineMap f := by
  exact (affineSpecFunctor k).map_comp (CommAlgCat.ofHom g).op (CommAlgCat.ofHom f).op

private theorem affineMap_injective {A B : Type u} [CommRing A] [Algebra k A] [CommRing B]
    [Algebra k B] : Function.Injective (@affineMap k _ A B _ _ _ _) := by
  intro f g h
  have h' := (affineFullyFaithful k).map_injective
    (show (affineSpecFunctor k).map (CommAlgCat.ofHom f).op =
      (affineSpecFunctor k).map (CommAlgCat.ofHom g).op from h)
  exact congrArg CommAlgCat.Hom.hom (Quiver.Hom.op_inj h')

private def affineRingMap {A B : Type u} [CommRing A] [Algebra k A] [CommRing B]
    [Algebra k B] (f : affineTest k B ⟶ affineTest k A) : A →ₐ[k] B :=
  ((affineFullyFaithful k).preimage f).unop.hom

@[simp] private theorem affineMap_affineRingMap {A B : Type u} [CommRing A] [Algebra k A]
    [CommRing B] [Algebra k B] (f : affineTest k B ⟶ affineTest k A) :
    affineMap (affineRingMap f) = f :=
  (affineFullyFaithful k).map_preimage f

private def affineTensorProduct (A B : Type u) [CommRing A] [Algebra k A] [CommRing B]
    [Algebra k B] :
    IsLimit (BinaryFan.mk (affineMap (includeLeft (R := k) (S := k) (A := A) (B := B)))
      (affineMap (includeRight (R := k) (A := A) (B := B)))) :=
  by
    apply mapIsLimitOfPreservesOfIsLimit (fieldSiteEquiv k).inverse
    letI : PreservesLimitsOfSize.{0, 0} (algSpec (CommRingCat.of k)) :=
      (algΓAlgSpecAdjunction (CommRingCat.of k)).rightAdjoint_preservesLimits
    apply mapIsLimitOfPreservesOfIsLimit (algSpec (CommRingCat.of k))
    exact BinaryCofan.IsColimit.op
      (CommAlgCat.binaryCofanIsColimit (CommAlgCat.of k A) (CommAlgCat.of k B))

private theorem covers_singleton {V W : fieldSite k} (f : V ⟶ W)
    (hf : IsFppf f.left.left) :
    Sieve.generate (Presieve.singleton f) ∈ torsorTopology (fieldBase k) W := by
  obtain ⟨hflat, hsurj, hfp⟩ := hf
  change Sieve.overEquiv W.left (Sieve.overEquiv W (Sieve.generate (Presieve.singleton f))) ∈
    Scheme.fppfTopology W.left.left
  refine Scheme.fppfTopology.superset_covering ?_
    (Precoverage.generate_mem_toGrothendieck f.left.left.singleton_mem_fppfPrecoverage)
  apply (Sieve.generate_le_iff _ _).2
  intro Z g hg
  cases hg
  rw [Sieve.overEquiv_generate, Sieve.overEquiv_generate]
  exact Sieve.le_generate _ _ _ ⟨_, f.left, 𝟙 _,
    ⟨_, f, 𝟙 _, Presieve.singleton_self f, by simp⟩, by simp⟩

private theorem field_extension_fppf (K : Type u) [Field K] [Algebra k K] [Module.Finite k K] :
    IsFppf (affineTest k K).hom.left := by
  rw [fieldHom_left k]
  let f : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) := fieldSpecMap k K
  have : LocallyOfFiniteType f :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2
      (RingHom.finiteType_algebraMap.2 inferInstance)
  exact (show IsFppf f from ⟨inferInstance,
    ⟨fun y ↦ ⟨default, Subsingleton.elim _ _⟩⟩, inferInstance⟩)

private structure SplittingField {H : Specs.GroupScheme k} (P : FppfTorsor (fieldBase k) H) where
  K : Type u
  [field : Field K]
  [algebra : Algebra k K]
  finite : Module.Finite k K
  section_ : P.val.Section (affineTest k K)

/-- Restrict a section on a member of the fppf cover to a closed point of one
of its nonempty affine opens. Zariski's lemma gives a finite residue extension. -/
private theorem exists_splittingField {H : Specs.GroupScheme k} (P : FppfTorsor (fieldBase k) H) :
    Nonempty (SplittingField P) := by
  let T := fieldTest k
  let R := P.val.sectionSieve T
  let R' := Sieve.overEquiv T R
  let R'' := Sieve.overEquiv T.left R'
  have h : R'' ∈ Scheme.fppfTopology (Spec (CommRingCat.of k)) := P.property.2 T
  let : Scheme.fppfPrecoverage.HasIsos := ⟨fun f _ ↦ f.singleton_mem_fppfPrecoverage⟩
  obtain ⟨V, hV, hle⟩ := (Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition
    (J := Scheme.fppfPrecoverage)).1 h
  obtain ⟨𝒰, rfl⟩ := Precoverage.mem_iff_exists_zeroHypercover.mp hV
  let 𝒱 : (Spec (CommRingCat.of k)).Cover
    (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) := 𝒰
  obtain ⟨j, y, _⟩ := 𝒱.exists_eq (default : Spec (CommRingCat.of k))
  let W := 𝒱.X j
  let f := 𝒱.f j
  have hf := 𝒱.map_prop j
  have hR : R'' f := hle _ _ (𝒰.toPreZeroHypercover.presieve₀_f j)
  let W₀ := W.affineCover.X (W.affineCover.idx y)
  let e := W₀.isoSpec
  let A := Γ(W₀, ⊤)
  let v : Spec A ⟶ W := e.inv ≫ W.affineCover.f (W.affineCover.idx y)
  have : Nonempty W₀ := by
    obtain ⟨z, _⟩ := W.affineCover.covers y
    exact ⟨z⟩
  have : Nonempty (Spec A) := ⟨e.hom (Classical.choice ‹Nonempty W₀›)⟩
  have : Nontrivial A := PrimeSpectrum.nonempty_iff_nontrivial.mp ‹Nonempty (Spec A)›
  have : LocallyOfFinitePresentation (v ≫ f) := by
    have : LocallyOfFinitePresentation f := hf.2
    have : IsOpenImmersion v := inferInstance
    infer_instance
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (v ≫ f)
  let : Algebra k A := φ.hom.toAlgebra
  have : Algebra.FiniteType k A := by
    apply RingHom.finiteType_algebraMap.1
    change φ.hom.FiniteType
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1
      (hφ.symm ▸ inferInstanceAs (LocallyOfFiniteType (v ≫ f)))
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  let : m.IsMaximal := hm
  let K := A ⧸ m
  let : Field K := Ideal.Quotient.field m
  have hK : Algebra.FiniteType k K :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k m) Ideal.Quotient.mk_surjective
  let t : Spec (CommRingCat.of K) ⟶ W :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk m)) ≫ v
  have ht : t ≫ f = fieldSpecMap k K := by
    dsimp only [t]
    rw [Category.assoc, ← hφ, ← Spec.map_comp]
    rfl
  let b : affineTest k K ⟶ T := Over.mkIdTerminal.from _
  have hb : R'' b.left.left := by
    have hb' : b.left.left = fieldSpecMap k K := by
      rw [show b.left = (affineTest k K).hom from Over.mkIdTerminal_from_left _]
      exact fieldHom_left k _
    rw [hb', ← ht]
    exact R''.downward_closed hR t
  have hb' : R' b.left := by
    have h' := (Sieve.overEquiv_symm_iff R'' b.left).2 hb
    rwa [show (Sieve.overEquiv T.left).symm R'' = R' from
      (Sieve.overEquiv T.left).symm_apply_apply R'] at h'
  have hs : R b := by
    have h' := (Sieve.overEquiv_symm_iff R' b).2 hb'
    rwa [show (Sieve.overEquiv T).symm R' = R from
      (Sieve.overEquiv T).symm_apply_apply R] at h'
  obtain ⟨s⟩ := hs
  exact ⟨{ K := K, finite := finite_of_finite_type_of_isJacobsonRing k K, section_ := s }⟩

variable {H : Specs.GroupScheme k} {P : SchemeAction (fieldBase k) H}

private theorem restriction_comp {V W Z : fieldSite k} (f : V ⟶ W) (g : W ⟶ Z)
    (x : P.Section Z) : P.res (f ≫ g) x = P.res f (P.res g x) := by
  change (P.sheaf.obj.map (f ≫ g).op) x = _
  rw [op_comp, Functor.map_comp]
  rfl

/-- The universal pair consisting of a map to the cover and a section of the sheaf. -/
private structure Chart (P : SchemeAction (fieldBase k) H) {U Y : fieldSite k} (q : Y ⟶ U) where
  section_ : P.Section Y
  bijective : ∀ W : fieldSite k,
    Function.Bijective (fun f : W ⟶ Y ↦ (f ≫ q, P.res f section_))

private def Chart.lift {U Y W : fieldSite k} {q : Y ⟶ U} (c : Chart P q)
    (a : W ⟶ U) (s : P.Section W) : W ⟶ Y :=
  (c.bijective W).2 (a, s) |>.choose

@[simp] private theorem Chart.lift_q {U Y W : fieldSite k} {q : Y ⟶ U} (c : Chart P q)
    (a : W ⟶ U) (s : P.Section W) : c.lift a s ≫ q = a :=
  congrArg Prod.fst ((c.bijective W).2 (a, s) |>.choose_spec)

@[simp] private theorem Chart.lift_res {U Y W : fieldSite k} {q : Y ⟶ U} (c : Chart P q)
    (a : W ⟶ U) (s : P.Section W) : P.res (c.lift a s) c.section_ = s :=
  congrArg Prod.snd ((c.bijective W).2 (a, s) |>.choose_spec)

private theorem Chart.hom_ext {U Y W : fieldSite k} {q : Y ⟶ U} (c : Chart P q)
    {f g : W ⟶ Y} (hq : f ≫ q = g ≫ q) (hs : P.res f c.section_ = P.res g c.section_) :
    f = g :=
  (c.bijective W).1 (Prod.ext hq hs)

private abbrev groupTest (H : Specs.GroupScheme k) : fieldSite k :=
  (fieldSiteEquiv k).inverse.obj H.X

private def groupPoint {W : fieldSite k} (f : W ⟶ groupTest H) :
    (groupSections (fieldBase k) H).obj (op W) := ⟨f.left⟩

private theorem groupPoint_bijective (W : fieldSite k) :
    Function.Bijective (groupPoint (H := H) (W := W)) := by
  exact Equiv.ulift.symm.bijective.comp
    ((fieldSiteEquiv k).fullyFaithfulFunctor.homEquiv : (W ⟶ groupTest H) ≃ (W.left ⟶ H.X)).bijective

private def torsorChart (hP : IsTorsor P) {U Y : fieldSite k} (x : P.Section U)
    {q : Y ⟶ U} {p : Y ⟶ groupTest H} (hp : IsLimit (BinaryFan.mk q p)) : Chart P q where
  section_ := P.act (P.res q x) (groupPoint p)
  bijective W := by
    classical
    have key (f : W ⟶ Y) :
        P.res f (P.act (P.res q x) (groupPoint p)) =
          P.act (P.res (f ≫ q) x) (groupPoint (f ≫ p)) := by
      calc
        _ = P.act (P.res f (P.res q x)) (groupPoint (f ≫ p)) :=
          P.map_act f (P.res q x) (groupPoint p)
        _ = _ := by rw [restriction_comp]
    constructor
    · intro f g h
      have hq : f ≫ q = g ≫ q := congrArg Prod.fst h
      have hs := congrArg Prod.snd h
      change P.res f (P.act (P.res q x) (groupPoint p)) =
        P.res g (P.act (P.res q x) (groupPoint p)) at hs
      rw [key, key, hq] at hs
      exact BinaryFan.IsLimit.hom_ext hp hq
        (groupPoint_bijective W |>.injective (hP.1 _ _ |>.injective hs))
    · rintro ⟨a, s⟩
      obtain ⟨z, hz⟩ := (hP.1 W (P.res a x)).surjective s
      obtain ⟨b, rfl⟩ := (groupPoint_bijective W).surjective z
      let f := BinaryFan.IsLimit.lift hp a b
      have hq : f ≫ q = a := BinaryFan.IsLimit.lift_fst hp a b
      have hs : f ≫ p = b := BinaryFan.IsLimit.lift_snd hp a b
      refine ⟨f, Prod.ext hq ?_⟩
      change P.res f (P.act (P.res q x) (groupPoint p)) = s
      exact (key f).trans (by rw [hq, hs, hz])

/-- A binary product over the terminal test object, viewed on underlying schemes. -/
private theorem product_isPullback {X U Y : fieldSite k} {q : Y ⟶ U} {r : Y ⟶ X}
    (hp : IsLimit (BinaryFan.mk q r)) :
    IsPullback q.left.left r.left.left U.hom.left X.hom.left := by
  have hl := mapIsLimitOfPreservesOfIsLimit (fieldSiteEquiv k).functor q r hp
  rw [fieldHom_left k U, fieldHom_left k X]
  exact Over.isPullback_of_binaryFan_isLimit _ hl

private abbrev tensorFst (A B : Type u) [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] :
    affineTest k (A ⊗[k] B) ⟶ affineTest k A :=
  affineMap (includeLeft (S := k))

private abbrev tensorSnd (A B : Type u) [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] :
    affineTest k (A ⊗[k] B) ⟶ affineTest k B :=
  affineMap includeRight

private theorem affineMap_id (A : Type u) [CommRing A] [Algebra k A] :
    affineMap (AlgHom.id k A) = 𝟙 (affineTest k A) :=
  (affineSpecFunctor k).map_id _

section CoordinateChart

variable {K B : Type u} [Field K] [Algebra k K] [CommRing B] [Algebra k B]
variable (i : K →ₐ[k] B) (c : Chart P (affineMap i))

/-- Change the choice of map to the cover, keeping the section fixed. -/
private def changeChart : affineTest k (K ⊗[k] B) ⟶ affineTest k B :=
  c.lift (tensorFst K B) (P.res (tensorSnd K B) c.section_)

private def chartCoaction : B →ₐ[k] K ⊗[k] B :=
  affineRingMap (changeChart i c)

private theorem chartCoaction_scalar :
    (chartCoaction i c).comp i = includeLeft := by
  apply affineMap_injective
  rw [affineMap_comp]
  change affineMap (affineRingMap (changeChart i c)) ≫ affineMap i = tensorFst K B
  rw [affineMap_affineRingMap]
  exact c.lift_q _ _

private theorem chartCoaction_counit (b : B) :
    Algebra.TensorProduct.productMap i (AlgHom.id k B) (chartCoaction i c b) = b := by
  let m := Algebra.TensorProduct.productMap i (AlgHom.id k B)
  have h : m.comp (chartCoaction i c) = AlgHom.id k B := by
    apply affineMap_injective
    rw [affineMap_comp, affineMap_id]
    change affineMap m ≫ affineMap (affineRingMap (changeChart i c)) = _
    rw [affineMap_affineRingMap]
    apply c.hom_ext
    · rw [Category.assoc, changeChart, c.lift_q, Category.id_comp]
      change affineMap m ≫ affineMap (includeLeft (S := k)) = affineMap i
      rw [← affineMap_comp, Algebra.TensorProduct.productMap_left]
    · rw [restriction_comp, changeChart, c.lift_res, ← restriction_comp]
      congr 1
      change affineMap m ≫ affineMap includeRight = 𝟙 (affineTest k B)
      rw [← affineMap_comp, Algebra.TensorProduct.productMap_right, affineMap_id]
  exact DFunLike.congr_fun h b

private theorem chartCoaction_cocycle (b : B) :
    Algebra.TensorProduct.map (AlgHom.id k K) (chartCoaction i c) (chartCoaction i c b) =
      Algebra.TensorProduct.map (AlgHom.id k K) includeRight (chartCoaction i c b) := by
  let ρ := chartCoaction i c
  let l := Algebra.TensorProduct.map (AlgHom.id k K) ρ
  let r := Algebra.TensorProduct.map (AlgHom.id k K)
    (includeRight (R := k) (A := K) (B := B))
  have he : affineMap ρ = changeChart i c := affineMap_affineRingMap _
  have hp₁ : affineMap l ≫ tensorSnd K B = tensorSnd K (K ⊗[k] B) ≫ changeChart i c := by
    change affineMap l ≫ affineMap includeRight = affineMap includeRight ≫ changeChart i c
    rw [← he, ← affineMap_comp, ← affineMap_comp, Algebra.TensorProduct.map_comp_includeRight]
  have hp₂ : affineMap r ≫ tensorSnd K B = tensorSnd K (K ⊗[k] B) ≫ tensorSnd K B := by
    change affineMap r ≫ affineMap includeRight = affineMap includeRight ≫ affineMap includeRight
    rw [← affineMap_comp, ← affineMap_comp, Algebra.TensorProduct.map_comp_includeRight]
  have h : l.comp ρ = r.comp ρ := by
    apply affineMap_injective
    rw [affineMap_comp, affineMap_comp, he]
    apply c.hom_ext
    · simp only [Category.assoc, changeChart, c.lift_q]
      change affineMap l ≫ affineMap (includeLeft (S := k)) =
        affineMap r ≫ affineMap (includeLeft (S := k))
      rw [← affineMap_comp, ← affineMap_comp, Algebra.TensorProduct.map_comp_includeLeft,
        Algebra.TensorProduct.map_comp_includeLeft]
    · simp only [restriction_comp, changeChart, c.lift_res]
      rw [← restriction_comp, ← restriction_comp, hp₁, hp₂]
      simp only [restriction_comp, changeChart, c.lift_res]
  exact DFunLike.congr_fun h b

end CoordinateChart

section Glue

variable {X U Y : fieldSite k} {q : Y ⟶ U} {r : Y ⟶ X}

private theorem chart_cover (hp : IsLimit (BinaryFan.mk q r)) (hU : IsFppf U.hom.left) :
    IsFppf r.left.left := by
  have pb := product_isPullback hp
  exact ⟨MorphismProperty.of_isPullback (P := @Flat) pb hU.1,
    MorphismProperty.of_isPullback (P := @Surjective) pb hU.2.1,
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) pb hU.2.2⟩

private theorem cover_coversTop (hU : IsFppf U.hom.left) :
    (torsorTopology (fieldBase k)).CoversTop (fun _ : Unit ↦ U) := by
  let T := fieldTest k
  let f : U ⟶ T := Over.mkIdTerminal.from U
  have hf : IsFppf f.left.left := by
    change IsFppf (Over.mkIdTerminal.from U).left.left
    rw [Over.mkIdTerminal_from_left]
    exact hU
  apply ((torsorTopology (fieldBase k)).coversTop_iff_of_isTerminal T Over.mkIdTerminal (fun _ : Unit ↦ U)).2
  refine (torsorTopology (fieldBase k)).superset_covering ?_ (covers_singleton f hf)
  apply (Sieve.generate_le_iff _ _).2
  intro Z g hg
  cases hg
  exact ⟨(), ⟨𝟙 U⟩⟩

/-- Glue the universal section and test the resulting representation over the
same cover on which the chart represents the sheaf. -/
private theorem glue_chart (c : Chart P q) (hp : IsLimit (BinaryFan.mk q r))
    (hU : IsFppf U.hom.left)
    (hc : ∀ {W : fieldSite k} (f g : W ⟶ Y), f ≫ r = g ≫ r →
      P.res f c.section_ = P.res g c.section_) :
    Nonempty (representedSheaf X ≅ P.sheaf) := by
  have hs := ((isSheaf_iff_isSheaf_of_type _ _).1 P.sheaf.property).isSheafFor
    (Presieve.singleton r) (covers_singleton r (chart_cover hp hU))
  obtain ⟨s, hs, _⟩ := Presieve.isSheafFor_singleton.1 hs c.section_ hc
  let f : representedSheaf X ⟶ P.sheaf := ⟨{
    app W := ↾fun t ↦ P.res (t.down : W.unop ⟶ X) s
    naturality W V g := by
      apply ConcreteCategory.hom_ext
      intro t
      change P.res (g.unop ≫ t.down) s = P.res g.unop (P.res t.down s)
      exact restriction_comp _ _ _ }⟩
  have hres : P.res r s = c.section_ := hs
  have hmap : IsIso f := by
    apply Sheaf.isIso_of_coversTop (cover_coversTop hU)
    intro j
    rw [← ObjectProperty.isIso_hom_iff, NatTrans.isIso_iff_isIso_app]
    intro W
    rw [isIso_iff_bijective]
    let V := W.unop.left
    let a : V ⟶ U := W.unop.hom
    change Function.Bijective (fun t : ULift (V ⟶ X) ↦ P.res t.down s)
    constructor
    · intro t₁ t₂ ht
      let g₁ := BinaryFan.IsLimit.lift hp a t₁.down
      let g₂ := BinaryFan.IsLimit.lift hp a t₂.down
      have h₁ : g₁ ≫ r = t₁.down := BinaryFan.IsLimit.lift_snd hp _ _
      have h₂ : g₂ ≫ r = t₂.down := BinaryFan.IsLimit.lift_snd hp _ _
      have he : g₁ = g₂ := c.hom_ext
        ((BinaryFan.IsLimit.lift_fst hp _ _).trans (BinaryFan.IsLimit.lift_fst hp _ _).symm) (by
          rw [← hres, ← restriction_comp, ← restriction_comp, h₁, h₂]
          exact ht)
      exact ULift.ext (h₁.symm.trans ((congrArg (· ≫ r) he).trans h₂))
    · intro t
      let g := c.lift a t
      refine ⟨⟨g ≫ r⟩, ?_⟩
      change P.res (g ≫ r) s = t
      rw [restriction_comp, hres]
      exact c.lift_res a t
  exact ⟨asIso f⟩

end Glue

/-- Descend the locally representing spectrum by the equalizer of the two
coordinate maps on the double overlap. -/
private theorem affine_chart_descent
    {K B : Type u} [Field K] [Algebra k K] [CommRing B] [Algebra k B]
    (i : K →ₐ[k] B) (c : Chart P (affineMap i))
    (hU : IsFppf (affineTest k K).hom.left) :
    ∃ (X : fieldSite k) (r : affineTest k B ⟶ X),
      Nonempty (IsLimit (BinaryFan.mk (affineMap i) r)) ∧
      IsAffine X.left.left ∧ Nonempty (representedSheaf X ≅ P.sheaf) := by
  let ρ := chartCoaction i c
  let C := invariantAlgebra ρ
  let r := affineMap C.val
  let m := recoveredAlgebraMap i ρ
  have hm : Function.Bijective m :=
    recoveredAlgebra_bijective i ρ (DFunLike.congr_fun (chartCoaction_scalar i c))
      (chartCoaction_counit i c) (chartCoaction_cocycle i c)
  have : IsIso (CommAlgCat.ofHom m) := (ConcreteCategory.isIso_iff_bijective (CommAlgCat.ofHom m)).2 hm
  have : IsIso (affineMap m) := by
    change IsIso ((affineSpecFunctor k).map (CommAlgCat.ofHom m).op)
    infer_instance
  have h₁ : affineMap m ≫ tensorFst K C = affineMap i := by
    change affineMap m ≫ affineMap (includeLeft (S := k)) = affineMap i
    rw [← affineMap_comp, Algebra.TensorProduct.productMap_left]
  have h₂ : affineMap m ≫ tensorSnd K C = r := by
    change affineMap m ≫ affineMap includeRight = r
    rw [← affineMap_comp, Algebra.TensorProduct.productMap_right]
  let hp : IsLimit (BinaryFan.mk (affineMap i) r) :=
    (affineTensorProduct (k := k) K C).ofIsoLimit
      (BinaryFan.ext (asIso (affineMap m)).symm
        (by
          change tensorFst K C = (asIso (affineMap m)).inv ≫ affineMap i
          rw [← h₁]
          exact ((asIso (affineMap m)).inv_hom_id_assoc _).symm)
        (by
          change tensorSnd K C = (asIso (affineMap m)).inv ≫ r
          rw [← h₂]
          exact ((asIso (affineMap m)).inv_hom_id_assoc _).symm))
  refine ⟨affineTest k C, r, ⟨hp⟩, inferInstanceAs (IsAffine (Spec (CommRingCat.of C))), glue_chart c hp hU ?_⟩
  intro W f g hfg
  have hEq : changeChart i c ≫ r = tensorSnd K B ≫ r := by
    rw [← affineMap_affineRingMap (changeChart i c)]
    change affineMap ρ ≫ affineMap C.val = affineMap includeRight ≫ affineMap C.val
    rw [← affineMap_comp, ← affineMap_comp]
    exact congrArg affineMap (AlgHom.ext fun x : C ↦ x.property)
  let d := BinaryFan.IsLimit.lift (affineTensorProduct (k := k) K B) (g ≫ affineMap i) f
  have hd₁ : d ≫ tensorFst K B = g ≫ affineMap i :=
    BinaryFan.IsLimit.lift_fst (affineTensorProduct (k := k) K B) _ _
  have hd₂ : d ≫ tensorSnd K B = f :=
    BinaryFan.IsLimit.lift_snd (affineTensorProduct (k := k) K B) _ _
  have hg : d ≫ changeChart i c = g := by
    apply BinaryFan.IsLimit.hom_ext hp
    · change (d ≫ changeChart i c) ≫ affineMap i = g ≫ affineMap i
      rw [Category.assoc, changeChart, c.lift_q, hd₁]
    · change (d ≫ changeChart i c) ≫ r = g ≫ r
      rw [Category.assoc, hEq, ← Category.assoc, hd₂, hfg]
  rw [← hg, restriction_comp, changeChart, c.lift_res, ← restriction_comp, hd₂]

theorem affineTorsorRepresentability : AffineTorsorRepresentability.{u} := by
  intro k _ H P
  obtain ⟨D⟩ := exists_splittingField P
  let K := D.K
  let : Field K := D.field
  let : Algebra k K := D.algebra
  have : Module.Finite k K := D.finite
  have x : P.val.Section (affineTest k K) := D.section_
  obtain ⟨A, ⟨e⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).2 H.property.1
  let B := K ⊗[k] A.unop
  let i : K →ₐ[k] B := includeLeft
  let e' : affineTest k A.unop ≅ groupTest H.val := (fieldSiteEquiv k).inverse.mapIso e
  let p : affineTest k B ⟶ groupTest H.val := tensorSnd K A.unop ≫ e'.hom
  let hp : IsLimit (BinaryFan.mk (affineMap i) p) :=
    BinaryFan.isLimitCompRightIso _ e'.hom (affineTensorProduct (k := k) K A.unop)
  let c := torsorChart P.property x hp
  have hU := field_extension_fppf (k := k) K
  obtain ⟨X, r, ⟨hX⟩, haff, ⟨eP⟩⟩ := affine_chart_descent i c hU
  obtain ⟨a, eAction, _⟩ := representSheafAction P.val X eP
  have hnonempty : Nonempty X.left.left :=
    ⟨((c.lift (𝟙 _) x ≫ r).left.left)
      (default : Spec (CommRingCat.of K))⟩
  let Q : MorphismProperty Scheme.{u} := @Surjective ⊓ @Flat ⊓ @QuasiCompact
  have hq : Q (affineTest k K).hom.left := by
    refine ⟨⟨hU.2.1, hU.1⟩, ?_⟩
    rw [fieldHom_left k]
    exact inferInstanceAs (QuasiCompact (fieldSpecMap k K))
  have pbX := product_isPullback hX
  have pbH := product_isPullback hp
  rw [fieldHom_left k (groupTest H.val)] at pbH
  have hft : LocallyOfFiniteType X.hom.left :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @LocallyOfFiniteType) (Q := Q)
      pbX hq (MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) pbH.flip H.property.2.1)
  have hqc : QuasiCompact X.hom.left := by
    rw [fieldHom_left k]
    let f : X.left.left ⟶ Spec (CommRingCat.of k) := X.left.hom
    have : IsAffine X.left.left := haff
    exact (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact) (f := f)).2
      (inferInstanceAs (CompactSpace X.left.left))
  refine ⟨X, a, ⟨eAction⟩, hnonempty, haff, hft, hqc, fun hsm ↦ ?_⟩
  exact MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth) (Q := Q)
    pbX hq (MorphismProperty.of_isPullback (P := @Smooth) pbH.flip hsm)

end Schemes

end
end LinearAlgebraicGroups.Fppf
