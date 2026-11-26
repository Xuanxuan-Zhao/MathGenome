import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.DerivedProjectionDescent
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.RelativeFormComparison
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AdjointBorelCohomology
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuasiSplitInducedWeilProduct
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite WithConv
open scoped TensorProduct

universe u

namespace LinearAlgebraicGroups.Arithmetic.DerivedProjectionDescent

open _root_.LinearAlgebraicGroups.Specs
open Specs.Arithmetic.DerivedProjectionDescent
open Specs.AutomorphismSequence (relativePoints restrictIso)
open Specs.RelativeFormComparison (fieldTest fieldMap IsInduced transportedAut)
open private relativeYoneda relativeYonedaIso relativeYonedaFullyFaithful
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AutomorphismSequence
open private schemeIsoEquiv induced_iff
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.RelativeFormComparison

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 550000

theorem comparisonUniqueness : ComparisonUniqueness.{u} := by
  intro F K _ _ _ V W
  let e := schemeIsoEquiv K V W
  refine ⟨fun v => ⟨e v, (induced_iff v (e v)).mpr rfl, ?_⟩,
    fun r => ⟨e.symm r, (induced_iff (e.symm r) r).mpr (e.apply_symm_apply r), ?_⟩⟩
  · intro r hr
    exact ((induced_iff v r).mp hr).symm
  · intro v hv
    exact e.injective (((induced_iff v r).mp hv).trans (e.apply_symm_apply r).symm)

section Relative

variable {F K : Type u} [Field F] [Field K] [Algebra F K]

local notation "B" => groupBaseChange F K
local notation "T" => fieldTest F K
local notation "Y" => relativeYoneda T

private def relativeMap {V W : GroupScheme F} (a : (B).obj V ⟶ (B).obj W) :
    relativePoints V T ⟶ relativePoints W T :=
  (relativeYonedaIso T V).inv ≫ (Y).map a ≫ (relativeYonedaIso T W).hom

private theorem relativeMap_comp {V W J : GroupScheme F}
    (a : (B).obj V ⟶ (B).obj W) (b : (B).obj W ⟶ (B).obj J) :
    relativeMap (a ≫ b) = relativeMap a ≫ relativeMap b := by
  simp only [relativeMap, Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]

set_option maxHeartbeats 1500000 in
private theorem relativeMap_injective {V W : GroupScheme F}
    (a b : (B).obj V ⟶ (B).obj W) (h : relativeMap a = relativeMap b) : a = b := by
  let i := relativeYonedaIso T V
  let j := relativeYonedaIso T W
  have he := congrArg (fun f : relativePoints V T ⟶ relativePoints W T =>
    i.hom ≫ f ≫ j.inv) h
  change i.hom ≫ (i.inv ≫ (Y).map a ≫ j.hom) ≫ j.inv =
    i.hom ≫ (i.inv ≫ (Y).map b ≫ j.hom) ≫ j.inv at he
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id] at he
  exact (relativeYonedaFullyFaithful T).map_injective he

private theorem relativeMap_iso {V W : GroupScheme F} (a : (B).obj V ≅ (B).obj W)
    (r : relativePoints V T ≅ relativePoints W T) (h : IsInduced F K a r) :
    relativeMap a.hom = r.hom :=
  congrArg Iso.hom ((induced_iff a r).mp h)

private theorem relativeMap_ground {V W : GroupScheme F} (a : V ⟶ W) :
    relativeMap ((B).map a) = Functor.whiskerLeft (Over.forget T).op (yonedaGrp.map a) := by
  apply NatTrans.ext
  funext U
  apply GrpCat.ext
  intro x
  apply Over.OverMorphism.ext
  change pullback.lift x.left U.unop.hom.left _ ≫
      ((baseChange F K).map a.hom.hom).left ≫ pullback.fst W.X.hom (fieldSpecMap F K) =
    x.left ≫ a.hom.hom.left
  simp only [baseChange, Over.pullback_map_left, pullback.lift_fst, pullback.lift_fst_assoc]

private theorem restrict_groundMap {V W : GroupScheme F} (a : V ⟶ W) (σ : Gal(K/F)) :
    Functor.whiskerLeft (Over.map (fieldMap F K σ)).op (relativeMap ((B).map a)) =
      relativeMap ((B).map a) := by
  rw [relativeMap_ground]
  apply NatTrans.ext
  funext U
  rfl

theorem displacementSquare : DisplacementSquare.{u} := by
  intro F K _ _ _ _ _ V₀ W₀ V W u₀ u v w h vR wR hv hw σ dV dW hdV hdW
  let bc := groupBaseChange F K
  let a := relativeMap (bc.map u₀)
  let b := relativeMap (bc.map u)
  have h₀ : a ≫ wR.hom = vR.hom ≫ b := by
    have he := congrArg relativeMap h
    simpa only [relativeMap_comp, relativeMap_iso v vR hv, relativeMap_iso w wR hw] using he
  have hσ : a ≫ (restrictIso (fieldMap F K σ) wR).hom =
      (restrictIso (fieldMap F K σ) vR).hom ≫ b := by
    have he := congrArg (Functor.whiskerLeft (Over.map (fieldMap F K σ)).op) h₀
    dsimp only [a, b, bc] at he
    rw [Functor.whiskerLeft_comp, Functor.whiskerLeft_comp,
      restrict_groundMap (F := F) (K := K) u₀ σ,
      restrict_groundMap (F := F) (K := K) u σ] at he
    exact he
  have hinv : b ≫ wR.inv = vR.inv ≫ a := by
    rw [← cancel_epi vR.hom, ← Category.assoc, ← h₀, Category.assoc,
      wR.hom_inv_id, Category.comp_id, vR.hom_inv_id_assoc]
  apply relativeMap_injective (F := F) (K := K)
  rw [relativeMap_comp, relativeMap_comp, relativeMap_iso dV _ hdV, relativeMap_iso dW _ hdW]
  change a ≫ (restrictIso (fieldMap F K σ) wR).hom ≫ wR.inv =
    ((restrictIso (fieldMap F K σ) vR).hom ≫ vR.inv) ≫ a
  rw [← Category.assoc, hσ, Category.assoc, hinv, Category.assoc]

end Relative

section Coordinates

open Descent (HopfDescentDatum SemilinearAction)
open Descent.Forms (spectrumIso)
open Specs.AdjointCocharacters (coordinateHopfIso coordinateHopfMap)
local notation "coordinates" => Specs.AdjointCocharacters.coordinateHopf
open Specs.QuasiSplitInducedWeilProduct (ProductDescent IsCoordinateProduct)
open Specs.RelativeFormComparison (HopfConjugates)
open private spectrumIsoEquiv standard baseHom_equivariant
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.Forms
open private hopfSchemeIso hopfIsoEquiv hopfIsoEquiv_apply hopfIsoEquiv_trans hopfInduced_iff
  restrict_hopfIso conjugates_exists from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.RelativeFormComparison
open private extendedGroupIso extendedSpecIso_hom_fst specGroupMap_comp specGroupMap_injective
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
open private extendedCoordinateIso extendedCoordinateIso_natural
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AdjointBorelCohomology
open private productPointsEquiv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuasiSplitInducedWeilProduct
open private actionRingHom from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AffineGroups

variable {F K I : Type u} [Field F] [Field K] [Algebra F K]

local notation "E" => groupBaseChange F K

private theorem inverseSquare {C : Type*} [Category C] {A B P Q : C}
    (e : A ≅ B) (s : P ≅ Q) {p : A ⟶ P} {q : B ⟶ Q}
    (h : p ≫ s.hom = e.hom ≫ q) : e.inv ≫ p = q ≫ s.inv := by
  rw [← cancel_mono s.hom, Category.assoc, h, Iso.inv_hom_id_assoc,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Pullback preserves products of group schemes, as it preserves limits
on the underlying schemes and the forgetful functors create products. -/
private def extendedProduct [Finite I] {G S : GroupScheme F} {π : I → (G ⟶ S)}
    (h : IsLimit (Fan.mk G π)) :
    IsLimit (Fan.mk ((E).obj G) (fun i => (E).map (π i))) := by
  let U := Grp.forget (SchemeOver F)
  let V := Grp.forget (SchemeOver K)
  let bc := baseChange F K
  let P : Fan (fun _ : I => S) := Fan.mk G π
  let P' : Fan (fun _ : I => (E).obj S) := Fan.mk ((E).obj G) (fun i => (E).map (π i))
  have h₀ := (Fan.isLimitMapConeEquiv U _ P) (isLimitOfPreserves U h)
  let Q : Fan (fun _ : I => S.X) := Fan.mk G.X (fun i => U.map (π i))
  have h₁ := (Fan.isLimitMapConeEquiv bc _ Q) (isLimitOfPreserves bc h₀)
  exact isLimitOfReflects V ((Fan.isLimitMapConeEquiv V _ P').symm h₁)

private def productOfComparison {C : Type*} [Category C] {A B S T : C}
    {p : I → (A ⟶ S)} {q : I → (B ⟶ T)}
    (h : IsLimit (Fan.mk B q)) (e : A ≅ B) (s : S ≅ T)
    (he : ∀ i, p i ≫ s.hom = e.hom ≫ q i) :
    IsLimit (Fan.mk A p) := by
  refine Fan.IsLimit.mk _ (fun c =>
    Fan.IsLimit.lift h (fun i => c.proj i ≫ s.hom) ≫ e.inv) ?_ ?_
  · intro c i
    rw [fan_mk_proj, ← cancel_mono s.hom, Category.assoc, Category.assoc, he,
      Iso.inv_hom_id_assoc]
    exact Fan.IsLimit.fac h _ i
  · intro c m hm
    apply (cancel_mono e.hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply Fan.IsLimit.hom_ext h
    intro i
    rw [Fan.IsLimit.fac, fan_mk_proj, Category.assoc, ← he, ← Category.assoc]
    exact congrArg (fun z => z ≫ s.hom) (hm i)

/-- The actual scheme projections give the universal product property on all
test algebras. -/
private theorem coordinateProduct [Finite I]
    {A : HopfAlgebraCategory K} {C : I → HopfAlgebraCategory K}
    (p : ∀ i, C i ⟶ A)
    (h : IsLimit (Fan.mk (specGroup A) (fun i => specGroupMap (p i)))) :
    IsCoordinateProduct p := by
  obtain ⟨e, _, he⟩ := LinearAlgebraicGroups.hopfSpecPoints K
  intro R
  let φ (D : HopfAlgebraCategory K) : (D →ₐ[K] R) ≃
      ((groupPointsFunctor K).obj (specGroup D)).obj R :=
    (WithConv.equiv _).symm.trans ((e D).app R).groupIsoToMulEquiv.toEquiv
  let ψ := productPointsEquiv _ h R
  let χ := (φ A).trans (ψ.toEquiv.trans (Equiv.piCongrRight fun i => (φ (C i)).symm))
  have hχ (x : A →ₐ[K] R) : χ x = fun i => x.comp (p i).hom.toAlgHom := by
    funext i
    apply (φ (C i)).injective
    change φ (C i) ((φ (C i)).symm
        (((groupPointsFunctor K).map (specGroupMap (p i))).app R (φ A x))) =
      φ (C i) (x.comp (p i).hom.toAlgHom)
    rw [Equiv.apply_symm_apply]
    exact (he (p i) R (toConv x)).symm
  exact (show (fun (x : A →ₐ[K] R) i => x.comp (p i).hom.toAlgHom) = χ from
    funext fun x => (hχ x).symm) ▸ χ.bijective

private theorem coordinateProjection_injective {A : HopfAlgebraCategory K}
    {B : I → HopfAlgebraCategory K} {p : ∀ i, B i ⟶ A} (hp : IsCoordinateProduct p) (i : I) :
    Function.Injective (p i).hom := by
  classical
  let x (j : I) : B j →ₐ[K] B i :=
    if h : j = i then h ▸ AlgHom.id K (B j)
    else (Algebra.ofId K (B i)).comp (Bialgebra.counitAlgHom K (B j))
  obtain ⟨f, hf⟩ := (hp (CommAlgCat.of K (B i))).surjective x
  have hi : f.comp (p i).hom.toAlgHom = AlgHom.id K (B i) := by
    simpa [x] using congrFun hf i
  intro y z he
  exact (DFunLike.congr_fun hi y).symm.trans ((congrArg f he).trans (DFunLike.congr_fun hi z))

/-- An equality of coordinate subalgebras restricts the semilinear
automorphism of the product to a ring equivalence of the two factors. -/
private def coordinateTransport {A : HopfAlgebraCategory K}
    (D : HopfDescentDatum F A) {B : I → HopfAlgebraCategory K}
    (p : ∀ i, B i ⟶ A) {i j : I}
    (hi : Function.Injective (p i).hom) (hj : Function.Injective (p j).hom)
    (σ : Gal(K/F))
    (h : D.action.act σ '' Set.range (p i).hom = Set.range (p j).hom) :
    { e : B i ≃+* B j //
      ∀ x, (p j).hom (e x) = D.action.act σ ((p i).hom x) } := by
  classical
  let f := (actionRingHom D σ).comp (p i).hom.toAlgHom.toRingHom
  have hmem (x : B i) : ∃ y : B j, (p j).hom y = f x := by
    change f x ∈ Set.range (p j).hom
    rw [← h]
    exact ⟨_, ⟨x, rfl⟩, rfl⟩
  let g : B i → B j := fun x => (hmem x).choose
  have hg (x : B i) : (p j).hom (g x) = f x := (hmem x).choose_spec
  let q : B i →+* B j :=
    { toFun := g
      map_one' := hj (by simp only [hg, map_one])
      map_mul' := fun x y => hj (by simp only [hg, map_mul])
      map_zero' := hj (by simp only [hg, map_zero])
      map_add' := fun x y => hj (by simp only [hg, map_add]) }
  have hq : Function.Bijective q := by
    refine ⟨fun x y he => hi ((D.action.act σ).injective ?_), ?_⟩
    · change f x = f y
      rw [← hg, ← hg]
      exact congrArg (p j).hom he
    · intro z
      have hz : (p j).hom z ∈ D.action.act σ '' Set.range (p i).hom :=
        h.symm ▸ ⟨z, rfl⟩
      obtain ⟨_, ⟨x, rfl⟩, hx⟩ := hz
      exact ⟨x, hj ((hg x).trans hx)⟩
  exact ⟨RingEquiv.ofBijective q hq, hg⟩

private def productDescentOfStableProjections [MulAction Gal(K/F) I]
    (A : HopfAlgebraCategory F) (B : I → HopfAlgebraCategory K)
    (hB : ∀ i, Algebra.FiniteType K (B i))
    (p : ∀ i, B i ⟶ extendedHopf K A) (hp : IsCoordinateProduct p)
    (hperm : ∀ σ i, (SemilinearAction.scalarExtension (K := K) A).act σ ''
      Set.range (p i).hom = Set.range (p (σ • i)).hom) :
    ProductDescent (F := F) (K := K) (I := I) := by
  let D := standard K A
  let e (σ : Gal(K/F)) (i j : I) (h : σ • i = j) :=
    coordinateTransport D p (coordinateProjection_injective hp i) (coordinateProjection_injective hp j)
      σ (h ▸ hperm σ i)
  refine
    { total := extendedHopf K A
      factor := B
      finiteType := hB
      projection := p
      product := hp
      datum := D
      transport := fun σ i j h => (e σ i j h).val
      transportProjection := fun σ i j h => (e σ i j h).property
      transportScalar := ?_
      descent := ⟨A, Iso.refl _, by intros; rfl⟩ }
  intro σ i j h r
  apply coordinateProjection_injective hp j
  rw [(e σ i j h).property]
  change D.action.act σ ((p i).hom.toAlgHom (algebraMap K (B i) r)) =
    (p j).hom.toAlgHom (algebraMap K (B j) (σ r))
  rw [(p i).hom.toAlgHom.commutes, (p j).hom.toAlgHom.commutes]
  change D.action.act σ (algebraMap K (extendedHopf K A) r) =
    algebraMap K (extendedHopf K A) (σ r)
  rw [Algebra.algebraMap_eq_smul_one, D.action.map_smul, D.map_one,
    Algebra.algebraMap_eq_smul_one]

private def inversePullbackIso {A B : HopfAlgebraCategory K} {P Q : GroupScheme K}
    (f : specGroup A ≅ P) (g : specGroup B ≅ Q) (e : P ≅ Q) : A ≅ B :=
  (spectrumIsoEquiv A B).symm (f ≪≫ e ≪≫ g.symm)

private theorem inversePullbackIso_spec {A B : HopfAlgebraCategory K} {P Q : GroupScheme K}
    (f : specGroup A ≅ P) (g : specGroup B ≅ Q) (e : P ≅ Q) :
    spectrumIso (inversePullbackIso f g e) = f ≪≫ e ≪≫ g.symm :=
  (spectrumIsoEquiv A B).apply_symm_apply _

private theorem inversePullbackIso_realization {A B : HopfAlgebraCategory K} {P Q : GroupScheme K}
    (f : specGroup A ≅ P) (g : specGroup B ≅ Q) (e : P ≅ Q) :
    f.symm ≪≫ spectrumIso (inversePullbackIso f g e) ≪≫ g = e := by
  simp only [inversePullbackIso_spec, Iso.trans_assoc, Iso.symm_self_id_assoc,
    Iso.symm_self_id, Iso.trans_refl]

private theorem inversePullbackIso_square {A B : HopfAlgebraCategory K} {P Q : GroupScheme K}
    (a : A ≅ B) (f : specGroup A ≅ P) (g : specGroup B ≅ Q) (e : P ≅ Q)
    (h : f.symm ≪≫ spectrumIso a ≪≫ g = e) :
    specGroupMap a.hom ≫ f.hom = g.hom ≫ e.inv := by
  rw [← h]
  simp only [Iso.trans_inv, Iso.symm_inv, Category.assoc, Iso.hom_inv_id_assoc]
  rfl

private theorem coordinateDisplacement {H₀ H : AffineAlgebraicGroup F}
    (e : (E).obj H₀.val ≅ (E).obj H.val)
    (r : relativePoints H₀.val (fieldTest F K) ≅ relativePoints H.val (fieldTest F K))
    (hr : IsInduced F K e r)
    (σ : Gal(K/F)) (δ : (E).obj H₀.val ≅ (E).obj H₀.val)
    (hδ : IsInduced F K δ (transportedAut F K r σ).asIso) :
    let e₀ := extendedCoordinateIso (K := K) H₀
    let a := inversePullbackIso e₀ (extendedCoordinateIso (K := K) H) e
    ∃ aσ, HopfConjugates σ a aσ ∧
      specGroupMap (aσ ≪≫ a.symm).hom ≫ e₀.hom = e₀.hom ≫ δ.inv := by
  dsimp only
  let t := extendedGroupIso (k := F) K
  let t₀ := extendedCoordinateIso (K := K) H₀
  let t₁ := extendedCoordinateIso (K := K) H
  let j₀ := coordinateHopfIso H₀
  let j₁ := coordinateHopfIso H
  let a := inversePullbackIso t₀ t₁ e
  have ha : hopfSchemeIso t j₀ j₁ a = e := by
    exact inversePullbackIso_realization t₀ t₁ e
  have ha' : hopfSchemeIso t j₁ j₀ a.symm = e.symm := by
    rw [← ha]
    change t₁.symm ≪≫ spectrumIso a.symm ≪≫ t₀ = (t₀.symm ≪≫ spectrumIso a ≪≫ t₁).symm
    simp only [spectrumIso, Iso.trans_symm, Functor.mapIso_symm, Iso.op_symm, Iso.symm_symm_eq,
      Iso.trans_assoc]
  have hrel : hopfIsoEquiv t j₀ j₁ a = r := by
    rw [hopfIsoEquiv_apply, ha]
    exact (induced_iff e r).mp hr
  have hrel' : hopfIsoEquiv t j₁ j₀ a.symm = r.symm := by
    rw [hopfIsoEquiv_apply, ha', ← hrel, hopfIsoEquiv_apply, ha]
    apply Iso.ext
    rfl
  obtain ⟨aσ, haσ⟩ := conjugates_exists σ a
  refine ⟨aσ, haσ, inversePullbackIso_square _ t₀ t₀ δ ?_⟩
  apply (schemeIsoEquiv K H₀.val H₀.val).injective
  change hopfIsoEquiv t j₀ j₀ (aσ ≪≫ a.symm) = _
  rw [hopfIsoEquiv_trans t j₀ j₁ j₀, ← restrict_hopfIso t (extendedSpecIso_hom_fst K) j₀ j₁ σ haσ,
    hrel, hrel', (induced_iff δ _).mp hδ]
  rfl

/-- Inverse pullback turns the forward geometric label permutation into the
forward permutation of the coordinate subalgebras. -/
private theorem projectionRange [MulAction Gal(K/F) I]
    {A₀ A C : HopfAlgebraCategory F}
    (q : I → (C ⟶ A₀)) (a : extendedHopf K A₀ ≅ extendedHopf K A)
    (σ : Gal(K/F)) (i : I) (aσ : extendedHopf K A₀ ≅ extendedHopf K A)
    (hσ : HopfConjugates σ a aσ) (c : extendedHopf K C ≅ extendedHopf K C)
    (h : extendedHopfMap K (q i) ≫ (aσ ≪≫ a.symm).hom =
      c.hom ≫ extendedHopfMap K (q (σ • i))) :
    (SemilinearAction.scalarExtension (K := K) A).act σ ''
      Set.range ((extendedHopfMap K (q i)) ≫ a.hom).hom =
        Set.range ((extendedHopfMap K (q (σ • i))) ≫ a.hom).hom := by
  have hs : extendedHopfMap K (q i) ≫ aσ.hom =
      c.hom ≫ extendedHopfMap K (q (σ • i)) ≫ a.hom := by
    simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      using congrArg (fun f => f ≫ a.hom) h
  let s := (SemilinearAction.scalarExtension (K := K) C).act σ
  have hx (x : extendedHopf K C) :
      (SemilinearAction.scalarExtension (K := K) A).act σ
          (((extendedHopfMap K (q i)) ≫ a.hom).hom x) =
        ((extendedHopfMap K (q (σ • i)) ≫ a.hom).hom) (c.hom.hom (s x)) := by
    change (SemilinearAction.scalarExtension (K := K) A).act σ
      (a.hom.hom ((extendedHopfMap K (q i)).hom x)) =
        a.hom.hom ((extendedHopfMap K (q (σ • i))).hom (c.hom.hom (s x)))
    have hmap : (extendedHopfMap K (q i)).hom (s x) =
        (SemilinearAction.scalarExtension (K := K) A₀).act σ
          ((extendedHopfMap K (q i)).hom x) :=
      baseHom_equivariant (K := K) (q i) σ x
    rw [← hσ ((extendedHopfMap K (q i)).hom x), ← hmap]
    exact ConcreteCategory.congr_hom hs (s x)
  ext y
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨c.hom.hom (s x), (hx x).symm⟩
  · rintro ⟨z, rfl⟩
    obtain ⟨x, hxz⟩ := s.surjective (c.inv.hom z)
    refine ⟨_, ⟨x, rfl⟩, ?_⟩
    rw [hx, hxz]
    exact congrArg _ (ConcreteCategory.congr_hom c.inv_hom_id z)

theorem coordinatePermutationDescent : CoordinatePermutationDescent.{u} := by
  classical
  intro F K I _ _ _ _ _ _ _ H₀ H S π hπ e r hr δ hδ hperm
  let bc := groupBaseChange F K
  let t₀ := extendedCoordinateIso (K := K) H₀
  let t₁ := extendedCoordinateIso (K := K) H
  let θ := extendedCoordinateIso (K := K) S
  let a := inversePullbackIso t₀ t₁ e
  let q (i : I) := coordinateHopfMap (G := H₀) (H := S) (π i)
  let p₀ (i : I) := extendedHopfMap K (q i)
  let p (i : I) := p₀ i ≫ a.hom
  have hn (i : I) : specGroupMap (p₀ i) ≫ θ.hom = t₀.hom ≫ bc.map (π i) :=
    extendedCoordinateIso_natural (π i)
  have ha : specGroupMap a.hom ≫ t₀.hom = t₁.hom ≫ e.inv := by
    exact inversePullbackIso_square a t₀ t₁ e (inversePullbackIso_realization t₀ t₁ e)
  have hp (i : I) :
      specGroupMap (p i) ≫ θ.hom = t₁.hom ≫ e.inv ≫ bc.map (π i) := by
    change specGroupMap (p₀ i ≫ a.hom) ≫ θ.hom = _
    rw [specGroupMap_comp, Category.assoc, hn, ← Category.assoc, ha, Category.assoc]
  have hstable (σ : Gal(K/F)) (i : I) :
      (SemilinearAction.scalarExtension (K := K) (coordinates H)).act σ ''
        Set.range (p i).hom = Set.range (p (σ • i)).hom := by
    obtain ⟨aσ, hσ, hd⟩ := coordinateDisplacement e r hr σ (δ σ) (hδ σ)
    change specGroupMap (aσ ≪≫ a.symm).hom ≫ t₀.hom = t₀.hom ≫ (δ σ).inv at hd
    obtain ⟨s, hs⟩ := hperm σ i
    let c := inversePullbackIso θ θ s
    have hc : specGroupMap c.hom ≫ θ.hom = θ.hom ≫ s.inv := by
      exact inversePullbackIso_square c θ θ s (inversePullbackIso_realization θ θ s)
    have hdq : p₀ i ≫ (aσ ≪≫ a.symm).hom = c.hom ≫ p₀ (σ • i) := by
      apply specGroupMap_injective
      rw [specGroupMap_comp, specGroupMap_comp, ← cancel_mono θ.hom]
      simp only [Category.assoc]
      rw [hn i]
      calc
        _ = (specGroupMap (aσ ≪≫ a.symm).hom ≫ t₀.hom) ≫ bc.map (π i) :=
          (Category.assoc ..).symm
        _ = (t₀.hom ≫ (δ σ).inv) ≫ bc.map (π i) :=
          congrArg (fun f => f ≫ bc.map (π i)) hd
        _ = t₀.hom ≫ bc.map (π (σ • i)) ≫ s.inv := by
          rw [Category.assoc, inverseSquare (δ σ) s hs.symm]
        _ = (specGroupMap (p₀ (σ • i)) ≫ θ.hom) ≫ s.inv := by
          rw [← Category.assoc, hn (σ • i)]
        _ = _ := by rw [Category.assoc, hc]
    exact projectionRange q a σ i aσ hσ c hdq
  have hfinite : Algebra.FiniteType K (extendedHopf K (coordinates S)) := by
    let j := coordinateHopfIso S
    have hft : LocallyOfFiniteType (specGroup (coordinates S)).X.hom := by
      rw [← Over.w j.hom.hom.hom]
      have : IsIso j.hom.hom.hom.left := ((Grp.forget (SchemeOver F)) ⋙
        Over.forget (Spec (CommRingCat.of F))).map_isIso j.hom
      let _ : LocallyOfFiniteType S.val.X.hom := S.property.2.1
      infer_instance
    let _ := (hopfSpec_locallyOfFiniteType_iff F _).mp hft
    change Algebra.FiniteType K (K ⊗[F] coordinates S)
    infer_instance
  have hproduct : IsLimit (Fan.mk (specGroup (extendedHopf K (coordinates H)))
      (fun i => specGroupMap (p i))) :=
    productOfComparison (extendedProduct (K := K) hπ) (t₁ ≪≫ e.symm) θ (by
      intro i
      simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc] using hp i)
  let X := productDescentOfStableProjections (coordinates H) (fun _ => extendedHopf K (coordinates S))
    (fun _ => hfinite) p (coordinateProduct p hproduct) hstable
  refine ⟨X, coordinateHopfIso H, extendedGroupIso K, extendedSpecIso_hom_fst K, fun _ => θ, ?_⟩
  intro γ i
  change ((bc.mapIso (coordinateHopfIso H).symm ≪≫
      (extendedGroupIso K (coordinates H)).symm ≪≫ spectrumIso (Iso.refl _)).hom) ≫
      specGroupMap (p i) ≫ θ.hom = _
  have hspec : spectrumIso (Iso.refl (extendedHopf K (coordinates H))) = Iso.refl _ := by
    change (hopfSpec (CommRingCat.of K)).mapIso (Iso.refl _) = _
    exact Functor.mapIso_refl _ _
  rw [hp i, hspec, Iso.trans_refl]
  have hγ : bc.mapIso (coordinateHopfIso H).symm ≪≫ (extendedGroupIso K (coordinates H)).symm =
      t₁.symm := by
    change _ = (extendedGroupIso K (coordinates H) ≪≫ bc.mapIso (coordinateHopfIso H)).symm
    rw [Iso.trans_symm, Functor.mapIso_symm]
  rw [hγ, Iso.symm_hom, Iso.inv_hom_id_assoc]

end Coordinates

end

end LinearAlgebraicGroups.Arithmetic.DerivedProjectionDescent
