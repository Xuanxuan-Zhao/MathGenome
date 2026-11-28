import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Invariants.RationalActionComparison
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Invariants.Actions
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Invariants.GlobalFunctionsHopf
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.RationalRepresentations
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SmoothnessCriteria
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits WithConv Opposite
open CategoryTheory.MonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj

universe u

namespace RepTheorySurvey.Invariants.RationalActionComparison

open LinearAlgebraicGroups
open LinearAlgebraicGroups.StandardGroups (generalLinearGroup generalLinearGroupPointsIso)
open GlobalFunctions (Sections evaluate pull)
open private chart chartMap pull_cover_injective isIso_unit_of_affine unique_precomp
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Invariants.GlobalFunctionsHopf
open private eq_zero_of_algHom_eq_zero
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.RationalRepresentations

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option linter.style.haveILetI false

variable {k : Type u} [Field k]

private theorem eval_comp {X Y : SchemeOver k} (p : Points X (CommAlgCat.of k k))
    (f : X ⟶ Y) : evaluate (p ≫ f) = (evaluate p).comp (pull f) := by
  rw [evaluate, GlobalFunctions.pull_comp, ← AlgHom.comp_assoc]
  rfl

private theorem affine_sections_finiteType (X : SchemeOver k)
    [IsAffine X.left] [LocallyOfFiniteType X.hom] : Algebra.FiniteType k (Sections X) := by
  have h := X.hom.finiteType_appLE (U := ⊤) (V := ⊤) (isAffineOpen_top _) (isAffineOpen_top _) (by simp)
  have ht : X.hom.appTop.hom.FiniteType := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact h
  change (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ X.hom.appTop).hom).FiniteType
  exact ht.comp (RingHom.FiniteType.of_surjective (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).2)

private theorem affine_sections_reduced (X : SchemeOver k)
    [IsAffine X.left] [IsReduced X.left] : _root_.IsReduced (Sections X) := by
  apply (affine_isReduced_iff _).mp
  exact isReduced_of_isOpenImmersion X.left.isoSpec.inv

private theorem affine_evaluation_surjective (X : SchemeOver k) [IsAffine X.left] :
    Function.Surjective (fun p : Points X (CommAlgCat.of k k) => evaluate p) := by
  intro f
  letI := isIso_unit_of_affine X
  letI := algSpec.instFaithful (R := CommRingCat.of k)
  let p : Points X (CommAlgCat.of k k) :=
    (testSpec k).map (CommAlgCat.ofHom f).op ≫ inv (GlobalFunctions.unit X)
  refine ⟨p, ?_⟩
  have h := GlobalFunctions.evaluationFormula p
  have hp : p ≫ GlobalFunctions.unit X = (testSpec k).map (CommAlgCat.ofHom f).op := by simp [p]
  rw [hp] at h
  exact congrArg (fun a => a.unop.hom) ((testSpec k).map_injective h.symm)

theorem sectionsSeparated : Specs.SectionsSeparated.{u} := by
  intro k _ _ X _ _ s t h
  let C := X.left.affineCover
  apply pull_cover_injective C
  funext i
  let U := chart C i
  let j := chartMap C i
  letI : IsAffine U.left := Scheme.isAffine_affineCover X.left i
  letI : LocallyOfFiniteType U.hom := locallyOfFiniteType_comp (C.f i) X.hom
  letI : IsReduced U.left := isReduced_of_isOpenImmersion (C.f i)
  letI : Algebra.FiniteType k (Sections (chart C i)) := affine_sections_finiteType U
  letI : _root_.IsReduced (Sections (chart C i)) := affine_sections_reduced U
  apply sub_eq_zero.mp
  apply eq_zero_of_algHom_eq_zero (F := k)
  intro f
  obtain ⟨p, rfl⟩ := affine_evaluation_surjective U f
  rw [map_sub, sub_eq_zero]
  exact (DFunLike.congr_fun (eval_comp p j) s).symm.trans
    ((congrFun h (p ≫ j)).trans (DFunLike.congr_fun (eval_comp p j) t))

private theorem groupReduced (G : GroupScheme k) [LocallyOfFiniteType G.X.hom]
    [Smooth G.X.hom] : IsReduced G.X.left := by
  have h := ((groupSmoothnessCriteria k G).1.mp (inferInstance : Smooth G.X.hom))
  exact h.geometrically_isReduced (𝟙 _) _ _ (IsPullback.of_id_fst (f := G.X.hom))

variable {G : GroupScheme k} (H : GlobalFunctions.Specs.GlobalHopf G)
variable {V W C : Type u} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [AddCommGroup C] [Module k C]

@[simp] theorem contract_tmul (f : C →ₗ[k] k) (v : V) (c : C) :
    contract f (v ⊗ₜ[k] c) = f c • v := rfl

private theorem contract_natural (f : C →ₗ[k] k) (l : V →ₗ[k] W) (t : V ⊗[k] C) :
    l (contract f t) = contract f (l.rTensor C t) := by
  induction t <;> simp_all

private theorem contract_separates {P : Type u} (f : P → C →ₗ[k] k)
    (hf : Function.Injective (fun c p => f p c)) :
    Function.Injective (fun t : V ⊗[k] C => fun p => contract (f p) t) := by
  intro s t h
  classical
  let b := Module.Basis.ofVectorSpace k V
  apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
  ext i
  rw [TensorProduct.equivFinsuppOfBasisLeft_apply, TensorProduct.equivFinsuppOfBasisLeft_apply]
  change RationalRepresentations.tensorCoordinate b i s =
    RationalRepresentations.tensorCoordinate b i t
  apply hf
  funext p
  have he (z : V ⊗[k] C) :
      f p (RationalRepresentations.tensorCoordinate b i z) = b.coord i (contract (f p) z) := by
    induction z with
    | tmul v c => simp [RationalRepresentations.tensorCoordinate, mul_comm]
    | add x y hx hy => simp only [map_add, hx, hy]
  exact (he s).trans ((congrArg (b.coord i) (congrFun h p)).trans (he t).symm)

private theorem char_separates [IsAlgClosed k] [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom] :
    Function.Injective (fun x : H.hopf => fun g : KPoints G => pointEvaluation H g x) := by
  letI := groupReduced G
  exact sectionsSeparated G.X

private theorem eval_separates [IsAlgClosed k] [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom] :
    Function.Injective (fun t : V ⊗[k] H.hopf => fun g : KPoints G =>
      contract (pointEvaluation H g).toLinearMap t) :=
  contract_separates _ (char_separates H)

private abbrev specPointIso :=
  hopfSpecPointIso H.hopf

private lemma specPointIso_eval (a : G ⟶ H.spectrum) (ha : a.hom.hom = GlobalFunctions.unit G.X)
    (g : KPoints G) :
    ((specPointIso H).hom.app (CommAlgCat.of k k)) (toConv (pointEvaluation H g)) =
      ((groupPointsFunctor k).map a).app (CommAlgCat.of k k) g := by
  change (specPointIso H).hom.app _ _ = (g : Points G.X (CommAlgCat.of k k)) ≫ a.hom.hom
  rw [ha, GlobalFunctions.evaluationFormula]
  rfl

private def pointCharacter (a : G ⟶ H.spectrum) :
    KPoints G →* ((convolutionPoints H.hopf).obj (CommAlgCat.of k k)) :=
  ((specPointIso H).inv.app _).hom.comp (((groupPointsFunctor k).map a).app _).hom

private lemma pointCharacter_apply (a : G ⟶ H.spectrum)
    (ha : a.hom.hom = GlobalFunctions.unit G.X) (g : KPoints G) :
    pointCharacter H a g = toConv (pointEvaluation H g) := by
  let e := (specPointIso H).app (CommAlgCat.of k k)
  let p := ((groupPointsFunctor k).map a).app (CommAlgCat.of k k) g
  change e.inv p = toConv (pointEvaluation H g)
  exact (congrArg (fun q => e.inv q) (specPointIso_eval H a ha g).symm).trans
    (GrpCat.inv_hom_apply e _)

private theorem counit_equation (a : G ⟶ H.spectrum)
    (ha : a.hom.hom = GlobalFunctions.unit G.X) :
    (pointEvaluation H (1 : KPoints G)).toLinearMap = Coalgebra.counit := by
  have h := (pointCharacter_apply H a ha 1).symm.trans (map_one (pointCharacter H a))
  ext x
  exact (congrArg (fun f : WithConv (H.hopf →ₐ[k] k) => f.ofConv x) h).trans
    (by simp [AlgHom.convOne_apply])

private def contract₂ (f g : H.hopf →ₗ[k] k) : V ⊗[k] (H.hopf ⊗[k] H.hopf) →ₗ[k] V :=
  (contract f).comp ((contract g (V := H.hopf)).lTensor V)

private theorem contract₂_separates [IsAlgClosed k] [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom] :
    Function.Injective (fun t : V ⊗[k] (H.hopf ⊗[k] H.hopf) => fun g h : KPoints G =>
      contract₂ H (pointEvaluation H g).toLinearMap (pointEvaluation H h).toLinearMap t) := by
  intro s t eq
  apply (TensorProduct.assoc k V H.hopf H.hopf).symm.injective
  apply eval_separates H
  funext h
  apply eval_separates H
  funext g
  have aux (w : V ⊗[k] (H.hopf ⊗[k] H.hopf)) :
      contract (pointEvaluation H g).toLinearMap
        (contract (pointEvaluation H h).toLinearMap ((TensorProduct.assoc k V H.hopf H.hopf).symm w)) =
      contract₂ H (pointEvaluation H g).toLinearMap (pointEvaluation H h).toLinearMap w := by
    induction w with
    | add x y hx hy => simp [hx, hy]
    | tmul v w =>
      induction w with
      | add x y hx hy => simp [TensorProduct.tmul_add, hx, hy]
      | tmul x y => simp [contract₂, TensorProduct.tmul_smul]
  dsimp only
  rw [aux, aux]
  exact congrFun (congrFun eq g) h

private theorem contract₂_coassoc (d : V →ₗ[k] V ⊗[k] H.hopf) (t : V ⊗[k] H.hopf)
    (f g : H.hopf →ₗ[k] k) :
    contract₂ H f g (TensorProduct.assoc k V H.hopf H.hopf (d.rTensor H.hopf t)) =
      contract f (d (contract g t)) := by
  induction t with
  | add x y hx hy => simp [hx, hy]
  | tmul v c =>
    simp only [LinearMap.rTensor_tmul, contract_tmul, map_smul]
    generalize d v = z
    induction z with
    | add x y hx hy => simp [TensorProduct.add_tmul, hx, hy]
    | tmul x y => simp [contract₂, TensorProduct.tmul_smul]

private theorem contract₂_comul (a : G ⟶ H.spectrum)
    (ha : a.hom.hom = GlobalFunctions.unit G.X) (g h : KPoints G)
    (t : V ⊗[k] H.hopf) :
    contract₂ H (pointEvaluation H g).toLinearMap (pointEvaluation H h).toLinearMap
        ((Coalgebra.comul (R := k) (A := H.hopf)).lTensor V t) =
      contract (pointEvaluation H (g * h)).toLinearMap t := by
  have hm := (pointCharacter_apply H a ha (g * h)).symm.trans (map_mul (pointCharacter H a) g h)
  rw [pointCharacter_apply H a ha g, pointCharacter_apply H a ha h] at hm
  induction t with
  | add x y hx hy => simp [hx, hy]
  | tmul v c =>
    rw [LinearMap.lTensor_tmul, contract_tmul]
    have hc := congrArg (fun f : WithConv (H.hopf →ₐ[k] k) => f.ofConv c) hm
    change (pointEvaluation H (g * h)).toLinearMap c = _ at hc
    rw [hc]
    change _ = ((toConv (pointEvaluation H g) * toConv (pointEvaluation H h)) c) • v
    rw [AlgHom.convMul_apply]
    generalize Coalgebra.comul (R := k) c = z
    induction z with
    | add x y hx hy => simp [TensorProduct.tmul_add, add_smul, hx, hy]
    | tmul x y =>
      simp [contract₂, TensorProduct.tmul_smul, Algebra.TensorProduct.lift_tmul, mul_smul]
      exact smul_comm _ _ _

private def toPointRepresentation (a : G ⟶ H.spectrum)
    (ha : a.hom.hom = GlobalFunctions.unit G.X) (d : RightComodule k H.hopf V) :
    Representation k (KPoints G) V where
  toFun g := (contract (pointEvaluation H g).toLinearMap).comp d.coaction
  map_one' := by
    ext v
    exact (congrArg (fun f => contract f (d.coaction v)) (counit_equation H a ha)).trans (d.counit v)
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    change contract (pointEvaluation H (g * h)).toLinearMap (d.coaction v) =
      contract (pointEvaluation H g).toLinearMap (d.coaction (contract (pointEvaluation H h).toLinearMap (d.coaction v)))
    rw [← contract₂_comul H a ha, ← d.coassoc, contract₂_coassoc]

private theorem regular_of_actsBy (d : RightComodule k H.hopf V)
    (r : Representation k (KPoints G) V) (h : ActsBy H d r) : HasRegularOrbits r := by
  intro v
  obtain ⟨n, w, f, hw⟩ := TensorProduct.exists_sum_tmul_eq (d.coaction v)
  refine ⟨n, f, w, fun g => ?_⟩
  rw [h, hw, map_sum]
  simp only [contract_tmul]
  rfl

private theorem exists_coaction [IsAlgClosed k] [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom]
    (a : G ⟶ H.spectrum) (ha : a.hom.hom = GlobalFunctions.unit G.X)
    (r : Representation k (KPoints G) V) (hr : HasRegularOrbits r) :
    ∃ d : RightComodule k H.hopf V, ActsBy H d r := by
  classical
  have ex (v : V) : ∃ t : V ⊗[k] H.hopf, ∀ g : KPoints G,
      r g v = contract (pointEvaluation H g).toLinearMap t := by
    obtain ⟨n, f, w, hw⟩ := hr v
    exact ⟨∑ i, w i ⊗ₜ[k] f i, fun g => by simp only [hw, map_sum, contract_tmul]; rfl⟩
  choose d hd using ex
  let D : V →ₗ[k] V ⊗[k] H.hopf :=
    { toFun := d
      map_add' := fun x y => by
        apply eval_separates H
        funext g
        simp [← hd]
      map_smul' := fun c x => by
        apply eval_separates H
        funext g
        simp [← hd] }
  refine ⟨⟨D, ?_, ?_⟩, fun g v => hd v g⟩
  · intro v
    apply contract₂_separates H
    funext g h
    dsimp only
    rw [contract₂_coassoc, contract₂_comul H a ha]
    change contract (pointEvaluation H g).toLinearMap (d (contract (pointEvaluation H h).toLinearMap (d v))) =
      contract (pointEvaluation H (g * h)).toLinearMap (d v)
    simp [← hd]
  · intro v
    change contract (Coalgebra.counit (R := k) (A := H.hopf)) (d v) = v
    rw [← counit_equation H a ha, ← hd]
    simp

private theorem coaction_unique [IsAlgClosed k] [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom]
    {d e : RightComodule k H.hopf V} {r : Representation k (KPoints G) V}
    (hd : ActsBy H d r) (he : ActsBy H e r) : d = e := by
  have h : d.coaction = e.coaction := by
    ext v
    apply eval_separates H
    funext g
    exact (hd g v).symm.trans (he g v)
  cases d
  cases e
  cases h
  rfl

theorem linearComparison : Specs.LinearComparison.{u} := by
  intro k V _ _ _ _ G _ _ _ H a ha
  let F (d : RightComodule k H.hopf V) :
      {r : Representation k (KPoints G) V // HasRegularOrbits r} :=
    ⟨toPointRepresentation H a ha d, regular_of_actsBy H d _ (fun _ _ => rfl)⟩
  have hF (d : RightComodule k H.hopf V) : ActsBy H d (F d).1 := fun _ _ => rfl
  refine ⟨Equiv.ofBijective F ⟨?_, ?_⟩, hF⟩
  · intro d e h
    apply coaction_unique H (hF d)
    rw [h]
    exact hF e
  · rintro ⟨r, hr⟩
    obtain ⟨d, hd⟩ := exists_coaction H a ha r hr
    refine ⟨d, Subtype.ext ?_⟩
    ext g v
    exact (hF d g v).trans (hd g v).symm


theorem equivariantMaps : Specs.EquivariantMaps.{u} := by
  intro k V W _ _ _ _ _ _ G _ _ H d e r s f hd he
  constructor
  · intro h
    apply LinearMap.ext
    intro v
    apply eval_separates H
    funext g
    change contract (pointEvaluation H g).toLinearMap (f.rTensor H.hopf (d.coaction v)) =
      contract (pointEvaluation H g).toLinearMap (e.coaction (f v))
    rw [← contract_natural]
    exact (congrArg f (hd g v)).symm.trans ((h.isIntertwining g v).trans (he g (f v)))
  · intro h
    constructor
    intro g v
    rw [hd g v, he g (f v), contract_natural]
    exact congrArg (contract (pointEvaluation H g).toLinearMap) (DFunLike.congr_fun h v)

theorem stableSubspaces : Specs.StableSubspaces.{u} := by
  intro k V _ _ _ _ G _ _ H d r S hd
  constructor
  · intro h x
    rw [← rTensor_mkQ H.hopf S, LinearMap.mem_ker]
    apply eval_separates H
    funext g
    change contract (pointEvaluation H g).toLinearMap (S.mkQ.rTensor H.hopf (d.coaction x)) =
      contract (pointEvaluation H g).toLinearMap 0
    rw [← contract_natural, ← hd g x, map_zero]
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact h g x
  · intro h g x
    obtain ⟨t, ht⟩ := h x
    rw [hd g x, ← ht, ← contract_natural]
    exact (contract (pointEvaluation H g).toLinearMap t : S).property

/-- Corresponding actions have the same ordered subspaces, with their two stability conditions. -/
def subrepresentationOrderIso [IsAlgClosed k] [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom]
    (d : RightComodule k H.hopf V) (r : Representation k (KPoints G) V) (hd : ActsBy H d r) :
    Subrepresentation r ≃o {S : Submodule k V // d.IsSubcomodule S} where
  toFun S := ⟨S.toSubmodule,
    (stableSubspaces G H d r S.toSubmodule hd).mp (fun g x => S.apply_mem_toSubmodule g x.2)⟩
  invFun S := ⟨S.1, fun g x hx => (stableSubspaces G H d r S.1 hd).mpr S.2 g ⟨x, hx⟩⟩
  left_inv _ := Subrepresentation.toSubmodule_injective rfl
  right_inv _ := Subtype.ext rfl
  map_rel_iff' := Iff.rfl

theorem invariantSubspaces : Specs.InvariantSubspaces.{u} := by
  intro k V _ _ _ _ G _ _ H d r hd
  ext v
  change (∀ g : KPoints G, r g v = v) ↔ d.coaction v - v ⊗ₜ[k] (1 : H.hopf) = 0
  rw [sub_eq_zero]
  constructor
  · intro hv
    apply eval_separates H
    funext g
    change contract (pointEvaluation H g).toLinearMap (d.coaction v) =
      contract (pointEvaluation H g).toLinearMap (v ⊗ₜ[k] (1 : H.hopf))
    rw [← hd g v, hv g, contract_tmul]
    simp
  · intro hv g
    rw [hd g v, hv, contract_tmul]
    simp

theorem orbitSpan : Specs.OrbitSpan.{u} := by
  intro k V _ _ _ G r hr v
  let orbit : Set V := Set.range fun g : KPoints G => r g v
  let S := Submodule.span k orbit
  have hS (g : KPoints G) : S ≤ S.comap (r g) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨h, rfl⟩
    exact Submodule.subset_span (s := orbit) ⟨g * h, by simp⟩
  refine ⟨⟨S, fun g _ hx => hS g hx⟩, rfl, ?_, ?_⟩
  · exact Submodule.subset_span (s := orbit) ⟨1, by simp⟩
  · obtain ⟨n, f, w, hw⟩ := hr v
    let T := Submodule.span k (Set.range w)
    letI : FiniteDimensional k T := FiniteDimensional.span_of_finite k (Set.finite_range w)
    have hST : S ≤ T := by
      apply Submodule.span_le.mpr
      rintro _ ⟨g, rfl⟩
      change r g v ∈ T
      rw [hw g]
      exact T.sum_mem fun i _ => T.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
    exact Submodule.finiteDimensional_of_le hST

/-- The span of the point orbit itself is a finite-dimensional subcomodule containing the vector. -/
theorem orbitSpan_subcomodule [IsAlgClosed k] [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom]
    (d : RightComodule k H.hopf V) (r : Representation k (KPoints G) V) (hd : ActsBy H d r) (v : V) :
    ∃ S : d.FiniteSubcomodule,
      S.val = Submodule.span k (Set.range (fun g : KPoints G => r g v)) ∧ v ∈ S.val := by
  obtain ⟨S, hS, hv, hfin⟩ := orbitSpan G r (regular_of_actsBy H d r hd) v
  let T := subrepresentationOrderIso H d r hd S
  exact ⟨⟨T.1, T.2, hfin⟩, hS, hv⟩

section Algebra

variable {A : Type u} [Ring A] [Algebra k A]

private def contractAlg (g : H.hopf →ₐ[k] k) : A ⊗[k] H.hopf →ₐ[k] A :=
  Algebra.TensorProduct.lift (AlgHom.id k A) ((Algebra.ofId k A).comp g)
    (fun x y => Algebra.commute_algebraMap_right (g y) x)

private theorem contractAlg_apply (g : H.hopf →ₐ[k] k) (t : A ⊗[k] H.hopf) :
    contractAlg H g t = contract g.toLinearMap t := by
  induction t with
  | tmul x y => simp [contractAlg, Algebra.smul_def, Algebra.commutes]
  | add t s ht hs => simp [ht, hs]

private def pointAlgHom (d : RationalAlgebraAction H.hopf A) (g : KPoints G) :
    A →ₐ[k] A := (contractAlg H (pointEvaluation H g)).comp d.coaction

private theorem pointAlgHom_apply (d : RationalAlgebraAction H.hopf A) (g : KPoints G) (x : A) :
    pointAlgHom H d g x = contract (pointEvaluation H g).toLinearMap (d.coaction x) :=
  contractAlg_apply H _ _

private def toPointAlgebraAction (a : G ⟶ H.spectrum)
    (ha : a.hom.hom = GlobalFunctions.unit G.X) (d : RationalAlgebraAction H.hopf A) :
    GroupAlgebraAction k (KPoints G) A := by
  let r := toPointRepresentation H a ha d.toRightComodule
  have he (g : KPoints G) (x : A) : pointAlgHom H d g x = r g x := pointAlgHom_apply H d g x
  have inverse (g : KPoints G) (x : A) : pointAlgHom H d g⁻¹ (pointAlgHom H d g x) = x := by
    rw [he, he, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  let e (g : KPoints G) : A ≃ₐ[k] A :=
    AlgEquiv.ofAlgHom (pointAlgHom H d g) (pointAlgHom H d g⁻¹)
      (by ext x; simpa only [AlgHom.comp_apply, AlgHom.id_apply, inv_inv] using inverse g⁻¹ x)
      (by ext x; exact inverse g x)
  refine { toFun := e, map_one' := ?_, map_mul' := ?_ }
  · ext x
    change pointAlgHom H d 1 x = x
    rw [he, map_one]
    rfl
  · intro g h
    ext x
    change pointAlgHom H d (g * h) x = pointAlgHom H d g (pointAlgHom H d h x)
    rw [he, he, he, map_mul]
    rfl

private theorem pointAlgebraActsBy (a : G ⟶ H.spectrum)
    (ha : a.hom.hom = GlobalFunctions.unit G.X) (d : RationalAlgebraAction H.hopf A) :
    ActsBy H d.toRightComodule (toPointAlgebraAction H a ha d).toRepresentation := by
  intro g x
  exact pointAlgHom_apply H d g x

private theorem exists_algebra_coaction [IsAlgClosed k] [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom]
    (a : G ⟶ H.spectrum) (ha : a.hom.hom = GlobalFunctions.unit G.X)
    (r : GroupAlgebraAction k (KPoints G) A) (hr : HasRegularOrbits r.toRepresentation) :
    ∃ d : RationalAlgebraAction H.hopf A, ActsBy H d.toRightComodule r.toRepresentation := by
  obtain ⟨d, hd⟩ := exists_coaction H a ha r.toRepresentation hr
  have he (g : KPoints G) (x : A) : contractAlg H (pointEvaluation H g) (d.coaction x) = r g x :=
    (contractAlg_apply H _ _).trans (hd g x).symm
  have hone : d.coaction 1 = 1 := by
    apply eval_separates H
    funext g
    change contract (pointEvaluation H g).toLinearMap (d.coaction 1) =
      contract (pointEvaluation H g).toLinearMap 1
    rw [← contractAlg_apply, ← contractAlg_apply, he, map_one, map_one]
  let D : A →ₐ[k] A ⊗[k] H.hopf :=
    { toFun := d.coaction
      map_zero' := map_zero _
      map_add' := map_add _
      map_one' := hone
      map_mul' := fun x y => by
        apply eval_separates H
        funext g
        change contract (pointEvaluation H g).toLinearMap (d.coaction (x * y)) =
          contract (pointEvaluation H g).toLinearMap (d.coaction x * d.coaction y)
        rw [← contractAlg_apply, ← contractAlg_apply, map_mul (contractAlg H _), he, he, he, map_mul]
      commutes' := fun c => by
        change d.coaction (algebraMap k A c) = _
        rw [Algebra.algebraMap_eq_smul_one, map_smul, hone, Algebra.algebraMap_eq_smul_one] }
  exact ⟨⟨D, d.coassoc, d.counit⟩, hd⟩

theorem algebraComparison : Specs.AlgebraComparison.{u} := by
  intro k A _ _ _ _ G _ _ _ H a ha
  let F (d : RationalAlgebraAction H.hopf A) :
      {r : GroupAlgebraAction k (KPoints G) A // HasRegularOrbits r.toRepresentation} :=
    ⟨toPointAlgebraAction H a ha d, regular_of_actsBy H _ _ (pointAlgebraActsBy H a ha d)⟩
  have hF (d : RationalAlgebraAction H.hopf A) : ActsBy H d.toRightComodule (F d).1.toRepresentation :=
    pointAlgebraActsBy H a ha d
  refine ⟨Equiv.ofBijective F ⟨?_, ?_⟩, fun d => ⟨hF d, ?_⟩⟩
  · intro d e h
    have hde : Invariants.Specs.rationalToRightComodule d =
        Invariants.Specs.rationalToRightComodule e := by
      apply coaction_unique H (hF d)
      rw [h]
      exact hF e
    have hc : d.coaction = e.coaction :=
      AlgHom.toLinearMap_injective (congrArg RightComodule.coaction hde)
    cases d
    cases e
    cases hc
    rfl
  · rintro ⟨r, hr⟩
    obtain ⟨d, hd⟩ := exists_algebra_coaction H a ha r hr
    refine ⟨d, Subtype.ext ?_⟩
    ext g x
    exact (hF d g x).trans (hd g x).symm
  · have h := invariantSubspaces G H (Invariants.Specs.rationalToRightComodule d) (F d).1.toRepresentation (hF d)
    ext x
    exact SetLike.ext_iff.mp h x

end Algebra

/-- Precomposition with a group-scheme affinization induces a bijection into affine targets. -/
private theorem groupAffinization_bijective [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    (a : G ⟶ H.spectrum) (ha : a.hom.hom = GlobalFunctions.unit G.X)
    (L : GroupScheme k) [IsAffine L.X.left] :
    Function.Bijective (fun f : H.spectrum ⟶ L => a ≫ f) := by
  constructor
  · intro f g h
    apply (Grp.forget _).map_injective
    apply unique_precomp (GlobalFunctions.unit G.X) (GlobalFunctions.affinizationUniversal G.X L.X)
    rw [← ha]
    exact congrArg (fun p : G ⟶ L => p.hom.hom) h
  · intro f
    obtain ⟨H₀, a₀, ha₀, h₀⟩ := GlobalFunctions.globalHopfExists G
    letI : IsAffine H.spectrum.X.left := ((affineHopfSpec k).obj (op H.hopf)).property
    obtain ⟨i, hi, _⟩ := h₀ H.spectrum a
    have hid : i.hom.hom = 𝟙 (GlobalFunctions.affinization G.X) := by
      apply unique_precomp (GlobalFunctions.unit G.X)
        (GlobalFunctions.affinizationUniversal G.X H.spectrum.X)
      rw [← ha₀]
      change (a₀ ≫ i).hom.hom = a₀.hom.hom ≫ 𝟙 _
      rw [hi, Category.comp_id, ha, ha₀]
    letI : IsIso i.hom.hom := by
      rw [hid]
      exact IsIso.id _
    let e : H₀.spectrum ≅ H.spectrum :=
      Grp.mkIso (asIso i.hom.hom) (IsMonHom.one_hom i.hom.hom) (IsMonHom.mul_hom i.hom.hom)
    have he : e.hom = i := (Grp.forget _).map_injective rfl
    obtain ⟨q, hq, _⟩ := h₀ L f
    refine ⟨e.inv ≫ q, ?_⟩
    change a ≫ e.inv ≫ q = f
    rw [← hi, ← he, Category.assoc, e.hom_inv_id_assoc, hq]

theorem finiteDimensionalComparison : Specs.FiniteDimensionalComparison.{u} := by
  intro k V I _ _ _ _ _ _ b G _ _ _ H a ha
  let L := generalLinearGroup k I
  letI : IsAffine L.val.X.left := L.property.1
  let A := (affineHopfSpec k).obj (op H.hopf)
  let l := generalLinearGroupPointsIso k I
  let F : (H.spectrum ⟶ L.val) ≃ (G ⟶ L.val) :=
    Equiv.ofBijective _ (groupAffinization_bijective H a ha L.val)
  obtain ⟨E, hE⟩ := RationalRepresentations.representationCoactionComparison H.hopf b
    A L.val (specPointIso H) l
  obtain ⟨S, hS⟩ := linearComparison (V := V) G H a ha
  refine ⟨(F.symm.trans E).trans S, ?_⟩
  intro f g j
  let p := F.symm f
  have hp : a ≫ p = f := F.apply_symm_apply f
  have hpoint :
      ((groupPointsFunctor k).map p).app (CommAlgCat.of k k)
        ((specPointIso H).hom.app (CommAlgCat.of k k) (toConv (pointEvaluation H g))) =
      ((groupPointsFunctor k).map f).app (CommAlgCat.of k k) g := by
    rw [specPointIso_eval H a ha g]
    have hcomp := (groupPointsFunctor k).map_comp a p
    rw [hp] at hcomp
    exact (congrArg (fun m => m.app (CommAlgCat.of k k) g) hcomp).symm
  have heval := RationalRepresentations.evaluationComparison H.hopf b A L.val (specPointIso H) l
    p (E p) (hE p) (CommAlgCat.of k k) (pointEvaluation H g) j
  change (S (E p)).1 g (b j) = _
  rw [hS (E p) g (b j)]
  let matrix (x : KPoints L.val) :=
    (l.hom.app (CommAlgCat.of k k) x).val
  have hmatrix := congrArg (fun x => ∑ i, matrix x i j • b i) hpoint
  refine (?_ : _ = _).trans hmatrix
  have h := congrArg (TensorProduct.rid k V) heval
  simp only [contract, RationalRepresentations.evaluate, LinearMap.comp_apply,
    LinearEquiv.coe_coe, map_sum, TensorProduct.rid_tmul, matrix] at h ⊢
  exact h

end
end RepTheorySurvey.Invariants.RationalActionComparison
