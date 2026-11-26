import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.LabelledSplitRankOneProduct
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.SpecialLinearDatum
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.RadicalBaseChange
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.GrpObj

universe u

namespace LinearAlgebraicGroups.Arithmetic.LabelledSplitRankOneProduct

open _root_.LinearAlgebraicGroups.Specs
open Specs.AbsoluteDynkinTypes (CartanRoots simpleCharacter reflectCoordinates)
open Specs.AbstractPairing (Root)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterDescent (Character)
open Specs.CharacterPairing (characterValue)
open Specs.GeometricRadicals
open Specs.Pinning (AttachedDatum BasedIso PinnedGroup SplitBorelPair)
open Specs.RootGroups (AdditiveLine HasScalarAction IsRootSubgroup rootPoint)
open Specs.RankOneFlag (IsGeometricallyMaximal)

noncomputable section

variable {k : Type u} [Field k]

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

open private affineProduct from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.ReductiveProductWithSplitTorus
open private productTorus splitProductTorus productRootEquiv productCharacterEquiv
  productCharacterEquiv_root_left productCharacterEquiv_root_right
  productTorus_geometricallyMaximal productReductive rootEquivOfRootMap characterValue_pullback
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes
open private splitBorelPair corootFullRank from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.SimplyConnectedLattice

private theorem smoothConnectedProduct (G H : AffineAlgebraicGroup k)
    (hg : IsReductive G) (hh : IsReductive H) :
    Smooth (affineProduct G H).val.X.hom ∧
      GeometricallyConnected (affineProduct G H).val.X.hom := by
  letI := hg.1
  letI := hh.1
  letI := hg.2.1
  letI := hh.2.1
  change Smooth (G.val.X ⊗ H.val.X).hom ∧ GeometricallyConnected (G.val.X ⊗ H.val.X).hom
  rw [Over.tensorObj_hom]
  exact ⟨inferInstance, GeometricallyConnected.comp _ _⟩

open private reductive_of_groupIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag

private theorem reductiveProduct (G H : AffineAlgebraicGroup k)
    (hg : IsReductive G) (hh : IsReductive H) : IsReductive (affineProduct G H) := by
  let K := AlgebraicClosure k
  let F := groupBaseChange k K
  let P := affineProduct G H
  have hP := smoothConnectedProduct G H hg hh
  have hG := (Reductive.RadicalBaseChange.reductiveFieldExtension (K := K) G
    hg.1 hg.2.1).mpr hg
  have hH := (Reductive.RadicalBaseChange.reductiveFieldExtension (K := K) H
    hh.1 hh.2.1).mpr hh
  have hprod := productReductive (GeometricGroup G) (GeometricGroup H) hG hH
  let e : (affineProduct (GeometricGroup G) (GeometricGroup H)).val ≅ (GeometricGroup P).val :=
    Functor.Monoidal.μIso F G.val H.val
  exact (Reductive.RadicalBaseChange.reductiveFieldExtension (K := K) P
    hP.1 hP.2).mp (reductive_of_groupIso e hprod)

open private splitTorus_baseChange geometricallyMaximal_of_maximal_split
  maximalTorus_of_geometricallyMaximal from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
open private maximal_of_square from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private lattice_torus_of_split from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag

private def pairOfMaximalTorus [IsAlgClosed k] (G : AffineAlgebraicGroup k)
    (hG : IsReductive G) (T : ClosedSubgroup G.val) (hs : IsSplitTorus T.group)
    (hm : IsMaximalTorus T) : SplitBorelPair k :=
  splitBorelPair G hG T hs (geometricallyMaximal_of_maximal_split G T hm hs)

set_option maxHeartbeats 1100000 in
private theorem productTorusMaximal (P Q : SplitBorelPair k) :
    IsGeometricallyMaximal (productTorus P Q) := by
  let K := AlgebraicClosure k
  let F := groupBaseChange k K
  obtain ⟨hp, hpmax⟩ := P.maximal
  obtain ⟨hq, hqmax⟩ := Q.maximal
  let TP := baseChangedSubgroup K P.T hp
  let TQ := baseChangedSubgroup K Q.T hq
  have hp' := splitTorus_baseChange (K := K) P.split
  have hq' := splitTorus_baseChange (K := K) Q.split
  have hPr := (Reductive.RadicalBaseChange.reductiveFieldExtension (K := K) P.G
    P.reductive.1 P.reductive.2.1).mpr P.reductive
  have hQr := (Reductive.RadicalBaseChange.reductiveFieldExtension (K := K) Q.G
    Q.reductive.1 Q.reductive.2.1).mpr Q.reductive
  let P' := pairOfMaximalTorus (k := K) (GeometricGroup P.G) hPr TP hp' hpmax
  let Q' := pairOfMaximalTorus (k := K) (GeometricGroup Q.G) hQr TQ hq' hqmax
  let e := Functor.Monoidal.μIso F P.G.val Q.G.val
  let t := Functor.Monoidal.μIso F P.T.group Q.T.group
  let T := productTorus P Q
  have hcomm : (productTorus P' Q').inclusion ≫ e.hom = t.hom ≫ F.map T.inclusion :=
    Functor.LaxMonoidal.μ_natural F P.T.inclusion Q.T.inclusion
  have hclosed : IsClosedImmersion (F.map T.inclusion).hom.hom.left :=
    baseChangeClosedSubgroup k K T.inclusion T.isClosedImmersion
  let U := productTorus P' Q'
  have hmax : IsMaximalTorus U :=
    maximalTorus_of_geometricallyMaximal (k := K) (affineProduct P'.G Q'.G) U
      (lattice_torus_of_split (splitProductTorus P' Q')) (productTorus_geometricallyMaximal P' Q')
  exact ⟨hclosed, maximal_of_square e U (baseChangedSubgroup K T hclosed) t hcomm.symm hmax⟩

private def productPair (P Q : SplitBorelPair k) : SplitBorelPair k :=
  splitBorelPair (affineProduct P.G Q.G) (reductiveProduct P.G Q.G P.reductive Q.reductive)
    (productTorus P Q) (splitProductTorus P Q) (productTorusMaximal P Q)

private def signedRoot {I : Type*} (i : I) (positive : Bool) : I → ℤ :=
  letI := Classical.decEq I
  Pi.single i (if positive then 2 else -2)

private theorem signedRoot_injective {I : Type*} :
    Function.Injective (fun t : I × Bool => signedRoot t.1 t.2) := by
  classical
  rintro ⟨i, b⟩ ⟨j, c⟩ h
  have hij : i = j := by
    by_contra ne
    have he := congrFun h i
    have hn : i ≠ j := ne
    cases b <;> cases c <;> simp [signedRoot, hn] at he
  subst j
  have he := congrFun h i
  cases b <;> cases c <;> simp_all [signedRoot]

private theorem cartanRoots_diagonal {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℤ) (hd : ∀ i j, A j i = if j = i then 2 else 0)
    {p : (I → ℤ) × (I → ℤ)} (hp : CartanRoots A p) :
    ∃ t : I × Bool, p.1 = signedRoot t.1 t.2 := by
  have hsimple (i : I) : simpleCharacter A i = signedRoot i true := by
    funext j
    simp [simpleCharacter, signedRoot, Pi.single_apply, hd]
  induction hp with
  | simple i => exact ⟨(i, true), hsimple i⟩
  | neg _ ih =>
    obtain ⟨⟨i, b⟩, h⟩ := ih
    refine ⟨(i, !b), ?_⟩
    change -_ = _
    rw [h]
    funext j
    cases b <;> by_cases e : j = i <;> simp [signedRoot, e]
  | reflect j _ ih =>
    obtain ⟨⟨i, b⟩, h⟩ := ih
    by_cases e : j = i
    · subst j
      refine ⟨(i, !b), ?_⟩
      change _ - _ • simpleCharacter A i = _
      rw [hsimple, h]
      funext j
      cases b <;> by_cases e : j = i <;> simp [signedRoot, e]
    · refine ⟨(i, b), ?_⟩
      change _ - _ • simpleCharacter A j = _
      rw [h]
      simp [signedRoot, e]

private def matrixRootIndex : Bool ≃ SpecialLinearDatum.RootIndices 2 :=
  Equiv.ofBijective (fun b => if b then ⟨(0, 1), by decide⟩ else ⟨(1, 0), by decide⟩) (by
    constructor
    · intro a b h
      cases a <;> cases b <;> simp_all
    · rintro ⟨⟨i, j⟩, h⟩
      fin_cases i <;> fin_cases j
      · exact (h rfl).elim
      · exact ⟨true, rfl⟩
      · exact ⟨false, rfl⟩
      · exact (h rfl).elim)

private structure RankOneModel (k : Type u) [Field k] where
  pair : SplitBorelPair k
  points : GeneralLinearStructure.SpecialMatrixPoints pair.G 2
  weights : Additive (Character pair.T.group) ≃ₗ[ℤ] ℤ
  roots : Bool ≃ Root pair.T
  weight_eq : ∀ b, weights (Additive.ofMul (roots b).val) = if b then 2 else -2
  upper : ClosedSubgroup pair.G.val
  line : AdditiveLine k
  parameter : line.group ≅ upper.group
  isRoot : IsRootSubgroup pair.T upper (roots true).val
  scalar : HasScalarAction pair.T (roots true).val (parameter.hom ≫ upper.inclusion)
  matrix_eq : ∀ (R : TestAlgebra k) (a : R),
    (points.hom.app R (rootPoint (parameter.hom ≫ upper.inclusion) R a)).val =
      1 + Matrix.single ⟨0⟩ ⟨1⟩ a

private theorem rankOneModel (k : Type u) [Field k] : Nonempty (RankOneModel k) := by
  let S := LinearAlgebraicGroups.StandardGroups.specialLinearGroup k (ULift.{u} (Fin 2))
  let s : GeneralLinearStructure.SpecialMatrixPoints S 2 :=
    LinearAlgebraicGroups.StandardGroups.specialLinearGroupPointsIso k (ULift.{u} (Fin 2))
  obtain ⟨T, L, M, B, _, _, ⟨A, U, x, hx, _, _⟩, _⟩ :=
    RootData.SpecialLinearDatum.matrixPinnedDatum k 1 S s
  obtain ⟨xc, _, _, _, hroot, _⟩ := RootData.SpecialLinearDatum.sizeTwoLattices
  let e := matrixRootIndex.trans M.indices
  let z := x (e true)
  refine ⟨⟨B.pair, s, L.characters.trans xc, e, ?_, (U (e true)).val, A,
    z.val, (U (e true)).property, z.property, fun R a => hx (matrixRootIndex true) R a⟩⟩
  intro b
  change xc (L.characters (Additive.ofMul (M.indices (matrixRootIndex b)).val)) = _
  rw [M.character_eq]
  cases b
  · change xc (SpecialLinearDatum.root 2 1 0) = -2
    have hneg : SpecialLinearDatum.root 2 1 0 = -SpecialLinearDatum.root 2 0 1 := by
      unfold SpecialLinearDatum.root
      rw [← map_neg, neg_sub]
    rw [hneg, map_neg, hroot]
  · exact hroot

private structure ProductModel (Q : RankOneModel k) (I : Type u) where
  pair : SplitBorelPair k
  projection : I → (pair.G.val ⟶ Q.pair.G.val)
  torusProjection : I → (pair.T.group ⟶ Q.pair.T.group)
  product : IsLimit (Fan.mk pair.G.val projection)
  torus_comm : ∀ i, pair.T.inclusion ≫ projection i = torusProjection i ≫ Q.pair.T.inclusion
  weights : Additive (Character pair.T.group) ≃ₗ[ℤ] (I → ℤ)
  roots : I × Bool ≃ Root pair.T
  root_eq : ∀ i b, (roots (i, b)).val = torusProjection i ≫ (Q.roots b).val
  weight_eq : ∀ i b, weights (Additive.ofMul (roots (i, b)).val) = signedRoot i b

private def singleModel (Q : RankOneModel k) : ProductModel Q PUnit.{u+1} where
  pair := Q.pair
  projection := fun _ => 𝟙 _
  torusProjection := fun _ => 𝟙 _
  product := Fan.IsLimit.mk _ (fun s => s.proj PUnit.unit)
    (by rintro s ⟨⟩; simp) (by rintro s m hm; simpa using hm PUnit.unit)
  torus_comm := by intro i; simp
  weights := Q.weights.trans (LinearEquiv.funUnique _ _ _).symm
  roots := (Equiv.punitProd Bool).trans Q.roots
  root_eq := by intro i b; simp
  weight_eq := by
    rintro ⟨⟩ b
    funext j
    cases j
    exact (Q.weight_eq b).trans (by simp [signedRoot])

private theorem single_option_none {I : Type*} (b : Bool) :
    ((LinearEquiv.piOptionEquivProd ℤ) : (Option I → ℤ) ≃ₗ[ℤ] ℤ × (I → ℤ)).symm
      ((if b then 2 else -2), 0) = signedRoot none b := by
  funext i
  cases i <;> simp [LinearEquiv.piOptionEquivProd, Equiv.piOptionEquivProd, signedRoot]

private theorem single_option_some {I : Type*} (i : I) (b : Bool) :
    ((LinearEquiv.piOptionEquivProd ℤ) : (Option I → ℤ) ≃ₗ[ℤ] ℤ × (I → ℤ)).symm
      (0, signedRoot i b) = signedRoot (some i) b := by
  funext j
  cases j with
  | none => simp [LinearEquiv.piOptionEquivProd, Equiv.piOptionEquivProd, signedRoot]
  | some j =>
    change signedRoot i b j = signedRoot (some i) b (some j)
    by_cases h : j = i
    · subst j
      simp [signedRoot]
    · have hn : (some j : Option I) ≠ some i := fun e => h (Option.some.inj e)
      simp [signedRoot, h, hn]

private def optionModel {Q : RankOneModel k} {I : Type u}
    (M : ProductModel Q I) : ProductModel Q (Option I) := by
  let P := productPair Q.pair M.pair
  let π : Option I → (P.G.val ⟶ Q.pair.G.val)
    | none => fst _ _
    | some j => snd _ _ ≫ M.projection j
  let πT : Option I → (P.T.group ⟶ Q.pair.T.group)
    | none => fst _ _
    | some j => snd _ _ ≫ M.torusProjection j
  let e₀ : Option I × Bool ≃ Bool ⊕ I × Bool :=
    { toFun := fun (i, b) => i.elim (.inl b) (fun j => .inr (j, b))
      invFun := fun s => s.elim (fun b => (none, b)) (fun (j, b) => (some j, b))
      left_inv := by rintro ⟨i, b⟩; cases i <;> rfl
      right_inv := by rintro (b | ⟨j, b⟩) <;> rfl }
  let e := (e₀.trans (Equiv.sumCongr Q.roots M.roots)).trans
    (productRootEquiv Q.pair M.pair)
  let w₀ : (Option I → ℤ) ≃ₗ[ℤ] ℤ × (I → ℤ) := LinearEquiv.piOptionEquivProd ℤ
  let w := (productCharacterEquiv Q.pair.T.group M.pair.T.group).symm.trans
    ((Q.weights.prodCongr M.weights).trans w₀.symm)
  refine ⟨P, π, πT, ?_, ?_, w, e, ?_, ?_⟩
  · refine Fan.IsLimit.mk _ (fun s => lift (s.proj none)
      (Fan.IsLimit.lift M.product (fun j => s.proj (some j)))) ?_ ?_
    · intro s j
      cases j with
      | none => exact lift_fst _ _
      | some i =>
        change lift _ _ ≫ snd _ _ ≫ M.projection i = _
        rw [lift_snd_assoc]
        exact Fan.IsLimit.fac M.product _ i
    · intro s f hf
      apply CartesianMonoidalCategory.hom_ext
      · rw [lift_fst]
        exact hf none
      · rw [lift_snd]
        apply Fan.IsLimit.hom_ext M.product
        intro i
        rw [Fan.IsLimit.fac M.product]
        exact (Category.assoc _ _ _).trans (hf (some i))
  · rintro (_ | i)
    · exact tensorHom_fst _ _
    · change (Q.pair.T.inclusion ⊗ₘ M.pair.T.inclusion) ≫
        snd _ _ ≫ M.projection i = (snd _ _ ≫ M.torusProjection i) ≫ Q.pair.T.inclusion
      simp [tensorHom_snd_assoc, Category.assoc, M.torus_comm]
  · rintro (_ | i) b
    · rfl
    · change snd _ _ ≫ (M.roots (i, b)).val = (snd _ _ ≫ M.torusProjection i) ≫ _
      rw [M.root_eq, Category.assoc]
  · rintro (_ | i) b
    · change w (Additive.ofMul ((productRootEquiv Q.pair M.pair) (.inl (Q.roots b))).val) = _
      rw [← productCharacterEquiv_root_left]
      have hm : M.weights (0 : Additive (Character M.pair.T.group)) = 0 :=
        M.weights.toLinearMap.map_zero
      simp only [w, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
        LinearEquiv.prodCongr_apply, Q.weight_eq, hm]
      exact single_option_none b
    · change w (Additive.ofMul ((productRootEquiv Q.pair M.pair) (.inr (M.roots (i, b)))).val) = _
      rw [← productCharacterEquiv_root_right]
      have hq : Q.weights (0 : Additive (Character Q.pair.T.group)) = 0 :=
        Q.weights.toLinearMap.map_zero
      simp only [w, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
        LinearEquiv.prodCongr_apply, M.weight_eq, hq]
      exact single_option_some i b

private def reindexModel {Q : RankOneModel k} {I J : Type u}
    (M : ProductModel Q I) (e : J ≃ I) : ProductModel Q J where
  pair := M.pair
  projection := M.projection ∘ e
  torusProjection := M.torusProjection ∘ e
  product := Fan.IsLimit.mk _ (fun s => Fan.IsLimit.lift M.product (fun i => s.proj (e.symm i)))
    (by
      intro s j
      have he := Fan.IsLimit.fac M.product (fun i => s.proj (e.symm i)) (e j)
      simpa using he)
    (by
      intro s f hf
      apply Fan.IsLimit.hom_ext M.product
      intro i
      rw [Fan.IsLimit.fac M.product]
      obtain ⟨j, rfl⟩ := e.surjective i
      simpa using hf j)
  torus_comm j := M.torus_comm (e j)
  weights := M.weights.trans (LinearEquiv.piCongrLeft ℤ (fun _ => ℤ) e).symm
  roots := (Equiv.prodCongr e (Equiv.refl Bool)).trans M.roots
  root_eq j b := M.root_eq (e j) b
  weight_eq j b := by
    change (LinearEquiv.piCongrLeft ℤ (fun _ => ℤ) e).symm
      (M.weights (Additive.ofMul (M.roots (e j, b)).val)) = _
    rw [M.weight_eq]
    funext i
    change signedRoot (e j) b (e i) = signedRoot j b i
    by_cases h : i = j
    · subst i
      simp [signedRoot]
    · have he : e i ≠ e j := fun he => h (e.injective he)
      simp [signedRoot, h, he]

private theorem productModel (Q : RankOneModel k) (I : Type u) [Finite I] [Nonempty I] :
    Nonempty (ProductModel Q I) := by
  classical
  let M (J : Type u) := Nonempty J → Nonempty (ProductModel Q J)
  refine (Finite.induction_empty_option (P := M) ?_ ?_ ?_ I) ‹Nonempty I›
  · intro J L e h hL
    have hJ := hL.map e.symm
    obtain ⟨m⟩ := h hJ
    exact ⟨reindexModel m e.symm⟩
  · rintro ⟨i⟩
    exact i.elim
  · intro J _ h _
    by_cases hj : Nonempty J
    · obtain ⟨m⟩ := h hj
      exact ⟨optionModel m⟩
    · letI : IsEmpty J := not_nonempty_iff.mp hj
      exact ⟨reindexModel (singleModel Q) (Equiv.ofUnique _ _)⟩

open Specs.BorelsAndChambers (IsPositiveSystem)
open Specs.Pinning (IsSimple)
open private pinnedLift from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.PinnedEquivalence

/-- Choose the split product Borel whose positive roots are the upper matrix roots. -/
private theorem productBorel {Q : RankOneModel k} {I : Type u} [Fintype I] [DecidableEq I]
    (M : ProductModel Q I) :
    ∃ (B : ClosedSubgroup M.pair.G.val) (hB : GeometricBorelConjugacy.IsKBorel B)
      (hTB : SchemeDerivedGroup.IsSubgroupOf M.pair.T B),
      let P : SplitBorelPair k := { M.pair with B := B, borel := hB, containsTorus := hTB }
      ∀ i b, IsSimple P (M.roots (i, b)) ↔ b = true := by
  classical
  let l : Additive (Character M.pair.T.group) →ₗ[ℤ] ℝ :=
    (Algebra.linearMap ℤ ℝ).comp ((∑ i : I, LinearMap.proj i).comp M.weights.toLinearMap)
  have hval (i : I) (b : Bool) :
      l (Additive.ofMul (M.roots (i, b)).val) = if b then 2 else -2 := by
    change (Algebra.linearMap ℤ ℝ) ((∑ j : I, LinearMap.proj j) (M.weights _)) = _
    rw [M.weight_eq]
    cases b <;> simp [signedRoot, LinearMap.sum_apply]
  let S : Set (Root M.pair.T) := {a | 0 < l (Additive.ofMul a.val)}
  have hS (i : I) (b : Bool) : M.roots (i, b) ∈ S ↔ b = true := by
    change 0 < l (Additive.ofMul (M.roots (i, b)).val) ↔ _
    rw [hval]
    cases b <;> norm_num
  have hpos : IsPositiveSystem M.pair.T S := ⟨l, fun a => by
    obtain ⟨⟨i, b⟩, rfl⟩ := M.roots.surjective a
    rw [hval]
    cases b <;> norm_num, rfl⟩
  obtain ⟨_, _, _, hB, _, _, _⟩ :=
    RootData.BorelPositivity.borelPositivity M.pair.G M.pair.reductive M.pair.T
      M.pair.split M.pair.maximal
  obtain ⟨B, hB, hTB, hBS⟩ := hB.2.1 S hpos
  let P : SplitBorelPair k := { M.pair with B := B, borel := hB, containsTorus := hTB }
  refine ⟨B, hB, hTB, fun i b => ⟨fun h => (hS i b).mp (hBS ▸ h.1), ?_⟩⟩
  rintro rfl
  refine ⟨hBS ▸ (hS i true).mpr rfl, ?_⟩
  intro a ha c hc heq
  obtain ⟨⟨j, d⟩, rfl⟩ := M.roots.surjective a
  obtain ⟨⟨q, e⟩, rfl⟩ := M.roots.surjective c
  have hd := (hS j d).mp (hBS ▸ ha)
  have he := (hS q e).mp (hBS ▸ hc)
  subst d
  subst e
  have hm := congrArg (fun z : Character M.pair.T.group => l (Additive.ofMul z)) heq
  change l (Additive.ofMul (M.roots (i, true)).val) =
    l (Additive.ofMul (M.roots (j, true)).val + Additive.ofMul (M.roots (q, true)).val) at hm
  rw [map_add, hval, hval, hval] at hm
  norm_num at hm

private theorem compareProduct {Q : RankOneModel k}
    {I : Type u} [Fintype I] [DecidableEq I] (M : ProductModel Q I)
    (P : SplitBorelPair k) (D : AttachedDatum P) (hY : SimplyConnectedLattice.corootLattice D = ⊤)
    (label : I ≃ D.toBased.base.support)
    (ho : ∀ i j, i ≠ j → RootData.integralCartan D.toBased.datum D.toBased.base (label i) (label j) = 0) :
    ∃ (g : P.G.val ≅ M.pair.G.val) (t : P.T.group ≅ M.pair.T.group),
      P.T.inclusion ≫ g.hom = t.hom ≫ M.pair.T.inclusion ∧
      ∀ i, t.inv ≫ (label i).val.val = M.torusProjection i ≫ (Q.roots true).val := by
  classical
  letI := D.comm
  letI := D.datum.finiteRoots
  letI := D.datum.freeCharacters
  letI := D.datum.freeCocharacters
  letI := D.datum.finiteCharacters
  letI := D.datum.finiteCocharacters
  letI := D.datum.reduced
  let C := D.datum.rootDatum
  obtain ⟨B, hB, hTB, hsimp⟩ := productBorel M
  let P' : SplitBorelPair k := { M.pair with B := B, borel := hB, containsTorus := hTB }
  let E := Classification.Pinning.attachedDatum P'
  letI := E.comm
  let A : Matrix I I ℤ := fun j i => if j = i then 2 else 0
  have hA (j i : I) : RootData.integralCartan C D.base (label j) (label i) = A j i := by
    by_cases e : j = i
    · subst j
      simpa only [A, ite_eq_left rfl, RootData.integralCartan] using! C.root_coroot_two (label i).val
    · simpa only [A, ite_eq_right e] using! ho j i e
  obtain ⟨c, x, _, _, hx, hset⟩ := RootData.AbsoluteDynkinTypes.cartanCoordinates C D.base hY A
    label.symm (by intro i j; simpa only [label.apply_symm_apply] using! hA (label.symm i) (label.symm j))
  have hsimple (i : I) : simpleCharacter A i = signedRoot i true := by
    funext j
    simp [A, simpleCharacter, signedRoot, Pi.single_apply]
  have hroot (a : Root P.T) : ∃ t : I × Bool, x (C.root a) = signedRoot t.1 t.2 := by
    apply cartanRoots_diagonal A (fun _ _ => rfl) (p := (x (C.root a), c.equivFun (C.coroot a)))
    change (x (C.root a), c.equivFun (C.coroot a)) ∈ {p | CartanRoots A p}
    rw [← hset]
    exact Set.mem_range_self a
  have hall (b : I × Bool) : ∃ a : Root P.T, x (C.root a) = signedRoot b.1 b.2 := by
    rcases b with ⟨i, b⟩
    cases b
    · have hn : CartanRoots A (-(simpleCharacter A i), -(Pi.single i 1)) :=
        CartanRoots.neg (CartanRoots.simple i)
      have hm : (-(simpleCharacter A i), -(Pi.single i 1)) ∈ {p | CartanRoots A p} := hn
      rw [← hset] at hm
      obtain ⟨a, ha⟩ := hm
      refine ⟨a, (congrArg Prod.fst ha).trans ?_⟩
      rw [hsimple]
      funext j
      by_cases e : j = i <;> simp [signedRoot, e]
    · exact ⟨(label i).val, by
        simpa only [Equiv.symm_symm, hsimple] using! hx i⟩
  let f := x.trans M.weights.symm
  have hmatch (a : Root P.T) (b : I × Bool) :
      f (C.root a) = E.datum.rootDatum.root (M.roots b) ↔ x (C.root a) = signedRoot b.1 b.2 := by
    obtain ⟨i, b⟩ := b
    rw [E.datum.root_eq, ← M.weights.apply_eq_iff_eq]
    change M.weights (M.weights.symm (x (C.root a))) =
      M.weights (Additive.ofMul (M.roots (i, b)).val) ↔ _
    rw [LinearEquiv.apply_symm_apply, M.weight_eq]
  let h : Root P.T → I × Bool := fun a => (hroot a).choose
  have hh (a : Root P.T) : x (C.root a) = signedRoot (h a).1 (h a).2 := (hroot a).choose_spec
  let d : Root P.T ≃ I × Bool := Equiv.ofBijective h
    ⟨fun a b e => C.root.injective (x.injective (by rw [hh a, hh b, e])),
      fun b => by
        obtain ⟨a, ha⟩ := hall b
        exact ⟨a, signedRoot_injective ((hh a).symm.trans ha)⟩⟩
  have hfin : Finite (Additive (Character P.T.group) ⧸ Submodule.span ℤ (Set.range C.root)) := by
    apply (Submodule.finiteQuotient_iff _).mpr
    exact (corootFullRank C D.base).mp (by
      change Module.finrank ℤ (SimplyConnectedLattice.corootLattice D) = _
      rw [hY, finrank_top])
  let equiv : C.Equiv E.datum.rootDatum :=
    rootEquivOfRootMap C E.datum.rootDatum hfin (d.trans M.roots) (x.trans M.weights.symm)
      (fun a => (hmatch a (h a)).mpr (hh a))

  have hlabel (i : I) : h (label i).val = (i, true) := by
    apply signedRoot_injective
    exact (hh _).symm.trans (by simpa only [Equiv.symm_symm, hsimple] using! hx i)
  have hb : (E.base.support : Set (Root M.pair.T)) =
      equiv.indexEquiv '' (D.base.support : Set (Root P.T)) := by
    ext a
    obtain ⟨⟨i, b⟩, rfl⟩ := M.roots.surjective a
    rw [Finset.mem_coe, E.simple_iff, hsimp i b]
    constructor
    · rintro rfl
      exact ⟨(label i).val, (label i).property, congrArg M.roots (hlabel i)⟩
    · rintro ⟨a, ha, he⟩
      obtain ⟨j, hj⟩ := label.surjective ⟨a, ha⟩
      have hja : (label j).val = a := congrArg Subtype.val hj
      change M.roots (h a) = M.roots (i, b) at he
      rw [← hja, hlabel] at he
      exact (congrArg Prod.snd (M.roots.injective he)).symm
  let Aline := Classification.Pinning.standardAdditiveLine k
  obtain ⟨U, ⟨p⟩⟩ := Classification.Pinning.pinningsExist Aline P
  obtain ⟨V, ⟨q⟩⟩ := Classification.Pinning.pinningsExist Aline P'
  let a : PinnedGroup Aline := ⟨P, U, p⟩
  let b : PinnedGroup Aline := ⟨P', V, q⟩
  obtain ⟨g, hg⟩ := pinnedLift a b D E ⟨equiv, hb.symm⟩
  refine ⟨g.group, g.torus, g.torus_comm, fun i => ?_⟩
  have hw := congrArg (fun z : BasedIso D.toBased E.toBased =>
    z.val.weightEquiv (Additive.ofMul (label i).val.val)) hg
  change Additive.ofMul (g.torus.inv ≫ (label i).val.val) =
    f (Additive.ofMul (label i).val.val) at hw
  have hr := (hmatch (label i).val (i, true)).mpr (by
    simpa only [Equiv.symm_symm, hsimple] using! hx i)
  rw [D.datum.root_eq, E.datum.root_eq] at hr
  exact (congrArg Additive.toMul (hw.trans hr)).trans (M.root_eq i true)


open private pointPost pointPost_comp pointPost_zero from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes
open private rootPoint_comp tangent_weight_of_scalarAction from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
open private subgroupIso rootPoint_surjective from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.OrderedRootProducts
open private normalizes_of_scalarAction from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.PinnedUniqueness
open private pushScalarAction from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.PinnedEquivalence
open private transportSubgroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate

private def upperInFactor {Q : RankOneModel k} {I : Type u} [DecidableEq I]
    (M : ProductModel Q I) (i : I) : Q.upper.group ⟶ M.pair.G.val :=
  Fan.IsLimit.lift M.product (fun j => if j = i then Q.upper.inclusion else 0)

private theorem upperInFactor_projection {Q : RankOneModel k} {I : Type u} [DecidableEq I]
    (M : ProductModel Q I) (i j : I) :
    upperInFactor M i ≫ M.projection j = if j = i then Q.upper.inclusion else 0 :=
  Fan.IsLimit.fac M.product _ j

private def upperSubgroup {Q : RankOneModel k} {I : Type u} [DecidableEq I]
    (M : ProductModel Q I) (i : I) : ClosedSubgroup M.pair.G.val := by
  let f := upperInFactor M i
  let g := M.projection i
  letI := M.pair.G.property.1
  letI : IsClosedImmersion (f.hom.hom.left ≫ g.hom.hom.left) := by
    change IsClosedImmersion (f ≫ g).hom.hom.left
    rw [upperInFactor_projection, ite_eq_left rfl]
    exact Q.upper.isClosedImmersion
  exact ⟨_, f, IsClosedImmersion.of_comp f.hom.hom.left g.hom.hom.left⟩

private theorem upperInFactor_scalar {Q : RankOneModel k} {I : Type u} [Finite I] [DecidableEq I]
    (M : ProductModel Q I) (i : I) :
    HasScalarAction M.pair.T (M.torusProjection i ≫ (Q.roots true).val)
      (Q.parameter.hom ≫ upperInFactor M i) := by
  intro R t a
  let g : GroupPoints M.pair.G.val R := pointPost M.pair.T.inclusion R t
  let χ := M.torusProjection i ≫ (Q.roots true).val
  let x := Q.parameter.hom ≫ upperInFactor M i
  change g * rootPoint x R a * g⁻¹ = rootPoint x R (characterValue χ R t * a)
  let L := isLimitFanMkObjOfIsLimit (Grp.forget (SchemeOver k))
    (fun _ : I => Q.pair.G.val) M.projection M.product
  apply Fan.IsLimit.hom_ext L
  intro j
  change pointPost (M.projection j) R (g * rootPoint x R a * g⁻¹) =
    pointPost (M.projection j) R (rootPoint x R (characterValue χ R t * a))
  have hx (v : R) : pointPost (M.projection j) R (rootPoint x R v) =
      pointPost (if j = i then Q.upper.inclusion else 0) R (rootPoint Q.parameter.hom R v) := by
    change rootPoint x R v ≫ (M.projection j).hom.hom =
      rootPoint Q.parameter.hom R v ≫ ((if j = i then Q.upper.inclusion else 0) :
        Q.upper.group ⟶ Q.pair.G.val).hom.hom
    dsimp only [x]
    rw [← rootPoint_comp, Category.assoc, upperInFactor_projection, rootPoint_comp]
  rw [map_mul, map_mul, map_inv, hx, hx]
  by_cases hj : j = i
  · subst j
    simp only [pointPost_comp, g, M.torus_comm]
    have h := Q.scalar R (pointPost (M.torusProjection i) R t) a
    change (pointPost Q.pair.T.inclusion R (pointPost (M.torusProjection i) R t)) *
        rootPoint (Q.parameter.hom ≫ Q.upper.inclusion) R a *
          (pointPost Q.pair.T.inclusion R (pointPost (M.torusProjection i) R t))⁻¹ =
        rootPoint (Q.parameter.hom ≫ Q.upper.inclusion) R
          (characterValue (Q.roots true).val R (pointPost (M.torusProjection i) R t) * a) at h
    rw [pointPost_comp, ← characterValue_pullback, rootPoint_comp, rootPoint_comp] at h
    exact h
  · simp only [ite_eq_right hj, pointPost_zero, mul_one, mul_inv_cancel]

private theorem placedRoot {Q : RankOneModel k} {I : Type u} [Finite I] [DecidableEq I]
    (M : ProductModel Q I) (P : SplitBorelPair k)
    (g : P.G.val ≅ M.pair.G.val) (t : P.T.group ≅ M.pair.T.group)
    (ht : P.T.inclusion ≫ g.hom = t.hom ≫ M.pair.T.inclusion)
    (i : I) (a : Root P.T) (ha : t.inv ≫ a.val = M.torusProjection i ≫ (Q.roots true).val)
    (V : ClosedSubgroup P.G.val) (hV : IsRootSubgroup P.T V a.val) :
    ∃ e : V.group ≅ Q.upper.group, ∀ j,
      V.inclusion ≫ g.hom ≫ M.projection j =
        e.hom ≫ (if j = i then Q.upper.inclusion else 0) := by
  let U := transportSubgroup g.symm (upperSubgroup M i)
  have hsquare : M.pair.T.inclusion ≫ g.inv = t.inv ≫ P.T.inclusion := by
    apply (cancel_mono g.hom).mp
    simp [Category.assoc, ht]
  have hact := pushScalarAction (P := M.pair) (Q := P) g.symm t.symm hsquare _
    _ (upperInFactor_scalar M i)
  have he : t.hom ≫ (M.torusProjection i ≫ (Q.roots true).val) = a.val := by
    rw [← ha, Iso.hom_inv_id_assoc]
  change HasScalarAction P.T (t.hom ≫ _) ((Q.parameter.hom ≫ upperInFactor M i) ≫ g.inv) at hact
  rw [he, Category.assoc] at hact
  have hroot : IsRootSubgroup P.T U a.val :=
    ⟨Q.isRoot.1, Q.isRoot.2.1,
      normalizes_of_scalarAction P.G.property.1 Q.parameter hact,
      tangent_weight_of_scalarAction P.T U a.val Q.line Q.parameter hact⟩
  obtain ⟨_, _, W, _, _, _, _, unique⟩ :=
    (RootData.RootGroups.rootSubgroups P.G P.reductive P.T P.split P.maximal).2 a.val a.property
  let f := subgroupIso (unique V hV)
  let e := subgroupIso (unique U hroot)
  let c : V.group ≅ Q.upper.group := f.val.symm ≪≫ e.val
  have hc : c.hom ≫ U.inclusion = V.inclusion := by
    change (f.val.inv ≫ e.val.hom) ≫ U.inclusion = V.inclusion
    rw [Category.assoc, e.property]
    exact (congrArg (f.val.inv ≫ ·) f.property.symm).trans (f.val.inv_hom_id_assoc _)
  refine ⟨c, fun j => ?_⟩
  rw [← hc]
  change (c.hom ≫ (upperInFactor M i ≫ g.inv)) ≫ g.hom ≫ M.projection j = _
  simp only [Category.assoc, Iso.inv_hom_id_assoc, upperInFactor_projection]

theorem splitRankOneProduct : Specs.Arithmetic.LabelledSplitRankOneProduct.Statement.{u} := by
  classical
  intro F I _ _ _ P D hss hsc
  letI := D.comm
  dsimp only
  intro label ho V hV
  letI := Fintype.ofFinite I
  have hY : SimplyConnectedLattice.corootLattice D = ⊤ :=
    (Classification.SimplyConnectedLattice.latticeCriterion P.G hss P.T P.split P.maximal D.datum).mp hsc
  obtain ⟨Q⟩ := rankOneModel F
  obtain ⟨M⟩ := productModel Q I
  obtain ⟨g, t, ht, hr⟩ := compareProduct M P D hY label ho
  let π : I → (P.G.val ⟶ Q.pair.G.val) := fun i => g.hom ≫ M.projection i
  refine ⟨Q.pair.G, Q.points, π, ⟨?_⟩, ?_⟩
  · refine Fan.IsLimit.mk _ (fun s => Fan.IsLimit.lift M.product s.proj ≫ g.inv) ?_ ?_
    · intro s j
      change (_ ≫ g.inv) ≫ g.hom ≫ M.projection j = _
      simpa only [Category.assoc, Iso.inv_hom_id_assoc] using! Fan.IsLimit.fac M.product s.proj j
    · intro s f hf
      apply (cancel_mono g.hom).mp
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      apply Fan.IsLimit.hom_ext M.product
      intro j
      exact (Category.assoc _ _ _).trans ((hf j).trans (Fan.IsLimit.fac M.product s.proj j).symm)
  · intro i
    obtain ⟨e, he⟩ := placedRoot M P g t ht i (label i).val (hr i) (V i) (hV i)
    have hdiag : (V i).inclusion ≫ π i = e.hom ≫ Q.upper.inclusion := by
      simpa [π] using! he i
    refine ⟨fun j hj => by simpa [π, hj] using! he j, ?_, ?_⟩
    · rw [hdiag]
      letI := Q.upper.isClosedImmersion
      let L := Grp.forget (SchemeOver F) ⋙ Over.forget _
      letI : IsIso e.hom.hom.hom.left := L.map_isIso e.hom
      change IsClosedImmersion (e.hom.hom.hom.left ≫ Q.upper.inclusion.hom.hom.left)
      infer_instance
    · intro R
      rw [hdiag]
      ext z
      constructor
      · rintro ⟨p, rfl⟩
        obtain ⟨a, ha⟩ := rootPoint_surjective Q.parameter R (p ≫ e.hom.hom.hom)
        exact ⟨a, by simpa only [rootPoint_comp, ha, Grp.comp_hom_hom, Category.assoc]
          using (Q.matrix_eq R a).symm⟩
      · rintro ⟨a, rfl⟩
        refine ⟨rootPoint Q.parameter.hom R a ≫ e.inv.hom.hom, ?_⟩
        have hi : e.inv.hom.hom ≫ e.hom.hom.hom ≫ Q.upper.inclusion.hom.hom =
            Q.upper.inclusion.hom.hom :=
          ((Grp.forget (SchemeOver F)).mapIso e).inv_hom_id_assoc _
        simpa only [Grp.comp_hom_hom, Category.assoc, hi, rootPoint_comp]
          using! Q.matrix_eq R a

end
end LinearAlgebraicGroups.Arithmetic.LabelledSplitRankOneProduct
