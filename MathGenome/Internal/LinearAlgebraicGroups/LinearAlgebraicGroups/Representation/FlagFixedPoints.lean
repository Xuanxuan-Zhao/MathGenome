import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.FlagFixedPoints
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.EquivariantCoherentRestriction
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagLocalizationGeometry
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagDerivedRestriction
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagEquivariantEulerMap
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.Localization.BaseChange

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Representation.FlagFixedPoints

open _root_.LinearAlgebraicGroups.Specs (GroupScheme AffineAlgebraicGroup ClosedSubgroup)
open Specs.AbstractPairing (Datum Root)
open Specs.CharacterDescent (Character)
open Specs.DatumAndWeyl (Identification)
open Specs.EquivariantAffineModules hiding pointAction
open Specs.EquivariantCoherentRestriction (HasRestrictionSequence)
open Specs.FlagFixedPoints
open Specs.FlagLineBundle (OppositeBorelPair BorelProjection)
open Specs.FlagLocalizationGeometry (PositiveRoot cotangentWeight torusAction RestrictionGeometry)
open Specs.QuotientEmbedding (Presentation)
open EquivariantAffineModules
open EquivariantCoherentRestriction (classOf_twist)

noncomputable section

set_option Elab.async false

variable {k : Type u} [Field k]

/-- Equivariant closed direct image and open restriction give the right exact
sequence on coherent sheaf classes. -/
theorem restrictionSequence : RestrictionSequence.{u} :=
  EquivariantCoherentRestriction.restrictionSequence

private theorem inverseTwist {T : GroupScheme k} {X : SchemeOver k}
    {a : ModObj T.X X} {f : Γ(X.left, ⊤)} {χ : Character T}
    (hf : IsUnit f) (hw : HasFunctionWeight a f χ) (F : EquivariantCoherent a) :
    IsTwist χ⁻¹ F F := by
  obtain ⟨r, rfl⟩ := hf
  let e := (multiplyUnit F.sheaf r).symm
  refine ⟨e, ?_⟩
  apply (cancel_mono ((Scheme.Modules.pullback a.smul.left).map e.inv)).1
  rw [Category.assoc, Category.assoc, Category.assoc, ← Functor.map_comp,
    Iso.hom_inv_id]
  rw [(Scheme.Modules.pullback a.smul.left).map_id F.sheaf, Category.comp_id]
  change F.lin.iso.hom ≫ (Scheme.Modules.pullback a.smul.left).map (multiply F.sheaf ↑r) =
    (Scheme.Modules.pullback (snd T.X X).left).map (multiply F.sheaf ↑r) ≫ F.lin.iso.hom ≫
      multiply _ ((fst T.X X).left.appTop (characterFunction χ⁻¹))
  rw [pullback_multiply, pullback_multiply, multiply_natural, Category.assoc, multiply_comp]
  apply congrArg (fun c => F.lin.iso.hom ≫ multiply _ c)
  rw [mul_comm]
  exact hw

private theorem coordinateStratum
    {T : GroupScheme k} {X : SchemeOver k} (a : ModObj T.X X)
    (f : Γ(X.left, ⊤)) (χ : Character T) (hf : IsUnit f) (hw : HasFunctionWeight a f χ)
    (c : GZero a) : (1 - eChar χ) • c = 0 := by
  have hgen (F : EquivariantCoherent a) : (1 - eChar χ) • classOf F = 0 := by
    have h := classOf_twist (inverseTwist hf hw F)
    have hmul : eChar χ * eChar χ⁻¹ = 1 := by
      change MonoidAlgebra.of ℤ _ χ * MonoidAlgebra.of ℤ _ χ⁻¹ = 1
      rw [← map_mul, mul_inv_cancel, map_one]
    rw [sub_smul, one_smul, sub_eq_zero]
    have h' := congrArg (fun x : GZero a => eChar χ • x) h
    simpa only [smul_smul, hmul, one_smul] using h'.symm
  obtain ⟨d, rfl⟩ := Submodule.mkQ_surjective (relationSubmodule a) c
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, smul_add, hx, hy, add_zero]
  | single F r =>
    rw [← Finsupp.smul_single_one, map_smul, smul_comm]
    change r • ((1 - eChar χ) • classOf F) = 0
    rw [hgen, smul_zero]

/-- Multiplication by a homogeneous unit identifies the inverse-character twist
with the original sheaf, so its character factor kills every class. -/
theorem coordinateStratumVanishing : CoordinateStratumVanishing.{u} :=
  fun a f χ hf hw c => coordinateStratum a f χ hf hw c

/-- A stratum with an invertible root-weight coordinate has zero localized
equivariant class group. -/
theorem localizedClasses_subsingleton_of_root_unit {G : AffineAlgebraicGroup k}
    {S : ClosedSubgroup G.val} {X : SchemeOver k} (a : ModObj S.group.X X)
    (f : Γ(X.left, ⊤)) (α : Root S) (hf : IsUnit f) (hw : HasFunctionWeight a f α.val) :
    Subsingleton (LocalGZero S a) := by
  apply LocalizedModule.subsingleton_iff.mpr
  intro c
  exact ⟨1 - eChar α.val, Submonoid.subset_closure (Set.mem_range_self α),
    coordinateStratum a f α.val hf hw c⟩


section LocalizedClasses

variable {G : AffineAlgebraicGroup k} {S : ClosedSubgroup G.val} {X Y Z : SchemeOver k}
  {a : ModObj S.group.X X} {b : ModObj S.group.X Z} {c : ModObj S.group.X Y}

/-- If the open term vanishes after localization, the localized direct image
from the closed term is surjective. -/
theorem localizedPush_surjective_of_vanishing
    {i : Z ⟶ X} {j : Y ⟶ X} (h : HasRestrictionSequence (a := a) (b := b) (c := c) i j)
    (hV : Subsingleton (LocalGZero S c)) :
    ∃ push : GZero b →ₗ[CharacterRing S.group] GZero a,
      Function.Surjective (LocalizedModule.map (rootFactors S) push) ∧
      ∀ H, ∃ (F : EquivariantCoherent a) (e : F.sheaf ≅
        (Scheme.Modules.pushforward i.left).obj H.sheaf),
        IsEquivariantPushforward i H F e ∧ push (classOf H) = classOf F := by
  obtain ⟨push, res, hex, _, hpush, _⟩ := h
  have hex' := LocalizedModule.map_exact (rootFactors S) push res hex
  exact ⟨push, fun m => (hex' m).mp (hV.elim _ _), hpush⟩

/-- Vanishing on both terms of an invariant closed-open decomposition
implies vanishing on the whole scheme. -/
theorem localizedClasses_subsingleton_of_closed_open
    {i : Z ⟶ X} {j : Y ⟶ X} (h : HasRestrictionSequence (a := a) (b := b) (c := c) i j)
    (hZ : Subsingleton (LocalGZero S b)) (hV : Subsingleton (LocalGZero S c)) :
    Subsingleton (LocalGZero S a) := by
  obtain ⟨push, hsurj, _⟩ := localizedPush_surjective_of_vanishing h hV
  exact hsurj.subsingleton

end LocalizedClasses

section Roots

variable {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
  [IsCommMonObj P.torus.group.X] {D : Datum P.torus}

/-- The weights occurring in the cotangent product are roots, so each factor
is among the denominators used in the localization. -/
theorem cotangentProduct_isUnit (J : Identification D) (w : D.rootDatum.weylGroup)
    [Fintype (PositiveRoot P)] : IsUnit (localScalar P.torus (cotangentProduct J w)) := by
  rw [cotangentProduct, map_prod]
  refine IsUnit.prod_iff.mpr fun α _ => ?_
  have hneg : ∃ β : Root P.torus, D.rootDatum.root β = -D.rootDatum.root α.val :=
    D.rootDatum.neg_root_mem α.val
  obtain ⟨β, hβ⟩ := hneg
  let rootIndex := D.rootDatum.weylGroupToPerm w β
  have hχ : cotangentWeight J w α = rootIndex.val := by
    apply Additive.ofMul.injective
    rw [cotangentWeight, ← J.characterAction]
    change w.val.weightEquiv (-Additive.ofMul α.val.val) = Additive.ofMul rootIndex.val
    rw [← D.root_eq α.val, ← hβ, ← D.root_eq rootIndex]
    exact D.rootDatum.weylGroup_apply_root w β
  rw [hχ]
  exact IsLocalization.map_units _ (⟨_, Submonoid.subset_closure (Set.mem_range_self rootIndex)⟩ :
    rootFactors P.torus)

end Roots

section Diagonal

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
  {I : Type*} [Fintype I] [DecidableEq I] {v : I → M}
  {δ : I → R} {res : I → M →ₗ[R] R}

/-- A spanning family with unit diagonal restrictions is a basis. -/
theorem basis_of_diagonal_restrictions
    (hspan : Submodule.span R (Set.range v) = ⊤)
    (hunit : ∀ i, IsUnit (δ i))
    (hdiag : ∀ i j, res i (v j) = if i = j then δ i else 0) :
    ∃ b : Module.Basis I R M, ∀ i, b i = v i := by
  have hind : LinearIndependent R v := by
    rw [Fintype.linearIndependent_iff]
    intro f hf i
    have hh := congrArg (res i) hf
    have hs : ∑ j, f j * (if i = j then δ i else 0) = f i * δ i := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        simp [Ne.symm hj]
      · simp
    simp only [map_sum, map_smul, smul_eq_mul, hdiag, map_zero, hs] at hh
    exact (IsUnit.mul_left_inj (hunit i)).mp (hh.trans (zero_mul _).symm)
  exact ⟨Module.Basis.mk hind hspan.ge, Module.Basis.mk_apply _ _⟩

/-- An additive Euler map sending each point basis vector to one is the sum
of the diagonal restrictions divided by the corresponding cotangent factors. -/
theorem euler_of_diagonal_restrictions (b : Module.Basis I R M)
    (hunit : ∀ i, IsUnit (δ i))
    (hdiag : ∀ i j, res i (b j) = if i = j then δ i else 0)
    (euler : M →ₗ[R] R) (heuler : ∀ i, euler (b i) = 1) (x : M) :
    euler x = ∑ i, res i x * Ring.inverse (δ i) := by
  have hcoeff (i : I) : res i x = b.repr x i * δ i := by
    conv_lhs => rw [← b.sum_repr x]
    simp only [map_sum, map_smul, smul_eq_mul, hdiag]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Ne.symm hj]
    · simp
  calc
    euler x = ∑ i, b.repr x i := by
      calc
        euler x = euler (∑ i, b.repr x i • b i) := congrArg euler (b.sum_repr x).symm
        _ = ∑ i, b.repr x i := by simp only [map_sum, map_smul, heuler, smul_eq_mul, mul_one]
    _ = ∑ i, res i x * Ring.inverse (δ i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hcoeff, Ring.mul_inverse_cancel_right _ _ (hunit i)]

end Diagonal


section RootOpenCover

open FlagLocalizationGeometry (exists_invariantClosedSubscheme)
open private reduced_closedScheme_product preimage_invariantOpen restrictionGeometry_of_closed
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagLocalizationGeometry
open private splitTorusSmooth from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.WeylScheme
open private geometricallyReduced_of_smooth from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SmoothnessCriteria

variable {T : GroupScheme k} {X : SchemeOver k}

theorem basicOpen_pullback_isUnit (f : Γ(X.left, ⊤)) :
    IsUnit ((openEmbedding X (X.left.basicOpen f)).left.appTop f) := by
  let U := X.left.basicOpen f
  change IsUnit (U.ι.appTop f)
  have hu := X.left.toRingedSpace.isUnit_res_basicOpen f
  change IsUnit (X.left.presheaf.map (homOfLE (X.left.basicOpen_le f)).op f) at hu
  have hr (V : X.left.Opens) (h : V = U) :
      IsUnit (X.left.presheaf.map V.leTop.op f) := by
    subst V
    exact hu
  rw [Scheme.Opens.ι_appTop]
  exact hr _ U.ι_image_top

/-- The nonvanishing locus of a root-weight function has vanishing
localized equivariant Grothendieck group. -/
theorem localizedClasses_subsingleton_of_root_basicOpen
    {G : AffineAlgebraicGroup k} {S : ClosedSubgroup G.val}
    (a : ModObj S.group.X X) (f : Γ(X.left, ⊤)) (α : Root S)
    (hf : HasFunctionWeight a f α.val) :
    Subsingleton (LocalGZero S
      (invariantOpenAction a (X.left.basicOpen f) (basicOpen_invariant_of_weight f α.val hf))) := by
  let U := X.left.basicOpen f
  let j := openEmbedding X U
  let hU := basicOpen_invariant_of_weight f α.val hf
  let c := invariantOpenAction a U hU
  have hj : IsEquivariantMap a c j := invariantOpenInclusion_equivariant a U hU
  exact localizedClasses_subsingleton_of_root_unit c (j.left.appTop f) α
    (basicOpen_pullback_isUnit f) (functionWeight_pullback j hj f α.val hf)

private theorem classes_subsingleton_of_empty {T : GroupScheme k} {X : SchemeOver k}
    [IsEmpty X.left] (a : ModObj T.X X) : Subsingleton (GZero a) := by
  have hz : (LinearMap.id : GZero a →ₗ[CharacterRing T] GZero a) = 0 := by
    apply classMap_ext
    intro F
    change classOf F = 0
    apply classOf_isZero
    apply (IsZero.iff_id_eq_zero _).mpr
    apply Scheme.Modules.hom_ext
    intro U
    let S : TopCat.Sheaf Ab X.left := ⟨F.sheaf.presheaf, F.sheaf.isSheaf⟩
    have hU : U = ⊥ := by
      apply bot_unique
      intro x _
      exact isEmptyElim x
    have h : IsZero Γ(F.sheaf, U) := (S.isTerminalOfEqEmpty hU).isZero
    exact h.eq_of_src _ _
  refine (subsingleton_iff_forall_eq 0).mpr fun x => ?_
  exact congrArg (fun f : GZero a →ₗ[CharacterRing T] GZero a => f x) hz

/-- Repeated restriction to a root-weight principal open and its zero locus
kills the localized group whenever these finitely many principal opens cover. -/
theorem localizedClasses_subsingleton_of_root_cover {G : AffineAlgebraicGroup k}
    (S : ClosedSubgroup G.val) (restriction : RestrictionSequence.{u})
    (hsplit : Specs.GeometricRadicals.IsSplitTorus S.group)
    (n : ℕ)
    {X : SchemeOver k} (a : ModObj S.group.X X)
    [LocallyOfFiniteType X.hom] [IsSeparated X.hom] [CompactSpace X.left]
    (hX : ∀ x : X.left, ∃ U : X.left.Opens,
      x ∈ U ∧ IsAffineOpen U ∧ a.smul.left ⁻¹ᵁ U = (snd S.group.X X).left ⁻¹ᵁ U)
    (f : Fin n → Γ(X.left, ⊤)) (α : Fin n → Root S)
    (h : ∀ i, HasFunctionWeight a (f i) (α i).val)
    (hcover : ∀ x : X.left, ∃ i, x ∈ X.left.basicOpen (f i)) :
    Subsingleton (LocalGZero S a) := by
  let : Smooth S.group.X.hom := splitTorusSmooth hsplit
  let : GeometricallyReduced S.group.X.hom := geometricallyReduced_of_smooth S.group.X.hom
  induction n generalizing X with
  | zero =>
    let : IsEmpty X.left := ⟨fun x => by obtain ⟨i, -⟩ := hcover x; exact i.elim0⟩
    let : Subsingleton (GZero a) := classes_subsingleton_of_empty a
    infer_instance
  | succ n ih =>
    let U := X.left.basicOpen (f 0)
    let Z : Closeds X.left := ⟨(U : Set X.left)ᶜ, U.isOpen.isClosed_compl⟩
    have hU : a.smul.left ⁻¹ᵁ U = (snd S.group.X X).left ⁻¹ᵁ U :=
      basicOpen_invariant_of_weight (f 0) (α 0).val (h 0)
    have hZ : a.smul.left ⁻¹' (Z : Set X.left) = (snd S.group.X X).left ⁻¹' (Z : Set X.left) := by
      change a.smul.left ⁻¹' (U : Set X.left)ᶜ = (snd S.group.X X).left ⁻¹' (U : Set X.left)ᶜ
      simp only [Set.preimage_compl]
      exact congrArg (fun W : (S.group.X ⊗ X).left.Opens => (W : Set (S.group.X ⊗ X).left)ᶜ) hU
    obtain ⟨Y, b, i, _, hi, he, hr⟩ := exists_invariantClosedSubscheme a Z hZ
      (reduced_closedScheme_product Z)
    let := hi
    let c := invariantOpenAction a U hU
    let j := openEmbedding X U
    have hj : IsEquivariantMap a c j := invariantOpenInclusion_equivariant a U hU
    have hc : Set.range j.left = (Set.range i.left)ᶜ := by
      rw [hr]
      exact (Scheme.Opens.range_ι U).trans (compl_compl _).symm
    have hseq := restriction a b c i j hsplit inferInstance inferInstance inferInstance hX
      hi (inferInstanceAs (IsOpenImmersion U.ι)) he hj hc
    apply localizedClasses_subsingleton_of_closed_open hseq ?_
      (localizedClasses_subsingleton_of_root_basicOpen a (f 0) (α 0) (h 0))
    obtain ⟨hft, hcompact, hsep, hAff⟩ :=
      restrictionGeometry_of_closed i he ⟨inferInstance, inferInstance, inferInstance, hX⟩
    let := hft
    let := hcompact
    let := hsep
    apply ih b hAff
      (fun r => i.left.appTop (f r.succ)) (fun r => α r.succ)
      (fun r => functionWeight_pullback i he (f r.succ) (α r.succ).val (h r.succ))
    intro y
    obtain ⟨r, hmem⟩ := hcover (i.left y)
    have hz : i.left y ∉ U := by
      have ht : i.left y ∈ (Z : Set X.left) := hr ▸ Set.mem_range_self y
      exact ht
    have hr0 : r ≠ 0 := by
      intro hr0
      subst r
      exact hz hmem
    have eq : (r.pred hr0).succ = r := Fin.succ_pred r hr0
    refine ⟨r.pred hr0, ?_⟩
    rw [eq, ← Scheme.preimage_basicOpen_top]
    exact hmem


end RootOpenCover

section Complement

open Specs.FlagLocalizationGeometry
  (InvariantClosed InvariantComplement ComplementFiltration OrderedCellCoordinates)
open private equivariant_of_comp_mono equivariant_comp restrictionGeometry_of_closed
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagLocalizationGeometry

variable {G : AffineAlgebraicGroup k} {S : ClosedSubgroup G.val}
  {X Y : SchemeOver k} {a : ModObj S.group.X X} {b : ModObj S.group.X Y}

private theorem restriction_of_geometry (hS : IsSplitTorus S.group)
    (hX : RestrictionGeometry a) (Z : InvariantClosed a) (V : InvariantComplement a Z) :
    HasRestrictionSequence (a := a) (b := Z.action) (c := V.action) Z.inclusion V.inclusion :=
  restrictionSequence a Z.action V.action Z.inclusion V.inclusion hS
    hX.1 hX.2.2.1 hX.2.1 hX.2.2.2 Z.closedImmersion V.openImmersion
    Z.equivariant V.equivariant V.range_eq

private theorem equivariant_inverse {T : GroupScheme k}
    {a : ModObj T.X X} {b : ModObj T.X Y} (e : Y ≅ X)
    (he : IsEquivariantMap a b e.hom) : IsEquivariantMap b a e.inv := by
  apply equivariant_of_comp_mono he
  simp [Specs.FlagLocalizationGeometry.IsEquivariantMap]

private theorem vanishing_of_equivariant_iso (hS : IsSplitTorus S.group)
    (hX : RestrictionGeometry a) (e : Y ⟶ X) [IsIso e] (he : IsEquivariantMap a b e)
    (hY : Subsingleton (LocalGZero S b)) : Subsingleton (LocalGZero S a) := by
  let U : X.left.Opens := ⊥
  have hU : a.smul.left ⁻¹ᵁ U = (snd S.group.X X).left ⁻¹ᵁ U := rfl
  let j := openEmbedding X U
  let c := invariantOpenAction a U hU
  let : IsEmpty (openSubscheme X U).left := by
    exact ⟨fun x => x.property⟩
  let : Subsingleton (GZero c) := classes_subsingleton_of_empty c
  have hr : Set.range j.left = (Set.range e.left)ᶜ := by
    rw [show Set.range j.left = (U : Set X.left) from Scheme.Opens.range_ι U,
      e.left.surjective.range_eq]
    simp [U]
  have hseq := restrictionSequence a b c e j hS hX.1 hX.2.2.1 hX.2.1 hX.2.2.2
    inferInstance (inferInstanceAs (IsOpenImmersion U.ι))
    he (invariantOpenInclusion_equivariant a U hU) hr
  exact localizedClasses_subsingleton_of_closed_open hseq hY inferInstance

/-- Pull the root-coordinate cover of a punctured cell back to the actual
open stratum in the filtration. -/
private theorem vanishing_of_punctured_cell (hS : IsSplitTorus S.group)
    {I : Type u} [Finite I] (hY : RestrictionGeometry b)
    (j : Y ⟶ X) (hj : IsEquivariantMap a b j)
    (f : I → Γ(X.left, ⊤)) (α : I → Root S)
    (hf : ∀ i, HasFunctionWeight a (f i) (α i).val)
    (hrange : Set.range j.left = ⋃ i, (X.left.basicOpen (f i) : Set X.left)) :
    Subsingleton (LocalGZero S b) := by
  let := hY.1
  let := hY.2.1
  let := hY.2.2.1
  let := Fintype.ofFinite I
  let e := (Fintype.equivFin I).symm
  apply localizedClasses_subsingleton_of_root_cover S restrictionSequence hS (Fintype.card I)
    b hY.2.2.2 (fun i => j.left.appTop (f (e i))) (fun i => α (e i))
    (fun i => functionWeight_pullback j hj (f (e i)) (α (e i)).val (hf (e i)))
  intro y
  have hy : j.left y ∈ ⋃ i, (X.left.basicOpen (f i) : Set X.left) := hrange ▸ Set.mem_range_self y
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
  refine ⟨e.symm i, ?_⟩
  rw [e.apply_symm_apply, ← Scheme.preimage_basicOpen_top]
  exact hi

private theorem vanishing_of_complement_filtration
    (hS : IsSplitTorus S.group) (Z : InvariantClosed a) (V : InvariantComplement a Z)
    (hV : RestrictionGeometry V.action)
    {W : Type u} {cells : W → SchemeOver k} {acts : ∀ w, ModObj S.group.X (cells w)}
    {inc : ∀ w, cells w ⟶ X} {o : ∀ w, 𝟙_ (SchemeOver k) ⟶ cells w}
    (F : ComplementFiltration a Z V cells acts inc o)
    (hstratum : ∀ (w : W) {O : SchemeOver k} (c : ModObj S.group.X O)
      (j : O ⟶ cells w), IsEquivariantMap (acts w) c j →
      Set.range j.left = (Set.range (o w).left)ᶜ → RestrictionGeometry c →
      Subsingleton (LocalGZero S c)) : Subsingleton (LocalGZero S V.action) := by
  have hs (i : Fin (F.length + 1)) : Subsingleton (LocalGZero S (F.stage i).action) := by
    induction i using Fin.induction with
    | zero =>
      let := F.first_empty
      let := classes_subsingleton_of_empty (F.stage 0).action
      infer_instance
    | succ i ih =>
      obtain ⟨A, e, _, he, O, j, _, hj, hr, _, hO⟩ := F.step i
      have hstage := F.geometry i.succ
      let : IsClosedImmersion A.inclusion.left := A.closedImmersion
      have hA := restrictionGeometry_of_closed A.inclusion A.equivariant hstage
      exact localizedClasses_subsingleton_of_closed_open (restriction_of_geometry hS hstage A O)
        (vanishing_of_equivariant_iso hS hA e.inv (equivariant_inverse e he) ih)
        (hstratum (F.order i) O.action j hj hr hO)
  let := F.last_full
  exact vanishing_of_equivariant_iso hS hV (F.stage (Fin.last F.length)).inclusion
    (F.stage _).equivariant (hs _)

private theorem inverse_is_root [IsCommMonObj S.group.X] {D : Datum S} (α : Root S) :
    ∃ β : Root S, β.val = α.val⁻¹ := by
  obtain ⟨β, hβ⟩ := D.rootDatum.neg_root_mem α
  refine ⟨β, Additive.ofMul.injective ?_⟩
  change Additive.ofMul β.val = -Additive.ofMul α.val
  simpa only [D.root_eq] using hβ

private theorem vanishing_of_orderedCell [IsCommMonObj S.group.X] (D : Datum S)
    {B : ClosedSubgroup G.val} {Q : Presentation B} {a : ModObj G.val.X Q.scheme}
    {g : 𝟙_ (SchemeOver k) ⟶ G.val.X} {H : ClosedSubgroup G.val}
    {U : Specs.OrderedRootProducts.RootSubgroupFamily S} {I : Set (Root S)}
    {C : Specs.BruhatOrbitParametrization.Cell (T := S) Q a g H}
    (hS : IsSplitTorus S.group) (c : OrderedCellCoordinates C U I)
    {Y : SchemeOver k} {b : ModObj S.group.X Y} (j : Y ⟶ C.orbit)
    (hj : IsEquivariantMap c.action b j)
    (hr : Set.range j.left = (Set.range (η[H.group.X] ≫ C.orbitIso.hom).left)ᶜ)
    (hY : RestrictionGeometry b) : Subsingleton (LocalGZero S b) := by
  let := D.finiteRoots
  choose β hβ using fun α : I => inverse_is_root (D := D) α.val
  exact vanishing_of_punctured_cell hS hY j hj
    (fun α : I => c.polynomial.coordinates (MvPolynomial.X α)) β
    (fun α => (hβ α).symm ▸ c.polynomial.weight α) (hr.trans c.puncture.symm)

end Complement

section LocalizationMaps

variable {G : AffineAlgebraicGroup k} {S : ClosedSubgroup G.val}
  {X : SchemeOver k} {a : ModObj S.group.X X}

/-- Scalar extension of a character-valued map on equivariant classes. -/
private def localizeCharacterMap (f : GZero a →ₗ[CharacterRing S.group] CharacterRing S.group) :
    LocalGZero S a →ₗ[LocalCharacterRing S] LocalCharacterRing S :=
  (IsLocalizedModule.isBaseChange (rootFactors S) (LocalCharacterRing S)
    (LocalizedModule.mkLinearMap (rootFactors S) (GZero a))).lift
      ((Algebra.linearMap (CharacterRing S.group) (LocalCharacterRing S)).comp f)

@[simp]
private theorem localizeCharacterMap_class
    (f : GZero a →ₗ[CharacterRing S.group] CharacterRing S.group) (F : EquivariantCoherent a) :
    localizeCharacterMap (S := S) f (localClass F) = localScalar S (f (classOf F)) :=
  IsBaseChange.lift_eq _ _ _

end LocalizationMaps

section Charts

open Specs.FlagDerivedRestriction (PolynomialChart polynomialAlgebra origin pointScheme)
open Specs.FlagLocalizationGeometry (PolynomialCoordinates)
open private actionOfMono from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.EquivariantAffineModules
open private equivariant_of_comp_mono equivariant_comp from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagLocalizationGeometry

variable {T : GroupScheme k} {X Y : SchemeOver k}

private theorem affinePoint_eq_terminal (k : Type u) [Field k] :
    pointScheme k = 𝟙_ (SchemeOver k) := by
  change Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k k))) =
    Over.mk (𝟙 (Spec (CommRingCat.of k)))
  rw [show CommRingCat.ofHom (algebraMap k k) = 𝟙 (CommRingCat.of k) from rfl, Spec.map_id]

set_option maxHeartbeats 650000 in
set_option backward.isDefEq.respectTransparency false in
private def polynomialCoordinatesIso {I : Type u} {b : ModObj T.X Y}
    {y : 𝟙_ (SchemeOver k) ⟶ Y} {ν : I → Character T}
    (p : PolynomialCoordinates b y ν) (m : ℕ) (e : Fin m ≃ I) :
    affineScheme (polynomialAlgebra k m) ≅ Y := by
  let := p.affine
  let : Algebra k Γ(Y.left, ⊤) := (Specs.FlagLocalizationGeometry.groundRingHom Y).toAlgebra
  let C := (MvPolynomial.renameEquiv k e).trans p.coordinates
  let φ : CommRingCat.of (MvPolynomial (Fin m) k) ⟶ Γ(Y.left, ⊤) :=
    C.toRingEquiv.toCommRingCatIso.hom
  let j := Y.left.isoSpec.hom ≫ Spec.map φ
  have hw : j ≫ (affineScheme (polynomialAlgebra k m)).hom = Y.hom := by
    let baseMap : CommRingCat.of k ⟶ CommRingCat.of (MvPolynomial (Fin m) k) :=
      CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin m) k))
    have hφ : baseMap ≫ φ = (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ Y.hom.appTop := by
      apply CommRingCat.hom_ext
      exact RingHom.ext C.commutes
    change (Y.left.isoSpec.hom ≫ Spec.map φ) ≫ Spec.map baseMap = _
    rw [Category.assoc, ← Spec.map_comp, hφ, Spec.map_comp, Scheme.isoSpec_hom,
      ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  let f : Y ⟶ affineScheme (polynomialAlgebra k m) := Over.homMk j hw
  letI : IsIso ((Over.forget (Spec (CommRingCat.of k))).map f) :=
    inferInstanceAs (IsIso (Y.left.isoSpec.hom ≫ Spec.map φ))
  letI : IsIso f := isIso_of_reflects_iso f (Over.forget _)
  exact (asIso f).symm

set_option maxHeartbeats 650000 in
set_option backward.isDefEq.respectTransparency false in
private theorem polynomialCoordinatesIso_appTop {I : Type u} {b : ModObj T.X Y}
    {y : 𝟙_ (SchemeOver k) ⟶ Y} {ν : I → Character T}
    (p : PolynomialCoordinates b y ν) (m : ℕ) (e : Fin m ≃ I) (i : Fin m) :
    (polynomialCoordinatesIso p m e).hom.left.appTop (p.coordinates (MvPolynomial.X (e i))) =
      (Scheme.ΓSpecIso (affineRing (polynomialAlgebra k m))).inv (MvPolynomial.X i) := by
  let := p.affine
  let : Algebra k Γ(Y.left, ⊤) := (Specs.FlagLocalizationGeometry.groundRingHom Y).toAlgebra
  let C := (MvPolynomial.renameEquiv k e).trans p.coordinates
  let φ : CommRingCat.of (MvPolynomial (Fin m) k) ⟶ Γ(Y.left, ⊤) :=
    C.toRingEquiv.toCommRingCatIso.hom
  have hC : φ (MvPolynomial.X i) = p.coordinates (MvPolynomial.X (e i)) := by
    change p.coordinates (MvPolynomial.rename e (MvPolynomial.X i)) = _
    rw [MvPolynomial.rename_X]
  let d := polynomialCoordinatesIso p m e
  let R := CommRingCat.of (MvPolynomial (Fin m) k)
  have h : (Scheme.ΓSpecIso R).inv ≫ d.inv.left.appTop = φ := by
    change (Scheme.ΓSpecIso R).inv ≫ (Y.left.isoSpec.hom ≫ Spec.map φ).appTop = φ
    rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality,
      Category.assoc, Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop, Iso.inv_hom_id, Category.comp_id]
  have hi := congrArg (fun g : R ⟶ Γ(Y.left, ⊤) => g (MvPolynomial.X i)) h
  change d.inv.left.appTop ((Scheme.ΓSpecIso R).inv (MvPolynomial.X i)) = φ (MvPolynomial.X i) at hi
  change d.hom.left.appTop _ = _
  rw [← hC, ← hi]
  have hh := congrArg (fun f : affineScheme (polynomialAlgebra k m) ⟶ _ =>
    f.left.appTop) d.hom_inv_id
  rw [Over.comp_left, Scheme.Hom.comp_appTop, Over.id_left, Scheme.Hom.id_appTop] at hh
  exact congrArg (fun g : Γ((affineScheme (polynomialAlgebra k m)).left, ⊤) ⟶ _ =>
    g ((Scheme.ΓSpecIso R).inv (MvPolynomial.X i))) hh

set_option maxHeartbeats 650000 in
set_option backward.isDefEq.respectTransparency false in
private theorem polynomialCoordinatesIso_origin {I : Type u} {b : ModObj T.X Y}
    {y : 𝟙_ (SchemeOver k) ⟶ Y} {ν : I → Character T}
    (p : PolynomialCoordinates b y ν) (m : ℕ) (e : Fin m ≃ I) :
    origin k m ≫ (polynomialCoordinatesIso p m e).hom = toUnit _ ≫ y := by
  let d := polynomialCoordinatesIso p m e
  let R := polynomialAlgebra k m
  let A := CommAlgCat.of k k
  let q : affineScheme A ⟶ affineScheme R := (toUnit (pointScheme k) ≫ y) ≫ d.inv
  let ff := algSpec.fullyFaithful (R := CommRingCat.of k)
  let v : R ⟶ A := (ff.preimage q).unop
  have hq : (testSpec k).map v.op = q := ff.map_preimage q
  have hcomp : (testSpec k).map v.op ≫ d.hom = toUnit (pointScheme k) ≫ y := by
    rw [hq, show q = _ from rfl, Category.assoc, d.inv_hom_id, Category.comp_id]
  have hv (i : Fin m) : v.hom (MvPolynomial.X i) = 0 := by
    let z := (testSpec k).map v.op
    let f := p.coordinates (MvPolynomial.X (e i))
    have hz : (z ≫ d.hom).left.appTop f = 0 := by
      rw [hcomp, Over.comp_left, Scheme.Hom.comp_appTop]
      change (toUnit (pointScheme k)).left.appTop (y.left.appTop f) = 0
      rw [p.vanishes (e i), map_zero]
    rw [Over.comp_left, Scheme.Hom.comp_appTop] at hz
    change z.left.appTop ((polynomialCoordinatesIso p m e).hom.left.appTop f) = 0 at hz
    rw [polynomialCoordinatesIso_appTop] at hz
    let ψ := CommRingCat.ofHom v.hom.toRingHom
    have hn := Scheme.ΓSpecIso_inv_naturality ψ
    have h := congrArg (fun g : affineRing R ⟶ Γ((affineScheme A).left, ⊤) =>
      g (MvPolynomial.X i)) hn
    change (Scheme.ΓSpecIso (affineRing A)).inv (v.hom (MvPolynomial.X i)) =
      z.left.appTop ((Scheme.ΓSpecIso (affineRing R)).inv (MvPolynomial.X i)) at h
    apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (affineRing A)).inv).1
    rw [h, hz, map_zero]
  have hv0 : v = CommAlgCat.ofHom (MvPolynomial.aeval (0 : Fin m → k)) := by
    apply CommAlgCat.hom_ext
    ext i
    change v.hom (MvPolynomial.X i) = MvPolynomial.aeval (0 : Fin m → k) (MvPolynomial.X i)
    rw [MvPolynomial.aeval_X]
    exact hv i
  rw [hv0] at hcomp
  exact hcomp

set_option maxHeartbeats 650000 in
set_option backward.isDefEq.respectTransparency false in
private theorem chart_of_fixed_point {I : Type u} [Fintype I] {a : ModObj T.X X}
    {x : 𝟙_ (SchemeOver k) ⟶ X} {ν : I → Character T}
    (hx : IsEquivariantMap a (pointAction T) x)
    (V : Specs.FlagLocalizationGeometry.FixedPointChart a x ν) :
    ∃ U : PolynomialChart a (Fintype.card I), U.point = toUnit _ ≫ x ∧
      U.weight = ν ∘ (Fintype.equivFin I).symm := by
  let m := Fintype.card I
  let e := (Fintype.equivFin I).symm
  let d := polynomialCoordinatesIso V.polynomial m e
  let f := d.hom
  let r := ((𝟙 T.X ⊗ₘ f) ≫ V.action.smul) ≫ d.inv
  have hr : r ≫ f = T.X ◁ f ≫ V.action.smul := by simp [r, f]
  let b := actionOfMono V.action f r hr
  have hf : IsEquivariantMap V.action b f := by
    exact hr.trans (by rw [id_tensorHom])
  have hinc : IsEquivariantMap a b (f ≫ V.inclusion) :=
    equivariant_comp V.equivariant hf
  have horigin : origin k m ≫ (f ≫ V.inclusion) = toUnit (pointScheme k) ≫ x := by
    rw [← Category.assoc, polynomialCoordinatesIso_origin, Category.assoc, V.over]
  have hfixed : IsEquivariantMap a (Specs.EquivariantAffineModules.pointAction T)
      (toUnit (pointScheme k) ≫ x) := by
    apply equivariant_comp hx
    exact Subsingleton.elim _ _
  let : IsOpenImmersion V.inclusion.left := V.openImmersion
  let : IsOpenImmersion (f ≫ V.inclusion).left := inferInstanceAs
    (IsOpenImmersion (f.left ≫ V.inclusion.left))
  let : Mono (f ≫ V.inclusion) := Over.mono_of_mono_left _
  have hfix : IsEquivariantMap b (Specs.EquivariantAffineModules.pointAction T) (origin k m) := by
    apply equivariant_of_comp_mono hinc
    exact horigin.symm ▸ hfixed
  refine ⟨⟨b, f ≫ V.inclusion, inferInstance, hinc, hfix, ν ∘ e, fun i => ?_⟩, horigin, rfl⟩
  have hw := functionWeight_pullback f hf (V.polynomial.coordinates (MvPolynomial.X (e i)))
    (ν (e i)) (V.polynomial.weight (e i))
  rw [polynomialCoordinatesIso_appTop] at hw
  exact hw

private theorem cotangent_weights_of_chart {I : Type u} {a : ModObj T.X X}
    {x : 𝟙_ (SchemeOver k) ⟶ X} {ν : I → Character T}
    (V : Specs.FlagLocalizationGeometry.FixedPointChart a x ν) : HasCotangentWeights (a := a) x ν := by
  obtain ⟨basis, hb⟩ := V.cotangent
  let W : FixedPointChart x := ⟨V.scheme, V.action, V.inclusion, V.point,
    V.polynomial.affine, V.openImmersion, V.equivariant, V.over⟩
  exact ⟨W, fun i => ⟨V.polynomial.coordinates (MvPolynomial.X i), V.polynomial.vanishes i⟩,
    basis, fun i => ⟨hb i, V.polynomial.weight i⟩⟩

end Charts

section ClosedImages

open EquivariantCoherentClosedImage
  (pushCoherent pullCoherent pushClasses pushClasses_classOf pushCoherent_isEquivariantPushforward
    pushCoherent_map directImageLinearization_unit directImageLinearization_counit)
open EquivariantCoherentRestriction (classOf_eq_of_linearizedIso)
open private adjointOfEquivariantPushforward composedPushforwardAdjoint
  linearizedMap_comp pullComp_linearized pullback_map_linearized
  pullbackComparison_linearized linearizedIso_inv
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagDerivedRestriction
open private transport_naturality from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.EquivariantCoherentClosedImage
open private equivariant_actOn from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.EquivariantAffineModules
open private equivariant_comp from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagLocalizationGeometry

variable {T : GroupScheme k} {X Y Z : SchemeOver k}
  {a : ModObj T.X X} {b : ModObj T.X Y} {c : ModObj T.X Z}

set_option maxHeartbeats 650000 in
set_option backward.isDefEq.respectTransparency false in
private theorem equivariant_pushforward_of_adjoint
    {f : Y ⟶ X} (hf : IsEquivariantMap a b f)
    {H : EquivariantCoherent b} {F : EquivariantCoherent a}
    {e : F.sheaf ≅ (Scheme.Modules.pushforward f.left).obj H.sheaf}
    (h : IsLinearizedMap (pullbackLinearization hf F.lin) H.lin
      (((Scheme.Modules.pullbackPushforwardAdjunction f.left).homEquiv _ _).symm e.hom)) :
    IsEquivariantPushforward f H F e := by
  intro Z t y
  let ε := ((Scheme.Modules.pullbackPushforwardAdjunction f.left).homEquiv _ _).symm e.hom
  refine ⟨equivariant_actOn hf, ?_⟩
  dsimp only
  rw [← pullbackLinearization_transport_assoc hf F.lin.iso t y, Iso.hom_inv_id_assoc]
  exact transport_naturality _ _ ε h t y

set_option maxHeartbeats 650000 in
set_option backward.isDefEq.respectTransparency false in
private theorem classOf_eq_pushCoherent (hT : IsSplitTorus T)
    {f : Y ⟶ X} [IsLocallyNoetherian X.left] [IsClosedImmersion f.left]
    (hf : IsEquivariantMap a b f) {H : EquivariantCoherent b} {F : EquivariantCoherent a}
    (e : F.sheaf ≅ (Scheme.Modules.pushforward f.left).obj H.sheaf)
    (he : IsEquivariantPushforward f H F e) :
    classOf F = classOf (pushCoherent hf H) := by
  let A := Scheme.Modules.pullbackPushforwardAdjunction f.left
  let P := pullCoherent hf F
  let ε : Pull f F.sheaf ⟶ H.sheaf := (A.homEquiv _ _).symm e.hom
  have hε : IsLinearizedMap P.lin H.lin ε := adjointOfEquivariantPushforward hf he
  let : (Pull f F.sheaf).IsQuasicoherent := P.coherent.exists_quasicoherentData.choose.isQuasicoherent
  let Q := Scheme.Modules.pushforward f.left
  have hη : IsLinearizedMap F.lin (pushCoherent hf P).lin (A.unit.app F.sheaf) :=
    directImageLinearization_unit hf F.lin
  have hmap : IsLinearizedMap (pushCoherent hf P).lin (pushCoherent hf H).lin
      (Q.map ε) := pushCoherent_map hf (H := P) (K := H) hε
  have heq : A.unit.app F.sheaf ≫ Q.map ε = e.hom := by
    exact (A.homEquiv_unit F.sheaf H.sheaf ε).symm.trans
      ((A.homEquiv F.sheaf H.sheaf).apply_symm_apply e.hom)
  have hlin := linearizedMap_comp hη hmap
  rw [heq] at hlin
  exact (classOf_eq_of_linearizedIso hT
    (H := pushCoherent hf H) e hlin).symm

set_option maxHeartbeats 850000 in
set_option backward.isDefEq.respectTransparency false in
private theorem pushCoherent_comp_equivariant {f : Y ⟶ X} {g : Z ⟶ Y}
    [IsLocallyNoetherian X.left] [IsLocallyNoetherian Y.left]
    [IsClosedImmersion f.left] [IsClosedImmersion g.left]
    (hf : IsEquivariantMap a b f) (hg : IsEquivariantMap b c g)
    (H : EquivariantCoherent c) :
    IsEquivariantPushforward (g ≫ f) H (pushCoherent hf (pushCoherent hg H))
      ((Scheme.Modules.pushforwardComp g.left f.left).app H.sheaf) := by
  let af := Scheme.Modules.pullbackPushforwardAdjunction f.left
  let ag := Scheme.Modules.pullbackPushforwardAdjunction g.left
  let ac := Scheme.Modules.pullbackPushforwardAdjunction (g ≫ f).left
  let K := pushCoherent hg H
  let F := pushCoherent hf K
  let e := (Scheme.Modules.pushforwardComp g.left f.left).app H.sheaf
  let α : Pull f F.sheaf ⟶ K.sheaf := af.counit.app K.sheaf
  let β : Pull g K.sheaf ⟶ H.sheaf := ag.counit.app H.sheaf
  have ha : IsLinearizedMap (pullbackLinearization hf F.lin) K.lin α := by
    let : K.sheaf.IsFinitePresentation := K.coherent
    exact directImageLinearization_counit hf K.lin
  have hb : IsLinearizedMap (pullbackLinearization hg K.lin) H.lin β := by
    let : H.sheaf.IsFinitePresentation := H.coherent
    exact directImageLinearization_counit hg H.lin
  have hcoe : (pullComp F.sheaf g f).hom ≫ (ac.homEquiv _ _).symm e.hom =
      (Scheme.Modules.pullback g.left).map α ≫ β := by
    have h := composedPushforwardAdjoint f.left g.left e.hom
    change (ag.homEquiv _ _).symm ((af.homEquiv _ _).symm (e.hom ≫ e.inv)) = _ at h
    rw [e.hom_inv_id] at h
    change (ag.homEquiv _ _).symm
      ((af.homEquiv ((Scheme.Modules.pushforward f.left).obj K.sheaf) K.sheaf).symm
        (𝟙 ((Scheme.Modules.pushforward f.left).obj K.sheaf))) = _ at h
    rw [af.homEquiv_symm_id K.sheaf] at h
    change (ag.homEquiv _ _).symm α = _ at h
    rw [ag.homEquiv_counit] at h
    exact h.symm
  apply equivariant_pushforward_of_adjoint (equivariant_comp hf hg)
  have h := linearizedMap_comp (linearizedIso_inv (pullComp_linearized hf hg F.lin))
      (linearizedMap_comp (pullback_map_linearized hg ha) hb)
  rw [← hcoe, Iso.inv_hom_id_assoc] at h
  exact h

set_option maxHeartbeats 650000 in
private theorem pushClasses_comp (hT : IsSplitTorus T) {f : Y ⟶ X} {g : Z ⟶ Y}
    [IsLocallyNoetherian X.left] [IsLocallyNoetherian Y.left]
    [IsClosedImmersion f.left] [IsClosedImmersion g.left]
    (hf : IsEquivariantMap a b f) (hg : IsEquivariantMap b c g) :
    letI : IsClosedImmersion (g ≫ f).left :=
      inferInstanceAs (IsClosedImmersion (g.left ≫ f.left))
    pushClasses (equivariant_comp hf hg) = (pushClasses hf).comp (pushClasses hg) := by
  let : IsClosedImmersion (g ≫ f).left := inferInstanceAs (IsClosedImmersion (g.left ≫ f.left))
  have hgf : IsEquivariantMap a c (g ≫ f) := equivariant_comp hf hg
  apply classMap_ext
  intro H
  change pushClasses hgf (classOf H) = _
  calc
    _ = classOf (pushCoherent hgf H) := pushClasses_classOf hgf H
    _ = classOf (pushCoherent hf (pushCoherent hg H)) :=
      (classOf_eq_pushCoherent hT hgf _ (pushCoherent_comp_equivariant hf hg H)).symm
    _ = _ := by rw [LinearMap.comp_apply, pushClasses_classOf hg, pushClasses_classOf hf]

end ClosedImages

section PointClasses

open Specs.FlagCohomology (structureModule)
open EquivariantCoherentClosedImage
  (pushCoherent pushCoherent_isEquivariantPushforward pushClasses pushClasses_classOf
    directImageLinearization_counit)
open EquivariantCoherentRestriction (classOf_eq_of_linearizedIso)
open private pullbackComparison_linearized linearizedIso_inv linearizedMap_comp
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagDerivedRestriction
open private pullCongr_refl from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.EquivariantAffineModules
open private equivariant_comp equivariant_of_comp_mono restrictionGeometry_of_closed
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagLocalizationGeometry

variable {T : GroupScheme k} {X Y : SchemeOver k}
  {a : ModObj T.X X} {b : ModObj T.X Y}

private instance closedPoint (x : 𝟙_ (SchemeOver k) ⟶ X) : IsClosedImmersion x.left :=
  letI : Subsingleton (𝟙_ (SchemeOver k) : SchemeOver k).left :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of k)))
  isClosedImmersion_of_comp_eq_id X.hom x.left (Over.w x)

private def trivialStructureLine (T : GroupScheme k) (V : SchemeOver k)
    (hV : (structureModule V.left).IsFinitePresentation) :
    EquivariantCoherent (ModObj.trivialAction T.X V) :=
  ⟨structureModule V.left, hV, trivialLinearization T (structureModule V.left)⟩

private theorem terminalStructure_finitePresentation (k : Type u) [Field k] :
    (structureModule (𝟙_ (SchemeOver k) : SchemeOver k).left).IsFinitePresentation := by
  let R := CommRingCat.of k
  change (structureModule (Spec R)).IsFinitePresentation
  exact (SheafOfModules.isFinitePresentation (Spec R).ringCatSheaf).prop_of_iso
    (tildeSelf (R := R)) (finitePresentation_tilde (R := R) (ModuleCat.of R R))

private def terminalStructureLine (T : GroupScheme k) : EquivariantCoherent (pointAction T) :=
  trivialStructureLine T (𝟙_ (SchemeOver k)) (terminalStructure_finitePresentation k)

private theorem point_classes_are_multiples (hT : IsSplitTorus T)
    (m : GZero (pointAction T)) : ∃ r : CharacterRing T, m = r • classOf (terminalStructureLine T) := by
  have aux (V : SchemeOver k) (hV : Specs.FlagDerivedRestriction.pointScheme k = V)
      (h : (structureModule V.left).IsFinitePresentation)
      (m : GZero (ModObj.trivialAction T.X V)) :
      ∃ r : CharacterRing T, m = r • classOf (trivialStructureLine T V h) := by
    subst V
    obtain ⟨_, _, e, _, _, h1, _⟩ := pointCharacterComparison T hT
    have he : e (classOf (trivialStructureLine T _ h)) = 1 :=
      h1 _ tildeSelf rfl
    refine ⟨e m, e.injective ?_⟩
    rw [map_smul, he, smul_eq_mul, mul_one]
  exact aux _ (affinePoint_eq_terminal k) (terminalStructure_finitePresentation k) m

private def pointPush (hX : LocallyOfFiniteType X.hom) (x : 𝟙_ (SchemeOver k) ⟶ X)
    (hx : IsEquivariantMap a (pointAction T) x) :
    GZero (pointAction T) →ₗ[CharacterRing T] GZero a :=
  letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  pushClasses hx

set_option maxHeartbeats 650000 in
set_option backward.isDefEq.respectTransparency false in
private theorem restriction_after_clopen_push (hT : IsSplitTorus T)
    {j : Y ⟶ X} [IsLocallyNoetherian X.left] [IsClosedImmersion j.left] [IsOpenImmersion j.left]
    (hj : IsEquivariantMap a b j) (r : GZero a →ₗ[CharacterRing T] GZero b)
    (hr : ∀ F, ∃ (H : EquivariantCoherent b) (e : Pull j F.sheaf ≅ H.sheaf),
      IsEquivariantPullback j F H e ∧ r (classOf F) = classOf H) :
    r.comp (pushClasses hj) = LinearMap.id := by
  apply classMap_ext
  intro H
  let F := pushCoherent hj H
  obtain ⟨K, e, he, hk⟩ := hr F
  let A := Scheme.Modules.pullbackPushforwardAdjunction j.left
  let ε : Pull j F.sheaf ≅ H.sheaf := asIso (A.counit.app H.sheaf)
  let : H.sheaf.IsQuasicoherent := H.coherent.exists_quasicoherentData.choose.isQuasicoherent
  have hε : IsLinearizedMap (pullbackLinearization hj F.lin) H.lin ε.hom :=
    directImageLinearization_counit hj H.lin
  have he' := pullbackComparison_linearized hj he
  have hK : EquivariantHom (F := K) (H := H) (e.symm ≪≫ ε).hom :=
    linearizedMap_comp (linearizedIso_inv he') hε
  rw [LinearMap.comp_apply, pushClasses_classOf, LinearMap.id_apply]
  exact hk.trans (classOf_eq_of_linearizedIso hT _ hK).symm

private def liftToOpen {j : Y ⟶ X} [IsOpenImmersion j.left] {W : SchemeOver k}
    (f : W ⟶ X) (h : Set.range f.left ⊆ Set.range j.left) : W ⟶ Y :=
  Over.homMk (IsOpenImmersion.lift j.left f.left h) (by
    rw [← Over.w j, ← Category.assoc, IsOpenImmersion.lift_fac, Over.w f])

@[reassoc]
private theorem liftToOpen_comp {j : Y ⟶ X} [IsOpenImmersion j.left] {W : SchemeOver k}
    (f : W ⟶ X) (h : Set.range f.left ⊆ Set.range j.left) : liftToOpen f h ≫ j = f :=
  Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)

private theorem range_comp_over {Z : SchemeOver k} (f : Z ⟶ Y) (j : Y ⟶ X) :
    Set.range (f ≫ j).left = j.left '' Set.range f.left := by
  rw [Over.comp_left, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]

private theorem separating_first_point {n : ℕ}
    (p : Fin (n + 1) → (𝟙_ (SchemeOver k) ⟶ X))
    (hd : Pairwise (fun i j => Disjoint (Set.range (p i).left) (Set.range (p j).left)))
    (hcov : (⋃ i, Set.range (p i).left) = Set.univ) :
    (Set.range (p 0).left)ᶜ = ⋃ i : Fin n, Set.range (p i.succ).left := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov ▸ Set.mem_univ x)
    have h0 : i ≠ 0 := fun h => hx (h ▸ hi)
    exact Set.mem_iUnion.mpr ⟨i.pred h0, by rwa [Fin.succ_pred]⟩
  · intro hx hx0
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact Set.disjoint_left.mp (hd (Fin.succ_ne_zero i)) hi hx0

set_option maxHeartbeats 900000 in
set_option backward.isDefEq.respectTransparency false in
/-- The coherent classes on a finite disjoint union of fixed rational points
are generated by their trivial lines pushed forward from the components. -/
private theorem pointPush_span_top (hT : IsSplitTorus T) (n : ℕ)
    {X : SchemeOver k} (a : ModObj T.X X) (hX : RestrictionGeometry a)
    (p : Fin n → (𝟙_ (SchemeOver k) ⟶ X)) (hp : ∀ i, IsEquivariantMap a (pointAction T) (p i))
    (hd : Pairwise (fun i j => Disjoint (Set.range (p i).left) (Set.range (p j).left)))
    (hcov : (⋃ i, Set.range (p i).left) = Set.univ) :
    Submodule.span (CharacterRing T) (Set.range fun i =>
      pointPush hX.1 (p i) (hp i) (classOf (terminalStructureLine T))) = ⊤ := by
  classical
  induction n generalizing X with
  | zero =>
    let : IsEmpty X.left := ⟨fun x => by
      obtain ⟨i, _⟩ := Set.mem_iUnion.mp (hcov ▸ Set.mem_univ x)
      exact i.elim0⟩
    let : Subsingleton (GZero a) := classes_subsingleton_of_empty a
    exact Subsingleton.elim _ _
  | succ n ih =>
    let N := Submodule.span (CharacterRing T) (Set.range fun i =>
      pointPush hX.1 (p i) (hp i) (classOf (terminalStructureLine T)))
    let := hX.1
    let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
    let U : X.left.Opens := ⟨(Set.range (p 0).left)ᶜ,
      (p 0).left.isClosedEmbedding.isClosed_range.isOpen_compl⟩
    have hU : a.smul.left ⁻¹ᵁ U = (snd T.X X).left ⁻¹ᵁ U := by
      apply Opens.ext
      change a.smul.left ⁻¹' (Set.range (p 0).left)ᶜ =
        (snd T.X X).left ⁻¹' (Set.range (p 0).left)ᶜ
      rw [Set.preimage_compl, Set.preimage_compl,
        FlagLocalizationGeometry.action_preimage_range_of_equivariant _ (hp 0)]
    let Y := openSubscheme X U
    let j := openEmbedding X U
    let : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion U.ι)
    let : Mono j := Over.mono_of_mono_left j
    let b := invariantOpenAction a U hU
    have hj : IsEquivariantMap a b j := invariantOpenInclusion_equivariant a U hU
    have hr : Set.range j.left = (Set.range (p 0).left)ᶜ := Scheme.Opens.range_ι U
    have hru : Set.range j.left = ⋃ i : Fin n, Set.range (p i.succ).left :=
      hr.trans (separating_first_point p hd hcov)
    let : IsClosedImmersion j.left := IsClosedImmersion.of_isPreimmersion _ (by
      rw [hru]
      exact isClosed_iUnion_of_finite fun i => (p i.succ).left.isClosedEmbedding.isClosed_range)
    have hY := restrictionGeometry_of_closed j hj hX
    let := hY.1
    let : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
    let q (i : Fin n) : 𝟙_ (SchemeOver k) ⟶ Y := liftToOpen (p i.succ) (by
      rw [hru]
      exact Set.subset_iUnion (fun i : Fin n => Set.range (p i.succ).left) i)
    have hq (i : Fin n) : q i ≫ j = p i.succ := liftToOpen_comp _ _
    have he (i : Fin n) : IsEquivariantMap b (pointAction T) (q i) :=
      equivariant_of_comp_mono hj ((hq i).symm ▸ hp i.succ)
    have hqr (i : Fin n) : Set.range (q i).left = j.left ⁻¹' Set.range (p i.succ).left := by
      rw [← hq i, range_comp_over, j.left.isOpenEmbedding.injective.preimage_image]
    have hqd : Pairwise (fun i l : Fin n => Disjoint (Set.range (q i).left) (Set.range (q l).left)) := by
      intro i l hil
      rw [hqr, hqr]
      exact (hd (fun h => hil (Fin.succ_inj.mp h))).preimage _
    have hqcov : (⋃ i, Set.range (q i).left) = Set.univ := by
      simp only [hqr, ← Set.preimage_iUnion, ← hru, Set.preimage_range]
    have hN : ∀ v : GZero b, pushClasses hj v ∈ N := by
      intro v
      have hv : v ∈ Submodule.span (CharacterRing T) (Set.range fun i =>
          pointPush hY.1 (q i) (he i) (classOf (terminalStructureLine T))) :=
        (ih b hY q he hqd hqcov).symm ▸ Submodule.mem_top
      change v ∈ N.comap (pushClasses hj)
      refine (Submodule.span_le.mpr ?_) hv
      rintro _ ⟨i, rfl⟩
      have hcomp (y : 𝟙_ (SchemeOver k) ⟶ X) (hy : q i ≫ j = y)
          (h : IsEquivariantMap a (pointAction T) y) :
          (pushClasses hj).comp (pointPush hY.1 (q i) (he i)) = pointPush hX.1 y h := by
        subst y
        exact (pushClasses_comp hT hj (he i)).symm
      change ((pushClasses hj).comp (pointPush hY.1 (q i) (he i)))
        (classOf (terminalStructureLine T)) ∈ N
      rw [hcomp (p i.succ) (hq i) (hp i.succ)]
      exact Submodule.subset_span (Set.mem_range_self i.succ)
    obtain ⟨c, r, hex, _, hc, hres⟩ :=
      restrictionSequence a (pointAction T) b (p 0) j hT hX.1 hX.2.2.1 hX.2.1 hX.2.2.2
        inferInstance inferInstance (hp 0) hj hr
    have hc' : c = pointPush hX.1 (p 0) (hp 0) := by
      apply classMap_ext
      intro H
      obtain ⟨F, e, he, hF⟩ := hc H
      rw [hF, classOf_eq_pushCoherent hT (hp 0) e he]
      exact (pushClasses_classOf (hp 0) H).symm
    rw [eq_top_iff]
    intro v _
    have hres' : r.comp (pushClasses hj) = LinearMap.id :=
      restriction_after_clopen_push hT hj r hres
    have hk : r (v - pushClasses hj (r v)) = 0 := by
      rw [map_sub, ← LinearMap.comp_apply, hres', LinearMap.id_apply, sub_self]
    obtain ⟨z, hz⟩ := (hex _).mp hk
    obtain ⟨s, hs⟩ := point_classes_are_multiples hT z
    have hv : v - pushClasses hj (r v) ∈ N := by
      rw [← hz, hs, map_smul, hc']
      exact N.smul_mem s (Submodule.subset_span (Set.mem_range_self 0))
    exact (sub_add_cancel v _).symm ▸ N.add_mem hv (hN _)

end PointClasses

section FiberComparison

open Specs.FlagCohomology (cohomology cohomologyZero sectionsFunctor structureModule)
open Specs.FlagEquivariantEulerMap (IsFiberCharacter IsPointClass IsCohomologyCharacter)
open Specs.FlagDerivedRestriction (pointScheme)
open FlagEquivariantEulerMap (cohomologyPullbacks_nonempty cohomologyWeights_zero)
open private pullCongr_refl from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.EquivariantAffineModules
open private pullbackComparison_linearized linearizedMap_comp linearizedIso_inv
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagDerivedRestriction

variable {T : GroupScheme k} {X : SchemeOver k} {a : ModObj T.X X}

private def pointSectionsEquiv (F : (pointScheme k).left.Modules) :
    (sectionsFunctor (pointScheme k)).obj F ≃ₗ[k]
      (affineSections (CommAlgCat.of k k)).obj F where
  toFun s := s
  invFun s := s
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c s := by
    let R := CommRingCat.of k
    let u : R ⟶ R := CommRingCat.ofHom (algebraMap k k)
    let A := (pointScheme k).left.ringCatSheaf.obj.obj (op ⊤)
    let M : ModuleCat A := F.val.obj (op ⊤)
    let z : M := s
    let r : A := ((Scheme.ΓSpecIso R).inv ≫ (Spec.map u).appTop) c
    let t : A := (Scheme.ΓSpecIso R).inv (u c)
    have h : r = t := (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality u) c).symm
    exact congrArg (fun a : A => a • z) h

set_option backward.isDefEq.respectTransparency false in
private theorem cohomologyCharacter_of_point_weights
    (H : EquivariantCoherent (Specs.EquivariantAffineModules.pointAction T))
    (A : WeightGrading k (Character T) ((affineSections (CommAlgCat.of k k)).obj H.sheaf))
    (hA : ∀ χ s, s ∈ A.piece χ ↔ HasSectionWeight H.lin s χ)
    (c : CharacterRing T) (hc : ∀ χ, c.coeff χ = (Module.finrank k (A.piece χ) : ℤ)) :
    IsCohomologyCharacter H 0 c := by
  let B := pointScheme k
  let e := ((cohomologyZero B).app H.sheaf).toLinearEquiv.trans (pointSectionsEquiv H.sheaf)
  let : H.sheaf.IsQuasicoherent := H.coherent.exists_quasicoherentData.choose.isQuasicoherent
  let : Module.FinitePresentation k ((affineSections (CommAlgCat.of k k)).obj H.sheaf) :=
    (affineFinitePresentation (CommRingCat.of k) H.sheaf).mp H.coherent
  let : Module.Finite k ((affineSections (CommAlgCat.of k k)).obj H.sheaf) := inferInstance
  obtain ⟨m⟩ := cohomologyPullbacks_nonempty H 0
  refine ⟨Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective, m, fun χ => ?_⟩
  have hweights (v : (cohomology B 0).obj H.sheaf) :
      e v ∈ A.piece χ ↔ v ∈ Specs.FlagEquivariantEulerMap.cohomologyWeightSpace m χ := by
    rw [hA]
    exact (cohomologyWeights_zero m χ v).symm
  have hs : (Specs.FlagEquivariantEulerMap.cohomologyWeightSpace m χ).map e.toLinearMap =
      A.piece χ := by
    ext y
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact (hweights v).2 hv
    · intro hy
      exact ⟨e.symm y, (hweights _).1 (by rwa [e.apply_symm_apply]), e.apply_symm_apply y⟩
  rw [hc, (e.ofSubmodules _ _ hs).finrank_eq]

private theorem fiberAtTerminal {x : 𝟙_ (SchemeOver k) ⟶ X}
    (F : EquivariantCoherent a) {d : CharacterRing T}
    (h : Specs.FlagDerivedRestriction.IsFiberCharacter (toUnit (pointScheme k) ≫ x) F d) :
    IsFiberCharacter x F d := by
  obtain ⟨H, e, A, hE, hA, hχ⟩ := h
  have hc := cohomologyCharacter_of_point_weights H A hA d hχ
  have fromPoint (B : SchemeOver k) (hB : B = 𝟙_ (SchemeOver k))
      (H : EquivariantCoherent (ModObj.trivialAction T.X B))
      (y : B ⟶ X) (hy : y = toUnit B ≫ x)
      (e : Pull y F.sheaf ≅ H.sheaf)
      (he : IsEquivariantPullback y F H e)
      (hc : IsCohomologyCharacter H 0 d) : IsFiberCharacter x F d := by
    subst B
    have h1 : toUnit (𝟙_ (SchemeOver k)) = 𝟙 _ := Subsingleton.elim _ _
    have hxy : y = x := by simpa only [h1, Category.id_comp] using hy
    subst y
    exact ⟨H, e, he, hc⟩
  exact fromPoint _ (affinePoint_eq_terminal k) H _ rfl e hE hc

private theorem pointClassAtAffinePoint {x : 𝟙_ (SchemeOver k) ⟶ X}
    {F : EquivariantCoherent a} (h : IsPointClass x F) :
    Specs.FlagDerivedRestriction.IsPointClass (toUnit (pointScheme k) ≫ x) F := by
  have transfer (B : SchemeOver k) (hB : B = 𝟙_ (SchemeOver k)) :
      ∃ (L : EquivariantCoherent (ModObj.trivialAction T.X B))
        (_ : structureModule B.left ≅ L.sheaf)
        (e : F.sheaf ≅ (Scheme.Modules.pushforward (toUnit B ≫ x).left).obj L.sheaf),
        L.lin.iso.hom = 𝟙 _ ∧ IsEquivariantPushforward (toUnit B ≫ x) L F e := by
    subst B
    obtain ⟨H, i, e, hH, he⟩ := h
    have h1 : toUnit (𝟙_ (SchemeOver k)) = 𝟙 _ := Subsingleton.elim _ _
    have hy : toUnit (𝟙_ (SchemeOver k)) ≫ x = x := by rw [h1, Category.id_comp]
    exact hy.symm ▸ ⟨H, i.symm, e, hH.trans (pullCongr_refl H.sheaf (snd T.X _)), he⟩
  obtain ⟨L, i, e, hL, he⟩ := transfer _ (affinePoint_eq_terminal k)
  exact ⟨L, tildeSelf ≪≫ i, e, hL, he⟩

set_option backward.isDefEq.respectTransparency false in
private theorem terminalFiber_unique {x : 𝟙_ (SchemeOver k) ⟶ X}
    (hx : IsEquivariantMap a (pointAction T) x) {F : EquivariantCoherent a}
    {c d : CharacterRing T} (hc : IsFiberCharacter x F c) (hd : IsFiberCharacter x F d) : c = d := by
  obtain ⟨H, e, he, h⟩ := hc
  obtain ⟨J, f, hf, h'⟩ := hd
  obtain ⟨_, m, hm⟩ := h
  obtain ⟨_, n, hn⟩ := h'
  let i := e.symm ≪≫ f
  have hi : IsLinearizedMap H.lin J.lin i.hom :=
    linearizedMap_comp (linearizedIso_inv (pullbackComparison_linearized hx he))
      (pullbackComparison_linearized hx hf)
  let B := (𝟙_ (SchemeOver k) : SchemeOver k)
  let j := (cohomology B 0).mapIso i
  let C := cohomologyZero B
  have hnat (v : (cohomology B 0).obj H.sheaf) :
      C.hom.app J.sheaf (j.hom v) = i.hom.app ⊤ (C.hom.app H.sheaf v) :=
    ConcreteCategory.congr_hom (C.hom.naturality i.hom) v
  have hmem (χ : Character T) (v : (cohomology B 0).obj H.sheaf) :
      j.hom v ∈ Specs.FlagEquivariantEulerMap.cohomologyWeightSpace n χ ↔
        v ∈ Specs.FlagEquivariantEulerMap.cohomologyWeightSpace m χ := by
    rw [cohomologyWeights_zero, cohomologyWeights_zero, hnat]
    refine ⟨fun h => ?_, linearizedMap_preserves_sectionWeight hi⟩
    have hh := linearizedMap_preserves_sectionWeight (linearizedIso_inv hi) h
    change HasSectionWeight H.lin ((i.hom ≫ i.inv).app ⊤ (C.hom.app H.sheaf v)) χ at hh
    rw [i.hom_inv_id] at hh
    exact hh
  ext χ
  rw [hm, hn]
  have hs : (Specs.FlagEquivariantEulerMap.cohomologyWeightSpace m χ).map
      j.toLinearEquiv.toLinearMap = Specs.FlagEquivariantEulerMap.cohomologyWeightSpace n χ := by
    ext y
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact (hmem χ v).2 hv
    · intro hy
      refine ⟨j.toLinearEquiv.symm y, (hmem χ _).1 ?_, j.toLinearEquiv.apply_symm_apply y⟩
      exact (j.toLinearEquiv.apply_symm_apply y).symm ▸ hy
  exact congrArg (fun m : ℕ => (m : ℤ)) (j.toLinearEquiv.ofSubmodules _ _ hs).finrank_eq

end FiberComparison

section Spanning

open Specs.FlagLocalizationGeometry (InvariantClosed InvariantComplement)
open EquivariantCoherentClosedImage
  (pushClasses pushCoherent pushClasses_classOf pushCoherent_isEquivariantPushforward)
open private equivariant_of_comp_mono equivariant_comp from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagLocalizationGeometry

variable {T : GroupScheme k} {X Y : SchemeOver k}

private theorem point_coproduct_ranges {W : Type u} (e : (∐ fun _ : W ↦ 𝟙_ (SchemeOver k)) ≅ X) :
    let p := fun w => Sigma.ι _ w ≫ e.hom
    Pairwise (fun v w => Disjoint (Set.range (p v).left) (Set.range (p w).left)) ∧
      (⋃ w, Set.range (p w).left) = Set.univ := by
  intro p
  let pt : SchemeOver k := 𝟙_ _
  let L := Over.forget (Spec (CommRingCat.of k))
  let d : (∐ fun _ : W => pt.left) ≅ X.left :=
    (PreservesCoproduct.iso L (fun _ : W => pt)).symm ≪≫ L.mapIso e
  have hp (w : W) : (p w).left = Sigma.ι (fun _ : W => pt.left) w ≫ d.hom := by
    change L.map (Sigma.ι _ w ≫ e.hom) = _
    rw [Functor.map_comp, Iso.trans_hom, ← Category.assoc]
    congr 1
    exact (ι_comp_sigmaComparison L (fun _ : W => pt) w).symm
  have hr (w : W) : Set.range (p w).left =
      d.hom '' Set.range (Sigma.ι (fun _ : W => pt.left) w) := by
    rw [hp, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  constructor
  · intro v w h
    rw [hr, hr]
    have hd := disjoint_opensRange_sigmaι (fun _ : W => pt.left) v w h
    have hd' : Disjoint (Set.range (Sigma.ι (fun _ : W => pt.left) v))
        (Set.range (Sigma.ι (fun _ : W => pt.left) w)) := Opens.coe_disjoint.mpr hd
    apply Set.disjoint_left.mpr
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    exact Set.disjoint_left.mp hd' hx (d.hom.isOpenEmbedding.injective hxy ▸ hy)
  · rw [Set.iUnion_congr hr, ← Set.image_iUnion]
    change d.hom '' (⋃ w, Set.range ((sigmaOpenCover (fun _ : W => pt.left)).f w)) = _
    rw [(sigmaOpenCover (fun _ : W => pt.left)).iUnion_range, Set.image_univ,
      d.hom.surjective.range_eq]

private theorem isEmpty_pullback_of_disjoint_ranges {U V : SchemeOver k}
    (f : U ⟶ X) (g : V ⟶ X)
    (hd : Disjoint (Set.range f.left) (Set.range g.left)) :
    IsEmpty (pullback f g).left := by
  let p := pullback.fst f g
  let q := pullback.snd f g
  refine ⟨fun z => ?_⟩
  have e := congrArg (fun h : pullback f g ⟶ X => h.left z) (pullback.condition (f := f) (g := g))
  change f.left (p.left z) = g.left (q.left z) at e
  exact Set.disjoint_left.mp hd (Set.mem_range_self (p.left z)) ⟨q.left z, e.symm⟩

private theorem span_localized_push {G : AffineAlgebraicGroup k} {S : ClosedSubgroup G.val}
    {a : ModObj S.group.X X} {b : ModObj S.group.X Y} {W : Type u}
    (push : GZero b →ₗ[CharacterRing S.group] GZero a)
    (hpush : Function.Surjective (LocalizedModule.map (rootFactors S) push))
    (v : W → GZero b) (hspan : Submodule.span (CharacterRing S.group) (Set.range v) = ⊤)
    (F : W → EquivariantCoherent a) (hF : ∀ w, push (v w) = classOf (F w)) :
    Submodule.span (LocalCharacterRing S) (Set.range fun w => localClass (F w)) = ⊤ := by
  let N := Submodule.span (LocalCharacterRing S) (Set.range fun w => localClass (F w))
  let p := (LocalizedModule.mkLinearMap (rootFactors S) (GZero a)).comp push
  let : SMul (LocalCharacterRing S) (LocalGZero S a) :=
    LocalizedModule.smulOfIsLocalization (LocalCharacterRing S)
  let : IsScalarTower (CharacterRing S.group) (LocalCharacterRing S) (LocalGZero S a) :=
    LocalizedModule.instIsScalarTower (S := rootFactors S) (M := GZero a) (LocalCharacterRing S)
  have hmem (z : GZero b) : p z ∈ N := by
    have hz : z ∈ Submodule.span (CharacterRing S.group) (Set.range v) :=
      hspan.symm ▸ Submodule.mem_top
    change z ∈ (N.restrictScalars (CharacterRing S.group)).comap p
    refine (Submodule.span_le.mpr ?_) hz
    rintro _ ⟨w, rfl⟩
    change LocalizedModule.mkLinearMap (rootFactors S) _ (push (v w)) ∈ N
    rw [hF]
    exact Submodule.subset_span (Set.mem_range_self w)
  rw [eq_top_iff]
  intro m _
  obtain ⟨z, rfl⟩ := hpush m
  induction z using LocalizedModule.induction_on with
  | _ z s =>
    rw [LocalizedModule.map_mk]
    have h : (IsLocalization.mk' (LocalCharacterRing S) 1 s •
        (p z : LocalGZero S a) : LocalGZero S a) = LocalizedModule.mk (push z) s := by
      exact (LocalizedModule.mk'_smul_mk (LocalCharacterRing S) 1 (push z) s 1).trans
        (by rw [one_smul, mul_one])
    exact h ▸ N.smul_mem _ (hmem z)

end Spanning

section FixedPointBasis

open Specs.FlagLocalizationGeometry (InvariantClosed InvariantComplement)
open Specs.FlagEquivariantEulerMap (IsPointClass)
open EquivariantCoherentClosedImage
  (pushCoherent pushCoherent_isEquivariantPushforward pushClasses_classOf)
open private equivariant_of_comp_mono fixedOver_section_of_fields from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagLocalizationGeometry

variable {G : AffineAlgebraicGroup k} {S : ClosedSubgroup G.val} {X : SchemeOver k}
  {a : ModObj S.group.X X}
  {W : Type u} {x : W → (𝟙_ (SchemeOver k) ⟶ X)}

private theorem fixedUnion_ranges (Z : InvariantClosed a)
    (e : (∐ fun _ : W ↦ 𝟙_ (SchemeOver k)) ≅ Z.scheme)
    (he : ∀ w, Sigma.ι _ w ≫ e.hom ≫ Z.inclusion = x w) :
    Pairwise (fun v w => Disjoint (Set.range (x v).left) (Set.range (x w).left)) ∧
      (⋃ w, Set.range (x w).left) = Set.range Z.inclusion.left := by
  let p (w : W) := Sigma.ι _ w ≫ e.hom
  obtain ⟨hd, hc⟩ := point_coproduct_ranges e
  have hr (w : W) : Set.range (x w).left = Z.inclusion.left '' Set.range (p w).left := by
    rw [← he w, ← Category.assoc, range_comp_over]
  let : IsClosedImmersion Z.inclusion.left := Z.closedImmersion
  refine ⟨fun v w h => ?_, ?_⟩
  · change Disjoint (Set.range (x v).left) (Set.range (x w).left)
    rw [hr, hr]
    exact Set.disjoint_image_of_injective Z.inclusion.left.isClosedEmbedding.injective (hd h)
  · rw [Set.iUnion_congr hr, ← Set.image_iUnion, show _ = Set.univ from hc, Set.image_univ]

private theorem fixedSections_equivariant {a : ModObj G.val.X X}
    (hd : Pairwise (fun v w => Disjoint (Set.range (x v).left) (Set.range (x w).left)))
    (hfixed : ∀ y : Over.mk (fieldSpecMap k k) ⟶ X,
      Specs.BruhatOrbitParametrization.FixedOver (T := S) a y ↔ ∃! w, y = toUnit _ ≫ x w)
    (w : W) : IsEquivariantMap (torusAction S a) (pointAction S.group) (x w) := by
  apply (FlagLocalizationGeometry.fixedOver_iff_equivariant_section S a (x w)).mp
  apply fixedOver_section_of_fields S a
  apply (hfixed _).mpr
  refine ⟨w, rfl, fun v hv => ?_⟩
  by_contra hvw
  let B := Over.mk (fieldSpecMap k k)
  let b : B.left := IsLocalRing.closedPoint k
  have hm (i : W) : (toUnit B ≫ x i).left b ∈ Set.range (x i).left :=
    ⟨(toUnit B).left b, rfl⟩
  exact Set.disjoint_left.mp (hd hvw) (hv ▸ hm v) (hm w)

set_option maxHeartbeats 850000 in
set_option backward.isDefEq.respectTransparency false in
private theorem fixedPointClasses_span [Fintype W] (hS : IsSplitTorus S.group)
    (hX : RestrictionGeometry a) (Z : InvariantClosed a) (V : InvariantComplement a Z)
    (hZ : RestrictionGeometry Z.action) (hV : Subsingleton (LocalGZero S V.action))
    (e : (∐ fun _ : W ↦ 𝟙_ (SchemeOver k)) ≅ Z.scheme)
    (he : ∀ w, Sigma.ι _ w ≫ e.hom ≫ Z.inclusion = x w)
    (hx : ∀ w, IsEquivariantMap a (pointAction S.group) (x w)) :
    ∃ F : W → EquivariantCoherent a,
      (∀ w, IsPointClass (x w) (F w)) ∧
      Submodule.span (LocalCharacterRing S) (Set.range fun w => localClass (F w)) = ⊤ := by
  let := hX.1
  let := hZ.1
  let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  let : IsLocallyNoetherian Z.scheme.left := LocallyOfFiniteType.isLocallyNoetherian Z.scheme.hom
  let : IsClosedImmersion Z.inclusion.left := Z.closedImmersion
  let : Mono Z.inclusion := Over.mono_of_mono_left _
  have hI : IsEquivariantMap a Z.action Z.inclusion := Z.equivariant
  let p (w : W) := Sigma.ι _ w ≫ e.hom
  have hp (w : W) : IsEquivariantMap Z.action (pointAction S.group) (p w) :=
    equivariant_of_comp_mono Z.equivariant
      (show IsEquivariantMap a (pointAction S.group) (p w ≫ Z.inclusion) from
        (he w).symm ▸ hx w)
  let L := terminalStructureLine S.group
  let v (w : W) := pointPush hZ.1 (p w) (hp w) (classOf L)
  obtain ⟨hd, hc⟩ := point_coproduct_ranges e
  let d := (Fintype.equivFin W).symm
  have hspan : Submodule.span (CharacterRing S.group) (Set.range v) = ⊤ := by
    have hcov : (⋃ i, Set.range (p (d i)).left) = Set.univ :=
      (d.surjective.iUnion_comp (fun w => Set.range (p w).left)).trans hc
    have h := pointPush_span_top hS (Fintype.card W) Z.action hZ (p ∘ d)
      (fun i => hp (d i)) (fun _ _ hij => hd (d.injective.ne hij)) hcov
    change Submodule.span (CharacterRing S.group) (Set.range (v ∘ d)) = ⊤ at h
    simpa only [EquivLike.range_comp] using h
  obtain ⟨push, hsurj, hpush⟩ :=
    localizedPush_surjective_of_vanishing (restriction_of_geometry hS hX Z V) hV
  let F (w : W) := pushCoherent (hx w) L
  have hF (w : W) : IsPointClass (x w) (F w) :=
    ⟨L, Iso.refl _, Iso.refl _, rfl, pushCoherent_isEquivariantPushforward (hx w) L⟩
  refine ⟨F, hF, span_localized_push push hsurj v hspan F (fun w => ?_)⟩
  have hcomp : (EquivariantCoherentClosedImage.pushClasses hI).comp
      (pointPush hZ.1 (p w) (hp w)) = pointPush hX.1 (x w) (hx w) := by
    have eq (y : 𝟙_ (SchemeOver k) ⟶ X) (hy : p w ≫ Z.inclusion = y)
        (h : IsEquivariantMap a (pointAction S.group) y) :
        (EquivariantCoherentClosedImage.pushClasses hI).comp
          (pointPush hZ.1 (p w) (hp w)) = pointPush hX.1 y h := by
      subst y
      exact (pushClasses_comp hS hI (hp w)).symm
    exact eq _ (he w) (hx w)
  obtain ⟨H, i, hi, hH⟩ := hpush (pushCoherent (hp w) L)
  calc
    push (v w) = push (classOf (pushCoherent (hp w) L)) :=
      congrArg push (pushClasses_classOf (hp w) L)
    _ = classOf H := hH
    _ = classOf (pushCoherent hI (pushCoherent (hp w) L)) :=
      classOf_eq_pushCoherent hS hI i hi
    _ = ((EquivariantCoherentClosedImage.pushClasses hI).comp
        (pointPush hZ.1 (p w) (hp w))) (classOf L) := by
      change _ = EquivariantCoherentClosedImage.pushClasses hI
        (EquivariantCoherentClosedImage.pushClasses (hp w) (classOf L))
      rw [pushClasses_classOf (hp w), pushClasses_classOf hI]
    _ = pointPush hX.1 (x w) (hx w) (classOf L) :=
      congrArg (fun f : GZero (pointAction S.group) →ₗ[CharacterRing S.group] GZero a =>
        f (classOf L)) hcomp
    _ = classOf (F w) := pushClasses_classOf (hx w) L

end FixedPointBasis

section PointRestrictions

open Specs.FlagDerivedRestriction (PolynomialChart pointScheme)
open Specs.FlagEquivariantEulerMap (IsFiberCharacter IsPointClass)

variable {k : Type u} [Field k] {T : GroupScheme k} {X : SchemeOver k} {a : ModObj T.X X}
  {I : Type u} [Fintype I] {x : 𝟙_ (SchemeOver k) ⟶ X} {ν : I → Character T}

set_option maxHeartbeats 650000 in
set_option backward.isDefEq.respectTransparency false in
private theorem derivedRestriction_of_chart (hT : IsSplitTorus T)
    (hx : IsEquivariantMap a (pointAction T) x)
    (V : Specs.FlagLocalizationGeometry.FixedPointChart a x ν) :
    ∃ res : GZero a →ₗ[CharacterRing T] CharacterRing T,
      (∀ H, IsDerivedFiberCharacter x H (res (classOf H))) ∧
      (∀ H : EquivariantCoherent a, H.sheaf.IsLocallyFree →
        IsFiberCharacter x H (res (classOf H))) ∧
      (∀ H, IsPointClass x H → res (classOf H) = ∏ i, (1 - eChar (ν i))) ∧
      (∀ (y : 𝟙_ (SchemeOver k) ⟶ X) H, IsPointClass y H →
        Disjoint (Set.range x.left) (Set.range y.left) → res (classOf H) = 0) := by
  obtain ⟨U, hU, hν⟩ := chart_of_fixed_point hx V
  obtain ⟨res, hres, hfiber, hself, hdisj⟩ := FlagDerivedRestriction.derivedRestriction hT U
  refine ⟨res, ?_, ?_, ?_, ?_⟩
  · intro H
    obtain ⟨⟨K, hK⟩, hlift⟩ := hres H
    obtain ⟨hTor, hfree, hEuler⟩ := hlift K hK
    exact ⟨_, U, hU, K, hK, hTor, hfree, fun C => (hEuler C).exists⟩
  · intro H hH
    exact fiberAtTerminal H (hU ▸ hfiber H hH)
  · intro H hH
    rw [hself H (hU.symm ▸ pointClassAtAffinePoint hH),
      Specs.FlagDerivedRestriction.cotangentProduct, hν]
    exact Fintype.prod_equiv (Fintype.equivFin I).symm _ _ (fun _ => rfl)
  · intro y H hH hd
    apply hdisj (toUnit (pointScheme k) ≫ y) H (pointClassAtAffinePoint hH)
    apply isEmpty_pullback_of_disjoint_ranges
    rw [hU, range_comp_over, range_comp_over]
    exact hd.mono (Set.image_subset_range _ _) (Set.image_subset_range _ _)

end PointRestrictions

section FlagLine

open Specs.FlagCohomology
  (FlagKernelPair flagLineSheaf flagCohomology CohomologyIndex CohomologyBasis
    IsFlagCohomologyAction equivariantEulerCharacteristic structureModule)
open Specs.FlagEquivariantEulerMap (IsFiberCharacter IsEulerCharacter)
open private exists_associatedBundle freeSingletonIso freeIsoGenerators freeIsoGenerators_iso
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagCohomology

set_option maxHeartbeats 500000 in
set_option backward.isDefEq.respectTransparency false in
private theorem locallyFree_of_unit_restrictions {X : Scheme.{u}} (F : X.Modules)
    {I : Type u} (U : I → X.Opens) (hU : IsOpenCover U)
    (i : ∀ j, F.restrict (U j).ι ≅ structureModule (U j).toScheme) :
    F.IsLocallyFree := by
  let e (j : I) : SheafOfModules.free (R := X.ringCatSheaf.over (U j)) PUnit.{u + 1} ≅
      F.over (U j) :=
    freeSingletonIso (X.ringCatSheaf.over (U j)) ≪≫
      (Scheme.Modules.overEquiv (U j)).functor.preimageIso
        ((U j).sheafOfModulesEquivOverUnit X.ringCatSheaf ≪≫ (i j).symm ≪≫
          ((Scheme.Modules.overFunctorEquiv (U j)).app F).symm)
  let gen (j : I) : (F.over (U j)).GeneratingSections := freeIsoGenerators (e j)
  have hgen (j : I) : IsIso (gen j).π := freeIsoGenerators_iso (e j)
  let q : F.LocalGeneratorsData :=
    { I := I
      X := U
      coversTop := (Opens.coversTop_iff _ U).mpr hU
      generators := gen }
  let : q.IsLocallyFreeData :=
    SheafOfModules.LocalGeneratorsData.IsLocallyFreeData.mk (q := q) hgen
  exact q.isLocallyFree

variable {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
  {Q : Presentation P.negative} {a : ModObj G.val.X Q.scheme}
  (ha : μ[G.val.X] ≫ Q.projection = (𝟙 G.val.X ⊗ₘ Q.projection) ≫ a.smul)

include ha

set_option maxHeartbeats 650000 in
set_option backward.isDefEq.respectTransparency false in
private theorem flagLineSheaf_locallyFree (p : BorelProjection P)
    (χ : Character P.torus.group) (h : FlagKernelPair Q) :
    (flagLineSheaf Q p χ h).IsLocallyFree := by
  obtain ⟨L⟩ := exists_associatedBundle Q p χ a ha
  obtain ⟨_, hl, _⟩ := FlagCohomology.flagLineSheafIdentification Q p χ h L
  choose U hU i using hl
  have hcover : IsOpenCover U := by
    apply top_unique
    intro y _
    exact Opens.mem_iSup.mpr ⟨y, hU y⟩
  exact locallyFree_of_unit_restrictions (flagLineSheaf Q p χ h) U hcover (fun y => (i y).some)

set_option maxHeartbeats 650000 in
set_option backward.isDefEq.respectTransparency false in
private theorem flagLine_characters [IsCommMonObj P.torus.group.X] {D : Datum P.torus}
    (J : Identification D)
    (n : D.rootDatum.weylGroup → (𝟙_ (SchemeOver k) ⟶ J.normalizer.group.X))
    (hn : ∀ w, Specs.BruhatOrbitParametrization.IsRepresentative J w (n w))
    (p : BorelProjection P) (χ : Character P.torus.group) (h : FlagKernelPair Q)
    (ρ : ∀ i, Specs.RootWeightAction.Representation G.val (CohomologyIndex (p := p) (χ := χ) h i))
    (b : ∀ i, CohomologyBasis (p := p) (χ := χ) h i)
    (hb : ∀ i, IsFlagCohomologyAction h a i (b i) (ρ i))
    (N : ℕ) (hN : ∀ i ≥ N, IsZero (flagCohomology Q p χ h i)) :
    ∃ L : EquivariantCoherent (torusAction P.torus a),
      L.sheaf.IsLocallyFree ∧ IsEulerCharacter L (equivariantEulerCharacteristic h ρ N) ∧
      ∀ w, IsFiberCharacter (n w ≫ J.normalizer.inclusion.hom.hom ≫ Q.projection) L
        (eChar ((J.labelEquiv w).val χ)) := by
  obtain ⟨hL, ℓ, _, hchar, hfiber⟩ := FlagEquivariantEulerMap.flagLineBundleCharacters Q a p χ h ha
  let L : EquivariantCoherent (torusAction P.torus a) := ⟨flagLineSheaf Q p χ h, hL, ℓ⟩
  have hE : IsEulerCharacter L (equivariantEulerCharacteristic h ρ N) :=
    ⟨N, fun i => Specs.FormalCharacters.formalCharacter P.torus (ρ i),
      fun i => hchar i (b i) (ρ i) (hb i), hN, rfl⟩
  exact ⟨L, flagLineSheaf_locallyFree ha p χ h, hE, fun w => hfiber J w (n w) (hn w)⟩

end FlagLine

section Localization

set_option maxHeartbeats 1200000 in
set_option backward.isDefEq.respectTransparency false in
/-- The Weyl point classes form a basis after root localization. Restriction
and Euler characteristic give the fixed-point sum on the actual flag. -/
theorem flagLocalization : FlagLocalization.{u} := by
  classical
  intro k _ G P Q a ha
  obtain ⟨hT, D, J, hW, hR, hrep, hgeometry⟩ :=
    FlagLocalizationGeometry.flagLocalizationGeometry P Q a ha
  let := hT
  let := hW
  let := hR
  refine ⟨hT, D, J, hW, hR, hrep, ?_⟩
  intro n hn x t R M δ
  obtain ⟨hfix, hcharts, hX, Z, V, ⟨e, he⟩, hZ, hV, U, H, C, coord, ⟨filtration⟩⟩ :=
    hgeometry n hn
  have hsections (w : D.rootDatum.weylGroup) :
      Sigma.ι _ w ≫ e.hom ≫ Z.inclusion = x w :=
    (he w).trans (Category.assoc _ _ _)
  have hfixed (K : Type u) [Field K] [Algebra k K]
      (y : Over.mk (fieldSpecMap k K) ⟶ Q.scheme) :
      Specs.BruhatOrbitParametrization.FixedOver (T := P.torus) a y ↔
        ∃! w, y = toUnit _ ≫ x w := by
    simpa only [x, Category.assoc] using hfix K y
  have hchart (w : D.rootDatum.weylGroup) :
      Nonempty (Specs.FlagLocalizationGeometry.FixedPointChart t (x w) (cotangentWeight J w)) := by
    simpa only [x, Category.assoc] using hcharts w
  obtain ⟨hdisj, hclosed⟩ := fixedUnion_ranges (x := x) Z e hsections
  have hx (w : D.rootDatum.weylGroup) : IsEquivariantMap t (pointAction P.torus.group) (x w) :=
    fixedSections_equivariant hdisj (hfixed k) w
  have hvanish : Subsingleton (LocalGZero P.torus V.action) := by
    apply vanishing_of_complement_filtration P.split Z V hV filtration
    exact fun w _ _ j hj hr hb => vanishing_of_orderedCell D P.split (coord w) j hj hr hb
  refine ⟨hfixed, fun w => cotangent_weights_of_chart (hchart w).some,
    ⟨V.scheme, V.action, V.inclusion, V.openImmersion, V.equivariant, ?_, hvanish⟩, ?_⟩
  · rw [V.range_eq, hclosed]
  obtain ⟨F, hF, hspan⟩ := fixedPointClasses_span P.split hX Z V hZ hvanish e hsections hx
  choose r hr hfiber hself hother using
    fun w => derivedRestriction_of_chart P.split (hx w) (hchart w).some
  obtain ⟨E, hEuler, hEulerPoint⟩ := FlagEquivariantEulerMap.flagEulerMap P Q a ha
  let res (w : D.rootDatum.weylGroup) : M →ₗ[R] R := localizeCharacterMap (S := P.torus) (r w)
  let euler : M →ₗ[R] R := localizeCharacterMap (S := P.torus) E
  have hunit (w : D.rootDatum.weylGroup) : IsUnit (δ w) := cotangentProduct_isUnit J w
  have hdiag (w v : D.rootDatum.weylGroup) :
      res w (localClass (F v)) = if w = v then δ w else 0 := by
    change localizeCharacterMap (r w) (localClass (F v)) = _
    rw [localizeCharacterMap_class]
    split_ifs with h
    · subst v
      exact congrArg (localScalar P.torus) (hself w _ (hF w))
    · rw [hother w (x v) (F v) (hF v) (hdisj h), map_zero]
  obtain ⟨basis, hbasis⟩ := basis_of_diagonal_restrictions hspan hunit hdiag
  have heuler (w : D.rootDatum.weylGroup) : euler (basis w) = 1 := by
    change localizeCharacterMap E (basis w) = _
    rw [hbasis, localizeCharacterMap_class,
      hEulerPoint (x w) (F w) (closedPoint _) (hx w) (hF w), map_one]
  have hdiag' (w v : D.rootDatum.weylGroup) :
      res w (basis v) = if w = v then δ w else 0 := by
    rw [hbasis, hdiag]
  have hsum (z : M) : euler z = ∑ w, res w z * Ring.inverse (δ w) :=
    euler_of_diagonal_restrictions basis hunit hdiag' euler heuler z
  refine ⟨F, basis, res, euler, fun w => ⟨hF w, hbasis w, hunit w, heuler w⟩, hdiag',
    fun w H => ⟨r w (classOf H), hr w H, localizeCharacterMap_class (r w) H⟩,
    fun H => ⟨E (classOf H), hEuler H, localizeCharacterMap_class E H⟩, ?_, ?_⟩
  · intro H hH
    refine ⟨fun w => r w (classOf H), fun w => hfiber w H hH, (hsum (localClass H)).trans ?_⟩
    apply Finset.sum_congr rfl
    intro w _
    exact congrArg (fun c : R => c * Ring.inverse (δ w))
      (localizeCharacterMap_class (S := P.torus) (r w) H)
  · intro p χ h ρ b hb N hN
    obtain ⟨L, hfree, hchar, hfiberL⟩ := flagLine_characters ha J n hn p χ h ρ b hb N hN
    have hE := FlagEquivariantEulerMap.eulerCharacter_unique L (hEuler L) hchar
    have hrw (w : D.rootDatum.weylGroup) :
        r w (classOf L) = eChar ((J.labelEquiv w).val χ) :=
      terminalFiber_unique (hx w) (hfiber w L hfree) (hfiberL w)
    calc
      _ = euler (localClass L) :=
        ((localizeCharacterMap_class (S := P.torus) E L).trans
          (congrArg (localScalar P.torus) hE)).symm
      _ = ∑ w, res w (localClass L) * Ring.inverse (δ w) := hsum (localClass L)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro w _
        exact congrArg (fun c : R => c * Ring.inverse (δ w))
          ((localizeCharacterMap_class (S := P.torus) (r w) L).trans
            (congrArg (localScalar P.torus) (hrw w)))

end Localization

end

end LinearAlgebraicGroups.Representation.FlagFixedPoints
