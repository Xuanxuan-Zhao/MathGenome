import Specs.LinearAlgebraicGroups.Classification.PinnedUniqueness
import LinearAlgebraicGroups.Classification.Pinning
import LinearAlgebraicGroups.RootData.OrderedRootProducts
import LinearAlgebraicGroups.RootData.RankOneFlag
import LinearAlgebraicGroups.Reductive.CocharacterDynamics
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Classification.PinnedUniqueness

open _root_.LinearAlgebraicGroups.Specs
open Specs.PinnedUniqueness Specs.Pinning
open Specs.AbstractPairing (Datum Root)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterDescent (Character Cocharacter StandardLattice)
open Specs.CharacterPairing (pairing characterValue)
open Specs.DiagonalizableGroups (groupAlgebra groupAlgebraMap)
open Specs.GeometricBorelConjugacy (subgroupOfSubgroup)
open Specs.GeometricRadicals (IsSplitTorus)
open Specs.RankOneFlag (SameSubgroup)
open Specs.RootGroups (AdditiveLine HasScalarAction IsRootSubgroup rootPoint rankOneWord)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open CocharacterDynamics

open private splitPresentation characterValue_monomial algebraPoint isTorus_of_split
  from LinearAlgebraicGroups.RootData.CharacterPairing
open private rootPoint_comp rootPoint_natural
  hom_ext_on_affine_tests tangent_weight_of_scalarAction
  from LinearAlgebraicGroups.RootData.RootGroups
open private rootPoint_surjective
  from LinearAlgebraicGroups.RootData.OrderedRootProducts
open private comp_conjugateFamily
  from LinearAlgebraicGroups.Affine.Stabilizers
open private centralizes_hasLimit centralizes_onAlgebras polynomialConstants
  polynomialConstants_laurent polynomialConstants_zero affine_subgroup
  from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private map_hasLimit same_subgroup_trans from LinearAlgebraicGroups.RootData.RankOneFlag
open private affine_tensor from LinearAlgebraicGroups.Solvable.FiniteWordClosure

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
set_option linter.style.haveILetI false

variable {k : Type u} [Field k]

private abbrev underlying := Grp.forget (SchemeOver k)

/-- Equality can be tested against the monomial characters of a split torus. -/
theorem charactersSeparatePoints : CharactersSeparatePoints.{u} := by
  intro k _ T hT R t s h
  obtain ⟨r, ⟨e⟩⟩ := splitPresentation hT
  let M := StandardLattice.{u} r
  let C : TestAlgebra k := CommAlgCat.of k (MonoidAlgebra k M)
  let F := algSpec.fullyFaithful (R := CommRingCat.of k)
  let p : C ⟶ R := (F.preimage (t ≫ e.inv.hom.hom)).unop
  let q : C ⟶ R := (F.preimage (s ≫ e.inv.hom.hom)).unop
  have hp : algebraPoint R p.hom = t ≫ e.inv.hom.hom := F.map_preimage _
  have hq : algebraPoint R q.hom = s ≫ e.inv.hom.hom := F.map_preimage _
  have heq (m : M) : p.hom (MonoidAlgebra.single m 1) = q.hom (MonoidAlgebra.single m 1) := by
    let χ := specGroupMap (groupAlgebraMap k ((zpowersHom M m).comp MulEquiv.ulift.toMonoidHom))
    rw [← characterValue_monomial, ← characterValue_monomial, hp, hq]
    have hχ : (t ≫ e.inv.hom.hom) ≫ χ.hom.hom = (s ≫ e.inv.hom.hom) ≫ χ.hom.hom := by
      simpa only [Grp.comp_hom_hom, Category.assoc] using h (e.inv ≫ χ)
    change characterValue χ R (t ≫ e.inv.hom.hom) = characterValue χ R (s ≫ e.inv.hom.hom)
    unfold characterValue
    rw [hχ]
  have h₁ : p = q := by
    apply CommAlgCat.hom_ext
    exact MonoidAlgebra.algHom_ext heq (by ext)
  have hm : t ≫ e.inv.hom.hom = s ≫ e.inv.hom.hom := hp.symm.trans (h₁ ▸ hq)
  exact (cancel_mono ((underlying (k := k)).mapIso e).inv).mp hm

private abbrev scalarEval {R : TestAlgebra k} {G : GroupScheme k}
    (f : scalarGroupPoints R G ⟶ scalarGroupPoints R G) (S : Under R) :
    GroupPoints G S.right →* GroupPoints G S.right :=
  (f.app S).hom

private abbrev extendTest {R : TestAlgebra k} (S : Under R) {B : TestAlgebra k}
    (a : S.right ⟶ B) : Under R := Under.mk (S.hom ≫ a)

private theorem scalarEval_natural {R : TestAlgebra k} {G : GroupScheme k}
    (f : scalarGroupPoints R G ⟶ scalarGroupPoints R G) {S B : Under R}
    (a : S.right ⟶ B.right) (h : S.hom ≫ a = B.hom) (g : GroupPoints G S.right) :
    scalarEval f B (mapPoints a g) = mapPoints a (scalarEval f S g) := by
  exact DFunLike.congr_fun (congrArg GrpCat.Hom.hom
    (f.naturality (Under.homMk a h : S ⟶ B))) g

private abbrev sectionPoint {G : GroupScheme k} (n : 𝟙_ (SchemeOver k) ⟶ G.X)
    (R : TestAlgebra k) : GroupPoints G R :=
  toUnit _ ≫ n

private theorem sectionPoint_natural {G : GroupScheme k} (n : 𝟙_ (SchemeOver k) ⟶ G.X)
    {R B : TestAlgebra k} (a : R ⟶ B) :
    mapPoints a (sectionPoint n R) = sectionPoint n B := by
  change (testSpec k).map a.op ≫ toUnit ((testSpec k).obj (op R)) ≫ n =
    toUnit ((testSpec k).obj (op B)) ≫ n
  rw [← Category.assoc, comp_toUnit]

private theorem scalarEval_limit {A : AdditiveLine k} {P : PinnedGroup A}
    {R : TestAlgebra k}
    (f : scalarGroupPoints R P.pair.G.val ⟶ scalarGroupPoints R P.pair.G.val)
    (hT : FixesTorus P f) (S : Under R) (c : Cocharacter P.pair.T.group)
    {g z : GroupPoints P.pair.G.val S.right}
    (h : HasLimit (c ≫ P.pair.T.inclusion) g z) :
    HasLimit (c ≫ P.pair.T.inclusion) (scalarEval f S g) (scalarEval f S z) := by
  obtain ⟨p, hp, hp₀⟩ := h
  let B := S.right
  let P' := extendTest S (polynomialConstants B)
  let L := extendTest S (laurentConstants B)
  have hL : P'.hom ≫ polynomialToLaurent B = L.hom := by
    change (S.hom ≫ polynomialConstants B) ≫ polynomialToLaurent B = S.hom ≫ laurentConstants B
    rw [Category.assoc, polynomialConstants_laurent]
  have h0 : P'.hom ≫ polynomialEvaluate B 0 = S.hom := by
    change (S.hom ≫ polynomialConstants B) ≫ polynomialEvaluate B 0 = S.hom
    rw [Category.assoc, polynomialConstants_zero, Category.comp_id]
  have ht : scalarEval f L (cocharacterPoint (c ≫ P.pair.T.inclusion) (laurentAlgebra B)
      (laurentParameter B)) =
      cocharacterPoint (c ≫ P.pair.T.inclusion) (laurentAlgebra B) (laurentParameter B) :=
    hT L (cocharacterPoint c (laurentAlgebra B) (laurentParameter B))
  refine ⟨scalarEval f P' p, ?_, ?_⟩
  · rw [← scalarEval_natural f (S := P') (B := L) _ hL p, hp]
    unfold orbit
    rw [map_mul, map_mul, map_inv, ht, scalarEval_natural f (S := S) (B := L) _ rfl g]
  · rw [← scalarEval_natural f (S := P') (B := S) _ h0 p, hp₀]

private theorem fixesSubgroup_of_le {G : GroupScheme k} {R : TestAlgebra k}
    (f : scalarGroupPoints R G ⟶ scalarGroupPoints R G) {U V : ClosedSubgroup G}
    (h : IsSubgroupOf U V) (S : Under R)
    (hV : ∀ v : GroupPoints V.group S.right, scalarEval f S (v ≫ V.inclusion.hom.hom) =
      v ≫ V.inclusion.hom.hom) (u : GroupPoints U.group S.right) :
    scalarEval f S (u ≫ U.inclusion.hom.hom) = u ≫ U.inclusion.hom.hom := by
  obtain ⟨j, hj⟩ := h
  simpa only [Category.assoc, ← Grp.comp_hom_hom, hj] using hV (u ≫ j.hom.hom)

private theorem fixesSimpleRoot {A : AdditiveLine k} {P : PinnedGroup A}
    {R : TestAlgebra k}
    {f : scalarGroupPoints R P.pair.G.val ⟶ scalarGroupPoints R P.pair.G.val}
    (hp : FixesPinning P f) (S : Under R) (α : SimpleRoot P.pair)
    (u : GroupPoints (P.roots α.val).val.group S.right) :
    scalarEval f S (u ≫ (P.roots α.val).val.inclusion.hom.hom) =
      u ≫ (P.roots α.val).val.inclusion.hom.hom := by
  obtain ⟨a, rfl⟩ := rootPoint_surjective (P.pin α).val S.right u
  have hh := hp S α a
  change scalarEval f S (rootPoint ((P.pin α).val.hom ≫ (P.roots α.val).val.inclusion) S.right a) =
    rootPoint ((P.pin α).val.hom ≫ (P.roots α.val).val.inclusion) S.right a at hh
  rw [rootPoint_comp] at hh
  exact hh

private theorem commute_of_affine_tests {G H : GroupScheme k} (i : H ⟶ G)
    {B : TestAlgebra k} (g : GroupPoints G B)
    (h : ∀ (C : TestAlgebra k) (a : B ⟶ C) (t : GroupPoints H C),
      Commute (mapPoints a g : GroupPoints G C) (t ≫ i.hom.hom)) : Centralizes i g := by
  apply hom_ext_on_affine_tests
  intro C p
  let F := algSpec.fullyFaithful (R := CommRingCat.of k)
  let a : B ⟶ C := (F.preimage (p ≫ snd _ _)).unop
  have ha : (testSpec k).map a.op = p ≫ snd _ _ := F.map_preimage _
  rw [comp_conjugateFamily]
  have h' := (h C a (p ≫ fst _ _)).eq
  change ((testSpec k).map a.op ≫ g) * _ = _ * ((testSpec k).map a.op ≫ g) at h'
  rw [ha, Category.assoc] at h'
  exact mul_inv_eq_iff_eq_mul.mpr h'

private theorem conjugation_on_points {G : GroupScheme k} {T : ClosedSubgroup G}
    {n : 𝟙_ (SchemeOver k) ⟶ G.X} {e : T.group ≅ T.group}
    (h : Specs.BorelNormalizer.InducesTorusConjugation T n e)
    (B : TestAlgebra k) (t : GroupPoints T.group B) :
    sectionPoint n B * (show GroupPoints G B from t ≫ T.inclusion.hom.hom) * (sectionPoint n B)⁻¹ =
      (t ≫ e.hom.hom.hom) ≫ T.inclusion.hom.hom := by
  have he := congrArg (fun s : T.group.X ⟶ G.X => t ≫ s) h
  simpa only [Grp.comp_hom_hom, Category.assoc, MonObj.comp_mul, GrpObj.comp_inv,
    comp_toUnit_assoc] using he.symm

private theorem normalizerDisplacement {A : AdditiveLine k} {P : PinnedGroup A}
    {R : TestAlgebra k}
    {f : scalarGroupPoints R P.pair.G.val ⟶ scalarGroupPoints R P.pair.G.val}
    (hT : FixesTorus P f) (S : Under R) {n : 𝟙_ (SchemeOver k) ⟶ P.pair.G.val.X}
    {e : P.pair.T.group ≅ P.pair.T.group}
    (he : Specs.BorelNormalizer.InducesTorusConjugation P.pair.T n e) :
    ∃ t : GroupPoints P.pair.T.group S.right,
      t ≫ P.pair.T.inclusion.hom.hom =
        scalarEval f S (sectionPoint n S.right) * (sectionPoint n S.right)⁻¹ := by
  let T := P.pair.T
  have htorus : GeometricRadicals.IsTorus T.group :=
    isTorus_of_split P.pair.split
  have hc := Reductive.TorusCentralizer.maximalTorusCentralizer P.pair.G
    P.pair.reductive T htorus P.pair.maximal
  apply (hc _ _).mp
  apply commute_of_affine_tests
  intro B a t
  let L := extendTest S a
  let nB := sectionPoint n B
  let t₀ : GroupPoints T.group B := t ≫ e.inv.hom.hom
  let x : GroupPoints P.pair.G.val B := t₀ ≫ T.inclusion.hom.hom
  let y : GroupPoints P.pair.G.val B := t ≫ T.inclusion.hom.hom
  let j : GroupPoints P.pair.G.val B →* GroupPoints P.pair.G.val B := scalarEval f L
  have hnx : nB * x * nB⁻¹ = y := by
    rw [conjugation_on_points he B t₀]
    change (t ≫ ((underlying (k := k)).mapIso e).inv) ≫
      ((underlying (k := k)).mapIso e).hom ≫ T.inclusion.hom.hom = _
    rw [Category.assoc, Iso.inv_hom_id_assoc]
  have hfx : j nB * x * (j nB)⁻¹ = y := by
    have h := congrArg j hnx
    have hx : j x = x := hT L t₀
    have hy : j y = y := hT L t
    rwa [map_mul, map_mul, map_inv, hx, hy] at h
  have hnmap := sectionPoint_natural n a
  have hmap : mapPoints a (scalarEval f S (sectionPoint n S.right)) = j nB :=
    (scalarEval_natural f (S := S) (B := L) a rfl (sectionPoint n S.right)).symm.trans
      (congrArg j hnmap)
  change Commute ((((groupPointsFunctor k).obj P.pair.G.val).map a).hom
    (scalarEval f S (sectionPoint n S.right) * (sectionPoint n S.right)⁻¹)) y
  rw [map_mul, map_inv]
  change Commute (mapPoints a (scalarEval f S (sectionPoint n S.right)) *
    (mapPoints a (sectionPoint n S.right) : GroupPoints P.pair.G.val B)⁻¹) y
  rw [hmap, hnmap]
  show j nB * nB⁻¹ * y = y * (j nB * nB⁻¹)
  calc
    _ = j nB * x * nB⁻¹ := by rw [← hnx]; group
    _ = (j nB * x * (j nB)⁻¹) * (j nB * nB⁻¹) := by group
    _ = _ := by rw [hfx]

private theorem torusPoint_hasLimit {G : GroupScheme k} {T : ClosedSubgroup G}
    [IsCommMonObj T.group.X] (c : Cocharacter T.group) {B : TestAlgebra k}
    (t : GroupPoints T.group B) :
    HasLimit (c ≫ T.inclusion) (show GroupPoints G B from t ≫ T.inclusion.hom.hom)
      (show GroupPoints G B from t ≫ T.inclusion.hom.hom) := by
  apply centralizes_hasLimit
  refine (centralizes_onAlgebras _ _).mpr (fun C a u => ?_)
  let j := ((groupPointsFunctor k).map T.inclusion).app C
  change Commute (j (mapPoints a t)) (j (cocharacterPoint c C u))
  letI : CommGroup (GroupPoints T.group C) := CategoryTheory.Hom.commGroup
  exact (Commute.all _ _).map j.hom

private theorem rankOneWord_base {G : GroupScheme k} {A : AdditiveLine k}
    (x y : A.group ⟶ G) (n : 𝟙_ (SchemeOver k) ⟶ G.X)
    (hw : sectionPoint n (CommAlgCat.of k k) = rankOneWord x y (CommAlgCat.of k k) 1)
    (B : TestAlgebra k) :
    sectionPoint n B = rootPoint x B 1 * rootPoint y B (-1) * rootPoint x B 1 := by
  let a : CommAlgCat.of k k ⟶ B := CommAlgCat.ofHom (Algebra.ofId k B)
  let m := (((groupPointsFunctor k).obj G).map a).hom
  have h := congrArg m hw
  change mapPoints a (sectionPoint n _) = m (rankOneWord x y _ 1) at h
  rw [sectionPoint_natural] at h
  rw [h, rankOneWord, map_mul, map_mul]
  change mapPoints a (rootPoint x _ (↑(1 : kˣ) : k)) *
    mapPoints a (rootPoint y _ (-(↑((1 : kˣ)⁻¹) : k))) *
      mapPoints a (rootPoint x _ (↑(1 : kˣ) : k)) = _
  simp only [rootPoint_natural, inv_one, Units.val_one, map_one, map_neg]

/-- The normalizer word is fixed once the positive subgroup and torus
are fixed. The opposite factor cannot change by an element of the
positive parabolic, by the trivial opposite-limit intersection. -/
private theorem fixedRankOneWord {A : AdditiveLine k} {P : PinnedGroup A}
    [IsCommMonObj P.pair.T.group.X] {R : TestAlgebra k}
    {f : scalarGroupPoints R P.pair.G.val ⟶ scalarGroupPoints R P.pair.G.val}
    (hT : FixesTorus P f) (S : Under R) (c : Cocharacter P.pair.T.group)
    (x y : GroupPoints P.pair.G.val S.right)
    (hx : HasLimit (c ≫ P.pair.T.inclusion) x 1)
    (hy : HasLimit (oppositeCocharacter (c ≫ P.pair.T.inclusion)) y 1)
    (hfx : scalarEval f S x = x)
    {n : 𝟙_ (SchemeOver k) ⟶ P.pair.G.val.X} {e : P.pair.T.group ≅ P.pair.T.group}
    (he : Specs.BorelNormalizer.InducesTorusConjugation P.pair.T n e)
    (hn : sectionPoint n S.right = x * y * x) :
    scalarEval f S (sectionPoint n S.right) = sectionPoint n S.right := by
  let B := S.right
  let j := scalarEval f S
  obtain ⟨t, ht⟩ := normalizerDisplacement hT S he
  let tG : GroupPoints P.pair.G.val B := t ≫ P.pair.T.inclusion.hom.hom
  have hword : x * j y * x = tG * (x * y * x) := by
    have hh := mul_inv_eq_iff_eq_mul.mp ht.symm
    rw [hn, map_mul, map_mul, hfx] at hh
    exact hh
  have heq : j y * y⁻¹ = x⁻¹ * tG * x := by
    calc
      j y * y⁻¹ = x⁻¹ * (x * j y * x) * (x⁻¹ * y⁻¹) := by group
      _ = x⁻¹ * tG * x := by rw [hword]; group
  have hneg : HasLimit (oppositeCocharacter (c ≫ P.pair.T.inclusion)) (j y * y⁻¹) 1 := by
    have hc' : oppositeCocharacter (c ≫ P.pair.T.inclusion) =
        oppositeCocharacter c ≫ P.pair.T.inclusion := by
      unfold oppositeCocharacter
      rw [Category.assoc]
    rw [hc'] at hy ⊢
    have hz := (scalarEval_limit f hT S (oppositeCocharacter c) hy).mul hy.inv
    simpa only [map_one, inv_one, mul_one] using hz
  have hpos : HasExtension (c ≫ P.pair.T.inclusion) (j y * y⁻¹) := by
    rw [heq]
    exact ⟨_, (hx.inv.mul (torusPoint_hasLimit c t)).mul hx⟩
  have h₁ := oppositeLimit_intersection_onPoints P.pair.G.property.1
    (c ≫ P.pair.T.inclusion) _ hpos hneg
  have hjy : j y = y := by simpa only [one_mul] using mul_inv_eq_iff_eq_mul.mp h₁
  rw [hn, map_mul, map_mul, hfx, hjy]

open private inducedConjugation_unique from LinearAlgebraicGroups.RootData.DatumAndWeyl

private theorem fixedSimpleRepresentative {A : AdditiveLine k} {P : PinnedGroup A}
    [IsCommMonObj P.pair.T.group.X] (D₀ : Datum P.pair.T) {R : TestAlgebra k}
    {f : scalarGroupPoints R P.pair.G.val ⟶ scalarGroupPoints R P.pair.G.val}
    (hT : FixesTorus P f) (hpin : FixesPinning P f) (α : SimpleRoot P.pair) :
    ∃ (n : 𝟙_ (SchemeOver k) ⟶ P.pair.G.val.X) (e : P.pair.T.group ≅ P.pair.T.group),
      Normalizes P.pair.T.inclusion n ∧
      Specs.BorelNormalizer.InducesTorusConjugation P.pair.T n e ∧
      (∀ χ : Character P.pair.T.group,
        (RootPairing.Equiv.reflection D₀.rootDatum α.val).weightEquiv (Additive.ofMul χ) =
          Additive.ofMul (e.inv ≫ χ)) ∧
      ∀ S : Under R, scalarEval f S (sectionPoint n S.right) = sectionPoint n S.right := by
  obtain ⟨C, c, _, _, D, E, _, Q, F, J, B, p, m, hpos, _, h⟩ := D₀.attached α.val
  dsimp only at h
  obtain ⟨_, _, r, hr⟩ := h
  refine ⟨r.representative, r.conjugation, r.normalizes, r.conjugates, ?_, ?_⟩
  · intro χ
    have hp : D₀.rootDatum.coroot' α.val (Additive.ofMul χ) =
        pairing P.pair.T.group χ r.coroot := by
      rw [hr]
      exact D₀.pairing_eq χ (Additive.toMul (D₀.rootDatum.coroot α.val))
    rw [RootPairing.Equiv.reflection_weightEquiv, RootPairing.reflection_apply, hp,
      D₀.root_eq, r.reflection, ofMul_mul, ofMul_zpow, neg_smul, sub_eq_add_neg]
  · intro S
    let T := P.pair.T
    let pos := p.root.hom ≫ D.contracting.inclusion ≫ C.subgroup.inclusion
    let neg := m.root.hom ≫ E.contracting.inclusion ≫ C.subgroup.inclusion
    let x := rootPoint pos S.right 1
    let y := rootPoint neg S.right (-1)
    have hcp : (c ≫ C.torusIso.hom ≫ C.torus.inclusion) ≫ C.subgroup.inclusion =
        c ≫ T.inclusion := by
      simp only [Category.assoc, C.torus_inclusion, T]
    have hx : HasLimit (c ≫ T.inclusion) x 1 := by
      have hp' := (D.contracting_points S.right _).mpr
        ⟨rootPoint p.root.hom S.right 1, rfl⟩
      have hh := map_hasLimit C.subgroup.inclusion _ hp'
      change HasLimit _ ((rootPoint p.root.hom S.right 1 ≫ D.contracting.inclusion.hom.hom) ≫
        C.subgroup.inclusion.hom.hom) ((1 : GroupPoints C.subgroup.group S.right) ≫
          C.subgroup.inclusion.hom.hom) at hh
      simpa only [hcp, MonObj.one_comp, ← rootPoint_comp, Category.assoc, x, pos] using hh
    have hy : HasLimit (oppositeCocharacter (c ≫ T.inclusion)) y 1 := by
      have hn' := (E.contracting_points S.right _).mpr
        ⟨rootPoint m.root.hom S.right (-1), rfl⟩
      have hh := map_hasLimit C.subgroup.inclusion _ hn'
      have hc' : oppositeCocharacter (c ≫ C.torusIso.hom ≫ C.torus.inclusion) ≫
          C.subgroup.inclusion = oppositeCocharacter (c ≫ T.inclusion) := by
        unfold oppositeCocharacter
        rw [Category.assoc, hcp]
      change HasLimit _ ((rootPoint m.root.hom S.right (-1) ≫ E.contracting.inclusion.hom.hom) ≫
        C.subgroup.inclusion.hom.hom) ((1 : GroupPoints C.subgroup.group S.right) ≫
          C.subgroup.inclusion.hom.hom) at hh
      simpa only [hc', MonObj.one_comp, ← rootPoint_comp, Category.assoc, y, neg] using hh
    have hle : IsSubgroupOf (subgroupOfSubgroup C.subgroup D.contracting) (P.roots α.val).val := by
      obtain ⟨_, _, _, _, _, huniq⟩ :=
        ((RootData.RootGroups.rootSubgroups P.pair.G P.pair.reductive T P.pair.split
          P.pair.maximal).2 α.val.val α.val.property).2.2
      exact (same_subgroup_trans ⟨(huniq _ hpos).2, (huniq _ hpos).1⟩
        (huniq _ (P.roots α.val).property)).1
    have hfx : scalarEval f S x = x := by
      have hh := fixesSubgroup_of_le f hle S (fixesSimpleRoot hpin S α) (rootPoint p.root.hom S.right 1)
      change scalarEval f S (rootPoint p.root.hom S.right 1 ≫
        (D.contracting.inclusion ≫ C.subgroup.inclusion).hom.hom) =
        rootPoint p.root.hom S.right 1 ≫ (D.contracting.inclusion ≫ C.subgroup.inclusion).hom.hom at hh
      simpa only [x, pos, ← rootPoint_comp] using hh
    exact fixedRankOneWord hT S c x y hx hy hfx r.conjugates
      (rankOneWord_base pos neg r.representative r.representative_word S.right)

private theorem normalizes_of_scalarAction {G : GroupScheme k} (hG : IsAffine G.X.left)
    {T U : ClosedSubgroup G} {A : AdditiveLine k} {χ : Character T.group}
    (x : A.group ≅ U.group) (hx : HasScalarAction T χ (x.hom ≫ U.inclusion)) :
    Normalizes U.inclusion T.inclusion.hom.hom := by
  let Y := U.group.X ⊗ T.group.X
  letI := affine_subgroup hG U
  letI := affine_subgroup hG T
  obtain ⟨B, ⟨a⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr
    (affine_tensor (A := U.group.X) (B := T.group.X))
  let t : GroupPoints T.group B.unop := a.hom ≫ snd _ _
  let u : GroupPoints U.group B.unop := a.hom ≫ fst _ _
  obtain ⟨b, hb⟩ := rootPoint_surjective x B.unop u
  have heq (g : Y ⟶ G.X) (v : GroupPoints U.group B.unop)
      (h : v ≫ U.inclusion.hom.hom = a.hom ≫ g) :
      ∃ z : Y ⟶ U.group.X, z ≫ U.inclusion.hom.hom = g :=
    ⟨a.inv ≫ v, by rw [Category.assoc, h, Iso.inv_hom_id_assoc]⟩
  have hb' : rootPoint (x.hom ≫ U.inclusion) B.unop b = u ≫ U.inclusion.hom.hom := by
    rw [rootPoint_comp, hb]
  apply (normalizesIff k U.inclusion U.isClosedImmersion _ _).mpr
  constructor
  · refine heq _ (rootPoint x.hom B.unop (characterValue χ B.unop t * b)) ?_
    simpa only [comp_conjugateFamily, Category.assoc, ← rootPoint_comp, hb', t, u] using
      (hx B.unop t b).symm
  · refine heq _ (rootPoint x.hom B.unop (characterValue χ B.unop t⁻¹ * b)) ?_
    have ht : a.hom ≫ snd U.group.X T.group.X ≫ (T.inclusion.hom.hom)⁻¹ =
        t⁻¹ ≫ T.inclusion.hom.hom := by
      calc
        _ = a.hom ≫ (snd U.group.X T.group.X ≫ T.inclusion.hom.hom)⁻¹ :=
          congrArg (a.hom ≫ ·) (GrpObj.comp_inv _ _)
        _ = (a.hom ≫ snd U.group.X T.group.X ≫ T.inclusion.hom.hom)⁻¹ :=
          GrpObj.comp_inv _ _
        _ = (t ≫ T.inclusion.hom.hom)⁻¹ :=
          congrArg (fun z : Points G.X B.unop => z⁻¹) (Category.assoc _ _ _).symm
        _ = _ := (GrpObj.inv_comp _ _).symm
    rw [comp_conjugateFamily, ht, ← rootPoint_comp]
    rw [← Category.assoc, ← show u = a.hom ≫ fst _ _ from rfl, ← hb']
    exact (hx B.unop t⁻¹ b).symm

open private transportSubgroup from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private conjugationIso conjugation_apply from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy

/-- Conjugating a root coordinate by a rational normalizer transports
its character by inverse pullback. -/
private theorem transportedRoot_fixed {A : AdditiveLine k} {P : PinnedGroup A}
    {R : TestAlgebra k}
    {f : scalarGroupPoints R P.pair.G.val ⟶ scalarGroupPoints R P.pair.G.val}
    (hpin : FixesPinning P f) (α : SimpleRoot P.pair) (β : Root P.pair.T)
    {n : 𝟙_ (SchemeOver k) ⟶ P.pair.G.val.X} {e : P.pair.T.group ≅ P.pair.T.group}
    (he : Specs.BorelNormalizer.InducesTorusConjugation P.pair.T n e)
    (hχ : β.val = e.inv ≫ α.val.val)
    (hn : ∀ S : Under R, scalarEval f S (sectionPoint n S.right) = sectionPoint n S.right)
    (S : Under R) (b : GroupPoints (P.roots β).val.group S.right) :
    scalarEval f S (b ≫ (P.roots β).val.inclusion.hom.hom) =
      b ≫ (P.roots β).val.inclusion.hom.hom := by
  let T := P.pair.T
  let U := (P.roots α.val).val
  let V := transportSubgroup (conjugationIso n) U
  let x := (P.pin α).val
  have hx : HasScalarAction T β.val (x.hom ≫ V.inclusion) := by
    intro B t z
    let s : GroupPoints T.group B := t ≫ e.inv.hom.hom
    have ht : sectionPoint n B * (show GroupPoints P.pair.G.val B from s ≫ T.inclusion.hom.hom) * (sectionPoint n B)⁻¹ =
        t ≫ T.inclusion.hom.hom := by
      rw [conjugation_on_points he B s]
      change (t ≫ ((underlying (k := k)).mapIso e).inv) ≫
        ((underlying (k := k)).mapIso e).hom ≫ T.inclusion.hom.hom = _
      rw [Category.assoc, Iso.inv_hom_id_assoc]
    have hval : characterValue β.val B t = characterValue α.val.val B s := by
      rw [hχ]
      rfl
    have hcoord (a : B) : rootPoint (x.hom ≫ V.inclusion) B a =
        sectionPoint n B * rootPoint (x.hom ≫ U.inclusion) B a * (sectionPoint n B)⁻¹ := by
      change rootPoint (x.hom ≫ U.inclusion ≫ (conjugationIso n).hom) B a = _
      rw [← Category.assoc, rootPoint_comp]
      exact conjugation_apply n _
    dsimp only
    rw [← ht, hval, hcoord, hcoord]
    have h := (P.pin α).property B s z
    dsimp only at h
    rw [← h]
    dsimp only [T, x, U]
    group
  have hV : IsRootSubgroup T V β.val :=
    ⟨(P.roots α.val).property.1, (P.roots α.val).property.2.1,
      normalizes_of_scalarAction P.pair.G.property.1 x hx,
      tangent_weight_of_scalarAction T V β.val A x hx⟩
  have hle : IsSubgroupOf (P.roots β).val V := by
    obtain ⟨_, _, _, _, _, hu⟩ :=
      ((RootData.RootGroups.rootSubgroups P.pair.G P.pair.reductive T P.pair.split
        P.pair.maximal).2 β.val β.property).2.2
    exact (same_subgroup_trans ⟨(hu _ (P.roots β).property).2, (hu _ (P.roots β).property).1⟩
      (hu _ hV)).1
  refine fixesSubgroup_of_le f hle S (fun v => ?_) b
  let v' : GroupPoints U.group S.right := v
  have hv : v ≫ V.inclusion.hom.hom =
      sectionPoint n S.right * (show GroupPoints P.pair.G.val S.right from
        v' ≫ U.inclusion.hom.hom) * (sectionPoint n S.right)⁻¹ := by
    change v' ≫ U.inclusion.hom.hom ≫ (conjugationIso n).hom.hom.hom = _
    rw [← Category.assoc]
    exact conjugation_apply n _
  rw [hv, map_mul, map_mul, map_inv, hn S, fixesSimpleRoot hpin S α v']

private theorem fixesAllRoots {A : AdditiveLine k} {P : PinnedGroup A}
    {R : TestAlgebra k}
    {f : scalarGroupPoints R P.pair.G.val ⟶ scalarGroupPoints R P.pair.G.val}
    (hT : FixesTorus P f) (hp : FixesPinning P f) (S : Under R) (β : Root P.pair.T)
    (b : GroupPoints (P.roots β).val.group S.right) :
    scalarEval f S (b ≫ (P.roots β).val.inclusion.hom.hom) =
      b ≫ (P.roots β).val.inclusion.hom.hom := by
  let T := P.pair.T
  let G := P.pair.G
  obtain ⟨c, _, hc, _, hpos⟩ :=
    (RootData.BorelsAndChambers.borelsThroughT G P.pair.reductive T P.pair.split P.pair.maximal).1
      P.pair.B P.pair.borel P.pair.containsTorus
  obtain ⟨hcomm, ⟨D⟩⟩ := RootData.AbstractPairing.abstractPairing G P.pair.reductive T
    P.pair.split P.pair.maximal
  letI := hcomm
  letI := D.finiteRoots
  letI := D.freeCharacters
  letI := D.finiteCharacters
  letI := D.reduced
  let v := Specs.SimpleRoots.evaluate D c
  have hv (i : Root T) : v (D.rootDatum.root i) = pairing T.group i.val c := by
    change D.rootDatum.toLinearMap (D.rootDatum.root i) (Additive.ofMul c) = _
    rw [D.root_eq, D.pairing_eq]
  obtain ⟨base, hb⟩ := RootData.SimpleRoots.baseFor D.rootDatum v (fun i => hv i ▸ hc i)
  have hsimple (i : Root T) (hi : i ∈ base.support) : IsSimple P.pair i := by
    have hpr : Specs.SimpleRoots.positive D.rootDatum v =
        Specs.BorelsAndChambers.subgroupRoots T P.pair.B := by
      rw [hpos]
      ext j
      change (0 < v (D.rootDatum.root j)) ↔ (0 < pairing T.group j.val c)
      rw [hv]
    rw [hb.simple_iff, hpr] at hi
    simpa only [IsSimple, D.root_eq, ← ofMul_mul, Additive.ofMul.injective.ne_iff] using hi
  obtain ⟨N, hN, act, hact⟩ := D.normalizerAction
  let j : (𝟙_ (SchemeOver k) ⟶ N.group.X) →* GroupPoints G.val R :=
    { toFun := fun n => sectionPoint (n ≫ N.inclusion.hom.hom) R
      map_one' := by simp only [MonObj.one_comp, MonObj.comp_one]
      map_mul' := by intro x y; simp only [MonObj.mul_comp, MonObj.comp_mul] }
  let K : Subgroup (𝟙_ (SchemeOver k) ⟶ N.group.X) :=
    MonoidHom.eqLocus ((scalarEval f (Under.mk (𝟙 R))).comp j) j
  let L : Subgroup D.rootDatum.weylGroup :=
    (K.map act).comap D.rootDatum.weylGroup.subtype
  have hL : L = ⊤ := by
    apply top_unique
    rw [← hb.generates]
    apply (Subgroup.closure_le L).mpr
    rintro _ ⟨i, rfl⟩
    let α : SimpleRoot P.pair := ⟨i.val, hsimple _ i.property⟩
    obtain ⟨n, e, hn, he, hw, hfixed⟩ := fixedSimpleRepresentative D hT hp α
    obtain ⟨n', hn'⟩ := (hN _ n).mp hn
    obtain ⟨e', he', hw', _⟩ := hact n'
    have he'' : Specs.BorelNormalizer.InducesTorusConjugation T n e' := by
      unfold Specs.BorelNormalizer.InducesTorusConjugation
      simpa only [Category.assoc, hn'] using he'
    have heq := inducedConjugation_unique he'' he
    have hweight : act n' = RootPairing.Equiv.reflection D.rootDatum i.val := by
      apply RootPairing.Equiv.weightHom_injective D.rootDatum
      apply LinearEquiv.ext
      intro χ
      change (act n').weightEquiv (Additive.ofMul (Additive.toMul χ)) =
        (RootPairing.Equiv.reflection D.rootDatum i.val).weightEquiv
          (Additive.ofMul (Additive.toMul χ))
      rw [hw', heq, hw]
    refine ⟨n', ?_, hweight⟩
    change scalarEval f (Under.mk (𝟙 R)) (sectionPoint (n' ≫ N.inclusion.hom.hom) R) =
      sectionPoint (n' ≫ N.inclusion.hom.hom) R
    rw [hn']
    exact hfixed _
  obtain ⟨w, i, hi⟩ := hb.orbit β
  have hw : w ∈ L := hL.symm ▸ Subgroup.mem_top w
  obtain ⟨n', hfixed, hn'⟩ := hw
  let n := n' ≫ N.inclusion.hom.hom
  obtain ⟨e, he, hweight, _⟩ := hact n'
  have hχ : β.val = e.inv ≫ i.val.val := by
    apply Additive.ofMul.injective
    rw [← hweight, ← D.root_eq β, ← D.root_eq i.val, ← hi, hn']
    exact (w.val.toHom.root_weightMap_apply D.rootDatum D.rootDatum i.val).symm
  have hn (B : Under R) : scalarEval f B (sectionPoint n B.right) = sectionPoint n B.right := by
    have hh := scalarEval_natural f (S := Under.mk (𝟙 R)) (B := B) B.hom
      (Category.id_comp _) (sectionPoint n R)
    change scalarEval f (Under.mk (𝟙 R)) (sectionPoint n R) = sectionPoint n R at hfixed
    rw [hfixed, sectionPoint_natural n B.hom] at hh
    exact hh
  exact transportedRoot_fixed hp ⟨i.val, hsimple _ i.property⟩ β he hχ hn S b

open private product_pullback from LinearAlgebraicGroups.Reductive.CocharacterOpenCell
open private isReduced_of_smooth_over_field from LinearAlgebraicGroups.Affine.SmoothnessCriteria
open private irreducible_of_geometricallyConnected
  from LinearAlgebraicGroups.Solvable.WordDomainGeometry

private theorem scheme_hom_eq_of_schematicallyDominant {X Y Z : Scheme.{u}} {i : X ⟶ Y}
    [IsSchemeTheoreticallyDominant i] [QuasiCompact i] [IsAffine Z]
    {f g : Y ⟶ Z} (h : i ≫ f = i ≫ g) : f = g := by
  apply AlgebraicGeometry.ext_of_isAffine
  apply ConcreteCategory.hom_ext
  intro s
  apply i.app_injective ⊤
  have hh := congrArg Scheme.Hom.appTop h
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at hh
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hh) s

private theorem tensor_id_pullback {X Y : SchemeOver k} (i : X ⟶ Y) (Z : SchemeOver k) :
    IsPullback (fst X Z).left (i ⊗ₘ 𝟙 Z).left i.left (fst Y Z).left := by
  apply IsPullback.of_bot _ _ (product_pullback Y Z)
  · simpa only [← Over.comp_left, tensorHom_snd, Category.comp_id, Over.w] using
      product_pullback X Z
  · rw [← Over.comp_left, ← Over.comp_left, tensorHom_fst]

/-- Restriction to a schematically dense affine cell determines a natural
endomorphism after any scalar extension. The flat base change is used on
schemes before evaluating at the universal affine point. -/
private theorem scalarEval_eq_of_cell {G : GroupScheme k} (hG : IsAffine G.X.left)
    {X : SchemeOver k} (hX : IsAffine X.left) (i : X ⟶ G.X)
    [IsSchemeTheoreticallyDominant i.left]
    {R : TestAlgebra k} (f : scalarGroupPoints R G ⟶ scalarGroupPoints R G)
    (hi : ∀ (B : Under R) (p : Points X B.right), scalarEval f B (p ≫ i) = p ≫ i) :
    f = 𝟙 _ := by
  let Z := (testSpec k).obj (op R)
  letI : IsAffine Z.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of R)))
  letI := hG
  letI := hX
  letI : QuasiCompact i.left := inferInstance
  let j := i ⊗ₘ 𝟙 Z
  have hpb := tensor_id_pullback i Z
  letI : Flat (fst G.X Z).left :=
    MorphismProperty.of_isPullback (product_pullback G.X Z).flip (inferInstance : Flat Z.hom)
  letI : IsSchemeTheoreticallyDominant j.left := IsSchemeTheoreticallyDominant.of_isPullback hpb
  let F := algSpec.fullyFaithful (R := CommRingCat.of k)
  obtain ⟨B, ⟨e⟩⟩ := essImage_algSpec.mpr (affine_tensor (A := G.X) (B := Z))
  obtain ⟨C, ⟨d⟩⟩ := essImage_algSpec.mpr (affine_tensor (A := X) (B := Z))
  let b : R ⟶ B.unop := (F.preimage (e.hom ≫ snd _ _)).unop
  let c : R ⟶ C.unop := (F.preimage (d.hom ≫ snd _ _)).unop
  let a : B.unop ⟶ C.unop := (F.preimage (d.hom ≫ j ≫ e.inv)).unop
  have hb : (testSpec k).map b.op = e.hom ≫ snd _ _ := F.map_preimage _
  have hc : (testSpec k).map c.op = d.hom ≫ snd _ _ := F.map_preimage _
  have ha : (testSpec k).map a.op = d.hom ≫ j ≫ e.inv := F.map_preimage _
  have hab : b ≫ a = c := by
    apply Quiver.Hom.op_inj
    apply F.map_injective
    simp only [op_comp, Functor.map_comp, ha, hb, hc, Category.assoc, Iso.inv_hom_id_assoc]
    exact congrArg (d.hom ≫ ·) (show j ≫ snd _ _ = snd _ _ from by simp [j])
  let p : GroupPoints G B.unop := e.hom ≫ fst _ _
  have hpa : mapPoints a p = (d.hom ≫ fst _ _) ≫ i := by
    simp only [mapPoints, p, ha, Category.assoc, Iso.inv_hom_id_assoc, j, tensorHom_fst]
  have hp : scalarEval f (Under.mk b) p = p := by
    have hh := scalarEval_natural f (S := Under.mk b) (B := Under.mk c) a hab p
    rw [hpa, hi] at hh
    have hf : mapPoints a (scalarEval f (Under.mk b) p) = mapPoints a p :=
      hh.symm.trans hpa.symm
    apply Over.OverMorphism.ext
    haveI : IsIso d.hom.left := (Over.forget _).map_isIso d.hom
    haveI : IsIso e.inv.left := (Over.forget _).map_isIso e.inv
    haveI : IsSchemeTheoreticallyDominant (d.hom ≫ j ≫ e.inv).left := by
      simp only [Over.comp_left]
      infer_instance
    haveI : IsAffine ((testSpec k).obj C).left :=
      inferInstanceAs (IsAffine (Spec (CommRingCat.of C.unop)))
    haveI : IsAffine ((testSpec k).obj B).left :=
      inferInstanceAs (IsAffine (Spec (CommRingCat.of B.unop)))
    haveI : QuasiCompact (d.hom ≫ j ≫ e.inv).left := inferInstance
    apply scheme_hom_eq_of_schematicallyDominant (i := (d.hom ≫ j ≫ e.inv).left)
    change (d.hom ≫ j ≫ e.inv ≫ scalarEval f (Under.mk b) p).left =
      (d.hom ≫ j ≫ e.inv ≫ p).left
    exact congrArg Over.Hom.left (by simpa only [mapPoints, ha, Category.assoc] using hf)
  apply NatTrans.ext
  funext S
  apply GrpCat.hom_ext
  apply DFunLike.ext
  intro g
  let g' : Points G.X S.right := g
  let q : (testSpec k).obj (op S.right) ⟶ G.X ⊗ Z :=
    lift g' ((testSpec k).map S.hom.op)
  let z : B.unop ⟶ S.right := (F.preimage (q ≫ e.inv)).unop
  have hz : (testSpec k).map z.op = q ≫ e.inv := F.map_preimage _
  have hz₀ : b ≫ z = S.hom := by
    apply Quiver.Hom.op_inj
    apply F.map_injective
    simp only [op_comp, Functor.map_comp, hz, hb, Category.assoc, Iso.inv_hom_id_assoc]
    exact lift_snd g' ((testSpec k).map S.hom.op)
  have hz₁ : mapPoints z p = g := by
    simp only [mapPoints, hz, p, Category.assoc, Iso.inv_hom_id_assoc]
    exact lift_fst g' ((testSpec k).map S.hom.op)
  have hn := scalarEval_natural f (S := Under.mk b) (B := S) z hz₀ p
  rw [hp, hz₁] at hn
  exact hn

open Specs.OrderedRootProducts (Enumerates rootCellMap rootProduct product)

private theorem product_affine {I : Type u} (X : I → SchemeOver k)
    (h : ∀ i, IsAffine (X i).left) (l : List I) : IsAffine (product X l).left := by
  induction l with
  | nil => exact inferInstanceAs (IsAffine (Spec (CommRingCat.of k)))
  | cons i l hl =>
    letI := h i
    letI := hl
    exact affine_tensor (A := X i) (B := product X l)

private theorem fixesRootProduct {A : AdditiveLine k} {P : PinnedGroup A}
    {R : TestAlgebra k}
    {f : scalarGroupPoints R P.pair.G.val ⟶ scalarGroupPoints R P.pair.G.val}
    (hroot : ∀ (S : Under R) (α : Root P.pair.T) (b : GroupPoints (P.roots α).val.group S.right),
      scalarEval f S (b ≫ (P.roots α).val.inclusion.hom.hom) =
        b ≫ (P.roots α).val.inclusion.hom.hom) (S : Under R) (l : List (Root P.pair.T))
    (x : Points (product (fun α => (P.roots α).val.group.X) l) S.right) :
    scalarEval f S (x ≫ rootProduct P.roots l) = x ≫ rootProduct P.roots l := by
  induction l with
  | nil =>
    change scalarEval f S (x ≫ 1) = x ≫ 1
    rw [MonObj.comp_one, map_one]
  | cons α l ih =>
    change scalarEval f S (x ≫ ((_ ≫ (P.roots α).val.inclusion.hom.hom) *
      (_ ≫ rootProduct P.roots l))) = _
    rw [MonObj.comp_mul, map_mul]
    simp only [← Category.assoc, hroot, ih]
    simp only [rootProduct, MonObj.comp_mul, Category.assoc]

theorem scalarRigidity : ScalarRigidity.{u} := by
  intro k _ A P R f hT hp
  classical
  let T := P.pair.T
  let G := P.pair.G
  obtain ⟨c, _, hc, _, _⟩ :=
    (RootData.BorelsAndChambers.borelsThroughT G P.pair.reductive T P.pair.split P.pair.maximal).1
      P.pair.B P.pair.borel P.pair.containsTorus
  haveI : Finite (Root T) := (RootData.OrderedRootProducts.contractingProduct G P.pair.reductive T
    P.pair.split P.pair.maximal).1
  letI := Fintype.ofFinite (Root T)
  let pos := (Specs.BorelsAndChambers.positiveRoots T c).toFinset
  let neg := (Specs.BorelsAndChambers.positiveRoots T (oppositeCocharacter c)).toFinset
  have hpos : Enumerates pos.toList (Specs.BorelsAndChambers.positiveRoots T c) :=
    ⟨Finset.nodup_toList _, by simp [pos]⟩
  have hneg : Enumerates neg.toList (Specs.BorelsAndChambers.positiveRoots T (oppositeCocharacter c)) :=
    ⟨Finset.nodup_toList _, by simp [neg]⟩
  let j := rootCellMap T P.roots neg.toList pos.toList
  letI : IsOpenImmersion j.left :=
    RootData.OrderedRootProducts.regularRootCell G P.pair.reductive T P.pair.split P.pair.maximal
      c hc P.roots _ _ hneg hpos
  letI : IsAffine (product (fun α => (P.roots α).val.group.X) neg.toList).left :=
    product_affine _ (fun _ => affine_subgroup G.property.1 _) neg.toList
  letI : IsAffine (product (fun α => (P.roots α).val.group.X) pos.toList).left :=
    product_affine _ (fun _ => affine_subgroup G.property.1 _) pos.toList
  letI : IsAffine T.group.X.left := affine_subgroup G.property.1 T
  letI : IsAffine (T.group.X ⊗ product (fun α => (P.roots α).val.group.X) pos.toList).left :=
    affine_tensor
  have hX : IsAffine (product (fun α => (P.roots α).val.group.X) neg.toList ⊗
      (T.group.X ⊗ product (fun α => (P.roots α).val.group.X) pos.toList)).left := affine_tensor
  letI := G.property.2.1
  letI := G.property.2.2
  letI := P.pair.reductive.2.1
  letI : IrreducibleSpace G.val.X.left := irreducible_of_geometricallyConnected G.val
  letI : Smooth G.val.X.hom := P.pair.reductive.1
  letI : IsReduced G.val.X.left := isReduced_of_smooth_over_field G.val.X.hom
  have hnonempty (l : List (Root T)) :
      Nonempty (𝟙_ (SchemeOver k) ⟶ product (fun α => (P.roots α).val.group.X) l) := by
    induction l with
    | nil => exact ⟨𝟙 _⟩
    | cons α l ih => exact ⟨lift η[_] (Classical.choice ih)⟩
  let point := lift (Classical.choice (hnonempty neg.toList))
    (lift η[T.group.X] (Classical.choice (hnonempty pos.toList)))
  letI : Nonempty (product (fun α => (P.roots α).val.group.X) neg.toList ⊗
      (T.group.X ⊗ product (fun α => (P.roots α).val.group.X) pos.toList)).left :=
    ⟨point.left (IsLocalRing.closedPoint k)⟩
  letI : IsDominant j.left := ⟨j.left.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  letI := IsSchemeTheoreticallyDominant.of_isDominant j.left
  apply scalarEval_eq_of_cell G.property.1 hX j f
  intro S b
  change scalarEval f S (b ≫ ((_ ≫ rootProduct P.roots neg.toList) *
    (_ ≫ ((_ ≫ T.inclusion.hom.hom) * (_ ≫ rootProduct P.roots pos.toList))))) = _
  have ht' (u : GroupPoints T.group S.right) :
      scalarEval f S (u ≫ T.inclusion.hom.hom) = u ≫ T.inclusion.hom.hom := hT S u
  symm
  simp only [j, rootCellMap, MonObj.comp_mul, map_mul, ← Category.assoc, ht',
    fixesRootProduct (fixesAllRoots hT hp) S]

theorem scalarCharacterRigidity : ScalarCharacterRigidity.{u} := by
  intro k _ A P R f g hg hχ hp
  apply scalarRigidity P R f _ hp
  intro S t
  have ht : scalarEval g S t = t :=
    charactersSeparatePoints P.pair.split S.right _ _ (hχ S t)
  exact (hg S t).trans (congrArg (fun z : GroupPoints P.pair.T.group S.right =>
    z ≫ P.pair.T.inclusion.hom.hom) ht)

private theorem sameTorus {A : AdditiveLine k} {P Q : PinnedGroup A}
    (f g : PinnedIso P Q)
    (h : ∀ χ : Character P.pair.T.group,
      transportCharacter f.torus χ = transportCharacter g.torus χ) : f.torus = g.torus := by
  apply Iso.ext_inv
  apply Grp.hom_ext
  apply hom_ext_on_affine_tests
  intro R t
  apply charactersSeparatePoints P.pair.split R
  intro χ
  simpa only [transportCharacter, Grp.comp_hom_hom, Category.assoc] using
    congrArg (fun a : Character Q.pair.T.group => t ≫ a.hom.hom) (h χ)

theorem pinnedIsoUniqueness : PinnedIsoUniqueness.{u} := by
  intro k _ A P Q f g h
  have ht := sameTorus f g h
  let a := f.trans g.symm
  have ha : a.torus = Iso.refl _ := by
    change f.torus ≪≫ g.torus.symm = _
    rw [ht, Iso.self_symm_id]
  have htorus (S : TestAlgebra k) (t : GroupPoints P.pair.T.group S) :
      (t ≫ P.pair.T.inclusion.hom.hom) ≫ a.group.hom.hom.hom =
        t ≫ P.pair.T.inclusion.hom.hom := by
    have hh := a.torus_comm
    rw [ha, Iso.refl_hom, Category.id_comp] at hh
    simpa only [Grp.comp_hom_hom, Category.assoc] using
      congrArg (fun j : P.pair.T.group ⟶ P.pair.G.val => t ≫ j.hom.hom) hh
  have hpin (i : SimpleRoot P.pair) :
      (P.pin i).val.hom ≫ (P.roots i.val).val.inclusion ≫ a.group.hom =
        (P.pin i).val.hom ≫ (P.roots i.val).val.inclusion := by
    have hp := a.pin_comm
    let x := (P.pin i).val.hom ≫ (P.roots i.val).val.inclusion
    have hh : (i.val.val, x ≫ a.group.hom) ∈ pinGraph P := by
      rw [← hp]
      refine ⟨(i.val.val, x), ⟨i, rfl⟩, ?_⟩
      simp [ha, transportCharacter]
    obtain ⟨j, hj⟩ := hh
    have he : j = i := Subtype.ext (Subtype.ext (congrArg Prod.fst hj))
    subst j
    exact (Category.assoc _ _ _).symm.trans (congrArg Prod.snd hj).symm
  let R := CommAlgCat.of k k
  let m : scalarGroupPoints R P.pair.G.val ⟶ scalarGroupPoints R P.pair.G.val :=
    Functor.whiskerLeft (Under.forget R) ((groupPointsFunctor k).map a.group.hom)
  have hm := scalarRigidity P R m (fun S t => htorus S.right t)
    (fun S i b => by
      change rootPoint ((P.pin i).val.hom ≫ (P.roots i.val).val.inclusion) S.right b ≫
        a.group.hom.hom.hom = _
      rw [← rootPoint_comp, Category.assoc, hpin])
  have hg : a.group.hom = 𝟙 _ := by
    apply Grp.hom_ext
    apply hom_ext_on_affine_tests
    intro S p
    let z : Under R := Under.mk (CommAlgCat.ofHom (Algebra.ofId k S))
    exact DFunLike.congr_fun (congrArg GrpCat.Hom.hom (NatTrans.congr_app hm z)) p
  have hg' : f.group.hom = g.group.hom := by
    have h' : f.group.hom ≫ g.group.inv = 𝟙 _ := hg
    calc
      f.group.hom = (f.group.hom ≫ g.group.inv) ≫ g.group.hom := by simp
      _ = g.group.hom := by rw [h', Category.id_comp]
  apply PinnedIso.ext
  · exact Iso.ext hg'
  · exact ht
  · apply Iso.ext
    apply Grp.hom_ext
    haveI : IsClosedImmersion Q.pair.B.inclusion.hom.hom.left := Q.pair.B.isClosedImmersion
    haveI : Mono Q.pair.B.inclusion.hom.hom := Over.mono_of_mono_left _
    apply (cancel_mono Q.pair.B.inclusion.hom.hom).mp
    change (f.borel.hom ≫ Q.pair.B.inclusion).hom.hom =
      (g.borel.hom ≫ Q.pair.B.inclusion).hom.hom
    rw [← f.borel_comm, ← g.borel_comm, hg']

theorem basedDatumFunctorFaithful : BasedDatumFunctorFaithful.{u} := by
  intro k _ A D F hObj hF
  constructor
  intro P Q f g h
  apply pinnedIsoUniqueness f g
  intro χ
  have h₁ := hF P Q f χ
  have h₂ := hF P Q g χ
  rw [h] at h₁
  exact Additive.ofMul.injective (h₁.symm.trans h₂)

/-- The functor defined on the shared pinned groupoid is faithful. -/
theorem faithfulBasedDatumFunctor (A : AdditiveLine k) :
    (LinearAlgebraicGroups.Classification.Pinning.basedDatumFunctor A).Faithful :=
  basedDatumFunctorFaithful A
    (fun P => LinearAlgebraicGroups.Classification.Pinning.attachedDatum P.pair)
    (LinearAlgebraicGroups.Classification.Pinning.basedDatumFunctor A)
    (fun _ => rfl) (fun _ _ _ _ => rfl)

end

end LinearAlgebraicGroups.Classification.PinnedUniqueness
