import Specs.LinearAlgebraicGroups.Arithmetic.ComplexToralInvolutions
import LinearAlgebraicGroups.Flag.ProjectiveFlags
import LinearAlgebraicGroups.Reductive.MaximalToriConjugate
import LinearAlgebraicGroups.RootData.OrderedRootProducts
import LinearAlgebraicGroups.Solvable.GeometricTorusSplitting
import LinearAlgebraicGroups.Reductive.RadicalBaseChange
import LinearAlgebraicGroups.Reductive.DiagonalizableFixedLocus
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.Group
import Mathlib.RingTheory.Filtration

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CartesianMonoidalCategory
open _root_.Specs.AdvCommAlg.Differentials.Tangent (PointLifts)
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj

namespace LinearAlgebraicGroups.Arithmetic.ComplexToralInvolutions

open _root_.LinearAlgebraicGroups.Specs
open Specs.Pinning (SplitBorelPair)
open Specs.Unipotent (IsFppfGroupQuotient ClosedSeries closedSubgroupAlgebraicGroup)
open Specs.EquivariantUnipotentSeries (GroupPoints onPoints)

open private closedPoint_lift from LinearAlgebraicGroups.Flag.ProjectiveFlags
open private affineBaseTerminal from LinearAlgebraicGroups.Solvable.SplitFixedPoint
open private schemeKernel_sections from LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private kBorel_smooth_connected maximalTorus_of_geometricallyMaximal
  connected_of_geometricallyConnected from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private restrictSubgroup compose_restrict local_maximal_of_ambient solvable_maximal_torus_iff
  from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private solvable_baseChange_iff from LinearAlgebraicGroups.Reductive.RadicalBaseChange
open private lattice_torus_of_split from LinearAlgebraicGroups.RootData.RankOneFlag
open private exists_regular_cocharacter centralizer_of_regular
  from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private cocharacterPoint_postcompose affinePointEquiv_lifts affinePointEquiv_postcomp
  from LinearAlgebraicGroups.RootData.OrderedRootProducts
open private affinePointEquiv from LinearAlgebraicGroups.Reductive.CocharacterSmoothAndUnipotent
open private smooth_spec_iff from LinearAlgebraicGroups.Reductive.DiagonalizableFixedLocus
open private affine_subgroup from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private splitTorusSmooth from LinearAlgebraicGroups.Reductive.WeylScheme
open private smoothConnectedGroup_integral from LinearAlgebraicGroups.RootData.BorelsAndChambers

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

universe u

private abbrev rationalAlgebra (k : Type u) [Field k] : TestAlgebra k := CommAlgCat.of k k

private abbrev RationalPoint {k : Type u} [Field k] (G : GroupScheme k) :=
  GroupPoints G (rationalAlgebra k)

private abbrev rationalMap {k : Type u} [Field k] {G H : GroupScheme k} (f : G ⟶ H) :
    RationalPoint G →* RationalPoint H :=
  onPoints f (rationalAlgebra k)

private def rationalSourceIso (k : Type u) [Field k] :
    (testSpec k).obj (op (rationalAlgebra k)) ≅ 𝟙_ (SchemeOver k) :=
  (affineBaseTerminal k).uniqueUpToIso isTerminalTensorUnit

private theorem rational_precompose {k : Type u} [Field k] {X : SchemeOver k}
    (p q : 𝟙_ (SchemeOver k) ⟶ X)
    (h : p.left (IsLocalRing.closedPoint k) = q.left (IsLocalRing.closedPoint k))
    [LocallyOfFiniteType X.hom] [IsAlgClosed k] : p = q := by
  apply Over.OverMorphism.ext
  exact ext_of_apply_closedPoint_eq X.hom (Over.w p) (Over.w q) h

private theorem sections_surjective {k : Type u} [Field k] [IsAlgClosed k]
    {X Y : SchemeOver k} (q : X ⟶ Y) [Surjective q.left]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] :
    Function.Surjective (fun p : 𝟙_ (SchemeOver k) ⟶ X => p ≫ q) := by
  intro y
  let yy := (pointEquivClosedPoint Y.hom) ⟨y.left, Over.w y⟩
  obtain ⟨x, hx⟩ := closedPoint_lift q yy.property
  exact ⟨x, rational_precompose _ _ hx⟩

private theorem quotient_points_surjective {k : Type u} [Field k] [IsAlgClosed k]
    {G H : AffineAlgebraicGroup k} {N : ClosedSubgroup G.val} {p : G.val ⟶ H.val}
    (hp : IsFppfGroupQuotient N p) : Function.Surjective (rationalMap p) := by
  letI := hp.2.2.1
  letI := G.property.2.1
  letI := H.property.2.1
  let e := rationalSourceIso k
  intro y
  obtain ⟨x, hx⟩ := sections_surjective p.hom.hom (e.inv ≫ y)
  change x ≫ p.hom.hom = e.inv ≫ y at hx
  exact ⟨e.hom ≫ x, by
    change (e.hom ≫ x) ≫ p.hom.hom = y
    rw [Category.assoc, hx, Iso.hom_inv_id_assoc]⟩

private theorem closed_points_injective {k : Type u} [Field k] {G H : GroupScheme k}
    (i : G ⟶ H) (hi : IsClosedImmersion i.hom.hom.left) :
    Function.Injective (rationalMap i) := by
  letI := hi
  haveI : Mono i.hom.hom := Over.mono_of_mono_left _
  exact fun _ _ h => (cancel_mono i.hom.hom).mp h

private theorem onPoints_comp {k : Type u} [Field k] {G H J : GroupScheme k}
    (i : G ⟶ H) (j : H ⟶ J) (g : RationalPoint G) :
    rationalMap (i ≫ j) g = rationalMap j (rationalMap i g) := by
  change g ≫ i.hom.hom ≫ j.hom.hom = (g ≫ i.hom.hom) ≫ j.hom.hom
  exact (Category.assoc _ _ _).symm

private def rationalIso {k : Type u} [Field k] {G H : GroupScheme k} (e : G ≅ H) :
    RationalPoint G ≃* RationalPoint H :=
  (((groupPointsFunctor k).mapIso e).app (rationalAlgebra k)).groupIsoToMulEquiv

private theorem additive_square_bijective (k : Type u) [Field k] [CharZero k] :
    Function.Bijective (fun x : Multiplicative k => x * x) := by
  constructor
  · intro x y h
    apply Multiplicative.toAdd.injective
    have hh := congrArg Multiplicative.toAdd h
    change x.toAdd + x.toAdd = y.toAdd + y.toAdd at hh
    exact mul_left_cancel₀ (two_ne_zero (α := k)) (by simpa only [two_mul] using hh)
  · intro x
    refine ⟨Multiplicative.ofAdd (x.toAdd / 2), Multiplicative.toAdd.injective ?_⟩
    change x.toAdd / 2 + x.toAdd / 2 = x.toAdd
    ring

/-- Squaring is bijective along a central series with additive quotients in characteristic zero.
At each step, conjugation is trivial on the quotient, so correcting a square only
requires solving for the correction in that additive quotient. -/
private theorem series_square_bijective {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {U : AffineAlgebraicGroup k} {n : ℕ} (S : ClosedSeries U n)
    (hc : S.IsCentral)
    (hfactor : ∀ i < n, ∃ (Q : AffineAlgebraicGroup k) (q : (S.term i).val ⟶ Q.val),
      IsFppfGroupQuotient ⟨_, S.step i, S.closed i⟩ q ∧
      Nonempty ((groupPointsFunctor k).obj Q.val ≅ StandardGroups.additivePoints k)) :
    Function.Bijective (fun x : RationalPoint U.val => x * x) := by
  have hinj (j : ℕ) : Function.Injective (rationalMap (S.inclusion j)) := by
    induction j with
    | zero => exact (rationalIso S.top).injective
    | succ j hj =>
      intro a b hab
      change rationalMap (S.step j ≫ S.inclusion j) a =
        rationalMap (S.step j ≫ S.inclusion j) b at hab
      rw [onPoints_comp, onPoints_comp] at hab
      exact closed_points_injective _ (S.closed j) (hj hab)
  let j (i : ℕ) := rationalMap (S.inclusion i)
  have step (i : ℕ) (z : RationalPoint (S.term (i + 1)).val) :
      j i (rationalMap (S.step i) z) = j (i + 1) z :=
    (onPoints_comp (S.step i) (S.inclusion i) z).symm
  have square (i : ℕ) (hi : i < n) (a : RationalPoint U.val)
      (w : RationalPoint (S.term i).val) :
      ∃ z : RationalPoint (S.term (i + 1)).val,
        (a * j i w) * (a * j i w) =
          (a * a) * j i (rationalMap (S.step i) z * (w * w)) := by
    obtain ⟨z, hz⟩ := hc i hi (rationalAlgebra k) a⁻¹ w
    change j (i + 1) z = a⁻¹ * j i w * (a⁻¹)⁻¹ * (j i w)⁻¹ at hz
    refine ⟨z, ?_⟩
    rw [map_mul, map_mul, step, hz, inv_inv]
    group
  have trivial (z : RationalPoint (S.term n).val) : j n z = 1 := by
    haveI : Subsingleton (RationalPoint (Grp.trivial (SchemeOver k))) :=
      ⟨isTerminalTensorUnit.hom_ext⟩
    have hz : z = 1 := (rationalIso S.bottom).injective (Subsingleton.elim _ _)
    rw [hz, map_one]
  have factors (i : ℕ) (hi : i < n) :
      ∃ (Q : AffineAlgebraicGroup k) (q : (S.term i).val ⟶ Q.val),
        Function.Surjective (rationalMap q) ∧
        (∀ w, rationalMap q w = 1 ↔ ∃ v, rationalMap (S.step i) v = w) ∧
        (Function.Bijective fun b : RationalPoint Q.val => b * b) := by
    obtain ⟨Q, q, hq, ⟨e⟩⟩ := hfactor i hi
    let f : RationalPoint Q.val ≃* Multiplicative k :=
      (e.app (rationalAlgebra k)).groupIsoToMulEquiv
    refine ⟨Q, q, quotient_points_surjective hq, fun w => (schemeKernel_sections hq.1 w).symm,
      ?_, ?_⟩
    · intro x y h
      apply f.injective
      exact (additive_square_bijective k).injective
        (by simpa only [← map_mul] using congrArg f h)
    · intro x
      obtain ⟨y, hy⟩ := (additive_square_bijective k).surjective (f x)
      refine ⟨f.symm y, f.injective ?_⟩
      simpa only [map_mul, MulEquiv.apply_symm_apply] using hy
  constructor
  · intro a b hab
    change a * a = b * b at hab
    have liftDifference : ∀ i ≤ n, ∃ w : RationalPoint (S.term i).val, b = a * j i w := by
      intro i hi
      induction i with
      | zero =>
        obtain ⟨w, hw⟩ := (rationalIso S.top).surjective (a⁻¹ * b)
        change j 0 w = a⁻¹ * b at hw
        refine ⟨w, ?_⟩
        rw [hw, mul_inv_cancel_left]
      | succ i ih =>
        have hi' : i < n := hi
        obtain ⟨w, hw⟩ := ih hi'.le
        obtain ⟨z, hz⟩ := square i hi' a w
        obtain ⟨Q, q, _, hker, hsq⟩ := factors i hi'
        rw [hw, hz] at hab
        have hprod : rationalMap (S.step i) z * (w * w) = 1 :=
          hinj i ((mul_left_cancel (hab.symm.trans (mul_one (a * a)).symm)).trans
            (map_one _).symm)
        have hzq := (hker _).mpr ⟨z, rfl⟩
        have hww : rationalMap q w * rationalMap q w = 1 := by
          simpa only [map_mul, hzq, one_mul, map_one] using congrArg (rationalMap q) hprod
        have hwq : rationalMap q w = 1 := hsq.injective (by simpa using hww)
        obtain ⟨v, hv⟩ := (hker w).mp hwq
        exact ⟨v, by rw [hw, ← step, hv]⟩
    obtain ⟨w, hw⟩ := liftDifference n le_rfl
    simpa only [trivial w, mul_one] using hw.symm
  · intro x
    have approximate : ∀ i ≤ n,
        ∃ (a : RationalPoint U.val) (w : RationalPoint (S.term i).val),
          x = (a * a) * j i w := by
      intro i hi
      induction i with
      | zero =>
        obtain ⟨w, hw⟩ := (rationalIso S.top).surjective x
        change j 0 w = x at hw
        exact ⟨1, w, by rw [hw, one_mul, one_mul]⟩
      | succ i ih =>
        have hi' : i < n := hi
        obtain ⟨a, w, hw⟩ := ih hi'.le
        obtain ⟨Q, q, hsurj, hker, hsq⟩ := factors i hi'
        obtain ⟨b, hb⟩ := hsq.surjective (rationalMap q w)
        obtain ⟨v, hv⟩ := hsurj b
        obtain ⟨z, hz⟩ := square i hi' a v
        let d := rationalMap (S.step i) z * (v * v)
        have hzq := (hker _).mpr ⟨z, rfl⟩
        have hdq : rationalMap q d = rationalMap q w := by
          simp only [d, map_mul, hzq, one_mul, hv, hb]
        obtain ⟨s, hs⟩ := (hker (d⁻¹ * w)).mp (by simp [hdq])
        refine ⟨a * j i v, s, ?_⟩
        rw [hw, hz, ← step, hs]
        change _ = (a * a) * j i d * j i (d⁻¹ * w)
        rw [mul_assoc (a * a), ← map_mul, mul_inv_cancel_left]
    obtain ⟨a, w, hw⟩ := approximate n le_rfl
    exact ⟨a, by simpa only [trivial w, mul_one] using hw.symm⟩

/-- The square-one elements of a Borel are conjugate into its specified maximal torus. -/
private theorem borel_square_one_conjugate (P : SplitBorelPair ℂ)
    (x : RationalPoint P.B.group) (hx : x * x = 1) :
    ∃ (b : RationalPoint P.B.group) (t : RationalPoint P.T.group),
      rationalMap P.B.inclusion (b * x * b⁻¹) = rationalMap P.T.inclusion t := by
  let B := closedSubgroupAlgebraicGroup (G := P.G) P.B
  change RationalPoint B.val at x
  change x * x = 1 at hx
  obtain ⟨hs, hc⟩ := kBorel_smooth_connected P.G P.B P.borel
  have hsolvable : Specs.SchemeDerivedGroup.IsSolvable B.val := by
    obtain ⟨_, hg⟩ := P.borel
    exact (solvable_baseChange_iff (K := AlgebraicClosure ℂ) B hs hc).mp hg.1.2.2
  obtain ⟨U, D, p, hU, hp, _, _, hT⟩ := GeometricTorusSplitting.splitting B hs hc hsolvable
  obtain ⟨j, hj⟩ := P.containsTorus
  let T : ClosedSubgroup B.val := restrictSubgroup P.T P.B j hj
  have hm := maximalTorus_of_geometricallyMaximal P.G P.T
    (lattice_torus_of_split P.split) P.maximal
  have hm' : Specs.GeometricTorusSplitting.IsMaximalTorus T := by
    apply (solvable_maximal_torus_iff B T).mpr
    apply local_maximal_of_ambient P.B T
    rwa [compose_restrict]
  letI : IsIso (T.inclusion ≫ p) := (hT T).1.mp hm'
  let E := rationalIso (asIso (T.inclusion ≫ p))
  let F := rationalMap p
  let J := rationalMap T.inclusion
  let I := rationalMap U.inclusion
  have hE (t : RationalPoint P.T.group) : E t = F (J t) :=
    onPoints_comp T.inclusion p t
  obtain ⟨t, ht⟩ := E.surjective (F x)
  have htx : F (J t) = F x := (hE t).symm.trans ht
  have ht₂ : J t * J t = 1 := by
    have ht' : t * t = 1 := by
      apply E.injective
      rw [map_mul, ht, ← map_mul, hx, map_one, map_one]
    rw [← map_mul, ht', map_one]
  have hker (a : RationalPoint B.val) : F a = 1 ↔ ∃ u, I u = a :=
    (schemeKernel_sections hp.1 a).symm
  obtain ⟨u, hu⟩ := (hker (x * (J t)⁻¹)).mp (by simp [htx])
  have hxu : x = I u * J t := by rw [hu, inv_mul_cancel_right]
  obtain ⟨n, S, hcentral, _, hfactors⟩ :=
    Unipotent.perfectFieldSplitness (closedSubgroupAlgebraicGroup U) hU.1 hU.2.1 hU.2.2.2.1
  have hsq := series_square_bijective S hcentral hfactors
  obtain ⟨v, hv⟩ := hsq.surjective u
  change RationalPoint U.group at v
  change v * v = u at hv
  have hvq : F (I v) = 1 := (hker _).mpr ⟨v, rfl⟩
  obtain ⟨w, hw⟩ := (hker (J t * I v * (J t)⁻¹)).mp (by simp [hvq])
  have hconj : J t * I u * (J t)⁻¹ = (I u)⁻¹ := by
    have htinv : (J t)⁻¹ = J t := inv_eq_of_mul_eq_one_right ht₂
    rw [htinv]
    apply eq_inv_of_mul_eq_one_left
    calc
      J t * I u * J t * I u = J t * (x * x) * (J t)⁻¹ := by rw [hxu]; group
      _ = 1 := by simp [hx]
  have hw' : w = v⁻¹ := by
    apply hsq.injective
    change w * w = v⁻¹ * v⁻¹
    apply closed_points_injective U.inclusion U.isClosedImmersion
    change I (w * w) = I (v⁻¹ * v⁻¹)
    rw [map_mul, hw]
    calc
      _ = J t * (I v * I v) * (J t)⁻¹ := by group
      _ = (I u)⁻¹ := by rw [← map_mul, hv, hconj]
      _ = I (v⁻¹ * v⁻¹) := by rw [← hv, ← mul_inv_rev, map_inv]
  have hop : J t * I v = (I v)⁻¹ * J t := by
    have heq := hw.symm.trans (by rw [hw', map_inv])
    rw [← heq]
    group
  have hb : (I v)⁻¹ * x * ((I v)⁻¹)⁻¹ = J t := by
    rw [hxu, ← hv, map_mul, inv_inv, ← mul_assoc, inv_mul_cancel_left,
      mul_assoc, hop, ← mul_assoc, mul_inv_cancel, one_mul]
  refine ⟨(I v)⁻¹, t, ?_⟩
  rw [hb]
  change rationalMap P.B.inclusion (rationalMap j t) = _
  rw [← onPoints_comp, hj]

/-- The conjugation map from the product with the fixed torus. -/
private def conjugationMap (P : SplitBorelPair ℂ) :
    P.G.val.X ⊗ P.T.group.X ⟶ P.G.val.X :=
  (fst _ _) * (snd _ _ ≫ P.T.inclusion.hom.hom) * (fst _ _)⁻¹

/-- Properness of the flag scheme turns density of torus conjugates into
the existence of a fixed flag for every point. -/
private theorem conjugate_into_borel_of_dominant (P : SplitBorelPair ℂ)
    (hdense : IsDominant (conjugationMap P).left) (x : RationalPoint P.G.val) :
    ∃ (g : RationalPoint P.G.val) (b : RationalPoint P.B.group),
      g⁻¹ * x * g = rationalMap P.B.inclusion b := by
  letI := P.G.property.2.1
  have hpar : BorelProper.IsParabolic P.G P.B := by
    obtain ⟨h, hb⟩ := P.borel
    exact ⟨P.reductive, (kBorel_smooth_connected P.G P.B P.borel).1,
      h, _, hb, ⟨𝟙 _, Category.id_comp _⟩⟩
  let Q := (ProjectiveFlags.smoothProjectiveQuotient ℂ P.G P.B hpar).1.some
  obtain ⟨_, hproper, V, _, _, _, a, line, b, j, hjclosed, horbit, hequiv, hj, hstab, _⟩ :=
    (ProjectiveFlags.smoothProjectiveQuotient ℂ P.G P.B hpar).2 Q
  letI := hproper
  letI := hjclosed
  letI := b
  letI := a
  let Y := Q.scheme
  let G := P.G.val.X
  let T := P.T.group.X
  let e : 𝟙_ (SchemeOver ℂ) ⟶ Y := η[G] ≫ Q.projection
  have hq : Q.projection = Specs.SmoothOrbit.orbitMap b e := by
    letI : ModObj G G := ModObj.regular G
    letI : IsModHom G Q.projection := ⟨hequiv⟩
    change Q.projection = (𝟙 G : G ⟶ G) • (toUnit G ≫ e)
    rw [show toUnit G ≫ e = (1 : G ⟶ G) ≫ Q.projection from (Category.assoc _ _ _).symm,
      ← IsModHom.map_smul]
    have h : (𝟙 G : G ⟶ G) • (1 : G ⟶ G) = 𝟙 G := by
      change lift (𝟙 G) (1 : G ⟶ G) ≫ μ[G] = 𝟙 G
      rw [← CategoryTheory.Hom.mul_def, mul_one]
    rw [h, Category.id_comp]
  have he : e ≫ j = line := by
    rw [show e = η[G] ≫ Q.projection from rfl, Category.assoc, horbit]
    change η[G] ≫ ((𝟙 G : G ⟶ G) • (toUnit G ≫ line)) = line
    rw [ModObj.comp_smul, Category.comp_id, ← Category.assoc,
      toUnit_unique (η[G] ≫ toUnit G) (𝟙 _), Category.id_comp]
    change (1 : (𝟙_ (SchemeOver ℂ) ⟶ G)) • line = line
    exact one_smul _ _
  letI : IsModHom G j := ⟨hj⟩
  have stabilizes (X : SchemeOver ℂ) (g : X ⟶ G) :
      g • (toUnit X ≫ e) = toUnit X ≫ e ↔
        ∃ s : X ⟶ P.B.group.X, s ≫ P.B.inclusion.hom.hom = g := by
    rw [← hstab]
    change _ ↔ g • (toUnit X ≫ line) = toUnit X ≫ line
    haveI : Mono j := Over.mono_of_mono_left _
    rw [← (cancel_mono j : _ ≫ j = _ ≫ j ↔ _), IsModHom.map_smul, Category.assoc, he]
  let f : G ⊗ Y ⟶ Y := b.smul
  let p : G ⊗ Y ⟶ Y := snd _ _
  let i : equalizer f p ⟶ G ⊗ Y := equalizer.ι f p
  let q : equalizer f p ⟶ G := i ≫ fst G Y
  haveI : IsClosedImmersion i.left := inferInstanceAs
    (IsClosedImmersion (equalizer.ι f p).left)
  haveI : IsProper (fst G Y).left := by dsimp [G, Y]; infer_instance
  haveI : IsProper q.left := by change IsProper (i.left ≫ (fst G Y).left); infer_instance
  haveI : LocallyOfFiniteType (equalizer f p).hom := by
    rw [← Over.w q]
    infer_instance
  let g : G ⊗ T ⟶ G := fst _ _
  let t : G ⊗ T ⟶ G := snd _ _ ≫ P.T.inclusion.hom.hom
  let y : G ⊗ T ⟶ Y := toUnit _ ≫ e
  have ht : t • y = y := by
    obtain ⟨jT, hjT⟩ := P.containsTorus
    apply (stabilizes _ _).mpr
    exact ⟨snd _ _ ≫ jT.hom.hom, by
      rw [Category.assoc]
      exact congrArg (fun m : P.T.group ⟶ P.G.val => snd G T ≫ m.hom.hom) hjT⟩
  have hfix : lift (conjugationMap P) (g • y) ≫ f =
      lift (conjugationMap P) (g • y) ≫ p := by
    change (g * t * g⁻¹) • (g • y) = lift (conjugationMap P) (g • y) ≫ snd _ _
    rw [lift_snd, ← mul_smul, mul_assoc (g * t), inv_mul_cancel, mul_one, mul_smul, ht]
  let c := equalizer.lift _ hfix
  have hc : c ≫ q = conjugationMap P := by
    change (c ≫ i) ≫ fst G Y = _
    rw [equalizer.lift_ι, lift_fst]
  have hclosed : IsClosed (Set.range q.left) := by
    rw [← Set.image_univ]
    exact q.left.isClosedMap _ isClosed_univ
  have hsur : Set.range (conjugationMap P).left ⊆ Set.range q.left := by
    intro z hz
    obtain ⟨w, rfl⟩ := hz
    exact ⟨c.left w, by
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hc]⟩
  haveI : Surjective q.left := ⟨fun z => hclosed.closure_subset_iff.mpr hsur
    (hdense.denseRange z)⟩
  let R := (testSpec ℂ).obj (op (rationalAlgebra ℂ))
  let xx : R ⟶ G := x
  let r := rationalSourceIso ℂ
  obtain ⟨v, hv⟩ := sections_surjective q (r.inv ≫ xx)
  change v ≫ q = r.inv ≫ xx at hv
  let m := r.hom ≫ v ≫ i
  let z := m ≫ snd G Y
  have hx : m ≫ fst G Y = xx := by
    change r.hom ≫ v ≫ q = xx
    rw [hv, Iso.hom_inv_id_assoc]
  have hz : xx • z = z := by
    have hm : m ≫ f = m ≫ p := by
      simp only [m, Category.assoc]
      rw [show i ≫ f = i ≫ p from equalizer.condition f p]
    rw [← hx]
    change lift (m ≫ fst G Y) (m ≫ snd G Y) ≫ f = z
    rw [← comp_lift, lift_fst_snd, Category.comp_id]
    exact hm
  letI := Q.surjective
  obtain ⟨gs, hgs⟩ := sections_surjective Q.projection (r.inv ≫ z)
  change gs ≫ Q.projection = r.inv ≫ z at hgs
  let g₀ : R ⟶ G := r.hom ≫ gs
  have hgz : g₀ • (toUnit R ≫ e) = z := by
    have hgz' : g₀ ≫ Q.projection = z := by
      change (r.hom ≫ gs) ≫ Q.projection = z
      rw [Category.assoc, hgs, Iso.hom_inv_id_assoc]
    rw [hq] at hgz'
    change g₀ ≫ ((𝟙 G : G ⟶ G) • (toUnit G ≫ e)) = z at hgz'
    rwa [ModObj.comp_smul, Category.comp_id, ← Category.assoc, comp_toUnit] at hgz'
  have hcc : (g₀⁻¹ * xx * g₀) • (toUnit R ≫ e) = toUnit R ≫ e := by
    rw [mul_smul, mul_smul, hgz, hz, ← hgz, ← mul_smul, inv_mul_cancel, one_smul]
  obtain ⟨b₀, hb₀⟩ := (stabilizes _ _).mp hcc
  exact ⟨g₀, b₀, hb₀.symm⟩

private abbrev complexBase := rationalAlgebra ℂ

private abbrev complexDual := CommAlgCat.of ℂ (DualNumber ℂ)

private abbrev constantLift (G : GroupScheme ℂ) :=
  (((groupPointsFunctor ℂ).obj G).map (Specs.AdjointRepresentation.constants complexBase)).hom

private theorem reduce_constant (G : GroupScheme ℂ) (t : RationalPoint G) :
    reduceTangentPoints G (constantLift G t) = t := by
  let F := (groupPointsFunctor ℂ).obj G
  change (F.map (dualReduction ℂ)).hom ((F.map _).hom t) = t
  have he : Specs.AdjointRepresentation.constants complexBase ≫ dualReduction ℂ =
      𝟙 complexBase := by
    apply CommAlgCat.hom_ext
    ext
  rw [← GrpCat.comp_apply, ← F.map_comp, he, F.map_id]
  rfl

open Specs.AdjointRepresentation (RelativeTangent conjugate)
open LinearAlgebraicGroups.CocharacterDynamics

/-- The differential of conjugation from the product with the torus is
surjective at the identity and a point on a regular cocharacter. -/
private theorem conjugationMap_lifts (P : SplitBorelPair ℂ) :
    ∃ t : RationalPoint P.T.group,
    ∀ v : GroupPoints P.G.val complexDual,
      reduceTangentPoints P.G.val v = rationalMap P.T.inclusion t →
      ∃ w : Points (P.G.val.X ⊗ P.T.group.X) complexDual,
        mapPoints (dualReduction ℂ) w = lift (1 : RationalPoint P.G.val) t ∧
        w ≫ conjugationMap P = v := by
  classical
  obtain ⟨c, hc⟩ := exists_regular_cocharacter P.G P.T P.split
  let cochar := c ≫ P.T.inclusion
  obtain ⟨D⟩ := existsLimitDecomposition P.G cochar
  obtain ⟨j, hj⟩ := (centralizer_of_regular P.G P.reductive P.T P.split P.maximal c hc D).1
  let s := identityLieStructure P.G
  letI := s.lieRing
  letI := s.lieAlgebra
  obtain ⟨W⟩ := existsAdjointWeightBasis P.G cochar s
  let a : ℝˣ := Units.mk0 2 (by norm_num)
  let b : ℂˣ := Units.map Complex.ofRealHom.toMonoidHom a
  let t := cocharacterPoint c complexBase b
  let tG := rationalMap P.T.inclusion t
  have htG : tG = cocharacterPoint cochar complexBase b :=
    (cocharacterPoint_postcompose c P.T.inclusion complexBase b).symm
  refine ⟨t, fun v hv => ?_⟩
  let C := constantLift P.G.val tG
  let x : RelativeTangent P.G.val complexBase :=
    ⟨v * C⁻¹, by
      change reduceTangentPoints P.G.val (v * C⁻¹) = 1
      rw [map_mul, map_inv, reduce_constant, hv, mul_inv_cancel]⟩
  let L := W.coordinates.equiv complexBase
  let A := L.symm x
  let q (i : ULift (Fin W.dimension)) : ℂ := ↑(b ^ W.weight i)
  have hn (i : ULift (Fin W.dimension)) (hi : W.weight i ≠ 0) : 1 - q i ≠ 0 := by
    intro h
    have hval : (b : ℂ) = Complex.ofReal (a : ℝ) := rfl
    have hval' : q i = Complex.ofReal ((2 : ℝ) ^ W.weight i) := by
      change (↑(b ^ W.weight i) : ℂ) = _
      rw [Units.val_zpow_eq_zpow_val, hval, Complex.ofReal_zpow]
      rfl
    have he : (2 : ℝ) ^ W.weight i = 1 := by
      apply Complex.ofReal_injective
      simpa only [← hval', Complex.ofReal_one] using (sub_eq_zero.mp h).symm
    exact hi (zpow_right_injective₀ (by norm_num : (0 : ℝ) < 2) (by norm_num)
      (he.trans (zpow_zero _).symm))
  let a₁ (i : ULift (Fin W.dimension)) : ℂ :=
    if W.weight i = 0 then 0 else A i / (1 - q i)
  let a₀ (i : ULift (Fin W.dimension)) : ℂ :=
    if W.weight i = 0 then A i else 0
  let d := L a₁
  have ha₀ : L a₀ ∈ relativeLieImage D.centralizer complexBase :=
    ((relativeLieWeights P.G cochar D s W complexBase a₀).2.2).mpr (by
      intro i hi
      exact ite_eq_right hi)
  obtain ⟨z, hz⟩ := ha₀
  let zT := mapPointKernel j z
  have hzT : onPoints P.T.inclusion complexDual zT.toMul.val = (L a₀).toMul.val := by
    have he := congrArg (fun f : D.centralizer.group ⟶ P.G.val =>
      onPoints f complexDual z.toMul.val) hj
    change (z.toMul.val ≫ j.hom.hom) ≫ P.T.inclusion.hom.hom = _
    exact (Category.assoc _ _ _).trans (he.trans hz)
  have hd : (L (fun i => q i * a₁ i)).toMul.val = C * d.toMul.val * C⁻¹ := by
    have h := W.diagonal complexBase b a₁
    change _ = conjugate (cocharacterPoint cochar complexBase b) d at h
    rw [← htG] at h
    exact h
  have hA : a₁ + a₀ - (fun i => q i * a₁ i) = A := by
    funext i
    change a₁ i + a₀ i - q i * a₁ i = A i
    by_cases hi : W.weight i = 0
    · simp [a₁, a₀, hi]
    · simp only [a₁, a₀, ite_eq_right hi, add_zero]
      calc
        _ = (1 - q i) * (A i / (1 - q i)) := by ring
        _ = A i := mul_div_cancel₀ _ (hn i hi)
  have hcalc : d.toMul.val * (L a₀).toMul.val * (C * d.toMul.val * C⁻¹)⁻¹ =
      v * C⁻¹ := by
    have he : L a₁ + L a₀ - L (fun i => q i * a₁ i) = x := by
      rw [← L.map_add, ← L.map_sub, hA]
      exact L.apply_symm_apply x
    have h := congrArg (fun y : RelativeTangent P.G.val complexBase => y.toMul.val) he
    change d.toMul.val * (L a₀).toMul.val * ((L _).toMul.val)⁻¹ = _ at h
    rwa [hd] at h
  refine ⟨lift d.toMul.val (zT.toMul.val * constantLift P.T.group t), ?_, ?_⟩
  · change (testSpec ℂ).map (dualReduction ℂ).op ≫ lift _ _ = _
    rw [comp_lift]
    change lift (reduceTangentPoints P.G.val d.toMul.val)
      (reduceTangentPoints P.T.group (zT.toMul.val * constantLift P.T.group t)) = _
    rw [d.toMul.property, map_mul, zT.toMul.property, reduce_constant, one_mul]
  · change _ ≫ ((fst _ _) * (snd _ _ ≫ P.T.inclusion.hom.hom) * (fst _ _)⁻¹) = _
    simp only [MonObj.comp_mul, GrpObj.comp_inv, lift_fst, lift_snd_assoc]
    change d.toMul.val * onPoints P.T.inclusion complexDual
      (zT.toMul.val * constantLift P.T.group t) * d.toMul.val⁻¹ = v
    have hnatur := congrArg (fun f => (GrpCat.Hom.hom f) t)
      (((groupPointsFunctor ℂ).map P.T.inclusion).naturality
        (Specs.AdjointRepresentation.constants complexBase))
    change onPoints P.T.inclusion complexDual (constantLift P.T.group t) = C at hnatur
    rw [map_mul, hzT, hnatur]
    calc
      _ = (d.toMul.val * (L a₀).toMul.val * (C * d.toMul.val * C⁻¹)⁻¹) * C := by group
      _ = v := by rw [hcalc, inv_mul_cancel_right]

section CotangentDominance

variable {k A B : Type u} [Field k] [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B]

private abbrev aug (e : A →ₐ[k] k) := RingHom.ker e.toRingHom

private def cotangentPart (e : A →ₐ[k] k) (a : A) : PointCotangent e :=
  (aug e).toCotangent ⟨a - algebraMap k A (e a), by simp [RingHom.mem_ker]⟩

private theorem cotangentPart_add (e : A →ₐ[k] k) (a b : A) :
    cotangentPart e (a + b) = cotangentPart e a + cotangentPart e b := by
  unfold cotangentPart
  rw [← map_add]
  congr 1
  apply Subtype.ext
  simp only [Submodule.coe_add, map_add]
  ring

private theorem cotangentPart_mul (e : A →ₐ[k] k) (a b : A) :
    cotangentPart e (a * b) = e a • cotangentPart e b + e b • cotangentPart e a := by
  let I := aug e
  let x : I := ⟨a - algebraMap k A (e a), by simp [I, RingHom.mem_ker]⟩
  let y : I := ⟨b - algebraMap k A (e b), by simp [I, RingHom.mem_ker]⟩
  have he :
      (⟨a * b - algebraMap k A (e (a * b)), by simp [I, RingHom.mem_ker]⟩ : I) =
        (e a) • y + (e b) • x + x * y := by
    apply Subtype.ext
    simp only [Submodule.coe_add, Submodule.coe_smul_of_tower, Algebra.smul_def,
      x, y, map_mul]
    change _ = _ + _ + (a - algebraMap k A (e a)) * (b - algebraMap k A (e b))
    ring
  have hz : I.toCotangent (x * y) = 0 :=
    (I.toCotangent_eq_zero _).mpr (pow_two I ▸ Ideal.mul_mem_mul x.property y.property)
  change I.toCotangent _ = e a • I.toCotangent y + e b • I.toCotangent x
  rw [he, map_add, map_add, hz, add_zero]
  exact congrArg₂ (· + ·) ((I.toCotangent.restrictScalars k).map_smul (e a) y)
    ((I.toCotangent.restrictScalars k).map_smul (e b) x)

private theorem cotangentPart_algebraMap (e : A →ₐ[k] k) (a : k) :
    cotangentPart e (algebraMap k A a) = 0 := by
  unfold cotangentPart
  apply ((aug e).toCotangent_eq_zero _).mpr
  simp

private abbrev cotangentMap (f : A →ₐ[k] B) (e : B →ₐ[k] k) :=
  Ideal.mapCotangent (aug (e.comp f)) (aug e) f (fun _ h => h)

private theorem cotangentPart_comp (f : A →ₐ[k] B) (e : B →ₐ[k] k) (a : A) :
    cotangentPart e (f a) = cotangentMap f e (cotangentPart (e.comp f) a) := by
  unfold cotangentPart
  rw [Ideal.mapCotangent_toCotangent]
  congr 1
  apply Subtype.ext
  simp

/-- Split the cotangent map over the ground field to retract the first
infinitesimal neighborhood on coordinate rings. -/
private theorem firstOrderRetraction (f : A →ₐ[k] B) (e : B →ₐ[k] k)
    (hf : Function.Injective (cotangentMap f e)) :
    ∃ r : B →ₐ[k] A ⧸ (aug (e.comp f)) ^ 2,
      r.comp f = Ideal.Quotient.mkₐ k ((aug (e.comp f)) ^ 2) := by
  let I := aug (e.comp f)
  let m := Ideal.Quotient.mkₐ k (I ^ 2)
  obtain ⟨l, hl⟩ := (cotangentMap f e).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hf)
  let L := (I.cotangentToQuotientSquare.restrictScalars k).comp l
  have hzero (x y : PointCotangent e) : L x * L y = 0 := by
    obtain ⟨a, ha⟩ := I.toCotangent_surjective (l x)
    obtain ⟨b, hb⟩ := I.toCotangent_surjective (l y)
    change I.cotangentToQuotientSquare (l x) * I.cotangentToQuotientSquare (l y) = 0
    rw [← ha, ← hb, Ideal.toCotangent_to_quotient_square,
      Ideal.toCotangent_to_quotient_square]
    change m a * m b = 0
    rw [← map_mul]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [pow_two]
    exact Ideal.mul_mem_mul a.property b.property
  let r : B →ₐ[k] A ⧸ I ^ 2 :=
    { toFun := fun b => algebraMap k (A ⧸ I ^ 2) (e b) + L (cotangentPart e b)
      map_one' := by
        rw [map_one, map_one, show (1 : B) = algebraMap k B 1 from (map_one _).symm,
          cotangentPart_algebraMap, map_zero, add_zero]
      map_zero' := by
        rw [map_zero, map_zero, show (0 : B) = algebraMap k B 0 from (map_zero _).symm,
          cotangentPart_algebraMap, map_zero, add_zero]
      map_add' := fun x y => by
        simp only [map_add, cotangentPart_add]
        ring
      map_mul' := fun x y => by
        simp only [map_mul, cotangentPart_mul, map_add, map_smul, Algebra.smul_def]
        have hh := hzero (cotangentPart e x) (cotangentPart e y)
        linear_combination -hh
      commutes' := fun a => by
        simp [cotangentPart_algebraMap] }
  refine ⟨r, AlgHom.ext fun a => ?_⟩
  change algebraMap k (A ⧸ I ^ 2) (e (f a)) + L (cotangentPart e (f a)) = m a
  rw [cotangentPart_comp]
  have hl' := LinearMap.congr_fun hl (cotangentPart (e.comp f) a)
  change l (cotangentMap f e (cotangentPart (e.comp f) a)) = _ at hl'
  change _ + I.cotangentToQuotientSquare (l _) = _
  rw [hl', LinearMap.id_apply]
  unfold cotangentPart
  rw [Ideal.toCotangent_to_quotient_square]
  change m (algebraMap k A (e (f a))) +
    m (a - algebraMap k A (e (f a))) = m a
  rw [← map_add]
  exact congrArg m (by ring)

/-- Agreement with the identity modulo the square of the augmentation
ideal makes the error raise the entire ideal-power filtration. -/
private theorem lift_detects_aug_powers {e : A →ₐ[k] k} {n : ℕ} (hn : 2 ≤ n)
    (g : A →ₐ[k] A ⧸ (aug e) ^ n)
    (h : (Ideal.Quotient.factorₐ k (Ideal.pow_le_pow_right hn)).comp g =
      Ideal.Quotient.mkₐ k ((aug e) ^ 2)) :
    ∀ a, g a = 0 → a ∈ aug e ^ n := by
  let I := aug e
  let q := Ideal.Quotient.mkₐ k (I ^ n)
  let J := I.map q.toRingHom
  let d (a : A) := q a - g a
  have hJ (j : ℕ) : J ^ j = (I ^ j).map q.toRingHom := (Ideal.map_pow _ _ _).symm
  have hd (a : A) : d a ∈ J ^ 2 := by
    rw [hJ]
    obtain ⟨v, hv⟩ := Ideal.Quotient.mk_surjective (d a)
    change q v = d a at hv
    have hh := AlgHom.congr_fun h a
    change (Ideal.Quotient.factorₐ k (Ideal.pow_le_pow_right hn)) (g a) =
      Ideal.Quotient.mkₐ k (I ^ 2) a at hh
    have hv' : v ∈ I ^ 2 := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [← Ideal.Quotient.factorₐ_apply_mk k (Ideal.pow_le_pow_right hn)]
      change (Ideal.Quotient.factorₐ k (Ideal.pow_le_pow_right hn)) (q v) = 0
      rw [hv]
      change (Ideal.Quotient.factorₐ k (Ideal.pow_le_pow_right hn)) (q a - g a) = 0
      rw [map_sub, hh]
      exact sub_self _
    exact hv ▸ Ideal.mem_map_of_mem _ hv'
  have hmul (a b : A) : d (a * b) = q a * d b + d a * g b := by
    change q (a * b) - g (a * b) = _
    rw [map_mul, map_mul]
    unfold d
    ring
  have hhigh (j : ℕ) : ∀ a ∈ I ^ j, d a ∈ J ^ (j + 1) := by
    induction j with
    | zero => exact fun a _ => Ideal.pow_le_pow_right (by decide : 1 ≤ 2) (hd a)
    | succ j ih =>
      rw [pow_succ']
      intro a ha
      refine Submodule.mul_induction_on ha ?_ ?_
      · intro a ha b hb
        have hgb : g b ∈ J ^ j := by
          rw [show g b = q b - d b by dsimp [d]; ring]
          apply Ideal.sub_mem _ (hJ j ▸ Ideal.mem_map_of_mem _ hb)
          exact Ideal.pow_le_pow_right (Nat.le_succ _) (ih b hb)
        have h₁ : q a * d b ∈ J ^ (j + 1 + 1) := by
          rw [pow_succ']
          exact Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ ha) (ih b hb)
        have h₂ : d a * g b ∈ J ^ (j + 1 + 1) := by
          rw [show j + 1 + 1 = 2 + j by omega, pow_add]
          exact Ideal.mul_mem_mul (hd a) hgb
        rw [hmul]
        exact Ideal.add_mem _ h₁ h₂
      · intro x y hx hy
        change q (x + y) - g (x + y) ∈ _
        rw [map_add, map_add, add_sub_add_comm]
        exact Ideal.add_mem _ hx hy
  intro a ha
  have hmem : ∀ j ≤ n, a ∈ I ^ j := by
    intro j hj
    induction j with
    | zero => simp
    | succ j ih =>
      have hh := hhigh j a (ih (Nat.le_of_succ_le hj))
      change q a - g a ∈ J ^ (j + 1) at hh
      rw [ha, sub_zero, hJ] at hh
      have heq : ((I ^ (j + 1)).map q.toRingHom).comap q.toRingHom = I ^ (j + 1) := by
        change ((I ^ (j + 1)).map (Ideal.Quotient.mk (I ^ n))).comap
          (Ideal.Quotient.mk (I ^ n)) = _
        rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective,
          Ideal.mk_ker, sup_eq_left.mpr (Ideal.pow_le_pow_right hj)]
      exact heq ▸ hh
  exact hmem n le_rfl

/-- Formal smoothness lifts the first-order retraction to every finite
infinitesimal neighborhood. Krull intersection then detects the kernel. -/
private theorem injective_of_tangent_lifts [IsDomain A] [IsNoetherianRing A]
    [Algebra.FormallySmooth k B] (f : A →ₐ[k] B) (e : B →ₐ[k] k)
    (h : ∀ v : PointLifts k A k (e.comp f), ∃ w : PointLifts k B k e, w.val.comp f = v.val) :
    Function.Injective f := by
  have hI : Function.Injective (cotangentMap f e) := by
    obtain ⟨a, ha, _⟩ := pointTangentLifts k A (e.comp f)
    obtain ⟨b, hb, _⟩ := pointTangentLifts k B e
    apply LinearMap.dualMap_surjective_iff.mp
    intro v
    obtain ⟨w, hw⟩ := h (a v)
    refine ⟨b.symm w, ?_⟩
    apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := (aug (e.comp f)).toCotangent_surjective x
    let y : aug e := ⟨f x, x.property⟩
    have he := congrArg (fun l : A →ₐ[k] DualNumber k => (l x).snd) hw
    change (w.val (f x)).snd = ((a v).val x).snd at he
    rw [ha] at he
    have hh := hb (b.symm w) y
    rw [Equiv.apply_symm_apply] at hh
    exact hh.symm.trans he
  obtain ⟨r, hr⟩ := firstOrderRetraction f e hI
  let I := aug (e.comp f)
  apply (injective_iff_map_eq_zero f).mpr
  intro a ha
  have ha' : a ∈ ⨅ j : ℕ, I ^ j := by
    simp only [Ideal.mem_iInf]
    intro j
    let n := max 2 j
    have hn : 2 ≤ n := le_max_left _ _
    let q := Ideal.Quotient.factorₐ k (Ideal.pow_le_pow_right (I := I) hn)
    have hsurj : Function.Surjective q := by
      intro a
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      exact ⟨Ideal.Quotient.mk _ a, rfl⟩
    have hnil : IsNilpotent (RingHom.ker q.toRingHom) := by
      have hker : RingHom.ker q.toRingHom = (I ^ 2).map (Ideal.Quotient.mk (I ^ n)) := by
        let m := Ideal.Quotient.mk (I ^ n)
        have hmk : (RingHom.ker q.toRingHom).comap m = I ^ 2 := by
          ext a
          exact Ideal.Quotient.eq_zero_iff_mem
        calc
          _ = ((RingHom.ker q.toRingHom).comap m).map m :=
            (Ideal.map_comap_of_surjective m Ideal.Quotient.mk_surjective _).symm
          _ = _ := congrArg (Ideal.map m) hmk
      refine ⟨n, ?_⟩
      rw [hker, ← Ideal.map_pow, ← pow_mul]
      apply (Ideal.map_eq_bot_iff_le_ker _).mpr
      rw [Ideal.mk_ker]
      exact Ideal.pow_le_pow_right (by omega)
    let r' := Algebra.FormallySmooth.liftOfSurjective r q hsurj hnil
    have hr' : q.comp (r'.comp f) = Ideal.Quotient.mkₐ k (I ^ 2) := by
      rw [← AlgHom.comp_assoc]
      unfold r'
      rw [Algebra.FormallySmooth.comp_liftOfSurjective, hr]
    have hh : (r'.comp f) a = 0 := by change r' (f a) = 0; rw [ha, map_zero]
    exact Ideal.pow_le_pow_right (le_max_right 2 j) (lift_detects_aug_powers hn _ hr' a hh)
  rw [Ideal.iInf_pow_eq_bot_of_isDomain _ (RingHom.ker_ne_top _)] at ha'
  exact ha'

end CotangentDominance


/-- In an affine smooth source, lifts of every first-order direction at an
integral target give dominance. -/
private theorem dominant_of_tangent_lifts {k : Type u} [Field k]
    {X Y : SchemeOver k} (p : X ⟶ Y) [IsAffine X.left] [IsAffine Y.left]
    [Smooth X.hom] [IsIntegral Y.left] [LocallyOfFiniteType Y.hom]
    (x : Points X (rationalAlgebra k))
    (h : ∀ v : Points Y (CommAlgCat.of k (DualNumber k)),
      mapPoints (dualReduction k) v = x ≫ p →
      ∃ w : Points X (CommAlgCat.of k (DualNumber k)),
        mapPoints (dualReduction k) w = x ∧ w ≫ p = v) :
    IsDominant p.left := by
  obtain ⟨Aop, ⟨eY⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr
    (inferInstance : IsAffine Y.left)
  obtain ⟨Bop, ⟨eX⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr
    (inferInstance : IsAffine X.left)
  let A := Aop.unop
  let B := Bop.unop
  let F := algSpec.fullyFaithful (R := CommRingCat.of k)
  let m := (F.preimage (eX.hom ≫ p ≫ eY.inv)).unop
  let f := m.hom
  have hm : (testSpec k).map m.op ≫ eY.hom = eX.hom ≫ p := by
    change (testSpec k).map (F.preimage (eX.hom ≫ p ≫ eY.inv)) ≫ eY.hom = _
    rw [F.map_preimage]
    simp
  have hcomp {R : TestAlgebra k} (z : B →ₐ[k] R) :
      affinePointEquiv eX R z ≫ p = affinePointEquiv eY R (z.comp f) :=
    affinePointEquiv_postcomp eX eY p f hm z
  let e := (affinePointEquiv eX (rationalAlgebra k)).symm x
  have hB : affinePointEquiv eX (rationalAlgebra k) e = x :=
    (affinePointEquiv eX _).apply_symm_apply x
  have hA : affinePointEquiv eY (rationalAlgebra k) (e.comp f) = x ≫ p :=
    (hcomp e).symm.trans (by rw [hB])
  let b := affinePointEquiv_lifts eX hB
  let a := affinePointEquiv_lifts eY hA
  let eYr : ((testSpec k).obj (op A)).left ≅ Y.left := (Over.forget _).mapIso eY
  haveI : IsDomain A := (affine_isIntegral_iff (CommRingCat.of A)).mp
    (IsIntegral.of_isIso eYr.inv)
  haveI : Algebra.FiniteType k A := by
    apply RingHom.finiteType_algebraMap.mp
    apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)
      (φ := CommRingCat.ofHom (algebraMap k A))).mp
    change LocallyOfFiniteType (Over.hom ((testSpec k).obj (op A)))
    rw [← Over.w eY.hom]
    infer_instance
  letI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  haveI : Algebra.Smooth k B := by
    apply (smooth_spec_iff (k := k) (A := B)).mp
    change Smooth (Over.hom ((testSpec k).obj (op B)))
    rw [← Over.w eX.hom]
    infer_instance
  have hfinj : Function.Injective f := injective_of_tangent_lifts f e (by
    intro v
    obtain ⟨w, h₁, h₂⟩ := h (a v).val (a v).property
    let w' := b.symm ⟨w, h₁⟩
    refine ⟨w', (affinePointEquiv eY (CommAlgCat.of k (DualNumber k))).injective ?_⟩
    rw [← hcomp]
    have hw := congrArg Subtype.val (b.apply_symm_apply ⟨w, h₁⟩)
    change affinePointEquiv eX _ w'.val = w at hw
    rwa [hw])
  have hdom : IsDominant ((testSpec k).map m.op).left := by
    change IsDominant (Spec.map (CommRingCat.ofHom f.toRingHom))
    constructor
    apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr
    change RingHom.ker f.toRingHom ≤ nilradical A
    rw [(RingHom.injective_iff_ker_eq_bot f.toRingHom).mp hfinj]
    exact bot_le
  haveI : IsDominant ((testSpec k).map m.op).left := hdom
  have hh : IsDominant (((testSpec k).map m.op).left ≫ eY.hom.left) := inferInstance
  rw [← Over.comp_left, hm, Over.comp_left] at hh
  exact (MorphismProperty.cancel_left_of_respectsIso @IsDominant eX.hom.left p.left).mp hh

private theorem conjugationMap_dominant (P : SplitBorelPair ℂ) :
    IsDominant (conjugationMap P).left := by
  haveI : Smooth P.G.val.X.hom := P.reductive.1
  haveI : Smooth P.T.group.X.hom := splitTorusSmooth P.split
  haveI : IsIntegral P.G.val.X.left := smoothConnectedGroup_integral P.G P.reductive.1
    (connected_of_geometricallyConnected P.reductive.2.1)
  haveI : LocallyOfFiniteType P.G.val.X.hom := P.G.property.2.1
  haveI : IsAffine P.G.val.X.left := P.G.property.1
  haveI : IsAffine P.T.group.X.left := affine_subgroup P.G.property.1 P.T
  haveI : IsAffine (P.G.val.X ⊗ P.T.group.X).left := by
    change IsAffine (pullback P.G.val.X.hom P.T.group.X.hom)
    infer_instance
  haveI : Smooth (P.G.val.X ⊗ P.T.group.X).hom := by
    dsimp
    infer_instance
  obtain ⟨t, ht⟩ := conjugationMap_lifts P
  apply dominant_of_tangent_lifts (conjugationMap P) (lift (1 : RationalPoint P.G.val) t)
  intro v hv
  apply ht v
  change mapPoints (dualReduction ℂ) v =
    lift (1 : RationalPoint P.G.val) t ≫ conjugationMap P at hv
  have hbase : lift (1 : RationalPoint P.G.val) t ≫ conjugationMap P =
      (rationalMap P.T.inclusion t : Points P.G.val.X complexBase) := by
    change lift (1 : RationalPoint P.G.val) t ≫
      (fst _ _ * (snd _ _ ≫ P.T.inclusion.hom.hom) * (fst _ _)⁻¹) = _
    simp only [MonObj.comp_mul, GrpObj.comp_inv, lift_fst, lift_snd_assoc, inv_one, one_mul, mul_one]
    rfl
  exact hv.trans hbase

/-- Every square-one complex point is conjugate to a point of the fixed torus. -/
theorem toralInvolutions : Specs.ComplexToralInvolutions.ToralInvolutions := by
  intro P i x hx
  change RationalPoint P.G.val at x
  change x * x = 1 at hx
  obtain ⟨g, b, hgb⟩ := conjugate_into_borel_of_dominant P (conjugationMap_dominant P) x
  let I := rationalMap P.B.inclusion
  have hb : b * b = 1 := by
    apply closed_points_injective P.B.inclusion P.B.isClosedImmersion
    change I (b * b) = I 1
    rw [map_mul, map_one, ← hgb]
    calc
      _ = g⁻¹ * (x * x) * g := by group
      _ = 1 := by rw [hx, mul_one, inv_mul_cancel]
  obtain ⟨c, t, hct⟩ := borel_square_one_conjugate P b hb
  refine ⟨I c * g⁻¹, t, ?_⟩
  change (I c * g⁻¹) * x * (I c * g⁻¹)⁻¹ = rationalMap P.T.inclusion t
  calc
    _ = I c * (g⁻¹ * x * g) * (I c)⁻¹ := by group
    _ = I (c * b * c⁻¹) := by rw [hgb, map_mul, map_mul, map_inv]
    _ = _ := hct

end LinearAlgebraicGroups.Arithmetic.ComplexToralInvolutions
