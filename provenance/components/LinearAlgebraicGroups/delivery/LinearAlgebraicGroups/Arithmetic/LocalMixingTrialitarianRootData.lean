import Specs.LinearAlgebraicGroups.Arithmetic.LocalMixingTrialitarianRootData
import LinearAlgebraicGroups.Arithmetic.TrialitarianRelativeRoots
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj InnerProductSpace TensorProduct

universe u

namespace LinearAlgebraicGroups.Arithmetic.LocalMixingTrialitarianRootData

open _root_.LinearAlgebraicGroups.Specs
open Specs.Arithmetic.LocalMixingTrialitarianRootData
open Specs.Arithmetic.RelativeRootIrreducibility (RealCharacters RealRootSpan realCharacter realRoot)
open Specs.Arithmetic.TrialitarianRelativeRoots (project longCoordinates Folding IsRestriction)
open Specs.CharacterDescent (Character)
open Specs.CharacterPairing (absoluteRoots pairing)
open Specs.GeometricRadicals (IsReductive)
open Specs.Relative.MaximalSplitTori (IsMaximalSplitTorus)
open Specs.Relative.RelativeChambers (relativeRoots)
open Specs.Relative.RelativeReflections (Datum)
open Specs.Relative.RelativeWeylScheme (QuotientData)
open LieAlgebrasAndRepresentations (rankTwoCoefficients)

set_option linter.style.haveILetI false

open private relativeForm relative_cartan realRoot_ne_zero from
  LinearAlgebraicGroups.Arithmetic.RelativeRootIrreducibility

noncomputable section

private abbrev coordinates := rankTwoCoefficients .G₂

private theorem coordinates_collinear :
    ∀ p q : ↥coordinates, p.val.1 * q.val.2 = p.val.2 * q.val.1 →
      q.val = p.val ∨ q.val = -p.val := by
  decide +kernel

private theorem reduced_of_coordinates {F : Type u} [Field F] {G : AffineAlgebraicGroup F}
    {S : ClosedSubgroup G.val} (coord : (ℤ × ℤ) →+ Additive (Character S.group))
    (hinj : Function.Injective coord)
    (hroots : relativeRoots S = (fun p => (coord p).toMul) '' (coordinates : Set (ℤ × ℤ))) :
    HasReducedRoots S := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩ ⟨m, n, hm, _, hmn⟩
  rw [hroots] at ha hb
  obtain ⟨p, hp, rfl⟩ := ha
  obtain ⟨q, hq, rfl⟩ := hb
  have h : m • p = n • q := by
    apply hinj
    rw [map_zsmul, map_zsmul]
    exact congrArg Additive.ofMul hmn
  have h₁ : m * p.1 = n * q.1 := congrArg Prod.fst h
  have h₂ : m * p.2 = n * q.2 := congrArg Prod.snd h
  have he : m * (p.1 * q.2 - p.2 * q.1) = 0 := by
    calc
      _ = (m * p.1) * q.2 - (m * p.2) * q.1 := by ring
      _ = 0 := by rw [h₁, h₂]; ring
  have hd := sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hm)
  rcases coordinates_collinear ⟨p, hp⟩ ⟨q, hq⟩ hd with heq | hneg
  · exact Or.inl (congrArg (fun x => (coord x).toMul) heq)
  · change q = -p at hneg
    exact Or.inr (by change (coord q).toMul = (coord p).toMul⁻¹; rw [hneg, map_neg]; rfl)

section Length

variable {F : Type u} [Field F] {G : AffineAlgebraicGroup F} {S : ClosedSubgroup G.val}
variable (coord : (ℤ × ℤ) →+ Additive (Character S.group))
variable (hroots : relativeRoots S = (fun p => (coord p).toMul) '' (coordinates : Set (ℤ × ℤ)))

private def coordinateRoot (p : ℤ × ℤ) (hp : p ∈ coordinates) : relativeRoots S :=
  ⟨(coord p).toMul, hroots.symm ▸ ⟨p, hp, rfl⟩⟩

private theorem coordinate_decompose (p : ℤ × ℤ) :
    coord p = p.1 • coord (1, 0) + p.2 • coord (0, 1) := by
  have hp : p = p.1 • ((1, 0) : ℤ × ℤ) + p.2 • ((0, 1) : ℤ × ℤ) := by
    ext <;> simp
  conv_lhs => rw [hp]
  simp only [map_add, map_zsmul]

private theorem pairing_coordinate {D : QuotientData S} [IsCommMonObj S.group.X]
    (d : Datum D) (r : relativeRoots S) (p : ℤ × ℤ) :
    pairing S.group (coord p).toMul (d.reflection r).coroot =
      p.1 * pairing S.group (coord (1, 0)).toMul (d.reflection r).coroot +
        p.2 * pairing S.group (coord (0, 1)).toMul (d.reflection r).coroot := by
  let f := d.rootDatum.toLinearMap
  let y := Additive.ofMul (d.reflection r).coroot
  simp only [← d.pairing_eq]
  change f (coord p) y = p.1 * f (coord (1, 0)) y + p.2 * f (coord (0, 1)) y
  rw [coordinate_decompose coord p, map_add, map_smul, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.smul_apply, zsmul_eq_mul, zsmul_eq_mul]
  rfl

private theorem reflected_coordinate {D : QuotientData S} [IsCommMonObj S.group.X]
    (d : Datum D) (hinj : Function.Injective coord) {p q : ℤ × ℤ}
    (hp : p ∈ coordinates) (hq : q ∈ coordinates) :
    p - pairing S.group (coord p).toMul (d.reflection (coordinateRoot coord hroots q hq)).coroot • q
      ∈ coordinates := by
  let a := coordinateRoot coord hroots q hq
  let b := coordinateRoot coord hroots p hp
  let r := d.normalizerPerm (d.reflection a).label b
  have hr : r.val ∈ (fun p => (coord p).toMul) '' (coordinates : Set (ℤ × ℤ)) :=
    hroots ▸ r.property
  obtain ⟨v, hv, hvr⟩ := hr
  have he : v = p - pairing S.group b.val (d.reflection a).coroot • q := by
    apply hinj
    rw [map_sub, map_zsmul]
    have h := hvr.trans ((d.rootAction (d.reflection a).label b).trans
      ((d.reflection a).characterFormula b.val))
    rw [sub_eq_add_neg, ← neg_smul]
    exact congrArg Additive.ofMul h
  exact he ▸ hv

private theorem simple_cartan {D : QuotientData S} [IsCommMonObj S.group.X]
    (d : Datum D) (hinj : Function.Injective coord) :
    let a := coordinateRoot coord hroots (1, 0) (by decide +kernel)
    let b := coordinateRoot coord hroots (0, 1) (by decide +kernel)
    pairing S.group a.val (d.reflection b).coroot = -1 ∧
      pairing S.group b.val (d.reflection a).coroot = -3 := by
  let a := coordinateRoot coord hroots (1, 0) (by decide +kernel)
  let b := coordinateRoot coord hroots (0, 1) (by decide +kernel)
  let x := pairing S.group a.val (d.reflection b).coroot
  let y := pairing S.group b.val (d.reflection a).coroot
  have ha : pairing S.group (coord (1, 0)).toMul (d.reflection a).coroot = 2 :=
    (d.reflection a).rootPairing
  have hb : pairing S.group (coord (0, 1)).toMul (d.reflection b).coroot = 2 :=
    (d.reflection b).rootPairing
  have h31 := reflected_coordinate coord hroots d hinj
    (p := (3, 1)) (q := (0, 1)) (by decide +kernel) (by decide +kernel)
  have h32 := reflected_coordinate coord hroots d hinj
    (p := (3, 2)) (q := (0, 1)) (by decide +kernel) (by decide +kernel)
  have h01 := reflected_coordinate coord hroots d hinj
    (p := (0, 1)) (q := (1, 0)) (by decide +kernel) (by decide +kernel)
  have h31' := reflected_coordinate coord hroots d hinj
    (p := (3, 1)) (q := (1, 0)) (by decide +kernel) (by decide +kernel)
  change _ - pairing S.group _ (d.reflection b).coroot • ((0, 1) : ℤ × ℤ) ∈ _ at h31 h32
  change _ - pairing S.group _ (d.reflection a).coroot • ((1, 0) : ℤ × ℤ) ∈ _ at h01 h31'
  rw [pairing_coordinate coord d b (3, 1), hb] at h31
  rw [pairing_coordinate coord d b (3, 2), hb] at h32
  rw [pairing_coordinate coord d a (3, 1), ha] at h31'
  change ((3, 1) - (3 * x + 1 * 2) • (0, 1) : ℤ × ℤ) ∈ coordinates at h31
  change ((3, 2) - (3 * x + 2 * 2) • (0, 1) : ℤ × ℤ) ∈ coordinates at h32
  change ((0, 1) - y • (1, 0) : ℤ × ℤ) ∈ coordinates at h01
  change ((3, 1) - (3 * 2 + 1 * y) • (1, 0) : ℤ × ℤ) ∈ coordinates at h31'
  have h₁ : (3, 1 - (3 * x + 2)) ∈ coordinates := by simpa using h31
  have h₂ : (3, 2 - (3 * x + 4)) ∈ coordinates := by simpa using h32
  have h₃ : (-y, 1) ∈ coordinates := by simpa using h01
  have h₄ : (3 - (6 + y), 1) ∈ coordinates := by simpa using h31'
  simp [rankTwoCoefficients] at h₁ h₂ h₃ h₄
  change x = -1 ∧ y = -3
  exact ⟨by omega, by omega⟩

attribute [local instance] InnerProductSpace.Core.toNormedAddCommGroup

private theorem realRoot_coordinate {a b r : relativeRoots S} {p : ℤ × ℤ}
    (ha : a.val = (coord (1, 0)).toMul) (hb : b.val = (coord (0, 1)).toMul)
    (hr : r.val = (coord p).toMul) :
    realRoot r = (p.1 : ℝ) • realRoot a + (p.2 : ℝ) • realRoot b := by
  apply Subtype.ext
  let f : Additive (Character S.group) →ₗ[ℤ] RealCharacters S :=
    TensorProduct.mk ℤ ℝ _ 1
  change f (Additive.ofMul r.val) =
    (p.1 : ℝ) • f (Additive.ofMul a.val) + (p.2 : ℝ) • f (Additive.ofMul b.val)
  rw [hr, ha, hb, Int.cast_smul_eq_zsmul ℝ, Int.cast_smul_eq_zsmul ℝ]
  change f (coord p) = p.1 • f (coord (1, 0)) + p.2 • f (coord (0, 1))
  rw [coordinate_decompose coord p, map_add, map_zsmul, map_zsmul]

private theorem norm_of_coordinate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b : E) (hLength : inner ℝ b b = 3 * inner ℝ a a)
    (hAngle : 2 * inner ℝ a b = -inner ℝ b b) (p : ℤ × ℤ) (hp : p ∈ coordinates) :
    ‖(p.1 : ℝ) • a + (p.2 : ℝ) • b‖ ≤ ‖b‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_comm a b]
  have hn : 0 ≤ inner ℝ a a := real_inner_self_nonneg
  simp only [rankTwoCoefficients, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num only [Prod.fst, Prod.snd, Int.cast_zero, Int.cast_one, Int.cast_ofNat, Int.cast_neg] <;>
    linarith

private theorem longest_of_coordinates (hG : IsReductive G) (hS : IsMaximalSplitTorus S)
    (hinj : Function.Injective coord) :
    IsLongest S (coordinateRoot coord hroots (0, 1) (by decide +kernel)) := by
  obtain ⟨D, _⟩ := Relative.RelativeWeylScheme.finiteConstantQuotient G hG S hS
  obtain ⟨comm, hd⟩ := Relative.RelativeReflections.relativeRootDatum G hG S hS D
  letI := comm
  obtain ⟨d⟩ := hd
  letI := relativeForm d
  letI := InnerProductSpace.ofCore (relativeForm d).toCore
  refine ⟨D, comm, d, relativeForm d, fun b r => relative_cartan d r b, ?_⟩
  let a := coordinateRoot coord hroots (1, 0) (by decide +kernel)
  let b := coordinateRoot coord hroots (0, 1) (by decide +kernel)
  change ∀ r : relativeRoots S, ‖realRoot r‖ ≤ ‖realRoot b‖
  obtain ⟨h₁, h₂⟩ := simple_cartan coord hroots d hinj
  have hc₁ := relative_cartan d b a
  have hc₂ := relative_cartan d a b
  change pairing S.group a.val (d.reflection b).coroot = -1 at h₁
  change pairing S.group b.val (d.reflection a).coroot = -3 at h₂
  rw [h₁, Int.cast_neg, Int.cast_one] at hc₁
  rw [h₂, Int.cast_neg, Int.cast_ofNat] at hc₂
  haveI := d.freeCharacters
  have hn₁ : inner ℝ (realRoot b) (realRoot b) ≠ 0 :=
    inner_self_ne_zero.mpr (realRoot_ne_zero b)
  have hn₂ : inner ℝ (realRoot a) (realRoot a) ≠ 0 :=
    inner_self_ne_zero.mpr (realRoot_ne_zero a)
  have hAngle : 2 * inner ℝ (realRoot a) (realRoot b) = -inner ℝ (realRoot b) (realRoot b) := by
    have h := (div_eq_iff hn₁).mp hc₁
    linarith
  have hLength : inner ℝ (realRoot b) (realRoot b) = 3 * inner ℝ (realRoot a) (realRoot a) := by
    have h := (div_eq_iff hn₂).mp hc₂
    rw [real_inner_comm (realRoot a) (realRoot b)] at h
    linarith
  rintro ⟨χ, hχ⟩
  rw [hroots] at hχ
  obtain ⟨p, hp, he⟩ := hχ
  rw [realRoot_coordinate coord (a := a) (b := b) rfl rfl he.symm]
  exact norm_of_coordinate _ _ hLength hAngle p hp

end Length

section Transport

open Specs.AdjointRepresentation (GroupPoints constants dualMap scale)
open Specs.CharacterPairing (adjointWeightVectors characterValue)
open Specs.GeometricBorelConjugacy (subgroupOfSubgroup)
open Specs.GeometricRadicals (baseChangedSubgroup)
open Specs.QuasiSplitOrbitLevis (MultiplicativeComparison)
open private charactersOfIso from LinearAlgebraicGroups.RootData.CharacterPairing
open private innerIso innerMap comp_innerMap from LinearAlgebraicGroups.Reductive.BorelProper
open private transportSubgroup from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private maximalTransport from LinearAlgebraicGroups.Classification.PinnedEquivalence
open private groupBaseChange_injective from LinearAlgebraicGroups.Arithmetic.QuasiSplitFixedWeyl

variable {F : Type u} [Field F]

set_option backward.isDefEq.respectTransparency false in
private theorem absoluteRoot_of_square {G H : GroupScheme F} {T : ClosedSubgroup G}
    {U : ClosedSubgroup H} (g : G ≅ H) (e : T.group ≅ U.group)
    (h : e.hom ≫ U.inclusion = T.inclusion ≫ g.hom)
    {χ : Character T.group} (hχ : χ ∈ absoluteRoots T) :
    e.inv ≫ χ ∈ absoluteRoots U := by
  obtain ⟨hn, v, hv, hv₀⟩ := hχ
  refine ⟨?_, mapPointKernel g.hom v, ?_, ?_⟩
  · intro he
    apply hn
    apply (charactersOfIso e).injective
    exact he.trans (map_one (charactersOfIso e)).symm
  · intro R t
    let s : GroupPoints T.group R := t ≫ e.inv.hom.hom
    let d := g.hom.hom.hom
    have ht : s ≫ T.inclusion.hom.hom ≫ d = t ≫ U.inclusion.hom.hom := by
      have hh : e.inv ≫ T.inclusion ≫ g.hom = U.inclusion := by
        rw [← h, Iso.inv_hom_id_assoc]
      simpa only [s, d, Grp.comp_hom_hom, Category.assoc] using
        congrArg (fun j : U.group ⟶ H => t ≫ j.hom.hom) hh
    have hχ : characterValue (e.inv ≫ χ) R t = characterValue χ R s := by
      unfold characterValue
      simp only [s, Grp.comp_hom_hom, Category.assoc]
    let a := dualMap (CommAlgCat.ofHom (Algebra.ofId F R))
    let z := mapPoints (constants R) (s ≫ T.inclusion.hom.hom)
    let p := mapPoints a v.toMul.val
    change mapPoints (constants R) (t ≫ U.inclusion.hom.hom) *
        mapPoints a (v.toMul.val ≫ d) *
        (mapPoints (constants R) (t ≫ U.inclusion.hom.hom))⁻¹ =
      mapPoints (scale R (characterValue (e.inv ≫ χ) R t)) (mapPoints a (v.toMul.val ≫ d))
    rw [hχ, ← ht]
    change (z ≫ d) * (p ≫ d) * (z ≫ d)⁻¹ =
      mapPoints (scale R (characterValue χ R s)) p ≫ d
    have he := congrArg (fun p => p ≫ d) (hv R s)
    change (z * p * z⁻¹) ≫ d = _ at he
    simpa only [d, MonObj.mul_comp, GrpObj.inv_comp] using he
  · intro he
    apply hv₀
    have hh := congrArg (fun z : Lie F H => z.toMul.val) he
    change v.toMul.val ≫ g.hom.hom.hom = 1 at hh
    rw [← MonObj.one_comp g.hom.hom.hom] at hh
    exact Additive.toMul.injective (Subtype.ext ((cancel_mono g.hom.hom.hom).mp hh))

private theorem absoluteRoot_iff_of_square {G H : GroupScheme F} {T : ClosedSubgroup G}
    {U : ClosedSubgroup H} (g : G ≅ H) (e : T.group ≅ U.group)
    (h : e.hom ≫ U.inclusion = T.inclusion ≫ g.hom) (χ : Character T.group) :
    e.inv ≫ χ ∈ absoluteRoots U ↔ χ ∈ absoluteRoots T := by
  refine ⟨fun hχ => ?_, absoluteRoot_of_square g e h⟩
  have h' : e.inv ≫ T.inclusion = U.inclusion ≫ g.inv := by
    apply (cancel_mono g.hom).mp
    simp only [Category.assoc, g.inv_hom_id, Category.comp_id, ← h, e.inv_hom_id_assoc]
  simpa using absoluteRoot_of_square g.symm e.symm h' hχ

private theorem transported_coordinates {G : AffineAlgebraicGroup F}
    {S₀ S : ClosedSubgroup G.val} (g : G.val ≅ G.val) (e : S₀.group ≅ S.group)
    (he : e.hom ≫ S.inclusion = S₀.inclusion ≫ g.hom)
    (coord : (ℤ × ℤ) →+ Additive (Character S₀.group))
    (hroots : relativeRoots S₀ = (fun p => (coord p).toMul) '' (coordinates : Set (ℤ × ℤ))) :
    relativeRoots S =
      (fun p => (((charactersOfIso e).toAdditive.toAddMonoidHom.comp coord) p).toMul) ''
        (coordinates : Set (ℤ × ℤ)) := by
  ext χ
  let χ₀ := e.hom ≫ χ
  have hχ : e.inv ≫ χ₀ = χ := e.inv_hom_id_assoc χ
  rw [← hχ]
  change e.inv ≫ χ₀ ∈ absoluteRoots S ↔ _
  rw [absoluteRoot_iff_of_square g e he χ₀]
  change χ₀ ∈ relativeRoots S₀ ↔ _
  rw [hroots]
  constructor
  · rintro ⟨p, hp, hpχ⟩
    exact ⟨p, hp, congrArg (fun a : Character S₀.group => e.inv ≫ a) hpχ⟩
  · rintro ⟨p, hp, hpχ⟩
    exact ⟨p, hp, (cancel_epi e.inv).mp hpχ⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 500000 in
private theorem transported_singleton {G : AffineAlgebraicGroup F}
    {M : Specs.QuasiSplitPinnedPairModel.BorelPair G}
    {S₀ : ClosedSubgroup M.torus.group} {S : ClosedSubgroup G.val}
    (g : G.val ≅ G.val) (e : S₀.group ≅ S.group)
    (he : e.hom ≫ S.inclusion = (subgroupOfSubgroup M.torus S₀).inclusion ≫ g.hom)
    {K : Type u} [Field K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    (P : Specs.Arithmetic.TrialitarianRelativeRoots.AbsolutePair K M)
    (t : MultiplicativeComparison F K)
    (ht : Specs.Arithmetic.QuasiSplitFixedWeyl.IsUnitComparison t)
    (restrict : Character P.pair.T.group →* Character S₀.group)
    (hres : IsRestriction S₀ t restrict)
    (a : Character S₀.group) (ha : ∃! β : AbstractPairing.Root P.pair.T, restrict β.val = a) :
    HasSingleAbsoluteRoot S (e.inv ≫ a) := by
  let E := groupBaseChange F K
  let T := transportSubgroup g M.torus
  let i : S.group ⟶ T.group := e.inv ≫ S₀.inclusion
  have hi : i ≫ T.inclusion = S.inclusion := by
    change e.inv ≫ S₀.inclusion ≫ M.torus.inclusion ≫ g.hom = S.inclusion
    rw [← Category.assoc S₀.inclusion, ← Category.assoc e.inv, Category.assoc e.inv,
      show S₀.inclusion ≫ M.torus.inclusion = (subgroupOfSubgroup M.torus S₀).inclusion from rfl,
      ← he, e.inv_hom_id_assoc]
  have hTK : E.map T.inclusion = P.pair.T.inclusion ≫ E.map g.hom :=
    E.map_comp M.torus.inclusion g.hom
  have hclosed : IsClosedImmersion (E.map T.inclusion).hom.hom.left := by
    rw [hTK]
    letI : IsClosedImmersion P.pair.T.inclusion.hom.hom.left := P.torusClosed
    letI : IsIso (E.map g.hom).hom.hom.left :=
      (Grp.forget (SchemeOver K) ⋙ Over.forget _).map_isIso (E.map g.hom)
    exact inferInstanceAs (IsClosedImmersion
      (P.pair.T.inclusion.hom.hom.left ≫ (E.map g.hom).hom.hom.left))
  let TK := baseChangedSubgroup K T hclosed
  have hroots (χ : Character P.pair.T.group) :
      χ ∈ absoluteRoots TK ↔ χ ∈ absoluteRoots P.pair.T := by
    have h := absoluteRoot_iff_of_square (E.mapIso g) (T := P.pair.T) (U := TK)
      (Iso.refl _) (by
        change 𝟙 _ ≫ E.map T.inclusion = P.pair.T.inclusion ≫ E.map g.hom
        rw [Category.id_comp, hTK]) χ
    change (𝟙 P.pair.T.group ≫ χ) ∈ absoluteRoots TK ↔ χ ∈ absoluteRoots P.pair.T at h
    erw [Category.id_comp] at h
    exact h
  have hrestrict_eq (χ : Character P.pair.T.group) :
      E.map i ≫ χ = E.map (e.inv ≫ a) ≫ t.inv ↔ restrict χ = a := by
    have hh₀ : E.map (restrict χ) = E.map S₀.inclusion ≫ χ ≫ t.hom := hres χ
    have hh : E.map S₀.inclusion ≫ χ = E.map (restrict χ) ≫ t.inv := by
      calc
        _ = (E.map S₀.inclusion ≫ χ ≫ t.hom) ≫ t.inv := by
          simp only [Category.assoc, t.hom_inv_id, Category.comp_id]
        _ = _ := congrArg (fun f => f ≫ t.inv) hh₀.symm
    have heq : E.map i ≫ χ = E.map (e.inv ≫ restrict χ) ≫ t.inv := by
      simpa only [i, E.map_comp, Category.assoc] using
        congrArg (fun f => E.map e.inv ≫ f) hh
    rw [heq]
    constructor
    · intro h
      exact (cancel_epi e.inv).mp
        (groupBaseChange_injective (F := F) (K := K) ((cancel_mono t.inv).mp h))
    · rintro rfl
      rfl
  refine ⟨T, i, M.isTorus, maximalTransport g M.torus M.maximal, hi,
    K, inferInstance, inferInstance, inferInstance, inferInstance, hclosed, t,
    ⟨P.reductive, P.pair.T, P.split, P.maximal⟩, P.split, ht, ?_⟩
  obtain ⟨β, hβ, hunique⟩ := ha
  refine ⟨β.val, ⟨(hroots β.val).mpr β.property, (hrestrict_eq β.val).mpr hβ⟩, ?_⟩
  rintro χ ⟨hχ, hχeq⟩
  exact congrArg Subtype.val (hunique ⟨χ, (hroots χ).mp hχ⟩ ((hrestrict_eq χ).mp hχeq))

end Transport

open Specs.GeometricBorelConjugacy (subgroupOfSubgroup)
open private charactersOfIso from LinearAlgebraicGroups.RootData.CharacterPairing
open private innerIso innerMap comp_innerMap from LinearAlgebraicGroups.Reductive.BorelProper

set_option backward.isDefEq.respectTransparency false in
/-- A quasi-split trialitarian group has reduced relative roots and a longest
root with one absolute root above it for every maximal split torus. -/
theorem trialitarianRootData : Statement.{u} := by
  intro F _ _ _ _ G hG hsc htrial hqs S hS
  obtain ⟨M, V, _, hV, K, _, _, _, _, P, D, data⟩ :=
    TrialitarianRelativeRoots.trialitarianRelativeRoots F G hG.1 hsc htrial hqs
  letI := D.comm
  obtain ⟨A, U, pin, simple, ω, t, ht, _, _, _, _, _, restrict, coeff, coord, hres, hfold, _⟩ :=
    data
  rcases hfold with ⟨_, hcoord, _, hinj, _, hrel, _, hproj, _, _, _, _, _, _, hlong⟩
  let V₀ := subgroupOfSubgroup M.torus V
  obtain ⟨g, e, he⟩ := Relative.MaximalSplitTori.maximalSplitToriConjugate G hqs.1 V₀ S hV hS
  let g' := innerIso g
  have he' : e.hom ≫ S.inclusion = V₀.inclusion ≫ g'.hom := by
    apply Grp.hom_ext
    change (e.hom ≫ S.inclusion).hom.hom = V₀.inclusion.hom.hom ≫ (innerMap g).hom.hom
    rw [comp_innerMap]
    exact he
  have hroots : relativeRoots V₀ =
      (fun p => (coord p).toMul) '' (coordinates : Set (ℤ × ℤ)) := by
    rw [← hproj, hrel]
    ext χ
    constructor
    · rintro ⟨β, rfl⟩
      exact ⟨project (coeff β), ⟨β, rfl⟩, congrArg Additive.toMul (hcoord β)⟩
    · rintro ⟨_, ⟨β, rfl⟩, rfl⟩
      exact ⟨β, (congrArg Additive.toMul (hcoord β)).symm⟩
  let c := (charactersOfIso e).toAdditive.toAddMonoidHom.comp coord
  have hc : Function.Injective c := (charactersOfIso e).toAdditive.injective.comp hinj
  have hr := transported_coordinates g' e he' coord hroots
  let a := coordinateRoot c hr (0, 1) (by decide +kernel)
  refine ⟨reduced_of_coordinates c hc hr, a, longest_of_coordinates c hr hqs.1 hS hc, ?_⟩
  have ha : ∃! β : AbstractPairing.Root P.pair.T, restrict β.val = (coord (0, 1)).toMul := by
    have hf (β : AbstractPairing.Root P.pair.T) :
        restrict β.val = (coord (0, 1)).toMul ↔ project (coeff β) = (0, 1) := by
      have hβ : (coord (project (coeff β))).toMul = restrict β.val :=
        congrArg Additive.toMul (hcoord β)
      rw [← hβ]
      exact (Additive.toMul.injective.comp hinj).eq_iff
    have h01 : ((0, 1) : ℤ × ℤ) ∈ longCoordinates := by decide +kernel
    obtain ⟨β, hβ, hβu⟩ := hlong (0, 1) h01
    exact ⟨β, (hf β).mpr hβ, fun δ hδ => hβu δ ((hf δ).mp hδ)⟩
  exact transported_singleton g' e he' P t ht restrict hres _ ha

end

end LinearAlgebraicGroups.Arithmetic.LocalMixingTrialitarianRootData
