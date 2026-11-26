import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.LocalBruhatTorusCommutator
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuasiSplitLocalGeneration
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RelativeReflections
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj Pointwise

universe u

namespace LinearAlgebraicGroups.Arithmetic.LocalBruhatTorusCommutator

open _root_.LinearAlgebraicGroups.Specs
open LocalAlgebraicTransport (RationalPoints)
open CocharacterDynamics (LimitDecomposition cocharacterPoint unitPoint HasLimit HasExtension
  orbit laurentAlgebra laurentParameter laurentConstants existsLimitDecomposition)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterDescent (Cocharacter)
open Specs.GeometricRadicals (IsReductive)
open Specs.Relative.MaximalSplitTori (IsMinimalParabolic IsMaximalSplitTorus)
open Specs.Relative.RelativeChambers (IsRegular)
open Specs.Relative.RelativeWeylScheme (QuotientData rationalProjection markedParabolic)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.SimpleParabolicProduct (doubleCoset)
open Specs.RankOneFlag (SameSubgroup)
open Specs.GeometricBorelConjugacy (ConjugatesSubgroups)

open private terminalPointHom terminalPointHom_surjective terminalSubgroup_mem
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuasiSplitLocalGeneration
open private quotientLabel_eq_of_projection conjugates_limitParabolics
  conjugates_iff_of_known_conjugate from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RelativeReflections
open private quotientLabel_conjugates comp_pointConj pointConj constantPoint
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.AbstractPairing
open private cocharacterPoint_postcompose from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.OrderedRootProducts
open private centralizes_onAlgebras from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private same_subgroup_of_same_affine_points
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag
open private constantRationalEquiv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RelativeWeylScheme

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {F : Type u} [Field F] {J : AffineAlgebraicGroup F}

private abbrev fieldPoints (B : ClosedSubgroup J.val) :=
  SubgroupSections B ((testSpec F).obj (op (CommAlgCat.of F F)))

private abbrev terminalToRational (G : GroupScheme F) :
    (𝟙_ (SchemeOver F) ⟶ G.X) →* RationalPoints G.X :=
  terminalPointHom G

private theorem outside_double_coset (hJ : IsReductive J)
    {S B : ClosedSubgroup J.val} (hS : IsMaximalSplitTorus S)
    (hB : IsMinimalParabolic J B) (hSB : IsSubgroupOf S B)
    {g : RationalPoints J.val.X} (hg : g ∉ fieldPoints B) :
    ∃ (Q : QuotientData S) (w : Q.splitImage.labels)
      (n : 𝟙_ (SchemeOver F) ⟶ Q.normalizer.group.X),
      w ≠ 1 ∧ rationalProjection Q n = Q.splitImage.constantGroup.sectionPoint w ∧
      ∃ (a : RationalPoints J.val.X) (_ : a ∈ fieldPoints B)
        (e : RationalPoints J.val.X) (_ : e ∈ fieldPoints B),
        g = a * terminalToRational J.val (n ≫ Q.normalizer.inclusion.hom.hom) * e := by
  classical
  obtain ⟨Q, _, _, _, hrep, hcover⟩ := Relative.RelativeBruhat.relativeBruhat J hJ S B hS hB hSB
  choose rep hrep using hrep
  let n (w : Q.splitImage.labels) := if w = 1 then 1 else rep w
  have hn (w) : rationalProjection Q (n w) = Q.splitImage.constantGroup.sectionPoint w := by
    by_cases hw : w = 1
    · subst w
      change rationalProjection Q (n 1) = constantRationalEquiv Q.splitImage.constantGroup 1
      rw [show n 1 = 1 by simp [n], map_one, map_one]
    · simpa only [n, ite_eq_right hw] using hrep w
  obtain ⟨x, hx⟩ := terminalPointHom_surjective J.val g
  have hcell : x ∈ ⋃ w, doubleCoset B (𝟙_ (SchemeOver F))
      (n w ≫ Q.normalizer.inclusion.hom.hom) :=
    (hcover n hn).1.symm ▸ Set.mem_univ _
  obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hcell
  obtain ⟨an, han, e, he, hxe⟩ := Set.mem_mul.mp hw
  obtain ⟨a, ha, y, hy, hay⟩ := Set.mem_mul.mp han
  have hy' : y = n w ≫ Q.normalizer.inclusion.hom.hom := by
    have hu : toUnit (𝟙_ (SchemeOver F)) = 𝟙 _ := Subsingleton.elim _ _
    simpa only [Set.mem_singleton_iff, hu, Category.id_comp] using hy
  let A := terminalToRational J.val
  have ha' : A a ∈ fieldPoints B := (terminalSubgroup_mem B a).mp ha
  have he' : A e ∈ fieldPoints B := (terminalSubgroup_mem B e).mp he
  have hfac : g = A a * A (n w ≫ Q.normalizer.inclusion.hom.hom) * A e := by
    have hx' : A x = g := hx
    rw [← hx', ← hxe, ← hay, hy', map_mul, map_mul]
  refine ⟨Q, w, n w, ?_, hn w, A a, ha', A e, he', hfac⟩
  intro h
  subst w
  have hn₁ : n 1 = 1 := by simp [n]
  apply hg
  rw [hfac, hn₁, MonObj.one_comp, map_one, mul_one]
  exact (fieldPoints B).mul_mem ha' he'

private theorem parabolic_limit (hJ : IsReductive J) {S : ClosedSubgroup J.val}
    (hS : IsMaximalSplitTorus S) (c : Cocharacter S.group) (hc : IsRegular S c)
    (D : LimitDecomposition (c ≫ S.inclusion)) {p : RationalPoints J.val.X}
    (hp : p ∈ fieldPoints D.parabolic) :
    ∃ z : RationalPoints J.val.X, HasLimit (c ≫ S.inclusion) p z ∧ Centralizes S.inclusion z := by
  let R := CommAlgCat.of F F
  obtain ⟨v, hv⟩ : ∃ v : GroupPoints D.parabolic.group R,
      ((groupPointsFunctor F).map D.parabolic.inclusion).app R v = p := hp
  let z : RationalPoints J.val.X :=
    ((groupPointsFunctor F).map (D.limit ≫ D.centralizer.inclusion)).app R v
  refine ⟨z, ?_, ?_⟩
  · rw [← hv]
    exact D.limit_points R v
  · apply (Relative.RelativeChambers.regularLevi J hJ S hS.1 c D hc _ z).mpr
    exact ⟨v ≫ D.limit.hom.hom, rfl⟩

private theorem difference_point {S : ClosedSubgroup J.val} [IsCommMonObj S.group.X]
    (c c' : Cocharacter S.group) (R : TestAlgebra F) (t : Rˣ) :
    cocharacterPoint ((c * (c')⁻¹) ≫ S.inclusion) R t =
      cocharacterPoint (c ≫ S.inclusion) R t * (cocharacterPoint (c' ≫ S.inclusion) R t)⁻¹ := by
  rw [cocharacterPoint_postcompose, cocharacterPoint_postcompose, cocharacterPoint_postcompose]
  change (unitPoint R t ≫ (c * (c')⁻¹).hom.hom) ≫ S.inclusion.hom.hom = _
  simp only [Grp.Hom.hom_mul, Mon.Hom.hom_mul, Grp.Hom.hom_hom_inv, MonObj.comp_mul,
    GrpObj.comp_inv, MonObj.mul_comp, GrpObj.inv_comp]
  rfl

private theorem torus_values_commute {S : ClosedSubgroup J.val} [IsCommMonObj S.group.X]
    (c d : Cocharacter S.group) (R : TestAlgebra F) (s t : Rˣ) :
    Commute (cocharacterPoint (c ≫ S.inclusion) R s) (cocharacterPoint (d ≫ S.inclusion) R t) := by
  rw [cocharacterPoint_postcompose, cocharacterPoint_postcompose]
  exact (Commute.all (show Points S.group.X R from cocharacterPoint c R s)
    (show Points S.group.X R from cocharacterPoint d R t)).map
      (IsMonHom.monoidHom S.inclusion.hom.hom _)

private theorem transported_point {S : ClosedSubgroup J.val} (Q : QuotientData S)
    (w : Q.splitImage.labels) (n : 𝟙_ (SchemeOver F) ⟶ Q.normalizer.group.X)
    (hn : rationalProjection Q n = Q.splitImage.constantGroup.sectionPoint w)
    (c : Cocharacter S.group) (t : Fˣ) :
    let b := terminalPointHom J.val (n ≫ Q.normalizer.inclusion.hom.hom)
    let R := CommAlgCat.of F F
    cocharacterPoint ((c ≫ (Q.splitImage.conjugation w).hom) ≫ S.inclusion) R t =
      b * cocharacterPoint (c ≫ S.inclusion) R t * b⁻¹ := by
  dsimp only
  let R := CommAlgCat.of F F
  let x := n ≫ Q.normalizer.inclusion.hom.hom
  have h := quotientLabel_conjugates Q.splitImage n
  rw [quotientLabel_eq_of_projection Q w n hn] at h
  rw [cocharacterPoint_postcompose, cocharacterPoint_postcompose, cocharacterPoint_postcompose]
  change (cocharacterPoint c R t ≫ (Q.splitImage.conjugation w).hom.hom.hom) ≫
      S.inclusion.hom.hom = _
  rw [Category.assoc]
  change cocharacterPoint c R t ≫ ((Q.splitImage.conjugation w).hom ≫ S.inclusion).hom.hom = _
  rw [h, comp_pointConj]
  let b : Points J.val.X R := terminalToRational J.val x
  let a : Points J.val.X R := cocharacterPoint c R t ≫ S.inclusion.hom.hom
  change pointConj x a = b * a * b⁻¹
  have hb : constantPoint x ((testSpec F).obj (op R)) = b :=
    congrArg (· ≫ x) (Subsingleton.elim _ _)
  rw [pointConj, hb]

private theorem same_parabolic_of_central_difference {S : ClosedSubgroup J.val}
    [IsCommMonObj S.group.X] (c c' : Cocharacter S.group)
    (D : LimitDecomposition (c ≫ S.inclusion)) (E : LimitDecomposition (c' ≫ S.inclusion))
    (h : ∀ (X : SchemeOver F) (x : X ⟶ J.val.X), Centralizes ((c * (c')⁻¹) ≫ S.inclusion) x) :
    SameSubgroup D.parabolic E.parabolic := by
  apply same_subgroup_of_same_affine_points (G := J) D.parabolic_points
  intro R g
  have ho : orbit (c ≫ S.inclusion) g = orbit (c' ≫ S.inclusion) g := by
    let L := laurentAlgebra R
    let t := laurentParameter R
    let x := cocharacterPoint (c ≫ S.inclusion) L t
    let y := cocharacterPoint (c' ≫ S.inclusion) L t
    let d := cocharacterPoint ((c * (c')⁻¹) ≫ S.inclusion) L t
    let gL : GroupPoints J.val L := mapPoints (laurentConstants R) g
    have hd : x = d * y := mul_inv_eq_iff_eq_mul.mp (difference_point c c' L t).symm
    have hdg : Commute gL d :=
      (centralizes_onAlgebras _ g).mp (h _ g) L (laurentConstants R) t
    have hdy : Commute y d := torus_values_commute c' (c * (c')⁻¹) L t t
    change x * gL * x⁻¹ = y * gL * y⁻¹
    rw [hd, hdy.eq.symm]
    calc
      (y * d) * gL * (y * d)⁻¹ = y * (d * gL * d⁻¹) * y⁻¹ := by group
      _ = y * gL * y⁻¹ := by rw [hdg.symm.mul_inv_cancel]
  simpa only [HasExtension, HasLimit, ← ho] using E.parabolic_points R g

private theorem noncentral_difference (hJ : IsReductive J) {S : ClosedSubgroup J.val}
    (hS : IsMaximalSplitTorus S) [IsCommMonObj S.group.X]
    (c : Cocharacter S.group) (D : LimitDecomposition (c ≫ S.inclusion))
    (hB : IsMinimalParabolic J D.parabolic) (hSB : IsSubgroupOf S D.parabolic)
    (Q : QuotientData S) (w : Q.splitImage.labels) (hw : w ≠ 1)
    (n : 𝟙_ (SchemeOver F) ⟶ Q.normalizer.group.X)
    (hn : rationalProjection Q n = Q.splitImage.constantGroup.sectionPoint w) :
    ∃ (X : SchemeOver F) (x : X ⟶ J.val.X),
      ¬ Centralizes ((c * (c ≫ (Q.splitImage.conjugation w).hom)⁻¹) ≫ S.inclusion) x := by
  classical
  let c' := c ≫ (Q.splitImage.conjugation w).hom
  obtain ⟨E⟩ := existsLimitDecomposition J (c' ≫ S.inclusion)
  by_contra h
  have hcentral (X : SchemeOver F) (x : X ⟶ J.val.X) :
      Centralizes ((c * (c')⁻¹) ≫ S.inclusion) x :=
    Classical.byContradiction (fun hx => h ⟨X, x, hx⟩)
  have hsame := same_parabolic_of_central_difference c c' D E hcentral
  have hconj := conjugates_limitParabolics Q w n hn c D E
  have hfix : ConjugatesSubgroups (n ≫ Q.normalizer.inclusion.hom.hom) D.parabolic D.parabolic :=
    (conjugates_iff_of_known_conjugate hconj).mpr hsame.symm
  obtain ⟨hZ, f, act, hf, _, hact, hfree⟩ :=
    Relative.RelativeWeylScheme.relativeWeylAction J hJ S D.parabolic hS hB hSB Q
  let := hZ
  let := act
  let B := markedParabolic D.parabolic hB hSB
  have hfn : f (QuotientGroup.mk n) = w :=
    (constantRationalEquiv Q.splitImage.constantGroup).injective ((hf n).symm.trans hn)
  have hfix' : w • B = B := hfn ▸ (hact n _ _ hB hB hSB hSB).mp hfix
  exact hw ((hfree B B).unique hfix' (one_smul _ _))

/-- The relative Bruhat torus commutator and parabolic limit. -/
theorem bruhatTorusCommutator : Specs.Arithmetic.LocalBruhatTorusCommutator.Statement.{u} := by
  intro F _ J hJ S hS c hc D N _ R B a hg
  obtain ⟨g, hgN, hgB⟩ := hg
  have hB := (Relative.RelativeChambers.minimalLimitParabolic J hJ S hS c D).mpr hc
  have hSB := (Relative.RelativeChambers.limitParabolicThroughSplitTorus J hJ S hS.1 c D).2
  obtain ⟨Q, w, n, hw, hn, l, hl, r, hr, hfac⟩ := outside_double_coset hJ hS hB hSB hgB
  let b := terminalToRational J.val (n ≫ Q.normalizer.inclusion.hom.hom)
  let p : RationalPoints J.val.X := l⁻¹ * r⁻¹
  have hp : p ∈ fieldPoints D.parabolic :=
    (fieldPoints D.parabolic).mul_mem ((fieldPoints D.parabolic).inv_mem hl)
      ((fieldPoints D.parabolic).inv_mem hr)
  obtain ⟨z, hz, hzS⟩ := parabolic_limit hJ hS c hc D hp
  obtain ⟨hcomm, _⟩ := RootData.CharacterPairing.perfectCharacterPairing S.group hS.1
  let := hcomm
  let c' := c ≫ (Q.splitImage.conjugation w).hom
  let d := c * (c')⁻¹
  refine ⟨b, p, z, d, ?_, hp, hz, hzS, noncentral_difference hJ hS c D hB hSB Q w hw n hn, ?_, ?_⟩
  · let q := QuotientGroup.mk' N
    have hq : q l * q b * q r = 1 := by
      rw [← map_mul, ← map_mul, ← hfac]
      exact (QuotientGroup.eq_one_iff g).mpr hgN
    change q b = q p
    calc
      q b = (q l)⁻¹ * (q l * q b * q r) * (q r)⁻¹ := by group
      _ = q p := by simp only [hq, p, map_mul, map_inv, mul_one]
  · intro t
    let bR : GroupPoints J.val R := b
    change cocharacterPoint (c ≫ S.inclusion) R t * bR *
        (cocharacterPoint (c ≫ S.inclusion) R t)⁻¹ * bR⁻¹ =
      cocharacterPoint (d ≫ S.inclusion) R t
    have ht : cocharacterPoint (c' ≫ S.inclusion) R t =
        bR * cocharacterPoint (c ≫ S.inclusion) R t * bR⁻¹ :=
      transported_point Q w n hn c t
    rw [difference_point c c' R t, ht]
    group
  · intro s t
    exact torus_values_commute c d R s t

end

end LinearAlgebraicGroups.Arithmetic.LocalBruhatTorusCommutator
