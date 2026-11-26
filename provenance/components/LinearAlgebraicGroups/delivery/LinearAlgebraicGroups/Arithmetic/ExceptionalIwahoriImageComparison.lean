import Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriImageComparison
import LinearAlgebraicGroups.Arithmetic.ExceptionalValuedTorusNormalizer
import LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
import LinearAlgebraicGroups.Relative.RelativeBruhat
import LinearAlgebraicGroups.Classification.CentralIsogenies
import LinearAlgebraicGroups.Classification.IntegralRealization
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj WithZero Pointwise

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriImageComparison

open _root_.LinearAlgebraicGroups.Specs
open _root_.LinearAlgebraicGroups.Specs.ExceptionalIwahoriImageComparison
open ValuativeRel WithZero

noncomputable section

universe u

theorem reductionIntersection : ReductionIntersection := by
  intro A G G₀ N W _ _ _ _ _ inc red B n q htor hlift marked
  ext x
  constructor
  · rintro ⟨a, ha, hax⟩
    obtain ⟨b, y, hby, hy, hb⟩ := hlift (q x)
    have hab : inc (a * b⁻¹) = n (x * y⁻¹) := by rw [map_mul, map_inv, hax, hby, map_mul, map_inv]
    have ht : red (a * b⁻¹) ∈ B := htor _ _ hab (by
      rw [map_mul, map_inv, hy, mul_inv_cancel])
    have hr : red b ∈ B := by
      have H := B.mul_mem (B.inv_mem ht) ha
      simpa [map_mul, map_inv] using H
    exact ⟨(hb.mp hr : q x = 1), ⟨a, hax⟩⟩
  · rintro ⟨hx, a, ha⟩
    exact ⟨a, htor a x ha hx, ha⟩

theorem uniformizerContraction : UniformizerContraction.{u} := by
  intro K _ _ _ _ c d hc hd x j
  let v := Specs.ExceptionalMarkedRootDescent.normalizedValuation K
  change v (c : K) = exp (-d) at hc
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  have hvx : v x ≠ 0 := (map_ne_zero v).mpr hx
  let a := log (v x)
  let b : ℤ := |a + j| + 1
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hb' : a + j < b := by
    dsimp [b]
    have h := le_abs_self (a + j)
    omega
  have hd' : 1 ≤ d * d := by
    rcases lt_or_gt_of_ne hd with hn | hp <;> nlinarith
  have hm : b ≤ (d * b) * d := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using Int.mul_le_mul_of_nonneg_right hd' hb
  refine ⟨d * b, ?_⟩
  change v ((↑(c ^ (d * b)) : K) * x) < exp (-j)
  have hvc : v (c : K) ≠ 0 := (map_ne_zero v).mpr c.ne_zero
  rw [map_mul, Units.val_zpow_eq_zpow_val, map_zpow₀, ← exp_log hvx, hc,
    ← exp_zsmul, ← exp_add, exp_lt_exp, zsmul_eq_mul]
  change (d * b) * (-d) + a < -j
  rw [mul_neg]
  linarith

open Specs.Relative.RelativeWeylScheme (rationalProjection)
open Specs.SimpleParabolicProduct (doubleCoset)

theorem rationalBorelFactorization : RationalBorelFactorization.{u} := by
  classical
  intro k _ G hG S B hs hb hsb N hn g
  obtain ⟨D, hZ, e, he, hrepr, hcov⟩ :=
    Relative.RelativeBruhat.relativeBruhat G hG S B hs hb hsb
  choose s h using hrepr
  have hg : g ∈ ⋃ w, doubleCoset B (𝟙_ (SchemeOver k))
      (s w ≫ D.normalizer.inclusion.hom.hom) := by
    rw [(hcov s h).1]
    exact Set.mem_univ _
  obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hg
  obtain ⟨_, ha, _, ⟨c, rfl⟩, rfl⟩ := Set.mem_mul.mp hw
  obtain ⟨_, ⟨b, rfl⟩, _, ht, rfl⟩ := Set.mem_mul.mp ha
  rw [Set.mem_singleton_iff] at ht
  subst ht
  let n := s w ≫ D.normalizer.inclusion.hom.hom
  have hNorm : Normalizes S.inclusion n := (D.normalizerProperty _ _).mpr ⟨s w, rfl⟩
  obtain ⟨r, hr⟩ := (hn _ _).mp hNorm
  refine ⟨b, c, r, ?_⟩
  change (b ≫ B.inclusion.hom.hom) * (toUnit _ ≫ n) * (c ≫ B.inclusion.hom.hom) = _
  rw [hr, toUnit_unit, Category.id_comp]

theorem ordinaryImageQuotient : OrdinaryImageQuotient := by
  intro Gsc G Y _ _ _ p Tsc Nsc T N I J ν hTN hν hfactor hstable hTsc hNsc hunit hI hJ hsc H Λ
  let U := ν.ker.map T.subtype
  have hUN : U ≤ N := by
    rintro _ ⟨t, ht, rfl⟩
    exact hTN t.property
  have hJN : J ≤ N := by
    rw [hJ]
    refine sup_le ?_ hUN
    rintro _ ⟨n, hn, rfl⟩
    rw [← hNsc] at hn
    exact hn
  have hhH : H = p.range ⊔ U := by
    apply le_antisymm
    · refine sup_le hI ?_
      rw [hJ]
      have hrange : Nsc.map p ≤ p.range := by
        rintro _ ⟨n, _, rfl⟩
        exact ⟨n, rfl⟩
      exact sup_le (hrange.trans le_sup_left) le_sup_right
    · exact sup_le hsc (hunit.trans le_sup_left)
  have hΛ : Λ = (p.range.comap T.subtype).map ν := by
    apply congrArg (Subgroup.map ν)
    ext t
    change (t : G) ∈ Tsc.map p ↔ (t : G) ∈ p.range
    constructor
    · rintro ⟨x, _, hx⟩
      exact ⟨x, hx⟩
    · rintro ⟨x, hx⟩
      refine ⟨x, ?_, hx⟩
      rw [← hTsc]
      change p x ∈ T
      exact hx.symm ▸ t.property
  have hp : p.range.Normal := by
    constructor
    intro g hg a
    rcases hg with ⟨y, rfl⟩
    obtain ⟨x, t, rfl⟩ := hfactor a
    have h₁ := p.range.mul_mem (show p x ∈ p.range from ⟨x, rfl⟩) (hstable t y)
    have h₂ := p.range.mul_mem h₁ (p.range.inv_mem (show p x ∈ p.range from ⟨x, rfl⟩))
    simpa only [mul_inv_rev, mul_assoc] using h₂
  have hIntersection : H ⊓ N = J := by
    apply le_antisymm
    · rintro g ⟨hg, hn⟩
      rw [hhH] at hg
      obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hg
      have haN : a ∈ N := by
        simpa [mul_assoc] using N.mul_mem hn (N.inv_mem (hUN hb))
      obtain ⟨x, rfl⟩ := ha
      rw [hJ]
      have hleft : Nsc.map p ≤ Nsc.map p ⊔ U := le_sup_left
      have hright : U ≤ Nsc.map p ⊔ U := le_sup_right
      exact (Nsc.map p ⊔ U).mul_mem
        (hleft ⟨x, hNsc ▸ haN, rfl⟩) (hright hb)
    · exact le_inf le_sup_right hJN
  refine ⟨hhH, hIntersection, ?_⟩
  let j : T →* G ⧸ p.range := (QuotientGroup.mk' p.range).comp T.subtype
  have hj : Function.Surjective j := by
    intro g
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨x, t, rfl⟩ := hfactor a
    refine ⟨t, ?_⟩
    have hx : (QuotientGroup.mk' p.range) (p x) = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨x, rfl⟩
    change (QuotientGroup.mk' p.range) (t : G) = (QuotientGroup.mk' p.range) (p x * t)
    rw [map_mul, hx, one_mul]
  let l : T →* Y ⧸ Λ := (QuotientGroup.mk' Λ).comp ν
  have hker : j.ker ≤ l.ker := by
    intro t ht
    have ht' : (t : G) ∈ p.range := (QuotientGroup.eq_one_iff _).mp ht
    exact (QuotientGroup.eq_one_iff _).mpr (hΛ ▸ ⟨t, ht', rfl⟩)
  let Φ : G ⧸ p.range →* Y ⧸ Λ := (j.liftOfSurjective hj) ⟨l, hker⟩
  have hΦ (t : T) : Φ (j t) = l t := j.liftOfRightInverse_comp_apply _ _ _ _
  let q := Φ.comp (QuotientGroup.mk' p.range)
  have hqt (t : T) : q t = QuotientGroup.mk (ν t) := hΦ t
  have hqp (x : Gsc) : q (p x) = 1 := by
    change Φ ((QuotientGroup.mk' p.range) (p x)) = 1
    rw [show (QuotientGroup.mk' p.range) (p x) = 1 from (QuotientGroup.eq_one_iff _).mpr ⟨x, rfl⟩,
      map_one]
  have hq : Function.Surjective q := by
    intro a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨t, rfl⟩ := hν b
    exact ⟨t, hqt t⟩
  have hh : H = q.ker := by
    apply le_antisymm
    · rw [hhH]
      apply sup_le
      · rintro _ ⟨x, rfl⟩
        exact hqp x
      · rintro _ ⟨t, ht, rfl⟩
        change q t = 1
        rw [hqt, show ν t = 1 from ht]
        exact (QuotientGroup.eq_one_iff _).mpr Λ.one_mem
    · intro g hg
      obtain ⟨x, t, rfl⟩ := hfactor g
      change q (p x * t) = 1 at hg
      rw [map_mul, hqp, one_mul, hqt, QuotientGroup.eq_one_iff] at hg
      rw [hΛ] at hg
      obtain ⟨s, hs, hsν⟩ := hg
      have hunit : t * s⁻¹ ∈ ν.ker := by
        change ν (t * s⁻¹) = 1
        rw [map_mul, map_inv, hsν, mul_inv_cancel]
      have hPH : p.range ≤ H := hhH.ge.trans' le_sup_left
      have hUH : ν.ker.map T.subtype ≤ H := hhH.ge.trans' le_sup_right
      have hs' : (s : G) ∈ H := hPH hs
      have hx : p x ∈ H := hPH ⟨x, rfl⟩
      have ht : (↑(t * s⁻¹) : G) ∈ H := hUH ⟨_, hunit, rfl⟩
      have h := H.mul_mem (H.mul_mem hx ht) hs'
      simpa [mul_assoc] using h
  have : H.Normal := hh ▸ inferInstance
  refine ⟨‹H.Normal›, QuotientGroup.liftEquiv H hq hh, ?_⟩
  intro t
  rw [QuotientGroup.liftEquiv_mk]
  exact hqt t

theorem ordinarySubgroupFromCentralMap : OrdinarySubgroupFromCentralMap := by
  intro Gsc G Y W Asc A _ _ _ _ _ _ p Tsc Nsc Isc T N I ν q a₀ a b
    hTN hν ha₀ hT hN hlabel hlift haction hnormal hsc had U hker hI J G₀ Λ
  let P := p.range
  letI : P.Normal := hnormal
  have hNsc (n : Nsc) : p n ∈ N := hN.symm ▸ n.property
  have hJ : J = Nsc.map p ⊔ U := by
    apply le_antisymm
    · rintro _ ⟨n, ⟨d, hd⟩, rfl⟩
      obtain ⟨x, rfl⟩ := ha₀ d
      let m : N := ⟨p x, hNsc x⟩
      have hma : a m = a n := (haction x m rfl).trans hd
      have hk : m⁻¹ * n ∈ a.ker := by
        change a (m⁻¹ * n) = 1
        rw [map_mul, map_inv, hma, inv_mul_cancel]
      have hm : (m : G) ∈ Nsc.map p := ⟨x, x.property, rfl⟩
      have hn : ((m⁻¹ * n : N) : G) ∈ U := hker ▸ ⟨_, hk, rfl⟩
      have h := (Nsc.map p ⊔ U).mul_mem
        ((le_sup_left : Nsc.map p ≤ Nsc.map p ⊔ U) hm)
        ((le_sup_right : U ≤ Nsc.map p ⊔ U) hn)
      change (n : G) ∈ Nsc.map p ⊔ U
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left] using h
    · apply sup_le
      · rintro _ ⟨x, hx, rfl⟩
        let n : Nsc := ⟨x, hx⟩
        exact ⟨⟨p x, hNsc n⟩, ⟨a₀ n, (haction n ⟨p x, hNsc n⟩ rfl).symm⟩, rfl⟩
      · rw [← hker]
        rintro _ ⟨n, hn, rfl⟩
        exact ⟨n, ⟨1, (map_one b).trans hn.symm⟩, rfl⟩
  have hUT : U ≤ T := by
    rintro _ ⟨t, _, rfl⟩
    exact t.property
  have hI_le : I ≤ P ⊔ T := by
    rw [hI]
    exact sup_le (fun _ ⟨x, _, hx⟩ => (le_sup_left : P ≤ P ⊔ T) ⟨x, hx⟩)
      (hUT.trans le_sup_right)
  have hN_le : N ≤ P ⊔ T := by
    intro n hn
    let n' : N := ⟨n, hn⟩
    obtain ⟨x, m, hm, hlabel'⟩ := hlift (q n')
    have hmP : (m : G) ∈ P := ⟨x, hm.symm⟩
    have hq : q (m⁻¹ * n') = 1 := by
      rw [map_mul, map_inv, hlabel', inv_mul_cancel]
    have hT' : ((m⁻¹ * n' : N) : G) ∈ T := (hlabel _).mp hq
    have hh := (P ⊔ T).mul_mem ((le_sup_left : P ≤ P ⊔ T) hmP)
      ((le_sup_right : T ≤ P ⊔ T) hT')
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left] using hh
  have hfactor (g : G) : ∃ (x : Gsc) (t : T), g = p x * t := by
    have hg : g ∈ P ⊔ T := (had ▸ sup_le hI_le hN_le) (Subgroup.mem_top g)
    obtain ⟨_, ⟨x, rfl⟩, t, ht, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hg
    exact ⟨x, ⟨t, ht⟩, rfl⟩
  have hPT : P ≤ I ⊔ J := by
    have htop : P = (⊤ : Subgroup Gsc).map p := (Subgroup.map_top p).symm
    rw [htop, ← hsc, Subgroup.map_sup]
    have h₁ : Isc.map p ≤ I := by rw [hI]; exact le_sup_left
    have h₂ : Nsc.map p ≤ J := by rw [hJ]; exact le_sup_left
    exact sup_le (h₁.trans le_sup_left) (h₂.trans le_sup_right)
  have hstable (t : T) (x : Gsc) : (t : G) * p x * (t : G)⁻¹ ∈ P :=
    hnormal.conj_mem _ ⟨x, rfl⟩ _
  have hUI : U ≤ I := by rw [hI]; exact le_sup_right
  have hIP : I ≤ P ⊔ U := by
    rw [hI]
    exact sup_le (fun _ ⟨x, _, hx⟩ => (le_sup_left : P ≤ P ⊔ U) ⟨x, hx⟩) le_sup_right
  exact ⟨hJ, ordinaryImageQuotient p Tsc Nsc T N I J ν hTN hν hfactor hstable hT hN hUI hIP hJ hPT⟩

section MarkedReduction

open _root_.LinearAlgebraicGroups.Specs.IntegralSemisimpleModel
open _root_.LinearAlgebraicGroups.Specs.ExceptionalValuedTorusNormalizer
open _root_.LinearAlgebraicGroups.Arithmetic.ExceptionalValuedTorusNormalizer
  (fibreNormalizerTorusAction splitTorusTranslation splitIntegralWeylLifts markedIntegralTorusKernel)
open _root_.LinearAlgebraicGroups.Specs.SchemeDerivedGroup (FactorsThrough)
open private fibrePointsEquiv from LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
open private groundIso from LinearAlgebraicGroups.Solvable.TorusSections
open private conjugates_of_normalizes subgroup_normalizes from LinearAlgebraicGroups.RootData.BorelNormalizer
open private integralClosedPoint from
  LinearAlgebraicGroups.Arithmetic.ExceptionalValuedTorusNormalizer

attribute [local instance] integerAlgebra

set_option backward.isDefEq.respectTransparency false in
private theorem borel_normalizer_torus {k : Type u} [Field k]
    (P : Pinning.SplitBorelPair k) {g : 𝟙_ (SchemeOver k) ⟶ P.G.val.X}
    (hg : FactorsThrough P.B g) (hn : Normalizes P.T.inclusion g) :
    FactorsThrough P.T g := by
  obtain ⟨_, ht⟩ := RootData.BorelNormalizer.weylSimplyTransitiveOnBorels
    P.G P.reductive P.T P.split P.maximal
  obtain ⟨n, _, _, hn'⟩ := ht P.B P.B P.borel P.borel P.containsTorus P.containsTorus
  have hN : Normalizes P.T.inclusion (1 : 𝟙_ (SchemeOver k) ⟶ P.G.val.X) :=
    subgroup_normalizes P.T (Subgroup.one_mem (SubgroupSections P.T _))
  have hB (x : 𝟙_ (SchemeOver k) ⟶ P.G.val.X) (hx : FactorsThrough P.B x) :
      GeometricBorelConjugacy.ConjugatesSubgroups x P.B P.B :=
    conjugates_of_normalizes P.B
      ((RootData.BorelNormalizer.groundFieldBorelNormalizer P.G P.reductive P.B P.borel _ _).mpr hx)
  let T₀ := SubgroupSections P.T (𝟙_ (SchemeOver k))
  have hnT : n⁻¹ ∈ T₀ := by
    change FactorsThrough P.T n⁻¹
    simpa only [mul_one] using (hn' 1 hN).mp (hB 1 (Subgroup.one_mem _))
  have hngT : n⁻¹ * g ∈ T₀ := (hn' g hn).mp (hB g hg)
  change g ∈ T₀
  simpa using T₀.mul_mem (T₀.inv_mem hnT) hngT

private def markedSectionHom {k : Type u} [Field k] {D : Pinning.BasedRootDatum.{u}}
    {M : Model D} (E : FibreNormalizer M k) :
    (𝟙_ (SchemeOver k) ⟶ E.realization.pinned.pair.G.val.X) →*
      IntegralPoints M.group (CommAlgCat.of Integers.{u} k) :=
  let R := CommAlgCat.of k k
  let Y := (testSpec k).obj (Opposite.op R)
  let i := MonoidHom.mk' (fun p : 𝟙_ (SchemeOver k) ⟶ E.realization.pinned.pair.G.val.X =>
      toUnit Y ≫ p) (fun x y => MonObj.comp_mul (toUnit Y) x y)
  (fibrePointsEquiv M.group R).toMonoidHom.comp ((pointHom E.fibreIso.inv Y).comp i)

private theorem markedSectionHom_injective {k : Type u} [Field k] {D : Pinning.BasedRootDatum.{u}}
    {M : Model D} (E : FibreNormalizer M k) : Function.Injective (markedSectionHom E) := by
  intro x y h
  let R := CommAlgCat.of k k
  let Y := (testSpec k).obj (Opposite.op R)
  have h₁ : (toUnit Y ≫ x) ≫ E.fibreIso.inv.hom.hom =
      (toUnit Y ≫ y) ≫ E.fibreIso.inv.hom.hom := (fibrePointsEquiv M.group R).injective h
  letI : IsIso E.fibreIso.inv.hom.hom := by infer_instance
  have h₂ := (cancel_mono E.fibreIso.inv.hom.hom).mp h₁
  have hg : toUnit Y = (groundIso (k := k)).hom := Subsingleton.elim _ _
  rw [hg] at h₂
  exact (cancel_epi (groundIso (k := k)).hom).mp h₂

private def markedBorelPoints {k : Type u} [Field k] {D : Pinning.BasedRootDatum.{u}}
    {M : Model D} (E : FibreNormalizer M k) :
    Subgroup (IntegralPoints M.group (CommAlgCat.of Integers.{u} k)) :=
  (SubgroupSections E.realization.pinned.pair.B (𝟙_ (SchemeOver k))).map (markedSectionHom E)

private theorem markedBorelPoints_set {k : Type u} [Field k] {D : Pinning.BasedRootDatum.{u}}
    {M : Model D} (E : FibreNormalizer M k) :
    (markedBorelPoints E : Set _) = positiveBorelPointSet E := by
  ext p
  constructor
  · rintro ⟨_, ⟨b, rfl⟩, rfl⟩
    refine ⟨b, ?_⟩
    change forgetFibrePoint _ _ (toUnit _ ≫ b ≫ _ ≫ _) =
      forgetFibrePoint _ _ ((toUnit _ ≫ (b ≫ _)) ≫ _)
    congr 1
  · rintro ⟨b, rfl⟩
    refine ⟨b ≫ E.realization.pinned.pair.B.inclusion.hom.hom, ⟨b, rfl⟩, ?_⟩
    change forgetFibrePoint _ _ ((toUnit _ ≫ b ≫
      E.realization.pinned.pair.B.inclusion.hom.hom) ≫ E.fibreIso.inv.hom.hom) = _
    rw [Category.assoc, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem normalizerPoint_borel_iff {k : Type u} [Field k]
    {D : Pinning.BasedRootDatum.{u}} {M : Model D} (E : FibreNormalizer M k) :
    letI := E.torusComm
    ∀ n : 𝟙_ (SchemeOver k) ⟶ E.identification.normalizer.group.X,
      E.point n ∈ markedBorelPoints E ↔ E.label n = 1 := by
  letI := E.torusComm
  intro n
  let C := E.identification
  let g := n ≫ C.normalizer.inclusion.hom.hom
  have hg : E.point n = markedSectionHom E g := by
    rw [E.point_eq]
    change _ = forgetFibrePoint _ _ ((toUnit _ ≫ g) ≫ E.fibreIso.inv.hom.hom)
    simp only [g, Category.assoc]
    rfl
  have h : E.point n ∈ markedBorelPoints E ↔
      FactorsThrough E.realization.pinned.pair.B g := by
    rw [hg]
    constructor
    · rintro ⟨x, hx, he⟩
      exact (markedSectionHom_injective E he) ▸ hx
    · exact fun hx => ⟨g, hx, rfl⟩
  rw [h]
  constructor
  · intro hb
    have hN : Normalizes E.realization.pinned.pair.T.inclusion g :=
      (C.representsNormalizer _ _).mpr ⟨n, rfl⟩
    obtain ⟨t, ht⟩ := borel_normalizer_torus E.realization.pinned.pair hb hN
    haveI : IsClosedImmersion C.normalizer.inclusion.hom.hom.left := C.normalizer.isClosedImmersion
    haveI : Mono C.normalizer.inclusion.hom.hom := Over.mono_of_mono_left _
    apply (E.kernel n).mpr
    refine ⟨t, (cancel_mono C.normalizer.inclusion.hom.hom).mp ?_⟩
    change (t ≫ C.torusInclusion.hom.hom) ≫ C.normalizer.inclusion.hom.hom = g
    rw [Category.assoc, ← Grp.comp_hom_hom, C.inclusion_eq]
    exact ht
  · intro hn
    obtain ⟨t, ht⟩ := (E.kernel n).mp hn
    obtain ⟨b, hb⟩ := E.realization.pinned.pair.containsTorus
    refine ⟨t ≫ b.hom.hom, ?_⟩
    change (t ≫ b.hom.hom) ≫ E.realization.pinned.pair.B.inclusion.hom.hom = g
    rw [Category.assoc, ← Grp.comp_hom_hom, hb]
    change _ = n ≫ C.normalizer.inclusion.hom.hom
    rw [← ht, Category.assoc, ← Grp.comp_hom_hom, C.inclusion_eq]

open private affineTorusPointEquiv torusPoint_natural from
  LinearAlgebraicGroups.Classification.IntegralSemisimpleModel

set_option backward.isDefEq.respectTransparency false in
private theorem integralTorus_reduces_borel {K : Type u} [Field K] [ValuativeRel K]
    {D : Pinning.BasedRootDatum.{u}} {M : Model D}
    (E : FibreNormalizer M (IsLocalRing.ResidueField (valuation K).valuationSubring))
    (a : IntegralPoints M.group (CommAlgCat.of Integers.{u} (valuation K).valuationSubring))
    (t : TorusValues D (CommAlgCat.of Integers.{u} K))
    (ht : (integralPointFunctor M.group).map (valuationRingInclusion K) a =
      torusPoint D (CommAlgCat.of Integers.{u} K) t ≫ M.torus.hom.hom) :
    (integralPointFunctor M.group).map (residueReduction K) a ∈ markedBorelPoints E := by
  letI := E.torusComm
  let O := CommAlgCat.of Integers.{u} (valuation K).valuationSubring
  let R := CommAlgCat.of Integers.{u} (IsLocalRing.ResidueField (valuation K).valuationSubring)
  have hm : IsClosedImmersion M.torus.hom.hom.left := M.torusClosed
  obtain ⟨p, hp⟩ := integralClosedPoint M.torus.hom.hom (valuationRingInclusion K)
    Subtype.val_injective a (torusPoint D (CommAlgCat.of Integers.{u} K) t) ht
  obtain ⟨s, hs⟩ := (affineTorusPointEquiv (k := Integers.{u}) (M := Multiplicative D.X) O).surjective p
  change torusPoint D O s = p at hs
  let s₀ := (Units.map (residueReduction K).hom.toMonoidHom).comp s
  have hr : (integralPointFunctor M.group).map (residueReduction K) a =
      torusPoint D R s₀ ≫ M.torus.hom.hom := by
    change integralSpec.map (residueReduction K).op ≫ a = _
    rw [← hp, ← hs, ← Category.assoc, torusPoint_natural]
  obtain ⟨j, hj, _⟩ := fibreNormalizerTorusAction E
  rw [hr, ← hj s₀]
  exact (normalizerPoint_borel_iff E _).mpr (j s₀).property

set_option backward.isDefEq.respectTransparency false in
theorem splitIwahoriIntersection : SplitIwahoriIntersection.{u} := by
  intro K _ _ _ _ D M F E index _ b
  letI := F.torusComm
  letI := E.torusComm
  let O := CommAlgCat.of Integers.{u} (valuation K).valuationSubring
  let i := ((integralPointFunctor M.group).map (valuationRingInclusion K)).hom
  let r := ((integralPointFunctor M.group).map (residueReduction K)).hom
  obtain ⟨j, hj, _⟩ := fibreNormalizerTorusAction F
  obtain ⟨ν, _, hν, hνker⟩ := splitTorusTranslation K D b
  refine ⟨markedBorelPoints E, markedBorelPoints_set E, j, ν, hj, hν, ?_⟩
  have hI := reductionIntersection i r (markedBorelPoints E) F.point F.label (by
    intro a x ha hx
    let t := j.symm ⟨x, hx⟩
    have ht : F.point (j t).val = F.point x := congrArg (fun y : F.label.ker => F.point y.val)
      (j.apply_symm_apply ⟨x, hx⟩)
    exact integralTorus_reduces_borel E a t (ha.trans (ht.symm.trans (hj t)))) (by
    intro w
    obtain ⟨x, y, a, hx, hy, ha, hb⟩ :=
      splitIntegralWeylLifts M F E O (valuationRingInclusion K) (residueReduction K) w
    exact ⟨a, x, ha, hx, hb ▸ hy ▸ normalizerPoint_borel_iff E y⟩)
  change (borelReduction i r (markedBorelPoints E)).comap F.point = _
  rw [hI]
  ext x
  constructor
  · rintro ⟨hx, ha⟩
    let t := j.symm ⟨x, hx⟩
    have ht : (j t).val = x := congrArg Subtype.val (j.apply_symm_apply ⟨x, hx⟩)
    have hmem : ν t = 1 := (hνker t).mpr
      ((markedIntegralTorusKernel D M.toIntegralMarking b t).mpr (by rwa [← hj, ht]))
    exact ⟨t, hmem, ht⟩
  · rintro ⟨t, ht, hx⟩
    change (j t).val = x at hx
    rw [← hx]
    refine ⟨(j t).property, ?_⟩
    change F.point (j t).val ∈ i.range
    rw [hj]
    exact (markedIntegralTorusKernel D M.toIntegralMarking b t).mp ((hνker t).mp ht)

open _root_.LinearAlgebraicGroups.Arithmetic.ExceptionalValuedTorusNormalizer
  (foldedIntegralNormalizerLifts pinnedQuadraticNormalizer)
open private markedNormalizerPointHom markedNormalizerPointHom_apply from
  LinearAlgebraicGroups.Arithmetic.ExceptionalValuedTorusNormalizer

set_option backward.isDefEq.respectTransparency false in
theorem foldedIwahoriIntersection : FoldedIwahoriIntersection.{u} := by
  intro k K _ _ _ _ _ _ D M F E l G B T d σ hdeg hσ
  letI := F.torusComm
  letI := E.torusComm
  let C := F.identification
  let s := (l (d.outer σ)).asIso.hom
  let R := CommAlgCat.of k K
  let Y := (testSpec k).obj (Opposite.op R)
  let O := CommAlgCat.of Integers.{u} (valuation K).valuationSubring
  let i := ((integralPointFunctor M.group).map (valuationRingInclusion K)).hom
  let r := ((integralPointFunctor M.group).map (residueReduction K)).hom
  intro _C _s _R _Y e hroot he hpair hort N hN
  obtain ⟨q, a, hq, hk, ha, q₀, hq₀, hk₀, hlift⟩ :=
    foldedIntegralNormalizerLifts F E e s σ hroot he hpair hort O
      (valuationRingInclusion K) (residueReduction K)
  let H := MonoidHom.eqLocus a.toMonoidHom (fieldCoefficientAction σ C.normalizer.group)
  obtain ⟨c₁, c₂, hc₁, hc₂, ti, uN, hti, huN, htor⟩ :=
    pinnedQuadraticNormalizer F d σ hdeg hσ a ha N hN
  let jH := (markedNormalizerPointHom F R).comp H.subtype
  let j := jH.comp uN.toMonoidHom
  have hj (n : 𝟙_ (SchemeOver k) ⟶ N.group.X) :
      j n = markedNormalizerPoint F R (uN n).val := markedNormalizerPointHom_apply F R _
  have htor' (n : 𝟙_ (SchemeOver k) ⟶ N.group.X) :
      q₀ (uN n) = 1 ↔ ∃ t : 𝟙_ (SchemeOver k) ⟶ T.group.X,
        t ≫ T.inclusion.hom.hom = n ≫ N.inclusion.hom.hom :=
    (hk₀ (uN n)).trans (htor n).symm
  refine ⟨a, ha, uN, q, q₀, j, markedBorelPoints E, markedBorelPoints_set E, hq₀, hj,
    htor', ?_⟩
  apply reductionIntersection i r (markedBorelPoints E) j (q₀.comp uN.toMonoidHom)
  · intro p n hp hn
    change q₀ (uN n) = 1 at hn
    obtain ⟨t, ht⟩ := (hk₀ (uN n)).mp hn
    let v := (F.torusValues R).symm t
    have hv : F.torusValues R v = t := (F.torusValues R).apply_symm_apply t
    have htv : j n = torusPoint D (CommAlgCat.of Integers.{u} K) v ≫ M.torus.hom.hom := by
      have hcomp : C.torusInclusion.hom.hom ≫ C.normalizer.inclusion.hom.hom =
          F.realization.pinned.pair.T.inclusion.hom.hom :=
        congrArg (fun f : F.realization.pinned.pair.T.group ⟶ F.realization.pinned.pair.G.val =>
          f.hom.hom) C.inclusion_eq
      rw [hj]
      change forgetFibrePoint M.group R
        ((uN n).val ≫ C.normalizer.inclusion.hom.hom ≫ F.fibreIso.inv.hom.hom) = _
      rw [← ht, Category.assoc, ← Category.assoc C.torusInclusion.hom.hom, hcomp, ← hv]
      exact F.torusPoint_eq R v
    exact integralTorus_reduces_borel E p v (hp.trans htv)
  · intro w
    obtain ⟨n, m, p, hn, hm, hp, hr⟩ := hlift w
    refine ⟨p, uN.symm n, ?_, ?_, ?_⟩
    · exact hp.trans (((hj (uN.symm n)).trans
        (congrArg (fun x : H => markedNormalizerPoint F R x.val) (uN.apply_symm_apply n))).symm)
    · change q₀ (uN (uN.symm n)) = w
      rw [uN.apply_symm_apply, hn]
    · change (integralPointFunctor M.group).map (residueReduction K) p ∈ markedBorelPoints E ↔ _
      rw [hr, normalizerPoint_borel_iff E m, hm]
      constructor
      · intro hw
        apply Subtype.ext
        exact hw
      · intro hw
        exact congrArg Subtype.val hw

open _root_.LinearAlgebraicGroups.Specs.ExceptionalMarkedRootDescent (markedRootPoint)
open private markedRootPoint_map markedRootPoint_zero from
  LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
open private markedTorusPointHom markedTorusPointHom_apply from
  LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent

set_option backward.isDefEq.respectTransparency false in
private theorem strictRoot_mem_reduction {K : Type u} [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {D : Pinning.BasedRootDatum.{u}} (M : IntegralMarking D)
    (B : Subgroup (IntegralPoints M.group (CommAlgCat.of Integers.{u}
      (IsLocalRing.ResidueField (valuation K).valuationSubring))))
    (a : D.I) (x : K) (hx : Specs.ExceptionalMarkedRootDescent.normalizedValuation K x < 1) :
    markedRootPoint M (CommAlgCat.of Integers.{u} K) a x ∈ markedBorelReduction M.group B := by
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  have hx' : valuation K x < 1 := by
    apply e.strictMono.lt_iff_lt.mp
    rwa [map_one]
  let O := CommAlgCat.of Integers.{u} (valuation K).valuationSubring
  let x₀ : O := ⟨x, hx'.le⟩
  refine ⟨markedRootPoint M O a x₀, ?_, ?_⟩
  · change (integralPointFunctor M.group).map (residueReduction K) (markedRootPoint M O a x₀) ∈ B
    have hred : (residueReduction K).hom x₀ = 0 :=
      (IsLocalRing.residue_eq_zero_iff x₀).mpr ((Valuation.mem_maximalIdeal_iff K (valuation K)).mpr hx')
    rw [markedRootPoint_map, hred, markedRootPoint_zero]
    exact B.one_mem
  · exact markedRootPoint_map M (valuationRingInclusion K) a x₀

private theorem corootPairing_self {D : Pinning.BasedRootDatum.{u}} (a : D.I) :
    D.datum.toLinearMap (D.datum.root a) (D.datum.coroot a) = 2 := by
  exact D.datum.pairing_same a

set_option backward.isDefEq.respectTransparency false in
private theorem cocharacterContraction {K : Type u} [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {D : Pinning.BasedRootDatum.{u}} (M : IntegralMarking D)
    (B : Subgroup (IntegralPoints M.group (CommAlgCat.of Integers.{u}
      (IsLocalRing.ResidueField (valuation K).valuationSubring))))
    (a : D.I) (y : D.Y) (π : Kˣ)
    (hπ : Specs.ExceptionalMarkedRootDescent.normalizedValuation K (π : K) = exp (-1))
    (h : D.datum.toLinearMap (D.datum.root a) y ≠ 0) (x : K) (j : ℤ) :
    let R := CommAlgCat.of Integers.{u} K
    let d := D.datum.toLinearMap (D.datum.root a) y
    let n : IntegralPoints M.group R := torusPoint D R (cocharacter D y R π) ≫ M.torus.hom.hom
    ∃ m : ℤ, Specs.ExceptionalMarkedRootDescent.normalizedValuation K
      ((↑((π ^ d) ^ m) : K) * x) < exp (-j) ∧
      n ^ m * markedRootPoint M R a x * (n ^ m)⁻¹ ∈ markedBorelReduction M.group B := by
  intro R d n
  let v := Specs.ExceptionalMarkedRootDescent.normalizedValuation K
  let c := cocharacter D y R π
  have hval : v ((π ^ d : Kˣ) : K) = exp (-d) := by
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hπ, ← exp_zsmul, zsmul_eq_mul]
    simp
  obtain ⟨m, hm⟩ := uniformizerContraction K (π ^ d) d hval h x (max j 0)
  refine ⟨m, hm.trans_le (exp_le_exp.mpr (by omega)), ?_⟩
  have hm' : v ((↑((π ^ d) ^ m) : K) * x) < 1 :=
    hm.trans_le (exp_le_one_iff.mpr (by omega))
  have hn : n ^ m = torusPoint D R (c ^ m) ≫ M.torus.hom.hom := by
    have he := (markedTorusPointHom M R).map_zpow c m
    rw [markedTorusPointHom_apply, markedTorusPointHom_apply] at he
    exact he.symm
  rw [hn]
  have heq := M.conjugation R (c ^ m) a x
  change (torusPoint D R (c ^ m) ≫ M.torus.hom.hom) * markedRootPoint M R a x *
      (torusPoint D R (c ^ m) ≫ M.torus.hom.hom)⁻¹ =
    markedRootPoint M R a (↑((c ^ m) (Multiplicative.ofAdd (D.datum.root a))) * x) at heq
  rw [heq]
  exact strictRoot_mem_reduction M B a _ hm'

set_option backward.isDefEq.respectTransparency false in
theorem splitRootContraction : SplitRootContraction.{u} := by
  intro K _ _ _ _ D M F B
  letI := F.torusComm
  intro R v I a y π h hh hπ
  obtain ⟨j, hj, _⟩ := fibreNormalizerTorusAction F
  let c := cocharacter D y R π
  refine ⟨(j c).val, (j c).property, hj c, ?_⟩
  intro u q
  obtain ⟨m, hm, hmem⟩ := cocharacterContraction M.toIntegralMarking B a y π hπ hh u q
  refine ⟨m, hm, ?_⟩
  change F.point ((j c).val ^ m) * _ * (F.point ((j c).val ^ m))⁻¹ ∈ I
  rw [F.point.map_zpow, hj]
  exact hmem

open _root_.LinearAlgebraicGroups.Specs.ExceptionalMarkedRootDescent (orderedRootPoint)

private theorem cocharacter_conjugates_root_word {D : Pinning.BasedRootDatum.{u}}
    (M : IntegralMarking D) (R : IntegralAlgebra.{u}) (c : TorusValues D R) (l : List D.I)
    (x : D.I → R) :
    let n : IntegralPoints M.group R := torusPoint D R c ≫ M.torus.hom.hom
    n * orderedRootPoint M R l x * n⁻¹ =
      orderedRootPoint M R l (fun a => (c (Multiplicative.ofAdd (D.datum.root a)) : R) * x a) := by
  intro n
  change MulAut.conj n (orderedRootPoint M R l x) = _
  induction l with
  | nil => exact (MulAut.conj n).map_one
  | cons a l ih =>
    change MulAut.conj n (markedRootPoint M R a (x a) * orderedRootPoint M R l x) = _
    rw [map_mul, ih]
    exact congrArg (· * orderedRootPoint M R l _) (M.conjugation R c a (x a))

set_option backward.isDefEq.respectTransparency false in
theorem markedRootWordContraction : MarkedRootWordContraction.{u} := by
  classical
  intro K _ _ _ _ D M B₀ y π e he hπ R v c n l hl x j
  let j₀ := max j 0
  let b (a : D.I) : ℕ := (log (v (x a)) + j₀).natAbs
  let m := (∑ a ∈ l.toFinset, b a) + 1
  have hm (a : D.I) (ha : a ∈ l) : log (v (x a)) + j₀ < (m : ℤ) := by
    have h₁ : log (v (x a)) + j₀ ≤ (b a : ℤ) := Int.le_natAbs
    have h₂ : b a ≤ ∑ a ∈ l.toFinset, b a :=
      Finset.single_le_sum (fun a _ => Nat.zero_le (b a)) (List.mem_toFinset.mpr ha)
    exact h₁.trans_lt (by exact_mod_cast Nat.lt_succ_of_le h₂)
  let z : D.I → K := fun a =>
    ((c ^ m) (Multiplicative.ofAdd (D.datum.root a)) : Kˣ) * x a
  have hz (a : D.I) (ha : a ∈ l) : v (z a) < exp (-j₀) := by
    by_cases hx : x a = 0
    · simp [z, hx]
    let d := D.datum.toLinearMap (D.datum.root a) y
    have hd : 0 < d := hl a ha
    have hc : v ((↑(π ^ d) : K)) = exp (-(e * d)) := by
      rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hπ, ← exp_zsmul, zsmul_eq_mul]
      simp [mul_comm]
    have hcalc : v (z a) = exp (-(e * d) * (m : ℤ) + log (v (x a))) := by
      change v ((↑((π ^ d) ^ m) : K) * x a) = _
      rw [map_mul, Units.val_pow_eq_pow_val, map_pow, hc,
        ← exp_log ((map_ne_zero v).mpr hx), ← exp_nsmul, ← exp_add]
      congr 1
      simp [mul_comm]
    rw [hcalc, exp_lt_exp]
    have hprod : 1 ≤ e * d := by
      have := mul_pos he hd
      omega
    have hbound : (m : ℤ) ≤ e * d * (m : ℤ) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hprod (Int.natCast_nonneg m)
    have H := hm a ha
    linarith
  refine ⟨m, fun a ha => (hz a ha).trans_le (exp_le_exp.mpr (by omega)), ?_⟩
  have ht : n ^ m = torusPoint D R (c ^ m) ≫ M.torus.hom.hom := by
    have h := (markedTorusPointHom M R).map_pow c m
    rw [markedTorusPointHom_apply, markedTorusPointHom_apply] at h
    exact h.symm
  rw [ht, cocharacter_conjugates_root_word]
  change orderedRootPoint M R l z ∈ markedBorelReduction M.group B₀
  have hroot (a : D.I) (ha : a ∈ l) : markedRootPoint M R a (z a) ∈ markedBorelReduction M.group B₀ :=
    strictRoot_mem_reduction M B₀ a _ ((hz a ha).trans_le (exp_le_one_iff.mpr (by omega)))
  exact Subgroup.list_prod_mem _ (by
    intro g hg
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
    exact hroot a ha)

end MarkedReduction

section CentralPreimage

open CategoryTheory.Limits
open _root_.LinearAlgebraicGroups.Specs.SchemeDerivedGroup (FactorsThrough IsSubgroupOf)
open _root_.LinearAlgebraicGroups.Specs.CentralIsogenies (IsTorusRestriction)
open private schemeKernel_sections from LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private descendAffine descendClosedFactor pushforwardNormalizes from
  LinearAlgebraicGroups.Classification.CentralIsogenies
open private centralizes_iff from LinearAlgebraicGroups.Affine.Stabilizers

set_option backward.isDefEq.respectTransparency false in
theorem centralTorusAndNormalizerPreimages : CentralTorusAndNormalizerPreimages.{u} := by
  intro k _ G H T U f fT hf Z hZ hZT
  haveI : IsClosedImmersion T.inclusion.hom.hom.left := T.isClosedImmersion
  haveI : IsClosedImmersion U.inclusion.hom.hom.left := U.isClosedImmersion
  haveI : Mono T.inclusion.hom.hom := Over.mono_of_mono_left _
  haveI : Mono U.inclusion.hom.hom := Over.mono_of_mono_left _
  haveI : IsAffine G.val.X.left := G.property.1
  haveI : IsAffine H.val.X.left := H.property.1
  haveI : IsAffine T.group.X.left := isAffine_of_isAffineHom T.inclusion.hom.hom.left
  haveI : IsAffine U.group.X.left := isAffine_of_isAffineHom U.inclusion.hom.hom.left
  haveI : Flat fT.hom.hom.left := hf.2.1
  haveI : Surjective fT.hom.hom.left := hf.2.2
  have hcomm : fT.hom.hom ≫ U.inclusion.hom.hom =
      T.inclusion.hom.hom ≫ f.hom.hom :=
    congrArg (fun q : T.group ⟶ H.val => q.hom.hom) hf.1
  have htor (X : SchemeOver k) [IsAffine X.left] (g : X ⟶ G.val.X) :
      FactorsThrough U (g ≫ f.hom.hom) ↔ FactorsThrough T g := by
    constructor
    · rintro ⟨s, hs⟩
      change s ≫ U.inclusion.hom.hom = g ≫ f.hom.hom at hs
      let V := pullback fT.hom.hom s
      let z : V ⟶ T.group.X := pullback.fst _ _
      let p : V ⟶ X := pullback.snd _ _
      have hp : IsPullback z.left p.left fT.hom.hom.left s.left :=
        (IsPullback.of_hasPullback fT.hom.hom s).map (Over.forget _)
      haveI : Flat p.left := MorphismProperty.of_isPullback (P := @Flat) hp hf.2.1
      haveI : Surjective p.left :=
        MorphismProperty.of_isPullback (P := (@Surjective : MorphismProperty Scheme.{u})) hp hf.2.2
      haveI : IsAffineHom p.left :=
        MorphismProperty.of_isPullback (P := @IsAffineHom) hp inferInstance
      haveI : IsAffine V.left := isAffine_of_isAffineHom p.left
      let y := z ≫ T.inclusion.hom.hom
      have hz : y ≫ f.hom.hom = (p ≫ g) ≫ f.hom.hom := by
        have hc : z ≫ fT.hom.hom = p ≫ s := pullback.condition
        rw [Category.assoc, ← hcomm, ← Category.assoc, hc, Category.assoc, hs, Category.assoc]
      have hker : ((p ≫ g) * y⁻¹) ≫ f.hom.hom = 1 := by
        rw [MonObj.mul_comp, GrpObj.inv_comp, ← hz, mul_inv_cancel]
      obtain ⟨z₁, hz₁⟩ := (schemeKernel_sections hZ _).mpr hker
      change z₁ ≫ Z.inclusion.hom.hom = (p ≫ g) * y⁻¹ at hz₁
      obtain ⟨j, hj⟩ := hZT
      have ht : (z₁ ≫ j.hom.hom) ≫ T.inclusion.hom.hom = (p ≫ g) * y⁻¹ := by
        rw [Category.assoc, ← Grp.comp_hom_hom, hj, hz₁]
      have ha : ((z₁ ≫ j.hom.hom) * z) ≫ T.inclusion.hom.hom = p ≫ g := by
        rw [MonObj.mul_comp, ht]
        change (p ≫ g) * y⁻¹ * y = p ≫ g
        exact inv_mul_cancel_right _ _
      exact descendClosedFactor p T.inclusion.hom.hom g _ ha
    · rintro ⟨t, ht⟩
      change t ≫ T.inclusion.hom.hom = g at ht
      refine ⟨t ≫ fT.hom.hom, ?_⟩
      change (t ≫ fT.hom.hom) ≫ U.inclusion.hom.hom = _
      rw [Category.assoc, hcomm, ← Category.assoc, ht]
  refine ⟨htor, fun g => ⟨?_, ?_⟩⟩
  · intro hg
    obtain ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ := (normalizesIff k U.inclusion U.isClosedImmersion _ _).mp hg
    apply (normalizesIff k T.inclusion T.isClosedImmersion _ _).mpr
    let X := T.group.X ⊗ (𝟙_ (SchemeOver k))
    let j : X ⟶ U.group.X ⊗ (𝟙_ (SchemeOver k)) := fT.hom.hom ▷ _
    haveI : IsAffine (𝟙_ (SchemeOver k)).left := by
      change IsAffine (Spec (CommRingCat.of k))
      infer_instance
    haveI : IsAffine X.left := by dsimp only [X]; rw [Over.tensorObj_left]; infer_instance
    have hcalc (s : 𝟙_ (SchemeOver k) ⟶ G.val.X) :
        conjugateFamily T.inclusion s ≫ f.hom.hom =
          j ≫ conjugateFamily U.inclusion (s ≫ f.hom.hom) := by
      unfold conjugateFamily
      simp only [MonObj.mul_comp, GrpObj.inv_comp, MonObj.comp_mul, GrpObj.comp_inv,
        Category.assoc, j, whiskerRight_snd_assoc, whiskerRight_fst_assoc, hcomm]
    constructor
    · apply (htor X _).mp
      refine ⟨j ≫ c, ?_⟩
      change (j ≫ c) ≫ U.inclusion.hom.hom = _
      rw [Category.assoc, hc, hcalc]
    · apply (htor X _).mp
      refine ⟨j ≫ d, ?_⟩
      change (j ≫ d) ≫ U.inclusion.hom.hom = _
      rw [Category.assoc, hd, hcalc, GrpObj.inv_comp]
  · intro hg
    haveI : IsAffine (𝟙_ (SchemeOver k)).left := by
      change IsAffine (Spec (CommRingCat.of k))
      infer_instance
    exact pushforwardNormalizes T U f fT (𝟙 (𝟙_ (SchemeOver k))) g (g ≫ f.hom.hom)
      hf.1 (Category.id_comp _) hg

set_option backward.isDefEq.respectTransparency false in
theorem centralIsogenyRationalImageNormal : CentralIsogenyRationalImageNormal.{u} := by
  intro k _ G H f hf
  obtain ⟨_, hflat, hsurj, Z, hZ, hcentral⟩ := hf
  constructor
  rintro _ ⟨x, rfl⟩ a
  let Y := 𝟙_ (SchemeOver k)
  let V := pullback f.hom.hom a
  let v : V ⟶ G.val.X := pullback.fst _ _
  let p : V ⟶ Y := pullback.snd _ _
  have hv : v ≫ f.hom.hom = p ≫ a := pullback.condition
  have hp : IsPullback v.left p.left f.hom.hom.left a.left :=
    (IsPullback.of_hasPullback f.hom.hom a).map (Over.forget _)
  haveI : IsAffine G.val.X.left := G.property.1
  haveI : IsAffine H.val.X.left := H.property.1
  haveI : IsAffine Y.left := by
    change IsAffine (Spec (CommRingCat.of k))
    infer_instance
  haveI : Flat p.left := MorphismProperty.of_isPullback (P := @Flat) hp hflat
  haveI : Surjective p.left :=
    MorphismProperty.of_isPullback (P := (@Surjective : MorphismProperty Scheme.{u})) hp hsurj
  haveI : IsAffineHom p.left := MorphismProperty.of_isPullback (P := @IsAffineHom) hp inferInstance
  haveI : IsAffine V.left := isAffine_of_isAffineHom p.left
  let y := v * (p ≫ x) * v⁻¹
  obtain ⟨b, hb⟩ := descendAffine p y (by
    intro A r s hrs
    let z := (s ≫ v)⁻¹ * (r ≫ v)
    have hr : (r ≫ v) ≫ f.hom.hom = (s ≫ v) ≫ f.hom.hom := by
      calc
        (r ≫ v) ≫ f.hom.hom = (r ≫ p) ≫ a := by
          rw [Category.assoc, hv, ← Category.assoc]
        _ = (s ≫ p) ≫ a := congrArg (· ≫ a) hrs
        _ = (s ≫ v) ≫ f.hom.hom := by
          exact (Category.assoc s v _).symm ▸
            ((Category.assoc s p a).trans (congrArg (fun g => s ≫ g) hv.symm))
    have hz : z ≫ f.hom.hom = 1 := by
      dsimp only [z]
      rw [MonObj.mul_comp, GrpObj.inv_comp, hr, inv_mul_cancel]
    obtain ⟨c, hc⟩ := (schemeKernel_sections hZ z).mpr hz
    change c ≫ Z.inclusion.hom.hom = z at hc
    have hcomm : Commute z ((s ≫ p) ≫ x) := by
      rw [← hc]
      simpa only [Grp.id_hom_hom, Category.comp_id] using
        (centralizes_iff (𝟙 G.val) Z.inclusion.hom.hom).mp hcentral A c ((s ≫ p) ≫ x)
    have hr' : r ≫ v = (s ≫ v) * z := (mul_inv_cancel_left _ _).symm
    dsimp only [y]
    simp only [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc _ p x, hrs]
    rw [hr', mul_inv_rev]
    calc
      (s ≫ v) * z * ((s ≫ p) ≫ x) * (z⁻¹ * (s ≫ v)⁻¹) =
          (s ≫ v) * (z * ((s ≫ p) ≫ x) * z⁻¹) * (s ≫ v)⁻¹ := by
        simp only [mul_assoc]
      _ = (s ≫ v) * ((s ≫ p) ≫ x) * (s ≫ v)⁻¹ := by
        rw [hcomm.eq, mul_assoc ((s ≫ p) ≫ x), mul_inv_cancel, mul_one])
  refine ⟨b, ?_⟩
  change b ≫ f.hom.hom = a * (x ≫ f.hom.hom) * a⁻¹
  haveI : Epi p.left := Flat.epi_of_flat_of_surjective p.left
  apply Over.OverMorphism.ext
  apply (cancel_epi p.left).mp
  change (p ≫ b ≫ f.hom.hom).left = (p ≫ (a * (x ≫ f.hom.hom) * a⁻¹)).left
  congr 1
  rw [← Category.assoc, hb, MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv,
    MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, hv, Category.assoc]

end CentralPreimage

section BorelCoordinates

open _root_.LinearAlgebraicGroups.Specs.IntegralSemisimpleModel
open _root_.LinearAlgebraicGroups.Specs.ExceptionalMarkedRootDescent
open _root_.LinearAlgebraicGroups.Specs.AdjointRepresentation (GroupPoints)
open _root_.LinearAlgebraicGroups.Specs.BorelsAndChambers (subgroupRoots)
open _root_.LinearAlgebraicGroups.Specs.OrderedRootProducts (Enumerates)
open _root_.LinearAlgebraicGroups.Specs.RootGroups (rootPoint)
open _root_.LinearAlgebraicGroups.CocharacterDynamics (multiplyFactors)
open private basedIso_pos_iff base_isPos_iff_subgroupRoots from
  LinearAlgebraicGroups.Classification.PinnedEquivalence
open private fibrePointEquiv fibrePointEquiv_apply markedTorusEquiv markedTorusIncl from
  LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
open private rootPoint_surjective from LinearAlgebraicGroups.RootData.OrderedRootProducts
open private rootPoint_comp from LinearAlgebraicGroups.RootData.RootGroups

attribute [local instance] integerAlgebra

set_option backward.isDefEq.respectTransparency false in
private theorem markedProduct_range {k : Type u} [Field k] {D : Pinning.BasedRootDatum.{u}}
    {M : Model D} (C : MarkedFibre M k) (R : TestAlgebra k) :
    let P := C.realization.pinned
    let U := P.roots
    let e := C.realization.datumIso.val.indexEquiv
    let S := CommAlgCat.of Integers.{u} R
    ∀ l : List D.I, l.Nodup →
      Set.range (fun p : Points
        (OrderedRootProducts.product (fun a => (U a).val.group.X) (l.map e)) R =>
        fibrePointEquiv C R (p ≫ OrderedRootProducts.rootProduct U (l.map e))) =
      Set.range (orderedRootPoint M.toIntegralMarking S l) := by
  classical
  intro P U e S l hl
  have hroot (a : D.I) (x : R) :
      fibrePointEquiv C R (rootPoint (C.coordinate a).val.hom R x ≫
        (U (e a)).val.inclusion.hom.hom) = markedRootPoint M.toIntegralMarking S a x := by
    rw [← rootPoint_comp, fibrePointEquiv_apply]
    exact C.root_eval a R x
  induction l with
  | nil =>
    ext g
    constructor
    · rintro ⟨p, rfl⟩
      use 0
      change 1 = fibrePointEquiv C R (p ≫ (1 : 𝟙_ (SchemeOver k) ⟶ P.pair.G.val.X))
      rw [MonObj.comp_one, map_one]
    · rintro ⟨v, rfl⟩
      use toUnit _
      change fibrePointEquiv C R ((toUnit _) ≫ (1 : 𝟙_ (SchemeOver k) ⟶ P.pair.G.val.X)) = 1
      rw [MonObj.comp_one, map_one]
  | cons a l ih =>
    ext g
    let X := (testSpec k).obj (Opposite.op R)
    let H := (U (e a)).val.group.X
    let Z := OrderedRootProducts.product (fun a => (U a).val.group.X) (l.map e)
    have hprod (p : X ⟶ H ⊗ Z) :
        fibrePointEquiv C R (p ≫ OrderedRootProducts.rootProduct U ((a :: l).map e)) =
          fibrePointEquiv C R (p ≫ fst H Z ≫ (U (e a)).val.inclusion.hom.hom) *
          fibrePointEquiv C R ((p ≫ snd H Z) ≫ OrderedRootProducts.rootProduct U (l.map e)) := by
      change fibrePointEquiv C R (p ≫ (_ * _)) = _
      rw [MonObj.comp_mul, map_mul, Category.assoc]
    have ih' := ih hl.of_cons
    constructor
    · rintro ⟨p, rfl⟩
      obtain ⟨z, hz⟩ := rootPoint_surjective (C.coordinate a).val R (p ≫ fst H Z)
      obtain ⟨v, hv⟩ := Set.ext_iff.mp ih' _
        |>.mp ⟨p ≫ snd H Z, rfl⟩
      use Function.update v a z
      change orderedRootPoint M.toIntegralMarking S l v =
        fibrePointEquiv C R ((p ≫ snd H Z) ≫ OrderedRootProducts.rootProduct U (l.map e)) at hv
      change _ = fibrePointEquiv C R (p ≫ OrderedRootProducts.rootProduct U ((a :: l).map e))
      rw [hprod, ← Category.assoc p, ← hz, hroot, ← hv]
      simp only [orderedRootPoint, List.map_cons, List.prod_cons, Function.update_self]
      congr 1
      apply congrArg List.prod
      apply List.map_congr_left
      intro i hi
      have hne : i ≠ a := fun h => (List.nodup_cons.mp hl).1 (h ▸ hi)
      rw [Function.update_of_ne hne]
    · rintro ⟨v, rfl⟩
      obtain ⟨p, hp⟩ := Set.ext_iff.mp ih' _
        |>.mpr ⟨v, rfl⟩
      let v₀ := rootPoint (C.coordinate a).val.hom R (v a)
      change fibrePointEquiv C R (p ≫ OrderedRootProducts.rootProduct U (l.map e)) =
        orderedRootPoint M.toIntegralMarking S l v at hp
      use lift v₀ p
      change fibrePointEquiv C R (lift v₀ p ≫ OrderedRootProducts.rootProduct U ((a :: l).map e)) = _
      rw [hprod, lift_fst_assoc, lift_snd, hroot, hp]
      rfl

set_option backward.isDefEq.respectTransparency false in
theorem markedPositiveBorelCoordinates : MarkedPositiveBorelCoordinates.{u} := by
  classical
  intro k _ D M C R l hl S
  let P := C.realization.pinned
  let B := P.pair.B
  let T := P.pair.T
  let U := P.roots
  let e := C.realization.datumIso.val.indexEquiv
  obtain ⟨_, _, _, hcor, _, _, hdecomp⟩ :=
    RootData.BorelPositivity.borelPositivity P.pair.G P.pair.reductive T P.pair.split P.pair.maximal
  obtain ⟨J, j, q, _, _, hj, _, _, hmul, hprod⟩ :=
    hdecomp B P.pair.borel P.pair.containsTorus
  have hp := hcor.1 B P.pair.borel P.pair.containsTorus
  have hl' : Enumerates (l.map e) (subgroupRoots T B) := by
    refine ⟨hl.1.map e.injective, fun a => ?_⟩
    obtain ⟨i, rfl⟩ := e.surjective a
    rw [List.mem_map_of_injective e.injective, hl.2 i]
    exact (basedIso_pos_iff C.realization.datumIso i).trans
      (base_isPos_iff_subgroupRoots C.realization.attached hp (e i))
  obtain ⟨p, hp⟩ := hprod U (l.map e) hl'
  let f := multiplyFactors j J.inclusion
  haveI : IsIso f := hmul
  have hj' : j.hom.hom ≫ B.inclusion.hom.hom = T.inclusion.hom.hom :=
    congrArg (fun z : T.group ⟶ P.pair.G.val => z.hom.hom) hj
  let X := (testSpec k).obj (Opposite.op R)
  let φ := fibrePointEquiv C R
  have htor (t : X ⟶ T.group.X) :
      φ (t ≫ T.inclusion.hom.hom) = markedTorusEquiv C R t ≫ M.torus.hom.hom :=
    markedTorusIncl C R t
  have hmul' (t : X ⟶ T.group.X) (s : X ⟶ J.group.X) :
      φ ((lift t s ≫ f) ≫ B.inclusion.hom.hom) =
        (markedTorusEquiv C R t ≫ M.torus.hom.hom) *
          φ (s ≫ J.inclusion.hom.hom ≫ B.inclusion.hom.hom) := by
    simp only [f, multiplyFactors, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc,
      MonObj.mul_comp, map_mul, Category.assoc, hj', htor]
  have hf : Function.Surjective (fun t : (X ⟶ T.group.X) × (X ⟶ J.group.X) => lift t.1 t.2 ≫ f) := by
    intro b
    let x := b ≫ inv f
    refine ⟨⟨x ≫ fst _ _, x ≫ snd _ _⟩, ?_⟩
    change lift (x ≫ fst _ _) (x ≫ snd _ _) ≫ f = b
    rw [← comp_lift, lift_fst_snd, Category.comp_id, show x = b ≫ inv f by rfl, Category.assoc, IsIso.inv_hom_id,
      Category.comp_id]
  ext g
  constructor
  · rintro ⟨b, rfl⟩
    obtain ⟨⟨t, s⟩, rfl⟩ := hf b
    let a := s ≫ p.inv
    have ha : a ≫ OrderedRootProducts.rootProduct U (l.map e) =
        s ≫ J.inclusion.hom.hom ≫ B.inclusion.hom.hom := by
      rw [← hp, ← Category.assoc a, show a ≫ p.hom = s by simp [a]]
    obtain ⟨v, hv⟩ := Set.ext_iff.mp (markedProduct_range C R l hl.1) _
      |>.mp ⟨a, congrArg φ ha⟩
    refine ⟨⟨markedTorusEquiv C R t, v⟩, ?_⟩
    change (markedTorusEquiv C R t ≫ M.torus.hom.hom) *
      orderedRootPoint M.toIntegralMarking S l v = φ ((lift t s ≫ f) ≫ B.inclusion.hom.hom)
    rw [hmul' t s, hv]
  · rintro ⟨⟨t, v⟩, rfl⟩
    obtain ⟨s, hs⟩ := Set.ext_iff.mp (markedProduct_range C R l hl.1) _
      |>.mpr ⟨v, rfl⟩
    obtain ⟨t', ht'⟩ := (markedTorusEquiv C R).surjective t
    refine ⟨lift t' (s ≫ p.hom) ≫ f, ?_⟩
    change φ ((lift t' (s ≫ p.hom) ≫ f) ≫ B.inclusion.hom.hom) = _
    change φ (s ≫ OrderedRootProducts.rootProduct U (l.map e)) =
      orderedRootPoint M.toIntegralMarking S l v at hs
    rw [hmul', ht', Category.assoc s, hp, hs]

end BorelCoordinates

section DepthCoordinates

open _root_.LinearAlgebraicGroups.Specs.IntegralSemisimpleModel
open _root_.LinearAlgebraicGroups.Specs.ExceptionalMarkedRootDescent
open _root_.LinearAlgebraicGroups.Specs.OrderedRootProducts (Enumerates)
open _root_.LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent (markedCellCoordinates)
open private rootFactorPoint rootFactorPoint_eq lift_cellMap_eq orderedRootPoint_map
  markedTorusPoint_map markedRootPoint_zero from
  LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
open private additivePoint_surjective from LinearAlgebraicGroups.Classification.IntegralFibreRootCoordinates
open private affineTorusPointEquiv from LinearAlgebraicGroups.Classification.IntegralSemisimpleModel

attribute [local instance] integerAlgebra

private theorem rootFactorPoint_congr {D : Pinning.BasedRootDatum.{u}}
    (M : IntegralMarking D) (R : IntegralAlgebra.{u}) (l : List D.I)
    (z w : D.I → R) (h : ∀ i ∈ l, z i = w i) :
    rootFactorPoint M R z l = rootFactorPoint M R w l := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change lift (M.line.point R (z i)) (rootFactorPoint M R z l) =
      lift (M.line.point R (w i)) (rootFactorPoint M R w l)
    rw [h i List.mem_cons_self, ih (fun i hi => h i (List.mem_cons_of_mem _ hi))]

set_option backward.isDefEq.respectTransparency false in
private theorem rootFactorPoint_surjective {D : Pinning.BasedRootDatum.{u}}
    (M : IntegralMarking D) (R : IntegralAlgebra.{u}) (l : List D.I) (hl : l.Nodup) :
    Function.Surjective (fun z : D.I → R => rootFactorPoint M R z l) := by
  classical
  induction l with
  | nil =>
    intro p
    exact ⟨0, toUnit_unique _ _⟩
  | cons a l ih =>
    intro p
    obtain ⟨z, hz⟩ := additivePoint_surjective R (p ≫ fst _ _)
    obtain ⟨w, hw⟩ := ih hl.of_cons (p ≫ snd _ _)
    refine ⟨Function.update w a z, ?_⟩
    apply CartesianMonoidalCategory.hom_ext
    · simpa only [rootFactorPoint, lift_fst, Function.update_self] using hz
    · simp only [rootFactorPoint, lift_snd]
      rw [← hw]
      apply rootFactorPoint_congr
      intro i hi
      have hne : i ≠ a := fun h => (List.nodup_cons.mp hl).1 (h ▸ hi)
      exact Function.update_of_ne hne z w

private theorem orderedRootPoint_eq_one_of_zero {D : Pinning.BasedRootDatum.{u}}
    (M : IntegralMarking D) (R : IntegralAlgebra.{u}) (l : List D.I)
    (z : D.I → R) (hz : ∀ a ∈ l, z a = 0) : orderedRootPoint M R l z = 1 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    change markedRootPoint M R a (z a) * orderedRootPoint M R l z = 1
    rw [hz a List.mem_cons_self, markedRootPoint_zero,
      ih (fun b hb => hz b (List.mem_cons_of_mem _ hb)), one_mul]

private theorem markedCellPoint_map {D : Pinning.BasedRootDatum.{u}} (M : IntegralMarking D)
    {R S : IntegralAlgebra.{u}} (f : R ⟶ S) (l r : List D.I)
    (z : D.I → R) (t : IntegralPoints (splitTorus D) R) :
    (integralPointFunctor M.group).map f (markedCellPoint M R l r z t) =
      markedCellPoint M S l r (fun a => f.hom (z a)) ((integralPointFunctor (splitTorus D)).map f t) := by
  let j : IntegralPoints M.group R →* IntegralPoints M.group S :=
    ((integralPointFunctor M.group).map f).hom
  change j (orderedRootPoint M R l z * ((t ≫ M.torus.hom.hom) * orderedRootPoint M R r z)) =
    markedCellPoint M S l r (fun a => f.hom (z a)) ((integralPointFunctor (splitTorus D)).map f t)
  rw [map_mul, map_mul]
  change (integralPointFunctor M.group).map f (orderedRootPoint M R l z) *
    ((integralPointFunctor M.group).map f (t ≫ M.torus.hom.hom) *
      (integralPointFunctor M.group).map f (orderedRootPoint M R r z)) = _
  rw [orderedRootPoint_map, markedTorusPoint_map, orderedRootPoint_map]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem iwahoriDepthCoordinates : IwahoriDepthCoordinates.{u} := by
  classical
  intro K _ _ D M O κ C B hB l r hl hr g
  let A := CommAlgCat.of Integers.{u} O
  let S := CommAlgCat.of Integers.{u} κ
  let red := residueReduction K
  let redG := ((integralPointFunctor M.group).map red).hom
  let redT := ((integralPointFunctor (splitTorus D)).map red).hom
  let c := cellMap M.line M.torus M.root l r
  have hB' : (B : Set (IntegralPoints M.group S)) =
      Set.range (fun q : IntegralPoints (splitTorus D) S × (D.I → S) =>
        (q.1 ≫ M.torus.hom.hom) * orderedRootPoint M.toIntegralMarking S r q.2) :=
    hB.trans (markedPositiveBorelCoordinates C (CommAlgCat.of κ κ) r hr)
  have hopen : IsOpenImmersion c.left := M.openCell l r hl hr
  have hchart (z : D.I → S) (t : IntegralPoints (splitTorus D) S)
      (hz : ∀ a ∈ l, z a = 0) :
      markedCellPoint M.toIntegralMarking S l r z t =
        (t ≫ M.torus.hom.hom) * orderedRootPoint M.toIntegralMarking S r z := by
    unfold markedCellPoint
    rw [orderedRootPoint_eq_one_of_zero _ _ _ _ hz, one_mul]
  constructor
  · rintro ⟨a, ha, hag⟩
    change IntegralPoints M.group A at a
    have ha' : redG a ∈ B := ha
    have hrng : (redG a : IntegralPoints M.group S) ∈ (B : Set (IntegralPoints M.group S)) := ha'
    rw [hB'] at hrng
    obtain ⟨⟨t, w⟩, hw⟩ := hrng
    let w₀ (i : D.I) : S := if D.base.IsPos i then w i else 0
    have hzero (i : D.I) (hi : i ∈ l) : w₀ i = 0 := if_neg ((hl.2 i).mp hi)
    have heq : orderedRootPoint M.toIntegralMarking S r w₀ =
        orderedRootPoint M.toIntegralMarking S r w := by
      apply congrArg List.prod
      exact List.map_congr_left (fun i hi => congrArg (markedRootPoint M.toIntegralMarking S i)
        (if_pos ((hr.2 i).mp hi)))
    have hcell : markedCellPoint M.toIntegralMarking S l r w₀ t = redG a := by
      rw [hchart w₀ t hzero, heq]
      exact hw
    have hf := lift_cellMap_eq M.toIntegralMarking S w₀ t l r
    have hpt : a.left (IsLocalRing.closedPoint O) ∈ Set.range c.left := by
      let x := IsLocalRing.closedPoint κ
      have hh : (integralSpec.map red.op).left x = IsLocalRing.closedPoint O :=
        IsLocalRing.PrimeSpectrum.comap_residue O x
      rw [← hh]
      have hleft : (integralSpec.map red.op ≫ a).left =
          (lift (rootFactorPoint M.toIntegralMarking S w₀ l)
            (lift t (rootFactorPoint M.toIntegralMarking S w₀ r)) ≫ c).left :=
        congrArg Over.Hom.left (hcell.symm.trans hf.symm)
      exact ⟨(lift (rootFactorPoint M.toIntegralMarking S w₀ l)
        (lift t (rootFactorPoint M.toIntegralMarking S w₀ r))).left x,
        (congrArg (fun p : (integralSpec.obj (Opposite.op S)).left ⟶ M.group.X.left =>
          p x) hleft).symm⟩
    have hsub : Set.range a.left ⊆ Set.range c.left := by
      rintro _ ⟨x, rfl⟩
      have hx : (x : PrimeSpectrum O) ⤳ IsLocalRing.closedPoint O :=
        IsLocalRing.specializes_closedPoint (R := O) x
      exact (hx.map a.left.continuous).mem_open (IsOpenImmersion.isOpen_range c.left) hpt
    let f := IsOpenImmersion.lift c.left a.left hsub
    have hf' : f ≫ c.left = a.left := IsOpenImmersion.lift_fac _ _ _
    let a₀ : integralSpec.obj (Opposite.op A) ⟶ _ :=
      Over.homMk f (by
        calc
          f ≫ _ = f ≫ (c.left ≫ M.group.X.hom) :=
            congrArg (fun h => f ≫ h) (Over.w c).symm
          _ = (f ≫ c.left) ≫ M.group.X.hom := (Category.assoc _ _ _).symm
          _ = a.left ≫ M.group.X.hom := congrArg (fun h => h ≫ _) hf'
          _ = _ := Over.w a)
    have ha₀ : a₀ ≫ c = a := Over.OverMorphism.ext hf'
    obtain ⟨v₁, hv₁⟩ := rootFactorPoint_surjective M.toIntegralMarking A l hl.1 (a₀ ≫ fst _ _)
    obtain ⟨v₂, hv₂⟩ := rootFactorPoint_surjective M.toIntegralMarking A r hr.1
      (a₀ ≫ snd _ _ ≫ snd _ _)
    let z (i : D.I) : A := if D.base.IsPos i then v₂ i else v₁ i
    let u := a₀ ≫ snd _ _ ≫ fst _ _
    have h1 : rootFactorPoint M.toIntegralMarking A z l = a₀ ≫ fst _ _ :=
      (rootFactorPoint_congr _ _ _ _ _ (fun i hi => if_neg ((hl.2 i).mp hi))).trans hv₁
    have h2 : rootFactorPoint M.toIntegralMarking A z r = a₀ ≫ snd _ _ ≫ snd _ _ :=
      (rootFactorPoint_congr _ _ _ _ _ (fun i hi => if_pos ((hr.2 i).mp hi))).trans hv₂
    have hprod : lift (a₀ ≫ fst _ _) (lift u (a₀ ≫ snd _ _ ≫ snd _ _)) = a₀ := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [lift_fst]
      · rw [lift_snd]
        apply CartesianMonoidalCategory.hom_ext
        · rw [lift_fst]
          exact (Category.assoc _ _ _).symm
        · rw [lift_snd, Category.assoc]
    have hz : markedCellPoint M.toIntegralMarking A l r z u = a := by
      rw [← lift_cellMap_eq, h1, h2, hprod]
      exact ha₀
    have hcomp : (fun i => red.hom (z i), redT u) = (w₀, t) :=
      (markedCellCoordinates M.toIntegralMarking S l r hl hr).1
        ((markedCellPoint_map M.toIntegralMarking red l r z u).symm.trans
          ((congrArg redG hz).trans hcell.symm))
    obtain ⟨t₀, ht₀⟩ := (affineTorusPointEquiv (k := Integers.{u}) (M := Multiplicative D.X) A).surjective u
    change torusPoint D A t₀ = u at ht₀
    refine ⟨z, t₀, ?_, ?_⟩
    · intro i hi
      apply (Valuation.mem_maximalIdeal_iff K (valuation K)).mp
      apply (IsLocalRing.residue_eq_zero_iff (z i)).mp
      exact (congrFun (congrArg Prod.fst hcomp) i).trans (hzero i hi)
    · rw [ht₀, hz]
      exact hag
  · rintro ⟨z, t, hz, h⟩
    let u := torusPoint D A t
    refine ⟨markedCellPoint M.toIntegralMarking A l r z u, ?_, h⟩
    have hz₀ (i : D.I) (hi : i ∈ l) : red.hom (z i) = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).mpr ((Valuation.mem_maximalIdeal_iff K (valuation K)).mpr (hz i hi))
    change redG _ ∈ B
    have hred : redG (markedCellPoint M.toIntegralMarking A l r z u) =
        ((redT u ≫ M.torus.hom.hom) : IntegralPoints M.group S) *
          orderedRootPoint M.toIntegralMarking S r (fun i => red.hom (z i)) :=
      (markedCellPoint_map M.toIntegralMarking red l r z u).trans (hchart _ _ hz₀)
    change (redG (markedCellPoint M.toIntegralMarking A l r z u) : IntegralPoints M.group S) ∈
      (B : Set (IntegralPoints M.group S))
    rw [hB', hred]
    exact ⟨(redT u, fun i => red.hom (z i)), rfl⟩

end DepthCoordinates

section OrderedDepthCoordinates

open _root_.LinearAlgebraicGroups.Specs.IntegralSemisimpleModel
open _root_.LinearAlgebraicGroups.Specs.ExceptionalMarkedRootDescent
open _root_.LinearAlgebraicGroups.Specs.ExceptionalValuedTorusNormalizer (valuationRingInclusion)
open _root_.LinearAlgebraicGroups.Specs.OrderedRootProducts (Enumerates)
open private reverseCellPoint_eq markedAbsoluteCell_injective from
  LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
open private affineTorusPointEquiv from LinearAlgebraicGroups.Classification.IntegralSemisimpleModel

attribute [local instance] integerAlgebra

set_option backward.isDefEq.respectTransparency false in
theorem iwahoriOrderedCoordinates : IwahoriOrderedCoordinates.{u} := by
  intro K _ _ D M O κ C B hB l r hl hr positiveFirst chart
  let R := CommAlgCat.of Integers.{u} O
  refine ⟨markedAbsoluteCell_injective M.toIntegralMarking R l r hl hr positiveFirst, ?_⟩
  cases positiveFirst
  · exact iwahoriDepthCoordinates C B hB l r hl hr
  · have hl' : Enumerates l.reverse {a | ¬ D.base.IsPos a} :=
      ⟨List.nodup_reverse.mpr hl.1, fun a => List.mem_reverse.trans (hl.2 a)⟩
    have hr' : Enumerates r.reverse {a | D.base.IsPos a} :=
      ⟨List.nodup_reverse.mpr hr.1, fun a => List.mem_reverse.trans (hr.2 a)⟩
    let inc : IntegralPoints M.group R →*
        IntegralPoints M.group (CommAlgCat.of Integers.{u} K) :=
      ((integralPointFunctor M.group).map (valuationRingInclusion K)).hom
    have hmap (z : D.I → O) (t : TorusValues D R) :
        inc (chart (z, torusPoint D R t)) =
          (inc (markedCellPoint M.toIntegralMarking R l.reverse r.reverse
            (fun a => -z a) (torusPoint D R t⁻¹)))⁻¹ := by
      have ht : torusPoint D R t⁻¹ = (torusPoint D R t)⁻¹ :=
        (affineTorusPointEquiv (k := Integers.{u}) (M := Multiplicative D.X) R).map_inv t
      rw [ht, ← map_inv]
      change inc (orderedRootPoint M.toIntegralMarking R r z *
        ((torusPoint D R t ≫ M.torus.hom.hom) * orderedRootPoint M.toIntegralMarking R l z)) = _
      congr 1
      simpa only [List.reverse_reverse] using
        reverseCellPoint_eq M.toIntegralMarking R l.reverse r.reverse z (torusPoint D R t)
    intro g
    rw [← (markedBorelReduction M.group B).inv_mem_iff (x := g)]
    rw [iwahoriDepthCoordinates C B hB l.reverse r.reverse hl' hr' g⁻¹]
    constructor
    · rintro ⟨z, t, hz, he⟩
      refine ⟨fun a => -z a, t⁻¹, fun a ha => ?_, ?_⟩
      · simpa only [NegMemClass.coe_neg, Valuation.map_neg] using hz a (List.mem_reverse.mpr ha)
      · change inc (chart ((fun a => -z a), torusPoint D R t⁻¹)) = g
        let t' : TorusValues D R := t
        have he' : inc (markedCellPoint M.toIntegralMarking R l.reverse r.reverse z (torusPoint D R t')) =
            g⁻¹ := he
        change inc (chart ((fun a => -z a), torusPoint D R t'⁻¹)) = g
        calc
          _ = _ := hmap (fun a => -z a) t'⁻¹
          _ = (inc (markedCellPoint M.toIntegralMarking R l.reverse r.reverse z
              (torusPoint D R t')))⁻¹ :=
            congrArg₂ (fun (v : D.I → O) (s : TorusValues D R) =>
              (inc (markedCellPoint M.toIntegralMarking R l.reverse r.reverse v (torusPoint D R s)))⁻¹)
              (funext (fun a => neg_neg (z a))) (inv_inv t')
          _ = g := by rw [he', inv_inv]
    · rintro ⟨z, t, hz, he⟩
      refine ⟨fun a => -z a, t⁻¹, fun a ha => ?_, ?_⟩
      · simpa only [NegMemClass.coe_neg, Valuation.map_neg] using hz a (List.mem_reverse.mp ha)
      · change inc (chart (z, torusPoint D R t)) = g at he
        rw [hmap] at he
        change inc (markedCellPoint M.toIntegralMarking R l.reverse r.reverse
          (fun a => -z a) (torusPoint D R t⁻¹)) = g⁻¹
        apply inv_injective
        rwa [inv_inv]

end OrderedDepthCoordinates

section Generation

open _root_.LinearAlgebraicGroups.Specs.IntegralSemisimpleModel
open _root_.LinearAlgebraicGroups.Specs.ExceptionalMarkedRootDescent
open _root_.LinearAlgebraicGroups.Specs.SchemeDerivedGroup (IsSubgroupOf)
open _root_.LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent (wallDepths)
open _root_.LinearAlgebraicGroups.Arithmetic.ExceptionalValuedTorusNormalizer (invariantRegularCocharacter)
open _root_.LinearAlgebraicGroups.Specs.GeometricBorelConjugacy (IsKBorel)
open _root_.LinearAlgebraicGroups.Specs.Relative.MaximalSplitTori (IsMinimalParabolic IsMaximalSplitTorus)
open _root_.LinearAlgebraicGroups.Specs.OrderedRootProducts (Enumerates)
open private groundIso from LinearAlgebraicGroups.Solvable.TorusSections
open private subgroup_descend subgroup_extend extendSubgroup from LinearAlgebraicGroups.RootData.BorelNormalizer
open private subgroupOf_trans from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private groundBorelSmooth from LinearAlgebraicGroups.Descent.AdjointBorelCohomology
open private isTorus_of_split from LinearAlgebraicGroups.Descent.FiniteFieldFlags
open private maximalTorus_of_geometricallyMaximal from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private subgroup_normalizes from LinearAlgebraicGroups.RootData.BorelNormalizer
open private fibrePointEquiv fibrePointEquiv_apply markedTorusEquiv markedTorusIncl from
  LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent

attribute [local instance] integerAlgebra

private def groundSectionsEquiv {k : Type u} [Field k] (G : GroupScheme k) :
    (𝟙_ (SchemeOver k) ⟶ G.X) ≃*
      ((testSpec k).obj (Opposite.op (CommAlgCat.of k k)) ⟶ G.X) :=
  let i : (testSpec k).obj (Opposite.op (CommAlgCat.of k k)) ≅ 𝟙_ (SchemeOver k) :=
    groundIso (k := k)
  { toEquiv := i.symm.homFromEquiv
    map_mul' := fun g h => MonObj.comp_mul i.hom g h }

private theorem groundSectionsEquiv_apply {k : Type u} [Field k]
    (G : GroupScheme k) (g : 𝟙_ (SchemeOver k) ⟶ G.X) :
    groundSectionsEquiv G g = toUnit _ ≫ g := by
  change (groundIso (k := k)).hom ≫ g = toUnit _ ≫ g
  have h : (groundIso (k := k)).hom = toUnit _ := Subsingleton.elim _ _
  exact congrArg (· ≫ g) h

private def markedGroundEquiv {k : Type u} [Field k] {D : Pinning.BasedRootDatum.{u}}
    {M : Model D} (C : MarkedFibre M k) :
    (𝟙_ (SchemeOver k) ⟶ C.realization.pinned.pair.G.val.X) ≃*
      IntegralPoints M.group (CommAlgCat.of Integers.{u} k) :=
  (groundSectionsEquiv _).trans (fibrePointEquiv C (CommAlgCat.of k k))

private theorem markedGroundEquiv_apply {k : Type u} [Field k] {D : Pinning.BasedRootDatum.{u}}
    {M : Model D} (C : MarkedFibre M k) (g : 𝟙_ (SchemeOver k) ⟶ C.realization.pinned.pair.G.val.X) :
    markedGroundEquiv C g = markedGroundPoint C g := by
  change fibrePointEquiv C (CommAlgCat.of k k) (groundSectionsEquiv _ g) = markedGroundPoint C g
  rw [groundSectionsEquiv_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 500000 in
theorem markedPositiveBorelSubgroup : MarkedPositiveBorelSubgroup.{u} := by
  intro k _ D M C
  let T := (testSpec k).obj (Opposite.op (CommAlgCat.of k k))
  let f := fibrePointEquiv C (CommAlgCat.of k k)
  refine ⟨(SubgroupSections C.realization.pinned.pair.B T).map f.toMonoidHom, ?_⟩
  ext g
  constructor
  · rintro ⟨_, ⟨b, rfl⟩, rfl⟩
    exact ⟨b, rfl⟩
  · rintro ⟨b, rfl⟩
    exact ⟨b ≫ C.realization.pinned.pair.B.inclusion.hom.hom, ⟨b, rfl⟩, rfl⟩

set_option backward.isDefEq.respectTransparency false in
private theorem borelMinimalParabolic {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
    (hG : GeometricRadicals.IsReductive G) (B : ClosedSubgroup G.val) (hB : IsKBorel B) :
    IsMinimalParabolic G B := by
  have hSm := groundBorelSmooth hB
  obtain ⟨ha, hb⟩ := hB
  constructor
  · exact ⟨hG, hSm, ha, _, hb, 𝟙 _, Category.id_comp _⟩
  · intro Q hQ hQB
    let K := AlgebraicClosure k
    obtain ⟨_, R, hR, hRQ⟩ := hQ.2.2
    have hRB : IsSubgroupOf R (extendSubgroup K B) := subgroupOf_trans hRQ (subgroup_extend K hQB)
    exact subgroup_descend K (subgroupOf_trans (hR.2 _ hb.1 hRB) hRQ)

private theorem splitGeometricallyMaximal {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
    (T : ClosedSubgroup G.val) (hs : GeometricRadicals.IsSplitTorus T.group)
    (hm : RankOneFlag.IsGeometricallyMaximal T) : IsMaximalSplitTorus T := by
  refine ⟨hs, ?_⟩
  intro S hS hTS
  exact (maximalTorus_of_geometricallyMaximal G T (isTorus_of_split hs) hm).2 S
    (isTorus_of_split hS) hTS

private theorem mem_of_conjugate_mem {G : Type*} [Group G] (H : Subgroup G) {x a : G}
    (ha : a ∈ H) (h : a * x * a⁻¹ ∈ H) : x ∈ H := by
  have hx := H.mul_mem (H.mul_mem (H.inv_mem ha) h) ha
  simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hx

set_option backward.isDefEq.respectTransparency false in
private theorem markedGroundTorusPoint {k : Type u} [Field k] {D : Pinning.BasedRootDatum.{u}}
    {M : Model D} (C : MarkedFibre M k)
    (t : IntegralPoints (splitTorus D) (CommAlgCat.of Integers.{u} k)) :
    let P := C.realization.pinned.pair
    ∃ c : 𝟙_ (SchemeOver k) ⟶ P.T.group.X,
      markedGroundEquiv C (c ≫ P.T.inclusion.hom.hom) = t ≫ M.torus.hom.hom := by
  intro P
  let R := CommAlgCat.of k k
  obtain ⟨b, hb⟩ := (markedTorusEquiv C R).surjective t
  obtain ⟨c, hc⟩ := (groundSectionsEquiv P.T.group).surjective b
  let Y := (testSpec k).obj (Opposite.op R)
  have hc' : toUnit Y ≫ c = b := (groundSectionsEquiv_apply P.T.group c).symm.trans hc
  refine ⟨c, (markedGroundEquiv_apply C _).trans ?_⟩
  change markedFibrePoint C R (toUnit Y ≫ (c ≫ P.T.inclusion.hom.hom)) = _
  have hcomp : toUnit Y ≫ (c ≫ P.T.inclusion.hom.hom) = b ≫ P.T.inclusion.hom.hom :=
    (Category.assoc _ _ _).symm.trans (congrArg (fun x : Y ⟶ P.T.group.X =>
      x ≫ P.T.inclusion.hom.hom) hc')
  exact (congrArg (markedFibrePoint C R) hcomp).trans ((markedTorusIncl C R b).trans
    (congrArg (fun x : IntegralPoints (splitTorus D) (CommAlgCat.of Integers.{u} k) =>
      x ≫ M.torus.hom.hom) hb))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 400000 in
theorem splitIwahoriGeneration : SplitIwahoriGeneration.{u} := by
  classical
  intro K _ _ _ _ D M C B₀ P I
  let e := markedGroundEquiv C
  have hS := splitGeometricallyMaximal P.T P.split P.maximal
  have hB := borelMinimalParabolic P.reductive P.B P.borel
  obtain ⟨Q, _⟩ := Relative.RelativeWeylScheme.finiteConstantQuotient P.G P.reductive P.T hS
  let i := pointHom Q.normalizer.inclusion (𝟙_ (SchemeOver K))
  let N := (e.toMonoidHom.comp i).range
  have hN (g : 𝟙_ (SchemeOver K) ⟶ P.G.val.X) :
      e g ∈ N ↔ Normalizes P.T.inclusion g := by
    exact ⟨fun ⟨n, hn⟩ => (Q.normalizerProperty _ _).mpr ⟨n, e.injective hn⟩,
      fun hn => by
        obtain ⟨n, hn⟩ := (Q.normalizerProperty _ _).mp hn
        exact ⟨n, congrArg e hn⟩⟩
  refine ⟨N, fun g => (markedGroundEquiv_apply C g) ▸ hN g, ?_⟩
  let H := I ⊔ N
  have hIH : I ≤ H := le_sup_left
  have hNH : N ≤ H := le_sup_right
  let R := CommAlgCat.of K K
  let S := CommAlgCat.of Integers.{u} K
  have htor (t : IntegralPoints (splitTorus D) S) : t ≫ M.torus.hom.hom ∈ N := by
    obtain ⟨c, hg⟩ := markedGroundTorusPoint C t
    change e (c ≫ P.T.inclusion.hom.hom) = _ at hg
    rw [← hg, hN]
    exact subgroup_normalizes P.T ⟨c, rfl⟩
  obtain ⟨π, hπ⟩ := (wallDepths K 1).1
  letI : Finite D.I := D.finiteRoots
  letI : Fintype D.I := Fintype.ofFinite _
  let l := (Finset.univ.filter D.base.IsPos).toList
  have hl : Enumerates l {a | D.base.IsPos a} := by
    refine ⟨Finset.nodup_toList _, fun a => ?_⟩
    simp only [l, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
  obtain ⟨y, _, hy, _⟩ := invariantRegularCocharacter D
  have hpos (a : D.I) (ha : a ∈ l) : 0 < D.datum.toLinearMap (D.datum.root a) y := by
    rw [hy]
    exact mul_pos (by decide) (D.base.isPos_iff.mp ((hl.2 a).mp ha))
  let n : IntegralPoints M.group S := torusPoint D S (cocharacter D y S π) ≫ M.torus.hom.hom
  have hn : n ∈ H := hNH (htor (torusPoint D S (cocharacter D y S π)))
  have hword (v : D.I → S) : orderedRootPoint M.toIntegralMarking S l v ∈ H := by
    obtain ⟨m, _, hm⟩ := markedRootWordContraction M.toIntegralMarking B₀ y π 1 (by decide) hπ l hpos v 0
    exact mem_of_conjugate_mem H (H.pow_mem hn m) (hIH hm)
  have hb (b : 𝟙_ (SchemeOver K) ⟶ P.B.group.X) : e (b ≫ P.B.inclusion.hom.hom) ∈ H := by
    have hb₀ : e (b ≫ P.B.inclusion.hom.hom) ∈ markedPositiveBorel C R := by
      refine ⟨toUnit _ ≫ b, ?_⟩
      rw [markedGroundEquiv_apply]
      simp only [markedGroundPoint, markedFibrePoint, Category.assoc]
      rfl
    rw [markedPositiveBorelCoordinates C R l hl] at hb₀
    obtain ⟨⟨t, v⟩, hv⟩ := hb₀
    rw [← hv]
    exact H.mul_mem (hNH (htor t)) (hword v)
  apply top_unique
  intro g _
  obtain ⟨x, rfl⟩ := e.surjective g
  obtain ⟨b, c, n, hn⟩ := rationalBorelFactorization P.G P.reductive P.T P.B hS hB
    P.containsTorus Q.normalizer Q.normalizerProperty x
  rw [hn, e.map_mul, e.map_mul]
  exact H.mul_mem (H.mul_mem (hb b) (hNH (show e (i n) ∈ N from ⟨n, rfl⟩))) (hb c)

end Generation

section IntegralImage

open _root_.LinearAlgebraicGroups.Specs.IntegralSemisimpleModel
open _root_.LinearAlgebraicGroups.Specs.ExceptionalMarkedRootDescent
open _root_.LinearAlgebraicGroups.Specs.OrderedRootProducts (Enumerates)
open _root_.LinearAlgebraicGroups.Specs.ExceptionalValuedTorusNormalizer (valuationRingInclusion)
open private affineTorusPointEquiv from LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
open private markedTorusPointHom markedTorusPointHom_apply orderedRootPoint_map from
  LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent

attribute [local instance] integerAlgebra

private theorem integralPointHom_natural {G H : IntegralGroup.{u}} (f : G ⟶ H)
    {R S : IntegralAlgebra.{u}} (a : R ⟶ S) (g : IntegralPoints G R) :
    integralPointHom f S ((integralPointFunctor G).map a g) =
      (integralPointFunctor H).map a (integralPointHom f R g) :=
  Category.assoc (integralSpec.map a.op) g f.hom.hom

private theorem orderedRootPoint_congr {D : Pinning.BasedRootDatum.{u}}
    (M : IntegralMarking D) (R : IntegralAlgebra.{u}) (l : List D.I)
    {z w : D.I → R} (h : ∀ i ∈ l, z i = w i) :
    orderedRootPoint M R l z = orderedRootPoint M R l w := by
  apply congrArg List.prod
  exact List.map_congr_left (fun a ha => congrArg (markedRootPoint M R a) (h a ha))

private theorem orderedRootPoint_image {D E : Pinning.BasedRootDatum.{u}}
    {M : Model D} {A : Model E} (f : M.group ⟶ A.group) (e : D.I ≃ E.I)
    (R : IntegralAlgebra.{u})
    (hf : ∀ a x, integralPointHom f R (markedRootPoint M.toIntegralMarking R a x) =
      markedRootPoint A.toIntegralMarking R (e a) x)
    (l : List D.I) (z : E.I → R) :
    integralPointHom f R (orderedRootPoint M.toIntegralMarking R l (z ∘ e)) =
      orderedRootPoint A.toIntegralMarking R (l.map e) z := by
  induction l with
  | nil => exact map_one _
  | cons a l ih =>
    change integralPointHom f R
        (markedRootPoint M.toIntegralMarking R a (z (e a)) *
          orderedRootPoint M.toIntegralMarking R l (z ∘ e)) =
      markedRootPoint A.toIntegralMarking R (e a) (z (e a)) *
        orderedRootPoint A.toIntegralMarking R (l.map e) z
    rw [(integralPointHom f R).map_mul, hf, ih]

private theorem markedCellPoint_image {D E : Pinning.BasedRootDatum.{u}}
    {M : Model D} {A : Model E} (f : M.group ⟶ A.group) (e : D.I ≃ E.I)
    (χ : Multiplicative E.X →* Multiplicative D.X) (h : PreservesIntegralMarking f e χ)
    (R : IntegralAlgebra.{u}) (l r : List D.I) (z : E.I → R) (t : TorusValues D R) :
    integralPointHom f R (markedCellPoint M.toIntegralMarking R l r (z ∘ e) (torusPoint D R t)) =
      markedCellPoint A.toIntegralMarking R (l.map e) (r.map e) z (torusPoint E R (t.comp χ)) := by
  unfold markedCellPoint
  rw [(integralPointHom f R).map_mul, (integralPointHom f R).map_mul,
    orderedRootPoint_image f e R (h.2.1 R), orderedRootPoint_image f e R (h.2.1 R), h.2.2]

private theorem enumerates_map {D E : Pinning.BasedRootDatum.{u}} (e : D.I ≃ E.I)
    (h : ∀ a, D.base.IsPos a ↔ E.base.IsPos (e a))
    (l r : List D.I)
    (hl : Enumerates l {a | ¬ D.base.IsPos a}) (hr : Enumerates r {a | D.base.IsPos a}) :
    Enumerates (l.map e) {b | ¬ E.base.IsPos b} ∧
    Enumerates (r.map e) {b | E.base.IsPos b} := by
  refine ⟨⟨hl.1.map e.injective, ?_⟩, ⟨hr.1.map e.injective, ?_⟩⟩
  · intro b
    obtain ⟨a, rfl⟩ := e.surjective b
    rw [List.mem_map_of_injective e.injective, hl.2]
    exact not_congr (h a)
  · intro b
    obtain ⟨a, rfl⟩ := e.surjective b
    rw [List.mem_map_of_injective e.injective, hr.2]
    exact h a

private theorem positiveAndNegativeEnumerations (D : Pinning.BasedRootDatum.{u}) :
    ∃ l r : List D.I, Enumerates l {a | ¬ D.base.IsPos a} ∧
      Enumerates r {a | D.base.IsPos a} := by
  classical
  letI : Finite D.I := D.finiteRoots
  letI : Fintype D.I := Fintype.ofFinite _
  exact ⟨(Finset.univ.filter fun a => ¬ D.base.IsPos a).toList,
    (Finset.univ.filter D.base.IsPos).toList,
    ⟨Finset.nodup_toList _, by simp⟩, ⟨Finset.nodup_toList _, by simp⟩⟩

open _root_.LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent (localSL2Generation)
open _root_.LinearAlgebraicGroups.Specs.IntegralRootRelations (upper lower)

set_option backward.isDefEq.respectTransparency false in
theorem markedRankOneMapCompatibility : MarkedRankOneMapCompatibility.{u} := by
  intro D E M A f e χ h he
  have hu (R : IntegralAlgebra.{u}) (a : D.I) (x : R) :
      integralPointHom f R ((M.rankOne a).app R (upper x)) = (A.rankOne (e a)).app R (upper x) := by
    rw [M.rankOneUpper, A.rankOneUpper]
    exact h.2.1 R a x
  have hl (R : IntegralAlgebra.{u}) (a : D.I) (x : R) :
      integralPointHom f R ((M.rankOne a).app R (lower x)) = (A.rankOne (e a)).app R (lower x) := by
    rw [M.rankOneLower, A.rankOneLower]
    have h' := h.2.1 R (D.datum.reflectionPerm a a) x
    rw [he] at h'
    exact h'
  constructor
  · intro R _ a
    let u := (integralPointHom f R).comp ((M.rankOne a).app R).hom
    let v := ((A.rankOne (e a)).app R).hom
    apply localSL2Generation (R := R) (fun g => u g = v g) (hu R a) (hl R a)
    intro x y hx hy
    rw [u.map_mul, v.map_mul, hx, hy]
  · intro R l
    have hw (a : D.I) : integralPointHom f R (markedWall M.toIntegralMarking R a 1) =
        markedWall A.toIntegralMarking R (e a) 1 := by
      simp only [markedWall, wallMatrix, rankOneMatrixWord]
      let g := ((M.rankOne a).app R).hom
      let g' := ((A.rankOne (e a)).app R).hom
      change integralPointHom f R (g _) = g' _
      rw [g.map_mul, g.map_mul, g'.map_mul, g'.map_mul,
        (integralPointHom f R).map_mul, (integralPointHom f R).map_mul]
      exact congrArg₂ (· * ·) (congrArg₂ (· * ·) (hu R a _) (hl R a _)) (hu R a _)
    induction l with
    | nil => exact map_one _
    | cons a l ih =>
      change integralPointHom f R (markedWall M.toIntegralMarking R a 1 *
          markedWeylWord M.toIntegralMarking R l) =
        markedWall A.toIntegralMarking R (e a) 1 * markedWeylWord A.toIntegralMarking R (l.map e)
      rw [(integralPointHom f R).map_mul, hw, ih]

set_option backward.isDefEq.respectTransparency false in
theorem splitIwahoriImage : SplitIwahoriImage.{u} := by
  classical
  intro K _ _ D E M A f e χ hf κ C C' B B' hB hB' p
  let O := CommAlgCat.of Integers.{u} (valuation K).valuationSubring
  let S := CommAlgCat.of Integers.{u} K
  let i := valuationRingInclusion K
  let im := ((integralPointFunctor M.group).map i).hom
  let ia := ((integralPointFunctor A.group).map i).hom
  let P := markedBorelReduction M.group B
  let Q := markedBorelReduction A.group B'
  let U := integralUnitTorus (K := K) A
  obtain ⟨l, r, hl, hr⟩ := positiveAndNegativeEnumerations D
  obtain ⟨hl', hr'⟩ := enumerates_map e hf.1 l r hl hr
  have hP := iwahoriDepthCoordinates C B hB l r hl hr
  have hQ := iwahoriDepthCoordinates C' B' hB' (l.map e) (r.map e) hl' hr'
  have hx (z : D.I → O) (t : TorusValues D O) :
      p (im (markedCellPoint M.toIntegralMarking O l r z (torusPoint D O t))) =
        ia (markedCellPoint A.toIntegralMarking O (l.map e) (r.map e)
          (z ∘ e.symm) (torusPoint E O (t.comp χ))) := by
    change integralPointHom f S ((integralPointFunctor M.group).map i _) = _
    rw [integralPointHom_natural]
    have hz : (z ∘ e.symm) ∘ e = z := funext (fun a => congrArg z (e.symm_apply_apply a))
    rw [← markedCellPoint_image f e χ hf, hz]
  have hmap : P.map p ≤ Q := by
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨z, t, hz, hg⟩ := (hP g).mp hg
    refine (hQ _).mpr ⟨z ∘ e.symm, t.comp χ, ?_, (hx z t).symm.trans (congrArg p hg)⟩
    intro a ha
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
    simpa using hz j hj
  have hU : U ≤ Q := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨s, rfl⟩ := (affineTorusPointEquiv (k := Integers.{u}) (M := Multiplicative E.X) O).surjective t
    refine (hQ _).mpr ⟨0, s, by simp, ?_⟩
    have hz (u : List E.I) : orderedRootPoint A.toIntegralMarking O u 0 = 1 :=
      orderedRootPoint_eq_one_of_zero _ _ _ _ (fun _ _ => rfl)
    change ia (markedCellPoint A.toIntegralMarking O (l.map e) (r.map e) 0 (torusPoint E O s)) = _
    rw [markedCellPoint, hz, hz, mul_one, one_mul]
    rfl
  apply le_antisymm ?_ (sup_le hmap hU)
  intro g hg
  obtain ⟨z, t, hz, rfl⟩ := (hQ g).mp hg
  let V := P.map p ⊔ U
  have hPV : P.map p ≤ V := le_sup_left
  have hUV : U ≤ V := le_sup_right
  have hneg : ia (orderedRootPoint A.toIntegralMarking O (l.map e) z) ∈ P.map p := by
    let w (a : D.I) : O := if D.base.IsPos a then 0 else z (e a)
    let x := im (markedCellPoint M.toIntegralMarking O l r w (torusPoint D O 1))
    have hw (a : E.I) (ha : a ∈ l.map e) : (w ∘ e.symm) a = z a := by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      have hneg : ¬ D.base.IsPos b := (hl.2 b).mp hb
      simp only [Function.comp_apply, e.symm_apply_apply, w, if_neg hneg]
    have hw' (a : E.I) (ha : a ∈ r.map e) : (w ∘ e.symm) a = 0 := by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      have hpos : D.base.IsPos b := (hr.2 b).mp hb
      simp only [Function.comp_apply, e.symm_apply_apply, w, if_pos hpos]
    have hp : p x = ia (orderedRootPoint A.toIntegralMarking O (l.map e) z) := by
      rw [hx]
      unfold markedCellPoint
      rw [orderedRootPoint_congr _ _ _ hw, orderedRootPoint_eq_one_of_zero _ _ _ _ hw']
      have ht : (1 : TorusValues D O).comp χ = 1 := by ext; rfl
      rw [ht, ← markedTorusPointHom_apply, map_one, mul_one, mul_one]
    refine ⟨x, (hP x).mpr ⟨w, 1, ?_, rfl⟩, hp⟩
    intro a ha
    have hneg : ¬ D.base.IsPos a := (hl.2 a).mp ha
    simpa only [w, if_neg hneg] using hz (e a) (List.mem_map.mpr ⟨a, ha, rfl⟩)
  have hpos : ia (orderedRootPoint A.toIntegralMarking O (r.map e) z) ∈ P.map p := by
    let w (a : D.I) : O := if D.base.IsPos a then z (e a) else 0
    let x := im (markedCellPoint M.toIntegralMarking O l r w (torusPoint D O 1))
    have hw (a : E.I) (ha : a ∈ r.map e) : (w ∘ e.symm) a = z a := by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      have hpos : D.base.IsPos b := (hr.2 b).mp hb
      simp only [Function.comp_apply, e.symm_apply_apply, w, if_pos hpos]
    have hw' (a : E.I) (ha : a ∈ l.map e) : (w ∘ e.symm) a = 0 := by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      have hneg : ¬ D.base.IsPos b := (hl.2 b).mp hb
      simp only [Function.comp_apply, e.symm_apply_apply, w, if_neg hneg]
    have hp : p x = ia (orderedRootPoint A.toIntegralMarking O (r.map e) z) := by
      rw [hx]
      unfold markedCellPoint
      rw [orderedRootPoint_eq_one_of_zero _ _ _ _ hw', orderedRootPoint_congr _ _ _ hw]
      have ht : (1 : TorusValues D O).comp χ = 1 := by ext; rfl
      rw [ht, ← markedTorusPointHom_apply, map_one, one_mul, one_mul]
    refine ⟨x, (hP x).mpr ⟨w, 1, ?_, rfl⟩, hp⟩
    intro a ha
    have hneg : ¬ D.base.IsPos a := (hl.2 a).mp ha
    simp only [w, if_neg hneg]
    change valuation K (0 : K) < 1
    simp
  have ht : ia (torusPoint E O t ≫ A.torus.hom.hom) ∈ U :=
    ⟨torusPoint E O t, rfl⟩
  change ia (markedCellPoint A.toIntegralMarking O _ _ _ _) ∈ V
  unfold markedCellPoint
  rw [ia.map_mul, ia.map_mul]
  exact V.mul_mem (hPV hneg) (V.mul_mem (hUV ht) (hPV hpos))

end IntegralImage

section IntegralPreimage

open _root_.LinearAlgebraicGroups.Specs.IntegralSemisimpleModel
open _root_.LinearAlgebraicGroups.Specs.ExceptionalMarkedRootDescent
open _root_.LinearAlgebraicGroups.Specs.ExceptionalValuedTorusNormalizer (valuationRingInclusion)
open _root_.LinearAlgebraicGroups.Arithmetic.ExceptionalValuedTorusNormalizer (integralTorusCoordinates)
open private affineTorusPointEquiv torusPoint_natural from
  LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
open private markedTorusPoint_map from LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent

attribute [local instance] integerAlgebra

private theorem unit_character_of_finite_index {K X Y : Type u} [Field K] [CommGroup X]
    [CommGroup Y] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (χ : Y →* X) [Finite (X ⧸ χ.range)] (t : X →* Kˣ)
    (hχ : ∀ y, normalizedValuation K (t (χ y) : K) = 1) :
    ∀ x, normalizedValuation K (t x : K) = 1 := by
  intro x
  let p := QuotientGroup.mk' χ.range
  let n := orderOf (p x)
  have hn : 0 < n := orderOf_pos _
  have hp : p (x ^ n) = 1 := by rw [p.map_pow, pow_orderOf_eq_one]
  obtain ⟨y, hy⟩ := (QuotientGroup.eq_one_iff _).mp hp
  have hval := hχ y
  rw [hy, t.map_pow, Units.val_pow_eq_pow_val, map_pow] at hval
  let z := normalizedValuation K (t x : K)
  have hz : z ≠ 0 := (map_ne_zero _).mpr (t x).ne_zero
  have hpow : exp ((n : ℤ) * log z) = exp 0 := by
    rw [← nsmul_eq_mul, exp_nsmul, exp_log hz, exp_zero]
    exact hval
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  have hlog := (mul_eq_zero.mp (exp_injective hpow)).resolve_left hn'
  exact (exp_log hz).symm.trans (hlog.symm ▸ exp_zero)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 550000 in
theorem splitIwahoriPreimage : SplitIwahoriPreimage.{u} := by
  classical
  intro K _ _ _ _ D E M A f e χ hf hfinite S p htor κ C C' B B' hB hB'
  letI := hfinite
  let O := CommAlgCat.of Integers.{u} (valuation K).valuationSubring
  let i := valuationRingInclusion K
  let im := ((integralPointFunctor M.group).map i).hom
  let ia := ((integralPointFunctor A.group).map i).hom
  obtain ⟨l, r, hl, hr⟩ := positiveAndNegativeEnumerations D
  obtain ⟨hl', hr'⟩ := enumerates_map e hf.1 l r hl hr
  have hI := iwahoriDepthCoordinates C B hB l r hl hr
  have hJ := iwahoriDepthCoordinates C' B' hB' (l.map e) (r.map e) hl' hr'
  have hmap := splitIwahoriImage M A f e χ hf C C' B B' hB hB'
  ext g
  constructor
  · intro hg
    obtain ⟨z, t, hz, ht⟩ := (hJ (p g)).mp hg
    let w : E.I → S := fun a => i.hom (z a)
    let x := orderedRootPoint M.toIntegralMarking S l (w ∘ e)
    let y := orderedRootPoint M.toIntegralMarking S r (w ∘ e)
    let u := (Units.map i.hom.toMonoidHom).comp t
    have htorus : p (x⁻¹ * g * y⁻¹) = torusPoint E S u ≫ A.torus.hom.hom := by
      have hp : p g = orderedRootPoint A.toIntegralMarking S (l.map e) w *
          ((torusPoint E S u ≫ A.torus.hom.hom) *
            orderedRootPoint A.toIntegralMarking S (r.map e) w) := by
        rw [← ht, markedCellPoint_map]
        unfold markedCellPoint
        change _ = orderedRootPoint _ _ _ _ * ((torusPoint E S u ≫ A.torus.hom.hom) * _)
        rw [show (integralPointFunctor (splitTorus E)).map i (torusPoint E O t) =
          torusPoint E S u from torusPoint_natural i t]
      rw [p.map_mul, p.map_mul, p.map_inv, p.map_inv, hp,
        show p x = orderedRootPoint A.toIntegralMarking S (l.map e) w from
          orderedRootPoint_image f e S (hf.2.1 S) l w,
        show p y = orderedRootPoint A.toIntegralMarking S (r.map e) w from
          orderedRootPoint_image f e S (hf.2.1 S) r w]
      rw [inv_mul_cancel_left, mul_inv_cancel_right]
    obtain ⟨s, hs⟩ := htor (x⁻¹ * g * y⁻¹) ⟨u, htorus⟩
    have hm : s.comp χ = u := by
      have h := (congrArg p hs).symm.trans htorus
      rw [hf.2.2] at h
      haveI : IsClosedImmersion A.torus.hom.hom.left := A.torusClosed
      haveI : Mono A.torus.hom.hom := Over.mono_of_mono_left _
      exact (affineTorusPointEquiv (k := Integers.{u}) S).injective
        ((cancel_mono A.torus.hom.hom).mp h)
    letI := D.freeY
    letI := D.finiteY
    let b := Module.Free.chooseBasis ℤ D.Y
    obtain ⟨q, hq⟩ := (integralTorusCoordinates D b s).mp (by
      intro a
      apply unit_character_of_finite_index χ s
      intro x
      change normalizedValuation K ((s.comp χ) x : K) = 1
      rw [hm]
      -- The equality follows from the unit and its inverse lying in the valuation ring.
      let z₀ := t x
      have hval : valuation K (u x : K) ≤ 1 := ((z₀ : (valuation K).valuationSubring)).property
      have hval' : valuation K (↑((u x)⁻¹) : K) ≤ 1 := by
        change valuation K (↑((Units.map i.hom.toMonoidHom z₀)⁻¹) : K) ≤ 1
        rw [← map_inv]
        exact ((↑(z₀⁻¹) : (valuation K).valuationSubring)).property
      have heq : valuation K (u x : K) = 1 := by
        have hvx : 0 < valuation K (u x : K) :=
          pos_iff_ne_zero.mpr ((map_ne_zero _).mpr (u x).ne_zero)
        rw [Units.val_inv_eq_inv_val, map_inv₀, inv_le_one₀ hvx] at hval'
        exact le_antisymm hval hval'
      change IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (valuation K (u x : K)) = 1
      rw [heq, map_one])
    refine (hI g).mpr ⟨z ∘ e, q, ?_, ?_⟩
    · exact fun a ha => hz (e a) (List.mem_map.mpr ⟨a, ha, rfl⟩)
    · rw [markedCellPoint_map]
      change x * ((show IntegralPoints M.group S from
        (integralPointFunctor (splitTorus D)).map i (torusPoint D O q) ≫ M.torus.hom.hom) * y) = _
      rw [show (integralPointFunctor (splitTorus D)).map i (torusPoint D O q) = torusPoint D S s from
        (torusPoint_natural i q).trans (congrArg (torusPoint D S) hq)]
      rw [← hs, inv_mul_cancel_right, mul_inv_cancel_left]
  · intro hg
    have h : p g ∈ (markedBorelReduction M.group B).map p := ⟨g, hg, rfl⟩
    rw [hmap]
    exact (le_sup_left : (markedBorelReduction M.group B).map p ≤ _) h

theorem markedTranslationCompatibility : MarkedTranslationCompatibility.{u} := by
  intro K _ _ _ _ D E χ f hf R v t a b ha hb
  have h : f a = b := by
    apply E.datum.toLinearMap.flip.toPerfPair.injective
    ext x
    change E.datum.toLinearMap x (f a) = E.datum.toLinearMap x b
    exact (hf x a).symm.trans ((ha (χ x)).trans (hb x).symm)
  exact ⟨h, fun q => (TensorProduct.map_tmul _ _ q a).trans
    (congrArg (TensorProduct.tmul ℤ q) h)⟩

end IntegralPreimage

section PinnedGround

open _root_.LinearAlgebraicGroups.Specs.IntegralSemisimpleModel
open _root_.LinearAlgebraicGroups.Specs.ExceptionalMarkedRootDescent
open _root_.LinearAlgebraicGroups.Specs.AdjointRepresentation (GroupPoints)
open _root_.LinearAlgebraicGroups.Specs.AdjointCocharacters (coordinateHopf coordinateHopfMap)
open _root_.LinearAlgebraicGroups.Specs.AdjointBorelCohomology (PinnedTwist)
open _root_.LinearAlgebraicGroups.Specs.Unipotent (closedSubgroupAlgebraicGroup)
open _root_.LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
  (pinnedMarkedPointEmbedding pinnedMarkedTorusPointComparison)
open private groundTensorIso evaluateGroundTensor_conjugate coordinatePointEquiv_comp
  restrictExtended_comp fibrePointEquiv quadraticGalois markedTorusPoint_map
  from LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
open Opposite
open scoped TensorProduct

attribute [local instance] integerAlgebra

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {D : Pinning.BasedRootDatum.{u}} {M : Model D} (C : MarkedFibre M k)
  {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
  {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}
  (d : PinnedTwist K C.realization.attached l B T)

private def groundEvaluation :
    (extendedTestAlgebra k K).obj (CommAlgCat.of k k) ⟶ CommAlgCat.of k K :=
  CommAlgCat.ofHom ((Algebra.TensorProduct.rid k K K).toAlgHom.restrictScalars k)

set_option backward.isDefEq.respectTransparency false in
private theorem pinnedSchemePoint_borel (R : TestAlgebra k)
    (b : GroupPoints B.group R) :
    ∃ q : GroupPoints C.realization.pinned.pair.B.group ((extendedTestAlgebra k K).obj R),
      pinnedSchemePoint d R ((coordinatePointEquiv G R).symm (b ≫ B.inclusion.hom.hom)) =
        q ≫ C.realization.pinned.pair.B.inclusion.hom.hom := by
  let P := C.realization.pinned.pair
  let A := closedSubgroupAlgebraicGroup B
  let A₀ := closedSubgroupAlgebraicGroup P.B
  let q := (coordinatePointEquiv A R).symm b
  let h := coordinateHopfMap (G := A) (H := G) B.inclusion
  let h₀ := coordinateHopfMap (G := A₀) (H := P.G) P.B.inclusion
  have hb : (coordinatePointEquiv G R).symm (b ≫ B.inclusion.hom.hom) =
      WithConv.toConv (q.ofConv.comp h.hom.toAlgHom) := by
    apply (coordinatePointEquiv G R).injective
    rw [MulEquiv.apply_symm_apply, coordinatePointEquiv_comp (G := A) (H := G),
      MulEquiv.apply_symm_apply]
  let v := extendAlgebraPoint (K := K) q.ofConv
  have hv : extendAlgebraPoint (K := K) (q.ofConv.comp h.hom.toAlgHom) =
      v.comp (extendedHopfMap K h).hom.toAlgHom := by
    apply (AlgHom.liftEquiv k K (Specs.AdjointCocharacters.coordinateHopf G) (K ⊗[k] R)).symm.injective
    rw [restrictExtended_comp]
    dsimp only [v, extendAlgebraPoint]
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, AlgHom.comp_assoc]
  let w := v.comp d.borelIso.hom.hom.toAlgHom
  have hw : (v.comp (extendedHopfMap K h).hom.toAlgHom).comp d.groupIso.hom.hom.toAlgHom =
      w.comp (extendedHopfMap K h₀).hom.toAlgHom := by
    apply AlgHom.ext
    intro a
    exact congrArg v (ConcreteCategory.congr_hom d.borelComm a)
  refine ⟨coordinatePointEquiv A₀ ((extendedTestAlgebra k K).obj R)
    (WithConv.toConv ((AlgHom.liftEquiv k K (Specs.AdjointCocharacters.coordinateHopf A₀)
      (K ⊗[k] R)).symm w)), ?_⟩
  rw [hb]
  unfold pinnedSchemePoint pinnedAlgebraPointMap
  rw [WithConv.ofConv_toConv, hv, hw, restrictExtended_comp]
  exact coordinatePointEquiv_comp (G := A₀) (H := P.G) P.B.inclusion _ _

private def groundToHopf (G : AffineAlgebraicGroup k) :
    (𝟙_ (SchemeOver k) ⟶ G.val.X) →* HopfPoints (Specs.AdjointCocharacters.coordinateHopf G) k :=
  let R := CommAlgCat.of k k
  ((coordinatePointEquiv G R).symm.toMonoidHom).comp
    { toFun := fun g => toUnit ((testSpec k).obj (op R)) ≫ g
      map_one' := MonObj.comp_one _
      map_mul' := MonObj.comp_mul _ }

private theorem groundToHopf_bijective (G : AffineAlgebraicGroup k) :
    Function.Bijective (groundToHopf G) := by
  let R := CommAlgCat.of k k
  let e := ((coordinatePointEquiv G R).symm).toMonoidHom
  have h (g : 𝟙_ (SchemeOver k) ⟶ G.val.X) :
      groundToHopf G g = e (groundSectionsEquiv G.val g) :=
    congrArg e (groundSectionsEquiv_apply G.val g).symm
  rw [show (groundToHopf G : _ → _) = fun g => e (groundSectionsEquiv G.val g) from funext h]
  exact (coordinatePointEquiv G R).symm.bijective.comp (groundSectionsEquiv _).bijective

private def groundHopfEquiv (G : AffineAlgebraicGroup k) :
    (𝟙_ (SchemeOver k) ⟶ G.val.X) ≃* HopfPoints (Specs.AdjointCocharacters.coordinateHopf G) k :=
  MulEquiv.ofBijective (groundToHopf G) (groundToHopf_bijective G)

private theorem pinnedGroundPoint_apply (g : 𝟙_ (SchemeOver k) ⟶ G.val.X) :
    pinnedGroundPoint C d g =
      (integralPointFunctor M.group).map (evaluateGroundTensor k K)
        (pinnedMarkedPoint C d (CommAlgCat.of k k) (groundHopfEquiv G g)) := rfl

set_option maxHeartbeats 45000 in
private theorem evaluateMarkedFibrePoint
    (u : GroupPoints C.realization.pinned.pair.G.val
      ((extendedTestAlgebra k K).obj (CommAlgCat.of k k))) :
    (integralPointFunctor M.group).map (evaluateGroundTensor k K)
      (markedFibrePoint C ((extendedTestAlgebra k K).obj (CommAlgCat.of k k)) u) =
    markedFibrePoint C (CommAlgCat.of k K) (mapPoints groundEvaluation u) := by
  apply Over.OverMorphism.ext
  exact (Category.assoc _ _ _).symm

set_option backward.isDefEq.respectTransparency false in
private theorem pinnedGroundPoint_borel (b : 𝟙_ (SchemeOver k) ⟶ B.group.X) :
    pinnedGroundPoint C d (b ≫ B.inclusion.hom.hom) ∈
      markedPositiveBorel C (CommAlgCat.of k K) := by
  let S := CommAlgCat.of k k
  let R := CommAlgCat.of k K
  let P := C.realization.pinned.pair
  let i : (extendedTestAlgebra k K).obj S ⟶ R := groundEvaluation
  obtain ⟨u, hu⟩ := pinnedSchemePoint_borel C d S (toUnit _ ≫ b)
  rw [Category.assoc] at hu
  refine ⟨mapPoints i u, ?_⟩
  change markedFibrePoint C R (mapPoints i u ≫ P.B.inclusion.hom.hom) =
    pinnedGroundPoint C d (b ≫ B.inclusion.hom.hom)
  unfold pinnedGroundPoint pinnedMarkedPoint
  rw [hu, evaluateMarkedFibrePoint]
  exact congrArg (markedFibrePoint C R) (Category.assoc ((testSpec k).map i.op) u _)

set_option backward.isDefEq.respectTransparency false in
private theorem pinnedGroundPoint_hom [FiniteDimensional k K] [IsGalois k K] :
    ∃ j : (𝟙_ (SchemeOver k) ⟶ G.val.X) →* IntegralPoints M.group (CommAlgCat.of Integers.{u} K),
      Function.Injective j ∧ ∀ g, j g = pinnedGroundPoint C d g := by
  let S := CommAlgCat.of k k
  let ev := ((integralPointFunctor M.group).map (evaluateGroundTensor k K)).hom
  obtain ⟨emb, he, h⟩ := pinnedMarkedPointEmbedding C d
  let j := ev.comp ((emb.app S).hom.comp (groundHopfEquiv G).toMonoidHom)
  have hev : Function.Injective ev :=
    (((integralPointFunctor M.group).mapIso (groundTensorIso k K)).groupIsoToMulEquiv).injective
  refine ⟨j, hev.comp ((h S).1.comp (groundHopfEquiv G).injective), fun g => ?_⟩
  exact (congrArg ev (he S (groundHopfEquiv G g))).trans (pinnedGroundPoint_apply C d g).symm

set_option backward.isDefEq.respectTransparency false in
private theorem pinnedGroundPoint_torus [FiniteDimensional k K] [IsGalois k K]
    (t : IntegralPoints (splitTorus D) (CommAlgCat.of Integers.{u} K))
    (g : 𝟙_ (SchemeOver k) ⟶ G.val.X)
    (hg : pinnedGroundPoint C d g = t ≫ M.torus.hom.hom) :
    SchemeDerivedGroup.FactorsThrough T g := by
  let S := CommAlgCat.of k k
  let ev := ((integralPointFunctor M.group).map (evaluateGroundTensor k K)).hom
  let evT := ((integralPointFunctor (splitTorus D)).map (evaluateGroundTensor k K)).hom
  have hev : Function.Injective ev :=
    (((integralPointFunctor M.group).mapIso (groundTensorIso k K)).groupIsoToMulEquiv).injective
  have hevT : Function.Surjective evT :=
    (((integralPointFunctor (splitTorus D)).mapIso (groundTensorIso k K)).groupIsoToMulEquiv).surjective
  obtain ⟨s, rfl⟩ := hevT t
  obtain ⟨_, ht, htor⟩ := pinnedMarkedTorusPointComparison C d S
  let p := groundHopfEquiv G g
  have hs : pinnedMarkedPoint C d S p = s ≫ M.torus.hom.hom :=
    hev ((pinnedGroundPoint_apply C d g).symm.trans
      (hg.trans (markedTorusPoint_map M.toIntegralMarking _ s).symm))
  obtain ⟨x, hx⟩ := (htor s).mpr ⟨p, hs⟩
  obtain ⟨emb, he, hi⟩ := pinnedMarkedPointEmbedding C d
  have hinj : Function.Injective (pinnedMarkedPoint C d S) := by
    intro a b hab
    exact (hi S).1 ((he S a).trans (hab.trans (he S b).symm))
  have hpx : p = descendedTorusInclusion S x := hinj (hs.trans ((ht x).trans
    (congrArg (fun z : IntegralPoints (splitTorus D) ((quadraticIntegralAlgebra k K).obj S) =>
      z ≫ M.torus.hom.hom) hx)).symm)
  let v := coordinatePointEquiv (closedSubgroupAlgebraicGroup T) S x
  let a := (groundSectionsEquiv T.group).symm v
  refine ⟨a, ?_⟩
  apply (groundSectionsEquiv G.val).injective
  have h := coordinatePointEquiv_comp (G := closedSubgroupAlgebraicGroup T) (H := G) T.inclusion S x
  change coordinatePointEquiv G S (descendedTorusInclusion S x) = v ≫ T.inclusion.hom.hom at h
  rw [← hpx] at h
  change (coordinatePointEquiv G S) ((coordinatePointEquiv G S).symm
    (toUnit _ ≫ g)) = _ at h
  rw [MulEquiv.apply_symm_apply] at h
  have ha : toUnit ((testSpec k).obj (op S)) ≫ a = v :=
    (groundSectionsEquiv_apply T.group a).symm.trans ((groundSectionsEquiv T.group).apply_symm_apply v)
  change groundSectionsEquiv G.val (a ≫ T.inclusion.hom.hom) = groundSectionsEquiv G.val g
  rw [groundSectionsEquiv_apply G.val (a ≫ T.inclusion.hom.hom), ← Category.assoc, ha]
  exact h.symm.trans (groundSectionsEquiv_apply G.val g).symm

set_option backward.isDefEq.respectTransparency false in
private theorem evaluatePinnedAction (σ : Gal(K/k))
    (u : GroupPoints C.realization.pinned.pair.G.val
      ((extendedTestAlgebra k K).obj (CommAlgCat.of k k))) :
    mapPoints groundEvaluation (pinnedSchemeAction d σ (CommAlgCat.of k k) u) =
      (testSpec k).map (CommAlgCat.ofHom σ.toAlgHom).op ≫ (mapPoints groundEvaluation u) ≫
        (l (d.outer σ)).asIso.hom.group.hom.hom.hom := by
  let S := CommAlgCat.of k k
  let i : (extendedTestAlgebra k K).obj S ⟶ CommAlgCat.of k K := groundEvaluation
  have hcomm : conjugateTestAlgebra σ S ≫ i = i ≫ CommAlgCat.ofHom σ.toAlgHom := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    exact evaluateGroundTensor_conjugate σ x
  change (testSpec k).map i.op ≫ (testSpec k).map (conjugateTestAlgebra σ S).op ≫
      u ≫ _ = (testSpec k).map (CommAlgCat.ofHom σ.toAlgHom).op ≫
        ((testSpec k).map i.op ≫ u) ≫ _
  rw [← Category.assoc ((testSpec k).map i.op), ← Functor.map_comp, ← op_comp,
    hcomm, op_comp, Functor.map_comp]
  simp only [Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem pinnedGroundPoint_range [FiniteDimensional k K] [IsGalois k K]
    (σ : Gal(K/k)) (hd : Module.finrank k K = 2) (hσ : σ ≠ 1)
    (v : GroupPoints C.realization.pinned.pair.G.val (CommAlgCat.of k K)) :
    markedFibrePoint C (CommAlgCat.of k K) v ∈ Set.range (pinnedGroundPoint C d) ↔
      (testSpec k).map (CommAlgCat.ofHom σ.toAlgHom).op ≫ v ≫
        (l (d.outer σ)).asIso.hom.group.hom.hom.hom = v := by
  let P := C.realization.pinned.pair
  let S := CommAlgCat.of k k
  let U := (extendedTestAlgebra k K).obj S
  let R := CommAlgCat.of k K
  let i : U ⟶ R := groundEvaluation
  let j := (integralPointFunctor M.group).map (evaluateGroundTensor k K)
  have hmap : Function.Bijective (mapPoints i : GroupPoints P.G.val U → GroupPoints P.G.val R) := by
    letI : IsIso i := by
      let e := (Algebra.TensorProduct.rid k K K).restrictScalars k
      change IsIso (CommAlgCat.ofHom e.toAlgHom)
      exact (CommAlgCat.isoMk e).isIso_hom
    exact ((testSpec k).mapIso (asIso i).op).symm.homFromEquiv.bijective
  obtain ⟨u, rfl⟩ := hmap.surjective v
  obtain ⟨emb, he, h⟩ := pinnedMarkedPointEmbedding C d
  have hinj : Function.Injective j :=
    (((integralPointFunctor M.group).mapIso (groundTensorIso k K)).groupIsoToMulEquiv).injective
  have hImage : markedFibrePoint C R (mapPoints i u) ∈ Set.range (pinnedGroundPoint C d) ↔
      markedFibrePoint C U u ∈ Set.range (emb.app S) := by
    rw [← evaluateMarkedFibrePoint C u]
    constructor
    · rintro ⟨g, hg⟩
      have hp := (pinnedGroundPoint_apply C d g).symm.trans hg
      exact ⟨groundHopfEquiv G g, (he S _).trans (hinj hp)⟩
    · rintro ⟨p, hp⟩
      obtain ⟨g, rfl⟩ := (groundHopfEquiv G).surjective p
      exact ⟨g, (pinnedGroundPoint_apply C d g).trans (congrArg j ((he S _).symm.trans hp))⟩
  rw [hImage, (h S).2]
  have hσ' : ∀ τ : Gal(K/k), τ = 1 ∨ τ = σ := (quadraticGalois hd σ hσ).1
  have htriv : pinnedSchemeAction d 1 S u = u := by
    apply hmap.injective
    rw [evaluatePinnedAction C d]
    have hId : CommAlgCat.ofHom ((1 : Gal(K/k)).toAlgHom) = 𝟙 R := rfl
    simp only [hId, map_one, Aut.one_asIso, Iso.refl_hom]
    change (testSpec k).map ((𝟙 R).op) ≫ mapPoints i u ≫ 𝟙 _ = mapPoints i u
    rw [Category.comp_id, op_id, (testSpec k).map_id, Category.id_comp]
  have hact := evaluatePinnedAction C d σ u
  refine ⟨fun h => hact.symm.trans (congrArg (mapPoints i) (h σ)), fun h τ => ?_⟩
  exact (hσ' τ).elim (fun e => e.symm ▸ htriv) (fun e => e.symm ▸ hmap.injective (hact.trans h))

theorem pinnedGroundPointComparison : PinnedGroundPointComparison.{u} := by
  intro k K _ _ _ _ _ D M C l G B T d σ hd hσ R P
  obtain ⟨j, hi, hj⟩ := pinnedGroundPoint_hom C d
  refine ⟨j, hi, hj, fun b => (hj _).symm ▸ pinnedGroundPoint_borel C d b,
    fun t g hg => pinnedGroundPoint_torus C d t g ((hj g).symm.trans hg), fun v => ?_⟩
  have he : Set.range j = Set.range (pinnedGroundPoint C d) := congrArg Set.range (funext hj)
  change markedFibrePoint C R v ∈ Set.range j ↔ _
  rw [he]
  exact pinnedGroundPoint_range C d σ hd hσ v

end PinnedGround

section FoldedGeneration

open _root_.LinearAlgebraicGroups.Specs.IntegralSemisimpleModel
open _root_.LinearAlgebraicGroups.Specs.ExceptionalMarkedRootDescent
open _root_.LinearAlgebraicGroups.Specs.AdjointRepresentation (GroupPoints)
open _root_.LinearAlgebraicGroups.Specs.AdjointBorelCohomology (PinnedTwist)
open _root_.LinearAlgebraicGroups.Specs.CharacterPairing (characterValue)
open _root_.LinearAlgebraicGroups.Specs.CharacterDescent (Character)
open _root_.LinearAlgebraicGroups.Specs.SchemeDerivedGroup (FactorsThrough)
open _root_.LinearAlgebraicGroups.Specs.ExceptionalValuedTorusNormalizer (markedDiagramEquiv)
open _root_.LinearAlgebraicGroups.Arithmetic.ExceptionalValuedTorusNormalizer
  (markedFibreTorusCoordinates markedPinnedTorus descendedRelativeNormalizer invariantRegularCocharacter)
open _root_.LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
  (wallDepths pinnedRationalFixedCellCoordinates pinnedOrderedRootProducts transportedIntegralCoordinates
    transportedOrbitParameterComparison pinnedMarkedTorusPointComparison)
open private pinnedLift_character from LinearAlgebraicGroups.Arithmetic.ExceptionalValuedTorusNormalizer
open private characterValue_pullback from LinearAlgebraicGroups.Classification.CentralIsogenies
open private characterValue_natural from LinearAlgebraicGroups.RootData.RootGroups
open private subgroup_normalizes from LinearAlgebraicGroups.RootData.BorelNormalizer
open private subgroupOf_trans from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private evaluateOrderedCoordinates rationalOrderedEquiv markedTorusPoint_map splitOrderedOrbitPoint_values
  splitOrderedValues splitOrderedValues_labels transportUnit
  from LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent

attribute [local instance] integerAlgebra

set_option backward.isDefEq.respectTransparency false in
private theorem invariantCocharacterPoint_fixed {k K : Type u} [Field k] [Field K] [Algebra k K]
    {D : Pinning.BasedRootDatum.{u}} {M : Model D} (C : MarkedFibre M k)
    {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
    {Q : AutomorphismSequence.AdjointQuotient C.realization.pinned.pair.G}
    (E : AutomorphismSequence.SplitSequence C.realization.pinned C.realization.attached l Q)
    (a : Aut C.realization.attached.toBased) (σ : Gal(K/k))
    (y : D.Y) (hy : ((markedDiagramEquiv C.realization a).asIso.hom).val.coweightEquiv.symm y = y)
    (π : kˣ) :
    let P := C.realization.pinned.pair
    let R := CommAlgCat.of k K
    let S := CommAlgCat.of Integers.{u} K
    let v := cocharacter D y S (Units.map (algebraMap k K).toMonoidHom π)
    ∃ t : GroupPoints P.T.group R,
      markedFibrePoint C R (t ≫ P.T.inclusion.hom.hom) =
        torusPoint D S v ≫ M.torus.hom.hom ∧
      (testSpec k).map (CommAlgCat.ofHom σ.toAlgHom).op ≫
        (t ≫ P.T.inclusion.hom.hom) ≫ (l a).asIso.hom.group.hom.hom.hom =
          t ≫ P.T.inclusion.hom.hom := by
  intro P R S v
  let p := C.realization
  let e := (markedDiagramEquiv p a).asIso.hom
  let s := (l a).asIso.hom
  let f : R ⟶ R := CommAlgCat.ofHom σ.toAlgHom
  letI := p.attached.comm
  obtain ⟨τ, hχ, hpoint⟩ := markedFibreTorusCoordinates D M p C.groupIso C.torusIso
    C.torus_comm C.torus_eval
  let χ (x : D.X) : Character P.T.group := Additive.toMul (p.datumIso.val.weightEquiv x)
  let t := τ R v
  have hev (x : D.X) : characterValue (χ x) R t = (v (Multiplicative.ofAdd x) : K) :=
    hχ R v x
  have hsep (t₁ t₂ : GroupPoints P.T.group R)
      (he : ∀ x, characterValue (χ x) R t₁ = characterValue (χ x) R t₂) : t₁ = t₂ := by
    obtain ⟨v₁, rfl⟩ := (τ R).surjective t₁
    obtain ⟨v₂, rfl⟩ := (τ R).surjective t₂
    apply congrArg (τ R)
    apply MonoidHom.ext
    intro x
    apply Units.ext
    exact (hχ R v₁ x.toAdd).symm.trans ((he x.toAdd).trans (hχ R v₂ x.toAdd))
  have hc : mapPoints f t = t := by
    apply hsep
    intro x
    rw [characterValue_natural]
    change σ (characterValue (χ x) R t) = _
    rw [hev]
    change σ ((↑((Units.map (algebraMap k K).toMonoidHom π) ^
        (D.datum.toLinearMap x y)) : K)) =
      (↑((Units.map (algebraMap k K).toMonoidHom π) ^ (D.datum.toLinearMap x y)) : K)
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀]
    exact congrArg (· ^ D.datum.toLinearMap x y) (σ.commutes (π : k))
  have htransport (x : D.X) :
      Pinning.transportCharacter s.torus (χ x) = χ (e.val.weightEquiv x) := by
    rw [pinnedLift_character E]
    change Additive.toMul (a.asIso.hom.val.weightEquiv (p.datumIso.val.weightEquiv x)) =
      Additive.toMul (p.datumIso.val.weightEquiv (p.datumIso.val.weightEquiv.symm
        (a.asIso.hom.val.weightEquiv (p.datumIso.val.weightEquiv x))))
    rw [LinearEquiv.apply_symm_apply]
  have hd : t ≫ s.torus.hom.hom.hom = t := by
    apply hsep
    intro x
    obtain ⟨x, rfl⟩ := e.val.weightEquiv.surjective x
    have hpb : s.torus.hom ≫ χ (e.val.weightEquiv x) = χ x := by
      rw [← htransport, Pinning.transportCharacter, Iso.hom_inv_id_assoc]
    have hpair : D.datum.toLinearMap (e.val.weightEquiv x) y = D.datum.toLinearMap x y := by
      rw [← hy, e.val.toLinearMap_weightEquiv, LinearEquiv.apply_symm_apply]
      exact congrArg (D.datum.toLinearMap x) hy.symm
    rw [← characterValue_pullback, show CentralIsogenies.characterPullback s.torus.hom
      (χ (e.val.weightEquiv x)) = χ x from hpb]
    rw [hev, hev]
    exact congrArg (fun j : ℤ => (↑((Units.map (algebraMap k K).toMonoidHom π) ^ j) : K)) hpair.symm
  refine ⟨t, hpoint R v, ?_⟩
  have hcomm : P.T.inclusion.hom.hom ≫ s.group.hom.hom.hom =
      s.torus.hom.hom.hom ≫ P.T.inclusion.hom.hom :=
    congrArg (fun f : P.T.group ⟶ P.G.val => f.hom.hom) s.torus_comm
  change (testSpec k).map f.op ≫ (t ≫ P.T.inclusion.hom.hom) ≫
    s.group.hom.hom.hom = _
  calc
    _ = mapPoints f t ≫ (P.T.inclusion.hom.hom ≫ s.group.hom.hom.hom) := by
      simp only [mapPoints, Category.assoc]
    _ = t ≫ P.T.inclusion.hom.hom := by
      rw [hcomm, hc, ← Category.assoc, hd]

private theorem list_values {I A : Type*} [Inhabited A] (p : List (I × A))
    (h : (p.map Prod.fst).Nodup) : ∃ f : I → A, p = (p.map Prod.fst).map (fun a => (a, f a)) := by
  classical
  induction p with
  | nil => exact ⟨fun _ => default, rfl⟩
  | cons a l ih =>
    obtain ⟨f, hf⟩ := ih h.of_cons
    refine ⟨Function.update f a.1 a.2, ?_⟩
    simp only [List.map_cons, Function.update_self, Prod.mk.eta, List.cons.injEq, true_and]
    refine hf.trans (List.map_congr_left (fun x hx => ?_))
    have hne : x ≠ a.1 := fun he => (List.nodup_cons.mp h).1 (he ▸ hx)
    rw [Function.update_of_ne hne]

set_option backward.isDefEq.respectTransparency false in
private theorem pinnedRationalWord_range {k K : Type u} [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K] {D : Pinning.BasedRootDatum.{u}} {M : Model D}
    (C : MarkedFibre M k) {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
    {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}
    (d : PinnedTwist K C.realization.attached l B T)
    (σ : Gal(K/k)) (hd : Module.finrank k K = 2) (hσ : σ ≠ 1)
    (hpair : ∀ i j, D.datum.pairing i j = D.datum.pairing j i)
    (bs : List (TransportedOrbit D))
    (hbs : ∀ b ∈ bs, b.1.Matches C (pinnedDiagram d σ) ∧
      ∀ o ∈ b.2, o.Matches C (pinnedDiagram d σ))
    (z : rationalOrderedParameters k K bs) :
    splitOrderedOrbitPoint M.toIntegralMarking (CommAlgCat.of Integers.{u} K) bs
      (rationalOrderedCoordinates σ bs z) ∈ Set.range (pinnedGroundPoint C d) := by
  obtain ⟨word, hword, _⟩ := pinnedOrderedRootProducts C d hd σ hσ hpair bs hbs
  obtain ⟨w, rfl⟩ := (rationalOrderedEquiv k K bs).surjective z
  let ground := CommAlgCat.of k k
  obtain ⟨g, hg⟩ := (groundHopfEquiv G).surjective (word ground w)
  refine ⟨g, ?_⟩
  rw [pinnedGroundPoint_apply, hg, hword, ← transportedOrbitParameterComparison, evaluateOrderedCoordinates]

set_option backward.isDefEq.respectTransparency false in
private theorem splitOrbitWord_expansion {k K : Type u} [Field k] [Field K] [Algebra k K]
    {D : Pinning.BasedRootDatum.{u}} (M : Model D) (σ : Gal(K/k)) (bs : List (TransportedOrbit D))
    (hb : (bs.flatMap transportedLabels).Nodup) (z : rationalOrderedParameters k K bs) :
    let R := CommAlgCat.of Integers.{u} K
    ∃ v : D.I → R,
      splitOrderedOrbitPoint M.toIntegralMarking R bs (rationalOrderedCoordinates σ bs z) =
        orderedRootPoint M.toIntegralMarking R (bs.flatMap transportedLabels) v := by
  intro R
  obtain ⟨c, hc⟩ := transportedIntegralCoordinates M
  let z' := rationalOrderedCoordinates σ bs z
  letI : Inhabited R := ⟨0⟩
  let p := splitOrderedValues R c bs z'
  have hp : p.map Prod.fst = bs.flatMap transportedLabels := splitOrderedValues_labels R c bs z'
  obtain ⟨v, hv⟩ := list_values p (hp.symm ▸ hb)
  have hv' : p = (bs.flatMap transportedLabels).map (fun a => (a, v a)) :=
    hv.trans (congrArg (List.map (fun a => (a, v a))) hp)
  refine ⟨v, ?_⟩
  rw [splitOrderedOrbitPoint_values M R c (hc R) bs z']
  change (p.map _).prod = _
  rw [hv']
  simp only [orderedRootPoint, List.map_map, Function.comp_def]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1100000 in
theorem foldedIwahoriGeneration : FoldedIwahoriGeneration.{u} := by
  classical
  intro k K _ _ _ _ _ _ _ _ _ _ _ D M C l Q E ω d σ hd hσ hram hpair b hb ns ps hbs hn hp B₀
  let R := CommAlgCat.of k K
  let S := CommAlgCat.of Integers.{u} K
  let a := d.data.outer σ
  let e := (markedDiagramEquiv C.realization a).asIso.hom
  obtain ⟨j, hj, hjpoint, hjB, hjT, hjfix⟩ := pinnedGroundPointComparison C d.data σ hd hσ
  obtain ⟨c, _, hc, _⟩ := markedPinnedTorus D C.realization E d.data b hb
  obtain ⟨S₀, Q₀, hS₀, hST, _, _, hNS, _⟩ := descendedRelativeNormalizer d c hc
  let Gp := (𝟙_ (SchemeOver k) ⟶ d.group.val.X)
  let I := (markedBorelReduction M.group B₀).comap j
  let N := SubgroupSections Q₀.normalizer (𝟙_ (SchemeOver k))
  let H := I ⊔ N
  have hIH : I ≤ H := le_sup_left
  have hNH : N ≤ H := le_sup_right
  refine ⟨j, S₀, Q₀, hjpoint, hj, hS₀, hNS, ?_⟩
  have hTN (g : Gp) (ht : FactorsThrough d.torus g) : g ∈ N :=
    (Q₀.normalizerProperty _ _).mp ((hNS g).mpr (subgroup_normalizes d.torus ht))
  obtain ⟨y, hy, hheight, _⟩ := invariantRegularCocharacter D
  obtain ⟨π, hπ⟩ := (wallDepths k 1).1
  let u := Units.map (algebraMap k K).toMonoidHom π
  have hu : normalizedValuation K (u : K) = exp (-2) := by
    change normalizedValuation K (algebraMap k K (π : k)) = exp (-2)
    rw [hram, hπ, ← exp_nsmul]
    rfl
  have hyN (y' : D.Y) (hf : e.val.coweightEquiv.symm y' = y') :
      ∃ n : Gp, n ∈ N ∧ j n = torusPoint D S (cocharacter D y' S u) ≫ M.torus.hom.hom := by
    obtain ⟨t, ht, hfix⟩ := invariantCocharacterPoint_fixed C E a σ y' hf π
    obtain ⟨n, hn⟩ := (hjfix (t ≫ C.realization.pinned.pair.T.inclusion.hom.hom)).mpr hfix
    have hn' : j n = torusPoint D S (cocharacter D y' S u) ≫ M.torus.hom.hom := hn.trans ht
    exact ⟨n, hTN n (hjT _ _ hn'), hn'⟩
  obtain ⟨nPos, hnPos, hjPos⟩ := hyN y (hy e)
  obtain ⟨nNeg, hnNeg, hjNeg⟩ := hyN (-y) (by rw [map_neg, hy])
  let ground := CommAlgCat.of k k
  let ev := ((integralPointFunctor M.group).map (evaluateGroundTensor k K)).hom
  have hR (p : HopfPoints (Specs.AdjointCocharacters.coordinateHopf d.group) k) :
      ev (pinnedMarkedPoint C d.data ground p) ∈ j.range := by
    obtain ⟨g, rfl⟩ := (groundHopfEquiv d.group).surjective p
    exact ⟨g, (hjpoint g).trans (pinnedGroundPoint_apply C d.data g)⟩
  have hW (l : List (TransportedOrbit D))
      (hl : ∀ o ∈ l, o.1.Matches C (pinnedDiagram d.data σ) ∧
        ∀ p ∈ o.2, p.Matches C (pinnedDiagram d.data σ))
      (z : rationalOrderedParameters k K l) :
      splitOrderedOrbitPoint M.toIntegralMarking S l (rationalOrderedCoordinates σ l z) ∈ j.range := by
    obtain ⟨g, hg⟩ := pinnedRationalWord_range C d.data σ hd hσ hpair l hl z
    exact ⟨g, (hjpoint g).trans hg⟩
  have hcontract (l : List (TransportedOrbit D)) (hl : (l.flatMap transportedLabels).Nodup)
      (z : rationalOrderedParameters k K l) (g n : Gp) (y' : D.Y)
      (hn' : n ∈ N) (hm : j n = torusPoint D S (cocharacter D y' S u) ≫ M.torus.hom.hom)
      (hpos : ∀ a ∈ l.flatMap transportedLabels, 0 < D.datum.toLinearMap (D.datum.root a) y')
      (hg : j g = splitOrderedOrbitPoint M.toIntegralMarking S l (rationalOrderedCoordinates σ l z)) :
      g ∈ H := by
    obtain ⟨v, hv⟩ := splitOrbitWord_expansion M σ l hl z
    obtain ⟨m, _, hm'⟩ := markedRootWordContraction M.toIntegralMarking B₀ y' u 2 (by decide) hu
      (l.flatMap transportedLabels) hpos v 0
    have hIg : n ^ m * g * (n ^ m)⁻¹ ∈ I := by
      change j (n ^ m * g * (n ^ m)⁻¹) ∈ markedBorelReduction M.group B₀
      rw [map_mul, map_mul, map_inv, map_pow, hm, hg, hv]
      exact hm'
    have hN' := H.pow_mem (hNH hn') m
    have hg' := H.mul_mem (H.mul_mem (H.inv_mem hN') (hIH hIg)) hN'
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hg'
  have hB (b' : 𝟙_ (SchemeOver k) ⟶ d.borel.group.X) : b' ≫ d.borel.inclusion.hom.hom ∈ H := by
    let bG := b' ≫ d.borel.inclusion.hom.hom
    have hchart := hjB b'
    rw [markedPositiveBorelCoordinates C R (ps.flatMap transportedLabels) hp] at hchart
    obtain ⟨⟨t, w⟩, ht⟩ := hchart
    let v (a : D.I) : S := if D.base.IsPos a then w a else 0
    have hNegative : orderedRootPoint M.toIntegralMarking S (ns.flatMap transportedLabels) v = 1 :=
      orderedRootPoint_eq_one_of_zero _ _ _ _ (fun a ha => ite_eq_right ((hn.2 a).mp ha))
    have hPositive : orderedRootPoint M.toIntegralMarking S (ps.flatMap transportedLabels) v =
        orderedRootPoint M.toIntegralMarking S (ps.flatMap transportedLabels) w :=
      orderedRootPoint_congr _ _ _ (fun a ha => ite_eq_left ((hp.2 a).mp ha))
    have hAbs : j bG ∈ Set.range (markedAbsoluteCell M.toIntegralMarking S
        (ns.flatMap transportedLabels) (ps.flatMap transportedLabels) false) := by
      refine ⟨(v, t), ?_⟩
      change orderedRootPoint M.toIntegralMarking S _ v * ((t ≫ M.torus.hom.hom) *
        orderedRootPoint M.toIntegralMarking S _ v) = _
      rw [hNegative, one_mul, hPositive]
      exact ht
    obtain ⟨_, hcell⟩ := pinnedRationalFixedCellCoordinates C d.data hd σ hσ hpair ns ps hbs hn hp false
    have hf : j bG ∈ Set.range (pinnedRationalRelativeCell C d.data σ ns ps false) := by
      rw [hcell]
      refine ⟨hAbs, ?_⟩
      exact ⟨(coordinatePointEquiv d.group ground).symm (toUnit _ ≫ bG), (hjpoint bG).symm⟩
    obtain ⟨⟨zNeg, t₀, zPos⟩, he⟩ := hf
    obtain ⟨gNeg, hgNeg⟩ := hW ns (fun a ha => hbs a (List.mem_append_left _ ha)) zNeg
    obtain ⟨gPos, hgPos⟩ := hW ps (fun a ha => hbs a (List.mem_append_right _ ha)) zPos
    let tK := (integralPointFunctor (splitTorus D)).map (evaluateGroundTensor k K)
      (pinnedMarkedTorusPoint C d.data ground t₀)
    have htK : tK ≫ M.torus.hom.hom ∈ j.range := by
      obtain ⟨_, ht₀, _⟩ := pinnedMarkedTorusPointComparison C d.data ground
      have h := hR (descendedTorusInclusion ground t₀)
      have heq := (congrArg ev (ht₀ t₀)).trans
        (markedTorusPoint_map M.toIntegralMarking (evaluateGroundTensor k K) _)
      exact heq ▸ h
    obtain ⟨gT, hgT⟩ := htK
    have hgTN := hTN gT (hjT _ _ hgT)
    have hHNeg := hcontract ns hn.1 zNeg gNeg nNeg (-y) hnNeg hjNeg (by
      intro a ha
      rw [map_neg, hheight]
      have hh : D.base.height a < 0 := lt_of_not_ge (fun h => (hn.2 a).mp ha (D.base.isPos_iff'.mpr h))
      omega) hgNeg
    have hHPos := hcontract ps hp.1 zPos gPos nPos y hnPos hjPos (by
      intro a ha
      rw [hheight]
      have hh : 0 < D.base.height a := (D.base.isPos_iff.mp ((hp.2 a).mp ha))
      omega) hgPos
    have hcomp : gNeg * (gT * gPos) = bG := by
      apply hj
      rw [map_mul, map_mul, hgNeg, hgT, hgPos]
      exact he
    change bG ∈ H
    rw [← hcomp]
    exact H.mul_mem hHNeg (H.mul_mem (hNH hgTN) hHPos)
  apply top_unique
  intro g _
  obtain ⟨b₁, b₂, n, rfl⟩ := rationalBorelFactorization d.group d.reductive S₀ d.borel
    hS₀ (borelMinimalParabolic d.reductive d.borel d.isKBorel)
    (subgroupOf_trans hST ⟨d.inclusion, d.inclusion_comm⟩) Q₀.normalizer Q₀.normalizerProperty g
  exact H.mul_mem (H.mul_mem (hB b₁) (hNH ⟨n, rfl⟩)) (hB b₂)

end FoldedGeneration

section FoldedRootWords

open _root_.LinearAlgebraicGroups.Specs.IntegralSemisimpleModel
open _root_.LinearAlgebraicGroups.Specs.ExceptionalMarkedRootDescent

attribute [local instance] integerAlgebra

private theorem weylWordPerm_comm {D E : Pinning.BasedRootDatum.{u}} (e : D.I ≃ E.I)
    (he : ∀ a x, e (D.datum.reflectionPerm a x) = E.datum.reflectionPerm (e a) (e x))
    (w : List D.I) (x : D.I) :
    e (weylWordPerm w x) = weylWordPerm (w.map e) (e x) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    change e (D.datum.reflectionPerm a (weylWordPerm w x)) =
      E.datum.reflectionPerm (e a) (weylWordPerm (w.map e) (e x))
    rw [he, ih]

set_option backward.isDefEq.respectTransparency false in
private theorem foldedOrbitMap {k K : Type u} [Field k] [Field K] [Algebra k K]
    {D E : Pinning.BasedRootDatum.{u}} {M : Model D} {A : Model E}
    (f : M.group ⟶ A.group) (e : D.I ≃ E.I)
    (χ : Multiplicative E.X →* Multiplicative D.X)
    (hf : PreservesIntegralMarking f e χ)
    (he : ∀ a, e (D.datum.reflectionPerm a a) = E.datum.reflectionPerm (e a) (e a))
    (σ : Gal(K/k)) (b : TransportedOrbit D) (b' : TransportedOrbit E)
    (hb : b.1.roots.map e = b'.1.roots)
    (hw : (b.2.flatMap SimpleRootOrbit.roots).map e = b'.2.flatMap SimpleRootOrbit.roots) :
    let R := CommAlgCat.of Integers.{u} K
    ∃ j : rationalOrbitParameter k K b ≃ rationalOrbitParameter k K b',
      ∀ x, integralPointHom f R (splitOrbitPoint M.toIntegralMarking R b
        (rationalOrbitCoordinates σ b x)) =
        splitOrbitPoint A.toIntegralMarking R b' (rationalOrbitCoordinates σ b' (j x)) := by
  intro R
  let p := integralPointHom f R
  let n := markedWeylWord M.toIntegralMarking R (b.2.flatMap SimpleRootOrbit.roots)
  let n' := markedWeylWord A.toIntegralMarking R (b'.2.flatMap SimpleRootOrbit.roots)
  have hn : p n = n' := by
    change integralPointHom f R (markedWeylWord M.toIntegralMarking R _) = _
    rw [(markedRankOneMapCompatibility f e χ hf he).2, hw]
  have hroot (a : D.I) (x : R) :
      p (n * markedRootPoint M.toIntegralMarking R a x * n⁻¹) =
      n' * markedRootPoint A.toIntegralMarking R (e a) x * n'⁻¹ := by
    rw [map_mul, map_mul, map_inv, hn, hf.2.1]
  rcases b with ⟨⟨a, c⟩, w⟩
  rcases b' with ⟨⟨a', c'⟩, w'⟩
  cases c <;> cases c' <;> simp [SimpleRootOrbit.roots] at hb
  · refine ⟨Equiv.refl k, fun x => ?_⟩
    change p (n * markedRootPoint M.toIntegralMarking R a (algebraMap k K x) * n⁻¹) =
      n' * markedRootPoint A.toIntegralMarking R a' (algebraMap k K x) * n'⁻¹
    rw [hroot, hb]
  · rename_i c c'
    refine ⟨Equiv.refl K, fun x => ?_⟩
    change p ((n * markedRootPoint M.toIntegralMarking R a x * n⁻¹) *
        (n * markedRootPoint M.toIntegralMarking R c (σ x) * n⁻¹)) =
      (n' * markedRootPoint A.toIntegralMarking R a' x * n'⁻¹) *
        (n' * markedRootPoint A.toIntegralMarking R c' (σ x) * n'⁻¹)
    rw [map_mul, hroot, hroot, hb.1, hb.2]

set_option backward.isDefEq.respectTransparency false in
theorem foldedRootWordCompatibility : FoldedRootWordCompatibility.{u} := by
  intro k K _ _ _ D E M A f e χ hf he σ l l' hl
  let R := CommAlgCat.of Integers.{u} K
  let p := integralPointHom f R
  induction hl with
  | nil =>
    exact ⟨rfl, Equiv.refl PUnit, fun _ => map_one p⟩
  | @cons b b' l l' hb _ ih =>
    obtain ⟨hle, j, hj⟩ := ih
    obtain ⟨j₀, hj₀⟩ := foldedOrbitMap f e χ hf (fun a => he a a) σ b b' hb.1 hb.2
    constructor
    · have h (a : D.I) :
          e (weylWordPerm (b.2.flatMap SimpleRootOrbit.roots) a) =
            weylWordPerm (b'.2.flatMap SimpleRootOrbit.roots) (e a) := by
        rw [weylWordPerm_comm e he, hb.2]
      simp only [List.flatMap_cons, List.map_append, hle, transportedLabels, List.map_map]
      congr 1
      calc
        _ = b.1.roots.map (fun a => weylWordPerm (b'.2.flatMap SimpleRootOrbit.roots) (e a)) :=
          List.map_congr_left (fun a _ => h a)
        _ = _ := by change b.1.roots.map (_ ∘ e) = _; rw [← List.map_map, hb.1]
    · refine ⟨j₀.prodCongr j, fun x => ?_⟩
      change p (splitOrbitPoint M.toIntegralMarking R b (rationalOrbitCoordinates σ b x.1) *
          splitOrderedOrbitPoint M.toIntegralMarking R l (rationalOrderedCoordinates σ l x.2)) =
        splitOrbitPoint A.toIntegralMarking R b' (rationalOrbitCoordinates σ b' (j₀ x.1)) *
          splitOrderedOrbitPoint A.toIntegralMarking R l' (rationalOrderedCoordinates σ l' (j x.2))
      rw [map_mul, hj₀, hj]

end FoldedRootWords

section FoldedIntegralImage

open _root_.LinearAlgebraicGroups.Specs.IntegralSemisimpleModel
open _root_.LinearAlgebraicGroups.Specs.ExceptionalMarkedRootDescent
open _root_.LinearAlgebraicGroups.Specs.ExceptionalValuedTorusNormalizer (valuationRingInclusion)
open _root_.LinearAlgebraicGroups.Specs.OrderedRootProducts (Enumerates)
open _root_.LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
  (markedCellCoordinates pinnedRationalFixedCellCoordinates)
open private affineTorusPointEquiv from LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
open private markedTorusPointHom markedTorusPointHom_apply markedTorusPoint_map from
  LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent

attribute [local instance] integerAlgebra

set_option backward.isDefEq.respectTransparency false in
private theorem iwahori_chart_factors {K : Type u} [Field K] [ValuativeRel K]
    {D : Pinning.BasedRootDatum.{u}} {M : Model D}
    (C : MarkedFibre M (IsLocalRing.ResidueField (valuation K).valuationSubring))
    (B : Subgroup (IntegralPoints M.group (CommAlgCat.of Integers.{u}
      (IsLocalRing.ResidueField (valuation K).valuationSubring))))
    (hB : (B : Set _) = markedPositiveBorel C
      (CommAlgCat.of (IsLocalRing.ResidueField (valuation K).valuationSubring)
        (IsLocalRing.ResidueField (valuation K).valuationSubring)))
    (ns ps : List D.I)
    (hn : Enumerates ns {a | ¬ D.base.IsPos a}) (hp : Enumerates ps {a | D.base.IsPos a}) :
    let R := CommAlgCat.of Integers.{u} K
    let I := markedBorelReduction M.group B
    ∀ (v w : D.I → R) (t : IntegralPoints (splitTorus D) R),
      let n := orderedRootPoint M.toIntegralMarking R ns v
      let p := orderedRootPoint M.toIntegralMarking R ps w
      n * ((t ≫ M.torus.hom.hom) * p) ∈ I →
        n ∈ I ∧ t ≫ M.torus.hom.hom ∈ integralUnitTorus (K := K) M ∧ p ∈ I := by
  classical
  intro R I v w t n p hg
  let O := (valuation K).valuationSubring
  let S := CommAlgCat.of Integers.{u} O
  let inc := valuationRingInclusion K
  let iG : IntegralPoints M.group S →* IntegralPoints M.group R :=
    ((integralPointFunctor M.group).map inc).hom
  let iT : IntegralPoints (splitTorus D) S →* IntegralPoints (splitTorus D) R :=
    ((integralPointFunctor (splitTorus D)).map inc).hom
  have hdepth := iwahoriDepthCoordinates C B hB ns ps hn hp
  obtain ⟨z, a, hz, he⟩ := (hdepth _).mp hg
  let a₀ := torusPoint D S a
  let y (i : D.I) := if D.base.IsPos i then w i else v i
  have hy₁ : orderedRootPoint M.toIntegralMarking R ns y = n :=
    orderedRootPoint_congr _ _ _ (fun i hi => if_neg ((hn.2 i).mp hi))
  have hy₂ : orderedRootPoint M.toIntegralMarking R ps y = p :=
    orderedRootPoint_congr _ _ _ (fun i hi => if_pos ((hp.2 i).mp hi))
  have hcell : markedCellPoint M.toIntegralMarking R ns ps (fun i => inc.hom (z i)) (iT a₀) =
      markedCellPoint M.toIntegralMarking R ns ps y t := by
    have hi : iG (markedCellPoint M.toIntegralMarking S ns ps z a₀) =
        markedCellPoint M.toIntegralMarking R ns ps (fun i => inc.hom (z i)) (iT a₀) :=
      markedCellPoint_map M.toIntegralMarking inc ns ps z a₀
    rw [← hi]
    change _ = orderedRootPoint M.toIntegralMarking R ns y *
      ((t ≫ M.torus.hom.hom) * orderedRootPoint M.toIntegralMarking R ps y)
    rw [hy₁, hy₂]
    exact he
  have hcoords : ((fun i => inc.hom (z i)), iT a₀) = (y, t) :=
    (markedCellCoordinates M.toIntegralMarking R ns ps hn hp).1 hcell
  have hy : (fun i => inc.hom (z i)) = y := congrArg Prod.fst hcoords
  have ht : iT a₀ = t := congrArg Prod.snd hcoords
  have htu : t ≫ M.torus.hom.hom ∈ integralUnitTorus (K := K) M :=
    ⟨a₀, congrArg (fun s : IntegralPoints (splitTorus D) R => s ≫ M.torus.hom.hom) ht⟩
  let oneT : TorusValues D S := 1
  have hone : (torusPoint D S oneT ≫ M.torus.hom.hom : IntegralPoints M.group S) = 1 :=
    (markedTorusPointHom_apply M.toIntegralMarking S oneT).symm.trans
      ((markedTorusPointHom M.toIntegralMarking S).map_one)
  have hmid : (iT (torusPoint D S oneT) ≫ M.torus.hom.hom : IntegralPoints M.group R) = 1 :=
    (markedTorusPoint_map M.toIntegralMarking inc (torusPoint D S oneT)).symm.trans
      ((congrArg iG hone).trans iG.map_one)
  have hword (z' : D.I → O) :
      iG (markedCellPoint M.toIntegralMarking S ns ps z' (torusPoint D S oneT)) =
        orderedRootPoint M.toIntegralMarking R ns (fun i => inc.hom (z' i)) *
          orderedRootPoint M.toIntegralMarking R ps (fun i => inc.hom (z' i)) := by
    have hm := markedCellPoint_map M.toIntegralMarking inc ns ps z' (torusPoint D S oneT)
    change iG _ = _ at hm
    rw [hm]
    change _ * ((iT (torusPoint D S oneT) ≫ M.torus.hom.hom) * _) = _
    rw [hmid, one_mul]
  refine ⟨(hdepth n).mpr ?_, htu, (hdepth p).mpr ?_⟩
  · let z' (i : D.I) : O := if D.base.IsPos i then 0 else z i
    refine ⟨z', oneT, fun i hi => ?_, ?_⟩
    · simpa only [z', if_neg ((hn.2 i).mp hi)] using hz i hi
    · change iG _ = n
      have hzero := orderedRootPoint_eq_one_of_zero M.toIntegralMarking R ps
        (fun i => inc.hom (z' i)) (fun i hi => by
          have h : z' i = 0 := ite_eq_left ((hp.2 i).mp hi)
          exact (congrArg inc.hom h).trans (map_zero _))
      rw [hword, hzero, mul_one, ← hy₁, ← hy]
      exact orderedRootPoint_congr _ _ _ (fun i hi =>
        congrArg inc.hom (if_neg ((hn.2 i).mp hi)))
  · let z' (i : D.I) : O := if D.base.IsPos i then z i else 0
    refine ⟨z', oneT, fun i hi => ?_, ?_⟩
    · simp only [z', if_neg ((hn.2 i).mp hi), ZeroMemClass.coe_zero, map_zero, zero_lt_one]
    · change iG _ = p
      have hzero := orderedRootPoint_eq_one_of_zero M.toIntegralMarking R ns
        (fun i => inc.hom (z' i)) (fun i hi => by simp only [z', if_neg ((hn.2 i).mp hi), map_zero])
      rw [hword, hzero, one_mul, ← hy₂, ← hy]
      exact orderedRootPoint_congr _ _ _ (fun i hi =>
        congrArg inc.hom (if_pos ((hp.2 i).mp hi)))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 850000 in
theorem foldedIwahoriImageAndPreimage : FoldedIwahoriImageAndPreimage.{u} := by
  classical
  intro k K _ _ _ _ _ _ _ _ D E M A f e χ hf hindex hrefl R fK htor
    C C' l l' G G' B T B' T' d d' p p₀ hcmp hdegree σ hσ hpair hpair'
    ns ps ns' ps' hbs hbs' hns hps hn' hp' κ C₀ C₀' B₀ B₀' hB₀ hB₀'
  obtain ⟨j, hj, hjpoint, _, _, _⟩ := pinnedGroundPointComparison C d σ hdegree hσ
  obtain ⟨j', hj', hjpoint', _, hjT', _⟩ := pinnedGroundPointComparison C' d' σ hdegree hσ
  refine ⟨j, j', hj, hj', hjpoint, hjpoint', ?_⟩
  dsimp only
  let L := markedBorelReduction M.group B₀
  let L' := markedBorelReduction A.group B₀'
  let I := L.comap j
  let I' := L'.comap j'
  let U := (integralUnitTorus (K := K) A).comap j'
  have hcomm (g) : j' (p₀ g) = fK (j g) :=
    (hjpoint' _).trans ((hcmp g).trans (congrArg fK (hjpoint g).symm))
  have hpre : L'.comap fK = L :=
    splitIwahoriPreimage M A f e χ hf hindex htor C₀ C₀' B₀ B₀' hB₀ hB₀'
  have hpre₀ : I'.comap p₀ = I := by
    ext g
    change j' (p₀ g) ∈ L' ↔ j g ∈ L
    rw [hcomm, ← hpre]
    rfl
  refine ⟨hpre₀, ?_, ?_⟩
  · apply le_antisymm
    · intro g hg
      let n := ns'.flatMap transportedLabels
      let s := ps'.flatMap transportedLabels
      have hI : j' g ∈ L' := hg
      obtain ⟨z, t, _, ht⟩ := (iwahoriDepthCoordinates C₀' B₀' hB₀' n s hn' hp' (j' g)).mp hI
      have hAbs : j' g ∈ Set.range (markedAbsoluteCell A.toIntegralMarking R n s false) := by
        let O := (valuation K).valuationSubring
        let S := CommAlgCat.of Integers.{u} O
        let i := valuationRingInclusion K
        refine ⟨(fun a => i.hom (z a),
          (integralPointFunctor (splitTorus E)).map i (torusPoint E S t)), ?_⟩
        change markedCellPoint A.toIntegralMarking R n s (fun a => i.hom (z a)) _ = _
        rw [← markedCellPoint_map]
        exact ht
      obtain ⟨_, hcell⟩ :=
        pinnedRationalFixedCellCoordinates C' d' hdegree σ hσ hpair' ns' ps' hbs' hn' hp' false
      have hRel : j' g ∈ Set.range (pinnedRationalRelativeCell C' d' σ ns' ps' false) := by
        rw [hcell]
        exact ⟨hAbs, ⟨(coordinatePointEquiv G' (CommAlgCat.of k k)).symm (toUnit _ ≫ g),
          (hjpoint' g).symm⟩⟩
      obtain ⟨⟨zN, t₁, zP⟩, hgchart⟩ := hRel
      obtain ⟨_, en, hen⟩ := foldedRootWordCompatibility f e χ hf hrefl σ ns ns' hns
      obtain ⟨_, ep, hep⟩ := foldedRootWordCompatibility f e χ hf hrefl σ ps ps' hps
      obtain ⟨wN, rfl⟩ := en.surjective zN
      obtain ⟨wP, rfl⟩ := ep.surjective zP
      obtain ⟨gN, hgN⟩ := pinnedRationalWord_range C d σ hdegree hσ hpair ns
        (fun a ha => hbs a (List.mem_append_left _ ha)) wN
      obtain ⟨gP, hgP⟩ := pinnedRationalWord_range C d σ hdegree hσ hpair ps
        (fun a ha => hbs a (List.mem_append_right _ ha)) wP
      let n₁ : IntegralPoints A.group R :=
        splitOrderedOrbitPoint A.toIntegralMarking R ns' (rationalOrderedCoordinates σ ns' (en wN))
      let p₁ : IntegralPoints A.group R :=
        splitOrderedOrbitPoint A.toIntegralMarking R ps' (rationalOrderedCoordinates σ ps' (ep wP))
      let t₂ : IntegralPoints (splitTorus E) R :=
        (integralPointFunctor (splitTorus E)).map (evaluateGroundTensor k K)
        (pinnedMarkedTorusPoint C' d' (CommAlgCat.of k k) t₁)
      have hgN' : j' (p₀ gN) = n₁ := (hcomm gN).trans
        ((congrArg fK ((hjpoint gN).trans hgN)).trans (hen wN))
      have hgP' : j' (p₀ gP) = p₁ := (hcomm gP).trans
        ((congrArg fK ((hjpoint gP).trans hgP)).trans (hep wP))
      have hg' : n₁ * ((t₂ ≫ A.torus.hom.hom : IntegralPoints A.group R) * p₁) = j' g := hgchart
      obtain ⟨v, hv⟩ := splitOrbitWord_expansion A σ ns' hn'.1 (en wN)
      obtain ⟨w, hw⟩ := splitOrbitWord_expansion A σ ps' hp'.1 (ep wP)
      have hL : n₁ ∈ L' ∧ t₂ ≫ A.torus.hom.hom ∈ integralUnitTorus (K := K) A ∧ p₁ ∈ L' := by
        change n₁ = orderedRootPoint A.toIntegralMarking R n v at hv
        change p₁ = orderedRootPoint A.toIntegralMarking R s w at hw
        rw [hv, hw] at hg' ⊢
        apply iwahori_chart_factors C₀' B₀' hB₀' n s hn' hp' v w t₂
        rwa [hg']
      have hN : gN ∈ I := by
        change j gN ∈ L
        rw [← hpre]
        change fK (j gN) ∈ L'
        rw [← hcomm, hgN']
        exact hL.1
      have hP : gP ∈ I := by
        change j gP ∈ L
        rw [← hpre]
        change fK (j gP) ∈ L'
        rw [← hcomm, hgP']
        exact hL.2.2
      let gT := (p₀ gN)⁻¹ * g * (p₀ gP)⁻¹
      have hgT : j' gT = t₂ ≫ A.torus.hom.hom := by
        change j' ((p₀ gN)⁻¹ * g * (p₀ gP)⁻¹) = _
        rw [map_mul, map_mul, map_inv, map_inv, hgN', hgP', ← hg']
        group
      have hU : gT ∈ U := by
        change j' gT ∈ integralUnitTorus (K := K) A
        exact hgT.symm ▸ hL.2.1
      have hprod : p₀ gN * (gT * p₀ gP) = g := by dsimp only [gT]; group
      rw [← hprod]
      have himage : I.map p₀ ≤ I.map p₀ ⊔ U := le_sup_left
      have hunit : U ≤ I.map p₀ ⊔ U := le_sup_right
      exact (I.map p₀ ⊔ U).mul_mem (himage ⟨gN, hN, rfl⟩)
        ((I.map p₀ ⊔ U).mul_mem (hunit hU) (himage ⟨gP, hP, rfl⟩))
    · apply sup_le (Subgroup.map_le_iff_le_comap.mpr hpre₀.ge)
      apply Subgroup.comap_mono
      change integralUnitTorus A ≤ markedBorelReduction A.group B₀'
      rw [splitIwahoriImage M A f e χ hf C₀ C₀' B₀ B₀' hB₀ hB₀']
      exact le_sup_right
  · rintro x ⟨t, ht⟩
    exact hjT' _ x ht.symm

end FoldedIntegralImage

section NormalizerPresentation

open _root_.LinearAlgebraicGroups.Specs.IntegralSemisimpleModel
open _root_.LinearAlgebraicGroups.Specs.ExceptionalValuedTorusNormalizer
open _root_.LinearAlgebraicGroups.Arithmetic.ExceptionalValuedTorusNormalizer
  (fibreNormalizerTorusAction splitTorusTranslation integralTorusCoordinates)
open scoped Matrix
open private rankOneMatrixWord_val wallMatrix_val from
  LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
open private fibrePointsEquiv affineTorusPointEquiv torusPoint_natural from LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
open private groundIso from LinearAlgebraicGroups.Solvable.TorusSections
open private markedTorusPointHom markedTorusPointHom_apply from
  LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent

attribute [local instance] integerAlgebra

set_option backward.isDefEq.respectTransparency false in
private theorem fibreNormalizerPoint_injective {k : Type u} [Field k] {D : Pinning.BasedRootDatum.{u}}
    {M : Model D} (F : FibreNormalizer M k) :
    Function.Injective F.point := by
  letI := F.torusComm
  intro x y h
  let Y := (testSpec k).obj (Opposite.op (CommAlgCat.of k k))
  have h' : (toUnit Y ≫ x ≫ F.identification.normalizer.inclusion.hom.hom) ≫ F.fibreIso.inv.hom.hom =
      (toUnit Y ≫ y ≫ F.identification.normalizer.inclusion.hom.hom) ≫ F.fibreIso.inv.hom.hom := by
    rw [Category.assoc, Category.assoc]
    exact (fibrePointsEquiv M.group (CommAlgCat.of k k)).injective
      ((F.point_eq x).symm.trans (h.trans (F.point_eq y)))
  letI : IsClosedImmersion F.identification.normalizer.inclusion.hom.hom.left :=
    F.identification.normalizer.isClosedImmersion
  letI : Mono F.identification.normalizer.inclusion.hom.hom := Over.mono_of_mono_left _
  have ht := (cancel_mono F.fibreIso.inv.hom.hom).mp h'
  simp only [← Category.assoc] at ht
  have h'' := (cancel_mono F.identification.normalizer.inclusion.hom.hom).mp ht
  rw [show toUnit Y = (groundIso (k := k)).hom from Subsingleton.elim _ _] at h''
  exact (cancel_epi (groundIso (k := k)).hom).mp h''

private theorem markedWeylWord_inv {D : Pinning.BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (a : D.I) :
    (markedWeylWord M a R 1)⁻¹ = ExceptionalMarkedRootDescent.markedWall M R a 1 := by
  let h : Matrix.SpecialLinearGroup (Fin 2) R →* IntegralPoints M.group R :=
    ((M.rankOne a).app R).hom
  change (h (ExceptionalMarkedRootDescent.rankOneMatrixWord 1))⁻¹ =
    h (ExceptionalMarkedRootDescent.wallMatrix 1)
  rw [← h.map_inv]
  apply congrArg h
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_inv, rankOneMatrixWord_val, Matrix.adjugate_fin_two, wallMatrix_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem splitMarkedNormalizerWord {K : Type u} [Field K] {D : Pinning.BasedRootDatum.{u}}
    {M : Model D} (F : FibreNormalizer M K)
    (l : List D.I) (hl : ∀ i ∈ l, i ∈ D.base.support) :
    ∃ n, F.point n = ExceptionalMarkedRootDescent.markedWeylWord M.toIntegralMarking
        (CommAlgCat.of Integers.{u} K) l ∧
      F.label n = (l.map (RootPairing.weylGroup.ofIdx D.datum)).prod := by
  induction l with
  | nil => exact ⟨1, map_one F.point, map_one F.label⟩
  | cons a l ih =>
    obtain ⟨m, hp, hq⟩ := ih (fun i hi => hl i (List.mem_cons_of_mem _ hi))
    obtain ⟨_, n, _, ha, hn, _⟩ := F.simple ⟨a, hl a List.mem_cons_self⟩
    refine ⟨n⁻¹ * m, ?_, ?_⟩
    · rw [map_mul, map_inv, hn, hp, markedWeylWord_inv]
      rfl
    · rw [map_mul, map_inv, ha, hq]
      have h₁ : (RootPairing.weylGroup.ofIdx D.datum a)⁻¹ = RootPairing.weylGroup.ofIdx D.datum a :=
        Subtype.ext (RootPairing.Equiv.reflection_inv D.datum a)
      rw [h₁]
      rfl

private theorem valuationRingTorusPoint {K : Type u} [Field K] [ValuativeRel K]
    {D : Pinning.BasedRootDatum.{u}} (M : Model D)
    (v : TorusValues D (CommAlgCat.of Integers.{u} (valuation K).valuationSubring)) :
    ((integralPointFunctor (splitTorus D)).map (valuationRingInclusion K)
      (torusPoint D _ v) ≫ M.torus.hom.hom : IntegralPoints M.group (CommAlgCat.of Integers.{u} K)) =
    torusPoint D _ ((Units.map (valuation K).valuationSubring.subtype.toMonoidHom).comp v) ≫
      M.torus.hom.hom :=
  congrArg (fun t : IntegralPoints (splitTorus D) (CommAlgCat.of Integers.{u} K) =>
    t ≫ M.torus.hom.hom) (torusPoint_natural (valuationRingInclusion K) v)

set_option backward.isDefEq.respectTransparency false in
theorem splitMarkedNormalizerPresentation : SplitMarkedNormalizerPresentation.{u} := by
  classical
  intro K _ _ _ _ D M F index _ b word hword hprod R
  letI := F.torusComm
  let e := MonoidHom.ofInjective (fibreNormalizerPoint_injective F)
  obtain ⟨j, hj, _⟩ := fibreNormalizerTorusAction F
  obtain ⟨ν, hν, hlog, hunit⟩ := splitTorusTranslation K D b
  choose lift hlift hl using fun w => splitMarkedNormalizerWord F (word w) (hword w)
  let k : TorusValues D R →* IntegralPoints M.group R := markedTorusPointHom M.toIntegralMarking R
  have hk (v : TorusValues D R) : k v = F.point (j v).val :=
    (markedTorusPointHom_apply _ _ _).trans (hj v).symm
  have hki : Function.Injective k := by
    intro v v' h
    rw [hk, hk] at h
    exact j.injective (Subtype.ext (fibreNormalizerPoint_injective F h))
  let eT := MonoidHom.ofInjective hki
  let q : F.point.range →* D.datum.weylGroup := F.label.comp e.symm.toMonoidHom
  have hker (n : F.point.range) : q n = 1 ↔ (n : IntegralPoints M.group R) ∈ k.range := by
    constructor
    · intro h
      let t : F.label.ker := ⟨e.symm n, h⟩
      refine ⟨j.symm t, (hk _).trans ?_⟩
      have he : F.point (j (j.symm t)).val = F.point (e.symm n) :=
        congrArg (fun z : F.label.ker => F.point z.val) (j.apply_symm_apply t)
      exact he.trans (congrArg Subtype.val (e.apply_symm_apply n))
    · rintro ⟨v, hv⟩
      have hnt : e ((j v).val) = n := Subtype.ext ((hk v).symm.trans hv)
      change F.label (e.symm n) = 1
      rw [← hnt, MulEquiv.symm_apply_apply]
      exact (j v).property
  have hTN : k.range ≤ F.point.range := by
    rintro _ ⟨v, rfl⟩
    exact ⟨(j v).val, (hk v).symm⟩
  let N : MarkedLocalNormalizer K (MonoidHom.id (IntegralPoints M.group R)) D.datum.weylGroup :=
    { torus := k.range
      normalizer := F.point.range
      torus_le := hTN
      torusPoints := fun g => by
        change (∃ t, k t = g) ↔ _
        exact exists_congr (fun _ => eq_comm)
      label := q
      labelKernel := hker
      translation := ν.comp eT.symm.toMonoidHom
      characterLog := fun t v ht x => by
        change (t : IntegralPoints M.group R) = torusPoint D R v ≫ M.torus.hom.hom at ht
        have he : eT v = t := Subtype.ext ((markedTorusPointHom_apply _ _ _).trans ht.symm)
        subst t
        change D.datum.toLinearMap x (ν (eT.symm (eT v))).toAdd = _
        rw [eT.symm_apply_apply]
        exact hlog v x
      word := word
      lift := fun w => e (lift w)
      lift_label := fun w => by
        change F.label (e.symm (e (lift w))) = w
        rw [e.symm_apply_apply, hl, hprod]
      lift_point := hlift }
  refine ⟨N, rfl, rfl, hν.comp eT.symm.surjective, ?_, ?_⟩
  · intro n h
    change F.label (e.symm (e n)) = F.label n
    rw [e.symm_apply_apply]
  · ext g
    change (∃ t : k.range, ν (eT.symm t) = 1 ∧ (t : IntegralPoints M.group R) = g) ↔ _
    constructor
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨s, hs⟩ := (integralTorusCoordinates D b (eT.symm t)).mp ((hunit _).mp ht)
      refine ⟨torusPoint D _ s, ?_⟩
      change ((integralPointFunctor (splitTorus D)).map (valuationRingInclusion K)
        (torusPoint D _ s)) ≫ M.torus.hom.hom = (t : IntegralPoints M.group R)
      exact (valuationRingTorusPoint M s).trans
        ((congrArg (fun v => torusPoint D R v ≫ M.torus.hom.hom) hs).trans
          ((markedTorusPointHom_apply _ _ _).symm.trans (congrArg Subtype.val (eT.apply_symm_apply t))))
    · rintro ⟨s, rfl⟩
      obtain ⟨v, rfl⟩ :=
        (affineTorusPointEquiv (k := Integers.{u}) (M := Multiplicative D.X) _).surjective s
      let t := (Units.map (valuation K).valuationSubring.subtype.toMonoidHom).comp v
      refine ⟨eT t, ?_, ?_⟩
      · rw [eT.symm_apply_apply]
        exact (hunit t).mpr ((integralTorusCoordinates D b t).mpr ⟨v, rfl⟩)
      · exact (markedTorusPointHom_apply _ _ _).trans
          (valuationRingTorusPoint M v).symm

end NormalizerPresentation

section MarkedOrdinarySubgroup

open _root_.LinearAlgebraicGroups.Specs.IntegralSemisimpleModel
open _root_.LinearAlgebraicGroups.Specs.ExceptionalValuedTorusNormalizer (valuationRingInclusion characterBasis)
open _root_.LinearAlgebraicGroups.Arithmetic.ExceptionalValuedTorusNormalizer (integralTorusCoordinates)
open private affineTorusPointEquiv torusPoint_natural from LinearAlgebraicGroups.Classification.IntegralSemisimpleModel

attribute [local instance] integerAlgebra

private theorem localNormalizer_unitKernel {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {D : Pinning.BasedRootDatum.{u}} {M : Model D}
    {G W : Type u} [Group G] [Group W]
    {j : G →* IntegralPoints M.group (CommAlgCat.of Integers.{u} K)}
    (N : MarkedLocalNormalizer K j W) :
    N.translation.ker.map N.torus.subtype = (integralUnitTorus (K := K) M).comap j := by
  letI := D.freeY
  letI := D.finiteY
  let index := Module.Free.ChooseBasisIndex ℤ D.Y
  letI : Fintype index := Fintype.ofFinite index
  let b : Module.Basis index ℤ D.Y := Module.Free.chooseBasis ℤ D.Y
  let R := CommAlgCat.of Integers.{u} K
  let O := (valuation K).valuationSubring
  let S := CommAlgCat.of Integers.{u} O
  let v := ExceptionalMarkedRootDescent.normalizedValuation K
  let inc := valuationRingInclusion K
  have hm (s : TorusValues D S) :
      ((integralPointFunctor (splitTorus D)).map inc (torusPoint D S s) ≫
          M.torus.hom.hom : IntegralPoints M.group R) =
        torusPoint D R ((Units.map O.subtype.toMonoidHom).comp s) ≫ M.torus.hom.hom :=
    congrArg (fun t : IntegralPoints (splitTorus D) R =>
      t ≫ M.torus.hom.hom) (torusPoint_natural inc s)
  have hv (t : N.torus) (s : TorusValues D R)
      (hs : j t = torusPoint D R s ≫ M.torus.hom.hom) :
      N.translation t = 1 ↔ ∀ i, v (s (Multiplicative.ofAdd (characterBasis D b i)) : K) = 1 := by
    have hlog := N.characterLog t s hs
    have hone (i : index) : v (s (Multiplicative.ofAdd (characterBasis D b i)) : K) ≠ 0 :=
      (map_ne_zero v).mpr (s (Multiplicative.ofAdd (characterBasis D b i))).ne_zero
    constructor
    · intro h i
      have h' := hlog (characterBasis D b i)
      rw [h] at h'
      have hz : log (v (s (Multiplicative.ofAdd (characterBasis D b i)) : K)) = 0 := by
        simpa using h'.symm
      rw [← exp_log (hone i), hz, exp_zero]
    · intro h
      apply Multiplicative.toAdd.injective
      have h' : ∀ x, D.datum.toLinearMap x (N.translation t).toAdd = 0 := by
        intro x
        rw [← (characterBasis D b).sum_repr x, map_sum]
        simp only [LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
        apply Finset.sum_eq_zero
        intro i _
        rw [hlog, h i, log_one, mul_zero]
      have hdual := D.datum.toLinearMap.flip.toPerfPair.injective
      apply hdual
      ext x
      exact (h' x).trans (by simp)
  ext g
  constructor
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨s, hs⟩ := (N.torusPoints t).mp t.property
    obtain ⟨r, hr⟩ := (integralTorusCoordinates D b s).mp ((hv t s hs).mp ht)
    exact ⟨torusPoint D S r, (hm r).trans ((congrArg
      (fun x => torusPoint D R x ≫ M.torus.hom.hom) hr).trans hs.symm)⟩
  · rintro ⟨r, hr⟩
    obtain ⟨s, rfl⟩ :=
      (affineTorusPointEquiv (k := Integers.{u}) (M := Multiplicative D.X) S).surjective r
    let t := (Units.map O.subtype.toMonoidHom).comp s
    have hp : j g = torusPoint D R t ≫ M.torus.hom.hom := hr.symm.trans (hm s)
    let x : N.torus := ⟨g, (N.torusPoints g).mpr ⟨t, hp⟩⟩
    exact ⟨x, (hv x t hp).mpr ((integralTorusCoordinates D b t).mpr ⟨s, rfl⟩), rfl⟩

set_option backward.isDefEq.respectTransparency false in
theorem markedOrdinaryIwahoriComparison : MarkedOrdinaryIwahoriComparison.{u} := by
  classical
  intro K _ _ _ _ D E M A c G G' W _ _ _ j j' N N' p hj' hp hw hT hN hnormal
    I I' U hgen hgen' hI Y ν Λ J H
  letI : p.range.Normal := hnormal
  let R := CommAlgCat.of Integers.{u} K
  have ht (t : N.torus) : p t ∈ N'.torus := (show (t : G) ∈ N'.torus.comap p by rw [hT]; exact t.property)
  have hn (n : N.normalizer) : p n ∈ N'.normalizer := (show (n : G) ∈ N'.normalizer.comap p by rw [hN]; exact n.property)
  let pN : N.normalizer →* N'.normalizer := (p.comp N.normalizer.subtype).codRestrict _ hn
  have hlift (w : W) : pN (N.lift w) = N'.lift w := by
    apply Subtype.ext
    apply hj'
    change j' (p (N.lift w)) = j' (N'.lift w)
    rw [hp, N.lift_point, N'.lift_point,
      (markedRankOneMapCompatibility c.map c.rootEquiv _ c.marking (fun a => c.reflections a a)).2, hw]
  have hlabel (n : N.normalizer) : N'.label (pN n) = N.label n := by
    let w := N.label n
    have e := (N'.labelKernel (pN (n * (N.lift w)⁻¹))).mpr (ht (N.torusPart n))
    rw [map_mul, map_inv, map_mul, map_inv, hlift, N'.lift_label] at e
    exact mul_inv_eq_one.mp e
  have hνmap (t : N.torus) (hm : p t ∈ N'.torus) :
      (N'.translation ⟨p t, hm⟩).toAdd = c.pushCocharacter (N.translation t).toAdd := by
    obtain ⟨v, hv⟩ := (N.torusPoints t).mp t.property
    have hv' : j' (p t) = torusPoint E R
          (v.comp c.pullCharacter.toAddMonoidHom.toMultiplicative) ≫ A.torus.hom.hom := by
      rw [hp, hv]
      exact c.marking.2.2 R v
    exact (markedTranslationCompatibility D E c.pullCharacter c.pushCocharacter c.pairing v
      (N.translation t).toAdd (N'.translation ⟨p t, hm⟩).toAdd
      (N.characterLog t v hv) (N'.characterLog ⟨p t, hm⟩ _ hv')).1.symm
  have hlift_range (w : W) : (N'.lift w : G') ∈ N.normalizer.map p :=
    ⟨N.lift w, (N.lift w).property, congrArg Subtype.val (hlift w)⟩
  have hU : ν.ker.map N'.torus.subtype = U := by
    change _ = (integralUnitTorus (K := K) A).comap j'
    rw [← localNormalizer_unitKernel N']
    congr 1
    ext t
    change ν t = 1 ↔ N'.translation t = 1
    exact Subtype.ext_iff
  have hUN : U ≤ N'.normalizer := by
    rw [← hU]
    rintro _ ⟨t, _, rfl⟩
    exact N'.torus_le t.property
  have hPleft : p.range ≤ p.range ⊔ N'.torus := le_sup_left
  have hTright : N'.torus ≤ p.range ⊔ N'.torus := le_sup_right
  have hfactor (g : G') : ∃ (x : G) (t : N'.torus), g = p x * t := by
    have hI' : I' ≤ p.range ⊔ N'.torus := by
      rw [hI, ← hU]
      refine sup_le (fun _ ⟨x, _, hx⟩ => hPleft (show _ ∈ p.range from ⟨x, hx⟩)) ?_
      rintro _ ⟨t, _, rfl⟩
      exact hTright t.property
    have hN' : N'.normalizer ≤ p.range ⊔ N'.torus := by
      intro n hn'
      let a : N'.normalizer := ⟨n, hn'⟩
      have ht' : (N'.torusPart a : G') ∈ p.range ⊔ N'.torus :=
        hTright (N'.torusPart a).property
      obtain ⟨x, _, hx⟩ := hlift_range (N'.label a)
      have hw' : (N'.lift (N'.label a) : G') ∈ p.range ⊔ N'.torus :=
        hPleft (show _ ∈ p.range from ⟨x, hx⟩)
      have h := (p.range ⊔ N'.torus).mul_mem ht' hw'
      simpa only [MarkedLocalNormalizer.torusPart, Subgroup.coe_mul, Subgroup.coe_inv,
        inv_mul_cancel_right] using h
    have hg : g ∈ p.range ⊔ N'.torus :=
      (hgen' ▸ sup_le hI' hN') (Subgroup.mem_top g)
    obtain ⟨_, ⟨x, rfl⟩, t, ht', rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hg
    exact ⟨x, ⟨t, ht'⟩, rfl⟩
  have hUI : U ≤ I' := hI ▸ le_sup_right
  have hIP : I' ≤ p.range ⊔ U := by
    rw [hI]
    have hleft : p.range ≤ p.range ⊔ U := le_sup_left
    exact sup_le (fun _ ⟨x, _, hx⟩ => hleft (show _ ∈ p.range from ⟨x, hx⟩)) le_sup_right
  have hPH : p.range ≤ H := by
    rw [← Subgroup.map_top, ← hgen, Subgroup.map_sup]
    exact sup_le ((hI ▸ le_sup_left : I.map p ≤ I').trans le_sup_left)
      ((le_sup_left : N.normalizer.map p ≤ J).trans le_sup_right)
  have hstable (t : N'.torus) (x : G) : (t : G') * p x * (t : G')⁻¹ ∈ p.range :=
    hnormal.conj_mem _ ⟨x, rfl⟩ _
  obtain ⟨hH, hJ, hQ, q, hq⟩ := ordinaryImageQuotient
    p N.torus N.normalizer N'.torus N'.normalizer I' J ν N'.torus_le
    N'.translation.rangeRestrict_surjective hfactor hstable hT hN (hU ▸ hUI) (hU ▸ hIP)
    (congrArg (fun V => N.normalizer.map p ⊔ V) hU.symm) hPH
  have hH' : H = p.range ⊔ U := hH.trans (congrArg (p.range ⊔ ·) hU)
  refine ⟨fun n _ => hlabel n, hνmap, ?_, hH', hJ, ?_, ⟨hQ, q, hq⟩⟩
  · intro n
    have hlJ : (N'.lift (N'.label n) : G') ∈ J := (show N.normalizer.map p ≤ J from le_sup_left) (hlift_range _)
    have hxJ : (n : G') ∈ J ↔ (N'.torusPart n : G') ∈ J := by
      constructor
      · intro h
        exact J.mul_mem h (J.inv_mem hlJ)
      · intro h
        have hm := J.mul_mem h hlJ
        simpa only [MarkedLocalNormalizer.torusPart, Subgroup.coe_mul, Subgroup.coe_inv,
          inv_mul_cancel_right] using hm
    have htor : ∀ t : N'.torus, (t : G') ∈ J ↔ ν t ∈ Λ := by
      intro t
      rw [← hJ]
      change ((t : G') ∈ H ∧ (t : G') ∈ N'.normalizer) ↔ _
      rw [and_iff_left (N'.torus_le t.property)]
      letI := hQ
      rw [← QuotientGroup.eq_one_iff, ← q.injective.eq_iff, hq, map_one, QuotientGroup.eq_one_iff]
    exact hxJ.trans (htor (N'.torusPart n))
  · intro g
    rw [hH', Subgroup.mem_sup_of_normal_left]
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, t, ht', rfl⟩
      exact ⟨x, ⟨t, ht'⟩, rfl⟩
    · rintro ⟨x, t, rfl⟩
      exact ⟨p x, ⟨x, rfl⟩, t, t.property, rfl⟩

end MarkedOrdinarySubgroup

section LayerAction

open _root_.LinearAlgebraicGroups.Specs.IntegralSemisimpleModel
open _root_.LinearAlgebraicGroups.Specs.ExceptionalMarkedRootDescent
open _root_.LinearAlgebraicGroups.Specs.ExceptionalValuedTorusNormalizer (valuationRingInclusion)
open _root_.LinearAlgebraicGroups.Specs.OrderedRootProducts (Enumerates)
open private markedTorusPointHom markedTorusPointHom_apply markedRootPoint_zero from
  LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
open private affineTorusPointEquiv from LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
open private ordered_single from LinearAlgebraicGroups.Classification.IntegralRootRelations
open scoped Classical

attribute [local instance] integerAlgebra

private theorem markedRootPoint_single {D : Pinning.BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (l : List D.I) (hl : l.Nodup) (a : D.I) (x : R) :
    let z : D.I → R := fun i => if i = a then x else 0
    orderedRootPoint M R l z = if a ∈ l then markedRootPoint M R a x else 1 := by
  classical
  intro z
  split_ifs with ha
  · rw [orderedRootPoint, ← ordered_single l hl a ha (markedRootPoint M R a x)]
    congr 1
    apply List.map_congr_left
    intro i _
    by_cases hi : i = a
    · simp [z, hi]
    · simp [z, hi, markedRootPoint_zero]
  · apply orderedRootPoint_eq_one_of_zero
    intro i hi
    change (if i = a then x else 0) = 0
    apply if_neg
    intro e
    exact ha (e ▸ hi)

section ReductionGenerators

private def allowedIwahoriRoot {K : Type u} [Field K] [ValuativeRel K]
    (D : Pinning.BasedRootDatum.{u}) (a : D.I) (x : K) : Prop :=
  valuation K x ≤ 1 ∧ (¬ D.base.IsPos a → valuation K x < 1)

variable {K : Type u} [Field K] [ValuativeRel K] {D : Pinning.BasedRootDatum.{u}} {M : Model D}
  (C : MarkedFibre M (IsLocalRing.ResidueField (valuation K).valuationSubring))
  (B : Subgroup (IntegralPoints M.group (CommAlgCat.of Integers.{u}
    (IsLocalRing.ResidueField (valuation K).valuationSubring))))
  (hB : (B : Set _) = markedPositiveBorel C (CommAlgCat.of
    (IsLocalRing.ResidueField (valuation K).valuationSubring)
    (IsLocalRing.ResidueField (valuation K).valuationSubring)))

include hB

set_option backward.isDefEq.respectTransparency false in
private theorem reduction_contains_unitTorus :
    integralUnitTorus (K := K) M ≤ markedBorelReduction M.group B := by
  classical
  let R := CommAlgCat.of Integers.{u} K
  let S := CommAlgCat.of Integers.{u} (valuation K).valuationSubring
  let inc := valuationRingInclusion K
  obtain ⟨l, r, hl, hr⟩ := positiveAndNegativeEnumerations D
  have hc := iwahoriDepthCoordinates C B hB l r hl hr
  rintro _ ⟨s, rfl⟩
  obtain ⟨t, rfl⟩ :=
    (affineTorusPointEquiv (k := Integers.{u}) (M := Multiplicative D.X) S).surjective s
  refine (hc _).mpr ⟨fun _ => 0, t, fun _ _ => by simp, ?_⟩
  simp only [markedCellPoint, orderedRootPoint_eq_one_of_zero _ _ _ _ (fun _ _ => rfl),
    one_mul, mul_one]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 400000 in
private theorem reduction_contains_rootLayer (a : D.I) (x : K) (hx : allowedIwahoriRoot D a x) :
    markedRootPoint M.toIntegralMarking (CommAlgCat.of Integers.{u} K) a x ∈
      markedBorelReduction M.group B := by
  classical
  let R := CommAlgCat.of Integers.{u} K
  let S := CommAlgCat.of Integers.{u} (valuation K).valuationSubring
  let inc := valuationRingInclusion K
  obtain ⟨l, r, hl, hr⟩ := positiveAndNegativeEnumerations D
  have hc := iwahoriDepthCoordinates C B hB l r hl hr
  let z (i : D.I) : S := if i = a then ⟨x, hx.1⟩ else 0
  refine (hc _).mpr ⟨z, 1, ?_, ?_⟩
  · intro i hi
    by_cases h : i = a
    · subst i
      simpa [z] using hx.2 ((hl.2 a).mp hi)
    · simp [z, h]
  · have hzero (i : D.I) : inc.hom (z i) = if i = a then x else 0 := by
      by_cases h : i = a
      · simp [z, h, inc, valuationRingInclusion]
      · simp [z, h]
    let j : IntegralPoints (splitTorus D) S →* IntegralPoints (splitTorus D) R :=
      ((integralPointFunctor (splitTorus D)).map inc).hom
    let k : IntegralPoints (splitTorus D) R →* IntegralPoints M.group R :=
      integralPointHom M.torus R
    have ht₀ : torusPoint D S 1 = (1 : IntegralPoints (splitTorus D) S) :=
      map_one (affineTorusPointEquiv (k := Integers.{u}) (M := Multiplicative D.X) S)
    have hT : k (j (torusPoint D S 1)) = 1 := by rw [ht₀, j.map_one, k.map_one]
    rw [markedCellPoint_map]
    change orderedRootPoint M.toIntegralMarking R l (fun i => inc.hom (z i)) *
      (k (j (torusPoint D S 1)) *
        orderedRootPoint M.toIntegralMarking R r (fun i => inc.hom (z i))) = _
    rw [hT, one_mul]
    have hl' := markedRootPoint_single M.toIntegralMarking R l hl.1 a x
    have hr' := markedRootPoint_single M.toIntegralMarking R r hr.1 a x
    rw [show (fun i => inc.hom (z i)) = (fun i => if i = a then x else 0) from funext hzero,
      hl', hr']
    by_cases ha : D.base.IsPos a
    · rw [if_neg (fun h => (hl.2 a).mp h ha), if_pos ((hr.2 a).mpr ha), one_mul]
    · rw [if_pos ((hl.2 a).mpr ha), if_neg (fun h => ha ((hr.2 a).mp h)), mul_one]

set_option backward.isDefEq.respectTransparency false in
private theorem reduction_le_of_layers
    (H : Subgroup (IntegralPoints M.group (CommAlgCat.of Integers.{u} K)))
    (hU : integralUnitTorus (K := K) M ≤ H)
    (hX : ∀ a x, allowedIwahoriRoot D a x →
      markedRootPoint M.toIntegralMarking (CommAlgCat.of Integers.{u} K) a x ∈ H) :
    markedBorelReduction M.group B ≤ H := by
  classical
  let R := CommAlgCat.of Integers.{u} K
  let S := CommAlgCat.of Integers.{u} (valuation K).valuationSubring
  let inc := valuationRingInclusion K
  obtain ⟨l, r, hl, hr⟩ := positiveAndNegativeEnumerations D
  have hc := iwahoriDepthCoordinates C B hB l r hl hr
  intro g hg
  obtain ⟨z, t, hz, rfl⟩ := (hc g).mp hg
  rw [markedCellPoint_map]
  have hor (s : List D.I) (hs : ∀ i ∈ s, allowedIwahoriRoot D i (z i : K)) :
      orderedRootPoint M.toIntegralMarking R s (fun i => inc.hom (z i)) ∈ H := by
    apply H.list_prod_mem
    intro a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
    exact hX i (z i : K) (hs i hi)
  have hT : (((integralPointFunctor (splitTorus D)).map inc)
      (torusPoint D S t) ≫ M.torus.hom.hom : IntegralPoints M.group R) ∈ H :=
    hU ⟨torusPoint D S t, rfl⟩
  exact H.mul_mem (hor l fun i hi => ⟨(z i).property, fun _ => hz i hi⟩)
    (H.mul_mem hT (hor r fun i hi => ⟨(z i).property, fun h => (h ((hr.2 i).mp hi)).elim⟩))

end ReductionGenerators

private theorem subgroup_preserved_by_root_layers {G A F : Type*} [Group G] [Field F]
    (I U : Subgroup G) (allowed : A → F → Prop) (X : A → F → G)
    (ht : U ≤ I) (hroot : ∀ a x, allowed a x → X a x ∈ I)
    (hgen : ∀ H : Subgroup G, U ≤ H → (∀ a x, allowed a x → X a x ∈ H) → I ≤ H)
    (n : G) (w : Equiv.Perm A) (m : A → Fˣ)
    (hu : ∀ t, t ∈ U ↔ n * t * n⁻¹ ∈ U)
    (ha : ∀ a x, allowed a x ↔ allowed (w a) ((m a : F) * x))
    (hw : ∀ a x, n * X a x * n⁻¹ = X (w a) ((m a : F) * x))
    (g : G) : g ∈ I ↔ n * g * n⁻¹ ∈ I := by
  let c := (MulAut.conj n).toMonoidHom
  change g ∈ I ↔ c g ∈ I
  constructor
  · exact fun hg => hgen (I.comap c) (fun t ht' => ht ((hu t).mp ht'))
      (fun a x hx => by
        change n * X a x * n⁻¹ ∈ I
        rw [hw]
        exact hroot _ _ ((ha a x).mp hx)) hg
  · intro hg
    let c' := (MulAut.conj n).symm.toMonoidHom
    have hcc (x : G) : c' (c x) = x :=
      (MulAut.conj n).symm_apply_apply x
    have hU' : U ≤ I.comap c' := by
      intro t h
      change c' t ∈ I
      apply ht ((hu (c' t)).mpr ?_)
      change c (c' t) ∈ U
      have hct : c (c' t) = t := (MulAut.conj n).apply_symm_apply t
      rwa [hct]
    have hX' (b : A) (y : F) (hy : allowed b y) :
        X b y ∈ I.comap c' := by
      let a := w.symm b
      let x := (↑(m a)⁻¹ : F) * y
      have hb : w a = b := w.apply_symm_apply b
      have hx : (m a : F) * x = y := by
        dsimp [x]
        rw [← mul_assoc, Units.mul_inv, one_mul]
      have hh : c (X a x) =
          X b y := by
        change n * _ * n⁻¹ = _
        rw [hw, hb, hx]
      rw [← hh]
      change c' (c _) ∈ I
      rw [hcc]
      exact hroot a x ((ha a x).mpr (by rwa [hb, hx]))
    have h := hgen (I.comap c') hU' hX' hg
    change c' (c g) ∈ I at h
    rwa [hcc] at h


set_option backward.isDefEq.respectTransparency false in
theorem iwahoriPreservedByLayerAction : IwahoriPreservedByLayerAction.{u} := by
  intro K _ _ D M κ R U allowed C B hB n w m hu ha hw g
  let I := markedBorelReduction M.group B
  have ht : U ≤ I := reduction_contains_unitTorus C B hB
  have hroot : ∀ a x, allowed a x → markedRootPoint M.toIntegralMarking R a x ∈ I :=
    reduction_contains_rootLayer C B hB
  have hgen (H : Subgroup (IntegralPoints M.group R)) (hU : U ≤ H)
      (hX : ∀ a x, allowed a x → markedRootPoint M.toIntegralMarking R a x ∈ H) : I ≤ H :=
    reduction_le_of_layers C B hB H hU hX
  exact subgroup_preserved_by_root_layers I U allowed (markedRootPoint M.toIntegralMarking R)
    ht hroot hgen n w m hu ha hw g

end LayerAction

section IntegralCentralCover

open CategoryTheory.Limits CategoryTheory.MorphismProperty Opposite Module
open scoped TensorProduct

open _root_.LinearAlgebraicGroups.Specs.IntegralSemisimpleModel
open _root_.LinearAlgebraicGroups.Specs.IntegralCentralQuotient
open _root_.LinearAlgebraicGroups.Specs.ExceptionalMarkedRootDescent (markedRootPoint)
open _root_.LinearAlgebraicGroups.Specs.OrderedRootProducts (Enumerates)
open private characterRestriction_injective derivedDatum derivedDatum_coroots_span semisimpleModel_exists derivedBase_height
  CentralLattice centralTorus coverGroup coverInclusion coverTorus coverTorusProductIso
  coverTorusProductIso_fst torusOf CoverCharacters coverCharactersLeft characterRestriction
  restrictToCorootLattice coverCharactersEquiv coverCharactersEquiv_root
  coverCharactersLeft_root coverProductCharacters quotientCharacters quotientCharacterMap
  torusKernel torusKernel_surjective characterRestriction_finiteQuotient KernelCharacters
  coverRootMap coverRootMap_eq coverRoot_closed coverRankOneNatural coverRankOne_compatible
  coverGroup_affine coverGroup_smooth coverGroup_integral coverTorus_closed coverCell_open orderedCell
  affineSpectrum markedTorusCoordinates markedTorusCoordinates_spec markedTorusCoordinates_surjective
  markedRootCoordinates markedRootCoordinates_spec markedRootCoordinates_surjective
  rankOneCoordinates markedCellCoordinates_spec cellDomainIso coverRootScalarAction
  groupAlgebra_map_surjective coverRoot_kernel domainCongrBialgEquiv_toBialgHom coordinatePoints_comp torusPoint_as_coordinates coverCoroot coverRoots_enumerated rootOrderings_exist
  central_of_openRootCell reductiveFibres_precompose cover_reductiveFibres
  from LinearAlgebraicGroups.Classification.IntegralRealization
open private MarkedQuotient MarkedQuotient.mk quotientMarking quotient_reductiveFibres modelOfMarking
  quotientTorusIso quotientTorusIso_hom range_eq_subalgebra quotientTorusRestriction_surjective
  quotientCell_open_of_sameImage coordinateFlat_of_flatSpectrum smoothConnectedOfGeometricFibres
  spectrumOfHopfHom_comp spectrumOfAlgHom_comp
  from LinearAlgebraicGroups.Classification.IntegralRealization
open private rightTorsor_over central_translation torusProjection_torsor
  from LinearAlgebraicGroups.Classification.IntegralCentralQuotient


private theorem centralLattice_eq_bot_of_rootSpan {E : Pinning.BasedRootDatum.{u}}
    (h : E.datum.rootSpan ℤ = ⊤) : CentralLattice E = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro y hy
  have hspan : E.datum.rootSpan ℤ ≤ (E.datum.toLinearMap.flip y).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    exact ((Submodule.mem_iInf _).mp hy) a
  have hz : E.datum.toLinearMap.flip y = 0 :=
    LinearMap.ker_eq_top.mp (top_le_iff.mp (h ▸ hspan))
  apply E.datum.toLinearMap.flip.toPerfPair.injective
  change E.datum.toLinearMap.flip y = E.datum.toLinearMap.flip 0
  rw [hz, map_zero]

private def centralTorusIsTerminal {E : Pinning.BasedRootDatum.{u}}
    (h : E.datum.rootSpan ℤ = ⊤) : IsTerminal (centralTorus E) := by
  have hzero := centralLattice_eq_bot_of_rootSpan h
  letI : Subsingleton (CentralLattice E) := hzero.symm ▸ inferInstanceAs (Subsingleton (⊥ : Submodule ℤ E.Y))
  let X := Multiplicative (Module.Dual ℤ (CentralLattice E))
  let A := MonoidAlgebra Integers.{u} X
  haveI : Subsingleton X := inferInstanceAs (Subsingleton (Module.Dual ℤ (CentralLattice E)))
  have he : Function.Bijective (algebraMap Integers.{u} A) :=
    (MonoidAlgebra.uniqueAlgEquiv (R := Integers.{u}) (A := Integers.{u}) (M := X)).symm.bijective
  let f := CommRingCat.ofHom (algebraMap Integers.{u} A)
  letI : IsIso f := (ConcreteCategory.isIso_iff_bijective f).mpr he
  letI : IsIso (centralTorus E).X.hom := inferInstanceAs (IsIso (Spec.map f))
  refine IsTerminal.ofUniqueHom (fun G => 0) fun G a => ?_
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  exact (cancel_mono (centralTorus E).X.hom).mp ((CategoryTheory.Over.w a.hom.hom).trans (CategoryTheory.Over.w _).symm)

private def coverInclusionIso {E : Pinning.BasedRootDatum.{u}}
    (h : E.datum.rootSpan ℤ = ⊤) (H : Model (derivedDatum E)) :
    H.group ≅ coverGroup H where
  hom := coverInclusion H
  inv := fst _ _
  hom_inv_id := lift_fst _ _
  inv_hom_id := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, show coverInclusion H ≫ fst _ _ = 𝟙 H.group from lift_fst _ _,
        Category.comp_id, Category.id_comp]
    · exact (centralTorusIsTerminal h).hom_ext _ _

private theorem coverCharacterRestriction {E : Pinning.BasedRootDatum.{u}}
    (h : E.datum.rootSpan ℤ = ⊤) (x : E.X) :
    coverCharactersLeft E (Multiplicative.ofAdd (restrictToCorootLattice E x)) =
      Multiplicative.ofAdd (characterRestriction E x) := by
  have hzero := centralLattice_eq_bot_of_rootSpan h
  letI : Subsingleton (CentralLattice E) := hzero.symm ▸ inferInstanceAs (Subsingleton (⊥ : Submodule ℤ E.Y))
  apply Multiplicative.toAdd.injective
  apply LinearMap.ext
  rintro ⟨y, z⟩
  have hz : z = 0 := Subsingleton.elim _ _
  subst z
  change ((Module.dualProdDualEquivDual ℤ _ _) (restrictToCorootLattice E x, 0)) (y, 0) =
    E.datum.toLinearMap x (y.val + 0)
  rw [Module.dualProdDualEquivDual_apply, LinearMap.coprod_apply, add_zero]
  simp only [LinearMap.zero_apply, add_zero]
  rfl

private theorem restrictedCharacterIndex {E : Pinning.BasedRootDatum.{u}}
    (h : E.datum.rootSpan ℤ = ⊤) :
    Function.Injective (restrictToCorootLattice E) ∧
    Finite (Multiplicative (derivedDatum E).X ⧸
      (restrictToCorootLattice E).toAddMonoidHom.toMultiplicative.range) := by
  have hzero := centralLattice_eq_bot_of_rootSpan h
  letI : Subsingleton (CentralLattice E) := hzero.symm ▸ inferInstanceAs (Subsingleton (⊥ : Submodule ℤ E.Y))
  let χ := (restrictToCorootLattice E).toAddMonoidHom.toMultiplicative
  let z := (torusKernel E).comp (coverCharactersLeft E)
  have hi : Function.Injective (coverCharactersLeft E) :=
    (coverProductCharacters E).injective.comp (fun _ _ e => congrArg Prod.fst e)
  have hs : Function.Surjective (coverCharactersLeft E) := by
    intro a
    obtain ⟨⟨x, y⟩, hxy⟩ := (coverProductCharacters E).surjective a
    have hy : y = 1 := Subsingleton.elim _ _
    subst y
    exact ⟨x, hxy⟩
  have hz : z.ker = χ.range := by
    ext x
    constructor
    · intro hx
      let y := (quotientCharacters E).symm ⟨coverCharactersLeft E x, hx⟩
      refine ⟨y, hi ?_⟩
      change coverCharactersLeft E (Multiplicative.ofAdd (restrictToCorootLattice E y.toAdd)) = _
      rw [coverCharacterRestriction h]
      exact congrArg Subtype.val ((quotientCharacters E).apply_symm_apply ⟨_, hx⟩)
    · rintro ⟨y, rfl⟩
      change torusKernel E (coverCharactersLeft E
        (Multiplicative.ofAdd (restrictToCorootLattice E y.toAdd))) = 1
      rw [coverCharacterRestriction h]
      exact ((quotientCharacters E) y).property
  have hzi := (torusKernel_surjective E).comp hs
  letI : Finite (KernelCharacters E) := characterRestriction_finiteQuotient E
  constructor
  · intro x y e
    have he := congrArg (fun w => coverCharactersLeft E (Multiplicative.ofAdd w)) e
    rw [coverCharacterRestriction h, coverCharacterRestriction h] at he
    exact (characterRestriction_injective E) (congrArg Multiplicative.toAdd he)
  · rw [← hz]
    letI : Finite (Multiplicative (KernelCharacters E)) :=
      Finite.of_equiv _ (Multiplicative.ofAdd : KernelCharacters E ≃ _)
    exact Finite.of_injective _ (QuotientGroup.quotientKerEquivOfSurjective z hzi).injective

/-- Data retained from the graded central quotient of the integral cover. -/
private structure IntegralCoverQuotient {E : Pinning.BasedRootDatum.{u}}
    (H : Model (derivedDatum E)) where
  model : Model E
  coordinate : CommHopfAlgCat.{u} Integers.{u}
  spectrum : HopfSpectrum Integers.{u} coordinate ≅ coverGroup H
  torus : coordinate →ₐc[Integers.{u}] MonoidAlgebra Integers.{u} (Multiplicative (CoverCharacters E))
  torus_eq : spectrumOfHopfHom torus = coverTorus H ≫ spectrum.inv
  target : CommHopfAlgCat.{u} Integers.{u}
  targetIso : HopfSpectrum Integers.{u} target ≅ model.group
  projection : target →ₐc[Integers.{u}] coordinate
  central : IsCentral ((MonoidAlgebra.mapDomainBialgHom Integers.{u} (torusKernel E)).comp torus)
  torsor : IsRightTorsor projection
    ((MonoidAlgebra.mapDomainBialgHom Integers.{u} (torusKernel E)).comp torus)
  torus_surj : Function.Surjective torus
  root : ∀ (R : IntegralAlgebra.{u}) (a : E.I) (x : R),
    integralPointHom (spectrum.inv ≫ spectrumOfHopfHom projection ≫ targetIso.hom) R
        (H.line.point R x ≫ (coverRootMap H a).hom.hom) =
      markedRootPoint model.toIntegralMarking R a x
  torus_comm :
    (spectrumOfHopfHom torus) ≫ spectrumOfHopfHom projection ≫ targetIso.hom =
    spectrumOfHopfHom (MonoidAlgebra.mapDomainBialgHom Integers.{u} (torusKernel E).ker.subtype) ≫
      (quotientTorusIso E).hom ≫ model.torus

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1500000 in
private theorem integralCoverQuotient_exists {E : Pinning.BasedRootDatum.{u}}
    (H : Model (derivedDatum E)) : Nonempty (IntegralCoverQuotient H) := by
  let R := Integers.{u}
  letI := E.freeY
  letI := E.finiteY
  letI : Finite (KernelCharacters E) := characterRestriction_finiteQuotient E
  letI : Finite (Multiplicative (KernelCharacters E)) :=
    Finite.of_equiv _ (Multiplicative.ofAdd : KernelCharacters E ≃ _)
  letI : Module.Free ℤ (Additive (Multiplicative (CoverCharacters E))) :=
    inferInstanceAs (Module.Free ℤ (CoverCharacters E))
  letI : Module.Finite ℤ (Additive (Multiplicative (CoverCharacters E))) :=
    inferInstanceAs (Module.Finite ℤ (CoverCharacters E))
  obtain ⟨A, ⟨e⟩⟩ := affineSpectrum (coverGroup H) (coverGroup_affine H)
  let t := markedTorusCoordinates e (coverTorus H)
  let x : E.I → A →ₐ[Integers.{u}] Polynomial Integers.{u} :=
    fun a => markedRootCoordinates e (coverRootMap H a)
  let r := fun a : E.I => rankOneCoordinates (coverRankOneNatural H e a)
  have ht := markedTorusCoordinates_surjective e (coverTorus H) (coverTorus_closed H)
  have ht_eq := markedTorusCoordinates_spec e (coverTorus H)
  let w := (Grp.forget IntegralScheme.{u} ⋙ CategoryTheory.Over.forget _).mapIso e
  have hs : Smooth (HopfSpectrum Integers.{u} A).X.hom := by
    rw [← CategoryTheory.Over.w e.hom.hom.hom]
    change Smooth (w.hom ≫ (coverGroup H).X.hom)
    letI := coverGroup_smooth H
    infer_instance
  have hcell (n p : List E.I) (hn : Enumerates n {a | ¬ E.base.IsPos a})
      (hp : Enumerates p {a | E.base.IsPos a}) :
      IsOpenImmersion (Specs.IntegralCentralQuotient.cellMap t x n p).left := by
    dsimp only [t, x]
    rw [markedCellCoordinates_spec, CategoryTheory.Over.comp_left, CategoryTheory.Over.comp_left]
    let i := (CategoryTheory.Over.forget _).mapIso
      (cellDomainIso (torusOf (Multiplicative (CoverCharacters E))) H.line n p)
    letI := coverCell_open H n p hn hp
    change IsOpenImmersion (i.hom ≫ (orderedCell H.line (coverTorus H)
      (coverRootMap H) n p).left ≫ w.inv)
    infer_instance
  obtain ⟨n, p, hn, hp⟩ := rootOrderings_exist E
  letI : IsIntegral ((Grp.forget IntegralScheme.{u} ⋙ CategoryTheory.Over.forget _).obj
      (coverGroup H)) := coverGroup_integral H
  letI : IsIntegral (Spec (CommRingCat.of A)) := IsIntegral.of_isIso w.inv
  letI : _root_.IsReduced A := (affine_isReduced_iff (CommRingCat.of A)).mp inferInstance
  letI : IrreducibleSpace (HopfSpectrum Integers.{u} A).X.left :=
    inferInstanceAs (IrreducibleSpace (Spec (CommRingCat.of A)))
  let z := torusKernel E
  let π := (MonoidAlgebra.mapDomainBialgHom Integers.{u} z).comp t
  let α := fun a : E.I => Multiplicative.ofAdd (characterRestriction E (E.datum.root a))
  have hc : IsCentral π := central_of_openRootCell z t x α (coverRoot_kernel E)
    (coverRootScalarAction H e) n p (hcell n p hn hp)
  have hred : ReductiveFibres (spectrumOfHopfHom t) := by
    rw [ht_eq]
    intro k _ _ _
    obtain ⟨G, i, hi, hG⟩ := cover_reductiveFibres H k
    let F := fibreGroup (R := Integers.{u}) k
    refine ⟨G, F.mapIso e ≪≫ i, ?_⟩
    change ∃ h, _
    have h : F.map (coverTorus H ≫ e.inv) ≫ (F.mapIso e ≪≫ i).hom =
        F.map (coverTorus H) ≫ i.hom := by simp [Functor.map_comp, Category.assoc]
    rw [h]
    exact ⟨hi, hG⟩
  have hroot (a : E.I) : Function.Surjective (x a) ∧ RootScalarAction t (x a) (α a) ∧
      RankOneCompatibility t (x a) (x (E.datum.reflectionPerm a a)) (coverCoroot E a) (r a) :=
    ⟨markedRootCoordinates_surjective e _ (coverRoot_closed H a),
      coverRootScalarAction H e a, coverRankOne_compatible H e a⟩
  have hquot (n p : List E.I) (hn : Enumerates n {a | ¬ E.base.IsPos a})
      (hp : Enumerates p {a | E.base.IsPos a}) := by
    obtain ⟨hnd, hall⟩ := coverRoots_enumerated E hn hp
    exact Classification.IntegralCentralQuotient.integralCentralQuotient.2.2 z t x n p
      (fun i => E.datum.reflectionPerm i i) α (coverCoroot E) r
      (torusKernel_surjective E) ht hc hs hred hnd hall (hcell n p hn hp) hroot
  obtain ⟨hb, j, t₀, hj, htor, hflat, hfp, hred₀, _, _, hcomm, _, _, hroot₀⟩ := hquot n p hn hp
  let B := ↥(invariants π)
  letI : Algebra Integers.{u} B := hb.toHopfAlgebraStruct.toBialgebra.toAlgebra
  letI : HopfAlgebra Integers.{u} B := hb
  letI : Flat (HopfSpectrum Integers.{u} B).X.hom := hflat
  letI : LocallyOfFinitePresentation (HopfSpectrum Integers.{u} B).X.hom := hfp
  obtain ⟨hsm, hconn⟩ := smoothConnectedOfGeometricFibres _ hred₀
  let x₀ (a : E.I) := (x a).comp j.toAlgHom
  have hsurj : Function.Surjective t₀ :=
    quotientTorusRestriction_surjective z t ht j t₀ (fun a ha => ⟨⟨a, ha⟩, hj _⟩) hcomm
  have hmarks (a : E.I) :
      Function.Surjective (x₀ a) ∧
      RootScalarAction t₀ (x₀ a) (quotientCharacters E (Multiplicative.ofAdd (E.datum.root a))) ∧
      ∃ q : RankOneMap Integers.{u} B, RankOneCompatibility t₀ (x₀ a)
        (x₀ (E.datum.reflectionPerm a a)) ((coverCoroot E a).comp z.ker.subtype) q := by
    obtain ⟨hx, hα, hscalar, q, _, hq⟩ := hroot₀ a
    exact ⟨hx, (Subtype.ext (show α a = _ from rfl) :
      (⟨α a, hα⟩ : z.ker) = quotientCharacters E (Multiplicative.ofAdd (E.datum.root a))) ▸ hscalar, q, hq⟩
  choose r₀ hr₀ using fun a => (hmarks a).2.2
  have allCells (n' p' : List E.I) (hn' : Enumerates n' {a | ¬ E.base.IsPos a})
      (hp' : Enumerates p' {a | E.base.IsPos a}) :
      IsOpenImmersion (Specs.IntegralCentralQuotient.cellMap t₀ x₀ n' p').left := by
    obtain ⟨hb', j', t₀', hj', _, hflat', _, _, _, _, hcomm', hopen, _, _⟩ :=
      hquot n' p' hn' hp'
    have hinj {f : B → A} (hf : ∀ a, f a = (a : A)) : Function.Injective f :=
      fun a b he => Subtype.ext ((hf a).symm.trans (he.trans (hf b)))
    have hsame : Set.range j = Set.range j' :=
      (range_eq_subalgebra (invariants π) j hj).trans (range_eq_subalgebra (invariants π) j' hj').symm
    letI : Smooth (HopfSpectrum Integers.{u} A).X.hom := hs
    exact @quotientCell_open_of_sameImage A B B _ _ E.I _ _ _ _ _
      _ hb hb' (@coordinateFlat_of_flatSpectrum Integers.{u} B _ _ hb' hflat')
      (coordinateFlat_of_flatSpectrum (inferInstance : Flat (HopfSpectrum Integers.{u} A).X.hom))
      z t x j j' t₀ t₀' (hinj hj) (hinj hj') hsame hcomm hcomm' n' p' hopen
  have root_eq (a : E.I) : (coverRootMap H a ≫ e.inv ≫ spectrumOfHopfHom j).hom.hom =
      spectrumOfAlgHom (x₀ a) := by
    rw [Grp.comp_hom_hom, Grp.comp_hom_hom, ← Category.assoc]
    exact (congrArg (· ≫ (spectrumOfHopfHom j).hom.hom)
      (markedRootCoordinates_spec e (coverRootMap H a)).symm).trans
        (spectrumOfAlgHom_comp j.toAlgHom (x a)).symm
  let Q : MarkedQuotient E :=
    MarkedQuotient.mk (CommHopfAlgCat.of Integers.{u} B) t₀ x₀ hsurj hsm hconn hred₀
      n p hn hp allCells r₀ (fun a => (hmarks a).1) (fun a => (hmarks a).2.1) hr₀
      H.line (fun a => coverRootMap H a ≫ e.inv ≫ spectrumOfHopfHom j) root_eq
  let model := modelOfMarking (quotientMarking Q) (quotient_reductiveFibres Q) n p hn hp
  refine ⟨⟨model, A, e, t, ht_eq, CommHopfAlgCat.of Integers.{u} B, Iso.refl _, j, hc, htor, ht, ?_, ?_⟩⟩
  · intro S a v
    change (H.line.point S v ≫ (coverRootMap H a).hom.hom) ≫
        (e.inv ≫ spectrumOfHopfHom j ≫ 𝟙 _).hom.hom =
      H.line.point S v ≫ (coverRootMap H a ≫ e.inv ≫ spectrumOfHopfHom j).hom.hom
    simp only [Category.comp_id, Grp.comp_hom_hom, Category.assoc]
  · change spectrumOfHopfHom t ≫ spectrumOfHopfHom j ≫ 𝟙 _ =
      spectrumOfHopfHom (MonoidAlgebra.mapDomainBialgHom Integers.{u} z.ker.subtype) ≫
        (quotientTorusIso E).hom ≫ ((quotientTorusIso E).inv ≫ spectrumOfHopfHom t₀)
    rw [Category.comp_id, Iso.hom_inv_id_assoc, ← spectrumOfHopfHom_comp, ← spectrumOfHopfHom_comp, hcomm]

private theorem kernelOfIntegralRightTorsor {G Q Z : IntegralGroup.{u}} (q : G ⟶ Q) (i : Z ⟶ G)
    (h : IsPullback (fst G.X Z.X) (fst _ _ * (snd _ _ ≫ i.hom.hom))
      q.hom.hom q.hom.hom) :
    IsPullback i.hom.hom (toUnit Z.X) q.hom.hom η[Q.X] := by
  let b : Z.X ⟶ G.X ⊗ Z.X := lift (1 : Z.X ⟶ G.X) (𝟙 Z.X)
  have hfst : b ≫ fst G.X Z.X = 1 := lift_fst _ _
  have hsnd : b ≫ snd G.X Z.X = 𝟙 _ := lift_snd _ _
  have hb : b ≫ (fst G.X Z.X * (snd _ _ ≫ i.hom.hom)) = i.hom.hom := by
    rw [MonObj.comp_mul, hfst, ← Category.assoc, hsnd, Category.id_comp, one_mul]
  have he (U : IntegralScheme.{u}) :
      (1 : U ⟶ G.X) ≫ q.hom.hom = toUnit U ≫ η[Q.X] := MonObj.one_comp _
  have w : i.hom.hom ≫ q.hom.hom = toUnit Z.X ≫ η[Q.X] := by
    calc
      _ = b ≫ (fst G.X Z.X * (snd _ _ ≫ i.hom.hom)) ≫ q.hom.hom := by rw [← Category.assoc, hb]
      _ = b ≫ fst G.X Z.X ≫ q.hom.hom := congrArg (b ≫ ·) h.w.symm
      _ = _ := by rw [← Category.assoc, hfst, he]
  let liftPoint (s : PullbackCone q.hom.hom η[Q.X]) : s.pt ⟶ G.X ⊗ Z.X :=
    h.lift 1 s.fst (by
      rw [he, s.condition, toUnit_unique s.snd _])
  have hl (s : PullbackCone q.hom.hom η[Q.X]) :
      (liftPoint s ≫ snd G.X Z.X) ≫ i.hom.hom = s.fst := by
    have hs := h.lift_snd (1 : s.pt ⟶ G.X) s.fst (by
      rw [he, s.condition, toUnit_unique s.snd _])
    change liftPoint s ≫ (fst G.X Z.X * (snd _ _ ≫ i.hom.hom)) = _ at hs
    rw [MonObj.comp_mul, show liftPoint s ≫ fst G.X Z.X = 1 from h.lift_fst _ _ _,
      one_mul, ← Category.assoc] at hs
    exact hs
  apply IsPullback.of_isLimit' ⟨w⟩
  refine PullbackCone.IsLimit.mk _ (fun s => liftPoint s ≫ snd _ _) hl
    (fun _ => Subsingleton.elim _ _) ?_
  intro s a ha _
  have hba : a ≫ b = liftPoint s := by
    apply h.hom_ext
    · rw [Category.assoc, hfst, MonObj.comp_one, show liftPoint s ≫ fst G.X Z.X = 1 from h.lift_fst _ _ _]
    · rw [Category.assoc, hb, show liftPoint s ≫
        (fst G.X Z.X * (snd _ _ ≫ i.hom.hom)) = s.fst from h.lift_snd _ _ _]
      exact ha
  rw [← hba, Category.assoc, hsnd, Category.comp_id]

attribute [local instance] integerAlgebra in
private theorem integralFibreMorphismProperty (k : Type u) [Field k] (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] {G H : IntegralGroup.{u}} (g : G ⟶ H)
    (hg : P g.hom.hom.left) : P ((fibre k).map g).hom.hom.left := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap Integers.{u} k))
  have hp : IsPullback ((CategoryTheory.Over.pullback f).map g.hom.hom).left
      (pullback.fst G.X.hom f) (pullback.fst H.X.hom f) g.hom.hom.left := by
    apply IsPullback.of_right (h₁₂ := pullback.snd H.X.hom f) (h₂₂ := H.X.hom) (v₁₃ := f)
    · simp only [CategoryTheory.Over.pullback_map_left, pullback.lift_snd, CategoryTheory.Over.w g.hom.hom]
      exact (IsPullback.of_hasPullback G.X.hom f).flip
    · simp only [CategoryTheory.Over.pullback_map_left, pullback.lift_fst]
    · exact (IsPullback.of_hasPullback H.X.hom f).flip
  exact MorphismProperty.of_isPullback hp.flip hg

attribute [local instance] integerAlgebra in
private theorem integralFibreKernel (k : Type u) [Field k] {G H Z : IntegralGroup.{u}}
    (q : G ⟶ H) (i : Z ⟶ G)
    (h : IsPullback i.hom.hom (toUnit Z.X) q.hom.hom η[H.X]) :
    IsPullback ((fibre k).map i).hom.hom (toUnit ((fibre k).obj Z).X)
      ((fibre k).map q).hom.hom η[((fibre k).obj H).X] := by
  let F := CategoryTheory.Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap Integers.{u} k)))
  let e := Functor.Monoidal.εIso F
  apply (h.map F).of_iso' (Iso.refl _) (Iso.refl _) e (Iso.refl _)
  · simp [F]
  · apply (cancel_mono e.inv).mp
    simp only [Iso.refl_hom, Category.id_comp]
    exact toUnit_unique _ _
  · simp [F]
  · change e.hom ≫ F.map η[H.X] = (e.hom ≫ F.map η[H.X]) ≫ 𝟙 _
    simp

attribute [local instance] integerAlgebra in
private theorem integralFibreCentrality (k : Type u) [Field k] {G Z : IntegralGroup.{u}} (i : Z ⟶ G)
    (h : fst G.X Z.X * (snd _ _ ≫ i.hom.hom) =
      (snd _ _ ≫ i.hom.hom) * fst G.X Z.X) :
    Centralizes (𝟙 ((fibre k).obj G)) ((fibre k).map i).hom.hom := by
  let F := CategoryTheory.Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap Integers.{u} k)))
  let e := prodComparisonIso F G.X Z.X
  letI : GrpObj (F.obj G.X) := ((fibre k).obj G).grp
  have hf : e.inv ≫ F.map (fst G.X Z.X) = fst (F.obj G.X) (F.obj Z.X) := by
    rw [← CartesianMonoidalCategory.prodComparison_fst, ← prodComparisonIso_hom, Iso.inv_hom_id_assoc]
  have hs : e.inv ≫ F.map (snd G.X Z.X) = snd (F.obj G.X) (F.obj Z.X) := by
    rw [← CartesianMonoidalCategory.prodComparison_snd, ← prodComparisonIso_hom, Iso.inv_hom_id_assoc]
  have hw := congrArg (fun f => e.inv ≫ F.map f) h
  simp only [F.map_mul, Functor.map_comp, MonObj.comp_mul, ← Category.assoc, hf, hs] at hw
  change conjugateFamily (𝟙 ((fibre k).obj G)) ((fibre k).map i).hom.hom =
    fst (F.obj G.X) (F.obj Z.X) ≫ 𝟙 _
  unfold conjugateFamily
  change (snd (F.obj G.X) (F.obj Z.X) ≫ F.map i.hom.hom) *
      (fst (F.obj G.X) (F.obj Z.X) ≫ 𝟙 _) *
      (snd (F.obj G.X) (F.obj Z.X) ≫ F.map i.hom.hom)⁻¹ = _
  simp only [Category.comp_id]
  let a := fst (F.obj G.X) (F.obj Z.X)
  let b := snd (F.obj G.X) (F.obj Z.X) ≫ F.map i.hom.hom
  change a * b = b * a at hw
  change b * a * b⁻¹ = a
  exact (congrArg (· * b⁻¹) hw.symm).trans (mul_inv_cancel_right a b)

private def coverTorusProjectionIso {E : Pinning.BasedRootDatum.{u}}
    (h : E.datum.rootSpan ℤ = ⊤) :
    torusOf (Multiplicative (CoverCharacters E)) ≅ splitTorus (derivedDatum E) :=
  coverTorusProductIso E ≪≫
    { hom := fst _ _
      inv := lift (𝟙 _) 0
      hom_inv_id := by
        apply CartesianMonoidalCategory.hom_ext
        · rw [Category.assoc, lift_fst, Category.comp_id, Category.id_comp]
        · exact (centralTorusIsTerminal h).hom_ext _ _
      inv_hom_id := lift_fst _ _ }

private def adjointTorusProjection (E : Pinning.BasedRootDatum.{u}) :
    splitTorus (derivedDatum E) ⟶ splitTorus E :=
  spectrumOfHopfHom (MonoidAlgebra.mapDomainBialgHom Integers.{u}
    (restrictToCorootLattice E).toAddMonoidHom.toMultiplicative)

set_option backward.isDefEq.respectTransparency false in
private theorem adjointTorusProjection_square {E : Pinning.BasedRootDatum.{u}}
    (h : E.datum.rootSpan ℤ = ⊤) :
    (coverTorusProjectionIso h).hom ≫ adjointTorusProjection E =
      spectrumOfHopfHom (MonoidAlgebra.mapDomainBialgHom Integers.{u} (torusKernel E).ker.subtype) ≫
        (quotientTorusIso E).hom := by
  have hleft : (coverTorusProjectionIso h).hom =
      spectrumOfHopfHom (MonoidAlgebra.mapDomainBialgHom Integers.{u} (coverCharactersLeft E)) := by
    apply Grp.hom_ext
    apply CategoryTheory.Over.OverMorphism.ext
    exact coverTorusProductIso_fst E
  have hright : (quotientTorusIso E).hom = spectrumOfHopfHom (quotientCharacterMap E) := by
    apply Grp.hom_ext
    apply CategoryTheory.Over.OverMorphism.ext
    exact quotientTorusIso_hom E
  rw [hleft, hright, adjointTorusProjection, ← spectrumOfHopfHom_comp, ← spectrumOfHopfHom_comp]
  congr 1
  have hq := domainCongrBialgEquiv_toBialgHom (quotientCharacters E)
  change (MonoidAlgebra.mapDomainBialgHom Integers.{u} (coverCharactersLeft E)).comp
        (MonoidAlgebra.mapDomainBialgHom Integers.{u}
          (restrictToCorootLattice E).toAddMonoidHom.toMultiplicative) =
      (MonoidAlgebra.mapDomainBialgHom Integers.{u} (torusKernel E).ker.subtype).comp
        (quotientCharacterMap E)
  rw [show quotientCharacterMap E = _ from hq, ← MonoidAlgebra.mapDomainBialgHom_comp,
    ← MonoidAlgebra.mapDomainBialgHom_comp]
  apply congrArg (MonoidAlgebra.mapDomainBialgHom Integers.{u})
  apply MonoidHom.ext
  intro x
  exact coverCharacterRestriction h x.toAdd

private theorem coverTorus_inclusion_square {E : Pinning.BasedRootDatum.{u}}
    (h : E.datum.rootSpan ℤ = ⊤) (H : Model (derivedDatum E)) :
    coverTorus H ≫ (coverInclusionIso h H).inv =
      (coverTorusProjectionIso h).hom ≫ H.torus := by
  change ((coverTorusProductIso E).hom ≫ (H.torus ⊗ₘ 𝟙 _)) ≫ fst _ _ =
    ((coverTorusProductIso E).hom ≫ fst _ _) ≫ H.torus
  rw [Category.assoc, tensorHom_fst, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem adjointTorusProjection_points (E : Pinning.BasedRootDatum.{u})
    (S : IntegralAlgebra.{u}) (w : TorusValues (derivedDatum E) S) :
    torusPoint (derivedDatum E) S w ≫ (adjointTorusProjection E).hom.hom =
      torusPoint E S (w.comp (restrictToCorootLattice E).toAddMonoidHom.toMultiplicative) := by
  let χ := (restrictToCorootLattice E).toAddMonoidHom.toMultiplicative
  let e := MonoidAlgebra.mapDomainBialgHom Integers.{u} χ
  let l := MonoidAlgebra.lift Integers.{u} S (Multiplicative (derivedDatum E).X)
    ((Units.coeHom S).comp w)
  let r := MonoidAlgebra.lift Integers.{u} S (Multiplicative E.X) ((Units.coeHom S).comp (w.comp χ))
  change spectrumOfAlgHom l ≫ spectrumOfAlgHom e.toAlgHom = spectrumOfAlgHom r
  rw [← spectrumOfAlgHom_comp]
  apply congrArg spectrumOfAlgHom
  apply MonoidAlgebra.algHom_ext
  · intro m
    have hm : e (MonoidAlgebra.single m 1) = MonoidAlgebra.single (χ m) 1 :=
      MonoidAlgebra.mapDomainBialgHom_single (R := Integers.{u}) χ m 1
    change l (e (MonoidAlgebra.single m 1)) = r (MonoidAlgebra.single m 1)
    rw [hm]
    change l (MonoidAlgebra.of Integers.{u} _ (χ m)) =
      r (MonoidAlgebra.of Integers.{u} _ m)
    have hl : l (MonoidAlgebra.of Integers.{u} _ (χ m)) = (w (χ m) : S) :=
      MonoidAlgebra.lift_of ((Units.coeHom S).comp w) (χ m)
    have hr : r (MonoidAlgebra.of Integers.{u} _ m) = (w (χ m) : S) :=
      MonoidAlgebra.lift_of ((Units.coeHom S).comp (w.comp χ)) m
    exact hl.trans hr.symm
  · exact Subsingleton.elim _ _

open private centralizes_iff from LinearAlgebraicGroups.Affine.Stabilizers

private theorem fibrePropertyOfIsomorphicMap {k : Type u} [Field k] (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] [P.RespectsIso]
    {G H : IntegralGroup.{u}} (f : G ⟶ H) (h : P f.hom.hom.left)
    {X Y : GroupScheme k} (x : (fibre k).obj G ≅ X) (y : (fibre k).obj H ≅ Y) :
    P (x.inv ≫ (fibre k).map f ≫ y.hom).hom.hom.left := by
  let F := Grp.forget (SchemeOver k) ⋙ CategoryTheory.Over.forget (Spec (CommRingCat.of k))
  letI : IsIso x.inv.hom.hom.left := (F.mapIso x).isIso_inv
  letI : IsIso y.hom.hom.hom.left := (F.mapIso y).isIso_hom
  change P (x.inv.hom.hom.left ≫ ((fibre k).map f).hom.hom.left ≫ y.hom.hom.hom.left)
  rw [P.cancel_left_of_respectsIso, P.cancel_right_of_respectsIso]
  exact integralFibreMorphismProperty k P f h

set_option backward.isDefEq.respectTransparency false in
private theorem fibreKernelOfIsomorphicMap {k : Type u} [Field k] {G H Z : IntegralGroup.{u}}
    (f : G ⟶ H) (i : Z ⟶ G)
    (h : IsPullback i.hom.hom (toUnit Z.X) f.hom.hom η[H.X])
    {X Y : GroupScheme k} (x : (fibre k).obj G ≅ X) (y : (fibre k).obj H ≅ Y) :
    IsPullback (((fibre k).map i) ≫ x.hom).hom.hom (toUnit ((fibre k).obj Z).X)
      (x.inv ≫ (fibre k).map f ≫ y.hom).hom.hom η[Y.X] := by
  let F := Grp.forget (SchemeOver k)
  refine (integralFibreKernel k f i h).of_iso (Iso.refl _) (F.mapIso x) (Iso.refl _)
    (F.mapIso y) ?_ ?_ ?_ ?_
  · simp only [Grp.comp_hom_hom, Functor.mapIso_hom, Category.id_comp]
    rfl
  · simp
  · change ((fibre k).map f).hom.hom ≫ y.hom.hom.hom =
        x.hom.hom.hom ≫ (x.inv ≫ (fibre k).map f ≫ y.hom).hom.hom
    simp only [Grp.comp_hom_hom, ← Category.assoc, ← Grp.comp_hom_hom, x.hom_inv_id,
      Grp.id_hom_hom, Category.id_comp]
  · simp only [Category.id_comp]
    exact IsMonHom.one_hom y.hom.hom.hom

private theorem centralizes_transport {k : Type u} [Field k] {G Z X : GroupScheme k}
    (i : Z ⟶ G) (e : G ≅ X) (h : Centralizes (𝟙 G) i.hom.hom) :
    Centralizes (𝟙 X) (i ≫ e.hom).hom.hom := by
  apply (centralizes_iff (𝟙 X) (i ≫ e.hom).hom.hom).mpr
  intro U t x
  let p := pointHom e.hom U
  have hc := (centralizes_iff (𝟙 G) i.hom.hom).mp h U t (x ≫ e.inv.hom.hom)
  simp only [Grp.id_hom_hom, Category.comp_id] at hc ⊢
  have hi : p (t ≫ i.hom.hom) = t ≫ (i ≫ e.hom).hom.hom := by
    change (t ≫ i.hom.hom) ≫ e.hom.hom.hom = _
    rw [Category.assoc, Grp.comp_hom_hom]
  have hx : p (x ≫ e.inv.hom.hom) = x := by
    change (x ≫ e.inv.hom.hom) ≫ e.hom.hom.hom = x
    rw [Category.assoc, ← Grp.comp_hom_hom, e.inv_hom_id, Grp.id_hom_hom, Category.comp_id]
  exact hi ▸ hx ▸ hc.map p

private def centralCoverMap {E : Pinning.BasedRootDatum.{u}} (h : E.datum.rootSpan ℤ = ⊤)
    {M : Model (derivedDatum E)} (Q : IntegralCoverQuotient M) :
    M.group ⟶ Q.model.group :=
  (coverInclusionIso h M).hom ≫ Q.spectrum.inv ≫ spectrumOfHopfHom Q.projection ≫ Q.targetIso.hom

set_option backward.isDefEq.respectTransparency false in
private theorem centralCoverTorusComm {E : Pinning.BasedRootDatum.{u}} (h : E.datum.rootSpan ℤ = ⊤)
    {M : Model (derivedDatum E)} (Q : IntegralCoverQuotient M) :
    M.torus ≫ centralCoverMap h Q = adjointTorusProjection E ≫ Q.model.torus := by
  have hcover := coverTorus_inclusion_square h M
  apply (cancel_epi (coverTorusProjectionIso h).hom).mp
  calc
    _ = coverTorus M ≫ Q.spectrum.inv ≫ spectrumOfHopfHom Q.projection ≫ Q.targetIso.hom := by
      simp only [centralCoverMap, Category.assoc]
      rw [← Category.assoc (coverTorusProjectionIso h).hom M.torus, ← hcover,
        Category.assoc, Iso.inv_hom_id_assoc]
    _ = spectrumOfHopfHom Q.torus ≫ spectrumOfHopfHom Q.projection ≫ Q.targetIso.hom := by
      rw [← Category.assoc (coverTorus M) Q.spectrum.inv, ← Q.torus_eq]
    _ = _ := Q.torus_comm.trans (((reassoc_of% adjointTorusProjection_square h) Q.model.torus).symm)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2200000 in
private theorem markedCoverFibre {E : Pinning.BasedRootDatum.{u}} (h : E.datum.rootSpan ℤ = ⊤)
    {M : Model (derivedDatum E)} (Q : IntegralCoverQuotient M) (k : Type u) [Field k]
    (C : ExceptionalMarkedRootDescent.MarkedFibre M k)
    (C' : ExceptionalMarkedRootDescent.MarkedFibre Q.model k) :
    let e := Q.spectrum ≪≫ (coverInclusionIso h M).symm
    let f := e.inv ≫ spectrumOfHopfHom Q.projection ≫ Q.targetIso.hom
    let f₀ := C.groupIso.inv ≫ (fibre k).map f ≫ C'.groupIso.hom
    let t₀ := C.torusIso.inv ≫ (fibre k).map (adjointTorusProjection E) ≫ C'.torusIso.hom
    CentralIsogenies.IsCentralIsogeny f₀ ∧ CentralIsogenies.IsTorusRestriction f₀ t₀ ∧
      ∃ Z : ClosedSubgroup C.realization.pinned.pair.G.val,
        IsSchemeKernel f₀ Z ∧ SchemeDerivedGroup.IsSubgroupOf Z C.realization.pinned.pair.T ∧
          Centralizes (𝟙 C.realization.pinned.pair.G.val) Z.inclusion.hom.hom := by
  intro e f f₀ t₀
  let F := fibre k
  letI : Algebra Integers.{u} k := integerAlgebra k
  let z := torusKernel E
  letI := E.freeY
  letI := E.finiteY
  letI : Finite (KernelCharacters E) := characterRestriction_finiteQuotient E
  letI : Finite (Multiplicative (KernelCharacters E)) :=
    Finite.of_equiv _ (Multiplicative.ofAdd : KernelCharacters E ≃ _)
  letI : Fintype (Multiplicative (KernelCharacters E)) := Fintype.ofFinite _
  letI : Module.Finite ℤ (Additive (Multiplicative (CoverCharacters E))) :=
    inferInstanceAs (Module.Finite ℤ (CoverCharacters E))
  let πT := MonoidAlgebra.mapDomainBialgHom Integers.{u} z
  let π := πT.comp Q.torus
  let q := spectrumOfHopfHom Q.projection
  let j := spectrumOfHopfHom π
  let Z₀ := HopfSpectrum Integers.{u} (MonoidAlgebra Integers.{u} (Multiplicative (KernelCharacters E)))
  let eG := F.mapIso e ≪≫ C.groupIso
  let eG' := F.mapIso Q.targetIso ≪≫ C'.groupIso
  let eT := F.mapIso (coverTorusProjectionIso h) ≪≫ C.torusIso
  let eT' := F.mapIso (quotientTorusIso E) ≪≫ C'.torusIso
  let qT := spectrumOfHopfHom (MonoidAlgebra.mapDomainBialgHom Integers.{u} z.ker.subtype)
  have hf₀ : f₀ = eG.inv ≫ F.map q ≫ eG'.hom := by
    simp only [f₀, f, eG, eG', Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom,
      Functor.mapIso_inv, Functor.map_comp, Category.assoc]
    rfl
  have ht₀ : t₀ = eT.inv ≫ F.map qT ≫ eT'.hom := by
    have hT : adjointTorusProjection E =
        (coverTorusProjectionIso h).inv ≫ qT ≫ (quotientTorusIso E).hom := by
      rw [← adjointTorusProjection_square h, Iso.inv_hom_id_assoc]
    simp only [t₀, eT, eT', hT, Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom,
      Functor.mapIso_inv, Functor.map_comp, Category.assoc]
    rfl
  have hπ : Function.Surjective π :=
    (groupAlgebra_map_surjective (R := Integers.{u}) z (torusKernel_surjective E)).comp Q.torus_surj
  have hjc : IsClosedImmersion j.hom.hom.left :=
    IsClosedImmersion.spec_of_surjective _ hπ
  have hkernel := kernelOfIntegralRightTorsor q j (rightTorsor_over π Q.projection Q.torsor)
  have hcommIntegral : M.torus ≫ f = adjointTorusProjection E ≫ Q.model.torus :=
    centralCoverTorusComm h Q
  have hcomm : t₀ ≫ C'.realization.pinned.pair.T.inclusion =
      C.realization.pinned.pair.T.inclusion ≫ f₀ := by
    apply (cancel_epi C.torusIso.hom).mp
    simp only [t₀, f₀, Iso.hom_inv_id_assoc, Category.assoc]
    rw [← C'.torus_comm, ← reassoc_of% C.torus_comm, Iso.hom_inv_id_assoc]
    change F.map (adjointTorusProjection E) ≫ F.map Q.model.torus ≫ C'.groupIso.hom =
      F.map M.torus ≫ F.map f ≫ C'.groupIso.hom
    rw [← F.map_comp_assoc, ← F.map_comp_assoc, hcommIntegral]
  let Z : ClosedSubgroup C.realization.pinned.pair.G.val :=
    ⟨F.obj Z₀, F.map j ≫ eG.hom, by
      letI := integralFibreMorphismProperty k (@IsClosedImmersion) j hjc
      letI : IsIso eG.hom.hom.hom.left :=
        ((Grp.forget (SchemeOver k) ⋙ CategoryTheory.Over.forget _).mapIso eG).isIso_hom
      exact inferInstanceAs (IsClosedImmersion ((F.map j).hom.hom.left ≫ eG.hom.hom.hom.left))⟩
  have hZ : IsSchemeKernel f₀ Z := by
    rw [hf₀]
    exact fibreKernelOfIsomorphicMap q j hkernel eG eG'
  have hcentral : Centralizes (𝟙 C.realization.pinned.pair.G.val) Z.inclusion.hom.hom :=
    centralizes_transport (F.map j) eG (integralFibreCentrality k j
      (central_translation π Q.central (fst _ _) (snd _ _)))
  have hZtor : SchemeDerivedGroup.IsSubgroupOf Z C.realization.pinned.pair.T := by
    let a := spectrumOfHopfHom πT
    have hfac : j ≫ e.hom =
        a ≫ (coverTorusProjectionIso h).hom ≫ M.torus := by
      have hj : j = a ≫ spectrumOfHopfHom Q.torus :=
        spectrumOfHopfHom_comp Q.torus πT
      have hT : spectrumOfHopfHom Q.torus ≫ e.hom =
          (coverTorusProjectionIso h).hom ≫ M.torus := by
        rw [Q.torus_eq]
        simp only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
        exact coverTorus_inclusion_square h M
      rw [hj, Category.assoc, hT]
    refine ⟨F.map (a ≫ (coverTorusProjectionIso h).hom) ≫ C.torusIso.hom, ?_⟩
    change _ = F.map j ≫ eG.hom
    rw [Category.assoc, ← C.torus_comm, ← F.map_comp_assoc, Category.assoc a,
      ← hfac, F.map_comp, Category.assoc]
    rfl
  letI : IsNoetherianRing Integers.{u} := isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  have hqT := torusProjection_torsor (R := Integers.{u}) z (torusKernel_surjective E)
  refine ⟨⟨?_, ?_, ?_, Z, hZ, hcentral⟩, ⟨hcomm, ?_, ?_⟩, Z, hZ, hZtor, hcentral⟩
  · rw [hf₀]
    exact fibrePropertyOfIsomorphicMap (@IsFinite) q Q.torsor.1 eG eG'
  · rw [hf₀]
    exact fibrePropertyOfIsomorphicMap (@Flat) q Q.torsor.2.1 eG eG'
  · rw [hf₀]
    exact fibrePropertyOfIsomorphicMap (@Surjective) q Q.torsor.2.2.1 eG eG'
  · rw [ht₀]
    exact fibrePropertyOfIsomorphicMap (@Flat) qT hqT.2.1 eT eT'
  · rw [ht₀]
    exact fibrePropertyOfIsomorphicMap (@Surjective) qT hqT.2.2.1 eT eT'


set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 900000 in
theorem markedCentralCoverExists : MarkedCentralCoverExists.{u} := by
  intro E hE
  obtain ⟨M⟩ := semisimpleModel_exists Classification.IntegralSemisimpleModel.integralSemisimpleModel E
  obtain ⟨Q⟩ := integralCoverQuotient_exists M
  let D := derivedDatum E
  let e : D.I ≃ E.I := Equiv.refl _
  let χ : E.X →ₗ[ℤ] D.X := restrictToCorootLattice E
  let ψ : D.Y →ₗ[ℤ] E.Y := (E.datum.corootSpan ℤ).subtype
  let f := centralCoverMap hE Q
  let t := adjointTorusProjection E
  have hc := centralCoverTorusComm hE Q
  have hidx := restrictedCharacterIndex hE
  refine ⟨D, M, Q.model, derivedDatum_coroots_span E, ⟨{
    map := f
    torusMap := t
    rootEquiv := e
    pullCharacter := χ
    pushCocharacter := ψ
    characterInjective := hidx.1
    characterIndex := hidx.2
    roots := fun _ => rfl
    coroots := fun _ => rfl
    reflections := fun _ _ => rfl
    pairing := fun _ _ => rfl
    marking := ?_
    torusComm := hc
    fibre := markedCoverFibre hE Q }⟩⟩
  refine ⟨fun a => ?_, fun R a x => ?_, fun R s => ?_⟩
  · change 0 < (derivedDatum E).base.height a ↔ 0 < E.base.height a
    rw [derivedBase_height]
  · have ht := Q.root R a x
    change (M.line.point R x ≫ (M.root a).hom.hom) ≫ f.hom.hom =
      markedRootPoint Q.model.toIntegralMarking R a x
    change (M.line.point R x ≫ (coverRootMap M a).hom.hom) ≫
        (Q.spectrum.inv ≫ spectrumOfHopfHom Q.projection ≫ Q.targetIso.hom).hom.hom = _ at ht
    rw [coverRootMap_eq] at ht
    have hi : (coverInclusionIso hE M).hom = coverInclusion M := rfl
    simpa only [centralCoverMap, f, hi, Grp.comp_hom_hom, Category.assoc] using ht
  · change (torusPoint D R s ≫ M.torus.hom.hom) ≫ f.hom.hom =
      torusPoint E R (s.comp χ.toAddMonoidHom.toMultiplicative) ≫ Q.model.torus.hom.hom
    rw [Category.assoc, ← Grp.comp_hom_hom, hc, Grp.comp_hom_hom, ← Category.assoc]
    exact congrArg (· ≫ Q.model.torus.hom.hom) (adjointTorusProjection_points E R s)

end IntegralCentralCover

section SplitCentralMap

open _root_.LinearAlgebraicGroups.Specs.IntegralSemisimpleModel
open _root_.LinearAlgebraicGroups.Specs.ExceptionalMarkedRootDescent (MarkedFibre markedFibrePoint)
open _root_.LinearAlgebraicGroups.Specs.SchemeDerivedGroup (FactorsThrough)
open private markedTorusEquiv markedTorusIncl from LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
open private affineTorusPointEquiv from LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
open private forgetFibrePoint_comp from LinearAlgebraicGroups.Classification.IntegralRealization

attribute [local instance] integerAlgebra

set_option backward.isDefEq.respectTransparency false in
theorem splitCentralPointComparison {k : Type u} [Field k] {D E : Pinning.BasedRootDatum.{u}}
    {M : Model D} {A : Model E} (c : MarkedCentralCover M A)
    (C : MarkedFibre M k) (C' : MarkedFibre A k) :
    let P := C.realization.pinned.pair
    let P' := C'.realization.pinned.pair
    let f := C.groupIso.inv ≫ (fibre k).map c.map ≫ C'.groupIso.hom
    let p := pointHom f (𝟙_ (SchemeOver k))
    (∀ g, markedGroundPoint C' (p g) =
      integralPointHom c.map (CommAlgCat.of Integers.{u} k) (markedGroundPoint C g)) ∧
    (∀ g, FactorsThrough P'.T (p g) ↔ FactorsThrough P.T g) ∧
    (∀ g, Normalizes P'.T.inclusion (p g) ↔ Normalizes P.T.inclusion g) ∧ p.range.Normal := by
  intro P P' f p
  let S := CommAlgCat.of k k
  let Y := (testSpec k).obj (Opposite.op S)
  let fT := C.torusIso.inv ≫ (fibre k).map c.torusMap ≫ C'.torusIso.hom
  obtain ⟨hf, ht, Z, hZ, hZT, _⟩ := c.fibre k C C'
  obtain ⟨hpreT, hpreN⟩ := centralTorusAndNormalizerPreimages P.G P'.G P.T P'.T f fT ht Z hZ hZT
  refine ⟨?_, ?_, hpreN, centralIsogenyRationalImageNormal P.G P'.G f hf⟩
  · intro g
    change forgetFibrePoint A.group S ((toUnit Y ≫ (g ≫ f.hom.hom)) ≫ C'.groupIso.inv.hom.hom) =
      forgetFibrePoint M.group S ((toUnit Y ≫ g) ≫ C.groupIso.inv.hom.hom) ≫ c.map.hom.hom
    rw [← forgetFibrePoint_comp]
    congr 1
    simp only [f, Grp.comp_hom_hom, Category.assoc]
    have he : C'.groupIso.hom.hom.hom ≫ C'.groupIso.inv.hom.hom = 𝟙 _ :=
      congrArg (fun u => u.hom.hom) C'.groupIso.hom_inv_id
    simp only [he, Category.comp_id]
  · intro g
    letI : IsAffine (𝟙_ (SchemeOver k)).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of k)))
    exact hpreT _ g

set_option backward.isDefEq.respectTransparency false in
theorem splitTorusPointPreimage {k : Type u} [Field k] {D E : Pinning.BasedRootDatum.{u}}
    {M : Model D} {A : Model E} (c : MarkedCentralCover M A)
    (C : MarkedFibre M k) (C' : MarkedFibre A k) :
    let R := CommAlgCat.of Integers.{u} k
    ∀ g : IntegralPoints M.group R,
      (∃ t : TorusValues E R, integralPointHom c.map R g = torusPoint E R t ≫ A.torus.hom.hom) →
      ∃ t : TorusValues D R, g = torusPoint D R t ≫ M.torus.hom.hom := by
  intro R g hg
  obtain ⟨t, ht⟩ := hg
  let S := CommAlgCat.of k k
  let P := C.realization.pinned.pair
  let P' := C'.realization.pinned.pair
  let f := C.groupIso.inv ≫ (fibre k).map c.map ≫ C'.groupIso.hom
  let p := pointHom f (𝟙_ (SchemeOver k))
  obtain ⟨h, rfl⟩ := (markedGroundEquiv C).surjective g
  obtain ⟨t', ht'⟩ := markedGroundTorusPoint C' (torusPoint E R t)
  obtain ⟨hcomm, htor, _, _⟩ := splitCentralPointComparison c C C'
  have he : p h = t' ≫ P'.T.inclusion.hom.hom := by
    apply (markedGroundEquiv C').injective
    rw [markedGroundEquiv_apply C' (p h), hcomm, ← markedGroundEquiv_apply, ht]
    exact ht'.symm
  have hT : FactorsThrough P'.T (p h) := ⟨t', he.symm⟩
  obtain ⟨s, hs⟩ := (htor h).mp hT
  let v := markedTorusEquiv C S (toUnit _ ≫ s)
  obtain ⟨u, hu⟩ :=
    (affineTorusPointEquiv (k := Integers.{u}) (M := Multiplicative D.X) R).surjective v
  refine ⟨u, ?_⟩
  rw [← hs, markedGroundEquiv_apply]
  change markedFibrePoint C S (toUnit _ ≫ s ≫ P.T.inclusion.hom.hom) = _
  rw [← Category.assoc, markedTorusIncl C S]
  exact congrArg (fun q : IntegralPoints (splitTorus D) R => q ≫ M.torus.hom.hom) hu.symm

theorem splitIwahoriCoverComparison : SplitIwahoriCoverComparison.{u} := by
  intro K _ _ _ _ D E M A c C C' R p κ C₀ C₀' B B' hB hB'
  exact ⟨splitIwahoriImage M A c.map c.rootEquiv _ c.marking C₀ C₀' B B' hB hB',
    splitIwahoriPreimage M A c.map c.rootEquiv _ c.marking c.characterIndex
      (splitTorusPointPreimage c C C') C₀ C₀' B B' hB hB'⟩

end SplitCentralMap

section FibreNormalizerFromMarking

open _root_.LinearAlgebraicGroups.Specs.IntegralSemisimpleModel
open _root_.LinearAlgebraicGroups.Specs.ExceptionalMarkedRootDescent (MarkedFibre)
open _root_.LinearAlgebraicGroups.Specs.ExceptionalValuedTorusNormalizer (FibreNormalizer)
open _root_.LinearAlgebraicGroups.Arithmetic.ExceptionalValuedTorusNormalizer
  (markedFibreTorusCoordinates markedFibreSimpleWeylLifts weylGroupTransport)
open private fibrePointsEquiv from LinearAlgebraicGroups.Classification.IntegralSemisimpleModel

attribute [local instance] integerAlgebra

set_option backward.isDefEq.respectTransparency false in
private def normalizerOfMarkedFibre {k : Type u} [Field k] {D : Pinning.BasedRootDatum.{u}}
    {M : Model D} (C : MarkedFibre M k) : FibreNormalizer M k := by
  classical
  let P := C.realization
  let g := C.groupIso
  letI := P.attached.comm
  choose e he ht using markedFibreTorusCoordinates D M P g C.torusIso C.torus_comm C.torus_eval
  choose N q hq hproj hker hsimple using markedFibreSimpleWeylLifts D M P g C.coordinate
    (fun a => Subtype.ext (C.simple_eq a)) C.root_eval e he ht
  choose w hw hχ using weylGroupTransport D P.attached.toBased P.datumIso
  let R := CommAlgCat.of k k
  let Y := (testSpec k).obj (Opposite.op R)
  let a : (𝟙_ (SchemeOver k) ⟶ N.normalizer.group.X) →* (Y ⟶ N.normalizer.group.X) :=
    MonoidHom.mk' (fun n => toUnit Y ≫ n) (fun x y => MonObj.comp_mul (toUnit Y) x y)
  let p := (fibrePointsEquiv M.group R).toMonoidHom.comp
    ((pointHom g.inv Y).comp ((pointHom N.normalizer.inclusion Y).comp a))
  have hp (x : 𝟙_ (SchemeOver k) ⟶ N.normalizer.group.X) :
      p x = forgetFibrePoint M.group R
        (toUnit Y ≫ x ≫ N.normalizer.inclusion.hom.hom ≫ g.inv.hom.hom) := by
    change forgetFibrePoint M.group R
      (((toUnit Y ≫ x) ≫ N.normalizer.inclusion.hom.hom) ≫ g.inv.hom.hom) = _
    simp only [Category.assoc]
  let q₀ := w.symm.toMonoidHom.comp q
  exact {
    line := C.line
    realization := P
    fibreIso := g
    torusComm := inferInstance
    identification := N
    labelIso := w
    labelIso_simple := hw
    labelIso_character := hχ
    label := q₀
    label_surjective := w.symm.surjective.comp hq
    projection := fun n => by
      change n ≫ N.quotient.hom.hom =
        N.image.constantGroup.sectionPoint (N.labelEquiv (w (w.symm (q n))))
      rw [w.apply_symm_apply]
      exact hproj n
    kernel := fun n => by
      change w.symm (q n) = 1 ↔ _
      rw [← w.symm.map_one, w.symm.injective.eq_iff]
      exact hker n
    point := p
    point_eq := hp
    torusValues := e
    character := he
    torusPoint_eq := ht
    simple := fun a => by
      obtain ⟨r, n, hn, h, hword⟩ := hsimple a
      refine ⟨r, n, hn, ?_, (hp n).trans (hword R), hword⟩
      apply w.injective
      change w (w.symm (q n)) = w _
      rw [w.apply_symm_apply, hw]
      exact h }

end FibreNormalizerFromMarking

section PinnedScalarComparison

open CategoryTheory.Limits Opposite WithConv
open scoped TensorProduct

open _root_.LinearAlgebraicGroups.Specs.IntegralSemisimpleModel
open _root_.LinearAlgebraicGroups.Specs.ExceptionalMarkedRootDescent
open _root_.LinearAlgebraicGroups.Specs.ExceptionalValuedTorusNormalizer
open _root_.LinearAlgebraicGroups.Specs.AdjointBorelCohomology (PinnedTwist)
open _root_.LinearAlgebraicGroups.Specs.AdjointRepresentation (GroupPoints)
open private extensionPointEquiv extensionPoint_coordinates evaluateSplitPoint extendedPresentation
  hopfRationalEquiv hopfRationalEquiv_apply hopfRationalPoint hopfRationalPoint_eq
  groundExtendPoint scalarPresentedCoordinate rationalPoint_compHopf sectionsIso
  from LinearAlgebraicGroups.Arithmetic.ExceptionalValuedTorusNormalizer
open private coordinatePointEquiv_natural from LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
open private extendedCoordinateIso from LinearAlgebraicGroups.Descent.AdjointBorelCohomology
open private groundIso from LinearAlgebraicGroups.Solvable.TorusSections

attribute [local instance] integerAlgebra

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

set_option backward.isDefEq.respectTransparency false in
private theorem extendedPresentation_unique (G : AffineAlgebraicGroup k)
    (a b : specGroup (extendedHopf K (Specs.AdjointCocharacters.coordinateHopf G)) ≅
      (groupBaseChange k K).obj G.val)
    (ha : ExtendsCoordinatePresentation G a) (hb : ExtendsCoordinatePresentation G b) : a = b := by
  apply Iso.ext
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext (ha.trans hb.symm)
  exact (Over.w a.hom.hom.hom).trans (Over.w b.hom.hom.hom).symm

set_option backward.isDefEq.respectTransparency false in
private theorem groundHopfEquiv_inverse (G : AffineAlgebraicGroup k)
    (p : Specs.AdjointCocharacters.coordinateHopf G →ₐ[k] k) :
    (groundHopfEquiv G).symm (toConv p) =
      hopfRationalPoint (Specs.AdjointCocharacters.coordinateHopf G) p ≫
        (Specs.AdjointCocharacters.coordinateHopfIso G).hom.hom.hom := by
  apply (groundHopfEquiv G).injective
  rw [MulEquiv.apply_symm_apply]
  let R := CommAlgCat.of k k
  apply (coordinatePointEquiv G R).injective
  change coordinatePointEquiv G R (toConv p) =
    coordinatePointEquiv G R ((coordinatePointEquiv G R).symm (toUnit _ ≫
      hopfRationalPoint (Specs.AdjointCocharacters.coordinateHopf G) p ≫
        (Specs.AdjointCocharacters.coordinateHopfIso G).hom.hom.hom))
  rw [MulEquiv.apply_symm_apply]
  change coordinatePointEquiv G R (toConv p) =
    toUnit ((testSpec k).obj (op R)) ≫ hopfRationalPoint (Specs.AdjointCocharacters.coordinateHopf G) p ≫
      (Specs.AdjointCocharacters.coordinateHopfIso G).hom.hom.hom
  let m : (testSpec k).obj (op R) ⟶ (specGroup (Specs.AdjointCocharacters.coordinateHopf G)).X :=
    (testSpec k).map (CommAlgCat.ofHom p).op
  let t := (Specs.AdjointCocharacters.coordinateHopfIso G).hom.hom.hom
  let e := groundIso (k := k)
  have hu : toUnit ((testSpec k).obj (op R)) = e.hom := Subsingleton.elim _ _
  have hm : hopfRationalPoint (Specs.AdjointCocharacters.coordinateHopf G) p = e.inv ≫ m := rfl
  calc
    _ = m ≫ t := rfl
    _ = (e.hom ≫ e.inv ≫ m) ≫ t := congrArg (· ≫ t) (e.hom_inv_id_assoc m).symm
    _ = e.hom ≫ (e.inv ≫ m) ≫ t := Category.assoc _ _ _
    _ = _ := congrArg₂ (fun x y => x ≫ y ≫ t) hu.symm hm.symm

set_option backward.isDefEq.respectTransparency false in
private theorem pinnedGroundPoint_scalar {D : Pinning.BasedRootDatum.{u}} {M : Model D}
    (C : MarkedFibre M k)
    {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
    {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}
    (d : PinnedTwist K C.realization.attached l B T)
    (a : specGroup (extendedHopf K (Specs.AdjointCocharacters.coordinateHopf G)) ≅
      (groupBaseChange k K).obj G.val)
    (b : specGroup (extendedHopf K (Specs.AdjointCocharacters.coordinateHopf C.realization.pinned.pair.G)) ≅
      (groupBaseChange k K).obj C.realization.pinned.pair.G.val)
    (ha : ExtendsCoordinatePresentation G a) (hb : ExtendsCoordinatePresentation C.realization.pinned.pair.G b)
    (g : 𝟙_ (SchemeOver k) ⟶ G.val.X) :
    let e := a.symm ≪≫ (hopfSpec (CommRingCat.of K)).mapIso d.groupIso.op ≪≫ b
    pinnedGroundPoint C d g = markedFibrePoint C (CommAlgCat.of k K)
      (extensionPointEquiv C.realization.pinned.pair.G.val
        (scalarExtendedRationalPoint K g ≫ e.hom.hom.hom)) := by
  let P := C.realization.pinned.pair.G
  let a₀ := extendedCoordinateIso (K := K) G
  have ha₀ : a = a₀ := extendedPresentation_unique G a a₀ ha (extendedPresentation G)
  subst a
  let q := (groundHopfEquiv G g).ofConv
  let p := ((groundExtendPoint (K := K) (Specs.AdjointCocharacters.coordinateHopf G) q)).comp
    d.groupIso.hom.hom.toAlgHom
  intro e
  have hg : g = hopfRationalPoint (Specs.AdjointCocharacters.coordinateHopf G) q ≫
      (Specs.AdjointCocharacters.coordinateHopfIso G).hom.hom.hom :=
    ((groundHopfEquiv G).symm_apply_apply g).symm.trans (groundHopfEquiv_inverse G q)
  have hscalar : scalarExtendedRationalPoint K g ≫ e.hom.hom.hom =
      hopfFieldPoint p ≫ b.hom.hom.hom := by
    rw [show scalarExtendedRationalPoint K g = _ from (congrArg (scalarExtendedRationalPoint K) hg).trans
      (scalarPresentedCoordinate (K := K) G q)]
    simp only [e, Iso.trans_hom, Iso.symm_hom, Grp.comp_hom_hom, Category.assoc]
    have hcancel : a₀.hom.hom.hom ≫ a₀.inv.hom.hom = 𝟙 _ :=
      congrArg (fun f => f.hom.hom) a₀.hom_inv_id
    rw [← Category.assoc a₀.hom.hom.hom, hcancel, Category.id_comp, ← Category.assoc]
    change (hopfRationalPoint _ (groundExtendPoint _ q) ≫
      (specGroupMap d.groupIso.hom).hom.hom) ≫ b.hom.hom.hom = _
    rw [rationalPoint_compHopf, hopfRationalPoint_eq]
  rw [hscalar, extensionPoint_coordinates P b hb, pinnedGroundPoint_apply,
    pinnedMarkedPoint, evaluateMarkedFibrePoint]
  congr 1
  let S := CommAlgCat.of k k
  let R := CommAlgCat.of k K
  change mapPoints (groundEvaluation (k := k) (K := K)) (pinnedSchemePoint d S (groundHopfEquiv G g)) =
    evaluateSplitPoint P p
  rw [pinnedSchemePoint, ← coordinatePointEquiv_natural]
  change coordinatePointEquiv P R _ = coordinatePointEquiv P R _
  apply congrArg (coordinatePointEquiv P R)
  apply ofConv_injective
  apply AlgHom.ext
  intro x
  change (groundEvaluation (k := k) (K := K)).hom
      (((AlgHom.liftEquiv k K _ _).symm (pinnedAlgebraPointMap d q)) x) =
    ((AlgHom.liftEquiv k K _ _).symm p) x
  change _ = p (1 ⊗ₜ[k] x)
  change (Algebra.TensorProduct.rid k K K)
      ((pinnedAlgebraPointMap d q) (1 ⊗ₜ[k] x)) = _
  have hq : extendAlgebraPoint (K := K) q = Algebra.TensorProduct.map (AlgHom.id K K) q := by
    apply Algebra.TensorProduct.ext_ring
    apply AlgHom.ext
    intro y
    change extendAlgebraPoint (K := K) q (1 ⊗ₜ[k] y) = _
    simp [extendAlgebraPoint, AlgHom.liftEquiv_tmul]
  rw [pinnedAlgebraPointMap, hq]
  rfl

end PinnedScalarComparison

section FoldedNormalizerPresentation

open CategoryTheory.Limits Opposite

open _root_.LinearAlgebraicGroups.Specs.IntegralSemisimpleModel
open _root_.LinearAlgebraicGroups.Specs.ExceptionalValuedTorusNormalizer
open _root_.LinearAlgebraicGroups.Specs.ExceptionalMarkedRootDescent
  (MarkedFibre SimpleRootOrbit markedFibrePoint pinnedDiagram pinnedMarkedPoint evaluateGroundTensor)
open _root_.LinearAlgebraicGroups.Specs.AdjointBorelCohomology (PinnedTwist)
open _root_.LinearAlgebraicGroups.Specs.SchemeDerivedGroup (FactorsThrough)
open _root_.LinearAlgebraicGroups.Arithmetic.ExceptionalValuedTorusNormalizer
  (foldedApartmentAction markedPinnedDiagramAction markedPinnedTorus descendedRelativeNormalizer
    pinnedQuadraticNormalizer quadraticStabilizerFields fibreNormalizerTorusAction
    involutiveValuationInvariant)
open _root_.LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent (pinnedWeylWordFixed)
open private quadraticGalois markedWeylWord_map fibrePointEquiv from
  LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
open private markedNormalizerPointHom markedNormalizerPointHom_apply extensionPointEquiv
  normalizedValuation_le_iff from
  LinearAlgebraicGroups.Arithmetic.ExceptionalValuedTorusNormalizer
open private affineTorusPointEquiv from LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
open private subgroup_normalizes from LinearAlgebraicGroups.RootData.BorelNormalizer
attribute [local instance] integerAlgebra

set_option backward.isDefEq.respectTransparency false in
private theorem fieldNormalizer_constantLabel {k K : Type u} [Field k] [Field K] [Algebra k K]
    {D : Pinning.BasedRootDatum.{u}} {M : Model D} (F : FibreNormalizer M k) :
    letI := F.torusComm
    let C := F.identification
    let Y := (testSpec k).obj (op (CommAlgCat.of k K))
    ∀ (q : (Y ⟶ C.normalizer.group.X) →* D.datum.weylGroup),
      (∀ n, n ≫ C.quotient.hom.hom = toUnit Y ≫
        C.image.constantGroup.sectionPoint (C.labelEquiv (F.labelIso (q n)))) →
      ∀ n, q (toUnit Y ≫ n) = F.label n := by
  letI := F.torusComm
  intro C Y q hp n
  let e := F.labelIso.trans C.labelEquiv
  have hproj := hp (toUnit Y ≫ n)
  rw [Category.assoc, F.projection] at hproj
  apply e.injective
  let h := C.image.constantGroup.families Y
  let y : Y.left := IsLocalRing.closedPoint K
  have he := congrArg (fun g => h g y) hproj.symm
  change h (toUnit Y ≫ C.image.constantGroup.sectionPoint (e (q (toUnit Y ≫ n)))) y =
    h (toUnit Y ≫ C.image.constantGroup.sectionPoint (e (F.label n))) y at he
  simpa only [h, C.image.constantGroup.constant, LocallyConstant.coe_const, Function.const_apply] using he

set_option backward.isDefEq.respectTransparency false in
private theorem extensionMarkedNormalizerWord {k K : Type u} [Field k] [Field K] [Algebra k K]
    {D : Pinning.BasedRootDatum.{u}} {M : Model D} (F : FibreNormalizer M k) :
    letI := F.torusComm
    let C := F.identification
    let R := CommAlgCat.of k K
    let Y := (testSpec k).obj (op R)
    ∀ (q : (Y ⟶ C.normalizer.group.X) →* D.datum.weylGroup),
      (∀ n, n ≫ C.quotient.hom.hom = toUnit Y ≫
        C.image.constantGroup.sectionPoint (C.labelEquiv (F.labelIso (q n)))) →
      ∀ (l : List D.I), (∀ i ∈ l, i ∈ D.base.support) →
      ∃ n, markedNormalizerPoint F R n =
        ExceptionalMarkedRootDescent.markedWeylWord M.toIntegralMarking (CommAlgCat.of Integers.{u} K) l ∧
        q n = (l.map (RootPairing.weylGroup.ofIdx D.datum)).prod := by
  letI := F.torusComm
  intro C R Y q hq l hl
  let p := markedNormalizerPointHom F R
  have hp (n : Y ⟶ C.normalizer.group.X) : p n = markedNormalizerPoint F R n :=
    markedNormalizerPointHom_apply F R n
  have hc := fieldNormalizer_constantLabel F q hq
  induction l with
  | nil => exact ⟨1, (hp 1).symm.trans (map_one p), map_one q⟩
  | cons i l ih =>
    obtain ⟨n, hn, hnq⟩ := ih (fun a ha => hl a (List.mem_cons_of_mem _ ha))
    obtain ⟨_, m, _, hmq, _, hm⟩ := F.simple ⟨i, hl i List.mem_cons_self⟩
    let m' := toUnit Y ≫ m
    have hm' : p m' = markedWeylWord M.toIntegralMarking i (CommAlgCat.of Integers.{u} K) 1 :=
      (hp m').trans (hm R)
    refine ⟨m'⁻¹ * n, ?_, ?_⟩
    · rw [← hp, map_mul, map_inv, hm', hp, hn, markedWeylWord_inv]
      rfl
    · rw [map_mul, map_inv, hc, hmq, hnq]
      have he : (RootPairing.weylGroup.ofIdx D.datum i)⁻¹ = RootPairing.weylGroup.ofIdx D.datum i :=
        Subtype.ext (RootPairing.Equiv.reflection_inv D.datum i)
      rw [he]
      rfl

private theorem monoOfClosedOverMap {k : Type u} [Field k] {X Y : SchemeOver k}
    (f : X ⟶ Y) (h : IsClosedImmersion f.left) : Mono f := by
  letI := h
  exact Over.mono_of_mono_left _

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1850000 in
theorem foldedMarkedNormalizerPresentation : FoldedMarkedNormalizerPresentation.{u} := by
  classical
  intro k K _ _ _ _ _ _ _ _ _ _ _ D M C F l Q hQ ω d σ hd hσ e W hsym horth hr b hb word hw hwq R
  let P := C.realization
  let F₀ := normalizerOfMarkedFibre C
  letI := F₀.torusComm
  letI := F.torusComm
  let C₁ := F₀.identification
  let R₁ := CommAlgCat.of k K
  let Y := (testSpec k).obj (op R₁)
  let G := (𝟙_ (SchemeOver k) ⟶ d.group.val.X)
  obtain ⟨p, hp, hp₀, _, hpT, hpFix⟩ := pinnedGroundPointComparison C d.data σ hd hσ
  obtain ⟨cb, _, hdiag, _⟩ := markedPinnedTorus D P hQ d.data b hb
  obtain ⟨S, Q₀, hS, hST, _, _, hNS, _⟩ := descendedRelativeNormalizer d cb hdiag
  obtain ⟨hpin, hchar, hinv⟩ := markedPinnedDiagramAction P hQ (d.data.outer σ)
  have hσsq := (quadraticGalois hd σ hσ).2
  have hσinv : Function.Involutive σ := fun x => by
    change (σ * σ) x = x
    rw [hσsq]
    rfl
  have hr' (a : k) : normalizedValuation K (algebraMap k K a) = (normalizedValuation k a) ^ 2 :=
    hr a
  letI : ValuativeExtension k K := ⟨fun a b => by
    rw [← normalizedValuation_le_iff, ← normalizedValuation_le_iff, hr', hr']
    exact pow_le_pow_iff_left₀ zero_le zero_le (by decide)⟩
  have hval := involutiveValuationInvariant σ hσinv
  have heinv : Function.Involutive e.val.indexEquiv := hinv (by rw [← map_mul, hσsq, map_one])
  let s := (l (d.data.outer σ)).asIso.hom
  obtain ⟨q, a, hq, hk, ha, q₀, ν, j, hq₀, hj, hjT, hproj, _⟩ :=
    foldedApartmentAction F₀ e s σ b hb hσinv heinv hsym horth hpin (hchar b hb) hval
  let H := MonoidHom.eqLocus a.toMonoidHom (fieldCoefficientAction σ C₁.normalizer.group)
  let N₀ := Q₀.normalizer
  have hN₀ (g : G) : Normalizes d.torus.inclusion g ↔
      ∃ n : 𝟙_ (SchemeOver k) ⟶ N₀.group.X, n ≫ N₀.inclusion.hom.hom = g :=
    (hNS g).symm.trans (Q₀.normalizerProperty _ _)
  obtain ⟨a₁, a₂, ha₁, ha₂, _, uN, _, huN, huT⟩ :=
    pinnedQuadraticNormalizer F₀ d.data σ hd hσ a ha N₀ hN₀
  let i := pointHom N₀.inclusion (𝟙_ (SchemeOver k))
  letI : IsClosedImmersion N₀.inclusion.hom.hom.left := N₀.isClosedImmersion
  letI : Mono N₀.inclusion.hom.hom := Over.mono_of_mono_left _
  let iN := MonoidHom.ofInjective (f := i) (fun _ _ h => (cancel_mono N₀.inclusion.hom.hom).mp h)
  let eN := iN.symm.trans uN
  let T := SubgroupSections d.torus (𝟙_ (SchemeOver k))
  let N := i.range
  have hTN : T ≤ N := fun g hg => (hN₀ g).mp (subgroup_normalizes d.torus hg)
  let qR := q₀.comp eN.toMonoidHom
  have hTker (n : N) : qR n = 1 ↔ (n : G) ∈ T := by
    have hx : (q₀ (uN (iN.symm n))) = 1 ↔ q (uN (iN.symm n)).val = 1 := by
      rw [← hq₀]
      exact Subtype.ext_iff
    have hm : i (iN.symm n) = (n : G) := congrArg Subtype.val (iN.apply_symm_apply n)
    change q₀ (uN (iN.symm n)) = 1 ↔ _
    rw [hx, hk, ← huT]
    change (∃ z, z ≫ d.torus.inclusion.hom.hom = i (iN.symm n)) ↔ _
    rw [hm]
    rfl
  have hext (g : 𝟙_ (SchemeOver k) ⟶ N₀.group.X) :
      p (i g) = j (uN g) := by
    let E := a₁.symm ≪≫ (hopfSpec (CommRingCat.of K)).mapIso d.data.groupIso.op ≪≫ a₂
    let x := scalarExtendedRationalPoint K (i g) ≫ E.hom.hom.hom
    rw [hp₀, pinnedGroundPoint_scalar C d.data a₁ a₂ ha₁ ha₂, hj]
    change markedFibrePoint C R₁ (extensionPointEquiv P.pinned.pair.G.val x) =
      markedFibrePoint C R₁ ((uN g).val ≫ C₁.normalizer.inclusion.hom.hom)
    apply congrArg (markedFibrePoint C R₁)
    apply Over.OverMorphism.ext
    have hx : (extensionPointEquiv P.pinned.pair.G.val x).left =
        x.left ≫ pullback.fst P.pinned.pair.G.val.X.hom (fieldSpecMap k K) := by
      change (𝟙 (Spec (CommRingCat.of K)) ≫ x.left) ≫ _ = _
      rw [Category.id_comp]
    rw [hx]
    exact (huN g).symm
  have hR (n : N) : p n = j (eN n) := by
    rw [← show i (iN.symm n) = (n : G) from congrArg Subtype.val (iN.apply_symm_apply n)]
    exact hext (iN.symm n)
  let hT : T →* N := T.subtype.codRestrict N (fun t => hTN t.property)
  let aT : T →* q₀.ker :=
    (eN.toMonoidHom.comp hT).codRestrict q₀.ker (fun t => (hTker (hT t)).mpr t.property)
  have haT : Function.Bijective aT := by
    constructor
    · intro x y h
      apply Subtype.ext
      exact congrArg (fun n : N => (n : G)) (eN.injective (congrArg Subtype.val h))
    · intro x
      let n := eN.symm x.val
      have h : (n : G) ∈ T := (hTker n).mp (by
        change q₀ (eN (eN.symm x.val)) = 1
        rw [eN.apply_symm_apply]
        exact x.property)
      refine ⟨⟨n, h⟩, Subtype.ext ?_⟩
      exact eN.apply_symm_apply x.val
  let eT := MulEquiv.ofBijective aT haT
  have htor (t : T) : ∃ v : TorusValues D R,
      p t = torusPoint D R v ≫ M.torus.hom.hom ∧
      ∀ x, D.datum.toLinearMap x (ν (eT t)).toAdd =
        WithZero.log (normalizedValuation K (v (Multiplicative.ofAdd x) : K)) := by
    obtain ⟨v, hv, hlog⟩ := hjT (eT t)
    exact ⟨v, (hR (hT t)).trans hv, hlog⟩
  let wL := fun w : W => (word w).flatMap SimpleRootOrbit.roots
  have hwL (w : W) : ∀ a ∈ wL w, a ∈ D.base.support := by
    intro a ha
    obtain ⟨o, _, ho⟩ := List.mem_flatMap.mp ha
    rcases o with ⟨z, y⟩
    cases y with
    | none =>
      simp [SimpleRootOrbit.roots] at ho
      exact ho ▸ z.property
    | some b =>
      simp [SimpleRootOrbit.roots] at ho
      exact ho.elim (fun h => h ▸ z.property) (fun h => h ▸ b.property)
  have hwords (w : W) : ∃ n : N, qR n = w ∧
      p n = ExceptionalMarkedRootDescent.markedWeylWord M.toIntegralMarking R (wL w) := by
    obtain ⟨m, hm, hmQ⟩ := extensionMarkedNormalizerWord F₀ q hq (wL w) (hwL w)
    obtain ⟨g, hg⟩ := pinnedWeylWordFixed C d.data hd σ hσ hsym (word w) (hw w)
      (CommAlgCat.of k k)
    obtain ⟨x, rfl⟩ := (groundHopfEquiv d.group).surjective g
    have hx : p x = ExceptionalMarkedRootDescent.markedWeylWord M.toIntegralMarking R (wL w) := by
      rw [hp₀, pinnedGroundPoint_apply, hg]
      exact markedWeylWord_map M.toIntegralMarking (evaluateGroundTensor k K) (wL w)
    have hm' : markedFibrePoint C R₁ (m ≫ C₁.normalizer.inclusion.hom.hom) = p x :=
      hm.trans hx.symm
    have hrange : markedFibrePoint C R₁ (m ≫ C₁.normalizer.inclusion.hom.hom) ∈ p.range :=
      ⟨x, hm'.symm⟩
    have hfixed := (hpFix (m ≫ C₁.normalizer.inclusion.hom.hom)).mp hrange
    have hmH : m ∈ H := by
      change a m = fieldCoefficientAction σ C₁.normalizer.group m
      letI : Mono C₁.normalizer.inclusion.hom.hom :=
        monoOfClosedOverMap _ C₁.normalizer.isClosedImmersion
      apply (cancel_mono C₁.normalizer.inclusion.hom.hom).mp
      rw [ha]
      let f := (testSpec k).map (CommAlgCat.ofHom σ.toAlgHom).op
      have hff : f ≫ f = 𝟙 Y := by
        let c : R₁ ⟶ R₁ := CommAlgCat.ofHom σ.toAlgHom
        have hc : c ≫ c = 𝟙 R₁ := by
          apply CommAlgCat.hom_ext
          apply AlgHom.ext
          intro z
          exact hσinv z
        change (testSpec k).map c.op ≫ (testSpec k).map c.op = _
        rw [← (testSpec k).map_comp, ← op_comp, hc, op_id, (testSpec k).map_id]
      change f ≫ (m ≫ C₁.normalizer.inclusion.hom.hom) ≫ s.group.hom.hom.hom =
        m ≫ C₁.normalizer.inclusion.hom.hom at hfixed
      have h := congrArg (f ≫ ·) hfixed
      simp only [← Category.assoc, hff] at h
      exact h
    let n := eN.symm ⟨m, hmH⟩
    refine ⟨n, ?_, ?_⟩
    · change q₀ (eN (eN.symm ⟨m, hmH⟩)) = w
      rw [eN.apply_symm_apply]
      exact Subtype.ext ((hq₀ _).trans (hmQ.trans (hwq w)))
    · rw [hR]
      change j (eN (eN.symm ⟨m, hmH⟩)) = _
      rw [eN.apply_symm_apply, hj]
      exact hm
  choose L hL hLp using hwords
  let V : MarkedLocalNormalizer K p W :=
    { torus := T
      normalizer := N
      torus_le := hTN
      torusPoints := fun g => ⟨fun h => by obtain ⟨v, hv, _⟩ := htor ⟨g, h⟩; exact ⟨v, hv⟩,
        fun ⟨v, hv⟩ => hpT (torusPoint D R v) g hv⟩
      label := qR
      labelKernel := hTker
      translation := ν.comp eT.toMonoidHom
      characterLog := fun t v hv x => by
        obtain ⟨v', hv', hl⟩ := htor t
        have ht : v' = v := by
          letI : IsClosedImmersion M.torus.hom.hom.left := M.torusClosed
          letI : Mono M.torus.hom.hom := Over.mono_of_mono_left _
          exact (affineTorusPointEquiv (k := Integers.{u}) (M := Multiplicative D.X) R).injective
            ((cancel_mono M.torus.hom.hom).mp (hv'.symm.trans hv))
        exact ht ▸ hl x
      word := wL
      lift := L
      lift_label := hL
      lift_point := hLp }
  refine ⟨p, V, S, hp, hp₀, hS, fun g => (hN₀ g).symm.trans (hNS g).symm,
    fun g => (hN₀ g).symm, fun _ => Iff.rfl, ?_, fun _ => rfl, localNormalizer_unitKernel V, ?_⟩
  · intro n
    let w := qR n
    obtain ⟨m, hm, hmq⟩ := splitMarkedNormalizerWord F (wL w) (hwL w)
    have ht : ((n * (L w)⁻¹ : N) : G) ∈ T :=
      (hTker _).mp (by rw [map_mul, map_inv, hL]; exact mul_inv_cancel _)
    obtain ⟨v, hv, _⟩ := htor ⟨_, ht⟩
    obtain ⟨z, hz, _⟩ := fibreNormalizerTorusAction F
    refine ⟨(z v).val * m, ?_, ?_⟩
    · rw [map_mul, hz, hm, ← hv, ← hLp w]
      change p _ * p _ = p _
      rw [← map_mul]
      congr 1
      exact inv_mul_cancel_right _ _
    · rw [map_mul, (z v).property, one_mul, hmq, hwq]
  · have hh := hproj hr' (quadraticStabilizerFields hd σ hσ).1
    rw [← hh]
    let f := fun z : q₀.ker => fun i : D.base.support => ((b.repr (ν z).toAdd i : ℤ) : ℚ) / 2
    change Set.range (f ∘ eT) = Set.range f
    rw [Set.range_comp, eT.surjective.range_eq, Set.image_univ]

end FoldedNormalizerPresentation

section CentralDiagram

open Specs.IntegralSemisimpleModel (Model)

private theorem characterPullback_commutes_diagram
    {D E : Pinning.BasedRootDatum.{u}} {M : Model D} {A : Model E}
    (c : MarkedCentralCover M A) (hE : E.datum.rootSpan ℤ = ⊤)
    (d : Pinning.BasedIso D D) (e : Pinning.BasedIso E E)
    (hde : ∀ a, c.rootEquiv (d.val.indexEquiv a) = e.val.indexEquiv (c.rootEquiv a)) :
    c.pullCharacter.comp e.val.weightEquiv.toLinearMap =
      d.val.weightEquiv.toLinearMap.comp c.pullCharacter := by
  let f := c.pullCharacter.comp e.val.weightEquiv.toLinearMap
  let g := d.val.weightEquiv.toLinearMap.comp c.pullCharacter
  have hroot (a : D.I) : f (E.datum.root (c.rootEquiv a)) = g (E.datum.root (c.rootEquiv a)) := by
    change c.pullCharacter (e.val.weightEquiv (E.datum.root (c.rootEquiv a))) =
      d.val.weightEquiv (c.pullCharacter (E.datum.root (c.rootEquiv a)))
    rw [show e.val.weightEquiv (E.datum.root (c.rootEquiv a)) =
      E.datum.root (e.val.indexEquiv (c.rootEquiv a)) from
        RootPairing.Hom.root_weightMap_apply E.datum E.datum _ e.val.toHom,
      ← hde, c.roots, c.roots]
    exact (RootPairing.Hom.root_weightMap_apply D.datum D.datum a d.val.toHom).symm
  have hker : E.datum.rootSpan ℤ ≤ (f - g).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    obtain ⟨a, rfl⟩ := c.rootEquiv.surjective a
    exact LinearMap.mem_ker.mpr (sub_eq_zero.mpr (hroot a))
  exact sub_eq_zero.mp (LinearMap.ker_eq_top.mp (top_le_iff.mp (hE ▸ hker)))

end CentralDiagram

section MarkedDiagramPoints

open CategoryTheory.Limits
open Opposite

open Specs.IntegralSemisimpleModel
open Specs.ExceptionalMarkedRootDescent
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterPairing (characterValue)
open Specs.Pinning (transportCharacter)
open Specs.ExceptionalValuedTorusNormalizer (markedDiagramEquiv simplePermutation)
open LinearAlgebraicGroups.Arithmetic.ExceptionalValuedTorusNormalizer
  (markedFibreTorusCoordinates markedPinnedDiagramAction)
open LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
  (pinnedSimpleRankOneEquivariance integralWeylWordTransport)
open private pinnedLift_character from LinearAlgebraicGroups.Arithmetic.ExceptionalValuedTorusNormalizer
open private characterValue_composition from LinearAlgebraicGroups.Relative.ReductiveLieCentralizers
open private fibrePointEquiv markedFibrePoint_root from
  LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
open private forgetFibrePoint_comp from LinearAlgebraicGroups.Classification.IntegralRealization

attribute [local instance] integerAlgebra

variable {k : Type u} [Field k]
  {D E : Pinning.BasedRootDatum.{u}} {M : Model D} {A : Model E}

set_option backward.isDefEq.respectTransparency false in
private theorem markedFibrePoint_natural (c : MarkedCentralCover M A)
    (C : MarkedFibre M k) (C' : MarkedFibre A k) (R : TestAlgebra k)
    (g : GroupPoints C.realization.pinned.pair.G.val R) :
    let f := C.groupIso.inv ≫ (fibre k).map c.map ≫ C'.groupIso.hom
    markedFibrePoint C' R (g ≫ f.hom.hom) =
      integralPointHom c.map ((integralTestAlgebra k).obj R) (markedFibrePoint C R g) := by
  intro f
  let g₀ : GroupPoints ((fibre k).obj M.group) R := g ≫ C.groupIso.inv.hom.hom
  have hx : (g ≫ f.hom.hom) ≫ C'.groupIso.inv.hom.hom =
      g₀ ≫ ((fibre k).map c.map).hom.hom := by
    simp only [f, g₀, Grp.comp_hom_hom, Category.assoc]
    have he : C'.groupIso.hom.hom.hom ≫ C'.groupIso.inv.hom.hom = 𝟙 _ :=
      congrArg (fun u => u.hom.hom) C'.groupIso.hom_inv_id
    simp only [he, Category.comp_id]
  exact (congrArg (forgetFibrePoint A.group R) hx).trans (forgetFibrePoint_comp c.map R g₀)

set_option backward.isDefEq.respectTransparency false in
private theorem simpleRoot_iff_indecomposable (D : Pinning.BasedRootDatum.{u}) (i : D.I) :
    i ∈ D.base.support ↔ D.base.IsPos i ∧
      ∀ j, D.base.IsPos j → ∀ l, D.base.IsPos l →
        D.datum.root i ≠ D.datum.root j + D.datum.root l := by
  letI := D.finiteRoots
  constructor
  · intro hi
    refine ⟨D.base.isPos_of_mem_support hi, fun j hj l hl h => ?_⟩
    have e := D.base.height_add h
    rw [D.base.height_one_of_mem_support hi] at e
    rw [RootPairing.Base.isPos_iff] at hj hl
    omega
  · rintro ⟨hi, h⟩
    have hp := hi.induction_on_add
      (p := fun a => D.base.IsPos a ∧ ((∀ j, D.base.IsPos j → ∀ l, D.base.IsPos l →
        D.datum.root a ≠ D.datum.root j + D.datum.root l) → a ∈ D.base.support))
      (fun a ha => ⟨D.base.isPos_of_mem_support ha, fun _ => ha⟩)
      (fun j l a hroot hj hl => ⟨hj.1.add (D.base.isPos_of_mem_support hl) hroot,
        fun h₀ => (h₀ j hj.1 l (D.base.isPos_of_mem_support hl) hroot).elim⟩)
    exact hp.2 h

set_option backward.isDefEq.respectTransparency false in
private theorem cover_simple (c : MarkedCentralCover M A) (i : D.I) :
    i ∈ D.base.support ↔ c.rootEquiv i ∈ E.base.support := by
  rw [simpleRoot_iff_indecomposable, simpleRoot_iff_indecomposable, c.marking.1 i]
  refine and_congr_right (fun _ => ⟨?_, ?_⟩)
  · intro h j hj l hl he
    obtain ⟨j, rfl⟩ := c.rootEquiv.surjective j
    obtain ⟨l, rfl⟩ := c.rootEquiv.surjective l
    apply h j ((c.marking.1 j).mpr hj) l ((c.marking.1 l).mpr hl)
    simpa only [map_add, c.roots] using congrArg c.pullCharacter he
  · intro h j hj l hl he
    apply h (c.rootEquiv j) ((c.marking.1 j).mp hj) (c.rootEquiv l) ((c.marking.1 l).mp hl)
    apply c.characterInjective
    simpa only [map_add, c.roots] using he

set_option backward.isDefEq.respectTransparency false in
private theorem markedDiagramCharacter (C : MarkedFibre M k)
    {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
    {Q : AutomorphismSequence.AdjointQuotient C.realization.pinned.pair.G}
    (hQ : AutomorphismSequence.SplitSequence C.realization.pinned C.realization.attached l Q)
    (a : Aut C.realization.attached.toBased) (x : D.X) :
    let s := (l a).asIso.hom
    let e := ((markedDiagramEquiv C.realization) a).asIso.hom
    transportCharacter s.torus (Additive.toMul (C.realization.datumIso.val.weightEquiv x)) =
      Additive.toMul (C.realization.datumIso.val.weightEquiv (e.val.weightEquiv x)) := by
  intro s e
  rw [pinnedLift_character hQ]
  change Additive.toMul (a.asIso.hom.val.weightEquiv (C.realization.datumIso.val.weightEquiv x)) = _
  change _ = Additive.toMul (C.realization.datumIso.val.weightEquiv
    (C.realization.datumIso.val.weightEquiv.symm (a.asIso.hom.val.weightEquiv
      (C.realization.datumIso.val.weightEquiv x))))
  rw [LinearEquiv.apply_symm_apply]

set_option backward.isDefEq.respectTransparency false in
private theorem pinnedTorusValues (C : MarkedFibre M k)
    {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
    {Q : AutomorphismSequence.AdjointQuotient C.realization.pinned.pair.G}
    (hQ : AutomorphismSequence.SplitSequence C.realization.pinned C.realization.attached l Q)
    (a : Aut C.realization.attached.toBased) (R : TestAlgebra k)
    (t : GroupPoints C.realization.pinned.pair.T.group R)
    (v : TorusValues D ((integralTestAlgebra k).obj R))
    (hv : ∀ x, characterValue (Additive.toMul (C.realization.datumIso.val.weightEquiv x)) R t =
      (v (Multiplicative.ofAdd x) : R)) :
    let s := (l a).asIso.hom
    let e := ((markedDiagramEquiv C.realization) a).asIso.hom
    let m := e.val.weightEquiv.symm.toLinearMap.toAddMonoidHom.toMultiplicative
    markedFibrePoint C R ((t ≫ s.torus.hom.hom.hom) ≫ C.realization.pinned.pair.T.inclusion.hom.hom) =
      torusPoint D ((integralTestAlgebra k).obj R) (v.comp m) ≫ M.torus.hom.hom := by
  intro s e m
  obtain ⟨u, hu, hi⟩ := markedFibreTorusCoordinates D M C.realization C.groupIso C.torusIso C.torus_comm C.torus_eval
  have ht : t ≫ s.torus.hom.hom.hom = u R (v.comp m) := by
    obtain ⟨w, hw⟩ := (u R).surjective (t ≫ s.torus.hom.hom.hom)
    rw [← hw]
    apply congrArg (u R)
    apply MonoidHom.ext
    intro z
    apply Units.ext
    let x := Multiplicative.toAdd z
    change ((w (Multiplicative.ofAdd x) : Rˣ) : R) = (v (m (Multiplicative.ofAdd x)) : R)
    let χ (y : D.X) : CharacterDescent.Character C.realization.pinned.pair.T.group :=
      Additive.toMul (C.realization.datumIso.val.weightEquiv y)
    have hχ : s.torus.inv ≫ χ (e.val.weightEquiv.symm x) = χ x := by
      have h := markedDiagramCharacter C hQ a (e.val.weightEquiv.symm x)
      change s.torus.inv ≫ χ (e.val.weightEquiv.symm x) = χ (e.val.weightEquiv (e.val.weightEquiv.symm x)) at h
      rwa [LinearEquiv.apply_symm_apply] at h
    have hχ' : s.torus.hom ≫ χ x = χ (e.val.weightEquiv.symm x) := by
      rw [← hχ, Iso.hom_inv_id_assoc]
    have he := characterValue_composition (χ x) s.torus.hom R t
    change characterValue (s.torus.hom ≫ χ x) R t =
      characterValue (χ x) R (t ≫ s.torus.hom.hom.hom) at he
    rw [← hu R w x, hw]
    change characterValue (χ x) R _ = _
    rw [← he, hχ']
    exact hv _
  rw [ht]
  exact hi R (v.comp m)

end MarkedDiagramPoints

section SimpleWallGeneration

open Specs.IntegralSemisimpleModel
open Specs.ExceptionalMarkedRootDescent
open Specs.SimpleRoots (wordProduct)
open LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent (integralWeylWordTransport)
open private exists_word perm_mul perm_reflection from LinearAlgebraicGroups.RootData.SimpleRoots
open private exists_regular_functional from LinearAlgebraicGroups.Classification.NormalizerComparison

private theorem markedRoots_of_simpleWallAgreement {D : Pinning.BasedRootDatum.{u}} (M : Model D)
    (R : IntegralAlgebra.{u}) {H : Type u} [Group H] (f g : IntegralPoints M.group R →* H)
    (hr : ∀ i : D.base.support, ∀ z : R, f (markedRootPoint M.toIntegralMarking R i z) =
      g (markedRootPoint M.toIntegralMarking R i z))
    (hn : ∀ i : D.base.support, f (markedWall M.toIntegralMarking R i 1) =
      g (markedWall M.toIntegralMarking R i 1)) :
    ∀ i z, f (markedRootPoint M.toIntegralMarking R i z) =
      g (markedRootPoint M.toIntegralMarking R i z) := by
  classical
  letI := D.finiteRoots
  letI := D.freeX
  letI := D.finiteX
  letI := D.reduced
  let P := D.datum
  obtain ⟨q, hq, hp⟩ := exists_regular_functional P D.base
  obtain ⟨b, hb⟩ := RootData.SimpleRoots.baseFor P q hq
  have hbase (i : D.I) : i ∈ b.support ↔ i ∈ D.base.support := by
    rw [hb.simple_iff, simpleRoot_iff_indecomposable D]
    simp only [Specs.SimpleRoots.positive, Set.mem_ofPred_eq, ← hp, P]
  intro i z
  obtain ⟨w, a, ha⟩ := hb.orbit i
  obtain ⟨l, hl⟩ := exists_word P b hb.generates w
  let ql := l.map Subtype.val
  have hperm (u : List b.support) (i : D.I) :
      weylWordPerm (u.map Subtype.val) i = P.weylGroupToPerm (wordProduct P b u) i := by
    induction u generalizing i with
    | nil => simp [weylWordPerm, wordProduct]
    | cons j u ih =>
      change P.reflectionPerm j.val (weylWordPerm (u.map Subtype.val) i) =
        P.weylGroupToPerm (RootPairing.weylGroup.ofIdx P j.val * wordProduct P b u) i
      rw [perm_mul, perm_reflection, ih]
  have hqi : weylWordPerm ql a.val = i := (hperm l a.val).trans (hl.symm ▸ ha)
  have hw (u : List b.support) :
      f (markedWeylWord M.toIntegralMarking R (u.map Subtype.val)) =
      g (markedWeylWord M.toIntegralMarking R (u.map Subtype.val)) := by
    induction u with
    | nil => simp [markedWeylWord]
    | cons j u ih =>
      simp only [List.map_cons, markedWeylWord, List.prod_cons, map_mul]
      exact congrArg₂ (· * ·) (hn ⟨j.val, (hbase j.val).mp j.property⟩) ih
  obtain ⟨c, hc⟩ := integralWeylWordTransport M ql a.val
  let v := Units.map (algebraMap Integers.{u} R).toMonoidHom c
  have ez : algebraMap Integers.{u} R (c : Integers.{u}) * ((↑v⁻¹ : R) * z) = z := by
    change (↑v : R) * ((↑v⁻¹ : R) * z) = z
    rw [← mul_assoc, Units.mul_inv, one_mul]
  have e := hc R ((↑v⁻¹ : R) * z)
  rw [hqi, ez] at e
  rw [← e, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hw l,
    hr ⟨a.val, (hbase a.val).mp a.property⟩]

end SimpleWallGeneration

section MarkedHomExt

open CategoryTheory.Limits
open Opposite

open Specs.IntegralSemisimpleModel
open Specs.ExceptionalMarkedRootDescent
open Specs.AbstractPairing (Root)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.OrderedRootProducts (Enumerates rootCellMap rootProduct product)
open _root_.LinearAlgebraicGroups.CocharacterDynamics (oppositeCocharacter)
open Specs.RootGroups (rootPoint)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open private scheme_hom_eq_of_schematicallyDominant product_affine from
  LinearAlgebraicGroups.Classification.PinnedUniqueness
open private integral_reductive from LinearAlgebraicGroups.Classification.CellHomomorphism
open private affine_tensor affinePoint_ext from LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
open private rootPoint_surjective from LinearAlgebraicGroups.RootData.OrderedRootProducts
open private rootPoint_comp from LinearAlgebraicGroups.RootData.RootGroups
open private fibrePointEquiv fibrePointEquiv_apply markedFibrePoint_root from
  LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent

attribute [local instance] integerAlgebra

variable {k : Type u} [Field k]
  {D : Pinning.BasedRootDatum.{u}} {M : Model D}

set_option backward.isDefEq.respectTransparency false in
private theorem markedHom_ext (C : MarkedFibre M k) {H : AffineAlgebraicGroup k}
    (f g : C.realization.pinned.pair.G.val ⟶ H.val)
    (hT : ∀ (R : TestAlgebra k) (t : GroupPoints C.realization.pinned.pair.T.group R),
      (t ≫ C.realization.pinned.pair.T.inclusion.hom.hom) ≫ f.hom.hom =
      (t ≫ C.realization.pinned.pair.T.inclusion.hom.hom) ≫ g.hom.hom)
    (hR : ∀ (R : TestAlgebra k) (i : D.I) (z : R),
      rootPoint (C.rootMap i) R z ≫ f.hom.hom = rootPoint (C.rootMap i) R z ≫ g.hom.hom) :
    f = g := by
  classical
  let P := C.realization.pinned
  let T := P.pair.T
  let G := P.pair.G
  obtain ⟨c, _, hc, _, _⟩ :=
    (RootData.BorelsAndChambers.borelsThroughT G P.pair.reductive T P.pair.split P.pair.maximal).1
      P.pair.B P.pair.borel P.pair.containsTorus
  letI : Finite (Root T) := (RootData.OrderedRootProducts.contractingProduct G P.pair.reductive T
    P.pair.split P.pair.maximal).1
  letI := Fintype.ofFinite (Root T)
  let pos := (Specs.BorelsAndChambers.positiveRoots T c).toFinset.toList
  let neg := (Specs.BorelsAndChambers.positiveRoots T (oppositeCocharacter c)).toFinset.toList
  have hpos : Enumerates pos (Specs.BorelsAndChambers.positiveRoots T c) :=
    ⟨Finset.nodup_toList _, by simp [pos]⟩
  have hneg : Enumerates neg (Specs.BorelsAndChambers.positiveRoots T (oppositeCocharacter c)) :=
    ⟨Finset.nodup_toList _, by simp [neg]⟩
  let j := rootCellMap T P.roots neg pos
  let X (α : Root T) := (P.roots α).val.group.X
  have haU (α : Root T) : IsAffine (X α).left := (closedSubgroupAlgebraicGroup (P.roots α).val).property.1
  letI : IsAffine (product X neg).left := product_affine X haU neg
  letI : IsAffine (product X pos).left := product_affine X haU pos
  letI : IsAffine T.group.X.left := (closedSubgroupAlgebraicGroup T).property.1
  letI : IsAffine (T.group.X ⊗ product X pos).left := affine_tensor inferInstance inferInstance
  have ha : IsAffine (product X neg ⊗ (T.group.X ⊗ product X pos)).left :=
    affine_tensor inferInstance inferInstance
  letI : IsOpenImmersion j.left :=
    RootData.OrderedRootProducts.regularRootCell G P.pair.reductive T P.pair.split P.pair.maximal
      c hc P.roots _ _ hneg hpos
  letI : IsIntegral G.val.X.left := integral_reductive G P.pair.reductive
  have hpoint (l : List (Root T)) : Nonempty (𝟙_ (SchemeOver k) ⟶ product X l) := by
    induction l with
    | nil => exact ⟨𝟙 _⟩
    | cons α l ih => exact ⟨lift η[(P.roots α).val.group.X] (Classical.choice ih)⟩
  let point := lift (Classical.choice (hpoint neg))
    (lift η[T.group.X] (Classical.choice (hpoint pos)))
  letI : Nonempty (product X neg ⊗ (T.group.X ⊗ product X pos)).left :=
    ⟨point.left (IsLocalRing.closedPoint k)⟩
  letI : IsDominant j.left := ⟨j.left.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  letI := IsSchemeTheoreticallyDominant.of_isDominant j.left
  letI := ha
  letI := G.property.1
  letI := H.property.1
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply scheme_hom_eq_of_schematicallyDominant (i := j.left)
  change (j ≫ f.hom.hom).left = (j ≫ g.hom.hom).left
  apply congrArg Over.Hom.left
  apply affinePoint_ext ha
  intro R y
  have hroot (α : Root T) (u : GroupPoints (P.roots α).val.group R) :
      (u ≫ (P.roots α).val.inclusion.hom.hom) ≫ f.hom.hom =
      (u ≫ (P.roots α).val.inclusion.hom.hom) ≫ g.hom.hom := by
    obtain ⟨i, rfl⟩ := C.realization.datumIso.val.indexEquiv.surjective α
    obtain ⟨z, rfl⟩ := rootPoint_surjective (C.coordinate i).val R u
    have h := hR R i z
    rwa [MarkedFibre.rootMap, rootPoint_comp] at h
  have hprod (l : List (Root T)) (u : (testSpec k).obj (op R) ⟶ product X l) :
      (u ≫ rootProduct P.roots l) ≫ f.hom.hom =
      (u ≫ rootProduct P.roots l) ≫ g.hom.hom := by
    induction l with
    | nil => simp only [OrderedRootProducts.rootProduct, MonObj.comp_one, MonObj.one_comp]
    | cons α l ih =>
      change (u ≫ ((fst _ _ ≫ (P.roots α).val.inclusion.hom.hom) *
        (snd _ _ ≫ rootProduct P.roots l))) ≫ f.hom.hom = _
      change _ = (u ≫ ((fst _ _ ≫ (P.roots α).val.inclusion.hom.hom) *
        (snd _ _ ≫ rootProduct P.roots l))) ≫ g.hom.hom
      simp only [MonObj.comp_mul, MonObj.mul_comp, ← Category.assoc, hroot, ih]
  have ht (u : GroupPoints T.group R) :
      (u ≫ T.inclusion.hom.hom) ≫ f.hom.hom =
      (u ≫ T.inclusion.hom.hom) ≫ g.hom.hom := hT R u
  simp only [j, rootCellMap, ← Category.assoc, MonObj.comp_mul, MonObj.mul_comp, ht, hprod]

end MarkedHomExt

section CentralEquivariance

open Opposite

open Specs.IntegralSemisimpleModel
open Specs.ExceptionalMarkedRootDescent
open Specs.AdjointRepresentation (GroupPoints)
open Specs.RootGroups (rootPoint)
open Specs.ExceptionalValuedTorusNormalizer (markedDiagramEquiv simplePermutation)
open Specs.CharacterPairing (characterValue)
open Specs.IntegralRootRelations (upper)
open LinearAlgebraicGroups.Arithmetic.ExceptionalValuedTorusNormalizer
  (markedFibreTorusCoordinates markedPinnedDiagramAction)
open LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
  (pinnedSimpleRankOneEquivariance)
open private fibrePointEquiv fibrePointEquiv_apply markedFibrePoint_root from
  LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent

attribute [local instance] integerAlgebra

variable {k : Type u} [Field k]
  {D E : Pinning.BasedRootDatum.{u}} {M : Model D} {A : Model E}

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
private theorem centralCover_diagramEquivariant (c : MarkedCentralCover M A) (hE : E.datum.rootSpan ℤ = ⊤)
    (C : MarkedFibre M k) (C' : MarkedFibre A k)
    {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
    {l' : Aut C'.realization.attached.toBased ≃* Aut C'.realization.pinned}
    {Q : AutomorphismSequence.AdjointQuotient C.realization.pinned.pair.G}
    {Q' : AutomorphismSequence.AdjointQuotient C'.realization.pinned.pair.G}
    (hQ : AutomorphismSequence.SplitSequence C.realization.pinned C.realization.attached l Q)
    (hQ' : AutomorphismSequence.SplitSequence C'.realization.pinned C'.realization.attached l' Q')
    (a : Aut C.realization.attached.toBased) (a' : Aut C'.realization.attached.toBased) :
    let e := (markedDiagramEquiv C.realization a).asIso.hom
    let e' := (markedDiagramEquiv C'.realization a').asIso.hom
    let s := (l a).asIso.hom
    let s' := (l' a').asIso.hom
    let f := C.groupIso.inv ≫ (fibre k).map c.map ≫ C'.groupIso.hom
    (∀ i, c.rootEquiv (e.val.indexEquiv i) = e'.val.indexEquiv (c.rootEquiv i)) →
    f ≫ s'.group.hom = s.group.hom ≫ f := by
  intro e e' s s' f hE'
  apply markedHom_ext C
  · intro R t
    let S := (integralTestAlgebra k).obj R
    let J := fibrePointEquiv C' R
    let T := C.realization.pinned.pair.T
    let U := C'.realization.pinned.pair.T
    let χ := c.pullCharacter.toAddMonoidHom.toMultiplicative
    let m := e.val.weightEquiv.symm.toLinearMap.toAddMonoidHom.toMultiplicative
    let m' := e'.val.weightEquiv.symm.toLinearMap.toAddMonoidHom.toMultiplicative
    obtain ⟨x, hx, hxi⟩ := markedFibreTorusCoordinates D M C.realization C.groupIso C.torusIso C.torus_comm C.torus_eval
    obtain ⟨y, hy, hyi⟩ := markedFibreTorusCoordinates E A C'.realization C'.groupIso C'.torusIso C'.torus_comm C'.torus_eval
    obtain ⟨v, rfl⟩ := (x R).surjective t
    have hxt : ((x R v) ≫ T.inclusion.hom.hom) ≫ f.hom.hom =
        (y R (v.comp χ)) ≫ U.inclusion.hom.hom := by
      apply J.injective
      change markedFibrePoint C' R _ = markedFibrePoint C' R _
      rw [markedFibrePoint_natural c C C' R]
      have hxv : markedFibrePoint C R ((x R v) ≫ T.inclusion.hom.hom) =
          torusPoint D S v ≫ M.torus.hom.hom := by
        unfold markedFibrePoint
        rw [Category.assoc]
        exact hxi R v
      have hyv : markedFibrePoint C' R ((y R (v.comp χ)) ≫ U.inclusion.hom.hom) =
          torusPoint E S (v.comp χ) ≫ A.torus.hom.hom := by
        unfold markedFibrePoint
        rw [Category.assoc]
        exact hyi R (v.comp χ)
      rw [hxv, hyv, c.marking.2.2]
    have hcomp : χ.comp m' = m.comp χ := by
      apply MonoidHom.ext
      intro i
      apply Multiplicative.toAdd.injective
      change c.pullCharacter (e'.val.weightEquiv.symm i.toAdd) =
        e.val.weightEquiv.symm (c.pullCharacter i.toAdd)
      apply e.val.weightEquiv.injective
      rw [LinearEquiv.apply_symm_apply]
      have hh := congrFun (congrArg DFunLike.coe
        (characterPullback_commutes_diagram c hE e e' hE')) (e'.val.weightEquiv.symm i.toAdd)
      change c.pullCharacter (e'.val.weightEquiv (e'.val.weightEquiv.symm i.toAdd)) = _ at hh
      rw [LinearEquiv.apply_symm_apply] at hh
      exact hh.symm
    have hT : ((x R v) ≫ T.inclusion.hom.hom) ≫ s.group.hom.hom.hom =
        ((x R v) ≫ s.torus.hom.hom.hom) ≫ T.inclusion.hom.hom := by
      have h := congrArg (fun u => (x R v) ≫ u.hom.hom) s.torus_comm
      simpa only [Grp.comp_hom_hom, ← Category.assoc] using h
    have hU : ((y R (v.comp χ)) ≫ U.inclusion.hom.hom) ≫ s'.group.hom.hom.hom =
        ((y R (v.comp χ)) ≫ s'.torus.hom.hom.hom) ≫ U.inclusion.hom.hom := by
      have h := congrArg (fun u => (y R (v.comp χ)) ≫ u.hom.hom) s'.torus_comm
      simpa only [Grp.comp_hom_hom, ← Category.assoc] using h
    have hL := pinnedTorusValues C' hQ' a' R (y R (v.comp χ)) (v.comp χ) (hy R _)
    have hR := pinnedTorusValues C hQ a R (x R v) v (hx R v)
    change markedFibrePoint C' R (((y R (v.comp χ)) ≫ s'.torus.hom.hom.hom) ≫ U.inclusion.hom.hom) = _ at hL
    change markedFibrePoint C R (((x R v) ≫ s.torus.hom.hom.hom) ≫ T.inclusion.hom.hom) = _ at hR
    have hl₀ : ((x R v) ≫ T.inclusion.hom.hom) ≫ (f ≫ s'.group.hom).hom.hom =
        (((x R v) ≫ T.inclusion.hom.hom) ≫ f.hom.hom) ≫ s'.group.hom.hom.hom :=
      (Category.assoc _ _ _).symm
    have hr₀ : ((x R v) ≫ T.inclusion.hom.hom) ≫ (s.group.hom ≫ f).hom.hom =
        (((x R v) ≫ T.inclusion.hom.hom) ≫ s.group.hom.hom.hom) ≫ f.hom.hom :=
      (Category.assoc _ _ _).symm
    change ((x R v) ≫ T.inclusion.hom.hom) ≫ (f ≫ s'.group.hom).hom.hom = _
    rw [hl₀, hr₀, hxt, hT, hU]
    apply J.injective
    change markedFibrePoint C' R _ = markedFibrePoint C' R _
    rw [hL, markedFibrePoint_natural c C C' R, hR, c.marking.2.2]
    simp only [MonoidHom.comp_assoc]
    change torusPoint E S (v.comp (χ.comp m')) ≫ A.torus.hom.hom =
      torusPoint E S (v.comp (m.comp χ)) ≫ A.torus.hom.hom
    rw [hcomp]
  · intro R i z
    let S := (integralTestAlgebra k).obj R
    let X := (testSpec k).obj (op R)
    let u := fibrePointEquiv C R
    let v := fibrePointEquiv C' R
    let p := v.toMonoidHom.comp ((pointHom (f ≫ s'.group.hom) X).comp u.symm.toMonoidHom)
    let q := v.toMonoidHom.comp ((pointHom (s.group.hom ≫ f) X).comp u.symm.toMonoidHom)
    have hsimple (j : D.base.support) (m : Matrix.SpecialLinearGroup (Fin 2) S)
        (h₁ : integralPointHom c.map S ((M.rankOne j).app S m) = (A.rankOne (c.rootEquiv j)).app S m)
        (h₂ : integralPointHom c.map S ((M.rankOne (simplePermutation D e j)).app S m) =
          (A.rankOne (c.rootEquiv (simplePermutation D e j))).app S m) :
        p ((M.rankOne j).app S m) = q ((M.rankOne j).app S m) := by
      let j' : E.base.support := ⟨c.rootEquiv j, (cover_simple c j).mp j.property⟩
      let j₁ := simplePermutation D e j
      let j₁' := simplePermutation E e' j'
      have hj : c.rootEquiv j₁ = j₁'.val := hE' j.val
      let g := u.symm ((M.rankOne j).app S m)
      have hg : markedFibrePoint C R g = (M.rankOne j).app S m := u.apply_symm_apply _
      have hg' : markedFibrePoint C' R (g ≫ f.hom.hom) = (A.rankOne j').app S m :=
        (markedFibrePoint_natural c C C' R g).trans (hg ▸ h₁)
      have hsa := (markedPinnedDiagramAction C.realization hQ a).1 j
      have hsa' := (markedPinnedDiagramAction C'.realization hQ' a').1 j'
      have hal := pinnedSimpleRankOneEquivariance C' (l' a') j' j₁'
        (by exact hsa') R m (g ≫ f.hom.hom) hg'
      have har := pinnedSimpleRankOneEquivariance C (l a) j j₁
        (by exact hsa) R m g hg
      change markedFibrePoint C' R (g ≫ (f ≫ s'.group.hom).hom.hom) =
        markedFibrePoint C' R (g ≫ (s.group.hom ≫ f).hom.hom)
      have hl₀ : g ≫ (f ≫ s'.group.hom).hom.hom = (g ≫ f.hom.hom) ≫ s'.group.hom.hom.hom :=
        (Category.assoc _ _ _).symm
      have hr₀ : g ≫ (s.group.hom ≫ f).hom.hom = (g ≫ s.group.hom.hom.hom) ≫ f.hom.hom :=
        (Category.assoc _ _ _).symm
      change markedFibrePoint C' R ((g ≫ f.hom.hom) ≫ s'.group.hom.hom.hom) = _ at hal
      change markedFibrePoint C R (g ≫ s.group.hom.hom.hom) = _ at har
      rw [hl₀, hr₀, hal, markedFibrePoint_natural c C C' R, har]
      rw [h₂, hj]
    obtain ⟨_, hword⟩ := markedRankOneMapCompatibility c.map c.rootEquiv
      c.pullCharacter.toAddMonoidHom.toMultiplicative c.marking (fun j => c.reflections j j)
    have hw (j : D.I) := hword S [j]
    have hr (j : D.base.support) (t : S) :
        p (markedRootPoint M.toIntegralMarking S j t) = q (markedRootPoint M.toIntegralMarking S j t) := by
      have hu : (M.rankOne j).app S (upper t) = markedRootPoint M.toIntegralMarking S j t :=
        M.rankOneUpper j S t
      rw [← hu]
      apply hsimple j (upper t)
      · rw [M.rankOneUpper, A.rankOneUpper]
        exact c.marking.2.1 S j t
      · rw [M.rankOneUpper, A.rankOneUpper]
        exact c.marking.2.1 S (simplePermutation D e j) t
    have hn (j : D.base.support) :
        p (markedWall M.toIntegralMarking S j 1) = q (markedWall M.toIntegralMarking S j 1) := by
      apply hsimple j (wallMatrix 1)
      · simpa only [markedWeylWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
          mul_one, markedWall] using hw j
      · simpa only [markedWeylWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
          mul_one, markedWall] using hw (simplePermutation D e j)
    have h := markedRoots_of_simpleWallAgreement M S p q hr hn i z
    have hi : u (rootPoint (C.rootMap i) R z) = markedRootPoint M.toIntegralMarking S i z :=
      markedFibrePoint_root C R i z
    rw [← hi] at h
    apply v.injective
    change v (u.symm (u (rootPoint (C.rootMap i) R z)) ≫ (f ≫ s'.group.hom).hom.hom) =
      v (u.symm (u (rootPoint (C.rootMap i) R z)) ≫ (s.group.hom ≫ f).hom.hom) at h
    rw [u.symm_apply_apply] at h
    exact h

end CentralEquivariance

section PinnedMapDescent

open Opposite
open scoped TensorProduct
open _root_.LinearAlgebraicGroups.Descent (SemilinearAction HopfDescentDatum)

open _root_.LinearAlgebraicGroups.Specs.AdjointCocharacters (coordinateHopfIso coordinateHopfMap)
open AdjointBorelCohomology (PinnedTwist)
open ExceptionalMarkedRootDescent (pinnedOperator pinnedAlgebraPointMap extendAlgebraPoint pinnedSchemePoint)
open AutomorphismSequence (forgetPinning)
open private standard standardAct baseHom_equivariant descend_standard_hom extendedHom_comp
  from LinearAlgebraicGroups.Descent.Forms
open private coordinateHopfMap_comp from LinearAlgebraicGroups.Descent.AdjointBorelCohomology
open private coordinatePresentationMap from LinearAlgebraicGroups.Descent.AdjointCocharacters
open private specGroupMap_comp specGroupMap_injective from LinearAlgebraicGroups.Affine.ClosedSubgroups

set_option backward.isDefEq.respectTransparency false in
private theorem descentThroughPinnedComparison
    {k K : Type u} [Field k] [Field K] [Algebra k K] [IsGalois k K]
    {L L' : RootGroups.AdditiveLine k} {P : Pinning.PinnedGroup L} {P' : Pinning.PinnedGroup L'}
    {D : Pinning.AttachedDatum P.pair} {E : Pinning.AttachedDatum P'.pair}
    {l : Aut D.toBased ≃* Aut P} {l' : Aut E.toBased ≃* Aut P'}
    {G G' : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val} {B' T' : ClosedSubgroup G'.val}
    (d : PinnedTwist K D l B T) (d' : PinnedTwist K E l' B' T')
    (f : P.pair.G.val ⟶ P'.pair.G.val)
    (hf : ∀ σ : Gal(K/k),
      f ≫ (Functor.mapAut P' (forgetPinning (A := L')) (l' (d'.outer σ))).asIso.inv =
        (Functor.mapAut P (forgetPinning (A := L)) (l (d.outer σ))).asIso.inv ≫ f) :
    ∃ p : G.val ⟶ G'.val,
      d'.groupIso.hom ≫ extendedHopfMap K (coordinateHopfMap (G := G) (H := G') p) =
        extendedHopfMap K (coordinateHopfMap (G := P.pair.G) (H := P'.pair.G) f) ≫ d.groupIso.hom := by
  let q := coordinateHopfMap (G := P.pair.G) (H := P'.pair.G) f
  let e := extendedHopfMap K q
  have he (σ : Gal(K/k)) (x : extendedHopf K (Specs.AdjointCocharacters.coordinateHopf P'.pair.G)) :
      e.hom (pinnedOperator d' σ x) = pinnedOperator d σ (e.hom x) := by
    let a := (Functor.mapAut P (forgetPinning (A := L)) (l (d.outer σ))).asIso.inv
    let a' := (Functor.mapAut P' (forgetPinning (A := L')) (l' (d'.outer σ))).asIso.inv
    let b := extendedHopfMap K (coordinateHopfMap (G := P.pair.G) (H := P.pair.G) a)
    let b' := extendedHopfMap K (coordinateHopfMap (G := P'.pair.G) (H := P'.pair.G) a')
    have hb : b' ≫ e = e ≫ b := by
      dsimp only [b, b', e, q]
      rw [← extendedHom_comp, ← extendedHom_comp, ← coordinateHopfMap_comp, ← coordinateHopfMap_comp]
      exact congrArg (fun f => extendedHopfMap K (coordinateHopfMap (G := P.pair.G) (H := P'.pair.G) f)) (hf σ)
    let z := (standardAct K (Specs.AdjointCocharacters.coordinateHopf P'.pair.G)).act σ x
    have hcomp := ConcreteCategory.congr_hom hb z
    change e.hom (b'.hom z) = b.hom (e.hom z) at hcomp
    have hσ := baseHom_equivariant (K := K) q σ x
    change e.hom z = (standardAct K (Specs.AdjointCocharacters.coordinateHopf P.pair.G)).act σ (e.hom x) at hσ
    change e.hom (b'.hom z) = b.hom ((standardAct K (Specs.AdjointCocharacters.coordinateHopf P.pair.G)).act σ (e.hom x))
    exact hcomp.trans (congrArg b.hom hσ)
  let r := d'.groupIso.inv ≫ e ≫ d.groupIso.hom
  have hr : (standard K (Specs.AdjointCocharacters.coordinateHopf G')).Equivariant (standard K (Specs.AdjointCocharacters.coordinateHopf G)) r := by
    intro σ x
    obtain ⟨y, rfl⟩ := (ConcreteCategory.bijective_of_isIso d'.groupIso.hom).surjective x
    have hη := ConcreteCategory.congr_hom d'.groupIso.hom_inv_id y
    have hη' := ConcreteCategory.congr_hom d'.groupIso.hom_inv_id (pinnedOperator d' σ y)
    change d'.groupIso.inv.hom (d'.groupIso.hom.hom y) = y at hη
    change d'.groupIso.inv.hom (d'.groupIso.hom.hom (pinnedOperator d' σ y)) = pinnedOperator d' σ y at hη'
    change d.groupIso.hom.hom (e.hom (d'.groupIso.inv.hom
        ((SemilinearAction.scalarExtension (K := K) (Specs.AdjointCocharacters.coordinateHopf G')).act σ (d'.groupIso.hom.hom y)))) =
      (SemilinearAction.scalarExtension (K := K) (Specs.AdjointCocharacters.coordinateHopf G)).act σ
        (d.groupIso.hom.hom (e.hom (d'.groupIso.inv.hom (d'.groupIso.hom.hom y))))
    rw [show _ = d'.groupIso.hom.hom (pinnedOperator d' σ y) from d'.twistedAction σ y,
      hη', hη, he]
    exact (d.twistedAction σ (e.hom y)).symm
  obtain ⟨u, hu⟩ := descend_standard_hom r hr
  let p := (coordinateHopfIso G).inv ≫ specGroupMap u ≫ (coordinateHopfIso G').hom
  have hp : coordinateHopfMap (G := G) (H := G') p = u := by
    apply specGroupMap_injective
    rw [coordinatePresentationMap]
    simp [p]
  refine ⟨p, ?_⟩
  rw [hp, hu]
  simp [r, e, q]

end PinnedMapDescent

section PinnedGroundNaturality

open Opposite
open scoped TensorProduct

open _root_.LinearAlgebraicGroups.Specs.AdjointBorelCohomology (PinnedTwist)
open _root_.LinearAlgebraicGroups.Specs.AdjointCocharacters (coordinateHopfMap)

open _root_.LinearAlgebraicGroups.Specs.IntegralSemisimpleModel
open _root_.LinearAlgebraicGroups.Specs.ExceptionalMarkedRootDescent
open private coordinatePointEquiv_comp restrictExtended_comp from
  LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
open WithConv

attribute [local instance] integerAlgebra

set_option backward.isDefEq.respectTransparency false in
private theorem pinnedGroundPoint_natural
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {D E : Pinning.BasedRootDatum.{u}} {M : Model D} {A : Model E}
    (c : MarkedCentralCover M A) (C : MarkedFibre M k) (C' : MarkedFibre A k)
    {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
    {l' : Aut C'.realization.attached.toBased ≃* Aut C'.realization.pinned}
    {G G' : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val} {B' T' : ClosedSubgroup G'.val}
    (d : PinnedTwist K C.realization.attached l B T)
    (d' : PinnedTwist K C'.realization.attached l' B' T')
    (p : G.val ⟶ G'.val) :
    let f := C.groupIso.inv ≫ (fibre k).map c.map ≫ C'.groupIso.hom
    d'.groupIso.hom ≫ extendedHopfMap K (coordinateHopfMap (G := G) (H := G') p) =
      extendedHopfMap K (coordinateHopfMap
        (G := C.realization.pinned.pair.G) (H := C'.realization.pinned.pair.G) f) ≫ d.groupIso.hom →
    ∀ g : 𝟙_ (SchemeOver k) ⟶ G.val.X,
      pinnedGroundPoint C' d' (pointHom p (𝟙_ (SchemeOver k)) g) =
        integralPointHom c.map (CommAlgCat.of Integers.{u} K) (pinnedGroundPoint C d g) := by
  intro f h g
  let S := CommAlgCat.of k k
  let U := (extendedTestAlgebra k K).obj S
  let p₀ := pointHom p (𝟙_ (SchemeOver k))
  let π := coordinateHopfMap (G := G) (H := G') p
  let φ := coordinateHopfMap (G := C.realization.pinned.pair.G) (H := C'.realization.pinned.pair.G) f
  let a := groundHopfEquiv G g
  have ha : groundHopfEquiv G' (p₀ g) = toConv (a.ofConv.comp π.hom.toAlgHom) := by
    apply (coordinatePointEquiv G' S).injective
    rw [coordinatePointEquiv_comp (G := G) (H := G') p S a]
    have h1 : coordinatePointEquiv G' S (groundHopfEquiv G' (p₀ g)) =
        toUnit ((testSpec k).obj (op S)) ≫ p₀ g :=
      (coordinatePointEquiv G' S).apply_symm_apply _
    have h2 : coordinatePointEquiv G S a = toUnit ((testSpec k).obj (op S)) ≫ g :=
      (coordinatePointEquiv G S).apply_symm_apply _
    rw [h1, h2]
    exact (Category.assoc _ _ _).symm
  have hP : extendAlgebraPoint (K := K) (a.ofConv.comp π.hom.toAlgHom) =
      (extendAlgebraPoint a.ofConv).comp (extendedHopfMap K π).hom.toAlgHom := by
    apply Algebra.TensorProduct.ext_ring
    apply AlgHom.ext
    intro x
    change extendAlgebraPoint (K := K) (a.ofConv.comp π.hom.toAlgHom) (1 ⊗ₜ[k] x) =
      extendAlgebraPoint (K := K) a.ofConv (1 ⊗ₜ[k] π.hom x)
    simp only [extendAlgebraPoint, AlgHom.liftEquiv_tmul, AlgHom.comp_apply]
    rfl
  have hA : pinnedAlgebraPointMap d' (a.ofConv.comp π.hom.toAlgHom) =
      (pinnedAlgebraPointMap d a.ofConv).comp (extendedHopfMap K φ).hom.toAlgHom := by
    unfold pinnedAlgebraPointMap
    rw [hP]
    apply AlgHom.ext
    intro x
    exact congrArg (extendAlgebraPoint (K := K) a.ofConv)
      (ConcreteCategory.congr_hom h x)
  have hscheme : pinnedSchemePoint d' S (groundHopfEquiv G' (p₀ g)) =
      pinnedSchemePoint d S a ≫ f.hom.hom := by
    rw [ha]
    unfold pinnedSchemePoint
    rw [ofConv_toConv, hA, restrictExtended_comp (K := K) S φ]
    exact coordinatePointEquiv_comp (G := C.realization.pinned.pair.G)
      (H := C'.realization.pinned.pair.G) f U _
  have hmark (x : AdjointRepresentation.GroupPoints C.realization.pinned.pair.G.val U) :
      markedFibrePoint C' U (x ≫ f.hom.hom) =
        integralPointHom c.map ((quadraticIntegralAlgebra k K).obj S) (markedFibrePoint C U x) :=
    markedFibrePoint_natural c C C' U x
  change pinnedGroundPoint C' d' (p₀ g) = _
  rw [pinnedGroundPoint_apply, pinnedGroundPoint_apply, pinnedMarkedPoint, pinnedMarkedPoint,
    hscheme, hmark, integralPointHom_natural]

end PinnedGroundNaturality

section FieldDescent

open CategoryTheory.Limits
open Opposite

open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.CentralIsogenies (IsCentralIsogeny IsTorusRestriction)
open private baseChangeMapPullback baseChangeKernelSquare from LinearAlgebraicGroups.Affine.Components
open private descendClosedFactor from LinearAlgebraicGroups.Classification.CentralIsogenies
open private subgroupFactor from LinearAlgebraicGroups.Reductive.WeylScheme
open private schemeKernel_exists schemeKernel_sections from LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private centralizes_iff from LinearAlgebraicGroups.Affine.Stabilizers

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

private theorem fieldProjectionEpi (X : SchemeOver k) :
    Epi (pullback.fst X.hom (fieldSpecMap k K)) :=
  Flat.epi_of_flat_of_surjective _

set_option backward.isDefEq.respectTransparency false in
private theorem fieldChangeProperty (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)]
    {G H G₀ H₀ : GroupScheme k} (f : G ⟶ H) (f₀ : G₀ ⟶ H₀)
    (a : (groupBaseChange k K).obj G ≅ (groupBaseChange k K).obj G₀)
    (b : (groupBaseChange k K).obj H ≅ (groupBaseChange k K).obj H₀)
    (h : a.hom ≫ (groupBaseChange k K).map f₀ = (groupBaseChange k K).map f ≫ b.hom)
    (hp : P f₀.hom.hom.left) : P f.hom.hom.left := by
  let F := groupBaseChange k K
  let U := Grp.forget (SchemeOver K) ⋙ Over.forget (Spec (CommRingCat.of K))
  let h' := congrArg U.map h
  simp only [Functor.map_comp] at h'
  haveI : P.RespectsIso := inferInstance
  have hp₀ : P (U.map (F.map f₀)) :=
    MorphismProperty.of_isPullback (baseChangeMapPullback (K := K) f₀.hom.hom).flip hp
  have hp₁ : P (U.map (F.map f)) := by
    rw [← MorphismProperty.cancel_right_of_respectsIso (P := P) (U.map (F.map f)) (U.map b.hom),
      ← h', MorphismProperty.cancel_left_of_respectsIso (P := P)]
    exact hp₀
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (P := P) (baseChangeMapPullback (K := K) f.hom.hom)
    (show (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme)
      (pullback.fst H.X.hom (fieldSpecMap k K)) from ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩) hp₁

set_option backward.isDefEq.respectTransparency false in
private theorem groupFactor_of_fieldChange
    {G H : GroupScheme k} (B : ClosedSubgroup H) (f : G ⟶ H) [IsAffine G.X.left]
    (a : (groupBaseChange k K).obj G ⟶ (groupBaseChange k K).obj B.group)
    (ha : a ≫ (groupBaseChange k K).map B.inclusion = (groupBaseChange k K).map f) :
    ∃ p : G ⟶ B.group, p ≫ B.inclusion = f := by
  let F := baseChange k K
  let j := B.inclusion.hom.hom
  let L := Over.map (fieldSpecMap k K)
  let adj := Over.mapPullbackAdj (fieldSpecMap k K)
  let p := adj.counit.app G.X
  let q := adj.counit.app B.group.X
  letI : IsClosedImmersion j.left := B.isClosedImmersion
  letI : Mono j := Over.mono_of_mono_left _
  letI : IsAffine ((Over.pullback (fieldSpecMap k K) ⋙ Over.map (fieldSpecMap k K)).obj G.X).left := inferInstanceAs
    (IsAffine (pullback G.X.hom (fieldSpecMap k K)))
  letI : Flat p.left := inferInstanceAs (Flat (pullback.fst G.X.hom (fieldSpecMap k K)))
  letI : Surjective p.left := inferInstanceAs (Surjective (pullback.fst G.X.hom (fieldSpecMap k K)))
  have h₀ : a.hom.hom ≫ F.map j = F.map f.hom.hom :=
    congrArg (fun v => v.hom.hom) ha
  let a₀ := L.map a.hom.hom ≫ q
  have hnat : L.map (F.map j) ≫ adj.counit.app H.X = q ≫ j := adj.counit.naturality j
  have h₁ : a₀ ≫ j = p ≫ f.hom.hom := by
    change (L.map a.hom.hom ≫ q) ≫ j = _
    rw [Category.assoc, ← hnat, ← Category.assoc, ← L.map_comp, h₀]
    exact adj.counit.naturality f.hom.hom
  have hex : ∃ z : G.X ⟶ B.group.X, z ≫ j = f.hom.hom :=
    descendClosedFactor (Y := G.X) (X := (Over.pullback (fieldSpecMap k K) ⋙ Over.map (fieldSpecMap k K)).obj G.X)
      p j f.hom.hom a₀ h₁
  obtain ⟨z, hz⟩ := hex
  exact subgroupFactor B f z hz

set_option backward.isDefEq.respectTransparency false in
private theorem centralizes_of_fieldChange {G Z : GroupScheme k} (i : Z ⟶ G)
    (h : Centralizes (𝟙 ((groupBaseChange k K).obj G)) ((groupBaseChange k K).map i).hom.hom) :
    Centralizes (𝟙 G) i.hom.hom := by
  let F := baseChange k K
  refine (centralizes_iff (𝟙 G) i.hom.hom).mpr (fun Y a b => ?_)
  have hc := (centralizes_iff _ _).mp h (F.obj Y) (F.map a) (F.map b)
  letI : GrpObj (F.obj G.X) := ((groupBaseChange k K).obj G).grp
  change Commute (F.map a ≫ F.map i.hom.hom)
      (F.map b ≫ 𝟙 (F.obj G.X)) at hc
  simp only [Category.comp_id, ← Functor.map_comp] at hc
  change Commute (a ≫ i.hom.hom) (b ≫ 𝟙 G.X)
  rw [Category.comp_id]
  change (a ≫ i.hom.hom) * b = b * (a ≫ i.hom.hom)
  have hf := hc.eq
  change F.map (a ≫ i.hom.hom) * F.map b = F.map b * F.map (a ≫ i.hom.hom) at hf
  rw [← F.map_mul, ← F.map_mul] at hf
  letI := fieldProjectionEpi (K := K) Y
  apply Over.OverMorphism.ext
  apply (cancel_epi (pullback.fst Y.hom (fieldSpecMap k K))).mp
  rw [← (baseChangeMapPullback (K := K) ((a ≫ i.hom.hom) * b)).w,
    ← (baseChangeMapPullback (K := K) (b * (a ≫ i.hom.hom))).w]
  exact congrArg (fun f => f.left ≫ pullback.fst G.X.hom (fieldSpecMap k K)) hf

end FieldDescent

section PinnedGeometry

open CategoryTheory.Limits
open Opposite

open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.CentralIsogenies (IsCentralIsogeny IsTorusRestriction)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.AdjointCocharacters (coordinateHopf)
open private baseChangeKernelSquare from LinearAlgebraicGroups.Affine.Components
open private centralizes_iff centralizes_baseChange from LinearAlgebraicGroups.Affine.Stabilizers
open private schemeKernel_exists schemeKernel_sections from LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private subgroupFactor from LinearAlgebraicGroups.Reductive.WeylScheme
open private centralizesIso extendedCoordinateIso_comm extendedCoordinateIso from
  LinearAlgebraicGroups.Descent.AdjointBorelCohomology

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

set_option backward.isDefEq.respectTransparency false in
private theorem centralizes_after_fieldChange {G Z : GroupScheme k} (i : Z ⟶ G)
    (h : Centralizes (𝟙 G) i.hom.hom) :
    Centralizes (𝟙 ((groupBaseChange k K).obj G)) ((groupBaseChange k K).map i).hom.hom := by
  let F := baseChange k K
  let j := (groupBaseChange k K).map i
  let adj := Over.mapPullbackAdj (fieldSpecMap k K)
  have ha : (adj.homEquiv (F.obj Z.X) G.X).symm j.hom.hom =
      (adj.homEquiv (F.obj Z.X) Z.X).symm (𝟙 (F.obj Z.X)) ≫ i.hom.hom := by
    rw [← adj.homEquiv_naturality_right_symm (𝟙 (F.obj Z.X)) i.hom.hom]
    congr 1
  have hc := (centralizes_baseChange K (𝟙 G) j.hom.hom)
  rw [(groupBaseChange k K).map_id G] at hc
  apply hc.mpr
  change Centralizes (𝟙 G) ((adj.homEquiv (F.obj Z.X) G.X).symm j.hom.hom)
  rw [ha]
  refine (centralizes_iff _ _).mpr (fun Y a b => ?_)
  simpa only [Category.assoc] using (centralizes_iff _ _).mp h Y
    (a ≫ (adj.homEquiv (F.obj Z.X) Z.X).symm (𝟙 (F.obj Z.X))) b

set_option backward.isDefEq.respectTransparency false in
private theorem restriction_of_comparison
    {G H G₀ H₀ : AffineAlgebraicGroup k} {S : ClosedSubgroup G.val} {T : ClosedSubgroup H.val}
    {S₀ : ClosedSubgroup G₀.val} {T₀ : ClosedSubgroup H₀.val}
    (f : G.val ⟶ H.val) (f₀ : G₀.val ⟶ H₀.val) (r₀ : S₀.group ⟶ T₀.group)
    (hr₀ : r₀ ≫ T₀.inclusion = S₀.inclusion ≫ f₀)
    (a : (groupBaseChange k K).obj G.val ≅ (groupBaseChange k K).obj G₀.val)
    (b : (groupBaseChange k K).obj H.val ≅ (groupBaseChange k K).obj H₀.val)
    (s : (groupBaseChange k K).obj S.group ≅ (groupBaseChange k K).obj S₀.group)
    (t : (groupBaseChange k K).obj T.group ≅ (groupBaseChange k K).obj T₀.group)
    (h : a.hom ≫ (groupBaseChange k K).map f₀ = (groupBaseChange k K).map f ≫ b.hom)
    (hs : s.hom ≫ (groupBaseChange k K).map S₀.inclusion = (groupBaseChange k K).map S.inclusion ≫ a.hom)
    (ht : t.hom ≫ (groupBaseChange k K).map T₀.inclusion = (groupBaseChange k K).map T.inclusion ≫ b.hom) :
    ∃ r : S.group ⟶ T.group, r ≫ T.inclusion = S.inclusion ≫ f ∧
      s.hom ≫ (groupBaseChange k K).map r₀ = (groupBaseChange k K).map r ≫ t.hom := by
  let F := groupBaseChange k K
  let x := s.hom ≫ F.map r₀ ≫ t.inv
  have hx' : x ≫ F.map T.inclusion = F.map (S.inclusion ≫ f) := by
    apply (cancel_mono b.hom).mp
    simp only [x, Category.assoc, Functor.map_comp]
    rw [← ht, Iso.inv_hom_id_assoc, ← F.map_comp, hr₀, F.map_comp, ← Category.assoc s.hom, hs,
      Category.assoc, h]
  letI : IsAffine S.group.X.left := (closedSubgroupAlgebraicGroup S).property.1
  obtain ⟨r, hr⟩ := groupFactor_of_fieldChange T (S.inclusion ≫ f) x hx'
  have htmono : Mono (F.map T.inclusion) := by
    letI : IsClosedImmersion (F.map T.inclusion).hom.hom.left :=
      LinearAlgebraicGroups.baseChangeClosedSubgroup k K T.inclusion T.isClosedImmersion
    have : Mono (F.map T.inclusion).hom.hom := Over.mono_of_mono_left _
    exact (Grp.forget (SchemeOver K)).mono_of_mono_map this
  have he : F.map r = x := (cancel_mono (F.map T.inclusion)).mp (by rw [← F.map_comp, hr, hx'])
  refine ⟨r, hr, ?_⟩
  rw [he]
  simp [x]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem kernel_of_comparison
    {G H G₀ H₀ : AffineAlgebraicGroup k} {T : ClosedSubgroup G.val} {T₀ : ClosedSubgroup G₀.val}
    (f : G.val ⟶ H.val) (f₀ : G₀.val ⟶ H₀.val)
    (a : (groupBaseChange k K).obj G.val ≅ (groupBaseChange k K).obj G₀.val)
    (b : (groupBaseChange k K).obj H.val ≅ (groupBaseChange k K).obj H₀.val)
    (t : (groupBaseChange k K).obj T.group ≅ (groupBaseChange k K).obj T₀.group)
    (h : a.hom ≫ (groupBaseChange k K).map f₀ = (groupBaseChange k K).map f ≫ b.hom)
    (ht : t.hom ≫ (groupBaseChange k K).map T₀.inclusion = (groupBaseChange k K).map T.inclusion ≫ a.hom)
    (Z₀ : ClosedSubgroup G₀.val) (hZ₀ : IsSchemeKernel f₀ Z₀) (hT₀ : IsSubgroupOf Z₀ T₀)
    (hc₀ : Centralizes (𝟙 G₀.val) Z₀.inclusion.hom.hom) :
    ∃ Z : ClosedSubgroup G.val, IsSchemeKernel f Z ∧
      IsSubgroupOf Z T ∧ Centralizes (𝟙 G.val) Z.inclusion.hom.hom := by
  let F := groupBaseChange k K
  letI : IsAffine H.val.X.left := H.property.1
  obtain ⟨Z, hZ⟩ := schemeKernel_exists f
  let ZK : ClosedSubgroup (F.obj G.val) := ⟨_, F.map Z.inclusion,
    LinearAlgebraicGroups.baseChangeClosedSubgroup k K Z.inclusion Z.isClosedImmersion⟩
  let Z₀K : ClosedSubgroup (F.obj G₀.val) := ⟨_, F.map Z₀.inclusion,
    LinearAlgebraicGroups.baseChangeClosedSubgroup k K Z₀.inclusion Z₀.isClosedImmersion⟩
  have hZK : IsSchemeKernel (F.map f) ZK :=
    baseChangeKernelSquare (K := K) f Z.inclusion hZ
  have hZ₀K : IsSchemeKernel (F.map f₀) Z₀K :=
    baseChangeKernelSquare (K := K) f₀ Z₀.inclusion hZ₀
  let n := F.map Z.inclusion ≫ a.hom
  have hn : n.hom.hom ≫ (F.map f₀).hom.hom = 1 := by
    have hx := congrArg (fun v => v.hom.hom) (show n ≫ F.map f₀ = F.map Z.inclusion ≫ F.map f ≫ b.hom by
      simpa only [n, Category.assoc] using
        congrArg (F.map Z.inclusion ≫ ·) h)
    simp only [Grp.comp_hom_hom] at hx
    have hZK' : (F.map Z.inclusion).hom.hom ≫ (F.map f).hom.hom = 1 := hZK.w
    rw [hx, ← Category.assoc, hZK',
      MonObj.one_comp]
  obtain ⟨q, hq⟩ := (schemeKernel_sections hZ₀K n.hom.hom).mpr hn
  obtain ⟨z, hz⟩ := subgroupFactor Z₀K n q hq
  have hzn : z ≫ F.map Z₀.inclusion = n := hz
  obtain ⟨v, hv⟩ := hT₀
  let m := z ≫ F.map v ≫ t.inv
  have hm : m ≫ F.map T.inclusion = F.map Z.inclusion := by
    apply (cancel_mono a.hom).mp
    simp only [m, Category.assoc]
    rw [← ht, Iso.inv_hom_id_assoc, ← F.map_comp, hv, hzn]
  letI : IsAffine Z.group.X.left := (closedSubgroupAlgebraicGroup Z).property.1
  obtain ⟨j, hj⟩ := groupFactor_of_fieldChange T Z.inclusion m hm
  refine ⟨Z, hZ, ⟨j, hj⟩, centralizes_of_fieldChange (K := K) Z.inclusion ?_⟩
  apply (centralizesIso a (F.map Z.inclusion).hom.hom).mpr
  change Centralizes (𝟙 (F.obj G₀.val)) n.hom.hom
  rw [← hzn, Grp.comp_hom_hom]
  refine (centralizes_iff _ _).mpr (fun Y a₀ b₀ => ?_)
  simpa only [← Category.assoc] using
    (centralizes_iff _ _).mp (centralizes_after_fieldChange (K := K) Z₀.inclusion hc₀)
      Y (a₀ ≫ z.hom.hom) b₀

end PinnedGeometry

section SplitCoverBorel

open CategoryTheory.Limits
open Opposite

open Specs.IntegralSemisimpleModel
open Specs.ExceptionalMarkedRootDescent
open Specs.AdjointRepresentation (GroupPoints)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open private subgroupFactor from LinearAlgebraicGroups.Reductive.WeylScheme
open private affineTorusPointEquiv from LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
open private fibrePointEquiv from LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent

attribute [local instance] integerAlgebra

set_option backward.isDefEq.respectTransparency false in
private theorem splitCoverBorelRestriction
    {k : Type u} [Field k] {D E : Pinning.BasedRootDatum.{u}} {M : Model D} {A : Model E}
    (c : MarkedCentralCover M A) (C : MarkedFibre M k) (C' : MarkedFibre A k) :
    let f := C.groupIso.inv ≫ (fibre k).map c.map ≫ C'.groupIso.hom
    let B := C.realization.pinned.pair.B
    let B' := C'.realization.pinned.pair.B
    ∃ fB : B.group ⟶ B'.group, fB ≫ B'.inclusion = B.inclusion ≫ f := by
  intro f B B'
  classical
  have hf : IsAffine B.group.X.left := (closedSubgroupAlgebraicGroup B).property.1
  obtain ⟨R, ⟨u⟩⟩ := essImage_algSpec.mpr hf
  let S := CommAlgCat.of Integers.{u} R.unop
  let g : GroupPoints C.realization.pinned.pair.G.val R.unop := u.hom ≫ B.inclusion.hom.hom
  have hg : markedFibrePoint C R.unop g ∈ markedPositiveBorel C R.unop :=
    ⟨u.hom, congrArg (forgetFibrePoint M.group R.unop) (Category.assoc _ _ _).symm⟩
  obtain ⟨l, r, hl, hr⟩ := positiveAndNegativeEnumerations D
  obtain ⟨⟨t, v⟩, ht⟩ := (markedPositiveBorelCoordinates C R.unop r hr ▸ hg)
  let tEq := affineTorusPointEquiv (k := Integers.{u}) (M := Multiplicative D.X) S
  obtain ⟨z, hz⟩ := tEq.surjective t
  change torusPoint D S z = t at hz
  have ht' : (torusPoint D S z ≫ M.torus.hom.hom) * orderedRootPoint M.toIntegralMarking S r v =
      markedFibrePoint C R.unop g := by simpa only [hz] using ht
  let w : E.I → S := v ∘ c.rootEquiv.symm
  have hw : (w ∘ c.rootEquiv) = v := funext fun i => congrArg v (c.rootEquiv.symm_apply_apply i)
  have h : markedFibrePoint C' R.unop (g ≫ f.hom.hom) ∈ markedPositiveBorel C' R.unop := by
    rw [markedFibrePoint_natural c C C' R.unop g, ← ht', map_mul, c.marking.2.2, ← hw,
      orderedRootPoint_image c.map c.rootEquiv S (c.marking.2.1 S)]
    rw [markedPositiveBorelCoordinates C' R.unop _ (enumerates_map c.rootEquiv c.marking.1 l r hl hr).2]
    exact ⟨⟨torusPoint E S (z.comp c.pullCharacter.toAddMonoidHom.toMultiplicative), w⟩, rfl⟩
  obtain ⟨b, hb⟩ := h
  have hbf : b ≫ B'.inclusion.hom.hom = g ≫ f.hom.hom :=
    (fibrePointEquiv C' R.unop).injective (by
      change markedFibrePoint C' R.unop (b ≫ B'.inclusion.hom.hom) =
        markedFibrePoint C' R.unop (g ≫ f.hom.hom)
      simpa only [markedFibrePoint, Category.assoc] using hb)
  apply subgroupFactor B' (B.inclusion ≫ f) (u.inv ≫ b)
  rw [Category.assoc, hbf]
  change u.inv ≫ (u.hom ≫ B.inclusion.hom.hom) ≫ f.hom.hom =
    B.inclusion.hom.hom ≫ f.hom.hom
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

end SplitCoverBorel

section PinnedCentralAssembly

open Opposite

open Specs.IntegralSemisimpleModel
open Specs.ExceptionalMarkedRootDescent (MarkedFibre)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.CentralIsogenies (IsCentralIsogeny IsTorusRestriction)
open Specs.AdjointCocharacters (coordinateHopf coordinateHopfMap)
open Specs.AdjointBorelCohomology (PinnedTwist)
open Specs.AutomorphismSequence (forgetPinning)
open private extendedCoordinateIso extendedCoordinateIso_comm from
  LinearAlgebraicGroups.Descent.AdjointBorelCohomology

attribute [local instance] integerAlgebra

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1300000 in
private theorem pinnedCentralCoverFromEquivariance
    {k K : Type u} [Field k] [Field K] [Algebra k K] [IsGalois k K]
    {D E : Pinning.BasedRootDatum.{u}} {M : Model D} {A : Model E} (c : MarkedCentralCover M A)
    (C : MarkedFibre M k) (C' : MarkedFibre A k)
    {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
    {l' : Aut C'.realization.attached.toBased ≃* Aut C'.realization.pinned}
    {G G' : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val} {B' T' : ClosedSubgroup G'.val}
    (d : PinnedTwist K C.realization.attached l B T)
    (d' : PinnedTwist K C'.realization.attached l' B' T') :
    let f := C.groupIso.inv ≫ (fibre k).map c.map ≫ C'.groupIso.hom
    (∀ σ : Gal(K/k),
      f ≫ (Functor.mapAut C'.realization.pinned (forgetPinning (A := C'.line))
        (l' (d'.outer σ))).asIso.inv =
        (Functor.mapAut C.realization.pinned (forgetPinning (A := C.line))
          (l (d.outer σ))).asIso.inv ≫ f) →
    ∃ (p : G.val ⟶ G'.val) (pT : T.group ⟶ T'.group) (pB : B.group ⟶ B'.group),
      IsCentralIsogeny p ∧ IsTorusRestriction p pT ∧
      B.inclusion ≫ p = pB ≫ B'.inclusion ∧
      (∃ Z : ClosedSubgroup G.val, IsSchemeKernel p Z ∧ SchemeDerivedGroup.IsSubgroupOf Z T ∧
        Centralizes (𝟙 G.val) Z.inclusion.hom.hom) ∧
      d'.groupIso.hom ≫ extendedHopfMap K (coordinateHopfMap (G := G) (H := G') p) =
        extendedHopfMap K (coordinateHopfMap
          (G := C.realization.pinned.pair.G) (H := C'.realization.pinned.pair.G) f) ≫ d.groupIso.hom ∧
      ∀ g : 𝟙_ (SchemeOver k) ⟶ G.val.X,
        pinnedGroundPoint C' d' (pointHom p (𝟙_ (SchemeOver k)) g) =
          integralPointHom c.map (CommAlgCat.of Integers.{u} K) (pinnedGroundPoint C d g) := by
  intro f hf
  obtain ⟨p, hp⟩ := descentThroughPinnedComparison d d' f hf
  let P := C.realization.pinned.pair
  let P' := C'.realization.pinned.pair
  let fT := C.torusIso.inv ≫ (fibre k).map c.torusMap ≫ C'.torusIso.hom
  obtain ⟨⟨hfin, hflat, hsurj, _⟩, hfT, Z₀, hZ₀, hZ₀T, hcentral⟩ := c.fibre k C C'
  obtain ⟨fB, hfB⟩ := splitCoverBorelRestriction c C C'
  let comparison (X Y : AffineAlgebraicGroup k)
      (e : extendedHopf K (Specs.AdjointCocharacters.coordinateHopf Y) ≅ extendedHopf K (Specs.AdjointCocharacters.coordinateHopf X)) :=
    (extendedCoordinateIso (K := K) X).symm ≪≫
      (hopfSpec (CommRingCat.of K)).mapIso e.op ≪≫ extendedCoordinateIso (K := K) Y
  let a := comparison G P.G d.groupIso
  let a' := comparison G' P'.G d'.groupIso
  let b := comparison (closedSubgroupAlgebraicGroup B) (closedSubgroupAlgebraicGroup P.B) d.borelIso
  let b' := comparison (closedSubgroupAlgebraicGroup B') (closedSubgroupAlgebraicGroup P'.B) d'.borelIso
  let t := comparison (closedSubgroupAlgebraicGroup T) (closedSubgroupAlgebraicGroup P.T) d.torusIso
  let t' := comparison (closedSubgroupAlgebraicGroup T') (closedSubgroupAlgebraicGroup P'.T) d'.torusIso
  let F := groupBaseChange k K
  have h := extendedCoordinateIso_comm (K := K) p f d.groupIso d'.groupIso hp
  have hB : b.hom ≫ F.map P.B.inclusion = F.map B.inclusion ≫ a.hom :=
    extendedCoordinateIso_comm (K := K) (G := closedSubgroupAlgebraicGroup B)
      (G₀ := closedSubgroupAlgebraicGroup P.B) B.inclusion P.B.inclusion d.borelIso d.groupIso d.borelComm
  have hB' : b'.hom ≫ F.map P'.B.inclusion = F.map B'.inclusion ≫ a'.hom :=
    extendedCoordinateIso_comm (K := K) (G := closedSubgroupAlgebraicGroup B')
      (G₀ := closedSubgroupAlgebraicGroup P'.B) B'.inclusion P'.B.inclusion d'.borelIso d'.groupIso d'.borelComm
  have hT : t.hom ≫ F.map P.T.inclusion = F.map T.inclusion ≫ a.hom :=
    extendedCoordinateIso_comm (K := K) (G := closedSubgroupAlgebraicGroup T)
      (G₀ := closedSubgroupAlgebraicGroup P.T) T.inclusion P.T.inclusion d.torusIso d.groupIso d.torusComm
  have hT' : t'.hom ≫ F.map P'.T.inclusion = F.map T'.inclusion ≫ a'.hom :=
    extendedCoordinateIso_comm (K := K) (G := closedSubgroupAlgebraicGroup T')
      (G₀ := closedSubgroupAlgebraicGroup P'.T) T'.inclusion P'.T.inclusion d'.torusIso d'.groupIso d'.torusComm
  obtain ⟨r, hr, hrt⟩ := restriction_of_comparison p f fT hfT.1 a a' t t' h hT hT'
  obtain ⟨s, hs, _⟩ := restriction_of_comparison p f fB hfB a a' b b' h hB hB'
  obtain ⟨Z, hZ, hZT, hc⟩ := kernel_of_comparison p f a a' t h hT Z₀ hZ₀ hZ₀T hcentral
  have hflat' : Flat p.hom.hom.left := fieldChangeProperty @Flat p f a a' h hflat
  have hsurj' : Surjective p.hom.hom.left := fieldChangeProperty @Surjective p f a a' h hsurj
  letI := hfin
  have hcl : UniversallyClosed p.hom.hom.left :=
    fieldChangeProperty @UniversallyClosed p f a a' h inferInstance
  letI := G.property.1
  letI := G'.property.1
  letI : LocallyOfFiniteType G.val.X.hom := G.property.2.1
  letI : LocallyOfFiniteType (p.hom.hom.left ≫ G'.val.X.hom) := Over.w p.hom.hom ▸ inferInstance
  have hfin' : IsFinite p.hom.hom.left := (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mpr
    ⟨IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr ⟨hcl, inferInstance⟩,
      locallyOfFiniteType_of_comp p.hom.hom.left G'.val.X.hom⟩
  have hr' : IsTorusRestriction p r := ⟨hr,
    fieldChangeProperty @Flat r fT t t' hrt hfT.2.1,
    fieldChangeProperty @Surjective r fT t t' hrt hfT.2.2⟩
  exact ⟨p, r, s, ⟨hfin', hflat', hsurj', Z, hZ, hc⟩, hr', hs.symm,
    ⟨Z, hZ, hZT, hc⟩, hp, pinnedGroundPoint_natural c C C' d d' p hp⟩

end PinnedCentralAssembly

section PinnedCentralComparison

open Specs.IntegralSemisimpleModel
open Specs.AutomorphismSequence (forgetPinning)
open private quadraticGalois from LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent

attribute [local instance] integerAlgebra

set_option backward.isDefEq.respectTransparency false in
theorem pinnedCentralCoverComparison : PinnedCentralCoverComparison.{u} := by
  intro k K _ _ _ _ _ D E M A c hE C C' l l' Q Q' hQ hQ' ω ω' d d' deg σ hσ hroots f
  have hequiv (τ : Gal(K/k)) :
      f ≫ ((Functor.mapAut C'.realization.pinned (forgetPinning (A := C'.line)))
        (l' (d'.data.outer τ))).asIso.inv =
      ((Functor.mapAut C.realization.pinned (forgetPinning (A := C.line)))
        (l (d.data.outer τ))).asIso.inv ≫ f := by
    rcases (quadraticGalois deg σ hσ).1 τ with hτ | hτ
    · rw [hτ]
      simp only [map_one]
      change f ≫ 𝟙 _ = 𝟙 _ ≫ f
      rw [Category.comp_id, Category.id_comp]
    · rw [hτ]
      let s := ((Functor.mapAut C.realization.pinned (forgetPinning (A := C.line)))
        (l (d.data.outer σ))).asIso
      let s' := ((Functor.mapAut C'.realization.pinned (forgetPinning (A := C'.line)))
        (l' (d'.data.outer σ))).asIso
      have h := centralCover_diagramEquivariant c hE C C' hQ hQ' (d.data.outer σ) (d'.data.outer σ) hroots
      change f ≫ s'.hom = s.hom ≫ f at h
      change f ≫ s'.inv = s.inv ≫ f
      apply (cancel_mono s'.hom).mp
      calc
        (f ≫ s'.inv) ≫ s'.hom = f := (Category.assoc _ _ _).trans (by
          rw [s'.inv_hom_id]
          exact Category.comp_id f)
        _ = (s.inv ≫ f) ≫ s'.hom := ((Category.assoc _ _ _).trans
          ((congrArg (s.inv ≫ ·) h).trans (s.inv_hom_id_assoc f))).symm
  obtain ⟨p, pT, pB, hp, hT, hB, ⟨Z, hZ, hZT, hc⟩, hs, hpoints⟩ :=
    pinnedCentralCoverFromEquivariance c C C' d.data d'.data hequiv
  obtain ⟨hpreT, hpreN⟩ :=
    centralTorusAndNormalizerPreimages d.group d'.group d.torus d'.torus p pT hT Z hZ hZT
  let Y := 𝟙_ (SchemeOver k)
  letI : IsAffine Y.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of k)))
  refine ⟨p, pT, pB, hp, hT, hB, ⟨Z, hZ, hZT, hc⟩, fun g => hpreT Y g, hpreN,
    centralIsogenyRationalImageNormal d.group d'.group p hp, hs, hpoints⟩

end PinnedCentralComparison

section CoverWeyl

open RootPairing
open Specs.IntegralSemisimpleModel (Model)

private theorem linearMap_ext_cover {D E : Pinning.BasedRootDatum.{u}} {M : Model D} {A : Model E}
    (c : MarkedCentralCover M A) (p q : D.X →ₗ[ℤ] D.X)
    (h : ∀ x : E.X, p (c.pullCharacter x) = q (c.pullCharacter x)) : p = q := by
  letI := D.freeX
  letI := c.characterIndex
  let χ := c.pullCharacter.toAddMonoidHom.toMultiplicative
  let π := QuotientGroup.mk' χ.range
  ext x
  let n := orderOf (π (Multiplicative.ofAdd x))
  have hn : 0 < n := orderOf_pos _
  have hp : π ((Multiplicative.ofAdd x) ^ n) = 1 := by
    rw [π.map_pow, pow_orderOf_eq_one]
  obtain ⟨y, hy⟩ := (QuotientGroup.eq_one_iff _).mp hp
  have hy' : c.pullCharacter y.toAdd = n • x := congrArg Multiplicative.toAdd hy
  have hx := h y.toAdd
  rw [hy', map_nsmul, map_nsmul] at hx
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  have hz : (n : ℤ) • p x = (n : ℤ) • q x := by simpa only [natCast_zsmul] using hx
  exact smul_right_injective D.X hn' hz

set_option backward.isDefEq.respectTransparency false in
private theorem coverWeylComparison
    {D E : Pinning.BasedRootDatum.{u}} {M : Model D} {A : Model E}
    (c : MarkedCentralCover M A) :
    ∃ d : D.datum.weylGroup ≃* E.datum.weylGroup,
      (∀ i, d (weylGroup.ofIdx D.datum i) = weylGroup.ofIdx E.datum (c.rootEquiv i)) ∧
      ∀ w x, w.val.weightEquiv (c.pullCharacter x) =
        c.pullCharacter ((d w).val.weightEquiv x) := by
  let V := D.datum.weylGroup × E.datum.weylGroup
  let H : Subgroup V :=
    { carrier := {v | ∀ x, v.1.val.weightEquiv (c.pullCharacter x) =
        c.pullCharacter (v.2.val.weightEquiv x)}
      one_mem' := by
        intro x
        simp only [Prod.fst_one, Prod.snd_one, Subgroup.coe_one]
        simp
      mul_mem' := by
        intro a b ha hb x
        change (a.1.val * b.1.val).weightEquiv (c.pullCharacter x) =
          c.pullCharacter ((a.2.val * b.2.val).weightEquiv x)
        simp only [RootPairing.Equiv.mul_eq_comp, RootPairing.Equiv.weightEquiv_comp_toLin,
          LinearEquiv.trans_apply]
        change a.1.val.weightEquiv (b.1.val.weightEquiv (c.pullCharacter x)) =
          c.pullCharacter (a.2.val.weightEquiv (b.2.val.weightEquiv x))
        rw [hb x, ha]
      inv_mem' := by
        intro a ha x
        change (a.1.val⁻¹).weightEquiv (c.pullCharacter x) =
          c.pullCharacter ((a.2.val⁻¹).weightEquiv x)
        rw [RootPairing.Equiv.weightEquiv_inv, RootPairing.Equiv.weightEquiv_inv]
        change a.1.val.weightEquiv.symm (c.pullCharacter x) =
          c.pullCharacter (a.2.val.weightEquiv.symm x)
        apply a.1.val.weightEquiv.injective
        rw [LinearEquiv.apply_symm_apply, ha, LinearEquiv.apply_symm_apply] }
  let p := (MonoidHom.fst D.datum.weylGroup E.datum.weylGroup).comp H.subtype
  let q := (MonoidHom.snd D.datum.weylGroup E.datum.weylGroup).comp H.subtype
  have hgen (i : D.I) : (weylGroup.ofIdx D.datum i, weylGroup.ofIdx E.datum (c.rootEquiv i)) ∈ H := by
    intro x
    change (RootPairing.Equiv.reflection D.datum i).weightEquiv (c.pullCharacter x) =
      c.pullCharacter ((RootPairing.Equiv.reflection E.datum (c.rootEquiv i)).weightEquiv x)
    rw [RootPairing.Equiv.reflection_weightEquiv, RootPairing.Equiv.reflection_weightEquiv,
      RootPairing.reflection_apply, RootPairing.reflection_apply, map_sub, map_smul, c.roots]
    change _ - (D.datum.toLinearMap (c.pullCharacter x) (D.datum.coroot i)) • _ =
      _ - (E.datum.toLinearMap x (E.datum.coroot (c.rootEquiv i))) • _
    rw [c.pairing, c.coroots]
  have hp : Function.Bijective p := by
    constructor
    · intro a b h
      have h₁ : a.val.1 = b.val.1 := h
      apply Subtype.ext
      apply Prod.ext h₁
      apply Subtype.ext
      apply RootPairing.Equiv.weightHom_injective E.datum
      ext x
      apply c.characterInjective
      exact (a.property x).symm.trans ((congrArg (fun z : D.datum.weylGroup =>
        z.val.weightEquiv (c.pullCharacter x)) h₁).trans (b.property x))
    · intro w
      obtain ⟨w, hw⟩ := w
      induction hw using RootPairing.weylGroup.induction with
      | mem i =>
        exact ⟨⟨_, hgen i⟩, rfl⟩
      | one =>
        exact ⟨1, map_one p⟩
      | mul x y hx hy h₁ h₂ =>
        obtain ⟨a, ha⟩ := h₁
        obtain ⟨b, hb⟩ := h₂
        exact ⟨a * b, by rw [map_mul, ha, hb]; rfl⟩
  have hq : Function.Bijective q := by
    constructor
    · intro a b h
      have h₂ : a.val.2 = b.val.2 := h
      apply Subtype.ext
      apply Prod.ext _ h₂
      apply Subtype.ext
      apply RootPairing.Equiv.weightHom_injective D.datum
      let u := a.val.1.val.weightEquiv
      let v := b.val.1.val.weightEquiv
      have h₀ : u.toLinearMap = v.toLinearMap := linearMap_ext_cover c _ _ (fun x =>
        (a.property x).trans ((congrArg (fun z : E.datum.weylGroup =>
          c.pullCharacter (z.val.weightEquiv x)) h₂).trans (b.property x).symm))
      exact LinearEquiv.ext (fun x => DFunLike.congr_fun h₀ x)
    · intro w
      obtain ⟨w, hw⟩ := w
      induction hw using RootPairing.weylGroup.induction with
      | mem i =>
        obtain ⟨a, rfl⟩ := c.rootEquiv.surjective i
        exact ⟨⟨_, hgen a⟩, rfl⟩
      | one =>
        exact ⟨1, map_one q⟩
      | mul x y hx hy h₁ h₂ =>
        obtain ⟨a, ha⟩ := h₁
        obtain ⟨b, hb⟩ := h₂
        exact ⟨a * b, by rw [map_mul, ha, hb]; rfl⟩
  let u := MulEquiv.ofBijective p hp
  let v := MulEquiv.ofBijective q hq
  refine ⟨u.symm.trans v, fun i => ?_, fun w x => ?_⟩
  · let z : H := ⟨_, hgen i⟩
    have h : u.symm (weylGroup.ofIdx D.datum i) = z := u.symm_apply_apply z
    change v (u.symm (weylGroup.ofIdx D.datum i)) = _
    rw [h]
    rfl
  · have h : (u.symm w).val.1 = w := u.apply_symm_apply w
    have hx := (u.symm w).property x
    change (u.symm w).val.1.val.weightEquiv (c.pullCharacter x) =
      c.pullCharacter ((v (u.symm w)).val.weightEquiv x) at hx
    rw [h] at hx
    exact hx

open Specs.ExceptionalValuedTorusNormalizer (fixedWeylGroup)

set_option backward.isDefEq.respectTransparency false in
private theorem coverWeyl_preservesFixedGroups
    {D E : Pinning.BasedRootDatum.{u}} {M : Model D} {A : Model E}
    (c : MarkedCentralCover M A) (hE : E.datum.rootSpan ℤ = ⊤)
    (d : Pinning.BasedIso D D) (e : Pinning.BasedIso E E)
    (hde : ∀ i, c.rootEquiv (d.val.indexEquiv i) = e.val.indexEquiv (c.rootEquiv i))
    (j : D.datum.weylGroup ≃* E.datum.weylGroup)
    (hj : ∀ w x, w.val.weightEquiv (c.pullCharacter x) =
      c.pullCharacter ((j w).val.weightEquiv x)) :
    ∃ i : fixedWeylGroup D d ≃* fixedWeylGroup E e, ∀ w, (i w).val = j w.val := by
  have hdiag (x : E.X) : c.pullCharacter (e.val.weightEquiv x) =
      d.val.weightEquiv (c.pullCharacter x) := by
    exact DFunLike.congr_fun (characterPullback_commutes_diagram c hE d e hde) x
  have hfix (w : D.datum.weylGroup) : w ∈ fixedWeylGroup D d ↔ j w ∈ fixedWeylGroup E e := by
    change w.val ∈ Subgroup.centralizer {d.val} ↔ (j w).val ∈ Subgroup.centralizer {e.val}
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      apply RootPairing.Equiv.weightHom_injective E.datum
      ext x
      apply c.characterInjective
      change c.pullCharacter ((j w).val.weightEquiv (e.val.weightEquiv x)) =
        c.pullCharacter (e.val.weightEquiv ((j w).val.weightEquiv x))
      rw [← hj, hdiag, hdiag, ← hj]
      exact DFunLike.congr_fun (congrArg RootPairing.Equiv.weightEquiv h) (c.pullCharacter x)
    · intro h
      apply RootPairing.Equiv.weightHom_injective D.datum
      have h' : (w.val * d.val).weightEquiv.toLinearMap = (d.val * w.val).weightEquiv.toLinearMap := by
        apply linearMap_ext_cover c
        intro x
        change w.val.weightEquiv (d.val.weightEquiv (c.pullCharacter x)) =
          d.val.weightEquiv (w.val.weightEquiv (c.pullCharacter x))
        rw [← hdiag, hj, hj, ← hdiag]
        exact congrArg c.pullCharacter (DFunLike.congr_fun
          (congrArg RootPairing.Equiv.weightEquiv h) x)
      exact LinearEquiv.ext (fun x => DFunLike.congr_fun h' x)
  let f := (j.toMonoidHom.comp (fixedWeylGroup D d).subtype).codRestrict (fixedWeylGroup E e)
    (fun w => (hfix w.val).mp w.property)
  refine ⟨MulEquiv.ofBijective f ⟨?_, ?_⟩, fun _ => rfl⟩
  · intro u v h
    exact Subtype.ext (j.injective (congrArg Subtype.val h))
  · intro v
    let w := j.symm v.val
    have hw : w ∈ fixedWeylGroup D d := (hfix w).mpr (by simp [w, v.property])
    exact ⟨⟨w, hw⟩, Subtype.ext (j.apply_symm_apply v.val)⟩

theorem centralCoverWeylComparison : CentralCoverWeylComparison.{u} := by
  intro D E M A c hE
  obtain ⟨j, hsimple, hchar⟩ := coverWeylComparison c
  exact ⟨j, hsimple, hchar, fun d e hde => coverWeyl_preservesFixedGroups c hE d e hde j hchar⟩

end CoverWeyl

section MarkedReductionIntersection

open Opposite

open Specs.IntegralSemisimpleModel
open Specs.ExceptionalMarkedRootDescent (MarkedFibre)
open Specs.ExceptionalValuedTorusNormalizer (FibreNormalizer valuationRingInclusion characterBasis normalizedValuation)
open LinearAlgebraicGroups.Arithmetic.ExceptionalValuedTorusNormalizer (integralTorusCoordinates)
open private torusPoint_natural from LinearAlgebraicGroups.Classification.IntegralSemisimpleModel

attribute [local instance] integerAlgebra

set_option backward.isDefEq.respectTransparency false in
theorem markedIwahoriNormalizerIntersection : MarkedIwahoriNormalizerIntersection.{u} := by
  intro K _ _ _ _ D M F G W _ _ j N hN κ C₀ B₀ hB₀
  let F₀ := normalizerOfMarkedFibre C₀
  letI := F₀.torusComm
  letI := D.freeY
  letI := D.finiteY
  let index := Module.Free.ChooseBasisIndex ℤ D.Y
  letI : Fintype index := Fintype.ofFinite index
  let b : Module.Basis index ℤ D.Y := Module.Free.chooseBasis ℤ D.Y
  let R := CommAlgCat.of Integers.{u} K
  let O := (valuation K).valuationSubring
  let S := CommAlgCat.of Integers.{u} O
  let B := C₀.realization.pinned.pair.B
  let e := groundSectionsEquiv B.group
  let L := CommAlgCat.of κ κ
  let Y := (testSpec κ).obj (op L)
  let i := B.inclusion.hom.hom
  let q := C₀.groupIso.inv.hom.hom
  have he (g : 𝟙_ (SchemeOver κ) ⟶ B.group.X) :
      forgetFibrePoint M.group L ((e g) ≫ i ≫ q) =
        forgetFibrePoint M.group L (toUnit Y ≫ g ≫ i ≫ q) := by
    rw [show e g = toUnit Y ≫ g from groundSectionsEquiv_apply B.group g]
    exact congrArg (forgetFibrePoint M.group L) (Category.assoc _ _ _)
  have hpos : positiveBorelPointSet F₀ = markedPositiveBorel C₀ L := by
    ext y
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨e g, he g⟩
    · rintro ⟨x, rfl⟩
      obtain ⟨g, hg⟩ := e.surjective x
      refine ⟨g, (he g).symm.trans ?_⟩
      exact congrArg (fun z => forgetFibrePoint M.group L (z ≫ i ≫ q)) hg
  obtain ⟨B₁, hB₁, a, ν, ha, hlog, hI⟩ := splitIwahoriIntersection M F F₀ b
  have hB : B₁ = B₀ := SetLike.coe_injective (hB₁.trans (hpos.trans hB₀.symm))
  subst B₁
  ext g
  constructor
  · rintro ⟨hg, hn⟩
    obtain ⟨n, hnp⟩ := hN ⟨g, hn⟩
    have h : n ∈ (markedBorelReduction M.group B₀).comap F.point := by
      change F.point n ∈ markedBorelReduction M.group B₀
      exact hnp.symm ▸ hg
    rw [hI] at h
    obtain ⟨t, ht, htn⟩ := h
    have hv (i : index) :
        normalizedValuation K (t (Multiplicative.ofAdd (characterBasis D b i)) : K) = 1 := by
      let x := characterBasis D b i
      have hh := hlog t x
      change ν t = 1 at ht
      rw [ht] at hh
      have hz : log (normalizedValuation K (t (Multiplicative.ofAdd x) : K)) = 0 := by
        simpa using hh.symm
      have hne : normalizedValuation K (t (Multiplicative.ofAdd x) : K) ≠ 0 :=
        (map_ne_zero (normalizedValuation K)).mpr (t (Multiplicative.ofAdd x)).ne_zero
      rw [← exp_log hne, hz, exp_zero]
    obtain ⟨s, hs⟩ := (integralTorusCoordinates D b t).mp hv
    refine ⟨torusPoint D S s, ?_⟩
    change (((integralPointFunctor (splitTorus D)).map (valuationRingInclusion K))
        (torusPoint D S s) ≫ M.torus.hom.hom : IntegralPoints M.group R) = j g
    calc
      _ = torusPoint D R ((Units.map O.subtype.toMonoidHom).comp s) ≫ M.torus.hom.hom :=
        congrArg (fun p : IntegralPoints (splitTorus D) R => p ≫ M.torus.hom.hom)
          (torusPoint_natural (valuationRingInclusion K) s)
      _ = _ := by
        change (a t).val = n at htn
        rw [hs, ← ha, htn]
        exact hnp
  · intro hg
    refine ⟨reduction_contains_unitTorus C₀ B₀ hB₀ hg, ?_⟩
    rw [← localNormalizer_unitKernel N] at hg
    obtain ⟨t, _, rfl⟩ := hg
    exact N.torus_le t.property

end MarkedReductionIntersection

end

end LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriImageComparison
