import Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalValuedTorusNormalizer
import LinearAlgebraicGroups.Arithmetic.GlobalPlaces
import LinearAlgebraicGroups.Descent.AdjointBorelCohomology
import LinearAlgebraicGroups.RootData.CharacterPairing
import LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
import LinearAlgebraicGroups.Classification.IntegralRealization
import LinearAlgebraicGroups.Relative.MaximalSplitTori
import LinearAlgebraicGroups.Relative.RelativeWeylScheme
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Batteries.Tactic.OpenPrivate

open CategoryTheory
open scoped WithZero

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalValuedTorusNormalizer

open ValuativeRel WithZero
open Specs.ExceptionalValuedTorusNormalizer

noncomputable section

universe u

set_option linter.style.haveILetI false

private theorem normalizedValuation_surjective (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (x : ℤᵐ⁰) :
    ∃ t : K, normalizedValuation K t = x := by
  let i := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  obtain ⟨t, ht⟩ := valuation_surjective (i.symm x)
  exact ⟨t, by change i (valuation K t) = x; rw [ht, i.apply_symm_apply]⟩


section Torus

open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel (IntegralAlgebra Integers IntegralMarking IntegralPoints
  TorusValues cocharacter integerAlgebra torusPoint)

private theorem characterBasis_repr {D : BasedRootDatum.{u}} {ι : Type u} [Fintype ι]
    (b : Module.Basis ι ℤ D.Y) (x : D.X) (i : ι) :
    (characterBasis D b).repr x i = D.datum.toLinearMap x (b i) := by
  classical
  change (b.dualBasis.map D.datum.toPerfPair.symm).repr x i = _
  rw [Module.Basis.map_repr, LinearEquiv.symm_symm]
  exact b.dualBasis_repr (D.datum.toPerfPair x) i

private theorem cocharacterBasis_repr {D : BasedRootDatum.{u}} {ι : Type u} [Fintype ι]
    (b : Module.Basis ι ℤ D.Y) (y : D.Y) (i : ι) :
    b.repr y i = D.datum.toLinearMap (characterBasis D b i) y := by
  classical
  change b.repr y i = D.datum.toPerfPair (D.datum.toPerfPair.symm (b.dualBasis i)) y
  rw [LinearEquiv.apply_symm_apply]
  exact (b.dualBasis_apply i y).symm

theorem torusBasisCoordinates : TorusBasisCoordinates.{u} := by
  classical
  intro D ι _ b R
  let c := characterBasis D b
  let eval : TorusValues D R →* (ι → Rˣ) :=
    { toFun := fun t i ↦ t (Multiplicative.ofAdd (c i))
      map_one' := rfl
      map_mul' _ _ := rfl }
  have hx (x : D.X) : Multiplicative.ofAdd x =
      ∏ i, Multiplicative.ofAdd (c i) ^ c.repr x i := by
    simpa only [ofAdd_sum, ofAdd_zsmul] using
      congrArg Multiplicative.ofAdd (c.sum_repr x).symm
  have hinj : Function.Injective eval := by
    intro f g h
    apply MonoidHom.ext
    intro x
    change f (Multiplicative.ofAdd x.toAdd) = g (Multiplicative.ofAdd x.toAdd)
    rw [hx, map_prod, map_prod]
    simp only [map_zpow]
    apply Finset.prod_congr rfl
    intro i _
    exact congrArg (fun z : Rˣ ↦ z ^ c.repr x.toAdd i) (congrFun h i)
  have hsurj : Function.Surjective eval := by
    intro u
    let f := c.constr ℤ (fun i ↦ Additive.ofMul (u i))
    refine ⟨f.toAddMonoidHom.toMultiplicativeLeft, ?_⟩
    funext i
    exact congrArg Additive.toMul (c.constr_basis ℤ (fun i ↦ Additive.ofMul (u i)) i)
  let e := MulEquiv.ofBijective eval ⟨hinj, hsurj⟩
  refine ⟨e, fun _ _ ↦ rfl, ?_⟩
  intro u x
  calc
    e.symm u (Multiplicative.ofAdd x) = ∏ i, e.symm u (Multiplicative.ofAdd (c i)) ^
        c.repr x i := by rw [hx x, map_prod]; simp only [map_zpow]
    _ = ∏ i, u i ^ (D.datum.toLinearMap x (b i)) := by
      apply Finset.prod_congr rfl
      intro i _
      have hi : e.symm u (Multiplicative.ofAdd (c i)) = u i :=
        congrFun (e.apply_symm_apply u) i
      rw [hi, characterBasis_repr]

theorem exceptionalCocharacterBases : ExceptionalCocharacterBases.{u} := by
  intro D
  constructor
  · intro h i
    unfold simpleCorootBasis
    exact Module.Basis.mk_apply _ _ i
  · intro h i j
    classical
    let b : Module.Basis D.base.support ℤ D.X :=
      Module.Basis.mk D.base.linearIndepOn_root <| by
        change ⊤ ≤ Submodule.span ℤ (Set.range (D.datum.root ∘ ((↑) : D.base.support → D.I)))
        rw [Set.range_comp, Subtype.range_coe, D.base.span_int_root_support, h]
    have hbj : b j = D.datum.root j := by
      dsimp only [b]
      exact Module.Basis.mk_apply _ _ j
    have hi : fundamentalCoweightBasis D h i = D.datum.toLinearMap.flip.toPerfPair.symm
        (b.dualBasis i) := rfl
    rw [hi, ← hbj, ← LinearMap.flip_apply D.datum.toLinearMap]
    exact (congrArg (fun l : Module.Dual ℤ D.X ↦ l (b j))
        (D.datum.toLinearMap.flip.toPerfPair.apply_symm_apply (b.dualBasis i))).trans
      (b.dualBasis_apply_self i j)

attribute [local instance] integerAlgebra

private def integerValuationOnUnits (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Kˣ →* Multiplicative ℤ where
  toFun u := Multiplicative.ofAdd (log (normalizedValuation K (u : K)))
  map_one' := by
    change Multiplicative.ofAdd (log (normalizedValuation K 1)) = 1
    rw [map_one, log_one]
    rfl
  map_mul' u v := by
    have hu : normalizedValuation K (u : K) ≠ 0 := by simp
    have hv : normalizedValuation K (v : K) ≠ 0 := by simp
    change Multiplicative.ofAdd (log (normalizedValuation K ((u : K) * (v : K)))) =
      Multiplicative.ofAdd (log (normalizedValuation K (u : K)) +
        log (normalizedValuation K (v : K)))
    rw [map_mul, log_mul hu hv]

private theorem integerValuationOnUnits_surj (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] :
    Function.Surjective (integerValuationOnUnits K) := by
  intro n
  obtain ⟨x, hx⟩ := normalizedValuation_surjective K (exp n.toAdd)
  have h₀ : x ≠ 0 := by
    intro h
    rw [h, map_zero] at hx
    exact exp_ne_zero hx.symm
  use Units.mk0 x h₀
  change Multiplicative.ofAdd (log (normalizedValuation K x)) = n
  rw [hx, log_exp]
  rfl

private theorem integerValuationOnUnits_eq_one (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (u : Kˣ) :
    integerValuationOnUnits K u = 1 ↔ normalizedValuation K (u : K) = 1 := by
  have h : normalizedValuation K (u : K) ≠ 0 := by simp
  change log (normalizedValuation K (u : K)) = 0 ↔ _
  constructor
  · intro hz
    simpa only [exp_log h, exp_zero] using congrArg exp hz
  · intro hz
    rw [hz, log_one]

theorem splitTorusTranslation : SplitTorusTranslation.{u} := by
  classical
  intro K _ _ _ _ D ι _ b
  let R := CommAlgCat.of Integers.{u} K
  obtain ⟨e, he, hcoords⟩ := torusBasisCoordinates D b R
  let del : (ι → (↑R)ˣ) →* Multiplicative D.Y :=
    { toFun := fun u ↦ Multiplicative.ofAdd
        (b.equivFun.symm fun i ↦ (integerValuationOnUnits K (u i)).toAdd)
      map_one' := by
        apply Multiplicative.toAdd.injective
        change b.equivFun.symm (fun i ↦ (integerValuationOnUnits K 1).toAdd) = 0
        simp only [map_one]
        exact map_zero b.equivFun.symm
      map_mul' := fun u v ↦ by
        apply Multiplicative.toAdd.injective
        change b.equivFun.symm (fun i ↦ (integerValuationOnUnits K (u i * v i)).toAdd) =
          b.equivFun.symm (fun i ↦ (integerValuationOnUnits K (u i)).toAdd) +
          b.equivFun.symm (fun i ↦ (integerValuationOnUnits K (v i)).toAdd)
        simp only [map_mul]
        exact map_add b.equivFun.symm _ _ }
  let ν : TorusValues D R →* Multiplicative D.Y :=
    { toFun := fun t ↦ del (e t)
      map_one' := by simp only [map_one]
      map_mul' _ _ := by simp only [map_mul] }
  refine ⟨ν, ?_, ?_, ?_⟩
  · intro y
    choose u hu using fun i : ι ↦ integerValuationOnUnits_surj K
      (Multiplicative.ofAdd (b.equivFun y.toAdd i))
    refine ⟨e.symm u, Multiplicative.toAdd.injective ?_⟩
    change b.equivFun.symm (fun i ↦ (integerValuationOnUnits K (e (e.symm u) i)).toAdd) = _
    rw [e.apply_symm_apply]
    apply b.equivFun.injective
    rw [LinearEquiv.apply_symm_apply]
    funext i
    exact congrArg Multiplicative.toAdd (hu i)
  · intro t x
    let n : ι → ℤ := fun i ↦ (integerValuationOnUnits K (e t i)).toAdd
    have ht : t (Multiplicative.ofAdd x) = ∏ i, (e t i) ^ (D.datum.toLinearMap x (b i)) := by
      simpa only [e.symm_apply_apply] using hcoords (e t) x
    have hn : ∀ i, b.repr (ν t).toAdd i = n i := by
      intro i
      exact congrFun (b.equivFun.apply_symm_apply n) i
    change D.datum.toLinearMap x (ν t).toAdd =
      (integerValuationOnUnits K (t (Multiplicative.ofAdd x))).toAdd
    rw [ht, map_prod, toAdd_prod]
    conv_lhs => rw [← b.sum_repr (ν t).toAdd]
    simp only [map_sum, map_smul, hn, map_zpow, toAdd_zpow, n]
    apply Finset.sum_congr rfl
    intro i _
    simp [mul_comm]
  · intro t
    rw [← Multiplicative.toAdd.injective.eq_iff, ← b.equivFun.injective.eq_iff]
    change b.equivFun (b.equivFun.symm
      (fun i ↦ (integerValuationOnUnits K (e t i)).toAdd)) = b.equivFun 0 ↔ _
    rw [LinearEquiv.apply_symm_apply, map_zero, funext_iff]
    constructor
    · intro h i
      rw [← he, ← integerValuationOnUnits_eq_one]
      exact Multiplicative.toAdd.injective (h i)
    · intro h i
      have hi := (integerValuationOnUnits_eq_one K (e t i)).mpr (by rw [he]; exact h i)
      exact congrArg Multiplicative.toAdd hi

theorem splitTranslationAction : SplitTranslationAction.{u} := by
  intro K _ _ _ _ D R ν hν
  constructor
  · intro y s
    apply D.datum.toLinearMap.flip.toPerfPair.injective
    ext x
    change D.datum.toLinearMap x (ν (cocharacter D y R s)).toAdd =
      D.datum.toLinearMap x (log (normalizedValuation K (s : K)) • y)
    rw [hν, map_smul]
    change (integerValuationOnUnits K (s ^ D.datum.toLinearMap x y)).toAdd = _
    rw [map_zpow, toAdd_zpow, zsmul_eq_mul, zsmul_eq_mul, mul_comm]
    rfl
  · intro w t
    apply D.datum.toLinearMap.flip.toPerfPair.injective
    ext x
    change D.datum.toLinearMap x (ν (t.comp w.weightEquiv.symm.toLinearMap.toAddMonoidHom.toMultiplicative)).toAdd =
      D.datum.toLinearMap x (w.coweightEquiv.symm (ν t).toAdd)
    rw [hν]
    change log (normalizedValuation K (t (Multiplicative.ofAdd (w.weightEquiv.symm x)) : K)) = _
    rw [← hν]
    have h := w.toLinearMap_weightEquiv (w.weightEquiv.symm x) (w.coweightEquiv.symm (ν t).toAdd)
    rwa [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, eq_comm] at h

theorem foldedTorusFactorValuations : FoldedTorusFactorValuations.{u} := by
  intro F L _ _ _ _ _ _ _ _ _ _ _ hv σ hσ
  have hbase (u : Fˣ) :
      ((log (normalizedValuation L (algebraMap F L (u : F))) : ℤ) : ℚ) / 2 =
        ((integerValuationOnUnits F u).toAdd : ℚ) := by
    change ((log (normalizedValuation L (algebraMap F L (u : F))) : ℤ) : ℚ) / 2 =
      ((log (normalizedValuation F (u : F)) : ℤ) : ℚ)
    rw [hv, log_pow, two_nsmul, Int.cast_add]
    ring
  have hpair (u : Lˣ) :
      (((log (normalizedValuation L (u : L)) : ℤ) : ℚ) / 2,
       ((log (normalizedValuation L (σ (u : L))) : ℤ) : ℚ) / 2) =
      (((integerValuationOnUnits L u).toAdd : ℚ) / 2,
       ((integerValuationOnUnits L u).toAdd : ℚ) / 2) := by
    rw [hσ]
    rfl
  constructor
  · ext x
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨(integerValuationOnUnits F u).toAdd, (hbase u).symm⟩
    · rintro ⟨n, rfl⟩
      obtain ⟨u, hu⟩ := integerValuationOnUnits_surj F (Multiplicative.ofAdd n)
      exact ⟨u, by dsimp only; rw [hbase u, hu]; rfl⟩
  · ext x
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨(integerValuationOnUnits L u).toAdd, (hpair u).symm⟩
    · rintro ⟨n, rfl⟩
      obtain ⟨u, hu⟩ := integerValuationOnUnits_surj L (Multiplicative.ofAdd n)
      exact ⟨u, by dsimp only; rw [hpair u, hu]; rfl⟩

end Torus

section Apartment

open scoped SemidirectProduct

theorem normalizerApartment : NormalizerApartment.{u} := by
  classical
  intro N W Λ V _ _ _ _ _ q J ν ρ j w h hj hw hν hq hunit hconj
  choose s hs using hq
  have hs' (a : W) : q (s a).val = a := hs a
  let t (n : N) : q.ker := ⟨n * (s (q n)).val⁻¹, by
    show q (n * (s (q n)).val⁻¹) = 1
    simp [hs']⟩
  have ht (n m : N) (hm : m ∈ J) (e : q n = q m) :
      ν (t n) = ν ⟨n * m⁻¹, by simp [e]⟩ := by
    have hc : q (m * (s (q n)).val⁻¹) = 1 := by simp [hs', e]
    have hc' : ν (⟨m * (s (q n)).val⁻¹, hc⟩ : q.ker) = 1 :=
      (hunit _).mpr (J.mul_mem hm (J.inv_mem (s (q n)).property))
    have he : t n = (⟨n * m⁻¹, by simp [e]⟩ : q.ker) * ⟨_, hc⟩ := by
      apply Subtype.ext
      change n * (s (q n)).val⁻¹ = (n * m⁻¹) * (m * (s (q n)).val⁻¹)
      group
    rw [he, map_mul, hc', mul_one]
  have htJ (n : N) (hn : n ∈ J) : ν (t n) = 1 :=
    (hunit _).mpr (J.mul_mem hn (J.inv_mem (s (q n)).property))
  have htT (a : q.ker) : ν (t a.val) = ν a := by
    have ha : q a.val = 1 := a.property
    have e : q a.val = q 1 := by simp [ha]
    simpa using ht a.val 1 J.one_mem e
  let p : N →* Λ ⋊[ρ] W :=
    { toFun := fun n => ⟨ν (t n), q n⟩
      map_one' := by ext <;> simp [htJ]
      map_mul' := by
        intro n m
        have hl : q ((s (q n)).val * (s (q m)).val) = q (n * m) := by simp [hs']
        have hv : (⟨(n * m) * ((s (q n)).val * (s (q m)).val)⁻¹,
            by
              change q ((n * m) * ((s (q n)).val * (s (q m)).val)⁻¹) = 1
              rw [map_mul, map_inv, hl, mul_inv_cancel]⟩ : q.ker) =
            t n * conjugateTorus q (s (q n)).val (t m) := by
          apply Subtype.ext
          change (n * m) * ((s (q n)).val * (s (q m)).val)⁻¹ =
            (n * (s (q n)).val⁻¹) *
              ((s (q n)).val * (m * (s (q m)).val⁻¹) * (s (q n)).val⁻¹)
          group
        ext
        · change ν (t (n * m)) = ν (t n) * ρ (q n) (ν (t m))
          rw [ht _ _ (J.mul_mem (s (q n)).property (s (q m)).property) hl.symm,
            hv, map_mul, hconj, hs']
        · exact map_mul q _ _ }
  have hleft (n : N) : (p n).left = ν (t n) := rfl
  have hright (n : N) : (p n).right = q n := rfl
  have hpJ (n : N) (hn : n ∈ J) : (p n).left = 1 := htJ n hn
  have hpT (a : q.ker) : (p a.val).left = ν a := htT a
  refine ⟨p, ?_, ?_, ?_, hright, hpT, hpJ, ht, ?_⟩
  · rintro ⟨z, a⟩
    obtain ⟨b, hb⟩ := hν z
    refine ⟨b.val * (s a).val, ?_⟩
    rw [map_mul]
    ext
    · simp [hpT, hpJ _ (s a).property, hb]
    · have hb' : q b.val = 1 := b.property
      simp [hright, hb', hs']
  · ext n
    constructor
    · intro hn
      have hn' : p n = 1 := hn
      have hqn : n ∈ q.ker := congrArg SemidirectProduct.right hn'
      have hνn : ν (⟨n, hqn⟩ : q.ker) = 1 := (hpT ⟨n, hqn⟩).symm.trans
        (congrArg SemidirectProduct.left hn')
      exact ⟨hqn, (hunit ⟨n, hqn⟩).mp hνn⟩
    · rintro ⟨hqn, hn⟩
      change p n = 1
      ext
      · exact hpJ _ hn
      · exact hqn
  · intro a b e
    have hlin : w a.right = w b.right :=
      congrArg AffineEquiv.linear e
    have hzero : (j a.left).toAdd = (j b.left).toAdd := by
      have he := DFunLike.congr_fun e 0
      simpa [affineTransformation, AffineEquiv.ofLinearEquiv] using he
    exact SemidirectProduct.ext (hj (Multiplicative.toAdd.injective hzero)) (hw hlin)
  · intro n x c d a hc hd
    have hc' : (p c.val).right = 1 := c.property
    have hd' : (p d.val).right = 1 := d.property
    have hmul : (j ((p (d.val * n * c.val⁻¹)).left)).toAdd = 0 := by
      rw [map_mul, map_mul, map_inv]
      change (j ((p d.val).left * ρ (p d.val).right (p n).left *
        ρ ((p d.val).right * (p n).right) (ρ (p c.val).right⁻¹ (p c.val).left⁻¹))).toAdd = 0
      simp only [hc', hd', one_mul, inv_one, map_one, MulAut.one_apply, hpT,
        map_mul, toAdd_mul, h, map_inv, toAdd_inv, hc, hd, map_neg, neg_neg]
      change -(w (p n).right (x - 0) + (j (p n).left).toAdd) +
        (j (p n).left).toAdd + w (p n).right x = 0
      simp
    have hz : (p (d.val * n * c.val⁻¹)).left = 1 := by
      apply hj
      apply Multiplicative.toAdd.injective
      simpa using hmul
    let g := d.val * n * c.val⁻¹
    have ht₁ : ν (t g) = 1 := hz
    have ht₂ : (t g).val ∈ J := (hunit _).mp ht₁
    have hg : g = (t g).val * (s (q g)).val := by
      change g = (g * (s (q g)).val⁻¹) * (s (q g)).val
      simp
    change g ∈ J
    rw [hg]
    exact J.mul_mem ht₂ (s (q g)).property

end Apartment

section PermutationBasis

open Specs.Pinning (BasedRootDatum BasedIso)

theorem basedPermutation : BasedPermutation.{u} := by
  classical
  intro D e b hb i
  let p := simplePermutation D e
  have hp (j : D.base.support) : (p j).val = e.val.indexEquiv j := rfl
  have hpair (x : D.X) (y : D.Y) :
      D.datum.toLinearMap (e.val.weightEquiv x) (e.val.coweightEquiv.symm y) =
        D.datum.toLinearMap x y := by
    rw [e.val.toLinearMap_weightEquiv, LinearEquiv.apply_symm_apply]
  have hc (j : D.base.support) : e.val.coweightEquiv.symm (b j) = b (p j) := by
    rcases hb with ⟨h, rfl⟩ | ⟨h, rfl⟩
    · rw [(exceptionalCocharacterBases D).1 h, (exceptionalCocharacterBases D).1 h, hp]
      apply e.val.coweightEquiv.injective
      rw [LinearEquiv.apply_symm_apply, RootPairing.Equiv.coweightEquiv_apply,
        RootPairing.Hom.coroot_coweightMap_apply, Equiv.symm_apply_apply]
    · let c : Module.Basis D.base.support ℤ D.X :=
        Module.Basis.mk D.base.linearIndepOn_root <| by
          change ⊤ ≤ Submodule.span ℤ (Set.range (D.datum.root ∘ ((↑) : D.base.support → D.I)))
          rw [Set.range_comp, Subtype.range_coe, D.base.span_int_root_support, h]
      suffices ev : ∀ k : D.base.support,
          D.datum.toLinearMap (D.datum.root k)
            (e.val.coweightEquiv.symm (fundamentalCoweightBasis D h j)) =
          D.datum.toLinearMap (D.datum.root k) (fundamentalCoweightBasis D h (p j)) by
        apply D.datum.toLinearMap.flip.toPerfPair.injective
        apply c.ext
        intro k
        have hk : c k = D.datum.root k := Module.Basis.mk_apply _ _ _
        exact hk ▸ ev k
      intro k
      obtain ⟨l, rfl⟩ := p.surjective k
      rw [hp, ← RootPairing.Hom.root_weightMap_apply D.datum D.datum l.val e.val.toHom]
      change D.datum.toLinearMap (e.val.weightEquiv (D.datum.root l))
        (e.val.coweightEquiv.symm (fundamentalCoweightBasis D h j)) = _
      rw [hpair, (exceptionalCocharacterBases D).2 h j l]
      have hl : e.val.weightEquiv (D.datum.root l) = D.datum.root (p l) := by
        rw [hp, RootPairing.Equiv.weightEquiv_apply, RootPairing.Hom.root_weightMap_apply]
      change (if l = j then 1 else 0) =
        D.datum.toLinearMap (e.val.weightEquiv (D.datum.root l))
          (fundamentalCoweightBasis D h (p j))
      rw [hl, (exceptionalCocharacterBases D).2 h]
      simp only [Equiv.apply_eq_iff_eq]
  refine ⟨hc i, ?_⟩
  let c := characterBasis D b
  apply c.repr.injective
  ext j
  obtain ⟨k, rfl⟩ := p.surjective j
  change (c.repr (e.val.weightEquiv (c i))) (p k) = (c.repr (c (p i))) (p k)
  rw [characterBasis_repr, ← hc k, hpair, ← characterBasis_repr, c.repr_self_apply,
    c.repr_self_apply]
  simp only [Equiv.apply_eq_iff_eq]

open private positiveCorootSum positiveCorootSum_pairing
  from LinearAlgebraicGroups.Classification.PinnedDatumFromMarkedRootGroups
open private positive_iff_of_injective from LinearAlgebraicGroups.Classification.NormalizerComparison

theorem invariantRegularCocharacter : InvariantRegularCocharacter.{u} := by
  classical
  intro D
  letI := D.finiteRoots
  letI := Fintype.ofFinite D.I
  refine ⟨positiveCorootSum D, ?_, positiveCorootSum_pairing D, ?_⟩
  · intro e
    let p := e.val.indexEquiv
    have hmem (i : D.I) : i ∈ D.base.support ↔ p i ∈ D.base.support := by
      change i ∈ (D.base.support : Set D.I) ↔ p i ∈ (D.base.support : Set D.I)
      conv_rhs => rw [← e.property]
      exact p.injective.mem_set_image.symm
    have hmap (i : D.I) : e.val.coweightEquiv (D.datum.coroot (p i)) = D.datum.coroot i := by
      rw [RootPairing.Equiv.coweightEquiv_apply, RootPairing.Hom.coroot_coweightMap_apply]
      simp only [p, Equiv.symm_apply_apply]
    have hpos (i : D.I) : D.base.flip.IsPos i ↔ D.base.flip.IsPos (p i) :=
      positive_iff_of_injective D.datum.flip D.datum.flip D.base.flip D.base.flip p
        e.val.coweightEquiv.toLinearMap e.val.coweightEquiv.injective hmap hmem i
    apply e.val.coweightEquiv.injective
    rw [LinearEquiv.apply_symm_apply]
    change (∑ i ∈ Finset.univ.filter D.base.flip.IsPos, D.datum.coroot i) =
      e.val.coweightEquiv (∑ i ∈ Finset.univ.filter D.base.flip.IsPos, D.datum.coroot i)
    rw [map_sum]
    refine Finset.sum_bij (fun i _ ↦ p i) ?_ (fun _ _ _ _ h ↦ p.injective h) ?_ ?_
    · intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hpos i).mp (Finset.mem_filter.mp hi).2⟩
    · intro i hi
      obtain ⟨j, rfl⟩ := p.surjective i
      exact ⟨j, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (hpos j).mpr (Finset.mem_filter.mp hi).2⟩, rfl⟩
    · intro i _
      exact (hmap i).symm
  · intro i
    exact (positiveCorootSum_pairing D i).trans_ne (mul_ne_zero (by decide) (D.base.height_ne_zero i))

open Specs.SimpleRoots (wordLength wordProduct inversions)
open private simple_reflections_generate exists_regular_functional
  from LinearAlgebraicGroups.Classification.NormalizerComparison
open private exists_shortest_word word_append word_cons word_nil reflection_cancel length_inverse
  length_eq_inversions rightInversions rightInversions_card_mul perm_mul perm_reflection reflected_value
  from LinearAlgebraicGroups.RootData.SimpleRoots

private theorem reflection_natural (D : BasedRootDatum.{u}) (g : RootPairing.Aut D.datum) (i : D.I) :
    g * RootPairing.Equiv.reflection D.datum i =
      RootPairing.Equiv.reflection D.datum (g.indexEquiv i) * g := by
  apply RootPairing.Equiv.weightHom_injective D.datum
  ext x
  simp only [map_mul, LinearEquiv.mul_apply]
  exact g.weightEquiv_reflection i x

theorem fixedWeylGeneration : FixedWeylGeneration.{u} := by
  classical
  intro D e he hord
  letI := D.finiteRoots
  letI := D.freeX
  letI := D.finiteX
  letI := D.reduced
  let P := D.datum
  let b := D.base
  let p := simplePermutation D e
  let s (i : b.support) := RootPairing.weylGroup.ofIdx P i.val
  let C := Subgroup.closure (Set.range (orbitWeylReflection D e))
  let B := (Subgroup.centralizer {e.val}).comap P.weylGroup.subtype
  have hB (w : P.weylGroup) : w ∈ B ↔ Commute e.val w.val := by
    change w.val ∈ Subgroup.centralizer {e.val} ↔ e.val * w.val = w.val * e.val
    exact Subgroup.mem_centralizer_singleton_iff.trans eq_comm
  have hp (i : b.support) : (p i).val = e.val.indexEquiv i.val := rfl
  have hp₂ (i : b.support) : p (p i) = i := Subtype.ext (he i.val)
  have hs (i : b.support) : s i * s i = 1 := reflection_cancel P i.val
  have hpref (i : b.support) (hi : p i ≠ i) :
      P.reflectionPerm i.val (p i).val = (p i).val := by
    apply P.root.injective
    rw [P.root_reflectionPerm, P.reflection_apply_root, hord i hi, zero_smul, sub_zero]
  have hcomm (i : b.support) (hi : p i ≠ i) : Commute (s i) (s (p i)) := by
    apply Subtype.ext
    have h := reflection_natural D (s i).val (p i).val
    change (s i).val * (s (p i)).val =
      RootPairing.Equiv.reflection P (P.reflectionPerm i.val (p i).val) * (s i).val at h
    rwa [hpref i hi] at h
  have hd (i : b.support) : e.val * (s i).val = (s (p i)).val * e.val :=
    reflection_natural D e.val i.val
  have hgenComm (i : b.support) : Commute e.val (orbitWeylReflection D e i).val := by
    by_cases hi : p i = i
    · rw [orbitWeylReflection, ite_eq_left hi]
      exact (hd i).trans (by rw [hi])
    · rw [orbitWeylReflection, ite_eq_right hi]
      change e.val * ((s i).val * (s (p i)).val) = ((s i).val * (s (p i)).val) * e.val
      rw [← mul_assoc, hd, mul_assoc, hd, hp₂, ← mul_assoc]
      exact congrArg (· * e.val) (congrArg Subtype.val (hcomm i hi).eq.symm)
  have hCB : C ≤ B := (Subgroup.closure_le B).mpr (by
    rintro w ⟨i, rfl⟩
    exact (hB _).mpr (hgenComm i))
  obtain ⟨f, hf₀, hf⟩ := exists_regular_functional P b
  let len := wordLength P b
  have hgen := simple_reflections_generate P b
  have hlen (w : P.weylGroup) : len w = (rightInversions P f w).ncard := by
    change wordLength P b w = _
    rw [← length_inverse P b w, length_eq_inversions P b f hf₀ hf hgen]
    simp only [inversions, rightInversions, inv_inv]
  have hup (w : P.weylGroup) (i : b.support)
      (hi : b.IsPos (P.weylGroupToPerm w i.val)) : len (w * s i) = len w + 1 := by
    rw [hlen, hlen w]
    exact rightInversions_card_mul P b f hf w i ((hf _).mp hi)
  have hdown (w : P.weylGroup) (i : b.support)
      (hi : ¬ b.IsPos (P.weylGroupToPerm w i.val)) : len (w * s i) < len w := by
    have hi' : f (P.root (P.weylGroupToPerm w i.val)) < 0 :=
      lt_of_le_of_ne (le_of_not_gt fun h ↦ hi ((hf _).mpr h)) (hf₀ _)
    have hj : b.IsPos (P.weylGroupToPerm (w * s i) i.val) := by
      apply (hf _).mpr
      change 0 < f (P.root (P.weylGroupToPerm (w * RootPairing.weylGroup.ofIdx P i.val) i.val))
      rw [perm_mul, perm_reflection, reflected_value]
      exact neg_pos.mpr hi'
    have h := hup (w * s i) i hj
    rw [mul_assoc, hs, mul_one] at h
    omega
  have hdescent (w : P.weylGroup) (hw : w ≠ 1) :
      ∃ i : b.support, ¬ b.IsPos (P.weylGroupToPerm w i.val) := by
    obtain ⟨l, hl, hll, _⟩ := exists_shortest_word P b hgen w
    cases l using List.reverseRecOn with
    | nil => exact (hw hl.symm).elim
    | append_singleton l i =>
      have hprod : wordProduct P b l * s i = w := by
        simpa only [word_append, word_cons, word_nil, mul_one] using hl
      have hprev : wordProduct P b l = w * s i := by rw [← hprod, mul_assoc, hs, mul_one]
      obtain ⟨v, _, hv, hmin⟩ := exists_shortest_word P b hgen (w * s i)
      refine ⟨i, fun hi ↦ ?_⟩
      have h₁ : v.length = len (w * s i) := hv
      have h₂ : (l ++ [i]).length = len w := hll
      have h₃ := hmin l hprev
      have h₄ := hup w i hi
      simp only [List.length_append, List.length_singleton] at h₂
      omega
  have hlabel (w : P.weylGroup) (hw : Commute e.val w.val) (i : D.I) :
      e.val.indexEquiv (P.weylGroupToPerm w i) = P.weylGroupToPerm w (e.val.indexEquiv i) :=
    DFunLike.congr_fun (congrArg (RootPairing.Equiv.indexHom P) hw.eq) i
  have hbase (i : D.I) : i ∈ b.support ↔ e.val.indexEquiv i ∈ b.support := by
    let a := e.val.indexEquiv
    change i ∈ (D.base.support : Set D.I) ↔ a i ∈ (D.base.support : Set D.I)
    conv_rhs => rw [← e.property]
    exact a.injective.mem_set_image.symm
  have hroot (i : D.I) : e.val.weightEquiv.symm (P.root (e.val.indexEquiv i)) = P.root i := by
    apply e.val.weightEquiv.injective
    rw [LinearEquiv.apply_symm_apply, RootPairing.Equiv.weightEquiv_apply,
      RootPairing.Hom.root_weightMap_apply]
  have hpos (i : D.I) : b.IsPos i ↔ b.IsPos (e.val.indexEquiv i) :=
    positive_iff_of_injective P P b b e.val.indexEquiv e.val.weightEquiv.symm.toLinearMap
      e.val.weightEquiv.symm.injective hroot hbase i
  refine ⟨?_, ?_⟩
  swap
  · intro w hw
    by_contra hn
    obtain ⟨i, hi⟩ := hdescent w hn
    obtain ⟨y, hy, hpair, _⟩ := invariantRegularCocharacter D
    have h := w.val.root'_coweightEquiv (i := i.val) (y := y)
    rw [hw y (hy e)] at h
    change P.toLinearMap (P.root (P.weylGroupToPerm w i.val)) y =
      P.toLinearMap (P.root i.val) y at h
    rw [hpair, hpair] at h
    change 2 * b.height (P.weylGroupToPerm w i.val) = 2 * b.height i.val at h
    apply hi
    change 0 < b.height (P.weylGroupToPerm w i.val)
    rw [b.height_one_of_mem_support i.property] at h
    omega
  intro w
  refine ⟨fun hw ↦ (hB w).mp (hCB hw), ?_⟩
  suffices ∀ (n : ℕ) (v : P.weylGroup), len v = n → Commute e.val v.val → v ∈ C by
    exact this (len w) w rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro v hn hv
    by_cases h₁ : v = 1
    · exact h₁ ▸ C.one_mem
    obtain ⟨i, hi⟩ := hdescent v h₁
    let r := orbitWeylReflection D e i
    have hd' : len (v * r) < len v := by
      by_cases hp' : p i = i
      · change len (v * orbitWeylReflection D e i) < len v
        rw [orbitWeylReflection, ite_eq_left hp']
        exact hdown v i hi
      · have hj : ¬ b.IsPos (P.weylGroupToPerm (v * s i) (p i).val) := by
          change ¬ b.IsPos (P.weylGroupToPerm (v * RootPairing.weylGroup.ofIdx P i.val) (p i).val)
          rw [perm_mul, perm_reflection, hpref i hp', hp, ← hlabel v hv, ← hpos]
          exact hi
        change len (v * orbitWeylReflection D e i) < len v
        rw [orbitWeylReflection, ite_eq_right hp', ← mul_assoc]
        exact (hdown (v * s i) (p i) hj).trans (hdown v i hi)
    have hr : r ∈ C := Subgroup.subset_closure ⟨i, rfl⟩
    have hvr : v * r ∈ C := ih (len (v * r)) (hn ▸ hd') _ rfl (hv.mul_right (hgenComm i))
    simpa only [mul_inv_cancel_right] using C.mul_mem hvr (C.inv_mem hr)

theorem weylGroupTransport : WeylGroupTransport.{u} := by
  intro D E e
  let P := D.datum
  let Q := E.datum
  let v := e.val
  let v' := RootPairing.Equiv.symm P Q v
  let F (w : RootPairing.Aut P) := v.comp (w.comp v')
  have hF (w : RootPairing.Aut P) (x : D.X) :
      (F w).weightEquiv (v.weightEquiv x) = v.weightEquiv (w.weightEquiv x) := by
    change v.weightEquiv (w.weightEquiv (v.weightEquiv.symm (v.weightEquiv x))) = _
    rw [LinearEquiv.symm_apply_apply]
  let a : RootPairing.Aut P →* RootPairing.Aut Q :=
    { toFun := F
      map_one' := by
        apply RootPairing.Equiv.weightHom_injective Q
        ext x
        obtain ⟨x, rfl⟩ := v.weightEquiv.surjective x
        change (F 1).weightEquiv (v.weightEquiv x) = v.weightEquiv x
        rw [hF]
        rfl
      map_mul' g h := by
        apply RootPairing.Equiv.weightHom_injective Q
        ext x
        obtain ⟨x, rfl⟩ := v.weightEquiv.surjective x
        change (F (g * h)).weightEquiv (v.weightEquiv x) =
          (F g).weightEquiv ((F h).weightEquiv (v.weightEquiv x))
        rw [hF (g * h), hF h, hF g]
        rfl }
  have hi : Function.Injective a := by
    intro g h hgh
    apply RootPairing.Equiv.weightHom_injective P
    ext x
    apply v.weightEquiv.injective
    exact (hF g x).symm.trans ((congrArg (fun t : RootPairing.Aut Q ↦
      t.weightEquiv (v.weightEquiv x)) hgh).trans (hF h x))
  have hs : Function.Surjective a := by
    intro w
    let u := v'.comp (w.comp v)
    refine ⟨u, ?_⟩
    apply RootPairing.Equiv.weightHom_injective Q
    ext x
    obtain ⟨x, rfl⟩ := v.weightEquiv.surjective x
    change (F u).weightEquiv (v.weightEquiv x) = w.weightEquiv (v.weightEquiv x)
    rw [hF]
    exact v.weightEquiv.apply_symm_apply _
  have hr (i : D.I) : a (RootPairing.Equiv.reflection P i) =
      RootPairing.Equiv.reflection Q (v.indexEquiv i) := by
    apply RootPairing.Equiv.weightHom_injective Q
    ext x
    obtain ⟨x, rfl⟩ := v.weightEquiv.surjective x
    change (F (RootPairing.Equiv.reflection P i)).weightEquiv (v.weightEquiv x) =
      (RootPairing.Equiv.reflection Q (v.indexEquiv i)).weightEquiv (v.weightEquiv x)
    rw [hF, RootPairing.Equiv.reflection_weightEquiv, RootPairing.Equiv.reflection_weightEquiv]
    exact v.weightEquiv_reflection i x
  have hR : a '' Set.range (RootPairing.Equiv.reflection P) =
      Set.range (RootPairing.Equiv.reflection Q) := by
    ext w
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨v.indexEquiv i, (hr i).symm⟩
    · rintro ⟨i, rfl⟩
      obtain ⟨j, rfl⟩ := v.indexEquiv.surjective i
      exact ⟨_, ⟨j, rfl⟩, hr j⟩
  have hW : P.weylGroup.map a = Q.weylGroup := by
    unfold RootPairing.weylGroup
    rw [MonoidHom.map_closure, hR]
  let f := MulEquiv.ofBijective a ⟨hi, hs⟩
  let j := (f.subgroupMap P.weylGroup).trans (MulEquiv.subgroupCongr hW)
  refine ⟨j, fun i => ?_, fun w x => hF w.val x⟩
  exact Subtype.ext (hr i)

end PermutationBasis

section FoldedLattice

theorem saturatedInvariantLattice : SaturatedInvariantLattice.{u} := by
  intro ι τ hτ
  refine ⟨?_, ?_, ?_⟩
  · intro n y hn h i
    have hh : n * y (τ i) = n * y i := h i
    exact mul_left_cancel₀ hn hh
  · intro y i
    simp [orbitProjection, hτ i, add_comm]
  · intro y h
    funext i
    unfold orbitProjection
    rw [show y (τ i) = y i from h i]
    ring

theorem foldedTranslationLattice : FoldedTranslationLattice.{u} := by
  classical
  intro F L _ _ _ _ _ _ _ _ _ σ hσ hFL hv hfixed ι _ τ hτ
  let r := Fintype.equivFin ι
  let valF (x : Fˣ) := (integerValuationOnUnits F x).toAdd
  let valL (x : Lˣ) := (integerValuationOnUnits L x).toAdd
  let act := Units.map σ.toRingEquiv.toMonoidHom
  have ha (x : Lˣ) : (act x : L) = σ (x : L) := rfl
  have haa (x : Lˣ) : act (act x) = x := Units.ext (hσ (x : L))
  have hav (x : Lˣ) : valL (act x) = valL x := congrArg log (hv (x : L))
  let inc := Units.map (algebraMap F L).toMonoidHom
  have hinc (x : Fˣ) : act (inc x) = inc x := Units.ext (σ.commutes (x : F))
  have hinv (x : Fˣ) : valL (inc x) = 2 * valF x := by
    change log (normalizedValuation L (algebraMap F L (x : F))) =
      2 * log (normalizedValuation F (x : F))
    rw [hFL, log_pow, two_nsmul]
    omega
  have hF (n : ℤ) : ∃ x, valF x = n := integerValuationOnUnits_surj F (Multiplicative.ofAdd n)
  have hL (n : ℤ) : ∃ x, valL x = n := integerValuationOnUnits_surj L (Multiplicative.ofAdd n)
  ext y
  constructor
  · rintro ⟨u, rfl⟩
    have hu (i : ι) : u.val (τ i) = act (u.val i) := Units.ext (u.property i)
    let m (i : ι) := valL (u.val i)
    have hm (i : ι) : m (τ i) = m i := by dsimp [m]; rw [hu, hav]
    have heven (i : ι) (hi : τ i = i) : m i = 2 * (m i / 2) := by
      obtain ⟨a, ha'⟩ := hfixed (u.val i) (by simpa [hi] using (u.property i).symm)
      have he : inc a = u.val i := Units.ext ha'
      have hh := hinv a
      rw [he] at hh
      change m i = 2 * valF a at hh
      omega
    let n (i : ι) := if τ i = i then m i / 2 else if r i < r (τ i) then m i else 0
    refine ⟨n, funext fun i => ?_⟩
    change orbitProjection τ n i = (m i : ℚ) / 2
    have ht : n i + n (τ i) = m i := by
      by_cases hi : τ i = i
      · have hn : n i = m i / 2 := by simp [n, hi]
        rw [hi, hn]
        have hh := heven i hi
        omega
      · have ht' : i ≠ τ i := Ne.symm hi
        have hr : r i ≠ r (τ i) := fun e => hi (r.injective e).symm
        rcases lt_or_gt_of_ne hr with hlt | hgt
        · have hgt' : ¬ r (τ i) < r i := not_lt_of_ge hlt.le
          simp [n, hi, ht', hlt, hgt', hτ i]
        · have hlt' : ¬ r i < r (τ i) := not_lt_of_ge hgt.le
          simp [n, hi, ht', hgt, hlt', hτ i, hm i]
    unfold orbitProjection
    rw [← Int.cast_add, ht]
  · rintro ⟨n, rfl⟩
    choose a ha' using fun i : ι => hF (n i)
    choose b hb using fun i : ι => hL (n i + n (τ i))
    let u (i : ι) := if τ i = i then inc (a i)
      else if r i < r (τ i) then b i else act (b (τ i))
    have hu (i : ι) : u (τ i) = act (u i) := by
      by_cases hi : τ i = i
      · rw [hi]
        simpa [u, hi] using (hinc (a i)).symm
      · have ht' : i ≠ τ i := Ne.symm hi
        have hr : r i ≠ r (τ i) := fun e => hi (r.injective e).symm
        rcases lt_or_gt_of_ne hr with hlt | hgt
        · have hgt' : ¬ r (τ i) < r i := not_lt_of_ge hlt.le
          simp [u, hi, ht', hlt, hgt', hτ i]
        · have hlt' : ¬ r i < r (τ i) := not_lt_of_ge hgt.le
          simp [u, hi, ht', hgt, hlt', hτ i, haa]
    refine ⟨⟨u, fun i => congrArg Units.val (hu i)⟩, funext fun i => ?_⟩
    change (valL (u i) : ℚ) / 2 = orbitProjection τ n i
    have hh : valL (u i) = n i + n (τ i) := by
      by_cases hi : τ i = i
      · simp [u, hi, hinv, ha']
        omega
      · dsimp only [u]
        rw [ite_eq_right hi]
        split_ifs
        · exact hb i
        · rw [hav, hb, hτ i, add_comm]
    rw [hh, Int.cast_add]
    rfl

end FoldedLattice

section DescendedTorus

open Specs.AdjointBorelCohomology (PinnedTwist PermutedCharacterBasis IsOrbitWeilProduct
  extendedCharacterValue)
open Specs.AdjointCocharacters renaming coordinateHopf → torusCoordinateHopf
open Specs.AdjointCocharacters (coordinateHopfIso coordinateHopfMap)
open Specs.CharacterDescent (Character GeometricCharacters)
open Specs.Pinning (AttachedDatum PinnedGroup transportCharacter)
open Specs.RootGroups (AdditiveLine)
open Specs.AutomorphismSequence (AdjointQuotient SplitSequence scalarAut forgetPinning)
open CategoryTheory.MonoidalCategory
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.DiagonalizableGroups (groupAlgebra groupAlgebraMap IntegerCharacters integerGenerator)
open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct

open private charactersOfIso splitPresentation
  from LinearAlgebraicGroups.RootData.CharacterPairing
open private groupLikeIso splitBaseChange integerHopfHomEquiv integerHopfHomEquiv_generator
  from LinearAlgebraicGroups.Multiplicative.CharacterDescent
open private extendedCharacterValue_twist orbitWeilProduct characterCoordinates
  characterCoordinates_spec pointCharacters pointCharacters_equivariant
  pointCharacters_bijective from LinearAlgebraicGroups.Descent.AdjointBorelCohomology
open private pinnedScalarAligned from LinearAlgebraicGroups.Descent.AutomorphismSequence
open private coordinatePresentationMap from LinearAlgebraicGroups.Descent.AdjointCocharacters
open private specGroupMap_comp from LinearAlgebraicGroups.Affine.ClosedSubgroups

private theorem splitTorusCoordinateDiagonalizable {k : Type u} [Field k]
    (H : Specs.AffineAlgebraicGroup k) (hH : Specs.GeometricRadicals.IsSplitTorus H.val) :
    Specs.CharacterDescent.IsDiagonalizable (torusCoordinateHopf H) := by
  obtain ⟨n, ⟨i⟩⟩ := splitPresentation hH
  let L := Specs.CharacterDescent.StandardLattice.{u} n
  let C := groupAlgebra k L
  let j : specGroup C ≅ specGroup (torusCoordinateHopf H) := i ≪≫ (coordinateHopfIso H).symm
  let e := ((hopfSpec.fullyFaithful (R := CommRingCat.of k)).preimageIso j).unop
  let M : Specs.DiagonalizableGroups.FGAbelianGroup.{u} := ⟨CommGrpCat.of L, inferInstance⟩
  exact ⟨M, ⟨e.symm⟩⟩

set_option backward.isDefEq.respectTransparency false in
theorem pinnedPermutationTorus : PinnedPermutationTorus.{u} := by
  classical
  intro k K _ _ _ _ _ A P D l G B T d ι _ b r hr H
  let H₀ := closedSubgroupAlgebraicGroup P.pair.T
  let C := torusCoordinateHopf H₀
  let toCharacter := (LinearAlgebraicGroups.CharacterDescent.groupLikeCharacterEquiv C).trans
    (charactersOfIso (coordinateHopfIso H₀))
  have hC : Specs.CharacterDescent.IsDiagonalizable C :=
    splitTorusCoordinateDiagonalizable H₀ P.pair.split
  have hH : Specs.CharacterDescent.IsDiagonalizable (extendedHopf K (torusCoordinateHopf H)) := by
    obtain ⟨M, ⟨m⟩⟩ := splitBaseChange (K := K) C hC
    exact ⟨M, ⟨m ≪≫ d.torusIso⟩⟩
  let bc := MulEquiv.ofBijective
    (LinearAlgebraicGroups.CharacterDescent.baseChangeCharacterMap K C)
    (LinearAlgebraicGroups.CharacterDescent.baseChangeCharacterMap_bijective K C hC)
  let ev := (toCharacter.symm.trans bc).trans (groupLikeIso d.torusIso)
  let c := b.map ev.toAdditive.toIntLinearEquiv
  have hc (i : ι) : (c i).toMul.val =
      d.torusIso.hom.hom (extendedCharacterValue K H₀ (b i).toMul) := by
    let x := toCharacter.symm (b i).toMul
    have hx : toCharacter x = (b i).toMul := toCharacter.apply_symm_apply _
    have he : specGroupMap (integerHopfHomEquiv C x) =
        (coordinateHopfIso H₀).hom ≫ (b i).toMul := by
      change (coordinateHopfIso H₀).inv ≫ specGroupMap (integerHopfHomEquiv C x) =
        (b i).toMul at hx
      rw [← hx, Iso.hom_inv_id_assoc]
    have hχ : characterCoordinates (G := H₀) (b i).toMul = integerHopfHomEquiv C x := by
      apply (opEquiv (op C) (op (groupAlgebra k IntegerCharacters))).symm.injective
      apply (hopfSpec.fullyFaithful (R := CommRingCat.of k)).map_injective
      exact (characterCoordinates_spec (G := H₀) (b i).toMul).trans he.symm
    dsimp only [c]
    rw [Module.Basis.map_apply]
    change d.torusIso.hom.hom (1 ⊗ₜ[k] x.val) =
      d.torusIso.hom.hom (1 ⊗ₜ[k] (characterCoordinates (G := H₀) (b i).toMul).hom
        (MonoidAlgebra.of k _ integerGenerator))
    rw [hχ, integerHopfHomEquiv_generator]
  have hperm : ∀ σ i,
      (_root_.LinearAlgebraicGroups.Descent.SemilinearAction.scalarExtension (K := K)
        (torusCoordinateHopf H)).act σ (c i).toMul.val = (c (r σ i)).toMul.val := by
    intro σ i
    rw [hc, hc, extendedCharacterValue_twist]
    exact congrArg (fun χ : Character P.pair.T.group ↦
      d.torusIso.hom.hom (extendedCharacterValue K H₀ χ)) (hr σ i)
  let c' : PermutedCharacterBasis K ι H r := ⟨c, hperm⟩
  exact ⟨c', hc, hH, orbitWeilProduct c' hH⟩

set_option backward.isDefEq.respectTransparency false in
private theorem pinnedLift_character {k : Type u} [Field k] {A : AdditiveLine k} {P : PinnedGroup A}
    {D : AttachedDatum P.pair} {l : Aut D.toBased ≃* Aut P} {Q : AdjointQuotient P.pair.G}
    (E : SplitSequence P D l Q) (a : Aut D.toBased) (χ : Character P.pair.T.group) :
    transportCharacter (l a).asIso.hom.torus χ =
      Additive.toMul (a.asIso.hom.val.weightEquiv (Additive.ofMul χ)) := by
  let S := 𝟙_ (SchemeOver k)
  let v : (Specs.AutomorphismSequence.constantGroup (Aut D.toBased)).obj (op S) :=
    ⟨LocallyConstant.const _ a⟩
  let f := scalarAut (Functor.mapAut P (forgetPinning (A := A)) (l a)) S
  have h := ConcreteCategory.congr_hom (congrArg (fun n => n.app (op S)) E.rightInverse) v
  change E.toExactSequence.outer.app (op S) (E.sectionMap.app (op S) v) = v at h
  rw [E.sectionOnConstants] at h
  let U : Over S := Over.mk (CategoryTheory.CartesianMonoidalCategory.toUnit P.pair.T.group.X)
  have ht := (E.latticeAction S f (pinnedScalarAligned (l a) S) a h).1 χ U (𝟙 _)
  apply Grp.hom_ext
  change ((𝟙 P.pair.T.group.X) ≫ (l a).asIso.hom.torus.inv.hom.hom) ≫ χ.hom.hom =
    (𝟙 P.pair.T.group.X) ≫
      (Additive.toMul (a.asIso.hom.val.weightEquiv (Additive.ofMul χ))).hom.hom at ht
  simpa only [transportCharacter, Grp.comp_hom_hom, Category.id_comp] using ht

set_option backward.isDefEq.respectTransparency false in
theorem markedPinnedTorus : MarkedPinnedTorus.{u} := by
  classical
  intro k K _ _ _ _ _ D A P l Q E G B T d b hb r H
  letI := D.finiteRoots
  let β := (characterBasis D b).map P.datumIso.val.weightEquiv
  have hβ (i : D.base.support) : β i = P.datumIso.val.weightEquiv (characterBasis D b i) :=
    Module.Basis.map_apply _ _ _
  have h (σ : Gal(K/k)) (i : D.base.support) :
      transportCharacter (l (d.outer σ)).asIso.hom.torus (β i).toMul = (β (r σ i)).toMul := by
    rw [pinnedLift_character E]
    let a := ((markedDiagramEquiv P) (d.outer σ)).asIso.hom
    have hi : r σ i = simplePermutation D a i := rfl
    have he (x : D.X) : P.datumIso.val.weightEquiv (a.val.weightEquiv x) =
        (d.outer σ).asIso.hom.val.weightEquiv (P.datumIso.val.weightEquiv x) := by
      change P.datumIso.val.weightEquiv (P.datumIso.val.weightEquiv.symm
        ((d.outer σ).asIso.hom.val.weightEquiv (P.datumIso.val.weightEquiv x))) = _
      exact LinearEquiv.apply_symm_apply _ _
    change Additive.toMul ((d.outer σ).asIso.hom.val.weightEquiv (β i)) = (β (r σ i)).toMul
    rw [hβ, hβ, ← he, (basedPermutation D a b hb i).2, hi]
  obtain ⟨c, hc, hH, hp⟩ := pinnedPermutationTorus d β r h
  refine ⟨c, fun i ↦ ?_, hH, hp⟩
  exact (hc i).trans (congrArg (fun χ : Additive (Character P.pinned.pair.T.group) ↦
    d.torusIso.hom.hom (extendedCharacterValue K (closedSubgroupAlgebraicGroup P.pinned.pair.T)
      χ.toMul)) (hβ i))

set_option backward.isDefEq.respectTransparency false in
theorem markedPinnedDiagramAction : MarkedPinnedDiagramAction.{u} := by
  intro k _ D A P l Q E a
  letI := P.attached.comm
  let r := markedDiagramEquiv P
  let e := (r a).asIso.hom
  let s := (l a).asIso.hom
  let d := P.datumIso.val
  let χ (x : D.X) := Additive.toMul (d.weightEquiv x)
  have hχ (x : D.X) : transportCharacter s.torus (χ x) = χ (e.val.weightEquiv x) := by
    rw [pinnedLift_character E]
    change Additive.toMul (a.asIso.hom.val.weightEquiv (d.weightEquiv x)) =
      Additive.toMul (d.weightEquiv (d.weightEquiv.symm (a.asIso.hom.val.weightEquiv (d.weightEquiv x))))
    rw [LinearEquiv.apply_symm_apply]
  have hsimple (i : D.base.support) : χ (D.datum.root i.val) = (P.simpleRoot i).val.val := by
    apply Additive.ofMul.injective
    exact (RootPairing.Hom.root_weightMap_apply D.datum P.attached.datum.rootDatum i.val d.toHom).trans
      (P.attached.datum.root_eq _)
  refine ⟨fun i => ?_, fun b hb i => ?_, fun ha i => ?_⟩
  · rw [← hsimple, ← hsimple, hχ]
    congr 1
    exact RootPairing.Hom.root_weightMap_apply D.datum D.datum i.val e.val.toHom
  · change transportCharacter s.torus (χ (characterBasis D b i)) =
      χ (characterBasis D b (simplePermutation D e i))
    rw [hχ, (basedPermutation D e b hb i).2]
  · have he : r a * r a = 1 := (map_mul r a a).symm.trans ((congrArg r ha).trans (map_one r))
    exact congrArg (fun f : Aut D => f.asIso.hom.val.indexEquiv i) he

theorem permutationTorusPoints : PermutationTorusPoints.{u} := by
  intro k K _ _ _ _ ι r H c hH R
  let f (x : torusCoordinateHopf H →ₐ[k] R) : equivariantUnits r R :=
    ⟨pointCharacters R c x, pointCharacters_equivariant R c x⟩
  exact ⟨Equiv.ofBijective f (pointCharacters_bijective R c hH), fun _ _ ↦ rfl⟩

theorem rationalPermutationTorusPoints : RationalPermutationTorusPoints.{u} := by
  intro k K _ _ _ _ ι r H c hH
  let R := CommAlgCat.of k k
  obtain ⟨e, he⟩ := permutationTorusPoints c hH R
  let a := Algebra.TensorProduct.rid k K K
  let u := Units.mapEquiv a.toMulEquiv
  let j : (ι → (K ⊗[k] k)ˣ) ≃ (ι → Kˣ) := Equiv.piCongrRight (fun _ ↦ u.toEquiv)
  have ha (σ : Gal(K/k)) (x : K ⊗[k] k) :
      a (Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id k k) x) = σ (a x) := by
    induction x using TensorProduct.inductionOn with
    | tmul x y =>
      change y • σ x = σ (y • x)
      simp [Algebra.smul_def]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hc : ∀ v, v ∈ equivariantUnits r R ↔ ∀ (σ : Gal(K/k)) i,
      (j v (r σ i) : K) = σ (j v i : K) := by
    intro v
    constructor
    · intro h σ i
      have h' := congrArg (fun z : (K ⊗[k] k)ˣ ↦ a z.val) (h σ i)
      exact h'.trans (ha σ (v i).val)
    · intro h σ i
      apply Units.ext
      apply a.injective
      exact (h σ i).trans (ha σ (v i).val).symm
  refine ⟨e.trans (j.subtypeEquiv hc), fun f i ↦ ?_⟩
  exact congrArg a (he f i)

open Coalgebra
open _root_.LinearAlgebraicGroups.CharacterDescent
  (baseChangeCharacterMap baseChangeCharacterMap_bijective groupAlgebraBaseChange
    scalarExtensionDatum mapGroupLike geometricAction extendedHopfFunctor)
open _root_.LinearAlgebraicGroups.Descent (SemilinearAction)
open private groupLikeSpanOfSplit groupAlgebraOfCharacters groupAlgebraOfCharacters_hom_single
  descendEquivariantHopfMap extendedHopfMap_equivariant extendedHopfFunctor_faithful
  geometricHopfMaps_ext from LinearAlgebraicGroups.Multiplicative.CharacterDescent
open private groupLikeEvaluation_basis_ext from LinearAlgebraicGroups.Descent.AdjointBorelCohomology
open private latticeCoordinates integerExponent integerExponent_zpow
  from LinearAlgebraicGroups.RootData.CharacterPairing
open private liftCharacters liftCharacters_single from LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups

private theorem equivariantHopfMap_of_basis {k K : Type u} [Field k] [Field K] [Algebra k K]
    {I : Type u} {r : Gal(K/k) →* Equiv.Perm I} {H : Specs.AffineAlgebraicGroup k}
    (c : PermutedCharacterBasis K I H r) {A : HopfAlgebraCategory k}
    (hH : Specs.CharacterDescent.IsDiagonalizable (extendedHopf K (torusCoordinateHopf H)))
    (f : extendedHopf K (torusCoordinateHopf H) ⟶ extendedHopf K A)
    (hf : ∀ σ i, f.hom (c.basis (r σ i)).toMul.val =
      (SemilinearAction.scalarExtension (k := k) (K := K) A).act σ (f.hom (c.basis i).toMul.val)) :
    (scalarExtensionDatum K (torusCoordinateHopf H)).Equivariant (scalarExtensionDatum K A) f := by
  intro σ x
  let C := torusCoordinateHopf H
  let a := SemilinearAction.scalarExtension (k := k) (K := K) C
  let b := SemilinearAction.scalarExtension (k := k) (K := K) A
  let p := (geometricAction K C σ).asHom.hom
  let t := (geometricAction K A σ).asHom.hom
  have h : (mapGroupLike f).comp p = t.comp (mapGroupLike f) := by
    apply groupLikeEvaluation_basis_ext c.basis
    intro i
    apply GroupLike.val_injective
    change f.hom (a.act σ (c.basis i).toMul.val) = b.act σ (f.hom (c.basis i).toMul.val)
    rw [show a.act σ (c.basis i).toMul.val = (c.basis (r σ i)).toMul.val from c.permutation σ i]
    exact hf σ i
  have hl : f.hom.toLinearMap.comp (a.operator σ) = (b.operator σ).comp f.hom.toLinearMap := by
    apply LinearMap.ext_on_range (groupLikeSpanOfSplit _ hH)
    intro y
    exact congrArg GroupLike.val (DFunLike.congr_fun h y)
  exact DFunLike.congr_fun hl x

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 500000 in
theorem permutationSplitSubtorus : PermutationSplitSubtorus.{u} := by
  classical
  intro k K _ _ _ _ ι _ r H c hH M A
  let O := OrbitIndices r
  let C := torusCoordinateHopf H
  let E := extendedHopf K C
  let z (o : O) : O →₀ ℤ := Finsupp.single o 1
  let ℓ := c.basis.constr ℤ (fun i ↦ z (orbitIndex r i))
  let m : GroupLike K E →* M := ℓ.toAddMonoidHom.toMultiplicative
  have hm (i : ι) : m (c.basis i).toMul = Multiplicative.ofAdd (z (orbitIndex r i)) :=
    congrArg Multiplicative.ofAdd (c.basis.constr_basis ℤ (fun i ↦ z (orbitIndex r i)) i)
  have hmsurj : Function.Surjective m := by
    have hℓ : Function.Surjective ℓ := by
      apply LinearMap.range_eq_top.mp
      apply top_unique
      rw [← (Finsupp.basisSingleOne : Module.Basis O ℤ (O →₀ ℤ)).span_eq]
      apply Submodule.span_le.mpr
      rintro _ ⟨o, rfl⟩
      obtain ⟨i, rfl⟩ := Quotient.exists_rep o
      exact ⟨c.basis i, c.basis.constr_basis ℤ (fun i ↦ z (orbitIndex r i)) i⟩
    intro x
    obtain ⟨y, hy⟩ := hℓ x.toAdd
    exact ⟨y.toMul, congrArg Multiplicative.ofAdd hy⟩
  have hspan := groupLikeSpanOfSplit E hH
  let e := groupAlgebraOfCharacters E hspan
  let v : extendedHopf K A ≅ groupAlgebra K M :=
    CommHopfAlgCat.isoMk (groupAlgebraBaseChange k K M)
  let f : E ⟶ extendedHopf K A := e.inv ≫ groupAlgebraMap K m ≫ v.inv
  have hf (x : GroupLike K E) : f.hom x.val = (1 : K) ⊗ₜ[k] MonoidAlgebra.of k M (m x) := by
    rw [← groupAlgebraOfCharacters_hom_single K hspan x]
    change (e.hom ≫ f).hom (MonoidAlgebra.single x 1) = _
    simp only [f, Iso.hom_inv_id_assoc]
    change (groupAlgebraBaseChange k K M).symm
      (MonoidAlgebra.mapDomainBialgHom K m (MonoidAlgebra.single x 1)) = _
    rw [MonoidAlgebra.mapDomainBialgHom_single]
    exact MonoidAlgebra.scalarTensorEquiv_symm_single (R := k) (A := K) (m x) 1
  have hσ (σ : Gal(K/k)) (i : ι) : orbitIndex r (r σ i) = orbitIndex r i :=
    Quotient.sound ⟨σ, rfl⟩
  have heq : (scalarExtensionDatum K C).Equivariant (scalarExtensionDatum K A) f := by
    apply equivariantHopfMap_of_basis c hH f
    intro σ i
    rw [hf, hf, hm, hm, hσ]
    change _ = σ 1 ⊗ₜ[k] _
    rw [map_one] <;> rfl
  obtain ⟨q, hq⟩ := descendEquivariantHopfMap K f heq
  have hqsurj : Function.Surjective q.hom := by
    apply (Module.FaithfullyFlat.lTensor_surjective_iff_surjective k K q.hom.toLinearMap).mp
    change Function.Surjective (extendedHopfMap K q).hom
    rw [hq]
    have hmap : Function.Surjective (groupAlgebraMap K m).hom := by
      intro x
      obtain ⟨y, hy⟩ := Finsupp.mapDomain_surjective (M := K) hmsurj x.coeff
      refine ⟨MonoidAlgebra.ofCoeff y, ?_⟩
      change MonoidAlgebra.ofCoeff (Finsupp.mapDomain m y) = x
      rw [hy]
    exact (CommHopfAlgCat.ofIso v).symm.surjective.comp
      (hmap.comp (CommHopfAlgCat.ofIso e).symm.surjective)
  refine ⟨q, hqsurj, ?_, ?_, fun i ↦ ?_⟩
  · letI : IsClosedImmersion (specGroupMap q).hom.hom.left := (hopfMapClosedImmersion k q).mpr hqsurj
    let F := Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))
    letI : IsIso (coordinateHopfIso H).hom.hom.hom.left := F.map_isIso (coordinateHopfIso H).hom
    change IsClosedImmersion ((specGroupMap q).hom.hom.left ≫ (coordinateHopfIso H).hom.hom.hom.left)
    exact IsClosedImmersion.comp _ _
  · letI : Finite O := Finite.of_surjective (orbitIndex r) Quotient.exists_rep
    letI := Fintype.ofFinite O
    let n := Fintype.card O
    let i : (O →₀ ℤ) ≃ₗ[ℤ] (Fin n → ℤ) := Finsupp.linearEquivFunOnFinite ℤ ℤ O |>.trans
      (LinearEquiv.piCongrLeft' ℤ (fun _ : O ↦ ℤ) (Fintype.equivFin O))
    let j : M ≃* Specs.CharacterDescent.StandardLattice.{u} n :=
      (i.trans (latticeCoordinates n).symm).toAddEquiv.toMultiplicative
    obtain ⟨d⟩ := _root_.LinearAlgebraicGroups.CharacterDescent.standardSplitTorus (k := k) n
    let g := CommHopfAlgCat.isoMk (MonoidAlgebra.domCongrBialgEquiv k k j.symm)
    exact ⟨n, ⟨(hopfSpec (CommRingCat.of k)).mapIso g.op ≪≫ d⟩⟩
  · rw [hq, hf, hm]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 500000 in
theorem permutationSplitFactorization : PermutationSplitFactorization.{u} := by
  classical
  intro k K _ _ _ _ ι r H c hH M A q hqs hq B hB f
  let O := OrbitIndices r
  let C := torusCoordinateHopf H
  let fK := extendedHopfMap K f
  let p := mapGroupLike fK
  let e := MulEquiv.ofBijective (baseChangeCharacterMap K B) (baseChangeCharacterMap_bijective K B hB)
  have hf (σ : Gal(K/k)) (i : ι) : p (c.basis (r σ i)).toMul = p (c.basis i).toMul := by
    apply GroupLike.val_injective
    change fK.hom (c.basis (r σ i)).toMul.val = (p (c.basis i).toMul).val
    rw [← c.permutation]
    have hp := extendedHopfMap_equivariant K f σ (c.basis i).toMul.val
    change fK.hom ((SemilinearAction.scalarExtension (K := K) C).act σ (c.basis i).toMul.val) =
      (SemilinearAction.scalarExtension (K := K) B).act σ (p (c.basis i).toMul).val at hp
    rw [hp]
    obtain ⟨x, hx⟩ := e.surjective (p (c.basis i).toMul)
    rw [← hx]
    change σ 1 ⊗ₜ[k] x.val = (1 : K) ⊗ₜ[k] x.val
    rw [map_one]
  have hi (i : ι) : p (c.basis (orbitIndex r i).out).toMul = p (c.basis i).toMul := by
    obtain ⟨σ, hσ⟩ := Quotient.exact (Quotient.out_eq (orbitIndex r i)).symm
    change r σ (orbitIndex r i).out = i at hσ
    exact (hf σ (orbitIndex r i).out).symm.trans (by rw [hσ])
  let basis : Module.Basis O ℤ (O →₀ ℤ) := Finsupp.basisSingleOne
  let L := basis.constr ℤ (fun o ↦ Additive.ofMul (e.symm (p (c.basis o.out).toMul)))
  let m : M →* GroupLike k B := L.toAddMonoidHom.toMultiplicative
  let g : A ⟶ B := CommHopfAlgCat.ofHom (liftCharacters m)
  have hg (o : O) : g.hom (MonoidAlgebra.of k M (Multiplicative.ofAdd (Finsupp.single o 1))) =
      (e.symm (p (c.basis o.out).toMul)).val := by
    change liftCharacters m (MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single o 1)) 1) = _
    rw [liftCharacters_single]
    exact congrArg (fun x : Additive (GroupLike k B) ↦ x.toMul.val)
      (basis.constr_basis ℤ (fun o ↦ Additive.ofMul (e.symm (p (c.basis o.out).toMul))) o)
  have heq : q ≫ g = f := by
    haveI := extendedHopfFunctor_faithful (k := k) K
    apply (extendedHopfFunctor (k := k) K).map_injective
    change extendedHopfMap K (q ≫ g) = fK
    rw [show extendedHopfMap K (q ≫ g) = extendedHopfMap K q ≫ extendedHopfMap K g from
      (extendedHopfFunctor (k := k) K).map_comp q g]
    apply geometricHopfMaps_ext K hH
    apply DFunLike.congr_fun
    apply groupLikeEvaluation_basis_ext c.basis
    intro i
    apply GroupLike.val_injective
    change (extendedHopfMap K g).hom ((extendedHopfMap K q).hom (c.basis i).toMul.val) =
      (p (c.basis i).toMul).val
    rw [hq]
    change (1 : K) ⊗ₜ[k] g.hom (MonoidAlgebra.of k M
      (Multiplicative.ofAdd (Finsupp.single (orbitIndex r i) 1))) = _
    rw [hg]
    exact congrArg GroupLike.val ((e.apply_symm_apply _).trans (hi i))
  refine ⟨g, heq, fun v hv ↦ ?_⟩
  apply CommHopfAlgCat.hom_ext
  apply BialgHom.ext
  intro x
  obtain ⟨a, rfl⟩ := hqs x
  exact ConcreteCategory.congr_hom (hv.trans heq.symm) a

set_option backward.isDefEq.respectTransparency false in
theorem orbitTorusCocharacters : OrbitTorusCocharacters.{u} := by
  classical
  intro k K _ _ _ ι r H c M A q hq y
  let O := OrbitIndices r
  let C := groupAlgebra k IntegerCharacters.{u}
  let v (o : O) := Multiplicative.ofAdd (Finsupp.single o (1 : ℤ))
  have he (z : A ⟶ C) (i : ι) :
      (extendedHopfMap K (q ≫ z)).hom (c.basis i).toMul.val =
        (1 : K) ⊗ₜ[k] z.hom (MonoidAlgebra.of k M (v (orbitIndex r i))) := by
    rw [show extendedHopfMap K (q ≫ z) = extendedHopfMap K q ≫ extendedHopfMap K z from
      (extendedHopfFunctor (k := k) K).map_comp q z]
    change (extendedHopfMap K z).hom ((extendedHopfMap K q).hom (c.basis i).toMul.val) = _
    rw [hq]
    rfl
  constructor
  · intro hy
    let f : O → ℤ := Quotient.lift y (by
      intro i j h
      obtain ⟨σ, hσ⟩ := h
      change r σ j = i at hσ
      rw [← hσ, hy])
    let basis : Module.Basis O ℤ (O →₀ ℤ) := Finsupp.basisSingleOne
    let d := basis.constr ℤ f
    let t : M →* IntegerCharacters.{u} :=
      MulEquiv.ulift.symm.toMonoidHom.comp d.toAddMonoidHom.toMultiplicative
    refine ⟨groupAlgebraMap k t, fun i ↦ ?_⟩
    rw [he]
    congr 1
    change MonoidAlgebra.mapDomainBialgHom k t (MonoidAlgebra.single (v (orbitIndex r i)) 1) = _
    rw [MonoidAlgebra.mapDomainBialgHom_single]
    congr 1
    apply integerExponent.injective
    rw [integerExponent_zpow]
    change d (basis (orbitIndex r i)) = y i
    exact basis.constr_basis ℤ f _
  · rintro ⟨z, hz⟩ σ i
    have hi : orbitIndex r (r σ i) = orbitIndex r i := Quotient.sound ⟨σ, rfl⟩
    have h₁ := (hz (r σ i)).symm.trans (he z (r σ i))
    rw [hi] at h₁
    have h₂ := (h₁.trans (he z i).symm).trans (hz i)
    apply (integerExponent_zpow (y (r σ i))).symm.trans
    apply Eq.trans _ (integerExponent_zpow (y i))
    apply congrArg integerExponent
    apply (MonoidAlgebra.single_left_injective (R := k) one_ne_zero)
    exact Algebra.TensorProduct.includeRight_injective (A := K) (algebraMap k K).injective h₂

set_option backward.isDefEq.respectTransparency false in
theorem largestSplitPermutationSubtorus : LargestSplitPermutationSubtorus.{u} := by
  intro k K _ _ _ _ ι _ r G T H c hc M A
  obtain ⟨q, hq, h, hs, hcoord⟩ := permutationSplitSubtorus c hc
  let i := specGroupMap q ≫ (coordinateHopfIso H).hom
  let S := Specs.GeometricBorelConjugacy.subgroupOfSubgroup T ⟨specGroup A, i, h⟩
  refine ⟨q, h, hs, ⟨i, rfl⟩, ?_, hcoord⟩
  intro U hU hUT
  obtain ⟨u, hu⟩ := hUT
  let H' := closedSubgroupAlgebraicGroup U
  let B := torusCoordinateHopf H'
  let f := coordinateHopfMap (G := H') (H := H) u
  obtain ⟨g, hg, _⟩ := permutationSplitFactorization c hc q hq hcoord B
    (splitTorusCoordinateDiagonalizable H' hU) f
  let p := (coordinateHopfIso H').inv ≫ specGroupMap g
  have hp : p ≫ i = u := by
    dsimp only [p, i]
    simp only [Category.assoc]
    rw [← Category.assoc (specGroupMap g), ← specGroupMap_comp, hg, coordinatePresentationMap]
    simp
  refine ⟨p, ?_⟩
  change p ≫ i ≫ T.inclusion = U.inclusion
  rw [← Category.assoc, hp, hu]

end DescendedTorus

section PinnedPoints

open Specs.AdjointCocharacters renaming coordinateHopf → affineCoordinateHopf
open _root_.LinearAlgebraicGroups.Descent (SemilinearAction)
open scoped TensorProduct
open private extendCoordinatePoint extendCoordinatePoint_injective extendCoordinatePoint_equivariant
  exists_extendCoordinatePoint from LinearAlgebraicGroups.Descent.AdjointBorelCohomology

set_option backward.isDefEq.respectTransparency false in
theorem pinnedCoordinateFixedPoints : PinnedCoordinateFixedPoints.{u} := by
  intro k K _ _ _ _ A P D l G B T d R
  let X := affineCoordinateHopf P.pair.G
  let Y := affineCoordinateHopf G
  let e := (CommHopfAlgCat.ofIso d.groupIso).toAlgEquiv
  let a := SemilinearAction.scalarExtension (k := k) (K := K) Y
  have h (σ : Gal(K/k)) (x : extendedHopf K X) :
      a.act σ (e x) = e (pinnedCoordinateAction d σ x) := d.twistedAction σ x
  constructor
  · intro f g hfg
    apply extendCoordinatePoint_injective (K := K) R
    apply AlgHom.ext
    intro x
    obtain ⟨y, rfl⟩ := e.surjective x
    exact DFunLike.congr_fun hfg y
  · intro f
    constructor
    · rintro ⟨g, rfl⟩ σ x
      change extendCoordinatePoint R g (e (pinnedCoordinateAction d σ x)) = _
      rw [← h]
      exact extendCoordinatePoint_equivariant R g σ (e x)
    · intro hf
      let g : extendedHopf K Y →ₐ[K] K ⊗[k] R := f.comp e.symm.toAlgHom
      have hg (σ : Gal(K/k)) (x : extendedHopf K Y) :
          g (a.act σ x) = (SemilinearAction.scalarExtension (K := K) R).act σ (g x) := by
        obtain ⟨y, rfl⟩ := e.surjective x
        rw [h]
        change f (e.symm (e (pinnedCoordinateAction d σ y))) =
          (SemilinearAction.scalarExtension (K := K) R).act σ (f (e.symm (e y)))
        rw [e.symm_apply_apply, e.symm_apply_apply]
        exact hf σ y
      obtain ⟨q, hq⟩ := exists_extendCoordinatePoint (A := Y) R g hg
      refine ⟨q, AlgHom.ext fun x ↦ ?_⟩
      change extendCoordinatePoint R q (e x) = f x
      rw [hq]
      exact congrArg f (e.symm_apply_apply x)

end PinnedPoints

section ValuationComparisons

open AlgebraicGeometry Opposite
open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel (Integers IntegralAlgebra IntegralScheme TorusValues
  integralSpec integerAlgebra splitTorus torusPoint)
attribute [local instance] integerAlgebra

theorem integralTorusCoordinates : IntegralTorusCoordinates.{u} := by
  classical
  intro K _ _ _ _ D ι _ b t O R
  obtain ⟨e, he, _⟩ := torusBasisCoordinates D b R
  obtain ⟨f, hf, _⟩ := torusBasisCoordinates D b (CommAlgCat.of Integers.{u} K)
  let j := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  have h (x : K) : normalizedValuation K x = 1 ↔ valuation K x = 1 := by
    change j (valuation K x) = 1 ↔ _
    rw [← map_one j]
    exact j.injective.eq_iff
  constructor
  · intro ht
    let v (i : ι) : O.unitGroup :=
      ⟨f t i, (Valuation.mem_unitGroup_iff _ (valuation K) (f t i)).mpr (by
        rw [hf]; exact (h _).mp (ht i))⟩
    let s := e.symm (fun i => O.unitGroupMulEquiv (v i))
    refine ⟨s, f.injective (funext fun i => ?_)⟩
    rw [hf, MonoidHom.comp_apply, ← he, MulEquiv.apply_symm_apply]
    apply Units.ext
    exact O.coe_unitGroupMulEquiv_apply (v i)
  · rintro ⟨s, rfl⟩ i
    let z := s (Multiplicative.ofAdd (characterBasis D b i))
    apply (h _).mpr
    let a := O.unitGroupMulEquiv.symm z
    have hz : Units.map O.subtype.toMonoidHom z = a.val := by
      apply Units.ext
      exact (O.coe_unitGroupMulEquiv_symm_apply z).symm
    change valuation K (↑(Units.map O.subtype.toMonoidHom z) : K) = 1
    rw [hz]
    exact (Valuation.mem_unitGroup_iff _ (valuation K) a.val).mp a.property

attribute [-instance] integerAlgebra in
private theorem integralClosedPoint {X Y : IntegralScheme.{u}} (m : X ⟶ Y)
    [IsClosedImmersion m.left] {R S : IntegralAlgebra.{u}} [IsReduced R]
    (f : R ⟶ S) (hf : Function.Injective f.hom) (p : integralSpec.obj (op R) ⟶ Y)
    (q : integralSpec.obj (op S) ⟶ X) (h : integralSpec.map f.op ≫ p = q ≫ m) :
    ∃ q₀ : integralSpec.obj (op R) ⟶ X, q₀ ≫ m = p := by
  let j := (integralSpec.map f.op).left
  have : IsDominant j := by
    change IsDominant (Spec.map (CommRingCat.ofHom f.hom.toRingHom))
    rw [isDominant_iff]
    apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr
    change RingHom.ker f.hom.toRingHom ≤ nilradical R
    rw [(RingHom.injective_iff_ker_eq_bot f.hom.toRingHom).mp hf]
    exact bot_le
  have : IsReduced (integralSpec.obj (op R)).left := by
    change IsReduced (Spec (CommRingCat.of R))
    infer_instance
  have : IsSchemeTheoreticallyDominant j := .of_isDominant j
  have hj : (j ≫ p.left).ker = p.left.ker := by
    rw [Scheme.Hom.ker_comp, j.ker_eq_bot, Scheme.IdealSheafData.map_bot]
  have hh : j ≫ p.left = q.left ≫ m.left := congrArg Over.Hom.left h
  have hker : m.left.ker ≤ p.left.ker := by
    rw [← hj, hh]
    exact q.left.le_ker_comp m.left
  let t := IsClosedImmersion.lift m.left p.left hker
  have ht : t ≫ m.left = p.left := IsClosedImmersion.lift_fac _ _ _
  refine ⟨Over.homMk t ?_, Over.OverMorphism.ext ht⟩
  rw [← Over.w m, ← Category.assoc, ht, Over.w p]

open scoped CategoryTheory.MonObj in
open private affineTorusPointEquiv torusPoint_natural
  from LinearAlgebraicGroups.Classification.IntegralSemisimpleModel in
set_option backward.isDefEq.respectTransparency false in
theorem markedIntegralTorusKernel : MarkedIntegralTorusKernel.{u} := by
  intro K _ _ _ _ D M I _ b O R S f t
  have h := integralTorusCoordinates D b t
  let m := M.torus.hom.hom
  have hval : f.hom.toMonoidHom = O.subtype.toMonoidHom := rfl
  constructor
  · intro hu
    obtain ⟨v, hv⟩ := h.mp hu
    refine ⟨torusPoint D R v ≫ m, ?_⟩
    change integralSpec.map f.op ≫ torusPoint D R v ≫ m = torusPoint D S t ≫ m
    rw [← Category.assoc, torusPoint_natural, hval, hv]
  · rintro ⟨p, hp⟩
    have hm : IsClosedImmersion m.left := M.torusClosed
    letI : Mono m := Over.mono_of_mono_left _
    have hf : Function.Injective f.hom := Subtype.val_injective
    change integralSpec.map f.op ≫ p = torusPoint D S t ≫ m at hp
    obtain ⟨q, hq⟩ := integralClosedPoint m f hf p (torusPoint D S t) hp
    obtain ⟨v, hv⟩ := (affineTorusPointEquiv (k := Integers.{u}) (M := Multiplicative D.X) R).surjective q
    have hq' : torusPoint D R v ≫ m = p := (congrArg (· ≫ m) hv).trans hq
    have he : torusPoint D S ((Units.map O.subtype.toMonoidHom).comp v) = torusPoint D S t := by
      apply (cancel_mono m).mp
      rw [← hval, ← torusPoint_natural, Category.assoc, hq', hp]
    exact h.mpr ⟨v, (affineTorusPointEquiv (k := Integers.{u}) S).injective he⟩

theorem foldedCharacterTranslation : FoldedCharacterTranslation.{u} := by
  classical
  intro K _ _ _ _ D ι _ b t x
  obtain ⟨e, he, hcoords⟩ := torusBasisCoordinates D b (CommAlgCat.of Integers.{u} K)
  have ht : t (Multiplicative.ofAdd x) =
      ∏ i, (e t i) ^ (D.datum.toLinearMap x (b i)) := by
    simpa only [e.symm_apply_apply] using hcoords (e t) x
  let n := integerValuationOnUnits K
  let m (i : ι) := D.datum.toLinearMap x (b i)
  simp_rw [← he]
  change (∑ i, ((n (e t i)).toAdd : ℚ) / 2 * (m i : ℚ)) =
    ((n (t (Multiplicative.ofAdd x))).toAdd : ℚ) / 2
  rw [ht, map_prod, toAdd_prod, Int.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zpow, toAdd_zpow, zsmul_eq_mul, Int.cast_mul]
  dsimp only [m]
  simp only [Int.cast_id]
  ring

end ValuationComparisons

section MarkedFibre

open AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Specs.AdjointRepresentation (GroupPoints)
open Specs.IntegralSemisimpleModel (Integers Model TorusValues fibre forgetFibrePoint integerAlgebra
  splitTorus torusPoint)

attribute [local instance] integerAlgebra

open private affineTorusPointEquiv fibrePointsEquiv forgetFibrePoint_comp
  from LinearAlgebraicGroups.Classification.IntegralSemisimpleModel

set_option backward.isDefEq.respectTransparency false in
theorem markedFibreTorusCoordinates : MarkedFibreTorusCoordinates.{u} := by
  intro k _ D M A P g s hT hχ
  let f (R : TestAlgebra k) :=
    (affineTorusPointEquiv (k := Integers.{u}) (M := Multiplicative D.X) R).trans
      (fibrePointsEquiv (splitTorus D) R).symm
  have hf (R : TestAlgebra k) v :
      forgetFibrePoint (splitTorus D) R (f R v) =
        torusPoint D (CommAlgCat.of Integers.{u} R) v :=
    (fibrePointsEquiv (splitTorus D) R).apply_symm_apply _
  let e (R : TestAlgebra k) := (f R).trans
    (((groupPointsFunctor k).mapIso s).app R).groupIsoToMulEquiv
  have he (R : TestAlgebra k) v : e R v = f R v ≫ s.hom.hom.hom := rfl
  refine ⟨e, fun R v x => hχ R (f R v) v (hf R v) x, ?_⟩
  intro R v
  have hs : P.pinned.pair.T.inclusion ≫ g.inv = s.inv ≫ (fibre k).map M.torus := by
    rw [Iso.comp_inv_eq, Category.assoc, hT, Iso.inv_hom_id_assoc]
  have hs' := congrArg (fun a => a.hom.hom) hs
  change P.pinned.pair.T.inclusion.hom.hom ≫ g.inv.hom.hom =
    s.inv.hom.hom ≫ ((fibre k).map M.torus).hom.hom at hs'
  rw [he, Category.assoc, hs', ← Category.assoc, ← Category.assoc]
  have hi : s.hom.hom.hom ≫ s.inv.hom.hom = 𝟙 _ := by
    exact congrArg (fun a => a.hom.hom) s.hom_inv_id
  rw [Category.assoc (f R v) _ _, hi, Category.comp_id, forgetFibrePoint_comp, hf]

end MarkedFibre

section IntegralReflections

open AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix
open Specs.IntegralSemisimpleModel (IntegralAlgebra IntegralMarking IntegralPoints Integers TorusValues
  integralPointFunctor torusPoint cocharacter rankOnePoints)
open Specs.IntegralRootRelations (upper lower diagonal)
open private affineTorusPointEquiv from LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
open private matrixWord matrixWord_factor from LinearAlgebraicGroups.Classification.IntegralFibreDatum

set_option backward.isDefEq.respectTransparency false in
theorem integralWeylWordConjugation : IntegralWeylWordConjugation.{u} := by
  intro D M a
  constructor
  · intro R S f u
    have hu : Matrix.SpecialLinearGroup.map f.hom.toRingHom (matrixWord u) =
        matrixWord (Units.map f.hom.toMonoidHom u) := by
      have h₁ (x : R) : Matrix.SpecialLinearGroup.map f.hom.toRingHom (upper x) =
          upper (f.hom x) := by
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.map, upper]
      have h₂ (x : R) : Matrix.SpecialLinearGroup.map f.hom.toRingHom (lower x) =
          lower (f.hom x) := by
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.map, lower]
      unfold matrixWord
      rw [map_mul, map_mul, h₁, h₂, map_neg]
      rfl
    have h := ConcreteCategory.congr_hom ((M.rankOne a).naturality f) (matrixWord u)
    change (M.rankOne a).app S (Matrix.SpecialLinearGroup.map f.hom.toRingHom (matrixWord u)) =
      (integralPointFunctor M.group).map f (markedWeylWord M a R u) at h
    rw [hu] at h
    exact h.symm
  · intro R t x n
    let p : TorusValues D R →* IntegralPoints M.group R :=
      (IsMonHom.monoidHom M.torus.hom.hom _).comp
        (affineTorusPointEquiv (k := Integers.{u}) R).toMonoidHom
    let w (s : Rˣ) : IntegralPoints M.group R := markedWeylWord M a R s
    let X (b : D.I) (z : R) : IntegralPoints M.group R := M.line.point R z ≫ (M.root b).hom.hom
    let c := D.datum.reflectionPerm a a
    let α (v : TorusValues D R) := v (Multiplicative.ofAdd (D.datum.root a))
    have hword (s : Rˣ) : w s = X a s * X c (-(↑s⁻¹ : R)) * X a s := by
      change ((M.rankOne a).app R).hom (matrixWord s) = _
      unfold matrixWord
      rw [map_mul, map_mul]
      exact congrArg₂ (· * ·) (congrArg₂ (· * ·) (M.rankOneUpper a R s)
        (M.rankOneLower a R (-(↑s⁻¹ : R)))) (M.rankOneUpper a R s)
    have htorus (s : Rˣ) : w s = p (cocharacter D (D.datum.coroot a) R s) * w 1 := by
      change ((M.rankOne a).app R).hom (matrixWord s) = _
      rw [matrixWord_factor, map_mul]
      exact congrArg (· * w 1) (M.rankOneDiagonal a R s)
    have hconj (v : TorusValues D R) : p v * w 1 * (p v)⁻¹ = w (α v) := by
      have hx (b : D.I) (z : R) : p v * X b z * (p v)⁻¹ =
          X b ((v (Multiplicative.ofAdd (D.datum.root b)) : R) * z) := M.conjugation R v b z
      have hn : v (Multiplicative.ofAdd (D.datum.root c)) = (α v)⁻¹ := by
        change v (Multiplicative.ofAdd (D.datum.root (D.datum.reflectionPerm a a))) = _
        rw [D.datum.root_reflectionPerm, D.datum.reflection_apply_self, ofAdd_neg, map_inv]
      calc
        p v * w 1 * (p v)⁻¹ = (p v * X a 1 * (p v)⁻¹) *
          (p v * X c (-1) * (p v)⁻¹) * (p v * X a 1 * (p v)⁻¹) := by
            rw [hword 1]
            simp only [inv_one, Units.val_one]
            group
        _ = w (α v) := by
          rw [hx a 1, hx c (-1), hn, hword]
          simp only [α, mul_one, mul_neg]
    have href : t * cocharacter D (D.datum.coroot a) R (α t)⁻¹ =
        t.comp (D.datum.reflection a).toLinearMap.toAddMonoidHom.toMultiplicative := by
      apply MonoidHom.ext
      intro v
      change t v * (α t)⁻¹ ^ D.datum.toLinearMap v.toAdd (D.datum.coroot a) =
        t (Multiplicative.ofAdd ((D.datum.reflection a) v.toAdd))
      rw [D.datum.reflection_apply, ofAdd_sub, ofAdd_zsmul, map_div, map_zpow, div_eq_mul_inv, inv_zpow] <;> rfl
    change w 1 * p t * (w 1)⁻¹ = p (t.comp _)
    have h : (p t)⁻¹ * w 1 * p t = w (α t)⁻¹ := by
      have h' := hconj t⁻¹
      rw [p.map_inv, inv_inv] at h'
      exact h'
    calc
      w 1 * p t * (w 1)⁻¹ = p t * ((p t)⁻¹ * w 1 * p t) * (w 1)⁻¹ := by group
      _ = p t * p (cocharacter D (D.datum.coroot a) R (α t)⁻¹) := by
        rw [h, htorus, mul_assoc, mul_inv_cancel_right]
      _ = _ := by rw [← map_mul, href]

end IntegralReflections

section AbsoluteWeyl

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open Specs.NormalizerComparison (SimpleRepresentative)
open private identification_of_attached_datum simple_representatives_exist simpleRootOfIndex
  representative_label simple_reflections_generate from LinearAlgebraicGroups.Classification.NormalizerComparison
open private quotientLabel quotientLabel_spec from LinearAlgebraicGroups.RootData.AbstractPairing
open private rationalSectionsEquiv from LinearAlgebraicGroups.RootData.DatumAndWeyl
open private schemeKernel_sections from LinearAlgebraicGroups.Affine.SchemeImageQuotient

set_option backward.isDefEq.respectTransparency false in
theorem pinnedAbsoluteWeylLabels : PinnedAbsoluteWeylLabels.{u} := by
  intro k _ A P D
  letI := D.comm
  obtain ⟨C⟩ := identification_of_attached_datum P.pair D
  let q := C.labelEquiv.symm.toMonoidHom.comp (quotientLabel C.image)
  have hq (n : 𝟙_ (SchemeOver k) ⟶ C.normalizer.group.X) :
      C.labelEquiv (q n) = quotientLabel C.image n := C.labelEquiv.apply_symm_apply _
  have hsec (n : 𝟙_ (SchemeOver k) ⟶ C.normalizer.group.X) :
      n ≫ C.quotient.hom.hom = C.image.constantGroup.sectionPoint (C.labelEquiv (q n)) := by
    have h := quotientLabel_spec C.image n
    rw [show toUnit (𝟙_ (SchemeOver k)) = 𝟙 _ from Subsingleton.elim _ _, Category.id_comp] at h
    exact h.trans (congrArg C.image.constantGroup.sectionPoint (hq n).symm)
  have hs (i : Specs.Pinning.SimpleRoot P.pair) (r : SimpleRepresentative P D i) n
      (hn : n ≫ C.normalizer.inclusion.hom.hom = r.reflection.representative) :
      q n = RootPairing.weylGroup.ofIdx D.datum.rootDatum i.val := by
    apply C.labelEquiv.injective
    exact representative_label D C i r n hn (C.labelEquiv (q n)) (hsec n)
  refine ⟨C, q, ?_, hsec, ?_, hs⟩
  · letI := D.datum.finiteRoots
    letI := D.datum.freeCharacters
    letI := D.datum.finiteCharacters
    letI := D.datum.reduced
    obtain ⟨r⟩ := simple_representatives_exist P D
    apply MonoidHom.range_eq_top.mp
    apply top_unique
    rw [← simple_reflections_generate D.datum.rootDatum D.base]
    apply (Subgroup.closure_le q.range).mpr
    rintro _ ⟨i, rfl⟩
    let a := simpleRootOfIndex D i
    obtain ⟨n, hn⟩ := (C.representsNormalizer _ _).mp (r a).reflection.normalizes
    exact ⟨n, hs a (r a) n hn⟩
  · intro n
    obtain ⟨e, he⟩ := rationalSectionsEquiv C.image.constantGroup
    have h : q n = 1 ↔ n ≫ C.quotient.hom.hom = 1 := by
      rw [hsec, ← he, ← e.map_one, e.injective.eq_iff, ← C.labelEquiv.map_one,
        C.labelEquiv.injective.eq_iff]
    exact h.trans (schemeKernel_sections C.isQuotient.1 n).symm

open Specs.RationalRealization (Realization)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterPairing (characterValue pairing)
open Specs.IntegralSemisimpleModel (IntegralPoints Integers TorusValues cocharacter forgetFibrePoint integerAlgebra torusPoint)
open Specs.IntegralRootRelations (diagonal)
open Specs.RootGroups (CorootReflection HasScalarAction rankOneWord rootPoint)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)
open private fibrePointsEquiv from LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
open private matrixWord matrixWord_factor from LinearAlgebraicGroups.Classification.IntegralFibreDatum
open private rankOneRepresentative rankOneRepresentative_point rootPoint_comp
  from LinearAlgebraicGroups.RootData.RootGroups
open private reflection_of_linked_word from LinearAlgebraicGroups.Classification.NormalizerComparison

attribute [local instance] integerAlgebra

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 600000 in
theorem markedFibreSimpleWeylLifts : MarkedFibreSimpleWeylLifts.{u} := by
  intro k _ D M A P g z hpin hroot e he ht
  letI := P.attached.comm
  obtain ⟨C, q, hq, hpr, hker, hlabel⟩ := pinnedAbsoluteWeylLabels P.pinned P.attached
  refine ⟨C, q, hq, hpr, hker, fun a => ?_⟩
  let Q := P.attached.datum.rootDatum
  let E := P.datumIso.val
  let T := P.pinned.pair.T
  let i := P.simpleRoot a
  let o := D.datum.reflectionPerm a.val a.val
  let y (b : D.I) := (z b).val.hom ≫ (P.pinned.roots (E.indexEquiv b)).val.inclusion
  let c := Additive.toMul (Q.coroot i.val)
  have hα (b : D.I) : Additive.toMul (E.weightEquiv (D.datum.root b)) = (E.indexEquiv b).val := by
    apply Additive.ofMul.injective
    exact (RootPairing.Hom.root_weightMap_apply D.datum Q b E.toHom).trans
      (P.attached.datum.root_eq _)
  have hneg : (E.indexEquiv o).val = i.val.val⁻¹ := by
    change (E.indexEquiv o).val = ((E.indexEquiv a.val).val)⁻¹
    rw [← hα o, ← hα a.val]
    change Additive.toMul (E.weightEquiv (D.datum.root (D.datum.reflectionPerm a.val a.val))) = _
    rw [D.datum.root_reflectionPerm, D.datum.reflection_apply_self, map_neg]
    rfl
  have hp (x : D.X) : pairing T.group (Additive.toMul (E.weightEquiv x)) c =
      D.datum.toLinearMap x (D.datum.coroot a.val) := by
    rw [← P.attached.datum.pairing_eq]
    exact E.coroot'_weightEquiv a.val x
  have htwo : pairing T.group i.val.val c = 2 := by
    calc
      _ = pairing T.group (Additive.toMul (E.weightEquiv (D.datum.root a.val))) c :=
        congrArg (fun χ : Specs.CharacterDescent.Character T.group => pairing T.group χ c) (hα a.val).symm
      _ = D.datum.toLinearMap (D.datum.root a.val) (D.datum.coroot a.val) := hp _
      _ = 2 := (D.datum.root_coroot_eq_pairing a.val a.val).trans (D.datum.pairing_same a.val)
  have hc (R : TestAlgebra k) (b : Rˣ) :
      e R (cocharacter D (D.datum.coroot a.val) (CommAlgCat.of Integers.{u} R) b) =
        cocharacterPoint c R b := by
    let v := (e R).symm (cocharacterPoint c R b)
    have hv : e R v = cocharacterPoint c R b := (e R).apply_symm_apply _
    rw [← hv]
    apply congrArg (e R)
    apply MonoidHom.ext
    intro m
    apply Units.val_injective
    have h := he R v m.toAdd
    rw [hv, (RootData.CharacterPairing.characterPairingComposition _ _ _).2, hp] at h
    exact h
  let f (R : TestAlgebra k) : GroupPoints P.pinned.pair.G.val R ≃*
      IntegralPoints M.group (CommAlgCat.of Integers.{u} R) :=
    (((groupPointsFunctor k).mapIso g.symm).app R).groupIsoToMulEquiv.trans (fibrePointsEquiv M.group R)
  have hf (R : TestAlgebra k) (p : GroupPoints P.pinned.pair.G.val R) :
      f R p = forgetFibrePoint M.group R (p ≫ g.inv.hom.hom) := rfl
  have hcoord (b : D.I) (R : TestAlgebra k) (v : R) : f R (rootPoint (y b) R v) =
      M.line.point (CommAlgCat.of Integers.{u} R) v ≫ (M.root b).hom.hom := by
    rw [hf, ← rootPoint_comp]
    exact hroot b R v
  have hw (R : TestAlgebra k) (b : Rˣ) : f R (rankOneWord (y a.val) (y o) R b) =
      markedWeylWord M.toIntegralMarking a.val (CommAlgCat.of Integers.{u} R) b := by
    change _ = ((M.rankOne a.val).app (CommAlgCat.of Integers.{u} R)).hom (matrixWord b)
    simp only [rankOneWord, matrixWord, map_mul, hcoord, M.rankOneUpper, M.rankOneLower]
    rfl
  have hword (R : TestAlgebra k) (b : Rˣ) : cocharacterPoint c R b ≫ T.inclusion.hom.hom =
      rankOneWord (y a.val) (y o) R b * (rankOneWord (y a.val) (y o) R 1)⁻¹ := by
    apply (f R).injective
    rw [map_mul, map_inv, hw, hw, hf, ← hc, Category.assoc, ht]
    have h := congrArg (fun x => ((M.rankOne a.val).app (CommAlgCat.of Integers.{u} R)).hom x)
      (matrixWord_factor b)
    rw [map_mul] at h
    change _ = ((M.rankOne a.val).app (CommAlgCat.of Integers.{u} R)).hom (matrixWord b) *
      (((M.rankOne a.val).app (CommAlgCat.of Integers.{u} R)).hom (matrixWord 1))⁻¹
    rw [h, mul_inv_cancel_right, M.rankOneDiagonal]
  have hx : HasScalarAction T i.val.val (y a.val) := (z a.val).property
  have hy : HasScalarAction T i.val.val⁻¹ (y o) := by
    rw [← hneg]
    exact (z o).property
  let n₀ := rankOneRepresentative (y a.val) (y o)
  obtain ⟨r₀, hrc, hrn⟩ := reflection_of_linked_word T P.pinned.pair.split
    i.val.val (y a.val) (y o) hx hy c n₀ (rankOneRepresentative_point _ _) hword htwo
  have hpin' : (P.pinned.pin i).val.hom ≫ (P.pinned.roots i.val).val.inclusion = y a.val := by
    change (P.pinned.pin i).val.hom ≫ (P.pinned.roots i.val).val.inclusion =
      (z a.val).val.hom ≫ (P.pinned.roots i.val).val.inclusion
    rw [hpin a]
  obtain ⟨r₁, hc₁, hn₁⟩ : ∃ r : CorootReflection T i.val.val
      ((P.pinned.pin i).val.hom ≫ (P.pinned.roots i.val).val.inclusion) (y o),
      r.coroot = c ∧ r.representative = n₀ := by
    rw [hpin']
    exact ⟨r₀, hrc, hrn⟩
  let r : SimpleRepresentative P.pinned P.attached i :=
    ⟨E.indexEquiv o, hneg, z o, r₁, hc₁⟩
  obtain ⟨n, hn⟩ := (C.representsNormalizer _ _).mp r.reflection.normalizes
  refine ⟨r, n, hn, hlabel i r n hn, fun R => ?_⟩
  rw [← Category.assoc n _ _, hn, show r.reflection.representative = n₀ from hn₁]
  have hn₀ : toUnit ((testSpec k).obj (Opposite.op R)) ≫ n₀ =
      rankOneWord (y a.val) (y o) R 1 := rankOneRepresentative_point _ _ R
  rw [← Category.assoc, hn₀, ← hf]
  exact hw R 1

open AlgebraicGeometry
open Specs.AbstractPairing (Root)
open Specs.Pinning (AttachedDatum PinnedGroup PinnedIso SimpleRoot pinGraph transportCharacter)
open Specs.RootGroups (AdditiveLine)
open private linked_coroot from LinearAlgebraicGroups.Classification.RankTwoLifting
open private linked_representative_eq map_linked_reflection scalar_action_along_iso
  pullback_inverse_character from LinearAlgebraicGroups.Classification.NormalizerComparison
open private groundIso from LinearAlgebraicGroups.Solvable.TorusSections

private abbrev positiveMap {k : Type u} [Field k] {A : AdditiveLine k}
    {P : PinnedGroup A} (i : SimpleRoot P.pair) :=
  (P.pin i).val.hom ≫ (P.roots i.val).val.inclusion

private abbrev negativeMap {k : Type u} [Field k] {A : AdditiveLine k}
    {P : PinnedGroup A} {D : AttachedDatum P.pair} {i : SimpleRoot P.pair}
    (r : SimpleRepresentative P D i) := r.negative.val.hom ≫ (P.roots r.opposite).val.inclusion

private theorem negativeScalarAction {k : Type u} [Field k] {A : AdditiveLine k}
    {P : PinnedGroup A} {D : AttachedDatum P.pair} {i : SimpleRoot P.pair}
    (r : SimpleRepresentative P D i) : HasScalarAction P.pair.T i.val.val⁻¹ (negativeMap r) := by
  rw [← r.opposite_eq]
  exact r.negative.property

set_option backward.isDefEq.respectTransparency false in
private theorem pinnedSimpleWordEquivariant {k : Type u} [Field k] {A : AdditiveLine k}
    {P : PinnedGroup A} (D : AttachedDatum P.pair) (W : letI := D.comm; Specs.DatumAndWeyl.Identification D.datum)
    (f : PinnedIso P P) (i j : SimpleRoot P.pair)
    (hij : transportCharacter f.torus i.val.val = j.val.val)
    (r : SimpleRepresentative P D i) (s : SimpleRepresentative P D j) :
    r.reflection.representative ≫ f.group.hom.hom.hom = s.reflection.representative := by
  letI := D.comm
  have hz : (transportCharacter f.torus i.val.val, positiveMap i ≫ f.group.hom) ∈ pinGraph P := by
    rw [← f.pin_comm]
    exact ⟨(i.val.val, positiveMap i), ⟨i, rfl⟩, rfl⟩
  obtain ⟨b, hb⟩ := hz
  have hb' : b = j := Subtype.ext (Subtype.ext ((congrArg Prod.fst hb).trans hij))
  subst b
  have hpin : positiveMap i ≫ f.group.hom = positiveMap j := (congrArg Prod.snd hb).symm
  have hχ : f.torus.hom ≫ j.val.val = i.val.val := by
    rw [← hij, transportCharacter, Iso.hom_inv_id_assoc]
  have hχ' : f.torus.hom ≫ j.val.val⁻¹ = i.val.val⁻¹ := by
    rw [pullback_inverse_character, hχ]
  have hx : HasScalarAction P.pair.T (f.torus.hom ≫ j.val.val) (positiveMap i) := by
    rw [hχ]
    exact (P.pin i).property
  have hy : HasScalarAction P.pair.T (f.torus.hom ≫ j.val.val⁻¹) (negativeMap r) := by
    rw [hχ']
    exact negativeScalarAction r
  have hx' := scalar_action_along_iso f.group.hom f.torus f.torus_comm _ _ hx
  have hy' := scalar_action_along_iso f.group.hom f.torus f.torus_comm _ _ hy
  obtain ⟨v, _, hv⟩ := map_linked_reflection f.group.hom f.torus.hom f.torus_comm
    P.pair.split hχ r.reflection hx' hy'
  exact hv.symm.trans (linked_representative_eq D W v s.reflection hpin
    ((linked_coroot D.datum j.val v).trans s.coroot_eq.symm) hx' hy' (negativeScalarAction s))

set_option backward.isDefEq.respectTransparency false in
private theorem orthogonalPinnedPoints {k : Type u} [Field k] {A : AdditiveLine k}
    {P : PinnedGroup A} (D : AttachedDatum P.pair) [IsCommMonObj P.pair.T.group.X]
    (hsym : ∀ i j, D.datum.rootDatum.pairing i j = D.datum.rootDatum.pairing j i)
    (i j : Root P.pair.T) (hij : D.datum.rootDatum.pairing i j = 0)
    (R : TestAlgebra k) (a : GroupPoints (P.roots i).val.group R) (b : GroupPoints (P.roots j).val.group R) :
    Commute (a ≫ (P.roots i).val.inclusion.hom.hom : GroupPoints P.pair.G.val R)
      (b ≫ (P.roots j).val.inclusion.hom.hom) := by
  letI := D.comm
  let Q := D.datum.rootDatum
  change Q.pairing i j = 0 at hij
  have hji : Q.pairing j i = 0 := (hsym j i).trans hij
  apply Classification.RankOneRelations.independentRootCommutation P.pair.G P.pair.reductive
    P.pair.T P.pair.split P.pair.maximal i.val i.property j.val j.property _ _
    (P.roots i).val (P.roots j).val (P.roots i).property (P.roots j).property R a b
  · rintro ⟨m, n, hm, hn, he⟩
    have he' : m • Q.root i = n • Q.root j := by
      rw [D.datum.root_eq, D.datum.root_eq]
      exact congrArg Additive.ofMul he
    have h := congrArg (Q.coroot' i) he'
    simp only [map_smul, Q.root_coroot'_eq_pairing, Q.pairing_same, hji, smul_eq_mul] at h
    omega
  · intro m n hm hn h
    let a₀ : Root P.pair.T := ⟨i.val ^ m * j.val ^ n, h⟩
    have he : Q.root a₀ = (m : ℤ) • Q.root i + (n : ℤ) • Q.root j := by
      rw [D.datum.root_eq, D.datum.root_eq, D.datum.root_eq]
      rfl
    have hmi : Q.pairing a₀ i = (m : ℤ) * 2 := by
      rw [RootPairing.pairing_eq_add_of_root_eq_smul_add_smul he]
      simp [hji]
    have hnj : Q.pairing a₀ j = (n : ℤ) * 2 := by
      rw [RootPairing.pairing_eq_add_of_root_eq_smul_add_smul he]
      simp [hij]
    have hEq : (2 : ℤ) = m * (m * 2) + n * (n * 2) := by
      calc
        2 = Q.pairing a₀ a₀ := (Q.pairing_same a₀).symm
        _ = (m : ℤ) • Q.pairing i a₀ + (n : ℤ) • Q.pairing j a₀ :=
          RootPairing.pairing_eq_add_of_root_eq_smul_add_smul he
        _ = _ := by rw [hsym i a₀, hsym j a₀, hmi, hnj, smul_eq_mul, smul_eq_mul]
    have hm₂ : 1 ≤ (m : ℤ) ^ 2 := by
      have h₀ : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
      have := sq_pos_iff.mpr h₀
      omega
    have hn₂ : 1 ≤ (n : ℤ) ^ 2 := by
      have h₀ : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
      have := sq_pos_iff.mpr h₀
      omega
    nlinarith only [hEq, hm₂, hn₂]

set_option backward.isDefEq.respectTransparency false in
private theorem orthogonalSimpleWords {k : Type u} [Field k] {A : AdditiveLine k}
    {P : PinnedGroup A} (D : AttachedDatum P.pair) [IsCommMonObj P.pair.T.group.X]
    (hsym : ∀ i j, D.datum.rootDatum.pairing i j = D.datum.rootDatum.pairing j i)
    (i j : SimpleRoot P.pair) (hij : D.datum.rootDatum.pairing i.val j.val = 0)
    (r : SimpleRepresentative P D i) (s : SimpleRepresentative P D j) :
    Commute r.reflection.representative s.reflection.representative := by
  letI := D.comm
  let Q := D.datum.rootDatum
  have hop {i₀ : SimpleRoot P.pair} (a : SimpleRepresentative P D i₀) :
      a.opposite = Q.reflectionPerm i₀.val i₀.val := by
    apply Q.root.injective
    rw [Q.root_reflectionPerm, Q.reflection_apply_self, D.datum.root_eq, D.datum.root_eq, a.opposite_eq]
    rfl
  let R := CommAlgCat.of k k
  let Y := (testSpec k).obj (Opposite.op R)
  have h {a b : Root P.pair.T} (h₀ : Q.pairing a b = 0)
      (x : A.group ⟶ (P.roots a).val.group) (y : A.group ⟶ (P.roots b).val.group) (v w : R) :
      Commute (rootPoint (x ≫ (P.roots a).val.inclusion) R v)
        (rootPoint (y ≫ (P.roots b).val.inclusion) R w) := by
    rw [rootPoint_comp, rootPoint_comp]
    exact orthogonalPinnedPoints D hsym a b h₀ R (rootPoint x R v) (rootPoint y R w)
  have hh₁ : Q.pairing i.val s.opposite = 0 := by rw [hop s, Q.pairing_reflectionPerm_self_right, hij, neg_zero]
  have hh₂ : Q.pairing r.opposite j.val = 0 := by rw [hop r, Q.pairing_reflectionPerm_self_left, hij, neg_zero]
  have hh₃ : Q.pairing r.opposite s.opposite = 0 := by
    rw [hop r, Q.pairing_reflectionPerm_self_left, hh₁, neg_zero]
  have h₁₁ := h hij (P.pin i).val.hom (P.pin j).val.hom 1 1
  have h₁₂ := h hh₁ (P.pin i).val.hom s.negative.val.hom 1 (-1)
  have h₂₁ := h hh₂ r.negative.val.hom (P.pin j).val.hom (-1) 1
  have h₂₂ := h hh₃ r.negative.val.hom s.negative.val.hom (-1) (-1)
  letI := (groundIso (k := k)).isIso_hom
  apply (cancel_epi (groundIso (k := k)).hom).mp
  have hy : (groundIso (k := k)).hom = toUnit Y := Subsingleton.elim _ _
  have hr : toUnit Y ≫ r.reflection.representative = rankOneWord (positiveMap i) (negativeMap r) R 1 :=
    r.reflection.representative_word
  have hs : toUnit Y ≫ s.reflection.representative = rankOneWord (positiveMap j) (negativeMap s) R 1 :=
    s.reflection.representative_word
  rw [hy, MonObj.comp_mul, MonObj.comp_mul, hr, hs]
  unfold rankOneWord
  simp only [Units.val_one, inv_one]
  exact ((((h₁₁.mul_right h₁₂).mul_right h₁₁).mul_left
    ((h₂₁.mul_right h₂₂).mul_right h₂₁)).mul_left ((h₁₁.mul_right h₁₂).mul_right h₁₁)).eq

set_option backward.isDefEq.respectTransparency false in
theorem pinnedOrbitWeylLifts : PinnedOrbitWeylLifts.{u} := by
  classical
  intro k _ A P D
  letI := D.comm
  intro C q r hq f τ hτ hinv hsym hortho
  have hf (i : SimpleRoot P.pair) := pinnedSimpleWordEquivariant D C f i (τ i) (hτ i) (r i) (r (τ i))
  let v (i : SimpleRoot P.pair) := (r i).reflection.representative
  have hex (i : SimpleRoot P.pair) := (C.representsNormalizer _ (v i)).mp (r i).reflection.normalizes
  choose n hn using hex
  let p := IsMonHom.monoidHom C.normalizer.inclusion.hom.hom (𝟙_ (SchemeOver k))
  let a := IsMonHom.monoidHom f.group.hom.hom.hom (𝟙_ (SchemeOver k))
  have hp (i) : p (n i) = v i := hn i
  have hact (i) : a (v i) = v (τ i) := hf i
  refine ⟨hf, fun i => ?_⟩
  by_cases hi : τ i = i
  · refine ⟨n i, ?_, ?_⟩
    · rw [← Category.assoc]
      change a (p (n i)) = p (n i)
      rw [hp, hact, hi]
    · simp only [ite_eq_left hi]
      exact ⟨hn i, hq i _ (hn i)⟩
  · refine ⟨n i * n (τ i), ?_, ?_⟩
    · rw [← Category.assoc]
      change a (p (n i * n (τ i))) = p (n i * n (τ i))
      rw [map_mul, map_mul, hp, hp, hact, hact, hinv i]
      exact (orthogonalSimpleWords D hsym i (τ i) (hortho i hi) (r i) (r (τ i))).eq.symm
    · simp only [ite_eq_right hi]
      constructor
      · change p (n i * n (τ i)) = v i * v (τ i)
        rw [map_mul, hp, hp]
      · rw [map_mul, hq i _ (hn i), hq (τ i) _ (hn (τ i))]

open Specs.IntegralSemisimpleModel (integralPointFunctor)

set_option backward.isDefEq.respectTransparency false in
theorem markedFibreNormalizer : MarkedFibreNormalizer.{u} := by
  intro k _ D M
  obtain ⟨A, P, g, s, z, hT, hp, hχ, hroot⟩ := M.fieldFibre k
  obtain ⟨e, he, ht⟩ := markedFibreTorusCoordinates D M P g s hT hχ
  letI := P.attached.comm
  obtain ⟨C, q, hq, hpr, hker, hsimple⟩ := markedFibreSimpleWeylLifts D M P g z hp hroot e he ht
  obtain ⟨v, hv, hvχ⟩ := weylGroupTransport D P.attached.toBased P.datumIso
  let R := CommAlgCat.of k k
  let N := (𝟙_ (SchemeOver k) ⟶ C.normalizer.group.X)
  let Y := (testSpec k).obj (Opposite.op R)
  let a : N →* (Y ⟶ C.normalizer.group.X) := MonoidHom.mk' (fun n => toUnit Y ≫ n)
    (fun x y => MonObj.comp_mul (toUnit Y) x y)
  let j := IsMonHom.monoidHom C.normalizer.inclusion.hom.hom Y
  let i := IsMonHom.monoidHom g.inv.hom.hom Y
  let F := ((fibrePointsEquiv M.group R).toMonoidHom).comp (i.comp (j.comp a))
  have hF (n : N) : F n = forgetFibrePoint M.group R
      (toUnit Y ≫ n ≫ C.normalizer.inclusion.hom.hom ≫ g.inv.hom.hom) := by
    change forgetFibrePoint M.group R (((toUnit Y ≫ n) ≫ C.normalizer.inclusion.hom.hom) ≫
      g.inv.hom.hom) = _
    simp only [Category.assoc]
  let label := v.symm.toMonoidHom.comp q
  refine ⟨{
    line := A
    realization := P
    fibreIso := g
    torusComm := P.attached.comm
    identification := C
    labelIso := v
    labelIso_simple := hv
    labelIso_character := hvχ
    label := label
    label_surjective := v.symm.surjective.comp hq
    projection := ?_
    kernel := ?_
    point := F
    point_eq := hF
    torusValues := e
    character := he
    torusPoint_eq := ht
    simple := ?_ }⟩
  · intro n
    change n ≫ C.quotient.hom.hom = C.image.constantGroup.sectionPoint (C.labelEquiv (v (v.symm (q n))))
    rw [v.apply_symm_apply]
    exact hpr n
  · intro n
    change v.symm (q n) = 1 ↔ _
    rw [← v.symm.map_one, v.symm.injective.eq_iff]
    exact hker n
  · intro a
    obtain ⟨r, n, hn, h, hword⟩ := hsimple a
    refine ⟨r, n, hn, ?_, (hF n).trans (hword R), hword⟩
    apply v.injective
    change v (v.symm (q n)) = v (RootPairing.weylGroup.ofIdx D.datum a.val)
    rw [v.apply_symm_apply, hv]
    exact h

set_option backward.isDefEq.respectTransparency false in
theorem normalizerFieldLabels : NormalizerFieldLabels.{u} := by
  intro k K _ _ _ D M F
  letI := F.torusComm
  let C := F.identification
  let R := CommAlgCat.of k K
  let Y := (testSpec k).obj (Opposite.op R)
  let W := C.image.labels
  let e := F.labelIso.trans C.labelEquiv
  let y : Y.left := IsLocalRing.closedPoint K
  let f := C.image.constantGroup.families Y
  let g := IsMonHom.monoidHom C.quotient.hom.hom Y
  let r := (LocallyConstant.evalMonoidHom y).comp (f.toMonoidHom.comp g)
  let q := e.symm.toMonoidHom.comp r
  let s := C.image.constantGroup.sectionPoint
  have hq (n : Y ⟶ C.normalizer.group.X) : e (q n) = r n := e.apply_symm_apply _
  have hp (n : Y ⟶ C.normalizer.group.X) : n ≫ C.quotient.hom.hom = toUnit Y ≫ s (e (q n)) := by
    apply f.injective
    change _ = C.image.constantGroup.families Y (toUnit Y ≫ C.image.constantGroup.sectionPoint (e (q n)))
    rw [C.image.constantGroup.constant, hq]
    apply LocallyConstant.ext
    intro x
    change f (n ≫ C.quotient.hom.hom) x = f (n ≫ C.quotient.hom.hom) y
    have hxy : x = y := Subsingleton.elim (α := PrimeSpectrum K) x y
    rw [hxy]
  have hs (v : W) : f (toUnit Y ≫ s v) y = v :=
    congrArg (fun h : LocallyConstant Y.left W => h y) (C.image.constantGroup.constant Y v)
  have hsi : Function.Injective (fun v : W => toUnit Y ≫ s v) := by
    intro v w h
    exact (hs v).symm.trans (congrArg (fun x => f x y) h) |>.trans (hs w)
  have hc (n : 𝟙_ (SchemeOver k) ⟶ C.normalizer.group.X) : q (toUnit Y ≫ n) = F.label n := by
    apply e.injective
    apply hsi
    change toUnit Y ≫ s (e (q (toUnit Y ≫ n))) = toUnit Y ≫ s (e (F.label n))
    rw [← hp, Category.assoc]
    exact congrArg (toUnit Y ≫ ·) (F.projection n)
  refine ⟨q, fun w ↦ ?_, hp, ?_, hc, ?_⟩
  · obtain ⟨n, hn⟩ := F.label_surjective w
    exact ⟨toUnit Y ≫ n, (hc n).trans hn⟩
  · intro n
    have hs₁ : toUnit Y ≫ s (e 1) = 1 := by rw [e.map_one, s.map_one, MonObj.comp_one]
    have hl : q n = 1 ↔ n ≫ C.quotient.hom.hom = 1 := by
      rw [hp, ← hs₁, hsi.eq_iff, e.injective.eq_iff]
    exact hl.trans (schemeKernel_sections C.isQuotient.1 n).symm
  · intro a n
    apply e.injective
    apply hsi
    change toUnit Y ≫ s (e (q ((testSpec k).map a.op ≫ n))) = toUnit Y ≫ s (e (q n))
    rw [← hp, ← hp, Category.assoc, hp, ← Category.assoc, comp_toUnit]

private theorem simultaneousIntegralLifts {N P A X Y W S : Type u}
    [Group N] [Group P] [Group A] [Group X] [Group Y] [Group W]
    (q : N →* W) (r : P →* W) (j : N →* X) (l : P →* Y) (f : A →* X) (g : A →* Y)
    (word : S → W)
    (hw : ∀ i, ∃ (n : N) (m : P) (p : A), q n = word i ∧ r m = word i ∧ f p = j n ∧ g p = l m)
    (w : W) (h : w ∈ Subgroup.closure (Set.range word)) :
    ∃ (n : N) (m : P) (p : A), q n = w ∧ r m = w ∧ f p = j n ∧ g p = l m := by
  let n := MonoidHom.fst N (P × A)
  let m := (MonoidHom.fst P A).comp (MonoidHom.snd N (P × A))
  let p := (MonoidHom.snd P A).comp (MonoidHom.snd N (P × A))
  let H := (r.comp m).eqLocus (q.comp n) ⊓
    ((f.comp p).eqLocus (j.comp n) ⊓ (g.comp p).eqLocus (l.comp m))
  let u := (q.comp n).comp H.subtype
  have hu : Subgroup.closure (Set.range word) ≤ u.range := by
    apply (Subgroup.closure_le u.range).mpr
    rintro _ ⟨i, rfl⟩
    obtain ⟨ni, mi, pi, hi, hmi, hfi, hgi⟩ := hw i
    exact ⟨⟨(ni, mi, pi), ⟨hmi.trans hi.symm, hfi, hgi⟩⟩, hi⟩
  obtain ⟨x, hx⟩ := hu h
  have hh : r (m x.val) = q (n x.val) ∧ f (p x.val) = j (n x.val) ∧
      g (p x.val) = l (m x.val) := x.property
  exact ⟨n x.val, m x.val, p x.val, hx, hh.1.trans hx, hh.2.1, hh.2.2⟩

set_option backward.isDefEq.respectTransparency false in
theorem splitIntegralWeylLifts : SplitIntegralWeylLifts.{u} := by
  intro k l _ _ D M F E R f e
  letI := F.torusComm
  letI := E.torusComm
  intro w
  letI := D.finiteRoots
  letI := D.reduced
  let a := ((integralPointFunctor M.group).map f).hom
  let b := ((integralPointFunctor M.group).map e).hom
  let gen (i : D.base.support) := RootPairing.weylGroup.ofIdx D.datum i.val
  have hw : w ∈ Subgroup.closure (Set.range gen) := by
    rw [simple_reflections_generate D.datum D.base]
    exact Subgroup.mem_top _
  apply simultaneousIntegralLifts F.label E.label F.point E.point a b gen _ w hw
  intro i
  obtain ⟨_, n, _, hn, hf, _⟩ := F.simple i
  obtain ⟨_, m, _, hm, he, _⟩ := E.simple i
  let p := markedWeylWord M.toIntegralMarking i.val R 1
  have hp : a p = F.point n := by
    rw [hf]
    simpa only [map_one] using (integralWeylWordConjugation M.toIntegralMarking i.val).1 f 1
  have hp' : b p = E.point m := by
    rw [he]
    simpa only [map_one] using (integralWeylWordConjugation M.toIntegralMarking i.val).1 e 1
  exact ⟨n, m, p, hn, hm, hp, hp'⟩

open Specs.CharacterDescent (Character)
open private labelConjugation from LinearAlgebraicGroups.RootData.DatumAndWeyl
open private conjugation_on_points from LinearAlgebraicGroups.Classification.PinnedUniqueness

set_option backward.isDefEq.respectTransparency false in
private theorem torusValues_weylConjugation {k : Type u} [Field k]
    {D : Specs.Pinning.BasedRootDatum.{u}} {M : Specs.IntegralSemisimpleModel.Model D}
    (F : FibreNormalizer M k) (R : TestAlgebra k) (w : D.datum.weylGroup)
    (v : TorusValues D (CommAlgCat.of Integers.{u} R)) :
    letI := F.torusComm
    let C := F.identification
    let d := C.image.conjugation (C.labelEquiv (F.labelIso w))
    F.torusValues R (v.comp w.val.weightEquiv.symm.toLinearMap.toAddMonoidHom.toMultiplicative) =
      F.torusValues R v ≫ d.hom.hom.hom := by
  letI := F.torusComm
  let P := F.realization
  let C := F.identification
  let T := P.pinned.pair.T
  let e : TorusValues D (CommAlgCat.of Integers.{u} R) ≃* GroupPoints T.group R := F.torusValues R
  let ℓ := C.labelEquiv (F.labelIso w)
  let d := C.image.conjugation ℓ
  let m := w.val.weightEquiv.symm.toLinearMap.toAddMonoidHom.toMultiplicative
  let χ (x : D.X) : Character T.group := Additive.toMul (P.datumIso.val.weightEquiv x)
  have hχ (x : D.X) : d.hom ≫ χ x = χ (w.val.weightEquiv.symm x) := by
    let z := χ (w.val.weightEquiv.symm x)
    have h := C.characterAction (F.labelIso w) z
    change (F.labelIso w).val.weightEquiv
      (P.datumIso.val.weightEquiv (w.val.weightEquiv.symm x)) = Additive.ofMul (ℓ.val z) at h
    rw [F.labelIso_character, LinearEquiv.apply_symm_apply] at h
    have he : ℓ.val z = χ x := Additive.ofMul.injective h.symm
    have hd : d.inv ≫ z = χ x := (C.image.characterAction ℓ z).symm.trans he
    rw [← hd, Iso.hom_inv_id_assoc]
  have hv : e (v.comp m) = e v ≫ d.hom.hom.hom := by
    let z := e.symm (e v ≫ d.hom.hom.hom)
    have hz : e z = e v ≫ d.hom.hom.hom := e.apply_symm_apply _
    rw [← hz]
    apply congrArg e
    apply MonoidHom.ext
    intro u
    apply Units.val_injective
    have h₁ : characterValue (χ u.toAdd) R (e z) = (z u : R) := F.character R z u.toAdd
    have h₂ : characterValue (χ (w.val.weightEquiv.symm u.toAdd)) R (e v) = ((v.comp m) u : R) :=
      F.character R v (w.val.weightEquiv.symm u.toAdd)
    have h₃ : characterValue (χ u.toAdd) R (e z) = characterValue (d.hom ≫ χ u.toAdd) R (e v) := by
      rw [hz]
      unfold characterValue
      rw [Grp.comp_hom_hom, Category.assoc]
    rw [hχ, h₁, h₂] at h₃
    exact h₃.symm
  exact hv

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 500000 in
theorem fibreNormalizerTorusAction : FibreNormalizerTorusAction.{u} := by
  intro k _ D M F
  letI := F.torusComm
  let P := F.realization
  let C := F.identification
  let T := P.pinned.pair.T
  let R := CommAlgCat.of k k
  let S := CommAlgCat.of Integers.{u} k
  let Y := (testSpec k).obj (Opposite.op R)
  let b := (groundIso (k := k)).inv
  have hb : toUnit Y ≫ b = 𝟙 Y := by
    rw [show toUnit Y = (groundIso (k := k)).hom from Subsingleton.elim _ _]
    exact (groundIso (k := k)).hom_inv_id
  let e : TorusValues D S ≃* GroupPoints T.group R := F.torusValues R
  let N := (𝟙_ (SchemeOver k) ⟶ C.normalizer.group.X)
  let a : GroupPoints T.group R →* (𝟙_ (SchemeOver k) ⟶ T.group.X) :=
    MonoidHom.mk' (fun t => b ≫ t) (fun t s => MonObj.comp_mul b t s)
  let i := IsMonHom.monoidHom C.torusInclusion.hom.hom (𝟙_ (SchemeOver k))
  let t : TorusValues D S →* N := i.comp (a.comp e.toMonoidHom)
  have ht (v : TorusValues D S) : F.label (t v) = 1 := (F.kernel _).mpr ⟨a (e v), rfl⟩
  let c : TorusValues D S →* F.label.ker := t.codRestrict F.label.ker ht
  letI : IsClosedImmersion C.torusInclusion.hom.hom.left := C.torusClosed
  letI : Mono C.torusInclusion.hom.hom := Over.mono_of_mono_left _
  letI : IsIso b := (groundIso (k := k)).isIso_inv
  have hc : Function.Bijective c := by
    constructor
    · intro u v h
      apply e.injective
      apply (cancel_epi b).mp
      apply (cancel_mono C.torusInclusion.hom.hom).mp
      exact congrArg Subtype.val h
    · intro n
      obtain ⟨z, hz⟩ := (F.kernel n.val).mp n.property
      obtain ⟨v, hv⟩ := e.surjective (toUnit Y ≫ z)
      refine ⟨v, Subtype.ext ?_⟩
      change (b ≫ e v) ≫ C.torusInclusion.hom.hom = n.val
      rw [hv, ← Category.assoc b, show b ≫ toUnit Y = 𝟙 _ from Subsingleton.elim _ _,
        Category.id_comp, hz]
  let j := MulEquiv.ofBijective c hc
  have hn (v : TorusValues D S) : toUnit Y ≫ (j v).val ≫ C.normalizer.inclusion.hom.hom =
      e v ≫ T.inclusion.hom.hom := by
    change toUnit Y ≫ ((b ≫ e v) ≫ C.torusInclusion.hom.hom) ≫ C.normalizer.inclusion.hom.hom = _
    simp only [Category.assoc]
    rw [← Category.assoc (toUnit Y) b, hb, Category.id_comp, ← Grp.comp_hom_hom, C.inclusion_eq]
  refine ⟨j, ?_, fun n v => ?_⟩
  · intro v
    rw [F.point_eq]
    change forgetFibrePoint M.group R
      (toUnit Y ≫ (j v).val ≫ C.normalizer.inclusion.hom.hom ≫ F.fibreIso.inv.hom.hom) = _
    rw [← Category.assoc (j v).val, ← Category.assoc (toUnit Y), hn]
    exact F.torusPoint_eq R v
  · let w := F.label n
    let ℓ := C.labelEquiv (F.labelIso w)
    let d := C.image.conjugation ℓ
    let m := (w.val.weightEquiv.symm.toLinearMap.toAddMonoidHom.toMultiplicative)
    have hv : e (v.comp m) = e v ≫ d.hom.hom.hom := torusValues_weylConjugation F R w v
    let p : N →* GroupPoints P.pinned.pair.G.val R :=
      (IsMonHom.monoidHom C.normalizer.inclusion.hom.hom Y).comp
        (MonoidHom.mk' (fun n => toUnit Y ≫ n) (fun x y => MonObj.comp_mul (toUnit Y) x y))
    have hp (v : TorusValues D S) : p (j v).val = e v ≫ T.inclusion.hom.hom := by
      change (toUnit Y ≫ (j v).val) ≫ C.normalizer.inclusion.hom.hom = _
      rw [Category.assoc, hn]
    letI : IsClosedImmersion C.normalizer.inclusion.hom.hom.left := C.normalizer.isClosedImmersion
    letI : Mono C.normalizer.inclusion.hom.hom := Over.mono_of_mono_left _
    letI := (groundIso (k := k)).isIso_hom
    have hpi : Function.Injective p := by
      intro x y h
      apply (cancel_epi (groundIso (k := k)).hom).mp
      rw [show (groundIso (k := k)).hom = toUnit Y from Subsingleton.elim _ _]
      exact (cancel_mono C.normalizer.inclusion.hom.hom).mp h
    apply Subtype.ext
    apply hpi
    change p (n * (j v).val * n⁻¹) = p (j (v.comp m)).val
    rw [map_mul, map_mul, map_inv, hp, hp, hv]
    have hconj := labelConjugation C.image ℓ n (F.projection n)
    exact conjugation_on_points hconj R (e v)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 500000 in
theorem normalizerFieldTorusAction : NormalizerFieldTorusAction.{u} := by
  intro k K _ _ _ D M F
  letI := F.torusComm
  dsimp only
  intro q hq hk
  let P := F.realization
  let C := F.identification
  let T := P.pinned.pair.T
  let R := CommAlgCat.of k K
  let S := CommAlgCat.of Integers.{u} K
  let Y := (testSpec k).obj (Opposite.op R)
  let N := (Y ⟶ C.normalizer.group.X)
  let e : TorusValues D S ≃* GroupPoints T.group R := F.torusValues R
  let j₀ : TorusValues D S →* N := (IsMonHom.monoidHom C.torusInclusion.hom.hom Y).comp e.toMonoidHom
  have hker (v : TorusValues D S) : q (j₀ v) = 1 := (hk _).mpr ⟨e v, rfl⟩
  let j' := j₀.codRestrict q.ker hker
  letI : IsClosedImmersion C.torusInclusion.hom.hom.left := C.torusClosed
  letI : Mono C.torusInclusion.hom.hom := Over.mono_of_mono_left _
  have h' : Function.Bijective j' := by
    constructor
    · intro u v h
      exact e.injective ((cancel_mono C.torusInclusion.hom.hom).mp (congrArg Subtype.val h))
    · intro n
      obtain ⟨t, ht⟩ := (hk n.val).mp n.property
      obtain ⟨v, hv⟩ := e.surjective t
      exact ⟨v, Subtype.ext ((congrArg (· ≫ C.torusInclusion.hom.hom) hv).trans ht)⟩
  let j := MulEquiv.ofBijective j' h'
  let i := IsMonHom.monoidHom C.normalizer.inclusion.hom.hom Y
  have hi (v : TorusValues D S) : i (j v).val = e v ≫ T.inclusion.hom.hom := by
    change (e v ≫ C.torusInclusion.hom.hom) ≫ C.normalizer.inclusion.hom.hom = _
    rw [Category.assoc, ← Grp.comp_hom_hom, C.inclusion_eq]
  refine ⟨j, hi, ?_, fun n v => ?_⟩
  · intro v
    change forgetFibrePoint M.group R
      ((i (j v).val) ≫ F.fibreIso.inv.hom.hom) = _
    rw [hi]
    exact F.torusPoint_eq R v
  · let w := q n
    let ℓ := C.labelEquiv (F.labelIso w)
    let d := C.image.conjugation ℓ
    let m := w.val.weightEquiv.symm.toLinearMap.toAddMonoidHom.toMultiplicative
    letI : IsClosedImmersion C.normalizer.inclusion.hom.hom.left := C.normalizer.isClosedImmersion
    letI : Mono C.normalizer.inclusion.hom.hom := Over.mono_of_mono_left _
    apply Subtype.ext
    apply (show Function.Injective i from fun _ _ h => (cancel_mono C.normalizer.inclusion.hom.hom).mp h)
    change i (n * (j v).val * n⁻¹) = i (j (v.comp m)).val
    rw [map_mul, map_mul, map_inv, hi, hi, torusValues_weylConjugation F R w v]
    have hc := C.image.conjugates Y n ℓ (hq n)
    have h := congrArg (fun z => lift (e v) (𝟙 Y) ≫ z) hc
    have hs : lift (e v) (𝟙 Y) ≫ snd F.realization.pinned.pair.T.group.X Y = 𝟙 Y := lift_snd _ _
    have hz : (𝟙 Y) ≫ n = n := Category.id_comp n
    let x : GroupPoints P.pinned.pair.G.val R := n ≫ C.normalizer.inclusion.hom.hom
    let y : GroupPoints P.pinned.pair.G.val R := e v ≫ T.inclusion.hom.hom
    let z : GroupPoints P.pinned.pair.G.val R := (e v ≫ d.hom.hom.hom) ≫ T.inclusion.hom.hom
    change x * y * x⁻¹ = z
    simpa only [conjugateFamily, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc,
      lift_fst, hs, hz, Category.id_comp, Grp.comp_hom_hom] using h

open private characterValue_natural from LinearAlgebraicGroups.RootData.RootGroups

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 600000 in
theorem fixedNormalizerTorusCoordinates : FixedNormalizerTorusCoordinates.{u} := by
  intro k K _ _ _ D M F index _ b s τ σ hσ
  letI := F.torusComm
  dsimp only
  intro hχ q a hq hk ha
  let C := F.identification
  let T := F.realization.pinned.pair.T
  let R := CommAlgCat.of k K
  let S := CommAlgCat.of Integers.{u} K
  let Y := (testSpec k).obj (Opposite.op R)
  let N := (Y ⟶ C.normalizer.group.X)
  let f : R ⟶ R := CommAlgCat.ofHom σ.toAlgHom
  let c := fieldCoefficientAction σ C.normalizer.group
  let χ (i : index) : Character T.group := Additive.toMul (F.realization.datumIso.val.weightEquiv (characterBasis D b i))
  let B := MonoidHom.eqLocus a.toMonoidHom c
  obtain ⟨j, hj, hpt, hconj⟩ := normalizerFieldTorusAction (K := K) F q hq hk
  let e := F.torusValues R
  letI : IsClosedImmersion C.normalizer.inclusion.hom.hom.left := C.normalizer.isClosedImmersion
  letI : Mono C.normalizer.inclusion.hom.hom := Over.mono_of_mono_left _
  letI : IsClosedImmersion T.inclusion.hom.hom.left := T.isClosedImmersion
  letI : Mono T.inclusion.hom.hom := Over.mono_of_mono_left _
  have h₁ (v : TorusValues D S) : a (j v).val ≫ C.normalizer.inclusion.hom.hom =
      (e v ≫ s.torus.hom.hom.hom) ≫ T.inclusion.hom.hom := by
    rw [ha, ← Category.assoc, hj, Category.assoc, ← Grp.comp_hom_hom, s.torus_comm, Grp.comp_hom_hom]
    exact (Category.assoc (e v) s.torus.hom.hom.hom T.inclusion.hom.hom).symm
  have h₂ (v : TorusValues D S) : c (j v).val ≫ C.normalizer.inclusion.hom.hom =
      mapPoints f (e v) ≫ T.inclusion.hom.hom := by
    change ((testSpec k).map f.op ≫ (j v).val) ≫ C.normalizer.inclusion.hom.hom = _
    rw [Category.assoc, hj, ← Category.assoc]
  have hp (i : index) : s.torus.hom ≫ χ (τ i) = χ i := by
    have h := hχ i
    change Specs.Pinning.transportCharacter s.torus (χ i) = χ (τ i) at h
    rw [← h, Specs.Pinning.transportCharacter, Iso.hom_inv_id_assoc]
  obtain ⟨u, hu, _⟩ := torusBasisCoordinates D b S
  have hsep (x y : GroupPoints T.group R) (h : ∀ i, characterValue (χ i) R x = characterValue (χ i) R y) :
      x = y := by
    obtain ⟨v, rfl⟩ := e.surjective x
    obtain ⟨w, rfl⟩ := e.surjective y
    apply congrArg e
    apply u.injective
    funext i
    apply Units.val_injective
    rw [hu, hu]
    exact (F.character R v _).symm.trans ((h i).trans (F.character R w _))
  refine ⟨j, hpt, hconj, fun v => ?_⟩
  let z (i : index) : K := v (Multiplicative.ofAdd (characterBasis D b i))
  have hl (i : index) : characterValue (χ (τ i)) R (e v ≫ s.torus.hom.hom.hom) = z i := by
    have hh : characterValue (χ (τ i)) R (e v ≫ s.torus.hom.hom.hom) =
        characterValue (s.torus.hom ≫ χ (τ i)) R (e v) := by
      unfold characterValue
      rw [Grp.comp_hom_hom, Category.assoc]
    rw [hh, hp]
    exact F.character R v _
  have hr (i : index) : characterValue (χ (τ i)) R (mapPoints f (e v)) = σ (z (τ i)) := by
    rw [characterValue_natural]
    exact congrArg σ (F.character R v _)
  change a (j v).val = c (j v).val ↔ ∀ i, z (τ i) = σ (z i)
  constructor
  · intro h i
    have ht : e v ≫ s.torus.hom.hom.hom = mapPoints f (e v) := by
      apply (cancel_mono T.inclusion.hom.hom).mp
      rw [← h₁, ← h₂, h]
    have h' := (hl i).symm.trans ((congrArg (characterValue (χ (τ i)) R) ht).trans (hr i))
    have hy := congrArg σ h'
    rw [hσ] at hy
    exact hy.symm
  · intro h
    apply (cancel_mono C.normalizer.inclusion.hom.hom).mp
    rw [h₁, h₂]
    apply congrArg (· ≫ T.inclusion.hom.hom)
    apply hsep
    intro i
    obtain ⟨j, rfl⟩ := τ.surjective i
    rw [hl, hr]
    have hy := congrArg σ (h j)
    rw [hσ] at hy
    exact hy.symm

open scoped SemidirectProduct TensorProduct

private def cocharacterLinearAction (D : Specs.Pinning.BasedRootDatum.{u}) :
    RootPairing.Aut D.datum →* (D.Y ≃ₗ[ℤ] D.Y) where
  toFun w := w.coweightEquiv.symm
  map_one' := by
    have h := congrArg MulOpposite.unop (map_one (RootPairing.Equiv.coweightHom D.datum))
    change (1 : RootPairing.Aut D.datum).coweightEquiv = 1 at h
    change (1 : RootPairing.Aut D.datum).coweightEquiv⁻¹ = 1
    rw [h, inv_one]
  map_mul' x y := by
    have h := congrArg MulOpposite.unop (map_mul (RootPairing.Equiv.coweightHom D.datum) x y)
    change (x * y).coweightEquiv = y.coweightEquiv * x.coweightEquiv at h
    change (x * y).coweightEquiv⁻¹ = x.coweightEquiv⁻¹ * y.coweightEquiv⁻¹
    rw [h, mul_inv_rev]

private def rationalCocharacterAction (D : Specs.Pinning.BasedRootDatum.{u}) :
    RootPairing.Aut D.datum →* ((ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] D.Y)) where
  toFun w := (cocharacterLinearAction D w).baseChange ℤ ℚ D.Y D.Y
  map_one' := by simp only [map_one, LinearEquiv.baseChange_one]
  map_mul' a c := by simp only [map_mul, LinearEquiv.baseChange_mul]

private theorem integralCocharacter_injective (D : Specs.Pinning.BasedRootDatum.{u})
    {index : Type u} (b : Module.Basis index ℤ D.Y) :
    Function.Injective (fun y : D.Y => (1 : ℚ) ⊗ₜ[ℤ] y) := by
  classical
  intro x y h
  apply b.repr.injective
  ext k
  have h' := congrArg (fun z => (TensorProduct.equivFinsuppOfBasisRight b z : index →₀ ℚ) k) h
  simp only [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply, zsmul_eq_mul, mul_one] at h'
  exact_mod_cast h'

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
theorem splitApartmentAction : SplitApartmentAction.{u} := by
  classical
  intro K _ _ _ _ D M F index _ b
  letI := F.torusComm
  let C := F.identification
  let N := (𝟙_ (SchemeOver K) ⟶ C.normalizer.group.X)
  let R := CommAlgCat.of Integers.{u} K
  let O := CommAlgCat.of Integers.{u} (valuation K).valuationSubring
  let f := valuationRingInclusion K
  let J := (((integralPointFunctor M.group).map f).hom.range).comap F.point
  let V := ℚ ⊗[ℤ] D.Y
  let W := D.datum.weylGroup
  obtain ⟨e, he, hconj⟩ := fibreNormalizerTorusAction F
  obtain ⟨ν, hνsurj, hνchar, hνker⟩ := splitTorusTranslation K D b
  let vf := ν.comp e.symm.toMonoidHom
  let d := (cocharacterLinearAction D).comp W.subtype
  let ρ : W →* MulAut (Multiplicative D.Y) :=
    { toFun := fun w => (d w).toAddEquiv.toMultiplicative
      map_one' := by
        apply MulEquiv.ext
        intro y
        change Multiplicative.ofAdd (d 1 y.toAdd) = y
        rw [map_one]
        rfl
      map_mul' x y := by
        apply MulEquiv.ext
        intro z
        change Multiplicative.ofAdd (d (x * y) z.toAdd) =
          Multiplicative.ofAdd (d x (d y z.toAdd))
        rw [map_mul]
        rfl }
  let w := (rationalCocharacterAction D).comp W.subtype
  let j := (TensorProduct.mk ℤ ℚ D.Y 1).toAddMonoidHom.toMultiplicative
  have hj := integralCocharacter_injective D b
  have hji : Function.Injective j := hj
  have hwi : Function.Injective w := by
    intro x y hxy
    have h : d x = d y := by
      ext z
      apply hj
      exact congrArg (fun g : V ≃ₗ[ℚ] V => g ((1 : ℚ) ⊗ₜ[ℤ] z)) hxy
    apply Subtype.ext
    apply RootPairing.Equiv.coweightHom_injective D.datum
    have h' := congrArg (LinearEquiv.symm : (D.Y ≃ₗ[ℤ] D.Y) → _) h
    change x.val.coweightEquiv.symm.symm = y.val.coweightEquiv.symm.symm at h'
    change MulOpposite.op x.val.coweightEquiv = MulOpposite.op y.val.coweightEquiv
    simpa only [LinearEquiv.symm_symm] using congrArg MulOpposite.op h'
  have hw (w₀ : W) (y : Multiplicative D.Y) : (j (ρ w₀ y)).toAdd = w w₀ (j y).toAdd := rfl
  have hsurj : Function.Surjective vf := hνsurj.comp e.symm.surjective
  have hJsurj : Function.Surjective (F.label.comp J.subtype) := by
    intro a
    obtain ⟨n, _, p, hn, _, hp, _⟩ := splitIntegralWeylLifts M F F O f f a
    exact ⟨⟨n, ⟨p, hp⟩⟩, hn⟩
  have hJ (t : F.label.ker) : vf t = 1 ↔ t.val ∈ J := by
    have h := he (e.symm t)
    rw [e.apply_symm_apply] at h
    change ν (e.symm t) = 1 ↔ ∃ p : IntegralPoints M.group O,
      (integralPointFunctor M.group).map f p = F.point t.val
    rw [hνker, h]
    exact markedIntegralTorusKernel D M.toIntegralMarking b (e.symm t)
  have hv (n : N) (t : F.label.ker) : vf (conjugateTorus F.label n t) = ρ (F.label n) (vf t) := by
    obtain ⟨t, rfl⟩ := e.surjective t
    rw [hconj]
    apply Multiplicative.toAdd.injective
    change (ν (e.symm (e (t.comp _)))).toAdd =
      (F.label n).val.coweightEquiv.symm (ν (e.symm (e t))).toAdd
    simp only [e.symm_apply_apply]
    exact (splitTranslationAction D ν hνchar).2 (F.label n).val t
  obtain ⟨p, hp, hpk, hinj, hr, ht, _, hi, hs⟩ := normalizerApartment F.label J vf ρ j w hw
    hji hwi hsurj hJsurj hJ hv
  let A := affineTransformation ρ j w hw
  let a := A.comp p
  have hak : a.ker = p.ker := by
    ext n
    change A (p n) = 1 ↔ p n = 1
    rw [← map_one A, hinj.eq_iff]
  refine ⟨e, ν, ρ, p, a, hνsurj, hp, hpk, hak, he, hνchar, fun _ _ => rfl, hr, ?_, ?_, hi, ?_⟩
  · intro t
    exact (ht (e t)).trans (congrArg ν (e.symm_apply_apply t))
  · intro n x
    change w (p n).right (x - 0) + ((1 : ℚ) ⊗ₜ[ℤ] (p n).left.toAdd) = _
    rw [sub_zero, hr]
    rfl
  · intro n x s t hs₀ ht₀
    apply hs n x (e s) (e t)
    · change (1 : ℚ) ⊗ₜ[ℤ] (ν (e.symm (e s))).toAdd = -x
      simpa only [e.symm_apply_apply] using hs₀
    · change (1 : ℚ) ⊗ₜ[ℤ] (ν (e.symm (e t))).toAdd = -(a n x)
      simpa only [e.symm_apply_apply] using ht₀

set_option backward.isDefEq.respectTransparency false in
theorem foldedWeylLinearAction : FoldedWeylLinearAction.{u} := by
  intro D e index _ b hinv horth
  let V₀ := ℚ ⊗[ℤ] D.Y
  let V := invariantApartment D e
  let W := fixedWeylGroup D e
  let L := rationalCocharacterAction D
  let d := L e.val
  let w := L.comp (D.datum.weylGroup.subtype.comp W.subtype)
  have hv (x : V₀) : x ∈ V ↔ d x = x := sub_eq_zero
  have hw (a : W) : Commute d (w a) := by
    have ha : a.val.val ∈ Subgroup.centralizer {e.val} := a.property
    have ha' : Commute e.val a.val.val := (Subgroup.mem_centralizer_singleton_iff.mp ha).symm
    exact ha'.map L
  have hmap (a : W) (x : V) : w a x.val ∈ V := by
    apply (hv _).mpr
    have h := congrArg (fun f : V₀ ≃ₗ[ℚ] V₀ => f x.val) (hw a).eq
    change d (w a x.val) = w a (d x.val) at h
    rw [(hv _).mp x.property] at h
    exact h
  let a (g : W) : V ≃ₗ[ℚ] V :=
    { toFun := fun x => ⟨w g x.val, hmap g x⟩
      invFun := fun x => ⟨w g⁻¹ x.val, hmap g⁻¹ x⟩
      left_inv := fun x => Subtype.ext (show w g⁻¹ (w g x.val) = _ by
        rw [w.map_inv]
        exact (w g).symm_apply_apply _)
      right_inv := fun x => Subtype.ext (show w g (w g⁻¹ x.val) = _ by
        rw [w.map_inv]
        exact (w g).apply_symm_apply _)
      map_add' := fun x y => Subtype.ext ((w g).map_add x.val y.val)
      map_smul' := fun r x => Subtype.ext ((w g).map_smul r x.val) }
  let A : W →* (V ≃ₗ[ℚ] V) :=
    { toFun := a
      map_one' := by
        ext x
        change w 1 x.val = _
        rw [w.map_one]
        rfl
      map_mul' x y := by
        ext z
        change w (x * y) z.val = w x (w y z.val)
        rw [w.map_mul]
        rfl }
  refine ⟨A, ?_, fun _ _ => rfl⟩
  intro u v huv
  have h₁ : A (u⁻¹ * v) = 1 := by rw [A.map_mul, A.map_inv, huv, inv_mul_cancel]
  apply inv_mul_eq_one.mp
  apply Subtype.ext
  apply (fixedWeylGeneration D e hinv horth).2
  intro y hy
  let x : V := ⟨(1 : ℚ) ⊗ₜ[ℤ] y, (hv _).mpr (by
    change (1 : ℚ) ⊗ₜ[ℤ] (e.val.coweightEquiv.symm y) = (1 : ℚ) ⊗ₜ[ℤ] y
    rw [hy])⟩
  apply integralCocharacter_injective D b
  exact congrArg (fun f : V ≃ₗ[ℚ] V => (f x).val) h₁

end AbsoluteWeyl

section Centralizer

open AlgebraicGeometry CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup GroupScheme ClosedSubgroup)
open Specs.CharacterDescent (Cocharacter)
open Specs.Unipotent (baseChangedAlgebraicGroup closedSubgroupAlgebraicGroup)
open Specs.GeometricRadicals (IsSplitTorus IsTorus IsMaximalTorus)
open Specs.GeometricBorelConjugacy (subgroupOfSubgroup)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.SubtorusCentralizer (IsCentralizer)
open private centralizes_iff conjugateLe_iff from LinearAlgebraicGroups.Affine.Stabilizers
open private torus_commutative from LinearAlgebraicGroups.Reductive.TorusFreeUnipotent
open private factor_of_baseChange from LinearAlgebraicGroups.Affine.ClosedSubgroups
open private factor_group_through_subgroup conjugation conjugation_apply
  from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private normalizes_iff_sections normalizes_inv conjugates_of_normalizes
  from LinearAlgebraicGroups.RootData.BorelNormalizer
open private extendSubgroup subgroup_extend subgroup_descend
  from LinearAlgebraicGroups.RootData.BorelNormalizer
open private isTorus_of_split from LinearAlgebraicGroups.Descent.FiniteFieldFlags
open private conjugate conjugate_inclusion from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private extendedCoordinateIso extendedCoordinateIso_comm groundBorelSmooth isIso_torus_to_limit
  from LinearAlgebraicGroups.Descent.AdjointBorelCohomology
open private local_maximal_of_ambient restrictSubgroup compose_restrict inclusion_mono
  from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private torus_after_algClosed_extension from LinearAlgebraicGroups.Reductive.MaximalToriExist
open private subgroupOf_mutual_iso subgroupOf_trans
  from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private splitTorusImage from LinearAlgebraicGroups.Relative.MaximalSplitTori
open private multiplicative_group_iso from LinearAlgebraicGroups.Relative.LeviConjugacy

private theorem centralizes_of_torus_factor {k : Type u} [Field k] {G : GroupScheme k}
    {S T : ClosedSubgroup G} (j : S.group ⟶ T.group) (hj : j ≫ T.inclusion = S.inclusion)
    [IsCommMonObj T.group.X] {Y : SchemeOver k} (p : Y ⟶ T.group.X) :
    Centralizes S.inclusion (p ≫ T.inclusion.hom.hom) := by
  apply (centralizes_iff _ _).mpr
  intro U t s
  have h : Commute (t ≫ p) (s ≫ j.hom.hom) := Commute.all _ _
  have h' := h.map (IsMonHom.monoidHom T.inclusion.hom.hom U)
  change Commute ((t ≫ p) ≫ T.inclusion.hom.hom)
    ((s ≫ j.hom.hom) ≫ T.inclusion.hom.hom) at h'
  simpa only [Category.assoc, ← Grp.comp_hom_hom, hj] using h'

set_option backward.isDefEq.respectTransparency false in
theorem regularSubtorusCentralizer : RegularSubtorusCentralizer.{u} := by
  intro k K _ _ _ G hG T S hT j hj F hTK TK hsK hmK c hc
  let H := baseChangedAlgebraicGroup K G
  let cc := c ≫ F.map j
  have hH := (Reductive.RadicalBaseChange.reductiveFieldExtension (K := K) G hG.1 hG.2.1).mpr hG
  obtain ⟨D⟩ := CocharacterDynamics.existsLimitDecomposition H (cc ≫ TK.inclusion)
  have hD := (RootData.BorelsAndChambers.regularCocharacterBorel H hH TK hsK hmK cc hc D).1.1
  obtain ⟨a, ha⟩ := hD
  obtain ⟨C, hC⟩ := centralizerScheme k G S
  obtain ⟨hCK, hC'⟩ := centralizerSchemeBaseChange k K S.inclusion C hC
  let CK := scalarExtendedSubgroup K C hCK
  have hZ : Centralizes (F.map S.inclusion) CK.inclusion.hom.hom :=
    (hC' _ _).mpr ⟨𝟙 _, Category.id_comp _⟩
  have hcS : cc ≫ TK.inclusion = c ≫ F.map S.inclusion := by
    change (c ≫ F.map j) ≫ F.map T.inclusion = _
    rw [Category.assoc, ← Functor.map_comp, hj]
  have hZ' : Centralizes (cc ≫ TK.inclusion) CK.inclusion.hom.hom := by
    rw [hcS]
    apply (centralizes_iff _ _).mpr
    intro U p v
    exact ((centralizes_iff _ _).mp hZ U p (v ≫ c.hom.hom))
  obtain ⟨v, hv⟩ := (D.centralizer_points _ _).mp hZ'
  have ha' := congrArg (fun f => f.hom.hom) ha
  change a.hom.hom ≫ TK.inclusion.hom.hom = D.centralizer.inclusion.hom.hom at ha'
  have hv' : (v ≫ a.hom.hom) ≫ TK.inclusion.hom.hom = CK.inclusion.hom.hom := by
    rw [Category.assoc, ha', hv]
  letI := T.isClosedImmersion
  obtain ⟨f, hf⟩ := factor_of_baseChange K C.inclusion.hom.hom T.inclusion.hom.hom
    (v ≫ a.hom.hom) hv'
  intro Y t
  constructor
  · intro ht
    obtain ⟨b, hb⟩ := (hC Y t).mp ht
    exact ⟨b ≫ f, by rw [Category.assoc, hf, hb]⟩
  · rintro ⟨b, rfl⟩
    letI : IsCommMonObj T.group.X := torus_commutative (closedSubgroupAlgebraicGroup T) hT
    exact centralizes_of_torus_factor j hj b

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 500000 in
theorem borelSplitTorusCentralizer : BorelSplitTorusCentralizer.{u} := by
  intro k _ G hG B T S hB hT ht hTB hST hs
  obtain ⟨j, hj⟩ := hTB
  obtain ⟨a, ha⟩ := hST
  let K := AlgebraicClosure k
  have hMT : IsMaximalTorus T := by
    refine ⟨hT, fun U hu hTU ↦ ?_⟩
    obtain ⟨h, hh⟩ := ht
    have hM : IsMaximalTorus (extendSubgroup K T) := hh
    exact subgroup_descend K (hM.2 (extendSubgroup K U)
      (torus_after_algClosed_extension K (closedSubgroupAlgebraicGroup U) hu)
      (subgroup_extend K hTU))
  let U := restrictSubgroup T B j hj
  have hU : subgroupOfSubgroup B U = T := compose_restrict T B j hj
  have hUM : IsMaximalTorus U := local_maximal_of_ambient B U (hU.symm ▸ hMT)
  have hP : Specs.BorelProper.IsParabolic G B := by
    have hSmooth := groundBorelSmooth hB
    obtain ⟨h, hh⟩ := hB
    exact ⟨hG, hSmooth, h, _, hh, 𝟙 _, Category.id_comp _⟩
  obtain ⟨c, D, hD, _, hRad⟩ := Relative.RationalCocharacter.rationalParabolicThroughTorus G B hP U hUM
  obtain ⟨e, he⟩ := subgroupOf_mutual_iso hD.1 hD.2
  let d := c ≫ (subgroupOfSubgroup B U).inclusion
  have hd : d = c ≫ T.inclusion := by
    change c ≫ (j ≫ B.inclusion) = _
    rw [hj]
  letI : IsCommMonObj T.group.X := torus_commutative (closedSubgroupAlgebraicGroup T) hT
  have hc : Centralizes d T.inclusion.hom.hom := by
    rw [hd]
    apply (centralizes_iff _ _).mpr
    intro Y y z
    have hh : Commute y (z ≫ c.hom.hom) := Commute.all _ _
    exact hh.map (IsMonHom.monoidHom T.inclusion.hom.hom Y)
  obtain ⟨x, hx⟩ := (D.centralizer_points _ _).mp hc
  obtain ⟨i, hi⟩ := factor_group_through_subgroup D.centralizer T.inclusion x hx
  have hi' : j ≫ e.hom = i ≫ D.sectionMap := by
    letI : Mono D.parabolic.inclusion := inclusion_mono D.parabolic
    apply (cancel_mono D.parabolic.inclusion).mp
    rw [Category.assoc, he, hj, Category.assoc, D.section_in_G, hi]
  have hiIso : IsIso i := by
    have hh : IsIso (U.inclusion ≫ e.hom ≫ D.limit) := isIso_torus_to_limit D e hG hB
      (hU.symm ▸ ht) hRad
    change IsIso (j ≫ e.hom ≫ D.limit) at hh
    rwa [← Category.assoc, hi', Category.assoc, D.section_limit, Category.comp_id] at hh
  let ev := asIso i
  let M := Specs.DiagonalizableGroups.IntegerCharacters.{u}
  let E : Multiplicative ℤ ≃* M := MulEquiv.ulift.symm
  letI : Group.FG M := Group.fg_of_surjective (f := E.toMonoidHom) E.surjective
  let A := Specs.DiagonalizableGroups.diagonalGroup k M
  have hA : IsSplitTorus A.val := ⟨1, multiplicative_group_iso⟩
  obtain ⟨I, p, hp, hI⟩ := splitTorusImage A (closedSubgroupAlgebraicGroup T) hA c
  let J := subgroupOfSubgroup T I
  obtain ⟨q, hq⟩ := hs J hp ⟨I.inclusion, rfl⟩
  have hcomp : (p ≫ q) ≫ S.inclusion = d := by
    rw [Category.assoc, hq, hd]
    change p ≫ I.inclusion ≫ T.inclusion = _
    rw [← Category.assoc, hI.1]
  intro Y y
  constructor
  · intro hy
    have hy' : Centralizes d y := by
      rw [← hcomp]
      apply (centralizes_iff _ _).mpr
      intro V v w
      exact (centralizes_iff _ _).mp hy V v (w ≫ (p ≫ q).hom.hom)
    obtain ⟨z, hz⟩ := (D.centralizer_points Y y).mp hy'
    refine ⟨z ≫ ev.inv.hom.hom, ?_⟩
    change z ≫ (ev.inv ≫ T.inclusion).hom.hom = _
    rw [← hi, ← Category.assoc]
    change z ≫ (ev.inv ≫ ev.hom ≫ _).hom.hom = _
    rw [Iso.inv_hom_id_assoc, hz]
  · rintro ⟨z, rfl⟩
    exact centralizes_of_torus_factor a ha z

set_option backward.isDefEq.respectTransparency false in
theorem centralizingSplitTorusNormalizer : CentralizingSplitTorusNormalizer.{u} := by
  intro k _ G T S hs hST hc hm
  obtain ⟨j, hj⟩ := hST
  constructor
  · refine ⟨hs, fun U hU hSU ↦ hm U hU ?_⟩
    obtain ⟨i, hi⟩ := hSU
    letI : IsCommMonObj U.group.X :=
      torus_commutative (closedSubgroupAlgebraicGroup U) (isTorus_of_split hU)
    have hu := centralizes_of_torus_factor i hi (𝟙 U.group.X)
    rw [Category.id_comp] at hu
    obtain ⟨v, hv⟩ := (hc _ _).mp hu
    exact factor_group_through_subgroup T U.inclusion v hv
  · intro g
    constructor
    · intro hg
      have h (n : 𝟙_ (SchemeOver k) ⟶ G.val.X) (hn : Normalizes S.inclusion n)
          (Y : SchemeOver k) (y : Y ⟶ 𝟙_ (SchemeOver k)) (t : Y ⟶ T.group.X) :
          ∃ u : Y ⟶ T.group.X, u ≫ T.inclusion.hom.hom =
            (y ≫ n) * (t ≫ T.inclusion.hom.hom) * (y ≫ n)⁻¹ := by
        apply (hc _ _).mp
        apply (centralizes_iff _ _).mpr
        intro V v s
        let a := (v ≫ y) ≫ n
        let b := (v ≫ t) ≫ T.inclusion.hom.hom
        let c := s ≫ S.inclusion.hom.hom
        obtain ⟨d, hd⟩ := ((normalizes_iff_sections S n).mp hn V (v ≫ y) s).2
        have hb := (centralizes_iff _ _).mp ((hc Y (t ≫ T.inclusion.hom.hom)).mpr ⟨t, rfl⟩) V v d
        rw [hd] at hb
        simp only [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc]
        change Commute (a * b * a⁻¹) c
        change Commute b (a⁻¹ * c * a) at hb
        calc
          (a * b * a⁻¹) * c = a * (b * (a⁻¹ * c * a)) * a⁻¹ := by group
          _ = a * ((a⁻¹ * c * a) * b) * a⁻¹ := congrArg (fun x => a * x * a⁻¹) hb.eq
          _ = c * (a * b * a⁻¹) := by group
      apply (normalizes_iff_sections T g).mpr
      intro Y y t
      exact ⟨h g hg Y y t, by
        simpa only [GrpObj.comp_inv, inv_inv] using h g⁻¹ (normalizes_inv S hg) Y y t⟩
    · intro hg
      have h (n : 𝟙_ (SchemeOver k) ⟶ G.val.X) (hn : Normalizes T.inclusion n)
          (Y : SchemeOver k) (y : Y ⟶ 𝟙_ (SchemeOver k)) (t : Y ⟶ S.group.X) :
          ∃ u : Y ⟶ S.group.X, u ≫ S.inclusion.hom.hom =
            (y ≫ n) * (t ≫ S.inclusion.hom.hom) * (y ≫ n)⁻¹ := by
        let U := conjugate n S
        obtain ⟨e, he⟩ := conjugates_of_normalizes T hn
        have hu : IsSubgroupOf U T := by
          refine ⟨j ≫ e.hom, ?_⟩
          apply Grp.hom_ext
          change j.hom.hom ≫ (e.hom ≫ T.inclusion).hom.hom =
            S.inclusion.hom.hom ≫ (conjugation n).hom.hom
          rw [he, conjugation_apply]
          simp only [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, comp_toUnit]
          have h' := congrArg (fun f => f.hom.hom) hj
          exact congrArg (fun p => (toUnit S.group.X ≫ n) * p * (toUnit S.group.X ≫ n)⁻¹) h'
        obtain ⟨i, hi⟩ := hm U hs hu
        refine ⟨t ≫ i.hom.hom, ?_⟩
        change t ≫ (i ≫ S.inclusion).hom.hom = _
        rw [hi, conjugate_inclusion, Grp.comp_hom_hom, ← Category.assoc, conjugation_apply]
        rw [show toUnit Y = y from Subsingleton.elim _ _]
      apply (normalizes_iff_sections S g).mpr
      intro Y y t
      exact ⟨h g hg Y y t, by
        simpa only [GrpObj.comp_inv, inv_inv] using h g⁻¹ (normalizes_inv T hg) Y y t⟩

set_option backward.isDefEq.respectTransparency false in
theorem rationalNormalizerBaseChange : RationalNormalizerBaseChange.{u} := by
  intro k K _ _ _ G T g
  obtain ⟨N, hN⟩ := normalizerScheme k G T
  obtain ⟨hNK, hN'⟩ := normalizerSchemeBaseChange k K T.inclusion N T.isClosedImmersion hN
  let F := baseChange k K
  let ε := Functor.LaxMonoidal.ε F
  let e := asIso ε
  refine (hN _ g).trans (Iff.trans ?_ (hN' _ (scalarExtendedRationalPoint K g)).symm)
  change (∃ n : 𝟙_ (SchemeOver k) ⟶ N.group.X, n ≫ N.inclusion.hom.hom = g) ↔
    ∃ n : 𝟙_ (SchemeOver K) ⟶ F.obj N.group.X,
      n ≫ F.map N.inclusion.hom.hom = ε ≫ F.map g
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨ε ≫ F.map n, by rw [Category.assoc, ← F.map_comp]⟩
  · rintro ⟨n, hn⟩
    have hf : (e.inv ≫ n) ≫ F.map N.inclusion.hom.hom = F.map g := by
      rw [Category.assoc, hn]
      exact e.inv_hom_id_assoc _
    letI := N.isClosedImmersion
    exact factor_of_baseChange K g N.inclusion.hom.hom (e.inv ≫ n) hf

private theorem conjugateLe_of_iso {k : Type u} [Field k] {G H : GroupScheme k}
    (T : ClosedSubgroup G) (U : ClosedSubgroup H) (e : G ≅ H) (t : T.group ≅ U.group)
    (h : t.hom ≫ U.inclusion = T.inclusion ≫ e.hom)
    {Y : SchemeOver k} {g : Y ⟶ G.X} (hg : ConjugateLe T.inclusion g) :
    ConjugateLe U.inclusion (g ≫ e.hom.hom.hom) := by
  apply (conjugateLe_iff _ _).mpr
  intro X x b
  let v := b ≫ t.inv.hom.hom
  let m := IsMonHom.monoidHom e.hom.hom.hom X
  have hp (z : X ⟶ T.group.X) :
      (z ≫ t.hom.hom.hom) ≫ U.inclusion.hom.hom = m (z ≫ T.inclusion.hom.hom) := by
    change z ≫ (t.hom ≫ U.inclusion).hom.hom = z ≫ (T.inclusion ≫ e.hom).hom.hom
    rw [h]
  have hb : v ≫ t.hom.hom.hom = b := by
    dsimp only [v]
    have hi := congrArg (fun f => f.hom.hom) t.inv_hom_id
    change t.inv.hom.hom ≫ t.hom.hom.hom = 𝟙 _ at hi
    rw [Category.assoc, hi, Category.comp_id]
  obtain ⟨z, hz⟩ := (conjugateLe_iff _ _).mp hg X x v
  refine ⟨z ≫ t.hom.hom.hom, ?_⟩
  rw [hp, hz, map_mul m, map_mul m, map_inv m, ← hp v, hb]
  simp only [m, IsMonHom.monoidHom_apply, Category.assoc]

private theorem normalizes_of_iso {k : Type u} [Field k] {G H : GroupScheme k}
    (T : ClosedSubgroup G) (U : ClosedSubgroup H) (e : G ≅ H) (t : T.group ≅ U.group)
    (h : t.hom ≫ U.inclusion = T.inclusion ≫ e.hom)
    {Y : SchemeOver k} {g : Y ⟶ G.X} (hg : Normalizes T.inclusion g) :
    Normalizes U.inclusion (g ≫ e.hom.hom.hom) := by
  obtain ⟨h₁, h₂⟩ := (normalizesIff k T.inclusion T.isClosedImmersion _ _).mp hg
  apply (normalizesIff k U.inclusion U.isClosedImmersion _ _).mpr
  exact ⟨conjugateLe_of_iso T U e t h h₁, by
    rw [← GrpObj.inv_comp]
    exact conjugateLe_of_iso T U e t h h₂⟩

set_option backward.isDefEq.respectTransparency false in
private theorem normalizingComparison {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G H : AffineAlgebraicGroup k} (T : ClosedSubgroup G.val) (U : ClosedSubgroup H.val)
    (e : (groupBaseChange k K).obj G.val ≅ (groupBaseChange k K).obj H.val)
    (t : (groupBaseChange k K).obj T.group ≅ (groupBaseChange k K).obj U.group)
    (ht : t.hom ≫ (groupBaseChange k K).map U.inclusion =
      (groupBaseChange k K).map T.inclusion ≫ e.hom)
    (g : 𝟙_ (SchemeOver k) ⟶ G.val.X) :
    Normalizes T.inclusion g ↔ Normalizes ((groupBaseChange k K).map U.inclusion)
      (scalarExtendedRationalPoint K g ≫ e.hom.hom.hom) := by
  rw [rationalNormalizerBaseChange (K := K) G T g]
  let F := groupBaseChange k K
  let TK := scalarExtendedSubgroup K T (baseChangeClosedSubgroup k K T.inclusion T.isClosedImmersion)
  let SK := scalarExtendedSubgroup K U (baseChangeClosedSubgroup k K U.inclusion U.isClosedImmersion)
  let n : 𝟙_ (SchemeOver K) ⟶ (F.obj G.val).X := scalarExtendedRationalPoint K g
  constructor
  · exact normalizes_of_iso TK SK e t ht
  · intro hn
    have h : t.inv ≫ TK.inclusion = SK.inclusion ≫ e.inv := by
      change t.inv ≫ F.map T.inclusion = F.map U.inclusion ≫ e.inv
      symm
      rw [Iso.comp_inv_eq, Category.assoc, ← ht, Iso.inv_hom_id_assoc]
    have hr := normalizes_of_iso SK TK e.symm t.symm h hn
    change Normalizes TK.inclusion ((n ≫ e.hom.hom.hom) ≫ e.inv.hom.hom) at hr
    have he := congrArg (fun f => f.hom.hom) e.hom_inv_id
    change e.hom.hom.hom ≫ e.inv.hom.hom = 𝟙 _ at he
    rw [Category.assoc, he, Category.comp_id] at hr
    exact hr

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 550000 in
theorem pinnedNormalizerComparison : PinnedNormalizerComparison.{u} := by
  intro k K _ _ _ A P D l G B T d F
  let H := closedSubgroupAlgebraicGroup T
  let H₀ := closedSubgroupAlgebraicGroup P.pair.T
  let e : F.obj G.val ≅ F.obj P.pair.G.val := (extendedCoordinateIso (K := K) G).symm ≪≫
    (hopfSpec (CommRingCat.of K)).mapIso d.groupIso.op ≪≫ extendedCoordinateIso (K := K) P.pair.G
  let t : F.obj T.group ≅ F.obj P.pair.T.group := (extendedCoordinateIso (K := K) H).symm ≪≫
    (hopfSpec (CommRingCat.of K)).mapIso d.torusIso.op ≪≫ extendedCoordinateIso (K := K) H₀
  have ht : t.hom ≫ F.map P.pair.T.inclusion = F.map T.inclusion ≫ e.hom :=
    extendedCoordinateIso_comm (G := H) (G₀ := H₀) (H := G) (H₀ := P.pair.G)
      T.inclusion P.pair.T.inclusion d.torusIso d.groupIso d.torusComm
  exact ⟨e, t, ht, normalizingComparison T P.pair.T e t ht⟩

set_option backward.isDefEq.respectTransparency false in
theorem descendedRelativeNormalizer : DescendedRelativeNormalizer.{u} := by
  intro k K _ _ _ _ A P D l ω d I _ r b hb
  obtain ⟨q, h, hs, hST, hm, _⟩ := largestSplitPermutationSubtorus d.torus b hb
  let S := Specs.GeometricBorelConjugacy.subgroupOfSubgroup d.torus
    ⟨_, specGroupMap q ≫ (Specs.AdjointCocharacters.coordinateHopfIso
      (closedSubgroupAlgebraicGroup d.torus)).hom, h⟩
  have hTB : IsSubgroupOf d.torus d.borel := ⟨d.inclusion, d.inclusion_comm⟩
  have hc : IsCentralizer S d.torus := borelSplitTorusCentralizer d.group d.reductive d.borel
    d.torus S d.isKBorel d.isTorus d.isMaximal hTB hST hm
  obtain ⟨hS, hN⟩ := centralizingSplitTorusNormalizer d.group d.torus S hs hST hc hm
  have hP : Specs.Relative.MaximalSplitTori.IsMinimalParabolic d.group d.borel := by
    constructor
    · obtain ⟨hB, hh⟩ := d.isKBorel
      exact ⟨d.reductive, groundBorelSmooth d.isKBorel, hB, _, hh, 𝟙 _, Category.id_comp _⟩
    · intro Q hQ hQB
      let E := AlgebraicClosure k
      obtain ⟨hQ', B', hB', hBQ⟩ := hQ.2.2
      obtain ⟨hB, hBg⟩ := d.isKBorel
      have h₁ : IsSubgroupOf B' (extendSubgroup E Q) := hBQ
      have h₂ : IsSubgroupOf B' (extendSubgroup E d.borel) :=
        subgroupOf_trans h₁ (subgroup_extend E hQB)
      exact subgroup_descend E (subgroupOf_trans (hB'.2 _ hBg.1 h₂) h₁)
  obtain ⟨N, _⟩ := Relative.RelativeWeylScheme.finiteConstantQuotient d.group d.reductive S hS
  have hC : Specs.RankOneFlag.SameSubgroup N.centralizer d.torus := by
    constructor
    · have h := (N.centralizerProperty _ N.centralizer.inclusion.hom.hom).mpr ⟨𝟙 _, Category.id_comp _⟩
      obtain ⟨f, hf⟩ := (hc _ _).mp h
      exact factor_group_through_subgroup d.torus N.centralizer.inclusion f hf
    · have h := (hc _ d.torus.inclusion.hom.hom).mpr ⟨𝟙 _, Category.id_comp _⟩
      obtain ⟨f, hf⟩ := (N.centralizerProperty _ _).mp h
      exact factor_group_through_subgroup N.centralizer d.torus.inclusion f hf
  obtain ⟨_, _, _, _, hlift, _, _⟩ := Relative.RelativeWeylScheme.relativeWeylAction d.group d.reductive
    S d.borel hS hP (subgroupOf_trans hST hTB) N
  exact ⟨S, N, hS, hST, hc, hC, hN, hlift⟩

end Centralizer

section FixedNormalizer

open AlgebraicGeometry CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct
open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup GroupScheme ClosedSubgroup)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open _root_.LinearAlgebraicGroups.Descent (SemilinearAction)
open private extendedCoordinateIso_comm from LinearAlgebraicGroups.Descent.AdjointBorelCohomology
open Specs.AdjointCocharacters renaming coordinateHopf → affineCoordinates
open Specs.AdjointCocharacters (coordinateHopfIso)
open private extendedCoordinateIso from LinearAlgebraicGroups.Descent.AdjointBorelCohomology
open private extendedSpecIso extendedSpecIso_hom_fst
  from LinearAlgebraicGroups.Affine.ClosedSubgroups
open private groundIso from LinearAlgebraicGroups.Solvable.TorusSections

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

set_option backward.isDefEq.respectTransparency false in
private def hopfRationalPoint (A : HopfAlgebraCategory k) (p : A →ₐ[k] k) :
    𝟙_ (SchemeOver k) ⟶ (specGroup A).X :=
  (groundIso (k := k)).inv ≫ (testSpec k).map (CommAlgCat.ofHom p).op

private def groundExtendPoint (A : HopfAlgebraCategory k) (p : A →ₐ[k] k) :
    extendedHopf K A →ₐ[K] K :=
  (Algebra.TensorProduct.rid k K K).toAlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id K K) p)

set_option backward.isDefEq.respectTransparency false in
private theorem scalarRationalPoint_comp {X Y : SchemeOver k}
    (p : 𝟙_ (SchemeOver k) ⟶ X) (f : X ⟶ Y) :
    scalarExtendedRationalPoint K (p ≫ f) =
      scalarExtendedRationalPoint K p ≫ (baseChange k K).map f := by
  unfold scalarExtendedRationalPoint
  rw [Functor.map_comp, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem scalarHopfPoint (A : HopfAlgebraCategory k) (p : A →ₐ[k] k) :
    scalarExtendedRationalPoint K (hopfRationalPoint A p) =
      hopfRationalPoint (extendedHopf K A) (groundExtendPoint A p) ≫
        (extendedSpecIso K A).hom := by
  apply Over.OverMorphism.ext
  let b := fieldSpecMap k K
  let a := (specGroup A).X.hom
  apply pullback.hom_ext
  · change ((Functor.LaxMonoidal.ε (baseChange k K)).left ≫
        ((baseChange k K).map (hopfRationalPoint A p)).left) ≫ pullback.fst a b = _
    rw [Category.assoc]
    change (Functor.LaxMonoidal.ε (baseChange k K)).left ≫
      ((Over.pullback b).map (hopfRationalPoint A p)).left ≫ pullback.fst a b = _
    have hmap : ((baseChange k K).map (hopfRationalPoint A p)).left ≫ pullback.fst a b =
        pullback.fst (𝟙_ (SchemeOver k)).hom b ≫ (hopfRationalPoint A p).left := by
      change (pullback.lift (pullback.fst (𝟙_ (SchemeOver k)).hom b ≫
        (hopfRationalPoint A p).left) (pullback.snd (𝟙_ (SchemeOver k)).hom b) _) ≫ pullback.fst a b = _
      exact pullback.lift_fst ..
    rw [hmap]
    have hε : (Functor.LaxMonoidal.ε (baseChange k K)).left ≫
        pullback.fst (𝟙_ (SchemeOver k)).hom b = b := by
      have hw : (Functor.LaxMonoidal.ε (baseChange k K)).left ≫
          pullback.snd (𝟙_ (SchemeOver k)).hom b = 𝟙 _ := Over.w _
      change _ ≫ pullback.snd (𝟙 (Spec (CommRingCat.of k))) b = 𝟙 _ at hw
      change _ ≫ pullback.fst (𝟙 (Spec (CommRingCat.of k))) b = b
      calc
        _ = ((Functor.LaxMonoidal.ε (baseChange k K)).left ≫
          pullback.fst (𝟙 (Spec (CommRingCat.of k))) b) ≫ 𝟙 _ := (Category.comp_id _).symm
        _ = _ := by
          rw [Category.assoc, pullback.condition, ← Category.assoc, hw]
          exact Category.id_comp b
    rw [← Category.assoc, hε]
    change b ≫ (hopfRationalPoint A p).left =
      ((hopfRationalPoint (extendedHopf K A) (groundExtendPoint A p)).left ≫
        (extendedSpecIso K A).hom.left) ≫ pullback.fst a b
    rw [Category.assoc, extendedSpecIso_hom_fst]
    change Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ Spec.map (CommRingCat.ofHom p.toRingHom) =
      Spec.map (CommRingCat.ofHom (groundExtendPoint (K := K) A p).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A).toRingHom)
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    change algebraMap k K (p x) = (Algebra.TensorProduct.rid k K K) (1 ⊗ₜ[k] p x)
    simp [Algebra.smul_def]
  · exact (Over.w _).trans (Over.w _).symm

open WithConv
open private extendCoordinatePoint_mul from LinearAlgebraicGroups.Descent.AdjointBorelCohomology

private def hopfRationalEquiv (A : HopfAlgebraCategory k) :
    WithConv (A →ₐ[k] k) ≃* (𝟙_ (SchemeOver k) ⟶ (specGroup A).X) := by
  let Y := (testSpec k).obj (Opposite.op (CommAlgCat.of k k))
  let b := (groundIso (k := k)).inv
  let t : (Y ⟶ (specGroup A).X) →* (𝟙_ (SchemeOver k) ⟶ (specGroup A).X) :=
    MonoidHom.mk' (fun p => b ≫ p) (MonObj.comp_mul b)
  letI : IsIso b := (groundIso (k := k)).isIso_inv
  let e := MulEquiv.ofBijective t ⟨fun _ _ h => (cancel_epi b).mp h, fun p =>
    ⟨(groundIso (k := k)).hom ≫ p, (groundIso (k := k)).inv_hom_id_assoc p⟩⟩
  exact (((hopfSpecPointIso A).app (CommAlgCat.of k k)).groupIsoToMulEquiv).trans e

set_option backward.isDefEq.respectTransparency false in
private theorem hopfRationalEquiv_apply (A : HopfAlgebraCategory k) (p : A →ₐ[k] k) :
    hopfRationalEquiv A (toConv p) = hopfRationalPoint A p := by
  apply Over.OverMorphism.ext
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem scalarPresentedCoordinate (G : AffineAlgebraicGroup k)
    (p : affineCoordinates G →ₐ[k] k) :
    scalarExtendedRationalPoint K (hopfRationalPoint (affineCoordinates G) p ≫ (coordinateHopfIso G).hom.hom.hom) =
      hopfRationalPoint (extendedHopf K (affineCoordinates G)) (groundExtendPoint (affineCoordinates G) p) ≫
        (extendedCoordinateIso (K := K) G).hom.hom.hom := by
  rw [scalarRationalPoint_comp, scalarHopfPoint, Category.assoc]
  rfl

private def groundExtendPointHom (A : HopfAlgebraCategory k) :
    WithConv (A →ₐ[k] k) →* WithConv (extendedHopf K A →ₐ[K] K) :=
  MonoidHom.mk' (fun p => toConv (groundExtendPoint A p.ofConv)) (by
    intro p q
    apply WithConv.ofConv_injective
    let r : K ⊗[k] k →ₐ[K] K := (Algebra.TensorProduct.rid k K K).toAlgHom
    let P := Algebra.TensorProduct.map (AlgHom.id K K) p.ofConv
    let Q := Algebra.TensorProduct.map (AlgHom.id K K) q.ofConv
    have he := extendCoordinatePoint_mul (K := K) (CommAlgCat.of k k) p q
    change Algebra.TensorProduct.map (AlgHom.id K K) (p * q).ofConv =
      (toConv P * toConv Q).ofConv at he
    change r.comp (Algebra.TensorProduct.map (AlgHom.id K K) (p * q).ofConv) =
      (toConv (r.comp P) * toConv (r.comp Q)).ofConv
    rw [he]
    exact AlgHom.comp_convMul_distrib r (toConv P) (toConv Q))

set_option backward.isDefEq.respectTransparency false in
private theorem rationalPoint_compHopf {A B : HopfAlgebraCategory k}
    (f : A ⟶ B) (p : B →ₐ[k] k) :
    hopfRationalPoint B p ≫ (specGroupMap f).hom.hom = hopfRationalPoint A (p.comp f.hom.toAlgHom) := by
  apply Over.OverMorphism.ext
  change (_ ≫ Spec.map (CommRingCat.ofHom p.toRingHom)) ≫ Spec.map (CommRingCat.ofHom f.hom.toAlgHom.toRingHom) =
    _ ≫ Spec.map (CommRingCat.ofHom (p.comp f.hom.toAlgHom).toRingHom)
  rw [Category.assoc, ← Spec.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem hopfRationalPoint_eq {A : HopfAlgebraCategory k} (p : A →ₐ[k] k) :
    hopfRationalPoint A p = hopfFieldPoint p := by
  apply Over.OverMorphism.ext
  exact Category.id_comp (Spec.map (CommRingCat.ofHom p.toRingHom))

set_option backward.isDefEq.respectTransparency false in
private theorem extendedPresentation (G : AffineAlgebraicGroup k) :
    ExtendsCoordinatePresentation G (extendedCoordinateIso (K := K) G) := by
  let A := affineCoordinates G
  let g := coordinateHopfIso G
  let b := fieldSpecMap k K
  let F := groupBaseChange k K
  have hf : (F.map g.hom).hom.hom.left ≫ pullback.fst G.val.X.hom b =
      pullback.fst (specGroup A).X.hom b ≫ g.hom.hom.hom.left := by
    change pullback.lift (pullback.fst (specGroup A).X.hom b ≫ g.hom.hom.hom.left)
      (pullback.snd (specGroup A).X.hom b) _ ≫ pullback.fst G.val.X.hom b = _
    exact pullback.lift_fst ..
  change ((extendedSpecIso K A).hom.left ≫ (F.map g.hom).hom.hom.left) ≫
    pullback.fst G.val.X.hom b = _
  rw [Category.assoc, hf, ← Category.assoc, extendedSpecIso_hom_fst]

private def sectionsIso {G H : GroupScheme k} (e : G ≅ H) :
    (𝟙_ (SchemeOver k) ⟶ G.X) ≃* (𝟙_ (SchemeOver k) ⟶ H.X) :=
  MulEquiv.ofBijective (IsMonHom.monoidHom e.hom.hom.hom (𝟙_ (SchemeOver k)))
    (((Grp.forget (SchemeOver k)).mapIso e).homToEquiv.bijective)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 600000 in
theorem pinnedFixedRationalNormalizer : PinnedFixedRationalNormalizer.{u} := by
  intro k K _ _ _ _ A P D l G B T d
  let F := groupBaseChange k K
  let A₁ := affineCoordinates G
  let A₂ := affineCoordinates P.pair.G
  let b₁ := extendedCoordinateIso (K := K) G
  let b₂ := extendedCoordinateIso (K := K) P.pair.G
  let b := (hopfSpec (CommRingCat.of K)).mapIso d.groupIso.op
  let e := b₁.symm ≪≫ b ≪≫ b₂
  let T₁ := closedSubgroupAlgebraicGroup T
  let T₂ := closedSubgroupAlgebraicGroup P.pair.T
  let t : F.obj T.group ≅ F.obj P.pair.T.group := (extendedCoordinateIso (K := K) T₁).symm ≪≫
    (hopfSpec (CommRingCat.of K)).mapIso d.torusIso.op ≪≫ extendedCoordinateIso (K := K) T₂
  have ht : t.hom ≫ F.map P.pair.T.inclusion = F.map T.inclusion ≫ e.hom :=
    extendedCoordinateIso_comm (G := T₁) (G₀ := T₂) (H := G) (H₀ := P.pair.G)
      T.inclusion P.pair.T.inclusion d.torusIso d.groupIso d.torusComm
  let g₁ := (hopfRationalEquiv A₁).trans (sectionsIso (coordinateHopfIso G))
  let g₂ := (hopfRationalEquiv (extendedHopf K A₂)).trans (sectionsIso b₂)
  let m : WithConv (extendedHopf K A₁ →ₐ[K] K) →* WithConv (extendedHopf K A₂ →ₐ[K] K) :=
    MonoidHom.mk' (fun f => toConv (f.ofConv.comp d.groupIso.hom.hom.toAlgHom)) (by
      intro f g
      exact ofConv_injective (AlgHom.convMul_comp_bialgHom_distrib f g d.groupIso.hom.hom))
  let L := m.comp (groundExtendPointHom (K := K) A₁)
  let f := g₂.toMonoidHom.comp (L.comp g₁.symm.toMonoidHom)
  have hf (p : WithConv (A₁ →ₐ[k] k)) : f (g₁ p) = g₂ (L p) := by
    change g₂ (L (g₁.symm (g₁ p))) = _
    rw [g₁.symm_apply_apply]
  have h₁ (p : A₁ →ₐ[k] k) : g₁ (toConv p) =
      hopfRationalPoint A₁ p ≫ (coordinateHopfIso G).hom.hom.hom := by
    change hopfRationalEquiv A₁ (toConv p) ≫ (coordinateHopfIso G).hom.hom.hom = _
    rw [hopfRationalEquiv_apply]
  have h₂ (p : extendedHopf K A₂ →ₐ[K] K) : g₂ (toConv p) =
      hopfRationalPoint (extendedHopf K A₂) p ≫ b₂.hom.hom.hom := by
    change hopfRationalEquiv (extendedHopf K A₂) (toConv p) ≫ b₂.hom.hom.hom = _
    rw [hopfRationalEquiv_apply]
  have hactual (g : 𝟙_ (SchemeOver k) ⟶ G.val.X) :
      f g = scalarExtendedRationalPoint K g ≫ e.hom.hom.hom := by
    obtain ⟨p, rfl⟩ := g₁.surjective g
    have hh : L p = toConv ((groundExtendPoint (K := K) A₁ p.ofConv).comp d.groupIso.hom.hom.toAlgHom) := rfl
    rw [hf, hh, h₂, ← rationalPoint_compHopf, h₁ p.ofConv, scalarPresentedCoordinate]
    simp only [e, Iso.trans_hom, Iso.symm_hom, Grp.comp_hom_hom, Category.assoc]
    have he : b₁.hom.hom.hom ≫ b₁.inv.hom.hom = 𝟙 _ := congrArg (fun v => v.hom.hom) b₁.hom_inv_id
    rw [← Category.assoc b₁.hom.hom.hom, he, Category.id_comp]
    rfl
  have hN (g : 𝟙_ (SchemeOver k) ⟶ G.val.X) :
      Normalizes T.inclusion g ↔ Normalizes (F.map P.pair.T.inclusion) (f g) := by
    rw [hactual]
    exact normalizingComparison T P.pair.T e t ht g
  let R := CommAlgCat.of k k
  let r : K ⊗[k] k ≃ₐ[K] K := Algebra.TensorProduct.rid k K K
  obtain ⟨hDinj, hD⟩ := pinnedCoordinateFixedPoints d R
  have hL (p : WithConv (A₁ →ₐ[k] k)) : (L p).ofConv = r.toAlgHom.comp (pinnedCoordinatePoint d R p.ofConv) := rfl
  have hLi : Function.Injective L := by
    intro p q hpq
    apply ofConv_injective
    apply hDinj
    apply AlgHom.ext
    intro x
    apply r.injective
    have h := hL p
    rw [hpq, hL q] at h
    exact (DFunLike.congr_fun h x).symm
  have hfi : Function.Injective f := g₂.injective.comp (hLi.comp g₁.symm.injective)
  have hr (σ : Gal(K/k)) (y : K ⊗[k] k) :
      r ((SemilinearAction.scalarExtension (K := K) k).act σ y) = σ (r y) := by
    induction y using TensorProduct.inductionOn with
    | tmul a c =>
      change r (σ a ⊗ₜ[k] c) = σ (r (a ⊗ₜ[k] c))
      simp only [r, Algebra.TensorProduct.rid_tmul, Algebra.smul_def, map_mul, AlgEquiv.commutes]
    | add a b ha hb => simp only [map_add, ha, hb]
  refine ⟨b₁, b₂, extendedPresentation G, extendedPresentation P.pair.G,
    t, f, ht, hfi, hactual, hN, ?_⟩
  intro p
  let q := r.symm.toAlgHom.comp p
  have hq (z : extendedHopf K A₂) : r (q z) = p z := r.apply_symm_apply _
  have hx : g₂ (toConv p) = hopfFieldPoint p ≫ b₂.hom.hom.hom := by
    rw [h₂, hopfRationalPoint_eq]
  let x := hopfFieldPoint p ≫ b₂.hom.hom.hom
  change (Normalizes (F.map P.pair.T.inclusion) x ∧
    ∀ σ z, p (pinnedCoordinateAction d σ z) = σ (p z)) ↔ _
  constructor
  · rintro ⟨hn, hfix⟩
    have hqfix : ∀ (σ : Gal(K/k)) z, q (pinnedCoordinateAction d σ z) =
        (SemilinearAction.scalarExtension (K := K) R).act σ (q z) := by
      intro σ z
      apply r.injective
      change r (q (pinnedCoordinateAction d σ z)) = (r ∘ (SemilinearAction.scalarExtension (K := K) k).act σ) (q z)
      rw [Function.comp_apply, hq, hr, hq]
      exact hfix σ z
    obtain ⟨p₀, hp₀⟩ := (hD q).mpr hqfix
    have hL₀ : L (toConv p₀) = toConv p := by
      apply ofConv_injective
      rw [hL, hp₀]
      exact AlgHom.ext hq
    have h : f (g₁ (toConv p₀)) = x := (hf _).trans ((congrArg g₂ hL₀).trans hx)
    exact ⟨g₁ (toConv p₀), (hN _).mpr (h.symm ▸ hn), h⟩
  · rintro ⟨g, hg, h⟩
    change f g = x at h
    refine ⟨h ▸ (hN g).mp hg, ?_⟩
    obtain ⟨p₀, rfl⟩ := g₁.surjective g
    have hLp : L p₀ = toConv p := g₂.injective ((hf p₀).symm.trans (h.trans hx.symm))
    have hp₀ : pinnedCoordinatePoint d R p₀.ofConv = q := by
      apply AlgHom.ext
      intro z
      apply r.injective
      have he := DFunLike.congr_fun ((hL p₀).symm.trans (congrArg ofConv hLp)) z
      exact he.trans (hq z).symm
    have he := (hD q).mp ⟨p₀.ofConv, hp₀⟩
    intro σ z
    have h₀ := congrArg r (he σ z)
    change r (q (pinnedCoordinateAction d σ z)) = r ((SemilinearAction.scalarExtension (K := K) k).act σ (q z)) at h₀
    rw [hq, hr, hq] at h₀
    exact h₀

end FixedNormalizer

section PinnedWeylAction

open AlgebraicGeometry CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open Specs.Pinning (PinnedIso)
open private simple_reflections_generate from LinearAlgebraicGroups.Classification.NormalizerComparison

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 700000 in
theorem pinnedWeylFieldAction : PinnedWeylFieldAction.{u} := by
  classical
  intro k K _ _ _ D M F e s hpin
  letI := F.torusComm
  letI := D.finiteRoots
  letI := D.reduced
  let P := F.realization.pinned
  let C := F.identification
  let R := CommAlgCat.of k K
  let Y := (testSpec k).obj (Opposite.op R)
  let N := (Y ⟶ C.normalizer.group.X)
  obtain ⟨q, hq, hproj, hk, hc, hcoef⟩ := normalizerFieldLabels (K := K) F
  let i := IsMonHom.monoidHom C.normalizer.inclusion.hom.hom Y
  letI : IsClosedImmersion C.normalizer.inclusion.hom.hom.left := C.normalizer.isClosedImmersion
  letI : Mono C.normalizer.inclusion.hom.hom := Over.mono_of_mono_left _
  have hinj : Function.Injective i := fun _ _ h => (cancel_mono C.normalizer.inclusion.hom.hom).mp h
  have h₀ (a : PinnedIso P P) (n : N) :
      ∃ m : N, i m = i n ≫ a.group.hom.hom.hom := by
    apply (C.representsNormalizer _ _).mp
    exact normalizes_of_iso P.pair.T P.pair.T a.group a.torus a.torus_comm.symm
      ((C.representsNormalizer _ _).mpr ⟨n, rfl⟩)
  choose v hv using h₀
  let t (a : PinnedIso P P) : N →* N := MonoidHom.mk' (v a) (by
    intro x y
    apply hinj
    have h₁ := hv a (x * y)
    change i (v a (x * y)) =
      (IsMonHom.monoidHom a.group.hom.hom.hom Y) (i (x * y)) at h₁
    rw [h₁, map_mul, map_mul, map_mul, hv a x, hv a y]
    rfl)
  have ht (a : PinnedIso P P) (n : N) : i (t a n) = i n ≫ a.group.hom.hom.hom := hv a n
  have hi (a : PinnedIso P P) (n : N) : t a.symm (t a n) = n := by
    apply hinj
    rw [ht, ht, Category.assoc]
    have hed : a.group.hom.hom.hom ≫ a.symm.group.hom.hom.hom = 𝟙 _ :=
      congrArg (fun v => v.hom.hom) a.group.hom_inv_id
    rw [hed, Category.comp_id]
  let a : MulAut N :=
    { toFun := t s
      invFun := t s.symm
      left_inv := hi s
      right_inv := hi s.symm
      map_mul' := map_mul (t s) }
  have ha (n : N) : i (a n) = i n ≫ s.group.hom.hom.hom := ht s n
  have hat (n : N) (hn : q n = 1) : q (a n) = 1 := by
    obtain ⟨b, hb⟩ := (hk n).mp hn
    apply (hk _).mpr
    refine ⟨b ≫ s.torus.hom.hom.hom, hinj ?_⟩
    change ((b ≫ s.torus.hom.hom.hom) ≫ C.torusInclusion.hom.hom) ≫ C.normalizer.inclusion.hom.hom = i (a n)
    rw [ha, ← hb]
    change _ = ((b ≫ C.torusInclusion.hom.hom) ≫ C.normalizer.inclusion.hom.hom) ≫ s.group.hom.hom.hom
    simp only [Category.assoc, ← Grp.comp_hom_hom, C.inclusion_eq, s.torus_comm]
  choose r m hinc hm _ _ using F.simple
  let l (x : D.base.support) : N := toUnit Y ≫ m x
  have hl (x : D.base.support) : i (l x) = toUnit Y ≫ (r x).reflection.representative := by
    change (toUnit Y ≫ m x) ≫ C.normalizer.inclusion.hom.hom = _
    rw [Category.assoc, hinc]
  have hla (x : D.base.support) : a (l x) = l (simplePermutation D e x) := by
    apply hinj
    rw [ha, hl, hl, Category.assoc]
    exact congrArg (toUnit Y ≫ ·)
      (pinnedSimpleWordEquivariant F.realization.attached C s _ _ (hpin x) (r x) (r (simplePermutation D e x)))
  let W := D.datum.weylGroup
  let φ := W.subtype.comp q
  let ψ := (MulAut.conj e.val).toMonoidHom.comp φ
  let E := MonoidHom.eqLocus (φ.comp a.toMonoidHom) ψ
  have hE (n : N) : n ∈ E ↔ (q (a n)).val = e.val * (q n).val * e.val⁻¹ := Iff.rfl
  have hlE (x : D.base.support) : l x ∈ E := by
    apply (hE _).mpr
    rw [hla]
    change (q (toUnit Y ≫ m (simplePermutation D e x))).val = e.val * (q (toUnit Y ≫ m x)).val * e.val⁻¹
    rw [hc, hc, hm, hm]
    exact eq_mul_inv_of_mul_eq (reflection_natural D e.val x.val).symm
  have hEt (n : N) (hn : q n = 1) : n ∈ E := by
    apply (hE _).mpr
    rw [hn, hat n hn]
    change (1 : RootPairing.Aut D.datum) = e.val * 1 * e.val⁻¹
    simp
  let qE := q.comp E.subtype
  have hEtop : qE.range = ⊤ := by
    apply top_unique
    rw [← simple_reflections_generate D.datum D.base]
    apply (Subgroup.closure_le qE.range).mpr
    rintro _ ⟨x, rfl⟩
    refine ⟨⟨l x, hlE x⟩, ?_⟩
    exact (hc (m x)).trans (hm x)
  refine ⟨q, a, hq, hproj, hk, hc, hcoef, ha, fun n => ?_⟩
  obtain ⟨m, he⟩ := MonoidHom.range_eq_top.mp hEtop (q n)
  have hquot : q (n * m.val⁻¹) = 1 := by
    have h : q m.val = q n := he
    rw [map_mul, map_inv, h, mul_inv_cancel]
  have hmem : n ∈ E := by
    simpa only [inv_mul_cancel_right] using E.mul_mem (hEt (n * m.val⁻¹) hquot) m.property
  have h := congrArg (· * e.val) ((hE n).mp hmem).symm
  simpa only [inv_mul_cancel_right] using h

open Specs.IntegralSemisimpleModel (Integers IntegralPoints TorusValues integerAlgebra integralPointFunctor forgetFibrePoint torusPoint)
open private fibrePointsEquiv from LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
attribute [local instance] integerAlgebra

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 850000 in
theorem foldedIntegralNormalizerLifts : FoldedIntegralNormalizerLifts.{u} := by
  classical
  intro k K l _ _ _ _ D M F E e s σ hpin hinv hsym horth R f g
  letI := F.torusComm
  letI := E.torusComm
  let C := F.identification
  let P := F.realization.pinned
  let S := CommAlgCat.of k K
  let Y := (testSpec k).obj (Opposite.op S)
  let N := (Y ⟶ C.normalizer.group.X)
  let W := fixedWeylGroup D e
  let p := simplePermutation D e
  obtain ⟨q, a, _, hproj, hk, hconst, hcoeff, ha, hact⟩ := pinnedWeylFieldAction (K := K) F e s hpin
  let c := fieldCoefficientAction σ C.normalizer.group
  let B := MonoidHom.eqLocus a.toMonoidHom c
  have hW (w : D.datum.weylGroup) : w ∈ W ↔ Commute e.val w.val := by
    change w.val ∈ Subgroup.centralizer {e.val} ↔ e.val * w.val = w.val * e.val
    exact Subgroup.mem_centralizer_singleton_iff.trans eq_comm
  have hqW (x : B) : q x.val ∈ W := by
    apply (hW _).mpr
    have h : a x.val = c x.val := x.property
    have h' : q (c x.val) = q x.val := hcoeff (CommAlgCat.ofHom σ.toAlgHom) x.val
    have hw := hact x.val
    rwa [h, h'] at hw
  let q₀ := (q.comp B.subtype).codRestrict W hqW
  have hker (n : B) : q₀ n = 1 ↔ ∃ t : Y ⟶ P.pair.T.group.X,
      t ≫ C.torusInclusion.hom.hom = n.val := by
    have h : q₀ n = 1 ↔ q n.val = 1 := Subtype.ext_iff
    exact h.trans (hk n.val)
  let i := IsMonHom.monoidHom C.normalizer.inclusion.hom.hom Y
  let j : N →* IntegralPoints M.group (CommAlgCat.of Integers.{u} K) :=
    (fibrePointsEquiv M.group S).toMonoidHom.comp
      ((IsMonHom.monoidHom F.fibreIso.inv.hom.hom Y).comp i)
  have hj (n : N) : j n = forgetFibrePoint M.group S
      (n ≫ C.normalizer.inclusion.hom.hom ≫ F.fibreIso.inv.hom.hom) := by
    change forgetFibrePoint M.group S ((n ≫ C.normalizer.inclusion.hom.hom) ≫ F.fibreIso.inv.hom.hom) = _
    rw [Category.assoc]
  letI : IsClosedImmersion C.normalizer.inclusion.hom.hom.left := C.normalizer.isClosedImmersion
  letI : Mono C.normalizer.inclusion.hom.hom := Over.mono_of_mono_left _
  have hi : Function.Injective i := fun _ _ h => (cancel_mono C.normalizer.inclusion.hom.hom).mp h
  choose r nx hnx hlabel _ hword using F.simple
  choose _ mx _ hres hrespt _ using E.simple
  let x (b : D.base.support) : N := toUnit Y ≫ nx b
  let z (b : D.base.support) := markedWeylWord M.toIntegralMarking b.val R 1
  let d := F.realization.datumIso.val
  have hd (b c : D.I) : F.realization.attached.datum.rootDatum.pairing (d.indexEquiv b) (d.indexEquiv c) =
      D.datum.pairing b c := d.toHom.pairing
  have hsym' (b c : Specs.AbstractPairing.Root P.pair.T) :
      F.realization.attached.datum.rootDatum.pairing b c = F.realization.attached.datum.rootDatum.pairing c b := by
    obtain ⟨b, rfl⟩ := d.indexEquiv.surjective b
    obtain ⟨c, rfl⟩ := d.indexEquiv.surjective c
    rw [hd, hd, hsym]
  have hx (b : D.base.support) : i (x b) = toUnit Y ≫ (r b).reflection.representative := by
    change (toUnit Y ≫ nx b) ≫ C.normalizer.inclusion.hom.hom = _
    rw [Category.assoc, hnx]
  have hax (b : D.base.support) : a (x b) = x (p b) := by
    apply hi
    have h : i (a (x b)) = i (x b) ≫ s.group.hom.hom.hom := ha (x b)
    rw [h, hx, hx, Category.assoc]
    exact congrArg (toUnit Y ≫ ·) (pinnedSimpleWordEquivariant F.realization.attached C s _ _ (hpin b) (r b) (r (p b)))
  have hcx (b : D.base.support) : c (x b) = x b := by
    change (testSpec k).map (CommAlgCat.ofHom σ.toAlgHom).op ≫ toUnit Y ≫ nx b = _
    rw [← Category.assoc, comp_toUnit]
  have hxx (b : D.base.support) (hb : p b ≠ b) : Commute (x b) (x (p b)) := by
    have hp : F.realization.attached.datum.rootDatum.pairing
        (F.realization.simpleRoot b).val (F.realization.simpleRoot (p b)).val = 0 :=
      (hd b.val (p b).val).trans ((hsym _ _).trans (horth b hb))
    have hc := orthogonalSimpleWords F.realization.attached hsym' _ _ hp (r b) (r (p b))
    change x b * x (p b) = x (p b) * x b
    apply hi
    rw [map_mul, map_mul, hx, hx]
    simpa only [MonObj.comp_mul] using congrArg (toUnit Y ≫ ·) hc.eq
  have hpp (b : D.base.support) : p (p b) = b := Subtype.ext (hinv b.val)
  let u := ((integralPointFunctor M.group).map f).hom
  let v := ((integralPointFunctor M.group).map g).hom
  have hu (b : D.base.support) : u (z b) = j (x b) := by
    rw [hj]
    change u (z b) = forgetFibrePoint M.group S
      ((toUnit Y ≫ nx b) ≫ C.normalizer.inclusion.hom.hom ≫ F.fibreIso.inv.hom.hom)
    rw [Category.assoc, hword b S]
    simpa only [z, map_one] using (integralWeylWordConjugation M.toIntegralMarking b.val).1 f 1
  have hv (b : D.base.support) : v (z b) = E.point (mx b) := by
    rw [hrespt]
    simpa only [z, map_one] using (integralWeylWordConjugation M.toIntegralMarking b.val).1 g 1
  have hlabel' (b : D.base.support) : q (x b) = RootPairing.weylGroup.ofIdx D.datum b.val :=
    (hconst (nx b)).trans (hlabel b)
  have hgen (b : D.base.support) : ∃ (n : B)
      (m : 𝟙_ (SchemeOver l) ⟶ E.identification.normalizer.group.X) (t : IntegralPoints M.group R),
      q n.val = orbitWeylReflection D e b ∧ E.label m = orbitWeylReflection D e b ∧
      u t = j n.val ∧ v t = E.point m := by
    by_cases hb : p b = b
    · have hb' : x b ∈ B := by
        change a (x b) = c (x b)
        rw [hax, hcx, hb]
      refine ⟨⟨x b, hb'⟩, mx b, z b, ?_, ?_, hu b, hv b⟩
      · change q (x b) = orbitWeylReflection D e b
        rw [orbitWeylReflection, ite_eq_left hb, hlabel']
      · rw [orbitWeylReflection, ite_eq_left hb, hres]
    · have hb' : x b * x (p b) ∈ B := by
        change a (x b * x (p b)) = c (x b * x (p b))
        rw [map_mul, map_mul, hax, hax, hpp, hcx, hcx]
        exact (hxx b hb).eq.symm
      refine ⟨⟨x b * x (p b), hb'⟩, mx b * mx (p b), z b * z (p b), ?_, ?_, ?_, ?_⟩
      · change q (x b * x (p b)) = orbitWeylReflection D e b
        rw [orbitWeylReflection, ite_eq_right hb, map_mul, hlabel', hlabel']
      · rw [orbitWeylReflection, ite_eq_right hb, map_mul, hres, hres]
      · change u (z b * z (p b)) = j (x b * x (p b))
        rw [map_mul, map_mul, hu, hu]
      · rw [map_mul, map_mul, hv, hv]
  refine ⟨q, a, hproj, hk, ha, q₀, fun _ => rfl, hker, fun w => ?_⟩
  have hw := (fixedWeylGeneration D e hinv horth).1 w.val
  obtain ⟨n, m, z, hn, hm, hf, hg⟩ := simultaneousIntegralLifts (q.comp B.subtype) E.label
    (j.comp B.subtype) E.point u v (orbitWeylReflection D e) hgen w.val (hw.mpr ((hW _).mp w.property))
  exact ⟨n, m, z, Subtype.ext hn, hm, hf.trans (hj n.val), hg⟩

open scoped SemidirectProduct TensorProduct

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
theorem foldedApartmentAction : FoldedApartmentAction.{u} := by
  classical
  intro k K _ _ _ _ _ _ D M F e s σ b hb hσ hinv hsym hord hpin hchar hval
  letI := F.torusComm
  let C := F.identification
  let R := CommAlgCat.of k K
  let S := CommAlgCat.of Integers.{u} K
  let Y := (testSpec k).obj (Opposite.op R)
  let N := (Y ⟶ C.normalizer.group.X)
  let O := CommAlgCat.of Integers.{u} (valuation K).valuationSubring
  let f := valuationRingInclusion K
  let W := fixedWeylGroup D e
  let V := invariantApartment D e
  let τ := simplePermutation D e
  obtain ⟨E⟩ := markedFibreNormalizer K M
  letI := E.torusComm
  obtain ⟨q, a, hp, hk, ha, q₀, hq, _, hlift⟩ :=
    foldedIntegralNormalizerLifts F E e s σ hpin hinv hsym hord O f f
  let B := MonoidHom.eqLocus a.toMonoidHom (fieldCoefficientAction σ C.normalizer.group)
  obtain ⟨T, hT, hconj, hfix⟩ := fixedNormalizerTorusCoordinates F b s τ σ hσ hchar q a hp hk ha
  obtain ⟨νK, _, hχ, hνker⟩ := splitTorusTranslation K D b
  let i := IsMonHom.monoidHom C.normalizer.inclusion.hom.hom Y
  let jN : N →* IntegralPoints M.group S := (fibrePointsEquiv M.group R).toMonoidHom.comp
    ((IsMonHom.monoidHom F.fibreIso.inv.hom.hom Y).comp i)
  let j := jN.comp B.subtype
  have hj (n : B) : j n = forgetFibrePoint M.group R
      (n.val ≫ C.normalizer.inclusion.hom.hom ≫ F.fibreIso.inv.hom.hom) := by
    change forgetFibrePoint M.group R ((n.val ≫ C.normalizer.inclusion.hom.hom) ≫ F.fibreIso.inv.hom.hom) = _
    rw [Category.assoc]
  let iT : q₀.ker →* q.ker := (B.subtype.comp q₀.ker.subtype).codRestrict q.ker (fun t => by
    change q t.val.val = 1
    rw [← hq t.val, show q₀ t.val = 1 from t.property]
    rfl)
  let vT : q₀.ker →* TorusValues D S := MonoidHom.mk' (fun t => T.symm (iT t)) (by
    intro x y
    simp only [map_mul])
  let ν := νK.comp vT
  have ht (t : q₀.ker) : T (vT t) = iT t := T.apply_symm_apply _
  have htj (t : q₀.ker) : j t.val = torusPoint D S (vT t) ≫ M.torus.hom.hom := by
    rw [hj]
    have h := hT (vT t)
    rw [ht] at h
    exact h
  let J := (((integralPointFunctor M.group).map f).hom.range).comap j
  let Λ := ν.range
  let ν₀ := ν.rangeRestrict
  have hJ (t : q₀.ker) : ν₀ t = 1 ↔ t.val ∈ J := by
    have h : ν₀ t = 1 ↔ νK (vT t) = 1 := Subtype.ext_iff
    rw [h, hνker]
    change _ ↔ ∃ p : IntegralPoints M.group O, (integralPointFunctor M.group).map f p = j t.val
    rw [htj]
    exact markedIntegralTorusKernel D M.toIntegralMarking b (vT t)
  have hJsurj : Function.Surjective (q₀.comp J.subtype) := by
    intro w
    obtain ⟨n, _, p, hn, _, h, _⟩ := hlift w
    exact ⟨⟨n, ⟨p, h.trans (hj n).symm⟩⟩, hn⟩
  have hfixed_mem (t : q₀.ker) : (T (vT t)).val ∈ B := by
    rw [ht]
    exact t.val.property
  have hfixed_surj (v : TorusValues D S) (hv : (T v).val ∈ B) :
      ∃ t : q₀.ker, vT t = v := by
    let n : B := ⟨(T v).val, hv⟩
    let t : q₀.ker := ⟨n, Subtype.ext ((hq n).trans (T v).property)⟩
    refine ⟨t, T.injective ?_⟩
    rw [ht]
    rfl
  have hrange [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (hbase : ∀ x : k, normalizedValuation K (algebraMap k K x) = (normalizedValuation k x) ^ 2)
      (hbaseUnits : ∀ u : Kˣ, σ (u : K) = (u : K) → ∃ a : kˣ, algebraMap k K (a : k) = (u : K)) :
      Set.range (fun t : q₀.ker => fun i : D.base.support => ((b.repr (ν t).toAdd i : ℤ) : ℚ) / 2) =
        Set.range (orbitProjection τ) := by
    let U := {u : D.base.support → Kˣ // ∀ i, (u (τ i) : K) = σ (u i : K)}
    obtain ⟨c, hc, _⟩ := torusBasisCoordinates D b S
    have hcoord : ∀ v, (T v).val ∈ B ↔ ∀ i, (c v (τ i) : K) = σ (c v i : K) := by
      intro v
      simp only [hc]
      exact hfix v
    have hrepr (t : q₀.ker) (i : D.base.support) :
        b.repr (ν t).toAdd i = log (normalizedValuation K (c (vT t) i : K)) := by
      rw [cocharacterBasis_repr, hc]
      exact hχ (vT t) (characterBasis D b i)
    calc
      _ = Set.range (fun u : U => fun i => ((log (normalizedValuation K (u.val i : K)) : ℤ) : ℚ) / 2) := by
        ext x
        constructor
        · rintro ⟨t, rfl⟩
          exact ⟨⟨c (vT t), (hcoord _).mp (hfixed_mem t)⟩, funext fun i =>
            congrArg (fun z : ℤ => (z : ℚ) / 2) (hrepr t i).symm⟩
        · rintro ⟨u, rfl⟩
          obtain ⟨v, hv⟩ := c.surjective u.val
          obtain ⟨t, ht'⟩ := hfixed_surj v ((hcoord v).mpr (hv.symm ▸ u.property))
          refine ⟨t, funext fun i => ?_⟩
          change ((b.repr (ν t).toAdd i : ℤ) : ℚ) / 2 =
            ((log (normalizedValuation K (u.val i : K)) : ℤ) : ℚ) / 2
          rw [hrepr t i, ht', hv]
      _ = _ := foldedTranslationLattice σ hσ hbase hval hbaseUnits τ
        (fun i => Subtype.ext (hinv i.val))
  let wInt := (cocharacterLinearAction D).comp (D.datum.weylGroup.subtype.comp W.subtype)
  have hcov (n : B) (t : q₀.ker) : (ν (conjugateTorus q₀ n t)).toAdd = wInt (q₀ n) (ν t).toAdd := by
    have hc : vT (conjugateTorus q₀ n t) = (vT t).comp
        (q n.val).val.weightEquiv.symm.toLinearMap.toAddMonoidHom.toMultiplicative := by
      apply T.injective
      rw [ht, ← hconj, ht]
      exact Subtype.ext rfl
    change (νK (vT (conjugateTorus q₀ n t))).toAdd = (q₀ n).val.val.coweightEquiv.symm (νK (vT t)).toAdd
    rw [hc, hq]
    exact (splitTranslationAction D νK hχ).2 (q n.val).val (vT t)
  have hf (t : q₀.ker) : e.val.coweightEquiv.symm (ν t).toAdd = (ν t).toAdd := by
    have hu := (hfix (vT t)).mp (hfixed_mem t)
    apply b.repr.injective
    ext i
    obtain ⟨i, rfl⟩ := τ.surjective i
    rw [cocharacterBasis_repr, cocharacterBasis_repr, ← ((basedPermutation D e b hb) i).2,
      e.val.toLinearMap_weightEquiv, LinearEquiv.apply_symm_apply]
    change D.datum.toLinearMap (characterBasis D b i) (νK (vT t)).toAdd =
      D.datum.toLinearMap (e.val.weightEquiv (characterBasis D b i)) (νK (vT t)).toAdd
    rw [((basedPermutation D e b hb) i).2, hχ, hχ, hu i, hval]
  let Aint (w : W) : MulAut (Multiplicative D.Y) := (wInt w).toAddEquiv.toMultiplicative
  have hΛ (w : W) (x : Multiplicative D.Y) (hx : x ∈ Λ) : Aint w x ∈ Λ := by
    obtain ⟨t, rfl⟩ := hx
    obtain ⟨n, hn⟩ := hJsurj w
    refine ⟨conjugateTorus q₀ n.val t, ?_⟩
    apply Multiplicative.toAdd.injective
    have h : q₀ n.val = w := hn
    change (ν (conjugateTorus q₀ n.val t)).toAdd = wInt w (ν t).toAdd
    exact (hcov n.val t).trans (congrArg (fun u => wInt u (ν t).toAdd) h)
  have heq (w : W) : Λ.map (Aint w).toMonoidHom = Λ := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hΛ w x hx
    · intro x hx
      refine ⟨Aint w⁻¹ x, hΛ _ _ hx, ?_⟩
      apply Multiplicative.toAdd.injective
      change wInt w (wInt w⁻¹ x.toAdd) = x.toAdd
      rw [map_inv]
      exact (wInt w).apply_symm_apply _
  let act (w : W) : MulAut Λ := ((Aint w).subgroupMap Λ).trans (MulEquiv.subgroupCongr (heq w))
  let ρ : W →* MulAut Λ :=
    { toFun := act
      map_one' := by
        apply MulEquiv.ext
        intro x
        apply Subtype.ext
        apply Multiplicative.toAdd.injective
        change wInt 1 x.val.toAdd = x.val.toAdd
        rw [map_one]
        rfl
      map_mul' x y := by
        apply MulEquiv.ext
        intro z
        apply Subtype.ext
        apply Multiplicative.toAdd.injective
        change wInt (x * y) z.val.toAdd = wInt x (wInt y z.val.toAdd)
        rw [map_mul]
        rfl }
  obtain ⟨w, hwi, hw⟩ := foldedWeylLinearAction D e b hinv hord
  let fL := TensorProduct.mk ℤ ℚ D.Y (1 / 2)
  have hV (x : Λ) : fL x.val.toAdd ∈ V := by
    obtain ⟨t, ht⟩ := x.property
    have h : (e.val.coweightEquiv.symm.baseChange ℤ ℚ D.Y D.Y) (fL x.val.toAdd) = fL x.val.toAdd := by
      change (1 / 2 : ℚ) ⊗ₜ[ℤ] e.val.coweightEquiv.symm x.val.toAdd = (1 / 2 : ℚ) ⊗ₜ[ℤ] x.val.toAdd
      rw [← ht, hf]
    apply LinearMap.mem_ker.mpr
    change (e.val.coweightEquiv.symm.baseChange ℤ ℚ D.Y D.Y) (fL x.val.toAdd) - fL x.val.toAdd = 0
    rw [h, sub_self]
  let jL : Λ →* Multiplicative V :=
    { toFun := fun x => Multiplicative.ofAdd ⟨fL x.val.toAdd, hV x⟩
      map_one' := by
        apply Multiplicative.toAdd.injective
        exact Subtype.ext fL.map_zero
      map_mul' x y := by
        apply Multiplicative.toAdd.injective
        exact Subtype.ext (fL.map_add x.val.toAdd y.val.toAdd) }
  have hji : Function.Injective jL := by
    intro x y h
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    apply b.repr.injective
    ext i
    have h' := congrArg (fun z : Multiplicative V =>
      (TensorProduct.equivFinsuppOfBasisRight b z.toAdd.val : D.base.support →₀ ℚ) i) h
    change (TensorProduct.equivFinsuppOfBasisRight b ((1 / 2 : ℚ) ⊗ₜ[ℤ] x.val.toAdd)) i =
      (TensorProduct.equivFinsuppOfBasisRight b ((1 / 2 : ℚ) ⊗ₜ[ℤ] y.val.toAdd)) i at h'
    simp only [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply, zsmul_eq_mul] at h'
    exact_mod_cast mul_right_cancel₀ (by norm_num : (1 / 2 : ℚ) ≠ 0) h'
  have hρ (w₀ : W) (x : Λ) : (jL (ρ w₀ x)).toAdd = w w₀ (jL x).toAdd := by
    apply Subtype.ext
    rw [hw]
    rfl
  have hsv : Function.Surjective ν₀ := fun x => ⟨x.property.choose, Subtype.ext x.property.choose_spec⟩
  have hν (n : B) (t : q₀.ker) : ν₀ (conjugateTorus q₀ n t) = ρ (q₀ n) (ν₀ t) := by
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    exact hcov n t
  obtain ⟨p, hps, hpk, hai, hr, ht₀, _, hl, hscale⟩ := normalizerApartment q₀ J ν₀ ρ jL w hρ
    hji hwi hsv hJsurj hJ hν
  let A := affineTransformation ρ jL w hρ
  let α := A.comp p
  have hak : α.ker = p.ker := by
    ext n
    change A (p n) = 1 ↔ p n = 1
    rw [← map_one A, hai.eq_iff]
  refine ⟨q, a, hp, hk, ha, q₀, ν, j, hq, hj, fun t => ⟨vT t, htj t, hχ _⟩,
    hrange, hJsurj, ρ, p, α, hps, hpk, hak, hr, fun t => congrArg Subtype.val (ht₀ t), ?_,
    fun n m hm he => congrArg Subtype.val (hl n m hm he), ?_⟩
  · intro n x
    change ((w (p n).right (x - 0)) + (jL (p n).left).toAdd).val = _
    rw [sub_zero, hr]
    change (w (q₀ n) x).val + (jL (p n).left).toAdd.val = _
    rw [hw]
    rfl
  · intro n x c d hc hd
    exact hscale n x c d (Subtype.ext hc) (Subtype.ext hd)

end PinnedWeylAction

section QuadraticFactors

private theorem quadraticAut_cases {F L : Type u} [Field F] [Field L] [Algebra F L]
    [FiniteDimensional F L] [IsGalois F L] (hdegree : Module.finrank F L = 2)
    (σ : Gal(L/F)) (hσ : σ ≠ 1) (g : Gal(L/F)) : g = 1 ∨ g = σ := by
  have hcard : Nat.card Gal(L/F) = 2 :=
    (IsGalois.card_aut_eq_finrank F L).trans hdegree
  by_cases hg : g = 1
  · exact Or.inl hg
  · exact Or.inr (ExistsUnique.unique ((Nat.card_eq_two_iff' (1 : Gal(L/F))).mp hcard) hg hσ)

theorem quadraticStabilizerFields : QuadraticStabilizerFields.{u} := by
  intro F L _ _ _ _ _ hdegree σ hσ
  have hcases := quadraticAut_cases hdegree σ hσ
  constructor
  · intro u hu
    have hf : ∀ g : Gal(L/F), g (u : L) = (u : L) := by
      intro g
      rcases hcases g with rfl | rfl
      · rfl
      · exact hu
    obtain ⟨a, ha⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (u : L)).mpr hf
    have ha₀ : a ≠ 0 := by
      intro e
      rw [e, map_zero] at ha
      exact u.ne_zero ha.symm
    exact ⟨Units.mk0 a ha₀, ha⟩
  · intro ι r i
    letI := MulAction.compHom ι r
    constructor
    · intro hi
      suffices he : MulAction.stabilizer Gal(L/F) i = ⊤ by
        rw [he, IsGalois.fixedField_top]
      apply top_unique
      intro g _
      change r g i = i
      rcases hcases g with rfl | rfl
      · simp
      · exact hi
    · intro hi
      suffices he : MulAction.stabilizer Gal(L/F) i = ⊥ by
        rw [he, IntermediateField.fixedField_bot]
      apply bot_unique
      intro g hg
      change r g i = i at hg
      rcases hcases g with rfl | rfl
      · exact Subgroup.one_mem _
      · exact (hi hg).elim

open Specs.AdjointCocharacters renaming coordinateHopf → affineCoordinateHopf
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false in
theorem descendedTorusTranslations : DescendedTorusTranslations.{u} := by
  intro F L _ _ _ _ _ _ _ _ _ _ _ hdegree σ hσ hFL hv ι _ r H c C hC
  obtain ⟨e, he⟩ := rationalPermutationTorusPoints c hC
  have hcases := quadraticAut_cases hdegree σ hσ
  have hσ₂ : σ * σ = 1 := (hcases (σ * σ)).resolve_right fun h ↦
    hσ (mul_right_cancel (h.trans (one_mul σ).symm))
  have hinv : Function.Involutive σ := fun z ↦ DFunLike.congr_fun hσ₂ z
  have hr : r σ * r σ = 1 := (map_mul r _ _).symm.trans ((congrArg r hσ₂).trans (map_one r))
  have hτ : Function.Involutive (r σ) := fun i ↦ Equiv.congr_fun hr i
  let V := {v : ι → Lˣ // ∀ i, (v (r σ i) : L) = σ (v i : L)}
  let ν (v : V) (i : ι) := ((log (normalizedValuation L (v.val i : L)) : ℤ) : ℚ) / 2
  have hV : Set.range (fun f : C →ₐ[F] F ↦ fun i ↦
      ((log (normalizedValuation L (Algebra.TensorProduct.rid F L L
        (Algebra.TensorProduct.map (AlgHom.id L L) f (c.basis i).toMul.val))) : ℤ) : ℚ) / 2) =
      Set.range ν := by
    ext y
    constructor
    · rintro ⟨f, rfl⟩
      refine ⟨⟨(e f).val, (e f).property σ⟩, funext fun i ↦ ?_⟩
      dsimp only [ν]
      rw [he]
    · rintro ⟨v, rfl⟩
      have h (g : Gal(L/F)) (i : ι) : (v.val (r g i) : L) = g (v.val i : L) := by
        rcases hcases g with rfl | rfl
        · simp
        · exact v.property i
      obtain ⟨f, hf⟩ := e.surjective ⟨v.val, h⟩
      refine ⟨f, funext fun i ↦ ?_⟩
      exact (congrArg (fun a : L ↦ ((log (normalizedValuation L a) : ℤ) : ℚ) / 2)
        (he f i)).symm.trans (congrArg (fun u : {v : ι → Lˣ // ∀ (g : Gal(L/F)) i,
        (v (r g i) : L) = g (v i : L)} ↦
        ((log (normalizedValuation L (u.val i : L)) : ℤ) : ℚ) / 2) hf)
  rw [hV]
  exact foldedTranslationLattice σ hinv hFL hv (quadraticStabilizerFields hdegree σ hσ).1 (r σ) hτ

end QuadraticFactors

section RationalFixedPoints

open AlgebraicGeometry CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct
open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup GroupScheme ClosedSubgroup)
open Specs.AdjointCocharacters (coordinateHopfIso coordinateHopfMap)
open Specs.AdjointCocharacters renaming coordinateHopf → affineCoordinates
open Specs.Pinning (AttachedDatum PinnedGroup)
open Specs.RootGroups (AdditiveLine)
open Specs.AdjointBorelCohomology (PinnedTwist)
open Specs.AutomorphismSequence (forgetPinning)
open _root_.LinearAlgebraicGroups.Descent (SemilinearAction)
open private groundIso from LinearAlgebraicGroups.Solvable.TorusSections
open private factor_of_baseChange from LinearAlgebraicGroups.Affine.ClosedSubgroups
open private coordinatePresentationMap from LinearAlgebraicGroups.Descent.AdjointCocharacters

set_option maxHeartbeats 520000

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- An extension-field point of the scalar extension, viewed as a test-algebra point. -/
private def extensionPointEquiv (G : GroupScheme k) :
    (𝟙_ (SchemeOver K) ⟶ ((groupBaseChange k K).obj G).X) ≃*
      Points G.X (CommAlgCat.of k K) := by
  let h := (groundIso (k := K)).hom
  let X := ((groupBaseChange k K).obj G).X
  let j : (𝟙_ (SchemeOver K) ⟶ X) →* Points X (CommAlgCat.of K K) :=
    MonoidHom.mk' (h ≫ ·) (MonObj.comp_mul h)
  letI : IsIso h := (groundIso (k := K)).isIso_hom
  let e : (𝟙_ (SchemeOver K) ⟶ X) ≃* Points X (CommAlgCat.of K K) :=
    MulEquiv.ofBijective j ⟨fun _ _ he => (cancel_epi h).mp he, fun p =>
      ⟨(groundIso (k := K)).inv ≫ p, (groundIso (k := K)).hom_inv_id_assoc p⟩⟩
  exact e.trans (baseChangePointGroupEquiv K G (CommAlgCat.of K K))

set_option backward.isDefEq.respectTransparency false in
private theorem extensionPointEquiv_natural {G H : GroupScheme k} (f : G ⟶ H)
    (x : 𝟙_ (SchemeOver K) ⟶ ((groupBaseChange k K).obj G).X) :
    extensionPointEquiv H (x ≫ ((groupBaseChange k K).map f).hom.hom) =
      extensionPointEquiv G x ≫ f.hom.hom := by
  change baseChangePoint k K H.X (CommAlgCat.of K K)
    ((groundIso (k := K)).hom ≫ x ≫ ((groupBaseChange k K).map f).hom.hom) =
    baseChangePoint k K G.X (CommAlgCat.of K K) ((groundIso (k := K)).hom ≫ x) ≫ f.hom.hom
  rw [← Category.assoc]
  exact baseChangePointsSchemeNaturality k K f.hom.hom (CommAlgCat.of K K) _

set_option backward.isDefEq.respectTransparency false in
private theorem extensionPoint_normalizes {G : GroupScheme k} (T N : ClosedSubgroup G)
    (hN : RepresentsSubgroup N (fun _ g ↦ Normalizes T.inclusion g))
    (x : 𝟙_ (SchemeOver K) ⟶ ((groupBaseChange k K).obj G).X) :
    Normalizes ((groupBaseChange k K).map T.inclusion) x ↔
      ∃ n : Points N.group.X (CommAlgCat.of k K),
        n ≫ N.inclusion.hom.hom = extensionPointEquiv G x := by
  obtain ⟨h, hb⟩ := normalizerSchemeBaseChange k K T.inclusion N T.isClosedImmersion hN
  have hb' : Normalizes ((groupBaseChange k K).map T.inclusion) x ↔
      ∃ z : 𝟙_ (SchemeOver K) ⟶ ((groupBaseChange k K).obj N.group).X,
        z ≫ ((groupBaseChange k K).map N.inclusion).hom.hom = x := hb _ x
  rw [hb']
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨extensionPointEquiv N.group z,
      (extensionPointEquiv_natural N.inclusion z).symm.trans (congrArg (extensionPointEquiv G) hz)⟩
  · rintro ⟨z, hz⟩
    obtain ⟨w, rfl⟩ := (extensionPointEquiv (K := K) N.group).surjective z
    exact ⟨w, (extensionPointEquiv G).injective ((extensionPointEquiv_natural N.inclusion w).trans hz)⟩

private def evaluateSplitPoint (G : AffineAlgebraicGroup k)
    (h : extendedHopf K (affineCoordinates G) →ₐ[K] K) :
    Points G.val.X (CommAlgCat.of k K) :=
  let f := (AlgHom.liftEquiv k K (affineCoordinates G) K).symm h
  (testSpec k).map (CommAlgCat.ofHom f).op ≫ (coordinateHopfIso G).hom.hom.hom

set_option backward.isDefEq.respectTransparency false in
private theorem extensionPoint_coordinates (G : AffineAlgebraicGroup k)
    (b : specGroup (extendedHopf K (affineCoordinates G)) ≅ (groupBaseChange k K).obj G.val)
    (hb : ExtendsCoordinatePresentation G b) (h : extendedHopf K (affineCoordinates G) →ₐ[K] K) :
    extensionPointEquiv G.val (hopfFieldPoint h ≫ b.hom.hom.hom) = evaluateSplitPoint G h := by
  apply Over.OverMorphism.ext
  let i : affineCoordinates G →ₐ[k] K ⊗[k] affineCoordinates G := Algebra.TensorProduct.includeRight
  change ((𝟙 (Spec (CommRingCat.of K)) ≫
    (Spec.map (CommRingCat.ofHom h.toRingHom) ≫ b.hom.hom.hom.left)) ≫
      pullback.fst G.val.X.hom (fieldSpecMap k K)) =
    Spec.map (CommRingCat.ofHom (((h.restrictScalars k).comp i).toRingHom)) ≫
      (coordinateHopfIso G).hom.hom.hom.left
  have hb' := hb
  change b.hom.hom.hom.left ≫ pullback.fst G.val.X.hom (fieldSpecMap k K) =
    Spec.map (CommRingCat.ofHom i.toRingHom) ≫ (coordinateHopfIso G).hom.hom.hom.left at hb'
  rw [Category.id_comp, Category.assoc, hb', ← Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
private theorem evaluateSplitPoint_fixed {A : AdditiveLine k} {P : PinnedGroup A}
    {D : AttachedDatum P.pair} {l : Aut D.toBased ≃* Aut P}
    {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}
    (d : PinnedTwist K D l B T) (σ : Gal(K/k))
    (h : extendedHopf K (affineCoordinates P.pair.G) →ₐ[K] K) :
    let a := (Functor.mapAut P (forgetPinning (A := A)) (l (d.outer σ))).asIso
    let p := evaluateSplitPoint P.pair.G h
    (∀ z, h (pinnedCoordinateAction d σ z) = σ (h z)) ↔
      p ≫ a.inv.hom.hom = (testSpec k).map (CommAlgCat.ofHom σ.toAlgHom).op ≫ p := by
  let H := P.pair.G
  let B₀ := affineCoordinates H
  let a : H.val ≅ H.val := (Functor.mapAut P (forgetPinning (A := A)) (l (d.outer σ))).asIso
  let c := coordinateHopfMap (G := H) (H := H) a.inv
  let f := (AlgHom.liftEquiv k K B₀ K).symm h
  let i := (coordinateHopfIso H).hom.hom.hom
  let p := evaluateSplitPoint H h
  have hi : (specGroupMap c).hom.hom ≫ i = i ≫ a.inv.hom.hom := by
    have he : specGroupMap c ≫ (coordinateHopfIso H).hom = (coordinateHopfIso H).hom ≫ a.inv := by
      dsimp only [c]
      rw [coordinatePresentationMap, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact congrArg (fun m => m.hom.hom) he
  have hc : p ≫ a.inv.hom.hom =
      (testSpec k).map (CommAlgCat.ofHom (f.comp c.hom.toAlgHom)).op ≫ i := by
    change (((testSpec k).map (CommAlgCat.ofHom f).op ≫ i) ≫ a.inv.hom.hom) = _
    rw [Category.assoc, ← hi, ← Category.assoc]
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom f.toRingHom) ≫ Spec.map (CommRingCat.ofHom c.hom.toAlgHom.toRingHom) ≫ _ = _
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have hσ : (testSpec k).map (CommAlgCat.ofHom σ.toAlgHom).op ≫ p =
      (testSpec k).map (CommAlgCat.ofHom (σ.toAlgHom.comp f)).op ≫ i := by
    change (testSpec k).map (CommAlgCat.ofHom σ.toAlgHom).op ≫
      (testSpec k).map (CommAlgCat.ofHom f).op ≫ i = _
    rw [← Category.assoc, ← Functor.map_comp]
    rfl
  change (∀ z, h (pinnedCoordinateAction d σ z) = σ (h z)) ↔
    p ≫ a.inv.hom.hom = (testSpec k).map (CommAlgCat.ofHom σ.toAlgHom).op ≫ p
  haveI : IsIso i := ((Grp.forget (SchemeOver k)).mapIso (coordinateHopfIso H)).isIso_hom
  rw [hc, hσ, cancel_mono]
  have hf : (testSpec k).map (CommAlgCat.ofHom (f.comp c.hom.toAlgHom)).op =
      (testSpec k).map (CommAlgCat.ofHom (σ.toAlgHom.comp f)).op ↔
      ∀ x : B₀, f (c.hom x) = σ (f x) := by
    constructor
    · intro he x
      have he' := Quiver.Hom.op_inj ((algSpec.fullyFaithful (R := CommRingCat.of k)).map_injective he)
      exact DFunLike.congr_fun (congrArg CommAlgCat.Hom.hom he') x
    · intro he
      exact congrArg (fun v : B₀ →ₐ[k] K => (testSpec k).map (CommAlgCat.ofHom v).op) (AlgHom.ext he)
  rw [hf]
  constructor
  · intro he x
    have hx := he ((1 : K) ⊗ₜ[k] x)
    change h (σ (1 : K) ⊗ₜ[k] c.hom x) = σ (h (1 ⊗ₜ[k] x)) at hx
    rw [map_one] at hx
    exact hx
  · intro he z
    have he₁ (r : K) (x : B₀) : h (r ⊗ₜ[k] x) = r * f x := by
      rw [← (AlgHom.liftEquiv k K B₀ K).apply_symm_apply h]
      exact AlgHom.liftEquiv_tmul f r x
    induction z using TensorProduct.inductionOn with
    | tmul r x =>
      change h (σ r ⊗ₜ[k] c.hom x) = σ (h (r ⊗ₜ[k] x))
      rw [he₁, he₁, map_mul, he]
    | add x y hx hy =>
      change h ((extendedHopfMap K c).hom
          ((SemilinearAction.scalarExtension (K := K) B₀).act σ (x + y))) = σ (h (x + y))
      simp only [map_add]
      exact congrArg₂ (· + ·) hx hy


set_option backward.isDefEq.respectTransparency false in
private theorem scalarPoint_torusFactor {G : GroupScheme k} (T : ClosedSubgroup G)
    (g : 𝟙_ (SchemeOver k) ⟶ G.X) :
    (∃ z : 𝟙_ (SchemeOver k) ⟶ T.group.X, z ≫ T.inclusion.hom.hom = g) ↔
      ∃ z : 𝟙_ (SchemeOver K) ⟶ ((groupBaseChange k K).obj T.group).X,
        z ≫ ((groupBaseChange k K).map T.inclusion).hom.hom =
          scalarExtendedRationalPoint K g := by
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨scalarExtendedRationalPoint K z, (scalarRationalPoint_comp z _).symm⟩
  · rintro ⟨z, hz⟩
    letI : IsClosedImmersion T.inclusion.hom.hom.left := T.isClosedImmersion
    let b := Functor.LaxMonoidal.ε (baseChange k K)
    refine factor_of_baseChange K g T.inclusion.hom.hom (inv b ≫ z) ?_
    change (inv b ≫ z) ≫ ((groupBaseChange k K).map T.inclusion).hom.hom = _
    rw [Category.assoc, hz]
    change inv b ≫ b ≫ (baseChange k K).map g = _
    simp

private theorem equiv_fixed_at_involution {S : Type*} [Category S] {X Y : S}
    (f : X ⟶ Y) (c : X ⟶ X) (e : Y ≅ Y) (hc : c ≫ c = 𝟙 X) :
    f ≫ e.inv = c ≫ f ↔ f ≫ e.hom = c ≫ f := by
  have h (u : X ⟶ Y) : c ≫ (c ≫ u) = u := by
    rw [← Category.assoc, hc, Category.id_comp]
  constructor
  · intro hf
    calc
      f ≫ e.hom = (c ≫ (c ≫ f)) ≫ e.hom := congrArg (· ≫ e.hom) (h f).symm
      _ = (c ≫ (f ≫ e.inv)) ≫ e.hom := congrArg (fun z => (c ≫ z) ≫ e.hom) hf.symm
      _ = c ≫ f := by simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · intro hf
    calc
      f ≫ e.inv = (c ≫ (c ≫ f)) ≫ e.inv := congrArg (· ≫ e.inv) (h f).symm
      _ = (c ≫ (f ≫ e.hom)) ≫ e.inv := congrArg (fun z => (c ≫ z) ≫ e.inv) hf.symm
      _ = c ≫ f := by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
private theorem pinnedQuadraticPoint_fixed {A : AdditiveLine k} {P : PinnedGroup A}
    {D : AttachedDatum P.pair} {l : Aut D.toBased ≃* Aut P}
    {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}
    [FiniteDimensional k K] [IsGalois k K]
    (d : PinnedTwist K D l B T) (σ : Gal(K/k)) (hdegree : Module.finrank k K = 2) (hσ : σ ≠ 1)
    (h : extendedHopf K (affineCoordinates P.pair.G) →ₐ[K] K) :
    let s := (l (d.outer σ)).asIso.hom
    let y := evaluateSplitPoint P.pair.G h
    (∀ g z, h (pinnedCoordinateAction d g z) = g (h z)) ↔
      y ≫ s.group.hom.hom.hom = (testSpec k).map (CommAlgCat.ofHom σ.toAlgHom).op ≫ y := by
  let a := (Functor.mapAut P (forgetPinning (A := A)) (l (d.outer σ))).asIso
  let c : CommAlgCat.of k K ⟶ CommAlgCat.of k K := CommAlgCat.ofHom σ.toAlgHom
  let S := (testSpec k).map c.op
  let y := evaluateSplitPoint P.pair.G h
  have hcases := quadraticAut_cases hdegree σ hσ
  have hσ₂ : σ * σ = 1 := (hcases (σ * σ)).resolve_right fun h ↦
    hσ (mul_right_cancel (h.trans (one_mul σ).symm))
  have hc : c ≫ c = 𝟙 _ := by
    ext x
    exact DFunLike.congr_fun hσ₂ x
  have hS : S ≫ S = 𝟙 _ := by
    change (testSpec k).map c.op ≫ (testSpec k).map c.op = _
    rw [← Functor.map_comp, ← op_comp, hc, op_id]
    exact (testSpec k).map_id _
  have h1 : ∀ z, h (pinnedCoordinateAction d (1 : Gal(K/k)) z) = (1 : Gal(K/k)) (h z) := by
    have h' := (evaluateSplitPoint_fixed d (1 : Gal(K/k)) h).mpr
    apply h'
    have hId : CommAlgCat.ofHom ((1 : Gal(K/k)).toAlgHom) = 𝟙 (CommAlgCat.of k K) := rfl
    simp only [hId, map_one, Aut.one_asIso, Iso.refl_inv, Grp.id_hom_hom, op_id]
    rw [(testSpec k).map_id]
    exact (Category.comp_id y).trans (Category.id_comp y).symm
  rw [show (∀ g z, h (pinnedCoordinateAction d g z) = g (h z)) ↔
      ∀ z, h (pinnedCoordinateAction d σ z) = σ (h z) from
    ⟨fun hh => hh σ, fun hh g => (hcases g).elim (fun e => e.symm ▸ h1) (fun e => e.symm ▸ hh)⟩]
  have hv := evaluateSplitPoint_fixed d σ h
  dsimp only at hv
  rw [hv]
  let e := (Grp.forget (SchemeOver k)).mapIso a
  exact equiv_fixed_at_involution y S e hS

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 850000 in
theorem pinnedQuadraticNormalizer : PinnedQuadraticNormalizer.{u} := by
  classical
  intro k K _ _ _ _ _ D M E l G B T d σ hdegree hσ
  letI := E.torusComm
  let C := E.identification
  let P := E.realization.pinned
  let R := CommAlgCat.of k K
  let Y := (testSpec k).obj (Opposite.op R)
  let s := (l (d.outer σ)).asIso.hom
  let F := groupBaseChange k K
  dsimp only
  intro a ha N hN
  let H := MonoidHom.eqLocus a.toMonoidHom (fieldCoefficientAction σ C.normalizer.group)
  obtain ⟨c₁, c₂, hc₁, hc₂, t, f, ht, hfi, hf, hnf, hfix⟩ := pinnedFixedRationalNormalizer d
  let e := c₁.symm ≪≫ (hopfSpec (CommRingCat.of K)).mapIso d.groupIso.op ≪≫ c₂
  let p := extensionPointEquiv (K := K) P.pair.G.val
  let i := (IsMonHom.monoidHom C.normalizer.inclusion.hom.hom Y).comp H.subtype
  let j := p.toMonoidHom.comp (f.comp (IsMonHom.monoidHom N.inclusion.hom.hom (𝟙_ (SchemeOver k))))
  letI : IsClosedImmersion C.normalizer.inclusion.hom.hom.left := C.normalizer.isClosedImmersion
  letI : Mono C.normalizer.inclusion.hom.hom := Over.mono_of_mono_left _
  letI : IsClosedImmersion N.inclusion.hom.hom.left := N.isClosedImmersion
  letI : Mono N.inclusion.hom.hom := Over.mono_of_mono_left _
  letI : IsClosedImmersion P.pair.T.inclusion.hom.hom.left := P.pair.T.isClosedImmersion
  have hi : Function.Injective i := fun _ _ h => Subtype.ext ((cancel_mono C.normalizer.inclusion.hom.hom).mp h)
  have hj : Function.Injective j := fun _ _ h => (cancel_mono N.inclusion.hom.hom).mp (hfi (p.injective h))
  have hmem (n : Y ⟶ C.normalizer.group.X) :
      n ∈ H ↔ (n ≫ C.normalizer.inclusion.hom.hom) ≫ s.group.hom.hom.hom =
        (testSpec k).map (CommAlgCat.ofHom σ.toAlgHom).op ≫ (n ≫ C.normalizer.inclusion.hom.hom) := by
    change a n = fieldCoefficientAction σ C.normalizer.group n ↔ _
    rw [← (cancel_mono C.normalizer.inclusion.hom.hom), ha n]
    exact Iff.rfl.trans (by rw [← Category.assoc]; rfl)
  have hcoord (x : 𝟙_ (SchemeOver K) ⟶ (F.obj P.pair.G.val).X) :
      ∃ z : extendedHopf K (affineCoordinates P.pair.G) →ₐ[K] K, x = hopfFieldPoint z ≫ c₂.hom.hom.hom := by
    let b := (hopfRationalEquiv (extendedHopf K (affineCoordinates P.pair.G))).trans (sectionsIso c₂)
    obtain ⟨z, hz⟩ := b.surjective x
    refine ⟨z.ofConv, hz.symm.trans ?_⟩
    change hopfRationalEquiv (extendedHopf K (affineCoordinates P.pair.G)) (WithConv.toConv z.ofConv) ≫
      c₂.hom.hom.hom = _
    rw [hopfRationalEquiv_apply, hopfRationalPoint_eq]
  have hR : Set.range j = Set.range i := by
    ext y
    constructor
    · rintro ⟨n, rfl⟩
      let g := n ≫ N.inclusion.hom.hom
      have hg := (hN g).mpr ⟨n, rfl⟩
      obtain ⟨z, hz⟩ := hcoord (f g)
      obtain ⟨hn, hzfix⟩ := (hfix z).mpr ⟨g, hg, hz⟩
      obtain ⟨m, hm⟩ := (extensionPoint_normalizes P.pair.T C.normalizer C.representsNormalizer _).mp hn
      have hjm : m ≫ C.normalizer.inclusion.hom.hom = j n := hm.trans (congrArg p hz.symm)
      have hmp : m ≫ C.normalizer.inclusion.hom.hom = evaluateSplitPoint P.pair.G z :=
        hm.trans (extensionPoint_coordinates P.pair.G c₂ hc₂ z)
      exact ⟨⟨m, (hmem m).mpr (hmp ▸ (pinnedQuadraticPoint_fixed d σ hdegree hσ z).mp hzfix)⟩, hjm⟩
    · rintro ⟨n, rfl⟩
      obtain ⟨x, hx⟩ := p.surjective (i n)
      obtain ⟨z, hz⟩ := hcoord x
      have hpz : evaluateSplitPoint P.pair.G z = i n :=
        (extensionPoint_coordinates P.pair.G c₂ hc₂ z).symm.trans ((congrArg p hz).symm.trans hx)
      have hn := (extensionPoint_normalizes P.pair.T C.normalizer C.representsNormalizer x).mpr ⟨n.val, hx.symm⟩
      have hzfix := (pinnedQuadraticPoint_fixed d σ hdegree hσ z).mpr
        (hpz.symm ▸ (hmem n.val).mp n.property)
      obtain ⟨g, hg, hfg⟩ := (hfix z).mp ⟨hz ▸ hn, hzfix⟩
      obtain ⟨m, hm⟩ := (hN g).mp hg
      exact ⟨m, (congrArg (fun g => p (f g)) hm).trans
        ((congrArg p (hfg.trans hz.symm)).trans hx)⟩
  let b := MulEquiv.ofBijective (i.rangeRestrict) ⟨fun _ _ h => hi (congrArg Subtype.val h),
    fun z => ⟨z.property.choose, Subtype.ext z.property.choose_spec⟩⟩
  have hsub : j.range = i.range := SetLike.coe_injective hR
  let u' := (MulEquiv.ofBijective j.rangeRestrict
    ⟨fun _ _ h => hj (congrArg Subtype.val h), fun z => ⟨z.property.choose, Subtype.ext z.property.choose_spec⟩⟩).trans
      ((MulEquiv.subgroupCongr hsub).trans b.symm)
  have hu (n : 𝟙_ (SchemeOver k) ⟶ N.group.X) : i (u' n) = j n := by
    change ((b (b.symm _)).val : Y ⟶ P.pair.G.val.X) = _
    rw [b.apply_symm_apply]
    rfl
  refine ⟨c₁, c₂, hc₁, hc₂, t, u', ht, fun n => ?_, fun n => ?_⟩
  · have h := hu n
    change (u' n).val ≫ C.normalizer.inclusion.hom.hom =
      p (f (n ≫ N.inclusion.hom.hom)) at h
    rw [h, hf]
    change (𝟙 (Spec (CommRingCat.of K)) ≫ _) ≫ _ = _
    rw [Category.id_comp]
  · let g := n ≫ N.inclusion.hom.hom
    have h := hu n
    change (u' n).val ≫ C.normalizer.inclusion.hom.hom = p (f g) at h
    have hp : ∀ z : Y ⟶ P.pair.T.group.X,
        (z ≫ C.torusInclusion.hom.hom = (u' n).val) ↔
          (z ≫ P.pair.T.inclusion.hom.hom = p (f g)) := by
      intro z
      rw [← cancel_mono C.normalizer.inclusion.hom.hom, Category.assoc, h]
      rw [← Grp.comp_hom_hom, C.inclusion_eq]
    change (∃ z : 𝟙_ (SchemeOver k) ⟶ T.group.X, z ≫ T.inclusion.hom.hom = g) ↔
      ∃ z : Y ⟶ P.pair.T.group.X, z ≫ C.torusInclusion.hom.hom = (u' n).val
    rw [exists_congr hp, scalarPoint_torusFactor (K := K) T g, hf g]
    have ht' : t.hom.hom.hom ≫ (F.map P.pair.T.inclusion).hom.hom =
        (F.map T.inclusion).hom.hom ≫ e.hom.hom.hom := congrArg (fun a => a.hom.hom) ht
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨extensionPointEquiv P.pair.T.group (z ≫ t.hom.hom.hom), ?_⟩
      rw [← extensionPointEquiv_natural, Category.assoc, ht', ← Category.assoc, hz]
    · rintro ⟨z, hz⟩
      obtain ⟨v, rfl⟩ := (extensionPointEquiv (K := K) P.pair.T.group).surjective z
      have hv := p.injective ((extensionPointEquiv_natural P.pair.T.inclusion v).trans hz)
      refine ⟨v ≫ t.inv.hom.hom, ?_⟩
      have hte : t.inv ≫ F.map T.inclusion = F.map P.pair.T.inclusion ≫ e.inv := by
        apply (cancel_mono e.hom).mp
        rw [Category.assoc, ← ht, Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id,
          Category.comp_id]
      rw [Category.assoc, ← Grp.comp_hom_hom, hte, Grp.comp_hom_hom, ← Category.assoc, hv,
        Category.assoc, ← Grp.comp_hom_hom, Iso.hom_inv_id, Grp.id_hom_hom]
      exact Category.comp_id _

end RationalFixedPoints

section ScalarScaling

open AlgebraicGeometry
open scoped TensorProduct
open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel (Integers IntegralPoints TorusValues Model integerAlgebra
  integralPointFunctor forgetFibrePoint torusPoint integralSpec cocharacter)
attribute [local instance] integerAlgebra

section ValuedExtensions

variable {K L : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

private theorem normalizedValuation_le_iff (a b : K) :
    normalizedValuation K a ≤ normalizedValuation K b ↔ a ≤ᵥ b := by
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  change e (valuation K a) ≤ e (valuation K b) ↔ a ≤ᵥ b
  rw [map_le_map_iff]
  exact ((valuation K).vle_iff_le).symm

variable [Field L] [Algebra K L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]

private theorem normalizedValuation_log_extension [ValuativeExtension K L]
    (π : Kˣ) (hπ : log (normalizedValuation K (π : K)) = -1) (x : Kˣ) :
    log (normalizedValuation L (algebraMap K L (x : K))) =
      -log (normalizedValuation L (algebraMap K L (π : K))) *
        log (normalizedValuation K (x : K)) := by
  let n := -log (normalizedValuation K (x : K))
  have hn : (integerValuationOnUnits K (π ^ n)).toAdd = (integerValuationOnUnits K x).toAdd := by
    rw [map_zpow, toAdd_zpow, zsmul_eq_mul]
    change n * log (normalizedValuation K (π : K)) = log (normalizedValuation K (x : K))
    rw [hπ]
    simp [n]
  have hx : normalizedValuation K ((π ^ n : Kˣ) : K) = normalizedValuation K (x : K) := by
    simpa only [integerValuationOnUnits, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd,
      exp_log (by exact (map_ne_zero (normalizedValuation K)).mpr (π ^ n : Kˣ).ne_zero : normalizedValuation K ((π ^ n : Kˣ) : K) ≠ 0),
      exp_log (by simp : normalizedValuation K (x : K) ≠ 0)] using congrArg exp hn
  have hL : normalizedValuation L (algebraMap K L ((π ^ n : Kˣ) : K)) =
      normalizedValuation L (algebraMap K L (x : K)) := by
    apply le_antisymm <;>
      rw [normalizedValuation_le_iff, ValuativeExtension.vle_iff_vle, ← normalizedValuation_le_iff, hx]
  let w : Kˣ →* Lˣ := Units.map (algebraMap K L).toMonoidHom
  have hx' := congrArg log hL
  change (integerValuationOnUnits L (w (π ^ n))).toAdd = log (normalizedValuation L (algebraMap K L ↑x)) at hx'
  rw [w.map_zpow, map_zpow, toAdd_zpow, zsmul_eq_mul] at hx'
  rw [← hx']
  change n * log (normalizedValuation L (algebraMap K L (π : K))) = _
  rw [neg_mul, neg_mul, mul_comm (log (normalizedValuation K (x : K)))]
  
end ValuedExtensions

theorem involutiveValuationInvariant : InvolutiveValuationInvariant.{u} := by
  intro k K _ _ _ _ _ _ _ r _ _ ext σ hσ x
  have hc (a b : K) : σ a ≤ᵥ σ b ↔ a ≤ᵥ b := by
    let v := valuation K
    have hiff (x y : K) : v x ≤ v y ↔ x ≤ᵥ y := ((valuation K).vle_iff_le).symm
    let w := ValuativeRel.ofValuation (v.comap σ.toRingHom)
    have hwe : @ValuativeExtension k K _ _ _ w _ := by
      constructor
      intro x y
      change v (σ (algebraMap k K x)) ≤ v (σ (algebraMap k K y)) ↔ _
      rw [σ.commutes, σ.commutes]
      exact (hiff _ _).trans (@ValuativeExtension.vle_iff_vle k K _ _ _ r _ ext x y)
    have hw : w = r := by
      obtain ⟨_, _, _, _, _, _, uniq⟩ := finiteExtension_localField (K := k) (L := K)
      exact (uniq w hwe).trans (uniq r ext).symm
    refine (hiff _ _).symm.trans ?_
    change @ValuativeRel.vle K _ w a b ↔ @ValuativeRel.vle K _ r a b
    rw [hw]
  have hv : normalizedValuation K (σ x) ≤ normalizedValuation K x ↔
      normalizedValuation K x ≤ normalizedValuation K (σ x) := by
    rw [normalizedValuation_le_iff, normalizedValuation_le_iff]
    simpa only [hσ x] using hc x (σ x)
  rcases le_total (normalizedValuation K (σ x)) (normalizedValuation K x) with h | h
  · exact le_antisymm h (hv.mp h)
  · exact le_antisymm (hv.mpr h) h

theorem uniformizerRootExtension : UniformizerRootExtension.{u} := by
  intro K _ _ _ _ m hm π hπ
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K (AlgebraicClosure K) (π : K)) hm
  let L := IntermediateField.adjoin K ({x} : Set (AlgebraicClosure K))
  let y : L := ⟨x, IntermediateField.mem_adjoin_simple_self K x⟩
  letI : FiniteDimensional K L := IntermediateField.adjoin.finiteDimensional
    (Algebra.IsIntegral.isIntegral (R := K) x)
  obtain ⟨v, t, hv, ht, _, _, _⟩ := finiteExtension_localField (K := K) (L := L)
  letI : ValuativeRel L := v
  letI : TopologicalSpace L := t
  letI : ValuativeExtension K L := hv
  letI : IsNonarchimedeanLocalField L := ht
  have hy : y ^ m = algebraMap K L (π : K) := Subtype.ext hx
  have hy₀ : y ≠ 0 := by
    intro h
    have hh : algebraMap K L (π : K) = algebraMap K L 0 := by
      simpa only [h, zero_pow hm.ne', map_zero] using hy.symm
    exact π.ne_zero ((algebraMap K L).injective hh)
  let s : Lˣ := Units.mk0 y hy₀
  have hs : s ^ m = Units.map (algebraMap K L).toMonoidHom π := Units.ext hy
  let c := -log (normalizedValuation L y)
  have hpow : log (normalizedValuation L (algebraMap K L (π : K))) = (m : ℤ) * -c := by
    rw [← hy, map_pow, log_pow, nsmul_eq_mul]
    simp [c]
  have hlt : normalizedValuation K (π : K) < 1 := by
    rw [← exp_zero, ← log_lt_iff_lt_exp (by simp), hπ]
    norm_num
  have hlt' : normalizedValuation L (algebraMap K L (π : K)) < 1 := by
    apply lt_of_not_ge
    intro hh
    have h' : normalizedValuation L (algebraMap K L 1) ≤
        normalizedValuation L (algebraMap K L (π : K)) := by simpa only [map_one] using hh
    rw [normalizedValuation_le_iff, ValuativeExtension.vle_iff_vle, ← normalizedValuation_le_iff] at h'
    exact hlt.not_ge (by simpa only [map_one] using h')
  have hneg : log (normalizedValuation L (algebraMap K L (π : K))) < 0 :=
    (log_lt_iff_lt_exp (by simp)).mpr (by simpa only [exp_zero] using hlt')
  rw [hpow] at hneg
  have hpos : 0 < c := by
    have hm' : 0 < (m : ℤ) := by exact_mod_cast hm
    nlinarith
  refine ⟨L, inferInstance, inferInstance, v, t, inferInstance, hv, ht, s, c, hpos, hs, by simp [c, s], ?_⟩
  intro u
  rw [normalizedValuation_log_extension π hπ, hpow, mul_neg, neg_neg]

section MarkedScaling

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open private fibrePointsEquiv torusPoint_natural restrictToIntegers
  from LinearAlgebraicGroups.Classification.IntegralSemisimpleModel

private theorem rationalCocharacters_clearDenominators {D : BasedRootDatum.{u}}
    {index : Type u} [Fintype index] (b : Module.Basis index ℤ D.Y) (x y : ℚ ⊗[ℤ] D.Y) :
    ∃ m : ℕ, 0 < m ∧ ∃ a b : D.Y,
      (1 : ℚ) ⊗ₜ[ℤ] a = (m : ℚ) • x ∧ (1 : ℚ) ⊗ₜ[ℤ] b = (m : ℚ) • y := by
  classical
  let e := (b.baseChange ℚ).repr
  let m₁ := ∏ i, (e x i).den
  let m₂ := ∏ i, (e y i).den
  let m := m₁ * m₂
  have h₁ : 0 < m₁ := Finset.prod_pos fun i _ => (e x i).den_pos
  have h₂ : 0 < m₂ := Finset.prod_pos fun i _ => (e y i).den_pos
  refine ⟨m, Nat.mul_pos h₁ h₂, ?_⟩
  have aux (z : ℚ ⊗[ℤ] D.Y) (hz : ∀ i, (e z i).den ∣ m) :
      ∃ a : D.Y, (1 : ℚ) ⊗ₜ[ℤ] a = (m : ℚ) • z := by
    choose p hp using hz
    let u (i : index) : ℤ := (e z i).num * (p i : ℤ)
    refine ⟨b.equivFun.symm u, e.injective ?_⟩
    ext i
    have hu : b.repr (b.equivFun.symm u) i = u i := congrFun (b.equivFun.apply_symm_apply u) i
    change (b.baseChange ℚ).repr ((1 : ℚ) ⊗ₜ[ℤ] b.equivFun.symm u) i = e ((m : ℚ) • z) i
    rw [map_smul, Finsupp.smul_apply, Module.Basis.baseChange_repr_tmul, hu,
      zsmul_eq_mul, mul_one, smul_eq_mul]
    have hq : ((e z i).den : ℚ) * e z i = (e z i).num := by
      rw [mul_comm, ← eq_div_iff (by exact_mod_cast (e z i).den_ne_zero)]
      exact (e z i).num_div_den.symm
    dsimp only [u]
    rw [Int.cast_mul, Int.cast_natCast, hp i, Nat.cast_mul, mul_right_comm, hq]
  obtain ⟨a, ha⟩ := aux x (fun i => dvd_mul_of_dvd_left
    (Finset.dvd_prod_of_mem (fun j => (e x j).den) (Finset.mem_univ i)) _)
  obtain ⟨b, hb⟩ := aux y (fun i => dvd_mul_of_dvd_right
    (Finset.dvd_prod_of_mem (fun j => (e y j).den) (Finset.mem_univ i)) _)
  exact ⟨a, b, ha, hb⟩

private def markedNormalizerPointHom {k : Type u} [Field k] {D : BasedRootDatum.{u}} {M : Model D}
    (F : FibreNormalizer M k) (R : TestAlgebra k) :
    letI := F.torusComm
    Points F.identification.normalizer.group.X R →* IntegralPoints M.group (CommAlgCat.of Integers.{u} R) := by
  letI := F.torusComm
  let Y := (testSpec k).obj (Opposite.op R)
  exact (fibrePointsEquiv M.group R).toMonoidHom.comp
    (IsMonHom.monoidHom (F.identification.normalizer.inclusion ≫ F.fibreIso.inv).hom.hom Y)

private theorem markedNormalizerPointHom_apply {k : Type u} [Field k] {D : BasedRootDatum.{u}}
    {M : Model D} (F : FibreNormalizer M k) (R : TestAlgebra k) :
    letI := F.torusComm
    ∀ n, markedNormalizerPointHom F R n = markedNormalizerPoint F R n := by
  letI := F.torusComm
  intro n
  change forgetFibrePoint M.group R
      (n ≫ F.identification.normalizer.inclusion.hom.hom ≫ F.fibreIso.inv.hom.hom) = markedNormalizerPoint F R n
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem markedNormalizerPoint_natural {k : Type u} [Field k] {D : BasedRootDatum.{u}}
    {M : Model D} (F : FibreNormalizer M k) {R S : TestAlgebra k} (f : R ⟶ S) :
    letI := F.torusComm
    ∀ n : Points F.identification.normalizer.group.X R,
      (integralPointFunctor M.group).map ((restrictToIntegers k).map f)
          (markedNormalizerPoint F R n) =
        markedNormalizerPoint F S (mapPoints f n) := by
  letI := F.torusComm
  intro n
  apply Over.OverMorphism.ext
  dsimp only [markedNormalizerPoint, forgetFibrePoint, mapPoints]
  change Spec.map (CommRingCat.ofHom f.hom.toRingHom) ≫
    ((n.left ≫ F.identification.normalizer.inclusion.hom.hom.left ≫ F.fibreIso.inv.hom.hom.left) ≫
      Limits.pullback.fst ..) =
    (((Spec.map (CommRingCat.ofHom f.hom.toRingHom) ≫ n.left) ≫
      F.identification.normalizer.inclusion.hom.hom.left ≫ F.fibreIso.inv.hom.hom.left)) ≫
      Limits.pullback.fst ..
  simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem normalizerLabel_natural {k K L : Type u} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] {D : BasedRootDatum.{u}} {M : Model D}
    (F : FibreNormalizer M k) :
    letI := F.torusComm
    let C := F.identification
    let R := CommAlgCat.of k K
    let S := CommAlgCat.of k L
    let X := (testSpec k).obj (Opposite.op R)
    let Y := (testSpec k).obj (Opposite.op S)
    ∀ (q : Points C.normalizer.group.X R →* D.datum.weylGroup)
      (q' : Points C.normalizer.group.X S →* D.datum.weylGroup),
      (∀ n, n ≫ C.quotient.hom.hom = toUnit X ≫ C.image.constantGroup.sectionPoint (C.labelEquiv (F.labelIso (q n)))) →
      (∀ n, n ≫ C.quotient.hom.hom = toUnit Y ≫ C.image.constantGroup.sectionPoint (C.labelEquiv (F.labelIso (q' n)))) →
      ∀ (f : R ⟶ S) n, q' (mapPoints f n) = q n := by
  letI := F.torusComm
  let C := F.identification
  let R := CommAlgCat.of k K
  let S := CommAlgCat.of k L
  let X := (testSpec k).obj (Opposite.op R)
  let Y := (testSpec k).obj (Opposite.op S)
  dsimp only
  intro q q' hq hq' f n
  have h := hq' (mapPoints f n)
  change (((testSpec k).map f.op ≫ n) ≫ C.quotient.hom.hom) = _ at h
  rw [Category.assoc, hq n, ← Category.assoc, comp_toUnit] at h
  apply F.labelIso.injective
  apply C.labelEquiv.injective
  have he := congrArg (fun z => C.image.constantGroup.families Y z (IsLocalRing.closedPoint L)) h.symm
  change C.image.constantGroup.families Y
      (toUnit Y ≫ C.image.constantGroup.sectionPoint (C.labelEquiv (F.labelIso (q' (mapPoints f n)))))
      (IsLocalRing.closedPoint L) =
    C.image.constantGroup.families Y
      (toUnit Y ≫ C.image.constantGroup.sectionPoint (C.labelEquiv (F.labelIso (q n))))
      (IsLocalRing.closedPoint L) at he
  simpa only [C.image.constantGroup.constant, LocallyConstant.coe_const, Function.const_apply] using he

private def extensionIntegerMap {K L : Type u} [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [ValuativeRel L] [ValuativeExtension K L] :
    CommAlgCat.of Integers.{u} (valuation K).valuationSubring ⟶
      CommAlgCat.of Integers.{u} (valuation L).valuationSubring :=
  CommAlgCat.ofHom
    ({ ((algebraMap K L).comp (valuation K).valuationSubring.subtype).codRestrict
      (valuation L).valuationSubring.toSubring (fun x => by
       change valuation L (algebraMap K L (x : K)) ≤ 1
       rw [← map_one (valuation L), ← map_one (algebraMap K L), ← (valuation L).vle_iff_le,
         ValuativeExtension.vle_iff_vle, (valuation K).vle_iff_le, map_one]
       exact x.property) with commutes' := fun x => Subtype.ext (map_intCast _ x.down) } :
      (valuation K).valuationSubring →ₐ[Integers.{u}] (valuation L).valuationSubring)


set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1700000 in
theorem scalarAffineScaling : ScalarAffineScaling.{u} := by
  classical
  intro k K _ _ _ _ _ _ D M F index _ b
  letI := F.torusComm
  let C := F.identification
  let R := CommAlgCat.of k K
  let S := CommAlgCat.of Integers.{u} K
  let Y := (testSpec k).obj (Opposite.op R)
  let N := (Y ⟶ C.normalizer.group.X)
  let J := markedNormalizerPointHom F R
  dsimp only
  intro q hq hk n m hnm hm r hr x π hπ
  obtain ⟨j, _, hj, _⟩ := normalizerFieldTorusAction F q hq hk
  let nt : q.ker := ⟨n * m⁻¹, by simp [hnm]⟩
  let t := j.symm nt
  have ht' : J (n * m⁻¹) = torusPoint D S t ≫ M.torus.hom.hom := by
    have he : j t = nt := j.apply_symm_apply nt
    rw [markedNormalizerPointHom_apply]
    change forgetFibrePoint M.group R
      (nt.val ≫ C.normalizer.inclusion.hom.hom ≫ F.fibreIso.inv.hom.hom) = _
    rw [← he]
    exact hj t
  obtain ⟨ν, _, hν, _⟩ := splitTorusTranslation K D b
  let z := (ν t).toAdd
  let w := (q n).val.coweightEquiv.symm
  let wℚ := w.baseChange ℤ ℚ D.Y D.Y
  let y := wℚ x + ((r : ℚ)⁻¹ ⊗ₜ[ℤ] z)
  refine ⟨t, z, ht', hν t, ?_⟩
  obtain ⟨d, hd, a, a', ha, ha'⟩ :=
    rationalCocharacters_clearDenominators b ((r : ℚ) • x) ((r : ℚ) • y)
  obtain ⟨L, fL, aL, vL, tL, hfin, hext, hloc, s, c, _, hs, hslog, hlog⟩ :=
    uniformizerRootExtension d hd π hπ
  letI := fL
  letI := aL
  letI := vL
  letI := tL
  letI := hfin
  letI := hext
  letI := hloc
  have hrr : (r : ℚ) ≠ 0 := by exact_mod_cast hr.ne'
  have hxy : (r : ℚ) • y = wℚ ((r : ℚ) • x) + ((1 : ℚ) ⊗ₜ[ℤ] z) := by
    dsimp only [y]
    rw [smul_add, map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_inv_cancel₀ hrr]
  have ha'' : a' = w a + (d : ℤ) • z := by
    apply integralCocharacter_injective D b
    change (1 : ℚ) ⊗ₜ[ℤ] a' = (1 : ℚ) ⊗ₜ[ℤ] (w a + (d : ℤ) • z)
    have htz : (d : ℚ) • ((1 : ℚ) ⊗ₜ[ℤ] z) = (1 : ℚ) ⊗ₜ[ℤ] ((d : ℤ) • z) := by
      rw [TensorProduct.smul_tmul', TensorProduct.tmul_smul]
      congr 1
    rw [ha', hxy, smul_add, ← map_smul, ← ha, TensorProduct.tmul_add, htz]
    rfl
  refine ⟨d, hd, L, fL, aL, vL, tL, hfin, hext, hloc, s, a, a', hs, ha, ha', ?_⟩
  letI : Algebra k L := ((algebraMap K L).comp (algebraMap k K)).toAlgebra
  let RL := CommAlgCat.of k L
  let SL := CommAlgCat.of Integers.{u} L
  let fKL : R ⟶ RL := CommAlgCat.ofHom
    ({ (algebraMap K L) with commutes' := fun _ ↦ rfl } : K →ₐ[k] L)
  let fI : S ⟶ SL := (restrictToIntegers k).map fKL
  let g : IntegralPoints M.group S →* IntegralPoints M.group SL := ((integralPointFunctor M.group).map fI).hom
  let mL := mapPoints fKL m
  let nL := mapPoints fKL n
  let JL := markedNormalizerPointHom F RL
  obtain ⟨qL, _, hqL, hkL, _, _⟩ := normalizerFieldLabels (K := L) F
  have hqLm : qL mL = q n := (normalizerLabel_natural F q qL hq hqL fKL m).trans hnm.symm
  obtain ⟨jL, _, hjL, hconj⟩ := normalizerFieldTorusAction F qL hqL hkL
  let ιT : TorusValues D SL →* IntegralPoints M.group SL :=
    MonoidHom.mk' (fun v => JL (jL v).val) (by
      intro u v
      rw [map_mul]
      exact JL.map_mul _ _)
  have hι (v : TorusValues D SL) : ιT v = torusPoint D SL v ≫ M.torus.hom.hom := by
    change JL (jL v).val = _
    rw [markedNormalizerPointHom_apply]
    exact hjL v
  let tE : TorusValues D SL := (Units.map fI.hom.toMonoidHom).comp t
  have hmap (v : N) : g (J v) = JL (mapPoints fKL v) := by
    change g (markedNormalizerPointHom F R v) = markedNormalizerPointHom F RL (mapPoints fKL v)
    rw [markedNormalizerPointHom_apply, markedNormalizerPointHom_apply]
    exact markedNormalizerPoint_natural F fKL v
  have htL : JL nL * (JL mL)⁻¹ = ιT tE := by
    rw [← hmap n, ← hmap m, ← map_inv, ← map_mul, ← map_inv, ← map_mul, ht', hι]
    change (integralSpec.map fI.op ≫ torusPoint D S t ≫ M.torus.hom.hom) = _
    rw [← Category.assoc]
    exact congrArg (· ≫ M.torus.hom.hom) (torusPoint_natural fI t)
  let wchar := (q n).val.weightEquiv.symm.toLinearMap.toAddMonoidHom.toMultiplicative
  have hmul (v : TorusValues D SL) : JL mL * ιT v * (JL mL)⁻¹ = ιT (v.comp wchar) := by
    have heq := congrArg (fun z : qL.ker => JL z.val) (hconj mL v)
    change JL (mL * (jL v).val * mL⁻¹) =
      JL (jL (v.comp (qL mL).val.weightEquiv.symm.toLinearMap.toAddMonoidHom.toMultiplicative)).val at heq
    rw [map_mul, map_mul, map_inv, hqLm] at heq
    exact heq
  let C₀ := cocharacter D a SL s
  let B₀ := cocharacter D a' SL s
  let z₀ := B₀ * tE * (C₀⁻¹).comp wchar
  have hscaled : ιT B₀ * JL nL * (ιT C₀)⁻¹ = ιT z₀ * JL mL := by
    have hn : JL nL = ιT tE * JL mL := by rw [← htL, inv_mul_cancel_right]
    dsimp only [z₀]
    rw [hn, ιT.map_mul, ιT.map_mul, ← hmul, ιT.map_inv]
    simp [mul_assoc]
  obtain ⟨νL, _, hνL, hνL0⟩ := splitTorusTranslation L D b
  have htlog : (νL tE).toAdd = ((d : ℤ) * c) • z := by
    apply D.datum.toLinearMap.flip.toPerfPair.injective
    ext χ
    change D.datum.toLinearMap χ (νL tE).toAdd = D.datum.toLinearMap χ (((d : ℤ) * c) • z)
    rw [hνL, map_smul]
    change log (normalizedValuation L (algebraMap K L (t (Multiplicative.ofAdd χ) : K))) =
      ((d : ℤ) * c) • D.datum.toLinearMap χ (ν t).toAdd
    rw [hν t χ, zsmul_eq_mul]
    exact hlog (t (Multiplicative.ofAdd χ))
  obtain ⟨hcoch, hweyl⟩ := splitTranslationAction D νL hνL
  have hB : (νL B₀).toAdd = -c • a' := (hcoch a' s).trans (congrArg (· • a') hslog)
  have hC : (νL C₀).toAdd = -c • a := (hcoch a s).trans (congrArg (· • a) hslog)
  have hz₀ : νL z₀ = 1 := by
    apply Multiplicative.toAdd.injective
    change (νL (B₀ * tE * (C₀⁻¹).comp wchar)).toAdd = 0
    have hv := hweyl (q n).val C₀⁻¹
    change (νL ((C₀⁻¹).comp wchar)).toAdd = w (νL C₀⁻¹).toAdd at hv
    simp only [νL.map_mul, toAdd_mul]
    rw [hB, htlog, hv, νL.map_inv, toAdd_inv, hC, map_neg, map_smul, ha'']
    simp only [smul_add, neg_smul, ← mul_smul, neg_neg]
    abel_nf
    rw [← add_smul]
    have hh : (-1 : ℤ) • c * (d : ℤ) + (d : ℤ) * c = 0 := by
      simp [mul_comm]
    rw [hh, zero_smul]
  have hw (χ : D.X) : normalizedValuation L (z₀ (Multiplicative.ofAdd χ) : L) = 1 := by
    rw [← integerValuationOnUnits_eq_one L]
    apply Multiplicative.toAdd.injective
    have hh := (hνL z₀ χ).symm
    rwa [hz₀, toAdd_one, map_zero] at hh
  obtain ⟨p, hp⟩ := hm
  have hpL : JL mL ∈ ((integralPointFunctor M.group).map (valuationRingInclusion L)).hom.range := by
    let β := extensionIntegerMap (K := K) (L := L)
    have he : β ≫ valuationRingInclusion L = valuationRingInclusion K ≫ fI := by
      ext p
      rfl
    refine ⟨(integralPointFunctor M.group).map β p, ?_⟩
    let U := integralPointFunctor M.group
    have he' := congrArg (fun f => (U.map f) p) he
    simp only [Functor.map_comp, GrpCat.comp_apply] at he'
    change (U.map (valuationRingInclusion L)) ((U.map β) p) = JL mL
    rw [he', ← hmap m, markedNormalizerPointHom_apply]
    exact congrArg g hp
  have hzL : ιT z₀ ∈ ((integralPointFunctor M.group).map (valuationRingInclusion L)).hom.range := by
    rw [hι]
    exact (markedIntegralTorusKernel D M.toIntegralMarking b z₀).mp (fun i => hw (characterBasis D b i))
  have hpoint (v : N) : g (markedNormalizerPoint F R v) = JL (mapPoints fKL v) :=
    (congrArg g (markedNormalizerPointHom_apply F R v).symm).trans (hmap v)
  let A := ((integralPointFunctor M.group).map (valuationRingInclusion L)).hom.range
  have heq :
      (show IntegralPoints M.group SL from torusPoint D SL B₀ ≫ M.torus.hom.hom) *
          g (markedNormalizerPoint F R n) *
          (show IntegralPoints M.group SL from torusPoint D SL C₀ ≫ M.torus.hom.hom)⁻¹ =
      (show IntegralPoints M.group SL from torusPoint D SL z₀ ≫ M.torus.hom.hom) *
          g (markedNormalizerPoint F R m) := by
    rw [← hι B₀, ← hι C₀, ← hι z₀, hpoint n, hpoint m]
    exact hscaled
  refine ⟨z₀, hw, heq, ?_⟩
  change (show IntegralPoints M.group SL from torusPoint D SL B₀ ≫ M.torus.hom.hom) *
          g (markedNormalizerPoint F R n) *
          (show IntegralPoints M.group SL from torusPoint D SL C₀ ≫ M.torus.hom.hom)⁻¹ ∈ A
  rw [heq, ← hι z₀, hpoint m]
  exact A.mul_mem hzL hpL

end MarkedScaling

end ScalarScaling

section RelativeLabels

open AlgebraicGeometry CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj
open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup ClosedSubgroup)
open Specs.Relative.RelativeWeylScheme (QuotientData rationalProjection)
open private constantRationalEquiv from LinearAlgebraicGroups.Relative.RelativeWeylScheme
open private schemeKernel_sections from LinearAlgebraicGroups.Affine.SchemeImageQuotient

set_option backward.isDefEq.respectTransparency false in
theorem relativeWeylLabels : RelativeWeylLabels.{u} := by
  intro k _ G S T N hT hsurj W _ q hq hk
  let C := constantRationalEquiv N.splitImage.constantGroup
  let l := C.symm.toMonoidHom.comp (rationalProjection N)
  have hl (n : 𝟙_ (SchemeOver k) ⟶ N.normalizer.group.X) : C (l n) = rationalProjection N n :=
    C.apply_symm_apply _
  have hC (w : N.splitImage.labels) : C w = N.splitImage.constantGroup.sectionPoint w := rfl
  have hls : Function.Surjective l := by
    intro w
    obtain ⟨n, hn⟩ := hsurj w
    exact ⟨n, C.injective ((hl n).trans (hn.trans (hC w).symm))⟩
  letI : IsClosedImmersion N.normalizer.inclusion.hom.hom.left := N.normalizer.isClosedImmersion
  letI : Mono N.normalizer.inclusion.hom.hom := Over.mono_of_mono_left _
  have hincl : N.inclusion.hom.hom ≫ N.normalizer.inclusion.hom.hom = N.centralizer.inclusion.hom.hom :=
    congrArg (fun f => f.hom.hom) N.inclusionProperty
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := hT
  have hi' : i.hom.hom ≫ T.inclusion.hom.hom = N.centralizer.inclusion.hom.hom :=
    congrArg (fun f => f.hom.hom) hi
  have hj' : j.hom.hom ≫ N.centralizer.inclusion.hom.hom = T.inclusion.hom.hom :=
    congrArg (fun f => f.hom.hom) hj
  have hker : l.ker = q.ker := by
    ext n
    have h₁ : l n = 1 ↔ rationalProjection N n = 1 := by rw [← hl, ← C.map_one, C.injective.eq_iff]
    change l n = 1 ↔ q n = 1
    rw [h₁, hk n]
    refine (schemeKernel_sections N.quotientProperty.1 n).symm.trans ?_
    constructor
    · rintro ⟨v, hv⟩
      change v ≫ N.inclusion.hom.hom = n at hv
      refine ⟨v ≫ i.hom.hom, ?_⟩
      rw [Category.assoc, hi', ← hincl, ← Category.assoc, hv]
    · rintro ⟨v, hv⟩
      refine ⟨v ≫ j.hom.hom, (cancel_mono N.normalizer.inclusion.hom.hom).mp ?_⟩
      change ((v ≫ j.hom.hom) ≫ N.inclusion.hom.hom) ≫ N.normalizer.inclusion.hom.hom =
        n ≫ N.normalizer.inclusion.hom.hom
      simp only [Category.assoc, hincl, hj', hv]
  let e := (QuotientGroup.quotientKerEquivOfSurjective l hls).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans (QuotientGroup.quotientKerEquivOfSurjective q hq))
  refine ⟨e, fun n => ?_⟩
  have he : e (l n) = q n := by
    have eqL : QuotientGroup.quotientKerEquivOfSurjective l hls (QuotientGroup.mk n) = l n := rfl
    rw [← eqL]
    change QuotientGroup.quotientKerEquivOfSurjective q hq
      (QuotientGroup.quotientMulEquivOfEq hker
        ((QuotientGroup.quotientKerEquivOfSurjective l hls).symm
          (QuotientGroup.quotientKerEquivOfSurjective l hls (QuotientGroup.mk n)))) = _
    rw [MulEquiv.symm_apply_apply, QuotientGroup.quotientMulEquivOfEq_mk]
    rfl
  rw [← he, e.symm_apply_apply, ← hC, hl]

end RelativeLabels

end

end LinearAlgebraicGroups.Arithmetic.ExceptionalValuedTorusNormalizer
