import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.OddSpinCharTwoStabilizer
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SplitSpin
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.SpinOrthogonalWords
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.StandardGroups
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.HopfFaithfulFlatness
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SmoothnessCriteria
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricRadicals
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.LinearAlgebra.CliffordAlgebra.Inversion
import Batteries.Tactic.OpenPrivate
import Mathlib.Data.Fintype.WithTopBot
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.RingTheory.Finiteness.Descent

open CliffordAlgebra Module
open LinearAlgebraicGroups.Albert
open LinearAlgebraicGroups.Specs.Arithmetic.OddSpinCharTwoStabilizer

namespace LinearAlgebraicGroups.Arithmetic.OddSpinCharTwoStabilizer

universe u v w i

noncomputable section

open private contract_polar contract_coord involute_of_two_eq_zero orderedBasis orderedBasis_apply orderedBasis_singleton orderedBasis_empty scalar_injective
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinFunctor

private theorem word_eq_sort {R V I : Type*} [CommRing R] [AddCommGroup V]
    [Module R V] [LinearOrder I] (q : QuadraticForm R V) (b : Basis I R V)
    (s : Finset I) :
    CliffordSpecification.orderedWord q b s = (s.sort.map (ι q ∘ b)).prod := by
  unfold CliffordSpecification.orderedWord
  rw [← Finset.listMap_orderEmbOfFin_finRange s rfl, List.map_map]
  simp [List.ofFn_eq_map, Function.comp_def, Set.powersetCard.ofFinEmbEquiv_symm_apply]

private def intoWithTop (I : Type*) [LinearOrder I] : I ↪o WithTop I :=
  OrderEmbedding.ofStrictMono (fun i => (i : WithTop I)) WithTop.coe_strictMono

private theorem map_orderedBasis {R V W I : Type*} [CommRing R] [AddCommGroup V]
    [Module R V] [AddCommGroup W] [Module R W] [LinearOrder I]
    {q : QuadraticForm R V} {Q : QuadraticForm R W} {J : q →qᵢ Q}
    {b : Basis I R V} {d : Basis (WithTop I) R W}
    (hb : ∀ a : I, d (a : WithTop I) = J (b a)) (s : Finset I) :
    CliffordAlgebra.map J (orderedBasis q b s) =
      orderedBasis Q d (s.map (intoWithTop I).toEmbedding) := by
  rw [orderedBasis_apply, orderedBasis_apply,
    word_eq_sort, word_eq_sort, map_list_prod, List.map_map, ← ((intoWithTop I).strictMono.strictMonoOn (s : Set I)).map_finsetSort, List.map_map]
  congr 1
  apply List.map_congr_left
  intro a _
  simp [intoWithTop, hb]

private theorem commute_from_generator {R V W : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    {q : QuadraticForm R V} {Q : QuadraticForm R W} (J : q →qᵢ Q)
    (r : W) (h₂ : (2 : R) = 0) (hr : ∀ v, Q.polarBilin r (J v) = 0)
    (x : CliffordAlgebra q) :
    Commute (ι Q r) (CliffordAlgebra.map J x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap s =>
    rw [AlgHom.commutes]
    exact Algebra.commute_algebraMap_right s _
  | ι v =>
    rw [CliffordAlgebra.map_apply_ι]
    apply sub_eq_zero.mp
    have hc := contract_polar Q r (ι Q (J v))
    rw [involute_of_two_eq_zero Q h₂, contractLeft_ι, hr, map_zero] at hc
    exact hc.symm
  | mul x y hx hy => rw [map_mul]; exact hx.mul_right hy
  | add x y hx hy => rw [map_add]; exact hx.add_right hy

theorem cliffordCentralizer : CliffordCentralizer.{u,v,w,i} := by
  intro R _ V _ _ W _ _ I _ _ q Q J b d r h₂ h
  classical
  let B := orderedBasis q b
  let D := orderedBasis Q d
  let f := intoWithTop I
  have hB (a : Finset I) : CliffordAlgebra.map J (B a) = D (a.map f.toEmbedding) :=
    map_orderedBasis h.coe_basis a
  have hf : Function.Injective (fun a : Finset I => a.map f.toEmbedding) :=
    Finset.map_injective _
  refine ⟨?_, fun a => ⟨?_, ?_⟩⟩
  · have hlin := (D.linearIndependent.comp _ hf)
    have hm : LinearIndependent R ((CliffordAlgebra.map J).toLinearMap ∘ B) := by
      convert hlin using 1
      funext a
      exact hB a
    have hconstr : B.constr R ((CliffordAlgebra.map J).toLinearMap ∘ B) =
        (CliffordAlgebra.map J).toLinearMap := by
      apply B.ext
      intro a
      rw [Basis.constr_basis]
      rfl
    change Function.Injective (CliffordAlgebra.map J).toLinearMap
    rw [← hconstr]
    exact B.injective_constr_of_linearIndependent hm
  · intro ha
    have hz : contractLeft (d.coord (⊤ : WithTop I)) a = 0 := by
      rw [← h.polar_coord, contract_polar, involute_of_two_eq_zero Q h₂, ha.eq, sub_self]
    have hcoef (s : Finset (WithTop I)) (ht : (⊤ : WithTop I) ∈ s) : D.coord s a = 0 :=
      contract_coord Q d a ⊤ hz s ht
    have hpre (s : Finset (WithTop I)) (hs : (⊤ : WithTop I) ∉ s) :
        D s ∈ (CliffordAlgebra.map J).range := by
      let t := s.preimage f.toEmbedding (by exact f.injective.injOn)
      have ht : t.map f.toEmbedding = s := by
        ext z
        cases z using WithTop.recTopCoe with
        | top => simp [t, f, intoWithTop, hs]
        | coe z => simp [t, f, intoWithTop]
      exact ⟨B t, (hB t).trans (congrArg D ht)⟩
    have hmem : a ∈ (CliffordAlgebra.map J).range.toSubmodule := by
      rw [← D.sum_repr a]
      apply Submodule.sum_mem
      intro s _
      by_cases hs : (⊤ : WithTop I) ∈ s
      · rw [← Basis.coord_apply, hcoef s hs, zero_smul]
        exact Submodule.zero_mem _
      · exact Submodule.smul_mem _ _ (hpre s hs)
    exact hmem
  · rintro ⟨x, rfl⟩
    apply commute_from_generator J (J r) h₂ _ x
    have hl : (Q.polarBilin (J r)).comp J.toLinearMap = 0 := by
      apply b.ext
      intro i
      change Q.polarBilin (J r) (J (b i)) = 0
      rw [h.polar_coord, ← h.coe_basis i]
      simp
    exact fun v => LinearMap.congr_fun hl v

section IntrinsicPoints

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
  {W : Type w} [AddCommGroup W] [Module R W] {I : Type i} [LinearOrder I] [Fintype I]
  {q : QuadraticForm R V} {Q : QuadraticForm R W} {J : q →qᵢ Q}
  {b : Basis I R V} {d : Basis (WithTop I) R W} {r : V}

open private map_isometry_reverse map_isometry_evenOdd
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SplitSpin

private theorem grade_coord {X : Type*} [AddCommGroup X] [Module R X]
    {L : Type*} [LinearOrder L] (P : QuadraticForm R X) (c : Basis L R X)
    {k : ZMod 2} {x : CliffordAlgebra P} (hx : x ∈ evenOdd P k)
    {s : Finset L} (hs : (s.card : ZMod 2) ≠ k) :
    (orderedBasis P c).coord s x = 0 := by
  classical
  rw [CliffordModel.parity_span P c k] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨t, ht, rfl⟩ := hy
    rw [← orderedBasis_apply P c, Basis.coord_apply, Basis.repr_self]
    exact Finsupp.single_eq_of_ne (fun h => hs (h.symm ▸ ht))
  | zero => exact map_zero _
  | add _ _ _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul _ _ _ hx => rw [map_smul, hx, smul_zero]

private theorem vector_of_scalar_commutators (h₂ : (2 : R) = 0)
    (j : WithTop I)
    (hp : ∀ a : WithTop I, a ≠ j → ∃ v : V, Q.polarBilin (J v) = d.coord a)
    (c : CliffordAlgebra Q) (hc : c ∈ evenOdd Q 1)
    (hcomm : ∀ v : V, ∃ t : R, ι Q (J v) * c - c * ι Q (J v) = algebraMap R _ t) :
    c ∈ LinearMap.range (ι Q) := by
  classical
  let D := orderedBasis Q d
  have hz (s : Finset (WithTop I)) (hs : s.card ≠ 1) : D.coord s c = 0 := by
    by_cases he : s = ∅
    · subst s
      exact grade_coord Q d hc (by simp)
    have hi : ∃ i ∈ s, i ≠ j := by
      by_contra! h
      obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr he
      have hs' : s = {j} := Finset.eq_singleton_iff_unique_mem.mpr ⟨h i hi ▸ hi, h⟩
      exact hs (by simp [hs'])
    obtain ⟨i, hi, hij⟩ := hi
    obtain ⟨v, hv⟩ := hp i hij
    obtain ⟨t, ht⟩ := hcomm v
    have hcontract : contractLeft (d.coord i) (c - t • ι Q (d i)) = 0 := by
      rw [map_sub, map_smul, contractLeft_ι, ← hv, contract_polar,
        involute_of_two_eq_zero Q h₂, ht, hv]
      simp [Algebra.smul_def]
    have hzero := contract_coord Q d _ i hcontract s hi
    have hne : s ≠ {i} := fun e => hs (e ▸ Finset.card_singleton i)
    simpa [map_sub, map_smul, ← orderedBasis_singleton Q d i, Basis.coord_apply,
      Basis.repr_self, Finsupp.single_eq_of_ne hne] using hzero
  rw [← D.sum_repr c]
  apply Submodule.sum_mem
  intro s _
  by_cases h : s.card = 1
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h
    apply Submodule.smul_mem
    exact ⟨d a, (orderedBasis_singleton Q d a).symm⟩
  · rw [← Basis.coord_apply, hz s h, zero_smul]
    exact Submodule.zero_mem _

private theorem ambient_vector_mem_hyperplane (h : AdaptedBasis q Q J b d r)
    (w : W) (hw : Q.polarBilin (J r) w = 0) :
    w ∈ LinearMap.range J.toLinearMap := by
  classical
  rw [h.polar_coord] at hw
  rw [← d.sum_repr w]
  apply Submodule.sum_mem
  intro i _
  cases i using WithTop.recTopCoe with
  | top =>
    rw [← Basis.coord_apply, hw, zero_smul]
    exact Submodule.zero_mem _
  | coe i =>
    apply Submodule.smul_mem
    exact ⟨b i, (h.coe_basis i).symm⟩

private theorem polar_zero_on_hyperplane (h : AdaptedBasis q Q J b d r) (v : V) :
    Q.polarBilin (J r) (J v) = 0 := by
  have hl : (Q.polarBilin (J r)).comp J.toLinearMap = 0 := by
    apply b.ext
    intro i
    change Q.polarBilin (J r) (J (b i)) = 0
    rw [h.polar_coord, ← h.coe_basis i]
    simp
  exact LinearMap.congr_fun hl v

private theorem commute_unit_inverse {A : Type*} [Monoid A] (r : A) (a : Aˣ)
    (h : Commute r a.val) : Commute r (a⁻¹ : Aˣ).val := by
  exact h.units_inv_right

private theorem reverse_eq_inverse {X : Type*} [AddCommGroup X] [Module R X]
    (P : QuadraticForm R X) (a : (CliffordAlgebra P)ˣ) (hn : reverse a.val * a.val = 1) :
    reverse a.val = (a⁻¹ : (CliffordAlgebra P)ˣ).val := by
  calc
    reverse a.val = (reverse a.val * a.val) * ↑a⁻¹ := by simp [mul_assoc]
    _ = _ := by rw [hn, one_mul]

private theorem forward_normalizes
    (h₂ : (2 : R) = 0)
    (j : I) (hp : ∀ a : WithTop I, a ≠ (j : WithTop I) →
      ∃ v : V, Q.polarBilin (J v) = d.coord a)
    (a : (CliffordAlgebra q)ˣ) (he : a.val ∈ evenOdd q 0)
    (hi : (a⁻¹ : (CliffordAlgebra q)ˣ).val ∈ evenOdd q 0)
    (hb : Set.MapsTo (fun x : CliffordAlgebra q => (↑a⁻¹ : CliffordAlgebra q) * x * a)
      (LinearMap.range (ι q)) (LinearMap.range (ι q))) (w : W) :
    let A := Units.map (CliffordAlgebra.map J).toMonoidHom a
    A.val * ι Q w * ↑A⁻¹ ∈ LinearMap.range (ι Q) := by
  classical
  dsimp only
  let f := CliffordAlgebra.map J
  let A := Units.map f.toMonoidHom a
  let c := A.val * ι Q w * ↑A⁻¹
  change c ∈ _
  apply vector_of_scalar_commutators (J := J) (d := d) h₂ (j : WithTop I) hp c
  · have he' : A.val ∈ evenOdd Q 0 := map_isometry_evenOdd J he
    have hi' : (A⁻¹ : (CliffordAlgebra Q)ˣ).val ∈ evenOdd Q 0 := map_isometry_evenOdd J hi
    have hw := SetLike.mul_mem_graded he' (ι_mem_evenOdd_one Q w)
    simpa using SetLike.mul_mem_graded hw hi'
  · intro v
    obtain ⟨v', hv'⟩ := hb (LinearMap.mem_range_self _ v)
    have hv'' : (↑A⁻¹ : CliffordAlgebra Q) * ι Q (J v) * A.val = ι Q (J v') := by
      change f (↑a⁻¹) * ι Q (J v) * f a.val = _
      simpa only [f, map_mul, map_apply_ι] using (congrArg f hv').symm
    refine ⟨Q.polarBilin (J v') w, ?_⟩
    have hcomm : ι Q (J v') * ι Q w - ι Q w * ι Q (J v') =
        algebraMap R _ (Q.polarBilin (J v') w) := by
      simpa only [involute_of_two_eq_zero Q h₂, contractLeft_ι] using
        (contract_polar Q (J v') (ι Q w)).symm
    have hcancel : A.val * ι Q (J v') * ↑A⁻¹ = ι Q (J v) := by
      rw [← hv'']
      simp [mul_assoc, ← mul_assoc A.val (↑A⁻¹ : CliffordAlgebra Q)]
    have hmult (x y : CliffordAlgebra Q) :
        (A.val * x * ↑A⁻¹) * (A.val * y * ↑A⁻¹) = A.val * (x * y) * ↑A⁻¹ := by
      simp [mul_assoc, ← mul_assoc (↑A⁻¹ : CliffordAlgebra Q) A.val]
    dsimp [c]
    rw [← hcancel, hmult, hmult, ← sub_mul, ← mul_sub, hcomm,
      ← Algebra.commutes, mul_assoc, Units.mul_inv, mul_one]

private theorem even_of_map_even (hinj : Function.Injective (CliffordAlgebra.map J))
    (x : CliffordAlgebra q) (hx : CliffordAlgebra.map J x ∈ evenOdd Q 0) :
    x ∈ evenOdd q 0 := by
  have hx' : x ∈ evenOdd q 0 ⊔ evenOdd q 1 := by
    rw [(evenOdd_isCompl (Q := q)).sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨x₀, h₀, x₁, h₁, rfl⟩ := Submodule.mem_sup.mp hx'
  have hy : CliffordAlgebra.map J x₁ ∈ evenOdd Q 0 := by
    rw [map_add] at hx
    simpa only [add_sub_cancel_left] using
      (evenOdd Q 0).sub_mem hx (map_isometry_evenOdd J h₀)
  have hz : CliffordAlgebra.map J x₁ = 0 :=
    Submodule.disjoint_def.mp (evenOdd_isCompl (Q := Q)).disjoint
      _ hy (map_isometry_evenOdd J h₁)
  rw [show x₁ = 0 from hinj (hz.trans (map_zero _).symm), add_zero]
  exact h₀

private theorem project_action (h₂ : (2 : R) = 0)
    (h : AdaptedBasis q Q J b d r) (hinj : Function.Injective (CliffordAlgebra.map J))
    (a : (CliffordAlgebra q)ˣ)
    (ha : Set.MapsTo (fun x : CliffordAlgebra Q =>
      (Units.map (CliffordAlgebra.map J).toMonoidHom a).val * x *
        ↑((Units.map (CliffordAlgebra.map J).toMonoidHom a)⁻¹))
        (LinearMap.range (ι Q)) (LinearMap.range (ι Q))) :
    Set.MapsTo (fun x : CliffordAlgebra q => a.val * x * ↑a⁻¹)
      (LinearMap.range (ι q)) (LinearMap.range (ι q)) := by
  rintro _ ⟨v, rfl⟩
  let f := CliffordAlgebra.map J
  let A := Units.map f.toMonoidHom a
  obtain ⟨w, hw⟩ := ha (LinearMap.mem_range_self _ (J v))
  change ι Q w = A.val * ι Q (J v) * ↑A⁻¹ at hw
  have hp (v : V) := polar_zero_on_hyperplane h v
  have hc : Commute (ι Q (J r)) (ι Q w) := by
    rw [hw]
    apply Commute.mul_right (Commute.mul_right ?_ ?_) ?_
    · exact commute_from_generator J (J r) h₂ hp a.val
    · simpa only [map_apply_ι] using commute_from_generator J (J r) h₂ hp (ι q v)
    · exact commute_from_generator J (J r) h₂ hp (↑a⁻¹ : CliffordAlgebra q)
  have hz := contract_polar Q (J r) (ι Q w)
  rw [involute_of_two_eq_zero Q h₂, hc.eq, sub_self, contractLeft_ι] at hz
  have hpw : Q.polarBilin (J r) w = 0 :=
    scalar_injective Q d (hz.trans (map_zero _).symm)
  obtain ⟨v', hv'⟩ := ambient_vector_mem_hyperplane h w hpw
  refine ⟨v', hinj ?_⟩
  rw [map_apply_ι, show J v' = w from hv', hw]
  simp only [map_mul, map_apply_ι, f, A]
  rfl

theorem intrinsicSpinComparison : IntrinsicSpinComparison.{u,v,w,i} := by
  intro R _ V _ _ W _ _ I _ _ q Q J b d r j h₂ h hp
  let f := CliffordAlgebra.map J
  obtain ⟨hinj, hcent⟩ := cliffordCentralizer q Q J b d r h₂ h
  have hmap (a : (CliffordAlgebra q)ˣ) :
      IsIntrinsicSpin q a ↔ IsIntrinsicSpin Q (Units.map f.toMonoidHom a) := by
    let A := Units.map f.toMonoidHom a
    have hnorm : reverse a.val * a.val = 1 ↔ reverse A.val * A.val = 1 := by
      rw [← hinj.eq_iff, map_mul, map_isometry_reverse, map_one]
      rfl
    constructor
    · rintro ⟨he, hn, hf, hb⟩
      have hi : (a⁻¹ : (CliffordAlgebra q)ˣ).val ∈ evenOdd q 0 := by
        rw [← reverse_eq_inverse q a hn, reverse_mem_evenOdd_iff]
        exact he
      refine ⟨map_isometry_evenOdd J he, hnorm.mp hn, ?_, ?_⟩
      · rintro _ ⟨w, rfl⟩
        exact forward_normalizes h₂ j hp a he hi hb w
      · rintro _ ⟨w, rfl⟩
        change (↑A⁻¹ : CliffordAlgebra Q) * ι Q w * A.val ∈ LinearMap.range (ι Q)
        simpa only [f, A, inv_inv, map_inv] using forward_normalizes h₂ j hp a⁻¹ hi
          (by simpa only [inv_inv] using he) (by simpa only [inv_inv] using hf) w
    · rintro ⟨he, hn, hf, hb⟩
      refine ⟨even_of_map_even hinj a.val he, hnorm.mpr hn, project_action h₂ h hinj a hf, ?_⟩
      simpa only [inv_inv] using project_action h₂ h hinj a⁻¹
        (by simpa only [map_inv, inv_inv] using hb)
  let toFun (a : {a : (CliffordAlgebra q)ˣ // IsIntrinsicSpin q a}) :
      {a : (CliffordAlgebra Q)ˣ // IsIntrinsicSpin Q a ∧ Commute (ι Q (J r)) a.val} :=
    ⟨Units.map f.toMonoidHom a.val, (hmap a.val).mp a.property, (hcent _).mpr ⟨a.val.val, rfl⟩⟩
  have hbij : Function.Bijective toFun := by
    constructor
    · intro a b hab
      apply Subtype.ext
      apply Units.ext
      exact hinj (congrArg (fun z => z.val.val) hab)
    · intro A
      obtain ⟨a, ha⟩ := (hcent _).mp A.property.2
      obtain ⟨a', ha'⟩ := (hcent _).mp (commute_unit_inverse _ _ A.property.2)
      let t : (CliffordAlgebra q)ˣ :=
        ⟨a, a', hinj (by rw [map_mul, ha, ha', Units.mul_inv, map_one]),
          hinj (by rw [map_mul, ha, ha', Units.inv_mul, map_one])⟩
      have ht : Units.map f.toMonoidHom t = A.val := Units.ext ha
      refine ⟨⟨t, (hmap t).mpr (ht ▸ A.property.1)⟩, Subtype.ext ht⟩
  refine ⟨Equiv.ofBijective toFun hbij, fun _ => rfl, fun a v => ?_⟩
  simp only [map_mul, map_apply_ι]
  rfl

end IntrinsicPoints

section SplitModel

open SplitSpinSpecification

variable {R : Type u} [CommRing R] {n : ℕ}

private theorem ambientForm_apply (x : AmbientModule R n) :
    ambientForm R n x = (∑ i : Fin n, x (eIndex i) * x (fIndex i)) +
      x (rIndex n) * (x (rIndex n) + x ⊤) := by
  simp [ambientForm, LinearMap.BilinMap.toQuadraticMap_apply]

@[simp] private theorem extendOdd_top (x : OddModule R n) :
    extendOdd R n x ⊤ = 0 := rfl

@[simp] private theorem extendOdd_coe (x : OddModule R n) (i : OddIndex n) :
    extendOdd R n x i = x i := rfl

private theorem ambient_polar (h₂ : (2 : R) = 0) (x y : AmbientModule R n) :
    (ambientForm R n).polarBilin x y =
      (∑ i : Fin n, (x (eIndex i) * y (fIndex i) + y (eIndex i) * x (fIndex i))) +
        (x (rIndex n) * y ⊤ + y (rIndex n) * x ⊤) := by
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
  simp only [ambientForm_apply, Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]
  have hz : x (rIndex n) * y (rIndex n) + y (rIndex n) * x (rIndex n) = 0 := by
    rw [mul_comm (y (rIndex n)), ← two_mul, h₂, zero_mul]
  linear_combination hz

private def ambientCoordinates (R : Type u) [CommRing R] (n : ℕ) :
    AmbientModule R n ≃ₗ[R] (PairIndex (n + 1) → R) where
  toFun x := Sum.elim (Fin.cases (x (rIndex n)) (fun i => x (eIndex i)))
    (Fin.cases (x (rIndex n) + x ⊤) (fun i => x (fIndex i)))
  invFun x := WithTop.recTopCoe (x (Sum.inr 0) - x (Sum.inl 0)) <|
    WithTop.recTopCoe (x (Sum.inl 0)) fun i => Sum.elim
      (fun j : Fin n => x (Sum.inl j.succ)) (fun j : Fin n => x (Sum.inr j.succ)) (ofLex i)
  left_inv x := by
    funext i
    cases i using WithTop.recTopCoe with
    | top => exact add_sub_cancel_left _ _
    | coe i =>
      cases i using WithTop.recTopCoe with
      | top => rfl
      | coe i =>
        obtain ⟨a, rfl⟩ := toLex.surjective i
        cases a <;> rfl
  right_inv x := by
    funext i
    cases i with
    | inl i => cases i using Fin.cases <;> rfl
    | inr i =>
      cases i using Fin.cases with
      | zero => exact add_sub_cancel _ _
      | succ i => rfl
  map_add' x y := by
    funext i
    cases i with
    | inl i => cases i using Fin.cases <;> rfl
    | inr i =>
      cases i using Fin.cases with
      | zero =>
        change (x (rIndex n) + y (rIndex n)) + (x ⊤ + y ⊤) =
          (x (rIndex n) + x ⊤) + (y (rIndex n) + y ⊤)
        abel
      | succ i => rfl
  map_smul' t x := by
    funext i
    cases i with
    | inl i => cases i using Fin.cases <;> rfl
    | inr i =>
      cases i using Fin.cases with
      | zero => exact (mul_add _ _ _).symm
      | succ i => rfl

private theorem ambientCoordinates_norm (x : AmbientModule R n) :
    ambientForm R n x = hyperbolicNorm (ambientCoordinates R n x) := by
  rw [ambientForm_apply, hyperbolicNorm, dotProduct, Fin.sum_univ_succ]
  exact add_comm _ _

private theorem inclusion_apply (x : OddModule R n) : inclusion R n x = extendOdd R n x := rfl

private theorem polar_restrict (x y : OddModule R n) :
    (oddForm R n).polarBilin x y =
      (ambientForm R n).polarBilin (inclusion R n x) (inclusion R n y) := by
  change ((ambientForm R n).comp (extendOdd R n)).polarBilin x y = _
  rw [QuadraticMap.polarBilin_comp]
  rfl

private theorem coordinate_basis (i : AmbientIndex n) :
    (Pi.basisFun R (AmbientIndex n)).coord i = LinearMap.proj i := by
  ext x
  simp [Basis.coord_apply, Pi.basisFun_repr]

private theorem split_model_data (h₂ : (2 : R) = 0) :
    AdaptedBasis (oddForm R n) (ambientForm R n) (inclusion R n)
      (Pi.basisFun R (OddIndex n)) (Pi.basisFun R (AmbientIndex n)) (radicalVector R n) ∧
    (∀ a : AmbientIndex n, a ≠ rIndex n →
      ∃ v : OddModule R n, (ambientForm R n).polarBilin (inclusion R n v) =
        (Pi.basisFun R (AmbientIndex n)).coord a) := by
  classical
  have hsingle (i : OddIndex n) :
      extendOdd R n (Pi.single i 1) = Pi.single (i : AmbientIndex n) 1 := by
    funext j
    cases j using WithTop.recTopCoe with
    | top => simp
    | coe j => simp [Pi.single_apply]
  have hr : (ambientForm R n).polarBilin (inclusion R n (radicalVector R n)) =
      (Pi.basisFun R (AmbientIndex n)).coord ⊤ := by
    rw [coordinate_basis, inclusion_apply, hsingle]
    apply LinearMap.ext
    intro x
    rw [ambient_polar h₂]
    simp [Pi.single_apply, eIndex, fIndex, rIndex]
  refine ⟨⟨fun i => ?_, hr⟩, ?_⟩
  · simpa [Pi.basisFun_apply, inclusion_apply] using (hsingle i).symm
  · intro a ha
    cases a using WithTop.recTopCoe with
    | top => exact ⟨radicalVector R n, hr⟩
    | coe a =>
      cases a using WithTop.recTopCoe with
      | top => exact (ha rfl).elim
      | coe a =>
        let a' : PairIndex n := ofLex a
        change ∃ v : OddModule R n, (ambientForm R n).polarBilin (inclusion R n v) =
          (Pi.basisFun R (AmbientIndex n)).coord (↑(↑(toLex a') : OddIndex n))
        cases a' with
        | inl i =>
          refine ⟨Pi.single (↑(toLex (Sum.inr i) : Lex (PairIndex n))) 1, ?_⟩
          rw [coordinate_basis, inclusion_apply, hsingle]
          apply LinearMap.ext
          intro x
          rw [ambient_polar h₂]
          simp [Pi.single_apply, eIndex, fIndex, rIndex]
        | inr i =>
          refine ⟨Pi.single (↑(toLex (Sum.inl i) : Lex (PairIndex n))) 1, ?_⟩
          rw [coordinate_basis, inclusion_apply, hsingle]
          apply LinearMap.ext
          intro x
          rw [ambient_polar h₂]
          simp [Pi.single_apply, eIndex, fIndex, rIndex]

theorem splitHyperplane : SplitHyperplane.{u} := by
  intro R _ n h₂
  classical
  obtain ⟨h, hp⟩ := split_model_data (R := R) (n := n) h₂
  refine ⟨⟨ambientCoordinates R n, ambientCoordinates_norm, fun a => ⟨rfl, ?_⟩⟩, h, hp, ?_, ?_⟩
  · change a ⊤ + 0 = a ⊤
    exact add_zero _
  · change ambientForm R n (extendOdd R n (radicalVector R n)) = 1
    rw [ambientForm_apply]
    simp [Pi.single_apply, eIndex, fIndex, rIndex]
  · ext v
    constructor
    · intro hv
      refine Submodule.mem_span_singleton.mpr ⟨v ⊤, ?_⟩
      funext i
      cases i using WithTop.recTopCoe with
      | top => simp
      | coe i =>
        have hi : (↑(↑i : OddIndex n) : AmbientIndex n) ≠ rIndex n := by simp [rIndex]
        obtain ⟨w, hw⟩ := hp _ hi
        have hzero : (ambientForm R n).polarBilin (inclusion R n w) (inclusion R n v) = 0 := by
          rw [← polar_restrict, QuadraticMap.polarBilin_apply_apply,
            QuadraticMap.polar_comm, ← QuadraticMap.polarBilin_apply_apply]
          exact LinearMap.congr_fun (LinearMap.mem_ker.mp hv) w
        rw [hw, coordinate_basis] at hzero
        simpa [Pi.single_apply, inclusion_apply] using hzero.symm
    · intro hv
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
      apply LinearMap.mem_ker.mpr
      apply LinearMap.ext
      intro w
      simp only [map_smul, LinearMap.smul_apply, LinearMap.zero_apply, smul_eq_mul]
      have hzero : (oddForm R n).polarBilin (radicalVector R n) w = 0 := by
        exact (polar_restrict _ _).trans (polar_zero_on_hyperplane h w)
      rw [hzero, mul_zero]

theorem splitSpinPoints : SplitSpinPoints.{u} := by
  intro R _ n h₂
  obtain ⟨h, hp⟩ := split_model_data (R := R) (n := n) h₂
  exact intrinsicSpinComparison _ _ _ _ _ _ ⊤ h₂ h hp

end SplitModel

section Schemes

open AlgebraicGeometry CategoryTheory Opposite SpinSpecification
open scoped TensorProduct CategoryTheory.MonObj
open private coordinateObject algebraRepresentation spinUnitPoints
  spinUnitPoints_represents schemePoints_onSpec specPointsMulEquiv
  changeModule_coord changeCoefficients_apply changeCoefficients_vector changeModule
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinFunctor

variable {k : Type u} [Field k] {W : Type u} [AddCommGroup W] [Module k W]
  {I : Type u} [LinearOrder I] [Fintype I]
  (Q : QuadraticForm k W) (b : Basis I k W) (r : W)

private def markedClifford (S : Type u) [CommRing S] [Algebra k S] : ScalarClifford Q S :=
  vectors Q S (1 ⊗ₜ[k] r)

private def stabilizerSubgroup (S : Type u) [CommRing S] [Algebra k S] :
    Subgroup (SpinFunctor.Spin Q S b) where
  carrier := {a | Commute (markedClifford Q r S) a.val.val}
  one_mem' := Commute.one_right _
  mul_mem' hg hh := hg.mul_right hh
  inv_mem' ha := ha.units_inv_right

private theorem markedClifford_map {S T : Type u} [CommRing S] [CommRing T]
    [Algebra k S] [Algebra k T] (f : S →ₐ[k] T) :
    SpinFunctor.changeCoefficients Q f (markedClifford Q r S) = markedClifford Q r T := by
  unfold markedClifford
  rw [changeCoefficients_vector]
  simp [changeModule]

private def stabilizerMap {S T : Type u} [CommRing S] [CommRing T]
    [Algebra k S] [Algebra k T] (f : S →ₐ[k] T) :
    stabilizerSubgroup Q b r S →* stabilizerSubgroup Q b r T :=
  ((SpinFunctor.map Q b f).comp (stabilizerSubgroup Q b r S).subtype).codRestrict
    (stabilizerSubgroup Q b r T) fun a => by
      have h := a.property
      change Commute (markedClifford Q r S) a.val.val.val at h
      change Commute (markedClifford Q r T) (SpinFunctor.changeCoefficients Q f a.val.val.val)
      rw [← markedClifford_map Q r f]
      exact h.map (SpinFunctor.changeCoefficients Q f)

private def stabilizerFunctor : ((CommAlgCat.{u} k)ᵒᵖ)ᵒᵖ ⥤ GrpCat.{u} where
  obj S := GrpCat.of (stabilizerSubgroup Q b r S.unop.unop)
  map f := GrpCat.ofHom (stabilizerMap Q b r f.unop.unop.hom)
  map_id S := by
    apply GrpCat.ext
    intro a
    exact Subtype.ext (SpinFunctor.map_id Q b a.val)
  map_comp f g := by
    apply GrpCat.ext
    intro a
    exact Subtype.ext (SpinFunctor.map_comp Q b f.unop.unop.hom g.unop.unop.hom a.val)

private abbrev SpinRing := SpinFunctor.CoordinateRing Q b

private def commutator {S : Type u} [CommRing S] [Algebra k S]
    (a : SpinFunctor.Spin Q S b) : ScalarClifford Q S :=
  markedClifford Q r S * a.val.val - a.val.val * markedClifford Q r S

private theorem commutator_map {S T : Type u} [CommRing S] [CommRing T]
    [Algebra k S] [Algebra k T] (f : S →ₐ[k] T) (a : SpinFunctor.Spin Q S b) :
    commutator Q b r (SpinFunctor.map Q b f a) =
      SpinFunctor.changeCoefficients Q f (commutator Q b r a) := by
  unfold commutator
  change _ * SpinFunctor.changeCoefficients Q f a.val.val -
      SpinFunctor.changeCoefficients Q f a.val.val * _ = _
  rw [map_sub, map_mul, map_mul, markedClifford_map]

private def equation (s : Finset I) : SpinRing Q b :=
  ((orderedBasis Q b).baseChange (SpinRing Q b)).coord s
    (commutator Q b r (SpinFunctor.pointEquiv Q b (SpinRing Q b) (AlgHom.id k _)))

private def stabilizerIdeal : Ideal (SpinRing Q b) :=
  Ideal.span (Set.range (equation Q b r))

private abbrev StabilizerRing := SpinRing Q b ⧸ stabilizerIdeal Q b r

private abbrev stabilizerQuotient : SpinRing Q b →ₐ[k] StabilizerRing Q b r :=
  Ideal.Quotient.mkₐ k (stabilizerIdeal Q b r)

private theorem stabilizer_equations {S : Type u} [CommRing S] [Algebra k S]
    (f : SpinRing Q b →ₐ[k] S) :
    SpinFunctor.pointEquiv Q b S f ∈ stabilizerSubgroup Q b r S ↔
      ∀ a ∈ stabilizerIdeal Q b r, f a = 0 := by
  change Commute _ _ ↔ _
  have he (s : Finset I) : f (equation Q b r s) =
      ((orderedBasis Q b).baseChange S).coord s
        (commutator Q b r (SpinFunctor.pointEquiv Q b S f)) := by
    rw [equation, ← changeModule_coord, ← changeCoefficients_apply,
      ← commutator_map, ← SpinFunctor.pointEquiv_natural, AlgHom.comp_id]
  change (_ * _ = _ * _) ↔ _
  rw [← sub_eq_zero]
  change commutator Q b r (SpinFunctor.pointEquiv Q b S f) = 0 ↔ _
  rw [← ((orderedBasis Q b).baseChange S).forall_coord_eq_zero_iff]
  simp_rw [← he]
  change (∀ s, f (equation Q b r s) = 0) ↔
    stabilizerIdeal Q b r ≤ RingHom.ker f.toRingHom
  rw [stabilizerIdeal, Ideal.span_le]
  simp [Set.range_subset_iff, RingHom.mem_ker]

private def stabilizerPointEquiv (S : Type u) [CommRing S] [Algebra k S] :
    (StabilizerRing Q b r →ₐ[k] S) ≃ stabilizerSubgroup Q b r S where
  toFun f := ⟨SpinFunctor.pointEquiv Q b S (f.comp (stabilizerQuotient Q b r)),
    (stabilizer_equations Q b r _).mpr fun a ha => by
      change f (Ideal.Quotient.mk (stabilizerIdeal Q b r) a) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]⟩
  invFun a := Ideal.Quotient.liftₐ (stabilizerIdeal Q b r)
    ((SpinFunctor.pointEquiv Q b S).symm a.val)
    ((stabilizer_equations Q b r _).mp (by simpa only [Equiv.apply_symm_apply] using a.property))
  left_inv f := by
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective k (stabilizerIdeal Q b r) x
    change (((SpinFunctor.pointEquiv Q b S).symm
      (SpinFunctor.pointEquiv Q b S (f.comp (stabilizerQuotient Q b r)))) x) = _
    rw [Equiv.symm_apply_apply]
    rfl
  right_inv a := by
    apply Subtype.ext
    change SpinFunctor.pointEquiv Q b S ((Ideal.Quotient.liftₐ _ _ _).comp _) = a.val
    rw [Ideal.Quotient.liftₐ_comp, Equiv.apply_symm_apply]

private abbrev stabObject : (CommAlgCat.{u} k)ᵒᵖ :=
  op (CommAlgCat.of k (StabilizerRing Q b r))

private def stabRepresentation :
    (stabilizerFunctor Q b r ⋙ forget _).RepresentableBy (stabObject Q b r) where
  homEquiv {S} :=
    { toFun := fun f => stabilizerPointEquiv Q b r S.unop f.unop.hom
      invFun := fun x => (CommAlgCat.ofHom ((stabilizerPointEquiv Q b r S.unop).symm x)).op
      left_inv := by intro f; simp
      right_inv := by intro t; exact (stabilizerPointEquiv Q b r S.unop).apply_symm_apply t }
  homEquiv_comp f g := Subtype.ext (SpinFunctor.pointEquiv_natural Q b f.unop.hom
    (g.unop.hom.comp (stabilizerQuotient Q b r)))

local instance stabGroup : GrpObj (stabObject Q b r) :=
  GrpObj.ofRepresentableBy _ _ (stabRepresentation Q b r)

local instance ambGroup : GrpObj (coordinateObject Q b) :=
  GrpObj.ofRepresentableBy _ _ (algebraRepresentation Q b)

local instance : (algSpec (CommRingCat.of k)).Braided := AlgebraicGeometry.braidedAlgSpec

private def subfunctorInclusion : stabilizerFunctor Q b r ⟶ SpinFunctor.pointsFunctor Q b where
  app S := GrpCat.ofHom (stabilizerSubgroup Q b r S.unop.unop).subtype
  naturality := by intros; rfl

private def stabAlgebraTransformation :
    yonedaGrp.obj (Grp.mk (stabObject Q b r)) ⟶ yonedaGrp.obj (Grp.mk (coordinateObject Q b)) :=
  (yonedaGrpObjIsoOfRepresentableBy _ _ (stabRepresentation Q b r)).hom ≫
    subfunctorInclusion Q b r ≫
      (yonedaGrpObjIsoOfRepresentableBy _ _ (algebraRepresentation Q b)).inv

private def stabAlgebraInclusion : Grp.mk (stabObject Q b r) ⟶ Grp.mk (coordinateObject Q b) :=
  yonedaGrpFullyFaithful.preimage (stabAlgebraTransformation Q b r)

private theorem stabAlgebraInclusion_points {S : CommAlgCat.{u} k} (p : op S ⟶ stabObject Q b r) :
    SpinFunctor.pointEquiv Q b S (p ≫ (stabAlgebraInclusion Q b r).hom.hom).unop.hom =
      (stabilizerPointEquiv Q b r S p.unop.hom).val := by
  let e := ((yonedaGrpObjIsoOfRepresentableBy _ _ (algebraRepresentation Q b)).app
    (op (op S))).groupIsoToMulEquiv
  have h := congrArg (fun α => (α.app (op (op S))).hom p)
    (yonedaGrpFullyFaithful.map_preimage (stabAlgebraTransformation Q b r))
  change p ≫ (stabAlgebraInclusion Q b r).hom.hom =
    e.symm (stabilizerPointEquiv Q b r S p.unop.hom).val at h
  exact (congrArg e h).trans (e.apply_symm_apply _)

private theorem stabAlgebraInclusion_hom :
    (stabAlgebraInclusion Q b r).hom.hom.unop.hom = stabilizerQuotient Q b r := by
  let S := (stabObject Q b r).unop
  have h := stabAlgebraInclusion_points Q b r (𝟙 (stabObject Q b r))
  rw [Category.id_comp] at h
  apply (SpinFunctor.pointEquiv Q b S).injective
  exact h

private def stabScheme : GroupScheme k :=
  ((algSpec (CommRingCat.of k)).mapGrp).obj (Grp.mk (stabObject Q b r))

private def stabInclusion : stabScheme Q b r ⟶ SpinFunctor.spinScheme Q b :=
  ((algSpec (CommRingCat.of k)).mapGrp).map (stabAlgebraInclusion Q b r)

private theorem stabInclusion_closed :
    IsClosedImmersion (stabInclusion Q b r).hom.hom.left := by
  change IsClosedImmersion (Spec.map (CommRingCat.ofHom
    (stabAlgebraInclusion Q b r).hom.hom.unop.hom.toRingHom))
  rw [stabAlgebraInclusion_hom]
  apply IsClosedImmersion.spec_of_surjective
  exact Ideal.Quotient.mkₐ_surjective k _

private theorem stabScheme_points (S : CommAlgCat.{u} k)
    (a : SchemePoints (SpinFunctor.spinScheme Q b) S) :
    Commute (markedClifford Q r S) (spinUnitPoints Q b S a).val ↔
      ∃! p : SchemePoints (stabScheme Q b r) S, p ≫ (stabInclusion Q b r).hom.hom = a := by
  let F := algSpec (CommRingCat.of k)
  obtain ⟨g, rfl⟩ := (specPointsMulEquiv (X := coordinateObject Q b) S).surjective a
  change Commute (markedClifford Q r S) (SpinFunctor.schemePoints Q b S (F.map g)).val.val ↔ _
  rw [schemePoints_onSpec]
  constructor
  · intro h
    let t : stabilizerSubgroup Q b r S :=
      ⟨SpinFunctor.pointEquiv Q b S g.unop.hom, h⟩
    let p : op S ⟶ stabObject Q b r :=
      (CommAlgCat.ofHom ((stabilizerPointEquiv Q b r S).symm t)).op
    have hp : p ≫ (stabAlgebraInclusion Q b r).hom.hom = g := by
      apply Quiver.Hom.unop_inj
      apply CommAlgCat.hom_ext
      apply (SpinFunctor.pointEquiv Q b S).injective
      rw [stabAlgebraInclusion_points]
      exact congrArg Subtype.val ((stabilizerPointEquiv Q b r S).apply_symm_apply t)
    refine ⟨F.map p, ?_, ?_⟩
    · change F.map p ≫ F.map _ = F.map g
      rw [← F.map_comp, hp]
    · intro p' hp'
      haveI : IsClosedImmersion (stabInclusion Q b r).hom.hom.left := stabInclusion_closed Q b r
      haveI : Mono (stabInclusion Q b r).hom.hom := Over.mono_of_mono_left _
      apply (cancel_mono (stabInclusion Q b r).hom.hom).mp
      exact hp'.trans (by change F.map g = F.map p ≫ F.map _; rw [← F.map_comp, hp])
  · rintro ⟨p, hp, _⟩
    obtain ⟨z, rfl⟩ := (specPointsMulEquiv (X := stabObject Q b r) S).surjective p
    change F.map z ≫ F.map _ = F.map g at hp
    rw [← F.map_comp] at hp
    have hzg := (algSpec.fullyFaithful (R := CommRingCat.of k)).map_injective hp
    rw [← hzg, stabAlgebraInclusion_points]
    exact (stabilizerPointEquiv Q b r S z.unop.hom).property

private theorem stabScheme_affine : IsAffine (stabScheme Q b r).X.left := by
  change IsAffine (Spec (CommRingCat.of (StabilizerRing Q b r)))
  infer_instance

private theorem stabScheme_finitePresentation :
    LocallyOfFinitePresentation (stabScheme Q b r).X.hom := by
  change LocallyOfFinitePresentation
    (Spec.map (CommRingCat.ofHom (algebraMap k (StabilizerRing Q b r))))
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
  change RingHom.FinitePresentation (algebraMap k (StabilizerRing Q b r))
  rw [RingHom.finitePresentation_algebraMap]
  apply Algebra.FinitePresentation.quotient
  exact Submodule.fg_span (Set.finite_range _)

include b in
private theorem representedStabilizer :
    ∃ (G H : GroupScheme k) (i : H ⟶ G)
        (e : ∀ S, SchemePoints G S →* (ScalarClifford Q S)ˣ),
      IsSpinPointRepresentation Q G e ∧
      IsAffine H.X.left ∧ LocallyOfFinitePresentation H.X.hom ∧
      IsClosedImmersion i.hom.hom.left ∧
      ∀ (S : CommAlgCat k) (a : SchemePoints G S),
        Commute (vectors Q S (1 ⊗ₜ[k] r)) (e S a).val ↔
          ∃! p : SchemePoints H S, p ≫ i.hom.hom = a := by
  exact ⟨SpinFunctor.spinScheme Q b, stabScheme Q b r, stabInclusion Q b r,
    spinUnitPoints Q b, spinUnitPoints_represents Q b, stabScheme_affine Q b r,
    stabScheme_finitePresentation Q b r, stabInclusion_closed Q b r, stabScheme_points Q b r⟩

theorem schemeStabilizer : SchemeStabilizer.{u} := by
  intro k _ n _ _
  exact representedStabilizer (ambientForm k n)
    ((Pi.basisFun k (AmbientIndex n)).reindex (Equiv.ulift.{u}.symm))
    (inclusion k n (radicalVector k n))

end Schemes

section GeometricPoints

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  (q : QuadraticForm K V)

private def unitVector (w : V) (hw : q w ≠ 0) : (CliffordAlgebra q)ˣ :=
  (isUnit_ι_of_isUnit q (isUnit_iff_ne_zero.mpr hw)).unit

private theorem unitVector_val (w : V) (hw : q w ≠ 0) :
    (unitVector q w hw).val = ι q w :=
  (isUnit_ι_of_isUnit q (isUnit_iff_ne_zero.mpr hw)).unit_spec

private theorem unitVector_inv (w : V) (hw : q w ≠ 0) :
    ((unitVector q w hw)⁻¹ : (CliffordAlgebra q)ˣ).val = (q w)⁻¹ • ι q w := by
  have hmul : (unitVector q w hw).val * ((q w)⁻¹ • ι q w) = 1 := by
    rw [unitVector_val, mul_smul_comm, ι_sq_scalar, Algebra.smul_def, ← map_mul,
      inv_mul_cancel₀ hw, map_one]
  calc
    _ = ((unitVector q w hw)⁻¹ : (CliffordAlgebra q)ˣ).val *
        ((unitVector q w hw).val * ((q w)⁻¹ • ι q w)) := by rw [hmul, mul_one]
    _ = _ := by rw [← mul_assoc, Units.inv_mul, one_mul]

private theorem charTwo_neg (h₂ : (2 : K) = 0) (w : V) : -w = w :=
  neg_eq_iff_add_eq_zero.mpr (by rw [← two_smul K, h₂, zero_smul])

private theorem unitVector_conjugate (h₂ : (2 : K) = 0) (w : V) (hw : q w ≠ 0) (z : V) :
    (unitVector q w hw).val * ι q z * ↑(unitVector q w hw)⁻¹ =
      ι q (z - (q.polarBilin w z / q w) • w) := by
  rw [unitVector_inv, unitVector_val, mul_smul_comm, ι_mul_ι_mul_ι, ← map_smul]
  congr 1
  rw [smul_sub, smul_smul, smul_smul, inv_mul_cancel₀ hw, one_smul,
    mul_comm (q w)⁻¹, ← div_eq_mul_inv, sub_eq_add_neg, sub_eq_add_neg,
    charTwo_neg h₂, charTwo_neg h₂, add_comm]
  rfl

private theorem unit_conjugate_mul {C : Type*} [Monoid C] (A B : Cˣ) (x : C) :
    (A * B).val * x * ↑(A * B)⁻¹ = A.val * (B.val * x * ↑B⁻¹) * ↑A⁻¹ := by
  simp only [Units.val_mul, mul_inv_rev, mul_assoc]

private theorem word_implementer (h₂ : (2 : K) = 0)
    (l : List V) (hl : ∀ w ∈ l, q w ≠ 0) :
    ∃ a : (CliffordAlgebra q)ˣ,
      a.val ∈ evenOdd q (l.length : ZMod 2) ∧
      reverse a.val * a.val = algebraMap K _ (l.map q).prod ∧
      ∀ x, a.val * ι q x * ↑a⁻¹ =
        ι q (l.foldr (fun w z => z - (q.polarBilin w z / q w) • w) x) := by
  induction l with
  | nil =>
    exact ⟨1, by simpa using SetLike.one_mem_graded (A := evenOdd q), by simp, by simp⟩
  | cons w l ih =>
    have hw := hl w (List.mem_cons_self ..)
    obtain ⟨a, ha, hn, hact⟩ := ih (fun v hv => hl v (List.mem_cons_of_mem _ hv))
    let A := unitVector q w hw
    refine ⟨A * a, ?_, ?_, ?_⟩
    · have he : A.val ∈ evenOdd q 1 := by
        rw [show A.val = ι q w from unitVector_val q w hw]
        exact ι_mem_evenOdd_one q _
      simpa [List.length_cons, add_comm] using SetLike.mul_mem_graded he ha
    · change reverse (A.val * a.val) * (A.val * a.val) = _
      rw [show A.val = ι q w from unitVector_val q w hw, reverse.map_mul, reverse_ι, mul_assoc, ← mul_assoc (ι q w),
        ι_sq_scalar]
      rw [← mul_assoc, ← Algebra.commutes (q w) (reverse a.val),
        mul_assoc, hn, ← map_mul, List.map_cons, List.prod_cons]
    · intro x
      rw [unit_conjugate_mul, hact, List.foldr_cons]
      exact unitVector_conjugate q h₂ w hw _

private theorem scalar_times_conjugate (s : Kˣ) (a : (CliffordAlgebra q)ˣ) (x : CliffordAlgebra q) :
    let u := Units.map (algebraMap K (CliffordAlgebra q)).toMonoidHom s
    (u * a).val * x * ↑(u * a)⁻¹ = a.val * x * ↑a⁻¹ := by
  dsimp only
  rw [unit_conjugate_mul]
  let u := Units.map (algebraMap K (CliffordAlgebra q)).toMonoidHom s
  change u.val * (a.val * x * ↑a⁻¹) * ↑u⁻¹ = _
  rw [show u.val = algebraMap K _ (s : K) from rfl, Algebra.commutes,
    ← show u.val = algebraMap K _ (s : K) from rfl, mul_assoc, Units.mul_inv, mul_one]

private theorem norm_one_implementer [IsAlgClosed K] (h₂ : (2 : K) = 0)
    (l : List V) (hl : ∀ w ∈ l, q w ≠ 0) (hEven : (l.length : ZMod 2) = 0)
    (g : V ≃ₗ[K] V)
    (hg : ∀ x, g x = l.foldr (fun w z => z - (q.polarBilin w z / q w) • w) x) :
    ∃ a : (CliffordAlgebra q)ˣ, IsIntrinsicSpin q a ∧
      ∀ x, a.val * ι q x * ↑a⁻¹ = ι q (g x) := by
  obtain ⟨a, ha, hn, hact⟩ := word_implementer q h₂ l hl
  let c := (l.map q).prod
  have hc : c ≠ 0 := by
    apply List.prod_ne_zero
    rintro hx
    obtain ⟨w, hw, hzw⟩ := List.mem_map.mp hx
    exact hl w hw hzw
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq c⁻¹ zero_lt_two
  have ht0 : t ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide : (2 : ℕ) ≠ 0)] at ht
    exact inv_ne_zero hc ht.symm
  let s := Units.mk0 t ht0
  let u := Units.map (algebraMap K (CliffordAlgebra q)).toMonoidHom s
  let A := u * a
  have hA (x : V) : A.val * ι q x * ↑A⁻¹ = ι q (g x) := by
    rw [scalar_times_conjugate, hact, hg]
  refine ⟨A, ⟨?_, ?_, ?_, ?_⟩, hA⟩
  · change algebraMap K _ t * a.val ∈ evenOdd q 0
    rw [← Algebra.smul_def]
    exact (evenOdd q 0).smul_mem _ (hEven ▸ ha)
  · change reverse (algebraMap K _ t * a.val) * (algebraMap K _ t * a.val) = 1
    rw [reverse.map_mul, reverse.commutes, mul_assoc, ← mul_assoc (algebraMap K _ t),
      ← map_mul, ← pow_two, ht, Algebra.commutes, ← mul_assoc,
      hn, ← map_mul, mul_inv_cancel₀ hc, map_one]
  · rintro _ ⟨x, rfl⟩
    exact ⟨g x, (hA x).symm⟩
  · rintro _ ⟨x, rfl⟩
    refine ⟨g.symm x, ?_⟩
    have h := hA (g.symm x)
    rw [g.apply_symm_apply] at h
    rw [← h]
    simp [mul_assoc, ← mul_assoc (↑A⁻¹ : CliffordAlgebra q)]

private theorem geometricIntrinsicRestriction (K : Type u) [Field K] [IsAlgClosed K]
    (n : ℕ) (h₂ : (2 : K) = 0) (g : OddModule K n ≃ₗ[K] OddModule K n)
    (hg : ∀ x, oddForm K n (g x) = oddForm K n x) :
    ∃ a : (CliffordAlgebra (oddForm K n))ˣ, IsIntrinsicSpin (oddForm K n) a ∧
      ∀ x, a.val * ι (oddForm K n) x * ↑a⁻¹ = ι (oddForm K n) (g x) := by
  classical
  let q := oddForm K n
  let r := radicalVector K n
  have geom := splitHyperplane K n h₂
  have hr : q r = 1 := geom.2.2.2.1
  have hrad : LinearMap.ker q.polarBilin = K ∙ r := geom.2.2.2.2
  obtain ⟨l, hl, hg'⟩ :=
    SpinOrthogonalWords.orthogonalWords q (Or.inr ⟨r, by simp [hr], hrad⟩) g hg
  have hzero : q.polarBilin r = 0 := by
    apply LinearMap.mem_ker.mp
    rw [hrad]
    exact Submodule.mem_span_singleton_self r
  obtain ⟨L, hL, hpar, hword⟩ :
      ∃ L : List (OddModule K n), (∀ w ∈ L, q w ≠ 0) ∧
        (L.length : ZMod 2) = 0 ∧
        ∀ x, g x = L.foldr (fun w z => z - (q.polarBilin w z / q w) • w) x := by
    by_cases he : (l.length : ZMod 2) = 0
    · exact ⟨l, hl, he, hg'⟩
    · refine ⟨r :: l, ?_, ?_, ?_⟩
      · intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · rw [hr]
          exact one_ne_zero
        · exact hl w hw
      · have h1 : (l.length : ZMod 2) = 1 := by
          have h : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
          exact (h _).resolve_left he
        simpa only [List.length_cons, Nat.cast_add, Nat.cast_one, h1] using
          (show (1 : ZMod 2) + 1 = 0 by decide)
      · intro x
        rw [List.foldr_cons, hzero]
        simpa using hg' x
  exact norm_one_implementer q h₂ L hL hpar g hword

theorem geometricRestriction : GeometricRestriction.{u} := by
  intro K _ _ n h₂ g hg _
  obtain ⟨a, ha, hv⟩ := geometricIntrinsicRestriction K n h₂ g hg
  obtain ⟨e, he, hconj⟩ := splitSpinPoints K n h₂
  exact ⟨(e ⟨a, ha⟩).val, (e ⟨a, ha⟩).property.1, (e ⟨a, ha⟩).property.2,
    fun x => (hconj ⟨a, ha⟩ x).symm.trans (by rw [hv, map_apply_ι])⟩

end GeometricPoints

section ScalarKernel

private theorem odd_polar_coordinates {R : Type u} [CommRing R] {n : ℕ} (h₂ : (2 : R) = 0)
    (i : OddIndex n) (hi : i ≠ ⊤) :
    ∃ v : OddModule R n, (oddForm R n).polarBilin v = (Pi.basisFun R (OddIndex n)).coord i := by
  obtain ⟨_, h⟩ := split_model_data (R := R) (n := n) h₂
  obtain ⟨v, hv⟩ := h (i : AmbientIndex n) (by simpa [rIndex] using hi)
  refine ⟨v, LinearMap.ext fun w => ?_⟩
  rw [polar_restrict, hv, coordinate_basis]
  simpa [inclusion_apply, Basis.coord_apply, Pi.basisFun_repr]

private theorem evenRestriction_scalar {R : Type u} [CommRing R] {n : ℕ} (h₂ : (2 : R) = 0)
    (a : CliffordAlgebra (ambientForm R n)) (ha : a ∈ evenOdd (ambientForm R n) 0)
    (hx : ∀ x, Commute a (ι (ambientForm R n) (inclusion R n x))) :
    ∃ t : R, a = algebraMap R _ t := by
  classical
  let q := oddForm R n
  let Q := ambientForm R n
  let b := Pi.basisFun R (OddIndex n)
  let d := Pi.basisFun R (AmbientIndex n)
  let J := inclusion R n
  let r := radicalVector R n
  obtain ⟨h, _⟩ := split_model_data (R := R) (n := n) h₂
  obtain ⟨hinj, H⟩ := cliffordCentralizer q Q J b d r h₂ h
  obtain ⟨z, hz⟩ := (H a).mp (hx r).symm
  have hcomm (x : OddModule R n) : Commute z (ι q x) := by
    apply hinj
    simp only [map_mul, map_apply_ι, hz]
    exact (hx x).eq
  obtain ⟨t, ht⟩ := SpinFunctor.evenCentralizer_of_coordinates q b
    (fun s hs hEven => by
      obtain ⟨i, hi⟩ := hs
      have hi' : ∃ j ∈ s, j ≠ (⊤ : OddIndex n) := by
        by_contra! htop
        have he : s = {⊤} := Finset.eq_singleton_iff_unique_mem.mpr
          ⟨htop i hi ▸ hi, htop⟩
        simp [he] at hEven
      obtain ⟨j, hj, hjt⟩ := hi'
      exact ⟨j, hj, odd_polar_coordinates h₂ j hjt⟩)
    (even_of_map_even hinj z (by rw [hz]; exact ha)) hcomm
  exact ⟨t, by rw [← hz, ht, AlgHom.commutes]⟩

theorem scalarRestrictionKernel : ScalarRestrictionKernel.{u} := by
  intro R _ n h₂ Q J a ha _
  classical
  refine ⟨⟨?_, ?_⟩, fun t => Algebra.commute_algebraMap_left _ _⟩
  · intro hx
    let d := Pi.basisFun R (AmbientIndex n)
    obtain ⟨t, hta⟩ := evenRestriction_scalar h₂ a.val ha.1 hx
    have hnorm : t ^ 2 = 1 := by
      apply scalar_injective Q d
      have hn := ha.2.1
      rw [hta, reverse.commutes, ← map_mul] at hn
      simpa only [pow_two, map_one] using hn
    have htMul : t * t = 1 := by simpa only [pow_two] using hnorm
    have htUnit : IsUnit t := ⟨⟨t, t, htMul, htMul⟩, rfl⟩
    let T : rootsOfUnity 2 R :=
      ⟨htUnit.unit, (mem_rootsOfUnity' 2 htUnit.unit).mpr (by
        rw [htUnit.unit_spec]
        exact hnorm)⟩
    refine ⟨T, ?_, ?_⟩
    · exact hta.trans (congrArg (algebraMap R _) htUnit.unit_spec).symm
    · intro y hy
      apply rootsOfUnity.coe_injective
      apply scalar_injective Q d
      exact hy.symm.trans (hta.trans (congrArg (algebraMap R _) htUnit.unit_spec).symm)
  · rintro ⟨t, ht, _⟩ x
    rw [ht]
    exact Algebra.commute_algebraMap_left _ _

end ScalarKernel

section ScalarExtension

open scoped TensorProduct
open SpinSpecification
open private map_isometry_reverse map_isometry_evenOdd
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SplitSpin
open private cliffordEquiv cliffordEquiv_even cliffordEquiv_vector
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinFunctor
open private baseChangeEquiv_reverse from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.CliffordModel

variable {k S : Type u} [CommRing k] [CommRing S] [Algebra k S]
  {L : Type*} [Fintype L] [LinearOrder L]

private def coordinatesOver (k S : Type u) [CommRing k] [CommRing S] [Algebra k S]
    (L : Type*) [Fintype L] : S ⊗[k] (L → k) ≃ₗ[S] (L → S) :=
  ((Pi.basisFun k L).baseChange S).equivFun

private theorem coordinatesOver_tmul (s : S) (x : L → k) (i : L) :
    coordinatesOver k S L (s ⊗ₜ[k] x) i = algebraMap k S (x i) * s := by
  change ((Pi.basisFun k L).baseChange S).repr (s ⊗ₜ[k] x) i = _
  rw [Basis.baseChange_repr_tmul, Pi.basisFun_repr, Algebra.smul_def]

private def nativeIsometry (q : QuadraticForm k (L → k)) (P : QuadraticForm S (L → S))
    (hp : ∀ x : L → k, P (fun i => algebraMap k S (x i)) = algebraMap k S (q x)) :
    (ExtendedForm q S (Pi.basisFun k L)).IsometryEquiv P where
  toLinearEquiv := coordinatesOver k S L
  map_app' x := by
    have h : P.comp (coordinatesOver k S L).toLinearMap =
        ExtendedForm q S (Pi.basisFun k L) := by
      apply (CliffordModel.coefficient_form_unique S q (Pi.basisFun k L) _).mpr
      intro y
      change P (coordinatesOver k S L (1 ⊗ₜ[k] y)) = _
      rw [show coordinatesOver k S L (1 ⊗ₜ[k] y) = (fun i => algebraMap k S (y i)) by
        funext i
        rw [coordinatesOver_tmul, mul_one]]
      exact hp y
    exact congrArg (fun Q : QuadraticForm S _ => Q x) h

private def transportedClifford {A U J : Type*} [CommRing A] [Algebra A S]
    [AddCommGroup U] [Module A U] [LinearOrder J] [Fintype J]
    (q : QuadraticForm A U) (b : Basis J A U) {P : QuadraticForm S (L → S)}
    (ei : (ExtendedForm q S b).IsometryEquiv P) :
    ScalarClifford q S ≃ₐ[S] CliffordAlgebra P :=
  (cliffordEquiv q S b).trans (equivOfIsometry ei)

private theorem transportedClifford_vector {A U J : Type*} [CommRing A] [Algebra A S]
    [AddCommGroup U] [Module A U] [LinearOrder J] [Fintype J]
    (q : QuadraticForm A U) (b : Basis J A U) {P : QuadraticForm S (L → S)}
    (ei : (ExtendedForm q S b).IsometryEquiv P) (x : S ⊗[A] U) :
    transportedClifford q b ei (vectors q S x) = ι P (ei.toLinearEquiv x) := by
  simp only [transportedClifford, AlgEquiv.trans_apply, cliffordEquiv_vector,
    equivOfIsometry_apply, map_apply_ι]
  rfl

private theorem transportedClifford_spin {A U J : Type*} [CommRing A] [Algebra A S]
    [AddCommGroup U] [Module A U] [LinearOrder J] [Fintype J]
    (q : QuadraticForm A U) (b : Basis J A U) {P : QuadraticForm S (L → S)}
    (ei : (ExtendedForm q S b).IsometryEquiv P) (a : (ScalarClifford q S)ˣ) :
    a ∈ spinUnits q S ↔ IsIntrinsicSpin P (Units.map (transportedClifford q b ei).toMonoidHom a) := by
  let e := transportedClifford q b ei
  let A := Units.map e.toMonoidHom a
  have he : a.val ∈ evenPart q S ↔ A.val ∈ evenOdd P 0 := by
    change a.val ∈ evenPart q S ↔
      (CliffordAlgebra.map ei.toIsometry) (cliffordEquiv q S b a.val) ∈ evenOdd P 0
    rw [← cliffordEquiv_even q S b]
    refine ⟨map_isometry_evenOdd ei.toIsometry, fun h => ?_⟩
    have hh := map_isometry_evenOdd ei.symm.toIsometry h
    change (equivOfIsometry ei).symm ((equivOfIsometry ei)
      (cliffordEquiv q S b a.val)) ∈ _ at hh
    rwa [AlgEquiv.symm_apply_apply] at hh
  have hr (x : ScalarClifford q S) : e (reversion q S x) = reverse (e x) := by
    change CliffordAlgebra.map ei.toIsometry (cliffordEquiv q S b (reversion q S x)) = _
    rw [show cliffordEquiv q S b (reversion q S x) = reverse (cliffordEquiv q S b x)
      from baseChangeEquiv_reverse S q b x, map_isometry_reverse]
    rfl
  have hn : reversion q S a.val * a.val = 1 ↔ reverse A.val * A.val = 1 := by
    rw [← e.injective.eq_iff, map_mul, hr, map_one]
    rfl
  have hv (c : (ScalarClifford q S)ˣ) :
      Set.MapsTo (conjugate q S c) (LinearMap.range (vectors q S))
        (LinearMap.range (vectors q S)) ↔
      Set.MapsTo (fun x : CliffordAlgebra P =>
        (Units.map e.toMonoidHom c).val * x * ↑(Units.map e.toMonoidHom c)⁻¹)
        (LinearMap.range (ι P)) (LinearMap.range (ι P)) := by
    constructor
    · intro h
      rintro _ ⟨y, rfl⟩
      obtain ⟨x, rfl⟩ := ei.toLinearEquiv.surjective y
      obtain ⟨z, hz⟩ := h (LinearMap.mem_range_self _ x)
      refine ⟨ei.toLinearEquiv z, ?_⟩
      rw [← transportedClifford_vector q b ei z, hz]
      change e (conjugate q S c (vectors q S x)) = _
      rw [conjugate, map_mul, map_mul, show e (vectors q S x) = _ from transportedClifford_vector q b ei x]
      rfl
    · intro h
      rintro _ ⟨x, rfl⟩
      obtain ⟨y, hy⟩ := h (LinearMap.mem_range_self _ (ei.toLinearEquiv x))
      obtain ⟨z, rfl⟩ := ei.toLinearEquiv.surjective y
      refine ⟨z, e.injective ?_⟩
      rw [show e (vectors q S z) = _ from transportedClifford_vector q b ei z, hy]
      change _ = e (conjugate q S c (vectors q S x))
      rw [conjugate, map_mul, map_mul, show e (vectors q S x) = _ from transportedClifford_vector q b ei x]
      rfl
  change (_ ∧ _ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _ ∧ _)
  exact and_congr he (and_congr hn (and_congr (hv a)
    (by simpa only [map_inv, inv_inv] using hv a⁻¹)))

private def nativeClifford (q : QuadraticForm k (L → k)) (P : QuadraticForm S (L → S))
    (hp : ∀ x : L → k, P (fun i => algebraMap k S (x i)) = algebraMap k S (q x)) :
    ScalarClifford q S ≃ₐ[S] CliffordAlgebra P :=
  transportedClifford q (Pi.basisFun k L) (nativeIsometry q P hp)

private theorem nativeClifford_vector (q : QuadraticForm k (L → k))
    (P : QuadraticForm S (L → S)) (hp : ∀ x : L → k,
      P (fun i => algebraMap k S (x i)) = algebraMap k S (q x))
    (x : S ⊗[k] (L → k)) :
    nativeClifford q P hp (vectors q S x) = ι P (coordinatesOver k S L x) :=
  transportedClifford_vector q (Pi.basisFun k L) (nativeIsometry q P hp) x

private theorem nativeClifford_spin (q : QuadraticForm k (L → k))
    (P : QuadraticForm S (L → S)) (hp : ∀ x : L → k,
      P (fun i => algebraMap k S (x i)) = algebraMap k S (q x))
    (a : (ScalarClifford q S)ˣ) :
    a ∈ spinUnits q S ↔ IsIntrinsicSpin P (Units.map (nativeClifford q P hp).toMonoidHom a) :=
  transportedClifford_spin q (Pi.basisFun k L) (nativeIsometry q P hp) a

private theorem ambient_map (n : ℕ) (x : AmbientModule k n) :
    ambientForm S n (fun i => algebraMap k S (x i)) = algebraMap k S (ambientForm k n x) := by
  simp only [ambientForm_apply, map_add, map_mul, map_sum]

private theorem odd_map (n : ℕ) (x : OddModule k n) :
    oddForm S n (fun i => algebraMap k S (x i)) = algebraMap k S (oddForm k n x) := by
  change ambientForm S n (extendOdd S n fun i => algebraMap k S (x i)) =
    algebraMap k S (ambientForm k n (extendOdd k n x))
  rw [← ambient_map]
  congr 1
  funext i
  cases i using WithTop.recTopCoe with
  | top => simp
  | coe i => rfl

private theorem nativeClifford_inclusion {n : ℕ} (x : ScalarClifford (oddForm k n) S) :
    let e := nativeClifford (ambientForm k n) (ambientForm S n) (ambient_map n)
    let e' := nativeClifford (oddForm k n) (oddForm S n) (odd_map n)
    e (Algebra.TensorProduct.map (AlgHom.id S S) (CliffordAlgebra.map (inclusion k n)) x) =
      CliffordAlgebra.map (inclusion S n) (e' x) := by
  dsimp only
  let e := nativeClifford (ambientForm k n) (ambientForm S n) (ambient_map n)
  let e' := nativeClifford (oddForm k n) (oddForm S n) (odd_map n)
  have h :
      e.toAlgHom.comp (Algebra.TensorProduct.map (AlgHom.id S S) (CliffordAlgebra.map (inclusion k n))) =
        (CliffordAlgebra.map (inclusion S n)).comp e'.toAlgHom := by
    apply Algebra.TensorProduct.ext_ring
    apply CliffordAlgebra.hom_ext
    apply LinearMap.ext
    intro v
    change e (Algebra.TensorProduct.map (AlgHom.id S S) (CliffordAlgebra.map (inclusion k n))
      (1 ⊗ₜ[k] ι (oddForm k n) v)) =
        CliffordAlgebra.map (inclusion S n) (e' (1 ⊗ₜ[k] ι (oddForm k n) v))
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_apply_ι]
    change e (vectors _ S (1 ⊗ₜ[k] inclusion k n v)) =
      CliffordAlgebra.map (inclusion S n) (e' (vectors _ S (1 ⊗ₜ[k] v)))
    simp only [e, e', nativeClifford_vector, map_apply_ι]
    congr 1
    funext i
    cases i using WithTop.recTopCoe with
    | top => simp [coordinatesOver_tmul, inclusion_apply]
    | coe i => simp [coordinatesOver_tmul, inclusion_apply]
  exact AlgHom.congr_fun h x

theorem tensorSpinComparison : TensorSpinComparison.{u} := by
  intro k _ n h₂ q Q J r S _ _ j
  classical
  have h₂S : (2 : S) = 0 := by
    simpa only [map_ofNat, map_zero] using congrArg (algebraMap k S) h₂
  let qs := oddForm S n
  let Qs := ambientForm S n
  let Js := inclusion S n
  let rs := radicalVector S n
  let ej := CliffordAlgebra.map Js
  let e := nativeClifford Q Qs (ambient_map n)
  let e' := nativeClifford q qs (odd_map n)
  obtain ⟨hadapt, _⟩ := split_model_data (R := S) (n := n) h₂S
  obtain ⟨hejinj, _⟩ := cliffordCentralizer qs Qs Js (Pi.basisFun S _)
    (Pi.basisFun S _) rs h₂S hadapt
  have hcomp (x : ScalarClifford q S) : e (j x) = ej (e' x) :=
    nativeClifford_inclusion x
  have hjinj : Function.Injective j := by
    intro x y hxy
    apply e'.injective
    apply hejinj
    rw [← hcomp, ← hcomp, hxy]
  have hunitcomp (x : (ScalarClifford q S)ˣ) :
      Units.map e.toMonoidHom (Units.map j.toMonoidHom x) =
        Units.map ej.toMonoidHom (Units.map e'.toMonoidHom x) :=
    Units.ext (hcomp x.val)
  have hmark : e (vectors Q S (1 ⊗ₜ[k] J r)) = ι Qs (Js rs) := by
    rw [show e (vectors Q S (1 ⊗ₜ[k] J r)) =
      ι Qs (coordinatesOver k S _ (1 ⊗ₜ[k] J r)) from nativeClifford_vector Q Qs _ _]
    congr 1
    funext i
    rw [coordinatesOver_tmul, mul_one]
    cases i using WithTop.recTopCoe with
    | top => simp [J, Js, inclusion_apply]
    | coe i => simp [J, Js, r, rs, inclusion_apply, Pi.single_apply]
  obtain ⟨f, hf, _⟩ := splitSpinPoints S n h₂S
  have hnorm (a : (ScalarClifford q S)ˣ) :
      a ∈ spinUnits q S ↔ Units.map j.toMonoidHom a ∈ spinUnits Q S ∧
        Commute (vectors Q S (1 ⊗ₜ[k] J r)) (j a.val) := by
    rw [nativeClifford_spin q qs (odd_map n), nativeClifford_spin Q Qs (ambient_map n)]
    change IsIntrinsicSpin qs (Units.map e'.toMonoidHom a) ↔
      IsIntrinsicSpin Qs (Units.map e.toMonoidHom (Units.map j.toMonoidHom a)) ∧ _
    rw [hunitcomp]
    have hcent : Commute (vectors Q S (1 ⊗ₜ[k] J r)) (j a.val) ↔
        Commute (ι Qs (Js rs)) (ej (e' a.val)) := by
      change (_ * _ = _ * _) ↔ (_ * _ = _ * _)
      rw [← e.injective.eq_iff, map_mul, map_mul, hmark, hcomp]
    rw [hcent]
    constructor
    · intro ha
      let A : {a : (CliffordAlgebra qs)ˣ // IsIntrinsicSpin qs a} :=
        ⟨Units.map e'.toMonoidHom a, ha⟩
      have hd : (f A).val = Units.map ej.toMonoidHom (Units.map e'.toMonoidHom a) := hf A
      change IsIntrinsicSpin Qs (Units.map ej.toMonoidHom (Units.map e'.toMonoidHom a)) ∧
        Commute (ι Qs (Js rs)) (Units.map ej.toMonoidHom (Units.map e'.toMonoidHom a)).val
      rw [← hd]
      exact (f A).property
    · intro ha
      let A := Units.map e'.toMonoidHom a
      have hA : ∃ t : {a : (CliffordAlgebra qs)ˣ // IsIntrinsicSpin qs a},
          (f t).val = Units.map ej.toMonoidHom A := by
        obtain ⟨t, ht⟩ := f.surjective ⟨Units.map ej.toMonoidHom A, ha⟩
        exact ⟨t, congrArg Subtype.val ht⟩
      obtain ⟨t, ht⟩ := hA
      have heq : t.val = A := Units.ext (hejinj (congrArg (fun z => z.val) ((hf t).symm.trans ht)))
      change IsIntrinsicSpin qs A
      rw [← heq]
      exact t.property
  refine ⟨hjinj, hnorm, ?_, ?_, ?_⟩
  · intro a ha hc
    let A := Units.map e.toMonoidHom a
    have hA : IsIntrinsicSpin Qs A := (nativeClifford_spin Q Qs _ a).mp ha
    have hfix : Commute (ι Qs (Js rs)) A.val := by
      rw [← hmark]
      exact hc.map e
    obtain ⟨b, hb⟩ := f.surjective ⟨A, hA, hfix⟩
    obtain ⟨t, ht⟩ := (Units.mapEquiv e'.toMulEquiv).surjective b.val
    have ht' : Units.map e'.toMonoidHom t = b.val := ht
    have hspin : t ∈ spinUnits q S :=
      (nativeClifford_spin q qs _ t).mpr (ht'.symm ▸ b.property)
    have hta : Units.map j.toMonoidHom t = a := by
      apply Units.ext
      apply e.injective
      change e (j t.val) = e a.val
      rw [hcomp]
      exact congrArg (fun z : (CliffordAlgebra Qs)ˣ => z.val)
        ((congrArg (Units.map ej.toMonoidHom) ht').trans
          ((hf b).symm.trans (congrArg Subtype.val hb)))
    exact ⟨t, ⟨hspin, hta⟩, fun z hz =>
      Units.ext (hjinj (congrArg (fun a : (ScalarClifford Q S)ˣ => a.val) (hz.2.trans hta.symm)))⟩
  · intro x
    induction x with
    | tmul s x =>
      simp only [vectors, LinearMap.baseChange_tmul, j, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply, map_apply_ι]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  · intro T _ _ g x
    induction x using TensorProduct.inductionOn with
    | tmul a x => simp [j, coefficientMap, Algebra.TensorProduct.map_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]

end ScalarExtension

section NativeCoefficients

open SpinSpecification SplitSpinSpecification
open scoped TensorProduct
open private changeCoefficients_vector changeModule changeModule_coord
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinFunctor
open private splitForm splitCoordinates split_form_coordinates from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SplitSpin

variable {A U J : Type*} [CommRing A] [AddCommGroup U] [Module A U]
  [Fintype J] [LinearOrder J] (q : QuadraticForm A U) (b : Basis J A U)
  {S T : Type u} [CommRing S] [CommRing T] [Algebra A S] [Algebra A T]
  {L : Type*} [Fintype L] [LinearOrder L] {P : QuadraticForm S (L → S)}
  {P' : QuadraticForm T (L → T)}
  (iS : (ExtendedForm q S b).IsometryEquiv P) (iT : (ExtendedForm q T b).IsometryEquiv P')
  (f : S →ₐ[A] T)

private def transportedCoefficients : CliffordAlgebra P →+* CliffordAlgebra P' :=
  (transportedClifford q b iT).toRingHom.comp <|
    (SpinFunctor.changeCoefficients q f).toRingHom.comp (transportedClifford q b iS).symm.toRingHom

private theorem transportedCoefficients_scalar (a : S) :
    transportedCoefficients q b iS iT f (algebraMap S _ a) = algebraMap T _ (f a) := by
  have h : SpinFunctor.changeCoefficients q f (algebraMap S (ScalarClifford q S) a) =
      algebraMap T (ScalarClifford q T) (f a) := by
    simp [SpinFunctor.changeCoefficients, Algebra.TensorProduct.map_tmul]
  change transportedClifford q b iT
    (SpinFunctor.changeCoefficients q f ((transportedClifford q b iS).symm (algebraMap S _ a))) = _
  rw [AlgEquiv.commutes, h, AlgEquiv.commutes]

private theorem transportedCoefficients_vector
    (hi : ∀ x : S ⊗[A] U, iT.toLinearEquiv (changeModule f x) = fun j => f (iS.toLinearEquiv x j))
    (x : L → S) :
    transportedCoefficients q b iS iT f (ι P x) = ι P' (fun j => f (x j)) := by
  obtain ⟨x, rfl⟩ := iS.toLinearEquiv.surjective x
  rw [← transportedClifford_vector q b iS x]
  change transportedClifford q b iT (SpinFunctor.changeCoefficients q f
    ((transportedClifford q b iS).symm (transportedClifford q b iS (vectors q S x)))) = _
  rw [AlgEquiv.symm_apply_apply, changeCoefficients_vector, transportedClifford_vector, hi]

variable {k : Type u} [CommRing k] [Algebra k S] [Algebra k T]

private abbrev ambientCliffordEquiv (k S : Type u) [CommRing k] [CommRing S] [Algebra k S] (n : ℕ) :=
  nativeClifford (ambientForm k n) (ambientForm S n) (ambient_map n)

private def ambientCoefficients (n : ℕ) (g : S →ₐ[k] T) :
    CliffordAlgebra (ambientForm S n) →+* CliffordAlgebra (ambientForm T n) :=
  transportedCoefficients (ambientForm k n) (Pi.basisFun k (AmbientIndex n))
    (nativeIsometry _ _ (ambient_map n)) (nativeIsometry _ _ (ambient_map n)) g

private theorem ambientCoefficients_apply (n : ℕ) (g : S →ₐ[k] T)
    (x : ScalarClifford (ambientForm k n) S) :
    ambientCoefficients n g (ambientCliffordEquiv k S n x) =
      ambientCliffordEquiv k T n (SpinFunctor.changeCoefficients (ambientForm k n) g x) := by
  change ambientCliffordEquiv k T n (SpinFunctor.changeCoefficients (ambientForm k n) g
    ((ambientCliffordEquiv k S n).symm (ambientCliffordEquiv k S n x))) = _
  rw [AlgEquiv.symm_apply_apply]

private theorem ambientCoefficients_vector (n : ℕ) (g : S →ₐ[k] T) (x : AmbientModule S n) :
    ambientCoefficients n g (ι (ambientForm S n) x) = ι (ambientForm T n) (fun j => g (x j)) := by
  apply transportedCoefficients_vector
  intro y
  funext j
  exact changeModule_coord (Pi.basisFun k (AmbientIndex n)) g y j

private def integralAmbientIsometry (n : ℕ) (S : Type u) [CommRing S] :
    (splitForm (n + 1) S).IsometryEquiv (ambientForm S n) where
  toLinearEquiv := (splitCoordinates (n + 1) S).trans (ambientCoordinates S n).symm
  map_app' x := by
    change ambientForm S n ((ambientCoordinates S n).symm (splitCoordinates (n + 1) S x)) = _
    rw [ambientCoordinates_norm, LinearEquiv.apply_symm_apply, split_form_coordinates]

private abbrev integralAmbientClifford (n : ℕ) (S : Type u) [CommRing S] :=
  transportedClifford (integralForm (n + 1)) (hyperbolicBasis ℤ (n + 1)) (integralAmbientIsometry n S)

private theorem integralAmbientClifford_natural (n : ℕ) (g : S →ₐ[k] T)
    (y : SplitSpinSpecification.ScalarClifford (n + 1) S) :
    integralAmbientClifford n T (SpinFunctor.changeCoefficients (integralForm (n + 1))
      g.toRingHom.toIntAlgHom y) = ambientCoefficients n g (integralAmbientClifford n S y) := by
  let qZ := integralForm (n + 1)
  let bZ := hyperbolicBasis ℤ (n + 1)
  let F := transportedCoefficients qZ bZ (integralAmbientIsometry n S) (integralAmbientIsometry n T)
    g.toRingHom.toIntAlgHom
  have h : F = ambientCoefficients n g := by
    ext x : 1
    induction x using CliffordAlgebra.induction with
    | algebraMap a =>
      rw [transportedCoefficients_scalar, ambientCoefficients, transportedCoefficients_scalar]
      rfl
    | ι x =>
      rw [ambientCoefficients_vector]
      apply transportedCoefficients_vector
      intro z
      have hz (j : PairIndex (n + 1)) : splitCoordinates (n + 1) T
          (changeModule g.toRingHom.toIntAlgHom z) j = g (splitCoordinates (n + 1) S z j) :=
        changeModule_coord bZ g.toRingHom.toIntAlgHom z (toLex j)
      apply (ambientCoordinates T n).injective
      change ambientCoordinates T n ((ambientCoordinates T n).symm _) = _
      rw [LinearEquiv.apply_symm_apply]
      let v := (ambientCoordinates S n).symm (splitCoordinates (n + 1) S z)
      have hv (j : PairIndex (n + 1)) :
          splitCoordinates (n + 1) S z j = ambientCoordinates S n v j :=
        (congrFun ((ambientCoordinates S n).apply_symm_apply _) j).symm
      funext j
      change splitCoordinates (n + 1) T (changeModule g.toRingHom.toIntAlgHom z) j =
        ambientCoordinates T n (fun i => g (v i)) j
      refine (hz j).trans ?_
      rw [hv j]
      cases j with
      | inl j => cases j using Fin.cases <;> rfl
      | inr j =>
        cases j using Fin.cases with
        | zero => exact (map_add g _ _)
        | succ j => rfl
    | mul x y hx hy => rw [map_mul, map_mul, hx, hy]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  rw [← h]
  change _ = integralAmbientClifford n T (SpinFunctor.changeCoefficients qZ
    g.toRingHom.toIntAlgHom ((integralAmbientClifford n S).symm (integralAmbientClifford n S y)))
  rw [AlgEquiv.symm_apply_apply]

end NativeCoefficients

section InfinitesimalOrbit

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

private theorem double_mem_square_zero {A : Type*} [Ring A] [Algebra R A]
    (I : Ideal R) (hI : I ^ 2 = ⊥) (a b : A)
    (ha : a ∈ I • (⊤ : Submodule R A)) (hb : b ∈ I • (⊤ : Submodule R A))
    (z : A) : a * z * b = 0 := by
  refine Submodule.smul_induction_on (p := fun x => x * z * b = 0) ha ?_ ?_
  · intro r hr x _
    refine Submodule.smul_induction_on (p := fun y => (r • x) * z * y = 0) hb ?_ ?_
    · intro s hs y _
      have hrs : r * s = 0 := by
        have hm := Ideal.mul_mem_mul hr hs
        rw [← pow_two, hI] at hm
        exact Ideal.mem_bot.mp hm
      rw [mul_smul_comm, smul_mul_assoc, smul_mul_assoc, smul_smul, mul_comm s r, hrs, zero_smul]
    · intro y₁ y₂ hy₁ hy₂
      rw [mul_add, hy₁, hy₂, add_zero]
  · intro x₁ x₂ hx₁ hx₂
    rw [add_mul, add_mul, hx₁, hx₂, add_zero]

private theorem bivector_commutator (Q : QuadraticForm R M) (v w x : M) :
    (ι Q v * ι Q w) * ι Q x - ι Q x * (ι Q v * ι Q w) =
      ι Q (Q.polarBilin w x • v - Q.polarBilin v x • w) := by
  have hxw := ι_mul_ι_comm (Q := Q) w x
  have hxv := ι_mul_ι_comm (Q := Q) v x
  rw [mul_assoc, hxw, mul_sub, ← mul_assoc, hxv, sub_mul, ← Algebra.commutes,
    ← Algebra.smul_def, ← Algebra.smul_def, mul_assoc, map_sub, map_smul, map_smul,
    ← QuadraticMap.polarBilin_apply_apply, ← QuadraticMap.polarBilin_apply_apply]
  abel

private theorem tangent_unit (Q : QuadraticForm R M) (h₂ : (2 : R) = 0)
    (I : Ideal R) (hI : I ^ 2 = ⊥) (c : CliffordAlgebra Q)
    (hc : c ∈ I • (⊤ : Submodule R (CliffordAlgebra Q))) (he : c ∈ evenOdd Q 0)
    (hr : reverse c = c)
    (hl : ∀ x : M, ∃ y : M, c * ι Q x - ι Q x * c = ι Q y) :
    ∃ a : (CliffordAlgebra Q)ˣ,
      a.val = 1 + c ∧ IsIntrinsicSpin Q a ∧
      ∀ x : M, a.val * ι Q x * ↑a⁻¹ = ι Q x + (c * ι Q x - ι Q x * c) := by
  have hneg (x : CliffordAlgebra Q) : -x = x := by
    apply neg_eq_iff_add_eq_zero.mpr
    rw [← two_smul R, h₂, zero_smul]
  have hcc : c * c = 0 := by
    simpa only [mul_one] using double_mem_square_zero I hI c c hc hc 1
  have ha : (1 + c) * (1 + c) = 1 := by
    simp only [add_mul, mul_add, mul_one, one_mul, hcc, add_zero]
    rw [add_assoc, ← two_smul R c, h₂, zero_smul, add_zero]
  let a : (CliffordAlgebra Q)ˣ := ⟨1 + c, 1 + c, ha, ha⟩
  have hact (x : M) : a.val * ι Q x * ↑a⁻¹ =
      ι Q x + (c * ι Q x - ι Q x * c) := by
    change (1 + c) * ι Q x * (1 + c) = _
    simp only [add_mul, mul_add, one_mul, mul_one, double_mem_square_zero I hI c c hc hc, add_zero]
    rw [sub_eq_add_neg, hneg]
    abel
  have hmaps : Set.MapsTo (fun x : CliffordAlgebra Q => a.val * x * ↑a⁻¹)
      (LinearMap.range (ι Q)) (LinearMap.range (ι Q)) := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := hl x
    exact ⟨x + y, by simp only [map_add, hact, hy]⟩
  refine ⟨a, rfl, ⟨(evenOdd Q 0).add_mem (SetLike.one_mem_graded _) he, ?_, hmaps, hmaps⟩, hact⟩
  change reverse (1 + c) * (1 + c) = 1
  simpa only [map_add, reverse.map_one, hr] using ha

theorem squareZeroOrbitLifting : SquareZeroOrbitLifting.{u} := by
  intro R _ n h₂ hn Q r I hI v hv hperp
  classical
  let j : Fin n := ⟨0, hn⟩
  let e : AmbientModule R n := Pi.single (eIndex j) 1
  let f : AmbientModule R n := Pi.single (fIndex j) 1
  let z : AmbientModule R n := Pi.single ⊤ 1
  let α := v (rIndex n)
  let c := ι Q v * ι Q z + α • (ι Q e * ι Q f)
  have hpolar_r : Q.polarBilin r = LinearMap.proj (⊤ : AmbientIndex n) := by
    rw [← coordinate_basis]
    exact (split_model_data (R := R) (n := n) h₂).1.polar_coord
  have hzv : Q.polarBilin v z = α := by
    change (ambientForm R n).polarBilin v z = _
    rw [ambient_polar h₂]
    simp [z, α, Pi.single_apply, eIndex, fIndex, rIndex]
  have hef : Q.polarBilin e f = 1 := by
    change (ambientForm R n).polarBilin e f = _
    rw [ambient_polar h₂]
    simp [e, f, Pi.single_apply, eIndex, fIndex, rIndex, ite_mul]
  have hzeroc : c ∈ I • (⊤ : Submodule R (CliffordAlgebra Q)) := by
    refine (I • (⊤ : Submodule R _)).add_mem ?_ (Submodule.smul_mem_smul (hv _) Submodule.mem_top)
    have hsum : ∑ i : AmbientIndex n, v i • (Pi.basisFun R (AmbientIndex n)) i = v := by
      simpa only [Pi.basisFun_repr] using (Pi.basisFun R (AmbientIndex n)).sum_repr v
    rw [← hsum, map_sum, Finset.sum_mul]
    apply Submodule.sum_mem
    intro i _
    rw [map_smul, smul_mul_assoc]
    exact Submodule.smul_mem_smul (hv i) Submodule.mem_top
  have hc : c ∈ evenOdd Q 0 := (evenOdd Q 0).add_mem (ι_mul_ι_mem_evenOdd_zero Q v z)
    ((evenOdd Q 0).smul_mem α (ι_mul_ι_mem_evenOdd_zero Q e f))
  have hrev : reverse c = c := by
    have hzv' : Q.polarBilin z v = α :=
      (QuadraticMap.polar_comm Q z v).trans hzv
    have hfe : Q.polarBilin f e = 1 :=
      (QuadraticMap.polar_comm Q f e).trans hef
    dsimp only [c]
    simp only [map_add, map_smul, reverse.map_mul, reverse_ι]
    rw [ι_mul_ι_comm (Q := Q) z v, ι_mul_ι_comm (Q := Q) f e,
      ← QuadraticMap.polarBilin_apply_apply, ← QuadraticMap.polarBilin_apply_apply, hzv', hfe,
      map_one, smul_sub, Algebra.smul_def α (1 : CliffordAlgebra Q), mul_one]
    have hneg (x : CliffordAlgebra Q) : -x = x :=
      neg_eq_iff_add_eq_zero.mpr (by rw [← two_smul R, h₂, zero_smul])
    simp only [sub_eq_add_neg, hneg, ← smul_neg, hneg]
    have hz' : algebraMap R (CliffordAlgebra Q) α + algebraMap R _ α = 0 := by
      rw [← two_smul R, h₂, zero_smul]
    rw [add_add_add_comm, hz', zero_add]
  have hcomm (x : AmbientModule R n) : c * ι Q x - ι Q x * c =
      ι Q ((Q.polarBilin z x • v - Q.polarBilin v x • z) +
        α • (Q.polarBilin f x • e - Q.polarBilin e x • f)) := by
    dsimp only [c]
    rw [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, add_sub_add_comm,
      ← smul_sub, bivector_commutator, bivector_commutator, ← map_smul, ← map_add]
  obtain ⟨a, hval, ha, hact⟩ :=
    tangent_unit Q h₂ I hI c hzeroc hc hrev (fun x => ⟨_, hcomm x⟩)
  refine ⟨a, ha, ?_, ?_⟩
  · rw [hval, add_sub_cancel_left]
    exact hzeroc
  · rw [hact, hcomm]
    have hflip (y : AmbientModule R n) : Q.polarBilin y r = y ⊤ := by
      rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm,
        ← QuadraticMap.polarBilin_apply_apply, hpolar_r]
      rfl
    have hz' : z ⊤ = 1 := by simp [z]
    have hv' : v ⊤ = 0 := by rw [hpolar_r] at hperp; exact hperp
    have he' : e ⊤ = 0 := by simp [e, Pi.single_apply, eIndex]
    have hf' : f ⊤ = 0 := by simp [f, Pi.single_apply, fIndex]
    simp only [hflip, hz', hv', he', hf', one_smul, zero_smul, sub_zero,
      smul_zero, add_zero, map_add]

end InfinitesimalOrbit

section StabilizerSmoothness

open AlgebraicGeometry CategoryTheory Opposite SpinSpecification SplitSpinSpecification
open scoped TensorProduct CategoryTheory.MonObj
open private splitSpinScheme switchOpen switchOpen_cover switchOpen_smooth
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SplitSpin
open private spinUnitPoints spinUnitPoints_represents from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinFunctor

private abbrev IntegralSpinRing (m : ℕ) :=
  SpinFunctor.CoordinateRing (integralForm m) (hyperbolicBasis ℤ m)

private theorem integralSpin_smooth (m : ℕ) (hm : 0 < m) : Algebra.Smooth ℤ (IntegralSpinRing m) := by
  rw [← RingHom.smooth_algebraMap]
  have h : Smooth (splitSpinScheme m).X.hom := by
    letI : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} (2 * m ^ 2 - m)) :=
      HasRingHomProperty.instIsZariskiLocalAtSource
        (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension (2 * m ^ 2 - m)))
    have : SmoothOfRelativeDimension (2 * m ^ 2 - m) (splitSpinScheme m).X.hom :=
      IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension (2 * m ^ 2 - m))
        (switchOpen m) (switchOpen_cover m) (switchOpen_smooth m hm)
    exact SmoothOfRelativeDimension.smooth (2 * m ^ 2 - m) _
  exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mp h

variable {k : Type u} [Field k] {S : Type u} [CommRing S] [Algebra k S]
  (n : ℕ) (I : Ideal S) (hI : I ^ 2 = ⊥)

include hI in
private theorem intrinsicAmbient_lift (a : (CliffordAlgebra (ambientForm (S ⧸ I) n))ˣ)
    (ha : IsIntrinsicSpin (ambientForm (S ⧸ I) n) a) :
    ∃ c : (CliffordAlgebra (ambientForm S n))ˣ,
      IsIntrinsicSpin (ambientForm S n) c ∧
      Units.map (ambientCoefficients n (Ideal.Quotient.mkₐ k I)).toMonoidHom c = a := by
  let qZ := integralForm (n + 1)
  let bZ := hyperbolicBasis ℤ (n + 1)
  let f := Ideal.Quotient.mkₐ k I
  obtain ⟨aZ, haZ⟩ := (Units.mapEquiv (integralAmbientClifford n (S ⧸ I)).toMulEquiv).surjective a
  let p : SpinFunctor.Spin qZ (S ⧸ I) bZ := ⟨aZ,
    (transportedClifford_spin qZ bZ (integralAmbientIsometry n (S ⧸ I)) aZ).mpr (haZ.symm ▸ ha)⟩
  have := integralSpin_smooth (n + 1) (by omega)
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.comp_surjective ℤ (IntegralSpinRing (n + 1)) I hI
    ((SpinFunctor.pointEquiv qZ bZ (S ⧸ I)).symm p)
  let a' := SpinFunctor.pointEquiv qZ bZ S g
  have ht : SpinFunctor.map qZ bZ f.toRingHom.toIntAlgHom a' = p := by
    have hh := congrArg (SpinFunctor.pointEquiv qZ bZ (S ⧸ I)) hg
    rw [Equiv.apply_symm_apply] at hh
    exact (SpinFunctor.pointEquiv_natural qZ bZ f.toRingHom.toIntAlgHom g).symm.trans hh
  refine ⟨Units.map (integralAmbientClifford n S).toMonoidHom a'.val,
    (transportedClifford_spin qZ bZ (integralAmbientIsometry n S) a'.val).mp a'.property, ?_⟩
  apply Units.ext
  change ambientCoefficients n f (integralAmbientClifford n S a'.val.val) = a.val
  rw [← integralAmbientClifford_natural]
  have hh := congrArg (fun z : SpinFunctor.Spin qZ (S ⧸ I) bZ =>
    integralAmbientClifford n (S ⧸ I) z.val.val) ht
  exact hh.trans (congrArg Units.val haZ)

private abbrev ambientBasis (k : Type u) [CommRing k] (n : ℕ) :=
  (Pi.basisFun k (AmbientIndex n)).reindex (Equiv.ulift.{u}.symm)

private abbrev markedVector (R : Type u) [CommRing R] (n : ℕ) :=
  inclusion R n (radicalVector R n)

private theorem markedVector_single (R : Type u) [CommRing R] (n : ℕ) :
    markedVector R n = Pi.single (rIndex n) 1 := by
  funext i
  cases i using WithTop.recTopCoe with
  | top =>
    change (0 : R) = (Pi.single (rIndex n) 1 : AmbientModule R n) ⊤
    simp [rIndex]
  | coe i =>
    change (radicalVector R n) i = _
    by_cases hi : i = ⊤ <;> simp [Pi.single_apply, rIndex, hi]

private theorem ambientCliffordEquiv_marked :
    ambientCliffordEquiv k S n (markedClifford (ambientForm k n) (markedVector k n) S) =
      CliffordAlgebra.ι (ambientForm S n) (markedVector S n) := by
  rw [markedClifford, nativeClifford_vector]
  congr 1
  funext i
  rw [coordinatesOver_tmul, mul_one, markedVector_single, markedVector_single]
  simp [Pi.single_apply]

include hI in
private theorem ambientSpin_lift (a : SpinFunctor.Spin (ambientForm k n) (S ⧸ I) (ambientBasis k n)) :
    ∃ c : SpinFunctor.Spin (ambientForm k n) S (ambientBasis k n),
      SpinFunctor.map (ambientForm k n) (ambientBasis k n) (Ideal.Quotient.mkₐ k I) c = a := by
  let Q := ambientForm k n
  let e := ambientCliffordEquiv k S n
  let e' := ambientCliffordEquiv k (S ⧸ I) n
  let A := Units.map e'.toMonoidHom a.val
  have hA : IsIntrinsicSpin (ambientForm (S ⧸ I) n) A := (nativeClifford_spin Q _ _ a.val).mp a.property
  obtain ⟨C, hC, hc⟩ := intrinsicAmbient_lift (k := k) n I hI A hA
  obtain ⟨c, hec⟩ := (Units.mapEquiv e.toMulEquiv).surjective C
  refine ⟨⟨c, (nativeClifford_spin Q _ _ c).mpr (hec.symm ▸ hC)⟩, ?_⟩
  apply Subtype.ext
  apply Units.ext
  apply e'.injective
  change e' (SpinFunctor.changeCoefficients Q (Ideal.Quotient.mkₐ k I) c.val) = e' a.val.val
  have he := congrArg Units.val hec
  change e c.val = C.val at he
  rw [← ambientCoefficients_apply, he]
  exact congrArg Units.val hc

private theorem intrinsic_vector_injective (P : QuadraticForm S (AmbientModule S n)) :
    Function.Injective (CliffordAlgebra.ι P) := by
  obtain ⟨f, hf⟩ := CliffordModel.vector_summand P (Pi.basisFun S (AmbientIndex n))
  have h : Function.LeftInverse f (CliffordAlgebra.ι P) := LinearMap.congr_fun hf
  exact h.injective

include hI in
private theorem mul_eq_zero_of_squareZero {x y : S} (hx : x ∈ I) (hy : y ∈ I) : x * y = 0 := by
  have h := Ideal.mul_mem_mul hx hy
  rw [← pow_two, hI] at h
  exact Ideal.mem_bot.mp h

include hI in
private theorem ambientVector_squareZero (v : AmbientModule S n) (hv : ∀ j, v j ∈ I) :
    ambientForm S n v = 0 := by
  rw [ambientForm_apply]
  have hterm (i : Fin n) : v (eIndex i) * v (fIndex i) = 0 :=
    mul_eq_zero_of_squareZero I hI (hv _) (hv _)
  rw [mul_eq_zero_of_squareZero I hI (hv _) (I.add_mem (hv _) (hv _)), add_zero]
  simp only [hterm, Finset.sum_const_zero]

private theorem ambientCoefficients_kills (x : CliffordAlgebra (ambientForm S n))
    (hx : x ∈ I • (⊤ : Submodule S (CliffordAlgebra (ambientForm S n)))) :
    ambientCoefficients n (Ideal.Quotient.mkₐ k I) x = 0 := by
  let g := Ideal.Quotient.mkₐ k I
  refine Submodule.smul_induction_on
    (p := fun y => ambientCoefficients n g y = 0) hx ?_ ?_
  · intro a ha y _
    rw [Algebra.smul_def, map_mul, ambientCoefficients, transportedCoefficients_scalar]
    have h : g a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr ha
    rw [h, map_zero, zero_mul]
  · intro x y hx hy
    rw [map_add, hx, hy, add_zero]

private theorem conjugation_swap {A : Type*} [Monoid A] (a : Aˣ) (x y : A)
    (h : a.val * x * ↑a⁻¹ = y) : (↑a⁻¹ : A) * y * a.val = x := by
  rw [← h]
  simp only [mul_assoc, Units.inv_mul, Units.inv_mul_cancel_left, mul_one]

include hI in
private theorem stabilizer_lift (h₂ : (2 : k) = 0) (hn : 0 < n)
    (p : stabilizerSubgroup (ambientForm k n) (ambientBasis k n) (markedVector k n) (S ⧸ I)) :
    ∃ l : stabilizerSubgroup (ambientForm k n) (ambientBasis k n) (markedVector k n) S,
      stabilizerMap (S := S) (T := S ⧸ I) (ambientForm k n) (ambientBasis k n) (markedVector k n)
        (Ideal.Quotient.mkₐ k I) l = p := by
  let Q := ambientForm k n
  let b := ambientBasis k n
  let r := markedVector k n
  let P := ambientForm S n
  let w₀ := markedVector S n
  let w'₀ := markedVector (S ⧸ I) n
  let e := ambientCliffordEquiv k S n
  let e' := ambientCliffordEquiv k (S ⧸ I) n
  let g := Ideal.Quotient.mkₐ k I
  let F := ambientCoefficients n g
  obtain ⟨a, ha⟩ := ambientSpin_lift n I hI p.val
  let A := Units.map e.toMonoidHom a.val
  let A' := Units.map e'.toMonoidHom p.val.val
  have hA : IsIntrinsicSpin P A := (nativeClifford_spin Q P _ a.val).mp a.property
  have hA' : Units.map F.toMonoidHom A = A' := by
    apply Units.ext
    change F (e a.val.val) = e' p.val.val.val
    rw [ambientCoefficients_apply]
    exact congrArg (fun x : SpinFunctor.Spin Q (S ⧸ I) b => e' x.val.val) ha
  obtain ⟨w, hw⟩ := hA.2.2.1 (LinearMap.mem_range_self (CliffordAlgebra.ι P) w₀)
  change CliffordAlgebra.ι P w = A.val * CliffordAlgebra.ι P w₀ * ↑A⁻¹ at hw
  have hc' : Commute (CliffordAlgebra.ι (ambientForm (S ⧸ I) n) w'₀) A'.val := by
    have h := p.property
    change Commute (markedClifford Q r (S ⧸ I)) p.val.val.val at h
    have hm := h.map e'
    rwa [ambientCliffordEquiv_marked] at hm
  have hw₀ : (fun j => g (w₀ j)) = w'₀ := by
    funext j
    simp [w₀, w'₀, markedVector_single, Pi.single_apply]
  have hw' : (fun j => g (w j)) = w'₀ := by
    apply intrinsic_vector_injective n
    have hx := congrArg F hw
    change F (CliffordAlgebra.ι P w) = F (A.val * CliffordAlgebra.ι P w₀ * ↑A⁻¹) at hx
    rw [map_mul, map_mul, show F (CliffordAlgebra.ι P w) = _ from ambientCoefficients_vector n g w,
      show F (CliffordAlgebra.ι P w₀) = _ from ambientCoefficients_vector n g w₀, hw₀] at hx
    change CliffordAlgebra.ι _ (fun j => g (w j)) = (Units.map F.toMonoidHom A).val * CliffordAlgebra.ι _ w'₀ *
      (Units.map F.toMonoidHom A⁻¹).val at hx
    rw [map_inv, hA', ← hc'.eq, mul_assoc, Units.mul_inv, mul_one] at hx
    exact hx
  let v := w - w₀
  have hv (j : AmbientIndex n) : v j ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change g (w j - w₀ j) = 0
    rw [map_sub, congrFun hw' j, congrFun hw₀ j, sub_self]
  have hnorm : P w = P w₀ := by
    apply scalar_injective P (Pi.basisFun S (AmbientIndex n))
    rw [← ι_sq_scalar, ← ι_sq_scalar, hw]
    change _ = CliffordAlgebra.ι P w₀ * CliffordAlgebra.ι P w₀
    calc
      _ = A.val * (CliffordAlgebra.ι P w₀ * CliffordAlgebra.ι P w₀) * ↑A⁻¹ := by
        simp only [mul_assoc, Units.inv_mul_cancel_left]
      _ = _ := by
        rw [ι_sq_scalar, ← Algebra.commutes, mul_assoc, Units.mul_inv, mul_one]
  have hvadd : w₀ + v = w := by simp [v, add_comm w₀ w]
  have hvnorm : P v = 0 := ambientVector_squareZero n I hI v hv
  have hperp : P.polarBilin w₀ v = 0 := by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, hvadd, hnorm, sub_self, hvnorm, sub_zero]
  have h₂S : (2 : S) = 0 := by
    simpa only [map_ofNat, map_zero] using congrArg (algebraMap k S) h₂
  obtain ⟨C, hC, hnear, hact⟩ := squareZeroOrbitLifting S n h₂S hn I hI v hv hperp
  rw [hvadd] at hact
  have hC' : Units.map F.toMonoidHom C = 1 := by
    apply Units.ext
    have hz := ambientCoefficients_kills (k := k) n I (C.val - 1) hnear
    change F (C.val - 1) = 0 at hz
    rw [map_sub, map_one, sub_eq_zero] at hz
    exact hz
  obtain ⟨c, hc⟩ := (Units.mapEquiv e.toMulEquiv).surjective C
  let c₁ : SpinFunctor.Spin Q S b := ⟨c, (nativeClifford_spin Q P _ c).mpr (hc.symm ▸ hC)⟩
  have hmapc : SpinFunctor.map Q b g c₁ = 1 := by
    apply Subtype.ext
    apply Units.ext
    apply e'.injective
    change e' (SpinFunctor.changeCoefficients Q g c.val) = e' 1
    rw [← ambientCoefficients_apply, map_one, show e c.val = C.val from congrArg Units.val hc]
    exact congrArg Units.val hC'
  let l := c₁⁻¹ * a
  have hl : Commute (markedClifford Q r S) l.val.val := by
    apply e.injective
    rw [map_mul, map_mul, ambientCliffordEquiv_marked]
    have hvₗ : e l.val.val = (C⁻¹ * A).val := by
      change e (c⁻¹ * a.val).val = _
      rw [show e (c⁻¹ * a.val).val = (Units.map e.toMonoidHom (c⁻¹ * a.val)).val from rfl,
        map_mul, map_inv]
      exact congrArg Units.val (congrArg (fun z => z⁻¹ * A) hc)
    rw [hvₗ]
    let d := C⁻¹ * A
    have hd : d.val * CliffordAlgebra.ι P w₀ * ↑d⁻¹ = CliffordAlgebra.ι P w₀ := by
      change (C⁻¹ * A).val * CliffordAlgebra.ι P w₀ * ↑(C⁻¹ * A)⁻¹ = _
      rw [unit_conjugate_mul, ← hw]
      exact conjugation_swap C _ _ hact
    have hh := congrArg (fun x : CliffordAlgebra P => x * d.val) hd
    exact Eq.symm (by simpa only [mul_assoc, Units.inv_mul, mul_one] using hh)
  refine ⟨⟨l, hl⟩, Subtype.ext ?_⟩
  change SpinFunctor.map Q b g (c₁⁻¹ * a) = p.val
  rw [map_mul, map_inv, hmapc, inv_one, one_mul, ha]

private theorem ambientRing_smooth (k : Type u) [Field k] (n : ℕ) :
    Algebra.Smooth k (SpinRing (ambientForm k n) (ambientBasis k n)) := by
  let Q := ambientForm k n
  let b := ambientBasis k n
  refine ⟨Algebra.FormallySmooth.iff_comp_surjective.mpr ?_, inferInstance⟩
  intro S _ _ I hI p
  let g := Ideal.Quotient.mkₐ k I
  obtain ⟨a, ha⟩ := ambientSpin_lift n I hI (SpinFunctor.pointEquiv Q b (S ⧸ I) p)
  let f := (SpinFunctor.pointEquiv Q b S).symm a
  refine ⟨f, (SpinFunctor.pointEquiv Q b (S ⧸ I)).injective ?_⟩
  change SpinFunctor.pointEquiv Q b (S ⧸ I) (g.comp f) = _
  rw [SpinFunctor.pointEquiv_natural, Equiv.apply_symm_apply, ha]

private theorem stabilizerRing_smooth (k : Type u) [Field k] (n : ℕ) (h₂ : (2 : k) = 0)
    (hn : 0 < n) :
    Algebra.Smooth k (StabilizerRing (ambientForm k n) (ambientBasis k n) (markedVector k n)) := by
  let Q := ambientForm k n
  let b := ambientBasis k n
  let r := markedVector k n
  refine ⟨Algebra.FormallySmooth.iff_comp_surjective.mpr ?_, ?_⟩
  · intro S _ _ I hI p
    let g := Ideal.Quotient.mkₐ k I
    obtain ⟨a, ha⟩ := stabilizer_lift n I hI h₂ hn (stabilizerPointEquiv Q b r (S ⧸ I) p)
    let f := (stabilizerPointEquiv Q b r S).symm a
    refine ⟨f, (stabilizerPointEquiv Q b r (S ⧸ I)).injective ?_⟩
    change stabilizerPointEquiv Q b r (S ⧸ I) (g.comp f) = _
    have hf (x : StabilizerRing Q b r →ₐ[k] S) :
        stabilizerPointEquiv Q b r (S ⧸ I) (g.comp x) =
          stabilizerMap Q b r g (stabilizerPointEquiv Q b r S x) :=
      Subtype.ext (SpinFunctor.pointEquiv_natural Q b g (x.comp (stabilizerQuotient Q b r)))
    rw [hf, Equiv.apply_symm_apply, ha]
  · apply Algebra.FinitePresentation.quotient
    exact Submodule.fg_span (Set.finite_range _)

theorem smoothSchemeStabilizer : SmoothSchemeStabilizer.{u} := by
  intro k _ n h₂ hn
  let Q := ambientForm k n
  let b := ambientBasis k n
  let r := markedVector k n
  refine ⟨SpinFunctor.spinScheme Q b, stabScheme Q b r, stabInclusion Q b r,
    spinUnitPoints Q b, spinUnitPoints_represents Q b, SpinFunctor.spinScheme_affine Q b,
    stabScheme_affine Q b r, ?_, ?_, stabInclusion_closed Q b r, stabScheme_points Q b r⟩
  · change Smooth (Spec.map (CommRingCat.ofHom (algebraMap k (SpinRing Q b))))
    exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
      (RingHom.smooth_algebraMap.mpr (ambientRing_smooth k n))
  · change Smooth (Spec.map (CommRingCat.ofHom (algebraMap k (StabilizerRing Q b r))))
    exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
      (RingHom.smooth_algebraMap.mpr (stabilizerRing_smooth k n h₂ hn))

end StabilizerSmoothness

section MarkedOrthogonalScheme

open scoped Matrix TensorProduct CategoryTheory.MonObj
open AlgebraicGeometry CategoryTheory Opposite SpinSpecification
open LinearAlgebraicGroups.Specs.StandardGroups (GLCoordinates)
open private glEvaluation glEvaluation_entry glCoordinates_ext evaluatedGeneralLinear
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.StandardGroups
open private specPointsMulEquiv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinFunctor

variable {R T : Type u} [CommRing R] [CommRing T] {n : ℕ}

private theorem oddForm_apply (x : OddModule R n) :
    oddForm R n x = (∑ i : Fin n, x (↑(toLex (Sum.inl i) : Lex (SplitSpinSpecification.PairIndex n))) *
      x (↑(toLex (Sum.inr i) : Lex (SplitSpinSpecification.PairIndex n)))) + x ⊤ ^ 2 := by
  change ambientForm R n (extendOdd R n x) = _
  rw [ambientForm_apply]
  simp only [eIndex, fIndex, rIndex, extendOdd_top, extendOdd_coe, add_zero, pow_two]

private theorem oddForm_map (f : R →+* T) (x : OddModule R n) :
    oddForm T n (fun j => f (x j)) = f (oddForm R n x) := by
  simp only [oddForm_apply, map_add, map_sum, map_mul, map_pow]

private def oddApply (M : Matrix (OddMatrixIndex.{u} n) (OddMatrixIndex.{u} n) R)
    (x : OddModule R n) : OddModule R n := fun i => (M *ᵥ (fun j => x j.down)) (ULift.up i)

private theorem oddBasis_repr (x : OddModule R n) :
    ⇑((oddBasis R n).repr x) = fun j => x j.down := by
  funext j
  rw [oddBasis, Basis.repr_reindex_apply, Pi.basisFun_repr]
  rfl

private theorem oddApply_linear (M : Matrix (OddMatrixIndex.{u} n) (OddMatrixIndex.{u} n) R)
    (x : OddModule R n) : Matrix.toLin (oddBasis R n) (oddBasis R n) M x = oddApply M x := by
  apply (oddBasis R n).equivFun.injective
  ext i
  change ((oddBasis R n).repr (Matrix.toLin (oddBasis R n) (oddBasis R n) M x)) i =
    ((oddBasis R n).repr (oddApply M x)) i
  rw [Matrix.repr_toLin, oddBasis_repr, oddBasis_repr]
  rfl

private theorem oddMatrixAction_apply (g : Matrix.GeneralLinearGroup (OddMatrixIndex.{u} n) R)
    (x : OddModule R n) : oddMatrixAction g x = oddApply g.val x := by
  exact oddApply_linear g.val x

private theorem oddApply_map (f : R →+* T) (M : Matrix (OddMatrixIndex.{u} n) (OddMatrixIndex.{u} n) R)
    (x : OddModule R n) : oddApply (M.map f) (fun j => f (x j)) = fun j => f (oddApply M x j) := by
  funext i
  simp only [oddApply, Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply, map_mul]

private theorem oddBasis_map (f : R →+* T) (i : OddMatrixIndex.{u} n) :
    (fun j => f ((oddBasis R n) i j)) = (oddBasis T n) i := by
  classical
  funext j
  simp [oddBasis, Pi.basisFun_apply, Pi.single_apply]

private theorem radicalVector_map (f : R →+* T) :
    (fun j => f (radicalVector R n j)) = radicalVector T n := by
  classical
  funext j
  simp [Pi.single_apply]

private theorem quadraticMap_eq_of_basis {I : Type*} [Fintype I] [LinearOrder I]
    {V : Type*} [AddCommGroup V] [Module R V]
    (b : Basis I R V) (p q : QuadraticForm R V)
    (h : ∀ i, p (b i) = q (b i)) (hp : ∀ i j, p (b i + b j) = q (b i + b j)) : p = q := by
  rw [← p.toQuadraticMap_toBilin b, ← q.toQuadraticMap_toBilin b]
  congr 1
  apply b.ext
  intro i
  apply b.ext
  intro j
  simp only [QuadraticMap.toBilin_apply, h, QuadraticMap.polar, hp]

private abbrev OddTestIndex (n : ℕ) :=
  (OddMatrixIndex.{u} n ⊕ (OddMatrixIndex.{u} n × OddMatrixIndex.{u} n)) ⊕ OddIndex n

private def oddTestVector (R : Type u) [CommRing R]
    (p : OddMatrixIndex.{u} n ⊕ (OddMatrixIndex.{u} n × OddMatrixIndex.{u} n)) : OddModule R n :=
  p.elim (oddBasis R n) (fun ij => oddBasis R n ij.1 + oddBasis R n ij.2)

private theorem oddTestVector_map (f : R →+* T)
    (p : OddMatrixIndex.{u} n ⊕ (OddMatrixIndex.{u} n × OddMatrixIndex.{u} n)) :
    (fun j => f (oddTestVector R p j)) = oddTestVector T p := by
  cases p with
  | inl i => exact oddBasis_map f i
  | inr ij =>
    funext j
    simp only [oddTestVector, Sum.elim_inr, Pi.add_apply, map_add]
    rw [congrFun (oddBasis_map f ij.1) j, congrFun (oddBasis_map f ij.2) j]

private def orthogonalEquations (M : Matrix (OddMatrixIndex.{u} n) (OddMatrixIndex.{u} n) R)
    (p : OddTestIndex.{u} n) : R :=
  p.elim (fun a => oddForm R n (oddApply M (oddTestVector R a)) - oddForm R n (oddTestVector R a))
    (fun i => oddApply M (radicalVector R n) i - radicalVector R n i)

private theorem orthogonalEquations_map (f : R →+* T)
    (M : Matrix (OddMatrixIndex.{u} n) (OddMatrixIndex.{u} n) R) (p : OddTestIndex.{u} n) :
    orthogonalEquations (M.map f) p = f (orthogonalEquations M p) := by
  cases p with
  | inl a =>
    simp only [orthogonalEquations, Sum.elim_inl, map_sub, ← oddForm_map f]
    rw [← oddTestVector_map f, oddApply_map]
  | inr i =>
    simp only [orthogonalEquations, Sum.elim_inr, map_sub]
    rw [← radicalVector_map f, oddApply_map]

private theorem mem_marked_iff (g : Matrix.GeneralLinearGroup (OddMatrixIndex.{u} n) R) :
    g ∈ MarkedIsometries R n ↔ ∀ p, orthogonalEquations g.val p = 0 := by
  change ((∀ x, oddForm R n (oddMatrixAction g x) = oddForm R n x) ∧
    oddMatrixAction g (radicalVector R n) = radicalVector R n) ↔ _
  constructor
  · rintro ⟨h, hr⟩ (a | i)
    · exact sub_eq_zero.mpr (by simpa only [oddMatrixAction_apply] using h (oddTestVector R a))
    · exact sub_eq_zero.mpr (by simpa only [oddMatrixAction_apply] using congrFun hr i)
  · intro h
    have hq : (oddForm R n).comp (oddMatrixAction g).toLinearMap = oddForm R n := by
      apply quadraticMap_eq_of_basis (oddBasis R n)
      · intro i
        have hi := sub_eq_zero.mp (h (Sum.inl (Sum.inl i)))
        change oddForm R n (oddMatrixAction g (oddBasis R n i)) = _
        rwa [oddMatrixAction_apply]
      · intro i j
        have hi := sub_eq_zero.mp (h (Sum.inl (Sum.inr (i, j))))
        change oddForm R n (oddMatrixAction g (oddBasis R n i + oddBasis R n j)) = _
        rwa [oddMatrixAction_apply]
    refine ⟨fun x => congrArg (fun p : QuadraticForm R _ => p x) hq, ?_⟩
    funext i
    exact (congrFun (oddMatrixAction_apply g (radicalVector R n)) i).trans
      (sub_eq_zero.mp (h (Sum.inr i)))

private def markedMap (n : ℕ) (f : R →+* T) : MarkedIsometries R n →* MarkedIsometries T n :=
  ((Matrix.GeneralLinearGroup.map f).comp (MarkedIsometries R n).subtype).codRestrict
    (MarkedIsometries T n) fun a => (mem_marked_iff _).mpr fun p => by
      change orthogonalEquations (a.val.val.map f) p = 0
      rw [orthogonalEquations_map, (mem_marked_iff _).mp a.property p, map_zero]

variable (k : Type u) [Field k] (n : ℕ)

private abbrev OddGL := GLCoordinates k (OddMatrixIndex.{u} n)
private abbrev universalOddMatrix := LinearAlgebraicGroups.StandardGroups.universalMatrix k (OddMatrixIndex.{u} n)

private def oddIsometryIdeal : Ideal (OddGL k n) :=
  Ideal.span (Set.range (orthogonalEquations (universalOddMatrix k n)))

private abbrev OddIsometryRing := OddGL k n ⧸ oddIsometryIdeal k n

private abbrev oddIsometryQuotient : OddGL k n →ₐ[k] OddIsometryRing k n :=
  Ideal.Quotient.mkₐ k (oddIsometryIdeal k n)

private theorem evaluatedGeneralLinear_glEvaluation {S : Type u} [CommRing S] [Algebra k S]
    (g : Matrix.GeneralLinearGroup (OddMatrixIndex.{u} n) S) :
    evaluatedGeneralLinear (glEvaluation g : OddGL k n →ₐ[k] S) = g := by
  ext i j
  exact glEvaluation_entry g i j

private theorem oddIdeal_zero {S : Type u} [CommRing S] [Algebra k S]
    (f : OddGL k n →ₐ[k] S) : evaluatedGeneralLinear f ∈ MarkedIsometries S n ↔
      ∀ a ∈ oddIsometryIdeal k n, f a = 0 := by
  rw [mem_marked_iff]
  change (∀ p, orthogonalEquations ((universalOddMatrix k n).map f.toRingHom) p = 0) ↔
    oddIsometryIdeal k n ≤ RingHom.ker f.toRingHom
  simp_rw [orthogonalEquations_map]
  rw [oddIsometryIdeal, Ideal.span_le]
  simp [Set.range_subset_iff, RingHom.mem_ker]

private def markedPointEquiv (S : Type u) [CommRing S] [Algebra k S] :
    (OddIsometryRing k n →ₐ[k] S) ≃ MarkedIsometries S n where
  toFun f := ⟨evaluatedGeneralLinear (f.comp (oddIsometryQuotient k n)),
    (oddIdeal_zero k n _).mpr fun a ha => by
      change f (Ideal.Quotient.mk (oddIsometryIdeal k n) a) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]⟩
  invFun g := Ideal.Quotient.liftₐ (oddIsometryIdeal k n) (glEvaluation g.val)
    ((oddIdeal_zero k n _).mp (by rw [evaluatedGeneralLinear_glEvaluation]; exact g.property))
  left_inv f := by
    apply AlgHom.ext
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective k (oddIsometryIdeal k n) x
    change glEvaluation (evaluatedGeneralLinear (f.comp (oddIsometryQuotient k n))) x = _
    have hf : glEvaluation (evaluatedGeneralLinear (f.comp (oddIsometryQuotient k n))) =
        f.comp (oddIsometryQuotient k n) := by
      apply glCoordinates_ext
      intro i j
      exact glEvaluation_entry _ i j
    rw [hf]
    rfl
  right_inv g := by
    apply Subtype.ext
    change evaluatedGeneralLinear ((Ideal.Quotient.liftₐ _ _ _).comp _) = g.val
    rw [Ideal.Quotient.liftₐ_comp, evaluatedGeneralLinear_glEvaluation]

private theorem markedPointEquiv_natural {S T : Type u} [CommRing S] [CommRing T]
    [Algebra k S] [Algebra k T] (f : S →ₐ[k] T) (p : OddIsometryRing k n →ₐ[k] S) :
    markedPointEquiv k n T (f.comp p) = markedMap n f.toRingHom (markedPointEquiv k n S p) := by
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intros
  rfl

private def markedFunctor : ((CommAlgCat.{u} k)ᵒᵖ)ᵒᵖ ⥤ GrpCat.{u} where
  obj S := GrpCat.of (MarkedIsometries S.unop.unop n)
  map f := GrpCat.ofHom (markedMap n f.unop.unop.hom.toRingHom)
  map_id S := by
    apply GrpCat.ext
    intro a
    exact Subtype.ext (congrFun (congrArg DFunLike.coe Matrix.GeneralLinearGroup.map_id) a.val)
  map_comp f g := by
    apply GrpCat.ext
    intro a
    exact Subtype.ext (Matrix.GeneralLinearGroup.map_comp_apply f.unop.unop.hom.toRingHom
      g.unop.unop.hom.toRingHom a.val)

private abbrev markedObject : (CommAlgCat.{u} k)ᵒᵖ := op (CommAlgCat.of k (OddIsometryRing k n))

private def markedRepresentation : (markedFunctor k n ⋙ forget _).RepresentableBy (markedObject k n) where
  homEquiv {S} :=
    { toFun := fun f => markedPointEquiv k n S.unop f.unop.hom
      invFun := fun g => (CommAlgCat.ofHom ((markedPointEquiv k n S.unop).symm g)).op
      left_inv := by intro f; simp
      right_inv := fun g => (markedPointEquiv k n S.unop).apply_symm_apply g }
  homEquiv_comp f g := markedPointEquiv_natural k n f.unop.hom g.unop.hom

local instance markedGroup : GrpObj (markedObject k n) := GrpObj.ofRepresentableBy _ _ (markedRepresentation k n)
local instance : (algSpec (CommRingCat.of k)).Braided := AlgebraicGeometry.braidedAlgSpec

private abbrev markedScheme : GroupScheme k :=
  ((algSpec (CommRingCat.of k)).mapGrp).obj (Grp.mk (markedObject k n))

private def markedSchemePoints (S : CommAlgCat.{u} k) :
    SchemePoints (markedScheme k n) S ≃* MarkedIsometries S n :=
  let e := yonedaGrpObjIsoOfRepresentableBy (markedObject k n) _ (markedRepresentation k n)
  (specPointsMulEquiv S).symm.trans ((e.app (op (op S))).groupIsoToMulEquiv)

private theorem markedSchemePoints_onSpec {S : CommAlgCat.{u} k} (p : op S ⟶ markedObject k n) :
    markedSchemePoints k n S ((algSpec (CommRingCat.of k)).map p) = markedPointEquiv k n S p.unop.hom := by
  let e := specPointsMulEquiv (X := markedObject k n) S
  let f := (markedRepresentation k n).homEquiv (X := op S)
  change f (e.symm (e p)) = f p
  rw [MulEquiv.symm_apply_apply]

private theorem markedSchemePoints_natural {S T : CommAlgCat.{u} k} (f : S ⟶ T)
    (p : SchemePoints (markedScheme k n) S) :
    markedSchemePoints k n T ((algSpec (CommRingCat.of k)).map f.op ≫ p) =
      markedMap n f.hom.toRingHom (markedSchemePoints k n S p) := by
  obtain ⟨a, rfl⟩ := (specPointsMulEquiv (X := markedObject k n) S).surjective p
  let F := algSpec (CommRingCat.of k)
  change markedSchemePoints k n T (F.map f.op ≫ F.map a) =
    markedMap n f.hom.toRingHom (markedSchemePoints k n S (F.map a))
  have h := congrArg (markedSchemePoints k n T) (F.map_comp f.op a)
  exact h.symm.trans ((markedSchemePoints_onSpec k n (f.op ≫ a)).trans
    ((markedPointEquiv_natural k n f.hom a.unop.hom).trans
      (congrArg (markedMap n f.hom.toRingHom) (markedSchemePoints_onSpec k n a).symm)))

private theorem markedScheme_affine : IsAffine (markedScheme k n).X.left := by
  change IsAffine (Spec (CommRingCat.of (OddIsometryRing k n)))
  infer_instance

private theorem markedRing_finitePresentation : Algebra.FinitePresentation k (OddIsometryRing k n) := by
  apply Algebra.FinitePresentation.quotient
  exact Submodule.fg_span (Set.finite_range _)

private theorem markedScheme_finitePresentation : LocallyOfFinitePresentation (markedScheme k n).X.hom := by
  change LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap k (OddIsometryRing k n))))
  exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mpr
    (RingHom.finitePresentation_algebraMap.mpr (markedRing_finitePresentation k n))

theorem markedIsometryScheme : MarkedIsometryScheme.{u} := by
  intro k _ n _
  exact ⟨markedScheme k n, markedSchemePoints k n, markedScheme_affine k n,
    markedScheme_finitePresentation k n, fun f p => congrArg Subtype.val (markedSchemePoints_natural k n f p)⟩

end MarkedOrthogonalScheme

section MarkedOrthogonalSmoothness

open scoped Matrix TensorProduct CategoryTheory.MonObj
open AlgebraicGeometry CategoryTheory Opposite SpinSpecification

variable {S : Type u} [CommRing S] {V : Type*} [AddCommGroup V] [Module S V]
  {L : Type*} [Fintype L] (b : Basis L S V) (I : Ideal S)

private theorem linear_mem_of_basis (f : V →ₗ[S] S) (H : ∀ i, f (b i) ∈ I) (x : V) : f x ∈ I := by
  rw [← b.sum_repr x, map_sum]
  exact I.sum_mem (fun i _ => by rw [map_smul]; exact I.smul_mem _ (H i))

private theorem linear_kills_squareZero (hI : I ^ 2 = ⊥) (f : V →ₗ[S] S)
    (H : ∀ i, f (b i) ∈ I) (x : V) (hx : ∀ i, b.repr x i ∈ I) : f x = 0 := by
  rw [← b.sum_repr x, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [map_smul, smul_eq_mul]
  exact mul_eq_zero_of_squareZero I hI (hx i) (H i)

variable (n : ℕ) (hI : I ^ 2 = ⊥)

include hI in
/-- Correct the quadratic defect of a lifted linear map that fixes the norm-one line. -/
private theorem odd_isometry_correction (h₂ : (2 : S) = 0)
    (g : OddModule S n →ₗ[S] OddModule S n) (hg : g (radicalVector S n) = radicalVector S n)
    (hdef : ∀ x, oddForm S n x - oddForm S n (g x) ∈ I) :
    ∃ X : OddModule S n →ₗ[S] OddModule S n,
      X (radicalVector S n) = 0 ∧ (∀ x i, X x i ∈ I) ∧
        ∀ x, oddForm S n (g (x + X x)) = oddForm S n x := by
  classical
  let q := oddForm S n
  let r := radicalVector S n
  let d := Pi.basisFun S (OddIndex n)
  let D := q - q.comp g
  let B := D.toBilin d
  have hrb : d ⊤ = r := Pi.basisFun_apply _ _ _
  have hrad : q.polarBilin r = 0 := by
    have h := (splitHyperplane S n h₂).2.2.2.2
    have hz : r ∈ LinearMap.ker q.polarBilin := by
      rw [h]
      exact Submodule.mem_span_singleton_self r
    exact hz
  have hradd (x : OddModule S n) : q (r + x) = q r + q x := by
    rw [QuadraticMap.map_add q r x, ← QuadraticMap.polarBilin_apply_apply, hrad,
      LinearMap.zero_apply, add_zero]
  have hDr : D r = 0 := by
    change q r - q (g r) = 0
    rw [hg, sub_self]
  have hDp (x : OddModule S n) : QuadraticMap.polar D r x = 0 := by
    rw [QuadraticMap.polar, hDr, sub_zero]
    change q (r + x) - q (g (r + x)) - (q x - q (g x)) = 0
    rw [g.map_add, hg, hradd, hradd]
    abel
  have hBk₁ : B r = 0 := by
    apply d.ext
    intro i
    change B r (d i) = 0
    rw [← hrb]
    change D.toBilin d (d ⊤) (d i) = 0
    rw [QuadraticMap.toBilin_apply]
    simp [hrb, hDr, hDp]
  have hBk₂ (x : OddModule S n) : B x r = 0 := by
    have h : B.flip r = 0 := by
      apply d.ext
      intro i
      change B (d i) r = 0
      rw [← hrb]
      change D.toBilin d (d i) (d ⊤) = 0
      rw [QuadraticMap.toBilin_apply]
      by_cases hi : i = ⊤
      · subst i
        simp [hrb, hDr]
      · rw [if_neg hi, QuadraticMap.polar_comm D, hrb, hDp]
        simp
    exact LinearMap.congr_fun h x
  have hB₀ (i j : OddIndex n) : B (d i) (d j) ∈ I := by
    simp only [B, QuadraticMap.toBilin_apply]
    split_ifs
    · exact hdef _
    · exact I.sub_mem (I.sub_mem (hdef _) (hdef _)) (hdef _)
    · exact I.zero_mem
  have hB₁ (i : OddIndex n) (x : OddModule S n) : B (d i) x ∈ I :=
    linear_mem_of_basis d I (B (d i)) (hB₀ i) x
  have hB₂ (x y : OddModule S n) : B x y ∈ I :=
    linear_mem_of_basis d I (B.flip y) (fun i => hB₁ i y) x
  let β (i : OddIndex n) : OddModule S n :=
    if hi : i = ⊤ then 0 else (odd_polar_coordinates (n := n) h₂ i hi).choose
  have hβ (i : OddIndex n) (hi : i ≠ ⊤) : q.polarBilin (β i) = d.coord i := by
    simpa only [β, dif_neg hi] using (odd_polar_coordinates (n := n) h₂ i hi).choose_spec
  let X : OddModule S n →ₗ[S] OddModule S n := ∑ i, (B (d i)).smulRight (β i)
  have hX (x : OddModule S n) : X x = ∑ i, (B (d i)) x • β i := by
    simp only [X, LinearMap.sum_apply, LinearMap.smulRight_apply]
  have hX₀ (x : OddModule S n) (i : OddIndex n) : X x i ∈ I := by
    rw [hX, Finset.sum_apply]
    apply I.sum_mem
    intro j _
    exact I.mul_mem_right _ (hB₁ j x)
  refine ⟨X, ?_, hX₀, fun x => ?_⟩
  · change X r = 0
    rw [hX]
    simp only [hBk₂, zero_smul, Finset.sum_const_zero]
  · have hDX : D (x + X x) = D x := by
      rw [← D.toQuadraticMap_toBilin d]
      change B (x + X x) (x + X x) = B x x
      have hz (a : OddModule S n) : B a (X x) = 0 :=
        linear_kills_squareZero d I hI (B a) (fun i => hB₂ a (d i)) _ (hX₀ x)
      have hz' (a : OddModule S n) : B (X x) a = 0 :=
        linear_kills_squareZero d I hI (B.flip a) (fun i => hB₁ i a) _ (hX₀ x)
      rw [map_add B, LinearMap.add_apply, map_add, hz, hz', add_zero, add_zero]
    have hqX : q (X x) = 0 := by
      apply ambientVector_squareZero n I hI (extendOdd S n (X x))
      intro i
      cases i using WithTop.recTopCoe with
      | top => exact I.zero_mem
      | coe j => exact hX₀ x j
    have hpX : q.polarBilin x (X x) = D x := by
      have hb : B x x = D x := congrArg (fun P : QuadraticForm S _ => P x) (D.toQuadraticMap_toBilin d)
      calc
        _ = ∑ i, (B (d i)) x * d.repr x i := by
          rw [hX, map_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [map_smul, smul_eq_mul]
          by_cases hi : i = ⊤
          · subst i
            rw [hrb, hBk₁, LinearMap.zero_apply, zero_mul, zero_mul]
          · congr 1
            rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm,
              ← QuadraticMap.polarBilin_apply_apply, hβ i hi, Basis.coord_apply]
        _ = B.flip x (∑ i, d.repr x i • d i) := by
          rw [map_sum]
          simp only [map_smul, smul_eq_mul]
          apply Finset.sum_congr rfl
          intro i _
          exact mul_comm _ _
        _ = B x x := by rw [d.sum_repr]; rfl
        _ = D x := hb
    have hq : q (x + X x) = q x + D x := by
      rw [QuadraticMap.map_add q x (X x), ← QuadraticMap.polarBilin_apply_apply, hpX, hqX, add_zero]
    change q (g (x + X x)) = q x
    calc
      _ = q (x + X x) - D (x + X x) := by
        change q (g (x + X x)) = q (x + X x) - (q (x + X x) - q (g (x + X x)))
        exact (sub_sub_cancel _ _).symm
      _ = q x := by rw [hq, hDX, add_sub_cancel_right]

private theorem oddApply_quotient_lift (n : ℕ) (I : Ideal S)
    (a : MarkedIsometries (S ⧸ I) n) :
    ∃ g : OddModule S n →ₗ[S] OddModule S n,
      g (radicalVector S n) = radicalVector S n ∧
      ∀ x, (fun j => Ideal.Quotient.mk I (g x j)) =
        oddMatrixAction a.val (fun j => Ideal.Quotient.mk I (x j)) := by
  let f := Ideal.Quotient.mk I
  let M : Matrix (OddMatrixIndex.{u} n) (OddMatrixIndex.{u} n) S :=
    fun i j => (Ideal.Quotient.mk_surjective (a.val.val i j)).choose
  have hM : M.map f = a.val.val := Matrix.ext fun i j =>
    (Ideal.Quotient.mk_surjective (a.val.val i j)).choose_spec
  let L := Matrix.toLin (oddBasis S n) (oddBasis S n) M
  have hL (x : OddModule S n) : (fun j => f (L x j)) =
      oddMatrixAction a.val (fun j => f (x j)) := by
    change (fun j => f (Matrix.toLin (oddBasis S n) (oddBasis S n) M x j)) = _
    rw [oddApply_linear, oddMatrixAction_apply, ← hM, oddApply_map]
  let r := radicalVector S n
  let g : OddModule S n →ₗ[S] OddModule S n := L + (LinearMap.proj ⊤).smulRight (r - L r)
  have hc : (fun j => f ((r - L r) j)) = 0 := by
    have h := hL r
    rw [radicalVector_map, a.property.2] at h
    funext j
    change f (r j - L r j) = 0
    rw [map_sub, congrFun h j, congrFun (radicalVector_map (n := n) f) j, sub_self]
  refine ⟨g, ?_, fun x => ?_⟩
  · simp only [g, LinearMap.add_apply, LinearMap.smulRight_apply, LinearMap.proj_apply]
    change L r + r ⊤ • (r - L r) = r
    rw [show r ⊤ = 1 by simp [r], one_smul, add_comm, sub_add_cancel]
  · rw [← hL x]
    funext j
    change f (L x j + x ⊤ * ((r - L r) j)) = _
    rw [map_add, map_mul, congrFun hc j, Pi.zero_apply, mul_zero, add_zero]

variable {k : Type u} [Field k]

private theorem oddMatrixAction_entry (g : Matrix.GeneralLinearGroup (OddMatrixIndex.{u} n) S)
    (i j : OddMatrixIndex.{u} n) : oddMatrixAction g (oddBasis S n j) i.down = g.val i j := by
  have h := congrArg (fun M : Matrix (OddMatrixIndex.{u} n) (OddMatrixIndex.{u} n) S => M i j)
    (LinearMap.toMatrix_toLin (oddBasis S n) (oddBasis S n) g.val)
  change LinearMap.toMatrix (oddBasis S n) (oddBasis S n)
    (Matrix.toLin (oddBasis S n) (oddBasis S n) g.val) i j = _ at h
  rw [LinearMap.toMatrix_apply, congrFun (oddBasis_repr _) i] at h
  exact h

private theorem markedPoint_lift (n : ℕ) (I : Ideal S) (hI : I ^ 2 = ⊥)
    (h₂ : (2 : S) = 0) (a : MarkedIsometries (S ⧸ I) n) :
    ∃ l : MarkedIsometries S n, markedMap n (Ideal.Quotient.mk I) l = a := by
  let f := Ideal.Quotient.mk I
  let q := oddForm S n
  let r := radicalVector S n
  obtain ⟨g, hgr, hg⟩ := oddApply_quotient_lift n I a
  have hdef (x : OddModule S n) : q x - q (g x) ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change f (q x - q (g x)) = 0
    rw [map_sub, ← oddForm_map f x, ← oddForm_map f (g x), hg x, a.property.1, sub_self]
  obtain ⟨X, hXr, hXI, hX⟩ := odd_isometry_correction I n hI h₂ g hgr hdef
  let L : OddModule S n →ₗ[S] OddModule S n := g.comp (LinearMap.id + X)
  let M := LinearMap.toMatrix (oddBasis S n) (oddBasis S n) L
  have hbar (x : OddModule S n) : (fun j => f (L x j)) =
      oddMatrixAction a.val (fun j => f (x j)) := by
    change (fun j => f (g (x + X x) j)) = _
    rw [hg]
    congr 1
    funext j
    change f (x j + X x j) = _
    rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr (hXI x j), add_zero]
  have hM : M.map f = a.val.val := by
    ext i j
    have h := congrFun (hbar (oddBasis S n j)) i.down
    rw [oddBasis_map f j] at h
    change f (LinearMap.toMatrix (oddBasis S n) (oddBasis S n) L i j) = _
    rw [LinearMap.toMatrix_apply, congrFun (oddBasis_repr _) i, h]
    exact oddMatrixAction_entry n a.val i j
  have hu : IsUnit M.det := by
    apply (IsNilpotent.isUnit_quotient_mk_iff (I := I) ⟨2, hI⟩).mp
    change IsUnit (f M.det)
    rw [f.map_det]
    change IsUnit (M.map f).det
    rw [hM]
    exact (Matrix.GeneralLinearGroup.det a.val).isUnit
  let u := Matrix.GeneralLinearGroup.mk'' M hu
  have happ (x : OddModule S n) : oddMatrixAction u x = L x := by
    change Matrix.toLin _ _ M x = _
    rw [Matrix.toLin_toMatrix]
  refine ⟨⟨u, (show (∀ x, q (oddMatrixAction u x) = q x) ∧ oddMatrixAction u r = r from ?_)⟩, ?_⟩
  · refine ⟨fun x => by rw [happ]; exact hX x, ?_⟩
    rw [happ]
    change g (r + X r) = r
    rwa [hXr, add_zero]
  · exact Subtype.ext (Matrix.GeneralLinearGroup.ext fun i j => congrArg (fun m : Matrix _ _ _ => m i j) hM)

private theorem markedRing_smooth (k : Type u) [Field k] (n : ℕ) (h₂ : (2 : k) = 0) :
    Algebra.Smooth k (OddIsometryRing k n) := by
  refine ⟨Algebra.FormallySmooth.iff_comp_surjective.mpr ?_, markedRing_finitePresentation k n⟩
  intro T _ _ I hI p
  let f := Ideal.Quotient.mkₐ k I
  have h₂T : (2 : T) = 0 := by simpa only [map_ofNat, map_zero] using congrArg (algebraMap k T) h₂
  obtain ⟨a, ha⟩ := markedPoint_lift n I hI h₂T (markedPointEquiv k n (T ⧸ I) p)
  let l := (markedPointEquiv k n T).symm a
  refine ⟨l, (markedPointEquiv k n (T ⧸ I)).injective ?_⟩
  change markedPointEquiv k n (T ⧸ I) (f.comp l) = _
  rw [markedPointEquiv_natural, Equiv.apply_symm_apply]
  exact ha

end MarkedOrthogonalSmoothness

section RestrictionToMarkedSpace

open AlgebraicGeometry CategoryTheory Opposite SpinSpecification
open scoped Matrix TensorProduct CategoryTheory.MonObj
open private changeModule changeModule_coord coordinateObject algebraRepresentation specPointsMulEquiv
  schemePoints_onSpec spinUnitPoints spinUnitPoints_represents
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinFunctor

variable {k : Type u} [Field k] (n : ℕ) {S T : Type u} [CommRing S] [CommRing T]
  [Algebra k S] [Algebra k T]

private abbrev oddCoordinates (k S : Type u) [CommRing k] [CommRing S] [Algebra k S] (n : ℕ) :=
  coordinatesOver k S (OddIndex n)

private theorem oddCoordinates_marked :
    oddCoordinates k S n (1 ⊗ₜ[k] radicalVector k n) = radicalVector S n := by
  funext j
  rw [coordinatesOver_tmul, mul_one]
  exact congrFun (radicalVector_map (n := n) (algebraMap k S)) j

private theorem oddCoordinates_change (f : S →ₐ[k] T) (x : S ⊗[k] OddModule k n) :
    oddCoordinates k T n (changeModule f x) = fun j => f (oddCoordinates k S n x j) := by
  funext j
  exact changeModule_coord (Pi.basisFun k (OddIndex n)) f x j

private theorem oddCoordinates_preserves (x : S ⊗[k] OddModule k n) :
    oddForm S n (oddCoordinates k S n x) = ExtendedForm (oddForm k n) S (oddBasis k n) x := by
  have h : (oddForm S n).comp (oddCoordinates k S n).toLinearMap =
      ExtendedForm (oddForm k n) S (oddBasis k n) := by
    apply (CliffordModel.coefficient_form_unique S (oddForm k n) (oddBasis k n) _).mpr
    intro y
    change oddForm S n (oddCoordinates k S n (1 ⊗ₜ[k] y)) = _
    rw [show oddCoordinates k S n (1 ⊗ₜ[k] y) = (fun j => algebraMap k S (y j)) by
      funext j
      rw [coordinatesOver_tmul, mul_one]]
    exact odd_map n y
  exact congrArg (fun F : QuadraticForm S _ => F x) h

private abbrev OddSpin (k S : Type u) [Field k] [CommRing S] [Algebra k S] (n : ℕ) :=
  SpinFunctor.Spin (oddForm k n) S (oddBasis k n)

private def oddVectorAction : OddSpin k S n →* (OddModule S n ≃ₗ[S] OddModule S n) where
  toFun a := (oddCoordinates k S n).symm.trans
    ((SpinFunctor.vectorAction (oddForm k n) S (oddBasis k n) a).trans (oddCoordinates k S n))
  map_one' := by
    apply LinearEquiv.ext
    intro x
    change oddCoordinates k S n (SpinFunctor.vectorAction (oddForm k n) S (oddBasis k n) 1
      ((oddCoordinates k S n).symm x)) = x
    rw [map_one]
    exact LinearEquiv.apply_symm_apply _ _
  map_mul' a b := by
    apply LinearEquiv.ext
    intro x
    let e := oddCoordinates k S n
    let ρ := SpinFunctor.vectorAction (oddForm k n) S (oddBasis k n)
    change e (ρ (a * b) (e.symm x)) = e (ρ a (e.symm (e (ρ b (e.symm x)))))
    rw [map_mul, LinearEquiv.mul_apply, LinearEquiv.symm_apply_apply]

private theorem oddVectorAction_preserves (a : OddSpin k S n) (x : OddModule S n) :
    oddForm S n (oddVectorAction n a x) = oddForm S n x := by
  obtain ⟨y, rfl⟩ := (oddCoordinates k S n).surjective x
  change oddForm S n (oddCoordinates k S n (SpinFunctor.vectorAction _ S _ a
    ((oddCoordinates k S n).symm (oddCoordinates k S n y)))) = _
  rw [LinearEquiv.symm_apply_apply, oddCoordinates_preserves, oddCoordinates_preserves,
    SpinFunctor.vectorAction_preserves]

private theorem oddVectorAction_fixes (h₂ : (2 : k) = 0) (a : OddSpin k S n) :
    oddVectorAction n a (radicalVector S n) = radicalVector S n := by
  let q := oddForm k n
  let b := oddBasis k n
  let r := radicalVector k n
  have hr : r ∈ LinearMap.ker q.polarBilin := by
    rw [(splitHyperplane k n h₂).2.2.2.2]
    exact Submodule.mem_span_singleton_self r
  have h := SpinFunctor.charTwoRadicalActionSpecification q b S h₂ a.val
    (SpinFunctor.vectorAction q S b a) (SpinFunctor.vectorAction_characterization q S b a) r hr
  rw [← oddCoordinates_marked (k := k) n]
  change oddCoordinates k S n (SpinFunctor.vectorAction q S b a
    ((oddCoordinates k S n).symm (oddCoordinates k S n (1 ⊗ₜ[k] r)))) = _
  rw [LinearEquiv.symm_apply_apply, h]

private theorem oddVectorAction_natural (f : S →ₐ[k] T) (a : OddSpin k S n) (x : OddModule S n) :
    oddVectorAction n (SpinFunctor.map (oddForm k n) (oddBasis k n) f a) (fun j => f (x j)) =
      fun j => f (oddVectorAction n a x j) := by
  let q := oddForm k n
  let b := oddBasis k n
  let y := (oddCoordinates k S n).symm x
  have hy : oddCoordinates k S n y = x := LinearEquiv.apply_symm_apply _ _
  rw [← hy, ← oddCoordinates_change n f y]
  change oddCoordinates k T n (SpinFunctor.vectorAction q T b (SpinFunctor.map q b f a)
    ((oddCoordinates k T n).symm (oddCoordinates k T n (changeModule f y)))) =
    (fun j => f (oddCoordinates k S n (SpinFunctor.vectorAction q S b a
      ((oddCoordinates k S n).symm (oddCoordinates k S n y))) j))
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply,
    ← SpinFunctor.vectorAction_naturality, oddCoordinates_change]

private theorem oddVectorAction_conjugates (a : OddSpin k S n) (x : OddModule S n) :
    let e := nativeClifford (oddForm k n) (oddForm S n) (odd_map n)
    let A := Units.map e.toMonoidHom a.val
    CliffordAlgebra.ι (oddForm S n) (oddVectorAction n a x) =
      A.val * CliffordAlgebra.ι (oddForm S n) x * ↑A⁻¹ := by
  let q := oddForm k n
  let b := oddBasis k n
  let e := nativeClifford q (oddForm S n) (odd_map n)
  let y := (oddCoordinates k S n).symm x
  dsimp only
  have h := congrArg e (SpinFunctor.vectorAction_characterization q S b a y)
  change e (vectors q S (SpinFunctor.vectorAction q S b a y)) =
    e (a.val.val * vectors q S y * ↑a.val⁻¹) at h
  rw [map_mul, map_mul, nativeClifford_vector, nativeClifford_vector] at h
  change _ = e a.val.val * CliffordAlgebra.ι (oddForm S n) (oddCoordinates k S n y) * _ at h
  rwa [show oddCoordinates k S n y = x from LinearEquiv.apply_symm_apply _ _] at h

private def markedAction (h₂ : (2 : k) = 0) : OddSpin k S n →* MarkedIsometries S n :=
  ((oddMatrixAction (R := S) (n := n)).symm.toMonoidHom.comp (oddVectorAction n)).codRestrict _ (fun a => by
    change (∀ x, oddForm S n (oddMatrixAction (oddMatrixAction.symm (oddVectorAction n a)) x) =
      oddForm S n x) ∧ oddMatrixAction (oddMatrixAction.symm (oddVectorAction n a)) (radicalVector S n) = _
    rw [MulEquiv.apply_symm_apply]
    exact ⟨oddVectorAction_preserves n a, oddVectorAction_fixes n h₂ a⟩)

private theorem markedAction_natural (h₂ : (2 : k) = 0) (f : S →ₐ[k] T) (a : OddSpin k S n) :
    markedAction n h₂ (SpinFunctor.map (oddForm k n) (oddBasis k n) f a) =
      markedMap n f.toRingHom (markedAction n h₂ a) := by
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  let a' := SpinFunctor.map (oddForm k n) (oddBasis k n) f a
  have h := congrFun (oddVectorAction_natural n f a (oddBasis S n j)) i.down
  rw [show (fun j' => f (oddBasis S n j j')) = oddBasis T n j from oddBasis_map f.toRingHom j] at h
  change (markedAction n h₂ a').val.val i j = f ((markedAction n h₂ a).val.val i j)
  rw [← oddMatrixAction_entry n _ i j, ← oddMatrixAction_entry n _ i j]
  change oddMatrixAction (oddMatrixAction.symm (oddVectorAction n a')) (oddBasis T n j) i.down =
    f (oddMatrixAction (oddMatrixAction.symm (oddVectorAction n a)) (oddBasis S n j) i.down)
  rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  exact h

private theorem markedAction_surj (h₂ : (2 : k) = 0) (K : Type u) [Field K] [IsAlgClosed K] [Algebra k K] :
    Function.Surjective (markedAction (S := K) n h₂) := by
  let q := oddForm k n
  let P := oddForm K n
  let e := nativeClifford q P (odd_map n)
  have h₂K : (2 : K) = 0 := by simpa only [map_ofNat, map_zero] using congrArg (algebraMap k K) h₂
  intro g
  obtain ⟨A, hA, hact⟩ := geometricIntrinsicRestriction K n h₂K (oddMatrixAction g.val) g.property.1
  obtain ⟨a, ha⟩ := (Units.mapEquiv e.toMulEquiv).surjective A
  let a' : OddSpin k K n := ⟨a, (nativeClifford_spin q P _ a).mpr (ha.symm ▸ hA)⟩
  refine ⟨a', Subtype.ext (oddMatrixAction.injective (LinearEquiv.ext fun x => ?_))⟩
  let G := (CliffordModel.vector_summand P (Pi.basisFun K (OddIndex n))).choose
  have hG : Function.LeftInverse G (CliffordAlgebra.ι P) :=
    LinearMap.congr_fun (CliffordModel.vector_summand P (Pi.basisFun K (OddIndex n))).choose_spec
  have hc := oddVectorAction_conjugates n a' x
  change CliffordAlgebra.ι P (oddVectorAction n a' x) =
    (Units.map e.toMonoidHom a).val * CliffordAlgebra.ι P x * ↑(Units.map e.toMonoidHom a)⁻¹ at hc
  rw [show Units.map e.toMonoidHom a = A from ha, hact] at hc
  change (oddMatrixAction (oddMatrixAction.symm (oddVectorAction n a'))) x = _
  rw [MulEquiv.apply_symm_apply]
  exact hG.injective hc

private abbrev oddCliffordMap (k S : Type u) [Field k] [CommRing S] [Algebra k S] (n : ℕ) :
    ScalarClifford (oddForm k n) S →ₐ[S] ScalarClifford (ambientForm k n) S :=
  Algebra.TensorProduct.map (AlgHom.id S S) (CliffordAlgebra.map (inclusion k n))

private def oddSpinToStabilizer (h₂ : (2 : k) = 0) : OddSpin k S n →*
    stabilizerSubgroup (ambientForm k n) (ambientBasis k n) (markedVector k n) S where
  toFun a :=
    let h := ((tensorSpinComparison k n h₂ S).2.1 a.val).mp a.property
    ⟨⟨Units.map (oddCliffordMap k S n).toMonoidHom a.val, h.1⟩, h.2⟩
  map_one' := Subtype.ext (Subtype.ext (map_one _))
  map_mul' a b := Subtype.ext (Subtype.ext (map_mul _ a.val b.val))

private theorem oddSpinToStabilizer_natural (h₂ : (2 : k) = 0) (f : S →ₐ[k] T) (a : OddSpin k S n) :
    oddSpinToStabilizer n h₂ (SpinFunctor.map (oddForm k n) (oddBasis k n) f a) =
      stabilizerMap (ambientForm k n) (ambientBasis k n) (markedVector k n) f (oddSpinToStabilizer n h₂ a) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  exact ((tensorSpinComparison k n h₂ S).2.2.2.2 T f a.val.val).symm

private theorem oddSpinToStabilizer_bijective (h₂ : (2 : k) = 0) :
    Function.Bijective (oddSpinToStabilizer (S := S) n h₂) := by
  let h := tensorSpinComparison k n h₂ S
  refine ⟨?_, ?_⟩
  · intro a b hab
    apply Subtype.ext
    apply Units.ext
    exact h.1 (congrArg (fun t : stabilizerSubgroup (ambientForm k n) (ambientBasis k n)
      (markedVector k n) S => t.val.val.val) hab)
  · intro a
    obtain ⟨b, hb, _⟩ := h.2.2.1 a.val.val a.val.property a.property
    exact ⟨⟨b, hb.1⟩, Subtype.ext (Subtype.ext hb.2)⟩

end RestrictionToMarkedSpace

section RestrictionMorphisms

open AlgebraicGeometry CategoryTheory Opposite SpinSpecification
open scoped TensorProduct CategoryTheory.MonObj
open private coordinateObject algebraRepresentation specPointsMulEquiv schemePoints_onSpec
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinFunctor
open private isReduced_of_smooth_algebra from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SmoothnessCriteria

variable (k : Type u) [Field k] (n : ℕ) (h₂ : (2 : k) = 0)

private abbrev ambientStabilizerObject := stabObject (ambientForm k n) (ambientBasis k n) (markedVector k n)
private abbrev ambientStabilizerRing := StabilizerRing (ambientForm k n) (ambientBasis k n) (markedVector k n)
private abbrev ambientStabilizerFunctor := stabilizerFunctor (ambientForm k n) (ambientBasis k n) (markedVector k n)
private abbrev ambientStabilizerRepresentation := stabRepresentation (ambientForm k n) (ambientBasis k n) (markedVector k n)

local instance : GrpObj (ambientStabilizerObject k n) := stabGroup (ambientForm k n) (ambientBasis k n) (markedVector k n)
local instance : GrpObj (markedObject k n) := markedGroup k n
local instance : GrpObj (coordinateObject (oddForm k n) (oddBasis k n)) :=
  GrpObj.ofRepresentableBy _ _ (algebraRepresentation (oddForm k n) (oddBasis k n))
local instance : (algSpec (CommRingCat.of k)).Braided := AlgebraicGeometry.braidedAlgSpec

private def oddSpinStabilizerIso : SpinFunctor.pointsFunctor (oddForm k n) (oddBasis k n) ≅
    ambientStabilizerFunctor k n :=
  NatIso.ofComponents (fun S => (MulEquiv.ofBijective (oddSpinToStabilizer (S := S.unop.unop) n h₂)
    (oddSpinToStabilizer_bijective n h₂)).toGrpIso) <| by
    intro S T f
    apply GrpCat.ext
    intro a
    exact oddSpinToStabilizer_natural n h₂ f.unop.unop.hom a

set_option maxRecDepth 1500 in
private def oddMarkedNat : SpinFunctor.pointsFunctor (oddForm k n) (oddBasis k n) ⟶ markedFunctor k n where
  app S := GrpCat.ofHom (markedAction (S := S.unop.unop) n h₂)
  naturality _ _ f := by
    apply GrpCat.ext
    intro a
    exact markedAction_natural n h₂ f.unop.unop.hom a

private def stabMarkedNat : ambientStabilizerFunctor k n ⟶ markedFunctor k n :=
  (oddSpinStabilizerIso k n h₂).inv ≫ oddMarkedNat k n h₂

private def restrictPoint (S : Type u) [CommRing S] [Algebra k S] :
    stabilizerSubgroup (ambientForm k n) (ambientBasis k n) (markedVector k n) S →*
      MarkedIsometries S n :=
  (markedAction (S := S) n h₂).comp
    (MulEquiv.ofBijective (oddSpinToStabilizer (S := S) n h₂)
      (oddSpinToStabilizer_bijective n h₂)).symm.toMonoidHom

private def restrictionAlgNat : yonedaGrp.obj (Grp.mk (ambientStabilizerObject k n)) ⟶
    yonedaGrp.obj (Grp.mk (markedObject k n)) :=
  (yonedaGrpObjIsoOfRepresentableBy _ _ (ambientStabilizerRepresentation k n)).hom ≫
    stabMarkedNat k n h₂ ≫ (yonedaGrpObjIsoOfRepresentableBy _ _ (markedRepresentation k n)).inv

private def restrictionAlg : Grp.mk (ambientStabilizerObject k n) ⟶ Grp.mk (markedObject k n) :=
  yonedaGrpFullyFaithful.preimage (restrictionAlgNat k n h₂)

private def restrictionRingMap : OddIsometryRing k n →ₐ[k] ambientStabilizerRing k n :=
  (restrictionAlg k n h₂).hom.hom.unop.hom

private theorem restrictionAlg_points {S : CommAlgCat.{u} k} (p : op S ⟶ ambientStabilizerObject k n) :
    markedPointEquiv k n S (p.unop.hom.comp (restrictionRingMap k n h₂)) =
      (stabMarkedNat k n h₂).app (op (op S)) (stabilizerPointEquiv (ambientForm k n)
        (ambientBasis k n) (markedVector k n) S p.unop.hom) := by
  let e := ((yonedaGrpObjIsoOfRepresentableBy _ _ (markedRepresentation k n)).app
    (op (op S))).groupIsoToMulEquiv
  have h := congrArg (fun α => (α.app (op (op S))).hom p)
    (yonedaGrpFullyFaithful.map_preimage (restrictionAlgNat k n h₂))
  change p ≫ (restrictionAlg k n h₂).hom.hom = e.symm
    ((stabMarkedNat k n h₂).app (op (op S)) (stabilizerPointEquiv (ambientForm k n)
      (ambientBasis k n) (markedVector k n) S p.unop.hom)) at h
  exact (congrArg e h).trans (e.apply_symm_apply _)

set_option maxRecDepth 1500 in
private theorem stabMarkedNat_apply {S : CommAlgCat.{u} k}
    (a : stabilizerSubgroup (ambientForm k n) (ambientBasis k n) (markedVector k n) S) :
    (stabMarkedNat k n h₂).app (op (op S)) a = restrictPoint k n h₂ S a := rfl

private def restrictionToMarked : stabScheme (ambientForm k n) (ambientBasis k n) (markedVector k n) ⟶
    markedScheme k n :=
  ((algSpec (CommRingCat.of k)).mapGrp).map (restrictionAlg k n h₂)

set_option maxRecDepth 1024 in
private theorem restrictionAlg_surj_on_points (K : Type u) [Field K] [IsAlgClosed K] [Algebra k K] :
    Function.Surjective (fun p : ambientStabilizerRing k n →ₐ[k] K => p.comp (restrictionRingMap k n h₂)) := by
  let S := CommAlgCat.of k K
  intro q
  obtain ⟨a, ha⟩ := markedAction_surj n h₂ K (markedPointEquiv k n K q)
  let t := oddSpinToStabilizer (S := K) n h₂ a
  let g := (stabilizerPointEquiv (ambientForm k n) (ambientBasis k n) (markedVector k n) K).symm t
  refine ⟨g, (markedPointEquiv k n K).injective ?_⟩
  have hp := restrictionAlg_points k n h₂ (CommAlgCat.ofHom g).op
  change markedPointEquiv k n K (g.comp (restrictionRingMap k n h₂)) = _ at hp
  refine hp.trans ((stabMarkedNat_apply k n h₂ (S := S) _).trans ?_)
  change restrictPoint k n h₂ K
    ((stabilizerPointEquiv (ambientForm k n) (ambientBasis k n) (markedVector k n) K) g) = _
  rw [Equiv.apply_symm_apply]
  let e := MulEquiv.ofBijective (oddSpinToStabilizer (S := K) n h₂)
    (oddSpinToStabilizer_bijective n h₂)
  change markedAction n h₂ (e.symm (e a)) = _
  rw [MulEquiv.symm_apply_apply]
  exact ha

private theorem restrictionRingMap_injective : Function.Injective (restrictionRingMap k n h₂) := by
  let D := OddIsometryRing k n
  let f := restrictionRingMap k n h₂
  letI : Algebra.Smooth k D := markedRing_smooth k n h₂
  letI : _root_.IsReduced D := isReduced_of_smooth_algebra k D
  apply (RingHom.injective_iff_ker_eq_bot f.toRingHom).mpr
  apply le_antisymm _ bot_le
  intro x hx
  have hx' : f x = 0 := RingHom.mem_ker.mp hx
  have hnil : x ∈ nilradical D := by
    rw [nilradical_eq_sInf]
    apply Ideal.mem_sInf.mpr
    intro p hp
    letI : p.IsPrime := hp
    let F := p.ResidueField
    let K := AlgebraicClosure F
    let j := (algebraMap F K).comp (algebraMap D F)
    letI : Algebra k K := (j.comp (algebraMap k D)).toAlgebra
    let q : D →ₐ[k] K := { j with commutes' := fun _ => rfl }
    obtain ⟨g, hg⟩ := restrictionAlg_surj_on_points k n h₂ K q
    have hq : q x = 0 := by rw [← hg, AlgHom.comp_apply, hx', map_zero]
    have hbar : algebraMap D F x = 0 := by
      apply (algebraMap F K).injective
      exact hq.trans (map_zero (algebraMap F K)).symm
    exact (Ideal.ker_algebraMap_residueField p) ▸ RingHom.mem_ker.mpr hbar
  exact Ideal.mem_bot.mpr (IsNilpotent.eq_zero hnil)

private abbrev markedHopf : CommHopfAlgCat (CommRingCat.of k) :=
  (commHopfAlgCatEquivCogrpCommAlgCat (CommRingCat.of k)).inverse.obj (op (Grp.mk (markedObject k n)))

private abbrev stabHopf : CommHopfAlgCat (CommRingCat.of k) :=
  (commHopfAlgCatEquivCogrpCommAlgCat (CommRingCat.of k)).inverse.obj (op (Grp.mk (ambientStabilizerObject k n)))

private abbrev restrictionHopf : markedHopf k n ⟶ stabHopf k n :=
  (commHopfAlgCatEquivCogrpCommAlgCat (CommRingCat.of k)).inverse.map (restrictionAlg k n h₂).op

private theorem restrictionRingMap_faithfullyFlat :
    RingHom.FaithfullyFlat (R := OddIsometryRing k n) (S := ambientStabilizerRing k n)
      (restrictionRingMap k n h₂).toRingHom := by
  haveI : Algebra.FinitePresentation k (OddIsometryRing k n) := markedRing_finitePresentation k n
  haveI : Algebra.FinitePresentation k (ambientStabilizerRing k n) := by
    apply Algebra.FinitePresentation.quotient
    exact Submodule.fg_span (Set.finite_range _)
  haveI : Algebra.FiniteType k (markedHopf k n) :=
    inferInstanceAs (Algebra.FiniteType k (OddIsometryRing k n))
  haveI : Algebra.FiniteType k (stabHopf k n) :=
    inferInstanceAs (Algebra.FiniteType k (ambientStabilizerRing k n))
  exact LinearAlgebraicGroups.hopfFaithfulFlatness k (restrictionHopf k n h₂) (restrictionRingMap_injective k n h₂)

private theorem restriction_flat_surjective :
    Flat (restrictionToMarked k n h₂).hom.hom.left ∧ Surjective (restrictionToMarked k n h₂).hom.hom.left := by
  let f := CommRingCat.ofHom (R := OddIsometryRing k n) (S := ambientStabilizerRing k n)
    (restrictionRingMap k n h₂).toRingHom
  change Flat (Spec.map f) ∧ Surjective (Spec.map f)
  exact (flat_and_surjective_SpecMap_iff _).mpr (restrictionRingMap_faithfullyFlat k n h₂)

end RestrictionMorphisms

section RestrictionKernel

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite SpinSpecification WithConv
open scoped TensorProduct CategoryTheory.MonObj
open private precomposePoint quotientPoint_restrict quotientPointLift exists_relativeShear
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.HopfFaithfulFlatness

variable (k : Type u) [Field k] (n : ℕ) (h₂ : (2 : k) = 0)
variable {S T : Type u} [CommRing S] [CommRing T] [Algebra k S] [Algebra k T]

private abbrev StabilizerPoints (S : Type u) [CommRing S] [Algebra k S] :=
  stabilizerSubgroup (ambientForm k n) (ambientBasis k n) (markedVector k n) S

private abbrev stabilizedPoints (S : Type u) [CommRing S] [Algebra k S] :=
  stabilizerPointEquiv (ambientForm k n) (ambientBasis k n) (markedVector k n) S

private def stabilizerScalar (S : Type u) [CommRing S] [Algebra k S] :
    rootsOfUnity 2 S →* StabilizerPoints k n S :=
  (oddSpinToStabilizer n h₂).comp (SpinFunctor.scalarEmbedding (oddForm k n) S (oddBasis k n))

private theorem stabilizerScalar_val (t : rootsOfUnity 2 S) :
    (stabilizerScalar k n h₂ S t).val.val.val = algebraMap S _ (t.val : S) := by
  change oddCliffordMap k S n ((SpinFunctor.scalarEmbedding (oddForm k n) S (oddBasis k n) t).val.val) = _
  rw [SpinFunctor.scalarEmbedding_val, AlgHom.commutes]

private theorem stabilizerScalar_injective : Function.Injective (stabilizerScalar k n h₂ S) :=
  (oddSpinToStabilizer_bijective n h₂).1.comp (SpinFunctor.scalarEmbedding_injective _ _ _)

private theorem stabilizerScalar_natural (f : S →ₐ[k] T) (t : rootsOfUnity 2 S) :
    stabilizerMap (ambientForm k n) (ambientBasis k n) (markedVector k n) f (stabilizerScalar k n h₂ S t) =
      stabilizerScalar k n h₂ T (SpinFunctor.muTwoMap f t) := by
  rw [stabilizerScalar, MonoidHom.comp_apply, ← oddSpinToStabilizer_natural, SpinFunctor.scalarEmbedding_natural]
  rfl

private theorem markedAction_eq_one (a : OddSpin k S n) :
    markedAction n h₂ a = 1 ↔ SpinFunctor.vectorAction (oddForm k n) S (oddBasis k n) a = 1 := by
  let e := oddCoordinates k S n
  let ρ := SpinFunctor.vectorAction (oddForm k n) S (oddBasis k n)
  constructor
  · intro h
    have h' := congrArg (fun p : MarkedIsometries S n => oddMatrixAction p.val) h
    change oddMatrixAction (oddMatrixAction.symm (oddVectorAction n a)) = oddMatrixAction 1 at h'
    rw [MulEquiv.apply_symm_apply, map_one] at h'
    apply LinearEquiv.ext
    intro x
    apply e.injective
    have hx := congrArg (fun f : OddModule S n ≃ₗ[S] OddModule S n => f (e x)) h'
    change e (ρ a (e.symm (e x))) = e x at hx
    rwa [LinearEquiv.symm_apply_apply] at hx
  · intro h
    apply Subtype.ext
    apply oddMatrixAction.injective
    change oddMatrixAction (oddMatrixAction.symm (oddVectorAction n a)) = oddMatrixAction 1
    rw [MulEquiv.apply_symm_apply, map_one]
    apply LinearEquiv.ext
    intro x
    change e (ρ a (e.symm x)) = x
    rw [h]
    exact LinearEquiv.apply_symm_apply _ _

private theorem restrictPoint_eq_one (a : StabilizerPoints k n S) :
    restrictPoint k n h₂ S a = 1 ↔ ∃! t : rootsOfUnity 2 S, stabilizerScalar k n h₂ S t = a := by
  obtain ⟨b, rfl⟩ := (oddSpinToStabilizer_bijective n h₂).2 a
  let e := MulEquiv.ofBijective (oddSpinToStabilizer (S := S) n h₂) (oddSpinToStabilizer_bijective n h₂)
  change markedAction n h₂ (e.symm (e b)) = 1 ↔ _
  rw [MulEquiv.symm_apply_apply, markedAction_eq_one]
  constructor
  · intro hb
    let q := oddForm k n
    let r := radicalVector k n
    let c := oddBasis k n
    let h := splitHyperplane k n h₂
    have hq : LinearMap.ker q.polarBilin = ⊥ ∨
        ∃ r : OddModule k n, q r ≠ 0 ∧ LinearMap.ker q.polarBilin = k ∙ r :=
      Or.inr ⟨r, by rw [h.2.2.2.1]; exact one_ne_zero, h.2.2.2.2⟩
    obtain ⟨t, ht⟩ := (SpinFunctor.regularKernel q S c hq).surjective ⟨b, hb⟩
    have ht' : SpinFunctor.scalarEmbedding q S c t = b := by
      apply Subtype.ext
      apply Units.ext
      rw [SpinFunctor.scalarEmbedding_val]
      have hz := congrArg (fun p : (SpinFunctor.vectorAction q S c).ker => p.val.val.val) ht
      rw [SpinFunctor.regularKernel_val] at hz
      exact hz
    have hs : stabilizerScalar k n h₂ S t = e b := congrArg e ht'
    exact ⟨t, hs, fun z hz => stabilizerScalar_injective k n h₂ (hz.trans hs.symm)⟩
  · rintro ⟨t, ht, _⟩
    have ht' : SpinFunctor.scalarEmbedding (oddForm k n) S (oddBasis k n) t = b := e.injective ht
    rw [← ht', SpinFunctor.scalarEmbedding_trivial_action]

private theorem markedPointEquiv_counit :
    markedPointEquiv k n S ((Algebra.ofId k S).comp (Bialgebra.counitAlgHom k (markedHopf k n))) = 1 := by
  let B := CommAlgCat.of k S
  let e := ((yonedaGrpObjIsoOfRepresentableBy _ _ (markedRepresentation k n)).app (op (op B))).groupIsoToMulEquiv
  exact map_one e

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 1500 in
set_option maxHeartbeats 600000 in
private theorem restrictionRingMap_points (p : ambientStabilizerRing k n →ₐ[k] S) :
    markedPointEquiv k n S (p.comp (restrictionRingMap k n h₂)) =
      restrictPoint k n h₂ S (stabilizedPoints k n S p) :=
  by
    let A := CommAlgCat.of k S
    let q : op A ⟶ ambientStabilizerObject k n := (CommAlgCat.ofHom p).op
    exact (restrictionAlg_points k n h₂ q).trans (stabMarkedNat_apply k n h₂ (S := A) _)

private theorem precomposePoint_eq_one (p : ambientStabilizerRing k n →ₐ[k] S) :
    precomposePoint (restrictionHopf k n h₂).hom (toConv p) = 1 ↔
      restrictPoint k n h₂ S (stabilizedPoints k n S p) = 1 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have ht := congrArg (fun a : WithConv (OddIsometryRing k n →ₐ[k] S) => markedPointEquiv k n S a.ofConv) h
    exact (restrictionRingMap_points k n h₂ p).symm.trans (ht.trans (markedPointEquiv_counit k n))
  · apply WithConv.ofConv_injective
    apply (markedPointEquiv k n S).injective
    exact (restrictionRingMap_points k n h₂ p).trans (h.trans (markedPointEquiv_counit k n).symm)

private abbrev RestrictionKernelRing := stabHopf k n ⧸ Specs.kernelIdeal (restrictionHopf k n h₂)

private def scalarToKernelPoint (S : Type u) [CommRing S] [Algebra k S] (t : rootsOfUnity 2 S) :
    RestrictionKernelRing k n h₂ →ₐ[k] S :=
  let p := (stabilizedPoints k n S).symm (stabilizerScalar k n h₂ S t)
  quotientPointLift (restrictionHopf k n h₂) (toConv p) <|
    (precomposePoint_eq_one k n h₂ p).mpr ((restrictPoint_eq_one k n h₂ _).mpr
      ⟨t, ((stabilizedPoints k n S).apply_symm_apply _).symm, fun s hs =>
        stabilizerScalar_injective k n h₂ (hs.trans ((stabilizedPoints k n S).apply_symm_apply _))⟩)

private theorem scalarToKernelPoint_spec (t : rootsOfUnity 2 S) :
    (scalarToKernelPoint k n h₂ S t).comp (Ideal.Quotient.mkₐ k _) =
      (stabilizedPoints k n S).symm (stabilizerScalar k n h₂ S t) :=
  Ideal.Quotient.liftₐ_comp _ _ _

private theorem scalarToKernelPoint_bijective : Function.Bijective (scalarToKernelPoint k n h₂ S) := by
  constructor
  · intro s t ht
    apply stabilizerScalar_injective k n h₂
    apply (stabilizedPoints k n S).symm.injective
    rw [← scalarToKernelPoint_spec, ← scalarToKernelPoint_spec, ht]
  · intro p
    let π := Ideal.Quotient.mkₐ k (Specs.kernelIdeal (restrictionHopf k n h₂))
    have hp := quotientPoint_restrict (restrictionHopf k n h₂) p
    obtain ⟨t, ht, _⟩ := (restrictPoint_eq_one k n h₂ _).mp ((precomposePoint_eq_one k n h₂ (p.comp π)).mp hp)
    refine ⟨t, AlgHom.ext fun x => ?_⟩
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective k (Specs.kernelIdeal (restrictionHopf k n h₂)) x
    change ((scalarToKernelPoint k n h₂ S t).comp π) x = _
    rw [scalarToKernelPoint_spec, ht, Equiv.symm_apply_apply]
    rfl

private theorem scalarToKernelPoint_natural (f : S →ₐ[k] T) (t : rootsOfUnity 2 S) :
    f.comp (scalarToKernelPoint k n h₂ S t) = scalarToKernelPoint k n h₂ T (SpinFunctor.muTwoMap f t) := by
  let π := Ideal.Quotient.mkₐ k (Specs.kernelIdeal (restrictionHopf k n h₂))
  apply AlgHom.ext
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective k (Specs.kernelIdeal (restrictionHopf k n h₂)) x
  suffices h : (f.comp (scalarToKernelPoint k n h₂ S t)).comp π =
      (scalarToKernelPoint k n h₂ T (SpinFunctor.muTwoMap f t)).comp π from DFunLike.congr_fun h x
  rw [AlgHom.comp_assoc, scalarToKernelPoint_spec, scalarToKernelPoint_spec]
  apply (stabilizedPoints k n T).injective
  have hx (p : ambientStabilizerRing k n →ₐ[k] S) : stabilizedPoints k n T (f.comp p) =
      stabilizerMap (ambientForm k n) (ambientBasis k n) (markedVector k n) f (stabilizedPoints k n S p) :=
    Subtype.ext (SpinFunctor.pointEquiv_natural _ _ f (p.comp (stabilizerQuotient _ _ _)))
  refine (hx _).trans ?_
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, stabilizerScalar_natural]

private def kernelPointEquiv (S : Type u) [CommRing S] [Algebra k S] :
    (muTwoCoordinateRing k →ₐ[k] S) ≃ (RestrictionKernelRing k n h₂ →ₐ[k] S) :=
  (SpinFunctor.muTwoPoints k S).trans (Equiv.ofBijective _ (scalarToKernelPoint_bijective k n h₂))

private theorem kernelPointEquiv_natural (f : S →ₐ[k] T) (p : muTwoCoordinateRing k →ₐ[k] S) :
    kernelPointEquiv k n h₂ T (f.comp p) = f.comp (kernelPointEquiv k n h₂ S p) := by
  change scalarToKernelPoint k n h₂ T (SpinFunctor.muTwoPoints k T (f.comp p)) =
    f.comp (scalarToKernelPoint k n h₂ S (SpinFunctor.muTwoPoints k S p))
  rw [scalarToKernelPoint_natural]
  congr 1
  apply rootsOfUnity.coe_injective
  exact SpinFunctor.muTwoPoints_natural f p

private def muTwoKernelRingEquiv : muTwoCoordinateRing k ≃ₐ[k] RestrictionKernelRing k n h₂ := by
  let U := muTwoCoordinateRing k
  let A := RestrictionKernelRing k n h₂
  let g := kernelPointEquiv k n h₂ U (.id k U)
  let f := (kernelPointEquiv k n h₂ A).symm (.id k A)
  refine AlgEquiv.ofAlgHom f g ?_ ?_
  · have h := kernelPointEquiv_natural k n h₂ f (AlgHom.id k U)
    rw [AlgHom.comp_id, Equiv.apply_symm_apply] at h
    exact h.symm
  · apply (kernelPointEquiv k n h₂ U).injective
    rw [kernelPointEquiv_natural, Equiv.apply_symm_apply, AlgHom.comp_id]

set_option maxHeartbeats 400000 in
private theorem finite_of_finite_hopf_kernel {F : Type u} [Field F]
    {D A : CommHopfAlgCat (CommRingCat.of F)} (i : D ⟶ A)
    [Module.Finite F (A ⧸ Specs.kernelIdeal i)]
    (hf : i.hom.toAlgHom.toRingHom.FaithfullyFlat) : i.hom.toAlgHom.toRingHom.Finite := by
  letI : Algebra D A := i.hom.toAlgHom.toRingHom.toAlgebra
  haveI : Module.FaithfullyFlat D A := RingHom.faithfullyFlat_algebraMap_iff.mp hf
  obtain ⟨e, _⟩ := exists_relativeShear i (𝟙 A)
  letI : Algebra A (A ⊗[D] A) := Algebra.TensorProduct.leftAlgebra
  let e' : A ⊗[D] A ≃ₐ[A] A ⊗[F] (A ⧸ Specs.kernelIdeal i) := e
  haveI : Module.Finite A (A ⊗[D] A) := Module.Finite.of_surjective e'.symm.toLinearMap e'.symm.surjective
  exact RingHom.finite_algebraMap.mpr (Module.Finite.of_finite_tensorProduct_of_faithfullyFlat A)

set_option maxHeartbeats 500000 in
private theorem restriction_finite : IsFinite (restrictionToMarked k n h₂).hom.hom.left := by
  let Q := RestrictionKernelRing k n h₂
  have hmonic : (muTwoPolynomial k).Monic := by
    simpa only [Polynomial.C_1] using (Polynomial.monic_X_pow_sub_C (1 : k) (n := 2) (by decide))
  haveI : Module.Finite k (muTwoCoordinateRing k) := Module.Finite.of_basis (AdjoinRoot.powerBasis' hmonic).basis
  haveI : Module.Finite k Q := Module.Finite.of_surjective
    (muTwoKernelRingEquiv k n h₂).toLinearMap (muTwoKernelRingEquiv k n h₂).surjective
  have hfin := finite_of_finite_hopf_kernel (restrictionHopf k n h₂) (restrictionRingMap_faithfullyFlat k n h₂)
  change IsFinite (Spec.map (CommRingCat.ofHom (R := OddIsometryRing k n) (S := ambientStabilizerRing k n)
    (restrictionRingMap k n h₂).toRingHom))
  exact (IsFinite.SpecMap_iff _).mpr hfin

set_option maxHeartbeats 700000 in
set_option maxRecDepth 1400 in
private theorem restriction_radicial : UniversallyInjective (restrictionToMarked k n h₂).hom.hom.left := by
  let A := ambientStabilizerRing k n
  let B := OddIsometryRing k n
  let f := restrictionRingMap k n h₂
  change UniversallyInjective (Spec.map (CommRingCat.ofHom (R := B) (S := A) f.toRingHom))
  apply (tfae_universallyInjective _).out 2 1 |>.mp
  intro F _ p q hpq
  obtain ⟨a, rfl⟩ := Spec.map_surjective p
  obtain ⟨b, rfl⟩ := Spec.map_surjective q
  simp only [← Spec.map_comp] at hpq
  have hcomp : a.hom.comp f.toRingHom = b.hom.comp f.toRingHom :=
    congrArg CommRingCat.Hom.hom (Spec.map_injective hpq)
  let baseA : k →+* A := algebraMap k (ambientStabilizerRing k n)
  let baseB : k →+* B := algebraMap k (OddIsometryRing k n)
  letI : Algebra k F := (a.hom.comp baseA).toAlgebra
  let p₀ : A →ₐ[k] F := { a.hom with commutes' := fun _ => rfl }
  have hb (c : k) : b.hom (baseA c) = algebraMap k F c := by
    change b.hom (baseA c) = a.hom (baseA c)
    have hc : f (baseB c) = baseA c := f.commutes c
    rw [← hc]
    exact DFunLike.congr_fun hcomp.symm (baseB c)
  let q₀ : A →ₐ[k] F := { b.hom with commutes' := hb }
  have h : p₀.comp f = q₀.comp f := AlgHom.ext (fun x => DFunLike.congr_fun hcomp x)
  let x := stabilizedPoints k n F p₀
  let y := stabilizedPoints k n F q₀
  let ρ := restrictPoint k n h₂ F
  have hp : ρ x = ρ y :=
    (restrictionRingMap_points k n h₂ p₀).symm.trans
      ((congrArg (markedPointEquiv k n F) h).trans (restrictionRingMap_points k n h₂ q₀))
  have hxy : ρ (x⁻¹ * y) = 1 := by rw [map_mul, map_inv, hp, inv_mul_cancel]
  obtain ⟨t, ht, _⟩ := (restrictPoint_eq_one k n h₂ _).mp hxy
  have h₂F : (2 : F) = 0 := by simpa only [map_ofNat, map_zero] using congrArg (algebraMap k F) h₂
  have ht₀ : (t.val : F) = 1 := by
    have hsq := (mem_rootsOfUnity' 2 t.val).mp t.property
    have hz : ((t.val : F) - 1)^2 = 0 := by
      rw [sub_sq, h₂F, zero_mul, zero_mul, sub_zero, hsq, one_pow, ← two_mul, h₂F, zero_mul]
    exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hz)
  have ho : t = 1 := rootsOfUnity.coe_injective ht₀
  rw [ho, map_one] at ht
  have hpoints : x = y := (inv_mul_eq_one.mp ht.symm)
  have hab : p₀ = q₀ := (stabilizedPoints k n F).injective hpoints
  have he : a = b := CommRingCat.hom_ext (congrArg AlgHom.toRingHom hab)
  rw [he]

include h₂ in
private theorem restriction_geometricallyConnected (hconn : GeometricallyConnected (markedScheme k n).X.hom) :
    GeometricallyConnected (stabScheme (ambientForm k n) (ambientBasis k n) (markedVector k n)).X.hom := by
  let f := (restrictionToMarked k n h₂).hom.hom.left
  let g := (markedScheme k n).X.hom
  have ht := (restrictionToMarked k n h₂).hom.hom.w
  change f ≫ g = _ at ht
  rw [← ht]
  letI : IsFinite f := restriction_finite k n h₂
  letI : Surjective f := (restriction_flat_surjective k n h₂).2
  letI : UniversallyInjective f := restriction_radicial k n h₂
  letI : GeometricallyConnected g := hconn
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ s => ?_⟩
  rw [← (pullbackRightPullbackFstIso g s f).hom.homeomorph.connectedSpace_iff]
  let p := pullback.snd f (pullback.fst g s)
  haveI : UniversallyInjective p := UniversallyInjective.isStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback f (pullback.fst g s)) inferInstance
  have hhomeo : IsHomeomorph p := isHomeomorph_iff_isQuotientMap_injective.mpr
    ⟨p.isClosedMap.isQuotientMap p.continuous p.surjective, p.injective⟩
  exact (hhomeo.homeomorph p).connectedSpace_iff.mpr
    (GeometricallyConnected.geometrically_connectedSpace _ _ _ (.of_hasPullback g s))

end RestrictionKernel

section DiagonalPreimage

open scoped Matrix TensorProduct
open SplitSpinSpecification
open private splitCoordinates splitVector unitConj action_matrix_on_vectors
  factorUnit factorUnit_lift factorUnit_natural factorUnit_congr IsTensorLift
  map_isometry_evenOdd map_isometry_reverse from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SplitSpin
open private cliffordEquiv cliffordEquiv_even from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinFunctor
open private baseChangeEquiv_reverse from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.CliffordModel

variable {R : Type u} [CommRing R] (n : ℕ)

private def scaleCoordinates {D : Type*} (t : D → Rˣ) : (D → R) ≃ₗ[R] (D → R) where
  toFun x i := (t i : R) * x i
  invFun x i := (↑(t i)⁻¹ : R) * x i
  left_inv x := by
    funext i
    change (↑(t i)⁻¹ : R) * ((t i : R) * x i) = _
    rw [← mul_assoc, Units.inv_mul, one_mul]
  right_inv x := by
    funext i
    change (t i : R) * ((↑(t i)⁻¹ : R) * x i) = _
    rw [← mul_assoc, Units.mul_inv, one_mul]
  map_add' x y := by funext i; exact mul_add _ _ _
  map_smul' z x := by funext i; simp only [Pi.smul_apply, smul_eq_mul]; exact mul_left_comm _ _ _

private def planeScales (t : Fin n → Rˣ) : Fin (n + 1) → Rˣ := Fin.cases 1 t

private def ambientScale (t : Fin n → Rˣ) : AmbientModule R n ≃ₗ[R] AmbientModule R n :=
  (ambientCoordinates R n).trans <|
    (scaleCoordinates (Sum.elim (planeScales n t) (fun i => (planeScales n t i)⁻¹))).trans
      (ambientCoordinates R n).symm

private theorem ambientScale_onOdd (t : Fin n → Rˣ) (x : OddModule R n) :
    ambientScale n t (inclusion R n x) = inclusion R n (diagonalOddVector t x) := by
  apply (ambientCoordinates R n).injective
  change ambientCoordinates R n ((ambientCoordinates R n).symm
    (scaleCoordinates _ (ambientCoordinates R n (inclusion R n x)))) = _
  rw [LinearEquiv.apply_symm_apply]
  funext j
  cases j with
  | inl j =>
    cases j using Fin.cases with
    | zero => simp [scaleCoordinates, planeScales, ambientCoordinates, inclusion_apply, rIndex, diagonalOddVector]
    | succ j => rfl
  | inr j =>
    cases j using Fin.cases with
    | zero => simp [scaleCoordinates, planeScales, ambientCoordinates, inclusion_apply, rIndex, diagonalOddVector]
    | succ j => rfl

private theorem ambientScale_marked (t : Fin n → Rˣ) :
    ambientScale n t (markedVector R n) = markedVector R n := by
  rw [markedVector, ambientScale_onOdd]
  congr 1
  funext j
  cases j using WithTop.recTopCoe with
  | top => rfl
  | coe j =>
    obtain ⟨a, rfl⟩ := toLex.surjective j
    cases a <;> simp [diagonalOddVector, Pi.single_apply]

private theorem diagonal_middle_action (t : Fin n → Rˣ) (x : PairIndex (n + 1) → R) :
    middle (Matrix.diagonal (fun i => (planeScales n t i : R))) *ᵥ x =
      scaleCoordinates (Sum.elim (planeScales n t) (fun i => (planeScales n t i)⁻¹)) x := by
  let d := planeScales n t
  have hi : (Matrix.diagonal fun i => (d i : R))⁻¹ = Matrix.diagonal (fun i => (↑(d i)⁻¹ : R)) := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.diagonal_mul_diagonal]
    simp only [Units.mul_inv, Matrix.diagonal_one]
  rw [middle, hi, Matrix.diagonal_transpose, Matrix.fromBlocks_mulVec]
  simp only [Matrix.zero_mulVec, zero_add, add_zero]
  funext i
  cases i <;> simp only [Sum.elim_inl, Sum.elim_inr, Matrix.mulVec_diagonal] <;> rfl

private abbrev diagonalBlock (t : Fin n → Rˣ) : Block (n + 1) R :=
  Matrix.diagonal (fun i => (planeScales n t i : R))

private theorem diagonalBlock_det (t : Fin n → Rˣ) :
    (diagonalBlock n t).det = ∏ i, (t i : R) := by
  rw [Matrix.det_diagonal, Fin.prod_univ_succ]
  change (1 : R) * (∏ i, (t i : R)) = _
  rw [one_mul]

private theorem diagonalBlock_det_isUnit (t : Fin n → Rˣ) : IsUnit (diagonalBlock n t).det := by
  rw [diagonalBlock_det]
  exact ⟨∏ i, t i, by simp⟩

private def diagonalLift (t : Fin n → Rˣ) :
    (CliffordAlgebra (ambientForm R n))ˣ :=
  Units.map (integralAmbientClifford n R).toMonoidHom
    (factorUnit 0 0 (diagonalBlock n t) (diagonalBlock_det_isUnit n t))

set_option maxHeartbeats 700000 in
set_option maxRecDepth 1300 in
private theorem diagonalLift_spec (t : Fin n → Rˣ) :
    let b := diagonalLift n t
    b.val ∈ evenOdd (ambientForm R n) 0 ∧
    reverse b.val * b.val = algebraMap R _ (∏ i, (t i : R)) ∧
    ∀ x : AmbientModule R n, b.val * ι (ambientForm R n) x * ↑b⁻¹ =
      ι (ambientForm R n) (ambientScale n t x) := by
  let m := n + 1
  let Q := ambientForm R n
  let A := diagonalBlock n t
  let a := factorUnit 0 0 A (diagonalBlock_det_isUnit n t)
  let b := diagonalLift n t
  let q := integralForm m
  let d := hyperbolicBasis ℤ m
  let i := integralAmbientIsometry n R
  let E := integralAmbientClifford n R
  have hz : IsAlternating (0 : Block m R) := by
    intro x
    rw [Matrix.zero_mulVec, dotProduct_zero]
  have hl : lower (0 : Block m R) = 1 := by
    simpa only [lower] using (Matrix.fromBlocks_one : Matrix.fromBlocks
      (1 : Block m R) 0 0 1 = 1)
  have hu : upper (0 : Block m R) = 1 := by
    simpa only [upper] using (Matrix.fromBlocks_one : Matrix.fromBlocks
      (1 : Block m R) 0 0 1 = 1)
  have ha := factorUnit_lift 0 0 A hz hz (diagonalBlock_det_isUnit n t)
  rw [hl, hu, one_mul, mul_one] at ha
  change IsTensorLift (middle A) a A.det at ha
  have he : E a.val ∈ evenOdd Q 0 :=
    map_isometry_evenOdd i.toIsometry ((cliffordEquiv_even q R d a.val).mpr ha.1)
  have hr (x : SplitSpinSpecification.ScalarClifford m R) :
      E (SpinSpecification.reversion q R x) = reverse (E x) := by
    change CliffordAlgebra.map i.toIsometry (cliffordEquiv q R d (SpinSpecification.reversion q R x)) = _
    rw [show cliffordEquiv q R d (SpinSpecification.reversion q R x) =
      reverse (cliffordEquiv q R d x) from baseChangeEquiv_reverse R q d x, map_isometry_reverse]
    rfl
  refine ⟨he, ?_, ?_⟩
  · change reverse (E a.val) * E a.val = algebraMap R _ (∏ i, (t i : R))
    rw [← hr, ← map_mul, ha.2.1, E.commutes, diagonalBlock_det]
  · intro y
    obtain ⟨x, rfl⟩ := i.toLinearEquiv.surjective y
    have hh : HasActionMatrix m a (middle A) := ha.2.2
    have hv (z : ExtendedModule m R) : E (splitVector m R z) = ι Q (i.toLinearEquiv z) :=
      transportedClifford_vector q d i z
    have h := congrArg (fun z : SplitSpinSpecification.ScalarClifford m R => E z)
      (action_matrix_on_vectors hh x)
    simp only [unitConj, map_mul, hv] at h
    have hs : i.toLinearEquiv ((splitCoordinates m R).symm (middle A *ᵥ splitCoordinates m R x)) =
        ambientScale n t (i.toLinearEquiv x) := by
      change (ambientCoordinates R n).symm
        (splitCoordinates m R ((splitCoordinates m R).symm (middle A *ᵥ splitCoordinates m R x))) =
        (ambientCoordinates R n).symm
          (scaleCoordinates (Sum.elim (planeScales n t) (fun j => (planeScales n t j)⁻¹))
            (ambientCoordinates R n ((ambientCoordinates R n).symm (splitCoordinates m R x))))
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, diagonal_middle_action]
    exact h.trans (congrArg (ι Q) hs)

section LiftNaturality

variable {k S T : Type u} [Field k] [CommRing S] [CommRing T] [Algebra k S] [Algebra k T]

set_option maxHeartbeats 650000 in
private theorem diagonalLift_natural (f : S →ₐ[k] T) (t : Fin n → Sˣ) :
    diagonalLift n (fun j => Units.map f.toMonoidHom (t j)) =
      Units.map (ambientCoefficients n f).toMonoidHom (diagonalLift n t) := by
  let g := f.toRingHom.toIntAlgHom
  let w (j : Fin n) := Units.map f.toMonoidHom (t j)
  let A := diagonalBlock n t
  let B := diagonalBlock n w
  have hAB : A.map g = B := by
    rw [Matrix.diagonal_map (map_zero g)]
    congr 1
    funext j
    cases j using Fin.cases with
    | zero => exact map_one _
    | succ j => rfl
  have hz : (0 : Block (n + 1) S).map g = 0 := by ext i j; simp
  have hdet : IsUnit (A.map g).det := by
    rw [hAB]
    exact diagonalBlock_det_isUnit n w
  have hcong := factorUnit_congr (h := hdet) (h' := diagonalBlock_det_isUnit n w) hz hz hAB
  have h := hcong.symm.trans (factorUnit_natural g 0 0 A (diagonalBlock_det_isUnit n t) hdet)
  apply Units.ext
  change integralAmbientClifford n T (factorUnit 0 0 B (diagonalBlock_det_isUnit n w)).val =
    ambientCoefficients n f (integralAmbientClifford n S (factorUnit 0 0 A (diagonalBlock_det_isUnit n t)).val)
  rw [h]
  exact integralAmbientClifford_natural n f _


end LiftNaturality

private theorem scalar_mul_norm {V : Type*} [AddCommGroup V] [Module R V]
    {Q : QuadraticForm R V} (a : CliffordAlgebra Q) (s c : R)
    (hn : reverse a * a = algebraMap R _ c) :
    reverse (algebraMap R _ s * a) * (algebraMap R _ s * a) = algebraMap R _ (s ^ 2 * c) := by
  rw [reverse.map_mul, reverse.commutes, mul_assoc, ← mul_assoc (algebraMap R _ s),
    ← map_mul, ← pow_two, Algebra.commutes, ← mul_assoc, hn, ← map_mul]
  rw [mul_comm c]

set_option maxHeartbeats 700000 in
private theorem diagonalNormEquation_for_lift (h₂ : (2 : R) = 0) (t : Fin n → Rˣ) :
    let Q := ambientForm R n
    let J := inclusion R n
    let r := radicalVector R n
    let b := diagonalLift n t
    ∀ a : (CliffordAlgebra Q)ˣ,
      IsIntrinsicSpin Q a ∧ Commute (ι Q (J r)) a.val ∧
        (∀ x, a.val * ι Q (J x) * ↑a⁻¹ = ι Q (J (diagonalOddVector t x))) ↔
      ∃! u : Rˣ, (u : R) ^ 2 * (∏ i, (t i : R)) = 1 ∧
        a = Units.map (algebraMap R (CliffordAlgebra Q)).toMonoidHom u * b := by
  intro Q J r b
  let s := ∏ i, t i
  have hs : (s : R) = ∏ i, (t i : R) := by simp [s]
  obtain ⟨he, hn, hb⟩ := diagonalLift_spec n t
  have hn' : reverse b.val * b.val = algebraMap R _ (s : R) := by rwa [hs]
  have hbcomm : Commute (ι Q (J r)) b.val := by
    have h : b.val * ι Q (J r) * ↑b⁻¹ = ι Q (ambientScale n t (markedVector R n)) := hb (J r)
    rw [ambientScale_marked] at h
    have h' := congrArg (fun z : CliffordAlgebra Q => z * b.val) h
    exact Eq.symm (by simpa only [mul_assoc, Units.inv_mul, mul_one] using h')
  have hbOdd (x : OddModule R n) : b.val * ι Q (J x) * ↑b⁻¹ = ι Q (J (diagonalOddVector t x)) := by
    rw [hb, ambientScale_onOdd]
  have hinv : (↑b⁻¹ : CliffordAlgebra Q) = (↑s⁻¹ : R) • reverse b.val := by
    have hd : ((↑s⁻¹ : R) • reverse b.val) * b.val = 1 := by
      rw [smul_mul_assoc, hn', Algebra.smul_def, ← map_mul, Units.inv_mul, map_one]
    calc
      _ = (((↑s⁻¹ : R) • reverse b.val) * b.val) * ↑b⁻¹ := by rw [hd, one_mul]
      _ = _ := by rw [mul_assoc, Units.mul_inv, mul_one]
  have hScale (u : Rˣ) (x : CliffordAlgebra Q) :
      let c := Units.map (algebraMap R (CliffordAlgebra Q)).toMonoidHom u * b
      c.val * x * ↑c⁻¹ = b.val * x * ↑b⁻¹ := by
    dsimp only
    rw [unit_conjugate_mul]
    let v := Units.map (algebraMap R (CliffordAlgebra Q)).toMonoidHom u
    have hcomm := (Algebra.commute_algebraMap_left (u : R) (b.val * x * ↑b⁻¹)).eq
    change v.val * (b.val * x * ↑b⁻¹) = _ * v.val at hcomm
    rw [hcomm, mul_assoc, Units.mul_inv, mul_one]
  intro a
  constructor
  · rintro ⟨ha, _, hact⟩
    let c := b⁻¹ * a
    have hcEven : c.val ∈ evenOdd Q 0 := by
      have hi : (↑b⁻¹ : CliffordAlgebra Q) ∈ evenOdd Q 0 := by
        rw [hinv]
        exact (evenOdd Q 0).smul_mem _ ((reverse_mem_evenOdd_iff _).mpr he)
      change (↑b⁻¹ : CliffordAlgebra Q) * a.val ∈ _
      have hm : (↑b⁻¹ : CliffordAlgebra Q) * a.val ∈ evenOdd Q ((0 : ZMod 2) + 0) :=
        SetLike.mul_mem_graded hi ha.1
      simpa only [add_zero] using hm
    have hc (x : OddModule R n) : Commute c.val (ι Q (J x)) := by
      have hz : c.val * ι Q (J x) * ↑c⁻¹ = ι Q (J x) := by
        change (b⁻¹ * a).val * ι Q (J x) * ↑(b⁻¹ * a)⁻¹ = _
        rw [unit_conjugate_mul, hact, inv_inv]
        exact conjugation_swap b _ _ (hbOdd x)
      have hz' := congrArg (fun z : CliffordAlgebra Q => z * c.val) hz
      change c.val * ι Q (J x) = ι Q (J x) * c.val
      simpa only [mul_assoc, Units.inv_mul, mul_one] using hz'
    obtain ⟨v, hv⟩ := evenRestriction_scalar (n := n) h₂ c.val hcEven hc
    have hav : a.val = algebraMap R _ v * b.val := by
      have h := congrArg Units.val (mul_inv_cancel_left b a)
      change b.val * c.val = a.val at h
      exact h.symm.trans ((congrArg (fun z : CliffordAlgebra Q => b.val * z) hv).trans
        (Algebra.commutes v b.val).symm)
    have hvnorm : v ^ 2 * (s : R) = 1 := by
      apply scalar_injective Q (Pi.basisFun R (AmbientIndex n))
      rw [← scalar_mul_norm b.val v (s : R) hn', ← hav, ha.2.1, map_one]
    have hvprod : v * (v * (s : R)) = 1 := by simpa only [pow_two, mul_assoc] using hvnorm
    let u : Rˣ := ⟨v, v * (s : R), hvprod, by rw [mul_comm, hvprod]⟩
    have hu : a = Units.map (algebraMap R (CliffordAlgebra Q)).toMonoidHom u * b := Units.ext hav
    refine ⟨u, ⟨by rw [← hs]; exact hvnorm, hu⟩, fun w hw => ?_⟩
    apply Units.ext
    apply scalar_injective Q (Pi.basisFun R (AmbientIndex n))
    have h := mul_right_cancel (a := Units.map (algebraMap R (CliffordAlgebra Q)).toMonoidHom w)
      (hw.2.symm.trans hu)
    exact congrArg Units.val h
  · rintro ⟨u, ⟨hu, h⟩, _⟩
    subst a
    refine ⟨⟨?_, ?_, ?_, ?_⟩, (Algebra.commute_algebraMap_right _ _).mul_right hbcomm, ?_⟩
    · change algebraMap R _ (u : R) * b.val ∈ evenOdd Q 0
      rw [← Algebra.smul_def]
      exact (evenOdd Q 0).smul_mem _ he
    · change reverse (algebraMap R _ (u : R) * b.val) * (algebraMap R _ (u : R) * b.val) = 1
      rw [scalar_mul_norm b.val (u : R) (∏ i, (t i : R)) hn, hu, map_one]
    · rintro _ ⟨x, rfl⟩
      exact ⟨ambientScale n t x, ((hScale u (ι Q x)).trans (hb x)).symm⟩
    · let d := Units.map (algebraMap R (CliffordAlgebra Q)).toMonoidHom u * b
      rintro _ ⟨x, rfl⟩
      let y := (ambientScale n t).symm x
      have h := (hScale u (ι Q y)).trans (hb y)
      rw [show ambientScale n t y = x from LinearEquiv.apply_symm_apply _ _] at h
      exact ⟨y, (conjugation_swap d _ _ h).symm⟩
    · intro x
      exact (hScale u (ι Q (J x))).trans (hbOdd x)

theorem diagonalNormEquation : DiagonalNormEquation.{u} := by
  intro R _ n h₂ Q J r t
  obtain ⟨he, hn, _⟩ := diagonalLift_spec n t
  exact ⟨diagonalLift n t, he, hn, diagonalNormEquation_for_lift n h₂ t⟩

end DiagonalPreimage

section RestrictionSchemeComparison

open AlgebraicGeometry CategoryTheory Opposite SpinSpecification
open scoped CategoryTheory.MonObj TensorProduct
open private specPointsMulEquiv schemePoints_onSpec spinUnitPoints spinUnitPoints_represents
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinFunctor

variable (k : Type u) [Field k] (n : ℕ) (h₂ : (2 : k) = 0)

private abbrev ambientGroupScheme := SpinFunctor.spinScheme (ambientForm k n) (ambientBasis k n)
private abbrev ambientStabilizer := stabScheme (ambientForm k n) (ambientBasis k n) (markedVector k n)
private abbrev ambientStabilizerInclusion := stabInclusion (ambientForm k n) (ambientBasis k n) (markedVector k n)
private abbrev ambientPointValues := spinUnitPoints (ambientForm k n) (ambientBasis k n)
local instance : GrpObj (ambientStabilizerObject k n) := stabGroup (ambientForm k n) (ambientBasis k n) (markedVector k n)
local instance : GrpObj (markedObject k n) := markedGroup k n

private def stabilizerSchemePoints (S : CommAlgCat.{u} k) :
    SchemePoints (ambientStabilizer k n) S ≃* StabilizerPoints k n S :=
  let e := yonedaGrpObjIsoOfRepresentableBy (ambientStabilizerObject k n) _ (ambientStabilizerRepresentation k n)
  (specPointsMulEquiv S).symm.trans ((e.app (op (op S))).groupIsoToMulEquiv)

private theorem stabilizerSchemePoints_onSpec {S : CommAlgCat.{u} k} (p : op S ⟶ ambientStabilizerObject k n) :
    stabilizerSchemePoints k n S ((algSpec (CommRingCat.of k)).map p) = stabilizedPoints k n S p.unop.hom := by
  let e := specPointsMulEquiv (X := ambientStabilizerObject k n) S
  let f := (ambientStabilizerRepresentation k n).homEquiv (X := op S)
  exact congrArg f (e.symm_apply_apply p)

set_option maxRecDepth 1500 in
private theorem restrictionToMarked_points {S : CommAlgCat.{u} k} (p : SchemePoints (ambientStabilizer k n) S) :
    markedSchemePoints k n S (p ≫ (restrictionToMarked k n h₂).hom.hom) =
      restrictPoint k n h₂ S (stabilizerSchemePoints k n S p) := by
  let F := algSpec (CommRingCat.of k)
  obtain ⟨a, rfl⟩ := (specPointsMulEquiv (X := ambientStabilizerObject k n) S).surjective p
  let b := (restrictionAlg k n h₂).hom.hom
  have hc := congrArg (markedSchemePoints k n S) (F.map_comp a b)
  exact hc.symm.trans ((markedSchemePoints_onSpec k n (a ≫ b)).trans
    ((restrictionAlg_points k n h₂ a).trans ((stabMarkedNat_apply k n h₂ _).trans
      (congrArg (restrictPoint k n h₂ S) (stabilizerSchemePoints_onSpec k n a).symm))))

private theorem ambientPointValues_stabilizer {S : CommAlgCat.{u} k} (p : SchemePoints (ambientStabilizer k n) S) :
    ambientPointValues k n S (p ≫ (ambientStabilizerInclusion k n).hom.hom) =
      (stabilizerSchemePoints k n S p).val.val := by
  let F := algSpec (CommRingCat.of k)
  obtain ⟨a, rfl⟩ := (specPointsMulEquiv (X := ambientStabilizerObject k n) S).surjective p
  let b := (stabAlgebraInclusion (ambientForm k n) (ambientBasis k n) (markedVector k n)).hom.hom
  have hc := congrArg (ambientPointValues k n S) (F.map_comp a b)
  apply hc.symm.trans
  change (SpinFunctor.schemePoints (ambientForm k n) (ambientBasis k n) S (F.map (a ≫ b))).val = _
  exact (congrArg Subtype.val (schemePoints_onSpec _ _ _)).trans
    ((congrArg Subtype.val (stabAlgebraInclusion_points (ambientForm k n) (ambientBasis k n) (markedVector k n) a)).trans
      (congrArg (fun z : StabilizerPoints k n S => z.val.val) (stabilizerSchemePoints_onSpec k n a).symm))

private theorem restrictionToMarked_vectorAction {S : CommAlgCat.{u} k}
    (p : SchemePoints (ambientStabilizer k n) S) (x : S ⊗[k] OddModule k n) :
    let Q := ambientForm k n
    let J := inclusion k n
    let v := oddCoordinates k S n
    vectors Q S (J.toLinearMap.baseChange S
      (v.symm (oddMatrixAction (markedSchemePoints k n S (p ≫ (restrictionToMarked k n h₂).hom.hom)).val (v x)))) =
      conjugate Q S (ambientPointValues k n S (p ≫ (ambientStabilizerInclusion k n).hom.hom))
        (vectors Q S (J.toLinearMap.baseChange S x)) := by
  let q := oddForm k n
  let Q := ambientForm k n
  let J := inclusion k n
  let v := oddCoordinates k S n
  let j := oddCliffordMap k S n
  let e := MulEquiv.ofBijective (oddSpinToStabilizer (S := S) n h₂) (oddSpinToStabilizer_bijective n h₂)
  let a := e.symm (stabilizerSchemePoints k n S p)
  have hp : e a = stabilizerSchemePoints k n S p := e.apply_symm_apply _
  have hmarked : markedSchemePoints k n S (p ≫ (restrictionToMarked k n h₂).hom.hom) = markedAction n h₂ a :=
    restrictionToMarked_points k n h₂ p
  have hu : ambientPointValues k n S (p ≫ (ambientStabilizerInclusion k n).hom.hom) = Units.map j.toMonoidHom a.val :=
    (ambientPointValues_stabilizer k n p).trans
      (congrArg (fun z : StabilizerPoints k n S => z.val.val) hp.symm)
  have hV (x : S ⊗[k] OddModule k n) : j (vectors q S x) = vectors Q S (J.toLinearMap.baseChange S x) :=
    (tensorSpinComparison k n h₂ S).2.2.2.1 x
  dsimp only
  rw [hmarked, hu]
  have hmat : oddMatrixAction (markedAction n h₂ a).val = oddVectorAction n a := MulEquiv.apply_symm_apply _ _
  have hx : v.symm (oddMatrixAction (markedAction n h₂ a).val (v x)) =
      SpinFunctor.vectorAction q S (oddBasis k n) a x := by
    rw [hmat]
    change v.symm (v (SpinFunctor.vectorAction q S (oddBasis k n) a (v.symm (v x)))) = _
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  rw [hx, ← hV, ← hV]
  have h := congrArg j (SpinFunctor.vectorAction_characterization q S (oddBasis k n) a x)
  change _ = (Units.map j.toMonoidHom a.val).val * j (vectors q S x) *
    (↑(Units.map j.toMonoidHom a.val)⁻¹ : ScalarClifford Q S)
  rw [← map_inv]
  change _ = j a.val.val * j (vectors q S x) * j (↑a.val⁻¹)
  simpa only [conjugate, map_mul] using h

private theorem restrictionScalarKernel_points {S : CommAlgCat.{u} k} (p : SchemePoints (ambientStabilizer k n) S) :
    p ≫ (restrictionToMarked k n h₂).hom.hom = 1 ↔
      ∃! t : muTwoCoordinateRing k →ₐ[k] S,
        (ambientPointValues k n S (p ≫ (ambientStabilizerInclusion k n).hom.hom)).val =
          algebraMap S _ (t (AdjoinRoot.root (muTwoPolynomial k))) := by
  let a := stabilizerSchemePoints k n S p
  let e := SpinFunctor.muTwoPoints k S
  have hp : p ≫ (restrictionToMarked k n h₂).hom.hom = 1 ↔ restrictPoint k n h₂ S a = 1 := by
    rw [← (markedSchemePoints k n S).injective.eq_iff, map_one, restrictionToMarked_points]
  rw [hp, restrictPoint_eq_one]
  have ht (s : muTwoCoordinateRing k →ₐ[k] S) :
      (ambientPointValues k n S (p ≫ (ambientStabilizerInclusion k n).hom.hom)).val =
          algebraMap S _ (s (AdjoinRoot.root (muTwoPolynomial k))) ↔
        stabilizerScalar k n h₂ S (e s) = a := by
    rw [ambientPointValues_stabilizer]
    constructor
    · intro h
      apply Subtype.ext
      apply Subtype.ext
      apply Units.ext
      exact (stabilizerScalar_val k n h₂ (e s)).trans h.symm
    · intro h
      exact (congrArg (fun z : StabilizerPoints k n S => z.val.val.val) h).symm.trans
        (stabilizerScalar_val k n h₂ (e s))
  constructor
  · rintro ⟨t, ht₁, ht₂⟩
    refine ⟨e.symm t, (ht _).mpr ?_, fun z hz => e.injective ?_⟩
    · rwa [Equiv.apply_symm_apply]
    · rw [Equiv.apply_symm_apply]
      exact ht₂ _ ((ht z).mp hz)
  · rintro ⟨s, hs, hu⟩
    refine ⟨e s, (ht _).mp hs, fun z hz => ?_⟩
    have h := hu (e.symm z) ((ht _).mpr (by rw [Equiv.apply_symm_apply]; exact hz))
    exact (e.apply_symm_apply z).symm.trans (congrArg e h)

private theorem restrictionScalarKernel_central {S : CommAlgCat.{u} k}
    (p q : SchemePoints (ambientStabilizer k n) S) (hp : p ≫ (restrictionToMarked k n h₂).hom.hom = 1) :
    Commute p q := by
  let e := stabilizerSchemePoints k n S
  have h : restrictPoint k n h₂ S (e p) = 1 := by rw [← restrictionToMarked_points k n h₂ p, hp, map_one]
  obtain ⟨t, ht, _⟩ := (restrictPoint_eq_one k n h₂ _).mp h
  apply e.injective
  rw [map_mul, map_mul]
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  change (e p).val.val.val * (e q).val.val.val = (e q).val.val.val * (e p).val.val.val
  rw [← ht, stabilizerScalar_val]
  exact Algebra.commutes _ _


end RestrictionSchemeComparison

section DiagonalCocharacters

open LaurentPolynomial
open scoped LaurentPolynomial

private theorem corootSpan_evenSum (n : ℕ) (hn : 0 < n) (v : Fin n → ℤ) :
    v ∈ Submodule.span ℤ (typeBCoroots n) ↔ Even (∑ i, v i) := by
  classical
  let L := Submodule.span ℤ (typeBCoroots n)
  let e (i : Fin n) : Fin n → ℤ := Pi.single i 1
  let E : Submodule ℤ (Fin n → ℤ) := {
    carrier := {x | Even (∑ i, x i)}
    zero_mem' := by simp
    add_mem' := by
      intro x y hx hy
      change Even (∑ i, x i) at hx
      change Even (∑ i, y i) at hy
      change Even (∑ i, (x i + y i))
      rw [Finset.sum_add_distrib]
      exact hx.add hy
    smul_mem' := by
      intro r x hx
      change Even (∑ i, x i) at hx
      change Even (∑ i, r * x i)
      rw [← Finset.mul_sum]
      exact hx.mul_left r }
  have hLE : L ≤ E := by
    apply Submodule.span_le.mpr
    rintro _ (⟨i, rfl | rfl⟩ | ⟨i, j, _, rfl | rfl | rfl⟩)
    all_goals
      change Even (∑ i, _)
      simp [Pi.smul_apply, Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Finset.sum_neg_distrib,
        Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  refine ⟨fun h => hLE h, ?_⟩
  intro hv
  let j : Fin n := ⟨0, hn⟩
  have hd (i : Fin n) : e i - e j ∈ L := by
    by_cases hij : i = j
    · simp [hij]
    · exact Submodule.subset_span (Or.inr ⟨i, j, hij, Or.inl rfl⟩)
  have he : (2 : ℤ) • e j ∈ L := Submodule.subset_span (Or.inl ⟨j, Or.inl rfl⟩)
  obtain ⟨a, ha⟩ := hv
  have hv₀ : ∑ i, v i • e i = v := by
    funext i
    simp [e, Finset.sum_apply, Pi.single_apply, mul_ite]
  have hv₁ : (∑ i, v i • (e i - e j)) + a • ((2 : ℤ) • e j) = v := by
    have hc : a • ((2 : ℤ) • e j) = (a + a) • e j := by rw [two_smul, smul_add, add_smul]
    simp_rw [smul_sub]
    rw [Finset.sum_sub_distrib, hv₀, ← Finset.sum_smul, ha, hc, sub_add_cancel]
  rw [← hv₁]
  exact L.add_mem (L.sum_mem fun i _ => L.smul_mem (v i) (hd i)) (L.smul_mem a he)

private theorem laurent_square_coeff_odd {k : Type u} [Field k] (h₂ : (2 : k) = 0)
    (f : LaurentPolynomial k) (a : ℤ) (ha : ¬ Even a) : (f ^ 2).coeff a = 0 := by
  have h₂' : (2 : LaurentPolynomial k) = 0 := by
    simpa only [map_ofNat, map_zero] using congrArg (LaurentPolynomial.C (R := k)) h₂
  induction f using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    rw [add_sq, h₂', zero_mul, zero_mul, add_zero]
    change ( (p ^ 2).coeff + (q ^ 2).coeff) a = 0
    rw [Finsupp.add_apply, hp, hq, add_zero]
  | C_mul_T d r =>
    rw [mul_pow, ← map_pow, T_pow]
    apply Finsupp.notMem_support_iff.mp
    intro h
    have hd := LaurentPolynomial.support_C_mul_T (r ^ 2) ((2 : ℤ) * d) h
    exact ha ⟨d, by have ha' := Finset.mem_singleton.mp hd; omega⟩

private theorem product_laurent_monomials {k : Type u} [Field k] {n : ℕ} (m : Fin n → ℤ)
    (s : Finset (Fin n)) : (∏ i ∈ s, LaurentPolynomial.T (R := k) (m i)) =
    LaurentPolynomial.T (∑ i ∈ s, m i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, ih, Finset.sum_insert hi, LaurentPolynomial.T_add]

private theorem laurent_norm_even {k : Type u} [Field k] (h₂ : (2 : k) = 0) (m : ℤ) :
    (∃ u : (LaurentPolynomial k)ˣ, (u : LaurentPolynomial k)^2 * LaurentPolynomial.T m = 1) ↔ Even m := by
  constructor
  · rintro ⟨u, hu⟩
    by_contra hm
    have hf := congrArg (fun z : LaurentPolynomial k => z * LaurentPolynomial.T (-m)) hu
    rw [mul_assoc, ← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero, mul_one, one_mul] at hf
    have hz := laurent_square_coeff_odd h₂ (u : LaurentPolynomial k) (-m) (by simpa using hm)
    rw [hf] at hz
    change (Finsupp.single (-m) (1 : k)) (-m) = 0 at hz
    rw [Finsupp.single_eq_same] at hz
    exact one_ne_zero hz
  · rintro ⟨d, hd⟩
    let u := (LaurentPolynomial.isUnit_T (R := k) (-d)).unit
    refine ⟨u, ?_⟩
    rw [(LaurentPolynomial.isUnit_T (R := k) (-d)).unit_spec, LaurentPolynomial.T_pow,
      ← LaurentPolynomial.T_add, ← LaurentPolynomial.T_zero (R := k)]
    congr 1
    norm_num
    omega

theorem laurentDiagonalLifting : LaurentDiagonalLifting.{u} := by
  intro k _ n h₂ hn m t ht R Q J r
  have h₂R : (2 : R) = 0 := by
    simpa only [map_ofNat, map_zero] using congrArg (LaurentPolynomial.C (R := k)) h₂
  obtain ⟨b, _, _, hb⟩ := diagonalNormEquation R n h₂R t
  have hprod : (∏ i, (t i : R)) = LaurentPolynomial.T (∑ i, m i) := by
    simp only [ht]
    exact product_laurent_monomials m Finset.univ
  rw [corootSpan_evenSum n hn, ← laurent_norm_even h₂]
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨u, hu, _⟩ := (hb a).mp ha
    exact ⟨u, hprod ▸ hu.1⟩
  · rintro ⟨u, hu⟩
    let a := Units.map (algebraMap R (CliffordAlgebra Q)).toMonoidHom u * b
    refine ⟨a, (hb a).mpr ⟨u, ⟨hprod.symm ▸ hu, rfl⟩, fun u' hu' => ?_⟩⟩
    apply Units.ext
    apply scalar_injective Q (Pi.basisFun R (AmbientIndex n))
    have h := mul_right_cancel hu'.2.symm
    exact congrArg Units.val h

end DiagonalCocharacters

section ReductiveTransfer

open Topology TopologicalSpace
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open Specs (subgroupConjugation)
open Specs.GeometricRadicals (GeometricGroup IsReductive geometricUnipotentRadical)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open private isReduced_of_smooth_over_field from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SmoothnessCriteria
open private baseChangeMapPullback from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Components
open private exists_section_lift sectionOfClosedPoint sectionOfClosedPoint_apply
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.WordDomainGeometry
open private rationalSections trivial_of_subsingleton_sections from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricRadicals

variable {K : Type u} [Field K] [IsAlgClosed K]

private theorem factors_through_closed_of_sections {X Y Z : SchemeOver K} (f : X ⟶ Y) (j : Z ⟶ Y)
    [LocallyOfFiniteType X.hom] [IsReduced X.left] [IsClosedImmersion j.left]
    (h : ∀ p : 𝟙_ (SchemeOver K) ⟶ X, ∃ z : 𝟙_ (SchemeOver K) ⟶ Z, z ≫ j = p ≫ f) :
    ∃ c : X ⟶ Z, c ≫ j = f := by
  let P := pullback f j
  let q : P ⟶ X := pullback.fst f j
  let t : P ⟶ Z := pullback.snd f j
  haveI : IsClosedImmersion q.left :=
    MorphismProperty.of_isPullback ((IsPullback.of_hasPullback f j).map (Over.forget _)).flip
      (show IsClosedImmersion j.left from inferInstance)
  haveI : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  have hc : closedPoints X.left ⊆ Set.range q.left := by
    intro x hx
    let p := sectionOfClosedPoint X x hx
    obtain ⟨z, hz⟩ := h p
    let a : 𝟙_ (SchemeOver K) ⟶ P := pullback.lift p z hz.symm
    have ha : a ≫ q = p := pullback.lift_fst _ _ _
    refine ⟨a.left (IsLocalRing.closedPoint K), ?_⟩
    exact (congrArg (fun g : 𝟙_ (SchemeOver K) ⟶ X => g.left (IsLocalRing.closedPoint K)) ha).trans
      (sectionOfClosedPoint_apply X x hx)
  have hs : Surjective q.left := by
    constructor
    have hc' := q.left.isClosedEmbedding.isClosed_range.closure_subset_iff.mpr hc
    rw [closure_closedPoints] at hc'
    exact Set.range_eq_univ.mp (Set.Subset.antisymm (Set.subset_univ _) hc')
  haveI : IsIso q.left := isIso_of_isClosedImmersion_of_surjective _
  haveI : IsIso ((Over.forget (Spec (CommRingCat.of K))).map q) := inferInstanceAs (IsIso q.left)
  haveI : IsIso q := isIso_of_reflects_iso _ (Over.forget _)
  refine ⟨inv q ≫ t, ?_⟩
  rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]

private theorem normal_scheme_image {G Q N I : AffineAlgebraicGroup K}
    (g : G.val ⟶ Q.val) (n : N.val ⟶ G.val) (p : N.val ⟶ I.val) (j : I.val ⟶ Q.val)
    (hgp : p ≫ j = n ≫ g) (hn : IsNormalSubgroup n)
    (hg : Surjective g.hom.hom.left) (hp : Surjective p.hom.hom.left)
    (hQ : Smooth Q.val.X.hom) (hI : Smooth I.val.X.hom) (hj : IsClosedImmersion j.hom.hom.left) :
    IsNormalSubgroup j := by
  haveI := G.property.2.1
  haveI := Q.property.2.1
  haveI := N.property.2.1
  haveI := I.property.2.1
  haveI := hQ
  haveI := hI
  haveI := hj
  let X := Q.val.X ⊗ I.val.X
  have hX : Smooth X.hom := by
    have hh : (fst Q.val.X I.val.X).left ≫ Q.val.X.hom = X.hom := (fst Q.val.X I.val.X).w
    rw [← hh]
    change Smooth (pullback.fst Q.val.X.hom I.val.X.hom ≫ Q.val.X.hom)
    infer_instance
  haveI : LocallyOfFiniteType X.hom := by letI := hX; infer_instance
  haveI := hX
  haveI : IsReduced X.left := isReduced_of_smooth_over_field X.hom
  apply factors_through_closed_of_sections
  intro v
  obtain ⟨uQ, hQv⟩ := exists_section_lift g.hom.hom (v ≫ fst Q.val.X I.val.X) (hg.1 _)
  obtain ⟨uI, hIv⟩ := exists_section_lift p.hom.hom (v ≫ snd Q.val.X I.val.X) (hp.1 _)
  obtain ⟨c, hc⟩ := hn
  let u := lift uQ uI
  have h1 : u ≫ fst G.val.X N.val.X = uQ := lift_fst _ _
  have h2 : u ≫ snd G.val.X N.val.X = uI := lift_snd _ _
  have he := congrArg (fun a : N.val ⟶ Q.val => a.hom.hom) hgp
  change p.hom.hom ≫ j.hom.hom = n.hom.hom ≫ g.hom.hom at he
  refine ⟨u ≫ c ≫ p.hom.hom, ?_⟩
  calc
    (u ≫ c ≫ p.hom.hom) ≫ j.hom.hom = (u ≫ subgroupConjugation n) ≫ g.hom.hom := by
      rw [Category.assoc, Category.assoc, he, ← Category.assoc c, hc, Category.assoc]
    _ = v ≫ subgroupConjugation j := by
      simp only [subgroupConjugation, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, h1, h2,
        MonObj.mul_comp, GrpObj.inv_comp]
      rw [hQv, Category.assoc uI n.hom.hom, ← he, ← Category.assoc uI, hIv]

set_option maxHeartbeats 850000 in
set_option maxRecDepth 1400 in
/-- The smooth geometric unipotent radical has a smooth normal unipotent
image. If that image is trivial, radiciality makes the radical itself
trivial, since it is reduced. -/
private theorem smooth_source_reductive {k : Type u} [Field k] (G Q : AffineAlgebraicGroup k)
    (f : G.val ⟶ Q.val) (hs : Surjective f.hom.hom.left)
    (hi : UniversallyInjective f.hom.hom.left) (hsm : Smooth G.val.X.hom)
    (hc : GeometricallyConnected G.val.X.hom) (hQ : IsReductive Q) : IsReductive G := by
  refine ⟨hsm, hc, ?_⟩
  let K := AlgebraicClosure k
  let Q' := GeometricGroup Q
  let f' : (GeometricGroup G).val ⟶ Q'.val := (groupBaseChange k K).map f
  let R := geometricUnipotentRadical G
  let U := geometricUnipotentRadical Q
  let N := closedSubgroupAlgebraicGroup R
  have hR := LinearAlgebraicGroups.GeometricRadicals.geometricUnipotentRadicalLargest G
  have hU := LinearAlgebraicGroups.GeometricRadicals.geometricUnipotentRadicalLargest Q
  have hbc := (baseChangeMapPullback (K := K) f.hom.hom).flip
  have hfs : Surjective f'.hom.hom.left := MorphismProperty.of_isPullback hbc hs
  have hfi : UniversallyInjective f'.hom.hom.left := MorphismProperty.of_isPullback hbc hi
  have hQ' : Smooth Q'.val.X.hom := by
    haveI := hQ.1
    change Smooth (pullback.snd Q.val.X.hom (fieldSpecMap k K))
    infer_instance
  obtain ⟨I, p, j, ⟨hcomp, hflat, hsurj, _, _, hclosed⟩, _, _⟩ :=
    LinearAlgebraicGroups.schemeImageFactorization N Q' (R.inclusion ≫ f')
  have hIa := I.property.1
  have hNa := N.property.1
  have : Smooth N.val.X.hom := hR.1.1
  have : IsReduced N.val.X.left := isReduced_of_smooth_over_field N.val.X.hom
  have hInj := ((Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine p.hom.hom.left).mp
    ⟨hflat, hsurj⟩).injective
  haveI : _root_.IsReduced Γ(I.val.X.left, ⊤) := isReduced_of_injective _ hInj
  have hrI : IsReduced I.val.X.left := isReduced_of_isAffine_isReduced _
  have hI' : Smooth I.val.X.hom := by
    haveI := I.property.2.1
    exact LinearAlgebraicGroups.smoothOfReducedOverPerfectField K I.val hrI
  have hIc : ConnectedSpace I.val.X.left := by
    haveI : ConnectedSpace N.val.X.left := hR.1.2.1
    exact hsurj.1.connectedSpace p.hom.hom.left.continuous
  have hIn : IsNormalSubgroup j :=
    normal_scheme_image (G := GeometricGroup G) (Q := Q') (N := N) (I := I)
      f' R.inclusion p j hcomp hR.1.2.2 hfs hsurj hQ' hI' hclosed
  let D : ClosedSubgroup Q'.val := ⟨I.val, j, hclosed⟩
  have hIu : Specs.Unipotent.IsUnipotent I := LinearAlgebraicGroups.Unipotent.faithfullyFlatQuotientsUnipotent N I p hflat hsurj hR.2.1
  obtain ⟨i, hi'⟩ := hU.2.2 D ⟨hI', hIc, hIn⟩ hIu
  obtain ⟨e⟩ := hQ.2.2
  have hUsub : Subsingleton ((𝟙_ (SchemeOver (AlgebraicClosure k))) ⟶ U.group.X) := by
    let d := (Grp.forget (SchemeOver (AlgebraicClosure k))).mapIso e
    constructor
    intro x y
    exact (cancel_mono d.hom).mp ((isTerminalTensorUnit (C := SchemeOver (AlgebraicClosure k))).hom_ext _ _)
  letI : Subsingleton (rationalSections N.val) := by
    change Subsingleton ((𝟙_ (SchemeOver (AlgebraicClosure k))) ⟶ R.group.X)
    constructor
    intro x y
    have h : p.hom.hom ≫ j.hom.hom = R.inclusion.hom.hom ≫ f'.hom.hom :=
      congrArg (fun z : N.val ⟶ Q'.val => z.hom.hom) hcomp
    have h' : i.hom.hom ≫ U.inclusion.hom.hom = j.hom.hom :=
      congrArg (fun z : D.group ⟶ Q'.val => z.hom.hom) hi'
    have hz := hUsub.elim ((x ≫ p.hom.hom) ≫ i.hom.hom) ((y ≫ p.hom.hom) ≫ i.hom.hom)
    have hxy : x ≫ R.inclusion.hom.hom ≫ f'.hom.hom = y ≫ R.inclusion.hom.hom ≫ f'.hom.hom := calc
      _ = ((x ≫ p.hom.hom) ≫ i.hom.hom) ≫ U.inclusion.hom.hom := by
        calc
          _ = x ≫ p.hom.hom ≫ j.hom.hom := congrArg (fun z => x ≫ z) h.symm
          _ = ((x ≫ p.hom.hom) ≫ i.hom.hom) ≫ U.inclusion.hom.hom := by
            simp only [Category.assoc]; exact congrArg (fun z => x ≫ p.hom.hom ≫ z) h'.symm
      _ = ((y ≫ p.hom.hom) ≫ i.hom.hom) ≫ U.inclusion.hom.hom :=
        congrArg (fun z => z ≫ U.inclusion.hom.hom) hz
      _ = _ := calc
        _ = y ≫ p.hom.hom ≫ j.hom.hom := by
          simp only [Category.assoc]; exact congrArg (fun z => y ≫ p.hom.hom ≫ z) h'
        _ = _ := congrArg (fun z => y ≫ z) h
    have hfK : ∀ (L : Type u) [Field L],
        Function.Injective (fun a : Spec (.of L) ⟶ (GeometricGroup G).val.X.left =>
          a ≫ f'.hom.hom.left) :=
      ((tfae_universallyInjective f'.hom.hom.left).out 1 2).mp hfi
    have hz' : x.left ≫ R.inclusion.hom.hom.left = y.left ≫ R.inclusion.hom.hom.left :=
      hfK (AlgebraicClosure k) (by
        have hxy' : x.left ≫ R.inclusion.hom.hom.left ≫ f'.hom.hom.left =
            y.left ≫ R.inclusion.hom.hom.left ≫ f'.hom.hom.left :=
          congrArg Over.Hom.left hxy
        exact (Category.assoc _ _ _).trans (hxy'.trans (Category.assoc _ _ _).symm))
    haveI : IsClosedImmersion R.inclusion.hom.hom.left := R.isClosedImmersion
    exact Over.OverMorphism.ext ((cancel_mono _).mp hz')
  exact trivial_of_subsingleton_sections N hR.1.1

end ReductiveTransfer

section CocharactersOfRestriction

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite SpinSpecification
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct
open private isReduced_of_smooth_over_field from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SmoothnessCriteria

private theorem equal_of_radicial_composites {X H O : Scheme.{u}} (f : H ⟶ O)
    [UniversallyInjective f] [IsSeparated f] [IsReduced X] (p q : X ⟶ H) (h : p ≫ f = q ≫ f) : p = q := by
  let s := pullback.lift p q h
  let d := pullback.diagonal f
  let P := pullback s d
  let a : P ⟶ X := pullback.fst s d
  let b : P ⟶ H := pullback.snd s d
  haveI : Surjective d := (UniversallyInjective.iff_diagonal f).mp inferInstance
  haveI : IsClosedImmersion a := inferInstanceAs (IsClosedImmersion (pullback.fst s d))
  haveI : Surjective a := inferInstanceAs (Surjective (pullback.fst s d))
  haveI : IsIso a := isIso_of_isClosedImmersion_of_surjective _
  apply (cancel_epi a).mp
  have ha : a ≫ s = b ≫ d := pullback.condition
  calc
    a ≫ p = (a ≫ s) ≫ pullback.fst f f := by rw [Category.assoc, pullback.lift_fst]
    _ = b := by rw [ha, Category.assoc, pullback.diagonal_fst, Category.comp_id]
    _ = (a ≫ s) ≫ pullback.snd f f := by rw [ha, Category.assoc, pullback.diagonal_snd, Category.comp_id]
    _ = a ≫ q := by rw [Category.assoc, pullback.lift_snd]

private theorem cocharacter_of_underlying_lift {k : Type u} [Field k]
    {M H O : GroupScheme k} (f : H ⟶ O) [UniversallyInjective f.hom.hom.left]
    [IsSeparated f.hom.hom.left] [IsReduced (M.X ⊗ M.X).left]
    (χ : M ⟶ O) (p : M.X ⟶ H.X) (hp : p ≫ f.hom.hom = χ.hom.hom) :
    ∃ c : M ⟶ H, c ≫ f = χ := by
  have h₁ : η[M.X] ≫ p = η[H.X] := by
    haveI : IsReduced (𝟙_ (SchemeOver k)).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of k)))
    apply Over.OverMorphism.ext
    apply equal_of_radicial_composites f.hom.hom.left
    have h : (η[M.X] ≫ p) ≫ f.hom.hom = η[H.X] ≫ f.hom.hom := by
      rw [Category.assoc, hp, IsMonHom.one_hom, IsMonHom.one_hom]
    exact congrArg Over.Hom.left h
  have h₂ : μ[M.X] ≫ p = (p ⊗ₘ p) ≫ μ[H.X] := by
    apply Over.OverMorphism.ext
    apply equal_of_radicial_composites f.hom.hom.left
    have h : (μ[M.X] ≫ p) ≫ f.hom.hom = ((p ⊗ₘ p) ≫ μ[H.X]) ≫ f.hom.hom := by
      rw [Category.assoc, hp, Category.assoc, IsMonHom.mul_hom f.hom.hom,
        tensorHom_comp_tensorHom_assoc, hp, ← IsMonHom.mul_hom χ.hom.hom]
    exact congrArg Over.Hom.left h
  exact ⟨Grp.homMk'' p h₁ h₂, Grp.hom_ext _ _ hp⟩

private theorem laurentMultiplicativeGroup_smooth (k : Type u) [Field k] : Smooth (laurentMultiplicativeGroup k).X.hom := by
  let R := LaurentPolynomial k
  change Smooth (Spec.map (CommRingCat.ofHom (algebraMap k R)))
  apply (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
  apply RingHom.smooth_algebraMap.mpr
  haveI : Algebra.Smooth (Polynomial k) R := Algebra.Smooth.of_isLocalization_Away Polynomial.X
  letI : IsScalarTower k (Polynomial k) R := IsScalarTower.of_algebraMap_eq fun x => by
    change LaurentPolynomial.C x = Polynomial.toLaurent (Polynomial.C x)
    exact (Polynomial.toLaurent_C x).symm
  haveI : Algebra.Smooth k (Polynomial k) := Algebra.Smooth.of_equiv (MvPolynomial.uniqueAlgEquiv k Unit)
  exact Algebra.Smooth.comp k (Polynomial k) R

private theorem laurentMultiplicativeGroup_square_reduced (k : Type u) [Field k] :
    IsReduced ((laurentMultiplicativeGroup k).X ⊗ (laurentMultiplicativeGroup k).X).left := by
  letI := laurentMultiplicativeGroup_smooth k
  let S := (laurentMultiplicativeGroup k).X
  haveI : Smooth (S ⊗ S).hom := by
    rw [← (fst S S).w]
    change Smooth (pullback.fst S.hom S.hom ≫ S.hom)
    infer_instance
  exact isReduced_of_smooth_over_field ((S ⊗ S).hom)


variable {k : Type u} [Field k] (n : ℕ) {S : CommAlgCat.{u} k}

private def nativeStabilizerValue (p : SchemePoints (ambientStabilizer k n) S) :
    (CliffordAlgebra (ambientForm S n))ˣ :=
  Units.map (ambientCliffordEquiv k S n).toMonoidHom
    (ambientPointValues k n S (p ≫ (ambientStabilizerInclusion k n).hom.hom))

private theorem nativeStabilizerValue_spec (p : SchemePoints (ambientStabilizer k n) S) :
    IsIntrinsicSpin (ambientForm S n) (nativeStabilizerValue n p) ∧
      Commute (CliffordAlgebra.ι (ambientForm S n) (inclusion S n (radicalVector S n)))
        (nativeStabilizerValue n p).val := by
  let q := ambientForm k n
  let Q := ambientForm S n
  let r := inclusion k n (radicalVector k n)
  let e := ambientCliffordEquiv k S n
  let a := stabilizerSchemePoints k n S p
  change IsIntrinsicSpin Q (Units.map e.toMonoidHom
    (ambientPointValues k n S (p ≫ (ambientStabilizerInclusion k n).hom.hom))) ∧ _
  unfold nativeStabilizerValue
  rw [ambientPointValues_stabilizer]
  refine ⟨(nativeClifford_spin q Q _ a.val.val).mp a.val.property, ?_⟩
  have h : Commute (markedClifford q r S) a.val.val.val := a.property
  have h' := h.map e
  rwa [ambientCliffordEquiv_marked] at h'

private theorem nativeStabilizerValue_surj (a : (CliffordAlgebra (ambientForm S n))ˣ)
    (ha : IsIntrinsicSpin (ambientForm S n) a)
    (hr : Commute (CliffordAlgebra.ι (ambientForm S n) (inclusion S n (radicalVector S n))) a.val) :
    ∃ p : SchemePoints (ambientStabilizer k n) S, nativeStabilizerValue n p = a := by
  let q := ambientForm k n
  let Q := ambientForm S n
  let r := inclusion k n (radicalVector k n)
  let e := ambientCliffordEquiv k S n
  obtain ⟨b, hb⟩ := (Units.mapEquiv e.toMulEquiv).surjective a
  have hbspin : b ∈ spinUnits q S := (nativeClifford_spin q Q _ b).mpr (hb.symm ▸ ha)
  have hbr : Commute (markedClifford q r S) b.val := by
    apply e.injective
    rw [map_mul, map_mul, ambientCliffordEquiv_marked,
      show e b.val = a.val from congrArg Units.val hb]
    exact hr.eq
  let z := (stabilizerSchemePoints k n S).symm ⟨⟨b, hbspin⟩, hbr⟩
  refine ⟨z, ?_⟩
  unfold nativeStabilizerValue
  rw [ambientPointValues_stabilizer, MulEquiv.apply_symm_apply]
  exact hb

private theorem nativeIncl_vector (h₂ : (2 : k) = 0) (x : S ⊗[k] OddModule k n) :
    ambientCliffordEquiv k S n (vectors (ambientForm k n) S ((inclusion k n).toLinearMap.baseChange S x)) =
      CliffordAlgebra.ι (ambientForm S n) (inclusion S n (oddCoordinates k S n x)) := by
  let j := oddCliffordMap k S n
  let e := nativeClifford (oddForm k n) (oddForm S n) (odd_map n)
  have h₁ : j (vectors (oddForm k n) S x) =
      vectors (ambientForm k n) S ((inclusion k n).toLinearMap.baseChange S x) :=
    (tensorSpinComparison k n h₂ S).2.2.2.1 x
  rw [← h₁, nativeClifford_inclusion, nativeClifford_vector, map_apply_ι]

private theorem restriction_nativeAction (h₂ : (2 : k) = 0)
    (p : SchemePoints (ambientStabilizer k n) S) (x : OddModule S n) :
    let a := nativeStabilizerValue n p
    a.val * CliffordAlgebra.ι (ambientForm S n) (inclusion S n x) * ↑a⁻¹ =
      CliffordAlgebra.ι (ambientForm S n) (inclusion S n
        (oddMatrixAction (markedSchemePoints k n S (p ≫ (restrictionToMarked k n h₂).hom.hom)).val x)) := by
  let v := oddCoordinates k S n
  let y := v.symm x
  let e := ambientCliffordEquiv k S n
  let Q := ambientForm k n
  let J := (inclusion k n).toLinearMap.baseChange S
  let a := ambientPointValues k n S (p ≫ (ambientStabilizerInclusion k n).hom.hom)
  let g := oddMatrixAction (markedSchemePoints k n S (p ≫ (restrictionToMarked k n h₂).hom.hom)).val
  have h := congrArg e (restrictionToMarked_vectorAction k n h₂ p y)
  change e (vectors Q S (J (v.symm (g (v y))))) = e (a.val * vectors Q S (J y) * ↑a⁻¹) at h
  rw [map_mul, map_mul, nativeIncl_vector n h₂, nativeIncl_vector n h₂,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h
  exact h.symm

set_option maxRecDepth 1200 in
set_option maxHeartbeats 1000000 in
private theorem actualDiagonalCocharacters (h₂ : (2 : k) = 0) (hn : 0 < n)
    (χ : laurentMultiplicativeGroup k ⟶ markedScheme k n) (m : Fin n → ℤ) (t : Fin n → (LaurentPolynomial k)ˣ)
    (ht : ∀ i, (t i : LaurentPolynomial k) = LaurentPolynomial.T (m i))
    (hχ : ∀ x : OddModule (LaurentPolynomial k) n,
      oddMatrixAction (markedSchemePoints k n (CommAlgCat.of k (LaurentPolynomial k)) χ.hom.hom).val x =
        diagonalOddVector t x) :
    (∃ c : laurentMultiplicativeGroup k ⟶ ambientStabilizer k n, c ≫ restrictionToMarked k n h₂ = χ) ↔
      m ∈ Submodule.span ℤ (typeBCoroots n) := by
  let R := LaurentPolynomial k
  let S := CommAlgCat.of k R
  let f := restrictionToMarked k n h₂
  have hL := laurentDiagonalLifting k n h₂ hn m t ht
  dsimp only at hL
  rw [← hL]
  constructor
  · rintro ⟨c, hc⟩
    let p : SchemePoints (ambientStabilizer k n) S := c.hom.hom
    refine ⟨nativeStabilizerValue n p, (nativeStabilizerValue_spec n p).1,
      (nativeStabilizerValue_spec n p).2, fun x => ?_⟩
    have hp : p ≫ f.hom.hom = χ.hom.hom := congrArg (fun j : laurentMultiplicativeGroup k ⟶ markedScheme k n => j.hom.hom) hc
    have h := restriction_nativeAction n h₂ p x
    rw [hp, hχ] at h
    exact h
  · rintro ⟨a, ha, hfix, hact⟩
    obtain ⟨p, hp⟩ := nativeStabilizerValue_surj (S := S) n a ha hfix
    have hc : p ≫ f.hom.hom = χ.hom.hom := by
      apply (markedSchemePoints k n S).injective
      apply Subtype.ext
      apply oddMatrixAction.injective
      apply LinearEquiv.ext
      intro x
      rw [hχ]
      have hh := restriction_nativeAction n h₂ p x
      rw [hp] at hh
      dsimp only at hh
      have h := intrinsic_vector_injective n (ambientForm R n) (hh.symm.trans (hact x))
      exact congrArg (fun y : AmbientModule R n => fun j : OddIndex n => y j) h
    haveI : IsFinite f.hom.hom.left := restriction_finite k n h₂
    haveI : UniversallyInjective f.hom.hom.left := restriction_radicial k n h₂
    haveI : IsReduced ((laurentMultiplicativeGroup k).X ⊗ (laurentMultiplicativeGroup k).X).left := laurentMultiplicativeGroup_square_reduced k
    exact cocharacter_of_underlying_lift f χ p hc


end CocharactersOfRestriction


section AffinePointMorphisms

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite SpinSpecification
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open private schemeKernel_exists schemeKernel_sections isMonHom_of_comp_closed
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private spinUnitPoints_represents muTwoSchemePoints_onSpec scalar_tensor_injective
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinFunctor

variable {k : Type u} [Field k]

private def affineTestIso (X : SchemeOver k) [IsAffine X.left] :
    (algSpec (CommRingCat.of k)).obj (op (Specs.coordinates X)) ≅ X := by
  let R := CommRingCat.of k
  let B := Specs.coordinates X
  have h : X.left.toSpecΓ ≫ ((algSpec R).obj (op B)).hom = X.hom := by
    change X.left.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso R).inv ≫ X.hom.appTop) = X.hom
    rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc]
    change X.hom ≫ (Spec R).isoSpec.hom ≫ _ = _
    rw [Scheme.isoSpec_Spec_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]
  let a : X ⟶ (algSpec R).obj (op B) := Over.homMk X.left.toSpecΓ h
  have ha : IsIso a.left := inferInstanceAs (IsIso X.left.toSpecΓ)
  haveI : IsIso ((Over.forget (Spec (CommRingCat.of k))).map a) := ha
  haveI : IsIso a := isIso_of_reflects_iso _ (Over.forget _)
  exact (asIso a).symm

private theorem tensor_affine {X Y : SchemeOver k} [IsAffine X.left] [IsAffine Y.left] :
    IsAffine (X ⊗ Y).left := by
  change IsAffine (pullback X.hom Y.hom)
  infer_instance

private theorem groupHom_of_affine_point_law {D G : GroupScheme k} [IsAffine D.X.left]
    (p : D.X ⟶ G.X) (F : ∀ S : CommAlgCat k, SchemePoints D S →* SchemePoints G S)
    (h : ∀ S x, x ≫ p = F S x) : ∃ j : D ⟶ G, j.hom.hom = p := by
  refine ⟨Grp.homMk'' p ?_ ?_, rfl⟩
  · let U := 𝟙_ (SchemeOver k)
    haveI : IsAffine U.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of k)))
    let e := affineTestIso U
    apply (cancel_epi e.hom).mp
    have he : toUnit ((algSpec (CommRingCat.of k)).obj (op (Specs.coordinates U))) = e.hom :=
      (isTerminalTensorUnit (C := SchemeOver k)).hom_ext _ _
    have h₁ := h (Specs.coordinates U) (1 : SchemePoints D (Specs.coordinates U))
    rw [map_one] at h₁
    change (toUnit _ ≫ η[D.X]) ≫ p = toUnit _ ≫ η[G.X] at h₁
    rw [he, Category.assoc] at h₁
    exact h₁
  · let P := D.X ⊗ D.X
    haveI : IsAffine P.left := tensor_affine
    let e := affineTestIso P
    let x : SchemePoints D (Specs.coordinates P) := e.hom ≫ fst D.X D.X
    let y : SchemePoints D (Specs.coordinates P) := e.hom ≫ snd D.X D.X
    have hxy : x * y = e.hom ≫ μ[D.X] := by
      change lift (e.hom ≫ fst _ _) (e.hom ≫ snd _ _) ≫ μ[D.X] = _
      rw [← comp_lift, lift_fst_snd, Category.comp_id]
    have hxy' :
        (x ≫ p) * (y ≫ p) = e.hom ≫ (p ⊗ₘ p) ≫ μ[G.X] := by
      change lift ((e.hom ≫ fst _ _) ≫ p) ((e.hom ≫ snd _ _) ≫ p) ≫ μ[G.X] = _
      have he : lift ((e.hom ≫ fst D.X D.X) ≫ p) ((e.hom ≫ snd D.X D.X) ≫ p) =
          e.hom ≫ (p ⊗ₘ p) := by
        apply CartesianMonoidalCategory.hom_ext <;> simp only [Category.assoc, lift_fst, lift_snd, tensorHom_fst, tensorHom_snd]
      rw [he, Category.assoc]
    apply (cancel_epi e.hom).mp
    calc
      e.hom ≫ μ[D.X] ≫ p = (x * y) ≫ p := by rw [hxy, Category.assoc]
      _ = (x ≫ p) * (y ≫ p) := by rw [h, map_mul, ← h, ← h]
      _ = e.hom ≫ (p ⊗ₘ p) ≫ μ[G.X] := hxy'

set_option maxHeartbeats 700000 in
private theorem groupHom_of_natural_points {D G : GroupScheme k} [IsAffine D.X.left]
    (A : CommAlgCat.{u} k) (e : (algSpec (CommRingCat.of k)).obj (op A) ≅ D.X)
    (F : ∀ S : CommAlgCat k, SchemePoints D S →* SchemePoints G S)
    (hF : ∀ {S T : CommAlgCat k} (a : S ⟶ T) (x : SchemePoints D S),
      F T ((algSpec (CommRingCat.of k)).map a.op ≫ x) =
        (algSpec (CommRingCat.of k)).map a.op ≫ F S x) :
    ∃ j : D ⟶ G, ∀ S x, x ≫ j.hom.hom = F S x := by
  let p : D.X ⟶ G.X := e.inv ≫ F A e.hom
  have hp (S : CommAlgCat k) (x : SchemePoints D S) : x ≫ p = F S x := by
    let Sfun := algSpec (CommRingCat.of k)
    let ff := algSpec.fullyFaithful (R := CommRingCat.of k)
    let a := (ff.preimage (x ≫ e.inv)).unop
    have ha : Sfun.map a.op = x ≫ e.inv := ff.map_preimage _
    have hx : Sfun.map a.op ≫ e.hom = x := by rw [ha, Category.assoc, e.inv_hom_id, Category.comp_id]
    calc
      x ≫ p = (Sfun.map a.op ≫ e.hom) ≫ e.inv ≫ F A e.hom := congrArg (· ≫ p) hx.symm
      _ = Sfun.map a.op ≫ F A e.hom := by
        simp only [Category.assoc, e.hom_inv_id_assoc]
      _ = F S x := (hF a e.hom).symm.trans (congrArg (F S) hx)
  obtain ⟨j, hj⟩ := groupHom_of_affine_point_law p F hp
  exact ⟨j, fun S x => (congrArg (x ≫ ·) hj).trans (hp S x)⟩

set_option maxHeartbeats 700000 in
private theorem restriction_centralKernel (n : ℕ) (h₂ : (2 : k) = 0) :
    let f := restrictionToMarked k n h₂
    ∃ N : Specs.ClosedSubgroup (ambientStabilizer k n), Specs.IsSchemeKernel f N ∧
        Centralizes (𝟙 _) N.inclusion.hom.hom := by
  let f := restrictionToMarked k n h₂
  let H := ambientStabilizer k n
  haveI : IsAffine (markedScheme k n).X.left := markedScheme_affine k n
  haveI : IsAffine H.X.left := stabScheme_affine (ambientForm k n) (ambientBasis k n) (markedVector k n)
  obtain ⟨N, hN⟩ := schemeKernel_exists f
  refine ⟨N, hN, ?_⟩
  haveI : IsClosedImmersion N.inclusion.hom.hom.left := N.isClosedImmersion
  haveI : IsAffine N.group.X.left := isAffine_of_isAffineHom N.inclusion.hom.hom.left
  let P := H.X ⊗ N.group.X
  haveI : IsAffine P.left := tensor_affine
  let e := affineTestIso P
  let p : SchemePoints H (Specs.coordinates P) := e.hom ≫ snd H.X N.group.X ≫ N.inclusion.hom.hom
  let q : SchemePoints H (Specs.coordinates P) := e.hom ≫ fst H.X N.group.X
  have hp : p ≫ f.hom.hom = 1 :=
    (schemeKernel_sections hN p).mp (by
      refine ⟨e.hom ≫ snd H.X N.group.X, ?_⟩
      change (e.hom ≫ snd H.X N.group.X) ≫ N.inclusion.hom.hom = p
      exact Category.assoc _ _ _)
  have hcomm := restrictionScalarKernel_central k n h₂ p q hp
  unfold Centralizes conjugateFamily
  simp only [Grp.id_hom_hom, Category.comp_id]
  apply (cancel_epi e.hom).mp
  simp only [MonObj.comp_mul, GrpObj.comp_inv]
  exact hcomm.mul_inv_cancel


set_option maxHeartbeats 950000 in
set_option maxRecDepth 1500 in
private theorem restriction_kernel_muTwo (n : ℕ) (h₂ : (2 : k) = 0)
    {N : Specs.ClosedSubgroup (ambientStabilizer k n)}
    (hN : Specs.IsSchemeKernel (restrictionToMarked k n h₂) N) :
    ∃ e : SpinFunctor.muTwoScheme k ≅ N.group,
      e.hom ≫ N.inclusion ≫ ambientStabilizerInclusion k n =
        SpinFunctor.scalarSchemeInclusion (ambientForm k n) (ambientBasis k n) := by
  let H := ambientStabilizer k n
  let M := SpinFunctor.muTwoScheme k
  let B := CommAlgCat.of k (muTwoCoordinateRing k)
  let f := restrictionToMarked k n h₂
  let i := ambientStabilizerInclusion k n
  let s := SpinFunctor.scalarSchemeInclusion (ambientForm k n) (ambientBasis k n)
  let a := N.inclusion ≫ i
  have hi : IsClosedImmersion i.hom.hom.left :=
    stabInclusion_closed (ambientForm k n) (ambientBasis k n) (markedVector k n)
  have ha : IsClosedImmersion a.hom.hom.left := by
    have := N.isClosedImmersion
    exact IsClosedImmersion.comp _ _
  have hVal (S : CommAlgCat.{u} k) (q : SchemePoints M S) :
      (ambientPointValues k n S (q ≫ s.hom.hom)).val =
        algebraMap S _ (SpinFunctor.muTwoSchemePoints k S q).val.val :=
    congrArg (fun x => x.val.val) (SpinFunctor.scalarSchemeInclusion_points
      (ambientForm k n) (ambientBasis k n) q)
  have hScalar (S : CommAlgCat.{u} k) (q : SchemePoints M S)
      (t : muTwoCoordinateRing k →ₐ[k] S)
      (ht : SpinFunctor.muTwoSchemePoints k S q = SpinFunctor.muTwoPoints k S t) :
      (ambientPointValues k n S (q ≫ s.hom.hom)).val =
        algebraMap S _ (t (AdjoinRoot.root (muTwoPolynomial k))) := by
    rw [hVal, ht]
    rfl
  let q0 : SchemePoints M B := 𝟙 M.X
  have hq0 : q0 ≫ s.hom.hom = s.hom.hom := Category.id_comp _
  have hfix : Commute (markedClifford (ambientForm k n) (markedVector k n) B)
      (ambientPointValues k n B s.hom.hom).val := by
    rw [← hq0, hVal B q0]
    exact Algebra.commute_algebraMap_right _ _
  obtain ⟨p, hp, _⟩ := (stabScheme_points (ambientForm k n) (ambientBasis k n)
    (markedVector k n) B s.hom.hom).mp hfix
  have hp₀ : p ≫ f.hom.hom = 1 := by
    apply (restrictionScalarKernel_points k n h₂ p).mpr
    let t := (SpinFunctor.muTwoPoints k B).symm (SpinFunctor.muTwoSchemePoints k B q0)
    have hs := hScalar B q0 t ((SpinFunctor.muTwoPoints k B).apply_symm_apply _).symm
    refine ⟨t, ?_, fun v hv => ?_⟩
    · change (ambientPointValues k n B (p ≫ i.hom.hom)).val = _
      rw [hp]
      exact hq0 ▸ hs
    · apply (SpinFunctor.muTwoPoints k B).injective
      apply rootsOfUnity.coe_injective
      change v (AdjoinRoot.root (muTwoPolynomial k)) = t (AdjoinRoot.root (muTwoPolynomial k))
      apply scalar_tensor_injective (ambientForm k n) B (ambientBasis k n)
      change algebraMap B (ScalarClifford (ambientForm k n) B)
          (v (AdjoinRoot.root (muTwoPolynomial k))) =
        algebraMap B (ScalarClifford (ambientForm k n) B)
          (t (AdjoinRoot.root (muTwoPolynomial k)))
      change (ambientPointValues k n B (p ≫ i.hom.hom)).val = _ at hv
      rw [← hv, hp]
      exact hq0 ▸ hs
  let v : M.X ⟶ N.group.X := hN.lift p (toUnit M.X) hp₀
  have hv : v ≫ N.inclusion.hom.hom = p := hN.lift_fst _ _ _
  have hv' : v ≫ a.hom.hom = s.hom.hom := (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ i.hom.hom) hv).trans hp)
  haveI : IsMonHom v := isMonHom_of_comp_closed v s a hv'
  haveI : IsClosedImmersion s.hom.hom.left := SpinFunctor.scalarSchemeInclusion_isClosedImmersion _ _
  haveI : Mono s.hom.hom := Over.mono_of_mono_left _
  haveI : Mono v := by
    haveI : Mono (v ≫ a.hom.hom) := hv' ▸ (inferInstance : Mono s.hom.hom)
    exact mono_of_mono v a.hom.hom
  have hHa : IsAffine H.X.left := stabScheme_affine (ambientForm k n) (ambientBasis k n) (markedVector k n)
  haveI : IsClosedImmersion N.inclusion.hom.hom.left := N.isClosedImmersion
  haveI : IsAffine N.group.X.left := isAffine_of_isAffineHom N.inclusion.hom.hom.left
  let E := affineTestIso N.group.X
  let C := Specs.coordinates N.group.X
  let g : SchemePoints H C := E.hom ≫ N.inclusion.hom.hom
  have hg : g ≫ f.hom.hom = 1 := (schemeKernel_sections hN g).mp ⟨E.hom, rfl⟩
  obtain ⟨t, ht, _⟩ := (restrictionScalarKernel_points k n h₂ g).mp hg
  let q : SchemePoints M C := (SpinFunctor.muTwoSchemePoints k C).symm
    (SpinFunctor.muTwoPoints k C t)
  have hq : q ≫ v = E.hom := by
    haveI : Mono a.hom.hom := Over.mono_of_mono_left _
    apply (cancel_mono a.hom.hom).mp
    rw [Category.assoc, hv']
    apply ((spinUnitPoints_represents (ambientForm k n) (ambientBasis k n)).1 C).1
    apply Units.ext
    have he : E.hom ≫ a.hom.hom = g ≫ i.hom.hom := (Category.assoc _ _ _).symm
    rw [he, ht]
    exact hScalar C q t ((SpinFunctor.muTwoSchemePoints k C).apply_symm_apply _)
  let w : N.group.X ⟶ M.X := E.inv ≫ q
  have hw : w ≫ v = 𝟙 N.group.X := by rw [show w = E.inv ≫ q from rfl, Category.assoc, hq, E.inv_hom_id]
  have hw' : v ≫ w = 𝟙 M.X :=
    (cancel_mono v).mp (by rw [Category.assoc, hw, Category.comp_id, Category.id_comp])
  let e : M.X ≅ N.group.X := ⟨v, w, hw', hw⟩
  let e' : M ≅ N.group := Grp.mkIso e (IsMonHom.one_hom (f := v)) (IsMonHom.mul_hom (f := v))
  refine ⟨e', Grp.hom_ext _ _ ?_⟩
  exact hv'


set_option maxHeartbeats 800000 in
private theorem actualScalarRestrictionKernel (n : ℕ) (h₂ : (2 : k) = 0) :
    HasScalarRestrictionKernel (n := n) (ambientStabilizerInclusion k n)
      (restrictionToMarked k n h₂) (ambientPointValues k n) := by
  obtain ⟨N, hN, hc⟩ := restriction_centralKernel n h₂
  obtain ⟨j, hj⟩ := restriction_kernel_muTwo n h₂ hN
  refine ⟨SpinFunctor.muTwoScheme k, rfl, N, j, hN, hc, ?_⟩
  intro S t
  have ht : j.hom.hom.hom ≫ N.inclusion.hom.hom ≫ (ambientStabilizerInclusion k n).hom.hom =
      (SpinFunctor.scalarSchemeInclusion (ambientForm k n) (ambientBasis k n)).hom.hom :=
    congrArg (fun z : SpinFunctor.muTwoScheme k ⟶ ambientGroupScheme k n => z.hom.hom) hj
  let p : SchemePoints (SpinFunctor.muTwoScheme k) S :=
    (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom t).op
  simp only [eqToHom_refl, Category.id_comp, ht]
  have h := congrArg (fun x => x.val.val) (SpinFunctor.scalarSchemeInclusion_points
    (ambientForm k n) (ambientBasis k n) p)
  change (ambientPointValues k n S (p ≫
    (SpinFunctor.scalarSchemeInclusion (ambientForm k n) (ambientBasis k n)).hom.hom)).val =
      algebraMap S _ (SpinFunctor.muTwoSchemePoints k S p).val.val at h
  have hr : (SpinFunctor.muTwoSchemePoints k S p).val.val =
      t (AdjoinRoot.root (muTwoPolynomial k)) := by
    rw [show p = (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom t).op from rfl,
      muTwoSchemePoints_onSpec]
    rfl
  rwa [hr] at h

end AffinePointMorphisms

section DiagonalSchemePoints

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite SpinSpecification
open LaurentPolynomial WithConv
open scoped CategoryTheory.MonObj TensorProduct Matrix
open private spinUnitPoints_represents from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinFunctor

variable {R R' : Type u} [CommRing R] [CommRing R'] {n : ℕ}

private def diagonalWeights : (Fin n → Rˣ) →* (OddIndex n → Rˣ) where
  toFun t := WithTop.recTopCoe 1 (fun j => (ofLex j).elim t (fun i => (t i)⁻¹))
  map_one' := by
    funext j
    cases j using WithTop.recTopCoe with
    | top => rfl
    | coe j =>
      obtain ⟨a, rfl⟩ := toLex.surjective j
      cases a <;> simp
  map_mul' s t := by
    funext j
    cases j using WithTop.recTopCoe with
    | top => exact (one_mul _).symm
    | coe j =>
      obtain ⟨a, rfl⟩ := toLex.surjective j
      cases a <;> simp [mul_comm]

private theorem diagonalWeights_map (f : R →+* R') (t : Fin n → Rˣ) (i : OddIndex n) :
    diagonalWeights (fun j => Units.map f.toMonoidHom (t j)) i =
      Units.map f.toMonoidHom (diagonalWeights t i) := by
  cases i using WithTop.recTopCoe with
  | top => exact (map_one _).symm
  | coe i =>
    obtain ⟨j, rfl⟩ := toLex.surjective i
    cases j <;> simp [diagonalWeights]

private def mkDiagonalGL : (OddIndex n → Rˣ) →* Matrix.GeneralLinearGroup (OddMatrixIndex.{u} n) R where
  toFun w :=
    ⟨Matrix.diagonal (fun j => (w j.down : R)), Matrix.diagonal (fun j => (↑(w j.down)⁻¹ : R)),
      by rw [Matrix.diagonal_mul_diagonal]; simp, by rw [Matrix.diagonal_mul_diagonal]; simp⟩
  map_one' := by apply Units.ext; exact Matrix.diagonal_one
  map_mul' _ _ := by
    apply Units.ext
    exact (Matrix.diagonal_mul_diagonal _ _).symm

private abbrev diagonalGL : (Fin n → Rˣ) →* Matrix.GeneralLinearGroup (OddMatrixIndex.{u} n) R :=
  mkDiagonalGL.comp diagonalWeights

private theorem diagonalGL_action (t : Fin n → Rˣ) (x : OddModule R n) :
    oddMatrixAction (diagonalGL t) x = diagonalOddVector t x := by
  rw [oddMatrixAction_apply]
  funext i
  change (Matrix.diagonal (fun j : OddMatrixIndex.{u} n => (diagonalWeights t j.down : R))
    *ᵥ (fun j : OddMatrixIndex.{u} n => x j.down)) (ULift.up i) = _
  rw [Matrix.mulVec_diagonal]
  cases i using WithTop.recTopCoe with
  | top => exact one_mul _
  | coe i =>
    obtain ⟨j, rfl⟩ := toLex.surjective i
    cases j <;> rfl

private theorem diagonalGL_marked (t : Fin n → Rˣ) : diagonalGL t ∈ MarkedIsometries R n := by
  change (∀ x, oddForm R n (oddMatrixAction (diagonalGL t) x) = oddForm R n x) ∧
    oddMatrixAction (diagonalGL t) (radicalVector R n) = radicalVector R n
  simp only [diagonalGL_action]
  refine ⟨fun x => ?_, ?_⟩
  · simp only [oddForm_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    change ((t i : R) * _) * ((↑(t i)⁻¹ : R) * _) = _
    rw [mul_mul_mul_comm, Units.mul_inv, one_mul]
  · funext j
    cases j using WithTop.recTopCoe with
    | top => rfl
    | coe j =>
      obtain ⟨a, rfl⟩ := toLex.surjective j
      cases a <;> simp [diagonalOddVector, Pi.single_apply]

private def diagonalMarked : (Fin n → Rˣ) →* MarkedIsometries R n :=
  diagonalGL.codRestrict _ diagonalGL_marked

private theorem diagonalMarked_natural (f : R →+* R') (t : Fin n → Rˣ) :
    diagonalMarked (fun i => Units.map f.toMonoidHom (t i)) = markedMap n f (diagonalMarked t) := by
  apply Subtype.ext
  apply Units.ext
  change Matrix.diagonal (fun j : OddMatrixIndex n =>
    (diagonalWeights (fun i => Units.map f.toMonoidHom (t i)) j.down : R')) =
    (Matrix.diagonal (fun j : OddMatrixIndex n => (diagonalWeights t j.down : R))).map f
  rw [Matrix.diagonal_map (map_zero f)]
  congr 1
  funext j
  exact congrArg Units.val (diagonalWeights_map f t j.down)

variable {k : Type u} [Field k]

private def laurentCoordinates (S : CommAlgCat.{u} k) :
    WithConv (LaurentPolynomial k →ₐ[k] S) ≃* SchemePoints (laurentMultiplicativeGroup k) S :=
  Spec.mapMulEquiv (R := k) (S := LaurentPolynomial k) (T := S)

private def laurentUnit (S : CommAlgCat.{u} k) : SchemePoints (laurentMultiplicativeGroup k) S →* Sˣ where
  toFun p := Units.map ((laurentCoordinates S).symm p).ofConv.toMonoidHom ((isUnit_T (R := k) 1).unit)
  map_one' := by
    apply Units.ext
    change ((laurentCoordinates S).symm 1).ofConv ((isUnit_T (R := k) 1).unit : LaurentPolynomial k) = 1
    rw [IsUnit.unit_spec, map_one]
    exact (AlgHom.convOne_apply (T 1)).trans (by rw [LaurentPolynomial.counit_T, map_one])
  map_mul' p q := by
    apply Units.ext
    change ((laurentCoordinates S).symm (p * q)).ofConv ((isUnit_T (R := k) 1).unit : LaurentPolynomial k) =
      ((laurentCoordinates S).symm p).ofConv ((isUnit_T (R := k) 1).unit : LaurentPolynomial k) *
        ((laurentCoordinates S).symm q).ofConv ((isUnit_T (R := k) 1).unit : LaurentPolynomial k)
    simp only [IsUnit.unit_spec, map_mul]
    change ((laurentCoordinates S).symm p * (laurentCoordinates S).symm q) (T 1) = _
    rw [AlgHom.convMul_apply, LaurentPolynomial.comul_T, Algebra.TensorProduct.lift_tmul]

private theorem laurentUnit_natural {S T : CommAlgCat.{u} k} (f : S ⟶ T)
    (p : SchemePoints (laurentMultiplicativeGroup k) S) :
    laurentUnit T ((algSpec (CommRingCat.of k)).map f.op ≫ p) =
      Units.map f.hom.toMonoidHom (laurentUnit S p) := by
  let A := CommHopfAlgCat.of k (LaurentPolynomial k)
  let e := hopfSpecPointIso A
  let g := (laurentCoordinates S).symm p
  have h := congrArg (fun j => j g) (e.hom.naturality f)
  change (laurentCoordinates T) (toConv (f.hom.comp g.ofConv)) =
    (algSpec (CommRingCat.of k)).map f.op ≫ laurentCoordinates S g at h
  rw [MulEquiv.apply_symm_apply] at h
  apply Units.ext
  change ((laurentCoordinates T).symm ((algSpec (CommRingCat.of k)).map f.op ≫ p)).ofConv (↑(isUnit_T (R := k) 1).unit) = _
  rw [← h, MulEquiv.symm_apply_apply]
  rfl

private def laurentMonomialUnit (k : Type u) [Field k] :
    Multiplicative ℤ →* (LaurentPolynomial k)ˣ :=
  MonoidHom.toHomUnits {
    toFun m := T m.toAdd
    map_one' := T_zero
    map_mul' s t := T_add s.toAdd t.toAdd }

private theorem laurent_monomial (m : ℤ) :
    Units.val ((isUnit_T (R := k) 1).unit ^ m) = T m := by
  have h : (isUnit_T (R := k) 1).unit = laurentMonomialUnit k (Multiplicative.ofAdd 1) :=
    Units.ext (isUnit_T (R := k) 1).unit_spec
  rw [h, ← map_zpow]
  change T ((Multiplicative.ofAdd (1 : ℤ) ^ m).toAdd) = T m
  simp

private theorem laurentUnit_generic :
    laurentUnit (CommAlgCat.of k (LaurentPolynomial k)) (𝟙 (laurentMultiplicativeGroup k).X) =
      (isUnit_T (R := k) 1).unit := by
  let S := CommAlgCat.of k (LaurentPolynomial k)
  let e := laurentCoordinates S
  let a : WithConv (LaurentPolynomial k →ₐ[k] S) := toConv (AlgHom.id k (LaurentPolynomial k))
  have h : e a = (𝟙 (laurentMultiplicativeGroup k).X : SchemePoints (laurentMultiplicativeGroup k) S) := by
    apply Over.OverMorphism.ext
    exact Spec.map_id _
  change laurentUnit S (𝟙 (laurentMultiplicativeGroup k).X) = _
  rw [← h]
  apply Units.ext
  change (e.symm (e a)).ofConv ((isUnit_T (R := k) 1).unit).val = _
  rw [MulEquiv.symm_apply_apply]
  rfl


private def diagonalCocharacterPoints {n : ℕ} (m : Fin n → ℤ) (S : CommAlgCat.{u} k) :
    SchemePoints (laurentMultiplicativeGroup k) S →* SchemePoints (markedScheme k n) S :=
  (markedSchemePoints k n S).symm.toMonoidHom.comp <|
    diagonalMarked.comp
      { toFun p i := (laurentUnit S p) ^ m i
        map_one' := by funext i; simp
        map_mul' := by intro p q; funext i; simp [mul_zpow] }

private theorem diagonalCocharacterPoints_natural {n : ℕ} (m : Fin n → ℤ)
    {S T : CommAlgCat.{u} k} (f : S ⟶ T) (p : SchemePoints (laurentMultiplicativeGroup k) S) :
    diagonalCocharacterPoints m T ((algSpec (CommRingCat.of k)).map f.op ≫ p) =
      (algSpec (CommRingCat.of k)).map f.op ≫ diagonalCocharacterPoints m S p := by
  apply (markedSchemePoints k n T).injective
  rw [markedSchemePoints_natural]
  change (markedSchemePoints k n T) ((markedSchemePoints k n T).symm
      (diagonalMarked (fun i => (laurentUnit T ((algSpec (CommRingCat.of k)).map f.op ≫ p)) ^ m i))) =
    markedMap n f.hom.toRingHom
      ((markedSchemePoints k n S) ((markedSchemePoints k n S).symm
        (diagonalMarked (fun i => (laurentUnit S p) ^ m i))))
  rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, laurentUnit_natural]
  simpa only [map_zpow] using
    diagonalMarked_natural f.hom.toRingHom (fun i => (laurentUnit S p) ^ m i)


set_option maxHeartbeats 650000 in
private theorem diagonalCocharacterExists {n : ℕ} (m : Fin n → ℤ) :
    ∃ χ : laurentMultiplicativeGroup k ⟶ markedScheme k n,
      HasDiagonalExponents (markedSchemePoints k n) χ m := by
  let A := CommAlgCat.of k (LaurentPolynomial k)
  haveI : IsAffine (laurentMultiplicativeGroup k).X.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of A)))
  obtain ⟨χ, hχ⟩ := groupHom_of_natural_points A (Iso.refl (laurentMultiplicativeGroup k).X)
    (diagonalCocharacterPoints m) (fun f p => diagonalCocharacterPoints_natural m f p)
  let t (i : Fin n) := (isUnit_T (R := k) 1).unit ^ m i
  refine ⟨χ, t, fun i => laurent_monomial (m i), ?_⟩
  have hp : χ.hom.hom = diagonalCocharacterPoints m A (𝟙 (laurentMultiplicativeGroup k).X) :=
    (CategoryTheory.Category.id_comp χ.hom.hom).symm.trans
      (hχ A (𝟙 (laurentMultiplicativeGroup k).X))
  have h := congrArg (markedSchemePoints k n A) hp
  change markedSchemePoints k n A χ.hom.hom =
    (markedSchemePoints k n A) ((markedSchemePoints k n A).symm
      (diagonalMarked (fun i => (laurentUnit A (𝟙 (laurentMultiplicativeGroup k).X)) ^ m i))) at h
  rw [MulEquiv.apply_symm_apply, laurentUnit_generic] at h
  intro x
  rw [h]
  exact diagonalGL_action t x

end DiagonalSchemePoints

section DiagonalRestrictionFibre

open AlgebraicGeometry CategoryTheory Opposite SpinSpecification
open scoped CategoryTheory.MonObj TensorProduct
open private spinUnitPoints_represents from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinFunctor

variable {k : Type u} [Field k] (n : ℕ)

private theorem nativeStabilizerValue_injective (S : CommAlgCat.{u} k) :
    Function.Injective (nativeStabilizerValue (k := k) (S := S) n) := by
  intro p q h
  have hp := (Units.mapEquiv (ambientCliffordEquiv k S n).toMulEquiv).injective h
  have he := ((spinUnitPoints_represents (ambientForm k n) (ambientBasis k n)).1 S).1
  have h' : p ≫ (ambientStabilizerInclusion k n).hom.hom = q ≫ (ambientStabilizerInclusion k n).hom.hom :=
    he hp
  haveI : IsClosedImmersion (ambientStabilizerInclusion k n).hom.hom.left :=
    stabInclusion_closed (ambientForm k n) (ambientBasis k n) (markedVector k n)
  haveI : Mono (ambientStabilizerInclusion k n).hom.hom := Over.mono_of_mono_left _
  exact (cancel_mono _).mp h'

private theorem scaledDiagUnit_unique {S : CommAlgCat.{u} k} (b : (CliffordAlgebra (ambientForm S n))ˣ)
    (u v : Sˣ)
    (h : Units.map (algebraMap S (CliffordAlgebra (ambientForm S n))).toMonoidHom u * b =
      Units.map (algebraMap S (CliffordAlgebra (ambientForm S n))).toMonoidHom v * b) :
    u = v := by
  apply Units.ext
  apply scalar_injective (ambientForm S n) (Pi.basisFun S (AmbientIndex n))
  exact congrArg Units.val (mul_right_cancel h)

set_option maxHeartbeats 600000 in
private theorem diagonalRestrictionFibre (h₂ : (2 : k) = 0) (S : CommAlgCat.{u} k)
    (t : Fin n → Sˣ) :
    let Q := ambientForm S n
    let b := diagonalLift n t
    b.val ∈ evenOdd Q 0 ∧ reverse b.val * b.val = algebraMap S _ (∏ i, (t i : S)) ∧
      (∀ p : SchemePoints (ambientStabilizer k n) S,
        (∀ x, oddMatrixAction (markedSchemePoints k n S
          (p ≫ (restrictionToMarked k n h₂).hom.hom)).val x = diagonalOddVector t x) ↔
        ∃! u : Sˣ, (u : S) ^ 2 * (∏ i, (t i : S)) = 1 ∧
          nativeStabilizerValue n p = Units.map (algebraMap S (CliffordAlgebra Q)).toMonoidHom u * b) ∧
      (∀ u : Sˣ, (u : S) ^ 2 * (∏ i, (t i : S)) = 1 →
        ∃! p : SchemePoints (ambientStabilizer k n) S,
          nativeStabilizerValue n p = Units.map (algebraMap S (CliffordAlgebra Q)).toMonoidHom u * b ∧
          ∀ x, oddMatrixAction (markedSchemePoints k n S
            (p ≫ (restrictionToMarked k n h₂).hom.hom)).val x = diagonalOddVector t x) := by
  intro Q b
  have h₂S : (2 : S) = 0 := by
    simpa only [map_ofNat, map_zero] using congrArg (algebraMap k S) h₂
  obtain ⟨he, hn, _⟩ := diagonalLift_spec n t
  have hb := diagonalNormEquation_for_lift n h₂S t
  dsimp only at hb
  refine ⟨he, hn, ?_, ?_⟩
  · intro p
    have hspin := nativeStabilizerValue_spec n p
    rw [← hb]
    refine ⟨fun h => ⟨hspin.1, hspin.2, ?_⟩, fun h x => ?_⟩
    · intro x
      have h' := restriction_nativeAction n h₂ p x
      rw [h x] at h'
      exact h'
    · have h' := h.2.2 x
      have h' := (restriction_nativeAction n h₂ p x).symm.trans h'
      exact congrArg (fun y : AmbientModule S n => fun j : OddIndex n => y j)
        (intrinsic_vector_injective n Q h')
  · intro u hu
    let a := Units.map (algebraMap S (CliffordAlgebra Q)).toMonoidHom u * b
    have hv : ∃! v : Sˣ, (v : S) ^ 2 * (∏ i, (t i : S)) = 1 ∧
        a = Units.map (algebraMap S (CliffordAlgebra Q)).toMonoidHom v * b :=
      ⟨u, ⟨hu, rfl⟩, fun v hv => scaledDiagUnit_unique n b v u hv.2.symm⟩
    obtain ⟨ha, hr, hact⟩ := (hb a).mpr hv
    obtain ⟨p, hp⟩ := nativeStabilizerValue_surj n a ha hr
    refine ⟨p, ⟨hp, ?_⟩, fun q hq => (nativeStabilizerValue_injective n S) (hq.1.trans hp.symm)⟩
    intro x
    have h := restriction_nativeAction n h₂ p x
    rw [hp] at h
    exact congrArg (fun y : AmbientModule S n => fun j : OddIndex n => y j)
      (intrinsic_vector_injective n Q (h.symm.trans (hact x)))


private theorem diagonalLift_tensor_natural {S T : CommAlgCat.{u} k} (f : S ⟶ T)
    (t : Fin n → Sˣ) :
    Units.map (coefficientMap (ambientForm k n) S f.hom).toMonoidHom
        (Units.map (ambientCliffordEquiv k S n).symm.toMonoidHom (diagonalLift n t)) =
      Units.map (ambientCliffordEquiv k T n).symm.toMonoidHom
        (diagonalLift n (fun j => Units.map f.hom.toMonoidHom (t j))) := by
  let e := ambientCliffordEquiv k T n
  apply (Units.mapEquiv e.toMulEquiv).injective
  apply Units.ext
  let b := diagonalLift n t
  let b' := diagonalLift n (fun j => Units.map f.hom.toMonoidHom (t j))
  let x := (ambientCliffordEquiv k S n).symm b.val
  change e (SpinFunctor.changeCoefficients (ambientForm k n) f.hom x) = e (e.symm b'.val)
  have hx : ambientCliffordEquiv k S n x = b.val :=
    (ambientCliffordEquiv k S n).apply_symm_apply b.val
  rw [e.apply_symm_apply, ← ambientCoefficients_apply, hx]
  exact congrArg Units.val (diagonalLift_natural n f.hom t).symm

end DiagonalRestrictionFibre

section RestrictionCover

open AlgebraicGeometry CategoryTheory Opposite SpinSpecification
open scoped TensorProduct
open private spinUnitPoints_represents from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinFunctor

set_option maxHeartbeats 600000 in
set_option maxRecDepth 1500 in
theorem splitRestrictionCover : SplitRestrictionCover.{u} := by
  intro k _ n h₂ hn
  let Q := ambientForm k n
  let b := ambientBasis k n
  let r := markedVector k n
  let H := ambientStabilizer k n
  let O := markedScheme k n
  have hH : Smooth H.X.hom := by
    change Smooth (Spec.map (CommRingCat.ofHom (algebraMap k (StabilizerRing Q b r))))
    exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
      (RingHom.smooth_algebraMap.mpr (stabilizerRing_smooth k n h₂ hn))
  have hO : Smooth O.X.hom := by
    change Smooth (Spec.map (CommRingCat.ofHom (algebraMap k (OddIsometryRing k n))))
    exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
      (RingHom.smooth_algebraMap.mpr (markedRing_smooth k n h₂))
  refine ⟨ambientGroupScheme k n, ambientStabilizer k n, markedScheme k n,
    ambientStabilizerInclusion k n, restrictionToMarked k n h₂, ambientPointValues k n,
    markedSchemePoints k n, spinUnitPoints_represents Q b, stabInclusion_closed Q b r,
    stabScheme_affine Q b r, hH, markedScheme_affine k n, hO, restriction_finite k n h₂,
    (restriction_flat_surjective k n h₂).1, (restriction_flat_surjective k n h₂).2,
    restriction_radicial k n h₂, restriction_geometricallyConnected k n h₂, ?_,
    actualScalarRestrictionKernel n h₂, ?_, fun m => diagonalCocharacterExists m, ?_,
    fun f p => congrArg Subtype.val (markedSchemePoints_natural k n f p),
    fun S => ⟨stabScheme_points Q b r S, restrictionToMarked_vectorAction k n h₂,
      restrictionScalarKernel_points k n h₂, restrictionScalarKernel_central k n h₂⟩⟩
  · rintro ⟨hOfin, hred⟩
    have hHfin : IsAffine H.X.left ∧ LocallyOfFiniteType H.X.hom ∧ QuasiCompact H.X.hom := by
      refine ⟨stabScheme_affine Q b r, inferInstance, ?_⟩
      change QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap k (StabilizerRing Q b r))))
      infer_instance
    refine ⟨hHfin, smooth_source_reductive (⟨H, hHfin⟩ : Specs.AffineAlgebraicGroup k)
      (⟨O, hOfin⟩ : Specs.AffineAlgebraicGroup k) (restrictionToMarked k n h₂)
      (restriction_flat_surjective k n h₂).2 (restriction_radicial k n h₂) hH
      (restriction_geometricallyConnected k n h₂ hred.2.1) hred⟩
  · refine ⟨fun S => ambientCliffordEquiv k S n, fun _ t => diagonalLift n t,
      diagonalLift_tensor_natural n, fun S => ⟨?_, diagonalRestrictionFibre n h₂ S⟩⟩
    exact nativeClifford_vector (ambientForm k n) (ambientForm S n) (ambient_map n)
  · intro χ m hm
    obtain ⟨t, ht, hχ⟩ := hm
    exact actualDiagonalCocharacters n h₂ hn χ m t ht hχ

end RestrictionCover

end

end LinearAlgebraicGroups.Arithmetic.OddSpinCharTwoStabilizer
