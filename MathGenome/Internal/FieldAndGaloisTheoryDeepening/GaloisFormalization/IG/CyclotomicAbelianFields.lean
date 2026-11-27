import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.IG.CyclotomicAbelianFields
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.IG.FreshPrimes
import MathGenome.Internal.D07.Ch15.CyclotomicGalois
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

namespace GaloisFormalization.IG

open scoped BigOperators

private theorem exists_injective_prime_family {ι : Type*} [Fintype ι]
    (n : ι → ℕ) (hn : ∀ i, 2 ≤ n i) :
    ∃ p : ι → ℕ, Function.Injective p ∧ ∀ i, (p i).Prime ∧ n i ∣ p i - 1 := by
  classical
  have select (T : Finset ι) :
      ∃ p : ι → ℕ, Set.InjOn p (↑T : Set ι) ∧
        ∀ i ∈ T, (p i).Prime ∧ n i ∣ p i - 1 := by
    induction T using Finset.induction_on with
    | empty =>
      exact ⟨fun _ => 0, by simp, by simp⟩
    | @insert a T ha ih =>
      obtain ⟨p, hp, hprime⟩ := ih
      have hT : ∀ q ∈ T.image p, Nat.Prime q := by
        intro q hq
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
        exact (hprime i hi).1
      obtain ⟨r, hr, hfresh, hdvd⟩ := exists_fresh_prime (n a) (hn a) (T.image p) hT
      let p' (i : ι) := if i = a then r else p i
      have hp'a : p' a = r := ite_eq_left rfl
      have hp'T (i : ι) (hi : i ∈ T) : p' i = p i :=
        ite_eq_right (show i ≠ a from fun h => ha (h ▸ hi))
      have hne (i : ι) (hi : i ∈ T) : r ≠ p i :=
        fun h => hfresh (h ▸ Finset.mem_image_of_mem p hi)
      refine ⟨p', ?_, ?_⟩
      · intro i hi j hj hij
        by_cases hia : i = a
        · subst i
          rcases Finset.mem_insert.mp hj with rfl | hjT
          · rfl
          · exact (hne _ hjT ((hp'a.symm.trans hij).trans (hp'T _ hjT))).elim
        · have hiT := (Finset.mem_insert.mp hi).resolve_left hia
          rcases Finset.mem_insert.mp hj with rfl | hjT
          · exact (hne _ hiT ((hp'a.symm.trans hij.symm).trans (hp'T _ hiT))).elim
          · exact hp hiT hjT ((hp'T _ hiT).symm.trans (hij.trans (hp'T _ hjT)))
      · intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · rw [hp'a]
          exact ⟨hr, hdvd⟩
        · rw [hp'T _ hi]
          exact hprime _ hi
  obtain ⟨p, hp, hprime⟩ := select Finset.univ
  exact ⟨p, fun _ _ => hp (Finset.mem_univ _) (Finset.mem_univ _),
    fun i => hprime i (Finset.mem_univ _)⟩

private theorem exists_cyclic_quotient_of_prime_units (p n : ℕ) [Fact p.Prime]
    (h : n ∣ p - 1) :
    ∃ f : (ZMod p)ˣ →* Multiplicative (ZMod n), Function.Surjective f := by
  classical
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
  let e : (ZMod p)ˣ ≃* Multiplicative (ZMod (p - 1)) :=
    hcard ▸ (zmodCyclicMulEquiv (G := (ZMod p)ˣ) inferInstance).symm
  let f := (ZMod.castHom h (ZMod n)).toAddMonoidHom.toMultiplicative
  exact ⟨f.comp e.toMonoidHom, (ZMod.castHom_surjective h).comp e.surjective⟩

open IntermediateField in
private theorem realizations_of_surjective_product
    {K L Ω : Type*} [Field K] [Field L] [Field Ω] [Algebra K L] [Algebra K Ω]
    [FiniteDimensional K L] [IsGalois K L] {A ι : Type*} [Group A]
    (emb : L →ₐ[K] Ω) (q : (L ≃ₐ[K] L) →* (ι → A)) (hq : Function.Surjective q) :
    ∃ F : ι → IntermediateField K Ω,
      (∀ j, FiniteDimensional K (F j) ∧ IsGalois K (F j) ∧
        Nonempty ((F j ≃ₐ[K] F j) ≃* A)) ∧
      (∀ j h, j ≠ h → F j ⊓ F h = ⊥) ∧
      (Subsingleton A → ∀ j, F j = ⊥) := by
  classical
  let qj (j : ι) := (Pi.evalMonoidHom (fun _ : ι => A) j).comp q
  have hqj (j : ι) : Function.Surjective (qj j) := by
    intro a
    obtain ⟨g, hg⟩ := hq (fun _ => a)
    exact ⟨g, congrFun hg j⟩
  let M (j : ι) := fixedField (qj j).ker
  refine ⟨fun j => (M j).map emb, ?_, ?_, ?_⟩
  · intro j
    have : IsGalois K (M j) := IsGalois.of_fixedField_normal_subgroup (qj j).ker
    have : FiniteDimensional K (M j) := IntermediateField.finiteDimensional_left (M j)
    let e := (M j).equivMap emb
    exact ⟨e.toLinearEquiv.finiteDimensional, IsGalois.of_algEquiv e,
      ⟨e.autCongr.symm.trans <|
        (IsGalois.normalAutEquivQuotient (qj j).ker).symm.trans <|
          QuotientGroup.quotientKerEquivOfSurjective (qj j) (hqj j)⟩⟩
  · intro j h hjh
    have hM : M j ⊓ M h = ⊥ := by
      apply le_antisymm _ bot_le
      intro x hx
      rcases (show x ∈ M j ∧ x ∈ M h from hx) with ⟨hxj, hxh⟩
      apply (IsGalois.mem_bot_iff_fixed x).mpr
      intro g
      -- Write g as a product of elements of the two coordinate kernels.
      obtain ⟨b, hb⟩ := hq (fun i => if i = j then q g j else 1)
      have hbj : q b j = q g j := by simpa using congrFun hb j
      have hbker : b ∈ (qj h).ker := by
        change q b h = 1
        simpa [Ne.symm hjh] using congrFun hb h
      have haker : g * b⁻¹ ∈ (qj j).ker := by
        change q (g * b⁻¹) j = 1
        simp [hbj]
      have hax := (mem_fixedField_iff _ _).mp hxj _ haker
      have hbx := (mem_fixedField_iff _ _).mp hxh _ hbker
      calc
        g x = ((g * b⁻¹) * b) x := by rw [mul_assoc, inv_mul_cancel, mul_one]
        _ = x := by rw [AlgEquiv.mul_apply, hbx, hax]
    rw [← IntermediateField.map_inf, hM, IntermediateField.map_bot]
  · intro hA j
    have hker : (qj j).ker = ⊤ := by
      exact top_unique fun g _ => hA.elim (qj j g) 1
    change (fixedField (qj j).ker).map emb = ⊥
    rw [hker, IsGalois.fixedField_top, IntermediateField.map_bot]

/-- Any finite number of copies of a finite abelian group can be realized by
finite Galois subfields of a fixed separable closure of `ℚ`, with pairwise
intersection equal to the base field. -/
theorem exists_pairwise_disjoint_galois_realizations :
    Specs.GaloisFormalization.IG.PairwiseDisjointGaloisRealizations := by
  intro Ω _ alg _ A _ _ s
  classical
  -- The cyclotomic equivalence uses the canonical rational algebra structure.
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have halg : alg = (DivisionRing.toRatAlgebra : Algebra ℚ Ω) := Subsingleton.elim _ _
  subst alg
  obtain ⟨ι, _, n, hn, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite A
  obtain ⟨p, hp, hprime⟩ :=
    exists_injective_prime_family (fun ji : Fin s × ι => n ji.2) (fun ji => hn ji.2)
  let m := ∏ ji, p ji
  have hm : 0 < m := Finset.prod_pos fun ji _ => (hprime ji).1.pos
  have hcoprime : Pairwise (fun i j => (p i).Coprime (p j)) :=
    fun i j hij => (Nat.coprime_primes (hprime i).1 (hprime j).1).2 (hp.ne hij)
  have : IsSepClosed Ω := IsSepClosure.sep_closed ℚ
  have : NeZero m := ⟨hm.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot Ω m
  let L := IntermediateField.adjoin ℚ ({ζ} : Set Ω)
  have : FiniteDimensional ℚ L :=
    (D07.Ch15.CyclotomicGalois.cyclotomic_degree Ω m hm ζ hζ).1
  have : IsGalois ℚ L :=
    (D07.Ch15.CyclotomicGalois.cyclotomic_splitting_galois Ω m hm ζ hζ).2.2
  obtain ⟨g, _⟩ := D07.Ch15.CyclotomicGalois.cyclotomic_galois_equivalence Ω m hm ζ hζ
  let crt := Units.mapEquiv (ZMod.prodEquivPi p hcoprime).toMulEquiv
  let u : (L ≃ₐ[ℚ] L) ≃* ((ji : Fin s × ι) → (ZMod (p ji))ˣ) :=
    g.trans (crt.trans MulEquiv.piUnits)
  have hquot (ji : Fin s × ι) :
      ∃ f : (ZMod (p ji))ˣ →* Multiplicative (ZMod (n ji.2)), Function.Surjective f := by
    have : Fact (p ji).Prime := ⟨(hprime ji).1⟩
    exact exists_cyclic_quotient_of_prime_units (p ji) (n ji.2) (hprime ji).2
  choose f hf using hquot
  let block : ((ji : Fin s × ι) → (ZMod (p ji))ˣ) →* (Fin s → A) :=
    MonoidHom.pi fun j => e.symm.toMonoidHom.comp <|
      MonoidHom.pi fun i => (f (j, i)).comp (Pi.evalMonoidHom _ (j, i))
  have hblock : Function.Surjective block := by
    intro a
    choose x hx using fun ji : Fin s × ι => hf ji (e (a ji.1) ji.2)
    refine ⟨x, ?_⟩
    funext j
    change e.symm (fun i => f (j, i) (x (j, i))) = a j
    apply e.symm_apply_eq.mpr
    funext i
    exact hx (j, i)
  exact realizations_of_surjective_product L.val (block.comp u.toMonoidHom)
    (hblock.comp u.surjective)

end GaloisFormalization.IG
