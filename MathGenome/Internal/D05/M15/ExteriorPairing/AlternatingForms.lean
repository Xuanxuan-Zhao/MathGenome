import MathGenome.Internal.Specs.D05.M15.ExteriorPairing.AlternatingForms
import MathGenome.Internal.D05.M15.ExteriorPairing
import MathGenome.Internal.D05.M15.InteriorProduct
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Fintype.Sort
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.Order.Hom.Set

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
namespace D05.M15.ExteriorPairing.AlternatingForms
open Specs.D05.M15.ExteriorPairing.AlternatingForms
universe u v
variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

abbrev toForm : toForm_type := toForm_value
abbrev shuffleProduct : shuffleProduct_type := shuffleProduct_value

theorem evaluation : Specs.D05.M15.ExteriorPairing.AlternatingForms.evaluation := by
  intro K V _ _ _ p a x
  exact exteriorPower.alternatingMapLinearEquiv_symm_apply _ _

theorem elementary : Specs.D05.M15.ExteriorPairing.AlternatingForms.elementary := by
  intro K V _ _ _ p f x
  rw [evaluation, D05.M15.ExteriorPairing.elementary]

theorem identification : Specs.D05.M15.ExteriorPairing.AlternatingForms.identification := by
  intro K V _ _ _ _ p
  obtain ⟨e, he⟩ := D05.M15.ExteriorPairing.perfect (K := K) (V := V) p
  refine ⟨e.trans exteriorPower.alternatingMapLinearEquiv.symm, ?_⟩
  change exteriorPower.alternatingMapLinearEquiv.symm.toLinearMap.comp e.toLinearMap = _
  rw [he]
  rfl

theorem degree_zero : Specs.D05.M15.ExteriorPairing.AlternatingForms.degree_zero := by
  intro K V _ _ _ c x
  rw [evaluation]
  have hx : exteriorPower.ιMulti K 0 x = (exteriorPower.zeroEquiv K V).symm 1 := by
    apply (exteriorPower.zeroEquiv K V).injective
    simp
  rw [hx, D05.M15.ExteriorPairing.degree_zero, mul_one]

/-- The image of an elementary exterior covector is the *unnormalized*
antisymmetrization of its ordinary tensor form, in every characteristic. -/
theorem elementary_alternatization (p : ℕ) (f : Fin p → Module.Dual K V) :
    toForm K V p (exteriorPower.ιMulti K p f) =
      (covectorTensorForm p f).alternatization := by
  apply AlternatingMap.ext
  intro x
  rw [evaluation]
  change exteriorPower.pairingDual K V p (exteriorPower.ιMulti K p f)
    (exteriorPower.ιMulti K p x) = _
  rw [exteriorPower.pairingDual_ιMulti_ιMulti, MultilinearMap.alternatization_apply,
    Matrix.det_apply]
  apply Finset.sum_congr rfl
  intro σ _
  rfl

theorem tensor_normalization :
    Specs.D05.M15.ExteriorPairing.AlternatingForms.tensor_normalization := by
  intro K V _ _ _ _ p f
  rw [elementary_alternatization]
  simp only [averageForm, Fintype.card_fin, smul_smul]
  rw [mul_inv_cancel₀ (Nat.cast_ne_zero.mpr p.factorial_ne_zero), one_smul]

/-- Antisymmetrization is independent of the names of the argument indices. -/
theorem alternatization_domDomCongr {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : ι ≃ κ)
    (T : MultilinearMap K (fun _ : ι => V) K) :
    (T.domDomCongr e).alternatization = T.alternatization.domDomCongr e := by
  ext x
  symm
  simp only [AlternatingMap.domDomCongr_apply, MultilinearMap.alternatization_apply,
    MultilinearMap.domDomCongr_apply]
  apply Fintype.sum_equiv e.permCongr
  intro σ
  rw [Equiv.Perm.sign_permCongr]
  congr 2
  funext i
  simp

/-- The internal permutations in the two blocks supply exactly p!q!. -/
theorem tensorForm_alternatization (p q : ℕ) (B : Form K V p) (C : Form K V q) :
    (tensorForm B C).alternatization.domDomCongr finSumFinEquiv =
      ((p.factorial * q.factorial : ℕ) : K) • shuffleProduct K V B C := by
  rw [tensorForm, LinearMap.compMultilinearMap_alternatization,
    MultilinearMap.domCoprod_alternatization_eq,
    LinearMap.compAlternatingMap_smul, AlternatingMap.domDomCongr_smul]
  simp only [Fintype.card_fin]
  rw [Nat.cast_smul_eq_nsmul K]
  rfl

theorem product_normalization :
    Specs.D05.M15.ExteriorPairing.AlternatingForms.product_normalization := by
  intro K V _ _ _ _ p q B C
  simp only [averageForm, Fintype.card_sum, Fintype.card_fin,
    AlternatingMap.domDomCongr_smul, tensorForm_alternatization, smul_smul]
  have hp : (p.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr p.factorial_ne_zero
  have hq : (q.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr q.factorial_ne_zero
  have hn : ((p+q).factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (p+q).factorial_ne_zero
  rw [Nat.cast_mul]
  have hc : (((p+q).factorial : K) / ((p.factorial : K) * (q.factorial : K))) *
      ((p+q).factorial : K)⁻¹ * ((p.factorial : K) * (q.factorial : K)) = 1 := by
    field_simp
  rw [← mul_assoc, hc, one_smul]

/-- The scalar tensor form on two blocks is the product form on their concatenation. -/
theorem covectorTensorForm_append (p q : ℕ) (f : Fin p → Module.Dual K V)
    (g : Fin q → Module.Dual K V) :
    ((LinearMap.mul' K K).compMultilinearMap
      ((covectorTensorForm p f).domCoprod (covectorTensorForm q g))).domDomCongr
        finSumFinEquiv = covectorTensorForm (p+q) (Fin.append f g) := by
  ext x
  simp only [MultilinearMap.domDomCongr_apply, LinearMap.compMultilinearMap_apply,
    MultilinearMap.domCoprod_apply, LinearMap.mul'_apply, covectorTensorForm,
    MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]
  rw [Fin.prod_univ_add]
  simp

/-- Multiplication compatibility for decomposable covectors uses the unique
factorization into a block permutation and a shuffle, without dividing by p!q!. -/
theorem multiplication_elementary (p q : ℕ) (f : Fin p → Module.Dual K V)
    (g : Fin q → Module.Dual K V) :
    toForm K V (p+q) (wedge (exteriorPower.ιMulti K p f) (exteriorPower.ιMulti K q g)) =
      shuffleProduct K V (toForm K V p (exteriorPower.ιMulti K p f))
        (toForm K V q (exteriorPower.ιMulti K q g)) := by
  have hw : wedge (exteriorPower.ιMulti K p f) (exteriorPower.ιMulti K q g) =
      exteriorPower.ιMulti K (p+q) (Fin.append f g) := by
    apply Subtype.ext
    exact _root_.ExteriorAlgebra.ιMulti_mul_ιMulti f g
  rw [hw, elementary_alternatization, elementary_alternatization,
    elementary_alternatization]
  change _ = ((LinearMap.mul' K K).compAlternatingMap
    ((covectorTensorForm p f).alternatization.domCoprod
      (covectorTensorForm q g).alternatization)).domDomCongr finSumFinEquiv
  rw [← MultilinearMap.domCoprod_alternatization,
    ← LinearMap.compMultilinearMap_alternatization,
    ← alternatization_domDomCongr, covectorTensorForm_append]

abbrev shuffleBilinear := @Specs.D05.M15.ExteriorPairing.AlternatingForms.shuffleBilinear

/-- Bilinear structure of multiplication in the existing homogeneous submodules. -/
def wedgeBilinear (p q : ℕ) : (⋀[K]^p (Module.Dual K V)) →ₗ[K]
    (⋀[K]^q (Module.Dual K V)) →ₗ[K] (⋀[K]^(p+q) (Module.Dual K V)) :=
  LinearMap.mk₂ K wedge
    (by intros; apply Subtype.ext; exact add_mul _ _ _)
    (by intros; apply Subtype.ext; exact smul_mul_assoc _ _ _)
    (by intros; apply Subtype.ext; exact mul_add _ _ _)
    (by intros; apply Subtype.ext; exact mul_smul_comm _ _ _)

theorem multiplication : Specs.D05.M15.ExteriorPairing.AlternatingForms.multiplication := by
  intro K V _ _ _ _ p q a b
  let L := (wedgeBilinear (K := K) (V := V) p q).compr₂ (toForm K V (p+q))
  let R := ((shuffleBilinear (K := K) (V := V) p q).compl₂ (toForm K V q)).comp
    (toForm K V p)
  have h : L = R := by
    refine exteriorPower.linearMap_ext (R := K) (n := p) (M := Module.Dual K V)
      (N := (⋀[K]^q (Module.Dual K V)) →ₗ[K] Form K V (p+q)) (f := L) (g := R) ?_
    apply AlternatingMap.ext
    intro f
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro g
    exact multiplication_elementary p q f g
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

/-- The existing exterior contraction restricted to its actual homogeneous target. -/
def contraction (p : ℕ) (v : V) : (⋀[K]^(p+1) (Module.Dual K V)) →ₗ[K]
    (⋀[K]^p (Module.Dual K V)) :=
  ((Specs.D05.M15.InteriorProduct.interior (Module.Dual.eval K V v)).comp
    (Submodule.subtype (⋀[K]^(p+1) (Module.Dual K V)))).codRestrict _ (fun a =>
      D05.M15.InteriorProduct.exterior_degree (Module.Dual.eval K V v) p a a.property)

/-- First-column Laplace expansion, with zero-based deletion signs. -/
theorem contraction_elementary (p : ℕ) (v : V) (f : Fin (p+1) → Module.Dual K V) :
    contraction p v (exteriorPower.ιMulti K (p+1) f) =
      ∑ j : Fin (p+1), ((-1 : K)^(j : ℕ) * f j v) •
        exteriorPower.ιMulti K p (fun i => f (j.succAbove i)) := by
  apply Subtype.ext
  change Specs.D05.M15.InteriorProduct.interior (Module.Dual.eval K V v)
    (_root_.ExteriorAlgebra.ιMulti K (p+1) f) = _
  simpa only [Submodule.coe_sum, Submodule.coe_smul_of_tower,
    exteriorPower.ιMulti_apply_coe, Module.Dual.eval_apply] using
      D05.M15.InteriorProduct.exterior_delete (Module.Dual.eval K V v) p f

theorem insertion : Specs.D05.M15.ExteriorPairing.AlternatingForms.insertion := by
  intro K V _ _ _ _ p a v
  refine ⟨contraction p v a, rfl, ?_⟩
  let L := (toForm K V p).comp (contraction p v)
  let R := ((AlternatingMap.curryLeftLinearMap (R := K) (M := V) (N := K) (n := p)).flip v).comp
    (toForm K V (p+1))
  have h : L = R := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro f
    apply AlternatingMap.ext
    intro x
    change toForm K V p (contraction p v (exteriorPower.ιMulti K (p+1) f)) x =
      (toForm K V (p+1) (exteriorPower.ιMulti K (p+1) f)).curryLeft v x
    rw [contraction_elementary]
    simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply,
      AlternatingMap.curryLeft_apply_apply, smul_eq_mul]
    simp_rw [show ∀ n (f : Fin n → Module.Dual K V) x,
      toForm K V n (exteriorPower.ιMulti K n f) x = Matrix.det (fun i j => f i (x j))
        from fun n f x => elementary n f x]
    change (∑ j : Fin (p+1), ((-1 : K)^(j : ℕ) * f j v) *
      Matrix.det (Matrix.of (fun i k => f (j.succAbove i) (x k)))) =
      Matrix.det (Matrix.of (fun i k => f i (Matrix.vecCons v x k)))
    rw [Matrix.det_succ_column_zero]
    apply Finset.sum_congr rfl
    intro j _
    simp [Matrix.submatrix, Matrix.vecCons]
  exact LinearMap.congr_fun h a

theorem insertion_degree_zero :
    Specs.D05.M15.ExteriorPairing.AlternatingForms.insertion_degree_zero := by
  intro K V _ _ _ c v
  simp only [exteriorPower.zeroEquiv_symm_apply, Submodule.coe_smul_of_tower,
    exteriorPower.ιMulti_apply_coe, _root_.ExteriorAlgebra.ιMulti_zero_apply,
    map_smul]
  have h : Specs.D05.M15.InteriorProduct.interior (Module.Dual.eval K V v)
      (1 : _root_.ExteriorAlgebra K (Module.Dual K V)) = 0 :=
    D05.M15.InteriorProduct.exterior_one (Module.Dual.eval K V v)
  rw [h, smul_zero]

theorem toForm_wedge [FiniteDimensional K V] {p q : ℕ}
    (a : ⋀[K]^p (Module.Dual K V)) (b : ⋀[K]^q (Module.Dual K V)) :
    toForm K V (p+q) (wedge a b) = shuffleProduct K V (toForm K V p a) (toForm K V q b) :=
  multiplication p q a b

/-- Equality of homogeneous degrees changes only the tuple index. -/
theorem toForm_cast {p q : ℕ} (h : p = q) (a : ⋀[K]^p (Module.Dual K V)) :
    (toForm K V p a).domDomCongr (finCongr h) =
      toForm K V q ⟨a.val, h ▸ a.property⟩ := by
  subst q
  rfl

theorem associativity : Specs.D05.M15.ExteriorPairing.AlternatingForms.associativity := by
  intro K V _ _ _ _ p q r B C D
  obtain ⟨ep, hp⟩ := identification (K := K) (V := V) p
  obtain ⟨eq, hq⟩ := identification (K := K) (V := V) q
  obtain ⟨er, hr⟩ := identification (K := K) (V := V) r
  obtain ⟨a, rfl⟩ := ep.surjective B
  obtain ⟨b, rfl⟩ := eq.surjective C
  obtain ⟨c, rfl⟩ := er.surjective D
  change (shuffleProduct K V (shuffleProduct K V (ep.toLinearMap a) (eq.toLinearMap b))
    (er.toLinearMap c)).domDomCongr _ =
    shuffleProduct K V (ep.toLinearMap a)
      (shuffleProduct K V (eq.toLinearMap b) (er.toLinearMap c))
  rw [hp, hq, hr, ← toForm_wedge, ← toForm_wedge, ← toForm_wedge, ← toForm_wedge,
    toForm_cast]
  congr 1
  apply Subtype.ext
  exact mul_assoc _ _ _

theorem graded_commutativity :
    Specs.D05.M15.ExteriorPairing.AlternatingForms.graded_commutativity := by
  intro K V _ _ _ _ p q B C
  obtain ⟨ep, hp⟩ := identification (K := K) (V := V) p
  obtain ⟨eq, hq⟩ := identification (K := K) (V := V) q
  obtain ⟨a, rfl⟩ := ep.surjective B
  obtain ⟨b, rfl⟩ := eq.surjective C
  change shuffleProduct K V (ep.toLinearMap a) (eq.toLinearMap b) =
    (-1 : K)^(p*q) • (shuffleProduct K V (eq.toLinearMap b) (ep.toLinearMap a)).domDomCongr _
  rw [hp, hq, ← toForm_wedge, ← toForm_wedge, toForm_cast, ← map_smul]
  congr 1
  apply Subtype.ext
  exact D05.M15.WedgeSign.graded_comm (K := K) (V := Module.Dual K V)
    p q a b a.property b.property

/-- Send an increasing shuffle to its coset modulo permutations within blocks. -/
def shuffleCoset (p q : ℕ)
    (σ : {σ : Equiv.Perm (Fin (p+q)) // IsShuffle p q σ}) :
    Equiv.Perm.ModSumCongr (Fin p) (Fin q) :=
  Quotient.mk'' (finSumFinEquiv.symm.permCongr σ.val)

/-- Two increasing representatives of the same block coset coincide. -/
theorem shuffleCoset_injective (p q : ℕ) : Function.Injective (shuffleCoset p q) := by
  classical
  intro σ τ h
  have hh := QuotientGroup.leftRel_apply.mp (Quotient.exact' h)
  obtain ⟨⟨sl, sr⟩, hh⟩ := hh
  have he : finSumFinEquiv.symm.permCongr τ.val =
      finSumFinEquiv.symm.permCongr σ.val * Equiv.Perm.sumCongrHom _ _ (sl, sr) :=
    inv_mul_eq_iff_eq_mul.mp hh.symm
  have hl (i : Fin p) : τ.val (Fin.castAdd q i) = σ.val (Fin.castAdd q (sl i)) := by
    have hi := congrArg (fun t : Equiv.Perm (Fin p ⊕ Fin q) =>
      finSumFinEquiv (t (Sum.inl i))) he
    simpa using hi
  have hr (j : Fin q) : τ.val (Fin.natAdd p j) = σ.val (Fin.natAdd p (sr j)) := by
    have hj := congrArg (fun t : Equiv.Perm (Fin p ⊕ Fin q) =>
      finSumFinEquiv (t (Sum.inr j))) he
    simpa using hj
  have hL : (fun i : Fin p => τ.val (Fin.castAdd q i)) =
      (fun i : Fin p => σ.val (Fin.castAdd q i)) := by
    apply StrictMono.eq_of_range_eq τ.property.1 σ.property.1
    have hf : (fun i : Fin p => τ.val (Fin.castAdd q i)) =
        (fun i : Fin p => σ.val (Fin.castAdd q i)) ∘ sl := funext hl
    rw [hf, Set.range_comp, sl.surjective.range_eq, Set.image_univ]
  have hR : (fun i : Fin q => τ.val (Fin.natAdd p i)) =
      (fun i : Fin q => σ.val (Fin.natAdd p i)) := by
    apply StrictMono.eq_of_range_eq τ.property.2 σ.property.2
    have hf : (fun i : Fin q => τ.val (Fin.natAdd p i)) =
        (fun i : Fin q => σ.val (Fin.natAdd p i)) ∘ sr := funext hr
    rw [hf, Set.range_comp, sr.surjective.range_eq, Set.image_univ]
  apply Subtype.ext
  apply Equiv.ext
  intro i
  obtain ⟨i | j, rfl⟩ := (finSumFinEquiv : Fin p ⊕ Fin q ≃ Fin (p+q)).surjective i
  · exact (congrFun hL i).symm
  · exact (congrFun hR j).symm


/-- Reorder a finite injective family into increasing order. The permutation
only changes the order of that family, including when its index type is empty. -/
theorem sortDomain {p n : ℕ} (f : Fin p → Fin n) (hf : Function.Injective f) :
    ∃ a : Equiv.Perm (Fin p), StrictMono (fun i => f (a i)) := by
  classical
  let e := Equiv.ofInjective f hf
  have hc : Fintype.card (Set.range f) = p :=
    (Fintype.card_congr e).symm.trans (Fintype.card_fin p)
  let o := monoEquivOfFin (Set.range f) hc
  let a := o.toEquiv.trans e.symm
  refine ⟨a, ?_⟩
  have h (i : Fin p) : f (a i) = (o i).val := by
    exact congrArg Subtype.val (e.apply_symm_apply (o i))
  simp_rw [h]
  exact (OrderEmbedding.subtype _).strictMono.comp o.strictMono

/-- Every block-permutation coset has an increasing shuffle representative. -/
theorem shuffleCoset_surjective (p q : ℕ) : Function.Surjective (shuffleCoset p q) := by
  classical
  intro z
  induction z using Quotient.inductionOn' with
  | h σ =>
    let ρ := (finSumFinEquiv : Fin p ⊕ Fin q ≃ Fin (p+q)).permCongr σ
    obtain ⟨a, ha⟩ := sortDomain (fun i : Fin p => ρ (Fin.castAdd q i))
      (ρ.injective.comp (Fin.castAdd_injective p q))
    obtain ⟨b, hb⟩ := sortDomain (fun j : Fin q => ρ (Fin.natAdd p j))
      (ρ.injective.comp (Fin.natAdd_injective q p))
    let τ := (finSumFinEquiv : Fin p ⊕ Fin q ≃ Fin (p+q)).symm.trans
      ((Equiv.Perm.sumCongr a b).trans (σ.trans finSumFinEquiv))
    have ht : IsShuffle p q τ := by
      constructor
      · simpa only [τ, Equiv.trans_apply, finSumFinEquiv_symm_apply_castAdd,
          Equiv.Perm.sumCongr_apply, Sum.map_inl, ρ, Equiv.permCongr_apply,
          finSumFinEquiv_apply_left] using ha
      · simpa only [τ, Equiv.trans_apply, finSumFinEquiv_symm_apply_natAdd,
          Equiv.Perm.sumCongr_apply, Sum.map_inr, ρ, Equiv.permCongr_apply,
          finSumFinEquiv_apply_right] using hb
    refine ⟨⟨τ, ht⟩, ?_⟩
    apply Quotient.sound'
    apply QuotientGroup.leftRel_apply.mpr
    have hc : finSumFinEquiv.symm.permCongr τ = σ * Equiv.Perm.sumCongr a b := by
      ext i
      simp [τ, Equiv.permCongr_apply]
    rw [hc, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
    exact Subgroup.inv_mem _ ⟨(a,b), rfl⟩

/-- Evaluation of a coset summand on its increasing representative. -/
theorem shuffleCoset_summand (p q : ℕ) (B : Form K V p) (C : Form K V q)
    (x : Fin (p+q) → V)
    (σ : {σ : Equiv.Perm (Fin (p+q)) // IsShuffle p q σ}) :
    (LinearMap.mul' K K)
      (AlternatingMap.domCoprod.summand B C (shuffleCoset p q σ)
        (x ∘ finSumFinEquiv)) =
      Equiv.Perm.sign σ.val •
        (B (fun i => x (σ.val (Fin.castAdd q i))) *
         C (fun j => x (σ.val (Fin.natAdd p j)))) := by
  classical
  simp [shuffleCoset, AlternatingMap.domCoprod.summand_mk'',
    MultilinearMap.domDomCongr_apply, MultilinearMap.domCoprod_apply,
    Equiv.permCongr_apply, Function.comp_def]

theorem shuffle_formula : Specs.D05.M15.ExteriorPairing.AlternatingForms.shuffle_formula := by
  intro K V _ _ _ p q B C x
  classical
  change (LinearMap.mul' K K) ((B.domCoprod C) (x ∘ finSumFinEquiv)) = _
  simp only [AlternatingMap.domCoprod_apply, _root_.sum_apply, map_sum]
  symm
  let e := Equiv.ofBijective (shuffleCoset p q)
    ⟨shuffleCoset_injective p q, shuffleCoset_surjective p q⟩
  apply Fintype.sum_equiv e
  intro σ
  exact (shuffleCoset_summand p q B C x σ).symm

open scoped DirectSum

theorem formsMul_lof (p q : ℕ) (B : Form K V p) (C : Form K V q) :
    formsMul (DirectSum.lof K ℕ (Form K V) p B) (DirectSum.lof K ℕ (Form K V) q C) =
      DirectSum.lof K ℕ (Form K V) (p+q) (shuffleProduct K V B C) := by
  simp [formsMul, LinearMap.flip_apply,
    Specs.D05.M15.ExteriorPairing.AlternatingForms.shuffleBilinear]

theorem graded_algebra_equivalence :
    Specs.D05.M15.ExteriorPairing.AlternatingForms.graded_algebra_equivalence := by
  intro K V _ _ _ _
  classical
  choose es hs using (fun p => identification (K := K) (V := V) p)
  let G := fun p : ℕ => ⋀[K]^p (Module.Dual K V)
  let e := (DirectSum.decomposeLinearEquiv G).trans (DirectSum.congrLinearEquiv es)
  have he (p : ℕ) (a : G p) :
      e a = DirectSum.lof K ℕ (Form K V) p (toForm K V p a) := by
    change (DirectSum.congrLinearEquiv es) (DirectSum.decomposeLinearEquiv G a) = _
    rw [DirectSum.decomposeLinearEquiv_apply_coe, DirectSum.coe_congrLinearEquiv,
      DirectSum.lmap_lof]
    exact congrArg (DirectSum.lof K ℕ (Form K V) p) (LinearMap.congr_fun (hs p) a)
  refine ⟨e, he, ?_, ?_⟩
  · intro a b
    induction a using DirectSum.Decomposition.inductionOn G with
    | zero => simp
    | add a a' ha ha' => simp only [add_mul, map_add, ha, ha', LinearMap.add_apply]
    | homogeneous a =>
      induction b using DirectSum.Decomposition.inductionOn G with
      | zero => simp
      | add b b' hb hb' => simp only [mul_add, map_add, hb, hb']
      | homogeneous b =>
        rw [he, he, formsMul_lof]
        exact (he _ (wedge a b)).trans (congrArg (DirectSum.lof K ℕ (Form K V) _)
          (toForm_wedge a b))
  · let a : G 0 := (exteriorPower.zeroEquiv K (Module.Dual K V)).symm 1
    have ha : (a : _root_.ExteriorAlgebra K (Module.Dual K V)) = 1 := by
      simp [a, exteriorPower.zeroEquiv_symm_apply,
        exteriorPower.ιMulti_apply_coe, _root_.ExteriorAlgebra.ιMulti_zero_apply]
    rw [← ha, he]
    congr 1
    apply AlternatingMap.ext
    intro x
    exact degree_zero 1 x

end D05.M15.ExteriorPairing.AlternatingForms
