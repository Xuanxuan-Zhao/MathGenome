import MathGenome.Internal.Specs.D05.M15.InteriorProduct.DegreeDetection
import MathGenome.Internal.D05.M15.InteriorProduct.Higher
import MathGenome.Internal.D05.M15.ExteriorDerivation
import MathGenome.Internal.D05.M15.ExteriorBasis

noncomputable section
namespace D05.M15.InteriorProduct.DegreeDetection
open Specs.D05.M15.InteriorProduct (word)
open D05.M15.InteriorProduct
universe u v w
variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

/-- The finite-basis sum, regarded as a linear endomorphism. -/
def contractionSum {I : Type w} [Fintype I] (b : Module.Basis I K V)
    (A : V →ₗ[K] V) : Module.End K (_root_.ExteriorAlgebra K V) :=
  ∑ j, (LinearMap.mulLeft K (_root_.ExteriorAlgebra.ι K (A (b j)))).comp
    (interior (b.coord j))

@[simp] theorem contractionSum_apply {I : Type w} [Fintype I]
    (b : Module.Basis I K V) (A : V →ₗ[K] V) (a : _root_.ExteriorAlgebra K V) :
    contractionSum b A a =
      ∑ j, _root_.ExteriorAlgebra.ι K (A (b j)) * interior (b.coord j) a := by
  simp [contractionSum]

/-- The Cartan relation and reconstruction in the given basis give the
same generator recursion as the induced derivation. -/
theorem contractionSum_cons {I : Type w} [Fintype I]
    (b : Module.Basis I K V) (A : V →ₗ[K] V) (v : V)
    (a : _root_.ExteriorAlgebra K V) :
    contractionSum b A (_root_.ExteriorAlgebra.ι K v * a) =
      _root_.ExteriorAlgebra.ι K (A v) * a +
        _root_.ExteriorAlgebra.ι K v * contractionSum b A a := by
  classical
  simp only [contractionSum_apply, exterior_cons, mul_sub, Finset.sum_sub_distrib,
    mul_smul_comm, ← smul_mul_assoc, ← Finset.sum_mul]
  have hexp : (∑ j, b.coord j v • _root_.ExteriorAlgebra.ι K (A (b j))) =
      _root_.ExteriorAlgebra.ι K (A v) := by
    simp only [← map_smul]
    rw [← map_sum]
    rw [← map_sum]
    rw [show (∑ j, b.coord j v • b j) = v from b.sum_repr v]
  rw [hexp]
  have hswap (j : I) :
      _root_.ExteriorAlgebra.ι K (A (b j)) *
        (_root_.ExteriorAlgebra.ι K v * interior (b.coord j) a) =
      -(_root_.ExteriorAlgebra.ι K v *
        (_root_.ExteriorAlgebra.ι K (A (b j)) * interior (b.coord j) a)) := by
    rw [← mul_assoc, (eq_neg_of_add_eq_zero_left (_root_.ExteriorAlgebra.ι_add_mul_swap (A (b j)) v)), neg_mul, mul_assoc]
  simp only [hswap, Finset.sum_neg_distrib, sub_neg_eq_add, Finset.mul_sum]

theorem derivation_formula : Specs.D05.M15.InteriorProduct.DegreeDetection.derivation_formula := by
  intro K V _ _ _ n b A a
  have heq (t : _root_.TensorAlgebra K V) :
      ExteriorDerivation.induced A (_root_.TensorAlgebra.toExterior t) =
        contractionSum b A (_root_.TensorAlgebra.toExterior t) := by
    induction t using tensor_left_induction with
    | hs r => simp [ExteriorDerivation.induced_scalar]
    | ha x y hx hy => simp only [map_add, hx, hy]
    | hc r x hx => simp only [map_smul, hx]
    | hv v x hx =>
      rw [map_mul, _root_.TensorAlgebra.toExterior_ι,
        ExteriorDerivation.induced_mul, ExteriorDerivation.induced_generator,
        contractionSum_cons, hx]
  obtain ⟨t, rfl⟩ := D05.M15.Exterior.quotient_surjective a
  simpa only [contractionSum_apply] using heq t

/-- The derivation of the identity is multiplication by the homogeneous degree. -/
theorem induced_id_degree (p : ℕ) (a : _root_.ExteriorAlgebra K V)
    (ha : a ∈ ⋀[K]^p V) :
    ExteriorDerivation.induced (LinearMap.id : V →ₗ[K] V) a = (p : K) • a := by
  induction ha using Submodule.pow_induction_on_left' with
  | algebraMap r => simp [ExteriorDerivation.induced_scalar]
  | add x y n hx hy ix iy => simp only [map_add, ix, iy, smul_add]
  | mem_mul m hm n x hx ih =>
    obtain ⟨v, rfl⟩ := hm
    rw [ExteriorDerivation.induced_mul, ExteriorDerivation.induced_generator, ih]
    simp [Nat.cast_add, add_smul, add_comm]

theorem wedge_contraction : Specs.D05.M15.InteriorProduct.DegreeDetection.wedge_contraction := by
  intro K V _ _ _ n b p a
  exact (derivation_formula n b LinearMap.id a).symm.trans
    (induced_id_degree (K := K) (V := V) p (a : _root_.ExteriorAlgebra K V) a.property)

theorem contraction_wedge : Specs.D05.M15.InteriorProduct.DegreeDetection.contraction_wedge := by
  intro K V _ _ _ n b p a
  classical
  have h := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun j _ => cartan_identity (b.coord j) (b j) (a : _root_.ExteriorAlgebra K V))
  simp only [Finset.sum_add_distrib, wedge_contraction n b p a] at h
  have hc (j : Fin n) : b.coord j (b j) = 1 := by simp
  simp only [hc, one_smul, Finset.sum_const, Finset.card_univ, Fintype.card_fin] at h
  rw [← Nat.cast_smul_eq_nsmul K] at h
  rw [sub_smul]
  exact eq_sub_of_add_eq h


/-- A word belongs to the homogeneous component given by its length. -/
theorem word_mem_degree (l : List V) :
    word (_root_.ExteriorAlgebra.ι K) l ∈ ⋀[K]^l.length V := by
  induction l with
  | nil =>
    change (1 : _root_.ExteriorAlgebra K V) ∈
      (LinearMap.range (_root_.ExteriorAlgebra.ι K)) ^ 0
    simp
  | cons v l ih =>
    change _root_.ExteriorAlgebra.ι K v * word (_root_.ExteriorAlgebra.ι K) l ∈
      (LinearMap.range (_root_.ExteriorAlgebra.ι K)) ^ (l.length + 1)
    rw [pow_succ']
    exact Submodule.mul_mem_mul (Set.mem_range_self v) ih

/-- Once every contraction of length k vanishes, every longer word of
contractions vanishes too. The prefix is contracted first. -/
theorem longer_contraction_zero (k : ℕ) (a : _root_.ExteriorAlgebra K V)
    (h : ∀ α : ⋀[K]^k (Module.Dual K V), higherInterior (K := K) (V := V) α a = 0)
    (l : List (Module.Dual K V)) (hl : k ≤ l.length) :
    higherInterior (word (_root_.ExteriorAlgebra.ι K) l) a = 0 := by
  have hm : word (_root_.ExteriorAlgebra.ι K) (l.take k) ∈
      ⋀[K]^k (Module.Dual K V) := by
    simpa only [List.length_take, Nat.min_eq_left hl] using word_mem_degree (K := K) (l.take k)
  have hz := h ⟨_, hm⟩
  have heq : word (_root_.ExteriorAlgebra.ι K) l =
      word (_root_.ExteriorAlgebra.ι K) (l.take k) *
        word (_root_.ExteriorAlgebra.ι K) (l.drop k) := by
    calc
      _ = word (_root_.ExteriorAlgebra.ι K) (l.take k ++ l.drop k) :=
        congrArg _ (List.take_append_drop k l).symm
      _ = _ := by simp only [word, List.map_append, List.prod_append]
  rw [heq, higher_product, LinearMap.comp_apply, hz, map_zero]

/-- Full contractions include every coordinate functional in the increasing
wedge basis. This separation statement does not require finite dimension. -/
theorem zero_of_full_contractions (p : ℕ) (a : ⋀[K]^p V)
    (h : ∀ f : Fin p → Module.Dual K V,
      higherInterior (_root_.ExteriorAlgebra.ιMulti K p f)
        (a : _root_.ExteriorAlgebra K V) = 0) : a = 0 := by
  classical
  let I := Module.Free.ChooseBasisIndex K V
  let : LinearOrder I := linearOrderOfSTO WellOrderingRel
  let b := Module.Free.chooseBasis K V
  apply (b.exteriorPower p).repr.injective
  ext s
  rw [map_zero, Finsupp.zero_apply, exteriorPower.basis_repr_apply]
  change exteriorPower.pairingDual K V p (exteriorPower.ιMulti_family K p b.coord s) a = 0
  rw [← scalar_contraction_pairing]
  change scalarPart (higherInterior (_root_.ExteriorAlgebra.ιMulti K p
    (b.coord ∘ s.val.orderEmbOfFin s.prop)) (a : _root_.ExteriorAlgebra K V)) = 0
  rw [h, map_zero]

theorem higher_detection : Specs.D05.M15.InteriorProduct.DegreeDetection.higher_detection := by
  intro K V _ _ _ p k _hk hkp a h
  apply zero_of_full_contractions p a
  intro f
  have hz := longer_contraction_zero k (a : _root_.ExteriorAlgebra K V) h (List.ofFn f)
    (by simpa using hkp)
  simpa only [word, List.map_ofFn, Function.comp_def,
    _root_.ExteriorAlgebra.ιMulti_apply] using hz

theorem iterated_detection : Specs.D05.M15.InteriorProduct.DegreeDetection.iterated_detection := by
  intro K V _ _ _ p k hk hkp a h
  apply higher_detection p k hk hkp a
  rintro ⟨α, hα⟩
  change higherInterior α (a : _root_.ExteriorAlgebra K V) = 0
  rw [← _root_.ExteriorAlgebra.ιMulti_span_fixedDegree K k] at hα
  induction hα using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, rfl⟩ := hx
    have hf := higher_word (List.ofFn f) (a : _root_.ExteriorAlgebra K V)
    simpa only [word, List.map_ofFn, Function.comp_def,
      _root_.ExteriorAlgebra.ιMulti_apply, h] using hf
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add x y _ _ hx hy => simp only [map_add, LinearMap.add_apply, hx, hy, add_zero]
  | smul c x _ hx => simp only [map_smul, LinearMap.smul_apply, hx, smul_zero]

end D05.M15.InteriorProduct.DegreeDetection

