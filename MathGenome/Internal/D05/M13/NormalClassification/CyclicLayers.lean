import MathGenome.Internal.Specs.D05.M13.NormalClassification.CyclicLayers
import MathGenome.Internal.D05.M10.Cyclic
import MathGenome.Internal.D05.Foundations.Crt
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module

noncomputable section
namespace D05.M13.NormalClassification.CyclicLayers
open Polynomial
local instance {α : Type*} : DecidableEq α := Classical.decEq α
open Specs.D05.M13.NormalClassification.CyclicLayers
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma cyclic_le (T : Module.End K V) (H : Submodule K V)
    (hH : ∀ x ∈ H, T x ∈ H) {v : V} (hv : v ∈ H) :
    M10.Cyclic.cyclicSpace K V T v ≤ H := by
  apply Submodule.span_le.mpr
  rintro _ ⟨n, rfl⟩
  induction n with
  | zero => simpa using hv
  | succ n ih => simpa [pow_succ', Module.End.mul_apply] using hH _ ih

lemma cyclic_mono (T : Module.End K V) {v w : V}
    (hw : w ∈ M10.Cyclic.cyclicSpace K V T v) :
    M10.Cyclic.cyclicSpace K V T w ≤ M10.Cyclic.cyclicSpace K V T v :=
  cyclic_le T _ (fun x hx => M10.Cyclic.invariant T v x hx) hw

lemma polynomial_mem (T : Module.End K V) (H : Submodule K V)
    (hH : ∀ x ∈ H, T x ∈ H) {v : V} (hv : v ∈ H) (p : K[X]) :
    aeval T p v ∈ H :=
  cyclic_le T H hH hv (M10.Cyclic.eval_mem_cyclic T v p)

theorem block_cyclic : Specs.D05.M13.NormalClassification.CyclicLayers.block_cyclic := by
  intro K V _ _ _ _ T H p h v hv hv0
  have hd := M10.Cyclic.monic_generator T v
  have hdp : M10.Cyclic.vectorAnnihilator K V T v ∣ p :=
    (M10.Cyclic.divides_iff_annihilates T v p).mpr (h.kills v hv)
  have hdu : ¬ IsUnit (M10.Cyclic.vectorAnnihilator K V T v) := by
    intro hu
    have hd1 := hd.1.eq_one_of_isUnit hu
    have hz := (M10.Cyclic.divides_iff_annihilates T v 1).mp (by rw [hd1])
    exact hv0 (by simpa [Specs.D05.M08.Evaluation.evaluation_value] using hz)
  have he : M10.Cyclic.vectorAnnihilator K V T v = p :=
    Polynomial.eq_of_monic_of_associated hd.1 h.monic
      (not_not.mp ((h.irreducible.isUnit_iff_not_associated_of_dvd hdp).not.mp hdu)).symm
  refine ⟨?_, he⟩
  apply Submodule.eq_of_le_of_finrank_eq (cyclic_le T H h.invariant hv)
  rw [M10.Cyclic.dimension T v]
  exact (congrArg Polynomial.natDegree he).trans h.dimension.symm

lemma coprime_labels {ι : Type*} (p : ι → K[X])
    (hm : ∀ i, (p i).Monic) (hi : ∀ i, Irreducible (p i))
    (hp : Function.Injective p) : Pairwise fun i j => IsCoprime (p i) (p j) := by
  intro i j hij
  apply (hi i).isCoprime_or_dvd (p j) |>.resolve_right
  intro hd
  have ha := ((hi j).isUnit_iff_not_associated_of_dvd hd).not.mp (hi i).not_isUnit
  exact hij (hp (Polynomial.eq_of_monic_of_associated (hm i) (hm j) (not_not.mp ha).symm))

lemma eval_eq_of_dvd_sub (T : Module.End K V) {p f g : K[X]} {v : V}
    (h : aeval T p v = 0) (hd : p ∣ f - g) : aeval T f v = aeval T g v := by
  obtain ⟨r, hr⟩ := hd
  apply sub_eq_zero.mp
  calc
    aeval T f v - aeval T g v = aeval T (f - g) v := by simp
    _ = aeval T (r * p) v := by rw [hr, mul_comm p r]
    _ = 0 := by simp [map_mul, Module.End.mul_apply, h]

theorem crt_selectors : Specs.D05.M13.NormalClassification.CyclicLayers.crt_selectors := by
  intro K V ι _ _ _ _ T H p hm hp hkill
  classical
  obtain ⟨u, _, hu⟩ := Foundations.Crt.bezoutResidues K ι p hm hp
  refine ⟨fun i => u i * Foundations.crtCofactor p i, ?_⟩
  intro i k x hx
  have hr := (hu i).2 k
  by_cases hki : k = i
  · subst k
    simp only [ite_true] at hr ⊢
    have hd : p i ∣ (u i * Foundations.crtCofactor p i) - 1 := by
      apply Ideal.mem_span_singleton.mp
      apply Ideal.Quotient.eq.mp
      simpa only [map_one] using hr
    simpa using eval_eq_of_dvd_sub T (hkill i x hx) hd
  · simp only [ite_eq_right hki] at hr ⊢
    have hd : p k ∣ (u i * Foundations.crtCofactor p i) - 0 := by
      simpa using (Foundations.Crt.residue_zero_iff _ _).mp hr
    simpa using eval_eq_of_dvd_sub T (hkill k x hx) hd


lemma selector_sum {ι : Type*} [Fintype ι] (T : Module.End K V)
    (H : ι → Submodule K V) (e : ι → K[X])
    (he : ∀ i k x, x ∈ H k → aeval T (e i) x = if k = i then x else 0)
    (x : ι → V) (hx : ∀ k, x k ∈ H k) (i : ι) :
    aeval T (e i) (∑ k, x k) = x i := by
  classical
  rw [map_sum, Finset.sum_eq_single i]
  · simpa using he i i (x i) (hx i)
  · intro k _ hki
    simpa [hki] using he i k (x k) (hx k)
  · simp

theorem single_layer : Specs.D05.M13.NormalClassification.CyclicLayers.single_layer := by
  intro K V ι _ _ _ _ _ T H p v h hp hv
  classical
  have hcop := coprime_labels p (fun i => (h i).monic) (fun i => (h i).irreducible) hp
  obtain ⟨e, he⟩ := crt_selectors T H p (fun i => (h i).monic) hcop
    (fun i x hx => (h i).kills x hx)
  have hextract := selector_sum T H e he
  have hcyclic (i : ι) := block_cyclic T (H i) (p i) (h i) (v i) (hv i).1 (hv i).2
  have hspan : M10.Cyclic.cyclicSpace K V T (∑ i, v i) = ⨆ i, H i := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨n, rfl⟩
      change (T ^ n) (∑ i, v i) ∈ _
      rw [map_sum]
      apply Submodule.sum_mem_iSup
      intro i
      exact cyclic_le T (H i) (h i).invariant (hv i).1
        (Submodule.subset_span ⟨n, rfl⟩)
    · apply iSup_le
      intro i
      rw [← (hcyclic i).1]
      apply cyclic_mono T
      rw [← hextract v (fun k => (hv k).1) i]
      exact M10.Cyclic.eval_mem_cyclic T (∑ i, v i) (e i)
  have hann (q : K[X]) : aeval T q (∑ i, v i) = 0 ↔ (∏ i, p i) ∣ q := by
    change _ ↔ Foundations.crtProduct p ∣ q
    rw [Foundations.Crt.product_dvd_iff p hcop]
    constructor
    · intro hq i
      rw [← (hcyclic i).2]
      apply (M10.Cyclic.divides_iff_annihilates T (v i) q).mpr
      change aeval T q (v i) = 0
      have hz : (∑ k, aeval T q (v k)) = 0 := by simpa using hq
      have hi := hextract (fun k => aeval T q (v k))
        (fun k => polynomial_mem T (H k) (h k).invariant (hv k).1 q) i
      rw [hz, map_zero] at hi
      exact hi.symm
    · intro hq
      rw [map_sum]
      apply Finset.sum_eq_zero
      intro i _
      apply (M10.Cyclic.divides_iff_annihilates T (v i) q).mp
      rw [(hcyclic i).2]
      exact hq i
  have hmonic : (∏ i, p i).Monic := Polynomial.monic_prod_of_monic _ _ (fun i _ => (h i).monic)
  have heq : M10.Cyclic.vectorAnnihilator K V T (∑ i, v i) = ∏ i, p i := by
    apply Foundations.IdealsGcd.monic_generators_eq
      (M10.Cyclic.monic_generator T (∑ i, v i)).1 hmonic
    rw [← (M10.Cyclic.monic_generator T (∑ i, v i)).2]
    ext q
    rw [Ideal.mem_span_singleton, M10.Cyclic.mem_annihilator]
    exact hann q
  refine ⟨hspan, heq, ?_, e, hextract v (fun i => (hv i).1)⟩
  intro x hx i
  apply Subtype.ext
  have hi := hextract (fun k => (x k : V)) (fun k => (x k).property) i
  rw [hx, map_zero] at hi
  exact hi.symm


theorem group_labels : Specs.D05.M13.NormalClassification.CyclicLayers.group_labels := by
  intro K ι _ _ p
  classical
  let P : Finset K[X] := Finset.univ.image p
  let f : ι → P := fun i => ⟨p i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  have hf : Function.Surjective f := by
    rintro ⟨q, hq⟩
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hq
    exact ⟨i, Subtype.ext hi⟩
  let m : P → ℕ := fun q => Fintype.card {i // f i = q}
  let e : ι ≃ (Σ q : P, Fin (m q)) :=
    (Equiv.sigmaFiberEquiv f).symm.trans
      (Equiv.sigmaCongrRight fun q => Fintype.equivFin {i // f i = q})
  refine ⟨P, m, e, fun i => rfl, ?_⟩
  intro q
  obtain ⟨i, hi⟩ := hf q
  exact Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩

theorem choose_vectors : Specs.D05.M13.NormalClassification.CyclicLayers.choose_vectors := by
  intro K V ι _ _ _ _ _ T m p H h
  have hex (i : ι) (k : Fin (m i)) : ∃ v : V, v ∈ H i k ∧ v ≠ 0 := by
    have hpos : 0 < Module.finrank K (H i k) :=
      (h i k).dimension ▸ (h i k).irreducible.natDegree_pos
    obtain ⟨v, hv⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := K) (M := H i k)).mp hpos
    exact ⟨v, v.property, fun hz => hv (Subtype.ext hz)⟩
  choose v hv using hex
  exact ⟨v, hv⟩

lemma layerPolynomial_filter {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (p : ι → K[X]) (j : ℕ) :
    layerPolynomial m p j = ∏ i ∈ Finset.univ.filter (fun i => j < m i), p i := by
  classical
  exact (Finset.prod_subtype _ (by simp) p).symm

theorem descending_factors : Specs.D05.M13.NormalClassification.CyclicLayers.descending_factors := by
  intro K ι _ _ m p j
  classical
  rw [layerPolynomial_filter, layerPolynomial_filter]
  apply Finset.prod_dvd_prod_of_subset
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  omega

theorem cyclic_layers : Specs.D05.M13.NormalClassification.CyclicLayers.cyclic_layers := by
  intro K V ι _ _ _ _ _ T m p H v h hp hv j hj
  classical
  let H' : Available m j → Submodule K V := fun i => H i.1 ⟨j, i.2⟩
  let p' : Available m j → K[X] := fun i => p i.1
  let v' : Available m j → V := fun i => v i.1 ⟨j, i.2⟩
  have hb (i : Available m j) : Block T (H' i) (p' i) := h i.1 ⟨j, i.2⟩
  have hp' : Function.Injective p' := fun i k hik => Subtype.ext (hp hik)
  obtain ⟨hs, ha, hd, e, he⟩ := single_layer T H' p' v' hb hp'
    (fun i => hv i.1 ⟨j, i.2⟩)
  have hm : (layerPolynomial m p j).Monic :=
    Polynomial.monic_prod_of_monic _ p' (fun i _ => (hb i).monic)
  have hpos : 0 < (layerPolynomial m p j).natDegree := by
    obtain ⟨i, _, hi⟩ := Finset.lt_sup_iff.mp hj
    let i' : Available m j := ⟨i, hi⟩
    change 0 < (∏ i : Available m j, p' i).natDegree
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun i _ => (hb i).monic)]
    exact lt_of_lt_of_le (hb i').irreducible.natDegree_pos
      (Finset.single_le_sum (f := fun i => (p' i).natDegree) (fun i _ => Nat.zero_le _) (Finset.mem_univ i'))
  exact ⟨hs, ha, hm, hpos, hd, e, he⟩

theorem zero_layers : Specs.D05.M13.NormalClassification.CyclicLayers.zero_layers := by
  intro K V ι _ _ _ _ _ _ T m p H v h
  classical
  have hm (i : ι) : m i = 0 := by
    by_contra hi
    have hi' : 0 < m i := Nat.pos_of_ne_zero hi
    have hz : Module.finrank K (H i ⟨0, hi'⟩) = 0 := Module.finrank_zero_of_subsingleton
    have hd := (h i ⟨0, hi'⟩).dimension
    have hp := (h i ⟨0, hi'⟩).irreducible.natDegree_pos
    omega
  have hc : layerCount m = 0 := by simp [layerCount, show m = fun _ => 0 from funext hm]
  refine ⟨hc, ?_, ?_⟩
  · exact List.ofFn_eq_nil_iff.mpr hc
  · exact List.ofFn_eq_nil_iff.mpr hc


theorem line_block : Specs.D05.M13.NormalClassification.CyclicLayers.line_block := by
  intro K V _ _ _ T v a hv hT
  refine ⟨monic_X_sub_C a, irreducible_X_sub_C a, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [map_smul, hT]
    exact Submodule.smul_mem _ c (Submodule.smul_mem _ a (Submodule.mem_span_singleton_self v))
  · simp [finrank_span_singleton hv]
  · intro x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    simp [map_sub, aeval_X, aeval_C, hT, Algebra.algebraMap_eq_smul_one]

lemma planePolynomial_degree (a b : ℝ) : (planePolynomial a b).natDegree = 2 := by
  rw [planePolynomial, Polynomial.natDegree_add_C]
  simp [Polynomial.natDegree_pow]

lemma planePolynomial_monic (a b : ℝ) : (planePolynomial a b).Monic := by
  apply ((monic_X_sub_C a).pow 2).add_of_left
  apply lt_of_le_of_lt (degree_C_le)
  simp [Polynomial.degree_pow]

lemma planePolynomial_irreducible (a b : ℝ) (hb : 0 < b) :
    Irreducible (planePolynomial a b) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · simp [planePolynomial_degree]
  · intro x hx
    have hz : (x - a) ^ 2 + b ^ 2 = 0 := by simpa [IsRoot, planePolynomial] using hx
    nlinarith [sq_nonneg (x - a), sq_pos_of_pos hb]

theorem plane_block : Specs.D05.M13.NormalClassification.CyclicLayers.plane_block := by
  intro V _ _ T e f a b ho hb hT
  let H := Submodule.span ℝ (Set.range ![e, f])
  have he : e ∈ H := Submodule.subset_span ⟨0, rfl⟩
  have hf : f ∈ H := Submodule.subset_span ⟨1, rfl⟩
  have hTe : T e ∈ H := by rw [hT.1]; exact H.add_mem (H.smul_mem a he) (H.smul_mem b hf)
  have hTf : T f ∈ H := by rw [hT.2]; exact H.add_mem (H.smul_mem (-b) he) (H.smul_mem a hf)
  refine ⟨planePolynomial_monic a b, planePolynomial_irreducible a b hb, ?_, ?_, ?_⟩
  · intro x hx
    apply Submodule.span_induction (p := fun x _ => T x ∈ H) _ _ _ _ hx
    · rintro _ ⟨i, rfl⟩
      fin_cases i <;> simpa using (by first | exact hTe | exact hTf)
    · simp
    · intro x y _ _ hx hy
      simpa using H.add_mem hx hy
    · intro c x _ hx
      simpa using H.smul_mem c hx
  · rw [planePolynomial_degree]
    simpa using finrank_span_eq_card ho.linearIndependent
  · have hkill (i : Fin 2) : aeval T (planePolynomial a b) (![e, f] i) = 0 := by
      fin_cases i <;>
        simp [planePolynomial, pow_two, map_add, map_mul, map_sub, aeval_X, aeval_C,
          Module.End.mul_apply, Algebra.algebraMap_eq_smul_one, hT.1, hT.2] <;> module
    intro x hx
    have hle : H ≤ LinearMap.ker (aeval T (planePolynomial a b)) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact hkill i
    exact hle hx


/-- Reindex the given blocks by their polynomial fibers, then choose one
nonzero vector per block and apply the proved CRT layer theorem. -/
theorem grouped_layers : Specs.D05.M13.NormalClassification.CyclicLayers.grouped_layers := by
  intro K V ι _ _ _ _ _ T H p h
  classical
  obtain ⟨P, m, e, he, hm⟩ := group_labels p
  let H' : ∀ q : P, Fin (m q) → Submodule K V := fun q k => H (e.symm ⟨q, k⟩)
  have hlabel (q : P) (k : Fin (m q)) : p (e.symm ⟨q, k⟩) = (q : K[X]) := by
    simpa using (he (e.symm ⟨q, k⟩)).symm
  have hb (q : P) (k : Fin (m q)) : Block T (H' q k) (q : K[X]) := by
    rw [← hlabel q k]
    exact h _
  obtain ⟨v, hv⟩ := choose_vectors T m (fun q : P => (q : K[X])) H' hb
  exact ⟨P, m, e, v, he, hm, hv,
    cyclic_layers T m (fun q : P => (q : K[X])) H' v hb Subtype.val_injective hv,
    descending_factors m (fun q : P => (q : K[X]))⟩

end D05.M13.NormalClassification.CyclicLayers
