import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.BialgebraDeformation.CompletedPolynomialMaps
import Mathlib.RingTheory.PowerSeries.Evaluation
import Mathlib.RingTheory.MvPowerSeries.LinearTopology
import Mathlib.Topology.UniformSpace.DiscreteUniformity
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.Algebra.Polynomial.Div

open scoped PowerSeries.WithPiTopology TensorProduct Topology

namespace LieNotes.BialgebraDeformation

open PowerSeries PowerSeries.WithPiTopology

noncomputable section

section Maps

variable {k A B D : Type*} [CommRing k] [CommRing A] [CommRing B] [CommRing D]
variable [Algebra k A] [Algebra k B] [Algebra k D]

local instance : UniformSpace k := ⊥
local instance : UniformSpace A := ⊥
local instance : UniformSpace B := ⊥
local instance : UniformSpace D := ⊥
local instance : DiscreteUniformity k := inferInstanceAs (@DiscreteUniformity k ⊥)
local instance : DiscreteUniformity A := inferInstanceAs (@DiscreteUniformity A ⊥)
local instance : DiscreteUniformity B := inferInstanceAs (@DiscreteUniformity B ⊥)
local instance : DiscreteUniformity D := inferInstanceAs (@DiscreteUniformity D ⊥)

private theorem continuous_mapCoefficients {S T : Type*} [CommRing S] [CommRing T]
    [TopologicalSpace S] [TopologicalSpace T] (f : S →+* T) (hf : Continuous f) :
    Continuous (PowerSeries.map f : PowerSeries S → PowerSeries T) := by
  rw [continuous_iff_continuousAt]
  intro p
  rw [ContinuousAt, tendsto_iff_coeff_tendsto]
  intro n
  simpa only [coeff_map, Function.comp_apply, Function.comp_def] using
    hf.continuousAt.tendsto.comp ((continuous_coeff S n).continuousAt (x := p)).tendsto

private theorem polynomial_restriction_ext {S Q : Type*} [CommRing S] [Semiring Q]
    (f g : PowerSeries S →+* Q) (hC : ∀ x, f (C x) = g (C x)) (hX : f X = g X) :
    f.comp Polynomial.coeToPowerSeries.ringHom = g.comp Polynomial.coeToPowerSeries.ringHom := by
  apply Polynomial.ringHom_ext
  · intro x
    simpa only [RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C]
      using hC x
  · simpa only [RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]
      using hX

private theorem continuous_ringHom_ext (f g : PowerSeries A →+* PowerSeries B)
    (hf : Continuous f) (hg : Continuous g)
    (hC : ∀ x, f (C x) = g (C x)) (hX : f X = g X) : f = g := by
  apply DFunLike.coe_injective
  apply (denseRange_toPowerSeries A).equalizer hf hg
  exact congrArg (fun h : Polynomial A →+* PowerSeries B ↦ ⇑h)
    (polynomial_restriction_ext f g hC hX)

private def evaluatedMap (a : A →ₐ[k] PowerSeries B) : PowerSeries A →+* PowerSeries B :=
  eval₂Hom (continuous_of_discreteTopology (f := a.toRingHom)) HasEval.X

private theorem evaluatedMap_apply (a : A →ₐ[k] PowerSeries B) (p : PowerSeries A) :
    evaluatedMap a p = eval₂ a.toRingHom (X : PowerSeries B) p :=
  congrFun (coe_eval₂Hom _ _) p

private theorem continuous_evaluatedMap (a : A →ₐ[k] PowerSeries B) :
    Continuous (evaluatedMap a) := by
  rw [show ⇑(evaluatedMap a) = eval₂ a.toRingHom (X : PowerSeries B) from
    funext (evaluatedMap_apply a)]
  exact continuous_eval₂ (continuous_of_discreteTopology (f := a.toRingHom))
      (HasEval.X : HasEval (X : PowerSeries B))

/-- Extend a coefficient algebra homomorphism by continuous evaluation at the same variable. -/
def extendSeries (a : A →ₐ[k] PowerSeries B) : PowerSeries A →ₐ[PowerSeries k] PowerSeries B where
  __ := evaluatedMap a
  commutes' p := by
    change ((evaluatedMap a).comp (PowerSeries.map (algebraMap k A))) p =
      PowerSeries.map (algebraMap k B) p
    congr 1
    apply continuous_ringHom_ext
    · exact (continuous_evaluatedMap a).comp (continuous_mapCoefficients _
        continuous_of_discreteTopology)
    · exact continuous_mapCoefficients _ continuous_of_discreteTopology
    · intro x
      simp only [RingHom.comp_apply, map_C, evaluatedMap_apply, eval₂_C]
      change a (algebraMap k A x) = C (algebraMap k B x)
      rw [a.commutes, PowerSeries.algebraMap_apply]
    · simp [evaluatedMap_apply]

theorem extendSeries_continuous (a : A →ₐ[k] PowerSeries B) : SeriesContinuous (extendSeries a) :=
  continuous_evaluatedMap a

@[simp] theorem extendSeries_C (a : A →ₐ[k] PowerSeries B) (x : A) :
    extendSeries a (C x) = a x := by
  change evaluatedMap a (C x) = a x
  simp [evaluatedMap_apply]

@[simp] theorem extendSeries_X (a : A →ₐ[k] PowerSeries B) :
    extendSeries a X = X := by
  change evaluatedMap a X = X
  simp [evaluatedMap_apply]

theorem extendSeries_coeff (a : A →ₐ[k] PowerSeries B) (p : PowerSeries A) (n : ℕ) :
    coeff n (extendSeries a p) =
      ∑ j ∈ Finset.range (n + 1), coeff (n - j) (a (coeff j p)) := by
  have h := hasSum_eval₂ (continuous_of_discreteTopology (f := a.toRingHom))
    (HasEval.X : HasEval (X : PowerSeries B)) p
  have hn := (hasSum_iff_hasSum_coeff B).mp h n
  change coeff n (evaluatedMap a p) = _
  rw [evaluatedMap_apply]
  refine (hn.unique (hasSum_sum_of_ne_finset_zero (s := Finset.range (n + 1)) ?_)).trans ?_
  · intro j hj
    simp only [Finset.mem_range, not_lt] at hj
    rw [coeff_mul_X_pow', ite_eq_right (by omega)]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [coeff_mul_X_pow', ite_eq_left (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
    rfl

theorem seriesHom_ext (f g : PowerSeries A →ₐ[PowerSeries k] PowerSeries B)
    (hf : SeriesContinuous f) (hg : SeriesContinuous g)
    (h : ∀ x, f (C x) = g (C x)) : f = g := by
  apply AlgHom.toRingHom_injective
  refine continuous_ringHom_ext _ _ hf hg h ?_
  change f X = g X
  calc
    f X = f (algebraMap (PowerSeries k) (PowerSeries A) X) :=
      congrArg f (map_X (algebraMap k A)).symm
    _ = g (algebraMap (PowerSeries k) (PowerSeries A) X) :=
      (f.commutes X).trans (g.commutes X).symm
    _ = g X := congrArg g (map_X (algebraMap k A))

theorem seriesExtension : SeriesExtensionSpec := by
  intro k A B _ _ _ _ _ a
  exact ⟨extendSeries a, ⟨extendSeries_continuous a, extendSeries_X a, extendSeries_C a⟩,
    fun G hG ↦ seriesHom_ext _ _ hG.1 (extendSeries_continuous a)
      (fun x ↦ (hG.2.2 x).trans (extendSeries_C a x).symm),
    extendSeries_coeff a⟩

theorem seriesComposition : SeriesCompositionSpec := by
  intro k A B D _ _ _ _ _ _ _ a b F G hF hG
  refine ⟨?_, ?_, ?_⟩
  · exact hG.1.comp hF.1
  · change G (F X) = X
    rw [hF.2.1, hG.2.1]
  · intro x
    change G (F (C x)) = G (a x)
    rw [hF.2.2]

theorem seriesCoefficientMap : SeriesCoefficientMapSpec := by
  intro k A B _ _ _ _ _ f
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · change Continuous (PowerSeries.map f.toRingHom)
    exact continuous_mapCoefficients _ continuous_of_discreteTopology
  · exact PowerSeries.map_X _
  · intro x
    change PowerSeries.map f.toRingHom (C x) = C (f x)
    rw [PowerSeries.map_C]
    rfl
  · intro p n
    change coeff n (PowerSeries.map f.toRingHom p) = f (coeff n p)
    rw [PowerSeries.coeff_map]
    rfl

theorem seriesPolynomialExt : SeriesPolynomialExtSpec := by
  intro k D ι _ _ _ F G hF hG h
  apply seriesHom_ext F G hF hG
  have he : (restrictSeriesMap F).comp (seriesConstants k (MvPolynomial ι k)) =
      (restrictSeriesMap G).comp (seriesConstants k (MvPolynomial ι k)) :=
    MvPolynomial.algHom_ext h
  exact AlgHom.congr_fun he

theorem seriesTensorExt : SeriesTensorExtSpec := by
  intro k A B D _ _ _ _ _ _ _ F G hF hG hleft hright
  apply seriesHom_ext F G hF hG
  have he : (restrictSeriesMap F).comp (seriesConstants k (A ⊗[k] B)) =
      (restrictSeriesMap G).comp (seriesConstants k (A ⊗[k] B)) := by
    apply Algebra.TensorProduct.ext
    · exact AlgHom.ext hleft
    · exact AlgHom.ext hright
  exact AlgHom.congr_fun he

/-- Tensor two coefficient homomorphisms and then extend on the completed tensor product. -/
def tensorSeriesMap {E : Type*} [CommRing E] [Algebra k E]
    (a : A →ₐ[k] PowerSeries D) (b : B →ₐ[k] PowerSeries E) :
    PowerSeries (A ⊗[k] B) →ₐ[PowerSeries k] PowerSeries (D ⊗[k] E) :=
  extendSeries (tensorSeriesCoefficient a b)

@[simp] theorem seriesMap_C (f : A →ₐ[k] B) (x : A) :
    seriesMap f (C x) = C (f x) :=
  (seriesCoefficientMap f).1.2.2 x

@[simp] theorem seriesMap_coeff (f : A →ₐ[k] B) (p : PowerSeries A) (n : ℕ) :
    coeff n (seriesMap f p) = f (coeff n p) :=
  (seriesCoefficientMap f).2 p n

theorem seriesMap_continuous (f : A →ₐ[k] B) : SeriesContinuous (seriesMap f) :=
  (seriesCoefficientMap f).1.1

private theorem seriesContinuous_comp {S T U : Type*}
    {f : PowerSeries S → PowerSeries T} {g : PowerSeries T → PowerSeries U}
    (hg : SeriesContinuous g) (hf : SeriesContinuous f) : SeriesContinuous (g ∘ f) :=
  Continuous.comp (g := g) (f := f) hg hf

theorem seriesTensorMaps : SeriesTensorMapsSpec := by
  intro k A B D E _ _ _ _ _ _ _ _ _ a b F G H hF hG hH p q
  let l : A →ₐ[k] A ⊗[k] B := Algebra.TensorProduct.includeLeft
  let r : B →ₐ[k] A ⊗[k] B := Algebra.TensorProduct.includeRight
  let l' : D →ₐ[k] D ⊗[k] E := Algebra.TensorProduct.includeLeft
  let r' : E →ₐ[k] D ⊗[k] E := Algebra.TensorProduct.includeRight
  have left : H.comp (seriesMap l) = (seriesMap l').comp F := by
    refine seriesHom_ext (H.comp (seriesMap l)) ((seriesMap l').comp F) ?_ ?_ ?_
    · exact seriesContinuous_comp (f := seriesMap l) (g := H) hH.1 (seriesMap_continuous l)
    · exact seriesContinuous_comp (f := F) (g := seriesMap l') (seriesMap_continuous l') hF.1
    intro x
    simp only [AlgHom.comp_apply, seriesMap_C, hH.2.2, hF.2.2]
    change tensorSeriesCoefficient a b (x ⊗ₜ[k] (1 : B)) = seriesMap l' (a x)
    rw [tensorSeriesCoefficient, Algebra.TensorProduct.productMap_left_apply]
    rfl
  have right : H.comp (seriesMap r) = (seriesMap r').comp G := by
    refine seriesHom_ext (H.comp (seriesMap r)) ((seriesMap r').comp G) ?_ ?_ ?_
    · exact seriesContinuous_comp (f := seriesMap r) (g := H) hH.1 (seriesMap_continuous r)
    · exact seriesContinuous_comp (f := G) (g := seriesMap r') (seriesMap_continuous r') hG.1
    intro y
    simp only [AlgHom.comp_apply, seriesMap_C, hH.2.2, hG.2.2]
    change tensorSeriesCoefficient a b ((1 : A) ⊗ₜ[k] y) = seriesMap r' (b y)
    rw [tensorSeriesCoefficient, Algebra.TensorProduct.productMap_right_apply]
    rfl
  change H (seriesMap l p * seriesMap r q) = seriesMap l' (F p) * seriesMap r' (G q)
  rw [map_mul]
  exact congrArg₂ (· * ·) (AlgHom.congr_fun left p) (AlgHom.congr_fun right q)

theorem seriesTensorAssociativity : SeriesTensorAssociativitySpec := by
  intro k A B D _ _ _ _ _ _ _ p q r
  let e := (Algebra.TensorProduct.assoc k k k A B D).toAlgHom
  let abL : A →ₐ[k] A ⊗[k] B := Algebra.TensorProduct.includeLeft
  let abR : B →ₐ[k] A ⊗[k] B := Algebra.TensorProduct.includeRight
  let bdL : B →ₐ[k] B ⊗[k] D := Algebra.TensorProduct.includeLeft
  let bdR : D →ₐ[k] B ⊗[k] D := Algebra.TensorProduct.includeRight
  let leftL : A ⊗[k] B →ₐ[k] (A ⊗[k] B) ⊗[k] D := Algebra.TensorProduct.includeLeft
  let leftR : D →ₐ[k] (A ⊗[k] B) ⊗[k] D := Algebra.TensorProduct.includeRight
  let rightL : A →ₐ[k] A ⊗[k] (B ⊗[k] D) := Algebra.TensorProduct.includeLeft
  let rightR : B ⊗[k] D →ₐ[k] A ⊗[k] (B ⊗[k] D) := Algebra.TensorProduct.includeRight
  have hp : seriesMap e (seriesMap leftL (seriesMap abL p)) = seriesMap rightL p := by
    apply PowerSeries.ext
    intro n
    simp only [seriesMap_coeff]
    rfl
  have hq : seriesMap e (seriesMap leftL (seriesMap abR q)) =
      seriesMap rightR (seriesMap bdL q) := by
    apply PowerSeries.ext
    intro n
    simp only [seriesMap_coeff]
    rfl
  have hr : seriesMap e (seriesMap leftR r) = seriesMap rightR (seriesMap bdR r) := by
    apply PowerSeries.ext
    intro n
    simp only [seriesMap_coeff]
    rfl
  change seriesMap e (seriesMap leftL (seriesMap abL p * seriesMap abR q) * seriesMap leftR r) =
    seriesMap rightL p * seriesMap rightR (seriesMap bdL q * seriesMap bdR r)
  rw [map_mul, map_mul, map_mul, hp, hq, hr, map_mul, mul_assoc]

end Maps


section Topology

open Filter Set

private theorem mem_seriesVariableIdeal_pow {A : Type*} [CommRing A] {n : ℕ} {p : PowerSeries A} :
    p ∈ seriesVariableIdeal A ^ n ↔ ∀ i < n, coeff i p = 0 := by
  rw [seriesVariableIdeal, Ideal.span_singleton_pow, Ideal.mem_span_singleton, X_pow_dvd_iff]

theorem seriesAdicTopology : SeriesAdicTopologySpec := by
  intro A _
  let : UniformSpace A := ⊥
  have : DiscreteUniformity A := inferInstanceAs (@DiscreteUniformity A ⊥)
  have hadic : IsAdic (seriesVariableIdeal A) := by
    rw [isAdic_iff]
    constructor
    · intro n
      have he : (↑(seriesVariableIdeal A ^ n) : Set (PowerSeries A)) =
          ⋂ i : Fin n, (coeff (i : ℕ)) ⁻¹' ({0} : Set A) := by
        ext p
        simp only [SetLike.mem_coe, mem_seriesVariableIdeal_pow, mem_iInter, mem_preimage,
          mem_singleton_iff]
        exact ⟨fun h i ↦ h i i.isLt, fun h i hi ↦ h ⟨i, hi⟩⟩
      rw [he]
      exact isOpen_iInter_of_finite fun i ↦ (continuous_coeff A i).isOpen_preimage _
        (isOpen_discrete _)
    · intro s hs
      let v : Set ((Unit →₀ ℕ) → A) := s
      have hsv : v ∈ 𝓝 (fun _ : Unit →₀ ℕ ↦ (0 : A)) := hs
      rw [nhds_pi] at hsv
      obtain ⟨J, U, hU, hJU⟩ := Filter.mem_pi'.mp hsv
      refine ⟨J.sup (fun j ↦ j ()) + 1, fun p hp ↦ hJU ?_⟩
      intro j hj
      have hzero : (0 : A) ∈ U j := mem_of_mem_nhds (hU j)
      have hlt : j () < J.sup (fun j ↦ j ()) + 1 :=
        Nat.lt_succ_of_le (Finset.le_sup (f := fun j ↦ j ()) hj)
      have hpj : p j = 0 := by
        change MvPowerSeries.coeff j p = 0
        rw [← coeff_def (R := A) (s := j) rfl]
        exact (mem_seriesVariableIdeal_pow.mp hp) (j ()) hlt
      simpa only [hpj] using hzero
  exact ⟨hadic, hadic.isAdicComplete_iff.mpr ⟨inferInstance, inferInstance⟩⟩

end Topology


section Completion

open Ideal

private theorem span_pow_le_comap {S T : Type*} [CommRing S] [CommRing T]
    (f : S →+* T) {x : S} {y : T} (h : f x = y) (n : ℕ) :
    Ideal.span {x} ^ n ≤ (Ideal.span {y} ^ n).comap f := by
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_pow, h,
    Ideal.span_singleton_pow]
  exact Ideal.subset_span (Set.mem_singleton _)

private theorem completion_eval_transition {S : Type*} [CommRing S]
    (I : Ideal S) {m n : ℕ} (h : m ≤ n) (x : AdicCompletion I S) :
    Ideal.Quotient.factorPow I h (AdicCompletion.evalₐ I n x) = AdicCompletion.evalₐ I m x := by
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  have htop (i : ℕ) : (I ^ i • ⊤ : Ideal S) = I ^ i := by rw [smul_eq_mul, Ideal.mul_top]
  have hv : (Ideal.Quotient.mk (I ^ n • ⊤ : Ideal S)) r = x.val n := by
    have he := congrArg (Ideal.Quotient.factor (le_of_eq (htop n).symm)) hr
    rw [Ideal.Quotient.factor_mk, AdicCompletion.factor_evalₐ_eq_eval] at he
    exact he
  have hn := x.prop h
  rw [← hv, AdicCompletion.transitionMap_ideal_mk] at hn
  have hm := congrArg (Ideal.Quotient.factor (le_of_eq (htop m))) hn
  change Ideal.Quotient.factor _ (Ideal.Quotient.mk _ r) =
    Ideal.Quotient.factor _ (AdicCompletion.eval I S m x) at hm
  rw [Ideal.Quotient.factor_mk, ← Submodule.factor_eq_factor,
    AdicCompletion.factor_eval_eq_evalₐ] at hm
  rw [← hr, Ideal.Quotient.factor_mk, hm]

/-- Compatible quotient identifications induced by one map identify its adic completion. -/
private theorem completion_of_quotient_equivs {S T : Type*} [CommRing S] [CommRing T]
    (I : Ideal S) (J : Ideal T) [IsAdicComplete J T] (f : S →+* T)
    (e : ∀ n, (S ⧸ I ^ n) ≃+* (T ⧸ J ^ n))
    (he : ∀ n x, e n (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (f x)) :
    ∃ E : AdicCompletion I S ≃+* T, ∀ x, E (AdicCompletion.of I S x) = f x := by
  have transition {m n} (h : m ≤ n) (q : S ⧸ I ^ n) :
      Ideal.Quotient.factorPow J h (e n q) = e m (Ideal.Quotient.factorPow I h q) := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    simp only [he, Ideal.Quotient.factor_mk]
  have reverseTransition {m n} (h : m ≤ n) (q : T ⧸ J ^ n) :
      Ideal.Quotient.factorPow I h ((e n).symm q) = (e m).symm (Ideal.Quotient.factorPow J h q) := by
    apply (e m).injective
    rw [← transition h, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  let forward := IsAdicComplete.liftRingHom J
    (fun n ↦ (e n).toRingHom.comp (AdicCompletion.evalₐ I n).toRingHom)
    (fun h ↦ RingHom.ext fun x ↦ (transition h _).trans (congrArg (e _) (completion_eval_transition I h x)))
  let backward := AdicCompletion.liftRingHom I
    (fun n ↦ (e n).symm.toRingHom.comp (Ideal.Quotient.mk (J ^ n)))
    (fun h ↦ RingHom.ext fun x ↦ reverseTransition h (Ideal.Quotient.mk _ x))
  have forward_apply (n) (x : AdicCompletion I S) :
      Ideal.Quotient.mk (J ^ n) (forward x) = e n (AdicCompletion.evalₐ I n x) := by
    exact IsAdicComplete.mk_liftRingHom J _ _ n x
  have backward_apply (n) (x : T) :
      AdicCompletion.evalₐ I n (backward x) = (e n).symm (Ideal.Quotient.mk (J ^ n) x) := by
    exact AdicCompletion.evalₐ_liftRingHom I _ _ n x
  have hleft : forward.comp backward = RingHom.id T := by
    apply DFunLike.coe_injective
    apply IsHausdorff.funext' J
    intro n x
    change Ideal.Quotient.mk (J ^ n) (forward (backward x)) = Ideal.Quotient.mk _ x
    rw [forward_apply, backward_apply, RingEquiv.apply_symm_apply]
  have hright : backward.comp forward = RingHom.id (AdicCompletion I S) := by
    apply RingHom.ext
    intro x
    apply AdicCompletion.ext_evalₐ
    intro n
    change AdicCompletion.evalₐ I n (backward (forward x)) = AdicCompletion.evalₐ I n x
    rw [backward_apply, forward_apply, RingEquiv.symm_apply_apply]
  refine ⟨RingEquiv.ofRingHom forward backward hleft hright, ?_⟩
  have h : (fun x ↦ forward (AdicCompletion.of I S x)) = f := by
    apply IsHausdorff.funext' J
    intro n x
    rw [forward_apply, AdicCompletion.evalₐ_of, he]
  exact congrFun h

theorem polynomialCompletion : PolynomialCompletionSpec := by
  intro A _
  let I := polynomialVariableIdeal A
  let J := seriesVariableIdeal A
  let f := Polynomial.coeToPowerSeries.ringHom (R := A)
  have : IsAdicComplete J (PowerSeries A) := (seriesAdicTopology A).2
  let nmap (n : ℕ) : (Polynomial A ⧸ I ^ n) →+* (PowerSeries A ⧸ J ^ n) :=
    Ideal.quotientMap _ f (span_pow_le_comap f Polynomial.coe_X n)
  have injective (n) : Function.Injective (nmap n) := by
    intro x y h
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective y
    change Ideal.Quotient.mk (J ^ n) (p : PowerSeries A) =
      Ideal.Quotient.mk (J ^ n) (q : PowerSeries A) at h
    have hz := mem_seriesVariableIdeal_pow.mp (Ideal.Quotient.eq.mp h)
    apply Ideal.Quotient.eq.mpr
    change p - q ∈ Ideal.span {Polynomial.X} ^ n
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, Polynomial.X_pow_dvd_iff]
    intro i hi
    rw [← Polynomial.coeff_coe, Polynomial.coe_sub]
    exact hz i hi
  have surjective (n) : Function.Surjective (nmap n) := by
    intro x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨Ideal.Quotient.mk _ (trunc n p), ?_⟩
    change Ideal.Quotient.mk (J ^ n) (trunc n p : PowerSeries A) = Ideal.Quotient.mk _ p
    apply Ideal.Quotient.eq.mpr
    apply mem_seriesVariableIdeal_pow.mpr
    intro i hi
    simp [Polynomial.coeff_coe, coeff_trunc, hi]
  obtain ⟨E, hE⟩ := completion_of_quotient_equivs I J f
    (fun n ↦ RingEquiv.ofBijective (nmap n) ⟨injective n, surjective n⟩) (fun _ _ ↦ rfl)
  refine ⟨E.symm, fun p ↦ E.injective ?_⟩
  exact (E.apply_symm_apply (p : PowerSeries A)).trans (hE p).symm

private theorem series_ringHom_ext_of_pow_zero {S T : Type*} [CommRing S] [CommRing T]
    (n : ℕ) (f g : PowerSeries S →+* T) (hf : f X ^ n = 0) (hg : g X ^ n = 0)
    (hC : ∀ x, f (C x) = g (C x)) (hX : f X = g X) : f = g := by
  have onPolynomials := polynomial_restriction_ext f g hC hX
  apply RingHom.ext
  intro p
  have eqTrunc (u : PowerSeries S →+* T) (hu : u X ^ n = 0) :
      u p = u (trunc n p : PowerSeries S) := by
    have h := congrArg u (eq_X_pow_mul_shift_add_trunc n p)
    simpa only [map_pow, map_mul, map_add, hu, zero_mul, zero_add] using h
  rw [eqTrunc f hf, eqTrunc g hg]
  exact DFunLike.congr_fun onPolynomials (trunc n p)

private def coefficientIntoAlgebra {k A Q : Type*} [CommRing k] [CommRing A] [CommRing Q]
    [Algebra k A] [Algebra (PowerSeries k) Q] [Algebra k Q]
    (h : ∀ x : k, algebraMap k Q x = algebraMap (PowerSeries k) Q (C x))
    (f : PowerSeries A →ₐ[PowerSeries k] Q) : A →ₐ[k] Q where
  toRingHom := f.toRingHom.comp C
  commutes' x := by
    change f (C (algebraMap k A x)) = algebraMap k Q x
    rw [← PowerSeries.algebraMap_apply, ← scalarSeries_C, f.commutes, h]

section NilpotentEvaluation

variable {S Q : Type*} [CommRing S] [CommRing Q]

local instance : UniformSpace S := ⊥
local instance : UniformSpace Q := ⊥
local instance : DiscreteUniformity S := inferInstanceAs (@DiscreteUniformity S ⊥)
local instance : DiscreteUniformity Q := inferInstanceAs (@DiscreteUniformity Q ⊥)

private def nilpotentSeriesEval (f : S →+* Q) {z : Q} (hz : IsNilpotent z) :
    PowerSeries S →+* Q :=
  eval₂Hom (continuous_of_discreteTopology (f := f)) hz.isTopologicallyNilpotent

@[simp] private theorem nilpotentSeriesEval_C
    (f : S →+* Q) {z : Q} (hz : IsNilpotent z) (x : S) :
    nilpotentSeriesEval f hz (C x) = f x :=
  (congrFun (coe_eval₂Hom _ _) _).trans (eval₂_C _ _ _)

@[simp] private theorem nilpotentSeriesEval_X
    (f : S →+* Q) {z : Q} (hz : IsNilpotent z) :
    nilpotentSeriesEval f hz X = z :=
  (congrFun (coe_eval₂Hom _ _) _).trans (eval₂_X _ _)

end NilpotentEvaluation

section FiniteTensor

variable {k A B : Type*} [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]

local notation "R" => PowerSeries k
local notation "T" => PowerSeries A ⊗[R] PowerSeries B
local notation "U" => PowerSeries (A ⊗[k] B)

private abbrev formalTensorLeft : PowerSeries A →ₐ[R] T :=
  Algebra.TensorProduct.includeLeft

private abbrev formalTensorRight : PowerSeries B →ₐ[R] T :=
  Algebra.TensorProduct.includeRight

private theorem formalScalar_X {S : Type*} [CommRing S] [Algebra k S] :
    algebraMap R (PowerSeries S) X = X := PowerSeries.map_X _

private theorem seriesTensorSource_ext {Q : Type*} [CommRing Q] (n : ℕ)
    (f g : T →+* Q) (hf : f (algebraMap R T X) ^ n = 0)
    (hg : g (algebraMap R T X) ^ n = 0)
    (hX : f (algebraMap R T X) = g (algebraMap R T X))
    (hl : ∀ x : A, f (formalTensorLeft (C x)) = g (formalTensorLeft (C x)))
    (hr : ∀ x : B, f (formalTensorRight (C x)) = g (formalTensorRight (C x))) : f = g := by
  have hleft : formalTensorLeft (k := k) (B := B) (X : PowerSeries A) = algebraMap R T X := by
    let l : PowerSeries A →ₐ[R] T := formalTensorLeft
    change l X = _
    exact (congrArg l (formalScalar_X (k := k) (S := A)).symm).trans (l.commutes X)
  have hright : formalTensorRight (k := k) (A := A) (X : PowerSeries B) = algebraMap R T X := by
    let r : PowerSeries B →ₐ[R] T := formalTensorRight
    change r X = _
    exact (congrArg r (formalScalar_X (k := k) (S := B)).symm).trans (r.commutes X)
  apply Algebra.TensorProduct.ringHom_ext
  · change f.comp formalTensorLeft.toRingHom = g.comp formalTensorLeft.toRingHom
    refine series_ringHom_ext_of_pow_zero n _ _ ?_ ?_ hl ?_
    · change f (formalTensorLeft X) ^ n = 0
      rw [hleft]
      exact hf
    · change g (formalTensorLeft X) ^ n = 0
      rw [hleft]
      exact hg
    · change f (formalTensorLeft X) = g (formalTensorLeft X)
      rw [hleft]
      exact hX
  · change f.comp formalTensorRight.toRingHom = g.comp formalTensorRight.toRingHom
    refine series_ringHom_ext_of_pow_zero n _ _ ?_ ?_ hr ?_
    · change f (formalTensorRight X) ^ n = 0
      rw [hright]
      exact hf
    · change g (formalTensorRight X) ^ n = 0
      rw [hright]
      exact hg
    · change f (formalTensorRight X) = g (formalTensorRight X)
      rw [hright]
      exact hX

private theorem seriesTensorTarget_ext {Q : Type*} [CommRing Q] (n : ℕ)
    (f g : U →+* Q) (hf : f X ^ n = 0) (hg : g X ^ n = 0) (hX : f X = g X)
    (hl : ∀ x : A, f (C (x ⊗ₜ[k] (1 : B))) = g (C (x ⊗ₜ[k] (1 : B))))
    (hr : ∀ y : B, f (C ((1 : A) ⊗ₜ[k] y)) = g (C ((1 : A) ⊗ₜ[k] y))) : f = g := by
  refine series_ringHom_ext_of_pow_zero n f g hf hg ?_ hX
  have hC : f.comp C = g.comp C := by
    exact Algebra.TensorProduct.ringHom_ext (RingHom.ext hl) (RingHom.ext hr)
  exact DFunLike.congr_fun hC

variable {Q : Type*} [CommRing Q] [Algebra (PowerSeries k) Q]

/-- The pair of maps obtained by restricting a homomorphism to the two coefficient algebras. -/
private def tensorConstantMap (m : T →ₐ[R] Q) : A ⊗[k] B →+* Q := by
  letI : Algebra k Q := ((algebraMap R Q).comp C).toAlgebra
  let a : A →ₐ[k] Q := coefficientIntoAlgebra (fun _ ↦ rfl) (m.comp formalTensorLeft)
  let b : B →ₐ[k] Q := coefficientIntoAlgebra (fun _ ↦ rfl) (m.comp formalTensorRight)
  exact (Algebra.TensorProduct.productMap a b).toRingHom

private theorem tensorConstantMap_left (m : T →ₐ[R] Q) (x : A) :
    tensorConstantMap m (x ⊗ₜ[k] (1 : B)) = m (formalTensorLeft (C x)) := by
  let : Algebra k Q := ((algebraMap R Q).comp C).toAlgebra
  unfold tensorConstantMap
  exact Algebra.TensorProduct.productMap_left_apply _ _ x

private theorem tensorConstantMap_right (m : T →ₐ[R] Q) (y : B) :
    tensorConstantMap m ((1 : A) ⊗ₜ[k] y) = m (formalTensorRight (C y)) := by
  let : Algebra k Q := ((algebraMap R Q).comp C).toAlgebra
  unfold tensorConstantMap
  exact Algebra.TensorProduct.productMap_right_apply _ _ y

private theorem tensorComparison_lift (m : T →ₐ[R] Q) (n : ℕ)
    (hn : m (algebraMap R T X) ^ n = 0) :
    ∃ g : U →+* Q,
      g X = m (algebraMap R T X) ∧
      (∀ x : A, g (C (x ⊗ₜ[k] (1 : B))) = m (formalTensorLeft (C x))) ∧
      (∀ y : B, g (C ((1 : A) ⊗ₜ[k] y)) = m (formalTensorRight (C y))) ∧
      g.comp (seriesTensorComparison (k := k)).toRingHom = m.toRingHom := by
  let z := m (algebraMap R T X)
  have hz : IsNilpotent z := ⟨n, hn⟩
  let c : A ⊗[k] B →+* Q := tensorConstantMap m
  let g : U →+* Q := nilpotentSeriesEval c hz
  have gX : g X = z := nilpotentSeriesEval_X c hz
  have gleft (x : A) : g (C (x ⊗ₜ[k] (1 : B))) = m (formalTensorLeft (C x)) :=
    (nilpotentSeriesEval_C c hz _).trans (tensorConstantMap_left m x)
  have gright (y : B) : g (C ((1 : A) ⊗ₜ[k] y)) = m (formalTensorRight (C y)) :=
    (nilpotentSeriesEval_C c hz _).trans (tensorConstantMap_right m y)
  refine ⟨g, gX, gleft, gright, ?_⟩
  let f : T →ₐ[R] U := seriesTensorComparison
  let t : T := algebraMap R T X
  have ft : f t = X := (f.commutes X).trans formalScalar_X
  have hX : g (f t) = m t := by rw [ft]; exact gX
  refine seriesTensorSource_ext (k := k) (A := A) (B := B) n
    (g.comp f.toRingHom) m.toRingHom ?_ hn hX ?_ ?_
  · change g (f t) ^ n = 0
    rw [hX]
    exact hn
  · intro x
    change g (f (formalTensorLeft (C x))) = m (formalTensorLeft (C x))
    have h (p : PowerSeries A) : f (formalTensorLeft p) =
        seriesMap (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] B) p :=
      Algebra.TensorProduct.productMap_left_apply _ _ p
    rw [h, seriesMap_C]
    exact gleft x
  · intro y
    change g (f (formalTensorRight (C y))) = m (formalTensorRight (C y))
    have h (q : PowerSeries B) : f (formalTensorRight q) =
        seriesMap (Algebra.TensorProduct.includeRight : B →ₐ[k] A ⊗[k] B) q :=
      Algebra.TensorProduct.productMap_right_apply _ _ q
    rw [h, seriesMap_C]
    exact gright y

end FiniteTensor

set_option maxHeartbeats 500000 in
theorem tensorTruncation : TensorTruncationSpec := by
  intro k A B _ _ _ _ _ n
  let R := PowerSeries k
  let T := PowerSeries A ⊗[R] PowerSeries B
  let U := PowerSeries (A ⊗[k] B)
  let J := tensorVariableIdeal k A B
  let I := seriesVariableIdeal (A ⊗[k] B)
  let Q := T ⧸ J ^ n
  let V := U ⧸ I ^ n
  let f : T →ₐ[R] U := seriesTensorComparison
  let left : PowerSeries A →ₐ[R] T := Algebra.TensorProduct.includeLeft
  let right : PowerSeries B →ₐ[R] T := Algebra.TensorProduct.includeRight
  let left₀ : A →ₐ[k] A ⊗[k] B := Algebra.TensorProduct.includeLeft
  let right₀ : B →ₐ[k] A ⊗[k] B := Algebra.TensorProduct.includeRight
  let mkT : T →ₐ[R] Q := Ideal.Quotient.mkₐ R _
  let mkU : U →+* V := Ideal.Quotient.mk _
  let t : T := algebraMap R T (PowerSeries.X : R)
  have scalar_U : algebraMap R U (PowerSeries.X : R) = PowerSeries.X := PowerSeries.map_X _
  have ft : f t = PowerSeries.X := (f.commutes _).trans scalar_U
  have fleft (p : PowerSeries A) : f (left p) = seriesMap left₀ p :=
    Algebra.TensorProduct.productMap_left_apply _ _ p
  have fright (q : PowerSeries B) : f (right q) = seriesMap right₀ q :=
    Algebra.TensorProduct.productMap_right_apply _ _ q
  let fₙ : Q →ₐ[R] V := Ideal.quotientMapₐ _ f (span_pow_le_comap f.toRingHom ft n)
  have fₙ_mk (p : T) : fₙ (mkT p) = mkU (f p) := rfl
  have mkT_zero : mkT t ^ n = 0 := by
    rw [← map_pow]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    change t ^ n ∈ Ideal.span {t} ^ n
    rw [Ideal.span_singleton_pow]
    exact Ideal.subset_span (Set.mem_singleton _)
  have mkU_zero : mkU X ^ n = 0 := by
    rw [← map_pow]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    change (X : U) ^ n ∈ Ideal.span {X} ^ n
    rw [Ideal.span_singleton_pow]
    exact Ideal.subset_span (Set.mem_singleton _)
  obtain ⟨g, gz, gleft, gright, gf⟩ :=
    tensorComparison_lift (k := k) (A := A) (B := B) (Q := Q) mkT n mkT_zero
  have fₙ_g : fₙ.toRingHom.comp g = mkU := by
    have hX : fₙ (g X) = mkU X := by rw [gz, fₙ_mk, ft]
    refine seriesTensorTarget_ext (k := k) (A := A) (B := B) (Q := V) n
      (fₙ.toRingHom.comp g) mkU ?_ mkU_zero hX ?_ ?_
    · change fₙ (g X) ^ n = 0
      rw [hX, mkU_zero]
    · intro x
      change fₙ (g (C (left₀ x))) = mkU (C (left₀ x))
      have hx : g (C (left₀ x)) = mkT (left (C x)) := gleft x
      rw [hx, fₙ_mk, fleft, seriesMap_C]
    · intro y
      change fₙ (g (C (right₀ y))) = mkU (C (right₀ y))
      have hy : g (C (right₀ y)) = mkT (right (C y)) := gright y
      rw [hy, fₙ_mk, fright, seriesMap_C]
  let gₙ : V →+* Q := Ideal.Quotient.lift (I ^ n) g (by
    change Ideal.span {X} ^ n ≤ RingHom.ker g
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, map_pow, gz]
    exact mkT_zero)
  have gₙ_mk (p : U) : gₙ (mkU p) = g p := rfl
  have leftInverse : Function.LeftInverse gₙ fₙ := by
    intro x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    change gₙ (fₙ (mkT p)) = mkT p
    rw [fₙ_mk, gₙ_mk]
    exact DFunLike.congr_fun gf p
  have rightInverse : Function.RightInverse gₙ fₙ := by
    intro x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    change fₙ (gₙ (mkU p)) = mkU p
    rw [gₙ_mk]
    exact DFunLike.congr_fun fₙ_g p
  exact ⟨AlgEquiv.ofBijective fₙ ⟨leftInverse.injective, rightInverse.surjective⟩, fₙ_mk⟩

theorem tensorCompletion : TensorCompletionSpec := by
  intro k A B _ _ _ _ _
  let R := PowerSeries k
  let T := PowerSeries A ⊗[R] PowerSeries B
  let U := PowerSeries (A ⊗[k] B)
  let J := tensorVariableIdeal k A B
  let I := seriesVariableIdeal (A ⊗[k] B)
  let f : T →ₐ[R] U := seriesTensorComparison
  have : IsAdicComplete I U := (seriesAdicTopology (A ⊗[k] B)).2
  choose e he using tensorTruncation k A B
  obtain ⟨E, hE⟩ := completion_of_quotient_equivs J I f.toRingHom
    (fun n ↦ (e n).toRingEquiv) he
  have hScalars (x : R) : E (algebraMap R (AdicCompletion J T) x) = algebraMap R U x := by
    rw [AdicCompletion.algebraMap_apply, hE]
    exact f.commutes x
  exact ⟨AlgEquiv.ofRingEquiv hScalars, hE⟩

end Completion

end

end LieNotes.BialgebraDeformation
