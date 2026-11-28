import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Quantum.Completion
import MathGenome.Internal.LieTheoryDeepening.LieNotes.Quantum.TriangularPBW
import MathGenome.Internal.LieTheoryDeepening.LieNotes.Quantum.Hopf
import Batteries.Tactic.OpenPrivate

noncomputable section

namespace LieNotes.Quantum.Completion

abbrev Uh := @Specs.LieNotes.Quantum.Completion.Uh
abbrev CompletedSquare := @Specs.LieNotes.Quantum.Completion.CompletedSquare
abbrev CompletedLeftCube := @Specs.LieNotes.Quantum.Completion.CompletedLeftCube
abbrev CompletedRightCube := @Specs.LieNotes.Quantum.Completion.CompletedRightCube
abbrev project := @Specs.LieNotes.Quantum.Completion.project

open scoped TensorProduct Topology

set_option linter.style.haveILetI false
open Specs.LieNotes.Quantum.Completion
open private reduce_scalar squareReduce_scalar from MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Quantum.Completion

universe u

variable {k : Type u} [Field k] [CharZero k]

private theorem project_reduce {p : TensorPower} {M N : Level} (e : M ≤ N)
    (x : Limit k p) : reduce p e (project k p N x) = project k p M x :=
  x.property M N e

private theorem project_algebraMap (p : TensorPower) (N : Level) (r : PowerSeries k) :
    project k p N (algebraMap (PowerSeries k) (Limit k p) r) =
      algebraMap (A k N) (AtLevel k p N) (Truncations.truncate N r) := rfl

private theorem project_ext {p : TensorPower} {x y : Limit k p}
    (h : ∀ N, project k p N x = project k p N y) : x = y :=
  Subtype.ext (funext h)

private theorem reduce_left_tmul {M N : Level} (e : M ≤ N) (x : Square k N) (y : U k N) :
    reduce (k := k) .leftCube e (x ⊗ₜ[A k N] y) =
      Specs.LieNotes.Quantum.Coproduct.tensorReduce e x ⊗ₜ[A k M] Presentation.reduce e y :=
  tensorChange_tmul (Truncations.reduce (R := k) e).toRingHom
    (Specs.LieNotes.Quantum.Coproduct.tensorReduce e) (Presentation.reduce e)
    (squareReduce_scalar (k := k) e) (Presentation.reduce_scalar e) x y

private theorem reduce_right_tmul {M N : Level} (e : M ≤ N) (x : U k N) (y : Square k N) :
    reduce (k := k) .rightCube e (x ⊗ₜ[A k N] y) =
      Presentation.reduce e x ⊗ₜ[A k M] Specs.LieNotes.Quantum.Coproduct.tensorReduce e y :=
  tensorChange_tmul (Truncations.reduce (R := k) e).toRingHom
    (Presentation.reduce e) (Specs.LieNotes.Quantum.Coproduct.tensorReduce e)
    (Presentation.reduce_scalar e) (squareReduce_scalar (k := k) e) x y

section Bases

open Specs.LieNotes.Quantum.Presentation (truncated cartan E F cartanReduce)
open Specs.LieNotes.Quantum.TriangularPBW (orderedMonomial zMinus zPlus)

private theorem reduce_monomial {M N : Level} (e : M ≤ N) (i : PBWIndex) :
    Presentation.reduce e (monomial k N i) = monomial k M i := by
  have hu : (Truncations.reduce (R := k) e) (↑((truncated k N).q⁻¹) : A k N) =
      (↑((truncated k M).q⁻¹) : A k M) := by
    have h := LieNotes.Quantum.Presentation.truncatedQ_reduce (k := k) e
    have hv : Units.map (Truncations.reduce (R := k) e).toRingHom.toMonoidHom
        ((truncated k N).q⁻¹) = (truncated k M).q⁻¹ := by rw [map_inv, h]
    exact congrArg Units.val hv
  have hs (a : A k N) (x : U k N) :
      Presentation.reduce e (a • x) = Truncations.reduce e a • Presentation.reduce e x := by
    rw [Algebra.smul_def a x, Algebra.smul_def (Truncations.reduce e a), map_mul,
      Presentation.reduce_scalar]
  simp only [monomial, orderedMonomial, zMinus, zPlus, map_mul, map_pow, map_sub,
    Presentation.reduce_E, Presentation.reduce_F, hs, hu, Presentation.reduce_cartan, map_prod,
    MvPolynomial.map_X]

theorem compatible_bases : CompatibleBasesProp.{u} := by
  intro k _ _ p
  have hb (N : Level) : ∃ b : Module.Basis PBWIndex (A k N) (U k N),
      ∀ i, b i = monomial k N i :=
    (TriangularPBW.truncated k N N.property).2
  choose b hb using hb
  constructor
  · cases p
    · exact ⟨b, hb⟩
    · refine ⟨fun N => (b N).tensorProduct (b N), ?_⟩
      intro N i
      rcases i with ⟨i, j⟩
      simp only [basisVector, Module.Basis.tensorProduct_apply, hb]
    · refine ⟨fun N => ((b N).tensorProduct (b N)).tensorProduct (b N), ?_⟩
      intro N i
      rcases i with ⟨⟨i, j⟩, l⟩
      simp only [basisVector, Module.Basis.tensorProduct_apply, hb]
    · refine ⟨fun N => (b N).tensorProduct ((b N).tensorProduct (b N)), ?_⟩
      intro N i
      rcases i with ⟨i, j, l⟩
      simp only [basisVector, Module.Basis.tensorProduct_apply, hb]
  · intro M N e i
    cases p
    · exact reduce_monomial e i
    · change Specs.LieNotes.Quantum.Coproduct.tensorReduce e (_ ⊗ₜ[A k N] _) = _
      simp only [Specs.LieNotes.Quantum.Coproduct.tensorReduce_tmul, reduce_monomial, basisVector]
    · rcases i with ⟨⟨i, j⟩, l⟩
      let x := monomial k N i
      let y := monomial k N j
      let z := monomial k N l
      have hxy := (Specs.LieNotes.Quantum.Coproduct.tensorReduce_tmul e x y).trans
        (congrArg₂ (TensorProduct.tmul (A k M)) (reduce_monomial e i) (reduce_monomial e j))
      exact (reduce_left_tmul e (x ⊗ₜ[A k N] y) z).trans
        (congrArg₂ (TensorProduct.tmul (A k M)) hxy (reduce_monomial e l))
    · rcases i with ⟨i, j, l⟩
      let x := monomial k N i
      let y := monomial k N j
      let z := monomial k N l
      have hyz := (Specs.LieNotes.Quantum.Coproduct.tensorReduce_tmul e y z).trans
        (congrArg₂ (TensorProduct.tmul (A k M)) (reduce_monomial e j) (reduce_monomial e l))
      exact (reduce_right_tmul e x (y ⊗ₜ[A k N] z)).trans
        (congrArg₂ (TensorProduct.tmul (A k M)) (reduce_monomial e i) hyz)

private theorem reduce_smul {p : TensorPower} {M N : Level} (e : M ≤ N)
    (a : A k N) (x : AtLevel k p N) :
    reduce p e (a • x) = Truncations.reduce e a • reduce p e x := by
  simp only [Algebra.smul_def, map_mul, reduce_scalar]

private theorem repr_reduce {p : TensorPower}
    (b : ∀ N : Level, Module.Basis (Index p) (A k N) (AtLevel k p N))
    (hb : ∀ N i, b N i = basisVector k p N i) {M N : Level} (e : M ≤ N)
    (x : AtLevel k p N) (i : Index p) :
    (b M).repr (reduce p e x) i = Truncations.reduce e ((b N).repr x i) := by
  classical
  have hb' (j : Index p) : reduce p e (b N j) = b M j := by
    rw [hb, hb]
    exact (compatible_bases k p).2 M N e j
  let r : (Index p →₀ A k N) →+ (Index p →₀ A k M) :=
    Finsupp.mapRange.addMonoidHom (Truncations.reduce (R := k) e).toAddMonoidHom
  have h (a : Index p →₀ A k N) : (b M).repr (reduce p e ((b N).repr.symm a)) = r a := by
    induction a using Finsupp.induction_linear with
    | zero => simp
    | add a c ha hc => simp only [map_add, ha, hc]
    | single j a =>
      rw [Module.Basis.repr_symm_single, reduce_smul, hb', map_smul, Module.Basis.repr_self]
      ext l
      simp [r, Finsupp.single_apply]
  have hx := h ((b N).repr x)
  rw [LinearEquiv.symm_apply_apply] at hx
  exact DFunLike.congr_fun hx i

theorem transition_laws : TransitionLawsProp.{u} := by
  intro k _ _ p
  obtain ⟨⟨b, hb⟩, _⟩ := compatible_bases k p
  constructor
  · intro N
    ext x : 1
    apply (b N).repr.injective
    ext i
    rw [repr_reduce b hb, Truncations.reduce_refl]
    rfl
  · intro L M N d e
    ext x : 1
    apply (b L).repr.injective
    ext i
    simp only [RingHom.comp_apply, repr_reduce b hb]
    exact DFunLike.congr_fun (Truncations.reduce_comp e d) _

end Bases

section Series

omit [CharZero k] in
private def seriesOfCoeffs {ι : Type} (v : ℕ → ι →₀ k) : Series k ι :=
  HahnModule.of k ⟨v, Set.IsPWO.of_linearOrder _⟩

omit [CharZero k] in
@[simp] private theorem seriesCoeff_ofCoeffs {ι : Type} (v : ℕ → ι →₀ k) (n : ℕ) :
    seriesCoeff k n (seriesOfCoeffs v) = v n := rfl

theorem series_coefficients : SeriesCoefficientsProp.{u} := by
  intro k _ ι
  exact ⟨fun _ _ h => HahnModule.ext _ _ h, fun v => ⟨seriesOfCoeffs v, rfl⟩⟩

theorem scalar_convolution : ScalarConvolutionProp.{u} := by
  intro k _ ι f x n
  classical
  let F := HahnSeries.toPowerSeries.symm f
  let X := (HahnModule.of k).symm x
  change ((HahnModule.of k).symm (F • (show HahnModule ℕ k (ι →₀ k) from x))).coeff n = _
  rw [HahnModule.coeff_smul]
  change (∑ ab ∈ Finset.VAddAntidiagonal n _, F.coeff ab.1 • X.coeff ab.2) = _
  simp only [F, X, HahnSeries.coeff_toPowerSeries_symm]
  refine Finset.sum_subset ?_ ?_
  · intro ab hab
    exact Finset.HasAntidiagonal.mem_antidiagonal.mpr ((Finset.mem_vaddAntidiagonal n _).mp hab).2.2
  · intro ab hab hnot
    have hh := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
    by_cases ha : PowerSeries.coeff ab.1 f = 0
    · rw [ha, zero_smul]
    · have hb : seriesCoeff k ab.2 x = 0 := by
        by_contra hb
        exact hnot ((Finset.mem_vaddAntidiagonal n _).mpr ⟨ha, hb, hh⟩)
      change _ • seriesCoeff k ab.2 x = _
      rw [hb, smul_zero]

end Series

section InitialTopology

private theorem continuous_initial {X Y J : Type*} [t : TopologicalSpace X]
    {Z : J → Type*} (g : ∀ j, Y → Z j) (f : X → Y) :
    Continuous[t, ⨅ j, TopologicalSpace.induced (g j) ⊥] f ↔
      ∀ j, Continuous[t, ⊥] (g j ∘ f) := by
  rw [continuous_iInf_rng]
  simp only [continuous_induced_rng]

private theorem continuous_project (p : TensorPower) (N : Level) :
    Continuous[limitTopology k p, ⊥] (project k p N) :=
  continuous_iInf_dom (i := N) continuous_induced_dom

omit [CharZero k] in
private theorem continuous_seriesCoeff {ι : Type} (n : ℕ) :
    Continuous[seriesTopology k ι, ⊥] (seriesCoeff k (ι := ι) n) :=
  continuous_iInf_dom (i := n) continuous_induced_dom

private theorem continuous_levelwise {p q : TensorPower} (f : Limit k p → Limit k q)
    (g : ∀ N : Level, AtLevel k p N → AtLevel k q N)
    (h : ∀ N x, project k q N (f x) = g N (project k p N x)) :
    Continuous f := by
  apply (continuous_initial (fun N => project k q N) f).2
  intro N
  have he : (project k q N) ∘ f = g N ∘ project k p N := funext (h N)
  rw [he]
  letI : TopologicalSpace (AtLevel k p N) := ⊥
  letI : TopologicalSpace (AtLevel k q N) := ⊥
  exact continuous_bot.comp (continuous_project p N)

end InitialTopology

section SeriesEquivalence

omit [CharZero k] in
private def indexSeries {ι : Type} (v : Series k ι) (i : ι) : PowerSeries k :=
  PowerSeries.mk fun n => seriesCoeff k n v i

omit [CharZero k] in
@[simp] private theorem coeff_indexSeries {ι : Type} (v : Series k ι) (i : ι) (n : ℕ) :
    PowerSeries.coeff n (indexSeries v i) = seriesCoeff k n v i :=
  PowerSeries.coeff_mk _ _

omit [CharZero k] in
private theorem indexSeries_add {ι : Type} (v w : Series k ι) (i : ι) :
    indexSeries (v + w) i = indexSeries v i + indexSeries w i := by
  ext n
  simp only [map_add, coeff_indexSeries]
  rfl

omit [CharZero k] in
private theorem indexSeries_smul {ι : Type} (f : PowerSeries k) (v : Series k ι) (i : ι) :
    indexSeries (f • v) i = f * indexSeries v i := by
  ext n
  simp only [coeff_indexSeries, PowerSeries.coeff_mul, scalar_convolution k ι f v n,
    Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]

omit [CharZero k] in
private def pack {ι : Type} (N : Level) (v : Series k ι) : ι →₀ A k N := by
  classical
  refine Finsupp.onFinset (Finset.univ.biUnion fun n : Fin N => (seriesCoeff k n v).support)
    (fun i => Truncations.truncate N (indexSeries v i)) ?_
  intro i hi
  by_contra h
  apply hi
  apply Truncations.ext_of_coeff
  intro n
  rw [Truncations.coeff_truncate, coeff_indexSeries, map_zero]
  exact Finsupp.notMem_support_iff.mp (fun h' =>
    h (Finset.mem_biUnion.mpr ⟨n, Finset.mem_univ n, h'⟩))

omit [CharZero k] in
@[simp] private theorem pack_apply {ι : Type} (N : Level) (v : Series k ι) (i : ι) :
    pack N v i = Truncations.truncate N (indexSeries v i) := by
  classical
  rfl

omit [CharZero k] in
@[simp] private theorem coeff_pack {ι : Type} (N : Level) (v : Series k ι) (i : ι) (n : Fin N) :
    Truncations.coeff n (pack N v i) = seriesCoeff k n v i := by
  rw [pack_apply, Truncations.coeff_truncate, coeff_indexSeries]

variable {p : TensorPower}
variable (b : ∀ N : Level, Module.Basis (Index p) (A k N) (AtLevel k p N))

private def fromSeries (hb : ∀ N i, b N i = basisVector k p N i) :
    Series k (Index p) →ₗ[PowerSeries k] Limit k p where
  toFun v := ⟨fun N => (b N).repr.symm (pack N v), by
    intro M N e
    apply (b M).repr.injective
    ext i
    rw [repr_reduce b hb, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
      pack_apply, pack_apply]
    exact DFunLike.congr_fun (Truncations.reduce_comp_truncate e) _⟩
  map_add' v w := by
    apply project_ext
    intro N
    apply (b N).repr.injective
    change (b N).repr ((b N).repr.symm (pack N (v + w))) =
      (b N).repr ((b N).repr.symm (pack N v) + (b N).repr.symm (pack N w))
    simp only [map_add, LinearEquiv.apply_symm_apply]
    ext i
    simp only [pack_apply, Finsupp.add_apply, indexSeries_add, map_add]
  map_smul' f v := by
    apply project_ext
    intro N
    apply (b N).repr.injective
    change (b N).repr ((b N).repr.symm (pack N (f • v))) =
      (b N).repr (Truncations.truncate N f • (b N).repr.symm (pack N v))
    simp only [map_smul, LinearEquiv.apply_symm_apply]
    ext i
    simp only [pack_apply, Finsupp.smul_apply, indexSeries_smul, map_mul, smul_eq_mul]

variable {b}

@[simp] private theorem project_fromSeries (hb : ∀ N i, b N i = basisVector k p N i)
    (N : Level) (v : Series k (Index p)) :
    project k p N (fromSeries b hb v) = (b N).repr.symm (pack N v) := rfl

private def degreeLevel (n : ℕ) : Level := ⟨n + 1, by omega⟩

private def extractCoeff (b : ∀ N : Level, Module.Basis (Index p) (A k N) (AtLevel k p N))
    (n : ℕ) (x : AtLevel k p (degreeLevel n)) : Index p →₀ k :=
  (b (degreeLevel n)).repr x |>.mapRange (Truncations.coeff ⟨n, Nat.lt_succ_self n⟩)
    (map_zero _)

private theorem fromSeries_bijective (hb : ∀ N i, b N i = basisVector k p N i) :
    Function.Bijective (fromSeries b hb) := by
  constructor
  · intro v w h
    apply (series_coefficients k (Index p)).injective
    funext n
    ext i
    have hh := congrArg (fun x => project k p (degreeLevel n) x) h
    simp only [project_fromSeries, LinearEquiv.symm_apply_eq, LinearEquiv.apply_symm_apply] at hh
    have hc := congrArg (fun a : Index p →₀ A k (degreeLevel n) =>
      Truncations.coeff (⟨n, Nat.lt_succ_self n⟩ : Fin (degreeLevel n : ℕ)) (a i)) hh
    simpa only [coeff_pack] using hc
  · intro x
    refine ⟨seriesOfCoeffs (fun n => extractCoeff b n (project k p (degreeLevel n) x)), ?_⟩
    apply project_ext
    intro N
    rw [project_fromSeries, LinearEquiv.symm_apply_eq]
    ext i
    apply Truncations.ext_of_coeff
    intro n
    have hN : degreeLevel n ≤ N := n.isLt
    rw [coeff_pack, seriesCoeff_ofCoeffs]
    change Truncations.coeff (⟨n, Nat.lt_succ_self n⟩ : Fin (degreeLevel n : ℕ))
      ((b (degreeLevel n)).repr (project k p (degreeLevel n) x) i) = _
    rw [← project_reduce hN x, repr_reduce b hb, Truncations.coeff_reduce]
    rfl

private theorem coeff_fromSeries_symm (hb : ∀ N i, b N i = basisVector k p N i)
    (N : Level) (n : Fin N) (x : Limit k p) (i : Index p) :
    seriesCoeff k n ((LinearEquiv.ofBijective (fromSeries b hb) (fromSeries_bijective hb)).symm x) i =
      Truncations.coeff n ((b N).repr (project k p N x) i) := by
  let c := LinearEquiv.ofBijective (fromSeries b hb) (fromSeries_bijective hb)
  change seriesCoeff k n (c.symm x) i = _
  nth_rw 2 [← c.apply_symm_apply x]
  change _ = Truncations.coeff n ((b N).repr (project k p N (fromSeries b hb (c.symm x))) i)
  rw [project_fromSeries, LinearEquiv.apply_symm_apply, coeff_pack]

private theorem continuous_fromSeries (hb : ∀ N i, b N i = basisVector k p N i) :
    Continuous (fromSeries b hb) := by
  apply (continuous_initial (fun N => project k p N) _).2
  intro N
  letI : TopologicalSpace (Index p →₀ k) := ⊥
  letI : DiscreteTopology (Index p →₀ k) := ⟨rfl⟩
  letI : TopologicalSpace (AtLevel k p N) := ⊥
  let finitelyMany : Series k (Index p) → Fin N → Index p →₀ k :=
    fun v n => seriesCoeff k n v
  let extend : (Fin N → Index p →₀ k) → ℕ → Index p →₀ k :=
    fun v n => if hn : n < N then v ⟨n, hn⟩ else 0
  have hf : Continuous finitelyMany := continuous_pi (fun n => continuous_seriesCoeff (k := k) n)
  let build : (Fin N → Index p →₀ k) → AtLevel k p N :=
    fun v => (b N).repr.symm (pack N (seriesOfCoeffs (extend v)))
  have hb0 : Continuous build := continuous_of_discreteTopology
  have he : project k p N ∘ fromSeries b hb = build ∘ finitelyMany := by
    funext x
    change project k p N (fromSeries b hb x) = (b N).repr.symm _
    rw [project_fromSeries]
    congr 1
    ext i
    apply Truncations.ext_of_coeff
    intro n
    simp only [coeff_pack, seriesCoeff_ofCoeffs, extend, dite_true, finitelyMany, n.isLt]
  rw [he]
  exact hb0.comp hf

private theorem continuous_fromSeries_symm (hb : ∀ N i, b N i = basisVector k p N i) :
    Continuous ((LinearEquiv.ofBijective (fromSeries b hb) (fromSeries_bijective hb)).symm) := by
  apply (continuous_initial (fun n => seriesCoeff k (ι := Index p) n) _).2
  intro n
  have he :
      seriesCoeff k n ∘ (LinearEquiv.ofBijective (fromSeries b hb) (fromSeries_bijective hb)).symm =
        extractCoeff b n ∘ project k p (degreeLevel n) := by
    funext x
    ext i
    exact coeff_fromSeries_symm hb (degreeLevel n) ⟨n, Nat.lt_succ_self n⟩ x i
  rw [he]
  letI : TopologicalSpace (AtLevel k p (degreeLevel n)) := ⊥
  letI : TopologicalSpace (Index p →₀ k) := ⊥
  exact continuous_bot.comp (continuous_project p (degreeLevel n))

theorem series_description : SeriesDescriptionProp.{u} := by
  intro k _ _ p
  obtain ⟨⟨b, hb⟩, _⟩ := compatible_bases k p
  exact ⟨b, hb, (LinearEquiv.ofBijective (fromSeries b hb) (fromSeries_bijective hb)).symm,
    continuous_fromSeries_symm hb, continuous_fromSeries hb, coeff_fromSeries_symm hb⟩

end SeriesEquivalence

section Reduction

open Filter
open scoped Pointwise

omit [CharZero k] in
private theorem seriesCoeff_X_pow {ι : Type} (m n : ℕ) (v : Series k ι) :
    seriesCoeff k m ((PowerSeries.X : PowerSeries k) ^ n • v) =
      if n ≤ m then seriesCoeff k (m - n) v else 0 := by
  classical
  rw [scalar_convolution k ι]
  simp only [PowerSeries.coeff_X_pow]
  split_ifs with h
  · rw [Finset.sum_eq_single_of_mem (n, m - n)
      (Finset.HasAntidiagonal.mem_antidiagonal.mpr (Nat.add_sub_of_le h))]
    · simp
    · intro a ha hne
      have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp ha
      have hfirst : a.1 ≠ n := by
        intro he
        exact hne (Prod.ext he (by omega))
      simp [hfirst]
  · apply Finset.sum_eq_zero
    intro a ha
    have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp ha
    have hfirst : a.1 ≠ n := by omega
    simp [hfirst]

omit [CharZero k] in
private theorem series_X_injective {ι : Type} :
    Function.Injective ((PowerSeries.X : PowerSeries k) • · : Series k ι → Series k ι) := by
  intro v w h
  apply (series_coefficients k ι).injective
  funext n
  have he := congrArg (seriesCoeff k (n + 1)) h
  rw [← pow_one (PowerSeries.X : PowerSeries k)] at he
  simpa only [seriesCoeff_X_pow, ite_eq_left (by omega : 1 ≤ n + 1), Nat.add_sub_cancel] using he

omit [CharZero k] in
private theorem series_X_pow_range {ι : Type} (N : ℕ) (v : Series k ι) :
    (∃ w : Series k ι, (PowerSeries.X : PowerSeries k) ^ N • w = v) ↔
      ∀ n < N, seriesCoeff k n v = 0 := by
  constructor
  · rintro ⟨w, rfl⟩ n hn
    rw [seriesCoeff_X_pow, ite_eq_right (not_le_of_gt hn)]
  · intro h
    refine ⟨seriesOfCoeffs (fun n => seriesCoeff k (n + N) v), ?_⟩
    apply (series_coefficients k ι).injective
    funext n
    change seriesCoeff k n _ = _
    rw [seriesCoeff_X_pow]
    split_ifs with hn
    · rw [seriesCoeff_ofCoeffs, Nat.sub_add_cancel hn]
    · exact (h n (by omega)).symm

private theorem project_kernel_iff {p : TensorPower}
    (b : ∀ N : Level, Module.Basis (Index p) (A k N) (AtLevel k p N))
    (hb : ∀ N i, b N i = basisVector k p N i) (N : Level) (x : Limit k p) :
    project k p N x = 0 ↔ ∃ y : Limit k p, (PowerSeries.X : PowerSeries k) ^ (N : ℕ) • y = x := by
  obtain ⟨v, rfl⟩ := (fromSeries_bijective hb).surjective x
  have h := (fromSeries_bijective hb).injective
  rw [project_fromSeries, LinearEquiv.map_eq_zero_iff]
  constructor
  · intro hv
    have hlow : ∀ n < (N : ℕ), seriesCoeff k n v = 0 := by
      intro n hn
      ext i
      rw [← coeff_pack N v i ⟨n, hn⟩, hv, Finsupp.zero_apply, map_zero, Finsupp.zero_apply]
    obtain ⟨w, hw⟩ := (series_X_pow_range N v).mpr hlow
    exact ⟨fromSeries b hb w, (map_smul (fromSeries b hb) _ w).symm.trans (congrArg _ hw)⟩
  · rintro ⟨y, hy⟩
    obtain ⟨w, rfl⟩ := (fromSeries_bijective hb).surjective y
    have hw := (series_X_pow_range N v).mp ⟨w, h ((map_smul (fromSeries b hb) _ w).trans hy)⟩
    ext i
    apply Truncations.ext_of_coeff
    intro n
    rw [coeff_pack, hw n n.isLt, Finsupp.zero_apply, Finsupp.zero_apply, map_zero]

private theorem project_surjective {p : TensorPower}
    (b : ∀ N : Level, Module.Basis (Index p) (A k N) (AtLevel k p N))
    (hb : ∀ N i, b N i = basisVector k p N i) (N : Level) :
    Function.Surjective (project k p N) := by
  intro z
  let v : ℕ → Index p →₀ k := fun n =>
    if hn : n < N then ((b N).repr z).mapRange (Truncations.coeff ⟨n, hn⟩) (map_zero _) else 0
  refine ⟨fromSeries b hb (seriesOfCoeffs v), ?_⟩
  rw [project_fromSeries, LinearEquiv.symm_apply_eq]
  ext i
  apply Truncations.ext_of_coeff
  intro n
  simp only [coeff_pack, seriesCoeff_ofCoeffs, v, n.isLt, dite_true, Finsupp.mapRange_apply]

private theorem adic_nhds {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (x : M) :
    @nhds M (I.adicModuleTopology M) x =
      ⨅ n : ℕ, 𝓟 ((x + ·) '' (↑(I ^ n • (⊤ : Submodule R M)) : Set M)) := by
  let F := I.ringFilterBasis.moduleFilterBasis (I.adic_module_basis M)
  let B := @ModuleFilterBasis.toAddGroupFilterBasis R M _ I.adicTopology _ _ F
  have h := B.nhds_hasBasis x
  apply Filter.HasBasis.eq_iInf
  refine h.to_hasBasis ?_ ?_
  · rintro V ⟨n, rfl⟩
    exact ⟨n, trivial, Set.Subset.rfl⟩
  · intro n _
    exact ⟨_, ⟨n, rfl⟩, Set.Subset.rfl⟩

private theorem adic_eq_projectTopology {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {Z : Level → Type*} [∀ N, AddCommGroup (Z N)]
    (I : Ideal R) (f : ∀ N, M →+ Z N)
    (h : ∀ (N : Level) (x : M), f N x = 0 ↔ x ∈ I ^ (N : ℕ) • (⊤ : Submodule R M)) :
    (⨅ N : Level, TopologicalSpace.induced (f N) ⊥) = I.adicModuleTopology M := by
  rw [TopologicalSpace.ext_iff_nhds]
  intro x
  rw [nhds_iInf, adic_nhds]
  have hn (N : Level) : @nhds M (TopologicalSpace.induced (f N) ⊥) x =
      𝓟 ((x + ·) '' (↑(I ^ (N : ℕ) • (⊤ : Submodule R M)) : Set M)) := by
    letI : TopologicalSpace (Z N) := ⊥
    letI : DiscreteTopology (Z N) := ⟨rfl⟩
    rw [nhds_induced, nhds_discrete, Filter.comap_pure]
    congr 1
    ext y
    change f N y = f N x ↔ ∃ z, z ∈ I ^ (N : ℕ) • (⊤ : Submodule R M) ∧ x + z = y
    constructor
    · intro hy
      refine ⟨y - x, (h N _).mp (by rw [map_sub, hy, sub_self]), by abel⟩
    · rintro ⟨z, hz, rfl⟩
      rw [map_add, (h N z).mpr hz, add_zero]
  simp only [hn]
  apply le_antisymm
  · refine le_iInf fun n => (iInf_le _ (degreeLevel n)).trans ?_
    apply Filter.principal_mono.mpr
    apply Set.image_mono
    exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ n))
  · exact le_iInf fun n => iInf_le _ (n : ℕ)

private theorem mem_parameter_pow_smul_top {R M : Type*}
    [CommRing R] [AddCommGroup M] [Module R M] (r : R) (n : ℕ) (x : M) :
    x ∈ (Ideal.span {r}) ^ n • (⊤ : Submodule R M) ↔ ∃ y : M, r ^ n • y = x := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  simp

theorem reduction : ReductionProp.{u} := by
  intro k _ _ p
  obtain ⟨⟨b, hb⟩, _⟩ := compatible_bases k p
  let c := LinearEquiv.ofBijective (fromSeries b hb) (fromSeries_bijective hb)
  refine ⟨?_, fun N => ⟨project_surjective b hb N, project_kernel_iff b hb N⟩, ?_⟩
  · intro x y h
    apply c.symm.injective
    apply series_X_injective
    change (PowerSeries.X : PowerSeries k) • c.symm x = PowerSeries.X • c.symm y
    rw [← c.symm.map_smul, ← c.symm.map_smul]
    exact congrArg c.symm h
  · exact adic_eq_projectTopology (Ideal.span {(PowerSeries.X : PowerSeries k)})
      (fun N => (project k p N).toAddMonoidHom) fun N x =>
        (project_kernel_iff b hb N x).trans (mem_parameter_pow_smul_top _ _ _).symm

/-- The algebra reduction induced by the projection, whose kernel is the
submodule of formal-parameter multiples computed in `reduction`. -/
def levelQuotientEquiv (p : TensorPower) (N : Level) :
    (Limit k p ⧸ RingHom.ker (project k p N).toRingHom) ≃ₐ[PowerSeries k] AtLevel k p N :=
  Ideal.quotientKerAlgEquivOfSurjective ((reduction k p).2.1 N).1

@[simp] theorem levelQuotientEquiv_mk (p : TensorPower) (N : Level) (x : Limit k p) :
    levelQuotientEquiv p N (Ideal.Quotient.mk _ x) = project k p N x :=
  Ideal.quotientKerAlgEquivOfSurjective_mk _ x

omit [CharZero k] in
private theorem scalarTopology_eq :
    scalarTopology k =
      ⨅ N : Level, TopologicalSpace.induced (Truncations.truncate (R := k) N) ⊥ := by
  symm
  apply adic_eq_projectTopology (Ideal.span {(PowerSeries.X : PowerSeries k)})
    (fun N => (Truncations.truncate (R := k) N).toAddMonoidHom)
  intro N f
  rw [mem_parameter_pow_smul_top]
  exact (Truncations.truncate_eq_zero_iff N f).trans
    ⟨fun ⟨a, ha⟩ => ⟨a, ha.symm⟩, fun ⟨a, ha⟩ => ⟨a, ha.symm⟩⟩

omit [CharZero k] in
private theorem continuous_truncate (N : Level) :
    Continuous[scalarTopology k, ⊥] (Truncations.truncate (R := k) N) := by
  rw [scalarTopology_eq]
  exact continuous_iInf_dom (i := N) continuous_induced_dom

private theorem continuous_discrete_binary {X Y B C D : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → B) (g : Y → C)
    (hf : Continuous[_, ⊥] f) (hg : Continuous[_, ⊥] g) (op : B × C → D) :
    Continuous[_, ⊥] (fun x : X × Y => op (f x.1, g x.2)) := by
  letI : TopologicalSpace B := ⊥
  letI : TopologicalSpace C := ⊥
  letI : DiscreteTopology B := ⟨rfl⟩
  letI : DiscreteTopology C := ⟨rfl⟩
  letI : TopologicalSpace D := ⊥
  exact (continuous_of_discreteTopology (f := op)).comp
    ((hf.comp continuous_fst).prodMk (hg.comp continuous_snd))

theorem topological_algebras : TopologicalAlgebrasProp.{u} := by
  intro k _ _ p
  letI : TopologicalSpace (PowerSeries k) := scalarTopology k
  refine ⟨?_, ⟨?_⟩⟩
  · refine { continuous_add := ?_, continuous_mul := ?_, continuous_neg := ?_ }
    · apply (continuous_initial (fun N => project k p N) _).2
      intro N
      simpa only [Function.comp_def, map_add] using
        continuous_discrete_binary _ _ (continuous_project p N) (continuous_project p N)
          (fun z => z.1 + z.2)
    · apply (continuous_initial (fun N => project k p N) _).2
      intro N
      simpa only [Function.comp_def, map_mul] using
        continuous_discrete_binary _ _ (continuous_project p N) (continuous_project p N)
          (fun z => z.1 * z.2)
    · apply continuous_levelwise (fun x : Limit k p => -x) (fun _ x => -x)
      intro N x
      exact map_neg (project k p N) x
  · apply (continuous_initial (fun N => project k p N) _).2
    intro N
    exact continuous_discrete_binary _ _ (continuous_truncate N) (continuous_project p N)
      (fun z : A k N × AtLevel k p N => z.1 • z.2)

end Reduction

section LiftMaps

private def limitLinear {p q : TensorPower}
    (f : ∀ N : Level, AtLevel k p N →ₗ[A k N] AtLevel k q N)
    (h : ∀ (M N : Level) (e : M ≤ N) x, reduce q e (f N x) = f M (reduce p e x)) :
    Limit k p →ₗ[PowerSeries k] Limit k q where
  toFun x := ⟨fun N => f N (project k p N x), by
    intro M N e
    rw [h M N e, project_reduce e x]⟩
  map_add' x y := project_ext (fun N => (f N).map_add (project k p N x) (project k p N y))
  map_smul' r x := project_ext (fun N => (f N).map_smul (Truncations.truncate N r) (project k p N x))

private def limitAlg {p q : TensorPower}
    (f : ∀ N : Level, AtLevel k p N →ₐ[A k N] AtLevel k q N)
    (h : ∀ (M N : Level) (e : M ≤ N) x, reduce q e (f N x) = f M (reduce p e x)) :
    Limit k p →ₐ[PowerSeries k] Limit k q :=
  { limitLinear (fun N => (f N).toLinearMap) h with
    map_one' := project_ext (fun N => (f N).map_one)
    map_zero' := project_ext (fun N => (f N).map_zero)
    map_mul' x y := project_ext (fun N => (f N).map_mul (project k p N x) (project k p N y))
    commutes' r := project_ext (fun N => (f N).commutes (Truncations.truncate N r)) }

private theorem bijective_levelwise {p q : TensorPower} (f : Limit k p → Limit k q)
    (g : ∀ N : Level, AtLevel k p N → AtLevel k q N)
    (h : ∀ N x, project k q N (f x) = g N (project k p N x))
    (hn : ∀ (M N : Level) (e : M ≤ N) x, reduce q e (g N x) = g M (reduce p e x))
    (hb : ∀ N, Function.Bijective (g N)) : Function.Bijective f := by
  constructor
  · intro x y he
    apply project_ext
    intro N
    apply (hb N).injective
    rw [← h N x, ← h N y, he]
  · intro y
    have hs (N : Level) : ∃ x, g N x = project k q N y := (hb N).surjective _
    choose x hx using hs
    have hc (M N : Level) (e : M ≤ N) : reduce p e (x N) = x M := by
      apply (hb M).injective
      rw [← hn M N e, hx N, hx M, project_reduce e y]
    refine ⟨⟨x, hc⟩, project_ext ?_⟩
    intro N
    rw [h]
    exact hx N

omit [CharZero k] in
private theorem scalar_project_ext {f g : PowerSeries k}
    (h : ∀ (N : Level), Truncations.truncate N f = Truncations.truncate N g) : f = g := by
  ext n
  let j : Fin (degreeLevel n : ℕ) := ⟨n, Nat.lt_succ_self n⟩
  have hn := congrArg (Truncations.coeff j) (h (degreeLevel n))
  exact (Truncations.coeff_truncate f j).symm.trans (hn.trans (Truncations.coeff_truncate g j))

private def compatibleScalars (a : ∀ N : Level, A k N) : PowerSeries k :=
  PowerSeries.mk fun n => Truncations.coeff ⟨n, Nat.lt_succ_self n⟩ (a (degreeLevel n))

omit [CharZero k] in
private theorem truncate_compatibleScalars (a : ∀ N : Level, A k N)
    (h : ∀ (M N : Level) (e : M ≤ N), Truncations.reduce e (a N) = a M) (N : Level) :
    Truncations.truncate N (compatibleScalars a) = a N := by
  apply Truncations.ext_of_coeff
  intro n
  rw [Truncations.coeff_truncate, compatibleScalars, PowerSeries.coeff_mk]
  have he : degreeLevel n ≤ N := n.isLt
  let j : Fin (degreeLevel n : ℕ) := ⟨n, Nat.lt_succ_self n⟩
  change Truncations.coeff j (a (degreeLevel n)) = _
  rw [← h (degreeLevel n) N he]
  exact Truncations.coeff_reduce he j (a N)

private def limitCounit (f : ∀ N : Level, U k N →ₐ[A k N] A k N)
    (h : ∀ (M N : Level) (e : M ≤ N) x,
      Truncations.reduce e (f N x) = f M (reduce .single e x)) : Uh k →ₐ[PowerSeries k] PowerSeries k := by
  let c : Uh k → PowerSeries k := fun x => compatibleScalars fun N => f N (project k .single N x)
  have hc (N : Level) (x : Uh k) : Truncations.truncate N (c x) = f N (project k .single N x) :=
    truncate_compatibleScalars _ (fun M N e => (h M N e _).trans (congrArg _ (project_reduce e x))) N
  exact
    { toFun := c
      map_one' := by
        apply scalar_project_ext
        intro N
        simp only [hc, map_one]
      map_mul' := by
        intro x y
        apply scalar_project_ext
        intro N
        simp only [map_mul, hc]
      map_zero' := by
        apply scalar_project_ext
        intro N
        simp only [hc, map_zero]
      map_add' := by
        intro x y
        apply scalar_project_ext
        intro N
        simp only [map_add, hc]
      commutes' := by
        intro r
        apply scalar_project_ext
        intro N
        rw [hc]
        exact (f N).commutes (Truncations.truncate N r) }

private theorem truncate_limitCounit (f : ∀ N : Level, U k N →ₐ[A k N] A k N)
    (h : ∀ (M N : Level) (e : M ≤ N) x,
      Truncations.reduce e (f N x) = f M (reduce .single e x)) (N : Level) (x : Uh k) :
    Truncations.truncate N (limitCounit f h x) = f N (project k .single N x) :=
  truncate_compatibleScalars _ (fun M N e => (h M N e _).trans (congrArg _ (project_reduce e x))) N

end LiftMaps

section HopfLimit

open Algebra.TensorProduct (lid rid)
open Specs.LieNotes.Quantum.Coproduct (tensorReduce tensorReduce_tmul)

private theorem tensor_addHom_ext {R X Y Z : Type*} [CommSemiring R]
    [AddCommMonoid X] [AddCommMonoid Y] [AddCommMonoid Z] [Module R X] [Module R Y]
    (f g : X ⊗[R] Y →+ Z) (h : ∀ a b, f (a ⊗ₜ[R] b) = g (a ⊗ₜ[R] b)) : f = g := by
  ext x : 1
  induction x using TensorProduct.inductionOn with
  | tmul a b => exact h a b
  | add a b ha hb => rw [f.map_add, g.map_add, ha, hb]

private theorem square_natural {q : TensorPower}
    (f : ∀ N : Level, Square k N →+ AtLevel k q N)
    (h : ∀ (M N : Level) (e : M ≤ N) (x y : U k N),
      reduce q e (f N (x ⊗ₜ[A k N] y)) =
        f M (Presentation.reduce e x ⊗ₜ[A k M] Presentation.reduce e y))
    (M N : Level) (e : M ≤ N) (x : Square k N) :
    reduce q e (f N x) = f M (tensorReduce e x) := by
  let l := (reduce (k := k) q e).toAddMonoidHom.comp (f N)
  let r := (f M).comp (tensorReduce (k := k) e).toAddMonoidHom
  have ht : l = r := tensor_addHom_ext l r fun a b =>
    (h M N e a b).trans (congrArg (f M) (tensorReduce_tmul e a b)).symm
  exact DFunLike.congr_fun ht x

private theorem assocAt_tmul (N : Level) (a b c : U k N) :
    assocAt k N ((a ⊗ₜ[A k N] b) ⊗ₜ[A k N] c) = a ⊗ₜ[A k N] (b ⊗ₜ[A k N] c) :=
  rfl

set_option maxHeartbeats 550000 in
private theorem assocAt_natural (M N : Level) (e : M ≤ N) (x : LeftCube k N) :
    reduce .rightCube e (assocAt k N x) = assocAt k M (reduce .leftCube e x) := by
  let lred : LeftCube k N →+* LeftCube k M := reduce (k := k) .leftCube e
  let rred : RightCube k N →+* RightCube k M := reduce (k := k) .rightCube e
  let l := rred.toAddMonoidHom.comp (assocAt k N).toAlgHom.toAddMonoidHom
  let r := (assocAt k M).toAlgHom.toAddMonoidHom.comp lred.toAddMonoidHom
  have ht : l = r := by
    apply tensor_addHom_ext
    intro z c
    let t := ((TensorProduct.mk (A k N) (Square k N) (U k N)).flip c).toAddMonoidHom
    have hc : l.comp t = r.comp t := by
      apply tensor_addHom_ext
      intro a b
      have hl := (congrArg (reduce (k := k) .rightCube e) (assocAt_tmul N a b c)).trans
        ((reduce_right_tmul e a (b ⊗ₜ[A k N] c)).trans
          (congrArg (TensorProduct.tmul (A k M) (Presentation.reduce e a)) (tensorReduce_tmul e b c)))
      have hr := (reduce_left_tmul e (a ⊗ₜ[A k N] b) c).trans
        (congrArg (fun z : Square k M => z ⊗ₜ[A k M] Presentation.reduce e c)
          (tensorReduce_tmul e a b))
      exact hl.trans ((congrArg (assocAt k M) hr).trans
        (assocAt_tmul M (Presentation.reduce e a) (Presentation.reduce e b) (Presentation.reduce e c))).symm
    exact DFunLike.congr_fun hc z
  exact DFunLike.congr_fun ht x

private def finiteComulLeft (N : Level) (d : Specs.LieNotes.Quantum.Coproduct.TruncatedData k N) :
    Square k N →ₐ[A k N] LeftCube k N :=
  Algebra.TensorProduct.map d.comul (AlgHom.id (A k N) (U k N))

private def finiteComulRight (N : Level) (d : Specs.LieNotes.Quantum.Coproduct.TruncatedData k N) :
    Square k N →ₐ[A k N] RightCube k N :=
  Algebra.TensorProduct.map (AlgHom.id (A k N) (U k N)) d.comul

private def finiteCounitLeft (N : Level) (d : Specs.LieNotes.Quantum.Coproduct.TruncatedData k N) :
    Square k N →ₐ[A k N] U k N :=
  (lid (A k N) (U k N)).toAlgHom.comp
    (Algebra.TensorProduct.map d.counit (AlgHom.id (A k N) (U k N)))

private def finiteCounitRight (N : Level) (d : Specs.LieNotes.Quantum.Coproduct.TruncatedData k N) :
    Square k N →ₐ[A k N] U k N :=
  (rid (A k N) (A k N) (U k N)).toAlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id (A k N) (U k N)) d.counit)

private def limitAntipode
    (f : ∀ N : Level, U k N →ₐ[A k N] (U k N)ᵐᵒᵖ)
    (hf : ∀ (M N : Level) (e : M ≤ N) x,
      Presentation.reduce e (Specs.LieNotes.Quantum.Hopf.antipodeLinear (f N) x) =
        Specs.LieNotes.Quantum.Hopf.antipodeLinear (f M) (Presentation.reduce e x)) :
    Uh k →ₐ[PowerSeries k] (Uh k)ᵐᵒᵖ :=
  let g := limitLinear (p := .single) (q := .single)
    (fun N => Specs.LieNotes.Quantum.Hopf.antipodeLinear (f N)) hf
  { toFun := fun x => MulOpposite.op (g x)
    map_one' := MulOpposite.unop_injective (project_ext fun N =>
      congrArg MulOpposite.unop ((f N).map_one))
    map_zero' := by simp
    map_add' := fun x y => by simp only [map_add, MulOpposite.op_add]
    map_mul' := fun x y => MulOpposite.unop_injective (project_ext fun N =>
      congrArg MulOpposite.unop ((f N).map_mul (project k .single N x) (project k .single N y)))
    commutes' := fun r => MulOpposite.unop_injective (project_ext fun N =>
      congrArg MulOpposite.unop ((f N).commutes (Truncations.truncate N r))) }

variable (d : ∀ N : Level, Specs.LieNotes.Quantum.Coproduct.TruncatedData k N)
variable (s : ∀ N : Level, Specs.LieNotes.Quantum.Hopf.TruncatedData k N (d N))

set_option maxHeartbeats 900000 in
private def completedMaps : {D : HopfMaps k // ProjectsTo D d s} := by
  let S := fun N => Specs.LieNotes.Quantum.Hopf.antipodeLinear (s N).antipode
  have hRed (M N : Level) (e : M ≤ N) :=
    Hopf.truncated_compatibility M.property e (s N) (s M)
  have hΔ (M N : Level) (e : M ≤ N) (x : U k N) :
      tensorReduce e ((d N).comul x) = (d M).comul (Presentation.reduce e x) :=
    DFunLike.congr_fun (hRed M N e).1 x
  have hε (M N : Level) (e : M ≤ N) (x : U k N) :
      Truncations.reduce e ((d N).counit x) = (d M).counit (Presentation.reduce e x) :=
    DFunLike.congr_fun (hRed M N e).2.1 x
  have hS (M N : Level) (e : M ≤ N) (x : U k N) :
      Presentation.reduce e (S N x) = S M (Presentation.reduce e x) :=
    (hRed M N e).2.2 x
  let fΔ := limitAlg (p := .single) (q := .square) (fun N => (d N).comul) hΔ
  let fε := limitCounit (fun N => (d N).counit) hε
  let fS := limitAntipode (fun N => (s N).antipode) hS
  let ΔL := fun N => finiteComulLeft N (d N)
  let ΔR := fun N => finiteComulRight N (d N)
  let εL := fun N => finiteCounitLeft N (d N)
  let εR := fun N => finiteCounitRight N (d N)
  let SL := fun N => (S N).rTensor (U k N)
  let SR := fun N => (S N).lTensor (U k N)
  let μ := fun N => LinearMap.mul' (A k N) (U k N)
  have hΔL := square_natural (q := .leftCube) (fun N => (ΔL N).toAddMonoidHom) (by
    intro M N e x y
    change reduce .leftCube e (ΔL N (x ⊗ₜ[A k N] y)) = _
    simp only [ΔL, finiteComulLeft,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    exact (reduce_left_tmul e _ _).trans
      (congrArg (fun z : Square k M => z ⊗ₜ[A k M] Presentation.reduce e y) (hΔ M N e x)))
  have hΔR := square_natural (q := .rightCube) (fun N => (ΔR N).toAddMonoidHom) (by
    intro M N e x y
    change reduce .rightCube e (ΔR N (x ⊗ₜ[A k N] y)) = _
    simp only [ΔR, finiteComulRight,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    exact (reduce_right_tmul e _ _).trans
      (congrArg (TensorProduct.tmul (A k M) (Presentation.reduce e x)) (hΔ M N e y)))
  have hεL := square_natural (q := .single) (fun N => (εL N).toAddMonoidHom) (by
    intro M N e x y
    change reduce .single e (εL N (x ⊗ₜ[A k N] y)) = _
    simp only [εL, finiteCounitLeft, AlgHom.comp_apply,
      AlgEquiv.coe_toAlgHom, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      Algebra.TensorProduct.lid_tmul]
    exact (reduce_smul (p := .single) e _ _).trans
      (congrArg (fun a : A k M => a • Presentation.reduce e y) (hε M N e x)))
  have hεR := square_natural (q := .single) (fun N => (εR N).toAddMonoidHom) (by
    intro M N e x y
    change reduce .single e (εR N (x ⊗ₜ[A k N] y)) = _
    simp only [εR, finiteCounitRight, AlgHom.comp_apply,
      AlgEquiv.coe_toAlgHom, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      Algebra.TensorProduct.rid_tmul]
    exact (reduce_smul (p := .single) e _ _).trans
      (congrArg (fun a : A k M => a • Presentation.reduce e x) (hε M N e y)))
  have hSL := square_natural (q := .square) (fun N => (SL N).toAddMonoidHom) (by
    intro M N e x y
    change tensorReduce e (SL N (x ⊗ₜ[A k N] y)) = _
    simp only [SL, LinearMap.toAddMonoidHom_coe, LinearMap.rTensor_tmul, tensorReduce_tmul, hS])
  have hSR := square_natural (q := .square) (fun N => (SR N).toAddMonoidHom) (by
    intro M N e x y
    change tensorReduce e (SR N (x ⊗ₜ[A k N] y)) = _
    simp only [SR, LinearMap.toAddMonoidHom_coe, LinearMap.lTensor_tmul, tensorReduce_tmul, hS])
  have hμ := square_natural (q := .single) (fun N => (μ N).toAddMonoidHom) (by
    intro M N e x y
    change Presentation.reduce e (μ N (x ⊗ₜ[A k N] y)) = _
    simp only [μ, LinearMap.toAddMonoidHom_coe, LinearMap.mul'_apply, map_mul])
  let a := limitAlg (p := .leftCube) (q := .rightCube) (fun N => (assocAt k N).toAlgHom)
    assocAt_natural
  have ha : Function.Bijective a :=
    bijective_levelwise (fun x => a x) (fun N x => assocAt k N x)
      (fun _ _ => rfl) assocAt_natural (fun N => (assocAt k N).bijective)
  let D : HopfMaps k :=
    { comul := fΔ
      counit := fε
      antipode := fS
      comulLeft := limitAlg ΔL hΔL
      comulRight := limitAlg ΔR hΔR
      associate := AlgEquiv.ofBijective a ha
      counitLeft := limitAlg εL hεL
      counitRight := limitAlg εR hεR
      antipodeLeft := limitLinear SL hSL
      antipodeRight := limitLinear SR hSR
      multiply := limitLinear μ hμ }
  exact ⟨D, ⟨fun _ _ => rfl, truncate_limitCounit _ hε, fun _ _ => rfl,
    fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩⟩

set_option maxHeartbeats 850000 in
private theorem hopfIdentities {D : HopfMaps k} (h : ProjectsTo D d s) : HopfIdentities D where
  coassoc x := by
    apply project_ext
    intro N
    let l := finiteComulLeft N (d N)
    let r := finiteComulRight N (d N)
    have hl := (h.comulLeft N (D.comul x)).trans (congrArg l (h.comul N x))
    have hr := (h.comulRight N (D.comul x)).trans (congrArg r (h.comul N x))
    exact (h.associate N (D.comulLeft (D.comul x))).trans
      ((congrArg (assocAt k N) hl).trans
        ((DFunLike.congr_fun (d N).coassoc (project k .single N x)).trans hr.symm))
  left_counit x := by
    apply project_ext
    intro N
    rw [h.counitLeft, h.comul]
    let l := lid (A k N) (U k N)
    let y := project k .single N x
    exact (congrArg l (DFunLike.congr_fun (d N).left_counit y)).trans (l.apply_symm_apply y)
  right_counit x := by
    apply project_ext
    intro N
    rw [h.counitRight, h.comul]
    let r := rid (A k N) (A k N) (U k N)
    let y := project k .single N x
    exact (congrArg r (DFunLike.congr_fun (d N).right_counit y)).trans (r.apply_symm_apply y)
  left_antipode x := by
    apply project_ext
    intro N
    let m := LinearMap.mul' (A k N) (U k N)
    let a := (Specs.LieNotes.Quantum.Hopf.antipodeLinear (s N).antipode).rTensor (U k N)
    let y := project k .single N x
    have h₁ := (h.antipodeLeft N (D.comul x)).trans (congrArg a (h.comul N x))
    have h₂ := (project_algebraMap .single N (D.counit x)).trans
      (congrArg (algebraMap (A k N) (U k N)) (h.counit N x))
    exact (h.multiply N (D.antipodeLeft (D.comul x))).trans
      ((congrArg m h₁).trans ((DFunLike.congr_fun (s N).convolution.left y).trans h₂.symm))
  right_antipode x := by
    apply project_ext
    intro N
    let m := LinearMap.mul' (A k N) (U k N)
    let a := (Specs.LieNotes.Quantum.Hopf.antipodeLinear (s N).antipode).lTensor (U k N)
    let y := project k .single N x
    have h₁ := (h.antipodeRight N (D.comul x)).trans (congrArg a (h.comul N x))
    have h₂ := (project_algebraMap .single N (D.counit x)).trans
      (congrArg (algebraMap (A k N) (U k N)) (h.counit N x))
    exact (h.multiply N (D.antipodeRight (D.comul x))).trans
      ((congrArg m h₁).trans ((DFunLike.congr_fun (s N).convolution.right y).trans h₂.symm))
  antipode_bijective :=
    bijective_levelwise _ _ h.antipode
      (fun M N e => (Hopf.truncated_compatibility M.property e (s N) (s M)).2.2)
      (fun N => (s N).bijective)

private theorem continuousHopfMaps {D : HopfMaps k} (h : ProjectsTo D d s) : ContinuousHopfMaps D where
  comul := continuous_levelwise _ _ h.comul
  counit := by
    rw [scalarTopology_eq]
    apply (continuous_initial (fun N : Level => Truncations.truncate (R := k) N) _).2
    intro N
    have he : Truncations.truncate N ∘ D.counit = (d N).counit ∘ project k .single N :=
      funext (h.counit N)
    rw [he]
    letI : TopologicalSpace (U k N) := ⊥
    letI : TopologicalSpace (A k N) := ⊥
    exact continuous_bot.comp (continuous_project .single N)
  antipode := continuous_levelwise _ _ h.antipode
  comulLeft := continuous_levelwise _ _ h.comulLeft
  comulRight := continuous_levelwise _ _ h.comulRight
  associate := continuous_levelwise _ _ h.associate
  associate_inv := by
    apply continuous_levelwise (p := .rightCube) (q := .leftCube) _ (fun N => (assocAt k N).symm)
    intro N x
    apply (assocAt k N).injective
    rw [AlgEquiv.apply_symm_apply, ← h.associate, AlgEquiv.apply_symm_apply]
  counitLeft := continuous_levelwise _ (fun N x => finiteCounitLeft N (d N) x) h.counitLeft
  counitRight := continuous_levelwise _ (fun N x => finiteCounitRight N (d N) x) h.counitRight
  antipodeLeft := continuous_levelwise _ _ h.antipodeLeft
  antipodeRight := continuous_levelwise _ _ h.antipodeRight
  multiply := continuous_levelwise _ _ h.multiply

theorem completed_hopf : CompletedHopfProp.{u} := by
  intro k _ _
  have hf (N : Level) : ∃ d : Specs.LieNotes.Quantum.Coproduct.TruncatedData k N,
      Nonempty (Specs.LieNotes.Quantum.Hopf.TruncatedData k N d) :=
    Hopf.truncated_hopf k N N.property
  choose d hs using hf
  let s := fun N => Classical.choice (hs N)
  let D := completedMaps d s
  exact ⟨d, s, D.val, D.property, hopfIdentities d s D.property, continuousHopfMaps d s D.property⟩

end HopfLimit

end LieNotes.Quantum.Completion
