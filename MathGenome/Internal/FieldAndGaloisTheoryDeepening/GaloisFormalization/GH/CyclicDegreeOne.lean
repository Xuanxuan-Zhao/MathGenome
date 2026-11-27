import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.CyclicDegreeOne
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.GH.Cochains

noncomputable section

namespace GaloisFormalization.GH.CyclicDegreeOne

open scoped BigOperators

universe u v

private theorem sum_generatorDifference {C : Type u} {A : Type v}
    [Group C] [AddCommGroup A] [DistribMulAction C A] (s : C) (a : A) (n : ℕ) :
    (∑ i ∈ Finset.range n, s ^ i • (s • a - a)) = s ^ n • a - a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, smul_sub, ← mul_smul, ← pow_succ]
    abel

theorem norm_kills_differences : Specification.NormKillsDifferences.{u,v} := by
  intro C A _ _ _ _ s a ha
  obtain ⟨b, rfl⟩ := LinearMap.mem_range.mp ha
  apply LinearMap.mem_ker.mpr
  change (∑ i ∈ Finset.range (orderOf s), s ^ i • (s • b - b)) = 0
  rw [sum_generatorDifference, pow_orderOf_eq_one, one_smul, sub_self]

theorem norm_formula : Specification.NormFormula.{u,v} := by
  intro C A _ _ _ _ s hs a
  change (∑ i ∈ Finset.range (orderOf s), s ^ i • a) =
    ∑ i ∈ Finset.range (Nat.card C), s ^ i • a
  rw [orderOf_eq_card_of_zpowers_eq_top hs]

section Powers

variable {C : Type u} {A : Type v} [Group C] [AddCommGroup A] [DistribMulAction C A]

private def powerSum (s : C) (a : A) (n : ℕ) : A :=
  ∑ i ∈ Finset.range n, s ^ i • a

private theorem powerSum_add (s : C) (a : A) (m n : ℕ) :
    powerSum s a (m + n) = powerSum s a m + s ^ m • powerSum s a n := by
  simp only [powerSum, Finset.sum_range_add, Finset.smul_sum, pow_add, mul_smul]

private theorem cocycle_pow (s : C) (f : C → A)
    (hf : ∀ g h, f (g * h) = f g + g • f h) (n : ℕ) :
    f (s ^ n) = powerSum s (f s) n := by
  induction n with
  | zero =>
    have h : f 1 = f 1 + f 1 := by simpa using hf 1 1
    have hz : f 1 = 0 := add_left_cancel (h.symm.trans (add_zero _).symm)
    simpa [powerSum] using hz
  | succ n ih =>
    rw [pow_succ, hf, ih]
    simp only [powerSum, Finset.sum_range_succ]

private theorem cocycle_norm_zero (s : C) (f : C → A)
    (hf : ∀ g h, f (g * h) = f g + g • f h) : norm s (f s) = 0 := by
  change powerSum s (f s) (orderOf s) = 0
  rw [← cocycle_pow s f hf, pow_orderOf_eq_one]
  simpa [powerSum] using cocycle_pow s f hf 0

variable [Finite C]

private theorem pow_surjective {s : C} (hs : Subgroup.zpowers s = ⊤) :
    Function.Surjective (s ^ · : ℕ → C) := by
  intro g
  have hg : g ∈ Subgroup.zpowers s := by rw [hs]; exact Subgroup.mem_top _
  exact (isOfFinOrder_of_finite s).mem_powers_iff_mem_zpowers.mpr hg

private theorem cocycle_eq_of_generator {s : C} (hs : Subgroup.zpowers s = ⊤)
    {f g : C → A} (hf : ∀ x y, f (x * y) = f x + x • f y)
    (hg : ∀ x y, g (x * y) = g x + x • g y) (he : f s = g s) : f = g := by
  funext x
  obtain ⟨n, rfl⟩ := pow_surjective hs x
  rw [cocycle_pow s f hf, cocycle_pow s g hg, he]

omit [Finite C] in
private theorem powerSum_mod {s : C} {a : A} (ha : norm s a = 0) (n : ℕ) :
    powerSum s a (n % orderOf s) = powerSum s a n := by
  have hperiod (m k : ℕ) :
      powerSum s a (m + orderOf s * k) = powerSum s a m := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.mul_succ, ← Nat.add_assoc, powerSum_add, show powerSum s a (orderOf s) = 0
        from ha, smul_zero, add_zero, ih]
  calc
    powerSum s a (n % orderOf s) =
        powerSum s a (n % orderOf s + orderOf s * (n / orderOf s)) := (hperiod _ _).symm
    _ = powerSum s a n := congrArg (powerSum s a) (Nat.mod_add_div _ _)

theorem cocycle_power_sums : Specification.CocyclePowerSums.{u,v} := by
  intro C A _ _ _ _ s hs a
  constructor
  · intro ha
    classical
    let exp (g : C) : ℕ := (pow_surjective hs g).choose
    have hexp (g : C) : s ^ exp g = g := (pow_surjective hs g).choose_spec
    let f (g : C) : A := powerSum s a (exp g)
    have hf (n : ℕ) : f (s ^ n) = powerSum s a n := by
      change powerSum s a (exp (s ^ n)) = _
      rw [← powerSum_mod ha (exp (s ^ n)), ← powerSum_mod ha n,
        pow_inj_mod.mp (hexp (s ^ n))]
    have he : f s = a := by simpa [powerSum] using hf 1
    refine ⟨f, ⟨he, ?_, hf⟩, ?_⟩
    · intro x y
      obtain ⟨m, rfl⟩ := pow_surjective hs x
      obtain ⟨n, rfl⟩ := pow_surjective hs y
      rw [← pow_add, hf, hf, hf, powerSum_add]
    · intro g hg
      funext x
      obtain ⟨n, rfl⟩ := pow_surjective hs x
      exact (hg.2.2 n).trans (hf n).symm
  · rintro ⟨f, ⟨he, hf, _⟩, _⟩
    rw [← he]
    exact cocycle_norm_zero s f hf

end Powers

section Continuous

variable {C : Type u} {A : Type v} [Group C] [AddCommGroup A] [DistribMulAction C A]
  [TopologicalSpace C] [IsTopologicalGroup C] [DiscreteTopology C]
  [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul C A]

private theorem oneTuple {X : Type u} (x : Fin 1 → X) : ![x 0] = x := by
  funext i
  fin_cases i
  rfl

omit [DiscreteTopology C] in
private theorem continuousCocycle_mul (z : continuousCocycles C A 1) (g h : C) :
    z.val.val ![g * h] = z.val.val ![g] + g • z.val.val ![h] :=
  (mem_continuousCocycles_one z.val).mp z.property g h

variable (A) in
private def evaluate (s : C) :
    continuousCocycles C A 1 →ₗ[ℤ] LinearMap.ker (norm (A := A) s) :=
  ({ toFun := fun z => ⟨z.val.val ![s], cocycle_norm_zero s
      (fun g => z.val.val ![g]) (continuousCocycle_mul z)⟩
     map_zero' := rfl
     map_add' := fun _ _ => rfl } :
    continuousCocycles C A 1 →+ LinearMap.ker (norm (A := A) s)).toIntLinearMap

private def continuousCocycleOfFunction (f : C → A)
    (hf : ∀ g h, f (g * h) = f g + g • f h) : continuousCocycles C A 1 := by
  let c := cochainOne f continuous_of_discreteTopology
  exact ⟨c, (mem_continuousCocycles_one c).mpr hf⟩

variable [Finite C]

omit [DiscreteTopology C] in
private theorem evaluate_injective {s : C} (hs : Subgroup.zpowers s = ⊤) :
    Function.Injective (evaluate A s) := by
  intro z w hz
  have he : z.val.val ![s] = w.val.val ![s] := congrArg Subtype.val hz
  have h := cocycle_eq_of_generator hs (f := fun g => z.val.val ![g])
    (g := fun g => w.val.val ![g]) (continuousCocycle_mul z) (continuousCocycle_mul w) he
  apply Subtype.ext
  apply Subtype.ext
  funext x
  rw [← oneTuple x]
  exact congrFun h (x 0)

private theorem evaluate_surjective {s : C} (hs : Subgroup.zpowers s = ⊤) :
    Function.Surjective (evaluate A s) := by
  intro a
  obtain ⟨f, ⟨he, hf, _⟩, _⟩ :=
    (cocycle_power_sums C A s hs a.val).mp (LinearMap.mem_ker.mp a.property)
  exact ⟨continuousCocycleOfFunction f hf, Subtype.ext he⟩

omit [DiscreteTopology C] in
private theorem evaluation_class_eq_iff {s : C} (hs : Subgroup.zpowers s = ⊤)
    (z w : continuousCocycles C A 1) :
    continuousClass C A 1 z = continuousClass C A 1 w ↔
      (Submodule.Quotient.mk (evaluate A s z) : NormQuotient (A := A) s) =
        Submodule.Quotient.mk (evaluate A s w) := by
  rw [continuousClass_succ_eq_iff, Submodule.Quotient.eq]
  change (∃ t : continuousCochains C A 0, continuousDifferential C A 0 t = z.val - w.val) ↔
    (evaluate A s z - evaluate A s w).val ∈ LinearMap.range (generatorDifference s)
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨t, ht⟩
    use t.val Fin.elim0
    have he := congrArg (fun c : continuousCochains C A 1 => c.val ![s]) ht
    rw [differential_zero] at he
    exact he
  · rintro ⟨b, hb⟩
    let t : continuousCochains C A 0 := cochainZero b
    let dt : continuousCocycles C A 1 :=
      ⟨continuousDifferential C A 0 t, Model.continuousDifferential_sq C A 0 t⟩
    refine ⟨t, congrArg Subtype.val (evaluate_injective hs (a₁ := dt) (a₂ := z - w) ?_)⟩
    apply Subtype.ext
    rw [map_sub]
    change (continuousDifferential C A 0 t).val ![s] = _
    rw [differential_zero]
    exact hb

private theorem continuous_evaluation {s : C} (hs : Subgroup.zpowers s = ⊤) :
    ∃ e : ContinuousH C A 1 ≃+ NormQuotient (A := A) s,
      ∀ z : continuousCocycles C A 1,
        e (continuousClass C A 1 z) = Submodule.Quotient.mk (evaluate A s z) := by
  let q := (generatorDifferences (A := A) s).mkQ
  let f := q.comp (evaluate A s)
  have hf : continuousCoboundaries C A 1 ≤ LinearMap.ker f := by
    intro z hz
    apply LinearMap.mem_ker.mpr
    have h := (continuousClass_eq_iff z 0).mpr (by simpa using hz)
    have he := (evaluation_class_eq_iff hs z 0).mp h
    exact he.trans (map_zero f)
  let E := (continuousCoboundaries C A 1).liftQ f hf
  have hE (z : continuousCocycles C A 1) :
      E (continuousClass C A 1 z) = Submodule.Quotient.mk (evaluate A s z) := rfl
  have hinj : Function.Injective E := by
    intro x y hxy
    obtain ⟨z, rfl⟩ := continuousClass_surjective (G := C) (M := A) 1 x
    obtain ⟨w, rfl⟩ := continuousClass_surjective (G := C) (M := A) 1 y
    exact (evaluation_class_eq_iff hs z w).mpr (by simpa only [hE] using hxy)
  have hsurj : Function.Surjective E := by
    intro y
    obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨z, rfl⟩ := evaluate_surjective hs a
    exact ⟨continuousClass C A 1 z, hE z⟩
  exact ⟨AddEquiv.ofBijective E.toAddMonoidHom ⟨hinj, hsurj⟩, hE⟩

end Continuous

theorem evaluation_at_generator : Specification.EvaluationAtGenerator.{u,v} := by
  intro C A _ _ _ _ s hs
  let : TopologicalSpace C := ⊥
  let : DiscreteTopology C := discreteTopology_bot C
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := discreteTopology_bot A
  let R := Model.integralRepresentation.{u,v,max u v} C A
  obtain ⟨e, he⟩ := continuous_evaluation (A := A) hs
  let comparison := ordinaryCohomologyEquiv.{u,v,0} C A 1
  refine ⟨comparison.symm.trans e, ?_⟩
  intro c
  let f (g : C) : A := (c (ULift.up g)).down
  have hf (g h : C) : f (g * h) = f g + g • f h := by
    have hmul := (groupCohomology.mem_cocycles₁_iff (A := R) c.val).mp c.property
      (ULift.up g) (ULift.up h)
    exact (congrArg ULift.down hmul).trans (add_comm _ _)
  let z := continuousCocycleOfFunction f hf
  have hz : comparison (continuousClass C A 1 z) = groupCohomology.H1π R c := by
    rw [show comparison = ordinaryCohomologyEquiv.{u,v,0} C A 1 from rfl,
      ordinaryCohomologyEquiv_class]
    change groupCohomology.π R 1 (ordinaryCyclesMk.{u,v,0} C A 1 z) =
      groupCohomology.π R 1 ((groupCohomology.isoCocycles₁ R).inv c)
    congr 1
    apply (ModuleCat.mono_iff_injective (groupCohomology.iCocycles R 1)).mp inferInstance
    rw [Model.ordinaryCyclesMk_val, groupCohomology.isoCocycles₁_inv_comp_iCocycles_apply]
    rfl
  refine ⟨evaluate A s z, rfl, ?_⟩
  change e (comparison.symm (groupCohomology.H1π R c)) = _
  rw [← hz, comparison.symm_apply_apply, he]

theorem trivial_group : Specification.TrivialGroup.{u,v} := by
  intro C A _ _ _ _ s hs hcard
  have hnorm (a : A) : norm s a = a := by
    rw [norm_formula C A s hs, hcard]
    simp
  have hker (a : LinearMap.ker (norm (A := A) s)) : a.val = 0 :=
    (hnorm a.val).symm.trans (LinearMap.mem_ker.mp a.property)
  have hquot : Subsingleton (NormQuotient (A := A) s) := by
    constructor
    intro x y
    obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ x
    obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective _ y
    have hab : a = b := Subtype.ext ((hker a).trans (hker b).symm)
    rw [hab]
  obtain ⟨e, _⟩ := evaluation_at_generator C A s hs
  exact ⟨⟨fun x y => e.injective (hquot.elim _ _)⟩, hquot⟩

end GaloisFormalization.GH.CyclicDegreeOne
