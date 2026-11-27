import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.Cochains

namespace GaloisFormalization.GH

open CategoryTheory
open Model
open scoped BigOperators

universe u v w u' v' u'' v''

noncomputable section

set_option backward.isDefEq.respectTransparency false

abbrev continuousCochains := @Model.continuousCochains
abbrev differentialFormula := @Model.differentialFormula
abbrev continuousDifferential := @Model.continuousDifferential
abbrev continuousComplex := @Model.continuousComplex
abbrev continuousIncoming := @Model.continuousIncoming
abbrev continuousShortComplex := @Model.continuousShortComplex
abbrev continuousCocycles := @Model.continuousCocycles
abbrev continuousCoboundaries := @Model.continuousCoboundaries
abbrev ContinuousH := @Model.ContinuousH
abbrev continuousClass := @Model.continuousClass
abbrev integralRepresentation := @Model.integralRepresentation
abbrev liftCochain := @Model.liftCochain
abbrev cochainZero := @Model.cochainZero
abbrev cochainOne := @Model.cochainOne
abbrev cochainTwo := @Model.cochainTwo
abbrev continuousCochainMap : Specification.CochainMapType.{u,v,u',v'} :=
  @Model.continuousCochainMap.{u,v,u',v'}
abbrev continuousCocycleMap : Specification.CocycleMapType.{u,v,u',v'} :=
  @Model.continuousCocycleMap.{u,v,u',v'}
abbrev continuousCohomologyMap : Specification.CohomologyMapType.{u,v,u',v'} :=
  @Model.continuousCohomologyMap.{u,v,u',v'}
abbrev fixedCoefficients := @Model.fixedCoefficients
abbrev continuousInflation := @Model.continuousInflation
abbrev continuousRestriction := @Model.continuousRestriction
abbrev ordinaryRestrictedComplex := @Model.ordinaryRestrictedComplex
abbrev liftedContinuousComplex := @Model.liftedContinuousComplex
abbrev ordinaryCyclesMk := @Model.ordinaryCyclesMk
abbrev liftGroupHom := @Model.liftGroupHom.{u,w,u'}
abbrev liftCoefficientMap := @Model.liftCoefficientMap.{u,v,w,u',v'}

abbrev ContinuousMulH := @Model.ContinuousMulH
abbrev continuousMulClass := @Model.continuousMulClass

section LowDegree

variable {G : Type u} {M : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem contractNth_last {n : ℕ} (x : Fin (n + 1) → G) :
    Fin.contractNth (Fin.last n) (· * ·) x = Fin.init x := by
  funext i
  exact Fin.contractNth_apply_of_lt _ _ _ _ i.isLt

omit [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace M] [DiscreteTopology M] in
theorem differentialFormula_expanded (n : ℕ) (f : (Fin n → G) → M)
    (x : Fin (n + 1) → G) :
    differentialFormula G M n f x =
      x 0 • f (fun i => x i.succ) +
        (∑ j : Fin n, (-1 : ℤ) ^ (j.val + 1) • f (Fin.contractNth j.castSucc (· * ·) x)) +
        (-1 : ℤ) ^ (n + 1) • f (Fin.init x) := by
  rw [differentialFormula, Model.differentialFormula, Fin.sum_univ_castSucc, contractNth_last, ← add_assoc]
  rfl

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem vec_one (x : Fin 1 → G) : ![x 0] = x :=
  funext fun i => by rw [Subsingleton.elim i 0]; rfl

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem vec_two (x : Fin 2 → G) : ![x 0, x 1] = x := by
  funext i
  fin_cases i <;> rfl

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem vec_three (x : Fin 3 → G) : ![x 0, x 1, x 2] = x := by
  funext i
  fin_cases i <;> rfl

theorem differential_zero (c : continuousCochains G M 0) (g : G) :
    (continuousDifferential G M 0 c).val ![g] =
      g • c.val Fin.elim0 - c.val Fin.elim0 := by
  rw [continuousDifferential_apply]
  have h (x : Fin 0 → G) : c.val x = c.val Fin.elim0 := congrArg c.val (Subsingleton.elim _ _)
  simp [Model.differentialFormula, h, sub_eq_add_neg]

@[simp] theorem differential_cochainZero (a : M) (g : G) :
    (continuousDifferential G M 0 (cochainZero a)).val ![g] = g • a - a :=
  differential_zero (cochainZero a) g

theorem differential_one (c : continuousCochains G M 1) (g h : G) :
    (continuousDifferential G M 1 c).val ![g, h] =
      c.val ![g] + g • c.val ![h] - c.val ![g * h] := by
  rw [continuousDifferential_apply, Model.differentialFormula, Fin.sum_univ_two]
  rw [← vec_one (fun i : Fin 1 => (![(g : G), h] : Fin 2 → G) i.succ)]
  rw [← vec_one (Fin.contractNth (0 : Fin 2) (· * ·) (![g, h] : Fin 2 → G)),
      ← vec_one (Fin.contractNth (1 : Fin 2) (· * ·) (![g, h] : Fin 2 → G))]
  change g • c.val ![h] + ((-1 : ℤ) ^ (0 + 1) • c.val ![g * h] +
    (-1 : ℤ) ^ (1 + 1) • c.val ![g]) = _
  simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]

theorem differential_two (c : continuousCochains G M 2) (g h k : G) :
    (continuousDifferential G M 2 c).val ![g, h, k] =
      g • c.val ![h, k] - c.val ![g * h, k] + c.val ![g, h * k] - c.val ![g, h] := by
  rw [continuousDifferential_apply, Model.differentialFormula, Fin.sum_univ_three]
  rw [← vec_two (fun i : Fin 2 => (![g, h, k] : Fin 3 → G) i.succ),
      ← vec_two (Fin.contractNth (0 : Fin 3) (· * ·) (![g, h, k] : Fin 3 → G)),
      ← vec_two (Fin.contractNth (1 : Fin 3) (· * ·) (![g, h, k] : Fin 3 → G)),
      ← vec_two (Fin.contractNth (2 : Fin 3) (· * ·) (![g, h, k] : Fin 3 → G))]
  change g • c.val ![h, k] + ((-1 : ℤ) ^ (0 + 1) • c.val ![g * h, k] +
    (-1 : ℤ) ^ (1 + 1) • c.val ![g, h * k] +
    (-1 : ℤ) ^ (2 + 1) • c.val ![g, h]) = _
  simp [sub_eq_add_neg, add_comm, add_left_comm, pow_succ' (-1 : ℤ) 2]

theorem mem_continuousCocycles_zero (c : continuousCochains G M 0) :
    c ∈ continuousCocycles G M 0 ↔ ∀ g : G, g • c.val Fin.elim0 = c.val Fin.elim0 := by
  change continuousDifferential G M 0 c = 0 ↔ _
  constructor
  · intro hc g
    have h := congrArg (fun z : continuousCochains G M 1 => z.val ![g]) hc
    exact sub_eq_zero.mp ((differential_zero c g).symm.trans h)
  · intro hc
    apply Subtype.ext
    funext x
    rw [← vec_one x]
    exact (differential_zero c (x 0)).trans (sub_eq_zero.mpr (hc _))

theorem mem_continuousCocycles_one (c : continuousCochains G M 1) :
    c ∈ continuousCocycles G M 1 ↔
      ∀ g h : G, c.val ![g * h] = c.val ![g] + g • c.val ![h] := by
  change continuousDifferential G M 1 c = 0 ↔ _
  constructor
  · intro hc g h
    have he := congrArg (fun z : continuousCochains G M 2 => z.val ![g,h]) hc
    exact (sub_eq_zero.mp ((differential_one c g h).symm.trans he)).symm
  · intro hc
    apply Subtype.ext
    funext x
    rw [← vec_two x]
    exact (differential_one c (x 0) (x 1)).trans (sub_eq_zero.mpr (hc _ _).symm)

theorem mem_continuousCocycles_two (c : continuousCochains G M 2) :
    c ∈ continuousCocycles G M 2 ↔ ∀ g h k : G,
      c.val ![g,h] + c.val ![g*h,k] = g • c.val ![h,k] + c.val ![g,h*k] := by
  change continuousDifferential G M 2 c = 0 ↔ _
  have form (g h k : G) : (continuousDifferential G M 2 c).val ![g,h,k] =
      (g • c.val ![h,k] + c.val ![g,h*k]) - (c.val ![g,h] + c.val ![g*h,k]) := by
    rw [differential_two]
    abel
  constructor
  · intro hc g h k
    have he := congrArg (fun z : continuousCochains G M 3 => z.val ![g,h,k]) hc
    exact (sub_eq_zero.mp ((form g h k).symm.trans he)).symm
  · intro hc
    apply Subtype.ext
    funext x
    rw [← vec_three x]
    exact (form (x 0) (x 1) (x 2)).trans (sub_eq_zero.mpr (hc _ _ _).symm)

theorem continuousClass_surjective (n : ℕ) :
    Function.Surjective (continuousClass G M n) :=
  Submodule.mkQ_surjective _

theorem continuousClass_eq_iff {n : ℕ} (a b : continuousCocycles G M n) :
    continuousClass G M n a = continuousClass G M n b ↔ a - b ∈ continuousCoboundaries G M n :=
  Submodule.Quotient.eq _

theorem continuousClass_zero_eq_iff (a b : continuousCocycles G M 0) :
    continuousClass G M 0 a = continuousClass G M 0 b ↔ a = b := by
  rw [continuousClass_eq_iff]
  change a - b ∈ Model.continuousCoboundaries G M 0 ↔ _
  rw [Model.continuousCoboundaries_zero, Submodule.mem_bot]
  exact sub_eq_zero

theorem continuousClass_succ_eq_iff {n : ℕ} (a b : continuousCocycles G M (n + 1)) :
    continuousClass G M (n + 1) a = continuousClass G M (n + 1) b ↔
      ∃ t : continuousCochains G M n, continuousDifferential G M n t = a.val - b.val := by
  rw [continuousClass_eq_iff]
  change (∃ t, _ = a - b) ↔ _
  exact ⟨fun ⟨t, ht⟩ => ⟨t, congrArg Subtype.val ht⟩,
    fun ⟨t, ht⟩ => ⟨t, Subtype.ext ht⟩⟩

end LowDegree

section Functoriality

variable {G : Type u} {M : Type v} {H : Type u'} {N : Type v'}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
  [DistribMulAction G M] [ContinuousSMul G M] [DistribMulAction H N] [ContinuousSMul H N]

omit [IsTopologicalGroup G] [DistribMulAction G M] [ContinuousSMul G M] in
@[simp] theorem continuousCochainMap_id (n : ℕ) :
    continuousCochainMap (MonoidHom.id G) continuous_id (AddMonoidHom.id M) n =
      LinearMap.id := rfl

@[simp] theorem continuousCohomologyMap_id (n : ℕ) :
    continuousCohomologyMap (MonoidHom.id G) continuous_id (AddMonoidHom.id M)
      (fun _ _ => rfl) n = LinearMap.id := by
  apply LinearMap.ext
  intro a
  obtain ⟨c, rfl⟩ := continuousClass_surjective n a
  rfl

variable {J : Type u''} {P : Type v''}
  [Group J] [TopologicalSpace J] [IsTopologicalGroup J]
  [AddCommGroup P] [TopologicalSpace P] [DiscreteTopology P]
  [DistribMulAction J P] [ContinuousSMul J P]

omit [IsTopologicalGroup G] [IsTopologicalGroup H] [IsTopologicalGroup J]
  [DistribMulAction G M] [ContinuousSMul G M] [DistribMulAction H N] [ContinuousSMul H N]
  [DistribMulAction J P] [ContinuousSMul J P] in
theorem continuousCochainMap_comp (φ : H →* G) (hφ : Continuous φ) (f : M →+ N)
    (ψ : J →* H) (hψ : Continuous ψ) (g : N →+ P) (n : ℕ) :
    continuousCochainMap (φ.comp ψ) (hφ.comp hψ) (g.comp f) n =
      (continuousCochainMap ψ hψ g n).comp (continuousCochainMap φ hφ f n) := rfl

theorem continuousCohomologyMap_comp (φ : H →* G) (hφ : Continuous φ) (f : M →+ N)
    (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m)
    (ψ : J →* H) (hψ : Continuous ψ) (g : N →+ P)
    (hg : ∀ (j : J) (a : N), g (ψ j • a) = j • g a) (n : ℕ) :
    continuousCohomologyMap (φ.comp ψ) (hφ.comp hψ) (g.comp f)
      (fun j m => by change g (f (φ (ψ j) • m)) = j • g (f m); rw [hf, hg]) n =
      (continuousCohomologyMap ψ hψ g hg n).comp (continuousCohomologyMap φ hφ f hf n) := by
  apply LinearMap.ext
  intro a
  obtain ⟨c, rfl⟩ := continuousClass_surjective n a
  rfl

end Functoriality

section Fixed

variable (G : Type u) (M : Type v) [Group G] [AddCommGroup M] [DistribMulAction G M]
  [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace M]
  [DiscreteTopology M] [ContinuousSMul G M]

/-- Evaluation at the empty tuple identifies degree zero with the fixed elements. -/
def continuousHZeroEquiv : ContinuousH G M 0 ≃ₗ[ℤ] fixedCoefficients G M ⊤ :=
  (Submodule.quotEquivOfEqBot _ (continuousCoboundaries_zero G M)).trans
    (({ toFun := fun c => ⟨c.val.val Fin.elim0, fun g =>
          (mem_continuousCocycles_zero c.val).mp c.property g⟩
        invFun := fun a => ⟨cochainZero a.val, (mem_continuousCocycles_zero _).mpr
          (fun g => a.property ⟨g, Subgroup.mem_top g⟩)⟩
        left_inv := fun c => Subtype.ext (Subtype.ext (funext fun _ =>
          congrArg c.val.val (Subsingleton.elim _ _)))
        right_inv := fun _ => Subtype.ext rfl
        map_add' := fun _ _ => rfl } :
      continuousCocycles G M 0 ≃+ fixedCoefficients G M ⊤).toIntLinearEquiv)

@[simp] theorem continuousHZeroEquiv_class (c : continuousCocycles G M 0) :
    (continuousHZeroEquiv G M (continuousClass G M 0 c)).val = c.val.val Fin.elim0 := rfl

theorem continuousInflation_class (U : Subgroup G) [U.Normal] (n : ℕ)
    (c : continuousCocycles (G ⧸ U) (fixedCoefficients G M U) n) :
    ∃ a : continuousCocycles G M n,
      (∀ x : Fin n → G, a.val.val x = (c.val.val fun i => QuotientGroup.mk' U (x i)).val) ∧
      continuousInflation G M U n (continuousClass (G ⧸ U) (fixedCoefficients G M U) n c) =
        continuousClass G M n a :=
  ⟨continuousCocycleMap (QuotientGroup.mk' U) QuotientGroup.continuous_mk
    (fixedCoefficients G M U).subtype.toAddMonoidHom (quotientFixedAction_mk G M U) n c,
    fun _ => rfl, rfl⟩

end Fixed

section Categorical

variable (G : Type u) (M : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M]

@[simp] theorem continuousComplex_d (n : ℕ) :
    (continuousComplex G M).d n (n + 1) = ModuleCat.ofHom (continuousDifferential G M n) :=
  CochainComplex.of_d (fun k => ModuleCat.of ℤ (continuousCochains G M k))
    (fun k => ModuleCat.ofHom (continuousDifferential G M k)) n

private theorem prev_degree (n : ℕ) : (ComplexShape.up ℕ).prev n = n.pred := by
  cases n <;> simp

/-- The concrete short complex computes the homology of the full cochain complex. -/
def continuousShortComplexIso (n : ℕ) :
    (continuousShortComplex G M n) ≅ (continuousComplex G M).sc n := by
  let K := continuousComplex G M
  refine (ShortComplex.isoMk (S₂ := K.sc' n.pred n (n + 1))
    (Iso.refl (K.X n.pred)) (Iso.refl (K.X n))
    (Iso.refl (K.X (n + 1))) ?_ ?_) ≪≫
      (K.isoSc' n.pred n (n + 1) (prev_degree n) (CochainComplex.next ℕ n)).symm
  · change 𝟙 _ ≫ K.d n.pred n = ModuleCat.ofHom (continuousIncoming G M n) ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
    cases n with
    | zero =>
      change K.d 0 0 = 0
      exact K.shape 0 0 (by decide)
    | succ n => exact continuousComplex_d G M n
  · change 𝟙 _ ≫ K.d n (n + 1) = ModuleCat.ofHom (continuousDifferential G M n) ≫ 𝟙 _
    simpa only [Category.id_comp, Category.comp_id] using continuousComplex_d G M n

private theorem continuousShortComplexIso_hom_τ₂ (n : ℕ) :
    (continuousShortComplexIso G M n).hom.τ₂ = 𝟙 _ := by
  simp only [continuousShortComplexIso, Iso.trans_hom, ShortComplex.comp_τ₂,
    ShortComplex.isoMk_hom_τ₂, Iso.refl_hom, Iso.symm_hom]
  rfl

/-- The categorical cocycle associated to the concrete kernel element. -/
def continuousCyclesMk (n : ℕ) (c : continuousCocycles G M n) :
    (continuousComplex G M).cycles n :=
  let S := continuousShortComplex G M n
  ShortComplex.cyclesMap (continuousShortComplexIso G M n).hom (S.moduleCatCyclesIso.inv c)

@[simp] theorem continuousCyclesMk_val (n : ℕ) (c : continuousCocycles G M n) :
    (continuousComplex G M).iCycles n (continuousCyclesMk G M n c) = c.val := by
  have h := ShortComplex.cyclesMap_i (continuousShortComplexIso G M n).hom
  have he := congr($h ((continuousShortComplex G M n).moduleCatCyclesIso.inv c))
  change (continuousComplex G M).iCycles n (continuousCyclesMk G M n c) = _ at he
  rw [he]
  rw [continuousShortComplexIso_hom_τ₂, Category.comp_id]
  exact (continuousShortComplex G M n).moduleCatCyclesIso_inv_iCycles_apply c

/-- The explicit quotient agrees with the categorical homology of the continuous complex. -/
def continuousHomologyIso (n : ℕ) :
    ModuleCat.of ℤ (ContinuousH G M n) ≅ (continuousComplex G M).homology n :=
  (continuousShortComplex G M n).moduleCatHomologyIso.symm ≪≫
    ShortComplex.homologyMapIso (continuousShortComplexIso G M n)

@[simp] theorem continuousHomologyIso_class (n : ℕ) (c : continuousCocycles G M n) :
    (continuousHomologyIso G M n).hom (continuousClass G M n c) =
      (continuousComplex G M).homologyπ n (continuousCyclesMk G M n c) := by
  let S := continuousShortComplex G M n
  have h := congr($(S.moduleCatCyclesIso_inv_π) c)
  have he := congr($(ShortComplex.homologyπ_naturality
    (continuousShortComplexIso G M n).hom) (S.moduleCatCyclesIso.inv c))
  change ShortComplex.homologyMap (continuousShortComplexIso G M n).hom
    (S.moduleCatHomologyIso.inv (continuousClass G M n c)) = _
  change S.homologyπ (S.moduleCatCyclesIso.inv c) =
    S.moduleCatHomologyIso.inv (continuousClass G M n c) at h
  rw [← h]
  exact he

variable {G M} {H : Type u} {N : Type v}
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
  [DistribMulAction H N] [ContinuousSMul H N]

/-- The chain map underlying continuous cohomology functoriality. -/
def continuousComplexMap (φ : H →* G) (hφ : Continuous φ) (f : M →+ N)
    (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m) :
    continuousComplex G M ⟶ continuousComplex H N :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (continuousCochainMap φ hφ f n)) fun n => by
    rw [continuousComplex_d, continuousComplex_d]
    exact ModuleCat.hom_ext (LinearMap.ext fun c => (continuousCochainMap_d φ hφ f hf n c).symm)

theorem continuousHomologyIso_map (φ : H →* G) (hφ : Continuous φ) (f : M →+ N)
    (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m) (n : ℕ)
    (a : ContinuousH G M n) :
    (continuousHomologyIso H N n).hom (continuousCohomologyMap φ hφ f hf n a) =
      HomologicalComplex.homologyMap (continuousComplexMap φ hφ f hf) n
        ((continuousHomologyIso G M n).hom a) := by
  obtain ⟨c, rfl⟩ := continuousClass_surjective n a
  rw [continuousCohomologyMap_class]
  let F := continuousComplexMap φ hφ f hf
  calc
    _ = (continuousComplex H N).homologyπ n
      (continuousCyclesMk H N n (continuousCocycleMap φ hφ f hf n c)) :=
        continuousHomologyIso_class H N n _
    _ = (continuousComplex H N).homologyπ n
      (HomologicalComplex.cyclesMap F n (continuousCyclesMk G M n c)) := ?_
    _ = _ := by
      have h := congr($(HomologicalComplex.homologyπ_naturality F n) (continuousCyclesMk G M n c))
      exact h.symm.trans (congrArg (HomologicalComplex.homologyMap F n)
        (continuousHomologyIso_class G M n c).symm)
  congr 1
  apply (ModuleCat.mono_iff_injective ((continuousComplex H N).iCycles n)).mp inferInstance
  rw [continuousCyclesMk_val]
  have he := congr($(HomologicalComplex.cyclesMap_i F n) (continuousCyclesMk G M n c))
  change (continuousComplex H N).iCycles n
    (HomologicalComplex.cyclesMap F n (continuousCyclesMk G M n c)) =
      F.f n ((continuousComplex G M).iCycles n (continuousCyclesMk G M n c)) at he
  rw [he, continuousCyclesMk_val]
  rfl

end Categorical

section Multiplicative

variable {G : Type u} {A : Type v}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [MulDistribMulAction G A] [ContinuousSMul G A]

theorem multiplicativeCoboundary (b : A) (g : G) :
    ((continuousDifferential G (Additive A) 0
      (cochainZero (Additive.ofMul b))).val ![g]).toMul = b⁻¹ * (g • b) := by
  rw [differential_cochainZero]
  change (g • b) / b = _
  rw [div_eq_mul_inv, mul_comm]

theorem multiplicativeCocycle_iff (c : G → A) (hc : Continuous c) :
    cochainOne (fun g => Additive.ofMul (c g)) (continuous_ofMul.comp hc) ∈
      continuousCocycles G (Additive A) 1 ↔
    ∀ g h : G, c (g * h) = c g * (g • c h) := by
  rw [mem_continuousCocycles_one]
  rfl

/-- In multiplicative notation the additive quotient relation is the
change of cocycle by a single coefficient element. -/
theorem multiplicativeClass_eq_iff (c c' : continuousCocycles G (Additive A) 1) :
    continuousClass G (Additive A) 1 c' = continuousClass G (Additive A) 1 c ↔
      ∃ b : A, ∀ g : G,
        (c'.val.val ![g]).toMul = b⁻¹ * (c.val.val ![g]).toMul * (g • b) := by
  rw [continuousClass_succ_eq_iff]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨(t.val Fin.elim0).toMul, fun g => ?_⟩
    let b := (t.val Fin.elim0).toMul
    have he := congrArg (fun z : continuousCochains G (Additive A) 1 => z.val ![g]) ht
    change (continuousDifferential G (Additive A) 0 t).val ![g] =
      c'.val.val ![g] - c.val.val ![g] at he
    rw [differential_zero] at he
    have hm : (g • b) / b = (c'.val.val ![g]).toMul / (c.val.val ![g]).toMul :=
      congrArg Additive.toMul he
    calc
      _ = ((c'.val.val ![g]).toMul / (c.val.val ![g]).toMul) * (c.val.val ![g]).toMul :=
        (div_mul_cancel _ _).symm
      _ = _ := by rw [← hm, div_eq_mul_inv]; ac_rfl
  · rintro ⟨b, hb⟩
    refine ⟨cochainZero (Additive.ofMul b), Subtype.ext (funext fun x => ?_)⟩
    rw [← vec_one x]
    change (continuousDifferential G (Additive A) 0 (cochainZero (Additive.ofMul b))).val
      ![x 0] = c'.val.val ![x 0] - c.val.val ![x 0]
    rw [differential_cochainZero]
    change (x 0 • b) / b = (c'.val.val ![x 0]).toMul / (c.val.val ![x 0]).toMul
    rw [hb, mul_comm (b⁻¹) _, mul_assoc, mul_comm ((c.val.val ![x 0]).toMul) _,
      mul_div_cancel_right, div_eq_mul_inv, mul_comm]

end Multiplicative

section ChangeOfUniverse

private theorem mapHomologyIso_π {C D : Type*} [Category* C] [Category* D]
    [Limits.HasZeroMorphisms C] [Limits.HasZeroMorphisms D] (F : C ⥤ D)
    [F.PreservesZeroMorphisms] (S : ShortComplex C) [S.HasHomology] [(S.map F).HasHomology]
    [F.PreservesLeftHomologyOf S] :
    (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
      (S.mapCyclesIso F).hom ≫ F.map S.homologyπ := by
  let L := S.homologyData.left
  change (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
    (S.mapCyclesIso F).hom ≫ F.map S.homologyπ
  rw [L.mapHomologyIso_eq, L.mapCyclesIso_eq]
  simp only [Iso.trans_hom, Category.assoc, ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom_assoc,
    Functor.mapIso_hom, Iso.symm_hom]
  change (L.map F).cyclesIso.hom ≫ F.map L.π ≫ F.map L.homologyIso.inv =
    (L.map F).cyclesIso.hom ≫ F.map L.cyclesIso.inv ≫ F.map S.homologyπ
  rw [← F.map_comp, ← F.map_comp, L.π_comp_homologyIso_inv]

private theorem mapHomologyIso_inv_π {C D : Type*} [Category* C] [Category* D]
    [Limits.HasZeroMorphisms C] [Limits.HasZeroMorphisms D] (F : C ⥤ D)
    [F.PreservesZeroMorphisms] (S : ShortComplex C) [S.HasHomology] [(S.map F).HasHomology]
    [F.PreservesLeftHomologyOf S] :
    F.map S.homologyπ ≫ (S.mapHomologyIso F).inv =
      (S.mapCyclesIso F).inv ≫ (S.map F).homologyπ := by
  apply (cancel_mono (S.mapHomologyIso F).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    mapHomologyIso_π, Iso.inv_hom_id_assoc]

private theorem mapCyclesIso_inv_i {C D : Type*} [Category* C] [Category* D]
    [Limits.HasZeroMorphisms C] [Limits.HasZeroMorphisms D] (F : C ⥤ D)
    [F.PreservesZeroMorphisms] (S : ShortComplex C) [S.HasLeftHomology]
    [F.PreservesLeftHomologyOf S] :
    (S.mapCyclesIso F).inv ≫ (S.map F).iCycles = F.map S.iCycles := by
  rw [← S.mapCyclesIso_hom_iCycles F, Iso.inv_hom_id_assoc]

end ChangeOfUniverse

section Discrete

variable (G : Type u) (M : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [DiscreteTopology G] [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M]

/-- When the group is discrete, every ordinary cochain is continuous. -/
def ordinaryCochainEquiv (n : ℕ) :
    (liftedContinuousComplex.{u,v,w} G M).X n ≃ₗ[ℤ]
      (ordinaryRestrictedComplex.{u,v,w} G M).X n :=
  ({ toFun := fun c => liftCochain.{u,v,max u v w} G M n c.down.val
     invFun := fun f => ⟨⟨fun x => (f (fun i => ULift.up (x i))).down,
       continuous_of_discreteTopology⟩⟩
     left_inv := fun _ => rfl
     right_inv := fun _ => rfl
     map_add' := fun _ _ => rfl } :
    (liftedContinuousComplex.{u,v,w} G M).X n ≃+
      (ordinaryRestrictedComplex.{u,v,w} G M).X n).toIntLinearEquiv

/-- Forgetting the continuity proof is an isomorphism of cochain complexes for a discrete group. -/
def ordinaryComplexIso : liftedContinuousComplex.{u,v,w} G M ≅
    ordinaryRestrictedComplex.{u,v,w} G M :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (ordinaryCochainEquiv.{u,v,w} G M n).toModuleIso)
    (by
      rintro i j (h : i + 1 = j)
      subst j
      change _ ≫ restrictIntegral.{max u v w}.map ((ordinaryIntegralComplex.{u,v,w} G M).d i (i + 1)) =
        (ModuleCat.uliftFunctor.{w,max u v} ℤ).map ((continuousComplex G M).d i (i + 1)) ≫ _
      rw [continuousComplex_d, groupCohomology.inhomogeneousCochains.d_def]
      exact ModuleCat.hom_ext (LinearMap.ext fun c =>
        ordinaryDifferential_lift.{u,v,w} G M i c.down.val))

@[simp] theorem ordinaryComplexIso_hom_apply (n : ℕ) (c : continuousCochains G M n)
    (x : Fin n → ULift.{max u v w} G) :
    ((ordinaryComplexIso.{u,v,w} G M).hom.f n (ULift.up c) x).down =
      c.val (fun i => (x i).down) := rfl

/-- The canonical continuous-to-ordinary comparison, in a chosen ambient universe. -/
def ordinaryCohomologyEquiv (n : ℕ) :
    ContinuousH G M n ≃+ groupCohomology (integralRepresentation.{u,v,max u v w} G M) n :=
  (continuousHomologyIso G M n).toLinearEquiv.toAddEquiv.trans <|
    ({ toFun := ULift.up
       invFun := ULift.down
       left_inv := fun _ => rfl
       right_inv := fun _ => rfl
       map_add' := fun _ _ => rfl } :
      (continuousComplex G M).homology n ≃+ ULift.{w} ((continuousComplex G M).homology n)).trans <|
    ((((continuousComplex G M).sc n).mapHomologyIso (ModuleCat.uliftFunctor.{w,max u v} ℤ)).symm ≪≫
      HomologicalComplex.homologyMapIso (ordinaryComplexIso.{u,v,w} G M) n ≪≫
      ((ordinaryIntegralComplex.{u,v,w} G M).sc n).mapHomologyIso
        restrictIntegral.{max u v w}).toLinearEquiv.toAddEquiv

private theorem ordinaryCycles_compare (n : ℕ) (c : continuousCocycles G M n) :
    let S := (ordinaryIntegralComplex.{u,v,w} G M).sc n
    let T := (continuousComplex G M).sc n
    let F := restrictIntegral.{max u v w}
    let L := ModuleCat.uliftFunctor.{w,max u v} ℤ
    let z := (T.mapCyclesIso L).inv (ULift.up (continuousCyclesMk G M n c))
    let e := ordinaryComplexIso.{u,v,w} G M
    (S.mapCyclesIso F).hom (HomologicalComplex.cyclesMap e.hom n z) =
      ordinaryCyclesMk.{u,v,w} G M n c := by
  dsimp only
  let S := (ordinaryIntegralComplex.{u,v,w} G M).sc n
  let T := (continuousComplex G M).sc n
  let F := restrictIntegral.{max u v w}
  let L := ModuleCat.uliftFunctor.{w,max u v} ℤ
  let z := (T.mapCyclesIso L).inv (ULift.up (continuousCyclesMk G M n c))
  let e := ordinaryComplexIso.{u,v,w} G M
  let t := HomologicalComplex.cyclesMap e.hom n z
  apply (ModuleCat.mono_iff_injective (F.map S.iCycles)).mp inferInstance
  have hi : (liftedContinuousComplex.{u,v,w} G M).iCycles n z =
      ULift.up ((continuousComplex G M).iCycles n (continuousCyclesMk G M n c)) :=
    congr($(mapCyclesIso_inv_i L T) (ULift.up (continuousCyclesMk G M n c)))
  calc
    F.map S.iCycles ((S.mapCyclesIso F).hom t) =
        (ordinaryRestrictedComplex.{u,v,w} G M).iCycles n t :=
      congr($(S.mapCyclesIso_hom_iCycles F) t)
    _ = e.hom.f n ((liftedContinuousComplex.{u,v,w} G M).iCycles n z) :=
      congr($(HomologicalComplex.cyclesMap_i e.hom n) z)
    _ = e.hom.f n (ULift.up c.val) := congrArg (e.hom.f n)
      (hi.trans (congrArg ULift.up (continuousCyclesMk_val G M n c)))
    _ = F.map S.iCycles (ordinaryCyclesMk.{u,v,w} G M n c) :=
      (ordinaryCyclesMk_val.{u,v,w} G M n c).symm

@[simp] theorem ordinaryCohomologyEquiv_class (n : ℕ) (c : continuousCocycles G M n) :
    ordinaryCohomologyEquiv.{u,v,w} G M n (continuousClass G M n c) =
      groupCohomology.π (integralRepresentation.{u,v,max u v w} G M) n
        (ordinaryCyclesMk.{u,v,w} G M n c) := by
  let S := (ordinaryIntegralComplex.{u,v,w} G M).sc n
  let T := (continuousComplex G M).sc n
  let F := restrictIntegral.{max u v w}
  let L := ModuleCat.uliftFunctor.{w,max u v} ℤ
  let c₀ := continuousCyclesMk G M n c
  let z := (T.mapCyclesIso L).inv (ULift.up c₀)
  let e := ordinaryComplexIso.{u,v,w} G M
  let t := HomologicalComplex.cyclesMap e.hom n z
  change (S.mapHomologyIso F).hom (HomologicalComplex.homologyMap e.hom n
    ((T.mapHomologyIso L).inv (ULift.up ((continuousHomologyIso G M n).hom
      (continuousClass G M n c))))) = _
  have h₁ := continuousHomologyIso_class G M n c
  have h₂ : (T.mapHomologyIso L).inv (ULift.up ((continuousComplex G M).homologyπ n c₀)) =
      (liftedContinuousComplex.{u,v,w} G M).homologyπ n z :=
    congr($(mapHomologyIso_inv_π L T) (ULift.up c₀))
  have h₃ : HomologicalComplex.homologyMap e.hom n
      ((liftedContinuousComplex.{u,v,w} G M).homologyπ n z) =
      (ordinaryRestrictedComplex.{u,v,w} G M).homologyπ n t :=
    congr($(HomologicalComplex.homologyπ_naturality e.hom n) z)
  have h₄ : (S.mapHomologyIso F).hom ((ordinaryRestrictedComplex.{u,v,w} G M).homologyπ n t) =
      groupCohomology.π (integralRepresentation.{u,v,max u v w} G M) n
        ((S.mapCyclesIso F).hom t) :=
    congr($(mapHomologyIso_π F S) t)
  exact (congrArg ((S.mapHomologyIso F).hom)
    ((congrArg (HomologicalComplex.homologyMap e.hom n)
      ((congrArg (fun a => (T.mapHomologyIso L).inv (ULift.up a)) h₁).trans h₂)).trans h₃)).trans <|
    h₄.trans (congrArg _ (ordinaryCycles_compare.{u,v,w} G M n c))

end Discrete

section OrdinaryMaps

variable {G : Type u} {M : Type v} {H : Type u'} {N : Type v'}
  [Group G] [Group H] [AddCommGroup M] [AddCommGroup N]
  [DistribMulAction G M] [DistribMulAction H N]

variable [TopologicalSpace G] [IsTopologicalGroup G] [DiscreteTopology G]
  [TopologicalSpace H] [IsTopologicalGroup H] [DiscreteTopology H]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]
  [TopologicalSpace N] [DiscreteTopology N] [ContinuousSMul H N]

/-- The ordinary and continuous cochain maps are the same on underlying functions. -/
theorem ordinaryComplexIso_map_apply (φ : H →* G) (hφ : Continuous φ) (f : M →+ N)
    (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m)
    (n : ℕ) (c : continuousCochains G M n) (x : Fin n → ULift.{max u v u' v' w} H) :
    (ordinaryComplexIso.{u',v',max u v w} H N).hom.f n
        (ULift.up (continuousCochainMap φ hφ f n c)) x =
      (groupCohomology.cochainsMap (liftGroupHom.{u,max u v u' v' w,u'} φ)
        (liftCoefficientMap.{u,v,max u u' w,u',v'} φ f hf)).f n
        ((ordinaryComplexIso.{u,v,max u' v' w} G M).hom.f n (ULift.up c)) x := rfl

/-- For discrete groups the ordinary comparison intertwines the induced maps. -/
theorem ordinaryCohomologyEquiv_map (φ : H →* G) (hφ : Continuous φ) (f : M →+ N)
    (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m) (n : ℕ) (a : ContinuousH G M n) :
    ordinaryCohomologyEquiv.{u',v',max u v w} H N n
        (continuousCohomologyMap φ hφ f hf n a) =
      groupCohomology.map (liftGroupHom.{u,max u v u' v' w,u'} φ)
        (liftCoefficientMap.{u,v,max u u' w,u',v'} φ f hf) n
        (ordinaryCohomologyEquiv.{u,v,max u' v' w} G M n a) := by
  obtain ⟨c, rfl⟩ := continuousClass_surjective n a
  let φ' := liftGroupHom.{u,max u v u' v' w,u'} φ
  let f' := liftCoefficientMap.{u,v,max u u' w,u',v'} φ f hf
  let cs := ordinaryCyclesMk.{u,v,max u' v' w} G M n c
  let ct := ordinaryCyclesMk.{u',v',max u v w} H N n (continuousCocycleMap φ hφ f hf n c)
  let B := integralRepresentation.{u',v',max u v u' v' w} H N
  have hc : ct = groupCohomology.cocyclesMap φ' f' n cs := by
    apply (ModuleCat.mono_iff_injective (groupCohomology.iCocycles B n)).mp inferInstance
    have hval := congr($(HomologicalComplex.cyclesMap_i (groupCohomology.cochainsMap φ' f') n) cs)
    change groupCohomology.iCocycles B n (groupCohomology.cocyclesMap φ' f' n cs) =
      (groupCohomology.cochainsMap φ' f').f n
        (groupCohomology.iCocycles _ n cs) at hval
    rw [hval]
    calc
      _ = liftCochain.{u',v',max u v u' v' w} H N n (continuousCocycleMap φ hφ f hf n c).val.val :=
        ordinaryCyclesMk_val.{u',v',max u v w} H N n _
      _ = (groupCohomology.cochainsMap φ' f').f n
        (liftCochain.{u,v,max u v u' v' w} G M n c.val.val) := rfl
      _ = _ := congrArg ((groupCohomology.cochainsMap φ' f').f n)
        (ordinaryCyclesMk_val.{u,v,max u' v' w} G M n c).symm
  rw [continuousCohomologyMap_class]
  calc
    _ = groupCohomology.π B n ct := ordinaryCohomologyEquiv_class.{u',v',max u v w} H N n _
    _ = groupCohomology.π B n (groupCohomology.cocyclesMap φ' f' n cs) :=
      congrArg _ hc
    _ = groupCohomology.map φ' f' n (groupCohomology.π _ n cs) :=
      (congr($(groupCohomology.π_map φ' f' n) cs)).symm
    _ = _ := congrArg (groupCohomology.map φ' f' n)
      (ordinaryCohomologyEquiv_class.{u,v,max u' v' w} G M n c).symm

end OrdinaryMaps

export Model (continuousDifferential_apply continuousCoboundaries_zero continuousCocycleMap_val
  ordinaryCyclesMk_val)

theorem mem_continuousCochains : Specification.CochainsAreContinuous.{u,v} := by
  unfold Specification.CochainsAreContinuous
  intros
  rfl

theorem continuousDifferential_formula : Specification.DifferentialFormula.{u,v} := by
  intro G M _ _ _ _ _ _ _ _ n c x
  exact differentialFormula_expanded n c.val x

theorem continuousDifferential_sq : Specification.DifferentialSquared.{u,v} :=
  Model.continuousDifferential_sq

theorem continuousCochainMap_apply : Specification.CochainMapFormula.{u,v,u',v'} :=
  @Model.continuousCochainMap_apply

theorem continuousCochainMap_d : Specification.CochainMapDifferential.{u,v,u',v'} :=
  @Model.continuousCochainMap_d

theorem continuousCohomologyMap_class : Specification.CohomologyMapClass.{u,v,u',v'} :=
  @Model.continuousCohomologyMap_class

theorem mem_fixedCoefficients : Specification.FixedCoefficientsMembership.{u,v} :=
  Model.mem_fixedCoefficients

theorem quotientFixedAction_mk : Specification.QuotientAction.{u,v} :=
  Model.quotientFixedAction_mk

theorem quotientAction_continuous : Specification.QuotientActionContinuous.{u,v} := by
  intro G M _ _ _ _ _ _ _ _ U _
  exact continuous_smul

theorem continuousHZero_fixed : Specification.DegreeZeroInvariants.{u,v} := by
  intro G M _ _ _ _ _ _ _ _
  exact ⟨continuousHZeroEquiv G M, continuousHZeroEquiv_class G M⟩

theorem continuousHomology_comparison : Specification.CategoricalHomology.{u,v} := by
  intro G M _ _ _ _ _ _ _ _ n
  exact ⟨continuousHomologyIso G M n, fun c =>
    ⟨continuousCyclesMk G M n c, continuousCyclesMk_val G M n c, continuousHomologyIso_class G M n c⟩⟩

theorem ordinary_comparison : Specification.DiscreteComparison.{u,v,w} := by
  intro G M _ _ _ _ _ _ _ _ _
  exact ⟨⟨ordinaryComplexIso.{u,v,w} G M, ordinaryComplexIso_hom_apply.{u,v,w} G M⟩,
    fun n => ⟨ordinaryCohomologyEquiv.{u,v,w} G M n, ordinaryCohomologyEquiv_class.{u,v,w} G M n⟩⟩

theorem ordinary_comparison_natural : Specification.DiscreteNaturality.{u,v,w,u',v'} := by
  intro G M H N _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ φ hφ f hf
  exact ⟨⟨ordinaryComplexIso.{u,v,max u' v' w} G M, ordinaryComplexIso.{u',v',max u v w} H N,
      ordinaryComplexIso_hom_apply.{u,v,max u' v' w} G M,
      ordinaryComplexIso_hom_apply.{u',v',max u v w} H N,
      ordinaryComplexIso_map_apply.{u,v,w,u',v'} φ hφ f hf⟩,
    fun n => ⟨ordinaryCohomologyEquiv.{u,v,max u' v' w} G M n,
      ordinaryCohomologyEquiv.{u',v',max u v w} H N n,
      ordinaryCohomologyEquiv_class.{u,v,max u' v' w} G M n,
      ordinaryCohomologyEquiv_class.{u',v',max u v w} H N n,
      ordinaryCohomologyEquiv_map.{u,v,w,u',v'} φ hφ f hf n⟩⟩

end
end GaloisFormalization.GH
