import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.Algebra.Module.ULift
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Data.Fin.VecNotation

namespace GaloisFormalization.GH.Model

open CategoryTheory
open scoped BigOperators

universe u v w u' v' u'' v''

noncomputable section

set_option backward.isDefEq.respectTransparency false

/-- An action between discrete spaces is continuous, including at finite stages. -/
instance (priority := low) continuousSMul_of_discrete
    {G : Type u} {M : Type v} [SMul G M]
    [TopologicalSpace G] [TopologicalSpace M] [DiscreteTopology G] [DiscreteTopology M] :
    ContinuousSMul G M :=
  ⟨continuous_of_discreteTopology⟩

section Cochains

variable (G : Type u) (M : Type v) [TopologicalSpace G]
  [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]

/-- Inhomogeneous continuous cochains, as an integral submodule of all cochains. -/
def continuousCochains (n : ℕ) : Submodule ℤ ((Fin n → G) → M) where
  carrier := {f | Continuous f}
  zero_mem' := continuous_const
  add_mem' hf hg := hf.add hg
  smul_mem' r _f hf := (continuous_of_discreteTopology (f := fun a : M => r • a)).comp hf

variable [Group G] [DistribMulAction G M]

/-- The inhomogeneous formula. At the last index, contraction drops the last entry. -/
def differentialFormula (n : ℕ) (f : (Fin n → G) → M) (x : Fin (n + 1) → G) : M :=
  x 0 • f (fun i => x i.succ) +
    ∑ j : Fin (n + 1), (-1 : ℤ) ^ (j.val + 1) • f (Fin.contractNth j (· * ·) x)

variable [IsTopologicalGroup G] [ContinuousSMul G M]

private theorem continuous_contractNth (n : ℕ) (j : Fin (n + 1)) :
    Continuous (Fin.contractNth j (· * ·) : (Fin (n + 1) → G) → (Fin n → G)) := by
  apply continuous_pi
  intro i
  by_cases h : i.val < j.val
  · simpa only [Fin.contractNth, h, ite_true] using
      (continuous_apply (Fin.castSucc i) : Continuous fun g : Fin (n + 1) → G => g i.castSucc)
  by_cases h' : i.val = j.val
  · simpa only [Fin.contractNth, h', lt_irrefl, ite_false, ite_true, Function.comp_def] using
      (continuous_mul.comp ((continuous_apply i.castSucc :
        Continuous fun g : Fin (n + 1) → G => g i.castSucc).prodMk (continuous_apply i.succ)))
  · simpa only [Fin.contractNth, h, h', ite_false] using
      (continuous_apply i.succ : Continuous fun g : Fin (n + 1) → G => g i.succ)

private theorem continuous_formula (n : ℕ) {f : (Fin n → G) → M} (hf : Continuous f) :
    Continuous (differentialFormula G M n f) := by
  refine ((continuous_apply 0).smul (hf.comp (continuous_pi fun i => continuous_apply i.succ))).add ?_
  refine continuous_finsetSum _ fun j _ => ?_
  exact continuous_of_discreteTopology.comp (hf.comp (continuous_contractNth G n j))

/-- The integral differential on continuous cochains. -/
def continuousDifferential (n : ℕ) : continuousCochains G M n →ₗ[ℤ] continuousCochains G M (n + 1) :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun f => ⟨differentialFormula G M n f, continuous_formula G M n f.property⟩
      map_zero' := by
        apply Subtype.ext
        funext x
        simp [differentialFormula]
      map_add' := by
        intro f g
        apply Subtype.ext
        funext x
        change differentialFormula G M n ((f : (Fin n → G) → M) + g) x =
          differentialFormula G M n f x + differentialFormula G M n g x
        simp [differentialFormula, smul_add, Finset.sum_add_distrib, add_add_add_comm] }

end Cochains

section Ordinary

variable (G : Type u) (M : Type v) [Group G] [AddCommGroup M] [DistribMulAction G M]

private instance : SMulCommClass (ULift.{w} G) (ULift.{w} ℤ) (ULift.{w} M) where
  smul_comm g r m := by
    apply ULift.ext
    change g.down • (r.down • m.down) = r.down • (g.down • m.down)
    exact map_zsmul
      ({ toFun := fun a : M => g.down • a
         map_zero' := smul_zero _
         map_add' := smul_add _ } : M →+ M) _ _

/-- The integral representation used by Mathlib's ordinary complex. All three
types can be lifted to a common universe. -/
abbrev integralRepresentation :
    Rep (ULift.{w} ℤ) (ULift.{w} G) :=
  Rep.ofDistribMulAction (ULift.{w} ℤ) (ULift.{w} G) (ULift.{w} M)

/-- Transport of functions to lifted group and coefficient types. -/
def liftCochain (n : ℕ) (f : (Fin n → G) → M)
    (x : Fin n → ULift.{w} G) : ULift.{w} M :=
  ⟨f (fun i => (x i).down)⟩

theorem ordinaryDifferential_lift (n : ℕ) (f : (Fin n → G) → M) :
    inhomogeneousCochains.d (integralRepresentation.{u,v,max u (max v w)} G M) n
      (liftCochain.{u,v,max u (max v w)} G M n f) =
      liftCochain G M (n + 1) (differentialFormula G M n f) := by
  funext x
  apply ULift.ext
  have h (j : Fin (n + 1)) :
      (fun i => (Fin.contractNth j (· * ·) x i).down) =
        Fin.contractNth j (· * ·) (fun i => (x i).down) :=
    Fin.comp_contractNth _ _ (fun _ _ => rfl) j x
  change ((x 0 : ULift.{max u (max v w)} G) •
      liftCochain G M n f (fun i => x i.succ) +
      ∑ j : Fin (n + 1), (-1 : ULift.{max u (max v w)} ℤ) ^ (j.val + 1) •
        liftCochain G M n f (Fin.contractNth j (· * ·) x)).down =
    differentialFormula G M n f (fun i => (x i).down)
  unfold differentialFormula
  apply congrArg₂ (· + ·) rfl
  change ULift.down (∑ j : Fin (n + 1), (-1 : ULift.{max u (max v w)} ℤ) ^ (j.val + 1) •
    liftCochain G M n f (Fin.contractNth j (· * ·) x)) = _
  let down : ULift.{max u (max v w)} M →+ M :=
    { toFun := ULift.down, map_zero' := rfl, map_add' := fun _ _ => rfl }
  change down _ = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  change ((ULift.ringEquiv ((-1 : ULift.{max u (max v w)} ℤ) ^ (j.val + 1))) : ℤ) •
    f (fun i => (Fin.contractNth j (· * ·) x i).down) = _
  rw [map_pow, map_neg, map_one, h]

theorem differentialFormula_sq (n : ℕ) (f : (Fin n → G) → M) :
    differentialFormula G M (n + 1) (differentialFormula G M n f) = 0 := by
  let A := integralRepresentation.{u,v,max u v} G M
  have hh := groupCohomology.inhomogeneousCochains.d_comp_d n A
  have h := congr($hh (liftCochain.{u,v,max u v} G M n f))
  change inhomogeneousCochains.d _ (n + 1) (inhomogeneousCochains.d _ n _) = 0 at h
  change inhomogeneousCochains.d (integralRepresentation.{u,v,max u v} G M) (n + 1)
    (inhomogeneousCochains.d (integralRepresentation.{u,v,max u v} G M) n
      (liftCochain G M n f)) = 0 at h
  rw [ordinaryDifferential_lift.{u,v,0}, ordinaryDifferential_lift.{u,v,0}] at h
  funext x
  exact congrArg ULift.down (congrFun h (fun i => ULift.up (x i)))

end Ordinary

section Complex

variable (G : Type u) (M : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M]

@[simp] theorem continuousDifferential_apply {G : Type u} {M : Type v}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M] (n : ℕ) (c : continuousCochains G M n)
    (x : Fin (n + 1) → G) :
    (continuousDifferential G M n c).val x = differentialFormula G M n c.val x := rfl

theorem continuousDifferential_sq (n : ℕ) (f : continuousCochains G M n) :
    continuousDifferential G M (n + 1) (continuousDifferential G M n f) = 0 :=
  Subtype.ext (differentialFormula_sq G M n f)

/-- The continuous inhomogeneous complex over the integers. -/
abbrev continuousComplex : CochainComplex (ModuleCat.{max u v} ℤ) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of ℤ (continuousCochains G M n))
    (fun n => ModuleCat.ofHom (continuousDifferential G M n)) fun n =>
      ModuleCat.hom_ext (LinearMap.ext (continuousDifferential_sq G M n))

/-- Continuous cocycles as the kernel inside continuous cochains. -/
def continuousCocycles (n : ℕ) : Submodule ℤ (continuousCochains G M n) :=
  LinearMap.ker (continuousDifferential G M n)

/-- The incoming differential is zero before degree zero. -/
def continuousIncoming : (n : ℕ) →
    continuousCochains G M n.pred →ₗ[ℤ] continuousCochains G M n
  | 0 => 0
  | n + 1 => continuousDifferential G M n

theorem continuousIncoming_d (n : ℕ) (c : continuousCochains G M n.pred) :
    continuousDifferential G M n (continuousIncoming G M n c) = 0 := by
  cases n with
  | zero => exact map_zero (continuousDifferential G M 0)
  | succ n => exact continuousDifferential_sq G M n c

/-- Continuous coboundaries inside the cocycles. -/
def continuousCoboundaries (n : ℕ) : Submodule ℤ (continuousCocycles G M n) :=
  LinearMap.range ((continuousIncoming G M n).codRestrict _ (continuousIncoming_d G M n))

@[simp] theorem continuousCoboundaries_zero : continuousCoboundaries G M 0 = ⊥ := by
  apply LinearMap.range_eq_bot.mpr
  exact LinearMap.ext fun c => Subtype.ext rfl

/-- The short complex consisting of the incoming and outgoing differentials. -/
abbrev continuousShortComplex (n : ℕ) : ShortComplex (ModuleCat.{max u v} ℤ) :=
  ShortComplex.moduleCatMk (continuousIncoming G M n) (continuousDifferential G M n)
    (LinearMap.ext (continuousIncoming_d G M n))

/-- Continuous group cohomology as cocycles modulo continuous coboundaries. -/
abbrev ContinuousH (n : ℕ) := continuousCocycles G M n ⧸ continuousCoboundaries G M n

/-- The class of a cocycle. -/
def continuousClass (n : ℕ) : continuousCocycles G M n →ₗ[ℤ] ContinuousH G M n :=
  (continuousCoboundaries G M n).mkQ

end Complex

section Coordinates

variable {G : Type u} {M : Type v} [TopologicalSpace G]
  [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]

/-- In degree zero the single empty tuple represents an element of the coefficient group. -/
def cochainZero (a : M) : continuousCochains G M 0 := ⟨fun _ => a, continuous_const⟩

/-- A continuous function of one variable as a cochain. -/
def cochainOne (f : G → M) (hf : Continuous f) : continuousCochains G M 1 :=
  ⟨fun x => f (x 0), hf.comp (continuous_apply 0)⟩

/-- A continuous function of two variables as a cochain. -/
def cochainTwo (f : G × G → M) (hf : Continuous f) : continuousCochains G M 2 :=
  ⟨fun x => f (x 0, x 1), hf.comp ((continuous_apply 0).prodMk (continuous_apply 1))⟩

end Coordinates

section Maps

variable {G : Type u} {M : Type v} {H : Type u'} {N : Type v'}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
  [DistribMulAction G M] [ContinuousSMul G M] [DistribMulAction H N] [ContinuousSMul H N]

/-- Pull back the group variables and apply the coefficient map to the value. -/
def continuousCochainMap (φ : H →* G) (hφ : Continuous φ) (f : M →+ N) (n : ℕ) :
    continuousCochains G M n →ₗ[ℤ] continuousCochains H N n :=
  ({ toFun := fun c =>
        ⟨fun x => f (c.val (fun i => φ (x i))),
          continuous_of_discreteTopology.comp
            (c.property.comp (continuous_pi fun i => hφ.comp (continuous_apply i)))⟩
     map_zero' := Subtype.ext (funext fun _ => map_zero f)
     map_add' := fun _ _ => Subtype.ext (funext fun _ => map_add f _ _) } :
    continuousCochains G M n →+ continuousCochains H N n).toIntLinearMap

omit [IsTopologicalGroup G] [IsTopologicalGroup H] [DistribMulAction G M] [ContinuousSMul G M]
  [DistribMulAction H N] [ContinuousSMul H N] in
@[simp] theorem continuousCochainMap_apply (φ : H →* G) (hφ : Continuous φ)
    (f : M →+ N) (n : ℕ) (c : continuousCochains G M n) (x : Fin n → H) :
    (continuousCochainMap φ hφ f n c).val x = f (c.val (fun i => φ (x i))) := rfl

theorem continuousCochainMap_d (φ : H →* G) (hφ : Continuous φ) (f : M →+ N)
    (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m)
    (n : ℕ) (c : continuousCochains G M n) :
    continuousCochainMap φ hφ f (n + 1) (continuousDifferential G M n c) =
      continuousDifferential H N n (continuousCochainMap φ hφ f n c) := by
  apply Subtype.ext
  funext x
  simp only [continuousCochainMap_apply, continuousDifferential_apply, differentialFormula,
    map_add, map_sum, hf, map_zsmul]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have he : (fun i => φ (Fin.contractNth j (· * ·) x i)) =
      Fin.contractNth j (· * ·) (fun i => φ (x i)) :=
    Fin.comp_contractNth _ _ (map_mul φ) j x
  rw [he]

/-- Pullback on continuous cocycles. -/
def continuousCocycleMap (φ : H →* G) (hφ : Continuous φ) (f : M →+ N)
    (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m) (n : ℕ) :
    continuousCocycles G M n →ₗ[ℤ] continuousCocycles H N n :=
  ((continuousCochainMap φ hφ f n).comp (continuousCocycles G M n).subtype).codRestrict _
    (fun c => show continuousDifferential H N n (continuousCochainMap φ hφ f n c.val) = 0 from by
      rw [← continuousCochainMap_d φ hφ f hf, LinearMap.mem_ker.mp c.property, map_zero])

@[simp] theorem continuousCocycleMap_val (φ : H →* G) (hφ : Continuous φ) (f : M →+ N)
    (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m) (n : ℕ)
    (c : continuousCocycles G M n) :
    (continuousCocycleMap φ hφ f hf n c).val = continuousCochainMap φ hφ f n c.val := rfl

private theorem map_continuousCoboundaries (φ : H →* G) (hφ : Continuous φ) (f : M →+ N)
    (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m) (n : ℕ) :
    continuousCoboundaries G M n ≤
      (continuousCoboundaries H N n).comap (continuousCocycleMap φ hφ f hf n) := by
  cases n with
  | zero => rw [continuousCoboundaries_zero]; exact bot_le
  | succ n =>
    rintro c ⟨t, rfl⟩
    exact ⟨continuousCochainMap φ hφ f n t, Subtype.ext (continuousCochainMap_d φ hφ f hf n t).symm⟩

/-- The induced morphism on continuous cohomology. -/
def continuousCohomologyMap (φ : H →* G) (hφ : Continuous φ) (f : M →+ N)
    (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m) (n : ℕ) :
    ContinuousH G M n →ₗ[ℤ] ContinuousH H N n :=
  (continuousCoboundaries G M n).mapQ (continuousCoboundaries H N n)
    (continuousCocycleMap φ hφ f hf n) (map_continuousCoboundaries φ hφ f hf n)

@[simp] theorem continuousCohomologyMap_class (φ : H →* G) (hφ : Continuous φ) (f : M →+ N)
    (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m)
    (n : ℕ) (a : continuousCocycles G M n) :
    continuousCohomologyMap φ hφ f hf n (continuousClass G M n a) =
      continuousClass H N n (continuousCocycleMap φ hφ f hf n a) := rfl

end Maps

section Fixed

variable (G : Type u) (M : Type v) [Group G] [AddCommGroup M] [DistribMulAction G M]

private abbrev actionRepresentation : Representation ℤ G M :=
  Representation.ofDistribMulAction ℤ G M

/-- The submodule fixed by the subgroup `U`. -/
abbrev fixedCoefficients (U : Subgroup G) : Submodule ℤ M :=
  Representation.invariants ((actionRepresentation G M).comp U.subtype)

@[simp] theorem mem_fixedCoefficients (U : Subgroup G) (a : M) :
    a ∈ fixedCoefficients G M U ↔ ∀ g ∈ U, g • a = a :=
  ⟨fun h g hg => h ⟨g, hg⟩, fun h g => h g g.property⟩

/-- The action of the quotient on the fixed coefficients. -/
instance quotientFixedAction (U : Subgroup G) [U.Normal] :
    DistribMulAction (G ⧸ U) (fixedCoefficients G M U) :=
  let ρ := (actionRepresentation G M).quotientToInvariants U
  { smul := fun g a => ρ g a
    one_smul := fun a => congrArg (fun l : fixedCoefficients G M U →ₗ[ℤ] _ => l a) (map_one ρ)
    mul_smul := fun g h a => congrArg (fun l : fixedCoefficients G M U →ₗ[ℤ] _ => l a) (map_mul ρ g h)
    smul_zero := fun g => map_zero (ρ g)
    smul_add := fun g => map_add (ρ g) }

@[simp] theorem quotientFixedAction_mk (U : Subgroup G) [U.Normal]
    (g : G) (a : fixedCoefficients G M U) :
    (((QuotientGroup.mk' U g) • a : fixedCoefficients G M U) : M) = g • (a : M) := rfl

variable [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]

instance continuousQuotientFixedAction (U : Subgroup G) [U.Normal] :
    ContinuousSMul (G ⧸ U) (fixedCoefficients G M U) := by
  constructor
  apply continuous_prod_of_discrete_right.mpr
  intro a
  apply (QuotientGroup.isQuotientMap_mk U).continuous_iff.mpr
  refine Continuous.subtype_mk ?_ _
  exact (continuous_id : Continuous (fun g : G => g)).smul
    (continuous_const (y := (a : M)))

/-- Inflation uses the quotient map in every argument and the inclusion of the fixed coefficients. -/
def continuousInflation (U : Subgroup G) [U.Normal] (n : ℕ) :
    ContinuousH (G ⧸ U) (fixedCoefficients G M U) n →ₗ[ℤ] ContinuousH G M n :=
  continuousCohomologyMap (QuotientGroup.mk' U) QuotientGroup.continuous_mk
    (fixedCoefficients G M U).subtype.toAddMonoidHom (quotientFixedAction_mk G M U) n

/-- Restriction to a subgroup uses the subgroup inclusion in every group argument. -/
def continuousRestriction (U : Subgroup G) (n : ℕ) :
    ContinuousH G M n →ₗ[ℤ] ContinuousH U M n :=
  continuousCohomologyMap U.subtype continuous_subtype_val (AddMonoidHom.id M)
    (fun _ _ => rfl) n

end Fixed

section Multiplicative

variable {G : Type u} {A : Type v}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [MulDistribMulAction G A] [ContinuousSMul G A]

/-- Use the given multiplicative action on the underlying additive coefficient group. -/
instance additiveCoefficientAction : DistribMulAction G (Additive A) where
  smul g a := Additive.ofMul (g • a.toMul)
  one_smul a := congrArg Additive.ofMul (one_smul G a.toMul)
  mul_smul g h a := congrArg Additive.ofMul (mul_smul g h a.toMul)
  smul_zero g := congrArg Additive.ofMul (smul_one g : g • (1 : A) = 1)
  smul_add g a b := congrArg Additive.ofMul (smul_mul' g a.toMul b.toMul)

instance continuousAdditiveCoefficientAction : ContinuousSMul G (Additive A) := by
  constructor
  exact continuous_ofMul.comp (continuous_fst.smul (continuous_toMul.comp continuous_snd))

variable (G A) in
/-- The same cohomology group, in multiplicative notation for multiplicative coefficients. -/
abbrev ContinuousMulH (n : ℕ) := Multiplicative (ContinuousH G (Additive A) n)

variable (G A) in
/-- The quotient map in multiplicative notation. -/
def continuousMulClass (n : ℕ) :
    Multiplicative (continuousCocycles G (Additive A) n) →* ContinuousMulH G A n :=
  (continuousClass G (Additive A) n).toAddMonoidHom.toMultiplicative

end Multiplicative

section OrdinaryComplex

variable (G : Type u) (M : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [DiscreteTopology G] [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M]

abbrev restrictIntegral : ModuleCat.{w} (ULift.{w} ℤ) ⥤ ModuleCat.{w} ℤ :=
  ModuleCat.restrictScalars (Int.castRingHom (ULift.{w} ℤ))

abbrev ordinaryIntegralComplex :
    CochainComplex (ModuleCat.{max u v w} (ULift.{max u v w} ℤ)) ℕ :=
  groupCohomology.inhomogeneousCochains (integralRepresentation.{u,v,max u v w} G M)

/-- The ordinary complex with scalars restricted to the original integers. -/
abbrev ordinaryRestrictedComplex : CochainComplex (ModuleCat.{max u v w} ℤ) ℕ :=
  (restrictIntegral.{max u v w}.mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (ordinaryIntegralComplex.{u,v,w} G M)

/-- Regard continuous cochains in the universe of the ordinary complex. -/
abbrev liftedContinuousComplex : CochainComplex (ModuleCat.{max u v w} ℤ) ℕ :=
  ((ModuleCat.uliftFunctor.{w,max u v} ℤ).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (continuousComplex G M)

end OrdinaryComplex

section OrdinaryCycles

variable (G : Type u) (M : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [DiscreteTopology G] [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M]

omit [DiscreteTopology G] in
private theorem ordinaryCyclesMk_closed (n : ℕ) (c : continuousCocycles G M n) :
    inhomogeneousCochains.d (integralRepresentation.{u,v,max u v w} G M) n
      (liftCochain.{u,v,max u v w} G M n c.val) = 0 := by
  rw [ordinaryDifferential_lift.{u,v,w}]
  have h : differentialFormula G M n c.val = 0 :=
    congrArg Subtype.val (LinearMap.mem_ker.mp c.property)
  rw [h]
  rfl

/-- The ordinary categorical cocycle represented by the same function on lifted types. -/
def ordinaryCyclesMk (n : ℕ) (c : continuousCocycles G M n) :
    groupCohomology.cocycles (integralRepresentation.{u,v,max u v w} G M) n :=
  groupCohomology.cocyclesMk _ (ordinaryCyclesMk_closed.{u,v,w} G M n c)

omit [DiscreteTopology G] in
@[simp] theorem ordinaryCyclesMk_val (n : ℕ) (c : continuousCocycles G M n) :
    groupCohomology.iCocycles (integralRepresentation.{u,v,max u v w} G M) n
      (ordinaryCyclesMk.{u,v,w} G M n c) = liftCochain.{u,v,max u v w} G M n c.val :=
  groupCohomology.iCocycles_mk _ (ordinaryCyclesMk_closed.{u,v,w} G M n c)

end OrdinaryCycles

section OrdinaryMaps

variable {G : Type u} {M : Type v} {H : Type u'} {N : Type v'}
  [Group G] [Group H] [AddCommGroup M] [AddCommGroup N]
  [DistribMulAction G M] [DistribMulAction H N]

/-- Transport a group homomorphism to lifted group types. -/
def liftGroupHom (φ : H →* G) : ULift.{w} H →* ULift.{w} G where
  toFun h := ULift.up (φ h.down)
  map_one' := ULift.ext (map_one φ)
  map_mul' h k := ULift.ext (map_mul φ h.down k.down)

/-- Transport the equivariant coefficient map to the ordinary integral representations. -/
def liftCoefficientMap (φ : H →* G) (f : M →+ N)
    (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m) :
    Rep.res (liftGroupHom.{u,max v v' w,u'} φ)
      (integralRepresentation.{u,v,max v v' w} G M) ⟶
      integralRepresentation.{u',v',max v v' w} H N :=
  Rep.ofHom {
    toLinearMap := {
      toFun := fun m => ULift.up (f m.down)
      map_add' := fun a b => ULift.ext (map_add f a.down b.down)
      map_smul' := fun r a => ULift.ext (map_zsmul f r.down a.down) }
    isIntertwining' := fun g => LinearMap.ext fun m => ULift.ext (hf g.down m.down) }

end OrdinaryMaps
end
end GaloisFormalization.GH.Model

namespace GaloisFormalization.GH.Specification

open CategoryTheory Model
open scoped BigOperators

universe u v w u' v' u'' v''

noncomputable section

/-- The canonical constructions above determine the types of the definition targets. -/
private abbrev declarationType {α : Sort w} (_ : α) : Sort w := α

section DefinitionTypes

set_option linter.checkUnivs false

def CochainsType := declarationType (@continuousCochains.{u,v})
def DifferentialType := declarationType (@continuousDifferential.{u,v})
def ComplexType := declarationType (@continuousComplex.{u,v})
def CocyclesType := declarationType (@continuousCocycles.{u,v})
def CoboundariesType := declarationType (@continuousCoboundaries.{u,v})
def CohomologyType := declarationType (@ContinuousH.{u,v})
def ClassType := declarationType (@continuousClass.{u,v})
abbrev CochainMapType := declarationType (@continuousCochainMap.{u,v,u',v'})
abbrev CocycleMapType := declarationType (@continuousCocycleMap.{u,v,u',v'})
abbrev CohomologyMapType := declarationType (@continuousCohomologyMap.{u,v,u',v'})
def FixedCoefficientsType := declarationType (@fixedCoefficients.{u,v})
def InflationType := declarationType (@continuousInflation.{u,v})
def RestrictionType := declarationType (@continuousRestriction.{u,v})

end DefinitionTypes

def CochainsAreContinuous : Prop :=
  ∀ (G : Type u) (M : Type v) [TopologicalSpace G]
    [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    (n : ℕ) (f : (Fin n → G) → M),
    f ∈ continuousCochains G M n ↔ Continuous f

def DifferentialFormula : Prop :=
  ∀ {G : Type u} {M : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M]
    (n : ℕ) (c : continuousCochains G M n) (x : Fin (n + 1) → G),
    (continuousDifferential G M n c).val x =
      x 0 • c.val (fun i => x i.succ) +
        (∑ j : Fin n, (-1 : ℤ) ^ (j.val + 1) • c.val (Fin.contractNth j.castSucc (· * ·) x)) +
        (-1 : ℤ) ^ (n + 1) • c.val (Fin.init x)

def DifferentialSquared : Prop :=
  ∀ (G : Type u) (M : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M]
    (n : ℕ) (c : continuousCochains G M n),
    continuousDifferential G M (n + 1) (continuousDifferential G M n c) = 0

def ClassesSurjective : Prop :=
  ∀ {G : Type u} {M : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M] (n : ℕ),
    Function.Surjective (continuousClass G M n)

def ClassEquality : Prop :=
  ∀ {G : Type u} {M : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M]
    {n : ℕ} (a b : continuousCocycles G M n),
    continuousClass G M n a = continuousClass G M n b ↔ a - b ∈ continuousCoboundaries G M n

def DegreeZeroClassEquality : Prop :=
  ∀ {G : Type u} {M : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M] (a b : continuousCocycles G M 0),
    continuousClass G M 0 a = continuousClass G M 0 b ↔ a = b

def PositiveDegreeClassEquality : Prop :=
  ∀ {G : Type u} {M : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M] {n : ℕ} (a b : continuousCocycles G M (n + 1)),
    continuousClass G M (n + 1) a = continuousClass G M (n + 1) b ↔
      ∃ t : continuousCochains G M n, continuousDifferential G M n t = a.val - b.val

def DegreeZeroDifferential : Prop :=
  ∀ {G : Type u} {M : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M] (c : continuousCochains G M 0) (g : G),
    (continuousDifferential G M 0 c).val ![g] = g • c.val Fin.elim0 - c.val Fin.elim0

def DegreeOneDifferential : Prop :=
  ∀ {G : Type u} {M : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M] (c : continuousCochains G M 1) (g h : G),
    (continuousDifferential G M 1 c).val ![g, h] =
      c.val ![g] + g • c.val ![h] - c.val ![g * h]

def DegreeOneCocycle : Prop :=
  ∀ {G : Type u} {M : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M] (c : continuousCochains G M 1),
    c ∈ continuousCocycles G M 1 ↔
      ∀ g h : G, c.val ![g * h] = c.val ![g] + g • c.val ![h]

def DegreeTwoCocycle : Prop :=
  ∀ {G : Type u} {M : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M] (c : continuousCochains G M 2),
    c ∈ continuousCocycles G M 2 ↔
      ∀ g h k : G, c.val ![g,h] + c.val ![g*h,k] = g • c.val ![h,k] + c.val ![g,h*k]

def FixedCoefficientsMembership : Prop :=
  ∀ (G : Type u) (M : Type v) [Group G] [AddCommGroup M] [DistribMulAction G M]
    (U : Subgroup G) (a : M), a ∈ fixedCoefficients G M U ↔ ∀ g ∈ U, g • a = a

def QuotientAction : Prop :=
  ∀ (G : Type u) (M : Type v) [Group G] [AddCommGroup M] [DistribMulAction G M]
    (U : Subgroup G) [U.Normal] (g : G) (a : fixedCoefficients G M U),
    (((QuotientGroup.mk' U g) • a : fixedCoefficients G M U) : M) = g • (a : M)

def QuotientActionContinuous : Prop :=
  ∀ (G : Type u) (M : Type v) [Group G] [AddCommGroup M] [DistribMulAction G M]
    [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace M] [DiscreteTopology M]
    [ContinuousSMul G M] (U : Subgroup G) [U.Normal],
    Continuous (fun p : (G ⧸ U) × fixedCoefficients G M U => p.1 • p.2)

def InflationOnClasses : Prop :=
  ∀ (G : Type u) (M : Type v) [Group G] [AddCommGroup M] [DistribMulAction G M]
    [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace M] [DiscreteTopology M]
    [ContinuousSMul G M] (U : Subgroup G) [U.Normal] (n : ℕ)
    (c : continuousCocycles (G ⧸ U) (fixedCoefficients G M U) n),
    ∃ a : continuousCocycles G M n,
      (∀ x : Fin n → G, a.val.val x = (c.val.val fun i => QuotientGroup.mk' U (x i)).val) ∧
      continuousInflation G M U n (continuousClass (G ⧸ U) (fixedCoefficients G M U) n c) =
        continuousClass G M n a

def DegreeZeroInvariants : Prop :=
  ∀ (G : Type u) (M : Type v) [Group G] [AddCommGroup M] [DistribMulAction G M]
    [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace M] [DiscreteTopology M]
    [ContinuousSMul G M],
    ∃ e : ContinuousH G M 0 ≃ₗ[ℤ] fixedCoefficients G M ⊤,
      ∀ c : continuousCocycles G M 0,
        (e (continuousClass G M 0 c)).val = c.val.val Fin.elim0

def MultiplicativeCoboundary : Prop :=
  ∀ {G : Type u} {A : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [MulDistribMulAction G A] [ContinuousSMul G A] (b : A) (g : G),
    ((continuousDifferential G (Additive A) 0 (cochainZero (Additive.ofMul b))).val ![g]).toMul =
      b⁻¹ * (g • b)

def MultiplicativeCocycle : Prop :=
  ∀ {G : Type u} {A : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [MulDistribMulAction G A] [ContinuousSMul G A] (c : G → A) (hc : Continuous c),
    cochainOne (fun g => Additive.ofMul (c g)) (continuous_ofMul.comp hc) ∈
      continuousCocycles G (Additive A) 1 ↔
    ∀ g h : G, c (g * h) = c g * (g • c h)

def MultiplicativeClasses : Prop :=
  ∀ {G : Type u} {A : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [MulDistribMulAction G A] [ContinuousSMul G A]
    (c c' : continuousCocycles G (Additive A) 1),
    continuousClass G (Additive A) 1 c' = continuousClass G (Additive A) 1 c ↔
      ∃ b : A, ∀ g : G,
        (c'.val.val ![g]).toMul = b⁻¹ * (c.val.val ![g]).toMul * (g • b)

set_option linter.checkUnivs false in
def MultiplicativeCohomologyType := declarationType (@ContinuousMulH.{u,v})
set_option linter.checkUnivs false in
def MultiplicativeClassType := declarationType (@continuousMulClass.{u,v})

def CochainMapFormula : Prop :=
  ∀ {G : Type u} {M : Type v} {H : Type u'} {N : Type v'}
    [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
    [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    (φ : H →* G) (hφ : Continuous φ) (f : M →+ N)
    (n : ℕ) (c : continuousCochains G M n) (x : Fin n → H),
    (continuousCochainMap φ hφ f n c).val x = f (c.val (fun i => φ (x i)))

def CochainMapDifferential : Prop :=
  ∀ {G : Type u} {M : Type v} {H : Type u'} {N : Type v'}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    [DistribMulAction G M] [ContinuousSMul G M] [DistribMulAction H N] [ContinuousSMul H N]
    (φ : H →* G) (hφ : Continuous φ) (f : M →+ N)
    (_ : ∀ (h : H) (m : M), f (φ h • m) = h • f m)
    (n : ℕ) (c : continuousCochains G M n),
    continuousCochainMap φ hφ f (n + 1) (continuousDifferential G M n c) =
      continuousDifferential H N n (continuousCochainMap φ hφ f n c)

def CohomologyMapClass : Prop :=
  ∀ {G : Type u} {M : Type v} {H : Type u'} {N : Type v'}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    [DistribMulAction G M] [ContinuousSMul G M] [DistribMulAction H N] [ContinuousSMul H N]
    (φ : H →* G) (hφ : Continuous φ) (f : M →+ N)
    (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m)
    (n : ℕ) (a : continuousCocycles G M n),
    continuousCohomologyMap φ hφ f hf n (continuousClass G M n a) =
      continuousClass H N n (continuousCocycleMap φ hφ f hf n a)

def CochainMapIdentity : Prop :=
  ∀ {G : Type u} {M : Type v} [Group G] [TopologicalSpace G]
    [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M] (n : ℕ),
    continuousCochainMap (MonoidHom.id G) continuous_id (AddMonoidHom.id M) n = LinearMap.id

def CohomologyMapIdentity : Prop :=
  ∀ {G : Type u} {M : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M] (n : ℕ),
    continuousCohomologyMap (MonoidHom.id G) continuous_id (AddMonoidHom.id M)
      (fun _ _ => rfl) n = LinearMap.id

def CochainMapComposition : Prop :=
  ∀ {G : Type u} {M : Type v} {H : Type u'} {N : Type v'}
    [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
    [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    {J : Type u''} {P : Type v''} [Group J] [TopologicalSpace J]
    [AddCommGroup P] [TopologicalSpace P] [DiscreteTopology P]
    (φ : H →* G) (hφ : Continuous φ) (f : M →+ N)
    (ψ : J →* H) (hψ : Continuous ψ) (g : N →+ P) (n : ℕ),
    continuousCochainMap (φ.comp ψ) (hφ.comp hψ) (g.comp f) n =
      (continuousCochainMap ψ hψ g n).comp (continuousCochainMap φ hφ f n)

def CohomologyMapComposition : Prop :=
  ∀ {G : Type u} {M : Type v} {H : Type u'} {N : Type v'}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    [DistribMulAction G M] [ContinuousSMul G M] [DistribMulAction H N] [ContinuousSMul H N]
    {J : Type u''} {P : Type v''}
    [Group J] [TopologicalSpace J] [IsTopologicalGroup J]
    [AddCommGroup P] [TopologicalSpace P] [DiscreteTopology P]
    [DistribMulAction J P] [ContinuousSMul J P]
    (φ : H →* G) (hφ : Continuous φ) (f : M →+ N)
    (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m)
    (ψ : J →* H) (hψ : Continuous ψ) (g : N →+ P)
    (hg : ∀ (j : J) (a : N), g (ψ j • a) = j • g a) (n : ℕ),
    continuousCohomologyMap (φ.comp ψ) (hφ.comp hψ) (g.comp f)
      (fun j m => by change g (f (φ (ψ j) • m)) = j • g (f m); rw [hf, hg]) n =
      (continuousCohomologyMap ψ hψ g hg n).comp (continuousCohomologyMap φ hφ f hf n)

def CategoricalHomology : Prop :=
  ∀ (G : Type u) (M : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M] (n : ℕ),
    ∃ e : ModuleCat.of ℤ (ContinuousH G M n) ≅ (continuousComplex G M).homology n,
      ∀ c : continuousCocycles G M n,
        ∃ z : (continuousComplex G M).cycles n,
          (continuousComplex G M).iCycles n z = c.val ∧
          e.hom (continuousClass G M n c) = (continuousComplex G M).homologyπ n z

section Ordinary

variable (G : Type u) (M : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [DiscreteTopology G] [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M]

/-- The comparison forgets continuity, after identifying the lifted group and coefficient types. -/
def IsOrdinaryCochainComparison
    (e : liftedContinuousComplex.{u,v,w} G M ≅ ordinaryRestrictedComplex.{u,v,w} G M) : Prop :=
  ∀ (n : ℕ) (c : continuousCochains G M n) (x : Fin n → ULift.{max u v w} G),
    (e.hom.f n (ULift.up c) x).down = c.val (fun i => (x i).down)

/-- The comparison sends every class to the class of the same ordinary cocycle. -/
def IsOrdinaryClassComparison (n : ℕ)
    (e : ContinuousH G M n ≃+ groupCohomology (integralRepresentation.{u,v,max u v w} G M) n) : Prop :=
  ∀ c : continuousCocycles G M n,
    e (continuousClass G M n c) = groupCohomology.π
      (integralRepresentation.{u,v,max u v w} G M) n (ordinaryCyclesMk.{u,v,w} G M n c)

end Ordinary

def DiscreteComparison : Prop :=
  ∀ (G : Type u) (M : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [DiscreteTopology G] [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M],
    (∃ e : liftedContinuousComplex.{u,v,w} G M ≅ ordinaryRestrictedComplex.{u,v,w} G M,
      IsOrdinaryCochainComparison.{u,v,w} G M e) ∧
    ∀ n : ℕ, ∃ e : ContinuousH G M n ≃+ groupCohomology (integralRepresentation.{u,v,max u v w} G M) n,
      IsOrdinaryClassComparison.{u,v,w} G M n e

def DiscreteNaturality : Prop :=
  ∀ {G : Type u} {M : Type v} {H : Type u'} {N : Type v'}
    [Group G] [Group H] [AddCommGroup M] [AddCommGroup N]
    [DistribMulAction G M] [DistribMulAction H N]
    [TopologicalSpace G] [IsTopologicalGroup G] [DiscreteTopology G]
    [TopologicalSpace H] [IsTopologicalGroup H] [DiscreteTopology H]
    [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]
    [TopologicalSpace N] [DiscreteTopology N] [ContinuousSMul H N]
    (φ : H →* G) (hφ : Continuous φ) (f : M →+ N)
    (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m),
    let GRep := integralRepresentation.{u,v,max u v u' v' w} G M
    let HRep := integralRepresentation.{u',v',max u v u' v' w} H N
    let φ' := liftGroupHom.{u,max u v u' v' w,u'} φ
    let f' := liftCoefficientMap.{u,v,max u u' w,u',v'} φ f hf
    (∃ (eG : liftedContinuousComplex.{u,v,max u' v' w} G M ≅
          ordinaryRestrictedComplex.{u,v,max u' v' w} G M)
        (eH : liftedContinuousComplex.{u',v',max u v w} H N ≅
          ordinaryRestrictedComplex.{u',v',max u v w} H N),
        IsOrdinaryCochainComparison.{u,v,max u' v' w} G M eG ∧
        IsOrdinaryCochainComparison.{u',v',max u v w} H N eH ∧
        ∀ (n : ℕ) (c : continuousCochains G M n) (x : Fin n → ULift.{max u v u' v' w} H),
          eH.hom.f n (ULift.up (continuousCochainMap φ hφ f n c)) x =
            (groupCohomology.cochainsMap (A := GRep) (B := HRep) φ' f').f n
              (eG.hom.f n (ULift.up c)) x) ∧
    ∀ n : ℕ,
      ∃ (eG : ContinuousH G M n ≃+ groupCohomology GRep n)
        (eH : ContinuousH H N n ≃+ groupCohomology HRep n),
        IsOrdinaryClassComparison.{u,v,max u' v' w} G M n eG ∧
        IsOrdinaryClassComparison.{u',v',max u v w} H N n eH ∧
        ∀ a : ContinuousH G M n,
          eH (continuousCohomologyMap φ hφ f hf n a) =
            groupCohomology.map φ' f' n (eG a)

end
end GaloisFormalization.GH.Specification
