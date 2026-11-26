import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.FieldTheory.KrullTopology

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace LinearAlgebraicGroups.Descent.NonabelianCohomology

universe u v w

section Cohomology

variable {Γ : Type u} {M : Type v} [Group Γ] [TopologicalSpace Γ]
  [Group M] [TopologicalSpace M]

/-- Continuous nonabelian cocycles for an action by group automorphisms. -/
def IsCocycle (ρ : Γ →* MulAut M) (a : Γ → M) : Prop :=
  Continuous a ∧ ∀ σ τ, a (σ * τ) = a σ * ρ σ (a τ)

/-- The coefficient group is given the discrete topology in Galois applications. -/
def Cocycle (ρ : Γ →* MulAut M) : Type (max u v) :=
  {a : Γ → M // IsCocycle ρ a}

instance (ρ : Γ →* MulAut M) : CoeFun (Cocycle ρ) (fun _ => Γ → M) :=
  ⟨Subtype.val⟩

/-- The constant identity cocycle. -/
def trivial (ρ : Γ →* MulAut M) : Cocycle ρ :=
  ⟨fun _ => 1, continuous_const, by simp⟩

/-- Change of cocycle by the specified element of the coefficient group. -/
def ChangesBy {ρ : Γ →* MulAut M} (a a' : Cocycle ρ) (b : M) : Prop :=
  ∀ σ, a' σ = b⁻¹ * a σ * ρ σ b

def Cohomologous {ρ : Γ →* MulAut M} (a a' : Cocycle ρ) : Prop :=
  ∃ b : M, ChangesBy a a' b

def cocycleSetoid (ρ : Γ →* MulAut M) : Setoid (Cocycle ρ) where
  r := Cohomologous
  iseqv := by
    refine ⟨fun a => ⟨1, ?_⟩, ?_, ?_⟩
    · intro σ
      simp
    · rintro a a' ⟨b, hb⟩
      refine ⟨b⁻¹, fun σ => ?_⟩
      rw [hb σ, map_inv]
      simp [mul_assoc]
    · rintro a a' a'' ⟨b, hb⟩ ⟨c, hc⟩
      refine ⟨b * c, fun σ => ?_⟩
      rw [hc σ, hb σ, map_mul, mul_inv_rev]
      simp only [mul_assoc]

/-- The pointed set of continuous nonabelian cohomology classes. -/
def H1 (ρ : Γ →* MulAut M) : Type (max u v) :=
  Quotient (cocycleSetoid ρ)

def classOf {ρ : Γ →* MulAut M} (a : Cocycle ρ) : H1 ρ :=
  Quotient.mk (cocycleSetoid ρ) a

def basepoint (ρ : Γ →* MulAut M) : H1 ρ :=
  classOf (trivial ρ)

/-- The coefficient subgroup fixed pointwise by a subgroup of the acting group. -/
def Fixed (ρ : Γ →* MulAut M) (N : Subgroup Γ) : Subgroup M where
  carrier := {m | ∀ n ∈ N, ρ n m = m}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy n hn
    exact (map_mul (ρ n) x y).trans (congrArg₂ (· * ·) (hx n hn) (hy n hn))
  inv_mem' := by
    intro x hx n hn
    exact (map_inv (ρ n) x).trans (congrArg Inv.inv (hx n hn))

variable (ρ : Γ →* MulAut M) (N : Subgroup Γ) [N.Normal]

omit [TopologicalSpace Γ] [TopologicalSpace M] in
private theorem fixed_preserved (σ : Γ) (m : Fixed ρ N) :
    ∀ n ∈ N, ρ n (ρ σ m.val) = ρ σ m.val := by
  intro n hn
  have h : σ⁻¹ * n * σ ∈ N := by
    simpa using (inferInstance : N.Normal).conj_mem n hn σ⁻¹
  have he : n * σ = σ * (σ⁻¹ * n * σ) := by simp [mul_assoc]
  calc
    ρ n (ρ σ m.val) = ρ (n * σ) m.val := by rw [map_mul]; rfl
    _ = ρ σ (ρ (σ⁻¹ * n * σ) m.val) := by rw [he, map_mul]; rfl
    _ = ρ σ m.val := congrArg (ρ σ) (m.property _ h)

/-- Restrict the action to the fixed subgroup of a normal subgroup. -/
def fixedAction : Γ →* MulAut (Fixed ρ N) where
  toFun σ :=
    { toFun := fun m => ⟨ρ σ m.val, fixed_preserved ρ N σ m⟩
      invFun := fun m => ⟨ρ σ⁻¹ m.val, fixed_preserved ρ N σ⁻¹ m⟩
      left_inv := fun m => Subtype.ext (by
        change ρ σ⁻¹ (ρ σ m.val) = m.val
        rw [map_inv]
        exact (ρ σ).symm_apply_apply _)
      right_inv := fun m => Subtype.ext (by
        change ρ σ (ρ σ⁻¹ m.val) = m.val
        rw [map_inv]
        exact (ρ σ).apply_symm_apply _)
      map_mul' := fun m n => Subtype.ext (map_mul (ρ σ) m.val n.val) }
  map_one' := by
    apply MulEquiv.ext
    intro m
    apply Subtype.ext
    change ρ 1 m.val = m.val
    rw [map_one]
    rfl
  map_mul' σ τ := by
    apply MulEquiv.ext
    intro m
    apply Subtype.ext
    change ρ (σ * τ) m.val = ρ σ (ρ τ m.val)
    rw [map_mul]
    rfl

variable {Δ : Type w} [Group Δ] (q : Γ →* Δ)

omit [TopologicalSpace Γ] [TopologicalSpace M] in
private theorem ker_le_fixedAction : q.ker ≤ (fixedAction ρ q.ker).ker := by
  intro n hn
  rw [MonoidHom.mem_ker]
  apply MulEquiv.ext
  intro m
  exact Subtype.ext (m.property n hn)

/-- The action on the kernel-fixed coefficients descends to the quotient group. -/
noncomputable def quotientAction (hq : Function.Surjective q) : Δ →* MulAut (Fixed ρ q.ker) :=
  (QuotientGroup.lift q.ker (fixedAction ρ q.ker) (ker_le_fixedAction ρ q)).comp
    (QuotientGroup.quotientKerEquivOfSurjective q hq).symm.toMonoidHom

omit [TopologicalSpace Γ] [TopologicalSpace M] in
@[simp]
theorem quotientAction_apply (hq : Function.Surjective q) (σ : Γ) (m : Fixed ρ q.ker) :
    (quotientAction ρ q hq (q σ) m).val = ρ σ m.val := by
  have he : (QuotientGroup.quotientKerEquivOfSurjective q hq).symm (q σ) =
      QuotientGroup.mk σ :=
    (QuotientGroup.quotientKerEquivOfSurjective q hq).symm_apply_eq.mpr rfl
  change ((QuotientGroup.lift q.ker (fixedAction ρ q.ker) (ker_le_fixedAction ρ q))
    ((QuotientGroup.quotientKerEquivOfSurjective q hq).symm (q σ)) m).val = _
  rw [he]
  rfl

end Cohomology

section Galois

variable {k S : Type u} [Field k] [Field S] [Algebra k S] [IsGalois k S]
  {M : Type v} [Group M] [TopologicalSpace M] [DiscreteTopology M]
  (ρ : Gal(S/k) →* MulAut M)

noncomputable abbrev restriction (L : FiniteGaloisIntermediateField k S) : Gal(S/k) →* Gal(L/k) :=
  AlgEquiv.restrictNormalHom L

noncomputable abbrev LevelCoefficients (L : FiniteGaloisIntermediateField k S) : Subgroup M :=
  Fixed ρ (restriction L).ker

noncomputable abbrev levelAction (L : FiniteGaloisIntermediateField k S) :
    Gal(L/k) →* MulAut (LevelCoefficients ρ L) :=
  quotientAction ρ (restriction L) (AlgEquiv.restrictNormalHom_surjective S)

/-- A finite-level cocycle whose inflation and inclusion give a. -/
def DescendsAt (a : Cocycle ρ) (L : FiniteGaloisIntermediateField k S)
    (c : Cocycle (levelAction ρ L)) : Prop :=
  ∀ σ, (c (restriction L σ)).val = a σ

end Galois

section SchemePoints

variable (k R : Type u) [Field k] [CommRing R] [Algebra k R]
  (H : Over (Spec (CommRingCat.of k)))

/-- The group of points on a test algebra, using the group object over Spec k. -/
abbrev Points := (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k R)) ⟶ H

variable [GrpObj H]

/-- Extension of scalars on the group of points. -/
noncomputable def pointMap {T : Type u} [CommRing T] [Algebra k T] (f : R →ₐ[k] T) :
    Points k R H →* Points k T H where
  toFun p := (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom f).op ≫ p
  map_one' := MonObj.comp_one _
  map_mul' p p' := MonObj.comp_mul _ p p'

/-- A field automorphism acts by precomposition with its contravariant scheme map. -/
noncomputable def pointAction : (R ≃ₐ[k] R) →* MulAut (Points k R H) where
  toFun σ :=
    { toFun := fun p => (algSpec (CommRingCat.of k)).map
        (CommAlgCat.ofHom σ.toAlgHom).op ≫ p
      invFun := fun p => (algSpec (CommRingCat.of k)).map
        (CommAlgCat.ofHom σ.symm.toAlgHom).op ≫ p
      left_inv := by
        intro p
        dsimp only
        rw [← Category.assoc, ← Functor.map_comp]
        have he : (CommAlgCat.ofHom σ.symm.toAlgHom).op ≫
            (CommAlgCat.ofHom σ.toAlgHom).op = 𝟙 _ := by
          apply Quiver.Hom.unop_inj
          ext x
          exact σ.symm_apply_apply x
        simp only [he, CategoryTheory.Functor.map_id, Category.id_comp]
      right_inv := by
        intro p
        dsimp only
        rw [← Category.assoc, ← Functor.map_comp]
        have he : (CommAlgCat.ofHom σ.toAlgHom).op ≫
            (CommAlgCat.ofHom σ.symm.toAlgHom).op = 𝟙 _ := by
          apply Quiver.Hom.unop_inj
          ext x
          exact σ.apply_symm_apply x
        simp only [he, CategoryTheory.Functor.map_id, Category.id_comp]
      map_mul' := fun p p' => MonObj.comp_mul _ p p' }
  map_one' := by
    ext p : 1
    change (algSpec (CommRingCat.of k)).map (𝟙 _) ≫ p = p
    simp
  map_mul' σ τ := by
    ext p : 1
    change (algSpec (CommRingCat.of k)).map
        (CommAlgCat.ofHom (σ * τ).toAlgHom).op ≫ p =
      (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom σ.toAlgHom).op ≫
      (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom τ.toAlgHom).op ≫ p
    rw [← Category.assoc, ← Functor.map_comp]
    rfl

variable (S : Type u) [Field S] [Algebra k S]

/-- Continuous Galois cohomology of the discrete points of H over a chosen separable closure. -/
noncomputable def groupH1 [IsSepClosure k S] :=
  @H1 (S ≃ₐ[k] S) (Points k S H) _ (krullTopology k S) _ ⊥ (pointAction k S H)

noncomputable def groupBasepoint [IsSepClosure k S] : groupH1 k H S :=
  @basepoint (S ≃ₐ[k] S) (Points k S H) _ (krullTopology k S) _ ⊥ (pointAction k S H)

end SchemePoints

namespace Specification

section Cohomology

-- The expected types quantify independently over both input universes.
set_option linter.checkUnivs false

def CocyclesType :=
  ∀ {Γ : Type u} {M : Type v} [Group Γ] [TopologicalSpace Γ]
    [Group M] [TopologicalSpace M], (Γ →* MulAut M) → Type (max u v)

def EquivalenceType :=
  ∀ {Γ : Type u} {M : Type v} [Group Γ] [TopologicalSpace Γ]
    [Group M] [TopologicalSpace M] {ρ : Γ →* MulAut M}, Cocycle ρ → Cocycle ρ → Prop

def BasepointType :=
  ∀ {Γ : Type u} {M : Type v} [Group Γ] [TopologicalSpace Γ]
    [Group M] [TopologicalSpace M] (ρ : Γ →* MulAut M), H1 ρ

def ClassEquality : Prop :=
  ∀ {Γ : Type u} {M : Type v} [Group Γ] [TopologicalSpace Γ]
    [Group M] [TopologicalSpace M] {ρ : Γ →* MulAut M} {a a' : Cocycle ρ},
    classOf a = classOf a' ↔ ∃ b : M, ∀ σ, a' σ = b⁻¹ * a σ * ρ σ b

end Cohomology

section FiniteLevels

def FiniteLevel : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S] [IsGalois k S]
    {M : Type v} [Group M] [TopologicalSpace M] [DiscreteTopology M]
    {ρ : Gal(S/k) →* MulAut M} (L₀ : FiniteGaloisIntermediateField k S) (a : Cocycle ρ),
    ∃ (L : FiniteGaloisIntermediateField k S) (c : Cocycle (levelAction ρ L)),
      L₀ ≤ L ∧ DescendsAt ρ a L c

def FiniteLevelWitness : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S] [IsGalois k S]
    {M : Type v} [Group M] [TopologicalSpace M] [DiscreteTopology M]
    {ρ : Gal(S/k) →* MulAut M} (L₀ : FiniteGaloisIntermediateField k S)
    (a a' : Cocycle ρ) (b : M), ChangesBy a a' b →
    ∃ (L : FiniteGaloisIntermediateField k S) (c c' : Cocycle (levelAction ρ L))
      (d : LevelCoefficients ρ L), L₀ ≤ L ∧ DescendsAt ρ a L c ∧ DescendsAt ρ a' L c' ∧
        d.val = b ∧ ChangesBy c c' d

def FiniteLevelClassEquality : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S] [IsGalois k S]
    {M : Type v} [Group M] [TopologicalSpace M] [DiscreteTopology M]
    {ρ : Gal(S/k) →* MulAut M} (L₀ : FiniteGaloisIntermediateField k S)
    (a a' : Cocycle ρ), classOf a = classOf a' ↔
    ∃ (L : FiniteGaloisIntermediateField k S) (c c' : Cocycle (levelAction ρ L)),
      L₀ ≤ L ∧ DescendsAt ρ a L c ∧ DescendsAt ρ a' L c' ∧ classOf c = classOf c'

def ContinuousActionCriterion : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S] [IsGalois k S]
    {M : Type v} [Group M] [TopologicalSpace M] [DiscreteTopology M]
    {ρ : Gal(S/k) →* MulAut M},
    Continuous (fun p : Gal(S/k) × M => ρ p.1 p.2) ↔
      ∀ m : M, ∃ L : FiniteGaloisIntermediateField k S, m ∈ LevelCoefficients ρ L

end FiniteLevels

section SchemePoints

def GroupH1Type :=
  ∀ (k : Type u) [Field k] (H : Over (Spec (CommRingCat.of k))) [GrpObj H]
    (S : Type u) [Field S] [Algebra k S] [IsSepClosure k S], Type u

def GroupBasepointType :=
  ∀ (k : Type u) [Field k] (H : Over (Spec (CommRingCat.of k))) [GrpObj H]
    (S : Type u) [Field S] [Algebra k S] [IsSepClosure k S], groupH1 k H S

def FinitePoints : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S]
    {H : Over (Spec (CommRingCat.of k))} [GrpObj H] [IsGalois k S]
    (L : FiniteGaloisIntermediateField k S) (p : Points k S H),
    p ∈ Set.range (pointMap k L H L.toIntermediateField.val) ↔
      p ∈ Fixed (pointAction k S H) (restriction L).ker

def FinitePointsIdentification : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S]
    {H : Over (Spec (CommRingCat.of k))} [GrpObj H] [IsGalois k S]
    (L : FiniteGaloisIntermediateField k S),
    ∃ e : Points k L H ≃* LevelCoefficients (pointAction k S H) L,
      (∀ p, (e p).val = pointMap k L H L.toIntermediateField.val p) ∧
      (∀ δ p, e (pointAction k L H δ p) = levelAction (pointAction k S H) L δ (e p))

def PointsAreUnion : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S]
    {H : Over (Spec (CommRingCat.of k))} [GrpObj H] [IsGalois k S]
    [LocallyOfFiniteType H.hom] (p : Points k S H),
    ∃ L : FiniteGaloisIntermediateField k S,
      p ∈ Set.range (pointMap k L H L.toIntermediateField.val)

def ContinuousPointAction : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S]
    {H : Over (Spec (CommRingCat.of k))} [GrpObj H] [IsSepClosure k S] [Smooth H.hom],
    letI : TopologicalSpace (Points k S H) := ⊥
    Continuous (fun p : Gal(S/k) × Points k S H => pointAction k S H p.1 p.2)

end SchemePoints

end Specification

end LinearAlgebraicGroups.Descent.NonabelianCohomology
