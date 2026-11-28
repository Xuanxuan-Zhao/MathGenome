import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.SuperRestricted.SuperEnvelopingModules
import MathGenome.Internal.LieTheoryDeepening.LieNotes.SuperRestricted.SuperEnveloping
import Mathlib.LinearAlgebra.BilinearMap

namespace LieNotes.SuperRestricted.SuperEnvelopingModules

open SuperEnveloping (Enveloping ι piece quotientMap quotientMap_surjective generator_relation
  ι_mem_piece relationIdeal)
open SuperEnveloping.Construction (generatorParity generatorParity_apply parityScalar
  parityScalar_add parityScalar_sq mem_paritySpace parity_quotientMap tensorParity_ι)

noncomputable section

abbrev EnvelopingModule := @Definitions.EnvelopingModule
abbrev EnvelopingModule.Hom := @Definitions.EnvelopingModule.Hom

universe u v w z

variable {k : Type u} {V : Type v} [Field k] [NeZero (2 : k)] [AddCommGroup V] [Module k V]
  {L : LieSuperalgebra k V}
  {M : Type w} [AddCommGroup M] [Module k M] {G : Grading k M}
  {N : Type z} [AddCommGroup N] [Module k N] {H : Grading k N}

omit [NeZero (2 : k)] in
private theorem span_homogeneous {P : Type*} [AddCommGroup P] [Module k P]
    (J : Grading k P) : Submodule.span k (⋃ i, (J.piece i : Set P)) = ⊤ := by
  rw [Submodule.span_iUnion]
  simpa using J.isInternal.submodule_iSup_eq_top

omit [NeZero (2 : k)] in
private theorem linearMap_ext_homogeneous {P Q : Type*}
    [AddCommGroup P] [Module k P] [AddCommGroup Q] [Module k Q]
    (J : Grading k P) {f g : P →ₗ[k] Q}
    (h : ∀ i (p : P), p ∈ J.piece i → f p = g p) : f = g :=
  LinearMap.ext_on (span_homogeneous J) fun p hp => by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp
    exact h i p hi

private theorem mem_piece_of_generatorParity {i : ZMod 2} {m : M}
    (h : generatorParity G m = parityScalar k i • m) : m ∈ G.piece i := by
  let p : M →ₗ[k] M := LinearMap.id + parityScalar k i • generatorParity G
  have hp (x : M) : p x = x + parityScalar k i • generatorParity G x := rfl
  have hle : (⊤ : Submodule k M) ≤ (G.piece i).comap p := by
    rw [← span_homogeneous G, Submodule.span_le]
    intro x hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
    change p x ∈ G.piece i
    rw [hp, generatorParity_apply G hj, smul_smul]
    by_cases hij : i = j
    · subst j
      exact (G.piece i).add_mem hj ((G.piece i).smul_mem _ hj)
    · have hs : parityScalar k i * parityScalar k j = -1 := by
        have hcases (a : ZMod 2) : a = 0 ∨ a = 1 := by
          fin_cases a
          · exact Or.inl rfl
          · exact Or.inr rfl
        rcases hcases i with rfl | rfl <;> rcases hcases j with rfl | rfl <;>
          first | exact (hij rfl).elim | simp [parityScalar, show (1 : ZMod 2) ≠ 0 by decide]
      simp [hs]
  have hm : p m ∈ G.piece i := hle (Submodule.mem_top)
  rw [hp, h, smul_smul, parityScalar_sq, one_smul, ← two_smul k] at hm
  exact ((G.piece i).smul_mem_iff (NeZero.ne (2 : k))).mp hm

private theorem intertwines_of_generators
    (A : Enveloping L →ₐ[k] Module.End k M) (B : Enveloping L →ₐ[k] Module.End k N)
    (f : M →ₗ[k] N)
    (h : ∀ (x : V) (m : M), f (A (ι L x) m) = B (ι L x) (f m)) :
    ∀ (a : Enveloping L) (m : M), f (A a m) = B a (f m) := by
  intro a
  obtain ⟨t, rfl⟩ := quotientMap_surjective L a
  induction t using TensorAlgebra.induction with
  | algebraMap r =>
    intro m
    simp
  | ι x => exact h x
  | mul a b ha hb =>
    intro m
    simp only [map_mul, Module.End.mul_apply]
    rw [ha, hb]
  | add a b ha hb =>
    intro m
    simp only [map_add, LinearMap.add_apply]
    rw [ha, hb]

/-- Intertwining the generator actions is sufficient for intertwining the enveloping actions. -/
theorem intertwines_iff_on_generators (A : EnvelopingModule L G) (B : EnvelopingModule L H)
    (f : M →ₗ[k] N) :
    (∀ (a : Enveloping L) (m : M), f (A.act a m) = B.act a (f m)) ↔
      (∀ (x : V) (m : M), f (A.act (ι L x) m) = B.act (ι L x) (f m)) :=
  ⟨fun h x => h (ι L x), intertwines_of_generators A.act B.act f⟩

/-- Restriction along the actual generator map gives the signed Lie action. -/
def restrict (A : EnvelopingModule L G) : GradedModule L G where
  act := A.act.toLinearMap.comp (ι L)
  act_mem := by
    intro i j x m hx hm
    exact A.act_mem (ι_mem_piece L hx) hm
  map_bracket := by
    intro i j x y hx hy
    change A.act (ι L (L.bracket x y)) = _
    rw [← generator_relation L hx hy, map_sub, map_mul, map_smul, map_mul]
    rfl

private theorem relations_le_ker (A : GradedModule L G) :
    (relationIdeal L).ringCon ≤ RingCon.ker (TensorAlgebra.lift k A.act).toRingHom := by
  change (relationIdeal L).ringCon ≤ (TwoSidedIdeal.ker (TensorAlgebra.lift k A.act)).ringCon
  apply TwoSidedIdeal.ringCon_le_iff.mp
  apply TwoSidedIdeal.span_le.mpr
  rintro a ⟨i, j, x, y, hx, hy, rfl⟩
  apply (TwoSidedIdeal.mem_ker (TensorAlgebra.lift k A.act)).mpr
  simp only [SuperEnveloping.Construction.relator, map_sub, map_mul, map_smul,
    TensorAlgebra.lift_ι_apply, A.map_bracket hx hy, sub_self]

private def extendAction (A : GradedModule L G) : Enveloping L →ₐ[k] Module.End k M :=
  (relationIdeal L).ringCon.liftₐ (TensorAlgebra.lift k A.act) (relations_le_ker A)

private theorem extendAction_ι (A : GradedModule L G) (x : V) :
    extendAction A (ι L x) = A.act x :=
  TensorAlgebra.lift_ι_apply A.act x

private theorem parity_ι (x : V) :
    SuperEnveloping.parity L (ι L x) = ι L (generatorParity L.grading x) := by
  change SuperEnveloping.parity L (quotientMap L (TensorAlgebra.ι k x)) = _
  rw [parity_quotientMap]
  simp [SuperEnveloping.Construction.tensorParity, SuperEnveloping.Construction.ι]

private theorem extendAction_commutes_parity (A : GradedModule L G) (a : Enveloping L)
    (m : M) : generatorParity G (extendAction A a m) =
      extendAction A (SuperEnveloping.parity L a) (generatorParity G m) := by
  apply intertwines_of_generators (extendAction A)
    ((extendAction A).comp (SuperEnveloping.parity L)) (generatorParity G) _ a m
  suffices h : A.act.compr₂ (generatorParity G) =
      (A.act.comp (generatorParity L.grading)).compl₂ (generatorParity G) by
    intro x n
    simpa only [AlgHom.comp_apply, parity_ι, extendAction_ι, LinearMap.compr₂_apply,
      LinearMap.compl₂_apply, LinearMap.comp_apply] using
      congrArg (fun f : V →ₗ[k] M →ₗ[k] M => f x n) h
  apply linearMap_ext_homogeneous L.grading
  intro i x hx
  apply linearMap_ext_homogeneous G
  intro j n hn
  simp only [LinearMap.compr₂_apply, LinearMap.compl₂_apply, LinearMap.comp_apply,
    generatorParity_apply G (A.act_mem hx hn), generatorParity_apply L.grading hx,
    generatorParity_apply G hn, map_smul, LinearMap.smul_apply, smul_smul]
  rw [parityScalar_add, mul_comm (parityScalar k i) (parityScalar k j)]

/-- The tensor action descends to the enveloping quotient and preserves the parity rule. -/
def extend (A : GradedModule L G) : EnvelopingModule L G where
  act := extendAction A
  act_mem := by
    intro i j a m ha hm
    apply mem_piece_of_generatorParity
    have ha' : SuperEnveloping.parity L a = parityScalar k i • a := (mem_paritySpace ..).mp ha
    simp only [extendAction_commutes_parity, ha', generatorParity_apply G hm, map_smul,
      LinearMap.smul_apply, smul_smul, parityScalar_add, mul_comm]

@[simp] theorem extend_act_ι (A : GradedModule L G) (x : V) :
    (extend A).act (ι L x) = A.act x :=
  extendAction_ι A x

@[simp] theorem restrict_act (A : EnvelopingModule L G) (x : V) :
    (restrict A).act x = A.act (ι L x) :=
  rfl

private theorem action_ext {A B : Enveloping L →ₐ[k] Module.End k M}
    (h : ∀ x : V, A (ι L x) = B (ι L x)) : A = B := by
  apply RingCon.Quotient.hom_extₐ
  apply TensorAlgebra.hom_ext
  exact LinearMap.ext h

/-- Restriction and extension on a fixed graded vector space. -/
def moduleEquiv (L : LieSuperalgebra k V) (G : Grading k M) :
    GradedModule L G ≃ EnvelopingModule L G where
  toFun := extend
  invFun := restrict
  left_inv := by
    intro A
    have h : (restrict (extend A)).act = A.act := LinearMap.ext (extend_act_ι A)
    cases hA : restrict (extend A)
    rw [hA] at h
    cases A
    congr 1
  right_inv := by
    intro A
    have h : (extend (restrict A)).act = A.act := action_ext (extend_act_ι (restrict A))
    cases hA : extend (restrict A)
    rw [hA] at h
    cases A
    congr 1

/-- Extension and restriction of morphisms use the same underlying linear maps. -/
def homEquiv (A : GradedModule L G) (B : GradedModule L H) :
    GradedModule.Hom A B ≃ EnvelopingModule.Hom (extend A) (extend B) where
  toFun f :=
    { toLinearMap := f.toLinearMap
      map_piece := f.map_piece
      intertwines := (intertwines_iff_on_generators (extend A) (extend B) f.toLinearMap).mpr
        (fun x m => by simpa only [extend_act_ι] using f.intertwines x m) }
  invFun f :=
    { toLinearMap := f.toLinearMap
      map_piece := f.map_piece
      intertwines := fun x m => by simpa only [extend_act_ι] using f.intertwines (ι L x) m }
  left_inv := fun f => by cases f; rfl
  right_inv := fun f => by cases f; rfl

/-- The graded module and graded intertwiner correspondences for the enveloping algebra. -/
theorem gradedModulesAgree :
    Specs.LieNotes.SuperRestricted.SuperEnvelopingModules.gradedModulesAgreeType := by
  intro k V _ _ _ _ L M _ _ G N _ _ H
  exact ⟨moduleEquiv L G, moduleEquiv L H, extend_act_ι, extend_act_ι, restrict_act, restrict_act,
    fun A B => ⟨homEquiv A B, fun _ => rfl⟩⟩

end

end LieNotes.SuperRestricted.SuperEnvelopingModules
