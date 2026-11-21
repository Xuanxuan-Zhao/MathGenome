import MathGenome.Internal.AlgebraCore.Specs.P103.Ch10.HomologySequence
import MathGenome.Internal.AlgebraCore.P103.Ch10.Complexes

namespace P103.Ch10.HomologySequence
open CategoryTheory P103.Specs.Ch10.Complexes
open P103.Specs.Ch10.HomologySequence
noncomputable section
universe u v w
variable {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
variable {A B C : HomologicalComplex (ModuleCat.{v} R) c}

lemma comm_apply {D E : HomologicalComplex (ModuleCat.{v} R) c}
    (f : D ⟶ E) (n m : ι) (x : D.X n) :
    (E.d n m).hom ((f.f n).hom x) = (f.f m).hom ((D.d n m).hom x) :=
  DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (f.comm n m)) x

lemma square_zero (D : HomologicalComplex (ModuleCat.{v} R) c)
    (l n m : ι) (x : D.X l) : (D.d n m).hom ((D.d l n).hom x) = 0 :=
  DFunLike.congr_fun (P103.Ch10.Complexes.differential_squared D l n m) x

lemma cycle_iff (D : HomologicalComplex (ModuleCat.{v} R) c)
    {n m : ι} (h : c.Rel n m) (x : D.X n) :
    x ∈ cycles D n ↔ (D.d n m).hom x = 0 := by
  change (D.d n (c.next n)).hom x = 0 ↔ _
  rw [c.next_eq' h]

lemma boundary_iff (D : HomologicalComplex (ModuleCat.{v} R) c)
    {n m : ι} (h : c.Rel n m) (x : D.X m) :
    x ∈ boundaries D m ↔ ∃ y, (D.d n m).hom y = x := by
  change (∃ y, (D.d (c.prev m) m).hom y = x) ↔ _
  rw [c.prev_eq' h]

lemma differential_cycle (D : HomologicalComplex (ModuleCat.{v} R) c)
    (n m : ι) (x : D.X n) : (D.d n m).hom x ∈ cycles D m :=
  square_zero D n m (c.next m) x

lemma class_zero_iff (D : HomologicalComplex (ModuleCat.{v} R) c)
    (n : ι) (z : cycles D n) :
    homologyClass D n z = 0 ↔ z.val ∈ boundaries D n :=
  Submodule.Quotient.mk_eq_zero (cycleBoundaries D n)

variable (i : A ⟶ B) (p : B ⟶ C) (hs : DegreewiseExact i p)
variable {n m : ι} (h : c.Rel n m)
include hs h

/-- Lift a cycle and its differential; the latter lift is itself a cycle. -/
lemma lifts (z : cycles C n) : ∃ (b : B.X n) (a : cycles A m),
    (p.f n).hom b = z.val ∧ (i.f m).hom a.val = (B.d n m).hom b := by
  obtain ⟨b, hb⟩ := (hs n).2.2 z.val
  have hp : (p.f m).hom ((B.d n m).hom b) = 0 := by
    rw [← comm_apply, hb]
    exact (cycle_iff C h z.val).mp z.property
  obtain ⟨a, ha⟩ := ((hs m).2.1 _).mp hp
  have hz : a ∈ cycles A m := by
    change (A.d m (c.next m)).hom a = 0
    apply (hs (c.next m)).1
    rw [map_zero, ← comm_apply, ha, square_zero]
  exact ⟨b, ⟨a, hz⟩, hb, ha⟩

/-- Any two lifts of the same cycle differ by a boundary in A. -/
lemma lift_classes_eq (z : cycles C n) (b₁ b₂ : B.X n) (a₁ a₂ : cycles A m)
    (hb₁ : (p.f n).hom b₁ = z.val) (hb₂ : (p.f n).hom b₂ = z.val)
    (ha₁ : (i.f m).hom a₁.val = (B.d n m).hom b₁)
    (ha₂ : (i.f m).hom a₂.val = (B.d n m).hom b₂) :
    homologyClass A m a₁ = homologyClass A m a₂ := by
  obtain ⟨x, hx⟩ := ((hs n).2.1 (b₁ - b₂)).mp
    (by rw [map_sub, hb₁, hb₂, sub_self])
  apply (P103.Ch10.Complexes.homologyClass_eq_iff A m a₁ a₂).mpr
  apply (boundary_iff A h _).mpr
  refine ⟨x, ?_⟩
  apply (hs m).1
  rw [map_sub, ha₁, ha₂, ← map_sub, ← hx, comm_apply]

lemma exists_connecting : ∃ δ : Homology C n →ₗ[R] Homology A m,
    Connecting i p n m δ := by
  classical
  choose b a hb ha using lifts i p hs h
  let f : cycles C n → Homology A m := fun z => homologyClass A m (a z)
  have hf : ∀ z b' a', (p.f n).hom b' = z.val →
      (i.f m).hom a'.val = (B.d n m).hom b' → f z = homologyClass A m a' := by
    intro z b' a' hb' ha'
    exact lift_classes_eq i p hs h z (b z) b' (a z) a' (hb z) hb' (ha z) ha'
  let F : cycles C n →ₗ[R] Homology A m :=
    { toFun := f
      map_add' := by
        intro z t
        rw [hf (z + t) (b z + b t) (a z + a t)]
        · exact map_add _ _ _
        · change (p.f n).hom (b z + b t) = z.val + t.val
          simp only [map_add, hb]
        · change (i.f m).hom ((a z).val + (a t).val) = _
          simp only [map_add, ha]
      map_smul' := by
        intro r z
        rw [hf (r • z) (r • b z) (r • a z)]
        · exact map_smul _ _ _
        · change (p.f n).hom (r • b z) = r • z.val
          simp only [map_smul, hb]
        · change (i.f m).hom (r • (a z).val) = _
          simp only [map_smul, ha] }
  have hF : cycleBoundaries C n ≤ LinearMap.ker F := by
    intro z hz
    obtain ⟨x, hx⟩ := hz
    obtain ⟨y, hy⟩ := (hs (c.prev n)).2.2 x
    change f z = 0
    rw [hf z ((B.d (c.prev n) n).hom y) 0]
    · exact map_zero _
    · rw [← comm_apply, hy, hx]
      rfl
    · change (i.f m).hom 0 = _
      rw [map_zero, square_zero]
  exact ⟨(cycleBoundaries C n).liftQ F hF, fun z b' a' hb' ha' => hf z b' a' hb' ha'⟩

/-- Exactness at H(B): remove the differential of a lift of the boundary. -/
lemma exact_middle : Function.Exact (homologyMap i n) (homologyMap p n) := by
  intro q
  obtain ⟨z, rfl⟩ := (cycleBoundaries B n).mkQ_surjective q
  constructor
  · intro hz
    change homologyClass C n (cyclesMap p n z) = 0 at hz
    obtain ⟨x, hx⟩ := (class_zero_iff C n _).mp hz
    obtain ⟨y, hy⟩ := (hs (c.prev n)).2.2 x
    have hp : (p.f n).hom (z.val - (B.d (c.prev n) n).hom y) = 0 := by
      rw [map_sub, ← comm_apply, hy, hx]
      exact sub_self _
    obtain ⟨a, ha⟩ := ((hs n).2.1 _).mp hp
    have haz : a ∈ cycles A n := by
      apply (cycle_iff A h _).mpr
      apply (hs m).1
      rw [map_zero, ← comm_apply, ha, map_sub,
        (cycle_iff B h z.val).mp z.property, square_zero, sub_self]
    refine ⟨homologyClass A n ⟨a, haz⟩, ?_⟩
    change homologyClass B n (cyclesMap i n ⟨a, haz⟩) = homologyClass B n z
    apply (P103.Ch10.Complexes.homologyClass_eq_iff B n _ _).mpr
    change ∃ y', (B.d (c.prev n) n).hom y' = (i.f n).hom a - z.val
    refine ⟨-y, ?_⟩
    rw [ha, map_neg]
    abel
  · rintro ⟨q, hq⟩
    obtain ⟨a, rfl⟩ := (cycleBoundaries A n).mkQ_surjective q
    rw [← hq]
    change homologyClass C n (cyclesMap p n (cyclesMap i n a)) = 0
    apply (class_zero_iff C n _).mpr
    change (p.f n).hom ((i.f n).hom a.val) ∈ boundaries C n
    rw [(hs n).2.1.apply_apply_eq_zero]
    exact Submodule.zero_mem _

variable (δ : Homology C n →ₗ[R] Homology A m) (hδ : Connecting i p n m δ)
include hδ

/-- Exactness at H(C): a zero connecting class permits a cycle lift. -/
lemma exact_before_connecting : Function.Exact (homologyMap p n) δ := by
  intro q
  obtain ⟨z, rfl⟩ := (cycleBoundaries C n).mkQ_surjective q
  constructor
  · intro hz
    obtain ⟨b, a, hb, ha⟩ := lifts i p hs h z
    change δ (homologyClass C n z) = 0 at hz
    rw [hδ z b a hb ha] at hz
    obtain ⟨x, hx⟩ := (boundary_iff A h a.val).mp ((class_zero_iff A m a).mp hz)
    have hbz : b - (i.f n).hom x ∈ cycles B n := by
      apply (cycle_iff B h _).mpr
      rw [map_sub, comm_apply, hx, ← ha, sub_self]
    refine ⟨homologyClass B n ⟨b - (i.f n).hom x, hbz⟩, ?_⟩
    change homologyClass C n (cyclesMap p n ⟨_, hbz⟩) = homologyClass C n z
    apply congrArg (homologyClass C n)
    apply Subtype.ext
    change (p.f n).hom (b - (i.f n).hom x) = z.val
    rw [map_sub, (hs n).2.1.apply_apply_eq_zero, sub_zero, hb]
  · rintro ⟨q, hq⟩
    obtain ⟨b, rfl⟩ := (cycleBoundaries B n).mkQ_surjective q
    rw [← hq]
    change δ (homologyClass C n (cyclesMap p n b)) = 0
    rw [hδ (cyclesMap p n b) b.val 0 rfl]
    · exact map_zero _
    · change (i.f m).hom 0 = (B.d n m).hom b.val
      rw [map_zero, (cycle_iff B h b.val).mp b.property]

/-- Exactness at H(A): a boundary image is exactly a connecting class. -/
lemma exact_after_connecting : Function.Exact δ (homologyMap i m) := by
  intro q
  obtain ⟨a, rfl⟩ := (cycleBoundaries A m).mkQ_surjective q
  constructor
  · intro ha
    change homologyClass B m (cyclesMap i m a) = 0 at ha
    obtain ⟨b, hb⟩ := (boundary_iff B h _).mp ((class_zero_iff B m _).mp ha)
    have hz : (p.f n).hom b ∈ cycles C n := by
      apply (cycle_iff C h _).mpr
      rw [comm_apply, hb]
      exact (hs m).2.1.apply_apply_eq_zero a.val
    exact ⟨homologyClass C n ⟨(p.f n).hom b, hz⟩,
      hδ ⟨_, hz⟩ b a rfl hb.symm⟩
  · rintro ⟨q, hq⟩
    obtain ⟨z, rfl⟩ := (cycleBoundaries C n).mkQ_surjective q
    obtain ⟨b, a', hb, ha'⟩ := lifts i p hs h z
    rw [← hq]
    change homologyMap i m (δ (homologyClass C n z)) = 0
    rw [hδ z b a' hb ha']
    change homologyClass B m (cyclesMap i m a') = 0
    apply (class_zero_iff B m _).mpr
    exact (boundary_iff B h _).mpr ⟨b, ha'.symm⟩

/-- The representative formula alone forces uniqueness. -/
lemma connecting_unique (ε : Homology C n →ₗ[R] Homology A m)
    (hε : Connecting i p n m ε) : ε = δ := by
  apply (cycleBoundaries C n).quot_hom_ext
  intro z
  obtain ⟨b, a, hb, ha⟩ := lifts i p hs h z
  exact (hε z b a hb ha).trans (hδ z b a hb ha).symm

omit hs h hδ in
/-- Arbitrary shape, with only an adjacent-degree relation required. -/
theorem sequence :
  ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
    {A B C : HomologicalComplex (ModuleCat.{v} R) c}
    (i : A ⟶ B) (p : B ⟶ C), DegreewiseExact i p →
    ∀ (n m : ι), c.Rel n m →
    ∃! δ : Homology C n →ₗ[R] Homology A m,
      Connecting i p n m δ ∧ SequenceExact i p n m δ := by
  intro R _ ι c A B C i p hs n m h
  obtain ⟨δ, hδ⟩ := exists_connecting i p hs h
  refine ⟨δ, ⟨hδ, exact_middle i p hs h,
    exact_before_connecting i p hs h δ hδ, exact_after_connecting i p hs h δ hδ⟩, ?_⟩
  intro ε hε
  exact connecting_unique i p hs h δ hδ ε hε.1

end

noncomputable section
theorem chainSequence :
  ∀ {R : Type u} [Ring R] {A B C : Chain.{u,v} R}
    (i : A ⟶ B) (p : B ⟶ C), DegreewiseExact i p →
    ∃ δ : ∀ n : ℤ, Homology C n →ₗ[R] Homology A (n - 1),
      ∀ n, Connecting i p n (n - 1) (δ n) ∧ SequenceExact i p n (n - 1) (δ n) := by
  intro R _ A B C i p hs
  have H (n : ℤ) := (sequence i p hs n (n - 1) (by
    change n - 1 + 1 = n
    omega)).exists
  choose δ hδ using H
  exact ⟨δ, hδ⟩

theorem cochainSequence :
  ∀ {R : Type u} [Ring R] {A B C : Cochain.{u,v} R}
    (i : A ⟶ B) (p : B ⟶ C), DegreewiseExact i p →
    ∃ δ : ∀ n : ℤ, Homology C n →ₗ[R] Homology A (n + 1),
      ∀ n, Connecting i p n (n + 1) (δ n) ∧ SequenceExact i p n (n + 1) (δ n) := by
  intro R _ A B C i p hs
  have H (n : ℤ) := (sequence i p hs n (n + 1) (by rfl)).exists
  choose δ hδ using H
  exact ⟨δ, hδ⟩

theorem sequence_right :
  ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
    {A B C : HomologicalComplex (ModuleCat.{v} Rᵐᵒᵖ) c}
    (i : A ⟶ B) (p : B ⟶ C), DegreewiseExact i p →
    ∀ (n m : ι), c.Rel n m →
    ∃! δ : Homology C n →ₗ[Rᵐᵒᵖ] Homology A m,
      Connecting i p n m δ ∧ SequenceExact i p n m δ := by
  intro R _ ι c A B C i p hs n m h
  exact sequence i p hs n m h

theorem naturality :
  ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
    {A B C : HomologicalComplex (ModuleCat.{v} R) c}
    {A' B' C' : HomologicalComplex (ModuleCat.{v} R) c}
    (i : A ⟶ B) (p : B ⟶ C) (i' : A' ⟶ B') (p' : B' ⟶ C')
    (α : A ⟶ A') (β : B ⟶ B') (γ : C ⟶ C')
    (_hi : i ≫ β = α ≫ i') (_hp : p ≫ γ = β ≫ p'),
    DegreewiseExact i p → DegreewiseExact i' p' →
    ∀ (n m : ι), c.Rel n m →
    ∀ (δ : Homology C n →ₗ[R] Homology A m)
      (ε : Homology C' n →ₗ[R] Homology A' m),
      Connecting i p n m δ → Connecting i' p' n m ε →
      (homologyMap β n).comp (homologyMap i n) =
        (homologyMap i' n).comp (homologyMap α n) ∧
      (homologyMap γ n).comp (homologyMap p n) =
        (homologyMap p' n).comp (homologyMap β n) ∧
      (homologyMap α m).comp δ = ε.comp (homologyMap γ n) ∧
      (homologyMap β m).comp (homologyMap i m) =
        (homologyMap i' m).comp (homologyMap α m) ∧
      (homologyMap γ m).comp (homologyMap p m) =
        (homologyMap p' m).comp (homologyMap β m) := by
  intro R _ ι c A B C A' B' C' i p i' p' α β γ hi hp hs hs' n m h δ ε hδ hε
  have hiH (j : ι) :
      (homologyMap β j).comp (homologyMap i j) =
        (homologyMap i' j).comp (homologyMap α j) := by
    simpa only [P103.Ch10.Complexes.homologyMap_comp] using
      congrArg (fun f => homologyMap f j) hi
  have hpH (j : ι) :
      (homologyMap γ j).comp (homologyMap p j) =
        (homologyMap p' j).comp (homologyMap β j) := by
    simpa only [P103.Ch10.Complexes.homologyMap_comp] using
      congrArg (fun f => homologyMap f j) hp
  refine ⟨hiH n, hpH n, ?_, hiH m, hpH m⟩
  apply (cycleBoundaries C n).quot_hom_ext
  intro z
  obtain ⟨b, a, hb, ha⟩ := lifts i p hs h z
  change homologyMap α m (δ (homologyClass C n z)) =
    ε (homologyClass C' n (cyclesMap γ n z))
  rw [hδ z b a hb ha]
  change homologyClass A' m (cyclesMap α m a) =
    ε (homologyClass C' n (cyclesMap γ n z))
  symm
  apply hε (cyclesMap γ n z) ((β.f n).hom b) (cyclesMap α m a)
  · have H := congrArg (fun f : B ⟶ C' => (f.f n).hom b) hp
    change (γ.f n).hom ((p.f n).hom b) =
      (p'.f n).hom ((β.f n).hom b) at H
    change (p'.f n).hom ((β.f n).hom b) = (γ.f n).hom z.val
    rw [← H, hb]
  · have H := congrArg (fun f : A ⟶ B' => (f.f m).hom a.val) hi
    change (β.f m).hom ((i.f m).hom a.val) =
      (i'.f m).hom ((α.f m).hom a.val) at H
    change (i'.f m).hom ((α.f m).hom a.val) =
      (B'.d n m).hom ((β.f n).hom b)
    rw [← H, ha, comm_apply]

theorem homology_supported :
  ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
    (C : HomologicalComplex (ModuleCat.{v} R) c) (s : Set ι),
    SupportedIn C s → ∀ n, n ∉ s → Subsingleton (Homology C n) := by
  intro R _ ι c C s hs n hn
  let := hs n hn
  infer_instance

lemma exact_injective_of_subsingleton {R M N P : Type*} [Ring R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P] [Subsingleton M]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (h : Function.Exact f g) :
    Function.Injective g := by
  apply (LinearMap.injective_iff_eq_zero_of_exact h).mpr
  ext x
  rw [Subsingleton.elim x 0, map_zero]
  rfl

lemma exact_surjective_of_subsingleton {R M N P : Type*} [Ring R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P] [Subsingleton P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (h : Function.Exact f g) :
    Function.Surjective f := by
  apply (LinearMap.surjective_iff_eq_zero_of_exact h).mpr
  ext x
  exact Subsingleton.elim _ _

theorem zero_endpoints :
  ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
    {A B C : HomologicalComplex (ModuleCat.{v} R) c}
    (i : A ⟶ B) (p : B ⟶ C) (n m : ι)
    (δ : Homology C n →ₗ[R] Homology A m), SequenceExact i p n m δ →
    (Subsingleton (Homology A n) → Function.Injective (homologyMap p n)) ∧
    (Subsingleton (Homology C n) → Function.Surjective (homologyMap i n) ∧
      Function.Injective (homologyMap i m)) ∧
    (Subsingleton (Homology A m) → Function.Surjective (homologyMap p n)) ∧
    (Subsingleton (Homology B n) → Function.Injective δ) ∧
    (Subsingleton (Homology B m) → Function.Surjective δ) := by
  intro R _ ι c A B C i p n m δ hs
  rcases hs with ⟨hB, hC, hA⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h
    let := h
    exact exact_injective_of_subsingleton _ _ hB
  · intro h
    let := h
    exact ⟨exact_surjective_of_subsingleton _ _ hB,
      exact_injective_of_subsingleton _ _ hA⟩
  · intro h
    let := h
    exact exact_surjective_of_subsingleton _ _ hC
  · intro h
    let := h
    exact exact_injective_of_subsingleton _ _ hC
  · intro h
    let := h
    exact exact_surjective_of_subsingleton _ _ hA

end
end P103.Ch10.HomologySequence
