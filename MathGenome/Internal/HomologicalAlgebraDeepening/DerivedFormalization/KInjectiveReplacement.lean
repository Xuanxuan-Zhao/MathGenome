import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.InjectiveTruncationTower
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.TowerKInjectivity
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.KInjectiveReplacement

namespace DerivedFormalization

open CategoryTheory CategoryTheory.Limits Opposite
open Specs.DerivedFormalization.TowerExactSequence (transition)

universe u v

/-- A limit of a countable tower of injectives with split epimorphic transitions
is injective. Extend into each stage and correct the next extension using the
section of the transition, preserving its restriction along the monomorphism. -/
private theorem injective_of_split_tower_limit {C : Type*} [Category C] [Preadditive C]
    {A : ℕᵒᵖ ⥤ C} {c : Cone A} (hc : IsLimit c)
    (hA : ∀ n : ℕ, Injective (A.obj (op n)))
    (hs : ∀ n : ℕ, ∃ s : A.obj (op n) ⟶ A.obj (op (n + 1)),
      s ≫ A.map (homOfLE (Nat.le_add_right n 1)).op = 𝟙 _) :
    Injective c.pt := by
  refine ⟨fun {X Y} g f _ ↦ ?_⟩
  choose s hs using hs
  let liftAt (n : ℕ) : Y ⟶ A.obj (op n) :=
    Injective.factorThru (g ≫ c.π.app (op n)) f
  have liftAt_fac (n : ℕ) : f ≫ liftAt n = g ≫ c.π.app (op n) :=
    Injective.comp_factorThru _ _
  let extend : (n : ℕ) → Y ⟶ A.obj (op n) :=
    Nat.rec (liftAt 0) (fun n prev ↦ liftAt (n + 1) +
      (prev - liftAt (n + 1) ≫ A.map (homOfLE (Nat.le_add_right n 1)).op) ≫ s n)
  have extend_succ (n : ℕ) : extend (n + 1) = liftAt (n + 1) +
      (extend n - liftAt (n + 1) ≫ A.map (homOfLE (Nat.le_add_right n 1)).op) ≫ s n := rfl
  have extend_step (n : ℕ) :
      extend (n + 1) ≫ A.map (homOfLE (Nat.le_add_right n 1)).op = extend n := by
    simp only [extend_succ, Preadditive.add_comp, Category.assoc, hs, Category.comp_id]
    rw [add_comm, sub_add_cancel]
  have extend_fac (n : ℕ) : f ≫ extend n = g ≫ c.π.app (op n) := by
    induction n with
    | zero => exact liftAt_fac 0
    | succ n ih =>
        simp only [extend_succ, Preadditive.comp_add, ← Category.assoc, Preadditive.comp_sub,
          liftAt_fac, ih, Category.assoc g, c.w, sub_self, zero_comp, add_zero]
  let d : Cone A := Cone.mk Y (NatTrans.ofOpSequence extend (fun n ↦ by
    change 𝟙 Y ≫ extend n = _
    rw [Category.id_comp, extend_step]))
  refine ⟨hc.lift d, hc.hom_ext (fun n ↦ ?_)⟩
  rw [Category.assoc, hc.fac]
  exact extend_fac n.unop

/-- Every unbounded cochain complex of modules over a commutative ring admits
a termwise monic quasi-isomorphism to a K-injective complex of injective modules. -/
theorem kInjectiveReplacement :
    Specs.DerivedFormalization.KInjectiveReplacement.replacementType.{u, v} := by
  intro R _ X
  obtain ⟨t, ht, htSurj, π, _, ⟨hπ⟩⟩ := truncationTowerExists X
  obtain ⟨I, ι, hStage, hSplit⟩ := injectiveTruncationTowerExists X t ht
  let T := Functor.ofOpSequence t
  let e : X ≅ limit T := hπ.conePointUniqueUpToIso (limit.isLimit T)
  have hSurjT (n : ℕ) (j : ℤ) : Function.Surjective ((transition T n).f j) := by
    change Function.Surjective (((Functor.ofOpSequence t).map
      (homOfLE (Nat.le_add_right n 1)).op).f j)
    rw [Functor.ofOpSequence_map_homOfLE_succ]
    exact htSurj n j
  have hSurjI (n : ℕ) (j : ℤ) : Function.Surjective ((transition I n).f j) := by
    obtain ⟨s, hs⟩ := hSplit n j
    intro x
    exact ⟨s x, congrArg (fun k : (I.obj (op n)).X j ⟶ _ ↦ k x) hs⟩
  have hQuasiIso : QuasiIso (limMap ι) :=
    towerLimitMap_quasiIso R T I ι hSurjT hSurjI (fun n ↦ (hStage n).2.2.2)
  have (n : ℕᵒᵖ) : Mono (ι.app n) :=
    HomologicalComplex.mono_of_mono_f _ (hStage n.unop).2.2.1
  refine ⟨limit I, e.hom ≫ limMap ι, fun j ↦ inferInstance, inferInstance, ?_, ?_⟩
  · refine towerLimit_isKInjective R I hSplit (fun n ↦ ?_)
    have := (hStage n).1
    have := (hStage n).2.1
    exact CochainComplex.isKInjective_of_injective (I.obj (op n)) (-(n : ℤ))
  · intro j
    let F := HomologicalComplex.eval (ModuleCat.{max u v} R) (.up ℤ) j
    exact injective_of_split_tower_limit (isLimitOfPreserves F (limit.isLimit I))
      (fun n ↦ (hStage n).2.1 j) (fun n ↦ hSplit n j)

end DerivedFormalization
