import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Descent.AmitsurTotalComplex
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Model.Complexes.SequentialHomotopyLimits
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Descent.AmitsurHorizontalLimit

/-! Horizontal finite-column limits of the Amitsur totalization. -/

namespace DerivedFormalization.Descent.AmitsurHorizontalLimit

open CategoryTheory CategoryTheory.Limits Opposite
open DerivedFormalization.Descent.AmitsurTotalComplex (rowIndex)
open DerivedFormalization.Descent.AmitsurTotalComplex.Independent
open Specs.DerivedFormalization.SequentialHomotopyLimits (holimValue)
open Specs.DerivedFormalization.Cochains (qValue)
open Specs.DerivedFormalization.Descent.AmitsurHorizontalLimit
  (SurjectiveTransitions ToLimitIsIso ToLimitNaturality ToHolimQuasiIso
    ToHolimNaturality DerivedComparisonIsIso NaturalLimitIso NaturalDerivedIso truncate_stageMap)

universe u v w

attribute [local instance] HasDerivedCategory.standard

noncomputable section

abbrev stageMap := @Specs.DerivedFormalization.Descent.AmitsurHorizontalLimit.stageMap.{u, v, w}
abbrev tower := @Specs.DerivedFormalization.Descent.AmitsurHorizontalLimit.tower.{u, v, w}
abbrev towerMap := @Specs.DerivedFormalization.Descent.AmitsurHorizontalLimit.towerMap.{u, v, w}
abbrev towerFunctor := @Specs.DerivedFormalization.Descent.AmitsurHorizontalLimit.towerFunctor.{u, v, w}
abbrev restrictionCone :=
  @Specs.DerivedFormalization.Descent.AmitsurHorizontalLimit.restrictionCone.{u, v, w}
abbrev toLimit := @Specs.DerivedFormalization.Descent.AmitsurHorizontalLimit.toLimit.{u, v, w}
abbrev toHolim := @Specs.DerivedFormalization.Descent.AmitsurHorizontalLimit.toHolim.{u, v, w}

theorem surjective_transitions : SurjectiveTransitions.{u, v, w} := by
  intro A B _ _ _ X k i
  exact projection_surjective A B X (Nat.le_add_right k 1) i

section Gluing

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
  (X : Input.{u, w} A)

/-- The coordinate at column p is read at the first stage that retains it. -/
private def glueComponent (s : Cone (tower A B X)) (i : ℤ) :
    s.pt.X i ⟶ (total A B X).X i :=
  ModuleCat.ofHom (LinearMap.pi fun p : ℕ =>
    (LinearMap.proj (⟨p, Nat.lt_succ_self p⟩ : Fin (p + 1))).comp
      ((s.π.app (op p)).f i).hom)

@[reassoc]
private theorem glueComponent_factor (s : Cone (tower A B X)) (i : ℤ) (k : ℕ) :
    glueComponent A B X s i ≫ (truncate A B X k).f i = (s.π.app (op k)).f i := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext p
  change (truncate A B X k).f i (glueComponent A B X s i x) p =
    (s.π.app (op k)).f i x p
  rw [truncate_apply]
  let h : (p : ℕ) ≤ k := Nat.le_of_lt_succ p.isLt
  let last : Fin ((p : ℕ) + 1) := ⟨p, Nat.lt_succ_self _⟩
  have compat :
      s.π.app (op k) ≫ projection A B X h = s.π.app (op (p : ℕ)) :=
    s.w (homOfLE h).op
  have hcoord := congrArg (fun g => g.f i x last) compat
  change (projection A B X h).f i ((s.π.app (op k)).f i x) last =
    (s.π.app (op (p : ℕ))).f i x last at hcoord
  rw [projection_apply] at hcoord
  exact hcoord.symm

private theorem truncate_jointly_monic {M : ModuleCat.{max u v w} A} {i : ℤ}
    {f g : M ⟶ (total A B X).X i}
    (h : ∀ k, f ≫ (truncate A B X k).f i = g ≫ (truncate A B X k).f i) :
    f = g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext p
  let last : Fin (p + 1) := ⟨p, Nat.lt_succ_self p⟩
  have hcoord := congrArg (fun m : M ⟶ (finiteTotal A B X p).X i => m x last) (h p)
  change (truncate A B X p).f i (f x) last = (truncate A B X p).f i (g x) last at hcoord
  rw [truncate_apply A B X, truncate_apply A B X] at hcoord
  exact hcoord

private def glue (s : Cone (tower A B X)) : s.pt ⟶ total A B X :=
  CochainComplex.ofHom (glueComponent A B X s) (fun i => by
    apply truncate_jointly_monic A B X
    intro k
    rw [Category.assoc, ← (truncate A B X k).comm, glueComponent_factor_assoc,
      Category.assoc, glueComponent_factor]
    exact (s.π.app (op k)).comm i (i + 1))

/-- The cone of coordinate restrictions is limiting. -/
private def restrictionConeIsLimit : IsLimit (restrictionCone A B X) where
  lift := glue A B X
  fac s k := HomologicalComplex.hom_ext _ _ (fun i => glueComponent_factor A B X s i k.unop)
  uniq s m h := by
    apply HomologicalComplex.hom_ext
    intro i
    apply truncate_jointly_monic A B X
    intro k
    exact (congrArg (fun g => g.f i) (h (op k))).trans
      (glueComponent_factor A B X s i k).symm

end Gluing

theorem toLimit_isIso : ToLimitIsIso.{u, v, w} := by
  intro A B _ _ _ X
  change IsIso (limit.lift _ (restrictionCone A B X))
  let e := (restrictionConeIsLimit A B X).conePointUniqueUpToIso (limit.isLimit (tower A B X))
  have he : e.hom = limit.lift (tower A B X) (restrictionCone A B X) := by
    apply limit.hom_ext
    intro k
    rw [limit.lift_π]
    exact IsLimit.conePointUniqueUpToIso_hom_comp (restrictionConeIsLimit A B X)
      (limit.isLimit (tower A B X)) k
  rw [← he]
  infer_instance

@[reassoc]
theorem toLimit_π (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    (X : Input.{u, w} A) (k : ℕ) :
    toLimit A B X ≫ limit.π (tower A B X) (op k) = truncate A B X k :=
  limit.lift_π (restrictionCone A B X) (op k)

theorem toLimit_naturality : ToLimitNaturality.{u, v, w} := by
  intro A B _ _ _ X Y f
  apply limit.hom_ext
  intro k
  change map A B f ≫ limit.lift _ (restrictionCone A B Y) ≫ limit.π _ k =
    (limit.lift _ (restrictionCone A B X) ≫ limMap (towerMap A B f)) ≫ limit.π _ k
  rw [limit.lift_π, Category.assoc, limMap_π, limit.lift_π_assoc]
  exact (truncate_stageMap A B f k.unop).symm

theorem toHolim_quasiIso : ToHolimQuasiIso.{u, v, w} := by
  intro A B _ _ _ X
  let : IsIso (toLimit A B X) := toLimit_isIso A B X
  let : QuasiIso (SequentialHomotopyLimits.comparison (tower A B X)) :=
    SequentialHomotopyLimits.comparison_quasiIso (tower A B X) (surjective_transitions A B X)
  change QuasiIso (toLimit A B X ≫ SequentialHomotopyLimits.comparison (tower A B X))
  infer_instance

theorem toHolim_naturality : ToHolimNaturality.{u, v, w} := by
  intro A B _ _ _ X Y f
  change map A B f ≫ toLimit A B Y ≫ SequentialHomotopyLimits.comparison (tower A B Y) =
    (toLimit A B X ≫ SequentialHomotopyLimits.comparison (tower A B X)) ≫
      holimValue.map (towerMap A B f)
  rw [← Category.assoc, toLimit_naturality A B f, Category.assoc,
    SequentialHomotopyLimits.comparison_naturality (towerMap A B f), Category.assoc]

theorem derivedComparison_isIso : DerivedComparisonIsIso.{u, v, w} := by
  intro A B _ _ _ X
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{max u v w} A) (toHolim A B X)).2
    (toHolim_quasiIso A B X)

section NaturalComparisons

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]

/-- The canonical chain isomorphism onto the ordinary limit, natural in X. -/
def limitIso : functor.{u, v, w} A B ≅ towerFunctor A B ⋙ lim := by
  let e (X : Input.{u, w} A) : total A B X ≅ limit (tower A B X) :=
    letI := toLimit_isIso A B X
    asIso (toLimit A B X)
  exact NatIso.ofComponents e (fun f => toLimit_naturality A B f)

/-- The canonical identification with the shifted-cone model in D(A). -/
def derivedIso : functor.{u, v, w} A B ⋙ qValue A ≅
    (towerFunctor A B ⋙ holimValue) ⋙ qValue A := by
  let e (X : Input.{u, w} A) :
      (qValue A).obj (total A B X) ≅ (qValue A).obj (holimValue.obj (tower A B X)) :=
    letI := derivedComparison_isIso A B X
    asIso ((qValue A).map (toHolim A B X))
  refine NatIso.ofComponents e (fun f => ?_)
  change (qValue A).map (map A B f) ≫ (qValue A).map (toHolim A B _) =
    (qValue A).map (toHolim A B _) ≫ (qValue A).map (holimValue.map (towerMap A B f))
  rw [← Functor.map_comp, ← Functor.map_comp, toHolim_naturality A B f]

end NaturalComparisons

theorem natural_limit_iso : NaturalLimitIso.{u, v, w} := by
  intro A B _ _ _
  exact ⟨limitIso A B, fun _ => rfl⟩

theorem natural_derived_iso : NaturalDerivedIso.{u, v, w} := by
  intro A B _ _ _
  exact ⟨derivedIso A B, fun _ => rfl⟩

end

end DerivedFormalization.Descent.AmitsurHorizontalLimit
