import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Brauer.FiniteCochains
import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Brauer.ScalarObstruction
import Mathlib.Algebra.Colimit.Module

/-! Continuous scalar cohomology and inflation for finite Galois stages. -/

namespace RM03.Brauer.ContinuousCohomology

open ScalarObstruction groupCohomology

universe u v

noncomputable section

variable {k : Type u} {S : Type v} [Field k] [Field S] [Algebra k S]

local instance : TopologicalSpace Sˣ := ⊥
local instance : DiscreteTopology Sˣ := ⟨rfl⟩

/-- Continuous two-cocycles with discrete coefficients in the units of the closure. -/
def continuousCocycles (k : Type u) (S : Type v) [Field k] [Field S] [Algebra k S] :
    Subgroup (ScalarCocycle k S) where
  carrier := {c | Continuous c.val}
  one_mem' := continuous_const
  mul_mem' ha hb := ha.mul hb
  inv_mem' ha := ha.inv

/-- Pointwise operations on continuous scalar one-cochains. -/
def continuousOneCochains (k : Type u) (S : Type v) [Field k] [Field S] [Algebra k S] :
    Subgroup (Gal(S/k) → Sˣ) where
  carrier := {f | Continuous f}
  one_mem' := continuous_const
  mul_mem' ha hb := ha.mul hb
  inv_mem' ha := ha.inv

/-- The subgroup of continuous scalar coboundaries, as a subgroup of continuous cocycles. -/
def continuousCoboundaries (k : Type u) (S : Type v) [Field k] [Field S] [Algebra k S] :
    Subgroup (continuousCocycles k S) where
  carrier := {c | ∃ f : continuousOneCochains k S, coboundary k S f.val = c.val}
  one_mem' := ⟨1, map_one _⟩
  mul_mem' := by
    rintro a b ⟨f, hf⟩ ⟨g, hg⟩
    exact ⟨f * g, (map_mul (coboundary k S) f.val g.val).trans (congrArg₂ (· * ·) hf hg)⟩
  inv_mem' := by
    rintro a ⟨f, hf⟩
    exact ⟨f⁻¹, (map_inv (coboundary k S) f.val).trans (congrArg Inv.inv hf)⟩

/-- Continuous second cohomology in the scalar-defect convention. -/
abbrev _root_.Specs.RM03.Brauer.ContinuousCohomology.H2ContinuousValue
    (k : Type u) (S : Type v) [Field k] [Field S] [Algebra k S] :=
  continuousCocycles k S ⧸ continuousCoboundaries k S

open _root_.Specs.RM03.Brauer.ContinuousCohomology (H2ContinuousValue)

/-- The class of a continuous two-cocycle. -/
def continuousClass : continuousCocycles k S →* H2ContinuousValue k S :=
  QuotientGroup.mk' (continuousCoboundaries k S)

abbrev Stage (k : Type u) (S : Type v) [Field k] [Field S] [Algebra k S] :=
  FiniteGaloisIntermediateField k S

variable {E F : Stage k S}

/-- Restriction along the specified inclusion of finite Galois subfields. -/
def stageRestrict (h : E ≤ F) : Gal(F/k) →* Gal(E/k) := by
  letI : Algebra E F := (IntermediateField.inclusion h).toAlgebra
  letI : IsScalarTower k E F := IsScalarTower.of_algebraMap_eq
    (fun x => ((IntermediateField.inclusion h).commutes x).symm)
  exact AlgEquiv.restrictNormalHom E

/-- Inclusion on the units of two finite Galois stages. -/
def stageUnits (h : E ≤ F) : Eˣ →* Fˣ :=
  Units.map (IntermediateField.inclusion h).toMonoidHom

/-- Inclusion of the units of a stage into the separable closure. -/
def absoluteUnits (E : Stage k S) : Eˣ →* Sˣ :=
  Units.map E.toIntermediateField.val.toMonoidHom

/-- Restriction from the absolute Galois group to a finite stage. -/
abbrev absoluteRestrict (E : Stage k S) : Gal(S/k) →* Gal(E/k) :=
  AlgEquiv.restrictNormalHom E.toIntermediateField

theorem stageRestrict_apply (h : E ≤ F) (g : Gal(F/k)) (x : E) :
    (IntermediateField.inclusion h) (stageRestrict h g x) =
      g ((IntermediateField.inclusion h) x) := by
  let : Algebra E F := (IntermediateField.inclusion h).toAlgebra
  let : IsScalarTower k E F := IsScalarTower.of_algebraMap_eq
    (fun x => ((IntermediateField.inclusion h).commutes x).symm)
  exact AlgEquiv.restrictNormal_commutes (F := k) g E x

theorem stageUnits_smul (h : E ≤ F) (g : Gal(F/k)) (a : Eˣ) :
    stageUnits h (stageRestrict h g • a) = g • stageUnits h a :=
  Units.ext (stageRestrict_apply h g a.val)

theorem absoluteUnits_smul (E : Stage k S) (g : Gal(S/k)) (a : Eˣ) :
    absoluteUnits E (absoluteRestrict E g • a) = g • absoluteUnits E a :=
  Units.ext (AlgEquiv.restrictNormalHom_apply E.toIntermediateField g a.val)

section Pullback

variable {K L : Type v} [Field K] [Field L] [Algebra k K] [Algebra k L]
  (r : Gal(L/k) →* Gal(K/k)) (i : Kˣ →* Lˣ)

private def pullOne : (Gal(K/k) → Kˣ) →* (Gal(L/k) → Lˣ) where
  toFun f g := i (f (r g))
  map_one' := funext fun _ => map_one i
  map_mul' _ _ := funext fun _ => map_mul i _ _

private def pullTwo : ((Gal(K/k) × Gal(K/k)) → Kˣ) →*
    ((Gal(L/k) × Gal(L/k)) → Lˣ) where
  toFun f p := i (f (r p.1, r p.2))
  map_one' := funext fun _ => map_one i
  map_mul' _ _ := funext fun _ => map_mul i _ _

variable (action : ∀ g a, i (r g • a) = g • i a)

private def pullCocycle : ScalarCocycle k K →* ScalarCocycle k L :=
  ((pullTwo r i).comp (cocycles k K).subtype).codRestrict _ (fun c => by
    intro g h j
    change i (c.val (r (g * h), r j)) * i (c.val (r g, r h)) =
      g • i (c.val (r h, r j)) * i (c.val (r g, r (h * j)))
    simpa only [map_mul, action] using congrArg i (c.property (r g) (r h) (r j)))

private theorem pullCocycle_coboundary (a : Gal(K/k) → Kˣ) :
    pullCocycle r i action (coboundary k K a) = coboundary k L (pullOne r i a) := by
  apply Subtype.ext
  funext p
  change i (r p.1 • a (r p.2) / a (r p.1 * r p.2) * a (r p.1)) =
    p.1 • i (a (r p.2)) / i (a (r (p.1 * p.2))) * i (a (r p.1))
  simp only [map_mul, map_div, action]

end Pullback

/-- The finite-stage inflation of a scalar cocycle. -/
def inflateCocycle (h : E ≤ F) : ScalarCocycle k E →* ScalarCocycle k F :=
  pullCocycle (stageRestrict h) (stageUnits h) (stageUnits_smul h)

/-- Inflation and extension of coefficients on finite second cohomology. -/
def inflate (h : E ≤ F) : H2 k E →* H2 k F :=
  QuotientGroup.lift _ ((cocycleClass k F).comp (inflateCocycle h)) (by
    rintro c ⟨a, rfl⟩
    change cocycleClass k F (inflateCocycle h (coboundary k E a)) = 1
    rw [inflateCocycle, pullCocycle_coboundary]
    exact (QuotientGroup.eq_one_iff _).mpr ⟨_, rfl⟩)

/-- Inflation of a finite cocycle to a continuous cocycle. -/
def toContinuousCocycle (E : Stage k S) : ScalarCocycle k E →* continuousCocycles k S :=
  (pullCocycle (absoluteRestrict E) (absoluteUnits E) (absoluteUnits_smul E)).codRestrict _
    (fun c => by
      change Continuous (fun p : Gal(S/k) × Gal(S/k) =>
        absoluteUnits E (c.val (absoluteRestrict E p.1, absoluteRestrict E p.2)))
      have hr := InfiniteGalois.restrictNormalHom_continuous E.toIntermediateField
      exact (show Continuous (fun q : Gal(E/k) × Gal(E/k) => absoluteUnits E (c.val q))
        from continuous_of_discreteTopology).comp
        ((hr.comp continuous_fst).prodMk (hr.comp continuous_snd)))

/-- The canonical map from a finite second cohomology group into continuous cohomology. -/
def toContinuous (E : Stage k S) : H2 k E →* H2ContinuousValue k S :=
  QuotientGroup.lift _ (continuousClass.comp (toContinuousCocycle E)) (by
    rintro c ⟨a, rfl⟩
    change continuousClass (toContinuousCocycle E (coboundary k E a)) = 1
    apply (QuotientGroup.eq_one_iff _).mpr
    refine ⟨⟨pullOne (absoluteRestrict E) (absoluteUnits E) a, ?_⟩, ?_⟩
    · change Continuous (fun g : Gal(S/k) => absoluteUnits E (a (absoluteRestrict E g)))
      exact (show Continuous (fun g : Gal(E/k) => absoluteUnits E (a g))
        from continuous_of_discreteTopology).comp
        (InfiniteGalois.restrictNormalHom_continuous E.toIntermediateField)
    · exact (pullCocycle_coboundary _ _ (absoluteUnits_smul E) a).symm)

/-- Stage groups use their additive notation in the abelian-group direct limit. -/
abbrev StageCohomology (E : Stage k S) := Additive (H2 k E)

/-- The transition map on stage groups in additive notation. -/
def stageTransition (E F : Stage k S) (h : E ≤ F) :
    StageCohomology E →+ StageCohomology F :=
  (inflate h).toAdditive

/-- Abelian-group direct limit of finite Galois second cohomology groups. -/
abbrev FiniteH2Limit (k : Type u) (S : Type v) [Field k] [Field S] [Algebra k S] :=
  @AddCommGroup.DirectLimit (Stage k S) _ (@StageCohomology k S _ _ _) _
    (Classical.decEq (Stage k S)) (@stageTransition k S _ _ _)

/-- The map from a finite stage into the direct limit. -/
def limitOf (E : Stage k S) : StageCohomology E →+ FiniteH2Limit k S :=
  @AddCommGroup.DirectLimit.of (Stage k S) _ (@StageCohomology k S _ _ _) _
    (@stageTransition k S _ _ _) (Classical.decEq (Stage k S)) E

end
end RM03.Brauer.ContinuousCohomology

namespace Specs.RM03.Brauer.ContinuousCohomology

open _root_.RM03.Brauer.ContinuousCohomology _root_.RM03.Brauer.ScalarObstruction

universe u v

set_option linter.checkUnivs false in
def H2ContinuousType :=
  ∀ (k : Type u) (S : Type v) [Field k] [Field S] [Algebra k S], Type v

def CoboundaryContinuous : Prop :=
  ∀ {k : Type u} {S : Type v} [Field k] [Field S] [Algebra k S] [IsSepClosure k S],
    letI : TopologicalSpace Sˣ := ⊥
    ∀ a : continuousOneCochains k S, Continuous (coboundary k S a.val).val

def InflateFormula : Prop :=
  ∀ {k : Type u} {S : Type v} [Field k] [Field S] [Algebra k S]
    {E F : Stage k S} (h : E ≤ F) (c : ScalarCocycle k E),
    (∀ g j, (inflateCocycle h c).val (g,j) =
      stageUnits h (c.val (stageRestrict h g, stageRestrict h j))) ∧
    inflate h (cocycleClass k E c) = cocycleClass k F (inflateCocycle h c)

def ToContinuousFormula : Prop :=
  ∀ {k : Type u} {S : Type v} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    (E : Stage k S) (c : ScalarCocycle k E),
    (∀ g j, (toContinuousCocycle E c).val.val (g,j) =
      absoluteUnits E (c.val (absoluteRestrict E g, absoluteRestrict E j))) ∧
    toContinuous E (cocycleClass k E c) = continuousClass (toContinuousCocycle E c)

def InflationDirectedSystem : Prop :=
  ∀ {k : Type u} {S : Type v} [Field k] [Field S] [Algebra k S] [IsSepClosure k S],
    DirectedSystem (fun E : Stage k S => H2 k E) (fun _ _ h => inflate h)

def ToContinuousCompatible : Prop :=
  ∀ {k : Type u} {S : Type v} [Field k] [Field S] [Algebra k S]
    {E F : Stage k S} (h : E ≤ F),
    (toContinuous F).comp (inflate h) = toContinuous E

def FiniteCocycleRepresentative : Prop :=
  ∀ {k : Type u} {S : Type v} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    (c : continuousCocycles k S),
    ∃ (E : Stage k S) (cE : ScalarCocycle k E), toContinuousCocycle E cE = c

def FiniteClassRepresentative : Prop :=
  ∀ {k : Type u} {S : Type v} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    (x : H2ContinuousValue k S), ∃ (E : Stage k S) (a : H2 k E), toContinuous E a = x

def EqualAtFiniteStage : Prop :=
  ∀ {k : Type u} {S : Type v} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    {E F : Stage k S} (a : H2 k E) (b : H2 k F),
    toContinuous E a = toContinuous F b ↔
    ∃ (L : Stage k S) (hE : E ≤ L) (hF : F ≤ L), inflate hE a = inflate hF b

/-- The isomorphism is required to have the canonical comparison as its stage maps. -/
def FiniteLimitComparison : Prop :=
  ∀ {k : Type u} {S : Type v} [Field k] [Field S] [Algebra k S] [IsSepClosure k S],
    ∃ e : FiniteH2Limit k S ≃+ Additive (H2ContinuousValue k S),
      ∀ (E : Stage k S) (a : H2 k E),
        e (limitOf E (Additive.ofMul a)) = Additive.ofMul (toContinuous E a)

end Specs.RM03.Brauer.ContinuousCohomology
