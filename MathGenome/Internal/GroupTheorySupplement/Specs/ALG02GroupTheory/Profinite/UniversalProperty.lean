import MathGenome.Internal.GroupTheorySupplement.Specs.ALG02GroupTheory.Profinite.Completion

/-! The universal property and induced maps of GR02-C05.03. -/

open CategoryTheory

namespace Specs.ALG02GroupTheory.Profinite

universe u v w

/-- A homomorphism to a profinite group extends uniquely across the canonical map. -/
def CompletionUniversal : Prop :=
  ∀ {G : Type u} [Group G] {P : ProfiniteGrp.{v}} (f : G →* P),
    ∃! F : completionValue G →ₜ* P, F.toMonoidHom.comp (etaValue G) = f

set_option linter.checkUnivs false in
/-- The type of the continuous map on completions induced by an abstract homomorphism. -/
def CompletionMapType :=
  ∀ {G : Type u} [Group G] {H : Type v} [Group H],
    (G →* H) → (completionValue G →ₜ* completionValue H)

variable {G : Type u} [Group G] {H : Type v} [Group H]

private def mapQuotient (f : G →* H) (N : FiniteIndexNormalSubgroup H) :
    finiteQuotient (N.comap f) →ₜ* finiteQuotient N where
  toMonoidHom := QuotientGroup.map _ _ f le_rfl
  continuous_toFun := by
    let _ : DiscreteTopology (finiteQuotient (N.comap f)) := ⟨rfl⟩
    exact continuous_of_discreteTopology

/-- At a finite quotient of the target, project to the quotient by its preimage
and apply the induced quotient homomorphism. -/
def completionMapValue : CompletionMapType.{u, v} :=
  fun {_} [_] {_} [_] f =>
    { toFun := fun x => ⟨fun N => mapQuotient f N (projectionValue (N.comap f) x), by
        intro M N i
        have h := FiniteIndexNormalSubgroup.comap_mono f i.le
        have hx := x.2 h.hom
        change transitionValue h (x.1 (M.comap f)) = x.1 (N.comap f) at hx
        change transitionValue i.le (mapQuotient f M (x.1 (M.comap f))) =
          mapQuotient f N (x.1 (N.comap f))
        obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (x.1 (M.comap f))
        rw [← hx, ← hg]
        rfl⟩
      map_one' := Subtype.ext (funext fun N => map_one (mapQuotient f N))
      map_mul' := fun x y => Subtype.ext (funext fun N =>
        map_mul (mapQuotient f N) (projectionValue (N.comap f) x)
          (projectionValue (N.comap f) y))
      continuous_toFun := continuous_induced_rng.mpr (continuous_pi fun N =>
        (mapQuotient f N).continuous_toFun.comp
          (projectionValue (N.comap f)).continuous_toFun) }

/-- The induced map on completions commutes with the canonical maps. -/
def CompletionMapEta : Prop :=
  ∀ {G : Type u} [Group G] {H : Type v} [Group H] (f : G →* H) (g : G),
    completionMapValue f (etaValue G g) = etaValue H (f g)

/-- Completion preserves the identity homomorphism. -/
def CompletionMapId : Prop :=
  ∀ (G : Type u) [Group G],
    completionMapValue (MonoidHom.id G) = ContinuousMonoidHom.id (completionValue G)

/-- Completion preserves composition across three arbitrary group universes. -/
def CompletionMapComp : Prop :=
  ∀ {G : Type u} [Group G] {H : Type v} [Group H] {K : Type w} [Group K]
    (f : G →* H) (g : H →* K),
    completionMapValue (g.comp f) = (completionMapValue g).comp (completionMapValue f)

end Specs.ALG02GroupTheory.Profinite
