import MathGenome.Internal.GroupTheorySupplement.ALG02GroupTheory.Profinite.Topology
import MathGenome.Internal.GroupTheorySupplement.Specs.ALG02GroupTheory.Profinite.UniversalProperty

/-! The universal property of profinite completion and its functoriality. -/

open CategoryTheory

namespace ALG02GroupTheory.Profinite

universe u v w

variable {G : Type u} [Group G] {H : Type v} [Group H] {K : Type w} [Group K]

/-- The continuous homomorphism induced on completions by an abstract homomorphism. -/
abbrev completionMap (f : G →* H) : Completion G →ₜ* Completion H :=
  Specs.ALG02GroupTheory.Profinite.completionMapValue f

@[simp]
theorem completionMap_eta (f : G →* H) (g : G) :
    completionMap f (eta G g) = eta H (f g) := by
  apply Subtype.ext
  funext N
  rfl

private theorem eq_of_eq_on_eta {P : ProfiniteGrp.{v}} {F F' : Completion G →ₜ* P}
    (h : ∀ g, F (eta G g) = F' (eta G g)) : F = F' :=
  DFunLike.ext' (F := Completion G →ₜ* P) (denseRange_eta G |>.equalizer
    F.continuous_toFun F'.continuous_toFun (funext h))

/-- Restrict all finite quotient coordinates to the quotients by open normal subgroups. -/
private def restrictToOpenQuotients (P : ProfiniteGrp.{v}) :
    Completion P →ₜ* ProfiniteGrp.limit P.diagram where
  toFun x := ⟨fun U => projection U.toFiniteIndexNormalSubgroup x, fun _ _ i =>
    projection_compatible (OpenNormalSubgroup.toFiniteIndexNormalSubgroup_mono i.le) x⟩
  map_one' := Subtype.ext (funext fun U => map_one (projection U.toFiniteIndexNormalSubgroup))
  map_mul' x y :=
    Subtype.ext (funext fun U => map_mul (projection U.toFiniteIndexNormalSubgroup) x y)
  continuous_toFun := continuous_induced_rng.mpr
    (continuous_pi fun U => projection_continuous U.toFiniteIndexNormalSubgroup)

/-- Every abstract homomorphism to a profinite group has a unique continuous extension.
The source and target groups may live in independent universes. -/
theorem completion_universal {P : ProfiniteGrp.{v}} (f : G →* P) :
    ∃! F : Completion G →ₜ* P, F.toMonoidHom.comp (eta G) = f := by
  let e := P.continuousMulEquivLimittoFiniteQuotientFunctor
  let F := (e.symm : ProfiniteGrp.limit P.diagram →ₜ* P).comp
    ((restrictToOpenQuotients P).comp (completionMap f))
  have hF (g : G) : F (eta G g) = f g := by
    change e.symm (restrictToOpenQuotients P (completionMap f (eta G g))) = f g
    rw [completionMap_eta]
    exact e.symm_apply_apply (f g)
  refine ⟨F, MonoidHom.ext hF, fun F' hF' => eq_of_eq_on_eta fun g => ?_⟩
  exact (DFunLike.congr_fun hF' g).trans (hF g).symm

@[simp]
theorem completionMap_id (G : Type u) [Group G] :
    completionMap (MonoidHom.id G) = ContinuousMonoidHom.id (Completion G) := by
  apply eq_of_eq_on_eta
  intro g
  exact completionMap_eta (MonoidHom.id G) g

theorem completionMap_comp (f : G →* H) (g : H →* K) :
    completionMap (g.comp f) = (completionMap g).comp (completionMap f) := by
  apply eq_of_eq_on_eta
  intro x
  simp [MonoidHom.comp_apply]

end ALG02GroupTheory.Profinite
