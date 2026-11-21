import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Differentials.Universal
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.Naturality

/-! KD-05: functoriality for arbitrary commutative squares of ring maps. -/
namespace AdvCommAlg.Differentials

universe u v u' v' u'' v''
noncomputable section

/-- The map on differentials, linear with the target restricted along f. -/
def algebraDifferentialMap :
    Specs.AdvCommAlg.Differentials.algebraDifferentialMapType.{u,v,u',v'} := by
  intro A B A' B' _ _ _ _ _ _ g f h
  letI : Algebra A A' := g.toAlgebra
  letI : Algebra B B' := f.toAlgebra
  letI : Algebra A B' := (f.comp (algebraMap A B)).toAlgebra
  letI : IsScalarTower A B B' := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower A A' B' := IsScalarTower.of_algebraMap_eq' h
  exact KaehlerDifferential.map A A' B B'

theorem algebraDifferentialMap_apply :
    Specs.AdvCommAlg.Differentials.algebraDifferentialMapApply.{u,v,u',v'} := by
  intro A B A' B' _ _ _ _ _ _ g f h b
  let : Algebra A A' := g.toAlgebra
  let : Algebra B B' := f.toAlgebra
  let : Algebra A B' := (f.comp (algebraMap A B)).toAlgebra
  let : IsScalarTower A B B' := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A A' B' := IsScalarTower.of_algebraMap_eq' h
  exact KaehlerDifferential.map_D A A' B B' b

theorem algebraDifferentialMap_smul
    {A : Type u} {B : Type v} {A' : Type u'} {B' : Type v'}
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra A B] [Algebra A' B']
    (g : A →+* A') (f : B →+* B')
    (h : f.comp (algebraMap A B) = (algebraMap A' B').comp g)
    (b : B) (x : KaehlerDifferential A B) :
    algebraDifferentialMap g f h (b • x) = f b • algebraDifferentialMap g f h x := by
  let : Algebra B B' := f.toAlgebra
  rw [map_smul]
  exact (IsScalarTower.algebraMap_smul B' b _).symm

theorem algebraDifferentialMap_unique :
    Specs.AdvCommAlg.Differentials.algebraDifferentialMapUnique.{u,v,u',v'} := by
  intro A B A' B' _ _ _ _ _ _ g f h
  let : Algebra B B' := f.toAlgebra
  intro L hL
  apply LinearMap.ext
  intro x
  have hx : x ∈ Submodule.span B (Set.range (KaehlerDifferential.D A B)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, rfl⟩ := hy
    exact (hL b).trans (algebraDifferentialMap_apply g f h b).symm
  | zero => simp
  | add x y hx hy ex ey => simp only [map_add, ex, ey]
  | smul b x hx ex => simp only [map_smul, ex]

theorem algebraDifferentialMap_id :
    Specs.AdvCommAlg.Differentials.algebraDifferentialMapId.{u,v} := by
  intro A B _ _ _ x
  have hx : x ∈ Submodule.span B (Set.range (KaehlerDifferential.D A B)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, rfl⟩ := hy
    exact algebraDifferentialMap_apply (RingHom.id A) (RingHom.id B) _ b
  | zero => simp
  | add x y hx hy ex ey => simp only [map_add, ex, ey]
  | smul b x hx ex =>
    change algebraDifferentialMap (RingHom.id A) (RingHom.id B) (by ext; rfl)
      (b • x) = b • x
    rw [algebraDifferentialMap_smul]
    exact congrArg (fun y => b • y) ex

theorem algebraDifferentialMap_comp :
    Specs.AdvCommAlg.Differentials.algebraDifferentialMapComp.{u,v,u',v',u'',v''} := by
  intro A B A' B' A'' B'' _ _ _ _ _ _ _ _ _ g f g' f' h h' x
  have hc : (f'.comp f).comp (algebraMap A B) =
      (algebraMap A'' B'').comp (g'.comp g) := by
    rw [RingHom.comp_assoc, h, ← RingHom.comp_assoc, h', RingHom.comp_assoc]
  have hx : x ∈ Submodule.span B (Set.range (KaehlerDifferential.D A B)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, rfl⟩ := hy
    rw [algebraDifferentialMap_apply, algebraDifferentialMap_apply,
      algebraDifferentialMap_apply]
    rfl
  | zero => simp
  | add x y hx hy ex ey => simp only [map_add, ex, ey]
  | smul b x hx ex =>
    change algebraDifferentialMap (g'.comp g) (f'.comp f) hc (b • x) =
      algebraDifferentialMap g' f' h' (algebraDifferentialMap g f h (b • x))
    rw [algebraDifferentialMap_smul, algebraDifferentialMap_smul,
      algebraDifferentialMap_smul]
    exact congrArg (fun y => f' (f b) • y) ex

end
end AdvCommAlg.Differentials
