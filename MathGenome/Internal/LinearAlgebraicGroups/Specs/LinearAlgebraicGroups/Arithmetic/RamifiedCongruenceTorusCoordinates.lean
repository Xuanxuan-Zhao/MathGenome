import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat

universe u

namespace LinearAlgebraicGroups.Specs.RamifiedCongruenceTorusCoordinates

open CategoryTheory
open IntegralSemisimpleModel (IntegralAlgebra TorusValues torusPoint)
open scoped CategoryTheory.MonObj
open ExceptionalAffineBruhat (RamifiedReference DiagramCompositum FoldedApartment FoldedLevel)
open ExceptionalAffineRootSystems (e6Partner)
open ExceptionalIwahoriCongruence (integralRing)
open Pinning (BasedRootDatum)

noncomputable section

/-- The simple character at a marked Bourbaki index. -/
def simpleCharacter {D : BasedRootDatum.{u}} (b : Fin 6 ≃ D.base.support) (i : Fin 6) :
    D.X :=
  D.datum.root (b i).val

/-- The value of a marked simple character in any test algebra. -/
def simpleUnit {D : BasedRootDatum.{u}} {S : IntegralAlgebra.{u}}
    (b : Fin 6 ≃ D.base.support) (t : TorusValues D S) (i : Fin 6) : Sˣ :=
  t (Multiplicative.ofAdd (simpleCharacter b i))

abbrev valuationRing (E : Type u) [Field E] [ValuativeRel E] :=
  (ValuativeRel.valuation E).valuationSubring

/-- The field value of an integral character unit. -/
def fieldUnit {E : Type u} [Field E] [ValuativeRel E] :
    (valuationRing E)ˣ →* Eˣ :=
  Units.map (valuationRing E).subtype.toMonoidHom

/-- The two singleton indices are 2 and 4. The representatives of the other
two orbits are 1 and 3, in the source's numbering. -/
def orbitValues {k K : Type u} [Field k] [Field K] [Algebra k K]
    (s : Gal(K/k)) (a c : kˣ) (p q : Kˣ) : Fin 6 → Kˣ :=
  ![p, Units.map (algebraMap k K).toMonoidHom a, q,
    Units.map (algebraMap k K).toMonoidHom c,
    Units.map s.toRingHom.toMonoidHom q, Units.map s.toRingHom.toMonoidHom p]

/-- The point of the actual integral model associated to the split torus tuple. -/
def torusPointInModel {D : BasedRootDatum.{u}} (M : IntegralSemisimpleModel.Model D)
    {K : Type u} [Field K] (t : TorusValues D (integralRing K)) :
    ExceptionalAffineBruhat.FieldPoints M K :=
  torusPoint D _ t ≫ M.torus.hom.hom

/-- The marked simple-coordinate description of the actual chart torus,
including independent lifts and the test at all positive congruence powers. -/
def PinnedTorusCoordinates : Prop :=
  ∀ {D : BasedRootDatum.{u}} (b : Fin 6 ≃ D.base.support),
    D.datum.rootSpan ℤ = ⊤ →
    (∃ B : Module.Basis (Fin 6) ℤ D.X, ∀ i, B i = simpleCharacter b i) ∧
    (∀ (S : IntegralAlgebra.{u}) (v : Fin 6 → Sˣ),
      ∃! t : TorusValues D S, ∀ i, simpleUnit b t i = v i) ∧
    (∀ (E : Type u) [Field E] [ValuativeRel E] [TopologicalSpace E]
      [IsNonarchimedeanLocalField E] (n : ℕ), 0 < n →
      ∀ t : TorusValues D (integralRing (valuationRing E)),
      let I := (IsLocalRing.maximalIdeal (valuationRing E)) ^ n
      (∀ i, (simpleUnit b t i : valuationRing E) - 1 ∈ I) →
      ∀ χ : D.X, (t (Multiplicative.ofAdd χ) : valuationRing E) - 1 ∈ I) ∧
    (∀ {F L k : Type u} [Field F] [Field L] [Field k] [Algebra F L] [Algebra F k]
      [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
      [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      {M : IntegralSemisimpleModel.Model D} (R : RamifiedReference F L M) (σ : Gal(L/F))
      (T : DiagramCompositum F L k σ) {A : FoldedApartment (R.diagram σ)}
      (X : FoldedLevel R σ T.diagram (IsScalarTower.toAlgHom F L T.field) A),
      (∀ i, (R.diagram σ).val.indexEquiv (b i) = b (e6Partner i)) →
      let K := T.field
      let act := Units.map T.diagram.toRingHom.toMonoidHom
      let chart := X.comparison.chart.chart.torus
      let v := fun (t : TorusValues D (integralRing K)) i => simpleUnit b t i
      let w := fun (t : TorusValues D (integralRing K)) =>
        ∀ i, v t (e6Partner i) = act (v t i)
      let z := fun (t : TorusValues D (integralRing K)) =>
        torusPointInModel M t
      (∀ t : TorusValues D (integralRing K), z t ∈ X.points.range ↔ w t) ∧
      (∀ t : TorusValues D (integralRing K), t ∈ chart ↔ w t) ∧
      (∀ (t : chart) (i : Fin 6), e6Partner i = i →
        ∃! a : kˣ,
          Units.map (algebraMap k K).toMonoidHom a = v t.val i) ∧
      (∀ (a c : kˣ) (p q : Kˣ),
        ∃! t : chart,
          ∀ i, v t.val i = orbitValues T.diagram a c p q i) ∧
      (∀ (a c : (valuationRing k)ˣ) (p q : (valuationRing K)ˣ),
        ∃! t : chart,
          (∀ i, v t.val i = orbitValues T.diagram (fieldUnit a) (fieldUnit c)
            (fieldUnit p) (fieldUnit q) i) ∧
          ∃ s : TorusValues D (integralRing (valuationRing K)), fieldUnit.comp s = t.val))

end
end LinearAlgebraicGroups.Specs.RamifiedCongruenceTorusCoordinates
