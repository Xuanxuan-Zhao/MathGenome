import Specs.LinearAlgebraicGroups.Arithmetic.ComplexExceptionalDatum
import LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes
import Mathlib.Analysis.Complex.Polynomial.Basic
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory

namespace LinearAlgebraicGroups.Arithmetic.ComplexExceptionalDatum

open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open Specs.AbsoluteDynkinTypes (HasDynkinType IsAbsolutelyAlmostSimple)
open Specs.ComplexExceptionalDatum
open Specs.GeometricRadicals (GeometricGroup IsReductive)
open Specs.IntegralSemisimpleModel (Integers IntegralGroup fibre integerAlgebra)
open Specs.Pinning (AttachedDatum BasedIso BasedRootDatum SplitBorelPair)
open Specs.SimplyConnectedLattice (corootLattice)
open Specs.Unipotent (baseChangedAlgebraicGroup)
open Classification.Pinning (inducedBasedIso standardAdditiveLine)

open private reductive_of_semisimple geometric_coroot_lattice coroot_span_of_equiv
  from LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes
open private groupBaseChangeTower from LinearAlgebraicGroups.Reductive.RadicalBaseChange
open private fibreIterateIso from LinearAlgebraicGroups.Classification.IntegralRealization
open private alignPairs pinAlignedPairs
  from LinearAlgebraicGroups.Classification.PinnedEquivalence

noncomputable section

/-- Conjugacy and pinning identify the based data of any two pairs in
isomorphic split groups over the same field. -/
private theorem basedIsoOfGroupIso {k : Type} [Field k] {P Q : SplitBorelPair k}
    (D : AttachedDatum P) (E : AttachedDatum Q) (f : P.G.val ≅ Q.G.val) :
    Nonempty (BasedIso D.toBased E.toBased) := by
  obtain ⟨F, t, b, ht, hb⟩ := alignPairs P Q f
  obtain ⟨P', Q', hP, hQ, ⟨j⟩⟩ :=
    pinAlignedPairs P Q (standardAdditiveLine k) F t ht b hb
  subst P
  subst Q
  exact ⟨inducedBasedIso j D E⟩

private theorem hasDynkinType_of_basedIso {D E : BasedRootDatum.{0}}
    (f : BasedIso D E) {t : LieAlgebrasAndRepresentations.FiniteDynkinType}
    (h : HasDynkinType (RootData.integralCartan D.datum D.base) t) :
    HasDynkinType (RootData.integralCartan E.datum E.base) t := by
  obtain ⟨e, he⟩ := h
  let d := f.val.indexEquiv
  have hs : d '' (D.base.support : Set D.I) = (E.base.support : Set E.I) := f.property
  let g : D.base.support ≃ E.base.support := d.subtypeEquiv (fun i => by
    change i ∈ (D.base.support : Set D.I) ↔ d i ∈ (E.base.support : Set E.I)
    rw [← hs]
    exact ⟨fun hi => ⟨i, hi, rfl⟩, fun ⟨j, hj, hji⟩ => d.injective hji ▸ hj⟩)
  refine ⟨g.symm.trans e, ?_⟩
  intro i j
  obtain ⟨i, rfl⟩ := g.surjective i
  obtain ⟨j, rfl⟩ := g.surjective j
  change E.datum.pairing (f.val.indexEquiv j.val) (f.val.indexEquiv i.val) =
    t.cartan (e (g.symm (g i))) (e (g.symm (g j)))
  rw [g.symm_apply_apply, g.symm_apply_apply, f.val.toHom.pairing]
  exact he i j

private abbrev RealAlgebraicClosure := AlgebraicClosure ℝ

private def complexClosureEquiv : RealAlgebraicClosure ≃ₐ[ℝ] ℂ :=
  letI : IsAlgClosure ℝ ℂ := ⟨inferInstance, inferInstance⟩
  IsAlgClosure.equiv ℝ RealAlgebraicClosure ℂ

private local instance closureAlgebra : Algebra RealAlgebraicClosure ℂ :=
  complexClosureEquiv.toRingHom.toAlgebra

private local instance closureTower : IsScalarTower ℝ RealAlgebraicClosure ℂ :=
  IsScalarTower.of_algebraMap_eq fun x => (complexClosureEquiv.commutes x).symm

/-- The complexification is the extension of the actual geometric group
along the real-algebra identification of its algebraic closure with ℂ. -/
private def complexBaseChange (G : AffineAlgebraicGroup ℝ) :
    (groupBaseChange RealAlgebraicClosure ℂ).obj (GeometricGroup G).val ≅
      (baseChangedAlgebraicGroup ℂ G).val :=
  ((groupBaseChangeTower (k := ℝ) (K := RealAlgebraicClosure) ℂ).app G.val).symm

/-- Pulling an integral model through the algebraic closure and then to ℂ
has the same effect as taking its complex fibre. -/
private def complexFibre (M : IntegralGroup.{0}) :
    (groupBaseChange RealAlgebraicClosure ℂ).obj ((fibre RealAlgebraicClosure).obj M) ≅
      (fibre ℂ).obj M := by
  letI := integerAlgebra RealAlgebraicClosure
  letI := integerAlgebra ℂ
  apply fibreIterateIso
  ext x
  exact map_intCast (algebraMap RealAlgebraicClosure ℂ) x.down

/-- Compare both groups with the field fibres of one integral realization.
The marking on each fibre retains the entire based root datum. -/
private theorem complexBasedIso (G : AffineAlgebraicGroup ℝ)
    {P₀ : SplitBorelPair RealAlgebraicClosure} (h₀ : P₀.G = GeometricGroup G) (D₀ : AttachedDatum P₀)
    {P : SplitBorelPair ℂ} (h : P.G = baseChangedAlgebraicGroup ℂ G) (D : AttachedDatum P) :
    Nonempty (BasedIso D₀.toBased D.toBased) := by
  obtain ⟨M⟩ := Classification.IntegralRealization.integralRealization D₀.toBased
  obtain ⟨_, F₀, e₀, _⟩ := M.fieldFibre RealAlgebraicClosure
  obtain ⟨_, F, e, _⟩ := M.fieldFibre ℂ
  obtain ⟨i₀⟩ := (Classification.PinnedEquivalence.pinnedEquivalence.2 RealAlgebraicClosure
    |>.2.1 P₀ F₀.pinned.pair D₀ F₀.attached).mpr ⟨F₀.datumIso.val⟩
  let i : (fibre RealAlgebraicClosure).obj M.group ≅ (GeometricGroup G).val :=
    e₀ ≪≫ i₀.symm ≪≫ eqToIso (congrArg Subtype.val h₀)
  let j : F.pinned.pair.G.val ≅ P.G.val :=
    e.symm ≪≫ (complexFibre M.group).symm ≪≫
      (groupBaseChange RealAlgebraicClosure ℂ).mapIso i ≪≫ complexBaseChange G ≪≫
      eqToIso (congrArg Subtype.val h.symm)
  obtain ⟨f⟩ := basedIsoOfGroupIso F.attached D j
  let first : D₀.toBased ⟶ F.attached.toBased := F.datumIso
  let second : F.attached.toBased ⟶ D.toBased := f
  exact ⟨first ≫ second⟩

/-- Reductivity and the exceptional simply connected datum on the complexification. -/
theorem complexExceptionalDatum : Statement := by
  intro G hG hsc htype
  obtain ⟨P₀, h₀, D₀, htype⟩ := htype
  have hRed := reductive_of_semisimple G hG.1
  refine ⟨(Reductive.RadicalBaseChange.reductiveFieldExtension (K := ℂ)
    G hRed.1 hRed.2.1).mpr hRed, ?_⟩
  intro P h D
  obtain ⟨f⟩ := complexBasedIso G h₀ D₀ h D
  let _ : Finite D₀.toBased.I := D₀.toBased.finiteRoots
  refine ⟨coroot_span_of_equiv D₀.toBased.datum D.toBased.datum f.val
    (geometric_coroot_lattice G hG.1 hsc P₀ h₀ D₀), ?_⟩
  rcases htype with h6 | h7 | h8
  · exact Or.inl (hasDynkinType_of_basedIso f h6)
  · exact Or.inr (Or.inl (hasDynkinType_of_basedIso f h7))
  · exact Or.inr (Or.inr (hasDynkinType_of_basedIso f h8))

end

end LinearAlgebraicGroups.Arithmetic.ComplexExceptionalDatum
