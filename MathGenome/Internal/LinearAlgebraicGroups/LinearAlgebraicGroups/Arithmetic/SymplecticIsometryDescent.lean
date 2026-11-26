import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.SymplecticIsometryDescent
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.SymplecticDatum
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.MatrixAlgebraForms
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.SemilinearVectorSpaces

open AlgebraicGeometry CategoryTheory Opposite WithConv
open scoped TensorProduct MatrixGroups CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Arithmetic.SymplecticIsometryDescent

open _root_.LinearAlgebraicGroups.Specs
open Specs.SymplecticDatumAdjointDescent (MatrixAlgebra adjoint)
open Specs.SymplecticMatrixStructure (Indices PointGroup symplecticPoints mapSymplecticPoint)
open Descent.MatrixAlgebraForms
open RM03.Brauer.ProjectiveClassification (Mat)
open RM03.Brauer.SemilinearDescent (AlgebraAction)

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem quotientPresentation : QuotientPresentation.{u} := by
  intro k I _ _ _ _ G c
  obtain ⟨Z, Q, q, hc, hs, hk, hp, hl, A, U, _, hi, hn, ha, hu, _, _⟩ :=
    RootData.SymplecticDatum.adjointQuotientAction k I G c
  exact ⟨⟨G, c, Z, hc, hs, Q, q, hk, hp, hl, A, U, hi, hn, ha, hu⟩, rfl, rfl⟩

variable {k K I : Type u} [Field k] [Field K] [Algebra k K]
  [Fintype I] [DecidableEq I]

private theorem relabel_map (g : Gal(K/k)) (X : MatrixAlgebra I K) :
    (relabel I K X).map g = relabel I K (X.map g) := rfl

private def reindexedAction (P : AdjointPresentation k I) (a : Coefficients (K := K) P) :
    Mat K (2 * Fintype.card I) ≃ₐ[K] Mat K (2 * Fintype.card I) :=
  (relabel I K).symm.trans ((P.onAlgebra (CommAlgCat.of k K) a).trans (relabel I K))

private theorem reindexedAction_apply (P : AdjointPresentation k I)
    (a : Coefficients (K := K) P) (X : MatrixAlgebra I K) :
    reindexedAction P a (relabel I K X) = relabel I K (P.onAlgebra (CommAlgCat.of k K) a X) := by
  exact congrArg (fun Y => relabel I K (P.onAlgebra (CommAlgCat.of k K) a Y))
    ((relabel I K).symm_apply_apply X)

private theorem adjoint_add {R : Type u} [CommRing R] (X Y : MatrixAlgebra I R) :
    adjoint (X + Y) = adjoint X + adjoint Y := by
  simp only [adjoint, Matrix.transpose_add, mul_add, add_mul]

private theorem adjoint_smul {R : Type u} [CommRing R] (a : R) (X : MatrixAlgebra I R) :
    adjoint (a • X) = a • adjoint X := by
  simp only [adjoint, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul]

private theorem adjoint_one : adjoint (1 : MatrixAlgebra I K) = 1 := by
  have h := (RootData.SymplecticDatumAdjointDescent.adjointIdentities I K).2.2.1 (1 : K)
  simpa only [map_one] using h

theorem algebraDescent : AlgebraDescent.{u} := by
  intro k K I _ _ _ _ _ _ _ _ P a
  have hn : 0 < 2 * Fintype.card I := Nat.mul_pos (by decide) Fintype.card_pos
  obtain ⟨e, hconj, he⟩ := conjugationIdentification (k := k) (K := K) hn
  let c : RM03.Brauer.ProjectiveClassification.Cocycle k K (2 * Fintype.card I) :=
    { val := fun g => e.symm (reindexedAction P (a g))
      law := by
        intro g h
        apply e.injective
        rw [map_mul]
        simp only [MulEquiv.apply_symm_apply]
        apply AlgEquiv.ext
        intro Y
        obtain ⟨X, rfl⟩ := (relabel I K).surjective Y
        let f : CommAlgCat.of k K ⟶ CommAlgCat.of k K := CommAlgCat.ofHom g.toAlgHom
        let aq : Gal(K/k) → (PointsOf P.quotient.val).obj (CommAlgCat.of k K) := a.val
        have ha : aq (g * h) = aq g * (PointsOf P.quotient.val).map f (aq h) :=
          a.property.2 g h
        have hg := he g (e.symm (reindexedAction P (a h))) (relabel I K (X.map g.symm))
        rw [MulEquiv.apply_symm_apply, reindexedAction_apply, relabel_map, relabel_map] at hg
        have hX : (X.map g.symm).map g = X := by
          ext i j
          exact g.apply_symm_apply _
        rw [hX] at hg
        change reindexedAction P (aq (g * h)) (relabel I K X) =
          (reindexedAction P (aq g) * e (projectiveAction _ g (e.symm (reindexedAction P (aq h)))))
            (relabel I K X)
        rw [ha, reindexedAction_apply, map_mul]
        change relabel I K (P.onAlgebra (CommAlgCat.of k K) (a g)
          (P.onAlgebra (CommAlgCat.of k K) ((PointsOf P.quotient.val).map f (a h)) X)) =
          reindexedAction P (a g) (e (projectiveAction _ g (e.symm (reindexedAction P (a h))))
            (relabel I K X))
        rw [← hg]
        erw [P.algebraNatural _ _ f]
        change _ = reindexedAction P (a g) (relabel I K
          (P.onAlgebra (CommAlgCat.of k K) ((PointsOf P.quotient.val).map f (a h))
            ((X.map g.symm).map g)))
        rw [hX, reindexedAction_apply] }
  obtain ⟨ρ, hρ, hcentral, hdegree, s, _, hs⟩ := effectiveDescent hn c
  have ht (g : Gal(K/k)) (X : MatrixAlgebra I K) :
      ρ.act g (relabel I K X) =
        relabel I K (P.onAlgebra (CommAlgCat.of k K) (a g) (X.map g)) := by
    obtain ⟨M, hM⟩ := Matrix.ProjGenLinGroup.mk_surjective (c.val g)
    rw [hρ g M hM, ← hconj M, hM, relabel_map]
    change e (e.symm (reindexedAction P (a g))) (relabel I K (X.map g)) = _
    rw [MulEquiv.apply_symm_apply, reindexedAction_apply]
  let j := relabel I K
  have hfixed (x : ρ.fixedSubalgebra) (g : Gal(K/k)) :
      P.onAlgebra (CommAlgCat.of k K) (a g) ((j.symm x.val).map g) = j.symm x.val := by
    apply j.injective
    rw [← ht, j.apply_symm_apply]
    exact x.property g
  have hstable (x : ρ.fixedSubalgebra) : j (adjoint (j.symm x.val)) ∈ ρ.fixedSubalgebra := by
    intro g
    rw [ht]
    have hg : (adjoint (j.symm x.val)).map g = adjoint ((j.symm x.val).map g) :=
      (RootData.SymplecticDatumAdjointDescent.adjointIdentities I K).2.2.2.2 g.toRingHom _
    erw [hg, P.preservesAdjoint, hfixed]
  let σ : Involution k (ρ.fixedSubalgebra : Type u) :=
    { toLinearMap :=
        { toFun := fun x => ⟨j (adjoint (j.symm x.val)), hstable x⟩
          map_add' := fun x y => Subtype.ext (by
            change j (adjoint (j.symm (x.val + y.val))) = _
            rw [map_add, adjoint_add, map_add]
            rfl)
          map_smul' := fun r x => Subtype.ext (by
            change j (adjoint (j.symm (r • x.val))) = r • j (adjoint (j.symm x.val))
            rw [← IsScalarTower.algebraMap_smul K r (x.val : Mat K _),
              ← IsScalarTower.algebraMap_smul K r (j (adjoint (j.symm x.val))),
              map_smul, adjoint_smul, map_smul]) }
      map_one := Subtype.ext (by
        change j (adjoint (j.symm 1)) = 1
        rw [map_one, adjoint_one, map_one])
      map_mul := fun x y => Subtype.ext (by
        change j (adjoint (j.symm (x.val * y.val))) =
          j (adjoint (j.symm y.val)) * j (adjoint (j.symm x.val))
        rw [map_mul, (RootData.SymplecticDatumAdjointDescent.adjointIdentities I K).2.1, map_mul])
      involutive := fun x => Subtype.ext (by
        change j (adjoint (j.symm (j (adjoint (j.symm x.val))))) = x.val
        rw [j.symm_apply_apply, (RootData.SymplecticDatumAdjointDescent.adjointIdentities I K).1,
          j.apply_symm_apply]) }
  have σ_formula (x : ρ.fixedSubalgebra) : j.symm (σ.toLinearMap x).val = adjoint (j.symm x.val) :=
    j.symm_apply_apply _
  let s' := s.trans j.symm
  have hs' (r : K) (x : ρ.fixedSubalgebra) : s' (r ⊗ₜ[k] x) = r • j.symm x.val := by
    change j.symm (s (r ⊗ₜ[k] x)) = _
    rw [hs, map_smul]
  refine ⟨⟨ρ, ht, hcentral, hdegree, σ, σ_formula, s', hs', ?_⟩⟩
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul r x => rw [Involution.baseChange_tmul, hs', hs', σ_formula, adjoint_smul]
  | add x y hx hy => simp only [map_add, adjoint_add, hx, hy]

section FixedPoints

variable [FiniteDimensional k K] [IsGalois k K]

private abbrev extendedTest (R : TestAlgebra k) : TestAlgebra K :=
  CommAlgCat.of K (K ⊗[k] R)

private def extendedBase (R : TestAlgebra k) : TestAlgebra k :=
  overBase k K (extendedTest (K := K) R)

private def includeTest (R : TestAlgebra k) : R ⟶ extendedBase (K := K) R := by
  refine ConcreteCategory.ofHom (C := CommAlgCat k)
    { toRingHom := (Algebra.TensorProduct.includeRight (R := k) (A := K) (B := R)).toRingHom
      commutes' := fun x => ?_ }
  change (1 : K) ⊗ₜ[k] algebraMap k R x = algebraMap k K x ⊗ₜ[k] (1 : R)
  rw [← Algebra.TensorProduct.algebraMap_apply', Algebra.TensorProduct.algebraMap_apply]

private def galoisTest (R : TestAlgebra k) (g : Gal(K/k)) :
    extendedBase (K := K) R ⟶ extendedBase (K := K) R := by
  refine ConcreteCategory.ofHom (C := CommAlgCat k)
    { toRingHom := (Algebra.TensorProduct.map g.toAlgHom (AlgHom.id k R)).toRingHom
      commutes' := fun x => ?_ }
  change g (algebraMap k K x) ⊗ₜ[k] (1 : R) = algebraMap k K x ⊗ₜ[k] (1 : R)
  rw [g.commutes]

/-- The two scalar structures on the scalar extension induce the same map
from the ground field. -/
private def extendedBaseEquiv (R : TestAlgebra k) : extendedBase (K := K) R ≃ₐ[k] K ⊗[k] R :=
  { RingEquiv.refl (K ⊗[k] R) with commutes' := fun _ => rfl }

private theorem galoisTest_semilinear (R : TestAlgebra k) (g : Gal(K/k)) (b : K) :
    (galoisTest R g).hom (algebraMap K (extendedTest (K := K) R) b) =
      algebraMap K (extendedTest (K := K) R) (g b) := rfl

private theorem includeTest_galois (R : TestAlgebra k) (g : Gal(K/k)) :
    includeTest (K := K) R ≫ galoisTest R g = includeTest R := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro r
  change g 1 ⊗ₜ[k] r = (1 : K) ⊗ₜ[k] r
  rw [map_one]

private def extendMap {R S : TestAlgebra k} (f : R ⟶ S) :
    extendedTest (K := K) R ⟶ extendedTest (K := K) S :=
  ConcreteCategory.ofHom (C := CommAlgCat K)
    (Algebra.TensorProduct.map (AlgHom.id K K) f.hom)

private theorem includeTest_natural {R S : TestAlgebra k} (f : R ⟶ S) :
    f ≫ includeTest (K := K) S =
      includeTest (K := K) R ≫ (restrictTestAlgebra k K).map (extendMap f) := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro r
  rfl

private theorem fixedTensorDescription {V : Type u} [AddCommGroup V] [Module k V] :
    Function.Injective (fun v : V => (1 : K) ⊗ₜ[k] v) ∧
      ∀ y : K ⊗[k] V, (∃ v : V, (1 : K) ⊗ₜ[k] v = y) ↔
        ∀ g : Gal(K/k), (Descent.SemilinearAction.scalarExtension V).act g y = y := by
  let ρ := Descent.SemilinearAction.scalarExtension (k := k) (K := K) V
  have h := Descent.SemilinearAction.scalarExtension_bijective (k := k) (K := K) V
  refine ⟨fun x y e => h.injective (Subtype.ext e), ?_⟩
  intro y
  constructor
  · rintro ⟨v, rfl⟩
    exact (Descent.SemilinearAction.scalarExtensionComparison (K := K) V v).property
  · intro hy
    obtain ⟨v, hv⟩ := h.surjective ⟨y, hy⟩
    exact ⟨v, congrArg Subtype.val hv⟩

private theorem galoisTest_apply (R : TestAlgebra k) (g : Gal(K/k)) (x : K ⊗[k] R) :
    (galoisTest R g).hom x = (Descent.SemilinearAction.scalarExtension R).act g x := by
  induction x using TensorProduct.inductionOn with
  | tmul a r => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem includeTest_fixed (R : TestAlgebra k) :
    Function.Injective (includeTest (K := K) R).hom ∧
      ∀ y : extendedBase (K := K) R, (∃ r : R, (includeTest R).hom r = y) ↔
        ∀ g : Gal(K/k), (galoisTest R g).hom y = y := by
  refine ⟨fixedTensorDescription (k := k) (K := K) (V := R) |>.1, fun y => ?_⟩
  let z : K ⊗[k] R := y
  have h := (fixedTensorDescription (k := k) (K := K) (V := R)).2 z
  constructor
  · rintro ⟨x, hx⟩ g
    exact (galoisTest_apply R g z).trans (h.mp ⟨x, hx⟩ g)
  · intro hg
    exact h.mpr (fun g => (galoisTest_apply R g z).symm.trans (hg g))

private theorem tensorInclusion_fixed {A : Type u} [Ring A] [Algebra k A] (R : TestAlgebra k) :
    Function.Injective (tensorMap (A := A) (includeTest (K := K) R)) ∧
      ∀ y : extendedBase (K := K) R ⊗[k] A, (∃ x : R ⊗[k] A, tensorMap (A := A) (includeTest R) x = y) ↔
        ∀ g : Gal(K/k), tensorMap (A := A) (galoisTest R g) y = y := by
  let assoc : (extendedBase (K := K) R ⊗[k] A) ≃ₗ[k] K ⊗[k] (R ⊗[k] A) :=
    (Algebra.TensorProduct.congr (extendedBaseEquiv (K := K) R) (AlgEquiv.refl : A ≃ₐ[k] A)).toLinearEquiv.trans
      (TensorProduct.assoc k K R A)
  have hι (x : R ⊗[k] A) : assoc (tensorMap (includeTest R) x) = (1 : K) ⊗ₜ[k] x := by
    induction x using TensorProduct.inductionOn with
    | tmul r a => rfl
    | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, hx, hy]
  have hact (g : Gal(K/k)) (x : extendedBase (K := K) R ⊗[k] A) :
      assoc (tensorMap (galoisTest R g) x) =
        (Descent.SemilinearAction.scalarExtension (R ⊗[k] A)).act g (assoc x) := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x a =>
      induction x using TensorProduct.inductionOn with
      | tmul b r => rfl
      | add x y hx hy => simp only [map_add, TensorProduct.add_tmul, hx, hy]
  have hd := fixedTensorDescription (k := k) (K := K) (V := R ⊗[k] A)
  refine ⟨fun x y h => hd.1 ((hι x).symm.trans ((congrArg assoc h).trans (hι y))), fun y => ?_⟩
  have hy : (∀ g : Gal(K/k), tensorMap (A := A) (galoisTest R g) y = y) ↔
      ∀ g : Gal(K/k), (Descent.SemilinearAction.scalarExtension (R ⊗[k] A)).act g (assoc y) =
        assoc y := by
    constructor
    · intro h g
      rw [← hact, h g]
    · intro h g
      apply assoc.injective
      rw [hact, h g]
  rw [hy, ← hd.2 (assoc y)]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, (hι x).symm⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, assoc.injective ((hι x).trans hx)⟩

private abbrev asAffine (G : AffineAlgebraicGroup k) : AffineGroupCategory k :=
  ⟨G.val, G.property.1⟩

private def coordinatesIso (G : AffineAlgebraicGroup k) :
    convolutionPoints (coordinateHopf (asAffine G)) ≅ PointsOf G.val :=
  hopfSpecPointIso _ ≪≫
    (groupPointsFunctor k).mapIso ((affineGroupInclusion k).mapIso (coordinateHopfSpecIso (asAffine G)))

private def pointValues (G : AffineAlgebraicGroup k) (R : TestAlgebra k)
    (p : (PointsOf G.val).obj R) : coordinateHopf (asAffine G) →ₐ[k] R :=
  (show WithConv _ from (coordinatesIso G).inv.app R p).ofConv

private theorem pointValues_bijective (G : AffineAlgebraicGroup k) (R : TestAlgebra k) :
    Function.Bijective (pointValues G R) :=
  WithConv.ofConv_bijective.comp ((coordinatesIso G).app R).symm.groupIsoToMulEquiv.bijective

private theorem pointValues_natural (G : AffineAlgebraicGroup k) {R S : TestAlgebra k}
    (f : R ⟶ S) (p : (PointsOf G.val).obj R) :
    pointValues G S ((PointsOf G.val).map f p) = f.hom.comp (pointValues G R p) := by
  exact congrArg (fun t : WithConv (coordinateHopf (asAffine G) →ₐ[k] S) => t.ofConv)
    (ConcreteCategory.congr_hom ((coordinatesIso G).inv.naturality f) p)

private theorem pointsInclusion_fixed (G : AffineAlgebraicGroup k) (R : TestAlgebra k) :
    Function.Injective ((PointsOf G.val).map (includeTest (K := K) R)) ∧
      ∀ y : (PointsOf G.val).obj (extendedBase (K := K) R),
        (∃ x, (PointsOf G.val).map (includeTest R) x = y) ↔
        ∀ g : Gal(K/k), (PointsOf G.val).map (galoisTest R g) y = y := by
  let F := PointsOf G.val
  let i := includeTest (K := K) R
  let S := extendedBase (K := K) R
  have hi := (includeTest_fixed (K := K) R).1
  refine ⟨fun x y h => (pointValues_bijective G R).1 ?_, fun y => ?_⟩
  · apply AlgHom.ext
    intro b
    apply hi
    have he : pointValues G S (F.map i x) b = pointValues G S (F.map i y) b :=
      congrArg (fun p => pointValues G S p b) h
    rw [pointValues_natural, pointValues_natural] at he
    exact he
  · constructor
    · rintro ⟨x, rfl⟩ g
      exact ConcreteCategory.congr_hom
        ((F.map_comp i (galoisTest R g)).symm.trans (congrArg F.map (includeTest_galois R g))) x
    · intro hy
      let f := pointValues G S y
      have hf (b : _) : f b ∈ i.hom.range := by
        apply (i.hom.mem_range).2
        apply ((includeTest_fixed (K := K) R).2 (f b)).2
        intro g
        have hg : pointValues G S (F.map (galoisTest R g) y) b = pointValues G S y b :=
          congrArg (fun p => pointValues G S p b) (hy g)
        rw [pointValues_natural] at hg
        exact hg
      let e := AlgEquiv.ofInjective i.hom hi
      let f₀ := e.symm.toAlgHom.comp (f.codRestrict _ hf)
      obtain ⟨x, hx⟩ := (pointValues_bijective G R).2 f₀
      refine ⟨x, (pointValues_bijective G S).1 ?_⟩
      rw [pointValues_natural, hx]
      apply AlgHom.ext
      intro b
      change i.hom (e.symm (f.codRestrict _ hf b)) = f b
      exact congrArg Subtype.val (e.apply_symm_apply (f.codRestrict _ hf b))

private theorem isometriesInclusion_fixed {A : Type u} [Ring A] [Algebra k A]
    (σ : Involution k A) (R : TestAlgebra k) :
    Function.Injective ((isometryPoints σ).map (includeTest (K := K) R)) ∧
      ∀ y : (isometryPoints σ).obj (extendedBase (K := K) R),
        (∃ x : (isometryPoints σ).obj R, (isometryPoints σ).map (includeTest R) x = y) ↔
          ∀ g : Gal(K/k), (isometryPoints σ).map (galoisTest R g) y = y := by
  let i := tensorMap (A := A) (includeTest (K := K) R)
  have hi := (tensorInclusion_fixed (K := K) (A := A) R).1
  let S := extendedBase (K := K) R
  let val (z : (isometryPoints σ).obj S) : S ⊗[k] A := (z.val : S ⊗[k] A)
  refine ⟨fun x y h => Subtype.ext (Units.ext (hi (congrArg val h))), fun y => ?_⟩
  constructor
  · rintro ⟨x, rfl⟩ g
    exact ConcreteCategory.congr_hom
      (((isometryPoints σ).map_comp (includeTest (K := K) R) (galoisTest R g)).symm.trans
        (congrArg (isometryPoints σ).map (includeTest_galois R g))) x
  · intro hy
    change (σ.baseChange (extendedBase (K := K) R)).isometries at y
    let v := (y.val : extendedBase (K := K) R ⊗[k] A)
    let w := ((y.val⁻¹ : (extendedBase (K := K) R ⊗[k] A)ˣ) : extendedBase (K := K) R ⊗[k] A)
    obtain ⟨v₀, hv₀⟩ := ((tensorInclusion_fixed (A := A) R).2 v).mpr
      (fun g => congrArg (fun z => ((z.val : (extendedBase (K := K) R ⊗[k] A)ˣ) :
        extendedBase (K := K) R ⊗[k] A)) (hy g))
    obtain ⟨w₀, hw₀⟩ := ((tensorInclusion_fixed (A := A) R).2 w).mpr
      (fun g => congrArg (fun z => (((z : (σ.baseChange (extendedBase (K := K) R)).isometries).val⁻¹ :
        (extendedBase (K := K) R ⊗[k] A)ˣ) : extendedBase (K := K) R ⊗[k] A)) (hy g))
    change i v₀ = v at hv₀
    change i w₀ = w at hw₀
    let u : (R ⊗[k] A)ˣ :=
      ⟨v₀, w₀, hi (by rw [map_mul, hv₀, hw₀, map_one]; exact y.val.val_inv),
        hi (by rw [map_mul, hv₀, hw₀, map_one]; exact y.val.inv_val)⟩
    have hu : u ∈ (σ.baseChange R).isometries := by
      change (σ.baseChange R).toLinearMap v₀ * v₀ = 1
      apply hi
      rw [map_mul, show i ((σ.baseChange R).toLinearMap v₀) =
          (σ.baseChange (extendedBase (K := K) R)).toLinearMap (i v₀) from
        tensorMap_involution σ (includeTest R) v₀, hv₀, map_one]
      exact y.property
    exact ⟨⟨u, hu⟩, Subtype.ext (Units.ext hv₀)⟩

/-- A compatible split comparison identifies the two groups of fixed points
and inherits naturality by injectivity of the extension maps. -/
private theorem descendNaturalIso (F H : TestAlgebra k ⥤ GrpCat.{u})
    (e : restrictTestAlgebra k K ⋙ F ≅ restrictTestAlgebra k K ⋙ H)
    (he : ∀ (R : TestAlgebra k) (g : Gal(K/k)) (x : F.obj (extendedBase (K := K) R)),
      e.hom.app (extendedTest R) (F.map (galoisTest R g) x) =
        H.map (galoisTest R g) (e.hom.app (extendedTest R) x))
    (hF : ∀ R : TestAlgebra k, Function.Injective (F.map (includeTest (K := K) R)) ∧
      ∀ y : F.obj (extendedBase (K := K) R),
        (∃ x, F.map (includeTest R) x = y) ↔ ∀ g : Gal(K/k), F.map (galoisTest R g) y = y)
    (hH : ∀ R : TestAlgebra k, Function.Injective (H.map (includeTest (K := K) R)) ∧
      ∀ y : H.obj (extendedBase (K := K) R),
        (∃ x, H.map (includeTest R) x = y) ↔ ∀ g : Gal(K/k), H.map (galoisTest R g) y = y) :
    ∃ d : F ≅ H, ∀ (R : TestAlgebra k) (x : F.obj R),
      H.map (includeTest (K := K) R) (d.hom.app R x) =
        e.hom.app (extendedTest R) (F.map (includeTest R) x) := by
  let j (R : TestAlgebra k) := (e.app (extendedTest (K := K) R)).groupIsoToMulEquiv
  have existsLift (R : TestAlgebra k) (x : F.obj R) :
      ∃ y : H.obj R, H.map (includeTest (K := K) R) y = j R (F.map (includeTest R) x) := by
    apply ((hH R).2 _).2
    intro g
    exact (he R g (F.map (includeTest R) x)).symm.trans
      (congrArg (j R) (((hF R).2 _).1 ⟨x, rfl⟩ g))
  let m (R : TestAlgebra k) : F.obj R →* H.obj R :=
    { toFun := fun x => (existsLift R x).choose
      map_one' := (hH R).1 (by
        rw [(existsLift R 1).choose_spec, map_one, map_one, map_one])
      map_mul' := fun x y => (hH R).1 (by
        rw [(existsLift R (x * y)).choose_spec, map_mul, map_mul, map_mul,
          (existsLift R x).choose_spec, (existsLift R y).choose_spec]) }
  have hm (R : TestAlgebra k) (x : F.obj R) :
      H.map (includeTest (K := K) R) (m R x) = j R (F.map (includeTest R) x) :=
    (existsLift R x).choose_spec
  have hb (R : TestAlgebra k) : Function.Bijective (m R) := by
    refine ⟨fun x y h => (hF R).1 ((j R).injective ?_), ?_⟩
    · rw [← hm, ← hm, h]
    · intro y
      let v := (j R).symm (H.map (includeTest R) y)
      have hv : j R v = H.map (includeTest R) y := (j R).apply_symm_apply _
      obtain ⟨x, hx⟩ := ((hF R).2 v).2 (fun g => (j R).injective (by
        rw [show j R (F.map (galoisTest R g) v) = H.map (galoisTest R g) (j R v) from he R g v,
          hv]
        exact ((hH R).2 _).1 ⟨y, rfl⟩ g))
      exact ⟨x, (hH R).1 ((hm R x).trans (hx ▸ hv))⟩
  have hn (R S : TestAlgebra k) (f : R ⟶ S) (x : F.obj R) :
      m S (F.map f x) = H.map f (m R x) := by
    apply (hH S).1
    let f' := (restrictTestAlgebra k K).map (extendMap (K := K) f)
    have hF' (x : F.obj R) : F.map (includeTest (K := K) S) (F.map f x) =
        F.map f' (F.map (includeTest (K := K) R) x) :=
      ConcreteCategory.congr_hom
        (((F.map_comp f _).symm.trans (congrArg F.map (includeTest_natural (K := K) f))).trans
          (F.map_comp _ _)) x
    have hH' (y : H.obj R) : H.map (includeTest (K := K) S) (H.map f y) =
        H.map f' (H.map (includeTest (K := K) R) y) :=
      ConcreteCategory.congr_hom
        (((H.map_comp f _).symm.trans (congrArg H.map (includeTest_natural (K := K) f))).trans
          (H.map_comp _ _)) y
    rw [hm, hF', hH', hm]
    exact ConcreteCategory.congr_hom (e.hom.naturality (extendMap (K := K) f)) _
  let d : F ≅ H := NatIso.ofComponents
    (fun R => (MulEquiv.ofBijective (m R) (hb R)).toGrpIso)
    (fun f => GrpCat.ext (hn _ _ f))
  exact ⟨d, hm⟩

end FixedPoints

/-- Associativity of scalar extension with a possibly noncommutative algebra
in the right factor. -/
private def extendScalarsEquiv (S : Type u) [CommRing S] [Algebra K S] [Algebra k S]
    [IsScalarTower k K S] (B : Type u) [Ring B] [Algebra k B] :
    S ⊗[k] B ≃ₐ[S] S ⊗[K] (K ⊗[k] B) :=
  AlgEquiv.ofLinearEquiv (TensorProduct.AlgebraTensorModule.cancelBaseChange k K S S B).symm
    (by simp [Algebra.TensorProduct.one_def])
    (LinearMap.map_mul_of_map_mul_tmul (fun _ _ _ _ => by simp))

private theorem extendScalarsEquiv_tmul (S : Type u) [CommRing S] [Algebra K S] [Algebra k S]
    [IsScalarTower k K S] (B : Type u) [Ring B] [Algebra k B] (r : S) (x : B) :
    extendScalarsEquiv (k := k) (K := K) S B (r ⊗ₜ[k] x) =
      r ⊗ₜ[K] ((1 : K) ⊗ₜ[k] x) := rfl

namespace FixedAlgebra

variable {P : AdjointPresentation k I} {a : Cocycle (K := K) P}
variable (D : FixedAlgebra P a)

private def splitAt (S : TestAlgebra K) :
    (overBase k K S ⊗[k] (D.action.fixedSubalgebra : Type u)) ≃ₐ[S] MatrixAlgebra I S := by
  letI : Algebra k S := (overBase k K S).algebra
  letI : IsScalarTower k K S := IsScalarTower.of_algebraMap_eq' rfl
  let m := (RootData.SymplecticDatumAdjointDescent.matrixScalarExtension K I S).choose
  exact (extendScalarsEquiv (k := k) (K := K) S (D.action.fixedSubalgebra : Type u)).trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S) D.split).trans m)

private theorem splitAt_pure (S : TestAlgebra K) (r : S) (x : D.action.fixedSubalgebra) :
    D.splitAt S (r ⊗ₜ[k] x) = r • ((relabel I K).symm x.val).map (algebraMap K S) := by
  letI : Algebra k S := (overBase k K S).algebra
  letI : IsScalarTower k K S := IsScalarTower.of_algebraMap_eq' rfl
  let h := (RootData.SymplecticDatumAdjointDescent.matrixScalarExtension K I S)
  let m := h.choose
  change m ((Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S) D.split)
    ((extendScalarsEquiv (k := k) (K := K) S (D.action.fixedSubalgebra : Type u)) (r ⊗ₜ[k] x))) = _
  rw [extendScalarsEquiv_tmul]
  change m (r ⊗ₜ[K] D.split ((1 : K) ⊗ₜ[k] x)) = _
  rw [D.splitPure, one_smul, h.choose_spec.1]

private theorem splitAt_involution (S : TestAlgebra K) (x : overBase k K S ⊗[k] (D.action.fixedSubalgebra : Type u)) :
    D.splitAt S ((D.involution.baseChange (overBase k K S)).toLinearMap x) =
      adjoint (D.splitAt S x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
    rw [Involution.baseChange_tmul, splitAt_pure, splitAt_pure, D.involutionFormula,
      adjoint_smul, (RootData.SymplecticDatumAdjointDescent.adjointIdentities I K).2.2.2.2
        (algebraMap K S)]
  | add x y hx hy => simp only [map_add, adjoint_add, hx, hy]

private theorem splitAt_natural {S T : TestAlgebra K} (f : S ⟶ T)
    (x : overBase k K S ⊗[k] (D.action.fixedSubalgebra : Type u)) :
    D.splitAt T (tensorMap ((restrictTestAlgebra k K).map f) x) = (D.splitAt S x).map f.hom := by
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
    rw [Algebra.TensorProduct.map_tmul, splitAt_pure, splitAt_pure]
    ext i j
    change f.hom r * algebraMap K T ((relabel I K).symm x.val i j) =
      f.hom (r * algebraMap K S ((relabel I K).symm x.val i j))
    rw [map_mul, f.hom.commutes]
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, map_add]
    ext i j
    exact (map_add f.hom _ _).symm

private theorem splitAt_twist {S T : TestAlgebra K} (g : Gal(K/k))
    (f : overBase k K S ⟶ overBase k K T)
    (hf : ∀ b : K, f.hom (algebraMap K S b) = algebraMap K T (g b))
    (x : overBase k K S ⊗[k] (D.action.fixedSubalgebra : Type u)) :
    D.splitAt T (tensorMap f x) =
      P.onAlgebra (overBase k K T) ((PointsOf P.quotient.val).map (coefficientHom T) (a g))
        ((D.splitAt S x).map f.hom) := by
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
    rw [Algebra.TensorProduct.map_tmul, splitAt_pure, splitAt_pure]
    change f.hom r • ((relabel I K).symm x.val).map (algebraMap K T) = _
    let X := (relabel I K).symm x.val
    have hcoeff : ((X.map (algebraMap K S)).map f.hom) =
        (X.map g).map (coefficientHom T).hom := by
      ext i j
      exact hf _
    have hsmul : (r • X.map (algebraMap K S)).map f.hom =
        (f.hom r) • ((X.map (algebraMap K S)).map f.hom) := by
      ext i j
      exact map_mul f.hom _ _
    erw [hsmul, hcoeff, map_smul, ← P.algebraNatural]
    have hX : P.onAlgebra (CommAlgCat.of k K) (a g) (X.map g) = X := by
      apply (relabel I K).injective
      rw [← D.twist]
      exact congrArg (D.action.act g) ((relabel I K).apply_symm_apply x.val) |>.trans
        ((x.property g).trans ((relabel I K).apply_symm_apply x.val).symm)
    rw [hX]
    rfl
  | add x y hx hy =>
    have hadd : ((D.splitAt S x + D.splitAt S y).map f.hom) =
        (D.splitAt S x).map f.hom + (D.splitAt S y).map f.hom := by
      ext i j
      exact map_add f.hom _ _
    erw [map_add, map_add, map_add, hadd, map_add, hx, hy]

/-- Split isometries are the ordinary symplectic matrices, with their matrix
multiplication and the same scalar-extension map on the underlying elements. -/
private def splitIsometry (S : TestAlgebra K) :
    (isometryPoints D.involution).obj (overBase k K S) ≃* PointGroup I S := by
  let e := D.splitAt S
  have hSp (X : MatrixAlgebra I S) :=
    (RootData.SymplecticDatumAdjointDescent.adjointIdentities I S).2.2.2.1 X
  let m : (isometryPoints D.involution).obj (overBase k K S) →* PointGroup I S :=
    { toFun := fun x => ⟨e ↑x.val, (hSp _).2 (by
        rw [← splitAt_involution, ← map_mul]
        exact congrArg e x.property |>.trans (map_one e))⟩
      map_one' := Subtype.ext (map_one e)
      map_mul' := fun x y => Subtype.ext (map_mul e
        (x.val : overBase k K S ⊗[k] (D.action.fixedSubalgebra : Type u))
        (y.val : overBase k K S ⊗[k] (D.action.fixedSubalgebra : Type u))) }
  refine MulEquiv.ofBijective m ⟨fun x y h => ?_, fun g => ?_⟩
  · exact Subtype.ext (Units.ext (e.injective (congrArg Subtype.val h)))
  · let u : (overBase k K S ⊗[k] (D.action.fixedSubalgebra : Type u))ˣ :=
      ⟨e.symm g.val, e.symm (g⁻¹).val,
        e.injective (by rw [map_mul, e.apply_symm_apply, e.apply_symm_apply, map_one]
                        exact congrArg Subtype.val (mul_inv_cancel g)),
        e.injective (by rw [map_mul, e.apply_symm_apply, e.apply_symm_apply, map_one]
                        exact congrArg Subtype.val (inv_mul_cancel g))⟩
    refine ⟨⟨u, ?_⟩, Subtype.ext (e.apply_symm_apply g.val)⟩
    change (D.involution.baseChange (overBase k K S)).toLinearMap (e.symm g.val) * e.symm g.val = 1
    apply e.injective
    rw [map_mul, splitAt_involution, e.apply_symm_apply, map_one]
    exact (hSp g.val).mp g.property

private theorem splitIsometry_apply (S : TestAlgebra K)
    (x : (isometryPoints D.involution).obj (overBase k K S)) :
    (D.splitIsometry S x).val = D.splitAt S (x.val : overBase k K S ⊗[k] (D.action.fixedSubalgebra : Type u)) := rfl

private def splitIsometryIso :
    restrictTestAlgebra k K ⋙ isometryPoints D.involution ≅
    restrictTestAlgebra k K ⋙ symplecticPoints k I :=
  NatIso.ofComponents (fun S => (D.splitIsometry S).toGrpIso) (by
    intro S T f
    apply GrpCat.ext
    intro x
    exact Subtype.ext (D.splitAt_natural f (x.val : overBase k K S ⊗[k] (D.action.fixedSubalgebra : Type u))))

private theorem splitIsometry_twist {S T : TestAlgebra K} (g : Gal(K/k))
    (f : overBase k K S ⟶ overBase k K T)
    (hf : ∀ b : K, f.hom (algebraMap K S b) = algebraMap K T (g b))
    (x : (isometryPoints D.involution).obj (overBase k K S)) :
    D.splitIsometry T ((isometryPoints D.involution).map f x) =
      P.onGroup (overBase k K T) ((PointsOf P.quotient.val).map (coefficientHom T) (a g))
        (mapSymplecticPoint f.hom.toRingHom (D.splitIsometry S x)) :=
  Subtype.ext ((D.splitAt_twist g f hf
    (x.val : overBase k K S ⊗[k] (D.action.fixedSubalgebra : Type u))).trans
    (P.groupMatrix (overBase k K T)
      ((PointsOf P.quotient.val).map (coefficientHom T) (a.val g))
      (mapSymplecticPoint f.hom.toRingHom (D.splitIsometry S x))).symm)

end FixedAlgebra

private def multiplyTest (S : TestAlgebra K) : extendedTest (overBase k K S) ⟶ S := by
  letI : Algebra k S := (overBase k K S).algebra
  letI : IsScalarTower k K S := IsScalarTower.of_algebraMap_eq' rfl
  exact ConcreteCategory.ofHom (C := CommAlgCat K)
    (Algebra.TensorProduct.lift (Algebra.ofId K S) (AlgHom.id k S) (fun x y => Commute.all _ _))

private theorem multiplyTest_include (S : TestAlgebra K) :
    includeTest (K := K) (overBase k K S) ≫ (restrictTestAlgebra k K).map (multiplyTest (k := k) (K := K) S) =
      𝟙 (overBase k K S) := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro r
  change (algebraMap K S 1) * r = r
  rw [map_one, one_mul]

theorem descent : DescentStatement.{u} := by
  intro k K I _ _ _ _ _ _ _ _ P G a c
  obtain ⟨D⟩ := algebraDescent k K I P a
  let F := PointsOf G.val
  let H := isometryPoints D.involution
  let e := c.iso ≪≫ D.splitIsometryIso.symm
  have he (R : TestAlgebra k) (g : Gal(K/k)) (x : F.obj (extendedBase (K := K) R)) :
      e.hom.app (extendedTest R) (F.map (galoisTest R g) x) =
        H.map (galoisTest R g) (e.hom.app (extendedTest R) x) := by
    let S := extendedTest (K := K) R
    let j := D.splitIsometry S
    apply j.injective
    change j (j.symm (c.iso.hom.app S (F.map (galoisTest R g) x))) =
      j (H.map (galoisTest R g) (j.symm (c.iso.hom.app S x)))
    rw [j.apply_symm_apply]
    calc
      _ = P.onGroup (overBase k K S)
          ((PointsOf P.quotient.val).map (coefficientHom S) (a.val g))
          (mapSymplecticPoint (galoisTest R g).hom.toRingHom (c.iso.hom.app S x)) :=
        c.inner g S S (galoisTest R g) (galoisTest_semilinear R g) x
      _ = _ := by
        have ht := D.splitIsometry_twist g (galoisTest R g) (galoisTest_semilinear R g)
          (j.symm (c.iso.hom.app S x))
        erw [show D.splitIsometry S (j.symm (c.iso.hom.app S x)) = c.iso.hom.app S x from
          j.apply_symm_apply _] at ht
        exact ht.symm
  obtain ⟨d, hd⟩ := descendNaturalIso F H e he (pointsInclusion_fixed G)
    (isometriesInclusion_fixed D.involution)
  refine ⟨⟨D, d, D.splitAt, D.splitAt_pure, D.splitAt_involution,
    fun σ _ _ f hf x => D.splitAt_twist σ f hf x, ?_⟩⟩
  intro S x
  have h : d.hom.app (overBase k K S) x = e.hom.app S x := by
    let R : TestAlgebra k := overBase k K S
    let i := includeTest (K := K) R
    let f := (restrictTestAlgebra k K).map (multiplyTest (k := k) (K := K) S)
    have hF : F.map f (F.map i x) = x := by
      exact ConcreteCategory.congr_hom
        (((F.map_comp i f).symm.trans (congrArg F.map (multiplyTest_include S))).trans
          (F.map_id _)) x
    have hH (y : H.obj R) : H.map f (H.map i y) = y := by
      exact ConcreteCategory.congr_hom
        (((H.map_comp i f).symm.trans (congrArg H.map (multiplyTest_include S))).trans
          (H.map_id _)) y
    calc
      _ = H.map f (H.map i (d.hom.app R x)) := (hH _).symm
      _ = H.map f (e.hom.app (extendedTest R) (F.map i x)) := congrArg (H.map f) (hd R x)
      _ = e.hom.app S (F.map f (F.map i x)) :=
        (ConcreteCategory.congr_hom (e.hom.naturality (multiplyTest (k := k) (K := K) S)) (F.map i x)).symm
      _ = _ := congrArg (e.hom.app S) hF
  exact congrArg Subtype.val (by
    change D.splitIsometry S (d.hom.app _ x) = c.iso.hom.app S x
    rw [h]
    exact (D.splitIsometry S).apply_symm_apply _)

end

end LinearAlgebraicGroups.Arithmetic.SymplecticIsometryDescent
