import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.FiniteTypeConstants
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.PicardVessiotRing
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.UniversalSolutionRing
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.PicardVessiotExistence

namespace GaloisFormalization.PV

universe u v

private theorem stable_comap {kind : OperatorKind} {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] {D : Operator kind R} {E : Operator kind S}
    {f : R →+* S} (hf : D.Commutes E f) {J : Ideal S} (hJ : E.IsStable (J : Set S)) :
    D.IsStable (J.comap f : Set R) := by
  have hforward {x : R} (hx : f x ∈ J) : f (D x) ∈ J :=
    (hf x).symm ▸ hJ.apply_mem hx
  cases kind with
  | differential => exact fun _ hx => hforward hx
  | difference =>
      refine ⟨fun _ hx => hforward hx, fun x hx => ?_⟩
      change f (D.toRingEquiv.symm x) ∈ J
      rw [hf.difference_symm x]
      exact hJ.symm_apply_mem hx

private theorem exists_maximal_stableIdeal {kind : OperatorKind} {R : Type u}
    [CommRing R] [Nontrivial R] [IsNoetherianRing R] (D : Operator kind R) :
    ∃ I : Ideal R, Maximal (fun J : Ideal R => J ≠ ⊤ ∧ D.IsStable (J : Set R)) I := by
  apply exists_maximal_of_wellFoundedGT
  refine ⟨⊥, bot_ne_top, ?_⟩
  have hforward {x : R} (hx : x ∈ (⊥ : Ideal R)) : D x ∈ (⊥ : Ideal R) := by
    have hx0 := (Submodule.mem_bot R).mp hx
    simp [hx0]
  cases kind with
  | differential => exact fun _ hx => hforward hx
  | difference =>
      refine ⟨fun _ hx => hforward hx, fun x hx => ?_⟩
      have hx0 := (Submodule.mem_bot R).mp hx
      change D.toRingEquiv.symm x ∈ (⊥ : Ideal R)
      simp [hx0]

private theorem quotient_isSimple {kind : OperatorKind} {R : Type u}
    [CommRing R] (D : Operator kind R) {I : Ideal R}
    (hI : Maximal (fun J : Ideal R => J ≠ ⊤ ∧ D.IsStable (J : Set R)) I) :
    (D.quotient I hI.1.2).IsSimple := by
  refine ⟨Ideal.Quotient.nontrivial_iff.mpr hI.1.1, ?_⟩
  intro J hJ
  by_cases htop : J = ⊤
  · exact Or.inr htop
  left
  let q := Ideal.Quotient.mk I
  have hker : (⊥ : Ideal (R ⧸ I)).comap q = I := Ideal.mk_ker
  have hle : I ≤ J.comap q := hker.ge.trans (Ideal.comap_mono bot_le)
  have hJproper : J.comap q ≠ ⊤ := fun h => htop (Ideal.comap_eq_top_iff.mp h)
  have hJstable := stable_comap (D.quotient_commutes I hI.1.2) hJ
  apply Ideal.comap_injective_of_surjective q Ideal.Quotient.mk_surjective
  exact (le_antisymm (hI.2 ⟨hJproper, hJstable⟩ hle) hle).trans hker.symm

private theorem fundamental_map {kind : OperatorKind} {K : Type u} [Field K]
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    {n : ℕ} {A : LinearSystem kind K n} {D : Operator kind R} {E : Operator kind S}
    {X : Matrix.GeneralLinearGroup (Fin n) R} (hX : A.IsFundamental D X)
    (f : R →ₐ[K] S) (hf : D.Commutes E f) :
    A.IsFundamental E (Matrix.GeneralLinearGroup.map f.toRingHom X) := by
  have hcoeff : (A.mapCoefficients R).map f = A.mapCoefficients S :=
    Matrix.ext fun i j => f.commutes (A.coefficientMatrix i j)
  have hop : (X.val.map f).map E.apply = (X.val.map D.apply).map f :=
    Matrix.ext fun i j => (hf (X.val i j)).symm
  change X.val.map D.apply = A.mapCoefficients R * X.val at hX
  change (X.val.map f).map E.apply = A.mapCoefficients S * X.val.map f
  rw [hop, hX, Matrix.map_mul (f := f), hcoeff]

private theorem matrixGeneratedSubalgebra_map {K : Type u} [Field K]
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    {n : ℕ} (X : Matrix.GeneralLinearGroup (Fin n) R) (f : R →ₐ[K] S) :
    matrixGeneratedSubalgebra K (Matrix.GeneralLinearGroup.map f.toRingHom X) =
      (matrixGeneratedSubalgebra K X).map f := by
  let Y := Matrix.GeneralLinearGroup.map f.toRingHom X
  have hinv : f (LinearSystem.determinantInverse X) = LinearSystem.determinantInverse Y := by
    simp only [Y, LinearSystem.determinantInverse, Matrix.GeneralLinearGroup.map_det, ← map_inv]
    rfl
  have hentries : f '' (Set.range fun ij : Fin n × Fin n => X.val ij.1 ij.2) =
      Set.range (fun ij : Fin n × Fin n => Y.val ij.1 ij.2) :=
    (Set.range_comp' f _).symm
  change matrixGeneratedSubalgebra K Y = _
  rw [matrixGeneratedSubalgebra, matrixGeneratedSubalgebra, ← Algebra.adjoin_image,
    Set.image_insert_eq, hinv, hentries]

/-- Every system over a Picard–Vessiot base field has a Picard–Vessiot ring,
with the same constants in the ring and its total extension. -/
theorem picardVessiot_exists : Specs.picardVessiotExists.{u} := by
  intro kind K _ n D A hK
  change OperatorField kind K at D
  change LinearSystem kind K n at A
  change D.IsBaseField at hK
  let U := UniversalSolutionRing.Ring K n
  let : Nontrivial U := UniversalSolutionRing.nontrivial K n
  let : IsNoetherianRing U := UniversalSolutionRing.isNoetherian K n
  let : Algebra.FiniteType K U := UniversalSolutionRing.finiteType K n
  obtain ⟨δ, hδ, hX⟩ := UniversalSolutionRing.exists_operator D A
  obtain ⟨I, hI⟩ := exists_maximal_stableIdeal δ
  let R := U ⧸ I
  let E := δ.quotient I hI.1.2
  have hsimple : E.IsSimple := quotient_isSimple δ hI
  let : Nontrivial R := hsimple.1
  let q : U →ₐ[K] R := Ideal.Quotient.mkₐ K I
  have hq : δ.Commutes E q := δ.quotient_commutes I hI.1.2
  have hbase : D.IsAlgebra E := hq.comp hδ.1
  let X := UniversalSolutionRing.genericMatrix K n
  have hgen : matrixGeneratedSubalgebra K X = ⊤ := by
    simpa only [X, matrixGeneratedSubalgebra, Set.union_comm, Set.singleton_union] using
      UniversalSolutionRing.generated_by_entries K n
  have hPV : IsPicardVessiotRing D A E := by
    refine ⟨⟨hbase, (algebraMap K R).injective⟩, hsimple,
      Matrix.GeneralLinearGroup.map q.toRingHom X, fundamental_map hX q hq, ?_⟩
    rw [matrixGeneratedSubalgebra_map, hgen, Algebra.map_top]
    exact (AlgHom.range_eq_top q).mpr (Ideal.Quotient.mkₐ_surjective K I)
  have htotal := hPV.totalExtension
  exact ⟨R, inferInstanceAs (CommRing R), inferInstanceAs (Algebra K R), E, E.totalQuotient,
    htotal, Operator.constants_finiteType D E hK hsimple hbase,
    Operator.constants_finiteType_fractionRing D E E.totalQuotient hK hsimple hbase htotal.2.1⟩

end GaloisFormalization.PV
