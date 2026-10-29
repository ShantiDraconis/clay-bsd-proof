import ClayBSDProof.RankZeroE32

/-!
# Redução boa de `y² = x³ − x` fora de 2

Portado do ATK kernel (espelho público, M-Core commit `390e378`), `ATK/BSDTamagawaE32.lean`
(`boa_reducao_de_unidade`, `dois_unidade`, `boa_E32`). Os fatores de Tamagawa do mesmo arquivo
(`fatorTamagawa_E32`, `tamagawa_E32`) não foram portados: dependem da fórmula refinada do ATK
(`BSDRefinada`, `BSDInvariantes`), que não é usada aqui.

* `boa_reducao_de_unidade`: se `W` é integral sobre o DVR `R` e `Δ(W)` é unidade, o modelo
  minimal da Mathlib tem redução boa;
* `dois_unidade`: `2` é unidade em `ℤ_v` para todo primo `v ∤ 2`;
* `boa_E32`: `y² = x³ − x` (`Δ = 64`) tem redução boa em todo primo `v ∤ 2`.
-/

open IsDedekindDomain NumberField WeierstrassCurve IsDiscreteValuationRing

namespace ClayBSDProof.GoodReductionE32

section geral

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- **Integral com discriminante unidade ⇒ o modelo minimal tem redução boa.** -/
theorem boa_reducao_de_unidade (W : WeierstrassCurve K) [hW : IsIntegral R W]
    (hΔ : HeightOneSpectrum.valuation K (maximalIdeal R) W.Δ = 1) :
    (W.minimal R).HasGoodReduction R := by
  set C := (W.exists_isMinimal R).choose with hC
  have hmin : IsMinimal R (C • W) := (W.exists_isMinimal R).choose_spec
  have hWC : C⁻¹ • (C • W) = W := by rw [smul_smul, inv_mul_cancel, one_smul]
  have hmax := hmin.val_Δ_maximal
  have hint : IsIntegral R (C⁻¹ • (C • W)) := by rw [hWC]; exact hW
  have hle : valuation_Δ_aux R ((1 : VariableChange K) • (C • W)) ≤
      valuation_Δ_aux R (C⁻¹ • (C • W)) := by
    rw [hWC, ← Subtype.coe_le_coe, valuation_Δ_aux_eq_of_isIntegral R W, hΔ]
    exact (valuation_Δ_aux R _).2
  have key : valuation_Δ_aux R (C⁻¹ • (C • W)) ≤ valuation_Δ_aux R ((1 : VariableChange K) • (C • W)) :=
    hmax.2 hint hle
  rw [hWC, one_smul] at key
  have h1 : (valuation_Δ_aux R W : WithZero (Multiplicative ℤ)) = 1 := by
    rw [valuation_Δ_aux_eq_of_isIntegral R W, hΔ]
  have h2 : (1 : WithZero (Multiplicative ℤ)) ≤ (valuation_Δ_aux R (C • W) : WithZero (Multiplicative ℤ)) := by
    calc (1 : WithZero (Multiplicative ℤ)) = (valuation_Δ_aux R W : WithZero (Multiplicative ℤ)) :=
          h1.symm
      _ ≤ _ := Subtype.coe_le_coe.mpr key
  have h3 : (valuation_Δ_aux R (C • W) : WithZero (Multiplicative ℤ)) ≤ 1 := (valuation_Δ_aux R (C • W)).2
  have hval : HeightOneSpectrum.valuation K (maximalIdeal R) (C • W).Δ = 1 := by
    rw [← valuation_Δ_aux_eq_of_isIntegral]
    exact le_antisymm h3 h2
  exact ⟨hval⟩

end geral

variable (v : HeightOneSpectrum (𝓞 ℚ))

/-- `2` é unidade em `ℤ_v` se `v ∤ 2`. -/
theorem dois_unidade (h2 : (2 : 𝓞 ℚ) ∉ v.asIdeal) : IsUnit (2 : v.adicCompletionIntegers ℚ) := by
  have hv : Valued.v (2 : v.adicCompletion ℚ) = 1 := by
    have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) (v := v) (2 : 𝓞 ℚ)
    rw [HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.intValuation_eq_one_iff.mpr h2] at h
    change Valued.v (algebraMap (𝓞 ℚ) (v.adicCompletion ℚ) 2) = 1 at h
    rwa [map_ofNat] at h
  refine (Valuation.valuationSubring.integers
    (v := (Valued.v : Valuation (v.adicCompletion ℚ) (WithZero (Multiplicative ℤ))))).isUnit_of_one' ?_
  convert hv using 2
  exact map_ofNat _ 2

/-- `y² = x³ − x` tem redução boa (no modelo minimal da Mathlib) em todo primo `v ∤ 2`. -/
theorem boa_E32 (h2 : (2 : 𝓞 ℚ) ∉ v.asIdeal) :
    ((ClayBSDProof.RankZeroE32.E32.baseChange (v.adicCompletion ℚ)).minimal
      (v.adicCompletionIntegers ℚ)).HasGoodReduction (v.adicCompletionIntegers ℚ) := by
  have hint : IsIntegral (v.adicCompletionIntegers ℚ)
      (ClayBSDProof.RankZeroE32.E32.baseChange (v.adicCompletion ℚ)) := by
    apply isIntegral_of_exists_lift
    · exact ⟨0, by simp [ClayBSDProof.RankZeroE32.E32, ClayBSDProof.CongruentCurve.E]⟩
    · exact ⟨0, by simp [ClayBSDProof.RankZeroE32.E32, ClayBSDProof.CongruentCurve.E]⟩
    · exact ⟨0, by simp [ClayBSDProof.RankZeroE32.E32, ClayBSDProof.CongruentCurve.E]⟩
    · exact ⟨-1, by simp [ClayBSDProof.RankZeroE32.E32, ClayBSDProof.CongruentCurve.E]⟩
    · exact ⟨0, by simp [ClayBSDProof.RankZeroE32.E32, ClayBSDProof.CongruentCurve.E]⟩
  refine boa_reducao_de_unidade (v.adicCompletionIntegers ℚ) _ ?_
  have hΔ : (ClayBSDProof.RankZeroE32.E32.baseChange (v.adicCompletion ℚ)).Δ =
      algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (2 ^ 6) := by
    have h64 : ClayBSDProof.RankZeroE32.E32.Δ = 64 := by
      norm_num [ClayBSDProof.RankZeroE32.E32, ClayBSDProof.CongruentCurve.E, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
        WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ, h64, map_pow, map_ofNat, map_ofNat]
    norm_num
  rw [hΔ, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
  exact IsLocalRing.notMem_maximalIdeal.mpr ((dois_unidade v h2).pow 6)

end ClayBSDProof.GoodReductionE32
