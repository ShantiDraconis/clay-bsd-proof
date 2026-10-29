import ClayBSD

/-!
# Decomposição do enunciado fixado: continuação, posto analítico ≤ 1, posto analítico ≥ 2

Os três `Prop` abaixo são escritos sobre os objetos do enunciado fixado (`ClayBSD.IsContinuation`,
`ClayBSD.algebraicRank`, `analyticOrderAt`). Provado aqui, sem hipóteses:

* `conjecture_iff`: `ClayBSD.Conjecture ↔ ContinuationExists ∧ LowRankTheorem ∧ RankOpen`;
* `conjecture_iff_rankOpen`: **condicional** a `ContinuationExists` e `LowRankTheorem` (teoremas
  publicados, ver as docstrings; não estão na Mathlib), `ClayBSD.Conjecture ↔ RankOpen`.

Ou seja: módulo os resultados publicados citados, o que falta para o enunciado fixado é
exatamente `RankOpen` (posto analítico ≥ 2), que é **aberto**. Nada aqui prova `RankOpen`.

A fidelidade de `ContinuationExists` e `LowRankTheorem` aos teoremas publicados depende de
`WeierstrassCurve.LFunction` (Mathlib) ser a função L clássica, a mesma suposição que o
enunciado fixado faz.

Origem: a forma `GrossZagierKolyvagin → RankOpen → BSDRank` vem de
`ATK/Conditional/BSD.lean` (ATK kernel, espelho público, M-Core commit `390e378`), lá sobre um
modelo paramétrico `BSDModel`; aqui é reescrita sobre o enunciado fixado.
-/

namespace ClayBSDProof.RankDecomposition

/-- **Resultado externo publicado — existência da continuação.** Toda `E/ℚ` é modular
(A. Wiles, *Modular elliptic curves and Fermat's Last Theorem*, Ann. of Math. 141 (1995) 443–551,
https://doi.org/10.2307/2118559; R. Taylor e A. Wiles, Ann. of Math. 141 (1995) 553–572,
https://doi.org/10.2307/2118560; C. Breuil, B. Conrad, F. Diamond e R. Taylor, *On the
modularity of elliptic curves over ℚ*, J. Amer. Math. Soc. 14 (2001) 843–939,
https://doi.org/10.1090/S0894-0347-01-00370-8), logo `L(E, s)` é a função L de uma newform de
peso 2 e tem continuação inteira (Hecke); a convergência absoluta em `Re s > 3/2` vem da cota de
Hasse (H. Hasse, J. Reine Angew. Math. 175, 1936). Não está na Mathlib. -/
def ContinuationExists : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic], ∃ L : ℂ → ℂ, ClayBSD.IsContinuation E L

/-- **Resultado externo publicado — posto analítico ≤ 1.** Se `ord_{s=1} L(E, s) ≤ 1`, então o
posto de `E(ℚ)` é igual a ele: B. Gross e D. Zagier, *Heegner points and derivatives of L-series*,
Invent. Math. 84 (1986) 225–320, https://doi.org/10.1007/BF01388809; V. A. Kolyvagin, *Euler
systems*, The Grothendieck Festschrift II (Birkhäuser, 1990), reimpresso em Modern Birkhäuser
Classics (2007), https://doi.org/10.1007/978-0-8176-4575-5_11; com o corpo quadrático auxiliar
dado por D. Bump, S. Friedberg e J. Hoffstein, *Nonvanishing theorems for L-functions of
modular forms and their derivatives*, Invent. Math. 102 (1990) 543–618, e por M. R. Murty e
V. K. Murty, *Mean values of derivatives of modular L-series*, Ann. of Math. 133 (1991)
447–475; e a modularidade (BCDT 2001, acima) para toda
`E/ℚ`. Não está na Mathlib. -/
def LowRankTheorem : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (L : ℂ → ℂ), ClayBSD.IsContinuation E L →
    analyticOrderAt L 1 ≤ 1 → (analyticOrderAt L 1 : Cardinal) = ClayBSD.algebraicRank E

/-- **Aberto**: a parte do posto de BSD para posto analítico `≥ 2`. Não há teorema geral nesse
caso. -/
def RankOpen : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (L : ℂ → ℂ), ClayBSD.IsContinuation E L →
    2 ≤ analyticOrderAt L 1 → (analyticOrderAt L 1 : Cardinal) = ClayBSD.algebraicRank E

/-- Sob o enunciado fixado, toda continuação tem ordem igual ao posto. -/
theorem order_eq_of_conjecture (h : ClayBSD.Conjecture) (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {L : ℂ → ℂ} (hL : ClayBSD.IsContinuation E L) :
    (analyticOrderAt L 1 : Cardinal) = ClayBSD.algebraicRank E := by
  obtain ⟨L', hL', hord⟩ := h E
  rw [ClayBSD.continuation_unique E hL hL']
  exact hord

/-- **Decomposição exata** (sem hipóteses): o enunciado fixado é a conjunção da existência da
continuação, do caso de posto analítico `≤ 1` e do caso de posto analítico `≥ 2`. -/
theorem conjecture_iff :
    ClayBSD.Conjecture ↔ ContinuationExists ∧ LowRankTheorem ∧ RankOpen := by
  constructor
  · intro h
    refine ⟨fun E _ => ?_, fun E _ L hL _ => order_eq_of_conjecture h E hL,
      fun E _ L hL _ => order_eq_of_conjecture h E hL⟩
    obtain ⟨L, hL, -⟩ := h E
    exact ⟨L, hL⟩
  · rintro ⟨hC, hLow, hOpen⟩ E _
    obtain ⟨L, hL⟩ := hC E
    refine ⟨L, hL, ?_⟩
    by_cases h1 : analyticOrderAt L 1 ≤ 1
    · exact hLow E L hL h1
    · have h2 : (1 : ℕ∞) + 1 ≤ analyticOrderAt L 1 := Order.add_one_le_of_lt (not_le.mp h1)
      exact hOpen E L hL (by simpa [one_add_one_eq_two] using h2)

/-- **Condicional a resultados publicados** (`ContinuationExists`: Wiles, Taylor–Wiles, BCDT;
`LowRankTheorem`: Gross–Zagier, Kolyvagin): o enunciado fixado equivale a `RankOpen`. -/
theorem conjecture_iff_rankOpen (hC : ContinuationExists) (hLow : LowRankTheorem) :
    ClayBSD.Conjecture ↔ RankOpen :=
  conjecture_iff.trans ⟨fun h => h.2.2, fun h => ⟨hC, hLow, h⟩⟩

end ClayBSDProof.RankDecomposition
