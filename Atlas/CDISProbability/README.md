# CDIS probability in Lean

This ATLAS v2 entry formalizes the probability chapters (Probabilités I to V) of CDIS, the
Mines Paris course *Calcul Différentiel, Intégral et Stochastique* by Sébastien Boisgérault,
Thomas Romary, Emilie Chautru and Pauline Bernard
([source](https://github.com/boisgera/CDIS), commit `afa15a2`, CC BY-NC-SA 4.0). The Lean
statements are original work; the mathematics is standard probability theory.

The course has 102 tagged statements. Three carry no mathematical content; the other 99 each
have a roadmap article. Of these, 56 are already in Mathlib and the roadmap cites the Mathlib
declaration. This entry formalizes 33 more, chosen where Mathlib lacked the result or states it
in a different form, with priority on the simulation chapter: 4 definitions, and 29 results
stated and proved. The remaining 10 are described in the roadmap and not formalized yet. Everything lives in
namespace `CDIS`; the module prefix is `Code`.

## Main results

| Course | Lean | File |
|---|---|---|
| Inversion method: `F⁻(U)` has the law of `X` | `CDIS.hasLaw_genInv_cdf` | `Code/ChapterV/Inversion.lean` |
| Uniform law on the subgraph of a density (rejection) | `CDIS.isUniform_subgraph` | `Code/ChapterV/Rejection.lean` |
| Box-Muller: two independent `N(0, 1)` | `CDIS.boxMuller_gaussian` | `Code/ChapterV/BoxMuller.lean` |
| Importance sampling, optimal instrumental density | `CDIS.tendsto_importanceSampling`, `CDIS.isMinOn_optimal_density` | `Code/ChapterV/ImportanceSampling.lean` |
| Conditional density and conditional law | `CDIS.condDistrib_ae_eq_withDensity_condDensity` | `Code/ChapterIII/Densities.lean` |
| Conditional transfer, independence criterion | `CDIS.condExpGiven_comp_prod_ae_eq`, `CDIS.indepFun_iff_condDistrib_ae_eq_const` | `Code/ChapterIII/ConditionalLaws.lean` |
| Multidimensional central limit theorem | `CDIS.tendstoInDistribution_multivariate_clt` | `Code/ChapterIV/MultiCLT.lean` |
| Lévy's continuity theorem (limit continuous at 0) | `CDIS.exists_tendsto_of_tendsto_charFun` | `Code/Bridges/ChapterIV.lean` |

`Code/Bridges/` proves course statements from existing Mathlib results, and `Code/Check.lean`
names every Mathlib declaration cited in the roadmap, so a rename breaks the build.

## Corrections to the course

Three statements are false as written; the Lean files prove the counterexamples and the
corrected versions.

- Markov's inequality is stated for `a ∈ ℝ*` and fails for `a < 0` (`CDIS.not_markov_of_neg`);
  corrected with `a > 0` (`CDIS.markov_abs_pow`).
- Bienaymé-Chebyshev does not quantify `a` and fails for `a < 0` (`CDIS.not_chebyshev_of_neg`);
  corrected with `a > 0` (`CDIS.chebyshev_abs_sub`).
- The importance sampling identity needs `g > 0` wherever `f > 0`
  (`CDIS.not_forall_integral_eq_integral_ratio`); corrected with that hypothesis
  (`CDIS.integral_mul_eq_integral_ratio`).

## Roadmap

`roadmap/` is an autoform blueprint with one article per course statement, linked to the
Lean declarations; `sources/` maps articles to the course sections.

## Build and verify

```bash
lake exe cache get
lake build
lake build Verify
```

`lake build Verify` fails if any declaration in namespace `CDIS` depends on an axiom other than
`propext`, `Classical.choice` and `Quot.sound`, so in particular on any `sorry`.
Toolchain: Lean `v4.34.0`, Mathlib `v4.34.0`.
