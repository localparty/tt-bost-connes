# tt-bost-connes

**Tomita–Takesaki modular theory of the Bost–Connes algebra at β = 1, formalized in Lean 4**

*G Six. math.OA submission, 2026.*

This repository hosts the paper and its Lean 4 formalization. The paper develops the Tomita–Takesaki modular theory of the Bost–Connes C\*-dynamical system $(B_K, \alpha_t, \omega_1)$ for $K = \mathbb{Q}(i)$ at the critical KMS state $\beta = 1$, with all five main results (Theorems A–E) formalized in Lean 4 against a pinned Mathlib revision.

## Repository contents

| Path | Contents |
|---|---|
| `preprint.md` | The paper (markdown source; §§1–9 + References + Appendix A). |
| `formalization/` | Git submodule → `integers-community--tt-bost-connes-lean`. The Lean 4 substrate: 11 modules in `Integers/TomitaTakesaki/`. |
| `LICENSE` | CC-BY-4.0. |

## Main results

- **Theorem A** — GNS triple + identification of $\pi_{\omega_1}(B_K)''$ as the unique injective type III$_1$ factor (via ITPFI factorization + [AW68] + [Haa87])
- **Theorem B** — Modular pair $(\Delta, J)$ via polar decomposition of the Tomita involution
- **Theorem C** — Modular flow theorem $\sigma_t = \alpha_t$ on $M$ (unconditional, via Takesaki's KMS-uniqueness theorem [BR97, Thm. 5.3.10])
- **Theorem D** — Galois compatibility of $(B_K, J)$ under $\mathrm{Gal}(K/\mathbb{Q})$
- **Theorem E** — Spectral realization $D_\infty = \log \Delta$ with explicit Hecke-basis eigenvalues

The scope partition (prose status × Lean status × discharge route) lives in §1.5 of the paper.

## Lean substrate at a glance

Extracted from `integers-mathlib-blueprint-tt-impl` at commit `1ca33cb` (Phase 6 sweep):

- **0 code-level sorries** across the entire formalization chain
- **8 named programme-level axioms** (6 carrying documented literature citations + 2 recording Mathlib infrastructure gaps with documented discharge paths)
- **6 documented scaffold-layer placeholders** (each with a stated discharge route)
- **1 Lean substrate hypothesis** (`hSubstrate_iii` for Theorem C, recorded as Open Problem 9.1)
- **Antilinear.lean** (230 lines): project-local polar-decomposition theory for unbounded antilinear operators, proposed for Mathlib upstream

See `formalization/README.md` for the full module inventory and build instructions.

## Build and verify

```bash
git clone --recursive <this-repo-url>
cd tt-bost-connes/formalization
elan default leanprover/lean4:v4.29.1
lake update
lake build Integers.TomitaTakesaki.Assembly      # Theorems A–E
lake build Integers.TomitaTakesaki.TomitaS       # Tomita S + modular data
lake build Integers.TomitaTakesaki.Antilinear    # antilinear-operator substrate
```

Toolchain: Lean 4 v4.29.1. Mathlib pinned at `5e932f97dd25535344f80f9dd8da3aab83df0fe6`.

## Pre-registration and submission

This work is pre-registered on Zenodo as a timestamped scope commitment; the deposit DOI is recorded in `preprint.md` footnote ² alongside this repository URL. The eventual arXiv math.OA submission and journal submission (J. Funct. Anal. tier) carry the Zenodo DOI in their metadata.

## License

CC-BY-4.0 (paper text + Lean source). See `LICENSE`.

## Provenance

This paper was developed through an adversarial-fleet peer-review-simulation discipline (cycles 7→8→9 against four generic-referee archetypes — skeptical-formalist / hostile-rejecter / scope-auditor / ua-auditor — multi-model rotation across Opus 4.8 / Sonnet 4.6 / Fable 5). Theorem C was upgraded from a named-hypothesis-conditional form to its unconditional form during the cycle-08→09 transition, via a focused BR97 verification consult. Two-consecutive-clean panel verdicts (cycles 8 + 9) cleared Layer C per the fleet's pass criteria.

During the preparation of this work, the author used Claude Opus 4.7. The author reviewed all content and takes full responsibility for the paper.
