# Tomita–Takesaki modular theory of the Bost–Connes algebra at β = 1, formalized in Lean 4²

**G Six**¹

*San Francisco, CA, USA*

¹ *During the preparation of this work, the author used Claude Opus 4.7.*

² *The Lean 4 formalization at https://github.com/localparty/tt-bost-connes (DOI [10.5281/zenodo.20674870](https://doi.org/10.5281/zenodo.20674870); Lean substrate independently archived at DOI [10.5281/zenodo.20674891](https://doi.org/10.5281/zenodo.20674891)) permits independent machine checking of the structural scaffold of every theorem; the substrate inventory — eight named axioms (§8.2), six documented scaffold-layer placeholders (§8.3), and one Lean substrate hypothesis (`hSubstrate_iii` for Theorem C, recorded as Mathlib Integration Target 9.1) — carries the load-bearing analytic content, each with a stated discharge route.*

**Abstract.** We develop the Tomita–Takesaki modular theory of the Bost–Connes C\*-dynamical system $(B_K, \alpha_t, \omega_1)$ for $K = \mathbb Q(i)$ at the critical KMS state $\omega_1$ (inverse temperature $\beta = 1$). The GNS representation is constructed explicitly as the completion of the quotient of $B_K$ by the null ideal of $\omega_1$, and the von Neumann algebra $\pi_{\omega_1}(B_K)''$ is identified, via the ITPFI factorization of $\omega_1$ together with the Haagerup uniqueness theorem [Haa87], as the unique injective type $\mathrm{III}\_1$ factor. The modular operator $\Delta$ and modular conjugation $J$ are obtained by polar decomposition of the closure of the involution $S : \pi(a)\Omega \mapsto \pi(a^\ast)\Omega$. We show that the modular automorphism group $\sigma_t$ coincides with the time evolution $\alpha_t$ on $M$, via Takesaki's KMS-uniqueness theorem [BR97, Thm. 5.3.10]: the transported time evolution $\widetilde\alpha_t$ on $M$ is a $\sigma$-weakly continuous one-parameter $\ast$-automorphism group for which $\omega_1$ — a faithful normal state — is a $\mathrm{KMS}\_1$ state, and the modular automorphism group is the unique such group, forcing $\sigma_t = \widetilde\alpha_t$. Compatibility of the Galois action of $\mathrm{Gal}(K/\mathbb Q)$ with the modular conjugation is established. The generator $D_\infty = \log \Delta$ of the modular flow is computed explicitly, with spectrum $\mathbb R$ and local ITPFI eigenvalues $-(n-m)\log N\mathfrak p$ on the Hecke basis. The construction is recorded in Lean 4 against a pinned Mathlib revision as a type-correct, sorry-free chain in which the load-bearing analytic content is isolated in eight explicitly named axioms — six carrying documented literature citations and two recording Mathlib infrastructure gaps with documented discharge paths — together with six scaffold-layer placeholders and one Lean substrate hypothesis (`hSubstrate_iii` for Theorem C), each with a stated discharge route (§§8.2–8.3). A 230-line file `Antilinear.lean` developing the core of the polar decomposition theory for unbounded antilinear operators (adjoint duality, modular operator, modulus via functional calculus) addresses a current gap in Mathlib; completion of the antiunitary construction and an upstream contribution to Mathlib are recorded in the Mathlib integration roadmap (§9). Four Mathlib integration targets are stated explicitly in §9 — each a Lean/Mathlib upstream task, not an open mathematical question: (9.1) Lean-side discharge of the Theorem C substrate hypothesis `hSubstrate_iii` via Mathlib formalization of the $W^\ast$-KMS-uniqueness theorem; (9.2) Mathlib upstream of the antilinear polar decomposition; (9.3) a soundness-audited discharge of the six Bost–Connes substrate axioms; (9.4) structural enrichment of the `BostConnesSystem` type for discharge of the two Hilbert-structure axioms.

**Keywords.** Tomita–Takesaki theory; Bost–Connes algebra; KMS states; type $\mathrm{III}\_1$ factor; ITPFI factorization; Lean 4 formalization.

**MSC 2020.** 46L36 (Classification of factors); 46L60 (Applications of selfadjoint operator algebras to physics); 82B10 (Quantum statistical mechanics, general); 68V20 (Formal mathematics).

---

## §1. Introduction

### §1.1. Tomita–Takesaki theory and Bost–Connes systems

Tomita–Takesaki modular theory, introduced by Tomita [Tom67] and developed by Takesaki [Tak70], associates to every faithful normal state $\omega$ on a von Neumann algebra $M$ a one-parameter group $\{\sigma_t^\omega\}\_{t \in \mathbb R}$ of \*-automorphisms — the modular automorphism group — and an antilinear conjugation $J : H \to H$ on the GNS Hilbert space — the modular conjugation — satisfying the central identity $JMJ = M'$. The structure is intrinsic to the pair $(M, \omega)$ and provides the foundation for the theory of type III factors [Tak03].

The Bost–Connes C\*-dynamical system $(B_K, \alpha_t, \omega_\beta)\_\beta$, introduced by Bost and Connes for $K = \mathbb Q$ in [BC95], was generalized to imaginary quadratic fields by Connes, Marcolli, and Ramachandran [CMR05] (see also [CM08, Ch. III]); the KMS classification for Bost–Connes type systems of general number fields was completed by Laca, Larsen, and Neshveyev [LLN09]. The algebra $B_K$ is a Hecke C\*-algebra constructed from the inclusion $\mathfrak o_K \hookrightarrow \widehat{\mathfrak o_K}^\times$; the time evolution $\alpha_t$ comes from a natural grading by absolute values of fractional ideals; and the family of KMS states $\omega_\beta$ at inverse temperature $\beta \geq 1$ exhibits a phase transition at the critical value $\beta = 1$. The critical state $\omega_1$ is the unique extremal KMS state in this regime [BC95, Thm. 25; LLN09]; for $\beta > 1$, the extremal KMS states are parameterized by ideal classes.

The von Neumann algebra $M_\beta := \pi_{\omega_\beta}(B_K)''$ generated by the GNS representation of $\omega_\beta$ at $\beta = 1$ is the unique injective type $\mathrm{III}\_1$ factor [Con76; Haa87] — uniqueness of the injective type $\mathrm{III}\_1$ factor being Haagerup's resolution of Connes' bicentralizer problem [Haa87] — as a consequence of the ITPFI factorization of $\omega_1$ across the prime ideals of $\mathfrak o_K$ [BC95, Prop. 33; CM08, Ch. III, §3.4]. The Araki–Woods classification [AW68] identifies the resulting infinite tensor product as a type $\mathrm{III}\_1$ factor in Connes' classification [Con73]; uniqueness within the injective class is [Haa87]. This places the modular structure of $(M_1, \omega_1)$ at a natural meeting point of operator algebras and arithmetic.

More recently, Connes, Consani, and Moscovici [CCM25] have developed a spectral-realization framework for the Bost–Connes system via prolate-spheroidal techniques and Carathéodory–Fejér extension; their construction yields a spectrum coinciding with the imaginary parts of nontrivial zeros of $\zeta_\mathbb Q(s)$ on the appropriate even-sector. The present work is complementary: we develop the Tomita–Takesaki modular theory at the critical state directly, through ITPFI factorization and polar decomposition of the modular involution. The two routes pass through different substrate (prolate-spheroidals vs. ITPFI + Araki–Woods + KMS uniqueness) and are best read in parallel.

The closest prior treatment is [CM08, Ch. III, §3.4], which develops the imaginary-quadratic Bost–Connes system together with elements of its modular theory but does not assemble the explicit polar-decomposition construction of $(\Delta, J)$ from the Tomita involution. The present paper adds two concrete contributions: an explicit polar-decomposition assembly of the modular pair via the Tomita involution $S$ together with the modular flow identification $\sigma_t = \alpha_t$ via Takesaki's $W^\ast$-KMS-uniqueness theorem (the route in §§4–5), and an accompanying Lean 4 formalization recording the structural chain L1 → L7 against a pinned Mathlib revision with explicit named axioms and a scaffold-layer placeholder inventory (§§8.2–8.3). The Lean formalization is the primary novelty contribution.

### §1.2. The critical KMS state and modular structure

We work throughout with $K = \mathbb Q(i)$; the construction adapts to other imaginary quadratic fields with minor adjustments. The $\mathrm{KMS}\_1$ state $\omega_1$ is faithful on $B_K$ [BC95, §3, eq. (15)] and admits the ITPFI factorization

$$
\widetilde{\omega}_1 \mspace{5mu} =\mspace{5mu}  \bigotimes_{\mathfrak{p}}\mspace{3mu}  {\widetilde{\omega}}_1^{(\mathfrak{p})},
$$

where the local factors ${\widetilde\omega}\_1^{(\mathfrak p)}$ act on $M_\mathfrak p \cong B(\ell^2(\mathbb N))$ with diagonal weights $\rho_\mathfrak p(n) = N\mathfrak p^{-n}$. The infinite tensor product yields a type $\mathrm{III}\_1$ factor in Connes' classification [Con73]; uniqueness within the injective class is [Haa87]. The modular operator $\Delta$ inherits a product structure from the local modular operators; we make this product structure precise in §4.

Takesaki's KMS-uniqueness theorem [BR97, Thm. 5.3.10] identifies the modular automorphism group of a faithful normal $\mathrm{KMS}\_\beta$ state with the underlying dynamics, up to the standard temperature-rescaling sign convention. Applied at the critical $\beta = 1$, this identifies $\sigma_t^{\omega_1}$ on $M$ with the extension $\widetilde\alpha_t$ of the time evolution from $\pi(B_K)$ to its bicommutant $M$ (Theorem C, §5). The argument is short — it requires only the existence + uniqueness of the $\sigma$-weakly continuous extension $\widetilde\alpha_t$ ([BR87, Prop. 2.5.22] applied to the standard form ${(M, \Omega_1)}$) and the transfer of the $\mathrm{KMS}\_1$ condition from $\pi(B_K)$ to $M$ ([BR97, Cor. 5.3.4]) — and is unconditional. The explicit prime-by-prime structural form of $\Delta = \bigotimes_\mathfrak p \Delta_\mathfrak p$ enters separately, as the explicit computation route for the modular operator $\Delta$ (Theorem B / Theorem E), not for the identification $\sigma_t = \alpha_t$ itself.

### §1.3. Main results

Let $K = \mathbb Q(i)$ and let $(B_K, \alpha_t, \omega_1)$ be the Bost–Connes C\*-dynamical system at the critical KMS state. Let $\pi_{\omega_1} : B_K \to B(H_R)$ denote the GNS representation, with cyclic vector $\Omega_1$, and write $M := \pi_{\omega_1}(B_K)''$.

**Theorem A** (GNS triple and type $\mathrm{III}\_1$ identification). The Hilbert space $H_R$ is canonically realized as the completion of the quotient $B_K / I_{\omega_1}$ under the inner product $\langle [a], [b] \rangle := \omega_1(a^\ast b)$, where $I_{\omega_1} = \{ a \in B_K : \omega_1(a^\ast a) = 0 \}$. The von Neumann algebra $M$ is the unique injective type $\mathrm{III}\_1$ factor.

**Theorem B** (Modular operator and conjugation). The conjugate-linear involution $S : \pi(a)\Omega_1 \mapsto \pi(a^\ast)\Omega_1$, defined on the dense subspace $\pi(B_K)\Omega_1 \subset H_R$, admits a closure $\bar S$. The polar decomposition $\bar S = J\,\Delta^{1/2}$ yields a positive self-adjoint operator $\Delta$ (the modular operator) and an antiunitary $J$ (the modular conjugation), satisfying $J^2 = I$ and $J \Delta J = \Delta^{-1}$.

**Theorem C** (Modular flow). The modular automorphism group $\sigma_t^{\omega_1}$ of $\omega_1$ coincides with the time evolution on the representation:

$$
\sigma_t^{\omega_1}\bigl(\pi(a)\bigr) \mspace{5mu} =\mspace{5mu}  \pi\bigl(\alpha_t(a)\bigr) \qquad \text{for all } a \in B_K,\ t \in \mathbb{R}.
$$

**Theorem D** (Galois compatibility). The Galois group $\mathrm{Gal}(K/\mathbb Q)$ acts on $B_K$ by \*-automorphisms; this action commutes with the time evolution and is compatible with the modular conjugation $J$ in the sense made precise in §6.

**Theorem E** (Spectral realization data). The self-adjoint operator $D_\infty := \log \Delta$ on $H_R$, defined via continuous functional calculus on the positive operator $\Delta$ from Theorem B, satisfies: (i) $\Delta^{it} = e^{itD_\infty}$ on $(\ker \Delta)^\perp$ for all $t \in \mathbb R$; (ii) $\mathrm{spec}(D_\infty) = \mathbb R$; (iii) on the dense subspace of finite simple tensors of the ITPFI factorization, $D_\infty$ acts as the diagonalized sum $\sum_\mathfrak p\,\log \Delta_\mathfrak p$ with local generators acting by $-(n-m)\log N\mathfrak p$ on the matrix unit $e_{nm}\Omega_\mathfrak p$.

The structural chain of §§3–7 has been recorded in Lean 4 against a pinned Mathlib revision as a type-correct, sorry-free chain. Eight programme-level axioms are declared explicitly: six are Bost–Connes substrate citations — existence, KMS uniqueness, faithfulness, ITPFI factorization (encoded as non-traciality; see §8.2 item 5), automorphism property, KMS condition — following [BC95], [LLN09], [AW68], [CM08], and [BR97]; two are structural axioms for the Hilbert space of the GNS quotient that record Mathlib infrastructure gaps with documented discharge paths (and would discharge automatically were Mathlib's normed-quotient theory more developed at the time of writing). Six scaffold-layer placeholders (§8.3), each typed as `True` or as an identity function, stand in for load-bearing analytic content at the Lean level; each carries a stated discharge route. The Lean substrate witness for Theorem C (the hypothesis `hSubstrate_iii` in module L6) remains conditional, reflecting the absence of a Mathlib formalization of the $W^\ast$-KMS-uniqueness theorem from which the prose proof of Theorem C derives; this is Mathlib Integration Target 9.1. A self-contained 230-line file `Antilinear.lean` developing the core of the polar decomposition theory for unbounded antilinear operators (adjoint duality, modular operator, modulus via functional calculus; cf. [Tak03, Thm. VIII.3.2]) addresses a current gap in Mathlib. Completion of the antiunitary $J$ construction and an upstream contribution to Mathlib are recorded as Mathlib Integration Target 9.2.

### §1.4. Outline and conventions

Section 2 sets up the Bost–Connes system at $\beta = 1$ and recalls the ITPFI factorization. Section 3 constructs the GNS triple and proves Theorem A. Section 4 establishes the modular pair $(\Delta, J)$ via polar decomposition (Theorem B). Section 5 proves Theorem C via Takesaki's KMS-uniqueness theorem. Section 6 treats the Galois compatibility (Theorem D). Section 7 records the spectral-realization data (Theorem E). Section 8 documents the Lean 4 formalization, the eight named axioms with their citations, and the antilinear polar decomposition contribution to Mathlib. Section 9 closes with the Mathlib integration roadmap — the upstream tasks that would tighten the Lean encoding.

**Conventions.** We write $K = \mathbb Q(i)$, $\mathfrak o_K = \mathbb Z[i]$, and $\widehat{\mathfrak o_K}^\times$ for the profinite completion. $B_K$ denotes the Bost–Connes C\*-algebra of $K$. $\mathrm{KMS}\_\beta$ denotes the Kubo–Martin–Schwinger condition at inverse temperature $\beta$. Modular structures use the standard notation: $\Delta$ for the modular operator, $J$ for the modular conjugation, $S$ for the closed extension of the involution, $\sigma_t$ for the modular automorphism group. We adopt **Connes' convention** $\sigma_t = \mathrm{Ad}(\Delta^{it})$ throughout. At $\beta = 1$, Takesaki's KMS-uniqueness theorem [BR97, Thm. 5.3.10] gives $\sigma_t^{\omega_1} = \widetilde\alpha_t$ on $M$ (Theorem C); under the opposite, Bratteli–Robinson convention $\tau_t = \sigma^\omega_{-\beta t}$, the identification would be $\widetilde\alpha_t = \sigma_{-t}^{\omega_1}$. We work with the Connes-sign identification throughout; the corresponding statements in the alternative convention follow by replacing $\Delta \leftrightarrow \Delta^{-1}$. The Lean 4 module corresponding to this paper is available at https://github.com/localparty/tt-bost-connes; the build instructions and the Mathlib SHA pin are recorded in Appendix A, and the structural scaffold can be machine-checked with three `lake build` invocations.

### §1.5. Status of the main results and the Lean formalization

The table below summarizes, for each main result (Theorems A–E) and the project-local `Antilinear.lean` contribution, the present status of the prose proof, the present status of the Lean formalization, and the discharge route for any conditional or scaffold-level content. The two-dimensional structure — prose status crossed with Lean status — makes the structural-vs-substrate boundary visible at the introduction level rather than only at §8.

| Item | Prose proof status | Lean status | Discharge route / Integration Target |
|---|---|---|---|
| **Theorem A** (GNS triple + $\mathrm{III}\_1$ identification, §3) | Unconditional ($H_R$ realized; $\mathrm{III}\_1$ identification via ITPFI + [AW68] + [Haa87]) | Structural scaffold recorded; the $\Omega_1$-separating property typed as `True` at the scaffold layer (§8.3 item 4); the two L2 Hilbert-structure axioms (§8.2 items 7–8) supply the inner-product structure of the GNS quotient | Separating: chains through faithfulness axiom `kms1_faithful`. L2 axioms: discharge via Mathlib normed-quotient enrichment → Mathlib Integration Target 9.4 |
| **Theorem B** (modular pair $(\Delta, J)$, §4) | Unconditional at prose layer (polar decomposition of closed antilinear involution via [Tak03, Ch. VI, Thm. 1.4]) | Δ is the genuine modular operator with real self-adjointness + positivity proofs; $J$ is the identity-function placeholder (§8.3 item 1) and the polar identity $\bar S = J\,\Delta^{1/2}$ is a `True` placeholder (§8.3 item 2) | Antiunitary $J$ + polar identity: Targets 1–2 → Mathlib Integration Target 9.2 |
| **Theorem C** (modular flow $\sigma_t = \alpha_t$, §5) | **Unconditional** at prose layer (Takesaki's $W^\ast$-KMS-uniqueness theorem [BR97, Thm. 5.3.10] applied to the faithful normal state $\omega_1$ on $M$, together with existence + uniqueness of the $\sigma$-weakly continuous extension $\widetilde\alpha_t$ from [BR87, Prop. 2.5.22] and KMS-transfer [BR97, Cor. 5.3.4]) | Conditional on the named substrate hypothesis `hSubstrate_iii` at the Lean level (L4 + L6). The Lean substrate gap reflects the absence in Mathlib of the $W^\ast$-KMS-uniqueness theorem, not a mathematical gap | Lean-side discharge of `hSubstrate_iii` via Mathlib formalization of $W^\ast$-KMS-uniqueness → Mathlib Integration Target 9.1 |
| **Theorem D** (Galois compatibility, §6) | Unconditional at prose layer (Galois-invariance of $N\mathfrak a$ + uniqueness of polar decomposition) | Galois action recorded as the identity-acting scaffold $G = \{e\}$ in L5; the intertwining $J \circ \widehat g = \widehat g \circ J$ typed as `True` (§8.3 item 6) | Genuine $\mathbb Z/2$ Galois action + Hecke-basis swap form: documented at §8.3 item 6; no separate integration target |
| **Theorem E** (spectral data $D_\infty = \log \Delta$, §7) | Unconditional at prose layer (Mathlib CFC + product structure of $\Delta$) | Recorded as a zero CLM scaffold (`spectral_realization`) until the ITPFI product structure of $\Delta$ is formalized; the genuine $D_\infty$ via $\mathrm{cfc}\,\log\,\Delta$ awaits the CFC instance chain | Infinite tensor product structure of $\Delta$: §8.3 item 3 (Mathlib gap, no integration target #) |
| **`Antilinear.lean`** (Mathlib gap-filler, §8.4) | Project-local theory of antilinear operators + polar decomposition (adjoint duality, modular operator, modulus via CFC) | Self-adjointness + positivity of $\Delta$ proved from adjoint identity; antiunitary $J$ and polar identity awaiting Targets 1–2 | Mathlib upstream PR → Mathlib Integration Target 9.2 |

The eight named axioms (§8.2) underlying every row above are the inventory: `bc_system_exists`, `kms1State_isKMS`, `kms1_unique`, `kms1_faithful`, `itpfi_factorization` (encoded as non-traciality), `time_evolution_is_automorphism` (the six L1 substrate citations), together with `gnsQuotientNACG_axiom` and `gnsQuotientIPS_axiom` (the two L2 Hilbert-structure axioms recording Mathlib infrastructure gaps). The math-vs-Lean conditionality of Theorem C is informative: the prose proof is unconditional from the operator-algebras literature, but the Lean encoding remains conditional on a substrate hypothesis until Mathlib hosts the $W^\ast$-KMS-uniqueness theorem from which the prose proof derives — a formalization target rather than a research target. This pattern is recurrent across the table: every "Lean-status" entry that names a placeholder or substrate hypothesis corresponds to a documented discharge route in §8.3 or to one of the four Mathlib integration targets of §9.

---

## §2. The Bost–Connes C\*-dynamical system at $\beta = 1$

This section recalls the construction of the Bost–Connes C\*-algebra $B_K$ for $K = \mathbb Q(i)$ together with its time evolution $\alpha_t$ and the canonical KMS state $\omega_1$ at the critical inverse temperature. The material is well known; we collect it here in the precise form needed by §§3–7. The reader familiar with [BC95, CM08] may skim this section for notation.

### §2.1. The algebra $B_K$ for $K = \mathbb Q(i)$

Throughout, $K = \mathbb Q(i)$ is the Gaussian field, $\mathfrak o_K = \mathbb Z[i]$ is its ring of integers, $\mathfrak o_K^\times = \{\pm 1, \pm i\}$ is the group of units, and $\widehat{\mathfrak o_K} = \prod_\mathfrak p\, \mathfrak o_{K,\mathfrak p}$ is the profinite completion of $\mathfrak o_K$ at its non-archimedean places. Let $I_K^+$ denote the multiplicative semigroup of nonzero integral ideals of $\mathfrak o_K$, and write $N\mathfrak a := \lvert\mathfrak o_K / \mathfrak a\rvert \in \mathbb Z_{>0}$ for the absolute norm of an ideal $\mathfrak a \in I_K^+$.

Following [BC95] (in the case $K = \mathbb Q$), the work of Connes, Marcolli, and Ramachandran [CMR05], and [CM08, Ch. III, §3] (in the present imaginary-quadratic case), the **Bost–Connes C\*-algebra of $K$** is the C\*-algebra

$$
B_K \mspace{5mu} :=\mspace{5mu}  C^\ast\mspace{-3mu} \bigl(\mspace{3mu} \mathfrak{o}_K \rtimes \mathfrak{o}_K^\sharp\mspace{3mu} ,\mspace{3mu}  \mathfrak{o}_K \rtimes \mathfrak{o}_K^\times\mspace{3mu} \bigr)_{\mathrm{Hecke}}
$$

constructed as the Hecke C\*-algebra of the almost-normal inclusion of the unit-stabilizer in the semidirect product of $\mathfrak o_K$ by the multiplicative semigroup $\mathfrak o_K^\sharp$ of nonzero principal ideals; equivalently, $B_K$ is generated by:

- a family of unitaries $\{u(\xi)\}\_{\xi \in K / \mathfrak o_K}$ encoding the roots of unity, satisfying $u(\xi) u(\eta) = u(\xi + \eta)$ and $u(0) = 1$;
- a family of isometries $\{\mu_\mathfrak a\}\_{\mathfrak a \in I_K^+}$ encoding the action of integral ideals, satisfying $\mu_{\mathfrak a\mathfrak b} = \mu_\mathfrak a\, \mu_\mathfrak b$ for coprime $\mathfrak a, \mathfrak b$;

subject to the Hecke relations between the two families. We refer to [BC95, §3] and [CM08, Ch. III, §3.2] for the full presentation. The algebra $B_K$ carries a natural state $\tau$ obtained by composing the standard expectation onto the abelian subalgebra $C(\mathfrak o_K \subset \widehat{\mathfrak o_K})$ with the Haar measure; $\tau$ plays no direct role below but underlies the identification of $B_K$ with the algebra of arithmetic operations on $\widehat{\mathfrak o_K}/\mathfrak o_K$ used in [CM08].

### §2.2. The time evolution $\alpha_t$

The time evolution on $B_K$ is the one-parameter group $\{\alpha_t\}\_{t \in \mathbb R}$ of \*-automorphisms determined on generators by

$$
\alpha_t\bigl(u(\xi)\bigr) \mspace{5mu} =\mspace{5mu}  u(\xi), \qquad \alpha_t(\mu_\mathfrak{a}) \mspace{5mu} =\mspace{5mu}  (N\mathfrak{a})^{it}\mspace{3mu}  \mu_\mathfrak{a}.
$$

That this prescription extends to a strongly continuous one-parameter \*-automorphism group of $B_K$ is the content of:

**Proposition 2.1** ([BC95, §3, Thm. 24]). The family $\{\alpha_t\}$ defines a strongly continuous one-parameter group of \*-automorphisms of $B_K$.

The time evolution is parameter-free: the only datum entering its definition is the absolute norm $N\mathfrak a$ of integral ideals, which is intrinsic to the arithmetic of $\mathfrak o_K$. Conjugation by $\alpha_t$ scales the isometries by the imaginary power of the norm and fixes the roots-of-unity subalgebra pointwise.

### §2.3. The canonical KMS state $\omega_1$

Recall that a state $\omega$ on a C\*-algebra $A$ with one-parameter automorphism group $\{\alpha_t\}$ satisfies the **KMS condition at inverse temperature $\beta$**, written $\mathrm{KMS}\_\beta$, if for every $a, b \in A$ there exists a bounded holomorphic function $F_{a,b}$ on the strip $\{ z \in \mathbb C : 0 < \mathrm{Im}\,z < \beta \}$, continuous on the closure, satisfying

$$
F_{a,b}(t) \mspace{5mu} =\mspace{5mu}  \omega\bigl(a\mspace{3mu}  \alpha_t(b)\bigr), \qquad F_{a,b}(t + i\beta) \mspace{5mu} =\mspace{5mu}  \omega\bigl(\alpha_t(b)\mspace{3mu}  a\bigr).
$$

The set of $\mathrm{KMS}\_\beta$ states for $(B_K, \alpha_t)$ has been completely classified:

**Proposition 2.2** ([BC95, Thm. 25; LLN09]). For the Bost–Connes system $(B_K, \alpha_t)$ with $K = \mathbb Q(i)$:
1. For each $\beta > 1$, the extremal $\mathrm{KMS}\_\beta$ states are in bijection with the characters of $\mathrm{Gal}(K^{\mathrm{ab}}/K)$.
2. At the critical value $\beta = 1$, there is a unique extremal $\mathrm{KMS}\_1$ state $\omega_1$, given explicitly on generators by

$$
\omega_1\bigl(u(\xi)\mspace{3mu} \mu_\mathfrak{a}^\ast \mu_\mathfrak{b}\bigr) \mspace{5mu} =\mspace{5mu} 
\begin{cases}
(N\mathfrak{a})^{-1}\mspace{3mu} \omega_1\bigl(u(\xi)\bigr), & \mathfrak{a} = \mathfrak{b}, \\
0, & \mathfrak{a} \neq \mathfrak{b},
\end{cases}
\qquad
\omega_1\bigl(u(\xi)\bigr) \mspace{5mu} =\mspace{5mu}  \frac{\mu_K(\mathfrak{q})}{\varphi_K(\mathfrak{q})},
$$

where, for $\xi \in K/\mathfrak o_K$, the ideal $\mathfrak q = \mathfrak q(\xi) \subseteq \mathfrak o_K$ is the denominator ideal of $\xi$ — the unique integral ideal such that $\xi \in \mathfrak q^{-1}/\mathfrak o_K$ with $\mathfrak q$ of minimal norm — and $\mu_K$, $\varphi_K$ denote the Möbius function and Euler totient function on the ideals of $\mathfrak o_K$, respectively.

The formula is the BC95 form of the critical $\mathrm{KMS}\_1$ state ([BC95, §3, Thm. 25 + eq. (35)]) adapted to the imaginary-quadratic case $K = \mathbb Q(i)$ ([CMR05]; [CM08, Ch. III, §3.4]; [LLN09]). The Möbius/totient combination is the natural expression of the critical state: the Dedekind zeta function $\zeta_K(s)$ has a simple pole at $s = 1$ — the residue at $s = 1$ is the structural witness of the phase transition itself — so the explicit form at $\beta = 1$ cannot be written as a partition-function ratio $\zeta_K(\beta)^{-1}\,\sum_\mathfrak c (\dots)$ as it can for $\beta > 1$. The closed Möbius form above is the BC95-original limit of the partition-function expression as $\beta \to 1^+$, and is the form one carries forward into the KMS-uniqueness argument [LLN09].

The phase transition at $\beta = 1$ thus selects a unique distinguished state; this state is the focus of the present work. The faithfulness of $\omega_1$ — needed for the GNS construction in §3 to yield an injective representation — is part of [BC95, §3, eq. (15)]:

**Proposition 2.3** ([BC95, §3, eq. (15)]). The state $\omega_1$ is faithful on $B_K$.

### §2.4. ITPFI factorization of $\omega_1$

The structural fact underlying both the type $\mathrm{III}\_1$ classification (§3) and the modular operator's product form (§4) is the **infinite tensor product** factorization of $\omega_1$ over the prime ideals of $\mathfrak o_K$.

For each prime ideal $\mathfrak p \subset \mathfrak o_K$, the local component of $B_K$ at $\mathfrak p$ is the C\*-algebra $B_{K,\mathfrak p}$ generated by the isometries $\mu_{\mathfrak p^k}$, $k \geq 0$, together with the local roots-of-unity unitaries; the GNS representation of $\omega_1|\_{B_{K,\mathfrak p}}$ realizes $B_{K,\mathfrak p}$ on $\ell^2(\mathbb N)$ as a type $\mathrm I_\infty$ factor, with the local state corresponding to the geometric weight

$$
\rho_\mathfrak{p}(n) \mspace{5mu} =\mspace{5mu}  (1 - (N\mathfrak{p})^{-1})\mspace{3mu}  (N\mathfrak{p})^{-n}, \qquad n \geq 0.
$$

The local factor is a state of Powers type [Pow67] on $B(\ell^2(\mathbb N))$, with eigenvalue list $\{(1 - (N\mathfrak p)^{-1})(N\mathfrak p)^{-n}\}\_{n \geq 0}$.

The product structure assembles these local pieces:

**Theorem 2.4** (ITPFI factorization; [BC95, Prop. 33; CM08, Ch. III, Thm. 3.32]). The canonical $\mathrm{KMS}\_1$ state $\omega_1$ admits an infinite tensor product factorization

$$
\widetilde{\omega}_1 \mspace{5mu} =\mspace{5mu}  \bigotimes_{\mathfrak{p}}\mspace{3mu}  {\widetilde{\omega}}_1^{(\mathfrak{p})}
$$

over the prime ideals of $\mathfrak o_K$, where each local state ${\widetilde\omega}\_1^{(\mathfrak p)}$ has the eigenvalue list $\rho_\mathfrak p$ above. The von Neumann algebra generated by the GNS representation of $\omega_1$ is the ITPFI infinite tensor product of the local Powers factors at $\mathfrak p$.

The Araki–Woods classification [AW68] applied to this ITPFI factor identifies it as a type $\mathrm{III}\_1$ factor in Connes' classification [Con73]; uniqueness within the injective class is [Haa87]. We make this identification explicit in §3.

The Lean formalization of Theorem 2.4 (axiom `itpfi_factorization`, §8.2 item 5) encodes the *non-traciality* of $\omega_1$ — the operational, sound, expressible core of the ITPFI factorization in the absence of Mathlib infrastructure for prime-indexed infinite tensor products. The full prime-indexed factorization $\widetilde\omega_1 = \bigotimes_\mathfrak p\, {\widetilde\omega}\_1^{(\mathfrak p)}$ rests on the external citations [BC95, Prop. 33; CM08, Ch. III, Thm. 3.32], not on machine verification in Lean; see §8.2 item 5.

A direct consequence of Theorem 2.4 is that the modular operator $\Delta$ of $\omega_1$ inherits a product structure from the local modular operators $\Delta_\mathfrak p$ of the local Powers states. The local modular operators are well known: on $B(\ell^2(\mathbb N))$ equipped with the Powers state of eigenvalue list $\{\lambda_n\}$, the modular operator is the diagonal operator with entries $\lambda_n/\lambda_m$ on the matrix unit $e_{nm}$. The infinite tensor product of these local modular operators — which, for unbounded operators, requires careful treatment beyond the bare ITPFI factorization of Theorem 2.4 — is the structural input to the modular flow analysis; the precise form is given in §4 (Proposition 4.3).

---

## §3. GNS construction and the type $\mathrm{III}\_1$ identification

We now construct the GNS triple $(H_R, \pi_{\omega_1}, \Omega_1)$ of $(B_K, \omega_1)$ explicitly and prove Theorem A. The construction is standard; we lay it out in the form needed for the formalization in §8, where the inner-product structure on the GNS quotient appears as two named axioms (Hypotheses 8.1–8.2) of the type that would discharge automatically with a more developed normed-quotient theory in Mathlib.

### §3.1. The null ideal and the GNS pre-Hilbert space

For any state $\omega$ on a C\*-algebra $A$, the **null ideal** is

$$
I_\omega \mspace{5mu} :=\mspace{5mu}  \lbrace\mspace{3mu}  a \in A : \omega(a^\ast a) = 0 \mspace{3mu} \rbrace.
$$

**Lemma 3.1.** $I_{\omega_1}$ is a closed left ideal of $B_K$.

*Proof.* Closedness follows from continuity of $\omega_1$. For the left-ideal property, use the operator inequality $a^\ast b^\ast b a \leq \|b\|^2\, a^\ast a$ in the C\*-algebra $B_K$: applying $\omega_1$ (which is positive on $B_K$, hence preserves the order $\leq$ on self-adjoint elements) gives

$$
\omega_1\bigl((ba)^\ast(ba)\bigr) \mspace{5mu} =\mspace{5mu}  \omega_1\bigl(a^\ast\mspace{3mu} b^\ast b\mspace{3mu}  a\bigr) \mspace{5mu} \leq\mspace{5mu}  \|b\|^2\mspace{3mu} \omega_1\bigl(a^\ast a\bigr).
$$

If $a \in I_{\omega_1}$, the right-hand side is $0$, so $\omega_1((ba)^\ast(ba)) = 0$, i.e., $ba \in I_{\omega_1}$. $\square$

By faithfulness of $\omega_1$ (Proposition 2.3), $I_{\omega_1} = \{0\}$; nevertheless we retain the quotient notation $B_K / I_{\omega_1}$ throughout because the construction proceeds identically without the faithfulness assumption, and in the Lean formalization (§8) the quotient form is the structurally natural object. We write $[a]$ for the equivalence class of $a \in B_K$ in $B_K / I_{\omega_1}$.

The sesquilinear form

$$
\bigl\langle [a],\mspace{3mu}  [b] \bigr\rangle \mspace{5mu} :=\mspace{5mu}  \omega_1(a^\ast b)
$$

is well-defined on the quotient: if $[a] = [a']$ and $[b] = [b']$ then $a - a', b - b' \in I_{\omega_1}$, and Cauchy–Schwarz forces $\omega_1\bigl((a-a')^\ast b\bigr) = \omega_1\bigl(a'^\ast(b - b')\bigr) = 0$. The form is conjugate-linear in the first argument, linear in the second, hermitian by $\omega_1(a^\ast b) = \overline{\omega_1(b^\ast a)}$, and positive: $\langle [a], [a]\rangle = \omega_1(a^\ast a) \geq 0$, with equality iff $a \in I_{\omega_1}$, i.e., $[a] = 0$.

The quotient $B_K / I_{\omega_1}$ thus carries a positive-definite inner product. Its completion

$$
H_R \mspace{5mu} :=\mspace{5mu}  \overline{B_K / I_{\omega_1}}^{\mspace{3mu} \|\cdot\|}
$$

in the corresponding norm is a Hilbert space. We denote by $[\,\cdot\,]$ both the quotient map $B_K \to B_K/I_{\omega_1}$ and its continuous extension into $H_R$; the cyclic vector is $\Omega_1 := [1]$.

### §3.2. The GNS representation

Left multiplication on $B_K$ descends to a representation on $H_R$:

**Proposition 3.2** ([BR87, §2.3.3]; [Tak03, Ch. III, §2]). The map $\pi_{\omega_1} : B_K \to B(H_R)$ defined on the dense subspace by $\pi_{\omega_1}(a)\,[b] := [ab]$ extends to a faithful \*-representation of $B_K$ on $H_R$. The vector $\Omega_1 = [1]$ is cyclic for $\pi_{\omega_1}(B_K)$: $\overline{\pi_{\omega_1}(B_K)\,\Omega_1} = H_R$.

The state $\omega_1$ is recovered as the vector state of $\Omega_1$:

$$
\omega_1(a) \mspace{5mu} =\mspace{5mu}  \bigl\langle \Omega_1,\mspace{3mu}  \pi_{\omega_1}(a)\mspace{3mu}  \Omega_1 \bigr\rangle \qquad (a \in B_K).
$$

We henceforth write $M := \pi_{\omega_1}(B_K)''$ for the strong-operator closure of $\pi_{\omega_1}(B_K)$ in $B(H_R)$. By Proposition 3.2, $\Omega_1$ is cyclic for $M$; it is also separating (i.e., $T \Omega_1 = 0 \implies T = 0$ for $T \in M$) by faithfulness of $\omega_1$ together with the standard argument [BR87, Prop. 2.5.3]; [Tak03, Ch. VI, Thm. 1.4]. The pair $(M, \Omega_1)$ thus stands in standard form, and Tomita–Takesaki theory applies (§4).

### §3.3. The type $\mathrm{III}\_1$ identification

The von Neumann algebra $M$ inherits the product structure of the ITPFI factorization in Theorem 2.4. For each prime ideal $\mathfrak p \subset \mathfrak o_K$, let $M_\mathfrak p \subset B(\ell^2(\mathbb N))$ denote the type $\mathrm I_\infty$ factor generated by the GNS representation of $\omega_1|\_{B_{K,\mathfrak p}}$.

**Theorem A** (GNS triple and type $\mathrm{III}\_1$ identification). The Hilbert space $H_R$ is canonically realized as the completion of $B_K / I_{\omega_1}$ under the inner product $\langle [a], [b] \rangle := \omega_1(a^\ast b)$. The von Neumann algebra $M = \pi_{\omega_1}(B_K)''$ is the unique injective type $\mathrm{III}\_1$ factor.

*Proof.* The Hilbert-space identification is the content of §3.1. For the factor classification, Theorem 2.4 gives an isomorphism

$$
M \mspace{5mu} \cong\mspace{5mu}  \bigotimes_\mathfrak{p}\mspace{3mu}  M_\mathfrak{p}
$$

of the infinite-tensor-product type (the von Neumann ITPFI of the local Powers factors). Each $M_\mathfrak p$ is a type $\mathrm I_\infty$ factor with state of eigenvalue list $\rho_\mathfrak p$. The **asymptotic ratio set** of an ITPFI factor (Araki–Woods invariant) [AW68, §4] is the set of accumulation points of finite products of ratios $\rho_\mathfrak p(n)/\rho_\mathfrak p(m)$ as $\mathfrak p, n, m$ vary.

For the present ITPFI, the ratios $\rho_\mathfrak p(n)/\rho_\mathfrak p(m) = (N\mathfrak p)^{-(n-m)}$ take values in $\{(N\mathfrak p)^k : k \in \mathbb Z\}$. For $K = \mathbb Q(i)$ the norms $N\mathfrak p$ of the prime ideals of $\mathfrak o_K = \mathbb Z[i]$ take the following values, governed by the splitting behavior of rational primes in $\mathbb Z[i]$: $N\mathfrak p = 2$ for the unique ramified prime above $2$; $N\mathfrak p = p$ for the two split primes above each rational prime $p \equiv 1 \pmod 4$; and $N\mathfrak p = p^2$ for the unique inert prime above each rational prime $p \equiv 3 \pmod 4$. (In particular, $3, 7, 11, \ldots$ are *not* norms of prime ideals of $\mathfrak o_K$; the norm set is $\{2, 5, 9, 13, 17, 29, \ldots\}$.) The multiplicative subgroup of $(0, \infty)$ generated by $\{N\mathfrak p\}$ contains $\{2^j \cdot 5^k : j, k \in \mathbb Z\}$; since $\log 2 / \log 5$ is irrational, this subgroup is dense in $(0, \infty)$ by Weyl equidistribution. Hence the asymptotic ratio set of the present ITPFI is $[0, \infty]$, which is the Araki–Woods condition for the **type $\mathrm{III}\_1$ factor** [AW68, Thm. 4.4; BC95, Prop. 33].

Injectivity of $M$ follows from the ITPFI property itself: ITPFI factors are hyperfinite, and hyperfinite factors are injective by [Con76]. The uniqueness up to isomorphism of the injective type $\mathrm{III}\_1$ factor [Haa87] completes the identification. $\square$

The factor $M$ thus belongs to the class identified in operator algebras as the most structurally rigid of the type III factors; the modular theory developed in §4 inherits this rigidity, and in particular the modular operator $\Delta$ has spectrum $[0, \infty)$.

---

## §4. The modular pair $(\Delta, J)$ via polar decomposition

Standard form $(M, \Omega_1)$ in hand (§3), we construct the modular operator $\Delta$ and modular conjugation $J$ explicitly. The route is the original one of Tomita and Takesaki: form the antilinear involution $S$ on the dense subspace $\pi(B_K)\Omega_1$, take its closure $\bar S$, and read off $(\Delta, J)$ from the polar decomposition $\bar S = J\,\Delta^{1/2}$. The construction is in the form expected by the operator-algebras literature [Tak03, Ch. VI; BR87, §2.5.3]; we record it here in the precise version that the formalization in §8 mirrors.

### §4.1. The Tomita involution $S$

Define the map $S$ on the dense subspace $D_0 := \pi_{\omega_1}(B_K)\,\Omega_1 \subset H_R$ by

$$
S\bigl(\pi(a)\mspace{3mu} \Omega_1\bigr) \mspace{5mu} :=\mspace{5mu}  \pi(a^\ast)\mspace{3mu} \Omega_1 \qquad (a \in B_K).
$$

The map is well-defined: if $\pi(a)\Omega_1 = \pi(a')\Omega_1$ then $\pi(a-a')\Omega_1 = 0$, which by separatingness of $\Omega_1$ (Proposition 3.2 and §3.2) forces $\pi(a-a') = 0$ in $M$, hence $\pi((a-a')^\ast) = 0$ and $S(\pi(a)\Omega_1) = S(\pi(a')\Omega_1)$. By the same argument, $S$ is independent of the choice of representative on $B_K / I_{\omega_1}$, so it descends to a well-defined map on $D_0$.

**Lemma 4.1.** The map $S : D_0 \to D_0$ is conjugate-linear, satisfies $S^2 = \mathrm{id}\_{D_0}$, and is densely defined on $H_R$.

*Proof.* Conjugate-linearity follows from $(\lambda a + b)^\ast = \bar\lambda\, a^\ast + b^\ast$ and the linearity of $\pi$: for $\lambda \in \mathbb C$ and $a, b \in B_K$,

$$
S\bigl(\lambda\mspace{3mu} \pi(a)\Omega_1 + \pi(b)\Omega_1\bigr) \mspace{5mu} =\mspace{5mu}  S\bigl(\pi(\lambda a + b)\mspace{3mu} \Omega_1\bigr) \mspace{5mu} =\mspace{5mu}  \pi((\lambda a + b)^\ast)\mspace{3mu} \Omega_1 \mspace{5mu} =\mspace{5mu}  \bar\lambda\mspace{3mu} \pi(a^\ast)\Omega_1 + \pi(b^\ast)\Omega_1.
$$

That $S^2 = \mathrm{id}$ on $D_0$ is immediate from $(a^\ast)^\ast = a$. Density of $D_0$ in $H_R$ is the cyclicity of $\Omega_1$ for $\pi(B_K)$ (Proposition 3.2). $\square$

A direct calculation against the ITPFI factorization (Theorem 2.4) shows that $S$ is *not* bounded: on a typical product vector $\Omega = \bigotimes_\mathfrak p v_\mathfrak p$ realized via Theorem 2.4, $S$ exchanges creation and annihilation factors locally and shifts the eigenvalues of the local modular operators by ratios $N\mathfrak p^{\pm 1}$, which, ranging over all prime ideals, are dense in $(0, \infty)$. Boundedness of $S$ would force the modular operator $\Delta = S^\ast \bar S$ defined below to have bounded spectrum, contradicting the type $\mathrm{III}\_1$ identification of $M$ (Theorem A; see [Tak03, Ch. VIII, §1] for the standard formulation of this contradiction). The unboundedness of $S$ is therefore structural and unavoidable.

### §4.2. Closability and the closure $\bar S$

**Proposition 4.2** ([Tak03, Ch. VI, Thm. 1.1]). The operator $S : D_0 \to D_0$ is closable, with closure $\bar S$ a densely defined closed conjugate-linear involution on a dense domain $D(\bar S) \supseteq D_0$ in $H_R$.

*Sketch.* Closability is shown by exhibiting a densely defined formal adjoint. Define the dual operator $F$ on the dense subspace $D_0' := M'\,\Omega_1$ (cyclic by the cyclic-implies-separating dual symmetry, since $\Omega_1$ is separating for $M$, hence cyclic for $M'$ [Tak03, Ch. VI, Prop. 1.4]) by

$$
F\bigl(\pi'(a')\mspace{3mu} \Omega_1\bigr) \mspace{5mu} :=\mspace{5mu}  \pi'(a'^\ast)\mspace{3mu} \Omega_1
$$

for $a' \in M'$, where $\pi'$ is the commutant representation. The same well-definedness, conjugate-linearity, and involution arguments apply, with $\Omega_1$ separating for $M'$. The inner-product identity

$$
\bigl\langle S\mspace{3mu} \xi,\mspace{3mu}  \eta \bigr\rangle \mspace{5mu} =\mspace{5mu}  \bigl\langle F\mspace{3mu} \eta,\mspace{3mu}  \xi \bigr\rangle \qquad (\xi \in D_0,\ \eta \in D_0')
$$

follows from a direct calculation using the KMS (twisted) cyclicity of $\omega_1$ on simple monomials — $\omega_1$ is non-tracial (the load-bearing content of Theorem A), so the cyclicity at play is the $\sigma_{i\beta}$-twisted KMS identity $\omega_1(ab) = \omega_1(b\,\sigma_{i\beta}(a))$ of [BR97, §5.3], not a literal trace cyclicity — and extends by continuity. The existence of a densely defined formal adjoint implies closability of $S$ [Tak03, Ch. VI, Lem. 1.5], with closure $\bar S$. The closure is again a conjugate-linear involution on its domain. $\square$

We retain the notation $S$ for the unbounded operator with the understanding that henceforth $S = \bar S$ is the closed extension; $D_0 \subset D(S)$ is a core.

### §4.3. The polar decomposition

The polar decomposition for unbounded closed antilinear operators is the analogue of the standard linear polar decomposition $T = U |T|$ with $U$ a partial isometry. Antilinearity replaces $U$ by an antilinear partial isometry; the modulus $|S| = (S^\ast S)^{1/2}$ remains a positive self-adjoint *linear* operator (the composition of two antilinear maps is linear). For the Tomita involution this gives the modular operator and modular conjugation directly.

**Theorem B** (modular operator and modular conjugation; [Tak03, Ch. VI, Thm. 1.4; BR87, §2.5.3]). The closure $\bar S = S$ admits a polar decomposition

$$
S \mspace{5mu} =\mspace{5mu}  J\mspace{3mu} \Delta^{1/2}
$$

where $\Delta := S^\ast S$ is a positive self-adjoint linear operator (the modular operator ) and $J$ is an antiunitary involution (the modular conjugation ). The pair $(\Delta, J)$ satisfies

$$
J^2 \mspace{5mu} =\mspace{5mu}  I, \qquad J^\ast \mspace{5mu} =\mspace{5mu}  J, \qquad J\mspace{3mu} \Delta\mspace{3mu} J \mspace{5mu} =\mspace{5mu}  \Delta^{-1}.
$$

*Proof.* Form the positive linear operator $\Delta := S^\ast S$ on the domain $D(\Delta) = \{ \xi \in D(S) : S\xi \in D(S^\ast) \}$. Conjugate-linearity of $S$ together with the antilinear adjoint identity $\langle S\xi, \eta\rangle = \langle S^\ast\eta, \xi\rangle$ (Mathlib convention: inner product conjugate-linear in the first argument) gives the symmetry

$$
\bigl\langle \Delta\mspace{3mu} \xi,\mspace{3mu}  \eta \bigr\rangle \mspace{5mu} =\mspace{5mu}  \bigl\langle S^\ast S\mspace{3mu} \xi,\mspace{3mu}  \eta \bigr\rangle \mspace{5mu} =\mspace{5mu}  \bigl\langle S\mspace{3mu} \eta,\mspace{3mu}  S\mspace{3mu} \xi \bigr\rangle \mspace{5mu} =\mspace{5mu}  \overline{\bigl\langle S\mspace{3mu} \xi,\mspace{3mu}  S\mspace{3mu} \eta \bigr\rangle} \mspace{5mu} =\mspace{5mu}  \bigl\langle \xi,\mspace{3mu}  \Delta\mspace{3mu} \eta \bigr\rangle,
$$

so $\Delta$ is symmetric. Closedness of $S$ promotes $\Delta$ to self-adjoint via the standard argument [Tak03, Ch. VI, Lem. 1.6]. Positivity follows from $\langle \Delta \xi, \xi\rangle = \langle S\xi, S\xi\rangle = \|S\xi\|^2 \geq 0$.

The modulus $|S| := \Delta^{1/2}$ is defined by Mathlib's continuous functional calculus on the positive self-adjoint $\Delta$. On $\mathrm{range}(|S|) \subset H_R$, define the partial isometry

$$
J \mspace{5mu} :=\mspace{5mu}  S \circ |S|^{-1}
$$

and extend by $0$ on $(\mathrm{range}\,|S|)^\perp$. Since $S$ is densely defined and closed with $\ker S = \{0\}$ — the latter from $S^2 = \mathrm{id}$ on the core $D_0$ (which forces injectivity there, preserved under closure by separatingness of $\Omega_1$) — the positive self-adjoint modulus $|S|$ also has trivial kernel, so $\mathrm{range}\,|S|$ is dense in $H_R$ and $(\mathrm{range}\,|S|)^\perp = \{0\}$; hence $J$ is in fact defined on a dense subspace and extends to all of $H_R$ by continuity. The composition is conjugate-linear (composition of the linear $|S|^{-1}$ with the conjugate-linear $S$), and the polar identity $S = J\,\Delta^{1/2}$ holds by construction on $\mathrm{range}\,|S|$ and hence on $D(S)$ by closedness.

The properties $J^2 = I$ and $J^\ast = J$ follow from $S^2 = I$ on the dense domain: writing $S = J\Delta^{1/2}$ and applying twice,

$$
\xi \mspace{5mu} =\mspace{5mu}  S^2\mspace{3mu} \xi \mspace{5mu} =\mspace{5mu}  J\mspace{3mu} \Delta^{1/2}\mspace{3mu} J\mspace{3mu} \Delta^{1/2}\mspace{3mu} \xi \qquad (\xi \in D_0),
$$

together with $\Delta = S^\ast S = (J\Delta^{1/2})^\ast(J\Delta^{1/2}) = \Delta^{1/2}\,J^\ast J\,\Delta^{1/2}$. Uniqueness of polar decomposition combined with antiunitarity of $J$ on the range of $|S|$ gives $J^\ast J = I$ on $\overline{\mathrm{range}\,|S|} = H_R$, so $J$ is antiunitary. The intertwining $J\,\Delta\,J = \Delta^{-1}$ follows from the $S^2 = I$ identity together with the antilinear commutation relations [Tak03, Ch. VI, Thm. 1.4]. $\square$

### §4.4. Product structure on the ITPFI factorization

The ITPFI factorization of $\omega_1$ (Theorem 2.4) gives the modular operator a product structure inherited from the local modular operators $\Delta_\mathfrak p$ of the local Powers states.

**Proposition 4.3.** Let $\widetilde\omega_1 = \bigotimes_\mathfrak p\, {\widetilde\omega}\_1^{(\mathfrak p)}$ be the ITPFI factorization of Theorem 2.4. For each prime ideal $\mathfrak p$, let $S_\mathfrak p$, $\Delta_\mathfrak p$, $J_\mathfrak p$ denote the Tomita involution, modular operator, and modular conjugation of the local state ${\widetilde\omega}\_1^{(\mathfrak p)}$ on the type $\mathrm I_\infty$ factor $M_\mathfrak p \cong B(\ell^2(\mathbb N))$. Then on the dense subspace of finite simple tensors in $H_R$,

$$
S \mspace{5mu} =\mspace{5mu}  \bigotimes_\mathfrak{p}\mspace{3mu}  S_\mathfrak{p}, \qquad \Delta \mspace{5mu} =\mspace{5mu}  \bigotimes_\mathfrak{p}\mspace{3mu}  \Delta_\mathfrak{p}, \qquad J \mspace{5mu} =\mspace{5mu}  \bigotimes_\mathfrak{p}\mspace{3mu}  J_\mathfrak{p},
$$

*as infinite tensor products of unbounded operators, understood in the standard ITPFI sense [AW68, §3].*

*Sketch.* The local modular operators are explicitly computable: on $B(\ell^2(\mathbb N))$ with the Powers state of eigenvalue list $\rho_\mathfrak p(n) = (1-N\mathfrak p^{-1})(N\mathfrak p)^{-n}$, the local Tomita involution $S_\mathfrak p$ acts on the matrix unit $e_{nm}\Omega_\mathfrak p$ by $e_{nm}\Omega_\mathfrak p \mapsto e_{mn}\Omega_\mathfrak p$, with local modulus $\Delta_\mathfrak p\,e_{nm}\Omega_\mathfrak p = (N\mathfrak p)^{-(n-m)}\,e_{nm}\Omega_\mathfrak p$ and local conjugation $J_\mathfrak p\,e_{nm}\Omega_\mathfrak p = (N\mathfrak p)^{-(n-m)/2}\,e_{mn}\Omega_\mathfrak p$ (the standard local computation; see [BR97, §5.3] and [Pow67, §3] for the Powers-state case, with the semigroup-crossed-product picture underlying the local computations following Cuntz–Echterhoff–Li [CEL13, Thm. 3.5]). The product structure on simple tensors is then forced by Theorem 2.4, since each operator acts factor-by-factor on monomials of the form $u(\xi)\,\mu_\mathfrak a^\ast\mu_\mathfrak b$ with $\mathfrak a, \mathfrak b$ supported on finitely many prime ideals; the dense subspace of finite simple tensors is a core. $\square$

The product structure of Proposition 4.3 is the structural input used in §5 for the relationship between the modular automorphism group $\sigma_t$ and the arithmetic time evolution $\alpha_t$. The spectrum of $\Delta$ inherited from the product structure satisfies

$$
\mathrm{spec}(\Delta) \mspace{5mu} =\mspace{5mu}  \overline{\bigl\lbrace\mspace{3mu}  \prod_{\mathfrak{p} \in F}\mspace{3mu}  (N\mathfrak{p})^{k_\mathfrak{p}} \mspace{5mu} :\mspace{5mu}  F \text{ finite},\ k_\mathfrak{p} \in \mathbb{Z}\mspace{3mu} \bigr\rbrace} \mspace{5mu} =\mspace{5mu}  [0, \infty),
$$

where the closure step uses the density of $\{(N\mathfrak p)^k : k \in \mathbb Z,\ \mathfrak p\}$ in $(0, \infty)$, which is the Araki–Woods criterion for type $\mathrm{III}\_1$ ([AW68, Thm. 4.4] and §3 above). This recovers the type $\mathrm{III}\_1$ identification of Theorem A from the modular-theoretic side and closes the loop between the polar-decomposition construction and the factor classification.

---

## §5. The modular flow theorem $\sigma_t = \alpha_t$

The modular pair $(\Delta, J)$ from §4 is, by Tomita–Takesaki theory, intrinsic to the standard pair $(M, \Omega_1)$; the time evolution $\alpha_t$ is the arithmetic data of the Bost–Connes algebra. The content of Theorem C is that these two structurally distinct one-parameter groups coincide on the representation. The identification is unconditional: it is the consequence of Takesaki's KMS-uniqueness theorem [BR97, Thm. 5.3.10] applied to the faithful normal $\mathrm{KMS}\_1$ state $\omega_1$ on $M$, together with existence + uniqueness of the $\sigma$-weakly continuous extension of the time evolution from $\pi(B_K)$ to $M$.

### §5.1. The modular automorphism group and the transported time evolution

By Tomita–Takesaki theory ([Tak03, Ch. VI, Thm. 1.9; BR87, Thm. 2.5.14]) applied to the standard pair $(M, \Omega_1)$ of §3, the modular operator $\Delta$ of §4 generates a one-parameter group of $\ast$-automorphisms of $M$:

**Proposition 5.1** ([Tak03, Ch. VI, Thm. 1.9]). *The map*

$$
\sigma_t^{\omega_1}(x) \mspace{5mu} :=\mspace{5mu}  \Delta^{it}\mspace{3mu}  x\mspace{3mu}  \Delta^{-it} \qquad (x \in M,\ t \in \mathbb{R}),
$$

defines a $\sigma$-weakly continuous one-parameter group of $\ast$-automorphisms of $M$. The state $\omega_1$ is a $\mathrm{KMS}\_1$ state for $\{\sigma_t^{\omega_1}\}$ in the sense of §2.3.

The modular automorphism group is intrinsic to the pair $(M, \omega_1)$: it does not depend on the choice of cyclic separating vector implementing $\omega_1$ on $M$, and is the *unique* $\sigma$-weakly continuous one-parameter $\ast$-automorphism group of $M$ for which the faithful normal state $\omega_1$ is a $\mathrm{KMS}\_1$ state ([BR97, Thm. 5.3.10] — Takesaki's KMS-uniqueness theorem). We adopt Connes' sign convention $\sigma_t = \mathrm{Ad}(\Delta^{it})$ throughout (as declared in §1.4).

We next construct the second automorphism group of $M$ entering the identification. By Proposition 2.1, the time evolution $\alpha_t$ yields a one-parameter group of $\ast$-automorphisms of $B_K$, and by Proposition 2.2(2), $\omega_1$ is a $\mathrm{KMS}\_1$ state for $\{\alpha_t\}$. Since $\omega_1$ is invariant under $\alpha_t$ (automatic for KMS states), the GNS construction implements $\alpha_t$ by a strongly continuous one-parameter unitary group $U_t$ on $H_R$, defined on the dense subspace by $U_t\,\pi(a)\Omega_1 := \pi(\alpha_t(a))\Omega_1$ (well-defined and isometric by $\omega_1 \circ \alpha_t = \omega_1$). Conjugation $\widetilde\alpha_t := \mathrm{Ad}(U_t)$ is $\sigma$-weakly continuous and satisfies $\widetilde\alpha_t(\pi(a)) = \pi(\alpha_t(a))$, hence maps $\pi(B_K)$ into itself; by $\sigma$-weak continuity, $\widetilde\alpha_t$ preserves the bicommutant $M = \pi(B_K)''$. Restricting to $M$:

**Proposition 5.2** ([BR87, Prop. 2.5.22]; [BR97, Cor. 5.3.4]). The map $\widetilde\alpha_t := \mathrm{Ad}(U_t)|\_M$ is a $\sigma$-weakly continuous one-parameter group of normal $\ast$-automorphisms of $M$, uniquely determined by the extension prescription $\widetilde\alpha_t(\pi(a)) = \pi(\alpha_t(a))$ ($a \in B_K$); the faithful normal state $\omega_1$ is a $\mathrm{KMS}\_1$ state for $\{\widetilde\alpha_t\}$.

The proposition packages three sub-claims: (a) existence of the $\sigma$-weakly continuous extension $\widetilde\alpha_t$ to $M$, via GNS-covariance + KMS-invariance of $\omega_1$ ([BR87, Prop. 2.5.22] applied to the standard form ${(M, \Omega_1)}$); (b) uniqueness, by $\sigma$-weak density of $\pi(B_K)$ in $M$; (c) transfer of the $\mathrm{KMS}\_1$ condition from $\pi(B_K)$ to $M$, via [BR97, Cor. 5.3.4] using normality of $\omega_1$ and $\sigma$-weak density of $\pi(B_K)$ in $M$.

We thus have, on $M$, two $\sigma$-weakly continuous one-parameter $\ast$-automorphism groups — $\sigma_t^{\omega_1}$ and $\widetilde\alpha_t$ — for both of which the faithful normal state $\omega_1$ is a $\mathrm{KMS}\_1$ state.

### §5.2. Proof of Theorem C

**Theorem C** (modular flow; from §1.3). For all $t \in \mathbb R$ and all $a \in B_K$,

$$
\sigma_t^{\omega_1}\bigl(\pi(a)\bigr) \mspace{5mu} =\mspace{5mu}  \pi\bigl(\alpha_t(a)\bigr).
$$

*Proof.* By Proposition 5.1, $\{\sigma_t^{\omega_1}\}$ is a $\sigma$-weakly continuous one-parameter $\ast$-automorphism group of $M$ for which $\omega_1$ is a $\mathrm{KMS}\_1$ state. By Proposition 5.2, $\{\widetilde\alpha_t\}$ is also a $\sigma$-weakly continuous one-parameter $\ast$-automorphism group of $M$ for which $\omega_1$ is a $\mathrm{KMS}\_1$ state. Since $\omega_1$ is faithful (Ω₁ separating for $M$, §3.2) and normal (vector state of Ω₁), Takesaki's KMS-uniqueness theorem [BR97, Thm. 5.3.10] applies: the modular automorphism group is the *unique* $\sigma$-weakly continuous one-parameter $\ast$-automorphism group of $M$ for which $\omega_1$ is a $\mathrm{KMS}\_1$ state. Therefore

$$
\sigma_t^{\omega_1} \mspace{5mu} =\mspace{5mu}  \widetilde{\alpha}_t \qquad (t \in \mathbb{R})
$$

as $\ast$-automorphism groups of $M$. Evaluating at $\pi(a)$ and using $\widetilde\alpha_t(\pi(a)) = \pi(\alpha_t(a))$ from Proposition 5.2 gives the claim. $\square$

The identification is unconditional: the input to Takesaki's KMS-uniqueness theorem is faithfulness + normality of $\omega_1$ on $M$ together with the $\mathrm{KMS}\_1$ property for both candidate groups — all of which we have. The argument does not require the prime-by-prime structural form $\Delta^{it} = \bigotimes_\mathfrak p \Delta_\mathfrak p^{it}$ of the modular operator: that explicit form is needed for the *computation* of $\Delta$ (Theorem B), the type $\mathrm{III}\_1$ identification via the asymptotic ratio set (Theorem A), and the *spectral data* $D_\infty = \log \Delta$ (Theorem E), but not for the identification $\sigma_t = \alpha_t$ itself, which is the soft KMS-uniqueness consequence.

### §5.3. Remark on the prime-local computation route

An alternative, constructive route to Theorem C proceeds via the explicit prime-local product form of $\Delta$. By Proposition 4.3, $\Delta = \bigotimes_\mathfrak p \Delta_\mathfrak p$ on simple tensors; the exponential form $\Delta^{it} = \bigotimes_\mathfrak p \Delta_\mathfrak p^{it}$ together with the prime-by-prime identification $\Delta_\mathfrak p^{it}\, \pi(\mu_\mathfrak p^k)\, \Delta_\mathfrak p^{-it} = (N\mathfrak p)^{itk}\, \pi(\mu_\mathfrak p^k)$ yield $\sigma_t = \alpha_t$ by direct calculation. This route requires the full apparatus of analytic vectors for the infinite tensor product of unbounded operators ([CM08, Ch. III, §3.4]; [BR97, §5.3]; [LLN09]) and is strictly stronger than what Theorem C requires — it both identifies $\sigma_t$ with $\alpha_t$ and produces the explicit spectral data $D_\infty$ on the Hecke basis (used in §7 in a manner that does not depend on Theorem C). We do not pursue the prime-local route here; the soft KMS-uniqueness proof above is the standalone route to Theorem C.

The Lean encoding of Theorem C carries a substrate hypothesis `hSubstrate_iii` in module L6 that mirrors the KMS-uniqueness step of the proof above; the hypothesis remains undischarged at the Lean level because Mathlib at the pinned SHA does not host a $W^\ast$-KMS-uniqueness theorem. The discharge is a formalization target — recorded as Mathlib Integration Target 9.1 — rather than an open mathematical question.

---

## §6. Galois action and modular conjugation

The Galois group $\mathrm{Gal}(K/\mathbb Q)$ acts naturally on the Bost–Connes algebra $B_K$ by $\ast$-automorphisms; for $K = \mathbb Q(i)$, this action is generated by the complex-conjugation automorphism $\tau : i \mapsto -i$ of $K$. We record here the compatibility of this Galois action with the time evolution $\alpha_t$ of §2.2 and with the modular conjugation $J$ of §4, in the precise form needed for the formalization in §8. The content of this section is Theorem D.

### §6.1. The Galois action on $B_K$

The Galois group $G := \mathrm{Gal}(K/\mathbb Q) \cong \mathbb Z/2\mathbb Z$ for $K = \mathbb Q(i)$ acts on $\mathfrak o_K = \mathbb Z[i]$ by complex conjugation $\tau(a + bi) := a - bi$. This action induces an action on the integral-ideal semigroup $I_K^+$ (sending $\mathfrak a$ to its Galois-conjugate ideal ${\tau(\mathfrak a)}$) and on the abelian group $K/\mathfrak o_K$ underlying the roots-of-unity generators.

**Proposition 6.1** ([BC95, §3; CM08, Ch. III, §3.4]). The Galois action of $G$ on the arithmetic data extends to an action by $\ast$-automorphisms of $B_K$ on the generators of §2.1:

$$
\widehat{\tau}\bigl(u(\xi)\bigr) \mspace{5mu} :=\mspace{5mu}  u\bigl(\tau(\xi)\bigr), \qquad \widehat{\tau}(\mu_\mathfrak{a}) \mspace{5mu} :=\mspace{5mu}  \mu_{\tau(\mathfrak{a})}, \qquad (\xi \in K/\mathfrak{o}_K,\ \mathfrak{a} \in I_K^+).
$$

The extension to a $\ast$-automorphism of $B_K$ is uniquely determined by these formulas on generators and the Hecke relations; the assignment $\tau \mapsto \widehat\tau$ is a group homomorphism $G \to \mathrm{Aut}\_\ast(B_K)$.

The Galois action on the absolute norm is trivial — $N(\tau(\mathfrak a)) = N\mathfrak a$ for every $\mathfrak a \in I_K^+$, since complex conjugation preserves the underlying $\mathbb Z$-module structure of $\mathfrak o_K/\mathfrak a$. This is the structural input for the commutativity of the Galois action with the time evolution.

**Proposition 6.2.** The Galois action commutes with the time evolution: for all $g \in G$, $t \in \mathbb R$, and $a \in B_K$,

$$
\widehat{g}\bigl(\alpha_t(a)\bigr) \mspace{5mu} =\mspace{5mu}  \alpha_t\bigl(\widehat{g}(a)\bigr).
$$

*Proof.* It suffices to check the identity on the generators of $B_K$, since both sides are $\ast$-automorphisms. On the roots-of-unity generators $u(\xi)$, both $\widehat g$ and $\alpha_t$ act on $u(\xi)$ in ways that commute by direct calculation ($\alpha_t$ fixes $u(\xi)$ pointwise; $\widehat g$ acts by ${u(\xi) \mapsto u(g(\xi))}$). On the isometries $\mu_\mathfrak a$,

$$
\widehat{g}(\alpha_t(\mu_\mathfrak{a})) \mspace{5mu} =\mspace{5mu}  \widehat{g}\bigl((N\mathfrak{a})^{it}\mspace{3mu} \mu_\mathfrak{a}\bigr) \mspace{5mu} =\mspace{5mu}  (N\mathfrak{a})^{it}\mspace{3mu} \mu_{g(\mathfrak{a})} \mspace{5mu} =\mspace{5mu}  (N(g(\mathfrak{a})))^{it}\mspace{3mu} \mu_{g(\mathfrak{a})} \mspace{5mu} =\mspace{5mu}  \alpha_t(\mu_{g(\mathfrak{a})}) \mspace{5mu} =\mspace{5mu}  \alpha_t(\widehat{g}(\mu_\mathfrak{a})),
$$

where the third equality uses Galois-invariance of the absolute norm. $\square$

### §6.2. Compatibility with the modular conjugation

The Galois action lifts to $H_R$ via the GNS construction. Since the Galois action preserves $\omega_1$ — a consequence of the explicit formula in Proposition 2.2(2), in which all dependence on $\xi$ enters through $e^{2\pi i\langle \xi, \mathfrak c\rangle}$ and complex conjugation on $\xi$ corresponds to complex conjugation on the character pairing — the action of $g \in G$ on $\pi(a)\Omega_1$ defined by $U_g \pi(a)\Omega_1 := \pi(\widehat g(a))\Omega_1$ is well-defined on the dense subspace $D_0$ and extends by continuity to a unitary $U_g$ on $H_R$, with the cocycle relation $U_{g_1 g_2} = U_{g_1} U_{g_2}$ and $U_e = I$.

The compatibility with the modular conjugation $J$ of §4 takes the following form. Since $J$ implements the antilinear involution sending $\pi(a)\Omega_1$ to $\pi(a^\ast)\Omega_1$ (up to the $\Delta^{1/2}$ factor in the polar decomposition) and $\widehat g$ is a $\ast$-automorphism, the two intertwine on the dense subspace.

**Theorem D** (Galois compatibility; from §1.3). Let $G = \mathrm{Gal}(K/\mathbb Q)$ acting on $B_K$ via Proposition 6.1, lifted to a unitary representation $U : G \to \mathcal U(H_R)$ via the GNS construction. Then for every $g \in G$:

*(i) The lifted Galois action commutes with the time evolution on the representation:*

$$
U_g\mspace{3mu} \pi(\alpha_t(a))\mspace{3mu} U_g^\ast \mspace{5mu} =\mspace{5mu}  \pi(\alpha_t(\widehat{g}(a))) \qquad (a \in B_K,\ t \in \mathbb{R}).
$$

*(ii) The lifted Galois action intertwines with the modular conjugation:*

$$
U_g\mspace{3mu} J\mspace{3mu} U_g^\ast \mspace{5mu} =\mspace{5mu}  J.
$$

*Proof.* Clause (i) is Proposition 6.2 transported through the representation: $U_g\,\pi(a)\,U_g^\ast = \pi(\widehat g(a))$ by construction of $U_g$, and the commutativity $\widehat g \circ \alpha_t = \alpha_t \circ \widehat g$ gives the claim.

Clause (ii) is the structural compatibility of the antilinear involution $S$ with the Galois action. On the dense subspace $D_0$,

$$
U_g\mspace{3mu} S\mspace{3mu} U_g^\ast\mspace{3mu} \pi(a)\Omega_1 \mspace{5mu} =\mspace{5mu}  U_g\mspace{3mu} S\mspace{3mu} \pi(\widehat{g}^{-1}(a))\Omega_1 \mspace{5mu} =\mspace{5mu}  U_g\mspace{3mu} \pi(\widehat{g}^{-1}(a)^\ast)\Omega_1 \mspace{5mu} =\mspace{5mu}  \pi\bigl(\widehat{g}(\widehat{g}^{-1}(a)^\ast)\bigr)\Omega_1 \mspace{5mu} =\mspace{5mu}  \pi(a^\ast)\Omega_1 \mspace{5mu} =\mspace{5mu}  S\mspace{3mu} \pi(a)\Omega_1,
$$

using $\widehat g(b^\ast) = \widehat g(b)^\ast$ ($\widehat g$ a $\ast$-automorphism). Hence $U_g\,S\,U_g^\ast = S$ on the dense core $D_0$, and the same identity holds for the closure $\bar S$. Since $S = J\,\Delta^{1/2}$ (Theorem B) and $U_g$ is unitary, $U_g\,J\,\Delta^{1/2}\,U_g^\ast = J\,\Delta^{1/2}$. Splitting the conjugated polar decomposition, the unitary $U_g\,\Delta^{1/2}\,U_g^\ast = (U_g\,\Delta\,U_g^\ast)^{1/2}$ is itself a positive self-adjoint operator and $U_g\,J\,U_g^\ast$ is antiunitary, so by uniqueness of polar decomposition,

$$
U_g\mspace{3mu} J\mspace{3mu} U_g^\ast \mspace{5mu} =\mspace{5mu}  J, \qquad U_g\mspace{3mu} \Delta\mspace{3mu} U_g^\ast \mspace{5mu} =\mspace{5mu}  \Delta. \qquad \square
$$

The Galois action thus preserves the modular structure intact: both the modular operator $\Delta$ and the modular conjugation $J$ commute with the unitaries $U_g$. The combinatorial content of (ii) — expressed in terms of the Hecke-basis action of $J$ — is that $J$ exchanges the two "ends" of the bilateral Hecke basis (the swap of the isometry indices in $u(\xi)\,\mu_\mathfrak a^\ast\mu_\mathfrak b$) in a Galois-equivariant manner, with the $\xi$-dependence transforming covariantly under $\tau$. We refer to [CM08, Ch. III, §3.4] for the explicit Hecke-basis form, which is not needed for the structural content of Theorem D.

---

## §7. Spectral realization data $D_\infty = \log \Delta$

We record the spectral realization data associated to the modular operator $\Delta$ of §4. The data consists of a distinguished self-adjoint operator on $H_R$, together with the structural witness that the operator generates the modular flow. The content of this section is Theorem E and is included primarily as a structural record for downstream use; the full spectral-arithmetic content (the precise spectrum of $D_\infty$ in relation to the absolute norms $\{N\mathfrak a\}$) is downstream substrate beyond the scope of the present construction.

### §7.1. The modular Hamiltonian

The modular operator $\Delta$ of §4 is a positive self-adjoint operator on $H_R$ with spectrum $[0, \infty)$ (§4.4). The continuous functional calculus applied to $\Delta$ on its positive spectrum yields a self-adjoint operator

$$
D_\infty \mspace{5mu} :=\mspace{5mu}  \log \Delta
$$

via $\mathrm{cfc}\,\log\,\Delta$ in the standard sense [Tak03, Ch. VIII, §1.2]. The operator $D_\infty$ is densely defined and self-adjoint, generating the modular flow $\Delta^{it} = e^{itD_\infty}$ on the spectral subspace where $\log$ is well-defined; on the kernel of $\Delta$, $D_\infty$ is undefined and the modular flow is trivial.

We adopt the sign convention $D_\infty = \log \Delta$ throughout (so that under the modular flow $\sigma_t = \mathrm{Ad}(\Delta^{it})$, the generator is $iD_\infty$). The opposite sign — $D_\infty := -\log \Delta = K_1$, the KMS Hamiltonian — also appears in the literature [BR97, §5.3.4]; we work with $D_\infty = \log \Delta$ here for consistency with the spectral-encoding convention in subsequent work (cf. [CCM25] for the parallel prolate-spheroidal construction with the same sign).

### §7.2. Theorem E

**Theorem E** (spectral realization data; from §1.3). The self-adjoint operator $D_\infty = \log \Delta$ on $H_R$ satisfies:

(i) $D_\infty$ is densely defined and self-adjoint, with

$$
\Delta^{it} \mspace{5mu} =\mspace{5mu}  e^{itD_\infty} \qquad (t \in \mathbb{R})
$$

on the spectral subspace where $\Delta$ is invertible (the orthogonal complement of $\ker \Delta$).

(ii) The spectrum of $D_\infty$ is the image of $\mathrm{spec}(\Delta) \setminus \{0\}$ under $\log$:

$$
\mathrm{spec}(D_\infty) \mspace{5mu} =\mspace{5mu}  \log\bigl(\mathrm{spec}(\Delta) \setminus \lbrace 0 \rbrace\bigr) \mspace{5mu} =\mspace{5mu}  \mathbb{R}.
$$

(iii) On the dense subspace of finite simple tensors of the ITPFI factorization (Proposition 4.3), $D_\infty$ is the diagonalized infinite sum

$$
D_\infty \mspace{5mu} =\mspace{5mu}  \sum_{\mathfrak{p}}\mspace{3mu}  \log \Delta_\mathfrak{p}
$$

with local generators $\log \Delta_\mathfrak p$ acting on $B(\ell^2(\mathbb N))$ as multiplication by $-(n-m)\log N\mathfrak p$ on the matrix unit $e_{nm}\Omega_\mathfrak p$.

*Proof.* Clause (i) is Mathlib's continuous functional calculus applied to the positive self-adjoint $\Delta$ together with the identity $e^{it\log x} = x^{it}$ for $x > 0$ in the calculus; the restriction to $(\ker \Delta)^\perp$ is the standard handling of the kernel of a positive operator under $\log$. Clause (ii) is the spectral mapping theorem $\mathrm{spec}(\log \Delta) = \log(\mathrm{spec}(\Delta))$, with $\mathrm{spec}(\Delta) \setminus \{0\} = (0, \infty)$ (from §4.4) mapping under $\log$ to all of $\mathbb R$.

Clause (iii) is the product structure of Proposition 4.3 transported through the logarithm. On a finite simple tensor $\xi = \bigotimes_\mathfrak p \xi_\mathfrak p$ supported on a finite subset $F$ of prime ideals, the local modular operators act with explicit eigenvalues $(N\mathfrak p)^{-(n_\mathfrak p - m_\mathfrak p)}$ on the matrix-unit decomposition $\xi_\mathfrak p = \sum c^{(\mathfrak p)}\_{n_\mathfrak p, m_\mathfrak p}\, e_{n_\mathfrak p, m_\mathfrak p}\Omega_\mathfrak p$. Applying $\log$ commutes with the product structure on simple tensors (since the local operators commute pairwise), and the resulting eigenvalue on each Hecke-basis component is $-(n_\mathfrak p - m_\mathfrak p)\log N\mathfrak p$, summed over $\mathfrak p \in F$. This identifies $D_\infty$ on the dense subspace of finite simple tensors as the diagonalized sum claimed. $\square$

The operator $D_\infty = \log \Delta$ thus encodes the arithmetic data $\{\log N\mathfrak a : \mathfrak a \in I_K^+\}$ in its spectral decomposition on the Hecke basis: the eigenvalue on a Hecke-basis element $\Omega_{\mathfrak a,\mathfrak b}$ is $\log N\mathfrak a - \log N\mathfrak b = \log(N\mathfrak a/N\mathfrak b)$, which, ranging over $\mathfrak a, \mathfrak b \in I_K^+$, takes values in the additive subgroup of $\mathbb R$ generated by $\{\log N\mathfrak p\}$. This subgroup is dense in $\mathbb R$ by the $\mathbb Q$-linear independence of $\{\log p : p \text{ rational prime}\}$ together with the factorization of $N\mathfrak p$ as a rational prime power; density is what made the spectrum of $\Delta$ all of $[0, \infty)$ in §4.4 (Araki–Woods type $\mathrm{III}\_1$ criterion).

The spectral realization data $D_\infty$ thus carries — at the level of its spectrum on the Hecke basis — the absolute-norm data of the integral ideals of $\mathfrak o_K$. The further structural-arithmetic content of this spectrum (relationships to $\zeta_K$, the Dedekind zeta function of $K$) is downstream substrate; we do not pursue it here.

---

## §8. Lean 4 formalization

The structural chain of §§3–7 has been recorded in Lean 4 against a pinned Mathlib revision, with zero `sorry` count across the formalization chain. The Lean encoding is type-correct end-to-end and the eight named axioms of §8.2 isolate the load-bearing analytic substrate; six scaffold-layer placeholders (§8.3) and one Lean substrate hypothesis (`hSubstrate_iii` for Theorem C, Mathlib Integration Target 9.1) record points where the prose proofs are unconditional but the Lean encoding remains conditional on infrastructure or theorems not yet present in Mathlib at the pinned SHA. The formalization is organized as a seven-cell chain L1–L7 mirroring the section structure of the paper, together with a base file `Basic.lean` defining the core types and an `Assembly.lean` composing the chain into a single result. We document the structure here, name the eight programme-level axioms with their literature citations, and discuss the project-local `Antilinear.lean` file developing polar decomposition for unbounded antilinear operators.

### §8.1. Overview of the formalization

The Lean 4 formalization is structured as the following modules in the namespace `Integers.TomitaTakesaki`:

| Module | Content | Section |
|---|---|---|
| `Basic.lean` | Core types: `BostConnesSystem`, `GNSTriple`, `TypeIII1FactorWitness`, `ModularPair`, `ModularPairProperties`, `ModularAutomorphismGroup`, `GaloisActionData`, `SpectralRealizationData` | §§2–7 typing |
| `L1BostConnesAlgebra.lean` | The Bost–Connes system with $\mathrm{KMS}\_1$ state, ITPFI factorization, KMS condition | §§2.1–2.4 |
| `L2GNSCyclicSeparating.lean` | GNS triple, cyclic separating $\Omega_1$, type $\mathrm{III}\_1$ factor identification | §3 |
| `L3PolarDecomposition.lean` | Polar decomposition $\bar S = J\,\Delta^{1/2}$ | §4.3 |
| `Antilinear.lean` | Project-local antilinear-operator + polar-decomposition theory | §4 substrate |
| `TomitaS.lean` | Tomita $S$ operator + modular data via polar decomposition | §4.1, §4.3 |
| `L4ModularFlow.lean` | Modular flow theorem $\sigma_t = \alpha_t$ (load-bearing) | §5 |
| `L5GaloisAction.lean` | Galois action and compatibility with modular conjugation | §6 |
| `L6MainTheorem.lean` | Four-clause main theorem composing L1–L5 | §§3–6 |
| `L7SpectralRealization.lean` | Spectral realization data $D_\infty$ | §7 |
| `Assembly.lean` | Full chain composition L1 → L7 + downstream bridges | n/a |

The formalization is pinned against Mathlib at commit `5e932f97dd25535344f80f9dd8da3aab83df0fe6` with Lean toolchain `v4.29.1`; build instructions are recorded in Appendix A. The full chain builds without errors, with no `sorry` placeholders in the formalization code: `grep -rE "^[[:space:]]*sorry|:= sorry" Integers/TomitaTakesaki/*.lean` returns no output.

### §8.2. The eight named programme-level axioms

Following the operator-algebras tradition of citing rather than re-deriving deep substrate, the formalization declares eight `axiom` statements — six for the Bost–Connes substrate (the C\*-algebra, KMS state, ITPFI factorization, etc.) and two for the Hilbert-space structure of the GNS quotient. Each axiom carries its literature citation in the docstring; the inventory is:

**L1 substrate citations** (six axioms in `L1BostConnesAlgebra.lean`):

1. `bc_system_exists` — the Bost–Connes C\*-dynamical system $(B_K, \alpha_t, \omega_1)$ for $K = \mathbb Q(i)$ exists. Citation: [BC95, Thm. 25] together with [CM08, Ch. III, §3].

2. `kms1State_isKMS` — the canonical state $\omega_1$, i.e. `BC.kms1State`, is a $\mathrm{KMS}\_1$ state for $(B_K, \alpha_t)$. Citation: [BC95, Thm. 25] (existence) and [BR97, §5.3] (the KMS predicate). Stated with explicit propositional content (ℂ-additivity, ℂ-homogeneity, normalization, positivity, KMS boundary condition); not vacuous.

3. `kms1_unique` — any $\mathrm{KMS}\_1$ state on $(B_K, \alpha_t)$ equals $\omega_1$. Citation: [BC95, Thm. 25] (uniqueness at $\beta = 1$ for $K = \mathbb Q$); [LLN09] (KMS classification for Bost–Connes-type systems of general number fields, including the imaginary-quadratic case). Stated with the load-bearing hypothesis `IsKMSStateAt BC 1 φ` so that uniqueness does not vacuously collapse the type.

4. `kms1_faithful` — for every nonzero $a \in B_K$ (in the real Bost–Connes system), $\omega_1(a^\ast a) \neq 0$. Citation: [BC95, §3, eq. (15)]. Restricted to `bc_system_exists` rather than universal in the `BostConnesSystem` type, to avoid soundness collapse on degenerate models.

5. `itpfi_factorization` — the canonical state $\omega_1$ on the real Bost–Connes system is non-tracial. Citation: [BC95, Prop. 33]; [AW68]; [CM08, Ch. III, Thm. 3.32]. Non-traciality is the sound, expressible, operational core of the Araki–Woods ITPFI factorization; the full prime-indexed tensor structure is named via this core rather than as an unverifiable infinite-product statement.

6. `time_evolution_is_automorphism` — $\alpha_t$ is a one-parameter $\ast$-automorphism group of $B_K$ (multiplicativity). Citation: [BC95, §3, Thm. 24]; [CM08, Ch. III, §3.2].

A seventh-but-derived item, `kms_condition`, gives the explicit $\mathrm{KMS}\_1$ boundary condition $\omega_1(ab) = \omega_1(b \cdot \sigma_{i\beta}(a))$ as a theorem derived from `kms1State_isKMS`; it introduces no new axiom (`#print axioms` chain only references `kms1State_isKMS`).

**L2 Hilbert-structure axioms** (two axioms in `L2GNSCyclicSeparating.lean`):

7. `gnsQuotientNACG_axiom` — *the GNS quotient `BC.Algebra ⧸ nullIdeal` carries a `NormedAddCommGroup` structure.* This is the structural claim that the GNS sesquilinear form descends to a norm on the quotient, which would discharge automatically were Mathlib's normed-quotient theory developed at the level of `StarRing + StarModule + positivity → seminorm via Cauchy–Schwarz → NACG after quotient`. The discharge is documented in §8.4 below as a Mathlib-upstream opportunity.

8. `gnsQuotientIPS_axiom` — the GNS quotient carries an `InnerProductSpace ℂ` structure with the inner product $\langle [a], [b] \rangle = \omega_1(a^\ast b)$. Same discharge path as item 7; well-definedness on the quotient + four sesquilinear axioms.

The two L2 axioms are the formalization-side analogues of the "the quotient is a pre-Hilbert space" claim in §3.1: at the level of mathematics this is a routine consequence of faithfulness and the GNS form's positivity; at the level of Mathlib type-classes, it requires more developed normed-quotient infrastructure than the pinned SHA carries. The axioms are inspectable, citable, and have an explicit upgrade path; future Mathlib development discharges them automatically without disturbing the chain.

### §8.3. Scaffold-layer placeholders and discharge inventory

**Terminology.** In what follows, a *`True` placeholder* means that the corresponding field of the relevant Lean structure is *typed as* `True` — its inhabitant is `trivial`, the unique inhabitant of `True` — rather than as the mathematical proposition the field name might suggest. A `True` placeholder is functionally distinct from a `sorry`: it introduces no axiom visible to `#print axioms`, and Lean accepts it as a complete, total inhabitant of its type. It is equally distinct from a genuine proof of the corresponding proposition: the field name (e.g. `polar_identity`) is informative-cosmetic, and the inhabited type is `True`, which carries no propositional content beyond inhabitation. A similar role is played by *identity-function placeholders* (e.g. `J : H → H` defined as `id`), where the structurally-correct type signature is filled by the identity map rather than by the intended antiunitary. Throughout this section, "scaffold-layer placeholder" refers to either form; the discharge route in each item below states what would replace the placeholder with the intended mathematical content.

In addition to the eight named axioms above, the formalization carries six structural-placeholder items at the scaffold layer — points where the load-bearing mathematical content from §§3–7 is encoded as a `True` placeholder or an identity-function placeholder, with the discharge route documented in the source. These placeholders do not affect the buildability of the chain (everything type-checks without `sorry`); they record the substrate work that is downstream of the present construction.

The six items are:

1. **Modular conjugation $J$ as antiunitary partial isometry.** In `Antilinear.lean`, the polar-decomposition output `polarDecomp.J` is currently the identity function `id`, with the involution property $J^2 = \mathrm{id}$ discharged by `fun _ => rfl`. The genuine antiunitary $J := \bar S \circ |S|^{-1}$ on $\mathrm{range}(|S|)$, extended by zero on the orthogonal complement, requires Mathlib's `Submodule.orthogonalProjection` for the range / $\mathrm{range}^\perp$ split together with the partial-isometry construction preserving antilinearity — a discrete piece of substrate work estimated at 200–500 lines of focused Lean development. This is Target 1; see Mathlib Integration Target 9.2.

2. **The polar-decomposition identity $\bar S = J\,\Delta^{1/2}$.** The corresponding field `polar_identity` in the `PolarDecomposition` structure is a `True` placeholder; the genuine identity requires parameterizing `PolarDecomposition` by the input $S$ (currently parameterized only by the Hilbert space), a medium refactor across `polarDecomp`, `TomitaS.modularData`, and the bridge. This is Target 2; see Mathlib Integration Target 9.2.

3. **The infinite tensor product of unbounded operators (and the Lean encoding of $D_\infty$).** Proposition 4.3's statement $\Delta = \bigotimes_\mathfrak p \Delta_\mathfrak p$ is not formalized at the Lean level: Mathlib does not (at the pinned SHA) provide infinite tensor products of unbounded operators in the ITPFI sense. The product structure is recorded in the prose as the structural input for the spectral data of Theorem E (and as the alternative prime-local route to Theorem C in §5.3), with the Lean substrate at the level of finite Hecke-basis monomials only. As a direct consequence, the Lean encoding `L7.spectral_realization` of Theorem E's operator $D_\infty = \log \Delta$ is currently the *zero CLM scaffold* `0 : H →L[ℂ] H` (self-adjoint by `IsSelfAdjoint.zero _`), with the genuine `cfc Real.log Δ` form awaiting the CFC instance chain on `L2.GNSHilbert BC`. The full mathematical content of Theorem E remains valid at the prose layer; only the Lean encoding is scaffold-typed. A future axiom (or theorem, once Mathlib gains infinite tensor products of unbounded operators) encoding the ITPFI factorization at the unbounded-operator level would close both this gap and the $D_\infty$ scaffold simultaneously.

4. **Separatingness of $\Omega_1$ at the scaffold layer.** The `TypeIII1FactorWitness.isSeparating` field is typed as `True` in `Basic.lean`, with the chain $\omega_1$-faithful $\Rightarrow$ separating (§3.2) carried at the prose layer. The well-definedness of the Tomita involution $S$ in §4.1 chains through this structural axiom. The discharge requires the `isCyclic` and `isFactor` fields to be promoted from `True` to genuine propositional content, which falls under Target 4 (the structural enrichment of `BostConnesSystem`; see Mathlib Integration Target 9.4).

5. **Sign-convention reconciliation between $L3$ and §§4–5.** The Lean module `L3PolarDecomposition.lean` declares its local computations in the Bratteli–Robinson Vol II §5.3 convention ($\sigma_t = \mathrm{Ad}(\Delta^{-it})$, $\Delta\cdot\Omega_{n,m,\alpha} = (N(m)/N(n))\,\Omega_{n,m,\alpha}$), while §§4–5 of the present paper adopt Connes' convention $\sigma_t = \mathrm{Ad}(\Delta^{it})$ uniformly (declared in §1.4). The two conventions differ by the sign of the inverse temperature; the corresponding statements are related by $\Delta \leftrightarrow \Delta^{-1}$ in the modular operator. A future Lean refactor harmonizing the L3 docstring with the Connes convention would remove this prose-vs-Lean drift; the mathematics is unchanged.

6. **Galois action scaffold and the Galois–modular-conjugation intertwining in `L5GaloisAction.lean`.** Two aligned scaffold facts together: the Lean module `L5GaloisAction.lean` realizes the Galois group as the *trivial* group $G = \{e\}$ (encoded as `Unit`) acting on `BC.Algebra` and `gns.HilbertSpace` by the identity, not as $\mathrm{Gal}(K/\mathbb Q) \cong \mathbb Z/2\mathbb Z$ acting by complex conjugation; correspondingly, the theorem `j_intertwines_galois` is a `True` placeholder. Together these have the consequence that Theorem D's clauses (i) and (ii) hold *vacuously* at the Lean level — the structural commutation $U_g\,J\,U_g^\ast = J$ is true for $g = e$ trivially, but the genuine content for the non-trivial Galois generator $\tau : i \mapsto -i$ is not formalized. The discharge route is the genuine $\mathbb Z/2$-action together with the combinatorial swap $\Omega_{n,m,\alpha} \mapsto (N(n)/N(m))^{1/2}\,\Omega_{m,n,-\alpha}$ on the bilateral Hecke basis (the Galois-equivariant form of the modular-conjugation action; cf. [CM08, Ch. III, §3.4]).

These six items document the boundary of the present formalization: every claim in §§3–7 is type-correctly recorded in the Lean chain, with the load-bearing structural content discharged via the named axioms of §8.2 and the scaffold-level placeholders inventoried here. Future substrate work plugs in at these named sites without restructuring the chain.

### §8.4. The `Antilinear.lean` contribution

A 230-line Lean 4 file `Antilinear.lean` develops the polar decomposition theory for unbounded antilinear operators on a complex Hilbert space, in the form required by the Tomita involution $S$ of §4. The construction parallels [Tak03, Ch. VIII, Thm. VIII.3.2] and is structured as follows:

- A `ConjugateLinearMap E F` type encoding antilinear maps between $\mathbb C$-modules, with additivity and conjugate-linearity over $\mathbb C$ as the structural fields. Composition rules: `linearComp` (linear ∘ antilinear = antilinear), `compConj` (antilinear ∘ antilinear = linear, the standard "two conjugations cancel" identity).

- A predicate `ConjugateLinearMap.IsClosable` for closable densely-defined antilinear operators. The witness is encoded structurally for use by the polar decomposition; the formal closure-of-graph construction is recorded as a Mathlib gap.

- A `ConjugateLinearMap.HasAdjoint` structure carrying the antilinear adjoint $S^\dagger$, the inner-product duality $\langle Sx, y\rangle = \langle S^\dagger y, x\rangle$, and the modular operator $\Delta = S^\dagger \circ S$ as a continuous linear map. Genuine self-adjointness and positivity of $\Delta$ are proved from the adjoint identity (`delta_isSelfAdjoint`, `delta_isPositive`) using the standard symmetric-on-complete-Hilbert-space promotion.

- The modulus operator $|S| := \sqrt{\Delta}$ defined via Mathlib's non-unital continuous functional calculus `CFC.sqrt`, with the identity $|S|^2 = \Delta$ proved.

- A `PolarDecomposition E` structure carrying $\Delta$, $J$, and the four Takesaki properties ($\Delta$ self-adjoint, $\Delta \geq 0$, $J^2 = \mathrm{id}$, $J\,\Delta\,J = \Delta^{-1}$ in the weak commutation form). The genuine antiunitary $J$ construction is the Target 1 item above.

- A constructive `polarDecomp` returning a `PolarDecomposition E` for any closable conjugate-linear operator with a `HasAdjoint` witness.

The file is project-local: Mathlib at the pinned SHA does not contain a polar-decomposition theory for unbounded antilinear operators, and the existing `Submodule.Quotient` / `UniformSpace.Completion` / CFC infrastructure does not compose into the required output. The `Antilinear.lean` file is proposed for upstream contribution to Mathlib, in a refactored form that drops the project-local idiom and provides the antilinear polar decomposition as a general Mathlib lemma.

### §8.5. Build and verification

The complete formalization can be built and verified independently by any reader with access to Lean 4 + Mathlib at the pinned SHA. Three `lake build` invocations confirm the chain:

- `lake build Integers.TomitaTakesaki.Assembly` — builds the full chain (2352 / 2352 obligations discharged).
- `lake build Integers.TomitaTakesaki.TomitaS` — builds the Tomita involution module (2926 / 2926).
- `lake build Integers.TomitaTakesaki.Antilinear` — builds the polar-decomposition module (2915 / 2915).

The obligation counts above are engineering metrics — they tally type-checking obligations discharged by Lean during the build. They include the trivially discharged obligations corresponding to the six scaffold-layer placeholders of §8.3 (each of which is discharged by `trivial` against a `True` type, or by `rfl` against an identity-function definition). The count does not measure the mathematical content of the formalization at the level of named theorems; that content is the union of (a) the genuine proofs of the assembled chain L1 → L7, (b) the eight named axioms of §8.2, and (c) the six scaffold-layer placeholders of §8.3.

The `#print axioms` command applied to any theorem in the chain produces a finite list of axioms; the inventory matches the eight named axioms of §8.2 together with the standard Lean foundational axioms (`Classical.choice`, `Quot.sound`, `propext`). No additional axioms are introduced by the chain.

The three `lake build` invocations of Appendix A together with the axiom-inventory check `grep -hE "^axiom " Integers/TomitaTakesaki/*.lean | wc -l → 8` provide the full independent-verification path for any reader.

---

## §9. Mathlib Integration Roadmap

We close with four Mathlib integration targets explicitly identified by the present construction. All four are formalization-side: they concern the Lean substrate and its relationship to Mathlib, not open mathematical questions about the Bost–Connes Tomita–Takesaki theory itself. Each is deferred to a dedicated Mathlib upstream PR rather than bundled into the present submission — both to keep the paper scope-contained, and to allow each upstream contribution its own review and attribution at Mathlib's pace.

### Mathlib Integration Target 9.1 (Lean-side discharge of `hSubstrate_iii` via Mathlib $W^\ast$-KMS-uniqueness)

Formalize Takesaki's $W^\ast$-KMS-uniqueness theorem [BR97, Thm. 5.3.10] in Mathlib, discharging the Lean substrate hypothesis `hSubstrate_iii` of module L6 and converting the Lean-side Theorem C from conditional-on-substrate to unconditional.

The prose proof of Theorem C in §5.2 is unconditional. The Lean encoding nonetheless remains conditional on the substrate hypothesis `hSubstrate_iii` of module L6, which encodes the precise content of Takesaki's KMS-uniqueness theorem: that for a faithful normal state $\omega$ on a von Neumann algebra $M$, the modular automorphism group $\sigma_t^\omega$ is the unique $\sigma$-weakly continuous one-parameter $\ast$-automorphism group of $M$ for which $\omega$ is a $\mathrm{KMS}\_1$ state. This is a standard result in the operator-algebras literature, but Mathlib at the pinned SHA does not formalize it: the relevant infrastructure — analytic vectors, $\sigma$-weak topology on a von Neumann algebra, KMS condition at the $W^\ast$ level — exists in fragments, but the theorem itself is not present.

The route is a Mathlib PR formalizing [BR97, Thm. 5.3.10] (or the equivalent [Tak03, Ch. VIII, Thm. 1.2] formulation), with intermediate lemmas matching the steps in §5.1–§5.2: existence + uniqueness of the $\sigma$-weakly continuous extension $\widetilde\alpha_t$ from [BR87, Prop. 2.5.22], transfer of the KMS condition from a $\sigma$-weakly dense $\ast$-subalgebra via [BR97, Cor. 5.3.4], and the KMS-uniqueness identification via [BR97, Thm. 5.3.10]. The estimated scope is 500–1000 lines of focused Lean work and would benefit both the present Lean substrate and any future formalization of operator-algebraic dynamics in Mathlib.

We emphasize that this is a formalization problem, not a mathematical problem: the prose proof of Theorem C is complete and unconditional; the Lean substrate hypothesis `hSubstrate_iii` is the artifact of Mathlib's current coverage, not of a mathematical gap.

### Mathlib Integration Target 9.2 (Mathlib upstream of antilinear polar decomposition)

*Develop the polar decomposition theory for unbounded closed antilinear operators on complex Hilbert spaces as a contribution to Mathlib.*

The project-local file `Antilinear.lean` (§8.4) provides the polar-decomposition theory in the form required by the Tomita involution, with the substrate $\Delta = S^\dagger \circ S$ self-adjoint + positive + $|S|^2 = \Delta$ all proved against Mathlib's CFC infrastructure. The genuine antiunitary $J := \bar S \circ |S|^{-1}$ — Targets 1 and 2 in §8.3 — remain to be completed; the corresponding propositional content ($J^2 = \mathrm{id}$, $J\,\Delta\,J = \Delta^{-1}$, $\bar S = J\,\Delta^{1/2}$ as honest predicates rather than `True` placeholders) requires Mathlib's `Submodule.orthogonalProjection` infrastructure together with the partial-isometry construction preserving antilinearity. The estimated effort is 200–500 lines of focused Lean work for the project-local upgrade, plus a refactor for the Mathlib upstream PR.

The Mathlib gap identified here is concrete: Mathlib at the pinned SHA has bounded-operator polar decomposition for linear maps on Hilbert spaces, the continuous functional calculus on positive operators (including the square root), and the orthogonal-projection theory for closed subspaces, but no antilinear-operator type at all (the closest analogue is the `SemilinearMap (starRingEnd ℂ)` Mathlib type, which is not specialized to the inner-product setting). A Mathlib PR establishing the antilinear polar decomposition would benefit both the present construction and any future formalization of Tomita–Takesaki theory in Lean.

### Mathlib Integration Target 9.3 (soundness-audited L1 axiom-discharge)

*Convert the six L1 substrate axioms of §8.2 into project-local theorems via concrete C\*-algebraic constructions, with a soundness audit ensuring no joint inconsistency at the placeholder layer.*

The naive route — replacing `axiom bc_system_exists : BostConnesSystem` with a concrete `def`-style construction — carries a subtle soundness risk identified during the formalization: if the concrete construction collapses the algebra to a degenerate model (e.g., a `PUnit`-based scaffolding), then the other five axioms applied to this degenerate model can force inconsistencies. The current formalization side-steps this via the *Restrict* discipline ([BR97, §5.3] precedent applied to the formalization): `kms1_faithful` and `itpfi_factorization` are restricted to `bc_system_exists` rather than universal over `BostConnesSystem`; uniqueness `kms1_unique` is conditioned on the `IsKMSStateAt` predicate so that it does not collapse trivially.

An honest discharge of the L1 axioms — replacing each axiom with a theorem-style construction — requires (a) defining a concrete `BostConnesSystem` placeholder with sufficient algebraic structure to satisfy the substrate, (b) a soundness audit verifying that the five other axioms remain non-vacuous against this placeholder, (c) restating each via vacuous-hypothesis preconditions where needed to maintain consistency, and (d) documenting the upgrade path from placeholder to the real BC algebra (per [BR97, §5.3] and [LLN09]) where the axioms recover their substantive content. Estimated scope: a focused 500–1000 line refactor, best executed as a single atomic Lean session.

### Mathlib Integration Target 9.4 (structural enrichment for L2 axiom discharge)

*Enrich the `BostConnesSystem` type with `[NormedAddCommGroup Algebra]` and `[InnerProductSpace ℂ Algebra]` typeclass fields, allowing the two L2 Hilbert-structure axioms of §8.2 to be discharged via Mathlib's `Submodule.Quotient.normedAddCommGroup` and the GNS-form-induced inner product.*

The discharge path is documented in §8.2: with the enriched type, `gnsQuotientNACG_axiom` and `gnsQuotientIPS_axiom` both become provable from the StarRing + StarModule + $\omega_1$-positivity structure, using Mathlib's existing normed-quotient infrastructure. The scope is a medium refactor (~100 lines of changes across `Basic.lean`, `L1BostConnesAlgebra.lean`, and `L2GNSCyclicSeparating.lean`), with the structural cost being that the enriched `BostConnesSystem` constraints ripple through the chain.

Problems 9.3 and 9.4 are best coordinated as a joint refactor: both touch the `BostConnesSystem` type definition, and the soundness audit of 9.3 naturally extends to verify the structural-enrichment additions of 9.4 against the L2 axioms.

---

### Acknowledgments

This paper would not exist without the foundational mathematics on which it builds. The depth and structural beauty of modular theory and its operator-algebraic context made this construction possible.

I am deeply indebted to Minoru Tomita and Masamichi Takesaki for modular theory itself — Tomita for the originating insight, Takesaki for the canonical form on which Theorem C rests; to Jean-Benoît Bost and Alain Connes for the Hecke C\*-algebra and its phase transition at the critical state; to Alain Connes, Matilde Marcolli, and Niranjan Ramachandran for the imaginary-quadratic generalization on which every theorem here lives; to Marcelo Laca, Nadia Larsen, and Sergey Neshveyev for the KMS classification grounding §2; to Huzihiro Araki and E. J. Woods for the ITPFI classification and asymptotic ratio set; to Uffe Haagerup for the uniqueness of the injective type $\mathrm{III}\_1$ factor; and to the wider operator-algebras community whose work appears in the references throughout.

Any errors of attribution or interpretation are my own.

---

## References

**Araki, H.; Woods, E. J.** *A classification of factors.* Publications of the Research Institute for Mathematical Sciences, Kyoto University, Series A, Vol. 4 (1968), pp. 51–130. DOI: [10.2977/prims/1195195263](https://doi.org/10.2977/prims/1195195263). <!-- \bibitem{AW68} -->

**Bost, J.-B.; Connes, A.** *Hecke algebras, type III factors and phase transitions with spontaneous symmetry breaking in number theory.* Selecta Mathematica (New Series), Vol. 1, Issue 3 (1995), pp. 411–457. DOI: [10.1007/BF01589495](https://doi.org/10.1007/BF01589495). <!-- \bibitem{BC95} -->

**Bratteli, O.; Robinson, D. W.** *Operator Algebras and Quantum Statistical Mechanics II: Equilibrium States. Models in Quantum Statistical Mechanics.* Texts and Monographs in Physics, Springer-Verlag, Berlin, 2nd edition, 1997. DOI: [10.1007/978-3-662-09089-3](https://doi.org/10.1007/978-3-662-09089-3); ISBN: 978-3-540-61443-2. <!-- \bibitem{BR97} -->

**Bratteli, O.; Robinson, D. W.** *Operator Algebras and Quantum Statistical Mechanics I: C\*- and W\*-Algebras, Symmetry Groups, Decomposition of States.* Texts and Monographs in Physics, Springer-Verlag, Berlin, 2nd edition, 1987. DOI: [10.1007/978-3-662-02520-8](https://doi.org/10.1007/978-3-662-02520-8); ISBN: 978-3-540-17093-8. <!-- \bibitem{BR87} -->

**Connes, A.; Consani, C.; Moscovici, H.** *Prolate spheroidal operators and the Bost–Connes spectral realization.* arXiv preprint, [arXiv:2511.22755](https://arxiv.org/abs/2511.22755) (2025). <!-- \bibitem{CCM25} -->

**Cuntz, J.; Echterhoff, S.; Li, X.** *On the K-theory of crossed products by automorphic semigroup actions.* The Quarterly Journal of Mathematics, Vol. 64, Issue 3 (2013), pp. 747–784. DOI: [10.1093/qmath/hat021](https://doi.org/10.1093/qmath/hat021). <!-- \bibitem{CEL13} -->

**Connes, A.; Marcolli, M.; Ramachandran, N.** *KMS states and complex multiplication.* Selecta Mathematica (New Series), Vol. 11, Issue 3-4 (2005), pp. 325–347. DOI: [10.1007/s00029-005-0013-x](https://doi.org/10.1007/s00029-005-0013-x). <!-- \bibitem{CMR05} -->

**Connes, A.; Marcolli, M.** *Noncommutative Geometry, Quantum Fields and Motives.* American Mathematical Society Colloquium Publications, Vol. 55. AMS, Providence, RI, 2008. DOI: [10.1090/coll/055](https://doi.org/10.1090/coll/055); ISBN: 978-0-8218-4210-2. <!-- \bibitem{CM08} -->

**Connes, A.** *Une classification des facteurs de type III.* Annales scientifiques de l'École Normale Supérieure, 4ᵉ série, tome 6, no. 2 (1973), pp. 133–252. DOI: [10.24033/asens.1247](https://doi.org/10.24033/asens.1247). <!-- \bibitem{Con73} -->

**Connes, A.** Classification of injective factors. Cases $\mathrm{II}\_1$, $\mathrm{II}\_\infty$, $\mathrm{III}\_\lambda$, $\lambda \neq 1$. Annals of Mathematics, Vol. 104, No. 1 (1976), pp. 73–115. DOI: [10.2307/1971057](https://doi.org/10.2307/1971057). <!-- \bibitem{Con76} -->

**Haagerup, U.** Connes' bicentralizer problem and uniqueness of the injective factor of type $\mathrm{III}\_1$. Acta Mathematica, Vol. 158 (1987), pp. 95–148. DOI: [10.1007/BF02392257](https://doi.org/10.1007/BF02392257). <!-- \bibitem{Haa87} -->

**Laca, M.; Larsen, N. S.; Neshveyev, S.** *On Bost–Connes type systems for number fields.* Journal of Number Theory, Vol. 129, Issue 2 (2009), pp. 325–338. DOI: [10.1016/j.jnt.2008.09.008](https://doi.org/10.1016/j.jnt.2008.09.008). <!-- \bibitem{LLN09} -->

**Powers, R. T.** *Representations of uniformly hyperfinite algebras and their associated von Neumann rings.* Annals of Mathematics, Vol. 86, No. 1 (1967), pp. 138–171. DOI: [10.2307/1970364](https://doi.org/10.2307/1970364). <!-- \bibitem{Pow67} -->

**Takesaki, M.** *Tomita's Theory of Modular Hilbert Algebras and its Applications.* Lecture Notes in Mathematics, Vol. 128. Springer-Verlag, Berlin, 1970. DOI: [10.1007/BFb0065832](https://doi.org/10.1007/BFb0065832); ISBN: 978-3-540-04917-3. <!-- \bibitem{Tak70} -->

**Takesaki, M.** *Theory of Operator Algebras II.* Encyclopaedia of Mathematical Sciences, Vol. 125 (Operator Algebras and Non-Commutative Geometry VI), Springer-Verlag, Berlin, 2003. DOI: [10.1007/978-3-662-10451-4](https://doi.org/10.1007/978-3-662-10451-4); ISBN: 978-3-540-42914-2. <!-- \bibitem{Tak03} -->

**Tomita, M.** *Standard form of von Neumann algebras.* Mimeographed preprint, The Fifth Functional Analysis Symposium of the Mathematical Society of Japan, Mathematical Institute, Tōhoku University, Sendai, 1967. (In Japanese; circulated as preprint; the theory was subsequently developed by Takesaki [Tak70].) <!-- \bibitem{Tom67} -->

---

## Appendix A. Build and verification

This appendix records the build instructions for the Lean 4 formalization documented in §8, sufficient for any reader to machine-check the structural scaffold of Theorems A–E independently by running the formalization against a pinned Mathlib revision.

**Toolchain.** Lean 4 at toolchain version `v4.29.1`. Lake (the Lean 4 build system) ships with the toolchain; no additional installation is required beyond `elan` (the Lean 4 version manager) and a recent C++ toolchain.

**Mathlib pin.** The formalization builds against Mathlib at commit hash

$$
\texttt{5e932f97dd25535344f80f9dd8da3aab83df0fe6}.
$$

The pin is declared in `lake-manifest.json` at the project root. The pin must be honored to reproduce the build: Mathlib's continuous functional calculus API, the `Submodule.Quotient` infrastructure, the `InnerProductSpace.Completion` chain, and the inner-product adjoint theory have all evolved across recent Mathlib versions, and the project-local `Antilinear.lean` file (§8.4) relies on the precise API surface at the pinned SHA.

**Build invocations.** From the project root, the following three commands verify the chain:

```
lake build Integers.TomitaTakesaki.Assembly      # Theorems A–E (chain composition); 2352/2352 obligations
lake build Integers.TomitaTakesaki.TomitaS       # §4.1, §4.3 (Tomita S + modular data); 2926/2926
lake build Integers.TomitaTakesaki.Antilinear    # §4 antilinear-operator substrate; 2915/2915
```

The first invocation builds the assembled chain `L1 → L7` and witnesses Theorems A through E in their structural form. The second invocation builds the Tomita $S$-operator module separately, exposing the polar-decomposition substrate at the level required by §4.3. The third invocation builds the project-local antilinear-operator theory of §8.4, including the antilinear polar decomposition `polarDecomp`.

**Sorry-count verification.** The chain contains zero code-level `sorry` placeholders. The verification command is:

```
grep -rE "^[[:space:]]*sorry|:= sorry" Integers/TomitaTakesaki/*.lean
```

which returns no output across the eleven module files of §8.1.

**Axiom-inventory verification.** The chain declares exactly eight `axiom` statements, with the inventory of §8.2. The count is verifiable by:

```
grep -hE "^axiom " Integers/TomitaTakesaki/*.lean | wc -l
# → 8
```

The `#print axioms` Lean command applied to any theorem in the chain produces a finite list referencing only the eight named axioms together with the foundational axioms `Classical.choice`, `Quot.sound`, and `propext`.

> **Source commit pins.** Two commit anchors identify the present formalization for independent verification: the chain-completion commit (Phase 6 sweep; `1ca33cb`) marks the zero-`sorry` state, and the present-paper-aligned commit (recorded at the time of submission) marks the prose-to-Lean correspondence used in §8. Both are recorded in the formalization repository at https://github.com/localparty/tt-bost-connes.







