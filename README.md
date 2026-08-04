# crypto_topos

A Formal Verification Framework for Cryptographic Protocols in the Effective 2-Topos via SynthLean / HoTTLean

[![Build Status](https://github.com/yura-ogura/crypto_topos/actions/workflows/build.yml/badge.svg)](https://github.com/yura-ogura/crypto_topos/actions)
[![Lean 4 CI](https://img.shields.io/badge/Lean4-v4.25.0--rc2-blue)](https://github.com/leanprover/lean4)
[![License](https://img.shields.io/badge/License-Apache_2.0-green.svg)](LICENSE)

---

## Overview

`crypto_topos` is a formally verified proof-of-concept (PoC) framework in Lean 4, designed to model zero-knowledge cryptographic protocols and geometric transformations within categorical semantics. By utilizing **Homotopy Type Theory (HoTT)**, **Natural Model Semantics**, and structural definitions of the **Effective 2-Topos ($\mathcal{Eff}_2$)**, this repository establishes a rigorous bridge between abstract type-theoretic syntax and concrete algebraic computations.

### Key Features & Current Capabilities

- **Axiomatic Semantic Bridge & Soundness:** Connects deeply embedded syntax (`SynthLean`) with concrete $\mathbb{Z}_q$ algebraic models via heavily optimized axiomatic interfaces (to prevent AST explosion). The absolute soundness theorem is mechanically checked with respect to these axioms.
- **Structural Formalization of $\mathcal{Eff}_2$:** Provides foundational definitions and axiomatic specifications for fibrant 0-types, coherent groupoids, and the $\tau_0$-truncation bridge mapping $\mathcal{Eff}_2$ structures to the $\mathcal{Eff}_1$ topos.
- **Verified Path Types & Internal Identity:** Implements Awodey–Hua Path Types. The intensional MLTT identity elimination ($J$-rule) is strictly proven via `theorem` using Hurewicz fibrations and connections.
- **Algebraic & Geometric Computation Engine:** Implements the Pohlig–Hellman discrete logarithm algorithm, 7D manifold potential fields ($\Psi_7$), geodesic residual constraints, and validates decryption correctness over the scalar field $\mathbb{Z}_q$.

---

## Repository Structure

- `CITATION.cff`
- `CryptoTopos.lean` : Main library export file
- `CryptoTopos/`
  - `Frontend.lean` : EDSL syntax declarations and macro expansions for `crypto_topos`
  - `Interpretation.lean` : Absolute Soundness mapping linking syntax to semantics via `Interpretation.Wf`
  - `Model.lean` : Discrete logarithm, 7D manifold geometry, and geodesic path computational models
  - `SemanticProofs.lean` : $\mathbb{Z}_q$ algebraic reduction infrastructure and fully proven correctness theorems
  - `main.lean` : End-to-end verification entry point evaluating syntactic judgments to presheaf morphisms
- `Reference/`
  - `Syntax.lean` : Pure HoTT-compliant formalization of $\mathcal{Eff}_2$ structures and MLTT Path Types

### Module Breakdown

- **`CryptoTopos/Model.lean`:** Defines the concrete mathematical engine. Implements modular arithmetic over $q = 2147483647$, the Pohlig–Hellman algorithm, discrete 4D manifolds, and geodesic path concatenation.
- **`CryptoTopos/SemanticProofs.lean`:** Contains concrete algebraic reduction lemmas using `ring` tactics. Fully proves `concrete_Correctness_Path_eps0_impl` ($c - s \cdot r + s \cdot r \equiv n \pmod q$) without unproven assumptions.
- **`CryptoTopos/Interpretation.lean`:** Bridges the abstract natural model universe with concrete proofs. Establishes `crypto_topos_interpretation_wf` and checks the structural `crypto_absolute_soundness` theorem.
- **`Reference/Syntax.lean`:** Serves as the pure theoretical foundation. Isolated in the `Reference/` directory to provide a standalone, strictly HoTT-compliant formalization of Awodey & Emmenegger (2025) and Awodey & Hua (2026), completely decoupled from the cryptographic application layer. The $J$-elimination rule is strictly proven (`IdElim_J_comp`), while higher topos structures are laid out as axiomatic interfaces.

---

## Formal Verification Highlights

### 1. Machine-Checked Correctness of Encryption/Decryption
The framework strictly proves that for any message $n$, secret $s$, and randomness $r$, deciphering an encrypted ciphertext strictly recovers the original plaintext $n$ in the scalar field $\mathbb{Z}_q$:

$$\text{Decipher}(\text{Cipher}(n, s, r), s, r) \equiv n \pmod q$$

### 2. Absolute Soundness Evaluation
Under the defined axiomatic signature, every syntactic typing derivation $\Gamma \vdash_l t : A$ in the `crypto_topos` theory translates directly into a commutative diagram of morphisms in the presheaf semantics:

$$\text{interpTm}(\text{deriv}) \gg (M_l).\text{tp} = \text{interpTy}(\text{deriv.wf}\_\text{tp})$$

---

## Limitations & Future Work

As a Proof of Concept (PoC), this framework currently abstracts certain complex type-theoretic and categorical formations (e.g., deeply nested $\Sigma$-types and presheaf limits) into `axiom` definitions to ensure computational feasibility in Lean 4 (avoiding AST explosion and timeout limits). 

Future milestones intended for ecosystem grants include:
1. Replacing intermediate `axiom` interfaces with constructed instances where computationally viable.
2. Extending the $\mathbb{Z}_q$ algebraic masking to support non-linear arithmetic circuits (e.g., PlonK / Kimchi).
3. Developing developer-friendly tooling to generate verified ZK-circuit representations directly from the `crypto_topos` DSL.

---

## Prerequisites and Building

### Prerequisites

- **Lean 4** (`v4.25.0-rc2`)
- **elan** (Lean version manager)

### Build Instructions

1. Clone the repository to your local environment.
2. Run `lake build` in your terminal.

The dependencies (including `HoTTLean`) will be automatically fetched and compiled during the build process.

---

## References & Citation

If you reference or use this work, please cite the following publications:

### 1. Toward the effective 2-topos (Journal Article)
* **Authors:** Steve Awodey, Jacopo Emmenegger
* **Journal:** *Mathematical Structures in Computer Science*, Vol. 35, e32 (2025)
* **DOI:** [10.1017/S0960129525100352](https://doi.org/10.1017/S0960129525100352)

### 2. A Certifying Proof Assistant for Synthetic Mathematics in Lean
* **Authors:** Wojciech Nawrocki, Joseph Hua, Mario Carneiro, Yiming Xu, Spencer Woolfson, Shuge Rong, Sina Hazratpour, Steve Awodey
* **Conference:** *Proceedings of the 15th ACM SIGPLAN International Conference on Certified Programs and Proofs (CPP '26)*, pp. 88–103 (2026)
* **DOI:** [10.1145/3779031.3779087](https://doi.org/10.1145/3779031.3779087)

### 3. Path Types in Algebraic Type Theory
* **Authors:** Steve Awodey, Joseph Hua
* **Preprint:** arXiv:2601.06567 (2026)

```bibtex
@article{awodey2025toward,
  author    = {Steve Awodey and Jacopo Emmenegger},
  title     = {Toward the effective 2-topos},
  journal   = {Mathematical Structures in Computer Science},
  volume    = {35},
  pages     = {e32},
  year      = {2025},
  publisher = {Cambridge University Press},
  doi       = {10.1017/S0960129525100352}
}

@inproceedings{nawrocki2026certifying,
  author    = {Wojciech Nawrocki and Joseph Hua and Mario Carneiro and Yiming Xu and Spencer Woolfson and Shuge Rong and Sina Hazratpour and Steve Awodey},
  title     = {A Certifying Proof Assistant for Synthetic Mathematics in Lean},
  booktitle = {Proceedings of the 15th ACM SIGPLAN International Conference on Certified Programs and Proofs (CPP '26)},
  pages     = {88--103},
  year      = {2026},
  publisher = {ACM},
  doi       = {10.1145/3779031.3779087}
}

@article{awodey2026path,
  author    = {Steve Awodey and Joseph Hua},
  title     = {Path Types in Algebraic Type Theory},
  journal   = {arXiv preprint arXiv:2601.06567},
  year      = {2026}
}
```
---

## License

This project is licensed under the Apache License 2.0 - see the LICENSE file for details.

Copyright (c) 2026 yura-ogura

