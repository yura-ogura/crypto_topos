# crypto_topos

Formally verified mathematical structures and cryptographic protocols using HoTTLean / SynthLean

## Overview
This repository contains formal proofs of Cryptographic Topos.

#Prerequisites
- Lean 4 ('v4.25.0-rc2')
- 【HoTTLean】(https://github.com/sinhp/HoTTLean) (Fetched automatically via Lake)

## Structure
- 'CryptoTopos/Syntax.lean': This is the internal language.
- 'CryptoTopos/Model.lean': This is the external model.
- 'CryptoTopos/INterpretation': This couples both of two.

## How to build
To build the project locally, run:
'''shell
lake build
