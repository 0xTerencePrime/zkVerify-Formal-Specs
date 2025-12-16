# zkVerify Formal Specifications

## Overview

This repository contains **formal proofs** for the non-standard Binary Merkle Tree logic used in [zkVerify](https://zkverify.io/)'s Substrate-compatible attestation contracts.

Specifically, we provide a mathematical proof of correctness for the `verifyProofKeccak` function found in `zkv-attestation-contracts`. This implementation includes a unique "quirk" in how it handles unbalanced tree layers (orphan nodes), which differs from standard Merkle Tree implementations.

**Key Achievement:**
We have formally verified that the Solidity implementation's iterative hashing logic is isomorphic to a structural inductive definition of a Merkle Tree, using concrete **256-bit vector (BitVec 256)** types to rigorously model EVM hash outputs.

## The "Substrate Quirk"

Standard Merkle Trees usually duplicate the last node or handle odd counts by lifting the node to the next layer. Substrate's implementation, however, treats an orphan node on the right as a "left sibling" hash input under specific conditions:

```solidity
// From Contracts
if (position % 2 == 1 || position + 1 == width) {
    computedHash = keccak256(abi.encodePacked(proofElement, computedHash));
} else {
    computedHash = keccak256(abi.encodePacked(computedHash, proofElement));
}
```

This logic is captured formally in `ZKVerify/MerkleSolid.lean` and proven sound.

## Verification Artifacts

*   **Language:** Lean 4
*   **Library:** Mathlib
*   **Main Theorem:** `soundness_of_substrate_merkle`
*   **Hash Model:** `BitVec 256` (Concrete EVM-compatible type)

The proof demonstrates that if the verification function returns `true`, there exists a valid Merkle path structure (`InMerkleTree`) linking the leaf to the root.

## Usage

Prerequisites: [Install Lean 4](https://leanprover.github.io/lean4/doc/quickstart.html).

1.  **Clone the repository:**
    ```bash
    git clone https://github.com/YOUR_USERNAME/zkVerify-Formal-Specs.git
    cd zkVerify-Formal-Specs
    ```

2.  **Get dependencies:**
    ```bash
    lake update
    ```

3.  **Compile and Verify:**
    ```bash
    lake build
    ```
    *A successful build (exit code 0) indicates all theorems have been proven.*

## Project Structure

*   `ZKVerify/MerkleSolid.lean`: The core specification and proof file.
*   `lakefile.toml`: Project configuration and dependencies.
