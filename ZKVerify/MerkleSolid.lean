import Mathlib.Data.Nat.Basic
import Mathlib.Data.UInt
import Mathlib.Data.BitVec
import Mathlib.Tactic

/-!
# Formal Verification of zkVerify's "Substrate Binary Merkle Tree" Logic

This file formalizes the EXACT logic found in `zkv-attestation-contracts/contracts/lib/Merkle.sol`.
We target the `verifyProofKeccak` function and its specific handling of edge nodes.
-/

namespace ZKVerify

-- Use a concrete 256-bit vector for hashes, matching Keccak-256 output.
abbrev Hash := BitVec 256

/--
The logic state for the verification loop.
-/
structure VerifyState where
  computedHash : Hash
  position : Nat
  width : Nat

/--
Problem 1: Implement the "Substrate Quirk" Logic.
Matches:
```solidity
if (position % 2 == 1 || position + 1 == width) {
    computedHash = keccak256(abi.encodePacked(proofElement, computedHash));
} else {
    computedHash = keccak256(abi.encodePacked(computedHash, proofElement));
}
position /= 2;
width = (width - 1) / 2 + 1;
```
-/
def step (keccak : Hash → Hash → Hash) (current : VerifyState) (proofElement : Hash) : VerifyState :=
  let pos := current.position
  let wid := current.width
  let h   := current.computedHash
  
  let newHash := 
    if pos % 2 == 1 || pos + 1 == wid then
      keccak proofElement h -- "Quirk": Proof is Left Sibling
    else
      keccak h proofElement -- Standard: Proof is Right Sibling
      
  { computedHash := newHash, 
    position := pos / 2, 
    width := (wid - 1) / 2 + 1 }

/--
Problem 2: The Full Verify Function.
Must match signature: root, proof[], numberOfLeaves, leafIndex, leaf
-/
def verify 
  (keccak : Hash → Hash → Hash) 
  (hash_leaf : String → Hash)
  (root : Hash) 
  (proof : List Hash) 
  (numberOfLeaves : Nat) 
  (leafIndex : Nat) 
  (leaf : String) : Bool :=
  let initialState : VerifyState := { 
    computedHash := hash_leaf leaf, 
    position := leafIndex, 
    width := numberOfLeaves 
  }
  let finalState := proof.foldl (step keccak) initialState
  finalState.computedHash == root

/--
Problem 3: The Collision Resistance Axiom.
We assume Keccak is perfect.
-/
def IsCollisionResistant (keccak : Hash → Hash → Hash) : Prop :=
  ∀ a b c d, keccak a b = keccak c d → a = c ∧ b = d

/--
A single step in the Merkle path. 
Captures the "Substrate Quirk" logic in a relational form.
-/
def MerkleStep (keccak : Hash → Hash → Hash) (child : Hash) (w i : Nat) (parent : Hash) : Prop :=
  ∃ sibling,
    let is_right_node := i % 2 == 1 || i + 1 == w
    let computed := if is_right_node then keccak sibling child else keccak child sibling
    parent = computed

/--
Inductive predicate defining membership in a Substrate Merkle Tree.
`InMerkleTree keccak root w i h` means `h` is a valid node at width `w` and index `i` 
that leads to `root` via the Substrate hashing rules.
-/
inductive InMerkleTree (keccak : Hash → Hash → Hash) (root : Hash) : Nat → Nat → Hash → Prop where
  | base (w i : Nat) : InMerkleTree keccak root w i root
  | step (child parent : Hash) (w i : Nat) :
      MerkleStep keccak child w i parent →
      InMerkleTree keccak root ((w - 1) / 2 + 1) (i / 2) parent →
      InMerkleTree keccak root w i child

/--
Lemma: Generalization for the verification loop.
If the fold of `step` over a proof results in `root`, then the starting state represents a valid node in the tree.
-/
lemma verify_lemma 
  (keccak : Hash → Hash → Hash) 
  (root : Hash) 
  (proof : List Hash) 
  (s : VerifyState) : 
  (proof.foldl (step keccak) s).computedHash = root → 
  InMerkleTree keccak root s.width s.position s.computedHash := by
  induction proof generalizing s with
  | nil =>
    intro h_eq
    dsimp at h_eq
    rw [h_eq]
    apply InMerkleTree.base
  | cons p ps ih =>
    intro h_eq
    dsimp at h_eq
    let next_s := step keccak s p
    have h_next := ih next_s h_eq
    
    refine InMerkleTree.step s.computedHash next_s.computedHash s.width s.position ?_ ?_
    · -- MerkleStep
      unfold MerkleStep
      -- Prove existence of sibling `p` and equality
      refine ⟨p, ?_⟩
      simp [step, next_s]
    · -- Tree structure
      exact h_next

/--
Problem 4: Soundness Theorem (The Sniper Shot).
Prove that if `verify` returns true, then `leaf` is part of the logical tree structure 
defined by this specific Substrate algorithm.
-/
theorem soundness_of_substrate_merkle 
  (keccak : Hash → Hash → Hash)
  (hash_leaf : String → Hash)
  (root : Hash) (proof : List Hash) (total : Nat) (idx : Nat) (leaf : String)
  (_h_cr : IsCollisionResistant keccak)
  (h_valid : verify keccak hash_leaf root proof total idx leaf = true) :
  InMerkleTree keccak root total idx (hash_leaf leaf) := by
  unfold verify at h_valid
  dsimp at h_valid
  rw [beq_iff_eq] at h_valid
  apply verify_lemma keccak root proof { computedHash := hash_leaf leaf, position := idx, width := total }
  exact h_valid

end ZKVerify
