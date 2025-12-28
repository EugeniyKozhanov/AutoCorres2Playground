# Chamber 03: Force Symbolic Names

## Purpose

This chamber demonstrates how using **symbolic constants instead of magic numbers** makes proofs more universal and maintainable - a key technique inspired by seL4's approach to platform-independent verification.

## Key Principle

**Universal Proofs Through Abstraction**: By replacing literal values with named constants, proofs reference symbolic names rather than specific numbers.

## Benefits for Verification

### 1. Platform-Independent Proofs
Change one constant definition, not every lemma.

### 2. Self-Documenting Proofs  
`PCI_VENDOR_INTEL` is clearer than `0x8086` in proofs.

### 3. Abstraction
Proofs work for any value of `PCI_MAX_DEVICES`, not just 32.

## Summary

Symbolic names transform specific proofs into universal theorems - foundational to seL4's "next 700 platforms" approach.
