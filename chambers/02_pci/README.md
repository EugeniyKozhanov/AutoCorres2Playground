# PCI MMIO Verification with Haskell Specifications

## Project Structure

```
chambers/02_pci/
├── c/
│   └── pci_mmio.c                    # C implementation
├── haskell/
│   └── src/
│       └── PCI_MMIO.lhs              # Haskell specification (SINGLE SOURCE)
├── skel/
│   └── PCI_MMIO_H.thy                # Skeleton template for code generation
├── design/
│   ├── PCI_MMIO_H.thy                # Generated theory (Haskell + AutoCorres)
│   └── PCI_MMIO_Proof.thy            # Refinement proofs
├── ROOT                              # Isabelle session configuration
├── skel.txt                          # Translator configuration
├── run_translator.sh                 # Haskell-to-Isabelle translator
└── Documentation files

```

## Workflow

### 1. Edit Haskell Specification
```bash
# Edit the specification
vim haskell/src/PCI_MMIO.lhs

# Test in ghci (optional)
cd haskell/src
ghci PCI_MMIO.lhs
```

### 2. Generate Isabelle Theory
```bash
# From project root
./run_translator.sh skel.txt
```

This translates `haskell/src/PCI_MMIO.lhs` → `design/PCI_MMIO_H.thy`

### 3. Build and Verify
```bash
isabelle build -d . c_02_pci
```
## Quick Commands

```bash
# View Haskell spec
cat haskell/src/PCI_MMIO.lhs

# Regenerate and verify
./run_translator.sh skel.txt && isabelle build -d . c_02_pci

# Interactive development
isabelle jedit -d . -R c_02_pci
```


