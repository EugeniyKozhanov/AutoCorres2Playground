CC = gcc
CFLAGS = -Wall -Wextra -O2

.PHONY: all clean run preprocess test

all: pci_mmio

pci_mmio: pci_mmio.c
	$(CC) $(CFLAGS) -o pci_mmio pci_mmio.c

run: pci_mmio
	@echo "Note: Requires root privileges to access /dev/mem"
	@echo "Running with sudo..."
	sudo ./pci_mmio

preprocess: pci_mmio.c insert_fnspec.py
	@echo "Preprocessing C code..."
	@$(CC) -DAUTOCORRES_VERIFY -E -P $(CFLAGS) pci_mmio.c -o pci_mmio.i.tmp
	@echo "Inserting FNSPEC annotations as axioms..."
	@python3 insert_fnspec.py pci_mmio.c pci_mmio.i.tmp pci_mmio.i
	@rm -f pci_mmio.i.tmp
	@echo "Generated: pci_mmio.i with FNSPEC axioms ($$(wc -l < pci_mmio.i) lines)"

test: pci_mmio preprocess
	@echo "=== Normal build: OK ==="
	@echo "=== Preprocessed lines: ===" 
	@wc -l pci_mmio.i
	@echo "=== Ready for verification ==="

clean:
	rm -f pci_mmio pci_mmio.i pci_scan pci_scan.i
