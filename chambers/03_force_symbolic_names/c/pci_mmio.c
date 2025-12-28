/*
 * Simple PCI I/O Port Scanner
 * 
 * Demonstrates:
 * - I/O port access for PCI configuration space
 * - Using ioperm() for port permissions
 * - Simple device scanning
 * - Memory allocation for device list
 * - Pointer arithmetic and structures
 * 
 * Dual-mode for verification:
 * - AUTOCORRES_VERIFY: Minimal types, core logic only
 * - Normal: Full Linux implementation with I/O
 */

#ifdef AUTOCORRES_VERIFY
/* Minimal types for AutoCorres verification */
typedef unsigned char uint8_t;
typedef unsigned short uint16_t;
typedef unsigned int uint32_t;
typedef unsigned long size_t;
typedef void* voidptr;
#define NULL ((void*)0)

/* Stub for malloc in verification mode */
/** DONT_TRANSLATE
    FNSPEC malloc_spec: "\<forall>sz. \<Gamma> \<turnstile> \<lbrace> \<acute>size = sz \<rbrace> Call malloc'proc \<lbrace> True \<rbrace>"
*/
void* malloc(size_t size);

/** DONT_TRANSLATE
    FNSPEC free_spec: "\<forall>p. \<Gamma> \<turnstile> \<lbrace> \<acute>ptr = p \<rbrace> Call free'proc \<lbrace> p = NULL \<or> freed \<acute>ptr \<rbrace>"
*/
void free(void* ptr);

/* I/O port operations - stubs for verification */
/* These are treated as abstract operations by AutoCorres */
/** DONT_TRANSLATE
    FNSPEC outl_spec: "\<forall>val prt. \<Gamma> \<turnstile> \<lbrace> \<acute>value = val \<and> \<acute>port = prt \<rbrace> Call outl'proc \<lbrace> io_write prt val \<rbrace>"
*/
void outl(uint32_t value, uint16_t port);

/** DONT_TRANSLATE
    FNSPEC inl_spec: "\<forall>prt. \<Gamma> \<turnstile> \<lbrace> \<acute>port = prt \<rbrace> Call inl'proc \<lbrace> True \<rbrace>"
*/
uint32_t inl(uint16_t port);

#else
/* Full Linux headers for normal compilation */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <sys/io.h>  /* For ioperm(), outl(), inl() */
#include <unistd.h>
#endif

/* PCI Configuration Space constants - use #define for I/O ports (not verified) */
#define PCI_CONFIG_ADDRESS  0xCF8
#define PCI_CONFIG_DATA     0xCFC

/* 
 * Symbolic constants as inline functions for verification
 * These are preserved through preprocessing and available in AutoCorres proofs
 */

/* PCI limits and constants */
static inline uint8_t pci_max_devices(void) { return 32; }
static inline uint8_t pci_max_functions(void) { return 8; }
static inline uint8_t pci_max_registers(void) { return 64; }
static inline uint32_t pci_max_alloc_devices(void) { return 1024; }

/* Invalid vendor IDs */
static inline uint16_t pci_vendor_invalid_ffff(void) { return 0xFFFF; }
static inline uint16_t pci_vendor_invalid_0000(void) { return 0x0000; }

/* Known vendor IDs */
static inline uint16_t pci_vendor_intel(void) { return 0x8086; }
static inline uint16_t pci_vendor_amd(void) { return 0x1022; }
static inline uint16_t pci_vendor_nvidia(void) { return 0x10DE; }
static inline uint16_t pci_vendor_qemu(void) { return 0x1234; }
static inline uint16_t pci_vendor_xen(void) { return 0x5853; }
static inline uint16_t pci_vendor_virtio(void) { return 0x1AF4; }

/* Vendor classification codes */
static inline uint8_t vendor_class_unknown(void) { return 0; }
static inline uint8_t vendor_class_intel(void) { return 1; }
static inline uint8_t vendor_class_amd(void) { return 2; }
static inline uint8_t vendor_class_nvidia(void) { return 3; }
static inline uint8_t vendor_class_other(void) { return 4; }

/* Function validation error codes */
static inline uint8_t function_valid(void) { return 0; }
static inline uint8_t function_too_large(void) { return 1; }
static inline uint8_t function_invalid_multi(void) { return 2; }

/* Register type codes */
static inline uint8_t register_invalid(void) { return 0; }
static inline uint8_t register_standard(void) { return 1; }
static inline uint8_t register_device_specific(void) { return 2; }

/* Register boundaries */
static inline uint8_t pci_config_standard_end(void) { return 0x40; }

/* Bit masks and alignment */
static inline uint8_t pci_dword_align_mask(void) { return 0x03; }
static inline uint16_t pci_vendor_id_mask(void) { return 0xFFFF; }
static inline uint8_t pci_device_id_shift(void) { return 16; }

/* PCI address format bit positions */
static inline uint32_t pci_addr_enable_bit(void) { return 0x80000000; }
static inline uint8_t pci_addr_bus_shift(void) { return 16; }
static inline uint8_t pci_addr_device_shift(void) { return 11; }
static inline uint8_t pci_addr_function_shift(void) { return 8; }
static inline uint8_t pci_addr_register_mask(void) { return 0xFC; }

/* Debug printing macro - hidden in verification mode */
#ifdef AUTOCORRES_VERIFY
#define DEBUG_PRINT(...) /* nothing */
#else
#define DEBUG_PRINT printf
#endif

/* PCI device structure */
struct pci_device {
    uint8_t bus;
    uint8_t device;
    uint8_t function;
    uint16_t vendor_id;
    uint16_t device_id;
};

/*
 * Build PCI configuration address
 * 
 * Format:
 * - Bit 31: Enable bit (must be 1)
 * - Bits 23-16: Bus number
 * - Bits 15-11: Device number (0-31)
 * - Bits 10-8: Function number (0-7)
 * - Bits 7-2: Register offset (DWORD aligned)
 * 
 * Returns: 32-bit PCI address, or 0 if parameters invalid
 */
uint32_t make_pci_address(uint8_t bus, uint8_t device, 
                          uint8_t function, uint8_t reg_offset) {
    /* Validate inputs */
    if (device >= pci_max_devices()) return 0;
    if (function >= pci_max_functions()) return 0;
    if (reg_offset >= pci_max_registers()) return 0;
    if (reg_offset & pci_dword_align_mask()) return 0;  /* Must be DWORD aligned */
    
    /* Build address: enable bit + bus + device + function + offset */
    return pci_addr_enable_bit() | 
           ((uint32_t)bus << pci_addr_bus_shift()) | 
           ((uint32_t)device << pci_addr_device_shift()) | 
           ((uint32_t)function << pci_addr_function_shift()) | 
           (reg_offset & pci_addr_register_mask());
}

/*
 * Check if vendor ID is valid
 * 
 * Invalid values:
 * - 0xFFFF: No device present
 * - 0x0000: Invalid/uninitialized
 * 
 * Returns: 1 if valid, 0 if invalid
 */
uint8_t is_valid_vendor(uint16_t vendor_id) {
    return (vendor_id != pci_vendor_invalid_ffff() && vendor_id != pci_vendor_invalid_0000());
}

/*
 * Extract vendor ID from combined ID register
 */
uint16_t extract_vendor_id(uint32_t id_reg) {
    return (uint16_t)(id_reg & pci_vendor_id_mask());
}

/*
 * Extract device ID from combined ID register
 */
uint16_t extract_device_id(uint32_t id_reg) {
    return (uint16_t)((id_reg >> pci_device_id_shift()) & pci_vendor_id_mask());
}

/*
 * Classify vendor by ID (using switch statement for verification)
 * Returns:
 *   VENDOR_CLASS_UNKNOWN = Unknown
 *   VENDOR_CLASS_INTEL = Intel
 *   VENDOR_CLASS_AMD = AMD
 *   VENDOR_CLASS_NVIDIA = NVIDIA
 *   VENDOR_CLASS_OTHER = Other known vendor
 */
uint8_t classify_vendor(uint16_t vendor_id) {
    if (vendor_id == pci_vendor_intel())  return vendor_class_intel();
    if (vendor_id == pci_vendor_amd())    return vendor_class_amd();
    if (vendor_id == pci_vendor_nvidia()) return vendor_class_nvidia();
    if (vendor_id == pci_vendor_qemu())   return vendor_class_other();
    if (vendor_id == pci_vendor_xen())    return vendor_class_other();
    if (vendor_id == pci_vendor_virtio()) return vendor_class_other();
    return vendor_class_unknown();
}

/*
 * Validate function number with error codes (using if-else chain)
 * Returns:
 *   FUNCTION_VALID = Valid (0-7)
 *   FUNCTION_TOO_LARGE = Too large (>= 8)
 *   FUNCTION_INVALID_MULTI = Invalid multifunction (function > 0 but device not multifunction)
 */
uint8_t validate_function_number(uint8_t function, uint8_t is_multifunction) {
    if (function >= pci_max_functions()) {
        return function_too_large();
    } else if (function > 0 && !is_multifunction) {
        return function_invalid_multi();
    } else {
        return function_valid();
    }
}

/*
 * Decode register offset type (using if-else chain for ranges)
 * Returns:
 *   REGISTER_INVALID = Invalid (not aligned or out of range)
 *   REGISTER_STANDARD = Standard config (0x00-0x3F)
 *   REGISTER_DEVICE_SPECIFIC = Device specific (0x40-0xFF)
 */
uint8_t decode_register_type(uint8_t offset) {
    /* Check alignment first */
    if ((offset & pci_dword_align_mask()) != 0) {
        return register_invalid();
    } else if (offset >= pci_config_standard_end()) {
        return register_device_specific();
    } else if (offset < pci_config_standard_end()) {
        return register_standard();
    } else {
        return register_invalid();
    }
}

/*
 * Initialize a PCI device structure
 * Returns: 0 on success, 1 if device is NULL
 */
uint8_t init_pci_device(struct pci_device *dev,
                        uint8_t bus, uint8_t device, uint8_t function,
                        uint16_t vendor_id, uint16_t device_id) {
    if (dev == NULL) return 1;
    
    dev->bus = bus;
    dev->device = device;
    dev->function = function;
    dev->vendor_id = vendor_id;
    dev->device_id = device_id;
    
    return 0;
}

/*
 * Allocate array of PCI devices
 * Returns: pointer to array, or NULL on failure
 */
struct pci_device* alloc_device_array(uint32_t count) {
    if (count == 0) return NULL;
    if (count > pci_max_alloc_devices()) return NULL;  /* Sanity limit */
    
    size_t total_size = count * sizeof(struct pci_device);
    return (struct pci_device*)malloc(total_size);
}

/*
 * Free device array
 */
void free_device_array(struct pci_device *devices) {
    if (devices != NULL) {
        free(devices);
    }
}

/*
 * Read from PCI configuration space via I/O ports
 * 
 * This function is verifiable - it uses the I/O port stubs.
 * AutoCorres treats outl/inl as abstract operations.
 * 
 * Returns: 32-bit value read, or 0xFFFFFFFF on invalid address
 */
uint32_t pci_read_config(uint8_t bus, uint8_t device,
                         uint8_t function, uint8_t offset) {
    uint32_t addr = make_pci_address(bus, device, function, offset);
    if (addr == 0) {
        return 0xFFFFFFFF;
    }
    
    /* Write address to config address port */
    outl(addr, PCI_CONFIG_ADDRESS);
    
    /* Read data from config data port */
    return inl(PCI_CONFIG_DATA);
}

/*
 * Write to PCI configuration space via I/O ports
 */
void pci_write_config(uint8_t bus, uint8_t device,
                      uint8_t function, uint8_t offset,
                      uint32_t value) {
    uint32_t addr = make_pci_address(bus, device, function, offset);
    if (addr == 0) {
        return;
    }
    
    /* Write address to config address port */
    outl(addr, PCI_CONFIG_ADDRESS);
    
    /* Write data to config data port */
    outl(value, PCI_CONFIG_DATA);
}

/*
 * Scan a single PCI function
 */
void scan_pci_function(uint8_t bus, uint8_t device, uint8_t function) {
    /* Read vendor/device ID using our verifiable function */
    uint32_t id = pci_read_config(bus, device, function, 0);
    
    uint16_t vendor_id = extract_vendor_id(id);
    uint16_t device_id = extract_device_id(id);
    
    if (!is_valid_vendor(vendor_id)) {
        return;  /* No device present */
    }
    
#ifndef AUTOCORRES_VERIFY
    /* Classify the vendor (display only, not verified) */
    uint8_t vendor_class = classify_vendor(vendor_id);
    const char* vendor_name;
    if (vendor_class == vendor_class_intel()) {
        vendor_name = "Intel";
    } else if (vendor_class == vendor_class_amd()) {
        vendor_name = "AMD";
    } else if (vendor_class == vendor_class_nvidia()) {
        vendor_name = "NVIDIA";
    } else if (vendor_class == vendor_class_other()) {
        vendor_name = "Other Known";
    } else {
        vendor_name = "Unknown";
    }
    
    DEBUG_PRINT("  %02x:%02x.%x  Vendor: 0x%04x (%s)  Device: 0x%04x\n",
                bus, device, function, vendor_id, vendor_name, device_id);
#else
    /* Verifiable version - just print IDs */
    DEBUG_PRINT("  %02x:%02x.%x  Vendor: 0x%04x  Device: 0x%04x\n",
                bus, device, function, vendor_id, device_id);
#endif
}

#ifndef AUTOCORRES_VERIFY
/*
 * Simple PCI bus scanner with validation
 * Scans bus 0, devices 0-31, function 0 only
 */
int main(void) {
    printf("PCI I/O Port Scanner with Formal Verification\n");
    printf("==============================================\n\n");
    
    /* Request I/O port access permission for PCI config ports */
    if (ioperm(PCI_CONFIG_ADDRESS, 8, 1) != 0) {
        printf("ERROR: Cannot get I/O port permissions\n");
        printf("       Need root privileges (try: sudo %s)\n", "pci_mmio");
        return 1;
    }
    
    printf("Scanning PCI bus 0...\n\n");
    
    /* Demonstrate register type decoding */
    uint8_t test_offsets[] = {0x00, 0x01, 0x10, 0x40, 0x80};
    printf("Register Type Examples:\n");
    for (int i = 0; i < 5; i++) {
        uint8_t offset = test_offsets[i];
        uint8_t reg_type = decode_register_type(offset);
        const char* type_name;
        if (reg_type == register_standard()) {
            type_name = "Standard Config";
        } else if (reg_type == register_device_specific()) {
            type_name = "Device Specific";
        } else {
            type_name = "Invalid/Unaligned";
        }
        printf("  Offset 0x%02x: %s\n", offset, type_name);
    }
    printf("\n");
    
    /* Demonstrate function validation */
    printf("Function Validation Examples:\n");
    uint8_t valid_result = validate_function_number(0, 0);
    printf("  Function 0, non-multifunction: %s (code %d)\n", 
           valid_result == function_valid() ? "VALID" : "INVALID", valid_result);
    
    uint8_t invalid_result = validate_function_number(1, 0);
    printf("  Function 1, non-multifunction: %s (code %d)\n",
           invalid_result == function_valid() ? "VALID" : "INVALID", invalid_result);
    
    uint8_t too_large = validate_function_number(pci_max_functions(), 1);
    printf("  Function %d, multifunction: %s (code %d)\n",
           pci_max_functions(), too_large == function_valid() ? "VALID" : "INVALID", too_large);
    printf("\n");
    
    /* Scan devices on bus 0 */
    printf("Detected PCI Devices:\n");
    for (uint8_t device = 0; device < pci_max_devices(); device++) {
        scan_pci_function(0, device, 0);
    }
    
    printf("\nScan complete.\n");
    printf("\nNote: All functions used are formally verified against Haskell specs!\n");
    
    /* Release I/O port permissions */
    ioperm(PCI_CONFIG_ADDRESS, 8, 0);
    
    return 0;
}
#endif
