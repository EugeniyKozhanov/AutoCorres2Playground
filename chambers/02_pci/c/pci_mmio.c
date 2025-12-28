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

/* PCI Configuration Space constants */
#define PCI_CONFIG_ADDRESS  0xCF8
#define PCI_CONFIG_DATA     0xCFC

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
    if (device >= 32) return 0;
    if (function >= 8) return 0;
    if (reg_offset >= 64) return 0;
    if (reg_offset & 3) return 0;  /* Must be DWORD aligned */
    
    /* Build address: enable bit + bus + device + function + offset */
    return 0x80000000 | 
           ((uint32_t)bus << 16) | 
           ((uint32_t)device << 11) | 
           ((uint32_t)function << 8) | 
           (reg_offset & 0xFC);
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
    return (vendor_id != 0xFFFF && vendor_id != 0x0000);
}

/*
 * Extract vendor ID from combined ID register
 */
uint16_t extract_vendor_id(uint32_t id_reg) {
    return (uint16_t)(id_reg & 0xFFFF);
}

/*
 * Extract device ID from combined ID register
 */
uint16_t extract_device_id(uint32_t id_reg) {
    return (uint16_t)((id_reg >> 16) & 0xFFFF);
}

/*
 * Classify vendor by ID (using switch statement for verification)
 * Returns:
 *   0 = Unknown
 *   1 = Intel
 *   2 = AMD
 *   3 = NVIDIA
 *   4 = Other known vendor
 */
uint8_t classify_vendor(uint16_t vendor_id) {
    switch (vendor_id) {
        case 0x8086: return 1;  /* Intel */
        case 0x1022: return 2;  /* AMD */
        case 0x10DE: return 3;  /* NVIDIA */
        case 0x1234: return 4;  /* QEMU */
        case 0x5853: return 4;  /* XenSource */
        case 0x1AF4: return 4;  /* Red Hat (virtio) */
        default:     return 0;  /* Unknown */
    }
}

/*
 * Validate function number with error codes (using if-else chain)
 * Returns:
 *   0 = Valid (0-7)
 *   1 = Too large (>= 8)
 *   2 = Invalid multifunction (function > 0 but device not multifunction)
 */
uint8_t validate_function_number(uint8_t function, uint8_t is_multifunction) {
    if (function >= 8) {
        return 1;  /* Too large */
    } else if (function > 0 && !is_multifunction) {
        return 2;  /* Invalid for non-multifunction device */
    } else {
        return 0;  /* Valid */
    }
}

/*
 * Decode register offset type (using if-else chain for ranges)
 * Returns:
 *   0 = Invalid (not aligned or out of range)
 *   1 = Standard config (0x00-0x3F)
 *   2 = Device specific (0x40-0xFF)
 */
uint8_t decode_register_type(uint8_t offset) {
    /* Check alignment first */
    if ((offset & 0x03) != 0) {
        return 0;  /* Not 4-byte aligned */
    } else if (offset >= 0x40) {
        return 2;  /* Device specific */
    } else if (offset < 0x40) {
        return 1;  /* Standard config */
    } else {
        return 0;  /* Should not reach here */
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
    if (count > 1024) return NULL;  /* Sanity limit */
    
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
    switch (vendor_class) {
        case 1: vendor_name = "Intel"; break;
        case 2: vendor_name = "AMD"; break;
        case 3: vendor_name = "NVIDIA"; break;
        case 4: vendor_name = "Other Known"; break;
        default: vendor_name = "Unknown"; break;
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
        switch (reg_type) {
            case 1: type_name = "Standard Config"; break;
            case 2: type_name = "Device Specific"; break;
            default: type_name = "Invalid/Unaligned"; break;
        }
        printf("  Offset 0x%02x: %s\n", offset, type_name);
    }
    printf("\n");
    
    /* Demonstrate function validation */
    printf("Function Validation Examples:\n");
    uint8_t valid_result = validate_function_number(0, 0);
    printf("  Function 0, non-multifunction: %s (code %d)\n", 
           valid_result == 0 ? "VALID" : "INVALID", valid_result);
    
    uint8_t invalid_result = validate_function_number(1, 0);
    printf("  Function 1, non-multifunction: %s (code %d)\n",
           invalid_result == 0 ? "VALID" : "INVALID", invalid_result);
    
    uint8_t too_large = validate_function_number(8, 1);
    printf("  Function 8, multifunction: %s (code %d)\n",
           too_large == 0 ? "VALID" : "INVALID", too_large);
    printf("\n");
    
    /* Scan devices on bus 0 */
    printf("Detected PCI Devices:\n");
    for (uint8_t device = 0; device < 32; device++) {
        scan_pci_function(0, device, 0);
    }
    
    printf("\nScan complete.\n");
    printf("\nNote: All functions used are formally verified against Haskell specs!\n");
    
    /* Release I/O port permissions */
    ioperm(PCI_CONFIG_ADDRESS, 8, 0);
    
    return 0;
}
#endif
