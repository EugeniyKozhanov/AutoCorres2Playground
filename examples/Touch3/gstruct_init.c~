// repo/seL4/include/stdint.h"

typedef unsigned char uint8_t;
typedef unsigned short uint16_t;
typedef unsigned int uint32_t;
typedef unsigned long long uint64_t;
 
typedef signed char int8_t;
typedef signed short int16_t;
typedef signed int int32_t;
typedef signed long long int64_t;

// "repo/seL4/include/arch/arm/arch/machine/gic_v2.h"
/* Helpers for VGIC */
/* Memory map for GIC distributor */
struct gic_dist_map {
    uint32_t enable; /* 0x000 */
    uint32_t ic_type; /* 0x004 */
    uint32_t dist_ident; /* 0x008 */
    uint32_t res1[29]; /* [0x00C, 0x080) */

    uint32_t security[32]; /* [0x080, 0x100) */

    uint32_t enable_set[32]; /* [0x100, 0x180) */
    uint32_t enable_clr[32]; /* [0x180, 0x200) */
    uint32_t pending_set[32]; /* [0x200, 0x280) */
    uint32_t pending_clr[32]; /* [0x280, 0x300) */
    uint32_t active[32]; /* [0x300, 0x380) */
    uint32_t res2[32]; /* [0x380, 0x400) */

    uint32_t priority[255]; /* [0x400, 0x7FC) */
    uint32_t res3; /* 0x7FC */

    uint32_t targets[255]; /* [0x800, 0xBFC) */
    uint32_t res4; /* 0xBFC */

    uint32_t config[64]; /* [0xC00, 0xD00) */

    uint32_t spi[32]; /* [0xD00, 0xD80) */
    uint32_t res5[20]; /* [0xD80, 0xDD0) */
    uint32_t res6; /* 0xDD0 */
    uint32_t legacy_int; /* 0xDD4 */
    uint32_t res7[2]; /* [0xDD8, 0xDE0) */
    uint32_t match_d; /* 0xDE0 */
    uint32_t enable_d; /* 0xDE4 */
    uint32_t res8[70]; /* [0xDE8, 0xF00) */

    uint32_t sgi_control; /* 0xF00 */
    uint32_t res9[3]; /* [0xF04, 0xF10) */
    uint32_t sgi_pending_clr[4]; /* [0xF10, 0xF20) */
    uint32_t res10[40]; /* [0xF20, 0xFC0) */

    uint32_t periph_id[12]; /* [0xFC0, 0xFF0) */
    uint32_t component_id[4]; /* [0xFF0, 0xFFF] */
};

extern volatile struct gic_dist_map *const gic_dist;

volatile struct gic_dist_map *const gic_dist =
    (volatile struct gic_dist_map *)((0xfff00000ul + 0x1000));    

/* Wrapping an int literal such as 0 or 1 in a function to prevent it from being
   simplified away in verification while still allowing the compiler to optimise
   it out and do code elimination on the result. */
static inline int wrap_config_set(int x)
{
    return x;
}


static void cpu_iface_init(void)
{   
    uint32_t i;

    /* For non-Exynos4, the registers are banked per CPU, need to clear them */
    gic_dist->enable_clr[0]  = 0xffffffff;
    gic_dist->pending_clr[0] = 0xffffffff;
    
    /* put everything in group 0; group 1 if in hyp mode */
    
    // original if (config_set(CONFIG_ARM_HYPERVISOR_SUPPORT) && !config_set(CONFIG_PLAT_QEMU_ARM_VIRT)) 
    // but we have to work after preprocessing
    if (wrap_config_set(0)) {
        gic_dist->security[0] = 0xffffffff;
        gic_dist->priority[0] = 0x80808080;
    }
}

void cpu_initLocalIRQController(void)
{
    cpu_iface_init();
}
