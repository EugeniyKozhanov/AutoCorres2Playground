(*
 * Symbolic Names for Universal Proofs
 * 
 * This theory demonstrates how symbolic constants enable platform-independent
 * proofs - inspired by seL4's "next 700 platforms" approach.
 * 
 * KEY PRINCIPLE:
 * - Proofs reference NAMES (pciVendorIntel) not VALUES (0x8086)
 * - Change constants in ONE place, proofs remain valid
 * - Self-documenting code and proofs
 *)

theory PCI_MMIO_Proof
imports PCI_MMIO_H
begin

context pci_mmio_all_corres begin

subsection \<open>Symbolic Names for Universal Proofs\<close>

text \<open>
  Using static inline functions and Haskell constants as symbolic names.
  
  C code uses: if (vendor_id == pci_vendor_intel()) return vendor_class_intel();
  Haskell uses: if vid == pciVendorIntel then vendorClassIntel
  
  Proofs reference symbolic names, making them:
  - Platform-independent (change value in ONE place)
  - Self-documenting (pciVendorIntel vs 0x8086)
  - Maintainable (add new vendor without changing proof structure)
\<close>

text \<open>
  Symbolic constant correspondence - C inline functions match Haskell constants.
  
  Note: We prove C functions equal symbolic constants, NOT hardcoded values.
  The actual values are defined in PCI_MMIO_H.thy definitions.
\<close>

lemma pci_vendor_intel_matches_haskell:
  shows "pci_vendor_intel' \<bullet> s
         \<lbrace> \<lambda>Res r t. t = s \<and> r = pciVendorIntel \<rbrace>"
  unfolding pci_vendor_intel'_def pciVendorIntel_def
  by runs_to_vcg

lemma pci_vendor_amd_matches_haskell:
  shows "pci_vendor_amd' \<bullet> s
         \<lbrace> \<lambda>Res r t. t = s \<and> r = pciVendorAMD \<rbrace>"
  unfolding pci_vendor_amd'_def pciVendorAMD_def
  by runs_to_vcg

lemma vendor_class_intel_matches_haskell:
  shows "vendor_class_intel' \<bullet> s
         \<lbrace> \<lambda>Res r t. t = s \<and> r = vendorClassIntel \<rbrace>"
  unfolding vendor_class_intel'_def vendorClassIntel_def
  by runs_to_vcg

lemma vendor_class_amd_matches_haskell:
  shows "vendor_class_amd' \<bullet> s
         \<lbrace> \<lambda>Res r t. t = s \<and> r = vendorClassAMD \<rbrace>"
  unfolding vendor_class_amd'_def vendorClassAMD_def
  by runs_to_vcg

text \<open>
  classify_vendor using ONLY symbolic names - no hardcoded values in proof!
  
  Compare this to: "classify_vendor' 0x8086 returns 1"
  vs symbolic: "classify_vendor' pci_vendor_intel() returns vendor_class_intel()"
  
  This makes the proof self-documenting and platform-independent.
\<close>

lemma classify_intel_symbolic:
  shows "do {
    vid \<leftarrow> pci_vendor_intel';
    classify_vendor' vid
  } \<bullet> s \<lbrace> \<lambda>Res r t. r = vendorClassIntel \<rbrace>"
  unfolding classify_vendor'_def 
  unfolding pci_vendor_intel'_def pci_vendor_amd'_def pci_vendor_nvidia'_def
  unfolding pci_vendor_qemu'_def pci_vendor_xen'_def pci_vendor_virtio'_def
  unfolding vendor_class_intel'_def vendor_class_amd'_def vendor_class_nvidia'_def
  unfolding vendor_class_other'_def vendor_class_unknown'_def
  unfolding vendorClassIntel_def
  by (runs_to_vcg; simp)

lemma classify_amd_symbolic:
  shows "do {
    vid \<leftarrow> pci_vendor_amd';
    classify_vendor' vid
  } \<bullet> s \<lbrace> \<lambda>Res r t. r = vendorClassAMD \<rbrace>"
  unfolding classify_vendor'_def 
  unfolding pci_vendor_intel'_def pci_vendor_amd'_def pci_vendor_nvidia'_def
  unfolding pci_vendor_qemu'_def pci_vendor_xen'_def pci_vendor_virtio'_def
  unfolding vendor_class_intel'_def vendor_class_amd'_def vendor_class_nvidia'_def
  unfolding vendor_class_other'_def vendor_class_unknown'_def
  unfolding vendorClassAMD_def
  by (runs_to_vcg; simp)

text \<open>
  Haskell spec using symbolic names - proof references names only
\<close>

lemma classify_vendor_intel_haskell:
  shows "classifyVendor pciVendorIntel = vendorClassIntel"
  unfolding classifyVendor_def
  unfolding pciVendorIntel_def pciVendorAMD_def pciVendorNVIDIA_def
  unfolding pciVendorQEMU_def pciVendorXen_def pciVendorVirtio_def
  unfolding vendorClassIntel_def vendorClassAMD_def vendorClassNVIDIA_def
  unfolding vendorClassOther_def vendorClassUnknown_def
  by simp

lemma classify_vendor_amd_haskell:
  shows "classifyVendor pciVendorAMD = vendorClassAMD"
  unfolding classifyVendor_def
  unfolding pciVendorIntel_def pciVendorAMD_def pciVendorNVIDIA_def
  unfolding pciVendorQEMU_def pciVendorXen_def pciVendorVirtio_def
  unfolding vendorClassIntel_def vendorClassAMD_def vendorClassNVIDIA_def
  unfolding vendorClassOther_def vendorClassUnknown_def
  by simp

text \<open>
  Universal theorem using ONLY symbolic names.
  
  If Intel changes their vendor ID from 0x8086 to something else:
  1. Update pci_vendor_intel() function: return NEW_VALUE;
  2. Update pciVendorIntel definition: \<equiv> NEW_VALUE
  3. All proofs remain UNCHANGED!
  
  This is the foundation of seL4's "next 700 platforms" approach.
\<close>

theorem classify_vendor_symbolic_correctness:
  shows "(classifyVendor pciVendorIntel = vendorClassIntel) \<and>
         (classifyVendor pciVendorAMD = vendorClassAMD) \<and>
         (classifyVendor pciVendorNVIDIA = vendorClassNVIDIA)"
  unfolding classifyVendor_def
  unfolding pciVendorIntel_def pciVendorAMD_def pciVendorNVIDIA_def
  unfolding pciVendorQEMU_def pciVendorXen_def pciVendorVirtio_def
  unfolding vendorClassIntel_def vendorClassAMD_def vendorClassNVIDIA_def
  unfolding vendorClassOther_def vendorClassUnknown_def
  by simp

end (* context *)
end (* theory *)
