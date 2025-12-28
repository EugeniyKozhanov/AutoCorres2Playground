theory PCI_MMIO_H
imports 
  "AutoCorres2_Main.AutoCorres_Main"
begin

install_C_file "../c/pci_mmio.i"

autocorres [
  ts_rules = nondet,
  heap_abs_syntax
] "pci_mmio.i"

#INCLUDE_HASKELL PCI_MMIO.lhs

text \<open>Additional specifications not handled by Haskell translator\<close>

definition
extractVendorId_spec :: "word32 \<Rightarrow> vendor_id"
where
"extractVendorId_spec reg \<equiv> ucast (reg && 0xFFFF)"

definition
extractDeviceId_spec :: "word32 \<Rightarrow> device_id"
where
"extractDeviceId_spec reg \<equiv> ucast ((reg >> 16) && 0xFFFF)"

definition
makePCIAddress_spec :: "bus \<Rightarrow> device \<Rightarrow> pci_function \<Rightarrow> register_offset \<Rightarrow> pciaddress"
where
"makePCIAddress_spec bus dev func offset \<equiv>
  if \<not>validDevice dev \<or> \<not>validFunction func \<or> 
     \<not>validRegisterOffset offset \<or> \<not>alignedRegisterOffset offset
  then 0
  else 0x80000000 || (ucast bus << 16) || (ucast dev << 11) || 
       (ucast func << 8) || (ucast offset && 0xFC)"

end
