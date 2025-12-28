----------------------------------------------------------------------
PCI MMIO Specification (Minimal for Translator)
----------------------------------------------------------------------

This version provides only the absolute minimum needed by the translator,
with Isabelle specifications defined separately.

----------------------------------------------------------------------

> module PCI_MMIO where
> import Data.Word
> import Data.Bits

----------------------------------------------------------------------
Type Definitions (Translator will convert these)
----------------------------------------------------------------------

> type Bus = Word8
> type Device = Word8  
> type PciFunction = Word8
> type RegisterOffset = Word8
> type VendorId = Word16
> type DeviceId = Word16
> type PCIAddress = Word32

----------------------------------------------------------------------
Constants (Simple values - translator handles these well)
----------------------------------------------------------------------

> maxDevices :: Word8
> maxDevices = 32

> maxFunctions :: Word8
> maxFunctions = 8

> maxRegisters :: Word8
> maxRegisters = 64

> invalidVendorFFFF :: VendorId
> invalidVendorFFFF = 0xFFFF

> invalidVendorZero :: VendorId
> invalidVendorZero = 0x0000

----------------------------------------------------------------------
Symbolic Vendor IDs
----------------------------------------------------------------------

> pciVendorIntel :: VendorId
> pciVendorIntel = 0x8086

> pciVendorAMD :: VendorId
> pciVendorAMD = 0x1022

> pciVendorNVIDIA :: VendorId
> pciVendorNVIDIA = 0x10DE

> pciVendorQEMU :: VendorId
> pciVendorQEMU = 0x1234

> pciVendorXen :: VendorId
> pciVendorXen = 0x5853

> pciVendorVirtio :: VendorId
> pciVendorVirtio = 0x1AF4

----------------------------------------------------------------------
Symbolic Vendor Classes
----------------------------------------------------------------------

> vendorClassUnknown :: VendorClass
> vendorClassUnknown = 0

> vendorClassIntel :: VendorClass
> vendorClassIntel = 1

> vendorClassAMD :: VendorClass
> vendorClassAMD = 2

> vendorClassNVIDIA :: VendorClass
> vendorClassNVIDIA = 3

> vendorClassOther :: VendorClass
> vendorClassOther = 4

----------------------------------------------------------------------
Simple Boolean Functions (These translate cleanly)
----------------------------------------------------------------------

> validDevice :: Device -> Bool
> validDevice d = d < maxDevices

> validFunction :: PciFunction -> Bool
> validFunction f = f < maxFunctions

> validRegisterOffset :: RegisterOffset -> Bool
> validRegisterOffset r = r < maxRegisters

> alignedRegisterOffset :: RegisterOffset -> Bool
> alignedRegisterOffset r = (r .&. 3) == 0

> isValidVendor :: VendorId -> Bool
> isValidVendor vid = vid /= invalidVendorFFFF && vid /= invalidVendorZero

----------------------------------------------------------------------
Memory Allocation Specifications
----------------------------------------------------------------------

> type DeviceCount = Word32

> maxAllowedDevices :: DeviceCount
> maxAllowedDevices = 1024

> validDeviceCount :: DeviceCount -> Bool
> validDeviceCount count = count > 0 && count <= maxAllowedDevices

> shouldAllocateSucceed :: DeviceCount -> Bool
> shouldAllocateSucceed count = validDeviceCount count

> shouldReturnNull :: DeviceCount -> Bool
> shouldReturnNull count = count == 0 || count > maxAllowedDevices

----------------------------------------------------------------------
Vendor Classification
----------------------------------------------------------------------

> type VendorClass = Word8

> classifyVendor :: VendorId -> VendorClass
> classifyVendor vid
>   | vid == pciVendorIntel  = vendorClassIntel
>   | vid == pciVendorAMD    = vendorClassAMD
>   | vid == pciVendorNVIDIA = vendorClassNVIDIA
>   | vid == pciVendorQEMU   = vendorClassOther
>   | vid == pciVendorXen    = vendorClassOther
>   | vid == pciVendorVirtio = vendorClassOther
>   | otherwise              = vendorClassUnknown

----------------------------------------------------------------------
Function Number Validation
----------------------------------------------------------------------

> type ValidationResult = Word8

> validateFunctionNumber :: PciFunction -> Word8 -> ValidationResult
> validateFunctionNumber func isMulti
>   | func >= 8 = 1                    -- Too large
>   | func > 0 && isMulti == 0 = 2     -- Invalid for non-multifunction
>   | otherwise = 0                    -- Valid

----------------------------------------------------------------------
Register Type Decoding
----------------------------------------------------------------------

> type RegisterType = Word8

> decodeRegisterType :: RegisterOffset -> RegisterType
> decodeRegisterType offset
>   | (offset .&. 0x03) /= 0 = 0  -- Not aligned
>   | offset >= 0x40 = 2          -- Device specific
>   | offset < 0x40 = 1           -- Standard config
>   | otherwise = 0               -- Should not reach

----------------------------------------------------------------------
