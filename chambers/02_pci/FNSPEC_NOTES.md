# FNSPEC Annotations for I/O and Memory Operations

## Overview

Added FNSPEC annotations for abstract operations (malloc, free, outl, inl) in the C source. These annotations define behavioral specifications for functions that AutoCorres treats as primitives.

## FNSPEC Syntax

Based on AutoCorres2 examples (`in_out_parameters.c`):

```c
/** DONT_TRANSLATE
    FNSPEC function_spec: "\<forall>params. \<Gamma> \<turnstile> \<lbrace>precondition\<rbrace> Call function'proc \<lbrace>postcondition\<rbrace>" MODIFIES: state
*/
```

## Annotations Added

### Memory Operations

```c
/** DONT_TRANSLATE
    FNSPEC malloc_spec: "\<forall>sz. \<Gamma> \<turnstile> \<lbrace> \<acute>size = sz \<rbrace> Call malloc'proc \<lbrace> if sz = 0 then \<acute>ret__ptr_to_void = NULL else is_valid_ptr \<acute>ret__ptr_to_void \<and> ptr_size \<acute>ret__ptr_to_void = sz \<rbrace>"
*/
void* malloc(size_t size);

/** DONT_TRANSLATE
    FNSPEC free_spec: "\<forall>p. \<Gamma> \<turnstile> \<lbrace> \<acute>ptr = p \<rbrace> Call free'proc \<lbrace> p = NULL \<or> freed \<acute>ptr \<rbrace>"
*/
void free(void* ptr);
```

### I/O Port Operations

```c
/** DONT_TRANSLATE
    FNSPEC outl_spec: "\<forall>val prt. \<Gamma> \<turnstile> \<lbrace> \<acute>value = val \<and> \<acute>port = prt \<rbrace> Call outl'proc \<lbrace> io_write prt val \<rbrace>" MODIFIES: io_state
*/
void outl(uint32_t value, uint16_t port);

/** DONT_TRANSLATE
    FNSPEC inl_spec: "\<forall>prt. \<Gamma> \<turnstile> \<lbrace> \<acute>port = prt \<rbrace> Call inl'proc \<lbrace> \<acute>ret__unsigned_int = io_read prt \<rbrace>" READS: io_state
*/
uint32_t inl(uint16_t port);
```

## Current Limitation

**FNSPEC annotations are removed during preprocessing** with the `-P` flag (removes all comments).

### Why This Happens

1. `gcc -E -P` strips all comments including `/** DONT_TRANSLATE */`
2. `gcc -E -C` preserves ALL comments, including unwanted system header comments that break parsing
3. AutoCorres C parser needs preprocessed code (to expand macros like `AUTOCORRES_VERIFY`)
4. But FNSPEC must be present in the file that `install_C_file` processes


