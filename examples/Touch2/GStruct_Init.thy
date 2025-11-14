(*
 * SPDX-License-Identifier: BSD-2-Clause
 *)


theory GStruct_Init
imports
  "AutoCorres2_Main.AutoCorres_Main"
begin

install_C_file "gstruct_init.c"


autocorres [
    ts_rules = nondet,
    ignore_addressable_fields_error,
    scope = cpu_initLocalIRQController bar
    ] "gstruct_init.c"


context ts_definition_cpu_initLocalIRQController begin

find_theorems name:cpu_iface_init'_def

find_theorems name:gic_dist_
find_consts name:gic_dist_map

lemma gic_init:
  assumes PRE: 
    "IS_VALID(gic_dist_map_C) s gic_dist 
     \<and> PTR_COERCE(gic_dist_map_C \<rightarrow> unit) gic_dist = PTR(unit) 0xFFF00000"
  shows
     "cpu_initLocalIRQController' \<equiv>
    do {
      guard (\<lambda>s. IS_VALID(gic_dist_map_C) s gic_dist);
      modify
       (heap_gic_dist_map_C_update
         (\<lambda>a. a(gic_dist := enable_clr_C_update (\<lambda>a. Arrays.update a 0 0xFFFFFFFF) (a gic_dist))));
      modify
       (heap_gic_dist_map_C_update
         (\<lambda>a. a(gic_dist := pending_clr_C_update (\<lambda>a. Arrays.update a 0 0xFFFFFFFF) (a gic_dist))));
      ret'int'1 \<leftarrow> wrap_config_set' 0;
      unless (ret'int'1 = 0)
       (do {
          modify
           (heap_gic_dist_map_C_update
             (\<lambda>a. a(gic_dist := security_C_update (\<lambda>a. Arrays.update a 0 0xFFFFFFFF) (a gic_dist))));
          modify
           (heap_gic_dist_map_C_update
             (\<lambda>a. a(gic_dist := priority_C_update (\<lambda>a. Arrays.update a 0 0x80808080) (a gic_dist))))
        })
    } "
  unfolding ts_def .


end  (* cpu_initLocalIRQController *)

end

