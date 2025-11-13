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


lemma
  "\<lbrakk> IS_VALID(gic_dist_map_C) s gic_dist \<rbrakk> \<Longrightarrow>
     cpu_iface_init' \<bullet> s
   \<lbrace> \<lambda> Res _ s.  enable_clr_C (heap_gic_dist_map_C s gic_dist).[0] = 0xFFFFFFFF \<rbrace> "
  unfolding cpu_iface_init'_def cpu_initLocalIRQController'_def
  apply runs_to_vcg
  done

end  (* cpu_initLocalIRQController *)

end

