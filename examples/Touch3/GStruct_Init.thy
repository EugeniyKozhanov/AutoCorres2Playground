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
    scope = cpu_initLocalIRQController
    ] "gstruct_init.c"


context ts_definition_cpu_initLocalIRQController begin

find_theorems name:update'_def


lemma update_modifies_aa_false:
  assumes VALID: "ptr_valid (heap_typing s) p"
  shows
" \<lbrakk> wrap_config_set'  \<bullet> s
                  \<lbrace> \<lambda>ret s'. ret = Result 0 \<rbrace> \<rbrakk>    \<Longrightarrow>
    update' p \<bullet> s
       \<lbrace> \<lambda>_ s'. heap_test_t_C s' p =

                 bb_C_update (\<lambda>_. 7) (heap_test_t_C s p)  \<rbrace>"
  using VALID
  unfolding update'_def
  apply runs_to_vcg
  apply (clarsimp simp: wrap_config_set'_def)
  (* apply runs_to_vcg // uncomment this in config == 0 case *)
  done


lemma update_modifies_aa_true:
  assumes VALID: "ptr_valid (heap_typing s) p"
  shows
" \<lbrakk> wrap_config_set'  \<bullet> s
                  \<lbrace> \<lambda>ret s'. ret = Result 1 \<rbrace> \<rbrakk>    \<Longrightarrow>
    update' p \<bullet> s
       \<lbrace> \<lambda>_ s'. heap_test_t_C s' p =
                 ( bb_C_update (\<lambda>_. 7) (aa_C_update (\<lambda>_. 5) (heap_test_t_C s p)))  \<rbrace>"
  using VALID
  unfolding update'_def
  apply runs_to_vcg
  apply (clarsimp simp: wrap_config_set'_def)
  apply runs_to_vcg
  done

end  (* cpu_initLocalIRQController *)

end

