(* THIS FILE WAS AUTOMATICALLY GENERATED. DO NOT EDIT. *)
(* instead, see the skeleton file Add_Or_Not_H.thy *)
theory Add_Or_Not_H
imports 
    "AutoCorres2_Main.AutoCorres_Main"
begin

install_C_file "../c/add_or_not.c"

autocorres [
    ts_rules = nondet,
    ignore_addressable_fields_error
    ] "add_or_not.c"


definition
wrap_config_set :: "bool"
where
"wrap_config_set \<equiv> False"

definition
addOrNot :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
"addOrNot a b \<equiv>
  if
  wrap_config_set = True  then a - b
  else if
  wrap_config_set = False then a + b - 3
  else undefined"


end
