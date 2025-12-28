theory Add_Or_Not_H
imports 
    "AutoCorres2_Main.AutoCorres_Main"
begin

install_C_file "../c/add_or_not.c"

autocorres [
    ts_rules = nondet,
    ignore_addressable_fields_error
    ] "add_or_not.c"


#INCLUDE_HASKELL API/add_or_not.lhs 

end
