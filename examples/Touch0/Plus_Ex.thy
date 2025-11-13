(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)


theory Plus_Ex
imports
  "AutoCorres2_Main.AutoCorres_Main"
begin

install_C_file "plus.c"

find_theorems name:plus2

autocorres [ts_force nondet = plus2] "plus.c"

context ts_definition_plus1 begin


find_theorems name:plus1
find_theorems name:plus2

thm plus1'_def
(* 3 + 2 should be 5 *)
lemma "plus1' 3 2 = 5"
  unfolding plus1'_def
  by eval

(* plus does what it says on the box *)
lemma plus_correct: "plus1' a b = a + b"
  unfolding plus1'_def
  apply (rule refl)
  done

end

(* Compare pre-lifting to post-lifting *)
context plus_all_corres 
begin
thm plus2_body_def
thm plus2'_def
end

lemmas runs_to_whileLoop2 =  runs_to_whileLoop_res' [split_tuple C and B arity: 2]

(* plus2 does what it says on the box *)
lemma (in ts_definition_plus2) plus2_correct: "plus2' a b \<bullet> s \<lbrace> \<lambda>r s. r = Result (a + b)\<rbrace>"
  unfolding plus2'_def
  apply (runs_to_vcg)
  apply (rule runs_to_whileLoop2 [
    where I="\<lambda>(a', b') s. a' + b' = a + b"
      and R="measure (\<lambda>((a', b'), s). unat b')"])
     by (auto simp: not_less measure_unat)

(* plus2 does what it says on plus's box *)
lemma (in plus_all_impl) plus2_is_plus: "plus2' a b \<bullet> s\<lbrace> \<lambda>r s. r = Result (plus1' a b )\<rbrace>"
  unfolding plus1'_def
  supply plus2_correct[runs_to_vcg]
  apply runs_to_vcg
  done

(* Prove plus2 with no failure *)
lemma (in ts_definition_plus2) plus2_valid:"plus2' a b \<bullet> s \<lbrace> \<lambda>r s. r = Result (a + b) \<rbrace>"
  unfolding plus2'_def
  apply (runs_to_vcg)
  apply (rule runs_to_whileLoop2 [
    where I="\<lambda>(a', b') s. a' + b' = a + b"
      and R="measure (\<lambda>((a', b'), s). unat b')"])
  by (auto simp: not_less measure_unat)

end

