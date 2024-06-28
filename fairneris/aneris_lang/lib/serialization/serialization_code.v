(* (* This file is automatically generated from the OCaml source file *)
(* <repository_root>/ml_sources/aneris_lang/lib/serialization/serialization_code.ml *) *)

(* From fairneris.aneris_lang Require Import ast. *)
(* From fairneris.aneris_lang.lib Require Import list_code. *)
(* From fairneris.aneris_lang.lib Require Import network_util_code. *)

(* Definition int_ser : val := λ: "v", i2s "v". *)

(* Definition int_deser : val := λ: "v", unSOME (s2i "v"). *)

(* Definition int_serializer := *)
(*   {| *)
(*       s_ser := int_ser; *)
(*       s_deser := int_deser; *)
(*   |}. *)

(* Definition bool_ser : val := λ: "v", i2s ((if: "v" *)
(*                                             then  #1 *)
(*                                             else  #0)). *)

(* Definition bool_deser : val := *)
(*   λ: "v", *)
(*   let: "i" := s2i "v" in *)
(*   (if: "i" = (SOME #1) *)
(*    then  #true *)
(*    else  #false). *)

(* Definition bool_serializer := *)
(*   {| *)
(*       s_ser := bool_ser; *)
(*       s_deser := bool_deser; *)
(*   |}. *)

(* Definition unit_ser : val := λ: "_u", #"". *)

(* Definition unit_deser : val := λ: "_s", #(). *)

(* Definition unit_serializer := *)
(*   {| *)
(*       s_ser := unit_ser; *)
(*       s_deser := unit_deser; *)
(*   |}. *)

(* Definition string_ser : val := λ: "x", "x". *)

(* Definition string_deser : val := λ: "x", "x". *)

(* Definition string_serializer := *)
(*   {| *)
(*       s_ser := string_ser; *)
(*       s_deser := string_deser; *)
(*   |}. *)

(* Definition prod_ser (serA : val) (serB : val) : val := *)
(*   λ: "v", *)
(*   let: "s1" := serA (Fst "v") in *)
(*   let: "s2" := serB (Snd "v") in *)
(*   (i2s (strlen "s1")) ^^ (#"_" ^^ ("s1" ^^ "s2")). *)

(* Definition prod_deser (deserA : val) (deserB : val) : val := *)
(*   λ: "s", *)
(*   match: FindFrom "s" #0 #"_" with *)
(*     SOME "i" => *)
(*     let: "len" := unSOME (s2i (Substring "s" #0 "i")) in *)
(*     let: "s1" := Substring "s" ("i" + #1) "len" in *)
(*     let: "s2" := Substring "s" (("i" + #1) + "len") ((strlen "s") - (("i" + #1) + "len")) in *)
(*     let: "v1" := deserA "s1" in *)
(*     let: "v2" := deserB "s2" in *)
(*     ("v1", "v2") *)
(*   | NONE => assert: #false *)
(*   end. *)

(* Definition prod_serializer (sA : serializer) (sB : serializer) := *)
(*   {| *)
(*       s_ser := prod_ser sA.(s_ser) sB.(s_ser); *)
(*       s_deser := prod_deser sA.(s_deser) sB.(s_deser); *)
(*   |}. *)

(* Definition saddr_ser : val := *)
(*   λ: "s", prod_ser string_ser int_ser (GetAddressInfo "s"). *)

(* Definition saddr_deser : val := *)
(*   λ: "s", *)
(*   let: "ipp" := prod_deser string_deser int_deser "s" in *)
(*   MakeAddress (Fst "ipp") (Snd "ipp"). *)

(* Definition saddr_serializer := *)
(*   {| *)
(*       s_ser := saddr_ser; *)
(*       s_deser := saddr_deser; *)
(*   |}. *)

(* Definition sum_ser (serA : val) (serB : val) : val := *)
(*   λ: "v", *)
(*   match: "v" with *)
(*     InjL "x" => #"L" ^^ (#"_" ^^ (serA "x")) *)
(*   | InjR "x" => #"R" ^^ (#"_" ^^ (serB "x")) *)
(*   end. *)

(* Definition sum_deser (deserA : val) (deserB : val) : val := *)
(*   λ: "s", *)
(*   let: "tag" := Substring "s" #0 #2 in *)
(*   let: "rest" := Substring "s" #2 ((strlen "s") - #2) in *)
(*   (if: "tag" = #"L_" *)
(*    then  InjL (deserA "rest") *)
(*    else  (if: "tag" = #"R_" *)
(*      then  InjR (deserB "rest") *)
(*      else  assert: #false)). *)

(* Definition sum_serializer (sA : serializer) (sB : serializer) := *)
(*   {| *)
(*       s_ser := sum_ser sA.(s_ser) sB.(s_ser); *)
(*       s_deser := sum_deser sA.(s_deser) sB.(s_deser); *)
(*   |}. *)

(* Definition option_ser (ser : val) : val := *)
(*   λ: "v", *)
(*   match: "v" with *)
(*     NONE => #"L" ^^ (#"_" ^^ #"") *)
(*   | SOME "x" => #"R" ^^ (#"_" ^^ (ser "x")) *)
(*   end. *)

(* Definition option_deser (deser : val) : val := *)
(*   λ: "s", *)
(*   let: "tag" := Substring "s" #0 #2 in *)
(*   let: "rest" := Substring "s" #2 ((strlen "s") - #2) in *)
(*   (if: "tag" = #"L_" *)
(*    then  NONE *)
(*    else  (if: "tag" = #"R_" *)
(*      then  SOME (deser "rest") *)
(*      else  assert: #false)). *)

(* Definition option_serializer (s : serializer) := *)
(*   {| *)
(*       s_ser := option_ser s.(s_ser); *)
(*       s_deser := option_deser s.(s_deser); *)
(*   |}. *)

(* Definition list_ser (ser : val) : val := *)
(*   rec: "list_ser" "v" := *)
(*   match: "v" with *)
(*     SOME "a" => *)
(*     let: "hd" := ser (Fst "a") in *)
(*     let: "tl" := "list_ser" (Snd "a") in *)
(*     (i2s (strlen "hd")) ^^ (#"_" ^^ ("hd" ^^ "tl")) *)
(*   | NONE => #"" *)
(*   end. *)

(* Definition list_deser (deser : val) : val := *)
(*   rec: "list_deser" "s" := *)
(*   match: FindFrom "s" #0 #"_" with *)
(*     SOME "i" => *)
(*     let: "len" := unSOME (s2i (Substring "s" #0 "i")) in *)
(*     let: "h" := Substring "s" ("i" + #1) "len" in *)
(*     let: "t" := Substring "s" (("i" + #1) + "len") ((strlen "s") - (("i" + #1) + "len")) in *)
(*     let: "hd" := deser "h" in *)
(*     let: "tail" := "list_deser" "t" in *)
(*     "hd" :: "tail" *)
(*   | NONE => NONE *)
(*   end. *)

(* Definition list_serializer (s : serializer) := *)
(*   {| *)
(*       s_ser := list_ser s.(s_ser); *)
(*       s_deser := list_deser s.(s_deser); *)
(*   |}. *)