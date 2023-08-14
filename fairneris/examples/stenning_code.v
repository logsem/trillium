(* From fairneris.aneris_lang Require Export lang. *)
(* From fairneris.aneris_lang.lib.serialization Require Export serialization_code. *)

(* (* OBS: Payload and index is the same for simplicity sake *) *)

(* Definition test_fun : val := λ: "x", "x". *)

(* Definition test_app : val := λ: <>, App (Val int_ser) #0. *)

(* Definition server : val := *)
(*   λ: "clt_sa" "srv_sa", *)
(*     let: "skt" := NewSocket #PF_INET #SOCK_DGRAM #IPPROTO_UDP in *)
(*     SetReceiveTimeout "skt" #0 #0;; (* Make receives blocking *) *)
(*     SocketBind "skt" "srv_sa";; *)
(*     letrec: "go" "cur" := *)
(*      (let: "msg" := ReceiveFrom "skt" in *)
(*       let: "sender" := Snd "skt" in *)
(*       assert: ("sender" = "clt_sa");; (* Loop/remove instead? *) *)
(*       let: "idx" := unSOME (i2s (Fst "msg")) in *)
(*       if: "idx" = "cur" *)
(*       then SendTo "skt" (s2i "cur") "sender";; "go" ("cur" + #1) *)
(*       else SendTo "skt" (s2i ("cur"-#1)) "sender";; "go" "cur") in *)
(*     "go" #0. *)


(* Definition server : val := *)
(*   λ: "clt_sa" "srv_sa", *)
(*     let: "skt" := NewSocket #() in *)
(*     SetReceiveTimeout "skt" #0 #0;; (* Make receives blocking *) *)
(*     SocketBind "skt" "srv_sa";; *)
(*     letrec: "go" "cur" := *)
(*      (let: "msg" := ReceiveFrom "skt" in *)
(*       let: "sender" := Snd "skt" in *)
(*       assert: ("sender" = "clt_sa");; (* Loop/remove instead? *) *)
(*       let: "idx" := int_deser (Fst "msg") in *)
(*       if: "idx" = "cur" *)
(*       then SendTo "skt" (int_ser "cur") "sender";; "go" ("cur" + #1) *)
(*       else SendTo "skt" (int_ser ("cur"-#1)) "sender";; "go" "cur") in *)
(*     "go" #0. *)

(* Definition client : val := *)
(*   λ: "clt_sa" "srv_sa" "n", *)
(*     let: "skt" := NewSocket #() in *)
(*     SetReceiveTimeout "skt" #0 #1;; (* Make receives non-blocking *) *)
(*     SocketBind "skt" "clt_sa";; *)
(*     letrec: "go" "cur" := *)
(*      (if: "cur" = "n" then #() *)
(*       else  *)
(*         SendTo "skt" "srv_sa" (int_ser "cur");; *)
(*         let: "msg" := ReceiveFrom "skt" in *)
(*         match: "msg" with *)
(*           NONE => "go" "cur" *)
(*         | SOME "msg" => *)
(*             let: "sender" := Snd "skt" in *)
(*             assert: ("sender" = "srv_sa");; (* Loop/remove instead? *) *)
(*             let: "idx" := int_deser (Fst "msg") in *)
(*             if: "idx" = "cur" then "go" ("cur"+#1) *)
(*             else "go" "cur" *)
(*         end) in *)
(*     "go" #0. *)