From fairneris.aneris_lang Require Export lang.

Definition client (sa_clt sa_srv : socket_address) : val :=
  λ: <>,
     let: "sh_clt" := NewSocket #() in
     SocketBind "sh_clt" #sa_clt;;
     (rec: "f" "i" :=
        SendTo "sh_clt" "sa_srv" (i2s "i");;
        match: (ReceiveFrom "sh_clt") with
          NONE     => "f" "i"
        | SOME "m" => if: Snd "m" = "sa_srv"
                      then
                        let: "j" := s2i (Fst "m") in
                        if: "i" = "j"
                        then "f" ("i" + #1)
                        else "f" "i"
                      else
                        "f" "i"
        end) #0.

Definition server (sa_clt sa_srv : socket_address) : val :=
  λ: <>,
     let: "sh_srv" := NewSocket #() in
     SocketBind "sh_srv" #sa_srv;;
     (rec: "f" "j" :=
        match: (ReceiveFrom "sh_srv") with
          NONE     => "f" "j"
        | SOME "m" => if: Snd "m" = "sa_clt"
                      then
                        let: "i" := s2i (Fst "m") in
                        if: "j"+#1 = "i"
                        then SendTo "sh_srv" "sa_clt" "i";; "f" "i"
                        else SendTo "sh_srv" "sa_clt" "j";; "f" "j"
                      else
                        "f" "j"
        end) #-1.
