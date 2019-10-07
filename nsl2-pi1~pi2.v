Load "tact_nsl2".
   
Theorem pi1_pi2: phi4 ~ phi24.
unfold phi4, phi24. 
assert( (ostomsg t25) # O).
repeat unf. 

simpl.  simpl. 

 (*
apply RESTR_rev with (ml1:= [t15; t14; t13; t12; msg (pk (N 2)); msg (pk (N 1))]) (ml2:=  [t25; t14; t13; t12; msg (pk (N 2)); msg (pk (N 1))]).

(*assert( (ostomsg t25) # O). *)
repeat unf. simpl.
*)
repeat unf; simpl.
Ltac aply_andBcomm m1 :=
match goal with
|[|- context[ ?B & (EQ_M ?M m1) ] ] => rewrite andB_comm with (b1:= B) (b2:= (EQ_M M m1))
end.
repeat aply_andBcomm (nc 3).

pose proof (EQ_BRmsg_msg').
Ltac aply_eqbr B m5  :=
 match goal with
| [|- context [(if_then_else_M ((EQ_M ?M1 m5) & B) ?M3 ?M4)] ] => rewrite EQ_BRmsg_msg'  with (m1:= M1) (m2:= m5) (m:= M1) (b:= B) (m3:= M3) (m4:=M4)    end.

 aply_eqbr  (EQ_M (to x2) (i 1)) (nc 3). 
simpl.
 


 repeat rewrite  EQ_BRmsg_msg' with (m1 := (pi1 (dec x2 (sk (N 1)))) ) (m2:= (nc 3)) (m:= (pi1 (dec x2 (sk (N 1)))) ) (b:=  (EQ_M (to x2) (i 1))) (m3:=      (if_then_else_M
                           ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
                             (EQ_M (to x1) (i 1))) &
                            (notb (EQ_M (act x2) new))) & 
                           (EQ_M (act x1) new) (pi1 (dec x2 (sk (N 1))))
                           (if_then_else_M (EQ_M (reveal x3) (i 2)) O
                              (if_then_else_M (EQ_M (to x3) (i 2))
                                 (enc
                                    (pi1 (dec x3 (sk (N 2))),
                                    (nc 4, pk (N 2)))
                                    (pi2 (dec x3 (sk (N 2)))) 
                                    (sr 6)) O)))). 
simpl. 
repeat rewrite  EQ_BRmsg_msg' with (m1 := (pi1 (dec x2 (sk (N 1)))) ) (m2:= (nc 3)) (m:= (pi1 (dec x2 (sk (N 1)))) ) (b:=  (EQ_M (to x2) (i 1))) (m3:=    (if_then_else_M
                           ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
                             (EQ_M (to x1) (i 1))) &
                            (notb (EQ_M (act x2) new))) & 
                           (EQ_M (act x1) new)
                           (if_then_else_M (EQ_M (reveal x4) (i 2)) O
                              (if_then_else_M (EQ_M (to x4) (i 2))
                                 (enc
                                    (pi1 (dec x4 (sk (N 2))),
                                    (nc 4, pk (N 2)))
                                    (pi2 (dec x4 (sk (N 2)))) 
                                    (sr 9)) O))
                           (if_then_else_M (EQ_M (reveal x3) (i 2)) O
                              (if_then_else_M (EQ_M (to x3) (i 2))
                                 (if_then_else_M
                                    (EQ_M (reveal x4) (i 2)) &
                                    (EQ_M (to x1) (i 2))
                                    (pi1 (dec x1 (sk (N 2))))
                                    (if_then_else_M
                                       (EQ_M (reveal x4) (i 2)) &
                                       (EQ_M (to x2) (i 2))
                                       (pi1 (dec x2 (sk (N 2))))
                                       (if_then_else_M
                                          (EQ_M (reveal x4) (i 2)) &
                                          (EQ_M (to x3) (i 2))
                                          (pi1 (dec x3 (sk (N 2))))
                                          (if_then_else_M
                                             ((((EQ_M (reveal x4) (i 1)) &
                                                (EQ_M (to x2) (i 1))) &
                                               (EQ_M (to x1) (i 1))) &
                                              (notb (EQ_M (act x2) new))) &
                                             (EQ_M (act x1) new)
                                             (pi1 (dec x2 (sk (N 1))))
                                             (if_then_else_M
                                                ((((EQ_M (reveal x4) (i 1)) &
                                                  (EQ_M (to x3) (i 1))) &
                                                  (EQ_M (to x1) (i 1))) &
                                                 (notb (EQ_M (act x3) new))) &
                                                (EQ_M (act x1) new)
                                                (pi1 (dec x3 (sk (N 1))))
                                                (if_then_else_M
                                                  ((((EQ_M (reveal x4) (i 1)) &
                                                  (EQ_M (to x3) (i 1))) &
                                                  (EQ_M (to x2) (i 1))) &
                                                  (notb (EQ_M (act x3) new))) &
                                                  (EQ_M (act x2) new)
                                                  (pi1 (dec x3 (sk (N 1)))) O))))))
                                 O)))).
simpl. 
repeat rewrite  EQ_BRmsg_msg' with (m1 := (pi1 (dec x2 (sk (N 1)))) ) (m2:= (nc 3)) (m:= (pi1 (dec x2 (sk (N 1)))) ) (b:=  (EQ_M (to x3) (i 1))) (m3:=    (if_then_else_M
                                    (EQ_M (reveal x4) (i 2)) &
                                    (EQ_M (to x1) (i 2))
                                    (pi1 (dec x1 (sk (N 2))))
                                    (if_then_else_M
                                       (EQ_M (reveal x4) (i 2)) &
                                       (EQ_M (to x2) (i 2))
                                       (pi1 (dec x2 (sk (N 2))))
                                       (if_then_else_M
                                          (EQ_M (reveal x4) (i 2)) &
                                          (EQ_M (to x3) (i 2))
                                          (pi1 (dec x3 (sk (N 2))))
                                          (if_then_else_M
                                             ((((EQ_M (reveal x4) (i 1)) &
                                                (EQ_M (to x2) (i 1))) &
                                               (EQ_M (to x1) (i 1))) &
                                              (notb (EQ_M (act x2) new))) &
                                             (EQ_M (act x1) new)
                                             (pi1 (dec x2 (sk (N 1))))
                                             (if_then_else_M
                                                ((((EQ_M (reveal x4) (i 1)) &
                                                  (EQ_M (to x3) (i 1))) &
                                                  (EQ_M (to x1) (i 1))) &
                                                 (notb (EQ_M (act x3) new))) &
                                                (EQ_M (act x1) new)
                                                (pi1 (dec x3 (sk (N 1))))
                                                (if_then_else_M
                                                  ((((EQ_M (reveal x4) (i 1)) &
                                                  (EQ_M (to x3) (i 1))) &
                                                  (EQ_M (to x2) (i 1))) &
                                                  (notb (EQ_M (act x3) new))) &
                                                  (EQ_M (act x2) new)
                                                  (pi1 (dec x3 (sk (N 1)))) O))))))).
simpl.

repeat rewrite  EQ_BRmsg_msg' with (m1 := (pi1 (dec x2 (sk (N 1)))) ) (m2:= (nc 3)) (m:= (pi1 (dec x2 (sk (N 1)))) ) (b:=  (EQ_M (to x2) (i 1))) (m3:=  (if_then_else_M
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)
      (if_then_else_M (EQ_M (reveal x4) (i 2)) O
         (if_then_else_M (EQ_M (to x4) (i 2))
            (enc (pi1 (dec x4 (sk (N 2))), (nc 4, pk (N 2)))
               (pi2 (dec x4 (sk (N 2)))) (sr 9)) O))
      (if_then_else_M (EQ_M (reveal x3) (i 2)) O
         (if_then_else_M (EQ_M (to x3) (i 2))
            (if_then_else_M
               (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
                    (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
                  (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
                (EQ_M (pi1 (dec x3 (sk (N 1)))) (nc 3))) &
               (EQ_M (pi1 (dec x2 (sk (N 2)))) (nc 3)) 
               (nc 5)
               (if_then_else_M
                  (((((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1))) &
                       (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
                     (notb (EQ_M (act x3) new))) & 
                    (EQ_M (act x1) new)) &
                   (EQ_M (pi1 (dec x3 (sk (N 1)))) (nc 3))) &
                  (EQ_M (pi1 (dec x2 (sk (N 2)))) (nc 3)) 
                  (nc 5)
                  (if_then_else_M
                     (EQ_M (reveal x4) (i 2)) & (EQ_M (to x1) (i 2))
                     (pi1 (dec x1 (sk (N 2))))
                     (if_then_else_M
                        (EQ_M (reveal x4) (i 2)) & (EQ_M (to x2) (i 2))
                        (pi1 (dec x2 (sk (N 2))))
                        (if_then_else_M
                           (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2))
                           (pi1 (dec x3 (sk (N 2))))
                           (if_then_else_M
                              ((((EQ_M (reveal x4) (i 1)) &
                                 (EQ_M (to x2) (i 1))) & 
                                (EQ_M (to x1) (i 1))) &
                               (notb (EQ_M (act x2) new))) &
                              (EQ_M (act x1) new) (pi1 (dec x2 (sk (N 1))))
                              (if_then_else_M
                                 ((((EQ_M (reveal x4) (i 1)) &
                                    (EQ_M (to x3) (i 1))) &
                                   (EQ_M (to x1) (i 1))) &
                                  (notb (EQ_M (act x3) new))) &
                                 (EQ_M (act x1) new)
                                 (pi1 (dec x3 (sk (N 1))))
                                 (if_then_else_M
                                    ((((EQ_M (reveal x4) (i 1)) &
                                       (EQ_M (to x3) (i 1))) &
                                      (EQ_M (to x2) (i 1))) &
                                     (notb (EQ_M (act x3) new))) &
                                    (EQ_M (act x2) new)
                                    (pi1 (dec x3 (sk (N 1)))) O)))))))) O)))). 
simpl. 

repeat rewrite  EQ_BRmsg_msg' with (m1 := (pi1 (dec x2 (sk (N 1)))) ) (m2:= (nc 3)) (m:= (pi1 (dec x2 (sk (N 1)))) ) (b:=  (EQ_M (to x3) (i 1))) (m3:=  (if_then_else_M
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (pi1 (dec x3 (sk (N 1)))) (nc 3))) &
      (EQ_M (pi1 (dec x2 (sk (N 2)))) (nc 3)) (nc 5)
      (if_then_else_M
         (((((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1))) &
              (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
            (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
          (EQ_M (pi1 (dec x3 (sk (N 1)))) (nc 3))) &
         (EQ_M (pi1 (dec x2 (sk (N 2)))) (nc 3)) (nc 5)
         (if_then_else_M (EQ_M (reveal x4) (i 2)) & (EQ_M (to x1) (i 2))
            (pi1 (dec x1 (sk (N 2))))
            (if_then_else_M (EQ_M (reveal x4) (i 2)) & (EQ_M (to x2) (i 2))
               (pi1 (dec x2 (sk (N 2))))
               (if_then_else_M
                  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2))
                  (pi1 (dec x3 (sk (N 2))))
                  (if_then_else_M
                     ((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1))) &
                       (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
                     (EQ_M (act x1) new) (pi1 (dec x2 (sk (N 1))))
                     (if_then_else_M
                        ((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1))) &
                          (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x3) new))) &
                        (EQ_M (act x1) new) (pi1 (dec x3 (sk (N 1))))
                        (if_then_else_M
                           ((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1))) &
                             (EQ_M (to x2) (i 1))) &
                            (notb (EQ_M (act x3) new))) & 
                           (EQ_M (act x2) new) (pi1 (dec x3 (sk (N 1)))) O))))))))). 
simpl.


(*assert((ostomsg t15) # (ostomsg t25)).
simpl. unfold qb10_ss, qb01_ss. unfold qb11_s. unfold qa12. unfold qa02_s.*)
 (*qb20_s qb21*)


apply  IFBRANCH_M4 with (ml1:=[msg (pk (N 1)); msg (pk (N 2))]) (ml2 := [msg (pk (N 1)); msg (pk (N 2))]); try  reflexivity;  simpl.
apply  IFBRANCH_M4 with (ml1:=[msg (pk (N 1)); msg (pk (N 2)) ; bol (EQ_M (reveal x1) (i 1))]) (ml2 := [msg (pk (N 1)); msg (pk (N 2)) ; bol (EQ_M (reveal x1) (i 1))]); try  reflexivity;  simpl. 
apply  IFBRANCH_M4 with (ml1:=[msg (pk (N 1)); msg (pk (N 2)); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 2))]) (ml2 := [msg (pk (N 1)); msg (pk (N 2)); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 2))]) ;try  reflexivity;  simpl. 

apply  IFBRANCH_M3 with (ml1:= [msg (pk (N 1)); msg (pk (N 2)); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 2));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    msg (enc (nc 3, pk (N 1)) (pk (N 2)) (sr 1))]) (ml2 := [msg (pk (N 1)); msg (pk (N 2)); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 2));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    msg (enc (nc 3, pk (N 1)) (pk (N 2)) (sr 1))]); try  reflexivity;  simpl. 

apply  IFBRANCH_M3 with (ml1:= [msg (pk (N 1)); msg (pk (N 2)); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 2));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    msg (enc (nc 3, pk (N 1)) (pk (N 2)) (sr 1));
    bol (EQ_M (reveal x2) (i 1))]) (ml2 := [msg (pk (N 1)); msg (pk (N 2)); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 2));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    msg (enc (nc 3, pk (N 1)) (pk (N 2)) (sr 1));
    bol (EQ_M (reveal x2) (i 1))]); try  reflexivity;  simpl. 
apply  IFBRANCH_M3 with (ml1:= [msg (pk (N 1)); msg (pk (N 2)); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 2));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    msg (enc (nc 3, pk (N 1)) (pk (N 2)) (sr 1));
    bol (EQ_M (reveal x2) (i 1)); bol (EQ_M (reveal x2) (i 2))]) (ml2 := [msg (pk (N 1)); msg (pk (N 2)); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 2));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    msg (enc (nc 3, pk (N 1)) (pk (N 2)) (sr 1));
    bol (EQ_M (reveal x2) (i 1)); bol (EQ_M (reveal x2) (i 2))]); try  reflexivity;  simpl. 

apply  IFBRANCH_M2 with (ml1:= [msg (pk (N 1)); msg (pk (N 2)); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 2));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    msg (enc (nc 3, pk (N 1)) (pk (N 2)) (sr 1));
    bol (EQ_M (reveal x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
    bol (EQ_M (pi1 (dec x2 (sk (N 1)))) (nc 3)) & (EQ_M (to x2) (i 1));
    msg
      (enc (pi1 (pi2 (dec (f mphi1) (pi2 (k (N 1))))))
         (pi2 (pi2 (dec (f mphi1) (pi2 (k (N 1)))))) 
         (rs (N 1)))]) (ml2 := [msg (pk (N 1)); msg (pk (N 2)); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 2));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    msg (enc (nc 3, pk (N 1)) (pk (N 2)) (sr 1));
    bol (EQ_M (reveal x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
    bol (EQ_M (pi1 (dec x2 (sk (N 1)))) (nc 3)) & (EQ_M (to x2) (i 1));
    msg
      (enc (pi1 (pi2 (dec (f mphi1) (pi2 (k (N 1))))))
         (pi2 (pi2 (dec (f mphi1) (pi2 (k (N 1)))))) 
         (rs (N 1)))]); try  reflexivity;  simpl. 
apply  IFBRANCH_M2 with (ml1:= [msg (pk (N 1)); msg (pk (N 2)); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 2));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    msg (enc (nc 3, pk (N 1)) (pk (N 2)) (sr 1));
    bol (EQ_M (reveal x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
    bol (EQ_M (pi1 (dec x2 (sk (N 1)))) (nc 3)) & (EQ_M (to x2) (i 1));
    msg
      (enc (pi1 (pi2 (dec (f mphi1) (pi2 (k (N 1))))))
         (pi2 (pi2 (dec (f mphi1) (pi2 (k (N 1)))))) 
         (rs (N 1)));
    bol
      (if_then_else_B
         (if_then_else_B
            (if_then_else_B
               (if_then_else_B (EQ_M (reveal (f mphi2)) (i 1))
                  (EQ_M (to (f mphi1)) (i 1)) FAlse)
               (EQ_M (to (f mphi0)) (i 1)) FAlse)
            (if_then_else_B (EQ_M (act (f mphi1)) new) FAlse TRue) FAlse)
         (EQ_M (act (f mphi0)) new) FAlse)]) (ml2 := [msg (pk (N 1)); msg (pk (N 2)); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 2));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    msg (enc (nc 3, pk (N 1)) (pk (N 2)) (sr 1));
    bol (EQ_M (reveal x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
    bol (EQ_M (pi1 (dec x2 (sk (N 1)))) (nc 3)) & (EQ_M (to x2) (i 1));
    msg
      (enc (pi1 (pi2 (dec (f mphi1) (pi2 (k (N 1))))))
         (pi2 (pi2 (dec (f mphi1) (pi2 (k (N 1)))))) 
         (rs (N 1)));
    bol
      (if_then_else_B
         (if_then_else_B
            (if_then_else_B
               (if_then_else_B (EQ_M (reveal (f mphi2)) (i 1))
                  (EQ_M (to (f mphi1)) (i 1)) FAlse)
               (EQ_M (to (f mphi0)) (i 1)) FAlse)
            (if_then_else_B (EQ_M (act (f mphi1)) new) FAlse TRue) FAlse)
         (EQ_M (act (f mphi0)) new) FAlse)]); try  reflexivity;  simpl. 


apply  IFBRANCH_M2 with (ml1:= [msg (pk (N 1)); msg (pk (N 2)); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 2));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    msg (enc (nc 3, pk (N 1)) (pk (N 2)) (sr 1));
    bol (EQ_M (reveal x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
    bol (EQ_M (pi1 (dec x2 (sk (N 1)))) (nc 3)) & (EQ_M (to x2) (i 1));
    msg
      (enc (pi1 (pi2 (dec (f mphi1) (pi2 (k (N 1))))))
         (pi2 (pi2 (dec (f mphi1) (pi2 (k (N 1)))))) 
         (rs (N 1)));
    bol
      (if_then_else_B
         (if_then_else_B
            (if_then_else_B
               (if_then_else_B (EQ_M (reveal (f mphi2)) (i 1))
                  (EQ_M (to (f mphi1)) (i 1)) FAlse)
               (EQ_M (to (f mphi0)) (i 1)) FAlse)
            (if_then_else_B (EQ_M (act (f mphi1)) new) FAlse TRue) FAlse)
         (EQ_M (act (f mphi0)) new) FAlse);
    bol (EQ_M (reveal (f mphi2)) (i 2))]) (ml2 := [msg (pk (N 1)); msg (pk (N 2)); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 2));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    msg (enc (nc 3, pk (N 1)) (pk (N 2)) (sr 1));
    bol (EQ_M (reveal x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
    bol (EQ_M (pi1 (dec x2 (sk (N 1)))) (nc 3)) & (EQ_M (to x2) (i 1));
    msg
      (enc (pi1 (pi2 (dec (f mphi1) (pi2 (k (N 1))))))
         (pi2 (pi2 (dec (f mphi1) (pi2 (k (N 1)))))) 
         (rs (N 1)));
    bol
      (if_then_else_B
         (if_then_else_B
            (if_then_else_B
               (if_then_else_B (EQ_M (reveal (f mphi2)) (i 1))
                  (EQ_M (to (f mphi1)) (i 1)) FAlse)
               (EQ_M (to (f mphi0)) (i 1)) FAlse)
            (if_then_else_B (EQ_M (act (f mphi1)) new) FAlse TRue) FAlse)
         (EQ_M (act (f mphi0)) new) FAlse);
    bol (EQ_M (reveal (f mphi2)) (i 2))]); try  reflexivity;  simpl. 
apply  IFBRANCH_M1 with (ml1:=[msg (pk (N 1)); msg (pk (N 2)); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 2));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    msg (enc (nc 3, pk (N 1)) (pk (N 2)) (sr 1));
    bol (EQ_M (reveal x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
    bol (EQ_M (pi1 (dec x2 (sk (N 1)))) (nc 3)) & (EQ_M (to x2) (i 1));
    msg
      (enc (pi1 (pi2 (dec (f mphi1) (pi2 (k (N 1))))))
         (pi2 (pi2 (dec (f mphi1) (pi2 (k (N 1)))))) 
         (rs (N 1)));
    bol
      (if_then_else_B
         (if_then_else_B
            (if_then_else_B
               (if_then_else_B (EQ_M (reveal (f mphi2)) (i 1))
                  (EQ_M (to (f mphi1)) (i 1)) FAlse)
               (EQ_M (to (f mphi0)) (i 1)) FAlse)
            (if_then_else_B (EQ_M (act (f mphi1)) new) FAlse TRue) FAlse)
         (EQ_M (act (f mphi0)) new) FAlse);
    bol (EQ_M (reveal (f mphi2)) (i 2)); bol (EQ_M (to (f mphi2)) (i 2));
    msg
      (enc (pi1 (dec (f mphi2) (pi2 (k (N 2)))), (nc 4, pi1 (k (N 2))))
         (pi2 (dec (f mphi2) (pi2 (k (N 2))))) (rs (N 1)))]) (ml2 :=[msg (pk (N 1)); msg (pk (N 2)); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 2));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    msg (enc (nc 3, pk (N 1)) (pk (N 2)) (sr 1));
    bol (EQ_M (reveal x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
    bol (EQ_M (pi1 (dec x2 (sk (N 1)))) (nc 3)) & (EQ_M (to x2) (i 1));
    msg
      (enc (pi1 (pi2 (dec (f mphi1) (pi2 (k (N 1))))))
         (pi2 (pi2 (dec (f mphi1) (pi2 (k (N 1)))))) 
         (rs (N 1)));
    bol
      (if_then_else_B
         (if_then_else_B
            (if_then_else_B
               (if_then_else_B (EQ_M (reveal (f mphi2)) (i 1))
                  (EQ_M (to (f mphi1)) (i 1)) FAlse)
               (EQ_M (to (f mphi0)) (i 1)) FAlse)
            (if_then_else_B (EQ_M (act (f mphi1)) new) FAlse TRue) FAlse)
         (EQ_M (act (f mphi0)) new) FAlse);
    bol (EQ_M (reveal (f mphi2)) (i 2)); bol (EQ_M (to (f mphi2)) (i 2));
    msg
      (enc (pi1 (dec (f mphi2) (pi2 (k (N 2)))), (nc 4, pi1 (k (N 2))))
         (pi2 (dec (f mphi2) (pi2 (k (N 2))))) (rs (N 1)))]); try  reflexivity;  simpl. 
Focus 2.  
apply   IFBRANCH_M1 with (ml1:=[msg (pk (N 1)); msg (pk (N 2)); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 2));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    msg (enc (nc 3, pk (N 1)) (pk (N 2)) (sr 1));
    bol (EQ_M (reveal x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
    bol (EQ_M (pi1 (dec x2 (sk (N 1)))) (nc 3)) & (EQ_M (to x2) (i 1));
    msg
      (enc (pi1 (pi2 (dec (f mphi1) (pi2 (k (N 1))))))
         (pi2 (pi2 (dec (f mphi1) (pi2 (k (N 1)))))) 
         (rs (N 1)));
    bol
      (if_then_else_B
         (if_then_else_B
            (if_then_else_B
               (if_then_else_B (EQ_M (reveal (f mphi2)) (i 1))
                  (EQ_M (to (f mphi1)) (i 1)) FAlse)
               (EQ_M (to (f mphi0)) (i 1)) FAlse)
            (if_then_else_B (EQ_M (act (f mphi1)) new) FAlse TRue) FAlse)
         (EQ_M (act (f mphi0)) new) FAlse);
    bol (EQ_M (reveal (f mphi2)) (i 2)); bol (EQ_M (to (f mphi2)) (i 2));
    msg
      (enc (pi1 (dec (f mphi2) (pi2 (k (N 2)))), (nc 4, pi1 (k (N 2))))
         (pi2 (dec (f mphi2) (pi2 (k (N 2))))) (rs (N 1)));
    bol
      (if_then_else_B (EQ_M (reveal (f mphi3)) (i 2))
         (EQ_M (to (f mphi0)) (i 2)) FAlse)]) (ml2 := [msg (pk (N 1)); msg (pk (N 2)); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 2));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    msg (enc (nc 3, pk (N 1)) (pk (N 2)) (sr 1));
    bol (EQ_M (reveal x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
    bol (EQ_M (pi1 (dec x2 (sk (N 1)))) (nc 3)) & (EQ_M (to x2) (i 1));
    msg
      (enc (pi1 (pi2 (dec (f mphi1) (pi2 (k (N 1))))))
         (pi2 (pi2 (dec (f mphi1) (pi2 (k (N 1)))))) 
         (rs (N 1)));
    bol
      (if_then_else_B
         (if_then_else_B
            (if_then_else_B
               (if_then_else_B (EQ_M (reveal (f mphi2)) (i 1))
                  (EQ_M (to (f mphi1)) (i 1)) FAlse)
               (EQ_M (to (f mphi0)) (i 1)) FAlse)
            (if_then_else_B (EQ_M (act (f mphi1)) new) FAlse TRue) FAlse)
         (EQ_M (act (f mphi0)) new) FAlse);
    bol (EQ_M (reveal (f mphi2)) (i 2)); bol (EQ_M (to (f mphi2)) (i 2));
    msg
      (enc (pi1 (dec (f mphi2) (pi2 (k (N 2)))), (nc 4, pi1 (k (N 2))))
         (pi2 (dec (f mphi2) (pi2 (k (N 2))))) (rs (N 1)));
    bol
      (if_then_else_B (EQ_M (reveal (f mphi3)) (i 2))
         (EQ_M (to (f mphi0)) (i 2)) FAlse)]); try  reflexivity;  simpl. 

(*
Ltac ifbr1 :=
match goal with 
|[|- (?L1 ++ (if_then_else_M ?B ?M1 ?M2)) ~ ?L2 ++ (if_then_else_M ?B1 ?M3 ?M4)] => pose proof(IFBRANCH_M1)
(*apply IFBRANCH_M1 with (ml1:= L1) (ml2:= L2) (b:=B) (b':= B1); try reflexivity; simpl*)
end. *)

apply RESTR_rev with (ml1:= 
apply IFBRANCH_M1.
aply_breq_same.


repeat redg; repeat rewrite IFTFb.

aply_breq_same.
 repeat rewrite andB_elm'' with (b1 := (EQ_M (to x1) (i 1)))(b2:= (EQ_M (act x1) new)).
 false_to_sesns_all.
aply_breq. 
repeat redg; repeat rewrite IFTFb.
 false_to_sesns_all.
aply_breq. 
repeat redg; repeat rewrite IFTFb.
aply_breq. 

repeat redg; repeat rewrite IFTFb. 
 aply_breq_same.
 repeat rewrite andB_elm'' with (b1 := (EQ_M (to (f mphi1)) (i 1)))(b2:=  (EQ_M (pi1 (dec (f mphi1) (pi2 (k (N 1))))) (nc 3))).
false_to_sesns_all. 
aply_breq.
repeat redg; repeat rewrite IFTFb. 
pose proof(EQ_BRmsg_msg''). 

rewrite EQ_BRmsg_msg''' with (m1 := (pi1 (dec (f mphi1) (pi2 (k (N 1))))) ) (m2:= (nc 3)) (m:= (pi1 (dec (f mphi1) (pi2 (k (N 1))))) ) (m3:=  (if_then_else_M
         (if_then_else_B (EQ_M (reveal (f mphi2)) (i 1))
            (if_then_else_B (EQ_M (act (f mphi1)) new) FAlse TRue) FAlse)
         (if_then_else_M (EQ_M (reveal (f mphi3)) (i 2)) O
            (if_then_else_M (EQ_M (to (f mphi3)) (i 2))
               (enc
                  (pi1 (dec (f mphi3) (pi2 (k (N 2)))),
                  (nc 4, pi1 (k (N 2))))
                  (pi2 (dec (f mphi3) (pi2 (k (N 2))))) 
                  (rs (N 1))) O))
         (if_then_else_M (EQ_M (reveal (f mphi2)) (i 2)) O
            (if_then_else_M (EQ_M (to (f mphi2)) (i 2))
               (if_then_else_M
                  (if_then_else_B (EQ_M (reveal (f mphi3)) (i 2))
                     (EQ_M (to (f mphi2)) (i 2)) FAlse)
                  (pi1 (dec (f mphi2) (pi2 (k (N 2)))))
                  (if_then_else_M
                     (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
                        (if_then_else_B (EQ_M (act (f mphi1)) new) FAlse TRue)
                        FAlse) (pi1 (dec (f mphi1) (pi2 (k (N 1)))))
                     (if_then_else_M
                        (if_then_else_B
                           (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
                              (EQ_M (to (f mphi2)) (i 1)) FAlse)
                           (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse
                              TRue) FAlse)
                        (pi1 (dec (f mphi2) (pi2 (k (N 1)))))
                        (if_then_else_M
                           (if_then_else_B
                              (if_then_else_B
                                 (if_then_else_B
                                    (EQ_M (reveal (f mphi3)) (i 1))
                                    (EQ_M (to (f mphi2)) (i 1)) FAlse)
                                 (if_then_else_B (EQ_M (act (f mphi2)) new)
                                    FAlse TRue) FAlse)
                              (EQ_M (act (f mphi1)) new) FAlse)
                           (pi1 (dec (f mphi2) (pi2 (k (N 1))))) O)))) O))))  .
simpl. 
repeat redg; repeat rewrite IFTFb.

aply_breq.
false_to_sesns_all. 
aply_breq. 
false_to_sesns_all. 
aply_breq. 
repeat redg; repeat rewrite IFTFb.
repeat rewrite andB_elm'' with (b1 := (EQ_M (to (f mphi2)) (i 1)))(b2:=  (EQ_M (pi1 (dec (f mphi1) (pi2 (k (N 1))))) (nc 3))).
false_to_sesns_all. simpl. 

aply_breq.

repeat redg; repeat rewrite IFTFb.
 rewrite EQ_BRmsg_msg''' with (m1 := (pi1 (dec (f mphi1) (pi2 (k (N 1))))) ) (m2:= (nc 3)) (m:= (pi1 (dec (f mphi1) (pi2 (k (N 1))))) ) (m3:= (if_then_else_M (EQ_M (reveal (f mphi3)) (i 2))
         (pi1 (dec (f mphi1) (pi2 (k (N 2)))))
         (if_then_else_M
            (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
               (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue) FAlse)
            (pi1 (dec (f mphi2) (pi2 (k (N 1))))) O))). simpl. 
 rewrite EQ_BRmsg_msg''' with (m1 := (pi1 (dec (f mphi1) (pi2 (k (N 1))))) ) (m2:= (nc 3)) (m:= (pi1 (dec (f mphi1) (pi2 (k (N 1))))) ) (m3:=  (if_then_else_M
           (if_then_else_B
              (if_then_else_B
                 (if_then_else_B (EQ_M (reveal (f mphi3)) (i 2))
                    (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                    FAlse)
                 (EQ_M (pi1 (dec (f mphi2) (pi2 (k (N 1))))) (nc 3)) FAlse)
              (EQ_M (pi1 (dec (f mphi1) (pi2 (k (N 2))))) (nc 3)) FAlse)
           (nc 5)
           (if_then_else_M
              (if_then_else_B
                 (if_then_else_B
                    (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
                       (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                       FAlse)
                    (EQ_M (pi1 (dec (f mphi2) (pi2 (k (N 1))))) (nc 3)) FAlse)
                 (EQ_M (pi1 (dec (f mphi1) (pi2 (k (N 2))))) (nc 3)) FAlse)
              (nc 5)
              (if_then_else_M (EQ_M (reveal (f mphi3)) (i 2))
                 (pi1 (dec (f mphi1) (pi2 (k (N 2)))))
                 (if_then_else_M
                    (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
                       (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                       FAlse) (pi1 (dec (f mphi2) (pi2 (k (N 1))))) O))))).  simpl. 
aply_breq. 
false_to_sesns_all.  simpl. 
rewrite andB_assoc with (b1:= (EQ_M (reveal (f mphi3)) (i 2))) (b2:= (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)) (b3:= (EQ_M (pi1 (dec (f mphi2) (pi2 (k (N 1))))) (nc 3))).

rewrite andB_assoc with (b1:= (EQ_M (reveal (f mphi3)) (i 2))) (b2:=  ((if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue) &
            (EQ_M (pi1 (dec (f mphi2) (pi2 (k (N 1))))) (nc 3)))) (b3:= (EQ_M (pi1 (dec (f mphi1) (pi2 (k (N 2))))) (nc 3))).
rewrite andB_elm'' with (b1:= (EQ_M (reveal (f mphi3)) (i 2))) (b2:=  (((if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue) &
          (EQ_M (pi1 (dec (f mphi2) (pi2 (k (N 1))))) (nc 3))) &
         (EQ_M (pi1 (dec (f mphi1) (pi2 (k (N 2))))) (nc 3))) ). 
false_to_sesns_all. simpl. 


aply_breq. 
repeat redg; repeat rewrite IFTFb.
rewrite <- IFSAME_M with (b:= (if_then_else_B
           (if_then_else_B
              (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
              (EQ_M (pi1 (dec (f mphi2) (pi2 (k (N 1))))) (nc 3)) FAlse)
           (EQ_M (pi1 (dec (f mphi1) (pi2 (k (N 2))))) (nc 3)) FAlse))  at 1. 
 repeat rewrite andB_elm'' with (b1:= (if_then_else_B
            (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
            (EQ_M (pi1 (dec (f mphi2) (pi2 (k (N 1))))) (nc 3)) FAlse)) (b2:=  (EQ_M (pi1 (dec (f mphi1) (pi2 (k (N 2))))) (nc 3))).
repeat rewrite andB_elm'' with (b1:= (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)) (b2:= (EQ_M (pi1 (dec (f mphi2) (pi2 (k (N 1))))) (nc 3))).
aply_breq. 
aply_breq. 
rewrite <- IFSAME_M with (b:= (EQ_M (pi1 (dec (f mphi1) (pi2 (k (N 2))))) (nc 3)))  at 1.
aply_breq. 
Focus 3.  
false_to_sesns_all.  simpl. 
 aply_breq.  
repeat redg; repeat rewrite IFTFb. reflexivity. 
simpl. 

aply_breq_same.
assert(qa10_ss # qb10_ss).

repeat unf.
assert(qa01_ss # qb01_ss).
repeat unf.
 

apply breq_msgeq1'. simpl.

aply_breq_same.