 Load "tact_DH_2".
 
 
Theorem Pi44_Pi24:  phi44 ~ phi24.

Proof.
unfold phi44, phi24. unfold t45, t25.
simpl.  
repeat unf.



apply  IFBRANCH_M4 with (ml1:= [msg (G 0); msg (g 0)]) (ml2 := [msg (G 0); msg (g 0)]); try  reflexivity;  simpl. 
apply  IFBRANCH_M4 with (ml1:= [msg (G 0); msg (g 0);  bol (EQ_M (reveal x1) (i 1)) ]) (ml2 := [msg (G 0); msg (g 0);  bol (EQ_M (reveal x1) (i 1))]); try   reflexivity;  simpl.
apply IFBRANCH_M4 with (ml1:= [msg (G 0); msg (g 0); bol (EQ_M (reveal x1) (i 1)); bol (EQ_M (reveal x1) (i 2))]) (ml2:= [msg (G 0); msg (g 0); bol (EQ_M (reveal x1) (i 1)); bol (EQ_M (reveal x1) (i 2))]); try reflexivity;  simpl. 
 
apply IFBRANCH_M3 with (ml1:= [msg (G 0); msg (g 0); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 2));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new); 
    msg (grn 1)])  (ml2:= [msg (G 0); msg (g 0); bol (EQ_M (reveal x1) (i 1)); 
    bol (EQ_M (reveal x1) (i 2));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new); 
    msg (grn 1)]); try reflexivity; simpl.
apply IFBRANCH_M3 with (ml1:= [msg (G 0); msg (g 0); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 2));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new); 
    msg (grn 1); bol (EQ_M (reveal x2) (i 1))])(ml2:= [msg (G 0); msg (g 0); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 2));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new); 
    msg (grn 1); bol (EQ_M (reveal x2) (i 1))]) ; try reflexivity; simpl.
apply IFBRANCH_M3 with (ml1 := [msg (G 0); msg (g 0); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 2));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new); 
    msg (grn 1); bol (EQ_M (reveal x2) (i 1)); bol (EQ_M (reveal x2) (i 2))])(ml2:= [msg (G 0); msg (g 0); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 2));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new); 
    msg (grn 1); bol (EQ_M (reveal x2) (i 1)); bol (EQ_M (reveal x2) (i 2))]) ; try reflexivity; simpl.

apply IFBRANCH_M2 with (ml1:= [msg (G 0); msg (g 0); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 2));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new); 
    msg (grn 1); bol (EQ_M (reveal x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
    bol (EQ_M (to x2) (i 1)); msg acc]) (ml2:= [msg (G 0); msg (g 0); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 2));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new); 
    msg (grn 1); bol (EQ_M (reveal x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
    bol (EQ_M (to x2) (i 1)); msg acc]) ; try reflexivity; simpl.
apply IFBRANCH_M2 with (ml1:=[msg (G 0); msg (g 0); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 2));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new); 
    msg (grn 1); bol (EQ_M (reveal x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
    bol (EQ_M (to x2) (i 1)); msg acc;
    bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)])
    (ml2:= [msg (G 0); msg (g 0); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 2));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new); 
    msg (grn 1); bol (EQ_M (reveal x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
    bol (EQ_M (to x2) (i 1)); msg acc;
    bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)])
   ; try reflexivity; simpl.
apply IFBRANCH_M2 with (ml1:= [msg (G 0); msg (g 0); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 2));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new); 
    msg (grn 1); bol (EQ_M (reveal x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
    bol (EQ_M (to x2) (i 1)); msg acc;
    bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new); bol (EQ_M (reveal x3) (i 2))]) (ml2:= [msg (G 0); msg (g 0); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 2));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new); 
    msg (grn 1); bol (EQ_M (reveal x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
    bol (EQ_M (to x2) (i 1)); msg acc;
    bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new); bol (EQ_M (reveal x3) (i 2))]) ; try reflexivity ; simpl.

apply IFBRANCH_M1 with (ml1:= [msg (G 0); msg (g 0); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 2));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new); 
    msg (grn 1); bol (EQ_M (reveal x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
    bol (EQ_M (to x2) (i 1)); msg acc;
    bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new); bol (EQ_M (reveal x3) (i 2));
    bol (EQ_M (to x3) (i 2)); msg (grn 2)])(ml2:= [msg (G 0); msg (g 0); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 2));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new); 
    msg (grn 1); bol (EQ_M (reveal x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
    bol (EQ_M (to x2) (i 1)); msg acc;
    bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new); bol (EQ_M (reveal x3) (i 2));
    bol (EQ_M (to x3) (i 2)); msg (grn 2)]); try reflexivity; simpl.

DDH2.







funapp_fm_in (i 1) DDH1.
funapp_fm_in (i 2) DDH1.

funapp_sublist_in 0 2 DDH1.
funapp_f1_in reveal 8 DDH1.
funapp_f2b_in EQ_M 9 6 DDH1.
funapp_f2b_in EQ_M 9 7 DDH1.
funapp_fm_in O DDH1.
funapp_f1_in to 8 DDH1.
funapp_f2b_in EQ_M 13 7 DDH1.
funapp_f3bm_in (if_then_else_M) 14 4 12  DDH1.
funapp_f2b_in EQ_M 13 6 DDH1.
funapp_f1_in act 8 DDH1.
funapp_fm_in new DDH1.
funapp_f2b_in EQ_M 17 18 DDH1.
funapp_andB_in 16 19 DDH1.
funapp_f3bm_in (if_then_else_M) 20 3 15 DDH1.

funapp_f3bm_in (if_then_else_M) 11 12 21 DDH1.
funapp_f3bm_in (if_then_else_M) 10 12 22 DDH1.
 reswap_in 5 23 DDH1.
reswap_in 4 5 DDH1.
reswap_in 3 4 DDH1.
funapp_sublist_in 0 3 DDH1.
funapp_f1_in reveal 24 DDH1.
funapp_f1_in to 24 DDH1.
funapp_f1_in act 24 DDH1.
funapp_f2b_in EQ_M 26 6 DDH1.
funapp_f2b_in EQ_M 26 7 DDH1.
funapp_f2b_in EQ_M 25 6 DDH1.
funapp_f2b_in EQ_M 25 7 DDH1.
funapp_f2b_in EQ_M 27 18 DDH1.
funapp_andB_in 28 32 DDH1.
funapp_f3bm_in (if_then_else_M) 33 4 12  DDH1.
funapp_f3bm_in (if_then_else_M) 30 12 34  DDH1.
funapp_andB_in 31 14 DDH1.

funapp_fm_in mx1rn1 DDH1.
funapp_f3bm_in (if_then_else_M) 36  37 35 DDH1.
(*******************************************************)
assert((f [G 0; g 0]) # x1).
reflexivity.
rewrite H in DDH1. 

assert((f
               [G 0; g 0;
               if_then_else_M (EQ_M (reveal (f [G 0; g 0])) (i 1)) O
                 (if_then_else_M (EQ_M (reveal (f [G 0; g 0])) (i 2)) O
                    (if_then_else_M
                       (EQ_M (to (f [G 0; g 0])) (i 1)) &
                       (EQ_M (act (f [G 0; g 0])) new)
                       (exp (G 0) (g 0) (r 1))
                       (if_then_else_M (EQ_M (to (f [G 0; g 0])) (i 2))
                          (exp (G 0) (g 0) (r 2)) O)))]) # x2).
reflexivity .
rewrite H0 in DDH1.


(**********************************************************)
funapp_f3bm_in (if_then_else_M) 14 38 12 DDH1.

funapp_f3bm_in (if_then_else_M) 29 5 12 DDH1.
funapp_fm_in acc DDH1.
funapp_f3bm_in (if_then_else_M) 28 41 40 DDH1.
funapp_f3bm_in (if_then_else_M) 31 12 42 DDH1.
funapp_f3bm_in (if_then_else_M) 30 12 43 DDH1.
funapp_f3bm_in (if_then_else_M) 20 44 39 DDH1.
funapp_f3bm_in (if_then_else_M) 11  12 45 DDH1.
funapp_f3bm_in (if_then_else_M) 10  12 46 DDH1.

(**********************************************************)
Eval compute in x3. 
assert((f
               [G 0; g 0;
               if_then_else_M (EQ_M (reveal (f [G 0; g 0])) (i 1)) O
                 (if_then_else_M (EQ_M (reveal (f [G 0; g 0])) (i 2)) O
                    (if_then_else_M
                       (EQ_M (to (f [G 0; g 0])) (i 1)) &
                       (EQ_M (act (f [G 0; g 0])) new)
                       (exp (G 0) (g 0) (r 1))
                       (if_then_else_M (EQ_M (to (f [G 0; g 0])) (i 2))
                          (exp (G 0) (g 0) (r 2)) O)));  (if_then_else_M (EQ_M (reveal x1) (i 1)) O
              (if_then_else_M (EQ_M (reveal x1) (i 2)) O
                 (if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
                    (if_then_else_M (EQ_M (reveal x2) (i 1)) O
                       (if_then_else_M (EQ_M (reveal x2) (i 2)) O
                          (if_then_else_M (EQ_M (to x2) (i 1)) acc
                             (if_then_else_M (EQ_M (to x2) (i 2))
                                (exp (G 0) (g 0) (r 2)) O))))
                    (if_then_else_M (EQ_M (to x1) (i 2))
                       (if_then_else_M
                          (EQ_M (reveal x2) (i 2)) & (EQ_M (to x1) (i 2))
                          mx1rn1
                          (if_then_else_M (EQ_M (reveal x2) (i 1)) O
                             (if_then_else_M
                                (EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)
                                (exp (G 0) (g 0) (r 1)) O))) O))))]) # x3).
 
reflexivity.
(***************************************  **************** *****)
reswap_in 6 47 DDH1. 
reswap_in 5 6 DDH1.
reswap_in 4 5 DDH1.
funapp_sublist_in 0 4 DDH1.
rewrite H1 in DDH1.
funapp_f1_in to 48 DDH1.
funapp_f2b_in EQ_M 49 47 DDH1.
funapp_f2b_in EQ_M 49 7 DDH1.
funapp_f1_in reveal 48 DDH1.
funapp_f2b_in EQ_M 52 47 DDH1.
funapp_f2b_in EQ_M 52 7 DDH1.
funapp_f1_in act 48 DDH1.
funapp_f2b_in EQ_M 55 18 DDH1.
funapp_andB_in 50 56 DDH1.
funapp_f3bm_in (if_then_else_M) 57 5 12 DDH1.
funapp_f3bm_in (if_then_else_M) 53 12 58 DDH1.

funapp_f3bm_in (if_then_else_M) 33  59 12 DDH1.
(*funapp_f3bm_in (if_then_else_M) 14 60 12 DDH1.*)
funapp_f3bm_in (if_then_else_M) 30 12 60 DDH1.
funapp_f3bm_in (if_then_else_M) 36 37 61 DDH1.

funapp_f3bm_in (if_then_else_M) 14 62 12 DDH1.
funapp_f3bm_in (if_then_else_M) 50 41 12 DDH1.


funapp_f3bm_in (if_then_else_M) 53 12 64 DDH1.
funapp_andB_in 54 29 DDH1.
funapp_fm_in mx2rn2 DDH1.
funapp_f3bm_in (if_then_else_M) 66 67 65 DDH1.
funapp_andB_in 54 14 DDH1.
  
funapp_f3bm_in (if_then_else_M) 69 37 68 DDH1.
funapp_f3bm_in (if_then_else_M) 29 70 12 DDH1.
funapp_f3bm_in (if_then_else_M) 51 6 12 DDH1.
funapp_f3bm_in (if_then_else_M) 54 12 72 DDH1.
funapp_fm_in mx2rn1 DDH1.
funapp_andB_in 53 28 DDH1.
funapp_andB_in 75 16 DDH1.

funapp_notB_in 32 DDH1.
funapp_andB_in 76 77 DDH1.
funapp_andB_in 78 19 DDH1.

 funapp_f3bm_in (if_then_else_M) 79 74 73 DDH1.
funapp_f3bm_in (if_then_else_M) 28 80 71 DDH1.
funapp_f3bm_in (if_then_else_M) 31 12 81 DDH1.
funapp_f3bm_in (if_then_else_M) 30 12 82 DDH1.
funapp_f3bm_in (if_then_else_M) 20 83 63 DDH1.
funapp_f3bm_in (if_then_else_M) 11 12 84  DDH1.
funapp_f3bm_in (if_then_else_M) 10 12 85 DDH1.
reswap_in 7 86  DDH1. 
reswap_in 6 7 DDH1. 
reswap_in 5 6 DDH1. 

funapp_sublist_in 0 5 DDH1.
assert((f
              [G 0; g 0;
              if_then_else_M (EQ_M (reveal x1) (i 1)) O
                (if_then_else_M (EQ_M (reveal x1) (i 2)) O
                   (if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
                      (exp (G 0) (g 0) (r 1))
                      (if_then_else_M (EQ_M (to x1) (i 2))
                         (exp (G 0) (g 0) (r 2)) O)));
              if_then_else_M (EQ_M (reveal x1) (i 1)) O
                (if_then_else_M (EQ_M (reveal x1) (i 2)) O
                   (if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
                      (if_then_else_M (EQ_M (reveal x2) (i 1)) O
                         (if_then_else_M (EQ_M (reveal x2) (i 2)) O
                            (if_then_else_M (EQ_M (to x2) (i 1)) acc
                               (if_then_else_M (EQ_M (to x2) (i 2))
                                  (exp (G 0) (g 0) (r 2)) O))))
                      (if_then_else_M (EQ_M (to x1) (i 2))
                         (if_then_else_M
                            (EQ_M (reveal x2) (i 2)) & (EQ_M (to x1) (i 2))
                            mx1rn1
                            (if_then_else_M (EQ_M (reveal x2) (i 1)) O
                               (if_then_else_M
                                  (EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)
                                  (exp (G 0) (g 0) (r 1)) O))) O)));
              if_then_else_M (EQ_M (reveal x1) (i 1)) O
                (if_then_else_M (EQ_M (reveal x1) (i 2)) O
                   (if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
                      (if_then_else_M (EQ_M (reveal x2) (i 1)) O
                         (if_then_else_M (EQ_M (reveal x2) (i 2)) O
                            (if_then_else_M (EQ_M (to x2) (i 1))
                               (if_then_else_M
                                  ((((EQ_M (reveal x3) (i 1)) &
                                     (EQ_M (to x2) (i 1))) &
                                    (EQ_M (to x1) (i 1))) &
                                   (notb (EQ_M (act x2) new))) &
                                  (EQ_M (act x1) new) mx2rn1
                                  (if_then_else_M (EQ_M (reveal x3) (i 2)) O
                                     (if_then_else_M 
                                        (EQ_M (to x3) (i 2))
                                        (exp (G 0) (g 0) (r 2)) O)))
                               (if_then_else_M (EQ_M (to x2) (i 2))
                                  (if_then_else_M
                                     (EQ_M (reveal x3) (i 2)) &
                                     (EQ_M (to x1) (i 2)) mx1rn1
                                     (if_then_else_M
                                        (EQ_M (reveal x3) (i 2)) &
                                        (EQ_M (to x2) (i 2)) mx2rn2
                                        (if_then_else_M
                                           (EQ_M (reveal x3) (i 1)) O
                                           (if_then_else_M
                                              (EQ_M (to x3) (i 1)) acc O))))
                                  O))))
                      (if_then_else_M (EQ_M (to x1) (i 2))
                         (if_then_else_M
                            (EQ_M (reveal x2) (i 2)) & (EQ_M (to x1) (i 2))
                            mx1rn1
                            (if_then_else_M (EQ_M (reveal x2) (i 1)) O
                               (if_then_else_M
                                  (EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)
                                  (if_then_else_M (EQ_M (reveal x3) (i 1)) O
                                     (if_then_else_M
                                        (EQ_M (to x3) (i 1)) &
                                        (EQ_M (act x3) new)
                                        (exp (G 0) (g 0) (r 1)) O)) O))) O)))]) # x4).

reflexivity.
rewrite H2 in DDH1.


clear H H0 H1 H2.
fold qa00 in DDH1.

restrproj_in 64 DDH1 .
restrproj_in 63 DDH1.
do 20 (restrproj_in 63 DDH1 ).
do 3 (restrproj_in 3 DDH1 ).

 do 3 (restrproj_in 17 DDH1 ).
 do 10 (restrproj_in 29 DDH1 ).

 do 11 (restrproj_in 37 DDH1 ).
 do 4 (restrproj_in 28 DDH1 ).
restr_swap_in 3 7 DDH1.
restr_swap_in 4 8 DDH1.
funapp_andB_in 13 16 DDH1. 
restr_swap_in 5 35 DDH1.
restr_swap_in 6 7 DDH1.
restr_swap_in 7 24 DDH1.
restr_swap_in 8 25 DDH1.
restr_swap_in 9 22 DDH1.
funapp_fm_in acc DDH1.
restr_swap_in 10 40 DDH1.
funapp_fm_in (i 1) DDH1.

funapp_f2b_in EQ_M 32 37 DDH1.

funapp_andB_in 38 9 DDH1.
funapp_andB_in 39 13 DDH1.
funapp_notB_in 26 DDH1.

funapp_andB_in 40 41 DDH1.
funapp_andB_in 42 16 DDH1.
do 4 (restrproj_in 39 DDH1).
funapp_f2b_in EQ_M 32 33 DDH1.
restr_swap_in 11 39 DDH1.
restr_swap_in 12 40 DDH1.
restr_swap_in 13 31 DDH1.
restr_swap_in 14 25 DDH1.
funapp_f1_in reveal 34 DDH1.
funapp_f2b_in EQ_M  41 33 DDH1.
 funapp_andB_in 42 30 DDH1.
funapp_andB_in 43 23 DDH1.
 funapp_andB_in 44 31 DDH1.
funapp_f1_in act 28 DDH1.
funapp_f2b_in EQ_M 46 15 DDH1.
funapp_notB_in 47 DDH1. 
restrproj_in 46 DDH1.
funapp_andB_in 45 47  DDH1.
funapp_f2b_in EQ_M 25 15 DDH1.
funapp_andB_in 48 49 DDH1.
funapp_f1_in m 18 DDH1.
funapp_f1_in m 28 DDH1.
funapp_f2b_in EQ_M 51 6 DDH1.
funapp_f2b_in EQ_M 52 14 DDH1.
funapp_andB_in 50 53 DDH1.
funapp_andB_in 55 54 DDH1.
restr_swap_in 15 56 DDH1.
restr_swap_in 16 17 DDH1.
do 40 (restrproj_in 17 DDH1).
pose proof(commexp).
rewrite commexp with (G:= (G 0)) (g:=(g 0)) (x:= (r 1)) (y:= (r 2)) in DDH1.

assumption.

funapp_notB_in 
aply1 3 (restrproj_in 10 DDH1).
assert (if_then_else_M (EQ_M (reveal x1) (i 1)) O
              (if_then_else_M (EQ_M (reveal x1) (i 2)) O
                 (if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
                    (if_then_else_M (EQ_M (reveal x2) (i 1)) O
                       (if_then_else_M (EQ_M (reveal x2) (i 2)) O
                          (if_then_else_M (EQ_M (to x2) (i 1))
                             (if_then_else_M
                                ((((EQ_M (reveal x3) (i 1)) &
                                   (EQ_M (to x2) (i 1))) &
                                  (EQ_M (to x1) (i 1))) &
                                 (notb (EQ_M (act x2) new))) &
                                (EQ_M (act x1) new) mx2rn1
                                (if_then_else_M (EQ_M (reveal x3) (i 2)) O
                                   (if_then_else_M 
                                      (EQ_M (to x3) (i 2))
                                      (exp (G 0) (g 0) (r 2)) O)))
                             (if_then_else_M (EQ_M (to x2) (i 2))
                                (if_then_else_M
                                   (EQ_M (reveal x3) (i 2)) &
                                   (EQ_M (to x1) (i 2)) mx1rn1
                                   (if_then_else_M
                                      (EQ_M (reveal x3) (i 2)) &
                                      (EQ_M (to x2) (i 2)) mx2rn2
                                      (if_then_else_M
                                         (EQ_M (reveal x3) (i 1)) O
                                         (if_then_else_M 
                                            (EQ_M (to x3) (i 1)) acc O)))) O))))
                    (if_then_else_M (EQ_M (to x1) (i 2))
                       (if_then_else_M
                          (EQ_M (reveal x2) (i 2)) & (EQ_M (to x1) (i 2))
                          mx1rn1
                          (if_then_else_M (EQ_M (reveal x2) (i 1)) O
                             (if_then_else_M
                                (EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)
                                (if_then_else_M (EQ_M (reveal x3) (i 1)) O
                                   (if_then_else_M
                                      (EQ_M (to x3) (i 1)) &
                                      (EQ_M (act x3) new)
                                      (exp (G 0) (g 0) (r 1)) O)) O))) O)))) #  (if_then_else_M (EQ_M (reveal x1) (i 1)) O
         (if_then_else_M (EQ_M (reveal x1) (i 2)) O
            (if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
               (if_then_else_M (EQ_M (reveal x2) (i 1)) O
                  (if_then_else_M (EQ_M (reveal x2) (i 2)) O
                     (if_then_else_M (EQ_M (to x2) (i 1))
                        (if_then_else_M
                           ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
                             (EQ_M (to x1) (i 1))) &
                            (notb (EQ_M (act x2) new))) & 
                           (EQ_M (act x1) new) mx2rn1
                           (if_then_else_M (EQ_M (reveal x3) (i 2)) O
                              (if_then_else_M (EQ_M (to x3) (i 2)) (grn 2) O)))
                        (if_then_else_M (EQ_M (to x2) (i 2))
                           (if_then_else_M
                              (EQ_M (reveal x3) (i 2)) & (EQ_M (to x1) (i 2))
                              mx1rn1
                              (if_then_else_M
                                 (EQ_M (reveal x3) (i 2)) &
                                 (EQ_M (to x2) (i 2)) mx2rn2
                                 (if_then_else_M (EQ_M (reveal x3) (i 1)) O
                                    (if_then_else_M 
                                       (EQ_M (to x3) (i 1)) acc O)))) O))))
               (if_then_else_M (EQ_M (to x1) (i 2))
                  (if_then_else_M
                     (EQ_M (reveal x2) (i 2)) & (EQ_M (to x1) (i 2)) mx1rn1
                     (if_then_else_M (EQ_M (reveal x2) (i 1)) O
                        (if_then_else_M
                           (EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)
                           (if_then_else_M (EQ_M (reveal x3) (i 1)) O
                              (if_then_else_M
                                 (EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)
                                 (grn 1) O)) O))) O)))).
simpl. 
fold grn.
unfold grn.
reflexivity. 
funapp_
funapp_
funapp_f3bm_in (if_then_else_M) 20 3 15 DDH1.

fresh_ind 3 3 DDH1.
Eval compute in grn 3.
funapp_f3m_in exp 2 3 1 H.



fresh_ind 5 5 H.
Fresh_ind 3 3.
repeat (split;  simpl;  try reflexivity ; try assumption).


aply_FrIND.
  split ;simpl.  reflexivity.  split ; simpl. reflexivity. assumption.
repeat (split;simpl); assumption.
apply FRESHIND in H. simpl in H. 
apply FRESHIND with (n1:= 3) (n2:= 3) in DDH1.
apply FUNCApp_sublist with (m:=0) (n:= 2) in DDH1. simpl in DDH1. unfold sublist in DDH1; simpl in DDH1.
Eval compute in grn 3.


 
simpl. 
  apply RESTR_rev with (ml1:= (reverse phi44)) (ml2 := (reverse phi24)).

simpl.


 

unfold t45, t25.   
ifb.
ifb.
ifb.
ifb.
ifb.
ifb.
ifb.
ifb.
ifb. 
ifb.

Focus 2.
ifb.
Unfocus.
Focus 3.
ifb.
ifb.
ifb.
ifb.
 (*
rewrite commexp .
*)
apply RESTR_rev in DDH1.  
simpl in DDH1.


restr_swap 1 12  [t14;
    bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) grn1)) & (EQ_M (m x3) (grn 2)); bol (EQ_M (to x3) (i 2));
    bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new); bol (EQ_M (reveal x3) (i 2));
    bol (EQ_M (to x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
    bol (EQ_M (reveal x2) (i 1));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1)); msg (grn 2)1; t13;
    t12; msg (g 0); msg (G 0)]   [t14 ;
   bol
     (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
          (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
        (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
      (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2)); bol (EQ_M (to x3) (i 2));
   bol
     ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
       (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
     (EQ_M (act x1) new); bol (EQ_M (reveal x3) (i 2));
   bol (EQ_M (to x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
   bol (EQ_M (reveal x2) (i 1));
   bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
   bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1)); msg grn4; t13; t12;
   msg (g 0); msg (G 0)].
unfold t14.
repeat ifb.
restr_swap 1 14 [t13 ; bol (EQ_M (reveal x1) (i 1));
    bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2)); bol (EQ_M (to x3) (i 2));
    bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new); bol (EQ_M (reveal x3) (i 2));
    bol (EQ_M (to x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
    bol (EQ_M (reveal x2) (i 1));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1)); 
    msg (grn 2)1; msg O; t12; msg (g 0); msg (G 0)]
   [t13 ; bol (EQ_M (reveal x1) (i 1));
   bol
     (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
          (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
        (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
      (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2)); bol (EQ_M (to x3) (i 2));
   bol
     ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
       (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
     (EQ_M (act x1) new); bol (EQ_M (reveal x3) (i 2));
   bol (EQ_M (to x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
   bol (EQ_M (reveal x2) (i 1));
   bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
   bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1)); 
   msg grn4; msg O; t12; msg (g 0); msg (G 0)].
unfold t13.
repeat ifb.

restr_swap 1 16 [t12; bol (EQ_M (reveal x1) (i 1)); bol (EQ_M (reveal x1) (i 1));
    bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2)); bol (EQ_M (to x3) (i 2));
    bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new); bol (EQ_M (reveal x3) (i 2));
    bol (EQ_M (to x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
    bol (EQ_M (reveal x2) (i 1));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1)); 
    msg (grn 2)1; msg O; msg O; msg (g 0); msg (G 0)]
   [t12; bol (EQ_M (reveal x1) (i 1)); bol (EQ_M (reveal x1) (i 1));
   bol
     (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
          (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
        (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
      (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2)); bol (EQ_M (to x3) (i 2));
   bol
     ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
       (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
     (EQ_M (act x1) new); bol (EQ_M (reveal x3) (i 2));
   bol (EQ_M (to x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
   bol (EQ_M (reveal x2) (i 1));
   bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
   bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1)); 
   msg grn4; msg O; msg O; msg (g 0); msg (G 0)].
unfold t12. unf_qa.
repeat ifb.
(*******************)
restr_proj_in 3 DDH1.
 funapp_droplt DDH1.
funapp_droplt DDH1.
funapp_O_in DDH1.
funapp_O_in DDH1.
restr_swap_in 2 4 DDH1.
restr_swap_in 3 5 DDH1.
funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).

rev_app funapp_O_in  DDH1; do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto.  
(**************************************)


 funapp_droplt DDH1.
funapp_droplt DDH1.
funapp_O_in DDH1.
funapp_O_in DDH1.
restr_swap_in 2 4 DDH1.
restr_swap_in 3 5 DDH1.
funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).

rev_app funapp_O_in DDH1.  assumption. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto.  
(*************************************************)
restr_swap_in 2 3 DDH1.

 funapp_droplt DDH1.
funapp_O_in DDH1.
funapp_O_in DDH1.
restr_swap_in 3 5 DDH1.
restr_swap_in 4 6 DDH1.
restr_swap_in 1 2 DDH1.


funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
restr_swap_in 1 16 DDH1.
  assumption. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto.  auto. 

(***********************************************************)

restr_swap_in 2 3 DDH1.

 funapp_droplt DDH1.
funapp_O_in DDH1.
funapp_O_in DDH1.
restr_swap_in 3 5 DDH1.
restr_swap_in 4 6 DDH1.
restr_swap_in 1 2 DDH1.


funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x1) (i 2))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
restr_swap_in 1 17 DDH1.
  assumption. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto. repeat (try reflexivity).
auto. auto . auto.
aply 3 auto. auto. auto. auto . auto.  auto.

(*******************************************************)


funapp_droplt DDH1.
funapp_droplt DDH1.
rev_app funapp_O_in DDH1.
rev_app funapp_O_in DDH1.
restr_swap_in 1 3 DDH1.

funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x1) (i 2))).
rev_app funapp_O_in DDH1.
assumption.
 aply 3 auto. auto. auto. auto. auto. auto.
auto. repeat (try reflexivity).
auto. auto . auto.
aply 3 auto. auto. auto. auto . auto.  auto.

(****************************************)
restr_swap_in 2 3 DDH1.
funapp_droplt DDH1.
funapp_droplt DDH1.

rev_app funapp_O_in DDH1.
rev_app funapp_O_in  DDH1.
restr_swap_in 1 3 DDH1.

funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
rev_app funapp_O_in DDH1.
restr_swap 1 17 [t12 ; bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 1));
    bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2)); bol (EQ_M (to x3) (i 2));
    bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new); bol (EQ_M (reveal x3) (i 2));
    bol (EQ_M (to x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
    bol (EQ_M (reveal x2) (i 1));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1)); 
    msg (grn 2)1; msg O; msg O; msg (g 0); msg (G 0)]
   [t12 ; bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1));
   bol (EQ_M (reveal x1) (i 1));
   bol
     (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
          (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
        (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
      (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2)); bol (EQ_M (to x3) (i 2));
   bol
     ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
       (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
     (EQ_M (act x1) new); bol (EQ_M (reveal x3) (i 2));
   bol (EQ_M (to x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
   bol (EQ_M (reveal x2) (i 1));
   bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
   bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1)); 
   msg grn4; msg O; msg O; msg (g 0); msg (G 0)].
unfold t12. unf_qa.
repeat ifb.
assumption.
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
restr_swap_in 1 2 DDH1.
 aply 3 auto. auto. clear DDH1.
(*************************************)
DDH2.
rewrite commexp in DDH1.
apply RESTR_rev in DDH1. simpl in DDH1.

restr_swap_in 2 3 DDH1.
funapp_droplt DDH1.
rev_app funapp_O_in DDH1.
restr_swap_in 1 2 DDH1.


funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
rev_app funapp_O_in DDH1.
restr_swap_in 1 20 DDH1.
assumption. auto. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto. auto.
clear DDH1.
(******************************)


DDH2.
rewrite commexp in DDH1.
apply RESTR_rev in DDH1. simpl in DDH1.

restr_swap_in 2 3 DDH1.
funapp_droplt DDH1.
rev_app funapp_O_in DDH1.
restr_swap_in 1 2 DDH1.


funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x1) (i 2))) .
rev_app funapp_O_in DDH1.
restr_swap_in 1 21 DDH1.
assumption. auto. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto. auto. auto.
clear DDH1.

(****************************************)
DDH2.
rewrite commexp in DDH1.
apply RESTR_rev in DDH1. simpl in DDH1.

funapp_droplt DDH1.
funapp_droplt DDH1.
rev_app funapp_O_in  DDH1.
rev_app funapp_O_in DDH1.
restr_swap_in 1 3 DDH1.


funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x1) (i 2))) .
rev_app funapp_O_in DDH1.

assumption. auto. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto. auto. auto.  auto. auto. auto. auto. auto.
 auto. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto. auto. auto.  auto. auto. auto. auto. auto.
(*************************************************************)
unf_qa.
repeat ifb.
restr_swap 1 19 [t12 ; bol (EQ_M (reveal x2) (i 1));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 1));
    bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2)); bol (EQ_M (to x3) (i 2));
    bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new); bol (EQ_M (reveal x3) (i 2));
    bol (EQ_M (to x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
    bol (EQ_M (reveal x2) (i 1));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1)); 
    msg (grn 2)1; msg O; msg O; msg (g 0); msg (G 0)]
   [t12 ; bol (EQ_M (reveal x2) (i 1));
   bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
   bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1));
   bol (EQ_M (reveal x1) (i 1));
   bol
     (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
          (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
        (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
      (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2)); bol (EQ_M (to x3) (i 2));
   bol
     ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
       (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
     (EQ_M (act x1) new); bol (EQ_M (reveal x3) (i 2));
   bol (EQ_M (to x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
   bol (EQ_M (reveal x2) (i 1));
   bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
   bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1)); 
   msg grn4; msg O; msg O; msg (g 0); msg (G 0)].
unfold t12. unf_qa. repeat ifb.

funapp_droplt DDH1.
funapp_droplt DDH1.
rev_app funapp_O_in DDH1.
rev_app funapp_O_in DDH1.
restr_swap_in 1 3 DDH1.

funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).

funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (reveal x2) (i 1))) .
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))) .
rev_app funapp_O_in DDH1.
assumption.


 auto. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto. auto. auto.  auto. auto. auto. auto. auto.
 auto. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. 
(******************************************)


funapp_droplt DDH1.
funapp_droplt DDH1.
rev_app funapp_O_in DDH1.
rev_app funapp_O_in DDH1.
restr_swap_in 1 3 DDH1.


funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).

funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
rev_app funapp_O_in DDH1.

assumption. auto. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto. auto. auto.  auto. auto. auto. auto. auto.
 auto. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.

(***********************************************************)


restr_swap_in 2 3 DDH1.
funapp_droplt DDH1.
rev_app funapp_O_in DDH1.
restr_swap_in 1 2 DDH1.


funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).

funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
rev_app funapp_O_in DDH1.
restr_swap_in 1 22 DDH1.
assumption. auto. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto. auto. auto.

auto.

(******************************************************)





restr_swap_in 2 3 DDH1.
funapp_droplt DDH1.
rev_app funapp_O_in DDH1.
restr_swap_in 1 2 DDH1.


funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).

funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (to x1) (i 2))).
rev_app funapp_O_in DDH1.
restr_swap_in 1 23 DDH1.
assumption. auto. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto. auto. auto.

auto. auto.
(*******************************************************)



funapp_droplt DDH1.
funapp_droplt DDH1.
rev_app funapp_O_in DDH1.
rev_app funapp_O_in  DDH1.
restr_swap_in 1 3 DDH1.


funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).

funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).

funapp_os 0 ( bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x1) (i 2))).
rev_app funapp_O_in DDH1.
assumption. auto. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto. auto. auto.  auto. auto. auto. auto. auto.
 auto. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.

(****************************************************)


restr_swap 1 20 [t12; bol (EQ_M (reveal x2) (i 2)); bol (EQ_M (reveal x2) (i 1));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 1));
    bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2)); bol (EQ_M (to x3) (i 2));
    bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new); bol (EQ_M (reveal x3) (i 2));
    bol (EQ_M (to x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
    bol (EQ_M (reveal x2) (i 1));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1)); 
    msg (grn 2)1; msg O; msg O; msg (g 0); msg (G 0)] 
   [t12 ; bol (EQ_M (reveal x2) (i 2)); bol (EQ_M (reveal x2) (i 1));
   bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
   bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1));
   bol (EQ_M (reveal x1) (i 1));
   bol
     (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
          (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
        (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
      (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2)); bol (EQ_M (to x3) (i 2));
   bol
     ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
       (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
     (EQ_M (act x1) new); bol (EQ_M (reveal x3) (i 2));
   bol (EQ_M (to x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
   bol (EQ_M (reveal x2) (i 1));
   bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
   bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1)); 
   msg grn4; msg O; msg O; msg (g 0); msg (G 0)].

unfold t12. unf_qa.
repeat ifb.

(*************************)



funapp_droplt DDH1.
funapp_droplt DDH1.
rev_app funapp_O_in DDH1.
rev_app funapp_O_in DDH1.
restr_swap_in 1 3 DDH1.


funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).

funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x2) (i 2))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).

rev_app funapp_O_in DDH1.
assumption. auto. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto. auto. auto.  auto. auto. auto. auto. auto.
 auto. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.


(*********************************)


funapp_droplt DDH1.
funapp_droplt DDH1.
rev_app funapp_O_in DDH1.
rev_app funapp_O_in DDH1.
restr_swap_in 1 3 DDH1.


funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).

funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x2) (i 2))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).

rev_app funapp_O_in DDH1.
assumption. auto. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto. auto. auto.  auto. auto. auto. auto. auto.
 auto. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.

(************************************)



restr_swap_in 2 3 DDH1.
funapp_droplt DDH1.
rev_app funapp_O_in DDH1.
restr_swap_in 1 2 DDH1.


funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).

funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).

rev_app funapp_O_in DDH1.
restr_swap_in 1 23 DDH1.
assumption. auto. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto. auto. auto.

auto. auto.

(**************************************)


restr_swap_in 2 3 DDH1.
funapp_droplt DDH1.
rev_app funapp_O_in DDH1.
restr_swap_in 1 2 DDH1.


funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).

funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (to x1) (i 2))).
rev_app funapp_O_in DDH1.
restr_swap_in 1 24 DDH1. 
assumption. auto. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto. auto. auto.

auto. auto. auto.

(*******************************************************************)



funapp_droplt DDH1.
funapp_droplt DDH1.
rev_app funapp_O_in DDH1.
rev_app funapp_O_in DDH1.
restr_swap_in 1 3 DDH1.


funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).

funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x2) (i 2))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (to x1) (i 2))).

rev_app funapp_O_in DDH1.
assumption. auto. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto. auto. auto.  auto. auto. auto. auto. auto.
 auto. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.

(*********************************************************************)
restr_swap 1 21 [t12 ; bol (EQ_M (to x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
    bol (EQ_M (reveal x2) (i 1));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 1));
    bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2)); bol (EQ_M (to x3) (i 2));
    bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new); bol (EQ_M (reveal x3) (i 2));
    bol (EQ_M (to x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
    bol (EQ_M (reveal x2) (i 1));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1)); 
    msg (grn 2)1; msg O; msg acc; msg (g 0); msg (G 0)]
   [t12 ; bol (EQ_M (to x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
   bol (EQ_M (reveal x2) (i 1));
   bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
   bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1));
   bol (EQ_M (reveal x1) (i 1));
   bol
     (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
          (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
        (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
      (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2)); bol (EQ_M (to x3) (i 2));
   bol
     ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
       (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
     (EQ_M (act x1) new); bol (EQ_M (reveal x3) (i 2));
   bol (EQ_M (to x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
   bol (EQ_M (reveal x2) (i 1));
   bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
   bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1)); 
   msg grn4; msg O; msg acc ; msg (g 0); msg (G 0)].
unfold t12 . unf_qa.
repeat ifb.
(***************************************)
rev_app funapp_acc_in DDH1.
aply_in 2 funapp_droplt DDH1.
restr_swap_in 1 2 DDH1.
rev_app funapp_O_in DDH1.
restr_swap_in 1 2 DDH1.

funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
 
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0  (bol (EQ_M (to x2) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).


rev_app funapp_O_in DDH1.
assumption. 
 do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto. auto. auto.  auto. auto. auto. auto. auto.
 auto. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.


(****************************************************************)

rev_app funapp_acc_in DDH1.
aply_in 2 funapp_droplt DDH1.
restr_swap_in 1 2 DDH1.
rev_app funapp_O_in DDH1.
restr_swap_in 1 2 DDH1.

funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
 
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0  (bol (EQ_M (to x2) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).

rev_app funapp_O_in DDH1.
assumption. 
 do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto. auto. auto.  auto. auto. auto. auto. auto.
 auto. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.

(*********************************************************)



restr_swap_in 2 3 DDH1.
aply_in 1 funapp_droplt DDH1.

rev_app funapp_O_in DDH1.
restr_swap_in 1 2 DDH1.

funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
 
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0  (bol (EQ_M (to x2) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
rev_app funapp_acc_in DDH1.
restr_swap_in 1 24 DDH1.
assumption. 
 do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto. auto. auto.  auto. auto. auto. auto. auto.
 auto. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.


(**********************************************************************)


restr_swap_in 2 3 DDH1.
aply_in 1 funapp_droplt DDH1.

rev_app funapp_O_in DDH1.
restr_swap_in 1 2 DDH1.

funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
 
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0  (bol (EQ_M (to x2) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 ( bol (EQ_M (to x1) (i 2))).
rev_app funapp_acc_in DDH1.
restr_swap_in 1 25 DDH1.
assumption. 
 do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto. auto. auto.  auto. auto. auto. auto. auto.
 auto. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.


(********************************************************************************)

rev_app funapp_acc_in DDH1.
aply_in 2 funapp_droplt DDH1.
restr_swap_in 1 2 DDH1.
rev_app funapp_O_in DDH1.
restr_swap_in 1 2 DDH1.

funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
 
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0  (bol (EQ_M (to x2) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (to x1) (i 2))).
rev_app funapp_O_in DDH1.
assumption. 
 do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto. auto. auto.  auto. auto. auto. auto. auto.
 auto. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.

(*****************************************************************)

restr_swap 1 22 [t12 ; bol (EQ_M (to x2) (i 2)); bol (EQ_M (to x2) (i 1));
    bol (EQ_M (reveal x2) (i 2)); bol (EQ_M (reveal x2) (i 1));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 1));
    bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2)); bol (EQ_M (to x3) (i 2));
    bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new); bol (EQ_M (reveal x3) (i 2));
    bol (EQ_M (to x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
    bol (EQ_M (reveal x2) (i 1));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1)); 
    msg (grn 2)1; msg O; msg (grn 1); msg (g 0); msg (G 0)]
   [t12 ; bol (EQ_M (to x2) (i 2)); bol (EQ_M (to x2) (i 1));
   bol (EQ_M (reveal x2) (i 2)); bol (EQ_M (reveal x2) (i 1));
   bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
   bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1));
   bol (EQ_M (reveal x1) (i 1));
   bol
     (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
          (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
        (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
      (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2)); bol (EQ_M (to x3) (i 2));
   bol
     ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
       (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
     (EQ_M (act x1) new); bol (EQ_M (reveal x3) (i 2));
   bol (EQ_M (to x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
   bol (EQ_M (reveal x2) (i 1));
   bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
   bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1)); 
   msg grn4; msg O; msg (grn 1); msg (g 0); msg (G 0)].
unfold t12; unf_qa.

repeat ifb.

(***********************************************************************)
restr_swap_in 2 3 DDH1.
funapp_droplt DDH1.
rev_app funapp_O_in DDH1.
restr_swap_in 1 2 DDH1.

funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
 
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0  (bol (EQ_M (to x2) (i 1))).
funapp_os 0  (bol (EQ_M (to x2) (i 2))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).

rev_app funapp_O_in DDH1.
assumption. 
 do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto. auto. auto.  auto. auto. auto. auto. auto.
 auto. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.

(****************************************************************************)

restr_swap_in 2 3 DDH1.
funapp_droplt DDH1.
rev_app funapp_O_in DDH1.
restr_swap_in 1 2 DDH1.

funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
 
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0  (bol (EQ_M (to x2) (i 1))).
funapp_os 0  (bol (EQ_M (to x2) (i 2))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
rev_app funapp_O_in DDH1.
assumption. 
 do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto. auto. auto.  auto. auto. auto. auto. auto.
 auto. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.

(*************************************************************************)

restr_swap_in 2 3 DDH1.
funapp_droplt DDH1.

funapp_elt_in 1 1 .


funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
 
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0  (bol (EQ_M (to x2) (i 1))).
funapp_os 0  (bol (EQ_M (to x2) (i 2))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
rev_app funapp_O_in DDH1.
restr_swap_in 1 24 DDH1.
assumption. 
 do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto. auto. auto.  auto. auto. auto. auto. auto.
 auto. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.


(*********************************************)


restr_swap_in 2 3 DDH1.
funapp_droplt DDH1.

funapp_elt_in 1 1 .


funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
 
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0  (bol (EQ_M (to x2) (i 1))).
funapp_os 0  (bol (EQ_M (to x2) (i 2))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (to x1) (i 2))).
rev_app funapp_O_in DDH1.
restr_swap_in 1 25 DDH1.
assumption. 
 do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto. auto. auto.  auto. auto. auto. auto. auto.
 auto. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.

(******************************************************************)


restr_swap_in 2 3 DDH1.
funapp_droplt DDH1.
rev_app funapp_O_in DDH1.
restr_swap_in 1 2 DDH1.



funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
 
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0  (bol (EQ_M (to x2) (i 1))).
funapp_os 0  (bol (EQ_M (to x2) (i 2))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (to x1) (i 2))).
rev_app funapp_O_in DDH1.

assumption. 
 do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto. auto. auto.  auto. auto. auto. auto. auto.
 auto. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.

(********************************************************************)

restr_swap 1 22 [t12; bol (EQ_M (to x2) (i 2)); bol (EQ_M (to x2) (i 1));
    bol (EQ_M (reveal x2) (i 2)); bol (EQ_M (reveal x2) (i 1));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 1));
    bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2)); bol (EQ_M (to x3) (i 2));
    bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new); bol (EQ_M (reveal x3) (i 2));
    bol (EQ_M (to x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
    bol (EQ_M (reveal x2) (i 1));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1)); 
    msg (grn 2)1; msg O; msg O; msg (g 0); msg (G 0)] [t12 ; bol (EQ_M (to x2) (i 2)); bol (EQ_M (to x2) (i 1));
   bol (EQ_M (reveal x2) (i 2)); bol (EQ_M (reveal x2) (i 1));
   bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
   bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1));
   bol (EQ_M (reveal x1) (i 1));
   bol
     (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
          (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
        (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
      (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2)); bol (EQ_M (to x3) (i 2));
   bol
     ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
       (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
     (EQ_M (act x1) new); bol (EQ_M (reveal x3) (i 2));
   bol (EQ_M (to x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
   bol (EQ_M (reveal x2) (i 1));
   bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
   bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1)); 
   msg grn4; msg O; msg O; msg (g 0); msg (G 0)].
unfold t12; unf_qa.
repeat ifb.

(************************************)
aply_in 2 funapp_droplt DDH1.
aply_in 2 funapp_O_in DDH1.

restr_swap_in 2 4 DDH1.
restr_swap_in 3 5 DDH1.
funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0  (bol (EQ_M (to x2) (i 1))).
funapp_os 0  (bol (EQ_M (to x2) (i 2))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
rev_app funapp_O_in  DDH1; do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto.   auto. auto. auto.   auto. auto. auto.   

(*********************************************************)

aply_in 2 funapp_droplt DDH1.
aply_in 2 funapp_O_in DDH1.

restr_swap_in 2 4 DDH1.
restr_swap_in 3 5 DDH1.
funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0  (bol (EQ_M (to x2) (i 1))).
funapp_os 0  (bol (EQ_M (to x2) (i 2))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
rev_app funapp_O_in  DDH1; do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto.   auto. auto. auto.   auto. auto. auto.   auto.


(****************************************************************)
restr_swap_in 2 3 DDH1.
aply_in 1  funapp_droplt DDH1.
rev_app funapp_O_in DDH1.
restr_swap_in 1 2 DDH1.


funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0  (bol (EQ_M (to x2) (i 1))).
funapp_os 0  (bol (EQ_M (to x2) (i 2))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0 (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
rev_app funapp_O_in  DDH1. restr_swap_in 1 25 DDH1. auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto.   auto. auto. auto.   auto. auto. auto.   auto. auto.

(***********************************************************************)

restr_swap_in 2 3 DDH1.
aply_in 1  funapp_droplt DDH1.
rev_app funapp_O_in DDH1.
restr_swap_in 1 2 DDH1.


funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0  (bol (EQ_M (to x2) (i 1))).
funapp_os 0  (bol (EQ_M (to x2) (i 2))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0 (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (to x1) (i 2))).
rev_app funapp_O_in  DDH1. restr_swap_in 1 26 DDH1. auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto.   auto. auto. auto.   auto. auto. auto.   auto. auto. auto.


(**************************************************************************)


aply_in 2 funapp_droplt DDH1.
aply_in 2 funapp_O_in DDH1.

restr_swap_in 2 4 DDH1.
restr_swap_in 3 5 DDH1.
funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0  (bol (EQ_M (to x2) (i 1))).
funapp_os 0  (bol (EQ_M (to x2) (i 2))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0 (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (to x1) (i 2))).
rev_app funapp_O_in  DDH1; do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto.   auto. auto. auto.   auto. auto. auto.   auto. auto. auto.

unfold qa01. repeat ifb.

restr_swap 1 20  [t12 ; bol (EQ_M (reveal x2) (i 1)); bol (EQ_M (to x1) (i 2));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 1));
    bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2)); bol (EQ_M (to x3) (i 2));
    bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new); bol (EQ_M (reveal x3) (i 2));
    bol (EQ_M (to x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
    bol (EQ_M (reveal x2) (i 1));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1)); 
    msg (grn 2)1; msg O; msg O; msg (g 0); msg (G 0)]  [t12 ; bol (EQ_M (reveal x2) (i 1)); bol (EQ_M (to x1) (i 2));
   bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
   bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1));
   bol (EQ_M (reveal x1) (i 1));
   bol
     (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
          (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
        (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
      (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2)); bol (EQ_M (to x3) (i 2));
   bol
     ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
       (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
     (EQ_M (act x1) new); bol (EQ_M (reveal x3) (i 2));
   bol (EQ_M (to x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
   bol (EQ_M (reveal x2) (i 1));
   bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
   bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1)); 
   msg grn4; msg O; msg O; msg (g 0); msg (G 0)].
unfold t12 ; unf_qa. repeat ifb.

(*******************************************************************)



aply_in 2 funapp_droplt DDH1.
aply_in 2 funapp_O_in DDH1.

restr_swap_in 2 4 DDH1.
restr_swap_in 3 5 DDH1.
funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x1) (i 2))).
funapp_os 0 (bol (EQ_M (reveal x2) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).

rev_app funapp_O_in  DDH1. assumption. auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto.   auto. auto. auto.   auto. auto. auto.   auto.

(***********************************************************)

aply_in 2 funapp_droplt DDH1.
aply_in 2 funapp_O_in DDH1.

restr_swap_in 2 4 DDH1.
restr_swap_in 3 5 DDH1.
funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x1) (i 2))).
funapp_os 0 (bol (EQ_M (reveal x2) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
rev_app funapp_O_in  DDH1. assumption. auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto.   auto. auto. auto.   auto. auto. auto.   auto.

(*******************************************************************************)



restr_swap_in 2 3 DDH1.
aply_in 1  funapp_droplt DDH1.
rev_app funapp_O_in DDH1.
restr_swap_in 1 2 DDH1.


funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x1) (i 2))).
funapp_os 0 (bol (EQ_M (reveal x2) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0 (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).

rev_app funapp_O_in  DDH1. restr_swap_in 1 23  DDH1. assumption. auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto.   auto. auto. auto.   auto. auto. auto.   auto. auto. auto.

(*********************************************************************)



restr_swap_in 2 3 DDH1.
aply_in 1  funapp_droplt DDH1.
rev_app funapp_O_in DDH1.
restr_swap_in 1 2 DDH1.


funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x1) (i 2))).
funapp_os 0 (bol (EQ_M (reveal x2) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0 (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x1) (i 2))).
rev_app funapp_O_in  DDH1. restr_swap_in 1 24 DDH1. assumption. auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto.   auto. auto. auto.   auto. auto. auto.   auto. auto. auto.


(************************************)

aply_in 2 funapp_droplt DDH1.
aply_in 2 funapp_O_in DDH1.

restr_swap_in 2 4 DDH1.
restr_swap_in 3 5 DDH1.
funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x1) (i 2))).
funapp_os 0 (bol (EQ_M (reveal x2) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x1) (i 2))).
rev_app funapp_O_in  DDH1. assumption. auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto.   auto. auto. auto.   auto. auto. auto.   auto.

Admitted.
