;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort B$ 0 )
(declare-sort Nat$ 0 )
(declare-sort Nat_nat_fun$ 0 )
(declare-sort Nat_enat_fun$ 0 )
(declare-sort Nat_option$ 0)
(declare-sort Enat$ 0)
(declare-fun none$ ()Nat_option$)
(declare-fun the$ (Nat_option$)Nat$)
(declare-fun some$ (Nat$ )Nat_option$)
(declare-fun rep_enat$ (Enat$)Nat_option$)
(declare-fun abs_enat$ (Nat_option$ )Enat$)
(declare-codatatypes ()((B_llist$ (lNil$ )(lCons$ (lhd$ B$ )(ltl$ B_llist$ )))))
(declare-fun na$ ()Nat$ )
(declare-fun zs$ ()B_llist$ )
(declare-fun suc$ (Nat$ )Nat$ )
(declare-fun eSuc$ (Enat$ )Enat$ )
(declare-fun enat$ (Nat$ )Enat$ )
(declare-fun fun_app$ (Nat_nat_fun$ Nat$ )Nat$ )
(declare-fun less_eq$ (Enat$ Enat$ )Bool )
(declare-fun llength$ (B_llist$ )Enat$ )
(declare-fun fun_app$a (Nat_enat_fun$ Nat$ )Enat$ )
(declare-fun less_eq$a (Nat$ Nat$ )Bool )
(declare-fun the_enat$ (Enat$ )Nat$ )
(assert (! (not (= (the_enat$ (eSuc$ (llength$ zs$ )))(suc$ (the_enat$ (llength$ zs$ ))))):named a0 ))
(assert (! (less_eq$ (llength$ zs$ )(enat$ na$ )):named a1 ))
(assert (! (forall ((?v0 Enat$ )(?v1 Enat$ ))(= (= (eSuc$ ?v0 )(eSuc$ ?v1 ))(= ?v0 ?v1 ))):named a2 ))
(assert (! (forall ((?v0 Enat$ )(?v1 Enat$ ))(= (= (eSuc$ ?v0 )(eSuc$ ?v1 ))(= ?v0 ?v1 ))):named a3 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(= (= (suc$ ?v0 )(suc$ ?v1 ))(= ?v0 ?v1 ))):named a4 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(= (= (suc$ ?v0 )(suc$ ?v1 ))(= ?v0 ?v1 ))):named a5 ))
(assert (! (forall ((?v0 Enat$ )(?v1 Nat$ ))(= (= (eSuc$ ?v0 )(enat$ ?v1 ))(exists ((?v2 Nat$ ))(and (= ?v1 (suc$ ?v2 ))(= ?v0 (enat$ ?v2 )))))):named a6 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Enat$ ))(= (= (enat$ ?v0 )(eSuc$ ?v1 ))(exists ((?v2 Nat$ ))(and (= ?v0 (suc$ ?v2 ))(= (enat$ ?v2 )?v1 ))))):named a7 ))
(assert (! (forall ((?v0 Nat$ ))(= (eSuc$ (enat$ ?v0 ))(enat$ (suc$ ?v0 )))):named a8 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(=> (= (suc$ ?v0 )(suc$ ?v1 ))(= ?v0 ?v1 ))):named a9 ))
(assert (! (forall ((?v0 Nat$ ))(not (= ?v0 (suc$ ?v0 )))):named a10 ))
(assert (! (forall ((?v0 Enat$ )(?v1 Enat$ ))(= (less_eq$ (eSuc$ ?v0 )(eSuc$ ?v1 ))(less_eq$ ?v0 ?v1 ))):named a11 ))
(assert (! (forall ((?v0 B$ )(?v1 B_llist$ ))(! (= (llength$ (lCons$ ?v0 ?v1 ))(eSuc$ (llength$ ?v1 ))):pattern ((lCons$ ?v0 ?v1 )))):named a12 ))
(assert (! (forall ((?v0 B$ )(?v1 B_llist$ )(?v2 B$ )(?v3 B_llist$ ))(= (= (lCons$ ?v0 ?v1 )(lCons$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a13 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(= (= (enat$ ?v0 )(enat$ ?v1 ))(= ?v0 ?v1 ))):named a14 ))
(assert (! (forall ((?v0 Enat$ )(?v1 Nat$ ))(=> (less_eq$ ?v0 (enat$ ?v1 ))(exists ((?v2 Nat$ ))(= ?v0 (enat$ ?v2 ))))):named a15 ))
(assert (! (forall ((?v0 Nat_nat_fun$ )(?v1 Nat$ )(?v2 Nat$ ))(=> (and (forall ((?v3 Nat$ ))(less_eq$a (fun_app$ ?v0 ?v3 )(fun_app$ ?v0 (suc$ ?v3 ))))(less_eq$a ?v1 ?v2 ))(less_eq$a (fun_app$ ?v0 ?v1 )(fun_app$ ?v0 ?v2 )))):named a16 ))
(assert (! (forall ((?v0 Nat_enat_fun$ )(?v1 Nat$ )(?v2 Nat$ ))(=> (and (forall ((?v3 Nat$ ))(less_eq$ (fun_app$a ?v0 ?v3 )(fun_app$a ?v0 (suc$ ?v3 ))))(less_eq$a ?v1 ?v2 ))(less_eq$ (fun_app$a ?v0 ?v1 )(fun_app$a ?v0 ?v2 )))):named a17 ))
(check-sat )
;(get-unsat-core )
