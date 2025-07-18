;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort Enat_enat_fun$ 0 )
(declare-sort Nat_option$ 0)
(declare-sort Enat$ 0)
(declare-fun none$ ()Nat_option$)
(declare-fun the$ (Nat_option$)Nat$)
(declare-fun some$ (Nat$ )Nat_option$)
(declare-fun rep_enat$ (Enat$)Nat_option$)
(declare-fun abs_enat$ (Nat_option$ )Enat$)
(declare-codatatypes ()((A_llist$ (lNil$ )(lCons$ (lhd$ A$ )(ltl$ A_llist$ )))))
(declare-fun n$ ()Enat$ )
(declare-fun xs$ ()A_llist$ )
(declare-fun zero$ ()Enat$ )
(declare-fun ldrop$ (Enat$ A_llist$ )A_llist$ )
(declare-fun minus$ (Enat$ )Enat_enat_fun$ )
(declare-fun fun_app$ (Enat_enat_fun$ Enat$ )Enat$ )
(declare-fun llength$ (A_llist$ )Enat$ )
(declare-fun infinity$ ()Enat$ )
(assert (! (not (= (llength$ (ldrop$ n$ xs$ ))(ite (= n$ infinity$ )zero$ (fun_app$ (minus$ (llength$ xs$ ))n$ )))):named a0 ))
(assert (! (forall ((?v0 A_llist$ ))(= (ldrop$ zero$ ?v0 )?v0 )):named a1 ))
(assert (! (forall ((?v0 Enat$ ))(! (=> (not (= ?v0 infinity$ ))(= (fun_app$ (minus$ ?v0 )?v0 )zero$ )):pattern ((minus$ ?v0 )))):named a2 ))
(assert (! (forall ((?v0 Enat$ ))(! (= (fun_app$ (minus$ infinity$ )?v0 )infinity$ ):pattern ((fun_app$ (minus$ infinity$ )?v0 )))):named a3 ))
(assert (! (forall ((?v0 Enat$ ))(= (fun_app$ (minus$ ?v0 )zero$ )?v0 )):named a4 ))
(assert (! (forall ((?v0 Enat$ ))(= (fun_app$ (minus$ zero$ )?v0 )zero$ )):named a5 ))
(assert (! (forall ((?v0 Enat$ ))(= (= zero$ ?v0 )(= ?v0 zero$ ))):named a6 ))
(check-sat )
;(get-unsat-core )
