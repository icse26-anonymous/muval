;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_set$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort A_a_bool_fun_fun$ 0 )
(declare-sort A_llist_bool_fun$ 0 )
(declare-sort A_llist_a_set_fun$ 0 )
(declare-sort Nat_option$ 0)
(declare-sort Enat$ 0)
(declare-fun none$ ()Nat_option$)
(declare-fun the$ (Nat_option$)Nat$)
(declare-fun some$ (Nat$ )Nat_option$)
(declare-fun rep_enat$ (Enat$)Nat_option$)
(declare-fun abs_enat$ (Nat_option$ )Enat$)
(declare-codatatypes ()((A_llist$ (lNil$ )(lCons$ (lhd$ A$ )(ltl$ A_llist$ )))))
(declare-fun n$ ()Nat$ )
(declare-fun enat$ (Nat$ )Enat$ )
(declare-fun plus$ (Enat$ Enat$ )Enat$ )
(declare-fun fun_app$ (A_llist_bool_fun$ A_llist$ )Bool )
(declare-fun llength$ (A_llist$ )Enat$ )
(declare-fun llexord$ (A_a_bool_fun_fun$ A_llist$ A_llist$ )Bool )
(declare-fun lmember$ (A$ )A_llist_bool_fun$ )
(declare-fun fun_app$a (A_llist_a_set_fun$ A_llist$ )A_set$ )
(declare-fun gen_lset$ (A_set$ )A_llist_a_set_fun$ )
(declare-fun ldistinct$ (A_llist$ )Bool )
(declare-fun pred_llist$ (A_bool_fun$ A_llist$ )Bool )
(declare-fun gen_llength$ (Nat$ A_llist$ )Enat$ )
(assert (! (not (= (gen_llength$ n$ lNil$ )(enat$ n$ ))):named a0 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(= (= (enat$ ?v0 )(enat$ ?v1 ))(= ?v0 ?v1 ))):named a1 ))
(assert (! (forall ((?v0 A$ ))(! (= (fun_app$ (lmember$ ?v0 )lNil$ )false ):pattern ((lmember$ ?v0 )))):named a2 ))
(assert (! (forall ((?v0 A_set$ ))(! (= (fun_app$a (gen_lset$ ?v0 )lNil$ )?v0 ):pattern ((gen_lset$ ?v0 )))):named a3 ))
(assert (! (forall ((?v0 A_bool_fun$ ))(pred_llist$ ?v0 lNil$ )):named a4 ))
(assert (! (ldistinct$ lNil$ ):named a5 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_llist$ ))(! (= (gen_llength$ ?v0 ?v1 )(plus$ (enat$ ?v0 )(llength$ ?v1 ))):pattern ((gen_llength$ ?v0 ?v1 )))):named a6 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A_llist$ ))(llexord$ ?v0 lNil$ ?v1 )):named a7 ))
(assert (! (forall ((?v0 Enat$ )(?v1 Nat$ )(?v2 Enat$ ))(= (= (plus$ ?v0 (enat$ ?v1 ))(plus$ ?v2 (enat$ ?v1 )))(= ?v0 ?v2 ))):named a8 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Enat$ )(?v2 Enat$ ))(= (= (plus$ (enat$ ?v0 )?v1 )(plus$ (enat$ ?v0 )?v2 ))(= ?v1 ?v2 ))):named a9 ))
(assert (! (forall ((?v0 Enat$ )(?v1 Enat$ )(?v2 Enat$ )(?v3 Enat$ ))(= (plus$ (plus$ ?v0 ?v1 )(plus$ ?v2 ?v3 ))(plus$ (plus$ ?v0 ?v2 )(plus$ ?v1 ?v3 )))):named a10 ))
(check-sat )
;(get-unsat-core )
