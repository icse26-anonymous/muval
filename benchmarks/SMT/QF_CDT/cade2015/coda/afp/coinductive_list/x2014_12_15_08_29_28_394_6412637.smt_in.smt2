;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort A_llist_bool_fun$ 0 )
(declare-sort A_llist_a_llist_fun$ 0 )
(declare-sort A_llist_a_llist_bool_fun_fun$ 0 )
(declare-codatatypes ()((A_llist$ (lNil$ )(lCons$ (lhd$ A$ )(ltl$ A_llist$ )))))
(declare-sort Nat_option$ 0)
(declare-sort Enat$ 0)
(declare-fun none$ ()Nat_option$)
(declare-fun the$ (Nat_option$)Nat$)
(declare-fun some$ (Nat$ )Nat_option$)
(declare-fun rep_enat$ (Enat$)Nat_option$)
(declare-fun abs_enat$ (Nat_option$ )Enat$)
(declare-fun p$ ()A_bool_fun$ )
(declare-fun uu$ (A$ )A_llist_a_llist_fun$ )
(declare-fun uua$ ()A_llist_a_llist_fun$ )
(declare-fun ldrop$ (Enat$ )A_llist_a_llist_fun$ )
(declare-fun fun_app$ (A_llist_a_llist_fun$ A_llist$ )A_llist$ )
(declare-fun lfilter$ (A_bool_fun$ )A_llist_a_llist_fun$ )
(declare-fun lprefix$ ()A_llist_a_llist_bool_fun_fun$ )
(declare-fun fun_app$a (A_llist_bool_fun$ A_llist$ )Bool )
(declare-fun fun_app$b (A_llist_a_llist_bool_fun_fun$ A_llist$ )A_llist_bool_fun$ )
(declare-fun monotone$ (A_llist_a_llist_bool_fun_fun$ A_llist_a_llist_bool_fun_fun$ A_llist_a_llist_fun$ )Bool )
(declare-fun ldropWhile$ (A_bool_fun$ )A_llist_a_llist_fun$ )
(declare-fun ltakeWhile$ (A_bool_fun$ )A_llist_a_llist_fun$ )
(declare-fun finite_lprefix$ ()A_llist_a_llist_bool_fun_fun$ )
(assert (! (forall ((?v0 A_llist$ ))(! (= (fun_app$ uua$ ?v0 )(ltl$ ?v0 )):pattern ((fun_app$ uua$ ?v0 )))):named a0 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(! (= (fun_app$ (uu$ ?v0 )?v1 )(lCons$ ?v0 ?v1 )):pattern ((fun_app$ (uu$ ?v0 )?v1 )))):named a1 ))
(assert (! (not (monotone$ lprefix$ lprefix$ (lfilter$ p$ ))):named a2 ))
(assert (! (forall ((?v0 A_llist$ ))(fun_app$a (fun_app$b lprefix$ ?v0 )?v0 )):named a3 ))
(assert (! (forall ((?v0 A_llist$ ))(fun_app$a (fun_app$b lprefix$ ?v0 )?v0 )):named a4 ))
(assert (! (forall ((?v0 A_llist_a_llist_fun$ )(?v1 A_llist$ )(?v2 A_llist$ )(?v3 A_llist_a_llist_fun$ )(?v4 A_llist_a_llist_bool_fun_fun$ ))(=> (and (forall ((?v5 A_llist$ ))(= (fun_app$ ?v0 ?v5 )(ite (fun_app$a (fun_app$b lprefix$ ?v5 )?v1 )?v2 (fun_app$ ?v3 ?v5 ))))(and (forall ((?v5 A_llist$ )(?v6 A_llist$ ))(=> (and (fun_app$a (fun_app$b lprefix$ ?v5 )?v6 )(not (fun_app$a (fun_app$b lprefix$ ?v5 )?v1 )))(fun_app$a (fun_app$b ?v4 (fun_app$ ?v3 ?v5 ))(fun_app$ ?v3 ?v6 ))))(and (forall ((?v5 A_llist$ ))(=> (not (fun_app$a (fun_app$b lprefix$ ?v5 )?v1 ))(fun_app$a (fun_app$b ?v4 ?v2 )(fun_app$ ?v3 ?v5 ))))(fun_app$a (fun_app$b ?v4 ?v2 )?v2 ))))(monotone$ lprefix$ ?v4 ?v0 ))):named a5 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (and (fun_app$a (fun_app$b lprefix$ ?v0 )?v1 )(fun_app$a (fun_app$b lprefix$ ?v1 )?v0 ))(= ?v0 ?v1 ))):named a6 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (and (fun_app$a (fun_app$b lprefix$ ?v0 )?v1 )(fun_app$a (fun_app$b lprefix$ ?v1 )?v0 ))(= ?v0 ?v1 ))):named a7 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(=> (and (fun_app$a (fun_app$b lprefix$ ?v0 )?v1 )(fun_app$a (fun_app$b lprefix$ ?v2 )?v1 ))(or (fun_app$a (fun_app$b lprefix$ ?v0 )?v2 )(fun_app$a (fun_app$b lprefix$ ?v2 )?v0 )))):named a8 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(=> (and (fun_app$a (fun_app$b lprefix$ ?v0 )?v1 )(fun_app$a (fun_app$b lprefix$ ?v1 )?v2 ))(fun_app$a (fun_app$b lprefix$ ?v0 )?v2 ))):named a9 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(=> (and (fun_app$a (fun_app$b lprefix$ ?v0 )?v1 )(fun_app$a (fun_app$b lprefix$ ?v1 )?v2 ))(fun_app$a (fun_app$b lprefix$ ?v0 )?v2 ))):named a10 ))
(assert (! (forall ((?v0 A_llist_a_llist_bool_fun_fun$ )(?v1 A_llist_a_llist_bool_fun_fun$ )(?v2 A_llist_a_llist_fun$ ))(= (monotone$ ?v0 ?v1 ?v2 )(forall ((?v3 A_llist$ )(?v4 A_llist$ ))(=> (fun_app$a (fun_app$b ?v0 ?v3 )?v4 )(fun_app$a (fun_app$b ?v1 (fun_app$ ?v2 ?v3 ))(fun_app$ ?v2 ?v4 )))))):named a11 ))
(assert (! (forall ((?v0 A_llist_a_llist_bool_fun_fun$ )(?v1 A_llist_a_llist_bool_fun_fun$ )(?v2 A_llist_a_llist_fun$ ))(=> (forall ((?v3 A_llist$ )(?v4 A_llist$ ))(=> (fun_app$a (fun_app$b ?v0 ?v3 )?v4 )(fun_app$a (fun_app$b ?v1 (fun_app$ ?v2 ?v3 ))(fun_app$ ?v2 ?v4 ))))(monotone$ ?v0 ?v1 ?v2 ))):named a12 ))
(assert (! (forall ((?v0 A_llist_a_llist_bool_fun_fun$ )(?v1 A_llist_a_llist_bool_fun_fun$ )(?v2 A_llist_a_llist_fun$ )(?v3 A_llist$ )(?v4 A_llist$ ))(=> (and (monotone$ ?v0 ?v1 ?v2 )(fun_app$a (fun_app$b ?v0 ?v3 )?v4 ))(fun_app$a (fun_app$b ?v1 (fun_app$ ?v2 ?v3 ))(fun_app$ ?v2 ?v4 )))):named a13 ))
(assert (! (forall ((?v0 A_bool_fun$ ))(monotone$ lprefix$ lprefix$ (ldropWhile$ ?v0 ))):named a14 ))
(assert (! (= finite_lprefix$ lprefix$ ):named a15 ))
(assert (! (forall ((?v0 Enat$ ))(monotone$ lprefix$ lprefix$ (ldrop$ ?v0 ))):named a16 ))
(assert (! (forall ((?v0 A$ ))(monotone$ lprefix$ lprefix$ (uu$ ?v0 ))):named a17 ))
(assert (! (forall ((?v0 A_bool_fun$ ))(monotone$ lprefix$ lprefix$ (ltakeWhile$ ?v0 ))):named a18 ))
(assert (! (monotone$ lprefix$ lprefix$ uua$ ):named a19 ))
(check-sat )
;(get-unsat-core )
