;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort A_llist_bool_fun$ 0 )
(declare-sort A_llist_a_llist_bool_fun_fun$ 0 )
(declare-sort A_llist$ 0)
(declare-fun lNil$ ()A_llist$)
(declare-fun lhd$ (A_llist$)A$)
(declare-fun ltl$ (A_llist$)A_llist$)
(declare-fun lCons$ (A$ A_llist$ )A_llist$)
(declare-sort Nat_option$ 0)
(declare-sort Enat$ 0)
(declare-fun none$ ()Nat_option$)
(declare-fun the$ (Nat_option$)Nat$)
(declare-fun some$ (Nat$ )Nat_option$)
(declare-fun rep_enat$ (Enat$)Nat_option$)
(declare-fun abs_enat$ (Nat_option$ )Enat$)
(declare-fun p$ ()A_bool_fun$ )
(declare-fun xs$ ()A_llist$ )
(declare-fun llcp$ (A_llist$ A_llist$ )Enat$ )
(declare-fun ldrop$ (Enat$ A_llist$ )A_llist$ )
(declare-fun fun_app$ (A_llist_bool_fun$ A_llist$ )Bool )
(declare-fun lappend$ (A_llist$ A_llist$ )A_llist$ )
(declare-fun less_eq$ (Enat$ Enat$ )Bool )
(declare-fun llength$ (A_llist$ )Enat$ )
(declare-fun lprefix$ ()A_llist_a_llist_bool_fun_fun$ )
(declare-fun fun_app$a (A_llist_a_llist_bool_fun_fun$ A_llist$ )A_llist_bool_fun$ )
(declare-fun ldropWhile$ (A_bool_fun$ A_llist$ )A_llist$ )
(declare-fun ltakeWhile$ (A_bool_fun$ A_llist$ )A_llist$ )
(declare-fun finite_lprefix$ ()A_llist_a_llist_bool_fun_fun$ )
(assert (! (not (fun_app$ (fun_app$a lprefix$ (ldrop$ (llength$ (ltakeWhile$ p$ xs$ ))xs$ ))(ldropWhile$ p$ xs$ ))):named a0 ))
(assert (! (forall ((?v0 A_llist$ ))(fun_app$ (fun_app$a lprefix$ ?v0 )?v0 )):named a1 ))
(assert (! (forall ((?v0 A_llist$ ))(fun_app$ (fun_app$a lprefix$ ?v0 )?v0 )):named a2 ))
(assert (! (fun_app$ (fun_app$a lprefix$ (ldropWhile$ p$ xs$ ))(ldrop$ (llength$ (ltakeWhile$ p$ xs$ ))xs$ )):named a3 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A_llist$ ))(= (= (llength$ (ltakeWhile$ ?v0 ?v1 ))(llength$ ?v1 ))(= (ltakeWhile$ ?v0 ?v1 )?v1 ))):named a4 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (and (fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )(= (llength$ ?v0 )(llength$ ?v1 )))(= ?v0 ?v1 ))):named a5 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (and (fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )(fun_app$ (fun_app$a lprefix$ ?v1 )?v0 ))(= ?v0 ?v1 ))):named a6 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (and (fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )(fun_app$ (fun_app$a lprefix$ ?v1 )?v0 ))(= ?v0 ?v1 ))):named a7 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(=> (and (fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )(fun_app$ (fun_app$a lprefix$ ?v2 )?v1 ))(or (fun_app$ (fun_app$a lprefix$ ?v0 )?v2 )(fun_app$ (fun_app$a lprefix$ ?v2 )?v0 )))):named a8 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(=> (and (fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )(fun_app$ (fun_app$a lprefix$ ?v1 )?v2 ))(fun_app$ (fun_app$a lprefix$ ?v0 )?v2 ))):named a9 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(=> (and (fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )(fun_app$ (fun_app$a lprefix$ ?v1 )?v2 ))(fun_app$ (fun_app$a lprefix$ ?v0 )?v2 ))):named a10 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A_llist$ ))(fun_app$ (fun_app$a lprefix$ (ltakeWhile$ ?v0 ?v1 ))?v1 )):named a11 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(! (=> (fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )(= (llcp$ ?v1 ?v0 )(llength$ ?v0 ))):pattern ((llcp$ ?v1 ?v0 )))):named a12 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(! (=> (fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )(= (llcp$ ?v0 ?v1 )(llength$ ?v0 ))):pattern ((llcp$ ?v0 ?v1 )))):named a13 ))
(assert (! (= finite_lprefix$ lprefix$ ):named a14 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A_llist$ ))(= (lappend$ (ltakeWhile$ ?v0 ?v1 )(ldropWhile$ ?v0 ?v1 ))?v1 )):named a15 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A_llist$ ))(less_eq$ (llength$ (ltakeWhile$ ?v0 ?v1 ))(llength$ ?v1 ))):named a16 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )(less_eq$ (llength$ ?v0 )(llength$ ?v1 )))):named a17 ))
(check-sat )
;(get-unsat-core )
