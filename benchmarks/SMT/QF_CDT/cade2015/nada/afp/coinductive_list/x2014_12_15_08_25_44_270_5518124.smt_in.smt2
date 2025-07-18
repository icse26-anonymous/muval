;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_set$ 0 )
(declare-sort A_a_fun$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort A_a_bool_fun_fun$ 0 )
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
(declare-fun n$ ()Nat$ )
(declare-fun p$ ()A_a_bool_fun_fun$ )
(declare-fun xs$ ()A_llist$ )
(declare-fun ys$ ()A_llist$ )
(declare-fun zs$ ()A_llist$ )
(declare-fun enat$ (Nat$ )Enat$ )
(declare-fun less$ (Enat$ Enat$ )Bool )
(declare-fun lmap$ (A_a_fun$ A_llist$ )A_llist$ )
(declare-fun lnth$ (A_llist$ Nat$ )A$ )
(declare-fun lset$ (A_llist$ )A_set$ )
(declare-fun member$ (A$ A_set$ )Bool )
(declare-fun transp$ (A_a_bool_fun_fun$ )Bool )
(declare-fun fun_app$ (A_bool_fun$ A$ )Bool )
(declare-fun lappend$ (A_llist$ A_llist$ )A_llist$ )
(declare-fun llength$ (A_llist$ )Enat$ )
(declare-fun lprefix$ (A_llist$ A_llist$ )Bool )
(declare-fun fun_app$a (A_a_bool_fun_fun$ A$ )A_bool_fun$ )
(declare-fun fun_app$b (A_a_fun$ A$ )A$ )
(declare-fun ltakeWhile$ (A_bool_fun$ A_llist$ )A_llist$ )
(assert (! (not (fun_app$ (fun_app$a p$ (lnth$ xs$ n$ ))(lnth$ zs$ n$ ))):named a0 ))
(assert (! (transp$ p$ ):named a1 ))
(assert (! (less$ (enat$ n$ )(llength$ xs$ )):named a2 ))
(assert (! (= (llength$ xs$ )(llength$ ys$ )):named a3 ))
(assert (! (fun_app$ (fun_app$a p$ (lnth$ xs$ n$ ))(lnth$ ys$ n$ )):named a4 ))
(assert (! (fun_app$ (fun_app$a p$ (lnth$ ys$ n$ ))(lnth$ zs$ n$ )):named a5 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(= (= (enat$ ?v0 )(enat$ ?v1 ))(= ?v0 ?v1 ))):named a6 ))
(assert (! (forall ((?v0 Enat$ )(?v1 Nat$ ))(=> (less$ ?v0 (enat$ ?v1 ))(exists ((?v2 Nat$ ))(= ?v0 (enat$ ?v2 ))))):named a7 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_llist$ )(?v2 A_a_fun$ ))(=> (less$ (enat$ ?v0 )(llength$ ?v1 ))(= (lnth$ (lmap$ ?v2 ?v1 )?v0 )(fun_app$b ?v2 (lnth$ ?v1 ?v0 ))))):named a8 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 Nat$ ))(=> (and (lprefix$ ?v0 ?v1 )(less$ (enat$ ?v2 )(llength$ ?v0 )))(= (lnth$ ?v0 ?v2 )(lnth$ ?v1 ?v2 )))):named a9 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_bool_fun$ )(?v2 A_llist$ ))(=> (less$ (enat$ ?v0 )(llength$ (ltakeWhile$ ?v1 ?v2 )))(= (lnth$ (ltakeWhile$ ?v1 ?v2 )?v0 )(lnth$ ?v2 ?v0 )))):named a10 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(= (member$ ?v0 (lset$ ?v1 ))(exists ((?v2 Nat$ ))(and (less$ (enat$ ?v2 )(llength$ ?v1 ))(= (lnth$ ?v1 ?v2 )?v0 ))))):named a11 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ ))(= (transp$ ?v0 )(forall ((?v1 A$ )(?v2 A$ )(?v3 A$ ))(=> (and (fun_app$ (fun_app$a ?v0 ?v1 )?v2 )(fun_app$ (fun_app$a ?v0 ?v2 )?v3 ))(fun_app$ (fun_app$a ?v0 ?v1 )?v3 ))))):named a12 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ ))(=> (forall ((?v1 A$ )(?v2 A$ )(?v3 A$ ))(=> (and (fun_app$ (fun_app$a ?v0 ?v1 )?v2 )(fun_app$ (fun_app$a ?v0 ?v2 )?v3 ))(fun_app$ (fun_app$a ?v0 ?v1 )?v3 )))(transp$ ?v0 ))):named a13 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A$ )(?v2 A$ )(?v3 A$ ))(=> (and (transp$ ?v0 )(and (fun_app$ (fun_app$a ?v0 ?v1 )?v2 )(and (fun_app$ (fun_app$a ?v0 ?v2 )?v3 )(=> (fun_app$ (fun_app$a ?v0 ?v1 )?v3 )false ))))false )):named a14 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A$ )(?v2 A$ )(?v3 A$ ))(=> (and (transp$ ?v0 )(and (fun_app$ (fun_app$a ?v0 ?v1 )?v2 )(fun_app$ (fun_app$a ?v0 ?v2 )?v3 )))(fun_app$ (fun_app$a ?v0 ?v1 )?v3 ))):named a15 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_llist$ )(?v2 A_llist$ ))(=> (less$ (enat$ ?v0 )(llength$ ?v1 ))(= (lnth$ (lappend$ ?v1 ?v2 )?v0 )(lnth$ ?v1 ?v0 )))):named a16 ))
(assert (! (forall ((?v0 A_llist$ ))(lprefix$ ?v0 ?v0 )):named a17 ))
(assert (! (forall ((?v0 A_llist$ ))(lprefix$ ?v0 ?v0 )):named a18 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_llist$ ))(= (llength$ (lmap$ ?v0 ?v1 ))(llength$ ?v1 ))):named a19 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(= (lappend$ (lappend$ ?v0 ?v1 )?v2 )(lappend$ ?v0 (lappend$ ?v1 ?v2 )))):named a20 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_llist$ )(?v2 A_llist$ ))(= (lmap$ ?v0 (lappend$ ?v1 ?v2 ))(lappend$ (lmap$ ?v0 ?v1 )(lmap$ ?v0 ?v2 )))):named a21 ))
(check-sat )
;(get-unsat-core )
