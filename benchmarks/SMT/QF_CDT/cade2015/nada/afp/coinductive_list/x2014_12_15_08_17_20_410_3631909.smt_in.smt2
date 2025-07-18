;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort Nat_bool_fun$ 0 )
(declare-sort Enat_bool_fun$ 0 )
(declare-sort Nat_nat_bool_fun_fun$ 0 )
(declare-sort Enat_enat_bool_fun_fun$ 0 )
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
(declare-fun xs$ ()A_llist$ )
(declare-fun ys$ ()A_llist$ )
(declare-fun enat$ (Nat$ )Enat$ )
(declare-fun less$ (Enat$ Enat$ )Bool )
(declare-fun lnull$ (A_llist$ )Bool )
(declare-fun minus$ (Nat$ Nat$ )Nat$ )
(declare-fun ldropn$ (Nat$ A_llist$ )A_llist$ )
(declare-fun minus$a (Enat$ Enat$ )Enat$ )
(declare-fun fun_app$ (Enat_bool_fun$ Enat$ )Bool )
(declare-fun lappend$ (A_llist$ A_llist$ )A_llist$ )
(declare-fun less_eq$ (Enat$ Enat$ )Bool )
(declare-fun llength$ (A_llist$ )Enat$ )
(declare-fun fun_app$a (Enat_enat_bool_fun_fun$ Enat$ )Enat_bool_fun$ )
(declare-fun fun_app$b (Nat_bool_fun$ Nat$ )Bool )
(declare-fun fun_app$c (Nat_nat_bool_fun_fun$ Nat$ )Nat_bool_fun$ )
(declare-fun less_eq$a (Nat$ Nat$ )Bool )
(declare-fun the_enat$ (Enat$ )Nat$ )
(assert (! (not (= (ldropn$ n$ (lappend$ xs$ ys$ ))(ldropn$ (minus$ n$ (the_enat$ (llength$ xs$ )))ys$ ))):named a0 ))
(assert (! (less_eq$ (llength$ xs$ )(enat$ n$ )):named a1 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(= (lappend$ (lappend$ ?v0 ?v1 )?v2 )(lappend$ ?v0 (lappend$ ?v1 ?v2 )))):named a2 ))
(assert (! (forall ((?v0 Enat_enat_bool_fun_fun$ )(?v1 Enat$ )(?v2 Enat$ ))(=> (and (forall ((?v3 Enat$ )(?v4 Enat$ ))(=> (less_eq$ ?v3 ?v4 )(fun_app$ (fun_app$a ?v0 ?v3 )?v4 )))(=> (fun_app$ (fun_app$a ?v0 ?v1 )?v2 )(fun_app$ (fun_app$a ?v0 ?v2 )?v1 )))(fun_app$ (fun_app$a ?v0 ?v2 )?v1 ))):named a3 ))
(assert (! (forall ((?v0 Nat_nat_bool_fun_fun$ )(?v1 Nat$ )(?v2 Nat$ ))(=> (and (forall ((?v3 Nat$ )(?v4 Nat$ ))(=> (less_eq$a ?v3 ?v4 )(fun_app$b (fun_app$c ?v0 ?v3 )?v4 )))(=> (fun_app$b (fun_app$c ?v0 ?v1 )?v2 )(fun_app$b (fun_app$c ?v0 ?v2 )?v1 )))(fun_app$b (fun_app$c ?v0 ?v2 )?v1 ))):named a4 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(= (= (enat$ ?v0 )(enat$ ?v1 ))(= ?v0 ?v1 ))):named a5 ))
(assert (! (forall ((?v0 Nat$ ))(! (= (the_enat$ (enat$ ?v0 ))?v0 ):pattern ((enat$ ?v0 )))):named a6 ))
(assert (! (forall ((?v0 Enat$ ))(less_eq$ ?v0 ?v0 )):named a7 ))
(assert (! (forall ((?v0 Nat$ ))(less_eq$a ?v0 ?v0 )):named a8 ))
(assert (! (forall ((?v0 Enat$ )(?v1 Nat$ ))(=> (less_eq$ ?v0 (enat$ ?v1 ))(exists ((?v2 Nat$ ))(= ?v0 (enat$ ?v2 ))))):named a9 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_llist$ )(?v2 A_llist$ ))(= (ldropn$ ?v0 (lappend$ ?v1 ?v2 ))(ite (less$ (enat$ ?v0 )(llength$ ?v1 ))(lappend$ (ldropn$ ?v0 ?v1 )?v2 )(ldropn$ (minus$ ?v0 (the_enat$ (llength$ ?v1 )))?v2 )))):named a10 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_llist$ ))(= (lnull$ (ldropn$ ?v0 ?v1 ))(less_eq$ (llength$ ?v1 )(enat$ ?v0 )))):named a11 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_llist$ ))(= (= (ldropn$ ?v0 ?v1 )lNil$ )(less_eq$ (llength$ ?v1 )(enat$ ?v0 )))):named a12 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(! (= (minus$a (enat$ ?v0 )(enat$ ?v1 ))(enat$ (minus$ ?v0 ?v1 ))):pattern ((minus$a (enat$ ?v0 )(enat$ ?v1 ))))):named a13 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(! (= (less_eq$ (enat$ ?v0 )(enat$ ?v1 ))(less_eq$a ?v0 ?v1 )):pattern ((less_eq$ (enat$ ?v0 )(enat$ ?v1 ))))):named a14 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(= (lnull$ (lappend$ ?v0 ?v1 ))(and (lnull$ ?v0 )(lnull$ ?v1 )))):named a15 ))
(check-sat )
;(get-unsat-core )
