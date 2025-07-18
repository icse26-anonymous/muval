;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort Enat_bool_fun$ 0 )
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
(declare-fun less$ (Enat$ )Enat_bool_fun$ )
(declare-fun less$a (Nat$ Nat$ )Bool )
(declare-fun minus$ (Nat$ Nat$ )Nat$ )
(declare-fun ldropn$ (Nat$ A_llist$ )A_llist$ )
(declare-fun minus$a (Enat$ Enat$ )Enat$ )
(declare-fun fun_app$ (Enat_bool_fun$ Enat$ )Bool )
(declare-fun lappend$ (A_llist$ A_llist$ )A_llist$ )
(declare-fun llength$ (A_llist$ )Enat$ )
(declare-fun the_enat$ (Enat$ )Nat$ )
(assert (! (not (= (ldropn$ n$ (lappend$ xs$ ys$ ))(ite (fun_app$ (less$ (enat$ n$ ))(llength$ xs$ ))(lappend$ (ldropn$ n$ xs$ )ys$ )(ldropn$ (minus$ n$ (the_enat$ (llength$ xs$ )))ys$ )))):named a0 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(= (lappend$ (lappend$ ?v0 ?v1 )?v2 )(lappend$ ?v0 (lappend$ ?v1 ?v2 )))):named a1 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(= (= (enat$ ?v0 )(enat$ ?v1 ))(= ?v0 ?v1 ))):named a2 ))
(assert (! (forall ((?v0 Nat$ ))(! (= (the_enat$ (enat$ ?v0 ))?v0 ):pattern ((enat$ ?v0 )))):named a3 ))
(assert (! (forall ((?v0 Enat$ )(?v1 Nat$ ))(=> (fun_app$ (less$ ?v0 )(enat$ ?v1 ))(exists ((?v2 Nat$ ))(= ?v0 (enat$ ?v2 ))))):named a4 ))
(assert (! (forall ((?v0 Enat_bool_fun$ )(?v1 Enat$ ))(=> (forall ((?v2 Enat$ ))(=> (forall ((?v3 Enat$ ))(=> (fun_app$ (less$ ?v3 )?v2 )(fun_app$ ?v0 ?v3 )))(fun_app$ ?v0 ?v2 )))(fun_app$ ?v0 ?v1 ))):named a5 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(= (minus$ (minus$ ?v0 ?v1 )?v2 )(minus$ (minus$ ?v0 ?v2 )?v1 ))):named a6 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(= (minus$ (minus$ ?v0 ?v1 )?v2 )(minus$ (minus$ ?v0 ?v2 )?v1 ))):named a7 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(! (= (minus$a (enat$ ?v0 )(enat$ ?v1 ))(enat$ (minus$ ?v0 ?v1 ))):pattern ((minus$a (enat$ ?v0 )(enat$ ?v1 ))))):named a8 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(! (= (fun_app$ (less$ (enat$ ?v0 ))(enat$ ?v1 ))(less$a ?v0 ?v1 )):pattern ((fun_app$ (less$ (enat$ ?v0 ))(enat$ ?v1 ))))):named a9 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(=> (less$a ?v0 ?v1 )(less$a (minus$ ?v0 ?v2 )?v1 ))):named a10 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(=> (and (less$a ?v0 ?v1 )(less$a ?v0 ?v2 ))(less$a (minus$ ?v2 ?v1 )(minus$ ?v2 ?v0 )))):named a11 ))
(check-sat )
;(get-unsat-core )
