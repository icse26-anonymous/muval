;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort B$ 0 )
(declare-sort Nat$ 0 )
(declare-sort Enat_bool_fun$ 0 )
(declare-sort Enat_enat_fun$ 0 )
(declare-sort A_b_bool_fun_fun$ 0 )
(declare-sort Enat_enat_bool_fun_fun$ 0 )
(declare-sort Nat_option$ 0)
(declare-sort Enat$ 0)
(declare-fun none$ ()Nat_option$)
(declare-fun the$ (Nat_option$)Nat$)
(declare-fun some$ (Nat$ )Nat_option$)
(declare-fun rep_enat$ (Enat$)Nat_option$)
(declare-fun abs_enat$ (Nat_option$ )Enat$)
(declare-codatatypes ()((A_llist$ (lNil$ )(lCons$ (lhd$ A$ )(ltl$ A_llist$ )))(B_llist$ (lNil$a )(lCons$a (lhd$a B$ )(ltl$a B_llist$ )))))
(declare-fun n$ ()Nat$ )
(declare-fun p$ ()A_b_bool_fun_fun$ )
(declare-fun xs$ ()A_llist$ )
(declare-fun ys$ ()B_llist$ )
(declare-fun xs$a ()A_llist$ )
(declare-fun enat$ (Nat$ )Enat$ )
(declare-fun less$ (Enat$ Enat$ )Bool )
(declare-fun plus$ (Enat$ )Enat_enat_fun$ )
(declare-fun fun_app$ (Enat_bool_fun$ Enat$ )Bool )
(declare-fun lappend$ (A_llist$ A_llist$ )A_llist$ )
(declare-fun less_eq$ (Enat$ Enat$ )Bool )
(declare-fun llength$ (A_llist$ )Enat$ )
(declare-fun fun_app$a (Enat_enat_bool_fun_fun$ Enat$ )Enat_bool_fun$ )
(declare-fun fun_app$b (Enat_enat_fun$ Enat$ )Enat$ )
(declare-fun lappend$a (B_llist$ B_llist$ )B_llist$ )
(declare-fun llength$a (B_llist$ )Enat$ )
(declare-fun llist_all2$ (A_b_bool_fun_fun$ A_llist$ B_llist$ )Bool )
(assert (! (not (less_eq$ (llength$ xs$ )(llength$ (lappend$ xs$ xs$a )))):named a0 ))
(assert (! (forall ((?v0 B_llist$ )(?v1 B_llist$ )(?v2 B_llist$ ))(= (lappend$a (lappend$a ?v0 ?v1 )?v2 )(lappend$a ?v0 (lappend$a ?v1 ?v2 )))):named a1 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(= (lappend$ (lappend$ ?v0 ?v1 )?v2 )(lappend$ ?v0 (lappend$ ?v1 ?v2 )))):named a2 ))
(assert (! (forall ((?v0 Enat_enat_bool_fun_fun$ )(?v1 Enat$ )(?v2 Enat$ ))(=> (and (forall ((?v3 Enat$ )(?v4 Enat$ ))(=> (less_eq$ ?v3 ?v4 )(fun_app$ (fun_app$a ?v0 ?v3 )?v4 )))(=> (fun_app$ (fun_app$a ?v0 ?v1 )?v2 )(fun_app$ (fun_app$a ?v0 ?v2 )?v1 )))(fun_app$ (fun_app$a ?v0 ?v2 )?v1 ))):named a3 ))
(assert (! (llist_all2$ p$ (lappend$ xs$ xs$a )ys$ ):named a4 ))
(assert (! (forall ((?v0 Enat$ ))(less_eq$ ?v0 ?v0 )):named a5 ))
(assert (! (less_eq$ (llength$ xs$a )(llength$a ys$ )):named a6 ))
(assert (! (less_eq$ (llength$ xs$ )(llength$a ys$ )):named a7 ))
(assert (! (less$ (enat$ n$ )(llength$ xs$ )):named a8 ))
(assert (! (= (fun_app$b (plus$ (llength$ xs$ ))(llength$ xs$a ))(llength$a ys$ )):named a9 ))
(assert (! (forall ((?v0 Enat$ )(?v1 Enat$ ))(= (= ?v0 ?v1 )(and (less_eq$ ?v0 ?v1 )(less_eq$ ?v1 ?v0 )))):named a10 ))
(assert (! (forall ((?v0 Enat$ )(?v1 Enat$ ))(=> (and (=> (less_eq$ ?v0 ?v1 )false )(=> (less_eq$ ?v1 ?v0 )false ))false )):named a11 ))
(assert (! (forall ((?v0 Enat_enat_bool_fun_fun$ )(?v1 Enat$ )(?v2 Enat$ ))(=> (and (forall ((?v3 Enat$ )(?v4 Enat$ ))(=> (less_eq$ ?v3 ?v4 )(fun_app$ (fun_app$a ?v0 ?v3 )?v4 )))(forall ((?v3 Enat$ )(?v4 Enat$ ))(=> (fun_app$ (fun_app$a ?v0 ?v4 )?v3 )(fun_app$ (fun_app$a ?v0 ?v3 )?v4 ))))(fun_app$ (fun_app$a ?v0 ?v1 )?v2 ))):named a12 ))
(assert (! (forall ((?v0 Enat$ )(?v1 Enat_enat_fun$ )(?v2 Enat$ )(?v3 Enat$ ))(=> (and (= ?v0 (fun_app$b ?v1 ?v2 ))(and (less_eq$ ?v2 ?v3 )(forall ((?v4 Enat$ )(?v5 Enat$ ))(=> (less_eq$ ?v4 ?v5 )(less_eq$ (fun_app$b ?v1 ?v4 )(fun_app$b ?v1 ?v5 ))))))(less_eq$ ?v0 (fun_app$b ?v1 ?v3 )))):named a13 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(= (llength$ (lappend$ ?v0 ?v1 ))(fun_app$b (plus$ (llength$ ?v0 ))(llength$ ?v1 )))):named a14 ))
(assert (! (forall ((?v0 B_llist$ )(?v1 B_llist$ ))(= (llength$a (lappend$a ?v0 ?v1 ))(fun_app$b (plus$ (llength$a ?v0 ))(llength$a ?v1 )))):named a15 ))
(assert (! (forall ((?v0 Enat$ )(?v1 Enat$ ))(= (not (= ?v0 ?v1 ))(or (less$ ?v0 ?v1 )(less$ ?v1 ?v0 )))):named a16 ))
(assert (! (forall ((?v0 Enat$ )(?v1 Enat$ ))(= (not (less$ ?v0 ?v1 ))(or (less$ ?v1 ?v0 )(= ?v0 ?v1 )))):named a17 ))
(check-sat )
;(get-unsat-core )
