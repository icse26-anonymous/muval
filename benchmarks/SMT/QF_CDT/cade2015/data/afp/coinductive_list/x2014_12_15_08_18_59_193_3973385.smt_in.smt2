;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort Nat_bool_fun$ 0 )
(declare-sort A_llist$ 0)
(declare-fun lNil$ ()A_llist$)
(declare-fun lhd$ (A_llist$)A$)
(declare-fun ltl$ (A_llist$)A_llist$)
(declare-fun lCons$ (A$ A_llist$ )A_llist$)
(declare-datatypes ()((Nat_option$ (none$ )(some$ (the$ Nat$ )))(Enat$ (abs_enat$ (rep_enat$ Nat_option$ )))))
(declare-fun ka$ ()Nat$ )
(declare-fun na$ ()Nat$ )
(declare-fun ys$ ()A_llist$ )
(declare-fun suc$ (Nat$ )Nat$ )
(declare-fun xsa$ ()A_llist$ )
(declare-fun enat$ (Nat$ )Enat$ )
(declare-fun lnth$ (A_llist$ Nat$ )A$ )
(declare-fun minus$ (Nat$ Nat$ )Nat$ )
(declare-fun fun_app$ (Nat_bool_fun$ Nat$ )Bool )
(declare-fun lappend$ (A_llist$ A_llist$ )A_llist$ )
(declare-fun less_eq$ (Nat$ )Nat_bool_fun$ )
(declare-fun llength$ (A_llist$ )Enat$ )
(assert (! (not (= (lnth$ (lappend$ xsa$ ys$ )(suc$ na$ ))(lnth$ ys$ (minus$ (suc$ na$ )ka$ )))):named a0 ))
(assert (! (fun_app$ (less_eq$ ka$ )(suc$ na$ )):named a1 ))
(assert (! (= (llength$ xsa$ )(enat$ ka$ )):named a2 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 Nat$ ))(=> (and (= (llength$ ?v0 )(enat$ ?v1 ))(fun_app$ (less_eq$ ?v1 )na$ ))(= (lnth$ (lappend$ ?v0 ys$ )na$ )(lnth$ ys$ (minus$ na$ ?v1 ))))):named a3 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(= (lappend$ (lappend$ ?v0 ?v1 )?v2 )(lappend$ ?v0 (lappend$ ?v1 ?v2 )))):named a4 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(= (minus$ (minus$ (suc$ ?v0 )?v1 )(suc$ ?v2 ))(minus$ (minus$ ?v0 ?v1 )?v2 ))):named a5 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(! (= (minus$ (suc$ ?v0 )(suc$ ?v1 ))(minus$ ?v0 ?v1 )):pattern ((minus$ (suc$ ?v0 )(suc$ ?v1 ))))):named a6 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(= (= (suc$ ?v0 )(suc$ ?v1 ))(= ?v0 ?v1 ))):named a7 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(= (= (suc$ ?v0 )(suc$ ?v1 ))(= ?v0 ?v1 ))):named a8 ))
(assert (! (forall ((?v0 Nat_bool_fun$ )(?v1 Nat$ )(?v2 Nat$ ))(=> (and (fun_app$ ?v0 ?v1 )(forall ((?v3 Nat$ ))(=> (fun_app$ ?v0 (suc$ ?v3 ))(fun_app$ ?v0 ?v3 ))))(fun_app$ ?v0 (minus$ ?v1 ?v2 )))):named a9 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(! (=> (fun_app$ (less_eq$ ?v0 )?v1 )(= (minus$ (suc$ ?v1 )?v0 )(suc$ (minus$ ?v1 ?v0 )))):pattern ((minus$ (suc$ ?v1 )?v0 )))):named a10 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(= (minus$ (minus$ ?v0 ?v1 )?v2 )(minus$ (minus$ ?v0 ?v2 )?v1 ))):named a11 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(=> (= (suc$ ?v0 )(suc$ ?v1 ))(= ?v0 ?v1 ))):named a12 ))
(assert (! (forall ((?v0 Nat$ ))(not (= ?v0 (suc$ ?v0 )))):named a13 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(= (minus$ (minus$ ?v0 ?v1 )?v2 )(minus$ (minus$ ?v0 ?v2 )?v1 ))):named a14 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(! (= (fun_app$ (less_eq$ (suc$ ?v0 ))(suc$ ?v1 ))(fun_app$ (less_eq$ ?v0 )?v1 )):pattern ((fun_app$ (less_eq$ (suc$ ?v0 ))(suc$ ?v1 ))))):named a15 ))
(check-sat )
;(get-unsat-core )
