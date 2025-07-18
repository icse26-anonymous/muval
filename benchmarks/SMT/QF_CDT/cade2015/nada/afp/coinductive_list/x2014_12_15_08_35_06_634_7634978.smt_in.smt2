;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort Nat_set$ 0 )
(declare-sort Nat_bool_fun$ 0 )
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
(declare-fun a$ ()Nat_set$ )
(declare-fun n$ ()Nat$ )
(declare-fun uu$ ()Nat_bool_fun$ )
(declare-fun xs$ ()A_llist$ )
(declare-fun suc$ (Nat$ )Nat$ )
(declare-fun uua$ (Nat_set$ Nat$ )Nat_bool_fun$ )
(declare-fun enat$ (Nat$ )Enat$ )
(declare-fun less$ (Enat$ Enat$ )Bool )
(declare-fun lnth$ (A_llist$ Nat$ )A$ )
(declare-fun plus$ (Nat$ Nat$ )Nat$ )
(declare-fun ltake$ (Enat$ A_llist$ )A_llist$ )
(declare-fun insert$ (Nat$ Nat_set$ )Nat_set$ )
(declare-fun ldropn$ (Nat$ A_llist$ )A_llist$ )
(declare-fun member$ (Nat$ Nat_set$ )Bool )
(declare-fun collect$ (Nat_bool_fun$ )Nat_set$ )
(declare-fun fun_app$ (Nat_bool_fun$ Nat$ )Bool )
(declare-fun lappend$ (A_llist$ A_llist$ )A_llist$ )
(declare-fun llength$ (A_llist$ )Enat$ )
(declare-fun lsublist$ (A_llist$ Nat_set$ )A_llist$ )
(assert (! (forall ((?v0 Nat$ ))(! (= (fun_app$ uu$ ?v0 )(member$ (suc$ (plus$ n$ ?v0 ))a$ )):pattern ((fun_app$ uu$ ?v0 )))):named a0 ))
(assert (! (forall ((?v0 Nat_set$ )(?v1 Nat$ )(?v2 Nat$ ))(! (= (fun_app$ (uua$ ?v0 ?v1 )?v2 )(member$ (plus$ ?v1 ?v2 )?v0 )):pattern ((fun_app$ (uua$ ?v0 ?v1 )?v2 )))):named a1 ))
(assert (! (not (= (lsublist$ xs$ (insert$ n$ a$ ))(lappend$ (lsublist$ (ltake$ (enat$ n$ )xs$ )a$ )(lCons$ (lnth$ xs$ n$ )(lsublist$ (ldropn$ (suc$ n$ )xs$ )(collect$ uu$ )))))):named a2 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A$ )(?v3 A_llist$ ))(= (= (lCons$ ?v0 ?v1 )(lCons$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a3 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A_llist$ ))(! (= (lappend$ (lCons$ ?v0 ?v1 )?v2 )(lCons$ ?v0 (lappend$ ?v1 ?v2 ))):pattern ((lappend$ (lCons$ ?v0 ?v1 )?v2 )))):named a4 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 A_llist$ ))(= (ldropn$ ?v0 (ldropn$ ?v1 ?v2 ))(ldropn$ (plus$ ?v0 ?v1 )?v2 ))):named a5 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 Nat$ ))(! (= (lnth$ (lCons$ ?v0 ?v1 )(suc$ ?v2 ))(lnth$ ?v1 ?v2 )):pattern ((lnth$ (lCons$ ?v0 ?v1 )(suc$ ?v2 ))))):named a6 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A$ )(?v2 A_llist$ ))(! (= (ldropn$ (suc$ ?v0 )(lCons$ ?v1 ?v2 ))(ldropn$ ?v0 ?v2 )):pattern ((ldropn$ (suc$ ?v0 )(lCons$ ?v1 ?v2 ))))):named a7 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_llist$ ))(= (lappend$ (ltake$ (enat$ ?v0 )?v1 )(ldropn$ ?v0 ?v1 ))?v1 )):named a8 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(= (lappend$ (lappend$ ?v0 ?v1 )?v2 )(lappend$ ?v0 (lappend$ ?v1 ?v2 )))):named a9 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 Nat_set$ )(?v2 Nat$ ))(= (lsublist$ ?v0 ?v1 )(lappend$ (lsublist$ (ltake$ (enat$ ?v2 )?v0 )?v1 )(lsublist$ (ldropn$ ?v2 ?v0 )(collect$ (uua$ ?v1 ?v2 )))))):named a10 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (forall ((?v2 Nat$ ))(= (ltake$ (enat$ ?v2 )?v0 )(ltake$ (enat$ ?v2 )?v1 )))(= ?v0 ?v1 ))):named a11 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(! (= (plus$ ?v0 (suc$ ?v1 ))(suc$ (plus$ ?v0 ?v1 ))):pattern ((plus$ ?v0 (suc$ ?v1 ))))):named a12 ))
(assert (! (less$ (enat$ n$ )(llength$ xs$ )):named a13 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(= (= (enat$ ?v0 )(enat$ ?v1 ))(= ?v0 ?v1 ))):named a14 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(= (= (suc$ ?v0 )(suc$ ?v1 ))(= ?v0 ?v1 ))):named a15 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(= (= (suc$ ?v0 )(suc$ ?v1 ))(= ?v0 ?v1 ))):named a16 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat_set$ ))(= (insert$ ?v0 (insert$ ?v0 ?v1 ))(insert$ ?v0 ?v1 ))):named a17 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat_set$ ))(= (member$ ?v0 (insert$ ?v1 ?v2 ))(or (= ?v0 ?v1 )(member$ ?v0 ?v2 )))):named a18 ))
(check-sat )
;(get-unsat-core )
