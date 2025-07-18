;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_a_fun$ 0 )
(declare-sort A_a_fun_a_a_fun_fun$ 0 )
(declare-sort Nat_a_a_fun_a_a_fun_fun_fun$ 0 )
(declare-codatatypes ()((A_llist$ (lNil$ )(lCons$ (lhd$ A$ )(ltl$ A_llist$ )))))
(declare-sort Nat_option$ 0)
(declare-sort Enat$ 0)
(declare-fun none$ ()Nat_option$)
(declare-fun the$ (Nat_option$)Nat$)
(declare-fun some$ (Nat$ )Nat_option$)
(declare-fun rep_enat$ (Enat$)Nat_option$)
(declare-fun abs_enat$ (Nat_option$ )Enat$)
(declare-fun f$ ()A_a_fun$ )
(declare-fun n$ ()Nat$ )
(declare-fun x$ ()A$ )
(declare-fun id$ ()A_a_fun$ )
(declare-fun enat$ (Nat$ )Enat$ )
(declare-fun lmap$ (A_a_fun$ A_llist$ )A_llist$ )
(declare-fun lnth$ (A_llist$ Nat$ )A$ )
(declare-fun ldrop$ (Enat$ A_llist$ )A_llist$ )
(declare-fun lnull$ (A_llist$ )Bool )
(declare-fun compow$ ()Nat_a_a_fun_a_a_fun_fun_fun$ )
(declare-fun funpow$ ()Nat_a_a_fun_a_a_fun_fun_fun$ )
(declare-fun ldropn$ (Nat$ A_llist$ )A_llist$ )
(declare-fun fun_app$ (A_a_fun$ A$ )A$ )
(declare-fun lappend$ (A_llist$ A_llist$ )A_llist$ )
(declare-fun lfinite$ (A_llist$ )Bool )
(declare-fun fun_app$a (A_a_fun_a_a_fun_fun$ A_a_fun$ )A_a_fun$ )
(declare-fun fun_app$b (Nat_a_a_fun_a_a_fun_fun_fun$ Nat$ )A_a_fun_a_a_fun_fun$ )
(declare-fun iterates$ (A_a_fun$ A$ )A_llist$ )
(assert (! (not (= (lnth$ (iterates$ f$ x$ )n$ )(fun_app$ (fun_app$a (fun_app$b compow$ n$ )f$ )x$ ))):named a0 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 Nat$ )(?v2 A$ ))(= (fun_app$ ?v0 (fun_app$ (fun_app$a (fun_app$b compow$ ?v1 )?v0 )?v2 ))(fun_app$ (fun_app$a (fun_app$b compow$ ?v1 )?v0 )(fun_app$ ?v0 ?v2 )))):named a1 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_fun$ )(?v2 A$ ))(= (ldropn$ ?v0 (iterates$ ?v1 ?v2 ))(iterates$ ?v1 (fun_app$ (fun_app$a (fun_app$b compow$ ?v0 )?v1 )?v2 )))):named a2 ))
(assert (! (= funpow$ compow$ ):named a3 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A$ ))(not (lnull$ (iterates$ ?v0 ?v1 )))):named a4 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A$ ))(= (lmap$ ?v0 (iterates$ ?v0 ?v1 ))(iterates$ ?v0 (fun_app$ ?v0 ?v1 )))):named a5 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A$ ))(not (lfinite$ (iterates$ ?v0 ?v1 )))):named a6 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A$ )(?v2 A_llist$ ))(= (lappend$ (iterates$ ?v0 ?v1 )?v2 )(iterates$ ?v0 ?v1 ))):named a7 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A$ ))(= (iterates$ ?v0 ?v1 )(lCons$ ?v1 (iterates$ ?v0 (fun_app$ ?v0 ?v1 ))))):named a8 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A$ ))(= (lhd$ (iterates$ ?v0 ?v1 ))?v1 )):named a9 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A$ ))(= (ltl$ (iterates$ ?v0 ?v1 ))(iterates$ ?v0 (fun_app$ ?v0 ?v1 )))):named a10 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_fun$ )(?v2 A$ ))(= (ldrop$ (enat$ ?v0 )(iterates$ ?v1 ?v2 ))(iterates$ ?v1 (fun_app$ (fun_app$a (fun_app$b compow$ ?v0 )?v1 )?v2 )))):named a11 ))
(assert (! (forall ((?v0 Nat$ ))(= (fun_app$a (fun_app$b compow$ ?v0 )id$ )id$ )):named a12 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A$ )(?v3 A_llist$ ))(= (= (lCons$ ?v0 ?v1 )(lCons$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a13 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(= (not (lnull$ (lappend$ ?v0 ?v1 )))(or (not (lnull$ ?v0 ))(not (lnull$ ?v1 ))))):named a14 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(= (lnull$ (lappend$ ?v0 ?v1 ))(and (lnull$ ?v0 )(lnull$ ?v1 )))):named a15 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A_llist$ ))(! (= (lappend$ (lCons$ ?v0 ?v1 )?v2 )(lCons$ ?v0 (lappend$ ?v1 ?v2 ))):pattern ((lappend$ (lCons$ ?v0 ?v1 )?v2 )))):named a16 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(! (= (lfinite$ (lCons$ ?v0 ?v1 ))(lfinite$ ?v1 )):pattern ((lCons$ ?v0 ?v1 )))):named a17 ))
(check-sat )
;(get-unsat-core )
