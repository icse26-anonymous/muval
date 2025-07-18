;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_a_fun$ 0 )
(declare-sort Nat_nat_fun$ 0 )
(declare-sort Nat_enat_fun$ 0 )
(declare-sort A_llist$ 0)
(declare-fun lNil$ ()A_llist$)
(declare-fun lhd$ (A_llist$)A$)
(declare-fun ltl$ (A_llist$)A_llist$)
(declare-fun lCons$ (A$ A_llist$ )A_llist$)
(declare-datatypes ()((Nat_option$ (none$ )(some$ (the$ Nat$ )))(Enat$ (abs_enat$ (rep_enat$ Nat_option$ )))))
(declare-fun x$ ()A$ )
(declare-fun na$ ()Nat$ )
(declare-fun xs$ ()A_llist$ )
(declare-fun suc$ (Nat$ )Nat$ )
(declare-fun xsa$ ()A_llist$ )
(declare-fun enat$ (Nat$ )Enat$ )
(declare-fun less$ (Enat$ Enat$ )Bool )
(declare-fun lnth$ (A_llist$ Nat$ )A$ )
(declare-fun less$a (Nat$ Nat$ )Bool )
(declare-fun ldropn$ (Nat$ A_llist$ )A_llist$ )
(declare-fun fun_app$ (A_a_fun$ A$ )A$ )
(declare-fun llength$ (A_llist$ )Enat$ )
(declare-fun fun_app$a (Nat_nat_fun$ Nat$ )Nat$ )
(declare-fun fun_app$b (Nat_enat_fun$ Nat$ )Enat$ )
(declare-fun iterates$ (A_a_fun$ A$ )A_llist$ )
(assert (! (not (= (lhd$ (ldropn$ (suc$ na$ )xsa$ ))(lnth$ xsa$ (suc$ na$ )))):named a0 ))
(assert (! (= (lhd$ (ldropn$ na$ xs$ ))(lnth$ xs$ na$ )):named a1 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(= (= (suc$ ?v0 )(suc$ ?v1 ))(= ?v0 ?v1 ))):named a2 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(= (= (suc$ ?v0 )(suc$ ?v1 ))(= ?v0 ?v1 ))):named a3 ))
(assert (! (=> (forall ((?v0 A$ )(?v1 A_llist$ ))(=> (= xsa$ (lCons$ ?v0 ?v1 ))false ))false ):named a4 ))
(assert (! (forall ((?v0 A_llist$ ))(=> (less$ (enat$ na$ )(llength$ ?v0 ))(= (lhd$ (ldropn$ na$ ?v0 ))(lnth$ ?v0 na$ )))):named a5 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(=> (= (suc$ ?v0 )(suc$ ?v1 ))(= ?v0 ?v1 ))):named a6 ))
(assert (! (forall ((?v0 Nat$ ))(not (= ?v0 (suc$ ?v0 )))):named a7 ))
(assert (! (less$ (enat$ (suc$ na$ ))(llength$ xsa$ )):named a8 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A$ ))(= (lhd$ (iterates$ ?v0 ?v1 ))?v1 )):named a9 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 Nat$ ))(! (= (lnth$ (lCons$ ?v0 ?v1 )(suc$ ?v2 ))(lnth$ ?v1 ?v2 )):pattern ((lnth$ (lCons$ ?v0 ?v1 )(suc$ ?v2 ))))):named a10 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A$ )(?v2 A_llist$ ))(! (= (ldropn$ (suc$ ?v0 )(lCons$ ?v1 ?v2 ))(ldropn$ ?v0 ?v2 )):pattern ((ldropn$ (suc$ ?v0 )(lCons$ ?v1 ?v2 ))))):named a11 ))
(assert (! (= xsa$ (lCons$ x$ xs$ )):named a12 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A$ )(?v3 A_llist$ ))(= (= (lCons$ ?v0 ?v1 )(lCons$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a13 ))
(assert (! (less$ (enat$ na$ )(llength$ xs$ )):named a14 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A$ ))(= (iterates$ ?v0 ?v1 )(lCons$ ?v1 (iterates$ ?v0 (fun_app$ ?v0 ?v1 ))))):named a15 ))
(assert (! (forall ((?v0 Nat_nat_fun$ )(?v1 Nat$ )(?v2 Nat$ ))(=> (and (forall ((?v3 Nat$ ))(less$a (fun_app$a ?v0 ?v3 )(fun_app$a ?v0 (suc$ ?v3 ))))(less$a ?v1 ?v2 ))(less$a (fun_app$a ?v0 ?v1 )(fun_app$a ?v0 ?v2 )))):named a16 ))
(assert (! (forall ((?v0 Nat_enat_fun$ )(?v1 Nat$ )(?v2 Nat$ ))(=> (and (forall ((?v3 Nat$ ))(less$ (fun_app$b ?v0 ?v3 )(fun_app$b ?v0 (suc$ ?v3 ))))(less$a ?v1 ?v2 ))(less$ (fun_app$b ?v0 ?v1 )(fun_app$b ?v0 ?v2 )))):named a17 ))
(check-sat )
;(get-unsat-core )
