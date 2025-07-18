;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_a_fun$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-codatatypes ()((A_llist$ (lNil$ )(lCons$ (lhd$ A$ )(ltl$ A_llist$ )))))
(declare-sort Nat_option$ 0)
(declare-sort Enat$ 0)
(declare-fun none$ ()Nat_option$)
(declare-fun the$ (Nat_option$)Nat$)
(declare-fun some$ (Nat$ )Nat_option$)
(declare-fun rep_enat$ (Enat$)Nat_option$)
(declare-fun abs_enat$ (Nat_option$ )Enat$)
(declare-fun x$ ()A$ )
(declare-fun na$ ()Enat$ )
(declare-fun xsa$ ()A_llist$ )
(declare-fun eSuc$ (Enat$ )Enat$ )
(declare-fun ldrop$ (Enat$ A_llist$ )A_llist$ )
(declare-fun ltake$ (Enat$ A_llist$ )A_llist$ )
(declare-fun fun_app$ (A_bool_fun$ A$ )Bool )
(declare-fun lfinite$ (A_llist$ )Bool )
(declare-fun llength$ (A_llist$ )Enat$ )
(declare-fun lmember$ (A$ A_llist$ )Bool )
(declare-fun fun_app$a (A_a_fun$ A$ )A$ )
(declare-fun iterates$ (A_a_fun$ A$ )A_llist$ )
(declare-fun pred_llist$ (A_bool_fun$ A_llist$ )Bool )
(assert (! (not (= (ldrop$ (eSuc$ na$ )(lCons$ x$ xsa$ ))(ltl$ (ldrop$ na$ (lCons$ x$ xsa$ ))))):named a0 ))
(assert (! (lfinite$ xsa$ ):named a1 ))
(assert (! (forall ((?v0 Enat$ ))(= (ldrop$ (eSuc$ ?v0 )xsa$ )(ltl$ (ldrop$ ?v0 xsa$ )))):named a2 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A$ )(?v3 A_llist$ ))(= (= (lCons$ ?v0 ?v1 )(lCons$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a3 ))
(assert (! (forall ((?v0 Enat$ )(?v1 A$ )(?v2 A_llist$ ))(= (ldrop$ (eSuc$ ?v0 )(lCons$ ?v1 ?v2 ))(ldrop$ ?v0 ?v2 ))):named a4 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(! (= (ltl$ (lCons$ ?v0 ?v1 ))?v1 ):pattern ((lCons$ ?v0 ?v1 )))):named a5 ))
(assert (! (forall ((?v0 A_llist$ ))(= (lfinite$ (ltl$ ?v0 ))(lfinite$ ?v0 ))):named a6 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(! (= (lfinite$ (lCons$ ?v0 ?v1 ))(lfinite$ ?v1 )):pattern ((lCons$ ?v0 ?v1 )))):named a7 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(! (= (lfinite$ (lCons$ ?v0 ?v1 ))(lfinite$ ?v1 )):pattern ((lCons$ ?v0 ?v1 )))):named a8 ))
(assert (! (forall ((?v0 Enat$ )(?v1 Enat$ ))(= (= (eSuc$ ?v0 )(eSuc$ ?v1 ))(= ?v0 ?v1 ))):named a9 ))
(assert (! (forall ((?v0 Enat$ )(?v1 Enat$ ))(= (= (eSuc$ ?v0 )(eSuc$ ?v1 ))(= ?v0 ?v1 ))):named a10 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A$ ))(=> (lfinite$ ?v0 )(lfinite$ (lCons$ ?v1 ?v0 )))):named a11 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A$ )(?v2 A_llist$ ))(! (= (pred_llist$ ?v0 (lCons$ ?v1 ?v2 ))(and (fun_app$ ?v0 ?v1 )(pred_llist$ ?v0 ?v2 ))):pattern ((pred_llist$ ?v0 (lCons$ ?v1 ?v2 ))))):named a12 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ )(?v2 A_llist$ ))(! (= (lmember$ ?v0 (lCons$ ?v1 ?v2 ))(or (= ?v0 ?v1 )(lmember$ ?v0 ?v2 ))):pattern ((lmember$ ?v0 (lCons$ ?v1 ?v2 ))))):named a13 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(! (= (llength$ (lCons$ ?v0 ?v1 ))(eSuc$ (llength$ ?v1 ))):pattern ((lCons$ ?v0 ?v1 )))):named a14 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A$ ))(= (ltl$ (iterates$ ?v0 ?v1 ))(iterates$ ?v0 (fun_app$a ?v0 ?v1 )))):named a15 ))
(assert (! (forall ((?v0 Enat$ )(?v1 A$ )(?v2 A_llist$ ))(= (ltake$ (eSuc$ ?v0 )(lCons$ ?v1 ?v2 ))(lCons$ ?v1 (ltake$ ?v0 ?v2 )))):named a16 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A$ ))(= (iterates$ ?v0 ?v1 )(lCons$ ?v1 (iterates$ ?v0 (fun_app$a ?v0 ?v1 ))))):named a17 ))
(check-sat )
;(get-unsat-core )
