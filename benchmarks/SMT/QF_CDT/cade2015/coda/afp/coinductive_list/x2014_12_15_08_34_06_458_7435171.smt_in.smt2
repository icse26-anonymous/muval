;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_set$ 0 )
(declare-sort Nat_set$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort Nat_bool_fun$ 0 )
(declare-sort A_llist_bool_fun$ 0 )
(declare-sort A_llist_a_set_fun$ 0 )
(declare-sort A_llist_a_llist_fun$ 0 )
(declare-codatatypes ()((A_llist$ (lNil$ )(lCons$ (lhd$ A$ )(ltl$ A_llist$ )))))
(declare-fun a$ ()Nat_set$ )
(declare-fun bot$ ()Nat_set$ )
(declare-fun member$ (Nat$ Nat_set$ )Bool )
(declare-fun collect$ (Nat_bool_fun$ )Nat_set$ )
(declare-fun fun_app$ (A_llist_bool_fun$ A_llist$ )Bool )
(declare-fun lmember$ (A$ )A_llist_bool_fun$ )
(declare-fun fun_app$a (A_llist_a_set_fun$ A_llist$ )A_set$ )
(declare-fun fun_app$b (A_llist_a_llist_fun$ A_llist$ )A_llist$ )
(declare-fun fun_app$c (Nat_bool_fun$ Nat$ )Bool )
(declare-fun gen_lset$ (A_set$ )A_llist_a_set_fun$ )
(declare-fun lsublist$ (A_llist$ Nat_set$ )A_llist$ )
(declare-fun ldistinct$ (A_llist$ )Bool )
(declare-fun ldropWhile$ (A_bool_fun$ )A_llist_a_llist_fun$ )
(declare-fun pred_llist$ (A_bool_fun$ )A_llist_bool_fun$ )
(declare-fun finite_lprefix$ (A_llist$ )A_llist_bool_fun$ )
(declare-fun lstrict_prefix$ (A_llist$ )A_llist_bool_fun$ )
(assert (! (not (= (lsublist$ lNil$ a$ )lNil$ )):named a0 ))
(assert (! (forall ((?v0 A_llist$ ))(= (lsublist$ ?v0 bot$ )lNil$ )):named a1 ))
(assert (! (forall ((?v0 A$ ))(! (= (fun_app$ (lmember$ ?v0 )lNil$ )false ):pattern ((lmember$ ?v0 )))):named a2 ))
(assert (! (forall ((?v0 A_set$ ))(! (= (fun_app$a (gen_lset$ ?v0 )lNil$ )?v0 ):pattern ((gen_lset$ ?v0 )))):named a3 ))
(assert (! (forall ((?v0 A_llist$ ))(! (= (fun_app$ (finite_lprefix$ ?v0 )lNil$ )(= ?v0 lNil$ )):pattern ((finite_lprefix$ ?v0 )))):named a4 ))
(assert (! (forall ((?v0 A_llist$ ))(! (= (fun_app$ (finite_lprefix$ lNil$ )?v0 )true ):pattern ((fun_app$ (finite_lprefix$ lNil$ )?v0 )))):named a5 ))
(assert (! (= (fun_app$ (lstrict_prefix$ lNil$ )lNil$ )false ):named a6 ))
(assert (! (forall ((?v0 A_bool_fun$ ))(fun_app$ (pred_llist$ ?v0 )lNil$ )):named a7 ))
(assert (! (= (ldistinct$ lNil$ )true ):named a8 ))
(assert (! (forall ((?v0 A_bool_fun$ ))(! (= (fun_app$b (ldropWhile$ ?v0 )lNil$ )lNil$ ):pattern ((ldropWhile$ ?v0 )))):named a9 ))
(assert (! (forall ((?v0 A_llist_bool_fun$ )(?v1 A_llist$ ))(=> (forall ((?v2 A_llist$ ))(=> (forall ((?v3 A_llist$ ))(=> (fun_app$ (lstrict_prefix$ ?v3 )?v2 )(fun_app$ ?v0 ?v3 )))(fun_app$ ?v0 ?v2 )))(fun_app$ ?v0 ?v1 ))):named a10 ))
(assert (! (ldistinct$ lNil$ ):named a11 ))
(assert (! (forall ((?v0 Nat_bool_fun$ ))(= (= (collect$ ?v0 )bot$ )(forall ((?v1 Nat$ ))(not (fun_app$c ?v0 ?v1 ))))):named a12 ))
(assert (! (forall ((?v0 Nat_set$ ))(= (forall ((?v1 Nat$ ))(not (member$ ?v1 ?v0 )))(= ?v0 bot$ ))):named a13 ))
(check-sat )
;(get-unsat-core )
