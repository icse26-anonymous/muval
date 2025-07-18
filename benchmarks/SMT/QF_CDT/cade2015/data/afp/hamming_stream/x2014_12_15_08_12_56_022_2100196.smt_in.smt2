;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort Nat$ 0 )
(declare-sort Unit$ 0 )
(declare-sort Unit_bool_fun$ 0 )
(declare-sort Nat_llist$ 0)
(declare-fun lNil$ ()Nat_llist$)
(declare-fun lhd$ (Nat_llist$)Nat$)
(declare-fun ltl$ (Nat_llist$)Nat_llist$)
(declare-fun lCons$ (Nat$ Nat_llist$ )Nat_llist$)
(declare-fun one$ ()Nat$ )
(declare-fun unity$ ()Unit$ )
(declare-fun of_nat$ (Nat$ )Nat$ )
(declare-fun default$ ()Unit$ )
(declare-fun fun_app$ (Unit_bool_fun$ Unit$ )Bool )
(declare-fun hamming$ (Unit$ )Nat_llist$ )
(declare-fun of_nat$a (Nat$ )Int )
(declare-fun hamming$a ()Nat_llist$ )
(assert (! (not (= (lhd$ (hamming$ unity$ ))one$ )):named a0 ))
(assert (! (= hamming$a (hamming$ unity$ )):named a1 ))
(assert (! (forall ((?v0 Bool ))(= (= ?v0 (= unity$ unity$ ))?v0 )):named a2 ))
(assert (! (forall ((?v0 Unit$ ))(=> (=> (= ?v0 unity$ )false )false )):named a3 ))
(assert (! (forall ((?v0 Unit_bool_fun$ )(?v1 Unit_bool_fun$ ))(=> (=> (fun_app$ ?v0 unity$ )(fun_app$ ?v1 unity$ ))(forall ((?v2 Unit$ ))(=> (fun_app$ ?v0 ?v2 )(fun_app$ ?v1 ?v2 ))))):named a4 ))
(assert (! (= one$ one$ ):named a5 ))
(assert (! (forall ((?v0 Nat$ ))(= (= one$ ?v0 )(= ?v0 one$ ))):named a6 ))
(assert (! (forall ((?v0 Int ))(= (= 1 ?v0 )(= ?v0 1 ))):named a7 ))
(assert (! (= default$ unity$ ):named a8 ))
(assert (! (= (of_nat$ one$ )one$ ):named a9 ))
(assert (! (= (of_nat$a one$ )1 ):named a10 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(= (= (of_nat$ ?v0 )(of_nat$ ?v1 ))(= ?v0 ?v1 ))):named a11 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(= (= (of_nat$a ?v0 )(of_nat$a ?v1 ))(= ?v0 ?v1 ))):named a12 ))
(assert (! (= (of_nat$a one$ )1 ):named a13 ))
(check-sat )
;(get-unsat-core )
