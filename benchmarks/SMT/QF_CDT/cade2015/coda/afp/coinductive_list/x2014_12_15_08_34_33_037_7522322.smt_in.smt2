;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_set$ 0 )
(declare-sort Nat_nat_fun$ 0 )
(declare-sort Nat_bool_fun$ 0 )
(declare-sort A_nat_prod_set$ 0 )
(declare-sort A_nat_bool_fun_fun$ 0 )
(declare-sort Nat_nat_bool_fun_fun$ 0 )
(declare-sort A_nat_prod$ 0)
(declare-fun fst$ (A_nat_prod$)A$)
(declare-fun snd$ (A_nat_prod$)Nat$)
(declare-fun pair$ (A$ Nat$ )A_nat_prod$)
(declare-codatatypes ()((A_nat_prod_llist$ (lNil$ )(lCons$ (lhd$ A_nat_prod$ )(ltl$ A_nat_prod_llist$ )))(A_llist$ (lNil$a )(lCons$a (lhd$a A$ )(ltl$a A_llist$ )))(Nat_llist$ (lNil$b )(lCons$b (lhd$b Nat$ )(ltl$b Nat_llist$ )))))
(declare-sort Nat_option$ 0)
(declare-sort Enat$ 0)
(declare-fun none$ ()Nat_option$)
(declare-fun the$ (Nat_option$)Nat$)
(declare-fun some$ (Nat$ )Nat_option$)
(declare-fun rep_enat$ (Enat$)Nat_option$)
(declare-fun abs_enat$ (Nat_option$ )Enat$)
(declare-fun uu$ ()A_nat_bool_fun_fun$ )
(declare-fun xs$ ()A_llist$ )
(declare-fun suc$ ()Nat_nat_fun$ )
(declare-fun uua$ (Bool A_nat_bool_fun_fun$ )A_nat_bool_fun_fun$ )
(declare-fun enat$ (Nat$ )Enat$ )
(declare-fun less$ (Enat$ Enat$ )Bool )
(declare-fun lnth$ (A_llist$ Nat$ )A$ )
(declare-fun lset$ (A_nat_prod_llist$ )A_nat_prod_set$ )
(declare-fun lzip$ (A_llist$ Nat_llist$ )A_nat_prod_llist$ )
(declare-fun zero$ ()Nat$ )
(declare-fun lnth$a (A_nat_prod_llist$ Nat$ )A_nat_prod$ )
(declare-fun lset$a (A_llist$ )A_set$ )
(declare-fun zero$a ()Enat$ )
(declare-fun member$ (A_nat_prod$ A_nat_prod_set$ )Bool )
(declare-fun fun_app$ (Nat_bool_fun$ Nat$ )Bool )
(declare-fun llength$ (A_llist$ )Enat$ )
(declare-fun member$a (A$ A_set$ )Bool )
(declare-fun fun_app$a (A_nat_bool_fun_fun$ A$ )Nat_bool_fun$ )
(declare-fun fun_app$b (Nat_nat_fun$ Nat$ )Nat$ )
(declare-fun fun_app$c (Nat_nat_bool_fun_fun$ Nat$ )Nat_bool_fun$ )
(declare-fun iterates$ (Nat_nat_fun$ Nat$ )Nat_llist$ )
(declare-fun llength$a (A_nat_prod_llist$ )Enat$ )
(declare-fun case_prod$ (A_nat_bool_fun_fun$ A_nat_prod$ )Bool )
(assert (! (forall ((?v0 A$ )(?v1 Nat$ ))(! (= (fun_app$ (fun_app$a uu$ ?v0 )?v1 )(and (less$ (enat$ ?v1 )(llength$ xs$ ))(= ?v0 (lnth$ xs$ ?v1 )))):pattern ((fun_app$ (fun_app$a uu$ ?v0 )?v1 )))):named a0 ))
(assert (! (forall ((?v0 Bool )(?v1 A_nat_bool_fun_fun$ )(?v2 A$ )(?v3 Nat$ ))(! (= (fun_app$ (fun_app$a (uua$ ?v0 ?v1 )?v2 )?v3 )(and ?v0 (fun_app$ (fun_app$a ?v1 ?v2 )?v3 ))):pattern ((fun_app$ (fun_app$a (uua$ ?v0 ?v1 )?v2 )?v3 )))):named a1 ))
(assert (! (not (forall ((?v0 A_nat_prod$ ))(=> (member$ ?v0 (lset$ (lzip$ xs$ (iterates$ suc$ zero$ ))))(case_prod$ uu$ ?v0 )))):named a2 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(= (member$a ?v0 (lset$a ?v1 ))(exists ((?v2 Nat$ ))(and (less$ (enat$ ?v2 )(llength$ ?v1 ))(= (lnth$ ?v1 ?v2 )?v0 ))))):named a3 ))
(assert (! (forall ((?v0 A_nat_prod$ )(?v1 A_nat_prod_llist$ ))(= (member$ ?v0 (lset$ ?v1 ))(exists ((?v2 Nat$ ))(and (less$ (enat$ ?v2 )(llength$a ?v1 ))(= (lnth$a ?v1 ?v2 )?v0 ))))):named a4 ))
(assert (! (forall ((?v0 Bool )(?v1 A_nat_bool_fun_fun$ )(?v2 A_nat_prod$ ))(= (case_prod$ (uua$ ?v0 ?v1 )?v2 )(and ?v0 (case_prod$ ?v1 ?v2 )))):named a5 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(= (= (enat$ ?v0 )(enat$ ?v1 ))(= ?v0 ?v1 ))):named a6 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(= (= (fun_app$b suc$ ?v0 )(fun_app$b suc$ ?v1 ))(= ?v0 ?v1 ))):named a7 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(= (= (fun_app$b suc$ ?v0 )(fun_app$b suc$ ?v1 ))(= ?v0 ?v1 ))):named a8 ))
(assert (! (forall ((?v0 Enat$ )(?v1 Nat$ ))(=> (less$ ?v0 (enat$ ?v1 ))(exists ((?v2 Nat$ ))(= ?v0 (enat$ ?v2 ))))):named a9 ))
(assert (! (forall ((?v0 Nat$ ))(=> (and (=> (= ?v0 zero$ )false )(forall ((?v1 Nat$ ))(=> (= ?v0 (fun_app$b suc$ ?v1 ))false )))false )):named a10 ))
(assert (! (forall ((?v0 Nat$ ))(=> (and (=> (= ?v0 zero$ )false )(forall ((?v1 Nat$ ))(=> (= ?v0 (fun_app$b suc$ ?v1 ))false )))false )):named a11 ))
(assert (! (forall ((?v0 Nat_nat_bool_fun_fun$ )(?v1 Nat$ )(?v2 Nat$ ))(=> (and (forall ((?v3 Nat$ ))(fun_app$ (fun_app$c ?v0 ?v3 )zero$ ))(and (forall ((?v3 Nat$ ))(fun_app$ (fun_app$c ?v0 zero$ )(fun_app$b suc$ ?v3 )))(forall ((?v3 Nat$ )(?v4 Nat$ ))(=> (fun_app$ (fun_app$c ?v0 ?v3 )?v4 )(fun_app$ (fun_app$c ?v0 (fun_app$b suc$ ?v3 ))(fun_app$b suc$ ?v4 ))))))(fun_app$ (fun_app$c ?v0 ?v1 )?v2 ))):named a12 ))
(assert (! (forall ((?v0 Nat$ ))(=> (= (fun_app$b suc$ ?v0 )zero$ )false )):named a13 ))
(assert (! (forall ((?v0 Enat$ ))(= (less$ zero$a ?v0 )(not (= ?v0 zero$a )))):named a14 ))
(assert (! (forall ((?v0 Enat$ ))(not (less$ ?v0 zero$a ))):named a15 ))
(assert (! (= zero$a (enat$ zero$ )):named a16 ))
(assert (! (forall ((?v0 Nat$ ))(= (= zero$a (enat$ ?v0 ))(= ?v0 zero$ ))):named a17 ))
(check-sat )
;(get-unsat-core )
