;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_set$ 0 )
(declare-sort Nat_set$ 0 )
(declare-sort Nat_a_fun$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort Nat_nat_fun$ 0 )
(declare-sort Nat_bool_fun$ 0 )
(declare-sort A_nat_prod_set$ 0 )
(declare-sort A_nat_a_fun_fun$ 0 )
(declare-sort A_nat_prod_a_fun$ 0 )
(declare-sort A_nat_bool_fun_fun$ 0 )
(declare-sort A_nat_prod_bool_fun$ 0 )
(declare-sort A_llist_a_bool_fun_fun$ 0 )
(declare-sort A_bool_fun_a_bool_fun_fun$ 0 )
(declare-sort Nat_llist_nat_bool_fun_fun$ 0 )
(declare-sort Nat_bool_fun_nat_bool_fun_fun$ 0 )
(declare-sort A_nat_prod_a_fun_a_nat_prod_bool_fun_fun$ 0 )
(declare-sort A_nat_prod_llist_a_nat_prod_bool_fun_fun$ 0 )
(declare-sort A_nat_bool_fun_fun_a_nat_bool_fun_fun_fun$ 0 )
(declare-sort A_nat_prod_bool_fun_a_nat_prod_bool_fun_fun$ 0 )
(declare-sort A_nat_prod$ 0)
(declare-fun fst$ (A_nat_prod$)A$)
(declare-fun snd$ (A_nat_prod$)Nat$)
(declare-fun pair$ (A$ Nat$ )A_nat_prod$)
(declare-sort A_nat_prod_llist$ 0)
(declare-fun lNil$ ()A_nat_prod_llist$)
(declare-fun lhd$ (A_nat_prod_llist$)A_nat_prod$)
(declare-fun ltl$ (A_nat_prod_llist$)A_nat_prod_llist$)
(declare-fun lCons$ (A_nat_prod$ A_nat_prod_llist$ )A_nat_prod_llist$)
(declare-sort Nat_option$ 0)
(declare-sort Enat$ 0)
(declare-fun none$ ()Nat_option$)
(declare-fun the$ (Nat_option$)Nat$)
(declare-fun some$ (Nat$ )Nat_option$)
(declare-fun rep_enat$ (Enat$)Nat_option$)
(declare-fun abs_enat$ (Nat_option$ )Enat$)
(declare-sort A_llist$ 0)
(declare-sort Nat_llist$ 0)
(declare-fun lNil$a ()A_llist$)
(declare-fun lhd$a (A_llist$)A$)
(declare-fun ltl$a (A_llist$)A_llist$)
(declare-fun lCons$a (A$ A_llist$ )A_llist$)
(declare-fun lNil$b ()Nat_llist$)
(declare-fun lhd$b (Nat_llist$)Nat$)
(declare-fun ltl$b (Nat_llist$)Nat_llist$)
(declare-fun lCons$b (Nat$ Nat_llist$ )Nat_llist$)
(declare-fun p$ ()A_bool_fun$ )
(declare-fun uu$ ()A_nat_bool_fun_fun$ )
(declare-fun xs$ ()A_llist$ )
(declare-fun suc$ ()Nat_nat_fun$ )
(declare-fun uua$ ()A_nat_prod_a_fun$ )
(declare-fun uub$ ()A_bool_fun$ )
(declare-fun uuc$ ()Nat_bool_fun$ )
(declare-fun uud$ ()A_nat_prod_bool_fun$ )
(declare-fun uue$ ()A_nat_bool_fun_fun$ )
(declare-fun uuf$ (A_bool_fun$ )A_bool_fun_a_bool_fun_fun$ )
(declare-fun uug$ (Nat_bool_fun$ )Nat_bool_fun_nat_bool_fun_fun$ )
(declare-fun uuh$ (A_nat_prod_bool_fun$ )A_nat_prod_bool_fun_a_nat_prod_bool_fun_fun$ )
(declare-fun uui$ ()Nat_bool_fun$ )
(declare-fun uuj$ (A_bool_fun$ )A_llist_a_bool_fun_fun$ )
(declare-fun uuk$ (Nat_bool_fun$ )Nat_llist_nat_bool_fun_fun$ )
(declare-fun uul$ (A_nat_prod_bool_fun$ )A_nat_prod_llist_a_nat_prod_bool_fun_fun$ )
(declare-fun uum$ (Bool )A_nat_bool_fun_fun_a_nat_bool_fun_fun_fun$ )
(declare-fun uun$ ()A_nat_a_fun_fun$ )
(declare-fun comp$ (A_bool_fun$ )A_nat_prod_a_fun_a_nat_prod_bool_fun_fun$ )
(declare-fun enat$ (Nat$ )Enat$ )
(declare-fun less$ (Enat$ Enat$ )Bool )
(declare-fun lmap$ (A_nat_prod_a_fun$ A_nat_prod_llist$ )A_llist$ )
(declare-fun lnth$ (A_llist$ Nat$ )A$ )
(declare-fun lset$ (A_nat_prod_llist$ )A_nat_prod_set$ )
(declare-fun lzip$ (A_llist$ Nat_llist$ )A_nat_prod_llist$ )
(declare-fun zero$ ()Nat$ )
(declare-fun lnth$a (Nat_llist$ Nat$ )Nat$ )
(declare-fun lnth$b (A_nat_prod_llist$ Nat$ )A_nat_prod$ )
(declare-fun lset$a (Nat_llist$ )Nat_set$ )
(declare-fun lset$b (A_llist$ )A_set$ )
(declare-fun zero$a ()Enat$ )
(declare-fun member$ (A_nat_prod$ A_nat_prod_set$ )Bool )
(declare-fun collect$ (Nat_bool_fun$ )Nat_set$ )
(declare-fun fun_app$ (Nat_bool_fun$ Nat$ )Bool )
(declare-fun lfilter$ (A_nat_prod_bool_fun$ A_nat_prod_llist$ )A_nat_prod_llist$ )
(declare-fun llength$ (A_llist$ )Enat$ )
(declare-fun member$a (Nat$ Nat_set$ )Bool )
(declare-fun member$b (A$ A_set$ )Bool )
(declare-fun collect$a (A_bool_fun$ )A_set$ )
(declare-fun collect$b (A_nat_prod_bool_fun$ )A_nat_prod_set$ )
(declare-fun fun_app$a (A_bool_fun$ A$ )Bool )
(declare-fun fun_app$b (A_nat_prod_a_fun$ A_nat_prod$ )A$ )
(declare-fun fun_app$c (A_nat_bool_fun_fun$ A$ )Nat_bool_fun$ )
(declare-fun fun_app$d (A_nat_prod_bool_fun$ A_nat_prod$ )Bool )
(declare-fun fun_app$e (A_nat_prod_llist_a_nat_prod_bool_fun_fun$ A_nat_prod_llist$ )A_nat_prod_bool_fun$ )
(declare-fun fun_app$f (Nat_llist_nat_bool_fun_fun$ Nat_llist$ )Nat_bool_fun$ )
(declare-fun fun_app$g (A_llist_a_bool_fun_fun$ A_llist$ )A_bool_fun$ )
(declare-fun fun_app$h (A_nat_prod_bool_fun_a_nat_prod_bool_fun_fun$ A_nat_prod_bool_fun$ )A_nat_prod_bool_fun$ )
(declare-fun fun_app$i (Nat_bool_fun_nat_bool_fun_fun$ Nat_bool_fun$ )Nat_bool_fun$ )
(declare-fun fun_app$j (A_bool_fun_a_bool_fun_fun$ A_bool_fun$ )A_bool_fun$ )
(declare-fun fun_app$k (A_nat_bool_fun_fun_a_nat_bool_fun_fun_fun$ A_nat_bool_fun_fun$ )A_nat_bool_fun_fun$ )
(declare-fun fun_app$l (Nat_a_fun$ Nat$ )A$ )
(declare-fun fun_app$m (A_nat_a_fun_fun$ A$ )Nat_a_fun$ )
(declare-fun fun_app$n (A_nat_prod_a_fun_a_nat_prod_bool_fun_fun$ A_nat_prod_a_fun$ )A_nat_prod_bool_fun$ )
(declare-fun fun_app$o (Nat_nat_fun$ Nat$ )Nat$ )
(declare-fun iterates$ (Nat_nat_fun$ Nat$ )Nat_llist$ )
(declare-fun lfilter$a (A_bool_fun$ A_llist$ )A_llist$ )
(declare-fun lfilter$b (Nat_bool_fun$ Nat_llist$ )Nat_llist$ )
(declare-fun llength$a (Nat_llist$ )Enat$ )
(declare-fun llength$b (A_nat_prod_llist$ )Enat$ )
(declare-fun lsublist$ (A_llist$ Nat_set$ )A_llist$ )
(declare-fun case_prod$ (A_nat_bool_fun_fun$ )A_nat_prod_bool_fun$ )
(declare-fun case_prod$a (A_nat_a_fun_fun$ )A_nat_prod_a_fun$ )
(assert (! (forall ((?v0 Nat$ ))(! (= (fun_app$ uui$ ?v0 )(and (less$ (enat$ ?v0 )(llength$ xs$ ))(fun_app$a p$ (lnth$ xs$ ?v0 )))):pattern ((fun_app$ uui$ ?v0 )))):named a0 ))
(assert (! (forall ((?v0 A_nat_prod$ ))(! (= (fun_app$b uua$ ?v0 )(fst$ ?v0 )):pattern ((fun_app$b uua$ ?v0 )))):named a1 ))
(assert (! (forall ((?v0 A$ )(?v1 Nat$ ))(! (= (fun_app$ (fun_app$c uue$ ?v0 )?v1 )(and (less$ (enat$ ?v1 )(llength$ xs$ ))(= ?v0 (lnth$ xs$ ?v1 )))):pattern ((fun_app$ (fun_app$c uue$ ?v0 )?v1 )))):named a2 ))
(assert (! (forall ((?v0 A$ )(?v1 Nat$ ))(! (= (fun_app$ (fun_app$c uu$ ?v0 )?v1 )(and (less$ (enat$ ?v1 )(llength$ xs$ ))(fun_app$a p$ (lnth$ xs$ ?v1 )))):pattern ((fun_app$ (fun_app$c uu$ ?v0 )?v1 )))):named a3 ))
(assert (! (forall ((?v0 A_nat_prod_bool_fun$ )(?v1 A_nat_prod_llist$ )(?v2 A_nat_prod$ ))(! (= (fun_app$d (fun_app$e (uul$ ?v0 )?v1 )?v2 )(and (member$ ?v2 (lset$ ?v1 ))(fun_app$d ?v0 ?v2 ))):pattern ((fun_app$d (fun_app$e (uul$ ?v0 )?v1 )?v2 )))):named a4 ))
(assert (! (forall ((?v0 Nat_bool_fun$ )(?v1 Nat_llist$ )(?v2 Nat$ ))(! (= (fun_app$ (fun_app$f (uuk$ ?v0 )?v1 )?v2 )(and (member$a ?v2 (lset$a ?v1 ))(fun_app$ ?v0 ?v2 ))):pattern ((fun_app$ (fun_app$f (uuk$ ?v0 )?v1 )?v2 )))):named a5 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A_llist$ )(?v2 A$ ))(! (= (fun_app$a (fun_app$g (uuj$ ?v0 )?v1 )?v2 )(and (member$b ?v2 (lset$b ?v1 ))(fun_app$a ?v0 ?v2 ))):pattern ((fun_app$a (fun_app$g (uuj$ ?v0 )?v1 )?v2 )))):named a6 ))
(assert (! (forall ((?v0 A_nat_prod_bool_fun$ )(?v1 A_nat_prod_bool_fun$ )(?v2 A_nat_prod$ ))(! (= (fun_app$d (fun_app$h (uuh$ ?v0 )?v1 )?v2 )(and (fun_app$d ?v0 ?v2 )(fun_app$d ?v1 ?v2 ))):pattern ((fun_app$d (fun_app$h (uuh$ ?v0 )?v1 )?v2 )))):named a7 ))
(assert (! (forall ((?v0 Nat_bool_fun$ )(?v1 Nat_bool_fun$ )(?v2 Nat$ ))(! (= (fun_app$ (fun_app$i (uug$ ?v0 )?v1 )?v2 )(and (fun_app$ ?v0 ?v2 )(fun_app$ ?v1 ?v2 ))):pattern ((fun_app$ (fun_app$i (uug$ ?v0 )?v1 )?v2 )))):named a8 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A_bool_fun$ )(?v2 A$ ))(! (= (fun_app$a (fun_app$j (uuf$ ?v0 )?v1 )?v2 )(and (fun_app$a ?v0 ?v2 )(fun_app$a ?v1 ?v2 ))):pattern ((fun_app$a (fun_app$j (uuf$ ?v0 )?v1 )?v2 )))):named a9 ))
(assert (! (forall ((?v0 Bool )(?v1 A_nat_bool_fun_fun$ )(?v2 A$ )(?v3 Nat$ ))(! (= (fun_app$ (fun_app$c (fun_app$k (uum$ ?v0 )?v1 )?v2 )?v3 )(and ?v0 (fun_app$ (fun_app$c ?v1 ?v2 )?v3 ))):pattern ((fun_app$ (fun_app$c (fun_app$k (uum$ ?v0 )?v1 )?v2 )?v3 )))):named a10 ))
(assert (! (forall ((?v0 A$ )(?v1 Nat$ ))(! (= (fun_app$l (fun_app$m uun$ ?v0 )?v1 )?v0 ):pattern ((fun_app$l (fun_app$m uun$ ?v0 )?v1 )))):named a11 ))
(assert (! (forall ((?v0 A_nat_prod$ ))(! (= (fun_app$d uud$ ?v0 )true ):pattern ((fun_app$d uud$ ?v0 )))):named a12 ))
(assert (! (forall ((?v0 Nat$ ))(! (= (fun_app$ uuc$ ?v0 )true ):pattern ((fun_app$ uuc$ ?v0 )))):named a13 ))
(assert (! (forall ((?v0 A$ ))(! (= (fun_app$a uub$ ?v0 )true ):pattern ((fun_app$a uub$ ?v0 )))):named a14 ))
(assert (! (not (= (lfilter$ (case_prod$ uu$ )(lzip$ xs$ (iterates$ suc$ zero$ )))(lfilter$ (fun_app$n (comp$ p$ )uua$ )(lzip$ xs$ (iterates$ suc$ zero$ ))))):named a15 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A_llist$ ))(= (lfilter$a ?v0 (lfilter$a ?v0 ?v1 ))(lfilter$a ?v0 ?v1 ))):named a16 ))
(assert (! (forall ((?v0 Nat_bool_fun$ )(?v1 Nat_llist$ ))(= (lfilter$b ?v0 (lfilter$b ?v0 ?v1 ))(lfilter$b ?v0 ?v1 ))):named a17 ))
(assert (! (forall ((?v0 A_nat_prod_bool_fun$ )(?v1 A_nat_prod_llist$ ))(= (lfilter$ ?v0 (lfilter$ ?v0 ?v1 ))(lfilter$ ?v0 ?v1 ))):named a18 ))
(assert (! (forall ((?v0 A_llist$ ))(= (lfilter$a uub$ ?v0 )?v0 )):named a19 ))
(assert (! (forall ((?v0 Nat_llist$ ))(= (lfilter$b uuc$ ?v0 )?v0 )):named a20 ))
(assert (! (forall ((?v0 A_nat_prod_llist$ ))(= (lfilter$ uud$ ?v0 )?v0 )):named a21 ))
(assert (! (forall ((?v0 A_nat_prod$ ))(=> (member$ ?v0 (lset$ (lzip$ xs$ (iterates$ suc$ zero$ ))))(fun_app$d (case_prod$ uue$ )?v0 ))):named a22 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A_bool_fun$ )(?v2 A_llist$ ))(= (lfilter$a ?v0 (lfilter$a ?v1 ?v2 ))(lfilter$a (fun_app$j (uuf$ ?v0 )?v1 )?v2 ))):named a23 ))
(assert (! (forall ((?v0 Nat_bool_fun$ )(?v1 Nat_bool_fun$ )(?v2 Nat_llist$ ))(= (lfilter$b ?v0 (lfilter$b ?v1 ?v2 ))(lfilter$b (fun_app$i (uug$ ?v0 )?v1 )?v2 ))):named a24 ))
(assert (! (forall ((?v0 A_nat_prod_bool_fun$ )(?v1 A_nat_prod_bool_fun$ )(?v2 A_nat_prod_llist$ ))(= (lfilter$ ?v0 (lfilter$ ?v1 ?v2 ))(lfilter$ (fun_app$h (uuh$ ?v0 )?v1 )?v2 ))):named a25 ))
(assert (! (= (lsublist$ xs$ (collect$ uui$ ))(lmap$ uua$ (lfilter$ (case_prod$ uu$ )(lzip$ xs$ (iterates$ suc$ zero$ ))))):named a26 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A_llist$ ))(= (lset$b (lfilter$a ?v0 ?v1 ))(collect$a (fun_app$g (uuj$ ?v0 )?v1 )))):named a27 ))
(assert (! (forall ((?v0 Nat_bool_fun$ )(?v1 Nat_llist$ ))(= (lset$a (lfilter$b ?v0 ?v1 ))(collect$ (fun_app$f (uuk$ ?v0 )?v1 )))):named a28 ))
(assert (! (forall ((?v0 A_nat_prod_bool_fun$ )(?v1 A_nat_prod_llist$ ))(= (lset$ (lfilter$ ?v0 ?v1 ))(collect$b (fun_app$e (uul$ ?v0 )?v1 )))):named a29 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat_llist$ ))(= (member$a ?v0 (lset$a ?v1 ))(exists ((?v2 Nat$ ))(and (less$ (enat$ ?v2 )(llength$a ?v1 ))(= (lnth$a ?v1 ?v2 )?v0 ))))):named a30 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(= (member$b ?v0 (lset$b ?v1 ))(exists ((?v2 Nat$ ))(and (less$ (enat$ ?v2 )(llength$ ?v1 ))(= (lnth$ ?v1 ?v2 )?v0 ))))):named a31 ))
(assert (! (forall ((?v0 A_nat_prod$ )(?v1 A_nat_prod_llist$ ))(= (member$ ?v0 (lset$ ?v1 ))(exists ((?v2 Nat$ ))(and (less$ (enat$ ?v2 )(llength$b ?v1 ))(= (lnth$b ?v1 ?v2 )?v0 ))))):named a32 ))
(assert (! (forall ((?v0 Bool )(?v1 A_nat_bool_fun_fun$ )(?v2 A_nat_prod$ ))(= (fun_app$d (case_prod$ (fun_app$k (uum$ ?v0 )?v1 ))?v2 )(and ?v0 (fun_app$d (case_prod$ ?v1 )?v2 )))):named a33 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(= (= (enat$ ?v0 )(enat$ ?v1 ))(= ?v0 ?v1 ))):named a34 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A_nat_prod_a_fun$ )(?v2 A_nat_prod$ ))(! (= (fun_app$d (fun_app$n (comp$ ?v0 )?v1 )?v2 )(fun_app$a ?v0 (fun_app$b ?v1 ?v2 ))):pattern ((fun_app$d (fun_app$n (comp$ ?v0 )?v1 )?v2 )))):named a35 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(= (= (fun_app$o suc$ ?v0 )(fun_app$o suc$ ?v1 ))(= ?v0 ?v1 ))):named a36 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(= (= (fun_app$o suc$ ?v0 )(fun_app$o suc$ ?v1 ))(= ?v0 ?v1 ))):named a37 ))
(assert (! (forall ((?v0 A_nat_prod$ ))(= (fst$ ?v0 )(fun_app$b (case_prod$a uun$ )?v0 ))):named a38 ))
(assert (! (forall ((?v0 Enat$ )(?v1 Nat$ ))(=> (less$ ?v0 (enat$ ?v1 ))(exists ((?v2 Nat$ ))(= ?v0 (enat$ ?v2 ))))):named a39 ))
(assert (! (forall ((?v0 Enat$ ))(= (less$ zero$a ?v0 )(not (= ?v0 zero$a )))):named a40 ))
(check-sat )
;(get-unsat-core )
