;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort Nat_nat_fun$ 0 )
(declare-sort A_llist_a_llist_fun$ 0 )
(declare-sort A_a_prod_llist_a_a_prod_llist_fun$ 0 )
(declare-sort A_a_a_prod_prod_llist_a_a_a_prod_prod_llist_fun$ 0 )
(declare-sort A_a_prod_a_prod_llist_a_a_prod_a_prod_llist_fun$ 0 )
(declare-sort A_a_prod_a_a_prod_prod_llist_a_a_prod_a_a_prod_prod_llist_fun$ 0 )
(declare-sort A_llist$ 0)
(declare-fun lNil$ ()A_llist$)
(declare-fun lhd$ (A_llist$)A$)
(declare-fun ltl$ (A_llist$)A_llist$)
(declare-fun lCons$ (A$ A_llist$ )A_llist$)
(declare-sort Nat_option$ 0)
(declare-sort Enat$ 0)
(declare-sort A_a_prod$ 0)
(declare-sort A_a_prod_a_a_prod_prod$ 0)
(declare-fun none$ ()Nat_option$)
(declare-fun the$ (Nat_option$)Nat$)
(declare-fun some$ (Nat$ )Nat_option$)
(declare-fun rep_enat$ (Enat$)Nat_option$)
(declare-fun abs_enat$ (Nat_option$ )Enat$)
(declare-fun fst$ (A_a_prod$)A$)
(declare-fun snd$ (A_a_prod$)A$)
(declare-fun pair$ (A$ A$ )A_a_prod$)
(declare-fun fst$a (A_a_prod_a_a_prod_prod$)A_a_prod$)
(declare-fun snd$a (A_a_prod_a_a_prod_prod$)A_a_prod$)
(declare-fun pair$a (A_a_prod$ A_a_prod$ )A_a_prod_a_a_prod_prod$)
(declare-sort A_a_prod_a_a_prod_prod_llist$ 0)
(declare-fun lNil$a ()A_a_prod_a_a_prod_prod_llist$)
(declare-fun lhd$a (A_a_prod_a_a_prod_prod_llist$)A_a_prod_a_a_prod_prod$)
(declare-fun ltl$a (A_a_prod_a_a_prod_prod_llist$)A_a_prod_a_a_prod_prod_llist$)
(declare-fun lCons$a (A_a_prod_a_a_prod_prod$ A_a_prod_a_a_prod_prod_llist$ )A_a_prod_a_a_prod_prod_llist$)
(declare-sort A_a_prod_a_prod$ 0)
(declare-fun fst$b (A_a_prod_a_prod$)A_a_prod$)
(declare-fun snd$b (A_a_prod_a_prod$)A$)
(declare-fun pair$b (A_a_prod$ A$ )A_a_prod_a_prod$)
(declare-sort A_a_prod_a_prod_llist$ 0)
(declare-fun lNil$b ()A_a_prod_a_prod_llist$)
(declare-fun lhd$b (A_a_prod_a_prod_llist$)A_a_prod_a_prod$)
(declare-fun ltl$b (A_a_prod_a_prod_llist$)A_a_prod_a_prod_llist$)
(declare-fun lCons$b (A_a_prod_a_prod$ A_a_prod_a_prod_llist$ )A_a_prod_a_prod_llist$)
(declare-sort A_a_a_prod_prod$ 0)
(declare-fun fst$c (A_a_a_prod_prod$)A$)
(declare-fun snd$c (A_a_a_prod_prod$)A_a_prod$)
(declare-fun pair$c (A$ A_a_prod$ )A_a_a_prod_prod$)
(declare-sort A_a_a_prod_prod_llist$ 0)
(declare-sort A_a_prod_llist$ 0)
(declare-fun lNil$c ()A_a_a_prod_prod_llist$)
(declare-fun lhd$c (A_a_a_prod_prod_llist$)A_a_a_prod_prod$)
(declare-fun ltl$c (A_a_a_prod_prod_llist$)A_a_a_prod_prod_llist$)
(declare-fun lCons$c (A_a_a_prod_prod$ A_a_a_prod_prod_llist$ )A_a_a_prod_prod_llist$)
(declare-fun lNil$d ()A_a_prod_llist$)
(declare-fun lhd$d (A_a_prod_llist$)A_a_prod$)
(declare-fun ltl$d (A_a_prod_llist$)A_a_prod_llist$)
(declare-fun lCons$d (A_a_prod$ A_a_prod_llist$ )A_a_prod_llist$)
(declare-sort A_a_a_prod_a_prod_prod$ 0)
(declare-fun fst$d (A_a_a_prod_a_prod_prod$)A$)
(declare-fun snd$d (A_a_a_prod_a_prod_prod$)A_a_prod_a_prod$)
(declare-fun pair$d (A$ A_a_prod_a_prod$ )A_a_a_prod_a_prod_prod$)
(declare-sort A_a_a_prod_a_prod_prod_llist$ 0)
(declare-fun lNil$e ()A_a_a_prod_a_prod_prod_llist$)
(declare-fun lhd$e (A_a_a_prod_a_prod_prod_llist$)A_a_a_prod_a_prod_prod$)
(declare-fun ltl$e (A_a_a_prod_a_prod_prod_llist$)A_a_a_prod_a_prod_prod_llist$)
(declare-fun lCons$e (A_a_a_prod_a_prod_prod$ A_a_a_prod_a_prod_prod_llist$ )A_a_a_prod_a_prod_prod_llist$)
(declare-sort A_a_a_a_prod_prod_prod$ 0)
(declare-fun fst$e (A_a_a_a_prod_prod_prod$)A$)
(declare-fun snd$e (A_a_a_a_prod_prod_prod$)A_a_a_prod_prod$)
(declare-fun pair$e (A$ A_a_a_prod_prod$ )A_a_a_a_prod_prod_prod$)
(declare-sort A_a_a_a_prod_prod_prod_llist$ 0)
(declare-fun lNil$f ()A_a_a_a_prod_prod_prod_llist$)
(declare-fun lhd$f (A_a_a_a_prod_prod_prod_llist$)A_a_a_a_prod_prod_prod$)
(declare-fun ltl$f (A_a_a_a_prod_prod_prod_llist$)A_a_a_a_prod_prod_prod_llist$)
(declare-fun lCons$f (A_a_a_a_prod_prod_prod$ A_a_a_a_prod_prod_prod_llist$ )A_a_a_a_prod_prod_prod_llist$)
(declare-sort A_a_prod_a_prod_a_prod$ 0)
(declare-fun fst$f (A_a_prod_a_prod_a_prod$)A_a_prod_a_prod$)
(declare-fun snd$f (A_a_prod_a_prod_a_prod$)A$)
(declare-fun pair$f (A_a_prod_a_prod$ A$ )A_a_prod_a_prod_a_prod$)
(declare-sort A_a_prod_a_prod_a_prod_llist$ 0)
(declare-fun lNil$g ()A_a_prod_a_prod_a_prod_llist$)
(declare-fun lhd$g (A_a_prod_a_prod_a_prod_llist$)A_a_prod_a_prod_a_prod$)
(declare-fun ltl$g (A_a_prod_a_prod_a_prod_llist$)A_a_prod_a_prod_a_prod_llist$)
(declare-fun lCons$g (A_a_prod_a_prod_a_prod$ A_a_prod_a_prod_a_prod_llist$ )A_a_prod_a_prod_a_prod_llist$)
(declare-sort A_a_a_prod_prod_a_prod$ 0)
(declare-fun fst$g (A_a_a_prod_prod_a_prod$)A_a_a_prod_prod$)
(declare-fun snd$g (A_a_a_prod_prod_a_prod$)A$)
(declare-fun pair$g (A_a_a_prod_prod$ A$ )A_a_a_prod_prod_a_prod$)
(declare-sort A_a_a_prod_prod_a_prod_llist$ 0)
(declare-fun lNil$h ()A_a_a_prod_prod_a_prod_llist$)
(declare-fun lhd$h (A_a_a_prod_prod_a_prod_llist$)A_a_a_prod_prod_a_prod$)
(declare-fun ltl$h (A_a_a_prod_prod_a_prod_llist$)A_a_a_prod_prod_a_prod_llist$)
(declare-fun lCons$h (A_a_a_prod_prod_a_prod$ A_a_a_prod_prod_a_prod_llist$ )A_a_a_prod_prod_a_prod_llist$)
(declare-sort A_a_a_prod_a_a_prod_prod_prod$ 0)
(declare-fun fst$h (A_a_a_prod_a_a_prod_prod_prod$)A$)
(declare-fun snd$h (A_a_a_prod_a_a_prod_prod_prod$)A_a_prod_a_a_prod_prod$)
(declare-fun pair$h (A$ A_a_prod_a_a_prod_prod$ )A_a_a_prod_a_a_prod_prod_prod$)
(declare-sort A_a_a_prod_a_a_prod_prod_prod_llist$ 0)
(declare-fun lNil$i ()A_a_a_prod_a_a_prod_prod_prod_llist$)
(declare-fun lhd$i (A_a_a_prod_a_a_prod_prod_prod_llist$)A_a_a_prod_a_a_prod_prod_prod$)
(declare-fun ltl$i (A_a_a_prod_a_a_prod_prod_prod_llist$)A_a_a_prod_a_a_prod_prod_prod_llist$)
(declare-fun lCons$i (A_a_a_prod_a_a_prod_prod_prod$ A_a_a_prod_a_a_prod_prod_prod_llist$ )A_a_a_prod_a_a_prod_prod_prod_llist$)
(declare-sort A_a_prod_a_a_prod_a_prod_prod$ 0)
(declare-fun fst$i (A_a_prod_a_a_prod_a_prod_prod$)A_a_prod$)
(declare-fun snd$i (A_a_prod_a_a_prod_a_prod_prod$)A_a_prod_a_prod$)
(declare-fun pair$i (A_a_prod$ A_a_prod_a_prod$ )A_a_prod_a_a_prod_a_prod_prod$)
(declare-sort A_a_prod_a_a_prod_a_prod_prod_llist$ 0)
(declare-fun lNil$j ()A_a_prod_a_a_prod_a_prod_prod_llist$)
(declare-fun lhd$j (A_a_prod_a_a_prod_a_prod_prod_llist$)A_a_prod_a_a_prod_a_prod_prod$)
(declare-fun ltl$j (A_a_prod_a_a_prod_a_prod_prod_llist$)A_a_prod_a_a_prod_a_prod_prod_llist$)
(declare-fun lCons$j (A_a_prod_a_a_prod_a_prod_prod$ A_a_prod_a_a_prod_a_prod_prod_llist$ )A_a_prod_a_a_prod_a_prod_prod_llist$)
(declare-fun na$ ()Nat$ )
(declare-fun suc$ (Nat$ )Nat$ )
(declare-fun xsa$ ()A_llist$ )
(declare-fun enat$ (Nat$ )Enat$ )
(declare-fun less$ (Enat$ Enat$ )Bool )
(declare-fun lzip$ (A_llist$ A_llist$ )A_a_prod_llist$ )
(declare-fun plus$ (Nat$ )Nat_nat_fun$ )
(declare-fun zero$ ()Nat$ )
(declare-fun llast$ (A_llist$ )A$ )
(declare-fun lzip$a (A_llist$ A_a_prod_llist$ )A_a_a_prod_prod_llist$ )
(declare-fun lzip$b (A_a_prod_llist$ A_llist$ )A_a_prod_a_prod_llist$ )
(declare-fun lzip$c (A_a_prod_llist$ A_a_prod_llist$ )A_a_prod_a_a_prod_prod_llist$ )
(declare-fun lzip$d (A_llist$ A_a_prod_a_prod_llist$ )A_a_a_prod_a_prod_prod_llist$ )
(declare-fun lzip$e (A_llist$ A_a_a_prod_prod_llist$ )A_a_a_a_prod_prod_prod_llist$ )
(declare-fun lzip$f (A_a_prod_a_prod_llist$ A_llist$ )A_a_prod_a_prod_a_prod_llist$ )
(declare-fun lzip$g (A_a_a_prod_prod_llist$ A_llist$ )A_a_a_prod_prod_a_prod_llist$ )
(declare-fun lzip$h (A_llist$ A_a_prod_a_a_prod_prod_llist$ )A_a_a_prod_a_a_prod_prod_prod_llist$ )
(declare-fun lzip$i (A_a_prod_llist$ A_a_prod_a_prod_llist$ )A_a_prod_a_a_prod_a_prod_prod_llist$ )
(declare-fun ldropn$ (Nat$ )A_llist_a_llist_fun$ )
(declare-fun llast$a (A_a_prod_llist$ )A_a_prod$ )
(declare-fun fun_app$ (A_llist_a_llist_fun$ A_llist$ )A_llist$ )
(declare-fun ldropn$a (Nat$ )A_a_prod_a_a_prod_prod_llist_a_a_prod_a_a_prod_prod_llist_fun$ )
(declare-fun ldropn$b (Nat$ )A_a_prod_a_prod_llist_a_a_prod_a_prod_llist_fun$ )
(declare-fun ldropn$c (Nat$ )A_a_a_prod_prod_llist_a_a_a_prod_prod_llist_fun$ )
(declare-fun ldropn$d (Nat$ )A_a_prod_llist_a_a_prod_llist_fun$ )
(declare-fun ldropn$e (Nat$ A_a_a_prod_a_prod_prod_llist$ )A_a_a_prod_a_prod_prod_llist$ )
(declare-fun ldropn$f (Nat$ A_a_a_a_prod_prod_prod_llist$ )A_a_a_a_prod_prod_prod_llist$ )
(declare-fun ldropn$g (Nat$ A_a_prod_a_prod_a_prod_llist$ )A_a_prod_a_prod_a_prod_llist$ )
(declare-fun ldropn$h (Nat$ A_a_a_prod_prod_a_prod_llist$ )A_a_a_prod_prod_a_prod_llist$ )
(declare-fun ldropn$i (Nat$ A_a_a_prod_a_a_prod_prod_prod_llist$ )A_a_a_prod_a_a_prod_prod_prod_llist$ )
(declare-fun ldropn$j (Nat$ A_a_prod_a_a_prod_a_prod_prod_llist$ )A_a_prod_a_a_prod_a_prod_prod_llist$ )
(declare-fun llength$ (A_llist$ )Enat$ )
(declare-fun fun_app$a (A_a_prod_a_a_prod_prod_llist_a_a_prod_a_a_prod_prod_llist_fun$ A_a_prod_a_a_prod_prod_llist$ )A_a_prod_a_a_prod_prod_llist$ )
(declare-fun fun_app$b (A_a_prod_a_prod_llist_a_a_prod_a_prod_llist_fun$ A_a_prod_a_prod_llist$ )A_a_prod_a_prod_llist$ )
(declare-fun fun_app$c (A_a_a_prod_prod_llist_a_a_a_prod_prod_llist_fun$ A_a_a_prod_prod_llist$ )A_a_a_prod_prod_llist$ )
(declare-fun fun_app$d (A_a_prod_llist_a_a_prod_llist_fun$ A_a_prod_llist$ )A_a_prod_llist$ )
(declare-fun fun_app$e (Nat_nat_fun$ Nat$ )Nat$ )
(assert (! (not (= (llast$ (fun_app$ (ldropn$ (suc$ na$ ))xsa$ ))(llast$ xsa$ ))):named a0 ))
(assert (! (forall ((?v0 A_llist$ ))(=> (less$ (enat$ na$ )(llength$ ?v0 ))(= (llast$ (fun_app$ (ldropn$ na$ )?v0 ))(llast$ ?v0 )))):named a1 ))
(assert (! (less$ (enat$ (suc$ na$ ))(llength$ xsa$ )):named a2 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(= (= (suc$ ?v0 )(suc$ ?v1 ))(= ?v0 ?v1 ))):named a3 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(= (= (suc$ ?v0 )(suc$ ?v1 ))(= ?v0 ?v1 ))):named a4 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(=> (= (suc$ ?v0 )(suc$ ?v1 ))(= ?v0 ?v1 ))):named a5 ))
(assert (! (forall ((?v0 Nat$ ))(not (= ?v0 (suc$ ?v0 )))):named a6 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_prod_a_a_prod_prod$ )(?v2 A_a_prod_a_a_prod_prod_llist$ ))(! (= (fun_app$a (ldropn$a (suc$ ?v0 ))(lCons$a ?v1 ?v2 ))(fun_app$a (ldropn$a ?v0 )?v2 )):pattern ((fun_app$a (ldropn$a (suc$ ?v0 ))(lCons$a ?v1 ?v2 ))))):named a7 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_prod_a_prod$ )(?v2 A_a_prod_a_prod_llist$ ))(! (= (fun_app$b (ldropn$b (suc$ ?v0 ))(lCons$b ?v1 ?v2 ))(fun_app$b (ldropn$b ?v0 )?v2 )):pattern ((fun_app$b (ldropn$b (suc$ ?v0 ))(lCons$b ?v1 ?v2 ))))):named a8 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_a_prod_prod$ )(?v2 A_a_a_prod_prod_llist$ ))(! (= (fun_app$c (ldropn$c (suc$ ?v0 ))(lCons$c ?v1 ?v2 ))(fun_app$c (ldropn$c ?v0 )?v2 )):pattern ((fun_app$c (ldropn$c (suc$ ?v0 ))(lCons$c ?v1 ?v2 ))))):named a9 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_prod$ )(?v2 A_a_prod_llist$ ))(! (= (fun_app$d (ldropn$d (suc$ ?v0 ))(lCons$d ?v1 ?v2 ))(fun_app$d (ldropn$d ?v0 )?v2 )):pattern ((fun_app$d (ldropn$d (suc$ ?v0 ))(lCons$d ?v1 ?v2 ))))):named a10 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A$ )(?v2 A_llist$ ))(! (= (fun_app$ (ldropn$ (suc$ ?v0 ))(lCons$ ?v1 ?v2 ))(fun_app$ (ldropn$ ?v0 )?v2 )):pattern ((fun_app$ (ldropn$ (suc$ ?v0 ))(lCons$ ?v1 ?v2 ))))):named a11 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_prod_a_a_prod_prod_llist$ ))(! (= (fun_app$a (ldropn$a (suc$ ?v0 ))?v1 )(fun_app$a (ldropn$a ?v0 )(ltl$a ?v1 ))):pattern ((fun_app$a (ldropn$a (suc$ ?v0 ))?v1 )))):named a12 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_prod_a_prod_llist$ ))(! (= (fun_app$b (ldropn$b (suc$ ?v0 ))?v1 )(fun_app$b (ldropn$b ?v0 )(ltl$b ?v1 ))):pattern ((fun_app$b (ldropn$b (suc$ ?v0 ))?v1 )))):named a13 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_a_prod_prod_llist$ ))(! (= (fun_app$c (ldropn$c (suc$ ?v0 ))?v1 )(fun_app$c (ldropn$c ?v0 )(ltl$c ?v1 ))):pattern ((fun_app$c (ldropn$c (suc$ ?v0 ))?v1 )))):named a14 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_prod_llist$ ))(! (= (fun_app$d (ldropn$d (suc$ ?v0 ))?v1 )(fun_app$d (ldropn$d ?v0 )(ltl$d ?v1 ))):pattern ((fun_app$d (ldropn$d (suc$ ?v0 ))?v1 )))):named a15 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_llist$ ))(! (= (fun_app$ (ldropn$ (suc$ ?v0 ))?v1 )(fun_app$ (ldropn$ ?v0 )(ltl$ ?v1 ))):pattern ((fun_app$ (ldropn$ (suc$ ?v0 ))?v1 )))):named a16 ))
(assert (! (forall ((?v0 A_a_prod_a_a_prod_prod_llist$ ))(! (= (fun_app$a (ldropn$a zero$ )?v0 )?v0 ):pattern ((fun_app$a (ldropn$a zero$ )?v0 )))):named a17 ))
(assert (! (forall ((?v0 A_a_prod_a_prod_llist$ ))(! (= (fun_app$b (ldropn$b zero$ )?v0 )?v0 ):pattern ((fun_app$b (ldropn$b zero$ )?v0 )))):named a18 ))
(assert (! (forall ((?v0 A_a_a_prod_prod_llist$ ))(! (= (fun_app$c (ldropn$c zero$ )?v0 )?v0 ):pattern ((fun_app$c (ldropn$c zero$ )?v0 )))):named a19 ))
(assert (! (forall ((?v0 A_a_prod_llist$ ))(! (= (fun_app$d (ldropn$d zero$ )?v0 )?v0 ):pattern ((fun_app$d (ldropn$d zero$ )?v0 )))):named a20 ))
(assert (! (forall ((?v0 A_llist$ ))(! (= (fun_app$ (ldropn$ zero$ )?v0 )?v0 ):pattern ((fun_app$ (ldropn$ zero$ )?v0 )))):named a21 ))
(assert (! (forall ((?v0 A_a_prod$ )(?v1 A_a_prod$ )(?v2 A_a_prod_llist$ ))(! (= (llast$a (lCons$d ?v0 (lCons$d ?v1 ?v2 )))(llast$a (lCons$d ?v1 ?v2 ))):pattern ((lCons$d ?v0 (lCons$d ?v1 ?v2 ))))):named a22 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ )(?v2 A_llist$ ))(! (= (llast$ (lCons$ ?v0 (lCons$ ?v1 ?v2 )))(llast$ (lCons$ ?v1 ?v2 ))):pattern ((lCons$ ?v0 (lCons$ ?v1 ?v2 ))))):named a23 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 A_a_prod_a_a_prod_prod_llist$ ))(= (fun_app$a (ldropn$a ?v0 )(fun_app$a (ldropn$a ?v1 )?v2 ))(fun_app$a (ldropn$a (fun_app$e (plus$ ?v0 )?v1 ))?v2 ))):named a24 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 A_a_prod_a_prod_llist$ ))(= (fun_app$b (ldropn$b ?v0 )(fun_app$b (ldropn$b ?v1 )?v2 ))(fun_app$b (ldropn$b (fun_app$e (plus$ ?v0 )?v1 ))?v2 ))):named a25 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 A_a_a_prod_prod_llist$ ))(= (fun_app$c (ldropn$c ?v0 )(fun_app$c (ldropn$c ?v1 )?v2 ))(fun_app$c (ldropn$c (fun_app$e (plus$ ?v0 )?v1 ))?v2 ))):named a26 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 A_a_prod_llist$ ))(= (fun_app$d (ldropn$d ?v0 )(fun_app$d (ldropn$d ?v1 )?v2 ))(fun_app$d (ldropn$d (fun_app$e (plus$ ?v0 )?v1 ))?v2 ))):named a27 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 A_llist$ ))(= (fun_app$ (ldropn$ ?v0 )(fun_app$ (ldropn$ ?v1 )?v2 ))(fun_app$ (ldropn$ (fun_app$e (plus$ ?v0 )?v1 ))?v2 ))):named a28 ))
(assert (! (forall ((?v0 Nat$ ))(! (= (fun_app$a (ldropn$a ?v0 )lNil$a )lNil$a ):pattern ((ldropn$a ?v0 )))):named a29 ))
(assert (! (forall ((?v0 Nat$ ))(! (= (fun_app$b (ldropn$b ?v0 )lNil$b )lNil$b ):pattern ((ldropn$b ?v0 )))):named a30 ))
(assert (! (forall ((?v0 Nat$ ))(! (= (fun_app$c (ldropn$c ?v0 )lNil$c )lNil$c ):pattern ((ldropn$c ?v0 )))):named a31 ))
(assert (! (forall ((?v0 Nat$ ))(! (= (fun_app$d (ldropn$d ?v0 )lNil$d )lNil$d ):pattern ((ldropn$d ?v0 )))):named a32 ))
(assert (! (forall ((?v0 Nat$ ))(! (= (fun_app$ (ldropn$ ?v0 )lNil$ )lNil$ ):pattern ((ldropn$ ?v0 )))):named a33 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_llist$ )(?v2 A_llist$ ))(= (fun_app$d (ldropn$d ?v0 )(lzip$ ?v1 ?v2 ))(lzip$ (fun_app$ (ldropn$ ?v0 )?v1 )(fun_app$ (ldropn$ ?v0 )?v2 )))):named a34 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_llist$ )(?v2 A_a_prod_llist$ ))(= (fun_app$c (ldropn$c ?v0 )(lzip$a ?v1 ?v2 ))(lzip$a (fun_app$ (ldropn$ ?v0 )?v1 )(fun_app$d (ldropn$d ?v0 )?v2 )))):named a35 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_prod_llist$ )(?v2 A_llist$ ))(= (fun_app$b (ldropn$b ?v0 )(lzip$b ?v1 ?v2 ))(lzip$b (fun_app$d (ldropn$d ?v0 )?v1 )(fun_app$ (ldropn$ ?v0 )?v2 )))):named a36 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_prod_llist$ )(?v2 A_a_prod_llist$ ))(= (fun_app$a (ldropn$a ?v0 )(lzip$c ?v1 ?v2 ))(lzip$c (fun_app$d (ldropn$d ?v0 )?v1 )(fun_app$d (ldropn$d ?v0 )?v2 )))):named a37 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_llist$ )(?v2 A_a_prod_a_prod_llist$ ))(= (ldropn$e ?v0 (lzip$d ?v1 ?v2 ))(lzip$d (fun_app$ (ldropn$ ?v0 )?v1 )(fun_app$b (ldropn$b ?v0 )?v2 )))):named a38 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_llist$ )(?v2 A_a_a_prod_prod_llist$ ))(= (ldropn$f ?v0 (lzip$e ?v1 ?v2 ))(lzip$e (fun_app$ (ldropn$ ?v0 )?v1 )(fun_app$c (ldropn$c ?v0 )?v2 )))):named a39 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_prod_a_prod_llist$ )(?v2 A_llist$ ))(= (ldropn$g ?v0 (lzip$f ?v1 ?v2 ))(lzip$f (fun_app$b (ldropn$b ?v0 )?v1 )(fun_app$ (ldropn$ ?v0 )?v2 )))):named a40 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_a_prod_prod_llist$ )(?v2 A_llist$ ))(= (ldropn$h ?v0 (lzip$g ?v1 ?v2 ))(lzip$g (fun_app$c (ldropn$c ?v0 )?v1 )(fun_app$ (ldropn$ ?v0 )?v2 )))):named a41 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_llist$ )(?v2 A_a_prod_a_a_prod_prod_llist$ ))(= (ldropn$i ?v0 (lzip$h ?v1 ?v2 ))(lzip$h (fun_app$ (ldropn$ ?v0 )?v1 )(fun_app$a (ldropn$a ?v0 )?v2 )))):named a42 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_prod_llist$ )(?v2 A_a_prod_a_prod_llist$ ))(= (ldropn$j ?v0 (lzip$i ?v1 ?v2 ))(lzip$i (fun_app$d (ldropn$d ?v0 )?v1 )(fun_app$b (ldropn$b ?v0 )?v2 )))):named a43 ))
(assert (! (forall ((?v0 A_a_prod$ )(?v1 A_a_prod_llist$ )(?v2 A_a_prod$ )(?v3 A_a_prod_llist$ ))(= (= (lCons$d ?v0 ?v1 )(lCons$d ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a44 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A$ )(?v3 A_llist$ ))(= (= (lCons$ ?v0 ?v1 )(lCons$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a45 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(= (= (fun_app$e (plus$ ?v0 )?v1 )zero$ )(and (= ?v0 zero$ )(= ?v1 zero$ )))):named a46 ))
(assert (! (forall ((?v0 Nat$ ))(! (= (fun_app$e (plus$ ?v0 )zero$ )?v0 ):pattern ((plus$ ?v0 )))):named a47 ))
(check-sat )
;(get-unsat-core )
