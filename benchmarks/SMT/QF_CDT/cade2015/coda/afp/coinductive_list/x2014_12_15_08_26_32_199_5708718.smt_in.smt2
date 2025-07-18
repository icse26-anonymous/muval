;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_set$ 0 )
(declare-sort A_a_fun$ 0 )
(declare-sort A_a_prod_set$ 0 )
(declare-sort A_a_a_prod_fun$ 0 )
(declare-sort A_a_prod_a_fun$ 0 )
(declare-sort A_a_a_prod_prod_set$ 0 )
(declare-sort A_a_prod_a_prod_set$ 0 )
(declare-sort A_llist_a_llist_fun$ 0 )
(declare-sort A_a_a_a_prod_prod_fun$ 0 )
(declare-sort A_a_a_prod_a_prod_fun$ 0 )
(declare-sort A_a_a_prod_prod_a_fun$ 0 )
(declare-sort A_a_prod_a_a_prod_fun$ 0 )
(declare-sort A_a_prod_a_prod_a_fun$ 0 )
(declare-sort A_a_prod_a_a_prod_prod_set$ 0 )
(declare-sort A_a_prod_a_a_prod_prod_a_fun$ 0 )
(declare-sort A_a_prod_a_prod_a_a_prod_fun$ 0 )
(declare-sort A_a_prod_llist_a_a_prod_llist_fun$ 0 )
(declare-sort A_a_a_prod_prod_llist_a_a_a_prod_prod_llist_fun$ 0 )
(declare-sort A_a_prod_a_prod_llist_a_a_prod_a_prod_llist_fun$ 0 )
(declare-sort A_a_prod_a_a_prod_prod_llist_a_a_prod_a_a_prod_prod_llist_fun$ 0 )
(declare-codatatypes ()((A_llist$ (lNil$ )(lCons$ (lhd$ A$ )(ltl$ A_llist$ )))))
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
(declare-codatatypes ()((A_a_prod_a_a_prod_prod_llist$ (lNil$a )(lCons$a (lhd$a A_a_prod_a_a_prod_prod$ )(ltl$a A_a_prod_a_a_prod_prod_llist$ )))))
(declare-sort A_a_prod_a_prod$ 0)
(declare-fun fst$b (A_a_prod_a_prod$)A_a_prod$)
(declare-fun snd$b (A_a_prod_a_prod$)A$)
(declare-fun pair$b (A_a_prod$ A$ )A_a_prod_a_prod$)
(declare-codatatypes ()((A_a_prod_a_prod_llist$ (lNil$b )(lCons$b (lhd$b A_a_prod_a_prod$ )(ltl$b A_a_prod_a_prod_llist$ )))))
(declare-sort A_a_a_prod_prod$ 0)
(declare-fun fst$c (A_a_a_prod_prod$)A$)
(declare-fun snd$c (A_a_a_prod_prod$)A_a_prod$)
(declare-fun pair$c (A$ A_a_prod$ )A_a_a_prod_prod$)
(declare-codatatypes ()((A_a_a_prod_prod_llist$ (lNil$c )(lCons$c (lhd$c A_a_a_prod_prod$ )(ltl$c A_a_a_prod_prod_llist$ )))(A_a_prod_llist$ (lNil$d )(lCons$d (lhd$d A_a_prod$ )(ltl$d A_a_prod_llist$ )))))
(declare-sort A_a_a_prod_a_prod_prod$ 0)
(declare-fun fst$d (A_a_a_prod_a_prod_prod$)A$)
(declare-fun snd$d (A_a_a_prod_a_prod_prod$)A_a_prod_a_prod$)
(declare-fun pair$d (A$ A_a_prod_a_prod$ )A_a_a_prod_a_prod_prod$)
(declare-codatatypes ()((A_a_a_prod_a_prod_prod_llist$ (lNil$e )(lCons$e (lhd$e A_a_a_prod_a_prod_prod$ )(ltl$e A_a_a_prod_a_prod_prod_llist$ )))))
(declare-sort A_a_a_a_prod_prod_prod$ 0)
(declare-fun fst$e (A_a_a_a_prod_prod_prod$)A$)
(declare-fun snd$e (A_a_a_a_prod_prod_prod$)A_a_a_prod_prod$)
(declare-fun pair$e (A$ A_a_a_prod_prod$ )A_a_a_a_prod_prod_prod$)
(declare-codatatypes ()((A_a_a_a_prod_prod_prod_llist$ (lNil$f )(lCons$f (lhd$f A_a_a_a_prod_prod_prod$ )(ltl$f A_a_a_a_prod_prod_prod_llist$ )))))
(declare-sort A_a_prod_a_prod_a_prod$ 0)
(declare-fun fst$f (A_a_prod_a_prod_a_prod$)A_a_prod_a_prod$)
(declare-fun snd$f (A_a_prod_a_prod_a_prod$)A$)
(declare-fun pair$f (A_a_prod_a_prod$ A$ )A_a_prod_a_prod_a_prod$)
(declare-codatatypes ()((A_a_prod_a_prod_a_prod_llist$ (lNil$g )(lCons$g (lhd$g A_a_prod_a_prod_a_prod$ )(ltl$g A_a_prod_a_prod_a_prod_llist$ )))))
(declare-sort A_a_a_prod_prod_a_prod$ 0)
(declare-fun fst$g (A_a_a_prod_prod_a_prod$)A_a_a_prod_prod$)
(declare-fun snd$g (A_a_a_prod_prod_a_prod$)A$)
(declare-fun pair$g (A_a_a_prod_prod$ A$ )A_a_a_prod_prod_a_prod$)
(declare-codatatypes ()((A_a_a_prod_prod_a_prod_llist$ (lNil$h )(lCons$h (lhd$h A_a_a_prod_prod_a_prod$ )(ltl$h A_a_a_prod_prod_a_prod_llist$ )))))
(declare-sort A_a_a_prod_a_a_prod_prod_prod$ 0)
(declare-fun fst$h (A_a_a_prod_a_a_prod_prod_prod$)A$)
(declare-fun snd$h (A_a_a_prod_a_a_prod_prod_prod$)A_a_prod_a_a_prod_prod$)
(declare-fun pair$h (A$ A_a_prod_a_a_prod_prod$ )A_a_a_prod_a_a_prod_prod_prod$)
(declare-codatatypes ()((A_a_a_prod_a_a_prod_prod_prod_llist$ (lNil$i )(lCons$i (lhd$i A_a_a_prod_a_a_prod_prod_prod$ )(ltl$i A_a_a_prod_a_a_prod_prod_prod_llist$ )))))
(declare-sort A_a_prod_a_a_prod_a_prod_prod$ 0)
(declare-fun fst$i (A_a_prod_a_a_prod_a_prod_prod$)A_a_prod$)
(declare-fun snd$i (A_a_prod_a_a_prod_a_prod_prod$)A_a_prod_a_prod$)
(declare-fun pair$i (A_a_prod$ A_a_prod_a_prod$ )A_a_prod_a_a_prod_a_prod_prod$)
(declare-codatatypes ()((A_a_prod_a_a_prod_a_prod_prod_llist$ (lNil$j )(lCons$j (lhd$j A_a_prod_a_a_prod_a_prod_prod$ )(ltl$j A_a_prod_a_a_prod_a_prod_prod_llist$ )))))
(declare-fun n$ ()Enat$ )
(declare-fun xs$ ()A_llist$ )
(declare-fun lmap$ (A_a_fun$ A_llist$ )A_llist$ )
(declare-fun lset$ (A_a_prod_a_a_prod_prod_llist$ )A_a_prod_a_a_prod_prod_set$ )
(declare-fun lzip$ (A_llist$ A_llist$ )A_a_prod_llist$ )
(declare-fun plus$ (Enat$ Enat$ )Enat$ )
(declare-fun zero$ ()Enat$ )
(declare-fun ldrop$ (Enat$ )A_llist_a_llist_fun$ )
(declare-fun lmap$a (A_a_prod_a_fun$ A_a_prod_llist$ )A_llist$ )
(declare-fun lmap$b (A_a_a_prod_fun$ A_llist$ )A_a_prod_llist$ )
(declare-fun lmap$c (A_a_prod_a_a_prod_fun$ A_a_prod_llist$ )A_a_prod_llist$ )
(declare-fun lmap$d (A_a_prod_a_prod_a_fun$ A_a_prod_a_prod_llist$ )A_llist$ )
(declare-fun lmap$e (A_a_a_prod_prod_a_fun$ A_a_a_prod_prod_llist$ )A_llist$ )
(declare-fun lmap$f (A_a_a_prod_a_prod_fun$ A_llist$ )A_a_prod_a_prod_llist$ )
(declare-fun lmap$g (A_a_a_a_prod_prod_fun$ A_llist$ )A_a_a_prod_prod_llist$ )
(declare-fun lmap$h (A_a_prod_a_a_prod_prod_a_fun$ A_a_prod_a_a_prod_prod_llist$ )A_llist$ )
(declare-fun lmap$i (A_a_prod_a_prod_a_a_prod_fun$ A_a_prod_a_prod_llist$ )A_a_prod_llist$ )
(declare-fun lset$a (A_a_prod_a_prod_llist$ )A_a_prod_a_prod_set$ )
(declare-fun lset$b (A_a_a_prod_prod_llist$ )A_a_a_prod_prod_set$ )
(declare-fun lset$c (A_a_prod_llist$ )A_a_prod_set$ )
(declare-fun lset$d (A_llist$ )A_set$ )
(declare-fun ltake$ (Enat$ )A_llist_a_llist_fun$ )
(declare-fun lzip$a (A_llist$ A_a_prod_llist$ )A_a_a_prod_prod_llist$ )
(declare-fun lzip$b (A_a_prod_llist$ A_llist$ )A_a_prod_a_prod_llist$ )
(declare-fun lzip$c (A_a_prod_llist$ A_a_prod_llist$ )A_a_prod_a_a_prod_prod_llist$ )
(declare-fun lzip$d (A_llist$ A_a_prod_a_prod_llist$ )A_a_a_prod_a_prod_prod_llist$ )
(declare-fun lzip$e (A_llist$ A_a_a_prod_prod_llist$ )A_a_a_a_prod_prod_prod_llist$ )
(declare-fun lzip$f (A_a_prod_a_prod_llist$ A_llist$ )A_a_prod_a_prod_a_prod_llist$ )
(declare-fun lzip$g (A_a_a_prod_prod_llist$ A_llist$ )A_a_a_prod_prod_a_prod_llist$ )
(declare-fun lzip$h (A_llist$ A_a_prod_a_a_prod_prod_llist$ )A_a_a_prod_a_a_prod_prod_prod_llist$ )
(declare-fun lzip$i (A_a_prod_llist$ A_a_prod_a_prod_llist$ )A_a_prod_a_a_prod_a_prod_prod_llist$ )
(declare-fun ldrop$a (Enat$ )A_a_prod_a_a_prod_prod_llist_a_a_prod_a_a_prod_prod_llist_fun$ )
(declare-fun ldrop$b (Enat$ )A_a_prod_a_prod_llist_a_a_prod_a_prod_llist_fun$ )
(declare-fun ldrop$c (Enat$ )A_a_a_prod_prod_llist_a_a_a_prod_prod_llist_fun$ )
(declare-fun ldrop$d (Enat$ )A_a_prod_llist_a_a_prod_llist_fun$ )
(declare-fun ldrop$e (Enat$ A_a_a_prod_a_prod_prod_llist$ )A_a_a_prod_a_prod_prod_llist$ )
(declare-fun ldrop$f (Enat$ A_a_a_a_prod_prod_prod_llist$ )A_a_a_a_prod_prod_prod_llist$ )
(declare-fun ldrop$g (Enat$ A_a_prod_a_prod_a_prod_llist$ )A_a_prod_a_prod_a_prod_llist$ )
(declare-fun ldrop$h (Enat$ A_a_a_prod_prod_a_prod_llist$ )A_a_a_prod_prod_a_prod_llist$ )
(declare-fun ldrop$i (Enat$ A_a_a_prod_a_a_prod_prod_prod_llist$ )A_a_a_prod_a_a_prod_prod_prod_llist$ )
(declare-fun ldrop$j (Enat$ A_a_prod_a_a_prod_a_prod_prod_llist$ )A_a_prod_a_a_prod_a_prod_prod_llist$ )
(declare-fun ldropn$ (Nat$ A_llist$ )A_llist$ )
(declare-fun ltake$a (Enat$ )A_a_prod_llist_a_a_prod_llist_fun$ )
(declare-fun member$ (A_a_prod_a_a_prod_prod$ A_a_prod_a_a_prod_prod_set$ )Bool )
(declare-fun fun_app$ (A_llist_a_llist_fun$ A_llist$ )A_llist$ )
(declare-fun lprefix$ (A_llist$ A_llist$ )Bool )
(declare-fun member$a (A_a_prod_a_prod$ A_a_prod_a_prod_set$ )Bool )
(declare-fun member$b (A_a_a_prod_prod$ A_a_a_prod_prod_set$ )Bool )
(declare-fun member$c (A_a_prod$ A_a_prod_set$ )Bool )
(declare-fun member$d (A$ A_set$ )Bool )
(declare-fun fun_app$a (A_a_prod_a_a_prod_prod_llist_a_a_prod_a_a_prod_prod_llist_fun$ A_a_prod_a_a_prod_prod_llist$ )A_a_prod_a_a_prod_prod_llist$ )
(declare-fun fun_app$b (A_a_prod_a_prod_llist_a_a_prod_a_prod_llist_fun$ A_a_prod_a_prod_llist$ )A_a_prod_a_prod_llist$ )
(declare-fun fun_app$c (A_a_a_prod_prod_llist_a_a_a_prod_prod_llist_fun$ A_a_a_prod_prod_llist$ )A_a_a_prod_prod_llist$ )
(declare-fun fun_app$d (A_a_prod_llist_a_a_prod_llist_fun$ A_a_prod_llist$ )A_a_prod_llist$ )
(declare-fun lprefix$a (A_a_prod_llist$ A_a_prod_llist$ )Bool )
(declare-fun ldistinct$ (A_llist$ )Bool )
(declare-fun ldistinct$a (A_a_prod_llist$ )Bool )
(assert (! (not (ldistinct$ (fun_app$ (ldrop$ n$ )xs$ ))):named a0 ))
(assert (! (ldistinct$ xs$ ):named a1 ))
(assert (! (forall ((?v0 A_a_prod_a_a_prod_prod_llist$ ))(= (fun_app$a (ldrop$a zero$ )?v0 )?v0 )):named a2 ))
(assert (! (forall ((?v0 A_a_prod_a_prod_llist$ ))(= (fun_app$b (ldrop$b zero$ )?v0 )?v0 )):named a3 ))
(assert (! (forall ((?v0 A_a_a_prod_prod_llist$ ))(= (fun_app$c (ldrop$c zero$ )?v0 )?v0 )):named a4 ))
(assert (! (forall ((?v0 A_a_prod_llist$ ))(= (fun_app$d (ldrop$d zero$ )?v0 )?v0 )):named a5 ))
(assert (! (forall ((?v0 A_llist$ ))(= (fun_app$ (ldrop$ zero$ )?v0 )?v0 )):named a6 ))
(assert (! (= (ldistinct$a lNil$d )true ):named a7 ))
(assert (! (= (ldistinct$ lNil$ )true ):named a8 ))
(assert (! (forall ((?v0 Enat$ )(?v1 Enat$ )(?v2 A_a_prod_a_a_prod_prod_llist$ ))(= (fun_app$a (ldrop$a ?v0 )(fun_app$a (ldrop$a ?v1 )?v2 ))(fun_app$a (ldrop$a (plus$ ?v0 ?v1 ))?v2 ))):named a9 ))
(assert (! (forall ((?v0 Enat$ )(?v1 Enat$ )(?v2 A_a_prod_a_prod_llist$ ))(= (fun_app$b (ldrop$b ?v0 )(fun_app$b (ldrop$b ?v1 )?v2 ))(fun_app$b (ldrop$b (plus$ ?v0 ?v1 ))?v2 ))):named a10 ))
(assert (! (forall ((?v0 Enat$ )(?v1 Enat$ )(?v2 A_a_a_prod_prod_llist$ ))(= (fun_app$c (ldrop$c ?v0 )(fun_app$c (ldrop$c ?v1 )?v2 ))(fun_app$c (ldrop$c (plus$ ?v0 ?v1 ))?v2 ))):named a11 ))
(assert (! (forall ((?v0 Enat$ )(?v1 Enat$ )(?v2 A_a_prod_llist$ ))(= (fun_app$d (ldrop$d ?v0 )(fun_app$d (ldrop$d ?v1 )?v2 ))(fun_app$d (ldrop$d (plus$ ?v0 ?v1 ))?v2 ))):named a12 ))
(assert (! (forall ((?v0 Enat$ )(?v1 Enat$ )(?v2 A_llist$ ))(= (fun_app$ (ldrop$ ?v0 )(fun_app$ (ldrop$ ?v1 )?v2 ))(fun_app$ (ldrop$ (plus$ ?v0 ?v1 ))?v2 ))):named a13 ))
(assert (! (forall ((?v0 Enat$ ))(! (= (fun_app$a (ldrop$a ?v0 )lNil$a )lNil$a ):pattern ((ldrop$a ?v0 )))):named a14 ))
(assert (! (forall ((?v0 Enat$ ))(! (= (fun_app$b (ldrop$b ?v0 )lNil$b )lNil$b ):pattern ((ldrop$b ?v0 )))):named a15 ))
(assert (! (forall ((?v0 Enat$ ))(! (= (fun_app$c (ldrop$c ?v0 )lNil$c )lNil$c ):pattern ((ldrop$c ?v0 )))):named a16 ))
(assert (! (forall ((?v0 Enat$ ))(! (= (fun_app$d (ldrop$d ?v0 )lNil$d )lNil$d ):pattern ((ldrop$d ?v0 )))):named a17 ))
(assert (! (forall ((?v0 Enat$ ))(! (= (fun_app$ (ldrop$ ?v0 )lNil$ )lNil$ ):pattern ((ldrop$ ?v0 )))):named a18 ))
(assert (! (forall ((?v0 Enat$ )(?v1 A_llist$ )(?v2 A_llist$ ))(= (fun_app$d (ldrop$d ?v0 )(lzip$ ?v1 ?v2 ))(lzip$ (fun_app$ (ldrop$ ?v0 )?v1 )(fun_app$ (ldrop$ ?v0 )?v2 )))):named a19 ))
(assert (! (forall ((?v0 Enat$ )(?v1 A_llist$ )(?v2 A_a_prod_llist$ ))(= (fun_app$c (ldrop$c ?v0 )(lzip$a ?v1 ?v2 ))(lzip$a (fun_app$ (ldrop$ ?v0 )?v1 )(fun_app$d (ldrop$d ?v0 )?v2 )))):named a20 ))
(assert (! (forall ((?v0 Enat$ )(?v1 A_a_prod_llist$ )(?v2 A_llist$ ))(= (fun_app$b (ldrop$b ?v0 )(lzip$b ?v1 ?v2 ))(lzip$b (fun_app$d (ldrop$d ?v0 )?v1 )(fun_app$ (ldrop$ ?v0 )?v2 )))):named a21 ))
(assert (! (forall ((?v0 Enat$ )(?v1 A_a_prod_llist$ )(?v2 A_a_prod_llist$ ))(= (fun_app$a (ldrop$a ?v0 )(lzip$c ?v1 ?v2 ))(lzip$c (fun_app$d (ldrop$d ?v0 )?v1 )(fun_app$d (ldrop$d ?v0 )?v2 )))):named a22 ))
(assert (! (forall ((?v0 Enat$ )(?v1 A_llist$ )(?v2 A_a_prod_a_prod_llist$ ))(= (ldrop$e ?v0 (lzip$d ?v1 ?v2 ))(lzip$d (fun_app$ (ldrop$ ?v0 )?v1 )(fun_app$b (ldrop$b ?v0 )?v2 )))):named a23 ))
(assert (! (forall ((?v0 Enat$ )(?v1 A_llist$ )(?v2 A_a_a_prod_prod_llist$ ))(= (ldrop$f ?v0 (lzip$e ?v1 ?v2 ))(lzip$e (fun_app$ (ldrop$ ?v0 )?v1 )(fun_app$c (ldrop$c ?v0 )?v2 )))):named a24 ))
(assert (! (forall ((?v0 Enat$ )(?v1 A_a_prod_a_prod_llist$ )(?v2 A_llist$ ))(= (ldrop$g ?v0 (lzip$f ?v1 ?v2 ))(lzip$f (fun_app$b (ldrop$b ?v0 )?v1 )(fun_app$ (ldrop$ ?v0 )?v2 )))):named a25 ))
(assert (! (forall ((?v0 Enat$ )(?v1 A_a_a_prod_prod_llist$ )(?v2 A_llist$ ))(= (ldrop$h ?v0 (lzip$g ?v1 ?v2 ))(lzip$g (fun_app$c (ldrop$c ?v0 )?v1 )(fun_app$ (ldrop$ ?v0 )?v2 )))):named a26 ))
(assert (! (forall ((?v0 Enat$ )(?v1 A_llist$ )(?v2 A_a_prod_a_a_prod_prod_llist$ ))(= (ldrop$i ?v0 (lzip$h ?v1 ?v2 ))(lzip$h (fun_app$ (ldrop$ ?v0 )?v1 )(fun_app$a (ldrop$a ?v0 )?v2 )))):named a27 ))
(assert (! (forall ((?v0 Enat$ )(?v1 A_a_prod_llist$ )(?v2 A_a_prod_a_prod_llist$ ))(= (ldrop$j ?v0 (lzip$i ?v1 ?v2 ))(lzip$i (fun_app$d (ldrop$d ?v0 )?v1 )(fun_app$b (ldrop$b ?v0 )?v2 )))):named a28 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 Nat$ ))(=> (ldistinct$ ?v0 )(ldistinct$ (ldropn$ ?v1 ?v0 )))):named a29 ))
(assert (! (forall ((?v0 Enat$ )(?v1 A_a_fun$ )(?v2 A_llist$ ))(= (fun_app$ (ldrop$ ?v0 )(lmap$ ?v1 ?v2 ))(lmap$ ?v1 (fun_app$ (ldrop$ ?v0 )?v2 )))):named a30 ))
(assert (! (forall ((?v0 Enat$ )(?v1 A_a_prod_a_fun$ )(?v2 A_a_prod_llist$ ))(= (fun_app$ (ldrop$ ?v0 )(lmap$a ?v1 ?v2 ))(lmap$a ?v1 (fun_app$d (ldrop$d ?v0 )?v2 )))):named a31 ))
(assert (! (forall ((?v0 Enat$ )(?v1 A_a_a_prod_fun$ )(?v2 A_llist$ ))(= (fun_app$d (ldrop$d ?v0 )(lmap$b ?v1 ?v2 ))(lmap$b ?v1 (fun_app$ (ldrop$ ?v0 )?v2 )))):named a32 ))
(assert (! (forall ((?v0 Enat$ )(?v1 A_a_prod_a_a_prod_fun$ )(?v2 A_a_prod_llist$ ))(= (fun_app$d (ldrop$d ?v0 )(lmap$c ?v1 ?v2 ))(lmap$c ?v1 (fun_app$d (ldrop$d ?v0 )?v2 )))):named a33 ))
(assert (! (forall ((?v0 Enat$ )(?v1 A_a_prod_a_prod_a_fun$ )(?v2 A_a_prod_a_prod_llist$ ))(= (fun_app$ (ldrop$ ?v0 )(lmap$d ?v1 ?v2 ))(lmap$d ?v1 (fun_app$b (ldrop$b ?v0 )?v2 )))):named a34 ))
(assert (! (forall ((?v0 Enat$ )(?v1 A_a_a_prod_prod_a_fun$ )(?v2 A_a_a_prod_prod_llist$ ))(= (fun_app$ (ldrop$ ?v0 )(lmap$e ?v1 ?v2 ))(lmap$e ?v1 (fun_app$c (ldrop$c ?v0 )?v2 )))):named a35 ))
(assert (! (forall ((?v0 Enat$ )(?v1 A_a_a_prod_a_prod_fun$ )(?v2 A_llist$ ))(= (fun_app$b (ldrop$b ?v0 )(lmap$f ?v1 ?v2 ))(lmap$f ?v1 (fun_app$ (ldrop$ ?v0 )?v2 )))):named a36 ))
(assert (! (forall ((?v0 Enat$ )(?v1 A_a_a_a_prod_prod_fun$ )(?v2 A_llist$ ))(= (fun_app$c (ldrop$c ?v0 )(lmap$g ?v1 ?v2 ))(lmap$g ?v1 (fun_app$ (ldrop$ ?v0 )?v2 )))):named a37 ))
(assert (! (forall ((?v0 Enat$ )(?v1 A_a_prod_a_a_prod_prod_a_fun$ )(?v2 A_a_prod_a_a_prod_prod_llist$ ))(= (fun_app$ (ldrop$ ?v0 )(lmap$h ?v1 ?v2 ))(lmap$h ?v1 (fun_app$a (ldrop$a ?v0 )?v2 )))):named a38 ))
(assert (! (forall ((?v0 Enat$ )(?v1 A_a_prod_a_prod_a_a_prod_fun$ )(?v2 A_a_prod_a_prod_llist$ ))(= (fun_app$d (ldrop$d ?v0 )(lmap$i ?v1 ?v2 ))(lmap$i ?v1 (fun_app$b (ldrop$b ?v0 )?v2 )))):named a39 ))
(assert (! (ldistinct$a lNil$d ):named a40 ))
(assert (! (ldistinct$ lNil$ ):named a41 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (and (ldistinct$ ?v0 )(lprefix$ ?v1 ?v0 ))(ldistinct$ ?v1 ))):named a42 ))
(assert (! (forall ((?v0 A_llist$ ))(=> (ldistinct$ ?v0 )(ldistinct$ (ltl$ ?v0 )))):named a43 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 Enat$ ))(=> (ldistinct$ ?v0 )(ldistinct$ (fun_app$ (ltake$ ?v1 )?v0 )))):named a44 ))
(assert (! (forall ((?v0 A_a_prod_a_a_prod_prod$ )(?v1 Enat$ )(?v2 A_a_prod_a_a_prod_prod_llist$ ))(=> (member$ ?v0 (lset$ (fun_app$a (ldrop$a ?v1 )?v2 )))(member$ ?v0 (lset$ ?v2 )))):named a45 ))
(assert (! (forall ((?v0 A_a_prod_a_prod$ )(?v1 Enat$ )(?v2 A_a_prod_a_prod_llist$ ))(=> (member$a ?v0 (lset$a (fun_app$b (ldrop$b ?v1 )?v2 )))(member$a ?v0 (lset$a ?v2 )))):named a46 ))
(assert (! (forall ((?v0 A_a_a_prod_prod$ )(?v1 Enat$ )(?v2 A_a_a_prod_prod_llist$ ))(=> (member$b ?v0 (lset$b (fun_app$c (ldrop$c ?v1 )?v2 )))(member$b ?v0 (lset$b ?v2 )))):named a47 ))
(assert (! (forall ((?v0 A_a_prod$ )(?v1 Enat$ )(?v2 A_a_prod_llist$ ))(=> (member$c ?v0 (lset$c (fun_app$d (ldrop$d ?v1 )?v2 )))(member$c ?v0 (lset$c ?v2 )))):named a48 ))
(assert (! (forall ((?v0 A$ )(?v1 Enat$ )(?v2 A_llist$ ))(=> (member$d ?v0 (lset$d (fun_app$ (ldrop$ ?v1 )?v2 )))(member$d ?v0 (lset$d ?v2 )))):named a49 ))
(assert (! (forall ((?v0 A_llist$ ))(lprefix$ ?v0 ?v0 )):named a50 ))
(assert (! (forall ((?v0 A_llist$ ))(lprefix$ ?v0 ?v0 )):named a51 ))
(assert (! (forall ((?v0 A_a_prod_llist$ ))(! (= (lprefix$a lNil$d ?v0 )true ):pattern ((lprefix$a lNil$d ?v0 )))):named a52 ))
(assert (! (forall ((?v0 A_llist$ ))(! (= (lprefix$ lNil$ ?v0 )true ):pattern ((lprefix$ lNil$ ?v0 )))):named a53 ))
(assert (! (forall ((?v0 Enat$ )(?v1 A_llist$ ))(lprefix$ (fun_app$ (ltake$ ?v0 )?v1 )?v1 )):named a54 ))
(assert (! (forall ((?v0 Enat$ ))(! (= (fun_app$d (ltake$a ?v0 )lNil$d )lNil$d ):pattern ((ltake$a ?v0 )))):named a55 ))
(assert (! (forall ((?v0 Enat$ ))(! (= (fun_app$ (ltake$ ?v0 )lNil$ )lNil$ ):pattern ((ltake$ ?v0 )))):named a56 ))
(check-sat )
;(get-unsat-core )
