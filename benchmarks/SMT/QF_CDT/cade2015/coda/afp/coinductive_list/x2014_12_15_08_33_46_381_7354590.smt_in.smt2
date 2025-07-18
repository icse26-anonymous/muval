;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_a_fun$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort A_llist_set$ 0 )
(declare-sort A_llist_bool_fun$ 0 )
(declare-sort A_a_prod_bool_fun$ 0 )
(declare-sort A_llist_a_llist_fun$ 0 )
(declare-sort A_a_prod_a_a_prod_fun$ 0 )
(declare-sort A_a_llist_prod_bool_fun$ 0 )
(declare-sort A_llist_a_prod_bool_fun$ 0 )
(declare-sort A_a_a_prod_prod_bool_fun$ 0 )
(declare-sort A_a_prod_a_prod_bool_fun$ 0 )
(declare-sort A_llist_a_llist_prod_bool_fun$ 0 )
(declare-sort A_a_a_llist_prod_prod_bool_fun$ 0 )
(declare-sort A_a_llist_a_prod_prod_bool_fun$ 0 )
(declare-sort A_a_llist_prod_a_a_llist_prod_fun$ 0 )
(declare-sort A_llist_a_prod_a_llist_a_prod_fun$ 0 )
(declare-sort A_a_a_prod_prod_a_a_a_prod_prod_fun$ 0 )
(declare-sort A_a_prod_a_prod_a_a_prod_a_prod_fun$ 0 )
(declare-sort A_llist_a_llist_prod_a_llist_a_llist_prod_fun$ 0 )
(declare-sort A_a_a_llist_prod_prod_a_a_a_llist_prod_prod_fun$ 0 )
(declare-sort A_a_llist_a_prod_prod_a_a_llist_a_prod_prod_fun$ 0 )
(declare-codatatypes ()((A_llist$ (lNil$ )(lCons$ (lhd$ A$ )(ltl$ A_llist$ )))(A_llist_llist$ (lNil$a )(lCons$a (lhd$a A_llist$ )(ltl$a A_llist_llist$ )))))
(declare-sort A_a_prod$ 0)
(declare-fun fst$ (A_a_prod$)A$)
(declare-fun snd$ (A_a_prod$)A$)
(declare-fun pair$ (A$ A$ )A_a_prod$)
(declare-codatatypes ()((A_a_prod_llist$ (lNil$b )(lCons$b (lhd$b A_a_prod$ )(ltl$b A_a_prod_llist$ )))))
(declare-sort A_llist_a_prod$ 0)
(declare-fun fst$a (A_llist_a_prod$)A_llist$)
(declare-fun snd$a (A_llist_a_prod$)A$)
(declare-fun pair$a (A_llist$ A$ )A_llist_a_prod$)
(declare-codatatypes ()((A_llist_a_prod_llist$ (lNil$c )(lCons$c (lhd$c A_llist_a_prod$ )(ltl$c A_llist_a_prod_llist$ )))))
(declare-sort A_a_llist_prod$ 0)
(declare-fun fst$b (A_a_llist_prod$)A$)
(declare-fun snd$b (A_a_llist_prod$)A_llist$)
(declare-fun pair$b (A$ A_llist$ )A_a_llist_prod$)
(declare-codatatypes ()((A_a_llist_prod_llist$ (lNil$d )(lCons$d (lhd$d A_a_llist_prod$ )(ltl$d A_a_llist_prod_llist$ )))))
(declare-sort A_llist_a_llist_prod$ 0)
(declare-fun fst$c (A_llist_a_llist_prod$)A_llist$)
(declare-fun snd$c (A_llist_a_llist_prod$)A_llist$)
(declare-fun pair$c (A_llist$ A_llist$ )A_llist_a_llist_prod$)
(declare-codatatypes ()((A_llist_a_llist_prod_llist$ (lNil$e )(lCons$e (lhd$e A_llist_a_llist_prod$ )(ltl$e A_llist_a_llist_prod_llist$ )))))
(declare-sort A_a_prod_a_prod$ 0)
(declare-fun fst$d (A_a_prod_a_prod$)A_a_prod$)
(declare-fun snd$d (A_a_prod_a_prod$)A$)
(declare-fun pair$d (A_a_prod$ A$ )A_a_prod_a_prod$)
(declare-codatatypes ()((A_a_prod_a_prod_llist$ (lNil$f )(lCons$f (lhd$f A_a_prod_a_prod$ )(ltl$f A_a_prod_a_prod_llist$ )))))
(declare-sort A_a_a_prod_prod$ 0)
(declare-fun fst$e (A_a_a_prod_prod$)A$)
(declare-fun snd$e (A_a_a_prod_prod$)A_a_prod$)
(declare-fun pair$e (A$ A_a_prod$ )A_a_a_prod_prod$)
(declare-codatatypes ()((A_a_a_prod_prod_llist$ (lNil$g )(lCons$g (lhd$g A_a_a_prod_prod$ )(ltl$g A_a_a_prod_prod_llist$ )))))
(declare-sort A_a_llist_a_prod_prod$ 0)
(declare-fun fst$f (A_a_llist_a_prod_prod$)A$)
(declare-fun snd$f (A_a_llist_a_prod_prod$)A_llist_a_prod$)
(declare-fun pair$f (A$ A_llist_a_prod$ )A_a_llist_a_prod_prod$)
(declare-codatatypes ()((A_a_llist_a_prod_prod_llist$ (lNil$h )(lCons$h (lhd$h A_a_llist_a_prod_prod$ )(ltl$h A_a_llist_a_prod_prod_llist$ )))))
(declare-sort A_a_a_llist_prod_prod$ 0)
(declare-fun fst$g (A_a_a_llist_prod_prod$)A$)
(declare-fun snd$g (A_a_a_llist_prod_prod$)A_a_llist_prod$)
(declare-fun pair$g (A$ A_a_llist_prod$ )A_a_a_llist_prod_prod$)
(declare-codatatypes ()((A_a_a_llist_prod_prod_llist$ (lNil$i )(lCons$i (lhd$i A_a_a_llist_prod_prod$ )(ltl$i A_a_a_llist_prod_prod_llist$ )))))
(declare-sort A_llist_a_a_prod_prod$ 0)
(declare-fun fst$h (A_llist_a_a_prod_prod$)A_llist$)
(declare-fun snd$h (A_llist_a_a_prod_prod$)A_a_prod$)
(declare-fun pair$h (A_llist$ A_a_prod$ )A_llist_a_a_prod_prod$)
(declare-codatatypes ()((A_llist_a_a_prod_prod_llist$ (lNil$j )(lCons$j (lhd$j A_llist_a_a_prod_prod$ )(ltl$j A_llist_a_a_prod_prod_llist$ )))))
(declare-sort A_llist_a_prod_a_prod$ 0)
(declare-fun fst$i (A_llist_a_prod_a_prod$)A_llist_a_prod$)
(declare-fun snd$i (A_llist_a_prod_a_prod$)A$)
(declare-fun pair$i (A_llist_a_prod$ A$ )A_llist_a_prod_a_prod$)
(declare-codatatypes ()((A_llist_a_prod_a_prod_llist$ (lNil$k )(lCons$k (lhd$k A_llist_a_prod_a_prod$ )(ltl$k A_llist_a_prod_a_prod_llist$ )))))
(declare-fun uu$ ()A_llist_bool_fun$ )
(declare-fun uua$ ()A_a_prod_bool_fun$ )
(declare-fun uub$ ()A_a_llist_prod_bool_fun$ )
(declare-fun uuc$ ()A_llist_a_prod_bool_fun$ )
(declare-fun uud$ ()A_llist_a_llist_prod_bool_fun$ )
(declare-fun uue$ ()A_bool_fun$ )
(declare-fun uuf$ ()A_llist_bool_fun$ )
(declare-fun xss$ ()A_llist_llist$ )
(declare-fun lset$ (A_llist_llist$ )A_llist_set$ )
(declare-fun lzip$ (A_llist$ A_llist$ )A_a_prod_llist$ )
(declare-fun lnull$ (A_llist$ )Bool )
(declare-fun lzip$a (A_llist$ A_llist_llist$ )A_a_llist_prod_llist$ )
(declare-fun lzip$b (A_llist_llist$ A_llist$ )A_llist_a_prod_llist$ )
(declare-fun lzip$c (A_llist_llist$ A_llist_llist$ )A_llist_a_llist_prod_llist$ )
(declare-fun lzip$d (A_llist$ A_a_prod_llist$ )A_a_a_prod_prod_llist$ )
(declare-fun lzip$e (A_a_prod_llist$ A_llist$ )A_a_prod_a_prod_llist$ )
(declare-fun lzip$f (A_llist$ A_llist_a_prod_llist$ )A_a_llist_a_prod_prod_llist$ )
(declare-fun lzip$g (A_llist$ A_a_llist_prod_llist$ )A_a_a_llist_prod_prod_llist$ )
(declare-fun lzip$h (A_llist_llist$ A_a_prod_llist$ )A_llist_a_a_prod_prod_llist$ )
(declare-fun lzip$i (A_llist_a_prod_llist$ A_llist$ )A_llist_a_prod_a_prod_llist$ )
(declare-fun ldropn$ (Nat$ )A_llist_a_llist_fun$ )
(declare-fun lnull$a (A_llist_llist$ )Bool )
(declare-fun lnull$b (A_a_prod_llist$ )Bool )
(declare-fun lnull$c (A_llist_a_prod_llist$ )Bool )
(declare-fun lnull$d (A_a_llist_prod_llist$ )Bool )
(declare-fun lnull$e (A_llist_a_llist_prod_llist$ )Bool )
(declare-fun lnull$f (A_a_prod_a_prod_llist$ )Bool )
(declare-fun lnull$g (A_a_a_prod_prod_llist$ )Bool )
(declare-fun lnull$h (A_a_llist_a_prod_prod_llist$ )Bool )
(declare-fun lnull$i (A_a_a_llist_prod_prod_llist$ )Bool )
(declare-fun member$ (A_llist$ A_llist_set$ )Bool )
(declare-fun fun_app$ (A_llist_bool_fun$ A_llist$ )Bool )
(declare-fun lconcat$ (A_llist_llist$ )A_llist$ )
(declare-fun ldropn$a (Nat$ A_llist_llist$ )A_llist_llist$ )
(declare-fun ldropn$b (Nat$ A_a_prod_llist$ )A_a_prod_llist$ )
(declare-fun ldropn$c (Nat$ A_llist_a_prod_llist$ )A_llist_a_prod_llist$ )
(declare-fun ldropn$d (Nat$ A_a_llist_prod_llist$ )A_a_llist_prod_llist$ )
(declare-fun ldropn$e (Nat$ A_llist_a_llist_prod_llist$ )A_llist_a_llist_prod_llist$ )
(declare-fun ldropn$f (Nat$ A_a_prod_a_prod_llist$ )A_a_prod_a_prod_llist$ )
(declare-fun ldropn$g (Nat$ A_a_a_prod_prod_llist$ )A_a_a_prod_prod_llist$ )
(declare-fun ldropn$h (Nat$ A_a_llist_a_prod_prod_llist$ )A_a_llist_a_prod_prod_llist$ )
(declare-fun ldropn$i (Nat$ A_a_a_llist_prod_prod_llist$ )A_a_a_llist_prod_prod_llist$ )
(declare-fun lfilter$ (A_bool_fun$ )A_llist_a_llist_fun$ )
(declare-fun lfinite$ (A_llist$ )Bool )
(declare-fun fun_app$a (A_llist_a_llist_prod_bool_fun$ A_llist_a_llist_prod$ )Bool )
(declare-fun fun_app$b (A_llist_a_prod_bool_fun$ A_llist_a_prod$ )Bool )
(declare-fun fun_app$c (A_a_llist_prod_bool_fun$ A_a_llist_prod$ )Bool )
(declare-fun fun_app$d (A_a_prod_bool_fun$ A_a_prod$ )Bool )
(declare-fun fun_app$e (A_bool_fun$ A$ )Bool )
(declare-fun fun_app$f (A_llist_a_llist_fun$ A_llist$ )A_llist$ )
(declare-fun iterates$ (A_a_fun$ A$ )A_llist$ )
(declare-fun lfilter$a (A_llist_bool_fun$ A_llist_llist$ )A_llist_llist$ )
(declare-fun lfilter$b (A_a_prod_bool_fun$ A_a_prod_llist$ )A_a_prod_llist$ )
(declare-fun lfilter$c (A_llist_a_prod_bool_fun$ A_llist_a_prod_llist$ )A_llist_a_prod_llist$ )
(declare-fun lfilter$d (A_a_llist_prod_bool_fun$ A_a_llist_prod_llist$ )A_a_llist_prod_llist$ )
(declare-fun lfilter$e (A_llist_a_llist_prod_bool_fun$ A_llist_a_llist_prod_llist$ )A_llist_a_llist_prod_llist$ )
(declare-fun lfilter$f (A_a_prod_a_prod_bool_fun$ A_a_prod_a_prod_llist$ )A_a_prod_a_prod_llist$ )
(declare-fun lfilter$g (A_a_a_prod_prod_bool_fun$ A_a_a_prod_prod_llist$ )A_a_a_prod_prod_llist$ )
(declare-fun lfilter$h (A_a_llist_a_prod_prod_bool_fun$ A_a_llist_a_prod_prod_llist$ )A_a_llist_a_prod_prod_llist$ )
(declare-fun lfilter$i (A_a_a_llist_prod_prod_bool_fun$ A_a_a_llist_prod_prod_llist$ )A_a_a_llist_prod_prod_llist$ )
(declare-fun lfinite$a (A_llist_llist$ )Bool )
(declare-fun lfinite$b (A_a_prod_llist$ )Bool )
(declare-fun lfinite$c (A_llist_a_prod_llist$ )Bool )
(declare-fun lfinite$d (A_a_llist_prod_llist$ )Bool )
(declare-fun lfinite$e (A_llist_a_llist_prod_llist$ )Bool )
(declare-fun lfinite$f (A_a_prod_a_prod_llist$ )Bool )
(declare-fun lfinite$g (A_a_a_prod_prod_llist$ )Bool )
(declare-fun lfinite$h (A_a_llist_a_prod_prod_llist$ )Bool )
(declare-fun lfinite$i (A_a_a_llist_prod_prod_llist$ )Bool )
(declare-fun lfinite$j (A_llist_a_a_prod_prod_llist$ )Bool )
(declare-fun lfinite$k (A_llist_a_prod_a_prod_llist$ )Bool )
(declare-fun iterates$a (A_llist_a_llist_fun$ A_llist$ )A_llist_llist$ )
(declare-fun iterates$b (A_a_prod_a_a_prod_fun$ A_a_prod$ )A_a_prod_llist$ )
(declare-fun iterates$c (A_llist_a_prod_a_llist_a_prod_fun$ A_llist_a_prod$ )A_llist_a_prod_llist$ )
(declare-fun iterates$d (A_a_llist_prod_a_a_llist_prod_fun$ A_a_llist_prod$ )A_a_llist_prod_llist$ )
(declare-fun iterates$e (A_llist_a_llist_prod_a_llist_a_llist_prod_fun$ A_llist_a_llist_prod$ )A_llist_a_llist_prod_llist$ )
(declare-fun iterates$f (A_a_prod_a_prod_a_a_prod_a_prod_fun$ A_a_prod_a_prod$ )A_a_prod_a_prod_llist$ )
(declare-fun iterates$g (A_a_a_prod_prod_a_a_a_prod_prod_fun$ A_a_a_prod_prod$ )A_a_a_prod_prod_llist$ )
(declare-fun iterates$h (A_a_llist_a_prod_prod_a_a_llist_a_prod_prod_fun$ A_a_llist_a_prod_prod$ )A_a_llist_a_prod_prod_llist$ )
(declare-fun iterates$i (A_a_a_llist_prod_prod_a_a_a_llist_prod_prod_fun$ A_a_a_llist_prod_prod$ )A_a_a_llist_prod_prod_llist$ )
(declare-fun lstrict_prefix$ (A_llist$ )A_llist_bool_fun$ )
(declare-fun lstrict_prefix$a (A_llist_llist$ A_llist_llist$ )Bool )
(declare-fun lstrict_prefix$b (A_a_prod_llist$ A_a_prod_llist$ )Bool )
(declare-fun lstrict_prefix$c (A_llist_a_prod_llist$ A_llist_a_prod_llist$ )Bool )
(declare-fun lstrict_prefix$d (A_a_llist_prod_llist$ A_a_llist_prod_llist$ )Bool )
(declare-fun lstrict_prefix$e (A_llist_a_llist_prod_llist$ A_llist_a_llist_prod_llist$ )Bool )
(declare-fun lstrict_prefix$f (A_a_prod_a_prod_llist$ A_a_prod_a_prod_llist$ )Bool )
(declare-fun lstrict_prefix$g (A_a_a_prod_prod_llist$ A_a_a_prod_prod_llist$ )Bool )
(declare-fun lstrict_prefix$h (A_a_llist_a_prod_prod_llist$ A_a_llist_a_prod_prod_llist$ )Bool )
(declare-fun lstrict_prefix$i (A_a_a_llist_prod_prod_llist$ A_a_a_llist_prod_prod_llist$ )Bool )
(assert (! (forall ((?v0 A_llist$ ))(! (= (fun_app$ uu$ ?v0 )(not (lnull$ ?v0 ))):pattern ((fun_app$ uu$ ?v0 )))):named a0 ))
(assert (! (forall ((?v0 A_llist$ ))(! (= (fun_app$ uuf$ ?v0 )true ):pattern ((fun_app$ uuf$ ?v0 )))):named a1 ))
(assert (! (forall ((?v0 A_llist_a_llist_prod$ ))(! (= (fun_app$a uud$ ?v0 )true ):pattern ((fun_app$a uud$ ?v0 )))):named a2 ))
(assert (! (forall ((?v0 A_llist_a_prod$ ))(! (= (fun_app$b uuc$ ?v0 )true ):pattern ((fun_app$b uuc$ ?v0 )))):named a3 ))
(assert (! (forall ((?v0 A_a_llist_prod$ ))(! (= (fun_app$c uub$ ?v0 )true ):pattern ((fun_app$c uub$ ?v0 )))):named a4 ))
(assert (! (forall ((?v0 A_a_prod$ ))(! (= (fun_app$d uua$ ?v0 )true ):pattern ((fun_app$d uua$ ?v0 )))):named a5 ))
(assert (! (forall ((?v0 A$ ))(! (= (fun_app$e uue$ ?v0 )true ):pattern ((fun_app$e uue$ ?v0 )))):named a6 ))
(assert (! (not (lfinite$ (lconcat$ xss$ ))):named a7 ))
(assert (! (forall ((?v0 A_llist$ ))(=> (member$ ?v0 (lset$ xss$ ))(lfinite$ ?v0 ))):named a8 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_bool_fun$ ))(=> (lfinite$ ?v0 )(lfinite$ (fun_app$f (lfilter$ ?v1 )?v0 )))):named a9 ))
(assert (! (forall ((?v0 A_llist_llist$ )(?v1 A_llist_bool_fun$ ))(=> (lfinite$a ?v0 )(lfinite$a (lfilter$a ?v1 ?v0 )))):named a10 ))
(assert (! (forall ((?v0 A_a_prod_llist$ )(?v1 A_a_prod_bool_fun$ ))(=> (lfinite$b ?v0 )(lfinite$b (lfilter$b ?v1 ?v0 )))):named a11 ))
(assert (! (forall ((?v0 A_llist_a_prod_llist$ )(?v1 A_llist_a_prod_bool_fun$ ))(=> (lfinite$c ?v0 )(lfinite$c (lfilter$c ?v1 ?v0 )))):named a12 ))
(assert (! (forall ((?v0 A_a_llist_prod_llist$ )(?v1 A_a_llist_prod_bool_fun$ ))(=> (lfinite$d ?v0 )(lfinite$d (lfilter$d ?v1 ?v0 )))):named a13 ))
(assert (! (forall ((?v0 A_llist_a_llist_prod_llist$ )(?v1 A_llist_a_llist_prod_bool_fun$ ))(=> (lfinite$e ?v0 )(lfinite$e (lfilter$e ?v1 ?v0 )))):named a14 ))
(assert (! (forall ((?v0 A_a_prod_a_prod_llist$ )(?v1 A_a_prod_a_prod_bool_fun$ ))(=> (lfinite$f ?v0 )(lfinite$f (lfilter$f ?v1 ?v0 )))):named a15 ))
(assert (! (forall ((?v0 A_a_a_prod_prod_llist$ )(?v1 A_a_a_prod_prod_bool_fun$ ))(=> (lfinite$g ?v0 )(lfinite$g (lfilter$g ?v1 ?v0 )))):named a16 ))
(assert (! (forall ((?v0 A_a_llist_a_prod_prod_llist$ )(?v1 A_a_llist_a_prod_prod_bool_fun$ ))(=> (lfinite$h ?v0 )(lfinite$h (lfilter$h ?v1 ?v0 )))):named a17 ))
(assert (! (forall ((?v0 A_a_a_llist_prod_prod_llist$ )(?v1 A_a_a_llist_prod_prod_bool_fun$ ))(=> (lfinite$i ?v0 )(lfinite$i (lfilter$i ?v1 ?v0 )))):named a18 ))
(assert (! (forall ((?v0 A_llist$ ))(=> (lnull$ ?v0 )(lfinite$ ?v0 ))):named a19 ))
(assert (! (forall ((?v0 A_llist_llist$ ))(=> (lnull$a ?v0 )(lfinite$a ?v0 ))):named a20 ))
(assert (! (forall ((?v0 A_a_prod_llist$ ))(=> (lnull$b ?v0 )(lfinite$b ?v0 ))):named a21 ))
(assert (! (forall ((?v0 A_llist_a_prod_llist$ ))(=> (lnull$c ?v0 )(lfinite$c ?v0 ))):named a22 ))
(assert (! (forall ((?v0 A_a_llist_prod_llist$ ))(=> (lnull$d ?v0 )(lfinite$d ?v0 ))):named a23 ))
(assert (! (forall ((?v0 A_llist_a_llist_prod_llist$ ))(=> (lnull$e ?v0 )(lfinite$e ?v0 ))):named a24 ))
(assert (! (forall ((?v0 A_a_prod_a_prod_llist$ ))(=> (lnull$f ?v0 )(lfinite$f ?v0 ))):named a25 ))
(assert (! (forall ((?v0 A_a_a_prod_prod_llist$ ))(=> (lnull$g ?v0 )(lfinite$g ?v0 ))):named a26 ))
(assert (! (forall ((?v0 A_a_llist_a_prod_prod_llist$ ))(=> (lnull$h ?v0 )(lfinite$h ?v0 ))):named a27 ))
(assert (! (forall ((?v0 A_a_a_llist_prod_prod_llist$ ))(=> (lnull$i ?v0 )(lfinite$i ?v0 ))):named a28 ))
(assert (! (forall ((?v0 A_a_prod_bool_fun$ )(?v1 A_a_prod_llist$ ))(= (lfilter$b ?v0 (lfilter$b ?v0 ?v1 ))(lfilter$b ?v0 ?v1 ))):named a29 ))
(assert (! (forall ((?v0 A_a_llist_prod_bool_fun$ )(?v1 A_a_llist_prod_llist$ ))(= (lfilter$d ?v0 (lfilter$d ?v0 ?v1 ))(lfilter$d ?v0 ?v1 ))):named a30 ))
(assert (! (forall ((?v0 A_llist_a_prod_bool_fun$ )(?v1 A_llist_a_prod_llist$ ))(= (lfilter$c ?v0 (lfilter$c ?v0 ?v1 ))(lfilter$c ?v0 ?v1 ))):named a31 ))
(assert (! (forall ((?v0 A_llist_a_llist_prod_bool_fun$ )(?v1 A_llist_a_llist_prod_llist$ ))(= (lfilter$e ?v0 (lfilter$e ?v0 ?v1 ))(lfilter$e ?v0 ?v1 ))):named a32 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A_llist$ ))(= (fun_app$f (lfilter$ ?v0 )(fun_app$f (lfilter$ ?v0 )?v1 ))(fun_app$f (lfilter$ ?v0 )?v1 ))):named a33 ))
(assert (! (forall ((?v0 A_llist_bool_fun$ )(?v1 A_llist_llist$ ))(= (lfilter$a ?v0 (lfilter$a ?v0 ?v1 ))(lfilter$a ?v0 ?v1 ))):named a34 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (fun_app$ (lstrict_prefix$ ?v0 )?v1 )(lfinite$ ?v0 ))):named a35 ))
(assert (! (forall ((?v0 A_llist_llist$ )(?v1 A_llist_llist$ ))(=> (lstrict_prefix$a ?v0 ?v1 )(lfinite$a ?v0 ))):named a36 ))
(assert (! (forall ((?v0 A_a_prod_llist$ )(?v1 A_a_prod_llist$ ))(=> (lstrict_prefix$b ?v0 ?v1 )(lfinite$b ?v0 ))):named a37 ))
(assert (! (forall ((?v0 A_llist_a_prod_llist$ )(?v1 A_llist_a_prod_llist$ ))(=> (lstrict_prefix$c ?v0 ?v1 )(lfinite$c ?v0 ))):named a38 ))
(assert (! (forall ((?v0 A_a_llist_prod_llist$ )(?v1 A_a_llist_prod_llist$ ))(=> (lstrict_prefix$d ?v0 ?v1 )(lfinite$d ?v0 ))):named a39 ))
(assert (! (forall ((?v0 A_llist_a_llist_prod_llist$ )(?v1 A_llist_a_llist_prod_llist$ ))(=> (lstrict_prefix$e ?v0 ?v1 )(lfinite$e ?v0 ))):named a40 ))
(assert (! (forall ((?v0 A_a_prod_a_prod_llist$ )(?v1 A_a_prod_a_prod_llist$ ))(=> (lstrict_prefix$f ?v0 ?v1 )(lfinite$f ?v0 ))):named a41 ))
(assert (! (forall ((?v0 A_a_a_prod_prod_llist$ )(?v1 A_a_a_prod_prod_llist$ ))(=> (lstrict_prefix$g ?v0 ?v1 )(lfinite$g ?v0 ))):named a42 ))
(assert (! (forall ((?v0 A_a_llist_a_prod_prod_llist$ )(?v1 A_a_llist_a_prod_prod_llist$ ))(=> (lstrict_prefix$h ?v0 ?v1 )(lfinite$h ?v0 ))):named a43 ))
(assert (! (forall ((?v0 A_a_a_llist_prod_prod_llist$ )(?v1 A_a_a_llist_prod_prod_llist$ ))(=> (lstrict_prefix$i ?v0 ?v1 )(lfinite$i ?v0 ))):named a44 ))
(assert (! (and (lfinite$a (lfilter$a uu$ xss$ ))(forall ((?v0 A_llist$ ))(=> (member$ ?v0 (lset$ xss$ ))(lfinite$ ?v0 )))):named a45 ))
(assert (! (lfinite$a (lfilter$a uu$ xss$ )):named a46 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_llist$ ))(= (lfinite$ (fun_app$f (ldropn$ ?v0 )?v1 ))(lfinite$ ?v1 ))):named a47 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_llist_llist$ ))(= (lfinite$a (ldropn$a ?v0 ?v1 ))(lfinite$a ?v1 ))):named a48 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_prod_llist$ ))(= (lfinite$b (ldropn$b ?v0 ?v1 ))(lfinite$b ?v1 ))):named a49 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_llist_a_prod_llist$ ))(= (lfinite$c (ldropn$c ?v0 ?v1 ))(lfinite$c ?v1 ))):named a50 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_llist_prod_llist$ ))(= (lfinite$d (ldropn$d ?v0 ?v1 ))(lfinite$d ?v1 ))):named a51 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_llist_a_llist_prod_llist$ ))(= (lfinite$e (ldropn$e ?v0 ?v1 ))(lfinite$e ?v1 ))):named a52 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_prod_a_prod_llist$ ))(= (lfinite$f (ldropn$f ?v0 ?v1 ))(lfinite$f ?v1 ))):named a53 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_a_prod_prod_llist$ ))(= (lfinite$g (ldropn$g ?v0 ?v1 ))(lfinite$g ?v1 ))):named a54 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_llist_a_prod_prod_llist$ ))(= (lfinite$h (ldropn$h ?v0 ?v1 ))(lfinite$h ?v1 ))):named a55 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_a_llist_prod_prod_llist$ ))(= (lfinite$i (ldropn$i ?v0 ?v1 ))(lfinite$i ?v1 ))):named a56 ))
(assert (! (= (lfinite$ lNil$ )true ):named a57 ))
(assert (! (= (lfinite$a lNil$a )true ):named a58 ))
(assert (! (= (lfinite$b lNil$b )true ):named a59 ))
(assert (! (= (lfinite$c lNil$c )true ):named a60 ))
(assert (! (= (lfinite$d lNil$d )true ):named a61 ))
(assert (! (= (lfinite$e lNil$e )true ):named a62 ))
(assert (! (= (lfinite$f lNil$f )true ):named a63 ))
(assert (! (= (lfinite$g lNil$g )true ):named a64 ))
(assert (! (= (lfinite$h lNil$h )true ):named a65 ))
(assert (! (= (lfinite$i lNil$i )true ):named a66 ))
(assert (! (=> (=> (and (lfinite$a (lfilter$a uu$ xss$ ))(forall ((?v0 A_llist$ ))(=> (member$ ?v0 (lset$ xss$ ))(lfinite$ ?v0 ))))false )false ):named a67 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(= (lfinite$b (lzip$ ?v0 ?v1 ))(or (lfinite$ ?v0 )(lfinite$ ?v1 )))):named a68 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist_llist$ ))(= (lfinite$d (lzip$a ?v0 ?v1 ))(or (lfinite$ ?v0 )(lfinite$a ?v1 )))):named a69 ))
(assert (! (forall ((?v0 A_llist_llist$ )(?v1 A_llist$ ))(= (lfinite$c (lzip$b ?v0 ?v1 ))(or (lfinite$a ?v0 )(lfinite$ ?v1 )))):named a70 ))
(assert (! (forall ((?v0 A_llist_llist$ )(?v1 A_llist_llist$ ))(= (lfinite$e (lzip$c ?v0 ?v1 ))(or (lfinite$a ?v0 )(lfinite$a ?v1 )))):named a71 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_a_prod_llist$ ))(= (lfinite$g (lzip$d ?v0 ?v1 ))(or (lfinite$ ?v0 )(lfinite$b ?v1 )))):named a72 ))
(assert (! (forall ((?v0 A_a_prod_llist$ )(?v1 A_llist$ ))(= (lfinite$f (lzip$e ?v0 ?v1 ))(or (lfinite$b ?v0 )(lfinite$ ?v1 )))):named a73 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist_a_prod_llist$ ))(= (lfinite$h (lzip$f ?v0 ?v1 ))(or (lfinite$ ?v0 )(lfinite$c ?v1 )))):named a74 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_a_llist_prod_llist$ ))(= (lfinite$i (lzip$g ?v0 ?v1 ))(or (lfinite$ ?v0 )(lfinite$d ?v1 )))):named a75 ))
(assert (! (forall ((?v0 A_llist_llist$ )(?v1 A_a_prod_llist$ ))(= (lfinite$j (lzip$h ?v0 ?v1 ))(or (lfinite$a ?v0 )(lfinite$b ?v1 )))):named a76 ))
(assert (! (forall ((?v0 A_llist_a_prod_llist$ )(?v1 A_llist$ ))(= (lfinite$k (lzip$i ?v0 ?v1 ))(or (lfinite$c ?v0 )(lfinite$ ?v1 )))):named a77 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A$ ))(not (lfinite$ (iterates$ ?v0 ?v1 )))):named a78 ))
(assert (! (forall ((?v0 A_llist_a_llist_fun$ )(?v1 A_llist$ ))(not (lfinite$a (iterates$a ?v0 ?v1 )))):named a79 ))
(assert (! (forall ((?v0 A_a_prod_a_a_prod_fun$ )(?v1 A_a_prod$ ))(not (lfinite$b (iterates$b ?v0 ?v1 )))):named a80 ))
(assert (! (forall ((?v0 A_llist_a_prod_a_llist_a_prod_fun$ )(?v1 A_llist_a_prod$ ))(not (lfinite$c (iterates$c ?v0 ?v1 )))):named a81 ))
(assert (! (forall ((?v0 A_a_llist_prod_a_a_llist_prod_fun$ )(?v1 A_a_llist_prod$ ))(not (lfinite$d (iterates$d ?v0 ?v1 )))):named a82 ))
(assert (! (forall ((?v0 A_llist_a_llist_prod_a_llist_a_llist_prod_fun$ )(?v1 A_llist_a_llist_prod$ ))(not (lfinite$e (iterates$e ?v0 ?v1 )))):named a83 ))
(assert (! (forall ((?v0 A_a_prod_a_prod_a_a_prod_a_prod_fun$ )(?v1 A_a_prod_a_prod$ ))(not (lfinite$f (iterates$f ?v0 ?v1 )))):named a84 ))
(assert (! (forall ((?v0 A_a_a_prod_prod_a_a_a_prod_prod_fun$ )(?v1 A_a_a_prod_prod$ ))(not (lfinite$g (iterates$g ?v0 ?v1 )))):named a85 ))
(assert (! (forall ((?v0 A_a_llist_a_prod_prod_a_a_llist_a_prod_prod_fun$ )(?v1 A_a_llist_a_prod_prod$ ))(not (lfinite$h (iterates$h ?v0 ?v1 )))):named a86 ))
(assert (! (forall ((?v0 A_a_a_llist_prod_prod_a_a_a_llist_prod_prod_fun$ )(?v1 A_a_a_llist_prod_prod$ ))(not (lfinite$i (iterates$i ?v0 ?v1 )))):named a87 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(! (= (lfinite$ (lCons$ ?v0 ?v1 ))(lfinite$ ?v1 )):pattern ((lCons$ ?v0 ?v1 )))):named a88 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist_llist$ ))(! (= (lfinite$a (lCons$a ?v0 ?v1 ))(lfinite$a ?v1 )):pattern ((lCons$a ?v0 ?v1 )))):named a89 ))
(assert (! (forall ((?v0 A_a_prod$ )(?v1 A_a_prod_llist$ ))(! (= (lfinite$b (lCons$b ?v0 ?v1 ))(lfinite$b ?v1 )):pattern ((lCons$b ?v0 ?v1 )))):named a90 ))
(assert (! (forall ((?v0 A_llist_a_prod$ )(?v1 A_llist_a_prod_llist$ ))(! (= (lfinite$c (lCons$c ?v0 ?v1 ))(lfinite$c ?v1 )):pattern ((lCons$c ?v0 ?v1 )))):named a91 ))
(assert (! (forall ((?v0 A_a_llist_prod$ )(?v1 A_a_llist_prod_llist$ ))(! (= (lfinite$d (lCons$d ?v0 ?v1 ))(lfinite$d ?v1 )):pattern ((lCons$d ?v0 ?v1 )))):named a92 ))
(assert (! (forall ((?v0 A_llist_a_llist_prod$ )(?v1 A_llist_a_llist_prod_llist$ ))(! (= (lfinite$e (lCons$e ?v0 ?v1 ))(lfinite$e ?v1 )):pattern ((lCons$e ?v0 ?v1 )))):named a93 ))
(assert (! (forall ((?v0 A_a_prod_a_prod$ )(?v1 A_a_prod_a_prod_llist$ ))(! (= (lfinite$f (lCons$f ?v0 ?v1 ))(lfinite$f ?v1 )):pattern ((lCons$f ?v0 ?v1 )))):named a94 ))
(assert (! (forall ((?v0 A_a_a_prod_prod$ )(?v1 A_a_a_prod_prod_llist$ ))(! (= (lfinite$g (lCons$g ?v0 ?v1 ))(lfinite$g ?v1 )):pattern ((lCons$g ?v0 ?v1 )))):named a95 ))
(assert (! (forall ((?v0 A_a_llist_a_prod_prod$ )(?v1 A_a_llist_a_prod_prod_llist$ ))(! (= (lfinite$h (lCons$h ?v0 ?v1 ))(lfinite$h ?v1 )):pattern ((lCons$h ?v0 ?v1 )))):named a96 ))
(assert (! (forall ((?v0 A_a_a_llist_prod_prod$ )(?v1 A_a_a_llist_prod_prod_llist$ ))(! (= (lfinite$i (lCons$i ?v0 ?v1 ))(lfinite$i ?v1 )):pattern ((lCons$i ?v0 ?v1 )))):named a97 ))
(assert (! (forall ((?v0 A_a_prod$ )(?v1 A_a_prod_llist$ )(?v2 A_a_prod$ )(?v3 A_a_prod_llist$ ))(= (= (lCons$b ?v0 ?v1 )(lCons$b ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a98 ))
(assert (! (forall ((?v0 A_a_llist_prod$ )(?v1 A_a_llist_prod_llist$ )(?v2 A_a_llist_prod$ )(?v3 A_a_llist_prod_llist$ ))(= (= (lCons$d ?v0 ?v1 )(lCons$d ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a99 ))
(assert (! (forall ((?v0 A_llist_a_prod$ )(?v1 A_llist_a_prod_llist$ )(?v2 A_llist_a_prod$ )(?v3 A_llist_a_prod_llist$ ))(= (= (lCons$c ?v0 ?v1 )(lCons$c ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a100 ))
(assert (! (forall ((?v0 A_llist_a_llist_prod$ )(?v1 A_llist_a_llist_prod_llist$ )(?v2 A_llist_a_llist_prod$ )(?v3 A_llist_a_llist_prod_llist$ ))(= (= (lCons$e ?v0 ?v1 )(lCons$e ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a101 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist_llist$ )(?v2 A_llist$ )(?v3 A_llist_llist$ ))(= (= (lCons$a ?v0 ?v1 )(lCons$a ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a102 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A$ )(?v3 A_llist$ ))(= (= (lCons$ ?v0 ?v1 )(lCons$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a103 ))
(assert (! (forall ((?v0 A_a_prod_llist$ ))(= (lfilter$b uua$ ?v0 )?v0 )):named a104 ))
(assert (! (forall ((?v0 A_a_llist_prod_llist$ ))(= (lfilter$d uub$ ?v0 )?v0 )):named a105 ))
(assert (! (forall ((?v0 A_llist_a_prod_llist$ ))(= (lfilter$c uuc$ ?v0 )?v0 )):named a106 ))
(assert (! (forall ((?v0 A_llist_a_llist_prod_llist$ ))(= (lfilter$e uud$ ?v0 )?v0 )):named a107 ))
(assert (! (forall ((?v0 A_llist$ ))(= (fun_app$f (lfilter$ uue$ )?v0 )?v0 )):named a108 ))
(assert (! (forall ((?v0 A_llist_llist$ ))(= (lfilter$a uuf$ ?v0 )?v0 )):named a109 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(! (= (lfinite$ (lCons$ ?v0 ?v1 ))(lfinite$ ?v1 )):pattern ((lCons$ ?v0 ?v1 )))):named a110 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist_llist$ ))(! (= (lfinite$a (lCons$a ?v0 ?v1 ))(lfinite$a ?v1 )):pattern ((lCons$a ?v0 ?v1 )))):named a111 ))
(assert (! (forall ((?v0 A_a_prod$ )(?v1 A_a_prod_llist$ ))(! (= (lfinite$b (lCons$b ?v0 ?v1 ))(lfinite$b ?v1 )):pattern ((lCons$b ?v0 ?v1 )))):named a112 ))
(assert (! (forall ((?v0 A_llist_a_prod$ )(?v1 A_llist_a_prod_llist$ ))(! (= (lfinite$c (lCons$c ?v0 ?v1 ))(lfinite$c ?v1 )):pattern ((lCons$c ?v0 ?v1 )))):named a113 ))
(assert (! (forall ((?v0 A_a_llist_prod$ )(?v1 A_a_llist_prod_llist$ ))(! (= (lfinite$d (lCons$d ?v0 ?v1 ))(lfinite$d ?v1 )):pattern ((lCons$d ?v0 ?v1 )))):named a114 ))
(assert (! (forall ((?v0 A_llist_a_llist_prod$ )(?v1 A_llist_a_llist_prod_llist$ ))(! (= (lfinite$e (lCons$e ?v0 ?v1 ))(lfinite$e ?v1 )):pattern ((lCons$e ?v0 ?v1 )))):named a115 ))
(assert (! (forall ((?v0 A_a_prod_a_prod$ )(?v1 A_a_prod_a_prod_llist$ ))(! (= (lfinite$f (lCons$f ?v0 ?v1 ))(lfinite$f ?v1 )):pattern ((lCons$f ?v0 ?v1 )))):named a116 ))
(assert (! (forall ((?v0 A_a_a_prod_prod$ )(?v1 A_a_a_prod_prod_llist$ ))(! (= (lfinite$g (lCons$g ?v0 ?v1 ))(lfinite$g ?v1 )):pattern ((lCons$g ?v0 ?v1 )))):named a117 ))
(assert (! (forall ((?v0 A_a_llist_a_prod_prod$ )(?v1 A_a_llist_a_prod_prod_llist$ ))(! (= (lfinite$h (lCons$h ?v0 ?v1 ))(lfinite$h ?v1 )):pattern ((lCons$h ?v0 ?v1 )))):named a118 ))
(assert (! (forall ((?v0 A_a_a_llist_prod_prod$ )(?v1 A_a_a_llist_prod_prod_llist$ ))(! (= (lfinite$i (lCons$i ?v0 ?v1 ))(lfinite$i ?v1 )):pattern ((lCons$i ?v0 ?v1 )))):named a119 ))
(assert (! (forall ((?v0 A_a_llist_prod_bool_fun$ )(?v1 A_a_llist_prod$ )(?v2 A_a_llist_prod_llist$ ))(! (= (lfilter$d ?v0 (lCons$d ?v1 ?v2 ))(ite (fun_app$c ?v0 ?v1 )(lCons$d ?v1 (lfilter$d ?v0 ?v2 ))(lfilter$d ?v0 ?v2 ))):pattern ((lfilter$d ?v0 (lCons$d ?v1 ?v2 ))))):named a120 ))
(assert (! (forall ((?v0 A_llist_a_prod_bool_fun$ )(?v1 A_llist_a_prod$ )(?v2 A_llist_a_prod_llist$ ))(! (= (lfilter$c ?v0 (lCons$c ?v1 ?v2 ))(ite (fun_app$b ?v0 ?v1 )(lCons$c ?v1 (lfilter$c ?v0 ?v2 ))(lfilter$c ?v0 ?v2 ))):pattern ((lfilter$c ?v0 (lCons$c ?v1 ?v2 ))))):named a121 ))
(assert (! (forall ((?v0 A_llist_a_llist_prod_bool_fun$ )(?v1 A_llist_a_llist_prod$ )(?v2 A_llist_a_llist_prod_llist$ ))(! (= (lfilter$e ?v0 (lCons$e ?v1 ?v2 ))(ite (fun_app$a ?v0 ?v1 )(lCons$e ?v1 (lfilter$e ?v0 ?v2 ))(lfilter$e ?v0 ?v2 ))):pattern ((lfilter$e ?v0 (lCons$e ?v1 ?v2 ))))):named a122 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A$ )(?v2 A_llist$ ))(! (= (fun_app$f (lfilter$ ?v0 )(lCons$ ?v1 ?v2 ))(ite (fun_app$e ?v0 ?v1 )(lCons$ ?v1 (fun_app$f (lfilter$ ?v0 )?v2 ))(fun_app$f (lfilter$ ?v0 )?v2 ))):pattern ((fun_app$f (lfilter$ ?v0 )(lCons$ ?v1 ?v2 ))))):named a123 ))
(assert (! (forall ((?v0 A_llist_bool_fun$ )(?v1 A_llist$ )(?v2 A_llist_llist$ ))(! (= (lfilter$a ?v0 (lCons$a ?v1 ?v2 ))(ite (fun_app$ ?v0 ?v1 )(lCons$a ?v1 (lfilter$a ?v0 ?v2 ))(lfilter$a ?v0 ?v2 ))):pattern ((lfilter$a ?v0 (lCons$a ?v1 ?v2 ))))):named a124 ))
(check-sat )
;(get-unsat-core )
