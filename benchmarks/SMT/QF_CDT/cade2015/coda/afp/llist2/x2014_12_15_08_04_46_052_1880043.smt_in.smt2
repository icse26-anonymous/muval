;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort A_llist_set$ 0 )
(declare-sort A_llist_set_set$ 0 )
(declare-sort A_llist_list_set$ 0 )
(declare-sort A_llist_set_set_set$ 0 )
(declare-sort A_llist_list_set_set$ 0 )
(declare-sort A_llist_set_list_set$ 0 )
(declare-sort A_llist_list_list_set$ 0 )
(declare-sort A_llist_a_llist_sum_set$ 0 )
(declare-sort A_llist_set_set_set_set$ 0 )
(declare-sort A_llist_list_set_set_set$ 0 )
(declare-sort A_llist_set_list_set_set$ 0 )
(declare-sort A_llist_set_set_list_set$ 0 )
(declare-sort A_llist_list_list_set_set$ 0 )
(declare-sort A_llist_list_set_list_set$ 0 )
(declare-sort A_llist_set_list_list_set$ 0 )
(declare-sort A_llist_list_list_list_set$ 0 )
(declare-sort A_llist_a_llist_set_sum_set$ 0 )
(declare-sort A_llist_a_llist_sum_set_set$ 0 )
(declare-sort A_llist_set_a_llist_sum_set$ 0 )
(declare-sort A_llist_a_llist_list_sum_set$ 0 )
(declare-sort A_llist_a_llist_sum_list_set$ 0 )
(declare-sort A_llist_list_a_llist_sum_set$ 0 )
(declare-sort A_llist_a_llist_sum_set_set_set$ 0 )
(declare-sort A_llist_set_a_llist_set_sum_set$ 0 )
(declare-sort A_llist_a_llist_sum_set_list_set$ 0 )
(declare-sort A_llist_list_a_llist_set_sum_set$ 0 )
(declare-sort A_llist_set_a_llist_list_sum_set$ 0 )
(declare-sort A_llist_list_a_llist_list_sum_set$ 0 )
(declare-sort A_llist_a_llist_a_llist_sum_sum_set$ 0 )
(declare-codatatypes ()((A_llist$ (lNil$ )(lCons$ (lhd$ A$ )(ltl$ A_llist$ )))))
(declare-sort A_llist_list$ 0)
(declare-sort A_llist_list_list$ 0)
(declare-sort A_llist_set_list$ 0)
(declare-sort A_llist_a_llist_sum$ 0)
(declare-fun nil$ ()A_llist_list$)
(declare-fun hd$ (A_llist_list$)A_llist$)
(declare-fun tl$ (A_llist_list$)A_llist_list$)
(declare-fun cons$ (A_llist$ A_llist_list$ )A_llist_list$)
(declare-fun nil$a ()A_llist_list_list$)
(declare-fun hd$a (A_llist_list_list$)A_llist_list$)
(declare-fun tl$a (A_llist_list_list$)A_llist_list_list$)
(declare-fun cons$a (A_llist_list$ A_llist_list_list$ )A_llist_list_list$)
(declare-fun nil$b ()A_llist_set_list$)
(declare-fun hd$b (A_llist_set_list$)A_llist_set$)
(declare-fun tl$b (A_llist_set_list$)A_llist_set_list$)
(declare-fun cons$b (A_llist_set$ A_llist_set_list$ )A_llist_set_list$)
(declare-fun projl$ (A_llist_a_llist_sum$)A_llist$)
(declare-fun inl$ (A_llist$ )A_llist_a_llist_sum$)
(declare-fun projr$ (A_llist_a_llist_sum$)A_llist$)
(declare-fun inr$ (A_llist$ )A_llist_a_llist_sum$)
(declare-fun s$ ()A_llist$ )
(declare-fun bot$ ()A_llist_list_list_set$ )
(declare-fun pow$ (A_llist_list_list_set$ )A_llist_list_list_set_set$ )
(declare-fun sup$ (A_llist_list_list_set_set$ )A_llist_list_list_set$ )
(declare-fun top$ ()A_llist_set$ )
(declare-fun bot$a ()A_llist_set_list_set$ )
(declare-fun bot$b ()A_llist_a_llist_sum_set_set$ )
(declare-fun bot$c ()A_llist_list_set_set$ )
(declare-fun bot$d ()A_llist_set_set_set$ )
(declare-fun bot$e ()A_llist_set_set$ )
(declare-fun bot$f ()A_llist_list_set$ )
(declare-fun bot$g ()A_llist_a_llist_sum_set$ )
(declare-fun bot$h ()A_llist_set$ )
(declare-fun bot$i ()A_llist_a_llist_list_sum_set$ )
(declare-fun bot$j ()A_llist_a_llist_set_sum_set$ )
(declare-fun bot$k ()A_llist_list_a_llist_sum_set$ )
(declare-fun bot$l ()A_llist_set_a_llist_sum_set$ )
(declare-fun bot$m ()A_llist_list_a_llist_list_sum_set$ )
(declare-fun bot$n ()A_llist_list_a_llist_set_sum_set$ )
(declare-fun bot$o ()A_llist_set_a_llist_list_sum_set$ )
(declare-fun bot$p ()A_llist_set_a_llist_set_sum_set$ )
(declare-fun bot$q ()A_llist_a_llist_a_llist_sum_sum_set$ )
(declare-fun plus$ (A_llist_set$ A_llist_set$ )A_llist_a_llist_sum_set$ )
(declare-fun pow$a (A_llist_set_list_set$ )A_llist_set_list_set_set$ )
(declare-fun pow$b (A_llist_a_llist_sum_set_set$ )A_llist_a_llist_sum_set_set_set$ )
(declare-fun pow$c (A_llist_list_set_set$ )A_llist_list_set_set_set$ )
(declare-fun pow$d (A_llist_set_set_set$ )A_llist_set_set_set_set$ )
(declare-fun pow$e (A_llist_set_set$ )A_llist_set_set_set$ )
(declare-fun pow$f (A_llist_list_set$ )A_llist_list_set_set$ )
(declare-fun pow$g (A_llist_a_llist_sum_set$ )A_llist_a_llist_sum_set_set$ )
(declare-fun pow$h (A_llist_set$ )A_llist_set_set$ )
(declare-fun sup$a (A_llist_set_list_set_set$ )A_llist_set_list_set$ )
(declare-fun sup$b (A_llist_a_llist_sum_set_set_set$ )A_llist_a_llist_sum_set_set$ )
(declare-fun sup$c (A_llist_list_set_set_set$ )A_llist_list_set_set$ )
(declare-fun sup$d (A_llist_set_set_set_set$ )A_llist_set_set_set$ )
(declare-fun sup$e (A_llist_set_set_set$ )A_llist_set_set$ )
(declare-fun sup$f (A_llist_list_set_set$ )A_llist_list_set$ )
(declare-fun sup$g (A_llist_a_llist_sum_set_set$ )A_llist_a_llist_sum_set$ )
(declare-fun sup$h (A_llist_set_set$ )A_llist_set$ )
(declare-fun top$a ()A_llist_list_list_set$ )
(declare-fun top$b ()A_llist_set_list_set$ )
(declare-fun top$c ()A_llist_a_llist_sum_set_set$ )
(declare-fun top$d ()A_llist_list_set_set$ )
(declare-fun top$e ()A_llist_set_set_set$ )
(declare-fun top$f ()A_llist_set_set$ )
(declare-fun top$g ()A_llist_list_set$ )
(declare-fun top$h ()A_llist_a_llist_sum_set$ )
(declare-fun top$i ()A_llist_list_list_set_set$ )
(declare-fun top$j ()A_llist_set_list_set_set$ )
(declare-fun top$k ()A_llist_a_llist_sum_set_set_set$ )
(declare-fun top$l ()A_llist_list_set_set_set$ )
(declare-fun top$m ()A_llist_set_set_set_set$ )
(declare-fun top$n ()A_llist_list_list_list_set$ )
(declare-fun top$o ()A_llist_set_list_list_set$ )
(declare-fun top$p ()A_llist_a_llist_sum_set_list_set$ )
(declare-fun top$q ()A_llist_list_set_list_set$ )
(declare-fun top$r ()A_llist_set_set_list_set$ )
(declare-fun top$s ()A_llist_a_llist_sum_list_set$ )
(declare-fun top$t ()A_llist_a_llist_set_sum_set$ )
(declare-fun top$u ()A_llist_a_llist_list_sum_set$ )
(declare-fun top$v ()A_llist_set_a_llist_sum_set$ )
(declare-fun top$w ()A_llist_list_a_llist_sum_set$ )
(declare-fun top$x ()A_llist_set_a_llist_set_sum_set$ )
(declare-fun top$y ()A_llist_set_a_llist_list_sum_set$ )
(declare-fun top$z ()A_llist_list_a_llist_set_sum_set$ )
(declare-fun lists$ (A_llist_list_list_set$ )A_llist_list_list_list_set$ )
(declare-fun plus$a (A_llist_set$ A_llist_set_set$ )A_llist_a_llist_set_sum_set$ )
(declare-fun plus$b (A_llist_set$ A_llist_list_set$ )A_llist_a_llist_list_sum_set$ )
(declare-fun plus$c (A_llist_set_set$ A_llist_set$ )A_llist_set_a_llist_sum_set$ )
(declare-fun plus$d (A_llist_list_set$ A_llist_set$ )A_llist_list_a_llist_sum_set$ )
(declare-fun plus$e (A_llist_set_set$ A_llist_set_set$ )A_llist_set_a_llist_set_sum_set$ )
(declare-fun plus$f (A_llist_set_set$ A_llist_list_set$ )A_llist_set_a_llist_list_sum_set$ )
(declare-fun plus$g (A_llist_list_set$ A_llist_set_set$ )A_llist_list_a_llist_set_sum_set$ )
(declare-fun plus$h (A_llist_list_set$ A_llist_list_set$ )A_llist_list_a_llist_list_sum_set$ )
(declare-fun plus$i (A_llist_set$ A_llist_a_llist_sum_set$ )A_llist_a_llist_a_llist_sum_sum_set$ )
(declare-fun top$aa ()A_llist_list_a_llist_list_sum_set$ )
(declare-fun top$ab ()A_llist_a_llist_a_llist_sum_sum_set$ )
(declare-fun atMost$ (A_llist_list_list_set$ )A_llist_list_list_set_set$ )
(declare-fun lists$a (A_llist_set_list_set$ )A_llist_set_list_list_set$ )
(declare-fun lists$b (A_llist_a_llist_sum_set_set$ )A_llist_a_llist_sum_set_list_set$ )
(declare-fun lists$c (A_llist_list_set_set$ )A_llist_list_set_list_set$ )
(declare-fun lists$d (A_llist_set_set_set$ )A_llist_set_set_list_set$ )
(declare-fun lists$e (A_llist_set_set$ )A_llist_set_list_set$ )
(declare-fun lists$f (A_llist_list_set$ )A_llist_list_list_set$ )
(declare-fun lists$g (A_llist_a_llist_sum_set$ )A_llist_a_llist_sum_list_set$ )
(declare-fun lists$h (A_llist_set$ )A_llist_list_set$ )
(declare-fun member$ (A_llist$ A_llist_set$ )Bool )
(declare-fun atMost$a (A_llist_set_list_set$ )A_llist_set_list_set_set$ )
(declare-fun atMost$b (A_llist_a_llist_sum_set_set$ )A_llist_a_llist_sum_set_set_set$ )
(declare-fun atMost$c (A_llist_list_set_set$ )A_llist_list_set_set_set$ )
(declare-fun atMost$d (A_llist_set_set_set$ )A_llist_set_set_set_set$ )
(declare-fun atMost$e (A_llist_set_set$ )A_llist_set_set_set$ )
(declare-fun atMost$f (A_llist_list_set$ )A_llist_list_set_set$ )
(declare-fun atMost$g (A_llist_a_llist_sum_set$ )A_llist_a_llist_sum_set_set$ )
(declare-fun atMost$h (A_llist_set$ )A_llist_set_set$ )
(declare-fun member$a (A_llist_list_list$ A_llist_list_list_set$ )Bool )
(declare-fun member$b (A_llist_set_list$ A_llist_set_list_set$ )Bool )
(declare-fun member$c (A_llist_a_llist_sum_set$ A_llist_a_llist_sum_set_set$ )Bool )
(declare-fun member$d (A_llist_list_set$ A_llist_list_set_set$ )Bool )
(declare-fun member$e (A_llist_set_set$ A_llist_set_set_set$ )Bool )
(declare-fun member$f (A_llist_set$ A_llist_set_set$ )Bool )
(declare-fun member$g (A_llist_list$ A_llist_list_set$ )Bool )
(declare-fun member$h (A_llist_a_llist_sum$ A_llist_a_llist_sum_set$ )Bool )
(declare-fun atLeastAtMost$ (A_llist_list_list_set$ A_llist_list_list_set$ )A_llist_list_list_set_set$ )
(declare-fun atLeastAtMost$a (A_llist_set_list_set$ A_llist_set_list_set$ )A_llist_set_list_set_set$ )
(declare-fun atLeastAtMost$b (A_llist_a_llist_sum_set_set$ A_llist_a_llist_sum_set_set$ )A_llist_a_llist_sum_set_set_set$ )
(declare-fun atLeastAtMost$c (A_llist_list_set_set$ A_llist_list_set_set$ )A_llist_list_set_set_set$ )
(declare-fun atLeastAtMost$d (A_llist_set_set_set$ A_llist_set_set_set$ )A_llist_set_set_set_set$ )
(declare-fun atLeastAtMost$e (A_llist_set_set$ A_llist_set_set$ )A_llist_set_set_set$ )
(declare-fun atLeastAtMost$f (A_llist_list_set$ A_llist_list_set$ )A_llist_list_set_set$ )
(declare-fun atLeastAtMost$g (A_llist_a_llist_sum_set$ A_llist_a_llist_sum_set$ )A_llist_a_llist_sum_set_set$ )
(declare-fun atLeastAtMost$h (A_llist_set$ A_llist_set$ )A_llist_set_set$ )
(assert (! (not (member$ s$ top$ )):named a0 ))
(assert (! (forall ((?v0 A_llist_list_list$ ))(= (member$a ?v0 top$a )true )):named a1 ))
(assert (! (forall ((?v0 A_llist_set_list$ ))(= (member$b ?v0 top$b )true )):named a2 ))
(assert (! (forall ((?v0 A_llist_a_llist_sum_set$ ))(= (member$c ?v0 top$c )true )):named a3 ))
(assert (! (forall ((?v0 A_llist_list_set$ ))(= (member$d ?v0 top$d )true )):named a4 ))
(assert (! (forall ((?v0 A_llist_set_set$ ))(= (member$e ?v0 top$e )true )):named a5 ))
(assert (! (forall ((?v0 A_llist_set$ ))(= (member$f ?v0 top$f )true )):named a6 ))
(assert (! (forall ((?v0 A_llist_list$ ))(= (member$g ?v0 top$g )true )):named a7 ))
(assert (! (forall ((?v0 A_llist_a_llist_sum$ ))(= (member$h ?v0 top$h )true )):named a8 ))
(assert (! (forall ((?v0 A_llist$ ))(= (member$ ?v0 top$ )true )):named a9 ))
(assert (! (forall ((?v0 A_llist_list_list$ ))(member$a ?v0 top$a )):named a10 ))
(assert (! (forall ((?v0 A_llist_set_list$ ))(member$b ?v0 top$b )):named a11 ))
(assert (! (forall ((?v0 A_llist_a_llist_sum_set$ ))(member$c ?v0 top$c )):named a12 ))
(assert (! (forall ((?v0 A_llist_list_set$ ))(member$d ?v0 top$d )):named a13 ))
(assert (! (forall ((?v0 A_llist_set_set$ ))(member$e ?v0 top$e )):named a14 ))
(assert (! (forall ((?v0 A_llist_set$ ))(member$f ?v0 top$f )):named a15 ))
(assert (! (forall ((?v0 A_llist_list$ ))(member$g ?v0 top$g )):named a16 ))
(assert (! (forall ((?v0 A_llist_a_llist_sum$ ))(member$h ?v0 top$h )):named a17 ))
(assert (! (forall ((?v0 A_llist$ ))(member$ ?v0 top$ )):named a18 ))
(assert (! (forall ((?v0 A_llist_list_list_set$ ))(=> (forall ((?v1 A_llist_list_list$ ))(member$a ?v1 ?v0 ))(= top$a ?v0 ))):named a19 ))
(assert (! (forall ((?v0 A_llist_set_list_set$ ))(=> (forall ((?v1 A_llist_set_list$ ))(member$b ?v1 ?v0 ))(= top$b ?v0 ))):named a20 ))
(assert (! (forall ((?v0 A_llist_a_llist_sum_set_set$ ))(=> (forall ((?v1 A_llist_a_llist_sum_set$ ))(member$c ?v1 ?v0 ))(= top$c ?v0 ))):named a21 ))
(assert (! (forall ((?v0 A_llist_list_set_set$ ))(=> (forall ((?v1 A_llist_list_set$ ))(member$d ?v1 ?v0 ))(= top$d ?v0 ))):named a22 ))
(assert (! (forall ((?v0 A_llist_set_set_set$ ))(=> (forall ((?v1 A_llist_set_set$ ))(member$e ?v1 ?v0 ))(= top$e ?v0 ))):named a23 ))
(assert (! (forall ((?v0 A_llist_set_set$ ))(=> (forall ((?v1 A_llist_set$ ))(member$f ?v1 ?v0 ))(= top$f ?v0 ))):named a24 ))
(assert (! (forall ((?v0 A_llist_list_set$ ))(=> (forall ((?v1 A_llist_list$ ))(member$g ?v1 ?v0 ))(= top$g ?v0 ))):named a25 ))
(assert (! (forall ((?v0 A_llist_a_llist_sum_set$ ))(=> (forall ((?v1 A_llist_a_llist_sum$ ))(member$h ?v1 ?v0 ))(= top$h ?v0 ))):named a26 ))
(assert (! (forall ((?v0 A_llist_set$ ))(=> (forall ((?v1 A_llist$ ))(member$ ?v1 ?v0 ))(= top$ ?v0 ))):named a27 ))
(assert (! (exists ((?v0 A_llist_list_list$ ))(member$a ?v0 top$a )):named a28 ))
(assert (! (exists ((?v0 A_llist_set_list$ ))(member$b ?v0 top$b )):named a29 ))
(assert (! (exists ((?v0 A_llist_a_llist_sum_set$ ))(member$c ?v0 top$c )):named a30 ))
(assert (! (exists ((?v0 A_llist_list_set$ ))(member$d ?v0 top$d )):named a31 ))
(assert (! (exists ((?v0 A_llist_set_set$ ))(member$e ?v0 top$e )):named a32 ))
(assert (! (exists ((?v0 A_llist_set$ ))(member$f ?v0 top$f )):named a33 ))
(assert (! (exists ((?v0 A_llist_list$ ))(member$g ?v0 top$g )):named a34 ))
(assert (! (exists ((?v0 A_llist_a_llist_sum$ ))(member$h ?v0 top$h )):named a35 ))
(assert (! (exists ((?v0 A_llist$ ))(member$ ?v0 top$ )):named a36 ))
(assert (! (forall ((?v0 A_llist_list_list_set$ ))(= (= (atMost$ ?v0 )top$i )(= ?v0 top$a ))):named a37 ))
(assert (! (forall ((?v0 A_llist_set_list_set$ ))(= (= (atMost$a ?v0 )top$j )(= ?v0 top$b ))):named a38 ))
(assert (! (forall ((?v0 A_llist_a_llist_sum_set_set$ ))(= (= (atMost$b ?v0 )top$k )(= ?v0 top$c ))):named a39 ))
(assert (! (forall ((?v0 A_llist_list_set_set$ ))(= (= (atMost$c ?v0 )top$l )(= ?v0 top$d ))):named a40 ))
(assert (! (forall ((?v0 A_llist_set_set_set$ ))(= (= (atMost$d ?v0 )top$m )(= ?v0 top$e ))):named a41 ))
(assert (! (forall ((?v0 A_llist_set_set$ ))(= (= (atMost$e ?v0 )top$e )(= ?v0 top$f ))):named a42 ))
(assert (! (forall ((?v0 A_llist_list_set$ ))(= (= (atMost$f ?v0 )top$d )(= ?v0 top$g ))):named a43 ))
(assert (! (forall ((?v0 A_llist_a_llist_sum_set$ ))(= (= (atMost$g ?v0 )top$c )(= ?v0 top$h ))):named a44 ))
(assert (! (forall ((?v0 A_llist_set$ ))(= (= (atMost$h ?v0 )top$f )(= ?v0 top$ ))):named a45 ))
(assert (! (= (sup$ top$i )top$a ):named a46 ))
(assert (! (= (sup$a top$j )top$b ):named a47 ))
(assert (! (= (sup$b top$k )top$c ):named a48 ))
(assert (! (= (sup$c top$l )top$d ):named a49 ))
(assert (! (= (sup$d top$m )top$e ):named a50 ))
(assert (! (= (sup$e top$e )top$f ):named a51 ))
(assert (! (= (sup$f top$d )top$g ):named a52 ))
(assert (! (= (sup$g top$c )top$h ):named a53 ))
(assert (! (= (sup$h top$f )top$ ):named a54 ))
(assert (! (= (lists$ top$a )top$n ):named a55 ))
(assert (! (= (lists$a top$b )top$o ):named a56 ))
(assert (! (= (lists$b top$c )top$p ):named a57 ))
(assert (! (= (lists$c top$d )top$q ):named a58 ))
(assert (! (= (lists$d top$e )top$r ):named a59 ))
(assert (! (= (lists$e top$f )top$b ):named a60 ))
(assert (! (= (lists$f top$g )top$a ):named a61 ))
(assert (! (= (lists$g top$h )top$s ):named a62 ))
(assert (! (= (lists$h top$ )top$g ):named a63 ))
(assert (! (= (pow$ top$a )top$i ):named a64 ))
(assert (! (= (pow$a top$b )top$j ):named a65 ))
(assert (! (= (pow$b top$c )top$k ):named a66 ))
(assert (! (= (pow$c top$d )top$l ):named a67 ))
(assert (! (= (pow$d top$e )top$m ):named a68 ))
(assert (! (= (pow$e top$f )top$e ):named a69 ))
(assert (! (= (pow$f top$g )top$d ):named a70 ))
(assert (! (= (pow$g top$h )top$c ):named a71 ))
(assert (! (= (pow$h top$ )top$f ):named a72 ))
(assert (! (forall ((?v0 A_llist_list_list_set$ )(?v1 A_llist_list_list_set$ ))(= (= (atLeastAtMost$ ?v0 ?v1 )top$i )(and (= ?v0 bot$ )(= ?v1 top$a )))):named a73 ))
(assert (! (forall ((?v0 A_llist_set_list_set$ )(?v1 A_llist_set_list_set$ ))(= (= (atLeastAtMost$a ?v0 ?v1 )top$j )(and (= ?v0 bot$a )(= ?v1 top$b )))):named a74 ))
(assert (! (forall ((?v0 A_llist_a_llist_sum_set_set$ )(?v1 A_llist_a_llist_sum_set_set$ ))(= (= (atLeastAtMost$b ?v0 ?v1 )top$k )(and (= ?v0 bot$b )(= ?v1 top$c )))):named a75 ))
(assert (! (forall ((?v0 A_llist_list_set_set$ )(?v1 A_llist_list_set_set$ ))(= (= (atLeastAtMost$c ?v0 ?v1 )top$l )(and (= ?v0 bot$c )(= ?v1 top$d )))):named a76 ))
(assert (! (forall ((?v0 A_llist_set_set_set$ )(?v1 A_llist_set_set_set$ ))(= (= (atLeastAtMost$d ?v0 ?v1 )top$m )(and (= ?v0 bot$d )(= ?v1 top$e )))):named a77 ))
(assert (! (forall ((?v0 A_llist_set_set$ )(?v1 A_llist_set_set$ ))(= (= (atLeastAtMost$e ?v0 ?v1 )top$e )(and (= ?v0 bot$e )(= ?v1 top$f )))):named a78 ))
(assert (! (forall ((?v0 A_llist_list_set$ )(?v1 A_llist_list_set$ ))(= (= (atLeastAtMost$f ?v0 ?v1 )top$d )(and (= ?v0 bot$f )(= ?v1 top$g )))):named a79 ))
(assert (! (forall ((?v0 A_llist_a_llist_sum_set$ )(?v1 A_llist_a_llist_sum_set$ ))(= (= (atLeastAtMost$g ?v0 ?v1 )top$c )(and (= ?v0 bot$g )(= ?v1 top$h )))):named a80 ))
(assert (! (forall ((?v0 A_llist_set$ )(?v1 A_llist_set$ ))(= (= (atLeastAtMost$h ?v0 ?v1 )top$f )(and (= ?v0 bot$h )(= ?v1 top$ )))):named a81 ))
(assert (! (= (plus$ top$ top$ )top$h ):named a82 ))
(assert (! (= (plus$a top$ top$f )top$t ):named a83 ))
(assert (! (= (plus$b top$ top$g )top$u ):named a84 ))
(assert (! (= (plus$c top$f top$ )top$v ):named a85 ))
(assert (! (= (plus$d top$g top$ )top$w ):named a86 ))
(assert (! (= (plus$e top$f top$f )top$x ):named a87 ))
(assert (! (= (plus$f top$f top$g )top$y ):named a88 ))
(assert (! (= (plus$g top$g top$f )top$z ):named a89 ))
(assert (! (= (plus$h top$g top$g )top$aa ):named a90 ))
(assert (! (= (plus$i top$ top$h )top$ab ):named a91 ))
(assert (! (forall ((?v0 A_llist_set$ )(?v1 A_llist_set$ ))(= (= (plus$ ?v0 ?v1 )bot$g )(and (= ?v0 bot$h )(= ?v1 bot$h )))):named a92 ))
(assert (! (forall ((?v0 A_llist_set$ )(?v1 A_llist_list_set$ ))(= (= (plus$b ?v0 ?v1 )bot$i )(and (= ?v0 bot$h )(= ?v1 bot$f )))):named a93 ))
(assert (! (forall ((?v0 A_llist_set$ )(?v1 A_llist_set_set$ ))(= (= (plus$a ?v0 ?v1 )bot$j )(and (= ?v0 bot$h )(= ?v1 bot$e )))):named a94 ))
(assert (! (forall ((?v0 A_llist_list_set$ )(?v1 A_llist_set$ ))(= (= (plus$d ?v0 ?v1 )bot$k )(and (= ?v0 bot$f )(= ?v1 bot$h )))):named a95 ))
(assert (! (forall ((?v0 A_llist_set_set$ )(?v1 A_llist_set$ ))(= (= (plus$c ?v0 ?v1 )bot$l )(and (= ?v0 bot$e )(= ?v1 bot$h )))):named a96 ))
(assert (! (forall ((?v0 A_llist_list_set$ )(?v1 A_llist_list_set$ ))(= (= (plus$h ?v0 ?v1 )bot$m )(and (= ?v0 bot$f )(= ?v1 bot$f )))):named a97 ))
(assert (! (forall ((?v0 A_llist_list_set$ )(?v1 A_llist_set_set$ ))(= (= (plus$g ?v0 ?v1 )bot$n )(and (= ?v0 bot$f )(= ?v1 bot$e )))):named a98 ))
(assert (! (forall ((?v0 A_llist_set_set$ )(?v1 A_llist_list_set$ ))(= (= (plus$f ?v0 ?v1 )bot$o )(and (= ?v0 bot$e )(= ?v1 bot$f )))):named a99 ))
(assert (! (forall ((?v0 A_llist_set_set$ )(?v1 A_llist_set_set$ ))(= (= (plus$e ?v0 ?v1 )bot$p )(and (= ?v0 bot$e )(= ?v1 bot$e )))):named a100 ))
(assert (! (forall ((?v0 A_llist_set$ )(?v1 A_llist_a_llist_sum_set$ ))(= (= (plus$i ?v0 ?v1 )bot$q )(and (= ?v0 bot$h )(= ?v1 bot$g )))):named a101 ))
(assert (! (forall ((?v0 A_llist_a_llist_sum_set$ ))(= (sup$g (pow$g ?v0 ))?v0 )):named a102 ))
(assert (! (forall ((?v0 A_llist_list_set$ ))(= (sup$f (pow$f ?v0 ))?v0 )):named a103 ))
(assert (! (forall ((?v0 A_llist_set_set$ ))(= (sup$e (pow$e ?v0 ))?v0 )):named a104 ))
(assert (! (forall ((?v0 A_llist_set$ ))(= (sup$h (pow$h ?v0 ))?v0 )):named a105 ))
(assert (! (forall ((?v0 A_llist_a_llist_sum_set_set$ ))(= (= bot$g (sup$g ?v0 ))(forall ((?v1 A_llist_a_llist_sum_set$ ))(=> (member$c ?v1 ?v0 )(= ?v1 bot$g ))))):named a106 ))
(assert (! (forall ((?v0 A_llist_list_set_set$ ))(= (= bot$f (sup$f ?v0 ))(forall ((?v1 A_llist_list_set$ ))(=> (member$d ?v1 ?v0 )(= ?v1 bot$f ))))):named a107 ))
(assert (! (forall ((?v0 A_llist_set_set_set$ ))(= (= bot$e (sup$e ?v0 ))(forall ((?v1 A_llist_set_set$ ))(=> (member$e ?v1 ?v0 )(= ?v1 bot$e ))))):named a108 ))
(assert (! (forall ((?v0 A_llist_set_set$ ))(= (= bot$h (sup$h ?v0 ))(forall ((?v1 A_llist_set$ ))(=> (member$f ?v1 ?v0 )(= ?v1 bot$h ))))):named a109 ))
(check-sat )
;(get-unsat-core )
