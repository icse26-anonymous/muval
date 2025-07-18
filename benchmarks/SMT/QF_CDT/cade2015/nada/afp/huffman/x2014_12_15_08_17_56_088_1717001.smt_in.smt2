;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_set$ 0 )
(declare-sort A_set_set$ 0 )
(declare-sort A_a_sum_set$ 0 )
(declare-sort A_set_set_set$ 0 )
(declare-sort A_a_set_sum_set$ 0 )
(declare-sort A_a_sum_set_set$ 0 )
(declare-sort A_set_a_sum_set$ 0 )
(declare-sort A_a_a_sum_sum_set$ 0 )
(declare-sort A_a_sum_a_sum_set$ 0 )
(declare-sort A_set_set_set_set$ 0 )
(declare-sort A_a_set_set_sum_set$ 0 )
(declare-sort A_a_set_sum_set_set$ 0 )
(declare-sort A_a_sum_set_set_set$ 0 )
(declare-sort A_set_a_set_sum_set$ 0 )
(declare-sort A_set_a_sum_set_set$ 0 )
(declare-sort A_a_a_sum_sum_set_set$ 0 )
(declare-sort A_a_sum_a_set_sum_set$ 0 )
(declare-sort A_set_a_a_sum_sum_set$ 0 )
(declare-sort A_a_sum_a_a_sum_sum_set$ 0 )
(declare-sort A_tree$ 0)
(declare-sort A_a_sum$ 0)
(declare-sort A_a_sum_tree$ 0)
(declare-sort A_set_tree$ 0)
(declare-fun select$ (A_tree$)Nat$)
(declare-fun selecta$ (A_tree$)A$)
(declare-fun leaf$ (Nat$ A$ )A_tree$)
(declare-fun selectb$ (A_tree$)Nat$)
(declare-fun selectc$ (A_tree$)A_tree$)
(declare-fun selectd$ (A_tree$)A_tree$)
(declare-fun innerNode$ (Nat$ A_tree$ A_tree$ )A_tree$)
(declare-fun projl$ (A_a_sum$)A$)
(declare-fun inl$ (A$ )A_a_sum$)
(declare-fun projr$ (A_a_sum$)A$)
(declare-fun inr$ (A$ )A_a_sum$)
(declare-fun selecte$ (A_a_sum_tree$)Nat$)
(declare-fun selectf$ (A_a_sum_tree$)A_a_sum$)
(declare-fun leaf$a (Nat$ A_a_sum$ )A_a_sum_tree$)
(declare-fun selectg$ (A_a_sum_tree$)Nat$)
(declare-fun selecth$ (A_a_sum_tree$)A_a_sum_tree$)
(declare-fun selecti$ (A_a_sum_tree$)A_a_sum_tree$)
(declare-fun innerNode$a (Nat$ A_a_sum_tree$ A_a_sum_tree$ )A_a_sum_tree$)
(declare-fun selectj$ (A_set_tree$)Nat$)
(declare-fun selectk$ (A_set_tree$)A_set$)
(declare-fun leaf$b (Nat$ A_set$ )A_set_tree$)
(declare-fun selectl$ (A_set_tree$)Nat$)
(declare-fun selectm$ (A_set_tree$)A_set_tree$)
(declare-fun selectn$ (A_set_tree$)A_set_tree$)
(declare-fun innerNode$b (Nat$ A_set_tree$ A_set_tree$ )A_set_tree$)
(declare-fun t$ ()A_tree$ )
(declare-fun inf$ (A_set_a_sum_set$ A_set_a_sum_set$ )A_set_a_sum_set$ )
(declare-fun pow$ (A_set_a_sum_set$ )A_set_a_sum_set_set$ )
(declare-fun sup$ (A_a_sum_set$ A_a_sum_set$ )A_a_sum_set$ )
(declare-fun inf$a (A_a_a_sum_sum_set$ A_a_a_sum_sum_set$ )A_a_a_sum_sum_set$ )
(declare-fun inf$b (A_a_set_sum_set$ A_a_set_sum_set$ )A_a_set_sum_set$ )
(declare-fun inf$c (A_a_sum_set_set$ A_a_sum_set_set$ )A_a_sum_set_set$ )
(declare-fun inf$d (A_set_set_set$ A_set_set_set$ )A_set_set_set$ )
(declare-fun inf$e (A_set_set$ A_set_set$ )A_set_set$ )
(declare-fun inf$f (A_a_sum_set$ A_a_sum_set$ )A_a_sum_set$ )
(declare-fun inf$g (A_set$ A_set$ )A_set$ )
(declare-fun plus$ (A_set$ A_set$ )A_a_sum_set$ )
(declare-fun pow$a (A_a_a_sum_sum_set$ )A_a_a_sum_sum_set_set$ )
(declare-fun pow$b (A_a_set_sum_set$ )A_a_set_sum_set_set$ )
(declare-fun pow$c (A_a_sum_set_set$ )A_a_sum_set_set_set$ )
(declare-fun pow$d (A_set_set_set$ )A_set_set_set_set$ )
(declare-fun pow$e (A_set_set$ )A_set_set_set$ )
(declare-fun pow$f (A_a_sum_set$ )A_a_sum_set_set$ )
(declare-fun pow$g (A_set$ )A_set_set$ )
(declare-fun sup$a (A_set_set$ A_set_set$ )A_set_set$ )
(declare-fun sup$b (A_set$ A_set$ )A_set$ )
(declare-fun sup$c (A_set_a_sum_set$ A_set_a_sum_set$ )A_set_a_sum_set$ )
(declare-fun sup$d (A_a_a_sum_sum_set$ A_a_a_sum_sum_set$ )A_a_a_sum_sum_set$ )
(declare-fun sup$e (A_a_set_sum_set$ A_a_set_sum_set$ )A_a_set_sum_set$ )
(declare-fun sup$f (A_a_sum_set_set$ A_a_sum_set_set$ )A_a_sum_set_set$ )
(declare-fun sup$g (A_set_set_set$ A_set_set_set$ )A_set_set_set$ )
(declare-fun minus$ (A_set_a_sum_set$ A_set_a_sum_set$ )A_set_a_sum_set$ )
(declare-fun plus$a (A_set$ A_set_set$ )A_a_set_sum_set$ )
(declare-fun plus$b (A_set_set$ A_set$ )A_set_a_sum_set$ )
(declare-fun plus$c (A_set$ A_a_sum_set$ )A_a_a_sum_sum_set$ )
(declare-fun plus$d (A_set_set$ A_set_set$ )A_set_a_set_sum_set$ )
(declare-fun plus$e (A_a_sum_set$ A_set$ )A_a_sum_a_sum_set$ )
(declare-fun plus$f (A_set_set$ A_a_sum_set$ )A_set_a_a_sum_sum_set$ )
(declare-fun plus$g (A_a_sum_set$ A_set_set$ )A_a_sum_a_set_sum_set$ )
(declare-fun plus$h (A_a_sum_set$ A_a_sum_set$ )A_a_sum_a_a_sum_sum_set$ )
(declare-fun plus$i (A_set$ A_set_set_set$ )A_a_set_set_sum_set$ )
(declare-fun finite$ (A_set$ )Bool )
(declare-fun minus$a (A_a_a_sum_sum_set$ A_a_a_sum_sum_set$ )A_a_a_sum_sum_set$ )
(declare-fun minus$b (A_a_set_sum_set$ A_a_set_sum_set$ )A_a_set_sum_set$ )
(declare-fun minus$c (A_a_sum_set_set$ A_a_sum_set_set$ )A_a_sum_set_set$ )
(declare-fun minus$d (A_set_set_set$ A_set_set_set$ )A_set_set_set$ )
(declare-fun minus$e (A_set_set$ A_set_set$ )A_set_set$ )
(declare-fun minus$f (A_a_sum_set$ A_a_sum_set$ )A_a_sum_set$ )
(declare-fun minus$g (A_set$ A_set$ )A_set$ )
(declare-fun finite$a (A_set_a_sum_set_set$ )Bool )
(declare-fun finite$b (A_set_a_sum_set$ )Bool )
(declare-fun finite$c (A_a_a_sum_sum_set_set$ )Bool )
(declare-fun finite$d (A_a_a_sum_sum_set$ )Bool )
(declare-fun finite$e (A_a_set_sum_set_set$ )Bool )
(declare-fun finite$f (A_a_set_sum_set$ )Bool )
(declare-fun finite$g (A_a_sum_set_set_set$ )Bool )
(declare-fun finite$h (A_a_sum_set_set$ )Bool )
(declare-fun finite$i (A_set_set_set_set$ )Bool )
(declare-fun finite$j (A_set_set_set$ )Bool )
(declare-fun finite$k (A_set_set$ )Bool )
(declare-fun finite$l (A_a_sum_set$ )Bool )
(declare-fun finite$m (A_set_a_set_sum_set$ )Bool )
(declare-fun finite$n (A_a_sum_a_sum_set$ )Bool )
(declare-fun finite$o (A_set_a_a_sum_sum_set$ )Bool )
(declare-fun finite$p (A_a_sum_a_set_sum_set$ )Bool )
(declare-fun finite$q (A_a_sum_a_a_sum_sum_set$ )Bool )
(declare-fun finite$r (A_a_set_set_sum_set$ )Bool )
(declare-fun alphabet$ (A_tree$ )A_set$ )
(declare-fun alphabet$a (A_a_sum_tree$ )A_a_sum_set$ )
(declare-fun alphabet$b (A_set_tree$ )A_set_set$ )
(assert (! (not (finite$ (alphabet$ t$ ))):named a0 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_sum_tree$ )(?v2 A_a_sum_tree$ ))(! (= (alphabet$a (innerNode$a ?v0 ?v1 ?v2 ))(sup$ (alphabet$a ?v1 )(alphabet$a ?v2 ))):pattern ((innerNode$a ?v0 ?v1 ?v2 )))):named a1 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_set_tree$ )(?v2 A_set_tree$ ))(! (= (alphabet$b (innerNode$b ?v0 ?v1 ?v2 ))(sup$a (alphabet$b ?v1 )(alphabet$b ?v2 ))):pattern ((innerNode$b ?v0 ?v1 ?v2 )))):named a2 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_tree$ )(?v2 A_tree$ ))(! (= (alphabet$ (innerNode$ ?v0 ?v1 ?v2 ))(sup$b (alphabet$ ?v1 )(alphabet$ ?v2 ))):pattern ((innerNode$ ?v0 ?v1 ?v2 )))):named a3 ))
(assert (! (forall ((?v0 A_set_a_sum_set$ ))(= (finite$a (pow$ ?v0 ))(finite$b ?v0 ))):named a4 ))
(assert (! (forall ((?v0 A_a_a_sum_sum_set$ ))(= (finite$c (pow$a ?v0 ))(finite$d ?v0 ))):named a5 ))
(assert (! (forall ((?v0 A_a_set_sum_set$ ))(= (finite$e (pow$b ?v0 ))(finite$f ?v0 ))):named a6 ))
(assert (! (forall ((?v0 A_a_sum_set_set$ ))(= (finite$g (pow$c ?v0 ))(finite$h ?v0 ))):named a7 ))
(assert (! (forall ((?v0 A_set_set_set$ ))(= (finite$i (pow$d ?v0 ))(finite$j ?v0 ))):named a8 ))
(assert (! (forall ((?v0 A_set_set$ ))(= (finite$j (pow$e ?v0 ))(finite$k ?v0 ))):named a9 ))
(assert (! (forall ((?v0 A_a_sum_set$ ))(= (finite$h (pow$f ?v0 ))(finite$l ?v0 ))):named a10 ))
(assert (! (forall ((?v0 A_set$ ))(= (finite$k (pow$g ?v0 ))(finite$ ?v0 ))):named a11 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_set$ ))(= (finite$l (plus$ ?v0 ?v1 ))(and (finite$ ?v0 )(finite$ ?v1 )))):named a12 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_set_set$ ))(= (finite$f (plus$a ?v0 ?v1 ))(and (finite$ ?v0 )(finite$k ?v1 )))):named a13 ))
(assert (! (forall ((?v0 A_set_set$ )(?v1 A_set$ ))(= (finite$b (plus$b ?v0 ?v1 ))(and (finite$k ?v0 )(finite$ ?v1 )))):named a14 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_a_sum_set$ ))(= (finite$d (plus$c ?v0 ?v1 ))(and (finite$ ?v0 )(finite$l ?v1 )))):named a15 ))
(assert (! (forall ((?v0 A_set_set$ )(?v1 A_set_set$ ))(= (finite$m (plus$d ?v0 ?v1 ))(and (finite$k ?v0 )(finite$k ?v1 )))):named a16 ))
(assert (! (forall ((?v0 A_a_sum_set$ )(?v1 A_set$ ))(= (finite$n (plus$e ?v0 ?v1 ))(and (finite$l ?v0 )(finite$ ?v1 )))):named a17 ))
(assert (! (forall ((?v0 A_set_set$ )(?v1 A_a_sum_set$ ))(= (finite$o (plus$f ?v0 ?v1 ))(and (finite$k ?v0 )(finite$l ?v1 )))):named a18 ))
(assert (! (forall ((?v0 A_a_sum_set$ )(?v1 A_set_set$ ))(= (finite$p (plus$g ?v0 ?v1 ))(and (finite$l ?v0 )(finite$k ?v1 )))):named a19 ))
(assert (! (forall ((?v0 A_a_sum_set$ )(?v1 A_a_sum_set$ ))(= (finite$q (plus$h ?v0 ?v1 ))(and (finite$l ?v0 )(finite$l ?v1 )))):named a20 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_set_set_set$ ))(= (finite$r (plus$i ?v0 ?v1 ))(and (finite$ ?v0 )(finite$j ?v1 )))):named a21 ))
(assert (! (forall ((?v0 A_set_a_sum_set$ )(?v1 A_set_a_sum_set$ ))(=> (finite$b ?v0 )(= (finite$b (minus$ ?v1 ?v0 ))(finite$b ?v1 )))):named a22 ))
(assert (! (forall ((?v0 A_a_a_sum_sum_set$ )(?v1 A_a_a_sum_sum_set$ ))(=> (finite$d ?v0 )(= (finite$d (minus$a ?v1 ?v0 ))(finite$d ?v1 )))):named a23 ))
(assert (! (forall ((?v0 A_a_set_sum_set$ )(?v1 A_a_set_sum_set$ ))(=> (finite$f ?v0 )(= (finite$f (minus$b ?v1 ?v0 ))(finite$f ?v1 )))):named a24 ))
(assert (! (forall ((?v0 A_a_sum_set_set$ )(?v1 A_a_sum_set_set$ ))(=> (finite$h ?v0 )(= (finite$h (minus$c ?v1 ?v0 ))(finite$h ?v1 )))):named a25 ))
(assert (! (forall ((?v0 A_set_set_set$ )(?v1 A_set_set_set$ ))(=> (finite$j ?v0 )(= (finite$j (minus$d ?v1 ?v0 ))(finite$j ?v1 )))):named a26 ))
(assert (! (forall ((?v0 A_set_set$ )(?v1 A_set_set$ ))(=> (finite$k ?v0 )(= (finite$k (minus$e ?v1 ?v0 ))(finite$k ?v1 )))):named a27 ))
(assert (! (forall ((?v0 A_a_sum_set$ )(?v1 A_a_sum_set$ ))(=> (finite$l ?v0 )(= (finite$l (minus$f ?v1 ?v0 ))(finite$l ?v1 )))):named a28 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_set$ ))(=> (finite$ ?v0 )(= (finite$ (minus$g ?v1 ?v0 ))(finite$ ?v1 )))):named a29 ))
(assert (! (forall ((?v0 A_set_a_sum_set$ )(?v1 A_set_a_sum_set$ ))(=> (finite$b ?v0 )(finite$b (minus$ ?v0 ?v1 )))):named a30 ))
(assert (! (forall ((?v0 A_a_a_sum_sum_set$ )(?v1 A_a_a_sum_sum_set$ ))(=> (finite$d ?v0 )(finite$d (minus$a ?v0 ?v1 )))):named a31 ))
(assert (! (forall ((?v0 A_a_set_sum_set$ )(?v1 A_a_set_sum_set$ ))(=> (finite$f ?v0 )(finite$f (minus$b ?v0 ?v1 )))):named a32 ))
(assert (! (forall ((?v0 A_a_sum_set_set$ )(?v1 A_a_sum_set_set$ ))(=> (finite$h ?v0 )(finite$h (minus$c ?v0 ?v1 )))):named a33 ))
(assert (! (forall ((?v0 A_set_set_set$ )(?v1 A_set_set_set$ ))(=> (finite$j ?v0 )(finite$j (minus$d ?v0 ?v1 )))):named a34 ))
(assert (! (forall ((?v0 A_set_set$ )(?v1 A_set_set$ ))(=> (finite$k ?v0 )(finite$k (minus$e ?v0 ?v1 )))):named a35 ))
(assert (! (forall ((?v0 A_a_sum_set$ )(?v1 A_a_sum_set$ ))(=> (finite$l ?v0 )(finite$l (minus$f ?v0 ?v1 )))):named a36 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_set$ ))(=> (finite$ ?v0 )(finite$ (minus$g ?v0 ?v1 )))):named a37 ))
(assert (! (forall ((?v0 A_set_a_sum_set$ )(?v1 A_set_a_sum_set$ ))(=> (or (finite$b ?v0 )(finite$b ?v1 ))(finite$b (inf$ ?v0 ?v1 )))):named a38 ))
(assert (! (forall ((?v0 A_a_a_sum_sum_set$ )(?v1 A_a_a_sum_sum_set$ ))(=> (or (finite$d ?v0 )(finite$d ?v1 ))(finite$d (inf$a ?v0 ?v1 )))):named a39 ))
(assert (! (forall ((?v0 A_a_set_sum_set$ )(?v1 A_a_set_sum_set$ ))(=> (or (finite$f ?v0 )(finite$f ?v1 ))(finite$f (inf$b ?v0 ?v1 )))):named a40 ))
(assert (! (forall ((?v0 A_a_sum_set_set$ )(?v1 A_a_sum_set_set$ ))(=> (or (finite$h ?v0 )(finite$h ?v1 ))(finite$h (inf$c ?v0 ?v1 )))):named a41 ))
(assert (! (forall ((?v0 A_set_set_set$ )(?v1 A_set_set_set$ ))(=> (or (finite$j ?v0 )(finite$j ?v1 ))(finite$j (inf$d ?v0 ?v1 )))):named a42 ))
(assert (! (forall ((?v0 A_set_set$ )(?v1 A_set_set$ ))(=> (or (finite$k ?v0 )(finite$k ?v1 ))(finite$k (inf$e ?v0 ?v1 )))):named a43 ))
(assert (! (forall ((?v0 A_a_sum_set$ )(?v1 A_a_sum_set$ ))(=> (or (finite$l ?v0 )(finite$l ?v1 ))(finite$l (inf$f ?v0 ?v1 )))):named a44 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_set$ ))(=> (or (finite$ ?v0 )(finite$ ?v1 ))(finite$ (inf$g ?v0 ?v1 )))):named a45 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_tree$ )(?v2 A_tree$ )(?v3 Nat$ )(?v4 A_tree$ )(?v5 A_tree$ ))(= (= (innerNode$ ?v0 ?v1 ?v2 )(innerNode$ ?v3 ?v4 ?v5 ))(and (= ?v0 ?v3 )(and (= ?v1 ?v4 )(= ?v2 ?v5 ))))):named a46 ))
(assert (! (forall ((?v0 A_set_a_sum_set$ )(?v1 A_set_a_sum_set$ ))(= (finite$b (sup$c ?v0 ?v1 ))(and (finite$b ?v0 )(finite$b ?v1 )))):named a47 ))
(assert (! (forall ((?v0 A_a_a_sum_sum_set$ )(?v1 A_a_a_sum_sum_set$ ))(= (finite$d (sup$d ?v0 ?v1 ))(and (finite$d ?v0 )(finite$d ?v1 )))):named a48 ))
(assert (! (forall ((?v0 A_a_set_sum_set$ )(?v1 A_a_set_sum_set$ ))(= (finite$f (sup$e ?v0 ?v1 ))(and (finite$f ?v0 )(finite$f ?v1 )))):named a49 ))
(assert (! (forall ((?v0 A_a_sum_set_set$ )(?v1 A_a_sum_set_set$ ))(= (finite$h (sup$f ?v0 ?v1 ))(and (finite$h ?v0 )(finite$h ?v1 )))):named a50 ))
(assert (! (forall ((?v0 A_set_set_set$ )(?v1 A_set_set_set$ ))(= (finite$j (sup$g ?v0 ?v1 ))(and (finite$j ?v0 )(finite$j ?v1 )))):named a51 ))
(assert (! (forall ((?v0 A_set_set$ )(?v1 A_set_set$ ))(= (finite$k (sup$a ?v0 ?v1 ))(and (finite$k ?v0 )(finite$k ?v1 )))):named a52 ))
(assert (! (forall ((?v0 A_a_sum_set$ )(?v1 A_a_sum_set$ ))(= (finite$l (sup$ ?v0 ?v1 ))(and (finite$l ?v0 )(finite$l ?v1 )))):named a53 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_set$ ))(= (finite$ (sup$b ?v0 ?v1 ))(and (finite$ ?v0 )(finite$ ?v1 )))):named a54 ))
(assert (! (forall ((?v0 A_set_a_sum_set$ )(?v1 A_set_a_sum_set$ ))(=> (and (finite$b ?v0 )(finite$b ?v1 ))(finite$b (sup$c ?v0 ?v1 )))):named a55 ))
(assert (! (forall ((?v0 A_a_a_sum_sum_set$ )(?v1 A_a_a_sum_sum_set$ ))(=> (and (finite$d ?v0 )(finite$d ?v1 ))(finite$d (sup$d ?v0 ?v1 )))):named a56 ))
(assert (! (forall ((?v0 A_a_set_sum_set$ )(?v1 A_a_set_sum_set$ ))(=> (and (finite$f ?v0 )(finite$f ?v1 ))(finite$f (sup$e ?v0 ?v1 )))):named a57 ))
(assert (! (forall ((?v0 A_a_sum_set_set$ )(?v1 A_a_sum_set_set$ ))(=> (and (finite$h ?v0 )(finite$h ?v1 ))(finite$h (sup$f ?v0 ?v1 )))):named a58 ))
(assert (! (forall ((?v0 A_set_set_set$ )(?v1 A_set_set_set$ ))(=> (and (finite$j ?v0 )(finite$j ?v1 ))(finite$j (sup$g ?v0 ?v1 )))):named a59 ))
(assert (! (forall ((?v0 A_set_set$ )(?v1 A_set_set$ ))(=> (and (finite$k ?v0 )(finite$k ?v1 ))(finite$k (sup$a ?v0 ?v1 )))):named a60 ))
(assert (! (forall ((?v0 A_a_sum_set$ )(?v1 A_a_sum_set$ ))(=> (and (finite$l ?v0 )(finite$l ?v1 ))(finite$l (sup$ ?v0 ?v1 )))):named a61 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_set$ ))(=> (and (finite$ ?v0 )(finite$ ?v1 ))(finite$ (sup$b ?v0 ?v1 )))):named a62 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_set$ ))(=> (and (finite$ ?v0 )(finite$ ?v1 ))(finite$l (plus$ ?v0 ?v1 )))):named a63 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_set_set$ ))(=> (and (finite$ ?v0 )(finite$k ?v1 ))(finite$f (plus$a ?v0 ?v1 )))):named a64 ))
(assert (! (forall ((?v0 A_set_set$ )(?v1 A_set$ ))(=> (and (finite$k ?v0 )(finite$ ?v1 ))(finite$b (plus$b ?v0 ?v1 )))):named a65 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_a_sum_set$ ))(=> (and (finite$ ?v0 )(finite$l ?v1 ))(finite$d (plus$c ?v0 ?v1 )))):named a66 ))
(assert (! (forall ((?v0 A_set_set$ )(?v1 A_set_set$ ))(=> (and (finite$k ?v0 )(finite$k ?v1 ))(finite$m (plus$d ?v0 ?v1 )))):named a67 ))
(assert (! (forall ((?v0 A_a_sum_set$ )(?v1 A_set$ ))(=> (and (finite$l ?v0 )(finite$ ?v1 ))(finite$n (plus$e ?v0 ?v1 )))):named a68 ))
(assert (! (forall ((?v0 A_set_set$ )(?v1 A_a_sum_set$ ))(=> (and (finite$k ?v0 )(finite$l ?v1 ))(finite$o (plus$f ?v0 ?v1 )))):named a69 ))
(assert (! (forall ((?v0 A_a_sum_set$ )(?v1 A_set_set$ ))(=> (and (finite$l ?v0 )(finite$k ?v1 ))(finite$p (plus$g ?v0 ?v1 )))):named a70 ))
(assert (! (forall ((?v0 A_a_sum_set$ )(?v1 A_a_sum_set$ ))(=> (and (finite$l ?v0 )(finite$l ?v1 ))(finite$q (plus$h ?v0 ?v1 )))):named a71 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_set_set_set$ ))(=> (and (finite$ ?v0 )(finite$j ?v1 ))(finite$r (plus$i ?v0 ?v1 )))):named a72 ))
(check-sat )
;(get-unsat-core )
