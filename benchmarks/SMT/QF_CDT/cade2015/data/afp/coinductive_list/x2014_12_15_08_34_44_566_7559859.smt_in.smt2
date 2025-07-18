;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_a_fun$ 0 )
(declare-sort Nat_set$ 0 )
(declare-sort A_nat_fun$ 0 )
(declare-sort Nat_a_fun$ 0 )
(declare-sort Nat_nat_fun$ 0 )
(declare-sort Nat_bool_fun$ 0 )
(declare-sort A_nat_a_fun_fun$ 0 )
(declare-sort A_a_nat_prod_fun$ 0 )
(declare-sort A_nat_prod_a_fun$ 0 )
(declare-sort A_nat_bool_fun_fun$ 0 )
(declare-sort A_nat_prod_nat_fun$ 0 )
(declare-sort Nat_a_nat_prod_fun$ 0 )
(declare-sort A_nat_prod_bool_fun$ 0 )
(declare-sort Nat_nat_bool_fun_fun$ 0 )
(declare-sort Nat_nat_prod_nat_fun$ 0 )
(declare-sort Nat_nat_prod_bool_fun$ 0 )
(declare-sort A_nat_prod_a_nat_prod_fun$ 0 )
(declare-sort A_nat_prod_nat_bool_fun_fun$ 0 )
(declare-sort A_nat_prod_nat_prod_bool_fun$ 0 )
(declare-sort A_nat_prod_nat_a_nat_prod_fun_fun$ 0 )
(declare-sort A_nat_prod_nat_prod_a_nat_prod_fun$ 0 )
(declare-sort A_nat_prod_bool_fun_a_nat_prod_bool_fun_fun$ 0 )
(declare-sort A_nat_prod_nat_prod_bool_fun_a_nat_prod_nat_prod_bool_fun_fun$ 0 )
(declare-sort A_llist$ 0)
(declare-fun lNil$ ()A_llist$)
(declare-fun lhd$ (A_llist$)A$)
(declare-fun ltl$ (A_llist$)A_llist$)
(declare-fun lCons$ (A$ A_llist$ )A_llist$)
(declare-datatypes ()((A_nat_prod$ (pair$ (fst$ A$ )(snd$ Nat$ )))))
(declare-sort A_nat_prod_llist$ 0)
(declare-sort Nat_llist$ 0)
(declare-fun lNil$a ()A_nat_prod_llist$)
(declare-fun lhd$a (A_nat_prod_llist$)A_nat_prod$)
(declare-fun ltl$a (A_nat_prod_llist$)A_nat_prod_llist$)
(declare-fun lCons$a (A_nat_prod$ A_nat_prod_llist$ )A_nat_prod_llist$)
(declare-fun lNil$b ()Nat_llist$)
(declare-fun lhd$b (Nat_llist$)Nat$)
(declare-fun ltl$b (Nat_llist$)Nat_llist$)
(declare-fun lCons$b (Nat$ Nat_llist$ )Nat_llist$)
(declare-datatypes ()((A_nat_prod_nat_prod$ (pair$a (fst$a A_nat_prod$ )(snd$a Nat$ )))))
(declare-sort A_nat_prod_nat_prod_llist$ 0)
(declare-fun lNil$c ()A_nat_prod_nat_prod_llist$)
(declare-fun lhd$c (A_nat_prod_nat_prod_llist$)A_nat_prod_nat_prod$)
(declare-fun ltl$c (A_nat_prod_nat_prod_llist$)A_nat_prod_nat_prod_llist$)
(declare-fun lCons$c (A_nat_prod_nat_prod$ A_nat_prod_nat_prod_llist$ )A_nat_prod_nat_prod_llist$)
(declare-datatypes ()((Nat_nat_prod$ (pair$b (fst$b Nat$ )(snd$b Nat$ )))))
(declare-sort Nat_nat_prod_llist$ 0)
(declare-fun lNil$d ()Nat_nat_prod_llist$)
(declare-fun lhd$d (Nat_nat_prod_llist$)Nat_nat_prod$)
(declare-fun ltl$d (Nat_nat_prod_llist$)Nat_nat_prod_llist$)
(declare-fun lCons$d (Nat_nat_prod$ Nat_nat_prod_llist$ )Nat_nat_prod_llist$)
(declare-fun a$ ()Nat_set$ )
(declare-fun uu$ ()A_nat_prod_a_fun$ )
(declare-fun xs$ ()A_llist$ )
(declare-fun ys$ ()A_llist$ )
(declare-fun suc$ ()Nat_nat_fun$ )
(declare-fun uua$ ()A_nat_bool_fun_fun$ )
(declare-fun uub$ ()A_a_fun$ )
(declare-fun uuc$ ()Nat_nat_fun$ )
(declare-fun uud$ ()A_nat_prod_nat_prod_bool_fun$ )
(declare-fun uue$ ()A_nat_prod_bool_fun$ )
(declare-fun uuf$ (A_nat_prod_nat_prod_bool_fun$ )A_nat_prod_nat_prod_bool_fun_a_nat_prod_nat_prod_bool_fun_fun$ )
(declare-fun uug$ (A_nat_prod_bool_fun$ )A_nat_prod_bool_fun_a_nat_prod_bool_fun_fun$ )
(declare-fun uuh$ ()Nat_nat_prod_nat_fun$ )
(declare-fun uui$ (Nat_set$ )Nat_nat_bool_fun_fun$ )
(declare-fun uuj$ ()A_nat_prod_nat_prod_a_nat_prod_fun$ )
(declare-fun uuk$ (Nat_set$ )A_nat_prod_nat_bool_fun_fun$ )
(declare-fun uul$ (Nat_set$ )A_nat_bool_fun_fun$ )
(declare-fun uum$ (Bool A_nat_prod_nat_bool_fun_fun$ )A_nat_prod_nat_bool_fun_fun$ )
(declare-fun uun$ (Bool A_nat_bool_fun_fun$ )A_nat_bool_fun_fun$ )
(declare-fun uuo$ ()A_nat_prod_nat_a_nat_prod_fun_fun$ )
(declare-fun uup$ ()A_nat_a_fun_fun$ )
(declare-fun lmap$ (A_nat_prod_a_fun$ A_nat_prod_llist$ )A_llist$ )
(declare-fun lzip$ (A_llist$ Nat_llist$ )A_nat_prod_llist$ )
(declare-fun zero$ ()Nat$ )
(declare-fun lmap$a (A_a_fun$ A_llist$ )A_llist$ )
(declare-fun lmap$b (Nat_nat_fun$ Nat_llist$ )Nat_llist$ )
(declare-fun lmap$c (A_nat_prod_nat_fun$ A_nat_prod_llist$ )Nat_llist$ )
(declare-fun lmap$d (Nat_a_nat_prod_fun$ Nat_llist$ )A_nat_prod_llist$ )
(declare-fun lmap$e (Nat_a_fun$ Nat_llist$ )A_llist$ )
(declare-fun lmap$f (A_nat_fun$ A_llist$ )Nat_llist$ )
(declare-fun lmap$g (A_a_nat_prod_fun$ A_llist$ )A_nat_prod_llist$ )
(declare-fun lmap$h (A_nat_prod_a_nat_prod_fun$ A_nat_prod_llist$ )A_nat_prod_llist$ )
(declare-fun lmap$i (Nat_nat_prod_nat_fun$ Nat_nat_prod_llist$ )Nat_llist$ )
(declare-fun lmap$j (A_nat_prod_nat_prod_a_nat_prod_fun$ A_nat_prod_nat_prod_llist$ )A_nat_prod_llist$ )
(declare-fun lzip$a (Nat_llist$ Nat_llist$ )Nat_nat_prod_llist$ )
(declare-fun lzip$b (A_nat_prod_llist$ Nat_llist$ )A_nat_prod_nat_prod_llist$ )
(declare-fun member$ (Nat$ Nat_set$ )Bool )
(declare-fun fun_app$ (A_nat_prod_nat_prod_a_nat_prod_fun$ A_nat_prod_nat_prod$ )A_nat_prod$ )
(declare-fun lappend$ (A_llist$ A_llist$ )A_llist$ )
(declare-fun lfilter$ (A_nat_prod_bool_fun$ A_nat_prod_llist$ )A_nat_prod_llist$ )
(declare-fun lfinite$ (A_llist$ )Bool )
(declare-fun fun_app$a (Nat_nat_prod_nat_fun$ Nat_nat_prod$ )Nat$ )
(declare-fun fun_app$b (A_nat_prod_a_fun$ A_nat_prod$ )A$ )
(declare-fun fun_app$c (Nat_bool_fun$ Nat$ )Bool )
(declare-fun fun_app$d (A_nat_bool_fun_fun$ A$ )Nat_bool_fun$ )
(declare-fun fun_app$e (A_nat_prod_nat_prod_bool_fun$ A_nat_prod_nat_prod$ )Bool )
(declare-fun fun_app$f (A_nat_prod_nat_prod_bool_fun_a_nat_prod_nat_prod_bool_fun_fun$ A_nat_prod_nat_prod_bool_fun$ )A_nat_prod_nat_prod_bool_fun$ )
(declare-fun fun_app$g (A_nat_prod_bool_fun$ A_nat_prod$ )Bool )
(declare-fun fun_app$h (A_nat_prod_bool_fun_a_nat_prod_bool_fun_fun$ A_nat_prod_bool_fun$ )A_nat_prod_bool_fun$ )
(declare-fun fun_app$i (A_nat_prod_nat_bool_fun_fun$ A_nat_prod$ )Nat_bool_fun$ )
(declare-fun fun_app$j (Nat_nat_bool_fun_fun$ Nat$ )Nat_bool_fun$ )
(declare-fun fun_app$k (Nat_a_nat_prod_fun$ Nat$ )A_nat_prod$ )
(declare-fun fun_app$l (A_nat_prod_nat_a_nat_prod_fun_fun$ A_nat_prod$ )Nat_a_nat_prod_fun$ )
(declare-fun fun_app$m (Nat_a_fun$ Nat$ )A$ )
(declare-fun fun_app$n (A_nat_a_fun_fun$ A$ )Nat_a_fun$ )
(declare-fun fun_app$o (Nat_nat_fun$ Nat$ )Nat$ )
(declare-fun fun_app$p (A_a_fun$ A$ )A$ )
(declare-fun fun_app$q (A_nat_prod_a_nat_prod_fun$ A_nat_prod$ )A_nat_prod$ )
(declare-fun iterates$ (Nat_nat_fun$ Nat$ )Nat_llist$ )
(declare-fun lappend$a (Nat_llist$ Nat_llist$ )Nat_llist$ )
(declare-fun lappend$b (A_nat_prod_llist$ A_nat_prod_llist$ )A_nat_prod_llist$ )
(declare-fun lfilter$a (A_nat_prod_nat_prod_bool_fun$ A_nat_prod_nat_prod_llist$ )A_nat_prod_nat_prod_llist$ )
(declare-fun lfilter$b (Nat_nat_prod_bool_fun$ Nat_nat_prod_llist$ )Nat_nat_prod_llist$ )
(declare-fun lsublist$ (A_llist$ Nat_set$ )A_llist$ )
(declare-fun case_prod$ (A_nat_bool_fun_fun$ )A_nat_prod_bool_fun$ )
(declare-fun iterates$a (A_nat_prod_a_nat_prod_fun$ A_nat_prod$ )A_nat_prod_llist$ )
(declare-fun iterates$b (A_a_fun$ A$ )A_llist$ )
(declare-fun lsublist$a (Nat_llist$ Nat_set$ )Nat_llist$ )
(declare-fun lsublist$b (A_nat_prod_llist$ Nat_set$ )A_nat_prod_llist$ )
(declare-fun case_prod$a (Nat_nat_bool_fun_fun$ )Nat_nat_prod_bool_fun$ )
(declare-fun case_prod$b (A_nat_prod_nat_bool_fun_fun$ )A_nat_prod_nat_prod_bool_fun$ )
(declare-fun case_prod$c (A_nat_prod_nat_a_nat_prod_fun_fun$ A_nat_prod_nat_prod$ )A_nat_prod$ )
(declare-fun case_prod$d (A_nat_a_fun_fun$ )A_nat_prod_a_fun$ )
(assert (! (forall ((?v0 A_nat_prod_nat_prod$ ))(! (= (fun_app$ uuj$ ?v0 )(fst$a ?v0 )):pattern ((fun_app$ uuj$ ?v0 )))):named a0 ))
(assert (! (forall ((?v0 Nat_nat_prod$ ))(! (= (fun_app$a uuh$ ?v0 )(fst$b ?v0 )):pattern ((fun_app$a uuh$ ?v0 )))):named a1 ))
(assert (! (forall ((?v0 A_nat_prod$ ))(! (= (fun_app$b uu$ ?v0 )(fst$ ?v0 )):pattern ((fun_app$b uu$ ?v0 )))):named a2 ))
(assert (! (forall ((?v0 A$ )(?v1 Nat$ ))(! (= (fun_app$c (fun_app$d uua$ ?v0 )?v1 )(member$ ?v1 a$ )):pattern ((fun_app$c (fun_app$d uua$ ?v0 )?v1 )))):named a3 ))
(assert (! (forall ((?v0 A_nat_prod_nat_prod_bool_fun$ )(?v1 A_nat_prod_nat_prod_bool_fun$ )(?v2 A_nat_prod_nat_prod$ ))(! (= (fun_app$e (fun_app$f (uuf$ ?v0 )?v1 )?v2 )(and (fun_app$e ?v0 ?v2 )(fun_app$e ?v1 ?v2 ))):pattern ((fun_app$e (fun_app$f (uuf$ ?v0 )?v1 )?v2 )))):named a4 ))
(assert (! (forall ((?v0 A_nat_prod_bool_fun$ )(?v1 A_nat_prod_bool_fun$ )(?v2 A_nat_prod$ ))(! (= (fun_app$g (fun_app$h (uug$ ?v0 )?v1 )?v2 )(and (fun_app$g ?v0 ?v2 )(fun_app$g ?v1 ?v2 ))):pattern ((fun_app$g (fun_app$h (uug$ ?v0 )?v1 )?v2 )))):named a5 ))
(assert (! (forall ((?v0 Nat_set$ )(?v1 A_nat_prod$ )(?v2 Nat$ ))(! (= (fun_app$c (fun_app$i (uuk$ ?v0 )?v1 )?v2 )(member$ ?v2 ?v0 )):pattern ((fun_app$c (fun_app$i (uuk$ ?v0 )?v1 )?v2 )))):named a6 ))
(assert (! (forall ((?v0 Nat_set$ )(?v1 Nat$ )(?v2 Nat$ ))(! (= (fun_app$c (fun_app$j (uui$ ?v0 )?v1 )?v2 )(member$ ?v2 ?v0 )):pattern ((fun_app$c (fun_app$j (uui$ ?v0 )?v1 )?v2 )))):named a7 ))
(assert (! (forall ((?v0 Nat_set$ )(?v1 A$ )(?v2 Nat$ ))(! (= (fun_app$c (fun_app$d (uul$ ?v0 )?v1 )?v2 )(member$ ?v2 ?v0 )):pattern ((fun_app$c (fun_app$d (uul$ ?v0 )?v1 )?v2 )))):named a8 ))
(assert (! (forall ((?v0 Bool )(?v1 A_nat_prod_nat_bool_fun_fun$ )(?v2 A_nat_prod$ )(?v3 Nat$ ))(! (= (fun_app$c (fun_app$i (uum$ ?v0 ?v1 )?v2 )?v3 )(and ?v0 (fun_app$c (fun_app$i ?v1 ?v2 )?v3 ))):pattern ((fun_app$c (fun_app$i (uum$ ?v0 ?v1 )?v2 )?v3 )))):named a9 ))
(assert (! (forall ((?v0 Bool )(?v1 A_nat_bool_fun_fun$ )(?v2 A$ )(?v3 Nat$ ))(! (= (fun_app$c (fun_app$d (uun$ ?v0 ?v1 )?v2 )?v3 )(and ?v0 (fun_app$c (fun_app$d ?v1 ?v2 )?v3 ))):pattern ((fun_app$c (fun_app$d (uun$ ?v0 ?v1 )?v2 )?v3 )))):named a10 ))
(assert (! (forall ((?v0 A_nat_prod$ )(?v1 Nat$ ))(! (= (fun_app$k (fun_app$l uuo$ ?v0 )?v1 )?v0 ):pattern ((fun_app$k (fun_app$l uuo$ ?v0 )?v1 )))):named a11 ))
(assert (! (forall ((?v0 A$ )(?v1 Nat$ ))(! (= (fun_app$m (fun_app$n uup$ ?v0 )?v1 )?v0 ):pattern ((fun_app$m (fun_app$n uup$ ?v0 )?v1 )))):named a12 ))
(assert (! (forall ((?v0 Nat$ ))(! (= (fun_app$o uuc$ ?v0 )?v0 ):pattern ((fun_app$o uuc$ ?v0 )))):named a13 ))
(assert (! (forall ((?v0 A$ ))(! (= (fun_app$p uub$ ?v0 )?v0 ):pattern ((fun_app$p uub$ ?v0 )))):named a14 ))
(assert (! (forall ((?v0 A_nat_prod_nat_prod$ ))(! (= (fun_app$e uud$ ?v0 )true ):pattern ((fun_app$e uud$ ?v0 )))):named a15 ))
(assert (! (forall ((?v0 A_nat_prod$ ))(! (= (fun_app$g uue$ ?v0 )true ):pattern ((fun_app$g uue$ ?v0 )))):named a16 ))
(assert (! (not (= (lsublist$ (lappend$ xs$ ys$ )a$ )(lmap$ uu$ (lfilter$ (case_prod$ uua$ )(lzip$ (lappend$ xs$ ys$ )(iterates$ suc$ zero$ )))))):named a17 ))
(assert (! (forall ((?v0 A_nat_prod_nat_prod_bool_fun$ )(?v1 A_nat_prod_nat_prod_llist$ ))(= (lfilter$a ?v0 (lfilter$a ?v0 ?v1 ))(lfilter$a ?v0 ?v1 ))):named a18 ))
(assert (! (forall ((?v0 A_nat_prod_bool_fun$ )(?v1 A_nat_prod_llist$ ))(= (lfilter$ ?v0 (lfilter$ ?v0 ?v1 ))(lfilter$ ?v0 ?v1 ))):named a19 ))
(assert (! (forall ((?v0 A_llist$ ))(= (lmap$a uub$ ?v0 )?v0 )):named a20 ))
(assert (! (forall ((?v0 Nat_llist$ ))(= (lmap$b uuc$ ?v0 )?v0 )):named a21 ))
(assert (! (forall ((?v0 A_nat_prod_nat_prod_llist$ ))(= (lfilter$a uud$ ?v0 )?v0 )):named a22 ))
(assert (! (forall ((?v0 A_nat_prod_llist$ ))(= (lfilter$ uue$ ?v0 )?v0 )):named a23 ))
(assert (! (forall ((?v0 A_nat_prod_nat_fun$ )(?v1 A_nat_prod_llist$ )(?v2 Nat_set$ ))(= (lsublist$a (lmap$c ?v0 ?v1 )?v2 )(lmap$c ?v0 (lsublist$b ?v1 ?v2 )))):named a24 ))
(assert (! (forall ((?v0 Nat_a_nat_prod_fun$ )(?v1 Nat_llist$ )(?v2 Nat_set$ ))(= (lsublist$b (lmap$d ?v0 ?v1 )?v2 )(lmap$d ?v0 (lsublist$a ?v1 ?v2 )))):named a25 ))
(assert (! (forall ((?v0 Nat_a_fun$ )(?v1 Nat_llist$ )(?v2 Nat_set$ ))(= (lsublist$ (lmap$e ?v0 ?v1 )?v2 )(lmap$e ?v0 (lsublist$a ?v1 ?v2 )))):named a26 ))
(assert (! (forall ((?v0 A_nat_fun$ )(?v1 A_llist$ )(?v2 Nat_set$ ))(= (lsublist$a (lmap$f ?v0 ?v1 )?v2 )(lmap$f ?v0 (lsublist$ ?v1 ?v2 )))):named a27 ))
(assert (! (forall ((?v0 A_a_nat_prod_fun$ )(?v1 A_llist$ )(?v2 Nat_set$ ))(= (lsublist$b (lmap$g ?v0 ?v1 )?v2 )(lmap$g ?v0 (lsublist$ ?v1 ?v2 )))):named a28 ))
(assert (! (forall ((?v0 A_nat_prod_a_nat_prod_fun$ )(?v1 A_nat_prod_llist$ )(?v2 Nat_set$ ))(= (lsublist$b (lmap$h ?v0 ?v1 )?v2 )(lmap$h ?v0 (lsublist$b ?v1 ?v2 )))):named a29 ))
(assert (! (forall ((?v0 Nat_nat_fun$ )(?v1 Nat_llist$ )(?v2 Nat_set$ ))(= (lsublist$a (lmap$b ?v0 ?v1 )?v2 )(lmap$b ?v0 (lsublist$a ?v1 ?v2 )))):named a30 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_llist$ )(?v2 Nat_set$ ))(= (lsublist$ (lmap$a ?v0 ?v1 )?v2 )(lmap$a ?v0 (lsublist$ ?v1 ?v2 )))):named a31 ))
(assert (! (forall ((?v0 A_nat_prod_a_fun$ )(?v1 A_nat_prod_llist$ )(?v2 Nat_set$ ))(= (lsublist$ (lmap$ ?v0 ?v1 )?v2 )(lmap$ ?v0 (lsublist$b ?v1 ?v2 )))):named a32 ))
(assert (! (forall ((?v0 Nat_llist$ )(?v1 Nat_llist$ )(?v2 Nat_llist$ ))(= (lappend$a (lappend$a ?v0 ?v1 )?v2 )(lappend$a ?v0 (lappend$a ?v1 ?v2 )))):named a33 ))
(assert (! (forall ((?v0 A_nat_prod_llist$ )(?v1 A_nat_prod_llist$ )(?v2 A_nat_prod_llist$ ))(= (lappend$b (lappend$b ?v0 ?v1 )?v2 )(lappend$b ?v0 (lappend$b ?v1 ?v2 )))):named a34 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(= (lappend$ (lappend$ ?v0 ?v1 )?v2 )(lappend$ ?v0 (lappend$ ?v1 ?v2 )))):named a35 ))
(assert (! (forall ((?v0 A_nat_prod_nat_prod_bool_fun$ )(?v1 A_nat_prod_nat_prod_bool_fun$ )(?v2 A_nat_prod_nat_prod_llist$ ))(= (lfilter$a ?v0 (lfilter$a ?v1 ?v2 ))(lfilter$a (fun_app$f (uuf$ ?v0 )?v1 )?v2 ))):named a36 ))
(assert (! (forall ((?v0 A_nat_prod_bool_fun$ )(?v1 A_nat_prod_bool_fun$ )(?v2 A_nat_prod_llist$ ))(= (lfilter$ ?v0 (lfilter$ ?v1 ?v2 ))(lfilter$ (fun_app$h (uug$ ?v0 )?v1 )?v2 ))):named a37 ))
(assert (! (forall ((?v0 A_nat_prod_a_nat_prod_fun$ )(?v1 A_nat_prod$ )(?v2 A_nat_prod_llist$ ))(= (lappend$b (iterates$a ?v0 ?v1 )?v2 )(iterates$a ?v0 ?v1 ))):named a38 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A$ )(?v2 A_llist$ ))(= (lappend$ (iterates$b ?v0 ?v1 )?v2 )(iterates$b ?v0 ?v1 ))):named a39 ))
(assert (! (forall ((?v0 Nat_nat_fun$ )(?v1 Nat$ )(?v2 Nat_llist$ ))(= (lappend$a (iterates$ ?v0 ?v1 )?v2 )(iterates$ ?v0 ?v1 ))):named a40 ))
(assert (! (forall ((?v0 A_nat_prod_a_nat_prod_fun$ )(?v1 A_nat_prod$ ))(= (lmap$h ?v0 (iterates$a ?v0 ?v1 ))(iterates$a ?v0 (fun_app$q ?v0 ?v1 )))):named a41 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A$ ))(= (lmap$a ?v0 (iterates$b ?v0 ?v1 ))(iterates$b ?v0 (fun_app$p ?v0 ?v1 )))):named a42 ))
(assert (! (forall ((?v0 Nat_nat_fun$ )(?v1 Nat$ ))(= (lmap$b ?v0 (iterates$ ?v0 ?v1 ))(iterates$ ?v0 (fun_app$o ?v0 ?v1 )))):named a43 ))
(assert (! (forall ((?v0 A_nat_fun$ )(?v1 A_llist$ )(?v2 A_llist$ ))(= (lmap$f ?v0 (lappend$ ?v1 ?v2 ))(lappend$a (lmap$f ?v0 ?v1 )(lmap$f ?v0 ?v2 )))):named a44 ))
(assert (! (forall ((?v0 A_a_nat_prod_fun$ )(?v1 A_llist$ )(?v2 A_llist$ ))(= (lmap$g ?v0 (lappend$ ?v1 ?v2 ))(lappend$b (lmap$g ?v0 ?v1 )(lmap$g ?v0 ?v2 )))):named a45 ))
(assert (! (forall ((?v0 Nat_a_fun$ )(?v1 Nat_llist$ )(?v2 Nat_llist$ ))(= (lmap$e ?v0 (lappend$a ?v1 ?v2 ))(lappend$ (lmap$e ?v0 ?v1 )(lmap$e ?v0 ?v2 )))):named a46 ))
(assert (! (forall ((?v0 Nat_a_nat_prod_fun$ )(?v1 Nat_llist$ )(?v2 Nat_llist$ ))(= (lmap$d ?v0 (lappend$a ?v1 ?v2 ))(lappend$b (lmap$d ?v0 ?v1 )(lmap$d ?v0 ?v2 )))):named a47 ))
(assert (! (forall ((?v0 A_nat_prod_nat_fun$ )(?v1 A_nat_prod_llist$ )(?v2 A_nat_prod_llist$ ))(= (lmap$c ?v0 (lappend$b ?v1 ?v2 ))(lappend$a (lmap$c ?v0 ?v1 )(lmap$c ?v0 ?v2 )))):named a48 ))
(assert (! (forall ((?v0 A_nat_prod_a_nat_prod_fun$ )(?v1 A_nat_prod_llist$ )(?v2 A_nat_prod_llist$ ))(= (lmap$h ?v0 (lappend$b ?v1 ?v2 ))(lappend$b (lmap$h ?v0 ?v1 )(lmap$h ?v0 ?v2 )))):named a49 ))
(assert (! (forall ((?v0 Nat_nat_fun$ )(?v1 Nat_llist$ )(?v2 Nat_llist$ ))(= (lmap$b ?v0 (lappend$a ?v1 ?v2 ))(lappend$a (lmap$b ?v0 ?v1 )(lmap$b ?v0 ?v2 )))):named a50 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_llist$ )(?v2 A_llist$ ))(= (lmap$a ?v0 (lappend$ ?v1 ?v2 ))(lappend$ (lmap$a ?v0 ?v1 )(lmap$a ?v0 ?v2 )))):named a51 ))
(assert (! (forall ((?v0 A_nat_prod_a_fun$ )(?v1 A_nat_prod_llist$ )(?v2 A_nat_prod_llist$ ))(= (lmap$ ?v0 (lappend$b ?v1 ?v2 ))(lappend$ (lmap$ ?v0 ?v1 )(lmap$ ?v0 ?v2 )))):named a52 ))
(assert (! (forall ((?v0 Nat_llist$ )(?v1 Nat_set$ ))(= (lsublist$a ?v0 ?v1 )(lmap$i uuh$ (lfilter$b (case_prod$a (uui$ ?v1 ))(lzip$a ?v0 (iterates$ suc$ zero$ )))))):named a53 ))
(assert (! (forall ((?v0 A_nat_prod_llist$ )(?v1 Nat_set$ ))(= (lsublist$b ?v0 ?v1 )(lmap$j uuj$ (lfilter$a (case_prod$b (uuk$ ?v1 ))(lzip$b ?v0 (iterates$ suc$ zero$ )))))):named a54 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 Nat_set$ ))(= (lsublist$ ?v0 ?v1 )(lmap$ uu$ (lfilter$ (case_prod$ (uul$ ?v1 ))(lzip$ ?v0 (iterates$ suc$ zero$ )))))):named a55 ))
(assert (! (forall ((?v0 Bool )(?v1 A_nat_prod_nat_bool_fun_fun$ )(?v2 A_nat_prod_nat_prod$ ))(= (fun_app$e (case_prod$b (uum$ ?v0 ?v1 ))?v2 )(and ?v0 (fun_app$e (case_prod$b ?v1 )?v2 )))):named a56 ))
(assert (! (forall ((?v0 Bool )(?v1 A_nat_bool_fun_fun$ )(?v2 A_nat_prod$ ))(= (fun_app$g (case_prod$ (uun$ ?v0 ?v1 ))?v2 )(and ?v0 (fun_app$g (case_prod$ ?v1 )?v2 )))):named a57 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(= (= (fun_app$o suc$ ?v0 )(fun_app$o suc$ ?v1 ))(= ?v0 ?v1 ))):named a58 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(= (= (fun_app$o suc$ ?v0 )(fun_app$o suc$ ?v1 ))(= ?v0 ?v1 ))):named a59 ))
(assert (! (forall ((?v0 A_nat_prod_nat_prod$ ))(= (fst$a ?v0 )(case_prod$c uuo$ ?v0 ))):named a60 ))
(assert (! (forall ((?v0 A_nat_prod$ ))(= (fst$ ?v0 )(fun_app$b (case_prod$d uup$ )?v0 ))):named a61 ))
(assert (! (lfinite$ xs$ ):named a62 ))
(check-sat )
;(get-unsat-core )
