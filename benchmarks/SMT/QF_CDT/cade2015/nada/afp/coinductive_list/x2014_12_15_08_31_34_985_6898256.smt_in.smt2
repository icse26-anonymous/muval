;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort A_llist_bool_fun$ 0 )
(declare-sort A_llist_a_llist_fun$ 0 )
(declare-sort A_llist_llist_bool_fun$ 0 )
(declare-sort A_llist_set_a_llist_fun$ 0 )
(declare-sort A_llist_llist_a_llist_fun$ 0 )
(declare-sort A_llist_a_llist_bool_fun_fun$ 0 )
(declare-sort A_llist_llist_llist_bool_fun$ 0 )
(declare-sort A_llist_llist_a_llist_llist_fun$ 0 )
(declare-sort A_llist_llist_llist_llist_bool_fun$ 0 )
(declare-sort A_llist_llist_set_a_llist_llist_fun$ 0 )
(declare-sort A_llist_llist_llist_a_llist_llist_fun$ 0 )
(declare-sort A_llist_llist_a_llist_llist_bool_fun_fun$ 0 )
(declare-sort A_llist_llist_llist_a_llist_llist_llist_fun$ 0 )
(declare-sort A_llist_llist_llist_set_a_llist_llist_llist_fun$ 0 )
(declare-sort A_llist_llist_llist_llist_a_llist_llist_llist_fun$ 0 )
(declare-sort A_llist_llist_llist_a_llist_llist_llist_bool_fun_fun$ 0 )
(declare-sort A_llist_llist_llist_llist_a_llist_llist_llist_llist_fun$ 0 )
(declare-sort A_llist_llist_llist_llist_set_a_llist_llist_llist_llist_fun$ 0 )
(declare-sort A_llist_llist_llist_llist_llist_a_llist_llist_llist_llist_fun$ 0 )
(declare-sort A_llist_llist_llist_llist_a_llist_llist_llist_llist_bool_fun_fun$ 0 )
(declare-sort A_llist_llist_llist_llist_llist_a_llist_llist_llist_llist_llist_bool_fun_fun$ 0 )
(declare-sort A_llist$ 0)
(declare-sort A_llist_llist$ 0)
(declare-sort A_llist_llist_llist$ 0)
(declare-sort A_llist_llist_llist_llist$ 0)
(declare-sort A_llist_llist_llist_llist_llist$ 0)
(declare-fun lNil$ ()A_llist$)
(declare-fun lhd$ (A_llist$)A$)
(declare-fun ltl$ (A_llist$)A_llist$)
(declare-fun lCons$ (A$ A_llist$ )A_llist$)
(declare-fun lNil$a ()A_llist_llist$)
(declare-fun lhd$a (A_llist_llist$)A_llist$)
(declare-fun ltl$a (A_llist_llist$)A_llist_llist$)
(declare-fun lCons$a (A_llist$ A_llist_llist$ )A_llist_llist$)
(declare-fun lNil$b ()A_llist_llist_llist$)
(declare-fun lhd$b (A_llist_llist_llist$)A_llist_llist$)
(declare-fun ltl$b (A_llist_llist_llist$)A_llist_llist_llist$)
(declare-fun lCons$b (A_llist_llist$ A_llist_llist_llist$ )A_llist_llist_llist$)
(declare-fun lNil$c ()A_llist_llist_llist_llist$)
(declare-fun lhd$c (A_llist_llist_llist_llist$)A_llist_llist_llist$)
(declare-fun ltl$c (A_llist_llist_llist_llist$)A_llist_llist_llist_llist$)
(declare-fun lCons$c (A_llist_llist_llist$ A_llist_llist_llist_llist$ )A_llist_llist_llist_llist$)
(declare-fun lNil$d ()A_llist_llist_llist_llist_llist$)
(declare-fun lhd$d (A_llist_llist_llist_llist_llist$)A_llist_llist_llist_llist$)
(declare-fun ltl$d (A_llist_llist_llist_llist_llist$)A_llist_llist_llist_llist_llist$)
(declare-fun lCons$d (A_llist_llist_llist_llist$ A_llist_llist_llist_llist_llist$ )A_llist_llist_llist_llist_llist$)
(declare-sort Nat_option$ 0)
(declare-sort Enat$ 0)
(declare-fun none$ ()Nat_option$)
(declare-fun the$ (Nat_option$)Nat$)
(declare-fun some$ (Nat$ )Nat_option$)
(declare-fun rep_enat$ (Enat$)Nat_option$)
(declare-fun abs_enat$ (Nat_option$ )Enat$)
(declare-fun uu$ (A_llist_llist_llist$ )A_llist_llist_llist_llist_a_llist_llist_llist_llist_fun$ )
(declare-fun uua$ (A_llist_llist$ )A_llist_llist_llist_a_llist_llist_llist_fun$ )
(declare-fun uub$ (A_llist$ )A_llist_llist_a_llist_llist_fun$ )
(declare-fun uuc$ (A$ )A_llist_a_llist_fun$ )
(declare-fun uud$ ()A_llist_llist_llist_llist_a_llist_llist_llist_llist_fun$ )
(declare-fun uue$ ()A_llist_llist_llist_a_llist_llist_llist_fun$ )
(declare-fun uuf$ ()A_llist_llist_a_llist_llist_fun$ )
(declare-fun uug$ ()A_llist_a_llist_fun$ )
(declare-fun lSup$ ()A_llist_llist_set_a_llist_llist_fun$ )
(declare-fun lSup$a ()A_llist_set_a_llist_fun$ )
(declare-fun lSup$b ()A_llist_llist_llist_llist_set_a_llist_llist_llist_llist_fun$ )
(declare-fun lSup$c ()A_llist_llist_llist_set_a_llist_llist_llist_fun$ )
(declare-fun ldrop$ (Enat$ )A_llist_llist_llist_llist_a_llist_llist_llist_llist_fun$ )
(declare-fun mcont$ (A_llist_llist_set_a_llist_llist_fun$ A_llist_llist_a_llist_llist_bool_fun_fun$ A_llist_set_a_llist_fun$ A_llist_a_llist_bool_fun_fun$ A_llist_llist_a_llist_fun$ )Bool )
(declare-fun ldrop$a (Enat$ )A_llist_llist_llist_a_llist_llist_llist_fun$ )
(declare-fun ldrop$b (Enat$ )A_llist_llist_a_llist_llist_fun$ )
(declare-fun ldrop$c (Enat$ )A_llist_a_llist_fun$ )
(declare-fun ldropn$ (Nat$ )A_llist_llist_llist_llist_a_llist_llist_llist_llist_fun$ )
(declare-fun mcont$a (A_llist_llist_llist_llist_set_a_llist_llist_llist_llist_fun$ A_llist_llist_llist_llist_a_llist_llist_llist_llist_bool_fun_fun$ A_llist_llist_llist_llist_set_a_llist_llist_llist_llist_fun$ A_llist_llist_llist_llist_a_llist_llist_llist_llist_bool_fun_fun$ A_llist_llist_llist_llist_a_llist_llist_llist_llist_fun$ )Bool )
(declare-fun mcont$b (A_llist_llist_llist_set_a_llist_llist_llist_fun$ A_llist_llist_llist_a_llist_llist_llist_bool_fun_fun$ A_llist_llist_llist_set_a_llist_llist_llist_fun$ A_llist_llist_llist_a_llist_llist_llist_bool_fun_fun$ A_llist_llist_llist_a_llist_llist_llist_fun$ )Bool )
(declare-fun mcont$c (A_llist_llist_set_a_llist_llist_fun$ A_llist_llist_a_llist_llist_bool_fun_fun$ A_llist_llist_set_a_llist_llist_fun$ A_llist_llist_a_llist_llist_bool_fun_fun$ A_llist_llist_a_llist_llist_fun$ )Bool )
(declare-fun mcont$d (A_llist_set_a_llist_fun$ A_llist_a_llist_bool_fun_fun$ A_llist_set_a_llist_fun$ A_llist_a_llist_bool_fun_fun$ A_llist_a_llist_fun$ )Bool )
(declare-fun fun_app$ (A_llist_llist_llist_llist_a_llist_llist_llist_llist_fun$ A_llist_llist_llist_llist$ )A_llist_llist_llist_llist$ )
(declare-fun lappend$ (A_llist_llist_llist_llist$ )A_llist_llist_llist_llist_a_llist_llist_llist_llist_fun$ )
(declare-fun lconcat$ ()A_llist_llist_a_llist_fun$ )
(declare-fun ldropn$a (Nat$ )A_llist_llist_llist_a_llist_llist_llist_fun$ )
(declare-fun ldropn$b (Nat$ )A_llist_llist_a_llist_llist_fun$ )
(declare-fun ldropn$c (Nat$ )A_llist_a_llist_fun$ )
(declare-fun lfilter$ (A_llist_llist_llist_bool_fun$ )A_llist_llist_llist_llist_a_llist_llist_llist_llist_fun$ )
(declare-fun lprefix$ ()A_llist_llist_a_llist_llist_bool_fun_fun$ )
(declare-fun fun_app$a (A_llist_llist_llist_a_llist_llist_llist_fun$ A_llist_llist_llist$ )A_llist_llist_llist$ )
(declare-fun fun_app$b (A_llist_llist_a_llist_llist_fun$ A_llist_llist$ )A_llist_llist$ )
(declare-fun fun_app$c (A_llist_a_llist_fun$ A_llist$ )A_llist$ )
(declare-fun fun_app$d (A_llist_llist_llist_llist_bool_fun$ A_llist_llist_llist_llist$ )Bool )
(declare-fun fun_app$e (A_llist_llist_llist_llist_a_llist_llist_llist_llist_bool_fun_fun$ A_llist_llist_llist_llist$ )A_llist_llist_llist_llist_bool_fun$ )
(declare-fun fun_app$f (A_llist_llist_llist_bool_fun$ A_llist_llist_llist$ )Bool )
(declare-fun fun_app$g (A_llist_llist_llist_a_llist_llist_llist_bool_fun_fun$ A_llist_llist_llist$ )A_llist_llist_llist_bool_fun$ )
(declare-fun fun_app$h (A_llist_llist_bool_fun$ A_llist_llist$ )Bool )
(declare-fun fun_app$i (A_llist_llist_a_llist_llist_bool_fun_fun$ A_llist_llist$ )A_llist_llist_bool_fun$ )
(declare-fun fun_app$j (A_llist_bool_fun$ A_llist$ )Bool )
(declare-fun fun_app$k (A_llist_a_llist_bool_fun_fun$ A_llist$ )A_llist_bool_fun$ )
(declare-fun fun_app$l (A_llist_llist_a_llist_fun$ A_llist_llist$ )A_llist$ )
(declare-fun lappend$a (A_llist_llist_llist$ )A_llist_llist_llist_a_llist_llist_llist_fun$ )
(declare-fun lappend$b (A_llist_llist$ )A_llist_llist_a_llist_llist_fun$ )
(declare-fun lappend$c (A_llist$ )A_llist_a_llist_fun$ )
(declare-fun lconcat$a ()A_llist_llist_llist_llist_llist_a_llist_llist_llist_llist_fun$ )
(declare-fun lconcat$b ()A_llist_llist_llist_llist_a_llist_llist_llist_fun$ )
(declare-fun lconcat$c ()A_llist_llist_llist_a_llist_llist_fun$ )
(declare-fun lfilter$a (A_llist_llist_bool_fun$ )A_llist_llist_llist_a_llist_llist_llist_fun$ )
(declare-fun lfilter$b (A_llist_bool_fun$ )A_llist_llist_a_llist_llist_fun$ )
(declare-fun lfilter$c (A_bool_fun$ )A_llist_a_llist_fun$ )
(declare-fun lprefix$a ()A_llist_a_llist_bool_fun_fun$ )
(declare-fun lprefix$b ()A_llist_llist_llist_llist_a_llist_llist_llist_llist_bool_fun_fun$ )
(declare-fun lprefix$c ()A_llist_llist_llist_a_llist_llist_llist_bool_fun_fun$ )
(declare-fun lprefix$d ()A_llist_llist_llist_llist_llist_a_llist_llist_llist_llist_llist_bool_fun_fun$ )
(declare-fun monotone$ (A_llist_llist_llist_llist_llist_a_llist_llist_llist_llist_llist_bool_fun_fun$ A_llist_llist_llist_llist_a_llist_llist_llist_llist_bool_fun_fun$ A_llist_llist_llist_llist_llist_a_llist_llist_llist_llist_fun$ )Bool )
(declare-fun monotone$a (A_llist_llist_llist_llist_a_llist_llist_llist_llist_bool_fun_fun$ A_llist_llist_llist_a_llist_llist_llist_bool_fun_fun$ A_llist_llist_llist_llist_a_llist_llist_llist_fun$ )Bool )
(declare-fun monotone$b (A_llist_llist_llist_a_llist_llist_llist_bool_fun_fun$ A_llist_llist_a_llist_llist_bool_fun_fun$ A_llist_llist_llist_a_llist_llist_fun$ )Bool )
(declare-fun monotone$c (A_llist_llist_a_llist_llist_bool_fun_fun$ A_llist_a_llist_bool_fun_fun$ A_llist_llist_a_llist_fun$ )Bool )
(declare-fun ldropWhile$ (A_llist_llist_llist_bool_fun$ )A_llist_llist_llist_llist_a_llist_llist_llist_llist_fun$ )
(declare-fun ltakeWhile$ (A_llist_llist_llist_bool_fun$ )A_llist_llist_llist_llist_a_llist_llist_llist_llist_fun$ )
(declare-fun ldropWhile$a (A_llist_llist_bool_fun$ )A_llist_llist_llist_a_llist_llist_llist_fun$ )
(declare-fun ldropWhile$b (A_llist_bool_fun$ )A_llist_llist_a_llist_llist_fun$ )
(declare-fun ldropWhile$c (A_bool_fun$ )A_llist_a_llist_fun$ )
(declare-fun ltakeWhile$a (A_llist_llist_bool_fun$ )A_llist_llist_llist_a_llist_llist_llist_fun$ )
(declare-fun ltakeWhile$b (A_llist_bool_fun$ )A_llist_llist_a_llist_llist_fun$ )
(declare-fun ltakeWhile$c (A_bool_fun$ )A_llist_a_llist_fun$ )
(assert (! (forall ((?v0 A_llist_llist_llist_llist$ ))(! (= (fun_app$ uud$ ?v0 )(ltl$c ?v0 )):pattern ((fun_app$ uud$ ?v0 )))):named a0 ))
(assert (! (forall ((?v0 A_llist_llist_llist$ ))(! (= (fun_app$a uue$ ?v0 )(ltl$b ?v0 )):pattern ((fun_app$a uue$ ?v0 )))):named a1 ))
(assert (! (forall ((?v0 A_llist_llist$ ))(! (= (fun_app$b uuf$ ?v0 )(ltl$a ?v0 )):pattern ((fun_app$b uuf$ ?v0 )))):named a2 ))
(assert (! (forall ((?v0 A_llist$ ))(! (= (fun_app$c uug$ ?v0 )(ltl$ ?v0 )):pattern ((fun_app$c uug$ ?v0 )))):named a3 ))
(assert (! (forall ((?v0 A_llist_llist_llist$ )(?v1 A_llist_llist_llist_llist$ ))(! (= (fun_app$ (uu$ ?v0 )?v1 )(lCons$c ?v0 ?v1 )):pattern ((fun_app$ (uu$ ?v0 )?v1 )))):named a4 ))
(assert (! (forall ((?v0 A_llist_llist$ )(?v1 A_llist_llist_llist$ ))(! (= (fun_app$a (uua$ ?v0 )?v1 )(lCons$b ?v0 ?v1 )):pattern ((fun_app$a (uua$ ?v0 )?v1 )))):named a5 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist_llist$ ))(! (= (fun_app$b (uub$ ?v0 )?v1 )(lCons$a ?v0 ?v1 )):pattern ((fun_app$b (uub$ ?v0 )?v1 )))):named a6 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(! (= (fun_app$c (uuc$ ?v0 )?v1 )(lCons$ ?v0 ?v1 )):pattern ((fun_app$c (uuc$ ?v0 )?v1 )))):named a7 ))
(assert (! (not (mcont$ lSup$ lprefix$ lSup$a lprefix$a lconcat$ )):named a8 ))
(assert (! (forall ((?v0 A_llist_llist_llist_llist$ ))(fun_app$d (fun_app$e lprefix$b ?v0 )?v0 )):named a9 ))
(assert (! (forall ((?v0 A_llist_llist_llist$ ))(fun_app$f (fun_app$g lprefix$c ?v0 )?v0 )):named a10 ))
(assert (! (forall ((?v0 A_llist_llist$ ))(fun_app$h (fun_app$i lprefix$ ?v0 )?v0 )):named a11 ))
(assert (! (forall ((?v0 A_llist$ ))(fun_app$j (fun_app$k lprefix$a ?v0 )?v0 )):named a12 ))
(assert (! (forall ((?v0 A_llist_llist_llist_llist$ ))(fun_app$d (fun_app$e lprefix$b ?v0 )?v0 )):named a13 ))
(assert (! (forall ((?v0 A_llist_llist_llist$ ))(fun_app$f (fun_app$g lprefix$c ?v0 )?v0 )):named a14 ))
(assert (! (forall ((?v0 A_llist_llist$ ))(fun_app$h (fun_app$i lprefix$ ?v0 )?v0 )):named a15 ))
(assert (! (forall ((?v0 A_llist$ ))(fun_app$j (fun_app$k lprefix$a ?v0 )?v0 )):named a16 ))
(assert (! (forall ((?v0 A_llist_llist_llist_llist$ )(?v1 A_llist_llist_llist_llist$ ))(=> (and (fun_app$d (fun_app$e lprefix$b ?v0 )?v1 )(fun_app$d (fun_app$e lprefix$b ?v1 )?v0 ))(= ?v0 ?v1 ))):named a17 ))
(assert (! (forall ((?v0 A_llist_llist_llist$ )(?v1 A_llist_llist_llist$ ))(=> (and (fun_app$f (fun_app$g lprefix$c ?v0 )?v1 )(fun_app$f (fun_app$g lprefix$c ?v1 )?v0 ))(= ?v0 ?v1 ))):named a18 ))
(assert (! (forall ((?v0 A_llist_llist$ )(?v1 A_llist_llist$ ))(=> (and (fun_app$h (fun_app$i lprefix$ ?v0 )?v1 )(fun_app$h (fun_app$i lprefix$ ?v1 )?v0 ))(= ?v0 ?v1 ))):named a19 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (and (fun_app$j (fun_app$k lprefix$a ?v0 )?v1 )(fun_app$j (fun_app$k lprefix$a ?v1 )?v0 ))(= ?v0 ?v1 ))):named a20 ))
(assert (! (forall ((?v0 A_llist_llist_llist_llist$ )(?v1 A_llist_llist_llist_llist$ ))(=> (and (fun_app$d (fun_app$e lprefix$b ?v0 )?v1 )(fun_app$d (fun_app$e lprefix$b ?v1 )?v0 ))(= ?v0 ?v1 ))):named a21 ))
(assert (! (forall ((?v0 A_llist_llist_llist$ )(?v1 A_llist_llist_llist$ ))(=> (and (fun_app$f (fun_app$g lprefix$c ?v0 )?v1 )(fun_app$f (fun_app$g lprefix$c ?v1 )?v0 ))(= ?v0 ?v1 ))):named a22 ))
(assert (! (forall ((?v0 A_llist_llist$ )(?v1 A_llist_llist$ ))(=> (and (fun_app$h (fun_app$i lprefix$ ?v0 )?v1 )(fun_app$h (fun_app$i lprefix$ ?v1 )?v0 ))(= ?v0 ?v1 ))):named a23 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (and (fun_app$j (fun_app$k lprefix$a ?v0 )?v1 )(fun_app$j (fun_app$k lprefix$a ?v1 )?v0 ))(= ?v0 ?v1 ))):named a24 ))
(assert (! (forall ((?v0 A_llist_llist_llist_llist$ )(?v1 A_llist_llist_llist_llist$ )(?v2 A_llist_llist_llist_llist$ ))(=> (and (fun_app$d (fun_app$e lprefix$b ?v0 )?v1 )(fun_app$d (fun_app$e lprefix$b ?v2 )?v1 ))(or (fun_app$d (fun_app$e lprefix$b ?v0 )?v2 )(fun_app$d (fun_app$e lprefix$b ?v2 )?v0 )))):named a25 ))
(assert (! (forall ((?v0 A_llist_llist_llist$ )(?v1 A_llist_llist_llist$ )(?v2 A_llist_llist_llist$ ))(=> (and (fun_app$f (fun_app$g lprefix$c ?v0 )?v1 )(fun_app$f (fun_app$g lprefix$c ?v2 )?v1 ))(or (fun_app$f (fun_app$g lprefix$c ?v0 )?v2 )(fun_app$f (fun_app$g lprefix$c ?v2 )?v0 )))):named a26 ))
(assert (! (forall ((?v0 A_llist_llist$ )(?v1 A_llist_llist$ )(?v2 A_llist_llist$ ))(=> (and (fun_app$h (fun_app$i lprefix$ ?v0 )?v1 )(fun_app$h (fun_app$i lprefix$ ?v2 )?v1 ))(or (fun_app$h (fun_app$i lprefix$ ?v0 )?v2 )(fun_app$h (fun_app$i lprefix$ ?v2 )?v0 )))):named a27 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(=> (and (fun_app$j (fun_app$k lprefix$a ?v0 )?v1 )(fun_app$j (fun_app$k lprefix$a ?v2 )?v1 ))(or (fun_app$j (fun_app$k lprefix$a ?v0 )?v2 )(fun_app$j (fun_app$k lprefix$a ?v2 )?v0 )))):named a28 ))
(assert (! (forall ((?v0 A_llist_llist_llist_llist$ )(?v1 A_llist_llist_llist_llist$ )(?v2 A_llist_llist_llist_llist$ ))(=> (and (fun_app$d (fun_app$e lprefix$b ?v0 )?v1 )(fun_app$d (fun_app$e lprefix$b ?v1 )?v2 ))(fun_app$d (fun_app$e lprefix$b ?v0 )?v2 ))):named a29 ))
(assert (! (forall ((?v0 A_llist_llist_llist$ )(?v1 A_llist_llist_llist$ )(?v2 A_llist_llist_llist$ ))(=> (and (fun_app$f (fun_app$g lprefix$c ?v0 )?v1 )(fun_app$f (fun_app$g lprefix$c ?v1 )?v2 ))(fun_app$f (fun_app$g lprefix$c ?v0 )?v2 ))):named a30 ))
(assert (! (forall ((?v0 A_llist_llist$ )(?v1 A_llist_llist$ )(?v2 A_llist_llist$ ))(=> (and (fun_app$h (fun_app$i lprefix$ ?v0 )?v1 )(fun_app$h (fun_app$i lprefix$ ?v1 )?v2 ))(fun_app$h (fun_app$i lprefix$ ?v0 )?v2 ))):named a31 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(=> (and (fun_app$j (fun_app$k lprefix$a ?v0 )?v1 )(fun_app$j (fun_app$k lprefix$a ?v1 )?v2 ))(fun_app$j (fun_app$k lprefix$a ?v0 )?v2 ))):named a32 ))
(assert (! (forall ((?v0 A_llist_llist_llist_llist$ )(?v1 A_llist_llist_llist_llist$ )(?v2 A_llist_llist_llist_llist$ ))(=> (and (fun_app$d (fun_app$e lprefix$b ?v0 )?v1 )(fun_app$d (fun_app$e lprefix$b ?v1 )?v2 ))(fun_app$d (fun_app$e lprefix$b ?v0 )?v2 ))):named a33 ))
(assert (! (forall ((?v0 A_llist_llist_llist$ )(?v1 A_llist_llist_llist$ )(?v2 A_llist_llist_llist$ ))(=> (and (fun_app$f (fun_app$g lprefix$c ?v0 )?v1 )(fun_app$f (fun_app$g lprefix$c ?v1 )?v2 ))(fun_app$f (fun_app$g lprefix$c ?v0 )?v2 ))):named a34 ))
(assert (! (forall ((?v0 A_llist_llist$ )(?v1 A_llist_llist$ )(?v2 A_llist_llist$ ))(=> (and (fun_app$h (fun_app$i lprefix$ ?v0 )?v1 )(fun_app$h (fun_app$i lprefix$ ?v1 )?v2 ))(fun_app$h (fun_app$i lprefix$ ?v0 )?v2 ))):named a35 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(=> (and (fun_app$j (fun_app$k lprefix$a ?v0 )?v1 )(fun_app$j (fun_app$k lprefix$a ?v1 )?v2 ))(fun_app$j (fun_app$k lprefix$a ?v0 )?v2 ))):named a36 ))
(assert (! (monotone$ lprefix$d lprefix$b lconcat$a ):named a37 ))
(assert (! (monotone$a lprefix$b lprefix$c lconcat$b ):named a38 ))
(assert (! (monotone$b lprefix$c lprefix$ lconcat$c ):named a39 ))
(assert (! (monotone$c lprefix$ lprefix$a lconcat$ ):named a40 ))
(assert (! (forall ((?v0 A_llist_llist_llist_bool_fun$ ))(mcont$a lSup$b lprefix$b lSup$b lprefix$b (ldropWhile$ ?v0 ))):named a41 ))
(assert (! (forall ((?v0 A_llist_llist_bool_fun$ ))(mcont$b lSup$c lprefix$c lSup$c lprefix$c (ldropWhile$a ?v0 ))):named a42 ))
(assert (! (forall ((?v0 A_llist_bool_fun$ ))(mcont$c lSup$ lprefix$ lSup$ lprefix$ (ldropWhile$b ?v0 ))):named a43 ))
(assert (! (forall ((?v0 A_bool_fun$ ))(mcont$d lSup$a lprefix$a lSup$a lprefix$a (ldropWhile$c ?v0 ))):named a44 ))
(assert (! (forall ((?v0 Nat$ ))(mcont$a lSup$b lprefix$b lSup$b lprefix$b (ldropn$ ?v0 ))):named a45 ))
(assert (! (forall ((?v0 Nat$ ))(mcont$b lSup$c lprefix$c lSup$c lprefix$c (ldropn$a ?v0 ))):named a46 ))
(assert (! (forall ((?v0 Nat$ ))(mcont$c lSup$ lprefix$ lSup$ lprefix$ (ldropn$b ?v0 ))):named a47 ))
(assert (! (forall ((?v0 Nat$ ))(mcont$d lSup$a lprefix$a lSup$a lprefix$a (ldropn$c ?v0 ))):named a48 ))
(assert (! (forall ((?v0 Enat$ ))(mcont$a lSup$b lprefix$b lSup$b lprefix$b (ldrop$ ?v0 ))):named a49 ))
(assert (! (forall ((?v0 Enat$ ))(mcont$b lSup$c lprefix$c lSup$c lprefix$c (ldrop$a ?v0 ))):named a50 ))
(assert (! (forall ((?v0 Enat$ ))(mcont$c lSup$ lprefix$ lSup$ lprefix$ (ldrop$b ?v0 ))):named a51 ))
(assert (! (forall ((?v0 Enat$ ))(mcont$d lSup$a lprefix$a lSup$a lprefix$a (ldrop$c ?v0 ))):named a52 ))
(assert (! (forall ((?v0 A_llist_llist_llist_set_a_llist_llist_llist_fun$ )(?v1 A_llist_llist_llist_a_llist_llist_llist_bool_fun_fun$ )(?v2 A_llist_llist_llist_set_a_llist_llist_llist_fun$ )(?v3 A_llist_llist_llist_a_llist_llist_llist_bool_fun_fun$ )(?v4 A_llist_llist_llist_a_llist_llist_llist_fun$ )(?v5 A_llist_llist_llist$ )(?v6 A_llist_llist_llist$ ))(=> (and (mcont$b ?v0 ?v1 ?v2 ?v3 ?v4 )(fun_app$f (fun_app$g ?v1 ?v5 )?v6 ))(fun_app$f (fun_app$g ?v3 (fun_app$a ?v4 ?v5 ))(fun_app$a ?v4 ?v6 )))):named a53 ))
(assert (! (forall ((?v0 A_llist_set_a_llist_fun$ )(?v1 A_llist_a_llist_bool_fun_fun$ )(?v2 A_llist_set_a_llist_fun$ )(?v3 A_llist_a_llist_bool_fun_fun$ )(?v4 A_llist_a_llist_fun$ )(?v5 A_llist$ )(?v6 A_llist$ ))(=> (and (mcont$d ?v0 ?v1 ?v2 ?v3 ?v4 )(fun_app$j (fun_app$k ?v1 ?v5 )?v6 ))(fun_app$j (fun_app$k ?v3 (fun_app$c ?v4 ?v5 ))(fun_app$c ?v4 ?v6 )))):named a54 ))
(assert (! (forall ((?v0 A_llist_llist_set_a_llist_llist_fun$ )(?v1 A_llist_llist_a_llist_llist_bool_fun_fun$ )(?v2 A_llist_llist_set_a_llist_llist_fun$ )(?v3 A_llist_llist_a_llist_llist_bool_fun_fun$ )(?v4 A_llist_llist_a_llist_llist_fun$ )(?v5 A_llist_llist$ )(?v6 A_llist_llist$ ))(=> (and (mcont$c ?v0 ?v1 ?v2 ?v3 ?v4 )(fun_app$h (fun_app$i ?v1 ?v5 )?v6 ))(fun_app$h (fun_app$i ?v3 (fun_app$b ?v4 ?v5 ))(fun_app$b ?v4 ?v6 )))):named a55 ))
(assert (! (forall ((?v0 A_llist_llist_set_a_llist_llist_fun$ )(?v1 A_llist_llist_a_llist_llist_bool_fun_fun$ )(?v2 A_llist_set_a_llist_fun$ )(?v3 A_llist_a_llist_bool_fun_fun$ )(?v4 A_llist_llist_a_llist_fun$ )(?v5 A_llist_llist$ )(?v6 A_llist_llist$ ))(=> (and (mcont$ ?v0 ?v1 ?v2 ?v3 ?v4 )(fun_app$h (fun_app$i ?v1 ?v5 )?v6 ))(fun_app$j (fun_app$k ?v3 (fun_app$l ?v4 ?v5 ))(fun_app$l ?v4 ?v6 )))):named a56 ))
(assert (! (forall ((?v0 A_llist_llist_llist$ ))(mcont$a lSup$b lprefix$b lSup$b lprefix$b (uu$ ?v0 ))):named a57 ))
(assert (! (forall ((?v0 A_llist_llist$ ))(mcont$b lSup$c lprefix$c lSup$c lprefix$c (uua$ ?v0 ))):named a58 ))
(assert (! (forall ((?v0 A_llist$ ))(mcont$c lSup$ lprefix$ lSup$ lprefix$ (uub$ ?v0 ))):named a59 ))
(assert (! (forall ((?v0 A$ ))(mcont$d lSup$a lprefix$a lSup$a lprefix$a (uuc$ ?v0 ))):named a60 ))
(assert (! (forall ((?v0 A_llist_llist_llist_bool_fun$ ))(mcont$a lSup$b lprefix$b lSup$b lprefix$b (lfilter$ ?v0 ))):named a61 ))
(assert (! (forall ((?v0 A_llist_llist_bool_fun$ ))(mcont$b lSup$c lprefix$c lSup$c lprefix$c (lfilter$a ?v0 ))):named a62 ))
(assert (! (forall ((?v0 A_llist_bool_fun$ ))(mcont$c lSup$ lprefix$ lSup$ lprefix$ (lfilter$b ?v0 ))):named a63 ))
(assert (! (forall ((?v0 A_bool_fun$ ))(mcont$d lSup$a lprefix$a lSup$a lprefix$a (lfilter$c ?v0 ))):named a64 ))
(assert (! (forall ((?v0 A_llist_llist_llist_bool_fun$ ))(mcont$a lSup$b lprefix$b lSup$b lprefix$b (ltakeWhile$ ?v0 ))):named a65 ))
(assert (! (forall ((?v0 A_llist_llist_bool_fun$ ))(mcont$b lSup$c lprefix$c lSup$c lprefix$c (ltakeWhile$a ?v0 ))):named a66 ))
(assert (! (forall ((?v0 A_llist_bool_fun$ ))(mcont$c lSup$ lprefix$ lSup$ lprefix$ (ltakeWhile$b ?v0 ))):named a67 ))
(assert (! (forall ((?v0 A_bool_fun$ ))(mcont$d lSup$a lprefix$a lSup$a lprefix$a (ltakeWhile$c ?v0 ))):named a68 ))
(assert (! (mcont$a lSup$b lprefix$b lSup$b lprefix$b uud$ ):named a69 ))
(assert (! (mcont$b lSup$c lprefix$c lSup$c lprefix$c uue$ ):named a70 ))
(assert (! (mcont$c lSup$ lprefix$ lSup$ lprefix$ uuf$ ):named a71 ))
(assert (! (mcont$d lSup$a lprefix$a lSup$a lprefix$a uug$ ):named a72 ))
(assert (! (forall ((?v0 A_llist_llist_llist_llist$ ))(mcont$a lSup$b lprefix$b lSup$b lprefix$b (lappend$ ?v0 ))):named a73 ))
(assert (! (forall ((?v0 A_llist_llist_llist$ ))(mcont$b lSup$c lprefix$c lSup$c lprefix$c (lappend$a ?v0 ))):named a74 ))
(assert (! (forall ((?v0 A_llist_llist$ ))(mcont$c lSup$ lprefix$ lSup$ lprefix$ (lappend$b ?v0 ))):named a75 ))
(assert (! (forall ((?v0 A_llist$ ))(mcont$d lSup$a lprefix$a lSup$a lprefix$a (lappend$c ?v0 ))):named a76 ))
(check-sat )
;(get-unsat-core )
