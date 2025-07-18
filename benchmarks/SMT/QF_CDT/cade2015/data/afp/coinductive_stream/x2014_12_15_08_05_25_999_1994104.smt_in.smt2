;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort A_llist_set$ 0 )
(declare-sort A_a_bool_fun_fun$ 0 )
(declare-sort A_a_prod_bool_fun$ 0 )
(declare-sort A_a_prod_llist_set$ 0 )
(declare-sort A_a_a_prod_prod_llist_set$ 0 )
(declare-sort A_a_prod_a_prod_llist_set$ 0 )
(declare-sort A_a_prod_a_a_prod_bool_fun_fun$ 0 )
(declare-sort A_a_prod_a_a_prod_prod_llist_set$ 0 )
(declare-sort A_a_a_prod_prod_a_a_a_prod_prod_bool_fun_fun$ 0 )
(declare-sort A_a_prod_a_prod_a_a_prod_a_prod_bool_fun_fun$ 0 )
(declare-sort A_a_prod_a_a_prod_prod_a_a_prod_a_a_prod_prod_bool_fun_fun$ 0 )
(declare-sort A_llist$ 0)
(declare-sort A_stream$ 0)
(declare-fun lNil$ ()A_llist$)
(declare-fun lhd$ (A_llist$)A$)
(declare-fun ltl$ (A_llist$)A_llist$)
(declare-fun lCons$ (A$ A_llist$ )A_llist$)
(declare-fun shd$ (A_stream$)A$)
(declare-fun stl$ (A_stream$)A_stream$)
(declare-fun sCons$ (A$ A_stream$ )A_stream$)
(declare-datatypes ()((A_a_prod$ (pair$ (fst$ A$ )(snd$ A$ )))))
(declare-sort A_a_prod_llist$ 0)
(declare-fun lNil$a ()A_a_prod_llist$)
(declare-fun lhd$a (A_a_prod_llist$)A_a_prod$)
(declare-fun ltl$a (A_a_prod_llist$)A_a_prod_llist$)
(declare-fun lCons$a (A_a_prod$ A_a_prod_llist$ )A_a_prod_llist$)
(declare-datatypes ()((A_a_prod_a_prod$ (pair$a (fst$a A_a_prod$ )(snd$a A$ )))))
(declare-sort A_a_prod_a_prod_llist$ 0)
(declare-fun lNil$b ()A_a_prod_a_prod_llist$)
(declare-fun lhd$b (A_a_prod_a_prod_llist$)A_a_prod_a_prod$)
(declare-fun ltl$b (A_a_prod_a_prod_llist$)A_a_prod_a_prod_llist$)
(declare-fun lCons$b (A_a_prod_a_prod$ A_a_prod_a_prod_llist$ )A_a_prod_a_prod_llist$)
(declare-datatypes ()((A_a_a_prod_prod$ (pair$b (fst$b A$ )(snd$b A_a_prod$ )))))
(declare-sort A_a_a_prod_prod_llist$ 0)
(declare-fun lNil$c ()A_a_a_prod_prod_llist$)
(declare-fun lhd$c (A_a_a_prod_prod_llist$)A_a_a_prod_prod$)
(declare-fun ltl$c (A_a_a_prod_prod_llist$)A_a_a_prod_prod_llist$)
(declare-fun lCons$c (A_a_a_prod_prod$ A_a_a_prod_prod_llist$ )A_a_a_prod_prod_llist$)
(declare-datatypes ()((A_a_prod_a_a_prod_prod$ (pair$c (fst$c A_a_prod$ )(snd$c A_a_prod$ )))))
(declare-sort A_a_prod_a_a_prod_prod_llist$ 0)
(declare-fun lNil$d ()A_a_prod_a_a_prod_prod_llist$)
(declare-fun lhd$d (A_a_prod_a_a_prod_prod_llist$)A_a_prod_a_a_prod_prod$)
(declare-fun ltl$d (A_a_prod_a_a_prod_prod_llist$)A_a_prod_a_a_prod_prod_llist$)
(declare-fun lCons$d (A_a_prod_a_a_prod_prod$ A_a_prod_a_a_prod_prod_llist$ )A_a_prod_a_a_prod_prod_llist$)
(declare-datatypes ()((A_a_a_prod_a_prod_prod$ (pair$d (fst$d A$ )(snd$d A_a_prod_a_prod$ )))))
(declare-sort A_a_a_prod_a_prod_prod_llist$ 0)
(declare-fun lNil$e ()A_a_a_prod_a_prod_prod_llist$)
(declare-fun lhd$e (A_a_a_prod_a_prod_prod_llist$)A_a_a_prod_a_prod_prod$)
(declare-fun ltl$e (A_a_a_prod_a_prod_prod_llist$)A_a_a_prod_a_prod_prod_llist$)
(declare-fun lCons$e (A_a_a_prod_a_prod_prod$ A_a_a_prod_a_prod_prod_llist$ )A_a_a_prod_a_prod_prod_llist$)
(declare-datatypes ()((A_a_a_a_prod_prod_prod$ (pair$e (fst$e A$ )(snd$e A_a_a_prod_prod$ )))))
(declare-sort A_a_a_a_prod_prod_prod_llist$ 0)
(declare-fun lNil$f ()A_a_a_a_prod_prod_prod_llist$)
(declare-fun lhd$f (A_a_a_a_prod_prod_prod_llist$)A_a_a_a_prod_prod_prod$)
(declare-fun ltl$f (A_a_a_a_prod_prod_prod_llist$)A_a_a_a_prod_prod_prod_llist$)
(declare-fun lCons$f (A_a_a_a_prod_prod_prod$ A_a_a_a_prod_prod_prod_llist$ )A_a_a_a_prod_prod_prod_llist$)
(declare-datatypes ()((A_a_prod_a_prod_a_prod$ (pair$f (fst$f A_a_prod_a_prod$ )(snd$f A$ )))))
(declare-sort A_a_prod_a_prod_a_prod_llist$ 0)
(declare-fun lNil$g ()A_a_prod_a_prod_a_prod_llist$)
(declare-fun lhd$g (A_a_prod_a_prod_a_prod_llist$)A_a_prod_a_prod_a_prod$)
(declare-fun ltl$g (A_a_prod_a_prod_a_prod_llist$)A_a_prod_a_prod_a_prod_llist$)
(declare-fun lCons$g (A_a_prod_a_prod_a_prod$ A_a_prod_a_prod_a_prod_llist$ )A_a_prod_a_prod_a_prod_llist$)
(declare-datatypes ()((A_a_a_prod_prod_a_prod$ (pair$g (fst$g A_a_a_prod_prod$ )(snd$g A$ )))))
(declare-sort A_a_a_prod_prod_a_prod_llist$ 0)
(declare-fun lNil$h ()A_a_a_prod_prod_a_prod_llist$)
(declare-fun lhd$h (A_a_a_prod_prod_a_prod_llist$)A_a_a_prod_prod_a_prod$)
(declare-fun ltl$h (A_a_a_prod_prod_a_prod_llist$)A_a_a_prod_prod_a_prod_llist$)
(declare-fun lCons$h (A_a_a_prod_prod_a_prod$ A_a_a_prod_prod_a_prod_llist$ )A_a_a_prod_prod_a_prod_llist$)
(declare-datatypes ()((A_a_a_prod_a_a_prod_prod_prod$ (pair$h (fst$h A$ )(snd$h A_a_prod_a_a_prod_prod$ )))))
(declare-sort A_a_a_prod_a_a_prod_prod_prod_llist$ 0)
(declare-fun lNil$i ()A_a_a_prod_a_a_prod_prod_prod_llist$)
(declare-fun lhd$i (A_a_a_prod_a_a_prod_prod_prod_llist$)A_a_a_prod_a_a_prod_prod_prod$)
(declare-fun ltl$i (A_a_a_prod_a_a_prod_prod_prod_llist$)A_a_a_prod_a_a_prod_prod_prod_llist$)
(declare-fun lCons$i (A_a_a_prod_a_a_prod_prod_prod$ A_a_a_prod_a_a_prod_prod_prod_llist$ )A_a_a_prod_a_a_prod_prod_prod_llist$)
(declare-datatypes ()((A_a_prod_a_a_prod_a_prod_prod$ (pair$i (fst$i A_a_prod$ )(snd$i A_a_prod_a_prod$ )))))
(declare-sort A_a_prod_a_a_prod_a_prod_prod_llist$ 0)
(declare-fun lNil$j ()A_a_prod_a_a_prod_a_prod_prod_llist$)
(declare-fun lhd$j (A_a_prod_a_a_prod_a_prod_prod_llist$)A_a_prod_a_a_prod_a_prod_prod$)
(declare-fun ltl$j (A_a_prod_a_a_prod_a_prod_prod_llist$)A_a_prod_a_a_prod_a_prod_prod_llist$)
(declare-fun lCons$j (A_a_prod_a_a_prod_a_prod_prod$ A_a_prod_a_a_prod_a_prod_prod_llist$ )A_a_prod_a_a_prod_a_prod_prod_llist$)
(declare-fun xs$ ()A_stream$ )
(declare-fun lzip$ (A_llist$ A_llist$ )A_a_prod_llist$ )
(declare-fun lnull$ (A_llist$ )Bool )
(declare-fun lzip$a (A_llist$ A_a_prod_llist$ )A_a_a_prod_prod_llist$ )
(declare-fun lzip$b (A_a_prod_llist$ A_llist$ )A_a_prod_a_prod_llist$ )
(declare-fun lzip$c (A_a_prod_llist$ A_a_prod_llist$ )A_a_prod_a_a_prod_prod_llist$ )
(declare-fun lzip$d (A_llist$ A_a_prod_a_prod_llist$ )A_a_a_prod_a_prod_prod_llist$ )
(declare-fun lzip$e (A_llist$ A_a_a_prod_prod_llist$ )A_a_a_a_prod_prod_prod_llist$ )
(declare-fun lzip$f (A_a_prod_a_prod_llist$ A_llist$ )A_a_prod_a_prod_a_prod_llist$ )
(declare-fun lzip$g (A_a_a_prod_prod_llist$ A_llist$ )A_a_a_prod_prod_a_prod_llist$ )
(declare-fun lzip$h (A_llist$ A_a_prod_a_a_prod_prod_llist$ )A_a_a_prod_a_a_prod_prod_prod_llist$ )
(declare-fun lzip$i (A_a_prod_llist$ A_a_prod_a_prod_llist$ )A_a_prod_a_a_prod_a_prod_prod_llist$ )
(declare-fun lnull$a (A_a_prod_llist$ )Bool )
(declare-fun lnull$b (A_a_prod_a_prod_llist$ )Bool )
(declare-fun lnull$c (A_a_a_prod_prod_llist$ )Bool )
(declare-fun lnull$d (A_a_prod_a_a_prod_prod_llist$ )Bool )
(declare-fun lnull$e (A_a_a_prod_a_prod_prod_llist$ )Bool )
(declare-fun lnull$f (A_a_a_a_prod_prod_prod_llist$ )Bool )
(declare-fun lnull$g (A_a_prod_a_prod_a_prod_llist$ )Bool )
(declare-fun lnull$h (A_a_a_prod_prod_a_prod_llist$ )Bool )
(declare-fun lnull$i (A_a_a_prod_a_a_prod_prod_prod_llist$ )Bool )
(declare-fun lnull$j (A_a_prod_a_a_prod_a_prod_prod_llist$ )Bool )
(declare-fun member$ (A_a_prod_a_a_prod_prod_llist$ A_a_prod_a_a_prod_prod_llist_set$ )Bool )
(declare-fun fun_app$ (A_a_prod_bool_fun$ A_a_prod$ )Bool )
(declare-fun llexord$ (A_a_prod_a_a_prod_prod_a_a_prod_a_a_prod_prod_bool_fun_fun$ A_a_prod_a_a_prod_prod_llist$ A_a_prod_a_a_prod_prod_llist$ )Bool )
(declare-fun member$a (A_a_prod_a_prod_llist$ A_a_prod_a_prod_llist_set$ )Bool )
(declare-fun member$b (A_a_a_prod_prod_llist$ A_a_a_prod_prod_llist_set$ )Bool )
(declare-fun member$c (A_a_prod_llist$ A_a_prod_llist_set$ )Bool )
(declare-fun member$d (A_llist$ A_llist_set$ )Bool )
(declare-fun fun_app$a (A_a_prod_a_a_prod_bool_fun_fun$ A_a_prod$ )A_a_prod_bool_fun$ )
(declare-fun fun_app$b (A_bool_fun$ A$ )Bool )
(declare-fun fun_app$c (A_a_bool_fun_fun$ A$ )A_bool_fun$ )
(declare-fun llexord$a (A_a_prod_a_prod_a_a_prod_a_prod_bool_fun_fun$ A_a_prod_a_prod_llist$ A_a_prod_a_prod_llist$ )Bool )
(declare-fun llexord$b (A_a_a_prod_prod_a_a_a_prod_prod_bool_fun_fun$ A_a_a_prod_prod_llist$ A_a_a_prod_prod_llist$ )Bool )
(declare-fun llexord$c (A_a_prod_a_a_prod_bool_fun_fun$ A_a_prod_llist$ A_a_prod_llist$ )Bool )
(declare-fun llexord$d (A_a_bool_fun_fun$ A_llist$ A_llist$ )Bool )
(declare-fun llist_of_stream$ (A_stream$ )A_llist$ )
(assert (! (not (not (lnull$ (llist_of_stream$ xs$ )))):named a0 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (and (=> (or (lnull$ ?v0 )(lnull$ ?v1 ))false )(=> (and (not (lnull$ ?v0 ))(not (lnull$ ?v1 )))false ))false )):named a1 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_a_prod_llist$ ))(=> (and (=> (or (lnull$ ?v0 )(lnull$a ?v1 ))false )(=> (and (not (lnull$ ?v0 ))(not (lnull$a ?v1 )))false ))false )):named a2 ))
(assert (! (forall ((?v0 A_a_prod_llist$ )(?v1 A_llist$ ))(=> (and (=> (or (lnull$a ?v0 )(lnull$ ?v1 ))false )(=> (and (not (lnull$a ?v0 ))(not (lnull$ ?v1 )))false ))false )):named a3 ))
(assert (! (forall ((?v0 A_a_prod_llist$ )(?v1 A_a_prod_llist$ ))(=> (and (=> (or (lnull$a ?v0 )(lnull$a ?v1 ))false )(=> (and (not (lnull$a ?v0 ))(not (lnull$a ?v1 )))false ))false )):named a4 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_a_prod_a_prod_llist$ ))(=> (and (=> (or (lnull$ ?v0 )(lnull$b ?v1 ))false )(=> (and (not (lnull$ ?v0 ))(not (lnull$b ?v1 )))false ))false )):named a5 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_a_a_prod_prod_llist$ ))(=> (and (=> (or (lnull$ ?v0 )(lnull$c ?v1 ))false )(=> (and (not (lnull$ ?v0 ))(not (lnull$c ?v1 )))false ))false )):named a6 ))
(assert (! (forall ((?v0 A_a_prod_a_prod_llist$ )(?v1 A_llist$ ))(=> (and (=> (or (lnull$b ?v0 )(lnull$ ?v1 ))false )(=> (and (not (lnull$b ?v0 ))(not (lnull$ ?v1 )))false ))false )):named a7 ))
(assert (! (forall ((?v0 A_a_a_prod_prod_llist$ )(?v1 A_llist$ ))(=> (and (=> (or (lnull$c ?v0 )(lnull$ ?v1 ))false )(=> (and (not (lnull$c ?v0 ))(not (lnull$ ?v1 )))false ))false )):named a8 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_a_prod_a_a_prod_prod_llist$ ))(=> (and (=> (or (lnull$ ?v0 )(lnull$d ?v1 ))false )(=> (and (not (lnull$ ?v0 ))(not (lnull$d ?v1 )))false ))false )):named a9 ))
(assert (! (forall ((?v0 A_a_prod_llist$ )(?v1 A_a_prod_a_prod_llist$ ))(=> (and (=> (or (lnull$a ?v0 )(lnull$b ?v1 ))false )(=> (and (not (lnull$a ?v0 ))(not (lnull$b ?v1 )))false ))false )):named a10 ))
(assert (! (forall ((?v0 A_a_prod_a_a_prod_prod_llist_set$ ))(=> (and (=> (forall ((?v1 A_a_prod_a_a_prod_prod_llist$ ))(=> (member$ ?v1 ?v0 )(lnull$d ?v1 )))false )(=> (not (forall ((?v1 A_a_prod_a_a_prod_prod_llist$ ))(=> (member$ ?v1 ?v0 )(lnull$d ?v1 ))))false ))false )):named a11 ))
(assert (! (forall ((?v0 A_a_prod_a_prod_llist_set$ ))(=> (and (=> (forall ((?v1 A_a_prod_a_prod_llist$ ))(=> (member$a ?v1 ?v0 )(lnull$b ?v1 )))false )(=> (not (forall ((?v1 A_a_prod_a_prod_llist$ ))(=> (member$a ?v1 ?v0 )(lnull$b ?v1 ))))false ))false )):named a12 ))
(assert (! (forall ((?v0 A_a_a_prod_prod_llist_set$ ))(=> (and (=> (forall ((?v1 A_a_a_prod_prod_llist$ ))(=> (member$b ?v1 ?v0 )(lnull$c ?v1 )))false )(=> (not (forall ((?v1 A_a_a_prod_prod_llist$ ))(=> (member$b ?v1 ?v0 )(lnull$c ?v1 ))))false ))false )):named a13 ))
(assert (! (forall ((?v0 A_a_prod_llist_set$ ))(=> (and (=> (forall ((?v1 A_a_prod_llist$ ))(=> (member$c ?v1 ?v0 )(lnull$a ?v1 )))false )(=> (not (forall ((?v1 A_a_prod_llist$ ))(=> (member$c ?v1 ?v0 )(lnull$a ?v1 ))))false ))false )):named a14 ))
(assert (! (forall ((?v0 A_llist_set$ ))(=> (and (=> (forall ((?v1 A_llist$ ))(=> (member$d ?v1 ?v0 )(lnull$ ?v1 )))false )(=> (not (forall ((?v1 A_llist$ ))(=> (member$d ?v1 ?v0 )(lnull$ ?v1 ))))false ))false )):named a15 ))
(assert (! (forall ((?v0 A_a_prod_a_a_prod_prod_llist$ )(?v1 A_a_prod_a_a_prod_prod_llist$ ))(=> (and (=> (and (lnull$d ?v0 )(lnull$d ?v1 ))false )(=> (or (not (lnull$d ?v0 ))(not (lnull$d ?v1 )))false ))false )):named a16 ))
(assert (! (forall ((?v0 A_a_prod_a_prod_llist$ )(?v1 A_a_prod_a_prod_llist$ ))(=> (and (=> (and (lnull$b ?v0 )(lnull$b ?v1 ))false )(=> (or (not (lnull$b ?v0 ))(not (lnull$b ?v1 )))false ))false )):named a17 ))
(assert (! (forall ((?v0 A_a_a_prod_prod_llist$ )(?v1 A_a_a_prod_prod_llist$ ))(=> (and (=> (and (lnull$c ?v0 )(lnull$c ?v1 ))false )(=> (or (not (lnull$c ?v0 ))(not (lnull$c ?v1 )))false ))false )):named a18 ))
(assert (! (forall ((?v0 A_a_prod_llist$ )(?v1 A_a_prod_llist$ ))(=> (and (=> (and (lnull$a ?v0 )(lnull$a ?v1 ))false )(=> (or (not (lnull$a ?v0 ))(not (lnull$a ?v1 )))false ))false )):named a19 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (and (=> (and (lnull$ ?v0 )(lnull$ ?v1 ))false )(=> (or (not (lnull$ ?v0 ))(not (lnull$ ?v1 )))false ))false )):named a20 ))
(assert (! (forall ((?v0 A_a_prod_a_a_prod_prod_llist$ ))(=> (and (=> (lnull$d ?v0 )false )(=> (not (lnull$d ?v0 ))false ))false )):named a21 ))
(assert (! (forall ((?v0 A_a_prod_a_prod_llist$ ))(=> (and (=> (lnull$b ?v0 )false )(=> (not (lnull$b ?v0 ))false ))false )):named a22 ))
(assert (! (forall ((?v0 A_a_a_prod_prod_llist$ ))(=> (and (=> (lnull$c ?v0 )false )(=> (not (lnull$c ?v0 ))false ))false )):named a23 ))
(assert (! (forall ((?v0 A_a_prod_llist$ ))(=> (and (=> (lnull$a ?v0 )false )(=> (not (lnull$a ?v0 ))false ))false )):named a24 ))
(assert (! (forall ((?v0 A_llist$ ))(=> (and (=> (lnull$ ?v0 )false )(=> (not (lnull$ ?v0 ))false ))false )):named a25 ))
(assert (! (forall ((?v0 A_a_prod_a_a_prod_prod_llist$ )(?v1 A_a_prod_a_a_prod_prod_a_a_prod_a_a_prod_prod_bool_fun_fun$ )(?v2 A_a_prod_a_a_prod_prod_llist$ ))(! (=> (lnull$d ?v0 )(= (llexord$ ?v1 ?v2 ?v0 )(lnull$d ?v2 ))):pattern ((llexord$ ?v1 ?v2 ?v0 )))):named a26 ))
(assert (! (forall ((?v0 A_a_prod_a_prod_llist$ )(?v1 A_a_prod_a_prod_a_a_prod_a_prod_bool_fun_fun$ )(?v2 A_a_prod_a_prod_llist$ ))(! (=> (lnull$b ?v0 )(= (llexord$a ?v1 ?v2 ?v0 )(lnull$b ?v2 ))):pattern ((llexord$a ?v1 ?v2 ?v0 )))):named a27 ))
(assert (! (forall ((?v0 A_a_a_prod_prod_llist$ )(?v1 A_a_a_prod_prod_a_a_a_prod_prod_bool_fun_fun$ )(?v2 A_a_a_prod_prod_llist$ ))(! (=> (lnull$c ?v0 )(= (llexord$b ?v1 ?v2 ?v0 )(lnull$c ?v2 ))):pattern ((llexord$b ?v1 ?v2 ?v0 )))):named a28 ))
(assert (! (forall ((?v0 A_a_prod_llist$ )(?v1 A_a_prod_a_a_prod_bool_fun_fun$ )(?v2 A_a_prod_llist$ ))(! (=> (lnull$a ?v0 )(= (llexord$c ?v1 ?v2 ?v0 )(lnull$a ?v2 ))):pattern ((llexord$c ?v1 ?v2 ?v0 )))):named a29 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_a_bool_fun_fun$ )(?v2 A_llist$ ))(! (=> (lnull$ ?v0 )(= (llexord$d ?v1 ?v2 ?v0 )(lnull$ ?v2 ))):pattern ((llexord$d ?v1 ?v2 ?v0 )))):named a30 ))
(assert (! (forall ((?v0 A_a_prod_a_a_prod_bool_fun_fun$ )(?v1 A_a_prod_llist$ ))(llexord$c ?v0 ?v1 ?v1 )):named a31 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A_llist$ ))(llexord$d ?v0 ?v1 ?v1 )):named a32 ))
(assert (! (forall ((?v0 A_a_prod_a_a_prod_bool_fun_fun$ )(?v1 A_a_prod_llist$ )(?v2 A_a_prod_llist$ ))(=> (forall ((?v3 A_a_prod$ )(?v4 A_a_prod$ ))(or (fun_app$ (fun_app$a ?v0 ?v3 )?v4 )(or (= ?v3 ?v4 )(fun_app$ (fun_app$a ?v0 ?v4 )?v3 ))))(or (llexord$c ?v0 ?v1 ?v2 )(llexord$c ?v0 ?v2 ?v1 )))):named a33 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A_llist$ )(?v2 A_llist$ ))(=> (forall ((?v3 A$ )(?v4 A$ ))(or (fun_app$b (fun_app$c ?v0 ?v3 )?v4 )(or (= ?v3 ?v4 )(fun_app$b (fun_app$c ?v0 ?v4 )?v3 ))))(or (llexord$d ?v0 ?v1 ?v2 )(llexord$d ?v0 ?v2 ?v1 )))):named a34 ))
(assert (! (forall ((?v0 A_a_prod_a_a_prod_bool_fun_fun$ )(?v1 A_a_prod_llist$ )(?v2 A_a_prod_llist$ )(?v3 A_a_prod_llist$ ))(=> (and (llexord$c ?v0 ?v1 ?v2 )(and (llexord$c ?v0 ?v2 ?v3 )(forall ((?v4 A_a_prod$ )(?v5 A_a_prod$ )(?v6 A_a_prod$ ))(=> (and (fun_app$ (fun_app$a ?v0 ?v4 )?v5 )(fun_app$ (fun_app$a ?v0 ?v5 )?v6 ))(fun_app$ (fun_app$a ?v0 ?v4 )?v6 )))))(llexord$c ?v0 ?v1 ?v3 ))):named a35 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A_llist$ )(?v2 A_llist$ )(?v3 A_llist$ ))(=> (and (llexord$d ?v0 ?v1 ?v2 )(and (llexord$d ?v0 ?v2 ?v3 )(forall ((?v4 A$ )(?v5 A$ )(?v6 A$ ))(=> (and (fun_app$b (fun_app$c ?v0 ?v4 )?v5 )(fun_app$b (fun_app$c ?v0 ?v5 )?v6 ))(fun_app$b (fun_app$c ?v0 ?v4 )?v6 )))))(llexord$d ?v0 ?v1 ?v3 ))):named a36 ))
(assert (! (forall ((?v0 A_a_prod_a_a_prod_bool_fun_fun$ )(?v1 A_a_prod_llist$ )(?v2 A_a_prod_llist$ ))(=> (and (llexord$c ?v0 ?v1 ?v2 )(and (llexord$c ?v0 ?v2 ?v1 )(forall ((?v3 A_a_prod$ )(?v4 A_a_prod$ ))(=> (and (fun_app$ (fun_app$a ?v0 ?v3 )?v4 )(fun_app$ (fun_app$a ?v0 ?v4 )?v3 ))false ))))(= ?v1 ?v2 ))):named a37 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A_llist$ )(?v2 A_llist$ ))(=> (and (llexord$d ?v0 ?v1 ?v2 )(and (llexord$d ?v0 ?v2 ?v1 )(forall ((?v3 A$ )(?v4 A$ ))(=> (and (fun_app$b (fun_app$c ?v0 ?v3 )?v4 )(fun_app$b (fun_app$c ?v0 ?v4 )?v3 ))false ))))(= ?v1 ?v2 ))):named a38 ))
(assert (! (forall ((?v0 A_a_prod_a_a_prod_prod_llist$ )(?v1 A_a_prod_a_a_prod_prod_a_a_prod_a_a_prod_prod_bool_fun_fun$ )(?v2 A_a_prod_a_a_prod_prod_llist$ ))(=> (lnull$d ?v0 )(llexord$ ?v1 ?v0 ?v2 ))):named a39 ))
(assert (! (forall ((?v0 A_a_prod_a_prod_llist$ )(?v1 A_a_prod_a_prod_a_a_prod_a_prod_bool_fun_fun$ )(?v2 A_a_prod_a_prod_llist$ ))(=> (lnull$b ?v0 )(llexord$a ?v1 ?v0 ?v2 ))):named a40 ))
(assert (! (forall ((?v0 A_a_a_prod_prod_llist$ )(?v1 A_a_a_prod_prod_a_a_a_prod_prod_bool_fun_fun$ )(?v2 A_a_a_prod_prod_llist$ ))(=> (lnull$c ?v0 )(llexord$b ?v1 ?v0 ?v2 ))):named a41 ))
(assert (! (forall ((?v0 A_a_prod_llist$ )(?v1 A_a_prod_a_a_prod_bool_fun_fun$ )(?v2 A_a_prod_llist$ ))(=> (lnull$a ?v0 )(llexord$c ?v1 ?v0 ?v2 ))):named a42 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_a_bool_fun_fun$ )(?v2 A_llist$ ))(=> (lnull$ ?v0 )(llexord$d ?v1 ?v0 ?v2 ))):named a43 ))
(assert (! (forall ((?v0 A_a_prod_a_a_prod_bool_fun_fun$ )(?v1 A_a_prod_llist$ ))(! (= (llexord$c ?v0 lNil$a ?v1 )true ):pattern ((llexord$c ?v0 lNil$a ?v1 )))):named a44 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A_llist$ ))(! (= (llexord$d ?v0 lNil$ ?v1 )true ):pattern ((llexord$d ?v0 lNil$ ?v1 )))):named a45 ))
(assert (! (forall ((?v0 A_a_prod_a_a_prod_bool_fun_fun$ )(?v1 A_a_prod$ )(?v2 A_a_prod_llist$ )(?v3 A_a_prod$ )(?v4 A_a_prod_llist$ ))(! (= (llexord$c ?v0 (lCons$a ?v1 ?v2 )(lCons$a ?v3 ?v4 ))(or (and (= ?v1 ?v3 )(llexord$c ?v0 ?v2 ?v4 ))(fun_app$ (fun_app$a ?v0 ?v1 )?v3 ))):pattern ((llexord$c ?v0 (lCons$a ?v1 ?v2 )(lCons$a ?v3 ?v4 ))))):named a46 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A$ )(?v2 A_llist$ )(?v3 A$ )(?v4 A_llist$ ))(! (= (llexord$d ?v0 (lCons$ ?v1 ?v2 )(lCons$ ?v3 ?v4 ))(or (and (= ?v1 ?v3 )(llexord$d ?v0 ?v2 ?v4 ))(fun_app$b (fun_app$c ?v0 ?v1 )?v3 ))):pattern ((llexord$d ?v0 (lCons$ ?v1 ?v2 )(lCons$ ?v3 ?v4 ))))):named a47 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(= (lnull$a (lzip$ ?v0 ?v1 ))(or (lnull$ ?v0 )(lnull$ ?v1 )))):named a48 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_a_prod_llist$ ))(= (lnull$c (lzip$a ?v0 ?v1 ))(or (lnull$ ?v0 )(lnull$a ?v1 )))):named a49 ))
(assert (! (forall ((?v0 A_a_prod_llist$ )(?v1 A_llist$ ))(= (lnull$b (lzip$b ?v0 ?v1 ))(or (lnull$a ?v0 )(lnull$ ?v1 )))):named a50 ))
(assert (! (forall ((?v0 A_a_prod_llist$ )(?v1 A_a_prod_llist$ ))(= (lnull$d (lzip$c ?v0 ?v1 ))(or (lnull$a ?v0 )(lnull$a ?v1 )))):named a51 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_a_prod_a_prod_llist$ ))(= (lnull$e (lzip$d ?v0 ?v1 ))(or (lnull$ ?v0 )(lnull$b ?v1 )))):named a52 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_a_a_prod_prod_llist$ ))(= (lnull$f (lzip$e ?v0 ?v1 ))(or (lnull$ ?v0 )(lnull$c ?v1 )))):named a53 ))
(assert (! (forall ((?v0 A_a_prod_a_prod_llist$ )(?v1 A_llist$ ))(= (lnull$g (lzip$f ?v0 ?v1 ))(or (lnull$b ?v0 )(lnull$ ?v1 )))):named a54 ))
(assert (! (forall ((?v0 A_a_a_prod_prod_llist$ )(?v1 A_llist$ ))(= (lnull$h (lzip$g ?v0 ?v1 ))(or (lnull$c ?v0 )(lnull$ ?v1 )))):named a55 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_a_prod_a_a_prod_prod_llist$ ))(= (lnull$i (lzip$h ?v0 ?v1 ))(or (lnull$ ?v0 )(lnull$d ?v1 )))):named a56 ))
(assert (! (forall ((?v0 A_a_prod_llist$ )(?v1 A_a_prod_a_prod_llist$ ))(= (lnull$j (lzip$i ?v0 ?v1 ))(or (lnull$a ?v0 )(lnull$b ?v1 )))):named a57 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(= (not (lnull$a (lzip$ ?v0 ?v1 )))(and (not (lnull$ ?v0 ))(not (lnull$ ?v1 ))))):named a58 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_a_prod_llist$ ))(= (not (lnull$c (lzip$a ?v0 ?v1 )))(and (not (lnull$ ?v0 ))(not (lnull$a ?v1 ))))):named a59 ))
(assert (! (forall ((?v0 A_a_prod_llist$ )(?v1 A_llist$ ))(= (not (lnull$b (lzip$b ?v0 ?v1 )))(and (not (lnull$a ?v0 ))(not (lnull$ ?v1 ))))):named a60 ))
(assert (! (forall ((?v0 A_a_prod_llist$ )(?v1 A_a_prod_llist$ ))(= (not (lnull$d (lzip$c ?v0 ?v1 )))(and (not (lnull$a ?v0 ))(not (lnull$a ?v1 ))))):named a61 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_a_prod_a_prod_llist$ ))(= (not (lnull$e (lzip$d ?v0 ?v1 )))(and (not (lnull$ ?v0 ))(not (lnull$b ?v1 ))))):named a62 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_a_a_prod_prod_llist$ ))(= (not (lnull$f (lzip$e ?v0 ?v1 )))(and (not (lnull$ ?v0 ))(not (lnull$c ?v1 ))))):named a63 ))
(assert (! (forall ((?v0 A_a_prod_a_prod_llist$ )(?v1 A_llist$ ))(= (not (lnull$g (lzip$f ?v0 ?v1 )))(and (not (lnull$b ?v0 ))(not (lnull$ ?v1 ))))):named a64 ))
(assert (! (forall ((?v0 A_a_a_prod_prod_llist$ )(?v1 A_llist$ ))(= (not (lnull$h (lzip$g ?v0 ?v1 )))(and (not (lnull$c ?v0 ))(not (lnull$ ?v1 ))))):named a65 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_a_prod_a_a_prod_prod_llist$ ))(= (not (lnull$i (lzip$h ?v0 ?v1 )))(and (not (lnull$ ?v0 ))(not (lnull$d ?v1 ))))):named a66 ))
(assert (! (forall ((?v0 A_a_prod_llist$ )(?v1 A_a_prod_a_prod_llist$ ))(= (not (lnull$j (lzip$i ?v0 ?v1 )))(and (not (lnull$a ?v0 ))(not (lnull$b ?v1 ))))):named a67 ))
(check-sat )
;(get-unsat-core )
