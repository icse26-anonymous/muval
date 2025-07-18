;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_a_fun$ 0 )
(declare-sort A_llist_set$ 0 )
(declare-sort A_a_prod_llist_set$ 0 )
(declare-sort A_a_prod_a_a_prod_fun$ 0 )
(declare-sort A_a_a_prod_prod_llist_set$ 0 )
(declare-sort A_a_prod_a_prod_llist_set$ 0 )
(declare-sort A_a_prod_a_a_prod_prod_llist_set$ 0 )
(declare-sort A_a_a_prod_prod_a_a_a_prod_prod_fun$ 0 )
(declare-sort A_a_prod_a_prod_a_a_prod_a_prod_fun$ 0 )
(declare-sort A_a_prod_a_a_prod_prod_a_a_prod_a_a_prod_prod_fun$ 0 )
(declare-datatypes ()((Nat_option$ (none$ )(some$ (the$ Nat$ )))(Enat$ (abs_enat$ (rep_enat$ Nat_option$ )))))
(declare-sort A_llist$ 0)
(declare-fun lNil$ ()A_llist$)
(declare-fun lhd$ (A_llist$)A$)
(declare-fun ltl$ (A_llist$)A_llist$)
(declare-fun lCons$ (A$ A_llist$ )A_llist$)
(declare-datatypes ()((A_a_prod$ (pair$ (fst$ A$ )(snd$ A$ )))(A_a_prod_a_a_prod_prod$ (pair$a (fst$a A_a_prod$ )(snd$a A_a_prod$ )))))
(declare-sort A_a_prod_a_a_prod_prod_llist$ 0)
(declare-fun lNil$a ()A_a_prod_a_a_prod_prod_llist$)
(declare-fun lhd$a (A_a_prod_a_a_prod_prod_llist$)A_a_prod_a_a_prod_prod$)
(declare-fun ltl$a (A_a_prod_a_a_prod_prod_llist$)A_a_prod_a_a_prod_prod_llist$)
(declare-fun lCons$a (A_a_prod_a_a_prod_prod$ A_a_prod_a_a_prod_prod_llist$ )A_a_prod_a_a_prod_prod_llist$)
(declare-datatypes ()((A_a_prod_a_prod$ (pair$b (fst$b A_a_prod$ )(snd$b A$ )))))
(declare-sort A_a_prod_a_prod_llist$ 0)
(declare-fun lNil$b ()A_a_prod_a_prod_llist$)
(declare-fun lhd$b (A_a_prod_a_prod_llist$)A_a_prod_a_prod$)
(declare-fun ltl$b (A_a_prod_a_prod_llist$)A_a_prod_a_prod_llist$)
(declare-fun lCons$b (A_a_prod_a_prod$ A_a_prod_a_prod_llist$ )A_a_prod_a_prod_llist$)
(declare-datatypes ()((A_a_a_prod_prod$ (pair$c (fst$c A$ )(snd$c A_a_prod$ )))))
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
(declare-fun xs$ ()A_llist$ )
(declare-fun lzip$ (A_llist$ A_llist$ )A_a_prod_llist$ )
(declare-fun zero$ ()Enat$ )
(declare-fun lnull$ (A_llist$ )Bool )
(declare-fun ltake$ (Enat$ A_a_prod_a_a_prod_prod_llist$ )A_a_prod_a_a_prod_prod_llist$ )
(declare-fun lzip$a (A_llist$ A_a_prod_llist$ )A_a_a_prod_prod_llist$ )
(declare-fun lzip$b (A_a_prod_llist$ A_llist$ )A_a_prod_a_prod_llist$ )
(declare-fun lzip$c (A_a_prod_llist$ A_a_prod_llist$ )A_a_prod_a_a_prod_prod_llist$ )
(declare-fun lzip$d (A_llist$ A_a_prod_a_prod_llist$ )A_a_a_prod_a_prod_prod_llist$ )
(declare-fun lzip$e (A_llist$ A_a_a_prod_prod_llist$ )A_a_a_a_prod_prod_prod_llist$ )
(declare-fun lzip$f (A_a_prod_a_prod_llist$ A_llist$ )A_a_prod_a_prod_a_prod_llist$ )
(declare-fun lzip$g (A_a_a_prod_prod_llist$ A_llist$ )A_a_a_prod_prod_a_prod_llist$ )
(declare-fun lzip$h (A_llist$ A_a_prod_a_a_prod_prod_llist$ )A_a_a_prod_a_a_prod_prod_prod_llist$ )
(declare-fun lzip$i (A_a_prod_llist$ A_a_prod_a_prod_llist$ )A_a_prod_a_a_prod_a_prod_prod_llist$ )
(declare-fun lnull$a (A_a_prod_a_a_prod_prod_llist$ )Bool )
(declare-fun lnull$b (A_a_prod_a_prod_llist$ )Bool )
(declare-fun lnull$c (A_a_a_prod_prod_llist$ )Bool )
(declare-fun lnull$d (A_a_prod_llist$ )Bool )
(declare-fun lnull$e (A_a_a_prod_a_prod_prod_llist$ )Bool )
(declare-fun lnull$f (A_a_a_a_prod_prod_prod_llist$ )Bool )
(declare-fun lnull$g (A_a_prod_a_prod_a_prod_llist$ )Bool )
(declare-fun lnull$h (A_a_a_prod_prod_a_prod_llist$ )Bool )
(declare-fun lnull$i (A_a_a_prod_a_a_prod_prod_prod_llist$ )Bool )
(declare-fun lnull$j (A_a_prod_a_a_prod_a_prod_prod_llist$ )Bool )
(declare-fun ltake$a (Enat$ A_a_prod_a_prod_llist$ )A_a_prod_a_prod_llist$ )
(declare-fun ltake$b (Enat$ A_a_a_prod_prod_llist$ )A_a_a_prod_prod_llist$ )
(declare-fun ltake$c (Enat$ A_a_prod_llist$ )A_a_prod_llist$ )
(declare-fun ltake$d (Enat$ A_llist$ )A_llist$ )
(declare-fun member$ (A_a_prod_a_a_prod_prod_llist$ A_a_prod_a_a_prod_prod_llist_set$ )Bool )
(declare-fun llength$ (A_llist$ )Enat$ )
(declare-fun member$a (A_a_prod_a_prod_llist$ A_a_prod_a_prod_llist_set$ )Bool )
(declare-fun member$b (A_a_a_prod_prod_llist$ A_a_a_prod_prod_llist_set$ )Bool )
(declare-fun member$c (A_a_prod_llist$ A_a_prod_llist_set$ )Bool )
(declare-fun member$d (A_llist$ A_llist_set$ )Bool )
(declare-fun iterates$ (A_a_prod_a_a_prod_prod_a_a_prod_a_a_prod_prod_fun$ A_a_prod_a_a_prod_prod$ )A_a_prod_a_a_prod_prod_llist$ )
(declare-fun iterates$a (A_a_prod_a_prod_a_a_prod_a_prod_fun$ A_a_prod_a_prod$ )A_a_prod_a_prod_llist$ )
(declare-fun iterates$b (A_a_a_prod_prod_a_a_a_prod_prod_fun$ A_a_a_prod_prod$ )A_a_a_prod_prod_llist$ )
(declare-fun iterates$c (A_a_prod_a_a_prod_fun$ A_a_prod$ )A_a_prod_llist$ )
(declare-fun iterates$d (A_a_fun$ A$ )A_llist$ )
(assert (! (not (= (= (llength$ xs$ )zero$ )(lnull$ xs$ ))):named a0 ))
(assert (! (forall ((?v0 Enat$ )(?v1 A_a_prod_a_a_prod_prod_llist$ ))(=> (and (=> (or (= ?v0 zero$ )(lnull$a ?v1 ))false )(=> (and (not (= ?v0 zero$ ))(not (lnull$a ?v1 )))false ))false )):named a1 ))
(assert (! (forall ((?v0 Enat$ )(?v1 A_a_prod_a_prod_llist$ ))(=> (and (=> (or (= ?v0 zero$ )(lnull$b ?v1 ))false )(=> (and (not (= ?v0 zero$ ))(not (lnull$b ?v1 )))false ))false )):named a2 ))
(assert (! (forall ((?v0 Enat$ )(?v1 A_a_a_prod_prod_llist$ ))(=> (and (=> (or (= ?v0 zero$ )(lnull$c ?v1 ))false )(=> (and (not (= ?v0 zero$ ))(not (lnull$c ?v1 )))false ))false )):named a3 ))
(assert (! (forall ((?v0 Enat$ )(?v1 A_a_prod_llist$ ))(=> (and (=> (or (= ?v0 zero$ )(lnull$d ?v1 ))false )(=> (and (not (= ?v0 zero$ ))(not (lnull$d ?v1 )))false ))false )):named a4 ))
(assert (! (forall ((?v0 Enat$ )(?v1 A_llist$ ))(=> (and (=> (or (= ?v0 zero$ )(lnull$ ?v1 ))false )(=> (and (not (= ?v0 zero$ ))(not (lnull$ ?v1 )))false ))false )):named a5 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (and (=> (or (lnull$ ?v0 )(lnull$ ?v1 ))false )(=> (and (not (lnull$ ?v0 ))(not (lnull$ ?v1 )))false ))false )):named a6 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_a_prod_llist$ ))(=> (and (=> (or (lnull$ ?v0 )(lnull$d ?v1 ))false )(=> (and (not (lnull$ ?v0 ))(not (lnull$d ?v1 )))false ))false )):named a7 ))
(assert (! (forall ((?v0 A_a_prod_llist$ )(?v1 A_llist$ ))(=> (and (=> (or (lnull$d ?v0 )(lnull$ ?v1 ))false )(=> (and (not (lnull$d ?v0 ))(not (lnull$ ?v1 )))false ))false )):named a8 ))
(assert (! (forall ((?v0 A_a_prod_llist$ )(?v1 A_a_prod_llist$ ))(=> (and (=> (or (lnull$d ?v0 )(lnull$d ?v1 ))false )(=> (and (not (lnull$d ?v0 ))(not (lnull$d ?v1 )))false ))false )):named a9 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_a_prod_a_prod_llist$ ))(=> (and (=> (or (lnull$ ?v0 )(lnull$b ?v1 ))false )(=> (and (not (lnull$ ?v0 ))(not (lnull$b ?v1 )))false ))false )):named a10 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_a_a_prod_prod_llist$ ))(=> (and (=> (or (lnull$ ?v0 )(lnull$c ?v1 ))false )(=> (and (not (lnull$ ?v0 ))(not (lnull$c ?v1 )))false ))false )):named a11 ))
(assert (! (forall ((?v0 A_a_prod_a_prod_llist$ )(?v1 A_llist$ ))(=> (and (=> (or (lnull$b ?v0 )(lnull$ ?v1 ))false )(=> (and (not (lnull$b ?v0 ))(not (lnull$ ?v1 )))false ))false )):named a12 ))
(assert (! (forall ((?v0 A_a_a_prod_prod_llist$ )(?v1 A_llist$ ))(=> (and (=> (or (lnull$c ?v0 )(lnull$ ?v1 ))false )(=> (and (not (lnull$c ?v0 ))(not (lnull$ ?v1 )))false ))false )):named a13 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_a_prod_a_a_prod_prod_llist$ ))(=> (and (=> (or (lnull$ ?v0 )(lnull$a ?v1 ))false )(=> (and (not (lnull$ ?v0 ))(not (lnull$a ?v1 )))false ))false )):named a14 ))
(assert (! (forall ((?v0 A_a_prod_llist$ )(?v1 A_a_prod_a_prod_llist$ ))(=> (and (=> (or (lnull$d ?v0 )(lnull$b ?v1 ))false )(=> (and (not (lnull$d ?v0 ))(not (lnull$b ?v1 )))false ))false )):named a15 ))
(assert (! (forall ((?v0 A_a_prod_a_a_prod_prod_llist_set$ ))(=> (and (=> (forall ((?v1 A_a_prod_a_a_prod_prod_llist$ ))(=> (member$ ?v1 ?v0 )(lnull$a ?v1 )))false )(=> (not (forall ((?v1 A_a_prod_a_a_prod_prod_llist$ ))(=> (member$ ?v1 ?v0 )(lnull$a ?v1 ))))false ))false )):named a16 ))
(assert (! (forall ((?v0 A_a_prod_a_prod_llist_set$ ))(=> (and (=> (forall ((?v1 A_a_prod_a_prod_llist$ ))(=> (member$a ?v1 ?v0 )(lnull$b ?v1 )))false )(=> (not (forall ((?v1 A_a_prod_a_prod_llist$ ))(=> (member$a ?v1 ?v0 )(lnull$b ?v1 ))))false ))false )):named a17 ))
(assert (! (forall ((?v0 A_a_a_prod_prod_llist_set$ ))(=> (and (=> (forall ((?v1 A_a_a_prod_prod_llist$ ))(=> (member$b ?v1 ?v0 )(lnull$c ?v1 )))false )(=> (not (forall ((?v1 A_a_a_prod_prod_llist$ ))(=> (member$b ?v1 ?v0 )(lnull$c ?v1 ))))false ))false )):named a18 ))
(assert (! (forall ((?v0 A_a_prod_llist_set$ ))(=> (and (=> (forall ((?v1 A_a_prod_llist$ ))(=> (member$c ?v1 ?v0 )(lnull$d ?v1 )))false )(=> (not (forall ((?v1 A_a_prod_llist$ ))(=> (member$c ?v1 ?v0 )(lnull$d ?v1 ))))false ))false )):named a19 ))
(assert (! (forall ((?v0 A_llist_set$ ))(=> (and (=> (forall ((?v1 A_llist$ ))(=> (member$d ?v1 ?v0 )(lnull$ ?v1 )))false )(=> (not (forall ((?v1 A_llist$ ))(=> (member$d ?v1 ?v0 )(lnull$ ?v1 ))))false ))false )):named a20 ))
(assert (! (forall ((?v0 A_a_prod_a_a_prod_prod_llist$ )(?v1 A_a_prod_a_a_prod_prod_llist$ ))(=> (and (=> (and (lnull$a ?v0 )(lnull$a ?v1 ))false )(=> (or (not (lnull$a ?v0 ))(not (lnull$a ?v1 )))false ))false )):named a21 ))
(assert (! (forall ((?v0 A_a_prod_a_prod_llist$ )(?v1 A_a_prod_a_prod_llist$ ))(=> (and (=> (and (lnull$b ?v0 )(lnull$b ?v1 ))false )(=> (or (not (lnull$b ?v0 ))(not (lnull$b ?v1 )))false ))false )):named a22 ))
(assert (! (forall ((?v0 A_a_a_prod_prod_llist$ )(?v1 A_a_a_prod_prod_llist$ ))(=> (and (=> (and (lnull$c ?v0 )(lnull$c ?v1 ))false )(=> (or (not (lnull$c ?v0 ))(not (lnull$c ?v1 )))false ))false )):named a23 ))
(assert (! (forall ((?v0 A_a_prod_llist$ )(?v1 A_a_prod_llist$ ))(=> (and (=> (and (lnull$d ?v0 )(lnull$d ?v1 ))false )(=> (or (not (lnull$d ?v0 ))(not (lnull$d ?v1 )))false ))false )):named a24 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (and (=> (and (lnull$ ?v0 )(lnull$ ?v1 ))false )(=> (or (not (lnull$ ?v0 ))(not (lnull$ ?v1 )))false ))false )):named a25 ))
(assert (! (forall ((?v0 A_a_prod_a_a_prod_prod_llist$ ))(=> (and (=> (lnull$a ?v0 )false )(=> (not (lnull$a ?v0 ))false ))false )):named a26 ))
(assert (! (forall ((?v0 A_a_prod_a_prod_llist$ ))(=> (and (=> (lnull$b ?v0 )false )(=> (not (lnull$b ?v0 ))false ))false )):named a27 ))
(assert (! (forall ((?v0 A_a_a_prod_prod_llist$ ))(=> (and (=> (lnull$c ?v0 )false )(=> (not (lnull$c ?v0 ))false ))false )):named a28 ))
(assert (! (forall ((?v0 A_a_prod_llist$ ))(=> (and (=> (lnull$d ?v0 )false )(=> (not (lnull$d ?v0 ))false ))false )):named a29 ))
(assert (! (forall ((?v0 A_llist$ ))(=> (and (=> (lnull$ ?v0 )false )(=> (not (lnull$ ?v0 ))false ))false )):named a30 ))
(assert (! (forall ((?v0 Enat$ )(?v1 A_a_prod_a_a_prod_prod_llist$ ))(= (not (lnull$a (ltake$ ?v0 ?v1 )))(and (not (= ?v0 zero$ ))(not (lnull$a ?v1 ))))):named a31 ))
(assert (! (forall ((?v0 Enat$ )(?v1 A_a_prod_a_prod_llist$ ))(= (not (lnull$b (ltake$a ?v0 ?v1 )))(and (not (= ?v0 zero$ ))(not (lnull$b ?v1 ))))):named a32 ))
(assert (! (forall ((?v0 Enat$ )(?v1 A_a_a_prod_prod_llist$ ))(= (not (lnull$c (ltake$b ?v0 ?v1 )))(and (not (= ?v0 zero$ ))(not (lnull$c ?v1 ))))):named a33 ))
(assert (! (forall ((?v0 Enat$ )(?v1 A_a_prod_llist$ ))(= (not (lnull$d (ltake$c ?v0 ?v1 )))(and (not (= ?v0 zero$ ))(not (lnull$d ?v1 ))))):named a34 ))
(assert (! (forall ((?v0 Enat$ )(?v1 A_llist$ ))(= (not (lnull$ (ltake$d ?v0 ?v1 )))(and (not (= ?v0 zero$ ))(not (lnull$ ?v1 ))))):named a35 ))
(assert (! (forall ((?v0 Enat$ )(?v1 A_a_prod_a_a_prod_prod_llist$ ))(= (lnull$a (ltake$ ?v0 ?v1 ))(or (= ?v0 zero$ )(lnull$a ?v1 )))):named a36 ))
(assert (! (forall ((?v0 Enat$ )(?v1 A_a_prod_a_prod_llist$ ))(= (lnull$b (ltake$a ?v0 ?v1 ))(or (= ?v0 zero$ )(lnull$b ?v1 )))):named a37 ))
(assert (! (forall ((?v0 Enat$ )(?v1 A_a_a_prod_prod_llist$ ))(= (lnull$c (ltake$b ?v0 ?v1 ))(or (= ?v0 zero$ )(lnull$c ?v1 )))):named a38 ))
(assert (! (forall ((?v0 Enat$ )(?v1 A_a_prod_llist$ ))(= (lnull$d (ltake$c ?v0 ?v1 ))(or (= ?v0 zero$ )(lnull$d ?v1 )))):named a39 ))
(assert (! (forall ((?v0 Enat$ )(?v1 A_llist$ ))(= (lnull$ (ltake$d ?v0 ?v1 ))(or (= ?v0 zero$ )(lnull$ ?v1 )))):named a40 ))
(assert (! (forall ((?v0 Enat$ )(?v1 A_a_prod_a_a_prod_prod_llist$ ))(=> (or (= ?v0 zero$ )(lnull$a ?v1 ))(lnull$a (ltake$ ?v0 ?v1 )))):named a41 ))
(assert (! (forall ((?v0 Enat$ )(?v1 A_a_prod_a_prod_llist$ ))(=> (or (= ?v0 zero$ )(lnull$b ?v1 ))(lnull$b (ltake$a ?v0 ?v1 )))):named a42 ))
(assert (! (forall ((?v0 Enat$ )(?v1 A_a_a_prod_prod_llist$ ))(=> (or (= ?v0 zero$ )(lnull$c ?v1 ))(lnull$c (ltake$b ?v0 ?v1 )))):named a43 ))
(assert (! (forall ((?v0 Enat$ )(?v1 A_a_prod_llist$ ))(=> (or (= ?v0 zero$ )(lnull$d ?v1 ))(lnull$d (ltake$c ?v0 ?v1 )))):named a44 ))
(assert (! (forall ((?v0 Enat$ )(?v1 A_llist$ ))(=> (or (= ?v0 zero$ )(lnull$ ?v1 ))(lnull$ (ltake$d ?v0 ?v1 )))):named a45 ))
(assert (! (forall ((?v0 Enat$ )(?v1 A_a_prod_a_a_prod_prod_llist$ ))(=> (and (not (= ?v0 zero$ ))(not (lnull$a ?v1 )))(not (lnull$a (ltake$ ?v0 ?v1 ))))):named a46 ))
(assert (! (forall ((?v0 Enat$ )(?v1 A_a_prod_a_prod_llist$ ))(=> (and (not (= ?v0 zero$ ))(not (lnull$b ?v1 )))(not (lnull$b (ltake$a ?v0 ?v1 ))))):named a47 ))
(assert (! (forall ((?v0 Enat$ )(?v1 A_a_a_prod_prod_llist$ ))(=> (and (not (= ?v0 zero$ ))(not (lnull$c ?v1 )))(not (lnull$c (ltake$b ?v0 ?v1 ))))):named a48 ))
(assert (! (forall ((?v0 Enat$ )(?v1 A_a_prod_llist$ ))(=> (and (not (= ?v0 zero$ ))(not (lnull$d ?v1 )))(not (lnull$d (ltake$c ?v0 ?v1 ))))):named a49 ))
(assert (! (forall ((?v0 Enat$ )(?v1 A_llist$ ))(=> (and (not (= ?v0 zero$ ))(not (lnull$ ?v1 )))(not (lnull$ (ltake$d ?v0 ?v1 ))))):named a50 ))
(assert (! (forall ((?v0 Enat$ ))(=> (and (=> (= ?v0 zero$ )false )(=> (not (= ?v0 zero$ ))false ))false )):named a51 ))
(assert (! (= (llength$ lNil$ )zero$ ):named a52 ))
(assert (! (forall ((?v0 Enat$ ))(= (= zero$ ?v0 )(= ?v0 zero$ ))):named a53 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(= (not (lnull$d (lzip$ ?v0 ?v1 )))(and (not (lnull$ ?v0 ))(not (lnull$ ?v1 ))))):named a54 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_a_prod_llist$ ))(= (not (lnull$c (lzip$a ?v0 ?v1 )))(and (not (lnull$ ?v0 ))(not (lnull$d ?v1 ))))):named a55 ))
(assert (! (forall ((?v0 A_a_prod_llist$ )(?v1 A_llist$ ))(= (not (lnull$b (lzip$b ?v0 ?v1 )))(and (not (lnull$d ?v0 ))(not (lnull$ ?v1 ))))):named a56 ))
(assert (! (forall ((?v0 A_a_prod_llist$ )(?v1 A_a_prod_llist$ ))(= (not (lnull$a (lzip$c ?v0 ?v1 )))(and (not (lnull$d ?v0 ))(not (lnull$d ?v1 ))))):named a57 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_a_prod_a_prod_llist$ ))(= (not (lnull$e (lzip$d ?v0 ?v1 )))(and (not (lnull$ ?v0 ))(not (lnull$b ?v1 ))))):named a58 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_a_a_prod_prod_llist$ ))(= (not (lnull$f (lzip$e ?v0 ?v1 )))(and (not (lnull$ ?v0 ))(not (lnull$c ?v1 ))))):named a59 ))
(assert (! (forall ((?v0 A_a_prod_a_prod_llist$ )(?v1 A_llist$ ))(= (not (lnull$g (lzip$f ?v0 ?v1 )))(and (not (lnull$b ?v0 ))(not (lnull$ ?v1 ))))):named a60 ))
(assert (! (forall ((?v0 A_a_a_prod_prod_llist$ )(?v1 A_llist$ ))(= (not (lnull$h (lzip$g ?v0 ?v1 )))(and (not (lnull$c ?v0 ))(not (lnull$ ?v1 ))))):named a61 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_a_prod_a_a_prod_prod_llist$ ))(= (not (lnull$i (lzip$h ?v0 ?v1 )))(and (not (lnull$ ?v0 ))(not (lnull$a ?v1 ))))):named a62 ))
(assert (! (forall ((?v0 A_a_prod_llist$ )(?v1 A_a_prod_a_prod_llist$ ))(= (not (lnull$j (lzip$i ?v0 ?v1 )))(and (not (lnull$d ?v0 ))(not (lnull$b ?v1 ))))):named a63 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(= (lnull$d (lzip$ ?v0 ?v1 ))(or (lnull$ ?v0 )(lnull$ ?v1 )))):named a64 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_a_prod_llist$ ))(= (lnull$c (lzip$a ?v0 ?v1 ))(or (lnull$ ?v0 )(lnull$d ?v1 )))):named a65 ))
(assert (! (forall ((?v0 A_a_prod_llist$ )(?v1 A_llist$ ))(= (lnull$b (lzip$b ?v0 ?v1 ))(or (lnull$d ?v0 )(lnull$ ?v1 )))):named a66 ))
(assert (! (forall ((?v0 A_a_prod_llist$ )(?v1 A_a_prod_llist$ ))(= (lnull$a (lzip$c ?v0 ?v1 ))(or (lnull$d ?v0 )(lnull$d ?v1 )))):named a67 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_a_prod_a_prod_llist$ ))(= (lnull$e (lzip$d ?v0 ?v1 ))(or (lnull$ ?v0 )(lnull$b ?v1 )))):named a68 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_a_a_prod_prod_llist$ ))(= (lnull$f (lzip$e ?v0 ?v1 ))(or (lnull$ ?v0 )(lnull$c ?v1 )))):named a69 ))
(assert (! (forall ((?v0 A_a_prod_a_prod_llist$ )(?v1 A_llist$ ))(= (lnull$g (lzip$f ?v0 ?v1 ))(or (lnull$b ?v0 )(lnull$ ?v1 )))):named a70 ))
(assert (! (forall ((?v0 A_a_a_prod_prod_llist$ )(?v1 A_llist$ ))(= (lnull$h (lzip$g ?v0 ?v1 ))(or (lnull$c ?v0 )(lnull$ ?v1 )))):named a71 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_a_prod_a_a_prod_prod_llist$ ))(= (lnull$i (lzip$h ?v0 ?v1 ))(or (lnull$ ?v0 )(lnull$a ?v1 )))):named a72 ))
(assert (! (forall ((?v0 A_a_prod_llist$ )(?v1 A_a_prod_a_prod_llist$ ))(= (lnull$j (lzip$i ?v0 ?v1 ))(or (lnull$d ?v0 )(lnull$b ?v1 )))):named a73 ))
(assert (! (forall ((?v0 A_a_prod_a_a_prod_prod_a_a_prod_a_a_prod_prod_fun$ )(?v1 A_a_prod_a_a_prod_prod$ ))(not (lnull$a (iterates$ ?v0 ?v1 )))):named a74 ))
(assert (! (forall ((?v0 A_a_prod_a_prod_a_a_prod_a_prod_fun$ )(?v1 A_a_prod_a_prod$ ))(not (lnull$b (iterates$a ?v0 ?v1 )))):named a75 ))
(assert (! (forall ((?v0 A_a_a_prod_prod_a_a_a_prod_prod_fun$ )(?v1 A_a_a_prod_prod$ ))(not (lnull$c (iterates$b ?v0 ?v1 )))):named a76 ))
(assert (! (forall ((?v0 A_a_prod_a_a_prod_fun$ )(?v1 A_a_prod$ ))(not (lnull$d (iterates$c ?v0 ?v1 )))):named a77 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A$ ))(not (lnull$ (iterates$d ?v0 ?v1 )))):named a78 ))
(check-sat )
;(get-unsat-core )
