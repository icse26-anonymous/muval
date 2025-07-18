;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_list_a_llist_fun$ 0 )
(declare-sort A_llist_list_a_llist_llist_fun$ 0 )
(declare-sort A_llist_llist_list_a_llist_llist_llist_fun$ 0 )
(declare-sort A_llist_llist_llist_list_a_llist_llist_llist_llist_fun$ 0 )
(declare-codatatypes ()((A_llist$ (lNil$ )(lCons$ (lhd$ A$ )(ltl$ A_llist$ )))))
(declare-sort A_llist_list$ 0)
(declare-fun nil$ ()A_llist_list$)
(declare-fun hd$ (A_llist_list$)A_llist$)
(declare-fun tl$ (A_llist_list$)A_llist_list$)
(declare-fun cons$ (A_llist$ A_llist_list$ )A_llist_list$)
(declare-codatatypes ()((A_llist_llist$ (lNil$a )(lCons$a (lhd$a A_llist$ )(ltl$a A_llist_llist$ )))(A_llist_llist_llist$ (lNil$b )(lCons$b (lhd$b A_llist_llist$ )(ltl$b A_llist_llist_llist$ )))))
(declare-sort A_llist_llist_llist_list$ 0)
(declare-fun nil$a ()A_llist_llist_llist_list$)
(declare-fun hd$a (A_llist_llist_llist_list$)A_llist_llist_llist$)
(declare-fun tl$a (A_llist_llist_llist_list$)A_llist_llist_llist_list$)
(declare-fun cons$a (A_llist_llist_llist$ A_llist_llist_llist_list$ )A_llist_llist_llist_list$)
(declare-codatatypes ()((A_llist_llist_llist_llist$ (lNil$c )(lCons$c (lhd$c A_llist_llist_llist$ )(ltl$c A_llist_llist_llist_llist$ )))))
(declare-sort A_list$ 0)
(declare-sort A_llist_llist_list$ 0)
(declare-sort A_llist_llist_llist_list_list$ 0)
(declare-fun nil$b ()A_list$)
(declare-fun hd$b (A_list$)A$)
(declare-fun tl$b (A_list$)A_list$)
(declare-fun cons$b (A$ A_list$ )A_list$)
(declare-fun nil$c ()A_llist_llist_list$)
(declare-fun hd$c (A_llist_llist_list$)A_llist_llist$)
(declare-fun tl$c (A_llist_llist_list$)A_llist_llist_list$)
(declare-fun cons$c (A_llist_llist$ A_llist_llist_list$ )A_llist_llist_list$)
(declare-fun nil$d ()A_llist_llist_llist_list_list$)
(declare-fun hd$d (A_llist_llist_llist_list_list$)A_llist_llist_llist_list$)
(declare-fun tl$d (A_llist_llist_llist_list_list$)A_llist_llist_llist_list_list$)
(declare-fun cons$d (A_llist_llist_llist_list$ A_llist_llist_llist_list_list$ )A_llist_llist_llist_list_list$)
(declare-codatatypes ()((A_llist_llist_llist_llist_llist$ (lNil$d )(lCons$d (lhd$d A_llist_llist_llist_llist$ )(ltl$d A_llist_llist_llist_llist_llist$ )))))
(declare-sort A_llist_llist_llist_llist_list$ 0)
(declare-sort A_llist_llist_list_list$ 0)
(declare-sort A_llist_list_list$ 0)
(declare-sort A_list_list$ 0)
(declare-fun nil$e ()A_llist_llist_llist_llist_list$)
(declare-fun hd$e (A_llist_llist_llist_llist_list$)A_llist_llist_llist_llist$)
(declare-fun tl$e (A_llist_llist_llist_llist_list$)A_llist_llist_llist_llist_list$)
(declare-fun cons$e (A_llist_llist_llist_llist$ A_llist_llist_llist_llist_list$ )A_llist_llist_llist_llist_list$)
(declare-fun nil$f ()A_llist_llist_list_list$)
(declare-fun hd$f (A_llist_llist_list_list$)A_llist_llist_list$)
(declare-fun tl$f (A_llist_llist_list_list$)A_llist_llist_list_list$)
(declare-fun cons$f (A_llist_llist_list$ A_llist_llist_list_list$ )A_llist_llist_list_list$)
(declare-fun nil$g ()A_llist_list_list$)
(declare-fun hd$g (A_llist_list_list$)A_llist_list$)
(declare-fun tl$g (A_llist_list_list$)A_llist_list_list$)
(declare-fun cons$g (A_llist_list$ A_llist_list_list$ )A_llist_list_list$)
(declare-fun nil$h ()A_list_list$)
(declare-fun hd$h (A_list_list$)A_list$)
(declare-fun tl$h (A_list_list$)A_list_list$)
(declare-fun cons$h (A_list$ A_list_list$ )A_list_list$)
(declare-fun y$ ()A_llist$ )
(declare-fun us$ ()A_llist_llist$ )
(declare-fun vs$ ()A_llist_llist$ )
(declare-fun map$ (A_llist_llist_llist_list_a_llist_llist_llist_llist_fun$ A_llist_llist_llist_list_list$ )A_llist_llist_llist_llist_list$ )
(declare-fun xss$ ()A_llist_llist$ )
(declare-fun drop$ (Nat$ A_llist_llist_llist_list$ )A_llist_llist_llist_list$ )
(declare-fun last$ (A_llist_llist_llist_list$ )A_llist_llist_llist$ )
(declare-fun map$a (A_llist_llist_list_a_llist_llist_llist_fun$ A_llist_llist_list_list$ )A_llist_llist_llist_list$ )
(declare-fun map$b (A_llist_list_a_llist_llist_fun$ A_llist_list_list$ )A_llist_llist_list$ )
(declare-fun map$c (A_list_a_llist_fun$ A_list_list$ )A_llist_list$ )
(declare-fun drop$a (Nat$ A_list$ )A_list$ )
(declare-fun drop$b (Nat$ A_llist_llist_list$ )A_llist_llist_list$ )
(declare-fun drop$c (Nat$ A_llist_list$ )A_llist_list$ )
(declare-fun last$a (A_list$ )A$ )
(declare-fun last$b (A_llist_llist_list$ )A_llist_llist$ )
(declare-fun last$c (A_llist_list$ )A_llist$ )
(declare-fun llast$ (A_llist_llist_llist_llist$ )A_llist_llist_llist$ )
(declare-fun lnull$ (A_llist_llist_llist_llist$ )Bool )
(declare-fun concat$ (A_llist_llist_llist_list_list$ )A_llist_llist_llist_list$ )
(declare-fun ldropn$ (Nat$ A_llist_llist_llist_llist$ )A_llist_llist_llist_llist$ )
(declare-fun llast$a (A_llist$ )A$ )
(declare-fun llast$b (A_llist_llist_llist$ )A_llist_llist$ )
(declare-fun llast$c (A_llist_llist$ )A_llist$ )
(declare-fun lnull$a (A_llist_llist_llist$ )Bool )
(declare-fun lnull$b (A_llist_llist$ )Bool )
(declare-fun lnull$c (A_llist$ )Bool )
(declare-fun thesis$ ()Bool )
(declare-fun concat$a (A_llist_llist_list_list$ )A_llist_llist_list$ )
(declare-fun concat$b (A_llist_list_list$ )A_llist_list$ )
(declare-fun concat$c (A_list_list$ )A_list$ )
(declare-fun fun_app$ (A_llist_list_a_llist_llist_fun$ A_llist_list$ )A_llist_llist$ )
(declare-fun lappend$ (A_llist_llist$ A_llist_llist$ )A_llist_llist$ )
(declare-fun lconcat$ (A_llist_llist_llist_llist_llist$ )A_llist_llist_llist_llist$ )
(declare-fun ldropn$a (Nat$ A_llist$ )A_llist$ )
(declare-fun ldropn$b (Nat$ A_llist_llist_llist$ )A_llist_llist_llist$ )
(declare-fun ldropn$c (Nat$ A_llist_llist$ )A_llist_llist$ )
(declare-fun lfinite$ (A_llist_llist$ )Bool )
(declare-fun list_of$ (A_llist_llist_llist_llist$ )A_llist_llist_llist_list$ )
(declare-fun distinct$ (A_llist_llist_llist_list$ )Bool )
(declare-fun fun_app$a (A_llist_llist_llist_list_a_llist_llist_llist_llist_fun$ A_llist_llist_llist_list$ )A_llist_llist_llist_llist$ )
(declare-fun fun_app$b (A_list_a_llist_fun$ A_list$ )A_llist$ )
(declare-fun fun_app$c (A_llist_llist_list_a_llist_llist_llist_fun$ A_llist_llist_list$ )A_llist_llist_llist$ )
(declare-fun lconcat$a (A_llist_llist_llist_llist$ )A_llist_llist_llist$ )
(declare-fun lconcat$b (A_llist_llist_llist$ )A_llist_llist$ )
(declare-fun lconcat$c (A_llist_llist$ )A_llist$ )
(declare-fun lfinite$a (A_llist_llist_llist_llist$ )Bool )
(declare-fun lfinite$b (A_llist$ )Bool )
(declare-fun lfinite$c (A_llist_llist_llist$ )Bool )
(declare-fun list_of$a (A_llist$ )A_list$ )
(declare-fun list_of$b (A_llist_llist_llist$ )A_llist_llist_list$ )
(declare-fun list_of$c (A_llist_llist$ )A_llist_list$ )
(declare-fun llist_of$ ()A_llist_list_a_llist_llist_fun$ )
(declare-fun distinct$a (A_list$ )Bool )
(declare-fun distinct$b (A_llist_llist_list$ )Bool )
(declare-fun distinct$c (A_llist_list$ )Bool )
(declare-fun ldistinct$ (A_llist_llist_llist_llist$ )Bool )
(declare-fun llist_of$a ()A_llist_llist_llist_list_a_llist_llist_llist_llist_fun$ )
(declare-fun llist_of$b ()A_list_a_llist_fun$ )
(declare-fun llist_of$c ()A_llist_llist_list_a_llist_llist_llist_fun$ )
(declare-fun llist_of$d (A_llist_llist_llist_llist_list$ )A_llist_llist_llist_llist_llist$ )
(declare-fun ldistinct$a (A_llist$ )Bool )
(declare-fun ldistinct$b (A_llist_llist_llist$ )Bool )
(declare-fun ldistinct$c (A_llist_llist$ )Bool )
(assert (! (not thesis$ ):named a0 ))
(assert (! (forall ((?v0 A_llist_list$ ))(=> (= us$ (fun_app$ llist_of$ ?v0 ))thesis$ )):named a1 ))
(assert (! (forall ((?v0 A_llist_llist_llist_list$ )(?v1 A_llist_llist_llist_list$ ))(= (= (fun_app$a llist_of$a ?v0 )(fun_app$a llist_of$a ?v1 ))(= ?v0 ?v1 ))):named a2 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_list$ ))(= (= (fun_app$b llist_of$b ?v0 )(fun_app$b llist_of$b ?v1 ))(= ?v0 ?v1 ))):named a3 ))
(assert (! (forall ((?v0 A_llist_llist_list$ )(?v1 A_llist_llist_list$ ))(= (= (fun_app$c llist_of$c ?v0 )(fun_app$c llist_of$c ?v1 ))(= ?v0 ?v1 ))):named a4 ))
(assert (! (forall ((?v0 A_llist_list$ )(?v1 A_llist_list$ ))(= (= (fun_app$ llist_of$ ?v0 )(fun_app$ llist_of$ ?v1 ))(= ?v0 ?v1 ))):named a5 ))
(assert (! (lfinite$ us$ ):named a6 ))
(assert (! (forall ((?v0 A_llist_llist_llist_list$ ))(= (list_of$ (fun_app$a llist_of$a ?v0 ))?v0 )):named a7 ))
(assert (! (forall ((?v0 A_list$ ))(= (list_of$a (fun_app$b llist_of$b ?v0 ))?v0 )):named a8 ))
(assert (! (forall ((?v0 A_llist_llist_list$ ))(= (list_of$b (fun_app$c llist_of$c ?v0 ))?v0 )):named a9 ))
(assert (! (forall ((?v0 A_llist_list$ ))(= (list_of$c (fun_app$ llist_of$ ?v0 ))?v0 )):named a10 ))
(assert (! (forall ((?v0 A_llist_llist_llist_list_list$ ))(= (lconcat$ (llist_of$d (map$ llist_of$a ?v0 )))(fun_app$a llist_of$a (concat$ ?v0 )))):named a11 ))
(assert (! (forall ((?v0 A_llist_llist_list_list$ ))(= (lconcat$a (fun_app$a llist_of$a (map$a llist_of$c ?v0 )))(fun_app$c llist_of$c (concat$a ?v0 )))):named a12 ))
(assert (! (forall ((?v0 A_llist_list_list$ ))(= (lconcat$b (fun_app$c llist_of$c (map$b llist_of$ ?v0 )))(fun_app$ llist_of$ (concat$b ?v0 )))):named a13 ))
(assert (! (forall ((?v0 A_list_list$ ))(= (lconcat$c (fun_app$ llist_of$ (map$c llist_of$b ?v0 )))(fun_app$b llist_of$b (concat$c ?v0 )))):named a14 ))
(assert (! (forall ((?v0 A_llist_llist_llist_list$ ))(lfinite$a (fun_app$a llist_of$a ?v0 ))):named a15 ))
(assert (! (forall ((?v0 A_list$ ))(lfinite$b (fun_app$b llist_of$b ?v0 ))):named a16 ))
(assert (! (forall ((?v0 A_llist_llist_list$ ))(lfinite$c (fun_app$c llist_of$c ?v0 ))):named a17 ))
(assert (! (forall ((?v0 A_llist_list$ ))(lfinite$ (fun_app$ llist_of$ ?v0 ))):named a18 ))
(assert (! (= xss$ (lappend$ us$ (lCons$a y$ vs$ ))):named a19 ))
(assert (! (forall ((?v0 A_llist_llist_llist_list$ ))(= (llast$ (fun_app$a llist_of$a ?v0 ))(last$ ?v0 ))):named a20 ))
(assert (! (forall ((?v0 A_list$ ))(= (llast$a (fun_app$b llist_of$b ?v0 ))(last$a ?v0 ))):named a21 ))
(assert (! (forall ((?v0 A_llist_llist_list$ ))(= (llast$b (fun_app$c llist_of$c ?v0 ))(last$b ?v0 ))):named a22 ))
(assert (! (forall ((?v0 A_llist_list$ ))(= (llast$c (fun_app$ llist_of$ ?v0 ))(last$c ?v0 ))):named a23 ))
(assert (! (forall ((?v0 A_llist_llist_llist_llist$ ))(=> (lfinite$a ?v0 )(= (fun_app$a llist_of$a (list_of$ ?v0 ))?v0 ))):named a24 ))
(assert (! (forall ((?v0 A_llist$ ))(=> (lfinite$b ?v0 )(= (fun_app$b llist_of$b (list_of$a ?v0 ))?v0 ))):named a25 ))
(assert (! (forall ((?v0 A_llist_llist_llist$ ))(=> (lfinite$c ?v0 )(= (fun_app$c llist_of$c (list_of$b ?v0 ))?v0 ))):named a26 ))
(assert (! (forall ((?v0 A_llist_llist$ ))(=> (lfinite$ ?v0 )(= (fun_app$ llist_of$ (list_of$c ?v0 ))?v0 ))):named a27 ))
(assert (! (forall ((?v0 A_llist_llist_llist_list$ ))(= (lhd$c (fun_app$a llist_of$a ?v0 ))(hd$a ?v0 ))):named a28 ))
(assert (! (forall ((?v0 A_list$ ))(= (lhd$ (fun_app$b llist_of$b ?v0 ))(hd$b ?v0 ))):named a29 ))
(assert (! (forall ((?v0 A_llist_llist_list$ ))(= (lhd$b (fun_app$c llist_of$c ?v0 ))(hd$c ?v0 ))):named a30 ))
(assert (! (forall ((?v0 A_llist_list$ ))(= (lhd$a (fun_app$ llist_of$ ?v0 ))(hd$ ?v0 ))):named a31 ))
(assert (! (forall ((?v0 A_llist_llist_llist_list$ ))(= (ldistinct$ (fun_app$a llist_of$a ?v0 ))(distinct$ ?v0 ))):named a32 ))
(assert (! (forall ((?v0 A_list$ ))(= (ldistinct$a (fun_app$b llist_of$b ?v0 ))(distinct$a ?v0 ))):named a33 ))
(assert (! (forall ((?v0 A_llist_llist_list$ ))(= (ldistinct$b (fun_app$c llist_of$c ?v0 ))(distinct$b ?v0 ))):named a34 ))
(assert (! (forall ((?v0 A_llist_list$ ))(= (ldistinct$c (fun_app$ llist_of$ ?v0 ))(distinct$c ?v0 ))):named a35 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_llist_llist_llist_list$ ))(= (ldropn$ ?v0 (fun_app$a llist_of$a ?v1 ))(fun_app$a llist_of$a (drop$ ?v0 ?v1 )))):named a36 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_list$ ))(= (ldropn$a ?v0 (fun_app$b llist_of$b ?v1 ))(fun_app$b llist_of$b (drop$a ?v0 ?v1 )))):named a37 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_llist_llist_list$ ))(= (ldropn$b ?v0 (fun_app$c llist_of$c ?v1 ))(fun_app$c llist_of$c (drop$b ?v0 ?v1 )))):named a38 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_llist_list$ ))(= (ldropn$c ?v0 (fun_app$ llist_of$ ?v1 ))(fun_app$ llist_of$ (drop$c ?v0 ?v1 )))):named a39 ))
(assert (! (forall ((?v0 A_llist_llist_llist_list$ ))(= (lnull$ (fun_app$a llist_of$a ?v0 ))(= ?v0 nil$a ))):named a40 ))
(assert (! (forall ((?v0 A_llist_llist_list$ ))(= (lnull$a (fun_app$c llist_of$c ?v0 ))(= ?v0 nil$c ))):named a41 ))
(assert (! (forall ((?v0 A_llist_list$ ))(= (lnull$b (fun_app$ llist_of$ ?v0 ))(= ?v0 nil$ ))):named a42 ))
(assert (! (forall ((?v0 A_list$ ))(= (lnull$c (fun_app$b llist_of$b ?v0 ))(= ?v0 nil$b ))):named a43 ))
(assert (! (forall ((?v0 A_llist_llist_llist_list$ ))(= (ltl$c (fun_app$a llist_of$a ?v0 ))(fun_app$a llist_of$a (tl$a ?v0 )))):named a44 ))
(assert (! (forall ((?v0 A_list$ ))(= (ltl$ (fun_app$b llist_of$b ?v0 ))(fun_app$b llist_of$b (tl$b ?v0 )))):named a45 ))
(assert (! (forall ((?v0 A_llist_llist_list$ ))(= (ltl$b (fun_app$c llist_of$c ?v0 ))(fun_app$c llist_of$c (tl$c ?v0 )))):named a46 ))
(assert (! (forall ((?v0 A_llist_list$ ))(= (ltl$a (fun_app$ llist_of$ ?v0 ))(fun_app$ llist_of$ (tl$ ?v0 )))):named a47 ))
(assert (! (not (lnull$c y$ )):named a48 ))
(assert (! (not (lnull$c (lconcat$c xss$ ))):named a49 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist_llist$ )(?v2 A_llist$ )(?v3 A_llist_llist$ ))(= (= (lCons$a ?v0 ?v1 )(lCons$a ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a50 ))
(check-sat )
;(get-unsat-core )
