;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort B$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_a_fun$ 0 )
(declare-sort B_b_fun$ 0 )
(declare-sort A_a_bool_fun_fun$ 0 )
(declare-sort A_b_bool_fun_fun$ 0 )
(declare-sort B_a_bool_fun_fun$ 0 )
(declare-sort B_b_bool_fun_fun$ 0 )
(declare-sort A_a_prod_a_a_prod_fun$ 0 )
(declare-sort A_b_prod_a_b_prod_fun$ 0 )
(declare-sort B_a_prod_b_a_prod_fun$ 0 )
(declare-sort B_b_prod_b_b_prod_fun$ 0 )
(declare-sort A_a_a_prod_bool_fun_fun$ 0 )
(declare-sort A_a_b_prod_bool_fun_fun$ 0 )
(declare-sort B_a_a_prod_bool_fun_fun$ 0 )
(declare-sort B_a_b_prod_bool_fun_fun$ 0 )
(declare-sort B_b_a_prod_bool_fun_fun$ 0 )
(declare-sort B_b_b_prod_bool_fun_fun$ 0 )
(declare-sort A_a_b_prod_prod_a_a_b_prod_prod_fun$ 0 )
(declare-sort A_b_a_prod_prod_a_b_a_prod_prod_fun$ 0 )
(declare-sort A_b_b_prod_prod_a_b_b_prod_prod_fun$ 0 )
(declare-sort B_a_a_prod_prod_b_a_a_prod_prod_fun$ 0 )
(declare-sort B_llist$ 0)
(declare-sort A_llist$ 0)
(declare-fun lNil$ ()B_llist$)
(declare-fun lhd$ (B_llist$)B$)
(declare-fun ltl$ (B_llist$)B_llist$)
(declare-fun lCons$ (B$ B_llist$ )B_llist$)
(declare-fun lNil$a ()A_llist$)
(declare-fun lhd$a (A_llist$)A$)
(declare-fun ltl$a (A_llist$)A_llist$)
(declare-fun lCons$a (A$ A_llist$ )A_llist$)
(declare-datatypes ()((A_a_prod$ (pair$ (fst$ A$ )(snd$ A$ )))))
(declare-sort A_a_prod_llist$ 0)
(declare-fun lNil$b ()A_a_prod_llist$)
(declare-fun lhd$b (A_a_prod_llist$)A_a_prod$)
(declare-fun ltl$b (A_a_prod_llist$)A_a_prod_llist$)
(declare-fun lCons$b (A_a_prod$ A_a_prod_llist$ )A_a_prod_llist$)
(declare-datatypes ()((A_b_prod$ (pair$a (fst$a A$ )(snd$a B$ )))))
(declare-sort A_b_prod_llist$ 0)
(declare-fun lNil$c ()A_b_prod_llist$)
(declare-fun lhd$c (A_b_prod_llist$)A_b_prod$)
(declare-fun ltl$c (A_b_prod_llist$)A_b_prod_llist$)
(declare-fun lCons$c (A_b_prod$ A_b_prod_llist$ )A_b_prod_llist$)
(declare-datatypes ()((B_a_prod$ (pair$b (fst$b B$ )(snd$b A$ )))))
(declare-sort B_a_prod_llist$ 0)
(declare-fun lNil$d ()B_a_prod_llist$)
(declare-fun lhd$d (B_a_prod_llist$)B_a_prod$)
(declare-fun ltl$d (B_a_prod_llist$)B_a_prod_llist$)
(declare-fun lCons$d (B_a_prod$ B_a_prod_llist$ )B_a_prod_llist$)
(declare-datatypes ()((B_b_prod$ (pair$c (fst$c B$ )(snd$c B$ )))))
(declare-sort B_b_prod_llist$ 0)
(declare-fun lNil$e ()B_b_prod_llist$)
(declare-fun lhd$e (B_b_prod_llist$)B_b_prod$)
(declare-fun ltl$e (B_b_prod_llist$)B_b_prod_llist$)
(declare-fun lCons$e (B_b_prod$ B_b_prod_llist$ )B_b_prod_llist$)
(declare-datatypes ()((B_a_a_prod_prod$ (pair$d (fst$d B$ )(snd$d A_a_prod$ )))))
(declare-sort B_a_a_prod_prod_llist$ 0)
(declare-fun lNil$f ()B_a_a_prod_prod_llist$)
(declare-fun lhd$f (B_a_a_prod_prod_llist$)B_a_a_prod_prod$)
(declare-fun ltl$f (B_a_a_prod_prod_llist$)B_a_a_prod_prod_llist$)
(declare-fun lCons$f (B_a_a_prod_prod$ B_a_a_prod_prod_llist$ )B_a_a_prod_prod_llist$)
(declare-datatypes ()((A_b_b_prod_prod$ (pair$e (fst$e A$ )(snd$e B_b_prod$ )))))
(declare-sort A_b_b_prod_prod_llist$ 0)
(declare-fun lNil$g ()A_b_b_prod_prod_llist$)
(declare-fun lhd$g (A_b_b_prod_prod_llist$)A_b_b_prod_prod$)
(declare-fun ltl$g (A_b_b_prod_prod_llist$)A_b_b_prod_prod_llist$)
(declare-fun lCons$g (A_b_b_prod_prod$ A_b_b_prod_prod_llist$ )A_b_b_prod_prod_llist$)
(declare-datatypes ()((A_b_a_prod_prod$ (pair$f (fst$f A$ )(snd$f B_a_prod$ )))))
(declare-sort A_b_a_prod_prod_llist$ 0)
(declare-fun lNil$h ()A_b_a_prod_prod_llist$)
(declare-fun lhd$h (A_b_a_prod_prod_llist$)A_b_a_prod_prod$)
(declare-fun ltl$h (A_b_a_prod_prod_llist$)A_b_a_prod_prod_llist$)
(declare-fun lCons$h (A_b_a_prod_prod$ A_b_a_prod_prod_llist$ )A_b_a_prod_prod_llist$)
(declare-datatypes ()((A_a_b_prod_prod$ (pair$g (fst$g A$ )(snd$g A_b_prod$ )))))
(declare-sort A_a_b_prod_prod_llist$ 0)
(declare-fun lNil$i ()A_a_b_prod_prod_llist$)
(declare-fun lhd$i (A_a_b_prod_prod_llist$)A_a_b_prod_prod$)
(declare-fun ltl$i (A_a_b_prod_prod_llist$)A_a_b_prod_prod_llist$)
(declare-fun lCons$i (A_a_b_prod_prod$ A_a_b_prod_prod_llist$ )A_a_b_prod_prod_llist$)
(declare-datatypes ()((B_a_b_prod_prod$ (pair$h (fst$h B$ )(snd$h A_b_prod$ )))))
(declare-sort B_a_b_prod_prod_llist$ 0)
(declare-fun lNil$j ()B_a_b_prod_prod_llist$)
(declare-fun lhd$j (B_a_b_prod_prod_llist$)B_a_b_prod_prod$)
(declare-fun ltl$j (B_a_b_prod_prod_llist$)B_a_b_prod_prod_llist$)
(declare-fun lCons$j (B_a_b_prod_prod$ B_a_b_prod_prod_llist$ )B_a_b_prod_prod_llist$)
(declare-datatypes ()((B_b_a_prod_prod$ (pair$i (fst$i B$ )(snd$i B_a_prod$ )))))
(declare-sort B_b_a_prod_prod_llist$ 0)
(declare-fun lNil$k ()B_b_a_prod_prod_llist$)
(declare-fun lhd$k (B_b_a_prod_prod_llist$)B_b_a_prod_prod$)
(declare-fun ltl$k (B_b_a_prod_prod_llist$)B_b_a_prod_prod_llist$)
(declare-fun lCons$k (B_b_a_prod_prod$ B_b_a_prod_prod_llist$ )B_b_a_prod_prod_llist$)
(declare-datatypes ()((B_b_b_prod_prod$ (pair$j (fst$j B$ )(snd$j B_b_prod$ )))))
(declare-sort B_b_b_prod_prod_llist$ 0)
(declare-fun lNil$l ()B_b_b_prod_prod_llist$)
(declare-fun lhd$l (B_b_b_prod_prod_llist$)B_b_b_prod_prod$)
(declare-fun ltl$l (B_b_b_prod_prod_llist$)B_b_b_prod_prod_llist$)
(declare-fun lCons$l (B_b_b_prod_prod$ B_b_b_prod_prod_llist$ )B_b_b_prod_prod_llist$)
(declare-datatypes ()((A_a_a_prod_prod$ (pair$k (fst$k A$ )(snd$k A_a_prod$ )))))
(declare-sort A_a_a_prod_prod_llist$ 0)
(declare-fun lNil$m ()A_a_a_prod_prod_llist$)
(declare-fun lhd$m (A_a_a_prod_prod_llist$)A_a_a_prod_prod$)
(declare-fun ltl$m (A_a_a_prod_prod_llist$)A_a_a_prod_prod_llist$)
(declare-fun lCons$m (A_a_a_prod_prod$ A_a_a_prod_prod_llist$ )A_a_a_prod_prod_llist$)
(declare-datatypes ()((B_list$ (nil$ )(cons$ (hd$ B$ )(tl$ B_list$ )))(A_list$ (nil$a )(cons$a (hd$a A$ )(tl$a A_list$ )))(A_a_prod_list$ (nil$b )(cons$b (hd$b A_a_prod$ )(tl$b A_a_prod_list$ )))(A_b_prod_list$ (nil$c )(cons$c (hd$c A_b_prod$ )(tl$c A_b_prod_list$ )))(B_a_prod_list$ (nil$d )(cons$d (hd$d B_a_prod$ )(tl$d B_a_prod_list$ )))(B_b_prod_list$ (nil$e )(cons$e (hd$e B_b_prod$ )(tl$e B_b_prod_list$ )))(B_a_a_prod_prod_list$ (nil$f )(cons$f (hd$f B_a_a_prod_prod$ )(tl$f B_a_a_prod_prod_list$ )))(A_b_b_prod_prod_list$ (nil$g )(cons$g (hd$g A_b_b_prod_prod$ )(tl$g A_b_b_prod_prod_list$ )))(A_b_a_prod_prod_list$ (nil$h )(cons$h (hd$h A_b_a_prod_prod$ )(tl$h A_b_a_prod_prod_list$ )))(A_a_b_prod_prod_list$ (nil$i )(cons$i (hd$i A_a_b_prod_prod$ )(tl$i A_a_b_prod_prod_list$ )))))
(declare-fun p$ ()A_b_bool_fun_fun$ )
(declare-fun xs$ ()A_llist$ )
(declare-fun ys$ ()B_llist$ )
(declare-fun xs$a ()A_llist$ )
(declare-fun ys$a ()B_llist$ )
(declare-fun lzip$ (B_llist$ B_llist$ )B_b_prod_llist$ )
(declare-fun lzip$a (B_llist$ A_llist$ )B_a_prod_llist$ )
(declare-fun lzip$b (A_llist$ B_llist$ )A_b_prod_llist$ )
(declare-fun lzip$c (A_llist$ A_llist$ )A_a_prod_llist$ )
(declare-fun lzip$d (B_llist$ A_a_prod_llist$ )B_a_a_prod_prod_llist$ )
(declare-fun lzip$e (B_llist$ A_b_prod_llist$ )B_a_b_prod_prod_llist$ )
(declare-fun lzip$f (B_llist$ B_a_prod_llist$ )B_b_a_prod_prod_llist$ )
(declare-fun lzip$g (B_llist$ B_b_prod_llist$ )B_b_b_prod_prod_llist$ )
(declare-fun lzip$h (A_llist$ A_a_prod_llist$ )A_a_a_prod_prod_llist$ )
(declare-fun lzip$i (A_llist$ A_b_prod_llist$ )A_a_b_prod_prod_llist$ )
(declare-fun ldropn$ (Nat$ B_llist$ )B_llist$ )
(declare-fun lappend$ (A_a_b_prod_prod_llist$ A_a_b_prod_prod_llist$ )A_a_b_prod_prod_llist$ )
(declare-fun ldropn$a (Nat$ A_llist$ )A_llist$ )
(declare-fun ldropn$b (Nat$ A_a_prod_llist$ )A_a_prod_llist$ )
(declare-fun ldropn$c (Nat$ A_b_prod_llist$ )A_b_prod_llist$ )
(declare-fun ldropn$d (Nat$ B_a_prod_llist$ )B_a_prod_llist$ )
(declare-fun ldropn$e (Nat$ B_b_prod_llist$ )B_b_prod_llist$ )
(declare-fun ldropn$f (Nat$ B_a_a_prod_prod_llist$ )B_a_a_prod_prod_llist$ )
(declare-fun ldropn$g (Nat$ A_b_b_prod_prod_llist$ )A_b_b_prod_prod_llist$ )
(declare-fun ldropn$h (Nat$ A_b_a_prod_prod_llist$ )A_b_a_prod_prod_llist$ )
(declare-fun ldropn$i (Nat$ A_a_b_prod_prod_llist$ )A_a_b_prod_prod_llist$ )
(declare-fun lfinite$ (B_llist$ )Bool )
(declare-fun iterates$ (B_b_fun$ B$ )B_llist$ )
(declare-fun lappend$a (A_a_a_prod_prod_llist$ A_a_a_prod_prod_llist$ )A_a_a_prod_prod_llist$ )
(declare-fun lappend$b (A_a_prod_llist$ A_a_prod_llist$ )A_a_prod_llist$ )
(declare-fun lappend$c (A_b_prod_llist$ A_b_prod_llist$ )A_b_prod_llist$ )
(declare-fun lappend$d (B_a_prod_llist$ B_a_prod_llist$ )B_a_prod_llist$ )
(declare-fun lappend$e (B_b_prod_llist$ B_b_prod_llist$ )B_b_prod_llist$ )
(declare-fun lappend$f (B_llist$ B_llist$ )B_llist$ )
(declare-fun lappend$g (A_llist$ A_llist$ )A_llist$ )
(declare-fun lfinite$a (A_llist$ )Bool )
(declare-fun lfinite$b (A_a_prod_llist$ )Bool )
(declare-fun lfinite$c (A_b_prod_llist$ )Bool )
(declare-fun lfinite$d (B_a_prod_llist$ )Bool )
(declare-fun lfinite$e (B_b_prod_llist$ )Bool )
(declare-fun lfinite$f (B_a_a_prod_prod_llist$ )Bool )
(declare-fun lfinite$g (A_b_b_prod_prod_llist$ )Bool )
(declare-fun lfinite$h (A_b_a_prod_prod_llist$ )Bool )
(declare-fun lfinite$i (A_a_b_prod_prod_llist$ )Bool )
(declare-fun lfinite$j (B_a_b_prod_prod_llist$ )Bool )
(declare-fun lfinite$k (B_b_a_prod_prod_llist$ )Bool )
(declare-fun lfinite$l (B_b_b_prod_prod_llist$ )Bool )
(declare-fun lfinite$m (A_a_a_prod_prod_llist$ )Bool )
(declare-fun llist_of$ (B_list$ )B_llist$ )
(declare-fun iterates$a (A_a_fun$ A$ )A_llist$ )
(declare-fun iterates$b (A_a_prod_a_a_prod_fun$ A_a_prod$ )A_a_prod_llist$ )
(declare-fun iterates$c (A_b_prod_a_b_prod_fun$ A_b_prod$ )A_b_prod_llist$ )
(declare-fun iterates$d (B_a_prod_b_a_prod_fun$ B_a_prod$ )B_a_prod_llist$ )
(declare-fun iterates$e (B_b_prod_b_b_prod_fun$ B_b_prod$ )B_b_prod_llist$ )
(declare-fun iterates$f (B_a_a_prod_prod_b_a_a_prod_prod_fun$ B_a_a_prod_prod$ )B_a_a_prod_prod_llist$ )
(declare-fun iterates$g (A_b_b_prod_prod_a_b_b_prod_prod_fun$ A_b_b_prod_prod$ )A_b_b_prod_prod_llist$ )
(declare-fun iterates$h (A_b_a_prod_prod_a_b_a_prod_prod_fun$ A_b_a_prod_prod$ )A_b_a_prod_prod_llist$ )
(declare-fun iterates$i (A_a_b_prod_prod_a_a_b_prod_prod_fun$ A_a_b_prod_prod$ )A_a_b_prod_prod_llist$ )
(declare-fun llist_of$a (A_list$ )A_llist$ )
(declare-fun llist_of$b (A_a_prod_list$ )A_a_prod_llist$ )
(declare-fun llist_of$c (A_b_prod_list$ )A_b_prod_llist$ )
(declare-fun llist_of$d (B_a_prod_list$ )B_a_prod_llist$ )
(declare-fun llist_of$e (B_b_prod_list$ )B_b_prod_llist$ )
(declare-fun llist_of$f (B_a_a_prod_prod_list$ )B_a_a_prod_prod_llist$ )
(declare-fun llist_of$g (A_b_b_prod_prod_list$ )A_b_b_prod_prod_llist$ )
(declare-fun llist_of$h (A_b_a_prod_prod_list$ )A_b_a_prod_prod_llist$ )
(declare-fun llist_of$i (A_a_b_prod_prod_list$ )A_a_b_prod_prod_llist$ )
(declare-fun llist_all2$ (A_b_bool_fun_fun$ A_llist$ B_llist$ )Bool )
(declare-fun llist_all2$a (B_b_bool_fun_fun$ B_llist$ B_llist$ )Bool )
(declare-fun llist_all2$b (B_a_bool_fun_fun$ B_llist$ A_llist$ )Bool )
(declare-fun llist_all2$c (A_a_bool_fun_fun$ A_llist$ A_llist$ )Bool )
(declare-fun llist_all2$d (B_a_a_prod_bool_fun_fun$ B_llist$ A_a_prod_llist$ )Bool )
(declare-fun llist_all2$e (B_a_b_prod_bool_fun_fun$ B_llist$ A_b_prod_llist$ )Bool )
(declare-fun llist_all2$f (B_b_a_prod_bool_fun_fun$ B_llist$ B_a_prod_llist$ )Bool )
(declare-fun llist_all2$g (B_b_b_prod_bool_fun_fun$ B_llist$ B_b_prod_llist$ )Bool )
(declare-fun llist_all2$h (A_a_a_prod_bool_fun_fun$ A_llist$ A_a_prod_llist$ )Bool )
(declare-fun llist_all2$i (A_a_b_prod_bool_fun_fun$ A_llist$ A_b_prod_llist$ )Bool )
(declare-fun lstrict_prefix$ (B_llist$ B_llist$ )Bool )
(declare-fun lstrict_prefix$a (A_llist$ A_llist$ )Bool )
(declare-fun lstrict_prefix$b (A_a_prod_llist$ A_a_prod_llist$ )Bool )
(declare-fun lstrict_prefix$c (A_b_prod_llist$ A_b_prod_llist$ )Bool )
(declare-fun lstrict_prefix$d (B_a_prod_llist$ B_a_prod_llist$ )Bool )
(declare-fun lstrict_prefix$e (B_b_prod_llist$ B_b_prod_llist$ )Bool )
(declare-fun lstrict_prefix$f (B_a_a_prod_prod_llist$ B_a_a_prod_prod_llist$ )Bool )
(declare-fun lstrict_prefix$g (A_b_b_prod_prod_llist$ A_b_b_prod_prod_llist$ )Bool )
(declare-fun lstrict_prefix$h (A_b_a_prod_prod_llist$ A_b_a_prod_prod_llist$ )Bool )
(declare-fun lstrict_prefix$i (A_a_b_prod_prod_llist$ A_a_b_prod_prod_llist$ )Bool )
(assert (! (not (not (lfinite$ ys$ ))):named a0 ))
(assert (! (llist_all2$ p$ xs$ ys$ ):named a1 ))
(assert (! (=> (and (lfinite$a xs$ )(lfinite$ ys$ ))(llist_all2$ p$ xs$a ys$a )):named a2 ))
(assert (! (forall ((?v0 B_b_bool_fun_fun$ )(?v1 B_llist$ )(?v2 B_llist$ ))(=> (llist_all2$a ?v0 ?v1 ?v2 )(= (lfinite$ ?v1 )(lfinite$ ?v2 )))):named a3 ))
(assert (! (forall ((?v0 B_a_bool_fun_fun$ )(?v1 B_llist$ )(?v2 A_llist$ ))(=> (llist_all2$b ?v0 ?v1 ?v2 )(= (lfinite$ ?v1 )(lfinite$a ?v2 )))):named a4 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A_llist$ )(?v2 A_llist$ ))(=> (llist_all2$c ?v0 ?v1 ?v2 )(= (lfinite$a ?v1 )(lfinite$a ?v2 )))):named a5 ))
(assert (! (forall ((?v0 A_b_bool_fun_fun$ )(?v1 A_llist$ )(?v2 B_llist$ ))(=> (llist_all2$ ?v0 ?v1 ?v2 )(= (lfinite$a ?v1 )(lfinite$ ?v2 )))):named a6 ))
(assert (! (forall ((?v0 B_a_a_prod_bool_fun_fun$ )(?v1 B_llist$ )(?v2 A_a_prod_llist$ ))(=> (llist_all2$d ?v0 ?v1 ?v2 )(= (lfinite$ ?v1 )(lfinite$b ?v2 )))):named a7 ))
(assert (! (forall ((?v0 B_a_b_prod_bool_fun_fun$ )(?v1 B_llist$ )(?v2 A_b_prod_llist$ ))(=> (llist_all2$e ?v0 ?v1 ?v2 )(= (lfinite$ ?v1 )(lfinite$c ?v2 )))):named a8 ))
(assert (! (forall ((?v0 B_b_a_prod_bool_fun_fun$ )(?v1 B_llist$ )(?v2 B_a_prod_llist$ ))(=> (llist_all2$f ?v0 ?v1 ?v2 )(= (lfinite$ ?v1 )(lfinite$d ?v2 )))):named a9 ))
(assert (! (forall ((?v0 B_b_b_prod_bool_fun_fun$ )(?v1 B_llist$ )(?v2 B_b_prod_llist$ ))(=> (llist_all2$g ?v0 ?v1 ?v2 )(= (lfinite$ ?v1 )(lfinite$e ?v2 )))):named a10 ))
(assert (! (forall ((?v0 A_a_a_prod_bool_fun_fun$ )(?v1 A_llist$ )(?v2 A_a_prod_llist$ ))(=> (llist_all2$h ?v0 ?v1 ?v2 )(= (lfinite$a ?v1 )(lfinite$b ?v2 )))):named a11 ))
(assert (! (forall ((?v0 A_a_b_prod_bool_fun_fun$ )(?v1 A_llist$ )(?v2 A_b_prod_llist$ ))(=> (llist_all2$i ?v0 ?v1 ?v2 )(= (lfinite$a ?v1 )(lfinite$c ?v2 )))):named a12 ))
(assert (! (forall ((?v0 B_llist$ )(?v1 B_llist$ ))(=> (lstrict_prefix$ ?v0 ?v1 )(lfinite$ ?v0 ))):named a13 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (lstrict_prefix$a ?v0 ?v1 )(lfinite$a ?v0 ))):named a14 ))
(assert (! (forall ((?v0 A_a_prod_llist$ )(?v1 A_a_prod_llist$ ))(=> (lstrict_prefix$b ?v0 ?v1 )(lfinite$b ?v0 ))):named a15 ))
(assert (! (forall ((?v0 A_b_prod_llist$ )(?v1 A_b_prod_llist$ ))(=> (lstrict_prefix$c ?v0 ?v1 )(lfinite$c ?v0 ))):named a16 ))
(assert (! (forall ((?v0 B_a_prod_llist$ )(?v1 B_a_prod_llist$ ))(=> (lstrict_prefix$d ?v0 ?v1 )(lfinite$d ?v0 ))):named a17 ))
(assert (! (forall ((?v0 B_b_prod_llist$ )(?v1 B_b_prod_llist$ ))(=> (lstrict_prefix$e ?v0 ?v1 )(lfinite$e ?v0 ))):named a18 ))
(assert (! (forall ((?v0 B_a_a_prod_prod_llist$ )(?v1 B_a_a_prod_prod_llist$ ))(=> (lstrict_prefix$f ?v0 ?v1 )(lfinite$f ?v0 ))):named a19 ))
(assert (! (forall ((?v0 A_b_b_prod_prod_llist$ )(?v1 A_b_b_prod_prod_llist$ ))(=> (lstrict_prefix$g ?v0 ?v1 )(lfinite$g ?v0 ))):named a20 ))
(assert (! (forall ((?v0 A_b_a_prod_prod_llist$ )(?v1 A_b_a_prod_prod_llist$ ))(=> (lstrict_prefix$h ?v0 ?v1 )(lfinite$h ?v0 ))):named a21 ))
(assert (! (forall ((?v0 A_a_b_prod_prod_llist$ )(?v1 A_a_b_prod_prod_llist$ ))(=> (lstrict_prefix$i ?v0 ?v1 )(lfinite$i ?v0 ))):named a22 ))
(assert (! (forall ((?v0 Nat$ )(?v1 B_llist$ ))(= (lfinite$ (ldropn$ ?v0 ?v1 ))(lfinite$ ?v1 ))):named a23 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_llist$ ))(= (lfinite$a (ldropn$a ?v0 ?v1 ))(lfinite$a ?v1 ))):named a24 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_prod_llist$ ))(= (lfinite$b (ldropn$b ?v0 ?v1 ))(lfinite$b ?v1 ))):named a25 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_b_prod_llist$ ))(= (lfinite$c (ldropn$c ?v0 ?v1 ))(lfinite$c ?v1 ))):named a26 ))
(assert (! (forall ((?v0 Nat$ )(?v1 B_a_prod_llist$ ))(= (lfinite$d (ldropn$d ?v0 ?v1 ))(lfinite$d ?v1 ))):named a27 ))
(assert (! (forall ((?v0 Nat$ )(?v1 B_b_prod_llist$ ))(= (lfinite$e (ldropn$e ?v0 ?v1 ))(lfinite$e ?v1 ))):named a28 ))
(assert (! (forall ((?v0 Nat$ )(?v1 B_a_a_prod_prod_llist$ ))(= (lfinite$f (ldropn$f ?v0 ?v1 ))(lfinite$f ?v1 ))):named a29 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_b_b_prod_prod_llist$ ))(= (lfinite$g (ldropn$g ?v0 ?v1 ))(lfinite$g ?v1 ))):named a30 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_b_a_prod_prod_llist$ ))(= (lfinite$h (ldropn$h ?v0 ?v1 ))(lfinite$h ?v1 ))):named a31 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_b_prod_prod_llist$ ))(= (lfinite$i (ldropn$i ?v0 ?v1 ))(lfinite$i ?v1 ))):named a32 ))
(assert (! (forall ((?v0 B_llist$ )(?v1 B_llist$ ))(= (lfinite$e (lzip$ ?v0 ?v1 ))(or (lfinite$ ?v0 )(lfinite$ ?v1 )))):named a33 ))
(assert (! (forall ((?v0 B_llist$ )(?v1 A_llist$ ))(= (lfinite$d (lzip$a ?v0 ?v1 ))(or (lfinite$ ?v0 )(lfinite$a ?v1 )))):named a34 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 B_llist$ ))(= (lfinite$c (lzip$b ?v0 ?v1 ))(or (lfinite$a ?v0 )(lfinite$ ?v1 )))):named a35 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(= (lfinite$b (lzip$c ?v0 ?v1 ))(or (lfinite$a ?v0 )(lfinite$a ?v1 )))):named a36 ))
(assert (! (forall ((?v0 B_llist$ )(?v1 A_a_prod_llist$ ))(= (lfinite$f (lzip$d ?v0 ?v1 ))(or (lfinite$ ?v0 )(lfinite$b ?v1 )))):named a37 ))
(assert (! (forall ((?v0 B_llist$ )(?v1 A_b_prod_llist$ ))(= (lfinite$j (lzip$e ?v0 ?v1 ))(or (lfinite$ ?v0 )(lfinite$c ?v1 )))):named a38 ))
(assert (! (forall ((?v0 B_llist$ )(?v1 B_a_prod_llist$ ))(= (lfinite$k (lzip$f ?v0 ?v1 ))(or (lfinite$ ?v0 )(lfinite$d ?v1 )))):named a39 ))
(assert (! (forall ((?v0 B_llist$ )(?v1 B_b_prod_llist$ ))(= (lfinite$l (lzip$g ?v0 ?v1 ))(or (lfinite$ ?v0 )(lfinite$e ?v1 )))):named a40 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_a_prod_llist$ ))(= (lfinite$m (lzip$h ?v0 ?v1 ))(or (lfinite$a ?v0 )(lfinite$b ?v1 )))):named a41 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_b_prod_llist$ ))(= (lfinite$i (lzip$i ?v0 ?v1 ))(or (lfinite$a ?v0 )(lfinite$c ?v1 )))):named a42 ))
(assert (! (= (lfinite$ lNil$ )true ):named a43 ))
(assert (! (= (lfinite$a lNil$a )true ):named a44 ))
(assert (! (= (lfinite$b lNil$b )true ):named a45 ))
(assert (! (= (lfinite$c lNil$c )true ):named a46 ))
(assert (! (= (lfinite$d lNil$d )true ):named a47 ))
(assert (! (= (lfinite$e lNil$e )true ):named a48 ))
(assert (! (= (lfinite$f lNil$f )true ):named a49 ))
(assert (! (= (lfinite$g lNil$g )true ):named a50 ))
(assert (! (= (lfinite$h lNil$h )true ):named a51 ))
(assert (! (= (lfinite$i lNil$i )true ):named a52 ))
(assert (! (forall ((?v0 B_b_fun$ )(?v1 B$ ))(not (lfinite$ (iterates$ ?v0 ?v1 )))):named a53 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A$ ))(not (lfinite$a (iterates$a ?v0 ?v1 )))):named a54 ))
(assert (! (forall ((?v0 A_a_prod_a_a_prod_fun$ )(?v1 A_a_prod$ ))(not (lfinite$b (iterates$b ?v0 ?v1 )))):named a55 ))
(assert (! (forall ((?v0 A_b_prod_a_b_prod_fun$ )(?v1 A_b_prod$ ))(not (lfinite$c (iterates$c ?v0 ?v1 )))):named a56 ))
(assert (! (forall ((?v0 B_a_prod_b_a_prod_fun$ )(?v1 B_a_prod$ ))(not (lfinite$d (iterates$d ?v0 ?v1 )))):named a57 ))
(assert (! (forall ((?v0 B_b_prod_b_b_prod_fun$ )(?v1 B_b_prod$ ))(not (lfinite$e (iterates$e ?v0 ?v1 )))):named a58 ))
(assert (! (forall ((?v0 B_a_a_prod_prod_b_a_a_prod_prod_fun$ )(?v1 B_a_a_prod_prod$ ))(not (lfinite$f (iterates$f ?v0 ?v1 )))):named a59 ))
(assert (! (forall ((?v0 A_b_b_prod_prod_a_b_b_prod_prod_fun$ )(?v1 A_b_b_prod_prod$ ))(not (lfinite$g (iterates$g ?v0 ?v1 )))):named a60 ))
(assert (! (forall ((?v0 A_b_a_prod_prod_a_b_a_prod_prod_fun$ )(?v1 A_b_a_prod_prod$ ))(not (lfinite$h (iterates$h ?v0 ?v1 )))):named a61 ))
(assert (! (forall ((?v0 A_a_b_prod_prod_a_a_b_prod_prod_fun$ )(?v1 A_a_b_prod_prod$ ))(not (lfinite$i (iterates$i ?v0 ?v1 )))):named a62 ))
(assert (! (forall ((?v0 B$ )(?v1 B_llist$ ))(! (= (lfinite$ (lCons$ ?v0 ?v1 ))(lfinite$ ?v1 )):pattern ((lCons$ ?v0 ?v1 )))):named a63 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(! (= (lfinite$a (lCons$a ?v0 ?v1 ))(lfinite$a ?v1 )):pattern ((lCons$a ?v0 ?v1 )))):named a64 ))
(assert (! (forall ((?v0 A_a_prod$ )(?v1 A_a_prod_llist$ ))(! (= (lfinite$b (lCons$b ?v0 ?v1 ))(lfinite$b ?v1 )):pattern ((lCons$b ?v0 ?v1 )))):named a65 ))
(assert (! (forall ((?v0 A_b_prod$ )(?v1 A_b_prod_llist$ ))(! (= (lfinite$c (lCons$c ?v0 ?v1 ))(lfinite$c ?v1 )):pattern ((lCons$c ?v0 ?v1 )))):named a66 ))
(assert (! (forall ((?v0 B_a_prod$ )(?v1 B_a_prod_llist$ ))(! (= (lfinite$d (lCons$d ?v0 ?v1 ))(lfinite$d ?v1 )):pattern ((lCons$d ?v0 ?v1 )))):named a67 ))
(assert (! (forall ((?v0 B_b_prod$ )(?v1 B_b_prod_llist$ ))(! (= (lfinite$e (lCons$e ?v0 ?v1 ))(lfinite$e ?v1 )):pattern ((lCons$e ?v0 ?v1 )))):named a68 ))
(assert (! (forall ((?v0 B_a_a_prod_prod$ )(?v1 B_a_a_prod_prod_llist$ ))(! (= (lfinite$f (lCons$f ?v0 ?v1 ))(lfinite$f ?v1 )):pattern ((lCons$f ?v0 ?v1 )))):named a69 ))
(assert (! (forall ((?v0 A_b_b_prod_prod$ )(?v1 A_b_b_prod_prod_llist$ ))(! (= (lfinite$g (lCons$g ?v0 ?v1 ))(lfinite$g ?v1 )):pattern ((lCons$g ?v0 ?v1 )))):named a70 ))
(assert (! (forall ((?v0 A_b_a_prod_prod$ )(?v1 A_b_a_prod_prod_llist$ ))(! (= (lfinite$h (lCons$h ?v0 ?v1 ))(lfinite$h ?v1 )):pattern ((lCons$h ?v0 ?v1 )))):named a71 ))
(assert (! (forall ((?v0 A_a_b_prod_prod$ )(?v1 A_a_b_prod_prod_llist$ ))(! (= (lfinite$i (lCons$i ?v0 ?v1 ))(lfinite$i ?v1 )):pattern ((lCons$i ?v0 ?v1 )))):named a72 ))
(assert (! (forall ((?v0 B$ )(?v1 B_llist$ ))(! (= (lfinite$ (lCons$ ?v0 ?v1 ))(lfinite$ ?v1 )):pattern ((lCons$ ?v0 ?v1 )))):named a73 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(! (= (lfinite$a (lCons$a ?v0 ?v1 ))(lfinite$a ?v1 )):pattern ((lCons$a ?v0 ?v1 )))):named a74 ))
(assert (! (forall ((?v0 A_a_prod$ )(?v1 A_a_prod_llist$ ))(! (= (lfinite$b (lCons$b ?v0 ?v1 ))(lfinite$b ?v1 )):pattern ((lCons$b ?v0 ?v1 )))):named a75 ))
(assert (! (forall ((?v0 A_b_prod$ )(?v1 A_b_prod_llist$ ))(! (= (lfinite$c (lCons$c ?v0 ?v1 ))(lfinite$c ?v1 )):pattern ((lCons$c ?v0 ?v1 )))):named a76 ))
(assert (! (forall ((?v0 B_a_prod$ )(?v1 B_a_prod_llist$ ))(! (= (lfinite$d (lCons$d ?v0 ?v1 ))(lfinite$d ?v1 )):pattern ((lCons$d ?v0 ?v1 )))):named a77 ))
(assert (! (forall ((?v0 B_b_prod$ )(?v1 B_b_prod_llist$ ))(! (= (lfinite$e (lCons$e ?v0 ?v1 ))(lfinite$e ?v1 )):pattern ((lCons$e ?v0 ?v1 )))):named a78 ))
(assert (! (forall ((?v0 B_a_a_prod_prod$ )(?v1 B_a_a_prod_prod_llist$ ))(! (= (lfinite$f (lCons$f ?v0 ?v1 ))(lfinite$f ?v1 )):pattern ((lCons$f ?v0 ?v1 )))):named a79 ))
(assert (! (forall ((?v0 A_b_b_prod_prod$ )(?v1 A_b_b_prod_prod_llist$ ))(! (= (lfinite$g (lCons$g ?v0 ?v1 ))(lfinite$g ?v1 )):pattern ((lCons$g ?v0 ?v1 )))):named a80 ))
(assert (! (forall ((?v0 A_b_a_prod_prod$ )(?v1 A_b_a_prod_prod_llist$ ))(! (= (lfinite$h (lCons$h ?v0 ?v1 ))(lfinite$h ?v1 )):pattern ((lCons$h ?v0 ?v1 )))):named a81 ))
(assert (! (forall ((?v0 A_a_b_prod_prod$ )(?v1 A_a_b_prod_prod_llist$ ))(! (= (lfinite$i (lCons$i ?v0 ?v1 ))(lfinite$i ?v1 )):pattern ((lCons$i ?v0 ?v1 )))):named a82 ))
(assert (! (forall ((?v0 B_list$ ))(lfinite$ (llist_of$ ?v0 ))):named a83 ))
(assert (! (forall ((?v0 A_list$ ))(lfinite$a (llist_of$a ?v0 ))):named a84 ))
(assert (! (forall ((?v0 A_a_prod_list$ ))(lfinite$b (llist_of$b ?v0 ))):named a85 ))
(assert (! (forall ((?v0 A_b_prod_list$ ))(lfinite$c (llist_of$c ?v0 ))):named a86 ))
(assert (! (forall ((?v0 B_a_prod_list$ ))(lfinite$d (llist_of$d ?v0 ))):named a87 ))
(assert (! (forall ((?v0 B_b_prod_list$ ))(lfinite$e (llist_of$e ?v0 ))):named a88 ))
(assert (! (forall ((?v0 B_a_a_prod_prod_list$ ))(lfinite$f (llist_of$f ?v0 ))):named a89 ))
(assert (! (forall ((?v0 A_b_b_prod_prod_list$ ))(lfinite$g (llist_of$g ?v0 ))):named a90 ))
(assert (! (forall ((?v0 A_b_a_prod_prod_list$ ))(lfinite$h (llist_of$h ?v0 ))):named a91 ))
(assert (! (forall ((?v0 A_a_b_prod_prod_list$ ))(lfinite$i (llist_of$i ?v0 ))):named a92 ))
(assert (! (forall ((?v0 B_llist$ ))(= (lfinite$ (ltl$ ?v0 ))(lfinite$ ?v0 ))):named a93 ))
(assert (! (forall ((?v0 A_llist$ ))(= (lfinite$a (ltl$a ?v0 ))(lfinite$a ?v0 ))):named a94 ))
(assert (! (forall ((?v0 A_a_prod_llist$ ))(= (lfinite$b (ltl$b ?v0 ))(lfinite$b ?v0 ))):named a95 ))
(assert (! (forall ((?v0 A_b_prod_llist$ ))(= (lfinite$c (ltl$c ?v0 ))(lfinite$c ?v0 ))):named a96 ))
(assert (! (forall ((?v0 B_a_prod_llist$ ))(= (lfinite$d (ltl$d ?v0 ))(lfinite$d ?v0 ))):named a97 ))
(assert (! (forall ((?v0 B_b_prod_llist$ ))(= (lfinite$e (ltl$e ?v0 ))(lfinite$e ?v0 ))):named a98 ))
(assert (! (forall ((?v0 B_a_a_prod_prod_llist$ ))(= (lfinite$f (ltl$f ?v0 ))(lfinite$f ?v0 ))):named a99 ))
(assert (! (forall ((?v0 A_b_b_prod_prod_llist$ ))(= (lfinite$g (ltl$g ?v0 ))(lfinite$g ?v0 ))):named a100 ))
(assert (! (forall ((?v0 A_b_a_prod_prod_llist$ ))(= (lfinite$h (ltl$h ?v0 ))(lfinite$h ?v0 ))):named a101 ))
(assert (! (forall ((?v0 A_a_b_prod_prod_llist$ ))(= (lfinite$i (ltl$i ?v0 ))(lfinite$i ?v0 ))):named a102 ))
(assert (! (forall ((?v0 A_a_b_prod_prod_llist$ )(?v1 A_a_b_prod_prod_llist$ ))(= (lfinite$i (lappend$ ?v0 ?v1 ))(and (lfinite$i ?v0 )(lfinite$i ?v1 )))):named a103 ))
(assert (! (forall ((?v0 A_a_a_prod_prod_llist$ )(?v1 A_a_a_prod_prod_llist$ ))(= (lfinite$m (lappend$a ?v0 ?v1 ))(and (lfinite$m ?v0 )(lfinite$m ?v1 )))):named a104 ))
(assert (! (forall ((?v0 A_a_prod_llist$ )(?v1 A_a_prod_llist$ ))(= (lfinite$b (lappend$b ?v0 ?v1 ))(and (lfinite$b ?v0 )(lfinite$b ?v1 )))):named a105 ))
(assert (! (forall ((?v0 A_b_prod_llist$ )(?v1 A_b_prod_llist$ ))(= (lfinite$c (lappend$c ?v0 ?v1 ))(and (lfinite$c ?v0 )(lfinite$c ?v1 )))):named a106 ))
(assert (! (forall ((?v0 B_a_prod_llist$ )(?v1 B_a_prod_llist$ ))(= (lfinite$d (lappend$d ?v0 ?v1 ))(and (lfinite$d ?v0 )(lfinite$d ?v1 )))):named a107 ))
(assert (! (forall ((?v0 B_b_prod_llist$ )(?v1 B_b_prod_llist$ ))(= (lfinite$e (lappend$e ?v0 ?v1 ))(and (lfinite$e ?v0 )(lfinite$e ?v1 )))):named a108 ))
(assert (! (forall ((?v0 B_llist$ )(?v1 B_llist$ ))(= (lfinite$ (lappend$f ?v0 ?v1 ))(and (lfinite$ ?v0 )(lfinite$ ?v1 )))):named a109 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(= (lfinite$a (lappend$g ?v0 ?v1 ))(and (lfinite$a ?v0 )(lfinite$a ?v1 )))):named a110 ))
(assert (! (not (lfinite$a xs$ )):named a111 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A$ )(?v3 A_llist$ ))(= (= (lCons$a ?v0 ?v1 )(lCons$a ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a112 ))
(assert (! (forall ((?v0 B$ )(?v1 B_llist$ )(?v2 B$ )(?v3 B_llist$ ))(= (= (lCons$ ?v0 ?v1 )(lCons$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a113 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_list$ ))(= (= (llist_of$a ?v0 )(llist_of$a ?v1 ))(= ?v0 ?v1 ))):named a114 ))
(assert (! (forall ((?v0 B_list$ )(?v1 B_list$ ))(= (= (llist_of$ ?v0 )(llist_of$ ?v1 ))(= ?v0 ?v1 ))):named a115 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A_llist$ ))(! (= (lappend$g (lCons$a ?v0 ?v1 )?v2 )(lCons$a ?v0 (lappend$g ?v1 ?v2 ))):pattern ((lappend$g (lCons$a ?v0 ?v1 )?v2 )))):named a116 ))
(assert (! (forall ((?v0 B$ )(?v1 B_llist$ )(?v2 B_llist$ ))(! (= (lappend$f (lCons$ ?v0 ?v1 )?v2 )(lCons$ ?v0 (lappend$f ?v1 ?v2 ))):pattern ((lappend$f (lCons$ ?v0 ?v1 )?v2 )))):named a117 ))
(check-sat )
;(get-unsat-core )
