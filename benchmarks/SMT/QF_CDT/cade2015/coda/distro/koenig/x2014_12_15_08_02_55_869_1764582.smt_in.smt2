;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort A_treeFI$ 0 )
(declare-codatatypes ()((A_stream$ (sCons$ (shd$ A$ )(stl$ A_stream$ )))))
(declare-fun tr$ ()A_treeFI$ )
(declare-fun konigPath$ (A_treeFI$ )A_stream$ )
(declare-fun infiniteTr$ (A_treeFI$ )Bool )
(declare-fun properPath$ (A_stream$ A_treeFI$ )Bool )
(assert (! (not (properPath$ (konigPath$ tr$ )tr$ )):named a0 ))
(assert (! (infiniteTr$ tr$ ):named a1 ))
(check-sat )
;(get-unsat-core )
