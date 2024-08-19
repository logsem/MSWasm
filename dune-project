(lang dune 3.11)
(using coq 0.2)
(using mdx 0.2)
(name coq-mswasm)
(version 2.0)

(generate_opam_files true)

(package
  (name coq-mswasm)
  (synopsis "MSWasm formalisation in Coq")
  (description "MSWasm formalisation in Coq")
  (depends
   (coq (= 8.17.1))
    (coq-iris (= dev.2023-06-30.0.7e865892))
    (coq-stdpp (= dev.2023-06-01.0.d1254759)) 
    (coq-compcert (= 3.14))
    (coq-ext-lib (= 0.12.1))
    (coq-mathcomp-ssreflect (= 1.18.0))
    (coq-parseque (= 0.2.1))
    (coq-itree (= 5.2.0))
    (cmdliner (= 1.3.0))
    (linenoise (= 1.5.1))
    (mdx (= 2.4.1))
    )	 
  (maintainers
    Maxime Legoupil
    )
  (authors
    Maxime Legoupil
    Bastien Rousseau
    Aina Linn Georges
    Jean Pichon-Pharabod
    Lars Birkedal
  )
)


(warnings (deprecated_coq_lang_lt_08 disabled))
